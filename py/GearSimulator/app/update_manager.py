from __future__ import annotations

import hashlib
import logging
import os
import re
import shutil
import subprocess
import tempfile
from dataclasses import dataclass
from pathlib import Path
from typing import Callable, Optional, Tuple
from urllib.parse import urlparse

import httpx


logger = logging.getLogger(__name__)
GITHUB_REPOSITORY = "Yoshihiko-Ino/GearSimulator"
GITHUB_LATEST_RELEASE_API = (
    f"https://api.github.com/repos/{GITHUB_REPOSITORY}/releases/latest"
)
WINDOWS_ASSET_NAME = "GearSimulator.exe"
MAX_UPDATE_BYTES = 500 * 1024 * 1024
_VERSION_PATTERN = re.compile(r"^v?(\d{1,9})\.(\d{1,9})\.(\d{1,9})$", re.IGNORECASE)
_ALLOWED_DOWNLOAD_HOSTS = {
    "github.com",
    "objects.githubusercontent.com",
    "release-assets.githubusercontent.com",
}
_REPOSITORY_PATH = f"/{GITHUB_REPOSITORY}/".lower()


class UpdateError(RuntimeError):
    pass


class UpdateCancelled(UpdateError):
    pass


@dataclass(frozen=True)
class ReleaseAsset:
    name: str
    download_url: str
    size: int
    sha256: Optional[str]


@dataclass(frozen=True)
class ReleaseInfo:
    version: str
    tag_name: str
    title: str
    notes: str
    html_url: str
    windows_asset: Optional[ReleaseAsset]


def parse_stable_version(value: object) -> Optional[Tuple[int, int, int]]:
    match = _VERSION_PATTERN.fullmatch(str(value or "").strip())
    if not match:
        return None
    return tuple(int(part) for part in match.groups())


def is_newer_version(candidate: object, current: object) -> bool:
    candidate_version = parse_stable_version(candidate)
    current_version = parse_stable_version(current)
    return bool(
        candidate_version is not None
        and current_version is not None
        and candidate_version > current_version
    )


def _parse_https_url(value: object):
    url = str(value or "").strip()
    parsed = urlparse(url)
    if parsed.scheme != "https" or parsed.username or parsed.password:
        return url, None
    try:
        if parsed.port not in (None, 443):
            return url, None
    except ValueError:
        return url, None
    return url, parsed


def _valid_release_page_url(value: object) -> Optional[str]:
    url, parsed = _parse_https_url(value)
    if parsed is None:
        return None
    host = (parsed.hostname or "").lower()
    path = parsed.path.lower()
    expected_prefix = f"{_REPOSITORY_PATH}releases/"
    return url if host == "github.com" and path.startswith(expected_prefix) else None


def _valid_release_asset_url(value: object) -> Optional[str]:
    url, parsed = _parse_https_url(value)
    if parsed is None:
        return None
    host = (parsed.hostname or "").lower()
    path = parsed.path.lower()
    expected_prefix = f"{_REPOSITORY_PATH}releases/download/"
    return url if host == "github.com" and path.startswith(expected_prefix) else None


def _valid_download_destination(value: object) -> Optional[str]:
    url, parsed = _parse_https_url(value)
    if parsed is None:
        return None
    host = (parsed.hostname or "").lower()
    if host == "github.com":
        return _valid_release_asset_url(url)
    return url if host in _ALLOWED_DOWNLOAD_HOSTS else None


def _asset_from_payload(payload: object) -> Optional[ReleaseAsset]:
    if not isinstance(payload, dict) or payload.get("name") != WINDOWS_ASSET_NAME:
        return None
    download_url = _valid_release_asset_url(payload.get("browser_download_url"))
    if not download_url:
        return None
    try:
        size = int(payload.get("size") or 0)
    except (TypeError, ValueError):
        return None
    if size <= 0 or size > MAX_UPDATE_BYTES:
        return None
    digest = str(payload.get("digest") or "").strip().lower()
    sha256 = digest.removeprefix("sha256:") if digest.startswith("sha256:") else None
    if sha256 is not None and not re.fullmatch(r"[0-9a-f]{64}", sha256):
        sha256 = None
    return ReleaseAsset(
        name=WINDOWS_ASSET_NAME,
        download_url=download_url,
        size=size,
        sha256=sha256,
    )


def check_for_update(
    current_version: str,
    skipped_version: Optional[str] = None,
    *,
    stop_event=None,
    client: Optional[httpx.Client] = None,
) -> Optional[ReleaseInfo]:
    if stop_event is not None and stop_event.is_set():
        return None
    own_client = client is None
    http_client = client or httpx.Client(
        timeout=8.0,
        follow_redirects=True,
        headers={
            "Accept": "application/vnd.github+json",
            "User-Agent": f"GearSimulator/{current_version}",
            "X-GitHub-Api-Version": "2022-11-28",
        },
    )
    try:
        response = http_client.get(GITHUB_LATEST_RELEASE_API)
        response.raise_for_status()
        payload = response.json()
    finally:
        if own_client:
            try:
                http_client.close()
            except Exception:
                logger.warning("Failed to close GitHub update-check client", exc_info=True)
    if stop_event is not None and stop_event.is_set():
        return None
    if not isinstance(payload, dict):
        raise UpdateError("GitHub Release APIの応答形式が不正です。")
    if bool(payload.get("draft")) or bool(payload.get("prerelease")):
        return None
    tag_name = str(payload.get("tag_name") or "").strip()
    parsed_version = parse_stable_version(tag_name)
    if parsed_version is None or not is_newer_version(tag_name, current_version):
        return None
    version = ".".join(str(part) for part in parsed_version)
    if parse_stable_version(skipped_version) == parsed_version:
        return None
    html_url = _valid_release_page_url(payload.get("html_url"))
    if not html_url:
        raise UpdateError("GitHub Release URLが不正です。")
    assets = payload.get("assets") or []
    windows_asset = next(
        (
            parsed
            for raw_asset in assets
            if (parsed := _asset_from_payload(raw_asset)) is not None
        ),
        None,
    )
    return ReleaseInfo(
        version=version,
        tag_name=tag_name,
        title=str(payload.get("name") or tag_name),
        notes=str(payload.get("body") or ""),
        html_url=html_url,
        windows_asset=windows_asset,
    )


def download_windows_update(
    asset: ReleaseAsset,
    *,
    stop_event=None,
    progress: Optional[Callable[[int, str], None]] = None,
    client: Optional[httpx.Client] = None,
) -> Path:
    if not asset.sha256:
        raise UpdateError("更新ファイルのSHA-256を確認できません。")
    own_client = client is None
    http_client: Optional[httpx.Client] = None
    update_dir: Optional[Path] = None
    digest = hashlib.sha256()
    downloaded = 0
    try:
        http_client = client or httpx.Client(
            timeout=httpx.Timeout(30.0, read=60.0),
            follow_redirects=True,
            headers={"User-Agent": "GearSimulator-Updater"},
        )
        update_dir = Path(tempfile.mkdtemp(prefix="GearSimulator-update-"))
        partial_path = update_dir / f"{WINDOWS_ASSET_NAME}.part"
        completed_path = update_dir / WINDOWS_ASSET_NAME
        with http_client.stream("GET", asset.download_url) as response:
            response.raise_for_status()
            final_url = _valid_download_destination(str(response.url))
            if not final_url:
                raise UpdateError("更新ファイルのダウンロード先が不正です。")
            with partial_path.open("wb") as output:
                for chunk in response.iter_bytes(chunk_size=1024 * 1024):
                    if stop_event is not None and stop_event.is_set():
                        raise UpdateCancelled("更新をキャンセルしました。")
                    if not chunk:
                        continue
                    downloaded += len(chunk)
                    if downloaded > asset.size or downloaded > MAX_UPDATE_BYTES:
                        raise UpdateError("更新ファイルのサイズが不正です。")
                    output.write(chunk)
                    digest.update(chunk)
                    if progress:
                        pct = int(downloaded * 100 / max(1, asset.size))
                        progress(min(99, pct), "アップデートをダウンロード中")
                output.flush()
                os.fsync(output.fileno())
        if stop_event is not None and stop_event.is_set():
            raise UpdateCancelled("更新をキャンセルしました。")
        if downloaded != asset.size:
            raise UpdateError("更新ファイルのサイズが一致しません。")
        if digest.hexdigest().lower() != asset.sha256.lower():
            raise UpdateError("更新ファイルのSHA-256が一致しません。")
        os.replace(partial_path, completed_path)
        if progress:
            progress(100, "アップデートの検証が完了しました")
        return completed_path
    except Exception:
        if update_dir is not None:
            shutil.rmtree(update_dir, ignore_errors=True)
        raise
    finally:
        if own_client and http_client is not None:
            try:
                http_client.close()
            except Exception:
                logger.warning("Failed to close update download client", exc_info=True)


def _powershell_update_script() -> str:
    return r'''param(
    [Parameter(Mandatory=$true)][string]$TargetPath,
    [Parameter(Mandatory=$true)][string]$PackagePath,
    [Parameter(Mandatory=$true)][int]$ProcessId,
    [Parameter(Mandatory=$true)][string]$ExpectedSha256
)
$ErrorActionPreference = "Stop"
$BackupPath = "$TargetPath.update-backup"
$ErrorLog = "$TargetPath.update-error.log"
$RollbackStarted = $false
try {
    $ActualSha256 = (Get-FileHash -LiteralPath $PackagePath -Algorithm SHA256).Hash
    if (-not [string]::Equals($ActualSha256, $ExpectedSha256, [System.StringComparison]::OrdinalIgnoreCase)) {
        throw "更新ファイルのSHA-256が差し替え前の検証結果と一致しません。"
    }
    $Deadline = (Get-Date).AddMinutes(5)
    while ((Get-Process -Id $ProcessId -ErrorAction SilentlyContinue) -and ((Get-Date) -lt $Deadline)) {
        Start-Sleep -Milliseconds 250
    }
    if (Get-Process -Id $ProcessId -ErrorAction SilentlyContinue) {
        throw "更新前のアプリケーションを終了できませんでした。"
    }
    Remove-Item -LiteralPath $ErrorLog -Force -ErrorAction SilentlyContinue
    Remove-Item -LiteralPath $BackupPath -Force -ErrorAction SilentlyContinue
    Move-Item -LiteralPath $TargetPath -Destination $BackupPath -Force
    try {
        Move-Item -LiteralPath $PackagePath -Destination $TargetPath -Force
        $Started = Start-Process -FilePath $TargetPath -WorkingDirectory (Split-Path -Parent $TargetPath) -PassThru
        Start-Sleep -Seconds 5
        if ($Started.HasExited) {
            throw "更新後のアプリケーションを起動できませんでした。"
        }
        Remove-Item -LiteralPath $BackupPath -Force -ErrorAction SilentlyContinue
    }
    catch {
        Remove-Item -LiteralPath $TargetPath -Force -ErrorAction SilentlyContinue
        if (Test-Path -LiteralPath $BackupPath) {
            Move-Item -LiteralPath $BackupPath -Destination $TargetPath -Force
            Start-Process -FilePath $TargetPath -WorkingDirectory (Split-Path -Parent $TargetPath)
            $RollbackStarted = $true
        }
        throw
    }
}
catch {
    $_ | Out-File -LiteralPath $ErrorLog -Encoding UTF8 -ErrorAction SilentlyContinue
    if ((-not $RollbackStarted) -and (-not (Get-Process -Id $ProcessId -ErrorAction SilentlyContinue)) -and (Test-Path -LiteralPath $TargetPath)) {
        Start-Process -FilePath $TargetPath -WorkingDirectory (Split-Path -Parent $TargetPath)
    }
    exit 1
}
finally {
    $ScriptDirectory = Split-Path -Parent $PSCommandPath
    Remove-Item -LiteralPath $PSCommandPath -Force -ErrorAction SilentlyContinue
    Remove-Item -LiteralPath $ScriptDirectory -Force -ErrorAction SilentlyContinue
}
'''


def launch_windows_update(
    package_path: Path,
    target_executable: Path,
    current_process_id: int,
    expected_sha256: str,
) -> None:
    package = package_path.resolve()
    target = target_executable.resolve()
    if os.name != "nt" or not target.is_file() or not package.is_file():
        raise UpdateError("Windows版アップデートを開始できません。")
    if package == target:
        raise UpdateError("実行中のアプリを更新ファイルとして使用できません。")
    try:
        process_id = int(current_process_id)
    except (TypeError, ValueError) as exc:
        raise UpdateError("更新元のプロセスIDが不正です。") from exc
    if process_id <= 0:
        raise UpdateError("更新元のプロセスIDが不正です。")
    normalized_sha256 = str(expected_sha256 or "").strip().lower()
    if not re.fullmatch(r"[0-9a-f]{64}", normalized_sha256):
        raise UpdateError("更新ファイルのSHA-256が不正です。")
    try:
        with tempfile.NamedTemporaryFile(
            prefix=".gearsimulator-update-",
            dir=target.parent,
        ):
            pass
    except OSError as exc:
        raise UpdateError("アプリの保存先に更新ファイルを書き込めません。") from exc
    script_path = package.parent / "apply-update.ps1"
    try:
        script_path.write_text(_powershell_update_script(), encoding="utf-8-sig")
    except Exception as exc:
        script_path.unlink(missing_ok=True)
        raise UpdateError("更新用スクリプトを書き込めません。") from exc
    creation_flags = getattr(subprocess, "CREATE_NO_WINDOW", 0) | getattr(
        subprocess,
        "CREATE_NEW_PROCESS_GROUP",
        0,
    )
    try:
        subprocess.Popen(
            [
                "powershell.exe",
                "-NoProfile",
                "-NonInteractive",
                "-ExecutionPolicy",
                "Bypass",
                "-File",
                str(script_path),
                "-TargetPath",
                str(target),
                "-PackagePath",
                str(package),
                "-ProcessId",
                str(process_id),
                "-ExpectedSha256",
                normalized_sha256,
            ],
            stdin=subprocess.DEVNULL,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
            creationflags=creation_flags,
            close_fds=True,
        )
    except Exception as exc:
        script_path.unlink(missing_ok=True)
        raise UpdateError("更新用プロセスを起動できません。") from exc
