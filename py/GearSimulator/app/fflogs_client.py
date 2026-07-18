from typing import Any, Callable, Dict, List, Optional, Tuple
import threading
import time

import httpx

from .utils import sim_log


BASE_URL_V2 = "https://www.fflogs.com/api/v2/client"
OAUTH_TOKEN_URL = "https://www.fflogs.com/oauth/token"


class FFLogsClient:
    def __init__(self, client_id: Optional[str] = None, client_secret: Optional[str] = None) -> None:
        self.client_id = client_id
        self.client_secret = client_secret
        self._client = httpx.Client(timeout=25)
        self._token_lock = threading.RLock()
        self._cache_lock = threading.RLock()
        self.last_enemy_npcs: List[dict] = []
        self.last_friendlies: List[dict] = []
        self._access_token: Optional[str] = None
        self._token_expires_at: float = 0.0
        # Session-level response cache to avoid repeated network calls for same query.
        self._response_cache: Dict[Tuple[str, Tuple[Tuple[str, Any], ...]], dict] = {}
        self._response_cache_order: List[Tuple[str, Tuple[Tuple[str, Any], ...]]] = []
        self._response_cache_limit = 512
        self._fight_friendly_ids: Dict[int, set] = {}

    def close(self) -> None:
        self._client.close()

    @staticmethod
    def _norm_int(value: Any) -> Optional[int]:
        try:
            if value is None:
                return None
            return int(value)
        except Exception:
            return None

    def ready(self) -> bool:
        with self._token_lock:
            return bool(self.client_id and self.client_secret)

    def set_credentials(self, client_id: str, client_secret: str) -> None:
        changed = False
        with self._token_lock:
            if client_id != self.client_id or client_secret != self.client_secret:
                self.client_id = client_id
                self.client_secret = client_secret
                self._access_token = None
                self._token_expires_at = 0.0
                changed = True
        if changed:
            self.clear_cache()

    def clear_credentials(self) -> None:
        with self._token_lock:
            self.client_id = None
            self.client_secret = None
            self._access_token = None
            self._token_expires_at = 0.0
        self.clear_cache()

    def _cache_key(self, query: str, variables: dict) -> Tuple[str, Tuple[Tuple[str, Any], ...]]:
        def normalize(obj: Any) -> Any:
            if isinstance(obj, dict):
                return tuple(sorted((str(k), normalize(v)) for k, v in obj.items()))
            if isinstance(obj, list):
                return tuple(normalize(v) for v in obj)
            return obj
        norm = normalize(variables)
        return (query, norm)

    def clear_cache(self) -> None:
        with self._cache_lock:
            self._response_cache.clear()
            self._response_cache_order.clear()

    def _ensure_token(self) -> str:
        with self._token_lock:
            if not self.client_id or not self.client_secret:
                raise RuntimeError("FFLogsのV2クライアント情報が設定されていません。")
            now = time.time()
            if self._access_token and now < self._token_expires_at:
                return self._access_token
            resp = self._client.post(
                OAUTH_TOKEN_URL,
                data={
                    "grant_type": "client_credentials",
                    "client_id": self.client_id,
                    "client_secret": self.client_secret,
                },
                headers={"Content-Type": "application/x-www-form-urlencoded"},
            )
            try:
                resp.raise_for_status()
            except httpx.HTTPStatusError as e:
                status = e.response.status_code
                raise RuntimeError(
                    f"FFLogs OAuth エラー (HTTP {status})。クライアントID/シークレットを確認してください。"
                ) from e
            data = resp.json()
            token = data.get("access_token")
            if not token:
                raise RuntimeError("FFLogs OAuth のトークン取得に失敗しました。")
            expires_in = data.get("expires_in")
            self._access_token = token
            if isinstance(expires_in, (int, float)) and expires_in > 0:
                # Refresh a bit early.
                self._token_expires_at = now + float(expires_in) - 30
            else:
                self._token_expires_at = now + 300
            return token

    def _post_graphql(self, query: str, variables: dict, use_cache: bool = True) -> dict:
        token = self._ensure_token()
        key = self._cache_key(query, variables)
        if use_cache:
            with self._cache_lock:
                cached = self._response_cache.get(key)
            if cached is not None:
                return cached
        resp = self._client.post(
            BASE_URL_V2,
            headers={"Authorization": f"Bearer {token}"},
            json={"query": query, "variables": variables},
        )
        try:
            resp.raise_for_status()
        except httpx.HTTPStatusError as e:
            status = e.response.status_code
            raise RuntimeError(
                f"FFLogs API エラー (HTTP {status})。クライアント情報やレポートコードを確認してください。"
            ) from e
        data = resp.json()
        if not isinstance(data, dict):
            raise RuntimeError("FFLogs API 応答が不正です。")
        if data.get("errors"):
            raise RuntimeError(str(data.get("errors")))
        if use_cache:
            with self._cache_lock:
                if key not in self._response_cache:
                    self._response_cache_order.append(key)
                self._response_cache[key] = data
                while len(self._response_cache_order) > self._response_cache_limit:
                    oldest = self._response_cache_order.pop(0)
                    self._response_cache.pop(oldest, None)
        return data

    def fetch_fights(self, report_code: str) -> List[dict]:
        variants = [
            (
                "full+friendlies",
                """
                query ReportFights($code: String!) {
                  reportData {
                    report(code: $code) {
                      fights { id name startTime endTime kill bossPercentage fightPercentage encounterID phaseTransitions { id startTime } friendlyPlayers }
                    }
                  }
                }
                """,
            ),
            (
                "full",
                """
                query ReportFights($code: String!) {
                  reportData {
                    report(code: $code) {
                      fights { id name startTime endTime kill bossPercentage fightPercentage encounterID phaseTransitions { id startTime } }
                    }
                  }
                }
                """,
            ),
            (
                "basic",
                """
                query ReportFights($code: String!) {
                  reportData {
                    report(code: $code) {
                      fights { id name startTime endTime kill }
                    }
                  }
                }
                """,
            ),
        ]
        data = None
        last_error: Optional[Exception] = None
        for _variant_name, query in variants:
            try:
                data = self._post_graphql(query, {"code": report_code})
                break
            except RuntimeError as e:
                last_error = e
                continue
        if data is None:
            if last_error:
                raise last_error
            return []
        report = ((data.get("data") or {}).get("reportData") or {}).get("report") or {}
        # V2 fights query no longer includes friendlies/enemies; keep empty defaults here.
        self.last_enemy_npcs = []
        fights = report.get("fights") or []
        self._fight_friendly_ids = {}
        for fight in fights:
            if not isinstance(fight, dict):
                continue
            try:
                fid = int(fight.get("id"))
            except Exception:
                continue
            ids = fight.get("friendlyPlayers") or []
            if isinstance(ids, list) and ids:
                norm_ids = {self._norm_int(v) for v in ids}
                norm_ids.discard(None)
                if norm_ids:
                    self._fight_friendly_ids[fid] = norm_ids
        return fights

    def fetch_phases(self, report_code: str, encounter_id: Optional[int]) -> dict:
        variants = [
            (
                "encounterID",
                """
                query ReportPhases($code: String!, $encounterID: Int) {
                  reportData {
                    report(code: $code) {
                      phases(encounterID: $encounterID) {
                        encounterID
                        separatesWipes
                        phases { id name isIntermission }
                      }
                    }
                  }
                }
                """,
                {"code": report_code, "encounterID": encounter_id},
            ),
            (
                "encounterId",
                """
                query ReportPhases($code: String!, $encounterId: Int) {
                  reportData {
                    report(code: $code) {
                      phases(encounterId: $encounterId) {
                        encounterID
                        separatesWipes
                        phases { id name isIntermission }
                      }
                    }
                  }
                }
                """,
                {"code": report_code, "encounterId": encounter_id},
            ),
            (
                "no-arg",
                """
                query ReportPhases($code: String!) {
                  reportData {
                    report(code: $code) {
                      phases {
                        encounterID
                        separatesWipes
                        phases { id name isIntermission }
                      }
                    }
                  }
                }
                """,
                {"code": report_code},
            ),
        ]
        data = None
        last_error: Optional[Exception] = None
        for _variant_name, query, variables in variants:
            try:
                data = self._post_graphql(query, variables)
                break
            except RuntimeError as e:
                last_error = e
                continue
        if data is None:
            if last_error:
                raise last_error
            return {}
        report = ((data.get("data") or {}).get("reportData") or {}).get("report") or {}
        phases = report.get("phases") or {}
        if isinstance(phases, list):
            if encounter_id is not None:
                for entry in phases:
                    if not isinstance(entry, dict):
                        continue
                    if entry.get("encounterID") == encounter_id or entry.get("encounterId") == encounter_id:
                        return entry
            return phases[0] if phases else {}
        if isinstance(phases, dict):
            return phases
        return {}

    def fetch_players(self, report_code: str, fight_id: int) -> List[dict]:
        variants = [
            (
                "fight+actors",
                """
                query ReportPlayers($code: String!, $fightIDs: [Int]) {
                  reportData {
                    report(code: $code) {
                      fights(fightIDs: $fightIDs) { id friendlyPlayers }
                      masterData {
                        actors(type: "Player") { id name type subType petOwner }
                      }
                    }
                  }
                }
                """,
                {"code": report_code, "fightIDs": [fight_id]},
            ),
            (
                "friendly+actors",
                """
                query ReportPlayers($code: String!) {
                  reportData {
                    report(code: $code) {
                      friendlyPlayers
                      masterData {
                        actors(type: "Player") { id name type subType petOwner }
                      }
                    }
                  }
                }
                """,
                {"code": report_code},
            ),
            (
                "actors-only",
                """
                query ReportPlayers($code: String!) {
                  reportData {
                    report(code: $code) {
                      masterData {
                        actors(type: "Player") { id name type subType petOwner }
                      }
                    }
                  }
                }
                """,
                {"code": report_code},
            ),
            (
                "actors-all",
                """
                query ReportPlayers($code: String!) {
                  reportData {
                    report(code: $code) {
                      masterData {
                        actors { id name type subType petOwner }
                      }
                    }
                  }
                }
                """,
                {"code": report_code},
            ),
        ]
        data = None
        last_error: Optional[Exception] = None
        for _variant_name, query, variables in variants:
            try:
                data = self._post_graphql(query, variables)
                break
            except RuntimeError as e:
                last_error = e
                continue
        if data is None:
            if last_error:
                raise last_error
            return []
        report = ((data.get("data") or {}).get("reportData") or {}).get("report") or {}
        friendly_ids = {self._norm_int(v) for v in (report.get("friendlyPlayers") or [])}
        friendly_ids.discard(None)
        if not friendly_ids:
            fights = report.get("fights") or []
            if isinstance(fights, list):
                for fight in fights:
                    if not isinstance(fight, dict):
                        continue
                    ids = fight.get("friendlyPlayers") or []
                    if ids:
                        friendly_ids = {self._norm_int(v) for v in ids}
                        friendly_ids.discard(None)
                        break
        if not friendly_ids:
            friendly_ids = self._fight_friendly_ids.get(int(fight_id), set())

        actors_raw = ((report.get("masterData") or {}).get("actors") or [])
        if isinstance(actors_raw, dict):
            actors = actors_raw.get("data") or actors_raw.get("entries") or []
        else:
            actors = actors_raw
        if friendly_ids:
            actors = [a for a in actors if self._norm_int(a.get("id")) in friendly_ids]
            if not actors:
                # Some reports do not expose friendlyPlayers; fall back to all actors.
                if isinstance(actors_raw, dict):
                    actors = actors_raw.get("data") or actors_raw.get("entries") or []
                else:
                    actors = actors_raw
        self.last_friendlies = actors
        return actors or []

    def _fetch_events(
        self,
        report_code: str,
        fight: dict,
        actor_id: int,
        data_type: str,
        include_pets: bool = False,
        stop_event=None,
        progress: Optional[Callable[[int, str], None]] = None,
    ) -> List[dict]:
        start = fight.get("startTime") or fight.get("start_time") or 0
        end = fight.get("endTime") or fight.get("end_time") or 0
        next_start = start
        total_span = max(1, end - start)
        all_events: List[dict] = []
        page_count = 0
        total_seen = 0
        max_ts = None
        filtered_out = 0
        query_enum = """
        query ReportEvents($code: String!, $fightIDs: [Int], $startTime: Float, $endTime: Float, $dataType: EventDataType!, $sourceID: Int, $limit: Int) {
          reportData {
            report(code: $code) {
              events(fightIDs: $fightIDs, startTime: $startTime, endTime: $endTime, dataType: $dataType, sourceID: $sourceID, limit: $limit) {
                data
                nextPageTimestamp
              }
            }
          }
        }
        """
        query_str = """
        query ReportEvents($code: String!, $fightIDs: [Int], $startTime: Float, $endTime: Float, $dataType: String!, $sourceID: Int, $limit: Int) {
          reportData {
            report(code: $code) {
              events(fightIDs: $fightIDs, startTime: $startTime, endTime: $endTime, dataType: $dataType, sourceID: $sourceID, limit: $limit) {
                data
                nextPageTimestamp
              }
            }
          }
        }
        """
        use_enum = True

        def _source_id(ev: dict) -> Optional[int]:
            return ev.get("sourceID") or ev.get("sourceId") or ev.get("sourceid")

        def _owner_id(ev: dict) -> Optional[int]:
            return ev.get("ownerID") or ev.get("ownerId") or ev.get("ownerid")

        while True:
            if stop_event and stop_event.is_set():
                break
            variables = {
                "code": report_code,
                "fightIDs": [fight.get("id")],
                "startTime": float(next_start) if next_start is not None else None,
                "endTime": float(end) if end is not None else None,
                "dataType": data_type,
                "sourceID": actor_id,
                "limit": 10000,
            }
            query = query_enum if use_enum else query_str
            try:
                data = self._post_graphql(query, variables)
            except RuntimeError as e:
                if use_enum and ("EventDataType" in str(e) or "dataType" in str(e)):
                    use_enum = False
                    data = self._post_graphql(query_str, variables)
                else:
                    raise
            container = ((data.get("data") or {}).get("reportData") or {}).get("report") or {}
            events_block = container.get("events") or {}
            events = events_block.get("data") or []
            page_count += 1
            total_seen += len(events)
            for ev in events:
                src = _source_id(ev)
                owner = _owner_id(ev)
                if include_pets:
                    if src is not None and src != actor_id and owner != actor_id:
                        filtered_out += 1
                        continue
                else:
                    if src is not None and src != actor_id:
                        filtered_out += 1
                        continue
                ts = ev.get("timestamp") or ev.get("time")
                if ts is not None:
                    max_ts = ts if max_ts is None else max(max_ts, ts)
                all_events.append(ev)
            next_page = events_block.get("nextPageTimestamp")
            if progress:
                pct = int(((next_start - start) / total_span) * 100)
                progress(min(99, pct), f"{data_type}取得中")
            if not next_page:
                break
            if next_page <= next_start:
                break
            next_start = next_page

        return all_events, page_count, total_seen, max_ts, filtered_out, end

    def fetch_casts(
        self,
        report_code: str,
        fight: dict,
        actor_id: int,
        stop_event=None,
        progress: Optional[Callable[[int, str], None]] = None,
    ) -> List[dict]:
        events, page_count, total_seen, max_ts, filtered_out, end = self._fetch_events(
            report_code,
            fight,
            actor_id,
            data_type="Casts",
            include_pets=False,
            stop_event=stop_event,
            progress=progress,
        )
        all_events: List[dict] = []
        for ev in events:
            ev_type = ev.get("type")
            if ev_type in ("cast", "begincast"):
                all_events.append(ev)
        if progress:
            progress(100, f"キャストを取得しました（{len(all_events)}件）")
        sim_log(
            f"[FFLogs] casts pages={page_count} seen={total_seen} kept={len(all_events)} "
            f"filtered={filtered_out} max_ts={max_ts} fight_end={end}"
        )
        return all_events

    def fetch_damage_events(
        self,
        report_code: str,
        fight: dict,
        actor_id: int,
        include_pets: bool = False,
        stop_event=None,
        progress: Optional[Callable[[int, str], None]] = None,
    ) -> List[dict]:
        events, page_count, total_seen, max_ts, filtered_out, end = self._fetch_events(
            report_code,
            fight,
            actor_id,
            data_type="DamageDone",
            include_pets=include_pets,
            stop_event=stop_event,
            progress=progress,
        )
        all_events = [ev for ev in events if ev.get("type") == "damage"]
        if progress:
            progress(100, f"ダメージを取得しました（{len(all_events)}件）")
        sim_log(
            f"[FFLogs] damage pages={page_count} seen={total_seen} kept={len(all_events)} "
            f"filtered={filtered_out} max_ts={max_ts} fight_end={end}"
        )
        return all_events

    def fetch_damage_done_table(
        self,
        report_code: str,
        fight_id: int,
        actor_id: Optional[int] = None,
        start: Optional[int] = None,
        end: Optional[int] = None,
        view: Optional[str] = None,
    ) -> dict:
        variants = [
            (
                "enum+view",
                """
                query ReportTable($code: String!, $fightIDs: [Int], $startTime: Float, $endTime: Float, $sourceID: Int, $view: String) {
                  reportData {
                    report(code: $code) {
                      table(dataType: DamageDone, fightIDs: $fightIDs, startTime: $startTime, endTime: $endTime, sourceID: $sourceID, view: $view)
                    }
                  }
                }
                """,
                {
                    "code": report_code,
                    "fightIDs": [fight_id],
                    "startTime": start,
                    "endTime": end,
                    "sourceID": actor_id,
                    "view": view,
                },
            ),
            (
                "string+view",
                """
                query ReportTable($code: String!, $fightIDs: [Int], $startTime: Float, $endTime: Float, $sourceID: Int, $view: String, $dataType: String!) {
                  reportData {
                    report(code: $code) {
                      table(dataType: $dataType, fightIDs: $fightIDs, startTime: $startTime, endTime: $endTime, sourceID: $sourceID, view: $view)
                    }
                  }
                }
                """,
                {
                    "code": report_code,
                    "fightIDs": [fight_id],
                    "startTime": start,
                    "endTime": end,
                    "sourceID": actor_id,
                    "view": view,
                    "dataType": "DamageDone",
                },
            ),
            (
                "enum+viewBy",
                """
                query ReportTable($code: String!, $fightIDs: [Int], $startTime: Float, $endTime: Float, $sourceID: Int, $viewBy: String) {
                  reportData {
                    report(code: $code) {
                      table(dataType: DamageDone, fightIDs: $fightIDs, startTime: $startTime, endTime: $endTime, sourceID: $sourceID, viewBy: $viewBy)
                    }
                  }
                }
                """,
                {
                    "code": report_code,
                    "fightIDs": [fight_id],
                    "startTime": start,
                    "endTime": end,
                    "sourceID": actor_id,
                    "viewBy": view,
                },
            ),
            (
                "string+viewBy",
                """
                query ReportTable($code: String!, $fightIDs: [Int], $startTime: Float, $endTime: Float, $sourceID: Int, $viewBy: String, $dataType: String!) {
                  reportData {
                    report(code: $code) {
                      table(dataType: $dataType, fightIDs: $fightIDs, startTime: $startTime, endTime: $endTime, sourceID: $sourceID, viewBy: $viewBy)
                    }
                  }
                }
                """,
                {
                    "code": report_code,
                    "fightIDs": [fight_id],
                    "startTime": start,
                    "endTime": end,
                    "sourceID": actor_id,
                    "viewBy": view,
                    "dataType": "DamageDone",
                },
            ),
            (
                "enum+plain",
                """
                query ReportTable($code: String!, $fightIDs: [Int], $startTime: Float, $endTime: Float, $sourceID: Int) {
                  reportData {
                    report(code: $code) {
                      table(dataType: DamageDone, fightIDs: $fightIDs, startTime: $startTime, endTime: $endTime, sourceID: $sourceID)
                    }
                  }
                }
                """,
                {
                    "code": report_code,
                    "fightIDs": [fight_id],
                    "startTime": start,
                    "endTime": end,
                    "sourceID": actor_id,
                },
            ),
            (
                "string+plain",
                """
                query ReportTable($code: String!, $fightIDs: [Int], $startTime: Float, $endTime: Float, $sourceID: Int, $dataType: String!) {
                  reportData {
                    report(code: $code) {
                      table(dataType: $dataType, fightIDs: $fightIDs, startTime: $startTime, endTime: $endTime, sourceID: $sourceID)
                    }
                  }
                }
                """,
                {
                    "code": report_code,
                    "fightIDs": [fight_id],
                    "startTime": start,
                    "endTime": end,
                    "sourceID": actor_id,
                    "dataType": "DamageDone",
                },
            ),
        ]
        data = None
        last_error: Optional[Exception] = None
        used_variant = None
        for variant_name, query, variables in variants:
            try:
                data = self._post_graphql(query, variables)
                used_variant = variant_name
                break
            except RuntimeError as e:
                last_error = e
                continue
        if data is None:
            if last_error:
                raise last_error
            return {}
        report = ((data.get("data") or {}).get("reportData") or {}).get("report") or {}
        table = report.get("table")
        if not isinstance(table, dict):
            return {}
        sim_log(
            f"[FFLogs] table variant={used_variant} view={view} sourceID={actor_id} "
            f"entries={len(table.get('entries') or [])}"
        )
        return table

    def fetch_actor_timeline_events(
        self,
        report_code: str,
        fight: dict,
        actor_id: int,
        include_pets: bool = False,
        stop_event=None,
        progress: Optional[Callable[[int, str], None]] = None,
    ) -> List[dict]:
        events, page_count, total_seen, max_ts, filtered_out, end = self._fetch_events(
            report_code,
            fight,
            actor_id,
            data_type="Buffs",
            include_pets=include_pets,
            stop_event=stop_event,
            progress=progress,
        )
        keep_types = {
            "cast",
            "begincast",
            "applybuff",
            "refreshbuff",
            "removebuff",
            "removebuffstack",
            "applydebuff",
            "refreshdebuff",
            "removedebuff",
            "removedebuffstack",
        }
        filtered = [ev for ev in events if ev.get("type") in keep_types]
        filtered.sort(key=lambda ev: ev.get("timestamp") or ev.get("time") or 0)
        if progress:
            progress(100, f"時系列を取得しました（{len(filtered)}件）")
        sim_log(
            f"[FFLogs] timeline pages={page_count} seen={total_seen} kept={len(filtered)} "
            f"filtered={filtered_out} max_ts={max_ts} fight_end={end}"
        )
        return filtered
