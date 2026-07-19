# GearSimulator

FF14用の装備・マテリア・食事シミュレーターです。

## 配布ファイル

- `GearSimulator.exe`: Windows向け単体実行ファイル
- `GearSimulator_v2.0.1_py.zip`: Python 3.9向けソース配布
- `SHA256SUMS.txt`: 配布ファイルのSHA-256チェックサム

## Windows版の起動

1. GitHub Releasesから`GearSimulator.exe`をダウンロードします。
2. 書き込み可能な任意のフォルダへ配置します。
3. `GearSimulator.exe`を起動します。

初回起動時に、exeと同じフォルダへ`config`と`cache`が作成されます。

## Python版の起動

1. Python 3.9を用意します。
2. zipを展開します。
3. 展開先で次を実行します。

```powershell
py -3.9 -m pip install -r requirements.txt
.\run_gui.bat
```

## 旧バージョンからの移行

- v2.0.1は旧バージョンと別のフォルダへ配置してください。
- 旧フォルダと同じ親フォルダへ`GearSimulator_v2.0.1`として配置すると、初回起動時に認証・画面設定・保存セットを引き継げます。
- 旧ファイルは削除・上書きしません。
- 旧形式の保存スコアは装備を保持したまま「要再計算」と表示されます。対象セットを選択し、必要なFFLogsデータを取得してから「計算」を実行してください。

## FFLogs連携

FFLogs APIのClient IDとClient Secretを設定画面へ入力します。Client SecretはWindowsの暗号化機能で保護して保存されます。

## 変更履歴

[CHANGELOG.md](CHANGELOG.md)を参照してください。
