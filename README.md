# GearSimulator

FF14 用の装備・マテリア・食事シミュレーターです。  
このリポジトリでは配布用ファイルを公開しています。

## 配布内容

### `exe/GearSimulator.exe`
- Windows 向けの単体実行ファイルです。
- アプリに必要な静的データは exe に内包されています。
- 起動時に必要であれば、exe と同じ場所に `config` と `cache` フォルダを自動生成します。

### `py/GearSimulator`
- Python 版の配布ファイルです。
- 依存関係をインストールした後、`run_gui.bat` から起動できます。

## 使い方

### exe 版
1. `exe/GearSimulator.exe` を直接起動します。

### Python 版
1. Python 3.9 環境を用意します。
2. `py/GearSimulator` で依存関係をインストールします。
3. `run_gui.bat` を実行します。

## 変更履歴
- 詳細は [CHANGELOG.md](CHANGELOG.md) を参照してください。
