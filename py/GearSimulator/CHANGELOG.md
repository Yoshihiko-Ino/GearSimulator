# Changelog / 変更履歴

## v1.0時点の仕様 / Baseline Spec (v1.0)
- 装備・マテリア・食事の選択に基づく試算スコアを表示。
- Displayed simulated score based on gear, materia, and food selection.
- FFLogsのキャスト/ダメージ取得を用いた試算DPS算出。
- Calculated simulated DPS using FFLogs cast and damage data.
- 保存セットの作成・選択・管理。
- Created, selected, and managed saved sets.

All notable changes to GearSimulator are documented here.
GearSimulator の主な変更点を記録しています。

## v1.0.3
- Added this changelog to keep version history in one place.
- 変更履歴を一箇所にまとめるため、チェンジログを追加しました。
- Improved simdps baseline handling when no selected items are available (defer instead of hard fail).
- 選択装備がない場合の simdps baseline 処理を改善（エラーではなく保留）しました。
- Added CRT/DH rate adjustment options (-20% to +20%) for calculation and optimization.
- 計算・最適化時に使える CRT/DH 率補正オプション（-20%〜+20%）を追加しました。
- Added an expected-score column to saved sets, separated from CRT/DH-adjusted score.
- 保存セットに CRT/DH 補正込みスコアとは別の期待値スコア列を追加しました。

## v1.0.2
- Added clipboard import for XIVGear JSON.
- XIVGear JSON のクリップボード取り込みを追加しました。
- Updated PT synergy selection UI to support multi-select and related display rules.
- PT シナジーの複数選択 UI と表示ルールを更新しました。
- Limited food list to combat food and sorted by item level.
- 食事一覧を戦闘向けのみ表示し、IL順に並ぶようにしました。
- Updated evaluation display options for simdps and Dmg/100p.
- 試算DPS/ Dmg/100p の評価表示オプションを更新しました。

## v1.0
- Initial release.
- 初回リリース。
