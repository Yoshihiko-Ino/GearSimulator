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

## v1.0.6
- 食事の VIT ボーナスを HP 計算へ正しく反映し、XIVGear との HP 表示差を修正しました。
- 保存セットや装備シミュレーション結果の同一スコア候補を、装備編集欄のタブで切り替えて確認できるようにしました。
- 装備一覧の右クリックメニューから FF14 公式 DB 検索を開けるようにし、検索時除外と除外数表示を追加しました。
- 圧縮表示が 1 件しか含まない場合は通常の装備行として表示し、選択や右クリック操作が分かりやすくなるよう改善しました。
- 保存セット切り替え時の一覧表示や選択復元、ユニーク装備判定まわりの不具合を修正しました。

## v1.0.5
- 部位ごとの装備固定・マテリア固定に対応し、未固定部位のみを対象に装備シミュレーションできるようにしました。
- 装備シミュレーション後に左右装備の再探索を追加し、候補精度を改善しました。
- 保存セット切り替え時の装備一覧表示を高速化し、選択中の装備行が一覧内で見えるように改善しました。
- CRT補正・DH補正、期待値スコア列、レベルシンク時の表示・試算の整合性を改善しました。
- 保存セットの削除後に一覧が一時的に消える不具合や、近い構成のセット切り替え時に不要な再選択が走る不具合を修正しました。

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
