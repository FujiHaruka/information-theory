# <親 Family>: <サブテーマ> サブ計画

> **Parent**: [`<parent>-moonshot-plan.md`](<parent>-moonshot-plan.md) §<該当 Phase>

<!--
雛形メモ:
- 記法は moonshot-plan-template と同じ（状態絵文字、取り消し線、判断ログ）
- Parent ヘッダは必須 (リンクは親 `*-plan.md` への相対パス)。plan_lint がこの行から親子グラフを構築し、
  pre-commit が「子を更新したら親も co-stage」を WARN する同期点。**子の状態 (本線/park、進捗) を
  変えたら親 DAG / sub-plan テーブルも直す** (衝突時は子が SoT → CLAUDE.md「Plan / docs hygiene」親子整合)
-->

## 進捗

- [ ] M0 在庫調査 📋
- [ ] skeleton 📋
- [ ] 本体実装 📋

## ゴール / Approach

(親の §該当 Phase を受けて何を完成させるか、1 段)

## Phase 詳細

(個別 step を `- [ ]` で書き下す)

## 判断ログ

書く頻度: 方針変更 / 撤退 / 当初仮定の修正があったとき。決着済 entry は削除 (git が履歴)、active な判断のみ残す (→ CLAUDE.md「Plan / docs hygiene」)。プラン予算 ≤ 600 行 / active 判断ログ ≤ 10 entry。
