# <Family> ムーンショット計画 🌙

<!--
雛形メモ:
- 「進捗」ブロック: `- [ ] Phase 名 — 短い説明 状態絵文字 (関連ファイルへのリンク)` の形式
- 状態絵文字: 📋 未着手 / 🚧 進行中 / ✅ 完了 / 🔄 方針変更（判断ログ参照）
- 削除/廃止された Phase は 1 行 + commit hash に圧縮（取り消し線残置は不可、git が履歴を持つ）。凍結 Phase 番号は他文書参照ありうるので番号は残す
- 完了済み Phase の本文は 1 段（commit hash + 結論 1 行）に圧縮
- 判断ログは決着済 entry を削除（採用方針確定 / 反例却下 / commit 済）。active な撤退ライン・判定軸・進行中の判断は残す。凍結 slug (L-* 系) 不可侵。詳細 → CLAUDE.md「Plan / docs hygiene」
- プラン予算: ≤ 600 行 / active 判断ログ ≤ 10 entry。超過は `/compact-plan`（handoff 境界で自動起動）
- `rg "^- \[ \]"` で残タスク横断 grep、`rg "🔄"` でピボット箇所だけ拾える
-->

## 進捗

- [ ] Phase 0 — <名前> 📋
- [ ] Phase 1 — <名前> 📋 → [<inventory or subplan>.md](<path>)
- [ ] Phase 2 — <名前> 📋
- [ ] Phase 3 — <名前> 📋

## ゴール / Approach

(1〜3 行: 最終的に証明したい定理 / 達成したい状態 + 全体戦略)

## Phase 0 - <名前> 📋

- [ ] step 1
- [ ] step 2

## Phase 1 - <名前> 📋

- [ ] step 1

## 判断ログ

書く頻度: Phase 中の方針変更 / 撤退 / 当初仮定の修正があったとき。決着済 entry は削除 (git が履歴)、active な判断のみ残す (→ CLAUDE.md「Plan / docs hygiene」)。

<!-- 例:
1. **Phase γ の方針転換**: 当初 encoder 付き版で計画していたが、Phase 4-α DPI と整合しないため `I(Msg; Yo)` 直接版に変更。encoder 版は Phase δ サブ計画に分離。
2. **`Y : 任意の可測空間` 維持**: M0 時には `[StandardBorelSpace Y]` 必要と書いていたが、instance 自動 derive と判明し撤回。
-->
