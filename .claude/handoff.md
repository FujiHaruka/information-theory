# Handoff — 2026-08-09. **T3c relay 終端 (DONE)。20 leg 完走・§0 未達 (§6-3 発火)。次の本線はユーザー判断待ち**

## State

- Branch: `bc-computable-region` / Uncommitted: **clean**（push 済、HEAD = `4822fd0f`）
- Active plan: `docs/shannon/bc-open-problem-t3c-plan.md`（**582 行 / 予算 600**）= ⚠⚠ **CLOSED (ゴール未達)**
- 子 plan: `docs/shannon/bc-computable-region-formalization-plan.md`（**299 / 300**）= ⚠ **単位 A / B / C は本 relay の枠外に残り、以後どの relay にも所有されていない**（孤児ではなく未割当）
- 祖父 plan: `docs/shannon/broadcast-channel-moonshot-plan.md`（**398 / 600**）= t3c 終端を反映済
- 親子整合: `plan_lint`（bc family 10 plans）= **STALE 0 · SUSPECT 0 · BUDGET 0**
- N19 の commit: `bd23adbf`（起票の凍結）/ `0311b4a0`（実行）/ `4f953d2c`（監査）/ `fbc06c9f`（着地）/ `4822fd0f`（祖父同期）

## Relay control

- Mode: **DONE**
- Goal: `docs/shannon/bc-open-problem-t3c-plan.md` §0（一般 2 受信者 DM-BC の容量領域の計算可能な特徴付けを、散文の証明 + Lean の proof done の両方で決着させる）
- Leg: 23 / cap 23 — **完走して終端**
- Predecessor: none（`bc-t3c-r22` は kill 済）
- **Stop-on: `completion`（N19 着地 = plan の 20 leg 全消化）**
- 終端サマリ: ⚠⚠ **§0 のゴールは未達**。20 leg (N0–N19) を使い切って **§6-3 が発火**し、「未達」と記録した。⚠⚠ **`Thm7 ⊋ C` の材料は 1 つも出ておらず、排除もされていない**。⚠ **中間結果でゴールを埋め合わせていない**（記録の正直さは §1 反証条件 1 で機械判定 = 不発火）。
- Progress ledger:
  - r19: N15 完遂 = 判定 GO。`e5e8dea9` … `220a9df9`
  - r20: N16 完遂 = 判定 `UV = C`（減算方向の較正）。`d9398597` … `c82fc351`
  - r21: N17 完遂 = 単位 B の受け皿が層 3 に実在。`93dd1527` … `510714ed`
  - r22: N18 完遂 = `thm7Region W ≠ ∅` を sorryAx-free で構成。`7390bc9a` … `7a9dc552`
  - r23: **N19 完遂 = relay 終端**。proof-log + metrics + 較正 + §6-3 発火 + 棚卸し最終形 + facts `## N19 (T3c)` + 祖父同期。**監査 = 訂正 15 件・主判定を動かすもの 0 件・主判定は生存**。`bd23adbf` … `4822fd0f`

## Where we are

**T3c relay は 20 leg を完走し、§0 のゴールに到達しないまま終端した**（前 2 次と合わせて **61 leg 未達**）。N19 は判定 leg ではなく記録 leg で、新しい GO / NO-GO は 1 本も出していない。

- ⚠⚠ **`Thm7 ⊋ C` の材料は relay を通じて 1 つも出ておらず、排除もされていない** / ⚠⚠ **レート領域の包含について Lean は依然 1 文字も言っていない**。
- ⭐ **層 3 に本 relay が足した `@[entry_point]` は 6 本**（N8 3 / N11 2 / **N18 1** = `c4ab66a6`）。⚠ 親 plan が長く書いていた「5 本ちょうど」は N16 着地時点の値で、N19 が終端値へ訂正した。
- ⭐ **本 relay は `sorry` + `@residual` を初めて使った relay**（`Thm7Region.lean` に 2 本、分類は `plan:bc-computable-region-formalization`、`wall:` は **0 本**）。前 2 次は 0 本で終わっている。
- ⭐⭐ **N19 の最大の収穫は較正の側**: 前 relay の「**義務を締める見立ては 9/9 で覆る**」は **本 relay では再現しなかった**（凍結型 4 leg の締める側 9 本のうち、完全に覆ったのは 1 本 / 結論水準の生存 4 / 部分評価 1 / 強い形だけが死んだ 3）。⚠⚠ **母集団が違う**（前 relay は事後拾い、本 relay は着手前凍結 = §4.4-1 の義務そのものが交絡）。
- ⚠⚠ **監査が「3 つ目の `9`」を検出した** — 締める側を 9 本と数えた母集団は **N19 自身を除外**しており、入れると 11 本になる。前 relay proof-log §3 冒頭が警告した「母集団の違う `9`」の再演で、proof-log と facts `N19-f` に除外を先に申告する形で記録した。
- ⭐ **運用の実測**: subagent の「報告なし idle 化」は **生産の失敗ではなく伝達の失敗**であることを監査が機械で確定（形式化枠 2 leg の 11 体中 **5 体**は報告が親 transcript に存在しない ＝ 読み落としではない）。⟹ 前 relay の処方（再発射）は二重ディスパッチを生む誤対処。

## Next step — ⚠⚠ **ユーザー判断待ち（自走で決めてはならない）**

**§6-3 は「本 relay を終了して次の判断をユーザーに返す」ライン**であり、継続するか / どの受け皿へ leg を配るかは**ユーザーが決める**（前身 t3b → t3c の承継も `子 §7 判断ログ 1` のとおりユーザー決定）。⚠ **第 4 次 relay を勝手に起票しない / 別路線を勝手に本線へ格上げしない**。

残っている受け皿（⚠⚠ **「尽きた」と書かない**。型つき一覧の SoT = 親 plan §5 の「relay 終端の棚卸し」表）:

- 第 2 段 `[構築 + probe]` = [glnsum] の和 (⊕) チャネル族（⚠ **N16 は 1 mm も触っていない**）
- (γ) `(R2)` / `(R3)` の層 3 化 / 他インスタンス / `e > h(p)` 側（死因 `probe-failed` = **比較の相手が無い**）
- 一般 BC への持ち上げ（⚠ `restatement` 公算が最も高い）
- **形式化債務 = 子 plan の単位 B の中核 8–10 / 単位 A / C**（⚠ **どの relay にも未割当**）
- **否定側 (T3-β) の形式化員数は誰も測っていない**

## Files to read first

- `docs/shannon/bc-open-problem-t3c-plan.md` — §5 の「relay 終端の棚卸し」表 / §5.1 の N19 着地ブロック / §6-3 / §7 判断ログ 14
- `docs/proof-logs/proof-log-bc-open-problem-t3c-relay.md` — **本 relay のボトルネック分析**（較正 / 運用 / 探索アークの実測）
- `docs/metrics/bc-open-problem-t3c-relay.{manifest.json,metrics.md}` — 定量。⚠ **`--discover --file-prefix` は「そのプレフィックスを触ったセッションだけを列挙する」包含フィルタ**（編集数のフィルタではない）
- `docs/shannon/bc-facts.md` `## N19 (T3c)`（claim 8 行 = `N19-a` … `N19-h`）
- `docs/shannon/bc-t3c-n19-audit.md` — 監査 15 件 + 自己申告 11 項の 3 値検算

## Load-bearing context

- ⭐ **凍結検査の不変量は「hunk の開始行と個数」であって末尾行数ではない** — 追記のたびに `+198,NNN` は変わる。`git diff <起票 commit>` の**削除行 0 だけでは不十分**（凍結区間への**挿入**は削除行 0 のまま通る。監査が機械で実演）⟹ **先頭 N 行の `cmp` と併用する**。
- ⭐ **監査ブリーフに毎回書くこと**（r20 / r21 / r22 / r23 で 4 leg 連続で効いた）: **「被監査 leg が §5 で自己申告した弱点を、その向きで本当に崩れるか 1 本ずつ検算せよ」**。r23 ではこれで**自己申告 11 項のうち 1 項が弱すぎ・2 項が強すぎ**と判定された。
- ⚠ **subagent の報告は成果物の証拠にならない** — `git log` / `git diff` / ファイル本体で必ず裏を取る（本 leg は 5 体すべて裏取り済で報告と実態の乖離は 0 件）。
- ⚠ **`.claude/handoff.md` は gitignore** ⟹ commit しようとしない。
