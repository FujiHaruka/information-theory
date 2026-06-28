# T3-F Relay Channel + Cut-set Outer Bound ムーンショット計画 🌙

**Status**: ✅ **GENUINE CLOSURE 達成** (2026-06-29, relay scopeout chain leg 4) — headline `relay_cutset_outer_bound` (Cover–Thomas Thm 15.10.1) が sorryAx-free + 独立 honesty audit `@audit:ok` で閉じた。旧 hypothesis pass-through 設計 (`_h_csiszar:True` で結論を bundle) は全廃、cut-set の核を **実際に証明**。BC-cut の当初 wall-likely 判定は gateway-atom-first で覆った (tractable, not wall)。旧 scope-out (下記履歴) は pass-through 設計に対する判断であり genuine closure は別物。

**SoT**: `docs/textbook-roadmap.md` Ch.15。詳細履歴は git。

## Genuine-closure 進捗 (active)

**完了 (leg 3, commit 62f99f95 / 9546e947, @audit:ok, sorryAx-free)** — `InformationTheory/Shannon/RelayCutset.lean`:
- `RelayChannel` (abbrev) / `RelayCode` (structure, causal relay field) / `relayCutsetBound (Ib Im) := min Ib Im` (scalar)。
- `relay_mac_cut_singleletterize`: `I(Xⁿ,X₁ⁿ;Yⁿ) ≤ ∑ I(Xᵢ,X₁ᵢ;Yᵢ)` — `mutualInfo_le_sum_per_letter_of_memoryless_strong` 直接適用 (joint input `(Xᵢ,X₁ᵢ)`, no conditioner)。
- `relay_broadcast_cut_singleletterize`: `I(Xⁿ;Y₁ⁿ,Yⁿ|X₁ⁿ) ≤ ∑ I(Xᵢ;Y₁ᵢ,Yᵢ|X₁ᵢ)` — `condMutualInfo_singleletter_le_of_memoryless` 直接適用 (var X, cond X₁, joint out (Y₁,Y))。
- 両者 `h_memo : IsMemorylessChannel` を **precondition (regularity)** として受け結論を genuinely 証明 = honest (監査が load-bearing でないと確認、core = entropy subadditivity の独立ステップ)。gateway-atom-first で「壁でない」確定。

**headline assembly (operational 層) ✅ 完了 (leg 4)** — `relay_cutset_outer_bound : log M ≤ relayCutsetBound Ib Im` — サブ計画 → [`relay-cutset-headline-plan.md`](relay-cutset-headline-plan.md):
- **MAC-cut (易, genuine)**: `relay_mac_cut_outer_bound` (commit `be67233f`) — `shannon_converse_single_shot` (Converse.lean:70, message-level Fano) → `mutualInfo_le_of_markov` (block Markov precondition) → `relay_mac_cut_singleletterize`。
- **BC-cut (核, wall-likely 判定を gateway-atom-first で覆す)**: `relay_broadcast_cut_message_telescope` (commit `786b15e2`) — per-letter causal telescoping が既存資産 (`mutualInfo_le_of_postprocess` + `jointEntropy_chain_rule` + `isMarkovChain_comp_conditioner_right`) で組め、d-separation 自作 (~150-250 行見積り) 不要だった。`relay_broadcast_cut_singleletterize` (block 条件付き MI) は予測通り未使用 (telescoping が直接 per-letter sum を出す)。h_memo は false な `W⊥X₁ⁿ` でなく i 番目入力で条件付けた memoryless d-separation precondition (監査 PASS)。
- **min 合成**: `relay_broadcast_cut_outer_bound` + `relay_cutset_outer_bound` (commit `f2547c93`, `@audit:ok` `9b4de42d`) — `le_min` で BC/MAC 2 cut を合成。relayCutsetBound の `Ib`/`Im` 引数に explicit per-letter sum + Fano を直接代入 (externalisation 仮説なし、outer max over p は caller 委任)。全 `@audit:ok`・0/0/0 sorryAx-free。

> **Parent**:
> - [`textbook-roadmap.md`](../textbook-roadmap.md) §「Tier 3 — T3-F. Relay Channel + Cut-set bound (Cover-Thomas Ch.15.7 / 15.10)」

## 要点 (将来再利用しうる設計のみ)

- 採った形: outer bound only + scalar form `relayCutsetBound (Ib Im : ℝ) := min Ib Im`。joint pmf 上の `sSup` (max over `p(x,x₁)`) は呼び出し側に外出しすることで `IsCompact + exists_isMaxOn` の plumbing を回避する設計。
- 雛形は T3-D Wyner-Ziv converse の statement-level hypothesis pass-through pattern。broadcast-cut / MAC-cut / composite rate bound / relay measurability / inner bound (DF/CF) を全て hypothesis pass-through ないし scope-out する判断だった。
- inner bound (decode-and-forward / compress-and-forward) は当初から完全 scope-out (random binning + jointly typical decoder + n-letter AEP で大規模)。
