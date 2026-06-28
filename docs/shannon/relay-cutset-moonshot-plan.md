# T3-F Relay Channel + Cut-set Outer Bound ムーンショット計画 🌙

**Status**: GENUINE-CLOSURE ラインで再活性 (2026-06-29, relay scopeout chain leg 3) — 旧 hypothesis pass-through 設計 (`_h_csiszar:True` で結論を bundle) を排し、cut-set の核を **実際に証明** する方針に転換。旧 scope-out (下記履歴) は pass-through 設計に対する判断であり、genuine closure は別物。

**SoT**: `docs/textbook-roadmap.md` Ch.15。詳細履歴は git。

## Genuine-closure 進捗 (active)

**完了 (leg 3, commit 62f99f95 / 9546e947, @audit:ok, sorryAx-free)** — `InformationTheory/Shannon/RelayCutset.lean`:
- `RelayChannel` (abbrev) / `RelayCode` (structure, causal relay field) / `relayCutsetBound (Ib Im) := min Ib Im` (scalar)。
- `relay_mac_cut_singleletterize`: `I(Xⁿ,X₁ⁿ;Yⁿ) ≤ ∑ I(Xᵢ,X₁ᵢ;Yᵢ)` — `mutualInfo_le_sum_per_letter_of_memoryless_strong` 直接適用 (joint input `(Xᵢ,X₁ᵢ)`, no conditioner)。
- `relay_broadcast_cut_singleletterize`: `I(Xⁿ;Y₁ⁿ,Yⁿ|X₁ⁿ) ≤ ∑ I(Xᵢ;Y₁ᵢ,Yᵢ|X₁ᵢ)` — `condMutualInfo_singleletter_le_of_memoryless` 直接適用 (var X, cond X₁, joint out (Y₁,Y))。
- 両者 `h_memo : IsMemorylessChannel` を **precondition (regularity)** として受け結論を genuinely 証明 = honest (監査が load-bearing でないと確認、core = entropy subadditivity の独立ステップ)。gateway-atom-first で「壁でない」確定。

**残 = headline assembly (operational 層, 次 leg)** — `relay_cutset_outer_bound : log M ≤ relayCutsetBound Im Ib` — サブ計画 → [`relay-cutset-headline-plan.md`](relay-cutset-headline-plan.md):
- 雛形 = Line A `bc_converse` (BroadcastChannel/Converse.lean:572): message-level Fano + single-letterization を `.mono` 合成。relay は単一メッセージ + `le_min_iff` で 2 cut を合成。
- **MAC-cut (易)**: `log M ≤ I(W;Yⁿ)+Fano` (単一ユーザ converse `channel_coding_converse_general_chainRule` / `shannon_converse_single_shot_markov_encoder` @ ConverseGeneral.lean) → `I(W;Yⁿ) ≤ I(Xⁿ,X₁ⁿ;Yⁿ)` (`mutualInfo_le_of_markov` @ CondMutualInfo.lean:356, precondition: block Markov `W→(Xⁿ,X₁ⁿ)→Yⁿ`) → `relay_mac_cut_singleletterize`。
- **BC-cut (核, wall-likely 判定済 → child §BC-cut 壁判定)**: 既存 `relay_broadcast_cut_singleletterize` (block 条件付き MI) は headline で直接消費不可。MAC `mac_message_le_condMI` の message→block 橋は `h_indep` (`I(Msg₁;Msg₂)=0`) load-bearing で、relay には独立第二メッセージが無く `I(W;X₁ⁿ)≠0` (causal feedback) ゆえ analog が FALSE。CT 15.10.1 の per-letter causal telescoping (~150-250 行, in-project 資産無し) が必要。child Phase 3 で gateway atom `relay_broadcast_cut_message_telescope` を 1 本 dispatch して tractability を確定 (gateway-atom-first)。閉じねば MAC-cut 単独 genuine publish + BC sorry+`@residual(plan:relay-cutset-headline-plan)` で partial、user-decision 停止。
- min 合成: `le_min_iff`。relayCutsetBound の `Ib`(BC-cut) / `Im`(MAC-cut) は per-letter-sum (+ Fano slack) を呼び出し側が渡す scalar 形 (max over p は外出し、Line A 同様)。

> **Parent**:
> - [`textbook-roadmap.md`](../textbook-roadmap.md) §「Tier 3 — T3-F. Relay Channel + Cut-set bound (Cover-Thomas Ch.15.7 / 15.10)」

## 要点 (将来再利用しうる設計のみ)

- 採った形: outer bound only + scalar form `relayCutsetBound (Ib Im : ℝ) := min Ib Im`。joint pmf 上の `sSup` (max over `p(x,x₁)`) は呼び出し側に外出しすることで `IsCompact + exists_isMaxOn` の plumbing を回避する設計。
- 雛形は T3-D Wyner-Ziv converse の statement-level hypothesis pass-through pattern。broadcast-cut / MAC-cut / composite rate bound / relay measurability / inner bound (DF/CF) を全て hypothesis pass-through ないし scope-out する判断だった。
- inner bound (decode-and-forward / compress-and-forward) は当初から完全 scope-out (random binning + jointly typical decoder + n-letter AEP で大規模)。
