# T3-C Broadcast Channel (degraded) Capacity Region ムーンショット計画 🌙

**Status**: degraded ✅ CLOSED / 一般 BC (Marton inner bound) ✅ CLOSED — degraded BC capacity region (Cover–Thomas Thm 15.6.2) は **converse + achievability 両側 genuine closure 済**: converse headline `bc_converse` (auxiliary-variable 容量領域 membership、核 `bc_input_singleletterize` / `bc_singleletterize_bound₁`、L-BC2 再開) + achievability headline `bc_achievability` (superposition inner bound、2026-07-03 relay closure) がともに `@audit:ok`・`InformationTheory.lean` 登録済 (子 [`bc-degraded-converse-plan.md`](bc-degraded-converse-plan.md) / [`bc-achievability-plan.md`](bc-achievability-plan.md)、`#print axioms` sorryAx-free)。achievability の最終ゲート = degradedness superadditivity `bc_degraded_infoJoint_ge` (`bcInfo₁+bcInfo₂ ≤ bcInfoJoint`) を stochastic Markov `U→Y₁→Y₂` 自作 + 既存 DPI `mutualInfo_le_of_markov` で closure (撤退スロット L-BC1/L-BC3 未使用)。**L-BC5 (一般 BC + Marton) はユーザー指示で解除** → 子 [`marton-inner-bound-plan.md`](marton-inner-bound-plan.md) で追跡し、**Phase 0–8 完了 = headline `marton_achievability` (EGK Thm 8.3、private message のみ) が proof-done**。bookkeeping (README 定理表 / proof-log / WZ 再配線) まで消化して子 plan は CLOSED、生きた撤退ラインは 0。Körner–Marton は scope-out 継続 (textbook-roadmap Ch.15)。**一般 BC の外界フレームは進行中 — うち less noisy クラスの容量領域は 2026-07-28 に等号で閉じた** (`bc_lessNoisy_capacity_eq_uv`、下記「後続」)。
**SoT**: `docs/textbook-roadmap.md` Ch.15 + 子 plan。詳細履歴は git。

**後続 (進行中)**: 一般 BC の足場は子 [`bc-general-region-plan.md`](bc-general-region-plan.md)。

**🎉 moonshot の到達 — less noisy BC の容量領域が単一文字式で閉じた (Phase 5 本線、S0–S8 全段
proof done)**: `@[entry_point]` **`bc_lessNoisy_capacity_eq_uv : bcCapacityRegion W = bcOuterRegionUV W`**
(`BroadcastChannel/Superposition/Assembly.lean`、明示仮説は `hW` = 全出力対に正の質量 + `hln` =
`IsBCLessNoisy W` のみ)。挟み込み `内界 ⊆ bcCapacityRegion ⊆ 外界` を作るのが本計画の当初目標
だったが、**degraded より真に広いクラスで挟み込みが等号に潰れた**。等号の心臓である逆包含
`@[entry_point]` `bc_lessNoisy_uv_subset_superposition` は `hW` すら要求しない (`hW` が要るのは
内界を符号に落とす段だけ)。`IsBCLessNoisy` は両領域を一切参照しないチャネルレベルの述語なので
load-bearing ではなく、3 本とも `#print axioms` = `[propext, Classical.choice, Quot.sound]`。

そこまでの土台: Phase 1 (操作的容量領域 = 主語) / Phase 3 (協調外界) / Phase 4a (UV 単一文字化、
floating 形) / **Phase 4b** headline `bc_capacity_subset_uv` の**全平面版** (明示仮説は `W` +
`[IsMarkovKernel W]` のみ、第一象限制約なし) / Phase 5 定義段 (`BroadcastChannel/Classes.lean` =
`IsBCLessNoisy` / `IsBCMoreCapable` / `IsBCSemiDeterministic` + 包含鎖
`degraded ⊆ less noisy ⊆ more capable`) / 内外の橋 S1–S6 (`OuterBoundUV/MartonBridge.lean`、到達点は
`@[entry_point]` `marton_region_subset_uv`) / Phase 2 の最小完遂 P1–P3
(`BroadcastChannel/MartonUnion.lean`)。実装は `ChannelCoding/CodeToAmbient.lean` (MAC/BC 共有層) +
`BroadcastChannel/OuterBoundUV/{Bridge,Region,Assembly,Quantization}.lean` +
`BroadcastChannel/Superposition/{Region,TimeShare,FullSupport,Assembly}.lean` +
`Shannon/CondMutualInfoMixture.lean` (いずれも 1500 行ガイド内)。

**🔄 経路変更 — 内界の選択がクラスごとに変わる (等号が成立した理由)**: 等号の次手としていた逆包含
`bcOuterRegionUV ⊆ martonRegionUnionFS` は**偽**と判定された (劣化 BSC 対 `q=0.1`, `p=0.25` の
数値反例。確定事実の台帳 [`bc-facts.md`](bc-facts.md)、再検証スクリプトは
`bc-marton-union-gap-check.py`)。`martonRegionUnion` は EGK Thm 8.3 の共通補助変数 `U₀` を持たない
形なので、**劣化 BSC 対ですら `martonRegionUnionFS ⊊ bcCapacityRegion`**。⟹ 等号を狙うクラスでは
内界を **superposition** に差し替え、達成側は `bc_achievability` の本体を degradedness 非依存の
共通形 `bc_achievability_of_rate_lt` へ factor out して再利用した (**`bc_achievability` の署名・
結論は逐語不変**)。Marton union 側の順包含 `martonRegionUnion_subset_uv` は一般 BC の内界として
そのまま生きている。一般 BC 容量領域の特徴づけ自体は未解決問題なので、内外一致は計画の Phase 外。

**後片付けは完了**: README 定理表への登録 (`b545cbd7`) と、`Superposition/` サブディレクトリ昇格 +
重複解消 + `ℝ≥0∞` イディオムの refactor leg (`4ea35cc0`…`d0ac3aed`、5 ファイル / **−85 行**、
新しい数学 0 行、style PASS)。**残作業は子 plan §推奨実行順の 5 本**: (1) proof-log →
(2) more capable の等号 (3 field の新 structure が要る) → (3) degraded との接続 →
(4) Phase 2 の P4–P7。(5) semi-deterministic は L-BCO7 で「外界側だけで止める」と判断済。

> **Parent**:
> - [`textbook-roadmap.md`](../textbook-roadmap.md) §「Tier 3 — T3-C. Broadcast Channel (degraded) (Cover–Thomas Ch.15.6)」

## 要点 (再利用しうる設計判断)

- **T3-B MAC を verbatim 雛形**として domain/codomain swap + auxiliary RV `U` 圧縮で導出: `BroadcastChannel := Kernel α (β₁ × β₂)`、`BroadcastCode` は encoder un-curry (1 joint) + decoder 2 分離、`InBCCapacityRegion` は 2 inequality bundle (`R₂ ≤ I_u`, `R₁ ≤ I_xy`)。BC は 2 receiver 非対称ゆえ region `swap` は無効 (mono のみ)。
- **撤退ライン L-BC1〜L-BC5** (frozen slug、他 plan が参照): L-BC1 joint typicality multi-receiver body / L-BC2 Fano + chain rule **(再開 → genuine closure 済、子 [`bc-degraded-converse-plan.md`](bc-degraded-converse-plan.md)、headline `bc_converse`、Route B = entropy-difference / term-by-term degradedness)** / L-BC3 inner bound existence pass-through / L-BC4 outer bound `InBCCapacityRegion` pass-through / L-BC5 一般 (non-degraded) BC + Marton / Körner-Marton は完全 scope-out **(Marton 部分は解除・達成 → 子 [`marton-inner-bound-plan.md`](marton-inner-bound-plan.md) の headline `marton_achievability`。Körner–Marton は scope-out 継続)**。
- rate-bound 系の proof done closure は子 plan [`broadcast-channel-signature-rewrite-plan.md`](broadcast-channel-signature-rewrite-plan.md) 参照。

## Sub-plan 一覧 (backlink — plan_lint 双方向照合点)

| 子 plan | 担当 | 状態 |
|---|---|---|
| [`bc-degraded-converse-plan.md`](bc-degraded-converse-plan.md) | L-BC2 degraded converse single-letterization (`bc_converse` / `bc_input_singleletterize`、Route B) | CLOSED ✅ (genuine、`@audit:ok`、root 登録済) |
| [`broadcast-channel-signature-rewrite-plan.md`](broadcast-channel-signature-rewrite-plan.md) | BC rate-bound declaration の defect → genuine signature rewrite | CLOSED ✅ |
| [`bc-achievability-plan.md`](bc-achievability-plan.md) | BC (degraded) achievability = superposition inner bound (`bc_achievability`、Cover–Thomas Thm 15.6.2 達成側) | CLOSED ✅ (genuine、`bc_achievability` `@audit:ok`、`#print axioms` sorryAx-free、root+README Ch.15 登録済) — two-tier superposition random coding (E0 vanishing typicality-LLN + per-receiver Bonferroni + averaged swap + two-tier pigeonhole + ε-selection)、最終ゲート `bc_degraded_infoJoint_ge` (degradedness superadditivity `bcInfo₁+bcInfo₂ ≤ bcInfoJoint`) を stochastic Markov `U→Y₁→Y₂` 自作 + DPI で closure。撤退スロット L-BC1/L-BC3 未使用 |
| [`bc-general-region-plan.md`](bc-general-region-plan.md) | 一般 BC 容量領域フレーム (操作的容量領域の定義 → 協調外界 → UV outer bound → 一致クラス拡張) | 進行中 🚧、**Phase 5 の本線は到達済** — Phase 1 ✅ (`BCAchievable` / `bcCapacityRegion`) / Phase 3 ✅ (`bcOuterRegionCoop`、Wolfowitz strong converse の対偶で ambient 構成を迂回) / Phase 4a ✅ (`bc_uv_converse` = Nair–El Gamal 単一文字化、**degradedness 前提なし**、核は新規自作 `csiszar_sum_identity_cond`) / **Phase 4b ✅ CLOSED** (headline `bc_capacity_subset_uv` を**全平面版**で達成。union を無制約に取ると外界が平面全体に退化する反例 class は `IsUVChannelLaw` = 1 本の合成積恒等式で閉じた。**外界に符号制約を入れなかった判断が退化被覆のコストを約 15 行に決めた**) / **Phase 2 🔄** 最小完遂 P1–P3 ✅ (`bcAuxAlphabet = ULift.{u} (Fin (k+1))` で `IsBCLessNoisy` の `Type u` 量化を 0 行で吸収)、**拡張 P4–P7 📋 は経路変更で「等号の前提」ではなくなった** / **Phase 5 🚧**: 定義段 ✅ (`Classes.lean`) / 内外の橋 S1–S6 ✅ (`MartonBridge.lean`、到達点 `marton_region_subset_uv`) / **less noisy の等号 ✅ 到達 — S0–S8 全段 proof done** (`06817339`…`558b3fca`。内界を Marton union から **superposition** へ差し替え、S3 スロット同定 / S4 Markov 鎖 + 四つ組法 (**どちらも自作した数学 0 行**) / S5 量子化 + 裾評価 (`OuterBoundUV/Quantization.lean`) / S6 時分割の補助への吸収 (`Superposition/TimeShare.lean`) / S7 全支持への摂動 802 行 (`Superposition/FullSupport.lean`) / **S8 組み立て + headline 等号 163 行 + 上流移動 15 行 = 178 行、自作した数学は 0 行** (`Superposition/Assembly.lean`)。全 leg で **Mathlib の壁 0 件**、style PASS、honesty は S0–S2 で all OK・以降は launch 条件外)。到達点 3 本は `@[entry_point]` `bc_lessNoisy_uv_subset_superposition` (逆包含、**`hW` を要求しない**) / `@[entry_point]` `bc_lessNoisy_capacity_eq_uv` (`bcCapacityRegion W = bcOuterRegionUV W`) / bare `bc_lessNoisy_superposition_eq_capacity`、いずれも `#print axioms` sorryAx-free。**残作業は子 §推奨実行順の 5 本** (proof-log → more capable → degraded 接続 → Phase 2 P4–P7 → semi-deterministic は判断済)。**見積り精度の教訓 (子の判断ログ 23 / 24)**: plan の粗見積りは S7 で 6.5 倍・S8 で約 2 倍外れ、どちらも実測は**在庫 probe の帯の中**に入った ⟹ 新しい数学を含む leg は在庫 leg から始める。加えて S8 の擬似 Lean は**入口が要求する仮説を 1 本落としていた** (在庫が plan の誤りを見つけたのは S6 / S7 / S8 の 3 leg 連続) ⟹ 「残るのは組み立てだけ」は入口の仮説の本数で検算する。refactor leg では逆向きに**在庫の予測が外れた** (重複は 2 本でなく 3 本 / `inferInstance` は非 reducible な `def` で落ちない) ⟹ probe の「機械確認済」が保証するのは確かめた等式だけで、完全性 (ちょうど N 本) にも自動性 (探索が見つける) にも及ばない (子の判断ログ 26)。**撤退ライン**: active は L-BCO2 / L-BCO3 (残る判定対象は more capable のみ) / L-BCO7 (semi-deterministic、判定対象は `bc_achievability_of_rate_lt` の全支持 3 本) の **3 本**。L-BCO1 / L-BCO4 / L-BCO5 / L-BCO6 は不発動、**L-BCO9 は S5 / S6 / S7 / S8 の 4 段連続で不発動のまま retire**、**L-BCO8 は無効化** (逆包含 `bcOuterRegionUV ⊆ martonRegionUnionFS` が偽と判定され枠組みごと失効。退避先だった「`sorry` で署名を保つ」は**偽の命題を署名に残すことになるため使用禁止**)。**後続作業** A / F-a / F-12 / **F-5 / F-19 / F-21 / F-22 / F-c** は完了、残る B–F は Phase 5 の前提ではない (F-15 汎用補題の置き場 計 11 本 / F-17 規約衝突の恒久解 = `docs/rules/` 側への起票 / F-20 = 実装 leg の検証バーに `lake build <module>`・在庫 probe 段階から linter 条件を有効にする、を family の既定手に / refactor leg が新たに立てた **F-23** `isUVChannelLaw_iff` の右辺重複 (statement 変更なので判断ログ 9 の特徴づけ点検が先) / **F-24** `uvMixLaw` API の 2 ファイル分断 / **F-25** BC 族外に残る `ℝ≥0∞` イディオム 2 箇所)。確定事実の台帳は [`bc-facts.md`](bc-facts.md) (現在 1 エントリ = Marton union の負の判定) |
| [`marton-inner-bound-plan.md`](marton-inner-bound-plan.md) | L-BC5 解除 = 一般 (non-degraded) BC の Marton inner bound (EGK Thm 8.3、private message のみ) | CLOSED ✅ (**Phase 0–8 完了**) — `marton_achievability` (`Marton/Achievability.lean`、`@[entry_point]` + `@audit:ok`、`#print axioms` sorryAx-free、root+README Ch.15 登録済) が厳密不等号 3 本 `R₁<I(V₁;Y₁)` / `R₂<I(V₂;Y₂)` / `R₁+R₂<I(V₁;Y₁)+I(V₂;Y₂)−I(V₁;V₂)` の達成可能性を無条件に与える (入力は一般カーネル `K : Kernel (V₁×V₂) α` 形。決定的 `x=f(v₁,v₂)` 版は full support 前提と両立せず直接の系にはならない)。機構: 抽象 second-moment 核 + 共分散の鋭化 (sum-rate 制約の要) + Fourier–Motzkin + mutual covering の weak/strong 両版 + 受信機ごとに分岐する 3 本入れ子の半径 + 3 段アンサンブルを 2 段 pigeonhole へ再結合。生きた撤退ラインは 0。Phase 8 bookkeeping (README 定理表 / [proof-log](../proof-logs/proof-log-marton-inner-bound.md) / WZ `Concentration.lean` を `Shannon/ConditionalAEP.lean` へ再配線) まで消化済 |
