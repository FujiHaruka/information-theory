# T3-C Broadcast Channel (degraded) Capacity Region ムーンショット計画 🌙

**Status**: degraded ✅ CLOSED / 一般 BC (Marton inner bound) ✅ CLOSED — degraded BC capacity region (Cover–Thomas Thm 15.6.2) は **converse + achievability 両側 genuine closure 済**: converse headline `bc_converse` (auxiliary-variable 容量領域 membership、核 `bc_input_singleletterize` / `bc_singleletterize_bound₁`、L-BC2 再開) + achievability headline `bc_achievability` (superposition inner bound、2026-07-03 relay closure) がともに `@audit:ok`・`InformationTheory.lean` 登録済 (子 [`bc-degraded-converse-plan.md`](bc-degraded-converse-plan.md) / [`bc-achievability-plan.md`](bc-achievability-plan.md)、`#print axioms` sorryAx-free)。achievability の最終ゲート = degradedness superadditivity `bc_degraded_infoJoint_ge` (`bcInfo₁+bcInfo₂ ≤ bcInfoJoint`) を stochastic Markov `U→Y₁→Y₂` 自作 + 既存 DPI `mutualInfo_le_of_markov` で closure (撤退スロット L-BC1/L-BC3 未使用)。**L-BC5 (一般 BC + Marton) はユーザー指示で解除** → 子 [`marton-inner-bound-plan.md`](marton-inner-bound-plan.md) で追跡し、**Phase 0–8 完了 = headline `marton_achievability` (EGK Thm 8.3、private message のみ) が proof-done**。bookkeeping (README 定理表 / proof-log / WZ 再配線) まで消化して子 plan は CLOSED、生きた撤退ラインは 0。Körner–Marton は scope-out 継続 (textbook-roadmap Ch.15)。**一般 BC の外界フレームは進行中** (下記「後続」)。
**SoT**: `docs/textbook-roadmap.md` Ch.15 + 子 plan。詳細履歴は git。

**後続 (進行中)**: 一般 BC の足場は子 [`bc-general-region-plan.md`](bc-general-region-plan.md) で
Phase 1 (操作的容量領域 = 主語) / Phase 3 (協調外界) / Phase 4a (UV 単一文字化、floating 形) /
**Phase 4b (UV 外界の集合化 + 操作的包含) まで完了**。headline
`bc_capacity_subset_uv : bcCapacityRegion W ⊆ bcOuterRegionUV W` が明示仮説 `W` + `[IsMarkovKernel W]`
のみの**全平面版** (第一象限制約なし) で成立し、挟み込みは Phase 3 の `bcOuterRegionCoop` 版と
**2 本並立**になった。実装は `ChannelCoding/CodeToAmbient.lean` (MAC/BC 共有層) +
`BroadcastChannel/OuterBoundUV/{Bridge,Region,Assembly,Quantization}.lean` +
`BroadcastChannel/Superposition{TimeShare,FullSupport}.lean` + `Shannon/CondMutualInfoMixture.lean` の
8 ファイル (いずれも 1500 行ガイド内)。
**本線は Phase 5 (一致クラスの拡張)** で、定義段 (`BroadcastChannel/Classes.lean` 新設 =
`IsBCLessNoisy` / `IsBCMoreCapable` / `IsBCSemiDeterministic` + 包含鎖
`degraded ⊆ less noisy ⊆ more capable`、内界 `martonRegion` の第一象限制約も除去して符号規約を統一) /
内外の橋 S1–S6 (`OuterBoundUV/MartonBridge.lean` 新設、到達点は `@[entry_point]`
`marton_region_subset_uv`) / Phase 2 の最小完遂 P1–P3 (`BroadcastChannel/MartonUnion.lean` 新設 =
`ULift.{u} (Fin (k+1))` 上の `martonRegionUnion` / `martonRegionUnionFS`) まで完遂済。

**🔄 経路変更 — 内界の選択がクラスごとに変わる**: 等号の次手としていた逆包含
`bcOuterRegionUV ⊆ martonRegionUnionFS` は**偽**と判定された (劣化 BSC 対 `q=0.1`, `p=0.25` の
数値反例。確定事実の台帳 [`bc-facts.md`](bc-facts.md)、再検証スクリプトは
`bc-marton-union-gap-check.py`)。`martonRegionUnion` は EGK Thm 8.3 の共通補助変数 `U₀` を持たない
形なので、**劣化 BSC 対ですら `martonRegionUnionFS ⊊ bcCapacityRegion`**。⟹ 等号を狙うクラスでは
内界を **superposition** に差し替え (`BroadcastChannel/SuperpositionRegion.lean` 新設 =
`bcSuperpositionRegionFullSupport` + `@[entry_point]` 2 本、達成側は `bc_achievability` の本体を
degradedness 非依存の共通形 `bc_achievability_of_rate_lt` へ factor out して再利用。
**`bc_achievability` の署名・結論は逐語不変**)、
`bcSuperpositionRegionFullSupport ⊆ bcCapacityRegion ⊆ bcOuterRegionUV` を **less noisy の言葉で**
並べた (S0–S2 ✅ 全段 proof done、両ゲート通過)。逆包含も **S3 (情報量スロットの同定 3 本) /
S4 (`IsUVChannelLaw` からの Markov 鎖 3 本 + 四つ組法) / S5 (補助の有限量子化 + 裾評価、
`OuterBoundUV/Quantization.lean` 新設) / S6 (時分割の補助への吸収、
`BroadcastChannel/SuperpositionTimeShare.lean` 新設 = 外界の 3 不等式から達成側の対 `(pU, K)` を
構成して返す `exists_bcInfo_ge_of_lessNoisy_of_isUVChannelLaw` まで到達) / S7 (全支持への摂動、
`BroadcastChannel/SuperpositionFullSupport.lean` 新設 = その対を全支持の対へ slack `δ` 以内で
置き換え、内界 union への着地まで運ぶ) が proof done** で、**次の一手は S8** (逆包含の組み立て +
headline 等号、残り ~90 行)。
Marton union 側の順包含 `martonRegionUnion_subset_uv` は一般 BC の内界としてそのまま生きている。
一般 BC 容量領域の特徴づけ自体は未解決問題なので、内外一致は計画の Phase 外。

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
| [`bc-general-region-plan.md`](bc-general-region-plan.md) | 一般 BC 容量領域フレーム (操作的容量領域の定義 → 協調外界 → UV outer bound → 一致クラス拡張) | 進行中 🚧 — Phase 1 ✅ (`BCAchievable` / `bcCapacityRegion`) / Phase 3 ✅ (`bcOuterRegionCoop`、Wolfowitz strong converse の対偶で ambient 構成を迂回) / Phase 4a ✅ (`bc_uv_converse` = Nair–El Gamal 単一文字化、**degradedness 前提なし**、核は新規自作 `csiszar_sum_identity_cond`) / **Phase 4b ✅ CLOSED** (headline `bc_capacity_subset_uv` を**全平面版**で達成。M0 在庫 [`bc-uv-operational-inventory.md`](bc-uv-operational-inventory.md) の S1–S8-b を全消化。union を無制約に取ると外界が平面全体に退化する反例 class は `IsUVChannelLaw` = 1 本の合成積恒等式で閉じた。**外界に符号制約を入れなかった判断が退化被覆のコストを約 15 行に決めた**成功要因の記録あり) / **Phase 2 🔄** 最小完遂 P1–P3 ✅ (M0 在庫 [`bc-phase2-union-inventory.md`](bc-phase2-union-inventory.md)、`bcAuxAlphabet = ULift.{u} (Fin (k+1))` で `IsBCLessNoisy` の `Type u` 量化を 0 行で吸収)、**拡張 P4–P7 📋 は経路変更で「等号の前提」ではなくなった** / **本線 = Phase 5 🚧**: 定義段 ✅ (`Classes.lean` 新設、M0 在庫 [`bc-phase5-class-inventory.md`](bc-phase5-class-inventory.md)) / 内外の橋 S1–S6 ✅ (`MartonBridge.lean` 新設、M0 在庫 [`bc-inner-outer-bridge-inventory.md`](bc-inner-outer-bridge-inventory.md)、到達点 `marton_region_subset_uv`。「橋は `.toReal` の同定 1 本で足りる」は 3/4 だけ正しく、和レートは内界 1 本 対 外界 2 本で別汎関数ゆえ情報量不等式の自作 ~257 行が要った) / **等号 🔄 経路変更** (M0 在庫 [`bc-lessnoisy-equality-inventory.md`](bc-lessnoisy-equality-inventory.md)、Mathlib の壁 0 件): 内界を Marton union から **superposition** へ差し替え、**S0–S7 ✅ 全段 proof done** (`06817339`…`a97fde13` / `102d514a` `28aafa87` / `c3508204` `89daa826` `47933abd` / `70fc424e` `308f7c15` `dd981e01`、`SuperpositionRegion.lean` 新設 + 達成側を `bc_achievability_of_rate_lt` へ factor out。S3 = スロット同定 3 本 41 行 / S4 = Markov 鎖 3 本 + 四つ組法 74 行 (**どちらも自作した数学は 0 行** = 既存部品の合成) / S5 = 補助の有限量子化 + 裾評価、`OuterBoundUV/Quantization.lean` 新設 21 decl 289 行 (M0 在庫 [`bc-s5-quantization-inventory.md`](bc-s5-quantization-inventory.md)、見積 280 に対しほぼ的中) / S6 = 時分割の補助への吸収、`BroadcastChannel/SuperpositionTimeShare.lean` 新設 32 decl 545 行 (M0 在庫 [`bc-s6-timesharing-inventory.md`](bc-s6-timesharing-inventory.md)、見積 440 に対し +24%。到達点 `exists_bcInfo_ge_of_lessNoisy_of_isUVChannelLaw` は外界の 3 不等式から達成側の対 `(pU, K)` を**実際に構成して**返し、仮説は `hln` / `IsUVChannelLaw` / 3 不等式のみ。**自作した数学は 3 本 45 行だけ**) / S7 = 全支持への摂動、`BroadcastChannel/SuperpositionFullSupport.lean` 新設 44 decl 802 行 (`560c3399` `069c6016`、M0 在庫 [`bc-s7-fullsupport-inventory.md`](bc-s7-fullsupport-inventory.md) 401 行 / probe 745 行 compile 通過)。到達点は `@[entry_point]` 2 本 (対レベルの `exists_fullSupport_bcInfo_ge` と S6 と合成済の `exists_fullSupport_bcInfo_ge_of_lessNoisy_of_isUVChannelLaw`) + 内界 union への着地版 `sub_mem_bcSuperpositionRegionFullSupport_of_lessNoisy_of_isUVChannelLaw`。honesty all OK / style PASS)、**次の一手は S8** (~90 行: `m → ∞` と `δ → 0` の 2 重極限 + closure + headline 等号。**S5 の裾評価 3 本を消費するのはここ**)。**⚠ 親の旧記述 2 点の訂正**: (i) S7 の見積 `~120 行` は実測 802 行に対し**約 6.5 倍の外れ**だった (在庫 probe が着手前に ~780 行へ上方修正し実測はその帯の中)。(ii)「**摂動対象は `(pU, K)` ではなく時分割済の五つ組法 `ν'`**」は内部実装としては正しいが**署名の高さとしては誤り** — S6 の到達点は `ν` を存在量化して捨てるので法 → 法では合成できず、正解は「headline は対レベル、対から五つ組を建て直す糊 (~45 行) を内部に閉じ込める」で、結果 **S6 は署名変更ゼロの黒箱**のまま残った。**見積り精度の教訓 (子の判断ログ 20 / 23)**: 在庫の probe 行数は「数学の行数」をよく予測するが「ファイルの行数」は予測せず、**probe を持たない plan の粗見積りは桁で外れうる**。**撤退ライン**: active は L-BCO2 / L-BCO3 / L-BCO7 (semi-deterministic、判定対象は経路変更で `bc_achievability_of_rate_lt` の全支持 3 本へ移った) / **L-BCO9 (S5 / S6 / S7 の 3 段連続で不発動が確定 ⟹ 発動判定の担い手は S8 のみに移った。閉じないときは逆包含を `sorry` + `@residual(plan:bc-lessnoisy-converse-quantization)` で署名保持)** の 4 本。L-BCO1 / L-BCO4 / L-BCO5 / L-BCO6 は不発動、**L-BCO8 は無効化** — 逆包含 `bcOuterRegionUV ⊆ martonRegionUnionFS` が偽と判定されたので枠組みごと失効し、退避先だった「`sorry` で署名を保つ」は**偽の命題を署名に残すことになるため使用禁止**。**後続作業 A (`Assembly.lean` 1588 → 851 行の二段分割) / F-a (`isMarkovChain_map_comp` の `CodeToAmbient.lean:496` への上流移動 = S4 の構造的前提だった) / F-12 (四つ組法を `IsUVChannelLaw.map_auxiliary_input_output` へリネーム) は完了**、残る B–F (命名 / 汎用補題の置換統合 / 各 leg が立てた flag。S5–S7 の style ゲートは汎用補題の置き場 = F-15 (**S7 で +4 = 計 9 本、import 循環の検討が要る一括タスク**) / 規約どうしの衝突 = F-17 (**4 度目の発火。今回は機構が特定された** — 再燃の原因は規約文 `docs/rules/docstrings.md` item 1 の括弧が S6 の決着に追随していないことで、恒久解は括弧を `@[entry_point]` のみに直すこと。起票先は `docs/rules/` 側) / `Superposition*` クラスタのサブディレクトリ昇格 = F-19 (**発火条件を満たした** — 3 ファイル 1556 行 ⟹ 在庫・実装・style の 3 者が「S8 と同 leg」で一致) / 内ループの `lake env lean` が一部 linter に盲目 = F-20 (**S7 で実測が裏付け** — `lake env lean` 沈黙に対し `lake build` が計 19 件 ⟹ 実装 leg の検証バーに `lake build <module>` を含めるのを family の既定手に) / **S7 の重複 2 件 = F-21 (`uvConstLaw` は S7 の `uvLawOfInput` の dirac 特殊化、`rfl` で通ることを機械確認。import 変更なしで Region 側 4 decl ~45 行が消える) / F-22 (S6 の分岐クラスタは S7 の一般混合の特殊化、3 本が証明本体まで逐語重複 ~60 行)** を追加提起。**F-16 (`Quantization.lean` の orphan 懸念) は S6 が同ファイルの 4 本を消費して決着**) は F-19 / F-21 / F-22 が S8 と同 leg になるほかは Phase 5 の前提ではない。確定事実の台帳は [`bc-facts.md`](bc-facts.md) (現在 1 エントリ = Marton union の負の判定) |
| [`marton-inner-bound-plan.md`](marton-inner-bound-plan.md) | L-BC5 解除 = 一般 (non-degraded) BC の Marton inner bound (EGK Thm 8.3、private message のみ) | CLOSED ✅ (**Phase 0–8 完了**) — `marton_achievability` (`Marton/Achievability.lean`、`@[entry_point]` + `@audit:ok`、`#print axioms` sorryAx-free、root+README Ch.15 登録済) が厳密不等号 3 本 `R₁<I(V₁;Y₁)` / `R₂<I(V₂;Y₂)` / `R₁+R₂<I(V₁;Y₁)+I(V₂;Y₂)−I(V₁;V₂)` の達成可能性を無条件に与える (入力は一般カーネル `K : Kernel (V₁×V₂) α` 形。決定的 `x=f(v₁,v₂)` 版は full support 前提と両立せず直接の系にはならない)。機構: 抽象 second-moment 核 + 共分散の鋭化 (sum-rate 制約の要) + Fourier–Motzkin + mutual covering の weak/strong 両版 + 受信機ごとに分岐する 3 本入れ子の半径 + 3 段アンサンブルを 2 段 pigeonhole へ再結合。生きた撤退ラインは 0。Phase 8 bookkeeping (README 定理表 / [proof-log](../proof-logs/proof-log-marton-inner-bound.md) / WZ `Concentration.lean` を `Shannon/ConditionalAEP.lean` へ再配線) まで消化済 |
