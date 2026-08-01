# T3-C Broadcast Channel (degraded) Capacity Region ムーンショット計画 🌙

**Status**: degraded ✅ CLOSED / 一般 BC (Marton inner bound) ✅ CLOSED — degraded BC capacity region (Cover–Thomas Thm 15.6.2) は **converse + achievability 両側 genuine closure 済**: converse headline `bc_degraded_converse` (auxiliary-variable 容量領域 membership、核 `bc_input_singleletterize` / `bc_singleletterize_bound₁`、L-BC2 再開) + achievability headline `bc_achievability` (superposition inner bound、2026-07-03 relay closure) がともに `@audit:ok`・`InformationTheory.lean` 登録済 (子 [`bc-degraded-converse-plan.md`](bc-degraded-converse-plan.md) / [`bc-achievability-plan.md`](bc-achievability-plan.md)、`#print axioms` sorryAx-free)。achievability の最終ゲート = degradedness superadditivity `bc_degraded_infoJoint_ge` (`bcInfo₁+bcInfo₂ ≤ bcInfoJoint`) を stochastic Markov `U→Y₁→Y₂` 自作 + 既存 DPI `mutualInfo_le_of_markov` で closure (撤退スロット L-BC1/L-BC3 未使用)。**L-BC5 (一般 BC + Marton) はユーザー指示で解除** → 子 [`marton-inner-bound-plan.md`](marton-inner-bound-plan.md) で追跡し、**Phase 0–8 完了 = headline `marton_achievability` (EGK Thm 8.3、private message のみ) が proof-done**。bookkeeping (README 定理表 / proof-log / WZ 再配線) まで消化して子 plan は CLOSED、生きた撤退ラインは 0。Körner–Marton は scope-out 継続 (textbook-roadmap Ch.15)。**一般 BC の外界フレームは進行中 — less noisy / more capable の 2 クラスで容量領域が等号で閉じた** (`bc_lessNoisy_capacity_eq_uv` / `bc_moreCapable_capacity_eq_uv`、下記「後続」)。**Phase 5 は完遂** (degraded 接続 = 古典形 converse の符号への着地 `bc_degraded_converse_from_code` まで)、**Phase 2 の拡張 P4–P7 も完遂したので子 plan は全 Phase 完遂**。子 §後続作業 も 9 leg relay で一括消化し、残るのは B-3 / B-4 / C-1 / C-2 / C-4 / D-2 / E-2 / F-14 / F-23 / G-1 の 10 項目のみで、いずれも到達目標の前提ではない。
**SoT**: `docs/textbook-roadmap.md` Ch.15 + 子 plan。詳細履歴は git。

**後続 (進行中)**: 一般 BC の足場は子 [`bc-general-region-plan.md`](bc-general-region-plan.md)。

**🎉 moonshot の到達 — more capable BC の容量領域が単一文字式で閉じた (Phase 5 本線)**:
`@[entry_point]` **`bc_moreCapable_capacity_eq_uv : bcCapacityRegion W = bcOuterRegionUV W`**
(`BroadcastChannel/Superposition/MoreCapable.lean`、明示仮説は `hW` = 全出力対に正の質量 + `hmc` =
`IsBCMoreCapable W` のみ)。挟み込み `内界 ⊆ bcCapacityRegion ⊆ 外界` を作るのが本計画の当初目標
だったが、**degraded より真に広い 2 クラスで挟み込みが等号に潰れた** (先行する less noisy 版
`bc_lessNoisy_capacity_eq_uv` は `IsBCLessNoisy.isBCMoreCapable` 経由で本 3 本の系になる)。等号の
心臓である逆包含 `@[entry_point]` `bc_moreCapable_uv_subset_superposition` は `hW` すら要求しない
(`hW` が要るのは内界を符号に落とす段だけ)。**クラス述語はどちらも両領域を一切参照しない
チャネルレベルの述語なので load-bearing ではない** (署名走査での判定。`sorryAx` 非依存の側は
`#print axioms` で毎回引き直す — 散文にキャッシュしない)。

そこまでの土台: Phase 1 (操作的容量領域 = 主語) / Phase 3 (協調外界) / Phase 4a (UV 単一文字化、
floating 形) / **Phase 4b** headline `bc_capacity_subset_uv` の**全平面版** (明示仮説は `W` +
`[IsMarkovKernel W]` のみ、第一象限制約なし) / Phase 5 定義段 (`BroadcastChannel/Classes.lean` =
`IsBCLessNoisy` / `IsBCMoreCapable` / `IsBCSemiDeterministic` + 包含鎖
`degraded ⊆ less noisy ⊆ more capable`) / 内外の橋 S1–S6 (`OuterBoundUV/MartonBridge.lean`、到達点は
`@[entry_point]` `marton_region_subset_uv`) / Phase 2 の最小完遂 P1–P3
(`BroadcastChannel/MartonUnion.lean`) / **less noisy の等号 S0–S8 全段** (子 plan が SoT)。実装は
`ChannelCoding/CodeToAmbient.lean` (MAC/BC 共有層) +
`BroadcastChannel/OuterBoundUV/{Bridge,Region,Assembly,Quantization}.lean` +
`BroadcastChannel/Superposition/{Region,TimeShare,FullSupport,Assembly,MoreCapable}.lean` +
`Shannon/{CondMutualInfoMixture,MutualInfoReencoding,MutualInfoFiniteRange,BoolLaw}.lean` +
`Probability/{Mixture,SingletonMass}.lean` (いずれも 1500 行ガイド内。後 4 者は後続作業 relay で
BC / MAC namespace から昇格した汎用層で、**この昇格で BC → MAC の import 辺は消滅した**)。

**🔄 経路変更 — 内界の選択がクラスごとに変わる (等号が成立した理由)**: 等号の次手としていた逆包含
`bcOuterRegionUV ⊆ martonRegionUnionFS` は**偽**と判定された (劣化 BSC 対 `q=0.1`, `p=0.25` の
数値反例。確定事実の台帳 [`bc-facts.md`](bc-facts.md)、再検証スクリプトは
`bc-marton-union-gap-check.py`)。`martonRegionUnion` は EGK Thm 8.3 の共通補助変数 `U₀` を持たない
形なので、**劣化 BSC 対ですら `martonRegionUnionFS ⊊ bcCapacityRegion`**。⟹ 等号を狙うクラスでは
内界を **superposition** に差し替え、達成側は `bc_achievability` の本体を degradedness 非依存の
共通形 `bc_achievability_of_rate_lt` へ factor out して再利用した (**`bc_achievability` の署名・
結論は逐語不変**)。Marton union 側の順包含 `martonRegionUnion_subset_uv` は一般 BC の内界として
そのまま生きている。一般 BC 容量領域の特徴づけ自体は未解決問題なので、内外一致は計画の Phase 外。

**後片付けは完了**: README 定理表への登録 (`b545cbd7` / `594887a4` / `e070dae4`)、`Superposition/`
サブディレクトリ昇格 + 重複解消 + `ℝ≥0∞` イディオムの refactor leg (`4ea35cc0`…`d0ac3aed`、
5 ファイル / **−85 行**、新しい数学 0 行、style PASS)、族としての proof-log (`3d680d3e`)、第 3 スロット
`uvInfoJoint` の def 化 + ベタ書き置換 (`bb40c820`)、汎用 2 本の `Shannon/` 直下への移設 (`730844a1`)。

**✅ degraded との接続も完遂 (子 plan §推奨実行順 #3、`bf49a91d`…`86b90af1`)** — 領域レベルの
degraded 等号は more capable の**系として 6 行**で取れた (`bc_degraded_capacity_eq_uv`) ので、
本 leg の価値はそこではなく**古典形 converse (Cover–Thomas Thm 15.6.2) の操作的着地**にある:
`@[entry_point]` `bc_degraded_converse_from_code` (`BroadcastChannel/DegradedFromCode.lean`) が
`bcConverseAmbient c W` 上で `bc_degraded_converse` の構造前提 (`h_deg_block` / `h_memo`) を両方
discharge し、**残る明示仮説を `IsBCDegraded W` と 2 本のメッセージ数だけにした** ⟹ `Converse.lean`
の docstring が散文で主張していた「両構造前提は操作的 degraded 設定では真」が機械検証された。
副産物として汎用 5 本が `ChannelCoding/CodeToAmbient.lean` へ、append 型 Markov 鎖 2 本が
`private` 解除で `Shannon/CondEntropyMemoryless.lean` へ上がり、WynerZiv の逐語重複 2 本が消えた
(−58 行)。

**✅ Phase 2 の拡張 P4–P7 も完遂 (子 plan §推奨実行順 #4、`64a2d6ab`…`93a3a6fb`) ⟹ 子 plan は
全 Phase 完遂**。P4/P5 (四角形と union の下方集合性 / 非空性 / 凸性) と P6 (補助アルファベットの
付け替え不変性 — `martonRegion_subset_union` が**任意 universe の四角形を union に吸収する**、
⟹ **L-BCO2 が「答えた」に到達**) は `MartonUnion.lean` へ、P7 (全支持の除去) は新規
`BroadcastChannel/MartonFullSupport.lean` (242 行 / 13 decl) へ。P7 の実りは `@[entry_point]`
`martonRegionUnion_subset_capacity` = 内界 union の包含から補助側の全支持仮説 (`hpV` / `hK`) を
一様測度への摂動 + 3 情報量の連続性で落とした版で、**残る明示仮説はチャネル側の `hW` のみ**。
攻略路は **MAC 側の完全な先例** (`mac_pentagon_subset_capacityRegion_allprob` + MAC の汎用混合
一族 = 後に `Probability/Mixture.lean` へ昇格し `mixLaw` 一族となる) がそのまま効き、superposition
側 S7 の混合不等式ルートは模倣不要だった (Marton 側は全アルファベットが `Fintype` ゆえ連続性
ルートが通る)。(5) semi-deterministic は L-BCO7 で「外界側だけで止める」と判断済 (**新規作業なし**)。

**✅ 子 §後続作業 も 9 leg relay で一括消化 (`aad88f5d`…`9081cef4`)** — 死んだ宣言の削除 / 命名束 /
汎用補題の `Shannon/` · `Probability/` への昇格 (**BC → MAC の import 辺が消滅**) / 重複の一般形への
畳み込み / module doc の実態同期 / 家系横断の `entropy_le_log_card` 重複統合 / MAC の `axis` 命名衝突の
解消まで。**残るのは子 §後続作業 の B-3 / B-4 / C-1 / C-2 / C-4 / D-2 / E-2 / F-14 / F-23 / G-1 のみで、
いずれも到達目標の前提ではない** (詳細と commit は子が SoT)。

> **Parent**:
> - [`textbook-roadmap.md`](../textbook-roadmap.md) §「Tier 3 — T3-C. Broadcast Channel (degraded) (Cover–Thomas Ch.15.6)」

## 要点 (再利用しうる設計判断)

- **T3-B MAC を verbatim 雛形**として domain/codomain swap + auxiliary RV `U` 圧縮で導出: `BroadcastChannel := Kernel α (β₁ × β₂)`、`BroadcastCode` は encoder un-curry (1 joint) + decoder 2 分離、`InBCCapacityRegion` は 2 inequality bundle (`R₂ ≤ I_u`, `R₁ ≤ I_xy`)。BC は 2 receiver 非対称ゆえ region `swap` は無効 (mono のみ)。
- **撤退ライン L-BC1〜L-BC5** (frozen slug、他 plan が参照): L-BC1 joint typicality multi-receiver body / L-BC2 Fano + chain rule **(再開 → genuine closure 済、子 [`bc-degraded-converse-plan.md`](bc-degraded-converse-plan.md)、headline `bc_degraded_converse`、Route B = entropy-difference / term-by-term degradedness)** / L-BC3 inner bound existence pass-through / L-BC4 outer bound `InBCCapacityRegion` pass-through / L-BC5 一般 (non-degraded) BC + Marton / Körner-Marton は完全 scope-out **(Marton 部分は解除・達成 → 子 [`marton-inner-bound-plan.md`](marton-inner-bound-plan.md) の headline `marton_achievability`。Körner–Marton は scope-out 継続)**。
- rate-bound 系の proof done closure は子 plan [`broadcast-channel-signature-rewrite-plan.md`](broadcast-channel-signature-rewrite-plan.md) 参照。

## Sub-plan 一覧 (backlink — plan_lint 双方向照合点)

| 子 plan | 担当 | 状態 |
|---|---|---|
| [`bc-degraded-converse-plan.md`](bc-degraded-converse-plan.md) | L-BC2 degraded converse single-letterization (`bc_degraded_converse` / `bc_input_singleletterize`、Route B) | CLOSED ✅ (genuine、`@audit:ok`、root 登録済) |
| [`broadcast-channel-signature-rewrite-plan.md`](broadcast-channel-signature-rewrite-plan.md) | BC rate-bound declaration の defect → genuine signature rewrite | CLOSED ✅ |
| [`bc-achievability-plan.md`](bc-achievability-plan.md) | BC (degraded) achievability = superposition inner bound (`bc_achievability`、Cover–Thomas Thm 15.6.2 達成側) | CLOSED ✅ (genuine、`bc_achievability` `@audit:ok`、`#print axioms` sorryAx-free、root+README Ch.15 登録済) — two-tier superposition random coding (E0 vanishing typicality-LLN + per-receiver Bonferroni + averaged swap + two-tier pigeonhole + ε-selection)、最終ゲート `bc_degraded_infoJoint_ge` (degradedness superadditivity `bcInfo₁+bcInfo₂ ≤ bcInfoJoint`) を stochastic Markov `U→Y₁→Y₂` 自作 + DPI で closure。撤退スロット L-BC1/L-BC3 未使用 |
| [`bc-general-region-plan.md`](bc-general-region-plan.md) | 一般 BC 容量領域フレーム (操作的容量領域の定義 → 協調外界 → UV outer bound → 一致クラス拡張) | **全 Phase 完遂 ✅** (Phase 5 = 等号 2 クラス + degraded 接続、Phase 2 = union の API 完成)。子 §後続作業 も 9 leg relay で消化し、残るのは B-3 / B-4 / C-1 / C-2 / C-4 / D-2 / E-2 / F-14 / F-23 / G-1 のみで**いずれも到達目標の前提ではない** — Phase 1 ✅ (`BCAchievable` / `bcCapacityRegion`) / Phase 3 ✅ (`bcOuterRegionCoop`、Wolfowitz strong converse の対偶で ambient 構成を迂回) / Phase 4a ✅ (`bc_uv_converse` = Nair–El Gamal 単一文字化、**degradedness 前提なし**、核は新規自作 `csiszar_sum_identity_cond`) / **Phase 4b ✅ CLOSED** (headline `bc_capacity_subset_uv` を**全平面版**で達成。union を無制約に取ると外界が平面全体に退化する反例 class は `IsUVChannelLaw` = 1 本の合成積恒等式で閉じた。**外界に符号制約を入れなかった判断が退化被覆のコストを約 15 行に決めた**) / **Phase 2 ✅ 完遂** 最小完遂 P1–P3 (`bcAuxAlphabet = ULift.{u} (Fin (k+1))` で `IsBCLessNoisy` の `Type u` 量化を 0 行で吸収) + 拡張 P4–P7 (`64a2d6ab`…`93a3a6fb`。**経路変更で「等号の前提」ではなくなっていたが API としては完成**。P6 で **L-BCO2 が「答えた」に到達**、P7 = 新規 `MartonFullSupport.lean` 242 行で内界 union の包含から補助側の全支持仮説を落とし残る明示仮説を `hW` のみにした。**MAC の `mac_pentagon_subset_capacityRegion_allprob` が同じ定理の完全な先例**で、superposition 側 S7 の混合不等式ルートは模倣不要 = **ルートが違えば行数見積りも移らない**) / **Phase 5 ✅ 完遂**: 定義段 ✅ (`Classes.lean`) / 内外の橋 S1–S6 ✅ (`MartonBridge.lean`、到達点 `marton_region_subset_uv`) / **less noisy の等号 ✅ S0–S8 全段 proof done** (`06817339`…`558b3fca`。内界を Marton union から **superposition** へ差し替え、S5 量子化 / S6 時分割 / S7 全支持摂動 802 行 / S8 組み立て + headline) / **more capable の等号 ✅ 到達** (`4a01dff8`…`594887a4`、`Superposition/MoreCapable.lean` 909 行 = 在庫の帯 820–980 の中。到達点 3 本 `bc_moreCapable_uv_subset_superposition` (逆包含、**`hW` を要求しない**) / `bc_moreCapable_capacity_eq_uv` / bare `bc_moreCapable_superposition_eq_capacity` で、`IsBCLessNoisy.isBCMoreCapable` 経由で **less noisy の 3 本を包含する** (畳み直しは意図的に未実施 = 子 §後続作業 G-1)。設計の要は 3 点 — (a) 受け皿の **新 `structure` は不要**だった (内界は `InBCCapacityRegion` を消費していない、`dep_consumers.sh` 実測)、(b) **第 3 制約を `max p.1 0 + p.2 ≤ bcInfoJoint` と書いて `bc_achievability_of_rate_lt` の `hJlt` に逐語で合わせる**判断が**内界の達成可能性からクラス仮説を完全に落とした**、(c) 唯一の新しい数学の核は **more capable の条件付き版** `IsBCMoreCapable.condMutualInfo_le` で、これが **less noisy の逆包含が捨てていた外界の 4 本目 `sumBound₁` を第 3 制約の担い手に変えた**。全 leg で **Mathlib の壁 0 件**、style PASS、honesty は新規 `sorry` 0 のため launch 条件外) / **degraded との接続 ✅ 完遂** (`bf49a91d`…`86b90af1`、新規 `BroadcastChannel/DegradedFromCode.lean` 213 行 / 4 decl。頂点は `@[entry_point]` `bc_degraded_converse_from_code` = 古典形 converse を符号に着地、加えて 6 行の系 `bc_degraded_capacity_eq_uv`。子 plan §存在しないもの (d) を `bcConverse_degradedBlock` が解消。壁は Mathlib / in-project とも 0 件 = **BC 家系 11 leg 連続**)。**子 §推奨実行順は #1 proof-log / #2 more capable / #3 degraded 接続 / #4 Phase 2 P4–P7 / #6 後続作業 relay がすべて完了、#5 semi-deterministic は L-BCO7 で判断済 = 新規作業なし ⟹ Phase としての残りゼロ**。**見積り精度の教訓 (子の判断ログ 23 / 24 / 26)**: plan の粗見積りは S7 で 6.5 倍・S8 で約 2 倍外れ、どちらも実測は**在庫 probe の帯の中**に入った ⟹ 新しい数学を含む leg は在庫 leg から始め、**「数学 (probe 実測) / 散文・section」の 2 列**で積む (2 列に切り替えた S7 / S8 / more capable の 3 leg 連続で帯内)。**degraded 接続で初めて下端を割った** (実測 355 行 / 帯 361–456、−2%) — 主因は**同じ leg の leg A が `private` 解除で上流公開した資産と主目標の結論が逐語一致した**ことで、⟹ **在庫は移設前の状態で見積もるので、資産移設は後続 step の見積りを下振れさせる**。加えて **在庫が plan の誤りを見つけたのは S6 / S7 / S8 / more capable の 4 leg 連続** ⟹ 「残るのは組み立てだけ」は入口の仮説の本数で検算し、plan が「既存の X では受けきれない」と書いたら着手前に `dep_consumers.sh` で X の消費者を確かめる。逆向きに **probe / 事前予測が外れる軸も 3 つ**判明 (個数 = 重複は 2 本でなく 3 本 / 自動性 = `inferInstance` は非 reducible な `def` で落ちない / **波及方向** = 非 reducible 化で落ちたのは下流 consumer ではなく当の宣言自身の証明本文)。**撤退ライン**: active は **L-BCO7 のみ** (semi-deterministic、判定対象は `bc_achievability_of_rate_lt` の全支持 3 本。等号を述べない判断が済んでいるので新規作業は生まない)。L-BCO1 / L-BCO4 / L-BCO5 / L-BCO6 は不発動、**L-BCO2 は P6 で「答えた」に到達**、**L-BCO3 は最後の判定対象だった more capable が閉じて retire**、**L-BCO9 は S5–S8 の 4 段連続で不発動のまま retire**、**L-BCO8 は無効化** (逆包含 `bcOuterRegionUV ⊆ martonRegionUnionFS` が偽と判定され枠組みごと失効。退避先だった「`sorry` で署名を保つ」は**偽の命題を署名に残すことになるため使用禁止**)、**L-BCO10** (degraded 接続の `bcConverse_block_append` が閉じない) **も不発動のまま retire**。**後続作業も 9 leg relay で一括消化 ✅** (`aad88f5d`…`9081cef4`。A / F-a / F-12 / F-5 / F-19 / F-21 / F-22 / F-c / F-28 / F-15 は先行して完了済) — 死んだ宣言 2 本の削除 (B-1 / B-5) / 命名束 (B-2 / F-1 / F-3 / F-4 / F-6 / G-2) / 汎用補題の `Shannon/` · `Probability/` への昇格 (F-15 / F-24 / F-b。**BC → MAC の import 辺が消滅**) / 重複の一般形への畳み込み (D-1 / G-3 / G-4) / `IsBCDegraded` の `Basic.lean` 移設 (F-29) / `CondMutualInfoMixture.lean` の分割 (E-1) / module doc と docstring の実態同期 (F-10 / F-11 / F-d / C-3) / BC 族外の `ℝ≥0∞` イディオム (F-25) / 家系横断の `entropy_le_log_card` 重複統合 / MAC の `axis` 命名衝突の解消。**残るのは B-3 / B-4 / C-1 / C-2 / C-4 / D-2 / E-2 / F-14 / F-23 / G-1 のみで Phase 5 の前提ではない** (F-9 / F-17 / C-5 / G-5 / F-26 / F-27 / F-20 / G-6 は `docs/rules/` · `scripts/` 側への起票または family 既定手の記録)。確定事実の台帳は [`bc-facts.md`](bc-facts.md) |
| [`bc-open-problem-plan.md`](bc-open-problem-plan.md) | 未解決本体 (一般 BC の計算可能な容量領域の特徴づけ) への攻略 — **進め方 (メタプラン) のみ策定済、数学の attack は未着手**。三層 (散文 → proof-probe → 形式化) × 階段 T0–T3 × 台帳。文献側の確定: **inner = outer も outer = capacity も既知の負の結果で閉じている** (BSSC の sum rate ギャップ / NEG outer の strict suboptimality) ので、標的は新クラス・新 outer bound・計算可能性の定式化。ブランチ `bc-computable-region`。**本 relay のゴールは散文レベルの候補経路 (5 条件つき) で、形式化はスコープ外 = 次 relay**。ユーザー提供の外部ノート (未検証、`bc-external-note-tensorization.md`) が「未解決問題 = Marton 領域の**自己テンソル化**の可否」への縮約を主張したため**軸 E を優先度 1 へ昇格**し、その還元の生死を決める **L2 を本 relay の分岐点**に置いた | **進行中** 🚧 (20 leg 予算、Leg 0 = 文献 verbatim 確定が未着手) |
| [`marton-inner-bound-plan.md`](marton-inner-bound-plan.md) | L-BC5 解除 = 一般 (non-degraded) BC の Marton inner bound (EGK Thm 8.3、private message のみ) | CLOSED ✅ (**Phase 0–8 完了**) — `marton_achievability` (`Marton/Achievability.lean`、`@[entry_point]` + `@audit:ok`、`#print axioms` sorryAx-free、root+README Ch.15 登録済) が厳密不等号 3 本 `R₁<I(V₁;Y₁)` / `R₂<I(V₂;Y₂)` / `R₁+R₂<I(V₁;Y₁)+I(V₂;Y₂)−I(V₁;V₂)` の達成可能性を無条件に与える (入力は一般カーネル `K : Kernel (V₁×V₂) α` 形。決定的 `x=f(v₁,v₂)` 版は full support 前提と両立せず直接の系にはならない)。機構: 抽象 second-moment 核 + 共分散の鋭化 (sum-rate 制約の要) + Fourier–Motzkin + mutual covering の weak/strong 両版 + 受信機ごとに分岐する 3 本入れ子の半径 + 3 段アンサンブルを 2 段 pigeonhole へ再結合。生きた撤退ラインは 0。Phase 8 bookkeeping (README 定理表 / [proof-log](../proof-logs/proof-log-marton-inner-bound.md) / WZ `Concentration.lean` を `Shannon/ConditionalAEP.lean` へ再配線) まで消化済 |
