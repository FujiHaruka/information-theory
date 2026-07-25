# Shannon: 一般 BC の Marton inner bound サブ計画

> **Parent**: [`broadcast-channel-moonshot-plan.md`](broadcast-channel-moonshot-plan.md) §L-BC5 (解除)

**Status**: ✅ **headline 到達 (proof-done)** — degraded 仮定を外した一般 (non-degraded) two-receiver
broadcast channel に対する **Marton inner bound (El Gamal–Kim *Network Information Theory* Thm 8.3、
private message のみ)** を、親 plan の撤退ライン **L-BC5** を解除して形式化した。
**Phase 0–7 完了**: headline `marton_achievability` (`Marton/Achievability.lean`、`@[entry_point]`) が
0 sorry / 0 `@residual` で閉じ、2 ゲート (honesty / style) とも PASS。**生きた撤退ラインは 0**。
残るは **Phase 8 = bookkeeping** (README 定理表 / 親 plan 同期 / proof-log / WZ 再配線)。
**SoT**: 在庫 [`marton-inner-bound-inventory.md`](marton-inner-bound-inventory.md) + 本 plan。詳細履歴は git。
**再検証** (prose にキャッシュしない。`Marton/` は `MarkovCore/` サブディレクトリを含むので**ディレクトリ指定**):

```
rg -c "sorry|@residual" InformationTheory/Shannon/BroadcastChannel/Marton/ \
  InformationTheory/Shannon/ConditionalAEP.lean          # 無出力 = 0 件
rg -c "@audit:ok" InformationTheory/Shannon/BroadcastChannel/Marton/
scripts/sig_view.ts --names InformationTheory/Shannon/BroadcastChannel/Marton/Achievability.lean
#print axioms InformationTheory.Shannon.BroadcastChannel.Marton.marton_achievability
rg -n "Marton|ConditionalAEP" InformationTheory.lean                        # root 登録の有無
```

## 進捗

- [x] Phase 0 — Mathlib / in-project 在庫調査 ✅ → [`marton-inner-bound-inventory.md`](marton-inner-bound-inventory.md)
- [x] Phase 1 — mutual covering の second moment 中核 (抽象 `S` 版) ✅ (`cd5c379a`)
- [x] Phase 2 — region 述語 + レート分割の消去補題 + root 登録 ✅ (`fa43fcb6`)
- [x] Phase 3 — 5-tuple ambient plumbing + `martonInfo₁/₂/V₁V₂` ✅ (`5800094e`)
- [x] Phase 4 — 共分散の鋭化 (conditional slice 版) ✅ (`6183832d`) ★ sum-rate 制約の要
- [x] Phase 5 — typicality 具体化 = `marton_mutual_covering` (weak) ✅ (`0d3412ec`)
- [x] Phase 6a — 受信機 1 の誤り分解 + E2 ✅ (`49a7191f`)
- [x] Phase 6a' — E1 の Markov 原子 + covering 集合の strong 化 (方針 B) ✅ (`c776a03f`、→ D5)
- [x] Phase 6b — 受信機 2 の誤り解析 (MarkovCore + ErrorAnalysis の鏡像) ✅ (`43d7ea76`)
- [x] Phase 7 — 組み立て = headline `marton_achievability` ✅ (`8f6f2f07` → 監査 `63d37b8f` → style `0f30e5d1`)
- [ ] Phase 8 — bookkeeping (README / 親 plan / proof-log / WZ 再配線) 📋 ★ 次の一手

---

## ゴール / Approach

**到達した命題**: 一般 BC `W : BCChannel α β₁ β₂` と補助変数の同時分布 `pV : Measure (V₁ × V₂)`、
入力カーネル `K : Kernel (V₁ × V₂) α` に対し、**厳密不等号 3 本**

```
R₁ < I(V₁;Y₁)                              -- martonInfo₁
R₂ < I(V₂;Y₂)                              -- martonInfo₂
R₁ + R₂ < I(V₁;Y₁) + I(V₂;Y₂) − I(V₁;V₂)   -- martonInfoV₁V₂ を差し引いた sum-rate
```

を満たす `(R₁,R₂)` は達成可能 (十分大きい `n` で平均誤り確率が両受信機とも `ε'` 未満の
`BroadcastCode M₁ M₂ n α β₁ β₂` が存在する)。

**全体戦略は 3 層**。層の境界は「抽象度」で切ってあり、下層は上層の定義を一切知らない。この分離が
方針 B (weak → strong の切替) を下層無改変で通した (→ 判断ログ 1)。

1. **抽象 second-moment 層** (Phase 1/4): 可測集合 `S ⊆ α × β` と `iIndepFun` だけを仮定して
   `P(どの組も S に落ちない) ≤ …` を出す層。typicality を一切参照しない。
2. **typicality 層** (Phase 3/5/6a'/6b): `S` を具体的な同時典型集合と置き、`p` の下界とスライスの
   一様上界 `q̄` を指数形で供給する層。**weak / strong の切替はこの層に閉じる**。
3. **operational 層** (Phase 6a/7): 符号帳から `BroadcastCode` を作り、Bonferroni + pigeonhole で
   平均誤り確率を落とす層。degraded BC 版の**骨格**は参考になるが個々の補題は写経できない
   (再利用できた/できなかったものの実測 → 判断ログ 3)。

**符号帳の索引設計 (本 plan で確定させた中核の設計判断)**: Marton の符号帳は
**メッセージ索引と covering 索引の直積** `Fin Mᵢ × Fin M̃ᵢ` を持つ。符号化器は与えられた `(m₁,m₂)` に
対し副符号帳の組 `(l₁,l₂)` を strong joint typical になるよう選ぶ (= mutual covering の適用点)。
制約 `R̃₁+R̃₂ > I(V₁;V₂)` / `R₁+R̃₁ < I(V₁;Y₁)` / `R₂+R̃₂ < I(V₂;Y₂)` から `(R̃₁,R̃₂)` を消去すると
目標の 3 本が出る (Phase 2 の Fourier–Motzkin 補題 `exists_martonRateSplit`)。
入力側の randomization は符号帳アンサンブルの 1 段に置き、pigeonhole で実現値を固定する
(`BroadcastCode` 構造体は無改修)。

---

## 確定した設計判断 (headline の読み方に効くものだけ)

### D1. 決定的関数 `x = f(v₁,v₂)` は採らず、一般カーネル `K : Kernel (V₁ × V₂) α` 形

`Kernel.deterministic f` は `(K v).real {b} = 0` (`b ≠ f v`) を生み、in-project の typicality mass
bound が**例外なく要求する full support 前提** (`hK : ∀ v a, 0 < (K v).real {a}`) と原理的に両立しない
(強 typicality 版も同前提)。教科書側も一般カーネルで領域が拡大しないので数学的損失はない。
⇒ **この射程の差は headline docstring に明記済** (「決定的版は本定理の直接の系としては出ない」)。

### D2. 構造改修なし / D3. 制約は厳密不等号

`BroadcastCode` は無改修で足りた (blast radius 0)。`InBCCapacityRegion` は改修せず `InMartonRegion`
(`≤` 3 本、region 記述 / 将来の converse 用) を別途新設。headline 側は既存 `bc_achievability` と同じく
**厳密不等号 3 本**を直接取る (achievability に境界は乗らない ⇒ 在庫 §1.1 の非厳密版は誤り)。

### D4. 粗い分散上界では sum-rate 制約に届かない (Phase 4 の存在理由) ★

粗い版の結論 `P(A = 0) ≤ 1/(M₂p) + 1/(M₁p)` は `R̃₁ > I(V₁;V₂)` **かつ** `R̃₂ > I(V₁;V₂)` を要求し、
教科書の**和条件**より真に強い (消去すると `R₁+R₂ < I₁+I₂−2·I₁₂` の弱い領域しか出ない)。
鋭い版 `meas_pairCount_eq_zero_le'` が第 1 項 `1/(M₁M₂p)` (= 和条件) を分離する。
**スライス上界は両方向が要る**: `covariance_pairIndicator_shared_le` は `hsliceX` / `hsliceY` の
**両方**を取る (片方向で足りるという当初予測は反例で棄却 → Settled facts)。粗い版 4 本は無改変で残置。

### D5. E1 は weak typicality の在庫では閉じない → covering 集合のみ strong 化 (方針 B) ★

「選択された `V₁ⁿ` に対して**一様に** E1 が成り立つ」は**偽** (根拠 → Settled facts)。機構は、E1 が
要求するのが「真の対が典型」= **下界**であるのに Phase 5 のファイバー上界は**向きが逆**であること
(上界は選択の条件付けの下でも生き残る = E2 が助かった理由)。degraded BC が閉じるのは送信符号語の法則が
ambient iid 法則に**一致する**からで、Marton は `martonAux₁` の行添字が両行全体の関数なのでこの潰し込みが
**原理的に不可能**。⇒ 採用した方針 B は `martonSelectRow` の判定のみ `jointStronglyTypicalSet` へ移し、
**復号側は weak のまま**、抽象層 (`MutualCovering.lean` / `Setup.lean` / `Basic.lean`) は無改変。

方針 B が確定させた構造 (Phase 7 が実際に消費した形):

- **半径は 3 本の入れ子**: 復号 `ε` ⊃ 送信対の pin `martonStrongRadius(₂) ε` ⊃ covering の pin
  `martonCoveringRadius(₂) ε`。後 2 者は `ε` の**計算項**であり独立パラメータではない (→ 判断ログ 2)。
- **covering 半径は受信機間で共通化できない** (`martonStrongRadius` 経由で帯定数に依存)。両受信機を
  同時に満たすには `min` を取り `jointStronglyTypicalSet_mono_radius` (`MarkovCore/Prelim.lean`) で
  各受信機の半径へ開き直す。**帯定数は 3 種あり流用不可**: `martonBandConst` = `(V₁,X)` 対用 /
  `martonBandConst₂` = `(V₂,X)` 対用 / `martonCoveringBandConst` (`Covering.lean`) = `(V₁,V₂)` 対用。
  取り違えても型は通るが意味が壊れる。
- **covering は weak 版 4 本を残したまま strong 版 4 本を並置**した (削除・書換ではない)。strong ⊆ weak
  なので上界は含意され、`C = martonCoveringBandConst = 0` で weak 版に退化する = 領域不変性の検算になる。
- **`MarkovCore` は非対称**: 受信機 1 のみが持つ `marton_condAEP_jointlyTypical_ge` と
  `marton_strongRadius_prob_tendsto_one` は下流が消費しないので鏡像を作っていない (Phase 7 でも不要と確定)。

**却下した代替 A** (weak のまま Sanov / I-射影) は在庫ゼロの凸解析 600–900 行かつ Fourier–Motzkin の
再設計を伴うため不採用。**L-MT5 (領域弱化) はこの障害に対応しない**。

---

## Phase 詳細

### Phase 0–7 ✅ 完了

| Phase | 出力 | commit |
|---|---|---|
| 0 | 在庫 [`marton-inner-bound-inventory.md`](marton-inner-bound-inventory.md)。Mathlib 壁 0 件 / 既存率 89% / 自前構築 8 種 | — |
| 1 | `Marton/MutualCovering.lean` 抽象核 4 段 + 充足可能性証明書 | `cd5c379a` |
| 2 | `Marton/Basic.lean` = `InMartonRegion` + `.mono` + `exists_martonRateSplit` (Fourier–Motzkin) + root 登録 | `fa43fcb6` |
| 3 | `Marton/Setup.lean` = ambient 測度 + 座標補題 + `martonInfo₁/₂/V₁V₂` | `5800094e` |
| 4 | `MutualCovering.lean` 追記 = `covariance_pairIndicator_shared_le` / `meas_pairCount_eq_zero_le'` (→ D4) | `6183832d` |
| 5 | `Marton/Covering.lean` = weak 版 `marton_mutual_covering` (`@[entry_point]`) + swap 橋 + ambient 輸送 | `0d3412ec` |
| 6a | `Marton/ErrorAnalysis.lean` = 符号帳/選択/復号器 + `martonCodebookToCode` + 受信機 1 の Bonferroni + E2 | `49a7191f` |
| 6a' | 方針 B (→ D5): 新規 `Shannon/ConditionalAEP.lean` (型汎用の条件付き AEP) + 新規 `Marton/MarkovCore.lean` + `Covering.lean` に strong 版 4 本並置 + `martonSelectRow` を strong 判定へ | `c776a03f` |
| 6b | 受信機 2 の鏡像 (MarkovCore 側 7 本 + ErrorAnalysis 側 6 本) + 半径単調性 2 本。実装 ~1070 行 = 起票見積 350–500 の 2 倍超 | `43d7ea76` |
| 7 | `Marton/Achievability.lean` (928 行 / 17 decl = `private` 16 + headline 1)。headline `marton_achievability` `@[entry_point]` + `@audit:ok`、`#print axioms` = `[propext, Classical.choice, Quot.sound]`。3 段アンサンブルの再結合 (`marton_three_tier_aggregate` / `marton_three_tier_pigeonhole`) と ε 配分がともに閉じ、**L-MT6 は不発動** | `8f6f2f07` → `63d37b8f` → `0f30e5d1` |

`MarkovCore` は `e83c1533` で `MarkovCore/{Prelim,Receiver1,Receiver2}` に分割され、`MarkovCore.lean`
自身は 3 本を再輸出する umbrella になった (root は 4 本すべて登録済)。

### Phase 8 — bookkeeping 📋 ★ 次の一手

2 ゲートは Phase 7 内で消化済 (honesty `63d37b8f` / style `0f30e5d1`) なので、残りは 4 件:

- [ ] **README 定理表**: `docs/readme-theorems.txt` の Ch.15 行に `marton_achievability` を追記
  (degraded 版 `bc_achievability` と並べる) → `deno run -A scripts/gen_readme_table.ts --write`。
  **未追記であることを確認済** (`rg marton docs/readme-theorems.txt` が 0 件)。
- [ ] **親 plan 同期** (下記「親との同期点」3 箇所)。
- [ ] **proof-log**: `docs/shannon/` に Marton の proof-log は 1 本も無い (`find docs -name "*marton*"` で
  確認済 = 在庫と本 plan のみ)。Phase 4/5/6a'/6b/7 を 1 本に統合して起こす。**proof-log: yes**。
- [ ] **follow-up (6a' 由来、Marton 家系の外)**: WZ `WynerZiv/Achievability/Concentration.lean` の
  `private` 3 本 (`wz_pi_nonuniform_mean_concentration` / `wz_pi_nonuniform_concentration_tendsto` /
  `wz_sum_eq_typeCount_mul`) は `Shannon/ConditionalAEP.lean` と同一命題。WZ 側を本モジュールへ
  再配線する (重複解消)。headline には不要なので本 plan の closure を塞がない。
- [ ] `deno run -A scripts/plan_lint.ts docs/shannon/marton-*.md docs/shannon/broadcast-channel-moonshot-plan.md`。

---

## 申し送り (非緊急。Marton 家系の外に出るものを含む)

1. **`ε_cov` が `ErrorAnalysis.lean` で auto-bound implicit になっている** ⚠ 潜在的な脆さ。
   `marton_random_codebook_alias₁_le` / `marton_random_codebook_alias₂_le` は binder に `{ε : ℝ}` しか
   宣言していないのに本文で `ε_cov` を使っており、`autoImplicit` が `{ε_cov : ℝ}` を署名の**先頭**に
   挿入している (`#check` で確認済)。同種の `ε_cov` は関数値引数からは推論できないことがあり、
   実際 `marton_inputTier_marginal` の呼び出しは `(ε_cov := ε_cov)` の明示を必要としている。
   明示 binder に直すのが望ましいが、署名の引数順が変わるので単独 leg 扱い。
2. **`@audit:ok` の付与漏れ 4 本** (headline 経路上ではないので Phase 7 の監査対象外だった):
   `Marton/Covering.lean` の weak 版 3 本 (`meas_marton_codebook_no_jointlyTypicalPair_lt` /
   `marton_mutual_covering` / `marton_mutual_covering_of_indepAux`) と `Marton/Basic.lean` の
   `exists_martonRateSplit`。strong 版 3 本には付与済 ⇒ 家系 closure 時の対称化バッチ候補。
3. **BC (degraded) 家系側**: `Achievability/Assembly.lean` の `bc_achievability` が取る `_hR₁` は
   underscore 接頭辞だが**実際に使われている** (`bc_Ec_lt_of_rate` へ `_hR₁.le` で渡している)。
   `hR₁` に改名すべき。`_hR₂` は本当に未使用なのでそのままでよい。
4. **`docs/rules/docstrings.md` の「module docstring の本文は 2 スペース字下げ」規則は repo 355 ファイル中
   0 件が遵守していない** (全部 flush-left)。規則を消すか repo 一括パスを組むかは人間判断。
   `docs/rules/` は本 plan の書込権限外なので記録のみ。

---

## 撤退ライン (frozen slug — 他文書が参照しうる)

**全 6 本が決着済 (解決 or 不発動)。生きた撤退口は 0。**

| slug | 発動条件 | 状態 |
|---|---|---|
| **L-MT1** | Phase 5 の typicality 具体化が 1 leg で閉じない | **不発動** (Phase 5 完了) |
| **L-MT2** | 決定的 `x = f(v₁,v₂)` 版が full support 前提と両立しない (D1) | **発動・解決済** — 一般カーネル形で述べ、射程の差を headline docstring に明記 |
| **L-MT3** | Phase 3 の 5-tuple ambient plumbing が爆発する | **不発動** (Phase 3 完了) |
| **L-MT4** | Phase 6a の選択索引の独立性が既存 `bcCodebookToCode` 系と噛み合わない | **trigger 条件は 6a で成立したが発動せず**。方針 B (D5) の成功後はもはや trigger しない |
| **L-MT5** | Phase 4 の鋭化が閉じない (領域を `R₁+R₂ < I₁+I₂−2·I₁₂` に弱化する退避) | **不発動** (Phase 4 完了)。D5 の障害には対応しない |
| **L-MT6** | Phase 7 の ε 配分 / 三重和を 2 段 pigeonhole へ再結合する段が閉じない | **不発動** (Phase 7 完了) — ε 配分も再結合 (`marton_three_tier_pigeonhole`) も閉じた |

> **禁止事項の再確認**: どの撤退ラインでも「covering が成立する」「選択索引が独立である」等を
> `*Hypothesis` 述語に束ねて仮説として渡す形は取らない (CLAUDE.md「検証の誠実性」tier 5)。
> 退避は必ず `sorry` + `@residual` で、署名は証明したい形のまま保つ。

---

## 親との同期点 (plan_lint 双方向照合)

親 `broadcast-channel-moonshot-plan.md` の 3 箇所が本子 plan の状態の**キャッシュ**。**衝突時は子が SoT**。

1. **Status 行**: degraded ✅ CLOSED / 一般 BC (Marton) ✅ headline 到達 の 2 本立て + 子へのリンク。
2. **要点の L-BC5 記述**: slug は**凍結なので消さない**。Marton 部分は解除 → headline 到達、
   Körner–Marton は scope-out 継続。
3. **Sub-plan 一覧テーブルの Marton 行**: 状態欄が進捗のキャッシュ。

Phase 7 完了時点 (2026-07-26) で 3 箇所とも同期済。Phase 8 の README 追記が済んだら 3 に反映する。

---

## Settled facts (再導出が高価なものだけ)

| claim | confidence | 再検証 | notes |
|---|---|---|---|
| Marton / mutual covering に対応する Mathlib 補題は存在しない (`"Paley"` / `"second_moment"` / `"covering_lemma"` はいずれも `Found 0 declarations`) | `loogle-neg` | 在庫 §8 のクエリを再実行 | 壁ではなく自前構築。近接テンプレ補題を各項目に名指し済 |
| 決定的カーネルは in-project typicality の full support 前提を原理的に壊す (`Kernel.deterministic` の質量が `b ≠ f v` で 0) | `machine` | `Mathlib/Probability/Kernel/Basic.lean:58` + `Mathlib/MeasureTheory/Measure/Dirac.lean:44` を Read | D1 の根拠。強 typicality 版も同前提なのでルート変更で回避不能 |
| 「選択された `V₁ⁿ` に対して一様に E1」は一般アルファベットで**偽** (補助 3 元・周辺 `(1/2,1/4,1/4)`・型 `(1/2,1/2,0)` が weak 典型なのに出力側経験エントロピーが `H(Y₁)` から `0.251 nats` = n 非依存の定数ずれ。補助 2 元では型が pin されて反例が消える) | `human-judgment` | 反例族を再構成 (実 `def` を Read して逐語確認済、`proof-pivot-advisor` が反証 3 本を試みたうえで支持) | D5 の根拠。weak 在庫に戻る誘惑が出たらここを読む |
| スライス上界の片方向では共分散上界が破れる (`α = {0}`, `β = {0,1}`, `μX = δ₀`, `μY(0) = ε`, `S = {(0,0)}` で snd 共有組の共分散 `ε−ε²` が `q̄·p = ε²` を `ε = 0.1` で破る) | `human-judgment` | 反例を再計算 | D4 の根拠。`covariance_pairIndicator_shared_le` が仮説を 2 本取る理由 |

---

## 判断ログ

1. **層の境界を「抽象度」で切る**: Phase 1/4 が typicality を一切知らないのは設計であり偶然ではない。
   おかげで方針 B (weak → strong の切替) が `MutualCovering.lean` を**無改変**で通過し、書換は typicality
   層に閉じた。`ErrorAnalysis` も選択がテストする典型性の**種類に鈍感**なまま受信機 2 の鏡像が入り
   (`martonStrongRadius₂` / `martonBandConst₂` / `martonCoveringRadius₂` は `ErrorAnalysis.lean` に
   一度も現れない)、Phase 7 では半径配分が `Achievability` と `MarkovCore` の間だけで閉じた。
2. **半径は「パラメータ」ではなく「`ε` の計算項」**: `martonStrongRadius(₂)` / `martonCoveringRadius(₂)`
   を `ε` の関数として定義したので、下流の署名が持つ半径は `ε` と `ε_cov` の 2 本で済んだ。Phase 7 は
   `ε_cov := min (min (min …) …) …` の入れ子 `min` 1 本で全制約を同時に満たしており、新しい半径
   パラメータは足していない。**後続 leg でも足さない** (足すと ε 配分が爆発する)。
3. **degraded BC 家系から「再利用できたもの / できなかったもの」の実測** (Phase 7 で確定、逐語確認済)。
   起票時の plan は入力に `bc_two_tier_pigeonhole` しか挙げていなかったが、実際は:
   - **逐語再利用できた**: generic な `bc_weighted_two_tier_{mono,add,const_mul,sum_index}` /
     `bc_two_tier_pigeonhole` (`κU := κ₁ × κ₂` に束ねて 3 段を 2 段へ再結合) /
     **`bc_Ec_lt_of_rate`** (Marton の alias 末尾項そのもの。両受信機に `(R₁ := R'ᵢ) (R₂ := Rᵢ)` で当たる。
     plan の Phase 7 入力に挙がっておらず、自己実装を 1 本節約できた)。
   - **再利用不可だった**: `bc_pair_aggregate₁/₂` — `hE0 : … = A` を**等式**で固定しているが Marton は
     `≤ A` が要り、alias 索引の形も違う ⇒ `Achievability.lean` に private な
     `marton_two_tier_aggregate` / `marton_three_tier_aggregate` を建て直した (中身は上記 generic 4 本)。
   ⇒ **再利用可否の境界は「generic な畳み込み補題か、索引形を固定した集約補題か」**。次に BC 家系から
   写経したくなったら、この境界で仕分けてから該当宣言を Read する。
4. **「対称だから共通/流用できる」は実物で確認するまで書かない**: 6b が plan の対称性予測を 2 件覆し
   (covering 半径は受信機共通ではない / 受信機 1 の Bonferroni は degraded BC 版を一切呼ばない)、D4 の
   「スライス上界は両方向が要る」も同じ軸。一方 Phase 7 では**前回の同期で入れた訂正がそのまま当たった**
   — `marton_condAEP_jointlyTypical_ge` / `marton_strongRadius_prob_tendsto_one` の鏡像は実際に不要で、
   受信機ごとに別物の covering 半径を `min` + `jointStronglyTypicalSet_mono_radius` で開き直す段が
   まさに必要だった。⇒ 対称性の主張は「実装で潰した後なら書いてよい」。
5. **`exists_martonRateSplit` (`Marton/Basic.lean`) は Phase 7 の入力としては弱い (未決の判断軸)**:
   結論が `0 ≤ R₁' ∧ 0 ≤ R₂'` だが、covering のレート条件 `(4C+6)·ε_cov < R₁'` は `R₁' = 0` では
   充足不能。Phase 7 は `Achievability.lean` 内の private `exists_martonRateSplit_pos` で両レートを
   `min ((I₁−R₁−R₁')/2) ((I₂−R₂−R₂')/2)` だけ押し上げて回避し、**`Basic.lean` の署名は変更していない**。
   ⇒ 「`Basic.lean` 側を `0 < R₁' ∧ 0 < R₂'` に強めて private 版を畳む」か「public は弱い形のまま残す」
   かは**未決**。強める場合は `scripts/dep_consumers.sh` で consumer を実測してから。
