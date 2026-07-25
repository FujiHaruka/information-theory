# Shannon: 一般 BC の Marton inner bound サブ計画

> **Parent**: [`broadcast-channel-moonshot-plan.md`](broadcast-channel-moonshot-plan.md) §L-BC5 (解除)

**Status**: 🚧 進行中 — degraded 仮定を外した一般 (non-degraded) two-receiver broadcast channel に対する
**Marton inner bound (El Gamal–Kim *Network Information Theory* Thm 8.3、private message のみ)** の形式化。
親 plan の撤退ライン **L-BC5** (一般 BC + Marton は完全 scope-out) を**ユーザー指示で解除**して追う。
**Phase 0–6b 完了**: mutual covering は weak / strong の両版が proof-done、**両受信機**の誤り分解 +
E1 (条件付き AEP) + E2 (alias) も proof-done。残りは **Phase 7 (組み立て) + 8 (ゲート等)**。
**SoT**: 在庫 [`marton-inner-bound-inventory.md`](marton-inner-bound-inventory.md) + 本 plan。詳細履歴は git。
**再検証** (prose にキャッシュしない):

```
rg -c "sorry|@residual" InformationTheory/Shannon/BroadcastChannel/Marton/*.lean \
  InformationTheory/Shannon/ConditionalAEP.lean          # 無出力 = 0 件
rg -c "@audit:ok" InformationTheory/Shannon/BroadcastChannel/Marton/*.lean
scripts/sig_view.ts --names InformationTheory/Shannon/BroadcastChannel/Marton/MarkovCore.lean
#print axioms InformationTheory.Shannon.BroadcastChannel.Marton.marton_strong_mutual_covering
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
- [x] Phase 6a' — E1 の Markov 原子 + covering 集合の strong 化 (方針 B) ✅ (`c776a03f` まで、→ D5)
- [x] Phase 6b — 受信機 2 の誤り解析 (MarkovCore + ErrorAnalysis の鏡像) ✅ (`43d7ea76` まで、→ D5)
- [ ] Phase 7 — 組み立て = headline `marton_achievability` 📋 ★ 次の一手
- [ ] Phase 8 — 2 ゲート + README + 親 plan 同期 + proof-log 📋

---

## ゴール / Approach

**到達目標**: 一般 BC `W : BCChannel α β₁ β₂` と補助変数の同時分布 `pV : Measure (V₁ × V₂)`、
入力カーネル `K : Kernel (V₁ × V₂) α` に対し、3 本の制約

```
R₁ < I(V₁;Y₁)                              -- martonInfo₁
R₂ < I(V₂;Y₂)                              -- martonInfo₂
R₁ + R₂ < I(V₁;Y₁) + I(V₂;Y₂) − I(V₁;V₂)   -- martonInfoV₁V₂ を差し引いた sum-rate
```

を満たす `(R₁,R₂)` が達成可能 (十分大きい `n` で平均誤り確率が両受信機とも `ε'` 未満の
`BroadcastCode M₁ M₂ n α β₁ β₂` が存在する) こと。

**全体戦略は 3 層に分ける**。層の境界は「抽象度」で切ってあり、下層は上層の定義を一切知らない。

1. **抽象 second-moment 層** (Phase 1/4): 可測集合 `S ⊆ α × β` と `iIndepFun (codebookFamily X Y) μ`
   だけを仮定して `P(どの組も S に落ちない) ≤ …` を出す層。typicality を一切参照しない。
2. **typicality 層** (Phase 3/5/6a'/6b): `S` を具体的な同時典型集合と置き、`p` の下界とスライスの
   一様上界 `q̄` を指数形で供給する層。**weak / strong の切替はこの層に閉じる** (下記 D5)。
3. **operational 層** (Phase 6–7): 符号帳から `BroadcastCode` を作り、Bonferroni + pigeonhole で
   平均誤り確率を落とす層。`bc_achievability` の**骨格**は参考になるが、個々の補題は写経できない
   ことが 6b で確定した (→ 判断ログ 4)。

**符号帳の索引設計 (本 plan で確定させた中核の設計判断)**: Marton の符号帳は
**メッセージ索引と covering 索引の直積** `Fin Mᵢ × Fin M̃ᵢ` を持つ。
`M̃ᵢ = ⌈exp(n R̃ᵢ)⌉` は「1 メッセージあたりの副符号帳サイズ」。符号化器は与えられた `(m₁,m₂)` に対し
副符号帳の組 `(l₁,l₂)` を joint typical になるよう選ぶ (= mutual covering の適用点、固定 `(m₁,m₂)` ごとに
2 本の副符号帳は独立なので Phase 1 の定理がそのまま当たる)。復号器は `(mᵢ,lᵢ)` の組を復号する。
これで制約は

```
covering : R̃₁ + R̃₂ > I(V₁;V₂)
decode 1 : R₁ + R̃₁ < I(V₁;Y₁)
decode 2 : R₂ + R̃₂ < I(V₂;Y₂)
```

の 3 本になり、`(R̃₁,R̃₂)` を消去すると目標の 3 本が出る (Phase 2 の Fourier–Motzkin 補題)。
**逆向きも初等**: `R̃ᵢ := (Iᵢ − Rᵢ)·θ`、`θ ∈ (I₁₂/D, 1)`、`D := (I₁−R₁)+(I₂−R₂)` と取れば
3 本すべてが満たされる (`D > I₁₂` が sum-rate 制約そのもの)。

**入力側の randomization は符号帳アンサンブルに置く**。`K` はカーネルだが `BroadcastCode.encoder` は
決定的写像なので、`bc_achievability` の satellite 段と同じく `X^n` を符号帳の 1 段として
`Πᵢ K(v₁ᵢ, v₂ᵢ)` から引き、pigeonhole で実現値を固定する。構造体の改修は不要。

---

## 確定済みの設計判断 (実装 leg の前提)

### D1. 決定的関数 `x = f(v₁,v₂)` は採らず、一般カーネル `K : Kernel (V₁ × V₂) α` 形で述べる

在庫 §4.2 の最重要所見。`Kernel.deterministic f` を入れると `(K v).real {b} = 0` (`b ≠ f v`) となり、
in-project の typicality mass bound が**例外なく要求する full support 前提**
(`hK : ∀ v a, 0 < (K v).real {a}`) と原理的に両立しない。強 typicality 版も同じ前提を要求するため
ルート変更では回避できない。教科書側も一般カーネルを許して領域が拡大しないことが知られており、
数学的損失はない。既存 `bc_achievability` も同じ full support 前提を持つのでプロジェクト内で一貫する。

⇒ **この射程の差 (EGK Thm 8.3 の逐語形である決定的関数版ではない) は headline docstring に明示する**
(Phase 7 の受け入れ条件)。「一般カーネル形で述べており、決定的 `x = f(v₁,v₂)` 版は本定理の直接の系
としては出ない」ことを 1–2 文で書く。

### D2. 構造改修はしない (`dep_consumers.sh` で機械実測済)

`BroadcastCode` は符号化器の型がそのまま使えるので**無改修**、blast radius 0。
`InBCCapacityRegion` は制約が 2 本しかないので、既存を改修せず `InMartonRegion` を
新規追加する。Phase 6a/6a'/6b でもこの判断は覆っていない (6b 終了時点の実測は
`BroadcastCode` 22 decl / 6 file・`InBCCapacityRegion` 3 decl / 2 file。うち Marton 側は
`martonCodebookToCode` + Bonferroni 2 本の 3 件で、すべて `BroadcastCode` を**消費するだけ**)。
Phase 7 の前に再実測するときは `scripts/dep_consumers.sh` を回す (prose の数はキャッシュ)。

### D3. headline の rate 制約は**厳密不等号**で置く (`InMartonRegion` を仮説に取らない)

既存 `bc_achievability` (`Achievability/Assembly.lean`) は `InBCCapacityRegion` を仮説に取らず
`hR₁lt` / `hR₂lt` の**厳密不等号 2 本**を直接取る (逐語確認済)。achievability に境界は乗らないので
在庫 §1.1 の非厳密版は誤り。⇒ headline は厳密不等号 3 本、`InMartonRegion` (`≤` 3 本) は
region 記述 / README / 将来の converse 用として別途定義する (Phase 2 で定義済)。

### D4. 粗い分散上界では sum-rate 制約に届かない (Phase 4 の存在理由、機械確認済) ★

粗い版 `meas_pairCount_eq_zero_le` の結論 `P(A = 0) ≤ 1/(M₂p) + 1/(M₁p)` は
`R̃₁ > I(V₁;V₂)` **かつ** `R̃₂ > I(V₁;V₂)` を要求し、教科書の**和条件**より真に強い
(消去すると `R₁+R₂ < I₁+I₂−2·I₁₂` の弱い領域しか出ない)。鋭い版 `meas_pairCount_eq_zero_le'` は
第 1 項 `1/(M₁M₂p)` (= 和条件) と `q̄/p` 経由の個別条件を分離する。

**スライス上界は両方向が要る** (実装時に反例で確定): fst 共有側は `∫ q(x)² dμX`、snd 共有側は
`∫ r(y)² dμY` に落ち、**μY 側の一様上界は μX 側を全く抑えない**。
反例: `α = {0}`, `β = {0,1}`, `μX = δ₀`, `μY(0) = ε`, `S = {(0,0)}` で snd 共有組の共分散 `ε−ε²` が
主張上界 `q̄·p = ε²` を `ε = 0.1` で破る。⇒ `covariance_pairIndicator_shared_le` は
`hsliceY` と `hsliceX` の**両方**を取る (どちらも `S` と周辺測度の構造的な量的性質であり、
結論を担ぐ仮説ではない)。粗い版 4 本は fallback として無改変で残置。

### D5. E1 は weak typicality の在庫では閉じない → covering 集合のみ strong 化 (方針 B、**完了**) ★

**判定 (2026-07 前半、実装者発見 → `proof-pivot-advisor` が反証 3 本を試みたうえで支持)**:
「選択された `V₁ⁿ` に対して**一様に** E1 が成り立つ」は**偽**。機構は、E1 が要求するのが
「真の対が典型」= **下界**であるのに対し Phase 5 のファイバー上界は**向きが逆**であること
(上界は選択の条件付けの下でも生き残る = E2 が助かった理由)。degraded BC が閉じるのは
`codebook_marginal_one` で送信符号語の法則が ambient iid 法則に**一致する**からで、Marton は
`martonAux₁` の行添字が両行全体の関数なのでこの潰し込みが**原理的に不可能**。
反例は補助アルファベット 3 元・周辺分布 `(1/2, 1/4, 1/4)`、型 `(1/2, 1/2, 0)` が
weak 典型なのに出力側経験エントロピーが `H(Y₁)` から `0.251 nats` (n 非依存) ずれる、の 1 径数族。
補助アルファベット 2 元では型が pin されて反例が消えるので、**一般アルファベットでのみ** false-as-framed。

**方針 B (採用・完了)**: `martonSelectRow` の判定を `jointStronglyTypicalSet` へ。**復号側は weak のまま**。
`MutualCovering.lean` (抽象 `S` 層) と `Setup.lean` / `Basic.lean` は**無改変**で済んだ
(Phase 1/4 を抽象に切った設計判断がここで効いた)。実装で判明した予測との差分 4 点 —
**Phase 7 が消費するのでここに残す** (宣言名で参照する。行番号はキャッシュすると腐るので書かない)。

1. **半径は 3 本の入れ子**である (起票時は 2 本しか想定していなかった):
   復号 `ε` ⊃ 送信対の pin `martonStrongRadius(₂) pV K W ε` ⊃ covering の pin
   `martonCoveringRadius(₂) pV K W ε`。定義 (`MarkovCore.lean`、逐語確認済) は
   `martonStrongRadius ε = ε / (2 * (1 + martonBandConst))`、
   `martonCoveringRadius ε = martonStrongRadius ε / (4 * (card (V₁ × V₂) + 1))`。
2. **covering 半径は受信機間で共通化できない** (⚠ 6b が plan の予測を覆した点)。起票時の plan は
   「`martonCoveringRadius` は covering 側の量なので**共通**、分岐するのは `martonBandConst` 以降」と
   書いていたが**誤り**: 上式のとおり `martonCoveringRadius` は `martonStrongRadius` 経由で
   `martonBandConst` に依存する。⇒ 6b は独立に **`martonCoveringRadius₂`** を新設し、Phase 7 で両者の
   `min` を取れるよう **`stronglyTypicalSet_mono_radius` / `jointStronglyTypicalSet_mono_radius`**
   (半径単調性、in-project に不在だったので新規に建てた汎用 2 本、`MarkovCore.lean` の
   `RadiusMonotone` 節) を用意した。**帯定数は 3 種あり流用不可**: `martonBandConst` が `(V₁,X)` 対用、
   `martonBandConst₂` が `(V₂,X)` 対用、`coveringBandConst` / `martonCoveringBandConst`
   (`Covering.lean`) が `(V₁,V₂)` 対用。取り違えても型は通るが意味が壊れる。
3. **起票時に無かった 2 本目の Markov lemma が要った**。covering が与えるのは `(v₁,v₂)` の strong
   同時典型だが、gateway atom が要求するのは `(v₁,x)` の strong 典型で `x` は `Π K(v₁ᵢ,v₂ᵢ)` から引かれる。
   この橋が `marton_transmitted_stronglyTypical_le` (受信機 2 版 `marton_transmitted_stronglyTypical₂_le`)。
   E1 の最終形は `marton_condAEP_selected_avg_le` / `marton_condAEP_selected_avg₂_le`
   (**入力段平均版**。閾値が選択対より前に立つので符号について一様 — これが `ErrorAnalysis` が
   消費できる唯一の形)。
4. **covering は weak 版 4 本を残したまま strong 版 4 本を並置した** (削除・書換ではない)。
   strong ⊆ weak なので strong 版の上界が weak 版を含意する。**領域は不変** — 監査が
   `C = martonCoveringBandConst = 0` で既存 weak 版の `3ε` / `6ε` に退化することを確認済 (D5 の予測どおり)。

**却下した代替 A** (weak のまま Sanov / I-射影) は、型空間上の I-射影一意性 + 定量ギャップという
在庫ゼロの凸解析 600–900 行、かつ `R₁'+R₂'` に上界制約が新規に要り Phase 7 の Fourier–Motzkin を
再設計することになるため不採用。**L-MT5 (領域弱化) はこの障害に対応しない** (弱化しても選択は残る)。
**退避 C** (E1 を `sorry` にして Phase 7 を先行) は方針 B の成功により**不要になった**。

---

## Phase 詳細

### Phase 0–6b ✅ 完了

| Phase | 出力 | commit |
|---|---|---|
| 0 | 在庫 [`marton-inner-bound-inventory.md`](marton-inner-bound-inventory.md)。Mathlib 壁 0 件 / 既存率 89% / 自前構築 8 種 | — |
| 1 | `Marton/MutualCovering.lean` 抽象核 4 段 (`integral_pairCount` / `covariance_pairIndicator_eq_zero` / `variance_pairCount_le` / `meas_pairCount_eq_zero_le`) + 充足可能性証明書 | `cd5c379a` |
| 2 | `Marton/Basic.lean` = `InMartonRegion` + `.mono` + `exists_martonRateSplit` (Fourier–Motzkin、`θ` のクランプが要る) + root 登録 | `fa43fcb6` |
| 3 | `Marton/Setup.lean` = `martonJointDistribution` / `martonAmbientMeasure` + 座標補題 + `martonInfo₁/₂/V₁V₂` (entropy 差分形) + `martonAmbient_entropy_coord` | `5800094e` |
| 4 | `MutualCovering.lean` 追記 = `covariance_pairIndicator_shared_le` / `variance_pairCount_le'` / `meas_pairCount_eq_zero_le'` (→ D4) | `6183832d` |
| 5 | `Marton/Covering.lean` = weak 版 mutual covering `marton_mutual_covering` (`@[entry_point]`) + swap 橋 45 行 + ambient 輸送 | `0d3412ec` |
| 6a | `Marton/ErrorAnalysis.lean` = 符号帳/選択/復号器の定義 + `marton_errorProbAt₁_le_bonferroni` + `marton_averageErrorProb₁_toReal_le` + E2 (`sum_codebook_alias_le` / `marton_random_codebook_alias₁_le`)。E2 は Phase 5 のファイバー上界が一様なため選択の条件付けを解かずに通り、警戒した averaged swap の作り込みは不要だった | `49a7191f` |
| 6a' | 下記 | `e4e73e87` → … → `c776a03f` |
| 6b | `MarkovCore.lean` に受信機 2 の鏡像 (`martonBandConst₂` / `martonStrongRadius₂` / `martonCoveringRadius₂` / 帯補題群₂ / `marton_condAEP_jointlyTypical₂` / `marton_transmitted_stronglyTypical₂_le` / `marton_condAEP_selected_avg₂_le`) + 汎用の半径単調性 2 本 (→ D5-2)、`ErrorAnalysis.lean` に受信機 2 の 6 本 (`marton_jointlyTypicalFiber₂_le` / `marton_alias_slice_avg_le₂` / `martonMessageDecoder₂_eq_of_unique` / `marton_errorProbAt₂_le_bonferroni` / `marton_averageErrorProb₂_toReal_le` / `marton_random_codebook_alias₂_le`)。実装 ~1070 行 (起票見積 350–500 の 2 倍超 — Phase 7 の見積を読むときの校正点)。`ErrorAnalysis` は 6 本ずつで対称だが `MarkovCore` は非対称: 受信機 1 のみが持つ `marton_condAEP_jointlyTypical_ge` (補集合読み替え) と `marton_strongRadius_prob_tendsto_one` (非空虚性の証明書) は**下流が消費しないので鏡像を作らなかった** — Phase 7 で `…₂_ge` を探しても無い | `0e9f21d5` → `4d05f51f` → `c237ab1f` → `43d7ea76` |

**Phase 6a' の内訳** (gateway-atom-first の順序を守り、`Covering.lean` の書換より先に E1 の Markov 原子を撃った):

- **新規ファイル `InformationTheory/Shannon/ConditionalAEP.lean`** — 型汎用の条件付き AEP モジュール
  (Chebyshev 集中 + 型 pin の Lipschitz 評価 + 合成 = `pi_empiricalMean_deviation_le_of_type_close`)。
  **WZ `WynerZiv/Achievability/Concentration.lean` の `private` 版 3 本
  (`wz_pi_nonuniform_mean_concentration` / `wz_pi_nonuniform_concentration_tendsto` /
  `wz_sum_eq_typeCount_mul`) と同一命題**であり、WZ を本モジュールへ再配線するのは **follow-up**
  (module docstring に記載済 → Phase 8)。
- **新規ファイル `Marton/MarkovCore.lean`** — Marton の 2 本の Markov lemma (→ D5-3) + 帯補題群 + 半径定義。
- `Covering.lean` に strong 版 4 本を並置、`ErrorAnalysis.lean` の `martonSelectRow` を strong 判定へ
  (`ε_cov` を独立パラメータとして追加)。
- **proof-log: yes** (Phase 4/5 の proof-log に統合)。

### Phase 7 — 組み立て = headline `marton_achievability` 📋 ★ 次の一手

- 入力: Phase 2 (`exists_martonRateSplit`)、Phase 6a/6a'/6b、`bc_two_tier_pigeonhole`
  (`Achievability/Assembly.lean`)、`bcCodebookToCode` (`Achievability/Setup.lean`) の相当物、
  `martonCodebookToCode` (6a で定義済)。
- **covering は ε を仮説に取る版を消費する**: `marton_strong_mutual_covering` は `ε` を結論側 (`∃`) に
  出しているので、復号解析と `ε` を協調させる Phase 7 では
  **`meas_marton_codebook_no_jointStronglyTypicalPair_lt`** (`Marton/Covering.lean`) を使う。
  レート条件は `I₁₂ + (C+3)ε < R₁'+R₂'` / `(4C+6)ε < R₁'` / `(4C+6)ε < R₂'`
  (`C = martonCoveringBandConst pV K W`、逐語確認済)。

- 出力: `Marton/Achievability.lean`
  - headline `marton_achievability` — 署名は在庫 §1.1 を D3 に従って厳密不等号 3 本へ差し替えた形。
  - **docstring 要件** (D1): 一般カーネル形であること + 決定的 `x = f(v₁,v₂)` 版は直接の系として
    出ないこと + `hpV`/`hK`/`hW` が full support の**正則性前提**であること (load-bearing ではない) を明記。
  - **半径の 3 本入れ子 (D5-1) も docstring に 1 文で書く** — 復号 `ε` と選択 `ε_cov` が別物である
    ことは署名から読み取れないため。
- 見積り: **250–400 行** (6b が起票見積の 2 倍超になった実績があるので上振れを見込む)。
  先行: Phase 2, 6a, 6a', 6b。**proof-log: yes**。撤退: L-MT6。

**Phase 7 が踏む設計事実 (6b までの実装で確定。予測ではなく実物確認済)**:

1. **半径は 3 本の入れ子** (→ D5-1): 復号 `ε` ⊃ 送信語 pin `martonStrongRadius(₂) ε` ⊃
   covering pin `martonCoveringRadius(₂) ε`。
2. **帯定数は 3 種あり流用不可** (→ D5-2): `martonBandConst` = `(V₁,X)` 対用 /
   `martonBandConst₂` = `(V₂,X)` 対用 / `coveringBandConst`・`martonCoveringBandConst`
   (`Covering.lean`) = `(V₁,V₂)` 対用。取り違えると型は通るが意味が壊れる。
3. **ε 配分の制約は 2 本増える** (旧記述「1 本増える」は covering 半径共通化の誤りに由来する過少計上)。
   covering は `ε_cov := min (martonCoveringRadius pV K W ε) (martonCoveringRadius₂ pV K W ε)` で
   instantiate し、`jointStronglyTypicalSet_mono_radius` で各受信機側の半径へ開き直す。既存 5 系統
   (covering 失敗 / E0₁ / E0₂ / alias₁ / alias₂) に加えて、(6) covering のレート条件 3 本を `ε_cov` で
   同時に満たす条件、(7) `ε_cov ≤ martonCoveringRadius(₂) ε` の両立 (= `min` + 単調性で開き直す段) が要る。
4. **strong 半径と weak 半径を同一にすると証明不能** (WZ 家系の doctrine): 同一半径だと `O(ε)` の
   部分ラベル入替クラスが開く。分離は**厳密不等号**で入れる。
5. **`marton_random_codebook_alias₂_le` の三重和の順序は受信機 1 版と揃えてある** (`c₁` 外側 → `c₂` →
   `cX`、両署名を逐語確認済)。Phase 7 で両受信機の alias 評価を**同一のアンサンブル期待値**に対して
   union bound するための設計判断。⚠ ただし `bc_two_tier_pigeonhole` は文字どおり **2 段** (`κU` / `κX`)
   なので、3 段のアンサンブルをそのまま食わせることはできない — 外側 2 段を
   `κU := MartonSubcodebook₁ × MartonSubcodebook₂` (重み = 積) に束ねる再結合
   (`Fintype.sum_prod_type`、`Mathlib/Data/Fintype/BigOperators.lean` に在庫) が 1 段要る。
6. **`ErrorAnalysis` は選択がテストする典型性の種類に鈍感**: `martonSelectRow` を「入力語上の確率法則を
   生む」という事実だけを通して読むので、`martonStrongRadius₂` / `martonBandConst₂` /
   `martonCoveringRadius₂` は `ErrorAnalysis.lean` では一度も現れない (`rg` で機械確認)。
   ⇒ 半径の配分は Phase 7 と `MarkovCore` の間だけで閉じる。

### Phase 8 — 2 ゲート + README + 親 plan 同期 + proof-log 📋

- `honesty-auditor` (新規 `sorry` + `@residual` を導入した Phase があれば必須) と
  `style-auditor` (`.lean` decl/docstring を触った全 Phase) を、触ったファイルに対して起動。
- `docs/readme-theorems.txt` に headline を追記 → `deno run -A scripts/gen_readme_table.ts --write`。
  Ch.15 行に degraded 版と並べる (章の対応は `docs/textbook-roadmap.md` Ch.15)。
- **follow-up (6a' 由来)**: WZ `Achievability/Concentration.lean` の `private` 3 本を
  `Shannon/ConditionalAEP.lean` へ再配線する (重複命題の解消)。本 plan の headline には不要なので
  Phase 7 を塞がない。
- 親 plan 同期 (下記「親との同期点」)。
- `deno run -A scripts/plan_lint.ts docs/shannon/marton-*.md docs/shannon/broadcast-channel-moonshot-plan.md`。
- **proof-log: no** (Phase 4/5/6a'/7 の proof-log を統合する metrics のみ)。

---

## 撤退ライン (frozen slug — 他文書が参照しうる)

| slug | 発動条件 | 退避 (= `sorry` + `@residual`。述語化して仮定に積むのは禁止) | 状態 |
|---|---|---|---|
| **L-MT1** | Phase 5 の typicality 具体化 (符号帳 ambient 配線 or 指数合成) が 1 leg で閉じない | `marton_mutual_covering` の body を `sorry` + `@residual(plan:marton-inner-bound-plan)` にして Phase 6–7 を先に組む | **不発動** (Phase 5 完了) |
| **L-MT2** | 決定的 `x = f(v₁,v₂)` 版が full support 前提と両立しない (D1) | 一般カーネル `K : Kernel (V₁ × V₂) α` 形で主定理を述べる。決定的版は別 leg。失うのは EGK Thm 8.3 逐語形との一致だけ (docstring に明示 → Phase 7 受け入れ条件) | **発動・解決済** |
| **L-MT3** | Phase 3 の 5-tuple ambient plumbing が 4-tuple の写経で済まず爆発する | 補助変数を `V := V₁ × V₂` と束ねた 4-tuple に落とし、射影を後付けする | **不発動** (Phase 3 完了) |
| **L-MT4** | Phase 6a の非構成的 encoder / 選択索引の独立性が既存 `bcCodebookToCode` 系と噛み合わない | sum-rate 制約なしの**退化版** (`V₁ ⟂ V₂`) を先に閉じる。mutual covering 不要 (`I₁₂ = 0`) | **trigger 条件は 6a で成立したが発動せず**。方針 B (D5) が成功したので**もはや trigger しない** — 退避先は Phase 1/4/5 の成果を headline に載せられず B に劣る |
| **L-MT5** | Phase 4 の鋭化 (3 変数独立性 + Tonelli) が閉じない | 粗い版のまま上を組み、headline の sum-rate 制約を `R₁+R₂ < I₁+I₂−2·I₁₂` に**弱化**。真の Marton は別 plan へ split | **不発動** (Phase 4 完了)。なお D5 の障害には対応しない |
| **L-MT6** | Phase 7 の ε 配分 7 系統 (→ Phase 7 設計事実 3) / 三重和を 2 段 pigeonhole へ再結合する段 (→ 同 5) が閉じない | headline を `sorry` + `@residual(plan:marton-assembly-plan)` に退避し、Phase 6b までの部品を proof-done として登録する | **未発動 (active)** — 残 Phase の唯一の生きた撤退口 |

> **禁止事項の再確認**: どの撤退ラインでも「covering が成立する」「選択索引が独立である」等を
> `*Hypothesis` 述語に束ねて仮説として渡す形は取らない (CLAUDE.md「検証の誠実性」tier 5)。
> 退避は必ず `sorry` + `@residual` で、署名は証明したい形のまま保つ。

---

## 親との同期点 (plan_lint 双方向照合)

親 `broadcast-channel-moonshot-plan.md` の 3 箇所が本子 plan の状態の**キャッシュ**。**衝突時は子が SoT**。

1. **Status 行**: degraded ✅ CLOSED / 一般 BC 🚧 進行中 の 2 本立て + 子へのリンク。
2. **要点の L-BC5 記述**: slug は**凍結なので消さない**。Marton 部分が解除されたこと + Körner–Marton は
   scope-out 継続、を括弧書きで足す形。
3. **Sub-plan 一覧テーブルの Marton 行**: 状態欄が進捗のキャッシュ。

Phase 6b 完了時点 (2026-07-25) で 3 箇所とも同期済。以降、本 plan の進捗が動いたら 3 の状態欄を追随させる。

---

## Settled facts (再導出が高価なものだけ)

| claim | confidence | 再検証 | notes |
|---|---|---|---|
| Marton / mutual covering に対応する Mathlib 補題は存在しない (`"Paley"` / `"second_moment"` / `"covering_lemma"` はいずれも `Found 0 declarations`) | `loogle-neg` | 在庫 §8 のクエリを再実行 | 壁ではなく自前構築。近接テンプレ補題を各項目に名指し済 |
| 決定的カーネルは in-project typicality の full support 前提を原理的に壊す (`Kernel.deterministic` の質量が `b ≠ f v` で 0) | `machine` | `Mathlib/Probability/Kernel/Basic.lean:58` + `Mathlib/MeasureTheory/Measure/Dirac.lean:44` を Read | D1 の根拠。強 typicality 版も同じ前提を要求するのでルート変更で回避不能 |
| 「選択された `V₁ⁿ` に対して一様に E1」は一般アルファベットで**偽** (補助 3 元・型 `(1/2,1/2,0)` の 1 径数族で出力側経験エントロピーが `H(Y₁)` から n 非依存の定数ずれ) | `human-judgment` | 反例族を再構成 (実 `def` を Read して逐語確認済、`proof-pivot-advisor` が反証 3 本を試みたうえで支持) | D5 の根拠。方針 B の採用理由であり、weak 在庫に戻る誘惑が出たらここを読む |
| 粗い分散上界からは sum-rate 制約が出ない (D4) | `machine` | `meas_pairCount_eq_zero_le'` (`MutualCovering.lean`) が `1/(M₁M₂p)` 項を分離しているか Read | Phase 4 で機械確認済 |

---

## 判断ログ

1. **層の境界を「抽象度」で切る (D5 で価値が実証された)**: Phase 1/4 が typicality を一切知らないのは
   設計であり偶然ではない。おかげで方針 B (weak → strong の切替) が `MutualCovering.lean` を
   **無改変**で通過し、書換は typicality 層に閉じた。6b も同型で、`ErrorAnalysis` は選択の典型性の
   種類に鈍感なまま鏡像が入った (→ Phase 7 設計事実 6)。Phase 7 でも新しい判定基準を導入するときは
   まず「どの層に属するか」を決めてから書く。
2. **weak 版は削除せず strong 版を並置する**: 6a' の書換で weak 版 4 本を消さなかったのは、
   (a) strong ⊆ weak なので両立し、(b) 復号側は weak のままで、(c) `C = 0` で strong 版が weak 版に
   退化することが領域不変性の検算になるため。Phase 7 でどちらを呼ぶかは**選択側か復号側か**で決まる
   (選択 = `martonSelectRow` は strong、復号 = `martonMessageDecoder₁/₂` は weak。逐語確認済)。
3. **半径を「パラメータ」ではなく「`ε` の計算項」にした**: `martonStrongRadius(₂)` /
   `martonCoveringRadius(₂)` を `ε` の関数として定義したので、下流の署名が持つ半径は `ε` 1 本で済む。
   6b の `V₂` 側もこの規約を守った。Phase 7 で `min` を取るときも**新しい半径パラメータは足さない**
   (足すと ε 配分が 7 系統から爆発する)。
4. **「対称だから共通/流用できる」は実物で確認するまで書かない**: 6b は plan の対称性予測を 2 件
   覆した — (a) covering 半径は受信機共通ではない (`martonStrongRadius` 依存、→ D5-2)、
   (b) 受信機 1 の Bonferroni は degraded BC 版を一切呼ばず自己完結する
   (alias 和の索引形が `Fin M₂` 単独 vs `Fin M₂ × Fin M₂'` で異なるため、鏡像元は同一ファイル内の
   Marton 受信機 1 側 6 本)。D4 の「スライス上界は両方向が要る」も同じ軸の反例。
   ⇒ Phase 7 で「degraded 版の組み立てを写経できる」と書きたくなったら、まず該当宣言を Read する。
