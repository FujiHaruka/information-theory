# less noisy broadcast channel の容量領域の等号 Lean 形式化 — ボトルネック分析

将来「plan が書いた前提を実物と突き合わせる検算ツール」「結論形で in-project と Mathlib を同時に引く
検索」を作るためのベースライン記録。

**定量データ**: [docs/metrics/bc-lessnoisy-equality.metrics.md](../metrics/bc-lessnoisy-equality.metrics.md)

参照: plan [`docs/shannon/bc-general-region-plan.md`](../shannon/bc-general-region-plan.md) /
確定事実 [`docs/shannon/bc-facts.md`](../shannon/bc-facts.md) /
在庫 8 本 (`docs/shannon/bc-*-inventory.md`)

---

## 0. 対象問題と成果物

**less noisy な broadcast channel の容量領域の単一文字特徴づけ** (Körner–Marton 1975/1977)。
全出力対に正の質量を与えるチャネルに対し、操作的に定義した容量領域が UV 外界と一致する:

```lean
@[entry_point] theorem bc_lessNoisy_capacity_eq_uv (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (hW : ∀ a b, 0 < (W a).real {b}) (hln : IsBCLessNoisy W) :
    bcCapacityRegion W = bcOuterRegionUV W
```

`InformationTheory/Shannon/BroadcastChannel/Superposition/Assembly.lean:142`。
`#print axioms` は `[propext, Classical.choice, Quot.sound]`。**明示仮説は 2 本だけ**で、
`hW` は全支持の regularity、`hln` は両領域を一切参照しないチャネルレベルの述語
(どちらも load-bearing ではない — honesty 監査の判定は plan §Phase 5)。

新設ファイル (すべて 0 error / 0 `sorry` / 0 `@residual`。行数と decl 数は実測):

| ファイル | 行 | decl | 役割 |
|---|---|---|---|
| `BroadcastChannel/Classes.lean` | 253 | 9 | 比較クラス 3 本 + 包含鎖 `degraded ⊆ less noisy ⊆ more capable` |
| `BroadcastChannel/MartonUnion.lean` | 110 | 6 | 補助アルファベットについての Marton 内界の union |
| `OuterBoundUV/MartonBridge.lean` | 523 | 31 | 内界と外界を同じ `ℕ` 添字に載せる橋 |
| `OuterBoundUV/Quantization.lean` | 393 | 23 | 補助変数の有限量子化と裾評価 (S5) |
| `OuterBoundUV/Region.lean` | 626 | 41 | UV 外界の集合版 + チャネル法の Markov 鎖 (分割 A + S4) |
| `Superposition/Region.lean` | 213 | 8 | superposition 内界 + 情報量スロット同定 (S0–S3) |
| `Superposition/TimeShare.lean` | 645 | 45 | 時分割の補助への吸収 (S6) |
| `Superposition/FullSupport.lean` | 615 | 26 | 全支持への摂動 (S7) |
| `Superposition/Assembly.lean` | 159 | 7 | 逆包含 + headline 等号 (S8) |
| `Shannon/CondMutualInfoMixture.lean` | 193 | 7 | 混合法と再符号化不変性 (分割 A で切り出し) |

`InformationTheory/` 全体の差分は 16 ファイル / +4005 −802 行 (`git diff --stat 210b7558~1..09ee5234`)。
`docs/` 側は 13 ファイル / +4933 −298 行 — **散文のほうが Lean より多い**。

---

## 1. 問題のキャラクター

支配項は Mathlib 探索でも in-project 資産の再利用可否でもなく、**「plan が書いた命題が真か」の検算**
だった。Mathlib の 0-hit は 15 件あったがすべて壁ではないと判定され、`@residual(wall:…)` は 1 本も
書かれていない。時間を食ったのは在庫 leg で、そこが 6 leg 中ほぼ毎回 plan の誤りを見つけた。

過去の proof-log との比較:

| 家系 | 支配項 | 効くツール |
|---|---|---|
| `shannon-hartley-converse-final` | Mathlib のどこに何があるか | loogle |
| `marton-inner-bound` | 自分たちが書いた資産のどこに何があるか | in-project の型検索 |
| **本件** | **plan が書いた命題・仮説・見積りが実物と合っているか** | **plan と実物の突合、probe の自動化** |

3 つ目は前 2 つと違い、検索の改良では埋まらない。plan は散文で、実物はコードなので、
**突き合わせるには一度 Lean を書いてコンパイラに通すしかない**。この家系が在庫 leg で
毎回 probe を書いたのはその理由による。

---

## 2. 数学的方針

### (1) 内界の選択はクラスごとに変わる

plan は当初「残る包含は `bcOuterRegionUV ⊆ martonRegionUnionFS` の 1 本」としていたが、
これは**偽**だった (→ 4.1)。共通補助 `U₀` を持たない Marton 内界は劣化 BSC 対ですら容量領域より
真に小さい。等号を狙うクラスでは superposition (cloud + satellite) を使う。
Marton union の順包含 `martonRegionUnion ⊆ bcOuterRegionUV` は一般 BC の内界としてそのまま残る。

### (2) 逆包含を 4 段に割る

外界の点 (`ν` は `ℕ × ℕ × α × β₁ × β₂` 上の任意のチャネル法) から内界の点を作るのに、
`ν` の持つ不都合を 1 つずつ潰す:

- **S5 量子化** — 補助が `ℕ` 値だと `IsBCLessNoisy` の `∀ (U : Type u) [Fintype U]` に渡せない。
  `ULift (Fin (m+1))` へ切り詰め、落ちた分を裾 `ν {q | m ≤ q.1} · log |β₂|` で評価する。
- **S6 時分割** — 外界は 2 制約の交わりの union だが内界は矩形の union。時分割変数 `Q` を
  補助 `U` に吸収して矩形に落とす。superposition では効く (Marton では `I(V₁;V₂)` が `H(Q)` だけ
  増えるので効かない — plan §Phase 2 の実測)。
- **S7 摂動** — 内界の達成側は全支持を要求するが `ν` から読んだ対は破りうる。一様分布と混ぜる。
- **S8 組み立て** — S5 の `m → ∞` と S7 の `δ → 0` を極限に載せて closure で回収。

### (3) 二重極限は 1 本の対角線に載る

`m → ∞` (量子化の裾) と `δ → 0` (摂動の損失) は独立なので、`m := k` / `δ := 1/(k+1)` で
**対角線 1 本**に乗る。plan の擬似 Lean は 2 本の極限と交互列を想定していたが、部分列選択も
交互列も要らなかった (S8 在庫の probe で確認)。

### (4) 全平面規約が下流を決めた

外界 `bcOuterRegionUV` は第一象限制約を持たない全平面版で、これは本キャンペーンの前
(Phase 4b、`c768cc00` まで) に確定していた。等号を述べるには内界側も揃える必要があり、
定義段で `martonRegion` から `0 ≤ p.1 ∧ 0 ≤ p.2` を除いた (`2c938fe0`)。
**これをやるまで等号はどのクラスでも述べられなかった**。

代償は、外界の点が `R₂ < 0` を取りうることである。これが 4 step 先の S6 で
被覆義務を 1 本増やした (→ 4.4)。

---

## 3. 補題探索の実録

### 3.1 Mathlib 側 — 0-hit 15 件、壁 0 件

在庫 8 本を通じて `Found 0 declarations` が 15 件出たが、**そのすべてが「壁ではない」と判定され、
判定は最後まで覆らなかった**。内訳と代替:

| loogle クエリ | 在庫 | 代わりに使ったもの |
|---|---|---|
| `"mutualInfo"` / `"Degraded"` / `"lessNoisy"` / `"Capable"` / `"semiDeterministic"` / `"Blackwell"` (6 件) | phase5-class | 情報理論のチャネル比較は Mathlib の射程外。in-project の `Shannon.mutualInfo` で定義する側 |
| `Kernel.comap, Measure.compProd, Measure.map` | bridge | in-project `compProd_comap_map_prodMap` (`CodeToAmbient.lean:346`) が既に埋めていた (`cause:loogle-blind`) |
| `condDistrib, klDiv` | bridge | `condMutualInfo` は in-project 自作。必要な補題は揃っていた |
| `klDiv, iSup` / `, Monotone` / `, generateFrom` / `, Filter.Tendsto` (4 件) | lessnoisy | 「MI = 有限量子化の上限」の一般定理は無い。**要らない** — 裾評価 `≤ P(U≥m)·log |β₂|` で足りる |
| `klDiv, Nat.min` | s5 | 同上 |
| `ConcaveOn, klDiv` | s7 | 相互情報量の入力分布についての凹性は Mathlib にも in-project にも無い (`rg 'concave'` 実測 0)。**S7 は凹性を使わない** — タグ変数経由の混合恒等式で代替 |
| `ENNReal.Tendsto.toReal` | s8 | → 3.2 |

**「一般定理が無い」の 5 件がいずれも「その一般定理は要らない」に落ちた**のがこの家系の特徴。
量子化の極限を「MI は有限量子化の上限」という一般定理から出そうとすると Mathlib に無いが、
裾を初等的に評価すれば済む。**在庫段階で「必要なもの」を一段抽象度の低い形に言い換えると
0-hit が消える**、というのがここから取れる一般則。

### 3.2 「Mathlib に無い」が実は「引き方が違った」— 独立に 2 件

同じ機構が 1 家系のなかで 2 回起きた。どちらも**名前で引いて 0-hit、結論形で引いて即ヒット**。

**(a) S8 の極限 (`7aac8226`)**

```
loogle "ENNReal.Tendsto.toReal"                             → Found 0 declarations
loogle "|- Filter.Tendsto (fun _ => ENNReal.toReal _) _ _"  → ENNReal.tendsto_toReal (1 件)
```

dot-notation 版が無いだけで本体は在り、`.comp` 1 発で足りた。

**(b) refactor leg の重複解消 F-c (`114d7654`)**

`ℝ≥0∞` の不等式を `.toReal` に落とす手書きイディオムが BC 家系に 4 箇所あった:

```lean
have hmono := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hfin_a, hfin_c⟩) hle
rw [ENNReal.toReal_add hfin_a hfin_c] at hmono
```

結論形で引くと 1 発だった:

```
loogle "|- ENNReal.toReal _ ≤ ENNReal.toReal _ + ENNReal.toReal _"
  → Found 4 declarations …, Of these, 3 match your pattern(s).
    ENNReal.toReal_add_le / ENNReal.toReal_le_add / ENNReal.toReal_le_add'
```

`ENNReal.toReal_le_add` (`Mathlib/Data/ENNReal/Operations.lean:170`) は
**置換前の in-project consumer が 0 件**だった。つまりこのプロジェクトの誰もこの補題を見つけて
おらず、同じ 2 行を 4 回書き写していた。4 箇所とも 1 呼び出しに潰れて `+4 −10` 行。

**教訓**: 名前検索の 0-hit は「無い」ではなく「その名前では無い」。Mathlib はこの近傍で
**語順だけが違う別命題**を並べている — `toReal_add_le` は無条件の劣加法性
`(a+b).toReal ≤ a.toReal + b.toReal`、`toReal_le_add` は仮説 `a ≤ b + c` を `.toReal` 側へ
移す形で、名前は 2 語の順序しか違わない。語順を 1 つ間違えた名前検索は構造的に外し、
しかも**外したことに気づく手がかりが無い**。結論形検索はこの誤りに耐性がある。
**この家系では名前 0-hit → 結論形ヒットが 2 件独立に出た** — 1 件なら偶然だが 2 件は機構。

---

## 4. 試行錯誤と後戻り

### 4.1 plan の次手が偽だった — 数値実験で潰し、経路ごと差し替えた

**症状**: plan は「残る包含は `bcOuterRegionUV W ⊆ martonRegionUnionFS W` の 1 本」として
撤退ライン L-BCO8 まで張っていた。この命題が**偽**だった (`9a41c3b7` / `9e6050b7`)。

**原因**: `martonRegionUnion` は EGK Thm 8.3 の private message のみ版で**共通補助 `U₀` を持たない**。
`U₀` は `martonRegion` の署名に足す余地がなく (足すのは符号化定理からの作り直し)、
劣化 BSC 対 (`q = 0.1`, `p = 0.25`) の superposition corner で 3 制約の最小スラックが
補助アルファベット `(2,2)`〜`(5,5)` で一様に約 `−0.013` に頭打ちする。しかもその corner は
`bc_capacity_subset_uv` により外界に入るので、**劣化 BSC 対ですら `martonRegionUnionFS ⊊ bcCapacityRegion`**。

**抜け方**: 目標を superposition 内界へ差し替え、L-BCO8 を無効化した。plan は
「正直な限界」の但し書きとしてこの限界を**書いてはいた**が、どのクラスで発火するかを
詰めていなかった。

**数値実験の設計が効いた点** (`docs/shannon/bc-marton-union-gap-check.py`):

- **sim を先に実 def と照合した**。`martonInfo₁/₂/V₁V₂` (`Marton/Setup.lean`)・`bcInfo₁/₂`
  (`Achievability/Setup.lean`)・`entropy` (`Shannon/Bridge.lean`) から逐語対応させ、
  閉形式 4 項目と 10 桁一致することを確認してから最適化を回した。
- **退化境界 2 本を対照実験にした**。`p = 1/2` (受信機 2 が無用) では slack がちょうど `0.000000`。
  境界で 0 ・内点で負、という形が「反例が最適化のノイズでない」ことの傍証になる。
- **確信度を `human-judgment` で台帳に置いた** ([`bc-facts.md`](../shannon/bc-facts.md))。
  数値実験は Lean の機械検証ではないので、3 値のうち最も保守的なものを採る。

**教訓**: 数値で FALSE を出すときに必要なのは 3 点セット — sim ↔ 実 def の照合 /
退化境界を対照に置く / 確信度を落として台帳に置く。**最初の 1 つを省くと「反例」が
sim の artefact になる**のは CLAUDE.md が既に規則化しているが、2 つ目 (対照実験) は
書かれていない。最適化ベースの反例では、これが無いと収束不良と区別できない。

### 4.2 在庫が plan を訂正したのが S6 / S7 / S8 の 3 leg 連続

いずれも同じ機構: **plan が「あとは X だけ」と書いたが、前 step の到達点が要求する仮説を
1 本ずつ数えていなかった**。

| step | plan の主張 | 在庫の実測 |
|---|---|---|
| **S6** | 逆包含は `bound₂` と `sumBound₂` の 2 本で被覆できる | **偽**。`bound₁` を落とすと `a = b = J = 0, R₁ = 1, R₂ = −2` が反例 (Lean で機械確認)。plan の擬似 Lean にも同じ穴 |
| **S7** | 摂動対象は対 `(pU, K)` ではなく法 `ν'` が安い | **内部実装としては正しいが署名としては誤り**。S6 の到達点が `ν` を存在量化して捨てるので法 → 法では合成できず、headline は対レベルに置くしかない |
| **S8** | 運ぶのは S5 の裾評価 3 本 | **スロット 1 の担い手 `h₁` が plan 上に存在しなかった**。実物は `uvInfo₁_map_uvRelabel` が `e₂ := id` で等式のまま当たり、新設 3 行で済んだ |

**教訓**: 「残るのは組み立てだけ」は**入口の仮説の本数で検算する**。到達点の署名を数えるのは
在庫 leg の最初の数分の作業で、plan の粗見積りより安い。ツール化するなら
「plan が名指した到達点の署名を `#check` で展開し、次 step の入口が要求する仮説と本数を突き合わせる」
の自動化が直球。`variable` ブロックから流れ込む仮説は宣言行に出ないので、**`rg` では作れない**。

### 4.3 乗法だけの下界は偽 — 罰則の形は命題の性質

**症状**: S7 の摂動でスロット 2 の下界を
`uvInfo₂ ((1−ε)ν + εσ) ≥ (1−ε) · uvInfo₂ ν` の形で立てたかった。

**実物**: **偽**。在庫が `U = X = Y₂ = Bool` で数値反例を持っている:

| ε | 混合の `I` | `(1−ε)·I(ν)` | 乗法だけの下界 | 加法罰則つき `(1−ε)I(ν) − h(ε)` |
|---|---|---|---|---|
| 0.5 | 0.130812 | 0.346574 | 偽 | −0.346574 |
| 0.1 | 0.494632 | 0.623832 | 偽 | 0.298749 |
| 0.01 | 0.661668 | 0.686216 | 偽 | 0.630214 |
| 0.001 | 0.688847 | 0.692454 | 偽 | 0.684547 |

**原因**: 混合を作るタグ変数それ自体が相互情報量を持ちうる。だから
`Real.binEntropy ε` の**加法**罰則は証明技法の都合ではなく命題の性質で、`δ → 0` には無害
(`binEntropy` は 0 で連続かつ値 0)。

**教訓**: これは**もっともらしさ検査を通過してしまう**形の誤りである。「摂動を小さくすれば
情報量の劣化も比例して小さい」は直観に合い、型も通る。`ε → 0` の極限でだけ見ると
どちらの形でも成立するので、**極限だけ確かめる検算では区別できない**。区別するには
`ε` を固定した中間値 (上表の 0.1 や 0.5) を 1 点入れる必要がある。

### 4.4 「不要に見える制約」が 4 step 先で load-bearing になった

**症状**: 外界の点は 4 制約 (`bound₁` / `bound₂` / `sumBound₂` / `sumBound₁`) を持つ。
S8 の逆包含はこのうち 3 本しか使わず `sumBound₁` を `obtain ⟨hb₁, hb₂, hs₂, -⟩` で捨てている。
同じ感覚でブリーフは S6 の設計から `bound₁` も落としていた。

**原因**: **全平面規約** (→ 2.(4))。外界に第一象限制約が無いので `R₂ < 0` の点が領域に入る。
このとき `sumBound₂` は `R₁ ≤ a + b − R₂` しか与えず、右辺は `I(X;Y₁)` を超えうる。
内界側は `bcInfo₁ ≤ log |β₁|` で有界なので `bound₁` なしでは被覆できない。
埋め方自体は `bound₁` から `R₁ ≤ (uvInfo₁ ν).toReal` を取って DPI 1 発 (`V → X → Y₁`) で済む。

**教訓**: 等号を述べるために揃えた規約 (第一象限制約の除去) が、4 step 先の被覆義務を 1 本
増やした。**規約変更の波及は「その規約を使う宣言」ではなく「その規約が新たに許した点」に出る**
ので、consumer グラフでは追えない。捨ててよい制約と捨ててはいけない制約の区別は
`obtain … -` の位置ごとに独立に点検するしかない。

### 4.5 内ループの `lake env lean` が一部の linter に盲目だった

**症状**: S7 の実装中、`lake env lean` が完全に沈黙するファイルに対し `lake build` が
`linter.flexible` / `linter.style.show` / `linter.unusedDecidableInType` を出した
(plan F-20 は計 19 件と記録。ファイルは既に修正済で transcript の出力も head 打ち切りのため、
本 proof-log では**件数は再導出できず、linter の種別のみ実測で確認した**)。

**抜け方**: `lake build` (全再ビルド) ではなく、`lakefile.toml` の `leanOptions` を再現する
フラグ付き単ファイル検査に切り替えた:

```bash
lake env lean -D linter.mathlibStandardSet=true -D linter.unusedFintypeInType=false <file>
```

S8 は在庫の probe 段階からこの条件で書いたので、**実装後の linter 掃除が 0 件**で着地した。

**教訓**: 検証ループの穴は「証明が通るか」ではなく「規約が通るか」の側に開く。CLAUDE.md は
`lake env lean` を definitive check と書いているが、それは**エラーについてのみ**正しい。
この 1 行のフラグは `lake build` の linter 条件を全再ビルドなしで再現するので、
**内ループの既定コマンドをこちらに変えるだけで穴が閉じる**。

### 4.6 「probe で機械確認済」が保証するもの・しないもの

**症状**: refactor leg (F-21 / F-22) の在庫は「重複は 2 本、`rfl` まで逐語一致」を probe で
確認していた。実測は 2 点で外れた。

- **重複は 3 本**だった。移設しようとした可測性補題と型も証明項も同一の private 補題を
  `OuterBoundUV/Region.lean:129` (`measurable_uvUnsplit`) が既に持っていた ⟹ 移設側を捨てて既存を消費。
- **`inferInstance` が落ちなかった**。在庫は `uvConstLaw_isProbabilityMeasure` が
  `inferInstance` で落ちると予測したが、`uvConstLaw` が非 reducible な `def` なので
  instance 探索が要求された透明度で展開しない。`uvLawOfInput_isProbabilityMeasure W _` と
  明示項で書いた (`OuterBoundUV/Region.lean:457`)。

**教訓**: probe は**肯定的な同一性** (この 2 本は等しい) を確かめる道具であり、そこから
**完全性** (ちょうど 2 本しかない) も**自動性** (探索が見つける) も出てこない。前者は着手時に
結論形での再検索で、後者は 1 行書いてコンパイラに落とさせて確かめる。
4.2 と同じ「機械確認の射程を超えて読む」誤りで、家系を通じて 4 leg 連続で出た。

### 4.7 却下は「この step では」と限定して書く

**症状**: S6 の在庫が `IsUVChannelLaw.condMutualInfo_le_map_cond` を「欲しい向きと逆」と判定した。
S7 は**まさにその向き** (補助の粗視化) を必要とし、5 行で当たった。

**教訓**: 在庫の却下判定は step の目標に相対的なので、**却下理由に step を明記しないと
次の step が同じ資産を自作する**。「向きが逆」は step が変われば反転する種類の理由で、
「Mathlib に無い」のような step 非依存の理由と混ぜて書くべきではない。

---

## 5. ボトルネックではなかったもの

- **Mathlib 壁**。`@residual(wall:…)` は 1 本も書かれず、撤退ライン L-BCO9 は S5 / S6 / S7 / S8 の
  4 段連続で不発動のまま判定の担い手を失って retire された。0-hit 15 件はすべて代替が立った。
- **honesty**。`sorry` を 1 本も残していないので `honesty-auditor` の起動は家系全体で 2 回だけ
  (定義段と S0–S2)。load-bearing hyp の誘惑が出る場面 — S6 の `bound₁`、S7 の全支持仮説 —
  はいずれも**実際に証明が通った**ので、述語に束ねる誘惑が発火する前に消えた。
- **証明の筋**。教科書 (Körner–Marton / El Gamal–Kim) の構造をそのまま追えた。S3 / S4 / S8 は
  **自作した数学が 0 行**で、既存部品の合成だけで閉じている (S4 の親玉は 13 行)。
- **型検査 / universe**。`IsBCLessNoisy` が `∀ (U : Type u)` を量化する点が唯一の universe 問題
  だったが、`bcAuxAlphabet = ULift.{u} (Fin (k+1))` が 0 行で吸収した (撤退ライン L-BCO2 不発動)。
- **ファイル分割**。`OuterBoundUV/Assembly.lean` の 1588 行と `Superposition*` クラスタの
  ディレクトリ昇格はどちらも純粋な移設で、新しい数学 0 行。F-19 の import 書換は予測どおり
  7 行で外部波及 0 件。

---

## 6. 計測から見えたこと

数値は [metrics.md](../metrics/bc-lessnoisy-equality.metrics.md) が SoT。そこから読める性質を 3 点。

**(a) 最も編集されたファイルは Lean ではなく plan だった**。編集ファイル別 Edit 回数で
`docs/shannon/bc-general-region-plan.md` が 218 回。Lean 側の最大は
`SuperpositionFullSupport.lean` の 45 回で、**どの `.lean` ファイルよりも plan のほうが 4 倍以上
編集されている**。relay 型の運用では各 leg の末尾に plan 同期 leg が入るので、
plan が構造的にホットスポットになる。派遣したエージェントの内訳も
`lean-planner` 12 体に対し `lean-implementer` 16 体で、同じオーダーにある。
8.(b) の誤記がこのホットスポットで起きたのは偶然ではない。

**(b) オーケストレーターの対象ファイル Edit は 0**。実装はすべてサブエージェントが書いており、
親 transcript には `Agent` しか残らない。marton-inner-bound の proof-log が指摘した
「オーケストレーター型 leg では計測手段が実装コストを構造的に過少報告する」性質は本件でも同じで、
`--no-subagents` で読むと実作業がまるごと消える。

**(c) `python3` が Bash 内訳に立っている**。Lean 形式化の leg で数値計算が走るのは、
4.1 の反例探索と 4.3 の罰則形の検証によるもの。**「証明できないことを確かめる」ための計算**が
この家系のコストの一部を占めた。

---

## 7. ツール開発への示唆

| 優先度 | 機能 | このセッションで節約できたであろうコスト |
|---|---|---|
| 高 | **plan の到達点と次 step の入口の仮説突合** — plan が名指した宣言を `#check` で展開し、次 step が要求する仮説と本数を diff する。`variable` ブロック由来の仮説は宣言行に出ないので `rg` では作れない | 4.2 の 3 leg 連続の訂正。とくに S6 の `bound₁` (**被覆漏れ = 逆包含が偽**) と S8 の `h₁` (存在しない担い手に自作見積り) |
| 高 | **結論形検索を名前検索の既定フォールバックにする** — 名前 0-hit のとき結論パターンを自動生成して再検索 | 3.2 の 2 件。とくに `ENNReal.toReal_le_add` は in-project consumer 0 = 誰も見つけていなかった |
| 中 | **内ループの既定を `lake env lean -D linter.mathlibStandardSet=true` にする** | 4.5。S7 で発覚し S8 で実害 0 になった差分がそのまま利得 |
| 中 | **数値反例の対照実験テンプレート** — 退化境界を自動で 2 本入れて「境界で 0」を確認させる | 4.1。最適化ベースの反例と収束不良を区別する唯一の安い手段 |
| 中 | **`plan_lint.ts` に「plan が書いた行数 vs 実物の行数」の照合を足す** — commit hash と併記された行数は `git show <c>:<f> \| wc -l` で機械照合できる | 8.(b)。誤記 1 件が 2 本の在庫で「自分の見積りは上振れしない」根拠として引用され、直後の S6 が帯の上を 13% 超えた |
| 中 | **在庫の却下理由に step スコープを必須にする** (「この step では逆向き」と「Mathlib に無い」を型で分ける) | 4.7 |
| 低 | **不等式の中間値検査** — `ε → 0` でしか確かめていない下界に中間値を 1 点入れさせる | 4.3 の乗法下界。極限だけの検算では通ってしまう |
| 低 | probe の予測を「肯定的同一性」と「完全性・自動性」に型で分ける | 4.6 の 2 件 |

---

## 8. 補足

### 見積り手法が家系のなかで収束した — ただし plan の記録が 1 件壊れていた

行数見積りの実測 (すべて `git show <commit>:<file> | wc -l` で再導出。plan 散文からの転記ではない):

| step | plan の粗見積り | 在庫の見積り | 実測 (as-landed) | 見積りの中か |
|---|---|---|---|---|
| S5 | ~160 | ~280 (帯なし) | **375** (style 後 382) | **外れ (上に 34%)** |
| S6 | ~180 | 帯 380–480 | **544** (flags 後 545) | **外れ (上に 13%)** |
| S7 | ~120 | 帯 720–850 | 802 | 中 |
| S8 | ~90 | 帯 175–215 | 163 + 上流移動 15 = 178 | 中 |

読み方は 2 段ある。

**(a) 手法の収束**。S5 / S6 の在庫は probe が測った**数学の行数**に行ごとの docstring 分を足しただけで、
module doc と `omit` 最小化のための `variable` 束分割を積んでいなかった。S7 の在庫から
見積り表に「数学 (probe 実測) / 散文・section」の**2 列**と `module doc` の独立行が入り、
**2 枠に分けた S7 と S8 はどちらも帯の中に入った**。probe があれば数学の行数は当たる、
当たらないのは散文と section 構造 — というのが 4 step で確定した。

**(b) plan の S5 の行数が誤っていた**。plan は S5 を `289 行 (見積 280)` と記録して
「ほぼ的中」と評価しているが、実測は as-landed 375 行、plan 同期時点で 382 行。
plan 同期を担当したエージェントは `wc -l` を実際に打っており (transcript で確認)、
**測った値と書いた値が違う**。S5 は当たっていたのではなく **34% 外していた**。

問題は誤記そのものではなく**その後の使われ方**で、この数字は 2 本の下流在庫で
**「自分の見積りも同じくらい当たる」の較正基準**として引用された。しかも
**引用された向きが 2 本で逆**である:

- S6 在庫: 「S3 / S4 のような**下振れ**は期待できない … **S5 が 280→289 で的中したのと同じ構造**だから」
- S7 在庫: 「S6 のような**上振れ**は期待しない … **S5 が 280 → 289 で的中したのと同じ構造**」

同じ 1 つの数値が、一方では「低く外れない」の根拠、他方では「高く外れない」の根拠になっている。
較正基準として使うには**方向を持たない**ということで、これは基準が実測ではなく
「当たった」という評価語だけで運ばれていた徴候。S6 はこの直後に、自分が守っていない側
(上) へ帯を 13% 超えた。S7 が帯に入ったのは較正基準のおかげではなく、
見積りを 2 枠に分けた (a) の方法変更による。

**stale な 1 つの数値が、2 本の在庫で確信度の議論に化けた**。
CLAUDE.md の「re-derive > cache」はまさにこれを禁じているが、
禁止対象が「機械で安く引ける事実」と書かれているため、**行数のような
「実測したはずの数値」は対象と読まれていない**。`git show <commit>:<file> | wc -l` は
機械で安く引ける典型なので、ここは cache 側ではなく re-derive 側に置くのが正しい。

`scripts/plan_lint.ts` は decl / `file:line` / wall slug の参照を突き合わせるが、
**plan が書いた行数と実物の行数は照合していない**。commit hash と併記された行数は
機械照合できるので、これは低コストで足せる規則。

### 撤退ラインが「判定の担い手」を失う

L-BCO9 は「S6 が閉じないとき」を発動条件としていたが、S5 / S6 / S7 / S8 が 4 段連続で
不発動になった時点で、この slug を評価する宣言が 1 本も残らなくなった。plan は
これを「不発動」ではなく **retire** として記録している。撤退ラインは目標に紐づくので、
**目標が差し替わったとき (4.1) と、全段が通ったときの両方で失効する**。
前者は L-BCO8 で「無効化」として、後者は L-BCO9 で「retire」として、
別の語彙で区別されている。
