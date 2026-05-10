# Shannon converse (Phase 4-δ-(b)) Markov chain encoder 版 Lean 形式化 — ボトルネック分析

将来「Mathlib に存在する補題形に合わせて定理本体を pivot するエージェント」「`StandardBorelSpace` のような型クラス制約の伝搬を事前に静的検出するツール」「3 重 compProd 等の `MeasurableEquiv` plumbing を生成する補助ツール」を作るためのベースライン記録。Phase 4-γ (Shannon converse 本体) を Markov chain `Msg → encoder ∘ Msg → Yo` 仮定下に拡張し、`I(Msg; Yo) ≤ I(encoder ∘ Msg; Yo)` で encoder 入りの single-shot converse を導く作業を **3 セッション**で完走した記録。

**定量データ**: [docs/metrics/shannon-markov-converse.metrics.md](metrics/shannon-markov-converse.metrics.md)

## 0. 対象問題と成果物

Phase 4-γ で得た encoder 無し版

```
log |M| ≤ I(Msg; Yo).toReal + h(Pe) + Pe · log(|M| − 1)
```

を、Markov chain `Msg → Z → Yo` 仮定下に encoder (= 一般の中間変数 `Z = encoder ∘ Msg`) を入れた版に拡張する：

```
shannon_converse_single_shot_markov_encoder
  (Msg : Ω → M) (encoder : M → X) (Yo : Ω → Y) (decoder : Y → M)
  (hMarkov : IsMarkovChain μ Msg (encoder ∘ Msg) Yo) :
  log |M| ≤ I(encoder ∘ Msg; Yo).toReal + h(Pe) + Pe · log(|M| − 1)
```

成果物:

- `Common2026/Shannon/CondMutualInfo.lean` — **新規 353 行**、0 errors / 0 sorry
  - `condMutualInfo` (compProd 形定義)
  - `IsMarkovChain` (γ-form: joint factorization)
  - `mutualInfo_chain_rule` (3 重 compProd plumbing 経由)
  - `condMutualInfo_eq_zero_of_markov`
  - `mutualInfo_le_of_markov` (`I(X; Y) ≤ I(Z; Y)` under `X → Z → Y`)
  - 補助 `permZXY_ZYX` / `permZYX_Z_XY` (`MeasurableEquiv` 2 本)、`product_map_perm_eq_compProd` / `factored_map_perm_eq_compProd_prod` (private plumbing 補題 2 本)
- `Common2026/Shannon/Converse.lean` — `shannon_converse_single_shot_markov_encoder` を末尾追記 (240 行)
- `Common2026/Shannon/MutualInfo.lean` — `klDiv_map_measurableEquiv` を `private` から public に格上げ (1 行 diff)
- `docs/shannon-condmi-inventory.md` — Phase 4-δ-(b) 着手前の Mathlib 在庫調査 (146 行、subagent 3 並列で 1 ターン)

`lake env lean Common2026/Shannon/CondMutualInfo.lean` / `Converse.lean` ともに silent。`lake build Common2026.Shannon.CondMutualInfo Common2026.Shannon.Converse` 通過。

## 1. 問題のキャラクター

「**Mathlib に補題が無いことが事前にわかった上での自作 plumbing**」型。在庫調査 (`docs/shannon-condmi-inventory.md`) で `condMutualInfo` 定義と Markov chain 述語が Mathlib 不在であること、chain rule plumbing は Phase 4-α (DPI) 級の作業量 (135〜195 行見積) を要することは事前に見えていた。実際には **3 重 compProd の `MeasurableEquiv` plumbing** が見積 40〜60 行に対し ~200 行に膨れ、見積 4× オーバー。

過去のフェーズとの規模感比較:

| Phase | 主要ファイル | 行数 | 性格 |
|---|---|---|---|
| Phase 4-α (DPI) | `Common2026/Shannon/DPI.lean` | 168 行 | klDiv の DPI 接続 |
| Phase 4-β (bridge) | `Common2026/Shannon/Bridge.lean` | 588 行 | KL ↔ entropy − condEntropy 同値 |
| Phase 4-γ (本体) | `Common2026/Shannon/Converse.lean` | 124 行 → 240 行 | plumbing 層の組み合わせ (Markov 版で +116 行) |
| **Phase 4-δ-(b) (本回)** | **`Common2026/Shannon/CondMutualInfo.lean`** | **353 行** | condMI 定義 + chain rule 自作 plumbing |

## 2. 数学的方針

主応用 `mutualInfo_le_of_markov` は次の 3 段で済む:

```
I(Msg; Yo)
  ≤ I((Msg, Z); Yo)                 -- Phase 4-α DPI を Prod.snd で適用 (+ mutualInfo_comm)
  = I(Z; Yo) + I(Msg; Yo | Z)       -- mutualInfo_chain_rule
  = I(Z; Yo) + 0                    -- condMutualInfo_eq_zero_of_markov (γ-form Markov)
```

各 `≤ / =` を `have` で立てて `linarith`、という素直な calc。**ただし `mutualInfo_chain_rule` の plumbing が本回の山**で、これが本ファイル 353 行のうち約 200 行を占める。

### 設計判断 1: `condMutualInfo` の定義を **compProd 形** に固定

教科書的な積分形:

```
condMutualInfo μ Xs Yo Zc := ∫⁻ z, klDiv (κ_joint z) (κ_factored z) ∂(μ.map Zc)
```

を最初は想定していた。しかし `klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η) = ∫⁻ klDiv (κ x) (η x) ∂μ` 形 (条件付き KL の積分公式) が **Mathlib に無い** ことが skeleton 直後に判明 (loogle queries: `"InformationTheory.klDiv (Measure.compProd _ _) (Measure.compProd _ _)"` 系を 5 種類試して空振り)。この公式を自作すると 50〜80 行になるため、**定義を compProd 形に切り替え**:

```lean
noncomputable def condMutualInfo (Xs Yo Zc) : ℝ≥0∞ :=
  klDiv ((μ.map Zc) ⊗ₘ condDistrib (fun ω => (Xs ω, Yo ω)) Zc μ)
        ((μ.map Zc) ⊗ₘ ((condDistrib Xs Zc μ) ×ₖ (condDistrib Yo Zc μ)))
```

副次効果として `condMutualInfo_eq_zero_of_markov` が **γ-form Markov ⇒ 第 1 引数 = 第 2 引数 ⇒ `klDiv_self`** で 10 行で終わる。

### 設計判断 2: Markov 述語を **γ-form (joint factorization)** に

inventory (`shannon-condmi-inventory.md` §設計判断) では **β-form** (`condDistrib Yo (Z, Msg) =ᵐ (condDistrib Yo Z).prodMkRight M`) を採用予定だった。理由は `condIndepFun_iff_condDistrib_prod_ae_eq_prodMkRight` (`Mathlib/Probability/Independence/Conditional.lean:867`) と直結するため。

しかし skeleton を書き始めて気付いたのは、**この Mathlib lemma が `[StandardBorelSpace Ω]` を必須インスタンスとして要求**する点。inventory 段階では Conditional.lean のシグネチャを subagent が summary でしか見ていなかったため、この hidden constraint を見落としていた。

→ **γ-form (joint factorization)**:

```lean
def IsMarkovChain (Xs Zc Yo) : Prop :=
  μ.map (fun ω => (Zc ω, Xs ω, Yo ω))
    = (μ.map Zc) ⊗ₘ ((condDistrib Xs Zc μ) ×ₖ (condDistrib Yo Zc μ))
```

に切り替えることで `Ω` への追加制約を完全回避。両形式は標準 Borel 仮定下で同値だが、γ-form は (1) `condMutualInfo_eq_zero_of_markov` を trivial にする (定義 = 第 2 引数なので `klDiv_self`)、(2) `Ω` 側の制約を持たないので主応用 `Converse.lean` 側が綺麗、という二重のメリット。

### 設計判断 3: composition を先に書いて plumbing を後回し

これは proof 戦略というよりプロセス上の判断。skeleton 完成直後に chain rule の Mathlib 不在が判明した時点で、**chain rule と condMI=0 を sorry のまま残し、`mutualInfo_le_of_markov` (合成補題) と Converse の Markov-encoder 版を先に型レベルで通す**ことを優先した。これにより:

- 後続の pivot (compProd 形定義 / γ-form Markov) が下流コードを破壊しない (signature が合っていれば中身は何でもよい) ことを確認できた
- chain rule 自作 plumbing に着手する前に「最終形が確かに converse を導くか」が型レベルで保証された

実際、後続の 2 回の pivot (`condMutualInfo` の rnDeriv 形 → compProd 形、Markov の β-form → γ-form) は composition 部のコードを 1 行も触らずに済んだ。

## 3. Mathlib 補題探索の実録

inventory フェーズで subagent 3 並列 (`condIndepFun` / `condMutualInfo` / kernel chain rule paths) を投げ、`docs/shannon-condmi-inventory.md` に整理。skeleton 着手後は実装のため追加で loogle / rg 検索した。

**見つかった主要補題** (chain rule plumbing で実際に使ったもの):

| 用途 | 場所 | 探索クエリ |
|---|---|---|
| chain rule の主役 | `Mathlib/InformationTheory/KullbackLeibler/ChainRule.lean:204` `klDiv_compProd_eq_add` | inventory で確認済 |
| Bayes 規則の kernel 形 | `Mathlib/Probability/Kernel/CondDistrib.lean:82` `compProd_map_condDistrib` | inventory |
| 3 重 compProd 結合則 | `Mathlib/Probability/Kernel/Composition/CompProd.lean:467` `Kernel.compProd_assoc` | inventory |
| `prodMkRight` の `compProd` 化 | `Mathlib/Probability/Kernel/Composition/MapComap.lean:249` `prodMkRight_apply` | rg `prodMkRight` を `Kernel/Composition/` で |
| Tonelli (Kernel 側) | `Mathlib/Probability/Kernel/MeasurableLIntegral.lean` `Measurable.lintegral_kernel_prod_right'` | rg `measurable_lintegral` を `Kernel/MeasurableLIntegral.lean` で |
| Measure 側 swap | `Mathlib/MeasureTheory/Measure/Prod.lean` `lintegral_lintegral_swap` | rg `lintegral_lintegral_swap` |
| Kernel 直積展開 | `Kernel.prod_apply` (Composition/Prod.lean) | loogle `"ProbabilityTheory.Kernel.prod, ProbabilityTheory.Kernel.prodMkRight"` |
| `Measure.map` の確率測度性 | `Measure.isProbabilityMeasure_map` | rg `isProbabilityMeasure_map` |

**「Mathlib に存在しなかった」もの (重要)**:

- **`klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η) = ∫⁻ x, klDiv (κ x) (η x) ∂μ`** — 条件付き KL の積分公式。loogle で
  - `"InformationTheory.klDiv (Measure.compProd _ _) (Measure.compProd _ _)"`
  - `"InformationTheory.klDiv (MeasureTheory.Measure.compProd _ _) _, MeasureTheory.lintegral"`
  - `"InformationTheory.klDiv, MeasureTheory.lintegral"`

  の 5 系統で空振り。Mathlib `KullbackLeibler/ChainRule.lean` には `klDiv_compProd_eq_add` (両 base 異なる版) と `klDiv_compProd_left` (`κ = η` 特例) の 2 つしかなく、第 2 項を「per-fibre 積分」に展開する形は不在。**この不在が `condMutualInfo` の定義 pivot を強制した**最大の単一要因。

- **`StandardBorelSpace (α × β)` の自動 instance** — rg `instance.*StandardBorelSpace.*Prod` を `Mathlib/MeasureTheory/MeasurableSpace/StandardBorel.lean` で空振り。`StandardBorelSpace.prod` は別ファイルにあるが、subagent inventory 時には見落としていた。これがあれば β-form Markov を保ったまま `[StandardBorelSpace M] [StandardBorelSpace X] [StandardBorelSpace Y]` 各個に書けば `Ω = M × X × Y` 経由で済んだ可能性がある (ただし主応用 `Ω` は型変数なので結局 hypothesis 化は必要)。

- **`compProd_assoc` の Measure 側等価形** — `Kernel.compProd_assoc` (`CompProd.lean:467`) は `(κ ⊗ₖ (η ⊗ₖ ξ)).map prodAssoc.symm = κ ⊗ₖ η ⊗ₖ ξ` という `map` 形。Measure 側で `(μ ⊗ₘ κ) ⊗ₘ η = (μ ⊗ₘ (κ ⊗ₖ η)).map prodAssoc` のような形を期待して loogle `"MeasureTheory.Measure.compProd, MeasurableEquiv.prodAssoc"` および rg `compProd_assoc|compProdAssoc` を打ったが Measure 側 wrapper は不在。手書きの `permZXY_ZYX` / `permZYX_Z_XY` で代替した。

- **`Measure.compProd` と `Measure.prod` の自然な書き換え** — `compProd_const : μ ⊗ₘ Kernel.const _ ν = μ.prod ν` (`MeasureCompProd.lean:141`) はあるが、逆向き「`(μ.map A).prod (μ.map B) = (μ.map A) ⊗ₘ Kernel.prodMkRight B (Kernel.const _ (μ.map B))`」のような書き換えは無い。`product_map_perm_eq_compProd` で `Measure.ext_of_lintegral` 経由で自作 (~30 行)。

## 4. 試行錯誤と後戻り

### 4.1 `condMutualInfo` 定義の pivot (rnDeriv 形 → compProd 形)

**症状**: skeleton で教科書的な積分形 `∫⁻ z, klDiv (κ_joint z) (κ_factored z) ∂(μ.map Zc)` を仮定し、chain rule の sorry を埋めようとした瞬間、`klDiv_compProd_eq_add` が返す形が「base 共有時の per-fibre 積分」ではなく「klDiv (compProd 同士)」のままであることに気づく。

**原因**: `klDiv_compProd_eq_add` は Mathlib 内で **第 2 項を compProd のままにする命題** (`klDiv (μ ⊗ₘ κ) (ν ⊗ₘ η) = klDiv μ ν + klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η)`)。条件付き KL を `∫⁻` で書くと、第 2 項を「`∫⁻` 形 = compProd 形」に書き換える補題 (Mathlib 不在) が別途必要になる。

**抜け方**: `condMutualInfo` の定義そのものを `klDiv (compProd, compProd)` 形に変更。`klDiv_compProd_eq_add` の戻り値とそのまま型一致する。

**教訓**: **「Mathlib にある補題の戻り値の形に合わせて定理本体の定義を選ぶ」** という発想を最初から持つべきだった。「教科書の定義に従う」と「Mathlib のレールに乗る」のどちらを優先するかは設計判断であり、後者を選ぶ場合は数式変形コストの大半が消える。将来のツール: 候補定義に対して「Mathlib の既存補題でこの定義を使うとき自然に出る等価形」を提示するエージェント。

### 4.2 β-form Markov の `[StandardBorelSpace Ω]` 制約

**症状**: skeleton で β-form `condDistrib Yo (Z, Msg) μ =ᵐ (condDistrib Yo Z μ).prodMkRight M` を採用したが、`condMutualInfo_eq_zero_of_markov` を埋めようと `condIndepFun_iff_condDistrib_prod_ae_eq_prodMkRight` を引いた瞬間、Lean が `failed to synthesize StandardBorelSpace Ω` を出す。

**原因**: `Conditional.lean:867` の lemma signature に `[StandardBorelSpace Ω]` が暗黙に乗っている。inventory では subagent が summary でこの constraint を拾っておらず、可視化されていなかった。

**抜け方**: Markov 述語自体を γ-form (joint factorization 等式) に変更。`Ω` への型クラス制約を回避。

**教訓**: 補題の **explicit signature の `[...]` 部分まで含めて** inventory に転記すべき (ツール仕様: subagent inventory のテンプレートに「型クラス前提条件」欄を必須化)。あるいは **`StandardBorelSpace` のような propagating type class** を「あなたの主定理にこの constraint を持ち込みますよ」と事前警告する静的検査が欲しい。Phase 4-α でも同種の制約 (`StandardBorelSpace` を `condDistrib` 経由で要求される) で 1 度ハマっており、これは反復ボトルネック。

### 4.3 chain rule plumbing の見積 4× オーバー

**症状**: inventory 見積で chain rule plumbing は 30〜50 行、associativity 込みで 40〜60 行だったが、最終的に **約 200 行** (helper 4 本 + 主補題)。

**原因の細分**:

- **`Kernel.compProd_assoc` の方向不一致**: `(κ ⊗ₖ (η ⊗ₖ ξ)).map prodAssoc.symm = κ ⊗ₖ η ⊗ₖ ξ` の形は Measure 側に直接持ち上がらず、`Measure.ext_of_lintegral` で per-test-function 展開する経路に切り替え (~80 行)。
- **`fun_prop` が `MeasurableEquiv.mk` の inline 構成を掴めない**: `permZXY_ZYX` / `permZYX_Z_XY` を `MeasurableEquiv` ラッパでなく `Equiv.mk` 直書きで書いた当初、`fun_prop` で測度可測性が降りなかった。明示的な `Measurable.prodMk` / `measurable_fst.comp` の組合せに退避 (4 ヶ所、計 ~20 行)。
- **`lintegral_prod` が integrand を unify できない**: `∫⁻ p, f (z, p) ∂((κ.prod η) z)` を `∫⁻ x, ∫⁻ y, f (z, (x, y))` に展開する際、`lintegral_prod` の第 1 引数 `f` を Lean が推論できず、明示的に `(fun b : X × Y => f (z, b))` を渡して回避。整数経路への explicit hint が 2 箇所必要。
- **`klDiv_map_measurableEquiv` の private 化解除**: 自分で書いた helper が `private` だったため、別ファイル (`CondMutualInfo.lean`) からは呼べず、`MutualInfo.lean:52` で `private theorem` → `theorem` に格上げ (Phase 4-γ 時には外部使用を想定していなかった)。

**抜け方**: 上記を順次手当て。`Measure.ext_of_lintegral` + `lintegral_compProd` + Tonelli (`lintegral_lintegral_swap`) の三段攻めで 2 つの plumbing 補題 (`product_map_perm_eq_compProd` / `factored_map_perm_eq_compProd_prod`) を作り、主定理 `mutualInfo_chain_rule` はそれを 2 回 pushforward して `klDiv_compProd_eq_add` を 1 回適用する形に整理。

**教訓**: `MeasurableEquiv` で結合則を回す plumbing は「どの順序で `prodAssoc` / `prodCongr` / `prodComm` を組むか」の設計が支配項。将来のツール: `(α × β) × γ ≃ α × (β × γ)` のような prod 配置の switch chain を `MeasurableEquiv.prodAssoc` `.trans` の合成で先に組む boilerplate を生成するエージェント (`fun_prop` を後段で打って測度可測性を一括処理)。

### 4.4 `lake env lean` の path 問題 (細かいが反復)

**症状**: `lake env lean` を素で打つと `command not found` (PATH 上に lake が無い)。

**抜け方**: `export PATH="$HOME/.elan/bin:$PATH"` を毎コマンド頭に付ける (3 セッション中ほぼ全ての検証コマンドで付与)。

**教訓**: 前段で `export PATH=...; ` をデフォルト化する shell hook が欲しい。proof-log 単発では小さいが、`lake env lean` を 20 回打つ session ではテンポを崩す。これはセッションメトリクスでは見えないが体感的には目立つ。

## 5. ボトルネックではなかったもの

- **数学のアイデア**: chain rule + DPI + Markov ⇒ condMI=0 の 3 段は教科書 (Cover & Thomas 2.5) 通り、新規アイデアゼロ。
- **converse 主応用**: `mutualInfo_le_of_markov` を `shannon_converse_single_shot` に流し込むだけで `shannon_converse_single_shot_markov_encoder` が 30 行で出る。Phase 4-γ の plumbing 投資が効いた。
- **ENNReal / toReal の境界**: Phase 4-γ で確立したパターン (`mutualInfo` を `ℝ≥0∞` のまま回し、最後に `.toReal`) をそのまま流用、ENNReal 側で詰まる箇所無し。
- **`linarith` 周り**: 最終 calc は `linarith` で閉じる。型推論で詰まる場面なし。
- **コンテキスト長**: 1M context で全 3 セッション余裕。inventory + skeleton + plumbing の全体を同時に保持できた (γ-form pivot の判断に inventory の β-form 採用根拠を逆引きする必要があった)。
- **ツール失敗 (recoverable)**: 1 セッションあたり 0〜1 回 (`elan not found` が 1 回)。失敗が plumbing 進行のボトルネックにはなっていない。

## 6. ツール開発への示唆

| 優先度 | 機能 | このセッションで節約できたであろうコスト |
|---|---|---|
| 高 | **Mathlib 補題の戻り値型に合わせた定義 pivot 提案エージェント** (例: `condMutualInfo` の rnDeriv 形を提示したら「`klDiv_compProd_eq_add` が compProd 形を返すので定義側を compProd 形にすると per-fibre 積分の自作 50〜80 行が不要」と返す) | ~80 行の自作 + pivot 判断時間 |
| 高 | **subagent inventory の構造化テンプレート**: 補題ごとに `signature`, `[type-class prereqs]`, `関数引数の型`, `戻り値の形` を必須欄に。`StandardBorelSpace Ω` のような propagating type class を強調表示 | β-form → γ-form pivot で失った ~30 分 |
| 高 | **3 重以上の `compProd` plumbing の boilerplate 生成**: `MeasurableEquiv.prodAssoc` / `prodCongr` の合成 chain を出力 + `fun_prop` でカバーできない部分を `Measurable.prodMk` の明示形で補う | chain rule plumbing ~80 行 / 約 30〜50 分 |
| 中 | **`fun_prop` の MeasurableEquiv リテラル対応** (Mathlib 側修正) | 4 ヶ所の手書き measurability ~20 行 |
| 中 | **「Mathlib に *無い* と判断する」ための loogle 多面検索エージェント**: 同じ意味の補題を 5 種類のクエリで一括検索し「いずれにも無し」を断定する | `klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η) = ∫⁻ ...` の不在判定で打った 5 クエリ |
| 中 | **skeleton-first / composition-before-plumbing 戦略の自動化**: 主応用の skeleton を sorry で先に通し、依存補題の sorry を後回しにする workflow を自動推進 | このセッションでは手動運用、ただし定着している |
| 低 | **`lake env lean` の PATH 自動補正** | 毎コマンド ~5 文字、累積で軽微 |

優先度の根拠: chain rule plumbing と β/γ-form pivot は本セッションの **行数・時間の支配項**。pivot 判断はとりわけ「事前に inventory で気付けたはずの落とし穴」なので、subagent の出力品質を上げるツール / プロンプトに直接還元できる。

## 7. 補足

### proof 戦略の最終形 (`mutualInfo_chain_rule`)

```
(Z × X) × Y --permZXY_ZYX--> (Z × Y) × X --permZYX_Z_XY--> Z × (X × Y)
   LHS pushforward             chain rule 適用ポイント         condMI 形に整列
```

- `klDiv_map_measurableEquiv` を 2 回適用 (両 perm の前後)
- `klDiv_compProd_eq_add` を `(Z, Y) base + X kernel` で 1 回適用
  - 第 1 項 = `klDiv (μ.map (Zc, Yo)) ((μ.map Zc).prod (μ.map Yo))` = `mutualInfo Zc Yo`
  - 第 2 項 = `klDiv ((μ.map (Zc, Yo)) ⊗ₘ κ) ((μ.map (Zc, Yo)) ⊗ₘ η)` を `factored_map_perm_eq_compProd_prod` で `condMutualInfo` 形に対応

ポイントは **base measure `(μ.map Zc).prod (μ.map Yo)` を第 2 引数の base にすると `mutualInfo Zc Yo` が出る**こと。Markov の γ-form を `(Zc, Yo, Xs)` 順ではなく `(Zc, Xs, Yo)` 順で書いているため、permutation 1 段で chain rule の適用形に揃う。

### 過去の proof-log との関係

- 直前の Phase 4-γ ([proof-log-shannon-converse.md](proof-log-shannon-converse.md)) で encoder を **引数から落とした**判断が、本回の `markov_encoder converse` への拡張パスを開いた。Phase 4-γ で encoder を引数に保ったまま完走しようとしていた場合、Markov 仮定を主定理に直接持ち込む必要があり、本回のような分離した補題 (`mutualInfo_le_of_markov`) を組む余地が無かった。
- Phase 4-γ で書いた `klDiv_map_measurableEquiv` (Phase 4-γ 時 `private`) を本回 public 化。**Phase 別の private/public 境界は将来の拡張で必ず崩れる**ので、新規 helper は最初から public で書くか、ファイル末尾に再エクスポート節を作るべき。
