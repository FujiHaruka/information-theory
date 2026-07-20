# Ch.14 Kolmogorov 複雑性 — plain C 背骨の Mathlib API 台帳

> **Status**: INVENTORY (2026-07-20)。第 1 波 relay(plain 複雑性 C、P1→P5、余力 P6)の着手前台帳。
> **親**: [`kolmogorov-scouting.md`](kolmogorov-scouting.md)(山場マップ + 定義形 §4 + modeling 論点 §5)。
> SoT は着手確定後の `kolmogorov-moonshot-plan.md`(未作成)。
> **scope**: plain C のみ。prefix-free 機械 / 普遍確率 / Ω(第 2 波)は台帳に **入れない**。
> 全 `file:line` は当リポジトリの `.lake/packages/mathlib/` 実体を Read して確認済み。

## 一行サマリ

**万能機械の「意味論」層(`Code`/`eval`/`evaln`/`exists_code`/`smn`/`curry`/停止問題/符号化)は
Mathlib に 100% 完備で、P3 数え上げ・P5 非計算可能性は既存資産で直行できる。しかし P1 不変性・
P2 上界・P4 上界が要求する「翻訳プログラム長 ≤ `l(p) + c_A`(加法定数)」は、scouting §4 の
定義形(`Nat.size ∘ encodeCode` + `eval c 0` 無入力)では原理的に成立しない**(`Code.const` の
Gödel 数が二重指数・`Nat.pair` が二次 = いずれも長さ非加法、両方 def から検証済み)。**この加法定数の
確保が本 relay 唯一の make-or-break で、Mathlib の壁ではなく「定義形の選択」= 長さ加法モデル
(`List Bool` + `List.length` + 専用万能機械 + 固定長機械記述子)への設計転換を要する。** よって
gateway atom(P1)は「naive curry ルートが加法定数を出せないこと」を最初に確認する probe にすべき。

- 意味論層 API 既存率: **100%**(§1–§2, §5, §6 の Mathlib 側は全て在)。
- 自作が要る中核: **(a) 長さ加法な複雑性の定義そのもの**(scouting §4 の pivot)、**(b) 専用万能機械の
  code 構成と `eval` 証明**、**(c) 加法翻訳補題 `l(translate p) ≤ l(p) + c_A`**。
- genuine Mathlib 壁: **prefix-free 機械の塔**(P7–P9、第 2 波)のみ。plain C 背骨には壁は無い。

---

## 主定理の最終形(再掲)— flagship P4

scouting §1 の flagship。**P1–P3・P5 はこの上界/下界の部品**なので P4 を主定理として掲げる。
番号(CT 2nd ed Thm 14.3.1)は原典 PDF 未収蔵につき着手前に要 verbatim 確認(数学的形は標準)。

```lean
-- 条件付き複雑性 C(x | n) を primary に(scouting §5.1)。X^n は Encodable.encode で ℕ へ。
-- ⟨length⟩ は「長さ加法モデル」の長さ関数(pivot 後に確定; naive は Nat.size)。
theorem kolmogorov_entropy_rate         -- @[entry_point] 予定
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (hiid : /- i.i.d. -/) (hpos : ∀ a, 0 < (μ.map (Xs 0)).real {a}) :
    Tendsto (fun n => (1/n) * ∫ ω, (condComplexity (Xs · ω |> encodeBlock n) n : ℝ) ∂μ)
            atTop (𝓝 (entropy μ (Xs 0)))
```

証明戦略(6–10 行の pseudo-Lean):

```
-- 上界 (≤ H + ε):
--   x ∈ typicalSet ⟹ x を A_ε^n 内の index で記述(index bits ≈ n(H+ε))
--   program = ⟨typical-set 復号器 c_dec⟩ ++ ⟨index⟩,  length = c_dec + n(H+ε)   ← P2 条件上界
--   typicalSet_card_le で |A_ε^n| ≤ exp(n(H+ε)) を消費、非typical は確率→0 で吸収
E[C(X^n|n)]/n ≤ (H + ε) + o(1)                                   -- typicalSet_prob_tendsto_one
-- 下界 (≥ H - ε):
--   #{x^n : C(x^n|n) < n(H-ε)} < 2^{n(H-ε)}                       ← P3 数え上げ
--   AEP: 高確率質量は ~exp(nH) 個の列に分散 ⟹ 短い記述は稀
E[C(X^n|n)]/n ≥ (H - ε) - o(1)                                    -- stronglyTypicalSet_card_ge_eventually
-- squeeze:
(1/n) E[C(X^n|n)] → H(X)                                          -- tendsto_of_le_le / squeeze
```

**核心の依存**: 上界は **P2 条件上界の加法定数** に、下界は **P3 数え上げ** に立つ。P2 が加法でなく
定数倍(下記 §walls)だと極限が `2H` 等に化けて P4 が崩れる ⟹ 定義形 pivot は P4 の生死を分ける。

---

## API 在庫テーブル

status 凡例: ✅ 既存 / ⚠️ 既存だが噛み合わせに注意 / ❌ 不在(自作)。
`[...]` 型クラス前提・結論形は **verbatim**(散文化しない)。

### §1. 万能機械コア(`Code` / `eval` / `evaln`)

| 概念 | Mathlib API(verbatim シグネチャ) | file:line | status | Phase での扱い |
|---|---|---|---|---|
| プログラムの inductive | `inductive Code : Type` — `zero/succ/left/right/pair(→→)/comp(→→)/prec(→→)/rfind'(→)` | `Mathlib/Computability/PartrecCode.lean:76` | ✅ | 「プログラム」の母体。`Denumerable` 経由で `ℕ` と同一視 |
| 万能解釈器 | `def eval : Code → ℕ →. ℕ`(`ℕ →. ℕ` = `PFun` = `Part`-値部分関数) | `PartrecCode.lean:464` | ✅ | 実行 = `eval (ofNat Code p) y`。出力は `Part ℕ` |
| 実行の membership | `instance : Membership (ℕ →. ℕ) Code := ⟨fun c f => eval c = f⟩` | `PartrecCode.lean:493` | ✅ | 注: `x ∈ eval c y` の `∈` は **`Part.Mem`**(`(eval c y).Dom ∧ get = x`)。`f ∈ c` の `∈` は上の Code-membership(別物、混同注意) |
| comp の実行 | (named lemma **無し**) 定義展開: `eval (comp cf cg) n = eval cg n >>= eval cf` | `PartrecCode.lean:470` | ⚠️ | `eval_comp` は **存在しない**(loogle Found 0)。合成の実行は `by rw [eval]`/`rfl` で def 展開 |
| prec 基底/再帰の実行 | `eval_prec_zero (cf cg a) : eval (prec cf cg) (Nat.pair a 0) = eval cf a` / `eval_prec_succ` | `PartrecCode.lean:482, 487` | ✅ | 再帰の展開に |
| 有界計算可能 eval | `def evaln : ℕ → Code → ℕ → Option ℕ` | `PartrecCode.lean:568` | ✅ | 数え上げ/停止判定の要(`Option`, 計算可能) |
| 有界性 | `theorem evaln_bound : ∀ {k c n x}, x ∈ evaln k c n → n < k` | `PartrecCode.lean:604` | ✅ | |
| 単調性 | `theorem evaln_mono : ∀ {k₁ k₂ c n x}, k₁ ≤ k₂ → x ∈ evaln k₁ c n → x ∈ evaln k₂ c n` | `PartrecCode.lean:612` | ✅ | |
| 健全 | `theorem evaln_sound : ∀ {k c n x}, x ∈ evaln k c n → x ∈ eval c n` | `PartrecCode.lean:651` | ✅ | |
| 完全 | `theorem evaln_complete {c n x} : x ∈ eval c n ↔ ∃ k, x ∈ evaln k c n` | `PartrecCode.lean:690` | ✅ | `eval` を `evaln` の可算和に落とす |
| eval = rfindOpt | `theorem eval_eq_rfindOpt (c n) : eval c n = Nat.rfindOpt fun k => evaln k c n` | `PartrecCode.lean:989` | ✅ | |
| eval の partrec 性 | `theorem eval_part : Partrec₂ eval` | `PartrecCode.lean:994` | ✅ | 「C は計算可能でない」の対比項(P5) |

**gap(§1)**: なし。意味論層は完備。ただし `eval_comp` は無く合成は def 展開で扱う(P1 で頻用)。

### §2. 不変性 P1 に効く資産(万能性 + 合成 + 符号化)

| 概念 | Mathlib API(verbatim シグネチャ) | file:line | status | Phase での扱い |
|---|---|---|---|---|
| 万能性(部分再帰 ⟺ code) | `theorem exists_code {f : ℕ →. ℕ} : Nat.Partrec f ↔ ∃ c : Code, eval c = f` | `PartrecCode.lean:533` | ✅ | 「別機械 A = `ℕ →. ℕ`」を `eval c_A` に落とす **P1 の礎石** |
| S-m-n | `theorem smn : ∃ f : Code → ℕ → Code, Computable₂ f ∧ ∀ c n x, eval (f c n) x = eval c (Nat.pair n x)` | `PartrecCode.lean:527` | ✅ | 第一引数固定。`f = curry` |
| curry(部分適用) | `def curry (c : Code) (n : ℕ) : Code := comp c (pair (Code.const n) Code.id)` | `PartrecCode.lean:113` | ⚠️ | 意味は合うが **長さが破綻**(下記 walls): `const n` を code に埋め込む |
| curry の実行 | `theorem eval_curry (c n x) : eval (curry c n) x = eval c (Nat.pair n x)` | `PartrecCode.lean:505` | ✅ | |
| 定数関数 code | `protected def Code.const : ℕ → Code`(`0↦zero`, `n+1↦comp succ (const n)`) | `PartrecCode.lean:96` | ⚠️ | **unary 塔**。`encodeCode (const n)` が二重指数(P2/P1 の長さ爆発源) |
| 定数の実行 | `theorem eval_const : ∀ n m, eval (Code.const n) m = Part.some n` | `PartrecCode.lean:497` | ✅ | |
| 恒等 code | `protected def Code.id : Code := pair left right` / `theorem eval_id (n) : eval Code.id n = Part.some n` | `PartrecCode.lean:108, 502` | ✅ | 「入力をそのまま返す」= 長さ加法モデルの echo 部品候補 |
| 合成が primrec | `theorem primrec₂_comp : Primrec₂ comp` / `primrec₂_curry : Primrec₂ curry` / `primrec_const : Primrec Code.const` | `PartrecCode.lean:226, 513, 507` | ✅ | 翻訳器が計算可能であることの担保 |
| Gödel 符号化 | `def encodeCode : Code → ℕ` / `def ofNatCode : ℕ → Code` | `PartrecCode.lean:117, 130` | ✅ | プログラム = ℕ の実体 |
| Code ≃ ℕ | `instance instDenumerable : Denumerable Code` / `encodeCode_eq : encode = encodeCode` / `ofNatCode_eq : ofNat Code = ofNatCode` | `PartrecCode.lean:176, 182, 185` | ✅ | `encode`/`ofNat Code` が使える。`Encodable`/`Primcodable` も自動 |
| Gödel 数の単調性 | `encode_lt_pair` / `encode_lt_comp` / `encode_lt_prec (cf cg) : encode cf < encode (…) ∧ encode cg < encode (…)` / `encode_lt_rfind'` | `PartrecCode.lean:188, 196, 201, 206` | ✅ | 「部分 code の Gödel 数 < 全体」。長さ下界に使えるが **加法上界は与えない** |
| 再帰定理 | `theorem fixed_point {f : Code → Code} (hf : Computable f) : ∃ c, eval (f c) = eval c` / `fixed_point₂ {f : Code → ℕ →. ℕ} (hf : Partrec₂ f) : ∃ c, eval c = f c` | `PartrecCode.lean:1004, 1022` | ✅ | P5(rice 経由)で間接使用 |

**gap(§2)**: **加法翻訳補題 `l(translate p) ≤ l(p) + c_A` は Mathlib に無く、しかも `curry`/`const` 経由では
偽**(walls 参照)。P1 の核はこの補題であり、Mathlib 資産だけでは組めない = 自作(かつ定義形 pivot 前提)。

### §3. 長さ `Nat.size` + `Nat.sInf` 到達性(定義の well-defined 性)

| 概念 | Mathlib API(verbatim シグネチャ) | file:line | status | Phase での扱い |
|---|---|---|---|---|
| ビット長 | `def Nat.size : ℕ → ℕ` | `Mathlib/Data/Nat/Size.lean`(§ 全体) | ⚠️ | naive 定義の長さ。**加法性が無い**ため pivot 候補(§walls) |
| size ↔ 2^n | `theorem Nat.size_le {m n : ℕ} : size m ≤ n ↔ m < 2 ^ n` | `Size.lean:79` | ✅ | 数え上げ P3 の要(size 束縛 → range 束縛) |
| size 逆向き | `theorem Nat.lt_size {m n : ℕ} : m < size n ↔ 2 ^ m ≤ n` | `Size.lean:90` | ✅ | |
| size 単調 | `theorem Nat.size_le_size {m n : ℕ} (h : m ≤ n) : size m ≤ size n` | `Size.lean:101` | ✅ | |
| size 自己束縛 | `theorem Nat.lt_size_self (n : ℕ) : n < 2 ^ size n` | `Size.lean:72` | ✅ | |
| size=0 | `theorem Nat.size_eq_zero {n : ℕ} : size n = 0 ↔ n = 0` | `Size.lean:95` | ✅ | |
| sInf 到達(非空⟹最小達成) | `theorem Nat.sInf_mem {s : Set ℕ} (h : s.Nonempty) : sInf s ∈ s` | `Mathlib/Order/Lattice/Nat.lean:79` | ✅ | **C(x) が min として実在**。`eval_const`/`eval_id` で非空を供給 ⟹ `sorry` を def 本体に置かない |
| sInf 上界 | `protected theorem Nat.sInf_le {s : Set ℕ} {m : ℕ} (hm : m ∈ s) : sInf s ≤ m` | `Order/Lattice/Nat.lean:90` | ✅ | 上界系(P1/P2)の道具。`protected` |
| sInf 下界(否定形) | `theorem Nat.notMem_of_lt_sInf {s : Set ℕ} {m : ℕ} (hm : m < sInf s) : m ∉ s` | `Order/Lattice/Nat.lean:84` | ✅ | 下界系(P3/P4 下界)の道具 |
| sInf 下界(∀形) | `le_csInf (hs : s.Nonempty) (h : ∀ b ∈ s, a ≤ b) : a ≤ sInf s`(`@[to_dual]` 生成) | `Mathlib/Order/ConditionallyCompleteLattice/Basic.lean:201` | ✅ | ℕ は `ConditionallyCompleteLinearOrderBot`。`k ≤ C(x)` を組む |
| Nat.find の計算可能性 | `lemma Computable.find {P : α → ℕ → Prop} [DecidableRel P] (hP_comp : ComputablePred (fun p => P p.1 p.2)) (hP_ex : ∀ x, ∃ n, P x n) : Computable (fun x => Nat.find (hP_ex x))` | `Mathlib/Computability/RE.lean:177` | ✅ | 「C が **計算可能でない**」を言うとき、計算可能側の対比に(P5) |

**gap(§3)**: なし(well-defined 性は完備)。**ただし `Nat.size` を長さに採ると §2 の加法性が壊れる**(§walls)。

### §4. 数え上げ P3(program 長 < k のカード ≤ 2^k)

| 概念 | Mathlib API(verbatim シグネチャ) | file:line | status | Phase での扱い |
|---|---|---|---|---|
| size束縛→range束縛 | `Nat.size_le : size m ≤ n ↔ m < 2 ^ n` | `Size.lean:79` | ✅ | `{p | size p < k} ⊆ {p | p < 2^k} = range (2^k)` |
| 部分集合⟹カード | `theorem Finset.card_le_card : s ⊆ t → #s ≤ #t` | `Mathlib/Data/Finset/Card.lean:66` | ✅ | |
| range のカード | `theorem Finset.card_range (n : ℕ) : #(range n) = n` | `Card.lean:174` | ✅ | `#(range (2^k)) = 2^k` |
| 単射⟹カード | `theorem Finset.card_le_card_of_injOn (hf : ∀ a ∈ s, f a ∈ t) (f_inj : Set.InjOn f s) : #s ≤ #t` | `Mathlib/Data/Finset/Card.lean`(loogle確認) | ✅ | `x ↦ (最小プログラム)` を `{p | size p < k}` へ単射 ⟹ `#{x|C(x)<k} ≤ #{p|size p<k}` |
| n < 2^n | `theorem Nat.lt_two_pow_self : n < 2 ^ n` | `Init.Data.Nat.Lemmas`(loogle確認) | ✅ | 補助(strict `< 2^k` の締め) |

**gap(§4)**: なし。P3 は naive `Nat.size` 定義でも **既存資産だけで閉じる**(iconic・小)。size 版だと厳密には
`#{x | C(x) < k} ≤ 2^{k-1} < 2^k`(`size p < k ↔ p < 2^{k-1}`)なので strict 版もそのまま出る。

### §5. 非計算可能性 P5(halting / rice)

| 概念 | Mathlib API(verbatim シグネチャ) | file:line | status | Phase での扱い |
|---|---|---|---|---|
| 計算可能述語 | `def ComputablePred {α} [Primcodable α] (p : α → Prop) := ∃ (_ : DecidablePred p), Computable fun a => decide (p a)` | `Mathlib/Computability/RE.lean:129` | ✅ | 「C は計算可能でない」の主語 |
| 帰納的可算述語 | `def REPred {α} [Primcodable α] (p : α → Prop) := Partrec fun a => Part.assert (p a) fun _ => Part.some ()` | `RE.lean:157` | ✅ | 上限・下限セット可算性 |
| 停止問題(非計算) | `theorem ComputablePred.halting_problem (n) : ¬ComputablePred fun c => (eval c n).Dom` | `Mathlib/Computability/Halting.lean:65` | ✅ | **P5 の背骨**。Berry/停止経由の還元先 |
| 停止問題(r.e.) | `theorem ComputablePred.halting_problem_re (n) : REPred fun c => (eval c n).Dom` | `Halting.lean:61` | ✅ | |
| 停止補(非 r.e.) | `theorem ComputablePred.halting_problem_not_re (n) : ¬REPred fun c => ¬(eval c n).Dom` | `Halting.lean:68` | ✅ | |
| Rice(関数版) | `theorem ComputablePred.rice (C : Set (ℕ →. ℕ)) (h : ComputablePred fun c => eval c ∈ C) {f g} (hf : Nat.Partrec f) (hg : Nat.Partrec g) (fC : f ∈ C) : g ∈ C` | `Halting.lean:33` | ✅ | 意味的性質は非計算 |
| Rice(code集合版) | `theorem ComputablePred.rice₂ (C : Set Code) (H : ∀ cf cg, eval cf = eval cg → (cf ∈ C ↔ cg ∈ C)) : (ComputablePred fun c => c ∈ C) ↔ C = ∅ ∨ C = Set.univ` | `Halting.lean:43` | ✅ | |

**gap(§5)**: なし。ただし「C 非計算可能」の還元(Berry のパラドクス、または「`C(x) ≥ k` の最小 x を
計算する ⟹ 矛盾」)そのものは **自作の還元補題**が要る(halting/rice は既製の弾)。P1/P3 のみ依存で並走可。

### §6. 符号化 / 文字列 ↔ ℕ(P4 の `X^n` を ℕ へ)+ 接続する project 内資産

| 概念 | Mathlib / project API(verbatim) | file:line | status | Phase での扱い |
|---|---|---|---|---|
| 符号化構造 | `structure Encoding (α)` / `structure FinEncoding (α)` | `Mathlib/Computability/Encoding.lean:41, 58` | ✅ | 長さ加法モデルの土台候補 |
| ℕ の 2 進符号 | `def encodeNat : ℕ → List Bool` / `def decodeNat : List Bool → Nat` / `@[simp] decode_encodeNat` | `Encoding.lean:105, 118, 139` | ✅ | **pivot 先の長さ = `List.length (encodeNat n)`**(加法的) |
| ℕ の FinEncoding | `def finEncodingNatBool : FinEncoding ℕ` | `Encoding.lean:151` | ✅ | |
| `X^n` を ℕ へ | `instance Primcodable.finArrow : Primcodable (Fin n → α)`(loogle確認) ⟹ `Encodable.encode : (Fin n → α) → ℕ` | `Mathlib/Computability/Primrec/List.lean` | ✅ | `X^n = (Fin n → α)` を単射に ℕ へ。P4 の入力符号化 |
| **project: entropy** | `noncomputable def entropy (μ : Measure Ω) (Xs : Ω → X) : ℝ := ∑ x : X, Real.negMulLog ((μ.map Xs).real {x})` | `InformationTheory/Shannon/Bridge.lean:40` | ✅ | P4 の右辺 H(X) |
| **project: typicalSet** | `noncomputable def typicalSet (μ) (Xs : ℕ → Ω → α) (n : ℕ) (ε : ℝ) : Set (Fin n → α)` | `InformationTheory/Shannon/AEP/Basic/Core.lean:214` | ✅ | P4 上界の符号化対象 |
| **project: 上界カード** | `theorem typicalSet_card_le (μ) [IsProbabilityMeasure μ] (Xs) (hXs : ∀ i, Measurable (Xs i)) (hpos : ∀ x, 0 < (μ.map (Xs 0)).real {x}) (n) {ε} (_hε : 0 < ε) : ((typicalSet μ Xs n ε).toFinite.toFinset.card : ℝ) ≤ Real.exp ((n:ℝ) * (entropy μ (Xs 0) + ε))` | `AEP/Basic/Core.lean:247` | ✅ | **P4 上界の index bits ≈ n(H+ε)** を供給 |
| **project: 質量→1** | `theorem typicalSet_prob_tendsto_one (μ) [IsProbabilityMeasure μ] (Xs) (hXs) (hindep : Pairwise …) (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ) {ε} (hε : 0 < ε) : Tendsto (fun n => μ {ω | jointRV Xs n ω ∈ typicalSet μ Xs n ε}) atTop (𝓝 1)` | `AEP/Basic/Core.lean:365` | ✅ | 非typical の確率吸収 |
| **project: stronglyTypicalSet** | `noncomputable def stronglyTypicalSet (μ) (Xs : ℕ → Ω → α) (n : ℕ) (ε : ℝ) : Set (Fin n → α)` | `InformationTheory/Shannon/StrongTypicality.lean:58` | ✅ | P4 下界(AEP 側) |
| **project: 下界カード** | `theorem stronglyTypicalSet_card_ge_eventually (μ) [IsProbabilityMeasure μ] (Xs) (hXs) (hindep_full : iIndepFun … μ) (hindep_pair : Pairwise …) (hident) (hpos) {ε δ η} (hε hδ hη : 0 < …) : ∃ N, ∀ n, N ≤ n → (1-η) * Real.exp ((n:ℝ)*(entropy μ (Xs 0) - ε*logSumAbs μ Xs - δ)) ≤ (…card : ℝ)` | `StrongTypicality.lean:446` | ✅ | **P4 下界の「~exp(nH) 個に分散」** を供給 |

**gap(§6)**: 符号化・AEP 資産は完備。**接続の橋(「複雑性の期待値 → typical set カードの log」)は
自作**(P4 の本体)。project 側は `Real.exp (n·(H±ε))` 形なので、複雑性側も `Real.log`/`Nat.size` を
exp/2^ 基底に揃える plumbing(`Real.log 2` の掛け合わせ)が要る。

---

## Key-preconditions box(事故が起きやすい前提)

- **`exists_code` の向き**: `Nat.Partrec f ↔ ∃ c, eval c = f`。**別機械 A を `ℕ →. ℕ` として与え、
  `Nat.Partrec` を示してから** `eval c_A` に落とす。A を最初から `Code` で与えると P1 の一般性が落ちる。
- **`smn`/`eval_curry` の入力規約**: `eval (curry c n) x = eval c (Nat.pair n x)` = **第一座標 `n` を固定**。
  条件版 `C(x|y)` は `eval (ofNat Code p) y`(y を直接入力)で定義し、curry は「無条件化(y を code に畳む)」に
  使う ⟹ **y を pair の第一座標に置く規約で統一**(`eval c (Nat.pair y ·)`)。混同すると P4 の `C(X^n|n)` が壊れる。
- **`typicalSet_card_le` の `hpos`(full-support)**: `∀ x, 0 < (μ.map (Xs 0)).real {x}` が **必須**
  (`Real.log 0 = 0` 規約により out-of-support 点で下界が崩れるため; docstring 明記)。P4 上界がこの hyp を継承する。
- **`stronglyTypicalSet_card_ge_eventually` の独立性 3 点**: `iIndepFun` + `Pairwise ⟂ᵢ` + `∀ i, IdentDistrib`
  を **全て** 要求(i.i.d. をこの 3 つに分解して渡す)。1 つ欠くと下界が出ない。
- **`Part.Mem` と `Code.Membership` の二重 `∈`**: `x ∈ eval c y`(Part 値、= 実行結果)と `f ∈ c`
  (`eval c = f`、Code の membership instance)は別。scouting §4 の `x ∈ eval (ofNat Code p) 0` は前者。
- **`Nat.sInf_le` は `protected`**: `Nat.sInf_le` とフル修飾で呼ぶ(`sInf_le` 単体は別物に解決されうる)。

---

## 自作が必要な要素(優先度順)

1. **【最優先・make-or-break】長さ加法な複雑性の定義 + 専用万能機械**
   scouting §4 の `C(x) := sInf {Nat.size p | x ∈ eval (ofNat Code p) 0}` は **P1/P2/P4 上界で破綻**(下記 walls)。
   推奨: **プログラム = `List Bool`(または ℕ を `encodeNat` で bit 列視)、長さ = `List.length`、
   固定万能機械 `U : List Bool →. ℕ`(`unary(index) ++ 0 ++ data` を parse して `eval (ofNat Code index) data` を回す)**。
   これで P2 上界(echo で `l(x)+O(1)`)・P1 不変性(固定 unary 記述子で `l(q)+c_A`)が **prefix-free 塔なしで** 加法になる。
   工数感: **専用 `U` の code 構成 + `eval U` の証明 = 100–300 行**(Mathlib に既製の「入力を parse する万能 code」は無い)。
   落とし穴: `U` を `Nat.Partrec.Code` として具体構成し `eval` を verbatim 確定するのは重い(`prec`/`rfind'` の手組み)。
   → **gateway atom(task #5)はまずこの定義形で P1 を 1 本通す probe にすべき**。naive curry 版は加法定数を出さずに詰む。

2. **加法翻訳補題 `l(translate_A p) ≤ l(p) + c_A`**(P1 の核)
   上の U の下で「A の program q を U-program `unary(i_A) ++ 0 ++ q` に写す写像の長さ = `c_A + l(q)`」。
   `List.length_append` + 固定 `unary(i_A)` 長で数行だが、**U の parse 正当性 `eval U (sd(i_A)++q) = eval c_A q` に依存**。
   工数感: U が組めれば **20–40 行**。組めなければ P1 全体が止まる(依存の連鎖点)。

3. **複雑性 ↔ typical-set カードの橋**(P4 本体、~100–200 行)
   `typicalSet_card_le`(exp 形)/`stronglyTypicalSet_card_ge_eventually` と、複雑性の `Nat.size`/`List.length`(2進)を
   `Real.log`/`2^·` 基底で接続。上界 = 条件上界 + index 符号化、下界 = 数え上げ + AEP。`Real.log 2` の plumbing に注意。

4. **P5 の還元補題**(~40–80 行)
   「C 計算可能 ⟹ 各 k で `C(x) ≥ k` の最小 x を計算 ⟹ その x の記述が短くなり矛盾(Berry)」または停止還元。
   halting/rice は既製、還元の骨格のみ自作。P1/P3 依存で並走可能。

5. **P3 数え上げの Finset 化**(~30–50 行、低リスク)
   `{x | C(x) < k}` の有限性 + `x ↦ 最小 program` の単射 + `card_le_card_of_injOn` + `size_le`/`card_range`。
   **naive `Nat.size` 定義のままでも閉じる**唯一の主要 leg(定義 pivot の影響を受けない)。

---

## Mathlib 壁の列挙(`@residual(wall:…)` 候補)

**plain C 背骨に genuine な Mathlib 壁は無い。** 「壁」に見える 2 点はいずれも壁ではない:

- **(非壁・定義選択)加法翻訳 `l(comp)`/`eval_comp`**: loogle
  `Nat.Partrec.Code.eval (Nat.Partrec.Code.comp _ _)` → **`Found 0 declarations`**。合成の実行に named lemma は無いが
  def 展開(`PartrecCode.lean:470`)で足りる。**加法定数化は Mathlib の不在ではなく「`Nat.size`/`Nat.pair`/`const` が
  非加法」という定義形の選択問題**(下記の検証)。CLAUDE.md「Misuse of Mathlib wall」に照らし **壁と呼ばない**。
  - 検証(refutation 済み、def から): `encodeCode(const (n+1)) = 2*(2*Nat.pair 1 (encodeCode(const n))+1)+4`、
    `Nat.pair 1 m = m²+1`(`m≥2`)⟹ `e_{n+1} ≈ 4·e_n²` ⟹ `encodeCode(const n)` は **二重指数** ⟹
    `Nat.size(const n) ≈ 2^n`。よって「x を出力する program」を `const x` で組むと長さ `≈ 2^x ≫ size x`、**P2 上界が偽**。
    `Nat.pair a b = if a<b then b*b+a else a*a+a+b`(`Pairing.lean:38`、二次)⟹ `Nat.size(pair tag data) ≈ 2·size data`、
    **タグ付けでも定数倍**。両者とも「長さ加法」を満たさず、加法定数は原理的に出ない(pivot が唯一の出口)。
  - `Nat.size(Nat.pair _ _)` の束縛補題: loogle `Nat.size (Nat.pair _ _)` → **`Found 0 declarations`**(自作しても加法にはならない)。

- **(真の壁・第 2 波、scope 外)prefix-free 機械の塔**: 普遍確率 `P_U`・符号化定理・Ω(P7–P9)。
  scouting §0/§6 の通り `@residual(wall:prefix-free-tower)` に隔離。**本 relay(P1–P6)は一切触れない**ので台帳外。
  共有 sorry-lemma 化の要否は第 2 波で判断(現段階では **推奨せず**、plain C 背骨に prefix 依存を持ち込まないため)。

**結論**: plain C 背骨の未達は全て「自作(定義形 pivot + 専用 U 構成)」であって「Mathlib 壁」ではない。
`@residual` を打つ先があるとすれば **P4 本体の途中 sorry**(class = `plan:kolmogorov-p4`)のみで、`wall:` は付かない。

---

## 撤退ラインへの距離

親計画は未作成(`kolmogorov-moonshot-plan.md` 起票が task #4)。scouting §6 のスコープ提案に対して:

- **触れる撤退ライン**: scouting §6「Out(第 2 波)」= prefix 塔。**本 relay は触れない**ので **発動しない**。
- **新規に立てるべき撤退ライン(定義形 pivot に起因)**:
  - **gateway atom P1 が「長さ加法モデル(専用 U)」で 1 セッション内に加法定数 `l(q)+c_A` を出せない**場合
    → **縮退案**: P1 を「**最適性(optimality)形**」に退避 = 「ある固定 U に対し C_U を定義し、well-defined 性
    (`sInf_mem`)+ P3 数え上げ + P5 非計算可能性のみを headline とし、加法不変性 `C_U ≤ C_A + c_A` は
    `sorry` + `@residual(plan:kolmogorov-invariance-additive)` で退避」。P4(flagship)はこの sorry に依存するため
    **P4 も同時に park**(下界の数え上げ部分だけ独立に出す部分勝利は可)。
    - 退避出口は **sorry + `@residual`**(hypothesis bundling 禁止)。`IsUniversalHypothesis` 等に不変性を畳んで
      P4 を「通ったことにする」のは load-bearing bundling = 禁止(CLAUDE.md Verification honesty)。
  - **専用 U の code 構成が 300 行を超えて発散**する場合 → P1/P2/P4 を丸ごと park し、**P3 + P5 の 2 headline
    (naive `Nat.size` 定義で閉じる)を第 1 波の最小成果**として先に確定。P4 flagship は第 1.5 波へ。

**判定(現時点)**: 撤退ラインは未発動。ただし **P1 gateway probe の結果次第で上記 1 本目が発動する公算が中程度**
(naive 定義だと確実に発動、長さ加法モデルを最初から採れば回避可能)。

---

## 着手のための skeleton

`InformationTheory/Kolmogorov/Complexity.lean`(仮)の出だし。**長さ加法モデルを既定**とし、
naive `Nat.size` 版は P3/P5 専用に別途置く想定。全 `sorry` は type-check-done を満たす退避出口。

```lean
import Mathlib.Computability.PartrecCode      -- Code, eval, exists_code, smn, curry, encodeCode
import Mathlib.Computability.Halting          -- halting_problem, rice
import Mathlib.Computability.Encoding         -- encodeNat : ℕ → List Bool（長さ加法モデルの長さ）
import Mathlib.Data.Nat.Size                  -- Nat.size_le（P3 数え上げ）
import Mathlib.Order.Lattice.Nat              -- Nat.sInf_mem / sInf_le（well-defined 性）
-- import InformationTheory.Shannon.AEP.Basic   -- P4 で typicalSet_card_le を消費（着手時に配線）

namespace InformationTheory.Kolmogorov

open Nat.Partrec Nat.Partrec.Code Computability

/-- 固定万能機械: プログラム `p : ℕ`（`unary(index) ++ 0 ++ data` を bit 列視）を条件 `y` の下で走らせる。
    長さ加法（P1/P2 の加法定数）を担保する専用構成。**核心の自作物**（skeleton では sorry）。 -/
noncomputable def universalEval (p y : ℕ) : Part ℕ := by sorry
  -- @residual(plan:kolmogorov-universal-machine)  -- 専用 U の code 構成 + eval 証明（100–300 行）

/-- プログラム長（長さ加法モデル）: `List.length (encodeNat p)`。naive 版は `Nat.size p`。 -/
def progLen (p : ℕ) : ℕ := (encodeNat p).length

/-- 条件付き Kolmogorov 複雑性 `C(x | y)`。`universalEval` の実行結果が `x` になる最短プログラム長。
    `Nat.sInf` は非空（`universalEval` の echo プログラムで供給）なら最小値に到達する。 -/
noncomputable def condComplexity (x y : ℕ) : ℕ :=
  sInf { l | ∃ p, progLen p = l ∧ x ∈ universalEval p y }

/-- 無条件複雑性 `C(x) := C(x | 0)`。 -/
noncomputable def complexity (x : ℕ) : ℕ := condComplexity x 0

/-- P1 不変性: 任意の別機械 `A : ℕ →. ℕ`（部分再帰）に対し `C(x) ≤ C_A(x) + c_A`。**gateway atom**。 -/
theorem invariance (A : ℕ → ℕ → Part ℕ) (hA : Partrec₂ A) :
    ∃ c : ℕ, ∀ x, complexity x ≤ /- C_A x -/ 0 + c := by sorry
  -- @residual(plan:kolmogorov-invariance-additive)  -- exists_code + 加法翻訳補題（U に依存）

/-- P3 数え上げ: `#{x | C(x) < k} < 2^k`。naive `Nat.size` 定義でも既存資産で閉じる（低リスク）。 -/
theorem incompressible_count (k : ℕ) :
    Set.Finite {x | complexity x < k} := by sorry
  -- @residual(plan:kolmogorov-counting)  -- size_le + card_le_card_of_injOn

/-- P5 非計算可能性: `complexity` は計算可能関数でない（halting / Berry 経由）。 -/
theorem complexity_not_computable : ¬ Computable complexity := by sorry
  -- @residual(plan:kolmogorov-noncomputable)  -- halting_problem への還元

end InformationTheory.Kolmogorov
```

最初に割るのは `universalEval`(自作物 1)と `invariance`(gateway)。両者が通れば P2/P4 の加法定数が確定する。
P3/P5 は `universalEval` の詳細に依存しない(実行の存在性/非計算性のみ)ので **並走レーン**として先行取得可能。
