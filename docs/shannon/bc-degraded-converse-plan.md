# Shannon: degraded BC converse single-letterization サブ計画

> **Parent**: [`broadcast-channel-moonshot-plan.md`](broadcast-channel-moonshot-plan.md) — 凍結退避線 **L-BC2「Fano + chain rule」を再開**

degraded broadcast channel の converse single-letterization (Cover–Thomas Thm 15.6.2) を
**genuine closure** する。crux は Csiszár sum 恒等式。既に
`InformationTheory/Shannon/BroadcastChannel/ConverseGateway.lean` に置かれた residual slug
`@residual(plan:bc-degraded-converse-plan)` (`csiszar_sum_identity:111`) を有効化する。

## 進捗

- [ ] Phase 0 — Mathlib/in-project API 在庫 再確認 📋
- [ ] Phase 1 — 条件付き n-var MI chain rule (prefix) 📋
- [ ] Phase 2 — Csiszár sum 恒等式 (suffix expansion via reflection) 📋
- [ ] Phase 3 — bound (b) single-letterization 📋
- [ ] Phase 4 — `bc_converse` headline + `InBCCapacityRegion` 領域述語 📋
- [ ] Phase 5 — 独立監査 + root 登録 + roadmap Ch.15 同期 📋

## ゴール / Approach

**ゴール**: gateway の crux `csiszar_sum_identity` (現 sorry) を genuine 化し、bound (a)
(`bc_converse_bound_a`、genuine 済) と組んで degraded BC converse の single-letter 領域
membership headline `bc_converse` を proof done で publish する。

### Approach 全体戦略

標準 El Gamal–Kim 証明: Csiszár sum の両辺を共通の三角二重和
`∑_{(i,j): i<j} I(Aᵢ; Bⱼ | A^{<i}, B^{>j})` に telescoping して一致を示す。

- **LHS** `∑ᵢ I(A^{<i}; Bᵢ | B^{>i})`: 各 i で **prefix** `A^{<i}` を、背景 conditioner
  `B^{>i}` (= i 依存 suffix) のもとで chain rule 展開 →
  `∑_{k<i} I(Aₖ; Bᵢ | A^{<k}, B^{>i})`。これは **条件付き (背景 conditioner 付き) n-var
  chain rule** (Phase 1) を直接適用。
- **RHS** `∑ᵢ I(B^{>i}; Aᵢ | A^{<i})`: 各 i で **suffix** `B^{>i}` を背景 `A^{<i}` のもとで
  chain rule 展開 → `∑_{j>i} I(Bⱼ; Aᵢ | A^{<i}, B^{>j})`。suffix 展開は in-project 前例
  ゼロ (既存 chain rule は全て prefix `Y^{<i}`)。
- 両二重和を `{i<j}` の共通形に reindex し、各項を MI 対称性
  (`condMutualInfo_comm`) で一致させる。

**支配コスト = RHS の suffix 展開**。gateway probe verdict の self-build 案 (suffix 機構
一から ~100-150 行) に対し、本 plan は **suffix-via-reflection** を主経路に採る:
列を `Fin.revPerm` (= `Fin.rev` の `Equiv.Perm`) で反転し、suffix conditioner を prefix に
変換して Phase 1 の prefix chain rule を再利用する。

### reflection 検証結果 (本起票パスで loogle + grep + Mathlib source 確認)

reflection に要る reindex 部品は **全て在庫あり**、ただし suffix 展開を「無料」にはしない
(下記 R1 が新規 build 要):

| 部品 | 在否 | file:line | 用途 |
|---|---|---|---|
| `Finset.sum_range_reflect` | ✅ | `Mathlib/Algebra/BigOperators/Intervals.lean:163` (`∑ j∈range n, f(n-1-j) = ∑ j∈range n, f j`) | ℕ-range 反転和 |
| `Fin.revPerm : Equiv.Perm (Fin n)` | ✅ | `Mathlib/Data/Fin/Rev.lean:35` | `Fin n` univ-sum 反転 (`Equiv.sum_comp`/`Fintype.sum_equiv` 経由) |
| `Fin.sum_univ_reflect` | ❌ 不在 | — | (上記 `Fin.revPerm`+`Equiv.sum_comp` で代替) |
| `MeasurableEquiv.piCongrLeft` | ✅ | `Mathlib/MeasureTheory/MeasurableSpace/Embedding.lean:490`、in-project 使用例 `LoomisWhitney.lean:269` | conditioner index 型 `{j//i<j} → γ ≃ᵐ Fin _ → γ` の relabel |
| `condMutualInfo_map_left_measurableEquiv` (data 引数 relabel) | ✅ | `CondMutualInfo.lean:400` | |
| `condMutualInfo_map_middle_measurableEquiv` (other 引数 relabel) | ✅ | `CondMutualInfo.lean:462` | |
| **`condMutualInfo` の conditioner 引数 relabel invariance** | ❌ **不在** | — (left/middle のみ) | **R1: 新規 build 要** |

**reflection 主経路の判定 = 有効 (主経路採用)**。ただし suffix 展開を無料化せず、コストを
次の 2 sub-task に移す:
- **R1**: 新規 invariance lemma `condMutualInfo_map_cond_measurableEquiv`
  (`I(X;Y|e∘Z) = I(X;Y|Z)`)。`_map_left` と同型の証明 (conditioner は condMutualInfo の
  3 entropy 項に現れるが、`condMutualInfo_comm` + 既存 left/middle と同じ MeasurableEquiv
  invariance パターン)。真の Mathlib 壁でなく既存資産への配線。**~30-50 行**。
  honesty: invariance lemma で load-bearing でない (regularity)。
- **R2**: 反転 equiv `{j : Fin n // i.val < j.val} ≃ Fin (n-1-i.val)` を `Fin.revPerm` から
  構成し `piCongrLeft` に合成。off-by-one (`n-1-i`) bookkeeping が支配的な fiddliness。
  **~50-90 行**。

**net suffix 展開コスト ~80-140 行** (vs self-build ~100-150 行) — 中程度の節約 +
chain rule 証明ロジックの重複回避。**独立支配コストは Phase 1 (条件付き n-var chain
rule)、reflection と無関係に必要**。

**代替経路 (R2 が off-by-one bookkeeping で詰まったとき)**: suffix chain rule を直接自作
(suffix induction、reflection を経由しない)。Phase 2 retreat 参照。

## Phase 0 — Mathlib/in-project API 在庫 再確認 📋

proof-log: no。既存 `broadcast-channel-mathlib-inventory.md` を base に、本 plan 固有の
3 点のみ verbatim 再確認 (mathlib-inventory agent に委任可):

- [ ] R1 invariance の証明テンプレ: `condMutualInfo_map_left_measurableEquiv`
  (`CondMutualInfo.lean:400`) の body を読み、conditioner 版に転用できる構造か確認。
- [ ] R2 reflection equiv: `Fin.revPerm` の `apply`/`symm_apply` + `Fin.rev_rev`、
  subtype `{j // i<j}` ↔ `Fin (n-1-i)` の order-iso を組む補題候補 (`Fin.revPerm` が
  `i ↦ n-1-i`、`i<j ↔ rev j < rev i` の antitone 性) を grep。
- [ ] Phase 1 テンプレ: `mutualInfo_chain_rule_fin` (`MIChainRule.lean:83`、prefix・無条件・
  `induction n` + `Fin.sum_univ_castSucc`) と `condMutualInfo_chain_rule_X_2var`
  (`ConverseMemorylessChainRule.lean:164`、2-var・背景 `Wc` 付き) の 2 つを照合し、
  induction step で背景 conditioner を carry する形を確定。

## Phase 1 — 条件付き n-var MI chain rule (prefix) 📋

proof-log: yes (新規 infra、後続 family で再利用見込み)。

目標 lemma (新規、`ConverseGateway.lean` または新 file に):
```
I(A^{<m}; C | Z) = ∑_{k<m} I(Aₖ; C | A^{<k}, Z)
```
(`A : Fin n → Ω → γ`, prefix `A^{<m} = fun j:Fin m ↦ A_j`, 背景 conditioner `Z`)

- [ ] template = `mutualInfo_chain_rule_fin` の `induction n` 証明を base に、全 step で
  背景 conditioner `Z` を carry。base case (m=0) は空和 + Unique pi、step は
  `condMutualInfo_chain_rule_X_2var` (背景 `(Z, A^{<m})`) で last を剥がし IH。
- [ ] finiteness threading: `condMutualInfo_chain_rule_X_2var` は `hWcY_fin :
  mutualInfo μ Wc Yo ≠ ∞` を要求。背景 conditioner 付きで `condMutualInfo_ne_top`
  (`CondMutualInfo.lean:320`) を各 step に供給。

**retreat**: 詰まったら本 lemma body を `sorry` + `@residual(plan:bc-degraded-converse-plan)`。
signature は genuine 形 (上記等式) を維持、`*Hypothesis` 束ね禁止。

**見積 ~100-130 行。**

## Phase 2 — Csiszár sum 恒等式 (suffix expansion via reflection) 📋

proof-log: yes (crux、reflection 機構の前例化)。gateway `csiszar_sum_identity`
(`ConverseGateway.lean:112`) を genuine 化。

- [ ] **R1** `condMutualInfo_map_cond_measurableEquiv` (`I(X;Y|e∘Z)=I(X;Y|Z)`、
  `e : Z ≃ᵐ Z'`)。`condMutualInfo_map_left_measurableEquiv` の証明を conditioner 版へ。
- [ ] **R2** 反転 equiv `revSuffixEquiv : {j:Fin n // i.val<j.val} ≃ Fin (n-1-i.val)`
  を `Fin.revPerm` から構成 → `piCongrLeft` で `{j//i<j}→γ ≃ᵐ Fin _ →γ`。
- [ ] **LHS telescope**: 各 i で Phase 1 を背景 `B^{>i}` で適用 →
  `∑ᵢ ∑_{k<i} I(Aₖ;Bᵢ|A^{<k},B^{>i})`。
- [ ] **RHS telescope**: 各 i で suffix `B^{>i}` を R1+R2 で prefix 化し Phase 1 適用 →
  `∑ᵢ ∑_{j>i} I(Bⱼ;Aᵢ|A^{<i},B^{>j})`。
- [ ] **reindex + symmetry**: 両二重和を `{(i,j):i<j}` 共通形に
  (`Finset.sum_sigma`/`Finset.sum_comm` 系 + filter `i<j`)、各項を
  `condMutualInfo_comm` (`CondMutualInfo.lean:285`) で一致。

**retreat (2 段)**:
1. R2 reflection bookkeeping が off-by-one で詰まったら → **代替経路**: suffix chain
   rule を直接自作 (Phase 1 の suffix-induction 版、reflection 不使用)。これも genuine。
2. 代替も詰まったら → `csiszar_sum_identity` body を `sorry` のまま
   `@residual(plan:bc-degraded-converse-plan)` 維持 (現状)。signature 不変、
   `*Hypothesis` 束ね禁止。

**見積 ~160-260 行 (本 plan 支配 Phase)**: R1 ~30-50 + R2 ~50-90 + telescope/reindex/
symmetry assembly ~80-120。

## Phase 3 — bound (b) single-letterization 📋

proof-log: yes。
```
I(W₁; Y₁ⁿ | W₂) = ∑ᵢ I(Xᵢ; Y_{1,i} | Uᵢ)   (Uᵢ = (W₂, Y₂^{i-1}))
```

- [ ] chain rule (Phase 1) で `I(W₁;Y₁ⁿ|W₂)` を prefix 展開 →
  `∑ᵢ I(Y_{1,i}; W₁ | W₂, Y₁^{i-1})` 形。
- [ ] Csiszár sum (Phase 2) で prefix conditioner `Y₁^{i-1}` ↔ suffix `Y₂^{i-1}` 入替え。
- [ ] degradedness `X→Y₁→Y₂` (Markov) で `Uᵢ=(W₂,Y₂^{i-1})` への単一文字化を確定。
  Markov の供給は `condMutualInfo_eq_zero_of_markov` (`CondMutualInfo.lean:339`)。

**retreat**: 各サブ等式を `sorry` + `@residual(plan:bc-degraded-converse-plan)`、
degradedness は **precondition (Markov hyp = regularity)** として取り、結論 (sum 形) を
仮説に encode しない。**見積 ~60-100 行。**

## Phase 4 — `bc_converse` headline + `InBCCapacityRegion` 領域述語 📋

proof-log: yes。**注意: BC operational scaffolding は tree に不在**
(`rg 'BroadcastChannel|InBCCapacityRegion|bc_common_rate_bound'` で gateway probe 以外
0 件、moonshot の旧 pass-through コードは現存しない)。本 Phase は RV/MI レベルで
**新規定義**する (gateway と同じ level、operational kernel/codebook には降りない)。

- [ ] `InBCCapacityRegion` (新規 def、情報レベル): RVs `U, X, Y₁, Y₂` に対し
  `R₂ ≤ I(U;Y₂)` ∧ `R₁ ≤ I(X;Y₁|U)`、補助仮説 `U→X→(Y₁,Y₂)` (Markov)、degradedness
  `X→Y₁→Y₂`。Mathlib-shape-driven: 結論形は `mutualInfo`/`condMutualInfo` の `.toReal`
  不等式 (gateway bound と同形)。
- [ ] `bc_converse` headline (single-letterization): n-letter bound (a) + (b) から、
  正規化レート対が単一文字領域不等式 (補助 `U` 存在) を満たすことを結論。
  bound (a) = `bc_converse_bound_a` (genuine 済) + bound (b) = Phase 3。

**honesty boundary (重要)**: Fano の寄与 (operational rate ≤ `I(W;Yⁿ)/n + ε`) を仮説で
入れる場合は、**genuine operational precondition** (Fano 不等式
`H(W|Ŵ) ≤ 1 + Pe·log|W|` 由来) のみ。「レート対 ∈ 領域」を仮説に bundle するのは
load-bearing 禁止。本 plan の headline は情報レベル single-letterization に scope し、
operational Fano wrapper は別 thin follow-on に分離 (本 plan では情報レベルまでで
genuine closure)。

**retreat**: headline が情報レベルまで届かない場合、領域述語 + bound 組立だけ genuine 化し
operational 接続を `sorry` + `@residual(plan:bc-degraded-converse-plan)` で分離。
**見積 ~80-140 行 (領域 def 新規含む)。**

## Phase 5 — 独立監査 + root 登録 + roadmap Ch.15 同期 📋

proof-log: no。

- [ ] 新規 `sorry`+`@residual` を導入した commit があれば `honesty-auditor` を起動
  (orchestrator-mandatory)。Phase 2 R1 invariance / Phase 3 degradedness precondition の
  非 load-bearing 性を独立確認。
- [ ] gateway file を `InformationTheory.lean` に登録 (genuine 化後、現状 intentionally
  未登録)。新 file を切った場合も import 追記。
- [ ] `docs/textbook-roadmap.md` Ch.15 同期 + README theorem table (`bc_converse` を
  headline 化するなら `docs/readme-theorems.txt` 編集 → `gen_readme_table.ts --write`)。

## 親同期 TODO (本パスでは plan 文記載のみ、親編集は co-stage が要るため別 commit)

親 `broadcast-channel-moonshot-plan.md` は現在 **Status: CLOSED ✅**。L-BC2 再開に伴い:

- [ ] 親に **sub-plan 一覧テーブル / 進捗 DAG** を追加し、本 child
  (`bc-degraded-converse-plan.md`) への backlink 行を入れる (plan_lint 双方向照合点)。
- [ ] 親 Status を CLOSED → L-BC2 再開中 (該当 Phase 進行中) に更新。L-BC1/3/4/5 凍結 slug は
  不可侵 (他 plan 参照)。
- [ ] 親編集 commit には本 child を co-stage (pre-commit WARN 回避)。

## 判断ログ

1. **suffix-via-reflection を主経路採用 (reflection 検証済)**: reindex 部品
   (`Fin.revPerm`/`Finset.sum_range_reflect`/`MeasurableEquiv.piCongrLeft`) は全在庫。
   ただし suffix 展開を無料化せず、新規 R1 `condMutualInfo_map_cond_measurableEquiv`
   (conditioner relabel invariance、現 left/middle のみで不在) + R2 off-by-one reflection
   equiv にコストが移る。net ~80-140 行。代替 = suffix chain rule 直接自作 (Phase 2 retreat 1)。
2. **Phase 1 (条件付き n-var chain rule) が reflection 非依存の独立支配コスト**:
   `mutualInfo_chain_rule_fin` を template に背景 conditioner carry で induction lift。
   LHS telescope に直接、RHS telescope に reflection 経由で両用。
3. **BC operational scaffolding は tree 不在**: moonshot 旧 pass-through コードが現存せず
   (`rg` 0 件)、Phase 4 は領域述語 `InBCCapacityRegion` + degradedness を RV/MI レベルで
   新規定義。operational kernel/codebook/Fano は本 plan scope 外 (情報レベル
   single-letterization まで genuine closure)。
4. **honesty 撤退口の統一**: 全 Phase の dead-end は各 sub-lemma body を `sorry` +
   `@residual(plan:bc-degraded-converse-plan)`。`*Hypothesis` 束ね・degradedness/Fano の
   load-bearing 化を禁止 (Markov degradedness は precondition = OK)。
