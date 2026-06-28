# Shannon: degraded BC converse single-letterization サブ計画

> **Parent**: [`broadcast-channel-moonshot-plan.md`](broadcast-channel-moonshot-plan.md) — 凍結退避線 **L-BC2「Fano + chain rule」を再開し genuine closure 済**

**Status**: CLOSED ✅ — degraded broadcast channel の converse single-letterization
(Cover–Thomas Thm 15.6.2) を genuine closure。headline `bc_converse`
(auxiliary-variable 容量領域 membership) + 核 `bc_input_singleletterize` /
`bc_singleletterize_bound₁` は全て `@audit:ok`・`InformationTheory.lean` 登録済。
**SoT**: code (`InformationTheory/Shannon/BroadcastChannel/{Converse,ConverseGateway,Basic}.lean`
+ `InformationTheory/Shannon/CondMIChainRule.lean`)。詳細履歴は git。
**再検証** (prose にキャッシュしない):
`scripts/sig_view.ts --sorry InformationTheory/Shannon/BroadcastChannel/Converse.lean` (0 件) /
`#print axioms InformationTheory.Shannon.BroadcastChannel.bc_converse` (sorryAx-free)。

## 進捗

- [x] Phase 0 — Mathlib/in-project API 在庫 再確認 ✅
- [x] Phase 1 — 条件付き n-var MI chain rule (prefix) ✅ → `condMutualInfo_prefix_chain_rule`
  (`CondMIChainRule.lean`、`@audit:ok`)
- [x] Phase 2 — Csiszár sum 恒等式 (suffix expansion via reflection) ✅ → `csiszar_sum_identity`
  (`ConverseGateway.lean`、`@audit:ok`)。**※ 最終 headline atom では未使用** — Route B にピボット
  (下記 Approach / 判断ログ #1)
- [x] Phase 3 — 入力単一文字化 (degraded core) ✅ → `bc_input_singleletterize` + message-level
  `bc_singleletterize_bound₁`
- [x] Phase 4 — `bc_converse` headline + `InBCCapacityRegion` 領域述語 ✅ (`Basic.lean` の
  `InBCCapacityRegion` + `InBCCapacityRegion.mono`)
- [x] Phase 5 — 独立監査 (`@audit:ok`) + root 登録 + roadmap Ch.15 同期 ✅

## ゴール / Approach (達成)

**達成状態**: degraded BC converse の single-letter 領域 membership headline `bc_converse` を
proof done で publish。rate pair `(log M₁, log M₂)` が、per-letter channel 和
`∑ᵢ I(Xᵢ;Y_{1,i}|Uᵢ)` (receiver 1) / `∑ᵢ I(Uᵢ;Y_{2,i})` (receiver 2、`Uᵢ=(W₂,Y₂^{i-1})`)
+ Fano error slack で定まる auxiliary-variable 容量領域 (`InBCCapacityRegion`) に入ることを示す。
memoryless + degradedness は explicit precondition (single-user
`channel_coding_converse_general_memoryless_pure` / `mac_converse` と parity)。operational
instantiation (uniform message → encoder → channel で `μ` を構成) は scope 外 (別 wrapper、
`mac_converse` と同方針)。

### 実際の closure ルート = Route B (entropy-difference、Csiszár 非経由)

**当初計画は Csiszár sum 恒等式を crux に置いていたが、最終 closure はそれを使わなかった**。
支配核 `bc_input_singleletterize` は、MAC の `condMutualInfo_singleletter_le_of_memoryless`
テンプレを clone した **Route B (term-by-term degradedness / 条件付きエントロピー差分)** で閉じた:

- LHS `I(Xⁿ;Y₁ⁿ|W₂)` を条件付きエントロピー差 `H(Y₁ⁿ|W₂) − H(Y₁ⁿ|(W₂,Xⁿ))` に展開
  (`condMutualInfo_eq_condEntropy_sub_condEntropy` + `condMutualInfo_comm`)。
- 両エントロピーを `condEntropy_pi_chain_rule_aux` で per-letter 和に分解 (prefix conditioner)。
- memoryless 雑音 (`h_memo`) で `H(Y₁ⁿ|(W₂,Xⁿ))` を `∑ᵢ H(Y₁ᵢ|Xᵢ)` に collapse。
- block-prefix degradedness (`h_deg_block`) で conditioner を `Y₁^{<i}` → `Y₂^{<i}` に入替え
  (conditioning-reduces-entropy)。

Csiszár route (LHS prefix / RHS suffix を共通三角二重和に telescoping) は degraded case には
over-powered と判断し放棄。

### Csiszár 系 infra は build 済だが本 atom では非 load-bearing

旧 Phase 1-2 が見込んだ重 infra は全て in-tree `@audit:ok` で、後続 family (一般 BC /
Marton / Relay) で再利用しうる資産。ただし **`bc_input_singleletterize` の最終証明はこれらを
呼ばない** (Route B が直接 condEntropy 差で閉じるため):

| 資産 | file | 用途 (本 atom では非依存) |
|---|---|---|
| `csiszar_sum_identity` | `ConverseGateway.lean` | Csiszár sum 恒等式 (prefix/suffix telescoping) |
| `condMutualInfo_prefix_chain_rule` / `condMutualInfo_suffix_chain_rule` | `CondMIChainRule.lean` | 条件付き n-var chain rule (prefix + reflection 経由 suffix) |
| `revSuffixEquiv` / `piReindexMeasurableEquiv` | `CondMIChainRule.lean` | R2 reflection equiv (suffix→prefix relabel) |
| `condMutualInfo_map_cond_measurableEquiv` | `CondMutualInfo.lean` | R1 conditioner relabel invariance |
| `bc_converse_bound_a` | `ConverseGateway.lean` | bound (a) genuine (gateway 由来) |

## クロージャ記録 (settled facts — 再利用しうる学び)

1. **`bc_input_singleletterize` は 2 回 false-as-framed と判明 → signature 強化で TRUE-as-framed
   化**。弱い per-letter 仮説では結論が偽だった:
   - **第1回** (commit `8cffe3cb`): free-W₂ collider 反例。弱い memoryless 仮説では `Y₁ᵢ` が
     W₂ 経由で交絡し、per-letter collapse が成立しない。
   - **第2回** (commit `3b3396e1`): cross-letter Y₂ leak 反例。per-letter degradedness
     `h_degraded` だけでは block-prefix の `Y₂^{<i}` 漏れを止められない。
   - **最終 (TRUE-as-framed) 仮説集合**: (a) `h_memo` = joint-output memoryless
     `Y₁ᵢ ⫫ (W₂, X^{≠i}, Y₁^{≠i}, Y₂^{≠i}) | Xᵢ` (各 i)、(b) `h_deg_block` = block-prefix
     degradedness `Y₁ᵢ ⫫ Y₂^{<i} | (W₂, Y₁^{<i})` (旧 weak `h_degraded` を置換)。両者 genuine な
     構造的 CI precondition で、独立監査で non-load-bearing 確認 (single-user converse parity)。
2. **Route B pivot**: crux を Csiszár sum 恒等式から MAC clone の entropy-difference /
   term-by-term degradedness に変更 (判断ログ #1)。Csiszár infra は build 済だが本 atom では非依存。

## 判断ログ

1. **crux を Csiszár sum → Route B (entropy-difference) にピボット**: 当初 Approach は Csiszár sum
   恒等式 (LHS prefix / RHS suffix telescoping) を支配核に置き ~300-500 行を見込んだが、degraded
   case では `condMutualInfo_singleletter_le_of_memoryless` (MAC) テンプレを clone した
   term-by-term degradedness で `bc_input_singleletterize` が閉じた。Csiszár route は
   over-powered として放棄 (infra 自体は `csiszar_sum_identity` 他で build 済・`@audit:ok`、
   後続 family で再利用可能)。
2. **`bc_input_singleletterize` の仮説は 2 回 false → 強化で TRUE**: 弱い per-letter
   memoryless / degradedness では反例 (free-W₂ collider / cross-letter Y₂ leak)。joint-output
   memoryless `h_memo` + block-prefix degradedness `h_deg_block` で TRUE-as-framed 化、監査 PASS
   (クロージャ記録 #1)。
3. **honesty boundary**: memoryless / degradedness / message uniformity / independence は全て
   precondition (regularity / 構造的 CI)。「レート対 ∈ 領域」を仮説に bundle せず、operational
   Fano wrapper は scope 外 (`mac_converse` と同方針)。
