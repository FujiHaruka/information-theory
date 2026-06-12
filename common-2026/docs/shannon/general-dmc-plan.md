# I-2 General DMC capacity (limit form) サブ計画 🌙

**Status**: CLOSED ✅ — `BlockwiseChannel` namespace + `capacity_lim` を publish、`capacity_lim_eq_capacity_of_memoryless` で既存単一-letter `capacity W` と接続。既存 callsite は不変。
**SoT**: `docs/textbook-roadmap.md` Ch.7 (general DMC / Tier ∞ Infrastructure)。詳細履歴は git。
> **Parent**: [`textbook-roadmap.md`](../textbook-roadmap.md) §「Tier ∞ — Infrastructure / I-2」

## 要点 (任意, ≤5 行)
- 戦略: 既存 `capacity W` を書き換えず並置 layer を積む。`BlockwiseChannel := (n:ℕ) → Kernel (Fin n→α) (Fin n→β)` (関数形、候補 A) + `capacityN : ℝ≥0∞` + `capacity_lim := atTop.limUnder (capacityN n / n)`。
- memoryless 接続は per-`n` 等式 `capacityN (ofMemoryless W) n = n·capacity W` + constant 列の limit (Fekete 不要)。
- `Kernel.pi` は Mathlib 不在。`Channel.toBlock` は `Kernel.mk` + `Measure.pi (fun i => W (x i))` 直接定義に再定義して `compProd`/`pi` factorize bridge を閉じた (inductive recursion 経路から pivot)。
- Inventory: [`general-dmc-mathlib-inventory.md`](./general-dmc-mathlib-inventory.md)。
