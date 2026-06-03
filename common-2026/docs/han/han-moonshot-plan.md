# Han 不等式・ムーンショット計画 🌙

> 実態整合 (2026-05-20): DONE-UNCOND — `han_inequality` (`InformationTheory/Shannon/Han.lean:330`、binder は `[IsProbabilityMeasure μ]` + `Measurable` のみ、pass-through 仮定なし) / `jointEntropy_chain_rule` (`Han.lean:56`)。`lake env lean InformationTheory/Shannon/Han.lean` silent 再確認、0 sorry。
> **Status (2026-05-10): Phase A / B / C 全完了 (zero sorry)。** `InformationTheory/Shannon/Han.lean` で `han_inequality` が `lake env lean` を silent 通過。Phase A 4 主定理 (`InformationTheory/Shannon/Entropy.lean`) + Phase B `jointEntropy_chain_rule` + Phase C 本体 + plumbing (Pi reshape `MeasurableEquiv` 3 本 / index 同型 2 本)。退化ケース (`n = 0, 1`) も同じ証明で通過し、当初想定の `hn : 1 ≤ n` 仮定は不要と判明 (削除済)。proof-log は [`proof-log-han-moonshot.md`](proof-logs/proof-log-han-moonshot.md)。
>
> ゴールは **Han の不等式 (補集合形)** を Mathlib + 既存 `InformationTheory/Shannon` API の上に形式化し、そのプロセスで「次のムーンショットに渡せる共通化候補」を浮き上がらせること。

## Context

### モチベーション

Shannon converse 達成時点で `InformationTheory/Shannon/` には `mutualInfo` / `condMutualInfo` / `entropy` / `condEntropy` / DPI / chain rule (2 変数) / Markov chain といった主要 API が出揃っている。これらは「Shannon converse という単一の応用例」を支えるためにのみ書かれており、**第二の応用で擦ってみないと、どれが本当に再利用される/どれを抽象化すべきかが定まらない**。

Han の不等式は次の理由で「第二の応用」として最適:

1. **既存 API の主役級を全部使う** — entropy・condEntropy・condMI 非負（= 「条件付けでエントロピーは減る」）・chain rule。Shannon converse で組んだ stack を再演する形で消費するので、再利用の摩擦が直接見える。
2. **新規測度論プリミティブが要らない** — 確率空間・kernel・disintegrate の Mathlib 探索ターンが発生しないので、純粋に「自前 API の n 変数化」だけにフォーカスできる。
3. **n 変数化 (`Fin n`) という未踏の軸を 1 本だけ追加する** — これは Shannon converse / encoder 拡張が手を付けなかった軸。ここで詰まったハマりどころがそのまま「次のムーンショット (例: Slepian-Wolf converse, source coding converse) で必要になる n 変数 chain rule の再利用素材」になる。
4. **撤退してもダメージが小さい** — 自前定義 + 1 主定理という小さなスコープで、撤退ラインを途中（Phase B / Phase C 境界）に設けやすい。

つまり Han は「ムーンショット感の小さい純応用」と引き換えに、**`InformationTheory/Shannon` の n 変数拡張を独立に検証する** 役を引き受ける。

### Han の不等式（補集合形）

最終到達点:

```lean
theorem han_inequality
    {n : ℕ}
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
                [MeasurableSpace α] [MeasurableSingletonClass α]
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Fin n → Ω → α) (hXs : ∀ i, Measurable (Xs i)) :
    ((n : ℝ) - 1) * jointEntropy μ Xs
      ≤ ∑ i : Fin n, jointEntropyExcept μ Xs i
```

ヘルパ:

- `jointEntropy μ Xs := entropy μ (fun ω i => Xs i ω)` — 既存 `Shannon.entropy` を `Fin n → α` 値の RV に適用しただけのラッパー
- `jointEntropyExcept μ Xs i := entropy μ (fun ω (j : {j // j ≠ i}) => Xs j ω)` — 補集合 `{j // j ≠ i}` 上の値で entropy を取った形

> **当初プランからの差分**: `hn : 1 ≤ n` を仮定していたが、`n = 0` で LHS = `(-1) · 0 = 0`、RHS = 空和 = 0 で成立。`hn` 不要が実装で判明し statement から削除。RHS は当初「無名 lambda」直書きだったが、各補題で再利用するため `jointEntropyExcept` ヘルパに切り出した。

### 非ゴール

- **subset average 形 (Han 1978 原論文)**: \(\binom{n}{k}^{-1} \sum_{|S|=k} H(X_S) / k\) の \(k\) 単調性。複合系として Phase D 候補
- **Shearer の不等式**: fractional cover 一般化。Phase D 候補
- **異種類型 `Xs : ∀ i, Ω → α i`**: 各 \(X_i\) が異なる codomain を持つ場合。homogeneous (`α` 固定) 版で textbook 形は十分カバーできるので Phase D 候補
- **Mathlib upstream PR**: 副産物として出るのは歓迎、能動的には追わない

---

## Approach

**4 段構成 (Phase 0 → A → B → C)。Phase A で「2 変数の自前 entropy 補題」、Phase B で「n 変数化」、Phase C で組み合わせて Han。**

```
Phase 0  : Mathlib + 既存 Shannon API インベントリ          ← 1 ターン
            ──────────────────────────────────────────
Phase A  : 2 変数 entropy 補題 (chain rule + monotonicity)  ← 既存 mutualInfo 経由で導出
            ──────────────────────────────────────────
Phase B  : n 変数 (Fin n) 化と n 変数 chain rule              ← Fin n 上の induction
            ──────────────────────────────────────────
Phase C  : Han 不等式 🌙                                    ← Phase A + B の組み合わせのみ
```

### Approach の根幹: 既存 API への薄いラッパーで通す

新規定義は `jointEntropy` (`entropy` の `Fin n → α`-値特殊化) と「部分集合 restrict 補題」程度に留め、**主要な内容は既存の `mutualInfo_*` / `condMutualInfo_*` / `mutualInfo_eq_entropy_sub_condEntropy` (Bridge) から導出**する方針。これは:

- (a) 既存 API の弱点 — 例えば「2 変数 chain rule は MI 経由でしか書けていない」「条件付けでエントロピーが減ることが直接補題として無い」── を顕在化させる
- (b) 新規証明の肉部分は Phase B の `Fin n` induction だけに局所化される

### Han の証明骨格 (純 plumbing)

```
∀ i, H(X_{[n]}) - H(X_{-i}) = H(X_i | X_{-i})            -- chain rule (Phase A の 2 変数版を pair 化)
                            ≤ H(X_i | X_{<i})            -- 条件付けでエントロピーは減る (Phase A)

∑ i, H(X_{<i} に対する条件付き) = H(X_{[n]})              -- n 変数 chain rule (Phase B)

∴ ∑ i, (H(X_{[n]}) - H(X_{-i})) = ∑ i, H(X_i | X_{-i})
                                ≤ ∑ i, H(X_i | X_{<i})
                                = H(X_{[n]})

∴ n · H(X_{[n]}) - ∑ i, H(X_{-i}) ≤ H(X_{[n]})
∴ (n-1) · H(X_{[n]}) ≤ ∑ i, H(X_{-i})
```

ここで \(X_{<i} := (X_0, \dots, X_{i-1})\), \(X_{-i} := (X_0, \dots, \hat{X_i}, \dots, X_{n-1})\)。

### なぜ 4 段に分けるか

1. **Phase A 単独で価値がある** — 「`InformationTheory/Shannon/Entropy.lean` に 2 変数 chain rule と『条件付けでエントロピーは減る』を整備した」という独立した成果として publish 可能。Han に届かなくても次の Slepian-Wolf / source coding に直接流用できる素材
2. **Phase B が技術的山場** — `Fin n` の prefix / complement / induction を Lean で扱う部分。ここが想定外に重ければ Phase C 着手前に判断できる
3. **Phase C は組み合わせのみ** — Phase A + B が片付けば 50〜100 行で Han 本体は通る見込み
4. **Phase 0 (M0) で「Mathlib に既存 Han がないこと」「既存 `InformationTheory/Shannon` に何が足りないか」を 1 ターンで明文化** することで、Phase A 着手時の不確実性を潰す

### ファイル構成 (Phase C 終了時)

```
InformationTheory/Shannon/
  Entropy.lean        ← Phase A: 2 変数 chain rule + 条件付けでエントロピーは減る
  Han.lean            ← Phase B + C: jointEntropy (Fin n), n 変数 chain rule, Han
```

`InformationTheory.lean` (library root) に対応する `import InformationTheory.Shannon.{Entropy,Han}` を順次追記。

---

## Phase 0 (M0): Mathlib + 既存 Shannon API インベントリ

### スコープ

- **Mathlib 側に Han / Shearer / 一般化エントロピー不等式が既に存在しないか確認** (`InformationTheory/Shannon/`, `InformationTheory/KullbackLeibler/`, 念のため `Combinatorics/`)
- **既存 `InformationTheory/Shannon/*.lean` の n 変数耐性レビュー**:
  - `entropy` を `Ω → (Fin n → α)` に instantiate したとき必要な instance チェイン (`Pi.fintype`, `MeasurableSpace.pi`, `MeasurableSingletonClass`) が自動で発火するか
  - `mutualInfo` を `(Fin n → α)`-値 RV に適用するときの障害物
  - `condMutualInfo_nonneg` の signature が `H(X|Y,Z) ≤ H(X|Y)` の形に乗るか
- **Phase A で必要な補題リストの確定** (下記 Phase A 「鍵となる作業」を裏取り)

### 成果物

- `docs/han/han-mathlib-inventory.md` — 上記 3 軸の調査結果 + Phase A 着手時の不確実性ランク
- 本計画書 ([このファイル](han-moonshot-plan.md)) への反映 (Approach / Phase A 節)

### Done 条件

- 「Mathlib に Han 不等式は無い」を裏取り済み (loogle + rg)
- Phase A の skeleton (`InformationTheory/Shannon/Entropy.lean` の sorry-driven 出だし) が書ける状態

### 工数感

1 ターン (10〜15 分)。subagent 1 本 + ローカル確認。

---

## Phase A: 2 変数 entropy 補題

### スコープ

```lean
namespace InformationTheory.Shannon

variable {Ω : Type*} [MeasurableSpace Ω]
variable {X : Type*} [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X]
variable {Y : Type*} [Fintype Y] [MeasurableSpace Y] [MeasurableSingletonClass Y]
variable {Z : Type*} [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]

/-- Entropy chain rule: `H(X, Y) = H(X) + H(Y | X)`. -/
theorem entropy_pair_eq_entropy_add_condEntropy
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Ω → X) (Yo : Ω → Y) (hXs : Measurable Xs) (hYo : Measurable Yo) :
    entropy μ (fun ω => (Xs ω, Yo ω))
      = entropy μ Xs + condEntropy μ Yo Xs

/-- Conditioning on more variables reduces entropy: `H(X | Y, Z) ≤ H(X | Y)`. -/
theorem condEntropy_le_condEntropy_of_pair
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Ω → X) (Yo : Ω → Y) (Zo : Ω → Z)
    (hXs : Measurable Xs) (hYo : Measurable Yo) (hZo : Measurable Zo) :
    condEntropy μ Xs (fun ω => (Yo ω, Zo ω)) ≤ condEntropy μ Xs Yo

end InformationTheory.Shannon
```

### 鍵となる作業

1. **`entropy_pair_eq_entropy_add_condEntropy` (chain rule)** — 既存 `mutualInfo_eq_entropy_sub_condEntropy` (Bridge) を 2 通りの順で適用して `H(X,Y) - H(X) = H(Y|X)` を導出。あるいは KL chain rule (`klDiv_compProd_eq_add`) から直接書き下す。50〜100 行
2. **`condEntropy_le_condEntropy_of_pair` (条件付けで減る)** — `condMutualInfo_nonneg` を bridge して `condMutualInfo = condEntropy - condEntropy` の形に直す中間補題が要る。Phase A の山場。**150〜200 行 (Bridge fiber 再利用ルート想定)**
   - 中間補題: `condMutualInfo_eq_condEntropy_sub_condEntropy: I(X; Z | Y) = H(X|Y) - H(X|Y,Z)` (要新規)
   - **採用ルート (Phase 0 で確定)**: `condMutualInfo` は両 base 共通 compProd 形なので `Bridge.lean` の Helper 1 (`klDiv_compProd_const_eq_lintegral_of_ac`) で fiber-wise に klDiv を分解 → fiber 上で Bridge 主定理 `mutualInfo_eq_entropy_sub_condEntropy` を呼ぶ → `condEntropy` の tower 補題 (`H(X|Y,Z) = ∫ z, H_z(X|Y) d(μ.map Z)`、要 derive 50 行) で結ぶ。Bridge 全体 (~190 行) の写経は不要。詳細: [`han-mathlib-inventory.md` §3](han-mathlib-inventory.md#3-phase-a-中間補題-condmutualinfo_eq_condentropy_sub_condentropy-所要量)
3. **両者の Real / ENNReal 整理** — `condEntropy` は `ℝ`、`mutualInfo`/`condMutualInfo` は `ℝ≥0∞`。Bridge と同じ `toReal` 取扱で揃える

### Done 条件

- 上記 2 定理が `lake env lean InformationTheory/Shannon/Entropy.lean` で silent
- `InformationTheory.lean` に `import InformationTheory.Shannon.Entropy` 追記
- skeleton-driven で `entropy_pair_eq_entropy_add_condEntropy` → `condMutualInfo_eq_condEntropy_sub_condEntropy` → `condEntropy_le_condEntropy_of_pair` の順に sorry を割っていく

### 工数感

1 週間予算。山場は中間補題 `condMutualInfo_eq_condEntropy_sub_condEntropy`。`mutualInfo_eq_entropy_sub_condEntropy` の証明骨格をほぼ写経できる見込み。

---

## Phase B: n 変数 (`Fin n`) infrastructure

### スコープ

```lean
namespace InformationTheory.Shannon

variable {n : ℕ}
variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
variable {Ω : Type*} [MeasurableSpace Ω]

/-- Joint entropy of a finite family of random variables. -/
noncomputable def jointEntropy
    (μ : Measure Ω) (Xs : Fin n → Ω → α) : ℝ :=
  entropy μ (fun ω i => Xs i ω)

/-- Joint entropy restricted to a subset of indices (here: complement of a single index). -/
noncomputable def jointEntropyExcept
    (μ : Measure Ω) (Xs : Fin n → Ω → α) (i : Fin n) : ℝ :=
  entropy μ (fun ω (j : {j // j ≠ i}) => Xs j ω)

/-- n 変数 chain rule:
`H(X_0, ..., X_{n-1}) = ∑ i, H(X_i | X_0, ..., X_{i-1})`. -/
theorem jointEntropy_chain_rule
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Fin n → Ω → α) (hXs : ∀ i, Measurable (Xs i)) :
    jointEntropy μ Xs
      = ∑ i : Fin n,
          condEntropy μ (Xs i) (fun ω (j : Fin i) => Xs ⟨j, j.isLt.trans i.isLt⟩ ω)

end InformationTheory.Shannon
```

### 鍵となる作業

1. **`jointEntropy` / `jointEntropyExcept` の定義** — 既存 `entropy` の薄いラッパー。Pi instance チェイン (`Pi.fintype` + `MeasurableSpace.pi` + `MeasurableSingletonClass`) が `Fin n → α` および `{j // j ≠ i} → α` で自動発火するか Phase 0 で確認済みであること
2. **n 変数 chain rule の induction** — `n` に関する induction で
   - base case: `n = 0` (空和、`entropy μ default = 0`) と `n = 1` (1 変数 = `entropy μ (Xs 0)`)
   - step: `Fin (n+1) → α` を `Fin n → α` に restrict した部分と `Xs ⟨n, _⟩` の pair に分解 → Phase A の `entropy_pair_eq_entropy_add_condEntropy` を 1 段適用 → IH で n-prefix を展開 → `Finset.sum_range_succ` で和に整理
3. **`Fin n` 上の `{j // j ≠ i}` (補集合) と prefix `Fin i` の Finset.sum 操作** — `Fin.cases` / `Fin.snoc` / `Equiv.optionEquivSumOne` 系の Mathlib API 探索が地味に重い可能性
4. **`condEntropy` と「Xs を `Fin i → α` 値 RV に纏めたもの」の整合** — Phase A の 2 変数 condEntropy に Pi-値 RV を喰わせるだけだが、measurability instance 補完がやや煩雑

### Done 条件

- `jointEntropy_chain_rule` が `lake env lean InformationTheory/Shannon/Han.lean` で silent
- Phase A に依存。`import InformationTheory.Shannon.Entropy` を含む
- skeleton: 定義 → `n = 0` / `n = 1` の sanity → induction step の順に sorry を割る

### 工数感

1〜2 週間予算。**Pi-値 RV measurability instance の自動発火は Phase 0 で confirm 済** (`Pi.instMeasurableSingletonClass [Countable δ]` + `MeasurableSingletonClass.toDiscreteMeasurableSpace` priority 100 + DMS → SBS の chain で `Fin n → α` まで自動)。残るリスクは skeleton 書き起こし時の type-check 1 発のみ。詰まったら異種類型を捨てて homogeneous (`α` 固定) に追加で手動 instance を充てる。

---

## Phase C: Han の不等式 🌙

### スコープ

```lean
namespace InformationTheory.Shannon

theorem han_inequality
    {n : ℕ}
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
                [MeasurableSpace α] [MeasurableSingletonClass α]
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Fin n → Ω → α) (hXs : ∀ i, Measurable (Xs i)) :
    ((n : ℝ) - 1) * jointEntropy μ Xs
      ≤ ∑ i : Fin n, jointEntropyExcept μ Xs i

end InformationTheory.Shannon
```

### 証明骨格 (純 plumbing)

```
∀ i,
  jointEntropy μ Xs - jointEntropyExcept μ Xs i
    = condEntropy μ (Xs i) (Xs except i)        -- Phase A chain rule + 添字並び替え
    ≤ condEntropy μ (Xs i) (Xs prefix < i)      -- Phase A condEntropy_le_condEntropy_of_pair
                                                   (補集合 = prefix + suffix なので suffix を「条件付けに追加した」)

∑ i, (jointEntropy μ Xs - jointEntropyExcept μ Xs i) ≤ ∑ i, condEntropy μ (Xs i) (prefix)
                                                       = jointEntropy μ Xs   -- Phase B chain rule

⟹ n · jointEntropy μ Xs - ∑ i, jointEntropyExcept μ Xs i ≤ jointEntropy μ Xs
⟹ (n - 1) · jointEntropy μ Xs ≤ ∑ i, jointEntropyExcept μ Xs i
```

### 鍵となる作業

1. **`Xs except i` を `Xs prefix < i` に condEntropy 経由で繋ぐ補題** — 補集合 `{j // j ≠ i}` を prefix `Fin i` + suffix `{j // i < j}` に分解し、Phase A の `condEntropy_le_condEntropy_of_pair` を 1 回呼ぶ。20〜40 行
2. **`Finset.sum_le_sum` で個別不等式を合計**
3. **Phase B chain rule で右辺の和を `jointEntropy` に潰す**
4. **代数: `n · H - ∑ ≤ H ⟹ (n-1) · H ≤ ∑`** — `linarith` / `nlinarith` で 1 行

### Done 条件

- `han_inequality` が `lake env lean InformationTheory/Shannon/Han.lean` で silent
- Phase A + B がすべて activated (主定理が `entropy_pair_eq_entropy_add_condEntropy`, `condEntropy_le_condEntropy_of_pair`, `jointEntropy_chain_rule` を直接呼ぶ)
- `n = 0, 1` 退化ケース (両辺 0) も同じ証明で追加処理なしに通った (`hn : 1 ≤ n` 不要が判明し statement から削除)

### 工数感

1 週間予算。Phase A + B が片付けば組み合わせのみ。**最大リスクは「補集合 ↔ prefix + suffix」変換の Fin/Subtype 等価性 plumbing**。

---

## 失敗判定 / 撤退ライン

- **Phase 0 で Mathlib に Han が既にあった**場合 → 計画破棄、proof-log だけ取って Slepian-Wolf converse 等に乗り換え
- **Phase A の `condMutualInfo_eq_condEntropy_sub_condEntropy` 中間補題で 1 週間溶ける**場合
  → Phase A を `entropy_pair_eq_entropy_add_condEntropy` のみで打ち止めにし、Phase B 着手は条件付けでエントロピーが減る部分を「KL chain rule から直接 Han 用に局所証明」する経路に倒す
- **Phase B の `Fin n` 上 Pi-値 RV measurability で 1 週間以上溶ける**場合
  → Phase C を `n = 3` / `n = 4` 固定の concrete 形に縮める。一般 n は将来課題に
- **Phase C の補集合 / prefix 変換で詰まる**場合
  → `n` 一般化を諦め `n = 3` 形 `2 H(X,Y,Z) ≤ H(X,Y) + H(Y,Z) + H(X,Z)` で publish。subset / Shearer 拡張は別計画に
- どのケースも「Han に届かなかった」ではなく **「`InformationTheory/Shannon` の n 変数化で詰まった具体ポイント」をデータとして残す**

---

## 当面の next step

1. ~~**Phase 0 着手** — Mathlib + 既存 Shannon API インベントリ調査 (subagent 1 本 + ローカル `loogle` / `rg`)~~ ✅ 2026-05-10 完了 → [`han-mathlib-inventory.md`](han-mathlib-inventory.md)
2. ~~Phase 0 結果を見て、本計画書の Approach / Phase A 節を必要に応じて更新~~ ✅ Phase A 工数感 (150〜200 行) / Phase B 最大リスク (instance 自動発火 confirm 済) 反映
3. ~~**Phase A skeleton + 充填**~~ ✅ 2026-05-10 完了 (`InformationTheory/Shannon/Entropy.lean` に 4 主定理: chain rule / tower / middle lemma / 「条件付けで減る」)
4. ~~**Phase B skeleton + 充填**~~ ✅ 2026-05-10 完了 (`jointEntropy` 定義 + n 変数 chain rule。`InformationTheory/Shannon/Han.lean`)
5. ~~**Phase C 充填**~~ ✅ 2026-05-10 完了 (`han_inequality` 本体。`hn : 1 ≤ n` 不要が判明し削除、index 同型 2 本 + Pi reshape `MeasurableEquiv` 3 本 + `han_single_bound` を投入)
6. ~~**proof-log 作成**~~ ✅ 2026-05-10 完了 → [`proof-log-han-moonshot.md`](proof-logs/proof-log-han-moonshot.md)

### ムーンショット完了後の方向 (user 判断)

- **Phase D (subset average / Shearer)**: 「非ゴール」(line 41-45) に置いた拡張を別 plan に切り出す候補。Han 本体の `han_single_bound` パターンが再利用できるかが見どころ。
- **Slepian-Wolf converse** (撤退ライン側にあった代替): n 変数 chain rule + Markov chain converse の組み合わせで、`InformationTheory/Shannon/Converse.lean` の延長として書ける見込み
- **`InformationTheory/Shannon` の API 整理**: Han で擦った結果 `MeasurableEquiv.piCongrLeft` + `sumPiEquivProdPi` + `funUnique` の 3 点セットや、`entropy_measurableEquiv_comp` のような plumbing は次のムーンショットでも使う。Shannon 本体に上げるかは proof-log 観察を踏まえて検討
