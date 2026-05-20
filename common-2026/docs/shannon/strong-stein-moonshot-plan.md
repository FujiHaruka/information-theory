# Strong Stein ムーンショット計画 🌙

(B-4 / moonshot-seeds.md, 2026-05-12 起草)

> **実態整合 (2026-05-20): DONE-UNCOND** — Phase A〜C すべて完了。`Common2026/Shannon/StrongStein.lean:498` の `stein_strong_lemma` が strict `Tendsto (… → 𝓝 (klDiv P Q).toReal)` を std binders (`hMapJoint` 等は honest i.i.d. joint-law 仮定、pass-through なし) で discharge。`StrongStein.lean` 全体 0 sorry / 0 `:=True`。

## 進捗

- [x] Phase 0 — Mathlib + 既存 inventory + 経路判定 ✅ → [strong-stein-mathlib-inventory.md](strong-stein-mathlib-inventory.md)
- [x] Phase A — `steinTypicalSet` の Q-側 lower bound (`Q^n(T_n^δ) ≥ exp(-n(K+δ)) · P^n(T_n^δ)`) ✅
- [x] Phase B — 任意 α-level test の Q^n に対する strong-converse 形 `liminf -(1/n) log Q^n(B_n) ≤ K` ✅
- [x] Phase C — `steinOptimalBeta` strict `Tendsto` 主定理 (`stein_strong_lemma`) ✅

## ゴール / Approach

**ゴール**: 任意 `ε ∈ (0,1)` に対して

```
Tendsto (fun n ↦ -(1/n) * log (steinOptimalBeta P Q n ε)) atTop (𝓝 (klDiv P Q).toReal)
```

を示す。既存 `stein_lemma` の `liminf ≥ K` 側はそのまま再利用し、`limsup ≤ K`
側 (=現状 `limsup ≤ K/(1-ε)` から `1/(1-ε)` 補正を消す) を補強する。

**Approach (採用経路: Pinsker 不要 / Sanov 不要 / Mathlib に既存の `stein_inProbability` 経由)**:

現行 converse `stein_converse_finite_n` は DPI on Bool reduction を経由するため
`Pn.real s * (-log Qn.real s) ≥ (1-ε) * (-log Qn.real s)` で `1/(1-ε)` 補正が
構造的に残る。これを置換し、**LLR-typicality (上側) + 集合交差** で直接

```
Q^n(B_n) ≥ exp(-n(K+δ)) · P^n(B_n ∩ T_n^δ)
```

を取る。`stein_inProbability` (WLLN on LLR) が既に `P^n((T_n^δ)^c) → 0` を与え、
任意 α-level test `B_n` (`P^n(B_n^c) ≤ ε`) と組合せて `P^n(B_n ∩ T_n^δ) ≥ 1-ε-o(1) > 0`。

- **Pinsker 経由ではない**: Pinsker (`TV ≤ √KL`) は alphabet 上の TV と KL を
  繋ぐが、Stein converse の `1/(1-ε)` は KL 値ではなく `Pn(s)` factor から来る。
  LLR typicality 経路の方が直接的。
- **information spectrum 不要**: Mathlib に `InformationSpectrum` 系の API は存在
  しない (`rg`/`loogle` 確認済)。Han-Verdú framework を Lean に持ち込むのは
  本シードの規模を破壊する (4-6 週)。LLR typicality + WLLN は既存 plumbing で完結。
- **既存 `steinTypicalSet_Q_prob_le` の双対形を新規補題で**: 既存は LLR 下側
  `K - δ < S/n` から `Q^n(x) ≤ exp(-n(K-δ)) · P^n(x)` を取る。Strong converse は
  LLR 上側 `S/n < K + δ` から `Q^n(x) ≥ exp(-n(K+δ)) · P^n(x)` を取る (symmetric)。

**規模見積 (Phase 0 inventory 後)**:

- Phase A: ~150 行 (per-point lower bound + 集合形)
- Phase B: ~200 行 (`liminf` 形の strong converse、任意 test → typicality 経由)
- Phase C: ~100 行 (Tendsto 主定理、既存 `stein_lemma` の liminf 側流用)
- 合計 ~450-550 行、新規 `Common2026/Shannon/StrongStein.lean`。
- 既存 `Stein.lean` 改変なし、downstream 影響なし。

## Phase 0 — Mathlib + 既存 inventory + 経路判定 ✅

参照: [strong-stein-mathlib-inventory.md](strong-stein-mathlib-inventory.md)

判定結論:
1. **information spectrum 経路**: Mathlib 0 件、4-6 週で別シード化。**却下**。
2. **Pinsker 経由**: `TV ≤ √KL` で `Pn(s) ≥ 1 - ε` を介して `Qn(s) ≥ ?` を取る経路、
   定数追跡が複雑かつ qualitative には LLR typicality と等価で短くならない。**却下**。
3. **LLR typicality (上側)**: 既存 `stein_inProbability` + `steinTypicalSet` の
   plumbing 上に、`steinTypicalSet_Q_prob_le` の双対形 (Q-side lower bound) を
   1 本追加するだけで strong converse が組める。**採用**。

## Phase A — `steinTypicalSet` の Q-側 lower bound

- [x] `steinTypicalSet_Q_prob_ge`: `Q^n(T_n^δ) ≥ exp(-n(K+δ)) · P^n(T_n^δ)`。
  - Per-point bound on `T_n^δ`: `x ∈ T_n^δ` ⇒ `S/n - K < δ`, i.e. `S < n(K+δ)`,
    where `S = ∑ i, llrPmf P Q (x i) = log(P^n(x)/Q^n(x))`.
    ⇒ `Q^n(x) ≥ exp(-n(K+δ)) · P^n(x)` (point-wise).
  - 集約 (`steinTypicalSet_Q_prob_le` の symmetric 構造):
    `Q^n(T_n^δ) = ∑_{x ∈ T_n^δ} Q^n(x) ≥ exp(-n(K+δ)) · ∑_{x ∈ T_n^δ} P^n(x)
                = exp(-n(K+δ)) · P^n(T_n^δ)`.

## Phase B — 任意 α-level test の Q^n strong-converse lower bound

- [x] `steinAlphaTest_Q_prob_ge`: 任意 `s : Set (Fin n → α)` with `P^n(sᶜ) ≤ ε` について
  ```
  Q^n(s) ≥ exp(-n(K+δ)) · P^n(s ∩ T_n^δ)
  ```
  - `s ∩ T_n^δ ⊆ T_n^δ` で per-point bound を流用 → `Q^n(s ∩ T_n^δ) ≥ exp(-n(K+δ)) · P^n(s ∩ T_n^δ)`。
  - `Q^n(s) ≥ Q^n(s ∩ T_n^δ)` (monotonicity)。

- [x] `steinAlphaTest_Pn_intersect_ge`: `P^n(s ∩ T_n^δ) ≥ P^n(T_n^δ) - ε` (集合論的)。
  - `s ∩ T_n^δ = T_n^δ \ (sᶜ ∩ T_n^δ)`、`P^n(sᶜ ∩ T_n^δ) ≤ P^n(sᶜ) ≤ ε`。

- [x] `steinOptimalBeta_log_le_of_strong_converse`: ある eventually 規模で
  ```
  -(1/n) * log (steinOptimalBeta P Q n ε) ≤ K + δ - (1/n) * log (1 - ε - η_n)
  ```
  ここで `η_n := P^n((T_n^δ)^c).toReal → 0`。`(1/n) * log (1 - ε - η_n) → 0`
  なので Tendsto/liminf/limsup に持ち上げ可能。

## Phase C — `Tendsto → K` 主定理

- [x] `stein_strong_lemma` — strong converse + 既存 achievability で sandwich を
  closed interval `[K, K]` に潰す。
  - `limsup ≤ K`: Phase B から、任意 δ > 0 で `limsup -(1/n) log β* ≤ K + δ`、
    δ → 0+ で `limsup ≤ K`。
  - `liminf ≥ K`: 既存 `stein_lemma` の前半をそのまま再利用。
  - 結合 → `Tendsto → K` (`tendsto_of_le_liminf_of_limsup_le` 形)。

## 判断ログ

書く頻度: Phase 中の方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

1. **Phase 0 経路判定 (2026-05-12)**: Pinsker (B-5 引き継ぎ) 経由ではなく LLR
   typicality 経由を採用。Pinsker は KL 値 → TV 値の翻訳でしかなく、Stein converse
   の `1/(1-ε)` 補正の原因 (DPI on Bool reduction の `Pn(s)` factor) を直接消す
   ことには寄与しない。`stein_inProbability` (WLLN on LLR) で LLR typicality
   を直接扱う方が短い。
2. **既存 `Stein.lean` を改変せず、新規 `StrongStein.lean` を並立**: 既存
   `stein_lemma` (sandwich 形) は依然 `K/(1-ε)` 限界の最良 sandwich として
   有用 (任意有限 n で成立する pointwise 形)。strict `Tendsto` 形は別
   theorem として publish した方が API として明確。
