# Type-class size lower bound (E-2) ムーンショット計画 🌙

> 実態整合 (2026-05-20): DONE-UNCOND — `typeClassByCount_card_ge_entropy` (`InformationTheory/Shannon/TypeClassLowerBound.lean:139`、`(c)(hc_sum : Σ c = n) : ((n+1)^|α|)⁻¹ · exp(n · entropyByCount c n) ≤ |T_c|`) を 0 sorry で証明、`entropyByCount` `:38` + bridge identity `pow_div_prod_pow_eq_exp_n_entropyByCount` 経由で既存 `typeClassByCount_card_ge` を rewrite。pass-through / `Prop := True` 不在。

> **シード由来**: `docs/moonshot-seeds.md` §E.E-2 (2026-05-13 起草)
> Cover-Thomas 11.1.3 size lower bound — `|T(P)| ≥ (n+1)^{-|α|} · exp(n·H(P))`。
> Sanov LDP equality 形 (`SanovLDPEquality.lean` 1394 行) を Stein 経由ではなく
> **直接 multinomial 経由**で出すための独立代替路、横断 utility。

## 進捗

- [x] Phase 0 — 起草: 既存 `typeClassByCount_card_ge` (生形) の確認 ✅
- [x] Phase 1 — `entropyByCount` 定義 + bridge identity ✅
- [x] Phase 2 — entropy 形 main theorem ✅
- [x] Phase 3 — InformationTheory.lean 登録 + seeds.md 更新 ✅

## ゴール / Approach

**最終目標** (Cover-Thomas Theorem 11.1.3, size lower bound):
任意 count vector `c : α → ℕ` で `∑ c = n` のとき、
`(n+1)^{-|α|} · exp(n · H(c/n)) ≤ |T(c)|`。

**戦略**: 既存 `SanovLDPEquality.lean:705` `typeClassByCount_card_ge` が
**生形** `(n+1)^{-|α|} · n^n / ∏ c(a)^{c(a)} ≤ |T_c|` で publish 済み。
本 plan は bridge identity を加えるだけで entropy 形を出す:
```
n^n / ∏ c(a)^{c(a)} = exp(n · H(c/n))
```
(`H(c/n) := -∑ (c(a)/n) · log(c(a)/n)`)

### Approach

1. **新規 file** `InformationTheory/Shannon/TypeClassLowerBound.lean` を作成 (`SanovLDPEquality`
   1394 行に追加でなく分離 — downstream import を軽くする)。
2. **`entropyByCount` 定義**: `klDivIndex` の `Q = uniformOn` 特殊化ではなく直接定義
   (`klDivIndex` は asymmetric で uniform 代入時 plumbing 重い、独立定義の方が短い)。
3. **Bridge identity** `pow_div_prod_pow_eq_exp_n_entropyByCount`: per-atom `c·log(c/n) = c·log c - c·log n` (`c = 0` は `log 0 = 0` 規約で吸収) + `Real.log_prod` + `Real.exp_log`。
4. **Main theorem** `typeClassByCount_card_ge_entropy`: bridge を `typeClassByCount_card_ge`
   の LHS に `rw` するだけで取得。

## Phase 0 — 既存資産の棚卸し ✅

| 補題 | ファイル | 形 |
|------|---------|-----|
| `typeClassByCount_card_ge` | `SanovLDPEquality.lean:705` | `(n+1)^{-|α|} · n^n / ∏ c^c ≤ |T_c|` |
| `typeClassByCount_Qn_ge` | `SanovLDPEquality.lean:918` | `(n+1)^{-|α|} · exp(-n·klDivIndex) ≤ Q^n(T_c)` |
| `klDivIndex` | `SanovLDP.lean:97` | `∑ (c/n) · (log(c/n) - log Q.real{a})` (asymmetric) |

`typeClassByCount_Qn_ge` は **measure-valued** lower bound (Q^n 用)、E-2 は
**size-valued** lower bound (|T| 用) で別物。`typeClassByCount_card_ge` の entropy 形
書き直しが本 plan 範囲。

## Phase 1 — `entropyByCount` 定義 + bridge identity ✅

`entropyByCount c n := -∑ a, ((c a : ℝ)/n) · Real.log ((c a : ℝ)/n)` を新規定義。

Bridge identity の proof outline:
- `n = 0`: 両辺 `1` (`c = 0` 全部 → product = 1, entropy = 0, exp 0 = 1)
- `n > 0`: take log of both sides → `n·log n - ∑ c·log c = n · entropyByCount c n`
  - `Real.log_div`, `Real.log_pow`, `Real.log_prod` (per-atom `c^c ≠ 0` proof)
  - 内部 identity `c · log(c/n) = c · log c - c · log n` を per-atom 分岐
    (`Nat.eq_zero_or_pos`: `c = 0` 側は両辺 0、`c > 0` 側は `Real.log_div` 標準)
  - `∑ c · log n = n · log n` via `∑ c = n` (cast 経由)

実装: `InformationTheory/Shannon/TypeClassLowerBound.lean` (181 行)。

## Phase 2 — entropy 形 main theorem ✅

```lean
theorem typeClassByCount_card_ge_entropy
    {n : ℕ} (c : α → ℕ) (hc_sum : (∑ a, c a) = n) :
    (((n : ℝ) + 1) ^ (Fintype.card α : ℕ))⁻¹
        * Real.exp ((n : ℝ) * entropyByCount c n)
      ≤ ((typeClassByCount (α := α) (n := n) c).toFinite.toFinset.card : ℝ) := by
  have h_raw := typeClassByCount_card_ge (α := α) c hc_sum
  rwa [pow_div_prod_pow_eq_exp_n_entropyByCount c hc_sum] at h_raw
```

3 行で main theorem 完成 (bridge identity が effective import で消す)。

## Phase 3 — 登録 + seeds.md 更新 ✅

- `InformationTheory.lean` に `import InformationTheory.Shannon.TypeClassLowerBound` 追加。
- `docs/moonshot-seeds.md` E-2 行を ✅ + plan pointer に更新。

## 判断ログ

1. **新規 file vs `SanovLDPEquality` 追記**: 既存 `SanovLDPEquality.lean` (1394 行) は
   Stein 経路の LDP equality 形が主で、E-2 (size 下界) は scope 別。独立 file の方が
   downstream (E-1 channel coding strong converse / E-5 Slepian–Wolf achievability) からの
   import が軽く、`SanovLDPEquality` の Stein dependency も連動しない。

2. **`entropyByCount` 直接定義 vs `klDivIndex` 特殊化**: `klDivIndex c n Q := ∑ (c/n)·(log(c/n) - log Q{a})` は asymmetric (`Q` を含む)。`Q = uniformOn univ` 代入時、`Q.real {a} = 1/|α|` の plumbing (`Measure.real`, `Measure.uniformOn` API) が 30-50 行追加。
   直接定義で 4 行。後者を採用。

3. **`Real.log 0 = 0` 規約による support 制限不要**: per-atom `c · log(c/n) = c · log c - c · log n`
   の identity が `c = 0` 側で両辺 0 に縮退するため、`hpos` 系の full support 仮定 不要。
   この点で D-3 (`hpos` が本質的) と対照的。

## 横断観察

- **E-1 / E-5 への利用余地**: E-1 (channel coding strong converse) を strong typicality
  (E-7) 経路ではなく **direct multinomial** 経路で書く場合、`typeClassByCount_card_ge_entropy`
  が size 下界 `|T(P)| ≳ exp(n·H(P))` を直接提供。E-5 (Slepian–Wolf achievability) でも
  joint type-class の size sandwich (E-2 + 既存 size upper bound) が effective。
- **`SanovLDPEquality` の Stein 依存性を切断する独立代替路**: `typeClassByCount_Qn_ge`
  (Q-measure 下界) は `typeClassByCount_card_ge` (size 下界) + atom-wise `∏ Q(a)^c(a)` 引き
  で得られる。E-2 (size 下界) を独立に書いておくと、Sanov LDP equality を Stein 経由でなく
  直接 multinomial 経由で組み直す道が開く (将来の整理 candidate)。
