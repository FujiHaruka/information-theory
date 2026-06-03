# Pi 値 measurable 構造 plumbing 切り出し判断

着手日: 2026-05-10
切り出し先: `InformationTheory/Shannon/Pi.lean`
背景: `docs/moonshot-seeds.md` 横断観察 — 5 本のムーンショット (Loomis–Whitney /
Slepian–Wolf / AEP / Stein / Polymatroid) 全てで Pi 値 RV の reshape plumbing が
再利用される。`Han.lean` / `HanD.lean` の中で散発的に育っているものを上流に上げる。

## 候補ごとの判断 (move / keep)

| 候補 | 場所 | 用途 | 判断 | 理由 |
|---|---|---|---|---|
| `entropy_measurableEquiv_comp` | `Han.lean:52-77` | `entropy μ (e ∘ Xs) = entropy μ Xs` (RV を `MeasurableEquiv` で押し出しても entropy 不変) | **move** | Han.lean 5 箇所 + HanD.lean 4 箇所で利用、本体に Han 固有要素なし、ムーンショット 5 本全てが `Fin n → α` reshape で同じ補題を呼ぶ |
| `condEntropy_measurableEquiv_comp` | `Han.lean:82-108` | conditioner 側を `MeasurableEquiv` で押し出しても condEntropy 不変 | **move** | HanD.lean 2 箇所で利用、Slepian–Wolf / AEP の condEntropy reshape で必須 |
| `MeasurableEquiv.piCongrLeft` 系 | Mathlib | 索引同型 lift | **keep (move 対象外)** | Mathlib 提供 API。プロジェクト側で再定義していない |
| `MeasurableEquiv.sumPiEquivProdPi` | Mathlib | sum 索引 → product 分解 | **keep (move 対象外)** | 同上 |
| `MeasurableEquiv.funUnique` | Mathlib | `(Unit → α) ≃ᵐ α` | **keep (move 対象外)** | 同上 |
| `exceptIdxEquiv` / `fullIdxEquiv` / `exceptSplitMEquiv` / `piExceptMEquiv` / `fullSplitMEquiv` | `Han.lean:209-285` (private) | `Fin n` の特定 index `i` を抜く形での Pi 分解 | **keep** | Han.lean 内 `han_single_bound` 1 箇所のみで使用、`Fin n` + 「特定 1 点 `i` を抜く」という Han 固有の構造 |
| `subsetIdxEquiv` / `subsetSplitMEquiv` / `subsetSplitMEquiv_apply` | `HanD.lean:46-112` (private) | `T₁ ⊆ T₂` の Pi 分解 | **keep** | HanD.lean 内 `condEntropy_subset_anti` 1 箇所のみで使用、Finset 包含構造に特化 |

## 切り出し方針

- `InformationTheory/Shannon/Pi.lean` を新規作成、import 元は `InformationTheory.Shannon.Entropy`
  のみ (chain rule `entropy_pair_eq_entropy_add_condEntropy` が
  `condEntropy_measurableEquiv_comp` の証明に必要なため)。
- namespace は元と同じ `InformationTheory.Shannon` を維持。
- `Han.lean` から該当 2 補題を削除し、`import InformationTheory.Shannon.Pi` を追加。
- `InformationTheory.lean` の Shannon ブロック先頭付近に `import InformationTheory.Shannon.Pi`
  を追加 (依存順は `Entropy → Pi → Han → HanD`)。

## 切り出さない理由 (補足)

- file-level の `private def` 群 (`exceptIdxEquiv` / `subsetIdxEquiv` 等) は
  CLAUDE.md にあるとおり file-scoped private なので、Pi.lean に持ち上げると
  自動的に public 化する。1 ファイルでしか使っていないものを public 化するのは
  「再利用」の用件を満たさない上に namespace 汚染になる。再利用が他のシード
  (例: Slepian–Wolf で対称差を使う場合) で発生したら、その時点で 1 つだけ
  上げる方針。
