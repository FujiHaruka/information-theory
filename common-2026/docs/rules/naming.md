# 命名規約

Mathlib 命名規約（<https://leanprover-community.github.io/contribute/naming.html>）から本プロジェクトに適用する分。スタイルは [`lean-style.md`](lean-style.md)。

本プロジェクトの実態は既にこの規約に沿っている（例: `exp_decay_N_of_pos` の `_of_`、`DotEq` の UpperCamelCase、`entropyPowerExt_add_ge_unconditional`）。

## 大文字小文字

| 対象 | 規約 | 例 |
|---|---|---|
| Prop / Type（inductive・structure・class） | `UpperCamelCase` | `DotEq`, `IsFiniteMeasure` |
| 定理・証明（`Prop` の項） | `snake_case` | `add_comm`, `exp_decay_N_of_pos` |
| 関数 | 戻り値の型の規約に従う | 型を返す関数は `UpperCamelCase` |
| その他の項 | `lowerCamelCase` | `differentialEntropy` |

- `snake_case` 文脈に現れる `UpperCamelCase` は `lowerCamelCase` に倒す。
- 頭字語はひとかたまりとして文脈の規則に従う。
- **識別子は英語・米綴り**（`factorization`、`factorisation` ではない）。docstring / コメントの日本語散文には適用しない。

## 定理名の組み立て

定理名は **結論を述べ、仮定を `of` で区切る**。

- パターン: `conclusion_of_hypothesis1_of_hypothesis2`
- 仮定は **出現順**（逆順にしない）。
- 例: `A → B → C` は `C_of_A_of_B`。

### 記号 → 語の対応

**論理**

| 記号 | 語 |
|---|---|
| `∨` | `or` |
| `∧` | `and` |
| `→` | `of` / `imp` |
| `↔` | `iff` |
| `¬` | `not` |
| `∃` | `exists` / `bex` |
| `∀` | `forall` / `ball` |

**集合**

| 記号 | 語 | | 記号 | 語 |
|---|---|---|---|---|
| `∈` | `mem` | | `∪` | `union` |
| `∉` | `notMem` | | `∩` | `inter` |
| `ᶜ` | `compl` | | `\` | `sdiff` |

**代数**

| 記号 | 語 |
|---|---|
| `+` | `add` |
| `-` | `neg`（単項） / `sub`（二項） |
| `*` | `mul` |
| `/` | `div` |
| `^` | `pow` |

**順序**

- `<` / `≤` = `lt` / `le`。引数が標準順と逆 / 他の関係の順に合わせる / 第 2 引数の方が「変化しやすい」ときは `gt` / `ge`。

## dot 記法（名前空間）

- intro / elim: `And.intro`, `Or.elim`, `Eq.refl`
- 射影: `Eq.symm`, `Eq.trans`
- 構造操作: `LE.trans`, `LT.trans_le`

## 構造補題の命名

- **外延性**: `(∀ x, f x = g x) → f = g` は `f_ext` / `.ext`（`@[ext]` 付き）、双方向は `.ext_iff`。
- **単射性**: `Function.Injective f` は `f_injective`、双方向 `f x = f y ↔ f x = f y` は `f_inj`、左右変種は `sub_right_inj` 型。
- **帰納/再帰**:

| motive | value 先 | constructions 先 |
|---|---|---|
| `Prop` | `T.induction_on` | `T.induction` |
| `Sort u` / `Type u` | `T.recOn` | `T.rec` |

- **述語を接尾辞に**: `_injective` `_surjective` `_bijective` / `_monotone` `_antitone` `_strictMono` `_strictAnti` / 二項演算の向きは `_left` `_right`。

## よくあるパターン

| パターン | 例 |
|---|---|
| 略語 | `pos` `neg` `nonpos` `nonneg`（`zero_lt` `lt_zero` ではなく） |
| 左右変種 | `add_le_add_left`, `le_of_mul_le_mul_right` |
| 公理的性質 | `refl` `symm` `trans` `antisymm` `assoc` `comm` |

- **強制型変換**は元の関数名に従う（`Subtype.val`, `ENNReal.ofNNReal`）。
- 曖昧でなければ略記可（`neg_neg` で `¬¬a = a`）。
- 名前空間の中では曖昧でない限り名前空間名を補題名から省く。
