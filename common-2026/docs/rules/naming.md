# 命名規約

Mathlib 命名規約（<https://leanprover-community.github.io/contribute/naming.html>）から本プロジェクトに適用する分。スタイルは [`lean-style.md`](lean-style.md)。

## 本リポジトリの適合状況（検証済）

定理・補題 1823 件を調べた結果、**基本文法は広く沿っているが、証明ステージング由来の命名層は Mathlib 外**。

- **沿っている**: snake_case 定理 / UpperCamelCase 型 / dot 記法（`HuffmanGrouping.nodup`）。`_of_` での仮定後置が **218 件**（`fano_inequality_of_le_qaryEntropy`, `condE_XY_zero_of_deterministic` など教科書通り）。演算語の転写（`add`/`mul`/`le`/`eq`）。
- **沿っていない（Mathlib に無い proof-staging 語彙）**: `Step`(18) / `Partial`(11) / `Bridge`(9) / `unconditional`(6) / `Full`(5) / `Discharge` / `Witness` 等、計 ~50 件超。うち `unconditional` / `Full` / `discharged` は CLAUDE.md honesty 系の **name laundering 監視語**と重なる（証明が真に無条件なら descriptive だが Mathlib 語彙ではない）。軽微な逸脱として `AWGNJointlyTypicalSet_zero` 式の **UpperCamelCase 接頭辞を `_` 直結**（Mathlib なら `.zero`）、末尾 `_`、`when_eq` 等の非標準接続詞。

→ 新規命名は下記の Mathlib ルールに寄せ、staging 語彙は最終 publish 名から落とす（distinguish が要るなら `_of_<hyp>` 形で条件版を分ける）。既存の一括リネームは別タスク。

## 大文字小文字

| 対象 | 規約 | 例 |
|---|---|---|
| Prop / Type（inductive・structure・class） | `UpperCamelCase` | `DotEq`, `IsFiniteMeasure` |
| 定理・証明（`Prop` の項） | `snake_case` | `add_comm`, `exp_decay_N_of_pos` |
| 関数 | 戻り値の型の規約に従う | 型を返す関数は `UpperCamelCase` |
| その他の項 | `lowerCamelCase` | `differentialEntropy` |

- `snake_case` 文脈に現れる `UpperCamelCase` は `lowerCamelCase` に倒す。
- 頭字語はひとかたまりとして文脈の規則に従う。
- **識別子・散文ともに英語・米綴り**（`factorization`、`factorisation` ではない）。docstring / コメントの散文も英語に統一する（2026-06-13 方針転換 → [`docstrings.md`](docstrings.md)）。

## 定理名の組み立て（最重要）

定理名は **言明そのものの転写**。各部分項の**主要シンボルを左から右へ**読んで語に直し、`_` で繋ぐ。多くの場合は**結論だけを記述**すれば足りる。

### 1. 結論の転写（等式・演算）

主要シンボルを左→右に並べる。式の左辺（複雑な側）を読むのが基本。

| 名前 | 言明 |
|---|---|
| `mul_comm` | 乗法の可換性 |
| `add_assoc` | 加法の結合律 |
| `mul_zero` | `a * 0 = 0` |
| `mul_one` | `a * 1 = a` |
| `neg_neg` | `- -a = a`（二重否定） |
| `succ_ne_zero` | `succ n ≠ 0` |

接頭辞だけで意味が通るなら**短くしてよい**（`If only a prefix … is enough … the name may be made even shorter`）。

### 2. 仮定は `of` で後置（出現順）

結論を述べた後、仮定を `of` で区切って**出現順**に並べる（逆順にしない）。`A → B → C` は `C_of_A_of_B`。

| 名前 | 言明 |
|---|---|
| `lt_of_succ_le` | `succ n ≤ m → n < m` |
| `lt_of_le_of_ne` | `a ≤ b → a ≠ b → a < b` |
| `le_of_mul_le_mul_left` | 左からの乗法 `≤` から `≤` を得る |

### 3. 接続詞での結合 `_iff_` / `_eq_`

`↔` / `=` の両辺をそれぞれ名づけて繋ぐ。

| 名前 | 言明 |
|---|---|
| `le_iff_lt_or_eq` | `a ≤ b ↔ a < b ∨ a = b` |

- `_iff_`: 双条件の両辺。
- `_eq_`: 等式で両辺を明示的に名づけたいとき（単純な等式は左辺パターンだけで足りることが多い → 上の `mul_zero` 等）。

### 4. 左右変種 `_left` / `_right`

二項演算のどちら側に作用するかを接尾辞で区別。

| 名前 | 言明 |
|---|---|
| `add_le_add_left` | `b ≤ c → a + b ≤ a + c`（左に加える） |
| `add_le_add_right` | `b ≤ c → b + a ≤ c + a`（右に加える） |

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
| 公理的性質 | `refl` `symm` `trans` `antisymm` `assoc` `comm` |

- **強制型変換**は元の関数名に従う（`Subtype.val`, `ENNReal.ofNNReal`）。
- 曖昧でなければ略記可（`neg_neg` で `¬¬a = a`）。
- 名前空間の中では曖昧でない限り名前空間名を補題名から省く。
