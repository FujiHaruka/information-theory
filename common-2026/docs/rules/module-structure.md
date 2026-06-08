# モジュール分割・ディレクトリ構造規約

Mathlib のファイル / ディレクトリ組織化規約から本プロジェクトに適用する分。スタイルは [`lean-style.md`](lean-style.md)、import の方針は `CLAUDE.md` Import Policy。

Mathlib にはこの主題の単一公式ページは無く、規約の実体は **linter**（`DirectoryDependency` / `MinImports` / `longFile`）と **実ディレクトリ構成の慣習**にある。本ファイルはそれを言語化する。

## 原則（Mathlib 由来）

### 1. ディレクトリ = 主題領域。階層はディレクトリで表す

- ディレクトリは 1 つのコヒーレントな主題に対応し、サブ主題で**ネスト**する。
- **長い複合ファイル名に階層を埋め込まない**。`FooBarBazQux.lean` ではなく `Foo/Bar/BazQux.lean`。
- 実例: `Mathlib/Analysis/SpecialFunctions/Log/` は `Base` / `Basic` / `Deriv` / `Monotone` / `NegMulLog` / `PosLog` / `InvLog` / … とアスペクト別ファイルに分かれる。「Log の微分」は `Log/Deriv.lean` であって `LogDeriv.lean` ではない。

### 2. ファイル名の役割（`Defs` / `Basic` / アスペクト別）

Mathlib 全体で `Defs.lean` 214 / `Basic.lean` 727 ディレクトリという普及度。

- **`Defs.lean`**: 定義だけ。import を最小に保ち、import DAG の**最下層**に置く。
- **`Basic.lean`**: その定義への基本 API（基礎補題・instance）。
- **アスペクト別ファイル**: `Deriv.lean` / `Monotone.lean` / `Lemmas.lean` / `<具体トピック>.lean` のように、1 ファイル 1 側面。

### 3. 1 ファイル = 1 コヒーレントな概念

- **1 ファイル 1500 行以内**（`longFile` linter）。超えたら分割。
- 行数未満でも**関心が混ざったら分割**する（定義と重い証明、独立した 2 トピック等）。

### 4. import は DAG。循環禁止

- Lean のモジュール import は**循環不可**（規約ではなく言語上のハード制約）。新ファイルの配置はこの DAG を意識して決める。
- **import を最小化**する（`MinImports` linter）。使わないものを import しない。`Defs` を低層・高度な内容を高層に置くことで、下流が重い依存を引かずに済む。
- import の方針（`import Mathlib` 禁止・必要モジュールのみ・`InformationTheory.lean` への登録）は `CLAUDE.md` Import Policy が SoT。

### 5. ディレクトリ間の依存層を宣言する（modularity）

- `DirectoryDependency` linter の発想: 「ディレクトリ A は B から import しない」と宣言してモジュール性を上げる。
- 本プロジェクトでは linter は無いが、**ディレクトリ間の依存方向を一方向に保つ**設計指針として採用する（例: `Shannon/Core/` は `Shannon/EPI/` を import しない）。

### 6. ルートモジュールが全 re-export

- `InformationTheory.lean` が全ファイルを import（Mathlib の `Mathlib.lean` に相当）。新ファイル追加時に登録（`CLAUDE.md`）。

## 本リポジトリの現状診断

| 指標 | 値 |
|---|---|
| `InformationTheory/Shannon/` 直下のファイル | **205 / 233（88%）** |
| `Shannon/` のサブディレクトリ | **0** |
| 1500 行超のファイル | **13**（最大 3589 行 = 上限の 2.4 倍） |
| 階層が複合ファイル名に埋め込まれた例 | `EPIConvDensityGaussianGateway`, `EPIInfiniteVarianceTruncation`, `ChannelCodingConverseGeneralStrong` … |

`Shannon/` 以外（`Probability/` `Meta/` `Polymatroid/`）はサブディレクトリ化されており、**`Shannon/` だけが例外的にフラット集中**している。ファイル名の接頭辞が既に暗黙の階層を成している（`EPI*` 40+、`ChannelCoding*` 13、`Huffman*` 12、`Fisher*` 11、`Rate*` 9 …）。

## 適用 / ターゲット形

ファイル名の接頭辞クラスタを、そのまま `Shannon/<Topic>/` サブディレクトリに昇格し、**冗長な接頭辞をファイル名から落とす**（ディレクトリが担う）。クラスタが大きい `EPI` は二段ネスト。

| 現状（フラット） | ターゲット |
|---|---|
| `EPIStamDischarge.lean` | `Shannon/EPI/Stam/Discharge.lean` |
| `EPIConvDensityRegular.lean` | `Shannon/EPI/Conv/DensityRegular.lean` |
| `EPICase1RatioLimit.lean` | `Shannon/EPI/Case1/RatioLimit.lean` |
| `EPIUncondDispatch.lean` | `Shannon/EPI/Unconditional/Dispatch.lean` |
| `ChannelCodingConverseGeneral.lean` | `Shannon/ChannelCoding/ConverseGeneral.lean` |
| `HuffmanOptimality.lean` | `Shannon/Huffman/Optimality.lean` |
| `FisherInfoV2DeBruijnAssembly.lean`（3589 行） | `Shannon/FisherInfo/` 配下に分割 |
| `RateDistortion…` | `Shannon/RateDistortion/…` |

トピック候補（接頭辞クラスタより）: `EPI/`（Stam / Conv / Case1 / Unconditional / Blachman / Vitali / G2 / InfiniteVariance）, `ChannelCoding/`, `Huffman/`, `FisherInfo/`, `RateDistortion/`, `SlepianWolf/`, `Wyner/`, `Hoeffding/`, `Sanov/`, `LZ78/`, `Han/`, `MethodOfTypes/`, `AWGN/`, `Gaussian/`。各トピック内は `Defs` / `Basic` / アスペクト別に整える。1500 行超 13 ファイルは移行時に分割。

## 移行の進め方（別タスク）

これは大規模な機械リファクタ（`git mv` + 全 `import InformationTheory.Shannon.Foo` の書換 + `InformationTheory.lean` 再登録 + namespace 整合）。本ファイルは**規約とターゲット形を定める**もので、移行自体は段階計画を立てて別タスクで行う。指針:

- **依存グラフを先に取る**: 移動前に `scripts/dep_consumers.sh <name> --transitive`（被参照）/ `scripts/dep_graph.sh <name>`（forward）で blast radius を把握し、循環を作らない安全な順序を決める。
- **トピック単位で 1 クラスタずつ**移行し、各クラスタ後に `lake build InformationTheory` で olean を更新（dep ツールはルート olean を読むため）。
- **接頭辞を落とす**リネームと**ディレクトリ移動**は同時に行う（`EPIStamDischarge` → `EPI/Stam/Discharge`）。
- 1500 行超ファイルの**分割**は移行と同じ PR で行うと import 書換が一度で済む。
