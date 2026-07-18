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

| 指標 | 移行前 | 移行後（2026-06-08） |
|---|---|---|
| `InformationTheory/Shannon/` 直下のファイル | **205 / 233（88%）** | **40**（真の単独概念のみ） |
| `Shannon/` のサブディレクトリ | **0** | **25** |
| 1500 行超のファイル | **13**（最大 3589 行 = 上限の 2.4 倍） | **0**（2026-06-09 分割完了。最大 3589 行 = V2DeBruijnAssembly を 4 part 化） |

移行前は `Shannon/` 以外（`Probability/` `Meta/` `Polymatroid/`）だけがサブディレクトリ化され、**`Shannon/` だけが例外的にフラット集中**していた。ファイル名接頭辞が既に暗黙の階層を成していた（`EPI*` 43、`ChannelCoding*` 13、`Huffman*` 12、`AWGN*` 14、`LZ78*` 11 …）。これを下記ターゲット形に従ってサブディレクトリへ昇格済み（→「移行ステータス」）。

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

## 移行ステータス（2026-06-08 実施）

ディレクトリ再編は **完了**（全主要接頭辞クラスタ + EPI 二段ネスト + Cramer + クリーンなミニクラスタ）。各クラスタ後 `lake build InformationTheory` 0 error で検証、commit/push 済み。25 サブディレクトリ: `AEP AWGN ChannelCoding Chernoff Cramer EntropyPower EPI FisherInfo GeneralDMC Han Hoeffding Huffman HypercubeEdge IIDProductInput LZ78 MaxEntropy ParallelGaussian Pinsker RateDistortion Sanov ShannonCode SlepianWolf SMB Stationary WynerZiv`。

- **namespace は変更していない**（flat `InformationTheory.Shannon` のまま）。Lean 4 では namespace とファイルパスは独立で、namespace を変えると宣言名が全変化し term 参照まで壊れ blast radius が激増するため、**移行はファイル移動 + import パス書換のみ**。
- **完了**: ① 1500 行超 14 ファイルの分割（2026-06-09 完了。subdir + part + umbrella 方式、全 part < 1500 行、namespace 不変、各 `lake build InformationTheory` EXIT=0 で検証）。
- **後続の昇格**: `ShannonHartley*` フラットクラスタ（10 ファイル）を `Shannon/ShannonHartley/` へ昇格（2026-07-19、接頭辞を落とし `Basic`/`Operational`/`Achievability`/`Preequalizer`/`Main`/`Converse`/`ConverseCount`/`Waterfill`/`Rotation`/`ConverseFinal`）。namespace 不変・import 書換のみ・`lake build InformationTheory` EXIT=0。サブディレクトリは 26 に（`TimeBandLimiting.lean` は接頭辞非該当のためフラット維持）。
- **再分割（1500 行超の再発解消, 2026-07-19）**: ①の後に WynerZiv / TimeBandLimiting / BroadcastChannel / MultipleAccess の新規実装で 6 ファイルが再び上限超過。subdir + part + umbrella 方式で分割（`docs/large-file-split-plan.md`）: `MultipleAccess/Achievability`（→ Codebook/RandomCoding）, `TimeBandLimiting`（→ Operator/Enumeration/TraceBound/SecondMoment/Count、`section TraceBound` を二分）, `MultipleAccess/TimeSharingConverse`（→ Bridge/Assembly）, `WynerZiv/Converse`（→ Prelim/SingleLetter/Headline）, `BroadcastChannel/Achievability`（→ Setup/ErrorAnalysis/Assembly）, `WynerZiv/Achievability`（7526 行 → 8 part）。逐語移動・namespace 不変・`lake build InformationTheory` EXIT=0・headline sorryAx-free 保持。**cross-part の `private` は de-private 化**（file-scoped ゆえ; 真の cross はコンパイラの `unknown identifier` で確定し docstring 言及のみのものは private 維持）。
- **未完（別パス）**: ② 真の単独フラットファイルはフラット維持（1 ファイルのサブ化は無価値）。③ docstring/プランの旧モジュールパス prose 参照の sweep（build 非依存。ShannonHartley 昇格分は移動ファイル内の docstring を更新済、docs/ 配下の歴史的 inventory prose は line 番号ごと stale なので未実施）。

### 残作業の進め方（1500 行分割 等）

これは大規模な機械リファクタ（`git mv` + 全 `import InformationTheory.Shannon.Foo` の書換 + `InformationTheory.lean` 再登録）。指針:

- **依存グラフを先に取る**: 移動前に `scripts/dep_consumers.sh <name> --transitive`（被参照）/ `scripts/dep_graph.sh <name>`（forward）で blast radius を把握し、循環を作らない安全な順序を決める。
- **import 書換は末尾アンカー or 境界マッチ sed** で機械的に。境界に `.` を含めると base 式（`AWGN → AWGN.Basic`）が直前置換後の `AWGN.` に再マッチして二重置換するので、**境界は `([ \t]|$)`（空白か行末のみ）に限定**する。書換後 `lake build InformationTheory` で olean 更新 + 検証（dep ツールはルート olean を読むため）。末尾コメント付き import 行を見落とさないこと。
- 1500 行超ファイルの**分割**は移行と同じ PR で行うと import 書換が一度で済む。
