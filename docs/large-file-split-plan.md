# 大ファイル分割プラン（1500 行超の解消）

`docs/rules/module-structure.md`（1 ファイル ≤ 1500 行）に反する 6 ファイルを、subdir + part + umbrella 方式で分割する。

## Context

`module-structure.md` の移行ステータスは「1500 行超 0（2026-06-09 分割完了）」と記録するが、その後 WynerZiv / TimeBandLimiting / BroadcastChannel / MultipleAccess の新規実装で再び 6 ファイルが上限超過した（`find … | xargs wc -l | awk '$1>1500'`）。

| ファイル | 行数 | private | section | 難度 |
|---|---|---|---|---|
| `Shannon/WynerZiv/Achievability.lean` | 7526 | 65 | 1 | 最難 |
| `Shannon/TimeBandLimiting.lean` | 4818 | 0 | 6 | 中 |
| `Shannon/BroadcastChannel/Achievability.lean` | 3231 | 6 | 0 | 中 |
| `Shannon/WynerZiv/Converse.lean` | 2781 | 22 | 0 | 中 |
| `Shannon/MultipleAccess/TimeSharingConverse.lean` | 2181 | 10 | 6 | 中 |
| `Shannon/MultipleAccess/Achievability.lean` | 2115 | 0 | 0 | 易（テンプレ） |

## Approach

**subdir + part + umbrella**（既存 `FisherInfo/DeBruijnAssembly` に一致）。`Foo.lean`（N 行）→ 同名サブディレクトリ `Foo/` にアスペクト別 part を置き、`Foo.lean` を part を import するだけの umbrella に変える。

- **namespace 不変**: フラット `InformationTheory.Shannon(.X)` のまま。ファイル移動 + import 書換のみ（`module-structure.md` の方針）。
- **下流無改変**: umbrella が原 module パスを保持するので、`import …Foo` する下流は変更不要。
- **preamble 複製**: 各 part の先頭に、原ファイルの `namespace` / `open` / file-level `variable` ブロックをそのまま複製する（`open`/`variable` は import では伝播しない）。
- **import は線形 DAG**: 先頭 part（base）が原 mathlib/project import を全部持ち、後続 part は「直前 part を import」だけ。umbrella は全 part を import。
- **切断点は decl 間**（`/-! -/` 見出し or `section … end` 境界）。`private` を跨ぐ切断は禁止（file-scoped なので壊れる）。跨ぐ場合は (a) その private を消費側と同じ part に置く、(b) やむを得ない共有 private は de-private 化（`InformationTheory.Shannon` に公開名が増える点を受容）。
- **各 part < 1500 行**。単一 `section` が 1500 超なら section を二分（同名 section を両 part で開き直し、同じ `variable` を再宣言）。
- **root 登録**: `InformationTheory.lean` に全 part + umbrella を追記。
- **検証**: 各 part を `lake env lean`、最後に `lake build InformationTheory` EXIT=0。移動は逐語（証明本文は 1 字も変えない）。
- **gate**: 分割後に `style-auditor` を触ったファイルに掛ける（新規 umbrella docstring 等）。honesty gate は逐語移動で honesty 不変のため原則不要（`private`→public はvisibility 変更で honesty 非関与）。
- **実行順**: 易→難。0-private の 2 本でテンプレ確立 → private ありへ。commit はファイル単位。

## 実行順と設計

### 1. MultipleAccess/Achievability.lean（2115 → 2 part）テンプレ確立
preamble = L30–40（namespace MAC + opens + variables）。0 private / 0 section。
- `Achievability/Codebook.lean` ← 本文 L42–1061（decoder / MACCode bundle / Bonferroni / corner-point / block-law channel-fold helpers）。原 import 4 本を保持。
- `Achievability/RandomCoding.lean` ← 本文 L1062–2114（per-event swaps / arithmetic / averaging / pigeonhole / `@[entry_point] mac_achievability`）。import = Codebook のみ。
- `Achievability.lean` → umbrella（両 part import + 集約 docstring）。

### 2. TimeBandLimiting.lean（4818 → 5 part）
preamble = L135–138（namespace TimeBandLimiting + `open MeasureTheory` + `open scoped ENNReal symmDiff FourierTransform`）。0 private。section 構造:
- L135–1424 top-level（`abbrev E` 他 Leg A/B: 部分空間・作用素・自己随伴/正値/縮小・境界退化）
- `section Enumeration` 1425–1692 / `NonVacuity` 1694–1882 / `Degeneracy` 1893–1952
- `section TraceBound` 1970–3936（**1966 行、二分割必須**。sub-header: 2350 R1 spectral gap / 2769 eigen-Hilbert basis / 3161 window deficit / 3483 second moment tr A²）
- `section EigenvalueCount` 3938–4560 / `section Achievability` 4562–4816

part 案（各 < 1500）:
- `Operator.lean` ← L135–1424（base, `abbrev E` 含む, 原 mathlib import 全部）
- `Enumeration.lean` ← L1425–1968（Enumeration+NonVacuity+Degeneracy）
- `TraceBound.lean` ← section TraceBound 前半（1970–~3160: TraceBound 本体 + R1 gap + eigen-basis transport）※二分の切れ目は section variable を確認して決定
- `TraceMoments.lean` ← section TraceBound 後半（~3161–3936: window deficit + tr A²）※同名 section 再宣言
- `Count.lean` ← L3938–4816（EigenvalueCount + Achievability）
- `TimeBandLimiting.lean` → umbrella

### 3–6（設計は着手時に private-crossing を `dep_consumers` で確定）
- `MultipleAccess/TimeSharingConverse.lean`（10 private, 6 section）
- `WynerZiv/Converse.lean`（22 private）
- `BroadcastChannel/Achievability.lean`（6 private）
- `WynerZiv/Achievability.lean`（65 private, 7526 行 → 最難、最後）

## 検証コマンド

```
lake env lean <part>                      # 各 part 単体
lake build InformationTheory              # 全体（root olean 更新込み）
find InformationTheory -name '*.lean' | xargs wc -l | awk '$1>1500 && $2!="total"'   # 残存超過ゼロ確認
```
