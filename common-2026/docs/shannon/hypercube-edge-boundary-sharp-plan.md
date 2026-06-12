# Hypercube edge-boundary entropy-sharp (B-2'') ムーンショット計画

**Status**: CLOSED ✅ — entropy-sharp 形 edge isoperimetric `|A|·(n − log₂|A|) ≤ |∂_e A|` (`edgeBoundary_entropy_sharp`) を条件付きエントロピー bridge 経由で genuine publish (pass-through なし)。

**SoT**: `docs/textbook-roadmap.md` Ch.17 (hypercube) + `docs/shannon/ch17-inequalities-status.md`。詳細履歴は git。

## 要点 (再利用可能)
- Cover-Thomas / Madiman 流の conditional-entropy bridge: `uniformOn A` 上で `H(X_i | X_{≠i})` を fibre size 1/2 の point-wise 計算で取り、chain rule + "conditioning reduces entropy" の 2 段で `Σ_i H(X_i|X_{≠i}) ≤ H(X) = log|A|`。
- 既存 counting identity `edgeBoundary_count_eq` (`Σ_i 2|π_{≠i}(A)| = n|A| + |∂_e A|`) を bridge に再利用。B-2' (AM-GM 形) の file は touch せず新規 file 並立 publish (依存表面を保護)。
- 単位は internal nats (`Real.negMulLog` = 自然対数)、statement は `Real.logb 2`、bridge は `logb` 定義で処理。
- 条件付け index reshape は `Fin i.val ↪ univ.filter (·<i) ↪ univ.erase i ↪ {j // j≠i}` の 3 段 (`piCongrLeft` + HanD の `condEntropy` reshape テンプレ) が proof の半分。
- `n = 0` / `|A| = 1` は両辺 0 で early return。
