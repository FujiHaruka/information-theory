-- This module serves as the root of the `Common2026` library.
-- Import modules here that should be built as part of `lake build`.
-- 入試系 (Common2026/Exam/) は完成済みのため列挙から外している。
-- 個別検証は `lake env lean Common2026/Exam/...` または `lake build Common2026.Exam.<...>` で行う。

-- Fano 不等式
import Common2026.Fano
import Common2026.Fano.Entropy
import Common2026.Fano.BinaryJensen
import Common2026.Fano.CondEntropy
import Common2026.Fano.Core
import Common2026.Fano.DPI
import Common2026.Fano.Measure
-- Shannon converse (Phase 4)
import Common2026.Shannon.MutualInfo
import Common2026.Shannon.DPI
import Common2026.Shannon.Bridge
import Common2026.Shannon.CondMutualInfo
import Common2026.Shannon.Converse
import Common2026.Shannon.Entropy
import Common2026.Shannon.SlepianWolf
import Common2026.Shannon.Pi
import Common2026.Shannon.Han
import Common2026.Shannon.HanD
import Common2026.Shannon.HanDAverage
import Common2026.Shannon.HanDShearer
import Common2026.Shannon.LoomisWhitney
import Common2026.Polymatroid.Basic
import Common2026.Shannon.Polymatroid
import Common2026.Shannon.AEP
import Common2026.Shannon.Stein
import Common2026.Shannon.MaxEntropy
import Common2026.Shannon.Pinsker
