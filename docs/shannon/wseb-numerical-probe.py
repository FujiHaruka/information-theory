"""
SUPERSEDED by docs/shannon/wseb-highprec-probe.py — this script's TRUE verdict (sup ~= 76.1) is a
double-precision artifact: lstsq(rcond=None) silently discards the super-exponentially small
singular values that drive the sup up. The atom is FALSE (sup = +infinity).

WSEB single-sample gateway atom — STABLE decisive test avoiding G^{-1}.

min window energy for f(0)=1  ==  squared L2([0,T]) distance from sinc_0 to span{sinc_n : n != 0}
  = || sinc_0 - proj_{span(sinc_n, n!=0)} sinc_0 ||^2_{L2([0,T])}.
Computed via numpy.linalg.lstsq (SVD-based, robust to the prolate ill-conditioning).

WSEB TRUE  <=>  this residual stays bounded away from 0 as (N, grid) refine (sup |f(0)|^2/window = 1/residual finite).
WSEB FALSE <=>  residual -> 0 (other sincs reconstruct sinc_0 on the window; sup blows up).

Also reports as a cross-check the interior-sample and multi-sample (n>1) cases.
"""
import numpy as np

def window_residual(T, N, dt, sample_pt=0.0):
    """min_{c: c at sample=1} ∫_0^T (Σ c_n sinc(t-n))^2 dt, via lstsq.
       Here the linear constraint is f(sample_pt)=1 with f=Σ c_n sinc(·-n)."""
    t = np.arange(dt/2, T, dt)
    ns = np.arange(-N, N+1)
    Sgrid = np.sinc(t[None, :] - ns[:, None]) * np.sqrt(dt)   # (2N+1, len(t)), weighted -> ||.||^2 = ∫
    svals = np.sinc(sample_pt - ns)                            # f(sample_pt) = Σ c_n sinc(sample-n)
    # split constraint index j0 (the mode with largest |svals|) as the pivot to set = ...
    # We want min ||Sgrid^T c||^2 s.t. svals·c = 1.
    # Parametrize: pick pivot p = argmax|svals|; c_p = (1 - Σ_{n≠p} svals_n c_n)/svals_p.
    p = int(np.argmax(np.abs(svals)))
    others = [i for i in range(len(ns)) if i != p]
    # f = c_p * col_p + Σ_{others} c_n col_n  (col_n = Sgrid[n])
    # substitute c_p: f = col_p/svals_p + Σ_{others} c_n (col_n - (svals_n/svals_p) col_p)
    b = Sgrid[p] / svals[p]                                    # target (len t)
    A = (Sgrid[others] - np.outer(svals[others]/svals[p], Sgrid[p])).T   # (len t, len others)
    # min || b + A d ||^2  -> lstsq on (A, -b)
    d, res, rank, sv = np.linalg.lstsq(A, -b, rcond=None)
    resid_vec = b + A @ d
    return float(resid_vec @ resid_vec)   # = min window energy

print("=== STABLE: min window energy for f(sample)=1 (boundary sample=0) vs (N, dt) ===")
print("TRUE if it stabilizes > 0;  FALSE if -> 0.\n")
for T in [4, 8, 16]:
    print(f"--- T={T} ---")
    print(f"{'N':>4} {'dt':>8} {'min_win_energy':>16} {'sup=1/it':>12}")
    for (N, dt) in [(16,0.001),(32,0.0005),(48,0.0005),(64,0.00025),(96,0.00025),(128,0.0002)]:
        r = window_residual(T, N, dt, sample_pt=0.0)
        print(f"{N:>4} {dt:>8} {r:>16.6e} {1.0/r:>12.4f}")
    print()

print("=== cross-check: interior sample point t0=T/2 (should also be finite if boundary is) ===")
for T in [8]:
    for t0 in [0.0, 0.5, T/4, T/2]:
        rs = [window_residual(T, N, 0.0003, sample_pt=t0) for N in [32,64,96]]
        print(f"T={T} sample t0={t0:>5}:  min_win_energy over N=32,64,96 = "
              + ", ".join(f"{r:.4e}" for r in rs) + f"   (sup~{1/rs[-1]:.3f})")
