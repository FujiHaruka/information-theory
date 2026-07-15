"""
Independent SPECTRAL-side cross-check of WSEB single-sample atom (different discretization/conditioning
path than the sinc-side lstsq probe).

Band-limited f <-> spectrum F on [-W,W]:  f(t) = ∫_{-W}^{W} F(ξ) e^{2πiξt} dξ.
  f(0) = ∫_{-W}^{W} F(ξ) dξ  =  c·F        (c = quadrature weights)
  ∫_0^T |f(t)|² dt = F* Q F                 (Q = window-energy Gram of the exponentials)
  sup_F |f(0)|² / ∫_0^T|f|²  =  c* Q^{-1} c  =  1 / (min F*QF s.t. c·F = 1)   [complex F]
Computed stably via lstsq (min-energy spectrum with f(0)=1). Complex F upper-bounds the real-f sup;
finiteness here => real WSEB atom finite. Independent of the sinc reduction.
"""
import numpy as np

def spectral_min_energy(T, W, K, Nt, dt):
    xi = np.linspace(-W, W, K)
    dxi = (2*W)/(K-1)
    t = np.arange(dt/2, T, dt)
    # E[k, it] = e^{2πi ξ_k t} * dxi   (so f(t) = Σ_k F_k E[k,it]/... ; window energy = F* Q F)
    E = np.exp(2j*np.pi*np.outer(xi, t)) * dxi          # (K, Nt)
    # window energy quadratic form Q = E diag(dt) E^H  -> ||F^T E||^2 * dt
    # f(0) = Σ_k F_k * dxi = c·F, c = dxi * ones
    c = np.full(K, dxi)
    # min F* Q F s.t. c·F = 1. Pivot on k0 (largest |c|, all equal -> pick middle).
    p = K // 2
    others = [k for k in range(K) if k != p]
    # F_p = (1 - Σ_{others} c_k F_k)/c_p
    # f(t) = F_p E_p + Σ_others F_k E_k = E_p/c_p + Σ_others F_k (E_k - (c_k/c_p) E_p)
    b = (E[p] / c[p]) * np.sqrt(dt)                      # (Nt,) weighted
    A = ((E[others] - np.outer(c[others]/c[p], E[p])) * np.sqrt(dt)).T   # (Nt, K-1)
    d, *_ = np.linalg.lstsq(A, -b, rcond=None)
    resid = b + A @ d
    return float(np.vdot(resid, resid).real)            # min window energy

print("=== SPECTRAL-side cross-check: sup |f(0)|²/∫₀ᵀf² = 1/min_window_energy ===")
print("W=1/2 (matches sinc probe). TRUE if finite & stable under K refinement.\n")
W = 0.5
for T in [4, 8, 16]:
    print(f"--- T={T} ---")
    print(f"{'K(spec pts)':>12} {'min_win_energy':>16} {'sup=1/it':>12}")
    for K in [41, 81, 161, 321]:
        Nt = int(T/0.0005)
        r = spectral_min_energy(T, W, K, Nt, 0.0005)
        print(f"{K:>12} {r:>16.6e} {1.0/r:>12.4f}")
    print()

print("Compare to sinc-side probe (wseb_probe3): T=4 sup~76.1, T=8 sup~62.4, T=16 sup~57.5")
