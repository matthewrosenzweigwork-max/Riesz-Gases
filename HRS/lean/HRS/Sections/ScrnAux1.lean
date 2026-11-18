import HRS.Energy.Modulated

/-!
# Packet SCRN: real-exponent helpers for the screening error terms (Proposition 6.1)

Generic facts about powers `N ^ e` of the particle number `N` (as a real), used to show that the
error terms of `O:eq:screening-bound` vanish along `ℓ_N = N^{-κ}`.

## Statement check (2026-10-17, SCRN-cmp / SCRN-stat): NO DEFECT FOUND

`screening_comparison` (Sec6.lean:111), `screening_stationary_limit` (:265); TeX `M:O:prop:screening`.
* C₀ threshold: the statement is `∃ C₀ C, 0 ≤ C₀ ∧ 0 ≤ C ∧ (F_N + o_N ≥ 0 off collisions) ∧ ∀ ...`; `C₀` is
  chosen BEFORE every particle datum and is only constrained from above-below by existence, so the proof takes
  `C₀ := C₀` of `commutator_coercivity_common_proof` (`oNΛ d s C₀ 1 N = oN d s C₀ N`).  No SPEC-C0/SPEC-C0B defect.
  The stationary statement uses `C₀` only through the comparison bound (existential), also fine.
* V regularity: `V = 0` (smooth), `IsCk 2` and `VHyp` are trivial (cf. ISSUES "G336").
* Junk values: `mesoTest` is a finite sum (compact support); `linCoord vol ψ X = √N (μ_N ψ - ∫ψ)`; laws are `P.map` of
  measurable maps (`X t` measurable by `IsStrongSolution.adapted`); `multivariateGaussian 0 (mesoCovMatrix ..)` is a genuine
  Gaussian (the matrix is PSD: `K(t,u;ξ) = e^{-a(t+u)} + S ∫_0^{t∧u} 2a e^{-a(t+u)+2as} ds`, a Gram form), so no
  `dirac` junk; `smoothDist` is a sup of a bounded family.  The constants of the covariance (`ĝ(k) = c r^{s-d}`,
  `r = 2π|k|`, `a_b = b⁻¹r² + c r^{2-q}`, `S_b = r^q/(r^q + bc)`) agree with `rieszCoeff`/`particleDrift`/`mfData`
  (`M = -I`, `invβ = β⁻¹`): `τ_N λ_{N,k} = a_{b_N}(ℓk)`, `Var η̂(k) = S_{b_N}(ℓk)` verified by hand.
* No upper bound on `ℓ` is imposed; the bound is trivial when its right side is `≥ 2` (`smoothDist ≤ 2`), so the
  proof may assume `ℓ ≤ ℓ₀`, `N^{-1/2}ℓ^{-d/2} ≤ δ`, etc.

## Chain plan (reuse in brackets; sizes S/M/L)

Probabilistic skeleton (one application of `iid_initial_sampling`, HilbertMartingale.lean, Cor. A.30):
`d3DistE(Law(∑_i N^{-1/2}(f(x_i)-m) + M_T + R), N(0, Cov_Haar(f) + ∫Σ̄)) ≤ E|R| + (1+√3)/(6√N)∫|f-m|³ + ½ E∫‖Σ-Σ̄‖_{S₁}`,
with `x_i = X^0_i` (iid Haar, `ℱ_0`-measurable), `f = (f_a^0)_a` the transported tests, `M = √N·(empirical martingale
vector)` from `several_times_covariation` (killed integrands, [A8PAux20 pattern]), `R_a = √N∫_0^{T_a} flucInteraction`,
`Σ^{ab}_r = 2β⁻¹ μ_N^r(∇f_a·∇f_b) 1_{r<T_a∧T_b}`, `Σ̄^{ab}_r = 2β⁻¹ ∫∇f_a^r·∇f_b^r dx 1_{r<T_a∧T_b}`.  Then
`smoothDist 3 ≤ (d3DistE).toReal` (CbUnitBall ⊆ D3TestClass) and the triangle inequality with
`smoothDist_gaussian_covariance` (Metrics.lean, A.31): `d₃(N(0,Q), N(0,Q')) ≤ ½‖Q-Q'‖_{S₁}`.
* (A) Fourier of the mesoscopic test (M): `ψ̂(k) = ℓ^{d/2} e^{-2πik·x₀} φ̂(ℓk)` (periodisation unfolding), rapid decay
  from `HasCompactSupport.toSchwartzMap`, weighted ℓ¹/ℓ² sums `∑_k |k|^r|ψ̂| ≤ Cℓ^{-d/2-r}` (ℓ ≤ 1).
* (B) Lattice sums (M): `ℓ^d ∑_k (1+ℓ|k|)^{-L}|k|^{-γ'} ≤ C ℓ^{d-(d-γ')}` through the product trick
  `1/|k| ≤ ∏ max(1,|k_i|)^{-1/d}` and 1-d sums `∑ max(1,|n|)^{-γ}(1+ℓ|n|)^{-a} ≤ Cℓ^{-(1-γ)}` (`γ<1`).
* (C) Riemann sum (L): `|∑_{k≠0} ℓ^d G(ℓk) - ∫G| ≤ C A ℓ` for `|G| ≤ A(1+|ξ|)^{-L}`, `|G(η)-G(ξ)| ≤ A|η-ξ|(1+|ξ|)^{-L}/|ξ|`
  on `|η-ξ| ≤ |ξ|/2` (cubes, `d ≥ 2`).  Kernel `K(t,u;b,ξ)`: derivative bounds `|∂_r K| ≤ C/r`, `|∂_b K| ≤ C`, PSD,
  `Q_N^{ab} = Re ∑_{k≠0} ℓ^d φ̂_a conj φ̂_b K(ℓk)` ⇒ `‖Q_N - mesoCovMatrix‖ ≤ C(ℓ + |b_N - b|)`; `mesoCovMatrix`,
  `mesoStatCovMatrix` PSD.
* (D) Fourier-diagonal semigroup (M): `D = mfData`, `ρ ≡ 1`: `forwardGen D 1 c k = -λ_k c k` (`coeffOf 1 = δ_0`),
  `AdjointData` (R1 if `s ≤ d-2`, else R3), `adjoint_torus_classical` + `hasDerivAt_coeff`/`coeffOf_backwardGenerator`
  ⇒ `coeffOf (f^r) k = e^{-(T-r)λ_k} ψ̂(k)`; `IsMeanFieldSolution D T 1` (`interactionPairing_withDensity_self`,
  `convGradConv 1 = 0`), `IsRegularMF 3 1 T 1`.
* (E) Norms of `f^r` (M-L): `‖∇f‖_∞, ‖∇²f‖_∞ ≤ ∑ |k|^j|f̂|`, `HasTransportBound d s (∇f^r)` (`F`-term by interpolation
  `‖w‖_{L^{2d/(d-1)}} ≤ ‖w‖_∞^{1/d}‖w‖_2^{1-1/d}`, sharp in ℓ), `λ_k ≥ c ℓ^{(q-2)_+}`; product `χ = ∇f_a·∇f_b`:
  Lipschitz `≤ Cℓ^{-d-3}`, `Ḣ^{q/2}` bound `≤ Cℓ^{-(d+q)/2-2}` (weighted Young `ℓ¹*ℓ²`).
* (F) Energy bound (M): B.15 (`b15_sde_entropy_law_free_proof`, `PathwiseUnique` from `particle_wellposed`) with
  `gibbsEntropy = H(·|dX) + β U`, `U = N F_N` (V = 0, `∫γ = 0`), initial law Haar (entropy `0`):
  `0 ≤ E[F_N(X^t)] + ... ⇒ E[F_N + o_N] ≤ o_N`, all `t ≥ 0`.
* (G) Particle assembly (L): `duality_identity_final` per test (ρ = 1, [A8PAux7 template]), the identification
  `flucInteraction D ψ X 1 = -½ commQuantity` (`interactionPairing`/`offDiagPairing`), remainder
  `E|R_a| ≤ C√N o_N ℓ^{-d/2-max(q,2)}`, covariance discrepancy
  `E∫‖Σ-Σ̄‖ ≤ C[N^{-1/d}ℓ^{-d-3+min(q,2)} + √o_N ℓ^{-(d+q)/2-2+min(q,2)}]` (coercivity test clause, Jensen),
  Lindeberg term `≤ C N^{-1/2}ℓ^{-d/2}`.
* (H) `ScrnFinal.lean`: `screening_comparison_proof`, then `screening_stationary_limit_proof` (S: dominated
  convergence for `‖mesoCov(b, u_n + t) - mesoStatCov(b, t)‖`, `e^{-2u a_b}` factor, `screening_error_tendsto`).
-/

noncomputable section

open Filter Topology

namespace HRS

/-- `N ↦ N ^ e` tends to `0` along `ℕ` for `e < 0`. -/
lemma scrn_rpow_nat_tendsto {e : ℝ} (he : e < 0) :
    Tendsto (fun N : ℕ => (N : ℝ) ^ e) atTop (𝓝 0) := by
  have h := (tendsto_rpow_neg_atTop (y := -e) (by linarith)).comp tendsto_natCast_atTop_atTop
  simpa [Function.comp_def, neg_neg] using h

/-- `N ↦ log N * N ^ e` tends to `0` along `ℕ` for `e < 0`. -/
lemma scrn_log_rpow_nat_tendsto {e : ℝ} (he : e < 0) :
    Tendsto (fun N : ℕ => Real.log N * (N : ℝ) ^ e) atTop (𝓝 0) := by
  have h := ((isLittleO_log_rpow_atTop (r := -e) (by linarith)).tendsto_div_nhds_zero).comp
    tendsto_natCast_atTop_atTop
  refine h.congr (fun N => ?_)
  simp only [Function.comp_apply]
  rw [div_eq_mul_inv, ← Real.rpow_neg (Nat.cast_nonneg N), neg_neg]

/-- `N ↦ (a + b log N) * N ^ e` tends to `0` along `ℕ` for `e < 0`. -/
lemma scrn_logpoly_nat_tendsto (a b : ℝ) {e : ℝ} (he : e < 0) :
    Tendsto (fun N : ℕ => (a + b * Real.log N) * (N : ℝ) ^ e) atTop (𝓝 0) := by
  have h := ((scrn_rpow_nat_tendsto he).const_mul a).add
    ((scrn_log_rpow_nat_tendsto he).const_mul b)
  simp only [mul_zero, add_zero] at h
  refine h.congr (fun N => ?_)
  ring

/-- Products of powers of the same positive base: `x ^ a * (x ^ b) ^ c = x ^ (a + b * c)`. -/
lemma scrn_pow_mul_pow {x : ℝ} (hx : 0 < x) (a b c : ℝ) :
    x ^ a * (x ^ b) ^ c = x ^ (a + b * c) := by
  rw [← Real.rpow_mul hx.le, ← Real.rpow_add hx]

lemma scrn_oN_nonneg {d : ℕ} {s C₀ : ℝ} (hC₀ : 0 ≤ C₀) {N : ℕ} (hN : 1 ≤ N) :
    0 ≤ oN d s C₀ N := by
  unfold oN
  have hL : (0 : ℝ) ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  refine add_nonneg (mul_nonneg hC₀ (Real.rpow_nonneg (Nat.cast_nonneg N) _)) ?_
  split_ifs
  · exact div_nonneg hL (by positivity)
  · exact le_refl _

/-- The admissible bound `o_N ≤ (C₀ + log N/(2d)) N^{s/d - 1}` (both cases of the indicator). -/
lemma scrn_oN_le {d : ℕ} {s C₀ : ℝ} (hC₀ : 0 ≤ C₀) {N : ℕ} (hN : 1 ≤ N) :
    oN d s C₀ N ≤ (C₀ + Real.log N / (2 * d)) * (N : ℝ) ^ (s / d - 1) := by
  have hL : (0 : ℝ) ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  have hL2 : (0 : ℝ) ≤ Real.log N / (2 * d) := div_nonneg hL (by positivity)
  have hP : (0 : ℝ) ≤ (N : ℝ) ^ (s / d - 1) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  unfold oN
  by_cases hs : s = 0
  · subst hs
    rw [if_pos rfl, zero_div, zero_sub, Real.rpow_neg_one]
    apply le_of_eq
    ring
  · rw [if_neg hs]
    nlinarith [mul_nonneg hL2 hP]

/-- Second error term: `√N · o_N · ℓ^c ≤ (C₀ + log N/(2d)) N^{1/2 + (s/d-1) + (-κ)c}` with `ℓ = N^{-κ}`. -/
lemma scrn_term2_le {d : ℕ} {s C₀ κ c : ℝ} (hC₀ : 0 ≤ C₀) {N : ℕ} (hN : 1 ≤ N) :
    Real.sqrt N * oN d s C₀ N * ((N : ℝ) ^ (-κ)) ^ c ≤
      (C₀ + Real.log N / (2 * d)) * (N : ℝ) ^ (1 / 2 + (s / d - 1) + (-κ) * c) := by
  have hx : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hx.le]
  have hP := scrn_oN_le (d := d) (s := s) hC₀ hN
  have hmono : (N : ℝ) ^ (1 / 2 : ℝ) * oN d s C₀ N * (N : ℝ) ^ (-κ * c) ≤
      (N : ℝ) ^ (1 / 2 : ℝ) * ((C₀ + Real.log N / (2 * d)) * (N : ℝ) ^ (s / d - 1)) *
        (N : ℝ) ^ (-κ * c) := by
    gcongr
  refine hmono.trans (le_of_eq ?_)
  rw [Real.rpow_add hx, Real.rpow_add hx]
  ring

/-- `√(1 + log-type)` bound: `√y ≤ 1 + y` for `y ≥ 0`. -/
lemma scrn_sqrt_le_one_add {y : ℝ} (hy : 0 ≤ y) : Real.sqrt y ≤ 1 + y := by
  have h0 := Real.sq_sqrt hy
  have h1 := Real.sqrt_nonneg y
  nlinarith [sq_nonneg (Real.sqrt y - 1 / 2)]

/-- Fourth error term: `√(o_N) · ℓ^c ≤ (1 + (C₀ + log N/(2d))) N^{(s/d-1)/2 + (-κ)c}`. -/
lemma scrn_term4_le {d : ℕ} {s C₀ κ c : ℝ} (hC₀ : 0 ≤ C₀) {N : ℕ} (hN : 1 ≤ N) :
    Real.sqrt (oN d s C₀ N) * ((N : ℝ) ^ (-κ)) ^ c ≤
      (1 + (C₀ + Real.log N / (2 * d))) * (N : ℝ) ^ ((s / d - 1) * (1 / 2) + (-κ) * c) := by
  have hx : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hL : (0 : ℝ) ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  have hL2 : (0 : ℝ) ≤ C₀ + Real.log N / (2 * d) :=
    add_nonneg hC₀ (div_nonneg hL (by positivity))
  have hsq : Real.sqrt (oN d s C₀ N) ≤
      Real.sqrt (C₀ + Real.log N / (2 * d)) * (N : ℝ) ^ ((s / d - 1) * (1 / 2)) := by
    have h1 := Real.sqrt_le_sqrt (scrn_oN_le (d := d) (s := s) hC₀ hN)
    rw [Real.sqrt_mul hL2, Real.sqrt_eq_rpow ((N : ℝ) ^ (s / d - 1)), ← Real.rpow_mul hx.le] at h1
    exact h1
  have hX : ((N : ℝ) ^ (-κ)) ^ c = (N : ℝ) ^ (-κ * c) := by rw [Real.rpow_mul hx.le]
  calc Real.sqrt (oN d s C₀ N) * ((N : ℝ) ^ (-κ)) ^ c
      ≤ (Real.sqrt (C₀ + Real.log N / (2 * d)) * (N : ℝ) ^ ((s / d - 1) * (1 / 2))) *
          ((N : ℝ) ^ (-κ)) ^ c := mul_le_mul_of_nonneg_right hsq (by positivity)
    _ ≤ ((1 + (C₀ + Real.log N / (2 * d))) * (N : ℝ) ^ ((s / d - 1) * (1 / 2))) *
          ((N : ℝ) ^ (-κ)) ^ c := by
        gcongr
        exact scrn_sqrt_le_one_add hL2
    _ = (1 + (C₀ + Real.log N / (2 * d))) * (N : ℝ) ^ ((s / d - 1) * (1 / 2) + (-κ) * c) := by
        rw [hX, Real.rpow_add hx]
        ring

end HRS
