import HRS.MS.PoisLipAux1

/-!
# LC-U (part 1): penalised maximum principle with the time derivative on `(0,T]` only, and the
one-point second-order test

* `lu_penalized_max_Ioc`: a copy of `HRS.MS.PoisMax.pm_penalized_max` in which the hypothesis `hder`
  (one-sided time derivative of `G` within `[0,T]`) is only required for `t ∈ (0,T]`; the proof uses the
  derivative only at the time `t0 > 0` of the penalised maximum.  Statement otherwise unchanged.
* `lu_second_nonpos`, `lu_laplacian_nonpos`: at a local maximum `z` of `u ∈ C²(ℝ^d)`, every second
  directional derivative is `≤ 0`, hence `Δu(z) ≤ 0` (restriction to lines and the one-variable test
  `PoissonSpike.localMax_second`).
* `lu_max_point`: at a global maximum `z` of `a(·) - κ(1+‖·‖²)` one has `∇a(z) = 2κ z` and
  `Δa(z) ≤ 2κ d`.
-/

open Filter Topology Set
open scoped RealInnerProductSpace

namespace HRS.MS.Lc

open HRS HRS.MS.PoissonSpike HRS.MS.PoisLip HRS.MS.PoisMax

/-- Penalised maximum principle (Lyapunov penalisation on `[0,T] × E`), variant of `pm_penalized_max`
with the one-sided time derivative required only on `(0,T]`.  If `G ≤ 0` at time `0`,
`G` has sub-quadratic growth, and at every spatial maximum (at a time in `(0,T]`) of the penalised
function `G t - ε(1+‖z‖²)e^{lam t}` with positive value the time derivative is `< ε lam (1+‖z‖²)e^{lam t}`
(the differential inequality fails), then `G ≤ 0` on `[0,T] × E`. -/
theorem lu_penalized_max_Ioc {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
    (G Gt : ℝ → E → ℝ) (T : ℝ)
    (hcont : ContinuousOn (fun p : ℝ × E => G p.1 p.2) (Icc 0 T ×ˢ univ))
    (hder : ∀ t ∈ Ioc 0 T, ∀ z, HasDerivWithinAt (fun s => G s z) (Gt t z) (Icc 0 T) t)
    (h0 : ∀ z, G 0 z ≤ 0)
    (hgrow : ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, ∀ t ∈ Icc 0 T, ∀ z, G t z ≤ C + δ * ‖z‖ ^ 2)
    (hfail : ∃ lam : ℝ, ∀ ε : ℝ, 0 < ε → ∀ t ∈ Ioc 0 T, ∀ z,
        0 < G t z - ε * (1 + ‖z‖ ^ 2) * Real.exp (lam * t) →
        (∀ z', G t z' - ε * (1 + ‖z'‖ ^ 2) * Real.exp (lam * t) ≤
          G t z - ε * (1 + ‖z‖ ^ 2) * Real.exp (lam * t)) →
        Gt t z < ε * lam * (1 + ‖z‖ ^ 2) * Real.exp (lam * t)) :
    ∀ t ∈ Icc 0 T, ∀ z, G t z ≤ 0 := by
  obtain ⟨lam, hlam⟩ := hfail
  by_contra hcon
  push Not at hcon
  obtain ⟨t1, ht1, z1, hz1⟩ := hcon
  set g := G t1 z1 with hg
  have hT : 0 ≤ T := ht1.1.trans ht1.2
  -- the penalty
  set ε : ℝ := g / (2 * ((1 + ‖z1‖ ^ 2) * Real.exp (lam * t1))) with hε
  have hden : 0 < (1 + ‖z1‖ ^ 2) * Real.exp (lam * t1) := by positivity
  have hεpos : 0 < ε := by rw [hε]; positivity
  have hεz1 : ε * ((1 + ‖z1‖ ^ 2) * Real.exp (lam * t1)) = g / 2 := by
    rw [hε]; field_simp
  set H : ℝ → E → ℝ := fun t z => G t z - ε * (1 + ‖z‖ ^ 2) * Real.exp (lam * t) with hH
  have hHz1 : H t1 z1 = g / 2 := by simp only [hH]; nlinarith
  -- lower bound on the exponential
  set m : ℝ := min 1 (Real.exp (lam * T)) with hm
  have hmpos : 0 < m := lt_min one_pos (Real.exp_pos _)
  have hexp : ∀ t ∈ Icc 0 T, m ≤ Real.exp (lam * t) := by
    intro t ht
    rcases le_total 0 lam with hl | hl
    · refine (min_le_left _ _).trans ?_
      rw [← Real.exp_zero]; exact Real.exp_le_exp.2 (by nlinarith [ht.1])
    · exact (min_le_right _ _).trans (Real.exp_le_exp.2 (by nlinarith [ht.2]))
  obtain ⟨C, hC⟩ := hgrow (ε * m / 2) (by positivity)
  have hHle : ∀ t ∈ Icc 0 T, ∀ z, H t z ≤ (C - ε * m) - (ε * m / 2) * ‖z‖ ^ 2 := by
    intro t ht z
    have h1 := hC t ht z
    have h2 : ε * m * (1 + ‖z‖ ^ 2) ≤ ε * (1 + ‖z‖ ^ 2) * Real.exp (lam * t) := by
      have := hexp t ht
      nlinarith [mul_le_mul_of_nonneg_left this (show 0 ≤ ε * (1 + ‖z‖ ^ 2) by positivity)]
    simp only [hH]
    nlinarith
  set ρ : ℝ := ‖z1‖ + (|C - ε * m| + g) / (ε * m / 2) + 1 with hρ
  have hρ1 : 1 ≤ ρ := by
    have : 0 ≤ (|C - ε * m| + g) / (ε * m / 2) := by positivity
    have := norm_nonneg z1
    rw [hρ]; linarith
  have hρz : ‖z1‖ ≤ ρ := by
    have : 0 ≤ (|C - ε * m| + g) / (ε * m / 2) := by positivity
    rw [hρ]; linarith
  have hρbig : |C - ε * m| + g ≤ (ε * m / 2) * ρ ^ 2 := by
    have h1 : (|C - ε * m| + g) / (ε * m / 2) ≤ ρ := by
      have := norm_nonneg z1
      rw [hρ]; linarith
    have h2 : |C - ε * m| + g ≤ (ε * m / 2) * ρ := by
      have h3 := (div_le_iff₀ (show 0 < ε * m / 2 by positivity)).1 h1
      linarith
    nlinarith [mul_le_mul_of_nonneg_left (show ρ ≤ ρ ^ 2 by nlinarith) (show 0 ≤ ε * m / 2 by positivity)]
  have hout : ∀ t ∈ Icc 0 T, ∀ z, ρ < ‖z‖ → H t z < 0 := by
    intro t ht z hz
    have h1 := hHle t ht z
    have h3 : ρ ^ 2 < ‖z‖ ^ 2 := by nlinarith
    have h4 := abs_nonneg (C - ε * m)
    have h5 := le_abs_self (C - ε * m)
    nlinarith [mul_lt_mul_of_pos_left h3 (show 0 < ε * m / 2 by positivity)]
  -- compactness
  have hK : IsCompact (Icc 0 T ×ˢ Metric.closedBall (0 : E) ρ) :=
    isCompact_Icc.prod (isCompact_closedBall _ _)
  have hKne : (Icc 0 T ×ˢ Metric.closedBall (0 : E) ρ).Nonempty :=
    ⟨(t1, z1), ht1, by simpa using hρz⟩
  have hHc : ContinuousOn (fun p : ℝ × E => H p.1 p.2) (Icc 0 T ×ˢ Metric.closedBall (0 : E) ρ) := by
    refine ContinuousOn.sub (hcont.mono (prod_mono le_rfl (subset_univ _))) ?_
    fun_prop
  obtain ⟨⟨t0, z0⟩, hp, hpmax⟩ := hK.exists_isMaxOn hKne hHc
  have hp1 : (t1, z1) ∈ Icc 0 T ×ˢ Metric.closedBall (0 : E) ρ := ⟨ht1, by simpa using hρz⟩
  have hge : g / 2 ≤ H t0 z0 := by
    have := hpmax hp1
    simp only [Set.mem_ofPred_eq] at this
    simpa [hHz1] using this
  have hgpos : 0 < g := hz1
  have hglob : ∀ t ∈ Icc 0 T, ∀ z, H t z ≤ H t0 z0 := by
    intro t ht z
    by_cases hz : ‖z‖ ≤ ρ
    · have := hpmax (show (t, z) ∈ Icc 0 T ×ˢ Metric.closedBall (0 : E) ρ from
        ⟨ht, by simpa using hz⟩)
      simpa using this
    · push Not at hz
      have := hout t ht z hz
      linarith
  have ht0 : t0 ∈ Icc 0 T := hp.1
  have ht0pos : 0 < t0 := by
    rcases ht0.1.eq_or_lt with h | h
    · exfalso
      have h1 := h0 z0
      have h2 : 0 < ε * (1 + ‖z0‖ ^ 2) := by positivity
      have : H t0 z0 < 0 := by
        simp only [hH, ← h, mul_zero, Real.exp_zero, mul_one]; linarith
      linarith
    · exact h
  have hfail' := hlam ε hεpos t0 ⟨ht0pos, ht0.2⟩ z0 (by simp only [hH] at hge; linarith)
    (fun z' => hglob t0 ht0 z')
  -- time derivative
  have hpen : HasDerivAt (fun s : ℝ => ε * (1 + ‖z0‖ ^ 2) * Real.exp (lam * s))
      (ε * (1 + ‖z0‖ ^ 2) * (Real.exp (lam * t0) * lam)) t0 := by
    have := (((hasDerivAt_id t0).const_mul lam).exp).const_mul (ε * (1 + ‖z0‖ ^ 2))
    simpa using this
  have hd := (hder t0 ⟨ht0pos, ht0.2⟩ z0).sub hpen.hasDerivWithinAt
  have hnn := pm_time_deriv_nonneg ht0pos ht0.2 hd (fun s hs => hglob s hs z0)
  nlinarith [hfail']

variable {d : ℕ}

theorem lu_second_nonpos {u : Euc d → ℝ} (hu : ContDiff ℝ 2 u) {z : Euc d} (hmax : IsLocalMax u z)
    (v : Euc d) : iteratedFDeriv ℝ 2 u z ![v, v] ≤ 0 := by
  have hl : IsLocalMax (fun s : ℝ => u (z + s • v)) 0 := by
    have hg : Continuous fun s : ℝ => z + s • v := by fun_prop
    have h0 : IsLocalMax u ((fun s : ℝ => z + s • v) 0) := by simpa using hmax
    exact h0.comp_continuous (b := (0 : ℝ)) hg.continuousAt
  have := localMax_second (h := fun s => u (z + s • v)) (G := fun s => fderiv ℝ u (z + s • v) v)
    (G2 := iteratedFDeriv ℝ 2 u (z + (0 : ℝ) • v) ![v, v])
    (Filter.Eventually.of_forall fun s => line_hasDerivAt hu z v s) (line_hasDerivAt2 hu z v 0) hl
  simpa using this.2

/-- One-point second-order necessary condition: `Δu(z) ≤ 0` at a local maximum of a `C²` function. -/
theorem lu_laplacian_nonpos {u : Euc d → ℝ} (hu : ContDiff ℝ 2 u) {z : Euc d}
    (hmax : IsLocalMax u z) : Laplacian.laplacian u z ≤ 0 := by
  rw [congrFun (InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis u
    (EuclideanSpace.basisFun (Fin d) ℝ)) z]
  exact Finset.sum_nonpos fun i _ => lu_second_nonpos hu hmax _

theorem lu_lap_pen {u : Euc d → ℝ} (hu : ContDiff ℝ 2 u) (κ : ℝ) (z : Euc d) :
    Laplacian.laplacian (fun w => u w - κ * ‖w‖ ^ 2) z = Laplacian.laplacian u z - 2 * κ * d := by
  have hsum : ∀ (b : OrthonormalBasis (Fin d) ℝ (Euc d)),
      ∑ i, iteratedFDeriv ℝ 2 (fun w => u w - κ * ‖w‖ ^ 2) z ![b i, b i] =
        Laplacian.laplacian u z - 2 * κ * d := by
    intro b
    simp only [ld_D2_pen hu, b.norm_eq_one, Finset.sum_sub_distrib]
    rw [← congrFun (InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis u b) z]
    simp
    ring
  rw [congrFun (InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _
    (EuclideanSpace.basisFun (Fin d) ℝ)) z, hsum (EuclideanSpace.basisFun (Fin d) ℝ)]

/-- Maximum-point step: at a global maximum `z` of `a(·) - κ(1+‖·‖²)` (`a ∈ C²`),
`∇a(z) = 2κ z` and `Δa(z) ≤ 2κ d`. -/
theorem lu_max_point {a : Euc d → ℝ} (ha : ContDiff ℝ 2 a) {κ : ℝ} {z : Euc d}
    (hmax : ∀ z', a z' - κ * (1 + ‖z'‖ ^ 2) ≤ a z - κ * (1 + ‖z‖ ^ 2)) :
    gradient a z = (2 * κ) • z ∧ Laplacian.laplacian a z ≤ 2 * κ * d := by
  have hφc : ContDiff ℝ 2 (fun w : Euc d => a w - κ * ‖w‖ ^ 2) :=
    ha.sub (contDiff_const.mul (contDiff_norm_sq ℝ))
  have hloc : IsLocalMax (fun w : Euc d => a w - κ * ‖w‖ ^ 2) z := by
    refine IsMaxOn.isLocalMax (s := Set.univ) (fun w _ => ?_) Filter.univ_mem
    have := hmax w
    simp only [Set.mem_ofPred_eq]
    linarith
  refine ⟨?_, ?_⟩
  · have h1 : fderiv ℝ (fun w : Euc d => a w - κ * ‖w‖ ^ 2) z = 0 := hloc.fderiv_eq_zero
    refine ext_inner_right ℝ fun v => ?_
    have h2 := ld_fderiv_pen ha κ z v
    rw [h1] at h2
    have h3 : inner ℝ (gradient a z) v = fderiv ℝ a z v := by
      unfold gradient
      rw [InnerProductSpace.toDual_symm_apply]
    rw [h3, real_inner_smul_left]
    simp at h2
    linarith
  · have h := lu_laplacian_nonpos hφc hloc
    rw [lu_lap_pen ha] at h
    linarith

end HRS.MS.Lc
