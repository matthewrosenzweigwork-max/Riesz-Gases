import Mathlib
import HRS.Torus.Basic
import HRS.MS.PoissonSpike

open Filter Topology Set
open scoped RealInnerProductSpace

/-!
# POIS-MAXP (part 1): tie to `Laplacian.laplacian` and the penalised maximum principle

(a) `pm_lapE_eq_laplacian` : `PoissonSpike.lapE u = Laplacian.laplacian u` (the spike's private trace
of `iteratedFDeriv ℝ 2` equals Mathlib's Laplacian, which is the one used by `poissonOp` and
`IsInvariantMeasure`).  `pm_poisson_maxpoint` is `PoissonSpike.poisson_maxpoint` restated with
`Laplacian.laplacian`.

(b) `pm_penalized_max` : Lyapunov penalisation on `[0,T] × E`.  Adjustments with respect to the
sketch (documented, harmless): the space `E` is any proper normed group (so that the doubled
space `Euc d × Euc d` is allowed); the spatial regularity of `G` is not needed in the abstract
statement (it is only used by the user to prove the failure hypothesis `hfail`), only joint
continuity on `[0,T] × E` and a one-sided time derivative `Gt`; the growth bound `G ≤ C(1+‖z‖²)`
is replaced by sub-quadratic growth (`∀ δ > 0, ∃ C, G ≤ C + δ‖z‖²`, implied by linear growth,
see `pm_penalized_max_linear`), because with a quadratic bound the quadratic penalty does not
force the penalised function to `-∞`; the penalty rate `lam` is uniform in `ε`.
-/

namespace HRS.MS.PoisMax

open HRS.MS.PoissonSpike

/-- Tie: the spike's `lapE` equals Mathlib's Laplacian. -/
theorem pm_lapE_eq_laplacian {d : ℕ} (u : Euc d → ℝ) (z : Euc d) :
    lapE u z = Laplacian.laplacian u z := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis u
    (EuclideanSpace.basisFun (Fin d) ℝ)]
  rfl

/-- The maximum-point step of `PoissonSpike`, with `Laplacian.laplacian`. -/
theorem pm_poisson_maxpoint {d : ℕ} (hd : 1 ≤ d) (u : Euc d → ℝ) (hu : ContDiff ℝ 2 u) (A : ℝ)
    (f : ℝ → ℝ) (hf : ContDiffOn ℝ 2 f (Set.Ioi 0)) (x y : Euc d)
    (hmax : IsLocalMax (fun p : Euc d × Euc d => u p.1 - u p.2 - A * f ‖p.1 - p.2‖) (x, y))
    (hxy : x ≠ y) :
    (∀ v : Euc d, fderiv ℝ u x v = A * deriv f ‖x - y‖ * inner ℝ (‖x - y‖⁻¹ • (x - y)) v ∧
      fderiv ℝ u y v = A * deriv f ‖x - y‖ * inner ℝ (‖x - y‖⁻¹ • (x - y)) v) ∧
    Laplacian.laplacian u x - Laplacian.laplacian u y ≤ 4 * A * deriv (deriv f) ‖x - y‖ := by
  have h := poisson_maxpoint hd u hu A f hf x y hmax hxy
  rw [pm_lapE_eq_laplacian, pm_lapE_eq_laplacian] at h
  exact h


/-- one-sided time argument: a maximum of `φ` over `[0,T]` at `t0 > 0` forces `φ' ≥ 0`. -/
theorem pm_time_deriv_nonneg {φ : ℝ → ℝ} {T t0 d : ℝ} (ht0 : 0 < t0) (htT : t0 ≤ T)
    (hd : HasDerivWithinAt φ d (Icc 0 T) t0) (hmax : ∀ s ∈ Icc (0:ℝ) T, φ s ≤ φ t0) :
    0 ≤ d := by
  have hm : IsLocalMaxOn φ (Icc 0 T) t0 :=
    (show IsMaxOn φ (Icc 0 T) t0 from fun s hs => hmax s hs).isLocalMaxOn
  have hseg : segment ℝ t0 (t0 + (-t0)) ⊆ Icc 0 T := by
    have h0 : (0:ℝ) ∈ Icc 0 T := ⟨le_rfl, ht0.le.trans htT⟩
    have h1 : t0 ∈ Icc 0 T := ⟨ht0.le, htT⟩
    simpa using (convex_Icc (0:ℝ) T).segment_subset h1 h0
  have := hm.hasFDerivWithinAt_nonpos hd.hasFDerivWithinAt
    (mem_posTangentConeAt_of_segment_subset hseg)
  simp at this
  nlinarith

/-- Penalised maximum principle (Lyapunov penalisation on `[0,T] × E`).  If `G ≤ 0` at time `0`,
`G` has sub-quadratic growth, and at every spatial maximum (at a time in `(0,T]`) of the penalised
function `G t - ε(1+‖z‖²)e^{lam t}` with positive value the time derivative is `< ε lam (1+‖z‖²)e^{lam t}`
(the differential inequality fails), then `G ≤ 0` on `[0,T] × E`. -/
theorem pm_penalized_max {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
    (G Gt : ℝ → E → ℝ) (T : ℝ)
    (hcont : ContinuousOn (fun p : ℝ × E => G p.1 p.2) (Icc 0 T ×ˢ univ))
    (hder : ∀ t ∈ Icc 0 T, ∀ z, HasDerivWithinAt (fun s => G s z) (Gt t z) (Icc 0 T) t)
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
    simp only [Set.mem_setOf_eq] at this
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
  have hd := (hder t0 ht0 z0).sub hpen.hasDerivWithinAt
  have hnn := pm_time_deriv_nonneg ht0pos ht0.2 hd (fun s hs => hglob s hs z0)
  nlinarith [hfail']

/-- Linear-growth form of `pm_penalized_max` (`G ≤ C(1+‖z‖)`). -/
theorem pm_penalized_max_linear {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
    (G Gt : ℝ → E → ℝ) (T : ℝ)
    (hcont : ContinuousOn (fun p : ℝ × E => G p.1 p.2) (Icc 0 T ×ˢ univ))
    (hder : ∀ t ∈ Icc 0 T, ∀ z, HasDerivWithinAt (fun s => G s z) (Gt t z) (Icc 0 T) t)
    (h0 : ∀ z, G 0 z ≤ 0)
    (hgrow : ∃ C : ℝ, ∀ t ∈ Icc 0 T, ∀ z, G t z ≤ C * (1 + ‖z‖))
    (hfail : ∃ lam : ℝ, ∀ ε : ℝ, 0 < ε → ∀ t ∈ Ioc 0 T, ∀ z,
        0 < G t z - ε * (1 + ‖z‖ ^ 2) * Real.exp (lam * t) →
        (∀ z', G t z' - ε * (1 + ‖z'‖ ^ 2) * Real.exp (lam * t) ≤
          G t z - ε * (1 + ‖z‖ ^ 2) * Real.exp (lam * t)) →
        Gt t z < ε * lam * (1 + ‖z‖ ^ 2) * Real.exp (lam * t)) :
    ∀ t ∈ Icc 0 T, ∀ z, G t z ≤ 0 := by
  obtain ⟨C, hC⟩ := hgrow
  refine pm_penalized_max G Gt T hcont hder h0 (fun δ hδ => ⟨|C| + |C| ^ 2 / (4 * δ), ?_⟩) hfail
  intro t ht z
  have h1 := hC t ht z
  have h2 : C * (1 + ‖z‖) ≤ |C| * (1 + ‖z‖) :=
    mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
  have h3 : |C| * ‖z‖ ≤ δ * ‖z‖ ^ 2 + |C| ^ 2 / (4 * δ) := by
    have h4 : 0 ≤ (2 * δ * ‖z‖ - |C|) ^ 2 := sq_nonneg _
    have h5 : |C| ^ 2 / (4 * δ) = |C| ^ 2 * (4 * δ)⁻¹ := div_eq_mul_inv _ _
    have h6 : (4 * δ) * (4 * δ)⁻¹ = 1 := mul_inv_cancel₀ (by positivity)
    have h7 : 0 < (4 * δ)⁻¹ := by positivity
    nlinarith [mul_nonneg h4 h7.le]
  nlinarith

end HRS.MS.PoisMax
