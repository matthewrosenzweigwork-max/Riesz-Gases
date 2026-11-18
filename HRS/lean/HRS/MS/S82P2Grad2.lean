import HRS.MS.S82P2Sum4

/-!
# S8.2 (S82P2): vector-valued centered sums (UNCOMPILED DRAFT)
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S82P2
open HRS HRS.Whole HRS.MS.Phase2S82

theorem s82p2_centered_vec_sum_sq {d : ℕ} {a beta C0 C1 : ℝ} {rho : Euc d → ℝ}
    {q : Euc d → ℝ} {h : ℕ → Euc d → ℝ}
    [IsProbabilityMeasure (HRS.Whole.withDensityReal rho)] (hd : 2 ≤ d)
    (hW : WeakReferenceSetup d a beta rho q h C0) (hbeta : 0 < beta)
    (hP : PinComparison beta rho q h C1) (G c : ℝ) (hG : 0 < G) (hc : 0 < c)
    (hρ : HRS.Whole.IsProbDensity rho) (hρG : HRS.Whole.HasR2GaussianUpper G c rho)
    {N : ℕ} (hN : 2 ≤ N) {p n : ℕ} (hp : p ≤ 2)
    (hnp : n + p ≤ N) (hNn : N - (n + p) ≤ 2) (pins : Fin p → Euc d)
    (g : Euc d → Euc d) (hgm : Measurable g)
    (hg2 : Integrable (fun z => ‖g z‖ ^ 2) (HRS.Whole.withDensityReal rho))
    (hg0 : ∫ z, g z ∂HRS.Whole.withDensityReal rho = 0) :
    ∫⁻ X : EucConfig d n, ENNReal.ofReal (‖∑ j, g (X j)‖ ^ 2)
          ∂referenceLaw q h (HRS.Whole.withDensityReal rho) beta N n pins ≤
        ENNReal.ofReal ((C0 ^ 2 * (2 + 2 * (1 + 2 * C1)) + (8 * C1 ^ 2 +
            2 * C1 ^ 2 * (1 + 2 * (1 / (1000 * beta))))) * N *
          ∫ z, ‖g z‖ ^ 2 ∂HRS.Whole.withDensityReal rho) := by
  set mu := HRS.Whole.withDensityReal rho with hmu
  set Cs : ℝ := C0 ^ 2 * (2 + 2 * (1 + 2 * C1)) + (8 * C1 ^ 2 +
    2 * C1 ^ 2 * (1 + 2 * (1 / (1000 * beta)))) with hCs
  have hCs0 : 0 ≤ Cs := by
    have := hW.positive
    have := s82p2_pinCmp_nonneg hP
    positivity
  have hNr : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hgi : Integrable g mu :=
    ((memLp_two_iff_integrable_sq_norm hgm.aestronglyMeasurable).2 hg2).integrable one_le_two
  have hproj : ∀ c' : Fin d, Measurable (fun z => g z c') := fun c' =>
    (EuclideanSpace.proj c' : Euc d →L[ℝ] ℝ).continuous.measurable.comp hgm
  have hpsi2 : ∀ c' : Fin d, Integrable (fun z => (g z c') ^ 2) mu := fun c' => by
    refine hg2.mono' ((hproj c').pow_const 2).aestronglyMeasurable (ae_of_all _ fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have := PiLp.norm_apply_le (g z) c'
    rw [Real.norm_eq_abs] at this
    calc (g z c') ^ 2 = |g z c'| ^ 2 := (sq_abs _).symm
      _ ≤ ‖g z‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2
  have hpsi0 : ∀ c' : Fin d, ∫ z, g z c' ∂mu = 0 := fun c' => by
    have := (EuclideanSpace.proj c' : Euc d →L[ℝ] ℝ).integral_comp_comm hgi
    simp only [PiLp.proj_apply] at this
    rw [this, hg0]; simp
  have hbound : ∀ c' : Fin d, ∫⁻ X : EucConfig d n, ENNReal.ofReal ((∑ j, g (X j) c') ^ 2)
      ∂referenceLaw q h mu beta N n pins ≤ ENNReal.ofReal (Cs * N * ∫ z, (g z c') ^ 2 ∂mu) :=
    fun c' => (s82p2_centered_sum_sq_simple hd hW hbeta hP G c hG hc hρ hρG hN hp hnp hNn pins
      (fun z => g z c') (hproj c') (hpsi2 c') (hpsi0 c')).2
  have hnorm : ∀ X : EucConfig d n, ‖∑ j, g (X j)‖ ^ 2 = ∑ c' : Fin d, (∑ j, g (X j) c') ^ 2 := by
    intro X
    rw [EuclideanSpace.norm_sq_eq]
    refine Finset.sum_congr rfl fun c' _ => ?_
    rw [Real.norm_eq_abs, sq_abs]
    have := map_sum (EuclideanSpace.proj c' : Euc d →L[ℝ] ℝ) (fun j => g (X j)) Finset.univ
    simpa using this.symm
  have hmeasS : ∀ c' : Fin d, Measurable (fun X : EucConfig d n => ENNReal.ofReal
      ((∑ j, g (X j) c') ^ 2)) := fun c' =>
    ENNReal.measurable_ofReal.comp
      ((Finset.measurable_sum _ fun j _ => (hproj c').comp (measurable_pi_apply j)).pow_const 2)
  simp_rw [hnorm]
  simp_rw [ENNReal.ofReal_sum_of_nonneg (fun c' _ => sq_nonneg _)]
  rw [lintegral_finset_sum _ fun c' _ => hmeasS c']
  calc ∑ c' : Fin d, ∫⁻ X : EucConfig d n, ENNReal.ofReal ((∑ j, g (X j) c') ^ 2)
        ∂referenceLaw q h mu beta N n pins
      ≤ ∑ c' : Fin d, ENNReal.ofReal (Cs * N * ∫ z, (g z c') ^ 2 ∂mu) :=
        Finset.sum_le_sum fun c' _ => hbound c'
    _ = ENNReal.ofReal (Cs * N * ∫ z, ‖g z‖ ^ 2 ∂mu) := by
        rw [← ENNReal.ofReal_sum_of_nonneg (fun c' _ => mul_nonneg (mul_nonneg hCs0 hNr)
          (integral_nonneg fun z => sq_nonneg _)), ← Finset.mul_sum]
        congr 2
        rw [← integral_finset_sum _ fun c' _ => hpsi2 c']
        refine integral_congr_ae (ae_of_all _ fun z => ?_)
        simp only
        rw [EuclideanSpace.norm_sq_eq]
        refine Finset.sum_congr rfl fun c' _ => ?_
        rw [Real.norm_eq_abs, sq_abs]

end HRS.MS.S82P2
