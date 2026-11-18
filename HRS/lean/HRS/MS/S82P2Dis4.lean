import HRS.MS.S82P2Dis3

/-!
# S8.2 (S82P2): the one-coordinate disintegration theorem
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S82P2
open HRS HRS.Whole HRS.MS.Phase2S82

/-- Disintegration of the weak reference law over coordinate `i`: the conditional law of the other
`m` coordinates given `X i = z` is the `m`-coordinate reference law with the extra pin `z`. -/
theorem s82p2_disintegration {d p m : ℕ} {q : Euc d → ℝ} {h : ℕ → Euc d → ℝ}
    {mu : Measure (Euc d)} [SigmaFinite mu] (hq : Measurable q) (hqe : ∀ z, q (-z) = q z)
    (beta : ℝ) (N : ℕ) (hh : Measurable (h N)) (pins : Fin p → Euc d) (i : Fin (m + 1))
    (h1 : IsProbabilityMeasure (referenceLaw q h mu beta N (m + 1) pins))
    (h0 : ∀ z : Euc d, IsProbabilityMeasure
      (referenceLaw q h mu beta N m (Fin.cons z pins : Fin (p + 1) → Euc d)))
    (F : EucConfig d (m + 1) → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ X, F X ∂referenceLaw q h mu beta N (m + 1) pins =
      ∫⁻ z, ∫⁻ X', F (i.insertNth z X')
          ∂referenceLaw q h mu beta N m (Fin.cons z pins : Fin (p + 1) → Euc d)
        ∂((referenceLaw q h mu beta N (m + 1) pins).map (fun X => X i)) := by
  obtain ⟨c1a, c1b, hr1⟩ := s82p2_ref_of_prob (n := m + 1) (mu := mu) hq beta N hh pins h1
  set c1 := (s82p2_W q h mu beta N pins : Measure (EucConfig d (m + 1))) Set.univ with hc1
  have hes := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => Euc d) i).symm.measurable
  -- notation for the pinned pieces
  let c0 : Euc d → ℝ≥0∞ := fun z =>
    (s82p2_W q h mu beta N (Fin.cons z pins : Fin (p + 1) → Euc d) : Measure (EucConfig d m)) Set.univ
  have hc0 : ∀ z, c0 z ≠ 0 ∧ c0 z ≠ ⊤ ∧
      referenceLaw q h mu beta N m (Fin.cons z pins : Fin (p + 1) → Euc d) =
        (c0 z)⁻¹ • (s82p2_W q h mu beta N (Fin.cons z pins : Fin (p + 1) → Euc d) :
          Measure (EucConfig d m)) := fun z =>
    s82p2_ref_of_prob (n := m) (mu := mu) hq beta N hh _ (h0 z)
  let J : Euc d → ℝ≥0∞ := fun z => ∫⁻ X', F (i.insertNth z X')
    ∂referenceLaw q h mu beta N m (Fin.cons z pins : Fin (p + 1) → Euc d)
  let K : Euc d → ℝ≥0∞ := fun z => ∫⁻ X', F (i.insertNth z X')
    ∂(s82p2_W q h mu beta N (Fin.cons z pins : Fin (p + 1) → Euc d) : Measure (EucConfig d m))
  have hJK : ∀ z, J z = (c0 z)⁻¹ * K z := fun z => by
    show ∫⁻ X', F (i.insertNth z X') ∂referenceLaw q h mu beta N m _ = _
    rw [(hc0 z).2.2, lintegral_smul_measure, smul_eq_mul]
  have hKJ : ∀ z, K z = c0 z * J z := fun z => by
    rw [hJK z, ← mul_assoc, ENNReal.mul_inv_cancel (hc0 z).1 (hc0 z).2.1, one_mul]
  -- measurability of c0 and K in z
  have hexpm : Measurable (fun r : Euc d × EucConfig d m => ENNReal.ofReal (Real.exp
      (referenceExponent q h mu beta N (Fin.cons r.1 pins : Fin (p + 1) → Euc d) r.2))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      (s82p2_exponent_cons_measurable (mu := mu) hq beta N hh pins))
  have hinsm : Measurable (fun r : Euc d × EucConfig d m => F (i.insertNth r.1 r.2)) :=
    hF.comp hes
  have hc0m : Measurable c0 := by
    have : c0 = fun z => ∫⁻ X', ENNReal.ofReal (Real.exp
        (referenceExponent q h mu beta N (Fin.cons z pins : Fin (p + 1) → Euc d) X'))
          ∂(Measure.pi fun _ : Fin m => mu) := by
      funext z
      show (s82p2_W q h mu beta N _ : Measure (EucConfig d m)) Set.univ = _
      unfold s82p2_W
      rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    rw [this]
    exact hexpm.lintegral_prod_right'
  have hKm : Measurable K := by
    have : K = fun z => ∫⁻ X', ENNReal.ofReal (Real.exp
        (referenceExponent q h mu beta N (Fin.cons z pins : Fin (p + 1) → Euc d) X')) *
          F (i.insertNth z X') ∂(Measure.pi fun _ : Fin m => mu) := by
      funext z
      have hf' : Measurable (fun X' : EucConfig d m => ENNReal.ofReal (Real.exp
          (referenceExponent q h mu beta N (Fin.cons z pins : Fin (p + 1) → Euc d) X'))) :=
        ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
          (s82p2_exponent_measurable (n := m) (h := h) (mu := mu) hq beta N hh _))
      have hFz : Measurable (fun X' : EucConfig d m => F (i.insertNth z X')) :=
        hF.comp (hes.comp measurable_prodMk_left)
      show ∫⁻ X', F (i.insertNth z X')
        ∂(s82p2_W q h mu beta N _ : Measure (EucConfig d m)) = _
      unfold s82p2_W
      rw [lintegral_withDensity_eq_lintegral_mul _ hf' hFz]
      rfl
    rw [this]
    exact (hexpm.mul hinsm).lintegral_prod_right'
  have hJm : Measurable J := by
    have : J = fun z => (c0 z)⁻¹ * K z := funext hJK
    rw [this]
    exact hc0m.inv.mul hKm
  -- left side
  have hL : ∫⁻ X, F X ∂referenceLaw q h mu beta N (m + 1) pins =
      c1⁻¹ * ∫⁻ z, ENNReal.ofReal (Real.exp (s82p2_site q h mu beta N pins z)) * K z ∂mu := by
    rw [hr1, lintegral_smul_measure, smul_eq_mul]
    rw [s82p2_W_lintegral hq hqe beta N hh pins i F hF]
  -- right side
  have hR : ∫⁻ z, J z ∂((referenceLaw q h mu beta N (m + 1) pins).map (fun X => X i)) =
      c1⁻¹ * ∫⁻ z, ENNReal.ofReal (Real.exp (s82p2_site q h mu beta N pins z)) * K z ∂mu := by
    rw [lintegral_map hJm (measurable_pi_apply i), hr1, lintegral_smul_measure, smul_eq_mul]
    rw [s82p2_W_lintegral hq hqe beta N hh pins i (fun X => J (X i)) (hJm.comp (measurable_pi_apply i))]
    congr 2
    funext z
    congr 1
    simp only [Fin.insertNth_apply_same]
    rw [lintegral_const, mul_comm, ← hKJ z]
  rw [hL]
  exact hR.symm

end HRS.MS.S82P2
