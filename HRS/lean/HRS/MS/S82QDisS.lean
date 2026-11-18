import HRS.MS.S82QDom

/-!
# S8.2 (S82Q): signed disintegration of the weak reference law over one coordinate
`s82q_J_measurable`: measurability of the conditional expectation `z |-> int F(insertNth z .) dR^{(z,pins)}`;
`s82q_disint_integral`: for an integrable `f`,
`int f dR = int_z (int f(insertNth z .) dR^{(z,pins)}) d(law of X_i)` (from `s82p2_disintegration` applied to the
positive and negative parts).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S82Q
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.S82P2

lemma s82q_J_measurable {d p m : ℕ} {q : Euc d → ℝ} {h : ℕ → Euc d → ℝ}
    {mu : Measure (Euc d)} [SigmaFinite mu] (hq : Measurable q) (hqe : ∀ z, q (-z) = q z)
    (beta : ℝ) (N : ℕ) (hh : Measurable (h N)) (pins : Fin p → Euc d) (i : Fin (m + 1))
    (h0 : ∀ z : Euc d, IsProbabilityMeasure
      (referenceLaw q h mu beta N m (Fin.cons z pins : Fin (p + 1) → Euc d)))
    (F : EucConfig d (m + 1) → ℝ≥0∞) (hF : Measurable F) :
    Measurable (fun z : Euc d => ∫⁻ X', F (i.insertNth z X')
      ∂referenceLaw q h mu beta N m (Fin.cons z pins : Fin (p + 1) → Euc d)) := by
  have hes := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => Euc d) i).symm.measurable
  let c0 : Euc d → ℝ≥0∞ := fun z =>
    (s82p2_W q h mu beta N (Fin.cons z pins : Fin (p + 1) → Euc d) : Measure (EucConfig d m)) Set.univ
  have hc0 : ∀ z, c0 z ≠ 0 ∧ c0 z ≠ ⊤ ∧
      referenceLaw q h mu beta N m (Fin.cons z pins : Fin (p + 1) → Euc d) =
        (c0 z)⁻¹ • (s82p2_W q h mu beta N (Fin.cons z pins : Fin (p + 1) → Euc d) :
          Measure (EucConfig d m)) := fun z =>
    s82p2_ref_of_prob (n := m) (mu := mu) hq beta N hh _ (h0 z)
  let K : Euc d → ℝ≥0∞ := fun z => ∫⁻ X', F (i.insertNth z X')
    ∂(s82p2_W q h mu beta N (Fin.cons z pins : Fin (p + 1) → Euc d) : Measure (EucConfig d m))
  have hJK : ∀ z, ∫⁻ X', F (i.insertNth z X')
      ∂referenceLaw q h mu beta N m (Fin.cons z pins : Fin (p + 1) → Euc d) = (c0 z)⁻¹ * K z := by
    intro z
    rw [(hc0 z).2.2, lintegral_smul_measure, smul_eq_mul]
  have hexpm : Measurable (fun r : Euc d × EucConfig d m => ENNReal.ofReal (Real.exp
      (referenceExponent q h mu beta N (Fin.cons r.1 pins : Fin (p + 1) → Euc d) r.2))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      (s82p2_exponent_cons_measurable (mu := mu) hq beta N hh pins))
  have hinsm : Measurable (fun r : Euc d × EucConfig d m => F (i.insertNth r.1 r.2)) := hF.comp hes
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
  have : (fun z : Euc d => ∫⁻ X', F (i.insertNth z X')
      ∂referenceLaw q h mu beta N m (Fin.cons z pins : Fin (p + 1) → Euc d)) =
      fun z => (c0 z)⁻¹ * K z := funext hJK
  rw [this]
  exact hc0m.inv.mul hKm

theorem s82q_disint_integral {d p m : ℕ} {q : Euc d → ℝ} {h : ℕ → Euc d → ℝ}
    {mu : Measure (Euc d)} [SigmaFinite mu] (hq : Measurable q) (hqe : ∀ z, q (-z) = q z)
    (beta : ℝ) (N : ℕ) (hh : Measurable (h N)) (pins : Fin p → Euc d) (i : Fin (m + 1))
    (h1 : IsProbabilityMeasure (referenceLaw q h mu beta N (m + 1) pins))
    (h0 : ∀ z : Euc d, IsProbabilityMeasure
      (referenceLaw q h mu beta N m (Fin.cons z pins : Fin (p + 1) → Euc d)))
    (f : EucConfig d (m + 1) → ℝ) (hfm : Measurable f)
    (hf : Integrable f (referenceLaw q h mu beta N (m + 1) pins)) :
    ∫ X, f X ∂referenceLaw q h mu beta N (m + 1) pins =
      ∫ z, (∫ X', f (i.insertNth z X')
          ∂referenceLaw q h mu beta N m (Fin.cons z pins : Fin (p + 1) → Euc d))
        ∂((referenceLaw q h mu beta N (m + 1) pins).map (fun X => X i)) := by
  set ref := referenceLaw q h mu beta N (m + 1) pins with href
  set marg := ref.map (fun X => X i) with hmarg
  set κ : Euc d → Measure (Fin m → Euc d) := fun z =>
    referenceLaw q h mu beta N m (Fin.cons z pins : Fin (p + 1) → Euc d) with hκ
  have hes := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => Euc d) i).symm.measurable
  have hD : ∀ F : EucConfig d (m + 1) → ℝ≥0∞, Measurable F →
      ∫⁻ X, F X ∂ref = ∫⁻ z, ∫⁻ X', F (i.insertNth z X') ∂κ z ∂marg := fun F hF =>
    s82p2_disintegration hq hqe beta N hh pins i h1 h0 F hF
  have hsec : ∀ z, Measurable (fun X' : Fin m → Euc d => f (i.insertNth z X')) := fun z =>
    hfm.comp (hes.comp measurable_prodMk_left)
  let Jp : Euc d → ℝ≥0∞ := fun z => ∫⁻ X', ENNReal.ofReal (f (i.insertNth z X')) ∂κ z
  let Jn : Euc d → ℝ≥0∞ := fun z => ∫⁻ X', ENNReal.ofReal (-f (i.insertNth z X')) ∂κ z
  have hFp : Measurable (fun X : EucConfig d (m + 1) => ENNReal.ofReal (f X)) :=
    ENNReal.measurable_ofReal.comp hfm
  have hFn : Measurable (fun X : EucConfig d (m + 1) => ENNReal.ofReal (-f X)) :=
    ENNReal.measurable_ofReal.comp hfm.neg
  have hJp : Measurable Jp := s82q_J_measurable hq hqe beta N hh pins i h0 _ hFp
  have hJn : Measurable Jn := s82q_J_measurable hq hqe beta N hh pins i h0 _ hFn
  have hp := hD _ hFp
  have hn := hD _ hFn
  have hfp : ∫⁻ X, ENNReal.ofReal (f X) ∂ref ≠ ⊤ := hf.lintegral_lt_top.ne
  have hfn : ∫⁻ X, ENNReal.ofReal (-f X) ∂ref ≠ ⊤ := hf.neg.lintegral_lt_top.ne
  have hJp' : ∫⁻ z, Jp z ∂marg ≠ ⊤ := by rw [← hp]; exact hfp
  have hJn' : ∫⁻ z, Jn z ∂marg ≠ ⊤ := by rw [← hn]; exact hfn
  have haep := ae_lt_top hJp hJp'
  have haen := ae_lt_top hJn hJn'
  have hI : ∀ᵐ z ∂marg, ∫ X', f (i.insertNth z X') ∂κ z = (Jp z).toReal - (Jn z).toReal := by
    filter_upwards [haep, haen] with z hzp hzn
    have hint : Integrable (fun X' => f (i.insertNth z X')) (κ z) := by
      refine ⟨(hsec z).aestronglyMeasurable, ?_⟩
      have hmz : Measurable (fun X' : Fin m → Euc d => ENNReal.ofReal (f (i.insertNth z X'))) :=
        ENNReal.measurable_ofReal.comp (hsec z)
      have : ∫⁻ X', ‖f (i.insertNth z X')‖ₑ ∂κ z = Jp z + Jn z := by
        show _ = ∫⁻ X', ENNReal.ofReal (f (i.insertNth z X')) ∂κ z +
          ∫⁻ X', ENNReal.ofReal (-f (i.insertNth z X')) ∂κ z
        rw [← lintegral_add_left hmz]
        refine lintegral_congr fun X' => ?_
        rw [Real.enorm_eq_ofReal_abs]
        rcases le_total 0 (f (i.insertNth z X')) with hx | hx
        · rw [abs_of_nonneg hx, ENNReal.ofReal_of_nonpos (by linarith : -f (i.insertNth z X') ≤ 0),
            add_zero]
        · rw [abs_of_nonpos hx, ENNReal.ofReal_of_nonpos hx, zero_add]
      show ∫⁻ X', ‖f (i.insertNth z X')‖ₑ ∂κ z < ⊤
      rw [this]
      exact ENNReal.add_lt_top.2 ⟨hzp, hzn⟩
    exact integral_eq_lintegral_pos_part_sub_lintegral_neg_part hint
  rw [integral_congr_ae hI, integral_eq_lintegral_pos_part_sub_lintegral_neg_part hf]
  have e1 := integral_toReal hJp.aemeasurable haep
  have e2 := integral_toReal hJn.aemeasurable haen
  rw [integral_sub (integrable_toReal_of_lintegral_ne_top hJp.aemeasurable hJp')
    (integrable_toReal_of_lintegral_ne_top hJn.aemeasurable hJn'), e1, e2, ← hp, ← hn]

end HRS.MS.S82Q
