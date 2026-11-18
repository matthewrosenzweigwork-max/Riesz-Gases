import HRS.MS.S82P2Pair1

/-!
# S8.2 (S82Q): one-site resampling is reversible for the weak reference law
For `referenceLaw N (m+1) pins` (a probability measure), resampling coordinate `i` from `resampleLaw`
preserves the law: `E_ref [ ∫ g(update X i y) d resample_i(X)(y) ] = E_ref [g]`.
Route: unnormalised weight `s82p2_W`, Tonelli swap of `(z, X')`, and the fact that the resampling law of
`X = insertNth z X'` is the normalised tilt `e^{V(X', .)} dmu`, independent of `z`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S82Q
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.S82P2

/-- The exponent of the new site `y` given the other `m` coordinates `X'` and the pins. -/
def s82q_V {d p m : ℕ} (q : Euc d → ℝ) (h : ℕ → Euc d → ℝ) (mu : Measure (Euc d)) (beta : ℝ)
    (N : ℕ) (pins : Fin p → Euc d) (X' : Fin m → Euc d) (y : Euc d) : ℝ :=
  s82p2_site q h mu beta N pins y - (beta / N) * ∑ j, q (X' j - y)

lemma s82q_V_measurable {d p m : ℕ} {q : Euc d → ℝ} {h : ℕ → Euc d → ℝ} {mu : Measure (Euc d)}
    [SFinite mu] (hq : Measurable q) (beta : ℝ) (N : ℕ) (hh : Measurable (h N))
    (pins : Fin p → Euc d) :
    Measurable (fun r : (Fin m → Euc d) × Euc d => s82q_V q h mu beta N pins r.1 r.2) := by
  unfold s82q_V s82p2_site
  have hc := s82p2_conv_measurable hq mu
  refine Measurable.sub (Measurable.sub ((measurable_const.mul (hc.comp measurable_snd)).add
    (hh.comp measurable_snd)) (measurable_const.mul (Finset.measurable_sum _ fun j _ =>
      hq.comp (measurable_snd.sub measurable_const)))) (measurable_const.mul
        (Finset.measurable_sum _ fun j _ => hq.comp
          (((measurable_pi_apply j).comp measurable_fst).sub measurable_snd)))

lemma s82q_V_measurable_swap {d p m : ℕ} {q : Euc d → ℝ} {h : ℕ → Euc d → ℝ}
    {mu : Measure (Euc d)} [SFinite mu] (hq : Measurable q) (beta : ℝ) (N : ℕ)
    (hh : Measurable (h N)) (pins : Fin p → Euc d) :
    Measurable (fun r : Euc d × (Fin m → Euc d) => s82q_V q h mu beta N pins r.2 r.1) :=
  (s82q_V_measurable (m := m) hq beta N hh pins).comp measurable_swap

lemma s82q_exp_insertNth {d p m : ℕ} {q : Euc d → ℝ} (hqe : ∀ z, q (-z) = q z)
    (h : ℕ → Euc d → ℝ) (mu : Measure (Euc d)) (beta : ℝ) (N : ℕ) (pins : Fin p → Euc d)
    (i : Fin (m + 1)) (z : Euc d) (X' : Fin m → Euc d) :
    referenceExponent q h mu beta N pins (i.insertNth z X' : EucConfig d (m + 1)) =
      referenceExponent q h mu beta N pins X' + s82q_V q h mu beta N pins X' z := by
  rw [s82p2_exponent_insertNth hqe, s82p2_exponent_cons]
  unfold s82q_V
  ring

/-- The resampling law of `insertNth z X'` is the tilt of `mu` by `V(X', .)`. -/
lemma s82q_res_insertNth {d p m : ℕ} {q : Euc d → ℝ} (hqe : ∀ z, q (-z) = q z)
    (h : ℕ → Euc d → ℝ) (mu : Measure (Euc d)) (beta : ℝ) (N : ℕ) (pins : Fin p → Euc d)
    (i : Fin (m + 1)) (z : Euc d) (X' : Fin m → Euc d) :
    resampleLaw q h mu beta N pins i (i.insertNth z X' : EucConfig d (m + 1)) =
      exponentialTilt mu (s82q_V q h mu beta N pins X') := by
  unfold resampleLaw
  congr 1
  funext y
  have e1 : ∑ j ∈ Finset.univ.erase i, q (y - (i.insertNth z X' : EucConfig d (m + 1)) j) =
      ∑ j, q (X' j - y) := by
    rw [s82p2_sum_erase (fun j => q (y - (i.insertNth z X' : EucConfig d (m + 1)) j)) i]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Fin.insertNth_apply_succAbove, ← hqe]
    congr 1
    abel
  rw [e1]
  unfold s82q_V s82p2_site
  ring

lemma s82q_insertNth_removeNth {d m : ℕ} (i : Fin (m + 1)) (X : EucConfig d (m + 1)) :
    i.insertNth (X i) (fun j => X (i.succAbove j)) = X := by
  funext j
  by_cases hj : j = i
  · subst hj; simp
  · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hj
    simp

lemma s82q_W_swap {d p m : ℕ} {q : Euc d → ℝ} {h : ℕ → Euc d → ℝ}
    {mu : Measure (Euc d)} [SigmaFinite mu] (hq : Measurable q) (hqe : ∀ z, q (-z) = q z)
    (beta : ℝ) (N : ℕ) (hh : Measurable (h N)) (pins : Fin p → Euc d) (i : Fin (m + 1))
    (F : EucConfig d (m + 1) → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ X, F X ∂(s82p2_W q h mu beta N pins : Measure (EucConfig d (m + 1))) =
      ∫⁻ X', ENNReal.ofReal (Real.exp (referenceExponent q h mu beta N pins X')) *
        ∫⁻ z, ENNReal.ofReal (Real.exp (s82q_V q h mu beta N pins X' z)) *
          F (i.insertNth z X') ∂mu ∂(Measure.pi fun _ : Fin m => mu) := by
  have hE := s82p2_exponent_measurable (n := m + 1) (h := h) (mu := mu) hq beta N hh pins
  have hf : Measurable (fun X : EucConfig d (m + 1) =>
      ENNReal.ofReal (Real.exp (referenceExponent q h mu beta N pins X))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hE)
  unfold s82p2_W
  rw [lintegral_withDensity_eq_lintegral_mul _ hf hF]
  have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => mu) i
  have hemb := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => Euc d) i).symm.measurableEmbedding
  have key := hmp.symm.lintegral_comp_emb hemb
    (fun X : EucConfig d (m + 1) => ((fun X : EucConfig d (m + 1) =>
      ENNReal.ofReal (Real.exp (referenceExponent q h mu beta N pins X))) * F) X)
  rw [← key]
  have hes := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => Euc d) i).symm.measurable
  have hprod := lintegral_prod_symm (μ := mu) (ν := Measure.pi fun _ : Fin m => mu)
    (fun a : Euc d × (Fin m → Euc d) => ((fun X : EucConfig d (m + 1) =>
      ENNReal.ofReal (Real.exp (referenceExponent q h mu beta N pins X))) * F)
        ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => Euc d) i).symm a))
    ((hf.mul hF).comp hes).aemeasurable
  rw [hprod]
  refine lintegral_congr fun X' => ?_
  have e1 : ∀ z : Euc d, (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => Euc d) i).symm
      (z, X') = i.insertNth z X' := fun z => rfl
  simp only [Pi.mul_apply, e1, s82q_exp_insertNth hqe]
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun z => ?_
  rw [Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le, mul_assoc]

lemma s82q_tilt_lintegral {α : Type*} [MeasurableSpace α] (P : Measure α) (V : α → ℝ)
    (hV : Measurable V) (g : α → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ y, g y ∂exponentialTilt P V =
      (ENNReal.ofReal (∫ x, Real.exp (V x) ∂P))⁻¹ *
        ∫⁻ y, ENNReal.ofReal (Real.exp (V y)) * g y ∂P := by
  have hmeas : Measurable (fun x => ENNReal.ofReal (Real.exp (V x))) :=
    ENNReal.measurable_ofReal.comp hV.exp
  unfold exponentialTilt
  rw [lintegral_smul_measure, smul_eq_mul, lintegral_withDensity_eq_lintegral_mul P hmeas hg]
  rfl

lemma s82q_zeta {α : Type*} [MeasurableSpace α] (P : Measure α) [IsProbabilityMeasure P]
    (V : α → ℝ) (hV : Measurable V) (c : ℝ) (hc : ∀ y, V y ≤ c) :
    ENNReal.ofReal (∫ x, Real.exp (V x) ∂P) = ∫⁻ y, ENNReal.ofReal (Real.exp (V y)) ∂P ∧
      ENNReal.ofReal (∫ x, Real.exp (V x) ∂P) ≠ 0 ∧
      ENNReal.ofReal (∫ x, Real.exp (V x) ∂P) ≠ ⊤ := by
  have hint : Integrable (fun x => Real.exp (V x)) P := by
    refine Integrable.mono' (integrable_const (Real.exp c)) hV.exp.aestronglyMeasurable
      (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.2 (hc x)
  refine ⟨ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun _ => (Real.exp_pos _).le),
    ?_, ENNReal.ofReal_ne_top⟩
  rw [Ne, ENNReal.ofReal_eq_zero, not_le]
  exact integral_exp_pos hint

/-- **Reversibility of one-site resampling** under the weak reference law. -/
theorem s82q_invariance {d p m : ℕ} {q : Euc d → ℝ} {h : ℕ → Euc d → ℝ} {mu : Measure (Euc d)}
    [IsProbabilityMeasure mu] (hq : Measurable q) (hqe : ∀ z, q (-z) = q z)
    (hq0 : ∀ z, 0 ≤ q z) (beta : ℝ) (N : ℕ) (hβN : 0 ≤ beta / N) (hh : Measurable (h N))
    (cB : ℝ) (hup : ∀ y, beta * HRS.Whole.convMeasure q mu y + h N y ≤ cB)
    (pins : Fin p → Euc d) (i : Fin (m + 1))
    (h1 : IsProbabilityMeasure (referenceLaw q h mu beta N (m + 1) pins))
    (g : EucConfig d (m + 1) → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ X, ∫⁻ y, g (Function.update X i y) ∂resampleLaw q h mu beta N pins i X
        ∂referenceLaw q h mu beta N (m + 1) pins =
      ∫⁻ X, g X ∂referenceLaw q h mu beta N (m + 1) pins := by
  obtain ⟨c0, ctop, hr⟩ := s82p2_ref_of_prob (n := m + 1) (mu := mu) hq beta N hh pins h1
  set c := (s82p2_W q h mu beta N pins : Measure (EucConfig d (m + 1))) Set.univ with hc
  have hVm := s82q_V_measurable_swap (m := m) (mu := mu) hq beta N hh pins
  have hVb : ∀ (X' : Fin m → Euc d) (y : Euc d), s82q_V q h mu beta N pins X' y ≤ cB := by
    intro X' y
    unfold s82q_V s82p2_site
    have h2 : 0 ≤ (beta / N) * ∑ j, q (y - pins j) :=
      mul_nonneg hβN (Finset.sum_nonneg fun j _ => hq0 _)
    have h3 : 0 ≤ (beta / N) * ∑ j, q (X' j - y) :=
      mul_nonneg hβN (Finset.sum_nonneg fun j _ => hq0 _)
    linarith [hup y]
  have hes := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => Euc d) i).symm.measurable
  have hVy : ∀ X' : Fin m → Euc d, Measurable (s82q_V q h mu beta N pins X') := fun X' =>
    hVm.comp measurable_prodMk_right
  have hVm' := s82q_V_measurable (m := m) (mu := mu) hq beta N hh pins
  have hfm : Measurable (fun r : (Fin m → Euc d) × Euc d =>
      ENNReal.ofReal (Real.exp (s82q_V q h mu beta N pins r.1 r.2))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hVm')
  let ζ : (Fin m → Euc d) → ℝ≥0∞ := fun X' =>
    ∫⁻ y, ENNReal.ofReal (Real.exp (s82q_V q h mu beta N pins X' y)) ∂mu
  have hζ : ∀ X', ENNReal.ofReal (∫ x, Real.exp (s82q_V q h mu beta N pins X' x) ∂mu) = ζ X' ∧
      ζ X' ≠ 0 ∧ ζ X' ≠ ⊤ := by
    intro X'
    obtain ⟨a, b, c'⟩ := s82q_zeta mu (s82q_V q h mu beta N pins X') (hVy X') cB (hVb X')
    exact ⟨a, fun h0 => b (a.trans h0), fun ht => c' (a.trans ht)⟩
  let Gh : (Fin m → Euc d) → ℝ≥0∞ := fun X' => (ζ X')⁻¹ *
    ∫⁻ y, ENNReal.ofReal (Real.exp (s82q_V q h mu beta N pins X' y)) * g (i.insertNth y X') ∂mu
  have hgm : Measurable (fun r : (Fin m → Euc d) × Euc d => g (i.insertNth r.2 r.1)) :=
    hg.comp (hes.comp measurable_swap)
  have hζm : Measurable ζ := hfm.lintegral_prod_right'
  have hGm : Measurable Gh := hζm.inv.mul (hfm.mul hgm).lintegral_prod_right'
  have hrem : Measurable (fun X : EucConfig d (m + 1) => fun j : Fin m => X (i.succAbove j)) :=
    measurable_pi_iff.2 fun j => measurable_pi_apply (i.succAbove j)
  -- Step 1: the inner integral is a function of the other coordinates
  have claim : ∀ (z : Euc d) (X' : Fin m → Euc d),
      ∫⁻ y, g (Function.update (i.insertNth z X' : EucConfig d (m + 1)) i y)
        ∂resampleLaw q h mu beta N pins i (i.insertNth z X' : EucConfig d (m + 1)) = Gh X' := by
    intro z X'
    have hfun : (fun y => g (Function.update (i.insertNth z X' : EucConfig d (m + 1)) i y)) =
        fun y => g (i.insertNth y X') := funext fun y => by rw [s82p2_update_insertNth]
    have hgy : Measurable (fun y => g (i.insertNth y X')) :=
      hg.comp (hes.comp measurable_prodMk_right)
    rw [hfun, s82q_res_insertNth hqe, s82q_tilt_lintegral mu _ (hVy X') _ hgy, (hζ X').1]
  have step1 : ∀ X : EucConfig d (m + 1),
      ∫⁻ y, g (Function.update X i y) ∂resampleLaw q h mu beta N pins i X =
        Gh (fun j => X (i.succAbove j)) := by
    intro X
    have := claim (X i) (fun j => X (i.succAbove j))
    rwa [s82q_insertNth_removeNth] at this
  simp_rw [step1]
  have hFm : Measurable (fun X : EucConfig d (m + 1) => Gh (fun j => X (i.succAbove j))) :=
    hGm.comp hrem
  have hFins : ∀ (z : Euc d) (X' : Fin m → Euc d),
      Gh (fun j => (i.insertNth z X' : EucConfig d (m + 1)) (i.succAbove j)) = Gh X' := by
    intro z X'
    congr 1
    funext j
    simp
  rw [hr, lintegral_smul_measure, lintegral_smul_measure, smul_eq_mul, smul_eq_mul]
  congr 1
  rw [s82q_W_swap hq hqe beta N hh pins i _ hFm, s82q_W_swap hq hqe beta N hh pins i _ hg]
  refine lintegral_congr fun X' => ?_
  congr 1
  simp_rw [hFins]
  have hamX : AEMeasurable (fun z => ENNReal.ofReal (Real.exp (s82q_V q h mu beta N pins X' z))) mu :=
    (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (hVy X'))).aemeasurable
  rw [lintegral_mul_const'' _ hamX]
  show ζ X' * Gh X' = _
  show ζ X' * ((ζ X')⁻¹ * _) = _
  rw [← mul_assoc, ENNReal.mul_inv_cancel (hζ X').2.1 (hζ X').2.2, one_mul]

end HRS.MS.S82Q
