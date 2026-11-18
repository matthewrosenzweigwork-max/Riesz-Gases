import HRS.Uniform.Q45Lind4

/-!
# Q45: the generalised finite-dimensional martingale CLT (Hessian pairing seminorm, `ℱ₀`-shift)
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.Uniform.Q45

open HRS HRS.LindebergAux

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
variable {p : ℕ}

local notation "ℝ^" p => EuclideanSpace ℝ (Fin p)

lemma gs_sub_le {h h' : (ℝ^p) → ℝ} (hh : ContDiff ℝ 2 h) {H : ℝ}
    (hH : ∀ x, ‖iteratedFDeriv ℝ 2 h x‖ ≤ H) (hh' : ContDiff ℝ 2 h') {H' : ℝ}
    (hH' : ∀ x, ‖iteratedFDeriv ℝ 2 h' x‖ ≤ H') {δ : ℝ} (hδ : ∀ x, |h' x - h x| ≤ δ)
    (Q : Matrix (Fin p) (Fin p) ℝ) (x : ℝ^p) : |gaussSmooth h' Q x - gaussSmooth h Q x| ≤ δ := by
  unfold gaussSmooth
  rw [← integral_sub (integrable_shift_gaussian hh' hH' _ x) (integrable_shift_gaussian hh hH _ x)]
  have := norm_integral_le_of_norm_le_const (μ := multivariateGaussian (0 : ℝ^p) Q) (C := δ)
    (f := fun y => h' (x + y) - h (x + y)) (ae_of_all _ fun y => by
      rw [Real.norm_eq_abs]; exact hδ _)
  simpa using this

/-- Generalised Lemma A.21 (finite-dimensional): the Hessian pairing seminorm `ν` replaces the trace
norm, and the test function is shifted by an `ℱ₀`-measurable random vector. -/
theorem clt_gen (ℱ : Filtration ℝ mΩ) (t : ℝ) (ht : 0 ≤ t)
    (M : ℝ → Ω → (ℝ^p)) (Sg : ℝ → Ω → Matrix (Fin p) (Fin p) ℝ)
    {adm : ℝ → ℝ → Prop} (hM : CellIface P ℱ t M Sg adm)
    (sb : ℝ → Matrix (Fin p) (Fin p) ℝ) (hsbmeas : Measurable sb)
    (hsbint : IntegrableOn (fun σ => s1Norm (sb σ)) (Set.Icc 0 t))
    (hsbpsd : ∀ σ ∈ Set.Icc 0 t, (sb σ).PosSemidef)
    {ν : Matrix (Fin p) (Fin p) ℝ → ℝ} {Cν : ℝ} (hν : PairNorm ν Cν)
    (ξ : Ω → ℝ^p) (hξ : StronglyMeasurable[ℱ 0] ξ)
    (h : (ℝ^p) → ℝ) (hh : ContDiff ℝ 2 h) (H Hp B0 G1 : ℝ) (hHp : 0 ≤ Hp)
    (hH : ∀ x, ‖iteratedFDeriv ℝ 2 h x‖ ≤ H)
    (hB0 : ∀ x, |h x| ≤ B0) (hG1 : ∀ x, ‖fderiv ℝ h x‖ ≤ G1)
    (hpair : ∀ x Q', |hessPair h x Q'| ≤ Hp * ν Q')
    (nn : ℕ → ℕ) (hnn : Tendsto nn atTop atTop) (hn1 : ∀ ℓ, 1 ≤ nn ℓ)
    (hadm : ∀ ℓ, ∀ k < nn ℓ, adm (unifPart t (nn ℓ) k) (unifPart t (nn ℓ) (k + 1)))
    (htendM : ∀ H L : ℝ, 0 ≤ H → 0 ≤ L → Tendsto (fun ℓ : ℕ => ∑ k ∈ Finset.range (nn ℓ),
        ∫ ω, taylorRem H L (M (unifPart t (nn ℓ) (k + 1)) ω - M (unifPart t (nn ℓ) k) ω) ∂P)
      atTop (𝓝 0)) :
    |∫ ω, h (ξ ω + M t ω) ∂P - ∫ ω, gaussSmooth h (covBlock sb 0 t) (ξ ω) ∂P| ≤
      (1 / 2) * Hp * ∫ ω, (∫ σ in Set.Icc 0 t, ν (Sg σ ω - sb σ)) ∂P := by
  classical
  have hHn : 0 ≤ H := (norm_nonneg _).trans (hH 0)
  have hent := sb_entry_integrableOn hsbmeas hsbint hsbpsd
  have hGpsd : (covBlock sb 0 t).PosSemidef := covBlock_psd hsbpsd hent le_rfl le_rfl
  set J := ∫ ω, (∫ σ in Set.Icc 0 t, ν (Sg σ ω - sb σ)) ∂P with hJ
  have hJ0 : 0 ≤ J := integral_nonneg fun ω =>
    setIntegral_nonneg measurableSet_Icc fun σ _ => hν.nonneg _
  have hξm : StronglyMeasurable ξ := hξ.mono (ℱ.le 0)
  have hMm : ∀ τ ∈ Set.Icc (0 : ℝ) t, StronglyMeasurable (M τ) := fun τ hτ =>
    (stronglyMeasurable_of_coord fun a => hM.adapted τ hτ a).mono (ℱ.le τ)
  have key : ∀ ε : ℝ, 0 < ε →
      |∫ ω, h (ξ ω + M t ω) ∂P - ∫ ω, gaussSmooth h (covBlock sb 0 t) (ξ ω) ∂P| ≤
        (1 / 2) * Hp * J + H * (ε ^ 2 * p) := by
    intro ε hε
    set Qe : Matrix (Fin p) (Fin p) ℝ := ε ^ 2 • (1 : Matrix (Fin p) (Fin p) ℝ) with hQe
    have hQpd : Qe.PosDef := Matrix.PosDef.one.smul (by positivity)
    obtain ⟨happ, L, hL⟩ := gaussSmooth_approx Qe hQpd h hh H hH
    have hQtr : Qe.trace = ε ^ 2 * p := by simp [hQe, Matrix.trace_smul]
    obtain ⟨he2, heH, -⟩ := gaussSmooth_hessian Qe hQpd.posSemidef h hh H hH
    set he := gaussSmooth h Qe with hhe
    have hL' : ∀ x y, ‖iteratedFDeriv ℝ 2 he x - iteratedFDeriv ℝ 2 he y‖ ≤ max L 0 * ‖x - y‖ :=
      fun x y => (hL x y).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
    set δ := (1 / 2) * H * (ε ^ 2 * p) with hδdef
    have hδ : ∀ x, |he x - h x| ≤ δ := fun x => by
      have := happ x
      rwa [hQtr] at this
    have hBe : ∀ x, |he x| ≤ B0 := fun x => gs_abs_le hB0 Qe x
    have hGe : ∀ x, ‖fderiv ℝ he x‖ ≤ G1 := fun x => gs_fderiv_le hh hH hG1 Qe x
    have hPe : ∀ x Q', |hessPair he x Q'| ≤ Hp * ν Q' := gs_hessPair_le hh hH hpair Qe
    have iPh : Integrable (fun ω => h (ξ ω + M t ω)) P :=
      Integrable.of_bound (hh.continuous.comp_aestronglyMeasurable
        (hξm.add (hMm t ⟨ht, le_rfl⟩)).aestronglyMeasurable) B0
        (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hB0 _)
    have iPe : Integrable (fun ω => he (ξ ω + M t ω)) P :=
      Integrable.of_bound (he2.continuous.comp_aestronglyMeasurable
        (hξm.add (hMm t ⟨ht, le_rfl⟩)).aestronglyMeasurable) B0
        (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hBe _)
    set Qt := covBlock sb 0 t with hQt
    have iGh : Integrable (fun ω => gaussSmooth h Qt (ξ ω)) P :=
      Integrable.of_bound ((gaussSmooth_hessian Qt hGpsd h hh H hH).1.continuous.comp_aestronglyMeasurable
        hξm.aestronglyMeasurable) B0
        (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact gs_abs_le hB0 Qt _)
    have iGe : Integrable (fun ω => gaussSmooth he Qt (ξ ω)) P :=
      Integrable.of_bound ((gaussSmooth_hessian Qt hGpsd he he2 H heH).1.continuous.comp_aestronglyMeasurable
        hξm.aestronglyMeasurable) B0
        (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact gs_abs_le hBe Qt _)
    have d1 : |∫ ω, h (ξ ω + M t ω) ∂P - ∫ ω, he (ξ ω + M t ω) ∂P| ≤ δ := by
      rw [← integral_sub iPh iPe, ← Real.norm_eq_abs]
      have := norm_integral_le_of_norm_le_const (μ := P) (C := δ)
        (f := fun ω => h (ξ ω + M t ω) - he (ξ ω + M t ω))
        (ae_of_all _ fun ω => by rw [Real.norm_eq_abs, abs_sub_comm]; exact hδ _)
      simpa using this
    have d2 : |∫ ω, gaussSmooth h Qt (ξ ω) ∂P - ∫ ω, gaussSmooth he Qt (ξ ω) ∂P| ≤ δ := by
      rw [← integral_sub iGh iGe, ← Real.norm_eq_abs]
      have := norm_integral_le_of_norm_le_const (μ := P) (C := δ)
        (f := fun ω => gaussSmooth h Qt (ξ ω) - gaussSmooth he Qt (ξ ω))
        (ae_of_all _ fun ω => by
          rw [Real.norm_eq_abs, abs_sub_comm]
          exact gs_sub_le hh hH he2 heH hδ Qt _)
      simpa using this
    have hL0 : 0 ≤ max L 0 := le_max_right _ _
    have hS := htendM H (max L 0) hHn hL0
    have hG := (gaussian_lindeberg_tendsto t ht sb hsbmeas hsbint hsbpsd H (max L 0) hHn hL0).comp hnn
    have hlim : Tendsto (fun ℓ : ℕ => (1 / 2) * Hp * J + 2 * δ +
        ((∑ k ∈ Finset.range (nn ℓ), ∫ ω, taylorRem H (max L 0)
            (M (unifPart t (nn ℓ) (k + 1)) ω - M (unifPart t (nn ℓ) k) ω) ∂P) +
         ∑ k ∈ Finset.range (nn ℓ), ∫ y, taylorRem H (max L 0) y ∂(ProbabilityTheory.multivariateGaussian 0
          (covBlock sb (unifPart t (nn ℓ) k) (unifPart t (nn ℓ) (k + 1)))))) atTop
        (𝓝 ((1 / 2) * Hp * J + 2 * δ + (0 + 0))) :=
      tendsto_const_nhds.add (hS.add hG)
    have hfin : |∫ ω, h (ξ ω + M t ω) ∂P - ∫ ω, gaussSmooth h Qt (ξ ω) ∂P| ≤
        (1 / 2) * Hp * J + 2 * δ + (0 + 0) := by
      refine ge_of_tendsto hlim ?_
      refine Filter.Eventually.of_forall fun ℓ => ?_
      have hb := partition_bound_gen P ℱ t ht M Sg hM sb hsbmeas hsbint hsbpsd hν ξ hξ he he2 H
        (max L 0) Hp B0 G1 hHp heH hL' hBe hGe hPe (nn ℓ) (hn1 ℓ) (hadm ℓ)
      rw [Finset.sum_add_distrib] at hb
      have e : ∫ ω, h (ξ ω + M t ω) ∂P - ∫ ω, gaussSmooth h Qt (ξ ω) ∂P =
          (∫ ω, he (ξ ω + M t ω) ∂P - ∫ ω, gaussSmooth he Qt (ξ ω) ∂P) +
            (∫ ω, h (ξ ω + M t ω) ∂P - ∫ ω, he (ξ ω + M t ω) ∂P) -
            (∫ ω, gaussSmooth h Qt (ξ ω) ∂P - ∫ ω, gaussSmooth he Qt (ξ ω) ∂P) := by ring
      rw [e]
      have a1 := abs_le.1 hb
      have a2 := abs_le.1 d1
      have a3 := abs_le.1 d2
      rw [abs_le]
      constructor <;> linarith [a1.1, a1.2, a2.1, a2.2, a3.1, a3.2]
    have : 2 * δ = H * (ε ^ 2 * p) := by rw [hδdef]; ring
    linarith
  refine le_of_forall_pos_le_add fun η hη => ?_
  have hpos : 0 < H * p + 1 := by positivity
  set ε := Real.sqrt (η / (H * p + 1)) with hεdef
  have hε : 0 < ε := Real.sqrt_pos.2 (by positivity)
  have hε2 : ε ^ 2 = η / (H * p + 1) := Real.sq_sqrt (by positivity)
  have := key ε hε
  have h3 : H * (ε ^ 2 * p) ≤ η := by
    rw [hε2]
    have : H * (η / (H * p + 1) * p) = η * (H * p) / (H * p + 1) := by field_simp
    rw [this, div_le_iff₀ hpos]
    nlinarith [mul_nonneg hHn (Nat.cast_nonneg p : (0 : ℝ) ≤ p)]
  linarith

end HRS.Uniform.Q45
