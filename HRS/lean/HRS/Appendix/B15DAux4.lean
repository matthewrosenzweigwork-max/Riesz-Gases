import HRS.Appendix.B15DAux3

/-!
# Packet D2 (proofs, part 4): expectation form of the Itô duality

Relocated proof of `d1_ito_expectation` (Fubini on the Dynkin form `d1_ito_pathwise_proof`).  The frozen
sorried statement lives in `HRS/Appendix/B15DAux1.lean`; this file restates it verbatim as
`d1_ito_expectation_proof`.  Helpers are prefixed `b15d2_`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace HRS

section D2proofs4

variable {d N : ℕ}

/-- Joint continuity of the clamped Itô generator `(s,y) ↦ d1_itoGen (clamp s) y`. -/
theorem b15d2_itoGen_clamp_continuous {T : ℝ} (hT : 0 ≤ T) {f : ℝ → (Fin N → Euc d) → ℝ}
    (hf : IsC12On T Set.univ f) {κ : ℝ} {bC : Config d N → Fin N → Euc d}
    (hbC : Continuous (d1_liftDrift bC)) :
    Continuous (fun p : ℝ × (Fin N → Euc d) => d1_itoGen κ bC T f (clampTI T p.1) p.2) := by
  have hq : Continuous (fun q : ℝ × (Fin N → Euc d) => (clampTI T q.1, q.2)) :=
    ((continuous_clampTI T).comp continuous_fst).prodMk continuous_snd
  have hmem : ∀ q : ℝ × (Fin N → Euc d),
      (clampTI T q.1, q.2) ∈ Icc 0 T ×ˢ (univ : Set (Fin N → Euc d)) :=
    fun q => ⟨clampTI_mem hT q.1, mem_univ _⟩
  have h1 : Continuous (fun q : ℝ × (Fin N → Euc d) =>
      derivWithin (fun r => f r q.2) (Icc 0 T) (clampTI T q.1)) :=
    ContinuousOn.comp_continuous hf.cont_deriv hq hmem
  have h2 : Continuous (fun q : ℝ × (Fin N → Euc d) =>
      fderiv ℝ (f (clampTI T q.1)) q.2 (d1_liftDrift bC q.2)) :=
    (ContinuousOn.comp_continuous hf.cont_fderiv hq hmem).clm_apply (hbC.comp continuous_snd)
  have h3 : ∀ k : Fin N × Fin d, Continuous (fun q : ℝ × (Fin N → Euc d) =>
      fderiv ℝ (fderiv ℝ (f (clampTI T q.1))) q.2 (d1_noise d N κ k) (d1_noise d N κ k)) := by
    intro k
    exact ((ContinuousOn.comp_continuous hf.cont_fderiv₂ hq hmem).clm_apply
      continuous_const).clm_apply continuous_const
  unfold d1_itoGen
  exact (h1.add h2).add (continuous_const.mul (continuous_finset_sum _ fun k _ => h3 k))

/-- Uniform bound of the Itô generator on `[0,T] × (ℝ^d)^N`, given the pointwise bounds `hC` on
`f` and a bound `C'` on the lifted drift (periodic, so bounded). -/
theorem b15d2_itoGen_bound {T : ℝ} {f : ℝ → (Fin N → Euc d) → ℝ} {κ : ℝ}
    {bC : Config d N → Fin N → Euc d} {C C' : ℝ}
    (hC : ∀ s ∈ Set.Icc 0 T, ∀ y, |f s y| ≤ C ∧ ‖fderiv ℝ (f s) y‖ ≤ C ∧
      ‖fderiv ℝ (fderiv ℝ (f s)) y‖ ≤ C ∧ |derivWithin (fun r => f r y) (Set.Icc 0 T) s| ≤ C)
    (hC' : ∀ y, ‖d1_liftDrift bC y‖ ≤ C') {s : ℝ} (hs : s ∈ Set.Icc 0 T) (y : Fin N → Euc d) :
    |d1_itoGen κ bC T f s y| ≤ C + C * C' +
      (1 / 2) * ∑ k : Fin N × Fin d, C * (‖d1_noise d N κ k‖ * ‖d1_noise d N κ k‖) := by
  obtain ⟨_, hA, hB, hD⟩ := hC s hs y
  have hC0 : 0 ≤ C := (norm_nonneg _).trans hA
  unfold d1_itoGen
  have e2 : |fderiv ℝ (f s) y (d1_liftDrift bC y)| ≤ C * C' := by
    rw [← Real.norm_eq_abs]
    calc ‖fderiv ℝ (f s) y (d1_liftDrift bC y)‖
        ≤ ‖fderiv ℝ (f s) y‖ * ‖d1_liftDrift bC y‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ C * C' := mul_le_mul hA (hC' y) (norm_nonneg _) hC0
  have hk : ∀ k : Fin N × Fin d,
      |fderiv ℝ (fderiv ℝ (f s)) y (d1_noise d N κ k) (d1_noise d N κ k)|
        ≤ C * (‖d1_noise d N κ k‖ * ‖d1_noise d N κ k‖) := by
    intro k
    rw [← Real.norm_eq_abs]
    calc ‖fderiv ℝ (fderiv ℝ (f s)) y (d1_noise d N κ k) (d1_noise d N κ k)‖
        ≤ ‖fderiv ℝ (fderiv ℝ (f s)) y (d1_noise d N κ k)‖ * ‖d1_noise d N κ k‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ (‖fderiv ℝ (fderiv ℝ (f s)) y‖ * ‖d1_noise d N κ k‖) * ‖d1_noise d N κ k‖ :=
          mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
      _ ≤ (C * ‖d1_noise d N κ k‖) * ‖d1_noise d N κ k‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hB (norm_nonneg _)) (norm_nonneg _)
      _ = C * (‖d1_noise d N κ k‖ * ‖d1_noise d N κ k‖) := by ring
  have e3 : |(1 / 2 : ℝ) * ∑ k : Fin N × Fin d,
      fderiv ℝ (fderiv ℝ (f s)) y (d1_noise d N κ k) (d1_noise d N κ k)|
        ≤ (1 / 2) * ∑ k : Fin N × Fin d, C * (‖d1_noise d N κ k‖ * ‖d1_noise d N κ k‖) := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    exact mul_le_mul_of_nonneg_left
      ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => hk k)) (by norm_num)
  exact (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add hD e2)) e3)

/-- Proof of `d1_ito_expectation`: integrate the Dynkin form `d1_ito_pathwise_proof`; the drift term is
a bounded jointly continuous function of `(s, Y_s)` (clamped in time), so Fubini applies. -/
theorem d1_ito_expectation_proof {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}
    (hW' : IsBrownianFiltration P ℱ W') {κ : ℝ} (hκ : 0 ≤ κ) {bC : Config d N → Fin N → Euc d}
    (hbC : Continuous (d1_liftDrift bC)) {Y₀ : Ω → Fin N → Euc d}
    (hY₀ : ∀ t : ℝ, Measurable[ℱ t] Y₀) {Y : ℝ → Ω → Fin N → Euc d}
    (hY : IsAdditiveSDESolution P ℱ W' (fun _ => d1_liftDrift bC) (d1_noise d N κ) Y₀
      (fun _ => ⊤) Y)
    {T : ℝ} (hT : 0 ≤ T) {f : ℝ → (Fin N → Euc d) → ℝ} (hf : IsC12On T Set.univ f)
    (hbd : ∃ C : ℝ, ∀ s ∈ Set.Icc 0 T, ∀ y, |f s y| ≤ C ∧ ‖fderiv ℝ (f s) y‖ ≤ C ∧
      ‖fderiv ℝ (fderiv ℝ (f s)) y‖ ≤ C ∧ |derivWithin (fun r => f r y) (Set.Icc 0 T) s| ≤ C)
    {t : ℝ} (ht : t ∈ Set.Icc 0 T) :
    ∫ ω, f t (Y t ω) ∂P = ∫ ω, f 0 (Y 0 ω) ∂P +
      ∫ s in Set.Icc (0 : ℝ) t, ∫ ω, d1_itoGen κ bC T f s (Y s ω) ∂P := by
  obtain ⟨M, hMint, hM0, hMae⟩ := d1_ito_pathwise_proof hW' hκ hbC hY₀ hY hT hf hbd t ht
  obtain ⟨C, hC⟩ := hbd
  obtain ⟨C', hC'⟩ := bounded_of_periodic (T := T) (fun _ y => d1_liftDrift bC y)
    (hbC.comp continuous_snd).continuousOn
    (fun _ Y v hv => by
      show bC _ = bC _
      rw [mk_add_lattice_vec hv Y])
  have hC'' : ∀ y, ‖d1_liftDrift bC y‖ ≤ C' := fun y => hC' 0 ⟨le_refl (0 : ℝ), hT⟩ y
  have hY0 : Y 0 = Y₀ := funext hY.init
  have hY0' : ∀ s : ℝ, Measurable[ℱ s] (Y 0) := fun s => by rw [hY0]; exact hY₀ s
  have hYad : ∀ u : ℝ, 0 ≤ u → Measurable[ℱ u] (Y u) := fun u _ => hY.adapted u
  have hYcI : ∀ ω, ContinuousOn (fun s => Y s ω) (Set.Ici 0) := fun ω =>
    b15d2_contOn_Ici (fun u hu => hY.cont ω u hu (WithTop.coe_lt_top _))
  have hZprog : IsProgressive ℱ (fun s ω => Y (max s 0) ω) :=
    b15d2_isProgressive_clampPath hY0' hYad hYcI
  have hZm : Measurable (fun p : ℝ × Ω => Y (max p.1 0) p.2) :=
    measurable_of_progressive hZprog
  -- the Fubini integrand
  have hFm : Measurable (fun p : ℝ × Ω => d1_itoGen κ bC T f (clampTI T p.1) (Y (max p.1 0) p.2)) :=
    (b15d2_itoGen_clamp_continuous hT hf hbC).measurable.comp (measurable_fst.prodMk hZm)
  have hFb : ∀ p : ℝ × Ω, ‖d1_itoGen κ bC T f (clampTI T p.1) (Y (max p.1 0) p.2)‖ ≤
      C + C * C' + (1 / 2) * ∑ k : Fin N × Fin d, C * (‖d1_noise d N κ k‖ * ‖d1_noise d N κ k‖) :=
    fun p => by
      rw [Real.norm_eq_abs]
      exact b15d2_itoGen_bound hC hC'' (clampTI_mem hT p.1) _
  haveI : IsFiniteMeasure (volume.restrict (Set.Icc (0 : ℝ) t)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_Icc_lt_top⟩
  have hFint : Integrable (fun p : ℝ × Ω => d1_itoGen κ bC T f (clampTI T p.1) (Y (max p.1 0) p.2))
      ((volume.restrict (Set.Icc (0 : ℝ) t)).prod P) :=
    Integrable.of_bound hFm.aestronglyMeasurable _ (ae_of_all _ hFb)
  have hIint : Integrable (fun ω => ∫ s in Set.Icc (0 : ℝ) t,
      d1_itoGen κ bC T f (clampTI T s) (Y (max s 0) ω)) P :=
    hFint.integral_prod_right
  -- the integrand agrees with the drift on `[0,t]`
  have hpt : ∀ s ∈ Set.Icc (0 : ℝ) t, ∀ ω,
      d1_itoGen κ bC T f (clampTI T s) (Y (max s 0) ω) = d1_itoGen κ bC T f s (Y s ω) := by
    intro s hs ω
    have hsT : s ∈ Set.Icc 0 T := ⟨hs.1, hs.2.trans ht.2⟩
    rw [clampTI_of_mem hsT, max_eq_left hs.1]
  have hf0 : Integrable (fun ω => f 0 (Y 0 ω)) P := by
    have hc0 : Continuous (fun y : Fin N → Euc d => ((0 : ℝ), y)) := continuous_const.prodMk continuous_id
    have hcont0 : Continuous (fun y => f 0 y) :=
      ContinuousOn.comp_continuous (f := fun y : Fin N → Euc d => ((0 : ℝ), y)) hf.cont hc0
        (fun y => (⟨⟨le_refl (0 : ℝ), hT⟩, mem_univ y⟩ : ((0 : ℝ), y) ∈ Icc 0 T ×ˢ univ))
    have hm0 : Measurable (fun ω => f 0 (Y 0 ω)) :=
      hcont0.measurable.comp ((hY.adapted 0).mono (ℱ.le 0) le_rfl)
    exact Integrable.of_bound hm0.aestronglyMeasurable (C) (ae_of_all _ fun ω =>
      by rw [Real.norm_eq_abs]; exact (hC 0 ⟨le_refl (0 : ℝ), hT⟩ _).1)
  have hft : Integrable (fun ω => f t (Y t ω)) P := by
    have hct : Continuous (fun y : Fin N → Euc d => (t, y)) := continuous_const.prodMk continuous_id
    have hcont : Continuous (fun y => f t y) :=
      ContinuousOn.comp_continuous (f := fun y : Fin N → Euc d => (t, y)) hf.cont hct
        (fun y => (⟨ht, mem_univ y⟩ : (t, y) ∈ Icc 0 T ×ˢ univ))
    have hm : Measurable (fun ω => f t (Y t ω)) :=
      hcont.measurable.comp ((hY.adapted t).mono (ℱ.le t) le_rfl)
    exact Integrable.of_bound hm.aestronglyMeasurable (C) (ae_of_all _ fun ω =>
      by rw [Real.norm_eq_abs]; exact (hC t ht _).1)
  -- integrate the Dynkin identity
  have hfae : (fun ω => f t (Y t ω)) =ᵐ[P] (fun ω => f 0 (Y 0 ω) +
      (∫ s in Set.Icc (0 : ℝ) t, d1_itoGen κ bC T f (clampTI T s) (Y (max s 0) ω)) + M ω) := by
    filter_upwards [hMae] with ω hω
    rw [hω]
    congr 2
    exact setIntegral_congr_fun measurableSet_Icc (fun s hs => (hpt s hs ω).symm)
  have hswap := integral_integral_swap (μ := volume.restrict (Set.Icc (0 : ℝ) t)) (ν := P)
    (f := fun s ω => d1_itoGen κ bC T f (clampTI T s) (Y (max s 0) ω)) hFint
  have hA : Integrable (fun ω => f 0 (Y 0 ω) +
      ∫ s in Set.Icc (0 : ℝ) t, d1_itoGen κ bC T f (clampTI T s) (Y (max s 0) ω)) P := hf0.add hIint
  rw [integral_congr_ae hfae, integral_add hA hMint, integral_add hf0 hIint, hM0, add_zero]
  congr 1
  rw [← hswap]
  refine setIntegral_congr_fun measurableSet_Icc (fun s hs => ?_)
  exact integral_congr_ae (ae_of_all _ fun ω => hpt s hs ω)

example := (@d1_ito_expectation_proof : type_of% @d1_ito_expectation)

end D2proofs4

end HRS
