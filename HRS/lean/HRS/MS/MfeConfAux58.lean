import HRS.MS.MfeConfAux57

/-!
# S.B.1, packet F6 (part 20): the limit of the source integral as the mollification is removed

`sb1_src_limit`: `∫_0^t ∫ u_{w_n,s} S_s dx ds → ∫_0^t ∫ S_s dμ_s ds` (and the integrability of the limit function).
-/

open MeasureTheory Filter Topology InformationTheory
open HRS HRS.Whole HRS.MP.SelfSimP4 HRS.MP.SelfSimP4Mol HRS.MP.SelfSimP4Impl
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MS.MfeConf

variable {d N : ℕ}

section
variable {θ T : ℝ} {b w : ℝ → EucConfig d N → EucConfig d N} {H : EucConfig d N → ℝ}
  {Ψ Wψ : ℝ → EucConfig d N → ℝ} {CΨ Bw Kw CS : ℝ → ℝ}
  {μ : ℝ → Measure (EucConfig d N)} {Kl : ℝ≥0} {B K M CV : ℝ} {v : ℝ}

theorem sb1_Fv_bound (hP : P4MolData θ T b (fun _ => H) (fun _ _ => 0) μ Kl B K M CV)
    (hΨ : Sb1Tilt θ T b w Ψ Wψ CΨ Bw Kw CS) (hv : 0 < v) (s : ℝ) :
    ‖∫ x, p4Mol v (μ s) x * sb1S θ b w Wψ s x‖ ≤ CS s * sb1Cu d N v M := by
  haveI := hP.prob s
  have hm := hP.hm s
  have hCS := (hΨ.nn s).2.2.2
  have hgi : Integrable (fun x => CS s * ((1 + p4m_q x) * p4Mol v (μ s) x)) :=
    (p4m_integrable_q_mol hv hm).const_mul _
  have hpt : ∀ x, ‖p4Mol v (μ s) x * sb1S θ b w Wψ s x‖ ≤ CS s * ((1 + p4m_q x) * p4Mol v (μ s) x) := by
    intro x
    have hu := p4m_mol_pos hv hm x
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hu]
    have h1 := hΨ.Sg s x
    calc p4Mol v (μ s) x * |sb1S θ b w Wψ s x| ≤ p4Mol v (μ s) x * (CS s * (1 + p4m_q x)) := by gcongr
      _ = _ := by ring
  refine (norm_integral_le_of_norm_le hgi (Filter.Eventually.of_forall hpt)).trans ?_
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left (sb1_int_q_mol_le hv hm (hP.hM s)) hCS

theorem sb1_src_limit (hP : P4MolData θ T b (fun _ => H) (fun _ _ => 0) μ Kl B K M CV)
    (hΨ : Sb1Tilt θ T b w Ψ Wψ CΨ Bw Kw CS) {DS : ℝ → ℝ} (hDS0 : ∀ s, 0 ≤ DS s)
    (hDSi : IntegrableOn DS (Set.Icc 0 T))
    (hSlip : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ x y : EucConfig d N,
      |sb1S θ b w Wψ s x - sb1S θ b w Wψ s y| ≤ DS s * ‖x - y‖ * (1 + ‖x‖ + ‖y‖))
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) {wn : ℕ → ℝ} (hw : ∀ n, 0 < wn n) (hw0 : Tendsto wn atTop (𝓝 0)) :
    Tendsto (fun n => ∫ s in Set.Icc (0 : ℝ) t, ∫ x, p4Mol (wn n) (μ s) x * sb1S θ b w Wψ s x) atTop
      (𝓝 (∫ s in Set.Icc (0 : ℝ) t, ∫ y, sb1S θ b w Wψ s y ∂(μ s))) ∧
    IntegrableOn (fun s => ∫ y, sb1S θ b w Wψ s y ∂(μ s)) (Set.Icc 0 T) := by
  have hM0 := sb1_M_nonneg hP
  have hSc := sb1_S_cont hP hΨ θ
  set c : ℝ := ((N * d : ℕ) : ℝ) with hc
  set ε : ℕ → ℝ := fun n => Real.sqrt (wn n) * (1 / 2 + 3 / 2 * c) + c * wn n + Real.sqrt (wn n) * M with hε
  have hε0 : Tendsto ε atTop (𝓝 0) := by
    have hs : Tendsto (fun n => Real.sqrt (wn n)) atTop (𝓝 0) := by
      have h := (Real.continuous_sqrt.tendsto 0).comp hw0
      rw [Real.sqrt_zero] at h
      exact h
    have h := ((hs.mul_const (1 / 2 + 3 / 2 * c)).add (hw0.const_mul c)).add (hs.mul_const M)
    simp only [zero_mul, mul_zero, add_zero] at h
    exact h
  -- the quantitative estimate
  have hest : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ n, ‖(∫ x, p4Mol (wn n) (μ s) x * sb1S θ b w Wψ s x) -
      ∫ y, sb1S θ b w Wψ s y ∂(μ s)‖ ≤ DS s * ε n := by
    intro s hs n
    haveI := hP.prob s
    rw [Real.norm_eq_abs]
    exact sb1_mol_approx (hw n) (hP.hm s) (hP.hM s) (hSc.comp (Continuous.prodMk continuous_const continuous_id))
      (hΨ.nn s).2.2.2 (hΨ.Sg s) (hDS0 s) (hSlip s hs)
  have hlim : ∀ s ∈ Set.Icc (0 : ℝ) T, Tendsto (fun n => ∫ x, p4Mol (wn n) (μ s) x * sb1S θ b w Wψ s x) atTop
      (𝓝 (∫ y, sb1S θ b w Wψ s y ∂(μ s))) := by
    intro s hs
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => hest s hs n) ?_
    simpa using hε0.const_mul (DS s)
  have hGaesm : AEStronglyMeasurable (fun s => ∫ y, sb1S θ b w Wψ s y ∂(μ s)) (volume.restrict (Set.Icc 0 T)) := by
    refine aestronglyMeasurable_of_tendsto_ae (u := atTop) (f := fun (n : ℕ) (s : ℝ) =>
      ∫ x, p4Mol (wn n) (μ s) x * sb1S θ b w Wψ s x) (fun n => sb1_Fv_aesm hP hΨ (hw n)) ?_
    exact (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun s hs => hlim s hs)
  have hGint : IntegrableOn (fun s => ∫ y, sb1S θ b w Wψ s y ∂(μ s)) (Set.Icc 0 T) := by
    refine Integrable.mono' ((hΨ.intS.mul_const (1 + M))) hGaesm ?_
    exact (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun s hs => sb1_G_bound hP hΨ s)
  refine ⟨?_, hGint⟩
  have hsub : Set.Icc (0 : ℝ) t ⊆ Set.Icc 0 T := Set.Icc_subset_Icc le_rfl ht.2
  have hGt : IntegrableOn (fun s => ∫ y, sb1S θ b w Wψ s y ∂(μ s)) (Set.Icc 0 t) := hGint.mono_set hsub
  have hFt : ∀ n, IntegrableOn (fun s => ∫ x, p4Mol (wn n) (μ s) x * sb1S θ b w Wψ s x) (Set.Icc 0 t) := by
    intro n
    refine Integrable.mono' ((hΨ.intS.mono_set hsub).mul_const (sb1Cu d N (wn n) M))
      ((sb1_Fv_aesm hP hΨ (hw n)).mono_measure (Measure.restrict_mono hsub le_rfl)) ?_
    exact (ae_restrict_iff' measurableSet_Icc).2
      (Filter.Eventually.of_forall fun s hs => sb1_Fv_bound hP hΨ (hw n) s)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hDt : IntegrableOn DS (Set.Icc 0 t) := hDSi.mono_set hsub
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) (by simpa using hε0.mul_const (∫ s in Set.Icc (0 : ℝ) t, DS s))
  rw [← integral_sub (hFt n) hGt]
  have hmaj : IntegrableOn (fun s => DS s * ε n) (Set.Icc 0 t) := hDt.mul_const _
  refine (norm_integral_le_of_norm_le hmaj ((ae_restrict_iff' measurableSet_Icc).2
    (Filter.Eventually.of_forall fun s hs => hest s (hsub hs) n))).trans (le_of_eq ?_)
  rw [integral_mul_const, mul_comm]

end

end HRS.MS.MfeConf
