import HRS.MS.S11Q2A2

/-!
# S11.3 Q-regularity (worker S11Q2), A3: the chain inequality for `s113q_Data`

`s11q2_chain_ac`: for a reference `q` of class `C^{1,2}` (positive on `[0,T+1]`), an absolutely continuous exponent `p > 1`,
`s113b_Gp` is interval integrable on `[0,T]` and the power chain inequality `M(t) - M(s) ≤ ∫_s^t Gp` holds.
Proof: `s113b_chain_ac` for the Steklov averages `q_k` and `k → ∞` (A2, mass convergence of S113Q2, dominated convergence in `τ`).
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

open MeasureTheory Filter Topology Set intervalIntegral

namespace HRS.MS.S11Q2

open HRS.MS.S113X2B HRS.MS.S113X2C HRS.MS.S113Q

theorem s11q2_Gp_eq {n : ℕ} {ν : ℝ} {b : s113b_E n → s113b_E n} {q : ℝ → s113b_E n → ℝ} {T : ℝ}
    {u : ℝ → s113b_E n → ℝ} {K G : Set (s113b_E n)} {B : ℝ} (hD : s113q_Data ν b q T u K G B)
    (P : ℝ → ℝ) {τ : ℝ} (hτ : τ ∈ Icc 0 T) :
    s113b_Gp ν b q u P τ = (P τ - 1) * (∫ x, s113b_N ν b q τ x * (u τ x / q τ x) ^ (P τ)) +
      deriv P τ * ∫ x, q τ x * ((u τ x / q τ x) ^ (P τ) * Real.log (u τ x / q τ x)) := by
  have h1 : ∫ x, q τ x * s113b_R ν b q τ x * (u τ x / q τ x) ^ (P τ) =
      ∫ x, s113b_N ν b q τ x * (u τ x / q τ x) ^ (P τ) := by
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    show q τ x * (s113b_N ν b q τ x / q τ x) * _ = _
    rw [mul_div_cancel₀ _ (hD.hq0 τ ⟨hτ.1, hτ.2.trans (by linarith)⟩ x).ne']
  unfold s113b_Gp
  rw [h1]
  simp only [mul_assoc]

theorem s11q2_chain_ac {n : ℕ} {ν : ℝ} {b : s113b_E n → s113b_E n} {q : ℝ → s113b_E n → ℝ} {T : ℝ}
    {u : ℝ → s113b_E n → ℝ} {K G : Set (s113b_E n)} {B : ℝ} (hD : s113q_Data ν b q T u K G B) (hT : 0 ≤ T)
    {p : ℝ → ℝ} (hp : AbsolutelyContinuousOnInterval p 0 T) (hp1 : ∀ t ∈ Icc 0 T, 1 < p t) :
    IntervalIntegrable (s113b_Gp ν b q u p) volume 0 T ∧
      ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ T →
        s113b_M q u p t - s113b_M q u p s ≤ ∫ τ in s..t, s113b_Gp ν b q u p τ := by
  have hpc : ContinuousOn p (Icc 0 T) := by simpa [uIcc_of_le hT] using hp.continuousOn
  obtain ⟨P, hP⟩ := isCompact_Icc.exists_bound_of_continuousOn hpc
  have hpP : ∀ τ ∈ Icc (0 : ℝ) T, p τ ∈ Icc (1 : ℝ) P := fun τ hτ =>
    ⟨(hp1 τ hτ).le, (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hP τ hτ)⟩
  obtain ⟨CA, CC, k0, hbd, hlim⟩ := s11q2_spatial hD hpP
  set pt : ℝ → ℝ := fun τ => p (max 0 (min τ T)) with hpt
  have hptc : Continuous pt := hpc.comp_continuous (continuous_const.max (continuous_id.min continuous_const))
    (fun τ => ⟨le_max_left _ _, max_le hT (min_le_right _ _)⟩)
  have hptEq : ∀ τ ∈ Icc (0 : ℝ) T, pt τ = p τ := fun τ hτ => by
    simp [hpt, min_eq_left hτ.2, max_eq_right hτ.1]
  have hderivI : IntervalIntegrable (deriv p) volume 0 T := hp.intervalIntegrable_deriv
  have hderivM : AEStronglyMeasurable (deriv p) (volume.restrict (Ioc 0 T)) := hderivI.1.aestronglyMeasurable
  set Gk : ℕ → ℝ → ℝ := fun k => s113b_Gp ν b (s113q_qk q k) u p with hGk
  have hGkm : ∀ k, AEStronglyMeasurable (Gk k) (volume.restrict (Ioc 0 T)) := by
    intro k
    have hDk := s113q_Data_k hD k
    obtain ⟨Z, hZ0, hr⟩ := s113b_ratio hDk
    have hφ1 : Measurable (fun y : ℝ × ℝ => y.2 ^ y.1) := measurable_snd.pow measurable_fst
    have hφ2 : Measurable (fun y : ℝ × ℝ => y.2 ^ y.1 * Real.log y.2) := hφ1.mul (Real.measurable_log.comp measurable_snd)
    have famN := s113b_fam hDk (w := s113b_N ν b (s113q_qk q k)) (s113b_N_contB9 ν hDk.hb hDk.hq)
      (φ := fun e z => z ^ e) hr hφ1 (s113b_pow_props 1 1 Z one_pos hZ0)
    have famC := s113b_fam hDk (w := s113q_qk q k) hDk.hq.continuous (φ := fun e z => z ^ e * Real.log z) hr hφ2
      (s113b_log_props 1 1 Z one_pos hZ0)
    have hm : AEStronglyMeasurable (fun τ => (pt τ - 1) * (∫ x, s113b_N ν b (s113q_qk q k) τ x * (u τ x / s113q_qk q k τ x) ^ (pt τ)) +
        deriv p τ * ∫ x, s113q_qk q k τ x * ((u τ x / s113q_qk q k τ x) ^ (pt τ) * Real.log (u τ x / s113q_qk q k τ x)))
        (volume.restrict (Ioc 0 T)) :=
      (((hptc.sub continuous_const).aestronglyMeasurable.mul (famN.2.2 pt hptc)).restrict).add
        (hderivM.mul (famC.2.2 pt hptc).restrict)
    refine hm.congr ?_
    refine (ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun τ hτ => ?_)
    have hτ' : τ ∈ Icc (0 : ℝ) T := ⟨hτ.1.le, hτ.2⟩
    simp only [hGk]
    rw [s113b_Gp_eq hDk p hτ', hptEq τ hτ']
  have hGlim : ∀ τ ∈ Icc (0 : ℝ) T, Tendsto (fun k => Gk k τ) atTop (𝓝 (s113b_Gp ν b q u p τ)) := by
    intro τ hτ
    rw [s11q2_Gp_eq hD p hτ]
    refine Tendsto.congr (fun k => (s113b_Gp_eq (s113q_Data_k hD k) p hτ).symm)
      ((((hlim τ hτ).1).const_mul (p τ - 1)).add (((hlim τ hτ).2).const_mul (deriv p τ)))
  have hPpos : 0 ≤ P := zero_le_one.trans ((hpP 0 ⟨le_rfl, hT⟩).1.trans (hpP 0 ⟨le_rfl, hT⟩).2)
  have hGkb : ∀ k, k0 ≤ k → ∀ τ ∈ Icc (0 : ℝ) T, |Gk k τ| ≤ P * CA + |deriv p τ| * CC := by
    intro k hk τ hτ
    obtain ⟨h1, h2⟩ := hbd k hk τ hτ
    simp only [hGk]
    rw [s113b_Gp_eq (s113q_Data_k hD k) p hτ]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul]
      have hp' := hpP τ hτ
      have : |p τ - 1| ≤ P := by rw [abs_of_nonneg (by linarith [hp'.1])]; linarith [hp'.2]
      exact mul_le_mul this h1 (abs_nonneg _) hPpos
    · rw [abs_mul]
      exact mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
  have hGb : ∀ τ ∈ Icc (0 : ℝ) T, |s113b_Gp ν b q u p τ| ≤ P * CA + |deriv p τ| * CC := fun τ hτ =>
    le_of_tendsto (hGlim τ hτ).abs (eventually_atTop.2 ⟨k0, fun k hk => hGkb k hk τ hτ⟩)
  have hae : ∀ {s t : ℝ}, 0 ≤ s → t ≤ T → ∀ᵐ τ ∂(volume.restrict (Ioc s t)), τ ∈ Icc (0 : ℝ) T := fun {s t} hs htT =>
    (ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun τ hτ => ⟨hs.trans hτ.1.le, hτ.2.trans htT⟩)
  have hDm : ∀ {s t : ℝ}, 0 ≤ s → s ≤ t → t ≤ T → Integrable (fun τ => P * CA + |deriv p τ| * CC) (volume.restrict (Ioc s t)) := by
    intro s t hs hst htT
    have hi : IntegrableOn (deriv p) (Ioc s t) := (hp.mono (by
      rw [uIcc_of_le hst, uIcc_of_le hT]; exact Icc_subset_Icc hs htT)).intervalIntegrable_deriv.1
    exact (integrable_const _).add (hi.norm.mul_const CC)
  have hGm : AEStronglyMeasurable (s113b_Gp ν b q u p) (volume.restrict (Ioc 0 T)) :=
    aestronglyMeasurable_of_tendsto_ae atTop hGkm ((hae le_rfl le_rfl).mono fun τ hτ => hGlim τ hτ)
  have hGint : IntervalIntegrable (s113b_Gp ν b q u p) volume 0 T := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT]
    exact Integrable.mono' (hDm le_rfl hT le_rfl) hGm ((hae le_rfl le_rfl).mono fun τ hτ => by
      simpa [Real.norm_eq_abs] using hGb τ hτ)
  refine ⟨hGint, fun s t hs hst htT => ?_⟩
  have hint : Tendsto (fun k => ∫ τ in s..t, Gk k τ) atTop (𝓝 (∫ τ in s..t, s113b_Gp ν b q u p τ)) := by
    simp only [intervalIntegral.integral_of_le hst]
    have := tendsto_integral_of_dominated_convergence (μ := volume.restrict (Ioc s t)) (F := fun k τ => Gk (k + k0) τ)
      (f := s113b_Gp ν b q u p) (fun τ => P * CA + |deriv p τ| * CC)
      (fun k => (hGkm _).mono_measure (Measure.restrict_mono (Ioc_subset_Ioc hs htT) le_rfl)) (hDm hs hst htT)
      (fun k => (hae hs htT).mono fun τ hτ => by simpa [Real.norm_eq_abs] using hGkb (k + k0) (Nat.le_add_left _ _) τ hτ)
      ((hae hs htT).mono fun τ hτ => (hGlim τ hτ).comp (tendsto_add_atTop_nat k0))
    exact (tendsto_add_atTop_iff_nat k0).1 this
  have hM : ∀ r ∈ Icc (0 : ℝ) T, Tendsto (fun k => s113b_M (s113q_qk q k) u p r) atTop (𝓝 (s113b_M q u p r)) :=
    fun r hr => s113q_M_tendsto hD hr (zero_lt_one.trans (hp1 r hr))
  exact le_of_tendsto_of_tendsto ((hM t ⟨hs.trans hst, htT⟩).sub (hM s ⟨hs, hst.trans htT⟩)) hint
    (Eventually.of_forall fun k => s113b_chain_ac (s113q_Data_k hD k) hp hp1 hs hst htT)

end HRS.MS.S11Q2

end
