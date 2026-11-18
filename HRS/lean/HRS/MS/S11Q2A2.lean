import HRS.MS.S11Q2A1

/-!
# S11.3 Q-regularity (worker S11Q2), A2: the chain inequality for a reference of class `C^{1,2}`

`s11q2_spatial`: for `τ ∈ [0,T]` the two spatial integrals along the Steklov averages converge and are bounded uniformly in
`(k ≥ k₀, τ)`.  `s11q2_chain_ac`: interval integrability of `s113b_Gp` and the chain inequality for `s113q_Data`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

open MeasureTheory Filter Topology Set intervalIntegral

namespace HRS.MS.S11Q2

open HRS.MS.S113X2B HRS.MS.S113X2C HRS.MS.S113Q

theorem s11q2_spatial {n : ℕ} {ν : ℝ} {b : s113b_E n → s113b_E n} {q : ℝ → s113b_E n → ℝ} {T : ℝ} {u : ℝ → s113b_E n → ℝ}
    {K G : Set (s113b_E n)} {B : ℝ} (hD : s113q_Data ν b q T u K G B) {p : ℝ → ℝ} {P : ℝ}
    (hpP : ∀ τ ∈ Icc 0 T, p τ ∈ Icc (1 : ℝ) P) :
    ∃ (CA CC : ℝ) (k0 : ℕ), (∀ k, k0 ≤ k → ∀ τ ∈ Icc 0 T,
        |∫ x, s113b_N ν b (s113q_qk q k) τ x * (u τ x / s113q_qk q k τ x) ^ (p τ)| ≤ CA ∧
        |∫ x, s113q_qk q k τ x * ((u τ x / s113q_qk q k τ x) ^ (p τ) * Real.log (u τ x / s113q_qk q k τ x))| ≤ CC) ∧
      ∀ τ ∈ Icc 0 T,
        Tendsto (fun k => ∫ x, s113b_N ν b (s113q_qk q k) τ x * (u τ x / s113q_qk q k τ x) ^ (p τ)) atTop
          (𝓝 (∫ x, s113b_N ν b q τ x * (u τ x / q τ x) ^ (p τ))) ∧
        Tendsto (fun k => ∫ x, s113q_qk q k τ x * ((u τ x / s113q_qk q k τ x) ^ (p τ) * Real.log (u τ x / s113q_qk q k τ x)))
          atTop (𝓝 (∫ x, q τ x * ((u τ x / q τ x) ^ (p τ) * Real.log (u τ x / q τ x)))) := by
  obtain ⟨d1, d2, d3, hd⟩ := hD.hq
  have hC : IsCompact (Icc (0 : ℝ) T ×ˢ K) := isCompact_Icc.prod hD.hKc
  have hpos : ∀ z ∈ Icc (0 : ℝ) T ×ˢ K, 0 < (fun z : ℝ × s113b_E n => q z.1 z.2) z := fun z hz =>
    hD.hq0 _ ⟨hz.1.1, hz.1.2.trans (by linarith)⟩ _
  obtain ⟨qmin, CQ, C1, C2, C3, k0, hqmin, hle, hk⟩ := s113q_uniform hd hC hpos
  obtain ⟨Cb, Cb', hCb, hCb'⟩ := s113q_bcoef hD.hb hD.hKc
  have hZ0 : 0 ≤ |B| / (qmin / 2) := by positivity
  obtain ⟨Cp, hp0, hpb, hpc⟩ := s113b_pow_props 1 P (|B| / (qmin / 2)) one_pos hZ0
  obtain ⟨Cl, hl0, hlb, hlc⟩ := s113b_log_props 1 P (|B| / (qmin / 2)) one_pos hZ0
  have hkm : ∀ k τ, τ ∈ Icc (0 : ℝ) T → ∀ x ∈ K, k0 ≤ k → qmin / 2 ≤ s113q_qk q k τ x ∧
      |s113q_qk q k τ x| ≤ max CQ 0 ∧ |s113b_N ν b (s113q_qk q k) τ x| ≤
        |ν| * (n * max C3 0) + (n * (max CQ 0 * max Cb' 0 + max Cb 0 * max C2 0)) + max C1 0 := by
    intro k τ hτ x hx hkk
    obtain ⟨h0, h1, h2, h3, h4⟩ := hk k hkk (τ, x) ⟨hτ, hx⟩
    refine ⟨h0, h1.trans (le_max_left _ _), ?_⟩
    rw [s11q2_Nk_eq hD hd]
    have hb := s113q_Nf_bound ν b x (Cb := max Cb 0) (Cb' := max Cb' 0) (fun k => (hCb x hx k).trans (le_max_left _ _))
      (fun k => (hCb' x hx k).trans (le_max_left _ _))
      (s113q_S (s113q_eta k) (fun z : ℝ × s113b_E n => q z.1 z.2) (τ, x))
      (s113q_S (s113q_eta k) d1 (τ, x)) (s113q_S (s113q_eta k) d2 (τ, x)) (s113q_S (s113q_eta k) d3 (τ, x))
    refine hb.trans ?_
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have e0 : |s113q_S (s113q_eta k) (fun z : ℝ × s113b_E n => q z.1 z.2) (τ, x)| ≤ max CQ 0 := h1.trans (le_max_left _ _)
    have e1 : |s113q_S (s113q_eta k) d1 (τ, x)| ≤ max C1 0 := h2.trans (le_max_left _ _)
    have e2 : ‖s113q_S (s113q_eta k) d2 (τ, x)‖ ≤ max C2 0 := h3.trans (le_max_left _ _)
    have e3 : ‖s113q_S (s113q_eta k) d3 (τ, x)‖ ≤ max C3 0 := h4.trans (le_max_left _ _)
    have m1 : 0 ≤ max Cb 0 := le_max_right _ _
    have m2 : 0 ≤ max Cb' 0 := le_max_right _ _
    gcongr
  have hZk : ∀ k τ, τ ∈ Icc (0 : ℝ) T → ∀ x ∈ K, k0 ≤ k → u τ x / s113q_qk q k τ x ≤ |B| / (qmin / 2) :=
    fun k τ hτ x hx hkk => div_le_div₀ (abs_nonneg B) ((hD.huB τ hτ x).trans (le_abs_self B)) (half_pos hqmin)
      (hkm k τ hτ x hx hkk).1
  have hum : ∀ τ, Measurable (u τ) := fun τ => hD.hum.comp measurable_prodMk_left
  have hNm : ∀ k τ, Measurable (fun x => s113b_N ν b (s113q_qk q k) τ x) := fun k τ =>
    ((s113b_N_contB9 ν hD.hb (s113q_Data_k hD k).hq).comp (continuous_const.prodMk continuous_id)).measurable
  have hA : ∀ τ ∈ Icc (0 : ℝ) T, _ := fun τ hτ => s11q2_dct_ratio hD.hKc (hum τ) (hD.hu0 τ) (hD.hKu τ)
    (wk := fun k x => s113b_N ν b (s113q_qk q k) τ x) (w := s113b_N ν b q τ)
    (qk := fun k x => s113q_qk q k τ x) (q := q τ) (ψ := fun z => z ^ (p τ))
    (W := |ν| * (n * max C3 0) + (n * (max CQ 0 * max Cb' 0 + max Cb 0 * max C2 0)) + max C1 0)
    (Z := |B| / (qmin / 2)) (Cψ := Cp) (qmin := qmin / 2) (k0 := k0) (hNm · τ)
    (fun k => (s113q_qk_cont hD k τ).measurable)
    (fun k hkk x hx => (hkm k τ hτ x hx hkk).2.2) (fun k hkk x hx => (hkm k τ hτ x hx hkk).1) (half_pos hqmin)
    (fun k hkk x hx => hZk k τ hτ x hx hkk) (measurable_id.pow_const _) (hp0 _ (hpP τ hτ))
    (fun z hz => hpb _ (hpP τ hτ) z hz)
    (fun z hz => Real.continuousAt_rpow_const _ _ (Or.inl hz.ne')) (fun x => s11q2_Nk_tendsto hD τ x)
    (fun x => s113q_qk_tendsto hD τ x) (fun x => hD.hq0 τ ⟨hτ.1, hτ.2.trans (by linarith)⟩ x)
  have hC' : ∀ τ ∈ Icc (0 : ℝ) T, _ := fun τ hτ => s11q2_dct_ratio hD.hKc (hum τ) (hD.hu0 τ) (hD.hKu τ)
    (wk := fun k x => s113q_qk q k τ x) (w := q τ)
    (qk := fun k x => s113q_qk q k τ x) (q := q τ) (ψ := fun z => z ^ (p τ) * Real.log z)
    (W := max CQ 0) (Z := |B| / (qmin / 2)) (Cψ := Cl) (qmin := qmin / 2) (k0 := k0)
    (fun k => (s113q_qk_cont hD k τ).measurable)
    (fun k => (s113q_qk_cont hD k τ).measurable)
    (fun k hkk x hx => (hkm k τ hτ x hx hkk).2.1) (fun k hkk x hx => (hkm k τ hτ x hx hkk).1) (half_pos hqmin)
    (fun k hkk x hx => hZk k τ hτ x hx hkk) ((measurable_id.pow_const _).mul Real.measurable_log) (hl0 _ (hpP τ hτ))
    (fun z hz => hlb _ (hpP τ hτ) z hz)
    (fun z hz => (Real.continuousAt_rpow_const _ _ (Or.inl hz.ne')).mul (Real.continuousAt_log hz.ne'))
    (fun x => s113q_qk_tendsto hD τ x)
    (fun x => s113q_qk_tendsto hD τ x) (fun x => hD.hq0 τ ⟨hτ.1, hτ.2.trans (by linarith)⟩ x)
  refine ⟨(|ν| * (n * max C3 0) + (n * (max CQ 0 * max Cb' 0 + max Cb 0 * max C2 0)) + max C1 0) * Cp * (volume K).toReal,
    max CQ 0 * Cl * (volume K).toReal, k0, fun k hkk τ hτ => ⟨(hA τ hτ).2 k hkk, (hC' τ hτ).2 k hkk⟩,
    fun τ hτ => ⟨(hA τ hτ).1, (hC' τ hτ).1⟩⟩

end HRS.MS.S11Q2

end
