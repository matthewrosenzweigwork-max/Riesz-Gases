import HRS.MS.Sf8Aux3

/-!
# MS-SF8II, the core theorem (route: `Sf8Plan.md`)
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.Sf8

open HRS.Whole HRS.MS.SameFunction

variable {d : ℕ}

theorem lintegral_ind_sq {B : Set (Euc d)} (hB : MeasurableSet B) (w : Euc d → ℝ) :
    ∫⁻ x, ENNReal.ofReal ((B.indicator w x) ^ 2) = ∫⁻ x in B, ENNReal.ofReal (w x ^ 2) := by
  rw [← lintegral_indicator hB]
  refine lintegral_congr fun x => ?_
  by_cases hx : x ∈ B <;> simp [Set.indicator, hx]

theorem lintegral_ind_abs {B : Set (Euc d)} (hB : MeasurableSet B) (w : Euc d → ℝ) :
    ∫⁻ x, ENNReal.ofReal (B.indicator (fun x => |w x|) x) = ∫⁻ x in B, ENNReal.ofReal |w x| := by
  rw [← lintegral_indicator hB]
  refine lintegral_congr fun x => ?_
  by_cases hx : x ∈ B <;> simp [Set.indicator, hx]

theorem I2_sub_comm (s : ℝ) (x y : Euc d) : msf_I2 s (x - y) = msf_I2 s (y - x) := by
  have h : ‖y - x‖ = ‖x - y‖ := norm_sub_rev y x
  rcases lt_or_ge ‖x - y‖ 1 with h1 | h1
  · rw [msf_I2_lt h1, msf_I2_lt (by rw [h]; exact h1)]
  · rw [msf_I2_ge h1, msf_I2_ge (by rw [h]; exact h1), h]

/-- The core estimate (no global `L²` assumption on `w`; local `L²`/`L¹` bounds only). -/
theorem core (hd : 1 ≤ d) {s : ℝ} (hs1 : (d : ℝ) - 1 < s) (hsd : s < d)
    {κ : Euc d → ℝ} {K₀ : ℝ} (hodd : ∀ z, κ (-z) = -κ z)
    (hsm : ContDiffOn ℝ ∞ κ {z | z ≠ 0})
    (hbd : ∀ z : Euc d, z ≠ 0 → |κ z| ≤ K₀ * ‖z‖ ^ (-s - 1))
    {La Λ : ℝ} {a : Euc d → ℝ} (ha : HRS.PDE.ToolboxRd.IsLipschitz La a)
    (hjb : ∀ x, jbracket x ^ ((d : ℝ) + 3) * |a x| ≤ Λ)
    {ς : Euc d → ℝ} {L' : ℝ} (hς0 : ∀ x, 0 ≤ ς x) (hς1 : ∀ x, ς x ≤ 1)
    (hςL : ∀ x y, |ς x - ς y| ≤ L' * ‖x - y‖)
    {c : Euc d} {R₀ : ℝ} (hsupp : ∀ x, ς x ≠ 0 → x ∈ Metric.ball c R₀)
    {w : Euc d → ℝ} (hw : Measurable w) {M1 M2 M3 : ℝ} (hM1 : 0 ≤ M1) (hM2 : 0 ≤ M2) (hM3 : 0 ≤ M3)
    (hm2 : ∫⁻ x in Metric.ball c (R₀ + 1), ENNReal.ofReal (w x ^ 2) ≤ ENNReal.ofReal M2)
    (hm1 : ∫⁻ x in Metric.ball c R₀, ENNReal.ofReal |w x| ≤ ENNReal.ofReal M1)
    (hm3 : ∀ u : Euc d, ∫⁻ x in Metric.ball u 1, ENNReal.ofReal |w x| ≤ ENNReal.ofReal M3) :
    Integrable (fun p : Euc d × Euc d => κ (p.1 - p.2) * w p.1 * w p.2 *
      (a p.2 * ς p.1 - a p.1 * ς p.2)) ∧
    Tendsto (fun ε => truncPairing ε κ a w ς) (𝓝[>] 0) (𝓝 (symPairing κ a w ς)) ∧
    |symPairing κ a w ς| ≤ K₀ * (La + Λ) * (1 + L') *
      ((∫ z : Euc d, msf_I1 s z) * M2 + farConst d s * M1 * M3) := by
  have hs2 : (d : ℝ) < s + 1 := by linarith
  obtain ⟨hK, hL, hΛ0⟩ := nonneg_facts hd hbd ha hjb
  have hL' : 0 ≤ L' := lip_nonneg hd hςL
  have hκm : Measurable κ := HRS.PDE.ToolboxRd.WeightAux.measurable_of_smooth hsm
  have hκ0 : κ 0 = 0 := by
    have h := hodd 0
    rw [neg_zero] at h
    linarith
  have hacont : Continuous a := HRS.PDE.ToolboxRd.WeightAux.isLipschitz_continuous ha
  have haΛ : ∀ x, |a x| ≤ Λ := fun x => msf_abs_le hjb x
  have hςm : Measurable ς := by
    have hςc : Continuous ς :=
      (LipschitzWith.of_dist_le_mul (K := L'.toNNReal) fun x y => by
        rw [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal L' hL']; exact hςL x y).continuous
    exact hςc.measurable
  -- the truncated functions
  set wΩ : Euc d → ℝ := (Metric.ball c (R₀ + 1)).indicator w with hwΩ
  set hh : Euc d → ℝ := (Metric.ball c R₀).indicator (fun x => |w x|) with hhh
  have hwΩm : Measurable wΩ := hw.indicator measurableSet_ball
  have hhm : Measurable hh := hw.abs.indicator measurableSet_ball
  have hh0 : ∀ x, 0 ≤ hh x := fun x => Set.indicator_nonneg (fun _ _ => abs_nonneg _) x
  have hwΩ2 : Integrable (fun x => wΩ x ^ 2) := by
    refine integrable_of_lintegral_ofReal (hwΩm.pow_const 2) (fun x => sq_nonneg _) ?_
    rw [hwΩ, lintegral_ind_sq measurableSet_ball]
    exact (hm2.trans_lt ENNReal.ofReal_lt_top).ne
  have hwΩL2 : MemLp wΩ 2 volume := (memLp_two_iff_integrable_sq hwΩm.aestronglyMeasurable).2 hwΩ2
  have hwΩint : ∫ x, wΩ x ^ 2 ≤ M2 := by
    refine integral_le_of_lintegral hwΩ2 (fun x => sq_nonneg _) hM2 ?_
    rw [hwΩ, lintegral_ind_sq measurableSet_ball]
    exact hm2
  -- near majorant
  set N : Euc d × Euc d → ℝ := fun p => msf_I1 s (p.1 - p.2) * (|wΩ p.1| * |wΩ p.2|) with hN
  have hNm : Measurable N :=
    (((measurable_msf_I1 (d := d) s).comp (measurable_fst.sub measurable_snd)).mul
      (((hwΩm.comp measurable_fst).abs).mul ((hwΩm.comp measurable_snd).abs)))
  have hρ1int : Integrable (fun z : Euc d => msf_I1 s z) := msf_I1_int hd hsd
  obtain ⟨hNint, hNval⟩ := HRS.PDE.ToolboxRd.WeightAux.schur_bound (G := N) hρ1int
    (msf_I1_nonneg s) hwΩL2 hNm.aestronglyMeasurable (fun p => by
      have : 0 ≤ N p := mul_nonneg (msf_I1_nonneg _ _) (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      exact (abs_of_nonneg this).le)
  have hInt0 : 0 ≤ ∫ z : Euc d, msf_I1 s z := integral_nonneg (msf_I1_nonneg s)
  have hNle : ∫ p, N p ≤ (∫ z : Euc d, msf_I1 s z) * M2 :=
    (le_abs_self _).trans (hNval.trans (mul_le_mul_of_nonneg_left hwΩint hInt0))
  -- far majorant
  have h1' : ∫⁻ x, ENNReal.ofReal (hh x) ≤ ENNReal.ofReal M1 := by
    rw [hhh, lintegral_ind_abs measurableSet_ball]; exact hm1
  obtain ⟨hHint, hHval⟩ := far_int hd hs2 hhm hw.abs hh0 (fun x => abs_nonneg _) hM1 hM3 h1' hm3
  set H : Euc d × Euc d → ℝ := fun p => msf_I2 s (p.1 - p.2) * hh p.1 * |w p.2| with hH
  set Hsw : Euc d × Euc d → ℝ := fun p => msf_I2 s (p.1 - p.2) * |w p.1| * hh p.2 with hHsw
  have hHswint : Integrable Hsw := by
    refine (hHint.swap).congr (Eventually.of_forall fun p => ?_)
    simp only [hHsw, hH, Function.comp, Prod.fst_swap, Prod.snd_swap]
    rw [I2_sub_comm s p.2 p.1]; ring
  have hHswval : ∫ p, Hsw p = ∫ p, H p := by
    have e : (fun p : Euc d × Euc d => Hsw p) = fun p => H (Prod.swap p) := by
      funext p
      simp only [hHsw, hH, Prod.fst_swap, Prod.snd_swap]
      rw [I2_sub_comm s p.2 p.1]; ring
    rw [e]
    exact integral_prod_swap (μ := (volume : Measure (Euc d))) (ν := (volume : Measure (Euc d))) H
  -- the symmetrized integrand
  set F : Euc d × Euc d → ℝ := fun p => κ (p.1 - p.2) * w p.1 * w p.2 *
    (a p.2 * ς p.1 - a p.1 * ς p.2) with hFdef
  have hw1 : Measurable fun p : Euc d × Euc d => w p.1 := hw.comp measurable_fst
  have hw2 : Measurable fun p : Euc d × Euc d => w p.2 := hw.comp measurable_snd
  have hk : Measurable fun p : Euc d × Euc d => κ (p.1 - p.2) :=
    hκm.comp (measurable_fst.sub measurable_snd)
  have ha1 : Measurable fun p : Euc d × Euc d => a p.1 := hacont.measurable.comp measurable_fst
  have ha2 : Measurable fun p : Euc d × Euc d => a p.2 := hacont.measurable.comp measurable_snd
  have hς1m : Measurable fun p : Euc d × Euc d => ς p.1 := hςm.comp measurable_fst
  have hς2m : Measurable fun p : Euc d × Euc d => ς p.2 := hςm.comp measurable_snd
  have hFm : Measurable F :=
    ((hk.mul hw1).mul hw2).mul ((ha2.mul hς1m).sub (ha1.mul hς2m))
  set c1 : ℝ := K₀ * (La + Λ) * (1 + L') with hc1
  have hc1nn : 0 ≤ c1 := by positivity
  have hc2nn : 0 ≤ K₀ * Λ := mul_nonneg hK hΛ0
  set Hmaj : Euc d × Euc d → ℝ := fun p => c1 * N p + K₀ * Λ * (H p + Hsw p) with hHmaj
  have hHmajint : Integrable Hmaj :=
    (hNint.const_mul c1).add ((hHint.add hHswint).const_mul (K₀ * Λ))
  have hFbd : ∀ p : Euc d × Euc d, ‖F p‖ ≤ Hmaj p := by
    intro p
    have h := pt_sym (s := s) (c := c) (R₀ := R₀) hK hL hΛ0 hL' hκ0 hbd ha haΛ hς0 hς1 hςL hsupp w
      p.1 p.2
    rw [Real.norm_eq_abs]
    refine h.trans (le_of_eq ?_)
    simp only [hHmaj, hN, hH, hHsw, hc1, hwΩ, hhh]
  have hFint : Integrable F := hHmajint.mono' hFm.aestronglyMeasurable (Eventually.of_forall hFbd)
  have hFval : ‖∫ p, F p‖ ≤ ∫ p, Hmaj p := norm_integral_le_of_norm_le hHmajint (Eventually.of_forall hFbd)
  have hHmajval : ∫ p, Hmaj p = c1 * (∫ p, N p) + K₀ * Λ * ((∫ p, H p) + ∫ p, Hsw p) := by
    simp only [hHmaj]
    have hI1 : Integrable (fun p => c1 * N p) := hNint.const_mul c1
    have hI2 : Integrable (fun p => K₀ * Λ * (H p + Hsw p)) :=
      (hHint.add hHswint).const_mul (K₀ * Λ)
    rw [integral_add hI1 hI2, integral_const_mul, integral_const_mul, integral_add hHint hHswint]
  -- truncations
  set T : ℝ → Euc d × Euc d → ℝ := fun ε p =>
    if ε < ‖p.1 - p.2‖ then κ (p.1 - p.2) * a p.2 * w p.2 * ς p.1 * w p.1 else 0 with hTdef
  set T' : ℝ → Euc d × Euc d → ℝ := fun ε p =>
    if ε < ‖p.1 - p.2‖ then κ (p.1 - p.2) * a p.1 * w p.2 * ς p.2 * w p.1 else 0 with hT'def
  set G : ℝ → Euc d × Euc d → ℝ := fun ε p =>
    if ε < ‖p.1 - p.2‖ then F p else 0 with hGdef
  have hsetm : ∀ ε : ℝ, MeasurableSet {p : Euc d × Euc d | ε < ‖p.1 - p.2‖} := fun ε =>
    measurableSet_lt measurable_const (measurable_fst.sub measurable_snd).norm
  have hTm : ∀ ε : ℝ, Measurable (T ε) := by
    intro ε
    have e : T ε = Set.indicator {p : Euc d × Euc d | ε < ‖p.1 - p.2‖}
        (fun p => κ (p.1 - p.2) * a p.2 * w p.2 * ς p.1 * w p.1) := by
      funext p; simp only [hTdef, Set.indicator, Set.mem_setOf_eq]
    rw [e]
    exact ((((hk.mul ha2).mul hw2).mul hς1m).mul hw1).indicator (hsetm ε)
  have hTint : ∀ ε : ℝ, 0 < ε → Integrable (T ε) := by
    intro ε hε
    have hmaj : Integrable (fun p => K₀ * Λ * ε⁻¹ * N p + K₀ * Λ * H p) :=
      (hNint.const_mul _).add (hHint.const_mul _)
    refine hmaj.mono' (hTm ε).aestronglyMeasurable (Eventually.of_forall fun p => ?_)
    have h := pt_trunc (s := s) (c := c) (R₀ := R₀) hK hΛ0 hbd haΛ hς0 hς1 hsupp w hε p.1 p.2
    rw [Real.norm_eq_abs]
    refine h.trans (le_of_eq ?_)
    simp only [hN, hH, hwΩ, hhh]
  have hsym : ∀ ε : ℝ, 0 < ε → ∫ p, T ε p = (1 / 2) * ∫ p, G ε p := by
    intro ε hε
    have hswap : ∀ p : Euc d × Euc d, T' ε p = -(T ε (Prod.swap p)) := by
      intro p
      simp only [hT'def, hTdef, Prod.fst_swap, Prod.snd_swap]
      rw [norm_sub_rev p.2 p.1]
      split_ifs with h
      · have : κ (p.2 - p.1) = -κ (p.1 - p.2) := by rw [← neg_sub, hodd]
        rw [this]; ring
      · simp
    have hT'int : Integrable (T' ε) := by
      have h2 := (hTint ε hε).swap.neg
      refine h2.congr (Eventually.of_forall fun p => ?_)
      exact (hswap p).symm
    have hGsplit : ∀ p, G ε p = T ε p - T' ε p := by
      intro p
      simp only [hGdef, hTdef, hT'def, hFdef]
      split_ifs
      · ring
      · simp
    have h1 : ∫ p, G ε p = (∫ p, T ε p) - ∫ p, T' ε p := by
      rw [show (fun p => G ε p) = fun p => T ε p - T' ε p from funext hGsplit]
      exact integral_sub (hTint ε hε) hT'int
    have h2 : ∫ p, T' ε p = -∫ p, T ε p := by
      rw [show (fun p => T' ε p) = fun p => -(T ε (Prod.swap p)) from funext hswap, integral_neg]
      congr 1
      exact integral_prod_swap (μ := (volume : Measure (Euc d))) (ν := (volume : Measure (Euc d)))
        (T ε)
    rw [h1, h2]; ring
  have hGint : ∀ ε : ℝ, Integrable (G ε) := by
    intro ε
    refine hFint.norm.mono' ?_ (Eventually.of_forall fun p => ?_)
    · have e : G ε = Set.indicator {p : Euc d × Euc d | ε < ‖p.1 - p.2‖} F := by
        funext p; simp only [hGdef, Set.indicator, Set.mem_setOf_eq]
      rw [e]
      exact (hFm.indicator (hsetm ε)).aestronglyMeasurable
    · simp only [hGdef]
      split_ifs
      · exact le_rfl
      · simp
  have hlim : Tendsto (fun ε : ℝ => ∫ p, G ε p) (𝓝[>] 0) (𝓝 (∫ p, F p)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun p => ‖F p‖)
      (Eventually.of_forall fun ε => (hGint ε).aestronglyMeasurable)
      (Eventually.of_forall fun ε => Eventually.of_forall fun p => ?_) hFint.norm ?_
    · simp only [hGdef]
      split_ifs
      · exact le_rfl
      · simp
    · refine Eventually.of_forall fun p => ?_
      by_cases hpt : ‖p.1 - p.2‖ = 0
      · have hz0 : p.1 - p.2 = 0 := norm_eq_zero.1 hpt
        have hF0 : F p = 0 := by simp only [hFdef, hz0, hκ0, zero_mul]
        rw [hF0]
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with ε hε
        have hn : ¬ ε < ‖p.1 - p.2‖ := by
          rw [hpt]; exact not_lt.2 (Set.mem_Ioi.1 hε).le
        show (0 : ℝ) = G ε p
        simp only [hGdef, if_neg hn]
      · have hpos : 0 < ‖p.1 - p.2‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hpt)
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [Ioo_mem_nhdsGT hpos] with ε hε
        show F p = G ε p
        simp only [hGdef, if_pos hε.2]
  have hTP : ∀ ε : ℝ, HRS.Whole.truncPairing ε κ a w ς = ∫ p, T ε p := by
    intro ε
    simp only [HRS.Whole.truncPairing, hTdef]
  have hSP : HRS.Whole.symPairing κ a w ς = (1 / 2) * ∫ p, F p := by
    simp only [HRS.Whole.symPairing, hFdef]
  refine ⟨hFint, ?_, ?_⟩
  · simp only [hTP, hSP]
    refine (hlim.const_mul (1 / 2)).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (hsym ε (Set.mem_Ioi.1 hε)).symm
  · rw [hSP, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    have hfc := farConst_nonneg hd hs2
    have hfM : 0 ≤ farConst d s * M1 * M3 := mul_nonneg (mul_nonneg hfc hM1) hM3
    have hcc : K₀ * Λ ≤ c1 := by
      have : Λ ≤ (La + Λ) * (1 + L') := by nlinarith [mul_nonneg hL hL', mul_nonneg hΛ0 hL']
      calc K₀ * Λ ≤ K₀ * ((La + Λ) * (1 + L')) := mul_le_mul_of_nonneg_left this hK
        _ = c1 := by simp only [hc1]; ring
    have hHsum : (∫ p, H p) + ∫ p, Hsw p ≤ 2 * (farConst d s * M1 * M3) := by
      rw [hHswval]; linarith
    have hstep : ‖∫ p, F p‖ ≤ c1 * ((∫ z : Euc d, msf_I1 s z) * M2) +
        K₀ * Λ * (2 * (farConst d s * M1 * M3)) := by
      refine hFval.trans ?_
      rw [hHmajval]
      refine add_le_add (mul_le_mul_of_nonneg_left hNle hc1nn)
        (mul_le_mul_of_nonneg_left hHsum hc2nn)
    rw [Real.norm_eq_abs] at hstep
    have hIM : 0 ≤ (∫ z : Euc d, msf_I1 s z) * M2 := mul_nonneg hInt0 hM2
    nlinarith [mul_nonneg hc1nn hIM, mul_nonneg (sub_nonneg.2 hcc) hfM]

end HRS.MS.Sf8
