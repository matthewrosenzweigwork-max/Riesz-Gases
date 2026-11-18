import HRS.MS.UniqC3c
import HRS.PDE.ToolboxRd.Fourier

/-!
# Packet C3, part 4: integral covering comparisons and the energy equivalence

* `cover_lower`, `cover_upper`: for measurable `G : ℝ^d → [0,∞]` and the centres `cellPt d z`,
  `∫ G ≤ ∑_z ∫ ς_z G` and `∑_z ∫ ς_z G ≤ N0 ∫ G` with `N0 = (4⌈√d⌉+1)^d`.
* `uc3_energy`: `sup_c ‖advCutoff χ Ψ τ c · F‖_{L²}` is comparable with `ulocNormE 0 χ F`
  (`BilipV.uloc_bilip_proof` (v) with `m = 0`, and Plancherel at order zero).
-/

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff
open HRS HRS.Whole

namespace HRS.MS.UniqC3

variable {d : ℕ}

section Integrals

variable {m : ℕ} {Cb t : ℝ} {Ψ : ℝ → Euc d → Euc d} {χ : Euc d → ℝ}

theorem varsigma_continuous (hF : FlowFacts m Cb t Ψ) (hχ : AppendixA.IsUlocCutoff χ) {τ : ℝ}
    (hτ : τ ∈ Icc (0 : ℝ) t) (c : Euc d) : Continuous (varsigma χ Ψ τ c) := by
  have hc : Continuous (Function.invFun (Ψ τ)) :=
    HRS.MS.FlowD.continuous_of_lip _ (Real.exp_pos _).le _ (hF.lip_inv τ hτ)
  exact (hχ.1.pow 2).continuous.comp (hc.sub continuous_const)

theorem sum_weights_le (hχ : AppendixA.IsUlocCutoff χ) (hF : FlowFacts m Cb t Ψ) (hCb : 0 ≤ Cb)
    {a : ℝ} (ha : 0 < a) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) t) (x : Euc d) :
    ∑' z : Fin d → ℤ, ENNReal.ofReal (varsigma χ Ψ τ (scaledPt a z) x) ≤
      ((⌊(2 * (2 / a) + 1) ^ d⌋₊ : ℕ) : ℝ≥0∞) := by
  obtain ⟨F, hF1, hF2⟩ := count_scaled ha (Function.invFun (Ψ τ) x) (r := 2) (by norm_num)
  rw [tsum_eq_sum (s := F)]
  · calc ∑ z ∈ F, ENNReal.ofReal (varsigma χ Ψ τ (scaledPt a z) x) ≤ ∑ _z ∈ F, (1 : ℝ≥0∞) :=
          Finset.sum_le_sum fun z _ =>
            ENNReal.ofReal_le_one.2 (varsigma_range hχ τ _ x).2
      _ = F.card := by simp
      _ ≤ _ := by exact_mod_cast Nat.le_floor hF2
  · intro z hz
    by_contra hne
    have h0 : varsigma χ Ψ τ (scaledPt a z) x ≠ 0 := fun h => hne (by simp [h])
    exact hz (hF1 z (varsigma_ne_zero hχ τ _ x h0).le |> fun h => by
      simpa [norm_sub_rev] using h)

theorem sum_weights_ge (hd : 1 ≤ d) (hχ : AppendixA.IsUlocCutoff χ) (τ : ℝ) (x : Euc d) :
    1 ≤ ∑' z : Fin d → ℤ, ENNReal.ofReal (varsigma χ Ψ τ (cellPt d z) x) := by
  obtain ⟨z, hz⟩ := exists_cellPt_near hd (Function.invFun (Ψ τ) x)
  have h1 : varsigma χ Ψ τ (cellPt d z) x = 1 := by
    have : χ (Function.invFun (Ψ τ) x - cellPt d z) = 1 :=
      hχ.2.2.2.2 _ (by rw [mem_closedBall_zero_iff]; linarith)
    simp [varsigma, advCutoff, this]
  calc (1 : ℝ≥0∞) = ENNReal.ofReal (varsigma χ Ψ τ (cellPt d z) x) := by rw [h1]; simp
    _ ≤ _ := ENNReal.le_tsum (f := fun z => ENNReal.ofReal (varsigma χ Ψ τ (cellPt d z) x)) z

theorem cover_lower (hd : 1 ≤ d) (hχ : AppendixA.IsUlocCutoff χ) (hF : FlowFacts m Cb t Ψ)
    {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) t) (G : Euc d → ℝ≥0∞) (hG : Measurable G) :
    ∫⁻ x, G x ≤ ∑' z : Fin d → ℤ, ∫⁻ x, ENNReal.ofReal (varsigma χ Ψ τ (cellPt d z) x) * G x := by
  have hm : ∀ z : Fin d → ℤ, Measurable
      (fun x => ENNReal.ofReal (varsigma χ Ψ τ (cellPt d z) x) * G x) := fun z =>
    (ENNReal.measurable_ofReal.comp (varsigma_continuous hF hχ hτ _).measurable).mul hG
  rw [← lintegral_tsum (fun z => (hm z).aemeasurable)]
  refine lintegral_mono fun x => ?_
  rw [ENNReal.tsum_mul_right]
  exact le_mul_of_one_le_left zero_le (sum_weights_ge hd hχ τ x)

theorem cellScale_pos (hd : 1 ≤ d) : 0 < cellScale d := by
  unfold cellScale
  exact Nat.ceil_pos.2 (Real.sqrt_pos.2 (by exact_mod_cast hd))

theorem floor_cell (hd : 1 ≤ d) :
    ⌊(2 * (2 / ((cellScale d : ℝ)⁻¹)) + 1) ^ d⌋₊ = multN d := by
  have hk : (cellScale d : ℝ) ≠ 0 := by exact_mod_cast (cellScale_pos hd).ne'
  have : (2 * (2 / ((cellScale d : ℝ)⁻¹)) + 1) = ((4 * cellScale d + 1 : ℕ) : ℝ) := by
    push_cast; field_simp; ring
  rw [this, ← Nat.cast_pow, Nat.floor_natCast]
  rfl

theorem sum_weights_le_cell (hd : 1 ≤ d) (hχ : AppendixA.IsUlocCutoff χ)
    (hF : FlowFacts m Cb t Ψ) (hCb : 0 ≤ Cb) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) t) (x : Euc d) :
    ∑' z : Fin d → ℤ, ENNReal.ofReal (varsigma χ Ψ τ (cellPt d z) x) ≤ (multN d : ℝ≥0∞) := by
  have hκ : (0 : ℝ) < (cellScale d : ℝ)⁻¹ := inv_pos.2 (by exact_mod_cast cellScale_pos hd)
  have := sum_weights_le hχ hF hCb hκ hτ x
  rw [floor_cell hd] at this
  simpa only [cellPt_eq_scaledPt] using this

theorem cover_upper (hd : 1 ≤ d) (hχ : AppendixA.IsUlocCutoff χ) (hF : FlowFacts m Cb t Ψ)
    (hCb : 0 ≤ Cb) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) t) (G : Euc d → ℝ≥0∞) (hG : Measurable G) :
    ∑' z : Fin d → ℤ, ∫⁻ x, ENNReal.ofReal (varsigma χ Ψ τ (cellPt d z) x) * G x ≤
      (multN d : ℝ≥0∞) * ∫⁻ x, G x := by
  have hm : ∀ z : Fin d → ℤ, Measurable
      (fun x => ENNReal.ofReal (varsigma χ Ψ τ (cellPt d z) x) * G x) := fun z =>
    (ENNReal.measurable_ofReal.comp (varsigma_continuous hF hχ hτ _).measurable).mul hG
  rw [← lintegral_tsum (fun z => (hm z).aemeasurable)]
  calc ∫⁻ x, ∑' z, ENNReal.ofReal (varsigma χ Ψ τ (cellPt d z) x) * G x
      ≤ ∫⁻ x, (multN d : ℝ≥0∞) * G x := by
        refine lintegral_mono fun x => ?_
        rw [ENNReal.tsum_mul_right]
        exact mul_le_mul_left (sum_weights_le_cell hd hχ hF hCb hτ x) _
    _ = _ := lintegral_const_mul _ hG

end Integrals


section Energy

/-- Plancherel at order zero (copy of `HRS.MH.Screened.l1_sobolev_zero_eq`, whose file is not imported here). -/
theorem uc3_sobolev_zero_L2 {v : Euc d → ℝ} (hv : MemLp v 2 volume) :
    sobolevNormE 0 v = eLpNorm v 2 volume := by
  have hint : Integrable (fun ξ : Euc d => (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (0 : ℝ) *
      ‖HRS.PDE.ToolboxRd.fourierL2 v ξ‖ ^ 2) := by
    simpa [Real.rpow_zero] using HRS.PDE.ToolboxRd.FourierAux.integrable_norm_sq_fourierL2 hv
  unfold sobolevNormE
  rw [if_pos (show HRS.PDE.ToolboxRd.MemSobolev 0 v from ⟨hv, hint⟩)]
  unfold HRS.PDE.ToolboxRd.sobolevNormSq
  simp only [Real.rpow_zero, one_mul]
  rw [HRS.PDE.ToolboxRd.FourierAux.integral_norm_sq_fourierL2 hv]
  rw [hv.eLpNorm_eq_integral_rpow_norm (by norm_num) (by simp)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs]
  rw [Real.sqrt_eq_rpow]
  norm_num

theorem uc3_sobolev_zero_eq (u : Euc d → ℝ) :
    sobolevNormE 0 u = eLpNorm u 2 volume := by
  by_cases hL : MemLp u 2 volume
  · exact uc3_sobolev_zero_L2 hL
  · have h1 : sobolevNormE 0 u = ⊤ := by
      unfold sobolevNormE
      rw [if_neg (fun h => hL h.1)]
    have h2 : eLpNorm u 2 volume = ⊤ := by
      by_contra h
      have h' : eLpNorm u 2 volume ≠ ⊤ := h
      exact hL h'.lt_top
    rw [h1, h2]

theorem uc3_eLpNorm_sq {f : Euc d → ℝ} (hf : AEStronglyMeasurable f volume) :
    eLpNorm f 2 volume ^ 2 = ∫⁻ x, ENNReal.ofReal (f x ^ 2) := by
  have h := eLpNorm_nnreal_pow_eq_lintegral (p := 2) (f := f) (μ := volume) (by norm_num) hf
  have h' : eLpNorm f 2 volume ^ 2 = ∫⁻ x, ‖f x‖ₑ ^ 2 := by simpa using h
  rw [h']
  refine lintegral_congr fun x => ?_
  rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]

theorem uc3_drift_zero {Λ T : ℝ} {b : ℝ → Euc d → Euc d} {m : ℕ}
    (hb : AppendixALemmas.IsDriftBounds T m Λ b) : AppendixALemmas.IsDriftBounds T 0 Λ b where
  cont := hb.cont
  smooth τ hτ := (hb.smooth τ hτ).of_le (by exact_mod_cast Nat.le_add_left 1 m)
  deriv_bound τ hτ j hj1 hj2 x := hb.deriv_bound τ hτ j hj1 (by omega) x
  growth := hb.growth

/-- Energy equivalence (order zero): `sup_c ‖advCutoff χ Ψ τ c · F‖_{L²} ≍ ‖F‖_{H^0_uloc}`. -/
theorem uc3_energy (m : ℕ) (Cb t : ℝ) (ht : 0 < t) (χ χh : Euc d → ℝ)
    (hχ : AppendixA.IsUlocCutoff χ) (hχh : AppendixALemmas.IsCutoffRad 6 8 χh) :
    ∃ K0 : ℝ, 0 < K0 ∧ ∀ K : ℝ, K0 ≤ K → ∀ (b : ℝ → Euc d → Euc d) (Ψ : ℝ → Euc d → Euc d),
      IsAdvectingDrift m Cb t b → IsNegDriftFlow t b Ψ → ∀ τ ∈ Icc (0 : ℝ) t,
      ∀ F : Euc d → ℝ,
        (ENNReal.ofReal (K⁻¹ * Real.exp (-(K * d * τ))) * AppendixA.ulocNormE 0 χ F ≤
          ⨆ c : Euc d, eLpNorm (fun x => advCutoff χ Ψ τ c x * F x) 2 volume) ∧
        (⨆ c : Euc d, eLpNorm (fun x => advCutoff χ Ψ τ c x * F x) 2 volume) ≤
          ENNReal.ofReal (K * Real.exp (K * d * τ)) * AppendixA.ulocNormE 0 χ F := by
  obtain ⟨C, c, hc, hprop⟩ := HRS.MS.BilipV.uloc_bilip_proof 0 t Cb ht χ χh hχ hχh
  refine ⟨max 1 (max C (1 / c)), lt_of_lt_of_le one_pos (le_max_left _ _), ?_⟩
  intro K hK b Ψ hb hΨ τ hτ F
  have hKC : C ≤ K := (le_max_left _ _).trans ((le_max_right _ _).trans hK)
  have hKc : 1 / c ≤ K := (le_max_right _ _).trans ((le_max_right _ _).trans hK)
  have hK1 : 1 ≤ K := (le_max_left _ _).trans hK
  have hK0 : 0 < K := lt_of_lt_of_le one_pos hK1
  obtain ⟨-, hex⟩ := hprop b (uc3_drift_zero (uc3_drift hb))
  obtain ⟨Ψinv, hΨinv⟩ := hex Ψ (uc3_flow hΨ)
  obtain ⟨⟨hi1, -⟩, -, -, -, hv⟩ := hΨinv τ hτ
  have hid : Ψinv τ = Function.invFun (Ψ τ) := funext fun y => by
    obtain ⟨x, rfl⟩ := (hΨ.bij τ hτ).2 y
    rw [hi1 x, Function.leftInverse_invFun (hΨ.bij τ hτ).1 x]
  obtain ⟨hlo, hup⟩ := hv F
  rw [hid] at hlo hup
  have key : ∀ z : Euc d, sobolevNormE ((0 : ℕ) : ℝ)
      (fun x => χ (Function.invFun (Ψ τ) x - z) * F x) =
      eLpNorm (fun x => advCutoff χ Ψ τ z x * F x) 2 volume := by
    intro z
    rw [Nat.cast_zero]
    exact uc3_sobolev_zero_eq _
  simp only [key] at hlo hup
  have hd0 : (0 : ℝ) ≤ d * τ := mul_nonneg (Nat.cast_nonneg _) hτ.1
  simp only [Nat.cast_zero, zero_add] at hlo hup
  constructor
  · refine le_trans (mul_le_mul_left ?_ _) hlo
    refine ENNReal.ofReal_le_ofReal (mul_le_mul ?_ ?_ (Real.exp_pos _).le hc.le)
    · exact (inv_le_comm₀ hK0 hc).2 (by simpa [one_div] using hKc)
    · exact Real.exp_le_exp.2 (by nlinarith)
  · refine hup.trans (mul_le_mul_left ?_ _)
    refine ENNReal.ofReal_le_ofReal ?_
    rcases le_or_gt C 0 with hC0 | hC0
    · calc C * Real.exp (C * d * τ) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hC0 (Real.exp_pos _).le
        _ ≤ K * Real.exp (K * d * τ) := (mul_pos hK0 (Real.exp_pos _)).le
    · exact mul_le_mul hKC (Real.exp_le_exp.2 (by nlinarith)) (Real.exp_pos _).le hK0.le


/-- The squared form: `sup_c ∫ ς_c F² ≍ ‖F‖²_{H^0_uloc}`. -/
theorem uc3_energy_sq (m : ℕ) (Cb t : ℝ) (ht : 0 < t) (χ χh : Euc d → ℝ)
    (hχ : AppendixA.IsUlocCutoff χ) (hχh : AppendixALemmas.IsCutoffRad 6 8 χh) :
    ∃ K0 : ℝ, 0 < K0 ∧ ∀ K : ℝ, K0 ≤ K → ∀ (b : ℝ → Euc d → Euc d) (Ψ : ℝ → Euc d → Euc d),
      IsAdvectingDrift m Cb t b → IsNegDriftFlow t b Ψ → ∀ τ ∈ Icc (0 : ℝ) t,
      ∀ F : Euc d → ℝ, AEStronglyMeasurable F volume →
        (ENNReal.ofReal (K⁻¹ * Real.exp (-(K * d * τ))) ^ 2 * AppendixA.ulocNormE 0 χ F ^ 2 ≤
          ⨆ c : Euc d, ∫⁻ x, ENNReal.ofReal (varsigma χ Ψ τ c x * F x ^ 2)) ∧
        (⨆ c : Euc d, ∫⁻ x, ENNReal.ofReal (varsigma χ Ψ τ c x * F x ^ 2)) ≤
          ENNReal.ofReal (K * Real.exp (K * d * τ)) ^ 2 * AppendixA.ulocNormE 0 χ F ^ 2 := by
  obtain ⟨K0, hK0, hE⟩ := uc3_energy m Cb t ht χ χh hχ hχh
  refine ⟨K0, hK0, fun K hK b Ψ hb hΨ τ hτ F hFm => ?_⟩
  obtain ⟨hlo, hup⟩ := hE K hK b Ψ hb hΨ τ hτ F
  have hFF := uc3_flowFacts ht.le hb hΨ
  have hcont : Continuous (Function.invFun (Ψ τ)) :=
    HRS.MS.FlowD.continuous_of_lip _ (Real.exp_pos _).le _ (hFF.lip_inv τ hτ)
  have E1 : ∀ c : Euc d, eLpNorm (fun x => advCutoff χ Ψ τ c x * F x) 2 volume ^ 2 =
      ∫⁻ x, ENNReal.ofReal (varsigma χ Ψ τ c x * F x ^ 2) := by
    intro c
    have hm : AEStronglyMeasurable (fun x => advCutoff χ Ψ τ c x * F x) volume :=
      (hχ.1.continuous.comp (hcont.sub continuous_const)).aestronglyMeasurable.mul hFm
    rw [uc3_eLpNorm_sq hm]
    refine lintegral_congr fun x => ?_
    simp only [varsigma, mul_pow]
  have hS : (⨆ c : Euc d, ∫⁻ x, ENNReal.ofReal (varsigma χ Ψ τ c x * F x ^ 2)) =
      (⨆ c : Euc d, eLpNorm (fun x => advCutoff χ Ψ τ c x * F x) 2 volume) ^ 2 := by
    rw [ENNReal.iSup_pow]
    exact iSup_congr fun c => (E1 c).symm
  rw [hS]
  constructor
  · rw [← mul_pow]
    exact pow_le_pow_left' hlo 2
  · rw [← mul_pow]
    exact pow_le_pow_left' hup 2

end Energy

end HRS.MS.UniqC3
