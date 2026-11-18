import HRS.MH.ScreenedCCGen
import HRS.MH.ScreenedF3
import HRS.MH.ScreenedF5
import HRS.MH.ScreenedF6
import HRS.MH.ScreenedA6
import HRS.MH.ScreenedL1Aux1
import HRS.MH.ScreenedK4Aux1
import HRS.MH.ScreenedP1Aux1

/-!
# Packet CC-near1 (`cc_near1_proof`, `ScreenedSpec.lean`): near kernel of the cutoff commutator.

Route (`ScreenedPlan.md` 3.7): the kernel `(χ̂_z - χ_z)(y) K_i(x-y)` is bounded by `σ Λ' |x-y|^{-s-1}` times
`1_{‖Φy-z‖<8} |ψ(y)|` for `x ∈ tsupport χ_z` (`|x-y| ≤ 10L` there), so the generic estimate `cc_gen`
(Young) applies; the cells `Q_{z'}` cover `{‖Φy-z‖<8}` with the weights `kcCoef` (`cc_cover`).
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform

namespace HRS.MH.Screened

open HRS HRS.Whole

variable {d : ℕ} {s : ℝ}

/-- Real constant bound for the near-field estimate (`p = s+1`, radius `10L`). -/
lemma cc1_pow (σ CK Λ L e : ℝ) (hσ : 0 ≤ σ) (hCK : 0 ≤ CK) (hL : 1 ≤ L) (he : e ≤ d) :
    (σ * max Λ 0 * CK * (10 * L) ^ e) ^ 2 ≤ σ ^ 2 * CK ^ 2 * 10 ^ (2 * d) * L ^ (2 * d) * Λ ^ 2 := by
  have hX0 : 0 ≤ (10 * L) ^ e := Real.rpow_nonneg (by linarith) _
  have hX : (10 * L) ^ e ≤ 10 ^ d * L ^ d := by
    calc (10 * L) ^ e ≤ (10 * L) ^ ((d : ℕ) : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) he
      _ = (10 * L) ^ d := Real.rpow_natCast _ _
      _ = 10 ^ d * L ^ d := mul_pow _ _ _
  have hΛ2 : (max Λ 0) ^ 2 ≤ Λ ^ 2 := by
    rcases le_total Λ 0 with h | h
    · rw [max_eq_right h, zero_pow two_ne_zero]
      positivity
    · rw [max_eq_left h]
  have hB : ((10 * L) ^ e) ^ 2 ≤ (10 ^ d * L ^ d) ^ 2 := pow_le_pow_left₀ hX0 hX 2
  calc (σ * max Λ 0 * CK * (10 * L) ^ e) ^ 2 = (σ ^ 2 * (max Λ 0) ^ 2) * (CK ^ 2 * ((10 * L) ^ e) ^ 2) := by
        ring
    _ ≤ (σ ^ 2 * Λ ^ 2) * (CK ^ 2 * (10 ^ d * L ^ d) ^ 2) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hΛ2 (sq_nonneg σ)) (mul_le_mul_of_nonneg_left hB (sq_nonneg CK))
          (by positivity) (by positivity)
    _ = σ ^ 2 * CK ^ 2 * 10 ^ (2 * d) * L ^ (2 * d) * Λ ^ 2 := by ring

/-- **CC-near1** (size M).  Kernel `χ_z(x)(χ̂_z-χ_z)(y)`, `d ≥ 2`, `s < d-1`: for `x ∈ tsupport χ_z` and
`(χ̂_z-χ_z)(y) ≠ 0` one has `‖Φx - z‖<2`, `‖Φy - z‖ < 8`, hence `|x-y| ≤ 10 L` (`advCutoff_facts`, `hlip`) and
`|kernel| ≤ σ|x-y|^{-s-1}`; `young_l1_l2` with `κ = σ|u|^{-s-1} 1_{|u| ≤ 10L}`
(`∫⁻ κ ≤ CK (10L)^{d-s-1}` by `lintegral_ball_rpow_le`), `f = 1_{‖Φy-z‖<8} aψ`,
`∫⁻ f² ≤ Λ² ∑_{|z'-z| ≤ 8+√d} ∫⁻_{Q_{z'}} ψ²` (cover), a.e. finiteness of `κ * |f|` from the `L²` bound. -/
theorem cc_near1_proof (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs1 : s < (d : ℝ) - 1) (m : ℕ) (Λ : ℝ) (χ χh : Euc d → ℝ)
    (hχ : IsCutoffPair χ χh) (L B : ℝ) (hL : 1 ≤ L) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Ψ : ℝ → Euc d → Euc d) (τ : ℝ), Function.Bijective (Ψ τ) →
      (∀ x y, ‖Ψ τ x - Ψ τ y‖ ≤ L * ‖x - y‖) →
      (∀ x y, ‖Function.invFun (Ψ τ) x - Function.invFun (Ψ τ) y‖ ≤ L * ‖x - y‖) →
      (∀ z : Euc d, ∀ x y : Euc d, x ∈ tsupport (advCutoff χ Ψ τ z) →
        y ∈ tsupport (fun y => 1 - advCutoff χh Ψ τ z y) → 4 / L ≤ ‖x - y‖) →
      ‖Ψ τ 0‖ ≤ B →
      ∀ μ : Euc d → ℝ, IsRegularDensityW (m + 3) Λ μ →
      ∀ (j : ℕ), j ≤ m + 1 → ∀ (idx : Fin j → Fin d) (i : Fin d) (ψ : Euc d → ℝ), Measurable ψ →
        ∀ z : Fin d → ℤ,
          (eLpNorm (fun x => advCutoff χ Ψ τ (latticePt z) x *
              ∫ y, (advCutoff χh Ψ τ (latticePt z) y - advCutoff χ Ψ τ (latticePt z) y) *
                (partialDeriv idx μ y * ψ y) * rieszKernelGrad d s (x - y) i) 2 volume) ^ 2 ≤
            ENNReal.ofReal (C * L ^ (2 * d) * Λ ^ 2) * ∑' z', (kcCoef d (8 + Real.sqrt d) 1 0 z z' : ℝ≥0∞) *
              (eLpNorm ((flowCell Ψ τ z').indicator ψ) 2 volume) ^ 2 ∧
          (ENNReal.ofReal (C * L ^ (2 * d) * Λ ^ 2) * ∑' z', (kcCoef d (8 + Real.sqrt d) 1 0 z z' : ℝ≥0∞) *
              (eLpNorm ((flowCell Ψ τ z').indicator ψ) 2 volume) ^ 2 < ⊤ →
            ∀ᵐ x ∂volume, x ∈ tsupport (advCutoff χ Ψ τ (latticePt z)) →
              Integrable (fun y => (advCutoff χh Ψ τ (latticePt z) y - advCutoff χ Ψ τ (latticePt z) y) *
                (partialDeriv idx μ y * ψ y) * rieszKernelGrad d s (x - y) i)) := by
  have hd1 : (1 : ℝ) ≤ d := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hd1' : 1 ≤ d := le_trans (by norm_num) hd
  have hsR : s + 1 < (d : ℝ) := by linarith
  have hL0 : 0 ≤ L := by linarith
  obtain ⟨CK, hCK, hgen⟩ := cc_gen (p := s + 1) hd1' hsR
  set σ : ℝ := max 1 s with hσdef
  have hσ0 : 0 ≤ σ := le_trans zero_le_one (le_max_left _ _)
  refine ⟨σ ^ 2 * CK ^ 2 * 10 ^ (2 * d), by positivity, ?_⟩
  intro Ψ τ hbij hlip hlipi _ _ μ hμ j hj idx i ψ hψ z
  have hΦc : Continuous (Function.invFun (Ψ τ)) := f5_cont_of_lip _ L hL0 hlipi
  obtain ⟨Lχ, hLχ0, hLχ1, hLχ2⟩ := cutoff_lipschitz_proof χ χh hχ
  obtain ⟨hf1, hf2, hf3, hf4, hf5, -, -, -⟩ :=
    advCutoff_facts_proof χ χh hχ Ψ τ L Lχ hL0 hlipi ⟨hLχ1, hLχ2⟩ (latticePt z)
  have hχc : Continuous χ := hχ.1.1.continuous
  have hχhc : Continuous χh := hχ.2.1.continuous
  have hadv : ∀ f : Euc d → ℝ, Continuous f →
      Continuous (fun x => advCutoff f Ψ τ (latticePt z) x) := fun f hf =>
    hf.comp (hΦc.sub continuous_const)
  have hAc := hadv χ hχc
  have hAhc := hadv χh hχhc
  obtain ⟨hDc, hDb⟩ := regularDensity_bounds_proof hμ hj idx
  have hDbd : ∀ y, |partialDeriv idx μ y| ≤ max Λ 0 := fun y =>
    (le_mul_of_one_le_left (abs_nonneg _)
      (Real.one_le_rpow (p1_one_le_jbracket y) (by positivity))).trans (hDb y)
  set S : Set (Euc d) := {y : Euc d | ‖Function.invFun (Ψ τ) y - latticePt z‖ < 8} with hSdef
  have hSm : MeasurableSet S :=
    (isOpen_lt (hΦc.sub continuous_const).norm continuous_const).measurableSet
  set G : Euc d → ℝ≥0∞ := S.indicator (fun y => ‖ψ y‖ₑ) with hGdef
  have hGm : Measurable G := hψ.enorm.indicator hSm
  set g : Euc d → Euc d → ℝ := fun x y => (advCutoff χh Ψ τ (latticePt z) y - advCutoff χ Ψ τ (latticePt z) y) *
    (partialDeriv idx μ y * ψ y) * rieszKernelGrad d s (x - y) i with hgdef
  have hgm : Measurable (fun q : Euc d × Euc d => g q.1 q.2) := by
    have h1 : Measurable (fun q : Euc d × Euc d =>
        advCutoff χh Ψ τ (latticePt z) q.2 - advCutoff χ Ψ τ (latticePt z) q.2) :=
      (hAhc.measurable.comp measurable_snd).sub (hAc.measurable.comp measurable_snd)
    have h2 : Measurable (fun q : Euc d × Euc d => partialDeriv idx μ q.2 * ψ q.2) :=
      (hDc.measurable.comp measurable_snd).mul (hψ.comp measurable_snd)
    have h3 : Measurable (fun q : Euc d × Euc d => rieszKernelGrad d s (q.1 - q.2) i) :=
      (k4_comp_measurable s i).comp (measurable_fst.sub measurable_snd)
    exact (h1.mul h2).mul h3
  have hbd : ∀ x ∈ tsupport (advCutoff χ Ψ τ (latticePt z)), ∀ y, y ≠ x →
      ‖g x y‖ₑ ≤ ENNReal.ofReal (σ * max Λ 0) *
        (Metric.closedBall (0 : Euc d) (10 * L)).indicator (fun u => ENNReal.ofReal (‖u‖ ^ (-(s + 1))))
          (x - y) * G y := by
    intro x hx y hy
    have hxΦ : ‖Function.invFun (Ψ τ) x - latticePt z‖ < 2 := hf3 x hx
    by_cases hyS : ‖Function.invFun (Ψ τ) y - latticePt z‖ < 8
    · have hyS' : y ∈ S := hyS
      have hGy : G y = ‖ψ y‖ₑ := by
        rw [hGdef]
        exact indicator_of_mem hyS' _
      have hdist : ‖x - y‖ ≤ 10 * L := by
        have hxy : x - y = Ψ τ (Function.invFun (Ψ τ) x) - Ψ τ (Function.invFun (Ψ τ) y) := by
          rw [Function.rightInverse_invFun hbij.2 x, Function.rightInverse_invFun hbij.2 y]
        rw [hxy]
        have hΦd : ‖Function.invFun (Ψ τ) x - Function.invFun (Ψ τ) y‖ ≤ 10 := by
          have hsub : Function.invFun (Ψ τ) x - Function.invFun (Ψ τ) y =
              (Function.invFun (Ψ τ) x - latticePt z) - (Function.invFun (Ψ τ) y - latticePt z) := by
            abel
          rw [hsub]
          calc _ ≤ ‖Function.invFun (Ψ τ) x - latticePt z‖ + ‖Function.invFun (Ψ τ) y - latticePt z‖ :=
                norm_sub_le _ _
            _ ≤ 10 := by linarith
        calc ‖Ψ τ (Function.invFun (Ψ τ) x) - Ψ τ (Function.invFun (Ψ τ) y)‖
            ≤ L * ‖Function.invFun (Ψ τ) x - Function.invFun (Ψ τ) y‖ := hlip _ _
          _ ≤ L * 10 := mul_le_mul_of_nonneg_left hΦd hL0
          _ = 10 * L := by ring
      have hu : x - y ≠ 0 := sub_ne_zero.2 (Ne.symm hy)
      have hmem : x - y ∈ Metric.closedBall (0 : Euc d) (10 * L) := by
        rw [Metric.mem_closedBall, dist_zero_right]
        exact hdist
      rw [indicator_of_mem hmem, hGy]
      have hA1 : ‖advCutoff χh Ψ τ (latticePt z) y - advCutoff χ Ψ τ (latticePt z) y‖ₑ ≤ 1 := by
        have ha := hf2 y
        have hb := hf1 y
        rw [← ofReal_norm_eq_enorm, Real.norm_eq_abs]
        apply ENNReal.ofReal_le_one.2
        rw [abs_le]
        constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]
      have hD : ‖partialDeriv idx μ y‖ₑ ≤ ENNReal.ofReal (max Λ 0) := by
        rw [← ofReal_norm_eq_enorm, Real.norm_eq_abs]
        exact ENNReal.ofReal_le_ofReal (hDbd y)
      have hB1 : ‖partialDeriv idx μ y * ψ y‖ₑ ≤ ENNReal.ofReal (max Λ 0) * ‖ψ y‖ₑ := by
        rw [enorm_mul]
        exact mul_le_mul_of_nonneg_right hD zero_le
      have hK1 : ‖rieszKernelGrad d s (x - y) i‖ₑ ≤ ENNReal.ofReal (σ * ‖x - y‖ ^ (-(s + 1))) := by
        rw [← ofReal_norm_eq_enorm]
        apply ENNReal.ofReal_le_ofReal
        calc ‖rieszKernelGrad d s (x - y) i‖ ≤ ‖rieszKernelGrad d s (x - y)‖ :=
              k4_comp_norm_le s (x - y) i
          _ ≤ max 1 s * ‖x - y‖ ^ (-s - 1) := kernel_bound_proof hs0 (x - y) hu
          _ = σ * ‖x - y‖ ^ (-(s + 1)) := by
              rw [show -(s + 1) = -s - 1 by ring]
      show ‖(advCutoff χh Ψ τ (latticePt z) y - advCutoff χ Ψ τ (latticePt z) y) *
          (partialDeriv idx μ y * ψ y) * rieszKernelGrad d s (x - y) i‖ₑ ≤ _
      rw [enorm_mul, enorm_mul]
      calc ‖advCutoff χh Ψ τ (latticePt z) y - advCutoff χ Ψ τ (latticePt z) y‖ₑ *
            ‖partialDeriv idx μ y * ψ y‖ₑ * ‖rieszKernelGrad d s (x - y) i‖ₑ
          ≤ 1 * (ENNReal.ofReal (max Λ 0) * ‖ψ y‖ₑ) * ENNReal.ofReal (σ * ‖x - y‖ ^ (-(s + 1))) :=
            mul_le_mul' (mul_le_mul' hA1 hB1) hK1
        _ = ENNReal.ofReal (σ * max Λ 0) * ENNReal.ofReal (‖x - y‖ ^ (-(s + 1))) * ‖ψ y‖ₑ := by
            simp only [one_mul, ENNReal.ofReal_mul hσ0]
            ring
    · have hyS' : y ∉ S := hyS
      have hG0 : G y = 0 := by
        rw [hGdef]
        exact indicator_of_notMem hyS' _
      have h8 : 8 ≤ ‖Function.invFun (Ψ τ) y - latticePt z‖ := not_lt.1 hyS
      have hA0 : advCutoff χh Ψ τ (latticePt z) y = 0 := hf4 y h8
      have hA1 : advCutoff χ Ψ τ (latticePt z) y = 0 := hf5 y (by linarith)
      have hg0 : g x y = 0 := by
        simp only [hgdef, hA0, hA1, sub_zero, zero_mul]
      rw [hG0, hg0]
      simp
  obtain ⟨hA, hB⟩ := hgen (tsupport (advCutoff χ Ψ τ (latticePt z))) g G (σ * max Λ 0) (10 * L)
    (mul_nonneg hσ0 (le_max_right _ _)) (by linarith) hGm hgm hbd
  have hnn : 0 ≤ σ * max Λ 0 * CK * (10 * L) ^ ((d : ℝ) - (s + 1)) :=
    mul_nonneg (mul_nonneg (mul_nonneg hσ0 (le_max_right _ _)) hCK.le) (Real.rpow_nonneg (by linarith) _)
  have hEsq : (ENNReal.ofReal (σ * max Λ 0 * CK * (10 * L) ^ ((d : ℝ) - (s + 1)))) ^ 2 ≤
      ENNReal.ofReal (σ ^ 2 * CK ^ 2 * 10 ^ (2 * d) * L ^ (2 * d) * Λ ^ 2) := by
    rw [← ENNReal.ofReal_pow hnn]
    exact ENNReal.ofReal_le_ofReal (cc1_pow σ CK Λ L _ hσ0 hCK.le hL (by linarith))
  obtain ⟨-, hQm, -, hiff, -⟩ := flowCell_geometry_proof Ψ τ L hL0 hbij hlip
  have hcellE : ∀ z' : Fin d → ℤ, ∫⁻ y, (flowCell Ψ τ z').indicator (fun y => ‖ψ y‖ₑ ^ 2) y =
      (eLpNorm ((flowCell Ψ τ z').indicator ψ) 2 volume) ^ 2 := by
    intro z'
    rw [l1_sq_eLpNorm_ae _ ((hψ.indicator (hQm z')).aestronglyMeasurable)]
    exact lintegral_congr fun y => (cc_sq_indicator (flowCell Ψ τ z') ψ y).symm
  have hcov : ∀ y ∈ S, ∃ z' : Fin d → ℤ,
      1 ≤ (kcCoef d (8 + Real.sqrt d) 1 0 z z' : ℝ≥0∞) ∧ y ∈ flowCell Ψ τ z' := by
    intro y hy
    have hy' : ‖Function.invFun (Ψ τ) y - latticePt z‖ < 8 := hy
    obtain ⟨zf, hzf⟩ : ∃ zf : Fin d → ℤ, ∀ i, zf i = ⌊Function.invFun (Ψ τ) y i⌋ :=
      ⟨fun i => ⌊Function.invFun (Ψ τ) y i⌋, fun i => rfl⟩
    have e1 : ∀ i, (Function.invFun (Ψ τ) y - latticePt zf) i =
        Function.invFun (Ψ τ) y i - ((zf i : ℤ) : ℝ) := by
      intro i
      simp [latticePt]
    have hcoord : ∀ i, 0 ≤ (Function.invFun (Ψ τ) y - latticePt zf) i ∧
        (Function.invFun (Ψ τ) y - latticePt zf) i ≤ 1 := by
      intro i
      rw [e1 i, hzf i]
      exact ⟨by linarith [Int.floor_le (Function.invFun (Ψ τ) y i)],
        by linarith [Int.lt_floor_add_one (Function.invFun (Ψ τ) y i)]⟩
    have hle : ‖latticePt z - latticePt zf‖ ≤ 8 + Real.sqrt d := by
      have htri : latticePt z - latticePt zf =
          (latticePt z - Function.invFun (Ψ τ) y) + (Function.invFun (Ψ τ) y - latticePt zf) := by
        abel
      rw [htri]
      have hn := norm_sub_rev (latticePt z) (Function.invFun (Ψ τ) y)
      have hbox : ‖Function.invFun (Ψ τ) y - latticePt zf‖ ≤ Real.sqrt d := f3_box_norm_le _ hcoord
      calc _ ≤ ‖latticePt z - Function.invFun (Ψ τ) y‖ + ‖Function.invFun (Ψ τ) y - latticePt zf‖ :=
            norm_add_le _ _
        _ ≤ 8 + Real.sqrt d := by linarith
    have hk : kcCoef d (8 + Real.sqrt d) 1 0 z zf = 1 := by
      unfold kcCoef
      rw [if_pos hle]
      simp
    refine ⟨zf, ?_, (hiff zf y).2 hcoord⟩
    rw [hk]
    simp
  have hGsum : ∫⁻ y, G y ^ 2 ≤ ∑' z' : Fin d → ℤ, (kcCoef d (8 + Real.sqrt d) 1 0 z z' : ℝ≥0∞) *
      (eLpNorm ((flowCell Ψ τ z').indicator ψ) 2 volume) ^ 2 := by
    have hG2 : ∀ y, G y ^ 2 = S.indicator (fun y => ‖ψ y‖ₑ ^ 2) y := by
      intro y
      by_cases hy : y ∈ S
      · rw [hGdef, indicator_of_mem hy, indicator_of_mem hy]
      · rw [hGdef, indicator_of_notMem hy, indicator_of_notMem hy, zero_pow two_ne_zero]
    calc ∫⁻ y, G y ^ 2 = ∫⁻ y, S.indicator (fun y => ‖ψ y‖ₑ ^ 2) y := lintegral_congr hG2
      _ ≤ ∑' z' : Fin d → ℤ, (kcCoef d (8 + Real.sqrt d) 1 0 z z' : ℝ≥0∞) *
            ∫⁻ y, (flowCell Ψ τ z').indicator (fun y => ‖ψ y‖ₑ ^ 2) y :=
          cc_cover S (fun z' => flowCell Ψ τ z') hQm
            (fun z' => (kcCoef d (8 + Real.sqrt d) 1 0 z z' : ℝ≥0∞))
            (fun y => ‖ψ y‖ₑ ^ 2) (hψ.enorm.pow_const 2) hcov
      _ = ∑' z' : Fin d → ℤ, (kcCoef d (8 + Real.sqrt d) 1 0 z z' : ℝ≥0∞) *
            (eLpNorm ((flowCell Ψ τ z').indicator ψ) 2 volume) ^ 2 := by
          apply tsum_congr
          intro z'
          rw [hcellE z']
  have hA1x : ∀ x, ‖advCutoff χ Ψ τ (latticePt z) x‖ₑ ≤ 1 := by
    intro x
    have hx := hf1 x
    rw [← ofReal_norm_eq_enorm, Real.norm_eq_abs]
    apply ENNReal.ofReal_le_one.2
    rw [abs_le]
    constructor <;> linarith [hx.1, hx.2]
  have hIm : StronglyMeasurable (fun x => ∫ y, g x y) := hgm.stronglyMeasurable.integral_prod_right'
  have hFm : AEStronglyMeasurable (fun x => advCutoff χ Ψ τ (latticePt z) x * ∫ y, g x y) volume :=
    (hAc.stronglyMeasurable.mul hIm).aestronglyMeasurable
  have hpt : ∀ x, ‖advCutoff χ Ψ τ (latticePt z) x * ∫ y, g x y‖ₑ ^ 2 ≤
      ((tsupport (advCutoff χ Ψ τ (latticePt z))).indicator (fun _ => (1 : ℝ≥0∞)) x *
        ‖∫ y, g x y‖ₑ) ^ 2 := by
    intro x
    by_cases hx : x ∈ tsupport (advCutoff χ Ψ τ (latticePt z))
    · rw [indicator_of_mem hx, one_mul, enorm_mul]
      exact pow_le_pow_left₀ zero_le (mul_le_of_le_one_left zero_le (hA1x x)) 2
    · rw [indicator_of_notMem hx, image_eq_zero_of_notMem_tsupport hx]
      simp
  refine ⟨?_, ?_⟩
  · calc (eLpNorm (fun x => advCutoff χ Ψ τ (latticePt z) x * ∫ y, g x y) 2 volume) ^ 2
        = ∫⁻ x, ‖advCutoff χ Ψ τ (latticePt z) x * ∫ y, g x y‖ₑ ^ 2 := l1_sq_eLpNorm_ae _ hFm
      _ ≤ ∫⁻ x, ((tsupport (advCutoff χ Ψ τ (latticePt z))).indicator (fun _ => (1 : ℝ≥0∞)) x *
            ‖∫ y, g x y‖ₑ) ^ 2 := lintegral_mono hpt
      _ ≤ (ENNReal.ofReal (σ * max Λ 0 * CK * (10 * L) ^ ((d : ℝ) - (s + 1)))) ^ 2 * ∫⁻ y, G y ^ 2 := hA
      _ ≤ ENNReal.ofReal (σ ^ 2 * CK ^ 2 * 10 ^ (2 * d) * L ^ (2 * d) * Λ ^ 2) *
            ∑' z' : Fin d → ℤ, (kcCoef d (8 + Real.sqrt d) 1 0 z z' : ℝ≥0∞) *
              (eLpNorm ((flowCell Ψ τ z').indicator ψ) 2 volume) ^ 2 :=
          mul_le_mul' hEsq hGsum
  · intro hP
    exact hB (lt_of_le_of_lt (mul_le_mul' hEsq hGsum) hP)

end HRS.MH.Screened
