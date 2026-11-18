import HRS.MC.Q714AsmBase
import HRS.MC.Q714GTFinal
import HRS.MC.Q714GW

/-!
# Packet ASM (row 7.14), part 2: the window-level estimates

For `a ≥ 0` the Gaussian Taylor bounds (`gaussian_taylor_proof`) for the windows `Z^{a+·}` and `Z_{∞,T}`, and from them
(with `quench_window_tensors_proof`) the uniform estimates (P2), (P3) used by `asm_seq_expansion`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.Q714.Asm

open HRS HRS.Sec7

variable {d : ℕ}

/-- The two Gaussian Taylor bounds for the window `Z^{a+·}` against the stationary window, for a given
`δ`-bound on `Δ`; `Δ` is also exhibited as a continuous linear functional. -/
theorem asm_gt_step
    (hGT : type_of% @HRS.MC.Q714.GT.gaussian_taylor_proof)
    (hGW : type_of% @HRS.MC.Q714.GW.gaussian_window_proof)
    (hd : 2 ≤ d) {s β β₀ : ℝ} (hβ : 0 < β) (hβ₀ : 0 < β₀)
    (D : DynData d) (hD : IsGradientData D s β (fun _ => 0)) (m : ℝ) (hm : (d : ℝ) / 2 + 1 < m)
    (T : ℝ) (hT : 0 < T)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → Ω → NegSobolev d m) (hZ : IsGaussianLimitField D (fun _ _ => 1) volume β₀ m P Z)
    {Ω' : Type} [MeasurableSpace Ω'] (Q : Measure Ω') [IsProbabilityMeasure Q]
    (Zs : ℝ → Ω' → NegSobolev d m) (hZs : IsGaussianLimitField D (fun _ _ => 1) volume β m Q Zs)
    (a : ℝ) (ha : 0 ≤ a) (Δ : (PathSpace d m T [×2]→L[ℝ] ℝ) → ℝ)
    (hΔ : ∀ M : PathSpace d m T [×2]→L[ℝ] ℝ, Δ M =
      ∫ ω, M ![procWin m T a Z ω, procWin m T a Z ω] ∂P -
        ∫ ω, M ![procWin m T 0 Zs ω, procWin m T 0 Zs ω] ∂Q)
    (δ : ℝ) (hδ : ∀ M : PathSpace d m T [×2]→L[ℝ] ℝ, ‖M‖ ≤ 1 → |Δ M| ≤ δ)
    (Φ : PathSpace d m T → ℝ) (hΦ : Φ ∈ CbUnitBall (PathSpace d m T) 5) :
    ∃ L : (PathSpace d m T [×2]→L[ℝ] ℝ) →L[ℝ] ℝ, (∀ M, L M = Δ M) ∧
      |∫ ω, Φ (procWin m T a Z ω) ∂P - ∫ ω, Φ (procWin m T 0 Zs ω) ∂Q| ≤ δ / 2 ∧
      |∫ ω, Φ (procWin m T a Z ω) ∂P - ∫ ω, Φ (procWin m T 0 Zs ω) ∂Q -
        (1 / 2) * ∫ ω, L (iteratedFDeriv ℝ 2 Φ (procWin m T 0 Zs ω)) ∂Q| ≤ δ ^ 2 / 8 := by
  have hw2 := hGW hd hβ hβ₀ D hD m hm T hT P Z hZ a ha
  have hw1 := hGW hd hβ hβ D hD m hm T hT Q Zs hZs 0 le_rfl
  have hmeas : ∀ M : PathSpace d m T [×2]→L[ℝ] ℝ, Continuous fun z : PathSpace d m T => M ![z, z] :=
    fun M => M.cont.comp (continuous_pi fun i => by fin_cases i <;> exact continuous_id)
  have hΔ' : ∀ M : PathSpace d m T [×2]→L[ℝ] ℝ,
      Δ M = ∫ z, M ![z, z] ∂(P.map (procWin m T a Z)) -
        ∫ z, M ![z, z] ∂(Q.map (procWin m T 0 Zs)) := by
    intro M
    rw [hΔ, integral_map hw2.1 (hmeas M).aestronglyMeasurable,
      integral_map hw1.1 (hmeas M).aestronglyMeasurable]
  obtain ⟨L, hLΔ, -, -⟩ := HRS.MC.Q714.GT.gt_delta_clm (gaussian_sqnorm_integrable hw1.2)
    (gaussian_sqnorm_integrable hw2.2) Δ hΔ' δ hδ
  have hgt := hGT Q (procWin m T 0 Zs) P (procWin m T a Z) hw1.1 hw2.1 hw1.2 hw2.2 Δ hΔ δ hδ Φ
    (asm_memCb4 hΦ) 1 1 (asm_norm2 hΦ) (asm_norm4 hΦ)
  refine ⟨L, hLΔ, ?_, ?_⟩
  · simpa using hgt.1
  · have e : ∫ ω, Δ (iteratedFDeriv ℝ 2 Φ (procWin m T 0 Zs ω)) ∂Q =
        ∫ ω, L (iteratedFDeriv ℝ 2 Φ (procWin m T 0 Zs ω)) ∂Q := by
      congr 1; funext ω; exact (hLΔ _).symm
    have := hgt.2
    rw [e] at this
    simpa using this

/-- Window-level estimates (P2), (P3) for `β₀ ≠ β`. -/
theorem asm_windows
    (hGT : type_of% @HRS.MC.Q714.GT.gaussian_taylor_proof)
    (hGW : type_of% @HRS.MC.Q714.GW.gaussian_window_proof)
    (hd : 2 ≤ d) {s β β₀ : ℝ} (hβ : 0 < β) (hβ₀ : 0 < β₀) (hne : β₀ ≠ β)
    (D : DynData d) (hD : IsGradientData D s β (fun _ => 0)) (m : ℝ) (hm : (d : ℝ) / 2 + 1 < m)
    (T : ℝ) (hT : 0 < T)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → Ω → NegSobolev d m) (hZ : IsGaussianLimitField D (fun _ _ => 1) volume β₀ m P Z)
    {Ω' : Type} [MeasurableSpace Ω'] (Q : Measure Ω') [IsProbabilityMeasure Q]
    (Zs : ℝ → Ω' → NegSobolev d m) (hZs : IsGaussianLimitField D (fun _ _ => 1) volume β m Q Zs) :
    0 < lamStar d s β ∧ ∃ C : ℝ,
      (∀ a : ℝ, 0 ≤ a → ∀ Φ ∈ CbUnitBall (PathSpace d m T) 5,
        |∫ ω, Φ (procWin m T a Z ω) ∂P - ∫ ω, Φ (procWin m T 0 Zs ω) ∂Q| ≤
          C * Real.exp (-2 * lamStar d s β * a)) ∧
      (∀ ε : ℝ, 0 < ε → ∃ a₀ : ℝ, ∀ a : ℝ, a₀ ≤ a → ∀ Φ ∈ CbUnitBall (PathSpace d m T) 5,
        |Real.exp (2 * lamStar d s β * a) *
            (∫ ω, Φ (procWin m T a Z ω) ∂P - ∫ ω, Φ (procWin m T 0 Zs ω) ∂Q) -
          (∫ ω, slowTensor d s β β₀ m T (iteratedFDeriv ℝ 2 Φ (procWin m T 0 Zs ω)) ∂Q) / 2| ≤ ε) := by
  have hq := quench_window_tensors_proof hd hβ hβ₀ hne D hD m hm T hT P Z hZ Q Zs hZs
  obtain ⟨⟨hlam, hfin, -⟩, -, hiii, -, cT, CT, hcT, hcTCT, hiv⟩ := hq
  simp only at hiii hiv
  set l := lamStar d s β with hl
  obtain ⟨S, hS⟩ := asm_slow_clm s β β₀ m T hfin
  refine ⟨hlam, CT / 2, ?_, ?_⟩
  · intro a ha Φ hΦ
    obtain ⟨L, -, h1, -⟩ := asm_gt_step hGT hGW hd hβ hβ₀ D hD m hm T hT P Z hZ Q Zs hZs a ha
      (fun M => ∫ ω, M ![procWin m T a Z ω, procWin m T a Z ω] ∂P -
        ∫ ω, M ![procWin m T 0 Zs ω, procWin m T 0 Zs ω] ∂Q) (fun M => rfl) (CT * Real.exp (-2 * l * a)) (fun M hM => (hiv a ha).1 M hM) Φ hΦ
    calc _ ≤ _ := h1
      _ = _ := by ring
  · intro ε hε
    obtain ⟨a₁, ha₁⟩ := hiii (ε / 2) (by positivity)
    have hev : ∀ᶠ a : ℝ in atTop, CT ^ 2 * Real.exp (-2 * l * a) / 8 ≤ ε / 2 := by
      have h0 : Tendsto (fun a : ℝ => CT ^ 2 * Real.exp (-2 * l * a) / 8) atTop (𝓝 (CT ^ 2 * 0 / 8)) := by
        have : Tendsto (fun a : ℝ => Real.exp (-2 * l * a)) atTop (𝓝 0) := by
          rw [Real.tendsto_exp_comp_nhds_zero]
          have : Tendsto (fun a : ℝ => (2 * l) * a) atTop atTop :=
            tendsto_id.const_mul_atTop (by linarith)
          exact (tendsto_neg_atTop_atBot.comp this).congr fun a => by simp only [Function.comp]; ring
        exact (this.const_mul _).div_const _
      simp only [mul_zero, zero_div] at h0
      exact h0.eventually_le_const (by linarith)
    obtain ⟨a₂, ha₂⟩ := eventually_atTop.1 (hev.and ((eventually_ge_atTop a₁).and (eventually_ge_atTop 0)))
    refine ⟨a₂, fun a ha Φ hΦ => ?_⟩
    obtain ⟨hev1, ha1, ha0⟩ := ha₂ a ha
    obtain ⟨L, hLΔ, -, h2⟩ := asm_gt_step hGT hGW hd hβ hβ₀ D hD m hm T hT P Z hZ Q Zs hZs a ha0
      (fun M => ∫ ω, M ![procWin m T a Z ω, procWin m T a Z ω] ∂P -
        ∫ ω, M ![procWin m T 0 Zs ω, procWin m T 0 Zs ω] ∂Q) (fun M => rfl) (CT * Real.exp (-2 * l * a)) (fun M hM => (hiv a ha0).1 M hM) Φ hΦ
    have hmQ := (hGW hd hβ hβ D hD m hm T hT Q Zs hZs 0 le_rfl).1
    have hint := asm_integral_clm hmQ hΦ L S (Real.exp (2 * l * a)) 1 (ε / 2) (fun M hM => by
      have := ha₁ a ha1 M hM
      rw [hLΔ, hS]
      simpa using this)
    have hSl : ∫ ω, S (iteratedFDeriv ℝ 2 Φ (procWin m T 0 Zs ω)) ∂Q =
        ∫ ω, slowTensor d s β β₀ m T (iteratedFDeriv ℝ 2 Φ (procWin m T 0 Zs ω)) ∂Q := by
      congr 1; funext ω; exact hS _
    rw [hSl] at hint
    set X := ∫ ω, Φ (procWin m T a Z ω) ∂P - ∫ ω, Φ (procWin m T 0 Zs ω) ∂Q with hX
    set Y := ∫ ω, L (iteratedFDeriv ℝ 2 Φ (procWin m T 0 Zs ω)) ∂Q with hY
    set Sl := ∫ ω, slowTensor d s β β₀ m T (iteratedFDeriv ℝ 2 Φ (procWin m T 0 Zs ω)) ∂Q with hSlD
    set u := Real.exp (2 * l * a) with hu
    have hu0 : 0 < u := Real.exp_pos _
    have hui : Real.exp (-2 * l * a) = u⁻¹ := by
      rw [hu, ← Real.exp_neg]; congr 1; ring
    have k1 : u * X - Sl / 2 = u * (X - 1 / 2 * Y) + (1 / 2) * (u * Y - 1 * Sl) := by ring
    have k2 : u * (CT * Real.exp (-2 * l * a)) ^ 2 / 8 = CT ^ 2 * Real.exp (-2 * l * a) / 8 := by
      rw [hui]; field_simp
    rw [k1]
    calc _ ≤ |u * (X - 1 / 2 * Y)| + |(1 / 2) * (u * Y - 1 * Sl)| := abs_add_le _ _
      _ = u * |X - 1 / 2 * Y| + (1 / 2) * |u * Y - 1 * Sl| := by
          rw [abs_mul, abs_mul, abs_of_pos hu0]; norm_num
      _ ≤ u * ((CT * Real.exp (-2 * l * a)) ^ 2 / 8) + (1 / 2) * (ε / 2) := by
          gcongr
      _ ≤ ε := by
          have : u * ((CT * Real.exp (-2 * l * a)) ^ 2 / 8) = CT ^ 2 * Real.exp (-2 * l * a) / 8 := by
            rw [← k2]; ring
          rw [this]; linarith

end HRS.MC.Q714.Asm

end
