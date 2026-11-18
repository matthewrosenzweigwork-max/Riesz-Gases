import HRS.MC.Q714CTGauss

/-!
# Packet 7.14 CT: the cosine test `cos_test`

`Φ = (1/6) cos ∘ ℓ`, `ℓ` the coordinate of the time-zero value on a slowest mode.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.Q714.CT

open HRS HRS.Sec7 HRS.Qch

/-- `|e^{-y} - 1| ≥ |y|/2` for `|y| ≤ 1`. -/
theorem ct_abs_exp_neg_sub_one (y : ℝ) (hy : |y| ≤ 1) : |y| / 2 ≤ |Real.exp (-y) - 1| := by
  rw [abs_le] at hy
  rcases le_total 0 y with h | h
  · have h1 := Real.add_one_le_exp y
    have h2 : Real.exp (-y) * (1 + y) ≤ 1 := by
      have := Real.add_one_le_exp y
      have h3 : Real.exp (-y) * Real.exp y = 1 := by rw [← Real.exp_add]; simp
      nlinarith [Real.exp_pos (-y)]
    have h4 : Real.exp (-y) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    rw [abs_of_nonneg h, abs_of_nonpos (by linarith)]
    nlinarith [Real.exp_pos (-y)]
  · have h1 := Real.add_one_le_exp (-y)
    rw [abs_of_nonpos h, abs_of_nonneg (by linarith)]
    linarith

theorem ct_expect {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : Type} [NormedAddCommGroup B] [NormedSpace ℝ B]
    (L : B →L[ℝ] ℝ) (W : Ω → B) (hX : HasGaussianLaw (fun ω => L (W ω)) P)
    (h0 : ∫ ω, L (W ω) ∂P = 0) :
    ∫ ω, ctPhi L (W ω) ∂P = (1 / 6) * Real.exp (-(1 / 2) * ∫ ω, L (W ω) * L (W ω) ∂P) := by
  have := ct_integral_cos hX h0 1
  simp only [one_mul] at this
  unfold ctPhi
  rw [integral_const_mul, this]
  congr 3
  · norm_num
  · refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp [sq]

variable {d : ℕ}

theorem cos_test_proof (hd : 2 ≤ d) {s β β₀ : ℝ} (hβ : 0 < β) (hβ₀ : 0 < β₀) (hne : β₀ ≠ β)
    (D : DynData d) (hD : IsGradientData D s β (fun _ => 0)) (m : ℝ) (hm : (d : ℝ) / 2 + 1 < m)
    (T : ℝ) (hT : 0 < T)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → Ω → NegSobolev d m) (hZ : IsGaussianLimitField D (fun _ _ => 1) volume β₀ m P Z)
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Zs : ℝ → Ω' → NegSobolev d m) (hZs : IsGaussianLimitField D (fun _ _ => 1) volume β m P' Zs) :
    ∃ Φ ∈ CbUnitBall (PathSpace d m T) 5, ∃ c : ℝ, 0 < c ∧ ∃ a₀ : ℝ, ∀ a : ℝ, a₀ ≤ a →
      c * Real.exp (-2 * lamStar d s β * a) ≤
        |∫ ω, Φ (procWin m T a Z ω) ∂P - ∫ ω, Φ (procWin m T 0 Zs ω) ∂P'| := by
  have hs0 : 0 ≤ s := hD.1 ▸ D.hs0
  have hsd : s < d := hD.1 ▸ D.hsd
  obtain ⟨Y, mf⟩ := Qch.modeField_of_limit hd hβ hβ₀ D hD P Z hZ
  obtain ⟨Ys, mf'⟩ := Qch.modeField_of_limit hd hβ hβ D hD P' Zs hZs
  set Δ : ℝ → (PathSpace d m T [×2]→L[ℝ] ℝ) → ℝ := fun a M =>
      ∫ ω, M ![procWin m T a Z ω, procWin m T a Z ω] ∂P -
        ∫ ω, M ![procWin m T 0 Zs ω, procWin m T 0 Zs ω] ∂P' with hΔ
  have hser : ∀ a : ℝ, 0 ≤ a → ∀ M : PathSpace d m T [×2]→L[ℝ] ℝ, Δ a M =
      ∑' k : PosHalf d, deltaVar d s β β₀ k.1 * Real.exp (-2 * lamMode d s β k.1 * a) *
          (M ![modePath m T (lamMode d s β k.1) (modeFn k.1 true),
               modePath m T (lamMode d s β k.1) (modeFn k.1 true)] +
            M ![modePath m T (lamMode d s β k.1) (modeFn k.1 false),
               modePath m T (lamMode d s β k.1) (modeFn k.1 false)]) :=
    fun a ha M => Qch.window_series hd hs0 hsd hβ hβ₀ hm mf mf' hT ha M
  obtain ⟨k0, c0, hc0, hΔ0⟩ := ct_test_form hd hs0 hsd hβ Δ hβ₀ hne hT hser
  have hlam : 0 < lamStar d s β := (Qch.gap_facts hd hs0 hsd hβ).1
  set L : PathSpace d m T →L[ℝ] ℝ := ell hT (idx k0 true) with hL
  have hLn : ‖L‖ ≤ 1 := norm_ell_le hT _
  -- the stationary variance
  obtain ⟨hGs, hms⟩ := ct_gauss hd hs0 hsd hβ hT mf' k0 (le_refl (0 : ℝ))
  set Vs : ℝ := ∫ ω, L (procWin m T 0 Zs ω) * L (procWin m T 0 Zs ω) ∂P' with hVs
  refine ⟨ctPhi L, ct_mem_cbUnitBall L hLn, (1 / 24) * Real.exp (-(1 / 2) * Vs) * |c0|,
    by positivity, max 0 (Real.log |c0| / (2 * lamStar d s β)), fun a ha => ?_⟩
  have ha0 : 0 ≤ a := le_trans (le_max_left _ _) ha
  have ha1 : Real.log |c0| / (2 * lamStar d s β) ≤ a := le_trans (le_max_right _ _) ha
  obtain ⟨hGa, hma⟩ := ct_gauss hd hs0 hsd hβ hT mf k0 ha0
  set Va : ℝ := ∫ ω, L (procWin m T a Z ω) * L (procWin m T a Z ω) ∂P with hVa
  rw [ct_expect L _ hGa hma, ct_expect L _ hGs hms]
  have hx : Va - Vs = Real.exp (-2 * lamStar d s β * a) * c0 := by
    rw [← hΔ0 a ha0]
    simp only [hΔ, hVa, hVs, hL, M0of_diag]
  have hxb : |Va - Vs| ≤ 1 := by
    rw [hx, abs_mul, abs_of_pos (Real.exp_pos _)]
    have hc : 0 < |c0| := abs_pos.2 hc0
    have h1 : Real.log |c0| ≤ 2 * lamStar d s β * a := by
      have := (div_le_iff₀ (by positivity : 0 < 2 * lamStar d s β)).1 ha1
      linarith
    have h2 : Real.exp (-2 * lamStar d s β * a) ≤ |c0|⁻¹ := by
      calc _ ≤ Real.exp (-Real.log |c0|) := Real.exp_le_exp.2 (by linarith)
        _ = |c0|⁻¹ := by rw [Real.exp_neg, Real.exp_log hc]
    calc Real.exp (-2 * lamStar d s β * a) * |c0| ≤ |c0|⁻¹ * |c0| :=
          mul_le_mul_of_nonneg_right h2 hc.le
      _ = 1 := inv_mul_cancel₀ hc.ne'
  have hkey := ct_abs_exp_neg_sub_one ((Va - Vs) / 2) (by rw [abs_div]; norm_num; linarith)
  have e1 : Real.exp (-(1 / 2) * Va) = Real.exp (-(1 / 2) * Vs) * Real.exp (-((Va - Vs) / 2)) := by
    rw [← Real.exp_add]; congr 1; ring
  have e2 : (1 / 6 : ℝ) * Real.exp (-(1 / 2) * Va) - (1 / 6) * Real.exp (-(1 / 2) * Vs) =
      (1 / 6) * Real.exp (-(1 / 2) * Vs) * (Real.exp (-((Va - Vs) / 2)) - 1) := by
    rw [e1]; ring
  rw [e2, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / 6 * Real.exp (-(1 / 2) * Vs))]
  have e3 : |Va - Vs| = Real.exp (-2 * lamStar d s β * a) * |c0| := by
    rw [hx, abs_mul, abs_of_pos (Real.exp_pos _)]
  have e4 : |(Va - Vs) / 2| = |Va - Vs| / 2 := by rw [abs_div]; norm_num
  rw [e4] at hkey
  have hpos : 0 < 1 / 6 * Real.exp (-(1 / 2) * Vs) := by positivity
  calc 1 / 24 * Real.exp (-(1 / 2) * Vs) * |c0| * Real.exp (-2 * lamStar d s β * a)
      = (1 / 6 * Real.exp (-(1 / 2) * Vs)) * ((|Va - Vs| / 2) / 2) := by rw [e3]; ring
    _ ≤ (1 / 6 * Real.exp (-(1 / 2) * Vs)) * |Real.exp (-((Va - Vs) / 2)) - 1| := by
        refine mul_le_mul_of_nonneg_left ?_ hpos.le
        have := abs_nonneg (Va - Vs)
        linarith

end HRS.MC.Q714.CT
