/-
# HRS.Equilibrium.L48Aux4 — Proposition 4.8, part 4: the exact quotient identity

TeX `R:eq:quotient-identity`: with `a₀ = e^{-tλ g₊(x-·)}`, `B = ∫ a₀ dμ`, `F = ∫ g₊(x-·) a₀ dμ`,
`ψ = F a₀ - B g₊(x-·) a₀` (so `∫ ψ dμ = 0`), `e^{-v} = 1 - v + H(v)`:
`B N_Y - F Z_Y = ∫ ψ v_Y dμ - ∫ ψ H(v_Y) dμ`, hence
`|T₁ - F/B| ≤ (|∫ ψ v_Y dμ| + F R₀ + B R₁) / (B e^{-3βCg})`,
`R₀ = ∫ a₀ H(v_Y) dμ`, `R₁ = ∫ g₊(x-·) a₀ H(v_Y) dμ` (`l48_quotient`).
-/
import HRS.Equilibrium.L48Aux3

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace HRS

namespace L48

variable {d : ℕ} {s c : ℝ}

open HRS.External HRS.PoleCavityAux HRS.MarginalAux HRS.ProdTransfer HRS.CavResp

/-- The pole factor `a₀(y) = e^{-tλ g₊(x-y)}`. -/
def l48_a0 (d : ℕ) (s c β : ℝ) (N : ℕ) (x : Torus d) (t : ℝ) (y : Torus d) : ℝ :=
  Real.exp (-(t * (β / N)) * gPlus d s c (x - y))

/-- `B_t = ∫ a₀ dμ`. -/
def l48_B (d : ℕ) (s c β : ℝ) (ρ : Torus d → ℝ) (N : ℕ) (x : Torus d) (t : ℝ) : ℝ :=
  ∫ y, l48_a0 d s c β N x t y ∂(withDensityReal ρ)

/-- `F_t = ∫ g₊(x - y) a₀(y) dμ`. -/
def l48_F (d : ℕ) (s c β : ℝ) (ρ : Torus d → ℝ) (N : ℕ) (x : Torus d) (t : ℝ) : ℝ :=
  ∫ y, gPlus d s c (x - y) * l48_a0 d s c β N x t y ∂(withDensityReal ρ)

/-- `ψ = F a₀ - B g₊(x-·) a₀`. -/
def l48_psi (d : ℕ) (s c β : ℝ) (ρ : Torus d → ℝ) (N : ℕ) (x : Torus d) (t : ℝ) (y : Torus d) : ℝ :=
  l48_F d s c β ρ N x t * l48_a0 d s c β N x t y -
    l48_B d s c β ρ N x t * (gPlus d s c (x - y) * l48_a0 d s c β N x t y)

/-- A nonnegative measurable function with finite `lintegral` is integrable, with
`∫ f = (∫⁻ ofReal f).toReal`. -/
theorem l48_int_of_lint {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    (hf : Measurable f) (h0 : ∀ y, 0 ≤ f y) (h : ∫⁻ y, ENNReal.ofReal (f y) ∂μ < ⊤) :
    Integrable f μ ∧ ∫ y, f y ∂μ = (∫⁻ y, ENNReal.ofReal (f y) ∂μ).toReal := by
  refine ⟨⟨hf.aestronglyMeasurable, ?_⟩, ?_⟩
  · refine lt_of_le_of_lt (le_of_eq ?_) h
    refine lintegral_congr fun y => ?_
    rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (h0 y)]
  · exact integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall h0) hf.aestronglyMeasurable

section Quot

variable (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) {β : ℝ} (hβ : 0 < β) {ρ : Torus d → ℝ}
  (hρ : SmoothPosDensity ρ) (hc : ∀ z, 0 ≤ periodicRiesz d s z + c)

include hd hcrit hβ hρ hc

theorem l48_a0_pos (N : ℕ) (x : Torus d) (t : ℝ) (y : Torus d) : 0 < l48_a0 d s c β N x t y :=
  Real.exp_pos _

theorem l48_a0_le_one {N : ℕ} (hN : 2 ≤ N) (x : Torus d) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (y : Torus d) : l48_a0 d s c β N x t y ≤ 1 := by
  unfold l48_a0
  rw [Real.exp_le_one_iff]
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have h1 : 0 ≤ t * (β / N) := mul_nonneg ht.1 (by positivity)
  have h2 : 0 ≤ gPlus d s c (x - y) := hc _
  nlinarith

theorem l48_meas_a0 (N : ℕ) (x : Torus d) (t : ℝ) :
    Measurable (l48_a0 d s c β N x t) := by
  obtain ⟨hs0, hsd⟩ := hs_aux hd hcrit
  have hgm := measurable_gPlus hd hs0 hsd c
  unfold l48_a0
  exact Real.measurable_exp.comp ((hgm.comp (measurable_const.sub measurable_id)).const_mul _)

theorem l48_BF_bounds {Cg : ℝ} (hCg : ∀ y, 0 ≤ convMeasure (gPlus d s c) (withDensityReal ρ) y ∧
      convMeasure (gPlus d s c) (withDensityReal ρ) y ≤ Cg)
    {N : ℕ} (hN : 2 ≤ N) (x : Torus d) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    Real.exp (-(β * Cg)) ≤ l48_B d s c β ρ N x t ∧ l48_B d s c β ρ N x t ≤ 1 ∧
      0 ≤ l48_F d s c β ρ N x t ∧ l48_F d s c β ρ N x t ≤ Cg := by
  obtain ⟨hs0, hsd⟩ := hs_aux hd hcrit
  have hμ := isProbabilityMeasure_mu hρ
  have hgm := measurable_gPlus hd hs0 hsd c
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlam : 0 ≤ β / N := by positivity
  have hlam1 : β / N ≤ β := by
    rw [div_le_iff₀ hN0]
    have : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
    nlinarith
  have htl : 0 ≤ t * (β / N) := mul_nonneg ht.1 hlam
  have htl1 : t * (β / N) ≤ β := by nlinarith [ht.2]
  have hCg0 : 0 ≤ Cg := (hCg 0).1.trans (hCg 0).2
  have hGi := gPlus_int hd hcrit hβ hρ hc hs0 hsd x
  have hGm : Measurable fun y => gPlus d s c (x - y) := hgm.comp (measurable_const.sub measurable_id)
  have ha0m := l48_meas_a0 hd hcrit hβ hρ hc (β := β) N x t
  have ha0i : Integrable (l48_a0 d s c β N x t) (withDensityReal ρ) :=
    Integrable.mono' (integrable_const (1 : ℝ)) ha0m.aestronglyMeasurable
      (Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_of_pos (l48_a0_pos hd hcrit hβ hρ hc N x t y)]
        exact l48_a0_le_one hd hcrit hβ hρ hc hN x ht y)
  have hFi : Integrable (fun y => gPlus d s c (x - y) * l48_a0 d s c β N x t y) (withDensityReal ρ) := by
    refine Integrable.mono' hGi (hGm.mul ha0m).aestronglyMeasurable (Eventually.of_forall fun y => ?_)
    have hG0 : 0 ≤ gPlus d s c (x - y) := hc _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hG0 (l48_a0_pos hd hcrit hβ hρ hc N x t y).le)]
    calc gPlus d s c (x - y) * l48_a0 d s c β N x t y ≤ gPlus d s c (x - y) * 1 :=
          mul_le_mul_of_nonneg_left (l48_a0_le_one hd hcrit hβ hρ hc hN x ht y) hG0
      _ = gPlus d s c (x - y) := mul_one _
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- Jensen via the tangent line
    set u : Torus d → ℝ := fun y => -(t * (β / N)) * gPlus d s c (x - y) with hu
    have hui : Integrable u (withDensityReal ρ) := hGi.const_mul _
    set ubar : ℝ := ∫ y, u y ∂(withDensityReal ρ) with hubar
    have hub : -(β * Cg) ≤ ubar := by
      have e : ubar = -(t * (β / N)) * convMeasure (gPlus d s c) (withDensityReal ρ) x := by
        simp only [hubar, hu]; rw [integral_const_mul]; rfl
      rw [e]
      have h1 := (hCg x).2
      have h2 := (hCg x).1
      nlinarith [mul_le_mul_of_nonneg_left h1 htl, mul_le_mul_of_nonneg_right htl1 h2]
    have hi1 : Integrable (fun y => u y - ubar) (withDensityReal ρ) := hui.sub (integrable_const _)
    have hi2 : Integrable (fun y => 1 + (u y - ubar)) (withDensityReal ρ) :=
      (integrable_const (1 : ℝ)).add hi1
    have hmono : ∫ y, Real.exp ubar * (1 + (u y - ubar)) ∂(withDensityReal ρ) ≤
        ∫ y, l48_a0 d s c β N x t y ∂(withDensityReal ρ) := by
      refine integral_mono (hi2.const_mul _) ha0i fun y => ?_
      have := Real.add_one_le_exp (u y - ubar)
      calc Real.exp ubar * (1 + (u y - ubar)) ≤ Real.exp ubar * Real.exp (u y - ubar) :=
            mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
        _ = l48_a0 d s c β N x t y := by
            unfold l48_a0; rw [← Real.exp_add]; congr 1; simp only [hu]; ring
    have hval : ∫ y, Real.exp ubar * (1 + (u y - ubar)) ∂(withDensityReal ρ) = Real.exp ubar := by
      rw [integral_const_mul, integral_add (integrable_const (1 : ℝ)) hi1,
        integral_sub hui (integrable_const _)]
      simp [hubar]
    unfold l48_B
    rw [hval] at hmono
    exact (Real.exp_le_exp.2 hub).trans hmono
  · unfold l48_B
    calc ∫ y, l48_a0 d s c β N x t y ∂(withDensityReal ρ) ≤ ∫ _y, (1 : ℝ) ∂(withDensityReal ρ) :=
          integral_mono ha0i (integrable_const _) fun y => l48_a0_le_one hd hcrit hβ hρ hc hN x ht y
      _ = 1 := by simp
  · exact integral_nonneg fun y =>
      mul_nonneg (show 0 ≤ gPlus d s c (x - y) from hc _) (l48_a0_pos hd hcrit hβ hρ hc N x t y).le
  · unfold l48_F
    calc ∫ y, gPlus d s c (x - y) * l48_a0 d s c β N x t y ∂(withDensityReal ρ)
        ≤ ∫ y, gPlus d s c (x - y) ∂(withDensityReal ρ) :=
          integral_mono hFi hGi fun y => by
            have hG0 : 0 ≤ gPlus d s c (x - y) := hc _
            calc gPlus d s c (x - y) * l48_a0 d s c β N x t y ≤ gPlus d s c (x - y) * 1 :=
                  mul_le_mul_of_nonneg_left (l48_a0_le_one hd hcrit hβ hρ hc hN x ht y) hG0
              _ = _ := mul_one _
      _ = convMeasure (gPlus d s c) (withDensityReal ρ) x := rfl
      _ ≤ Cg := (hCg x).2

theorem l48_int_a0 {N : ℕ} (hN : 2 ≤ N) (x : Torus d) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    Integrable (l48_a0 d s c β N x t) (withDensityReal ρ) := by
  have hμ := isProbabilityMeasure_mu hρ
  exact Integrable.mono' (integrable_const (1 : ℝ))
    (l48_meas_a0 hd hcrit hβ hρ hc (β := β) N x t).aestronglyMeasurable
    (Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_pos (l48_a0_pos hd hcrit hβ hρ hc N x t y)]
      exact l48_a0_le_one hd hcrit hβ hρ hc hN x ht y)

theorem l48_int_f1 {N : ℕ} (hN : 2 ≤ N) (x : Torus d) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    Integrable (fun y => gPlus d s c (x - y) * l48_a0 d s c β N x t y) (withDensityReal ρ) := by
  obtain ⟨hs0, hsd⟩ := hs_aux hd hcrit
  have hgm := measurable_gPlus hd hs0 hsd c
  have hGi := gPlus_int hd hcrit hβ hρ hc hs0 hsd x
  refine Integrable.mono' hGi
    ((hgm.comp (measurable_const.sub measurable_id)).mul
      (l48_meas_a0 hd hcrit hβ hρ hc (β := β) N x t)).aestronglyMeasurable
    (Eventually.of_forall fun y => ?_)
  have hG0 : 0 ≤ gPlus d s c (x - y) := hc _
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hG0 (l48_a0_pos hd hcrit hβ hρ hc N x t y).le)]
  calc gPlus d s c (x - y) * l48_a0 d s c β N x t y ≤ gPlus d s c (x - y) * 1 :=
        mul_le_mul_of_nonneg_left (l48_a0_le_one hd hcrit hβ hρ hc hN x ht y) hG0
    _ = gPlus d s c (x - y) := mul_one _

set_option maxHeartbeats 1600000 in
/-- The exact quotient identity (TeX `R:eq:quotient-identity`) in inequality form. -/
theorem l48_quotient {Cg : ℝ} (hCg : ∀ y, 0 ≤ convMeasure (gPlus d s c) (withDensityReal ρ) y ∧
      convMeasure (gPlus d s c) (withDensityReal ρ) y ≤ Cg)
    {N : ℕ} (hN : 2 ≤ N) (x : Torus d) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (i : Fin (N - 1))
    (Y : Config d (N - 1))
    (h0 : ∫⁻ y, ENNReal.ofReal (l48_a0 d s c β N x t y * taylorH (cavityField d s c β ρ N i Y y))
      ∂(withDensityReal ρ) < ⊤)
    (h1 : ∫⁻ y, ENNReal.ofReal ((gPlus d s c (x - y) * l48_a0 d s c β N x t y) *
      taylorH (cavityField d s c β ρ N i Y y)) ∂(withDensityReal ρ) < ⊤) :
    |l48_T d s c β ρ N x t i Y - l48_F d s c β ρ N x t / l48_B d s c β ρ N x t| ≤
      (|∫ y, l48_psi d s c β ρ N x t y * cavityField d s c β ρ N i Y y ∂(withDensityReal ρ)| +
        l48_F d s c β ρ N x t *
          (∫⁻ y, ENNReal.ofReal (l48_a0 d s c β N x t y * taylorH (cavityField d s c β ρ N i Y y))
            ∂(withDensityReal ρ)).toReal +
        l48_B d s c β ρ N x t *
          (∫⁻ y, ENNReal.ofReal ((gPlus d s c (x - y) * l48_a0 d s c β N x t y) *
            taylorH (cavityField d s c β ρ N i Y y)) ∂(withDensityReal ρ)).toReal) /
        (l48_B d s c β ρ N x t * Real.exp (-(3 * (β * Cg)))) := by
  obtain ⟨hs0, hsd⟩ := hs_aux hd hcrit
  have hμ := isProbabilityMeasure_mu hρ
  have hgm := measurable_gPlus hd hs0 hsd c
  obtain ⟨hB1, hB2, hF1, hF2⟩ := l48_BF_bounds hd hcrit hβ hρ hc hCg hN x ht
  obtain ⟨hZ1, hZ2, hN1, hN2⟩ := l48_bounds hd hcrit hβ hρ hc hCg hN x ht i Y
  have hBpos : 0 < l48_B d s c β ρ N x t := lt_of_lt_of_le (Real.exp_pos _) hB1
  have hZpos : 0 < l48_Z d s c β ρ N x t i Y := lt_of_lt_of_le (Real.exp_pos _) hZ1
  have hvm : Measurable (cavityField d s c β ρ N i Y) := measurable_field_slice hd hcrit hβ hρ hc N i Y
  have hup : ∀ y, -cavityField d s c β ρ N i Y y ≤ β * Cg := fun y =>
    neg_field_le hd hcrit hβ hρ hc hCg hN i Y y
  have hHm : Measurable fun y => taylorH (cavityField d s c β ρ N i Y y) := by
    unfold taylorH
    exact ((Real.measurable_exp.comp hvm.neg).sub measurable_const).add hvm
  have hH0 : ∀ y, 0 ≤ taylorH (cavityField d s c β ρ N i Y y) := fun y => by
    unfold taylorH
    have := Real.add_one_le_exp (-cavityField d s c β ρ N i Y y)
    linarith
  have hem : Measurable fun y => Real.exp (-cavityField d s c β ρ N i Y y) :=
    Real.measurable_exp.comp hvm.neg
  have he_pos : ∀ y, 0 < Real.exp (-cavityField d s c β ρ N i Y y) := fun y => Real.exp_pos _
  have he_le : ∀ y, Real.exp (-cavityField d s c β ρ N i Y y) ≤ Real.exp (β * Cg) := fun y =>
    Real.exp_le_exp.2 (hup y)
  have ha0m := l48_meas_a0 hd hcrit hβ hρ hc (β := β) N x t
  have hGm : Measurable fun y => gPlus d s c (x - y) := hgm.comp (measurable_const.sub measurable_id)
  have hf0i := l48_int_a0 hd hcrit hβ hρ hc hN x ht
  have hf1i := l48_int_f1 hd hcrit hβ hρ hc hN x ht
  have ha0p := l48_a0_pos hd hcrit hβ hρ hc (β := β) N x t
  have hG0 : ∀ y, 0 ≤ gPlus d s c (x - y) := fun y => hc _
  set B := l48_B d s c β ρ N x t with hBdef
  set F := l48_F d s c β ρ N x t with hFdef
  set a0 := l48_a0 d s c β N x t with ha0def
  set v := cavityField d s c β ρ N i Y with hvdef
  set ψ := l48_psi d s c β ρ N x t with hψdef
  have hψy : ∀ y, ψ y = F * a0 y - B * (gPlus d s c (x - y) * a0 y) := fun y => rfl
  have hψm : Measurable ψ := by
    have : ψ = fun y => F * a0 y - B * (gPlus d s c (x - y) * a0 y) := funext hψy
    rw [this]
    exact (ha0m.const_mul _).sub ((hGm.mul ha0m).const_mul _)
  have hψi : Integrable ψ (withDensityReal ρ) := by
    have : ψ = fun y => F * a0 y - B * (gPlus d s c (x - y) * a0 y) := funext hψy
    rw [this]
    exact (hf0i.const_mul _).sub (hf1i.const_mul _)
  have hψ0 : ∫ y, ψ y ∂(withDensityReal ρ) = 0 := by
    have : ψ = fun y => F * a0 y - B * (gPlus d s c (x - y) * a0 y) := funext hψy
    rw [this, integral_sub (hf0i.const_mul _) (hf1i.const_mul _), integral_const_mul,
      integral_const_mul]
    have e1 : ∫ y, a0 y ∂(withDensityReal ρ) = B := rfl
    have e2 : ∫ y, gPlus d s c (x - y) * a0 y ∂(withDensityReal ρ) = F := rfl
    rw [e1, e2]; ring
  have hψabs : ∀ y, |ψ y| ≤ F * a0 y + B * (gPlus d s c (x - y) * a0 y) := fun y => by
    rw [hψy]
    have h1 : 0 ≤ F * a0 y := mul_nonneg hF1 (ha0p y).le
    have h2 : 0 ≤ B * (gPlus d s c (x - y) * a0 y) := mul_nonneg hBpos.le (mul_nonneg (hG0 y) (ha0p y).le)
    rw [abs_le]; constructor <;> linarith
  -- finiteness of the remainders
  obtain ⟨hr0i, hr0e⟩ := l48_int_of_lint (μ := withDensityReal ρ)
    (f := fun y => a0 y * taylorH (v y)) (ha0m.mul hHm)
    (fun y => mul_nonneg (ha0p y).le (hH0 y)) h0
  obtain ⟨hr1i, hr1e⟩ := l48_int_of_lint (μ := withDensityReal ρ)
    (f := fun y => (gPlus d s c (x - y) * a0 y) * taylorH (v y)) ((hGm.mul ha0m).mul hHm)
    (fun y => mul_nonneg (mul_nonneg (hG0 y) (ha0p y).le) (hH0 y)) h1
  set R0 : ℝ := (∫⁻ y, ENNReal.ofReal (a0 y * taylorH (v y)) ∂(withDensityReal ρ)).toReal with hR0
  set R1 : ℝ := (∫⁻ y, ENNReal.ofReal ((gPlus d s c (x - y) * a0 y) * taylorH (v y))
    ∂(withDensityReal ρ)).toReal with hR1
  have hψHi : Integrable (fun y => ψ y * taylorH (v y)) (withDensityReal ρ) := by
    refine Integrable.mono' ((hr0i.const_mul F).add (hr1i.const_mul B))
      (hψm.mul hHm).aestronglyMeasurable (Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hH0 y)]
    calc |ψ y| * taylorH (v y) ≤ (F * a0 y + B * (gPlus d s c (x - y) * a0 y)) * taylorH (v y) :=
          mul_le_mul_of_nonneg_right (hψabs y) (hH0 y)
      _ = F * (a0 y * taylorH (v y)) + B * ((gPlus d s c (x - y) * a0 y) * taylorH (v y)) := by ring
  have hψei : Integrable (fun y => ψ y * Real.exp (-v y)) (withDensityReal ρ) := by
    refine Integrable.mono' (hψi.abs.mul_const (Real.exp (β * Cg)))
      (hψm.mul hem).aestronglyMeasurable (Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (he_pos y)]
    exact mul_le_mul_of_nonneg_left (he_le y) (abs_nonneg _)
  have hψvi : Integrable (fun y => ψ y * v y) (withDensityReal ρ) := by
    have := (hψHi.add hψi).sub hψei
    refine this.congr (Eventually.of_forall fun y => ?_)
    simp only [Pi.sub_apply, Pi.add_apply, taylorH]
    ring
  -- `∫ ψ e = ∫ ψ H - ℓ`
  have hψe : ∫ y, ψ y * Real.exp (-v y) ∂(withDensityReal ρ) =
      ∫ y, ψ y * taylorH (v y) ∂(withDensityReal ρ) - ∫ y, ψ y * v y ∂(withDensityReal ρ) := by
    have e : ∀ y, ψ y * Real.exp (-v y) = ψ y * taylorH (v y) + ψ y - ψ y * v y := fun y => by
      simp only [taylorH]; ring
    simp_rw [e]
    have hpa : Integrable (fun y => ψ y * taylorH (v y) + ψ y) (withDensityReal ρ) := hψHi.add hψi
    rw [integral_sub hpa hψvi, integral_add hψHi hψi, hψ0]
    ring
  -- the numerator and denominator
  have hexA : ∀ y, Real.exp (l48_A d s c β ρ N x t i Y y) = a0 y * Real.exp (-v y) := fun y => by
    unfold l48_A
    rw [sub_eq_add_neg, Real.exp_add]
    rfl
  have hZ : l48_Z d s c β ρ N x t i Y = ∫ y, a0 y * Real.exp (-v y) ∂(withDensityReal ρ) := by
    unfold l48_Z
    exact integral_congr_ae (Eventually.of_forall hexA)
  have hNn : l48_Nn d s c β ρ N x t i Y =
      ∫ y, (gPlus d s c (x - y) * a0 y) * Real.exp (-v y) ∂(withDensityReal ρ) := by
    unfold l48_Nn
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    show gPlus d s c (x - y) * Real.exp (l48_A d s c β ρ N x t i Y y) =
      (gPlus d s c (x - y) * a0 y) * Real.exp (-v y)
    rw [hexA, mul_assoc]
  have hi_a0e : Integrable (fun y => a0 y * Real.exp (-v y)) (withDensityReal ρ) := by
    refine Integrable.mono' (hf0i.mul_const (Real.exp (β * Cg))) (ha0m.mul hem).aestronglyMeasurable
      (Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (ha0p y).le (he_pos y).le)]
    exact mul_le_mul_of_nonneg_left (he_le y) (ha0p y).le |>.trans_eq (by ring) |>.trans_eq' (by ring)
  have hi_f1e : Integrable (fun y => (gPlus d s c (x - y) * a0 y) * Real.exp (-v y))
      (withDensityReal ρ) := by
    refine Integrable.mono' (hf1i.mul_const (Real.exp (β * Cg))) ((hGm.mul ha0m).mul hem).aestronglyMeasurable
      (Eventually.of_forall fun y => ?_)
    have h2 : 0 ≤ gPlus d s c (x - y) * a0 y := mul_nonneg (hG0 y) (ha0p y).le
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h2 (he_pos y).le)]
    exact mul_le_mul_of_nonneg_left (he_le y) h2
  -- `B N - F Z = ℓ - ∫ ψ H`
  have hkey : B * l48_Nn d s c β ρ N x t i Y - F * l48_Z d s c β ρ N x t i Y =
      (∫ y, ψ y * v y ∂(withDensityReal ρ)) - ∫ y, ψ y * taylorH (v y) ∂(withDensityReal ρ) := by
    rw [hNn, hZ, ← integral_const_mul, ← integral_const_mul,
      ← integral_sub (hi_f1e.const_mul B) (hi_a0e.const_mul F)]
    have e : ∀ y, B * ((gPlus d s c (x - y) * a0 y) * Real.exp (-v y)) - F * (a0 y * Real.exp (-v y)) =
        -(ψ y * Real.exp (-v y)) := fun y => by rw [hψy]; ring
    simp_rw [e]
    rw [integral_neg, hψe]
    ring
  -- bound on `∫ ψ H`
  have hψH : |∫ y, ψ y * taylorH (v y) ∂(withDensityReal ρ)| ≤ F * R0 + B * R1 := by
    refine (abs_integral_le_integral_abs).trans ?_
    have hle : ∫ y, |ψ y * taylorH (v y)| ∂(withDensityReal ρ) ≤
        ∫ y, (F * (a0 y * taylorH (v y)) + B * ((gPlus d s c (x - y) * a0 y) * taylorH (v y)))
          ∂(withDensityReal ρ) := by
      refine integral_mono hψHi.abs ((hr0i.const_mul F).add (hr1i.const_mul B)) fun y => ?_
      show |ψ y * taylorH (v y)| ≤ F * (a0 y * taylorH (v y)) +
        B * ((gPlus d s c (x - y) * a0 y) * taylorH (v y))
      rw [abs_mul, abs_of_nonneg (hH0 y)]
      calc |ψ y| * taylorH (v y) ≤ (F * a0 y + B * (gPlus d s c (x - y) * a0 y)) * taylorH (v y) :=
            mul_le_mul_of_nonneg_right (hψabs y) (hH0 y)
        _ = _ := by ring
    refine hle.trans (le_of_eq ?_)
    rw [integral_add (hr0i.const_mul F) (hr1i.const_mul B), integral_const_mul, integral_const_mul,
      hr0e, hr1e]
  -- the quotient
  have hZne : l48_Z d s c β ρ N x t i Y ≠ 0 := hZpos.ne'
  have hBne : B ≠ 0 := hBpos.ne'
  have hq : l48_T d s c β ρ N x t i Y - F / B =
      (B * l48_Nn d s c β ρ N x t i Y - F * l48_Z d s c β ρ N x t i Y) /
        (B * l48_Z d s c β ρ N x t i Y) := by
    unfold l48_T
    field_simp
  rw [hq, abs_div, abs_of_pos (mul_pos hBpos hZpos), hkey]
  have hnum : |(∫ y, ψ y * v y ∂(withDensityReal ρ)) - ∫ y, ψ y * taylorH (v y) ∂(withDensityReal ρ)| ≤
      |∫ y, ψ y * v y ∂(withDensityReal ρ)| + F * R0 + B * R1 := by
    calc _ ≤ |∫ y, ψ y * v y ∂(withDensityReal ρ)| + |∫ y, ψ y * taylorH (v y) ∂(withDensityReal ρ)| :=
          abs_sub _ _
      _ ≤ _ := by linarith
  have hnn : 0 ≤ |∫ y, ψ y * v y ∂(withDensityReal ρ)| + F * R0 + B * R1 := by
    have h0' : 0 ≤ R0 := ENNReal.toReal_nonneg
    have h1' : 0 ≤ R1 := ENNReal.toReal_nonneg
    positivity
  refine (div_le_div_of_nonneg_right hnum (mul_pos hBpos hZpos).le).trans ?_
  exact div_le_div_of_nonneg_left hnn (mul_pos hBpos (Real.exp_pos _)) (mul_le_mul_of_nonneg_left hZ1 hBpos.le)

end Quot

end L48

end HRS

end
