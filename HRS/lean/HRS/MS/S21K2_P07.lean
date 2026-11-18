import HRS.MS.S21K2_P07D

/-!
# S21K2 P07 -- finite Gaussian heat equation for an integrable covariance density (R26-T3.P07)

Contract `r26t3_finite_heat_equation` verbatim (qualified names).  Route (no heat-kernel PDE): the Gaussian laws of `Gamma r` are
`gam (Sm r)`, `Sm s = Sm t + D` with `D = ∫_s^t A` PSD, so `law(Gamma s) = law(Gamma t) * gam D` (characteristic functions) and a
third-order Taylor estimate gives the one-step formula
`|u(s) - u(t) - 1/2 sum D_ij d_ij u(t)| <= C (tr D)^(3/2)`, `|d_ij u(s) - d_ij u(t)| <= C (tr D)^(1/2)` (file `P07C`);
the local defect is `sqrt(tr D) * (additive mass)`, so an additive-defect lemma (file `P07D`) gives the integrated equation.
Helper prefix `s21k2_p07_`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Filter Topology Set Matrix
open scoped ENNReal NNReal BigOperators
noncomputable section
namespace HRS.MS.R26T3

section Main
variable {n : ℕ} {H : ℝ} {A : ℝ → Matrix (Fin n) (Fin n) ℝ}

/-- `Fc r = ∫_0^r tr A` -/
def s21k2_p07_Fc (A : ℝ → Matrix (Fin n) (Fin n) ℝ) (r : ℝ) : ℝ := ∫ x in (0 : ℝ)..r, ∑ i, A x i i

theorem s21k2_p07_hh_lip {Φ : HRS.Euc n → ℝ} (hΦ : ContDiff ℝ 3 Φ) {B2 C K1 : ℝ}
    (hB2 : ∀ z, ‖iteratedFDeriv ℝ 2 Φ z‖ ≤ B2) (hC : ∀ z, ‖iteratedFDeriv ℝ 3 Φ z‖ ≤ C) (hC0 : 0 ≤ C)
    (hK1 : ∀ D : Matrix (Fin n) (Fin n) ℝ, D.PosSemidef →
      ∫ w, ‖w‖ ∂(s21k2_p07_gam D) ≤ K1 * Real.sqrt D.trace)
    (hA : ∀ i j, IntegrableOn (fun v => A v i j) (Icc 0 H))
    (hpos : ∀ᵐ v ∂volume.restrict (Icc 0 H), Matrix.PosSemidef (A v)) (y : HRS.Euc n) {r b : ℝ}
    (hr : 0 ≤ r) (hrb : r ≤ b) (hb : b ≤ H) (hSb : (s21k2_p07_Sm A H b).PosSemidef) (i j : Fin n) :
    |s21k2_p07_hh Φ y (s21k2_p07_Sm A H r) i j - s21k2_p07_hh Φ y (s21k2_p07_Sm A H b) i j| ≤
      C * (K1 * Real.sqrt (s21k2_p07_Fc A b - s21k2_p07_Fc A r)) := by
  have hD := s21k2_p07_D_psd hA hpos hr hrb hb
  have e : s21k2_p07_Sm A H b + (s21k2_p07_Sm A H r - s21k2_p07_Sm A H b) = s21k2_p07_Sm A H r := by abel
  have h := s21k2_p07_step_hh hΦ hB2 hC hSb hD y i j
  rw [e] at h
  refine h.trans (mul_le_mul_of_nonneg_left ?_ hC0)
  have := hK1 _ hD
  rwa [s21k2_p07_trace_sub hA hr hrb hb] at this

theorem s21k2_p07_U_step {Φ : HRS.Euc n → ℝ} (hΦ : ContDiff ℝ 3 Φ) {B0 B2 C K3 : ℝ}
    (hB0 : ∀ z, ‖Φ z‖ ≤ B0) (hB2 : ∀ z, ‖iteratedFDeriv ℝ 2 Φ z‖ ≤ B2)
    (hC : ∀ z, ‖iteratedFDeriv ℝ 3 Φ z‖ ≤ C) (hC0 : 0 ≤ C)
    (hK3 : ∀ D : Matrix (Fin n) (Fin n) ℝ, D.PosSemidef →
      ∫ w, ‖w‖ ^ 3 ∂(s21k2_p07_gam D) ≤ K3 * Real.sqrt D.trace ^ 3)
    (hA : ∀ i j, IntegrableOn (fun v => A v i j) (Icc 0 H))
    (hpos : ∀ᵐ v ∂volume.restrict (Icc 0 H), Matrix.PosSemidef (A v)) (y : HRS.Euc n) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ H) (hSb : (s21k2_p07_Sm A H b).PosSemidef) :
    |s21k2_p07_U Φ y (s21k2_p07_Sm A H a) - s21k2_p07_U Φ y (s21k2_p07_Sm A H b) -
      (1 / 2) * ∑ i, ∑ j, (∫ r in a..b, A r i j) * s21k2_p07_hh Φ y (s21k2_p07_Sm A H b) i j| ≤
      C * (K3 * Real.sqrt (s21k2_p07_Fc A b - s21k2_p07_Fc A a) ^ 3) := by
  have hD := s21k2_p07_D_psd hA hpos ha hab hb
  have e : s21k2_p07_Sm A H b + (s21k2_p07_Sm A H a - s21k2_p07_Sm A H b) = s21k2_p07_Sm A H a := by abel
  have h := s21k2_p07_step_U hΦ hB0 hB2 hC hSb hD y
  rw [e] at h
  have hsum : ∑ i, ∑ j, (s21k2_p07_Sm A H a - s21k2_p07_Sm A H b) i j * s21k2_p07_hh Φ y (s21k2_p07_Sm A H b) i j =
      ∑ i, ∑ j, (∫ r in a..b, A r i j) * s21k2_p07_hh Φ y (s21k2_p07_Sm A H b) i j :=
    Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
      rw [s21k2_p07_Sm_sub hA ha hab hb]
  have hK := hK3 _ hD
  rw [s21k2_p07_trace_sub hA ha hab hb] at hK
  rw [hsum] at h
  have : s21k2_p07_Sm A H b + (s21k2_p07_Sm A H a - s21k2_p07_Sm A H b) = s21k2_p07_Sm A H a := e
  refine h.trans (mul_le_mul_of_nonneg_left hK hC0)


theorem s21k2_p07_Fc_mono (hA : ∀ i j, IntegrableOn (fun v => A v i j) (Icc 0 H))
    (hpos : ∀ᵐ v ∂volume.restrict (Icc 0 H), Matrix.PosSemidef (A v)) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) (hb : b ≤ H) : 0 ≤ s21k2_p07_Fc A b - s21k2_p07_Fc A a := by
  have h1 := s21k2_p07_trace_sub hA ha hab hb
  have h2 := (s21k2_p07_D_psd hA hpos ha hab hb).trace_nonneg
  unfold s21k2_p07_Fc
  linarith

theorem s21k2_p07_Fc_cont (hA : ∀ i j, IntegrableOn (fun v => A v i j) (Icc 0 H)) (hH0 : 0 ≤ H) :
    ContinuousOn (s21k2_p07_Fc A) (Icc 0 H) := by
  have hτ : IntegrableOn (fun x => ∑ i, A x i i) (uIcc 0 H) := by
    rw [uIcc_of_le hH0]
    exact integrable_finsetSum _ fun i _ => hA i i
  have := intervalIntegral.continuousOn_primitive_interval (a := 0) (b := H) hτ
  rwa [uIcc_of_le hH0] at this

theorem s21k2_p07_hh_cont {Φ : HRS.Euc n → ℝ} (hΦ : ContDiff ℝ 3 Φ) {B2 C K1 : ℝ}
    (hB2 : ∀ z, ‖iteratedFDeriv ℝ 2 Φ z‖ ≤ B2) (hC : ∀ z, ‖iteratedFDeriv ℝ 3 Φ z‖ ≤ C) (hC0 : 0 ≤ C)
    (hK10 : 0 ≤ K1)
    (hK1 : ∀ D : Matrix (Fin n) (Fin n) ℝ, D.PosSemidef →
      ∫ w, ‖w‖ ∂(s21k2_p07_gam D) ≤ K1 * Real.sqrt D.trace)
    (hA : ∀ i j, IntegrableOn (fun v => A v i j) (Icc 0 H))
    (hpos : ∀ᵐ v ∂volume.restrict (Icc 0 H), Matrix.PosSemidef (A v)) (y : HRS.Euc n) (hH0 : 0 ≤ H)
    (hSpsd : ∀ r ∈ Icc 0 H, (s21k2_p07_Sm A H r).PosSemidef) (i j : Fin n) :
    ContinuousOn (fun r => s21k2_p07_hh Φ y (s21k2_p07_Sm A H r) i j) (Icc 0 H) := by
  have hlip : ∀ a ∈ Icc (0 : ℝ) H, ∀ b ∈ Icc (0 : ℝ) H,
      |s21k2_p07_hh Φ y (s21k2_p07_Sm A H a) i j - s21k2_p07_hh Φ y (s21k2_p07_Sm A H b) i j| ≤
        C * (K1 * Real.sqrt |s21k2_p07_Fc A a - s21k2_p07_Fc A b|) := fun a ha b hb => by
    rcases le_total a b with hab | hab
    · have := s21k2_p07_hh_lip hΦ hB2 hC hC0 hK1 hA hpos y ha.1 hab hb.2 (hSpsd b hb) i j
      rwa [abs_of_nonpos (by linarith [s21k2_p07_Fc_mono hA hpos ha.1 hab hb.2] : s21k2_p07_Fc A a - s21k2_p07_Fc A b ≤ 0),
        neg_sub] 
    · have := s21k2_p07_hh_lip hΦ hB2 hC hC0 hK1 hA hpos y hb.1 hab ha.2 (hSpsd a ha) i j
      rwa [abs_sub_comm, abs_of_nonneg (by linarith [s21k2_p07_Fc_mono hA hpos hb.1 hab ha.2] : 0 ≤ s21k2_p07_Fc A a - s21k2_p07_Fc A b)]
  have hFc := s21k2_p07_Fc_cont hA hH0
  intro b hb
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  set M : ℝ := C * K1 with hM
  have hM0 : 0 ≤ M := mul_nonneg hC0 hK10
  have hρ : 0 < (ε / (M + 1)) ^ 2 := by positivity
  obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousWithinAt_iff.1 (hFc b hb) _ hρ
  refine ⟨δ, hδ, fun a ha hab => ?_⟩
  have h1 := hlip a ha b hb
  have h2 := hδ' ha hab
  rw [Real.dist_eq] at h2 ⊢
  have h3 : Real.sqrt |s21k2_p07_Fc A a - s21k2_p07_Fc A b| < ε / (M + 1) := by
    rw [← Real.sqrt_sq (by positivity : 0 ≤ ε / (M + 1))]
    exact Real.sqrt_lt_sqrt (abs_nonneg _) h2
  calc _ ≤ C * (K1 * Real.sqrt |s21k2_p07_Fc A a - s21k2_p07_Fc A b|) := h1
    _ = M * Real.sqrt |s21k2_p07_Fc A a - s21k2_p07_Fc A b| := by rw [hM]; ring
    _ ≤ M * (ε / (M + 1)) := mul_le_mul_of_nonneg_left h3.le hM0
    _ < ε := by
        rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith


theorem s21k2_p07_ii_sum {ι : Type*} (s : Finset ι) {f : ι → ℝ → ℝ} {a b : ℝ}
    (h : ∀ i ∈ s, IntervalIntegrable (f i) volume a b) :
    IntervalIntegrable (fun r => ∑ i ∈ s, f i r) volume a b := by
  have := IntervalIntegrable.sum (μ := volume) s h
  convert this using 1
  ext r; simp [Finset.sum_apply]

theorem s21k2_p07_local {Φ : HRS.Euc n → ℝ} (hΦ : ContDiff ℝ 3 Φ) {B0 B2 C K1 K3 : ℝ}
    (hB0 : ∀ z, ‖Φ z‖ ≤ B0) (hB2 : ∀ z, ‖iteratedFDeriv ℝ 2 Φ z‖ ≤ B2)
    (hC : ∀ z, ‖iteratedFDeriv ℝ 3 Φ z‖ ≤ C) (hC0 : 0 ≤ C) (hK10 : 0 ≤ K1)
    (hK1 : ∀ D : Matrix (Fin n) (Fin n) ℝ, D.PosSemidef →
      ∫ w, ‖w‖ ∂(s21k2_p07_gam D) ≤ K1 * Real.sqrt D.trace)
    (hK3 : ∀ D : Matrix (Fin n) (Fin n) ℝ, D.PosSemidef →
      ∫ w, ‖w‖ ^ 3 ∂(s21k2_p07_gam D) ≤ K3 * Real.sqrt D.trace ^ 3)
    (hA : ∀ i j, IntegrableOn (fun v => A v i j) (Icc 0 H))
    (hpos : ∀ᵐ v ∂volume.restrict (Icc 0 H), Matrix.PosSemidef (A v)) (y : HRS.Euc n)
    (hSpsd : ∀ r ∈ Icc 0 H, (s21k2_p07_Sm A H r).PosSemidef)
    (hAh : ∀ i j, IntegrableOn (fun r => A r i j * s21k2_p07_hh Φ y (s21k2_p07_Sm A H r) i j) (Icc 0 H))
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ H) :
    |(s21k2_p07_U Φ y (s21k2_p07_Sm A H b) - s21k2_p07_U Φ y (s21k2_p07_Sm A H a)) +
      (1 / 2) * ∫ r in a..b, ∑ i, ∑ j, A r i j * s21k2_p07_hh Φ y (s21k2_p07_Sm A H r) i j| ≤
      Real.sqrt (s21k2_p07_Fc A b - s21k2_p07_Fc A a) *
        ((C * K1 / 2) * (∑ i, ∑ j, ∫ r in a..b, |A r i j|) +
          C * K3 * (s21k2_p07_Fc A b - s21k2_p07_Fc A a)) := by
  have hSb : (s21k2_p07_Sm A H b).PosSemidef := hSpsd b ⟨ha.trans hab, hb⟩
  set τ := s21k2_p07_Fc A b - s21k2_p07_Fc A a with hτdef
  have hτ : 0 ≤ τ := s21k2_p07_Fc_mono hA hpos ha hab hb
  have hint : ∀ i j, IntervalIntegrable (fun r => A r i j) volume a b := fun i j =>
    s21k2_p07_intIcc (hA i j) ha hab hb
  have hAhi : ∀ i j, IntervalIntegrable
      (fun r => A r i j * s21k2_p07_hh Φ y (s21k2_p07_Sm A H r) i j) volume a b := fun i j =>
    s21k2_p07_intIcc (hAh i j) ha hab hb
  have hU := s21k2_p07_U_step hΦ hB0 hB2 hC hC0 hK3 hA hpos y ha hab hb hSb
  have hdiff : ∀ i j, |(∫ r in a..b, A r i j * s21k2_p07_hh Φ y (s21k2_p07_Sm A H r) i j) -
      (∫ r in a..b, A r i j) * s21k2_p07_hh Φ y (s21k2_p07_Sm A H b) i j| ≤
      C * K1 * Real.sqrt τ * ∫ r in a..b, |A r i j| := fun i j => by
    have e : (∫ r in a..b, A r i j * s21k2_p07_hh Φ y (s21k2_p07_Sm A H r) i j) -
        (∫ r in a..b, A r i j) * s21k2_p07_hh Φ y (s21k2_p07_Sm A H b) i j =
        ∫ r in a..b, A r i j * (s21k2_p07_hh Φ y (s21k2_p07_Sm A H r) i j -
          s21k2_p07_hh Φ y (s21k2_p07_Sm A H b) i j) := by
      rw [← intervalIntegral.integral_mul_const,
        ← intervalIntegral.integral_sub (hAhi i j) ((hint i j).mul_const _)]
      congr 1; ext r; ring
    rw [e, ← Real.norm_eq_abs]
    have hbd : IntervalIntegrable (fun r => C * K1 * Real.sqrt τ * |A r i j|) volume a b :=
      ((hint i j).abs).const_mul _
    refine (intervalIntegral.norm_integral_le_of_norm_le hab (Eventually.of_forall fun r hr => ?_) hbd).trans ?_
    · rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      have h1 := s21k2_p07_hh_lip hΦ hB2 hC hC0 hK1 hA hpos y (ha.trans hr.1.le) hr.2 hb hSb i j
      have h2 : Real.sqrt (s21k2_p07_Fc A b - s21k2_p07_Fc A r) ≤ Real.sqrt τ :=
        Real.sqrt_le_sqrt (by linarith [s21k2_p07_Fc_mono hA hpos ha hr.1.le (hr.2.trans hb)])
      calc |A r i j| * |s21k2_p07_hh Φ y (s21k2_p07_Sm A H r) i j - s21k2_p07_hh Φ y (s21k2_p07_Sm A H b) i j|
          ≤ |A r i j| * (C * (K1 * Real.sqrt τ)) := by
            refine mul_le_mul_of_nonneg_left (h1.trans ?_) (abs_nonneg _)
            exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hK10) hC0
        _ = _ := by ring
    · rw [intervalIntegral.integral_const_mul]
  have hsplit : ∫ r in a..b, ∑ i, ∑ j, A r i j * s21k2_p07_hh Φ y (s21k2_p07_Sm A H r) i j =
      ∑ i, ∑ j, ∫ r in a..b, A r i j * s21k2_p07_hh Φ y (s21k2_p07_Sm A H r) i j := by
    rw [intervalIntegral.integral_finsetSum fun i _ => s21k2_p07_ii_sum _ fun j _ => hAhi i j]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact intervalIntegral.integral_finsetSum fun j _ => hAhi i j
  set X := s21k2_p07_U Φ y (s21k2_p07_Sm A H a) - s21k2_p07_U Φ y (s21k2_p07_Sm A H b) -
    (1 / 2) * ∑ i, ∑ j, (∫ r in a..b, A r i j) * s21k2_p07_hh Φ y (s21k2_p07_Sm A H b) i j with hX
  set Y : ℝ := ∑ i, ∑ j, ((∫ r in a..b, A r i j * s21k2_p07_hh Φ y (s21k2_p07_Sm A H r) i j) -
      (∫ r in a..b, A r i j) * s21k2_p07_hh Φ y (s21k2_p07_Sm A H b) i j) with hY
  have e : (s21k2_p07_U Φ y (s21k2_p07_Sm A H b) - s21k2_p07_U Φ y (s21k2_p07_Sm A H a)) +
      (1 / 2) * ∫ r in a..b, ∑ i, ∑ j, A r i j * s21k2_p07_hh Φ y (s21k2_p07_Sm A H r) i j =
      -X + (1 / 2) * Y := by
    rw [hsplit, hX, hY]
    simp only [Finset.sum_sub_distrib]
    ring
  have hYb : |Y| ≤ C * K1 * Real.sqrt τ * ∑ i, ∑ j, ∫ r in a..b, |A r i j| := by
    rw [hY, Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [Finset.mul_sum]
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => hdiff i j)
  have hsq : Real.sqrt τ ^ 2 = τ := Real.sq_sqrt hτ
  have hα : 0 ≤ ∑ i, ∑ j, ∫ r in a..b, |A r i j| :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      intervalIntegral.integral_nonneg hab fun r _ => abs_nonneg _
  rw [e]
  calc |-X + 1 / 2 * Y| ≤ |-X| + |1 / 2 * Y| := abs_add_le _ _
    _ = |X| + 1 / 2 * |Y| := by rw [abs_neg, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    _ ≤ C * (K3 * Real.sqrt τ ^ 3) + 1 / 2 * (C * K1 * Real.sqrt τ * ∑ i, ∑ j, ∫ r in a..b, |A r i j|) := by
        gcongr
    _ = _ := by
        have : Real.sqrt τ ^ 3 = Real.sqrt τ * τ := by
          calc Real.sqrt τ ^ 3 = Real.sqrt τ * Real.sqrt τ ^ 2 := by ring
            _ = _ := by rw [hsq]
        rw [this]; ring

end Main

theorem r26t3_finite_heat_equation {n : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (H : ℝ) (hH : 0 < H)
    (Γ : ℝ → Ω → HRS.Euc n) (A : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (hG : ∀ v ∈ Set.Icc 0 H, AEStronglyMeasurable (Γ v) P ∧ HRS.IsCenteredGaussian (HRS.law P (Γ v)))
    (hA : ∀ i j, IntegrableOn (fun v => A v i j) (Set.Icc 0 H))
    (hpos : ∀ᵐ v ∂volume.restrict (Set.Icc 0 H), Matrix.PosSemidef (A v))
    (hcov : ∀ v ∈ Set.Icc 0 H, ∀ i j, ∫ ω, Γ v ω i * Γ v ω j ∂P = ∫ r in Set.Icc v H, A r i j)
    (Φ : HRS.Euc n → ℝ) (hΦ : HRS.MemCb 3 Φ) :
    ∀ y s t, 0 ≤ s → s ≤ t → t ≤ H →
      r26t3_heat P (Γ t) Φ y - r26t3_heat P (Γ s) Φ y =
        -(1 / 2 : ℝ) * ∫ r in Set.Icc s t, ∑ i, ∑ j, A r i j *
          iteratedFDeriv ℝ 2 (r26t3_heat P (Γ r) Φ) y
            ![EuclideanSpace.single i 1, EuclideanSpace.single j 1] := by
  intro y s t hs hst ht
  have hH0 : 0 ≤ H := hH.le
  have hΦ3 : ContDiff ℝ 3 Φ := hΦ.1
  obtain ⟨B0, hB0⟩ : ∃ B0, ∀ z, ‖Φ z‖ ≤ B0 := by
    obtain ⟨M, hM⟩ := hΦ.2 0 (by norm_num)
    exact ⟨M, fun z => by simpa using hM ⟨z, rfl⟩⟩
  obtain ⟨B2, hB2⟩ : ∃ B2, ∀ z, ‖iteratedFDeriv ℝ 2 Φ z‖ ≤ B2 := by
    obtain ⟨M, hM⟩ := hΦ.2 2 (by norm_num)
    exact ⟨M, fun z => hM ⟨z, rfl⟩⟩
  obtain ⟨C, hC⟩ : ∃ C, ∀ z, ‖iteratedFDeriv ℝ 3 Φ z‖ ≤ C := by
    obtain ⟨M, hM⟩ := hΦ.2 3 (by norm_num)
    exact ⟨M, fun z => hM ⟨z, rfl⟩⟩
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  obtain ⟨K1, hK10, hK1'⟩ := s21k2_p07_moment n 0
  obtain ⟨K3, hK30, hK3'⟩ := s21k2_p07_moment n 2
  have hK1 : ∀ D : Matrix (Fin n) (Fin n) ℝ, D.PosSemidef →
      ∫ w, ‖w‖ ∂(s21k2_p07_gam D) ≤ K1 * Real.sqrt D.trace := fun D hD => by simpa using hK1' D hD
  have hK3 : ∀ D : Matrix (Fin n) (Fin n) ℝ, D.PosSemidef →
      ∫ w, ‖w‖ ^ 3 ∂(s21k2_p07_gam D) ≤ K3 * Real.sqrt D.trace ^ 3 := fun D hD => hK3' D hD
  have hlaw : ∀ r ∈ Icc (0 : ℝ) H, (s21k2_p07_Sm A H r).PosSemidef ∧
      HRS.law P (Γ r) = s21k2_p07_gam (s21k2_p07_Sm A H r) := fun r hr =>
    s21k2_p07_law_eq (hG r hr) (fun i j => hcov r hr i j)
  have hSpsd : ∀ r ∈ Icc (0 : ℝ) H, (s21k2_p07_Sm A H r).PosSemidef := fun r hr => (hlaw r hr).1
  have hheat : ∀ r ∈ Icc (0 : ℝ) H, r26t3_heat P (Γ r) Φ y = s21k2_p07_U Φ y (s21k2_p07_Sm A H r) :=
    fun r hr => by
      rw [s21k2_p07_heat_U P (hG r hr).1 hΦ3.continuous y, (hlaw r hr).2]; rfl
  have hder : ∀ r ∈ Icc (0 : ℝ) H, ∀ i j, iteratedFDeriv ℝ 2 (r26t3_heat P (Γ r) Φ) y
      ![EuclideanSpace.single i 1, EuclideanSpace.single j 1] =
      s21k2_p07_hh Φ y (s21k2_p07_Sm A H r) i j := fun r hr i j => by
    rw [s21k2_p07_heat_hh P (hG r hr).1 hΦ y i j, (hlaw r hr).2]; rfl
  have hhcont := fun i j => s21k2_p07_hh_cont hΦ3 hB2 hC hC0 hK10 hK1 hA hpos y hH0 hSpsd i j
  have hhbd : ∀ r i j, |s21k2_p07_hh Φ y (s21k2_p07_Sm A H r) i j| ≤ B2 := fun r i j => by
    obtain ⟨hFc, hFb⟩ := s21k2_p07_hF hΦ3 hB2 i j
    have : IsProbabilityMeasure (s21k2_p07_gam (s21k2_p07_Sm A H r)) := inferInstance
    have := norm_integral_le_of_norm_le_const (μ := s21k2_p07_gam (s21k2_p07_Sm A H r)) (C := B2)
      (f := fun x => iteratedFDeriv ℝ 2 Φ (y + x) ![EuclideanSpace.single i 1, EuclideanSpace.single j 1])
      (Eventually.of_forall fun x => hFb _)
    simpa [s21k2_p07_hh, Real.norm_eq_abs] using this
  have hAh : ∀ i j, IntegrableOn (fun r => A r i j * s21k2_p07_hh Φ y (s21k2_p07_Sm A H r) i j)
      (Icc 0 H) := fun i j => by
    have := (hA i j).bdd_mul (c := B2) ((hhcont i j).aestronglyMeasurable measurableSet_Icc)
      (Eventually.of_forall fun r => by simpa [Real.norm_eq_abs] using hhbd r i j)
    exact this.congr (Eventually.of_forall fun r => mul_comm _ _)
  set g : ℝ → ℝ := fun r => ∑ i, ∑ j, A r i j * s21k2_p07_hh Φ y (s21k2_p07_Sm A H r) i j with hg
  have hgi : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ H → IntervalIntegrable g volume a b := fun a b ha hab hb => by
    have : IntegrableOn g (Icc 0 H) := integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hAh i j
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
    exact this.mono_set (Icc_subset_Icc ha hb)
  have hI : ∀ i j (a b : ℝ), 0 ≤ a → a ≤ b → b ≤ H → IntervalIntegrable (fun r => |A r i j|) volume a b :=
    fun i j a b ha hab hb => (s21k2_p07_intIcc (hA i j) ha hab hb).abs
  have hα0 : ∀ a b : ℝ, a ≤ b → 0 ≤ ∑ i, ∑ j, ∫ r in a..b, |A r i j| := fun a b hab =>
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      intervalIntegral.integral_nonneg hab fun r _ => abs_nonneg _
  have hs0 : 0 ≤ s := hs
  have hadd : ∀ a b c : ℝ, s ≤ a → a ≤ b → b ≤ c → c ≤ t →
      ((s21k2_p07_U Φ y (s21k2_p07_Sm A H c) - s21k2_p07_U Φ y (s21k2_p07_Sm A H a)) +
        (1 / 2) * ∫ r in a..c, g r) =
      ((s21k2_p07_U Φ y (s21k2_p07_Sm A H b) - s21k2_p07_U Φ y (s21k2_p07_Sm A H a)) +
        (1 / 2) * ∫ r in a..b, g r) +
      ((s21k2_p07_U Φ y (s21k2_p07_Sm A H c) - s21k2_p07_U Φ y (s21k2_p07_Sm A H b)) +
        (1 / 2) * ∫ r in b..c, g r) := fun a b c ha hab hbc hct => by
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hgi a b (hs0.trans ha) hab (hbc.trans (hct.trans ht)))
      (hgi b c ((hs0.trans ha).trans hab) hbc (hct.trans ht))]
    ring
  have hmadd : ∀ a b c : ℝ, s ≤ a → a ≤ b → b ≤ c → c ≤ t →
      ((C * K1 / 2) * (∑ i, ∑ j, ∫ r in a..c, |A r i j|) +
        C * K3 * (s21k2_p07_Fc A c - s21k2_p07_Fc A a)) =
      ((C * K1 / 2) * (∑ i, ∑ j, ∫ r in a..b, |A r i j|) +
        C * K3 * (s21k2_p07_Fc A b - s21k2_p07_Fc A a)) +
      ((C * K1 / 2) * (∑ i, ∑ j, ∫ r in b..c, |A r i j|) +
        C * K3 * (s21k2_p07_Fc A c - s21k2_p07_Fc A b)) := fun a b c ha hab hbc hct => by
    have h0a : 0 ≤ a := hs0.trans ha
    have hαadd : (∑ i, ∑ j, ∫ r in a..c, |A r i j|) =
        (∑ i, ∑ j, ∫ r in a..b, |A r i j|) + ∑ i, ∑ j, ∫ r in b..c, |A r i j| := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      exact (intervalIntegral.integral_add_adjacent_intervals (hI i j a b h0a hab (hbc.trans (hct.trans ht)))
        (hI i j b c (h0a.trans hab) hbc (hct.trans ht))).symm
    rw [hαadd]
    ring
  have hm0 : ∀ a b : ℝ, s ≤ a → a ≤ b → b ≤ t →
      0 ≤ (C * K1 / 2) * (∑ i, ∑ j, ∫ r in a..b, |A r i j|) +
        C * K3 * (s21k2_p07_Fc A b - s21k2_p07_Fc A a) := fun a b ha hab hb => by
    have := s21k2_p07_Fc_mono hA hpos (hs0.trans ha) hab (hb.trans ht)
    have := hα0 a b hab
    positivity
  have hFc := s21k2_p07_Fc_cont hA hH0
  have hsmall : ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∀ a b : ℝ, s ≤ a → a ≤ b → b ≤ t → b - a ≤ δ →
      |(s21k2_p07_U Φ y (s21k2_p07_Sm A H b) - s21k2_p07_U Φ y (s21k2_p07_Sm A H a)) +
        (1 / 2) * ∫ r in a..b, g r| ≤ η *
      ((C * K1 / 2) * (∑ i, ∑ j, ∫ r in a..b, |A r i j|) +
        C * K3 * (s21k2_p07_Fc A b - s21k2_p07_Fc A a)) := fun η hη => by
    have hUC : UniformContinuousOn (s21k2_p07_Fc A) (Icc 0 H) :=
      isCompact_Icc.uniformContinuousOn_of_continuous hFc
    obtain ⟨δ, hδ, hδ'⟩ := Metric.uniformContinuousOn_iff.1 hUC (η ^ 2) (by positivity)
    refine ⟨δ / 2, by positivity, fun a b ha hab hb hba => ?_⟩
    have h0a : 0 ≤ a := hs0.trans ha
    have hbH : b ≤ H := hb.trans ht
    have hloc := s21k2_p07_local hΦ3 hB0 hB2 hC hC0 hK10 hK1 hK3 hA hpos y hSpsd hAh h0a hab hbH
    have hdist := hδ' a ⟨h0a, hab.trans hbH⟩ b ⟨h0a.trans hab, hbH⟩
      (by rw [Real.dist_eq, abs_of_nonpos (by linarith)]; linarith)
    rw [Real.dist_eq, abs_of_nonpos (by linarith [s21k2_p07_Fc_mono hA hpos h0a hab hbH])] at hdist
    have hτη : Real.sqrt (s21k2_p07_Fc A b - s21k2_p07_Fc A a) ≤ η := by
      rw [← Real.sqrt_sq hη.le]
      exact Real.sqrt_le_sqrt (by linarith)
    refine hloc.trans (mul_le_mul_of_nonneg_right hτη (hm0 a b ha hab hb))
  have hz := s21k2_p07_additive_zero hst
    (fun a b => (s21k2_p07_U Φ y (s21k2_p07_Sm A H b) - s21k2_p07_U Φ y (s21k2_p07_Sm A H a)) +
        (1 / 2) * ∫ r in a..b, g r)
    (fun a b => (C * K1 / 2) * (∑ i, ∑ j, ∫ r in a..b, |A r i j|) +
        C * K3 * (s21k2_p07_Fc A b - s21k2_p07_Fc A a))
    hadd hmadd hm0 hsmall
  have hmem : ∀ r, s ≤ r → r ≤ t → r ∈ Icc (0 : ℝ) H := fun r h1 h2 => ⟨hs0.trans h1, h2.trans ht⟩
  have hint_eq : ∫ r in Set.Icc s t, ∑ i, ∑ j, A r i j * iteratedFDeriv ℝ 2 (r26t3_heat P (Γ r) Φ) y
      ![EuclideanSpace.single i 1, EuclideanSpace.single j 1] = ∫ r in s..t, g r := by
    rw [intervalIntegral.integral_of_le hst, ← integral_Icc_eq_integral_Ioc]
    refine setIntegral_congr_fun measurableSet_Icc fun r hr => ?_
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hder r (hmem r hr.1 hr.2) i j]
  rw [hint_eq, hheat t ⟨hs0.trans hst, ht⟩, hheat s ⟨hs0, hst.trans ht⟩]
  linarith

end HRS.MS.R26T3
