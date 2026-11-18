import HRS.MS.Fp81V01Insert
import HRS.MS.Fp81V01Regular
import HRS.MS.ProClosureS111PhysicalIntervals

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.Fp81.V01

open HRS HRS.Whole HRS.MS.R26T6 HRS.MS.S111T
open HRS.MS.ProClosureS111

variable {d r : ℕ}
variable {s a β γ T u c B Pw : ℝ}
variable {ρ : Euc d → ℝ}
variable {Ω : Type*} [MeasurableSpace Ω]
variable {E : r26t6_WeightedChart d r Pw}

local notation "X" => R2X d T
local notation "P2" => projTensor X 2
local notation "P3" => projTensor X 3
local notation "C" => r26t6_thermalCoeff d s a β ρ

/-- A three-factor Hölder bound for the norm of an inserted Bochner integral. -/
theorem fp81v01_insert_integral_bound (P : Measure Ω) (j : Fin 3)
    {A x y : Ω → X} (hA : MemLp A 2 P) (hx : MemLp x 4 P) (hy : MemLp y 4 P)
    {a₀ a₁ a₂ : ℝ} (ha₀ : 0 ≤ a₀) (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂)
    (hA₀ : eLpNorm A 2 P ≤ ENNReal.ofReal a₀)
    (hx₀ : eLpNorm x 4 P ≤ ENNReal.ofReal a₁)
    (hy₀ : eLpNorm y 4 P ≤ ENNReal.ofReal a₂) :
    ‖∫ w, Insert j (A w) (x w) (y w) ∂P‖ ≤ a₀ * a₁ * a₂ := by
  let f : Ω → ℝ := fun w => ‖A w‖ * (‖x w‖ * ‖y w‖)
  have hxyMem : MemLp (fun w => ‖x w‖ * ‖y w‖) 2 P := hx.norm.mul hy.norm (r := 2)
  have hxy : eLpNorm (fun w => ‖x w‖ * ‖y w‖) 2 P ≤
      ENNReal.ofReal a₁ * ENNReal.ofReal a₂ := by
    have h := eLpNorm_le_eLpNorm_mul_eLpNorm_of_norm (p := 4) (q := 4) (r := 2)
      (f := fun w => ‖x w‖) (g := fun w => ‖y w‖)
      (fun z z' : ℝ => z * z') 1 continuous_mul
      hx.norm.aestronglyMeasurable hy.norm.aestronglyMeasurable
      (Eventually.of_forall fun w => by simp)
    have hxe : eLpNorm (fun w => ‖x w‖) 4 P = eLpNorm x 4 P :=
      eLpNorm_norm _ hx.aestronglyMeasurable
    have hye : eLpNorm (fun w => ‖y w‖) 4 P = eLpNorm y 4 P :=
      eLpNorm_norm _ hy.aestronglyMeasurable
    rw [hxe, hye] at h
    calc eLpNorm (fun w => ‖x w‖ * ‖y w‖) 2 P
        ≤ eLpNorm x 4 P * eLpNorm y 4 P := by simpa using h
      _ ≤ ENNReal.ofReal a₁ * ENNReal.ofReal a₂ := mul_le_mul' hx₀ hy₀
  have hscalar : Integrable f P := hA.norm.integrable_mul hxyMem
  have hscalarBound : eLpNorm f 1 P ≤ ENNReal.ofReal (a₀ * a₁ * a₂) := by
    have h := eLpNorm_le_eLpNorm_mul_eLpNorm_of_norm (p := 2) (q := 2) (r := 1)
      (f := fun w => ‖A w‖) (g := fun w => ‖x w‖ * ‖y w‖)
      (fun z z' : ℝ => z * z') 1 continuous_mul
      hA.norm.aestronglyMeasurable hxyMem.aestronglyMeasurable
      (Eventually.of_forall fun w => by simp)
    have hAe : eLpNorm (fun w => ‖A w‖) 2 P = eLpNorm A 2 P :=
      eLpNorm_norm _ hA.aestronglyMeasurable
    rw [hAe] at h
    calc eLpNorm f 1 P ≤ eLpNorm A 2 P * eLpNorm (fun w => ‖x w‖ * ‖y w‖) 2 P := by
          simpa [f] using h
      _ ≤ ENNReal.ofReal a₀ * (ENNReal.ofReal a₁ * ENNReal.ofReal a₂) :=
          mul_le_mul' hA₀ hxy
      _ = ENNReal.ofReal (a₀ * a₁ * a₂) := by
          rw [← ENNReal.ofReal_mul ha₁, ← ENNReal.ofReal_mul ha₀]
          congr 1
          ring
  have hF : Integrable (fun w => Insert j (A w) (x w) (y w)) P :=
    Insert_integrable P hA hx hy j
  have hnormF : Integrable (fun w => ‖Insert j (A w) (x w) (y w)‖) P := hF.norm
  have hpoint : ∀ w, ‖Insert j (A w) (x w) (y w)‖ ≤ f w := by
    intro w
    have h := (insertion_bounds j (A w) (x w) (y w) (0 : P2)).1
    simpa [f, mul_assoc] using h
  have hmono : (∫ w, ‖Insert j (A w) (x w) (y w)‖ ∂P) ≤ ∫ w, f w ∂P :=
    integral_mono hnormF hscalar hpoint
  have hscalarInt : ∫ w, f w ∂P = (eLpNorm f 1 P).toReal := by
    have hnonneg : ∀ w, 0 ≤ f w := fun w => mul_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    calc ∫ w, f w ∂P = ∫ w, ‖f w‖ ∂P := by
          apply integral_congr_ae
          filter_upwards with w
          rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg w)]
      _ = (eLpNorm f 1 P).toReal := by
          rw [eLpNorm_one_eq_lintegral_enorm,
            integral_norm_eq_lintegral_enorm hscalar.aestronglyMeasurable]
          exact hscalar.aestronglyMeasurable
  have hreal : (eLpNorm f 1 P).toReal ≤ a₀ * a₁ * a₂ :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) hscalarBound
  calc ‖∫ w, Insert j (A w) (x w) (y w) ∂P‖
      ≤ ∫ w, ‖Insert j (A w) (x w) (y w)‖ ∂P := norm_integral_le_integral_norm _
    _ ≤ ∫ w, f w ∂P := hmono
    _ = (eLpNorm f 1 P).toReal := hscalarInt
    _ ≤ a₀ * a₁ * a₂ := hreal

/-- The corresponding two-factor estimate for a paired covariance insertion. -/
theorem fp81v01_pairinsert_integral_bound (P : Measure Ω) (j : Fin 3)
    {Q : Ω → P2} {x : Ω → X} (hQ : MemLp Q 2 P) (hx : MemLp x 2 P)
    {a₀ a₁ : ℝ} (ha₀ : 0 ≤ a₀) (ha₁ : 0 ≤ a₁)
    (hQ₀ : eLpNorm Q 2 P ≤ ENNReal.ofReal a₀)
    (hx₀ : eLpNorm x 2 P ≤ ENNReal.ofReal a₁) :
    ‖∫ w, PairInsert j (Q w) (x w) ∂P‖ ≤ a₀ * a₁ := by
  let f : Ω → ℝ := fun w => ‖Q w‖ * ‖x w‖
  have hscalar : Integrable f P := hQ.norm.integrable_mul hx.norm
  have hscalarBound : eLpNorm f 1 P ≤ ENNReal.ofReal (a₀ * a₁) := by
    have h := eLpNorm_le_eLpNorm_mul_eLpNorm_of_norm (p := 2) (q := 2) (r := 1)
      (f := fun w => ‖Q w‖) (g := fun w => ‖x w‖)
      (fun z z' : ℝ => z * z') 1 continuous_mul
      hQ.norm.aestronglyMeasurable hx.norm.aestronglyMeasurable
      (Eventually.of_forall fun w => by simp)
    have hQe : eLpNorm (fun w => ‖Q w‖) 2 P = eLpNorm Q 2 P :=
      eLpNorm_norm _ hQ.aestronglyMeasurable
    have hxe : eLpNorm (fun w => ‖x w‖) 2 P = eLpNorm x 2 P :=
      eLpNorm_norm _ hx.aestronglyMeasurable
    rw [hQe, hxe] at h
    calc eLpNorm f 1 P ≤ eLpNorm Q 2 P * eLpNorm x 2 P := by simpa [f] using h
      _ ≤ ENNReal.ofReal a₀ * ENNReal.ofReal a₁ := mul_le_mul' hQ₀ hx₀
      _ = ENNReal.ofReal (a₀ * a₁) := by rw [← ENNReal.ofReal_mul ha₀]
  have hF : Integrable (fun w => PairInsert j (Q w) (x w)) P := PairInsert_integrable P hQ hx j
  have hnormF : Integrable (fun w => ‖PairInsert j (Q w) (x w)‖) P := hF.norm
  have hpoint : ∀ w, ‖PairInsert j (Q w) (x w)‖ ≤ f w := by
    intro w
    have h := (insertion_bounds j 0 0 (x w) (Q w)).2
    simpa [f] using h
  have hmono : (∫ w, ‖PairInsert j (Q w) (x w)‖ ∂P) ≤ ∫ w, f w ∂P :=
    integral_mono hnormF hscalar hpoint
  have hscalarInt : ∫ w, f w ∂P = (eLpNorm f 1 P).toReal := by
    have hnonneg : ∀ w, 0 ≤ f w := fun w => mul_nonneg (norm_nonneg _) (norm_nonneg _)
    calc ∫ w, f w ∂P = ∫ w, ‖f w‖ ∂P := by
          apply integral_congr_ae
          filter_upwards with w
          rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg w)]
      _ = (eLpNorm f 1 P).toReal := by
          rw [eLpNorm_one_eq_lintegral_enorm,
            integral_norm_eq_lintegral_enorm hscalar.aestronglyMeasurable]
          exact hscalar.aestronglyMeasurable
  have hreal : (eLpNorm f 1 P).toReal ≤ a₀ * a₁ :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) hscalarBound
  calc ‖∫ w, PairInsert j (Q w) (x w) ∂P‖
      ≤ ∫ w, ‖PairInsert j (Q w) (x w)‖ ∂P := norm_integral_le_integral_norm _
    _ ≤ ∫ w, f w ∂P := hmono
    _ = (eLpNorm f 1 P).toReal := hscalarInt
    _ ≤ a₀ * a₁ := hreal

private theorem fp81v01_age_nonneg (c u t : ℝ) : 0 ≤ HRS.MS.S111K2.s111k2_age c u t :=
  (Real.exp_pos _).le

private theorem fp81v01_age_integrable (H : ℝ) (hH : 0 ≤ H) (c u : ℝ) :
    IntegrableOn (fun t => HRS.MS.S111K2.s111k2_age c u t) (Icc 0 H) := by
  have hc : Continuous fun t => HRS.MS.S111K2.s111k2_age c u t := by
    unfold HRS.MS.S111K2.s111k2_age
    fun_prop
  exact hc.continuousOn.integrableOn_Icc

private theorem fp81v01_age_sq_integrable (H : ℝ) (hH : 0 ≤ H) (c u : ℝ) :
    IntegrableOn (fun t => HRS.MS.S111K2.s111k2_age c u t ^ 2) (Icc 0 H) := by
  have hc : Continuous fun t => HRS.MS.S111K2.s111k2_age c u t := by
    unfold HRS.MS.S111K2.s111k2_age
    fun_prop
  exact (hc.pow 2).continuousOn.integrableOn_Icc

/-- Cumulative cubic sources built from random interval responses. The observation bound
is stated explicitly because it is the `M` used in the scalar variation majorants. -/
theorem cumulative_sources
    (hu : 0 ≤ u) (hT : 0 < T) (hc : 0 < c) (hB : 0 ≤ B)
    (R M : ℝ) (hR : 0 ≤ R) (hM : 0 ≤ M)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (O : r26t6_IntervalOperators E C T u c B)
    (qL qQ : ℝ × Ω → r26t6_Coeff) (Z : Ω → X)
    (hL : RandomIntervalControl P O qL (fun _ => R))
    (hQ : RandomIntervalControl P O qQ (fun _ => R))
    (hZ : MemLp Z 4 P ∧ eLpNorm Z 4 P ≤ ENNReal.ofReal M) (I : P3) :
    ∃ S : CubicSources d T u (I + D P O qQ Z (u + T) + J P O qL Z (u + T)),
      S.initial = I ∧ S.drift = D P O qQ Z ∧ S.covariance = J P O qL Z := by
  let H := u + T
  have hH : 0 ≤ H := by dsimp [H]; linarith
  have hZ2 : MemLp Z 2 P := hZ.1.mono_exponent (by norm_num)
  have hZ2bound : eLpNorm Z 2 P ≤ ENNReal.ofReal M := by
    exact (eLpNorm_le_eLpNorm_of_exponent_le (μ := P) (f := Z)
      (p := (2 : ℝ≥0∞)) (q := 4) (by norm_num)).trans hZ.2
  have hDinc : ∀ v w, 0 ≤ v → v ≤ w → w ≤ H →
      ‖D P O qQ Z w - D P O qQ Z v‖ ≤
        ∫ t in Icc v w, (3 * B * R * M ^ 2) * HRS.MS.S111K2.s111k2_age c u t := by
    intro v w hv hvw hw
    have hres := (hQ.increments v w hv hvw (by dsimp [H] at hw ⊢; exact hw)).1
    have hage : IntegrableOn (fun t => HRS.MS.S111K2.s111k2_age c u t) (Icc v w) := by
      apply (fp81v01_age_integrable H hH c u).mono_set
      intro t ht
      exact ⟨hv.trans ht.1, ht.2.trans hw⟩
    have hage0 : ∀ t ∈ Icc v w, 0 ≤ HRS.MS.S111K2.s111k2_age c u t :=
      fun t _ => fp81v01_age_nonneg c u t
    have hconstant : (∫ t in Icc v w,
        HRS.MS.S111K2.s111k2_age c u t * (fun _ : ℝ => R) t) =
        R * ∫ t in Icc v w, HRS.MS.S111K2.s111k2_age c u t := by
      rw [integral_mul_const]
      ring
    have hageInt0 : 0 ≤ ∫ t in Icc v w, HRS.MS.S111K2.s111k2_age c u t :=
      setIntegral_nonneg measurableSet_Icc (fun t _ => fp81v01_age_nonneg c u t)
    have hres' : eLpNorm (fun z => r26t6_randomDrift O qQ w z -
          r26t6_randomDrift O qQ v z) 2 P ≤
        ENNReal.ofReal (B * R * ∫ t in Icc v w, HRS.MS.S111K2.s111k2_age c u t) := by
      rw [hconstant] at hres
      simpa [mul_assoc] using hres
    have hMv := hQ.moments v ⟨hv, hvw.trans hw⟩
    have hMw := hQ.moments w ⟨hv.trans hvw, hw⟩
    have hA : MemLp (fun z => r26t6_randomDrift O qQ w z -
        r26t6_randomDrift O qQ v z) 2 P := hMw.1.sub hMv.1
    have hsum : ∀ j : Fin 3,
        ‖(∫ z, Insert j (r26t6_randomDrift O qQ w z) (Z z) (Z z) ∂P) -
          (∫ z, Insert j (r26t6_randomDrift O qQ v z) (Z z) (Z z) ∂P)‖ ≤
          (B * R * ∫ t in Icc v w, HRS.MS.S111K2.s111k2_age c u t) * M * M := by
      intro j
      let A : Ω → X := fun z => r26t6_randomDrift O qQ w z - r26t6_randomDrift O qQ v z
      have hIw := Insert_integrable P (hMw.1) hZ.1 hZ.1 j
      have hIv := Insert_integrable P (hMv.1) hZ.1 hZ.1 j
      have hEq : (∫ z, Insert j (A z) (Z z) (Z z) ∂P) =
          (∫ z, Insert j (r26t6_randomDrift O qQ w z) (Z z) (Z z) ∂P) -
            (∫ z, Insert j (r26t6_randomDrift O qQ v z) (Z z) (Z z) ∂P) := by
        rw [← integral_sub hIw hIv]
        congr 1
        funext z
        simp [A]
      rw [← hEq]
      exact fp81v01_insert_integral_bound P j hA hZ.1 hZ.1
        (mul_nonneg (mul_nonneg hB hR) hageInt0) hM hM hres' hZ.2 hZ.2
    unfold D
    rw [← Finset.sum_sub_distrib]
    calc ‖∑ j : Fin 3,
          ((∫ z, Insert j (r26t6_randomDrift O qQ w z) (Z z) (Z z) ∂P) -
            (∫ z, Insert j (r26t6_randomDrift O qQ v z) (Z z) (Z z) ∂P))‖
        ≤ ∑ j : Fin 3, ‖(∫ z, Insert j (r26t6_randomDrift O qQ w z) (Z z) (Z z) ∂P) -
            (∫ z, Insert j (r26t6_randomDrift O qQ v z) (Z z) (Z z) ∂P)‖ := norm_sum_le _ _
      _ ≤ ∑ _j : Fin 3,
          (B * R * ∫ t in Icc v w, HRS.MS.S111K2.s111k2_age c u t) * M * M :=
            Finset.sum_le_sum fun j _ => hsum j
      _ = ∫ t in Icc v w, (3 * B * R * M ^ 2) * HRS.MS.S111K2.s111k2_age c u t := by
        rw [Finset.sum_const, Finset.card_fin]
        simp only [nsmul_eq_mul]
        rw [integral_const_mul]
        ring
  have hJinc : ∀ v w, 0 ≤ v → v ≤ w → w ≤ H →
      ‖J P O qL Z w - J P O qL Z v‖ ≤
        ∫ t in Icc v w, (3 * B * |2 * (r26t6_thermalCoeff d s a β ρ).ν| * R * M) *
          HRS.MS.S111K2.s111k2_age c u t ^ 2 := by
    intro v w hv hvw hw
    have hres := (hL.increments v w hv hvw (by dsimp [H] at hw ⊢; exact hw)).2
    have hconstant : (∫ t in Icc v w,
        HRS.MS.S111K2.s111k2_age c u t ^ 2 * (fun _ : ℝ => R) t) =
        R * ∫ t in Icc v w, HRS.MS.S111K2.s111k2_age c u t ^ 2 := by
      rw [integral_mul_const]
      ring
    have hageSqInt0 : 0 ≤ ∫ t in Icc v w, HRS.MS.S111K2.s111k2_age c u t ^ 2 :=
      setIntegral_nonneg measurableSet_Icc (fun t _ => sq_nonneg _)
    have hres' : eLpNorm (fun z => r26t6_randomCovariance O qL w z -
          r26t6_randomCovariance O qL v z) 2 P ≤
        ENNReal.ofReal (B * |2 * (r26t6_thermalCoeff d s a β ρ).ν| * R * ∫ t in Icc v w,
          HRS.MS.S111K2.s111k2_age c u t ^ 2) := by
      rw [hconstant] at hres
      simpa [mul_assoc] using hres
    have hMv := hL.moments v ⟨hv, hvw.trans hw⟩
    have hMw := hL.moments w ⟨hv.trans hvw, hw⟩
    have hA : MemLp (fun z => r26t6_randomCovariance O qL w z -
        r26t6_randomCovariance O qL v z) 2 P := hMw.2.sub hMv.2
    have hsum : ∀ j : Fin 3,
        ‖(∫ z, PairInsert j (r26t6_randomCovariance O qL w z) (Z z) ∂P) -
          (∫ z, PairInsert j (r26t6_randomCovariance O qL v z) (Z z) ∂P)‖ ≤
          (B * |2 * (r26t6_thermalCoeff d s a β ρ).ν| * R * ∫ t in Icc v w,
            HRS.MS.S111K2.s111k2_age c u t ^ 2) * M := by
      intro j
      let A : Ω → P2 := fun z => r26t6_randomCovariance O qL w z - r26t6_randomCovariance O qL v z
      have hIw := PairInsert_integrable P hMw.2 hZ2 j
      have hIv := PairInsert_integrable P hMv.2 hZ2 j
      have hEq : (∫ z, PairInsert j (A z) (Z z) ∂P) =
          (∫ z, PairInsert j (r26t6_randomCovariance O qL w z) (Z z) ∂P) -
            (∫ z, PairInsert j (r26t6_randomCovariance O qL v z) (Z z) ∂P) := by
        rw [← integral_sub hIw hIv]
        apply integral_congr_ae
        filter_upwards with z
        simp [A]
      rw [← hEq]
      exact fp81v01_pairinsert_integral_bound P j hA hZ2
        (mul_nonneg (mul_nonneg (mul_nonneg hB (abs_nonneg _)) hR) hageSqInt0)
        hM hres' hZ2bound
    unfold J
    rw [← Finset.sum_sub_distrib]
    calc ‖∑ j : Fin 3,
          ((∫ z, PairInsert j (r26t6_randomCovariance O qL w z) (Z z) ∂P) -
            (∫ z, PairInsert j (r26t6_randomCovariance O qL v z) (Z z) ∂P))‖
        ≤ ∑ j : Fin 3, ‖(∫ z, PairInsert j (r26t6_randomCovariance O qL w z) (Z z) ∂P) -
            (∫ z, PairInsert j (r26t6_randomCovariance O qL v z) (Z z) ∂P)‖ := norm_sum_le _ _
      _ ≤ ∑ _j : Fin 3,
          (B * |2 * (r26t6_thermalCoeff d s a β ρ).ν| * R * ∫ t in Icc v w,
            HRS.MS.S111K2.s111k2_age c u t ^ 2) * M := Finset.sum_le_sum fun j _ => hsum j
      _ = ∫ t in Icc v w, (3 * B * |2 * (r26t6_thermalCoeff d s a β ρ).ν| * R * M) *
            HRS.MS.S111K2.s111k2_age c u t ^ 2 := by
        rw [Finset.sum_const, Finset.card_fin]
        simp only [nsmul_eq_mul]
        rw [integral_const_mul]
        ring
  have hDreg := fp81v01_regular_of_majorant
    (D P O qQ Z) H hH
    (fun t => (3 * B * R * M ^ 2) * HRS.MS.S111K2.s111k2_age c u t)
    ((fp81v01_age_integrable H hH c u).const_mul (3 * B * R * M ^ 2))
    (fun t ht => mul_nonneg (by positivity) (fp81v01_age_nonneg c u t)) hDinc
  have hJreg := fp81v01_regular_of_majorant
    (J P O qL Z) H hH
    (fun t => (3 * B * |2 * (r26t6_thermalCoeff d s a β ρ).ν| * R * M) * HRS.MS.S111K2.s111k2_age c u t ^ 2)
    ((fp81v01_age_sq_integrable H hH c u).const_mul
      (3 * B * |2 * (r26t6_thermalCoeff d s a β ρ).ν| * R * M))
    (fun t ht => mul_nonneg (by positivity) (sq_nonneg _)) hJinc
  have hD0 : D P O qQ Z 0 = 0 := by
    simp [D, hQ.drift_zero]
  have hJ0 : J P O qL Z 0 = 0 := by
    simp [J, hL.covariance_zero]
  let S : CubicSources d T u (I + D P O qQ Z H + J P O qL Z H) :=
    ⟨I, D P O qQ Z, J P O qL Z, hD0, hJ0,
      by simpa [H] using hDreg.1,
      by simpa [H] using hJreg.1,
      lt_of_le_of_lt hDreg.2 ENNReal.ofReal_lt_top,
      lt_of_le_of_lt hJreg.2 ENNReal.ofReal_lt_top, by dsimp [H]⟩
  exact ⟨S, rfl, rfl, rfl⟩

#print axioms fp81v01_insert_integral_bound
#print axioms fp81v01_pairinsert_integral_bound
#print axioms cumulative_sources

end HRS.Fp81.V01
end
