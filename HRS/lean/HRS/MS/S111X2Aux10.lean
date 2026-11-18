import HRS.MS.S111X2Aux9

/-!
# S11.1 X2, packet E02 (part 5): `IsResponse` of the generator and the Dirichlet identity
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S111X2

open HRS HRS.Whole
open HRS.MS.S111X1 (EnData KData Nnl)
open HRS.Whole.Q34 (isProbabilityMeasure_nu)
open HRS.MS.TcR (tc2_integrable_nu tc2_integral_nu)

variable {d : ℕ}

section Core

variable {s β : ℝ} {ρ : Euc d → ℝ} {M : ℝ} {C : WholeCoeff d}

theorem s111x2_N_facts (T : TD d s β ρ M C) {h : Euc d → ℝ} {B1 B2 : ℝ} (H : CbD h B1 B2) :
    Measurable (Nnl d s ρ (gradient h)) ∧
      ∀ x, |Nnl d s ρ (gradient h) x| ≤ B1 * HRS.MS.S111X1.kA d s M ρ := by
  have hgm : Measurable (gradient h) :=
    (s111x2_gradient_continuous (H.smooth.of_le (by norm_num))).measurable
  exact ⟨HRS.MS.S111X1.Nnl_meas T.en.K hgm,
    fun x => HRS.MS.S111X1.Nnl_bdd T.en.K (a := gradient h) (Ba := B1)
      (fun y => by rw [s111x2_norm_gradient]; exact H.d1 y) x⟩

theorem s111x2_N_integrable (T : TD d s β ρ M C) {h : Euc d → ℝ} {B1 B2 : ℝ} (H : CbD h B1 B2) :
    Integrable (Nnl d s ρ (gradient h)) (HRS.Whole.withDensityReal ρ) := by
  haveI := isProbabilityMeasure_nu T.prob
  obtain ⟨hm, hb⟩ := s111x2_N_facts T H
  exact (integrable_const (B1 * HRS.MS.S111X1.kA d s M ρ)).mono' hm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hb x)

/-- `β ∫ g(x-y) (-β⁻¹ L h)(y) dμ(y) = N(x)`: the nonlocal term is the potential of `L h`. -/
theorem s111x2_T_eq (T : TD d s β ρ M C) {h : Euc d → ℝ} {B1 B2 : ℝ} (H : CbD h B1 B2) (x : Euc d) :
    ∫ y, HRS.Whole.rieszKernel d s (x - y) * (-β⁻¹ * s111x2_L ρ h y) ∂(HRS.Whole.withDensityReal ρ) =
      β⁻¹ * Nnl d s ρ (gradient h) x := by
  obtain ⟨C0, c, hC0, hc, h0, h1⟩ := T.gauss
  have hβ := T.en.hβ
  rw [tc2_integral_nu T.prob]
  have hibp := s111x2_nonlocal_ibp T.en.K.hd T.en.K.hs0 T.en.K.hs1 T.en.K T.en.smooth hc hC0 h0 h1
    H.smooth H.d1 H.d2 x
  have e : ∀ y, ρ y * (HRS.Whole.rieszKernel d s (x - y) * (-β⁻¹ * s111x2_L ρ h y)) =
      β⁻¹ * (HRS.Whole.rieszKernel d s (x - y) *
        (ρ y * Laplacian.laplacian h y + inner ℝ (gradient ρ y) (gradient h y))) := by
    intro y
    have := s111x2_rhoL T h y
    calc ρ y * (HRS.Whole.rieszKernel d s (x - y) * (-β⁻¹ * s111x2_L ρ h y))
        = -β⁻¹ * HRS.Whole.rieszKernel d s (x - y) * (ρ y * s111x2_L ρ h y) := by ring
      _ = _ := by rw [this]; ring
  simp_rw [e]
  rw [integral_const_mul, hibp]
  rfl

theorem s111x2_gen_eq (T : TD d s β ρ M C) {h : Euc d → ℝ} {B1 B2 : ℝ} (H : CbD h B1 B2) :
    generatorW C 0 h = fun x => -β⁻¹ * s111x2_L ρ h x + Nnl d s ρ (gradient h) x :=
  funext fun x => s111x2_gen_split T H x

theorem s111x2_gen_memLp (T : TD d s β ρ M C) {h : Euc d → ℝ} {B1 B2 : ℝ} (H : CbD h B1 B2) :
    MemLp (generatorW C 0 h) 2 (HRS.Whole.withDensityReal ρ) := by
  haveI := isProbabilityMeasure_nu T.prob
  rw [s111x2_gen_eq T H]
  obtain ⟨hm, hb⟩ := s111x2_N_facts T H
  have hN : MemLp (Nnl d s ρ (gradient h)) 2 (HRS.Whole.withDensityReal ρ) :=
    (MemLp.of_bound hm.aestronglyMeasurable (B1 * HRS.MS.S111X1.kA d s M ρ)
      (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hb x)).mono_exponent le_top
  exact ((s111x2_L_memLp T H).const_mul (-β⁻¹)).add hN

/-- **E02, `IsResponse`.** -/
theorem s111x2_isResponse_gen (T : TD d s β ρ M C) {h : Euc d → ℝ} {B1 B2 : ℝ} (H : CbD h B1 B2) :
    HRS.Whole.IsResponse (HRS.Whole.rieszKernel d s) (HRS.Whole.withDensityReal ρ) β (generatorW C 0 h)
      (fun x => -β⁻¹ * s111x2_L ρ h x) := by
  haveI := isProbabilityMeasure_nu T.prob
  have hβ := T.en.hβ
  have hLi : Integrable (s111x2_L ρ h) (HRS.Whole.withDensityReal ρ) :=
    (s111x2_L_memLp T H).integrable (by norm_num)
  have hNi := s111x2_N_integrable T H
  refine ⟨⟨(s111x2_L_memLp T H).const_mul (-β⁻¹), ?_⟩, Filter.Eventually.of_forall fun x => ?_⟩
  · rw [integral_const_mul, s111x2_L_mean_zero T H, mul_zero]
  · have hG : ∫ y, generatorW C 0 h y ∂(HRS.Whole.withDensityReal ρ) =
        ∫ y, Nnl d s ρ (gradient h) y ∂(HRS.Whole.withDensityReal ρ) := by
      rw [s111x2_gen_eq T H]
      rw [integral_add (hLi.const_mul _) hNi, integral_const_mul, s111x2_L_mean_zero T H]
      simp
    have hK : HRS.Whole.Kop (HRS.Whole.rieszKernel d s) (HRS.Whole.withDensityReal ρ)
        (fun x => -β⁻¹ * s111x2_L ρ h x) x =
        β⁻¹ * Nnl d s ρ (gradient h) x - β⁻¹ * ∫ y, Nnl d s ρ (gradient h) y ∂(HRS.Whole.withDensityReal ρ) := by
      unfold HRS.Whole.Kop HRS.Whole.projMean HRS.Whole.pair
      simp only
      have e : ∀ x', ∫ y, HRS.Whole.rieszKernel d s (x' - y) * (-β⁻¹ * s111x2_L ρ h y)
          ∂(HRS.Whole.withDensityReal ρ) = β⁻¹ * Nnl d s ρ (gradient h) x' := fun x' =>
        s111x2_T_eq T H x'
      simp_rw [e]
      rw [integral_const_mul]
    unfold HRS.Whole.projMean HRS.Whole.pair
    rw [hK, hG, s111x2_gen_eq T H]
    field_simp
    ring

end Core

end HRS.MS.S111X2
