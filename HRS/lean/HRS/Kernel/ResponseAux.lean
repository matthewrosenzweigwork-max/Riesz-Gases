import HRS.Torus.Basic

/-!
# Auxiliary results for the response equation (work package KERN-02)

Generic Hilbert-space facts used to solve `h + β K_μ h = P_μ ψ` for `μ = ρ dx`:
the convolution with an even integrable kernel `g` whose Fourier coefficients `ĝ ≥ 0`
is a bounded, self-adjoint, nonnegative operator on `L²`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.ResponseAux

open HRS

variable {d : ℕ}

local instance : (volume : Measure (Torus d)).IsNegInvariant :=
  MeasureTheory.Measure.pi.isNegInvariant (fun _ : Fin d => (volume : Measure UnitAddCircle))


theorem eLpNorm_two_sq {α : Type*} [MeasurableSpace α] {ν : Measure α} {F : α → ℝ}
    (hF : AEStronglyMeasurable F ν) :
    eLpNorm F 2 ν ^ 2 = ∫⁻ x, ‖F x‖ₑ ^ 2 ∂ν := by
  have h := eLpNorm_nnreal_pow_eq_lintegral (p := 2) (f := F) (by norm_num) hF
  simpa using h

theorem memLp_two_of_lintegral {α : Type*} [MeasurableSpace α] {ν : Measure α} {F : α → ℝ}
    (hF : AEStronglyMeasurable F ν) (h : ∫⁻ x, ‖F x‖ₑ ^ 2 ∂ν < ∞) : MemLp F 2 ν := by
  rw [memLp_iff]
  rw [← eLpNorm_two_sq hF] at h
  by_contra hc
  rw [not_lt, top_le_iff] at hc
  rw [hc] at h
  simp at h

theorem lintegral_of_memLp_two {α : Type*} [MeasurableSpace α] {ν : Measure α} {F : α → ℝ}
    (hF : MemLp F 2 ν) : ∫⁻ x, ‖F x‖ₑ ^ 2 ∂ν < ∞ := by
  rw [← eLpNorm_two_sq hF.aestronglyMeasurable]
  exact ENNReal.pow_lt_top hF


theorem lintegral_sub_left (F : Torus d → ℝ≥0∞) (x : Torus d) :
    ∫⁻ y, F (x - y) = ∫⁻ y, F y := lintegral_sub_left_eq_self F x

theorem lintegral_sub_right (F : Torus d → ℝ≥0∞) (x : Torus d) :
    ∫⁻ y, F (y - x) = ∫⁻ y, F y := lintegral_sub_right_eq_self F x

/-- Cauchy–Schwarz in `ℝ≥0∞`: `(∫ a b)² ≤ (∫ a)(∫ a b²)`. -/
theorem cs_lintegral {α : Type*} [MeasurableSpace α] (ν : Measure α) {a b : α → ℝ≥0∞}
    (ha : AEMeasurable a ν) (hb : AEMeasurable b ν) :
    (∫⁻ y, a y * b y ∂ν) ^ 2 ≤ (∫⁻ y, a y ∂ν) * ∫⁻ y, a y * b y ^ 2 ∂ν := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq ν (Real.HolderConjugate.two_two)
    (f := fun y => a y ^ (1/2 : ℝ)) (g := fun y => a y ^ (1/2 : ℝ) * b y)
    (ha.pow_const _) ((ha.pow_const _).mul hb)
  have e1 : ∀ y, ((fun y => a y ^ (1/2 : ℝ)) * (fun y => a y ^ (1/2 : ℝ) * b y)) y = a y * b y := by
    intro y
    simp only [Pi.mul_apply]
    rw [← mul_assoc, ← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
    norm_num
  have e2 : ∀ y, (a y ^ (1/2 : ℝ)) ^ (2 : ℝ) = a y := by
    intro y; rw [← ENNReal.rpow_mul]; norm_num
  have e3 : ∀ y, (a y ^ (1/2 : ℝ) * b y) ^ (2 : ℝ) = a y * b y ^ 2 := by
    intro y
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), e2]
    norm_cast
  simp_rw [e1, e2, e3] at h
  calc (∫⁻ y, a y * b y ∂ν) ^ 2
      ≤ ((∫⁻ y, a y ∂ν) ^ (1 / (2:ℝ)) * (∫⁻ y, a y * b y ^ 2 ∂ν) ^ (1 / (2:ℝ))) ^ 2 := by
        gcongr
    _ = _ := by
        rw [mul_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast (x := (∫⁻ y, a y * b y ^ 2 ∂ν) ^ (1 / (2:ℝ))),
          ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
        norm_num


theorem young_lintegral (g F : Torus d → ℝ) (hg : Measurable g) (hF : Measurable F) :
    ∫⁻ x, (∫⁻ y, ‖g (x - y)‖ₑ * ‖F y‖ₑ) ^ 2 ≤ (∫⁻ y, ‖g y‖ₑ) ^ 2 * ∫⁻ y, ‖F y‖ₑ ^ 2 := by
  set N : ℝ≥0∞ := ∫⁻ y, ‖g y‖ₑ with hN
  have hga : ∀ x, Measurable fun y : Torus d => ‖g (x - y)‖ₑ := fun x =>
    (hg.comp (measurable_const.sub measurable_id)).enorm
  have h1 : ∀ x, (∫⁻ y, ‖g (x - y)‖ₑ * ‖F y‖ₑ) ^ 2 ≤ N * ∫⁻ y, ‖g (x - y)‖ₑ * ‖F y‖ₑ ^ 2 := by
    intro x
    have := cs_lintegral (volume : Measure (Torus d)) (a := fun y => ‖g (x - y)‖ₑ)
      (b := fun y => ‖F y‖ₑ) (hga x).aemeasurable hF.enorm.aemeasurable
    rw [lintegral_sub_left (fun z => ‖g z‖ₑ) x] at this
    exact this
  calc ∫⁻ x, (∫⁻ y, ‖g (x - y)‖ₑ * ‖F y‖ₑ) ^ 2
      ≤ ∫⁻ x, N * ∫⁻ y, ‖g (x - y)‖ₑ * ‖F y‖ₑ ^ 2 := lintegral_mono h1
    _ = N * ∫⁻ x, ∫⁻ y, ‖g (x - y)‖ₑ * ‖F y‖ₑ ^ 2 := by
        rw [lintegral_const_mul]
        exact Measurable.lintegral_prod_right' (f := fun p : Torus d × Torus d =>
          ‖g (p.1 - p.2)‖ₑ * ‖F p.2‖ₑ ^ 2)
          (((hg.comp (measurable_fst.sub measurable_snd)).enorm).mul
            ((hF.comp measurable_snd).enorm.pow_const 2))
    _ = N * ∫⁻ y, ∫⁻ x, ‖g (x - y)‖ₑ * ‖F y‖ₑ ^ 2 := by
        rw [lintegral_lintegral_swap]
        exact (((hg.comp (measurable_fst.sub measurable_snd)).enorm).mul
            ((hF.comp measurable_snd).enorm.pow_const 2)).aemeasurable
    _ = N * ∫⁻ y, N * ‖F y‖ₑ ^ 2 := by
        congr 1
        refine lintegral_congr fun y => ?_
        have hm : Measurable fun x : Torus d => ‖g (x - y)‖ₑ :=
          (hg.comp (measurable_id.sub measurable_const)).enorm
        rw [lintegral_mul_const _ hm, lintegral_sub_right (fun z => ‖g z‖ₑ) y]
    _ = _ := by
        rw [lintegral_const_mul _ (hF.enorm.pow_const 2)]
        ring


theorem mode_add_pt (k : Lattice d) (x y : Torus d) :
    Torus.mode k (x + y) = Torus.mode k x * Torus.mode k y := by
  unfold Torus.mode UnitAddTorus.mFourier
  simp only [ContinuousMap.coe_mk, Pi.add_apply, fourier_apply, smul_add, AddCircle.toCircle_add,
    Circle.coe_mul, Finset.prod_mul_distrib]

theorem mode_sub_pt (k : Lattice d) (x y : Torus d) :
    Torus.mode k x = Torus.mode k (x - y) * Torus.mode k y := by
  rw [← mode_add_pt]; simp

/-- Convolution against `volume`: `(g ⋆ F)(x) = ∫ g(x-y) F(y) dy`. -/
def cv (g F : Torus d → ℝ) (x : Torus d) : ℝ := ∫ y, g (x - y) * F y

theorem cv_congr_ae (g : Torus d → ℝ) {F F' : Torus d → ℝ} (h : F =ᵐ[volume] F') : cv g F = cv g F' := by
  funext x
  unfold cv
  refine integral_congr_ae ?_
  filter_upwards [h] with y hy
  rw [hy]

theorem integrable_cv_integrand {g F : Torus d → ℝ} (hg : Integrable g) (hF : Integrable F) :
    Integrable (fun p : Torus d × Torus d => g (p.1 - p.2) * F p.2) (volume.prod volume) := by
  have := Integrable.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) hF hg
  refine this.congr (Filter.Eventually.of_forall fun p => ?_)
  simp [mul_comm]

theorem fourier_cv {g F : Torus d → ℝ} (hg : Integrable g) (hF : Integrable F)
    (ĝ : Lattice d → ℝ) (hcoef : ∀ n, ∫ x, Torus.mode (-n) x * (g x : ℂ) = (ĝ n : ℂ)) (n : Lattice d) :
    ∫ x, Torus.mode (-n) x * (cv g F x : ℂ) = (ĝ n : ℂ) * ∫ y, Torus.mode (-n) y * (F y : ℂ) := by
  have hint := integrable_cv_integrand hg hF
  have hcpx : Integrable (fun p : Torus d × Torus d =>
      Torus.mode (-n) p.1 * ((g (p.1 - p.2) * F p.2 : ℝ) : ℂ)) (volume.prod volume) := by
    refine Integrable.bdd_mul (c := 1) hint.ofReal ?_ ?_ 
    · exact ((Torus.continuous_mode (-n)).comp continuous_fst).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun p => (Torus.norm_mode _ _).le
  have h1 : ∀ x, Torus.mode (-n) x * (cv g F x : ℂ) =
      ∫ y, Torus.mode (-n) x * ((g (x - y) * F y : ℝ) : ℂ) := by
    intro x
    rw [integral_const_mul, integral_complex_ofReal]
    rfl
  simp_rw [h1]
  rw [integral_integral_swap hcpx]
  have h2 : ∀ y, ∫ x, Torus.mode (-n) x * ((g (x - y) * F y : ℝ) : ℂ) =
      (ĝ n : ℂ) * (Torus.mode (-n) y * (F y : ℂ)) := by
    intro y
    have e : ∀ x, Torus.mode (-n) x * ((g (x - y) * F y : ℝ) : ℂ) =
        (Torus.mode (-n) (x - y) * (g (x - y) : ℂ)) * (Torus.mode (-n) y * (F y : ℂ)) := by
      intro x
      rw [mode_sub_pt (-n) x y]
      push_cast
      ring
    simp_rw [e]
    rw [integral_mul_const]
    congr 1
    rw [integral_sub_right_eq_self (fun z => Torus.mode (-n) z * (g z : ℂ)) y]
    exact hcoef n
  simp_rw [h2]
  rw [integral_const_mul]


theorem memLp_cv {g F : Torus d → ℝ} (hg : Measurable g) (hgi : Integrable g)
    (hF : MemLp F 2 volume) :
    MemLp (cv g F) 2 volume ∧
      ∫⁻ x, ‖cv g F x‖ₑ ^ 2 ≤ (∫⁻ y, ‖g y‖ₑ) ^ 2 * ∫⁻ y, ‖F y‖ₑ ^ 2 := by
  have hFm := hF.aestronglyMeasurable
  set F₀ := hFm.mk F with hF₀
  have hF₀m : StronglyMeasurable F₀ := hFm.stronglyMeasurable_mk
  have hFF : F =ᵐ[volume] F₀ := hFm.ae_eq_mk
  rw [cv_congr_ae g hFF]
  have hsm : AEStronglyMeasurable (cv g F₀) volume := by
    have : StronglyMeasurable (fun p : Torus d × Torus d => g (p.1 - p.2) * F₀ p.2) :=
      (hg.comp (measurable_fst.sub measurable_snd)).stronglyMeasurable.mul
        (hF₀m.comp_measurable measurable_snd)
    exact (this.integral_prod_right' (ν := (volume : Measure (Torus d)))).aestronglyMeasurable
  have hbd : ∀ x, ‖cv g F₀ x‖ₑ ≤ ∫⁻ y, ‖g (x - y)‖ₑ * ‖F₀ y‖ₑ := by
    intro x
    refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
    simp [enorm_mul]
  have hle : ∫⁻ x, ‖cv g F₀ x‖ₑ ^ 2 ≤ (∫⁻ y, ‖g y‖ₑ) ^ 2 * ∫⁻ y, ‖F₀ y‖ₑ ^ 2 :=
    calc ∫⁻ x, ‖cv g F₀ x‖ₑ ^ 2 ≤ ∫⁻ x, (∫⁻ y, ‖g (x - y)‖ₑ * ‖F₀ y‖ₑ) ^ 2 :=
          lintegral_mono fun x => by gcongr; exact hbd x
      _ ≤ _ := young_lintegral g F₀ hg hF₀m.measurable
  have hFF2 : ∫⁻ y, ‖F₀ y‖ₑ ^ 2 = ∫⁻ y, ‖F y‖ₑ ^ 2 := by
    refine lintegral_congr_ae ?_
    filter_upwards [hFF] with y hy
    rw [hy]
  rw [hFF2] at hle
  refine ⟨memLp_two_of_lintegral hsm ?_, hle⟩
  refine hle.trans_lt ?_
  have hN : ∫⁻ y, ‖g y‖ₑ < ∞ := hgi.hasFiniteIntegral
  exact ENNReal.mul_lt_top (ENNReal.pow_lt_top hN) (lintegral_of_memLp_two hF)

theorem cosCoeff_cv {g F : Torus d → ℝ} (hg : Integrable g) (hF : Integrable F)
    (hG : Integrable (cv g F))
    (ĝ : Lattice d → ℝ) (hcoef : ∀ n, ∫ x, Torus.mode (-n) x * (g x : ℂ) = (ĝ n : ℂ))
    (n : Lattice d) :
    Torus.cosCoeff (cv g F) n = ĝ n * Torus.cosCoeff F n ∧
      Torus.sinCoeff (cv g F) n = ĝ n * Torus.sinCoeff F n := by
  have h := fourier_cv hg hF ĝ hcoef n
  rw [Torus.integral_mode_mul_real hG, Torus.integral_mode_mul_real hF] at h
  have h1 := congrArg Complex.re h
  have h2 := congrArg Complex.im h
  simp at h1 h2
  exact ⟨h1, h2⟩

theorem hasSum_bilin {φ ψ : Torus d → ℝ} (hφ : MemLp φ 2 volume) (hψ : MemLp ψ 2 volume) :
    HasSum (fun n : Lattice d => Torus.cosCoeff φ n * Torus.cosCoeff ψ n +
      Torus.sinCoeff φ n * Torus.sinCoeff ψ n) (∫ x, φ x * ψ x) := by
  have hφ1 : Integrable φ := hφ.integrable one_le_two
  have hψ1 : Integrable ψ := hψ.integrable one_le_two
  have hp := Torus.hasSum_sq_coeff (hφ.add hψ)
  have hm := Torus.hasSum_sq_coeff (hφ.sub hψ)
  have hcos_add : ∀ n, Torus.cosCoeff (fun x => (φ + ψ) x) n =
      Torus.cosCoeff φ n + Torus.cosCoeff ψ n := by
    intro n
    unfold Torus.cosCoeff
    simp only [Pi.add_apply, mul_add]
    exact integral_add (Torus.integrable_cosMode_mul n hφ1) (Torus.integrable_cosMode_mul n hψ1)
  have hsin_add : ∀ n, Torus.sinCoeff (fun x => (φ + ψ) x) n =
      Torus.sinCoeff φ n + Torus.sinCoeff ψ n := by
    intro n
    unfold Torus.sinCoeff
    simp only [Pi.add_apply, mul_add]
    exact integral_add (Torus.integrable_sinMode_mul n hφ1) (Torus.integrable_sinMode_mul n hψ1)
  have hcos_sub : ∀ n, Torus.cosCoeff (fun x => (φ - ψ) x) n =
      Torus.cosCoeff φ n - Torus.cosCoeff ψ n := by
    intro n
    unfold Torus.cosCoeff
    simp only [Pi.sub_apply, mul_sub]
    exact integral_sub (Torus.integrable_cosMode_mul n hφ1) (Torus.integrable_cosMode_mul n hψ1)
  have hsin_sub : ∀ n, Torus.sinCoeff (fun x => (φ - ψ) x) n =
      Torus.sinCoeff φ n - Torus.sinCoeff ψ n := by
    intro n
    unfold Torus.sinCoeff
    simp only [Pi.sub_apply, mul_sub]
    exact integral_sub (Torus.integrable_sinMode_mul n hφ1) (Torus.integrable_sinMode_mul n hψ1)
  have hd := (hp.sub hm).div_const 4
  have hi1 : Integrable (fun x => (φ x + ψ x) ^ 2) := by
    simpa using (hφ.add hψ).integrable_sq
  have hi2 : Integrable (fun x => (φ x - ψ x) ^ 2) := by
    simpa using (hφ.sub hψ).integrable_sq
  have hint : ((∫ x, (φ + ψ) x ^ 2) - ∫ x, (φ - ψ) x ^ 2) / 4 = ∫ x, φ x * ψ x := by
    simp only [Pi.add_apply, Pi.sub_apply]
    rw [← integral_sub hi1 hi2, ← integral_div]
    congr 1
    funext x
    ring
  rw [← hint]
  convert hd using 1
  funext n
  rw [hcos_add, hsin_add, hcos_sub, hsin_sub]
  ring

/-- The quadratic form of convolution with `g` in terms of Fourier coefficients. -/
theorem hasSum_cv_form {g F F' : Torus d → ℝ} (hg : Measurable g) (hgi : Integrable g)
    (ĝ : Lattice d → ℝ) (hcoef : ∀ n, ∫ x, Torus.mode (-n) x * (g x : ℂ) = (ĝ n : ℂ))
    (hF : MemLp F 2 volume) (hF' : MemLp F' 2 volume) :
    HasSum (fun n : Lattice d => ĝ n * (Torus.cosCoeff F n * Torus.cosCoeff F' n +
      Torus.sinCoeff F n * Torus.sinCoeff F' n)) (∫ x, cv g F x * F' x) := by
  have hG := (memLp_cv hg hgi hF).1
  have h := hasSum_bilin hG hF'
  convert h using 2 with n
  obtain ⟨h1, h2⟩ := cosCoeff_cv hgi (hF.integrable one_le_two) (hG.integrable one_le_two) ĝ hcoef n
  rw [h1, h2]
  ring

theorem cv_form_nonneg {g F : Torus d → ℝ} (hg : Measurable g) (hgi : Integrable g)
    (ĝ : Lattice d → ℝ) (hĝ : ∀ n, 0 ≤ ĝ n)
    (hcoef : ∀ n, ∫ x, Torus.mode (-n) x * (g x : ℂ) = (ĝ n : ℂ))
    (hF : MemLp F 2 volume) : 0 ≤ ∫ x, cv g F x * F x := by
  refine (hasSum_cv_form hg hgi ĝ hcoef hF hF).nonneg fun n => ?_
  exact mul_nonneg (hĝ n) (add_nonneg (mul_self_nonneg _) (mul_self_nonneg _))

theorem cv_form_symm {g F F' : Torus d → ℝ} (hg : Measurable g) (hgi : Integrable g)
    (ĝ : Lattice d → ℝ) (hcoef : ∀ n, ∫ x, Torus.mode (-n) x * (g x : ℂ) = (ĝ n : ℂ))
    (hF : MemLp F 2 volume) (hF' : MemLp F' 2 volume) :
    ∫ x, cv g F x * F' x = ∫ x, cv g F' x * F x := by
  refine (hasSum_cv_form hg hgi ĝ hcoef hF hF').unique ?_
  have := hasSum_cv_form hg hgi ĝ hcoef hF' hF
  convert this using 2 with n
  ring

/-! ### Measures with bounded density -/

section Density

variable {ρ : Torus d → ℝ} {Λ : ℝ}

theorem measurable_ofReal_rho (hρ : IsProbDensity ρ) :
    Measurable fun x => ENNReal.ofReal (ρ x) := ENNReal.measurable_ofReal.comp hρ.measurable

theorem integrable_rho (hρ : IsProbDensity ρ) : Integrable ρ := by
  by_contra h
  have := hρ.integral_one
  rw [integral_undef h] at this
  exact zero_ne_one this

theorem integral_dens (hρ : IsProbDensity ρ) (h : Torus d → ℝ) :
    ∫ x, h x ∂(withDensityReal ρ) = ∫ x, ρ x * h x := by
  unfold withDensityReal
  rw [integral_withDensity_eq_integral_toReal_smul (measurable_ofReal_rho hρ)
    (ae_of_all _ fun x => ENNReal.ofReal_lt_top) h]
  simp [ENNReal.toReal_ofReal (hρ.nonneg _)]

theorem isProbabilityMeasure_dens (hρ : IsProbDensity ρ) :
    IsProbabilityMeasure (withDensityReal ρ) := by
  refine ⟨?_⟩
  unfold withDensityReal
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_rho hρ)
      (Filter.Eventually.of_forall hρ.nonneg), hρ.integral_one]
  simp

theorem dens_le (Λ : ℝ) (hΛ : ∀ x, ρ x ≤ Λ) :
    withDensityReal ρ ≤ ENNReal.ofReal Λ • (volume : Measure (Torus d)) := by
  unfold withDensityReal
  rw [← withDensity_const]
  exact withDensity_mono (Filter.Eventually.of_forall fun x => ENNReal.ofReal_le_ofReal (hΛ x))

theorem dens_ac (ρ : Torus d → ℝ) : withDensityReal ρ ≪ (volume : Measure (Torus d)) :=
  withDensity_absolutelyContinuous _ _

theorem ae_vol_of_ae_dens (hρ : IsProbDensity ρ) {u v : Torus d → ℝ}
    (h : u =ᵐ[withDensityReal ρ] v) :
    (fun x => ρ x * u x) =ᵐ[volume] (fun x => ρ x * v x) := by
  have := (ae_withDensity_iff (measurable_ofReal_rho hρ)).1 h
  filter_upwards [this] with x hx
  by_cases h0 : ρ x = 0
  · simp [h0]
  · rw [hx (by simpa [ENNReal.ofReal_eq_zero, not_le] using lt_of_le_of_ne (hρ.nonneg x) (Ne.symm h0))]

theorem memLp_dens_of_vol (hΛ : ∀ x, ρ x ≤ Λ) {F : Torus d → ℝ}
    (hF : MemLp F 2 volume) :
    MemLp F 2 (withDensityReal ρ) ∧
      ∫⁻ x, ‖F x‖ₑ ^ 2 ∂(withDensityReal ρ) ≤ ENNReal.ofReal Λ * ∫⁻ x, ‖F x‖ₑ ^ 2 := by
  have hle : ∫⁻ x, ‖F x‖ₑ ^ 2 ∂(withDensityReal ρ) ≤ ENNReal.ofReal Λ * ∫⁻ x, ‖F x‖ₑ ^ 2 := by
    calc ∫⁻ x, ‖F x‖ₑ ^ 2 ∂(withDensityReal ρ)
        ≤ ∫⁻ x, ‖F x‖ₑ ^ 2 ∂(ENNReal.ofReal Λ • (volume : Measure (Torus d))) :=
          lintegral_mono' (dens_le Λ hΛ) le_rfl
      _ = _ := by rw [lintegral_smul_measure, smul_eq_mul]
  refine ⟨memLp_two_of_lintegral (hF.aestronglyMeasurable.mono_ac (dens_ac ρ)) ?_, hle⟩
  exact hle.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lintegral_of_memLp_two hF))

theorem rho_mul_memLp (hρ : IsProbDensity ρ) (hΛ : ∀ x, ρ x ≤ Λ) {f : Torus d → ℝ}
    (hf : MemLp f 2 (withDensityReal ρ)) :
    MemLp (fun x => ρ x * f x) 2 volume ∧
      ∫⁻ x, ‖ρ x * f x‖ₑ ^ 2 ≤
        ENNReal.ofReal Λ * ∫⁻ x, ‖f x‖ₑ ^ 2 ∂(withDensityReal ρ) := by
  have hfm := hf.aestronglyMeasurable
  set f₀ := hfm.mk f with hf₀def
  have hf₀ : StronglyMeasurable f₀ := hfm.stronglyMeasurable_mk
  have hff : f =ᵐ[withDensityReal ρ] f₀ := hfm.ae_eq_mk
  have hae := ae_vol_of_ae_dens hρ hff
  have key : ∫⁻ x, ‖ρ x * f₀ x‖ₑ ^ 2 ≤
      ENNReal.ofReal Λ * ∫⁻ x, ‖f₀ x‖ₑ ^ 2 ∂(withDensityReal ρ) := by
    unfold withDensityReal
    rw [lintegral_withDensity_eq_lintegral_mul _ (measurable_ofReal_rho hρ)
      (hf₀.measurable.enorm.pow_const 2), ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun x => ?_
    simp only [Pi.mul_apply, enorm_mul, mul_pow]
    rw [Real.enorm_of_nonneg (hρ.nonneg x)]
    rw [pow_two, mul_assoc]
    gcongr
    exact hΛ x
  have e1 : ∫⁻ x, ‖ρ x * f x‖ₑ ^ 2 = ∫⁻ x, ‖ρ x * f₀ x‖ₑ ^ 2 := by
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with x hx
    rw [hx]
  have e2 : ∫⁻ x, ‖f₀ x‖ₑ ^ 2 ∂(withDensityReal ρ) = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂(withDensityReal ρ) := by
    refine lintegral_congr_ae ?_
    filter_upwards [hff] with x hx
    rw [hx]
  rw [e2] at key
  rw [e1]
  have hsm : AEStronglyMeasurable (fun x => ρ x * f x) volume := by
    refine AEStronglyMeasurable.congr ?_ hae.symm
    exact hρ.measurable.aestronglyMeasurable.mul hf₀.aestronglyMeasurable
  refine ⟨memLp_two_of_lintegral hsm ?_, key⟩
  rw [e1]
  exact key.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lintegral_of_memLp_two hf))

/-! #### The operator `f ↦ ∫ g(x-y) f(y) dμ(y)` -/

/-- `K̃_μ f (x) = ∫ g(x-y) f(y) dμ(y)` (the operator `K_μ` before centering). -/
def Kt (g : Torus d → ℝ) (μ : Measure (Torus d)) (f : Torus d → ℝ) (x : Torus d) : ℝ :=
  ∫ y, g (x - y) * f y ∂μ

theorem Kt_eq_cv (hρ : IsProbDensity ρ) (g f : Torus d → ℝ) :
    Kt g (withDensityReal ρ) f = cv g (fun y => ρ y * f y) := by
  funext x
  unfold Kt cv
  rw [integral_dens hρ]
  congr 1
  funext y
  ring

theorem Kt_congr {μ : Measure (Torus d)} (g : Torus d → ℝ) {f f' : Torus d → ℝ}
    (h : f =ᵐ[μ] f') : Kt g μ f = Kt g μ f' := by
  funext x
  unfold Kt
  refine integral_congr_ae ?_
  filter_upwards [h] with y hy
  rw [hy]

theorem memLp_Kt (hρ : IsProbDensity ρ) (hΛ : ∀ x, ρ x ≤ Λ) {g : Torus d → ℝ}
    (hg : Measurable g) (hgi : Integrable g) {f : Torus d → ℝ}
    (hf : MemLp f 2 (withDensityReal ρ)) :
    MemLp (Kt g (withDensityReal ρ) f) 2 (withDensityReal ρ) ∧
      ∫⁻ x, ‖Kt g (withDensityReal ρ) f x‖ₑ ^ 2 ∂(withDensityReal ρ) ≤
        (ENNReal.ofReal Λ * ∫⁻ y, ‖g y‖ₑ) ^ 2 * ∫⁻ x, ‖f x‖ₑ ^ 2 ∂(withDensityReal ρ) := by
  obtain ⟨h1, h2⟩ := rho_mul_memLp hρ hΛ hf
  obtain ⟨h3, h4⟩ := memLp_cv hg hgi h1
  rw [Kt_eq_cv hρ]
  obtain ⟨h5, h6⟩ := memLp_dens_of_vol hΛ h3
  refine ⟨h5, h6.trans ?_⟩
  calc ENNReal.ofReal Λ * ∫⁻ x, ‖cv g (fun y => ρ y * f y) x‖ₑ ^ 2
      ≤ ENNReal.ofReal Λ * ((∫⁻ y, ‖g y‖ₑ) ^ 2 * ∫⁻ y, ‖ρ y * f y‖ₑ ^ 2) := by gcongr
    _ ≤ ENNReal.ofReal Λ * ((∫⁻ y, ‖g y‖ₑ) ^ 2 *
          (ENNReal.ofReal Λ * ∫⁻ x, ‖f x‖ₑ ^ 2 ∂(withDensityReal ρ))) := by gcongr
    _ = _ := by ring

theorem Kt_form (hρ : IsProbDensity ρ) (g f f' : Torus d → ℝ) :
    ∫ x, Kt g (withDensityReal ρ) f x * f' x ∂(withDensityReal ρ) =
      ∫ x, cv g (fun y => ρ y * f y) x * (ρ x * f' x) := by
  rw [integral_dens hρ, Kt_eq_cv hρ]
  congr 1
  funext x
  ring

theorem Kt_form_symm (hρ : IsProbDensity ρ) (hΛ : ∀ x, ρ x ≤ Λ) {g : Torus d → ℝ}
    (hg : Measurable g) (hgi : Integrable g)
    (ĝ : Lattice d → ℝ) (hcoef : ∀ n, ∫ x, Torus.mode (-n) x * (g x : ℂ) = (ĝ n : ℂ))
    {f f' : Torus d → ℝ} (hf : MemLp f 2 (withDensityReal ρ))
    (hf' : MemLp f' 2 (withDensityReal ρ)) :
    ∫ x, Kt g (withDensityReal ρ) f x * f' x ∂(withDensityReal ρ) =
      ∫ x, Kt g (withDensityReal ρ) f' x * f x ∂(withDensityReal ρ) := by
  rw [Kt_form hρ, Kt_form hρ]
  exact cv_form_symm hg hgi ĝ hcoef (rho_mul_memLp hρ hΛ hf).1 (rho_mul_memLp hρ hΛ hf').1

theorem Kt_form_nonneg (hρ : IsProbDensity ρ) (hΛ : ∀ x, ρ x ≤ Λ) {g : Torus d → ℝ}
    (hg : Measurable g) (hgi : Integrable g)
    (ĝ : Lattice d → ℝ) (hĝ : ∀ n, 0 ≤ ĝ n)
    (hcoef : ∀ n, ∫ x, Torus.mode (-n) x * (g x : ℂ) = (ĝ n : ℂ))
    {f : Torus d → ℝ} (hf : MemLp f 2 (withDensityReal ρ)) :
    0 ≤ ∫ x, Kt g (withDensityReal ρ) f x * f x ∂(withDensityReal ρ) := by
  rw [Kt_form hρ]
  exact cv_form_nonneg hg hgi ĝ hĝ hcoef (rho_mul_memLp hρ hΛ hf).1

theorem cv_add_ae {g F₁ F₂ : Torus d → ℝ} (hg : Integrable g) (h1 : Integrable F₁)
    (h2 : Integrable F₂) :
    cv g (fun y => F₁ y + F₂ y) =ᵐ[volume] fun x => cv g F₁ x + cv g F₂ x := by
  have e1 := Integrable.ae_convolution_exists (ContinuousLinearMap.mul ℝ ℝ) h1 hg
  have e2 := Integrable.ae_convolution_exists (ContinuousLinearMap.mul ℝ ℝ) h2 hg
  filter_upwards [e1, e2] with x hx1 hx2
  have i1 : Integrable (fun y => g (x - y) * F₁ y) := by
    refine hx1.congr (Filter.Eventually.of_forall fun y => ?_)
    simp [mul_comm]
  have i2 : Integrable (fun y => g (x - y) * F₂ y) := by
    refine hx2.congr (Filter.Eventually.of_forall fun y => ?_)
    simp [mul_comm]
  unfold cv
  rw [← integral_add i1 i2]
  congr 1
  funext y
  ring

theorem Kt_add_ae (hρ : IsProbDensity ρ) (hΛ : ∀ x, ρ x ≤ Λ) {g : Torus d → ℝ}
    (hgi : Integrable g) {f₁ f₂ : Torus d → ℝ} (h1 : MemLp f₁ 2 (withDensityReal ρ))
    (h2 : MemLp f₂ 2 (withDensityReal ρ)) :
    Kt g (withDensityReal ρ) (fun y => f₁ y + f₂ y) =ᵐ[withDensityReal ρ]
      fun x => Kt g (withDensityReal ρ) f₁ x + Kt g (withDensityReal ρ) f₂ x := by
  have := cv_add_ae hgi ((rho_mul_memLp hρ hΛ h1).1.integrable one_le_two)
    ((rho_mul_memLp hρ hΛ h2).1.integrable one_le_two)
  refine (dens_ac ρ).ae_le ?_
  rw [Kt_eq_cv hρ, Kt_eq_cv hρ, Kt_eq_cv hρ]
  filter_upwards [this] with x hx
  simp only [mul_add]
  exact hx

theorem Kt_smul (g : Torus d → ℝ) (μ : Measure (Torus d)) (c : ℝ) (f : Torus d → ℝ) :
    Kt g μ (fun y => c * f y) = fun x => c * Kt g μ f x := by
  funext x
  unfold Kt
  rw [← integral_const_mul]
  congr 1
  funext y
  ring

end Density

/-! ### Abstract Hilbert space part -/

section Abstract

open InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Lax–Milgram for a coercive operator: it is bijective. -/
theorem bijective_of_coercive (T : H →L[ℝ] H) (h : ∀ u, ‖u‖ * ‖u‖ ≤ inner ℝ (T u) u) :
    Function.Bijective T := by
  let B : H →L[ℝ] H →L[ℝ] ℝ := (innerSL ℝ).comp T
  have hB : ∀ v w, B v w = inner ℝ (T v) w := fun v w => rfl
  have hc : IsCoercive B := ⟨1, one_pos, fun u => by rw [hB]; simpa using h u⟩
  have hT : ∀ v, continuousLinearMapOfBilin B v = T v := by
    intro v
    refine ext_inner_right ℝ fun w => ?_
    rw [continuousLinearMapOfBilin_apply, hB]
  have : (continuousLinearMapOfBilin B) = T := ContinuousLinearMap.ext hT
  rw [← this]
  exact (hc.continuousLinearEquivOfBilin).bijective

/-- The orthogonal projection onto `{one}ᗮ`, `P f = f - ⟪one, f⟫ one`. -/
def projL (one : H) : H →L[ℝ] H :=
  ContinuousLinearMap.id ℝ H - (innerSL ℝ one).smulRight one

omit [CompleteSpace H] in
theorem projL_apply (one f : H) : projL one f = f - inner ℝ one f • one := by
  simp [projL]

omit [CompleteSpace H] in
theorem inner_one_projL {one : H} (hone : ‖one‖ = 1) (f : H) : inner ℝ one (projL one f) = 0 := by
  rw [projL_apply, inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq, hone]
  ring

omit [CompleteSpace H] in
theorem projL_projL {one : H} (hone : ‖one‖ = 1) (f : H) : projL one (projL one f) = projL one f := by
  rw [projL_apply (f := projL one f), inner_one_projL hone, zero_smul, sub_zero]

omit [CompleteSpace H] in
theorem projL_eq_self_iff {one : H} (hone : ‖one‖ = 1) {f : H} :
    projL one f = f ↔ inner ℝ one f = 0 := by
  rw [projL_apply]
  constructor
  · intro h
    have h2 : inner ℝ one f • one = 0 := by
      have := congrArg (fun z => f - z) h
      simpa using this
    rcases smul_eq_zero.1 h2 with h3 | h3
    · exact h3
    · rw [h3] at hone; simp at hone
  · intro h
    simp [h]

omit [CompleteSpace H] in
theorem inner_projL_left (one f f' : H) : inner ℝ (projL one f) f' = inner ℝ f (projL one f') := by
  rw [projL_apply, projL_apply, inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right]
  simp only [conj_trivial]
  rw [real_inner_comm one f]
  ring

/-- `T = I + β P K P`. -/
def Top (one : H) (K : H →L[ℝ] H) (β : ℝ) : H →L[ℝ] H :=
  ContinuousLinearMap.id ℝ H + β • ((projL one).comp (K.comp (projL one)))

omit [CompleteSpace H] in
theorem Top_apply (one : H) (K : H →L[ℝ] H) (β : ℝ) (f : H) :
    Top one K β f = f + β • projL one (K (projL one f)) := by
  simp [Top]

omit [CompleteSpace H] in
theorem Top_coercive {one : H} {K : H →L[ℝ] H}
    (hK : ∀ u, 0 ≤ inner ℝ (K u) u) {β : ℝ} (hβ : 0 ≤ β) (u : H) :
    ‖u‖ * ‖u‖ ≤ inner ℝ (Top one K β u) u := by
  rw [Top_apply, inner_add_left, inner_smul_left, inner_projL_left, real_inner_self_eq_norm_sq]
  have := hK (projL one u)
  simp only [conj_trivial]
  nlinarith [mul_nonneg hβ this]

end Abstract

/-! ### The concrete operators on `L²(μ)` -/

section Concrete

open InnerProductSpace

variable {g ρ : Torus d → ℝ} {Λ : ℝ}

/-- Standing hypotheses of the response equation. -/
structure Setup (g ρ : Torus d → ℝ) (Λ : ℝ) : Prop where
  hρ : IsProbDensity ρ
  hΛ : ∀ x, ρ x ≤ Λ
  hg : Measurable g
  hgi : Integrable g
  hĝ : ∃ ĝ : Lattice d → ℝ, (∀ n, 0 ≤ ĝ n) ∧
    ∀ n, ∫ x, Torus.mode (-n) x * (g x : ℂ) = (ĝ n : ℂ)

/-- The constant function `1` as an element of `L²(μ)`. -/
def oneL (hρ : IsProbDensity ρ) : Lp ℝ 2 (withDensityReal ρ) :=
  haveI := isProbabilityMeasure_dens hρ
  (memLp_const (1 : ℝ)).toLp (fun _ => (1 : ℝ))

theorem oneL_coe (hρ : IsProbDensity ρ) :
    (oneL hρ : Torus d → ℝ) =ᵐ[withDensityReal ρ] fun _ => (1 : ℝ) := by
  have := isProbabilityMeasure_dens hρ
  exact MemLp.coeFn_toLp _

theorem inner_oneL (hρ : IsProbDensity ρ) (f : Lp ℝ 2 (withDensityReal ρ)) :
    inner ℝ (oneL hρ) f = ∫ x, f x ∂(withDensityReal ρ) := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [oneL_coe hρ] with x hx
  simp [hx]

theorem norm_oneL (hρ : IsProbDensity ρ) : ‖oneL hρ‖ = 1 := by
  have := isProbabilityMeasure_dens hρ
  have h := inner_oneL hρ (oneL hρ)
  rw [real_inner_self_eq_norm_sq] at h
  have h2 : ∫ x, (oneL hρ : Torus d → ℝ) x ∂(withDensityReal ρ) = 1 := by
    rw [integral_congr_ae (oneL_coe hρ)]
    simp
  rw [h2] at h
  have : 0 ≤ ‖oneL hρ‖ := norm_nonneg _
  nlinarith

theorem projL_coe (hρ : IsProbDensity ρ) (f : Lp ℝ 2 (withDensityReal ρ)) :
    (projL (oneL hρ) f : Torus d → ℝ) =ᵐ[withDensityReal ρ]
      fun x => f x - ∫ y, f y ∂(withDensityReal ρ) := by
  rw [projL_apply, inner_oneL]
  filter_upwards [Lp.coeFn_sub f ((∫ y, f y ∂(withDensityReal ρ)) • oneL hρ),
    Lp.coeFn_smul (∫ y, f y ∂(withDensityReal ρ)) (oneL hρ), oneL_coe hρ] with x h1 h2 h3
  rw [h1]
  simp only [Pi.sub_apply]
  rw [h2]
  simp [h3]

variable (S : Setup g ρ Λ)

include S in
/-- `f ↦ K̃_μ f` as a map `L²(μ) → L²(μ)` (not yet known to be linear). -/
def KLfun (f : Lp ℝ 2 (withDensityReal ρ)) : Lp ℝ 2 (withDensityReal ρ) :=
  (memLp_Kt S.hρ S.hΛ S.hg S.hgi (Lp.memLp f)).1.toLp (Kt g (withDensityReal ρ) f)

theorem KLfun_coe (f : Lp ℝ 2 (withDensityReal ρ)) :
    (KLfun S f : Torus d → ℝ) =ᵐ[withDensityReal ρ] Kt g (withDensityReal ρ) f :=
  MemLp.coeFn_toLp _

theorem KLfun_add (f f' : Lp ℝ 2 (withDensityReal ρ)) :
    KLfun S (f + f') = KLfun S f + KLfun S f' := by
  apply Lp.ext
  have h1 := Kt_add_ae S.hρ S.hΛ S.hgi (Lp.memLp f) (Lp.memLp f')
  have h2 := Kt_congr (μ := withDensityReal ρ) g (Lp.coeFn_add f f')
  filter_upwards [KLfun_coe S (f + f'), Lp.coeFn_add (KLfun S f) (KLfun S f'), KLfun_coe S f,
    KLfun_coe S f', h1] with x a b c e h
  rw [a, b]
  simp only [Pi.add_apply]
  rw [c, e]
  have := congrFun h2 x
  rw [this]
  exact h

theorem KLfun_smul (c : ℝ) (f : Lp ℝ 2 (withDensityReal ρ)) :
    KLfun S (c • f) = c • KLfun S f := by
  apply Lp.ext
  have h2 := Kt_congr (μ := withDensityReal ρ) g (Lp.coeFn_smul c f)
  have h3 := Kt_smul g (withDensityReal ρ) c f
  filter_upwards [KLfun_coe S (c • f), Lp.coeFn_smul c (KLfun S f), KLfun_coe S f] with x a b e
  rw [a, b]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [e]
  have := congrFun h2 x
  rw [this]
  have h4 := congrFun h3 x
  exact h4

/-- The norm bound constant of `K̃_μ`. -/
def Cnorm (g : Torus d → ℝ) (Λ : ℝ) : ℝ := (ENNReal.ofReal Λ * ∫⁻ y, ‖g y‖ₑ).toReal

theorem norm_KLfun_le (f : Lp ℝ 2 (withDensityReal ρ)) :
    ‖KLfun S f‖ ≤ Cnorm g Λ * ‖f‖ := by
  have hN : ∫⁻ y, ‖g y‖ₑ < ∞ := S.hgi.hasFiniteIntegral
  have hC : ENNReal.ofReal Λ * ∫⁻ y, ‖g y‖ₑ ≠ ∞ :=
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hN).ne
  obtain ⟨h1, h2⟩ := memLp_Kt S.hρ S.hΛ S.hg S.hgi (Lp.memLp f)
  have hfm := (Lp.memLp f).aestronglyMeasurable
  have hsq : eLpNorm (Kt g (withDensityReal ρ) f) 2 (withDensityReal ρ) ≤
      (ENNReal.ofReal Λ * ∫⁻ y, ‖g y‖ₑ) * eLpNorm (f : Torus d → ℝ) 2 (withDensityReal ρ) := by
    refine (ENNReal.pow_le_pow_left_iff two_ne_zero).1 ?_
    rw [mul_pow, eLpNorm_two_sq h1.aestronglyMeasurable, eLpNorm_two_sq hfm]
    exact h2
  unfold KLfun Cnorm
  rw [Lp.norm_toLp, Lp.norm_def]
  calc (eLpNorm (Kt g (withDensityReal ρ) f) 2 (withDensityReal ρ)).toReal
      ≤ ((ENNReal.ofReal Λ * ∫⁻ y, ‖g y‖ₑ) *
          eLpNorm (f : Torus d → ℝ) 2 (withDensityReal ρ)).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top hC (Lp.memLp f).ne) hsq
    _ = _ := ENNReal.toReal_mul

/-- `K̃_μ` as a bounded operator on `L²(μ)`. -/
def KL : Lp ℝ 2 (withDensityReal ρ) →L[ℝ] Lp ℝ 2 (withDensityReal ρ) :=
  LinearMap.mkContinuous
    { toFun := KLfun S
      map_add' := KLfun_add S
      map_smul' := fun c f => by simpa using KLfun_smul S c f }
    (Cnorm g Λ) (norm_KLfun_le S)

theorem KL_apply (f : Lp ℝ 2 (withDensityReal ρ)) : KL S f = KLfun S f := rfl

theorem inner_KL_nonneg (u : Lp ℝ 2 (withDensityReal ρ)) : 0 ≤ inner ℝ (KL S u) u := by
  obtain ⟨ĝ, hĝ, hcoef⟩ := S.hĝ
  rw [L2.inner_def]
  have : ∫ x, inner ℝ ((KL S u : Lp ℝ 2 (withDensityReal ρ)) x) (u x) ∂(withDensityReal ρ) =
      ∫ x, Kt g (withDensityReal ρ) u x * u x ∂(withDensityReal ρ) := by
    refine integral_congr_ae ?_
    filter_upwards [KLfun_coe S u] with x hx
    rw [KL_apply, hx]
    simp [mul_comm]
  rw [this]
  exact Kt_form_nonneg S.hρ S.hΛ S.hg S.hgi ĝ hĝ hcoef (Lp.memLp u)

/-- The response equation, in terms of `Kt` (this is `IsResponse` of `HRS.Kernel.Riesz`). -/
def RespEq (g : Torus d → ℝ) (μ : Measure (Torus d)) (β : ℝ) (ψ h : Torus d → ℝ) : Prop :=
  MemLp h 2 μ ∧ ∫ x, h x ∂μ = 0 ∧
    ∀ᵐ x ∂μ, h x + β * (Kt g μ h x - ∫ y, Kt g μ h y ∂μ) = ψ x - ∫ y, ψ y ∂μ

theorem coe_Top (β : ℝ) {u : Lp ℝ 2 (withDensityReal ρ)} (hPu : projL (oneL S.hρ) u = u) :
    (Top (oneL S.hρ) (KL S) β u : Torus d → ℝ) =ᵐ[withDensityReal ρ] fun x =>
      u x + β * (Kt g (withDensityReal ρ) u x - ∫ y, Kt g (withDensityReal ρ) u y ∂(withDensityReal ρ)) := by
  rw [Top_apply, hPu]
  have hint : ∫ y, (KL S u : Torus d → ℝ) y ∂(withDensityReal ρ) =
      ∫ y, Kt g (withDensityReal ρ) u y ∂(withDensityReal ρ) :=
    integral_congr_ae (KLfun_coe S u)
  filter_upwards [Lp.coeFn_add u (β • projL (oneL S.hρ) (KL S u)),
    Lp.coeFn_smul β (projL (oneL S.hρ) (KL S u)), projL_coe S.hρ (KL S u), KLfun_coe S u]
    with x h1 h2 h3 h4
  rw [h1]
  simp only [Pi.add_apply]
  rw [h2]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [h3]
  rw [hint]
  have : (KL S u : Torus d → ℝ) x = Kt g (withDensityReal ρ) u x := h4
  rw [this]

theorem respEq_iff (β : ℝ) {ψ h : Torus d → ℝ} (hψ : MemLp ψ 2 (withDensityReal ρ))
    (hh : MemLp h 2 (withDensityReal ρ)) :
    RespEq g (withDensityReal ρ) β ψ h ↔
      (projL (oneL S.hρ) (hh.toLp h) = hh.toLp h ∧
        Top (oneL S.hρ) (KL S) β (hh.toLp h) = projL (oneL S.hρ) (hψ.toLp ψ)) := by
  set u := hh.toLp h with hudef
  set w := hψ.toLp ψ with hwdef
  have hu : (u : Torus d → ℝ) =ᵐ[withDensityReal ρ] h := hh.coeFn_toLp
  have hint : ∫ x, (u : Torus d → ℝ) x ∂(withDensityReal ρ) = ∫ x, h x ∂(withDensityReal ρ) :=
    integral_congr_ae hu
  have hPu_iff : projL (oneL S.hρ) u = u ↔ ∫ x, h x ∂(withDensityReal ρ) = 0 := by
    rw [projL_eq_self_iff (norm_oneL S.hρ), inner_oneL, hint]
  have hKt : Kt g (withDensityReal ρ) u = Kt g (withDensityReal ρ) h := Kt_congr g hu
  have hwint : ∫ x, (w : Torus d → ℝ) x ∂(withDensityReal ρ) = ∫ x, ψ x ∂(withDensityReal ρ) :=
    integral_congr_ae hψ.coeFn_toLp
  have hw : (projL (oneL S.hρ) w : Torus d → ℝ) =ᵐ[withDensityReal ρ]
      fun x => ψ x - ∫ y, ψ y ∂(withDensityReal ρ) := by
    filter_upwards [projL_coe S.hρ w, hψ.coeFn_toLp] with x h1 h2
    rw [h1, hwint, h2]
  constructor
  · rintro ⟨_, h0, heq⟩
    have hP := hPu_iff.2 h0
    refine ⟨hP, Lp.ext ?_⟩
    filter_upwards [coe_Top S β hP, hw, hu, heq] with x a b c d
    rw [a, b, hKt, c]
    exact d
  · rintro ⟨hP, hT⟩
    refine ⟨hh, hPu_iff.1 hP, ?_⟩
    have hT' : (Top (oneL S.hρ) (KL S) β u : Torus d → ℝ) =ᵐ[withDensityReal ρ]
        (projL (oneL S.hρ) w : Torus d → ℝ) := by rw [hT]
    filter_upwards [coe_Top S β hP, hw, hu, hT'] with x a b c d
    rw [a, hKt, c] at d
    rw [d, b]

include S in
theorem exists_unique_respEq {β : ℝ} (hβ : 0 ≤ β) {ψ : Torus d → ℝ}
    (hψ : MemLp ψ 2 (withDensityReal ρ)) :
    ∃ h, RespEq g (withDensityReal ρ) β ψ h ∧
      ∀ h', RespEq g (withDensityReal ρ) β ψ h' → h' =ᵐ[withDensityReal ρ] h := by
  have hbij := bijective_of_coercive (Top (oneL S.hρ) (KL S) β)
    (Top_coercive (one := oneL S.hρ) (inner_KL_nonneg S) hβ)
  set w := hψ.toLp ψ with hwdef
  obtain ⟨u, hu⟩ := hbij.2 (projL (oneL S.hρ) w)
  have hPu : projL (oneL S.hρ) u = u := by
    have h1 := Top_apply (oneL S.hρ) (KL S) β u
    rw [hu] at h1
    have h2 : u = projL (oneL S.hρ) w - β • projL (oneL S.hρ) (KL S (projL (oneL S.hρ) u)) := by
      rw [h1]; abel
    conv_lhs => rw [h2]
    rw [map_sub, map_smul, projL_projL (norm_oneL S.hρ), projL_projL (norm_oneL S.hρ)]
    exact h2.symm
  refine ⟨(u : Torus d → ℝ), ?_, ?_⟩
  · rw [respEq_iff S β hψ (Lp.memLp u), Lp.toLp_coeFn]
    exact ⟨hPu, hu⟩
  · intro h' hh'
    have hmem := hh'.1
    rw [respEq_iff S β hψ hmem] at hh'
    obtain ⟨_, hT'⟩ := hh'
    have : hmem.toLp h' = u := hbij.1 (hT'.trans hu.symm)
    have h5 := hmem.coeFn_toLp
    rw [this] at h5
    exact h5.symm

include S in
theorem susc_bounds {β : ℝ} (hβ : 0 ≤ β) :
    ∃ c : ℝ, 0 < c ∧ ∀ (φ h : Torus d → ℝ), MemLp φ 2 (withDensityReal ρ) →
      RespEq g (withDensityReal ρ) β φ h →
      c * ∫ x, (φ x - ∫ y, φ y ∂(withDensityReal ρ)) * (φ x - ∫ y, φ y ∂(withDensityReal ρ))
          ∂(withDensityReal ρ) ≤
        ∫ x, (φ x - ∫ y, φ y ∂(withDensityReal ρ)) * h x ∂(withDensityReal ρ) ∧
      ∫ x, (φ x - ∫ y, φ y ∂(withDensityReal ρ)) * h x ∂(withDensityReal ρ) ≤
        ∫ x, (φ x - ∫ y, φ y ∂(withDensityReal ρ)) * (φ x - ∫ y, φ y ∂(withDensityReal ρ))
          ∂(withDensityReal ρ) := by
  set T := Top (oneL S.hρ) (KL S) β with hT
  set t := ‖T‖ with ht
  have ht0 : 0 ≤ t := norm_nonneg _
  refine ⟨1 / (1 + t) ^ 2, by positivity, fun φ h hφ hresp => ?_⟩
  have hmem := hresp.1
  have hiff := (respEq_iff S β hφ hmem).1 hresp
  obtain ⟨_, hTu⟩ := hiff
  set u := hmem.toLp h with hudef
  set w := hφ.toLp φ with hwdef
  set Pw := projL (oneL S.hρ) w with hPw
  have hu : (u : Torus d → ℝ) =ᵐ[withDensityReal ρ] h := hmem.coeFn_toLp
  have hwint : ∫ x, (w : Torus d → ℝ) x ∂(withDensityReal ρ) = ∫ x, φ x ∂(withDensityReal ρ) :=
    integral_congr_ae hφ.coeFn_toLp
  have hPwc : (Pw : Torus d → ℝ) =ᵐ[withDensityReal ρ]
      fun x => φ x - ∫ y, φ y ∂(withDensityReal ρ) := by
    filter_upwards [projL_coe S.hρ w, hφ.coeFn_toLp] with x h1 h2
    rw [h1, hwint, h2]
  have e1 : ∫ x, (φ x - ∫ y, φ y ∂(withDensityReal ρ)) * h x ∂(withDensityReal ρ) =
      inner ℝ Pw u := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hPwc, hu] with x h1 h2
    simp [h1, h2, mul_comm]
  have e2 : ∫ x, (φ x - ∫ y, φ y ∂(withDensityReal ρ)) * (φ x - ∫ y, φ y ∂(withDensityReal ρ))
      ∂(withDensityReal ρ) = ‖Pw‖ * ‖Pw‖ := by
    rw [← real_inner_self_eq_norm_mul_norm, L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hPwc] with x h1
    simp [h1, sq]
  rw [e1, e2]
  have hcoer := Top_coercive (one := oneL S.hρ) (inner_KL_nonneg S) hβ u
  rw [← hT, hTu] at hcoer
  have hb : ‖Pw‖ ≤ t * ‖u‖ := by
    rw [← hTu]; exact T.le_opNorm u
  have hcs : inner ℝ Pw u ≤ ‖Pw‖ * ‖u‖ := real_inner_le_norm _ _
  have ha0 := norm_nonneg u
  have hb0 := norm_nonneg Pw
  constructor
  · rw [one_div, inv_mul_le_iff₀ (by positivity)]
    have : ‖Pw‖ * ‖Pw‖ ≤ (t * ‖u‖) * (t * ‖u‖) := mul_self_le_mul_self hb0 hb
    nlinarith [mul_nonneg ht0 ha0, mul_self_nonneg ‖u‖]
  · by_cases hu0 : ‖u‖ = 0
    · rw [hu0] at hcs; nlinarith
    · have hapos : 0 < ‖u‖ := lt_of_le_of_ne ha0 (Ne.symm hu0)
      have : ‖u‖ ≤ ‖Pw‖ := by
        by_contra hlt
        push Not at hlt
        nlinarith
      nlinarith

end Concrete

/-! ### Packaging for an arbitrary integrable kernel with nonnegative Fourier coefficients -/

section General

variable {g ρ : Torus d → ℝ} {Λ : ℝ}

/-- Fourier coefficients in the form used above. -/
theorem hcoef_of_funFourierCoeff {g : Torus d → ℝ} {ĝ : Lattice d → ℝ}
    (h : ∀ n, Torus.funFourierCoeff (fun x => (g x : ℂ)) n = (ĝ n : ℂ)) (n : Lattice d) :
    ∫ x, Torus.mode (-n) x * (g x : ℂ) = (ĝ n : ℂ) := by
  have h' := h n
  unfold Torus.funFourierCoeff UnitAddTorus.mFourierCoeff at h'
  rw [Torus.volume_eq_pi_haar]
  simp only [smul_eq_mul] at h'
  exact h'

theorem Kt_congr_kernel {g g' : Torus d → ℝ} (h : g =ᵐ[volume] g') (ρ : Torus d → ℝ)
    (f : Torus d → ℝ) : Kt g (withDensityReal ρ) f = Kt g' (withDensityReal ρ) f := by
  funext x
  unfold Kt
  refine integral_congr_ae ?_
  have h1 : (fun y => g (x - y)) =ᵐ[volume] fun y => g' (x - y) :=
    (Measure.measurePreserving_sub_left (volume : Measure (Torus d)) x).quasiMeasurePreserving.ae_eq_comp h
  filter_upwards [(dens_ac ρ).ae_le h1] with y hy
  rw [hy]

theorem RespEq_congr_kernel {g g' : Torus d → ℝ} (h : g =ᵐ[volume] g') (ρ : Torus d → ℝ)
    (β : ℝ) (ψ h' : Torus d → ℝ) :
    RespEq g (withDensityReal ρ) β ψ h' ↔ RespEq g' (withDensityReal ρ) β ψ h' := by
  unfold RespEq
  rw [Kt_congr_kernel h ρ h']

theorem setup_of_kernel (hgi : Integrable g) (ĝ : Lattice d → ℝ) (hĝ : ∀ n, 0 ≤ ĝ n)
    (hcoef : ∀ n, ∫ x, Torus.mode (-n) x * (g x : ℂ) = (ĝ n : ℂ))
    (hρ : IsProbDensity ρ) (hΛ : ∀ x, ρ x ≤ Λ) :
    ∃ g' : Torus d → ℝ, g' =ᵐ[volume] g ∧ Setup g' ρ Λ := by
  have hgm := hgi.aestronglyMeasurable
  have hae : hgm.mk g =ᵐ[volume] g := hgm.ae_eq_mk.symm
  refine ⟨hgm.mk g, hae, hρ, hΛ, hgm.stronglyMeasurable_mk.measurable, ?_, ĝ, hĝ, ?_⟩
  · exact hgi.congr hgm.ae_eq_mk
  · intro n
    rw [← hcoef n]
    refine integral_congr_ae ?_
    filter_upwards [hae] with x hx
    rw [hx]

theorem exists_unique_respEq_general (hgi : Integrable g) (ĝ : Lattice d → ℝ)
    (hĝ : ∀ n, 0 ≤ ĝ n) (hcoef : ∀ n, ∫ x, Torus.mode (-n) x * (g x : ℂ) = (ĝ n : ℂ))
    (hρ : IsProbDensity ρ) (hΛ : ∀ x, ρ x ≤ Λ) {β : ℝ} (hβ : 0 ≤ β) {ψ : Torus d → ℝ}
    (hψ : MemLp ψ 2 (withDensityReal ρ)) :
    ∃ h, RespEq g (withDensityReal ρ) β ψ h ∧
      ∀ h', RespEq g (withDensityReal ρ) β ψ h' → h' =ᵐ[withDensityReal ρ] h := by
  obtain ⟨g', hgg', S⟩ := setup_of_kernel hgi ĝ hĝ hcoef hρ hΛ
  obtain ⟨h, h1, h2⟩ := exists_unique_respEq S hβ hψ
  refine ⟨h, (RespEq_congr_kernel hgg' ρ β ψ h).1 h1, fun h' hh' => h2 h' ?_⟩
  exact (RespEq_congr_kernel hgg' ρ β ψ h').2 hh'

theorem susc_bounds_general (hgi : Integrable g) (ĝ : Lattice d → ℝ)
    (hĝ : ∀ n, 0 ≤ ĝ n) (hcoef : ∀ n, ∫ x, Torus.mode (-n) x * (g x : ℂ) = (ĝ n : ℂ))
    (hρ : IsProbDensity ρ) (hΛ : ∀ x, ρ x ≤ Λ) {β : ℝ} (hβ : 0 ≤ β) :
    ∃ c : ℝ, 0 < c ∧ ∀ (φ h : Torus d → ℝ), MemLp φ 2 (withDensityReal ρ) →
      RespEq g (withDensityReal ρ) β φ h →
      c * ∫ x, (φ x - ∫ y, φ y ∂(withDensityReal ρ)) * (φ x - ∫ y, φ y ∂(withDensityReal ρ))
          ∂(withDensityReal ρ) ≤
        ∫ x, (φ x - ∫ y, φ y ∂(withDensityReal ρ)) * h x ∂(withDensityReal ρ) ∧
      ∫ x, (φ x - ∫ y, φ y ∂(withDensityReal ρ)) * h x ∂(withDensityReal ρ) ≤
        ∫ x, (φ x - ∫ y, φ y ∂(withDensityReal ρ)) * (φ x - ∫ y, φ y ∂(withDensityReal ρ))
          ∂(withDensityReal ρ) := by
  obtain ⟨g', hgg', S⟩ := setup_of_kernel hgi ĝ hĝ hcoef hρ hΛ
  obtain ⟨c, hc, H⟩ := susc_bounds S hβ
  exact ⟨c, hc, fun φ h hφ hr => H φ h hφ ((RespEq_congr_kernel hgg' ρ β φ h).2 hr)⟩

end General

end HRS.ResponseAux
