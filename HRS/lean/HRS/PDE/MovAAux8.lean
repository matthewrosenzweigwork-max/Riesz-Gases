import HRS.PDE.MovAAux7

/-!
# MOVA Aux8: the moving reference `Q^M` as a Gibbs weight, and `E_{Q^M}[Lψ + κ‖∇ψ‖²] = 0`.
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

variable {d N : ℕ}

theorem mova_integral_withDensity_real {α : Type*} [MeasurableSpace α] (μ : Measure α) {h : α → ℝ}
    (hh : Measurable h) (h0 : ∀ x, 0 ≤ h x) (f : α → ℝ) :
    ∫ x, f x ∂(μ.withDensity fun x => ENNReal.ofReal (h x)) = ∫ x, h x * f x ∂μ := by
  have : (fun x => ENNReal.ofReal (h x)) = fun x => ((h x).toNNReal : ENNReal) := rfl
  rw [this, integral_withDensity_eq_integral_smul hh.real_toNNReal f]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [NNReal.smul_def, Real.coe_toNNReal _ (h0 x)]

theorem mova_integral_pi_withDensityReal {ρ : Torus d → ℝ} (hρ : Continuous ρ) (h0 : ∀ x, 0 ≤ ρ x)
    (g : Config d N → ℝ) :
    ∫ X, g X ∂(Measure.pi fun _ : Fin N => withDensityReal ρ) = ∫ X : Config d N, (∏ i, ρ (X i)) * g X := by
  rw [pi_withDensityReal_eq ρ hρ.measurable]
  have e : (fun X : Config d N => ∏ i, ENNReal.ofReal (ρ (X i))) =
      fun X => ENNReal.ofReal (∏ i, ρ (X i)) := by
    funext X
    rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => h0 _)]
  rw [e]
  exact mova_integral_withDensity_real _ (Finset.measurable_prod _ fun i _ => hρ.measurable.comp
    (measurable_pi_apply i)) (fun X => Finset.prod_nonneg fun i _ => h0 _) g

theorem mova_integral_modulatedGibbs (g : Torus d → ℝ) (N : ℕ) (β : ℝ) (μ : Measure (Torus d))
    {W : Config d N → ℝ} (hW : ∀ X, W X = Real.exp (-β * N * modulatedEnergyKernel g X μ))
    (hWm : Measurable W) (f : Config d N → ℝ) :
    ∫ X, f X ∂(modulatedGibbs g N β μ) =
      ((ENNReal.ofReal (gibbsNormalizer g N β μ))⁻¹).toReal •
        ∫ X, W X * f X ∂(Measure.pi fun _ : Fin N => μ) := by
  unfold modulatedGibbs
  rw [integral_smul_measure]
  congr 1
  have e : (fun X : Config d N => ENNReal.ofReal (Real.exp (-β * N * modulatedEnergyKernel g X μ))) =
      fun X => ENNReal.ofReal (W X) := funext fun X => by rw [hW]
  rw [e]
  exact mova_integral_withDensity_real _ hWm (fun X => by rw [hW]; exact (Real.exp_pos _).le) f

theorem mova_integral_kernel_withDensity {ρ : Torus d → ℝ} (hdens : IsProbDensity ρ) (g : Torus d → ℝ)
    (x : Torus d) : ∫ y, g (x - y) ∂(withDensityReal ρ) = convFun g ρ x := by
  rw [PDE.MFPairing.integral_withDensityReal hdens.measurable hdens.nonneg]
  unfold convFun
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only
  ring

/-- The constant `∬ g_M(x-y) dμ dμ`. -/
def mova_c3 (g : Torus d → ℝ) (μ : Measure (Torus d)) : ℝ := ∫ x, ∫ y, g (x - y) ∂μ ∂μ

theorem mova_modEnergy_expand {ρ : Torus d → ℝ} (hdens : IsProbDensity ρ) (g : Torus d → ℝ)
    (X : Config d N) :
    modulatedEnergyKernel g X (withDensityReal ρ) =
      (1 / (2 * (N : ℝ) ^ 2)) * ∑ i, ∑ j ∈ Finset.univ.erase i, g (X i - X j)
        - (1 / (N : ℝ)) * ∑ i, convFun g ρ (X i) + (1 / 2) * mova_c3 g (withDensityReal ρ) := by
  unfold modulatedEnergyKernel modulatedEnergy mova_c3
  simp_rw [mova_integral_kernel_withDensity hdens]

theorem mova_continuous_modEnergy {ρ : Torus d → ℝ} (hdens : IsProbDensity ρ) (hρc : Continuous ρ)
    {g : Torus d → ℝ} (hg : Continuous g) (hgi : Integrable g) :
    Continuous fun X : Config d N => modulatedEnergyKernel g X (withDensityReal ρ) := by
  have e : (fun X : Config d N => modulatedEnergyKernel g X (withDensityReal ρ)) = fun X =>
      (1 / (2 * (N : ℝ) ^ 2)) * ∑ i, ∑ j ∈ Finset.univ.erase i, g (X i - X j)
        - (1 / (N : ℝ)) * ∑ i, convFun g ρ (X i) + (1 / 2) * mova_c3 g (withDensityReal ρ) :=
    funext fun X => mova_modEnergy_expand hdens g X
  rw [e]
  have hc : Continuous (convFun g ρ) := PDE.MFAux.continuous_convFun hgi hρc
  refine ((continuous_const.mul (continuous_finsetSum _ fun i _ => continuous_finsetSum _
    fun j _ => hg.comp ((continuous_apply i).sub (continuous_apply j)))).sub
    (continuous_const.mul (continuous_finsetSum _ fun i _ => hc.comp (continuous_apply i)))).add
    continuous_const

theorem mova_weight_eq (hN : 0 < N) (D : DynData d) (M : ℝ) {ρ : Torus d → ℝ}
    (hdens : IsProbDensity ρ) (hpos : ∀ x, 0 < ρ x) {φ : Torus d → ℝ}
    (hφeq : ∀ x, φ x = D.invβ⁻¹ * (D.V x + convFun (b15c_gReg d D.s M) ρ x) + Real.log (ρ x))
    (X : Config d N) :
    Real.exp (-D.invβ⁻¹ * N * modulatedEnergyKernel (b15c_gReg d D.s M) X (withDensityReal ρ)) *
        ∏ i, ρ (X i) =
      Real.exp (-(D.invβ⁻¹ * N / 2) * mova_c3 (b15c_gReg d D.s M) (withDensityReal ρ)) *
        Real.exp (-(D.invβ⁻¹ * b15c_potentialReg D M X) + ∑ i, φ (X i)) := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hprod : ∏ i, ρ (X i) = Real.exp (∑ i, Real.log (ρ (X i))) := by
    rw [Real.exp_sum]
    exact Finset.prod_congr rfl fun i _ => (Real.exp_log (hpos _)).symm
  rw [mova_modEnergy_expand hdens, hprod, ← Real.exp_add, ← Real.exp_add]
  congr 1
  unfold b15c_potentialReg b15c_potentialOf
  simp_rw [hφeq]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  field_simp
  ring

/-- `E_{Q^M}[Lψ + κ‖∇ψ‖²] = 0` for the tilt `ψ = ∑ φ(x_i)` of `Q^M`. -/
theorem mova_EQ_A0 (hN : 0 < N) (D : DynData d) (hM : D.M = -(1 : Matrix (Fin d) (Fin d) ℝ))
    (hV : Torus.IsCk 2 D.V) (hκ : 0 < D.invβ) (M : ℝ) {ρ : Torus d → ℝ} (hρ : Torus.IsCk 2 ρ)
    (hdens : IsProbDensity ρ) (hpos : ∀ x, 0 < ρ x) {φ : Torus d → ℝ} (hφ : Torus.IsCk 2 φ)
    (hφeq : ∀ x, φ x = D.invβ⁻¹ * (D.V x + convFun (b15c_gReg d D.s M) ρ x) + Real.log (ρ x)) :
    ∫ X : Config d N, (d1_configGen D.invβ (b15d_configDriftReg D M) (fun X => ∑ i, φ (X i)) X +
        D.invβ * ∑ i, ‖Torus.grad φ (X i)‖ ^ 2)
      ∂(modulatedGibbs (b15c_gReg d D.s M) N D.invβ⁻¹ (withDensityReal ρ)) = 0 := by
  have hρc := mova_continuous_of_isCk hρ
  have hgc : Continuous (b15c_gReg d D.s M) :=
    b15c_isSmooth_continuous (b15c_gReg_isSmooth (b15_one_le_d D) D.hs0 D.hsd M)
  have hWm : Measurable fun X : Config d N => Real.exp (-D.invβ⁻¹ * N *
      modulatedEnergyKernel (b15c_gReg d D.s M) X (withDensityReal ρ)) :=
    (Real.continuous_exp.comp (continuous_const.mul
      (mova_continuous_modEnergy hdens hρc hgc (mova_integrable_gReg D M)))).measurable
  rw [mova_integral_modulatedGibbs (b15c_gReg d D.s M) N D.invβ⁻¹ (withDensityReal ρ)
    (W := fun X : Config d N => Real.exp (-D.invβ⁻¹ * N *
      modulatedEnergyKernel (b15c_gReg d D.s M) X (withDensityReal ρ))) (fun X => rfl) hWm,
    mova_integral_pi_withDensityReal hρc hdens.nonneg]
  have hpt : ∀ X : Config d N, (∏ i, ρ (X i)) *
      (Real.exp (-D.invβ⁻¹ * N * modulatedEnergyKernel (b15c_gReg d D.s M) X (withDensityReal ρ)) *
        (d1_configGen D.invβ (b15d_configDriftReg D M) (fun X => ∑ i, φ (X i)) X +
          D.invβ * ∑ i, ‖Torus.grad φ (X i)‖ ^ 2)) =
      Real.exp (-(D.invβ⁻¹ * N / 2) * mova_c3 (b15c_gReg d D.s M) (withDensityReal ρ)) *
        ((d1_configGen D.invβ (b15d_configDriftReg D M) (fun X => ∑ i, φ (X i)) X +
          D.invβ * ∑ i, ‖Torus.grad φ (X i)‖ ^ 2) *
          Real.exp (-(D.invβ⁻¹ * b15c_potentialReg D M X) + ∑ i, φ (X i))) := by
    intro X
    have := mova_weight_eq hN D M hdens hpos hφeq X
    calc _ = (Real.exp (-D.invβ⁻¹ * N * modulatedEnergyKernel (b15c_gReg d D.s M) X
          (withDensityReal ρ)) * ∏ i, ρ (X i)) * (d1_configGen D.invβ (b15d_configDriftReg D M)
            (fun X => ∑ i, φ (X i)) X + D.invβ * ∑ i, ‖Torus.grad φ (X i)‖ ^ 2) := by ring
      _ = _ := by rw [this]; ring
  simp_rw [hpt]
  rw [integral_const_mul, mova_ibp_config hκ D hM hV M hφ, mul_zero, smul_zero]

end HRS
