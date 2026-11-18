import HRS.MD.EQ29Vocab
import HRS.Energy.Commutator.AbsConv
import HRS.Sections.Q40bAux3
import HRS.PDE.EnergyTorusSqrt
import HRS.PDE.EnergyR2Fn
import HRS.PDE.MeanFieldLinearLoss
import HRS.Equilibrium.PairCorrection

/-!
# EQ-REM, part 1: elementary properties of the pair kernel `h_φ = pairKernel d s φ`

For `φ ∈ C²`: measurability, symmetry, the singular envelope `|h_φ| ≤ C₀ ‖φ‖_{C²} (1 + r^{-s})`, and boundedness of the
kernel fields `H_{ν,φ}` for measures with bounded density.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MD.EQRem

open HRS HRS.MD.EQ29

variable {d : ℕ} {s : ℝ}

theorem eqrem_pairKernel_symm (hsd : s < d) (φ : Torus d → ℝ) (x y : Torus d) :
    pairKernel d s φ x y = pairKernel d s φ y x := by
  unfold pairKernel commKernel
  by_cases hxy : x = y
  · subst hxy; rfl
  · have hyx : y ≠ x := fun h => hxy h.symm
    rw [if_neg hxy, if_neg hyx]
    rw [← neg_sub x y, ← neg_sub (Torus.grad φ x) (Torus.grad φ y),
      KernelGrad.periodicRieszGrad_neg_of_lt hsd, inner_neg_neg]

theorem eqrem_continuous_grad {φ : Torus d → ℝ} (hφ : Torus.IsCk 2 φ) : Continuous (Torus.grad φ) :=
  PDE.MFLinear.continuous_grad (PDE.ClassicalAux.isCk_of_le (by exact_mod_cast (by norm_num : (1 : ℕ) ≤ 2)) hφ)

theorem eqrem_pairKernel_meas (hsd : s < d) {φ : Torus d → ℝ} (hφ : Torus.IsCk 2 φ) :
    Measurable (Function.uncurry (pairKernel d s φ)) := by
  have hvc := eqrem_continuous_grad hφ
  unfold pairKernel commKernel Function.uncurry
  refine Measurable.ite (measurableSet_eq_fun measurable_fst measurable_snd) measurable_const ?_
  refine Measurable.inner ?_ ?_
  · exact (hvc.measurable.comp measurable_fst).sub (hvc.measurable.comp measurable_snd)
  · exact (KernelGrad.measurable_periodicRieszGrad hsd).comp (measurable_fst.sub measurable_snd)

theorem eqrem_lip_grad {φ : Torus d → ℝ} (hφ : Torus.IsCk 2 φ) :
    IsLipschitzVF (Torus.cbNorm 2 φ) (Torus.grad φ) :=
  Q40b.q40b_grad_lip hφ fun y => PDE.ET.norm_iteratedFDeriv_le_cbNorm (le_refl 2) hφ y

theorem eqrem_cbNorm_nonneg (k : ℕ) (φ : Torus d → ℝ) : 0 ≤ Torus.cbNorm k φ :=
  PDE.cbNorm_nonneg' k φ

/-- The envelope: `|h_φ(x,y)| ≤ C₀ ‖φ‖_{C²} singEnvelope s (|x-y|)` off the diagonal, `C₀ = C₀(d,s)`. -/
theorem eqrem_pairKernel_env (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ φ : Torus d → ℝ, Torus.IsCk 2 φ → ∀ x y : Torus d, x ≠ y →
      |pairKernel d s φ x y| ≤ (C₀ * Torus.cbNorm 2 φ) * singEnvelope s (Torus.eucDist x y) := by
  obtain ⟨C, hC0, hC⟩ := Commutator.commKernel_bound (d := d) (s := s) (by omega) hs0 hsd
  refine ⟨2 * C, by positivity, fun φ hφ x y hxy => ?_⟩
  have h1 := hC (Torus.cbNorm 2 φ) (Torus.grad φ) (eqrem_cbNorm_nonneg 2 φ) (eqrem_lip_grad hφ) x y hxy
  have hpos : 0 < Torus.eucDist x y := by
    have := Q40b.q40b_tdist_eq_eucDist x y
    rw [← PairCorrAux.eucDist_sub_zero] at this
    rw [← this, KernelGrad.tdist_eq_sub_zero]
    exact KernelGrad.tdist_pos (sub_ne_zero.mpr hxy)
  have ht : KernelGrad.tdist x y = Torus.eucDist x y := by
    rw [Q40b.q40b_tdist_eq_eucDist, ← PairCorrAux.eucDist_sub_zero]
  have h3 : KernelGrad.tdist x y ^ (-s) + 1 ≤ 2 * singEnvelope s (Torus.eucDist x y) := by
    rw [ht]
    by_cases hs : s = 0
    · subst hs
      simp only [singEnvelope, if_true, neg_zero, Real.rpow_zero]
      linarith [abs_nonneg (Real.log (Torus.eucDist x y))]
    · simp only [singEnvelope, hs, if_false]
      have := Real.rpow_nonneg hpos.le (-s)
      linarith
  have hcb := eqrem_cbNorm_nonneg 2 φ
  calc |pairKernel d s φ x y| = |commKernel (periodicRieszGrad d s) (Torus.grad φ) x y| := rfl
    _ ≤ C * Torus.cbNorm 2 φ * (KernelGrad.tdist x y ^ (-s) + 1) := h1
    _ ≤ C * Torus.cbNorm 2 φ * (2 * singEnvelope s (Torus.eucDist x y)) := by gcongr
    _ = (2 * C * Torus.cbNorm 2 φ) * singEnvelope s (Torus.eucDist x y) := by ring


/-- Fibrewise integrability and the uniform `L¹(ν)` bound of the pair kernel for a measure `ν ≤ Λ · dx`. -/
theorem eqrem_kernel_L1 (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∀ φ : Torus d → ℝ, Torus.IsCk 2 φ → ∀ (ν : Measure (Torus d)) (Λ : ℝ), 0 ≤ Λ →
      ν ≤ ENNReal.ofReal Λ • (volume : Measure (Torus d)) →
      ∀ x : Torus d, Integrable (fun y => pairKernel d s φ x y) ν ∧
        ∫ y, |pairKernel d s φ x y| ∂ν ≤ Λ * (C₁ * Torus.cbNorm 2 φ) := by
  obtain ⟨C, hC0, hC⟩ := Commutator.commKernel_bound (d := d) (s := s) (by omega) hs0 hsd
  have hgi : Integrable (fun z : Torus d => ‖z‖ ^ (-s) + 1) volume :=
    (KernelGrad.integrable_norm_rpow_neg (by omega) hsd).add (integrable_const _)
  set K0 : ℝ := ∫ z : Torus d, (‖z‖ ^ (-s) + 1) with hK0
  have hK00 : 0 ≤ K0 := integral_nonneg fun z => add_nonneg (Real.rpow_nonneg (norm_nonneg _) _) zero_le_one
  refine ⟨C * K0, mul_nonneg hC0 hK00, fun φ hφ ν Λ hΛ hν x => ?_⟩
  set L := Torus.cbNorm 2 φ with hL
  have hL0 : 0 ≤ L := eqrem_cbNorm_nonneg 2 φ
  have hK : 0 ≤ C * L := mul_nonneg hC0 hL0
  have hlip := eqrem_lip_grad hφ
  have hbound : ∀ y : Torus d, |pairKernel d s φ x y| ≤ (C * L) * (‖x - y‖ ^ (-s) + 1) := by
    intro y
    by_cases hxy : x = y
    · subst hxy
      unfold pairKernel commKernel
      rw [if_pos rfl, abs_zero]
      exact mul_nonneg hK (add_nonneg (Real.rpow_nonneg (norm_nonneg _) _) zero_le_one)
    · have h1 := hC L (Torus.grad φ) hL0 hlip x y hxy
      have hz : x - y ≠ 0 := sub_ne_zero.mpr hxy
      have h2 : KernelGrad.tdist x y ^ (-s) ≤ ‖x - y‖ ^ (-s) := by
        rw [KernelGrad.tdist_eq_sub_zero]
        exact Real.rpow_le_rpow_of_nonpos (norm_pos_iff.mpr hz) (KernelGrad.norm_le_tdist _)
          (by linarith)
      calc |pairKernel d s φ x y| ≤ C * L * (KernelGrad.tdist x y ^ (-s) + 1) := h1
        _ ≤ (C * L) * (‖x - y‖ ^ (-s) + 1) := mul_le_mul_of_nonneg_left (by linarith) hK
  have hgi' : Integrable (fun y : Torus d => (C * L) * (‖x - y‖ ^ (-s) + 1)) volume :=
    (hgi.comp_sub_left x).const_mul _
  have hνfin : IsFiniteMeasure ν := by
    refine ⟨?_⟩
    have h := Measure.le_iff'.1 hν Set.univ
    rw [Measure.smul_apply, smul_eq_mul] at h
    exact lt_of_le_of_lt h (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _))
  have hint : Integrable (fun y : Torus d => (C * L) * (‖x - y‖ ^ (-s) + 1)) ν :=
    (hgi'.smul_measure ENNReal.ofReal_ne_top).mono_measure hν
  have hmeas : Measurable (fun y => pairKernel d s φ x y) :=
    (eqrem_pairKernel_meas hsd hφ).comp (measurable_const.prodMk measurable_id)
  have hI : Integrable (fun y => pairKernel d s φ x y) ν := by
    refine Integrable.mono' hint hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs]; exact hbound y
  refine ⟨hI, ?_⟩
  have h1 : ∫ y, |pairKernel d s φ x y| ∂ν ≤ ∫ y, (C * L) * (‖x - y‖ ^ (-s) + 1) ∂ν :=
    integral_mono hI.abs hint hbound
  refine h1.trans ?_
  have h2 := integral_mono_measure hν
    (Filter.Eventually.of_forall fun y => mul_nonneg hK (add_nonneg (Real.rpow_nonneg (norm_nonneg _) _) zero_le_one))
    (hgi'.smul_measure ENNReal.ofReal_ne_top)
  rw [integral_smul_measure, ENNReal.toReal_ofReal hΛ, smul_eq_mul] at h2
  refine h2.trans ?_
  have h3 : ∫ y : Torus d, (C * L) * (‖x - y‖ ^ (-s) + 1) = (C * L) * K0 := by
    rw [integral_const_mul]
    congr 1
    exact integral_sub_left_eq_self (fun z : Torus d => (‖z‖ ^ (-s) + 1)) volume x
  rw [h3]
  nlinarith [mul_nonneg hK hK00]


/-- Pointwise bound (all `x, y`) of the pair kernel by the integrable radial majorant `‖x-y‖^{-s} + 1`. -/
theorem eqrem_pairKernel_bound (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ φ : Torus d → ℝ, Torus.IsCk 2 φ → ∀ x y : Torus d,
      |pairKernel d s φ x y| ≤ (C * Torus.cbNorm 2 φ) * (‖x - y‖ ^ (-s) + 1) := by
  obtain ⟨C, hC0, hC⟩ := Commutator.commKernel_bound (d := d) (s := s) (by omega) hs0 hsd
  refine ⟨C, hC0, fun φ hφ x y => ?_⟩
  have hL0 : 0 ≤ Torus.cbNorm 2 φ := eqrem_cbNorm_nonneg 2 φ
  have hK : 0 ≤ C * Torus.cbNorm 2 φ := mul_nonneg hC0 hL0
  by_cases hxy : x = y
  · subst hxy
    unfold pairKernel commKernel
    rw [if_pos rfl, abs_zero]
    exact mul_nonneg hK (add_nonneg (Real.rpow_nonneg (norm_nonneg _) _) zero_le_one)
  · have h1 := hC (Torus.cbNorm 2 φ) (Torus.grad φ) hL0 (eqrem_lip_grad hφ) x y hxy
    have hz : x - y ≠ 0 := sub_ne_zero.mpr hxy
    have h2 : KernelGrad.tdist x y ^ (-s) ≤ ‖x - y‖ ^ (-s) := by
      rw [KernelGrad.tdist_eq_sub_zero]
      exact Real.rpow_le_rpow_of_nonpos (norm_pos_iff.mpr hz) (KernelGrad.norm_le_tdist _)
        (by linarith)
    calc |pairKernel d s φ x y| ≤ C * Torus.cbNorm 2 φ * (KernelGrad.tdist x y ^ (-s) + 1) := h1
      _ ≤ (C * Torus.cbNorm 2 φ) * (‖x - y‖ ^ (-s) + 1) := mul_le_mul_of_nonneg_left (by linarith) hK

/-- The integral `K₀ = ∫ (‖z‖^{-s} + 1) dz` of the radial majorant is finite (integrable for `s < d`). -/
theorem eqrem_radial_integrable (hd : 2 ≤ d) (hsd : s < d) :
    Integrable (fun z : Torus d => ‖z‖ ^ (-s) + 1) volume :=
  (KernelGrad.integrable_norm_rpow_neg (by omega) hsd).add (integrable_const _)

end HRS.MD.EQRem

end
