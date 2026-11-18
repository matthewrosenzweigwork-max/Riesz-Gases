import HRS.Whole.Adjoint
import HRS.PDE.ToolboxRd.Fourier

/-!
# MS-SOBMUL, part 1: translation invariance of `H^s` norms, Peetre, a Young-type inequality
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ComplexConjugate FourierTransform

namespace HRS.MS.SobMul
open HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux

variable {d : ℕ}

/-! ### Translation -/

theorem sobmul_fourierL2_translate {u : Euc d → ℝ} (hu : MemLp u 2 volume) (z : Euc d) :
    fourierL2 (fun x => u (x - z)) =ᵐ[volume] fun ξ => phase z ξ * fourierL2 u ξ := by
  have hs := memLp_translate hu z
  rw [fourierL2_eq hs, ← ofRealLp_translate hu z, fourier_translLp, fourierL2_eq hu]
  exact mulPhase_coe z _

theorem sobmul_wtnorm_translate {u : Euc d → ℝ} (hu : MemLp u 2 volume) (z : Euc d) (s : ℝ) :
    (fun ξ => wt ξ ^ s * ‖fourierL2 (fun x => u (x - z)) ξ‖ ^ 2) =ᵐ[volume]
      fun ξ => wt ξ ^ s * ‖fourierL2 u ξ‖ ^ 2 := by
  filter_upwards [sobmul_fourierL2_translate hu z] with ξ hξ
  rw [hξ, norm_mul, norm_phase, one_mul]

theorem sobmul_memSobolev_translate {s : ℝ} {u : Euc d → ℝ} (hu : HRS.PDE.ToolboxRd.MemSobolev s u) (z : Euc d) :
    HRS.PDE.ToolboxRd.MemSobolev s (fun x => u (x - z)) := by
  refine ⟨memLp_translate hu.1 z, ?_⟩
  exact hu.2.congr (sobmul_wtnorm_translate hu.1 z s).symm

theorem sobmul_sobolevNormSq_translate {u : Euc d → ℝ} (hu : MemLp u 2 volume) (z : Euc d)
    (s : ℝ) :
    HRS.PDE.ToolboxRd.sobolevNormSq s (fun x => u (x - z)) = HRS.PDE.ToolboxRd.sobolevNormSq s u := by
  rw [sobolevNormSq_eq, sobolevNormSq_eq]
  exact integral_congr_ae (sobmul_wtnorm_translate hu z s)

theorem sobolevNormE_translate (s : ℝ) (u : Euc d → ℝ) (z : Euc d) :
    HRS.Whole.sobolevNormE s (fun x => u (x - z)) = HRS.Whole.sobolevNormE s u := by
  have key : ∀ (u : Euc d → ℝ) (z : Euc d), HRS.PDE.ToolboxRd.MemSobolev s u →
      HRS.PDE.ToolboxRd.MemSobolev s (fun x => u (x - z)) ∧
        HRS.PDE.ToolboxRd.sobolevNormSq s (fun x => u (x - z)) = HRS.PDE.ToolboxRd.sobolevNormSq s u := fun u z hu =>
    ⟨sobmul_memSobolev_translate hu z, sobmul_sobolevNormSq_translate hu.1 z s⟩
  by_cases hu : HRS.PDE.ToolboxRd.MemSobolev s u
  · obtain ⟨h1, h2⟩ := key u z hu
    unfold HRS.Whole.sobolevNormE
    rw [if_pos hu, if_pos h1, h2]
  · have hu' : ¬ HRS.PDE.ToolboxRd.MemSobolev s (fun x => u (x - z)) := by
      intro h
      apply hu
      have := (key _ (-z) h).1
      simpa using this
    unfold HRS.Whole.sobolevNormE
    rw [if_neg hu, if_neg hu']

/-! ### Peetre -/

theorem sobmul_wt_le (ξ η : Euc d) : wt ξ ≤ 2 * (wt (ξ - η) * wt η) := by
  unfold wt
  have h1 : ‖ξ‖ ≤ ‖ξ - η‖ + ‖η‖ := by simpa using norm_add_le (ξ - η) η
  have h2 : ‖ξ‖ ^ 2 ≤ 2 * ‖ξ - η‖ ^ 2 + 2 * ‖η‖ ^ 2 := by
    nlinarith [sq_nonneg (‖ξ - η‖ - ‖η‖), norm_nonneg ξ]
  have hc : 0 ≤ 4 * Real.pi ^ 2 := by positivity
  have h3 : 0 ≤ (4 * Real.pi ^ 2) ^ 2 * (‖ξ - η‖ ^ 2 * ‖η‖ ^ 2) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h2 hc]

theorem sobmul_wt_rpow_le {s : ℝ} (hs : 0 ≤ s) (ξ η : Euc d) :
    wt ξ ^ (s / 2) ≤ 2 ^ (s / 2) * (wt (ξ - η) ^ (s / 2) * wt η ^ (s / 2)) := by
  have h0 : 0 ≤ s / 2 := by positivity
  calc wt ξ ^ (s / 2) ≤ (2 * (wt (ξ - η) * wt η)) ^ (s / 2) :=
        Real.rpow_le_rpow (wt_pos ξ).le (sobmul_wt_le ξ η) h0
    _ = _ := by
        rw [Real.mul_rpow (by norm_num) (mul_nonneg (wt_pos _).le (wt_pos _).le),
          Real.mul_rpow (wt_pos _).le (wt_pos _).le]

/-! ### Cauchy–Schwarz and a Young-type inequality in `ℝ≥0∞` -/

theorem sobmul_cs {α : Type*} [MeasurableSpace α] (ν : Measure α) (g : α → ℝ≥0∞)
    (hg : AEMeasurable g ν) :
    (∫⁻ x, g x ∂ν) ^ 2 ≤ ν Set.univ * ∫⁻ x, g x ^ 2 ∂ν := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq ν Real.HolderConjugate.two_two
    (aemeasurable_const (b := (1 : ℝ≥0∞))) hg
  have h : ∫⁻ x, g x ∂ν ≤ (ν Set.univ) ^ ((1 : ℝ) / 2) *
      (∫⁻ x, g x ^ (2 : ℝ) ∂ν) ^ ((1 : ℝ) / 2) := by simpa using h
  have h2 : (∫⁻ x, g x ∂ν) ^ 2 ≤ ((ν Set.univ) ^ ((1 : ℝ) / 2) *
      (∫⁻ x, g x ^ (2 : ℝ) ∂ν) ^ ((1 : ℝ) / 2)) ^ 2 := by gcongr
  refine h2.trans (le_of_eq ?_)
  rw [mul_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast (_ ^ _ : ℝ≥0∞), ← ENNReal.rpow_mul,
    ← ENNReal.rpow_mul]
  simp only [Nat.cast_ofNat]
  norm_num

theorem sobmul_young {A B : Euc d → ℝ≥0∞} (hA : Measurable A) (hB : Measurable B) :
    ∫⁻ ξ, (∫⁻ η, A (ξ - η) * B η) ^ 2 ≤ (∫⁻ x, A x) ^ 2 * ∫⁻ η, B η ^ 2 := by
  have hAs : ∀ ξ : Euc d, Measurable fun η => A (ξ - η) := fun ξ =>
    hA.comp (measurable_const.sub measurable_id)
  have step1 : ∀ ξ : Euc d, (∫⁻ η, A (ξ - η) * B η) ^ 2 ≤
      (∫⁻ x, A x) * ∫⁻ η, A (ξ - η) * B η ^ 2 := by
    intro ξ
    have h := sobmul_cs (volume.withDensity fun η => A (ξ - η)) B hB.aemeasurable
    rw [lintegral_withDensity_eq_lintegral_mul _ (hAs ξ) hB,
      lintegral_withDensity_eq_lintegral_mul _ (hAs ξ) (hB.pow_const 2),
      withDensity_apply _ MeasurableSet.univ] at h
    simp only [Pi.mul_apply, Measure.restrict_univ] at h
    have e : ∫⁻ η, A (ξ - η) = ∫⁻ x, A x := lintegral_sub_left_eq_self A ξ
    rwa [e] at h
  calc ∫⁻ ξ, (∫⁻ η, A (ξ - η) * B η) ^ 2
      ≤ ∫⁻ ξ, (∫⁻ x, A x) * ∫⁻ η, A (ξ - η) * B η ^ 2 := lintegral_mono step1
    _ = (∫⁻ x, A x) * ∫⁻ ξ, ∫⁻ η, A (ξ - η) * B η ^ 2 := lintegral_const_mul _ (by
          have := ((hA.comp (measurable_fst.sub measurable_snd)).mul
            ((hB.comp measurable_snd).pow_const 2)).lintegral_prod_right' (ν := (volume : Measure (Euc d)))
          exact this)
    _ = (∫⁻ x, A x) * ∫⁻ η, ∫⁻ ξ, A (ξ - η) * B η ^ 2 := by
        congr 1
        refine lintegral_lintegral_swap ?_
        exact ((hA.comp (measurable_fst.sub measurable_snd)).mul
          ((hB.comp measurable_snd).pow_const 2)).aemeasurable
    _ = (∫⁻ x, A x) * ∫⁻ η, (∫⁻ x, A x) * B η ^ 2 := by
        congr 1
        refine lintegral_congr fun η => ?_
        have hm : Measurable fun ξ : Euc d => A (ξ - η) :=
          hA.comp (measurable_id.sub measurable_const)
        rw [lintegral_mul_const _ hm, lintegral_sub_right_eq_self A η]
    _ = _ := by
        rw [lintegral_const_mul _ (hB.pow_const 2), ← mul_assoc, sq]

end HRS.MS.SobMul
