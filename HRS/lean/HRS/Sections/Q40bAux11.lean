import HRS.Sections.Sec5
import HRS.PDE.MeanField
import HRS.Sections.Q40bAux2
import HRS.Sections.Q40bAux10

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section
namespace HRS.Q40b

variable {d N : ℕ}

section PropSmul

open HRS.PDE

theorem q40b_propagator_smul_ad (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {m : ℕ}
    (hm : mStar d ≤ m) {R : Regime} {MB Λ VB : ℝ} {D : DynData d} {ν₀ T : ℝ}
    {μ : ℝ → Torus d → ℝ} (hA : AdjointData s m R MB Λ VB D ν₀ T μ) {t : ℝ}
    (ht : t ∈ Set.Ioc 0 T) (a : ℝ) {φ : Torus d → ℝ} (hφc : Continuous φ)
    (hφ : MemSobolev (m : ℝ) φ) :
    ∀ r ∈ Set.Icc 0 t, propagator D μ r t (fun x => a * φ x) =
      fun x => a * propagator D μ r t φ x := by
  intro r hr
  have hm1 : 1 ≤ m := by have := ClassicalPart.one_le_of_mStar hm; omega
  have hcoef : coeffOf (fun x => a * φ x) = fun k => (a : ℂ) * coeffOf φ k :=
    funext fun k => MFThermalReg.coeffOf_const_mul_fun a φ k
  have hc : MemHs (m : ℝ) (coeffOf φ) := (hsNormSq_coeffOf (m : ℝ) φ hφ).1
  have hL2 : MemLp (fun x => a * φ x) 2 volume := hφ.1.const_mul a
  have hφ' : MemSobolev (m : ℝ) (fun x => a * φ x) :=
    memSobolev_of_memHs _ _ hL2 (by rw [hcoef]; exact MFThermalReg.memHs_smul hc _)
  have e1 := ClassicalPart.propagator_eq_toFun hd s hs0 hsd m hm R MB Λ VB D ν₀ T μ hA t ht φ hφc hφ r hr
  have e2 := ClassicalPart.propagator_eq_toFun hd s hs0 hsd m hm R MB Λ VB D ν₀ T μ hA t ht
    (fun x => a * φ x) (continuous_const.mul hφc) hφ' r hr
  have hF : propagatorCoeff D μ m t (coeffOf (fun x => a * φ x)) (t - r) =
      fun k => (a : ℂ) * propagatorCoeff D μ m t (coeffOf φ) (t - r) k := by
    rw [hcoef]
    exact MFPair.propagatorCoeff_smul_aux hd s hs0 hsd m hm1 R MB Λ VB D ν₀ T μ hA ht (a : ℂ) hc
      ⟨by linarith [hr.2], by linarith [hr.1]⟩
  funext x
  rw [e2, e1, hF]
  exact MFPair.toFun_smul_aux a _ x

end PropSmul

variable {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}

theorem q40b_propagator_smul (hd : 2 ≤ d) (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ)
    {ρβ : Torus d → ℝ} (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ)
    (hρS : Torus.IsSmooth ρβ) (hρpos : ∀ x, 0 < ρβ x) (a : ℝ) {φ : Torus d → ℝ}
    (hφ : Torus.IsSmooth φ) {t : ℝ} (ht : 0 < t) :
    ∀ r ∈ Set.Icc 0 t, propagator htr.dyn ρ r t (fun x => a * φ x) =
      fun x => a * propagator htr.dyn ρ r t φ x := by
  intro r hr
  have hd1 : 1 ≤ d := by omega
  obtain ⟨j, hj, hmj⟩ : ∃ j : ℕ, (d : ℝ) / 2 + 4 < j ∧ PDE.mStar d ≤ j := by
    refine ⟨2 * d + 9, ?_, ?_⟩
    · push_cast
      have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
      linarith
    · have h := Nat.floor_le (show (0 : ℝ) ≤ (d : ℝ) / 2 by positivity)
      have h2 : ⌊(d : ℝ) / 2⌋₊ ≤ d := by
        have : (⌊(d : ℝ) / 2⌋₊ : ℝ) ≤ d := by
          have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
          linarith
        exact_mod_cast this
      unfold PDE.mStar
      omega
  have hK := q40b_K_ok d j
  have H := q40b_finiteRegHyp htr hK
  obtain ⟨ρc, hρc, hρ⟩ := q40b_sol htr hK
  have hρβc : Continuous ρβ := PDE.MFLinear.continuous_of_isSmooth hρS
  obtain ⟨R, Λ, Λ₀, c₀, Cd, κ, hc₀, hκ, hall⟩ :=
    PDE.MFAdjoint.finiteReg_hypotheses hd1 s β β (2 * j + 4 * d + 20) V ρ₀ H j hj le_rfl
  obtain ⟨-, hAD, -⟩ := hall β ⟨le_rfl, le_rfl⟩ ρc hρc ρβ hρβ hρβc hρpos
  have hcongr : ∀ r ∈ Set.Icc (0 : ℝ) t, ρ r = PDE.mfPath ρc r :=
    fun r hr => (hρ r hr.1).symm
  have key := q40b_propagator_smul_ad hd1 htr.hs0 htr.hsd hmj (hAD t ht) ⟨ht, le_rfl⟩ a
    (PDE.MFLinear.continuous_of_isSmooth hφ) (PDE.MFSemigroup.memSobolev_of_isSmooth hφ _) r hr
  rw [q40b_propagator_congr hcongr r, q40b_propagator_congr hcongr r φ]
  exact key


section Scale

variable {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}

theorem q40b_modEnergy_smul (c : ℝ) (h : Torus d → Torus d → ℝ) (X : Config d N)
    (μ : Measure (Torus d)) :
    modulatedEnergy (fun x y => c * h x y) X μ = c * modulatedEnergy h X μ := by
  unfold modulatedEnergy
  simp only [integral_const_mul, ← Finset.mul_sum]
  ring

theorem q40b_commKernel_smul (G : Torus d → Euc d) {c : ℝ} (hc : c ≠ 0) (f : Torus d → ℝ) :
    commKernel G (Torus.grad (fun y => c * f y)) =
      fun x y => c * commKernel G (Torus.grad f) x y := by
  funext x y
  unfold commKernel
  simp only [q38_grad_const_mul c hc f]
  split_ifs
  · simp
  · rw [← smul_sub, inner_smul_left]; simp

theorem q40b_ccf_smul (D : DynData d) {c : ℝ} (hc : c ≠ 0) (P : Measure Ω)
    (μ : ℝ → Measure (Torus d)) (X : ℝ≥0 → Ω → Config d N) (f : Torus d → ℝ) (r : ℝ) (ω : Ω) :
    centeredCommutatorForcing d D.s P μ X (fun y => c * f y) r ω =
      c * centeredCommutatorForcing d D.s P μ X f r ω := by
  unfold centeredCommutatorForcing
  rw [q40b_commKernel_smul _ hc f]
  simp only [q40b_modEnergy_smul, integral_const_mul]
  ring


theorem q40b_IR_smul (hd : 2 ≤ d) (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ) (P : Measure Ω)
    (X : ℝ≥0 → Ω → Config d N)
    {ρβ : Torus d → ℝ} (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ)
    (hρS : Torus.IsSmooth ρβ) (hρpos : ∀ x, 0 < ρβ x) {c : ℝ} (hc : c ≠ 0) {φ : Torus d → ℝ}
    (hφ : Torus.IsSmooth φ) {t : ℝ} (ht : 0 ≤ t) (ω : Ω) :
    integratedRemainder htr.dyn ρ P X t (fun x => c * φ x) ω =
      c * integratedRemainder htr.dyn ρ P X t φ ω := by
  rcases ht.eq_or_lt with h0 | hpos
  · subst h0
    simp [integratedRemainder]
  · unfold integratedRemainder
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun r hr => ?_
    have hr' : r ∈ Set.Icc 0 t := by rwa [Set.uIcc_of_le ht] at hr
    rw [q40b_propagator_smul hd htr hρβ hρS hρpos c hφ hpos r hr']
    exact q40b_ccf_smul htr.dyn hc P _ X _ r ω

theorem q40b_projMean_smul (μ : Measure (Torus d)) (c : ℝ) (f : Torus d → ℝ) :
    projMean μ (fun x => c * f x) = fun x => c * projMean μ f x := by
  funext x
  simp only [projMean, pair, integral_const_mul]
  ring

theorem q40b_sobolevNorm_smul (m c : ℝ) (f : Torus d → ℝ) :
    sobolevNorm m (fun x => c * f x) = |c| * sobolevNorm m f := by
  unfold sobolevNorm
  have h1 : Torus.mean (fun x => c * f x) = c * Torus.mean f := by
    unfold Torus.mean; rw [integral_const_mul]
  have h2 : ∀ k : NonzeroLattice d, Torus.funRealCoeff (fun x => c * f x) k =
      c * Torus.funRealCoeff f k := by
    intro k
    unfold Torus.funRealCoeff
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only
    ring
  have h3 : (Torus.mean (fun x => c * f x)) ^ 2 +
      ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (2 * m) * Torus.funRealCoeff (fun x => c * f x) k ^ 2 =
      c ^ 2 * ((Torus.mean f) ^ 2 +
        ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (2 * m) * Torus.funRealCoeff f k ^ 2) := by
    rw [h1, mul_add, ← tsum_mul_left]
    congr 1
    · ring
    · refine tsum_congr fun k => ?_
      rw [h2 k]; ring
  rw [h3, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

theorem q40b_isSmooth_smul (c : ℝ) {f : Torus d → ℝ} (hf : Torus.IsSmooth f) :
    Torus.IsSmooth (fun x => c * f x) := by
  have h : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => c * Torus.lift f z) := contDiff_const.mul hf
  exact h

theorem q40b_R_le (hd : 2 ≤ d) (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ) (P : Measure Ω)
    (X : ℝ≥0 → Ω → Config d N) {ρβ : Torus d → ℝ}
    (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ)
    (hρS : Torus.IsSmooth ρβ) (hρpos : ∀ x, 0 < ρβ x) (j : ℕ) {φ : Torus d → ℝ}
    (hφ : Torus.IsSmooth φ) {t : ℝ} (ht : 0 ≤ t) :
    ∫⁻ ω, ENNReal.ofReal |integratedRemainder htr.dyn ρ P X t φ ω| ∂P ≤
      ENNReal.ofReal (sobolevNorm (j : ℝ) (projMean (withDensityReal ρβ) φ) + 1) *
        criterionRemainder htr.dyn ρ ρβ j P X := by
  set L : ℝ := sobolevNorm (j : ℝ) (projMean (withDensityReal ρβ) φ) with hL
  have hL0 : 0 ≤ L := Real.sqrt_nonneg _
  have hL1 : 0 < L + 1 := by linarith
  set c : ℝ := (L + 1)⁻¹ with hcdef
  have hc0 : 0 < c := inv_pos.2 hL1
  have hψ : Torus.IsSmooth (fun x => c * φ x) := q40b_isSmooth_smul c hφ
  have hle : ∫⁻ ω, ENNReal.ofReal |integratedRemainder htr.dyn ρ P X t (fun x => c * φ x) ω| ∂P ≤
      criterionRemainder htr.dyn ρ ρβ j P X := by
    unfold criterionRemainder
    refine le_iSup_of_le t (le_iSup_of_le ht (le_iSup_of_le (fun x => c * φ x)
      (le_iSup_of_le ⟨PDE.MFLinear.continuous_of_isSmooth hψ,
        PDE.MFSemigroup.memSobolev_of_isSmooth hψ _, ?_⟩ le_rfl)))
    rw [q40b_projMean_smul, q40b_sobolevNorm_smul, abs_of_pos hc0, ← hL, hcdef,
      inv_mul_le_iff₀ hL1]
    linarith
  have heq : ∫⁻ ω, ENNReal.ofReal |integratedRemainder htr.dyn ρ P X t (fun x => c * φ x) ω| ∂P =
      ENNReal.ofReal c * ∫⁻ ω, ENNReal.ofReal |integratedRemainder htr.dyn ρ P X t φ ω| ∂P := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun ω => ?_
    rw [q40b_IR_smul hd htr P X hρβ hρS hρpos hc0.ne' hφ ht ω, abs_mul, abs_of_pos hc0,
      ENNReal.ofReal_mul hc0.le]
  rw [heq] at hle
  have hmul : ENNReal.ofReal (L + 1) * ENNReal.ofReal c = 1 := by
    rw [← ENNReal.ofReal_mul hL1.le, hcdef, mul_inv_cancel₀ hL1.ne', ENNReal.ofReal_one]
  calc ∫⁻ ω, ENNReal.ofReal |integratedRemainder htr.dyn ρ P X t φ ω| ∂P
      = ENNReal.ofReal (L + 1) * (ENNReal.ofReal c *
          ∫⁻ ω, ENNReal.ofReal |integratedRemainder htr.dyn ρ P X t φ ω| ∂P) := by
        rw [← mul_assoc, hmul, one_mul]
    _ ≤ _ := by gcongr

end Scale

end HRS.Q40b
