import HRS.MS.Fp81S21Uniform
import HRS.MS.WhoAux4
import HRS.MS.S104eC5B

/-! Auxiliary definitions and identities for the G4 generator estimate. -/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory
open scoped ENNReal BigOperators
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3

def fp81s21_g4J (d : ℕ) (f : Euc d → ℝ) : ℝ :=
  (weightedSobolevE 2 (2 * (d : ℝ) + 4) f).toReal ^ 2

def fp81s21_g4Phys (p : Parameters)
    (P : (δ : ℝ) → Trajectory p δ → Prop) : Prop :=
  ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
    ∀ δ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ, P δ R

def fp81s21_g4N (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (q : ℝ) (f : Euc p.d → ℝ) (x : Euc p.d) : ℝ :=
  ∑ k : Fin p.d,
    (convGradConvW (rieszKernelGrad p.d p.s)
      (fun y => R.ρ q y *
        (HRS.Torus.matVec (r26t3_coeff R).M.transpose (gradient f y)) k) x) k

/-- The physical assumptions put the gradient kernel below the integrability threshold. -/
theorem fp81s21_g4_kernel_exponent (p : Parameters) : p.s + 1 < (p.d : ℝ) := by
  have hd : (2 : ℝ) ≤ p.d := by exact_mod_cast p.hd
  linarith [p.hs]

/-- The nonlocal expression is exactly the term subtracted in the generator. -/
theorem fp81s21_g4_generator_eq (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (q : ℝ) (f : Euc p.d → ℝ) (x : Euc p.d) :
    generatorW (r26t3_coeff R) q f x =
      (r26t3_coeff R).ν * Laplacian.laplacian f x +
        inner ℝ ((r26t3_coeff R).drift q x) (gradient f x) - fp81s21_g4N p R q f x := by
  rfl

theorem fp81s21_g4J_nonneg (d : ℕ) (f : Euc d → ℝ) : 0 ≤ fp81s21_g4J d f :=
  sq_nonneg _

/-- Weighted cancellation-convolution estimate for one coordinate.  The decay
hypothesis ensures that the vector Bochner integral agrees with `ultK`. -/
theorem fp81s21_g4_convolution_weighted (p : Parameters) (k : Fin p.d)
    {P : ℝ} (hP : 0 ≤ P) (hPd : (p.d : ℝ) / 2 < P) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {L A : ℝ}, (p.d : ℝ) < L → 0 ≤ A →
      ∀ {g : Euc p.d → ℝ}, U2Dec 1 L A g →
      HRS.MS.Who.wSq P (fun x => ‖(convGradConvW (rieszKernelGrad p.d p.s) g x) k‖) ≤
        ENNReal.ofReal C *
          (HRS.MS.Who.wSq P (fun x => ‖g x‖) +
            (∫⁻ y, ENNReal.ofReal ‖g y‖) ^ 2 * HRS.MS.Who.wtMass (d := p.d) P) := by
  have hd : 1 ≤ p.d := le_trans (by decide) p.hd
  have hsd : p.s < (p.d : ℝ) := by linarith [p.hs]
  have hk := HRS.MS.Ul.ult_ker_kap p.hs0 hsd k
  obtain ⟨C, hC, hbound⟩ := HRS.MS.Who.who_ultK_wSq (F := ℝ) hd hP hPd hk
    (fp81s21_g4_kernel_exponent p)
  refine ⟨C, hC, ?_⟩
  intro L A hL hA g hg
  have heq : (fun x => (convGradConvW (rieszKernelGrad p.d p.s) g x) k) =
      HRS.MS.Ul.ultK (u2_kap p.d p.s k) g := by
    funext x
    exact (HRS.MS.Ul.ult_conv_comp hd p.hs0 hsd hL hA hg x).2 k
  have hw := congrArg (fun h : Euc p.d → ℝ =>
    HRS.MS.Who.wSq P (fun x => ‖h x‖)) heq
  rw [hw]
  exact hbound hg.1.continuous

/-- The first spatial jet of the moving density has a time-uniform decay
bound at every polynomial order. -/
theorem fp81s21_g4_density_decay (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (n : ℕ) : ∃ A : ℝ, 0 ≤ A ∧ ∀ q : ℝ, 0 ≤ q → U2Dec 1 (n : ℝ) A (R.ρ q) := by
  have hsd : p.s < (p.d : ℝ) := by linarith [p.hs]
  exact HRS.MS.S104e.c5_rho_unif p.hd p.hs0 hsd p.ha p.hβ δ p.c₁ p.C₁ 1 n
    (by omega) R.thermal R.resulting

/-- Multiplying a bounded first jet by the density gives the decay needed
for the coordinate convolution, with a constant uniform in time. -/
theorem fp81s21_g4_density_product_decay (p : Parameters) {δ : ℝ}
    (R : Trajectory p δ) (n : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ q : ℝ, 0 ≤ q →
      ∀ (φ : Euc p.d → ℝ), ContDiff ℝ 1 φ →
      ∀ B : ℝ, (∀ i ≤ 1, ∀ y, ‖iteratedFDeriv ℝ i φ y‖ ≤ B) →
        U2Dec 1 (n : ℝ) (A * B * 2 ^ 1) (fun y => R.ρ q y * φ y) := by
  obtain ⟨A, hA, hρ⟩ := fp81s21_g4_density_decay p R n
  exact ⟨A, hA, fun q hq φ hφ B hB => HRS.MS.Who.who_u2dec_mul (hρ q hq) hφ hB⟩

#print axioms HRS.Fp81.S21.fp81s21_g4_density_product_decay
#print axioms HRS.Fp81.S21.fp81s21_g4_density_decay
#print axioms HRS.Fp81.S21.fp81s21_g4_convolution_weighted
#print axioms HRS.Fp81.S21.fp81s21_g4_kernel_exponent
#print axioms HRS.Fp81.S21.fp81s21_g4_generator_eq
#print axioms HRS.Fp81.S21.fp81s21_g4J_nonneg
end HRS.Fp81.S21
