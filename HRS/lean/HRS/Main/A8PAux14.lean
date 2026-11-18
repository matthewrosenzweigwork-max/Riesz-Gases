import HRS.Main.A8PAux13

/-!
# Packet A8P, part 14: the coercivity bound for one covariance entry
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators MeasureTheory

namespace HRS.Main.A8P

open HRS.GF HRS.Uniform

variable {d : ℕ}

/-- The covariance test bound at one time: `ψ = ⟨∇f,∇g⟩`. -/
theorem a8p_cov_pt {s C₀ Cq Cp : ℝ} (hcom : A8CommSpec d s C₀ Cq) (hCq : 0 ≤ Cq) (hCp0 : 0 ≤ Cp)
    (hCp : ∀ f g : Torus d → ℝ, Torus.IsCk 2 f → Torus.IsCk 2 g →
      MemSobolev (PDE.mStar d : ℝ) f → MemSobolev (PDE.mStar d : ℝ) g →
      HasFiniteHomSobolev (((d : ℝ) - s) / 2) (fun x => inner ℝ (Torus.grad f x) (Torus.grad g x)) ∧
      homSobolev (((d : ℝ) - s) / 2) (fun x => inner ℝ (Torus.grad f x) (Torus.grad g x)) ≤
        Cp * sobolevNorm (PDE.mStar d : ℝ) f * sobolevNorm (PDE.mStar d : ℝ) g)
    {Λ : ℝ} (hΛ : 1 ≤ Λ) {N : ℕ} (hN : 2 ≤ N) {ρ : Torus d → ℝ} (hρ : IsProbDensity ρ)
    (hup : ∀ x, ρ x ≤ Λ) {X : Config d N} (hX : X ∉ collisionSet d N) {f g : Torus d → ℝ}
    (hf : Torus.IsCk 2 f) (hg : Torus.IsCk 2 g) (hmf : MemSobolev (PDE.mStar d : ℝ) f)
    (hmg : MemSobolev (PDE.mStar d : ℝ) g) {Kf Kg Bf Bg : ℝ}
    (hKf : sobolevNorm (PDE.mStar d : ℝ) f ≤ Kf) (hKg : sobolevNorm (PDE.mStar d : ℝ) g ≤ Kg)
    (hBf : Torus.cbNorm 2 f ≤ Bf) (hBg : Torus.cbNorm 2 g ≤ Bg) :
    |∫ x, inner ℝ (Torus.grad f x) (Torus.grad g x) ∂(empirical X) -
        ∫ x, inner ℝ (Torus.grad f x) (Torus.grad g x) * ρ x| ≤
      Cq * (2 * d * Bf * Bg) * smearScale d N Λ +
        Cq * (Cp * Kf * Kg) *
          Real.sqrt (rieszEnergy d s X (withDensityReal ρ) + oNΛ d s C₀ Λ N) := by
  have hbf := gfb2_cbNorm_nonneg f 2
  have hbg := gfb2_cbNorm_nonneg g 2
  obtain ⟨hfin, hhom⟩ := hCp f g hf hg hmf hmg
  obtain ⟨-, -, htest⟩ := hcom Λ hΛ N hN ρ hρ hup X hX
  have hL0 : 0 ≤ 2 * d * Bf * Bg := by
    have : 0 ≤ Bf := hbf.trans hBf
    have : 0 ≤ Bg := hbg.trans hBg
    positivity
  have hlip : KernelGrad.IsLipschitz (2 * d * Bf * Bg)
      (fun x => inner ℝ (Torus.grad f x) (Torus.grad g x)) := by
    intro x y
    refine (a8p_prodgrad_lip hf hg x y).trans ?_
    have htd : 0 ≤ KernelGrad.tdist x y := by unfold KernelGrad.tdist; exact norm_nonneg _
    refine mul_le_mul_of_nonneg_right ?_ htd
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    have := mul_le_mul hBf hBg hbg (hbf.trans hBf)
    nlinarith
  have h := htest _ _ hL0 hlip hfin
  have hmc : ∫ x, inner ℝ (Torus.grad f x) (Torus.grad g x) * ρ x =
      ∫ x, ρ x * inner ℝ (Torus.grad f x) (Torus.grad g x) :=
    integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)
  rw [hmc, ← HRS.PDE.MFPairing.integral_withDensityReal hρ.measurable hρ.nonneg]
  refine h.trans ?_
  have hs0 : 0 ≤ Real.sqrt (rieszEnergy d s X (withDensityReal ρ) + oNΛ d s C₀ Λ N) := Real.sqrt_nonneg _
  have hKf0 : 0 ≤ sobolevNorm (PDE.mStar d : ℝ) f := Real.sqrt_nonneg _
  have hKg0 : 0 ≤ sobolevNorm (PDE.mStar d : ℝ) g := Real.sqrt_nonneg _
  have hhom0 : homSobolev (((d : ℝ) - s) / 2) (fun x => inner ℝ (Torus.grad f x) (Torus.grad g x)) ≤
      Cp * Kf * Kg := by
    refine hhom.trans ?_
    have := mul_le_mul hKf hKg hKg0 (hKf0.trans hKf)
    nlinarith [mul_le_mul_of_nonneg_left this hCp0]
  have := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hhom0 hCq) hs0
  linarith

end HRS.Main.A8P
