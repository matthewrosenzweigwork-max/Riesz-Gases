import HRS.MS.SpecAux31

/-!
# S8P: the pairing `⟨v, A w⟩` as an integral (S8.7, gap b1, part i, Fubini bridge)

Namespace `HRS.MS.Spec`, helper prefix `s8p_`.  `s8p_polar_eq`: for Schwartz `φ, ψ` and `L²` elements `v' = ψ`, `w = S φ` a.e.,
`ν ⟨v', w⟩ + qf(v', w) = ∫ W_ψ S φ` (`W_ψ = ν ψ + √ρ (g * (√ρ ψ))`), so that `ν⟨v', w⟩ + qf(v', w)` is symmetric in `(φ, ψ)`
(`s8p_gen_symm`).
-/

noncomputable section

open MeasureTheory
open scoped ENNReal RealInnerProductSpace

namespace HRS.MS.Spec

open HRS HRS.Whole HRS.MS.MovDec

variable {d : ℕ} {s : ℝ} {ρ : Euc d → ℝ}

local notation "𝓢R" => SchwartzMap (Euc d) ℝ

theorem s8p_qf_eq_iter {M : ℝ} (h : S8pRho d s ρ M) (ψ : 𝓢R) (v' w : Lp ℝ 2 (volume : Measure (Euc d)))
    (f : Euc d → ℝ) (hv' : ∀ᵐ x ∂(volume : Measure (Euc d)), v' x = ψ x)
    (hw : ∀ᵐ x ∂(volume : Measure (Euc d)), w x = f x) :
    s8p_qf s ρ v' w = ∫ y, (Real.sqrt (ρ y) * f y) *
      HRS.Whole.convFun (rieszKernel d s) (fun z => Real.sqrt (ρ z) * ψ z) y := by
  unfold s8p_qf
  rw [integral_prod_symm _ (s8p_qf_integrable h v' w)]
  have hy : ∀ y : Euc d, ∫ x, s8p_kern d s ρ (x, y) * (v' x * w y) =
      (Real.sqrt (ρ y) * w y) * HRS.Whole.convFun (rieszKernel d s) (fun z => Real.sqrt (ρ z) * ψ z) y := by
    intro y
    unfold HRS.Whole.convFun
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [hv'] with x hx
    unfold s8p_kern
    simp only []
    have : rieszKernel d s (y - x) = rieszKernel d s (x - y) := by
      rw [← neg_sub x y, HRS.MS.MovDec.mov2e_g_even]
    rw [this, hx]
    ring
  simp_rw [hy]
  refine integral_congr_ae ?_
  filter_upwards [hw] with y hy'
  rw [hy']

theorem s8p_polar_eq (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hρ : Mov2eRho d ρ) (hE : Mov2eEll d ρ)
    {M : ℝ} (h : S8pRho d s ρ M) (β : ℝ) (φ ψ : 𝓢R) (v' w : Lp ℝ 2 (volume : Measure (Euc d)))
    (hv' : ∀ᵐ x ∂(volume : Measure (Euc d)), v' x = ψ x)
    (hw : ∀ᵐ x ∂(volume : Measure (Euc d)), w x = movS d s β ρ φ x) :
    β⁻¹ * ⟪v', w⟫ + s8p_qf s ρ v' w = ∫ x, mov2eW d s β ρ ψ x * movS d s β ρ φ x := by
  have hin : ⟪v', w⟫ = ∫ x, ψ x * movS d s β ρ φ x := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hv', hw] with x h1 h2
    rw [h1, h2]
    simp [mul_comm]
  have hI1 : Integrable (fun x => ψ x * movS d s β ρ φ x) := by
    have : Integrable (fun x => (v' x) * (w x)) := (Lp.memLp v').integrable_mul (Lp.memLp w)
    refine this.congr ?_
    filter_upwards [hv', hw] with x h1 h2
    rw [h1, h2]
  obtain ⟨hI2, -⟩ := s8p_WS_integral hd hs0 hsd hρ hE β φ ψ
  rw [hin, s8p_qf_eq_iter h ψ v' w (movS d s β ρ φ) hv' hw]
  have e : (fun x => mov2eW d s β ρ ψ x * movS d s β ρ φ x - β⁻¹ * (ψ x * movS d s β ρ φ x)) =
      fun y => (Real.sqrt (ρ y) * movS d s β ρ φ y) *
        HRS.Whole.convFun (rieszKernel d s) (fun z => Real.sqrt (ρ z) * ψ z) y := by
    funext y
    unfold mov2eW
    ring
  have := integral_sub hI2 (hI1.const_mul β⁻¹)
  rw [integral_const_mul] at this
  rw [← e, this]
  ring

end HRS.MS.Spec
