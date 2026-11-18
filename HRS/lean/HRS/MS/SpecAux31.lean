import HRS.MS.SpecAux19
import HRS.MS.MovDecAux3

/-!
# S8P: polarised ground-state identity `∫ W_ψ S φ = ∫ ∑ Z^ψ_i Z^φ_i` (S8.7, gap b1, part i, function level)

Namespace `HRS.MS.Spec`, helper prefix `s8p_`.  Polarisation of `mov2e_WS_identity` / `mov2e_energy_identity`
(`HRS.MS.MovDec`): for Schwartz `φ, ψ`, with `W_ψ = ν ψ + √ρ (g * (√ρ ψ))` and `Z^φ_i` the components of `√ρ ∇(A f_φ)`,
`W_ψ · S φ = ∑ Z^ψ_i Z^φ_i - ∑ ∂_i (W_ψ Z^φ_i)`, all terms integrable, the divergence terms integrate to zero.  Hence
`∫ W_ψ S φ = ∫ ∑ Z^ψ_i Z^φ_i` is symmetric in `(φ, ψ)`.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal RealInnerProductSpace

namespace HRS.MS.Spec

open HRS HRS.Whole HRS.MS.MovDec

variable {d : ℕ} {s : ℝ} {ρ : Euc d → ℝ}

local notation "𝓢R" => SchwartzMap (Euc d) ℝ

theorem s8p_WS_pol (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hρ : Mov2eRho d ρ) (hE : Mov2eEll d ρ)
    (β : ℝ) (φ ψ : 𝓢R) (x : Euc d) :
    mov2eW d s β ρ ψ x * movS d s β ρ φ x =
      ∑ i, mov2eZ d s β ρ ψ i x * mov2eZ d s β ρ φ i x -
        ∑ i, fderiv ℝ (fun y => mov2eW d s β ρ ψ y * mov2eZ d s β ρ φ i y) x
          (EuclideanSpace.single i 1) := by
  rw [mov2e_S_eq hd hs0 hsd hρ hE β φ x, mul_neg, Finset.mul_sum, ← Finset.sum_neg_distrib,
    ← Finset.sum_sub_distrib]
  have hmul : ∀ i : Fin d, fderiv ℝ (fun y => mov2eW d s β ρ ψ y * mov2eZ d s β ρ φ i y) x
      (EuclideanSpace.single i 1) =
      (mov2eZ d s β ρ ψ i x + (1 / 2) * gradient (fun y => Real.log (ρ y)) x i * mov2eW d s β ρ ψ x) *
        mov2eZ d s β ρ φ i x +
      mov2eW d s β ρ ψ x * fderiv ℝ (mov2eZ d s β ρ φ i) x (EuclideanSpace.single i 1) := by
    intro i
    have hWd : DifferentiableAt ℝ (mov2eW d s β ρ ψ) x :=
      ((mov2e_W_GD hd hs0 hsd hρ hE β ψ).1.differentiable (by norm_num)) x
    have hZd : DifferentiableAt ℝ (mov2eZ d s β ρ φ i) x :=
      ((mov2e_Z_GD hd hs0 hsd hρ hE β φ i).1.differentiable (by norm_num)) x
    have h1 : fderiv ℝ (fun y => mov2eW d s β ρ ψ y * mov2eZ d s β ρ φ i y) x =
        mov2eW d s β ρ ψ x • fderiv ℝ (mov2eZ d s β ρ φ i) x +
          mov2eZ d s β ρ φ i x • fderiv ℝ (mov2eW d s β ρ ψ) x :=
      (hWd.hasFDerivAt.mul hZd.hasFDerivAt).fderiv
    rw [h1]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [mov2e_W_deriv hd hs0 hsd hρ hE β ψ i x]
    ring
  simp_rw [hmul]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem s8p_WS_integral (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hρ : Mov2eRho d ρ) (hE : Mov2eEll d ρ)
    (β : ℝ) (φ ψ : 𝓢R) :
    Integrable (fun x => mov2eW d s β ρ ψ x * movS d s β ρ φ x) ∧
      ∫ x, mov2eW d s β ρ ψ x * movS d s β ρ φ x =
        ∫ x, ∑ i, mov2eZ d s β ρ ψ i x * mov2eZ d s β ρ φ i x := by
  have hZ : ∀ i : Fin d, Integrable (fun x => mov2eZ d s β ρ ψ i x * mov2eZ d s β ρ φ i x) := fun i =>
    ((mov2e_Z_GD hd hs0 hsd hρ hE β ψ i).mul (mov2e_Z_GD hd hs0 hsd hρ hE β φ i)).integrable
  have hX : ∀ i : Fin d, Mov2eGD (fun y => mov2eW d s β ρ ψ y * mov2eZ d s β ρ φ i y) := fun i =>
    (mov2e_W_GD hd hs0 hsd hρ hE β ψ).mul (mov2e_Z_GD hd hs0 hsd hρ hE β φ i)
  have hD : ∀ i : Fin d, Integrable (fun x => fderiv ℝ (fun y => mov2eW d s β ρ ψ y *
      mov2eZ d s β ρ φ i y) x (EuclideanSpace.single i 1)) := fun i => (hX i).integrable_fderiv _
  have hZs : Integrable (fun x => ∑ i, mov2eZ d s β ρ ψ i x * mov2eZ d s β ρ φ i x) :=
    integrable_finsetSum _ fun i _ => hZ i
  have hDs : Integrable (fun x => ∑ i, fderiv ℝ (fun y => mov2eW d s β ρ ψ y * mov2eZ d s β ρ φ i y) x
      (EuclideanSpace.single i 1)) := integrable_finsetSum _ fun i _ => hD i
  have hid : (fun x => mov2eW d s β ρ ψ x * movS d s β ρ φ x) = fun x =>
      ∑ i, mov2eZ d s β ρ ψ i x * mov2eZ d s β ρ φ i x -
      ∑ i, fderiv ℝ (fun y => mov2eW d s β ρ ψ y * mov2eZ d s β ρ φ i y) x (EuclideanSpace.single i 1) :=
    funext fun x => s8p_WS_pol hd hs0 hsd hρ hE β φ ψ x
  rw [hid]
  refine ⟨hZs.sub hDs, ?_⟩
  rw [integral_sub hZs hDs, integral_finset_sum _ fun i _ => hD i]
  have : ∑ i : Fin d, ∫ x, fderiv ℝ (fun y => mov2eW d s β ρ ψ y * mov2eZ d s β ρ φ i y) x
      (EuclideanSpace.single i 1) = 0 :=
    Finset.sum_eq_zero fun i _ => (hX i).integral_fderiv_zero _
  rw [this, sub_zero]

/-- **Symmetry of the polarised energy form**: `∫ W_ψ S φ = ∫ W_φ S ψ`. -/
theorem s8p_WS_symm (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hρ : Mov2eRho d ρ) (hE : Mov2eEll d ρ)
    (β : ℝ) (φ ψ : 𝓢R) :
    ∫ x, mov2eW d s β ρ ψ x * movS d s β ρ φ x = ∫ x, mov2eW d s β ρ φ x * movS d s β ρ ψ x := by
  rw [(s8p_WS_integral hd hs0 hsd hρ hE β φ ψ).2, (s8p_WS_integral hd hs0 hsd hρ hE β ψ φ).2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

end HRS.MS.Spec
