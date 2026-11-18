/-
# HRS.Equilibrium.Q84dAuxB — packet Q84d: almost-everywhere joint measurability of `𝒥ψ`

For a kernel `ψ` with `IsPairCorrector` the Poisson equation expresses
`𝒥ψ(x,y) = S(x,y) + δ(x) + δ(y)` off the diagonal, with `S` jointly measurable (a combination of
`H_f` and the measurable surrogates of the generator `B` on `ψ(·,y)`) and `δ` a function of one
variable that is a.e.-measurable because `𝒥ψ(x₀,·)` is integrable (`jpair_canonical`).
-/
import HRS.Equilibrium.Q84dAuxA

open MeasureTheory Filter Topology

noncomputable section

namespace HRS.Q84d

variable {d : ℕ} {s : ℝ}

theorem q84d_measurable_swap_arg {F : Torus d → Torus d → ℝ}
    (h : Measurable (fun p : Torus d × Torus d => F p.1 p.2)) :
    Measurable (fun p : Torus d × Torus d => F p.2 p.1) :=
  h.comp measurable_swap

/-- Measurable surrogate for `Bop (ψ(·,y)) x`. -/
def Bsur (d : ℕ) (s : ℝ) (V : Torus d → ℝ) (β : ℝ) (ρ : Torus d → ℝ) (ψ : Torus d → Torus d → ℝ)
    (x y : Torus d) : ℝ :=
  β⁻¹ * ∑ m, hK ψ m x y -
    ∑ m, ((Torus.grad V x + forceField d s ρ x) m) * gK ψ m x y

theorem q84d_Bop_eq {V : Torus d → ℝ} {β : ℝ} {ρ : Torus d → ℝ} {ψ : Torus d → Torus d → ℝ}
    (hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (lift2 ψ) (offDiag d)) {x y : Torus d}
    (hxy : x ≠ y) :
    Bop d s V β ρ (fun z => ψ z y) x = Bsur d s V β ρ ψ x y := by
  unfold Bop Bsur
  rw [q84d_lap_comp hsm hxy]
  congr 1
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [q84d_grad_comp hsm hxy m]
  simp [mul_comm]

theorem q84d_measurable_Bsur {V : Torus d → ℝ} {β : ℝ} {ρ : Torus d → ℝ}
    {ψ : Torus d → Torus d → ℝ} :
    Measurable (fun p : Torus d × Torus d => Bsur d s V β ρ ψ p.1 p.2) := by
  unfold Bsur
  refine (measurable_const.mul (Finset.measurable_sum _ fun m _ => q84d_measurable_hK ψ m)).sub
    (Finset.measurable_sum _ fun m _ => ?_)
  have hV : Measurable (fun p : Torus d × Torus d => (Torus.grad V p.1 + forceField d s ρ p.1) m) := by
    have h1 : Measurable (fun x : Torus d => (Torus.grad V x + forceField d s ρ x)) :=
      (q84d_measurable_grad V).add (q84d_measurable_grad _)
    exact ((EuclideanSpace.proj m).continuous.measurable.comp h1).comp measurable_fst
  exact hV.mul (q84d_measurable_gK ψ m)

theorem q84d_measurable_Hsource {f : Torus d → ℝ} (hsd : s < d) (hf : Torus.IsSmooth f)
    {ρ : Torus d → ℝ} (hρ : IsProbDensity ρ) :
    Measurable (fun p : Torus d × Torus d => Hsource d s ρ f p.1 p.2) := by
  haveI : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hρ
  have hh : Measurable (fun p : Torus d × Torus d => hTransport d s f p.1 p.2) :=
    HRS.LocalDivAux.measurable_hTransport hsd hf
  have hsh : StronglyMeasurable (fun p : Torus d × Torus d => hTransport d s f p.1 p.2) :=
    hh.stronglyMeasurable
  have i1 : Measurable (fun p : Torus d × Torus d => ∫ y', hTransport d s f p.1 y' ∂(withDensityReal ρ)) :=
    (hsh.integral_prod_right' (ν := withDensityReal ρ)).measurable.comp measurable_fst
  have hsw : StronglyMeasurable (fun p : Torus d × Torus d => hTransport d s f p.2 p.1) :=
    (hh.comp measurable_swap).stronglyMeasurable
  have i2 : Measurable (fun p : Torus d × Torus d => ∫ x', hTransport d s f x' p.2 ∂(withDensityReal ρ)) := by
    have := (hsh.integral_prod_left' (μ := withDensityReal ρ)).measurable
    exact this.comp measurable_snd
  unfold Hsource canonicalCenter
  refine measurable_const.mul ?_
  exact (((hh.sub i1).sub i2).add measurable_const)

/-- The measurable part of `𝒥ψ`: `-H_f - B(ψ(·,y))(x) - B(ψ(·,x))(y)`. -/
def Ssur (d : ℕ) (s : ℝ) (V : Torus d → ℝ) (β : ℝ) (ρ : Torus d → ℝ) (f : Torus d → ℝ)
    (ψ : Torus d → Torus d → ℝ) (x y : Torus d) : ℝ :=
  -Hsource d s ρ f x y - Bsur d s V β ρ ψ x y - Bsur d s V β ρ ψ y x

theorem q84d_measurable_Ssur {V : Torus d → ℝ} {β : ℝ} {ρ : Torus d → ℝ} {f : Torus d → ℝ}
    {ψ : Torus d → Torus d → ℝ} (hsd : s < d) (hf : Torus.IsSmooth f) (hρ : IsProbDensity ρ) :
    Measurable (fun p : Torus d × Torus d => Ssur d s V β ρ f ψ p.1 p.2) := by
  have h1 : Measurable (fun p : Torus d × Torus d => -Hsource d s ρ f p.1 p.2) :=
    (q84d_measurable_Hsource hsd hf hρ).neg
  have h2 : Measurable (fun p : Torus d × Torus d => Bsur d s V β ρ ψ p.1 p.2) :=
    q84d_measurable_Bsur
  have h3 : Measurable (fun p : Torus d × Torus d => Bsur d s V β ρ ψ p.2 p.1) :=
    q84d_measurable_swap_arg h2
  simp only [Ssur]
  exact (h1.sub h2).sub h3

/-- Algebraic decomposition of `𝒥ψ` from the Poisson equation. -/
theorem q84d_jpair_decomp {V : Torus d → ℝ} {β : ℝ} {ρ : Torus d → ℝ} {f : Torus d → ℝ} {K₁ : ℝ}
    {ψ : Torus d → Torus d → ℝ} (hψ : IsPairCorrector d s V β ρ f K₁ ψ) :
    ∃ δ : Torus d → ℝ, ∀ x y : Torus d, x ≠ y →
      Jpair d s ρ ψ x y = Ssur d s V β ρ f ψ x y + δ x + δ y := by
  set μ := withDensityReal ρ with hμ
  set c : Torus d → ℝ := fun y => ∫ z, (Bop d s V β ρ (fun w => ψ w y) z +
    Jop d s ρ (fun w => ψ w y) z) ∂μ with hc
  set cJ : Torus d → ℝ := fun y => ∫ z, Jop d s ρ (fun w => ψ w y) z ∂μ with hcJ
  refine ⟨fun y => c y - cJ y, fun x y hxy => ?_⟩
  have hsm := hψ.size.smooth
  have hP := hψ.poisson x y hxy
  have hsymx : (fun z => ψ x z) = fun z => ψ z x := funext fun z => hψ.symm x z
  have e1 : genFst d s V β ρ ψ x y = (Bop d s V β ρ (fun w => ψ w y) x + Jop d s ρ (fun w => ψ w y) x) - c y := by
    unfold genFst projGen projMean pair
    rfl
  have e2 : genSnd d s V β ρ ψ x y = (Bop d s V β ρ (fun w => ψ w x) y + Jop d s ρ (fun w => ψ w x) y) - c x := by
    unfold genSnd projGen projMean pair
    rw [hsymx]
  have e3 : Jpair d s ρ ψ x y = (Jop d s ρ (fun w => ψ w y) x - cJ y) + (Jop d s ρ (fun w => ψ w x) y - cJ x) := by
    unfold Jpair projMean pair
    rw [hsymx]
  have b1 := q84d_Bop_eq (s := s) (V := V) (β := β) (ρ := ρ) hsm hxy
  have b2 := q84d_Bop_eq (s := s) (V := V) (β := β) (ρ := ρ) hsm hxy.symm
  rw [e1, e2, b1, b2] at hP
  rw [e3]
  unfold Ssur
  linarith

end HRS.Q84d

end
