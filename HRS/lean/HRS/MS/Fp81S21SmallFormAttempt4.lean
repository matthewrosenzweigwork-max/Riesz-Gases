import HRS.MS.Fp81S21SmallForm

/-!
# S2.1(iii), packet 3, attempt 4: generator-difference decomposition

This file records the exact decomposition of the moving generator relative to the
thermal generator.  In this repository `WholeCoeff.drift` is the full mean-field
drift, including the density-dependent interaction force.  Consequently the drift
contribution does not cancel; its local-force part is controlled separately by the
class-uniform estimate from `Fp81S21SmallForm`.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators RealInnerProductSpace
open HRS HRS.Whole

namespace HRS.Fp81.S21

/-- Exact moving-minus-thermal generator decomposition.  The viscosity is common,
while the full drift and the differentiated-force convolution both vary with the
density. -/
theorem sol13_generator_difference_decomposition
    {p : HRS.MS.R26T3.Parameters} {δ : ℝ}
    (R : HRS.MS.R26T3.Trajectory p δ) (t : ℝ)
    (f : Euc p.d → ℝ) (x : Euc p.d) :
    let Cₜ := HRS.MS.R26T3.r26t3_coeff R
    let Cstar := (quadraticGradientDyn p.d p.s p.a p.β).coeff (fun _ => R.ρβ)
    generatorW Cₜ t f x - generatorW Cstar 0 f x =
      inner ℝ (Cₜ.drift t x - Cstar.drift 0 x) (gradient f x) -
        ∑ j : Fin p.d,
          ((convGradConvW (rieszKernelGrad p.d p.s)
              (fun y => Cₜ.ρ t y *
                (Torus.matVec Cₜ.M.transpose (gradient f y)) j) x) j -
            (convGradConvW (rieszKernelGrad p.d p.s)
              (fun y => Cstar.ρ 0 y *
                (Torus.matVec Cstar.M.transpose (gradient f y)) j) x) j) := by
  dsimp
  simp only [HRS.MS.R26T3.r26t3_coeff, WholeDyn.coeff, quadraticGradientDyn,
    generatorW]
  rw [Finset.sum_sub_distrib]
  simp only [inner_sub_left]
  abel

/-- The interaction contribution to the moving drift is controlled pointwise by
the already-proved class-uniform local-force bound. -/
theorem sol13_drift_interaction_pointwise_bound (p : HRS.MS.R26T3.Parameters) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 2 →
      ∀ R : HRS.MS.R26T3.Trajectory p δ, ∀ t : ℝ, 0 ≤ t →
      ∀ x : Euc p.d,
    ‖(HRS.MS.R26T3.r26t3_coeff R).drift t x -
          ((quadraticGradientDyn p.d p.s p.a p.β).coeff
            (fun _ => R.ρβ)).drift 0 x‖ ≤
          C * δ * Real.exp (-p.c₁ * t) := by
  obtain ⟨C, hC, hforce⟩ := sol13_local_force_difference_bound p
  refine ⟨C, hC, fun δ hδ hδh R t ht x => ?_⟩
  have hmove : (HRS.MS.R26T3.r26t3_coeff R).drift t x =
      -convGradConvW (rieszKernelGrad p.d p.s) (R.ρ t) x - gradient (confinement p.a) x := by
    simp [HRS.MS.R26T3.r26t3_coeff, WholeDyn.coeff, quadraticGradientDyn,
      meanFieldDriftW, Torus.matVec]
  have hstat : ((quadraticGradientDyn p.d p.s p.a p.β).coeff
        (fun _ => R.ρβ)).drift 0 x =
      -convGradConvW (rieszKernelGrad p.d p.s) R.ρβ x - gradient (confinement p.a) x := by
    simp [WholeDyn.coeff, quadraticGradientDyn, meanFieldDriftW,
      Torus.matVec]
  have hnorm : ‖(HRS.MS.R26T3.r26t3_coeff R).drift t x -
      ((quadraticGradientDyn p.d p.s p.a p.β).coeff
        (fun _ => R.ρβ)).drift 0 x‖ =
      ‖convGradConvW (rieszKernelGrad p.d p.s) (R.ρ t) x -
        convGradConvW (rieszKernelGrad p.d p.s) R.ρβ x‖ := by
    rw [hmove, hstat]
    let Fₜ := convGradConvW (rieszKernelGrad p.d p.s) (R.ρ t) x
    let Fstar := convGradConvW (rieszKernelGrad p.d p.s) R.ρβ x
    let g := gradient (confinement p.a) x
    change ‖(-Fₜ - g) - (-Fstar - g)‖ = ‖Fₜ - Fstar‖
    have hvec : (-Fₜ - g) - (-Fstar - g) = -(Fₜ - Fstar) := by abel
    rw [hvec, norm_neg]
  rw [hnorm]
  exact hforce δ hδ hδh R t ht x

/-- The local drift part of the generator form is bounded by the same decaying
class-uniform coefficient times the pointwise gradient. -/
theorem sol13_local_drift_form_pointwise_bound (p : HRS.MS.R26T3.Parameters) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 2 →
      ∀ R : HRS.MS.R26T3.Trajectory p δ, ∀ t : ℝ, 0 ≤ t →
      ∀ f : Euc p.d → ℝ, ∀ x : Euc p.d,
        |inner ℝ
            ((HRS.MS.R26T3.r26t3_coeff R).drift t x -
              ((quadraticGradientDyn p.d p.s p.a p.β).coeff
                (fun _ => R.ρβ)).drift 0 x)
            (gradient f x)| ≤
          C * δ * Real.exp (-p.c₁ * t) * ‖gradient f x‖ := by
  obtain ⟨C, hC, hdrift⟩ := sol13_drift_interaction_pointwise_bound p
  refine ⟨C, hC, fun δ hδ hδh R t ht f x => ?_⟩
  calc
    |inner ℝ
        ((HRS.MS.R26T3.r26t3_coeff R).drift t x -
          ((quadraticGradientDyn p.d p.s p.a p.β).coeff
            (fun _ => R.ρβ)).drift 0 x)
        (gradient f x)| ≤
      ‖(HRS.MS.R26T3.r26t3_coeff R).drift t x -
        ((quadraticGradientDyn p.d p.s p.a p.β).coeff
          (fun _ => R.ρβ)).drift 0 x‖ * ‖gradient f x‖ :=
        abs_real_inner_le_norm _ _
    _ ≤ (C * δ * Real.exp (-p.c₁ * t)) * ‖gradient f x‖ :=
      mul_le_mul_of_nonneg_right (hdrift δ hδ hδh R t ht x) (norm_nonneg _)

end HRS.Fp81.S21

#print axioms HRS.Fp81.S21.sol13_generator_difference_decomposition
#print axioms HRS.Fp81.S21.sol13_drift_interaction_pointwise_bound
#print axioms HRS.Fp81.S21.sol13_local_drift_form_pointwise_bound
