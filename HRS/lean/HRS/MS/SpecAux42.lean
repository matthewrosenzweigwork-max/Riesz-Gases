import HRS.MS.SpecAux41

/-!
# S8P: Hardy-type bound for the ground-state gradient (S8.7, packet b6)

Namespace `HRS.MS.Spec`, helper prefix `s8p_`.  For a Schwartz function `S` and `ℓ = ∇ log ρ`, `D_j S = ∂_j S - ½ ℓ_j S`:
`∫ |∇S|² + ¼ ∫ |ℓ|² S² ≤ ∫ |D S|² + ½ d Df ∫ S²` (integration by parts of `S² ℓ_j`, `Df` a bound of `∇ℓ`).
-/

noncomputable section

open MeasureTheory
open scoped ENNReal RealInnerProductSpace ContDiff

namespace HRS.MS.Spec

open HRS HRS.Whole HRS.MS.MovDec

variable {d : ℕ} {ρ : Euc d → ℝ}

local notation "𝓢R" => SchwartzMap (Euc d) ℝ

/-- The partial derivative `∂_j S`. -/
abbrev s8p_pd (S : Euc d → ℝ) (j : Fin d) (x : Euc d) : ℝ := fderiv ℝ S x (EuclideanSpace.single j 1)

/-- `ℓ_j = ∂_j log ρ`. -/
abbrev s8p_ell (ρ : Euc d → ℝ) (j : Fin d) (x : Euc d) : ℝ := gradient (fun y => Real.log (ρ y)) x j

/-- The ground-state derivative `D_j S = ∂_j S - ½ ℓ_j S`. -/
def s8p_Dj (ρ : Euc d → ℝ) (S : Euc d → ℝ) (j : Fin d) (x : Euc d) : ℝ :=
  s8p_pd S j x - (1 / 2) * s8p_ell ρ j x * S x

theorem s8p_ell_bounds (hE : Mov2eEll d ρ) :
    ∃ Df : ℝ, 0 ≤ Df ∧ ∀ x (j : Fin d), |fderiv ℝ (fun y => s8p_ell ρ j y) x (EuclideanSpace.single j 1)| ≤ Df := by
  obtain ⟨c, a, M0, -, ha, hM0, -, hs, hlin, hD⟩ := hE.ex
  obtain ⟨Df, hDf⟩ := hD 1 le_rfl
  have hDf0 : 0 ≤ Df := (norm_nonneg _).trans (hDf 0)
  refine ⟨Df, hDf0, fun x j => ?_⟩
  have hsm : ContDiff ℝ 1 (fun y => gradient (fun z => Real.log (ρ z)) y) :=
    hs.of_le (by exact_mod_cast le_top)
  have hdiff : DifferentiableAt ℝ (fun y => gradient (fun z => Real.log (ρ z)) y) x :=
    hsm.differentiable (by norm_num) x
  have h1 : fderiv ℝ (fun y => s8p_ell ρ j y) x =
      (EuclideanSpace.proj j : Euc d →L[ℝ] ℝ).comp (fderiv ℝ (fun y => gradient (fun z => Real.log (ρ z)) y) x) :=
    ((EuclideanSpace.proj j : Euc d →L[ℝ] ℝ).hasFDerivAt.comp x hdiff.hasFDerivAt).fderiv
  rw [h1]
  have h2 := hDf x
  rw [norm_iteratedFDeriv_one] at h2
  have h3 : ‖(EuclideanSpace.proj j : Euc d →L[ℝ] ℝ).comp (fderiv ℝ (fun y => gradient (fun z => Real.log (ρ z)) y) x)‖
      ≤ Df := by
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    have := HRS.MS.MovForce.movb2_norm_proj_le (d := d) j
    nlinarith [norm_nonneg (fderiv ℝ (fun y => gradient (fun z => Real.log (ρ z)) y) x)]
  have h4 : ‖(EuclideanSpace.single j (1 : ℝ) : Euc d)‖ ≤ 1 := by simp
  calc |((EuclideanSpace.proj j : Euc d →L[ℝ] ℝ).comp (fderiv ℝ (fun y => gradient (fun z => Real.log (ρ z)) y) x))
        (EuclideanSpace.single j 1)|
      ≤ ‖(EuclideanSpace.proj j : Euc d →L[ℝ] ℝ).comp (fderiv ℝ (fun y => gradient (fun z => Real.log (ρ z)) y) x)‖ *
          ‖(EuclideanSpace.single j (1 : ℝ) : Euc d)‖ := by
        rw [← Real.norm_eq_abs]; exact ContinuousLinearMap.le_opNorm _ _
    _ ≤ Df * 1 := mul_le_mul h3 h4 (norm_nonneg _) hDf0
    _ = Df := mul_one _

theorem s8p_hardy_j (hE : Mov2eEll d ρ) {Df : ℝ}
    (hDf : ∀ x (j : Fin d), |fderiv ℝ (fun y => s8p_ell ρ j y) x (EuclideanSpace.single j 1)| ≤ Df)
    (S : 𝓢R) (j : Fin d) :
    Integrable (fun x => s8p_pd S j x ^ 2) ∧ Integrable (fun x => s8p_ell ρ j x ^ 2 * S x ^ 2) ∧
      Integrable (fun x => s8p_Dj ρ S j x ^ 2) ∧
      (∫ x, s8p_pd S j x ^ 2) + (1 / 4) * ∫ x, s8p_ell ρ j x ^ 2 * S x ^ 2 ≤
        (∫ x, s8p_Dj ρ S j x ^ 2) + (Df / 2) * ∫ x, S x ^ 2 := by
  have hℓ := hE.ell_PB j
  have hℓd : ContDiff ℝ 1 (fun y => s8p_ell ρ j y) := hℓ.1
  have hSGD : Mov2eGD (S : Euc d → ℝ) := mov2e_schwartz_GD S
  have hpd : Mov2eGD (fun x => s8p_pd S j x) := mov2e_schwartz_pderiv_GD S _
  have hX : Mov2eGD (fun y => S y * S y * s8p_ell ρ j y) := (hSGD.mul hSGD).mul_pb hℓ
  have hDGD : Mov2eGD (fun x => s8p_Dj ρ S j x) := by
    have := hpd.sub ((hSGD.mul_pb hℓ).const_mul (1 / 2))
    have e : (fun x => s8p_Dj ρ S j x) = fun x => s8p_pd S j x - (1 / 2) * (S x * s8p_ell ρ j x) := by
      funext x; unfold s8p_Dj; ring
    rw [e]; exact this
  -- integrability of the pieces
  have Ia : Integrable (fun x => s8p_pd S j x ^ 2) :=
    (hpd.mul hpd).integrable.congr (Filter.Eventually.of_forall fun x => by simp [sq])
  have hbGD : Mov2eGD (fun x => S x * S x * (s8p_ell ρ j x * s8p_ell ρ j x)) :=
    (hSGD.mul hSGD).mul_pb (hℓ.mul hℓ)
  have Ib : Integrable (fun x => s8p_ell ρ j x ^ 2 * S x ^ 2) :=
    hbGD.integrable.congr (Filter.Eventually.of_forall fun x => by simp only [sq]; ring)
  have ID : Integrable (fun x => s8p_Dj ρ S j x ^ 2) :=
    (hDGD.mul hDGD).integrable.congr (Filter.Eventually.of_forall fun x => by simp [sq])
  have IS2 : Integrable (fun x => S x ^ 2) :=
    (hSGD.mul hSGD).integrable.congr (Filter.Eventually.of_forall fun x => by simp [sq])
  have hcc : Continuous (fun x => fderiv ℝ (fun y => s8p_ell ρ j y) x (EuclideanSpace.single j 1)) :=
    (hℓd.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have Ic : Integrable (fun x => S x ^ 2 * fderiv ℝ (fun y => s8p_ell ρ j y) x (EuclideanSpace.single j 1)) := by
    refine Integrable.mono' (IS2.const_mul Df) ((S.continuous.pow 2).mul hcc).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _)]
    exact mul_comm Df _ ▸ mul_le_mul_of_nonneg_left (hDf x j) (sq_nonneg _)
  have Ie : Integrable (fun x => fderiv ℝ (fun y => S y * S y * s8p_ell ρ j y) x
      (EuclideanSpace.single j 1)) := hX.integrable_fderiv _
  have He0 : ∫ x, fderiv ℝ (fun y => S y * S y * s8p_ell ρ j y) x (EuclideanSpace.single j 1) = 0 :=
    hX.integral_fderiv_zero _
  -- pointwise identity
  have hpt : ∀ x, s8p_Dj ρ S j x ^ 2 = s8p_pd S j x ^ 2 + (1 / 4) * (s8p_ell ρ j x ^ 2 * S x ^ 2) +
      (1 / 2) * (S x ^ 2 * fderiv ℝ (fun y => s8p_ell ρ j y) x (EuclideanSpace.single j 1)) -
      (1 / 2) * fderiv ℝ (fun y => S y * S y * s8p_ell ρ j y) x (EuclideanSpace.single j 1) := by
    intro x
    have hSd : HasFDerivAt (S : Euc d → ℝ) (fderiv ℝ S x) x := S.differentiableAt.hasFDerivAt
    have hLd : HasFDerivAt (fun y => s8p_ell ρ j y) (fderiv ℝ (fun y => s8p_ell ρ j y) x) x :=
      (hℓd.differentiable one_ne_zero x).hasFDerivAt
    have h1 : fderiv ℝ (fun y => S y * S y * s8p_ell ρ j y) x = _ :=
      (((hSd.mul hSd).mul hLd : HasFDerivAt (fun y => S y * S y * s8p_ell ρ j y) _ x)).fderiv
    rw [h1]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, Pi.mul_apply]
    unfold s8p_Dj
    ring
  have hint : ∫ x, s8p_Dj ρ S j x ^ 2 = (∫ x, s8p_pd S j x ^ 2) + (1 / 4) * (∫ x, s8p_ell ρ j x ^ 2 * S x ^ 2) +
      (1 / 2) * (∫ x, S x ^ 2 * fderiv ℝ (fun y => s8p_ell ρ j y) x (EuclideanSpace.single j 1)) := by
    simp_rw [hpt]
    have I1 : Integrable (fun x => s8p_pd S j x ^ 2 + (1 / 4) * (s8p_ell ρ j x ^ 2 * S x ^ 2)) :=
      Ia.add (Ib.const_mul _)
    have I2 : Integrable (fun x => s8p_pd S j x ^ 2 + (1 / 4) * (s8p_ell ρ j x ^ 2 * S x ^ 2) +
        (1 / 2) * (S x ^ 2 * fderiv ℝ (fun y => s8p_ell ρ j y) x (EuclideanSpace.single j 1))) :=
      I1.add (Ic.const_mul _)
    rw [integral_sub I2 (Ie.const_mul _), integral_add I1 (Ic.const_mul _), integral_add Ia (Ib.const_mul _),
      integral_const_mul, integral_const_mul, integral_const_mul, He0]
    ring
  have hlow : -(Df * ∫ x, S x ^ 2) ≤ ∫ x, S x ^ 2 * fderiv ℝ (fun y => s8p_ell ρ j y) x (EuclideanSpace.single j 1) := by
    have := integral_mono (IS2.const_mul Df).neg Ic (f := fun x => -(Df * S x ^ 2))
      (g := fun x => S x ^ 2 * fderiv ℝ (fun y => s8p_ell ρ j y) x (EuclideanSpace.single j 1)) (fun x => by
        have h1 := (abs_le.1 (hDf x j)).1
        nlinarith [sq_nonneg (S x)])
    rwa [integral_neg, integral_const_mul] at this
  refine ⟨Ia, Ib, ID, ?_⟩
  rw [hint]
  nlinarith [hlow]

end HRS.MS.Spec
