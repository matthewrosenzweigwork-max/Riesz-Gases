import HRS.MS.Fp81S21SmallFormFull

/-!
# S2.1(iii), packet 3: final generator small-form assembly

The drift estimate and the finite sum of componentwise convolution estimates
combine in the thermal weighted L² norm.  All constants are selected from the
fixed class parameters before the trajectory and test function binders.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators RealInnerProductSpace
open HRS HRS.Whole HRS.MS.MovOsc HRS.MS.MovAdj

namespace HRS.Fp81.S21

private theorem fp81s21_eLpNorm_two_toReal_full2 {d : ℕ} {μ : Measure (Euc d)}
    {f : Euc d → ℝ} (hf : MemLp f 2 μ) :
    (eLpNorm f 2 μ).toReal = Real.sqrt (∫ x, f x ^ 2 ∂μ) := by
  rw [hf.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num),
    ENNReal.toReal_ofReal (by positivity)]
  simp [Real.sqrt_eq_rpow]

private theorem fp81s21_finset_L2_bound_full2 {d : ℕ} {μ : Measure (Euc d)}
    (S : Finset (Fin d)) (g : Fin d → Euc d → ℝ)
    (hmem : ∀ j ∈ S, MemLp (g j) 2 μ) :
    MemLp (fun x => ∑ j ∈ S, g j x) 2 μ ∧
      Real.sqrt (∫ x, (∑ j ∈ S, g j x) ^ 2 ∂μ) ≤
        ∑ j ∈ S, Real.sqrt (∫ x, (g j x) ^ 2 ∂μ) := by
  classical
  have hsumMem : MemLp (fun x => ∑ j ∈ S, g j x) 2 μ :=
    memLp_finsetSum _ hmem
  have htermsTop : (∑ j ∈ S, eLpNorm (g j) 2 μ) ≠ ⊤ :=
    (ENNReal.sum_lt_top.2 fun j hj =>
      lt_top_iff_ne_top.mpr (hmem j hj).eLpNorm_ne_top).ne
  have hsumNorm : eLpNorm (fun x => ∑ j ∈ S, g j x) 2 μ ≤
      ∑ j ∈ S, eLpNorm (g j) 2 μ := by
    calc
      eLpNorm (fun x => ∑ j ∈ S, g j x) 2 μ =
          eLpNorm (∑ j ∈ S, g j) 2 μ := by
        congr 1
        funext x
        simp
      _ ≤ ∑ j ∈ S, eLpNorm (g j) 2 μ :=
        eLpNorm_sum_le (μ := μ) (p := (2 : ℝ≥0∞))
          (f := g) (s := S) (by norm_num)
  refine ⟨hsumMem, ?_⟩
  calc
    Real.sqrt (∫ x, (∑ j ∈ S, g j x) ^ 2 ∂μ) =
        (eLpNorm (fun x => ∑ j ∈ S, g j x) 2 μ).toReal :=
      (fp81s21_eLpNorm_two_toReal_full2 hsumMem).symm
    _ ≤ (∑ j ∈ S, eLpNorm (g j) 2 μ).toReal :=
      ENNReal.toReal_mono htermsTop hsumNorm
    _ = ∑ j ∈ S, (eLpNorm (g j) 2 μ).toReal := by
      rw [ENNReal.toReal_sum fun j hj => (hmem j hj).eLpNorm_ne_top]
    _ = ∑ j ∈ S, Real.sqrt (∫ x, (g j x) ^ 2 ∂μ) := by
      refine Finset.sum_congr rfl fun j hj => ?_
      exact fp81s21_eLpNorm_two_toReal_full2 (hmem j hj)

private theorem fp81s21_L2_add_full2 {d : ℕ} {μ : Measure (Euc d)}
    {u v : Euc d → ℝ} (hu : MemLp u 2 μ) (hv : MemLp v 2 μ) :
    MemLp (fun x => u x + v x) 2 μ ∧
      Real.sqrt (∫ x, (u x + v x) ^ 2 ∂μ) ≤
        Real.sqrt (∫ x, u x ^ 2 ∂μ) + Real.sqrt (∫ x, v x ^ 2 ∂μ) := by
  have huv : MemLp (fun x => u x + v x) 2 μ := hu.add hv
  have hsum : eLpNorm (fun x => u x + v x) 2 μ ≤ eLpNorm u 2 μ + eLpNorm v 2 μ :=
    eLpNorm_add_le (by norm_num)
  have htop : eLpNorm u 2 μ + eLpNorm v 2 μ ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨hu.eLpNorm_ne_top, hv.eLpNorm_ne_top⟩
  refine ⟨huv, ?_⟩
  calc
    Real.sqrt (∫ x, (u x + v x) ^ 2 ∂μ) =
        (eLpNorm (fun x => u x + v x) 2 μ).toReal :=
      (fp81s21_eLpNorm_two_toReal_full2 huv).symm
    _ ≤ (eLpNorm u 2 μ + eLpNorm v 2 μ).toReal := ENNReal.toReal_mono htop hsum
    _ = (eLpNorm u 2 μ).toReal + (eLpNorm v 2 μ).toReal :=
      ENNReal.toReal_add hu.eLpNorm_ne_top hv.eLpNorm_ne_top
    _ = Real.sqrt (∫ x, u x ^ 2 ∂μ) + Real.sqrt (∫ x, v x ^ 2 ∂μ) := by
      rw [fp81s21_eLpNorm_two_toReal_full2 hu, fp81s21_eLpNorm_two_toReal_full2 hv]

/-- The full moving-minus-thermal generator difference has the common-radius
small-form bound under the thermal probability measure. -/
theorem sol13_small_form (p : HRS.MS.R26T3.Parameters) :
    ∃ C_D : ℝ, 0 ≤ C_D ∧
      ∀ (δ : ℝ), 0 < δ → δ ≤ 1 / 2 →
        ∀ (R : HRS.MS.R26T3.Trajectory p δ),
          ∀ (t : ℝ), 0 ≤ t →
            ∀ (f : Euc p.d → ℝ), MemCb 2 f →
              MemLp
                (fun x =>
                  generatorW (HRS.MS.R26T3.r26t3_coeff R) t f x -
                    generatorW ((quadraticGradientDyn p.d p.s p.a p.β).coeff
                      (fun _ => R.ρβ)) 0 f x)
                2 (HRS.Whole.withDensityReal R.ρβ) ∧
              (∫ x,
                (generatorW (HRS.MS.R26T3.r26t3_coeff R) t f x -
                  generatorW ((quadraticGradientDyn p.d p.s p.a p.β).coeff
                    (fun _ => R.ρβ)) 0 f x) ^ 2
                ∂(HRS.Whole.withDensityReal R.ρβ)) ≤
                (C_D * δ * Real.exp (-p.c₁ * t)) ^ 2 *
                  ∫ x, ‖gradient f x‖ ^ 2 ∂(HRS.Whole.withDensityReal R.ρβ) := by
  obtain ⟨Cdrift, hCdrift, hdriftBound⟩ :=
    sol13_local_drift_form_pointwise_bound p
  obtain ⟨CNL, hCNL, hnonlocal⟩ := sol13_nonlocal_component_estimates p
  let C_D : ℝ := Cdrift + (p.d : ℝ) * CNL
  have hCD : 0 ≤ C_D := by
    dsimp [C_D]
    positivity
  refine ⟨C_D, hCD, ?_⟩
  intro δ hδ hδh R t ht f hf
  let μstar : Measure (Euc p.d) := HRS.Whole.withDensityReal R.ρβ
  have hρstar : HRS.Whole.IsProbDensity R.ρβ := R.thermal.1.1
  have hμprob : IsProbabilityMeasure μstar := HRS.Whole.Q34.isProbabilityMeasure_nu hρstar
  letI : IsProbabilityMeasure μstar := hμprob
  have hcb := HRS.MS.S111X2.s111x2_cbNorm_bounds hf
  let B1 : ℝ := HRS.cbNorm 2 f
  let B2 : ℝ := HRS.cbNorm 2 f
  have Hf : HRS.MS.S111X2.CbD f B1 B2 := by
    simpa [B1, B2] using hcb.2
  have hB1 : 0 ≤ B1 := Hf.B1_nonneg
  have hgradCont : Continuous (gradient f) :=
    HRS.MS.S111X2.s111x2_gradient_continuous (Hf.smooth.of_le (by norm_num))
  have hgradm : Measurable (gradient f) := hgradCont.measurable
  have hgradB : ∀ x, ‖gradient f x‖ ≤ B1 := by
    intro x
    rw [HRS.MS.S111X2.s111x2_norm_gradient]
    exact Hf.d1 x
  have hgradSqI : Integrable (fun x => ‖gradient f x‖ ^ 2) μstar := by
    have hmajor : Integrable (fun _ : Euc p.d => B1 ^ 2) μstar := integrable_const _
    refine hmajor.mono' (measurable_norm.comp hgradm |>.pow_const 2).aestronglyMeasurable ?_
    filter_upwards with x
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    calc
      ‖gradient f x‖ ^ 2 = ‖gradient f x‖ * ‖gradient f x‖ := by ring
      _ ≤ B1 * B1 := mul_le_mul (hgradB x) (hgradB x)
        (norm_nonneg _) hB1
      _ = B1 ^ 2 := by ring
  let b : Euc p.d → ℝ := fun x =>
    inner ℝ
      ((HRS.MS.R26T3.r26t3_coeff R).drift t x -
        ((quadraticGradientDyn p.d p.s p.a p.β).coeff
          (fun _ => R.ρβ)).drift 0 x)
      (gradient f x)
  have hconvT : Measurable (convGradConvW (rieszKernelGrad p.d p.s) (R.ρ t)) :=
    HRS.MS.Wad.s8h2_conv_meas (HRS.MS.S111X1.kG_measurable p.s)
      (R.resulting.regular t ht).measurable
  have hconvStar : Measurable (convGradConvW (rieszKernelGrad p.d p.s) R.ρβ) :=
    HRS.MS.Wad.s8h2_conv_meas (HRS.MS.S111X1.kG_measurable p.s) hρstar.measurable
  have hmove : ∀ x,
      (HRS.MS.R26T3.r26t3_coeff R).drift t x =
        -convGradConvW (rieszKernelGrad p.d p.s) (R.ρ t) x -
          gradient (confinement p.a) x := by
    intro x
    simp [HRS.MS.R26T3.r26t3_coeff, WholeDyn.coeff, quadraticGradientDyn,
      meanFieldDriftW, Torus.matVec]
  have hstar : ∀ x,
      ((quadraticGradientDyn p.d p.s p.a p.β).coeff
        (fun _ => R.ρβ)).drift 0 x =
        -convGradConvW (rieszKernelGrad p.d p.s) R.ρβ x -
          gradient (confinement p.a) x := by
    intro x
    simp [WholeDyn.coeff, quadraticGradientDyn, meanFieldDriftW, Torus.matVec]
  have hdriftForm : b = fun x =>
      inner ℝ (-(convGradConvW (rieszKernelGrad p.d p.s) (R.ρ t) x -
        convGradConvW (rieszKernelGrad p.d p.s) R.ρβ x)) (gradient f x) := by
    funext x
    dsimp [b]
    rw [hmove x, hstar x]
    congr 2
    abel
  have hbMeas : Measurable b := by
    rw [hdriftForm]
    exact (hconvT.sub hconvStar).neg.inner hgradm
  have hK : 0 ≤ Cdrift * δ * Real.exp (-p.c₁ * t) :=
    mul_nonneg (mul_nonneg hCdrift hδ.le) (Real.exp_pos _).le
  have hbPoint : ∀ x, |b x| ≤
      (Cdrift * δ * Real.exp (-p.c₁ * t)) * ‖gradient f x‖ := by
    intro x
    simpa [b] using hdriftBound δ hδ hδh R t ht f x
  have hbSqI : Integrable (fun x => b x ^ 2) μstar := by
    have hmajor : Integrable
        (fun x => (Cdrift * δ * Real.exp (-p.c₁ * t)) ^ 2 *
          ‖gradient f x‖ ^ 2) μstar := hgradSqI.const_mul _
    refine hmajor.mono' (hbMeas.pow_const 2).aestronglyMeasurable ?_
    filter_upwards with x
    rw [Real.norm_of_nonneg (sq_nonneg (b x))]
    have hnonneg : 0 ≤ (Cdrift * δ * Real.exp (-p.c₁ * t)) * ‖gradient f x‖ :=
      mul_nonneg hK (norm_nonneg _)
    have hsquare := (sq_le_sq₀ (abs_nonneg (b x)) hnonneg).2 (hbPoint x)
    rw [sq_abs] at hsquare
    simpa [mul_pow] using hsquare
  have hbMem : MemLp b 2 μstar :=
    (memLp_two_iff_integrable_sq hbMeas.aestronglyMeasurable).2 hbSqI
  have hbIntegral : (∫ x, b x ^ 2 ∂μstar) ≤
      (Cdrift * δ * Real.exp (-p.c₁ * t)) ^ 2 *
        ∫ x, ‖gradient f x‖ ^ 2 ∂μstar := by
    calc
      (∫ x, b x ^ 2 ∂μstar) ≤
          ∫ x, (Cdrift * δ * Real.exp (-p.c₁ * t)) ^ 2 *
            ‖gradient f x‖ ^ 2 ∂μstar :=
        integral_mono hbSqI (hgradSqI.const_mul _) (fun x => by
          have hnonneg : 0 ≤ (Cdrift * δ * Real.exp (-p.c₁ * t)) * ‖gradient f x‖ :=
            mul_nonneg hK (norm_nonneg _)
          have hsquare := (sq_le_sq₀ (abs_nonneg (b x)) hnonneg).2 (hbPoint x)
          rw [sq_abs] at hsquare
          simpa [mul_pow] using hsquare)
      _ = (Cdrift * δ * Real.exp (-p.c₁ * t)) ^ 2 *
            ∫ x, ‖gradient f x‖ ^ 2 ∂μstar := by rw [integral_const_mul]
  have hbL2 : Real.sqrt (∫ x, b x ^ 2 ∂μstar) ≤
      (Cdrift * δ * Real.exp (-p.c₁ * t)) *
        Real.sqrt (∫ x, ‖gradient f x‖ ^ 2 ∂μstar) := by
    calc
      Real.sqrt (∫ x, b x ^ 2 ∂μstar) ≤
          Real.sqrt ((Cdrift * δ * Real.exp (-p.c₁ * t)) ^ 2 *
            ∫ x, ‖gradient f x‖ ^ 2 ∂μstar) := Real.sqrt_le_sqrt hbIntegral
      _ = (Cdrift * δ * Real.exp (-p.c₁ * t)) *
            Real.sqrt (∫ x, ‖gradient f x‖ ^ 2 ∂μstar) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs, abs_of_nonneg hK]
  let q : Fin p.d → Euc p.d → ℝ := fun j x =>
    (convGradConvW (rieszKernelGrad p.d p.s)
        (fun y => R.ρ t y *
          (Torus.matVec (-1 : Matrix (Fin p.d) (Fin p.d) ℝ).transpose
            (gradient f y)) j) x -
      convGradConvW (rieszKernelGrad p.d p.s)
        (fun y => R.ρβ y *
          (Torus.matVec (-1 : Matrix (Fin p.d) (Fin p.d) ℝ).transpose
            (gradient f y)) j) x) j
  have hqMem : ∀ j, MemLp (q j) 2 μstar := by
    intro j
    simpa [q, μstar] using (hnonlocal δ hδ hδh R t ht f hf j).1
  have hqBound : ∀ j, Real.sqrt (∫ x, (q j x) ^ 2 ∂μstar) ≤
      (CNL * δ * Real.exp (-p.c₁ * t)) *
        Real.sqrt (∫ x, ‖gradient f x‖ ^ 2 ∂μstar) := by
    intro j
    simpa [q, μstar] using (hnonlocal δ hδ hδh R t ht f hf j).2
  have hsum := fp81s21_finset_L2_bound_full2 (Finset.univ : Finset (Fin p.d)) q
    (fun j _ => hqMem j)
  let s : Euc p.d → ℝ := fun x => ∑ j : Fin p.d, q j x
  have hsMem : MemLp s 2 μstar := by
    simpa [s] using hsum.1
  have hgradNorm : 0 ≤ Real.sqrt (∫ x, ‖gradient f x‖ ^ 2 ∂μstar) :=
    Real.sqrt_nonneg _
  have hsL2 : Real.sqrt (∫ x, s x ^ 2 ∂μstar) ≤
      ((p.d : ℝ) * CNL * δ * Real.exp (-p.c₁ * t)) *
        Real.sqrt (∫ x, ‖gradient f x‖ ^ 2 ∂μstar) := by
    calc
      Real.sqrt (∫ x, s x ^ 2 ∂μstar) ≤
          ∑ j : Fin p.d, Real.sqrt (∫ x, (q j x) ^ 2 ∂μstar) := by
        simpa [s] using hsum.2
      _ ≤ ∑ _j : Fin p.d,
            (CNL * δ * Real.exp (-p.c₁ * t)) *
              Real.sqrt (∫ x, ‖gradient f x‖ ^ 2 ∂μstar) :=
        Finset.sum_le_sum fun j _ => hqBound j
      _ = ((p.d : ℝ) * CNL * δ * Real.exp (-p.c₁ * t)) *
            Real.sqrt (∫ x, ‖gradient f x‖ ^ 2 ∂μstar) := by
        simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        ring
  have hD : (fun x =>
      generatorW (HRS.MS.R26T3.r26t3_coeff R) t f x -
        generatorW ((quadraticGradientDyn p.d p.s p.a p.β).coeff
          (fun _ => R.ρβ)) 0 f x) = fun x => b x - s x := by
    funext x
    have hdecomp := sol13_generator_difference_decomposition (R := R) t f x
    simpa [b, s, q, HRS.MS.R26T3.r26t3_coeff, WholeDyn.coeff,
      quadraticGradientDyn] using hdecomp
  have hDmem : MemLp (fun x => b x - s x) 2 μstar := hbMem.sub hsMem
  have hDnorm : Real.sqrt (∫ x, (b x - s x) ^ 2 ∂μstar) ≤
      (C_D * δ * Real.exp (-p.c₁ * t)) *
        Real.sqrt (∫ x, ‖gradient f x‖ ^ 2 ∂μstar) := by
    have hnegSq : ∫ x, (-s x) ^ 2 ∂μstar = ∫ x, s x ^ 2 ∂μstar := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      ring
    have hL2 := fp81s21_L2_add_full2 hbMem hsMem.neg
    calc
      Real.sqrt (∫ x, (b x - s x) ^ 2 ∂μstar) =
          Real.sqrt (∫ x, (b x + -s x) ^ 2 ∂μstar) := by congr 2 <;> ring
      _ ≤ Real.sqrt (∫ x, b x ^ 2 ∂μstar) +
            Real.sqrt (∫ x, (-s x) ^ 2 ∂μstar) := hL2.2
      _ = Real.sqrt (∫ x, b x ^ 2 ∂μstar) +
            Real.sqrt (∫ x, s x ^ 2 ∂μstar) := by rw [hnegSq]
      _ ≤ (Cdrift * δ * Real.exp (-p.c₁ * t)) *
            Real.sqrt (∫ x, ‖gradient f x‖ ^ 2 ∂μstar) +
          ((p.d : ℝ) * CNL * δ * Real.exp (-p.c₁ * t)) *
            Real.sqrt (∫ x, ‖gradient f x‖ ^ 2 ∂μstar) :=
        add_le_add hbL2 hsL2
      _ = (C_D * δ * Real.exp (-p.c₁ * t)) *
            Real.sqrt (∫ x, ‖gradient f x‖ ^ 2 ∂μstar) := by
        dsimp [C_D]
        ring
  have hDIntegral : (∫ x, (b x - s x) ^ 2 ∂μstar) ≤
      (C_D * δ * Real.exp (-p.c₁ * t)) ^ 2 *
        ∫ x, ‖gradient f x‖ ^ 2 ∂μstar := by
    have hgradI : 0 ≤ ∫ x, ‖gradient f x‖ ^ 2 ∂μstar :=
      integral_nonneg fun x => sq_nonneg _
    have hDint : 0 ≤ ∫ x, (b x - s x) ^ 2 ∂μstar :=
      integral_nonneg fun x => sq_nonneg _
    have hcoef : 0 ≤ C_D * δ * Real.exp (-p.c₁ * t) :=
      mul_nonneg (mul_nonneg hCD hδ.le) (Real.exp_pos _).le
    have hsqr := (sq_le_sq₀ (Real.sqrt_nonneg _) (mul_nonneg hcoef hgradNorm)).2 hDnorm
    calc
      (∫ x, (b x - s x) ^ 2 ∂μstar) =
          (Real.sqrt (∫ x, (b x - s x) ^ 2 ∂μstar)) ^ 2 :=
        (Real.sq_sqrt hDint).symm
      _ ≤ ((C_D * δ * Real.exp (-p.c₁ * t)) *
            Real.sqrt (∫ x, ‖gradient f x‖ ^ 2 ∂μstar)) ^ 2 := hsqr
      _ = (C_D * δ * Real.exp (-p.c₁ * t)) ^ 2 *
            ∫ x, ‖gradient f x‖ ^ 2 ∂μstar := by
        rw [mul_pow, Real.sq_sqrt hgradI]
  refine ⟨?_, ?_⟩
  · rw [hD]
    exact hDmem
  · calc
      (∫ x,
          (generatorW (HRS.MS.R26T3.r26t3_coeff R) t f x -
            generatorW ((quadraticGradientDyn p.d p.s p.a p.β).coeff
              (fun _ => R.ρβ)) 0 f x) ^ 2
          ∂(HRS.Whole.withDensityReal R.ρβ)) =
          ∫ x, (b x - s x) ^ 2 ∂μstar := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        change (generatorW (HRS.MS.R26T3.r26t3_coeff R) t f x -
          generatorW ((quadraticGradientDyn p.d p.s p.a p.β).coeff
            (fun _ => R.ρβ)) 0 f x) ^ 2 = (b x - s x) ^ 2
        rw [congrFun hD x]
      _ ≤ (C_D * δ * Real.exp (-p.c₁ * t)) ^ 2 *
            ∫ x, ‖gradient f x‖ ^ 2 ∂(HRS.Whole.withDensityReal R.ρβ) := by
        simpa [μstar] using hDIntegral

end HRS.Fp81.S21

#print axioms HRS.Fp81.S21.sol13_small_form
