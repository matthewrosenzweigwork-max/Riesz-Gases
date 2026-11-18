import HRS.MS.WadAux61

/-!
# S8.3, packet S8D-2, part 8: constants and mean preservation

`s8d_gen_const`: `generatorW` of a constant is `0`.  `s8d_const_classical`: the constant function is a classical
adjoint solution (datum `c`).  `s8d_U_one`: `U_t 1 = 1`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Metric
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.Wad

open HRS HRS.Whole

variable {d : ℕ}

theorem s8d_gen_const (C : WholeCoeff d) (r c : ℝ) (x : Euc d) :
    generatorW C r (fun _ => c) x = 0 := by
  have hg : gradient (fun _ : Euc d => c) = fun _ => 0 := by
    funext y; unfold gradient; simp
  have hl : Laplacian.laplacian (fun _ : Euc d => c) x = 0 := by
    simp [InnerProductSpace.laplacian_const]
  have hm : ∀ A : Matrix (Fin d) (Fin d) ℝ, Torus.matVec A (0 : Euc d) = 0 := fun A => by
    unfold Torus.matVec; simp
  unfold generatorW
  simp only [hg, hl, mul_zero, inner_zero_right, hm, zero_sub, PiLp.zero_apply]
  simp [convGradConvW]

theorem s8d_int_wdr (ρ : Euc d → ℝ) (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (f : Euc d → ℝ) :
    ∫ y, f y ∂(HRS.Whole.withDensityReal ρ) = ∫ y, ρ y * f y := by
  unfold HRS.Whole.withDensityReal
  rw [integral_withDensity_eq_integral_toReal_smul₀ (f := fun x => ENNReal.ofReal (ρ x))
    (ENNReal.measurable_ofReal.comp hρ).aemeasurable
    (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp [ENNReal.toReal_ofReal (hρ0 y)]

theorem s8d_const_classical (C : WholeCoeff d) (t c : ℝ) :
    IsClassicalAdjointW C t (fun _ => c) (fun _ _ => c) where
  c2 := fun r _ => contDiff_const
  bdd := fun j _ => ⟨|c|, fun r _ x => by
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp [norm_iteratedFDeriv_zero]
    · rw [iteratedFDeriv_const_of_ne hj.ne']; simp⟩
  cont_c2 := fun j _ => by
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp only [iteratedFDeriv_zero_eq_comp]
      exact continuous_const
    · simp only [iteratedFDeriv_const_of_ne hj.ne']
      exact continuous_const
  terminal := rfl
  time_deriv := fun x r _ => by
    rw [s8d_gen_const]
    simpa using hasDerivAt_const r c
  cont_time_deriv := by
    simp only [s8d_gen_const]
    exact continuous_const
  bdd_time_deriv := ⟨0, fun r _ x => by simp [s8d_gen_const]⟩

theorem s8d_memCM_const {M : ℝ} (hM : 0 < M) (c : ℝ) : MemCM M (fun _ : Euc d => c) :=
  s85_cm_of_wt (M' := 0) (Φ := |c|) hM continuous_const (fun x => by
    simp [Real.rpow_zero])

/-- `U_t 1 = 1`. -/
theorem s8d_Ulim_one {a β T M : ℝ} {ρβ : Euc d → ℝ} (H : S85Hyp d a β T M ρβ) (hMpos : 0 < M) {t : ℝ}
    (ht0 : 0 ≤ t) (htT : t ≤ T) (x : Euc d) :
    s85_Ulim a β ρβ M t (fun _ => (1 : ℝ)) x = 1 := by
  obtain ⟨hd, ha, hβ, hT, hM, hρ⟩ := id H
  haveI : IsProbabilityMeasure (HRS.Whole.withDensityReal ρβ) := s85_isProb hρ.1.1
  rw [s85_Ulim_ext H ht0 htT (s8d_const_classical (critCoeff d a β ρβ) t 1) (s8d_memCM_const hMpos 1) x]
  unfold s85_V
  simp [HRS.Whole.pair]

end HRS.MS.Wad
