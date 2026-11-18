import HRS.MS.QsfOsc2

/-!
# S4.5 oscillator clause, part 3: derivative bounds `‖D^j h_α‖_∞ ≤ C0 (2d)^j (|α|+j+1)^{j/2}`
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal RealInnerProductSpace ContDiff

noncomputable section

namespace S45

open HRS.Whole
open HRS (Euc cbNorm MemCb)

variable {d : ℕ}

theorem s45_le_infty (j : ℕ) : ((j : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
  exact_mod_cast le_top

theorem s45_norm_proj_le (i : Fin d) : ‖(EuclideanSpace.proj i : Euc d →L[ℝ] ℝ)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
    simpa using PiLp.norm_apply_le x i

theorem s45_iter_bound {C0 : ℝ} (hC0 : ∀ (α : MultiIndex d) (x : Euc d), |hermiteFunD α x| ≤ C0)
    (j : ℕ) : ∀ (α : MultiIndex d) (D : ℕ), α.degree ≤ D → ∀ x : Euc d,
      ‖iteratedFDeriv ℝ j (hermiteFunD α) x‖ ≤
        C0 * (2 * (d : ℝ)) ^ j * Real.sqrt ((D : ℝ) + j + 1) ^ j := by
  induction j with
  | zero =>
    intro α D hD x
    rw [norm_iteratedFDeriv_zero]
    simpa using hC0 α x
  | succ j ih =>
    intro α D hD x
    have hC00 : 0 ≤ C0 := (abs_nonneg _).trans (hC0 0 0)
    have hsm : ∀ β : MultiIndex d, ContDiff ℝ ∞ (hermiteFunD β) := contDiff_hermiteFunD
    rw [← norm_iteratedFDeriv_fderiv, s45_fderiv_hermiteFunD α]
    set g : Fin d → Euc d → ℝ := fun i y =>
      Real.sqrt ((α i : ℝ) / 2) * hermiteFunD (s45_dec α i) y -
        Real.sqrt (((α i : ℝ) + 1) / 2) * hermiteFunD (s45_inc α i) y with hg
    have hgs : ∀ i, ContDiff ℝ ∞ (g i) := fun i => by
      simp only [hg]
      exact (contDiff_const.mul (hsm _)).sub (contDiff_const.mul (hsm _))
    have hfun : (fun y => ∑ i : Fin d, g i y • (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ)) =
        fun y => ∑ i : Fin d, ((ContinuousLinearMap.id ℝ ℝ).smulRight
          (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ)) (g i y) := by
      funext y; simp
    rw [show (fun y => ∑ i : Fin d, (Real.sqrt ((α i : ℝ) / 2) * hermiteFunD (s45_dec α i) y -
        Real.sqrt (((α i : ℝ) + 1) / 2) * hermiteFunD (s45_inc α i) y) •
          (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ)) = fun y => ∑ i : Fin d, ((ContinuousLinearMap.id ℝ ℝ).smulRight
          (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ)) (g i y) from by
      funext y; simp [hg]]
    have hcd : ∀ i : Fin d, ContDiffAt ℝ j (fun y => ((ContinuousLinearMap.id ℝ ℝ).smulRight
        (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ)) (g i y)) x := fun i =>
      (((ContinuousLinearMap.id ℝ ℝ).smulRight
        (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ)).contDiff.comp (hgs i)).contDiffAt.of_le
        (s45_le_infty _)
    rw [iteratedFDeriv_fun_sum_apply (fun i _ => hcd i)]
    set B : ℝ := C0 * (2 * (d : ℝ)) ^ j * Real.sqrt (((D + 1 : ℕ) : ℝ) + j + 1) ^ j with hB
    have hB0 : 0 ≤ B := by positivity
    have hterm : ∀ i : Fin d, ‖iteratedFDeriv ℝ j (fun y => ((ContinuousLinearMap.id ℝ ℝ).smulRight
        (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ)) (g i y)) x‖ ≤ 2 * Real.sqrt ((D : ℝ) + 1) * B := by
      intro i
      set L : ℝ →L[ℝ] (Euc d →L[ℝ] ℝ) := (ContinuousLinearMap.id ℝ ℝ).smulRight
        (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ) with hL
      have hLn : ‖L‖ ≤ 1 := by
        rw [hL, ContinuousLinearMap.norm_smulRight_apply]
        calc ‖(ContinuousLinearMap.id ℝ ℝ)‖ * ‖(EuclideanSpace.proj i : Euc d →L[ℝ] ℝ)‖ ≤ 1 * 1 :=
              mul_le_mul ContinuousLinearMap.norm_id_le (s45_norm_proj_le i) (norm_nonneg _) zero_le_one
          _ = 1 := one_mul 1
      have h1 := ContinuousLinearMap.norm_iteratedFDeriv_comp_left L (f := g i) (x := x)
        ((hgs i).contDiffAt.of_le (s45_le_infty j)) le_rfl
      have h2 : ‖iteratedFDeriv ℝ j (g i) x‖ ≤ 2 * Real.sqrt ((D : ℝ) + 1) * B := by
        have e : g i = (Real.sqrt ((α i : ℝ) / 2)) • hermiteFunD (s45_dec α i) -
            (Real.sqrt (((α i : ℝ) + 1) / 2)) • hermiteFunD (s45_inc α i) := by
          funext y; simp [hg]
        have hca : ContDiffAt ℝ j ((Real.sqrt ((α i : ℝ) / 2)) • hermiteFunD (s45_dec α i)) x :=
          ((hsm (s45_dec α i)).const_smul (Real.sqrt ((α i : ℝ) / 2))).contDiffAt.of_le (s45_le_infty j)
        have hcb : ContDiffAt ℝ j ((Real.sqrt (((α i : ℝ) + 1) / 2)) • hermiteFunD (s45_inc α i)) x :=
          ((hsm (s45_inc α i)).const_smul (Real.sqrt (((α i : ℝ) + 1) / 2))).contDiffAt.of_le (s45_le_infty j)
        rw [e, iteratedFDeriv_sub_apply hca hcb,
          iteratedFDeriv_const_smul_apply (((hsm (s45_dec α i)).contDiffAt).of_le (s45_le_infty j)),
          iteratedFDeriv_const_smul_apply (((hsm (s45_inc α i)).contDiffAt).of_le (s45_le_infty j))]
        have hαi : (α i : ℝ) ≤ D := by exact_mod_cast (s45_le_degree α i).trans hD
        have hdec := ih (s45_dec α i) (D + 1) ((s45_degree_dec_le α i).trans (hD.trans (Nat.le_succ D))) x
        have hinc := ih (s45_inc α i) (D + 1) (by rw [s45_degree_inc]; exact Nat.succ_le_succ hD) x
        have ca : Real.sqrt ((α i : ℝ) / 2) ≤ Real.sqrt ((D : ℝ) + 1) :=
          Real.sqrt_le_sqrt (by have : (0 : ℝ) ≤ α i := Nat.cast_nonneg _; linarith)
        have cb : Real.sqrt (((α i : ℝ) + 1) / 2) ≤ Real.sqrt ((D : ℝ) + 1) :=
          Real.sqrt_le_sqrt (by have : (0 : ℝ) ≤ α i := Nat.cast_nonneg _; linarith)
        calc ‖Real.sqrt ((α i : ℝ) / 2) • iteratedFDeriv ℝ j (hermiteFunD (s45_dec α i)) x -
              Real.sqrt (((α i : ℝ) + 1) / 2) • iteratedFDeriv ℝ j (hermiteFunD (s45_inc α i)) x‖
            ≤ ‖Real.sqrt ((α i : ℝ) / 2) • iteratedFDeriv ℝ j (hermiteFunD (s45_dec α i)) x‖ +
              ‖Real.sqrt (((α i : ℝ) + 1) / 2) • iteratedFDeriv ℝ j (hermiteFunD (s45_inc α i)) x‖ :=
              norm_sub_le _ _
          _ ≤ Real.sqrt ((D : ℝ) + 1) * B + Real.sqrt ((D : ℝ) + 1) * B := by
              rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
                abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg (Real.sqrt_nonneg _)]
              exact add_le_add (mul_le_mul ca hdec (norm_nonneg _) (Real.sqrt_nonneg _))
                (mul_le_mul cb hinc (norm_nonneg _) (Real.sqrt_nonneg _))
          _ = _ := by ring
      exact h1.trans (by simpa using mul_le_mul hLn h2 (norm_nonneg _) zero_le_one)
    refine (norm_sum_le _ _).trans ?_
    calc ∑ i : Fin d, ‖iteratedFDeriv ℝ j (fun y => ((ContinuousLinearMap.id ℝ ℝ).smulRight
          (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ)) (g i y)) x‖
        ≤ ∑ _i : Fin d, 2 * Real.sqrt ((D : ℝ) + 1) * B := Finset.sum_le_sum fun i _ => hterm i
      _ = (d : ℝ) * (2 * Real.sqrt ((D : ℝ) + 1) * B) := by simp
      _ ≤ _ := by
        have hr : Real.sqrt ((D : ℝ) + 1) ≤ Real.sqrt ((D : ℝ) + (j + 1 : ℕ) + 1) :=
          Real.sqrt_le_sqrt (by push_cast; have : (0 : ℝ) ≤ j := Nat.cast_nonneg _; linarith)
        have hr2 : Real.sqrt (((D + 1 : ℕ) : ℝ) + j + 1) = Real.sqrt ((D : ℝ) + (j + 1 : ℕ) + 1) := by
          congr 1; push_cast; ring
        rw [hB, hr2]
        have hrn : 0 ≤ Real.sqrt ((D : ℝ) + 1) := Real.sqrt_nonneg _
        have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
        calc (d : ℝ) * (2 * Real.sqrt ((D : ℝ) + 1) *
              (C0 * (2 * (d : ℝ)) ^ j * Real.sqrt ((D : ℝ) + (j + 1 : ℕ) + 1) ^ j))
            = C0 * (2 * (d : ℝ)) ^ (j + 1) * (Real.sqrt ((D : ℝ) + 1) *
                Real.sqrt ((D : ℝ) + (j + 1 : ℕ) + 1) ^ j) := by ring
          _ ≤ C0 * (2 * (d : ℝ)) ^ (j + 1) * (Real.sqrt ((D : ℝ) + (j + 1 : ℕ) + 1) *
                Real.sqrt ((D : ℝ) + (j + 1 : ℕ) + 1) ^ j) := by gcongr
          _ = _ := by push_cast; ring

end S45

end
