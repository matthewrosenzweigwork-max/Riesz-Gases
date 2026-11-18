import HRS.MS.FixEqP3Aux22

/-!
# S5.7 `fixed_equation` (worker S57P), part 35: difference of the initial parts of two families
-/

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.FixEq

open HRS HRS.Whole HRS.MP.RdGen HRS.MS.Go HRS.MS.Fcau

variable {d : ℕ} {T : ℝ} {n : ℕ} {s : ℝ} {M Q : Matrix (Fin d) (Fin d) ℝ} {ν νN : ℝ}
  {c cN : ℝ → Euc d → Euc d} {ρ ρN : ℝ → Euc d → ℝ} {m : ℝ} {J : ℕ} {Ca CaN Cd CdN : ℝ}
  {P : ℝ} {η : (Euc d → ℝ) → ℝ}

theorem s57p_init_diff (hP : (d : ℝ) < 2 * P) (hη : IsBoundedLinearOnE n P η) (hdual : dualNormE n P η < ⊤)
    (hbdC : S57pOrbBd (fixedEqCoeff s M Q ν c ρ) T n m J Ca Cd)
    (hbdN : S57pOrbBd (fixedEqCoeff s M Q νN cN ρN) T n m J CaN CdN) (hCa : 0 ≤ Ca) (hCaN : 0 ≤ CaN)
    {Cp1 Dt : ℝ} (hCp1n : 0 ≤ Cp1) (hDt0 : 0 ≤ Dt) (hCp1 : ∀ α : MultiIndex d, ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ r ∈ Set.Icc (0 : ℝ) t, ∀ i ≤ n, ∀ x,
      ‖iteratedFDeriv ℝ i (fun y => propagatorW (fixedEqCoeff s M Q ν c ρ) r t (oscTestFun m α) y -
        propagatorW (fixedEqCoeff s M Q νN cN ρN) r t (oscTestFun m α) y) x‖ ≤
        Cp1 * oscEigenvalue d α ^ (((J : ℝ) - m) / 2) * Dt)
    (hsum : Summable fun α : MultiIndex d => oscEigenvalue d α ^ ((J : ℝ) - m)) (aN a : ℝ) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) T) (hCd0 : 0 ≤ Cd) (hCdN0 : 0 ≤ CdN) :
    ‖s57pI (fixedEqCoeff s M Q νN cN ρN) m aN η t - s57pI (fixedEqCoeff s M Q ν c ρ) m a η t‖ ≤
      (|aN - a| * s57pD d n P η * CaN + |a| * s57pD d n P η * (Cp1 * Dt)) *
        Real.sqrt (∑' α : MultiIndex d, oscEigenvalue d α ^ ((J : ℝ) - m)) := by
  set CC := fixedEqCoeff s M Q ν c ρ with hCC
  set CN := fixedEqCoeff s M Q νN cN ρN with hCN
  have hD := s57pD_nonneg d n P η
  have hmemC := ((s57p_init_lip hP hη hdual hbdC hCa hCd0 a hsum).1 t ht).1
  have hmemN := ((s57p_init_lip hP hη hdual hbdN hCaN hCdN0 aN hsum).1 t ht).1
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) t := ⟨le_rfl, ht.1⟩
  have hsq : ∀ (C0 : ℝ) (α : MultiIndex d), (C0 * oscEigenvalue d α ^ (((J : ℝ) - m) / 2)) ^ 2 =
      C0 ^ 2 * oscEigenvalue d α ^ ((J : ℝ) - m) := by
    intro C0 α; rw [mul_pow, rpow_half_sq _ _ (oscEv_pos α)]
  have hS0 : 0 ≤ ∑' α : MultiIndex d, oscEigenvalue d α ^ ((J : ℝ) - m) :=
    tsum_nonneg fun α => (Real.rpow_pos_of_pos (oscEv_pos α) _).le
  set E1 : ℝ := |aN - a| * s57pD d n P η * CaN + |a| * s57pD d n P η * (Cp1 * Dt) with hE1
  have hcoord : ∀ α : MultiIndex d, |aN * η (propagatorW CN 0 t (oscTestFun m α)) - a * η (propagatorW CC 0 t (oscTestFun m α))| ≤
      E1 * oscEigenvalue d α ^ (((J : ℝ) - m) / 2) := by
    intro α
    obtain ⟨-, hbC⟩ := (hbdC α).1 t ht
    obtain ⟨-, hbN⟩ := (hbdN α).1 t ht
    have hcC : ContDiff ℝ (n : WithTop ℕ∞) (propagatorW CC 0 t (oscTestFun m α)) :=
      (hbC 0 h0).1.of_le (by exact_mod_cast Nat.le_succ n)
    have hcN : ContDiff ℝ (n : WithTop ℕ∞) (propagatorW CN 0 t (oscTestFun m α)) :=
      (hbN 0 h0).1.of_le (by exact_mod_cast Nat.le_succ n)
    have hsub := s57p_eta_sub hP hη hcN hcC (B := (CaN + Ca) * oscEigenvalue d α ^ (((J : ℝ) - m) / 2))
      (fun j hj x => ((hbN 0 h0).2 j (by omega) x).trans (mul_le_mul_of_nonneg_right (by linarith)
        (Real.rpow_nonneg (oscEigenvalue_pos α).le _)))
      (fun j hj x => ((hbC 0 h0).2 j (by omega) x).trans (mul_le_mul_of_nonneg_right (by linarith)
        (Real.rpow_nonneg (oscEigenvalue_pos α).le _)))
    have hdiffb : ∀ j ≤ n, ∀ x, ‖iteratedFDeriv ℝ j (fun y => propagatorW CN 0 t (oscTestFun m α) y -
        propagatorW CC 0 t (oscTestFun m α) y) x‖ ≤ Cp1 * oscEigenvalue d α ^ (((J : ℝ) - m) / 2) * Dt := by
      intro j hj x
      have e : (fun y => propagatorW CN 0 t (oscTestFun m α) y - propagatorW CC 0 t (oscTestFun m α) y) =
          fun y => (-1 : ℝ) * (propagatorW CC 0 t (oscTestFun m α) y - propagatorW CN 0 t (oscTestFun m α) y) := by
        funext y; ring
      rw [e]
      refine (s57p_norm_const_mul ((hcC.sub hcN).of_le (by exact_mod_cast hj)) (-1) x).trans ?_
      simpa using hCp1 α t ht 0 h0 j hj x
    have hb := s57p_eta_bound hP hη hdual (hcN.sub hcC) hdiffb
    rw [hsub] at hb
    have h1 := s57p_init_coord hP hη hdual hbdN ht α
    calc |aN * η (propagatorW CN 0 t (oscTestFun m α)) - a * η (propagatorW CC 0 t (oscTestFun m α))|
        = |(aN - a) * η (propagatorW CN 0 t (oscTestFun m α)) +
          a * (η (propagatorW CN 0 t (oscTestFun m α)) - η (propagatorW CC 0 t (oscTestFun m α)))| := by ring_nf
      _ ≤ |aN - a| * |η (propagatorW CN 0 t (oscTestFun m α))| +
          |a| * |η (propagatorW CN 0 t (oscTestFun m α)) - η (propagatorW CC 0 t (oscTestFun m α))| := by
          refine (abs_add_le _ _).trans (le_of_eq ?_); rw [abs_mul, abs_mul]
      _ ≤ |aN - a| * (s57pD d n P η * (CaN * oscEigenvalue d α ^ (((J : ℝ) - m) / 2))) +
          |a| * ((dualNormE n P η).toReal * (s57pC d n P * (Cp1 * oscEigenvalue d α ^ (((J : ℝ) - m) / 2) * Dt))) := by
          gcongr
      _ = E1 * oscEigenvalue d α ^ (((J : ℝ) - m) / 2) := by
          rw [hE1]; simp only [s57pD]; ring
  have key := s57p_ellVec_norm_sq (m := m)
    (v := fun α => aN * η (propagatorW CN 0 t (oscTestFun m α)) - a * η (propagatorW CC 0 t (oscTestFun m α)))
    (g := fun α => E1 ^ 2 * oscEigenvalue d α ^ ((J : ℝ) - m)) (hsum.mul_left _) (fun α => by
      have h3 := pow_le_pow_left₀ (abs_nonneg _) (hcoord α) 2
      rw [sq_abs, hsq] at h3
      exact h3)
  unfold s57pI
  rw [s57p_ellVec_sub hmemN hmemC]
  rw [tsum_mul_left] at key
  have hE10 : 0 ≤ E1 := by
    rw [hE1]; positivity
  refine le_of_sq_le_sq ?_ (mul_nonneg hE10 (Real.sqrt_nonneg _))
  refine key.2.trans (le_of_eq ?_)
  rw [mul_pow, Real.sq_sqrt hS0]

end HRS.MS.FixEq
