import HRS.MS.QsfOsc3
import HRS.Whole.Oscillator

/-!
# S4.5 oscillator clause, part 4: `C_b^J` norms of the Hermite test functions and their summability

`cbNorm J (φ_α) ≤ K λ_α^{-(m-J)/2}` for `φ_α = λ_α^{-m/2} h_α` (`oscTestFun m α`); the family is
`ℓ¹` in `C_b^J` exactly when `m > J + 2d`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal RealInnerProductSpace ContDiff

noncomputable section

namespace S45

open HRS.Whole
open HRS (Euc cbNorm MemCb)

variable {d : ℕ}

theorem s45_cb_oscTest (hd : 1 ≤ d) (J : ℕ) (m : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ α : MultiIndex d, MemCb J (oscTestFun m α) ∧
      cbNorm J (oscTestFun m α) ≤ K * oscEigenvalue d α ^ (-((m - J) / 2)) := by
  obtain ⟨C0, hC0⟩ := hermiteFunD_uniform_bound (d := d)
  have hC00 : 0 ≤ C0 := (abs_nonneg _).trans (hC0 0 0)
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  set K0 : ℝ := C0 * (2 * (d : ℝ)) ^ J * Real.sqrt ((J : ℝ) + 1) ^ J with hK0
  have hK00 : 0 ≤ K0 := by positivity
  refine ⟨((J : ℝ) + 1) * K0, by positivity, fun α => ?_⟩
  set lam := oscEigenvalue d α with hlam
  have hlam1 : 1 ≤ lam := one_le_oscEigenvalue α
  have hlam0 : 0 < lam := by linarith
  set c : ℝ := lam ^ (-(m / 2)) with hc
  have hc0 : 0 < c := Real.rpow_pos_of_pos hlam0 _
  have hfun : oscTestFun m α = c • hermiteFunD α := by
    funext x; simp [oscTestFun, hc, hlam]
  have hsm : ContDiff ℝ ∞ (hermiteFunD α) := contDiff_hermiteFunD α
  -- per-derivative bound
  have hbd : ∀ j ≤ J, ∀ x : Euc d, ‖iteratedFDeriv ℝ j (oscTestFun m α) x‖ ≤
      c * (K0 * Real.sqrt lam ^ J) := by
    intro j hj x
    rw [hfun, iteratedFDeriv_const_smul_apply (hsm.contDiffAt.of_le (s45_le_infty j)), norm_smul,
      Real.norm_eq_abs, abs_of_pos hc0]
    refine mul_le_mul_of_nonneg_left ?_ hc0.le
    refine (s45_iter_bound hC0 j α α.degree le_rfl x).trans ?_
    have hdeg : (α.degree : ℝ) + j + 1 ≤ ((J : ℝ) + 1) * lam := by
      have h1 : (j : ℝ) ≤ J := by exact_mod_cast hj
      have h2 : (0 : ℝ) ≤ α.degree := Nat.cast_nonneg _
      have h3 : (0 : ℝ) ≤ J := Nat.cast_nonneg _
      simp only [hlam, oscEigenvalue]
      nlinarith
    have hb1 : 1 ≤ Real.sqrt ((α.degree : ℝ) + j + 1) :=
      Real.one_le_sqrt.2 (by have : (0 : ℝ) ≤ α.degree := Nat.cast_nonneg _
                             have : (0 : ℝ) ≤ j := Nat.cast_nonneg _
                             linarith)
    have hsq : Real.sqrt ((α.degree : ℝ) + j + 1) ≤ Real.sqrt ((J : ℝ) + 1) * Real.sqrt lam := by
      rw [← Real.sqrt_mul (by positivity)]
      exact Real.sqrt_le_sqrt hdeg
    calc C0 * (2 * (d : ℝ)) ^ j * Real.sqrt ((α.degree : ℝ) + j + 1) ^ j
        ≤ C0 * (2 * (d : ℝ)) ^ J * (Real.sqrt ((J : ℝ) + 1) * Real.sqrt lam) ^ J := by
          have e1 : (2 * (d : ℝ)) ^ j ≤ (2 * (d : ℝ)) ^ J :=
            pow_le_pow_right₀ (by linarith) hj
          have e2 : Real.sqrt ((α.degree : ℝ) + j + 1) ^ j ≤
              (Real.sqrt ((J : ℝ) + 1) * Real.sqrt lam) ^ J :=
            (pow_le_pow_right₀ hb1 hj).trans (pow_le_pow_left₀ (by positivity) hsq J)
          calc C0 * (2 * (d : ℝ)) ^ j * Real.sqrt ((α.degree : ℝ) + j + 1) ^ j
              ≤ C0 * (2 * (d : ℝ)) ^ J * Real.sqrt ((α.degree : ℝ) + j + 1) ^ j :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left e1 hC00) (by positivity)
            _ ≤ _ := mul_le_mul_of_nonneg_left e2 (by positivity)
      _ = K0 * Real.sqrt lam ^ J := by rw [mul_pow, hK0]; ring
  refine ⟨⟨?_, fun j hj => ⟨c * (K0 * Real.sqrt lam ^ J), by
      rintro _ ⟨x, rfl⟩; exact hbd j hj x⟩⟩, ?_⟩
  · rw [hfun]; exact (hsm.of_le (s45_le_infty J)).const_smul c
  · unfold cbNorm
    have hle : ∀ j ∈ Finset.range (J + 1), (⨆ z : Euc d, ‖iteratedFDeriv ℝ j (oscTestFun m α) z‖) ≤
        c * (K0 * Real.sqrt lam ^ J) := fun j hj =>
      ciSup_le fun x => hbd j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)) x
    refine (Finset.sum_le_sum hle).trans ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast
    have e : c * Real.sqrt lam ^ J = lam ^ (-((m - J) / 2)) := by
      rw [hc, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hlam0.le,
        ← Real.rpow_add hlam0]
      congr 1; ring
    refine le_of_eq ?_
    calc ((J : ℝ) + 1) * (c * (K0 * Real.sqrt lam ^ J)) =
        ((J : ℝ) + 1) * K0 * (c * Real.sqrt lam ^ J) := by ring
      _ = _ := by rw [e]

theorem s45_summable_oscTest (hd : 1 ≤ d) (J : ℕ) {m : ℝ} (hm : (J : ℝ) + 2 * d < m)
    (e : ℕ ≃ MultiIndex d) :
    HRS.Whole.IsSummableFeatureFamily J (fun j : ℕ => oscTestFun m (e j)) := by
  obtain ⟨K, hK0, hK⟩ := s45_cb_oscTest hd J m
  have hlt : (d : ℝ) < (m - J) / 2 := by linarith
  have hsum : Summable fun α : MultiIndex d => oscEigenvalue d α ^ (-((m - J) / 2)) :=
    (summable_oscEigenvalue_rpow_iff hd ((m - J) / 2)).2 hlt
  have h2 : Summable fun α : MultiIndex d => K * oscEigenvalue d α ^ (-((m - J) / 2)) :=
    hsum.mul_left K
  have h1 : Summable fun α : MultiIndex d => cbNorm J (oscTestFun m α) := by
    refine Summable.of_nonneg_of_le (fun α => HRS.MS.Tc5.tc5_cb_nonneg J _) (fun α => ?_) h2
    exact (hK α).2
  refine ⟨fun j => (hK (e j)).1, ?_⟩
  exact (Equiv.summable_iff e (f := fun α : MultiIndex d => cbNorm J (oscTestFun m α))).2 h1

theorem s45_exists_enum (hd : 1 ≤ d) : Nonempty (ℕ ≃ MultiIndex d) := by
  haveI : Infinite (MultiIndex d) := by
    haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
    infer_instance
  exact nonempty_equiv_of_countable

end S45

end
