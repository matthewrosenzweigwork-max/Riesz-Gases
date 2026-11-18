import HRS.Whole.Adjoint

/-!
# LC-F, part 1: bounds on all derivatives from a finite decay norm; congruence of solutions

Helper lemmas (prefix `lcf_`) for the assembly `local_decay_proof` (`HRS/MS/LcFinal.lean`):
* `lcf_norm_le_sum`: the operator norm of a multilinear form on `Euc d` is at most the sum of its
  absolute values on basis tuples;
* `lcf_bdd_iteratedFDeriv`: `decayNormE k b f < ⊤`, `0 ≤ b`, `j ≤ k` bounds `‖D^j f‖` uniformly;
* `lcf_solution_congr`: `IsLocalBackwardSolution` only sees the drift on `[0,t]`.
-/

open MeasureTheory Set Filter Topology
open HRS HRS.Whole

noncomputable section

namespace HRS.MS.Lc

variable {d : ℕ}

theorem lcf_norm_le_sum {j : ℕ} (A : ContinuousMultilinearMap ℝ (fun _ : Fin j => Euc d) ℝ) :
    ‖A‖ ≤ ∑ I : Fin j → Fin d, |A (fun l => EuclideanSpace.single (I l) (1 : ℝ))| := by
  refine A.opNorm_le_bound (Finset.sum_nonneg fun _ _ => abs_nonneg _) fun m => ?_
  have hm : m = fun l => ∑ i : Fin d, m l i • (EuclideanSpace.single i (1 : ℝ) : Euc d) := by
    funext l
    have := (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr (m l)
    simpa [EuclideanSpace.basisFun_apply] using this.symm
  have hsum : A m = ∑ r : Fin j → Fin d, (∏ l, m l (r l)) *
      A (fun l => EuclideanSpace.single (r l) (1 : ℝ)) := by
    conv_lhs => rw [hm]
    rw [A.map_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [A.map_smul_univ]
    simp
  rw [hsum, Finset.sum_mul]
  refine (Real.norm_eq_abs _ ▸ norm_sum_le _ _).trans (Finset.sum_le_sum fun r _ => ?_)
  rw [norm_mul, mul_comm]
  have hpr : ‖∏ l, m l (r l)‖ ≤ ∏ l, ‖m l‖ := by
    rw [norm_prod]
    gcongr with l _
    exact PiLp.norm_apply_le (m l) (r l)
  have h0 : 0 ≤ ‖A (fun l => EuclideanSpace.single (r l) (1 : ℝ))‖ := norm_nonneg _
  calc ‖A (fun l => EuclideanSpace.single (r l) (1 : ℝ))‖ * ‖∏ l, m l (r l)‖
      ≤ ‖A (fun l => EuclideanSpace.single (r l) (1 : ℝ))‖ * ∏ l, ‖m l‖ :=
        mul_le_mul_of_nonneg_left hpr h0
    _ = _ := by rw [Real.norm_eq_abs]

/-- A finite decay norm (`0 ≤ b`) bounds every derivative of order `j ≤ k` uniformly. -/
theorem lcf_bdd_iteratedFDeriv {k : ℕ} {b : ℝ} (hb : 0 ≤ b) {f : Euc d → ℝ}
    (hf : decayNormE k b f < ⊤) {j : ℕ} (hj : j ≤ k) :
    ∃ M : ℝ, ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ M := by
  set M0 : ℝ := (decayNormE k b f).toReal with hM0
  have hterm : ∀ (I : Fin j → Fin d) (x : Euc d),
      |partialDeriv I f x| ≤ M0 := by
    intro I x
    have h1 : ENNReal.ofReal (jbracket x ^ (b + (j : ℝ)) * |partialDeriv I f x|) ≤
        decayNormE k b f := by
      unfold decayNormE derivSupE
      exact le_iSup_of_le (⟨j, Nat.lt_succ_of_le hj⟩ : Fin (k + 1))
        (le_iSup_of_le I (le_iSup_of_le x le_rfl))
    have h2 := (ENNReal.ofReal_le_iff_le_toReal hf.ne).1 h1
    have hj0 : 1 ≤ jbracket x := by
      unfold jbracket
      exact (Real.le_sqrt' one_pos).2 (by nlinarith [sq_nonneg ‖x‖])
    have hj1 : 1 ≤ jbracket x ^ (b + (j : ℝ)) :=
      Real.one_le_rpow hj0 (by have : (0 : ℝ) ≤ j := Nat.cast_nonneg _; linarith)
    nlinarith [mul_le_mul_of_nonneg_right hj1 (abs_nonneg (partialDeriv I f x))]
  refine ⟨(Fintype.card (Fin j → Fin d) : ℝ) * M0, fun x => ?_⟩
  refine (lcf_norm_le_sum _).trans ?_
  calc ∑ I : Fin j → Fin d, |iteratedFDeriv ℝ j f x (fun l => EuclideanSpace.single (I l) (1 : ℝ))|
      ≤ ∑ _I : Fin j → Fin d, M0 := Finset.sum_le_sum fun I _ => hterm I x
    _ = _ := by simp

/-- `IsLocalBackwardSolution` only depends on the drift on `[0,t]`. -/
theorem lcf_solution_congr {ν : ℝ → ℝ} {b b' : ℝ → Euc d → Euc d} {t : ℝ} {f : Euc d → ℝ}
    {u : ℝ → Euc d → ℝ} (hbb : ∀ r ∈ Icc 0 t, ∀ x, b r x = b' r x)
    (h : IsLocalBackwardSolution ν b t f u) : IsLocalBackwardSolution ν b' t f u where
  c2 := h.c2
  bdd := h.bdd
  cont := h.cont
  terminal := h.terminal
  time_deriv x r hr := by
    have := h.time_deriv x r hr
    rwa [hbb r ⟨hr.1.le, hr.2.le⟩ x] at this

end HRS.MS.Lc
