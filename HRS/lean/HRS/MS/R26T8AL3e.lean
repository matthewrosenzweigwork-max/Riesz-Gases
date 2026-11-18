import HRS.MS.R26T8AL3d

/-!
# S8.2 observed-time layer, generic lemma L3 (final): Sobolev multiplier by a smooth bounded-derivative coefficient

For `c` smooth with every iterated derivative bounded and `v` `SobSmooth`:
`c · v` is `SobSmooth` and `sobolevNormE m (c·v) ≤ C_m · sobolevNormE m v` for every natural `m`.
Route: pointwise Leibniz bound on the directional iterates, weak-derivative chains (Q09A `memSobolev_of_chains`),
and Cauchy–Schwarz on the Leibniz sum.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform ComplexConjugate
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux HRS.Whole.Q09A LineDeriv

variable {d : ℕ}

theorem r26t8a_l3e_pw (i : Fin d) (c v : Euc d → ℝ) (hc : ContDiff ℝ ∞ c)
    (Bc : ℕ → ℝ) (hBc : ∀ k (x : Euc d), ‖iteratedFDeriv ℝ k c x‖ ≤ Bc k)
    (hv : r26t8a_SobSmooth v) (j : ℕ) (x : Euc d) :
    |(r26t8a_l3_D i)^[j] (fun y => c y * v y) x| ≤
      ∑ k ∈ Finset.range (j + 1), (j.choose k : ℝ) * (|Bc k| * |(r26t8a_l3_D i)^[j - k] v x|) := by
  rw [r26t8a_l3_leibniz i c v hc hv.1 j]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  have ha : |(r26t8a_l3_D i)^[k] c x| ≤ |Bc k| :=
    (r26t8a_l3_iter_bound i c hc k x).trans ((hBc k x).trans (le_abs_self _))
  calc |(j.choose k : ℝ) * ((r26t8a_l3_D i)^[k] c x * (r26t8a_l3_D i)^[j - k] v x)|
      = (j.choose k : ℝ) * (|(r26t8a_l3_D i)^[k] c x| * |(r26t8a_l3_D i)^[j - k] v x|) := by
        rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
    _ ≤ (j.choose k : ℝ) * (|Bc k| * |(r26t8a_l3_D i)^[j - k] v x|) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ha (abs_nonneg _)) (Nat.cast_nonneg _)

theorem r26t8a_l3e_bdd (i : Fin d) (c v : Euc d → ℝ) (hc : ContDiff ℝ ∞ c)
    (hcb : ∀ n : ℕ, ∃ B : ℝ, ∀ x, ‖iteratedFDeriv ℝ n c x‖ ≤ B) (hv : r26t8a_SobSmooth v) (j : ℕ) :
    ∃ B : ℝ, ∀ x, |(r26t8a_l3_D i)^[j] (fun y => c y * v y) x| ≤ B := by
  choose Bc hBc using hcb
  choose Bv hBv using fun l => r26t8a_l3d_bdd_iter i v hv l
  refine ⟨∑ k ∈ Finset.range (j + 1), (j.choose k : ℝ) * (|Bc k| * |Bv (j - k)|), fun x => ?_⟩
  refine (r26t8a_l3e_pw i c v hc Bc (fun k x => hBc k x) hv j x).trans
    (Finset.sum_le_sum fun k _ => ?_)
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ((hBv (j - k) x).trans (le_abs_self _))
    (abs_nonneg _)) (Nat.cast_nonneg _)

theorem r26t8a_l3e_wd (i : Fin d) (c v : Euc d → ℝ) (hc : ContDiff ℝ ∞ c)
    (hcb : ∀ n : ℕ, ∃ B : ℝ, ∀ x, ‖iteratedFDeriv ℝ n c x‖ ≤ B) (hv : r26t8a_SobSmooth v) (j : ℕ) :
    WD i (fun x => (((r26t8a_l3_D i)^[j] (fun y => c y * v y) x : ℝ) : ℂ))
      (fun x => (((r26t8a_l3_D i)^[j + 1] (fun y => c y * v y) x : ℝ) : ℂ)) := by
  obtain ⟨B0, hB0⟩ := r26t8a_l3e_bdd i c v hc hcb hv j
  obtain ⟨B1, hB1⟩ := r26t8a_l3e_bdd i c v hc hcb hv (j + 1)
  have hcu : ContDiff ℝ ∞ ((r26t8a_l3_D i)^[j] (fun y => c y * v y)) :=
    r26t8a_l3_contDiff_iter i _ (hc.mul hv.1) j
  have hfe : ∀ x, fderiv ℝ ((r26t8a_l3_D i)^[j] (fun y => c y * v y)) x (EuclideanSpace.single i (1 : ℝ))
      = (r26t8a_l3_D i)^[j + 1] (fun y => c y * v y) x := fun x => by
    rw [Function.iterate_succ_apply']
    rfl
  have hmemf := (r26t8a_l3d_memLp_iter i c v hc hv hcb j).ofReal (K := ℂ)
  have hmemg := (r26t8a_l3d_memLp_iter i c v hc hv hcb (j + 1)).ofReal (K := ℂ)
  refine ⟨hmemf, hmemg, fun ψ => ?_⟩
  have h := r26t8a_l3d_ibp _ (EuclideanSpace.single i (1 : ℝ)) hcu B0 B1 hB0
    (fun x => by rw [hfe x]; exact hB1 x) ψ
  simp only [hfe] at h
  exact h

end HRS.MS.R26T8A

end
