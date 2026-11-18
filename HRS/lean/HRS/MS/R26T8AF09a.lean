import HRS.MS.R26T8AF07k
import HRS.MP.RdGenSob

/-!
# S8.2 observed-time layer, packet T8A.F09 (helper 09a): the gradient jets of a Sobolev function

`cbNormVecE K (gradient g) ≤ C · HRS.Whole.sobolevNorm q g` for `q > K + 1 + d/2` and smooth `g`:
`‖∂^k(∇g)‖ ≤ ‖∂^(k+1) g‖` (the gradient is a linear isometry of `fderiv g`) and the Sobolev embedding.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform ComplexConjugate
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux

variable {d : ℕ}

theorem r26t8a_f09a_iter_grad_le (g : Euc d → ℝ) (hg : ContDiff ℝ ∞ g) (k : ℕ) (x : Euc d) :
    ‖iteratedFDeriv ℝ k (fun y => gradient g y) x‖ ≤ ‖iteratedFDeriv ℝ (k + 1) g x‖ := by
  set L : StrongDual ℝ (Euc d) →L[ℝ] Euc d :=
    (InnerProductSpace.toDual ℝ (Euc d)).symm.toContinuousLinearEquiv.toContinuousLinearMap with hL
  have hfd : ContDiff ℝ ∞ (fderiv ℝ g) := hg.fderiv_right (by simp)
  have e : (fun y => gradient g y) = L ∘ (fderiv ℝ g) := funext fun y => rfl
  rw [e, ContinuousLinearMap.iteratedFDeriv_comp_left L hfd.contDiffAt
    (by first | simp | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)]
  refine (ContinuousLinearMap.norm_compContinuousMultilinearMap_le L _).trans ?_
  have hLn : ‖L‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by simp [hL]
  have hF := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := g) (x := x) (n := k)
  rw [hF]
  simpa using mul_le_mul_of_nonneg_right hLn (norm_nonneg _)

theorem r26t8a_f09a_cb (d K : ℕ) (q : ℝ) (hq : (K : ℝ) + 1 + (d : ℝ) / 2 < q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g : Euc d → ℝ, ContDiff ℝ ∞ g → HRS.PDE.ToolboxRd.MemSobolev q g →
      cbNormVecE K (fun y => gradient g y) ≤ ENNReal.ofReal (C * HRS.Whole.sobolevNorm q g) := by
  have hC : ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ (k ≤ K → ∀ g : Euc d → ℝ, ContDiff ℝ ∞ g →
      HRS.PDE.ToolboxRd.MemSobolev q g → ∀ x : Euc d, ‖iteratedFDeriv ℝ (k + 1) g x‖ ≤ C * HRS.Whole.sobolevNorm q g) := by
    intro k
    by_cases hk : k ≤ K
    · have hqk : ((k + 1 : ℕ) : ℝ) + (d : ℝ) / 2 < q := by
        push_cast
        have : (k : ℝ) ≤ K := by exact_mod_cast hk
        linarith
      obtain ⟨C, hC0, hb⟩ := HRS.MP.RdGen.rg_sobolev_embedding (d := d) (k + 1) hqk
      exact ⟨C, hC0, fun _ => fun g hg hm x => hb g hg hm x⟩
    · exact ⟨0, le_rfl, fun h => absurd h hk⟩
  choose Cc hCc0 hCc using hC
  refine ⟨∑ k ∈ Finset.range (K + 1), Cc k, Finset.sum_nonneg fun k _ => hCc0 k, fun g hg hm => ?_⟩
  have hS : 0 ≤ HRS.Whole.sobolevNorm q g := Real.sqrt_nonneg _
  unfold cbNormVecE
  refine le_trans (Finset.sum_le_sum (g := fun k => ENNReal.ofReal (Cc k * HRS.Whole.sobolevNorm q g))
    fun k hk => ?_) (le_of_eq ?_)
  · refine iSup_le fun x => ?_
    have hk' : k ≤ K := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
    have h1 := hCc k hk' g hg hm x
    have h2 := r26t8a_f09a_iter_grad_le g hg k x
    exact ENNReal.ofReal_le_ofReal (h2.trans h1)
  · rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ => mul_nonneg (hCc0 k) hS), Finset.sum_mul]

end HRS.MS.R26T8A

end
