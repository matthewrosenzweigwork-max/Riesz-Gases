import HRS.MS.MovAdjAux26
import HRS.MS.GradSmTie
import HRS.MS.Mov63Tie
import HRS.MS.MovOpAux5
import HRS.MS.MovLinTie
import HRS.MS.S67NlBD04
import HRS.MS.S67NlBD09

/-!
# S6.7 nonlinear breakdown, packet 05: integer oscillator membership from Gaussian jets

`s67bd_gaussian_osc`: every weighted coordinate jet `x^a D^γ u` (`|a| + k ≤ n`) is dominated by
`A (1+|x|)^{|a|} e^{-b|x|²}`, hence (packet 04) lies in `L²` with norm `≤ C_{|a|} A`; packet 09 finishes.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.BreakdownS67

open HRS HRS.Whole HRS.MS.MovLin HRS.MS.MovOsc HRS.MS.MovAdj
open HRS.MS.Mov63 HRS.MS.MovForce HRS.MS.MovC2
open HRS.MS.PoisFlow HRS.MS.PoisSg HRS.MS.PoisKolm HRS.MS.PoisHigh

variable {d : ℕ} {s β q : ℝ} {ρ₀ : Euc d → ℝ}

theorem s67bd_abs_xpow_le (a : MultiIndex d) (x : Euc d) :
    |s67bd_xpow a x| ≤ (1 + ‖x‖) ^ MultiIndex.degree a := by
  unfold s67bd_xpow MultiIndex.degree
  rw [← Finset.prod_pow_eq_pow_sum, Finset.abs_prod]
  refine Finset.prod_le_prod₀ (fun i _ => abs_nonneg _) (fun i _ => ?_)
  rw [abs_pow]
  refine pow_le_pow_left₀ (abs_nonneg _) ?_ _
  have := PiLp.norm_apply_le x i
  rw [Real.norm_eq_abs] at this
  linarith [norm_nonneg x]

theorem s67bd_abs_jet_le (k : ℕ) (γ : Fin k → Fin d) (u : Euc d → ℝ) (x : Euc d) :
    |s67bd_jet k γ u x| ≤ ‖iteratedFDeriv ℝ k u x‖ := by
  unfold s67bd_jet
  have h := (iteratedFDeriv ℝ k u x).le_opNorm (fun l => (EuclideanSpace.single (γ l) (1 : ℝ) : Euc d))
  have hp : ∏ l : Fin k, ‖(EuclideanSpace.single (γ l) (1 : ℝ) : Euc d)‖ = 1 := by simp
  rw [hp, mul_one] at h
  rwa [Real.norm_eq_abs] at h

theorem s67bd_gaussian_osc (d n : ℕ) (b : ℝ) (hb : 0 < b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (A : ℝ), 0 ≤ A → ∀ u : Euc d → ℝ,
      ContDiff ℝ (n : WithTop ℕ∞) u →
      (∀ k ≤ n, ∀ x, ‖iteratedFDeriv ℝ k u x‖ ≤ A * Real.exp (-b * ‖x‖ ^ 2)) →
      MemOsc (n : ℝ) u ∧ oscNorm (n : ℝ) u ≤ C * A := by
  obtain ⟨C9, hC9, h9⟩ := s67bd_integer_converse d n
  have hG : ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (A : ℝ), 0 ≤ A → ∀ v : Euc d → ℝ,
      AEStronglyMeasurable v volume →
      (∀ x, |v x| ≤ A * (1 + ‖x‖) ^ m * Real.exp (-b * ‖x‖ ^ 2)) →
      MemLp v 2 volume ∧ (eLpNorm v 2 volume).toReal ≤ C * A :=
    fun m => s67bd_gaussian_L2 d m b hb
  choose Cg hCg0 hCg using hG
  set Ctot : ℝ := ∑ m ∈ Finset.range (n + 1), Cg m with hCtot
  have hCtot0 : 0 ≤ Ctot := Finset.sum_nonneg fun m _ => hCg0 m
  have hle : ∀ m ≤ n, Cg m ≤ Ctot := fun m hm =>
    Finset.single_le_sum (f := Cg) (fun m _ => hCg0 m) (Finset.mem_range.2 (by omega))
  refine ⟨C9 * Ctot, mul_nonneg hC9 hCtot0, fun A hA u hu hjet => ?_⟩
  have hA' : 0 ≤ Ctot * A := mul_nonneg hCtot0 hA
  obtain ⟨hm, hnorm⟩ := h9 u (Ctot * A) hA' hu (fun k a γ hk => by
    have hkn : k ≤ n := by omega
    have hcont : Continuous (fun x => s67bd_xpow a x * s67bd_jet k γ u x) := by
      refine Continuous.mul ?_ ?_
      · unfold s67bd_xpow
        exact continuous_finsetProd _ fun l _ =>
          ((EuclideanSpace.proj (𝕜 := ℝ) l : Euc d →L[ℝ] ℝ).continuous).pow _
      · unfold s67bd_jet
        exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => Euc d) ℝ
          (fun l => (EuclideanSpace.single (γ l) (1 : ℝ) : Euc d))).continuous.comp
          (hu.continuous_iteratedFDeriv (by exact_mod_cast hkn))
    have hdom : ∀ x, |s67bd_xpow a x * s67bd_jet k γ u x| ≤
        A * (1 + ‖x‖) ^ MultiIndex.degree a * Real.exp (-b * ‖x‖ ^ 2) := by
      intro x
      rw [abs_mul]
      calc |s67bd_xpow a x| * |s67bd_jet k γ u x|
          ≤ (1 + ‖x‖) ^ MultiIndex.degree a * (A * Real.exp (-b * ‖x‖ ^ 2)) :=
            mul_le_mul (s67bd_abs_xpow_le a x) ((s67bd_abs_jet_le k γ u x).trans (hjet k hkn x))
              (abs_nonneg _) (by positivity)
        _ = _ := by ring
    obtain ⟨hmem, hn⟩ := hCg (MultiIndex.degree a) A hA _ hcont.aestronglyMeasurable hdom
    refine ⟨hmem, hn.trans ?_⟩
    have := hle (MultiIndex.degree a) (by omega)
    exact mul_le_mul_of_nonneg_right this hA)
  refine ⟨hm, hnorm.trans (le_of_eq ?_)⟩
  ring

end HRS.MS.BreakdownS67
