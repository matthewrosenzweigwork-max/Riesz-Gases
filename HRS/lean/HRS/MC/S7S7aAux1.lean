import HRS.MC.SEdgeB1
import HRS.MC.Sec7Vocab
import HRS.PDE.MeanFieldAprioriUpper
import HRS.PDE.MeanFieldAprioriLower
import HRS.PDE.MeanFieldAprioriSobolev
import HRS.PDE.MeanFieldProductB
import HRS.PDE.MeanFieldProduct
import HRS.PDE.MeanFieldThermalReg
import HRS.PDE.ClassicalPart
import HRS.PDE.MeanFieldPairSeries
import HRS.Equilibrium.PoleCavity
import HRS.Kernel.ResponseAux

/-!
# Packet `s7_S7a_mode_data`, helper 1: Sobolev embedding `H^{d+2} -> C^1` with an explicit constant
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ComplexConjugate

noncomputable section

namespace HRS.MC.Sec7.S7a

open HRS HRS.PDE HRS.PDE.MFApriori HRS.PDE.MFPair HRS.PDE.MFThermalReg HRS.PDE.ClassicalPart

variable {d : ℕ}

theorem s7a_cb1_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ f : Torus d → ℝ, Torus.IsSmooth f →
    Torus.cbNorm 1 f ≤ C * HRS.PDE.hsNorm (((d + 2 : ℕ)) : ℝ) (coeffOf f) := by
  obtain ⟨C, hC0, hC⟩ := exists_ws_bound (d := d) 1 ((d + 2 : ℕ) : ℝ) (by
    push_cast; have : (0 : ℝ) ≤ d := Nat.cast_nonneg d; linarith)
  refine ⟨(1 + d) * C, by positivity, fun f hf => ?_⟩
  have hfc : Continuous f := HRS.Q66.q66_cont_of_smooth hf
  have hm : MemHs ((d + 2 : ℕ) : ℝ) (coeffOf f) :=
    (ClassicalPart.memHs_coeffOf_cbNorm (d + 2) f (HRS.Q66.q66_isCk_of_smooth hf _)).1
  obtain ⟨hWS, hWN⟩ := hC _ hm
  set B : ℝ := C * HRS.PDE.hsNorm ((d + 2 : ℕ) : ℝ) (coeffOf f) with hB
  have hB0 : 0 ≤ B := mul_nonneg hC0 (Real.sqrt_nonneg _)
  have hWS0 : WS 0 (coeffOf f) := hWS.mono (by norm_num)
  have hf0 : ∀ x, |f x| ≤ B := fun x => by
    have h1 : toFun (coeffOf f) = f := toFun_coeffOf f hfc ((WS_zero_iff _).1 hWS0)
    have := abs_toFun_le_WN hWS0 x
    rw [h1] at this
    exact this.trans ((WN_mono (by norm_num) hWS).trans hWN)
  have hder : ∀ (i : Fin d) x, |Torus.partialDeriv i f x| ≤ B := fun i x => by
    have hsm := HRS.Q66.q66_isSmooth_partialDeriv hf i
    have hc : Continuous (Torus.partialDeriv i f) := HRS.Q66.q66_cont_of_smooth hsm
    have hco : coeffOf (Torus.partialDeriv i f) = derivCoeff i (coeffOf f) :=
      coeffOf_partialDeriv i f (HRS.Q66.q66_isCk_of_smooth hf 1)
    have hW : WS 0 (derivCoeff i (coeffOf f)) := WS_deriv0 hWS i
    have h1 : toFun (coeffOf (Torus.partialDeriv i f)) = Torus.partialDeriv i f :=
      toFun_coeffOf _ hc ((WS_zero_iff _).1 (hco ▸ hW))
    have := abs_toFun_le_WN (hco ▸ hW) x
    rw [h1, hco] at this
    exact this.trans ((WN_deriv0 hWS i).trans hWN)
  have hgrad : ∀ x, ‖Torus.grad f x‖ ≤ d * B := fun x => by
    rw [EuclideanSpace.norm_eq]
    refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
    have : ∀ i, ‖Torus.grad f x i‖ ^ 2 ≤ B ^ 2 := fun i => by
      rw [Real.norm_eq_abs, MFAux.grad_apply]
      exact pow_le_pow_left₀ (abs_nonneg _) (hder i x) 2
    calc ∑ i, ‖Torus.grad f x i‖ ^ 2 ≤ ∑ _i : Fin d, B ^ 2 := Finset.sum_le_sum fun i _ => this i
      _ = d * B ^ 2 := by simp
      _ ≤ (d * B) ^ 2 := by
        have hd1 : (1 : ℝ) ≤ d ∨ d = 0 := by
          rcases Nat.eq_zero_or_pos d with h | h
          · right; exact h
          · left; exact_mod_cast h
        rcases hd1 with h | h
        · nlinarith [sq_nonneg B]
        · subst h; simp
  have := cbNorm_one_le hB0 (by positivity) hf0 hgrad
  calc Torus.cbNorm 1 f ≤ B + d * B := this
    _ = (1 + d) * C * HRS.PDE.hsNorm ((d + 2 : ℕ) : ℝ) (coeffOf f) := by rw [hB]; ring

end HRS.MC.Sec7.S7a

end
