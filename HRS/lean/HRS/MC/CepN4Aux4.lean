import Mathlib
import HRS.MC.CepN4Aux3

/-!
# Packet CEPN4 (aux 4): measurability of the explicit gap remainder
-/

open MeasureTheory Filter Topology Set
open scoped BigOperators

noncomputable section

namespace HRS.MC.CepN4

open HRS Real

variable {N : ℕ}

lemma cepn4_E_measurable (a : ℝ) {ρ : ℝ → ℝ} (hρ : Continuous ρ) {V : Torus 1 → ℝ}
    (hV : Torus.IsCk 1 V) (i0 i1 : Fin N) :
    Measurable fun y : Fin N → Euc 1 => cepn4_E a ρ V y i0 i1 := by
  have hg := (cepn4_continuous_gV hV).measurable
  have hρm := hρ.measurable
  have hcoord : ∀ i : Fin N, Measurable fun y : Fin N → Euc 1 => y i 0 := fun i =>
    ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp (continuous_apply i)).measurable
  unfold cepn4_E cepn4_bdrift cepn4_h
  have hb : ∀ i : Fin N, Measurable fun y : Fin N → Euc 1 =>
      (1 / (N : ℝ)) * ∑ j ∈ Finset.univ.erase i, a * (π * (Real.cos (π * (y i 0 - y j 0)) /
        Real.sin (π * (y i 0 - y j 0))) - ρ (y i 0 - y j 0)) - cepn4_gV V (y i) := by
    intro i
    refine Measurable.sub (Measurable.const_mul (Finset.measurable_sum _ fun j _ => ?_) _)
      (hg.comp (measurable_pi_apply i))
    have hd : Measurable fun y : Fin N → Euc 1 => y i 0 - y j 0 := (hcoord i).sub (hcoord j)
    exact Measurable.const_mul (Measurable.sub (Measurable.const_mul
      ((Real.measurable_cos.comp (hd.const_mul π)).div (Real.measurable_sin.comp (hd.const_mul π))) _)
      (hρm.comp hd)) _
  exact Measurable.sub (Measurable.sub (hb i1) (hb i0))
    (Measurable.div measurable_const ((hcoord i1).sub (hcoord i0)))

end HRS.MC.CepN4
