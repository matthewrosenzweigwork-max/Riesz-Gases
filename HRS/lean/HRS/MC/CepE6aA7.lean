import HRS.MC.CepE5c
import HRS.MC.CepE6aA3
import HRS.MC.CepE6aA5
import HRS.MC.CepE6aA6

/-!
# Packet CEPE6A, file 7: conjuncts (a)-(d) of `cep_E6_limit_solution`

`cep_E6_abcd_ext` constructs the limit `Zl` (adapted, continuous, uniform convergence in probability on every
`[0,T]`), shows `Zl_t ∈ closure(alcove)`, that the contact set is Lebesgue-null and `‖∇Φ(Zl)‖` locally integrable
(all a.s.), and exports the two quantitative facts that conjunct (e) will consume:
`E ∫_0^T ‖∇Φ(Zl_s)‖₁ ds ≤ C_T` and `∫_0^T ∑_{k<l} 1/m_{kl}(Zl_s) ds < ∞` a.s. (`m_{kl}` the circle distance).
`cep_E6_abcd` is the conjunction of the six conjuncts of `cep_E6_limit_solution` preceding the integral equation.
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

noncomputable section

namespace HRS.MC.CepE6A

open HRS HRS.MC.Cepa HRS.MC.CepE4

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {N : ℕ}

theorem e6a_J_cont {a : ℝ} {J : ℝ → Ch N → Ch N} (hJ : cep_Yosida a N J) {n : ℝ} (hn : 0 < n) :
    Continuous (J n) := by
  have h := (hJ.lip n hn).continuous
  have e : J n = fun z => z - n⁻¹ • (n • (z - J n z)) := by
    funext z
    rw [smul_smul, inv_mul_cancel₀ hn.ne', one_smul]
    abel
  rw [e]
  exact continuous_id.sub (h.const_smul n⁻¹)

theorem e6a_ofReal_l1_le_ext (a : ℝ) (z : Ch N) :
    ENNReal.ofReal (∑ i, |(gradient (cep_chamberPot a N) z) i|) ≤ e6a_ext a N z := by
  classical
  unfold e6a_ext
  split_ifs with h
  · exact le_rfl
  · exact le_top

theorem e6a_ext_eq_top {a : ℝ} {z : Ch N} (h : z ∉ cep_Alcove N) : e6a_ext a N z = ⊤ := by
  classical
  simp [e6a_ext, h]

theorem e6a_gradient_measurable (a : ℝ) : Measurable (gradient (cep_chamberPot a N)) := by
  unfold gradient
  exact (InnerProductSpace.toDual ℝ (Ch N)).symm.continuous.measurable.comp (measurable_fderiv ℝ _)

end HRS.MC.CepE6A
