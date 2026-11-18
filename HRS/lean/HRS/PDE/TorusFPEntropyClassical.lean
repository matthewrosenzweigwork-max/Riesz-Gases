import HRS.PDE.TorusFPEntropyClassicalAux5

/-!
# D3-a: the classical layer of the free-energy identity (proofs of the four D3-a specifications)

Relocated proofs of the frozen specifications `HRS.d3_classical_exists`, `HRS.d3_classical_isWeak`,
`HRS.d3_fisher_classical`, `HRS.d3_tilted_identity_classical` (`HRS/PDE/TorusFPEntropySpec.lean`; the
statements there are unchanged and keep their `sorry`).  Each theorem below is tied to its specification
by `example := (@..._proof : type_of% @...)`.

Route (helpers `TorusFPEntropyClassicalAux1`-`Aux5`, names `d3a_*`):

* `Aux1`: product rule / logarithm / tilt for `Torus.partialDeriv`, the Gibbs probability measure, the
  weighted Green identity `∫ (L w) f dP = -κ ∫ ⟨∇f, ∇w⟩ dP` and `G`-self-adjointness of `L`;
* `Aux2`: parametric integrals and the integrated product rule `d3a_ftc` (differentiation under the integral);
* `Aux3`: existence (time reversal of `d1_backward_classical`, minimum principle) and the weak formulation;
* `Aux4`: Fisher information of a classical density (integration by parts, uniform approximation of the
  continuous field `∇ log w - ∇ψ` by smooth fields);
* `Aux5`: the exact free-energy identity.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HRS

variable {n : ℕ}

theorem d3_classical_exists_proof (hn : 1 ≤ n) {κ : ℝ} (hκ : 0 < κ) {U : Torus n → ℝ}
    (hU : Torus.IsSmooth U) {T : ℝ} (hT : 0 < T) {w0 : Torus n → ℝ} (hw0 : Torus.IsSmooth w0)
    (hpos : ∀ x, 0 < w0 x) :
    ∃ w : ℝ → Torus n → ℝ, D3Classical κ U T w ∧ w 0 = w0 :=
  d3a_exists hn hκ hU hT hw0 hpos

example := (@d3_classical_exists_proof : type_of% @d3_classical_exists)

theorem d3_classical_isWeak_proof (hn : 1 ≤ n) {κ : ℝ} (hκ : 0 < κ) {U : Torus n → ℝ}
    (hU : Torus.IsSmooth U) {T : ℝ} {w : ℝ → Torus n → ℝ} (hw : D3Classical κ U T w) :
    D1WeakSolution κ (d1_gradDrift U) T
      (fun s => (d1_gibbsMeasure κ U).withDensity fun x => ENNReal.ofReal (w s x)) :=
  d3a_isWeak hn hκ hU hw

example := (@d3_classical_isWeak_proof : type_of% @d3_classical_isWeak)

theorem d3_fisher_classical_proof {κ : ℝ} (hκ : 0 < κ) {U : Torus n → ℝ} (hU : Torus.IsSmooth U)
    {w ψ : Torus n → ℝ} (hw : Torus.IsCk 2 w) (hwpos : ∀ x, 0 < w x) (hψ : Torus.IsCk 2 ψ) :
    d1_fisherInfo κ (d3_tiltPot κ U ψ)
        ((d1_gibbsMeasure κ U).withDensity fun x => ENNReal.ofReal (w x))
      = ENNReal.ofReal (∫ x, ‖Torus.grad (fun y => Real.log (w y)) x - Torus.grad ψ x‖ ^ 2
          ∂((d1_gibbsMeasure κ U).withDensity fun x => ENNReal.ofReal (w x))) :=
  d3a_fisher hκ hU hw hwpos hψ

example := (@d3_fisher_classical_proof : type_of% @d3_fisher_classical)

theorem d3_tilted_identity_classical_proof (hn : 1 ≤ n) {κ : ℝ} (hκ : 0 < κ) {U : Torus n → ℝ}
    (hU : Torus.IsSmooth U) {T : ℝ} (hT : 0 < T) {w : ℝ → Torus n → ℝ} (hw : D3Classical κ U T w)
    (hmass : ∫ x, w 0 x ∂(d1_gibbsMeasure κ U) = 1) {ψ ψt : ℝ → Torus n → ℝ} (hψ : IsC12Test T ψ ψt) :
    ∀ t ∈ Set.Icc 0 T,
      (relEntropy ((d1_gibbsMeasure κ U).withDensity fun x => ENNReal.ofReal (w t x))
          (d1_gibbsMeasure κ U)).toReal
        - ∫ x, ψ t x ∂((d1_gibbsMeasure κ U).withDensity fun x => ENNReal.ofReal (w t x))
        + κ * ∫ r in Set.Icc 0 t, ∫ x, ‖Torus.grad (fun y => Real.log (w r y)) x - Torus.grad (ψ r) x‖ ^ 2
            ∂((d1_gibbsMeasure κ U).withDensity fun x => ENNReal.ofReal (w r x))
      = (relEntropy ((d1_gibbsMeasure κ U).withDensity fun x => ENNReal.ofReal (w 0 x))
          (d1_gibbsMeasure κ U)).toReal
        - ∫ x, ψ 0 x ∂((d1_gibbsMeasure κ U).withDensity fun x => ENNReal.ofReal (w 0 x))
        + ∫ r in Set.Icc 0 t, ∫ x, d3_source κ U ψ ψt r x
            ∂((d1_gibbsMeasure κ U).withDensity fun x => ENNReal.ofReal (w r x)) :=
  d3a_identity hn hκ hU hT hw hmass hψ

example := (@d3_tilted_identity_classical_proof : type_of% @d3_tilted_identity_classical)

end HRS
