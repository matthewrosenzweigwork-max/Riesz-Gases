import HRS.MC.CepK0
import HRS.MC.CepK2

/-!
# Packet CEPU2 (aux 1): deterministic ingredients of the pathwise uniqueness of the Cépa–Lépingle flow

* `cepu2_gronwall`: K3 for `Fin N → Euc 1`-valued differences (through `PiLp 2`);
* torus/lattice helpers and strictness of an ordered contact-free lift;
* `cepu2_transfer`: continuous lifts and the non-continuous strong-solution lifts have the same
  increment equation (via U1 applied to the clipped primitive).
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.CepU2

open HRS

/-- K3 for `Fin N → Euc 1`-valued paths, componentwise integral equation. -/
theorem cepu2_gronwall {N : ℕ} {T Λ : ℝ} (hT : 0 ≤ T) {F Z : ℝ → Fin N → Euc 1}
    (hF : ∀ i, IntervalIntegrable (fun s => F s i) volume 0 T)
    (hZ : ∀ t ∈ Set.Icc 0 T, ∀ i, Z t i = Z 0 i + ∫ s in (0 : ℝ)..t, F s i)
    (h0 : Z 0 = 0)
    (hdiss : ∀ᵐ s ∂(volume.restrict (Set.Icc 0 T)),
      ∑ i, inner ℝ (Z s i) (F s i) ≤ Λ * ∑ i, ‖Z s i‖ ^ 2) :
    ∀ t ∈ Set.Icc 0 T, Z t = 0 := by
  let E := PiLp 2 (fun _ : Fin N => Euc 1)
  have hF' : IntervalIntegrable (fun s => (WithLp.toLp 2 (F s) : E)) volume 0 T := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT]
    refine MeasureTheory.integrable_piLp_iff.2 fun i => ?_
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).1 (hF i)
  have key := HRS.MC.CepK0.cep_K3_gronwall_ac_proof (E := E) (Z := fun s => (WithLp.toLp 2 (Z s) : E))
    (F := fun s => (WithLp.toLp 2 (F s) : E)) (T := T) (Λ := Λ) hT hF' ?_ ?_ ?_
  · intro t ht
    exact (WithLp.toLp_injective 2) (by rw [key t ht]; simp)
  · intro t ht
    refine PiLp.ext fun i => ?_
    have hti : (0:ℝ) ≤ t := ht.1
    rw [intervalIntegral.integral_of_le hti, PiLp.add_apply]
    rw [MeasureTheory.eval_integral_piLp]
    · simpa [intervalIntegral.integral_of_le hti] using hZ t ht i
    · intro i
      have h1 : IntervalIntegrable (fun s => F s i) volume 0 t :=
        (hF i).mono_set (by rw [Set.uIcc_of_le hti, Set.uIcc_of_le hT]; exact Set.Icc_subset_Icc le_rfl ht.2)
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hti).1 h1
  · simp [h0]
  · filter_upwards [hdiss] with s hs
    rw [PiLp.inner_apply, PiLp.norm_sq_eq_of_L2]
    simpa using hs

end HRS.MC.CepU2
