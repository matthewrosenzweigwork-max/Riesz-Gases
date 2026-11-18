import HRS.MS.Fp81S21GaussianPropagated
import HRS.MS.Fp81S21WickApprox33

/-!
# Spatial zero mass of the selected quadratic Gaussian field

The packet-31 payload is quantified over every Gaussian realization. Its weak
moment representation supplies joint measurability, slice L² membership, and
compact-test agreement with the strong chart field. The latter agrees with the
payload's own supplied Wick operator. Constant cancellation therefore applies
to the selected weak field itself, for every realization.

Fubini changes the order of the time and sample almost-everywhere quantifiers
using the measurable constant-test action. No simultaneous event over all
real times, replacement field, or additional source hypothesis is needed.
The requested binders and conclusion are unchanged.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Classical MeasureTheory Filter Set
open scoped ENNReal

namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6

/-- The selected weak quadratic field has spatial zero mass for almost every
sample and almost every time in the full history interval. -/
theorem fp81s21_quadraticPhysical31_zero_mass
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4))
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2))
    {ε : ℕ → ℝ} (S : fp81s21_QuadraticPhysical31 p R Es E ε)
    (G : GaussianRealization R) (H : ℝ) (hH : 0 ≤ H) :
    ∀ᵐ ω ∂G.P, ∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) H),
      fp81s21_chartAction E (S.qe G s ω) (fun _ => 1) = 0 := by
  clear hH
  have he := (S.payload G).2.2.2.2.1
  have hfixed : ∀ u, 0 ≤ u →
      (fun ω => fp81s21_chartAction E (S.qe G u ω) (fun _ => 1)) =ᵐ[G.P] 0 := by
    apply fp81s21_wick_constant_agreement_time p R E G.P (S.W G) (S.qe G)
      (fun u hu => (he.2 u hu).1)
    intro u hu g hg hk
    obtain ⟨hk', hag⟩ := (S.payload G).2.2.2.2.2.1 u hu g hg
    have hchart : (fun ω => fp81s21_chartAction E (S.qe G u ω) g) =ᵐ[G.P]
        (fun ω => fp81s21_wickChartField Es (S.qs G) u ω g) := by
      filter_upwards [(he.2 u hu).2.2] with ω hω
      exact hω.1 g hg
    exact hchart.trans hag
  let dt : Measure ℝ := volume.restrict (Icc (0 : ℝ) H)
  let F : ℝ × G.Ω → ℝ := fun z =>
    fp81s21_chartAction E (S.qe G z.1 z.2) (fun _ => 1)
  have hF : Measurable F := by
    change Measurable (fun z : ℝ × G.Ω =>
      inner ℝ (Function.uncurry (S.qe G) z) (E.encode (fun _ => 1)))
    exact he.1.inner measurable_const
  have hsections : ∀ᵐ s ∂dt, ∀ᵐ ω ∂G.P, F (s, ω) = 0 := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    exact hfixed s hs.1
  have hprod : ∀ᵐ z ∂dt.prod G.P, F z = 0 := by
    exact (Measure.ae_prod_iff_ae_ae
      (measurableSet_eq_fun hF measurable_const)).2 hsections
  have hswap :=
    (Measure.measurePreserving_swap (μ := G.P) (ν := dt)).quasiMeasurePreserving.ae hprod
  exact Measure.ae_ae_of_ae_prod hswap

#print axioms fp81s21_quadraticPhysical31_zero_mass

end HRS.Fp81.S21
end
