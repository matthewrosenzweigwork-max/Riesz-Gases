import HRS.MC.SEdgeVocab
import HRS.MC.SEdgeB3
import HRS.Equilibrium.QuadraticLimit.Features
import HRS.Equilibrium.QuadraticVariance

/-!
# Packet B4a: Holder transfer from the product law to the Gibbs law (relocated proof of
`sed_B4a_transfer`)

Route: `Q_{N,beta} << mu^N` with density `w_N`; `q08_weight_Lq` (instantiated with a `Q08Data` built
from `h = 0`, `p = 0` and the ONB of B3) gives `sup_N ||w_N||_{L^q} < infinity`; Holder.  For `beta = 0`
the Gibbs law is the product law (density `1`).
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.SEdge.B4a

open HRS.Sec7

/-- Abstract Holder transfer: `Q << P`, `||dQ/dP||_{L^q(P)}^q <= C0`, `1/r + 1/q = 1`. -/
theorem b4a_holder {α : Type*} [MeasurableSpace α] (P Q : Measure α) [SigmaFinite P]
    [SigmaFinite Q] (hQP : Q ≪ P) {r q : ℝ} (hrq : r.HolderConjugate q) (C0 : ℝ)
    (hw : ∫⁻ x, (Q.rnDeriv P x) ^ q ∂P ≤ ENNReal.ofReal C0) (f : α → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ x, f x ∂Q ≤ ENNReal.ofReal ((max C0 0) ^ (1 / q)) * (∫⁻ x, f x ^ r ∂P) ^ (1 / r) := by
  have hq0 : 0 < q := hrq.symm.pos
  have h1 : ∫⁻ x, f x ∂Q = ∫⁻ x, Q.rnDeriv P x * f x ∂P :=
    (lintegral_rnDeriv_mul hQP hf.aemeasurable).symm
  have h2 : ∫⁻ x, Q.rnDeriv P x * f x ∂P ≤
      (∫⁻ x, (Q.rnDeriv P x) ^ q ∂P) ^ (1 / q) * (∫⁻ x, f x ^ r ∂P) ^ (1 / r) := by
    have := ENNReal.lintegral_mul_le_Lp_mul_Lq P hrq.symm (Measure.measurable_rnDeriv Q P).aemeasurable
      hf.aemeasurable
    simpa using this
  rw [h1]
  refine h2.trans ?_
  gcongr
  calc (∫⁻ x, (Q.rnDeriv P x) ^ q ∂P) ^ (1 / q) ≤ (ENNReal.ofReal C0) ^ (1 / q) := by
        gcongr
    _ ≤ (ENNReal.ofReal (max C0 0)) ^ (1 / q) := by
        gcongr
        exact le_max_left _ _
    _ = ENNReal.ofReal ((max C0 0) ^ (1 / q)) := by
        rw [ENNReal.ofReal_rpow_of_nonneg (le_max_right _ _) (by positivity)]

/-- At `beta = 0` the modulated Gibbs law is the product law. -/
theorem b4a_gibbs_zero {d : ℕ} (g : Torus d → ℝ) (N : ℕ) (μ : Measure (Torus d))
    [IsProbabilityMeasure μ] :
    modulatedGibbs g N 0 μ = Measure.pi fun _ : Fin N => μ := by
  have hn : gibbsNormalizer g N 0 μ = 1 := by
    unfold gibbsNormalizer
    simp
  unfold modulatedGibbs
  rw [hn]
  simp

/-- A constant `c` with `1 ≤ g + c` off zero. -/
theorem b4a_exists_c {d : ℕ} {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) :
    ∃ c : ℝ, ∀ z : Torus d, z ≠ 0 → 1 ≤ periodicRiesz d s z + c := by
  have hdpos : (0 : ℝ) < d := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hsd : s < (d : ℝ) := by linarith
  obtain ⟨Cg, hCg⟩ := HRS.Quad.periodicRiesz_lower_env hd hs0 hsd
  refine ⟨Cg, fun z hz => ?_⟩
  have := HRS.Quad.one_le_envT (d := d) (s := s) z
  have := hCg z hz
  linarith

section Main

variable {d : ℕ} {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {β : ℝ} (hβ : 0 ≤ β)
  {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ)
include hd hs0 hs hβ hρ

theorem sed_B4a_transfer_proof {r : ℝ} (hr : 1 < r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N → ∀ f : Config d N → ℝ≥0∞, Measurable f →
      ∫⁻ X, f X ∂(sed_Q d s N β ρ) ≤
        ENNReal.ofReal C *
          (∫⁻ X, f X ^ r ∂(Measure.pi fun _ : Fin N => withDensityReal ρ)) ^ (1 / r) := by
  have hr0 : 0 < r := by linarith
  set q : ℝ := r / (r - 1) with hq
  have hrq : r.HolderConjugate q := by
    rw [Real.holderConjugate_iff]
    refine ⟨hr, ?_⟩
    have : r - 1 ≠ 0 := by linarith
    rw [hq]
    field_simp
    ring
  have hq1 : 1 ≤ q := (Real.HolderConjugate.symm hrq).lt.le
  haveI : IsProbabilityMeasure (withDensityReal ρ) := HRS.MC.SEdge.B3.b3_prob hρ
  rcases hβ.eq_or_lt with h0 | hpos
  · -- β = 0
    subst h0
    refine ⟨1, zero_le_one, fun N hN f hf => ?_⟩
    have hQ : sed_Q d s N 0 ρ = Measure.pi fun _ : Fin N => withDensityReal ρ :=
      b4a_gibbs_zero _ _ _
    rw [hQ]
    have := b4a_holder (Measure.pi fun _ : Fin N => withDensityReal ρ)
      (Measure.pi fun _ : Fin N => withDensityReal ρ) Measure.AbsolutelyContinuous.rfl hrq 1
      (by
        have h1 : ∀ᵐ x ∂(Measure.pi fun _ : Fin N => withDensityReal ρ),
            ((Measure.pi fun _ : Fin N => withDensityReal ρ).rnDeriv
              (Measure.pi fun _ : Fin N => withDensityReal ρ) x) ^ q = 1 := by
          filter_upwards [Measure.rnDeriv_self (Measure.pi fun _ : Fin N => withDensityReal ρ)]
            with x hx
          rw [hx]
          simp
        rw [lintegral_congr_ae h1]
        simp) f hf
    simpa using this
  · -- β > 0
    obtain ⟨e, he⟩ := HRS.MC.SEdge.B3.sed_B3_onb_proof (by omega : 1 ≤ d) hρ
    obtain ⟨c, hc⟩ := b4a_exists_c hd hs0 hs
    let D : HRS.Q08.Q08Data d :=
      { s := s, β := β, ρ := ρ, c := c, B := 0, h := fun _ _ => 0, e := e, p := 0,
        φ := fun a => a.elim0, hd := hd, hs0 := hs0, hs := hs, hβ := hpos, hρ := hρ,
        hc := hc, hmeas := measurable_const, hsymm := fun _ _ => rfl,
        hB := fun x y _ => by simp, he := he,
        hφ := fun a => a.elim0 }
    obtain ⟨C0, hC0⟩ := HRS.Q08.q08_weight_Lq D q hq1
    refine ⟨(max C0 0) ^ (1 / q), by positivity, fun N hN f hf => ?_⟩
    haveI : IsProbabilityMeasure (D.Gibbs N) := HRS.Q08.q08_gibbs_isProb D N hN
    haveI : IsProbabilityMeasure (D.prodLaw N) := by
      unfold HRS.Q08.Q08Data.prodLaw; infer_instance
    exact b4a_holder (D.prodLaw N) (D.Gibbs N) (HRS.Q08.q08f_gibbs_ac D N) hrq C0 (hC0 N hN) f hf

end Main


end HRS.MC.SEdge.B4a
