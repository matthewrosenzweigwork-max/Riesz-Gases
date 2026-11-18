import HRS.MS.ShiftFldAux3
import HRS.MS.GenPathAux10
import HRS.Main.ThermAux2

/-!
# S79: continuity of the empirical field, translation invariance of `W_p`

* `s79_continuous_ofMeasureDiff_empirical`: `X ↦ μ_N(X) - ν ∈ B_m` is continuous on `(ℝ^d)^N` for `m > d`
  (dominated convergence on the Hermite coordinates; `|h_α| ≤ C₀`, `∑ λ^{-m} < ∞`).
* `s79_wassersteinE_map_add_le`: `W_p(P(· + v), Q(· + v)) ≤ W_p(P, Q)` (push a coupling forward by the translation).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.Whole.S79

open HRS (Euc)

variable {d : ℕ} {m : ℝ}

theorem s79_continuous_ofMeasureDiff_empirical {N : ℕ} (hN : 0 < N) (hm : (d : ℝ) < m)
    (ν : Measure (Euc d)) [IsFiniteMeasure ν] :
    Continuous (fun x : EucConfig d N => OscDual.ofMeasureDiff m (empirical x) ν) := by
  obtain ⟨C0, hC0⟩ := hermiteFunD_uniform_bound (d := d)
  have hC0nn : 0 ≤ C0 := (abs_nonneg _).trans (hC0 0 0)
  have hS := OscDual.summable_oscEv_neg_rpow (d := d) hm
  set c : MultiIndex d → EucConfig d N → ℝ := fun α x => (N : ℝ)⁻¹ * ∑ i, hermiteFunD α (x i) with hc
  have hcc : ∀ α, Continuous (c α) := fun α =>
    continuous_const.mul (continuous_finset_sum _ fun i _ =>
      (contDiff_hermiteFunD α).continuous.comp (continuous_apply i))
  have hcb : ∀ α x, |c α x| ≤ C0 := by
    intro α x
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    simp only [hc, abs_mul, abs_inv, Nat.abs_cast]
    calc (N : ℝ)⁻¹ * |∑ i, hermiteFunD α (x i)| ≤ (N : ℝ)⁻¹ * ∑ i : Fin N, C0 := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => hC0 α (x i))
      _ = C0 := by simp [Finset.sum_const]; field_simp
  have hcoef : ∀ (x : EucConfig d N) α, OscDual.hermiteCoeff
      (OscDual.ofMeasureDiff m (empirical x) ν) α = c α x - measureHermiteCoeff ν α := by
    intro x α
    haveI : IsProbabilityMeasure (empirical x) := empirical_isProbabilityMeasure hN x
    rw [OscDual.hermiteCoeff_ofMeasureDiff hm]
    congr 1
    exact pair_empirical hN x (hermiteFunD α)
  rw [continuous_iff_continuousAt]
  intro x₀
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hnorm : ∀ x : EucConfig d N, ‖OscDual.ofMeasureDiff m (empirical x) ν -
      OscDual.ofMeasureDiff m (empirical x₀) ν‖ =
      Real.sqrt (∑' α : MultiIndex d, oscEigenvalue d α ^ (-m) * (c α x - c α x₀) ^ 2) := by
    intro x
    rw [OscDual.norm_eq]
    congr 1
    refine tsum_congr fun α => ?_
    rw [s79_hermiteCoeff_sub, hcoef, hcoef]
    ring_nf
  simp_rw [hnorm]
  have hlim : Tendsto (fun x : EucConfig d N =>
      ∑' α : MultiIndex d, oscEigenvalue d α ^ (-m) * (c α x - c α x₀) ^ 2) (𝓝 x₀)
      (𝓝 (∑' α : MultiIndex d, (0 : ℝ))) := by
    refine tendsto_tsum_of_dominated_convergence (bound := fun α => 4 * C0 ^ 2 * oscEigenvalue d α ^ (-m))
      (hS.mul_left (4 * C0 ^ 2)) (fun α => ?_) (Filter.Eventually.of_forall fun x α => ?_)
    · have : Tendsto (fun x : EucConfig d N => oscEigenvalue d α ^ (-m) * (c α x - c α x₀) ^ 2) (𝓝 x₀)
          (𝓝 (oscEigenvalue d α ^ (-m) * (c α x₀ - c α x₀) ^ 2)) :=
        (continuous_const.mul (((hcc α).sub continuous_const).pow 2)).tendsto x₀
      simpa using this
    · have hl := Real.rpow_nonneg (oscEv_pos α).le (-m)
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hl (sq_nonneg _))]
      have h2 : (c α x - c α x₀) ^ 2 ≤ 4 * C0 ^ 2 := by
        have h1 := hcb α x
        have h3 := hcb α x₀
        nlinarith [abs_le.1 h1, abs_le.1 h3]
      calc _ ≤ oscEigenvalue d α ^ (-m) * (4 * C0 ^ 2) := mul_le_mul_of_nonneg_left h2 hl
        _ = _ := by ring
  rw [tsum_zero] at hlim
  have h2 := (Real.continuous_sqrt.tendsto 0).comp hlim
  rw [Real.sqrt_zero] at h2
  exact h2

section Wass

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [MeasurableSpace B] [BorelSpace B]
  [SecondCountableTopology B]

theorem s79_wassersteinE_map_add_le (p : ℝ) (P Q : Measure B) (v : B) :
    HRS.wassersteinE p (P.map (· + v)) (Q.map (· + v)) ≤ HRS.wassersteinE p P Q := by
  unfold HRS.wassersteinE
  refine le_iInf fun π => ?_
  set f : B × B → B × B := fun z => (z.1 + v, z.2 + v) with hf
  have hfm : Measurable f := by fun_prop
  have hπ : HRS.IsCoupling (π.1.map f) (P.map (· + v)) (Q.map (· + v)) := by
    obtain ⟨h1, h2⟩ := π.2
    constructor
    · calc (π.1.map f).map Prod.fst = (π.1.map Prod.fst).map (· + v) := by
            rw [Measure.map_map measurable_fst hfm,
              Measure.map_map (measurable_add_const v) measurable_fst]; rfl
        _ = P.map (· + v) := by rw [h1]
    · calc (π.1.map f).map Prod.snd = (π.1.map Prod.snd).map (· + v) := by
            rw [Measure.map_map measurable_snd hfm,
              Measure.map_map (measurable_add_const v) measurable_snd]; rfl
        _ = Q.map (· + v) := by rw [h2]
  refine (iInf_le (fun π : HRS.couplings (P.map (· + v)) (Q.map (· + v)) =>
    (∫⁻ z, ENNReal.ofReal (‖z.1 - z.2‖ ^ p) ∂π.1) ^ (1 / p)) ⟨π.1.map f, hπ⟩).trans ?_
  show (∫⁻ z, ENNReal.ofReal (‖z.1 - z.2‖ ^ p) ∂(π.1.map f)) ^ (1 / p) ≤ _
  rw [lintegral_map (by fun_prop) hfm]
  refine le_of_eq ?_
  congr 2
  funext z
  simp [hf]

end Wass

end HRS.Whole.S79
