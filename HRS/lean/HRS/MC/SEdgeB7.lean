import HRS.MC.SEdgeVocab
import HRS.MC.SEdgeB3
import HRS.MC.SEdgeB4a
import HRS.MC.SEdgeB4c

/-!
# Packet B7: law of large numbers in `L^{2m}` under the Gibbs law (relocated proof of `sed_B7_lln`)

Route: B4a with `r = 2` reduces `E_Q Z^{2m}` to `(E_{mu^N} Z^{4m})^{1/2}`, which B4c bounds by
`(C/N^{2m})^{1/2}`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.SEdge.B7

open HRS.Sec7

/-- Boundedness of the centred empirical average of a bounded function. -/
theorem b7_bound {d N : ℕ} (hN : 1 ≤ N) (μ : Measure (Torus d)) [IsProbabilityMeasure μ]
    {M : ℝ} {u : Torus d → ℝ} (hum : Measurable u) (hb : ∀ x, |u x| ≤ M) (X : Config d N) :
    |pair (empirical X) u - pair μ u| ≤ 2 * M := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 : |pair (empirical X) u| ≤ M := by
    rw [HRS.MC.SEdge.B4c.b4c_pair_empirical X hum, abs_div, abs_of_pos hNpos,
      div_le_iff₀ hNpos]
    calc |∑ i, u (X i)| ≤ ∑ i, |u (X i)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin N, M := Finset.sum_le_sum fun i _ => hb _
      _ = M * N := by simp [mul_comm]
  have h2 : |pair μ u| ≤ M := by
    unfold pair
    have := norm_integral_le_of_norm_le_const (μ := μ) (f := u) (C := M)
      (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hb x)
    simpa using this
  calc |pair (empirical X) u - pair μ u| ≤ |pair (empirical X) u| + |pair μ u| := abs_sub _ _
    _ ≤ 2 * M := by linarith

section Main

variable {d : ℕ} {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {β : ℝ} (hβ : 0 ≤ β)
  {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ)
include hd hs0 hs hβ hρ

theorem sed_B7_lln_proof (M : ℝ) (m : ℕ) :
    ∃ C : ℝ, ∀ u : Torus d → ℝ, Measurable u → (∀ x, |u x| ≤ M) → ∀ N : ℕ, 1 ≤ N →
      ∫ X, (pair (empirical X) u - pair (withDensityReal ρ) u) ^ (2 * m) ∂(sed_Q d s N β ρ) ≤
        C / (N : ℝ) ^ m := by
  haveI hP : IsProbabilityMeasure (withDensityReal ρ) := HRS.MC.SEdge.B3.b3_prob hρ
  obtain ⟨C2, hC2, T2⟩ := HRS.MC.SEdge.B4a.sed_B4a_transfer_proof hd hs0 hs hβ hρ (r := 2)
    (by norm_num)
  obtain ⟨C', hC'⟩ := HRS.MC.SEdge.B4c.sed_B4c_iid_moment_proof (withDensityReal ρ) M (2 * m)
  refine ⟨C2 * Real.sqrt (max C' 0), fun u hum hb N hN => ?_⟩
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hNm : (0 : ℝ) < (N : ℝ) ^ m := by positivity
  set Z : Config d N → ℝ := fun X => pair (empirical X) u - pair (withDensityReal ρ) u with hZ
  have hZm : Measurable Z := by
    have : Z = fun X => (∑ i, u (X i)) / N - pair (withDensityReal ρ) u := by
      funext X
      simp only [hZ]
      rw [HRS.MC.SEdge.B4c.b4c_pair_empirical X hum]
    rw [this]
    exact ((Finset.measurable_sum _ fun i _ => hum.comp (measurable_pi_apply i)).div_const _).sub_const _
  have hZb : ∀ X, |Z X| ≤ 2 * M := fun X => b7_bound hN (withDensityReal ρ) hum hb X
  have hnn : ∀ X, 0 ≤ Z X ^ (2 * m) := fun X => Even.pow_nonneg (even_two_mul m) _
  set P : Measure (Config d N) := Measure.pi fun _ : Fin N => withDensityReal ρ with hPdef
  have hint : Integrable (fun X => Z X ^ (2 * (2 * m))) P := by
    refine Integrable.of_bound (hZm.pow_const _).aestronglyMeasurable ((2 * M) ^ (2 * (2 * m)))
      (Filter.Eventually.of_forall fun X => ?_)
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hZb X) _
  have hf : Measurable (fun X => ENNReal.ofReal (Z X ^ (2 * m))) :=
    (hZm.pow_const _).ennreal_ofReal
  have h1 := T2 N hN _ hf
  have h2 : ∫⁻ X, (ENNReal.ofReal (Z X ^ (2 * m))) ^ (2 : ℝ) ∂P =
      ∫⁻ X, ENNReal.ofReal (Z X ^ (2 * (2 * m))) ∂P := by
    refine lintegral_congr fun X => ?_
    rw [ENNReal.ofReal_rpow_of_nonneg (hnn X) (by norm_num), Real.rpow_two, ← pow_mul,
      mul_comm (2 * m) 2]
  rw [h2, ← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun X => Even.pow_nonneg (even_two_mul _) _)] at h1
  have hC'' := hC' u hum hb N hN
  have h3 : ∫⁻ X, ENNReal.ofReal (Z X ^ (2 * m)) ∂(sed_Q d s N β ρ) ≤
      ENNReal.ofReal (C2 * Real.sqrt (max C' 0) / (N : ℝ) ^ m) := by
    refine h1.trans ?_
    have hle : ∫ X, Z X ^ (2 * (2 * m)) ∂P ≤ max C' 0 / (N : ℝ) ^ (2 * m) :=
      hC''.trans (by gcongr; exact le_max_left _ _)
    have hsq : (max C' 0 / (N : ℝ) ^ (2 * m)) ^ (1 / (2 : ℝ)) =
        Real.sqrt (max C' 0) / (N : ℝ) ^ m := by
      rw [← Real.sqrt_eq_rpow, Real.sqrt_div (le_max_right _ _),
        show (N : ℝ) ^ (2 * m) = ((N : ℝ) ^ m) ^ 2 by rw [mul_comm, pow_mul],
        Real.sqrt_sq hNm.le]
    calc ENNReal.ofReal C2 * (ENNReal.ofReal (∫ X, Z X ^ (2 * (2 * m)) ∂P)) ^ (1 / (2 : ℝ))
        ≤ ENNReal.ofReal C2 * (ENNReal.ofReal (max C' 0 / (N : ℝ) ^ (2 * m))) ^ (1 / (2 : ℝ)) := by
          gcongr
      _ = ENNReal.ofReal (C2 * Real.sqrt (max C' 0) / (N : ℝ) ^ m) := by
          rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
            ← ENNReal.ofReal_mul hC2]
          congr 1
          rw [hsq]
          ring
  have h4 : ∫ X, Z X ^ (2 * m) ∂(sed_Q d s N β ρ) =
      (∫⁻ X, ENNReal.ofReal (Z X ^ (2 * m)) ∂(sed_Q d s N β ρ)).toReal :=
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hnn)
      (hZm.pow_const _).aestronglyMeasurable
  show ∫ X, Z X ^ (2 * m) ∂(sed_Q d s N β ρ) ≤ _
  rw [h4]
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) h3

end Main


end HRS.MC.SEdge.B7
