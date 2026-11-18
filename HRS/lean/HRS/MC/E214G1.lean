import HRS.MC.E214FP4

/-!
# E214G1: the path-supremum estimate with a general coordinate weight and Hölder exponent

`p4_of_inputs_gen`: as `HRS.MC.E214F.p4_of_inputs`, but the increment input (I) is
`E (ξ_k(t) - ξ_k(s))² ≤ B |t-s|^γ w_k` for `|t-s| ≤ 1`, `γ > 0`, for an arbitrary summable weight `w_k ≥ ⟨k⟩^{-2r}`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

noncomputable section

namespace HRS.MC.E214G

variable {d : ℕ}

open HRS.MC.E214F

theorem p4_of_inputs_gen {r A c B γ : ℝ} (hr : (d : ℝ) < 2 * r) (wB : NonzeroLattice d → ℝ)
    (hwB0 : ∀ k, 0 ≤ wB k) (hwBs : Summable wB) (hwAB : ∀ k, Lattice.jp k.1 ^ (-(2 * r)) ≤ wB k)
    (hγ : 0 < γ) (hA : 0 < A) (hc : 0 < c) (hB : 0 < B)
    {T : ℝ} (hT : 0 < T) {p : ℝ} (hp : 2 ≤ p) :
    ∃ C κ : ℝ, 0 < C ∧ 0 < κ ∧ ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℝ → Ω → NegSobolev d r) (hXm : ∀ t, Measurable (X t))
    (hcont : ∀ᵐ ω ∂μ, ContinuousOn (fun t => X t ω) (Ici 0))
    (hD : ∀ t, 0 ≤ t → ∀ k : NonzeroLattice d,
      ∫ ω, NegSobolev.eval (X t ω) (Torus.realMode k) ^ 2 ∂μ ≤ A * Real.exp (-c * t))
    (hI : ∀ s t, 0 ≤ s → 0 ≤ t → |t - s| ≤ 1 → ∀ k : NonzeroLattice d,
      ∫ ω, (NegSobolev.coord (X t ω) k - NegSobolev.coord (X s ω) k) ^ 2 ∂μ ≤
        B * |t - s| ^ γ * wB k)
    (hG : ∀ t, 0 ≤ t → ∀ k, HasGaussianLaw (fun ω => NegSobolev.coord (X t ω) k) μ)
    (hG0 : ∀ t, 0 ≤ t → ∀ k, ∫ ω, NegSobolev.coord (X t ω) k ∂μ = 0)
    (hGi : ∀ s t, 0 ≤ s → 0 ≤ t → ∀ k, HasGaussianLaw
      (fun ω => NegSobolev.coord (X t ω) k - NegSobolev.coord (X s ω) k) μ)
    (hGi0 : ∀ s t, 0 ≤ s → 0 ≤ t → ∀ k,
      ∫ ω, (NegSobolev.coord (X t ω) k - NegSobolev.coord (X s ω) k) ∂μ = 0),
    ∀ a : ℝ, 0 ≤ a →
      ∫⁻ ω, (⨆ t ∈ Icc (0 : ℝ) T, ‖X (a + t) ω‖ₑ) ^ p ∂μ ≤ ENNReal.ofReal ((C * Real.exp (-κ * a)) ^ p) := by
  have hr0 : (d : ℝ) < 2 * r := hr
  set wA : NonzeroLattice d → ℝ := fun k => Lattice.jp k.1 ^ (-(2 * r)) with hwA
  have hwA0 : ∀ k, 0 ≤ wA k := fun k => Real.rpow_nonneg (Torus.jp_pos k.1).le _
  obtain ⟨C, κ, hC, hκ, hmain⟩ := sup_moment_of_coordinates (d := d) (m := r) hA (lt_max_of_lt_left hB) hc
    hγ wA wB hwA0 hwB0 (summable_jp_rpow r hr0) hwBs hT hp
  refine ⟨C, κ, hC, hκ, ?_⟩
  intro Ω _ μ _ X hXm hcont hD hI hG hG0 hGi hGi0 a ha
  have hdec : ∀ t, 0 ≤ t → ∀ k, ∫ ω, NegSobolev.coord (X t ω) k ^ 2 ∂μ ≤ A * Real.exp (-c * t) * wA k :=
    fun t ht k => coord_sq_of_eval_sq μ (X t) k (hD t ht k)
  have hinc : ∀ s t, 0 ≤ s → 0 ≤ t → ∀ k,
      ∫ ω, (NegSobolev.coord (X t ω) k - NegSobolev.coord (X s ω) k) ^ 2 ∂μ ≤
        (max B (4 * A)) * |t - s| ^ γ * wB k := by
    intro s t hs ht k
    by_cases h1 : |t - s| ≤ 1
    · refine (hI s t hs ht h1 k).trans ?_
      have := hwB0 k
      gcongr
      exact le_max_left _ _
    · push Not at h1
      have i1 := (hG t ht k).memLp_two.integrable_sq
      have i2 := (hG s hs k).memLp_two.integrable_sq
      calc ∫ ω, (NegSobolev.coord (X t ω) k - NegSobolev.coord (X s ω) k) ^ 2 ∂μ
          ≤ ∫ ω, (2 * NegSobolev.coord (X t ω) k ^ 2 + 2 * NegSobolev.coord (X s ω) k ^ 2) ∂μ := by
            refine integral_mono_of_nonneg (ae_of_all _ fun ω => sq_nonneg _)
              ((i1.const_mul 2).add (i2.const_mul 2)) (ae_of_all _ fun ω => ?_)
            nlinarith [sq_nonneg (NegSobolev.coord (X t ω) k + NegSobolev.coord (X s ω) k)]
        _ = 2 * ∫ ω, NegSobolev.coord (X t ω) k ^ 2 ∂μ + 2 * ∫ ω, NegSobolev.coord (X s ω) k ^ 2 ∂μ := by
            rw [integral_add (i1.const_mul 2) (i2.const_mul 2), integral_const_mul, integral_const_mul]
        _ ≤ 4 * A * wB k * 1 := by
            have e1 := hdec t ht k
            have e2 := hdec s hs k
            have x1 : Real.exp (-c * t) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
            have x2 : Real.exp (-c * s) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
            have y1 : A * Real.exp (-c * t) * wA k ≤ A * wB k := by
              calc A * Real.exp (-c * t) * wA k ≤ A * 1 * wB k := by
                    gcongr; exact hwA0 k; exact hwAB k
                _ = A * wB k := by ring
            have y2 : A * Real.exp (-c * s) * wA k ≤ A * wB k := by
              calc A * Real.exp (-c * s) * wA k ≤ A * 1 * wB k := by
                    gcongr; exact hwA0 k; exact hwAB k
                _ = A * wB k := by ring
            linarith
        _ ≤ max B (4 * A) * |t - s| ^ γ * wB k := by
            have := hwB0 k
            have hm : 4 * A ≤ max B (4 * A) := le_max_right _ _
            have h1' : 1 ≤ |t - s| ^ γ := Real.one_le_rpow h1.le hγ.le
            have hM0 : 0 ≤ max B (4 * A) := by positivity
            calc 4 * A * wB k * 1 ≤ max B (4 * A) * 1 * wB k := by
                  rw [mul_one, mul_one]; exact mul_le_mul_of_nonneg_right hm this
              _ ≤ max B (4 * A) * |t - s| ^ γ * wB k := by gcongr
  exact hmain μ X hXm hcont hdec hinc hG hG0 hGi hGi0 a ha

end HRS.MC.E214G

end
