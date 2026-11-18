import HRS.MS.Fp81S21VersionGTime

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Classical MeasureTheory Filter Topology Set
open scoped ENNReal

namespace HRS.Fp81.S21

open HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6

/-- The packet-30 canonical weak-chart representatives selected for every
Gaussian realization, together with their full canonical time payload. -/
structure fp81s21_gaussian_V2_G_canonicalFamily
    (p : Parameters)
    (Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4))
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2))
    {δ : ℝ} (R : Trajectory p δ) (MUG : ℝ) (ε : ℕ → ℝ) where
  q : ∀ G : GaussianRealization R, ℝ → G.Ω → r26t6_Coeff
  payload : ∀ G : GaussianRealization R,
    fp81s21_gaussian_canonical_time_payload p Es E G.P
      (fun u ω f => OscDual.eval (G.Z u ω) f) MUG (q G)
      (fp81s21_gaussian_embedFamily p Es E (q G)) ε

/-- Physical Gaussian V2-G: packet 30's one selected canonical field and
all of its time classes are used for every horizon and start. Its time class
is the L² class of the V1-G continuous version, and the continuous version
retains the simultaneous physical chart identity. -/
theorem fp81s21_gaussian_V2_G_physical
    (p : Parameters)
    (Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4))
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2)) :
    ∃ ε : ℕ → ℝ, (∀ m, 0 ≤ ε m) ∧ Filter.Tendsto ε atTop (𝓝 0) ∧
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ R : Trajectory p δ,
        ∃ M2 M6 : ℝ, 0 ≤ M2 ∧ 0 ≤ M6 ∧
        ∃ MUG : ℝ, 0 ≤ MUG ∧
        ∃ canon : fp81s21_gaussian_V2_G_canonicalFamily p Es E R MUG ε,
        ∀ H : ℝ, (hH : 0 < H) →
          ∃ D : ℝ, 0 ≤ D ∧
          ∀ G : GaussianRealization R,
            ∃ qsG : ℝ → G.Ω → r26t6_Coeff,
              fp81s21_MomentRep Es G.P
                (fun u ω f => OscDual.eval (G.Z u ω) f) qsG M2 ∧
              fp81s21_Six G.P qsG M6 ∧
              fp81s21_MomentRep E G.P
                (fun u ω f => OscDual.eval (G.Z u ω) f)
                (fun u ω => fp81s21_gaussian_chartEmbed p Es E (qsG u ω)) M2 ∧
              fp81s21_Six G.P
                (fun u ω => fp81s21_gaussian_chartEmbed p Es E (qsG u ω)) M6 ∧
              ∀ a : ℝ, 0 ≤ a →
                ∃ XG : G.Ω → fp81s21_SmoothCH H,
                  Measurable XG ∧ MemLp XG 2 G.P ∧
                  (∀ t : Icc (0 : ℝ) H,
                    (fun ω => XG ω t) =ᵐ[G.P]
                      (fun ω => fp81s21_gaussian_chartEmbed p Es E
                        (qsG (a + t) ω))) ∧
                  ∃ B : G.Ω → ℝ, Measurable B ∧ (∀ ω, 0 ≤ B ω) ∧
                    Integrable (fun ω => B ω ^ 2) G.P ∧
                    (∫ ω, B ω ^ 2 ∂G.P) ≤ D ∧
                    (∀ᵐ ω ∂G.P, ∀ s t : Icc (0 : ℝ) H,
                      ‖XG ω t - XG ω s‖ ≤
                        B ω * |(t : ℝ) - s| ^ (1 / 8 : ℝ)) ∧
                  ∃ UG : G.Ω → fp81s21_SmoothUH H,
                    fp81s21_TimeL2Rep G.P
                      (fp81s21_gaussian_embedFamily p Es E (canon.q G))
                      MUG a H UG ∧
                    UG =ᵐ[G.P]
                      (fun ω => fp81s21_smoothPathToL2 H hH (XG ω)) ∧
                    ∀ᵐ ω ∂G.P, ∀ t : Icc (0 : ℝ) H, ∀ f, IsR2Test f →
                      fp81s21_chartAction E (XG ω t) f =
                        OscDual.eval (G.Z (a + t) ω) f := by
  let canonicalResult := Classical.choice
    (fp81s21_gaussian_canonical_TimeRep_tails p Es E)
  obtain ⟨δv, hδv, hδvhalf, hV1⟩ :=
    fp81s21_gaussian_physical_continuous_version p
  let δ₀ : ℝ := min δv canonicalResult.delta₀
  have hδ₀ : 0 < δ₀ := lt_min hδv canonicalResult.delta₀_positive
  have hδ₀half : δ₀ ≤ 1 / 2 :=
    (min_le_left _ _).trans hδvhalf
  refine ⟨canonicalResult.epsilon, canonicalResult.epsilon_nonneg,
    canonicalResult.epsilon_tendsto, δ₀, hδ₀, hδ₀half, ?_⟩
  intro δ hδ hδle R
  have hδvle : δ ≤ δv := hδle.trans (min_le_left _ _)
  have hδcanle : δ ≤ canonicalResult.delta₀ :=
    hδle.trans (min_le_right _ _)
  obtain ⟨M2, M6, hM2, hM6, hV1charts⟩ :=
    hV1 δ hδ hδvle R Es E
  obtain ⟨MUG, hMUG, hcanonicalG⟩ :=
    canonicalResult.realizations δ hδ hδcanle R
  let canon : fp81s21_gaussian_V2_G_canonicalFamily p Es E R MUG
      canonicalResult.epsilon :=
    ⟨fun G => Classical.choose (hcanonicalG G),
      fun G => Classical.choose_spec (hcanonicalG G)⟩
  refine ⟨M2, M6, hM2, hM6, MUG, hMUG, canon, ?_⟩
  intro H hH
  obtain ⟨D, hD, hV1forG⟩ := hV1charts H hH
  refine ⟨D, hD, ?_⟩
  intro G
  obtain ⟨qsG, hStrong, hSixStrong, hWeak, hSixWeak, hForA⟩ := hV1forG G
  refine ⟨qsG, hStrong, hSixStrong, hWeak, hSixWeak, ?_⟩
  intro a ha
  obtain ⟨XG, hXG, hXGmem, hsec, B, hBmeas, hBnonneg, hBint, hBbound,
      hHolder⟩ := hForA a ha
  obtain ⟨UG, hUG, hUGeq, hphysical⟩ :=
    fp81s21_gaussian_V2_G_selected p R Es E G a H ha hH MUG (canon.q G)
      canonicalResult.epsilon (canon.payload G) M2
      (fun u ω => fp81s21_gaussian_chartEmbed p Es E (qsG u ω))
      hWeak XG hXG hsec
  exact ⟨XG, hXG, hXGmem, hsec,
    B, hBmeas, hBnonneg, hBint, hBbound, hHolder,
    UG, hUG, hUGeq, hphysical⟩

#print axioms HRS.Fp81.S21.fp81s21_gaussian_V2_G_physical

end HRS.Fp81.S21

end
