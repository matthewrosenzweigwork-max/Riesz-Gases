import HRS.Main.Rel513RieszC

/-!
# HRS.Main.Rel513RieszD -- packet rel513, part 4: the time-integral bound (Prop 5.13, part (b))

`stationary_remainder_time_integral_proof` is `relative_remainder` with `A^r ≡ R_{N,stat}(φ)`, `a ≡ 1`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.Main

variable {d : ℕ}

theorem stationary_remainder_time_integral_proof (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (β : ℝ) (hβ : 0 < β) (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (ρβ : Torus d → ℝ)
    (hρ : SmoothPosDensity ρβ) (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ)
    (N : ℕ) (hN : 2 ≤ N) (φ : Torus d → ℝ) (hφ : Torus.IsSmooth φ) (ε : ℝ) (hε : 0 ≤ ε)
    (hA : eLpNorm (stationaryRemainder d s β V ρβ N φ) 2
      (canonicalGibbs (periodicRiesz d s) V N β) ≤ ENNReal.ofReal ε)
    (κ : ℝ → ProbabilityTheory.Kernel (Config d N) (Config d N))
    [∀ r, ProbabilityTheory.IsMarkovKernel (κ r)]
    (hinv : ∀ r, 0 ≤ r →
      (canonicalGibbs (periodicRiesz d s) V N β).bind (κ r) = canonicalGibbs (periodicRiesz d s) V N β)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Xp : ℝ → Ω → Config d N) (hXp : Measurable fun q : ℝ × Ω => Xp q.1 q.2)
    (ν : Measure (Config d N)) (hν : ν ≪ canonicalGibbs (periodicRiesz d s) V N β) (R : ℝ)
    (hR : eLpNorm (ν.rnDeriv (canonicalGibbs (periodicRiesz d s) V N β)) 2
      (canonicalGibbs (periodicRiesz d s) V N β) ≤ ENNReal.ofReal R)
    (hlaw : ∀ r, 0 ≤ r → P.map (Xp r) = ν.bind (κ r)) (t : ℝ) (ht : 0 ≤ t) :
    ∫⁻ ω, ENNReal.ofReal |∫ r in (0 : ℝ)..t,
        (stationaryRemainder d s β V ρβ N φ (Xp r ω)
          - ∫ ω', stationaryRemainder d s β V ρβ N φ (Xp r ω') ∂P)| ∂P ≤
      ENNReal.ofReal (2 * R * t * ε) := by
  have hN1 : 1 ≤ N := by omega
  have hZ := canonicalPartition_pos_riesz_proof hd hs0 hsd β hβ V hV hN1
  have := canonicalGibbs_isProbability_proof (periodicRiesz d s) V N β hZ
  have hmeas := stationaryRemainder_measurable_proof hd hs0 hsd β hβ V hV ρβ hρ hρβ N hN φ hφ
  have key := relative_remainder (canonicalGibbs (periodicRiesz d s) V N β) κ hinv P Xp hXp ν hν R hR hlaw
    (fun _ => stationaryRemainder d s β V ρβ N φ)
    (hmeas.comp measurable_snd) ε hε (fun _ => 1) (fun _ => zero_le_one) measurable_const t t ht
    (integrableOn_const (by simp) (by simp))
    (fun r _ => by simpa using hA)
    (by simp [ht])
  exact key

example := (@stationary_remainder_time_integral_proof :
  type_of% @stationary_remainder_time_integral)

end HRS.Main

end
