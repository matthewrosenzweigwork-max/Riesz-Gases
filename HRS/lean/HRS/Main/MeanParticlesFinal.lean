import HRS.Main.MeanParticlesFinalA
import HRS.Main.MeanParticlesFinalC
import HRS.Sections.Sec5

/-!
# Corollary 5.17 (`mean_particles`): proof

(packet `mpfinal`.)  The frozen statement `HRS.mean_particles` is proved here as
`mean_particles_proof` (relocation pattern).  Parts (a), (b) from `mpfin_ab_core`
(`MeanParticlesFinalA`), part (c) from `mpfin_c_core` (`MeanParticlesFinalC`); the prepared data
come from `mpp_preparedData`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace HRS

variable {d : ℕ}

theorem mean_particles_proof (hd : 2 ≤ d) {s β : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (hs : s < 2 * (d : ℝ) / 3) (hβ : 0 < β) (k : Lattice d) (hk : k ≠ 0)
    (hkβ : β * rieszCoeff d s k ≤ 1 / 4) (ε A : ℝ) (hε : 0 < ε) (ρ : ℝ → Torus d → ℝ) (C : ℝ)
    (Cj : ℕ → ℝ) (hρ : IsMeanTransient d s β hs0 hsd hβ k ε A ρ C Cj) (β₀ : ℝ) (hβ₀ : 0 ≤ β₀)
    (S : ParticleSeq d)
    (hS : ∀ T' : ℝ, 0 ≤ T' → S.IsSolutionOn (PDE.mfData d s hs0 hsd (fun _ => 0) β hβ) T')
    (hSF : ∀ n, ∃ (ℱ : MeasureTheory.Filtration ℝ (S.mΩ n))
      (W' : ℝ≥0 → S.Ω n → (Fin (n + 2) × Fin d) → ℝ),
      IsFilteredSolution (S.P n) ℱ W' (S.W n) (S.X n))
    (hinit : ∀ n, (S.P n).map (S.X₀ n) =
      modulatedGibbs (periodicRiesz d s) (n + 2) β₀ (withDensityReal (ρ 0)))
    (T : ℝ) (hT : 0 ≤ T) (m : ℝ) (hm : (d : ℝ) + 2 < m) (u : ℕ → ℝ) (hu0 : ∀ n, 0 ≤ u n)
    (hu : Tendsto u atTop atTop)
    (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Z : ℝ → Ω' → NegSobolev d m)
    (hZ : IsStationaryGaussianField P' s β hs0 hsd hβ (fun _ => 0) (fun _ => 1) m Z) :
    (∀ τ : ℝ,
      Tendsto (fun n : ℕ => u n - (2 * PDE.transientRate d s β k)⁻¹ * Real.log (n + 2 : ℕ)) atTop
        (𝓝 τ) →
      MeasureTheory.TendstoInDistribution
        (fun n ω => flucPath m T (Real.sqrt ((n + 2 : ℕ) : ℝ))
          (fun t ω' => S.X n ((u n).toNNReal + t) ω') (fun _ _ => (1 : ℝ)) ω) atTop
        (toPath m T (fun t ω' => Z t ω' +
          (A * Real.exp (-PDE.transientRate d s β k * (τ + t))) •
            NegSobolev.ofFun m (PDE.cosTest k)))
        S.P P') ∧
    (Tendsto (fun n : ℕ => u n - (2 * PDE.transientRate d s β k)⁻¹ * Real.log (n + 2 : ℕ)) atTop
        atTop →
      MeasureTheory.TendstoInDistribution
        (fun n ω => flucPath m T (Real.sqrt ((n + 2 : ℕ) : ℝ))
          (fun t ω' => S.X n ((u n).toNNReal + t) ω') (fun _ _ => (1 : ℝ)) ω) atTop
        (toPath m T Z) S.P P') ∧
    (Tendsto (fun n : ℕ => u n - (2 * PDE.transientRate d s β k)⁻¹ * Real.log (n + 2 : ℕ)) atTop
        atBot →
      ∀ M : ℝ, Tendsto (fun n : ℕ => S.P n {ω | linCoord (volume : Measure (Torus d))
          (PDE.cosTest k) (S.X n (u n).toNNReal ω) ≤ M}) atTop (𝓝 0)) := by
  obtain ⟨S0, hSs, hSβ, hSV, hSρ0, hSρ⟩ := mpp_preparedData hd hs0 hsd hβ k hk ε A ρ C Cj hρ
  have hρ0 : ρ 0 = fun x => 1 + ε * PDE.cosTest k x := hρ.init
  have hm2 : (d : ℝ) < 2 * m := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  refine ⟨?_, ?_, ?_⟩
  · intro τ hτ
    exact Main.mpfin_ab_core hd hs0 hsd hs hβ k ε ρ hρ0 β₀ hβ₀ S hS hSF hinit S0 hSs hSβ hSV hSρ0
      T hT m hm u hu0 hu P' Z hZ (Main.mp_dInfFun m A (PDE.transientRate d s β k) τ k)
      (Main.mp_dInfFun_cont m A (PDE.transientRate d s β k) τ k)
      (Main.mp_det_shift_critical hd hs0 hsd hβ k hk hkβ ε A hε ρ C Cj hρ S0 hSρ hm2 u hu0 hu τ hτ)
  · intro hlate
    have hDp := Main.mp_det_shift_late hd hs0 hsd hβ k hk hkβ ε A hε ρ C Cj hρ S0 hSρ hm2
      (T := T + 1) u hu0 hu hlate
    have h := Main.mpfin_ab_core hd hs0 hsd hs hβ k ε ρ hρ0 β₀ hβ₀ S hS hSF hinit S0 hSs hSβ hSV hSρ0
      T hT m hm u hu0 hu P' Z hZ (fun _ => 0) continuous_const (by
        simpa [Main.mpfin_shiftPath_zero] using hDp)
    simpa using h
  · intro hearly M
    exact Main.mpfin_c_core hd hs0 hsd hs hβ k hk ε ρ hρ0 (fun t ht => (hρ.smooth_pos t ht).1)
      β₀ hβ₀ S hS hSF hinit S0 hSs hSβ hSV hSρ0 hSρ m hm u hu0 hu
      (Main.mp_delta_early hd hs0 hsd hβ k hk hkβ ε A hε ρ C Cj hρ u hu hearly) P' Z hZ M

example := (@mean_particles_proof : type_of% @HRS.mean_particles)

end HRS
