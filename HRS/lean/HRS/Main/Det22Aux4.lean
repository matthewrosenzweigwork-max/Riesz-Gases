import HRS.Main.Det22Aux3

/-!
# Packet DET22, part 4: the assembly at a general level `m` (`m = γ` gradient, `m = γ+2` matrix)
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.Det22

variable {d : ℕ}

theorem det22_assemble (S : GeneralSetup d) (M : Matrix (Fin d) (Fin d) ℝ) (hMF : S.MFHypM M)
    (N : ℕ) (hN : 2 ≤ N) (m : ℝ) (hm : (S.γ : ℝ) ≤ m) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (x₀ : Config d N)
    (W : ℝ≥0 → Ω → (Fin N → Euc d)) (hW : IsVectorBrownian P W) (X : ℝ≥0 → Ω → Config d N)
    (hX : IsStrongSolution P (S.dynM M N) S.T (fun _ => x₀) W X)
    (hF : ∃ (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
        (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ), IsFilteredSolution P ℱ W' W X)
    (hE : S.EnergyMomentFinite P N X) (hβ : S.invβ N = 0)
    (VE : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m)
    (hdual : HRS.GF.IsDualOn (S.dynM M N) (S.ρ N) m S.T VE)
    (hself : ∀ t ∈ Set.Icc (0 : ℝ) S.T, VE t t = 1)
    (hcont : ∀ y, ContinuousOn (fun p : ℝ × ℝ => VE p.1 p.2 y)
      {p | 0 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ S.T})
    (y₀ : NegSobolev d m) (F : NegSobolev d (S.γ : ℝ)) (C : ℝ) (hC : 0 < C)
    (hT : ∀ Y : ℝ → Ω → NegSobolev d m,
      IsLinearFluctuationSolution P (S.dynM M N) (S.ρ N) m (qScale N (S.κ N) (S.invβ N)) S.T
        (fun _ => Ascale N (S.κ N) (S.invβ N) • y₀) Y →
      wassersteinE 1 (law P (flucPath m S.T (sigmaScale N (S.κ N) (S.invβ N)) X (S.ρ N)))
        (law P (toPath m S.T Y)) ≤
      ENNReal.ofReal (C * (Ascale N (S.κ N) (S.invβ N) *
          S.initialError P N 1 (fun _ => x₀) (fun _ => F) +
        sigmaScale N (S.κ N) (S.invβ N) * S.energyMoment P N X +
        Real.sqrt (qScale N (S.κ N) (S.invβ N)) * (S.energyMoment P N X ^ ((1 : ℝ) / 4) +
          (N : ℝ) ^ (-(1 : ℝ) / d))))) :
    ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) S.T,
      ‖S.κ N • NegSobolev.ofMeasureDiff m (empirical (X (Real.toNNReal t) ω))
          (withDensityReal (S.ρ N t)) - HRS.Main.transportField (S.dynM M N) (S.ρ N) t m y₀‖ ≤
        C * (‖S.κ N • NegSobolev.ofMeasureDiff (S.γ : ℝ) (empirical x₀)
            (withDensityReal (S.ρ N 0)) - F‖ + S.κ N * S.energyMoment P N X) := by
  have hσ : sigmaScale N (S.κ N) (S.invβ N) = S.κ N := by simp [sigmaScale, hβ]
  have hA : Ascale N (S.κ N) (S.invβ N) = 1 := by simp [Ascale, hβ]
  have hq : qScale N (S.κ N) (S.invβ N) = 0 := by simp [qScale, hβ]
  have hε : S.initialError P N 1 (fun _ => x₀) (fun _ => F) =
      ‖S.κ N • NegSobolev.ofMeasureDiff (S.γ : ℝ) (empirical x₀) (withDensityReal (S.ρ N 0)) - F‖ := by
    simp [GeneralSetup.initialError]
  have hE0 := HRS.GF.gff_energyMoment_nonneg S M hMF N hN P (fun _ => x₀) W X hX hF hE
  have hκ := S.hκ N
  -- determinism
  have hV2 : Torus.IsCk 2 (S.dynM M N).V := by
    have h1 : (2 : WithTop ℕ∞) ≤ ((S.γ + 2 * d + 12 : ℕ) : WithTop ℕ∞) := by
      exact_mod_cast (show 2 ≤ S.γ + 2 * d + 12 by omega)
    exact ContDiff.of_le S.V_reg h1
  have hbL : IsLocLipschitzDrift (liftedFree d N) (fun _ Z => liftedDrift (S.dynM M N) Z) :=
    liftedDrift_locLipschitz (S.dynM M N)
      (kernelLocal_of_two_le S.hd (S.dynM M N).hs0 (S.dynM M N).hsd).smoothOffZero hV2
  have hdet := det22_deterministic P (S.dynM M N) hbL hβ S.T x₀ W hW X hX
  -- the deterministic linear solution
  have hY := det22_linearSol (S.dynM M N) (S.ρ N) m S.T P VE hdual hself hcont S.hT.le y₀
    (fun _ => Ascale N (S.κ N) (S.invβ N) • y₀) (fun _ => by rw [hA, one_smul]) 
  have hY' : IsLinearFluctuationSolution P (S.dynM M N) (S.ρ N) m (qScale N (S.κ N) (S.invβ N)) S.T
      (fun _ => Ascale N (S.κ N) (S.invβ N) • y₀) (fun t _ => VE t 0 y₀) := by
    rw [hq]; exact hY
  have hW1 := hT _ hY'
  rw [hσ, hA, hq, hε] at hW1
  simp only [Real.sqrt_zero, zero_mul, add_zero, one_mul] at hW1
  have hcc := (HRS.GF.gf_fluc_continuous_proof S M hMF N m hm P (fun _ => x₀) W X hX (S.κ N)).1
  have hyc : ContinuousOn (fun t => VE t 0 y₀) (Set.Icc 0 S.T) := by
    have := (hcont y₀).comp (f := fun t : ℝ => ((t, 0) : ℝ × ℝ)) (by fun_prop)
      (s := Set.Icc 0 S.T) (fun t ht => ⟨le_rfl, ht.1, ht.2⟩)
    exact this
  have hB : 0 ≤ C * (‖S.κ N • NegSobolev.ofMeasureDiff (S.γ : ℝ) (empirical x₀)
            (withDensityReal (S.ρ N 0)) - F‖ + S.κ N * S.energyMoment P N X) := by
    have := norm_nonneg (S.κ N • NegSobolev.ofMeasureDiff (S.γ : ℝ) (empirical x₀)
            (withDensityReal (S.ρ N 0)) - F)
    positivity
  have key := det22_path_bound P m S.T (S.κ N) X (S.ρ N) (fun t => VE t 0 y₀) _ hB hdet hcc hyc hW1
  filter_upwards [key] with ω hω t ht
  have := hω t ht
  rwa [← det22_VE_eq_transport (S.dynM M N) (S.ρ N) m S.T VE hdual ht.1 ht.2 y₀]

end HRS.Det22
