import HRS.MC.S7FCHA1
import HRS.MC.S7FCHA2
import HRS.MC.S7FCH2G
import HRS.MC.S7FCH3G
import HRS.MC.S7FCH4I
import HRS.MC.S7FCW12G
import HRS.MC.S7FCW12F

/-!
# S7FCHA3: `W_q`-convergence of the pair for every admissible `B` (FC-H assembly, part 1)

Instantiates `S7FCHA_Wq_abstract` with `U_N = pairN`, `U' = pairLim`, the finite-rank pairs
`V_N^{(S,L)} = (ζ_N, ℬ_N^{S,K(·,L)})`, `V'^{(S,L)} = (η, ℬ^{S,K(·,L)})`, the index `j = (S, L)` being chosen from H2 and H3
(common `S ⊇ S₀`, common `L ≥ L₀`, kernel data from `S7FCHA_kernelData`) and the convergence of the middle term from H4.
The measurability inputs (so that the laws are honest) are E (`pairN`), E3, E4.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.SEdge HRS.MC.QRSpec HRS.MC.Sec7.FCPlan
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7FCH

variable {d : ℕ}

/-- `L²([0,T];E_r)` is second countable (`Lp.SecondCountableTopology`; `E_r` is separable). -/
instance S7FCHA_L2Path_sc (d : ℕ) (r T : ℝ) : SecondCountableTopology (L2Path d r T) := by
  haveI : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  haveI : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  exact Lp.SecondCountableTopology

/-- The norm of a difference of two pairs with the same first component. -/
theorem S7FCHA_norm_prod_sub {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] (a : E) (b b' : F) :
    ‖((a, b) : E × F) - (a, b')‖ = ‖b - b'‖ := by
  rw [Prod.norm_def]
  simp

/-- From an integrable moment bounded by `δ` to the `lintegral` bound used by the abstract assembly. -/
theorem S7FCHA_lint_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (f : Ω → ℝ) (hf : ∀ ω, 0 ≤ f ω)
    (hI : Integrable f P) {δ : ℝ} (hle : ∫ ω, f ω ∂P ≤ δ) :
    ∫⁻ ω, ENNReal.ofReal (f ω) ∂P ≤ ENNReal.ofReal δ := by
  rw [← ofReal_integral_eq_lintegral_ofReal hI (Eventually.of_forall hf)]
  exact ENNReal.ofReal_le_ofReal hle

/-- **Part 1 of the assembly**: `W_q(Law pairN, Law pairLim) → 0` for every admissible `B`. -/
theorem S7FCHA_Wq (R : Regime d) (r : ℝ) (hr : r = 2 * (d : ℝ) + 6) (T : ℝ) (hT : 0 < T)
    {Ω : ℕ → Type} [∀ N, MeasurableSpace (Ω N)] (P : ∀ N, Measure (Ω N))
    [∀ N, IsProbabilityMeasure (P N)] (X₀ : ∀ N, Ω N → Config d N)
    (W : ∀ N, ℝ≥0 → Ω N → (Fin N → Euc d)) (X : ∀ N, ℝ≥0 → Ω N → Config d N)
    (hreal : ∀ N, 1 ≤ N → PreparedRealization R.D (P N)
      (modulatedGibbs (periodicRiesz d R.D.s) N R.β₀ (withDensityReal R.ρ₀)) (X₀ N) (W N) (X N))
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (η : ℝ → Ω' → NegSobolev d r)
    (hη : IsGaussianLimitField R.D R.ρ (withDensityReal R.ρ₀) R.β₀ r P' η)
    (B : ℝ → Ω' → NegSobolev d r) (hBm : Measurable (Function.uncurry B))
    (hBL2 : ∀ᵐ ω ∂P', MemLp (fun t => B t ω) 2 (volume.restrict (Set.Icc (0 : ℝ) T)))
    (hBW : ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      IsWickQuadraticField R.D.s P' (fun ω => η t ω) (withDensityReal (R.ρ t)) (B t))
    (q : ℝ) (hq : 1 ≤ q) :
    Tendsto (fun N : ℕ => wassersteinE q (law (P N) (pairN r T 0 R.D.s R.ρ (P N) (X N)))
      (law P' (pairLim r T 0 η B))) atTop (𝓝 0) := by
  obtain ⟨ε₂, c, K, hK⟩ := S7FCHA_kernelData R
  have hE4 := fun (S : Finset (NonzeroLattice d)) (K' : NonzeroLattice d → FRKernel d) =>
    HRS.MC.Sec7.S7FCW12.s7_FC_E4_limit_measurable_proof R r hr T hT P' η hη B hBm hBL2 S K'
  refine S7FCHA_Wq_abstract (J := Finset (NonzeroLattice d) × ℕ) P P'
    (fun N => pairN r T 0 R.D.s R.ρ (P N) (X N)) (pairLim r T 0 η B)
    (fun j N ω => (zetaWin r T 0 (P N) (X N) ω, toL2 r T (fun t =>
      fcPartAt r j.1 (fun k => K k j.2) (fun t => withDensityReal (R.ρ t)) (P N) (X N) (0 + t) ω)))
    (fun j ω => (procWin r T 0 η ω, toL2 r T (fun t => fcGaussAt r j.1 (fun k => K k j.2) P' η (0 + t) ω)))
    q hq ?_ ?_ ?_ ?_ ?_
  · intro N hN
    exact HRS.MC.Sec7.S7FCW12.s7_FC_E_pair_measurable_proof R r hr T hT (P N) (by omega) (X₀ N) (W N) (X N)
      (hreal N (by omega))
  · exact (hE4 ∅ (fun k => K k 0)).1
  · intro j N hN
    exact HRS.MC.Sec7.S7FCW12.s7_FC_E3_finite_rank_measurable_proof R r hr T hT (P N) (by omega) (X₀ N) (W N) (X N)
      (hreal N (by omega)) j.1 (fun k => K k j.2)
  · intro j
    exact (hE4 j.1 (fun k => K k j.2)).2
  · intro δ hδ
    obtain ⟨S₂, h2⟩ := HRS.MC.Sec7.S7FCH2.s7_FC_H2_particle_approx_proof R r hr T hT P X₀ W X hreal ε₂ c K hK q hq δ hδ
    obtain ⟨S₃, h3⟩ := HRS.MC.Sec7.S7FCH3.s7_FC_H3_gauss_approx_proof R r hr T hT P' η hη B hBm hBL2 hBW
      ε₂ c K hK q hq δ hδ
    obtain ⟨L₂, hL₂⟩ := h2 (S₂ ∪ S₃) Finset.subset_union_left
    obtain ⟨L₃, hL₃⟩ := h3 (S₂ ∪ S₃) Finset.subset_union_right
    refine ⟨(S₂ ∪ S₃, max L₂ L₃), ?_, ?_, ?_⟩
    · intro N hN
      obtain ⟨hI, hle⟩ := hL₂ (max L₂ L₃) (le_max_left _ _) N hN
      have e : ∀ ω, ‖pairN r T 0 R.D.s R.ρ (P N) (X N) ω - (zetaWin r T 0 (P N) (X N) ω, toL2 r T (fun t =>
          fcPartAt r (S₂ ∪ S₃) (fun k => K k (max L₂ L₃)) (fun t => withDensityReal (R.ρ t)) (P N) (X N)
            (0 + t) ω))‖ = ‖(pairN r T 0 R.D.s R.ρ (P N) (X N) ω).2 - toL2 r T (fun t =>
          fcPartAt r (S₂ ∪ S₃) (fun k => K k (max L₂ L₃)) (fun t => withDensityReal (R.ρ t)) (P N) (X N)
            (0 + t) ω)‖ := fun ω => S7FCHA_norm_prod_sub _ _ _
      simp only [e]
      exact S7FCHA_lint_le (P N) _ (fun ω => Real.rpow_nonneg (norm_nonneg _) q) hI hle
    · obtain ⟨hI, hle⟩ := hL₃ (max L₂ L₃) (le_max_right _ _)
      have e : ∀ ω, ‖pairLim r T 0 η B ω - (procWin r T 0 η ω, toL2 r T (fun t =>
          fcGaussAt r (S₂ ∪ S₃) (fun k => K k (max L₂ L₃)) P' η (0 + t) ω))‖ =
          ‖(pairLim r T 0 η B ω).2 - toL2 r T (fun t =>
          fcGaussAt r (S₂ ∪ S₃) (fun k => K k (max L₂ L₃)) P' η (0 + t) ω)‖ := fun ω =>
        S7FCHA_norm_prod_sub _ _ _
      simp only [e]
      exact S7FCHA_lint_le P' _ (fun ω => Real.rpow_nonneg (norm_nonneg _) q) hI hle
    · exact HRS.MC.Sec7.S7FCH4.s7_FC_H4_finite_rank_W_proof R r hr T hT P X₀ W X hreal P' η hη (S₂ ∪ S₃)
        (fun k => K k (max L₂ L₃)) q hq

end HRS.MC.Sec7.S7FCH

end
