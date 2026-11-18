import HRS.MC.S7UCDefs
import HRS.MC.S7UCAWq
import HRS.MC.S7UCAE
import HRS.MC.S7UCPB
import HRS.MC.S7UCQA
import HRS.MC.S7UCW
import HRS.MC.S7FCHA1
import HRS.MC.S7FCF5E

/-!
# Packet ucZ (part 1): `W_q` convergence of the pair, uniformly in the window, for every `UCField` `B`

Proof of `s7_UC_Wq_every_B` (`S7UCPlan.lean`), a port of `S7FCHA_Wq` (`S7FCHA3.lean`) with the supremum over the
window start `a ≥ 0` carried along: `s7_UC_Wq_abstract_proof` (ABS) with the index `j = (S, L)` chosen from H2 and H3
(common `S ⊇ S₀`, `L ≥ L₀`, kernel data `S7FCHA_kernelData`), measurability from G1/E3/E4, the middle term from H4.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7UCZ

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.SEdge HRS.MC.QRSpec HRS.MC.Sec7.FCPlan HRS.MC.Sec7.S7FCH4
open HRS.MC.Sec7.UCPlan

variable {d : ℕ}

/-- `L²([0,T];E_r)` is second countable (`Lp.SecondCountableTopology`; `E_r` is separable). -/
instance S7UCZ_L2Path_sc (d : ℕ) (r T : ℝ) : SecondCountableTopology (L2Path d r T) := by
  haveI : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  haveI : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  exact Lp.SecondCountableTopology

/-- The norm of a difference of two pairs with the same first component. -/
theorem S7UCZ_norm_prod_sub {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] (a : E) (b b' : F) :
    ‖((a, b) : E × F) - (a, b')‖ = ‖b - b'‖ := by
  rw [Prod.norm_def]
  simp

/-- From an integrable moment bounded by `δ` to the `lintegral` bound used by the abstract assembly. -/
theorem S7UCZ_lint_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (f : Ω → ℝ) (hf : ∀ ω, 0 ≤ f ω)
    (hI : Integrable f P) {δ : ℝ} (hle : ∫ ω, f ω ∂P ≤ δ) :
    ∫⁻ ω, ENNReal.ofReal (f ω) ∂P ≤ ENNReal.ofReal δ := by
  rw [← ofReal_integral_eq_lintegral_ofReal hI (Eventually.of_forall hf)]
  exact ENNReal.ofReal_le_ofReal hle

theorem s7_UC_Wq_every_B_proof (R : Regime d) (r : ℝ) (hr : r = 2 * (d : ℝ) + 6) (T : ℝ) (hT : 0 < T)
    {Ω : ℕ → Type} [∀ N, MeasurableSpace (Ω N)] (P : ∀ N, Measure (Ω N))
    [∀ N, IsProbabilityMeasure (P N)] (X₀ : ∀ N, Ω N → Config d N)
    (W : ∀ N, ℝ≥0 → Ω N → (Fin N → Euc d)) (X : ∀ N, ℝ≥0 → Ω N → Config d N)
    (hreal : ∀ N, 1 ≤ N → PreparedRealization R.D (P N)
      (modulatedGibbs (periodicRiesz d R.D.s) N R.β₀ (withDensityReal R.ρ₀)) (X₀ N) (W N) (X N))
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (η : ℝ → Ω' → NegSobolev d r)
    (hη : IsGaussianLimitField R.D R.ρ (withDensityReal R.ρ₀) R.β₀ r P' η)
    (B : ℝ → Ω' → NegSobolev d r) (hB : UCField R r P' η B) (p : ℝ) (hp : 1 ≤ p) :
    Tendsto (fun N : ℕ => ⨆ a : {a : ℝ // 0 ≤ a},
        wassersteinE p (law (P N) (pairN r T a.1 R.D.s R.ρ (P N) (X N)))
          (law P' (pairLim r T a.1 η B))) atTop (𝓝 0) := by
  obtain ⟨ε₂, c, K, hK⟩ := HRS.MC.Sec7.S7FCH.S7FCHA_kernelData R
  have hE4 := fun (a : {a : ℝ // 0 ≤ a}) (S : Finset (NonzeroLattice d)) (K' : NonzeroLattice d → FRKernel d) =>
    HRS.MC.Sec7.S7UCA.s7_UC_E4_limit_measurable_proof R r hr T hT P' η hη B hB.1 a.1 a.2 S K'
  refine HRS.MC.Sec7.S7UCA.s7_UC_Wq_abstract_proof (B := PathSpace d r T × L2Path d r T) (A := {a : ℝ // 0 ≤ a}) (J := Finset (NonzeroLattice d) × ℕ) P P'
    (fun a N => pairN r T a.1 R.D.s R.ρ (P N) (X N)) (fun a => pairLim r T a.1 η B)
    (fun j a N ω => (zetaWin r T a.1 (P N) (X N) ω, toL2 r T (fun t =>
      fcPartAt r j.1 (fun k => K k j.2) (fun t => withDensityReal (R.ρ t)) (P N) (X N) (a.1 + t) ω)))
    (fun j a ω => (procWin r T a.1 η ω, toL2 r T (fun t => fcGaussAt r j.1 (fun k => K k j.2) P' η (a.1 + t) ω)))
    p hp ?_ ?_ ?_ ?_ ?_
  · intro a N hN
    exact HRS.MC.Sec7.S7FCF5E.fcf5_G1_pair_aemeasurable_proof R r hr T hT (P N) (by omega) (X₀ N) (W N) (X N)
      (hreal N (by omega)) a.1 a.2
  · intro a
    exact (hE4 a ∅ (fun k => K k 0)).1
  · intro j a N hN
    exact HRS.MC.Sec7.S7UCA.s7_UC_E3_finite_rank_measurable_proof R r hr T hT (P N) (by omega) (X₀ N) (W N) (X N)
      (hreal N (by omega)) a.1 a.2 j.1 (fun k => K k j.2)
  · intro j a
    exact (hE4 a j.1 (fun k => K k j.2)).2
  · intro δ hδ
    obtain ⟨S₂, h2⟩ := HRS.MC.Sec7.S7UCP.s7_UC_H2_particle_approx_unif_proof R r hr T hT P X₀ W X hreal
      ε₂ c K hK p hp δ hδ
    obtain ⟨S₃, h3⟩ := HRS.MC.Sec7.S7UCQ.s7_UC_H3_gauss_approx_unif_proof R r hr T hT P' η hη B hB
      ε₂ c K hK p hp δ hδ
    obtain ⟨L₂, hL₂⟩ := h2 (S₂ ∪ S₃) Finset.subset_union_left
    obtain ⟨L₃, hL₃⟩ := h3 (S₂ ∪ S₃) Finset.subset_union_right
    refine ⟨(S₂ ∪ S₃, max L₂ L₃), ?_, ?_, ?_⟩
    · intro a N hN
      obtain ⟨hI, hle⟩ := hL₂ (max L₂ L₃) (le_max_left _ _) N hN a.1 a.2
      have e : ∀ ω, ‖pairN r T a.1 R.D.s R.ρ (P N) (X N) ω - (zetaWin r T a.1 (P N) (X N) ω, toL2 r T (fun t =>
          fcPartAt r (S₂ ∪ S₃) (fun k => K k (max L₂ L₃)) (fun t => withDensityReal (R.ρ t)) (P N) (X N)
            (a.1 + t) ω))‖ = ‖(pairN r T a.1 R.D.s R.ρ (P N) (X N) ω).2 - toL2 r T (fun t =>
          fcPartAt r (S₂ ∪ S₃) (fun k => K k (max L₂ L₃)) (fun t => withDensityReal (R.ρ t)) (P N) (X N)
            (a.1 + t) ω)‖ := fun ω => S7UCZ_norm_prod_sub _ _ _
      simp only [e]
      exact S7UCZ_lint_le (P N) _ (fun ω => Real.rpow_nonneg (norm_nonneg _) p) hI hle
    · intro a
      obtain ⟨hI, hle⟩ := hL₃ (max L₂ L₃) (le_max_right _ _) a.1 a.2
      have e : ∀ ω, ‖pairLim r T a.1 η B ω - (procWin r T a.1 η ω, toL2 r T (fun t =>
          fcGaussAt r (S₂ ∪ S₃) (fun k => K k (max L₂ L₃)) P' η (a.1 + t) ω))‖ =
          ‖(pairLim r T a.1 η B ω).2 - toL2 r T (fun t =>
          fcGaussAt r (S₂ ∪ S₃) (fun k => K k (max L₂ L₃)) P' η (a.1 + t) ω)‖ := fun ω =>
        S7UCZ_norm_prod_sub _ _ _
      simp only [e]
      exact S7UCZ_lint_le P' _ (fun ω => Real.rpow_nonneg (norm_nonneg _) p) hI hle
    · exact HRS.MC.Sec7.S7UCW.s7_UC_H4_finite_rank_W_unif_proof R r hr T hT P X₀ W X hreal P' η hη (S₂ ∪ S₃)
        (fun k => K k (max L₂ L₃)) p hp

end HRS.MC.Sec7.S7UCZ

end
