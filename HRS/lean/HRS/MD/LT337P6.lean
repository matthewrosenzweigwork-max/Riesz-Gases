import HRS.MD.LT337Vocab
import HRS.MD.LT337P1
import HRS.Energy.Commutator.SuperAssembly
import HRS.Energy.Commutator.Coerc0
import HRS.Stochastic.Particle
import HRS.PDE.EnergyR2Fn

/-!
# Packet LT6 (chunk D): the pathwise drift bound of the Coulomb energy identity

`lt6_drift_bound_proof` is the statement `HRS.MD.LT337.lt6_drift_bound` (M L3147-3151), written with the sorry-free
vocabulary copy `HRS.MD.LT337Vocab`.  Inputs: the Lipschitz bound `lt1_lipschitz_proof`, the proved commutator estimate
`HRS.Commutator.commutator_estimate_super` (the spec's `lt0`), `energy_add_oN_nonneg`, the sign of the micro term.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators
open HRS HRS.MD.LT337Vocab

namespace HRS.MD.LT337P6

variable {d N : ℕ}

/-- `𝒟_N ≤ 2 c_d Λ` (copy of the proof of `lt3_diffLimit_le`, with `0 < c_d` as an input). -/
theorem lt6_diffLimit_le (hN : 0 < N) {ρ : Torus d → ℝ} (Λ : ℝ) (hρ : ∀ x, ρ x ≤ Λ)
    (hc : 0 < cd d) (X : Config d N) : diffLimit d ρ X ≤ 2 * cd d * Λ := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 : (1 / (N : ℝ)) * ∑ i, ρ (X i) ≤ Λ := by
    have : ∑ i, ρ (X i) ≤ N * Λ := by
      calc ∑ i, ρ (X i) ≤ ∑ _i : Fin N, Λ := Finset.sum_le_sum fun i _ => hρ _
        _ = N * Λ := by simp
    calc (1 / (N : ℝ)) * ∑ i, ρ (X i) ≤ (1 / (N : ℝ)) * (N * Λ) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = Λ := by field_simp
  have h2 : 0 ≤ ∫ x : Torus d, ρ x ^ 2 := integral_nonneg fun x => sq_nonneg _
  have h3 : 0 ≤ 1 / (N : ℝ) := by positivity
  unfold diffLimit
  have : -(1 / (N : ℝ)) + 2 * ((1 / (N : ℝ)) * ∑ i, ρ (X i)) - ∫ x, ρ x ^ 2 ≤ 2 * Λ := by linarith
  calc cd d * (-(1 / (N : ℝ)) + 2 * ((1 / (N : ℝ)) * ∑ i, ρ (X i)) - ∫ x, ρ x ^ 2)
      ≤ cd d * (2 * Λ) := mul_le_mul_of_nonneg_left this hc.le
    _ = 2 * cd d * Λ := by ring

/-- The microscopic term is nonpositive for `M` with nonpositive symmetric part. -/
theorem lt6_microG_nonpos (D : DynData d) (hS : Torus.SymNonpos D.M) (ρ : Torus d → ℝ) (X : Config d N) :
    microG D ρ X ≤ 0 := by
  unfold microG
  refine mul_nonpos_of_nonneg_of_nonpos (by positivity) (Finset.sum_nonpos fun i _ => ?_)
  exact inner_matVec_nonpos hS _

theorem lt6_drift_bound_proof (hd : 2 ≤ d) (T Λ ΛV Mb : ℝ) :
    ∃ C₀min κ κ' : ℝ, 0 ≤ C₀min ∧ 0 ≤ κ ∧ 0 ≤ κ' ∧ ∀ C₀ : ℝ, C₀min ≤ C₀ →
      ∀ (D : DynData d) (N : ℕ), 2 ≤ N → ∀ ρ : ℝ → Torus d → ℝ, LTDet D T Λ ΛV Mb ρ →
        ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ Z : Config d N, Z ∉ collisionSet d N →
          0 ≤ correctedEnergy D C₀ Λ ρ Z r ∧
          ltDrift D ρ r Z ≤ κ * correctedEnergy D C₀ Λ ρ Z r + κ' * D.invβ := by
  have hd1 : 1 ≤ d := by omega
  have hs0 : (0 : ℝ) ≤ (d : ℝ) - 2 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hsd : (d : ℝ) - 2 < d := by linarith
  obtain ⟨L, hL0, hL⟩ := HRS.MD.LT337P1.lt1_lipschitz_proof hd Λ ΛV Mb
  obtain ⟨C₀c, Cc, hC₀c, hCc, hcomm⟩ :=
    HRS.Commutator.commutator_estimate_super (d := d) (s := (d : ℝ) - 2) hd1 hs0 le_rfl hsd
  obtain ⟨C₀e, hC₀e, hen⟩ :=
    HRS.Commutator.energy_add_oN_nonneg (d := d) (s := (d : ℝ) - 2) hd1 hs0 hsd
  have hcd : 0 < cd d := rieszConst_pos hd hs0 hsd
  refine ⟨max C₀c C₀e, Cc * L / 2, 2 * cd d * max Λ 0, le_max_of_le_left hC₀c, by positivity,
    by positivity, ?_⟩
  intro C₀ hC₀ D N hN ρ hdet r hr Z hZ
  obtain ⟨hs, hSN, hM, ⟨hV, hVb⟩, hmf, hreg, hΛ⟩ := hdet
  have hρ : IsProbDensity (ρ r) := hmf.density r hr
  have hreg' := hreg r hr
  have hρΛ : ∀ x, ρ r x ≤ Λ := fun x =>
    (le_abs_self _).trans ((HRS.PDE.R2Aux.abs_le_cbNorm hreg'.1 x).trans hreg'.2)
  have hLip := hL D hs hM hV hVb (ρ r) hreg'.1 hreg'.2
  have hΛ0 : 0 ≤ Λ := by linarith
  have hce : correctedEnergy D C₀ Λ ρ Z r =
      rieszEnergy d D.s Z (withDensityReal (ρ r)) + oNΛ d D.s C₀ Λ N := rfl
  have hm1 : oNΛ d D.s C₀e Λ N ≤ oNΛ d D.s C₀ Λ N := by
    rw [hs]; exact oNΛ_mono_C₀ ((le_max_right _ _).trans hC₀) hΛ0 N
  have hm2 : oNΛ d D.s C₀c Λ N ≤ oNΛ d D.s C₀ Λ N := by
    rw [hs]; exact oNΛ_mono_C₀ ((le_max_left _ _).trans hC₀) hΛ0 N
  have hnn : 0 ≤ correctedEnergy D C₀ Λ ρ Z r := by
    have := hen Λ hΛ N hN (ρ r) hρ hρΛ Z hZ
    rw [← hs] at this
    rw [hce]; linarith
  refine ⟨hnn, ?_⟩
  have hc := hcomm Λ hΛ N hN (ρ r) hρ hρΛ Z hZ L (meanFieldDrift D (ρ r)) hL0 hLip
  rw [← hs] at hc
  have hc2 : (1 / 2 : ℝ) * commQuantity d D.s (meanFieldDrift D (ρ r)) Z (withDensityReal (ρ r)) ≤
      Cc * L / 2 * correctedEnergy D C₀ Λ ρ Z r := by
    have h1 := le_abs_self (commQuantity d D.s (meanFieldDrift D (ρ r)) Z (withDensityReal (ρ r)))
    have h2 : 0 ≤ Cc * L := by positivity
    have h3 : Cc * L * (rieszEnergy d D.s Z (withDensityReal (ρ r)) + oNΛ d D.s C₀c Λ N) ≤
        Cc * L * correctedEnergy D C₀ Λ ρ Z r := by
      rw [hce]; exact mul_le_mul_of_nonneg_left (by linarith) h2
    linarith
  have hmic := lt6_microG_nonpos D hSN (ρ r) Z
  have hdiff := lt6_diffLimit_le (by omega : 0 < N) Λ hρΛ hcd Z
  have hβ : 0 ≤ D.invβ := D.hβ
  have hdiff2 : D.invβ * diffLimit d (ρ r) Z ≤ 2 * cd d * max Λ 0 * D.invβ := by
    calc D.invβ * diffLimit d (ρ r) Z ≤ D.invβ * (2 * cd d * Λ) := mul_le_mul_of_nonneg_left hdiff hβ
      _ ≤ D.invβ * (2 * cd d * max Λ 0) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)) hβ
      _ = _ := by ring
  unfold ltDrift
  linarith

end HRS.MD.LT337P6
