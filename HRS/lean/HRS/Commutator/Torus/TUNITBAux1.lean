import HRS.Commutator.Torus.TUNITAux8
import HRS.Commutator.Torus.TLIProof

/-!
# T-UNIT-b helpers, part 1: `low_bound_T`

Prefix `tunitb_`.  Torus analogue of `ULOW.ulow_main` (`(5.lowpartbound)`): Lemma 4.1 (`low_velocity_T_proof`)
applied to `σ = ν = chargeT X ρ` (finite, mass zero), `scoercive_T`, and `‖ν‖²_{g_η} ≤ (2+K_s)Q_η`
(`tunit_kerEnergy_le`).
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators

namespace HRS.Commutator.TorusNote

open HRS HRS.KernelGrad

variable {d : ℕ} {s : ℝ}

theorem tunitb_K_nonneg {v : Torus d → Euc d} {K : ℝ} (hv : TorusSubTransport d s v K) : 0 ≤ K := by
  obtain ⟨L, F, hL, hF, -, -, hLF⟩ := hv
  linarith

theorem tunitb_Q_nonneg {p : ℝ≥0∞} (hp1 : 1 ≤ p) {η : ℝ} (hη : 0 < η) {ρ : Torus d → ℝ}
    {N : ℕ} (hN : 1 ≤ N) {Q : ℝ}
    (hA : η ^ (-s) / (N : ℝ) + normT p ρ * η ^ ((d : ℝ) * (1 - (p⁻¹).toReal) - s) ≤ Q)
    (hρ : BddDensityT ρ) : 0 ≤ Q := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hnp1 : 1 ≤ normT p ρ := ten2_normT_ge_one hp1 hρ
  have h1 : 0 ≤ η ^ ((d : ℝ) * (1 - (p⁻¹).toReal) - s) := Real.rpow_nonneg hη.le _
  have h2 : 0 ≤ η ^ (-s) / (N : ℝ) := by
    have : 0 ≤ η ^ (-s) := Real.rpow_nonneg hη.le _
    positivity
  have : 0 ≤ normT p ρ * η ^ ((d : ℝ) * (1 - (p⁻¹).toReal) - s) :=
    mul_nonneg (by linarith) h1
  linarith

theorem tunitb_low_main (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ η₀ C : ℝ, 0 < η₀ ∧ η₀ ≤ 1 ∧ 0 < C ∧ ∀ p : ℝ≥0∞,
      ENNReal.ofReal ((d : ℝ) / (d - s)) < p →
      ∃ Cp0 : ℝ, 0 < Cp0 ∧ ∀ Cp : ℝ, Cp0 ≤ Cp → ∀ η : ℝ, 0 < η → η ≤ η₀ →
      ∀ ρ : Torus d → ℝ, BddDensityT ρ → ∀ (N : ℕ) (X : Config d N), 1 ≤ N → X ∉ collisionSet d N →
      ∀ (v : Torus d → Euc d) (K : ℝ), TorusSubTransport d s v K →
        |CcommT (gloForceT s η) (PleqT η v) (chargeT X ρ)| ≤ C * K * scaleQT s Cp p η X ρ := by
  obtain ⟨Cl, hCl, hlow⟩ := low_velocity_T_proof hd hs0 hsd
  obtain ⟨Cs, hCs, hsc⟩ := scoercive_T hd hs0 hsd
  obtain ⟨Cb, η₀, hCb, hη₀, hη₀1, hEC⟩ := energy_control_T hd hs0 hsd
  have hK2 : 0 < 2 + ten2K d s := by have := ten2K_nonneg hd hs0 hsd; linarith
  refine ⟨η₀, Cl * Cs * (2 + ten2K d s), hη₀, hη₀1, by positivity, fun p hp => ?_⟩
  obtain ⟨Cp0, hCp0, hE⟩ := hEC p hp
  refine ⟨Cp0, hCp0, fun Cp hCp η hη hηη₀ ρ hρ N X hN hX v K hv => ?_⟩
  have hη1 : η ≤ 1 := hηη₀.trans hη₀1
  have hp1 : 1 ≤ p := (tunit_one_lt_p hd hs0 hsd hp).le
  obtain ⟨hA, hB, -, -⟩ := hE Cp hCp η hη hηη₀ ρ hρ N X hN hX
  set Q := scaleQT s Cp p η X ρ with hQ
  have hQ0 : 0 ≤ Q := tunitb_Q_nonneg hp1 hη hN hA hρ
  have hK0 : 0 ≤ K := tunitb_K_nonneg hv
  have hker : kerEnergyT (gTorus s η) (chargeT X ρ) ≤ (2 + ten2K d s) * Q :=
    tunit_kerEnergy_le hd hs0 hsd hp1 hη hη1 hρ hN X hA hB
  have hfin := ten2_charge_finite hN X hρ
  have hmass := tunit_charge_mass ρ hρ hN X
  have h2 := hlow η hη hη1 v K hv (chargeT X ρ) hfin hmass
  have h3 := hsc η hη hη1 (chargeT X ρ) hfin hmass
  have h4 : homSqT (-Whole.alphaE d s) (lowFreqT η 4 (chargeT X ρ).coef) ≤
      ENNReal.ofReal (Cs * ((2 + ten2K d s) * Q)) :=
    le_trans (le_trans le_self_add h3) (ENNReal.ofReal_le_ofReal (by gcongr))
  have hR : 0 ≤ Cl * Cs * (2 + ten2K d s) * K * Q := by positivity
  have hfin2 : |CcommT (gloForceT s η) (PleqT η v) (chargeT X ρ)| ≤
      Cl * K * (Cs * ((2 + ten2K d s) * Q)) := by
    rw [← ENNReal.ofReal_le_ofReal_iff (by positivity)]
    calc ENNReal.ofReal |CcommT (gloForceT s η) (PleqT η v) (chargeT X ρ)|
        ≤ ENNReal.ofReal (Cl * K) *
            homSqT (-Whole.alphaE d s) (lowFreqT η 4 (chargeT X ρ).coef) := h2
      _ ≤ ENNReal.ofReal (Cl * K) * ENNReal.ofReal (Cs * ((2 + ten2K d s) * Q)) := by gcongr
      _ = ENNReal.ofReal (Cl * K * (Cs * ((2 + ten2K d s) * Q))) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
  calc _ ≤ Cl * K * (Cs * ((2 + ten2K d s) * Q)) := hfin2
    _ = Cl * Cs * (2 + ten2K d s) * K * Q := by ring

end HRS.Commutator.TorusNote
