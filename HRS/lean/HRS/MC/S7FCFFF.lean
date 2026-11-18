import HRS.MC.S7FCF5RE3b
import HRS.MC.S7FCF5NF6c
import HRS.MC.S7FCF5E

/-!
# Packet fcf5t, FC-F restated (`s7_FC_F_strong_moments_N2`): proof

`s7_FC_F_strong_moments_N2_proof`: the statement of `HRS.MC.Sec7.FCPlan.s7_FC_F_strong_moments_N2` (`S7FCPlan.lean`,
copied verbatim, checked in `HRS/MC/S7FCFFTie.lean`), proved from

* `HRS.MC.Sec7.S7FCF5R.fcf5_E3b_F5_zeta_moments_proof` (F5: moment of `ζ_N^{0+·}` in `C([0,T];E_r)`, uniform in `N ≥ 2`),
* `HRS.MC.Sec7.S7FCF5N.fcf5_F6c_B_moments_proof` (F6: moment of `ℬ_N^{0+·}` in `L²([0,T];E_r)`, uniform in `N ≥ 2`),
* `HRS.MC.Sec7.S7FCF5E.fcf5_G1_pair_aemeasurable_proof` (`AEMeasurable` of the particle pair `pairN`).

The product norm is the sup norm (`Prod.norm_def`), so `‖pairN‖^q = max (‖ζ‖^q) (‖ℬ‖^q)` for `q ≥ 0`
(`S7FCFF_rpow_max_eq`), which gives both the bound `≤ ‖ζ‖^q + ‖ℬ‖^q` and the measurability (`AEMeasurable.max` of the two
component integrands; no Borel structure on the product is needed).  The constant is `C5 + C6`.  No sorried module is imported.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7FCFF

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.SEdge HRS.MC.QRSpec HRS.MC.Sec7.FCPlan

variable {d : ℕ}

/-- `(max a b)^q = max (a^q) (b^q)` for nonnegative `a, b` and `q ≥ 0`. -/
theorem S7FCFF_rpow_max_eq {a b q : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hq : 0 ≤ q) :
    (max a b) ^ q = max (a ^ q) (b ^ q) := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, max_eq_right (Real.rpow_le_rpow ha h hq)]
  · rw [max_eq_left h, max_eq_left (Real.rpow_le_rpow hb h hq)]

/-- **FC-F, restated with `2 ≤ N`, proof.**  Statement verbatim from `S7FCPlan.lean`. -/
theorem s7_FC_F_strong_moments_N2_proof (R : Regime d) (r : ℝ) (hr : r = 2 * (d : ℝ) + 6) (T : ℝ) (hT : 0 < T)
    {Ω : ℕ → Type} [∀ N, MeasurableSpace (Ω N)] (P : ∀ N, Measure (Ω N))
    [∀ N, IsProbabilityMeasure (P N)] (X₀ : ∀ N, Ω N → Config d N)
    (W : ∀ N, ℝ≥0 → Ω N → (Fin N → Euc d)) (X : ∀ N, ℝ≥0 → Ω N → Config d N)
    (hreal : ∀ N, 1 ≤ N → PreparedRealization R.D (P N)
      (modulatedGibbs (periodicRiesz d R.D.s) N R.β₀ (withDensityReal R.ρ₀)) (X₀ N) (W N) (X N))
    (q : ℝ) (hq : 1 ≤ q) :
    ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N →
      Integrable (fun ω => ‖pairN r T 0 R.D.s R.ρ (P N) (X N) ω‖ ^ q) (P N) ∧
        ∫ ω, ‖pairN r T 0 R.D.s R.ρ (P N) (X N) ω‖ ^ q ∂(P N) ≤ C := by
  obtain ⟨C5, hC5⟩ := HRS.MC.Sec7.S7FCF5R.fcf5_E3b_F5_zeta_moments_proof R r hr T hT q hq
  obtain ⟨C6, hC6⟩ := HRS.MC.Sec7.S7FCF5N.fcf5_F6c_B_moments_proof R r hr T hT q hq
  refine ⟨C5 + C6, ?_⟩
  intro N hN
  have hN1 : 1 ≤ N := by omega
  have hp := hreal N hN1
  obtain ⟨⟨hZi, hZ⟩, -⟩ := hC5 0 le_rfl N hN (P N) (X₀ N) (W N) (X N) hp
  obtain ⟨hBi, hB⟩ := hC6 0 le_rfl N hN (P N) (X₀ N) (W N) (X N) hp
  have hq0 : (0 : ℝ) ≤ q := by linarith
  -- pointwise: the sup norm of the pair is the max of the two component norms (`Prod.norm_def`)
  have h1 : ∀ ω, ‖pairN r T 0 R.D.s R.ρ (P N) (X N) ω‖ =
      max ‖zetaWin r T 0 (P N) (X N) ω‖ ‖(pairN r T 0 R.D.s R.ρ (P N) (X N) ω).2‖ :=
    fun ω => Prod.norm_def _
  -- the integrand is the max of the two component integrands (no Borel structure on the product is needed)
  have heq : ∀ ω, ‖pairN r T 0 R.D.s R.ρ (P N) (X N) ω‖ ^ q =
      max (‖zetaWin r T 0 (P N) (X N) ω‖ ^ q) (‖(pairN r T 0 R.D.s R.ρ (P N) (X N) ω).2‖ ^ q) := by
    intro ω
    rw [h1 ω]
    exact S7FCFF_rpow_max_eq (norm_nonneg _) (norm_nonneg _) hq0
  have hmZ : AEMeasurable (fun ω => ‖zetaWin r T 0 (P N) (X N) ω‖ ^ q) (P N) := hZi.aemeasurable
  have hmB : AEMeasurable (fun ω => ‖(pairN r T 0 R.D.s R.ρ (P N) (X N) ω).2‖ ^ q) (P N) :=
    hBi.aemeasurable
  have hint : AEStronglyMeasurable (fun ω => ‖pairN r T 0 R.D.s R.ρ (P N) (X N) ω‖ ^ q) (P N) := by
    have hfun : (fun ω => ‖pairN r T 0 R.D.s R.ρ (P N) (X N) ω‖ ^ q) =
        fun ω => max (‖zetaWin r T 0 (P N) (X N) ω‖ ^ q) (‖(pairN r T 0 R.D.s R.ρ (P N) (X N) ω).2‖ ^ q) :=
      funext heq
    rw [hfun]
    exact (hmZ.max hmB).aestronglyMeasurable
  -- pointwise bound by the sum of the two component integrands
  have hpair : ∀ ω, ‖pairN r T 0 R.D.s R.ρ (P N) (X N) ω‖ ^ q ≤
      ‖zetaWin r T 0 (P N) (X N) ω‖ ^ q + ‖(pairN r T 0 R.D.s R.ρ (P N) (X N) ω).2‖ ^ q := by
    intro ω
    rw [heq ω]
    exact max_le (le_add_of_nonneg_right (Real.rpow_nonneg (norm_nonneg _) _))
      (le_add_of_nonneg_left (Real.rpow_nonneg (norm_nonneg _) _))
  have hmaj : Integrable (fun ω => ‖zetaWin r T 0 (P N) (X N) ω‖ ^ q +
      ‖(pairN r T 0 R.D.s R.ρ (P N) (X N) ω).2‖ ^ q) (P N) :=
    hZi.add hBi
  have hbound : ∀ ω, ‖‖pairN r T 0 R.D.s R.ρ (P N) (X N) ω‖ ^ q‖ ≤
      ‖zetaWin r T 0 (P N) (X N) ω‖ ^ q + ‖(pairN r T 0 R.D.s R.ρ (P N) (X N) ω).2‖ ^ q := by
    intro ω
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    exact hpair ω
  have hI : Integrable (fun ω => ‖pairN r T 0 R.D.s R.ρ (P N) (X N) ω‖ ^ q) (P N) :=
    Integrable.mono' hmaj hint (Filter.Eventually.of_forall hbound)
  refine ⟨hI, ?_⟩
  calc ∫ ω, ‖pairN r T 0 R.D.s R.ρ (P N) (X N) ω‖ ^ q ∂(P N)
      ≤ ∫ ω, (‖zetaWin r T 0 (P N) (X N) ω‖ ^ q + ‖(pairN r T 0 R.D.s R.ρ (P N) (X N) ω).2‖ ^ q) ∂(P N) :=
        integral_mono hI hmaj (fun ω => hpair ω)
    _ = (∫ ω, ‖zetaWin r T 0 (P N) (X N) ω‖ ^ q ∂(P N)) +
          ∫ ω, ‖(pairN r T 0 R.D.s R.ρ (P N) (X N) ω).2‖ ^ q ∂(P N) :=
        integral_add hZi hBi
    _ ≤ C5 + C6 := add_le_add hZ hB

end HRS.MC.Sec7.S7FCFF
