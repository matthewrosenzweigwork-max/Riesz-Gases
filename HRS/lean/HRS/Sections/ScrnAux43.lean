import HRS.Sections.ScrnAux42

/-!
# Packet SCRN, part 43: the particle-to-Gaussian bound `smoothDist 3 (law Z) N(0,Q_N)`

`scrn_prob_bound`: for the transported mesoscopic tests (`ScrnTr`),
`d₃(law Z, N(0, Q_N)) ≤ E‖R‖-bound + Lindeberg + ½ covariation-discrepancy-bound`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS

open HRS.Main.A8P PDE

variable {d : ℕ}

local notation "ℝ^" p => EuclideanSpace ℝ (Fin p)

theorem scrn_prob_bound (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (β : ℝ) (hβ : 0 < β)
    {N : ℕ} (hN : 2 ≤ N) {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X₀ : Ω → Config d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)}
    {X : ℝ≥0 → Ω → Config d N} (hfl : ScrnFlow d hs0 hsd β hβ N P X₀ W X)
    {C₀ Cq : ℝ} (hC₀ : 0 ≤ C₀) (hcom : A8CommSpec d s C₀ Cq) (hCq : 0 ≤ Cq) {bm bp ℓ CG : ℝ}
    (hbm : 0 < bm) (hbp : 0 < bp) (hℓ : 0 < ℓ) (hCG : 0 ≤ CG) (hbN : bm ≤ β * ℓ ^ ((d : ℝ) - s))
    {p : ℕ} {ts : Fin p → ℝ} {ψ : Fin p → Torus d → ℝ} {f : Fin p → ℝ → Torus d → ℝ}
    (htr : ScrnTr d hs0 hsd hβ ℓ (scrnLamS d s bp ℓ) CG ts ψ f) :
    smoothDist 3 (law P (scrnZ ψ ts X))
        (multivariateGaussian 0 (scrnQ f ts (∑ a, ts a + 1) β⁻¹)) ≤
      p * (Cq * CG / (2 * min (rieszConst d s) bp⁻¹)) *
          (Real.sqrt N * oN d s C₀ N *
            ℓ ^ (-((d : ℝ) / 2) - 2 - max ((d : ℝ) - s - 2) 0)) +
        (1 + Real.sqrt 3) / (6 * Real.sqrt N) *
          (2 * p * (CG * ℓ ^ (-((d : ℝ) / 2))) * (p * CG ^ 2)) +
        (1 / 2) * ((p : ℝ) ^ 2 * (2 * Cq / (bm * min (rieszConst d s) bp⁻¹)) *
        ((2 * d * CG ^ 2) * ((N : ℝ) ^ (-(1 : ℝ) / d) * ℓ ^ (-(d : ℝ) - 3 + min ((d : ℝ) - s) 2)) +
          (2 * d * 2 ^ (3 * (((d : ℝ) - s) / 2) / 2) * CG ^ 2) * (Real.sqrt (oN d s C₀ N) *
            ℓ ^ (-((d : ℝ) + ((d : ℝ) - s)) / 2 - 2 + min ((d : ℝ) - s) 2)))) := by
  obtain ⟨ℱ, W', hF⟩ := hfl.filt
  set Tm : ℝ := ∑ a, ts a + 1 with hTm
  have hTm0 : 0 < Tm := by
    have : 0 ≤ ∑ a, ts a := Finset.sum_nonneg fun a _ => htr.ts0 a
    rw [hTm]; linarith
  have htsT : ∀ a, ts a ∈ Set.Icc 0 Tm := fun a =>
    ⟨htr.ts0 a, by
      have : ts a ≤ ∑ b, ts b := Finset.single_le_sum (fun b _ => htr.ts0 b) (Finset.mem_univ a)
      rw [hTm]; linarith⟩
  obtain ⟨hRint, hRbd⟩ := scrn_rem_final hd hs0 hsd β hβ hN hfl hC₀ hcom hCq hbp hℓ hCG htr
  have hcov := scrn_cov_final hd hs0 hsd β hβ hN hfl hC₀ hcom hCq hbm hbp hℓ hCG hbN hTm0 htr htsT
  have hlin := scrn_lind_final hℓ hCG htr
  have hsolT := hfl.sol Tm hTm0.le
  have hass := scrn_assembly hd hs0 hsd β hβ hN hF hTm0.le hsolT hfl.law0 ts htsT ψ htr.ck2 f
    htr.cases htr.c12 htr.fcont hRint
  set B1 : ℝ := ∫ ω, ‖scrnRem (PDE.mfData d s hs0 hsd (fun _ => 0) β hβ) f ts X ω‖ ∂P +
        (1 + Real.sqrt 3) / (6 * Real.sqrt N) * ∫ y, ‖scrnFvec f y -
          ∫ y', scrnFvec f y' ∂(volume : Measure (Torus d))‖ ^ 3 ∂(volume : Measure (Torus d)) +
        (1 / 2) * covDiscrepancyMatrix P Tm
          (killedCovMatrix (fun a => scrnPhi (PDE.mfData d s hs0 hsd (fun _ => 0) β hβ) (Real.sqrt N)
            (ts a) (f a) X) ts)
          (scrnSig ts (scrnGc ts f) (2 * (PDE.mfData d s hs0 hsd (fun _ => 0) β hβ).invβ)) with hB1
  have hsqN : 0 < Real.sqrt N := Real.sqrt_pos.2 (by exact_mod_cast (show 0 < N by omega))
  have hcoef : 0 ≤ (1 + Real.sqrt 3) / (6 * Real.sqrt N) := by positivity
  have hB1le : B1 ≤ p * (Cq * CG / (2 * min (rieszConst d s) bp⁻¹)) *
          (Real.sqrt N * oN d s C₀ N *
            ℓ ^ (-((d : ℝ) / 2) - 2 - max ((d : ℝ) - s - 2) 0)) +
        (1 + Real.sqrt 3) / (6 * Real.sqrt N) *
          (2 * p * (CG * ℓ ^ (-((d : ℝ) / 2))) * (p * CG ^ 2)) +
        (1 / 2) * ((p : ℝ) ^ 2 * (2 * Cq / (bm * min (rieszConst d s) bp⁻¹)) *
        ((2 * d * CG ^ 2) * ((N : ℝ) ^ (-(1 : ℝ) / d) * ℓ ^ (-(d : ℝ) - 3 + min ((d : ℝ) - s) 2)) +
          (2 * d * 2 ^ (3 * (((d : ℝ) - s) / 2) / 2) * CG ^ 2) * (Real.sqrt (oN d s C₀ N) *
            ℓ ^ (-((d : ℝ) + ((d : ℝ) - s)) / 2 - 2 + min ((d : ℝ) - s) 2)))) := by
    have h2 := mul_le_mul_of_nonneg_left hlin hcoef
    have h3 := mul_le_mul_of_nonneg_left hcov (by norm_num : (0 : ℝ) ≤ 1 / 2)
    simp only [hB1]
    linarith
  have hB1' : 0 ≤ p * (Cq * CG / (2 * min (rieszConst d s) bp⁻¹)) *
          (Real.sqrt N * oN d s C₀ N *
            ℓ ^ (-((d : ℝ) / 2) - 2 - max ((d : ℝ) - s - 2) 0)) +
        (1 + Real.sqrt 3) / (6 * Real.sqrt N) *
          (2 * p * (CG * ℓ ^ (-((d : ℝ) / 2))) * (p * CG ^ 2)) +
        (1 / 2) * ((p : ℝ) ^ 2 * (2 * Cq / (bm * min (rieszConst d s) bp⁻¹)) *
        ((2 * d * CG ^ 2) * ((N : ℝ) ^ (-(1 : ℝ) / d) * ℓ ^ (-(d : ℝ) - 3 + min ((d : ℝ) - s) 2)) +
          (2 * d * 2 ^ (3 * (((d : ℝ) - s) / 2) / 2) * CG ^ 2) * (Real.sqrt (oN d s C₀ N) *
            ℓ ^ (-((d : ℝ) + ((d : ℝ) - s)) / 2 - 2 + min ((d : ℝ) - s) 2)))) := by
    have hc1 : 0 < min (rieszConst d s) bp⁻¹ :=
      lt_min (rieszConst_pos hd hs0 hsd) (inv_pos.2 hbp)
    have hoN : 0 ≤ oN d s C₀ N := scrn_oN_nonneg hC₀ (show 1 ≤ N by omega)
    have hdR : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    positivity
  exact scrn_smoothDist_le_d3 _ _ hB1' (hass.trans (ENNReal.ofReal_le_ofReal hB1le))

end HRS
