import HRS.MS.UniqN1cC
import HRS.MS.UniqN2bD
import HRS.MS.UniqN3cE
import HRS.MS.UniqE3c

/-!
# G2e, part A: the regime dispatch for the nonlocal term

`g2e_locMass_of_cell`: a continuous `w` with finite sup-energy has uniform local mass `√(N · cellEnergy)`.
`g2e_nmain_bound`: for `R1`, `R2a`, `R2c` (not `R3`) there is `Cd ≥ 0` with
`-nMain ≤ Cd · cellEnergy(moll z_σ).toReal`, uniformly in `ε ∈ (0,1]`, `σ ∈ [0,t]`, `c`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric Set
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.UniqG2e

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MS.UniqM1 HRS.MS.UniqT3
  HRS.MS.UniqC3 HRS.MS.UniqE3 HRS.MS.UniqNDefs HRS.PDE.ToolboxRd

variable {d : ℕ}

theorem g2e_locMass_of_cell {m : ℕ} {Cb t : ℝ} {χ χh : Euc d → ℝ} {b : ℝ → Euc d → Euc d}
    {Ψ : ℝ → Euc d → Euc d} {K : ℝ} (hF : FlowBundle d m Cb t χ χh b Ψ K) {σ : ℝ}
    (hσ : σ ∈ Icc (0 : ℝ) t) {w : Euc d → ℝ} (hw : Continuous w)
    (hfin : cellEnergy χ Ψ σ w ≠ ⊤) :
    LocMass (Real.sqrt ((coverN d Cb t 1 : ℝ) * (cellEnergy χ Ψ σ w).toReal)) w := by
  refine ⟨hw.aestronglyMeasurable, fun c => ?_⟩
  have h1 : ∫⁻ y in ball c 1, ‖w y‖ₑ ^ 2 ≤
      (coverN d Cb t 1 : ℝ≥0∞) * cellEnergy χ Ψ σ w := by
    refine le_trans ?_ (e3_cover_ball hF hσ zero_le_one hw c)
    refine (lintegral_mono_set ball_subset_closedBall).trans ?_
    refine le_of_eq (lintegral_congr fun y => ?_)
    exact enorm_sq_eq (w y)
  refine h1.trans (le_of_eq ?_)
  rw [Real.sq_sqrt (mul_nonneg (Nat.cast_nonneg _) ENNReal.toReal_nonneg),
    ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast, ENNReal.ofReal_toReal hfin]

/-- Uniform bounds of the mollification by `B` (value and derivative). -/
theorem g2e_moll_lip {ε : ℝ} (hε : 0 < ε) :
    ∃ L0 L1 : ℝ, 0 ≤ L0 ∧ 0 ≤ L1 ∧ ∀ (B : ℝ) (u : Euc d → ℝ), 0 ≤ B → LocMass B u →
      IsLipschitz (L1 * B) (moll d ε u) ∧ ∀ x, |moll d ε u x| ≤ L0 * B := by
  obtain ⟨L0, hL0, h0⟩ := moll_iteratedFDeriv_le (d := d) hε 0
  obtain ⟨L1, hL1, h1⟩ := moll_iteratedFDeriv_le (d := d) hε 1
  refine ⟨L0, L1, hL0, hL1, fun B u hB hu => ⟨?_, fun x => ?_⟩⟩
  · have hd : ContDiff ℝ ∞ (moll d ε u) := moll_contDiff hε hu.locallyIntegrable
    have hdiff : Differentiable ℝ (moll d ε u) := hd.differentiable (by simp)
    intro x y
    have := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := moll d ε u)
      (s := Set.univ) (C := L1 * B) (x := y) (y := x) (fun z _ => hdiff z)
      (fun z _ => by
        have := h1 B u hB hu z
        rwa [norm_iteratedFDeriv_one] at this) convex_univ (Set.mem_univ _) (Set.mem_univ _)
    simpa [Real.norm_eq_abs] using this
  · have := h0 B u hB hu x
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this

/-- The regime dispatch: a uniform constant `Cd` with `-nMain ≤ Cd · cellEnergy`. -/
theorem g2e_nmain_bound (hd : 1 ≤ d) (D : WholeDyn d) (hs0 : 0 ≤ D.s) (hsd : D.s < d) (ν₀ : ℝ)
    (Rg : PDE.Regime) (hR : RdRegimeHolds Rg d D.s D.M D.invβ ν₀) (hRne : Rg ≠ PDE.Regime.R3)
    (m : ℕ) (Cb Λ T t : ℝ) (ρ : ℝ → Euc d → ℝ) (hcoef : CoeffHypRd D.s m Λ T ρ)
    (ht : t ∈ Set.Icc (0 : ℝ) T) (χ χh : Euc d → ℝ) (hχ : IsCutoffPair χ χh)
    (b : ℝ → Euc d → Euc d) (Ψ : ℝ → Euc d → Euc d)
    (hb : HRS.Whole.IsAdvectingDrift m Cb t b) (hΨ : HRS.Whole.IsNegDriftFlow t b Ψ)
    (K : ℝ) (hK : FlowBundle d m Cb t χ χh b Ψ K)
    {z : ℝ → Euc d → ℝ} {B : ℝ} (hB : 0 ≤ B) (hLM : ∀ τ ∈ Icc (0 : ℝ) t, LocMass B (z τ)) :
    ∃ Cd : ℝ, 0 ≤ Cd ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ σ ∈ Icc (0 : ℝ) t, ∀ c : Euc d,
      -(nMain D (ρ (t - σ)) (moll d ε (z σ)) (fun x => varsigma χ Ψ σ c x * moll d ε (z σ) x)) ≤
        Cd * (cellEnergy χ Ψ σ (moll d ε (z σ))).toReal := by
  have hcore : ∃ C : ℝ, 0 ≤ C ∧ ∀ σ ∈ Set.Icc (0 : ℝ) t, ∀ (c : Euc d) (A LF BF : ℝ) (f : Euc d → ℝ),
      0 ≤ A → ContDiff ℝ ∞ f → LocMass A f → IsLipschitz LF f → (∀ x, |f x| ≤ BF) →
      -(nMain D (ρ (t - σ)) f (fun x => varsigma χ Ψ σ c x * f x)) ≤ C * A ^ 2 := by
    cases Rg with
    | R1 =>
      obtain ⟨C, hC, h⟩ := HRS.MS.UniqN1c.n1c_r1_core hd D hs0 hsd ν₀ hR m Cb Λ T t ρ hcoef ht χ χh
        hχ b Ψ hb hΨ K hK
      exact ⟨C, hC, fun σ hσ c A LF BF f hA hf hLMf _ _ =>
        (neg_le_abs _).trans (h σ hσ c A f hA hf hLMf)⟩
    | R2a =>
      obtain ⟨C, hC, h⟩ := HRS.MS.UniqN2b.n2b_r2a_core hd D hs0 hsd ν₀ hR m Cb Λ T t ρ hcoef ht χ χh
        hχ b Ψ hb hΨ K hK
      exact ⟨C, hC, fun σ hσ c A LF BF f hA hf hLMf _ _ =>
        (neg_le_abs _).trans (h σ hσ c A f hA hf hLMf)⟩
    | R2b a => exact hR.elim
    | R2c =>
      exact HRS.MS.UniqN3c.n3c_r2c_core hd D hs0 hsd ν₀ hR m Cb Λ T t ρ hcoef ht χ χh
        hχ b Ψ hb hΨ K hK
    | R3 => exact absurd rfl hRne
  obtain ⟨C, hC, hcore⟩ := hcore
  obtain ⟨N0, hN0⟩ := e3_cellEnergy_le hK
  refine ⟨C * (coverN d Cb t 1 : ℝ), mul_nonneg hC (Nat.cast_nonneg _), fun ε hε hε1 σ hσ c => ?_⟩
  have hfin : cellEnergy χ Ψ σ (moll d ε (z σ)) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ENNReal.ofReal_ne_top)
      (hN0 ε hε hε1 B (z σ) (hLM σ hσ) σ hσ)
  have hcd : ContDiff ℝ ∞ (moll d ε (z σ)) := moll_contDiff hε (hLM σ hσ).locallyIntegrable
  have hLMf := g2e_locMass_of_cell hK hσ hcd.continuous hfin
  obtain ⟨L0, L1, -, -, hL⟩ := g2e_moll_lip (d := d) hε
  obtain ⟨hlip, hbd⟩ := hL B (z σ) hB (hLM σ hσ)
  have := hcore σ hσ c _ _ _ _ (Real.sqrt_nonneg _) hcd hLMf hlip hbd
  rw [Real.sq_sqrt (mul_nonneg (Nat.cast_nonneg _) ENNReal.toReal_nonneg)] at this
  linarith

end HRS.MS.UniqG2e
