import HRS.MS.SA16Y4Ct5
import HRS.MS.SA16SEn2

/-!
# S.A.16 (SA16Y4) Ct6: derivative gain of `R_n` on `WmpSpace`

`sa16y4_Rgain`: for any CLM `R` with `R (Jcc ψ) = Jcc (ρ_n ⋆ ψ)` and `Z ∈ W^{k+1,p}`:
`‖ι Z - R (ι Z)‖ ≤ (card(WIndex d k) · d / (n+1)) ‖Z‖` (`ι : W^{k+1} → W^k`).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Q Phase2SA16Evolution Phase2SA16Transfer

section Ct6
variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)]

lemma sa16y4_pd_sub {f g : EuclideanSpace ℝ (Fin d) → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) {j : ℕ}
    (idx : Fin j → Fin d) (x : EuclideanSpace ℝ (Fin d)) :
    partialDeriv idx (fun y => f y - g y) x = partialDeriv idx f x - partialDeriv idx g x := by
  unfold partialDeriv
  have := iteratedFDeriv_sub_apply (𝕜 := ℝ) (i := j) (x := x) (f := f) (g := g)
    (hf.contDiffAt.of_le (by exact_mod_cast le_top)) (hg.contDiffAt.of_le (by exact_mod_cast le_top))
  rw [show (fun y => f y - g y) = f - g from rfl, this]
  rfl

theorem sa16y4_Rgain (k n : ℕ) (R : WmpSpace d k p →L[ℝ] WmpSpace d k p)
    (hR : ∀ ψ : ccSub d, R (sa16r_Jcc d k p ψ) = sa16r_Jcc d k p ⟨sa16q_mol n ψ.1, sa16y4_mol_cc ψ.2 n⟩)
    (Z : WmpSpace d (k + 1) p) :
    ‖sa16r_iota d k p Z - R (sa16r_iota d k p Z)‖ ≤
      ((Fintype.card (WIndex d k) : ℝ) * d / ((n : ℝ) + 1)) * ‖Z‖ := by
  have hp1 : 1 ≤ p := le_trans one_le_two (Fact.out : 2 ≤ p)
  refine (sa16r_Jcc_dense d (k + 1) p).induction_on Z (isClosed_le ?_ ?_) (fun φ => ?_)
  · exact ((sa16r_iota d k p).continuous.sub (R.continuous.comp (sa16r_iota d k p).continuous)).norm
  · exact continuous_const.mul continuous_norm
  · rw [sa16r_iota_Jcc, hR φ, ← map_sub]
    set χ : ccSub d := φ - ⟨sa16q_mol n φ.1, sa16y4_mol_cc φ.2 n⟩ with hχ
    have hχ1 : χ.1 = fun x => φ.1 x - sa16q_mol n φ.1 x := rfl
    rw [sa16y4_Jcc_norm' k χ, sa16y4_Jcc_norm' (k + 1) φ]
    set c : ℝ := (Fintype.card (WIndex d k) : ℝ) * d / ((n : ℝ) + 1) with hc
    -- componentwise bound
    have hcomp : ∀ τ : WIndex d k, eLpNorm (partialDeriv τ.2 χ.1) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal (1 / ((n : ℝ) + 1)) * (((d : ℝ≥0∞)) *
          eLpNorm (fun x => ‖wJet (k + 1) φ.1 x‖) (ENNReal.ofReal p) volume) := by
      intro τ
      have hφ1 : ContDiff ℝ ∞ φ.1 := φ.2.1
      have hpd : IsCcInfty (partialDeriv τ.2 φ.1) := sa16s_cc_partialDeriv φ.2 τ.2
      have e1 : partialDeriv τ.2 χ.1 = fun x => partialDeriv τ.2 φ.1 x - sa16q_mol n (partialDeriv τ.2 φ.1) x := by
        funext x
        rw [hχ1, sa16y4_pd_sub hφ1 (sa16y4_mol_cc φ.2 n).1 τ.2 x,
          sa16q_mol_pd n (φ.2.1.of_le (by simp)) τ.2]
      rw [e1]
      refine (sa16y4_mol_sub_eLp hp1 n hpd).trans (mul_le_mul' le_rfl ?_)
      -- `G1` of a derivative
      have hG : ∀ x, sa16y4_G1 (partialDeriv τ.2 φ.1) x ≤ ∑ i : Fin d, ‖wJet (k + 1) φ.1 x‖ := by
        intro x
        unfold sa16y4_G1
        refine Finset.sum_le_sum fun i _ => ?_
        have h1 : fderiv ℝ (partialDeriv τ.2 φ.1) x (EuclideanSpace.single i 1) =
            partialDeriv (Fin.cons i τ.2 : Fin ((τ.1 : ℕ) + 1) → Fin d) φ.1 x :=
          (sa16s_pd_cons hφ1 i τ.2 x).symm
        rw [h1]
        have hτm : (τ.1 : ℕ) + 1 ≤ k + 1 := by have := τ.1.isLt; omega
        have := sa16j_pd_le_jet (k + 1) φ.1 x hτm (Fin.cons i τ.2)
        simpa [Real.norm_eq_abs] using this
      have hGc := sa16y4_G1_cont hpd
      calc eLpNorm (sa16y4_G1 (partialDeriv τ.2 φ.1)) (ENNReal.ofReal p) volume
          ≤ eLpNorm (fun x => ∑ i : Fin d, ‖wJet (k + 1) φ.1 x‖) (ENNReal.ofReal p) volume :=
            eLpNorm_mono_real hGc.aestronglyMeasurable (fun x => by
              rw [Real.norm_of_nonneg (by unfold sa16y4_G1; exact Finset.sum_nonneg fun i _ => abs_nonneg _)]
              exact hG x)
        _ = (d : ℝ≥0∞) * eLpNorm (fun x => ‖wJet (k + 1) φ.1 x‖) (ENNReal.ofReal p) volume := by
            have : (fun x => ∑ i : Fin d, ‖wJet (k + 1) φ.1 x‖) = fun x => (d : ℝ) * ‖wJet (k + 1) φ.1 x‖ := by
              funext x; simp
            rw [this, sa16y3_eLp_mul_const (q := p) (Nat.cast_nonneg d), ENNReal.ofReal_natCast]
    have hE : eLpNorm (fun x => ‖wJet k χ.1 x‖) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal c * eLpNorm (fun x => ‖wJet (k + 1) φ.1 x‖) (ENNReal.ofReal p) volume := by
      refine (sa16y4_jet_eLp_le χ.2 k hp1).trans ?_
      calc ∑ τ : WIndex d k, eLpNorm (partialDeriv τ.2 χ.1) (ENNReal.ofReal p) volume
          ≤ ∑ τ : WIndex d k, ENNReal.ofReal (1 / ((n : ℝ) + 1)) * (((d : ℝ≥0∞)) *
              eLpNorm (fun x => ‖wJet (k + 1) φ.1 x‖) (ENNReal.ofReal p) volume) :=
            Finset.sum_le_sum fun τ _ => hcomp τ
        _ = ENNReal.ofReal c * eLpNorm (fun x => ‖wJet (k + 1) φ.1 x‖) (ENNReal.ofReal p) volume := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hc]
            have hn1 : (0 : ℝ) ≤ 1 / ((n : ℝ) + 1) := by positivity
            have : ENNReal.ofReal ((Fintype.card (WIndex d k) : ℝ) * d / ((n : ℝ) + 1)) =
                (Fintype.card (WIndex d k) : ℝ≥0∞) * ENNReal.ofReal (1 / ((n : ℝ) + 1)) * (d : ℝ≥0∞) := by
              rw [show (Fintype.card (WIndex d k) : ℝ) * d / ((n : ℝ) + 1) =
                (Fintype.card (WIndex d k) : ℝ) * (1 / ((n : ℝ) + 1)) * d by ring,
                ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (Nat.cast_nonneg _),
                ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
            rw [this]; ring
    have hfin : eLpNorm (fun x => ‖wJet (k + 1) φ.1 x‖) (ENNReal.ofReal p) volume ≠ ⊤ := by
      rw [sa16y3_norm_wJet_eq φ.2 (k + 1)]
      exact (sa16r_jet_memLp_cc (p := p) φ.2 (k + 1)).eLpNorm_lt_top.ne
    have h2 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) hE
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at h2
    exact h2

end Ct6

end HRS.Whole.AppendixA.Phase2SA16R
