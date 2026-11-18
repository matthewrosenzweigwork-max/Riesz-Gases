import HRS.MS.SA16SEn9

/-!
# S.A.16 (SA16S) En10: the energy inequality of the generator on `W^{m+2,p}` (packet P7, step 11)

* `sa16sz_fderiv_le`: `d(jetEnergy)_G(H) ≤ p ‖G‖_J^{p-1} ‖H‖_J` (abstract, from `IsSmoothNorm`);
* `sa16sz_gen_energy`: for `G ∈ W^{m+2,p}`, `ν ≥ 0`, `b` smooth with `‖D^i b_l‖ ≤ B` (`i ≤ m+1`) and `T0` a bounded operator
  on `W^{m,p}` (the nonlocal term): `d(jetEnergy)_{ι²G}(νΔG + ι(b·∇G) - T0 ι²G) ≤ c · jetEnergy(ι²G)`,
  `c = p (cTr + C_J ‖T0‖)` independent of `ν`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer
open HRS.Whole.AppendixA.Phase2SA16V2

section En10
variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)]

lemma sa16sz_fderiv_le (k : ℕ) (G H : WmpSpace d k p) :
    fderiv ℝ (jetEnergy d k p) G H ≤ p * jetNorm d k p G ^ (p - 1) * jetNorm d k p H := by
  have hp2 : (2 : ℝ) ≤ p := Fact.out
  have hp0 : 0 < p := by linarith
  obtain ⟨hN, -, hpow, -⟩ := closed_jet_energy_calculus d k p
  set N := jetNorm d k p with hNdef
  set a := N G with ha
  set b := N H with hb
  have ha0 : 0 ≤ a := hN.nonneg G
  have hb0 : 0 ≤ b := hN.nonneg H
  -- the line `t ↦ G + t H`
  have hline : HasDerivAt (fun t : ℝ => G + t • H) H 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const H).const_add G
  have hE : HasFDerivAt (jetEnergy d k p) (sa16v2_Dj d k p G) (G + (0 : ℝ) • H) := by
    simpa using sa16v2_jetEnergy_hasFDerivAt d k p G
  have hf : HasDerivAt (jetEnergy d k p ∘ fun t : ℝ => G + t • H) (sa16v2_Dj d k p G H) 0 :=
    hE.comp_hasDerivAt (0 : ℝ) hline
  have hg : HasDerivAt (fun t : ℝ => (a + t * b) ^ p) (p * a ^ (p - 1) * b) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => a + t * b) b 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const b).const_add a
    have := h1.rpow_const (p := p) (Or.inr (by linarith))
    simpa [mul_comm, mul_assoc, mul_left_comm] using this
  have hsl1 := hf.tendsto_slope_zero_right
  have hsl2 := hg.tendsto_slope_zero_right
  have hle : sa16v2_Dj d k p G H ≤ p * a ^ (p - 1) * b := by
    refine le_of_tendsto_of_tendsto hsl1 hsl2 ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : 0 < t := ht
    simp only [Function.comp_apply, zero_add, smul_eq_mul, zero_smul, add_zero, zero_mul]
    have h1 : jetEnergy d k p (G + t • H) = N (G + t • H) ^ p := (hpow _).symm
    have h2 : jetEnergy d k p G = a ^ p := (hpow G).symm
    have h3 : N (G + t • H) ≤ a + t * b := by
      refine (hN.add _ _).trans ?_
      rw [hN.smul, abs_of_pos ht0]
    have h4 : N (G + t • H) ^ p ≤ (a + t * b) ^ p :=
      Real.rpow_le_rpow (hN.nonneg _) h3 hp0.le
    rw [h1, h2]
    exact mul_le_mul_of_nonneg_left (by linarith) (inv_nonneg.2 ht0.le)
  have hder : fderiv ℝ (jetEnergy d k p) G = sa16v2_Dj d k p G :=
    (sa16v2_jetEnergy_hasFDerivAt d k p G).fderiv
  rw [hder]
  exact hle

end En10

end HRS.Whole.AppendixA.Phase2SA16R
