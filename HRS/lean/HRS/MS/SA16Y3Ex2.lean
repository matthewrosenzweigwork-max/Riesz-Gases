import HRS.MS.SA16Y3Ex1
import HRS.MS.SA16JetSchwartz

/-!
# S.A.16 (SA16Y3) Ex2: the cut-off mollifier as a bounded operator on `WmpSpace` (SA16S item (iii), steps (b))

`sa16y3_Lop n : ccSub d →ₗ sa16r_S d m p`, `ψ ↦ cutmol n ψ`, is linear and lands in `sa16r_S`.
`sa16y3_extend_cutmol`: for every `n` there is a bounded operator `T_n` on `WmpSpace d m p` with
`‖T_n‖ ≤ C` (`C` independent of `n`) and `T_n (Jcc ψ) = J (cutmol n ψ)`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal ContDiff Pointwise

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Q

variable {d : ℕ}

lemma sa16y3_mol_integrable (n : ℕ) {g : EuclideanSpace ℝ (Fin d) → ℝ} (hg : IsCcInfty g)
    (x : EuclideanSpace ℝ (Fin d)) :
    Integrable (fun z => sa16y_rho d n z * g (x - z)) volume := by
  have h := hg.2.convolutionExists_right (ContinuousLinearMap.lsmul ℝ ℝ)
    (sa16y_rho_integrable (d := d) n).locallyIntegrable hg.1.continuous
  exact h x

lemma sa16y3_cutmol_add (n : ℕ) {ψ₁ ψ₂ : EuclideanSpace ℝ (Fin d) → ℝ} (h₁ : IsCcInfty ψ₁)
    (h₂ : IsCcInfty ψ₂) :
    sa16y3_cutmol d n (fun y => ψ₁ y + ψ₂ y) = fun x => sa16y3_cutmol d n ψ₁ x + sa16y3_cutmol d n ψ₂ x := by
  funext x
  unfold sa16y3_cutmol sa16q_mol sa16j_conv
  simp only [mul_add]
  rw [← integral_add (sa16y3_mol_integrable n (sa16y3_cut_cc h₁ n) x)
    (sa16y3_mol_integrable n (sa16y3_cut_cc h₂ n) x)]

lemma sa16y3_cutmol_smul (n : ℕ) {ψ : EuclideanSpace ℝ (Fin d) → ℝ} (h : IsCcInfty ψ) (c : ℝ) :
    sa16y3_cutmol d n (fun y => c * ψ y) = fun x => c * sa16y3_cutmol d n ψ x := by
  funext x
  unfold sa16y3_cutmol sa16q_mol sa16j_conv
  have e : ∀ z, sa16y_rho d n z * (sa16y3_cut d n (x - z) * (c * ψ (x - z))) =
      c * (sa16y_rho d n z * (sa16y3_cut d n (x - z) * ψ (x - z))) := fun z => by ring
  simp only [e]
  rw [integral_const_mul]

lemma sa16y3_cutmol_mem {ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hψ : IsCcInfty ψ) (m : ℕ) (p : ℝ)
    [Fact (2 ≤ p)] (n : ℕ) : sa16y3_cutmol d n ψ ∈ sa16r_S d m p := by
  have hc := sa16y3_cutmol_cc hψ n
  refine ⟨hc.1, ?_⟩
  exact ⟨sa16r_Jcc d m p ⟨sa16y3_cutmol d n ψ, hc⟩, by
    rw [sa16r_Jcc_eq]
    exact sa16r_cc_elt_wrep (p := p) hc m⟩

lemma sa16y3_cutmol_S {p : ℝ} [Fact (2 ≤ p)] {ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hψ : IsCcInfty ψ) (m n : ℕ) :
    MemLp (sa16j_S d m (sa16y3_cutmol d n ψ)) (ENNReal.ofReal p) volume := by
  have hc := sa16y3_cutmol_cc hψ n
  exact sa16j_S_memLp m p (hc.2.toSchwartzMap hc.1)

def sa16y3_Lop (m : ℕ) (p : ℝ) [Fact (2 ≤ p)] (n : ℕ) : ccSub d →ₗ[ℝ] sa16r_S d m p where
  toFun ψ := ⟨sa16y3_cutmol d n ψ.1, sa16y3_cutmol_mem ψ.2 m p n⟩
  map_add' ψ₁ ψ₂ := Subtype.ext (sa16y3_cutmol_add n ψ₁.2 ψ₂.2)
  map_smul' c ψ := Subtype.ext (sa16y3_cutmol_smul n ψ.2 c)

lemma sa16y3_norm_wJet_eq {p : ℝ} [Fact (2 ≤ p)] {φ : EuclideanSpace ℝ (Fin d) → ℝ} (hφ : IsCcInfty φ) (k : ℕ) :
    eLpNorm (fun x => ‖wJet k φ x‖) (ENNReal.ofReal p) volume = eLpNorm (wJet k φ) (ENNReal.ofReal p) volume :=
  eLpNorm_norm _ (sa16j_jet_cont hφ.1 k).aestronglyMeasurable

lemma sa16y3_Lop_bound {p : ℝ} [Fact (2 ≤ p)] (hp : 1 ≤ p) (m : ℕ) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ (n : ℕ) {ψ : EuclideanSpace ℝ (Fin d) → ℝ}, IsCcInfty ψ →
      eLpNorm (fun x => ‖wJet m (sa16y3_cutmol d n ψ) x‖) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal C * eLpNorm (fun x => ‖wJet m ψ x‖) (ENNReal.ofReal p) volume)
    (n : ℕ) (ψ : ccSub d) :
    ‖sa16r_J d m p (sa16y3_Lop m p n ψ)‖ ≤ C * ‖sa16r_Jcc d m p ψ‖ := by
  have hS : MemLp (sa16j_S d m (sa16y3_cutmol d n ψ.1)) (ENNReal.ofReal p) volume :=
    sa16y3_cutmol_S (p := p) ψ.2 m n
  have hL : sa16y3_Lop m p n ψ = ⟨sa16y3_cutmol d n ψ.1, sa16y3_cutmol_mem ψ.2 m p n⟩ := rfl
  have hJ' : ‖sa16r_J d m p (sa16y3_Lop m p n ψ)‖ =
      (eLpNorm (fun x => ‖wJet m (sa16y3_cutmol d n ψ.1) x‖) (ENNReal.ofReal p) volume).toReal := by
    rw [hL, sa16r_J_norm (f := ⟨sa16y3_cutmol d n ψ.1, sa16y3_cutmol_mem ψ.2 m p n⟩) m hS,
      sa16y3_norm_wJet_eq (sa16y3_cutmol_cc ψ.2 n) m]
  have hD' : ‖sa16r_Jcc d m p ψ‖ = (eLpNorm (fun x => ‖wJet m ψ.1 x‖) (ENNReal.ofReal p) volume).toReal := by
    rw [sa16r_Jcc_norm d m p ψ, sa16y3_norm_wJet_eq ψ.2 m]
  have hE : eLpNorm (fun x => ‖wJet m ψ.1 x‖) (ENNReal.ofReal p) volume ≠ ⊤ := by
    rw [sa16y3_norm_wJet_eq ψ.2 m]
    exact (sa16r_jet_memLp_cc (p := p) ψ.2 m).eLpNorm_lt_top.ne
  rw [hJ', hD']
  have h2 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hE) (hC n ψ.2)
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC0] at h2
  exact h2


theorem sa16y3_extend_cutmol {p : ℝ} [Fact (2 ≤ p)] (hp : 1 ≤ p) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ∃ T : WmpSpace d m p →L[ℝ] WmpSpace d m p, ‖T‖ ≤ C ∧
      ∀ ψ : ccSub d, T (sa16r_Jcc d m p ψ) = sa16r_J d m p (sa16y3_Lop m p n ψ) := by
  obtain ⟨C, hC0, hC⟩ := sa16y3_cutmol_jet (d := d) hp m
  refine ⟨C, hC0, fun n => ?_⟩
  obtain ⟨T, hT, hTJ, -⟩ := sa16r_extend_cc d m m p (sa16y3_Lop m p n) hC0
    (sa16y3_Lop_bound hp m hC0 hC n)
  exact ⟨T, hT, hTJ⟩

end HRS.Whole.AppendixA.Phase2SA16R
