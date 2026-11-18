import HRS.MC.QRPHdAux10
import HRS.MC.QRPHdAux11
import HRS.MC.QRPHdAux12

/-!
# Packet HD, part 13: the Hilbert-Schmidt tail of the Wick matrix from the out-of-band sums
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped BigOperators ComplexConjugate

namespace HRS.MC.QRSpec.Hd

open HRS

variable {d : ℕ} {s : ℝ}

open Classical in
theorem hd_W_reindex (κ : Lattice d) (Q : Lattice d → Prop) (hQ : ∀ (σ : Bool) (x : Lattice d), Q (hdsg σ • x) ↔ Q x)
    (σ ε τ : Bool) (c : Lattice d) :
    (if Q c ∧ Q (hdφ κ σ ε τ c) then (0 : ℝ) else hdw d s κ σ ε c) =
      ((fun α => (4 * Real.pi ^ 2 * Lattice.enorm κ) ^ 2 * hdOut d s (hdsg ε • κ) Q α) ∘ hdE d σ) c := by
  classical
  have hneg : ∀ y, Q (-y) ↔ Q y := by
    intro y
    have := hQ false y
    simpa [hdsg] using this
  have h1 : Q (hdsg σ • c) ↔ Q c := hQ σ c
  have h2 : Q (hdφ κ σ ε τ c) ↔ Q (hdsg σ • c + hdsg ε • κ) := by
    unfold hdφ
    rw [hneg, hQ]
  simp only [Function.comp, hdOut, hdw]
  show _ = (4 * Real.pi ^ 2 * Lattice.enorm κ) ^ 2 *
    (if Q (hdsg σ • c) ∧ Q (hdsg σ • c + hdsg ε • κ) then 0 else hdD d s (hdsg ε • κ) (hdsg σ • c) ^ 2)
  by_cases hq : Q c ∧ Q (hdφ κ σ ε τ c)
  · have : Q (hdsg σ • c) ∧ Q (hdsg σ • c + hdsg ε • κ) := ⟨h1.mpr hq.1, h2.mp hq.2⟩
    rw [if_pos hq, if_pos this]; ring
  · have : ¬ (Q (hdsg σ • c) ∧ Q (hdsg σ • c + hdsg ε • κ)) := fun h => hq ⟨h1.mp h.1, h2.mpr h.2⟩
    rw [if_neg hq, if_neg this]

open Classical in
theorem hd_W_N (κ : Lattice d) (Q : Lattice d → Prop)
    (hQ : ∀ (σ : Bool) (x : Lattice d), Q (hdsg σ • x) ↔ Q x) (σ ε τ : Bool) {B : ℝ}
    (hB : Summable (hdOut d s (hdsg ε • κ) Q) ∧ ∑' α, hdOut d s (hdsg ε • κ) Q α ≤ B) :
    Summable (fun a : NonzeroLattice d => if Q a.1 ∧ Q (hdφ κ σ ε τ a.1) then (0 : ℝ) else hdw d s κ σ ε a.1) ∧
    ∑' a : NonzeroLattice d, (if Q a.1 ∧ Q (hdφ κ σ ε τ a.1) then (0 : ℝ) else hdw d s κ σ ε a.1) ≤
      (4 * Real.pi ^ 2 * Lattice.enorm κ) ^ 2 * B := by
  classical
  set K2 := (4 * Real.pi ^ 2 * Lattice.enorm κ) ^ 2 with hK2
  set Wf : Lattice d → ℝ := fun c => if Q c ∧ Q (hdφ κ σ ε τ c) then (0 : ℝ) else hdw d s κ σ ε c with hWf
  have hWe : Wf = (fun α => K2 * hdOut d s (hdsg ε • κ) Q α) ∘ hdE d σ := by
    funext c; exact hd_W_reindex κ Q hQ σ ε τ c
  have hsumF : Summable Wf := by
    rw [hWe]; exact (hdE d σ).summable_iff.mpr (hB.1.mul_left K2)
  have htsumF : ∑' c, Wf c = K2 * ∑' α, hdOut d s (hdsg ε • κ) Q α := by
    have := (hdE d σ).tsum_eq (fun α => K2 * hdOut d s (hdsg ε • κ) Q α)
    rw [hWe]
    simp only [Function.comp]
    rw [this, tsum_mul_left]
  have hnn : ∀ c, 0 ≤ Wf c := by
    intro c
    rw [show Wf c = _ from congrFun hWe c]
    exact mul_nonneg (sq_nonneg _) (hdOut_nonneg _ _ _)
  refine ⟨hsumF.subtype _, ?_⟩
  have hle := Summable.tsum_subtype_le Wf {k : Lattice d | k ≠ 0} hnn hsumF
  calc ∑' a : NonzeroLattice d, Wf a.1 ≤ ∑' c, Wf c := hle
    _ = K2 * ∑' α, hdOut d s (hdsg ε • κ) Q α := htsumF
    _ ≤ K2 * B := mul_le_mul_of_nonneg_left hB.2 (sq_nonneg _)

open Classical in
theorem hd_tail_gen (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs1 : s + 1 < d) {ρ : Torus d → ℝ} {Λ : ℝ}
    (hΛ : ∀ x, ρ x ≤ Λ) (κ : NonzeroLattice d) (Q : Lattice d → Prop)
    (hQ : ∀ (σ : Bool) (x : Lattice d), Q (hdsg σ • x) ↔ Q x) (F : Finset (NonzeroLattice d))
    (hF : ∀ a : NonzeroLattice d, Q a.1 → a ∈ F) {B : ℝ}
    (hB : ∀ ε : Bool, Summable (hdOut d s (hdsg ε • κ.1) Q) ∧ ∑' α, hdOut d s (hdsg ε • κ.1) Q α ≤ B) :
    Summable (fun p : NonzeroLattice d × NonzeroLattice d => if p.1 ∈ F ∧ p.2 ∈ F then (0 : ℝ) else
      (Sec7.wickCoeff (withDensityReal ρ) (hTransport d s (Torus.realMode κ)) p.1 p.2) ^ 2) ∧
    ∑' p : NonzeroLattice d × NonzeroLattice d, (if p.1 ∈ F ∧ p.2 ∈ F then (0 : ℝ) else
      (Sec7.wickCoeff (withDensityReal ρ) (hTransport d s (Torus.realMode κ)) p.1 p.2) ^ 2) ≤
      64 * (4 * Real.pi ^ 2 * Lattice.enorm κ.1) ^ 2 * B := by
  classical
  set A : NonzeroLattice d → NonzeroLattice d → ℝ :=
    Sec7.wickCoeff (withDensityReal ρ) (hTransport d s (Torus.realMode κ)) with hA
  set K2 := (4 * Real.pi ^ 2 * Lattice.enorm κ.1) ^ 2 with hK2
  set H : Bool → Bool → Bool → NonzeroLattice d × NonzeroLattice d → ℝ := fun σ ε τ p =>
    if p.1 ∈ F ∧ p.2 ∈ F then (0 : ℝ) else
      if p.2.1 = hdφ κ.1 σ ε τ p.1.1 then hdw d s κ.1 σ ε p.1.1 else 0 with hH
  have hHs : ∀ σ ε τ, Summable (H σ ε τ) ∧ ∑' p, H σ ε τ p ≤ K2 * B := by
    intro σ ε τ
    obtain ⟨hWs, hWt⟩ := hd_W_N κ.1 Q hQ σ ε τ (hB ε)
    have hw0 : ∀ c, 0 ≤ hdw d s κ.1 σ ε c := fun c => mul_nonneg (sq_nonneg _) (sq_nonneg _)
    obtain ⟨h1, h2⟩ := hd_pair_sum (hdφ κ.1 σ ε τ) (hdw d s κ.1 σ ε) hw0 Q F hF hWs
    exact ⟨h1, h2.trans hWt⟩
  have hHn : ∀ σ ε τ p, 0 ≤ H σ ε τ p := by
    intro σ ε τ p
    simp only [hH]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
    · exact le_rfl
  set R : NonzeroLattice d × NonzeroLattice d → ℝ := fun p => 8 * ∑ σ : Bool, ∑ ε : Bool, ∑ τ : Bool, H σ ε τ p with hR
  have hRs : Summable R := by
    refine Summable.mul_left _ ?_
    exact summable_sum fun σ _ => summable_sum fun ε _ => summable_sum fun τ _ => (hHs σ ε τ).1
  have hpt : ∀ p : NonzeroLattice d × NonzeroLattice d,
      (if p.1 ∈ F ∧ p.2 ∈ F then (0 : ℝ) else A p.1 p.2 ^ 2) ≤ R p := by
    intro p
    have hRn : 0 ≤ R p := by
      simp only [hR]
      exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun σ _ => Finset.sum_nonneg fun ε _ =>
        Finset.sum_nonneg fun τ _ => hHn σ ε τ p)
    by_cases hFF : p.1 ∈ F ∧ p.2 ∈ F
    · rw [if_pos hFF]; exact hRn
    · rw [if_neg hFF]
      have := hd_A_sq_le hd hs0 hs1 hΛ κ p.1 p.2
      refine this.trans (le_of_eq ?_)
      simp only [hR, hH, if_neg hFF]
  have hnn : ∀ p : NonzeroLattice d × NonzeroLattice d, 0 ≤ (if p.1 ∈ F ∧ p.2 ∈ F then (0 : ℝ) else A p.1 p.2 ^ 2) := by
    intro p; split_ifs
    · exact le_rfl
    · exact sq_nonneg _
  have hsm := Summable.of_nonneg_of_le hnn hpt hRs
  refine ⟨hsm, ?_⟩
  have hts : ∑' p, R p = 8 * ∑ σ : Bool, ∑ ε : Bool, ∑ τ : Bool, ∑' p, H σ ε τ p := by
    simp only [hR]
    rw [tsum_mul_left]
    congr 1
    rw [Summable.tsum_finsetSum fun σ _ => summable_sum fun ε _ => summable_sum fun τ _ => (hHs σ ε τ).1]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Summable.tsum_finsetSum fun ε _ => summable_sum fun τ _ => (hHs σ ε τ).1]
    refine Finset.sum_congr rfl fun ε _ => ?_
    rw [Summable.tsum_finsetSum fun τ _ => (hHs σ ε τ).1]
  calc _ ≤ ∑' p, R p := Summable.tsum_le_tsum hpt hsm hRs
    _ = _ := hts
    _ ≤ 8 * ∑ σ : Bool, ∑ ε : Bool, ∑ τ : Bool, K2 * B := by
        gcongr with σ _ ε _ τ _
        exact (hHs σ ε τ).2
    _ = 64 * K2 * B := by
        simp [Finset.sum_const]; ring

end HRS.MC.QRSpec.Hd

end
