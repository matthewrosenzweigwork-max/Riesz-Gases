import HRS.MC.QRPHdAux8
import HRS.MC.QRPHdAux9

/-!
# Packet HD, part 12: the "outside the cube" sums of `D(α,λ)²` and reindexing
-/

noncomputable section

open Finset
open scoped BigOperators

namespace HRS.MC.QRSpec.Hd

open HRS

variable {d : ℕ} {s : ℝ}

theorem hdD_symm (s : ℝ) (lam α : Lattice d) : hdD d s lam (-α - lam) = hdD d s lam α := by
  unfold hdD
  have h1 : -α - lam + lam = -α := by abel
  have h2 : -α - lam = -(α + lam) := by abel
  rw [h1, h2, hdq_neg, hdq_neg, neg_sub_neg]

/-- The involution `c ↦ ±c`. -/
def hdE (d : ℕ) (σ : Bool) : Lattice d ≃ Lattice d where
  toFun c := hdsg σ • c
  invFun c := hdsg σ • c
  left_inv c := hdsg_smul_smul σ c
  right_inv c := hdsg_smul_smul σ c

/-- The involution `α ↦ -α - λ`. -/
def hdR (lam : Lattice d) : Lattice d ≃ Lattice d where
  toFun α := -α - lam
  invFun α := -α - lam
  left_inv α := by simp
  right_inv α := by simp

/-- The cube predicate `{|c|_∞ ≤ L}`. -/
def hdCu (L : ℕ) (c : Lattice d) : Prop := ∀ i, |c i| ≤ (L : ℤ)

theorem hdCu_neg (L : ℕ) (c : Lattice d) : hdCu L (-c) ↔ hdCu L c := by
  simp [hdCu]

theorem hdCu_smul (L : ℕ) (σ : Bool) (c : Lattice d) : hdCu L (hdsg σ • c) ↔ hdCu L c := by
  cases σ
  · simp only [hdsg, Bool.false_eq_true, ite_false, neg_smul, one_smul]; exact hdCu_neg L c
  · simp [hdsg]

theorem hdS1_out {lam : Lattice d} {L : ℕ} {α : Lattice d} (h : ¬ hdCu L α) :
    hdS1 d s lam L α = hdD d s lam α ^ 2 := by
  unfold hdS1; exact if_neg h

open Classical in
/-- `D²` outside the "band" `Q α ∧ Q (α+λ)`. -/
def hdOut (d : ℕ) (s : ℝ) (lam : Lattice d) (Q : Lattice d → Prop) (α : Lattice d) : ℝ :=
  if Q α ∧ Q (α + lam) then 0 else hdD d s lam α ^ 2

theorem hdOut_nonneg (lam : Lattice d) (Q : Lattice d → Prop) (α : Lattice d) :
    0 ≤ hdOut d s lam Q α := by
  unfold hdOut; split_ifs
  · exact le_rfl
  · exact sq_nonneg _

theorem hdOut_le_D (lam : Lattice d) (Q : Lattice d → Prop) (α : Lattice d) :
    hdOut d s lam Q α ≤ hdD d s lam α ^ 2 := by
  unfold hdOut; split_ifs
  · exact sq_nonneg _
  · exact le_rfl

open Classical in
theorem hdOut_le_S1 (lam : Lattice d) (L : ℕ) (α : Lattice d) :
    hdOut d s lam (hdCu L) α ≤ hdS1 d s lam L α + hdS1 d s lam L (hdR lam α) := by
  have h0 := hdS1_nonneg (s := s) lam L α
  have h0' := hdS1_nonneg (s := s) lam L (hdR lam α)
  unfold hdOut
  by_cases hQ : hdCu L α ∧ hdCu L (α + lam)
  · rw [if_pos hQ]; linarith
  · rw [if_neg hQ]
    by_cases h1 : hdCu L α
    · have h2 : ¬ hdCu L (α + lam) := fun h2 => hQ ⟨h1, h2⟩
      have h3 : ¬ hdCu L (hdR lam α) := by
        intro h
        apply h2
        have : hdR lam α = -(α + lam) := by simp [hdR]; abel
        rw [this, hdCu_neg] at h
        exact h
      have e : hdS1 d s lam L (hdR lam α) = hdD d s lam α ^ 2 := by
        rw [hdS1_out h3]
        show hdD d s lam (-α - lam) ^ 2 = _
        rw [hdD_symm]
      linarith
    · have e : hdS1 d s lam L α = hdD d s lam α ^ 2 := by
        exact hdS1_out h1
      linarith

theorem hdOut_tsum (lam : Lattice d) (L : ℕ) (hS : Summable (hdS1 d s lam L)) :
    Summable (hdOut d s lam (hdCu L)) ∧
      ∑' α, hdOut d s lam (hdCu L) α ≤ 2 * ∑' α, hdS1 d s lam L α := by
  have hS2 : Summable (hdS1 d s lam L ∘ hdR lam) := (hdR lam).summable_iff.mpr hS
  have hsum := hS.add hS2
  have hsm : Summable (hdOut d s lam (hdCu L)) :=
    Summable.of_nonneg_of_le (hdOut_nonneg lam _) (hdOut_le_S1 lam L) hsum
  refine ⟨hsm, ?_⟩
  calc ∑' α, hdOut d s lam (hdCu L) α ≤ ∑' α, (hdS1 d s lam L α + hdS1 d s lam L (hdR lam α)) :=
        Summable.tsum_le_tsum (hdOut_le_S1 lam L) hsm hsum
    _ = ∑' α, hdS1 d s lam L α + ∑' α, hdS1 d s lam L (hdR lam α) := hS.tsum_add hS2
    _ = 2 * ∑' α, hdS1 d s lam L α := by
        rw [(hdR lam).tsum_eq (hdS1 d s lam L)]; ring

/-- Combined bound: for every `L ≥ 1`. -/
theorem hd_outBound (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : 2 * s < d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ lam : Lattice d, lam ≠ 0 → ∀ L : ℕ, 1 ≤ L →
      Summable (hdOut d s lam (hdCu L)) ∧
      ∑' α, hdOut d s lam (hdCu L) α ≤ C * Lattice.enorm lam ^ ((d : ℝ) + 1) * (L : ℝ) ^ (-((d : ℝ) - 2 * s)) := by
  obtain ⟨CA, hCA0, hA⟩ := hd_tailA hd hs0 hsd
  obtain ⟨CB, hCB0, hB⟩ := hd_totalB hd hs0 hsd
  have hp : 0 < (d : ℝ) - 2 * s := by linarith
  refine ⟨2 * CA + CB * 2 ^ ((d : ℝ) - 2 * s), by positivity, fun lam hlam L hL => ?_⟩
  set el := Lattice.enorm lam with hel
  have hel1 : 1 ≤ el := hd_enorm_ge_one hlam
  have hel0 : 0 < el := by linarith
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hL0 : (0 : ℝ) < L := by linarith
  have hLp : 0 ≤ (L : ℝ) ^ (-((d : ℝ) - 2 * s)) := Real.rpow_nonneg hL0.le _
  by_cases hcase : 2 * el ≤ L
  · obtain ⟨hs1, ht1⟩ := hA lam hlam L hL hcase
    obtain ⟨hs2, ht2⟩ := hdOut_tsum lam L hs1
    refine ⟨hs2, ht2.trans ?_⟩
    have h3 : el ^ 2 ≤ el ^ ((d : ℝ) + 1) := by
      have : (2 : ℝ) = ((2 : ℕ) : ℝ) := by norm_num
      rw [show el ^ 2 = el ^ ((2 : ℕ) : ℝ) by rw [Real.rpow_natCast]]
      exact Real.rpow_le_rpow_of_exponent_le hel1 (by have : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
                                                      push_cast; linarith)
    have h4 : CA * el ^ 2 * (L : ℝ) ^ (-((d : ℝ) - 2 * s)) ≤ CA * el ^ ((d : ℝ) + 1) * (L : ℝ) ^ (-((d : ℝ) - 2 * s)) := by
      gcongr
    have h5 : 0 ≤ CB * 2 ^ ((d : ℝ) - 2 * s) * el ^ ((d : ℝ) + 1) * (L : ℝ) ^ (-((d : ℝ) - 2 * s)) := by positivity
    have h6 : (2 * CA + CB * 2 ^ ((d : ℝ) - 2 * s)) * el ^ ((d : ℝ) + 1) * (L : ℝ) ^ (-((d : ℝ) - 2 * s)) =
        2 * (CA * el ^ ((d : ℝ) + 1) * (L : ℝ) ^ (-((d : ℝ) - 2 * s))) +
          CB * 2 ^ ((d : ℝ) - 2 * s) * el ^ ((d : ℝ) + 1) * (L : ℝ) ^ (-((d : ℝ) - 2 * s)) := by ring
    rw [h6]
    linarith
  · push Not at hcase
    obtain ⟨hsB, htB⟩ := hB lam hlam
    have hsm : Summable (hdOut d s lam (hdCu L)) :=
      Summable.of_nonneg_of_le (hdOut_nonneg lam _) (hdOut_le_D lam _) hsB
    refine ⟨hsm, ?_⟩
    calc ∑' α, hdOut d s lam (hdCu L) α ≤ ∑' α, hdD d s lam α ^ 2 :=
          Summable.tsum_le_tsum (hdOut_le_D lam _) hsm hsB
      _ ≤ CB * el ^ (1 + 2 * s) := htB
      _ ≤ CB * (2 ^ ((d : ℝ) - 2 * s) * el ^ ((d : ℝ) + 1) * (L : ℝ) ^ (-((d : ℝ) - 2 * s))) := by
          refine mul_le_mul_of_nonneg_left ?_ hCB0
          have e1 : el ^ (1 + 2 * s) = el ^ ((d : ℝ) + 1) * el ^ (-((d : ℝ) - 2 * s)) := by
            rw [← Real.rpow_add hel0]; congr 1; ring
          have e2 : el ^ (-((d : ℝ) - 2 * s)) ≤ (L / 2 : ℝ) ^ (-((d : ℝ) - 2 * s)) :=
            Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
          have e3 : (L / 2 : ℝ) ^ (-((d : ℝ) - 2 * s)) = 2 ^ ((d : ℝ) - 2 * s) * (L : ℝ) ^ (-((d : ℝ) - 2 * s)) := by
            rw [Real.div_rpow hL0.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
            field_simp
          rw [e1]
          have hp0 : 0 ≤ el ^ ((d : ℝ) + 1) := Real.rpow_nonneg hel0.le _
          calc el ^ ((d : ℝ) + 1) * el ^ (-((d : ℝ) - 2 * s)) ≤ el ^ ((d : ℝ) + 1) * (2 ^ ((d : ℝ) - 2 * s) * (L : ℝ) ^ (-((d : ℝ) - 2 * s))) := by
                rw [← e3]; exact mul_le_mul_of_nonneg_left e2 hp0
            _ = _ := by ring
      _ ≤ _ := by
          have h5 : 0 ≤ 2 * CA * el ^ ((d : ℝ) + 1) * (L : ℝ) ^ (-((d : ℝ) - 2 * s)) := by positivity
          have h6 : (2 * CA + CB * 2 ^ ((d : ℝ) - 2 * s)) * el ^ ((d : ℝ) + 1) * (L : ℝ) ^ (-((d : ℝ) - 2 * s)) =
              2 * CA * el ^ ((d : ℝ) + 1) * (L : ℝ) ^ (-((d : ℝ) - 2 * s)) +
                CB * (2 ^ ((d : ℝ) - 2 * s) * el ^ ((d : ℝ) + 1) * (L : ℝ) ^ (-((d : ℝ) - 2 * s))) := by ring
          rw [h6]
          linarith

end HRS.MC.QRSpec.Hd

end
