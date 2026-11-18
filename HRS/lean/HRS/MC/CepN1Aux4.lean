import HRS.MC.CepN1Aux3

/-!
# Packet CEPN1, part 4: the piecewise event `Good`, its deterministic consequence and measurability
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal Real

noncomputable section

namespace HRS.MC.CepN1

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- One-piece condition on a path `z` and target `g`. -/
def cepn1_Piece (h : ℝ≥0) (ε ρ : ℝ) (g : ℝ≥0 → ℝ) (z : ℝ≥0 → ℝ) : Prop :=
  |z h - g h| < ε ∧ ∀ n k : ℕ, k ≤ 2 ^ n → |z (cepn1_dy h n k)| ≤ ρ

/-- The `M`-piece event: pieces of length `h`, successive shifted paths. -/
def cepn1_Good (h : ℝ≥0) (ε ρ : ℝ) : ℕ → (ℝ≥0 → ℝ) → (ℝ≥0 → ℝ) → Prop
  | 0, _, _ => True
  | M + 1, g, z => cepn1_Piece h ε ρ g z ∧
      cepn1_Good h ε ρ M (fun t => g (h + t) - g h) (fun t => z (h + t) - z h)

/-- `g` is `L`-Lipschitz on `[0, M h]`. -/
def cepn1_LipOn (h : ℝ≥0) (L : ℝ) (M : ℕ) (g : ℝ≥0 → ℝ) : Prop :=
  ∀ s t : ℝ≥0, s ≤ M * h → t ≤ M * h → |g s - g t| ≤ L * |(s : ℝ) - t|

theorem cepn1_LipOn_shift {h : ℝ≥0} {L : ℝ} {M : ℕ} {g : ℝ≥0 → ℝ}
    (hg : cepn1_LipOn h L (M + 1) g) : cepn1_LipOn h L M (fun t => g (h + t) - g h) := by
  intro s t hs ht
  have hs' : h + s ≤ ((M + 1 : ℕ) : ℝ≥0) * h := by
    push_cast; rw [add_mul, one_mul, add_comm]; exact add_le_add_left hs h
  have ht' : h + t ≤ ((M + 1 : ℕ) : ℝ≥0) * h := by
    push_cast; rw [add_mul, one_mul, add_comm]; exact add_le_add_left ht h
  have := hg _ _ hs' ht'
  simp only at this ⊢
  have e : |((h + s : ℝ≥0) : ℝ) - ((h + t : ℝ≥0) : ℝ)| = |(s : ℝ) - t| := by
    push_cast; congr 1; ring
  rw [e] at this
  convert this using 2
  ring


/-- Deterministic consequence of `Good`: tracking of `g` by `z` on `[0, M h]`. -/
theorem cepn1_good_bound {h : ℝ≥0} {ε ρ L : ℝ} (hε : 0 ≤ ε) (hρ : 0 ≤ ρ) (hL : 0 ≤ L) :
    ∀ (M : ℕ) (g z : ℝ≥0 → ℝ), g 0 = 0 → cepn1_LipOn h L M g → Continuous z → z 0 = 0 →
      cepn1_Good h ε ρ M g z → ∀ t : ℝ≥0, t ≤ M * h → |z t - g t| ≤ M * ε + ρ + L * h := by
  intro M
  induction M with
  | zero =>
    intro g z hg0 _ _ hz0 _ t ht
    have : t = 0 := by
      simp only [Nat.cast_zero, zero_mul] at ht
      exact le_antisymm ht bot_le
    subst this
    simp only [hz0, hg0, sub_self, abs_zero, Nat.cast_zero, zero_mul, zero_add]
    positivity
  | succ M ih =>
    intro g z hg0 hgL hzc hz0 hgood t ht
    obtain ⟨⟨hp1, hp2⟩, hrest⟩ := hgood
    have hzb : ∀ s : ℝ≥0, s ≤ h → |z s| ≤ ρ := fun s hs => cepn1_dy_dense hzc hp2 s hs
    have hh1 : h ≤ ((M + 1 : ℕ) : ℝ≥0) * h := by
      push_cast; rw [add_mul, one_mul]; exact le_add_of_nonneg_left bot_le
    have hMh : (M : ℝ) * ε ≥ 0 := by positivity
    by_cases hth : t ≤ h
    · have h1 := hzb t hth
      have h2 : |g t| ≤ L * h := by
        have := hgL t 0 (hth.trans hh1) (bot_le) 
        simp only [hg0, sub_zero, NNReal.coe_zero] at this
        refine this.trans ?_
        rw [abs_of_nonneg (NNReal.coe_nonneg t)]
        gcongr
      calc |z t - g t| ≤ |z t| + |g t| := abs_sub _ _
        _ ≤ ρ + L * h := add_le_add h1 h2
        _ ≤ ((M + 1 : ℕ) : ℝ) * ε + ρ + L * h := by
          push_cast; nlinarith
    · have hth : h < t := not_le.1 hth
      obtain ⟨t', rfl⟩ : ∃ t', t = h + t' := ⟨t - h, by rw [add_tsub_cancel_of_le hth.le]⟩
      have ht' : t' ≤ M * h := by
        push_cast at ht; rw [add_mul, one_mul, add_comm] at ht
        exact le_of_add_le_add_right ht
      have hzc' : Continuous (fun t => z (h + t) - z h) := by
        exact (hzc.comp (continuous_const.add continuous_id)).sub continuous_const
      have := ih (fun t => g (h + t) - g h) (fun t => z (h + t) - z h) (by simp)
        (cepn1_LipOn_shift hgL) hzc' (by simp) hrest t' ht'
      have e : z (h + t') - g (h + t') = (z (h + t') - z h - (g (h + t') - g h)) + (z h - g h) := by ring
      rw [e]
      calc _ ≤ |z (h + t') - z h - (g (h + t') - g h)| + |z h - g h| := abs_add_le _ _
        _ ≤ (M * ε + ρ + L * h) + ε := add_le_add this hp1.le
        _ = ((M + 1 : ℕ) : ℝ) * ε + ρ + L * h := by push_cast; ring

end HRS.MC.CepN1
