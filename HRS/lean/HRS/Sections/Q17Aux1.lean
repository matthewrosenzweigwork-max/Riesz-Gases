import HRS.Sections.Sec7Fields

/-!
# Q17 auxiliary: Riemann--Stieltjes refinement estimate (for `measure_projection`)

Cell lists `(left, right, tag)`; RS sum `q17_sum`; admissibility `q17_P`; head-splitting
lemma `q17_head` and the refinement estimate `q17_rl`, which compares two admissible cell
lists with the same endpoints, given a modulus of continuity of the integrand and a
superadditive budget `W` dominating the increments of `G`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HRS.Sec7

section Q17RS

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Riemann--Stieltjes sum over a list of cells `(left, right, tag)`. -/
def q17_sum (B : ℝ → (E →L[ℝ] ℝ)) (G : ℝ → E) : List (ℝ × ℝ × ℝ) → ℝ
  | [] => 0
  | c :: cs => B c.2.2 (G c.2.1 - G c.1) + q17_sum B G cs

/-- Admissible cell lists from `a` to `b`: consecutive cells, lengths `≤ δ`, tags in `[0,T]`
within `δ` of every point of their cell. -/
def q17_P (T δ : ℝ) : List (ℝ × ℝ × ℝ) → ℝ → ℝ → Prop
  | [], a, b => a = b
  | c :: cs, a, b => c.1 = a ∧ a ≤ c.2.1 ∧ c.2.1 - c.1 ≤ δ ∧ 0 ≤ c.2.2 ∧ c.2.2 ≤ T ∧
      (∀ z, c.1 ≤ z → z ≤ c.2.1 → |c.2.2 - z| ≤ δ) ∧ q17_P T δ cs c.2.1 b

theorem q17_P_nil (T δ a b : ℝ) : q17_P T δ [] a b ↔ a = b := Iff.rfl

theorem q17_P_cons (T δ x y τ a b : ℝ) (cs : List (ℝ × ℝ × ℝ)) :
    q17_P T δ ((x, y, τ) :: cs) a b ↔
      (x = a ∧ a ≤ y ∧ y - x ≤ δ ∧ 0 ≤ τ ∧ τ ≤ T ∧
        (∀ z, x ≤ z → z ≤ y → |τ - z| ≤ δ) ∧ q17_P T δ cs y b) := Iff.rfl

theorem q17_P_le (T δ : ℝ) : ∀ (cs : List (ℝ × ℝ × ℝ)) (a b : ℝ), q17_P T δ cs a b → a ≤ b
  | [], a, b, h => ((q17_P_nil T δ a b).1 h).le
  | c :: cs, a, b, h => by
    obtain ⟨_, h2, _, _, _, _, h7⟩ := (q17_P_cons T δ c.1 c.2.1 c.2.2 a b cs).1 h
    exact le_trans h2 (q17_P_le T δ cs _ b h7)

theorem q17_sum_degenerate (B : ℝ → (E →L[ℝ] ℝ)) (G : ℝ → E) (T δ a : ℝ) :
    ∀ (cs : List (ℝ × ℝ × ℝ)), q17_P T δ cs a a → q17_sum B G cs = 0
  | [], _ => rfl
  | (x, y, τ) :: cs, h => by
    obtain ⟨h1, h2, _, _, _, _, h7⟩ := (q17_P_cons T δ x y τ a a cs).1 h
    have hle := q17_P_le T δ cs _ _ h7
    have h8 : y = a := le_antisymm hle h2
    have hG : G y - G x = 0 := by rw [h8, h1]; exact sub_self _
    have h9 : q17_P T δ cs a a := by rw [h8] at h7; exact h7
    have ih := q17_sum_degenerate B G T δ a cs h9
    simp only [q17_sum]
    rw [hG, map_zero, ih, zero_add]

theorem q17_sum_split (B : ℝ → (E →L[ℝ] ℝ)) (G : ℝ → E) (a y y' σ : ℝ) (ds : List (ℝ × ℝ × ℝ))
    (hy' : y ≤ y') :
    q17_sum B G ((a, y, σ) :: (y, y', σ) :: ds) = q17_sum B G ((a, y', σ) :: ds) := by
  simp only [q17_sum]
  rw [← add_assoc, ← map_add]
  congr 2
  abel

/-- Head lemma: two admissible lists starting with cells on the same `[a,y]`, with tails
satisfying the bound on `[y,b]`, give the bound on `[a,b]`. -/
theorem q17_head (B : ℝ → (E →L[ℝ] ℝ)) (G : ℝ → E) (W : ℝ → ℝ → ℝ) (T δ c : ℝ)
    (hW0 : ∀ x y, 0 ≤ x → x ≤ y → y ≤ T → ‖G y - G x‖ ≤ W x y)
    (hWadd : ∀ x u y, 0 ≤ x → x ≤ u → u ≤ y → y ≤ T → W x u + W u y ≤ W x y)
    (hc : 0 ≤ c)
    (hB : ∀ s t, 0 ≤ s → s ≤ T → 0 ≤ t → t ≤ T → |s - t| ≤ 2 * δ → ‖B s - B t‖ ≤ c)
    (a y b τ σ : ℝ) (P Q : List (ℝ × ℝ × ℝ))
    (ha : 0 ≤ a) (hay : a ≤ y) (hyb : y ≤ b) (hb : b ≤ T)
    (hτ0 : 0 ≤ τ) (hτT : τ ≤ T) (hσ0 : 0 ≤ σ) (hσT : σ ≤ T)
    (hτa : |τ - a| ≤ δ) (hσa : |σ - a| ≤ δ)
    (hPQ : ‖q17_sum B G P - q17_sum B G Q‖ ≤ c * W y b) :
    ‖q17_sum B G ((a, y, τ) :: P) - q17_sum B G ((a, y, σ) :: Q)‖ ≤ c * W a b := by
  have hτσ : ‖B τ - B σ‖ ≤ c := by
    refine hB τ σ hτ0 hτT hσ0 hσT ?_
    have h1 := abs_sub_le τ a σ
    rw [abs_sub_comm a σ] at h1
    linarith
  have hGa : ‖G y - G a‖ ≤ W a y := hW0 a y ha hay (le_trans hyb hb)
  have hW := hWadd a y b ha hay hyb hb
  have e : q17_sum B G ((a, y, τ) :: P) - q17_sum B G ((a, y, σ) :: Q)
      = (B τ - B σ) (G y - G a) + (q17_sum B G P - q17_sum B G Q) := by
    simp only [q17_sum, ContinuousLinearMap.sub_apply]
    abel
  rw [e]
  have h1 : ‖(B τ - B σ) (G y - G a)‖ ≤ c * W a y := by
    refine le_trans (ContinuousLinearMap.le_opNorm _ _) ?_
    refine le_trans (mul_le_mul_of_nonneg_right hτσ (norm_nonneg _)) ?_
    exact mul_le_mul_of_nonneg_left hGa hc
  calc ‖(B τ - B σ) (G y - G a) + (q17_sum B G P - q17_sum B G Q)‖
      ≤ ‖(B τ - B σ) (G y - G a)‖ + ‖q17_sum B G P - q17_sum B G Q‖ := norm_add_le _ _
    _ ≤ c * W a y + c * W y b := add_le_add h1 hPQ
    _ = c * (W a y + W y b) := by ring
    _ ≤ c * W a b := mul_le_mul_of_nonneg_left hW hc

/-- Refinement estimate: two admissible cell lists from `a` to `b` (with `0 ≤ a`, `b ≤ T`) have
RS sums differing by at most `c * W a b`. -/
theorem q17_rl (B : ℝ → (E →L[ℝ] ℝ)) (G : ℝ → E) (W : ℝ → ℝ → ℝ) (T δ c : ℝ)
    (hW0 : ∀ x y, 0 ≤ x → x ≤ y → y ≤ T → ‖G y - G x‖ ≤ W x y)
    (hWadd : ∀ x u y, 0 ≤ x → x ≤ u → u ≤ y → y ≤ T → W x u + W u y ≤ W x y)
    (hc : 0 ≤ c)
    (hB : ∀ s t, 0 ≤ s → s ≤ T → 0 ≤ t → t ≤ T → |s - t| ≤ 2 * δ → ‖B s - B t‖ ≤ c) :
    ∀ (N : ℕ) (cs ds : List (ℝ × ℝ × ℝ)) (a b : ℝ), cs.length + ds.length ≤ N →
      0 ≤ a → b ≤ T → q17_P T δ cs a b → q17_P T δ ds a b →
      ‖q17_sum B G cs - q17_sum B G ds‖ ≤ c * W a b := by
  have hWnn : ∀ x y, 0 ≤ x → x ≤ y → y ≤ T → 0 ≤ W x y := fun x y hx hxy hy =>
    le_trans (norm_nonneg _) (hW0 x y hx hxy hy)
  intro N
  induction N with
  | zero =>
    intro cs ds a b hlen ha hb hcs hds
    have hcs0 : cs = [] := List.length_eq_zero_iff.mp (by omega)
    have hds0 : ds = [] := List.length_eq_zero_iff.mp (by omega)
    subst hcs0 hds0
    have hab : a = b := (q17_P_nil T δ a b).1 hcs
    rw [← hab] at hb ⊢
    simp only [q17_sum, sub_self, norm_zero]
    exact mul_nonneg hc (hWnn a a ha le_rfl hb)
  | succ N ih =>
    intro cs ds a b hlen ha hb hcs hds
    rcases cs with _ | ⟨⟨x, y, τ⟩, cs'⟩
    · -- `cs = []`: then `a = b` and `ds` is degenerate
      have hab : a = b := (q17_P_nil T δ a b).1 hcs
      rw [← hab] at hds hb ⊢
      rw [q17_sum_degenerate B G T δ a ds hds]
      have hn : q17_sum B G [] = 0 := rfl
      simp only [hn, sub_zero, norm_zero]
      exact mul_nonneg hc (hWnn a a ha le_rfl hb)
    rcases ds with _ | ⟨⟨x', y', σ⟩, ds'⟩
    · -- `ds = []` (and `cs` nonempty): symmetric degenerate case
      have hab : a = b := (q17_P_nil T δ a b).1 hds
      rw [← hab] at hcs hb ⊢
      rw [q17_sum_degenerate B G T δ a _ hcs]
      have hn : q17_sum B G [] = 0 := rfl
      simp only [hn, sub_zero, norm_zero]
      exact mul_nonneg hc (hWnn a a ha le_rfl hb)
    -- both nonempty
    obtain ⟨hx, hay, hlen1, hτ0, hτT, hτbd, hcs'⟩ := (q17_P_cons T δ x y τ a b cs').1 hcs
    obtain ⟨hx', hay', hlen2, hσ0, hσT, hσbd, hds'⟩ := (q17_P_cons T δ x' y' σ a b ds').1 hds
    subst x
    subst x'
    have hτa : |τ - a| ≤ δ := hτbd a le_rfl hay
    have hσa : |σ - a| ≤ δ := hσbd a le_rfl hay'
    have hyb : y ≤ b := q17_P_le T δ cs' y b hcs'
    have hy'b : y' ≤ b := q17_P_le T δ ds' y' b hds'
    rcases lt_trichotomy y y' with h | h | h
    · -- `y < y'`: split the second head cell `[a,y']` at `y`
      have htail : q17_P T δ ((y, y', σ) :: ds') y b :=
        (q17_P_cons T δ y y' σ y b ds').2 ⟨rfl, h.le, by linarith, hσ0, hσT,
          fun z hz1 hz2 => hσbd z (le_trans hay hz1) hz2, hds'⟩
      have hsplit : q17_P T δ ((a, y, σ) :: (y, y', σ) :: ds') a b :=
        (q17_P_cons T δ a y σ a b _).2 ⟨rfl, hay, by linarith, hσ0, hσT,
          fun z hz1 hz2 => hσbd z hz1 (le_trans hz2 h.le), htail⟩
      have hIH := ih cs' ((y, y', σ) :: ds') y b
        (by simp only [List.length_cons] at hlen ⊢; omega) (le_trans ha hay) hb hcs' htail
      have hA := q17_head B G W T δ c hW0 hWadd hc hB a y b τ σ cs' ((y, y', σ) :: ds')
        ha hay hyb hb hτ0 hτT hσ0 hσT hτa hσa hIH
      rw [← q17_sum_split B G a y y' σ ds' h.le]
      exact hA
    · -- `y = y'`: the two head cells coincide
      subst h
      have hIH := ih cs' ds' y b (by simp only [List.length_cons] at hlen ⊢; omega)
        (le_trans ha hay) hb hcs' hds'
      exact q17_head B G W T δ c hW0 hWadd hc hB a y b τ σ cs' ds'
        ha hay hyb hb hτ0 hτT hσ0 hσT hτa hσa hIH
    · -- `y' < y`: split the first head cell `[a,y]` at `y'`
      have htail : q17_P T δ ((y', y, τ) :: cs') y' b :=
        (q17_P_cons T δ y' y τ y' b cs').2 ⟨rfl, h.le, by linarith, hτ0, hτT,
          fun z hz1 hz2 => hτbd z (le_trans hay' hz1) hz2, hcs'⟩
      have hsplit : q17_P T δ ((a, y', τ) :: (y', y, τ) :: cs') a b :=
        (q17_P_cons T δ a y' τ a b _).2 ⟨rfl, hay', by linarith, hτ0, hτT,
          fun z hz1 hz2 => hτbd z hz1 (le_trans hz2 h.le), htail⟩
      have hIH := ih ((y', y, τ) :: cs') ds' y' b
        (by simp only [List.length_cons] at hlen ⊢; omega) (le_trans ha hay') hb htail hds'
      have hA := q17_head B G W T δ c hW0 hWadd hc hB a y' b τ σ ((y', y, τ) :: cs') ds'
        ha hay' hy'b hb hτ0 hτT hσ0 hσT hτa hσa hIH
      rw [← q17_sum_split B G a y' y τ cs' h.le]
      exact hA

end Q17RS

end HRS.Sec7
