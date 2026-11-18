import HRS.MS.SA12K3

/-!
# S.A.12 C1, from convergence along diagonals to uniform convergence in the time parameter

If `G L τ x → G∞ τ* x` uniformly in `x ∈ K` whenever `τ = τ̂(L) → τ*` (any function `τ̂`), then
`G L τ x - G∞ τ x → 0` uniformly in `τ ∈ [0,T]`, `x ∈ K`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Construction

open HRS

/-- The diagonal function: `τ n` on the points `a n`, and `τ'` elsewhere. -/
def sa12k_diag (a : ℕ → ℝ) (τ : ℕ → ℝ) (τ' : ℝ) (L : ℝ) : ℝ :=
  open Classical in if h : ∃ n, a n = L then τ (Classical.choose h) else τ'

theorem sa12k_diag_apply {a : ℕ → ℝ} (ha : StrictMono a) (τ : ℕ → ℝ) (τ' : ℝ) (n : ℕ) :
    sa12k_diag a τ τ' (a n) = τ n := by
  unfold sa12k_diag
  have h : ∃ k, a k = a n := ⟨n, rfl⟩
  rw [dif_pos h]
  have := Classical.choose_spec h
  rw [ha.injective this]

theorem sa12k_diag_mem {a : ℕ → ℝ} {τ : ℕ → ℝ} {τ' : ℝ} {S : Set ℝ} (hτ : ∀ n, τ n ∈ S)
    (hτ' : τ' ∈ S) (L : ℝ) : sa12k_diag a τ τ' L ∈ S := by
  unfold sa12k_diag
  split_ifs with h
  · exact hτ _
  · exact hτ'

theorem sa12k_diag_tendsto {a : ℕ → ℝ} (ha : StrictMono a) {τ : ℕ → ℝ} {τ' : ℝ}
    (ht : Tendsto τ atTop (𝓝 τ')) : Tendsto (sa12k_diag a τ τ') atTop (𝓝 τ') := by
  rw [Metric.tendsto_atTop] at ht ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := ht ε hε
  refine ⟨a N, fun L hL => ?_⟩
  unfold sa12k_diag
  split_ifs with h
  · have hn : N ≤ Classical.choose h := by
      by_contra hlt
      have h1 : a (Classical.choose h) < a N := ha (not_le.1 hlt)
      have := Classical.choose_spec h
      linarith
    exact hN _ hn
  · simpa using hε

theorem sa12k_uniformize {X : Type} [NormedAddCommGroup X] {d : ℕ} (G : ℝ → ℝ → Euc d → X)
    (G' : ℝ → Euc d → X) (T : ℝ) (K : Set (Euc d))
    (H : ∀ τs ∈ Icc (0 : ℝ) T, ∀ τh : ℝ → ℝ, (∀ L, τh L ∈ Icc (0 : ℝ) T) →
      Tendsto τh atTop (𝓝 τs) → ∀ ε : ℝ, 0 < ε → ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L → ∀ x ∈ K,
        ‖G L (τh L) x - G' τs x‖ ≤ ε) :
    ∀ ε : ℝ, 0 < ε → ∃ L₁ : ℝ, ∀ L : ℝ, L₁ ≤ L → ∀ τ ∈ Icc (0 : ℝ) T, ∀ x ∈ K,
      ‖G L τ x - G' τ x‖ ≤ ε := by
  intro ε hε
  by_contra hcon
  push Not at hcon
  -- the bad points
  choose fL hfL fτ hfτ fx hfx hbad using hcon
  set bs : ℕ → ℝ := fun n => Nat.rec 0 (fun _ bn => fL bn + 1) n with hbs
  have hb0 : bs 0 = 0 := rfl
  have hbS : ∀ n, bs (n + 1) = fL (bs n) + 1 := fun n => rfl
  set a : ℕ → ℝ := fun n => fL (bs n) with ha_def
  set τn : ℕ → ℝ := fun n => fτ (bs n) with hτn
  set xn : ℕ → Euc d := fun n => fx (bs n) with hxn
  have ha_ge : ∀ n, bs n ≤ a n := fun n => hfL (bs n)
  have ha_succ : ∀ n, a n + 1 ≤ a (n + 1) := fun n => by
    have := ha_ge (n + 1)
    rw [hbS] at this
    exact this
  have ha : StrictMono a := strictMono_nat_of_lt_succ fun n => by linarith [ha_succ n]
  have ha_nat : ∀ n : ℕ, (n : ℝ) ≤ a n := by
    intro n
    induction n with
    | zero => simpa [hb0] using ha_ge 0
    | succ n ih => push_cast; linarith [ha_succ n]
  have hτmem : ∀ n, τn n ∈ Icc (0 : ℝ) T := fun n => hfτ (bs n)
  obtain ⟨τs, hτs, φ, hφ, hlim⟩ := isCompact_Icc.tendsto_subseq hτmem
  -- pointwise convergence along the constant diagonals
  have hconst : ∀ n, ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L → ∀ x ∈ K, ‖G L (τn (φ n)) x - G' (τn (φ n)) x‖ ≤ ε / 4 :=
    fun n => H (τn (φ n)) (hτmem _) (fun _ => τn (φ n)) (fun _ => hτmem _) tendsto_const_nhds
      (ε / 4) (by linarith)
  choose c hc using hconst
  set a' : ℕ → ℝ := fun n => Nat.rec (max (c 0) 0) (fun k ak => max (c (k + 1)) (ak + 1)) n with ha'
  have ha'0 : a' 0 = max (c 0) 0 := rfl
  have ha'S : ∀ n, a' (n + 1) = max (c (n + 1)) (a' n + 1) := fun n => rfl
  have ha'c : ∀ n, c n ≤ a' n := by
    intro n
    cases n with
    | zero => rw [ha'0]; exact le_max_left _ _
    | succ n => rw [ha'S]; exact le_max_left _ _
  have ha'mono : StrictMono a' := strictMono_nat_of_lt_succ fun n => by
    rw [ha'S]; exact lt_of_lt_of_le (by linarith) (le_max_right _ _)
  have ha'_nat : ∀ n : ℕ, (n : ℝ) ≤ a' n := by
    intro n
    induction n with
    | zero => rw [ha'0]; simp
    | succ n ih => push_cast; rw [ha'S]; linarith [le_max_right (c (n + 1)) (a' n + 1)]
  have haφ : StrictMono (a ∘ φ) := ha.comp hφ
  obtain ⟨L₁, hL₁⟩ := H τs hτs (sa12k_diag (a ∘ φ) (τn ∘ φ) τs)
    (sa12k_diag_mem (fun n => hτmem _) hτs) (sa12k_diag_tendsto haφ hlim) (ε / 4) (by linarith)
  obtain ⟨L₂, hL₂⟩ := H τs hτs (sa12k_diag a' (τn ∘ φ) τs)
    (sa12k_diag_mem (fun n => hτmem _) hτs) (sa12k_diag_tendsto ha'mono hlim) (ε / 4) (by linarith)
  obtain ⟨n, hn⟩ := exists_nat_ge (max L₁ L₂)
  have hφn : (n : ℝ) ≤ φ n := by exact_mod_cast hφ.id_le n
  have hx := hfx (bs (φ n))
  have e1 := hL₁ (a (φ n)) (by
    have := ha_nat (φ n)
    linarith [le_max_left L₁ L₂]) (xn (φ n)) hx
  have e2 := hL₂ (a' n) (by
    have := ha'_nat n
    linarith [le_max_right L₁ L₂]) (xn (φ n)) hx
  have e3 := hc n (a' n) (ha'c n) (xn (φ n)) hx
  have hd1 : sa12k_diag (a ∘ φ) (τn ∘ φ) τs (a (φ n)) = τn (φ n) :=
    sa12k_diag_apply haφ (τn ∘ φ) τs n
  have hd2 : sa12k_diag a' (τn ∘ φ) τs (a' n) = τn (φ n) :=
    sa12k_diag_apply ha'mono (τn ∘ φ) τs n
  rw [hd1] at e1
  rw [hd2] at e2
  have hbd := hbad (bs (φ n))
  have hbd' : ε < ‖G (a (φ n)) (τn (φ n)) (xn (φ n)) - G' (τn (φ n)) (xn (φ n))‖ := hbd
  have tri : ‖G (a (φ n)) (τn (φ n)) (xn (φ n)) - G' (τn (φ n)) (xn (φ n))‖ ≤
      ‖G (a (φ n)) (τn (φ n)) (xn (φ n)) - G' τs (xn (φ n))‖ +
      ‖G (a' n) (τn (φ n)) (xn (φ n)) - G' τs (xn (φ n))‖ +
      ‖G (a' n) (τn (φ n)) (xn (φ n)) - G' (τn (φ n)) (xn (φ n))‖ := by
    calc _ = ‖(G (a (φ n)) (τn (φ n)) (xn (φ n)) - G' τs (xn (φ n))) -
          (G (a' n) (τn (φ n)) (xn (φ n)) - G' τs (xn (φ n))) +
          (G (a' n) (τn (φ n)) (xn (φ n)) - G' (τn (φ n)) (xn (φ n)))‖ := by congr 1; abel
      _ ≤ ‖(G (a (φ n)) (τn (φ n)) (xn (φ n)) - G' τs (xn (φ n))) -
          (G (a' n) (τn (φ n)) (xn (φ n)) - G' τs (xn (φ n)))‖ +
          ‖G (a' n) (τn (φ n)) (xn (φ n)) - G' (τn (φ n)) (xn (φ n))‖ := norm_add_le _ _
      _ ≤ _ := by gcongr; exact norm_sub_le _ _
  linarith

end HRS.MH.AdjointRd.Phase2SA12Construction
