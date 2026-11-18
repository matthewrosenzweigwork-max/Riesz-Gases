import HRS.MS.GradSmAux3

/-!
# S6.7 packet S67B: gradient smoothing, part 4: the qualitative gain `C_b^k → C^{k+1}`

`s67b_gs_gain`: the literal statement of `W:r2mov:gradient-smoothing`.  For `F ∈ C^k` with `‖D^i F‖ ≤ M i` (`i ≤ k`; no
regularity beyond `k` and no bound on `D^{k+1}F` is assumed) and `t > 0`:
`P_t F ∈ C^{k+1}` and `‖D^j P_t F‖ ≤ C (1 + t^{-1/2}) e^{-c0 t} ∑_{i ≤ k} M i`, `1 ≤ j ≤ k+1`.
The drift needs `m ≥ k+2` derivatives (one more level than in `s67b_gs_close`).

Proof.  Mollify `F_n → F` (`pois_moll_data`); `G_n = P_t F_n` satisfies `‖D^j G_n‖ ≤ Bd` for `j ≤ k+1` (`s67b_gs_smooth`, independent
of `n`) and, by `P_t = P_{t/2} P_{t/2}` and a second application to `H_n = P_{t/2}F_n` (order `k+1 → k+2`),
`‖D^{k+2} G_n‖ ≤ Bd₃`.  Then `s67b_lim` gives `P_t F = lim G_n ∈ C^{k+1}` and the closing lemma `moll_closing` the bounds.
-/

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal Interval RealInnerProductSpace ContDiff
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MS.PoisFlow HRS.MS.PoisSg
  HRS.MS.PoisMarkov HRS.MS.PoisKolm HRS.MS.PoisGrad HRS.MS.PoisMax HRS.MS.PoisMoll
  HRS.MS.PoisHigh

noncomputable section

universe u

namespace HRS.MS.GradSm

variable {d : ℕ}

theorem s67b_gs_gain (q Mb : ℝ) (hq : 0 < q) (hMb : 0 ≤ Mb) (m : ℕ) (hm : 2 ≤ m) (k : ℕ)
    (hk : k + 2 ≤ m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω)
      [IsProbabilityMeasure P] (ℱ : Filtration ℝ mΩ) (W : ℝ≥0 → Ω → Fin d → ℝ),
      IsBrownianFiltration P ℱ W → ∀ B : Euc d → Euc d, HasCbBound m Mb B →
      ∀ F : Euc d → ℝ, ContDiff ℝ (k : WithTop ℕ∞) F → ∀ M : ℕ → ℝ,
      (∀ i ≤ k, ∀ y, ‖iteratedFDeriv ℝ i F y‖ ≤ M i) → ∀ t : ℝ, 0 < t →
      ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞) (sg P W q B t F) ∧
      ∀ j : ℕ, 1 ≤ j → j ≤ k + 1 → ∀ x,
      ‖iteratedFDeriv ℝ j (sg P W q B t F) x‖ ≤
        C * (1 + (Real.sqrt t)⁻¹) * Real.exp (-(pm_c0 q Mb) * t) *
          ∑ i ∈ Finset.range (k + 1), M i := by
  obtain ⟨C, hC0, hC⟩ := s67b_gs_smooth (d := d) q Mb hq hMb m hm k (by omega)
  obtain ⟨C', hC'0, hC'⟩ := s67b_gs_smooth (d := d) q Mb hq hMb m hm (k + 1) (by omega)
  refine ⟨C, hC0, fun {Ω} {mΩ} P _ ℱ W hW B hBm F hF M hM t ht0 => ?_⟩
  have hWs := sgNoise_of_brownian hW
  have hM0 : ∀ i ≤ k, 0 ≤ M i := fun i hi => (norm_nonneg _).trans (hM i hi 0)
  obtain ⟨hn, hnc, hnM, hnb, hn0, hnlim⟩ := pois_moll_data (k := k) hF (M := M) hM
  choose Cn hCn using hnb
  set c0 : ℝ := pm_c0 q Mb with hc0
  set K : ℝ := ∑ i ∈ Finset.range (k + 1), M i with hK
  have hK0 : 0 ≤ K := Finset.sum_nonneg fun i hi => hM0 i (by
    have := Finset.mem_range.1 hi; omega)
  let Mt : ℕ → ℕ → ℝ := fun n i => if i ≤ k then M i else Cn n i
  have hMt : ∀ n, ∀ i ≤ m, ∀ y, ‖iteratedFDeriv ℝ i (hn n) y‖ ≤ Mt n i := by
    intro n i hi y
    by_cases hik : i ≤ k
    · simp only [Mt, hik, ite_true]; exact hnM n i hik y
    · simp only [Mt, hik, ite_false]; exact hCn n i y
  have hMtK : ∀ n, ∑ i ∈ Finset.range (k + 1), Mt n i = K := fun n =>
    Finset.sum_congr rfl fun i hi => by
      have := Finset.mem_range.1 hi
      simp only [Mt, show i ≤ k by omega, ite_true]
  let Bf : ℝ → ℝ := fun s => C * (1 + (Real.sqrt s)⁻¹) * Real.exp (-c0 * s) * K
  have ha : ∀ s : ℝ, 0 < s → ∀ n, ∀ j : ℕ, 1 ≤ j → j ≤ k + 1 → ∀ x,
      ‖iteratedFDeriv ℝ j (sg P W q B s (hn n)) x‖ ≤ Bf s := by
    intro s hs n j hj1 hj2 x
    have := hC P ℱ W hW B hBm (hn n) ((hnc n).of_le (by exact_mod_cast le_top)) (Mt n) (hMt n) s hs
      j hj1 hj2 x
    rw [hMtK n] at this
    exact this
  -- the order `k + 2` bound, uniformly in `n`
  set t₂ : ℝ := t / 2 with ht₂def
  have ht₂ : 0 < t₂ := by positivity
  obtain ⟨Csg, hCsg1, hCsg⟩ := sg_contDiff (d := d) q Mb hq m hm t₂ ht₂.le m le_rfl
  set Mx : ℝ := max (M 0) (Bf t₂) with hMx
  have hMx0 : 0 ≤ Mx := le_max_of_le_left (hM0 0 (Nat.zero_le _))
  set Bd₃ : ℝ := C' * (1 + (Real.sqrt t₂)⁻¹) * Real.exp (-c0 * t₂) * (((k : ℝ) + 2) * Mx) with hBd₃
  have hD3 : ∀ n x, ‖iteratedFDeriv ℝ (k + 2) (sg P W q B t (hn n)) x‖ ≤ Bd₃ := by
    intro n x
    set Mn' : ℝ := ∑ i ∈ Finset.range (m + 1), |Mt n i| with hMn'
    have hMn'b : ∀ i ≤ m, Mt n i ≤ Mn' := fun i hi =>
      (le_abs_self _).trans (Finset.single_le_sum (f := fun i => |Mt n i|) (fun _ _ => abs_nonneg _)
        (Finset.mem_range.2 (by omega)))
    obtain ⟨hrc, -, hrb⟩ := hCsg P W hWs B hBm (hn n) ((hnc n).of_le (by exact_mod_cast le_top)) Mn'
      (fun i hi y => (hMt n i hi y).trans (hMn'b i hi)) t₂ ⟨ht₂.le, le_rfl⟩
    set Hn : Euc d → ℝ := sg P W q B t₂ (hn n) with hHn
    let MH : ℕ → ℝ := fun i => if i = 0 then M 0 else if i ≤ k + 1 then Bf t₂ else Csg * Mn'
    have hH : ∀ i ≤ m, ∀ y, ‖iteratedFDeriv ℝ i Hn y‖ ≤ MH i := by
      intro i hi y
      by_cases hi0 : i = 0
      · subst hi0
        simp only [MH, ite_true]
        rw [norm_iteratedFDeriv_zero]
        exact gs_sg_abs_le (P := P) (W := W) (q := q) (B := B) (hn0 n) t₂ y
      · by_cases hi1 : i ≤ k + 1
        · simp only [MH, hi0, hi1, ite_true, ite_false]
          exact ha t₂ ht₂ n i (by omega) hi1 y
        · simp only [MH, hi0, hi1, ite_false]
          exact hrb i hi y
    have hb3 := hC' P ℱ W hW B hBm Hn hrc MH hH t₂ ht₂ (k + 2) (by omega) le_rfl x
    have hmk : sg P W q B t (hn n) = sg P W q B t₂ Hn := by
      funext y
      have := sg_markov_C2 hW hq.le (by omega : 1 ≤ m) hBm (h := hn n)
        ((hnc n).of_le (by norm_num) : ContDiff ℝ (2 : WithTop ℕ∞) (hn n)) (M := Mn')
        (fun i hi y => (hMt n i (by omega) y).trans (hMn'b i (by omega))) (t := t₂) (s := t₂)
        ht₂.le ht₂.le y
      have e : t₂ + t₂ = t := by rw [ht₂def]; ring
      rw [e] at this
      exact this
    rw [hmk]
    refine hb3.trans ?_
    have hsum : ∑ i ∈ Finset.range (k + 1 + 1), MH i ≤ ((k : ℝ) + 2) * Mx := by
      have h1 : ∀ i ∈ Finset.range (k + 1 + 1), MH i ≤ Mx := by
        intro i hi
        have hi' := Finset.mem_range.1 hi
        by_cases hi0 : i = 0
        · simp only [MH, hi0, ite_true]; exact le_max_left _ _
        · simp only [MH, hi0, show i ≤ k + 1 by omega, ite_true, ite_false]
          exact le_max_right _ _
      have := Finset.sum_le_card_nsmul _ _ Mx h1
      simpa [nsmul_eq_mul, add_assoc, one_add_one_eq_two] using this
    rw [hBd₃]
    exact mul_le_mul_of_nonneg_left hsum (by positivity)
  -- the uniform bound
  set Bd : ℝ := Bf t with hBd
  set K2 : ℝ := max (M 0) (max Bd Bd₃) with hK2
  have hK20 : 0 ≤ K2 := le_max_of_le_left (hM0 0 (Nat.zero_le _))
  have hG : ∀ n, ∀ i ≤ k + 2, ∀ x, ‖iteratedFDeriv ℝ i (sg P W q B t (hn n)) x‖ ≤ K2 := by
    intro n i hi x
    by_cases hi0 : i = 0
    · subst hi0
      rw [norm_iteratedFDeriv_zero]
      exact (gs_sg_abs_le (P := P) (W := W) (q := q) (B := B) (hn0 n) t x).trans (le_max_left _ _)
    · by_cases hi2 : i = k + 2
      · subst hi2
        exact (hD3 n x).trans ((le_max_right _ _).trans' (le_max_right _ _))
      · exact (ha t ht0 n i (by omega) (by omega) x).trans
          ((le_max_left _ _).trans (le_max_right _ _))
  obtain ⟨Csg', -, hCsg'⟩ := sg_contDiff (d := d) q Mb hq m hm t ht0.le m le_rfl
  have hcd : ∀ n, ContDiff ℝ (m : WithTop ℕ∞) (sg P W q B t (hn n)) := by
    intro n
    set Mn' : ℝ := ∑ i ∈ Finset.range (m + 1), |Mt n i| with hMn'
    have hMn'b : ∀ i ≤ m, Mt n i ≤ Mn' := fun i hi =>
      (le_abs_self _).trans (Finset.single_le_sum (f := fun i => |Mt n i|) (fun _ _ => abs_nonneg _)
        (Finset.mem_range.2 (by omega)))
    exact (hCsg' P W hWs B hBm (hn n) ((hnc n).of_le (by exact_mod_cast le_top)) Mn'
      (fun i hi y => (hMt n i hi y).trans (hMn'b i hi)) t ⟨ht0.le, le_rfl⟩).1
  have hlim : ∀ x, Tendsto (fun n => sg P W q B t (hn n) x) atTop (𝓝 (sg P W q B t F x)) := fun x =>
    moll_sg_tendsto_data P hWs hq.le (by omega : 1 ≤ m) hBm (fun n => (hnc n).continuous) hnlim
      (M0 := M 0) hn0 ht0.le x
  have hmain : ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞) (sg P W q B t F) :=
    s67b_lim K2 hK20 (k + 1) (fun n => sg P W q B t (hn n)) (sg P W q B t F)
      (fun n => (hcd n).of_le (by exact_mod_cast hk)) (fun n i hi x => hG n i (by omega) x) hlim
  refine ⟨hmain, fun j hj1 hjk x => ?_⟩
  have hcl := moll_closing (j0 := k + 1) (C := fun i => if i = 0 then M 0 else Bd)
    (fun n => (hcd n).of_le (by exact_mod_cast (by omega : k + 1 ≤ m))) hmain hlim
    (fun n i hi y => ?_) j hjk x
  · have : j ≠ 0 := by omega
    simp only [this, ite_false] at hcl
    exact hcl
  · by_cases hi0 : i = 0
    · subst hi0
      rw [norm_iteratedFDeriv_zero]
      simpa using gs_sg_abs_le (P := P) (W := W) (q := q) (B := B) (hn0 n) t y
    · simp only [hi0, ite_false]
      exact ha t ht0 n i (by omega) hi y

end HRS.MS.GradSm
