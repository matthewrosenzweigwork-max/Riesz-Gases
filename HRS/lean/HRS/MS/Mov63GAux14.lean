import HRS.MS.Mov63GAux13

/-!
# S6.3, packet N8 (part 14): the core estimate

Namespace `HRS.MS.Mov63`, prefix `mng_`.  `mng_growth_conc`: the a priori growth `S_m ≤ K_p e^{κ₀‖x‖²}`, `κ₀ < q/(2ν) = βq/2`, from the crude bound
(`mng_crude`) and the interpolation (`mng_growth_iter`).  **`mng_core`**: for the mild solution `v` with `‖v_t‖ ≤ C_v K e^{-c₁ t}`, `Q_t ∈ [1/2,2]`
and `‖D^i Q_0‖ ≤ K`: `‖D^i Q_t(x)‖ ≤ C K e^{-ct}` for `1 ≤ i ≤ N`, with `c ≤ c₁`, `C` independent of `v`, `K`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.Mov63

open HRS HRS.Whole HRS.MS.MovOsc HRS.MS.MovC1 HRS.MS.MovForce HRS.MS.MovLin HRS.MH.DualityRd HRS.MS.PoisKolm

variable {d : ℕ} {s β q : ℝ} {ρ : Euc d → ℝ}

section Growth

variable {m : ℕ} (H : Mov2dTh d s β q ρ) (hm : (d : ℝ) / 2 + 3 < m)

include H hm in
lemma mng_growth_conc {N : ℕ} (hN : (d : ℝ) / 2 + N + 2 < m) (Cv : ℝ) {v : ℝ → OscSpace d (m : ℝ)}
    (hvb : ∀ t, 0 ≤ t → ‖v t‖ ≤ Cv) (hQ : ∀ t, 0 ≤ t → ∀ x, |mneQ ρ hm (v t) x| ≤ 2) (T : ℝ) :
    ∃ Kp κ0 : ℝ, 0 ≤ Kp ∧ κ0 < q / (2 * β⁻¹) ∧ ∀ m', 1 ≤ m' → m' ≤ N → ∀ t ∈ Icc 0 T, ∀ x : Euc d,
      mngS (fun t => mneQ ρ hm (v t)) m' t x ≤ Kp * Real.exp (κ0 * ‖x‖ ^ 2) := by
  have hβ := H.hβ
  have hq := H.hq
  set u : ℝ := (1 / 2 : ℝ) ^ N with hu
  have hu0 : 0 < u := by positivity
  have hu1 : u ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  set K1 : ℝ := (β * q / 4) * (1 + u ^ 2 / 2) with hK1
  have hbq : 0 < β * q := mul_pos hβ hq
  have hK1pos : 0 < K1 := by rw [hK1]; positivity
  have hK1gt : β * q / 4 < K1 := by rw [hK1]; nlinarith [sq_pos_of_pos hu0, mul_pos hbq (sq_pos_of_pos hu0)]
  obtain ⟨Cc, hCc0, hCc⟩ := mng_crude H hm hN hK1gt Cv
  set δ : ℝ := K1 * u / 2 with hδ
  have hδpos : 0 < δ := by rw [hδ]; positivity
  have hQcd : ∀ t, ContDiff ℝ ((N + 1 : ℕ) : WithTop ℕ∞) (mneQ ρ hm (v t)) := fun t =>
    (mng_Q_cd H hm hN (v t)).of_le (by exact_mod_cast Nat.le_succ (N + 1))
  have hgi := mng_growth_iter (Qf := fun t => mneQ ρ hm (v t)) (N := N) hQcd (MQ := 2) (K1 := K1) (δ := δ) hK1pos hδpos
    (by rw [hδ]; rw [← hu]; nlinarith)
    (fun t ht y => by
      rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]; exact hQ t ht y)
    (fun i hi1 hiN => ⟨Cc, hCc0, fun t ht y => hCc (v t) (hvb t ht) i hi1 hiN y⟩)
  have hgi' : ∀ i : ℕ, ∃ C : ℝ, 0 ≤ C ∧ (i ≤ N → ∀ t, 0 ≤ t → ∀ y,
      ‖iteratedFDeriv ℝ i (mneQ ρ hm (v t)) y‖ ≤ C * Real.exp ((K1 + 2 * δ) * (1 - (1 / 2 : ℝ) ^ i) * ‖y‖ ^ 2)) := by
    intro i
    by_cases hi : i ≤ N
    · obtain ⟨C, hC0, hC⟩ := hgi i hi
      exact ⟨C, hC0, fun _ => hC⟩
    · exact ⟨0, le_rfl, fun h => absurd h hi⟩
  choose Cg hCg0 hCg using hgi'
  set eN : ℝ := (K1 + 2 * δ) * (1 - u) with heN
  have hKδ : K1 + 2 * δ = K1 * (1 + u) := by rw [hδ]; ring
  have heN2 : eN = K1 * (1 - u ^ 2) := by rw [heN, hKδ]; ring
  refine ⟨∑ i ∈ Finset.range (N + 1), (d : ℝ) ^ i * Cg i ^ 2, 2 * eN, by positivity, ?_, ?_⟩
  · -- 2 eN < βq/2
    have e : q / (2 * β⁻¹) = β * q / 2 := by field_simp
    rw [e, heN2, hK1]
    nlinarith [sq_pos_of_pos hu0, mul_pos hbq (sq_pos_of_pos hu0), mul_pos hbq (pow_pos hu0 4)]
  · intro m' hm1 hmN t ht x
    have h1 := mng_S_le_norm_sq (Q := fun t => mneQ ρ hm (v t)) (N := N + 2)
      (fun t => mng_Q_cd H hm hN (v t)) (by omega : m' ≤ N + 2) t x
    obtain ⟨-, h2⟩ := (⟨hCg0 m', hCg m'⟩ : 0 ≤ Cg m' ∧ _)
    have h3 := hCg m' hmN t ht.1 x
    have hep : (K1 + 2 * δ) * (1 - (1 / 2 : ℝ) ^ m') ≤ eN := by
      rw [heN]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      have : u ≤ (1 / 2 : ℝ) ^ m' := pow_le_pow_of_le_one (by norm_num) (by norm_num) hmN
      linarith
    have hsq : ‖iteratedFDeriv ℝ m' (mneQ ρ hm (v t)) x‖ ^ 2 ≤
        (Cg m' * Real.exp (eN * ‖x‖ ^ 2)) ^ 2 := by
      refine pow_le_pow_left₀ (norm_nonneg _) (h3.trans ?_) 2
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (hCg0 m')
      exact mul_le_mul_of_nonneg_right hep (sq_nonneg _)
    calc mngS (fun t => mneQ ρ hm (v t)) m' t x ≤ (d : ℝ) ^ m' * ‖iteratedFDeriv ℝ m' (mneQ ρ hm (v t)) x‖ ^ 2 := h1
      _ ≤ (d : ℝ) ^ m' * (Cg m' * Real.exp (eN * ‖x‖ ^ 2)) ^ 2 := mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = ((d : ℝ) ^ m' * Cg m' ^ 2) * Real.exp (2 * eN * ‖x‖ ^ 2) := by
          have e2 : Real.exp (eN * ‖x‖ ^ 2) ^ 2 = Real.exp (2 * eN * ‖x‖ ^ 2) := by
            rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
          rw [mul_pow, e2]; ring
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
          exact Finset.single_le_sum (f := fun i => (d : ℝ) ^ i * Cg i ^ 2) (fun i _ => by positivity)
            (Finset.mem_range.2 (by omega))

end Growth

end HRS.MS.Mov63

end
