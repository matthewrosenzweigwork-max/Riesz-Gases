import Mathlib

/-!
# S11.3 Liouville (worker S11Q2), C1: deterministic analysis of the Euler scheme for `y' = b~(y) + c'`

For a bounded Lipschitz drift `b~` and a continuous forcing `c`, the Euler scheme with step `h` and increments
`c((j+1)h) - c(jh)` is (i) a lower Lipschitz map of the initial point, with constant `(1 - hL)^j`, and (ii) uniformly close to any
solution `y s = y 0 + ∫_0^s b~(y) + c s - c 0` on `[0,t]` (error `≤ (e^{Lt} - 1)(M h + modulus of c)`).
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

open MeasureTheory Filter Topology Set intervalIntegral

namespace HRS.MS.S11Q2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The Euler scheme with step `h`, drift `bt`, increments `inc`, started at `x`. -/
def s11q2_eul (h : ℝ) (bt : E → E) (inc : ℕ → E) (x : E) : ℕ → E
  | 0 => x
  | j + 1 => s11q2_eul h bt inc x j + h • bt (s11q2_eul h bt inc x j) + inc j

theorem s11q2_eul_lower {bt : E → E} {L h : ℝ} (hh : 0 ≤ h) (hL : ∀ x y, ‖bt x - bt y‖ ≤ L * ‖x - y‖)
    (hL0 : 0 ≤ L) (hhL : h * L ≤ 1 / 2) (inc : ℕ → E) (x x' : E) (j : ℕ) :
    (1 - h * L) ^ j * ‖x - x'‖ ≤ ‖s11q2_eul h bt inc x j - s11q2_eul h bt inc x' j‖ := by
  induction j with
  | zero => simp [s11q2_eul]
  | succ j ih =>
    set a := s11q2_eul h bt inc x j
    set a' := s11q2_eul h bt inc x' j
    have e : s11q2_eul h bt inc x (j + 1) - s11q2_eul h bt inc x' (j + 1) = (a - a') + h • (bt a - bt a') := by
      simp only [s11q2_eul]
      rw [smul_sub]; abel
    rw [e]
    have h1 : ‖a - a'‖ - h * (L * ‖a - a'‖) ≤ ‖(a - a') + h • (bt a - bt a')‖ := by
      have := norm_sub_norm_le (a - a') (-(h • (bt a - bt a')))
      rw [sub_neg_eq_add, norm_neg, norm_smul, Real.norm_of_nonneg hh] at this
      have h2 : h * ‖bt a - bt a'‖ ≤ h * (L * ‖a - a'‖) := mul_le_mul_of_nonneg_left (hL a a') hh
      linarith
    have hpos : 0 ≤ 1 - h * L := by linarith
    calc (1 - h * L) ^ (j + 1) * ‖x - x'‖ = (1 - h * L) * ((1 - h * L) ^ j * ‖x - x'‖) := by ring
      _ ≤ (1 - h * L) * ‖a - a'‖ := mul_le_mul_of_nonneg_left ih hpos
      _ = ‖a - a'‖ - h * (L * ‖a - a'‖) := by ring
      _ ≤ _ := h1

theorem s11q2_pow_lower {u : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ 1 / 2) (j : ℕ) : Real.exp (-2 * u * j) ≤ (1 - u) ^ j := by
  have h0 : Real.exp (-2 * u) ≤ 1 - u := by
    have h1 : 1 + 2 * u ≤ Real.exp (2 * u) := by linarith [Real.add_one_le_exp (2 * u)]
    have h2 : Real.exp (-2 * u) * (1 + 2 * u) ≤ 1 := by
      calc Real.exp (-2 * u) * (1 + 2 * u) ≤ Real.exp (-2 * u) * Real.exp (2 * u) :=
            mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
        _ = 1 := by rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos (-2 * u)]
  have : Real.exp (-2 * u * j) = (Real.exp (-2 * u)) ^ j := by
    rw [← Real.exp_nat_mul]; ring_nf
  rw [this]
  exact pow_le_pow_left₀ (Real.exp_pos _).le h0 j

section Conv

variable {bt : E → E} {L M : ℝ} {t : ℝ} {y c : ℝ → E}

/-- Setting for the error analysis. -/
structure s11q2_Sol (bt : E → E) (L M t : ℝ) (y c : ℝ → E) : Prop where
  hL0 : 0 ≤ L
  hM0 : 0 ≤ M
  hL : ∀ x y, ‖bt x - bt y‖ ≤ L * ‖x - y‖
  hM : ∀ x, ‖bt x‖ ≤ M
  hbc : Continuous bt
  hy : ContinuousOn y (Icc 0 t)
  hc : ContinuousOn c (Icc 0 t)
  heq : ∀ s ∈ Icc 0 t, y s = y 0 + (∫ r in (0 : ℝ)..s, bt (y r)) + (c s - c 0)

theorem s11q2_Sol.diff (H : s11q2_Sol bt L M t y c) {a r : ℝ} (ha : a ∈ Icc 0 t) (hr : r ∈ Icc 0 t) (har : a ≤ r) :
    y r - y a = (∫ s in a..r, bt (y s)) + (c r - c a) := by
  have hi : ∀ z ∈ Icc (0 : ℝ) t, IntervalIntegrable (fun s => bt (y s)) volume 0 z := fun z hz =>
    (H.hbc.comp_continuousOn (H.hy.mono (by
      rw [uIcc_of_le hz.1]; exact Icc_subset_Icc le_rfl hz.2))).intervalIntegrable
  have := intervalIntegral.integral_interval_sub_left (hi r hr) (hi a ha)
  rw [H.heq r hr, H.heq a ha, ← this]
  abel

theorem s11q2_Sol.step (H : s11q2_Sol bt L M t y c) {a h η : ℝ} (ha : 0 ≤ a) (hh : 0 ≤ h) (hat : a + h ≤ t)
    (hη : ∀ r ∈ Icc a (a + h), ‖c r - c a‖ ≤ η) (z : E) :
    ‖(z + h • bt z + (c (a + h) - c a)) - y (a + h)‖ ≤ (1 + h * L) * ‖z - y a‖ + h * L * (M * h + η) := by
  have haI : a ∈ Icc 0 t := ⟨ha, by linarith⟩
  have hrI : ∀ r ∈ Icc a (a + h), r ∈ Icc 0 t := fun r hr => ⟨ha.trans hr.1, hr.2.trans hat⟩
  have hint : ∀ r ∈ Icc a (a + h), IntervalIntegrable (fun s => bt (y s)) volume a r := fun r hr =>
    (H.hbc.comp_continuousOn (H.hy.mono (by
      rw [uIcc_of_le hr.1]; exact Icc_subset_Icc ha (hr.2.trans hat)))).intervalIntegrable
  have h1 := H.diff haI (hrI (a + h) ⟨by linarith, le_rfl⟩) (by linarith)
  have hconst : ∫ s in a..(a + h), bt z = h • bt z := by
    rw [intervalIntegral.integral_const]; congr 1; ring
  have hvec : (z + h • bt z + (c (a + h) - c a)) - y (a + h) =
      (z - y a) + ∫ s in a..(a + h), (bt z - bt (y s)) := by
    rw [intervalIntegral.integral_sub (intervalIntegrable_const) (hint _ ⟨by linarith, le_rfl⟩), hconst]
    have : y (a + h) = y a + (∫ s in a..(a + h), bt (y s)) + (c (a + h) - c a) := by rw [add_assoc, ← h1]; abel
    rw [this]; abel
  have hyr : ∀ r ∈ Icc a (a + h), ‖y r - y a‖ ≤ M * h + η := by
    intro r hr
    rw [H.diff haI (hrI r hr) hr.1]
    refine (norm_add_le _ _).trans (add_le_add ?_ (hη r hr))
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := r) (C := M) (f := fun s => bt (y s))
      (fun s _ => H.hM _)
    rw [abs_of_nonneg (by linarith [hr.1])] at this
    refine this.trans ?_
    exact mul_le_mul_of_nonneg_left (by linarith [hr.2]) H.hM0
  have hint2 : ‖∫ s in a..(a + h), (bt z - bt (y s))‖ ≤ (L * (‖z - y a‖ + (M * h + η))) * h := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := a + h)
      (C := L * (‖z - y a‖ + (M * h + η))) (f := fun s => bt z - bt (y s)) (fun s hs => by
        have hs' : s ∈ Icc a (a + h) := by
          rw [uIoc_of_le (by linarith)] at hs; exact ⟨hs.1.le, hs.2⟩
        refine (H.hL _ _).trans (mul_le_mul_of_nonneg_left ?_ H.hL0)
        calc ‖z - y s‖ = ‖(z - y a) - (y s - y a)‖ := by congr 1; abel
          _ ≤ ‖z - y a‖ + ‖y s - y a‖ := norm_sub_le _ _
          _ ≤ _ := add_le_add le_rfl (hyr s hs'))
    rwa [show a + h - a = h by ring, abs_of_nonneg hh] at this
  rw [hvec]
  refine (norm_add_le _ _).trans ?_
  nlinarith [hint2]

theorem s11q2_eul_err (H : s11q2_Sol bt L M t y c) {h η : ℝ} (hh : 0 ≤ h) (hη0 : 0 ≤ η)
    (hη : ∀ a ∈ Icc (0 : ℝ) t, a + h ≤ t → ∀ r ∈ Icc a (a + h), ‖c r - c a‖ ≤ η) (j : ℕ) (hj : j * h ≤ t) :
    ‖s11q2_eul h bt (fun i => c ((i + 1) * h) - c (i * h)) (y 0) j - y (j * h)‖ ≤
      ((1 + h * L) ^ j - 1) * (M * h + η) := by
  induction j with
  | zero => simp [s11q2_eul]
  | succ j ih =>
    have hj1 : ((j : ℝ) + 1) * h ≤ t := by push_cast at hj; exact hj
    have hjh : (j : ℝ) * h ≤ t := by nlinarith [hh]
    have ih' := ih hjh
    have ha : 0 ≤ (j : ℝ) * h := by positivity
    have hst := H.step (a := (j : ℝ) * h) (h := h) (η := η) ha hh (by linarith) (hη _ ⟨ha, hjh⟩ (by linarith))
      (s11q2_eul h bt (fun i => c ((i + 1) * h) - c (i * h)) (y 0) j)
    have e1 : (j : ℝ) * h + h = ((j + 1 : ℕ) : ℝ) * h := by push_cast; ring
    rw [e1] at hst
    have e2 : s11q2_eul h bt (fun i => c ((i + 1) * h) - c (i * h)) (y 0) (j + 1) =
        s11q2_eul h bt (fun i => c ((i + 1) * h) - c (i * h)) (y 0) j +
          h • bt (s11q2_eul h bt (fun i => c ((i + 1) * h) - c (i * h)) (y 0) j) +
          (c (((j : ℝ) + 1) * h) - c (j * h)) := rfl
    have e3 : c (((j : ℝ) + 1) * h) = c (((j + 1 : ℕ) : ℝ) * h) := by push_cast; rfl
    rw [e2, e3]
    have hc : 0 ≤ h * L := mul_nonneg hh H.hL0
    calc _ ≤ (1 + h * L) * ‖s11q2_eul h bt (fun i => c ((i + 1) * h) - c (i * h)) (y 0) j - y (j * h)‖ +
          h * L * (M * h + η) := by simpa [e1] using hst
      _ ≤ (1 + h * L) * (((1 + h * L) ^ j - 1) * (M * h + η)) + h * L * (M * h + η) :=
          by gcongr
      _ = ((1 + h * L) ^ (j + 1) - 1) * (M * h + η) := by ring

/-- The dyadic Euler scheme converges to the solution. -/
theorem s11q2_eul_tendsto (H : s11q2_Sol bt L M t y c) (ht : 0 ≤ t) :
    Tendsto (fun k : ℕ => s11q2_eul (t / 2 ^ k) bt (fun i => c ((i + 1) * (t / 2 ^ k)) - c (i * (t / 2 ^ k))) (y 0) (2 ^ k))
      atTop (𝓝 (y t)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  set K : ℝ := Real.exp (L * t) with hK
  have hK1 : 1 ≤ K := Real.one_le_exp (mul_nonneg H.hL0 ht)
  have hK0 : 0 < K := by linarith
  obtain ⟨δ1, hδ1, hc⟩ := Metric.uniformContinuousOn_iff.1
    (isCompact_Icc.uniformContinuousOn_of_continuous H.hc) (ε / (4 * K)) (by positivity)
  have hh0 : Tendsto (fun k : ℕ => t / 2 ^ k) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))
  obtain ⟨k0, hk0⟩ := Filter.eventually_atTop.1 (hh0.eventually (gt_mem_nhds
    (lt_min hδ1 (show 0 < ε / (4 * K * (M + 1)) by have := H.hM0; positivity))))
  refine ⟨k0, fun k hk => ?_⟩
  have hhk := hk0 k hk
  set h : ℝ := t / 2 ^ k with hhdef
  have hh : 0 ≤ h := by positivity
  have hjh : ((2 ^ k : ℕ) : ℝ) * h = t := by
    simp only [hhdef]; push_cast; field_simp
  have herr := s11q2_eul_err H (h := h) (η := ε / (4 * K)) hh (by positivity) (by
    intro a ha hat r hr
    have := hc r ⟨ha.1.trans hr.1, hr.2.trans hat⟩ a ha (by
      rw [Real.dist_eq, abs_of_nonneg (by linarith [hr.1])]
      exact lt_of_le_of_lt (by linarith [hr.2]) (lt_of_lt_of_le hhk (min_le_left _ _)))
    rw [dist_eq_norm] at this
    exact this.le) (2 ^ k) (by rw [hjh])
  rw [hjh] at herr
  rw [dist_eq_norm]
  refine lt_of_le_of_lt herr ?_
  have hpow : (1 + h * L) ^ (2 ^ k) ≤ K := by
    calc (1 + h * L) ^ (2 ^ k) ≤ (Real.exp (h * L)) ^ (2 ^ k) :=
          pow_le_pow_left₀ (by have := mul_nonneg hh H.hL0; linarith) (by linarith [Real.add_one_le_exp (h * L)]) _
      _ = K := by
          rw [← Real.exp_nat_mul, hK]; congr 1
          have : ((2 ^ k : ℕ) : ℝ) * h = t := hjh
          push_cast at this ⊢
          rw [← this]; ring
  have hMh : M * h ≤ ε / (4 * K) := by
    have h1 : h < ε / (4 * K * (M + 1)) := lt_of_lt_of_le hhk (min_le_right _ _)
    have h2 : M * h ≤ (M + 1) * h := by nlinarith [H.hM0]
    have h3 : (M + 1) * h ≤ ε / (4 * K) := by
      have : (M + 1) * h ≤ (M + 1) * (ε / (4 * K * (M + 1))) := mul_le_mul_of_nonneg_left h1.le (by linarith [H.hM0])
      refine this.trans_eq ?_
      have hM1 : M + 1 ≠ 0 := by linarith [H.hM0]
      field_simp
    linarith
  have hnn : 0 ≤ M * h + ε / (4 * K) := by have := H.hM0; positivity
  calc ((1 + h * L) ^ (2 ^ k) - 1) * (M * h + ε / (4 * K)) ≤ (K - 1) * (ε / (4 * K) + ε / (4 * K)) := by
        gcongr
    _ ≤ K * (ε / (4 * K) + ε / (4 * K)) := by
        gcongr; linarith
    _ = ε / 2 := by field_simp; ring
    _ < ε := by linarith

end Conv

end HRS.MS.S11Q2

end
