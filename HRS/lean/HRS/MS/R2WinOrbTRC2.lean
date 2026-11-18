import HRS.MS.R2WinOrbTRC1

/-!
# S10.3 packet [C], part 2: iterated differences, averages of functions with bounded jets, time-Lipschitz bounds

Prefix `s103c_`, namespace `HRS.MS.R2WinOrbNL`.

* `s103c_dp_bound`: iterated mean value bound with the weight `((1+‖y‖)⁻¹)^p` (all orders, `p = 0` is the unweighted bound).
* `s103c_iter_le_of_dpF`: a bound on the small iterated differences at `x` gives a bound on `‖D^k G(x)‖` (loses the factor `d^k`).
* `s103c_avg_bd`: if `G(y) = ∫_e^l g_σ(y) dσ` with `g_σ ∈ Bd N B` and `G ∈ C^N` then `G ∈ Bd N (c B (l-e))`.
* `s103c_rho_lip`: the weighted jets of `ρ_b - ρ_a` are `O(b-a)` when the right derivative `ρ'` has weighted jets (iterated differences in the time variable).
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory Metric
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.R2WinOrbNL

open HRS HRS.Whole HRS.MS.Wad HRS.MS.Ul

variable {d : ℕ}

theorem s103c_dp_bound (p : ℕ) : ∀ (k : ℕ) {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : Euc d → F) {N : ℝ}, 0 ≤ N → ContDiff ℝ k g →
    (∀ i, i ≤ k → ∀ y, ‖iteratedFDeriv ℝ i g y‖ ≤ N * ((1 + ‖y‖)⁻¹) ^ p) →
    ∀ η : List (Euc d), η.length = k → (η.map (fun e => ‖e‖)).sum ≤ 1 / 8 → ∀ y,
      ‖s8f_dp η g y‖ ≤ N * ((5 / 4) ^ p) ^ k * (η.map (fun e => ‖e‖)).prod * ((1 + ‖y‖)⁻¹) ^ p := by
  intro k
  induction k with
  | zero =>
    intro F _ _ g N hN hg hb η hη hs y
    have : η = [] := List.length_eq_zero_iff.1 hη
    subst this
    simp only [s8f_dp, pow_zero, mul_one, List.map_nil, List.prod_nil]
    have := hb 0 le_rfl y
    rwa [norm_iteratedFDeriv_zero] at this
  | succ k ih =>
    intro F _ _ g N hN hg hb η hη hs y
    obtain ⟨e, rest, rfl⟩ : ∃ e rest, η = e :: rest := by
      cases η with
      | nil => simp at hη
      | cons e rest => exact ⟨e, rest, rfl⟩
    have hη' : rest.length = k := by simpa using hη
    simp only [List.map_cons, List.sum_cons, List.prod_cons] at hs ⊢
    have hS : 0 ≤ (rest.map (fun e => ‖e‖)).sum := List.sum_nonneg (by
      intro x hx
      obtain ⟨a, -, rfl⟩ := List.mem_map.1 hx
      exact norm_nonneg a)
    have hrest : (rest.map (fun e => ‖e‖)).sum ≤ 1 / 8 := by linarith [norm_nonneg e]
    have hdg : Differentiable ℝ g := hg.differentiable (by simp)
    have hDg : ContDiff ℝ k (fderiv ℝ g) := hg.fderiv_right (by norm_cast)
    have hP : 0 ≤ (rest.map (fun e => ‖e‖)).prod := List.prod_nonneg (by
      intro x hx
      obtain ⟨a, -, rfl⟩ := List.mem_map.1 hx
      exact norm_nonneg a)
    have hw0 : 0 ≤ ((1 + ‖y‖)⁻¹) ^ p := by positivity
    have hc0 : 0 ≤ ((5 / 4 : ℝ) ^ p) := by positivity
    set C : ℝ := N * ((5 / 4) ^ p) ^ k * (rest.map (fun e => ‖e‖)).prod *
      (((5 / 4) ^ p) * ((1 + ‖y‖)⁻¹) ^ p) with hC
    have hmv := (convex_ball y (1 / 4 : ℝ)).norm_image_sub_le_of_norm_fderiv_le (f := s8f_dp rest g) (C := C)
      (fun y' _ => (s8f_dp_differentiable rest hdg) y') (fun y' hy' => ?_) (mem_ball_self (by norm_num))
      (show y + e ∈ ball y (1 / 4) by
        rw [mem_ball_iff_norm]; simp only [add_sub_cancel_left]; linarith [norm_nonneg e])
    · simp only [add_sub_cancel_left] at hmv
      show ‖s8f_dp rest g (y + e) - s8f_dp rest g y‖ ≤ _
      refine hmv.trans (le_of_eq ?_)
      rw [hC]; ring
    · rw [s8f_dp_fderiv rest hdg]
      have := ih (fderiv ℝ g) (N := N) hN hDg (fun i hi y' => by
        rw [norm_iteratedFDeriv_fderiv]; exact hb (i + 1) (by omega) y') rest hη' hrest y'
      refine this.trans ?_
      have hy'' : ‖y' - y‖ ≤ 1 / 4 := by rw [mem_ball_iff_norm] at hy'; exact hy'.le
      have hj := s103b_w_ball hy''
      have hjp : ((1 + ‖y'‖)⁻¹) ^ p ≤ ((5 / 4) ^ p) * ((1 + ‖y‖)⁻¹) ^ p := by
        rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) hj p
      rw [hC]
      calc N * ((5 / 4) ^ p) ^ k * (rest.map (fun e => ‖e‖)).prod * ((1 + ‖y'‖)⁻¹) ^ p
          ≤ N * ((5 / 4) ^ p) ^ k * (rest.map (fun e => ‖e‖)).prod * (((5 / 4) ^ p) * ((1 + ‖y‖)⁻¹) ^ p) :=
            mul_le_mul_of_nonneg_left hjp (by positivity)
        _ = _ := rfl

theorem s103c_dpF_bound (p : ℕ) {k : ℕ} {g : Euc d → ℝ} {Ng : ℝ} (hN : 0 ≤ Ng) (hg : ContDiff ℝ k g)
    (hb : ∀ i, i ≤ k → ∀ y, ‖iteratedFDeriv ℝ i g y‖ ≤ Ng * ((1 + ‖y‖)⁻¹) ^ p)
    (m : Fin k → Euc d) (hm : ∑ l, ‖m l‖ ≤ 1 / 8) (y : Euc d) :
    |s8f_dpF k m g y| ≤ Ng * ((5 / 4) ^ p) ^ k * (∏ l, ‖m l‖) * ((1 + ‖y‖)⁻¹) ^ p := by
  rw [← s8f_dp_ofFn]
  have hs : (((List.ofFn m).reverse).map (fun e => ‖e‖)).sum ≤ 1 / 8 := by
    rw [List.map_reverse, List.sum_reverse, List.map_ofFn, List.sum_ofFn]
    exact hm
  have := s103c_dp_bound p k g hN hg hb (List.ofFn m).reverse (by simp) hs y
  rw [List.map_reverse, List.prod_reverse, List.map_ofFn, List.prod_ofFn] at this
  rwa [Real.norm_eq_abs] at this

/-- A bound on the small iterated differences at `x` gives a bound on the `k`-th derivative at `x`. -/
theorem s103c_iter_le_of_dpF {k : ℕ} {G : Euc d → ℝ} (hG : ContDiff ℝ k G) {B : ℝ} (hB : 0 ≤ B) (x : Euc d)
    (hdp : ∀ h : ℝ, 0 < h → h ≤ 1 / (8 * ((k : ℝ) + 1)) → ∀ idx : Fin k → Fin d,
      |s8f_dpF k (fun l => h • (EuclideanSpace.single (idx l) (1 : ℝ) : Euc d)) G x| ≤ B * h ^ k) :
    ‖iteratedFDeriv ℝ k G x‖ ≤ (d : ℝ) ^ k * B := by
  refine s83_norm_iter_le_card hB k G x fun idx => ?_
  exact s8f_partial_le_of_dp hG idx x (h0 := 1 / (8 * ((k : ℝ) + 1))) (by positivity) (fun h hh hh0 => hdp h hh hh0 idx)

/-- The small steps `h • e_i` have total length `≤ 1/8`. -/
theorem s103c_steps_small {k : ℕ} {h : ℝ} (hh : 0 < h) (hh0 : h ≤ 1 / (8 * ((k : ℝ) + 1)))
    (idx : Fin k → Fin d) :
    (∀ l, ‖(h • (EuclideanSpace.single (idx l) (1 : ℝ) : Euc d))‖ = h) ∧
    ∑ l, ‖(h • (EuclideanSpace.single (idx l) (1 : ℝ) : Euc d))‖ ≤ 1 / 8 ∧
    ∏ l : Fin k, ‖(h • (EuclideanSpace.single (idx l) (1 : ℝ) : Euc d))‖ = h ^ k := by
  have hn : ∀ l, ‖(h • (EuclideanSpace.single (idx l) (1 : ℝ) : Euc d))‖ = h := fun l => by
    simp [norm_smul, abs_of_pos hh]
  refine ⟨hn, ?_, ?_⟩
  · simp only [hn, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hi0 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    calc (k : ℝ) * h ≤ ((k : ℝ) + 1) * (1 / (8 * ((k : ℝ) + 1))) :=
          mul_le_mul (by linarith) hh0 hh.le hi0.le
      _ = 1 / 8 := by field_simp
  · simp only [hn, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem s103c_avg_bd {N : ℕ} {B e l : ℝ} (hel : e ≤ l) (hB : 0 ≤ B) {g : ℝ → Euc d → ℝ}
    (hint : ∀ y, IntervalIntegrable (fun σ => g σ y) volume e l)
    (hg : ∀ σ ∈ Set.Icc e l, Bd N B (g σ))
    {G : Euc d → ℝ} (hG : ContDiff ℝ (N : WithTop ℕ∞) G) (hGeq : ∀ y, G y = ∫ σ in e..l, g σ y) :
    Bd N ((max 1 (d : ℝ)) ^ N * B * (l - e)) G := by
  refine ⟨hG, fun i hi x => ?_⟩
  have hGe : G = fun y => ∫ σ in e..l, g σ y := funext hGeq
  have hBl : 0 ≤ B * (l - e) := mul_nonneg hB (sub_nonneg.2 hel)
  have hGi : ContDiff ℝ (i : WithTop ℕ∞) G := hG.of_le (by exact_mod_cast hi)
  have hmain : ‖iteratedFDeriv ℝ i G x‖ ≤ (d : ℝ) ^ i * (B * (l - e)) := by
    refine s103c_iter_le_of_dpF hGi hBl x fun h hh hh0 idx => ?_
    obtain ⟨hn, hsum, hprod⟩ := s103c_steps_small hh hh0 idx
    set m : Fin i → Euc d := fun l => h • (EuclideanSpace.single (idx l) (1 : ℝ) : Euc d) with hm
    obtain ⟨-, hi2⟩ := s103b_dpF_integral (r := e) (t := l) hint i m
    rw [hGe, hi2 x]
    have hb : ∀ σ ∈ Set.uIoc e l, ‖s8f_dpF i m (g σ) x‖ ≤ B * h ^ i := by
      intro σ hσ
      have hσ' : σ ∈ Set.Icc e l := by
        rw [Set.uIoc_of_le hel] at hσ; exact ⟨hσ.1.le, hσ.2⟩
      have hgi : ContDiff ℝ (i : WithTop ℕ∞) (g σ) := (hg σ hσ').1.of_le (by exact_mod_cast hi)
      have := s103c_dpF_bound 0 hB hgi (fun j hj y => by simpa using (hg σ hσ').2 j (hj.trans hi) y) m hsum x
      rw [Real.norm_eq_abs]
      simp only [pow_zero, one_pow, mul_one] at this
      rw [hprod] at this
      exact this
    have := intervalIntegral.norm_integral_le_of_norm_le_const hb
    rw [Real.norm_eq_abs] at this
    refine this.trans (le_of_eq ?_)
    rw [abs_of_nonneg (sub_nonneg.2 hel)]; ring
  refine hmain.trans ?_
  have hd1 : (1 : ℝ) ≤ max 1 (d : ℝ) := le_max_left _ _
  have hdi : (d : ℝ) ^ i ≤ (max 1 (d : ℝ)) ^ N :=
    (pow_le_pow_left₀ (Nat.cast_nonneg d) (le_max_right _ _) i).trans (pow_le_pow_right₀ hd1 hi)
  calc (d : ℝ) ^ i * (B * (l - e)) ≤ (max 1 (d : ℝ)) ^ N * (B * (l - e)) :=
        mul_le_mul_of_nonneg_right hdi hBl
    _ = _ := by ring

theorem s103c_dpF_hasDeriv {S : Set ℝ} {σ₀ : ℝ} {u u' : ℝ → Euc d → ℝ}
    (h : ∀ y, HasDerivWithinAt (fun σ => u σ y) (u' σ₀ y) S σ₀) :
    ∀ (k : ℕ) (m : Fin k → Euc d) (x : Euc d),
      HasDerivWithinAt (fun σ => s8f_dpF k m (u σ) x) (s8f_dpF k m (u' σ₀) x) S σ₀ := by
  intro k
  induction k with
  | zero => intro m x; exact h x
  | succ k ih =>
    intro m x
    exact (ih (Fin.init m) (x + m (Fin.last k))).sub (ih (Fin.init m) x)

theorem s103c_dpF_contOn {S : Set ℝ} {u : ℝ → Euc d → ℝ}
    (h : ∀ y, ContinuousOn (fun σ => u σ y) S) :
    ∀ (k : ℕ) (m : Fin k → Euc d) (x : Euc d), ContinuousOn (fun σ => s8f_dpF k m (u σ) x) S := by
  intro k
  induction k with
  | zero => intro m x; exact h x
  | succ k ih =>
    intro m x
    exact (ih (Fin.init m) (x + m (Fin.last k))).sub (ih (Fin.init m) x)

theorem s103c_rho_lip {K L : ℕ} {A : ℝ} (hA : 0 ≤ A) {ρ ρ' : ℝ → Euc d → ℝ}
    (hder : ∀ t, 0 ≤ t → ∀ x, HasDerivWithinAt (fun τ => ρ τ x) (ρ' t x) (Set.Ici t) t)
    (hcont : ∀ x, ContinuousOn (fun τ => ρ τ x) (Set.Ici 0))
    (hC : ∀ t, 0 ≤ t → ContDiff ℝ (K : WithTop ℕ∞) (ρ t))
    (hD : ∀ t, 0 ≤ t → U2Dec K (L : ℝ) A (ρ' t)) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    U2Dec K (L : ℝ) (((max 1 (d : ℝ)) ^ K * ((5 / 4 : ℝ) ^ L) ^ K) * A * (b - a)) (fun y => ρ b y - ρ a y) := by
  have hb0 : 0 ≤ b := ha.trans hab
  have hδ : ContDiff ℝ (K : WithTop ℕ∞) (fun y => ρ b y - ρ a y) := (hC b hb0).sub (hC a ha)
  refine ⟨hδ, fun j hj x => ?_⟩
  have hc1 : (1 : ℝ) ≤ (5 / 4 : ℝ) ^ L := one_le_pow₀ (by norm_num)
  have hwL' : ∀ y : Euc d, u2Wt (L : ℝ) y = ((1 + ‖y‖)⁻¹) ^ L := by
    intro y
    unfold u2Wt
    rw [Real.rpow_neg (by positivity), Real.rpow_natCast, inv_pow]
  rw [hwL' x]
  have hw0 : 0 ≤ ((1 + ‖x‖)⁻¹) ^ L := by positivity
  have hBnn : 0 ≤ A * ((5 / 4 : ℝ) ^ L) ^ j * ((1 + ‖x‖)⁻¹) ^ L * (b - a) := by
    have := sub_nonneg.2 hab
    positivity
  have hδj : ContDiff ℝ (j : WithTop ℕ∞) (fun y => ρ b y - ρ a y) := hδ.of_le (by exact_mod_cast hj)
  have hmain : ‖iteratedFDeriv ℝ j (fun y => ρ b y - ρ a y) x‖ ≤
      (d : ℝ) ^ j * (A * ((5 / 4 : ℝ) ^ L) ^ j * ((1 + ‖x‖)⁻¹) ^ L * (b - a)) := by
    refine s103c_iter_le_of_dpF hδj hBnn x fun h hh hh0 idx => ?_
    obtain ⟨hn, hsum, hprod⟩ := s103c_steps_small hh hh0 idx
    set m : Fin j → Euc d := fun l => h • (EuclideanSpace.single (idx l) (1 : ℝ) : Euc d) with hm
    have hsub : s8f_dpF j m (fun y => ρ b y - ρ a y) x = s8f_dpF j m (ρ b) x - s8f_dpF j m (ρ a) x := by
      have := s103b_dpF_add j m (ρ b) (fun y => -ρ a y) x
      have hneg : ∀ (k : ℕ) (m : Fin k → Euc d) (g : Euc d → ℝ) (y : Euc d),
          s8f_dpF k m (fun y => -g y) y = - s8f_dpF k m g y := by
        intro k
        induction k with
        | zero => intro m g y; rfl
        | succ k ih => intro m g y; show s8f_dpF k (Fin.init m) (fun y => -g y) _ - s8f_dpF k (Fin.init m) (fun y => -g y) _ = _
                       rw [ih, ih]; show _ = -(s8f_dpF k (Fin.init m) g _ - s8f_dpF k (Fin.init m) g _); ring
      rw [hneg] at this
      simpa [sub_eq_add_neg] using this
    rw [hsub]
    set φ : ℝ → ℝ := fun σ => s8f_dpF j m (ρ σ) x with hφ
    have hφc : ContinuousOn φ (Set.Icc a b) :=
      (s103c_dpF_contOn hcont j m x).mono (fun σ hσ => ha.trans hσ.1)
    have hφd : ∀ σ ∈ Set.Ico a b, HasDerivWithinAt φ (s8f_dpF j m (ρ' σ) x) (Set.Ici σ) σ := fun σ hσ =>
      s103c_dpF_hasDeriv (S := Set.Ici σ) (u := ρ) (u' := ρ') (σ₀ := σ) (fun y => hder σ (ha.trans hσ.1) y) j m x
    have hφb : ∀ σ ∈ Set.Ico a b, ‖s8f_dpF j m (ρ' σ) x‖ ≤
        A * ((5 / 4 : ℝ) ^ L) ^ j * h ^ j * ((1 + ‖x‖)⁻¹) ^ L := by
      intro σ hσ
      have h0 := hD σ (ha.trans hσ.1)
      have := s103c_dpF_bound L hA (h0.1.of_le (by exact_mod_cast hj)) (fun i hi y => by
        have := h0.2 i (hi.trans hj) y
        rwa [hwL' y] at this) m hsum x
      rw [Real.norm_eq_abs]
      rw [hprod] at this
      exact this.trans (le_of_eq (by ring))
    have := norm_image_sub_le_of_norm_deriv_right_le_segment hφc hφd hφb b ⟨hab, le_rfl⟩
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_of_eq (by ring))
  refine hmain.trans ?_
  have hdi : (d : ℝ) ^ j ≤ (max 1 (d : ℝ)) ^ K :=
    (pow_le_pow_left₀ (Nat.cast_nonneg d) (le_max_right _ _) j).trans
      (pow_le_pow_right₀ (le_max_left _ _) hj)
  have hcj : ((5 / 4 : ℝ) ^ L) ^ j ≤ ((5 / 4 : ℝ) ^ L) ^ K := pow_le_pow_right₀ hc1 hj
  have hba := sub_nonneg.2 hab
  calc (d : ℝ) ^ j * (A * ((5 / 4 : ℝ) ^ L) ^ j * ((1 + ‖x‖)⁻¹) ^ L * (b - a))
      ≤ (max 1 (d : ℝ)) ^ K * (A * ((5 / 4 : ℝ) ^ L) ^ K * ((1 + ‖x‖)⁻¹) ^ L * (b - a)) := by
        gcongr
    _ = _ := by ring

end HRS.MS.R2WinOrbNL

end
