import HRS.MS.SA16TCo2

/-!
# S.A.16 (SA16T) Co3: `sa16t_bc` depends continuously on `g` (sup norm on a ball), derivatives included

`sa16t_bc_small`: for fixed `n, k` there is `Cn` with `‖D^j (χ_{n+1} (ρ_n ⋆ G))‖ ≤ Cn A` whenever `|G| ≤ A` on the ball
of radius `2 (n+1) + 1` (`j ≤ k`).  `sa16t_bc_sub`: `sa16t_bc` is linear in `g`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff Convolution

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16

section Co3
variable {d : ℕ}

lemma sa16t_rho_cc (n : ℕ) : IsCcInfty (sa16y_rho d n) := ⟨sa16y_rho_smooth n, sa16y_rho_compact n⟩

lemma sa16t_pd_rho_supp (n : ℕ) {j : ℕ} (r : Fin j → Fin d) (z : Euc d) (hz : 1 < ‖z‖) :
    partialDeriv r (sa16y_rho d n) z = 0 := by
  by_contra hne
  have hne' : iteratedFDeriv ℝ j (sa16y_rho d n) z ≠ 0 := by
    intro h0
    apply hne
    unfold partialDeriv
    rw [h0]; rfl
  have h2 : z ∈ tsupport (sa16y_rho d n) := support_iteratedFDeriv_subset (𝕜 := ℝ) (f := sa16y_rho d n) j hne'
  have h3 : tsupport (sa16y_rho d n) ⊆ closedBall (0 : Euc d) (1 / ((n : ℝ) + 1)) := by
    refine closure_minimal (fun y hy => ?_) isClosed_closedBall
    by_contra hn
    rw [mem_closedBall_zero_iff, not_le] at hn
    exact hy (sa16y_rho_supp n y hn)
  have h4 := h3 h2
  rw [mem_closedBall_zero_iff] at h4
  have : 1 / ((n : ℝ) + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith [n.cast_nonneg (α := ℝ)]
  linarith

/-- the constant `∑_{j ≤ k} ∑_r ∫ |∂^r ρ_n|` -/
def sa16t_Crho (d n k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (k + 1), ∑ r : Fin j → Fin d, ∫ z, |partialDeriv r (sa16y_rho d n) z|

lemma sa16t_Crho_nonneg (d n k : ℕ) : 0 ≤ sa16t_Crho d n k :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => abs_nonneg _

lemma sa16t_mollify_small {G : Euc d → ℝ} (hG : Continuous G) (n k : ℕ) {A : ℝ} (x : Euc d)
    (hA : ∀ z, ‖z‖ ≤ 1 → |G (x - z)| ≤ A) {j : ℕ} (hj : j ≤ k) :
    ‖iteratedFDeriv ℝ j (sa16j_conv (sa16y_rho d n) G) x‖ ≤ sa16t_Crho d n k * A := by
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA 0 (by simp))
  have hsm : ∀ r : Fin j → Fin d, ‖partialDeriv r (sa16j_conv (sa16y_rho d n) G) x‖ ≤
      (∫ z, |partialDeriv r (sa16y_rho d n) z|) * A := by
    intro r
    rw [sa16t_pd_conv_kernel (sa16t_rho_cc n) hG j r x]
    exact sa16t_conv_le (k := partialDeriv r (sa16y_rho d n)) (u := G) (R := 1) (A := A)
      (Continuous.integrable_of_hasCompactSupport (sa16s_cc_partialDeriv (sa16t_rho_cc n) r).1.continuous
        (sa16s_cc_partialDeriv (sa16t_rho_cc n) r).2)
      (fun z hz => sa16t_pd_rho_supp n r z hz) x hA
  refine (sa16j_norm_iter_le _ x j).trans ?_
  calc ∑ r : Fin j → Fin d, |partialDeriv r (sa16j_conv (sa16y_rho d n) G) x|
      ≤ ∑ r : Fin j → Fin d, (∫ z, |partialDeriv r (sa16y_rho d n) z|) * A :=
        Finset.sum_le_sum fun r _ => by simpa [Real.norm_eq_abs] using hsm r
    _ = (∑ r : Fin j → Fin d, ∫ z, |partialDeriv r (sa16y_rho d n) z|) * A := by rw [Finset.sum_mul]
    _ ≤ sa16t_Crho d n k * A := by
        refine mul_le_mul_of_nonneg_right ?_ hA0
        unfold sa16t_Crho
        exact Finset.single_le_sum (f := fun j => ∑ r : Fin j → Fin d, ∫ z, |partialDeriv r (sa16y_rho d n) z|)
          (fun _ _ => Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => abs_nonneg _)
          (Finset.mem_range.2 (by omega))

theorem sa16t_bc_small (d k n : ℕ) :
    ∃ Cn : ℝ, 0 ≤ Cn ∧ ∀ G : Euc d → ℝ, Continuous G → ∀ A : ℝ, (∀ y, ‖y‖ ≤ 2 * sa16t_R n + 1 → |G y| ≤ A) →
      ∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j (sa16t_bc d n G) x‖ ≤ Cn * A := by
  obtain ⟨Bχ, hB0, hBχ⟩ := sa16j_cut_bound d k
  refine ⟨2 ^ k * (max 1 Bχ * sa16t_Crho d n k), by have := sa16t_Crho_nonneg d n k; positivity,
    fun G hG A hA j hjk x => ?_⟩
  have hR1 := sa16t_R_ge n
  have hR0 : 0 < sa16t_R n := by linarith
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA 0 (by simp; linarith))
  have hhs : ContDiff ℝ ∞ (sa16j_conv (sa16y_rho d n) G) := sa16y_mollify_smooth n hG
  have hχs := sa16j_chi_contDiff d (sa16t_R n)
  have hbc : sa16t_bc d n G = fun x => sa16j_chi d (sa16t_R n) x * sa16j_conv (sa16y_rho d n) G x := rfl
  have hKu0 : 0 ≤ max 1 Bχ * sa16t_Crho d n k * A := by
    have := sa16t_Crho_nonneg d n k; positivity
  by_cases hx : 2 * sa16t_R n < ‖x‖
  · rw [hbc, sa16t_vanish hR0 _ hx j, norm_zero]
    have := sa16t_Crho_nonneg d n k; positivity
  · push Not at hx
    have hL' := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (hχs.of_le (by exact_mod_cast le_top))
      (hhs.of_le (by exact_mod_cast le_top)) x (n := j) (N := (j : ℕ∞ω)) le_rfl
    rw [hbc]
    refine hL'.trans ?_
    have hterm : ∀ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i (sa16j_chi d (sa16t_R n)) x‖ *
        ‖iteratedFDeriv ℝ (j - i) (sa16j_conv (sa16y_rho d n) G) x‖ ≤
        (j.choose i : ℝ) * (max 1 Bχ * sa16t_Crho d n k * A) := by
      intro i hi
      have hi' : i ≤ j := by have := Finset.mem_range.1 hi; omega
      rw [mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
      have h1 := hBχ (sa16t_R n) hR1 i (hi'.trans hjk) x
      have h2 := sa16t_mollify_small hG n k (A := A) x (fun z hz => hA _ (by
        calc ‖x - z‖ ≤ ‖x‖ + ‖z‖ := norm_sub_le _ _
          _ ≤ 2 * sa16t_R n + 1 := by linarith)) (j := j - i) (by omega)
      calc ‖iteratedFDeriv ℝ i (sa16j_chi d (sa16t_R n)) x‖ *
            ‖iteratedFDeriv ℝ (j - i) (sa16j_conv (sa16y_rho d n) G) x‖
          ≤ max 1 Bχ * (sa16t_Crho d n k * A) :=
            mul_le_mul (h1.trans (le_max_right _ _)) h2 (norm_nonneg _) (by positivity)
        _ = _ := by ring
    calc ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i (sa16j_chi d (sa16t_R n)) x‖ *
          ‖iteratedFDeriv ℝ (j - i) (sa16j_conv (sa16y_rho d n) G) x‖
        ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * (max 1 Bχ * sa16t_Crho d n k * A) :=
          Finset.sum_le_sum hterm
      _ = 2 ^ j * (max 1 Bχ * sa16t_Crho d n k * A) := by
          rw [← Finset.sum_mul]
          have : ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) = 2 ^ j := by
            exact_mod_cast Nat.sum_range_choose j
          rw [this]
      _ ≤ 2 ^ k * (max 1 Bχ * sa16t_Crho d n k) * A := by
          rw [mul_assoc (2 ^ k)]
          calc 2 ^ j * (max 1 Bχ * sa16t_Crho d n k * A) ≤ 2 ^ k * (max 1 Bχ * sa16t_Crho d n k * A) :=
                mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hjk) hKu0
            _ = _ := by ring

lemma sa16t_conv_int {g : Euc d → ℝ} (hg : Continuous g) (n : ℕ) (x : Euc d) :
    Integrable (fun z => sa16y_rho d n z * g (x - z)) := by
  refine (((sa16y_rho_smooth n).continuous.mul (hg.comp (continuous_const.sub continuous_id)))).integrable_of_hasCompactSupport ?_
  exact (sa16y_rho_compact n).mul_right

lemma sa16t_conv_sub {g h : Euc d → ℝ} (hg : Continuous g) (hh : Continuous h) (n : ℕ) :
    sa16j_conv (sa16y_rho d n) (fun y => g y - h y) =
      fun x => sa16j_conv (sa16y_rho d n) g x - sa16j_conv (sa16y_rho d n) h x := by
  funext x
  unfold sa16j_conv
  rw [← integral_sub (sa16t_conv_int hg n x) (sa16t_conv_int hh n x)]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only [mul_sub]

lemma sa16t_bc_sub {g h : Euc d → ℝ} (hg : Continuous g) (hh : Continuous h) (n : ℕ) :
    sa16t_bc d n (fun y => g y - h y) = fun x => sa16t_bc d n g x - sa16t_bc d n h x := by
  funext x
  unfold sa16t_bc
  rw [sa16t_conv_sub hg hh n]
  ring

end Co3

end HRS.Whole.AppendixA.Phase2SA16R
