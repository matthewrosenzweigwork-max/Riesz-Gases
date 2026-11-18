import HRS.MS.SA16TCo3
import HRS.MS.SA16PForce6
import HRS.MS.SA16SOp2

/-!
# S.A.16 (SA16T) Co4: the smoothed drift as an `SA16BddCoef`, and its pointwise convergence

For a vector field `b ∈ C^k` with `‖b 0‖ ≤ C0` and `‖D^j b‖ ≤ L` (`1 ≤ j ≤ k`), the components `χ_{n+1} (ρ_n ⋆ b_i)` form an
`SA16BddCoef k Bn` for every `n`, with the derivatives of order `≥ 1` bounded uniformly in `n` (`sa16t_Bu`), and
`|f_n(x)| ≤ C0 + L (|x|+1)`; `f_n(x) → b_i(x)` and `∂_l f_n(x) → ∂_l b_i(x)` pointwise.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff Convolution

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16

section Co4
variable {d : ℕ}

/-- the components of the smoothed, cut-off vector field -/
def sa16t_bcv (d n : ℕ) (b : Euc d → Euc d) : Fin d → Euc d → ℝ :=
  fun i => sa16t_bc d n (fun y => b y i)

lemma sa16t_bc_abs {g : Euc d → ℝ} (hg : Continuous g) {C0 L : ℝ} (hC0 : 0 ≤ C0) (hL : 0 ≤ L) (hgl : ∀ y, |g y| ≤ C0 + L * ‖y‖)
    (n : ℕ) (x : Euc d) : |sa16t_bc d n g x| ≤ C0 + L * (‖x‖ + 1) := by
  simp only [sa16t_bc, abs_mul]
  have h1 : |sa16j_chi d (sa16t_R n) x| ≤ 1 := by
    rw [abs_of_nonneg (by exact (sa16j_bump d).nonneg)]; exact (sa16j_bump d).le_one
  calc |sa16j_chi d (sa16t_R n) x| * |sa16j_conv (sa16y_rho d n) g x| ≤ 1 * (C0 + L * (‖x‖ + 1)) :=
        mul_le_mul h1 (sa16t_mollify_growth hC0 hL hgl n x) (abs_nonneg _) (by norm_num)
    _ = _ := one_mul _

lemma sa16t_bc_eventually_eq (g : Euc d → ℝ) (n : ℕ) {x : Euc d} (hx : ‖x‖ < sa16t_R n) :
    sa16t_bc d n g =ᶠ[𝓝 x] sa16j_conv (sa16y_rho d n) g := by
  have hR0 : 0 < sa16t_R n := by linarith [norm_nonneg x]
  filter_upwards [Metric.isOpen_ball.mem_nhds (show x ∈ Metric.ball (0 : Euc d) (sa16t_R n) by simpa using hx)]
    with y hy
  simp [sa16t_bc, sa16j_chi_one d hR0 (mem_ball_zero_iff.1 hy).le]

lemma sa16t_bc_tendsto {g : Euc d → ℝ} (hg : Continuous g) (x : Euc d) :
    Tendsto (fun n => sa16t_bc d n g x) atTop (𝓝 (g x)) := by
  refine (sa16y_mollify_tendsto hg x).congr' ?_
  filter_upwards [eventually_gt_atTop ⌈‖x‖⌉₊] with n hn
  have : ‖x‖ < sa16t_R n := by
    have h1 : ‖x‖ ≤ (⌈‖x‖⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈‖x‖⌉₊ : ℝ) < n := by exact_mod_cast hn
    unfold sa16t_R; linarith
  exact ((sa16t_bc_eventually_eq g n this).self_of_nhds).symm

lemma sa16t_pd1_tendsto {g : Euc d → ℝ} (hg : ContDiff ℝ 1 g) (i : Fin d) (x : Euc d) :
    Tendsto (fun n => partialDeriv (fun _ : Fin 1 => i) (sa16t_bc d n g) x) atTop
      (𝓝 (partialDeriv (fun _ : Fin 1 => i) g x)) := by
  have hg' : ContDiff ℝ ((1 + 0 : ℕ) : WithTop ℕ∞) g := by simpa using hg
  have hpc : Continuous (partialDeriv (fun _ : Fin 1 => i) g) := (sa16y_pd_contDiffN hg' _).continuous
  refine (sa16y_mollify_tendsto hpc x).congr' ?_
  filter_upwards [eventually_gt_atTop ⌈‖x‖⌉₊] with n hn
  have hlt : ‖x‖ < sa16t_R n := by
    have h1 : ‖x‖ ≤ (⌈‖x‖⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈‖x‖⌉₊ : ℝ) < n := by exact_mod_cast hn
    unfold sa16t_R; linarith
  have hsupp : ∀ z, 1 / ((n : ℝ) + 1) < ‖z‖ → sa16y_rho d n z = 0 := fun z hz => sa16y_rho_supp n z hz
  have h1 := sa16y_conv_pdN hsupp (by positivity) (sa16y_rho_integrable n) 1 0 (fun _ : Fin 1 => i) g hg'
  have h2 : partialDeriv (fun _ : Fin 1 => i) (sa16t_bc d n g) x =
      partialDeriv (fun _ : Fin 1 => i) (sa16j_conv (sa16y_rho d n) g) x := by
    unfold partialDeriv
    rw [((sa16t_bc_eventually_eq g n hlt).iteratedFDeriv ℝ 1).self_of_nhds]
  rw [h2, h1]

lemma sa16t_comp_bounds {b : Euc d → Euc d} {k : ℕ} (hb : ContDiff ℝ k b) (i : Fin d) {j : ℕ} (hjk : j ≤ k)
    (y : Euc d) : ‖iteratedFDeriv ℝ j (fun y => b y i) y‖ ≤ ‖iteratedFDeriv ℝ j b y‖ := by
  set P : Euc d →L[ℝ] ℝ := EuclideanSpace.proj i with hP
  have hproj : ‖P‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun v => by
      simpa [hP, Real.norm_eq_abs] using PiLp.norm_apply_le v i)
  have hfun : (fun y => b y i) = P ∘ b := rfl
  rw [hfun]
  have h := P.norm_iteratedFDeriv_comp_left (hb.contDiffAt (x := y)) (by exact_mod_cast hjk)
  exact h.trans (mul_le_of_le_one_left (norm_nonneg _) hproj)

theorem sa16t_coef_vec (d k : ℕ) (hk : 1 ≤ k) :
    ∃ Bχ : ℝ, 0 ≤ Bχ ∧ ∀ (b : Euc d → Euc d) (C0 L : ℝ), 0 ≤ C0 → 0 ≤ L → ContDiff ℝ k b → ‖b 0‖ ≤ C0 →
      (∀ j, 1 ≤ j → j ≤ k → ∀ x, ‖iteratedFDeriv ℝ j b x‖ ≤ L) → ∀ n : ℕ,
        SA16BddCoef k (max (C0 + L * (2 * sa16t_R n + 1)) (sa16t_Bu Bχ d k C0 L)) (sa16t_bcv d n b) ∧
        (∀ i, ∀ j, 1 ≤ j → j ≤ k → ∀ x, ‖iteratedFDeriv ℝ j (sa16t_bcv d n b i) x‖ ≤ sa16t_Bu Bχ d k C0 L) ∧
        ∀ i x, |sa16t_bcv d n b i x| ≤ C0 + L * (‖x‖ + 1) := by
  obtain ⟨Bχ, hB0, H⟩ := sa16t_bc_bounds d k
  refine ⟨Bχ, hB0, fun b C0 L hC0 hL hb hb0 hbd n => ?_⟩
  have hgrow : ∀ y, ‖b y‖ ≤ C0 + L * ‖y‖ := by
    have hdiff : Differentiable ℝ b := hb.differentiable (by exact_mod_cast Nat.one_le_iff_ne_zero.1 hk)
    have hf : ∀ y, ‖fderiv ℝ b y‖ ≤ L := fun y => by
      rw [Phase2SA16P.sa16p_norm_fderiv_eq]; exact hbd 1 le_rfl hk y
    intro y
    have := Phase2SA16P.sa16p_mvt hdiff hf 0 y
    rw [sub_zero] at this
    calc ‖b y‖ ≤ ‖b 0‖ + ‖b y - b 0‖ := by
          have := norm_add_le (b 0) (b y - b 0); simpa using this
      _ ≤ C0 + L * ‖y‖ := add_le_add hb0 this
  have hcomp : ∀ i : Fin d, ContDiff ℝ k (fun y => b y i) := fun i =>
    (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).contDiff.comp hb
  have hgl : ∀ i : Fin d, ∀ y, |b y i| ≤ C0 + L * ‖y‖ := fun i y => by
    have : |b y i| ≤ ‖b y‖ := by simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (b y) i
    exact this.trans (hgrow y)
  have hgb : ∀ i : Fin d, ∀ j, 1 ≤ j → j ≤ k → ∀ y, ‖iteratedFDeriv ℝ j (fun y => b y i) y‖ ≤ L :=
    fun i j hj1 hjk y => (sa16t_comp_bounds hb i hjk y).trans (hbd j hj1 hjk y)
  have hmain := fun i : Fin d => H (fun y => b y i) C0 L hC0 hL (hcomp i) (hgl i) (hgb i) n
  set R := sa16t_R n
  have hBu0 : 0 ≤ sa16t_Bu Bχ d k C0 L := by unfold sa16t_Bu; positivity
  refine ⟨⟨?_, fun i => (hmain i).1, ?_⟩,
    fun i j hj1 hjk x => (hmain i).2.2 j hj1 hjk x, fun i x => ?_⟩
  · exact (add_nonneg hC0 (mul_nonneg hL (by linarith [sa16t_R_ge n]))).trans (le_max_left _ _)
  · intro i j hj x
    rcases Nat.eq_zero_or_pos j with h0 | hpos
    · subst h0
      rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
      exact ((hmain i).2.1 x).trans (le_max_left _ _)
    · exact ((hmain i).2.2 j hpos hj x).trans (le_max_right _ _)
  · exact sa16t_bc_abs (hcomp i).continuous hC0 hL (hgl i) n x

end Co4

end HRS.Whole.AppendixA.Phase2SA16R
