import HRS.Commutator.Whole.ExternalAuxMult3

/-!
# X-MULT auxiliary (4): the Bessel symbol `(1+4π²|ξ|²)^{α/2}(1-χ)|2πξ|^{-α} - (1-χ)`

`cmxMY_mult_kernel_bessel`: the symbol minus `1 - χ` equals `(1-χ) W ν(W)` with `W = (2π|ξ|)^{-2}` and
`ν(y) = ((1+y)^p - 1)/y` (analytic, `p = α/2`).  Its dyadic pieces `ρ · w̃ · ν(ε w̃)`, `ε = 4^{-j}`, are
bounded in `C^n` uniformly in `j` (Faà di Bruno, `norm_iteratedFDeriv_comp_le'`), so `cmxMY_LP`
(with `γ = 2 < d`) gives the kernel.  Names prefixed `cmxMY_`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff

namespace HRS.Commutator.Whole

open HRS HRS.Whole

variable {d : ℕ}

/-- `ν(y) = ((1+y)^p - 1)/y`, `ν(0) = p`. -/
def cmxMY_nu (p : ℝ) : ℝ → ℝ := dslope (fun y : ℝ => (1 + y) ^ p) 0

lemma cmxMY_nu_mul (p : ℝ) (y : ℝ) : y * cmxMY_nu p y = (1 + y) ^ p - 1 := by
  have := sub_smul_dslope (fun y : ℝ => (1 + y) ^ p) 0 y
  simp only [sub_zero, smul_eq_mul, add_zero] at this
  simpa [cmxMY_nu] using this

lemma cmxMY_nu_contDiffAt (p : ℝ) {y : ℝ} (hy : -1 < y) : ContDiffAt ℝ ∞ (cmxMY_nu p) y := by
  by_cases h0 : y = 0
  · subst h0
    have h1 := Real.one_add_rpow_hasFPowerSeriesAt_zero (a := p)
    have h2 := h1.has_fpower_series_dslope_fslope
    exact h2.analyticAt.contDiffAt
  · have hev : cmxMY_nu p =ᶠ[𝓝 y] fun z : ℝ => ((1 + z) ^ p - 1) / z := by
      filter_upwards [isOpen_ne.mem_nhds h0] with z hz
      rw [cmxMY_nu, dslope_of_ne _ hz, slope_def_field]
      simp
    refine ContDiffAt.congr_of_eventuallyEq ?_ hev
    refine ContDiffAt.div ?_ contDiffAt_id h0
    exact (ContDiffAt.rpow_const_of_ne (contDiffAt_const.add contDiffAt_id) (by simp only [id]; linarith)).sub contDiffAt_const

lemma cmxMY_contDiff_of_away_real {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : Euc d → E}
    {r : ℝ} (hr : 0 < r) (hf : ∀ η : Euc d, η ≠ 0 → ContDiffAt ℝ ∞ f η)
    (hz : ∀ η : Euc d, ‖η‖ < r → f η = 0) : ContDiff ℝ ∞ f := by
  rw [contDiff_iff_contDiffAt]
  intro η
  by_cases h : η = 0
  · subst h
    have : f =ᶠ[𝓝 (0 : Euc d)] fun _ => (0 : E) := by
      filter_upwards [Metric.ball_mem_nhds (0 : Euc d) hr] with y hy
      exact hz y (by simpa using hy)
    exact contDiffAt_const.congr_of_eventuallyEq this
  · exact hf η h

/-- `w̃(η) = (1 - χ(4η)) / (2π|η|)²`, smooth everywhere (zero near `0`). -/
def cmxMY_wt (η : Euc d) : ℝ := (1 - chi ((4 : ℝ) • η)) * ((2 * Real.pi * ‖η‖) ^ 2)⁻¹

lemma cmxMY_wt_contDiff : ContDiff ℝ ∞ (cmxMY_wt : Euc d → ℝ) := by
  refine cmxMY_contDiff_of_away_real (r := 1 / 4) (by norm_num) (fun η hη => ?_) (fun η hη => ?_)
  · unfold cmxMY_wt
    refine ContDiffAt.mul ?_ ?_
    · exact (contDiffAt_const.sub (cmxFB_chi_contDiff.comp (contDiff_const_smul _)).contDiffAt)
    · have h1 : ContDiffAt ℝ ∞ (fun η : Euc d => (2 * Real.pi * ‖η‖) ^ 2) η :=
        (contDiffAt_const.mul (contDiffAt_norm ℝ hη)).pow 2
      exact h1.inv (by positivity)
  · unfold cmxMY_wt
    rw [cmxFB_chi_one (by rw [norm_smul]; simp; linarith)]
    simp

lemma cmxMY_wt_eq {η : Euc d} (h : 1 / 2 ≤ ‖η‖) : cmxMY_wt η = ((2 * Real.pi * ‖η‖) ^ 2)⁻¹ := by
  unfold cmxMY_wt
  rw [cmxFB_chi_zero (by rw [norm_smul]; simp; linarith)]
  simp

lemma cmxMY_wt_nonneg (η : Euc d) : 0 ≤ cmxMY_wt η := by
  unfold cmxMY_wt
  have := cmxFB_chi_le_one ((4 : ℝ) • η)
  exact mul_nonneg (by linarith) (by positivity)

lemma cmxMY_wt_le (η : Euc d) : cmxMY_wt η ≤ 1 / 2 := by
  unfold cmxMY_wt
  by_cases h : ‖η‖ ≤ 1 / 4
  · rw [cmxFB_chi_one (by rw [norm_smul]; simp; linarith)]
    simp
  · push Not at h
    have h1 := cmxFB_chi_nonneg ((4 : ℝ) • η)
    have h2 : (1 - chi ((4 : ℝ) • η)) ≤ 1 := by linarith
    have h3 : ((2 * Real.pi * ‖η‖) ^ 2)⁻¹ ≤ 1 / 2 := by
      rw [inv_le_comm₀ (by positivity) (by norm_num)]
      have : Real.pi * ‖η‖ * 2 > 3 * (1 / 4) * 2 := by
        have := Real.pi_gt_three
        nlinarith
      nlinarith [Real.pi_gt_three]
    calc (1 - chi ((4 : ℝ) • η)) * ((2 * Real.pi * ‖η‖) ^ 2)⁻¹ ≤ 1 * (1 / 2) :=
          mul_le_mul h2 h3 (by positivity) (by norm_num)
      _ = 1 / 2 := one_mul _

lemma cmxMY_bdd_ball {E : Type*} [NormedAddCommGroup E] (f : Euc d → E) (hf : Continuous f) (R : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ η : Euc d, ‖η‖ ≤ R → ‖f η‖ ≤ B := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : Euc d) R).exists_bound_of_continuousOn hf.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun η hη => ?_⟩
  exact (hC η (by simpa using hη)).trans (le_max_left _ _)

lemma cmxMY_wt_deriv_bound (n : ℕ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ η : Euc d, ‖η‖ ≤ 2 →
    ‖iteratedFDeriv ℝ n (cmxMY_wt : Euc d → ℝ) η‖ ≤ B :=
  cmxMY_bdd_ball _ (cmxMY_wt_contDiff.continuous_iteratedFDeriv (by exact_mod_cast le_top)) 2

lemma cmxMY_nu_comp_bound (p : ℝ) (m : ℕ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 →
    ∀ η : Euc d, ‖η‖ ≤ 2 →
      ‖iteratedFDeriv ℝ m (fun η : Euc d => cmxMY_nu p (ε * cmxMY_wt η)) η‖ ≤ B := by
  set t : Set ℝ := Set.Ioo (-1 / 2 : ℝ) 1 with ht
  have ht' : UniqueDiffOn ℝ t := isOpen_Ioo.uniqueDiffOn
  have hg : ContDiffOn ℝ ∞ (cmxMY_nu p) t := fun y hy =>
    (cmxMY_nu_contDiffAt p (by linarith [hy.1])).contDiffWithinAt
  have hcomp : IsCompact (Set.Icc (0 : ℝ) (1 / 2)) := isCompact_Icc
  have hsub : Set.Icc (0 : ℝ) (1 / 2) ⊆ t := fun y hy => ⟨by linarith [hy.1], by linarith [hy.2]⟩
  -- bounds for the derivatives of `ν`
  have hCi : ∀ i : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ Set.Icc (0 : ℝ) (1 / 2),
      ‖iteratedFDerivWithin ℝ i (cmxMY_nu p) t y‖ ≤ C := by
    intro i
    have hc := hg.continuousOn_iteratedFDerivWithin (m := i) (by exact_mod_cast le_top) ht'
    obtain ⟨C, hC⟩ := hcomp.exists_bound_of_continuousOn (hc.mono hsub)
    exact ⟨max C 0, le_max_right _ _, fun y hy => (hC y hy).trans (le_max_left _ _)⟩
  choose C hC0 hC using hCi
  set Cν : ℝ := ∑ i ∈ Finset.range (m + 1), C i with hCν
  have hCν0 : 0 ≤ Cν := Finset.sum_nonneg fun i _ => hC0 i
  choose Bw hBw0 hBw using fun i : ℕ => cmxMY_wt_deriv_bound (d := d) i
  set D : ℝ := 1 + ∑ i ∈ Finset.range (m + 1), Bw i with hD
  have hD1 : 1 ≤ D := by
    rw [hD]; have : 0 ≤ ∑ i ∈ Finset.range (m + 1), Bw i := Finset.sum_nonneg fun i _ => hBw0 i
    linarith
  refine ⟨m.factorial * Cν * D ^ m, by positivity, fun ε hε0 hε1 η hη => ?_⟩
  have hf : ContDiff ℝ ∞ (fun η : Euc d => ε * cmxMY_wt η) := contDiff_const.mul cmxMY_wt_contDiff
  have hrange : Set.range (fun η : Euc d => ε * cmxMY_wt η) ⊆ t := by
    rintro _ ⟨η', rfl⟩
    refine ⟨?_, ?_⟩
    · have := cmxMY_wt_nonneg η'; nlinarith
    · have := cmxMY_wt_le η'; nlinarith
  have key := norm_iteratedFDeriv_comp_le' (𝕜 := ℝ) (g := cmxMY_nu p)
    (f := fun η : Euc d => ε * cmxMY_wt η) (n := m) (N := ∞) hrange ht' hg hf
    (by exact_mod_cast le_top) η (C := Cν) (D := D) ?_ ?_
  · exact key
  · intro i hi
    have hy : ε * cmxMY_wt η ∈ Set.Icc (0 : ℝ) (1 / 2) :=
      ⟨by have := cmxMY_wt_nonneg η; positivity, by have := cmxMY_wt_le η; nlinarith⟩
    calc ‖iteratedFDerivWithin ℝ i (cmxMY_nu p) t (ε * cmxMY_wt η)‖ ≤ C i := hC i _ hy
      _ ≤ Cν := Finset.single_le_sum (f := C) (fun j _ => hC0 j) (by simpa [Nat.lt_succ_iff] using hi)
  · intro i hi1 him
    have h1 : iteratedFDeriv ℝ i (fun η : Euc d => ε • cmxMY_wt η) η =
        ε • iteratedFDeriv ℝ i (cmxMY_wt : Euc d → ℝ) η :=
      iteratedFDeriv_const_smul_apply' ((cmxMY_wt_contDiff.of_le (by exact_mod_cast le_top)).contDiffAt)
    simp only [smul_eq_mul] at h1
    rw [h1, norm_smul, Real.norm_of_nonneg hε0]
    have h2 : ‖iteratedFDeriv ℝ i (cmxMY_wt : Euc d → ℝ) η‖ ≤ Bw i := hBw i η hη
    have h3 : Bw i ≤ D := by
      rw [hD]
      have : Bw i ≤ ∑ j ∈ Finset.range (m + 1), Bw j :=
        Finset.single_le_sum (f := Bw) (fun j _ => hBw0 j) (by simpa [Nat.lt_succ_iff] using him)
      linarith
    calc ε * ‖iteratedFDeriv ℝ i (cmxMY_wt : Euc d → ℝ) η‖ ≤ 1 * Bw i :=
          mul_le_mul hε1 h2 (norm_nonneg _) (by norm_num)
      _ ≤ D := by linarith
      _ ≤ D ^ i := by
          calc D = D ^ 1 := (pow_one D).symm
            _ ≤ D ^ i := pow_le_pow_right₀ hD1 hi1

lemma cmxMY_nuw_contDiff (p ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    ContDiff ℝ ∞ (fun η : Euc d => cmxMY_nu p (ε * cmxMY_wt η)) := by
  rw [contDiff_iff_contDiffAt]
  intro η
  have h1 : ContDiffAt ℝ ∞ (fun η : Euc d => ε * cmxMY_wt η) η :=
    (contDiff_const.mul cmxMY_wt_contDiff).contDiffAt
  have h2 : ContDiffAt ℝ ∞ (cmxMY_nu p) (ε * cmxMY_wt η) :=
    cmxMY_nu_contDiffAt p (by have := cmxMY_wt_nonneg η; nlinarith)
  exact h2.comp η h1

/-- the dyadic piece profile `ρ · w̃ · ν(ε w̃)` -/
def cmxMY_Th (p ε : ℝ) (η : Euc d) : ℝ := cmxMY_rho η * (cmxMY_wt η * cmxMY_nu p (ε * cmxMY_wt η))

lemma cmxMY_Th_contDiff (p ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    ContDiff ℝ ∞ (cmxMY_Th p ε : Euc d → ℝ) :=
  cmxMY_rho_contDiff.mul (cmxMY_wt_contDiff.mul (cmxMY_nuw_contDiff p ε hε0 hε1))

lemma cmxMY_Th_supp (p ε : ℝ) (η : Euc d) (h : 2 < ‖η‖) : cmxMY_Th p ε η = 0 := by
  unfold cmxMY_Th
  rw [cmxMY_rho_eq_zero_of_ge h.le]; simp

lemma cmxMY_Th_bound (p : ℝ) (n : ℕ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 → ∀ η : Euc d,
    ‖iteratedFDeriv ℝ n (cmxMY_Th p ε : Euc d → ℝ) η‖ ≤ B := by
  choose Bρ hBρ0 hBρ using fun i : ℕ => cmxMY_bdd_ball (d := d)
    (iteratedFDeriv ℝ i (cmxMY_rho : Euc d → ℝ))
    (cmxMY_rho_contDiff.continuous_iteratedFDeriv (by exact_mod_cast le_top)) 2
  choose Bw hBw0 hBw using fun i : ℕ => cmxMY_wt_deriv_bound (d := d) i
  choose Bν hBν0 hBν using fun i : ℕ => cmxMY_nu_comp_bound (d := d) p i
  -- bound for `Z = w̃ * ν(ε w̃)`
  set BZ : ℕ → ℝ := fun k => ∑ l ∈ Finset.range (k + 1), (k.choose l : ℝ) * Bw l * Bν (k - l) with hBZ
  have hBZ0 : ∀ k, 0 ≤ BZ k := fun k =>
    Finset.sum_nonneg fun l _ => mul_nonneg (mul_nonneg (by positivity) (hBw0 l)) (hBν0 _)
  set Bt : ℝ := ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * Bρ i * BZ (n - i) with hBt
  have hBt0 : 0 ≤ Bt := Finset.sum_nonneg fun i _ => mul_nonneg (mul_nonneg (by positivity) (hBρ0 i)) (hBZ0 _)
  refine ⟨Bt, hBt0, fun ε hε0 hε1 η => ?_⟩
  by_cases hη : ‖η‖ ≤ 2
  · have hZ : ∀ k : ℕ, ‖iteratedFDeriv ℝ k
        (fun η : Euc d => cmxMY_wt η * cmxMY_nu p (ε * cmxMY_wt η)) η‖ ≤ BZ k := by
      intro k
      refine (norm_iteratedFDeriv_mul_le cmxMY_wt_contDiff (cmxMY_nuw_contDiff p ε hε0 hε1) η
        (by exact_mod_cast le_top)).trans ?_
      apply Finset.sum_le_sum
      intro l hl
      have hl' : l ≤ k := by simpa [Nat.lt_succ_iff] using hl
      have hc : (0 : ℝ) ≤ (k.choose l : ℝ) := by positivity
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hBw l η hη) hc)
        (hBν (k - l) ε hε0 hε1 η hη) (norm_nonneg _) (mul_nonneg hc (hBw0 l))
    refine (norm_iteratedFDeriv_mul_le cmxMY_rho_contDiff
      (cmxMY_wt_contDiff.mul (cmxMY_nuw_contDiff p ε hε0 hε1)) η (by exact_mod_cast le_top)).trans ?_
    apply Finset.sum_le_sum
    intro i hi
    have hc : (0 : ℝ) ≤ (n.choose i : ℝ) := by positivity
    exact mul_le_mul (mul_le_mul_of_nonneg_left (hBρ i η hη) hc)
      (hZ (n - i)) (norm_nonneg _) (mul_nonneg hc (hBρ0 i))
  · push Not at hη
    have : (cmxMY_Th p ε : Euc d → ℝ) =ᶠ[𝓝 η] fun _ => (0 : ℝ) := by
      filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hη] with y hy
      exact cmxMY_Th_supp p ε y hy
    have h2 := (this.iteratedFDeriv (𝕜 := ℝ) n).eq_of_nhds
    rw [h2, iteratedFDeriv_fun_zero]
    simpa using hBt0

/-- the Bessel-minus-one symbol `q(ξ) = (1-χ) W ν(W)`, `W = (2π|ξ|)^{-2}` -/
def cmxMY_qB (p : ℝ) (ξ : Euc d) : ℝ :=
  (1 - chi ξ) * (((2 * Real.pi * ‖ξ‖) ^ 2)⁻¹ * cmxMY_nu p (((2 * Real.pi * ‖ξ‖) ^ 2)⁻¹))

/-- the `j`-th dyadic profile -/
def cmxMY_thB (p : ℝ) (j : ℕ) (η : Euc d) : ℂ :=
  ((cmxMY_rho η * (1 - chi (((2 : ℝ) ^ j) • η)) *
    (cmxMY_wt η * cmxMY_nu p ((((2 : ℝ) ^ j) ^ 2)⁻¹ * cmxMY_wt η)) : ℝ) : ℂ)

lemma cmxMY_eps_pos (j : ℕ) : 0 < (((2 : ℝ) ^ j) ^ 2)⁻¹ := by positivity

lemma cmxMY_eps_le (j : ℕ) : (((2 : ℝ) ^ j) ^ 2)⁻¹ ≤ 1 := by
  apply inv_le_one_of_one_le₀
  exact one_le_pow₀ (one_le_pow₀ (by norm_num))

lemma cmxMY_thB_contDiff (p : ℝ) (j : ℕ) : ContDiff ℝ ∞ (cmxMY_thB p j : Euc d → ℂ) := by
  unfold cmxMY_thB
  refine Complex.ofRealCLM.contDiff.comp ?_
  exact (cmxMY_rho_contDiff.mul (contDiff_const.sub
    (cmxFB_chi_contDiff.comp (contDiff_const_smul _)))).mul
    (cmxMY_wt_contDiff.mul (cmxMY_nuw_contDiff p _ (cmxMY_eps_pos j).le (cmxMY_eps_le j)))

lemma cmxMY_thB_supp (p : ℝ) (j : ℕ) (η : Euc d) (h : 2 < ‖η‖) : cmxMY_thB p j η = 0 := by
  unfold cmxMY_thB
  rw [cmxMY_rho_eq_zero_of_ge h.le]; simp

lemma cmxMY_thB_ge_two (p : ℝ) {j : ℕ} (hj : 2 ≤ j) :
    cmxMY_thB p j = fun η : Euc d => ((cmxMY_Th p ((((2 : ℝ) ^ j) ^ 2)⁻¹) η : ℝ) : ℂ) := by
  funext η
  unfold cmxMY_thB cmxMY_Th
  by_cases hη : ‖η‖ ≤ 1 / 2
  · rw [cmxMY_rho_eq_zero_of_le hη]; simp
  · push Not at hη
    have h2 : chi (((2 : ℝ) ^ j) • η) = 0 := by
      apply cmxFB_chi_zero
      rw [norm_smul, Real.norm_of_nonneg (by positivity)]
      have : (2 : ℝ) ^ 2 ≤ 2 ^ j := pow_le_pow_right₀ (by norm_num) hj
      nlinarith
    rw [h2]; simp

lemma cmxMY_thB_bdd (p : ℝ) :
    ∃ j₀ : ℕ, ∀ n : ℕ, ∃ B : ℝ, ∀ j ≥ j₀, ∀ η : Euc d,
      ‖iteratedFDeriv ℝ n (cmxMY_thB p j) η‖ ≤ B := by
  refine ⟨2, fun n => ?_⟩
  obtain ⟨B, -, hB⟩ := cmxMY_Th_bound (d := d) p n
  refine ⟨B, fun j hj η => ?_⟩
  rw [cmxMY_thB_ge_two p hj]
  have h := Complex.ofRealLI.norm_iteratedFDeriv_comp_left
    (cmxMY_Th_contDiff (d := d) p _ (cmxMY_eps_pos j).le (cmxMY_eps_le j)).contDiffAt (x := η)
    (i := n) (by exact_mod_cast le_top)
  have h' : ‖iteratedFDeriv ℝ n (fun η : Euc d => ((cmxMY_Th p ((((2 : ℝ) ^ j) ^ 2)⁻¹) η : ℝ) : ℂ)) η‖ =
      ‖iteratedFDeriv ℝ n (cmxMY_Th p ((((2 : ℝ) ^ j) ^ 2)⁻¹) : Euc d → ℝ) η‖ := h
  rw [h']
  exact hB _ (cmxMY_eps_pos j).le (cmxMY_eps_le j) η

lemma cmxMY_thB_piece (p : ℝ) (j : ℕ) (ξ : Euc d) :
    (((2 : ℝ) ^ j) ^ (-(2 : ℝ)) : ℝ) • cmxMY_thB p j (((2 : ℝ) ^ j)⁻¹ • ξ) =
      ((cmxMY_rho (((2 : ℝ) ^ j)⁻¹ • ξ) * cmxMY_qB p ξ : ℝ) : ℂ) := by
  set s : ℝ := (2 : ℝ) ^ j with hs
  have hs0 : 0 < s := by positivity
  set η : Euc d := s⁻¹ • ξ with hη
  by_cases hρ : cmxMY_rho η = 0
  · unfold cmxMY_thB
    rw [← hs, hρ]; simp
  · have hη2 : 1 / 2 < ‖η‖ := by
      by_contra h
      exact hρ (cmxMY_rho_eq_zero_of_le (not_lt.1 h))
    have hnorm : ‖η‖ = ‖ξ‖ / s := by
      rw [hη, norm_smul, norm_inv, Real.norm_of_nonneg hs0.le, inv_mul_eq_div]
    have hW : ((2 * Real.pi * ‖η‖) ^ 2)⁻¹ = s ^ 2 * ((2 * Real.pi * ‖ξ‖) ^ 2)⁻¹ := by
      rw [hnorm]
      field_simp
    have hwt : cmxMY_wt η = s ^ 2 * ((2 * Real.pi * ‖ξ‖) ^ 2)⁻¹ := by
      rw [cmxMY_wt_eq hη2.le, hW]
    have hε : (s ^ 2)⁻¹ * cmxMY_wt η = ((2 * Real.pi * ‖ξ‖) ^ 2)⁻¹ := by
      rw [hwt]; field_simp
    have hsη : s • η = ξ := by rw [hη, smul_smul, mul_inv_cancel₀ hs0.ne', one_smul]
    unfold cmxMY_thB
    rw [← hs, hε, hsη, hwt, Complex.real_smul, ← Complex.ofReal_mul]
    congr 1
    unfold cmxMY_qB
    have : s ^ (-(2 : ℝ)) = (s ^ 2)⁻¹ := by
      rw [Real.rpow_neg hs0.le]; norm_cast
    rw [this]
    have hs2 : s ^ 2 ≠ 0 := by positivity
    field_simp

lemma cmxMY_qB_even (p : ℝ) (ξ : Euc d) : cmxMY_qB p (-ξ) = cmxMY_qB p ξ := by
  unfold cmxMY_qB
  rw [cmxFB_chi_neg, norm_neg]

/-- the Bessel symbol minus `1 - χ` -/
lemma cmxMY_bessel_symbol (α : ℝ) (ξ : Euc d) :
    (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (α / 2) * ((1 - chi ξ) * (2 * Real.pi * ‖ξ‖) ^ (-α)) =
      (1 - chi ξ) + cmxMY_qB (α / 2) ξ := by
  by_cases hξ : ξ = 0
  · subst hξ
    have : chi (0 : Euc d) = 1 := cmxFB_chi_one (by simp)
    simp [cmxMY_qB, this]
  · have hn : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
    set a : ℝ := 2 * Real.pi * ‖ξ‖ with ha
    have ha0 : 0 < a := by positivity
    have h1 : 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 = a ^ 2 := by rw [ha]; ring
    rw [h1]
    unfold cmxMY_qB
    rw [← ha]
    have h2 : a ^ (-α) = (a ^ 2) ^ (-(α / 2)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul ha0.le]; congr 1; push_cast; ring
    have h3 : (1 + a ^ 2) ^ (α / 2) * (a ^ 2) ^ (-(α / 2)) = (1 + ((a ^ 2)⁻¹)) ^ (α / 2) := by
      rw [Real.rpow_neg (by positivity), ← div_eq_mul_inv, ← Real.div_rpow (by positivity) (by positivity)]
      congr 1
      field_simp
      ring
    have h4 := cmxMY_nu_mul (α / 2) ((a ^ 2)⁻¹)
    rw [h2]
    calc (1 + a ^ 2) ^ (α / 2) * ((1 - chi ξ) * (a ^ 2) ^ (-(α / 2)))
        = (1 - chi ξ) * ((1 + a ^ 2) ^ (α / 2) * (a ^ 2) ^ (-(α / 2))) := by ring
      _ = (1 - chi ξ) * (1 + ((a ^ 2)⁻¹)) ^ (α / 2) := by rw [h3]
      _ = (1 - chi ξ) + (1 - chi ξ) * ((a ^ 2)⁻¹ * cmxMY_nu (α / 2) ((a ^ 2)⁻¹)) := by
          rw [h4]; ring

theorem cmxMY_mult_kernel_bessel (hd : 3 ≤ d) (α : ℝ) (hα : 0 < α) (hαd : α < d) :
    ∃ k : Euc d → ℝ, Integrable k ∧ ∀ ξ : Euc d,
      (((1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (α / 2) * ((1 - chi ξ) * (2 * Real.pi * ‖ξ‖) ^ (-α)) : ℝ) : ℂ) =
        (((1 - chi ξ : ℝ)) : ℂ) + 𝓕 (fun x : Euc d => ((k x : ℝ) : ℂ)) ξ := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨K, hK, hF, -, -⟩ := cmxMY_LP hd1 (γ := 2) (by norm_num) (cmxMY_thB (α / 2))
    (cmxMY_thB_contDiff (α / 2)) (cmxMY_thB_supp (α / 2)) (cmxMY_thB_bdd (α / 2))
  have hq : ∀ ξ : Euc d, 𝓕 K ξ = ((cmxMY_qB (α / 2) ξ : ℝ) : ℂ) := by
    intro ξ
    have h1 := hF ξ
    simp_rw [cmxMY_thB_piece] at h1
    have h2 : HasSum (fun j : ℕ => ((cmxMY_rho (((2 : ℝ) ^ j)⁻¹ • ξ) * cmxMY_qB (α / 2) ξ : ℝ) : ℂ))
        ((cmxMY_qB (α / 2) ξ : ℝ) : ℂ) := by
      by_cases hξ : 1 ≤ ‖ξ‖
      · have := (cmxMY_rho_sum_eq_one hξ).mul_right (cmxMY_qB (α / 2) ξ)
        rw [one_mul] at this
        exact Complex.ofRealCLM.hasSum this
      · have hc : chi ξ = 1 := cmxFB_chi_one (by linarith)
        have h0 : cmxMY_qB (α / 2) ξ = 0 := by simp [cmxMY_qB, hc]
        simp only [h0, mul_zero, Complex.ofReal_zero]
        exact hasSum_zero
    exact h1.unique h2
  have heven : ∀ ξ : Euc d, cmxMY_qB (α / 2) (-ξ) = cmxMY_qB (α / 2) ξ := cmxMY_qB_even _
  refine ⟨fun x => (K x).re, hK.re, fun ξ => ?_⟩
  rw [cmxMY_real_part K hK _ heven hq ξ, cmxMY_bessel_symbol]
  push_cast
  ring

end HRS.Commutator.Whole
