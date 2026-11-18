import HRS.MS.MfeConfAux104

/-!
# S.B.1, packet F9 (part 8): the concrete kernel family `k_M = h_{s,1/(M+1)^2}(|·|²)` and its uniform estimates

* `sb1kM`, `sb1kM_isKernel`, `sb1kM_tend` (eventually equal to the Riesz kernel off the origin), `sb1kM_fderiv_tend`;
* `sb1kM_grad_pow`: `|∇k_M(z)·e| ≤ A |z|^{-s-1}|e|` uniformly in `M`; `sb1kM_hk_bound`: the commutator pair kernel
  `|∇k_M(x-y)·(u(x)-u(y))| ≤ A K |x-y|^{-s}` for a `K`-Lipschitz field `u`;
* `sb1kM_grad_env`: `|z||∇k_M(z)| ≤ A (k_M(z) + log(1+|z|) + 1)`.
-/

noncomputable section

open MeasureTheory Filter Topology
open HRS HRS.MP.SelfSimP4 HRS.MP.SelfSimP4Impl
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MfeConf

variable {d : ℕ}

/-- the truncated kernel at scale `r` -/
def sb1pk (d : ℕ) (s r : ℝ) : Euc d → ℝ := fun x => p4k_h s (r ^ 2) (‖x‖ ^ 2)

/-- the family `r_M = 1/(M+1)` -/
def sb1kM (d : ℕ) (s : ℝ) (M : ℕ) : Euc d → ℝ := sb1pk d s (1 / ((M : ℝ) + 1))

theorem sb1_rM_pos (M : ℕ) : 0 < 1 / ((M : ℝ) + 1) := by positivity

theorem sb1_rM_le (M : ℕ) : 1 / ((M : ℝ) + 1) ≤ 1 := by
  rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg M : (0 : ℝ) ≤ M)]

theorem sb1kM_isKernel (s : ℝ) (hs : 0 ≤ s) (M : ℕ) : IsP4Kernel d s (1 / ((M : ℝ) + 1)) (sb1kM d s M) :=
  p4k_isKernel d s hs (sb1_rM_pos M) (sb1_rM_le M)

theorem sb1kM_ker (s : ℝ) (hs : 0 ≤ s) (M : ℕ) : Sb1KerU d s (sb1kM d s M) :=
  sb1KerU_of_p4 hs (sb1kM_isKernel s hs M)

/-- for `M` large the truncated kernel equals the Riesz kernel near `z ≠ 0` -/
theorem sb1kM_eventually_eq (s : ℝ) (hs : 0 ≤ s) {z : Euc d} (hz : z ≠ 0) :
    ∀ᶠ M : ℕ in atTop, sb1kM d s M =ᶠ[𝓝 z] Whole.rieszKernel d s := by
  have hn : 0 < ‖z‖ := norm_pos_iff.2 hz
  obtain ⟨M0, hM0⟩ := exists_nat_gt (2 / ‖z‖)
  filter_upwards [eventually_ge_atTop M0] with M hM
  have hr : 1 / ((M : ℝ) + 1) < ‖z‖ := by
    have h1 : 2 / ‖z‖ < (M : ℝ) + 1 := by
      have : (M0 : ℝ) ≤ M := by exact_mod_cast hM
      linarith
    rw [div_lt_iff₀ hn] at h1
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  have hopen : {y : Euc d | 1 / ((M : ℝ) + 1) < ‖y‖} ∈ 𝓝 z :=
    (isOpen_lt continuous_const continuous_norm).mem_nhds hr
  filter_upwards [hopen] with y hy using (sb1kM_isKernel s hs M).eq_far y hy.le

theorem sb1kM_tend (s : ℝ) (hs : 0 ≤ s) {z : Euc d} (hz : z ≠ 0) :
    Tendsto (fun M => sb1kM d s M z) atTop (𝓝 (Whole.rieszKernel d s z)) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [sb1kM_eventually_eq s hs hz] with M h using (h.eq_of_nhds).symm

theorem sb1kM_fderiv_tend (s : ℝ) (hs : 0 ≤ s) {z : Euc d} (hz : z ≠ 0) (e : Euc d) :
    Tendsto (fun M => fderiv ℝ (sb1kM d s M) z e) atTop (𝓝 (fderiv ℝ (Whole.rieszKernel d s) z e)) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [sb1kM_eventually_eq s hs hz] with M h
  rw [h.fderiv_eq]

/-- uniform pointwise gradient bound `|∇k_M(z)·e| ≤ A |z|^{-s-1} |e|` -/
theorem sb1kM_grad_pow (s : ℝ) (hs : 0 ≤ s) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (M : ℕ) (z : Euc d), z ≠ 0 → ∀ e : Euc d,
      |fderiv ℝ (sb1kM d s M) z e| ≤ A * ‖z‖ ^ (-s - 1) * ‖e‖ := by
  obtain ⟨A, hA0, hA⟩ := sb1_p4k_grad_bound d s hs
  refine ⟨A, hA0, fun M z hz e => ?_⟩
  have hn : 0 < ‖z‖ := norm_pos_iff.2 hz
  have hb := hA (1 / ((M : ℝ) + 1)) (sb1_rM_pos M) (sb1_rM_le M) z
  have hk := sb1kM_isKernel (d := d) s hs M
  have hpow : ‖z‖ * ‖gradient (sb1kM d s M) z‖ ≤ A * ‖z‖ ^ (-s) := by
    refine hb.trans (mul_le_mul_of_nonneg_left ?_ hA0)
    by_cases h0 : s = 0
    · simp [h0]
    · simp only [h0, if_false]
      have := hk.le_riesz z hz
      have hr : Whole.rieszKernel d s z = ‖z‖ ^ (-s) := by unfold Whole.rieszKernel; simp [h0]
      rw [hr] at this
      exact this
  have h2 : ‖gradient (sb1kM d s M) z‖ ≤ A * ‖z‖ ^ (-s - 1) := by
    have h3 : ‖z‖ ^ (-s - 1) * ‖z‖ = ‖z‖ ^ (-s) := by
      rw [← Real.rpow_add_one hn.ne']; congr 1; ring
    have : ‖z‖ * ‖gradient (sb1kM d s M) z‖ ≤ ‖z‖ * (A * ‖z‖ ^ (-s - 1)) := by
      calc _ ≤ A * ‖z‖ ^ (-s) := hpow
        _ = _ := by rw [← h3]; ring
    exact le_of_mul_le_mul_left this hn
  rw [← p4k_inner_grad, ← Real.norm_eq_abs]
  calc ‖inner ℝ (gradient (sb1kM d s M) z) e‖ ≤ ‖gradient (sb1kM d s M) z‖ * ‖e‖ := norm_inner_le_norm _ _
    _ ≤ A * ‖z‖ ^ (-s - 1) * ‖e‖ := mul_le_mul_of_nonneg_right h2 (norm_nonneg _)

/-- the commutator pair kernel of a Lipschitz field is dominated by `A K |x-y|^{-s}` uniformly in `M` -/
theorem sb1kM_hk_bound (s : ℝ) (hs : 0 ≤ s) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (M : ℕ) {u : Euc d → Euc d} {Kc : ℝ}, 0 ≤ Kc → (∀ x y, ‖u x - u y‖ ≤ Kc * ‖x - y‖) →
      ∀ x y : Euc d, |sb1hk (sb1kM d s M) u x y| ≤ A * Kc * ‖x - y‖ ^ (-s) := by
  obtain ⟨A, hA0, hA⟩ := sb1kM_grad_pow (d := d) s hs
  refine ⟨A, hA0, fun M u Kc hKc hu x y => ?_⟩
  by_cases hxy : x = y
  · subst hxy
    simp only [sb1hk, sub_self, map_zero, abs_zero]
    exact mul_nonneg (mul_nonneg hA0 hKc) (Real.rpow_nonneg (norm_nonneg _) _)
  · have hz : x - y ≠ 0 := sub_ne_zero.2 hxy
    have hzp : 0 < ‖x - y‖ := norm_pos_iff.2 hz
    unfold sb1hk
    refine (hA M _ hz _).trans ?_
    have h3 : ‖x - y‖ ^ (-s - 1) * ‖x - y‖ = ‖x - y‖ ^ (-s) := by
      rw [← Real.rpow_add_one hzp.ne']; congr 1; ring
    calc A * ‖x - y‖ ^ (-s - 1) * ‖u x - u y‖
        ≤ A * ‖x - y‖ ^ (-s - 1) * (Kc * ‖x - y‖) :=
          mul_le_mul_of_nonneg_left (hu x y) (mul_nonneg hA0 (Real.rpow_nonneg hzp.le _))
      _ = A * Kc * ‖x - y‖ ^ (-s) := by rw [← h3]; ring

/-- the envelope form `|z||∇k_M(z)| ≤ A (k_M(z) + log(1+|z|) + 1)` -/
theorem sb1kM_grad_env (s : ℝ) (hs : 0 ≤ s) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (M : ℕ) (z : Euc d),
      ‖z‖ * ‖gradient (sb1kM d s M) z‖ ≤ A * (sb1kM d s M z + Real.log (1 + ‖z‖) + 1) := by
  obtain ⟨A, hA0, hA⟩ := sb1_p4k_grad_bound d s hs
  refine ⟨A, hA0, fun M z => ?_⟩
  have hb := hA (1 / ((M : ℝ) + 1)) (sb1_rM_pos M) (sb1_rM_le M) z
  have hk := sb1kM_isKernel (d := d) s hs M
  have hlow := hk.lower z
  have hlog : 0 ≤ Real.log (1 + ‖z‖) := Real.log_nonneg (by linarith [norm_nonneg z])
  refine hb.trans (mul_le_mul_of_nonneg_left ?_ hA0)
  have hdef : (sb1kM d s M z) = p4k_h s ((1 / ((M : ℝ) + 1)) ^ 2) (‖z‖ ^ 2) := rfl
  by_cases h0 : s = 0
  · simp only [h0, ite_true]
    rw [h0] at hlow
    rw [h0] at hdef
    linarith
  · simp only [h0, if_false]
    have hpos := hk.nonneg (lt_of_le_of_ne hs (Ne.symm h0)) z
    linarith

end HRS.MS.MfeConf
