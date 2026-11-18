import HRS.MC.D3TWAux1

/-!
# Packet D3TW: Lemma D.3 on `𝕋^d`, item (ii) for the short-scale kernel `w_λ = fdlWT`.

Spec: `HRS/Appendix/FDL.lean`, `HRS.fdl_kernel_torus` (the `fdlWT` conjuncts of (ii)).
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal ContDiff

namespace HRS.MC.D3TW

open HRS HRS.MC.FDLE HRS.MC.Per HRS.MC.D3EW HRS.MC.D3T1

variable {d : ℕ}

lemma d3tw_mk_zero_iff {y : Euc d} (n : Lattice d) (h : Torus.mk y ≠ 0) :
    y + Lattice.toEuc n ≠ 0 := by
  intro h0
  apply h
  rw [← d3t_mk_add y n, h0]
  ext i; simp [Torus.mk]

lemma d3tw_ge_tdist (y : Euc d) (n : Lattice d) :
    KernelGrad.tdist (Torus.mk y) 0 ≤ ‖y + Lattice.toEuc n‖ := by
  have := d3t_tdist_mk_le (y + Lattice.toEuc n)
  rwa [d3t_mk_add] at this

theorem d3tw_deriv (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ψ : Euc d → ℝ}
    (hψ : IsFDLProfile ψ) {b : ℝ} (hb : IsFDLConst ψ s b) :
    ∀ j : ℕ, 0 < (j : ℝ) + s → ∃ C : ℝ, 0 ≤ C ∧ ∀ lam : ℝ, 0 < lam → lam < 1 →
      ∀ y : Euc d, Torus.mk y ≠ 0 →
        ‖iteratedFDeriv ℝ j (Torus.lift (fdlWT ψ s b lam)) y‖ ≤
          (if KernelGrad.tdist (Torus.mk y) 0 ≤ lam then
            C * KernelGrad.tdist (Torus.mk y) 0 ^ (-s - (j : ℝ)) else 0) := by
  intro j hj
  obtain ⟨C, hC0, hC⟩ := d3ew_deriv hd hs0 hsd hψ hb j hj
  obtain ⟨N, hN⟩ := d3tw_card d
  refine ⟨N * C, mul_nonneg (Nat.cast_nonneg _) hC0, fun lam hl0 hl1 y hy => ?_⟩
  set τ := KernelGrad.tdist (Torus.mk y) 0 with hτ
  have hτ0 : 0 < τ := KernelGrad.tdist_pos hy
  set S : Finset (Lattice d) := (per_finite_lattice (d := d) (‖y‖ + 2)).toFinset with hS
  have hev : Torus.lift (fdlWT ψ s b lam) =ᶠ[𝓝 y]
      fun y' => ∑ n ∈ S, fdlWE ψ s b lam (y' + Lattice.toEuc n) := by
    filter_upwards [Metric.ball_mem_nhds y (lt_min one_pos (half_pos hτ0))] with y' hy'
    rw [Metric.mem_ball, dist_eq_norm] at hy'
    have h1 : ‖y' - y‖ < 1 := lt_of_lt_of_le hy' (min_le_left _ _)
    have h2 : ‖y' - y‖ < τ / 2 := lt_of_lt_of_le hy' (min_le_right _ _)
    unfold Torus.lift
    refine d3tw_rep_sum hψ s b hl0 hl1 (fun n h0 => ?_) S (fun n hn => ?_)
    · have := d3tw_ge_tdist y n
      have h4 : ‖y + Lattice.toEuc n‖ ≤ ‖y' - y‖ := by
        have e : y + Lattice.toEuc n = -(y' - y) + (y' + Lattice.toEuc n) := by abel
        rw [e, h0, add_zero, norm_neg]
      linarith
    · rw [hS, Set.Finite.mem_toFinset]
      show ‖Lattice.toEuc n‖ ≤ ‖y‖ + 2
      have e : Lattice.toEuc n = (y' + Lattice.toEuc n) - y' := by abel
      have h5 : ‖y'‖ ≤ ‖y‖ + ‖y' - y‖ := by
        have := norm_le_norm_add_norm_sub' y' y
        linarith
      have := norm_sub_le (y' + Lattice.toEuc n) y'
      rw [← e] at this
      linarith
  have hderiv : iteratedFDeriv ℝ j (Torus.lift (fdlWT ψ s b lam)) y
      = ∑ n ∈ S, iteratedFDeriv ℝ j (fdlWE ψ s b lam) (y + Lattice.toEuc n) := by
    rw [(hev.iteratedFDeriv ℝ j).eq_of_nhds, iteratedFDeriv_fun_sum_apply]
    · refine Finset.sum_congr rfl fun n _ => ?_
      exact iteratedFDeriv_comp_add_right (f := fdlWE ψ s b lam) j (Lattice.toEuc n) y
    · intro n _
      have h1 : ContDiffAt ℝ j (fdlWE ψ s b lam) (y + Lattice.toEuc n) :=
        d3tw_wE_contDiffAt hψ s b (d3tw_mk_zero_iff n hy) j
      have h2 : ContDiffAt ℝ j (fun y' : Euc d => y' + Lattice.toEuc n) y :=
        contDiffAt_id.add contDiffAt_const
      exact ContDiffAt.comp (g := fdlWE ψ s b lam) y h1 h2
  rw [hderiv]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ n ∈ S, ‖iteratedFDeriv ℝ j (fdlWE ψ s b lam) (y + Lattice.toEuc n)‖
      ≤ if ‖y + Lattice.toEuc n‖ ≤ lam then C * τ ^ (-s - (j : ℝ)) else 0 := by
    intro n _
    have h := hC lam hl0 hl1 _ (d3tw_mk_zero_iff n hy)
    by_cases h1 : ‖y + Lattice.toEuc n‖ ≤ lam
    · rw [if_pos h1] at h ⊢
      refine h.trans (mul_le_mul_of_nonneg_left ?_ hC0)
      exact Real.rpow_le_rpow_of_nonpos hτ0 (d3tw_ge_tdist y n)
        (by linarith)
    · rw [if_neg h1] at h ⊢
      exact h
  refine (Finset.sum_le_sum hterm).trans ?_
  have hnn : 0 ≤ C * τ ^ (-s - (j : ℝ)) := mul_nonneg hC0 (Real.rpow_nonneg hτ0.le _)
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  split_ifs with hτl
  · have hc : ((S.filter fun n => ‖y + Lattice.toEuc n‖ ≤ lam).card : ℝ) ≤ N := by
      exact_mod_cast hN y (S.filter fun n => ‖y + Lattice.toEuc n‖ ≤ lam)
        (fun n hn => ((Finset.mem_filter.1 hn).2).trans hl1.le)
    calc _ ≤ (N : ℝ) * (C * τ ^ (-s - (j : ℝ))) := mul_le_mul_of_nonneg_right hc hnn
      _ = _ := by ring
  · have : (S.filter fun n => ‖y + Lattice.toEuc n‖ ≤ lam) = ∅ :=
      Finset.filter_eq_empty_iff.2 (fun n _ h => hτl ((d3tw_ge_tdist y n).trans h))
    simp [this]

theorem d3tw_log (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ψ : Euc d → ℝ}
    (hψ : IsFDLProfile ψ) {b : ℝ} (hb : IsFDLConst ψ s b) :
    s = 0 → ∃ C : ℝ, 0 ≤ C ∧ ∀ lam : ℝ, 0 < lam → lam < 1 → ∀ x : Torus d, x ≠ 0 →
      |fdlWT ψ s b lam x| ≤
        (if KernelGrad.tdist x 0 ≤ lam then C * Real.log (lam / KernelGrad.tdist x 0) else 0) := by
  intro hs
  obtain ⟨C, hC0, hC⟩ := d3ew_log hd hs0 hsd hψ hb hs
  obtain ⟨N, hN⟩ := d3tw_card d
  refine ⟨N * C, mul_nonneg (Nat.cast_nonneg _) hC0, fun lam hl0 hl1 x hx => ?_⟩
  obtain ⟨y, hyx, hyn⟩ := d3t_exists_rep x
  subst hyx
  set τ := KernelGrad.tdist (Torus.mk y) 0 with hτ
  have hτ0 : 0 < τ := KernelGrad.tdist_pos hx
  set S : Finset (Lattice d) := (per_finite_lattice (d := d) (‖y‖ + 1)).toFinset with hS
  rw [d3tw_rep_sum hψ s b hl0 hl1 (fun n => d3tw_mk_zero_iff n hx) S (fun n hn => by
    rw [hS, Set.Finite.mem_toFinset]
    show ‖Lattice.toEuc n‖ ≤ ‖y‖ + 1
    have := norm_sub_le (y + Lattice.toEuc n) y
    simp only [add_sub_cancel_left] at this
    linarith)]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ n ∈ S, |fdlWE ψ s b lam (y + Lattice.toEuc n)|
      ≤ if ‖y + Lattice.toEuc n‖ ≤ lam then C * Real.log (lam / τ) else 0 := by
    intro n _
    have h := hC lam hl0 hl1 _ (d3tw_mk_zero_iff n hx)
    by_cases h1 : ‖y + Lattice.toEuc n‖ ≤ lam
    · rw [if_pos h1] at h ⊢
      refine h.trans (mul_le_mul_of_nonneg_left ?_ hC0)
      exact Real.log_le_log (div_pos hl0 (lt_of_lt_of_le hτ0 (d3tw_ge_tdist y n)))
        (div_le_div_of_nonneg_left hl0.le hτ0 (d3tw_ge_tdist y n))
    · rw [if_neg h1] at h ⊢
      exact h
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  split_ifs with hτl
  · have hc : ((S.filter fun n => ‖y + Lattice.toEuc n‖ ≤ lam).card : ℝ) ≤ N := by
      exact_mod_cast hN y (S.filter fun n => ‖y + Lattice.toEuc n‖ ≤ lam)
        (fun n hn => ((Finset.mem_filter.1 hn).2).trans hl1.le)
    have hnn : 0 ≤ C * Real.log (lam / τ) :=
      mul_nonneg hC0 (Real.log_nonneg ((one_le_div hτ0).2 hτl))
    calc _ ≤ (N : ℝ) * (C * Real.log (lam / τ)) := mul_le_mul_of_nonneg_right hc hnn
      _ = _ := by ring
  · have : (S.filter fun n => ‖y + Lattice.toEuc n‖ ≤ lam) = ∅ :=
      Finset.filter_eq_empty_iff.2 (fun n _ h => hτl ((d3tw_ge_tdist y n).trans h))
    simp [this]

end HRS.MC.D3TW
