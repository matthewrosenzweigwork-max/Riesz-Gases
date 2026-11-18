import HRS.MS.Mov63GAux10

/-!
# S6.3, packet N8 (part 11): the abstract system for the N5-N7 solution

Namespace `HRS.MS.Mov63`, prefix `mng_`.  **`mng_conc_sys`**: for the mild solution `v` with `‖v_t‖ ≤ C_v K e^{-ct}` (`0 ≤ K ≤ 1`),
`Q_t = mneQ (v_t)`, `b_k = (ν∇log ρ + F_t)_k`, `A_t = div F_t + ⟨∇log ρ, F_t⟩`, `a(t) = K e^{-ct}` form an `MngSys` of order `N`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.Mov63

open HRS HRS.Whole HRS.MS.MovOsc HRS.MS.MovC1 HRS.MS.MovForce HRS.MS.MovLin HRS.MH.DualityRd

variable {d : ℕ} {s β q : ℝ} {ρ : Euc d → ℝ}

lemma mng_cast_le_infty (n : ℕ) : ((n : ℕ) : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) := by
  exact_mod_cast le_top

section Conc2

variable {m : ℕ} (H : Mov2dTh d s β q ρ) (hm : (d : ℝ) / 2 + 3 < m)

include H hm in
theorem mng_conc_sys {N : ℕ} (hN1 : 1 ≤ N) (hN : (d : ℝ) / 2 + N + 2 < m) :
    ∃ C0 Cg : ℝ, 0 ≤ C0 ∧ 0 ≤ Cg ∧ ∀ {v : ℝ → OscSpace d (m : ℝ)},
    MneMild H hm v → ∀ {K c Cv MQ : ℝ}, 0 ≤ K → K ≤ 1 → 0 ≤ Cv → 0 < c → 0 ≤ MQ →
    (∀ t, 0 ≤ t → ‖v t‖ ≤ Cv * K * Real.exp (-c * t)) →
    (∀ t, 0 ≤ t → ∀ x, |mneQ ρ hm (v t) x| ≤ MQ) →
    MngSys N β⁻¹ (fun t => mneQ ρ hm (v t)) (fun k t x => (mnfb d s β ρ hm (v t) x) k)
      (fun t => mnfA d s ρ hm (v t)) (fun t => K * Real.exp (-c * t)) (β⁻¹ * Cg + C0 * Cv) (C0 * Cv) MQ := by
  obtain ⟨C0, hC00, hU⟩ := mng_unif H hm hN
  obtain ⟨Cg, hCg0, hCg⟩ := mng_dlog_unif H N
  refine ⟨C0, Cg, hC00, hCg0, fun {v} hmild {K c Cv MQ} hK0 hK1 hCv hc hMQ hvd hQb => ?_⟩
  have hex : ∀ t, 0 ≤ t → Real.exp (-c * t) ≤ 1 := fun t ht => by
    rw [← Real.exp_zero]; exact Real.exp_le_exp.2 (by nlinarith)
  have hvb : ∀ t, 0 ≤ t → ‖v t‖ ≤ Cv := fun t ht => by
    refine (hvd t ht).trans ?_
    have := hex t ht
    have h2 : 0 ≤ K * Real.exp (-c * t) := by positivity
    nlinarith [mul_le_mul hK1 this (Real.exp_pos _).le zero_le_one]
  have hlog := mng_logrho_cd H
  -- smoothness of the time independent parts
  have hgrad : ∀ n : ℕ, ContDiff ℝ (n : WithTop ℕ∞) (fun y => gradient (fun z => Real.log (ρ z)) y) := fun n =>
    mne_grad_cd (n := n) (hlog.of_le (by exact_mod_cast le_top))
  have hGk : ∀ (n : ℕ) (k : Fin d), ContDiff ℝ (n : WithTop ℕ∞)
      (fun y => β⁻¹ * (gradient (fun z => Real.log (ρ z)) y) k) := fun n k =>
    contDiff_const.mul (mng_proj_cd (hgrad n) k)
  -- the family b_k
  have hbeq : ∀ (k : Fin d) (t : ℝ), (fun x => (mnfb d s β ρ hm (v t) x) k) =
      fun x => β⁻¹ * (gradient (fun z => Real.log (ρ z)) x) k + (mneFo d s ρ hm (v t) x) k :=
    fun k t => funext (mng_mnfb_coord hm (v t) k)
  have hFk : ∀ (k : Fin d) (t : ℝ), ContDiff ℝ (N : WithTop ℕ∞) (fun x => (mneFo d s ρ hm (v t) x) k) :=
    fun k t => mng_proj_cd (((hU (v t)).2.2.1).of_le (by exact_mod_cast Nat.le_succ N)) k
  have hcdb : ∀ k t, ContDiff ℝ (N : WithTop ℕ∞) (fun x => (mnfb d s β ρ hm (v t) x) k) := fun k t => by
    rw [hbeq]; exact (hGk N k).add (hFk k t)
  -- joint continuity of F_k and A
  have hjcF : ∀ k : Fin d, mngJC N (fun t x => (mneFo d s ρ hm (v t) x) k) := fun k => by
    refine mng_jc_lin (Φ := fun u x => (mneFo d s ρ hm u x) k) (r := N) ?_ (fun u => ?_) C0 (fun u l hl x => ?_)
      hmild.cont
    · intro u u' x; simp [mne_Fo_sub hm H u u' x]
    · exact mng_proj_cd (((hU u).2.2.1).of_le (by exact_mod_cast Nat.le_succ N)) k
    · exact (mng_proj_iter_le (k := l) (((hU u).2.2.1).of_le (by exact_mod_cast (by omega : l ≤ N + 1))) k x).trans
        ((hU u).2.2.2.1 l (by omega) x)
  have hjcb : ∀ k : Fin d, mngJC N (fun t x => (mnfb d s β ρ hm (v t) x) k) := fun k => by
    have h1 := mngJC_add (r := N) (f := fun _ x => β⁻¹ * (gradient (fun z => Real.log (ρ z)) x) k)
      (g := fun t x => (mneFo d s ρ hm (v t) x) k) (fun t => hGk N k) (fun t => hFk k t)
      (mngJC_ofx N (hGk N k)) (hjcF k)
    have e : (fun t x => (mnfb d s β ρ hm (v t) x) k) = fun t x => β⁻¹ * (gradient (fun z => Real.log (ρ z)) x) k +
        (mneFo d s ρ hm (v t) x) k := funext fun t => hbeq k t
    exact mngJC_congr h1 e.symm
  have hbwb : ∀ k i : Fin d, mngBW (N - 1) (fun _ => 1) (β⁻¹ * Cg + C0 * Cv)
      (mngPd i (fun t x => (mnfb d s β ρ hm (v t) x) k)) := by
    intro k i
    refine mngBW_of_iter (N - 1) (fun _ => 1) _ _ (fun t => ?_) (fun t ht l hl x => ?_)
    · have hc' : ContDiff ℝ ((N - 1 + 1 : ℕ) : WithTop ℕ∞) (fun x => (mnfb d s β ρ hm (v t) x) k) := by
        rw [show N - 1 + 1 = N by omega]; exact hcdb k t
      exact mng_cd_pd hc' i
    · have hc' : ContDiff ℝ ((l + 1 : ℕ) : WithTop ℕ∞) (fun x => (mnfb d s β ρ hm (v t) x) k) :=
        (hcdb k t).of_le (by exact_mod_cast (by omega : l + 1 ≤ N))
      refine (mng_norm_iter_pd_le hc' i x).trans ?_
      rw [mul_one]
      have e1 : iteratedFDeriv ℝ (l + 1) (fun x => (mnfb d s β ρ hm (v t) x) k) x =
          iteratedFDeriv ℝ (l + 1) (fun x => β⁻¹ * (gradient (fun z => Real.log (ρ z)) x) k) x +
            iteratedFDeriv ℝ (l + 1) (fun x => (mneFo d s ρ hm (v t) x) k) x := by
        rw [hbeq k t]
        have := iteratedFDeriv_add_apply (𝕜 := ℝ) (i := l + 1)
          (f := fun x => β⁻¹ * (gradient (fun z => Real.log (ρ z)) x) k)
          (g := fun x => (mneFo d s ρ hm (v t) x) k) (x := x)
          (((hGk N k).of_le (by exact_mod_cast (by omega : l + 1 ≤ N))).contDiffAt)
          (((hFk k t).of_le (by exact_mod_cast (by omega : l + 1 ≤ N))).contDiffAt)
        exact this
      rw [e1]
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · have hcs : ContDiffAt ℝ ((l + 1 : ℕ) : WithTop ℕ∞) (fun x => (gradient (fun z => Real.log (ρ z)) x) k) x :=
          (mng_proj_cd ((hgrad N).of_le (by exact_mod_cast (by omega : l + 1 ≤ N))) k).contDiffAt
        have e2 : (fun x => β⁻¹ * (gradient (fun z => Real.log (ρ z)) x) k) =
            β⁻¹ • (fun x => (gradient (fun z => Real.log (ρ z)) x) k) := by
          funext x; simp [smul_eq_mul]
        rw [e2, iteratedFDeriv_const_smul_apply hcs, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (inv_nonneg.2 H.hβ.le)]
        refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 H.hβ.le)
        refine (mng_proj_iter_le ((hgrad N).of_le (by exact_mod_cast (by omega : l + 1 ≤ N))) k x).trans ?_
        exact hCg (l + 1) (by omega) (by omega) x
      · refine (mng_proj_iter_le (((hU (v t)).2.2.1).of_le (by exact_mod_cast (by omega : l + 1 ≤ N + 1))) k x).trans ?_
        refine ((hU (v t)).2.2.2.1 (l + 1) (by omega) x).trans ?_
        exact mul_le_mul_of_nonneg_left (hvb t ht) hC00
  -- the zero order coefficient
  have hcdA : ∀ t, ContDiff ℝ (N : WithTop ℕ∞) (mnfA d s ρ hm (v t)) := fun t => (hU (v t)).2.2.2.2.1
  have hjcA : mngJC N (fun t => mnfA d s ρ hm (v t)) := by
    refine mng_jc_lin (Φ := fun u => mnfA d s ρ hm u) (r := N) (fun u u' x => ?_) (fun u => (hU u).2.2.2.2.1) C0
      (fun u l hl x => (hU u).2.2.2.2.2 l hl x) hmild.cont
    exact mng_mnfA_sub H hm u u' x (((hU u).2.2.1).differentiable (by simp)) (((hU u').2.2.1).differentiable (by simp))
  have hbwA : mngBW N (fun t => K * Real.exp (-c * t)) (C0 * Cv) (fun t => mnfA d s ρ hm (v t)) := by
    refine mngBW_of_iter N _ _ _ hcdA (fun t ht l hl x => ?_)
    refine ((hU (v t)).2.2.2.2.2 l hl x).trans ?_
    calc C0 * ‖v t‖ ≤ C0 * (Cv * K * Real.exp (-c * t)) := mul_le_mul_of_nonneg_left (hvd t ht) hC00
      _ = C0 * Cv * (K * Real.exp (-c * t)) := by ring
  -- the function Q
  have hcdV : ∀ t, ContDiff ℝ ((N + 2 : ℕ) : WithTop ℕ∞) (mneV hm (v t)) := fun t => (hU (v t)).1
  have hcdQ : ∀ t, ContDiff ℝ ((N + 2 : ℕ) : WithTop ℕ∞) (mneQ ρ hm (v t)) := fun t => by
    rw [mng_Q_eq H hm (v t)]
    exact contDiff_const.add (((mngW_cd H).of_le (mng_cast_le_infty _)).mul (hcdV t))
  have hjcV : mngJC (N + 2) (fun t => mneV hm (v t)) := by
    refine mng_jc_lin (Φ := fun u => mneV hm u) (r := N + 2) (fun u u' x => ?_) (fun u => (hU u).1) C0
      (fun u l hl x => (hU u).2.1 l hl x) hmild.cont
    show mneV hm (u - u') x = _
    rw [mneV_sub hm u u']
  have hjcQ : mngJC (N + 2) (fun t => mneQ ρ hm (v t)) := by
    have hw : ContDiff ℝ ((N + 2 : ℕ) : WithTop ℕ∞) (mngW ρ) := (mngW_cd H).of_le (mng_cast_le_infty _)
    have h1 := mngJC_add (r := N + 2) (f := fun _ _ => (1 : ℝ)) (g := fun t z => mngW ρ z * mneV hm (v t) z)
      (fun t => contDiff_const) (fun t => hw.mul (hcdV t)) (mngJC_const _ 1)
      (mngJC_mul (f := fun _ z => mngW ρ z) (g := fun t z => mneV hm (v t) z) (fun t => hw) hcdV
        (mngJC_ofx _ hw) hjcV)
    have e : (fun t => mneQ ρ hm (v t)) = fun t z => 1 + mngW ρ z * mneV hm (v t) z :=
      funext fun t => mng_Q_eq H hm (v t)
    exact mngJC_congr h1 e.symm
  -- Duhamel form
  have hG0 : mngJC 0 (mngGen β⁻¹ (fun k t x => (mnfb d s β ρ hm (v t) x) k) (fun t => mnfA d s ρ hm (v t))
      (fun t => mneQ ρ hm (v t))) := by
    have := mngGen_reg (ν := β⁻¹) (b := fun k t x => (mnfb d s β ρ hm (v t) x) k)
      (A := fun t => mnfA d s ρ hm (v t)) (g := fun t => mneQ ρ hm (v t)) (r := 0)
      (fun t => (hcdQ t).of_le (by exact_mod_cast (by omega : 0 + 2 ≤ N + 2)))
      (mngJC_mono (by omega) hjcQ) (fun k t => (hcdb k t).of_le (by exact_mod_cast Nat.zero_le N))
      (fun k => mngJC_mono (Nat.zero_le N) (hjcb k)) (fun t => (hcdA t).of_le (by exact_mod_cast Nat.zero_le N))
      (mngJC_mono (Nat.zero_le N) hjcA)
    exact this.2
  have hQc : ContinuousOn (fun p : ℝ × Euc d => mneQ ρ hm (v p.1) p.2) (Ici 0 ×ˢ univ) := mngJC_zero hjcQ
  have hduh : mngDuh (fun t => mneQ ρ hm (v t)) (mngGen β⁻¹ (fun k t x => (mnfb d s β ρ hm (v t) x) k)
      (fun t => mnfA d s ρ hm (v t)) (fun t => mneQ ρ hm (v t))) := by
    intro x t ht
    rcases ht.eq_or_lt with h0 | hpos
    · subst h0; simp
    · have hderiv : ∀ r ∈ Ioo (0 : ℝ) t, HasDerivWithinAt (fun τ => mneQ ρ hm (v τ) x)
          (mngGen β⁻¹ (fun k t x => (mnfb d s β ρ hm (v t) x) k) (fun t => mnfA d s ρ hm (v t))
            (fun t => mneQ ρ hm (v t)) r x) (Ioi r) r := by
        intro r hr
        have h1 := (mne_Q_hasDeriv hm H hmild hr.1.le x).mono (Set.Ioi_subset_Ici hr.1.le)
        refine h1.congr_deriv ?_
        have hq2 : ContDiff ℝ 2 (mneQ ρ hm (v r)) := (hcdQ r).of_le (by exact_mod_cast (by omega : 2 ≤ N + 2))
        rw [mng_lap_eq hq2 x, mng_inner_grad (hq2.differentiable (by norm_num)) x]
        rfl
      have hcont : ContinuousOn (fun τ => mneQ ρ hm (v τ) x) (Icc 0 t) := by
        have := hQc.comp (by fun_prop : Continuous fun τ : ℝ => (τ, x)).continuousOn
          (fun τ hτ => ⟨hτ, mem_univ _⟩)
        exact this.mono Set.Icc_subset_Ici_self
      have hGc : ContinuousOn (fun τ => mngGen β⁻¹ (fun k t x => (mnfb d s β ρ hm (v t) x) k)
          (fun t => mnfA d s ρ hm (v t)) (fun t => mneQ ρ hm (v t)) τ x) (Icc 0 t) := by
        have := (mngJC_zero hG0).comp (by fun_prop : Continuous fun τ : ℝ => (τ, x)).continuousOn
          (fun τ hτ => ⟨hτ, mem_univ _⟩)
        exact this.mono Set.Icc_subset_Ici_self
      have hint := ContinuousOn.intervalIntegrable_of_Icc (μ := volume) hpos.le hGc
      have := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hpos.le hcont hderiv hint
      linarith
  refine ⟨hN1, add_nonneg (mul_nonneg (inv_nonneg.2 H.hβ.le) hCg0) (mul_nonneg hC00 hCv), mul_nonneg hC00 hCv, hMQ,
    hQb, hcdQ, hjcQ, hcdb, hjcb, hbwb, hcdA, hjcA, hbwA, fun t ht => by positivity, fun t ht => ?_, hduh⟩
  have := hex t ht
  nlinarith [mul_le_mul hK1 this (Real.exp_pos _).le zero_le_one]

end Conc2

end HRS.MS.Mov63

end
