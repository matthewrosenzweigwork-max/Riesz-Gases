import HRS.Kernel.GradBasic

/-!
# Smoothness of the periodic Riesz kernel off the origin, and its gradient

Auxiliary file of `HRS/Kernel/GradConv.lean`.  `g ∘ mk` is `C^∞` off the lattice (image-sum
formula `decomp1` of `Riesz.lean`, re-centred at an arbitrary point), and `∇g = periodicRieszGrad`
is its classical gradient there (differentiation under the subordination integral).
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators Real

namespace HRS.KernelGrad

open HRS.KernelAux

local notation "∞'" => ((⊤ : ℕ∞) : WithTop ℕ∞)

variable {d : ℕ}

/-- the quadratic `π²|x - c|²` centred at an arbitrary `c` -/
def qc (c x : Euc d) : ℝ := π ^ 2 * ‖x - c‖ ^ 2

theorem contDiff_qc (c : Euc d) : ContDiff ℝ ∞' (qc c) := by
  unfold qc
  exact contDiff_const.mul ((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const))

theorem norm_iteratedFDeriv_qc_le (c : Euc d) (n : ℕ) (x : Euc d) :
    ‖iteratedFDeriv ℝ n (qc c) x‖ ≤ π ^ 2 * 2 ^ n * (1 + ‖x - c‖) ^ 2 := by
  set B : Euc d →L[ℝ] Euc d →L[ℝ] ℝ := (π ^ 2) • (innerSL ℝ : Euc d →L[ℝ] Euc d →L[ℝ] ℝ) with hB
  have hq : qc c = fun y => B (y - c) (y - c) := by
    funext y
    simp only [qc, B, ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [innerSL_apply_apply, real_inner_self_eq_norm_sq]
  have hf : ContDiff ℝ ∞' (fun y : Euc d => y - c) := contDiff_id.sub contDiff_const
  rw [hq]
  have h1 := B.norm_iteratedFDeriv_le_of_bilinear hf hf x (n := n) (by exact_mod_cast le_top)
  have hBn : ‖B‖ ≤ π ^ 2 := by
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun u => ?_
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
    rw [hB]
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, norm_mul, Real.norm_eq_abs]
    rw [innerSL_apply_apply, abs_of_nonneg (by positivity : (0:ℝ) ≤ π^2), mul_assoc]
    gcongr
    exact abs_real_inner_le_norm u v
  set R := 1 + ‖x - c‖ with hR
  have hR0 : 0 ≤ R := by positivity
  have hsum : ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i (fun y : Euc d => y - c) x‖ *
        ‖iteratedFDeriv ℝ (n - i) (fun y : Euc d => y - c) x‖ ≤ 2 ^ n * R ^ 2 := by
    calc _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (R * R) := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [mul_assoc]
          gcongr
          · exact norm_iteratedFDeriv_sub_const_le _ _ _
          · exact norm_iteratedFDeriv_sub_const_le _ _ _
      _ = 2 ^ n * R ^ 2 := by
          rw [← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
          push_cast; ring
  calc _ ≤ ‖B‖ * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i (fun y : Euc d => y - c) x‖ *
        ‖iteratedFDeriv ℝ (n - i) (fun y : Euc d => y - c) x‖ := h1
    _ ≤ π ^ 2 * (2 ^ n * R ^ 2) := by gcongr
    _ = _ := by ring

theorem image_comp_bound_c {s : ℝ} (hs : 0 ≤ s) (n : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ c : Euc d, 1 ≤ ‖c‖ → ∀ x : Euc d, ‖x‖ ≤ 1/4 → ∀ j ≤ n,
      ‖iteratedFDeriv ℝ j (fun y => Wt s (qc c y)) x‖ ≤
        K * (‖c‖ ^ (2 * n) * Real.exp (-2 * ‖c‖ ^ 2)) := by
  choose B hB0 hB using Wt_deriv_bound s hs
  set BS := ∑ i ∈ Finset.range (n + 1), B i with hBS
  have hBS0 : 0 ≤ BS := Finset.sum_nonneg fun i _ => hB0 i
  have hπ : (9:ℝ) ≤ π ^ 2 := by nlinarith [Real.pi_gt_three]
  refine ⟨(n.factorial : ℝ) * BS * (18 * π ^ 2) ^ n, by positivity, fun c hc x hx j hj => ?_⟩
  set e := ‖c‖ with he
  have he1 : 1 ≤ e := hc
  set w := qc c x with hw
  set R := 1 + ‖x - c‖ with hR
  have hdist1 : e - 1/4 ≤ ‖x - c‖ := by
    have := norm_sub_norm_le c x
    rw [norm_sub_rev] at this
    linarith
  have hdist2 : ‖x - c‖ ≤ e + 1/4 := by
    have := norm_sub_le x c
    linarith
  have hw4 : 4 * e ^ 2 ≤ w := by
    have h1 : 3/4 * e ≤ ‖x - c‖ := by linarith
    have h2 : (3/4 * e) ^ 2 ≤ ‖x - c‖ ^ 2 := by gcongr
    simp only [hw, qc]
    nlinarith
  have hw1 : 1 ≤ w := by nlinarith
  have hR1 : 1 ≤ R := by simp only [hR]; linarith [norm_nonneg (x - c)]
  have hR3 : R ≤ 3 * e := by simp only [hR]; linarith
  have hC : ∀ i, i ≤ j → ‖iteratedFDeriv ℝ i (Wt s) (qc c x)‖ ≤ BS * Real.exp (-w / 2) := by
    intro i hi
    refine (hB i w hw1).trans ?_
    gcongr
    exact Finset.single_le_sum (f := B) (fun k _ => hB0 k) (Finset.mem_range.mpr (by omega))
  have hD : ∀ i, 1 ≤ i → i ≤ j → ‖iteratedFDeriv ℝ i (qc c) x‖ ≤ (2 * π ^ 2 * R ^ 2) ^ i := by
    intro i hi _
    have h1 : 1 ≤ π ^ 2 * R ^ 2 := by nlinarith
    have h2 : π ^ 2 * 2 ^ i * R ^ 2 ≤ (2 * π ^ 2 * R ^ 2) ^ i := by
      rw [show 2 * π ^ 2 * R ^ 2 = 2 * (π ^ 2 * R ^ 2) by ring, mul_pow]
      calc π ^ 2 * 2 ^ i * R ^ 2 = 2 ^ i * (π ^ 2 * R ^ 2) := by ring
        _ ≤ 2 ^ i * (π ^ 2 * R ^ 2) ^ i := by gcongr; exact le_self_pow₀ h1 (by omega)
    exact (norm_iteratedFDeriv_qc_le c i x).trans h2
  have hFB := norm_iteratedFDeriv_comp_le (contDiff_Wt s hs) (contDiff_qc c) (n := j)
    (by exact_mod_cast le_top) x hC hD
  refine (le_of_eq_of_le rfl hFB).trans ?_
  have hexp : Real.exp (-w / 2) ≤ Real.exp (-2 * e ^ 2) := by
    rw [Real.exp_le_exp]; linarith
  have hpow : (2 * π ^ 2 * R ^ 2) ^ j ≤ (18 * π ^ 2) ^ n * e ^ (2 * n) := by
    have hb : 1 ≤ 18 * π ^ 2 * e ^ 2 := by nlinarith
    have hR9 : R ^ 2 ≤ 9 * e ^ 2 := by nlinarith
    have hbase : 2 * π ^ 2 * R ^ 2 ≤ 18 * π ^ 2 * e ^ 2 := by
      calc 2 * π ^ 2 * R ^ 2 ≤ 2 * π ^ 2 * (9 * e ^ 2) := by gcongr
        _ = 18 * π ^ 2 * e ^ 2 := by ring
    calc (2 * π ^ 2 * R ^ 2) ^ j ≤ (18 * π ^ 2 * e ^ 2) ^ j :=
          pow_le_pow_left₀ (by positivity) hbase j
      _ ≤ (18 * π ^ 2 * e ^ 2) ^ n := pow_le_pow_right₀ hb hj
      _ = (18 * π ^ 2) ^ n * e ^ (2 * n) := by rw [mul_pow, pow_mul]
  have hfact : (j.factorial : ℝ) ≤ n.factorial := by exact_mod_cast Nat.factorial_le hj
  calc (j.factorial : ℝ) * (BS * Real.exp (-w / 2)) * (2 * π ^ 2 * R ^ 2) ^ j
      ≤ (n.factorial : ℝ) * (BS * Real.exp (-2 * e ^ 2)) * ((18 * π ^ 2) ^ n * e ^ (2 * n)) := by
        gcongr
    _ = _ := by ring

theorem image_term_bound_c {s : ℝ} (hs : 0 ≤ s) (n : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ c : Euc d, 1 ≤ ‖c‖ → ∀ x : Euc d,
      ‖iteratedFDeriv ℝ n (fun y => chi d y * Wt s (qc c y)) x‖ ≤
        K * (‖c‖ ^ (2 * n) * Real.exp (-2 * ‖c‖ ^ 2)) := by
  obtain ⟨K, hK0, hK⟩ := image_comp_bound_c (d := d) hs n
  choose M hM0 hM using fun i => chi_deriv_bound (d := d) i
  set MS := ∑ i ∈ Finset.range (n + 1), M i with hMS
  have hMS0 : 0 ≤ MS := Finset.sum_nonneg fun i _ => hM0 i
  refine ⟨2 ^ n * MS * K, by positivity, fun c hc x => ?_⟩
  set E := ‖c‖ ^ (2 * n) * Real.exp (-2 * ‖c‖ ^ 2) with hE
  have hE0 : 0 ≤ E := by
    have : 0 ≤ ‖c‖ := norm_nonneg _
    positivity
  by_cases hx : 1/8 < ‖x‖
  · rw [iteratedFDeriv_chi_mul_eq_zero _ hx, norm_zero]
    positivity
  · push Not at hx
    have hx4 : ‖x‖ ≤ 1/4 := by linarith
    have hG : ContDiff ℝ ∞' (fun y => Wt s (qc c y)) := (contDiff_Wt s hs).comp (contDiff_qc c)
    refine (norm_iteratedFDeriv_mul_le contDiff_chi hG x (n := n) (by exact_mod_cast le_top)).trans ?_
    calc ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (chi d) x‖ *
          ‖iteratedFDeriv ℝ (n - i) (fun y => Wt s (qc c y)) x‖
        ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * MS * (K * E) := by
          refine Finset.sum_le_sum fun i hi => ?_
          have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
          gcongr
          · exact (hM i x).trans (Finset.single_le_sum (f := M) (fun k _ => hM0 k) hi)
          · exact hK c hc x hx4 (n - i) (Nat.sub_le n i)
      _ = 2 ^ n * MS * K * E := by
          rw [← Finset.sum_mul, ← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
          push_cast; ring

theorem wsq_eq_norm (y : Euc d) (m : Lattice d) :
    wsq (fun i => y i) m = ‖y - Lattice.toEuc m‖ ^ 2 := by
  have h := wsq_eq_qm y m
  unfold qm at h
  have hπ : (0:ℝ) < π ^ 2 := by positivity
  exact (mul_left_cancel₀ hπ.ne' h)

theorem finite_ball_lattice (y0 : Euc d) :
    {m : Lattice d | ‖Lattice.toEuc m - y0‖ < 1}.Finite := by
  set N : Lattice d := fun _ => ⌈‖y0‖ + 1⌉ with hN
  refine (Set.finite_Icc (-N) N).subset fun m hm => ?_
  simp only [Set.mem_setOf_eq] at hm
  have hb : ∀ i, |((m i : ℤ) : ℝ)| ≤ ‖y0‖ + 1 := by
    intro i
    have h1 := abs_coord_le_enorm m i
    have h2 : Lattice.enorm m = ‖Lattice.toEuc m‖ := rfl
    have h3 : ‖Lattice.toEuc m‖ ≤ ‖Lattice.toEuc m - y0‖ + ‖y0‖ := norm_le_norm_sub_add _ _
    linarith
  have hb' : ∀ i, |m i| ≤ N i := by
    intro i
    have h1 : |((m i : ℤ) : ℝ)| ≤ (⌈‖y0‖ + 1⌉ : ℝ) := (hb i).trans (Int.le_ceil _)
    have h2 : |m i| ≤ ⌈‖y0‖ + 1⌉ := by exact_mod_cast h1
    simpa [hN] using h2
  constructor
  · intro i; have := hb' i; simp only [Pi.neg_apply]; linarith [neg_abs_le (m i)]
  · intro i; exact (le_abs_self _).trans (hb' i)

theorem summable_shifted_gauss (y0 : Euc d) (n : ℕ) :
    Summable fun m : Lattice d =>
      ‖Lattice.toEuc m - y0‖ ^ (2 * n) * Real.exp (-2 * ‖Lattice.toEuc m - y0‖ ^ 2) := by
  obtain ⟨M, hM0, hM⟩ := enorm_pow_gauss_bound (2 * n)
  refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_)
    ((summable_gauss_lattice d (1/8) (by norm_num)).mul_left (M * Real.exp (‖y0‖ ^ 2 / 4)))
  set e := ‖Lattice.toEuc m - y0‖ with he
  have he0 : 0 ≤ e := norm_nonneg _
  have h1 := hM e he0
  have h2 : Real.exp (-2 * e ^ 2) ≤ Real.exp (-e ^ 2 / 2) := by
    rw [Real.exp_le_exp]; nlinarith [sq_nonneg e]
  have h3 : ‖Lattice.toEuc m‖ ^ 2 ≤ 2 * e ^ 2 + 2 * ‖y0‖ ^ 2 := by
    have h4 : ‖Lattice.toEuc m‖ ≤ e + ‖y0‖ := by rw [he]; exact norm_le_norm_sub_add _ _
    have h5 := pow_le_pow_left₀ (norm_nonneg _) h4 2
    nlinarith [sq_nonneg (e - ‖y0‖)]
  have h5 : Real.exp (-(1/4) * e ^ 2) ≤ Real.exp (‖y0‖ ^ 2 / 4) * Real.exp (-(1/8) * Lattice.enorm m ^ 2) := by
    rw [← Real.exp_add, Real.exp_le_exp]
    have : Lattice.enorm m = ‖Lattice.toEuc m‖ := rfl
    rw [this]
    nlinarith
  calc e ^ (2 * n) * Real.exp (-2 * e ^ 2) ≤ e ^ (2 * n) * Real.exp (-e ^ 2 / 2) := by gcongr
    _ ≤ M * Real.exp (-(1/4) * e ^ 2) := h1
    _ ≤ M * (Real.exp (‖y0‖ ^ 2 / 4) * Real.exp (-(1/8) * Lattice.enorm m ^ 2)) := by gcongr
    _ = _ := by ring

/-- the sum over the lattice of `W_s(π²|y-m|²)`, the singular part of the kernel -/
def Ssum (d : ℕ) (s : ℝ) (y : Euc d) : ℝ := ∑' m : Lattice d, Wfun s (π ^ 2 * wsq (fun i => y i) m)

theorem Wfun_wsq_eq (s : ℝ) (y : Euc d) (m : Lattice d) :
    Wfun s (π ^ 2 * wsq (fun i => y i) m) = Wfun s (qc (Lattice.toEuc m) y) := by
  rw [wsq_eq_norm]; rfl

theorem contDiffAt_Ssum {s : ℝ} (hs : 0 ≤ s) {y0 : Euc d}
    (hy0 : ∀ m : Lattice d, 0 < wsq (fun i => y0 i) m) :
    ContDiffAt ℝ ∞' (Ssum d s) y0 := by
  set F := (finite_ball_lattice y0).toFinset with hF
  have hmemF : ∀ m, m ∈ F ↔ ‖Lattice.toEuc m - y0‖ < 1 := by
    intro m; simp [hF]
  set T : Euc d → ℝ := fun z => ∑' m : Lattice d,
    (if m ∈ F then 0 else chi d z * Wt s (qc (Lattice.toEuc m - y0) z)) with hT
  have hTsm : ContDiff ℝ ∞' T := by
    choose K hK0 hK using fun n => image_term_bound_c (d := d) hs n
    set v : ℕ → Lattice d → ℝ := fun n m =>
      K n * (‖Lattice.toEuc m - y0‖ ^ (2 * n) * Real.exp (-2 * ‖Lattice.toEuc m - y0‖ ^ 2)) with hv
    refine contDiff_tsum (v := v) (fun m => ?_) (fun n _ => ?_) (fun n m x _ => ?_)
    · by_cases hm : m ∈ F
      · simp only [hm, if_true]; exact contDiff_const
      · simp only [hm, if_false]
        exact contDiff_chi.mul ((contDiff_Wt s hs).comp (contDiff_qc _))
    · exact (summable_shifted_gauss y0 n).mul_left (K n)
    · by_cases hm : m ∈ F
      · simp only [hm, if_true]
        rw [iteratedFDeriv_fun_zero]
        simp only [Pi.zero_apply, norm_zero, hv]
        have := hK0 n
        positivity
      · simp only [hm, if_false]
        refine hK n _ ?_ x
        by_contra h
        exact hm ((hmemF m).2 (not_le.mp h))
  have hfin : ContDiffAt ℝ ∞' (fun y : Euc d => ∑ m ∈ F, Wfun s (qc (Lattice.toEuc m) y)) y0 := by
    refine ContDiffAt.sum fun m _ => ?_
    have hpos : 0 < qc (Lattice.toEuc m) y0 := by
      have := hy0 m
      rw [wsq_eq_norm] at this
      unfold qc
      exact mul_pos (by positivity) this
    exact ((contDiffOn_Wfun s hs).contDiffAt (Ioi_mem_nhds hpos)).comp y0 (contDiff_qc _).contDiffAt
  have hall : ContDiffAt ℝ ∞' (fun y : Euc d => (∑ m ∈ F, Wfun s (qc (Lattice.toEuc m) y)) + T (y - y0)) y0 :=
    hfin.add ((hTsm.contDiffAt).comp y0 (contDiff_id.sub contDiff_const).contDiffAt)
  refine hall.congr_of_eventuallyEq ?_
  filter_upwards [Metric.ball_mem_nhds y0 (by norm_num : (0:ℝ) < 1/16)] with y hy
  have hy' : ‖y - y0‖ < 1/16 := by simpa [dist_eq_norm] using hy
  unfold Ssum
  have hsum := summable_Wfun_wsq hs (fun i => y i)
  set a : Lattice d → ℝ := fun m => Wfun s (qc (Lattice.toEuc m) y) with ha
  have haeq : (fun m => Wfun s (π ^ 2 * wsq (fun i => y i) m)) = a := by
    funext m; exact Wfun_wsq_eq s y m
  rw [haeq] at hsum ⊢
  set b : Lattice d → ℝ := fun m => if m ∈ F then 0 else a m with hb
  set e : Lattice d → ℝ := fun m => if m ∈ F then a m else 0 with he
  have hba : ∀ m, a m = e m + b m := by
    intro m; by_cases hm : m ∈ F <;> simp [hb, he, hm]
  have hTb : T (y - y0) = ∑' m, b m := by
    refine tsum_congr fun m => ?_
    by_cases hm : m ∈ F
    · simp [hb, hm]
    · simp only [hb, hm, if_false]
      have hm1 : 1 ≤ ‖Lattice.toEuc m - y0‖ := not_lt.mp (fun h => hm ((hmemF m).2 h))
      have hch : chi d (y - y0) = 1 := chi_one (by linarith)
      rw [hch, one_mul]
      have hq : qc (Lattice.toEuc m - y0) (y - y0) = qc (Lattice.toEuc m) y := by
        unfold qc; congr 2; abel
      rw [hq]
      simp only [ha]
      have : 1 / 2 < qc (Lattice.toEuc m) y := by
        have h1 : 15/16 ≤ ‖y - Lattice.toEuc m‖ := by
          have h2 : ‖Lattice.toEuc m - y0‖ ≤ ‖Lattice.toEuc m - y‖ + ‖y - y0‖ := by
            have := norm_add_le (Lattice.toEuc m - y) (y - y0)
            rwa [sub_add_sub_cancel] at this
          rw [norm_sub_rev y (Lattice.toEuc m)]
          linarith
        unfold qc
        have h3 : (15/16 : ℝ) ^ 2 ≤ ‖y - Lattice.toEuc m‖ ^ 2 := by gcongr
        nlinarith [Real.pi_gt_three]
      exact ((Wt_eventuallyEq this).self_of_nhds)
  have hE : HasSum e (∑ m ∈ F, a m) := by
    have h0 : HasSum e (∑ m ∈ F, e m) :=
      hasSum_sum_of_ne_finset_zero (s := F) (f := e) (fun m hm => by simp [he, hm])
    rwa [Finset.sum_congr rfl (fun m hm => by simp [he, hm] : ∀ m ∈ F, e m = a m)] at h0
  have hb' : HasSum b (∑' m, a m - ∑ m ∈ F, a m) := by
    have := hsum.hasSum.sub hE
    convert this using 1
    funext m; rw [hba m]; ring
  rw [hTb, hb'.tsum_eq]
  simp only [ha]
  ring

theorem mk_toEuc (m : Lattice d) : Torus.mk (Lattice.toEuc m) = 0 := by
  funext i
  simp only [Torus.mk, Lattice.toEuc, Pi.zero_apply]
  exact (AddCircle.coe_eq_zero_iff (1:ℝ)).2 ⟨m i, by simp⟩

theorem wsq_pos_of_mk_ne_zero {y : Euc d} (hy : Torus.mk y ≠ 0) (m : Lattice d) :
    0 < wsq (fun i => y i) m := by
  rw [wsq_eq_norm]
  have : y - Lattice.toEuc m ≠ 0 := by
    intro h
    apply hy
    have : y = Lattice.toEuc m := sub_eq_zero.mp h
    rw [this, mk_toEuc]
  have := norm_pos_iff.mpr this
  positivity

theorem isOpen_mk_ne_zero : IsOpen {y : Euc d | Torus.mk y ≠ 0} :=
  isOpen_compl_singleton.preimage isOpenQuotientMap_mk.continuous

theorem contDiffAt_periodicRiesz {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {y0 : Euc d}
    (hy0 : Torus.mk y0 ≠ 0) :
    ContDiffAt ℝ ∞' (fun y : Euc d => periodicRiesz d s (Torus.mk y)) y0 := by
  have hS := contDiffAt_Ssum (s := s) hs0 (wsq_pos_of_mk_ne_zero hy0)
  have hF2 := (contDiff_F2 (d := d) hsd).contDiffAt (x := y0)
  have hall : ContDiffAt ℝ ∞' (fun y : Euc d =>
      subA d s * (π ^ ((d:ℝ)/2) * Ssum d s y - 1 / (((d:ℝ) - s)/2)) +
        ∑' k : Lattice d, coefF2 d s k * Torus.cosMode k (Torus.mk y)) y0 :=
    (((hS.const_smul (π ^ ((d:ℝ)/2))).sub contDiffAt_const).const_smul (subA d s)).add hF2
  refine hall.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_mk_ne_zero.mem_nhds hy0] with y hy
  exact decomp1 hd hs0 hsd y (wsq_pos_of_mk_ne_zero hy)

theorem contDiffOn_periodicRiesz {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) :
    ContDiffOn ℝ ∞' (fun y : Euc d => periodicRiesz d s (Torus.mk y)) {y : Euc d | Torus.mk y ≠ 0} :=
  fun y hy => (contDiffAt_periodicRiesz hd hs0 hsd hy).contDiffWithinAt

/-! ### Gradient of the subordination integrand, uniformly away from the origin -/

theorem norm_le_card_of_box {x : Euc d} (hx : ∀ i, |x i| ≤ 1/2) : ‖x‖ ≤ d := by
  have h := norm_toLp_le_sum (d := d) (WithLp.ofLp x)
  rw [WithLp.toLp_ofLp] at h
  refine h.trans ?_
  calc ∑ j, |(WithLp.ofLp x) j| ≤ ∑ _j : Fin d, (1 : ℝ) := Finset.sum_le_sum fun j _ => by
        have := hx j; linarith
    _ = d := by simp

theorem psiG_bound_unif (j : Fin d) {r : ℝ} (hr : 0 < r) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x : Euc d, (∀ i, |x i| ≤ 1/2) → r ≤ ‖x‖ → ∀ u : ℝ, 0 < u →
      |psiG j (Torus.mk x) u| ≤ M * Real.exp (-u) := by
  obtain ⟨K, hK0, hK⟩ := psiG_small_bound (d := d) j
  obtain ⟨M1, hM10, hM1⟩ := psiG_large_bound (d := d) j
  set c0 := min (π ^ 2 * r ^ 2) (π ^ 2 / 8) with hc0
  have hc0p : 0 < c0 := lt_min (by positivity) (by positivity)
  set R : ℝ := (d : ℝ) with hR
  have hR0 : 0 ≤ R := by positivity
  set M0 := π ^ d * (2 * π ^ 2) * (R + K) * (((d + 1).factorial : ℝ) / c0 ^ (d + 1)) with hM0
  have hM00 : 0 ≤ M0 := by positivity
  refine ⟨M0 * Real.exp 1 + M1, by positivity, fun x hx hrx u hu => ?_⟩
  have hxR : ‖x‖ ≤ R := norm_le_card_of_box hx
  rcases le_total u 1 with h1 | h1
  · refine (hK x hx u hu h1).trans ?_
    set w := 1 / u with hw
    have hw0 : 0 < w := by positivity
    have hsq : Real.sqrt (π / u) ≤ π * w := by
      have h2 : 1 ≤ π / u := by rw [le_div_iff₀ hu]; linarith [Real.pi_gt_three]
      have h3 : Real.sqrt (π / u) ≤ π / u := Real.sqrt_le_iff.mpr ⟨by linarith, by nlinarith⟩
      calc Real.sqrt (π / u) ≤ π / u := h3
        _ = π * w := by rw [hw]; ring
    have he1 : Real.exp (-(π ^ 2 * ‖x‖ ^ 2 / u)) ≤ Real.exp (-(c0 * w)) := by
      rw [Real.exp_le_exp, hw]
      have : c0 ≤ π ^ 2 * ‖x‖ ^ 2 := (min_le_left _ _).trans (by gcongr)
      have : c0 * (1 / u) ≤ π ^ 2 * ‖x‖ ^ 2 * (1 / u) := by gcongr
      have e : π ^ 2 * ‖x‖ ^ 2 / u = π ^ 2 * ‖x‖ ^ 2 * (1 / u) := by ring
      linarith
    have he2 : Real.exp (-(π ^ 2 / (8 * u))) ≤ Real.exp (-(c0 * w)) := by
      rw [Real.exp_le_exp, hw]
      have : c0 ≤ π ^ 2 / 8 := min_le_right _ _
      have : c0 * (1 / u) ≤ π ^ 2 / 8 * (1 / u) := by gcongr
      have e : π ^ 2 / (8 * u) = π ^ 2 / 8 * (1 / u) := by field_simp
      linarith
    have hpe := pow_exp_bound c0 hc0p (d + 1) w hw0.le
    have hfin : Real.sqrt (π / u) ^ d * (2 * π ^ 2 / u) *
        (‖x‖ * Real.exp (-(π ^ 2 * ‖x‖ ^ 2 / u)) + K * Real.exp (-(π ^ 2 / (8 * u)))) ≤ M0 := by
      have hxe : ‖x‖ * Real.exp (-(π ^ 2 * ‖x‖ ^ 2 / u)) ≤ R * Real.exp (-(c0 * w)) :=
        mul_le_mul hxR he1 (Real.exp_pos _).le hR0
      calc Real.sqrt (π / u) ^ d * (2 * π ^ 2 / u) *
            (‖x‖ * Real.exp (-(π ^ 2 * ‖x‖ ^ 2 / u)) + K * Real.exp (-(π ^ 2 / (8 * u))))
          ≤ (π * w) ^ d * (2 * π ^ 2 * w) * (R * Real.exp (-(c0 * w)) + K * Real.exp (-(c0 * w))) := by
            have e : 2 * π ^ 2 / u = 2 * π ^ 2 * w := by rw [hw]; ring
            rw [e]
            have hK' : K * Real.exp (-(π ^ 2 / (8 * u))) ≤ K * Real.exp (-(c0 * w)) := by gcongr
            have hs' : Real.sqrt (π / u) ^ d ≤ (π * w) ^ d := by gcongr
            gcongr
        _ = π ^ d * (2 * π ^ 2) * (R + K) * (w ^ (d + 1) * Real.exp (-(c0 * w))) := by ring
        _ ≤ M0 := by rw [hM0]; gcongr
    have : 1 ≤ Real.exp 1 * Real.exp (-u) := by
      rw [← Real.exp_add]; apply Real.one_le_exp; linarith
    nlinarith [Real.exp_pos (-u), Real.exp_pos 1]
  · refine (hM1 _ u h1).trans ?_
    have : 0 ≤ M0 * Real.exp 1 * Real.exp (-u) := by positivity
    nlinarith [Real.exp_pos (-u)]

/-- the gradient (a continuous linear functional) of `y ↦ Ψ(t, mk y)` -/
def psiGrad (y : Euc d) (t : ℝ) : Euc d →L[ℝ] ℝ :=
  ∑ j, psiG j (Torus.mk y) t • (EuclideanSpace.proj j : Euc d →L[ℝ] ℝ)

theorem psiGrad_apply (y : Euc d) (t : ℝ) (v : Euc d) :
    psiGrad y t v = ∑ j, psiG j (Torus.mk y) t * v j := by
  simp [psiGrad, ContinuousLinearMap.sum_apply]

theorem summable_psiG_term (j : Fin d) {t : ℝ} (ht : 0 < t) (x : Torus d) :
    Summable fun k : Lattice d =>
      -(Real.exp (-t * Lattice.enorm k ^ 2) * (2 * π * ((k j : ℤ) : ℝ)) * Torus.sinMode k x) := by
  refine Summable.of_norm_bounded ((summable_pow_gauss_lattice d ht 1).mul_left (2 * π)) fun k => ?_
  rw [norm_neg, Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _),
    abs_of_pos (by positivity : (0:ℝ) < 2 * π)]
  have h1 := abs_coord_le_enorm k j
  have hk0 : 0 ≤ Lattice.enorm k := norm_nonneg _
  have h2 : |Torus.sinMode k x| ≤ 1 := by
    rw [Torus.sinMode]; exact (Complex.abs_im_le_norm _).trans (by rw [Torus.norm_mode])
  calc Real.exp (-t * Lattice.enorm k ^ 2) * (2 * π * |((k j : ℤ) : ℝ)|) * |Torus.sinMode k x|
      ≤ Real.exp (-t * Lattice.enorm k ^ 2) * (2 * π * Lattice.enorm k) * 1 := by gcongr
    _ = _ := by ring

theorem hasFDerivAt_psiFn {t : ℝ} (ht : 0 < t) (y : Euc d) :
    HasFDerivAt (fun y : Euc d => psiFn (Torus.mk y) t) (psiGrad y t) y := by
  set f : Lattice d → Euc d → ℝ := fun k y =>
    if k = 0 then 0 else Real.exp (-t * Lattice.enorm k ^ 2) * Real.cos (Torus.freqFunctional k y) with hf
  set f' : Lattice d → Euc d → (Euc d →L[ℝ] ℝ) := fun k y =>
    if k = 0 then 0 else (-(Real.exp (-t * Lattice.enorm k ^ 2) * Real.sin (Torus.freqFunctional k y))) •
      Torus.freqFunctional k with hf'
  have hfeq : (fun y : Euc d => psiFn (Torus.mk y) t) = fun y => ∑' k, f k y := by
    funext y
    unfold psiFn
    refine tsum_congr fun k => ?_
    by_cases hk : k = 0
    · simp [hf, hk]
    · simp only [hf, hk, if_false, Torus.cosMode_mk, Torus.freqFunctional_apply]
  have hder : ∀ k y, HasFDerivAt (f k) (f' k y) y := by
    intro k y
    by_cases hk : k = 0
    · simp only [hf, hf', hk, if_true]; exact hasFDerivAt_const _ _
    · simp only [hf, hf', hk, if_false]
      have h1 := (Real.hasDerivAt_cos (Torus.freqFunctional k y)).comp_hasFDerivAt y
        (Torus.freqFunctional k).hasFDerivAt
      have h2 := h1.const_mul (Real.exp (-t * Lattice.enorm k ^ 2))
      have h3 : HasFDerivAt (fun y => Real.exp (-t * Lattice.enorm k ^ 2) *
          Real.cos (Torus.freqFunctional k y))
          (Real.exp (-t * Lattice.enorm k ^ 2) • (-Real.sin (Torus.freqFunctional k y) • Torus.freqFunctional k)) y := h2
      convert h3 using 1
      simp only [smul_smul, mul_neg]
  have hbd : ∀ k y, ‖f' k y‖ ≤ 2 * π * (Lattice.enorm k ^ 1 * Real.exp (-t * Lattice.enorm k ^ 2)) := by
    intro k y
    by_cases hk : k = 0
    · subst hk
      simp only [hf', if_true, norm_zero]
      have : 0 ≤ Lattice.enorm (0 : Lattice d) := norm_nonneg _
      exact mul_nonneg (by positivity) (mul_nonneg (pow_nonneg this _) (Real.exp_pos _).le)
    · simp only [hf', hk, if_false]
      rw [norm_smul, norm_neg, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      have h1 := Real.abs_sin_le_one (Torus.freqFunctional k y)
      have h2 := Torus.norm_freqFunctional_le k
      have hk0 : 0 ≤ Lattice.enorm k := norm_nonneg _
      calc Real.exp (-t * Lattice.enorm k ^ 2) * |Real.sin (Torus.freqFunctional k y)| *
            ‖Torus.freqFunctional k‖
          ≤ Real.exp (-t * Lattice.enorm k ^ 2) * 1 * (2 * π * Lattice.enorm k) := by gcongr
        _ = _ := by ring
  have hf0 : Summable fun k => f k y := by
    refine (psi_summable (Torus.mk y) ht).congr fun k => ?_
    by_cases hk : k = 0
    · simp [hf, hk]
    · simp only [hf, hk, if_false, Torus.cosMode_mk, Torus.freqFunctional_apply]
  have hH := hasFDerivAt_tsum ((summable_pow_gauss_lattice d ht 1).mul_left (2 * π)) hder hbd hf0 y
  rw [hfeq]
  convert hH using 1
  -- identify the derivative
  have hsumm : Summable fun k => f' k y :=
    Summable.of_norm_bounded ((summable_pow_gauss_lattice d ht 1).mul_left (2 * π)) (hbd · y)
  ext v
  rw [psiGrad_apply]
  have hv : (∑' k, f' k y) v = ∑' k, f' k y v := by
    have := (ContinuousLinearMap.apply ℝ ℝ v).map_tsum hsumm
    simpa using this
  rw [hv]
  have hpsi : ∀ j, psiG j (Torus.mk y) t * v j =
      ∑' k, -(Real.exp (-t * Lattice.enorm k ^ 2) * (2 * π * ((k j : ℤ) : ℝ)) * Torus.sinMode k (Torus.mk y)) * v j := by
    intro j
    unfold psiG
    rw [tsum_mul_right]
  simp_rw [hpsi]
  rw [← Summable.tsum_finsetSum (fun j _ => (summable_psiG_term j ht (Torus.mk y)).mul_right (v j))]
  refine tsum_congr fun k => ?_
  by_cases hk : k = 0
  · simp [hf', hk]
  · simp only [hf', hk, if_false, ContinuousLinearMap.smul_apply, smul_eq_mul, Torus.freqFunctional_apply,
      Torus.sinMode_mk, Lattice.dot, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring

theorem exists_lattice_of_mk_eq {x y : Euc d} (h : Torus.mk x = Torus.mk y) :
    ∃ m : Lattice d, x = y + Lattice.toEuc m := by
  have : ∀ i, ∃ n : ℤ, (n : ℝ) = x i - y i := by
    intro i
    have hi := congrFun h i
    simp only [Torus.mk] at hi
    have : ((x i - y i : ℝ) : UnitAddCircle) = 0 := by
      rw [AddCircle.coe_sub, hi, sub_self]
    obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (1:ℝ)).mp this
    exact ⟨n, by simpa using hn⟩
  choose m hm using this
  refine ⟨m, ?_⟩
  ext i
  simp [Lattice.toEuc, hm]

theorem norm_sub_toEuc_ge_of_box {x : Euc d} (hx : ∀ i, |x i| ≤ 1/2) (m : Lattice d) :
    ‖x‖ ≤ ‖x - Lattice.toEuc m‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)
  simp only [Real.norm_eq_abs, sq_abs, Lattice.toEuc]
  have := abs_sq_le_sub_sq (x i) (hx i) (m i)
  simp only [PiLp.sub_apply]
  nlinarith [sq_abs (x i)]

/-- uniform bound for the gradient of the subordination integrand near a point of the box
(not the origin). -/
theorem psiG_bound_near (j : Fin d) {x0 : Euc d} (hx0 : ∀ i, |x0 i| ≤ 1/2) (hx0n : x0 ≠ 0) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ y : Euc d, ‖y - x0‖ < ‖x0‖ / 2 → ∀ u : ℝ, 0 < u →
      |psiG j (Torus.mk y) u| ≤ M * Real.exp (-u) := by
  have hρ : 0 < ‖x0‖ := norm_pos_iff.mpr hx0n
  obtain ⟨M, hM0, hM⟩ := psiG_bound_unif (d := d) j (r := ‖x0‖ / 2) (by positivity)
  refine ⟨M, hM0, fun y hy u hu => ?_⟩
  obtain ⟨x, hxm, hxb⟩ := exists_mk_box (Torus.mk y)
  obtain ⟨m, hm⟩ := exists_lattice_of_mk_eq hxm
  have hneg : Lattice.toEuc (-m) = -Lattice.toEuc m := by ext i; simp [Lattice.toEuc]
  have h1 : ‖x0‖ ≤ ‖x0 + Lattice.toEuc m‖ := by
    have := norm_sub_toEuc_ge_of_box hx0 (-m)
    rwa [hneg, sub_neg_eq_add] at this
  have h3 : ‖x0 + Lattice.toEuc m‖ ≤ ‖x0 - y‖ + ‖y + Lattice.toEuc m‖ := by
    have := norm_add_le (x0 - y) (y + Lattice.toEuc m)
    rwa [show x0 - y + (y + Lattice.toEuc m) = x0 + Lattice.toEuc m by abel] at this
  have h4 : ‖x0 - y‖ = ‖y - x0‖ := norm_sub_rev _ _
  have hr : ‖x0‖ / 2 ≤ ‖x‖ := by rw [hm]; linarith
  have := hM x hxb hr u hu
  rwa [hxm] at this

theorem norm_psiGrad_le (y : Euc d) (t : ℝ) : ‖psiGrad y t‖ ≤ ∑ j, |psiG j (Torus.mk y) t| := by
  refine ContinuousLinearMap.opNorm_le_bound _ (Finset.sum_nonneg fun j _ => abs_nonneg _) fun v => ?_
  rw [psiGrad_apply, Real.norm_eq_abs, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [abs_mul]
  gcongr
  have := PiLp.norm_apply_le v j
  rwa [Real.norm_eq_abs] at this

theorem mk_ne_zero_ne_zero {x : Euc d} (h : Torus.mk x ≠ 0) : x ≠ 0 := by
  intro hx
  apply h
  rw [hx]
  funext i
  simp [Torus.mk]

theorem hasFDerivAt_intPsi {s : ℝ} (hsd : s < d) {x0 : Euc d} (hx0 : ∀ i, |x0 i| ≤ 1/2)
    (hx0n : Torus.mk x0 ≠ 0) :
    HasFDerivAt (fun y : Euc d => ∫ t in Ioi (0:ℝ), t ^ (((d:ℝ) - s)/2 - 1) * psiFn (Torus.mk y) t)
      (∑ j, (∫ t in Ioi (0:ℝ), t ^ (((d:ℝ) - s)/2 - 1) * psiG j (Torus.mk x0) t) •
        (EuclideanSpace.proj j : Euc d →L[ℝ] ℝ)) x0 := by
  set a : ℝ := ((d:ℝ) - s) / 2 with ha_def
  have ha : 0 < a := by rw [ha_def]; linarith
  have hx0z : x0 ≠ 0 := mk_ne_zero_ne_zero hx0n
  have hρ : 0 < ‖x0‖ := norm_pos_iff.mpr hx0z
  choose M hM0 hM using fun j : Fin d => psiG_bound_near j hx0 hx0z
  set C : ℝ := ∑ j, M j with hC
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun j _ => hM0 j
  have hbdint : Integrable (fun t : ℝ => C * (Real.exp (-t) * t ^ (a - 1))) (volume.restrict (Ioi (0:ℝ))) :=
    (Real.GammaIntegral_convergent ha).const_mul C
  have hcontF : ∀ y : Euc d, ContinuousOn (fun t : ℝ => t ^ (a - 1) * psiFn (Torus.mk y) t) (Ioi 0) :=
    fun y => ContinuousOn.mul (continuousOn_id.rpow_const fun t ht => Or.inl (ne_of_gt ht))
      (psi_continuousOn _)
  have hcontF' : ContinuousOn (fun t : ℝ => t ^ (a - 1) • psiGrad x0 t) (Ioi 0) := by
    have : (fun t : ℝ => t ^ (a - 1) • psiGrad x0 t) =
        fun t => ∑ j, (t ^ (a - 1) * psiG j (Torus.mk x0) t) • (EuclideanSpace.proj j : Euc d →L[ℝ] ℝ) := by
      funext t
      simp only [psiGrad, Finset.smul_sum, smul_smul, smul_eq_mul]
    rw [this]
    refine continuousOn_finset_sum _ fun j _ => ?_
    exact (ContinuousOn.mul (continuousOn_id.rpow_const fun t ht => Or.inl (ne_of_gt ht))
      (psiG_continuousOn j _)).smul continuousOn_const
  have key := hasFDerivAt_integral_of_dominated_of_fderiv_le
    (μ := volume.restrict (Ioi (0:ℝ)))
    (F := fun (y : Euc d) (t : ℝ) => t ^ (a - 1) * psiFn (Torus.mk y) t)
    (F' := fun (y : Euc d) (t : ℝ) => t ^ (a - 1) • psiGrad y t)
    (x₀ := x0) (s := Metric.ball x0 (‖x0‖ / 2))
    (bound := fun t => C * (Real.exp (-t) * t ^ (a - 1)))
    (Metric.ball_mem_nhds _ (by positivity))
    (Filter.Eventually.of_forall fun y => (hcontF y).aestronglyMeasurable measurableSet_Ioi)
    (integrableOn_psi hsd (Torus.mk x0) hx0n)
    (hcontF'.aestronglyMeasurable measurableSet_Ioi)
    ?_ hbdint ?_
  · convert key using 1
    -- identify the derivative
    have hint : ∀ j, Integrable (fun t : ℝ => t ^ (a - 1) * psiG j (Torus.mk x0) t)
        (volume.restrict (Ioi (0:ℝ))) := by
      intro j
      refine Integrable.mono' ((Real.GammaIntegral_convergent ha).const_mul (M j)) ?_ ?_
      · exact (ContinuousOn.mul (continuousOn_id.rpow_const fun t ht => Or.inl (ne_of_gt ht))
          (psiG_continuousOn j _)).aestronglyMeasurable measurableSet_Ioi
      · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun t ht => ?_)
        have ht' : 0 < t := ht
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.rpow_pos_of_pos ht' _)]
        have h1 := hM j x0 (by simpa using hρ) t ht'
        calc t ^ (a - 1) * |psiG j (Torus.mk x0) t| ≤ t ^ (a - 1) * (M j * Real.exp (-t)) := by gcongr
          _ = _ := by ring
    have : (fun t : ℝ => t ^ (a - 1) • psiGrad x0 t) =
        fun t => ∑ j, (t ^ (a - 1) * psiG j (Torus.mk x0) t) • (EuclideanSpace.proj j : Euc d →L[ℝ] ℝ) := by
      funext t
      simp only [psiGrad, Finset.smul_sum, smul_smul, smul_eq_mul]
    rw [this, integral_finset_sum _ fun j _ => (hint j).smul_const _]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_smul_const]
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun t ht y hy => ?_)
    have ht' : 0 < t := ht
    have hy' : ‖y - x0‖ < ‖x0‖ / 2 := by simpa [dist_eq_norm] using hy
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos ht' _)]
    calc t ^ (a - 1) * ‖psiGrad y t‖ ≤ t ^ (a - 1) * ∑ j, |psiG j (Torus.mk y) t| := by
          gcongr; exact norm_psiGrad_le y t
      _ ≤ t ^ (a - 1) * ∑ j, (M j * Real.exp (-t)) := by
          gcongr with j _
          exact hM j y hy' t ht'
      _ = _ := by rw [← Finset.sum_mul]; ring
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun t ht y _ => ?_)
    have ht' : 0 < t := ht
    exact (hasFDerivAt_psiFn ht' y).const_mul (t ^ (a - 1)) |>.congr_fderiv (by simp [smul_eq_mul])

theorem hasFDerivAt_periodicRiesz_box {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {x0 : Euc d}
    (hx0 : ∀ i, |x0 i| ≤ 1/2) (hx0n : Torus.mk x0 ≠ 0) :
    HasFDerivAt (fun y : Euc d => periodicRiesz d s (Torus.mk y))
      (∑ j, gradComp s j (Torus.mk x0) • (EuclideanSpace.proj j : Euc d →L[ℝ] ℝ)) x0 := by
  have h := (hasFDerivAt_intPsi (s := s) hsd hx0 hx0n).const_mul (subA d s)
  have heq : (fun y : Euc d => periodicRiesz d s (Torus.mk y)) =ᶠ[𝓝 x0]
      fun y => subA d s * ∫ t in Ioi (0:ℝ), t ^ (((d:ℝ) - s) / 2 - 1) * psiFn (Torus.mk y) t := by
    filter_upwards [isOpen_mk_ne_zero.mem_nhds hx0n] with y hy
    exact periodicRiesz_eq_integral hd hs0 hsd (Torus.mk y) hy
  refine (h.congr_of_eventuallyEq heq).congr_fderiv ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_smul, gradComp]

theorem hasFDerivAt_periodicRiesz {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {y0 : Euc d}
    (hy0 : Torus.mk y0 ≠ 0) :
    HasFDerivAt (fun y : Euc d => periodicRiesz d s (Torus.mk y))
      (∑ j, (periodicRieszGrad d s (Torus.mk y0)) j • (EuclideanSpace.proj j : Euc d →L[ℝ] ℝ)) y0 := by
  obtain ⟨x0, hxm, hxb⟩ := exists_mk_box (Torus.mk y0)
  obtain ⟨m, hm⟩ := exists_lattice_of_mk_eq hxm
  have hx0n : Torus.mk x0 ≠ 0 := by rw [hxm]; exact hy0
  have hx0z : x0 ≠ 0 := mk_ne_zero_ne_zero hx0n
  have h := hasFDerivAt_periodicRiesz_box hd hs0 hsd hxb hx0n
  have h2 : HasFDerivAt (fun y : Euc d => periodicRiesz d s (Torus.mk (y + Lattice.toEuc m)))
      (∑ j, gradComp s j (Torus.mk x0) • (EuclideanSpace.proj j : Euc d →L[ℝ] ℝ)) y0 := by
    have hadd : HasFDerivAt (fun y : Euc d => y + Lattice.toEuc m) (ContinuousLinearMap.id ℝ (Euc d)) y0 :=
      (hasFDerivAt_id y0).add_const _
    have hm' : y0 + Lattice.toEuc m = x0 := hm.symm
    have h' : HasFDerivAt (fun y : Euc d => periodicRiesz d s (Torus.mk y))
        (∑ j, gradComp s j (Torus.mk x0) • (EuclideanSpace.proj j : Euc d →L[ℝ] ℝ)) (y0 + Lattice.toEuc m) := by
      rw [hm']; exact h
    exact (h'.comp y0 hadd).congr_fderiv (ContinuousLinearMap.comp_id _)
  have hfun : (fun y : Euc d => periodicRiesz d s (Torus.mk (y + Lattice.toEuc m))) =
      fun y => periodicRiesz d s (Torus.mk y) := by
    funext y
    rw [mk_add, mk_toEuc, add_zero]
  rw [hfun] at h2
  have hgrad := periodicRieszGrad_eq hsd x0 hxb hx0z
  rw [hxm] at hgrad hx0n
  rw [hxm] at h2
  convert h2 using 2
  rw [hgrad]

theorem periodicRieszGrad_hasGradientAt {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d)
    {x : Torus d} (hx : x ≠ 0) (y₀ : Euc d) (hy₀ : Torus.mk y₀ = x) :
    HasGradientAt (fun y : Euc d => periodicRiesz d s (Torus.mk y)) (periodicRieszGrad d s x) y₀ := by
  subst hy₀
  have h := hasFDerivAt_periodicRiesz hd hs0 hsd hx
  rw [hasGradientAt_iff_hasFDerivAt]
  convert h using 1
  ext v
  simp [PiLp.inner_apply, mul_comm]

theorem lift_periodicRieszGrad_eq_gradient {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d)
    {y : Euc d} (hy : Torus.mk y ≠ 0) :
    Torus.lift (periodicRieszGrad d s) y =
      (InnerProductSpace.toDual ℝ (Euc d)).symm (fderiv ℝ (fun y : Euc d => periodicRiesz d s (Torus.mk y)) y) := by
  have h := (periodicRieszGrad_hasGradientAt hd hs0 hsd hy y rfl).gradient
  unfold gradient at h
  exact h.symm

theorem periodicRieszGrad_smoothOffZero' {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) :
    ContDiffOn ℝ ∞' (Torus.lift (periodicRieszGrad d s)) {x : Euc d | Torus.mk x ≠ 0} := by
  have hU := isOpen_mk_ne_zero (d := d)
  have h1 := (contDiffOn_periodicRiesz hd hs0 hsd (s := s)).fderiv_of_isOpen hU (m := ∞') (by simp)
  have h2 := ((InnerProductSpace.toDual ℝ (Euc d)).symm.contDiff (n := ∞')).comp_contDiffOn h1
  exact h2.congr fun y hy => lift_periodicRieszGrad_eq_gradient hd hs0 hsd hy

end HRS.KernelGrad
