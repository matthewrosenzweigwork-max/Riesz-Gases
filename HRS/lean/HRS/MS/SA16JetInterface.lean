import HRS.MS.SA16StrongSL6
import HRS.MS.SA16StrongSL5

/-!
# S.A.16 closed-jet interface

A smooth function all of whose derivatives up to order `m` lie in `L^p` has its (coordinate) jet in
`WmpSpace d m p`: cut off with `χ(x/R)` and let `R → ∞` (the jet of the cut-off converges in `L^p` because
the derivatives of `χ(·/R)` are uniformly bounded and `χ(·/R) = 1` on the ball of radius `R`).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16
open HRS HRS.Whole HRS.Whole.AppendixA

section Jet
variable {d : ℕ}

/-- a coordinate partial derivative is bounded by the norm of the iterated derivative -/
lemma sa16j_partial_le {j : ℕ} (idx : Fin j → Fin d) (g : Euc d → ℝ) (x : Euc d) :
    |partialDeriv idx g x| ≤ ‖iteratedFDeriv ℝ j g x‖ := by
  unfold partialDeriv
  have h := (iteratedFDeriv ℝ j g x).le_opNorm (fun l => EuclideanSpace.single (idx l) (1 : ℝ))
  have hn : ∏ l : Fin j, ‖(EuclideanSpace.single (idx l) (1 : ℝ) : Euc d)‖ = 1 := by
    simp [EuclideanSpace.norm_single]
  rw [hn, mul_one] at h
  simpa [Real.norm_eq_abs] using h

/-- sup-norm of the jet -/
lemma sa16j_jet_norm_le (m : ℕ) (g : Euc d → ℝ) (x : Euc d) :
    ‖wJet m g x‖ ≤ ∑ j ∈ Finset.range (m + 1), ‖iteratedFDeriv ℝ j g x‖ := by
  refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun j _ => norm_nonneg _)).2 fun τ => ?_
  have h1 : ‖wJet m g x τ‖ ≤ ‖iteratedFDeriv ℝ (τ.1 : ℕ) g x‖ := by
    rw [Real.norm_eq_abs]
    exact sa16j_partial_le τ.2 g x
  refine h1.trans ?_
  exact Finset.single_le_sum (f := fun j => ‖iteratedFDeriv ℝ j g x‖) (fun j _ => norm_nonneg _)
    (Finset.mem_range.2 (by have := τ.1.2; omega))

/-- the fixed cutoff bump (`1` on the unit ball, supported in the ball of radius `2`) -/
def sa16j_bump (d : ℕ) : ContDiffBump (0 : Euc d) := ⟨1, 2, one_pos, one_lt_two⟩

/-- the scaled cutoff -/
def sa16j_chi (d : ℕ) (R : ℝ) : Euc d → ℝ := fun y => sa16j_bump d (R⁻¹ • y)

/-- the cut-off of `f` -/
def sa16j_cutf (d : ℕ) (R : ℝ) (f : Euc d → ℝ) : Euc d → ℝ := fun y => sa16j_chi d R y * f y

lemma sa16j_chi_contDiff (d : ℕ) (R : ℝ) : ContDiff ℝ ∞ (sa16j_chi d R) :=
  (sa16j_bump d).contDiff.comp (contDiff_id.const_smul R⁻¹)

lemma sa16j_chi_support (d : ℕ) {R : ℝ} (hR : 0 < R) : HasCompactSupport (sa16j_chi d R) :=
  (sa16j_bump d).hasCompactSupport.comp_smul (inv_ne_zero hR.ne')

lemma sa16j_chi_one (d : ℕ) {R : ℝ} (hR : 0 < R) {y : Euc d} (hy : ‖y‖ ≤ R) :
    sa16j_chi d R y = 1 := by
  unfold sa16j_chi
  refine (sa16j_bump d).one_of_mem_closedBall ?_
  show R⁻¹ • y ∈ Metric.closedBall (0 : Euc d) 1
  rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hR.le)]
  calc R⁻¹ * ‖y‖ ≤ R⁻¹ * R := mul_le_mul_of_nonneg_left hy (inv_nonneg.2 hR.le)
    _ = 1 := inv_mul_cancel₀ hR.ne'

lemma sa16j_cut_bound (d m : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ R : ℝ, 1 ≤ R → ∀ i ≤ m, ∀ x : Euc d,
      ‖iteratedFDeriv ℝ i (sa16j_chi d R) x‖ ≤ B := by
  obtain ⟨B, hB0, hB⟩ := (sa16j_bump d).hasCompactSupport.exists_bound_iteratedFDeriv
    (sa16j_bump d).contDiff m
  refine ⟨B, hB0, fun R hR i hi x => ?_⟩
  set g : Euc d →L[ℝ] Euc d := R⁻¹ • ContinuousLinearMap.id ℝ (Euc d) with hg
  have hfun : sa16j_chi d R = (⇑(sa16j_bump d)) ∘ g := by
    funext y; simp [hg, sa16j_chi]
  have hR0 : 0 < R := by linarith
  have hgn : ‖g‖ ≤ 1 := by
    refine (norm_smul_le R⁻¹ (ContinuousLinearMap.id ℝ (Euc d))).trans ?_
    rw [Real.norm_of_nonneg (inv_nonneg.2 hR0.le)]
    calc R⁻¹ * ‖ContinuousLinearMap.id ℝ (Euc d)‖ ≤ R⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (inv_nonneg.2 hR0.le)
      _ ≤ 1 := by rw [mul_one]; exact inv_le_one_of_one_le₀ hR
  rw [hfun, g.iteratedFDeriv_comp_right (sa16j_bump d).contDiff x (by exact_mod_cast le_top)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have hprod : ∏ _ : Fin i, ‖g‖ ≤ 1 := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact pow_le_one₀ (norm_nonneg _) hgn
  calc ‖iteratedFDeriv ℝ i (sa16j_bump d) (g x)‖ * ∏ _ : Fin i, ‖g‖ ≤ B * 1 :=
        mul_le_mul (hB i hi _) hprod (Finset.prod_nonneg fun _ _ => norm_nonneg _) hB0
    _ = B := mul_one B

/-- the sum of the norms of the derivatives up to order `m` -/
def sa16j_S (d m : ℕ) (f : Euc d → ℝ) (x : Euc d) : ℝ :=
  ∑ j ∈ Finset.range (m + 1), ‖iteratedFDeriv ℝ j f x‖

lemma sa16j_S_nonneg (d m : ℕ) (f : Euc d → ℝ) (x : Euc d) : 0 ≤ sa16j_S d m f x :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

/-- pointwise bound for the cut-off error -/
lemma sa16j_diff_bound {f : Euc d → ℝ} (hf : ContDiff ℝ ∞ f) (m : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ R : ℝ, 1 ≤ R → ∀ x : Euc d,
      ‖wJet m (sa16j_cutf d R f) x - wJet m f x‖ ≤
        {x : Euc d | R ≤ ‖x‖}.indicator (fun x => K * sa16j_S d m f x) x := by
  obtain ⟨B, hB0, hB⟩ := sa16j_cut_bound d m
  refine ⟨((m + 1) * 2 ^ m * B + 1), by positivity, fun R hR x => ?_⟩
  have hR0 : 0 < R := by linarith
  by_cases hx : ‖x‖ < R
  · have hev : sa16j_cutf d R f =ᶠ[𝓝 x] f := by
      have : Metric.ball (0 : Euc d) R ∈ 𝓝 x :=
        Metric.isOpen_ball.mem_nhds (by simpa using hx)
      filter_upwards [this] with y hy
      have hy' : ‖y‖ ≤ R := by simpa using (mem_ball_zero_iff.1 hy).le
      simp [sa16j_cutf, sa16j_chi_one d hR0 hy']
    have heq : wJet m (sa16j_cutf d R f) x = wJet m f x := by
      funext τ
      simp only [wJet, partialDeriv]
      rw [(hev.iteratedFDeriv ℝ _).self_of_nhds]
    rw [heq, sub_self, norm_zero]
    have hxn : x ∉ {x : Euc d | R ≤ ‖x‖} := fun h => absurd (not_le.2 hx) (by simpa using h)
    rw [Set.indicator_of_notMem hxn]
  · push Not at hx
    have hxm : x ∈ {x : Euc d | R ≤ ‖x‖} := hx
    rw [Set.indicator_of_mem hxm]
    have hS0 := sa16j_S_nonneg d m f x
    have h1 : ‖wJet m f x‖ ≤ sa16j_S d m f x := sa16j_jet_norm_le m f x
    have hF : ContDiff ℝ ∞ (sa16j_cutf d R f) := (sa16j_chi_contDiff d R).mul hf
    have h3 : ∀ j ≤ m, ‖iteratedFDeriv ℝ j (sa16j_cutf d R f) x‖ ≤ 2 ^ m * B * sa16j_S d m f x := by
      intro j hj
      have h4 := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (sa16j_chi_contDiff d R) hf x
        (n := j) (by exact_mod_cast le_top)
      refine h4.trans ?_
      have h5 : ∀ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i (sa16j_chi d R) x‖ *
          ‖iteratedFDeriv ℝ (j - i) f x‖ ≤ 2 ^ m * B * ‖iteratedFDeriv ℝ (j - i) f x‖ := by
        intro i hi
        have hi' : i ≤ j := by have := Finset.mem_range.1 hi; omega
        have hc : (j.choose i : ℝ) ≤ 2 ^ m := by
          calc (j.choose i : ℝ) ≤ 2 ^ j := by exact_mod_cast Nat.choose_le_two_pow j i
            _ ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) hj
        have hd := hB R hR i (hi'.trans hj) x
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul hc hd (norm_nonneg _) (by positivity)) (norm_nonneg _)
      refine (Finset.sum_le_sum h5).trans ?_
      rw [← Finset.mul_sum]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      have h6 : ∑ i ∈ Finset.range (j + 1), ‖iteratedFDeriv ℝ (j - i) f x‖ =
          ∑ i ∈ Finset.range (j + 1), ‖iteratedFDeriv ℝ i f x‖ := by
        rw [← Finset.sum_range_reflect (fun i => ‖iteratedFDeriv ℝ i f x‖) (j + 1)]
        refine Finset.sum_congr rfl fun i hi => ?_
        congr 3
      rw [h6]
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_subset_range.2 (by omega)) (fun _ _ _ => norm_nonneg _)
    have h2 : ‖wJet m (sa16j_cutf d R f) x‖ ≤ (m + 1) * (2 ^ m * B * sa16j_S d m f x) := by
      refine (sa16j_jet_norm_le m _ x).trans ?_
      calc ∑ j ∈ Finset.range (m + 1), ‖iteratedFDeriv ℝ j (sa16j_cutf d R f) x‖
          ≤ ∑ j ∈ Finset.range (m + 1), (2 ^ m * B * sa16j_S d m f x) :=
            Finset.sum_le_sum fun j hj => h3 j (by have := Finset.mem_range.1 hj; omega)
        _ = (m + 1) * (2 ^ m * B * sa16j_S d m f x) := by simp
    calc ‖wJet m (sa16j_cutf d R f) x - wJet m f x‖
        ≤ ‖wJet m (sa16j_cutf d R f) x‖ + ‖wJet m f x‖ := norm_sub_le _ _
      _ ≤ (m + 1) * (2 ^ m * B * sa16j_S d m f x) + sa16j_S d m f x := add_le_add h2 h1
      _ = ((m + 1) * 2 ^ m * B + 1) * sa16j_S d m f x := by ring

lemma sa16j_jet_cont {g : Euc d → ℝ} (hg : ContDiff ℝ ∞ g) (m : ℕ) : Continuous (wJet m g) := by
  refine continuous_pi fun τ => ?_
  have h := hg.continuous_iteratedFDeriv (m := (τ.1 : ℕ)) (by exact_mod_cast le_top)
  exact (continuous_eval_const (fun l => EuclideanSpace.single (τ.2 l) (1 : ℝ))).comp h

lemma sa16j_jet_support {g : Euc d → ℝ} (hg : HasCompactSupport g) (m : ℕ) :
    HasCompactSupport (wJet m g) := by
  refine HasCompactSupport.intro hg.isCompact (fun x hx => ?_)
  have hev : g =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.1 hx
  funext τ
  simp only [wJet, partialDeriv]
  rw [(hev.iteratedFDeriv ℝ _).self_of_nhds]
  simp

lemma sa16j_S_cont {f : Euc d → ℝ} (hf : ContDiff ℝ ∞ f) (m : ℕ) : Continuous (sa16j_S d m f) :=
  continuous_finsetSum _ fun j _ =>
    (hf.continuous_iteratedFDeriv (m := j) (by exact_mod_cast le_top)).norm

/-- A smooth function whose derivatives up to order `m` are in `L^p` has its jet in `WmpSpace`. -/
theorem sa16j_jet_mem (d m : ℕ) (p : ℝ) [Fact (2 ≤ p)] {f : Euc d → ℝ} (hf : ContDiff ℝ ∞ f)
    (hS : MemLp (sa16j_S d m f) (ENNReal.ofReal p) volume) :
    ∃ G : WmpSpace d m p, ((G : WLp d m p) : Euc d → (WIndex d m → ℝ)) =ᵐ[volume] wJet m f := by
  obtain ⟨K, hK0, hK⟩ := sa16j_diff_bound hf m
  have hp2 : (2 : ℝ) ≤ p := Fact.out
  have hpe0 : ENNReal.ofReal p ≠ 0 := by simp; linarith
  have hpetop : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  have hpr : 0 < (ENNReal.ofReal p).toReal := by
    rw [ENNReal.toReal_ofReal (by linarith)]; linarith
  have hjet : MemLp (wJet m f) (ENNReal.ofReal p) volume := by
    refine hS.mono' (sa16j_jet_cont hf m).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
    exact sa16j_jet_norm_le m f x
  set Φ : WLp d m p := hjet.toLp (wJet m f) with hΦ
  have hFcd : ∀ n : ℕ, ContDiff ℝ ∞ (sa16j_cutf d ((n : ℝ) + 1) f) := fun n =>
    (sa16j_chi_contDiff d _).mul hf
  have hFcs : ∀ n : ℕ, HasCompactSupport (sa16j_cutf d ((n : ℝ) + 1) f) := fun n =>
    (sa16j_chi_support d (by positivity)).mul_right
  have hjetF : ∀ n : ℕ, MemLp (wJet m (sa16j_cutf d ((n : ℝ) + 1) f)) (ENNReal.ofReal p) volume :=
    fun n => (sa16j_jet_cont (hFcd n) m).memLp_of_hasCompactSupport (sa16j_jet_support (hFcs n) m)
  set Ψ : ℕ → WLp d m p := fun n => (hjetF n).toLp _ with hΨ
  have hmem : ∀ n, Ψ n ∈ WmpSpace d m p := by
    intro n
    unfold WmpSpace
    refine Submodule.le_topologicalClosure _ (Submodule.subset_span ?_)
    refine ⟨sa16j_cutf d ((n : ℝ) + 1) f, ⟨hFcd n, hFcs n⟩, ?_⟩
    exact (hjetF n).coeFn_toLp
  -- convergence in `L^p`
  have hdiff : ∀ n, ‖Ψ n - Φ‖ = (eLpNorm (wJet m (sa16j_cutf d ((n : ℝ) + 1) f) - wJet m f)
      (ENNReal.ofReal p) volume).toReal := by
    intro n
    rw [hΨ, hΦ, ← MemLp.toLp_sub]
    exact Lp.norm_toLp _ _
  have hSm : Measurable (sa16j_S d m f) := (sa16j_S_cont hf m).measurable
  have hbound_int : ∫⁻ x, ‖K * sa16j_S d m f x‖ₑ ^ (ENNReal.ofReal p).toReal ≠ ⊤ := by
    have := (hS.const_mul K).eLpNorm_lt_top
    have hKS : AEStronglyMeasurable (fun x => K * sa16j_S d m f x) volume :=
      (measurable_const.mul hSm).aestronglyMeasurable
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hpe0 hpetop hKS] at this
    have h2 := ENNReal.rpow_lt_top_iff_of_pos (by positivity : 0 < 1 / (ENNReal.ofReal p).toReal) |>.1
      this
    exact h2.ne
  have hlim0 : Tendsto (fun n : ℕ => eLpNorm ({x : Euc d | ((n : ℝ) + 1) ≤ ‖x‖}.indicator
      (fun x => K * sa16j_S d m f x)) (ENNReal.ofReal p) volume) atTop (𝓝 0) := by
    have hl : Tendsto (fun n : ℕ => ∫⁻ x, ‖{x : Euc d | ((n : ℝ) + 1) ≤ ‖x‖}.indicator
        (fun x => K * sa16j_S d m f x) x‖ₑ ^ (ENNReal.ofReal p).toReal) atTop
        (𝓝 (∫⁻ x : Euc d, (0 : ℝ≥0∞))) := by
      refine tendsto_lintegral_of_dominated_convergence
        (fun x => ‖K * sa16j_S d m f x‖ₑ ^ (ENNReal.ofReal p).toReal) (fun n => ?_) (fun n => ?_)
        hbound_int ?_
      · refine Measurable.pow_const (Measurable.enorm ?_) _
        exact (measurable_const.mul hSm).indicator
          (measurableSet_le measurable_const measurable_norm)
      · refine Eventually.of_forall fun x => ?_
        refine ENNReal.rpow_le_rpow ?_ hpr.le
        by_cases hx : x ∈ {x : Euc d | ((n : ℝ) + 1) ≤ ‖x‖}
        · rw [Set.indicator_of_mem hx]
        · rw [Set.indicator_of_notMem hx]; simp
      · refine Eventually.of_forall fun x => ?_
        obtain ⟨N0, hN0⟩ := exists_nat_gt ‖x‖
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_ge_atTop N0] with n hn
        have hx : x ∉ {x : Euc d | ((n : ℝ) + 1) ≤ ‖x‖} := by
          simp only [Set.mem_setOf_eq, not_le]
          have : (N0 : ℝ) ≤ n := by exact_mod_cast hn
          linarith
        rw [Set.indicator_of_notMem hx]
        simp [ENNReal.zero_rpow_of_pos hpr]
    simp only [lintegral_zero] at hl
    have h2 := (ENNReal.continuous_rpow_const (y := 1 / (ENNReal.ofReal p).toReal)).tendsto 0
      |>.comp hl
    rw [ENNReal.zero_rpow_of_pos (by positivity)] at h2
    refine h2.congr fun n => ?_
    have hind : AEStronglyMeasurable ({x : Euc d | ((n : ℝ) + 1) ≤ ‖x‖}.indicator
        (fun x => K * sa16j_S d m f x)) volume :=
      ((measurable_const.mul hSm).indicator
        (measurableSet_le measurable_const measurable_norm)).aestronglyMeasurable
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hpe0 hpetop hind]
    rfl
  have hlim1 : Tendsto (fun n : ℕ => eLpNorm (wJet m (sa16j_cutf d ((n : ℝ) + 1) f) - wJet m f)
      (ENNReal.ofReal p) volume) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim0
      (fun n => bot_le) (fun n => ?_)
    refine eLpNorm_mono_ae ((hjetF n).sub hjet).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
    refine (hK ((n : ℝ) + 1) (by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith) x).trans ?_
    exact le_trans (by rfl) (le_abs_self _ |>.trans (Real.norm_eq_abs _).symm.le)
  have hlim2 : Tendsto (fun n => ‖Ψ n - Φ‖) atTop (𝓝 0) := by
    simp only [hdiff]
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hlim1
    simpa [Function.comp_def] using this
  have hΨΦ : Tendsto Ψ atTop (𝓝 Φ) := (tendsto_iff_norm_sub_tendsto_zero).2 hlim2
  have hΦmem : Φ ∈ WmpSpace d m p :=
    (Submodule.isClosed_topologicalClosure _).mem_of_tendsto hΨΦ (Eventually.of_forall hmem)
  exact ⟨⟨Φ, hΦmem⟩, hjet.coeFn_toLp⟩

end Jet

end HRS.Whole.AppendixA.Phase2SA16
