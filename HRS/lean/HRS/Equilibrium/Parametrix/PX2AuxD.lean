import HRS.Equilibrium.Parametrix.PX2AuxB

/-!
# Packet PX2b auxiliaries: the Hadamard function and the near-diagonal estimate of `(φ x - φ y) γ(x-y)`

* `mixedDeriv_sum`, `mixedDeriv_congr` (local in `z`),
* `hadam ψ (X, z) = ∫₀¹ ψ(X + (t-½) z) dt`: smooth with `‖D^k‖ ≤ 2^k sup‖D^kψ‖`,
* `Φ(X + z/2) - Φ(X - z/2) = ∑ᵢ zᵢ hadam(∂ᵢΦ)(X, z)`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.Parx

universe u

variable {d : ℕ}

local notation "∞'" => ((⊤ : ℕ∞) : WithTop ℕ∞)

theorem natCast_le_infty (m : ℕ) : (m : WithTop ℕ∞) ≤ ∞' := by exact_mod_cast le_top

/-! ### Mixed derivatives of finite sums, and locality in `z` -/

theorem mixedDeriv_sum {ι : Type*} (s : Finset ι) {G : ι → Euc d × Euc d → ℝ}
    (hG : ∀ i, ContDiff ℝ ∞' (G i)) (a c : ℕ) (X z : Euc d) :
    mixedDeriv a c (fun p => ∑ i ∈ s, G i p) X z = ∑ i ∈ s, mixedDeriv a c (G i) X z := by
  unfold mixedDeriv
  have hin : ∀ X' : Euc d, iteratedFDeriv ℝ c (fun z' => ∑ i ∈ s, G i (X', z')) z =
      ∑ i ∈ s, iteratedFDeriv ℝ c (fun z' => G i (X', z')) z := by
    intro X'
    exact iteratedFDeriv_fun_sum_apply fun i _ =>
      ((hG i).comp (contDiff_const.prodMk contDiff_id)).contDiffAt.of_le (by exact_mod_cast le_top)
  have hfun : (fun X' : Euc d => iteratedFDeriv ℝ c (fun z' => ∑ i ∈ s, G i (X', z')) z) =
      fun X' => ∑ i ∈ s, iteratedFDeriv ℝ c (fun z' => G i (X', z')) z := by
    funext X'; exact hin X'
  rw [hfun]
  exact iteratedFDeriv_fun_sum_apply fun i _ =>
    ((contDiff_inner (hG i) c z).contDiffAt).of_le (by exact_mod_cast le_top)

/-- `mixedDeriv` only depends on `G` for `z'` in a neighbourhood of `z`. -/
theorem mixedDeriv_congr {G₁ G₂ : Euc d × Euc d → ℝ} (a c : ℕ) (X z : Euc d) {U : Set (Euc d)}
    (hU : U ∈ 𝓝 z) (h : ∀ X' z', z' ∈ U → G₁ (X', z') = G₂ (X', z')) :
    mixedDeriv a c G₁ X z = mixedDeriv a c G₂ X z := by
  unfold mixedDeriv
  have hfun : (fun X' : Euc d => iteratedFDeriv ℝ c (fun z' => G₁ (X', z')) z) =
      fun X' => iteratedFDeriv ℝ c (fun z' => G₂ (X', z')) z := by
    funext X'
    have hev : (fun z' => G₁ (X', z')) =ᶠ[𝓝 z] (fun z' => G₂ (X', z')) := by
      filter_upwards [hU] with z' hz' using h X' z' hz'
    exact (hev.iteratedFDeriv ℝ c).eq_of_nhds
  rw [hfun]

/-! ### The Hadamard function -/

theorem iteratedFDeriv_slice_inl {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] {G : E₁ × E₂ → ℝ} (hG : ContDiff ℝ ∞' G) (c : ℕ)
    (e₁ : E₁) (e₂ : E₂) :
    iteratedFDeriv ℝ c (fun x => G (x, e₂)) e₁ =
      (iteratedFDeriv ℝ c G (e₁, e₂)).compContinuousLinearMap
        (fun _ => ContinuousLinearMap.inl ℝ E₁ E₂) := by
  have hfun : (fun x : E₁ => G (x, e₂)) =
      (fun p : E₁ × E₂ => G (p + (0, e₂))) ∘ (ContinuousLinearMap.inl ℝ E₁ E₂) := by
    funext x; simp
  have hcd : ContDiff ℝ ∞' (fun p : E₁ × E₂ => G (p + (0, e₂))) :=
    hG.comp (contDiff_id.add contDiff_const)
  rw [hfun, ContinuousLinearMap.iteratedFDeriv_comp_right _ hcd e₁ (by exact_mod_cast le_top),
    iteratedFDeriv_comp_add_right]
  simp

/-- `∫₀¹ ψ(X + (t - ½) z) dt`. -/
def hadam (ψ : Euc d → ℝ) (p : Euc d × Euc d) : ℝ :=
  ∫ t in Set.Ioc (0 : ℝ) 1, ψ (p.1 + (t - 1 / 2) • p.2)

theorem hadam_smooth_bound {ψ : Euc d → ℝ} (hψ : ContDiff ℝ ∞' ψ) (M : ℕ → ℝ)
    (hM : ∀ k y, ‖iteratedFDeriv ℝ k ψ y‖ ≤ M k) :
    ContDiff ℝ ∞' (hadam ψ) ∧ ∀ k p, ‖iteratedFDeriv ℝ k (hadam ψ) p‖ ≤ 2 ^ k * M k := by
  set ν : Measure ℝ := (volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) 1) with hν
  set K : Euc d × Euc d → ℝ → ℝ := fun p t => ψ (p.1 + (t - 1 / 2) • p.2) with hK
  haveI : IsFiniteMeasure ν := by rw [hν]; infer_instance
  have hΨ : ContDiff ℝ ∞' (fun q : (Euc d × Euc d) × ℝ => ψ (q.1.1 + (q.2 - 1 / 2) • q.1.2)) :=
    hψ.comp (((contDiff_fst.comp contDiff_fst)).add
      (((contDiff_snd.sub contDiff_const)).smul (contDiff_snd.comp contDiff_fst)))
  have hLt : ∀ t : ℝ, t ∈ Set.Ioc (0 : ℝ) 1 → ∃ L : Euc d × Euc d →L[ℝ] Euc d,
      ‖L‖ ≤ 2 ∧ (fun p' : Euc d × Euc d => K p' t) = ψ ∘ L := by
    intro t ht
    refine ⟨ContinuousLinearMap.fst ℝ _ _ + (t - 1 / 2) • ContinuousLinearMap.snd ℝ _ _, ?_, ?_⟩
    · calc _ ≤ ‖ContinuousLinearMap.fst ℝ (Euc d) (Euc d)‖ +
            ‖(t - 1 / 2) • ContinuousLinearMap.snd ℝ (Euc d) (Euc d)‖ := norm_add_le _ _
        _ ≤ 1 + |t - 1 / 2| * 1 := by
          rw [norm_smul, Real.norm_eq_abs]
          exact add_le_add (ContinuousLinearMap.norm_fst_le _ _ _)
            (mul_le_mul_of_nonneg_left (ContinuousLinearMap.norm_snd_le _ _ _) (abs_nonneg _))
        _ ≤ 2 := by
          have : |t - 1 / 2| ≤ 1 / 2 := by
            rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
          linarith
    · funext p'; simp [hK]
  have hbnd : ∀ k : ℕ, ∀ᵐ t ∂ν, ∀ p : Euc d × Euc d,
      ‖iteratedFDeriv ℝ k (fun p' => K p' t) p‖ ≤ 2 ^ k * M k := by
    intro k
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht p
    obtain ⟨L, hL, hfun⟩ := hLt t ht
    rw [hfun, ContinuousLinearMap.iteratedFDeriv_comp_right L (hψ) p (by exact_mod_cast le_top)]
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    have h2 : ∏ _j : Fin k, ‖L‖ ≤ 2 ^ k := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      exact pow_le_pow_left₀ (norm_nonneg _) hL k
    calc ‖iteratedFDeriv ℝ k ψ (L p)‖ * ∏ _j : Fin k, ‖L‖ ≤ M k * 2 ^ k :=
          mul_le_mul (hM k _) h2 (Finset.prod_nonneg fun _ _ => norm_nonneg _)
            (le_trans (norm_nonneg _) (hM k 0))
      _ = 2 ^ k * M k := by ring
  have hparam : ∀ m : ℕ, ParamHyp m K ν := by
    intro m
    refine ⟨Filter.Eventually.of_forall fun t => ?_, ?_, ?_⟩
    · have hlin : ContDiff ℝ ∞' (fun p : Euc d × Euc d => p.1 + (t - 1 / 2) • p.2) :=
        contDiff_fst.add ((contDiff_const (c := t - 1 / 2)).smul contDiff_snd)
      exact (hψ.comp hlin).of_le (natCast_le_infty m)
    · intro k hk p
      have hcont : Continuous fun t : ℝ => iteratedFDeriv ℝ k (fun p' => K p' t) p := by
        have : (fun t : ℝ => iteratedFDeriv ℝ k (fun p' => K p' t) p) =
            fun t => (iteratedFDeriv ℝ k (fun q : (Euc d × Euc d) × ℝ =>
              ψ (q.1.1 + (q.2 - 1 / 2) • q.1.2)) (p, t)).compContinuousLinearMap
              (fun _ => ContinuousLinearMap.inl ℝ (Euc d × Euc d) ℝ) := by
          funext t
          exact iteratedFDeriv_slice_inl hΨ k p t
        rw [this]
        exact (ContinuousMultilinearMap.compContinuousLinearMapL
          (fun _ : Fin k => ContinuousLinearMap.inl ℝ (Euc d × Euc d) ℝ)).continuous.comp
          ((hΨ.continuous_iteratedFDeriv (m := k) (by exact_mod_cast le_top)).comp
            (continuous_const.prodMk continuous_id))
      exact hcont.aestronglyMeasurable
    · intro k hk
      exact ⟨fun _ => 2 ^ k * M k, integrable_const _, hbnd k⟩
  have hfun : hadam ψ = fun p => ∫ t, K p t ∂ν := rfl
  refine ⟨?_, fun k p => ?_⟩
  · rw [contDiff_infty]
    intro n
    exact (contDiff_integral_param_aux n K (hparam n)).1
  · obtain ⟨_, hform⟩ := contDiff_integral_param_aux k K (hparam k)
    rw [hfun, hform k le_rfl p]
    refine (norm_integral_le_of_norm_le (integrable_const (2 ^ k * M k))
      ((hbnd k).mono fun t ht => ht p)).trans ?_
    simp [hν]

theorem hadam_identity {Φ : Euc d → ℝ} (hΦ : ContDiff ℝ ∞' Φ) (X z : Euc d) :
    Φ (X + (1 / 2 : ℝ) • z) - Φ (X - (1 / 2 : ℝ) • z) =
      ∑ i, z i * hadam (fun y => fderiv ℝ Φ y (EuclideanSpace.single i (1 : ℝ))) (X, z) := by
  have hdiff : Differentiable ℝ Φ := hΦ.differentiable (by simp)
  have hcontD : Continuous fun y => fderiv ℝ Φ y := (hΦ.fderiv_right (m := 0) (by simp)).continuous
  have hD : ∀ t : ℝ, HasDerivAt (fun t : ℝ => Φ (X + (t - 1 / 2) • z))
      (fderiv ℝ Φ (X + (t - 1 / 2) • z) z) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => X + (t - 1 / 2) • z) z t := by
      have : HasDerivAt (fun t : ℝ => (t - 1 / 2) • z) ((1 : ℝ) • z) t :=
        ((hasDerivAt_id t).sub_const (1 / 2)).smul_const z
      simpa using this.const_add X
    exact (hdiff (X + (t - 1 / 2) • z)).hasFDerivAt.comp_hasDerivAt t h1
  have hcont1 : Continuous fun t : ℝ => fderiv ℝ Φ (X + (t - 1 / 2) • z) z := by
    have : Continuous fun t : ℝ => X + (t - 1 / 2) • z := by fun_prop
    exact (ContinuousLinearMap.apply ℝ ℝ z).continuous.comp (hcontD.comp this)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := 1)
    (fun t _ => hD t) (hcont1.intervalIntegrable _ _)
  have e1 : Φ (X + ((1 : ℝ) - 1 / 2) • z) = Φ (X + (1 / 2 : ℝ) • z) := by
    congr 2; norm_num
  have e0 : Φ (X + ((0 : ℝ) - 1 / 2) • z) = Φ (X - (1 / 2 : ℝ) • z) := by
    congr 1; module
  rw [e1, e0] at hftc
  rw [← hftc, intervalIntegral.integral_of_le zero_le_one]
  have hz : ∀ y : Euc d, fderiv ℝ Φ y z = ∑ i, z i * fderiv ℝ Φ y (EuclideanSpace.single i (1 : ℝ)) := by
    intro y
    have : z = ∑ i, z i • (EuclideanSpace.single i (1 : ℝ) : Euc d) := by
      ext j
      simp [Pi.single_apply, Finset.sum_apply]
    conv_lhs => rw [this]
    simp [map_sum, map_smul]
  simp_rw [hz]
  unfold hadam
  simp only
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_const_mul]
  · intro i _
    have hc : Continuous fun t : ℝ => z i * fderiv ℝ Φ (X + (t - 1 / 2) • z)
        (EuclideanSpace.single i (1 : ℝ)) := by
      have : Continuous fun t : ℝ => X + (t - 1 / 2) • z := by fun_prop
      exact continuous_const.mul ((ContinuousLinearMap.apply ℝ ℝ _).continuous.comp (hcontD.comp this))
    exact hc.integrableOn_Ioc

/-! ### Localisation of the kernel `Γ` and the pure-`z` factors `z_i Γ(z)` -/

theorem norm_lt_half_of_small {z y : Euc d} (hz : ‖z‖ < r0) (hy : dist y z < ‖z‖) (i : Fin d) :
    |y i| ≤ 1 / 2 := by
  have h1 : ‖y‖ ≤ ‖z‖ + dist y z := by
    have := norm_le_norm_add_norm_sub' y z
    rw [dist_eq_norm]; linarith
  have h2 : |y i| ≤ ‖y‖ := by
    have := PiLp.norm_apply_le y i
    rwa [Real.norm_eq_abs] at this
  unfold r0 at hz
  linarith

theorem exists_localisation {Γ : Euc d → ℝ}
    (hΓ : ContDiffOn ℝ ∞' Γ {y : Euc d | Torus.mk y ≠ 0}) {z : Euc d} (hz0 : 0 < ‖z‖) (hz : ‖z‖ < r0) :
    ∃ Γh : Euc d → ℝ, ContDiff ℝ ∞' Γh ∧ ∀ y ∈ Metric.ball z (‖z‖ / 4), Γh y = Γ y := by
  set b : ContDiffBump z := ⟨‖z‖ / 4, ‖z‖ / 2, by positivity, by linarith⟩ with hb
  refine ⟨fun y => b y * Γ y, ?_, fun y hy => ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy : dist y z < ‖z‖ * (3 / 4)
    · have hyU : Torus.mk y ≠ 0 := by
        have hy' : dist y z < ‖z‖ := by nlinarith
        have hy0 : y ≠ 0 := by
          intro h0
          rw [h0, dist_zero_left] at hy
          nlinarith
        refine box_ne_zero hy0 fun i => ?_
        have := norm_lt_half_of_small (z := z) (y := y) hz hy' i
        exact this
      have hΓy : ContDiffAt ℝ ∞' Γ y := hΓ.contDiffAt (isOpen_mk_ne_zero'.mem_nhds hyU)
      exact b.contDiffAt.mul hΓy
    · push Not at hy
      have hzero : (fun y' : Euc d => b y' * Γ y') =ᶠ[𝓝 y] fun _ => 0 := by
        have hopen : IsOpen {y' : Euc d | ‖z‖ / 2 < dist y' z} :=
          isOpen_lt continuous_const (continuous_id.dist continuous_const)
        filter_upwards [hopen.mem_nhds (by show ‖z‖ / 2 < dist y z; nlinarith)] with y' hy'
        have : b y' = 0 := b.zero_of_le_dist (by simp only [hb]; exact hy'.le)
        simp [this]
      exact contDiffAt_const.congr_of_eventuallyEq hzero
  · have : b y = 1 := b.one_of_mem_closedBall (by
      simp only [hb]; exact Metric.ball_subset_closedBall hy)
    simp [this]

theorem norm_iteratedFDeriv_proj_le (i : Fin d) (n : ℕ) (y : Euc d) :
    ‖iteratedFDeriv ℝ n (fun y : Euc d => y i) y‖ ≤
      if n = 0 then ‖y‖ else if n = 1 then 1 else 0 := by
  have hℓ : (fun y : Euc d => y i) = fun y => (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ) y := rfl
  have hnorm : ‖(EuclideanSpace.proj i : Euc d →L[ℝ] ℝ)‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
      simpa [Real.norm_eq_abs] using PiLp.norm_apply_le x i
  rw [hℓ]
  rcases n with _ | _ | n
  · simp only [norm_iteratedFDeriv_zero, if_true]
    have := PiLp.norm_apply_le y i
    simpa using this
  · simp only [Nat.zero_add, one_ne_zero, if_false, if_true]
    have := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ)) (x := y) (n := 0)
    rw [norm_iteratedFDeriv_zero] at this
    rw [zero_add] at this
    rw [← this, ContinuousLinearMap.fderiv]
    exact hnorm
  · have := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ)) (x := y) (n := n + 1)
    have h0 : ‖iteratedFDeriv ℝ (n + 1) (fderiv ℝ (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ)) y‖ = 0 := by
      have : fderiv ℝ (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ) = fun _ => (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ) := by
        funext x; exact ContinuousLinearMap.fderiv _
      rw [this, iteratedFDeriv_const_of_ne (by omega)]
      exact norm_zero (E := ContinuousMultilinearMap ℝ (fun _ : Fin (n + 1) => Euc d) (Euc d →L[ℝ] ℝ))
    simp only [show ¬ (n + 1 + 1 = 0) by omega, show ¬ (n + 1 + 1 = 1) by omega, if_false]
    rw [← this]; exact h0.le

theorem pureZ_bound {σ : ℝ} {m : ℕ} {γ : Torus d → ℝ} (hγ : KerBound (σ + 1) m γ) :
    ∃ K : ℕ → ℝ, (∀ n, 0 ≤ K n) ∧ ∀ (i : Fin d) (z : Euc d), 0 < ‖z‖ → ‖z‖ < r0 →
      ∃ κh : Euc d → ℝ, ContDiff ℝ ∞' κh ∧
        (∀ y ∈ Metric.ball z (‖z‖ / 4), κh y = y i * Torus.lift γ y) ∧
        ∀ n : ℕ, n ≤ m → ‖iteratedFDeriv ℝ n κh z‖ ≤ K n * (‖z‖ ^ (-(σ + n)) + 1) := by
  choose! Cg hCg0 hCg using hγ.bound
  refine ⟨fun n => |Cg n| + n * |Cg (n - 1)|, fun n => by positivity, fun i z hz0 hz => ?_⟩
  obtain ⟨Γh, hΓh, hΓeq⟩ := exists_localisation hγ.smooth hz0 hz
  refine ⟨fun y => y i * Γh y, ?_, fun y hy => by simp [hΓeq y hy], fun n hn => ?_⟩
  · have hproj : ContDiff ℝ ∞' (fun y : Euc d => y i) :=
      (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).contDiff
    exact hproj.mul hΓh
  · set r : ℝ := ‖z‖ with hr
    have hr1 : r ≤ 1 := by unfold r0 at hz; linarith
    have hzb : ∀ j, |z j| ≤ 1 / 2 := fun j => by
      have := PiLp.norm_apply_le z j
      rw [Real.norm_eq_abs] at this
      unfold r0 at hz; linarith
    have hzU : Torus.mk z ≠ 0 := box_ne_zero (norm_pos_iff.mp hz0) hzb
    -- derivatives of `Γh` at `z` agree with those of `Γ`
    have hev : Γh =ᶠ[𝓝 z] Torus.lift γ := by
      filter_upwards [Metric.ball_mem_nhds z (show 0 < r / 4 by positivity)] with y hy
      exact hΓeq y hy
    have hDΓ : ∀ l, iteratedFDeriv ℝ l Γh z = iteratedFDeriv ℝ l (Torus.lift γ) z := fun l =>
      (hev.iteratedFDeriv ℝ l).eq_of_nhds
    have hbd : ∀ l, l ≤ m → ‖iteratedFDeriv ℝ l Γh z‖ ≤ Cg l * (r ^ (-(σ + 1) - (l : ℝ)) + 1) := by
      intro l hl
      rw [hDΓ]
      exact hCg l hl z z hzU rfl hzb
    have hproj : ContDiff ℝ ∞' (fun y : Euc d => y i) :=
      (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).contDiff
    have hmul := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) hproj hΓh z (n := n) (by exact_mod_cast le_top)
    refine hmul.trans ?_
    have hrp : 0 < r := hz0
    have hpow_nonneg : ∀ e : ℝ, 0 ≤ r ^ e := fun e => Real.rpow_nonneg hrp.le e
    -- term bounds
    have hT : ∀ j ∈ Finset.range (n + 1), (n.choose j : ℝ) * ‖iteratedFDeriv ℝ j (fun y : Euc d => y i) z‖ *
        ‖iteratedFDeriv ℝ (n - j) Γh z‖ ≤
        (if j = 0 then r * ‖iteratedFDeriv ℝ n Γh z‖ else 0) +
          (if j = 1 then (n : ℝ) * ‖iteratedFDeriv ℝ (n - 1) Γh z‖ else 0) := by
      intro j hj
      have hc : (0 : ℝ) ≤ (n.choose j : ℝ) := Nat.cast_nonneg _
      have hD := norm_iteratedFDeriv_proj_le i j z
      have hn1 : 0 ≤ ‖iteratedFDeriv ℝ (n - j) Γh z‖ := norm_nonneg _
      by_cases h0 : j = 0
      · subst h0
        simp only [if_true, Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero,
          show (0 : ℕ) ≠ 1 by omega, if_false, add_zero]
        simp only [if_true] at hD
        exact mul_le_mul_of_nonneg_right hD hn1
      · by_cases h1 : j = 1
        · subst h1
          simp only [show (1 : ℕ) ≠ 0 by omega, if_false, if_true, Nat.choose_one_right, zero_add]
          simp only [show (1 : ℕ) ≠ 0 by omega, if_false, if_true] at hD
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hD (Nat.cast_nonneg _) |>.trans_eq
            (by ring)) hn1 |>.trans_eq (by ring)
        · simp only [h0, h1, if_false, add_zero] at hD ⊢
          have : ‖iteratedFDeriv ℝ j (fun y : Euc d => y i) z‖ ≤ 0 := hD
          have h2 : ‖iteratedFDeriv ℝ j (fun y : Euc d => y i) z‖ = 0 := le_antisymm this (norm_nonneg _)
          rw [h2]; simp
    have hsum := Finset.sum_le_sum hT
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq'] at hsum
    have h0mem : 0 ∈ Finset.range (n + 1) := by simp
    rw [if_pos h0mem] at hsum
    refine hsum.trans ?_
    have key1 : r * ‖iteratedFDeriv ℝ n Γh z‖ ≤ |Cg n| * (r ^ (-(σ + (n : ℝ))) + 1) := by
      have h1 := hbd n hn
      have e1 : r * r ^ (-(σ + 1) - (n : ℝ)) = r ^ (-(σ + (n : ℝ))) := by
        calc r * r ^ (-(σ + 1) - (n : ℝ)) = r ^ (1 : ℝ) * r ^ (-(σ + 1) - (n : ℝ)) := by
              rw [Real.rpow_one]
          _ = r ^ (1 + (-(σ + 1) - (n : ℝ))) := (Real.rpow_add hrp _ _).symm
          _ = r ^ (-(σ + (n : ℝ))) := by congr 1; ring
      calc r * ‖iteratedFDeriv ℝ n Γh z‖ ≤ r * (Cg n * (r ^ (-(σ + 1) - (n : ℝ)) + 1)) :=
            mul_le_mul_of_nonneg_left h1 hrp.le
        _ = Cg n * (r ^ (-(σ + (n : ℝ))) + r) := by rw [← e1]; ring
        _ ≤ |Cg n| * (r ^ (-(σ + (n : ℝ))) + 1) := by
            have : Cg n ≤ |Cg n| := le_abs_self _
            have h2 : r ^ (-(σ + (n : ℝ))) + r ≤ r ^ (-(σ + (n : ℝ))) + 1 := by linarith
            have h3 : 0 ≤ r ^ (-(σ + (n : ℝ))) + r := by have := hpow_nonneg (-(σ + (n : ℝ))); positivity
            calc Cg n * (r ^ (-(σ + (n : ℝ))) + r) ≤ |Cg n| * (r ^ (-(σ + (n : ℝ))) + r) :=
                  mul_le_mul_of_nonneg_right this h3
              _ ≤ _ := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
    have key2 : (if 1 ∈ Finset.range (n + 1) then (n : ℝ) * ‖iteratedFDeriv ℝ (n - 1) Γh z‖ else 0) ≤
        (n : ℝ) * |Cg (n - 1)| * (r ^ (-(σ + (n : ℝ))) + 1) := by
      rcases n with _ | n'
      · simp
      · have hmem : 1 ∈ Finset.range (n' + 1 + 1) := by simp
        rw [if_pos hmem]
        have h1 := hbd n' (by omega)
        have e1 : r ^ (-(σ + 1) - (n' : ℝ)) = r ^ (-(σ + ((n' + 1 : ℕ) : ℝ))) := by
          congr 1; push_cast; ring
        rw [Nat.add_sub_cancel]
        have h2 : ‖iteratedFDeriv ℝ n' Γh z‖ ≤ |Cg n'| * (r ^ (-(σ + ((n' + 1 : ℕ) : ℝ))) + 1) := by
          calc _ ≤ Cg n' * (r ^ (-(σ + 1) - (n' : ℝ)) + 1) := h1
            _ ≤ |Cg n'| * (r ^ (-(σ + 1) - (n' : ℝ)) + 1) :=
                mul_le_mul_of_nonneg_right (le_abs_self _) (by have := hpow_nonneg (-(σ + 1) - (n' : ℝ)); positivity)
            _ = _ := by rw [e1]
        calc ((n' + 1 : ℕ) : ℝ) * ‖iteratedFDeriv ℝ n' Γh z‖
            ≤ ((n' + 1 : ℕ) : ℝ) * (|Cg n'| * (r ^ (-(σ + ((n' + 1 : ℕ) : ℝ))) + 1)) :=
              mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg _)
          _ = _ := by ring
    calc r * ‖iteratedFDeriv ℝ n Γh z‖ +
          (if 1 ∈ Finset.range (n + 1) then (n : ℝ) * ‖iteratedFDeriv ℝ (n - 1) Γh z‖ else 0)
        ≤ |Cg n| * (r ^ (-(σ + (n : ℝ))) + 1) + (n : ℝ) * |Cg (n - 1)| * (r ^ (-(σ + (n : ℝ))) + 1) :=
          add_le_add key1 key2
      _ = (|Cg n| + (n : ℝ) * |Cg (n - 1)|) * (r ^ (-(σ + (n : ℝ))) + 1) := by ring

/-! ### The near-diagonal estimate for `(φ x - φ y) γ(x - y)` -/

theorem lift_partialDeriv_isSmooth {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) (i : Fin d) :
    ContDiff ℝ ∞' (Torus.lift (Torus.partialDeriv i φ)) :=
  LocalDivAux.isSmooth_partialDeriv hφ i

theorem norm_lift_partialDeriv_le {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) (i : Fin d) (k : ℕ)
    (y : Euc d) :
    ‖iteratedFDeriv ℝ k (Torus.lift (Torus.partialDeriv i φ)) y‖ ≤
      ‖iteratedFDeriv ℝ (k + 1) (Torus.lift φ) y‖ := by
  have hF : ContDiff ℝ ∞' (Torus.lift φ) := hφ
  have h1 : Torus.IsCk 1 φ := ContDiff.of_le hF (by exact_mod_cast le_top)
  rw [HRS.PDE.lift_partialDeriv i φ h1]
  have hc : ContDiffAt ℝ ∞' (fderiv ℝ (Torus.lift φ)) y := (hF.fderiv_right (m := ∞') (by simp)).contDiffAt
  have h := norm_iteratedFDeriv_clm_apply_const (c := (EuclideanSpace.single i (1 : ℝ) : Euc d)) (n := k) hc
    (by exact_mod_cast le_top)
  rw [norm_iteratedFDeriv_fderiv] at h
  have h1' : ‖(EuclideanSpace.single i (1 : ℝ) : Euc d)‖ = 1 := by simp
  rw [h1', one_mul] at h
  exact h

theorem near_chart_bound {σ : ℝ} {m : ℕ} {γ : Torus d → ℝ} (hγ : KerBound (σ + 1) m γ) :
    ∃ Kb : ℝ, 0 ≤ Kb ∧ ∀ (φ : Torus d → ℝ), Torus.IsSmooth φ → ∀ N : ℝ,
      (∀ k : ℕ, k ≤ m + 1 → ∀ y : Euc d, ‖iteratedFDeriv ℝ k (Torus.lift φ) y‖ ≤ N) →
      ∀ (a c : ℕ), a + c ≤ m → ∀ (X z : Euc d), 0 < ‖z‖ → ‖z‖ < r0 →
        ‖mixedDeriv a c (fun p : Euc d × Euc d =>
          (Torus.lift φ (p.1 + (1 / 2 : ℝ) • p.2) - Torus.lift φ (p.1 - (1 / 2 : ℝ) • p.2)) *
            Torus.lift γ p.2) X z‖ ≤
          (d * 4 ^ m * Kb * N) * (1 + ‖z‖ ^ (-(σ + (c : ℝ)))) := by
  obtain ⟨K, hK0, hK⟩ := pureZ_bound hγ
  set Kb : ℝ := ∑ n ∈ Finset.range (m + 1), K n with hKb
  have hKb0 : 0 ≤ Kb := Finset.sum_nonneg fun n _ => hK0 n
  refine ⟨Kb, hKb0, fun φ hφ N hN a c hac X z hz0 hz => ?_⟩
  have hN0 : 0 ≤ N := (norm_nonneg _).trans (hN 0 (Nat.zero_le _) 0)
  have hm : a + c ≤ m := hac
  set r : ℝ := ‖z‖ with hr
  have hrp : 0 < r := hz0
  have hr1 : r ≤ 1 := by unfold r0 at hz; linarith
  have hΦ : ContDiff ℝ ∞' (Torus.lift φ) := hφ
  -- the derivatives of `ψ i = ∂_i Φ`
  have hψsm : ∀ i, ContDiff ℝ ∞' (Torus.lift (Torus.partialDeriv i φ)) :=
    fun i => lift_partialDeriv_isSmooth hφ i
  choose Mb _ hMb using fun (i : Fin d) (k : ℕ) =>
    bdd_iteratedFDeriv_lift (Torus.partialDeriv i φ) k ((hψsm i).of_le (natCast_le_infty k))
  set M : Fin d → ℕ → ℝ := fun i k => if k ≤ m then N else Mb i k with hM
  have hMbound : ∀ i k y, ‖iteratedFDeriv ℝ k (Torus.lift (Torus.partialDeriv i φ)) y‖ ≤ M i k := by
    intro i k y
    by_cases hk : k ≤ m
    · simp only [hM, hk, if_true]
      exact (norm_lift_partialDeriv_le hφ i k y).trans (hN (k + 1) (by omega) y)
    · simp only [hM, hk, if_false]
      exact hMb i k y
  have hHad := fun i => hadam_smooth_bound (hψsm i) (M i) (hMbound i)
  -- the pure `z` factors
  have hκ := fun i => hK i z hz0 hz
  choose κh hκsm hκeq hκbd using hκ
  -- the chart function agrees with `∑ Ā_i κ_i` near `z`
  set Gi : Fin d → Euc d × Euc d → ℝ := fun i p => hadam (Torus.lift (Torus.partialDeriv i φ)) p * κh i p.2 with hGi
  have hGi_sm : ∀ i, ContDiff ℝ ∞' (Gi i) := fun i => (hHad i).1.mul ((hκsm i).comp contDiff_snd)
  have hcongr : mixedDeriv a c (fun p : Euc d × Euc d =>
      (Torus.lift φ (p.1 + (1 / 2 : ℝ) • p.2) - Torus.lift φ (p.1 - (1 / 2 : ℝ) • p.2)) *
        Torus.lift γ p.2) X z = mixedDeriv a c (fun p => ∑ i, Gi i p) X z := by
    refine mixedDeriv_congr a c X z (U := Metric.ball z (r / 4)) (Metric.ball_mem_nhds z (by positivity)) ?_
    intro X' z' hz'
    have hid := hadam_identity hΦ X' z'
    have hψeq : ∀ i, (fun y => fderiv ℝ (Torus.lift φ) y (EuclideanSpace.single i (1 : ℝ))) =
        Torus.lift (Torus.partialDeriv i φ) := fun i =>
      (HRS.PDE.lift_partialDeriv i φ (ContDiff.of_le hΦ (by exact_mod_cast le_top))).symm
    simp only [hψeq] at hid
    simp only [hGi]
    rw [hid, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hκeq i z' hz']
    ring
  rw [hcongr, mixedDeriv_sum Finset.univ hGi_sm]
  have hnorm_sum := norm_sum_le (Finset.univ : Finset (Fin d))
    (fun i => mixedDeriv a c (Gi i) X z)
  refine hnorm_sum.trans ?_
  have hw : 0 ≤ r ^ (-(σ + (c : ℝ))) := Real.rpow_nonneg hrp.le _
  have hterm : ∀ i, ‖mixedDeriv a c (Gi i) X z‖ ≤ 4 ^ m * Kb * N * (1 + r ^ (-(σ + (c : ℝ)))) := by
    intro i
    have hSP := norm_mixedDeriv_mul_pureZ c (hadam (Torus.lift (Torus.partialDeriv i φ))) (κh i)
      (hHad i).1 (hκsm i) a X z
    set T1 : ℕ → ℝ := fun k => ‖mixedDeriv a k (hadam (Torus.lift (Torus.partialDeriv i φ))) X z‖ with hT1
    set T2 : ℕ → ℝ := fun k => ‖iteratedFDeriv ℝ k (κh i) z‖ with hT2
    have hSP' : ‖mixedDeriv a c (Gi i) X z‖ ≤ ∑ k ∈ Finset.range (c + 1), (c.choose k : ℝ) * T1 k * T2 (c - k) := hSP
    refine hSP'.trans ?_
    have hk_term : ∀ k ∈ Finset.range (c + 1), (c.choose k : ℝ) * T1 k * T2 (c - k) ≤
        (c.choose k : ℝ) * (2 ^ m * N) * (K (c - k) * (r ^ (-(σ + (c : ℝ))) + 1)) := by
      intro k hk
      have hkc : k ≤ c := by have := Finset.mem_range.mp hk; omega
      have h1 : T1 k ≤ 2 ^ m * N := by
        refine (norm_mixedDeriv_le k (hHad i).1 a X z).trans ?_
        refine ((hHad i).2 (a + k) (X, z)).trans ?_
        have hak : a + k ≤ m := by omega
        simp only [hM, hak, if_true]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hak) hN0
      have h2 : T2 (c - k) ≤ K (c - k) * (r ^ (-(σ + (c : ℝ))) + 1) := by
        refine (hκbd i (c - k) (by omega)).trans ?_
        refine mul_le_mul_of_nonneg_left ?_ (hK0 _)
        have : r ^ (-(σ + ((c - k : ℕ) : ℝ))) ≤ r ^ (-(σ + (c : ℝ))) := by
          refine Real.rpow_le_rpow_of_exponent_ge hrp hr1 ?_
          have : ((c - k : ℕ) : ℝ) ≤ c := by exact_mod_cast Nat.sub_le c k
          linarith
        linarith
      have hc : (0 : ℝ) ≤ (c.choose k : ℝ) := Nat.cast_nonneg _
      have hT2n : 0 ≤ T2 (c - k) := norm_nonneg _
      calc (c.choose k : ℝ) * T1 k * T2 (c - k) ≤ (c.choose k : ℝ) * (2 ^ m * N) * T2 (c - k) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hc) hT2n
        _ ≤ _ := mul_le_mul_of_nonneg_left h2 (mul_nonneg hc (by positivity))
    refine (Finset.sum_le_sum hk_term).trans ?_
    have hchoose : ∀ k ∈ Finset.range (c + 1), (c.choose k : ℝ) ≤ 2 ^ m := by
      intro k _
      have : c.choose k ≤ 2 ^ c := Nat.choose_le_two_pow c k
      calc (c.choose k : ℝ) ≤ 2 ^ c := by exact_mod_cast this
        _ ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) (by omega)
    have hsumK : ∑ k ∈ Finset.range (c + 1), K (c - k) ≤ Kb := by
      have hrefl : ∑ k ∈ Finset.range (c + 1), K (c - k) = ∑ k ∈ Finset.range (c + 1), K k := by
        have := Finset.sum_range_reflect (fun j => K j) (c + 1)
        simpa using this
      rw [hrefl]
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_subset_range.mpr (by omega)) (fun j _ _ => hK0 j)
    calc ∑ k ∈ Finset.range (c + 1), (c.choose k : ℝ) * (2 ^ m * N) * (K (c - k) * (r ^ (-(σ + (c : ℝ))) + 1))
        ≤ ∑ k ∈ Finset.range (c + 1), (2 ^ m : ℝ) * (2 ^ m * N) * (K (c - k) * (r ^ (-(σ + (c : ℝ))) + 1)) := by
          refine Finset.sum_le_sum fun k hk => ?_
          refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (hK0 _) (by linarith))
          exact mul_le_mul_of_nonneg_right (hchoose k hk) (by positivity)
      _ = (2 ^ m : ℝ) * (2 ^ m * N) * ((∑ k ∈ Finset.range (c + 1), K (c - k)) * (r ^ (-(σ + (c : ℝ))) + 1)) := by
          rw [← Finset.mul_sum, ← Finset.sum_mul]
      _ ≤ (2 ^ m : ℝ) * (2 ^ m * N) * (Kb * (r ^ (-(σ + (c : ℝ))) + 1)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul_of_nonneg_right hsumK (by linarith)
      _ = 4 ^ m * Kb * N * (1 + r ^ (-(σ + (c : ℝ)))) := by
          rw [show (4 : ℝ) ^ m = 2 ^ m * 2 ^ m by rw [← mul_pow]; norm_num]
          ring
  calc ∑ i, ‖mixedDeriv a c (Gi i) X z‖ ≤ ∑ _i : Fin d, 4 ^ m * Kb * N * (1 + r ^ (-(σ + (c : ℝ)))) :=
        Finset.sum_le_sum fun i _ => hterm i
    _ = (d * 4 ^ m * Kb * N) * (1 + r ^ (-(σ + (c : ℝ)))) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-! ### The class of `(φ x - φ y) γ(x - y)` -/

theorem toChart_diffProd (φ γ : Torus d → ℝ) :
    toChart (fun x y => (φ x - φ y) * γ (x - y)) = fun p : Euc d × Euc d =>
      (Torus.lift φ (p.1 + (1 / 2 : ℝ) • p.2) - Torus.lift φ (p.1 - (1 / 2 : ℝ) • p.2)) *
        Torus.lift γ p.2 := by
  funext p
  simp only [toChart, Torus.lift, Function.comp_apply]
  congr 2
  rw [← mk_sub_eq]
  congr 1
  module

theorem lift2_diffProd (φ γ : Torus d → ℝ) :
    lift2 (fun x y => (φ x - φ y) * γ (x - y)) = fun p : Euc d × Euc d =>
      (Torus.lift φ p.1 - Torus.lift φ p.2) * Torus.lift γ (p.1 - p.2) := by
  funext p
  simp only [lift2, Torus.lift, Function.comp_apply, mk_sub_eq]

theorem norm_iteratedFDeriv_mul_le_of_open {U : Set (Euc d × Euc d)} (hU : IsOpen U)
    {f g : Euc d × Euc d → ℝ} {n : ℕ} (hf : ContDiffOn ℝ (n : WithTop ℕ∞) f U)
    (hg : ContDiffOn ℝ (n : WithTop ℕ∞) g U) {x : Euc d × Euc d} (hx : x ∈ U) :
    ‖iteratedFDeriv ℝ n (fun y => f y * g y) x‖ ≤
      ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i f x‖ *
        ‖iteratedFDeriv ℝ (n - i) g x‖ := by
  have h := norm_iteratedFDerivWithin_mul_le hf hg hU.uniqueDiffOn hx le_rfl
  have e0 := iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := fun y => f y * g y) n hU hx
  rw [e0] at h
  refine h.trans (le_of_eq ?_)
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ n := by have := Finset.mem_range.mp hi; omega
  rw [iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := f) i hU hx,
    iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := g) (n - i) hU hx]

theorem norm_iteratedFDeriv_sub_prod_le' {Φ₁ Φ₂ : Euc d → ℝ} (hΦ₁ : ContDiff ℝ ∞' Φ₁)
    (hΦ₂ : ContDiff ℝ ∞' Φ₂) (i : ℕ) (p : Euc d × Euc d) :
    ‖iteratedFDeriv ℝ i (fun q : Euc d × Euc d => Φ₁ q.1 - Φ₂ q.2) p‖ ≤
      ‖iteratedFDeriv ℝ i Φ₁ p.1‖ + ‖iteratedFDeriv ℝ i Φ₂ p.2‖ := by
  have h1 : ContDiff ℝ ∞' (fun q : Euc d × Euc d => Φ₁ q.1) := hΦ₁.comp contDiff_fst
  have h2 : ContDiff ℝ ∞' (fun q : Euc d × Euc d => Φ₂ q.2) := hΦ₂.comp contDiff_snd
  rw [show (fun q : Euc d × Euc d => Φ₁ q.1 - Φ₂ q.2) =
      (fun q : Euc d × Euc d => Φ₁ q.1) - (fun q : Euc d × Euc d => Φ₂ q.2) from rfl,
    iteratedFDeriv_sub_apply (h1.contDiffAt.of_le (natCast_le_infty i)) (h2.contDiffAt.of_le (natCast_le_infty i))]
  have e1 : iteratedFDeriv ℝ i (fun q : Euc d × Euc d => Φ₁ q.1) p =
      (iteratedFDeriv ℝ i Φ₁ p.1).compContinuousLinearMap (fun _ => ContinuousLinearMap.fst ℝ (Euc d) (Euc d)) :=
    ContinuousLinearMap.iteratedFDeriv_comp_right (ContinuousLinearMap.fst ℝ (Euc d) (Euc d)) hΦ₁ p
      (natCast_le_infty i)
  have e2 : iteratedFDeriv ℝ i (fun q : Euc d × Euc d => Φ₂ q.2) p =
      (iteratedFDeriv ℝ i Φ₂ p.2).compContinuousLinearMap (fun _ => ContinuousLinearMap.snd ℝ (Euc d) (Euc d)) :=
    ContinuousLinearMap.iteratedFDeriv_comp_right (ContinuousLinearMap.snd ℝ (Euc d) (Euc d)) hΦ₂ p
      (natCast_le_infty i)
  have hfst : ∏ _j : Fin i, ‖ContinuousLinearMap.fst ℝ (Euc d) (Euc d)‖ ≤ 1 := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact pow_le_one₀ (norm_nonneg _) (ContinuousLinearMap.norm_fst_le _ _ _)
  have hsnd : ∏ _j : Fin i, ‖ContinuousLinearMap.snd ℝ (Euc d) (Euc d)‖ ≤ 1 := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact pow_le_one₀ (norm_nonneg _) (ContinuousLinearMap.norm_snd_le _ _ _)
  refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
  · rw [e1]
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    calc _ ≤ ‖iteratedFDeriv ℝ i Φ₁ p.1‖ * 1 := by gcongr
      _ = _ := mul_one _
  · rw [e2]
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    calc _ ≤ ‖iteratedFDeriv ℝ i Φ₂ p.2‖ * 1 := by gcongr
      _ = _ := mul_one _

theorem norm_iteratedFDeriv_sub_prod_le {Φ : Euc d → ℝ} (hΦ : ContDiff ℝ ∞' Φ) (i : ℕ)
    (p : Euc d × Euc d) :
    ‖iteratedFDeriv ℝ i (fun q : Euc d × Euc d => Φ q.1 - Φ q.2) p‖ ≤
      ‖iteratedFDeriv ℝ i Φ p.1‖ + ‖iteratedFDeriv ℝ i Φ p.2‖ :=
  norm_iteratedFDeriv_sub_prod_le' hΦ hΦ i p

theorem conormal_diffProd {σ : ℝ} {m : ℕ} {γ : Torus d → ℝ} (hγ : KerBound (σ + 1) m γ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (φ : Torus d → ℝ), Torus.IsSmooth φ → ∀ N : ℝ,
      (∀ k : ℕ, k ≤ m + 1 → ∀ y : Euc d, ‖iteratedFDeriv ℝ k (Torus.lift φ) y‖ ≤ N) →
      Conormal σ 0 m (C * N) (fun x y => (φ x - φ y) * γ (x - y)) := by
  obtain ⟨Kb, hKb0, hnear⟩ := near_chart_bound hγ
  obtain ⟨Cγ, hCγ0, hCγ⟩ := conormal_of_kerBound hγ
  refine ⟨d * 4 ^ m * Kb + 2 ^ (m + 1) * Cγ, by positivity, fun φ hφ N hN => ?_⟩
  have hN0 : 0 ≤ N := (norm_nonneg _).trans (hN 0 (Nat.zero_le _) 0)
  have hΦ : ContDiff ℝ ∞' (Torus.lift φ) := hφ
  have hsmooth2 : ContDiffOn ℝ (m : WithTop ℕ∞) (fun p : Euc d × Euc d => Torus.lift γ (p.1 - p.2))
      (offDiag d) := by
    have := hCγ.smooth
    rwa [lift2_transl] at this
  have hf : ∀ n : ℕ, ContDiff ℝ (n : WithTop ℕ∞) (fun p : Euc d × Euc d => Torus.lift φ p.1 - Torus.lift φ p.2) :=
    fun n => ((hΦ.comp contDiff_fst).sub (hΦ.comp contDiff_snd)).of_le (natCast_le_infty n)
  refine ⟨?_, ?_, ?_⟩
  · rw [lift2_diffProd]
    exact (hf m).contDiffOn.mul hsmooth2
  · intro a c hac X z hz hzr
    rw [toChart_diffProd]
    have h1 := hnear φ hφ N hN a c hac X z (norm_pos_iff.mpr hz) hzr
    have hw : 0 ≤ 1 + ‖z‖ ^ (-(σ + (c : ℝ))) := by
      have := Real.rpow_nonneg (norm_nonneg z) (-(σ + (c : ℝ))); linarith
    simp only [pow_zero, mul_one]
    refine h1.trans ?_
    refine mul_le_mul_of_nonneg_right ?_ hw
    have : (d : ℝ) * 4 ^ m * Kb ≤ d * 4 ^ m * Kb + 2 ^ (m + 1) * Cγ := by
      have : 0 ≤ (2 : ℝ) ^ (m + 1) * Cγ := by positivity
      linarith
    nlinarith
  · intro k hk p hp hdist
    rw [lift2_diffProd]
    have hopen := px2_isOpen_offDiag (d := d)
    have hg : ContDiffOn ℝ (k : WithTop ℕ∞) (fun p : Euc d × Euc d => Torus.lift γ (p.1 - p.2)) (offDiag d) :=
      hsmooth2.of_le (by exact_mod_cast hk)
    have hmul := norm_iteratedFDeriv_mul_le_of_open hopen (n := k) (hf k).contDiffOn hg hp
    refine hmul.trans ?_
    have hterm : ∀ i ∈ Finset.range (k + 1),
        (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun p : Euc d × Euc d =>
          Torus.lift φ p.1 - Torus.lift φ p.2) p‖ *
          ‖iteratedFDeriv ℝ (k - i) (fun p : Euc d × Euc d => Torus.lift γ (p.1 - p.2)) p‖ ≤
        (k.choose i : ℝ) * (2 * N * Cγ) := by
      intro i hi
      have hi' : i ≤ k := by have := Finset.mem_range.mp hi; omega
      have e1 : ‖iteratedFDeriv ℝ i (fun p : Euc d × Euc d => Torus.lift φ p.1 - Torus.lift φ p.2) p‖ ≤ 2 * N :=
        (norm_iteratedFDeriv_sub_prod_le hΦ i p).trans (by
          have := hN i (by omega) p.1; have := hN i (by omega) p.2; linarith)
      have e2 : ‖iteratedFDeriv ℝ (k - i) (fun p : Euc d × Euc d => Torus.lift γ (p.1 - p.2)) p‖ ≤ Cγ := by
        have := hCγ.far (k - i) (by omega) p hp hdist
        rwa [lift2_transl] at this
      have hc : (0 : ℝ) ≤ (k.choose i : ℝ) := Nat.cast_nonneg _
      calc (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun p : Euc d × Euc d =>
            Torus.lift φ p.1 - Torus.lift φ p.2) p‖ *
          ‖iteratedFDeriv ℝ (k - i) (fun p : Euc d × Euc d => Torus.lift γ (p.1 - p.2)) p‖
          ≤ (k.choose i : ℝ) * (2 * N) * Cγ :=
            mul_le_mul (mul_le_mul_of_nonneg_left e1 hc) e2 (norm_nonneg _) (by positivity)
        _ = _ := by ring
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.sum_mul]
    have hsumc : ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) = 2 ^ k := by
      exact_mod_cast Nat.sum_range_choose k
    rw [hsumc]
    have : (2 : ℝ) ^ k ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) hk
    calc (2 : ℝ) ^ k * (2 * N * Cγ) ≤ 2 ^ m * (2 * N * Cγ) :=
          mul_le_mul_of_nonneg_right this (by positivity)
      _ = 2 ^ (m + 1) * Cγ * N := by ring
      _ ≤ (d * 4 ^ m * Kb + 2 ^ (m + 1) * Cγ) * N := by
          refine mul_le_mul_of_nonneg_right ?_ hN0
          have : 0 ≤ (d : ℝ) * 4 ^ m * Kb := by positivity
          linarith

end HRS.Parx

end
