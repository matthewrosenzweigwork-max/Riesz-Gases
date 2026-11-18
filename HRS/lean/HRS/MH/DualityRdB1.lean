import HRS.MH.DualityRdB1Aux

/-!
# DualityRd packet B1: `mf_weak_integrable` (the mean-field weak form with integrable generator on `ℝ^d`)

Port of `HRS.Stochastic.Duality` (`measurable_pair_clamp`, `measurable_rho_clamp`, `measurable_rho_joint`,
`measurable_genL_clamp`, `integrableOn_genL`, `weak_interval`, `Duality.lean:530-720`).  The Fejér kernel is replaced by
`ContDiffBump.convolution_tendsto_right_of_continuous` (approximate identity); the torus bound `genL_bound` is replaced by
`db1_mfGen_bound` (`DualityRdB1Aux.lean`).  Helper names carry the prefix `db1_`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.DualityRd

open HRS.Whole HRS.Whole.AppendixA

variable {d : ℕ}

/-! ### Measurability of parametrised integrals with a clamped time -/

/-- If `F t = F 0 + ∫_0^t g` on `[0,T]` and `g` is bounded on `[0,T]` (but not a priori measurable), then `r ↦ F(clamp r)` is
measurable: `F` is Lipschitz on the order-connected set of times where `g` is integrable on `[0,t]`, and constant after. -/
theorem db1_meas_of_weak {g F : ℝ → ℝ} {T K : ℝ} (hT : 0 ≤ T)
    (hK : ∀ r ∈ Set.Icc (0 : ℝ) T, |g r| ≤ K)
    (hF : ∀ t ∈ Set.Icc (0 : ℝ) T, F t = F 0 + ∫ r in Set.Icc (0 : ℝ) t, g r) :
    Measurable (fun r => F (max 0 (min r T))) := by
  classical
  set E : Set ℝ := {t | t ∈ Set.Icc (0 : ℝ) T ∧ IntegrableOn g (Set.Icc 0 t)} with hE
  set Λ' : ℝ → ℝ := fun t => ∫ r in Set.Icc (0 : ℝ) t, g r with hΛ
  have hEconn : E.OrdConnected := by
    refine ⟨fun x hx y hy z hz => ⟨⟨hx.1.1.trans hz.1, hz.2.trans hy.1.2⟩, ?_⟩⟩
    exact hy.2.mono_set (Set.Icc_subset_Icc_right hz.2)
  have hEm : MeasurableSet E := hEconn.measurableSet
  have hLip : ∀ s ∈ E, ∀ t ∈ E, s ≤ t → |Λ' t - Λ' s| ≤ K * (t - s) := by
    intro s hs t ht hst
    have hs0 : 0 ≤ s := hs.1.1
    have hsplit : Set.Icc (0 : ℝ) t = Set.Icc 0 s ∪ Set.Ioc s t :=
      (Set.Icc_union_Ioc_eq_Icc hs0 hst).symm
    have hdisj : Disjoint (Set.Icc (0 : ℝ) s) (Set.Ioc s t) := by
      rw [Set.disjoint_left]
      intro x hx hx'
      exact absurd hx.2 (not_le.2 hx'.1)
    have hi2 : IntegrableOn g (Set.Ioc s t) :=
      ht.2.mono_set (by rw [hsplit]; exact Set.subset_union_right)
    have hsum : Λ' t = Λ' s + ∫ r in Set.Ioc s t, g r := by
      simp only [hΛ]
      rw [hsplit, MeasureTheory.setIntegral_union hdisj measurableSet_Ioc hs.2 hi2]
    have hb : ‖∫ r in Set.Ioc s t, g r‖ ≤ K * volume.real (Set.Ioc s t) := by
      refine norm_setIntegral_le_of_norm_le_const (by simp) fun r hr => ?_
      rw [Real.norm_eq_abs]
      exact hK r ⟨hs0.trans hr.1.le, hr.2.trans ht.1.2⟩
    rw [Real.volume_real_Ioc_of_le hst] at hb
    rw [hsum, add_sub_cancel_left, ← Real.norm_eq_abs]
    exact hb
  have hLip' : ∀ s ∈ E, ∀ t ∈ E, |Λ' t - Λ' s| ≤ K * |t - s| := by
    intro s hs t ht
    rcases le_total s t with h | h
    · rw [abs_of_nonneg (sub_nonneg.2 h)]
      exact hLip s hs t ht h
    · rw [abs_sub_comm (Λ' t) (Λ' s), abs_sub_comm t s, abs_of_nonneg (sub_nonneg.2 h)]
      exact hLip t ht s hs h
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK 0 ⟨le_rfl, hT⟩)
  have hcontE : ContinuousOn Λ' E := by
    refine LipschitzOnWith.continuousOn (K := Real.toNNReal K) ?_
    refine LipschitzOnWith.of_dist_le_mul fun s hs t ht => ?_
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ hK0, abs_sub_comm (Λ' s) (Λ' t), abs_sub_comm s t]
    exact hLip' s hs t ht
  have hpw : Measurable (E.piecewise Λ' (fun _ => 0)) :=
    ContinuousOn.measurable_piecewise hcontE continuousOn_const hEm
  have hclamp : Measurable (fun r : ℝ => max 0 (min r T)) :=
    measurable_const.max (measurable_id.min measurable_const)
  have hclamp_mem : ∀ r, max 0 (min r T) ∈ Set.Icc (0 : ℝ) T := fun r =>
    ⟨le_max_left _ _, max_le hT (min_le_right _ _)⟩
  have hfun : ∀ r, F (max 0 (min r T)) = F 0 + E.piecewise Λ' (fun _ => 0) (max 0 (min r T)) := by
    intro r
    have hw := hF _ (hclamp_mem r)
    by_cases hmem : max 0 (min r T) ∈ E
    · rw [Set.piecewise_eq_of_mem _ _ _ hmem]
      have : Λ' (max 0 (min r T)) = ∫ x in Set.Icc (0 : ℝ) (max 0 (min r T)), g x := rfl
      rw [this]
      linarith [hw]
    · rw [Set.piecewise_eq_of_notMem _ _ _ hmem]
      have hni : ¬ IntegrableOn g (Set.Icc 0 (max 0 (min r T))) := fun hi => hmem ⟨hclamp_mem r, hi⟩
      rw [integral_undef hni] at hw
      linarith [hw]
  have e : (fun r => F (max 0 (min r T))) = fun r => F 0 + E.piecewise Λ' (fun _ => 0) (max 0 (min r T)) :=
    funext hfun
  rw [e]
  exact measurable_const.add (hpw.comp hclamp)

/-! ### Approximate identity and the bump test functions -/

/-- The `n`-th bump: support radius `1/(n+1)`. -/
def db1_bump (d n : ℕ) : ContDiffBump (0 : Euc d) where
  rIn := 1 / (2 * ((n : ℝ) + 1))
  rOut := 1 / ((n : ℝ) + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := by
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    apply one_div_lt_one_div_of_lt hn
    linarith

theorem db1_bump_tendsto : Tendsto (fun n : ℕ => (db1_bump d n).rOut) atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

theorem db1_memCb_of_compact {g : Euc d → ℝ} (hc : ContDiff ℝ 2 g) (hs : HasCompactSupport g) :
    MemCb 2 g := by
  refine ⟨hc, fun j hj => ?_⟩
  have hcont : Continuous (fun x => ‖iteratedFDeriv ℝ j g x‖) :=
    (hc.continuous_iteratedFDeriv (by exact_mod_cast hj)).norm
  have hsupp : HasCompactSupport (fun x => ‖iteratedFDeriv ℝ j g x‖) := (hs.iteratedFDeriv j).norm
  exact hcont.bddAbove_range_of_hasCompactSupport hsupp

/-- The `n`-th approximate-identity test function `y ↦ φ_n(x - y)`: a `C_b²` function. -/
theorem db1_test_memCb (n : ℕ) (x : Euc d) :
    MemCb 2 (fun y => ((db1_bump d n).normed volume) (x - y)) := by
  refine db1_memCb_of_compact ?_ ?_
  · exact (ContDiffBump.contDiff_normed (f := db1_bump d n) (μ := volume)).comp
      (contDiff_const.sub contDiff_id)
  · exact (ContDiffBump.hasCompactSupport_normed (f := db1_bump d n) (μ := volume)).comp_homeomorph
      (Homeomorph.subLeft x)

/-- Approximate identity: for a continuous density `ρ`, `∫ ρ(y) φ_n(x - y) dy → ρ(x)`. -/
theorem db1_approx {ρ : Euc d → ℝ} (hρ : Whole.IsProbDensity ρ) (hρc : Continuous ρ) (x : Euc d) :
    Tendsto (fun n : ℕ => Whole.pair (Whole.withDensityReal ρ) (fun y => ((db1_bump d n).normed volume) (x - y)))
      atTop (𝓝 (ρ x)) := by
  have h := ContDiffBump.convolution_tendsto_right_of_continuous (μ := (volume : Measure (Euc d)))
    (φ := fun n : ℕ => db1_bump d n) db1_bump_tendsto hρc x
  refine Tendsto.congr (fun n => ?_) h
  rw [Q09A.pair_withDensityReal hρ]
  unfold convolution
  simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  rw [← integral_sub_left_eq_self (fun y => ρ y * ((db1_bump d n).normed volume) (x - y)) volume x]
  congr 1
  funext t
  simp only [sub_sub_cancel]
  ring

/-! ### Slices of the mean-field hypotheses -/

theorem db1_abs_le_cbNorm {k : ℕ} {f : Euc d → ℝ} (hf : MemCb k f) (x : Euc d) :
    |f x| ≤ HRS.cbNorm k f := by
  have h0 : |f x| ≤ ⨆ z : Euc d, ‖iteratedFDeriv ℝ 0 f z‖ := by
    have := le_ciSup (hf.2 0 (Nat.zero_le _)) x
    simpa using this
  refine h0.trans ?_
  unfold HRS.cbNorm
  exact Finset.single_le_sum (f := fun j => ⨆ z : Euc d, ‖iteratedFDeriv ℝ j f z‖)
    (fun j _ => Real.iSup_nonneg fun z => norm_nonneg _) (Finset.mem_range.2 (Nat.succ_pos k))

theorem db1_cont {s Λ T ΛV G₀ : ℝ} {D : WholeDyn d} {ρ : ℝ → Euc d → ℝ} (h : MFData s Λ T ΛV G₀ D ρ)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) : Continuous (ρ t) :=
  (h.hreg.1 t ht).1.1.continuous

theorem db1_sup {s Λ T ΛV G₀ : ℝ} {D : WholeDyn d} {ρ : ℝ → Euc d → ℝ} (h : MFData s Λ T ΛV G₀ D ρ)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) (x : Euc d) : ρ t x ≤ Λ := by
  obtain ⟨hmem, -, hcb⟩ := h.hreg.1 t ht
  have h1 := db1_abs_le_cbNorm hmem x
  have h2 : 0 ≤ (weightedSupE 3 ((d : ℝ) + 3) (ρ t)).toReal := ENNReal.toReal_nonneg
  exact (le_abs_self _).trans (h1.trans (by linarith))

theorem db1_Lambda_nonneg {s Λ T ΛV G₀ : ℝ} {D : WholeDyn d} {ρ : ℝ → Euc d → ℝ} (h : MFData s Λ T ΛV G₀ D ρ)
    (hT : 0 ≤ T) : 0 ≤ Λ :=
  ((h.hρ.density 0 ⟨le_rfl, hT⟩).nonneg 0).trans (db1_sup h ⟨le_rfl, hT⟩ 0)

/-- The density slice bounds at a time `r ∈ [0,T]`: density, sup bound, second moment. -/
theorem db1_slice {s Λ T ΛV G₀ : ℝ} {D : WholeDyn d} {ρ : ℝ → Euc d → ℝ} (h : MFData s Λ T ΛV G₀ D ρ)
    {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) T) :
    Whole.IsProbDensity (ρ r) ∧ (∀ x, ρ r x ≤ Λ) ∧ Integrable (fun x => ρ r x * ‖x‖ ^ 2) ∧
      ∫ x, ρ r x * ‖x‖ ^ 2 ≤ Λ * Q09B.q09b_K d := by
  refine ⟨h.hρ.density r hr, db1_sup h hr, ?_, ?_⟩
  · have e : (fun x => ρ r x * ‖x‖ ^ 2) = fun x => ‖x‖ ^ 2 * ρ r x := funext fun x => mul_comm _ _
    rw [e]
    exact h.hρ.second_moment r hr
  · have h2 := Q09B.q09b_mf_second_moment (d := d) h.hreg (fun t ht => h.hρ.density t ht) hr
    unfold secondMomentOf at h2
    rwa [Q09A.pair_withDensityReal (h.hρ.density r hr)] at h2

/-! ### Measurability of the density path and of the generator -/

theorem db1_pair_meas {s Λ T ΛV G₀ : ℝ} {D : WholeDyn d} {ρ : ℝ → Euc d → ℝ} (h : MFData s Λ T ΛV G₀ D ρ)
    (hT : 0 ≤ T) {φ : Euc d → ℝ} (hφ : MemCb 2 φ) :
    Measurable (fun r => Whole.pair (Whole.withDensityReal (ρ (max 0 (min r T)))) φ) := by
  have hd : 1 ≤ d := h.one_le_d
  have hs0 : 0 ≤ D.s := by rw [h.hs]; exact h.hs0
  have hsd : D.s < d := by rw [h.hs]; exact h.hsd
  obtain ⟨K, hK⟩ := db1_mfGen_bound D hd hs0 hsd h.hV hφ Λ (Λ * Q09B.q09b_K d) (db1_Lambda_nonneg h hT)
  refine db1_meas_of_weak (g := fun r => mfGen D φ (ρ r)) (F := fun t => Whole.pair (Whole.withDensityReal (ρ t)) φ)
    (K := K) hT ?_ ?_
  · intro r hr
    obtain ⟨h1, h2, h3, h4⟩ := db1_slice h hr
    exact hK _ h1 h2 h3 h4
  · intro t ht
    have hw := h.hρ.weak φ hφ t ht
    have e : ∫ r in Set.Icc (0 : ℝ) t, mfGen D φ (ρ r) = ∫ r in Set.Icc (0 : ℝ) t,
        (Whole.pair (Whole.withDensityReal (ρ r)) (fun x => D.invβ * Laplacian.laplacian φ x -
            inner ℝ (gradient D.V x) (gradient φ x)) +
          interactionPairingW D φ (Whole.withDensityReal (ρ r)) (Whole.withDensityReal (ρ r))) := rfl
    show Whole.pair (Whole.withDensityReal (ρ t)) φ = Whole.pair (Whole.withDensityReal (ρ 0)) φ +
      ∫ r in Set.Icc (0 : ℝ) t, mfGen D φ (ρ r)
    rw [e]
    linarith [hw]

theorem db1_rho_meas {s Λ T ΛV G₀ : ℝ} {D : WholeDyn d} {ρ : ℝ → Euc d → ℝ} (h : MFData s Λ T ΛV G₀ D ρ)
    (hT : 0 ≤ T) (x : Euc d) : Measurable (fun r => ρ (max 0 (min r T)) x) := by
  have hmem : ∀ r : ℝ, max 0 (min r T) ∈ Set.Icc (0 : ℝ) T := fun r =>
    ⟨le_max_left _ _, max_le hT (min_le_right _ _)⟩
  refine measurable_of_tendsto_metrizable
    (f := fun (n : ℕ) (r : ℝ) => Whole.pair (Whole.withDensityReal (ρ (max 0 (min r T))))
      (fun y => ((db1_bump d n).normed volume) (x - y))) (g := fun r => ρ (max 0 (min r T)) x)
    (fun n => db1_pair_meas h hT (db1_test_memCb n x)) ?_
  refine tendsto_pi_nhds.2 fun r => ?_
  exact db1_approx (h.hρ.density _ (hmem r)) (db1_cont h (hmem r)) x

theorem db1_rho_joint {s Λ T ΛV G₀ : ℝ} {D : WholeDyn d} {ρ : ℝ → Euc d → ℝ} (h : MFData s Λ T ΛV G₀ D ρ)
    (hT : 0 ≤ T) : Measurable (fun p : ℝ × Euc d => ρ (max 0 (min p.1 T)) p.2) := by
  have hmem : ∀ r : ℝ, max 0 (min r T) ∈ Set.Icc (0 : ℝ) T := fun r =>
    ⟨le_max_left _ _, max_le hT (min_le_right _ _)⟩
  have hu := measurable_uncurry_of_continuous_of_measurable
    (u := fun (x : Euc d) (r : ℝ) => ρ (max 0 (min r T)) x)
    (fun r => db1_cont h (hmem r))
    (fun x => db1_rho_meas h hT x)
  exact hu.comp measurable_swap

theorem db1_mfGen_meas {s Λ T ΛV G₀ : ℝ} {D : WholeDyn d} {ρ : ℝ → Euc d → ℝ} (h : MFData s Λ T ΛV G₀ D ρ)
    (hT : 0 ≤ T) {ψ : Euc d → ℝ} (hψ : MemCb 2 ψ) :
    Measurable (fun r => mfGen D ψ (ρ (max 0 (min r T)))) := by
  have hmem : ∀ r : ℝ, max 0 (min r T) ∈ Set.Icc (0 : ℝ) T := fun r =>
    ⟨le_max_left _ _, max_le hT (min_le_right _ _)⟩
  have hψC : ContDiff ℝ 2 ψ := hψ.1
  have hV2 : ContDiff ℝ 2 D.V := h.hV.1.of_le (by norm_num)
  have hJ := db1_rho_joint h hT
  have hgT : Measurable (fun x => D.invβ * Laplacian.laplacian ψ x - inner ℝ (gradient D.V x) (gradient ψ x)) :=
    Measurable.sub (Measurable.const_mul (db1_laplacian_continuous hψC).measurable _)
      (Measurable.inner (db1_gradient_continuous hV2).measurable (db1_gradient_continuous hψC).measurable)
  have hF1 : Measurable (fun r => ∫ x, ρ (max 0 (min r T)) x *
      (D.invβ * Laplacian.laplacian ψ x - inner ℝ (gradient D.V x) (gradient ψ x))) := by
    have hf : Measurable (fun p : ℝ × Euc d => ρ (max 0 (min p.1 T)) p.2 *
        (D.invβ * Laplacian.laplacian ψ p.2 - inner ℝ (gradient D.V p.2) (gradient ψ p.2))) :=
      hJ.mul (hgT.comp measurable_snd)
    exact (hf.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure (Euc d)))).measurable
  have hF2 : Measurable (fun q : ℝ × Euc d => ∫ y, ρ (max 0 (min q.1 T)) y * pairKernelRd D ψ q.2 y) := by
    have hf : Measurable (fun p : (ℝ × Euc d) × Euc d =>
        ρ (max 0 (min p.1.1 T)) p.2 * pairKernelRd D ψ p.1.2 p.2) :=
      (hJ.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).mul
        ((db1_pK_measurable hψC).comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
    exact (hf.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure (Euc d)))).measurable
  have hF3 : Measurable (fun r => ∫ x, ρ (max 0 (min r T)) x *
      ∫ y, ρ (max 0 (min r T)) y * pairKernelRd D ψ x y) := by
    have hf : Measurable (fun p : ℝ × Euc d => ρ (max 0 (min p.1 T)) p.2 *
        ∫ y, ρ (max 0 (min p.1 T)) y * pairKernelRd D ψ p.2 y) := hJ.mul hF2
    exact (hf.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure (Euc d)))).measurable
  have e : (fun r => mfGen D ψ (ρ (max 0 (min r T)))) = fun r =>
      (∫ x, ρ (max 0 (min r T)) x *
        (D.invβ * Laplacian.laplacian ψ x - inner ℝ (gradient D.V x) (gradient ψ x)))
      + (1 / 2 : ℝ) * ∫ x, ρ (max 0 (min r T)) x * ∫ y, ρ (max 0 (min r T)) y * pairKernelRd D ψ x y :=
    funext fun r => db1_mfGen_eq D (h.hρ.density _ (hmem r))
  rw [e]
  exact hF1.add (measurable_const.mul hF3)

theorem mf_weak_integrable_proof {s Λ T ΛV G₀ : ℝ} {D : WholeDyn d} {ρ : ℝ → Euc d → ℝ}
    (h : MFData s Λ T ΛV G₀ D ρ) {ψ : Euc d → ℝ} (hψ : MemCb 2 ψ) :
    IntegrableOn (fun r => mfGen D ψ (ρ r)) (Set.Icc (0 : ℝ) T) ∧
    (∃ K : ℝ, ∀ r ∈ Set.Icc (0 : ℝ) T, |mfGen D ψ (ρ r)| ≤ K) ∧
    ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ T →
      Whole.pair (Whole.withDensityReal (ρ b)) ψ - Whole.pair (Whole.withDensityReal (ρ a)) ψ
        = ∫ r in a..b, mfGen D ψ (ρ r) := by
  by_cases hT : 0 ≤ T
  swap
  · have hempty : Set.Icc (0 : ℝ) T = ∅ := Set.Icc_eq_empty hT
    refine ⟨?_, ⟨0, fun r hr => ?_⟩, fun a b ha hab hb => ?_⟩
    · rw [hempty]
      exact integrableOn_empty
    · rw [hempty] at hr
      exact absurd hr (Set.notMem_empty r)
    · exact absurd (ha.trans (hab.trans hb)) hT
  have hd : 1 ≤ d := h.one_le_d
  have hs0 : 0 ≤ D.s := by rw [h.hs]; exact h.hs0
  have hsd : D.s < d := by rw [h.hs]; exact h.hsd
  obtain ⟨K, hK⟩ := db1_mfGen_bound D hd hs0 hsd h.hV hψ Λ (Λ * Q09B.q09b_K d) (db1_Lambda_nonneg h hT)
  have hbd : ∀ r ∈ Set.Icc (0 : ℝ) T, |mfGen D ψ (ρ r)| ≤ K := by
    intro r hr
    obtain ⟨h1, h2, h3, h4⟩ := db1_slice h hr
    exact hK _ h1 h2 h3 h4
  have hcl : ∀ r ∈ Set.Icc (0 : ℝ) T, max 0 (min r T) = r := fun r hr => by
    rw [min_eq_left hr.2, max_eq_right hr.1]
  have hIcc : IntegrableOn (fun r => mfGen D ψ (ρ (max 0 (min r T)))) (Set.Icc (0 : ℝ) T) := by
    refine Integrable.of_bound (μ := volume.restrict (Set.Icc (0 : ℝ) T)) (C := K) ?_ ?_
    · exact (db1_mfGen_meas h hT hψ).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
      rw [Real.norm_eq_abs, hcl r hr]
      exact hbd r hr
  have hIcc' : IntegrableOn (fun r => mfGen D ψ (ρ r)) (Set.Icc (0 : ℝ) T) :=
    hIcc.congr_fun (fun r hr => by simp only [hcl r hr]) measurableSet_Icc
  refine ⟨hIcc', ⟨K, fun r hr => hbd r hr⟩, fun a b ha hab hb => ?_⟩
  have hbT : b ∈ Set.Icc (0 : ℝ) T := ⟨ha.trans hab, hb⟩
  have haT : a ∈ Set.Icc (0 : ℝ) T := ⟨ha, hab.trans hb⟩
  have hsplit : Set.Icc (0 : ℝ) b = Set.Icc 0 a ∪ Set.Ioc a b := (Set.Icc_union_Ioc_eq_Icc ha hab).symm
  have hdisj : Disjoint (Set.Icc (0 : ℝ) a) (Set.Ioc a b) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    exact absurd hx.2 (not_le.2 hx'.1)
  have hi1 : IntegrableOn (fun r => mfGen D ψ (ρ r)) (Set.Icc 0 a) :=
    hIcc'.mono_set (Set.Icc_subset_Icc_right (hab.trans hb))
  have hi2 : IntegrableOn (fun r => mfGen D ψ (ρ r)) (Set.Ioc a b) :=
    hIcc'.mono_set (fun r hr => ⟨ha.trans hr.1.le, hr.2.trans hb⟩)
  have h1 : Whole.pair (Whole.withDensityReal (ρ b)) ψ - Whole.pair (Whole.withDensityReal (ρ 0)) ψ
      = ∫ r in Set.Icc (0 : ℝ) b, mfGen D ψ (ρ r) := h.hρ.weak ψ hψ b hbT
  have h2 : Whole.pair (Whole.withDensityReal (ρ a)) ψ - Whole.pair (Whole.withDensityReal (ρ 0)) ψ
      = ∫ r in Set.Icc (0 : ℝ) a, mfGen D ψ (ρ r) := h.hρ.weak ψ hψ a haT
  rw [hsplit, MeasureTheory.setIntegral_union hdisj measurableSet_Ioc hi1 hi2] at h1
  rw [intervalIntegral.integral_of_le hab]
  linarith

end HRS.MH.DualityRd
