import HRS.Prob.MRepAux2

/-!
# MREP, part 3: density of elementary integrands

Bounded progressive finite-coordinate integrands are approximable (`approx_of_bounded`); `Approx` is closed under
`L²_loc` limits.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MRep

section Density

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ mΩ}

/-- A progressive process is jointly measurable. -/
theorem isProgressive_measurable_uncurry {β : Type*} [TopologicalSpace β] [TopologicalSpace.PseudoMetrizableSpace β]
    [MeasurableSpace β] [BorelSpace β] {f : ℝ → Ω → β} (hf : IsProgressive ℱ f) :
    Measurable fun p : ℝ × Ω => f p.1 p.2 := by
  have hN : ∀ N : ℕ, Measurable fun x : ℝ × Ω => f (min x.1 N) x.2 := by
    intro N
    have hq : Measurable[Prod.instMeasurableSpace, Subtype.instMeasurableSpace.prod (ℱ N)]
        fun x : ℝ × Ω => ((⟨min x.1 N, Set.mem_Iic.2 (min_le_right _ _)⟩ : Set.Iic (N : ℝ)), x.2) :=
      Measurable.prodMk (Measurable.subtype_mk (measurable_fst.min measurable_const))
        (measurable_snd.mono le_rfl (ℱ.le N))
    exact (hf N).comp hq
  refine measurable_of_tendsto_metrizable hN ?_
  rw [tendsto_pi_nhds]
  intro x
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop ⌈x.1⌉₊] with N hN'
  have : x.1 ≤ N := (Nat.le_ceil _).trans (by exact_mod_cast hN')
  simp [min_eq_left this]

variable {κ : Type*} [Fintype κ]

/-- Clipping of a simple integrand. -/
def clipS (C : ℝ) (hC : 0 ≤ C) (Ψ : SimpleIntegrand ℱ κ) : SimpleIntegrand ℱ κ where
  n := Ψ.n
  t := Ψ.t
  mono := Ψ.mono
  nonneg := Ψ.nonneg
  ξ := fun i ω => HRS.clipv C (Ψ.ξ i ω)
  meas := fun i => (HRS.measurable_clipv C).comp (Ψ.meas i)
  bdd := ⟨C, fun i ω k => HRS.abs_clip_le hC⟩

lemma Ioc_disjoint (Ψ : SimpleIntegrand ℱ κ) {i j : Fin Ψ.n} (hij : i ≠ j) {r : ℝ}
    (hi : r ∈ Set.Ioc (Ψ.t i.castSucc) (Ψ.t i.succ))
    (hj : r ∈ Set.Ioc (Ψ.t j.castSucc) (Ψ.t j.succ)) : False := by
  rcases lt_or_gt_of_ne hij with h | h
  · have h1 : Ψ.t i.succ ≤ Ψ.t j.castSucc := Ψ.mono (Fin.succ_le_castSucc_iff.2 h)
    exact absurd (lt_of_le_of_lt hi.2 (lt_of_le_of_lt h1 hj.1)) (lt_irrefl _)
  · have h1 : Ψ.t j.succ ≤ Ψ.t i.castSucc := Ψ.mono (Fin.succ_le_castSucc_iff.2 h)
    exact absurd (lt_of_le_of_lt hj.2 (lt_of_le_of_lt h1 hi.1)) (lt_irrefl _)

lemma toFun_clipS (C : ℝ) (hC : 0 ≤ C) (Ψ : SimpleIntegrand ℱ κ) (r : ℝ) (ω : Ω) (k : κ) :
    (clipS C hC Ψ).toFun r ω k = max (-C) (min C (Ψ.toFun r ω k)) := by
  classical
  rw [SimpleIntegrand.toFun_apply, SimpleIntegrand.toFun_apply]
  change (∑ i : Fin Ψ.n, (Set.Ioc (Ψ.t i.castSucc) (Ψ.t i.succ)).indicator
      (fun _ => HRS.clipv C (Ψ.ξ i ω) k) r) = _
  by_cases h : ∃ i : Fin Ψ.n, r ∈ Set.Ioc (Ψ.t i.castSucc) (Ψ.t i.succ)
  · obtain ⟨i₀, hi₀⟩ := h
    have hsingle : ∀ (x : Fin Ψ.n → ℝ), ∑ i : Fin Ψ.n,
        (Set.Ioc (Ψ.t i.castSucc) (Ψ.t i.succ)).indicator (fun _ => x i) r = x i₀ := by
      intro x
      rw [Finset.sum_eq_single i₀]
      · simp [hi₀]
      · intro j _ hj
        have : r ∉ Set.Ioc (Ψ.t j.castSucc) (Ψ.t j.succ) := fun hjm =>
          Ioc_disjoint Ψ hj hjm hi₀
        simp [this]
      · simp
    rw [hsingle (fun i => HRS.clipv C (Ψ.ξ i ω) k), hsingle (fun i => Ψ.ξ i ω k)]
    rfl
  · push Not at h
    have z : ∀ (x : Fin Ψ.n → ℝ), ∑ i : Fin Ψ.n,
        (Set.Ioc (Ψ.t i.castSucc) (Ψ.t i.succ)).indicator (fun _ => x i) r = 0 := by
      intro x
      refine Finset.sum_eq_zero fun i _ => ?_
      simp [h i]
    rw [z, z]
    simp [hC]

section VNorm

variable {A : Type*} {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K]
  [MeasurableSpace K] [BorelSpace K] [SecondCountableTopology K]
  {N : ℝ → Ω → A → ℝ} {v : ℝ → Ω → A → K}

lemma IsNoiseK.eLpNorm_v_lt_top (hN : IsNoiseK P ℱ N v) (α : A) (t : ℝ) :
    eLpNorm (fun p : ℝ × Ω => v p.1 p.2 α) 2 (tsm P t) < ∞ := by
  have hm : Measurable fun p : ℝ × Ω => v p.1 p.2 α := hN.vmeas α
  set C : Ω → ℝ := fun ω => ∫ r in Set.Icc 0 t, inner ℝ (v r ω α) (v r ω α) with hC
  have hCint : Integrable C P := by
    have h1 := (hN.noise.sq t α).integrable_mul (hN.noise.sq t α)
    have h2 := (hN.noise.cov α α).integrable t
    refine (h1.sub h2).congr (ae_of_all _ fun ω => ?_)
    simp only [Pi.sub_apply, Pi.mul_apply, hC]
    ring
  have hq : qn P t (fun r ω => v r ω α) = ENNReal.ofReal (∫ ω, C ω ∂P) := by
    rw [ofReal_integral_eq_lintegral_ofReal hCint
      (ae_of_all _ fun ω => integral_nonneg fun r => real_inner_self_nonneg)]
    unfold qn
    refine lintegral_congr_ae ?_
    filter_upwards [hN.noise.Qint] with ω hω
    have hint := hω α α t
    rw [hC]
    simp only []
    rw [ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun r => real_inner_self_nonneg)]
    refine lintegral_congr fun r => ?_
    rw [real_inner_self_eq_norm_sq, enorm_sq_eq_ofReal_norm]
  have h := qn_eq (P := P) (G := fun r ω => v r ω α) hm t
  rw [hq] at h
  by_contra hcon
  rw [not_lt, top_le_iff] at hcon
  rw [hcon] at h
  simp at h

end VNorm

section BoundedApprox

variable {A : Type*} {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K]
  [MeasurableSpace K] [BorelSpace K] [SecondCountableTopology K]
  {N : ℝ → Ω → A → ℝ} {v : ℝ → Ω → A → K}

lemma abs_clip_sub_le_abs_sub {C x y : ℝ} (hy : |y| ≤ C) :
    |max (-C) (min C x) - y| ≤ |x - y| := by
  rw [abs_le] at hy
  rcases le_total x (-C) with h | h
  · have h1 : min C x = x := min_eq_right (by linarith)
    rw [h1, max_eq_left h]
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith
  rcases le_total x C with h' | h'
  · rw [min_eq_right h', max_eq_right h]
  · rw [min_eq_left h', max_eq_right (by linarith)]
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; linarith

lemma sqIntegralOn_lt_top_of_bdd {F : Type*} [Fintype F] (Θ : ℝ → Ω → F → ℝ) {C : ℝ}
    (hC : ∀ r ω k, |Θ r ω k| ≤ C) (n : ℝ) : sqIntegralOn P Θ n < ∞ := by
  unfold sqIntegralOn
  have h1 : ∀ r ω, ∑ k, ‖Θ r ω k‖ₑ ^ 2 ≤ ∑ _k : F, (ENNReal.ofReal C) ^ 2 := by
    intro r ω
    refine Finset.sum_le_sum fun k _ => pow_le_pow_left' ?_ 2
    rw [← ofReal_norm_eq_enorm]
    exact ENNReal.ofReal_le_ofReal (by simpa using hC r ω k)
  calc ∫⁻ ω, (∫⁻ r in Set.Icc 0 n, ∑ k, ‖Θ r ω k‖ₑ ^ 2) ∂P
      ≤ ∫⁻ _ω, (∫⁻ _r in Set.Icc 0 n, ∑ _k : F, (ENNReal.ofReal C) ^ 2) ∂P :=
        lintegral_mono fun ω => lintegral_mono fun r => h1 r ω
    _ < ∞ := by
        rw [lintegral_const, lintegral_const, Measure.restrict_apply_univ, measure_univ, mul_one,
          Real.volume_Icc]
        refine ENNReal.mul_lt_top ?_ ENNReal.ofReal_lt_top
        exact ENNReal.sum_lt_top.2 fun _ _ => ENNReal.pow_lt_top ENNReal.ofReal_lt_top

theorem approx_of_bounded (hℱ : IsCompleteFiltration P ℱ) (hN : IsNoiseK P ℱ N v)
    (F : Finset A) (Θ : ℝ → Ω → F → ℝ) (hΘ : IsProgressive ℱ Θ) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ r ω k, |Θ r ω k| ≤ C) :
    Approx P ℱ v (fun r ω => ∑ k : F, Θ r ω k • v r ω k.1) := by
  intro n ε hε
  set G : ℝ → Ω → K := fun r ω => ∑ k : F, Θ r ω k • v r ω k.1 with hG
  have hΘm : Measurable fun p : ℝ × Ω => Θ p.1 p.2 := isProgressive_measurable_uncurry hΘ
  have hΘk : ∀ k : F, Measurable fun p : ℝ × Ω => Θ p.1 p.2 k := fun k =>
    (measurable_pi_apply k).comp hΘm
  have hGm : Measurable fun p : ℝ × Ω => G p.1 p.2 :=
    Finset.measurable_sum _ fun k _ => (hΘk k).smul (hN.vmeas k.1)
  -- simple approximants, clipped
  have hfin : sqIntegralOn P Θ n < ∞ := sqIntegralOn_lt_top_of_bdd Θ hC n
  obtain ⟨Ψ, hΨ⟩ := exists_simple_approx P ℱ Θ hΘ (n : ℝ) hfin
  obtain ⟨Ψ', hΨ'def⟩ : ∃ Ψ' : ℕ → SimpleIntegrand ℱ F, ∀ j s ω k, (Ψ' j).toFun s ω k =
      max (-C) (min C ((Ψ j).toFun s ω k)) :=
    ⟨fun j => clipS C hC0 (Ψ j), fun j => toFun_clipS C hC0 (Ψ j)⟩
  have hΨ' : Tendsto (fun j => sqIntegralOn P (fun s ω => (Ψ' j).toFun s ω - Θ s ω) n) atTop
      (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hΨ (fun j => bot_le)
      (fun j => HRS.sqIntegralOn_mono_of_enorm_le (fun s ω k => ?_) _)
    show ‖(Ψ' j).toFun s ω k - Θ s ω k‖ₑ ≤ ‖(Ψ j).toFun s ω k - Θ s ω k‖ₑ
    rw [hΨ'def, ← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm]
    exact ENNReal.ofReal_le_ofReal (by
      simpa using abs_clip_sub_le_abs_sub (x := (Ψ j).toFun s ω k) (hC s ω k))
  -- the differences
  set f : ℕ → ℝ × Ω → F → ℝ := fun j p k => (Ψ' j).toFun p.1 p.2 k - Θ p.1 p.2 k with hf
  have hfm : ∀ j k, Measurable fun p : ℝ × Ω => f j p k := fun j k =>
    (((measurable_pi_apply k).comp (Ψ' j).measurable_toFun_joint)).sub (hΘk k)
  set rr : ℕ → ℝ × Ω → ℝ := fun j p => ∑ k, (f j p k) ^ 2 with hrr
  have hrrm : ∀ j, Measurable (rr j) := fun j =>
    Finset.measurable_sum _ fun k _ => (hfm j k).pow_const 2
  have hrr_int : ∀ j, eLpNorm (rr j - 0) 1 (tsm P n) =
      sqIntegralOn P (fun s ω => (Ψ' j).toFun s ω - Θ s ω) n := by
    intro j
    rw [sub_zero, eLpNorm_one_eq_lintegral_enorm (hrrm j).aestronglyMeasurable]
    unfold sqIntegralOn tsm
    have : ∀ p : ℝ × Ω, ‖rr j p‖ₑ = ∑ k, ‖(Ψ' j).toFun p.1 p.2 k - Θ p.1 p.2 k‖ₑ ^ 2 := by
      intro p
      rw [hrr, Real.enorm_of_nonneg (Finset.sum_nonneg fun k _ => sq_nonneg _),
        ENNReal.ofReal_sum_of_nonneg (fun k _ => sq_nonneg _)]
      exact Finset.sum_congr rfl fun k _ => (HRS.SimpleIntegrand.enorm_sq_eq' _).symm
    simp_rw [this]
    rw [lintegral_prod_symm' _ (Finset.measurable_sum _ fun k _ => by
      have := (hfm j k).enorm.pow_const 2
      exact this)]
    rfl
  have hmeasure : TendstoInMeasure (tsm P n) rr atTop 0 := by
    refine tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero ?_
    exact hΨ'.congr (fun j => (hrr_int j).symm)
  obtain ⟨ns, hns, hae⟩ := hmeasure.exists_seq_tendsto_ae
  -- pointwise convergence of each coordinate
  have hcoord : ∀ᵐ p ∂(tsm P n), ∀ k, Tendsto (fun l => f (ns l) p k) atTop (𝓝 0) := by
    filter_upwards [hae] with p hp k
    have h2 : Tendsto (fun l => (f (ns l) p k) ^ 2) atTop (𝓝 0) :=
      squeeze_zero (fun l => sq_nonneg _)
        (fun l => Finset.single_le_sum (f := fun k => (f (ns l) p k) ^ 2)
          (fun k _ => sq_nonneg _) (Finset.mem_univ k)) hp
    have h3 : Tendsto (fun l => |f (ns l) p k|) atTop (𝓝 0) := by
      have := (Real.continuous_sqrt.tendsto 0).comp h2
      simp only [Real.sqrt_zero] at this
      refine this.congr (fun l => ?_)
      simp [Real.sqrt_sq_eq_abs]
    exact (tendsto_zero_iff_abs_tendsto_zero _).2 h3
  -- domination
  have hdiff : ∀ j p, hat v F (Ψ' j) p.1 p.2 - G p.1 p.2 =
      ∑ k : F, f j p k • v p.1 p.2 k.1 := by
    intro j p
    simp only [hat, hG, hf, sub_smul, Finset.sum_sub_distrib]
  set Wf : ℝ × Ω → ℝ := fun p => ∑ k : F, ‖v p.1 p.2 k.1‖ with hWf
  have hWm : Measurable Wf := Finset.measurable_sum _ fun k _ => (hN.vmeas k.1).norm
  have hWL2 : eLpNorm Wf 2 (tsm P n) < ∞ := by
    have e : Wf = ∑ k : F, fun p : ℝ × Ω => ‖v p.1 p.2 k.1‖ := by
      funext p; simp [hWf, Finset.sum_apply]
    rw [e]
    refine lt_of_le_of_lt (eLpNorm_sum_le (by norm_num)) ?_
    refine ENNReal.sum_lt_top.2 fun k _ => ?_
    have hk : AEStronglyMeasurable (fun p : ℝ × Ω => v p.1 p.2 k.1) (tsm P n) :=
      (hN.vmeas k.1).aestronglyMeasurable
    rw [eLpNorm_norm _ hk]
    exact hN.eLpNorm_v_lt_top k.1 n
  set D : ℝ × Ω → ℝ≥0∞ := fun p => ‖(2 * C) * Wf p‖ₑ ^ 2 with hD
  have hDfin : ∫⁻ p, D p ∂(tsm P n) ≠ ∞ := by
    have hm : AEStronglyMeasurable (fun p => (2 * C) * Wf p) (tsm P n) :=
      (measurable_const.mul hWm).aestronglyMeasurable
    rw [hD]
    simp only []
    rw [HRS.lintegral_enorm_sq_eq_eLpNorm_sq hm]
    refine (ENNReal.pow_lt_top ?_).ne
    have : (fun p => (2 * C) * Wf p) = (2 * C) • Wf := by funext p; simp
    rw [this, eLpNorm_const_smul]
    exact ENNReal.mul_lt_top enorm_lt_top hWL2
  -- pointwise bound of the differences
  have hbdd : ∀ j (p : ℝ × Ω) k, |f j p k| ≤ 2 * C := by
    intro j p k
    have h1 : |(Ψ' j).toFun p.1 p.2 k| ≤ C := by
      rw [hΨ'def]; exact HRS.abs_clip_le hC0
    calc |f j p k| = |(Ψ' j).toFun p.1 p.2 k - Θ p.1 p.2 k| := rfl
      _ ≤ |(Ψ' j).toFun p.1 p.2 k| + |Θ p.1 p.2 k| := abs_sub _ _
      _ ≤ 2 * C := by linarith [hC p.1 p.2 k]
  have hnorm_le : ∀ j (p : ℝ × Ω), ‖hat v F (Ψ' j) p.1 p.2 - G p.1 p.2‖ ≤
      ∑ k : F, |f j p k| * ‖v p.1 p.2 k.1‖ := by
    intro j p
    rw [hdiff]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [norm_smul, Real.norm_eq_abs]
  have hdom : ∀ j, (fun p => ‖hat v F (Ψ' j) p.1 p.2 - G p.1 p.2‖ₑ ^ 2) ≤ᵐ[tsm P n] D := by
    intro j
    refine Eventually.of_forall fun p => ?_
    simp only [hD]
    rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _),
      ← ENNReal.ofReal_pow (norm_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : ‖hat v F (Ψ' j) p.1 p.2 - G p.1 p.2‖ ≤ (2 * C) * Wf p := by
      refine (hnorm_le j p).trans ?_
      rw [hWf, Finset.mul_sum]
      exact Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right (hbdd j p k) (norm_nonneg _)
    have h2 : (2 * C) * Wf p ≤ ‖(2 * C) * Wf p‖ := by
      rw [Real.norm_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) (h1.trans h2) 2
  have hlim : ∀ᵐ p ∂(tsm P n), Tendsto (fun l => ‖hat v F (Ψ' (ns l)) p.1 p.2 - G p.1 p.2‖ₑ ^ 2)
      atTop (𝓝 0) := by
    filter_upwards [hcoord] with p hp
    have h1 : Tendsto (fun l => ∑ k : F, |f (ns l) p k| * ‖v p.1 p.2 k.1‖) atTop (𝓝 0) := by
      have : Tendsto (fun l => ∑ k : F, |f (ns l) p k| * ‖v p.1 p.2 k.1‖) atTop
          (𝓝 (∑ k : F, 0 * ‖v p.1 p.2 k.1‖)) :=
        tendsto_finset_sum _ fun k _ =>
          ((tendsto_zero_iff_abs_tendsto_zero _).1 (hp k)).mul_const _
      simpa using this
    have h2 : Tendsto (fun l => ‖hat v F (Ψ' (ns l)) p.1 p.2 - G p.1 p.2‖) atTop (𝓝 0) :=
      squeeze_zero (fun l => norm_nonneg _) (fun l => hnorm_le (ns l) p) h1
    have h3 : Tendsto (fun l => ENNReal.ofReal (‖hat v F (Ψ' (ns l)) p.1 p.2 - G p.1 p.2‖ ^ 2))
        atTop (𝓝 0) := by
      have := (ENNReal.tendsto_ofReal (h2.pow 2))
      simpa using this
    refine h3.congr (fun l => ?_)
    rw [← ofReal_norm_eq_enorm, ENNReal.ofReal_pow (norm_nonneg _)]
  have hdct := tendsto_lintegral_of_dominated_convergence (μ := tsm P n) D
    (fun l => ((measurable_hat hN F (Ψ' (ns l))).sub hGm).enorm.pow_const 2)
    (fun l => hdom (ns l)) hDfin hlim
  simp only [lintegral_zero] at hdct
  have hel : Tendsto (fun l => eLpNorm (fun p : ℝ × Ω =>
      hat v F (Ψ' (ns l)) p.1 p.2 - G p.1 p.2) 2 (tsm P n)) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_sq (hdct.congr (fun l => ?_))
    exact HRS.lintegral_enorm_sq_eq_eLpNorm_sq
      (((measurable_hat hN F (Ψ' (ns l))).sub hGm).aestronglyMeasurable)
  obtain ⟨l, hl⟩ := ((tendsto_order.1 hel).2 ε hε).exists
  exact ⟨F, Ψ' (ns l), hl⟩

theorem Approx.of_limit {G : ℝ → Ω → K} {Gs : ℕ → ℝ → Ω → K}
    (hs : ∀ m, Approx P ℱ v (Gs m))
    (hlim : ∀ n : ℕ, Tendsto (fun m => eLpNorm (fun p : ℝ × Ω => Gs m p.1 p.2 - G p.1 p.2) 2
      (tsm P n)) atTop (𝓝 0)) : Approx P ℱ v G := by
  intro n ε hε
  have hε2 : 0 < ε / 2 := ENNReal.half_pos hε.ne'
  obtain ⟨m, hm⟩ := ((tendsto_order.1 (hlim n)).2 (ε / 2) hε2).exists
  obtain ⟨F, Ψ, hFΨ⟩ := hs m n (ε / 2) hε2
  refine ⟨F, Ψ, ?_⟩
  have e : (fun p : ℝ × Ω => hat v F Ψ p.1 p.2 - G p.1 p.2) =
      (fun p : ℝ × Ω => hat v F Ψ p.1 p.2 - Gs m p.1 p.2) +
      (fun p : ℝ × Ω => Gs m p.1 p.2 - G p.1 p.2) := by
    funext p; simp
  rw [e]
  calc eLpNorm _ 2 (tsm P n) ≤ _ := eLpNorm_add_le (by norm_num)
    _ < ε / 2 + ε / 2 := ENNReal.add_lt_add hFΨ hm
    _ = ε := ENNReal.add_halves ε

end BoundedApprox

end Density

end HRS.MRep
