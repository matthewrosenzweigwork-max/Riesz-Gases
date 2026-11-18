import HRS.MS.ZeroTempAux1

/-!
# SA11, packet A2: integration by parts for jets and uniqueness of weak jets

* `sa11_ibp_jet`: for `τ : Fin j → Fin d` and `ψ ∈ C_c^∞` there is `ψ' ∈ C_c^∞` with
  `∫ ∂^τ φ · ψ = ∫ φ · ψ'` for every `φ ∈ C_c^∞`.
* `sa11_zeroth_inj`: an element of `W^{m,p}` whose zeroth component vanishes a.e. is `0`
  (the weak jet is unique), hence `sa11_eq_of_zeroth`.
-/

noncomputable section

open MeasureTheory
open HRS HRS.Whole HRS.Whole.AppendixA
open scoped ENNReal ContDiff

namespace HRS.MS.ZeroTemp

variable {d : ℕ}

/-- a `C_c^∞` function, as a predicate on functions -/
theorem sa11_isCc_partialDeriv {j : ℕ} (τ : Fin j → Fin d) {φ : Euc d → ℝ} (hφ : IsCcInfty φ) :
    IsCcInfty (partialDeriv τ φ) := by
  refine ⟨?_, ?_⟩
  · show ContDiff ℝ ∞ fun x => iteratedFDeriv ℝ j φ x (fun l => EuclideanSpace.single (τ l) 1)
    exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => Euc d) ℝ
      (fun l => EuclideanSpace.single (τ l) 1)).contDiff.comp
      (hφ.1.iteratedFDeriv_right (by simp) : ContDiff ℝ ∞ (iteratedFDeriv ℝ j φ))
  · refine HasCompactSupport.intro hφ.2 fun x hx => ?_
    have : iteratedFDeriv ℝ j φ x = 0 := by
      by_contra h
      exact hx (support_iteratedFDeriv_subset (𝕜 := ℝ) j h)
    show iteratedFDeriv ℝ j φ x _ = 0
    rw [this]; rfl

theorem sa11_partialDeriv_zero (τ : Fin 0 → Fin d) (φ : Euc d → ℝ) : partialDeriv τ φ = φ := by
  funext x
  unfold partialDeriv
  rw [iteratedFDeriv_zero_apply]

/-- `∂_{τ_0}` of `∂^{tail τ} φ` is `∂^τ φ`. -/
theorem sa11_partialDeriv_succ {j : ℕ} (τ : Fin (j + 1) → Fin d) {φ : Euc d → ℝ} (hφ : ContDiff ℝ ∞ φ) (x : Euc d) :
    partialDeriv τ φ x =
      fderiv ℝ (partialDeriv (Fin.tail τ) φ) x (EuclideanSpace.single (τ 0) 1) := by
  have hdiff : DifferentiableAt ℝ (iteratedFDeriv ℝ j φ) x :=
    (((hφ.iteratedFDeriv_right (by simp) : ContDiff ℝ ∞ (iteratedFDeriv ℝ j φ))).differentiable (by simp)) x
  unfold partialDeriv
  rw [iteratedFDeriv_succ_apply_left]
  have hL := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => Euc d) ℝ
      (fun l => EuclideanSpace.single (Fin.tail τ l) 1)).hasFDerivAt.comp x hdiff.hasFDerivAt
  have e : (fun y => iteratedFDeriv ℝ j φ y (fun l => EuclideanSpace.single (Fin.tail τ l) 1)) =
      (ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => Euc d) ℝ
        (fun l => EuclideanSpace.single (Fin.tail τ l) 1)) ∘ iteratedFDeriv ℝ j φ := rfl
  rw [e, hL.fderiv]
  rfl

theorem sa11_integrable_cc {f : Euc d → ℝ} (hf : IsCcInfty f) : Integrable f :=
  hf.1.continuous.integrable_of_hasCompactSupport hf.2

/-- One integration by parts. -/
theorem sa11_ibp_one {f ψ : Euc d → ℝ} (hf : IsCcInfty f) (hψ : IsCcInfty ψ) (u : Euc d) :
    ∫ x, fderiv ℝ f x u * ψ x = -∫ x, f x * fderiv ℝ ψ x u := by
  have hfd : Differentiable ℝ f := hf.1.differentiable (by simp)
  have hψd : Differentiable ℝ ψ := hψ.1.differentiable (by simp)
  have hdf : ∀ g : Euc d → ℝ, IsCcInfty g → IsCcInfty (fun x => fderiv ℝ g x u) := by
    intro g hg
    refine ⟨?_, ?_⟩
    · have h1 : ContDiff ℝ ∞ (fderiv ℝ g) := hg.1.fderiv_right (by simp)
      exact (ContinuousLinearMap.apply ℝ ℝ u).contDiff.comp h1
    · exact hg.2.fderiv_apply (𝕜 := ℝ) u
  have hI1 := sa11_integrable_cc (hdf f hf)
  have h1 : Integrable (fun x => fderiv ℝ f x u * ψ x) := by
    have : IsCcInfty (fun x => fderiv ℝ f x u * ψ x) := by
      refine ⟨(hdf f hf).1.mul hψ.1, ?_⟩
      exact hψ.2.mul_left
    exact sa11_integrable_cc this
  have h2 : Integrable (fun x => f x * fderiv ℝ ψ x u) := by
    have : IsCcInfty (fun x => f x * fderiv ℝ ψ x u) := ⟨hf.1.mul (hdf ψ hψ).1, (hdf ψ hψ).2.mul_left⟩
    exact sa11_integrable_cc this
  have h3 : Integrable (fun x => f x * ψ x) :=
    sa11_integrable_cc ⟨hf.1.mul hψ.1, hψ.2.mul_left⟩
  have := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume) (v := u) h1 h2 h3
    (fun x _ => hfd x) (fun x _ => hψd x)
  linarith

/-- Integration by parts for iterated partial derivatives: the transposed test function depends only on `(τ, ψ)`. -/
theorem sa11_ibp_jet : ∀ (j : ℕ) (τ : Fin j → Fin d) (ψ : Euc d → ℝ), IsCcInfty ψ →
    ∃ ψ' : Euc d → ℝ, IsCcInfty ψ' ∧ ∀ φ : Euc d → ℝ, IsCcInfty φ →
      ∫ x, partialDeriv τ φ x * ψ x = ∫ x, φ x * ψ' x := by
  intro j
  induction j with
  | zero =>
    intro τ ψ hψ
    refine ⟨ψ, hψ, fun φ hφ => ?_⟩
    rw [sa11_partialDeriv_zero]
  | succ j ih =>
    intro τ ψ hψ
    have hψ1 : IsCcInfty (fun x => fderiv ℝ ψ x (EuclideanSpace.single (τ 0) 1)) := by
      refine ⟨?_, hψ.2.fderiv_apply (𝕜 := ℝ) _⟩
      have h1 : ContDiff ℝ ∞ (fderiv ℝ ψ) := hψ.1.fderiv_right (by simp)
      exact (ContinuousLinearMap.apply ℝ ℝ _).contDiff.comp h1
    obtain ⟨ψ', hψ', hψ'eq⟩ := ih (Fin.tail τ) _ hψ1
    refine ⟨fun x => -ψ' x, ⟨hψ'.1.neg, hψ'.2.neg⟩, fun φ hφ => ?_⟩
    have hg : IsCcInfty (partialDeriv (Fin.tail τ) φ) := sa11_isCc_partialDeriv _ hφ
    have e1 : ∫ x, partialDeriv τ φ x * ψ x =
        ∫ x, fderiv ℝ (partialDeriv (Fin.tail τ) φ) x (EuclideanSpace.single (τ 0) 1) * ψ x :=
      integral_congr_ae (Filter.Eventually.of_forall fun x => by
        simp only [sa11_partialDeriv_succ τ hφ.1 x])
    rw [e1, sa11_ibp_one hg hψ, hψ'eq φ hφ, ← integral_neg]
    congr 1
    funext x
    ring


/-! ### Continuity of the pairing of a component with a compactly supported test -/

section Pairing

variable {m : ℕ} {p : ℝ} [Fact (2 ≤ p)]

theorem sa11_pair_bound (τ : WIndex d m) {ψ : Euc d → ℝ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ G : WLp d m p,
      |∫ x, ((G : WLp d m p) : Euc d → (WIndex d m → ℝ)) x τ * ψ x| ≤ C * ‖G‖ := by
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := Fact.out
  set K : Set (Euc d) := tsupport ψ with hK
  have hKc : IsCompact K := hψc
  haveI : Fact (volume K < ⊤) := ⟨hKc.measure_lt_top⟩
  haveI : IsFiniteMeasure (volume.restrict K) := ⟨by simpa using hKc.measure_lt_top⟩
  obtain ⟨B, hB⟩ := hψ.bounded_above_of_compact_support hψc
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  set c : ℝ := (volume K).toReal ^ (1 - 1 / p) with hc
  have hc0 : 0 ≤ c := Real.rpow_nonneg ENNReal.toReal_nonneg _
  refine ⟨B * c, mul_nonneg hB0 hc0, fun G => ?_⟩
  set g : Euc d → ℝ := fun x => ((G : WLp d m p) : Euc d → (WIndex d m → ℝ)) x τ with hg
  have hgm : AEStronglyMeasurable g volume :=
    ((continuous_apply τ).comp_aestronglyMeasurable (Lp.stronglyMeasurable (G : WLp d m p)).aestronglyMeasurable)
  have hgle : ∀ x, ‖g x‖ ≤ ‖((G : WLp d m p) : Euc d → (WIndex d m → ℝ)) x‖ := fun x =>
    norm_le_pi_norm (((G : WLp d m p) : Euc d → (WIndex d m → ℝ)) x) τ
  have hgp : eLpNorm g (ENNReal.ofReal p) volume ≤ eLpNorm ((G : WLp d m p) : Euc d → (WIndex d m → ℝ))
      (ENNReal.ofReal p) volume :=
    eLpNorm_mono_ae hgm (Filter.Eventually.of_forall hgle)
  have hGnorm : ‖G‖ = (eLpNorm ((G : WLp d m p) : Euc d → (WIndex d m → ℝ)) (ENNReal.ofReal p) volume).toReal :=
    Lp.norm_def G
  have hGfin : eLpNorm ((G : WLp d m p) : Euc d → (WIndex d m → ℝ)) (ENNReal.ofReal p) volume < ⊤ :=
    Lp.eLpNorm_lt_top G
  have hgfin : eLpNorm g (ENNReal.ofReal p) volume < ⊤ := lt_of_le_of_lt hgp hGfin
  -- integrability of g on K
  have hgK : MemLp g (ENNReal.ofReal p) (volume.restrict K) :=
    lt_of_le_of_lt (eLpNorm_restrict_le _ _ _ _) hgfin
  have hgint : Integrable g (volume.restrict K) := hgK.integrable hp1
  -- step a
  have ha : |∫ x, g x * ψ x| ≤ B * ∫ x in K, |g x| := by
    have h1 : |∫ x, g x * ψ x| ≤ ∫ x, |g x * ψ x| := by
      have := norm_integral_le_integral_norm (μ := volume) (fun x => g x * ψ x)
      simpa [Real.norm_eq_abs] using this
    refine h1.trans ?_
    have h2 : ∫ x, |g x * ψ x| = ∫ x in K, |g x * ψ x| := by
      symm
      refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_
      rw [image_eq_zero_of_notMem_tsupport hx]
      simp
    rw [h2, ← integral_const_mul]
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => abs_nonneg _)
      (hgint.abs.const_mul B) (Filter.Eventually.of_forall fun x => ?_)
    show |g x * ψ x| ≤ B * |g x|
    rw [abs_mul]
    have := hB x
    rw [Real.norm_eq_abs] at this
    nlinarith [abs_nonneg (g x)]
  -- step b
  have hb : ∫ x in K, |g x| ≤ c * ‖G‖ := by
    have e1 : ∫ x in K, |g x| = (eLpNorm g 1 (volume.restrict K)).toReal := by
      rw [eLpNorm_one_eq_lintegral_enorm hgint.aestronglyMeasurable]
      have := integral_norm_eq_lintegral_enorm (μ := volume.restrict K) hgint.aestronglyMeasurable
      simpa [Real.norm_eq_abs] using this
    have h3 := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := volume.restrict K) (f := g)
      (p := 1) (q := ENNReal.ofReal p) hp1 hgm.restrict
    have h4 : eLpNorm g (ENNReal.ofReal p) (volume.restrict K) ≤ eLpNorm g (ENNReal.ofReal p) volume :=
      eLpNorm_restrict_le _ _ _ _
    have hp0 : (0 : ℝ) ≤ p := by linarith [(Fact.out : 2 ≤ p)]
    have h5 : (1 / (1 : ℝ≥0∞).toReal - 1 / (ENNReal.ofReal p).toReal) = 1 - 1 / p := by
      rw [ENNReal.toReal_ofReal hp0]; simp
    rw [h5] at h3
    have h6 : (volume.restrict K) Set.univ = volume K := by simp
    rw [h6] at h3
    rw [e1]
    have hfin1 : eLpNorm g 1 (volume.restrict K) ≠ ⊤ := by
      refine ne_top_of_le_ne_top ?_ h3
      refine ENNReal.mul_ne_top (lt_of_le_of_lt h4 hgfin).ne ?_
      exact ENNReal.rpow_ne_top_of_nonneg (by
        have : (0 : ℝ) ≤ 1 - 1 / p := by
          have : 1 / p ≤ 1 := by
            rw [div_le_one (by linarith [(Fact.out : 2 ≤ p)])]; linarith [(Fact.out : 2 ≤ p)]
          linarith
        exact this) (hKc.measure_lt_top).ne
    have h7 := ENNReal.toReal_mono (ENNReal.mul_ne_top (lt_of_le_of_lt h4 hgfin).ne
      (ENNReal.rpow_ne_top_of_nonneg (by
        have : 1 / p ≤ 1 := by
          rw [div_le_one (by linarith [(Fact.out : 2 ≤ p)])]; linarith [(Fact.out : 2 ≤ p)]
        linarith) (hKc.measure_lt_top).ne)) h3
    refine h7.trans ?_
    rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, hc, mul_comm]
    refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg ENNReal.toReal_nonneg _)
    rw [hGnorm]
    exact ENNReal.toReal_mono hGfin.ne (h4.trans hgp)
  calc |∫ x, ((G : WLp d m p) : Euc d → (WIndex d m → ℝ)) x τ * ψ x| = |∫ x, g x * ψ x| := rfl
    _ ≤ B * ∫ x in K, |g x| := ha
    _ ≤ B * (c * ‖G‖) := mul_le_mul_of_nonneg_left hb hB0
    _ = B * c * ‖G‖ := by ring


theorem sa11_comp_memLp (τ : WIndex d m) (G : WLp d m p) :
    MemLp (fun x => ((G : WLp d m p) : Euc d → (WIndex d m → ℝ)) x τ) (ENNReal.ofReal p) volume := by
  have hgm : AEStronglyMeasurable (fun x => ((G : WLp d m p) : Euc d → (WIndex d m → ℝ)) x τ) volume :=
    ((continuous_apply τ).comp_aestronglyMeasurable (Lp.stronglyMeasurable (G : WLp d m p)).aestronglyMeasurable)
  have hgle : ∀ x, ‖((G : WLp d m p) : Euc d → (WIndex d m → ℝ)) x τ‖ ≤
      ‖((G : WLp d m p) : Euc d → (WIndex d m → ℝ)) x‖ := fun x =>
    norm_le_pi_norm (((G : WLp d m p) : Euc d → (WIndex d m → ℝ)) x) τ
  exact lt_of_le_of_lt (eLpNorm_mono_ae hgm (Filter.Eventually.of_forall hgle)) (Lp.eLpNorm_lt_top G)

theorem sa11_pair_integrable (τ : WIndex d m) {ψ : Euc d → ℝ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ)
    (G : WLp d m p) :
    Integrable (fun x => ((G : WLp d m p) : Euc d → (WIndex d m → ℝ)) x τ * ψ x) := by
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := Fact.out
  exact ((sa11_comp_memLp τ G).locallyIntegrable hp1).integrable_smul_right_of_hasCompactSupport hψ hψc

/-- The pairing of the `τ`-component with a `C_c` test as a continuous linear functional on `WLp`. -/
def sa11_pairL (τ : WIndex d m) {ψ : Euc d → ℝ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) :
    WLp d m p →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun G => ∫ x, ((G : WLp d m p) : Euc d → (WIndex d m → ℝ)) x τ * ψ x
      map_add' := fun G H => by
        have e : (fun x => (((G + H : WLp d m p) : WLp d m p) : Euc d → (WIndex d m → ℝ)) x τ * ψ x) =ᵐ[volume]
            fun x => ((G : WLp d m p) : Euc d → (WIndex d m → ℝ)) x τ * ψ x +
              ((H : WLp d m p) : Euc d → (WIndex d m → ℝ)) x τ * ψ x := by
          filter_upwards [Lp.coeFn_add G H] with x hx
          rw [hx]; simp [add_mul]
        rw [integral_congr_ae e, integral_add (sa11_pair_integrable τ hψ hψc G) (sa11_pair_integrable τ hψ hψc H)]
      map_smul' := fun c G => by
        have e : (fun x => (((c • G : WLp d m p) : WLp d m p) : Euc d → (WIndex d m → ℝ)) x τ * ψ x) =ᵐ[volume]
            fun x => c * (((G : WLp d m p) : Euc d → (WIndex d m → ℝ)) x τ * ψ x) := by
          filter_upwards [Lp.coeFn_smul c G] with x hx
          rw [hx]; simp [mul_assoc]
        rw [integral_congr_ae e, integral_const_mul]
        rfl }
    (Classical.choose (sa11_pair_bound (m := m) (p := p) τ hψ hψc))
    (Classical.choose_spec (sa11_pair_bound (m := m) (p := p) τ hψ hψc)).2

theorem sa11_pairL_apply (τ : WIndex d m) {ψ : Euc d → ℝ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ)
    (G : WLp d m p) :
    sa11_pairL τ hψ hψc G = ∫ x, ((G : WLp d m p) : Euc d → (WIndex d m → ℝ)) x τ * ψ x := rfl

/-- Weak jets are unique: an element of `W^{m,p}` with vanishing zeroth component is zero. -/
theorem sa11_zeroth_inj {F : WmpSpace d m p}
    (h : ∀ᵐ x ∂(volume : Measure (Euc d)),
      ((F : WLp d m p) : Euc d → (WIndex d m → ℝ)) x (wZero d m) = 0) : F = 0 := by
  have hF := sa11_denseRange_J (d := d) (m := m) (p := p) F
  rw [mem_closure_iff_seq_limit] at hF
  obtain ⟨x, hxr, hxt⟩ := hF
  choose φ hφ using hxr
  -- each component is orthogonal to every test function
  have hcomp : ∀ τ : WIndex d m, ∀ ψ : Euc d → ℝ, IsCcInfty ψ →
      ∫ y, ((F : WLp d m p) : Euc d → (WIndex d m → ℝ)) y τ * ψ y = 0 := by
    intro τ ψ hψ
    obtain ⟨j, i⟩ := τ
    obtain ⟨ψ', hψ', hψ'eq⟩ := sa11_ibp_jet (j : ℕ) i ψ hψ
    have hL1 := sa11_pairL (m := m) (p := p) ⟨j, i⟩ hψ.1.continuous hψ.2
    have hL2 := sa11_pairL (m := m) (p := p) (wZero d m) hψ'.1.continuous hψ'.2
    -- value at the approximants
    have hval : ∀ n, sa11_pairL (m := m) (p := p) ⟨j, i⟩ hψ.1.continuous hψ.2 ((x n : WmpSpace d m p) : WLp d m p) =
        sa11_pairL (m := m) (p := p) (wZero d m) hψ'.1.continuous hψ'.2 ((x n : WmpSpace d m p) : WLp d m p) := by
      intro n
      rw [sa11_pairL_apply, sa11_pairL_apply]
      have hn : (x n : WmpSpace d m p) = sa11_J (φ n) := (hφ n).symm
      rw [hn]
      have e1 : ∫ y, (((sa11_J (m := m) (p := p) (φ n) : WmpSpace d m p) : WLp d m p) : Euc d → (WIndex d m → ℝ)) y ⟨j, i⟩ * ψ y
          = ∫ y, partialDeriv i (φ n).1 y * ψ y := by
        refine integral_congr_ae ?_
        filter_upwards [sa11_J_coe (m := m) (p := p) (φ n)] with y hy
        rw [hy]; rfl
      have e2 : ∫ y, (((sa11_J (m := m) (p := p) (φ n) : WmpSpace d m p) : WLp d m p) : Euc d → (WIndex d m → ℝ)) y (wZero d m) * ψ' y
          = ∫ y, (φ n).1 y * ψ' y := by
        refine integral_congr_ae ?_
        filter_upwards [sa11_J_coe (m := m) (p := p) (φ n)] with y hy
        rw [hy]
        show partialDeriv (wZero d m).2 (φ n).1 y * ψ' y = _
        rw [show partialDeriv (wZero d m).2 (φ n).1 = (φ n).1 from sa11_partialDeriv_zero (wZero d m).2 (φ n).1]
      rw [e1, e2]
      exact hψ'eq (φ n).1 (φ n).2
    -- limits
    have hlim1 : Filter.Tendsto (fun n => sa11_pairL (m := m) (p := p) ⟨j, i⟩ hψ.1.continuous hψ.2
        ((x n : WmpSpace d m p) : WLp d m p)) Filter.atTop
        (nhds (sa11_pairL (m := m) (p := p) ⟨j, i⟩ hψ.1.continuous hψ.2 (F : WLp d m p))) :=
      ((sa11_pairL (m := m) (p := p) ⟨j, i⟩ hψ.1.continuous hψ.2).continuous.tendsto _).comp
        ((continuous_subtype_val.tendsto F).comp hxt)
    have hlim2 : Filter.Tendsto (fun n => sa11_pairL (m := m) (p := p) (wZero d m) hψ'.1.continuous hψ'.2
        ((x n : WmpSpace d m p) : WLp d m p)) Filter.atTop
        (nhds (sa11_pairL (m := m) (p := p) (wZero d m) hψ'.1.continuous hψ'.2 (F : WLp d m p))) :=
      ((sa11_pairL (m := m) (p := p) (wZero d m) hψ'.1.continuous hψ'.2).continuous.tendsto _).comp
        ((continuous_subtype_val.tendsto F).comp hxt)
    have heq := tendsto_nhds_unique hlim1 (hlim2.congr fun n => (hval n).symm)
    rw [sa11_pairL_apply, sa11_pairL_apply] at heq
    rw [heq]
    have : ∀ᵐ y ∂(volume : Measure (Euc d)), ((F : WLp d m p) : Euc d → (WIndex d m → ℝ)) y (wZero d m) * ψ' y = 0 := by
      filter_upwards [h] with y hy
      rw [hy]; simp
    rw [integral_congr_ae this]; simp
  have hall : ∀ τ : WIndex d m, ∀ᵐ y ∂(volume : Measure (Euc d)),
      ((F : WLp d m p) : Euc d → (WIndex d m → ℝ)) y τ = 0 := by
    intro τ
    refine ae_eq_zero_of_integral_contDiff_smul_eq_zero ?_ fun g hg hgc => ?_
    · have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := Fact.out
      exact (sa11_comp_memLp τ (F : WLp d m p)).locallyIntegrable hp1
    · have := hcomp τ g ⟨hg, hgc⟩
      simp only [smul_eq_mul]
      rw [← this]
      congr 1; funext y; ring
  have hF0 : ((F : WLp d m p) : Euc d → (WIndex d m → ℝ)) =ᵐ[volume] 0 := by
    have := ae_all_iff.2 hall
    filter_upwards [this] with y hy
    funext τ
    exact hy τ
  apply Subtype.ext
  apply Lp.ext
  exact hF0.trans (Lp.coeFn_zero _ _ _).symm

end Pairing

/-- Two elements of `W^{m,p}` with the same zeroth component are equal. -/
theorem sa11_eq_of_zeroth {m : ℕ} {p : ℝ} [Fact (2 ≤ p)] {F G : WmpSpace d m p}
    (h : ∀ᵐ x ∂(volume : Measure (Euc d)),
      ((F : WLp d m p) : Euc d → (WIndex d m → ℝ)) x (wZero d m) =
        ((G : WLp d m p) : Euc d → (WIndex d m → ℝ)) x (wZero d m)) : F = G := by
  have h1 : F - G = 0 := by
    refine sa11_zeroth_inj ?_
    have := Lp.coeFn_sub (F : WLp d m p) (G : WLp d m p)
    filter_upwards [h, this] with x hx hs
    show ((((F : WLp d m p) - (G : WLp d m p) : WLp d m p)) : Euc d → (WIndex d m → ℝ)) x (wZero d m) = 0
    rw [hs]
    simp [Pi.sub_apply, hx]
  exact sub_eq_zero.1 h1

/-! ### `wNormE` and the weak output class -/

section WeakClass

variable {m : ℕ} {p : ℝ} [Fact (2 ≤ p)]

/-- `wNormE` of a function with weak jet `G` is `‖G‖`. -/
theorem sa11_wNormE_eq {u : Euc d → ℝ} {G : WmpSpace d m p}
    (hG : ∀ᵐ x ∂(volume : Measure (Euc d)),
      ((G : WLp d m p) : Euc d → (WIndex d m → ℝ)) x (wZero d m) = u x) :
    wNormE m p u = ENNReal.ofReal ‖G‖ := by
  unfold wNormE
  refine le_antisymm (iInf₂_le G hG) (le_iInf₂ fun G' hG' => ?_)
  have : G' = G := sa11_eq_of_zeroth (hG'.mp (hG.mono fun x h1 h2 => h2.trans h1.symm))
  rw [this]

theorem sa11_wWeak_mem {u : Euc d → ℝ} : (wWeakClass (d := d) m p).mem u ↔ wNormE m p u < ⊤ := by
  unfold wWeakClass
  rw [dif_pos (Fact.out : 2 ≤ p)]

theorem sa11_wWeak_norm {u : Euc d → ℝ} : (wWeakClass (d := d) m p).norm u = (wNormE m p u).toReal := by
  unfold wWeakClass
  rw [dif_pos (Fact.out : 2 ≤ p)]

/-- Membership in the weak class gives a (unique) weak jet. -/
theorem sa11_exists_weakJet {u : Euc d → ℝ} (h : (wWeakClass (d := d) m p).mem u) :
    ∃ G : WmpSpace d m p, ∀ᵐ x ∂(volume : Measure (Euc d)),
      ((G : WLp d m p) : Euc d → (WIndex d m → ℝ)) x (wZero d m) = u x := by
  rw [sa11_wWeak_mem] at h
  by_contra hne
  have : wNormE m p u = ⊤ := by
    unfold wNormE
    refine iInf₂_eq_top.2 fun G hG => absurd ⟨G, hG⟩ hne
  exact absurd h (by rw [this]; exact lt_irrefl _)

/-- The norm of the weak class is the norm of the weak jet. -/
theorem sa11_wWeak_norm_eq {u : Euc d → ℝ} {G : WmpSpace d m p}
    (hG : ∀ᵐ x ∂(volume : Measure (Euc d)),
      ((G : WLp d m p) : Euc d → (WIndex d m → ℝ)) x (wZero d m) = u x) :
    (wWeakClass (d := d) m p).norm u = ‖G‖ := by
  rw [sa11_wWeak_norm, sa11_wNormE_eq hG, ENNReal.toReal_ofReal (norm_nonneg _)]

end WeakClass

end HRS.MS.ZeroTemp
