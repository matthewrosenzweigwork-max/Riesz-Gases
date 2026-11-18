import HRS.Main.ThermLin2St4
import HRS.Main.ThermLin2Ba4

/-!
# THERMLIN2, packet St, part 5: D5 `tl2_zero_start_vs_stationary`

The product system `P₂ ⊗ γ` (zero-start Gaussian times the independent initial datum `ξ ~ N(0, C_β)`) carries the process
`Z̃^t = W^{t,0} ξ + Zb^t`.  Its finite-dimensional laws are the stationary ones (`tl2St_fdd_core`: the noise vector has
the law given by `tl2Ba_zb_fdd` and is independent of `ξ` because the measure is a product, so no martingale on the
product space is needed).  `tl2_stationary_window_indep_proof` identifies its window law with that of any stationary
field, and `tl2_init_shift_proof` compares it with the window of `Zb`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators Matrix RealInnerProductSpace

namespace HRS.ThermLin.Plan2

open HRS HRS.PDE HRS.PDE.MFSemigroup HRS.Uniform HRS.GF HRS.AdjK HRS.T25P HRS.Uniform.Q54c HRS.Uniform.Q07c

variable {d : ℕ}

/-- Symmetry of `wassersteinE` (the Hilbert-space proof `HilbertCLTAux.wassersteinE_comm_aux`, without measurability of the
cost). -/
theorem tl2St_wE_comm_aux {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [MeasurableSpace B]
    [BorelSpace B] (p : ℝ)
    (P Q : Measure B) : wassersteinE p P Q ≤ wassersteinE p Q P := by
  refine le_iInf fun π => ?_
  have hsw : IsCoupling (π.1.map Prod.swap) P Q := by
    refine ⟨?_, ?_⟩
    · rw [Measure.map_map measurable_fst measurable_swap]
      exact π.2.2
    · rw [Measure.map_map measurable_snd measurable_swap]
      exact π.2.1
  refine (wassersteinE_le_cost (p := p) hsw).trans (le_of_eq ?_)
  congr 1
  rw [show π.1.map Prod.swap = π.1.map (MeasurableEquiv.prodComm : B × B ≃ᵐ B × B) from rfl,
    lintegral_map_equiv (fun z : B × B => ENNReal.ofReal (‖z.1 - z.2‖ ^ p)) (MeasurableEquiv.prodComm)]
  congr 1; ext z
  change ENNReal.ofReal (‖z.2 - z.1‖ ^ p) = ENNReal.ofReal (‖z.1 - z.2‖ ^ p)
  rw [norm_sub_rev]

theorem tl2St_wE_comm {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [MeasurableSpace B]
    [BorelSpace B] (p : ℝ)
    (P Q : Measure B) : wassersteinE p P Q = wassersteinE p Q P :=
  le_antisymm (tl2St_wE_comm_aux p P Q) (tl2St_wE_comm_aux p Q P)

/-- Finite `p`-th moments of a Gaussian, `p = 1, 2`. -/
theorem tl2St_gauss_moment {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]
    (γ : Measure E) [IsGaussian γ] (p : ℝ) (hp : p = 1 ∨ p = 2) :
    (∫⁻ x, ‖x‖ₑ ^ p ∂γ) ^ (1 / p) < ⊤ := by
  have hp0 : 0 < p := by rcases hp with rfl | rfl <;> norm_num
  have hmem : MemLp id (ENNReal.ofReal p) γ := IsGaussian.memLp_id γ (ENNReal.ofReal p) (by simp)
  have h2 := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (p := ENNReal.ofReal p)
    (by simpa using hp0) (by simp) hmem.eLpNorm_lt_top
  rw [ENNReal.toReal_ofReal hp0.le] at h2
  exact ENNReal.rpow_lt_top_of_nonneg (by positivity) h2.ne

/-- D5 proof. -/
theorem tl2_zero_start_vs_stationary_proof (S : HRS.Main.PreparedData d) {ρβ : Torus d → ℝ}
    (h : IsThermalDensity (periodicRiesz d S.s) S.V S.β ρβ) (m : ℝ) (hm : (d : ℝ) + 2 < m) (T : ℝ) (hT : 0 < T) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ a : ℝ, 0 ≤ a → ∀ (p : ℝ), (p = 1 ∨ p = 2) →
      ∀ (Wev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m), IsDualEvolution S.dyn (fun _ => ρβ) m Wev →
      (∀ T' : ℝ, 0 ≤ T' → IsPlainEvolution Wev T') →
      ∀ {Ω₂ : Type} [mΩ₂ : MeasurableSpace Ω₂] (P₂ : Measure Ω₂) [IsProbabilityMeasure P₂] {ℱ₂ : Filtration ℝ mΩ₂}
        (Ĝ Zb : ℝ → Ω₂ → NegSobolev d m),
        IsHilbertMartingaleWithCovariation P₂ ℱ₂ (a + T) Ĝ (fun r _ => tl2CbDens S ρβ m (a + T) r) →
        (∀ t ∈ Set.Icc (0 : ℝ) (a + T),
          IsStochConv P₂ Wev (ContinuousLinearMap.id ℝ (NegSobolev d m)) Ĝ 0 t (Zb t)) →
        (∀ t, Measurable (Zb t)) → (∀ᵐ ω ∂P₂, ContinuousOn (fun t => Zb t ω) (Set.Icc 0 (a + T))) →
      ∀ {Ω'' : Type} [MeasurableSpace Ω''] (P'' : Measure Ω'') [IsProbabilityMeasure P'']
        (Z : ℝ → Ω'' → NegSobolev d m),
        IsStationaryGaussianField P'' S.s S.β S.hs0 S.hsd S.hβ S.V ρβ m Z →
        wassersteinE p (law P₂ (Uniform.windowPath a T Zb)) (law P'' (HRS.Main.windowPath m T 0 Z)) ≤
          ENNReal.ofReal (C * Real.exp (-c * a)) := by
  obtain ⟨γ, hγp, hγ, -⟩ := tl2_xi_law_proof S h m hm
  haveI : IsProbabilityMeasure γ := hγp
  haveI : IsGaussian γ := hγ.1.1
  obtain ⟨Cr, cr, hCr, hcr, WA, hdualA, -, hdecA⟩ := HRS.ThermLin.thermlin_stationary_evolution S h m
  -- moments
  set M : ℝ → ℝ := fun p => ((∫⁻ x, ‖x‖ₑ ^ p ∂γ) ^ (1 / p)).toReal with hM
  have hM1 := tl2St_gauss_moment γ 1 (Or.inl rfl)
  have hM2 := tl2St_gauss_moment γ 2 (Or.inr rfl)
  refine ⟨Cr * (M 1 + M 2) + 1, cr, by positivity, hcr, ?_⟩
  intro a ha p hp Wev hWd hWp Ω₂ _ P₂ _ ℱ₂ Ĝ Zb hĜ hZb hZbm hZbc Ω'' _ P'' _ Z hZ
  have hMp : (∫⁻ x, ‖x‖ₑ ^ p ∂γ) ^ (1 / p) < ⊤ := by
    rcases hp with rfl | rfl
    · exact hM1
    · exact hM2
  have hMp0 : 0 ≤ M p := ENNReal.toReal_nonneg
  have hMle : M p ≤ M 1 + M 2 := by
    have h1 : 0 ≤ M 1 := ENNReal.toReal_nonneg
    have h2 : 0 ≤ M 2 := ENNReal.toReal_nonneg
    rcases hp with rfl | rfl <;> linarith
  -- decay of the given evolution
  have hdec : ∀ u t : ℝ, 0 ≤ u → u ≤ t → ‖Wev t u‖ ≤ Cr * Real.exp (-cr * (t - u)) := by
    intro u t hu hut
    rw [t25p_dual_unique hWd hdualA hu hut]
    exact hdecA u t hu hut
  have hTa : 0 < a + T := by linarith
  have hWp' : IsPlainEvolution Wev (a + T) := hWp (a + T) hTa.le
  have hWb : ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ a + T → ‖Wev t r‖ ≤ Cr := by
    intro r t hr hrt _
    refine (hdec r t hr hrt).trans ?_
    have : Real.exp (-cr * (t - r)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith [sub_nonneg.2 hrt]
    nlinarith
  have hdec0 : ∀ t : ℝ, 0 ≤ t → t ≤ a + T → ‖Wev t 0‖ ≤ Cr * Real.exp (-cr * t) := by
    intro t ht _
    simpa using hdec 0 t le_rfl ht
  -- the product system
  set P₁ : Measure (Ω₂ × NegSobolev d m) := P₂.prod γ with hP₁
  set Zt : ℝ → Ω₂ × NegSobolev d m → NegSobolev d m := fun t w => Wev t 0 w.2 + Zb t w.1 with hZt
  have hZtm : ∀ t, Measurable (Zt t) := fun t =>
    (((Wev t 0).continuous).measurable.comp measurable_snd).add ((hZbm t).comp measurable_fst)
  have hZtc : ∀ᵐ w ∂P₁, ContinuousOn (fun t => Zt t w) (Set.Icc 0 (a + T)) := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hZbc] with w hw
    exact (HRS.Uniform.Comp28.continuousOn_V_zero Wev hWp'.2.2 w.2).add hw
  have hCb0 : ∀ σ : ℝ, σ ∉ Set.Icc 0 (a + T) → tl2CbDens S ρβ m (a + T) σ = 0 := by
    intro σ hσ
    simp [tl2CbDens, covDensT, hσ]
  have hfdd : Tl2StatFdd S ρβ m (a + T) P₁ Zt := by
    refine ⟨hZtm, hZtc, ?_⟩
    intro p' τ φ hτ hφ
    have hmem : ∀ i, MemSobolev m (φ i) := fun i => HRS.PDE.MFSemigroup.memSobolev_of_isSmooth (hφ i) m
    have hX2 := tl2Ba_zb_fdd hTa hCr.le Wev hWp' hWb (tl2CbDens S ρβ m (a + T)) hCb0 P₂ Ĝ Zb hĜ hZb hZbm τ hτ φ hmem
    set Bm : Matrix (Fin p') (Fin p') ℝ := Matrix.of fun i j => ∫ σ in Set.Icc 0 (min (τ i) (τ j)),
        tl2CbDens S ρβ m (a + T) σ
          (pullbackVec (HRS.Uniform.Comp28.plainData Wev) (τ i) σ (gfb4_ell m (φ i)))
          (pullbackVec (HRS.Uniform.Comp28.plainData Wev) (τ j) σ (gfb4_ell m (φ j))) with hBm
    have hXlaw : P₁.map (fun w : Ω₂ × NegSobolev d m => (WithLp.toLp 2 fun i => NegSobolev.eval (Zb (τ i) w.1) (φ i) :
        EuclideanSpace ℝ (Fin p'))) = multivariateGaussian 0 Bm := by
      have hXm : Measurable (fun ω : Ω₂ => (WithLp.toLp 2 fun i => NegSobolev.eval (Zb (τ i) ω) (φ i) :
          EuclideanSpace ℝ (Fin p'))) :=
        measurable_toLp_eval fun i => (continuous_eval_const (hmem i)).measurable.comp (hZbm _)
      have : (fun w : Ω₂ × NegSobolev d m => (WithLp.toLp 2 fun i => NegSobolev.eval (Zb (τ i) w.1) (φ i) :
          EuclideanSpace ℝ (Fin p'))) = (fun ω : Ω₂ => (WithLp.toLp 2 fun i => NegSobolev.eval (Zb (τ i) ω) (φ i) :
          EuclideanSpace ℝ (Fin p'))) ∘ Prod.fst := rfl
      rw [this, ← Measure.map_map hXm measurable_fst, hP₁, Measure.map_fst_prod, measure_univ, one_smul]
      exact hX2
    obtain ⟨G', hG', hGc, hGz, -⟩ := gfb4_modify P₂ ℱ₂ hTa.le Ĝ (tl2CbDens S ρβ m (a + T)) hCb0 hĜ
    have hBpsd : Bm.PosSemidef := by
      refine tl2St_cov_psd (B := Cr * ∑ b, ‖gfb4_ell m (φ b)‖) hG' hGc hGz hTa τ hτ
        (fun i σ => pullbackVec (HRS.Uniform.Comp28.plainData Wev) (τ i) σ (gfb4_ell m (φ i))) ?_ ?_
      · intro i σ hσ
        have h1 := t25p_norm_pullback_le Wev hWb hCr.le hσ.1 hσ.2 (hτ i).2 (gfb4_ell m (φ i))
        refine h1.trans ?_
        refine mul_le_mul_of_nonneg_left ?_ hCr.le
        exact Finset.single_le_sum (f := fun b => ‖gfb4_ell m (φ b)‖) (fun b _ => norm_nonneg _)
          (Finset.mem_univ i)
      · intro i x
        exact t25p_pullback_weak Wev hWp'.2.2 (hτ i) _ x
    have hindX : IndepFun (fun w : Ω₂ × NegSobolev d m => (WithLp.toLp 2 fun i =>
        NegSobolev.eval (Zb (τ i) w.1) (φ i) : EuclideanSpace ℝ (Fin p'))) (fun w : Ω₂ × NegSobolev d m => w.2) P₁ :=
      indepFun_prod (μ := P₂) (ν := γ) (X := fun ω : Ω₂ => (WithLp.toLp 2 fun i =>
        NegSobolev.eval (Zb (τ i) ω) (φ i) : EuclideanSpace ℝ (Fin p'))) (Y := fun x : NegSobolev d m => x)
        (measurable_toLp_eval fun i => (continuous_eval_const (hmem i)).measurable.comp (hZbm _)) measurable_id
    have hξlaw : P₁.map (fun w : Ω₂ × NegSobolev d m => w.2) = γ := by
      rw [hP₁]; exact (by simp [Measure.map_snd_prod])
    exact tl2St_fdd_core S h m hm hTa hCr.le Wev hWd hWb P₁ γ hγ (fun w => w.2) measurable_snd hξlaw
      (fun t w => Zb t w.1) (fun t => (hZbm t).comp measurable_fst) τ φ hτ hφ hBpsd hXlaw hindX
  have hstat := tl2_isStationary_finite_proof S m T P'' Z hZ
  have hlaw0 := tl2_stationary_window_indep_proof S m T hT P₁ P'' Zt Z ha hfdd hstat
  have hinit := tl2_init_shift_proof hT ha hCr.le hcr.le Wev hWp' hdec0 P₂ Zb hZbm hZbc γ p hp
  have hconv : law P₁ (Uniform.windowPath a T Zt) = law P'' (HRS.Main.windowPath m T 0 Z) := by
    rw [tl2Ba_uwin_eq m T a Zt]
    exact hlaw0
  have hmain : wassersteinE p (law P₂ (Uniform.windowPath a T Zb)) (law P₁ (Uniform.windowPath a T Zt)) ≤
      ENNReal.ofReal ((Cr * (M 1 + M 2) + 1) * Real.exp (-cr * a)) := by
    rw [tl2St_wE_comm]
    refine hinit.trans ?_
    rw [← ENNReal.ofReal_toReal hMp.ne, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have he : 0 ≤ Real.exp (-cr * a) := (Real.exp_pos _).le
    have : Cr * Real.exp (-cr * a) * M p ≤ Cr * Real.exp (-cr * a) * (M 1 + M 2) :=
      mul_le_mul_of_nonneg_left hMle (by positivity)
    nlinarith
  rw [hconv] at hmain
  exact hmain

example := (@tl2_zero_start_vs_stationary_proof : type_of% @tl2_zero_start_vs_stationary)

end HRS.ThermLin.Plan2
