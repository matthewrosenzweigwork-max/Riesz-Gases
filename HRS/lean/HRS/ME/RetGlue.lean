import HRS.ME.RetGlueB
import HRS.MD.EQLawFlow

/-!
# Row 5.10: `ui_comparison` from the two stationary retained estimates

`ui_comparison_of_ret_proof`: truncate the initial density at level `L` and renormalise (`ret_trunc_exists`); the actual
window is within `2Θ(L)` of the weighted stationary window (`ret_window_compare`, from `ret_path_law_proof`), the weighted
stationary window is within `C ‖h'‖₂ √δ_N` of the target by the stationary estimate with `‖h'‖₂² ≤ 2L`, and the target of
the weighted stationary estimate is within `2Θ(L)` of the target of `ui_comparison` (`ret_target_compare`).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

namespace HRS.ME.Ret

open HRS HRS.LZ HRS.MD.EQLawFlow

/-- The square-root bound `(∫⁻ h'^2)^{1/2} ≤ ofReal (√2 √L)`. -/
theorem ret_rpow_half_le {L : ℝ} (hL : 0 ≤ L) {x : ℝ≥0∞} (hx : x ≤ ENNReal.ofReal (2 * L)) :
    x ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal (Real.sqrt 2 * Real.sqrt L) := by
  calc x ^ (1 / 2 : ℝ) ≤ (ENNReal.ofReal (2 * L)) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow hx (by norm_num)
    _ = ENNReal.ofReal ((2 * L) ^ (1 / 2 : ℝ)) :=
        ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)
    _ = ENNReal.ofReal (Real.sqrt 2 * Real.sqrt L) := by
        rw [← Real.sqrt_eq_rpow, Real.sqrt_mul (by norm_num)]

theorem ret_const_le {C₁ K L e : ℝ} (hC₁ : 0 ≤ C₁) (_hL : 0 ≤ L) (he : 0 ≤ e) {x : ℝ≥0∞}
    (hx : x ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal (Real.sqrt 2 * Real.sqrt L)) (hC : C₁ ≤ K) :
    ENNReal.ofReal C₁ * x ^ (1 / 2 : ℝ) * ENNReal.ofReal e ≤
      ENNReal.ofReal (Real.sqrt 2 * K * Real.sqrt L * e) := by
  calc ENNReal.ofReal C₁ * x ^ (1 / 2 : ℝ) * ENNReal.ofReal e
      ≤ ENNReal.ofReal C₁ * ENNReal.ofReal (Real.sqrt 2 * Real.sqrt L) * ENNReal.ofReal e := by
        gcongr
    _ = ENNReal.ofReal (C₁ * (Real.sqrt 2 * Real.sqrt L) * e) := by
        rw [← ENNReal.ofReal_mul hC₁, ← ENNReal.ofReal_mul (by positivity)]
    _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        have h2 : 0 ≤ Real.sqrt 2 * Real.sqrt L := by positivity
        calc C₁ * (Real.sqrt 2 * Real.sqrt L) * e
            = (C₁ * (Real.sqrt 2 * Real.sqrt L)) * e := rfl
          _ ≤ (K * (Real.sqrt 2 * Real.sqrt L)) * e := by gcongr
          _ = _ := by ring

theorem ui_comparison_of_ret_proof (d : ℕ) (hS2a : RetStationaryInitial d)
    (hS2b : RetStationaryShift d) : type_of% (@HRS.ui_comparison d) := by
  intro hd s β hs0 hsd hβ V hV ρβ hρβ hρS hρpos T hT p φ hφ
  have hT1 : (0 : ℝ) < T + 1 := by linarith
  obtain ⟨C₁, hC₁0, hC₁⟩ :=
    hS2a hd hs0 hsd hβ V hV ρβ hρβ hρS hρpos (T + 1) hT1 p φ hφ
  obtain ⟨C₂, c, hC₂0, hc, hC₂⟩ :=
    hS2b hd hs0 hsd hβ V hV ρβ hρβ hρS hρpos (T + 1) hT1 p φ hφ
  have hφc : ∀ a, Continuous (φ a) := fun a =>
    Torus.continuous_of_continuous_lift (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift (φ a)) from hφ a).continuous
  refine ⟨Real.sqrt 2 * max C₁ C₂, c, by positivity, hc, ?_⟩
  intro S hsol hfilt hac L hL hΘ n
  have hL0 : (0 : ℝ) ≤ L := by linarith
  have hN : 2 ≤ n + 2 := by omega
  have : BorelSpace (Torus d) := Pi.borelSpace
  have : BorelSpace (Config d (n + 2)) := Pi.borelSpace
  have hGp : IsProbabilityMeasure (canonicalGibbs (periodicRiesz d s) V (n + 2) β) :=
    eqlaw_gibbs_prob hd hs0 hsd hV hβ (by omega)
  set Gb : Measure (Config d (n + 2)) := canonicalGibbs (periodicRiesz d s) V (n + 2) β with hGb
  set Θ : ℝ≥0∞ := uiTail d s β V (fun n => (S.P n).map (S.X₀ n)) L with hΘdef
  set ν : Measure (Config d (n + 2)) := (S.P n).map (S.X₀ n) with hν
  set D : DynData d := PDE.mfData d s hs0 hsd V β hβ with hD
  have hsolT : ∀ T' : ℝ, 0 ≤ T' →
      IsParticleSystem (S.P n) D T' (S.X₀ n) (S.W n) (S.X n) := fun T' hT' => hsol T' hT' n
  have hX₀m : AEMeasurable (S.X₀ n) (S.P n) := by
    have hstr := (hsolT 0 le_rfl).sol
    exact (hstr.adapted 0).aemeasurable.congr hstr.init
  have hνac : ν ≪ Gb := hac n
  have hθ : ν {x | ENNReal.ofReal L < ν.rnDeriv Gb x} ≤ Θ :=
    le_iSup (f := fun m => ((S.P m).map (S.X₀ m))
      {X | ENNReal.ofReal L < ((S.P m).map (S.X₀ m)).rnDeriv
        (canonicalGibbs (periodicRiesz d s) V (m + 2) β) X}) n
  have hΘ' : Θ ≤ 2⁻¹ := by simpa [one_div] using hΘ
  obtain ⟨h', hh'm, ⟨M, hM⟩, hint, hsq, hTV⟩ := ret_trunc_exists Gb ν hνac L Θ hθ hΘ'
  have h2Θ : 2 * Θ ≤ 4 * Θ := by
    gcongr; norm_num
  have hhalf : ∀ {Ω₂ : Type} [MeasurableSpace Ω₂] (P₂ : Measure Ω₂) (X₀₂ : Ω₂ → Config d (n + 2)),
      AEMeasurable X₀₂ P₂ → P₂.map X₀₂ = Gb →
      ∫⁻ ω, h' (X₀₂ ω) ∂P₂ = 1 ∧ ∫⁻ ω, h' (X₀₂ ω) ^ 2 ∂P₂ ≤ ENNReal.ofReal (2 * L) := by
    intro Ω₂ _ P₂ X₀₂ hm hlaw
    refine ⟨?_, ?_⟩
    · rw [← lintegral_map' hh'm.aemeasurable hm, hlaw, hint]
    · rw [← lintegral_map' (hh'm.pow_const 2).aemeasurable hm, hlaw]; exact hsq
  constructor
  · intro t ht G hG hGm hind
    set γ := ProbabilityTheory.multivariateGaussian 0
      (noiseCovMatrix D (fun _ => ρβ) β⁻¹ t φ) with hγ
    have ht' : ∀ a, t a ∈ Set.Icc (0 : ℝ) (T + 1) := fun a => ⟨(ht a).1, by linarith [(ht a).2]⟩
    have hτ : ∀ a, (((t a).toNNReal : ℝ≥0) : ℝ) ≤ T + 1 := fun a => by
      rw [Real.coe_toNNReal _ (ht a).1]; linarith [(ht a).2]
    obtain ⟨Ω₂, _, P₂, _, X₀₂, W₂, X₂, hflow⟩ :=
      eq_flow_exists_proof hd hs0 hsd V hV hβ hN (T + 1) hT1.le
    have hstr₂ : IsStrongSolution P₂ D (T + 1) X₀₂ W₂ X₂ := by
      rcases hflow.flow.flow with ⟨h, _⟩ | ⟨h1, _⟩
      · exact h
      · exfalso; omega
    have hX₀₂m : AEMeasurable X₀₂ P₂ := (hstr₂.adapted 0).aemeasurable.congr hstr₂.init
    obtain ⟨hint2, hsq2⟩ := hhalf P₂ X₀₂ hX₀₂m hflow.init
    have hmain := ret_window_compare hd hs0 hsd V hV hβ hN (T + 1) hT1.le φ hφc
      (fun a => (t a).toNNReal) hτ (S.P n) (S.X₀ n) (S.W n) (S.X n) (hsolT _ hT1.le) (hfilt n)
      hνac P₂ X₀₂ W₂ X₂ hflow h' hh'm hint
    have hbound := hC₁ (n + 2) hN P₂ X₀₂ W₂ X₂ hflow h' hh'm ⟨M, hM⟩ hint2 t ht'
    have hWD : IsProbabilityMeasure (P₂.withDensity fun ω => h' (X₀₂ ω)) :=
      ⟨by rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]; exact hint2⟩
    set f : Config d (n + 2) → EuclideanSpace ℝ (Fin p) := fun x =>
      retVec d s β V (n + 2) (fun a => propagator D (fun _ => ρβ) 0 (t a) (φ a)) (fun _ => x)
      with hf
    have hfm : Measurable f :=
      (ret_retVec_measurable s β V (n + 2) _
        (fun a => ret_propagator_continuous _ _ (ht a).1 _)).comp
        (measurable_pi_iff.2 fun _ => measurable_id)
    have eB : ((P₂.withDensity fun ω => h' (X₀₂ ω)).map fun ω => retVec d s β V (n + 2)
        (fun a => propagator D (fun _ => ρβ) 0 (t a) (φ a)) fun _ => X₀₂ ω) =
        (Gb.withDensity h').map f := by
      have := ret_init_law P₂ X₀₂ (X₂ 0) (hstr₂.adapted 0) hstr₂.init h' hh'm f hfm
      rw [show P₂.map X₀₂ = Gb from hflow.init] at this
      exact this
    rw [eB] at hbound
    have eT : (law (S.P n) fun ω => (WithLp.toLp 2 fun a =>
        linCoord (firstMarginal Gb) (propagator D (fun _ => ρβ) 0 (t a) (φ a)) (S.X₀ n ω) + G ω a :
          EuclideanSpace ℝ (Fin p))) = (ν.map f) ∗ γ := by
      have hfun : (fun ω => (WithLp.toLp 2 fun a =>
          linCoord (firstMarginal Gb) (propagator D (fun _ => ρβ) 0 (t a) (φ a)) (S.X₀ n ω) +
            G ω a : EuclideanSpace ℝ (Fin p))) = (fun ω => f (S.X₀ n ω)) + G := by
        funext ω; ext a; simp [hf, retVec, hGb]
      rw [hfun]
      have hind' : IndepFun (fun ω => f (S.X₀ n ω)) G (S.P n) := hind.comp hfm measurable_id
      have e := hind'.map_add_eq_map_conv_map₀ (f := fun ω => f (S.X₀ n ω))
        (hfm.comp_aemeasurable hX₀m) hGm
      refine e.trans ?_
      rw [show Measure.map G (S.P n) = γ from hG]
      congr 1
      exact (AEMeasurable.map_map_of_aemeasurable hfm.aemeasurable hX₀m).symm
    rw [eT]
    have hfin : ∀ (μ : Measure (EuclideanSpace ℝ (Fin p))), IsProbabilityMeasure μ →
        IsFiniteMeasure μ := fun μ h => inferInstance
    -- the three comparisons
    have t1 := hmain.trans hTV
    have t2 : ENNReal.ofReal (smoothDist 2
        ((P₂.withDensity fun ω => h' (X₀₂ ω)).map fun ω =>
          retVec d s β V (n + 2) φ fun a => X₂ (t a).toNNReal ω)
        (((Gb.withDensity h').map f) ∗ γ)) ≤
        ENNReal.ofReal (Real.sqrt 2 * max C₁ C₂ * Real.sqrt L * Real.sqrt (deltaN d s (n + 2))) :=
      hbound.trans (ret_const_le hC₁0 hL0 (Real.sqrt_nonneg _)
        ((ENNReal.rpow_le_rpow hsq2 (by norm_num)).trans (ret_rpow_half_le hL0 le_rfl))
        (le_max_left _ _))
    have t3 : ENNReal.ofReal (smoothDist 2 (((Gb.withDensity h').map f) ∗ γ) ((ν.map f) ∗ γ)) ≤
        2 * Θ := by
      rw [ret_smoothDist_comm]
      exact (ret_target_compare Gb ν hνac γ f hfm h' hh'm hint).trans hTV
    have hGh : IsProbabilityMeasure (Gb.withDensity h') :=
      ⟨by rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]; exact hint⟩
    refine (ret_ofReal_triangle3 _ _ _ _).trans
      ((add_le_add (add_le_add t1 t2) t3).trans (le_of_eq ?_))
    ring
  · intro u hu t ht
    have ht' : ∀ a, t a ∈ Set.Icc (0 : ℝ) (T + 1) := fun a => ⟨(ht a).1, by linarith [(ht a).2]⟩
    have hTu : (0 : ℝ) ≤ u + (T + 1) := by linarith
    have hτ : ∀ a, (((u + t a).toNNReal : ℝ≥0) : ℝ) ≤ u + (T + 1) := fun a => by
      rw [Real.coe_toNNReal _ (by linarith [(ht a).1])]; linarith [(ht a).2]
    obtain ⟨Ω₂, _, P₂, _, X₀₂, W₂, X₂, hflow⟩ :=
      eq_flow_exists_proof hd hs0 hsd V hV hβ hN (u + (T + 1)) hTu
    have hstr₂ : IsStrongSolution P₂ D (u + (T + 1)) X₀₂ W₂ X₂ := by
      rcases hflow.flow.flow with ⟨h, _⟩ | ⟨h1, _⟩
      · exact h
      · exfalso; omega
    have hX₀₂m : AEMeasurable X₀₂ P₂ := (hstr₂.adapted 0).aemeasurable.congr hstr₂.init
    obtain ⟨hint2, hsq2⟩ := hhalf P₂ X₀₂ hX₀₂m hflow.init
    have hmain := ret_window_compare hd hs0 hsd V hV hβ hN (u + (T + 1)) hTu φ hφc
      (fun a => (u + t a).toNNReal) hτ (S.P n) (S.X₀ n) (S.W n) (S.X n) (hsolT _ hTu) (hfilt n)
      hνac P₂ X₀₂ W₂ X₂ hflow h' hh'm hint
    have hbound := hC₂ (n + 2) hN u hu P₂ X₀₂ W₂ X₂ hflow h' hh'm ⟨M, hM⟩ hint2 t ht'
    have hWD : IsProbabilityMeasure (P₂.withDensity fun ω => h' (X₀₂ ω)) :=
      ⟨by rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]; exact hint2⟩
    have t1 := hmain.trans hTV
    have t2 : ENNReal.ofReal (smoothDist 2
        ((P₂.withDensity fun ω => h' (X₀₂ ω)).map fun ω =>
          retVec d s β V (n + 2) φ fun a => X₂ (u + t a).toNNReal ω)
        (ProbabilityTheory.multivariateGaussian 0 (PDE.stationaryLagCov d s β D ρβ t φ))) ≤
        ENNReal.ofReal (Real.sqrt 2 * max C₁ C₂ * Real.sqrt L *
          (Real.sqrt (deltaN d s (n + 2)) + Real.exp (-c * u))) :=
      hbound.trans (ret_const_le hC₂0 hL0 (add_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le)
        ((ENNReal.rpow_le_rpow hsq2 (by norm_num)).trans (ret_rpow_half_le hL0 le_rfl))
        (le_max_right _ _))
    refine (ret_ofReal_triangle2 _ _ _).trans ((add_le_add t1 t2).trans ?_)
    calc 2 * Θ + ENNReal.ofReal (Real.sqrt 2 * max C₁ C₂ * Real.sqrt L *
          (Real.sqrt (deltaN d s (n + 2)) + Real.exp (-c * u))) ≤ _ + 4 * Θ := by
          rw [add_comm]; exact add_le_add le_rfl h2Θ


end HRS.ME.Ret

end
