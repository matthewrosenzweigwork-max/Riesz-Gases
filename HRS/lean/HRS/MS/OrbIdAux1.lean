import HRS.Prob.HilbertMartingale

/-!
# S5.2 identification (aux 1): generic Itô-integral bookkeeping

Infrastructure for `orbit_maximal_identification` (packet S52); helper lemmas carry the prefix `s52_`, namespace
`HRS.MS.S52`.  Everything here is generic (no oscillator or orbit data):

* `s52_brownian_of_cyl`: for a finite index set, a cylindrical Brownian motion is a Brownian filtration;
* `s52_pair_ito`: for a finite index set the coordinates `⟨M_τ, x⟩` of a Hilbert Itô integral are the real Itô integral
  of `⟨Φ, x⟩` (the `approx` field at the full finite set, reindexing along `↥univ → κ`);
* `s52_kill`: `∫ 1_{r ≤ t} u dW (τ) = ∫ u dW (min τ t)`;
* `s52_lc`: integrands that agree on `[0,t]` (for all `ω`) have a.s. equal integrals at all times `min τ t`.
-/

noncomputable section

set_option linter.unusedSectionVars false

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.S52

open HRS

section Brown

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ mΩ}

lemma s52_law_restrict {ι ι' : Type*} [Fintype ι] [Fintype ι'] (e : ι' → ι)
    (he : Function.Injective e) (Y : Ω → ι → ℝ) (v : ℝ≥0)
    (h : HasLaw Y (Measure.pi fun _ : ι => gaussianReal 0 v) P) :
    HasLaw (fun ω i => Y ω (e i)) (Measure.pi fun _ : ι' => gaussianReal 0 v) P := by
  classical
  have hY : ∀ i, AEMeasurable (fun ω => Y ω i) P := fun i =>
    (measurable_pi_apply i).comp_aemeasurable h.aemeasurable
  have hmarg : ∀ i, P.map (fun ω => Y ω i) = gaussianReal 0 v := by
    intro i
    have h1 : (fun ω => Y ω i) = (Function.eval i) ∘ Y := rfl
    have h2 := AEMeasurable.map_map_of_aemeasurable (μ := P) (g := Function.eval i) (f := Y)
      (by rw [h.map_eq]; exact (measurable_pi_apply i).aemeasurable) h.aemeasurable
    rw [h1, ← h2, h.map_eq, Measure.pi_map_eval]
    simp
  have hind : iIndepFun (fun i ω => Y ω i) P := by
    rw [iIndepFun_iff_map_fun_eq_pi_map hY]
    simp_rw [hmarg]
    exact h.map_eq
  have hind' := hind.precomp he
  have hY' : ∀ i, AEMeasurable (fun ω => Y ω (e i)) P := fun i => hY (e i)
  refine ⟨AEMeasurable.of_eval hY', ?_⟩
  have := (iIndepFun_iff_map_fun_eq_pi_map hY').mp hind'
  rw [this]
  simp_rw [hmarg]

/-- Restriction of a Brownian filtration to a subfamily of the coordinates. -/
theorem s52_brownian_restrict {ι ι' : Type*} [Fintype ι] [Fintype ι']
    (e : ι' → ι) (he : Function.Injective e) {W : ℝ≥0 → Ω → ι → ℝ}
    (hW : IsBrownianFiltration P ℱ W) :
    IsBrownianFiltration P ℱ (fun t ω (i : ι') => W t ω (e i)) where
  complete := hW.complete
  adapted t := by
    let _ : MeasurableSpace Ω := ℱ t
    exact measurable_pi_iff.mpr fun i => (measurable_pi_apply (e i)).comp (hW.adapted t)
  zero ω := by
    funext i
    simp [hW.zero ω]
  cont ω := continuous_pi fun i => (continuous_apply (e i)).comp (hW.cont ω)
  indep_incr s t hst := by
    refine indep_of_indep_of_le_left (hW.indep_incr s t hst) ?_
    intro A hA
    obtain ⟨B, hB, rfl⟩ := hA
    refine ⟨(fun x : ι' → ℝ => x) ⁻¹' B |>.preimage (fun y : ι → ℝ => fun i => y (e i)), ?_, ?_⟩
    · exact (measurable_pi_iff.mpr fun i => measurable_pi_apply (e i)) hB
    · rfl
  gaussian_incr s t hst :=
    s52_law_restrict e he _ (t - s) (hW.gaussian_incr s t hst)

/-- For a finite index set, a cylindrical Brownian motion is a Brownian filtration. -/
theorem s52_brownian_of_cyl {κ : Type*} [Fintype κ] {W : ℝ≥0 → Ω → κ → ℝ}
    (hW : IsCylindricalBrownian P ℱ W) : IsBrownianFiltration P ℱ W := by
  have h1 := hW (Finset.univ : Finset κ)
  exact s52_brownian_restrict (fun k : κ => (⟨k, Finset.mem_univ k⟩ : ↥(Finset.univ : Finset κ)))
    (fun a b h => congrArg Subtype.val h) h1

end Brown

section Pair

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ mΩ}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
variable {κ : Type*} [Fintype κ]

/-- For a finite index set, the coordinates `⟨M_τ, x⟩` of the Hilbert Itô integral are the real Itô integral of
`⟨Φ, x⟩` (the `approx` field at the full finite set, plus reindexing along `↥univ → κ`). -/
lemma s52_pair_ito {W' : ℝ≥0 → Ω → κ → ℝ} (hW : IsBrownianFiltration P ℱ W') {Φ : ℝ → Ω → κ → H}
    {Mart : ℝ → Ω → H} (hMart : IsHilbertItoIntegral P ℱ W' Φ Mart) (x : H)
    (hξ' : IsProgressiveL2 P ℱ
      (fun r ω (k : (Finset.univ : Finset κ)) => inner ℝ (Φ r ω k) x))
    {τ : ℝ} (hτ : 0 ≤ τ) :
    (fun ω => inner ℝ (Mart τ ω) x) =ᵐ[P]
      itoIntegral P ℱ W' (fun r ω k => inner ℝ (Φ r ω k) x) τ := by
  classical
  have h := hMart.approx τ hτ x
  have h1 : (atTop : Filter (Finset κ)) = pure Finset.univ :=
    atTop_eq_pure_of_isTop (x := (Finset.univ : Finset κ)) (fun s => Finset.subset_univ s)
  rw [h1] at h
  have h0 := tendsto_nhds_unique (tendsto_pure_nhds _ _) h
  set e : ↥(Finset.univ : Finset κ) → κ := fun k => (k : κ) with he
  have hinj : Function.Injective e := Subtype.val_injective
  have hW₁ : IsBrownianFiltration P ℱ (fun t ω (i : (Finset.univ : Finset κ)) => W' t ω (e i)) :=
    s52_brownian_restrict e hinj hW
  have hpad := itoIntegral_pad e hinj hW hW₁ hξ'
  have hpadfun : padFun e (fun r ω (k : (Finset.univ : Finset κ)) => inner ℝ (Φ r ω k) x) =
      fun r ω k => inner ℝ (Φ r ω k) x := by
    funext r ω k
    have := padVec_apply e hinj (fun (k : (Finset.univ : Finset κ)) => inner ℝ (Φ r ω k) x)
      ⟨k, Finset.mem_univ k⟩
    simpa [padFun, he] using this
  rw [hpadfun] at hpad
  have hmeas : AEMeasurable (fun ω => itoIntegral P ℱ
      (fun t ω (k : (Finset.univ : Finset κ)) => W' t ω k)
      (fun r ω (k : (Finset.univ : Finset κ)) => inner ℝ (Φ r ω k) x) τ ω - inner ℝ (Mart τ ω) x) P := by
    refine ((((adapted_itoIntegral P ℱ _ _ τ).mono (ℱ.le τ) le_rfl)).sub ?_).aemeasurable
    exact ((hMart.adapted τ).mono (ℱ.le τ) le_rfl).inner measurable_const
  have h2 := ae_eq_zero_of_lintegral_enorm_sq_eq_zero hmeas h0
  filter_upwards [h2, hpad] with ω hω hp
  have hp' := hp τ
  have : itoIntegral P ℱ (fun t ω (k : (Finset.univ : Finset κ)) => W' t ω k)
      (fun r ω (k : (Finset.univ : Finset κ)) => inner ℝ (Φ r ω k) x) τ ω - inner ℝ (Mart τ ω) x = 0 := hω
  rw [← hp']
  linarith

end Pair

section Kill

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ mΩ}
variable {ι : Type*} [Fintype ι] {W : ℝ≥0 → Ω → ι → ℝ}

lemma s52_ae_ne_zero : ∀ᵐ r ∂(volume : Measure ℝ), r ≠ 0 := by
  rw [ae_iff]; simp

lemma s52_isProgressive_ite {u : ℝ → Ω → ι → ℝ} (hu : IsProgressive ℱ u) {R : Set ℝ}
    [DecidablePred (· ∈ R)] (hR : MeasurableSet R) :
    IsProgressive ℱ (fun r ω k => if r ∈ R then u r ω k else 0) := by
  classical
  have := pc_isProgressive_ite (β := ι → ℝ) hu hR
  convert this using 3 with r ω
  funext k; by_cases h : r ∈ R <;> simp [h]

lemma s52_isProgressiveL2_ite {u : ℝ → Ω → ι → ℝ} (hu : IsProgressiveL2 P ℱ u) {R : Set ℝ}
    [DecidablePred (· ∈ R)] (hR : MeasurableSet R) :
    IsProgressiveL2 P ℱ (fun r ω k => if r ∈ R then u r ω k else 0) :=
  pc_isProgressiveL2_ite hu hR

/-- Killing the integrand after `t` stops the integral at `t`. -/
lemma s52_kill (hW : IsBrownianFiltration P ℱ W) {u : ℝ → Ω → ι → ℝ} (hL : IsProgressiveL2 P ℱ u)
    {t : ℝ} (ht : 0 ≤ t) :
    ∀ᵐ ω ∂P, ∀ τ : ℝ, 0 ≤ τ →
      itoIntegral P ℱ W (fun r ω k => if r ≤ t then u r ω k else 0) τ ω =
      itoIntegral P ℱ W u (min τ t) ω := by
  classical
  set g : ℝ → Ω → ι → ℝ := fun r ω k => if r ≤ t then u r ω k else 0 with hg
  set ind : ℝ → Ω → ι → ℝ := fun s ω => Set.indicator (Set.Ioc 0 t) (fun _ => u s ω) s with hind0
  have hind : ind = fun r ω k => if r ∈ Set.Ioc 0 t then u r ω k else 0 := by
    funext r ω k
    simp only [hind0, Set.indicator_apply]
    split_ifs <;> rfl
  have hLg : IsProgressiveL2 P ℱ g := by
    have := s52_isProgressiveL2_ite hL (measurableSet_Iic (a := t))
    simpa [hg] using this
  have hLind : IsProgressiveL2 P ℱ ind := by
    rw [hind]; exact s52_isProgressiveL2_ite hL measurableSet_Ioc
  have hcong := itoIntegral_congr hW hLg hLind (fun T => by
    unfold sqIntegralOn
    have hz : ∀ᵐ r ∂(volume.restrict (Set.Icc 0 T)), r ≠ 0 := ae_restrict_of_ae s52_ae_ne_zero
    have hz3 : ∀ᵐ r ∂(volume.restrict (Set.Icc 0 T)), r ∈ Set.Icc 0 T :=
      ae_restrict_mem measurableSet_Icc
    have hz2 : ∀ ω, ∫⁻ r in Set.Icc 0 T, ∑ k, ‖(g r ω - ind r ω) k‖ₑ ^ 2 = 0 := by
      intro ω
      rw [lintegral_congr_ae (g := fun _ => 0)]
      · simp
      · filter_upwards [hz, hz3] with r h1 h2
        have hr : 0 < r := lt_of_le_of_ne h2.1 (Ne.symm h1)
        have : g r ω = ind r ω := by
          rw [hind]; simp only [hg]
          by_cases hrt : r ≤ t
          · simp [hrt, hr]
          · simp [hrt]
        simp [this]
    exact (lintegral_congr hz2).trans lintegral_zero)
  have hI := itoIntegral_indicator_Ioc hW hL (le_refl 0) ht
  filter_upwards [hcong, hI] with ω h1 h2 τ hτ
  have e1 := h1 τ
  have e2 := h2 τ
  have h0 : itoIntegral P ℱ W u (min τ 0) ω = 0 :=
    itoIntegral_of_nonpos _ _ _ _ (min_le_right _ _) ω
  rw [h0, sub_zero] at e2
  exact e1.trans e2

/-- Integrands that agree on `[0,t]` (for every `ω`) have almost surely equal integrals at the times `min τ t`. -/
lemma s52_lc (hW : IsBrownianFiltration P ℱ W) {u u' : ℝ → Ω → ι → ℝ}
    (hu : IsProgressiveL2 P ℱ u) (hu' : IsProgressiveL2 P ℱ u') {t : ℝ} (ht : 0 ≤ t)
    (heq : ∀ r ∈ Set.Icc (0 : ℝ) t, ∀ ω, u r ω = u' r ω) :
    ∀ᵐ ω ∂P, ∀ τ : ℝ, 0 ≤ τ →
      itoIntegral P ℱ W u (min τ t) ω = itoIntegral P ℱ W u' (min τ t) ω := by
  classical
  have hg : IsProgressiveL2 P ℱ (fun r ω k => if r ≤ t then u r ω k else 0) := by
    have := s52_isProgressiveL2_ite hu (measurableSet_Iic (a := t))
    simpa using this
  have hg' : IsProgressiveL2 P ℱ (fun r ω k => if r ≤ t then u' r ω k else 0) := by
    have := s52_isProgressiveL2_ite hu' (measurableSet_Iic (a := t))
    simpa using this
  have hcong := itoIntegral_congr hW hg hg' (fun T => by
    unfold sqIntegralOn
    have hz3 : ∀ᵐ r ∂(volume.restrict (Set.Icc 0 T)), r ∈ Set.Icc 0 T :=
      ae_restrict_mem measurableSet_Icc
    have hz2 : ∀ ω, ∫⁻ r in Set.Icc 0 T, ∑ k, ‖((fun r ω k => if r ≤ t then u r ω k else 0) r ω -
        (fun r ω k => if r ≤ t then u' r ω k else 0) r ω) k‖ₑ ^ 2 = 0 := by
      intro ω
      rw [lintegral_congr_ae (g := fun _ => 0)]
      · simp
      · filter_upwards [hz3] with r h2
        by_cases hrt : r ≤ t
        · have := heq r ⟨h2.1, hrt⟩ ω
          simp [hrt, this]
        · simp [hrt]
    exact (lintegral_congr hz2).trans lintegral_zero)
  filter_upwards [hcong, s52_kill hW hu ht, s52_kill hW hu' ht] with ω h1 h2 h3 τ hτ
  rw [← h2 τ hτ, ← h3 τ hτ]
  exact h1 τ

end Kill

end HRS.MS.S52
