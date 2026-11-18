import HRS.MD.EQBurnBurnMain
import HRS.MD.EQAsmInit
import HRS.MD.EQGaussWindow
import HRS.MD.EQInterpWin
import HRS.Energy.StaticLimitCoupling
import HRS.MD.EQInitParticle
import HRS.MD.EQInitGauss
import HRS.Main.Headline

/-!
# Packet EQ-BURN P5 (chunk D): `eq_burnin_zero_proof`

Relocated proof of `HRS.MD.EQBurn.eq_burnin_zero` (frozen with its `sorry` in `HRS/MD/EQBurnSpec.lean`; the tie `HRS/MD/EQBurnZeroTie.lean`
checks that the statements agree).  Route: for `a ≥ 1` the flow has horizon `(a-1)+1`, P4 (`eq_burnin_of_evo_proof`) at window start `a-1` and
window length `1` gives the bounds for the windows of length `1`; the contraction `Φ = Cst ∘ ev₁ : C([0,1];E_m) → C([0,0];E_m)`
(`smoothDist_map_clm_le`, `wassersteinE_map_clm_le`) carries them to the windows of length `0`; the Gaussian side is moved from the
window start `1` to `0` by `eq_gauss_window_law_proof`.  For `a < 1`: `smoothDist ≤ 2` and `W₂ ≤ √(2Cp + 2Cg)` from the uniform second
moments of EQ-INITMOM, absorbed by `e^{c}e^{-ca} ≥ 1`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MD.EQBurnZero

open HRS HRS.LZ HRS.Uniform HRS.Main HRS.MD.EQAsmInit HRS.MD.EQ29 HRS.MD.EQBurn

variable {d : ℕ}

/-! ### The contraction `Φ : C([0,1];E_m) → C([0,0];E_m)` -/

/-- Evaluation at time `1` of a path on `[0,1]`. -/
def ebzEv1 (d : ℕ) (m : ℝ) : PathSpace d m 1 →L[ℝ] NegSobolev d m :=
  ContinuousMap.evalCLM ℝ (⟨1, zero_le_one, le_rfl⟩ : Set.Icc (0 : ℝ) 1)

/-- The endpoint evaluation followed by the constant path on `[0,0]`. -/
def ebzPhi (d : ℕ) (m : ℝ) : PathSpace d m 1 →L[ℝ] PathSpace d m 0 :=
  (eqiCst (d := d) m).comp (ebzEv1 d m)

theorem ebzEv1_norm_le (m : ℝ) : ‖ebzEv1 d m‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun w => by
    rw [one_mul]; exact ContinuousMap.norm_coe_le_norm w _

theorem eqiCst_norm_le (m : ℝ) : ‖(eqiCst (d := d) m)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun e => by
    rw [one_mul]
    exact (ContinuousMap.norm_le _ (norm_nonneg e)).2 fun t => le_rfl

theorem ebzPhi_norm_le (m : ℝ) : ‖ebzPhi d m‖ ≤ 1 := by
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  have h1 := eqiCst_norm_le (d := d) m
  have h2 := ebzEv1_norm_le (d := d) m
  nlinarith [norm_nonneg (eqiCst (d := d) m), norm_nonneg (ebzEv1 d m)]

theorem ebzPhi_apply (m : ℝ) (w : PathSpace d m 1) :
    ebzPhi d m w = eqiCst m (w.at' ⟨1, zero_le_one, le_rfl⟩) := rfl

/-! ### Pointwise identities -/

theorem ebz_windowZeta0 (m a : ℝ) {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} (P : Measure Ω)
    (X : ℝ≥0 → Ω → Config d N) (ω : Ω) :
    Main.windowZeta m 0 a P X ω =
      eqiCst m (zetaE m (P.map (X (Real.toNNReal (a + 0)))) (X (Real.toNNReal (a + 0)) ω)) := by
  unfold Main.windowZeta
  exact eqi_dite m _

theorem ebz_windowPath0 (m a : ℝ) {Ω : Type*} (Z : ℝ → Ω → NegSobolev d m) (ω : Ω) :
    Main.windowPath m 0 a Z ω = eqiCst m (Z (a + 0) ω) := by
  unfold Main.windowPath HRS.toPath
  exact eqi_dite m (fun t : Set.Icc (0 : ℝ) 0 => Z (a + (t : ℝ)) ω)

theorem ebz_Phi_windowZeta (m a : ℝ) {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} (P : Measure Ω)
    (X : ℝ≥0 → Ω → Config d N) (ω : Ω)
    (hc : Continuous fun τ : Set.Icc (0 : ℝ) 1 =>
      zetaE m (P.map (X (Real.toNNReal ((a - 1) + τ)))) (X (Real.toNNReal ((a - 1) + τ)) ω)) :
    ebzPhi d m (Main.windowZeta m 1 (a - 1) P X ω) = Main.windowZeta m 0 a P X ω := by
  rw [ebz_windowZeta0, ebzPhi_apply]
  have h := EQInterp.windowZeta_at' (m := m) (T := 1) (u := a - 1) P X ω hc ⟨1, zero_le_one, le_rfl⟩
  have e : (a - 1 + ((⟨1, zero_le_one, le_rfl⟩ : Set.Icc (0 : ℝ) 1) : ℝ)) = a + 0 := by
    show a - 1 + 1 = a + 0
    ring
  rw [e] at h
  rw [h]

theorem ebz_Phi_windowPath (m : ℝ) {Ω : Type*} (Z : ℝ → Ω → NegSobolev d m) (ω : Ω)
    (hc : ContinuousOn (fun t => Z t ω) (Set.Ici 0)) :
    ebzPhi d m (Main.windowPath m 1 0 Z ω) = Main.windowPath m 0 1 Z ω := by
  rw [ebz_windowPath0, ebzPhi_apply]
  have h := MD.EQGaussWindow.eqgw_windowPath_at (M := m) 1 0 le_rfl Z ω hc ⟨1, zero_le_one, le_rfl⟩
  rw [h]
  have e : (0 + ((⟨1, zero_le_one, le_rfl⟩ : Set.Icc (0 : ℝ) 1) : ℝ)) = 1 + 0 := by
    show (0 : ℝ) + 1 = 1 + 0
    ring
  rw [e]

/-! ### Laws -/

theorem ebz_law_zeta (m a : ℝ) {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} (P : Measure Ω)
    (X : ℝ≥0 → Ω → Config d N)
    (hae : AEMeasurable (Main.windowZeta m 1 (a - 1) P X) P)
    (hgood : ∀ᵐ ω ∂P, Continuous fun τ : Set.Icc (0 : ℝ) 1 =>
      zetaE m (P.map (X (Real.toNNReal ((a - 1) + τ)))) (X (Real.toNNReal ((a - 1) + τ)) ω)) :
    law P (Main.windowZeta m 0 a P X) = (law P (Main.windowZeta m 1 (a - 1) P X)).map (ebzPhi d m) := by
  unfold law
  rw [AEMeasurable.map_map_of_aemeasurable (ebzPhi d m).continuous.measurable.aemeasurable hae]
  refine Measure.map_congr ?_
  filter_upwards [hgood] with ω hω
  exact (ebz_Phi_windowZeta m a P X ω hω).symm

theorem ebz_law_path (m : ℝ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Z : ℝ → Ω → NegSobolev d m)
    (hae : AEMeasurable (Main.windowPath m 1 0 Z) P)
    (hgood : ∀ᵐ ω ∂P, ContinuousOn (fun t => Z t ω) (Set.Ici 0)) :
    law P (Main.windowPath m 0 1 Z) = (law P (Main.windowPath m 1 0 Z)).map (ebzPhi d m) := by
  unfold law
  rw [AEMeasurable.map_map_of_aemeasurable (ebzPhi d m).continuous.measurable.aemeasurable hae]
  refine Measure.map_congr ?_
  filter_upwards [hgood] with ω hω
  exact (ebz_Phi_windowPath m Z ω hω).symm

/-! ### Trivial bounds -/

theorem ebz_smoothDist_le_two {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [MeasurableSpace B]
    [BorelSpace B]
    (P Q : Measure B) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] : smoothDist 2 P Q ≤ 2 := by
  refine Real.iSup_le (fun Φ => ?_) (by norm_num)
  have hb : ∀ (ρ : Measure B) [IsProbabilityMeasure ρ], |∫ z, Φ.1 z ∂ρ| ≤ 1 := by
    intro ρ _
    have := norm_integral_le_of_norm_le_const (μ := ρ) (f := Φ.1) (C := 1)
      (Eventually.of_forall fun z => by simpa [Real.norm_eq_abs] using abs_apply_le_of_mem Φ.2 z)
    simpa using this
  have h1 := hb P
  have h2 := hb Q
  calc |∫ z, Φ.1 z ∂P - ∫ z, Φ.1 z ∂Q| ≤ |∫ z, Φ.1 z ∂P| + |∫ z, Φ.1 z ∂Q| := abs_sub _ _
    _ ≤ 2 := by linarith

theorem ebz_ofReal_sq {E : Type*} [NormedAddCommGroup E] (x : E) :
    ENNReal.ofReal (‖x‖ ^ 2) = ‖x‖ₑ ^ 2 := by
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

/-- `W₂` of two laws with second moments at most `A`, `B` is at most `√(2A + 2B)`. -/
theorem ebz_wass_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E] {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P] (P' : Measure Ω') [IsProbabilityMeasure P']
    (f : Ω → E) (g : Ω' → E) (hf : Measurable f) (hg : Measurable g) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hfA : ∫⁻ ω, ‖f ω‖ₑ ^ 2 ∂P ≤ ENNReal.ofReal A) (hgB : ∫⁻ ω, ‖g ω‖ₑ ^ 2 ∂P' ≤ ENNReal.ofReal B) :
    wassersteinE 2 (law P f) (law P' g) ≤ ENNReal.ofReal (Real.sqrt (2 * A + 2 * B)) := by
  haveI : IsProbabilityMeasure (law P f) := (Measure.isProbabilityMeasure_map_iff hf.aemeasurable).2 inferInstance
  haveI : IsProbabilityMeasure (law P' g) := (Measure.isProbabilityMeasure_map_iff hg.aemeasurable).2 inferInstance
  have h := HRS.StaticLimitAux.wassersteinE_two_le_common (0 : Measure E) (law P f) (law P' g) 1
    (by simp) (by simp)
  rw [zero_add, zero_add] at h
  refine h.trans ?_
  have e1 : ∫⁻ u, ENNReal.ofReal (‖u‖ ^ 2) ∂(law P f) = ∫⁻ ω, ‖f ω‖ₑ ^ 2 ∂P := by
    unfold law
    rw [lintegral_map (f := fun u : E => ENNReal.ofReal (‖u‖ ^ 2)) (ENNReal.measurable_ofReal.comp (measurable_norm.pow_const 2)) hf]
    exact lintegral_congr fun ω => ebz_ofReal_sq _
  have e2 : ∫⁻ u, ENNReal.ofReal (‖u‖ ^ 2) ∂(law P' g) = ∫⁻ ω, ‖g ω‖ₑ ^ 2 ∂P' := by
    unfold law
    rw [lintegral_map (f := fun u : E => ENNReal.ofReal (‖u‖ ^ 2)) (ENNReal.measurable_ofReal.comp (measurable_norm.pow_const 2)) hg]
    exact lintegral_congr fun ω => ebz_ofReal_sq _
  rw [e1, e2]
  have h3 : 2 * ∫⁻ ω, ‖f ω‖ₑ ^ 2 ∂P + 2 * ∫⁻ ω, ‖g ω‖ₑ ^ 2 ∂P' ≤ ENNReal.ofReal (2 * A + 2 * B) := by
    rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by norm_num),
      ENNReal.ofReal_mul (by norm_num)]
    simp only [ENNReal.ofReal_ofNat]
    gcongr
  calc _ ≤ (ENNReal.ofReal (2 * A + 2 * B)) ^ (1 / (2 : ℝ)) := ENNReal.rpow_le_rpow h3 (by norm_num)
    _ = ENNReal.ofReal (Real.sqrt (2 * A + 2 * B)) := by
        rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), ← Real.sqrt_eq_rpow]


/-! ### The theorem -/

theorem eq_burnin_zero_proof (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (βm βp : ℝ) (hβm : 0 < βm) (hββ : βm ≤ βp)
    (m : ℝ) (hm : max ((d : ℝ) + 1) ((d : ℝ) / 2 + 2) < m)
    (K c Cmax : ℝ) (hK : 0 ≤ K) (hc : 0 < c) (hCmax : 0 ≤ Cmax)
    (hevo : EvoPkg d s hs0 hsd V βm βp hβm m K c 1 Cmax) :
    BurninConcl d s hs0 hsd V βm βp hβm m 0 := by
  have hmd : (d : ℝ) / 2 + 2 < m := lt_of_le_of_lt (le_max_right _ _) hm
  have hm1 : (d : ℝ) + 1 < m := lt_of_le_of_lt (le_max_left _ _) hm
  have hmh : (d : ℝ) / 2 < m := by linarith
  have hm2 : (d : ℝ) < 2 * m := by linarith
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨C₁, c₁, hC₁, hc₁, h1⟩ := HRS.MD.EQBurnBurn.eq_burnin_of_evo_proof hd hs0 hsd V hV βm βp hβm hββ m hm
    1 one_pos K c Cmax hK hc hCmax hevo
  obtain ⟨Cp, hCp0, hinp⟩ := HRS.MD.EQInit.eq_init_particle_proof hd hs0 hsd V hV βm βp hβm hββ m hmh
  obtain ⟨Cg, hCg0, hing⟩ := HRS.MD.EQInit.eq_init_gauss_proof hd hs0 hsd V hV βm βp hβm hββ m hmh
  set S : ℝ := Real.sqrt (2 * Cp + 2 * Cg) with hSdef
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  have hec : 1 ≤ Real.exp c₁ := Real.one_le_exp hc₁.le
  set Cf : ℝ := C₁ * Real.exp c₁ + 2 * Real.exp c₁ + S * Real.exp c₁ with hCf
  have hCf0 : 0 < Cf := by
    have : 0 < C₁ * Real.exp c₁ := mul_pos hC₁ (Real.exp_pos _)
    have : 0 ≤ S * Real.exp c₁ := mul_nonneg hS0 (Real.exp_pos _).le
    have : 0 < 2 * Real.exp c₁ := by positivity
    linarith
  refine ⟨Cf, c₁, hCf0, hc₁, ?_⟩
  intro β hβ ρβ hρβ a ha N hN Ω _ P _ X₀ W X hX Ω' _ P' _ Z hZ
  have hβ0 : 0 < β := hβm.trans_le hβ.1
  have hδ0 : 0 ≤ deltaN d s N := deltaN_nonneg s (by omega)
  have hn0 : 0 ≤ (N : ℝ) ^ (-(1 : ℝ) / 4) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hexp0 : 0 ≤ Real.exp (-c₁ * a) := (Real.exp_pos _).le
  have hsq0 : 0 ≤ Real.sqrt (deltaN d s N) := Real.sqrt_nonneg _
  obtain ⟨hstat, hmeas, -⟩ := EQInterp.flow_facts hd hs0 hsd V hV hβ0 hN P hX
  have hG : IsProbabilityMeasure (canonicalGibbs (periodicRiesz d s) V N β) := by
    rw [← hstat 0 (by simp; positivity)]
    exact (Measure.isProbabilityMeasure_map_iff (hmeas 0).aemeasurable).2 inferInstance
  rcases lt_or_ge a 1 with ha1 | ha1
  · ------------------------------------------------------------ a < 1: trivial bounds
    have hE : 1 ≤ Real.exp c₁ * Real.exp (-c₁ * a) := by
      rw [← Real.exp_add]; apply Real.one_le_exp; nlinarith
    have hmap : P.map (X (Real.toNNReal (a + 0))) = canonicalGibbs (periodicRiesz d s) V N β :=
      hstat _ (by rw [Real.coe_toNNReal _ (by linarith)])
    obtain ⟨ζ, hζ⟩ : ∃ ζ : Ω → NegSobolev d m, ζ = fun ω =>
        zetaE m (canonicalGibbs (periodicRiesz d s) V N β) (X (Real.toNNReal (a + 0)) ω) := ⟨_, rfl⟩
    have hζm : Measurable ζ := by
      rw [hζ]
      exact (EQLawPath.eqlaw_continuous_zetaE hm2 (by omega) _).measurable.comp (hmeas _)
    have hI1 : ∫⁻ ω, ‖ζ ω‖ₑ ^ 2 ∂P ≤ ENNReal.ofReal Cp := by
      have := lintegral_map (μ := P) (f := fun x => ‖zetaE m (canonicalGibbs (periodicRiesz d s) V N β) x‖ₑ ^ 2)
        (g := X (Real.toNNReal (a + 0))) ((EQLawPath.eqlaw_continuous_zetaE hm2 (by omega) _).measurable.enorm.pow_const 2)
        (hmeas _)
      rw [hmap] at this
      rw [hζ]
      simp only []
      rw [← this]
      exact hinp β hβ ρβ hρβ N hN
    have hI2 := hing β hβ ρβ hρβ P' Z hZ
    haveI : IsProbabilityMeasure (law P ζ) := (Measure.isProbabilityMeasure_map_iff hζm.aemeasurable).2 inferInstance
    haveI : IsProbabilityMeasure (law P' (Z 0)) :=
      (Measure.isProbabilityMeasure_map_iff (hZ.meas 0).aemeasurable).2 inferInstance
    have e1 : law P (Main.windowZeta m 0 a P X) = (law P ζ).map (eqiCst m) := by
      unfold law
      rw [Measure.map_map (eqiCst (d := d) m).continuous.measurable hζm]
      refine Measure.map_congr (Eventually.of_forall fun ω => ?_)
      rw [ebz_windowZeta0, hmap, hζ]
      rfl
    have e2 : law P' (Main.windowPath m 0 0 Z) = (law P' (Z 0)).map (eqiCst m) := by
      unfold law
      rw [Measure.map_map (eqiCst (d := d) m).continuous.measurable (hZ.meas 0)]
      refine Measure.map_congr (Eventually.of_forall fun ω => ?_)
      exact eqi_windowPath m Z ω
    have hLm := (eqiCst (d := d) m).continuous.measurable
    haveI : IsProbabilityMeasure ((law P ζ).map (eqiCst (d := d) m)) :=
      (Measure.isProbabilityMeasure_map_iff hLm.aemeasurable).2 inferInstance
    haveI : IsProbabilityMeasure ((law P' (Z 0)).map (eqiCst (d := d) m)) :=
      (Measure.isProbabilityMeasure_map_iff hLm.aemeasurable).2 inferInstance
    rw [e1, e2]
    constructor
    · refine (ebz_smoothDist_le_two _ _).trans ?_
      have : 2 ≤ Cf * Real.exp (-c₁ * a) := by
        have h2 : 2 * Real.exp c₁ * Real.exp (-c₁ * a) ≥ 2 := by nlinarith
        have h3 : 2 * Real.exp c₁ * Real.exp (-c₁ * a) ≤ Cf * Real.exp (-c₁ * a) := by
          apply mul_le_mul_of_nonneg_right _ hexp0
          have : 0 ≤ C₁ * Real.exp c₁ := mul_nonneg hC₁.le (Real.exp_pos _).le
          have : 0 ≤ S * Real.exp c₁ := mul_nonneg hS0 (Real.exp_pos _).le
          linarith
        linarith
      nlinarith [mul_nonneg hCf0.le hsq0]
    · have hW := wassersteinE_map_clm_le (eqiCst (d := d) m) 2 (by norm_num) (law P ζ) (law P' (Z 0))
      refine hW.trans ?_
      have hn : ENNReal.ofReal ‖(eqiCst (d := d) m)‖ ≤ 1 := by
        rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (eqiCst_norm_le m)
      refine (mul_le_mul' hn le_rfl).trans ?_
      rw [one_mul]
      refine (ebz_wass_le P P' ζ (Z 0) hζm (hZ.meas 0) hCp0.le hCg0.le hI1 hI2).trans ?_
      refine ENNReal.ofReal_le_ofReal ?_
      have h3 : S ≤ Cf * Real.exp (-c₁ * a) := by
        have h4 : S ≤ S * Real.exp c₁ * Real.exp (-c₁ * a) := by nlinarith
        refine h4.trans ?_
        apply mul_le_mul_of_nonneg_right _ hexp0
        have : 0 ≤ C₁ * Real.exp c₁ := mul_nonneg hC₁.le (Real.exp_pos _).le
        have : 0 ≤ 2 * Real.exp c₁ := by positivity
        linarith
      nlinarith [mul_nonneg hCf0.le hn0, mul_nonneg hCf0.le hsq0]
  · ------------------------------------------------------------ a ≥ 1: P4 and the contraction
    have hu : 0 ≤ a - 1 := by linarith
    have hX' : IsStationaryGibbsFlow P s hs0 hsd V β hβ0 ((a - 1) + 1) X₀ W X := by
      have e : (a - 1) + 1 = a + 0 := by ring
      rw [e]; exact hX
    obtain ⟨h1a, h1b⟩ := h1 β hβ ρβ hρβ (a - 1) hu N hN P X₀ W X hX' P' Z hZ
    have hae := EQInterp.windowZeta_aemeasurable hd hs0 hsd V hV hβ0 hN hu zero_le_one P hX' hm2
    have hgood := EQInterp.windowZeta_cont_ae hd hs0 hsd V hV hβ0 hN hu zero_le_one P hX' hm2
    have haeG := (MD.EQGaussWindow.eqgw_fidi hd hs0 hsd V hβ0 ρβ m 1 P' Z hZ 0 le_rfl).1
    haveI : IsProbabilityMeasure (law P (Main.windowZeta m 1 (a - 1) P X)) :=
      (Measure.isProbabilityMeasure_map_iff hae).2 inferInstance
    haveI : IsProbabilityMeasure (law P' (Main.windowPath m 1 0 Z)) :=
      (Measure.isProbabilityMeasure_map_iff haeG).2 inferInstance
    have hL1 := ebz_law_zeta m a P X hae hgood
    have hL2 : law P' (Main.windowPath m 0 0 Z) = (law P' (Main.windowPath m 1 0 Z)).map (ebzPhi d m) := by
      rw [← ebz_law_path m P' Z haeG hZ.cont]
      exact (MD.EQGaussWindow.eq_gauss_window_law_proof hd hs0 hsd V hβ0 ρβ m 0 le_rfl P' P' Z Z hZ hZ 1 0
        zero_le_one le_rfl).symm
    rw [hL1, hL2]
    have hΦ := ebzPhi_norm_le (d := d) m
    have hexp : Real.exp (-c₁ * (a - 1)) = Real.exp c₁ * Real.exp (-c₁ * a) := by
      rw [← Real.exp_add]; congr 1; ring
    have hA : C₁ * Real.exp c₁ ≤ Cf := by
      have : 0 ≤ S * Real.exp c₁ := mul_nonneg hS0 (Real.exp_pos _).le
      have : 0 ≤ 2 * Real.exp c₁ := by positivity
      linarith
    have hC1 : C₁ ≤ Cf := by
      have : C₁ ≤ C₁ * Real.exp c₁ := le_mul_of_one_le_right hC₁.le hec
      linarith
    have key : ∀ x y z : ℝ, 0 ≤ x → 0 ≤ y → 0 ≤ z →
        C₁ * (Real.exp c₁ * x + y + z) ≤ Cf * (x + y + z) := by
      intro x y z hx hy hz
      have h1 := mul_le_mul_of_nonneg_right hA hx
      have h2 := mul_le_mul_of_nonneg_right hC1 hy
      have h3 := mul_le_mul_of_nonneg_right hC1 hz
      linarith
    constructor
    · have hsm := smoothDist_map_clm_le (ebzPhi d m) 2 (law P (Main.windowZeta m 1 (a - 1) P X))
        (law P' (Main.windowPath m 1 0 Z))
      have hmx : max 1 (‖ebzPhi d m‖ ^ 2) = 1 := max_eq_left (pow_le_one₀ (norm_nonneg _) hΦ)
      rw [hmx, one_mul] at hsm
      refine hsm.trans (h1a.trans ?_)
      rw [hexp]
      have := key (Real.exp (-c₁ * a)) 0 (Real.sqrt (deltaN d s N)) hexp0 le_rfl hsq0
      linarith
    · have hW := wassersteinE_map_clm_le (ebzPhi d m) 2 (by norm_num) (law P (Main.windowZeta m 1 (a - 1) P X))
        (law P' (Main.windowPath m 1 0 Z))
      refine hW.trans ?_
      have hn : ENNReal.ofReal ‖ebzPhi d m‖ ≤ 1 := by
        rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hΦ
      refine (mul_le_mul' hn le_rfl).trans ?_
      rw [one_mul]
      refine h1b.trans (ENNReal.ofReal_le_ofReal ?_)
      rw [hexp]
      exact key _ _ _ hexp0 hn0 hsq0


end HRS.MD.EQBurnZero

end
