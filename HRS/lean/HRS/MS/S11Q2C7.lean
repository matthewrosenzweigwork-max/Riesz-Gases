import HRS.MS.S11Q2C6
import HRS.MS.S113X2Defs
import HRS.MS.S11Q2C2

/-!
# S11.3 Liouville (worker S11Q2), C7: the density bound for the killed law at a fixed time

`s11q2_liouville_t`: if the weighted initial killed law is at most `C0 dx`, then for every `t ∈ [0,T]` the killed law at time `t` is at most
`max C0 0 * (e^{2Lt})^{Nd} dx`, `L` the Lipschitz constant of the cut-off drift.  (No flow is constructed: the Euler maps of C5 are measurable in
`(x, noise)`, lower Lipschitz, and converge to the surviving paths; independence of `X₀` and the noise gives the product law.)
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal

namespace HRS.MS.S11Q2

open HRS HRS.Whole HRS.MS.S113X2

variable {d N : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- The weight of the initial condition in the killed law. -/
def s11q2_gw (D : Set (EucConfig d N)) (chi : EucConfig d N → ℝ) : EucConfig d N → ℝ≥0∞ :=
  D.indicator fun x => ENNReal.ofReal (chi x)

theorem s11q2_gw_measurable {D : Set (EucConfig d N)} (hD : MeasurableSet D) {chi : EucConfig d N → ℝ}
    (hchi : Measurable chi) : Measurable (s11q2_gw D chi) :=
  (ENNReal.measurable_ofReal.comp hchi).indicator hD

theorem s11q2_killedLaw_zero {P : Measure Ω} {X₀ : Ω → EucConfig d N} {X : ℝ≥0 → Ω → EucConfig d N}
    (hX0 : Measurable (X 0)) (hinit : X 0 =ᵐ[P] X₀) {D : Set (EucConfig d N)} (hD : MeasurableSet D)
    {chi : EucConfig d N → ℝ} (hchi : Measurable chi) :
    s113a_killedLaw P D X₀ X chi 0 = (P.map (X 0)).withDensity (s11q2_gw D chi) := by
  classical
  have hφ : (fun w => if w ∈ s113a_survives D X 0 then ENNReal.ofReal (chi (X₀ w)) else 0) =ᵐ[P]
      fun w => s11q2_gw D chi (X 0 w) := by
    filter_upwards [hinit] with w hw
    have hs : w ∈ s113a_survives D X 0 ↔ X 0 w ∈ D := by
      refine ⟨fun h => (h : ∀ r : ℝ≥0, r ≤ 0 → X r w ∈ D) 0 le_rfl, fun h r hr => ?_⟩
      rw [show r = 0 from le_antisymm hr (zero_le)]; exact h
    by_cases h : X 0 w ∈ D
    · rw [if_pos (hs.2 h)]; simp only [s11q2_gw, indicator_of_mem h]; rw [hw]
    · rw [if_neg (fun h' => h (hs.1 h'))]; simp [s11q2_gw, h]
  unfold s113a_killedLaw
  rw [withDensity_congr_ae hφ]
  ext A hA
  rw [Measure.map_apply hX0 hA, withDensity_apply _ (hX0 hA), withDensity_apply _ hA,
    setLIntegral_map hA (s11q2_gw_measurable hD hchi) hX0]

/-- The initial bound in terms of the law of `X 0`. -/
theorem s11q2_init_bound {P : Measure Ω} [IsProbabilityMeasure P] {X₀ : Ω → EucConfig d N} {X : ℝ≥0 → Ω → EucConfig d N}
    (hX0 : Measurable (X 0)) (hinit : X 0 =ᵐ[P] X₀) {D : Set (EucConfig d N)} (hD : MeasurableSet D)
    {chi : EucConfig d N → ℝ} (hchi : Measurable chi) {C0 : ℝ}
    (hC0 : s113a_killedLaw P D X₀ X chi 0 ≤ ENNReal.ofReal C0 • volume) {h : EucConfig d N → ℝ≥0∞} (hh : Measurable h) :
    ∫⁻ x, s11q2_gw D chi x * h x ∂(P.map (X 0)) ≤ ENNReal.ofReal C0 * ∫⁻ x, h x := by
  have h1 := lintegral_mono' hC0 (le_refl h)
  rw [s11q2_killedLaw_zero hX0 hinit hD hchi, lintegral_withDensity_eq_lintegral_mul _ (s11q2_gw_measurable hD hchi) hh,
    lintegral_smul_measure] at h1
  simpa [smul_eq_mul] using h1

theorem s11q2_killed_le {s q β : ℝ} {P : Measure Ω} [IsProbabilityMeasure P] {X₀ : Ω → EucConfig d N}
    {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → EucConfig d N} (hX : MovParticleSetup P d s q β N X₀ W X)
    {D : Set (EucConfig d N)} (hD : IsOpen D) {bt : EucConfig d N → EucConfig d N} {L M : ℝ} (hL0 : 0 ≤ L) (hM0 : 0 ≤ M)
    (hL : ∀ x y, ‖bt x - bt y‖ ≤ L * ‖x - y‖) (hM : ∀ x, ‖bt x‖ ≤ M) (hbc : Continuous bt)
    (hbD : ∀ x ∈ closure D, bt x = particleDriftW (quadraticGradientDyn d s q β) x)
    {chi : EucConfig d N → ℝ} (hchi : Measurable chi) {C0 : ℝ}
    (hC0 : s113a_killedLaw P D X₀ X chi 0 ≤ ENNReal.ofReal C0 • volume) {T t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    s113a_killedLaw P D X₀ X chi t.toNNReal ≤
      ENNReal.ofReal (max C0 0 * (Real.exp (2 * L * t)) ^ (Module.finrank ℝ (EucConfig d N))) • volume := by
  classical
  set Dyn := quadraticGradientDyn d s q β with hDyn
  set σ := Real.sqrt (2 * Dyn.invβ) with hσ
  have hsol := hX.sol T
  have hX0 : Measurable (X 0) := hsol.adapted 0
  have hXt : Measurable (X t.toNNReal) := hsol.adapted _
  have hinit : X 0 =ᵐ[P] X₀ := hsol.init
  set gw := s11q2_gw D chi with hgw
  have hgwm : Measurable gw := s11q2_gw_measurable hD.measurableSet hchi
  set S := s11q2_Sset bt σ t with hS
  set Fs := s11q2_Fs bt σ t with hFs
  have hSm : MeasurableSet S := s11q2_Sset_measurable hbc σ t
  have hFm : Measurable Fs := s11q2_Fs_measurable hbc σ t
  refine Measure.le_iff.2 fun A hA => ?_
  rw [Measure.smul_apply, smul_eq_mul]
  set Φ : EucConfig d N × (ℕ × ℕ → EucConfig d N) → ℝ≥0∞ := (S ∩ Fs ⁻¹' A).indicator (fun p => gw p.1) with hΦ
  have hΦm : Measurable Φ := (hgwm.comp measurable_fst).indicator (hSm.inter (hFm hA))
  -- Step 1: domination by a function of `(X 0, noise)`
  have hstep1 : s113a_killedLaw P D X₀ X chi t.toNNReal A ≤ ∫⁻ ω, Φ (X 0 ω, s11q2_Vq W t ω) ∂P := by
    unfold s113a_killedLaw
    rw [Measure.map_apply hXt hA, withDensity_apply _ (hXt hA), ← lintegral_indicator (hXt hA)]
    refine lintegral_mono_ae ?_
    filter_upwards [hinit, hsol.eqn, hsol.cont, s11q2_W_cont hX.brownian] with ω h0 heqn hcont hWc
    by_cases hA' : ω ∈ X t.toNNReal ⁻¹' A
    · by_cases hs : ω ∈ s113a_survives D X t.toNNReal
      · have hXc : Continuous fun r : ℝ≥0 => X r ω := continuous_pi hcont
        have hSol := s11q2_path_sol Dyn hL0 hM0 hL hM hbc hbD hXc hWc ht heqn hs
        have hv : ∀ i k : ℕ, σ • (s11q2_Vq W t ω (i + 1, k) - s11q2_Vq W t ω (i, k)) =
            (fun r : ℝ => σ • W r.toNNReal ω) (((i : ℝ) + 1) * (t / 2 ^ k)) -
              (fun r : ℝ => σ • W r.toNNReal ω) (i * (t / 2 ^ k)) := by
          intro i k
          simp only [s11q2_Vq, smul_sub]
          push_cast
          rfl
        obtain ⟨hSmem, hFeq⟩ := s11q2_Fs_sol hSol ht.1 σ hv
        have hX0D : X 0 ω ∈ D := (hs : ∀ r : ℝ≥0, r ≤ t.toNNReal → X r ω ∈ D) 0 (zero_le)
        simp only [Real.toNNReal_zero] at hSmem hFeq
        have hmem : (X 0 ω, s11q2_Vq W t ω) ∈ S ∩ Fs ⁻¹' A := ⟨hSmem, by
          show Fs (X 0 ω, s11q2_Vq W t ω) ∈ A
          show s11q2_Fs bt σ t (X 0 ω, s11q2_Vq W t ω) ∈ A
          rw [hFeq]; exact hA'⟩
        rw [indicator_of_mem hA', if_pos hs, hΦ, indicator_of_mem hmem]
        have hg : gw (X 0 ω) = ENNReal.ofReal (chi (X₀ ω)) := by
          show D.indicator (fun x => ENNReal.ofReal (chi x)) (X 0 ω) = _
          rw [indicator_of_mem hX0D, h0]
        exact hg.symm.le
      · rw [indicator_of_mem hA', if_neg hs]; exact zero_le
    · rw [indicator_of_notMem hA']; exact zero_le
  -- Step 2: product law
  have hind := s11q2_indep hX.indep hinit t
  have hVm := s11q2_Vq_aemeasurable hX.brownian t
  have hmap := hind.map_prod_eq_prod_map_map hX0.aemeasurable hVm
  have hstep2 : ∫⁻ ω, Φ (X 0 ω, s11q2_Vq W t ω) ∂P =
      ∫⁻ p, Φ p ∂((P.map (X 0)).prod (P.map (s11q2_Vq W t))) := by
    rw [← hmap, lintegral_map' hΦm.aemeasurable (hX0.aemeasurable.prodMk hVm)]
  set κ : ℝ≥0 := (Real.exp (-2 * L * t)).toNNReal with hκ
  have hκpos : 0 < κ := by
    rw [hκ]; exact Real.toNNReal_pos.2 (Real.exp_pos _)
  have hκe : ((κ⁻¹ : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal (Real.exp (2 * L * t)) := by
    rw [ENNReal.coe_inv hκpos.ne']
    rw [hκ, ← ENNReal.ofReal.eq_1, ← ENNReal.ofReal_inv_of_pos (Real.exp_pos _), ← Real.exp_neg]
    congr 2; ring
  -- Step 3: inner bound
  have hinner : ∀ v : ℕ × ℕ → EucConfig d N, ∫⁻ x, Φ (x, v) ∂(P.map (X 0)) ≤
      ENNReal.ofReal C0 * ((ENNReal.ofReal (Real.exp (2 * L * t))) ^ (Module.finrank ℝ (EucConfig d N)) * volume A) := by
    intro v
    set Sv : Set (EucConfig d N) := {x | (x, v) ∈ S ∩ Fs ⁻¹' A} with hSv
    have hSvm : MeasurableSet Sv := (hSm.inter (hFm hA)).preimage (measurable_id.prodMk measurable_const)
    have hΦv : ∀ x, Φ (x, v) = gw x * Sv.indicator (fun _ => (1 : ℝ≥0∞)) x := by
      intro x
      by_cases hx : x ∈ Sv
      · rw [hΦ, indicator_of_mem (show (x, v) ∈ S ∩ Fs ⁻¹' A from hx), indicator_of_mem hx]; simp
      · rw [hΦ, indicator_of_notMem (show (x, v) ∉ S ∩ Fs ⁻¹' A from hx), indicator_of_notMem hx]; simp
    simp_rw [hΦv]
    refine (s11q2_init_bound hX0 hinit hD.measurableSet hchi hC0 (measurable_const.indicator hSvm)).trans ?_
    rw [lintegral_indicator_const hSvm, one_mul]
    gcongr
    set S0 : Set (EucConfig d N) := {x | (x, v) ∈ S} with hS0
    have hSv' : Sv = S0 ∩ (fun x => Fs (x, v)) ⁻¹' A := by
      ext x; simp [hSv, hS0]
    rw [hSv', ← hκe]
    refine s11q2_vol_preimage volume hκpos (F := fun x => Fs (x, v)) (S := S0) (fun x hx x' hx' => ?_) A
    have := s11q2_Fs_lower hL0 hL σ ht.1 hx hx'
    rw [dist_eq_norm, dist_eq_norm]
    have hκc : (κ : ℝ) = Real.exp (-2 * L * t) := Real.coe_toNNReal _ (Real.exp_pos _).le
    rw [hκc]; exact this
  have hstep3 : ∫⁻ p, Φ p ∂((P.map (X 0)).prod (P.map (s11q2_Vq W t))) ≤
      ENNReal.ofReal C0 * ((ENNReal.ofReal (Real.exp (2 * L * t))) ^ (Module.finrank ℝ (EucConfig d N)) * volume A) := by
    rw [lintegral_prod_symm _ hΦm.aemeasurable]
    calc ∫⁻ v, ∫⁻ x, Φ (x, v) ∂(P.map (X 0)) ∂(P.map (s11q2_Vq W t)) ≤
        ∫⁻ v, ENNReal.ofReal C0 * ((ENNReal.ofReal (Real.exp (2 * L * t))) ^ (Module.finrank ℝ (EucConfig d N)) * volume A)
          ∂(P.map (s11q2_Vq W t)) := lintegral_mono hinner
      _ = _ := by simp
  refine hstep1.trans (hstep2.trans_le (hstep3.trans ?_))
  calc ENNReal.ofReal C0 * ((ENNReal.ofReal (Real.exp (2 * L * t))) ^ (Module.finrank ℝ (EucConfig d N)) * volume A) ≤
      ENNReal.ofReal (max C0 0) * ((ENNReal.ofReal (Real.exp (2 * L * t))) ^ (Module.finrank ℝ (EucConfig d N)) * volume A) := by
        gcongr; exact le_max_left _ _
    _ = _ := by
        rw [ENNReal.ofReal_mul (le_max_right _ _), ENNReal.ofReal_pow (Real.exp_pos _).le]; ring

end HRS.MS.S11Q2

end
