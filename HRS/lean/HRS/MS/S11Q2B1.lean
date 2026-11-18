import HRS.MS.S11Q2A3
import HRS.MS.S113X2C13

/-!
# S11.3 Q-regularity (worker S11Q2), B1: the weak QReg core and the integrated chain inequality in configuration coordinates

* `s11q2_QReg`, `S11Q2QReg`: the moving reference only needs to be of class `C^{1,2}` (`s113q_C12`) and positive on `[0,T+1]`;
  the core is stated for tuples with the hypotheses `hNL`, `hf0`, `hρ` of `s113c_Q_facts`.
* `s11q2_R_eq`: copy of `s113c_R_eq` (the source in `ℝ^{Nd}` coordinates) for such a reference.
* `s11q2_chain_conf`: copy of `s113c_chain_conf` with `s11q2_chain_ac`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory intervalIntegral
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S11Q2

open HRS HRS.Whole HRS.MS.S113X2 HRS.MS.S113X2B HRS.MS.S113X2C HRS.MS.S113Q
open HRS.MC.CepP3 (Jc Jc_single fderiv2_comp_clm)
open HRS.MS.S113BD (s113x_source)

variable {d N : ℕ}

/-- Spatial `C²` regularity of a `C^{1,2}` function. -/
theorem s11q2_spatial_contDiff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {Q : ℝ × E → ℝ}
    {d1 : ℝ × E → ℝ} {d2 : ℝ × E → E →L[ℝ] ℝ} {d3 : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ}
    (h : s113q_C12Data Q d1 d2 d3) (τ : ℝ) : ContDiff ℝ 2 (fun y : E => Q (τ, y)) := by
  have e2 : ContDiff ℝ 1 (fun y : E => d2 (τ, y)) := by
    have : ContDiff ℝ ((0 : ℕ) + 1) (fun y : E => d2 (τ, y)) :=
      contDiff_succ_iff_hasFDerivAt.2 ⟨fun y => d3 (τ, y), contDiff_zero.2 (h.c3.comp (continuous_const.prodMk continuous_id)),
        fun y => h.h3 (τ, y)⟩
    exact this
  have : ContDiff ℝ ((1 : ℕ) + 1) (fun y : E => Q (τ, y)) :=
    contDiff_succ_iff_hasFDerivAt.2 ⟨fun y => d2 (τ, y), e2, fun y => h.h2 (τ, y)⟩
  exact this

/-- The data of the moving reference in `ℝ^{Nd}` coordinates on a compact set `K` (weak form of `s113c_QReg`): an open set `G' ⊇ Jc⁻¹ K`
and a space-time function `q̃` of class `C^{1,2}`, positive on `[0,T+1]`, agreeing with `movQDensity (ρ t) ∘ Jc` on `G'` for
`t ∈ [0,T+1]`. -/
structure s11q2_QReg (d N : ℕ) (s β : ℝ) (ρ : ℝ → Euc d → ℝ) (T : ℝ) (K : Set (EucConfig d N))
    (qt : ℝ → s113b_E (N * d) → ℝ) (G' : Set (s113b_E (N * d))) : Prop where
  isOpen : IsOpen G'
  subset : ∀ z, Jc d N z ∈ K → z ∈ G'
  smooth : s113q_C12 (fun z : ℝ × s113b_E (N * d) => qt z.1 z.2)
  pos : ∀ t ∈ Icc (0 : ℝ) (T + 1), ∀ z, 0 < qt t z
  match_ : ∀ t ∈ Icc (0 : ℝ) (T + 1), ∀ z ∈ G', qt t z = movQDensity d s β N (ρ t) (Jc d N z)

/-- Core QREG (weak form): for a tuple with the hypotheses of `s113c_Q_facts`, the moving reference `q_N^t` is, near any compact
collision-free set and for `t ∈ [0,T+1]`, the restriction of a positive space-time function of class `C^{1,2}` on `ℝ × ℝ^{Nd}`. -/
def S11Q2QReg (d : ℕ) (s q β : ℝ) (ρ₀ : Euc d → ℝ) (j m : ℕ) (εstar r c₀ c C₁ : ℝ) : Prop :=
  2 ≤ d → 0 ≤ s → s < (d : ℝ) / 2 → 0 < β → 0 < q → IsThermalEquilibrium d s q β ρ₀ → 0 < C₁ → 0 < c₀ →
  MovNonlinearConclusion d s q β ρ₀ j m εstar r c₀ c C₁ →
  ∀ f0 : Euc d → ℝ, MovInitialClass ρ₀ j m εstar f0 →
    ∀ ρ : ℝ → Euc d → ℝ, MovInSmallClass d s q β ρ₀ m r c₀ f0 ρ →
    ∀ N : ℕ, 2 ≤ N → ∀ T : ℝ, 0 < T → ∀ K : Set (EucConfig d N), IsCompact K →
      (∀ x ∈ K, x ∉ eucCollisionSet d N) →
      ∃ (qt : ℝ → s113b_E (N * d) → ℝ) (G' : Set (s113b_E (N * d))), s11q2_QReg d N s β ρ T K qt G'


/-- **The source in `ℝ^{Nd}` coordinates.**  For a space-time density `q̃` of class `C²` agreeing with `movQDensity ∘ Jc` on
an open set `G'` for times in `[0,T+1]`, and a drift `b'` agreeing with the physical drift on an open set `G`:
`s113b_R (β⁻¹) b' q̃ τ z = s113x_source τ (Jc z)` for `z ∈ G ∩ G'` away from collisions and `τ ∈ [0,T]`. -/
theorem s11q2_R_eq (s q β : ℝ) {ρ : ℝ → Euc d → ℝ} {T : ℝ}
    {qt : ℝ → s113b_E (N * d) → ℝ} (hq : s113q_C12 (fun z : ℝ × s113b_E (N * d) => qt z.1 z.2))
    {G' : Set (s113b_E (N * d))} (hG' : IsOpen G')
    (hmatch : ∀ t ∈ Set.Icc (0 : ℝ) (T + 1), ∀ z ∈ G', qt t z = movQDensity d s β N (ρ t) (Jc d N z))
    {b' : s113b_E (N * d) → s113b_E (N * d)} {G : Set (s113b_E (N * d))} (hG : IsOpen G)
    (hb' : ∀ z ∈ G, b' z = s113c_bE d s q β N z)
    {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) T) {z : s113b_E (N * d)} (hzG : z ∈ G) (hzG' : z ∈ G')
    (hz : Jc d N z ∉ eucCollisionSet d N) :
    s113b_R β⁻¹ b' qt τ z = s113x_source d s q β N ρ τ (Jc d N z) := by
  have hτ1 : τ ∈ Set.Icc (0 : ℝ) (T + 1) := ⟨hτ.1, by linarith [hτ.2]⟩
  obtain ⟨d1, d2, d3, hdd⟩ := hq
  have hqτ : ContDiff ℝ 2 (qt τ) := s11q2_spatial_contDiff hdd τ
  have hFP := s113c_FP_E s q β (F := movQDensity d s β N (ρ τ)) hqτ hG' (fun w hw => hmatch τ hτ1 w hw) hG hb' hzG
    hzG' hz
  have hden : movQDensity d s β N (ρ τ) (Jc d N z) = qt τ z := (hmatch τ hτ1 z hzG').symm
  have hd : HasDerivAt (fun σ => qt σ z) (deriv (fun σ => qt σ z) τ) τ :=
    (hdd.h1 (τ, z)).differentiableAt.hasDerivAt
  have hev : (fun σ => qt σ z) =ᶠ[𝓝[Set.Ici τ] τ] fun σ => movQDensity d s β N (ρ σ) (Jc d N z) := by
    have hmem : Set.Icc τ (T + 1) ∈ 𝓝[Set.Ici τ] τ := Icc_mem_nhdsGE (by linarith [hτ.2])
    filter_upwards [hmem] with σ hσ
    exact hmatch σ ⟨hτ.1.trans hσ.1, hσ.2⟩ z hzG'
  have hdw : HasDerivWithinAt (fun σ => movQDensity d s β N (ρ σ) (Jc d N z)) (deriv (fun σ => qt σ z) τ)
      (Set.Ici τ) τ :=
    hd.hasDerivWithinAt.congr_of_eventuallyEq hev.symm (hmatch τ hτ1 z hzG').symm
  have htime := hdw.derivWithin (uniqueDiffWithinAt_Ici τ)
  unfold s113b_R s113x_source
  rw [if_neg hz, hFP, htime, hden]


theorem s11q2_chain_conf {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {s q β : ℝ} (hβ : 0 < β)
    {X₀ : Ω → EucConfig d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → EucConfig d N}
    (hX : MovParticleSetup P d s q β N X₀ W X)
    (D : Set (EucConfig d N)) (hD : IsOpen D) (hDc : IsCompact (closure D))
    (hDfree : closure D ⊆ (eucCollisionSet d N)ᶜ)
    (chi : EucConfig d N → ℝ) (hchi : Measurable chi) (hchi0 : ∀ z, 0 ≤ chi z) (hchi1 : ∀ z, chi z ≤ 1)
    {T : ℝ} (hT : 0 < T) {B : ℝ}
    (u : ℝ → EucConfig d N → ℝ) (hu0 : ∀ t x, 0 ≤ u t x) (hum : Measurable (Function.uncurry u))
    (huD : ∀ t x, x ∉ D → u t x = 0) (huB : ∀ t x, u t x ≤ B)
    (hdens : ∀ t ∈ Set.Icc (0 : ℝ) T, s113a_killedLaw P D X₀ X chi t.toNNReal =
      volume.withDensity (fun x => ENNReal.ofReal (u t x)))
    {ρ : ℝ → Euc d → ℝ} {qt : ℝ → s113b_E (N * d) → ℝ} {G' : Set (s113b_E (N * d))}
    (hQ : s11q2_QReg d N s β ρ T (closure D) qt G')
    {p : ℝ → ℝ} (hp : AbsolutelyContinuousOnInterval p 0 T) (hp1 : ∀ t ∈ Set.Icc (0 : ℝ) T, 1 < p t) :
    IntervalIntegrable (s113c_Gc d s q β N ρ u p) volume 0 T ∧
      ∀ s' t : ℝ, 0 ≤ s' → s' ≤ t → t ≤ T →
        s113c_Mc d s β N ρ u p t - s113c_Mc d s β N ρ u p s' ≤ ∫ τ in s'..t, s113c_Gc d s q β N ρ u p τ := by
  have hc := s113c_c_pos d N
  set c := s113c_c d N with hcdef
  -- the compact set and the cutoff
  set KE : Set (s113b_E (N * d)) := Jc d N ⁻¹' closure D with hKE
  have hKEc : IsCompact KE := ((Jc d N).toHomeomorph.isCompact_preimage).2 hDc
  set UE : Set (s113b_E (N * d)) := {z | Jc d N z ∉ eucCollisionSet d N} with hUE
  have hUEo : IsOpen UE := (s113a_isOpen_free d N).preimage (Jc d N).continuous
  have hKU : KE ⊆ UE := fun z hz => hDfree hz
  obtain ⟨θ, G, hθ, hθc, hθU, hθ01, hGo, hKG, hθG⟩ := s113c_cutoff hKEc hUEo hKU
  have hGfree : ∀ z ∈ G, Jc d N z ∉ eucCollisionSet d N := by
    intro z hz
    have h1 : θ z ≠ 0 := by rw [hθG z hz]; exact one_ne_zero
    exact hθU (subset_tsupport _ h1)
  set bt : s113b_E (N * d) → s113b_E (N * d) := fun z => θ z • s113c_bE d s q β N z with hbt
  have hbtG : ∀ z ∈ G, bt z = s113c_bE d s q β N z := fun z hz => by simp [hbt, hθG z hz]
  have hbtC : ContDiff ℝ 2 bt := s113c_btilde_contDiff s q β hθ hθU
  have hum' : ∀ t, Measurable (u t) := fun t => hum.comp (measurable_prodMk_left (x := t))
  set uE : ℝ → s113b_E (N * d) → ℝ := fun t z => u t (Jc d N z) with huE
  -- the Data
  have hData : s113q_Data β⁻¹ bt qt T uE KE G B := by
    refine ⟨inv_pos.2 hβ, hbtC, hQ.smooth, hQ.pos, hKEc, hGo, hKG, ?_, fun t x => hu0 _ _, fun t _ x => huB _ _, ?_, ?_⟩
    · intro t x hx
      exact huD t _ (fun h => hx (subset_closure h))
    · exact hum.comp (measurable_fst.prodMk ((Jc d N).continuous.measurable.comp measurable_snd))
    · exact s113c_sub' hβ hX D hD chi hchi hchi0 hchi1 u hu0 hum' hdens G hGfree bt hbtG
  -- pointwise identifications
  have hT0 : 0 ≤ T := hT.le
  have hmatch : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ z, uE τ z ≠ 0 → qt τ z = movQDensity d s β N (ρ τ) (Jc d N z) := by
    intro τ hτ z hne
    have hzD : Jc d N z ∈ D := by
      by_contra h
      exact hne (huD τ _ h)
    exact hQ.match_ τ ⟨hτ.1, by linarith [hτ.2]⟩ z (hQ.subset z (subset_closure hzD))
  have hMpt : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ z, qt τ z * (uE τ z / qt τ z) ^ (p τ) =
      movQDensity d s β N (ρ τ) (Jc d N z) * (u τ (Jc d N z) / movQDensity d s β N (ρ τ) (Jc d N z)) ^ (p τ) := by
    intro τ hτ z
    by_cases h0 : uE τ z = 0
    · have hp0 : p τ ≠ 0 := by linarith [hp1 τ hτ]
      have h0' : u τ (Jc d N z) = 0 := h0
      simp only [huE] at h0 ⊢
      rw [h0', zero_div, zero_div, Real.zero_rpow hp0]
      simp
    · rw [hmatch τ hτ z h0]
  have hMeq : ∀ t ∈ Set.Icc (0 : ℝ) T, s113b_M qt uE p t = c * s113c_Mc d s β N ρ u p t := by
    intro t ht
    unfold s113b_M s113c_Mc
    simp_rw [hMpt t ht]
    exact s113c_c_integral d N (fun x => movQDensity d s β N (ρ t) x * (u t x / movQDensity d s β N (ρ t) x) ^ (p t))
  have hGeq : ∀ τ ∈ Set.Icc (0 : ℝ) T, s113b_Gp β⁻¹ bt qt uE p τ = c * s113c_Gc d s q β N ρ u p τ := by
    intro τ hτ
    have hp0 : p τ ≠ 0 := by linarith [hp1 τ hτ]
    have h1 : ∀ z, qt τ z * s113b_R β⁻¹ bt qt τ z * (uE τ z / qt τ z) ^ (p τ) =
        (fun x => movQDensity d s β N (ρ τ) x * s113x_source d s q β N ρ τ x *
          (u τ x / movQDensity d s β N (ρ τ) x) ^ (p τ)) (Jc d N z) := by
      intro z
      by_cases h0 : uE τ z = 0
      · have h0' : u τ (Jc d N z) = 0 := h0
        simp only [huE] at h0 ⊢
        rw [h0', zero_div, zero_div, Real.zero_rpow hp0]
        simp
      · have hzD : Jc d N z ∈ D := by
          by_contra h
          exact h0 (huD τ _ h)
        have hzK : z ∈ KE := subset_closure hzD
        have hqe := hmatch τ hτ z h0
        have hR := s11q2_R_eq s q β (ρ := ρ) (T := T) hQ.smooth hQ.isOpen hQ.match_ hGo hbtG hτ (hKG hzK)
          (hQ.subset z (subset_closure hzD)) (hDfree (subset_closure hzD))
        simp only [huE]
        rw [hqe, hR]
    have h2 : ∀ z, qt τ z * (uE τ z / qt τ z) ^ (p τ) * Real.log (uE τ z / qt τ z) =
        (fun x => movQDensity d s β N (ρ τ) x * (u τ x / movQDensity d s β N (ρ τ) x) ^ (p τ) *
          Real.log (u τ x / movQDensity d s β N (ρ τ) x)) (Jc d N z) := by
      intro z
      by_cases h0 : uE τ z = 0
      · have h0' : u τ (Jc d N z) = 0 := h0
        simp only [huE] at h0 ⊢
        rw [h0', zero_div, zero_div, Real.zero_rpow hp0]
        simp
      · simp only [huE]
        rw [hmatch τ hτ z h0]
    unfold s113b_Gp s113c_Gc
    simp_rw [h1, h2]
    rw [s113c_c_integral d N (fun x => movQDensity d s β N (ρ τ) x * s113x_source d s q β N ρ τ x *
        (u τ x / movQDensity d s β N (ρ τ) x) ^ (p τ)),
      s113c_c_integral d N (fun x => movQDensity d s β N (ρ τ) x * (u τ x / movQDensity d s β N (ρ τ) x) ^ (p τ) *
        Real.log (u τ x / movQDensity d s β N (ρ τ) x))]
    ring
  -- the chain inequality
  obtain ⟨hGi, hchain⟩ := s11q2_chain_ac hData hT0 hp hp1
  refine ⟨?_, ?_⟩
  · -- integrability of `G_c`
    have hGi' : IntegrableOn (fun τ => c⁻¹ * s113b_Gp β⁻¹ bt qt uE p τ) (Ioc 0 T) :=
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hT0).1 hGi).const_mul c⁻¹
    refine (intervalIntegrable_iff_integrableOn_Ioc_of_le hT0).2 (hGi'.congr_fun (fun τ hτ => ?_) measurableSet_Ioc)
    simp only
    rw [hGeq τ ⟨hτ.1.le, hτ.2⟩]
    field_simp
  · intro s' t hs hst htT
    have h1 := hchain s' t hs hst htT
    have hs'I : s' ∈ Set.Icc (0 : ℝ) T := ⟨hs, hst.trans htT⟩
    have htI : t ∈ Set.Icc (0 : ℝ) T := ⟨hs.trans hst, htT⟩
    rw [hMeq t htI, hMeq s' hs'I] at h1
    have h2 : ∫ τ in s'..t, s113b_Gp β⁻¹ bt qt uE p τ = c * ∫ τ in s'..t, s113c_Gc d s q β N ρ u p τ := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun τ hτ => ?_
      rw [Set.uIcc_of_le hst] at hτ
      exact hGeq τ ⟨hs.trans hτ.1, hτ.2.trans htT⟩
    rw [h2] at h1
    nlinarith

end HRS.MS.S11Q2

end
