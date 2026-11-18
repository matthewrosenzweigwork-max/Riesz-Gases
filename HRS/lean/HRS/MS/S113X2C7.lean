import HRS.MS.S113X2C6

/-!
# S11.3 X2 wiring (worker S11W), C7: the integrated power chain inequality for the killed density

`s113c_chain_conf`: for a bounded domain `D` with closure in the collision-free set, the killed laws `ν_t` (`t ∈ [0,T]`) with
`ν_t ≤ B dx` (the Liouville bound, Pro D03), a `C²` reference `q̃` as in `s113c_QReg`, and an absolutely continuous exponent
`p > 1` on `[0,T]`: there is a density family `u` of the killed laws with
`M_c(t) - M_c(s') ≤ ∫_{s'}^t G_c` for `0 ≤ s' ≤ t ≤ T`, `G_c` interval integrable.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory intervalIntegral
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S113X2C

open HRS HRS.Whole HRS.MS.S113X2 HRS.MS.S113X2B
open HRS.MC.CepP3 (Jc Jc_single fderiv2_comp_clm)
open HRS.MS.S113BD (s113x_source)

variable {d N : ℕ}

theorem s113c_chain_conf {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
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
    (hQ : s113c_QReg d N s β ρ T (closure D) qt G')
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
  have hData : s113b_Data β⁻¹ bt qt T uE KE G B := by
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
        have hR := s113c_R_eq s q β (ρ := ρ) (T := T) hQ.smooth hQ.isOpen hQ.match_ hGo hbtG hτ (hKG hzK)
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
  have hchain := fun s' t (hs : 0 ≤ s') (hst : s' ≤ t) (htT : t ≤ T) => s113b_chain_ac hData hp hp1 hs hst htT
  have hGi := s113c_Gp_integrable hData hT0 hp hp1
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

end HRS.MS.S113X2C

end
