import HRS.MS.S113X2A2g

/-!
# S11.3 X2 part A2h: pointwise equation for a smooth density satisfying the weak equation
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S113X2

open HRS HRS.Whole

variable {d N : ℕ}

theorem s113a_config_decomp (x : EucConfig d N) :
    x = ∑ k : Fin N × Fin d, x k.1 k.2 • HRS.configBasis d N k := by
  funext i
  ext j
  simp only [Finset.sum_apply, PiLp.smul_apply, smul_eq_mul, HRS.configBasis, Fintype.sum_prod_type, Pi.single_apply]
  rw [Finset.sum_eq_single i]
  · simp [Pi.single_apply, EuclideanSpace.single_apply]
  · intro a _ ha
    simp [Ne.symm ha]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem s113a_fderiv_vec (Φ : ℝ × EucConfig d N → ℝ) (p : ℝ × EucConfig d N) (b : EucConfig d N) :
    fderiv ℝ Φ p (0, b) = ∑ k : Fin N × Fin d, b k.1 k.2 * fderiv ℝ Φ p (0, HRS.configBasis d N k) := by
  have : ((0 : ℝ), b) = ∑ k : Fin N × Fin d, b k.1 k.2 • ((0 : ℝ), HRS.configBasis d N k) := by
    refine Prod.ext ?_ ?_
    · simp [Prod.fst_sum]
    · simp only [Prod.snd_sum, Prod.smul_snd]
      exact s113a_config_decomp b
  conv_lhs => rw [this]
  rw [map_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [map_smul, smul_eq_mul]

theorem s113a_fderiv2_zero_off {Φ : ℝ × EucConfig d N → ℝ} {p : ℝ × EucConfig d N}
    (hp : p ∉ tsupport Φ) : fderiv ℝ Φ p = 0 ∧ fderiv ℝ (fderiv ℝ Φ) p = 0 := by
  have h0 : Φ =ᶠ[𝓝 p] fun _ => 0 := by
    filter_upwards [(isClosed_tsupport Φ).isOpen_compl.mem_nhds hp] with q hq
    exact image_eq_zero_of_notMem_tsupport hq
  have h1 : fderiv ℝ Φ =ᶠ[𝓝 p] fun _ => 0 := by
    filter_upwards [h0.eventuallyEq_nhds] with q hq
    simpa using hq.fderiv_eq
  exact ⟨by simpa using h0.fderiv_eq, by simpa using h1.fderiv_eq⟩

theorem s113a_cdo_fderiv_apply {O : Set (ℝ × EucConfig d N)} (hO : IsOpen O) {G : ℝ × EucConfig d N → ℝ}
    (hG : ContDiffOn ℝ ∞ G O) (v : ℝ × EucConfig d N) :
    ContDiffOn ℝ ∞ (fun p => fderiv ℝ G p v) O :=
  (hG.fderiv_of_isOpen hO (by simp)).clm_apply contDiffOn_const

/-- **Pointwise equation.**  A smooth function `F` on an open `O` with `∫ F · LΦ = 0` for all `Φ ∈ C_c^∞(O)` satisfies
`∂ₜF = c ΔF - div(bF)` on `O`. -/
theorem s113a_pde_of_weak {O : Set (ℝ × EucConfig d N)} (hO : IsOpen O) {F : ℝ × EucConfig d N → ℝ}
    (hF : ContDiffOn ℝ ∞ F O) {b : ℝ × EucConfig d N → EucConfig d N}
    (hb : ContDiffOn ℝ ∞ b O) {c : ℝ}
    (hweak : ∀ Φ : ℝ × EucConfig d N → ℝ, ContDiff ℝ ∞ Φ → HasCompactSupport Φ → tsupport Φ ⊆ O →
      ∫ p, F p * HRS.MC.CepP3.Lop c b Φ p = 0) :
    ∀ p ∈ O, fderiv ℝ F p (1, 0) =
      c * ∑ k : Fin N × Fin d, fderiv ℝ (fderiv ℝ F) p (0, HRS.configBasis d N k) (0, HRS.configBasis d N k) -
        ∑ k : Fin N × Fin d, fderiv ℝ (fun q => F q * b q k.1 k.2) p (0, HRS.configBasis d N k) := by
  haveI : (volume : Measure (ℝ × EucConfig d N)).IsAddHaarMeasure := HRS.MC.CepP3.isAddHaar_volume_cov
  set e : Fin N × Fin d → EucConfig d N := HRS.configBasis d N with he
  have hbc : ∀ k : Fin N × Fin d, ContDiffOn ℝ ∞ (fun q => b q k.1 k.2) O := fun k => by
    have h1 : ContDiffOn ℝ ∞ (fun q => b q k.1) O := contDiffOn_pi.1 hb k.1
    exact (EuclideanSpace.proj k.2).contDiff.comp_contDiffOn h1
  have hG : ∀ k : Fin N × Fin d, ContDiffOn ℝ ∞ (fun q => F q * b q k.1 k.2) O := fun k => hF.mul (hbc k)
  -- the integrated identity
  set R : ℝ × EucConfig d N → ℝ := fun p => -fderiv ℝ F p (1, 0) +
    c * ∑ k : Fin N × Fin d, fderiv ℝ (fderiv ℝ F) p (0, e k) (0, e k) -
      ∑ k : Fin N × Fin d, fderiv ℝ (fun q => F q * b q k.1 k.2) p (0, e k) with hR
  have t1 : ContinuousOn (fun p => fderiv ℝ F p (1, 0)) O := (s113a_cdo_fderiv_apply hO hF _).continuousOn
  have h2F : ContDiffOn ℝ ∞ (fderiv ℝ F) O := hF.fderiv_of_isOpen hO (by simp)
  have h3F : ContDiffOn ℝ ∞ (fderiv ℝ (fderiv ℝ F)) O := h2F.fderiv_of_isOpen hO (by simp)
  have t2 : ∀ k : Fin N × Fin d, ContinuousOn (fun p => fderiv ℝ (fderiv ℝ F) p (0, e k) (0, e k)) O := fun k =>
    ((h3F.clm_apply contDiffOn_const).clm_apply contDiffOn_const).continuousOn
  have t3 : ∀ k : Fin N × Fin d, ContinuousOn (fun p => fderiv ℝ (fun q => F q * b q k.1 k.2) p (0, e k)) O :=
    fun k => (s113a_cdo_fderiv_apply hO (hG k) _).continuousOn
  have hRc : ContinuousOn R O :=
    ((t1.neg).add ((continuousOn_const.mul (continuousOn_finsetSum _ fun k _ => t2 k)))).sub
      (continuousOn_finsetSum _ fun k _ => t3 k)
  have hmain : ∀ Φ : ℝ × EucConfig d N → ℝ, ContDiff ℝ ∞ Φ → HasCompactSupport Φ → tsupport Φ ⊆ O →
      ∫ p, Φ p • R p = 0 := by
    intro Φ hΦ hc hs
    have hΦ1 : ContDiff ℝ 1 Φ := hΦ.of_le (by simp)
    have hDD : ContDiff ℝ ∞ (fderiv ℝ Φ) := hΦ.fderiv_right (by simp)
    have hD1 : Continuous (fderiv ℝ Φ) := hΦ.continuous_fderiv (by simp)
    have hD2 : Continuous (fderiv ℝ (fderiv ℝ Φ)) := hDD.continuous_fderiv (by simp)
    have hzf : ∀ p, p ∉ tsupport Φ → fderiv ℝ Φ p = 0 ∧ fderiv ℝ (fderiv ℝ Φ) p = 0 := fun p hp =>
      s113a_fderiv2_zero_off hp
    have hΦz : ∀ p, p ∉ tsupport Φ → Φ p = 0 := fun p hp => image_eq_zero_of_notMem_tsupport hp
    have intO : ∀ (h φ' : ℝ × EucConfig d N → ℝ), ContinuousOn h O → Continuous φ' →
        (∀ p, p ∉ tsupport Φ → φ' p = 0) → Integrable (fun p => h p * φ' p) :=
      fun h φ' hh hφ' hzφ => s113a_integrable_of_compact hc.isCompact ((hh.mono hs).mul hφ'.continuousOn)
        (fun p hp => by simp [hzφ p hp])
    have hFc : ContinuousOn F O := hF.continuousOn
    have hD1c : ∀ v : ℝ × EucConfig d N, Continuous (fun p => fderiv ℝ Φ p v) := fun v =>
      hD1.clm_apply continuous_const
    have hD1z : ∀ (v : ℝ × EucConfig d N) p, p ∉ tsupport Φ → fderiv ℝ Φ p v = 0 := fun v p hp => by
      simp [(hzf p hp).1]
    have hD2c : ∀ v : ℝ × EucConfig d N, Continuous (fun p => fderiv ℝ (fderiv ℝ Φ) p v v) := fun v =>
      (hD2.clm_apply continuous_const).clm_apply continuous_const
    have hD2z : ∀ (v : ℝ × EucConfig d N) p, p ∉ tsupport Φ → fderiv ℝ (fderiv ℝ Φ) p v v = 0 := fun v p hp => by
      simp [(hzf p hp).2]
    -- integration by parts, three families
    have ibp1 : ∫ p, F p * fderiv ℝ Φ p (1, 0) = -∫ p, fderiv ℝ F p (1, 0) * Φ p :=
      s113a_ibp' hO (hF.of_le (by simp)) hΦ1 hc hs
    have ibp2 : ∀ k : Fin N × Fin d, ∫ p, F p * fderiv ℝ (fderiv ℝ Φ) p (0, e k) (0, e k) =
        ∫ p, fderiv ℝ (fderiv ℝ F) p (0, e k) (0, e k) * Φ p := by
      intro k
      set v : ℝ × EucConfig d N := (0, e k) with hv
      have hg1 : ContDiff ℝ 1 (fun q => fderiv ℝ Φ q v) :=
        (hDD.of_le (by simp)).clm_apply contDiff_const
      have step1 := s113a_ibp' hO (G := F) (v := v) (hF.of_le (by simp)) hg1 (hc.fderiv_apply ℝ v)
        ((tsupport_fderiv_apply_subset ℝ v).trans hs)
      have e1 : ∀ p, fderiv ℝ (fun q => fderiv ℝ Φ q v) p v = fderiv ℝ (fderiv ℝ Φ) p v v := fun p =>
        s113a_fderiv_clm_const (hDD.differentiable (by simp) p) v v
      simp only [e1] at step1
      have hG2 : ContDiffOn ℝ 1 (fun p => fderiv ℝ F p v) O :=
        (s113a_cdo_fderiv_apply hO hF v).of_le (by simp)
      have step2 := s113a_ibp' hO (G := fun p => fderiv ℝ F p v) (v := v) hG2 hΦ1 hc hs
      have e2 : ∀ p ∈ O, fderiv ℝ (fun q => fderiv ℝ F q v) p v = fderiv ℝ (fderiv ℝ F) p v v := fun p hp =>
        s113a_fderiv_clm_const ((h2F.contDiffAt (hO.mem_nhds hp)).differentiableAt (by simp)) v v
      have e3 : ∫ p, fderiv ℝ (fun q => fderiv ℝ F q v) p v * Φ p =
          ∫ p, fderiv ℝ (fderiv ℝ F) p v v * Φ p := by
        refine integral_congr_ae (ae_of_all _ fun p => ?_)
        by_cases hp : p ∈ O
        · simp only [e2 p hp]
        · have : p ∉ tsupport Φ := fun h => hp (hs h)
          simp [hΦz p this]
      rw [step1]
      have : ∫ p, fderiv ℝ F p v * fderiv ℝ Φ p v = ∫ p, fderiv ℝ F p v * fderiv ℝ Φ p v := rfl
      rw [step2, e3]
      ring
    have ibp3 : ∀ k : Fin N × Fin d, ∫ p, (F p * b p k.1 k.2) * fderiv ℝ Φ p (0, e k) =
        -∫ p, fderiv ℝ (fun q => F q * b q k.1 k.2) p (0, e k) * Φ p := fun k =>
      s113a_ibp' hO (hG k |>.of_le (by simp)) hΦ1 hc hs
    -- integrabilities
    have iA : Integrable (fun p => fderiv ℝ F p (1, 0) * Φ p) :=
      intO _ Φ t1 hΦ.continuous hΦz
    have iB : ∀ k : Fin N × Fin d, Integrable (fun p => fderiv ℝ (fderiv ℝ F) p (0, e k) (0, e k) * Φ p) :=
      fun k => intO _ Φ (t2 k) hΦ.continuous hΦz
    have iC : ∀ k : Fin N × Fin d, Integrable (fun p => fderiv ℝ (fun q => F q * b q k.1 k.2) p (0, e k) * Φ p) :=
      fun k => intO _ Φ (t3 k) hΦ.continuous hΦz
    have iT1 : Integrable (fun p => F p * fderiv ℝ Φ p (1, 0)) :=
      intO _ _ hFc (hD1c _) (hD1z _)
    have iT2 : ∀ k : Fin N × Fin d, Integrable (fun p => F p * fderiv ℝ (fderiv ℝ Φ) p (0, e k) (0, e k)) :=
      fun k => intO _ _ hFc (hD2c _) (hD2z _)
    have iT3 : ∀ k : Fin N × Fin d, Integrable (fun p => (F p * b p k.1 k.2) * fderiv ℝ Φ p (0, e k)) :=
      fun k => intO _ _ (hG k).continuousOn (hD1c _) (hD1z _)
    -- expand the weak identity
    have hexp : ∀ p, F p * HRS.MC.CepP3.Lop c b Φ p = F p * fderiv ℝ Φ p (1, 0) +
        c * ∑ k : Fin N × Fin d, F p * fderiv ℝ (fderiv ℝ Φ) p (0, e k) (0, e k) +
        ∑ k : Fin N × Fin d, (F p * b p k.1 k.2) * fderiv ℝ Φ p (0, e k) := by
      intro p
      unfold HRS.MC.CepP3.Lop
      rw [s113a_fderiv_vec Φ p (b p)]
      simp only [he, Finset.mul_sum, mul_add]
      refine congrArg₂ (· + ·) (congrArg₂ (· + ·) rfl (Finset.sum_congr rfl fun k _ => by ring))
        (Finset.sum_congr rfl fun k _ => by ring)
    have hw := hweak Φ hΦ hc hs
    simp only [hexp] at hw
    have hs2 : Integrable (fun p => c * ∑ k : Fin N × Fin d, F p * fderiv ℝ (fderiv ℝ Φ) p (0, e k) (0, e k)) :=
      (integrable_finset_sum _ fun k _ => iT2 k).const_mul c
    have hs3 : Integrable (fun p => ∑ k : Fin N × Fin d, (F p * b p k.1 k.2) * fderiv ℝ Φ p (0, e k)) :=
      integrable_finset_sum _ fun k _ => iT3 k
    have hs12 : Integrable (fun p => F p * fderiv ℝ Φ p (1, 0) +
        c * ∑ k : Fin N × Fin d, F p * fderiv ℝ (fderiv ℝ Φ) p (0, e k) (0, e k)) := iT1.add hs2
    rw [integral_add hs12 hs3, integral_add iT1 hs2, integral_const_mul,
      integral_finset_sum _ fun k _ => iT2 k, integral_finset_sum _ fun k _ => iT3 k] at hw
    simp only [ibp1, ibp2, ibp3] at hw
    have hR2 : ∀ p, Φ p • R p = -(fderiv ℝ F p (1, 0) * Φ p) +
        c * ∑ k : Fin N × Fin d, fderiv ℝ (fderiv ℝ F) p (0, e k) (0, e k) * Φ p -
          ∑ k : Fin N × Fin d, fderiv ℝ (fun q => F q * b q k.1 k.2) p (0, e k) * Φ p := by
      intro p
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      simp only [hR, smul_eq_mul]
      ring
    simp only [hR2]
    have hAn : Integrable (fun p => -(fderiv ℝ F p (1, 0) * Φ p)) := iA.neg
    have hB' : Integrable (fun p => c * ∑ k : Fin N × Fin d, fderiv ℝ (fderiv ℝ F) p (0, e k) (0, e k) * Φ p) :=
      (integrable_finset_sum _ fun k _ => iB k).const_mul c
    have hAB : Integrable (fun p => -(fderiv ℝ F p (1, 0) * Φ p) +
        c * ∑ k : Fin N × Fin d, fderiv ℝ (fderiv ℝ F) p (0, e k) (0, e k) * Φ p) := hAn.add hB'
    rw [integral_sub hAB (integrable_finset_sum _ fun k _ => iC k), integral_add hAn hB',
      integral_neg, integral_const_mul, integral_finset_sum _ fun k _ => iB k,
      integral_finset_sum _ fun k _ => iC k]
    rw [Finset.sum_neg_distrib] at hw
    linarith
  have hae := hO.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (hRc.locallyIntegrableOn hO.measurableSet) hmain
  have hae' : R =ᵐ[volume.restrict O] fun _ => 0 := by
    rw [Filter.EventuallyEq, ae_restrict_iff' hO.measurableSet]
    filter_upwards [hae] with p h1 h2 using h1 h2
  have := Measure.eqOn_open_of_ae_eq hae' hO hRc continuousOn_const
  intro p hp
  have hp0 := this hp
  simp only [hR] at hp0
  linarith

end HRS.MS.S113X2

end
