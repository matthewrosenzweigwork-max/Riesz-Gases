import HRS.PDE.TorusFPExistAux17

/-!
# D1 existence, helper 18: right derivative of `s ↦ ∫ f_s dμ_s` and the time-dependent weak equation
-/

noncomputable section

open MeasureTheory Filter Topology

namespace HRS

variable {n : ℕ}

theorem d1_integrable_of_continuous (ρ : Measure (Torus n)) [IsFiniteMeasure ρ] {g : Torus n → ℝ}
    (hc : Continuous g) : Integrable g ρ :=
  hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

section TimeDepDeriv

variable (hn : 1 ≤ n) {κ : ℝ} (hκ : 0 < κ) {U : Torus n → ℝ} (hU : Torus.IsSmooth U)
  (μ₀ : Measure (Torus n)) [IsProbabilityMeasure μ₀]

local notation "μt" => d1_mu hn hκ hU μ₀

theorem d1_G_hasDerivWithinAt {τ : ℝ} (hτ : 0 < τ) {f ft : ℝ → Torus n → ℝ} (hf : IsC12Test τ f ft)
    {s : ℝ} (hs : s ∈ Set.Ico 0 τ) :
    HasDerivWithinAt (fun t => ∫ x, f t x ∂(μt t))
      (∫ x, (ft s x + d1_gen κ (d1_gradDrift U) (f s) x) ∂(μt s)) (Set.Ioi s) s := by
  have hsI : s ∈ Set.Icc 0 τ := ⟨hs.1, hs.2.le⟩
  have hfc : ∀ t ∈ Set.Icc 0 τ, Continuous (f t) := fun t ht => d1_continuous_of_isCk2 (hf.c2 t ht)
  have hfs2 : Torus.IsCk 2 (f s) := hf.c2 s hsI
  have hfts : ∀ t ∈ Set.Icc (0 : ℝ) τ, Continuous (ft t) := fun t ht =>
    hf.cont_time_deriv.comp (Continuous.prodMk continuous_const continuous_id :
      Continuous fun x : Torus n => ((⟨t, ht⟩ : Set.Icc (0 : ℝ) τ), x))
  have hLs : Continuous (d1_gen κ (d1_gradDrift U) (f s)) :=
    d1_gen_continuous (d1_gradDrift_continuous hU) hfs2
  have hmem : Set.Icc 0 τ ∈ 𝓝[Set.Ioi s] s :=
    Filter.mem_of_superset (Ioo_mem_nhdsGT hs.2) (fun r hr => ⟨by linarith [hs.1, hr.1], hr.2.le⟩)
  have hmem2 : Set.Ioo s τ ∈ 𝓝[Set.Ioi s] s := Ioo_mem_nhdsGT hs.2
  -- the three limits
  have hQ : Tendsto (fun t => ((∫ x, f s x ∂(μt t)) - ∫ x, f s x ∂(μt s)) / (t - s)) (𝓝[Set.Ioi s] s)
      (𝓝 (∫ x, d1_gen κ (d1_gradDrift U) (f s) x ∂(μt s))) := by
    have h := hasDerivWithinAt_iff_tendsto_slope.1
      (d1_hasDerivWithinAt_Ioi_C2 hn hκ hU μ₀ hfs2 hs.1)
    rw [show Set.Ioi s \ {s} = Set.Ioi s by simp] at h
    refine h.congr fun t => ?_
    rw [slope_def_field]
  have hN : Tendsto (fun t => ∫ x, ft s x ∂(μt t)) (𝓝[Set.Ioi s] s) (𝓝 (∫ x, ft s x ∂(μt s))) := by
    have := d1_narrow hn hκ hU μ₀ (hfts s hsI) τ s hsI
    exact this.tendsto.mono_left (nhdsWithin_le_of_mem hmem)
  have hE : Tendsto (fun t => ∫ x, ((f t x - f s x) / (t - s) - ft s x) ∂(μt t)) (𝓝[Set.Ioi s] s)
      (𝓝 0) := by
    rw [Metric.tendsto_nhdsWithin_nhds]
    intro ε hε
    obtain ⟨δ₀, hδ₀, hδ⟩ := d1_time_diff_quot hτ hf hsI (half_pos hε)
    refine ⟨min δ₀ (τ - s), lt_min hδ₀ (by linarith [hs.2]), fun t ht hdist => ?_⟩
    have hts : s < t := ht
    have hd1 : t - s < δ₀ := by
      have := lt_of_lt_of_le hdist (min_le_left _ _)
      rwa [Real.dist_eq, abs_of_pos (by linarith)] at this
    have hd2 : t - s < τ - s := by
      have := lt_of_lt_of_le hdist (min_le_right _ _)
      rwa [Real.dist_eq, abs_of_pos (by linarith)] at this
    have htI : t ∈ Set.Icc 0 τ := ⟨by linarith [hs.1], by linarith⟩
    have := d1_mu_prob hn hκ hU μ₀ t
    have hb : ∀ x, |((f t x - f s x) / (t - s) - ft s x) - 0| ≤ ε / 2 := by
      intro x
      have := hδ (t - s) (by linarith) hd1 (by linarith) x
      rw [show s + (t - s) = t by ring] at this
      simpa using this
    have hc : Continuous fun x => ((f t x - f s x) / (t - s) - ft s x) :=
      (((hfc t htI).sub (hfc s hsI)).div_const _).sub (hfts s hsI)
    have h2 := d1_abs_integral_sub_le (ρ := μt t) hc continuous_const hb
    simp only [integral_zero] at h2
    rw [Real.dist_eq, sub_zero]
    simpa using h2.trans_lt (half_lt_self hε)
  have hsum : Tendsto (fun t => (∫ x, ((f t x - f s x) / (t - s) - ft s x) ∂(μt t)) +
      (∫ x, ft s x ∂(μt t)) + ((∫ x, f s x ∂(μt t)) - ∫ x, f s x ∂(μt s)) / (t - s)) (𝓝[Set.Ioi s] s)
      (𝓝 (0 + (∫ x, ft s x ∂(μt s)) + ∫ x, d1_gen κ (d1_gradDrift U) (f s) x ∂(μt s))) :=
    (hE.add hN).add hQ
  rw [hasDerivWithinAt_iff_tendsto_slope]
  rw [show Set.Ioi s \ {s} = Set.Ioi s by simp]
  have hlim : (0 : ℝ) + (∫ x, ft s x ∂(μt s)) + ∫ x, d1_gen κ (d1_gradDrift U) (f s) x ∂(μt s) =
      ∫ x, (ft s x + d1_gen κ (d1_gradDrift U) (f s) x) ∂(μt s) := by
    have := d1_mu_prob hn hκ hU μ₀ s
    rw [integral_add (d1_integrable_of_continuous _ (hfts s hsI)) (d1_integrable_of_continuous _ hLs)]
    ring
  rw [hlim] at hsum
  refine hsum.congr' ?_
  filter_upwards [hmem2] with t ht
  have htI : t ∈ Set.Icc 0 τ := ⟨by linarith [hs.1, ht.1], ht.2.le⟩
  have hts : t - s ≠ 0 := by have := ht.1; intro h; linarith
  have := d1_mu_prob hn hκ hU μ₀ t
  rw [slope_def_field]
  have i1 : Integrable (f t) (μt t) := d1_integrable_of_continuous _ (hfc t htI)
  have i2 : Integrable (f s) (μt t) := d1_integrable_of_continuous _ (hfc s hsI)
  have i3 : Integrable (ft s) (μt t) := d1_integrable_of_continuous _ (hfts s hsI)
  have e1 : ∫ x, ((f t x - f s x) / (t - s) - ft s x) ∂(μt t) =
      (∫ x, f t x ∂(μt t) - ∫ x, f s x ∂(μt t)) / (t - s) - ∫ x, ft s x ∂(μt t) := by
    have i4 : Integrable (fun x => (f t x - f s x) / (t - s)) (μt t) := (i1.sub i2).div_const _
    rw [integral_sub i4 i3, integral_div, integral_sub i1 i2]
  rw [e1]
  field_simp
  ring

end TimeDepDeriv

end HRS
