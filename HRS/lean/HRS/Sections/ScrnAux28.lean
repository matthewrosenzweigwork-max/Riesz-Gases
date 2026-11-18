import HRS.Sections.ScrnAux27

/-!
# Packet SCRN, part 28: `E‖R‖ ≤ ∑_a √N · ½ C_q (∫_0^{t_a} K_a) · o_N`

Pointwise commutator estimate (`a8p_rem_pointwise`) for `flucInteraction`, integrated in time with the
weights `K_a(r)` (transport bounds of `∇ f_a^r`), then in `ω` by Tonelli using `E[F_N(X^r)] ≤ 0`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace HRS

open HRS.Main.A8P HRS.Uniform

variable {d : ℕ}

local notation "ℝ^" p => EuclideanSpace ℝ (Fin p)

lemma scrn_oNΛ_one (d : ℕ) (s C₀ : ℝ) (N : ℕ) : oNΛ d s C₀ 1 N = oN d s C₀ N := by
  unfold oNΛ oN
  simp only [mul_one, Real.one_rpow, one_mul]
  ring

theorem scrn_rem_bound (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (β : ℝ) (hβ : 0 < β)
    {N : ℕ} (hN : 2 ≤ N) {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X₀ : Ω → Config d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)}
    {X : ℝ≥0 → Ω → Config d N} (hfl : ScrnFlow d hs0 hsd β hβ N P X₀ W X)
    {ℱ : MeasureTheory.Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}
    (hF : IsFilteredSolution P ℱ W' W X) {C₀ Cq : ℝ} (hcom : A8CommSpec d s C₀ Cq) (hCq : 0 ≤ Cq)
    {p : ℕ} (ts : Fin p → ℝ) (hts0 : ∀ a, 0 ≤ ts a) (ψ : Fin p → Torus d → ℝ)
    (hψ2 : ∀ a, Torus.IsCk 2 (ψ a)) (f : Fin p → ℝ → Torus d → ℝ)
    (hf : ∀ a, (ts a = 0 ∧ f a = fun _ => ψ a) ∨ (0 < ts a ∧ IsClassicalAdjointSolution
      (PDE.mfData d s hs0 hsd (fun _ => 0) β hβ) (fun _ _ => (1 : ℝ)) (ts a) (ψ a) (f a)))
    (hC12 : ∀ a, ∃ ft, IsC12Test (ts a) (f a) ft) (hfc : ∀ a, Continuous (f a 0))
    (Kf : Fin p → ℝ → ℝ) (hKm : ∀ a, Measurable (Kf a))
    (hKint : ∀ a, IntegrableOn (Kf a) (Set.Icc 0 (ts a)))
    (hKnn : ∀ a, ∀ r ∈ Set.Icc 0 (ts a), 0 ≤ Kf a r)
    (hKtb : ∀ a, ∀ r ∈ Set.Icc 0 (ts a),
      HasTransportBound d s (HRS.GF.gfb2_v (PDE.mfData d s hs0 hsd (fun _ => 0) β hβ).M (f a r)) (Kf a r)) :
    Integrable (scrnRem (PDE.mfData d s hs0 hsd (fun _ => 0) β hβ) f ts X) P ∧
      ∫ ω, ‖scrnRem (PDE.mfData d s hs0 hsd (fun _ => 0) β hβ) f ts X ω‖ ∂P ≤
        ∑ a, Real.sqrt N * ((1 / 2) * Cq * (∫ r in Set.Icc 0 (ts a), Kf a r) * oN d s C₀ N) := by
  set D := PDE.mfData d s hs0 hsd (fun _ => 0) β hβ with hD
  have hd1 : 1 ≤ d := by omega
  have hN0 : 0 < N := by omega
  set o : ℝ := oN d s C₀ N with ho
  set Tm : ℝ := ∑ a, ts a + 1 with hTm
  have hTm0 : 0 < Tm := by
    have : 0 ≤ ∑ a, ts a := Finset.sum_nonneg fun a _ => hts0 a
    rw [hTm]; linarith
  have htsT : ∀ a, ts a ∈ Set.Icc 0 Tm := fun a =>
    ⟨hts0 a, by
      have : ts a ≤ ∑ b, ts b := Finset.single_le_sum (fun b _ => hts0 b) (Finset.mem_univ a)
      rw [hTm]; linarith⟩
  have hsolT := hfl.sol Tm hTm0.le
  have hXm : ∀ r : ℝ≥0, Measurable (X r) := fun r => (hF.adapted r).mono (ℱ.le _) le_rfl
  -- energy facts
  have hEn : ∀ t : ℝ, 0 ≤ t →
      Integrable (fun ω => rieszEnergy d s (X t.toNNReal ω) (volume : Measure (Torus d))) P ∧
      ∫ ω, rieszEnergy d s (X t.toNNReal ω) (volume : Measure (Torus d)) ∂P ≤ 0 := fun t ht =>
    scrn_energy_bound hd hs0 hsd β hβ hN P X₀ W X hfl.brownian hfl.indep hfl.law hfl.sol hfl.filt t ht
  have hFmeas : Measurable (fun Y : Config d N => rieszEnergy d s Y (volume : Measure (Torus d))) := by
    obtain ⟨hm, -⟩ := movf_energy_facts hd1 hs0 hsd scrn_isProbDensity_one continuous_const hN0 (N := N)
    rw [scrn_withDensityReal_one] at hm
    exact hm
  have hρ := scrn_isProbDensity_one (d := d)
  -- the completed positive energy (clamped in time)
  set G : ℝ → Ω → ℝ := fun r ω => max (rieszEnergy d s (X (Real.toNNReal (Q54c.clampT Tm r)) ω)
    (volume : Measure (Torus d)) + o) 0 with hG
  have hGm : Measurable fun q : ℝ × Ω => G q.1 q.2 :=
    ((hFmeas.comp (scrn_progressive_meas ℱ X hF.progressive hTm0.le)).add_const o).max measurable_const
  have hnoc : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ) ≤ Tm → X t ω ∉ collisionSet d N := hsolT.no_collision
  have hpos : ∀ᵐ ω ∂P, ∀ r ∈ Set.Icc (0 : ℝ) Tm,
      0 ≤ rieszEnergy d s (X (Real.toNNReal r) ω) (volume : Measure (Torus d)) + o := by
    filter_upwards [hnoc] with ω hω r hr
    have hcoll : X (Real.toNNReal r) ω ∉ collisionSet d N := hω _ (by
      rw [Real.coe_toNNReal _ hr.1]; exact hr.2)
    have h := (hcom 1 le_rfl N hN (fun _ => (1 : ℝ)) hρ (fun _ => le_rfl) _ hcoll).1
    rw [scrn_withDensityReal_one, scrn_oNΛ_one] at h
    exact h
  -- integrability and moment of `G r`
  have hGint : ∀ r ∈ Set.Icc (0 : ℝ) Tm, Integrable (G r) P := by
    intro r hr
    have hr0 : 0 ≤ Q54c.clampT Tm r := (Q54c.clampT_mem hTm0.le r).1
    exact ((hEn _ hr0).1.add (integrable_const o)).pos_part
  have hGmom : ∀ r ∈ Set.Icc (0 : ℝ) Tm, ∫ ω, G r ω ∂P ≤ o := by
    intro r hr
    have hcl := Q54c.clampT_mem hTm0.le r
    have hae : G r =ᵐ[P] fun ω => rieszEnergy d s (X (Real.toNNReal (Q54c.clampT Tm r)) ω)
        (volume : Measure (Torus d)) + o := by
      filter_upwards [hpos] with ω hω
      simp only [hG]
      exact max_eq_left (hω _ hcl)
    rw [integral_congr_ae hae, integral_add (hEn _ hcl.1).1 (integrable_const o)]
    have := (hEn _ hcl.1).2
    simp only [integral_const, probReal_univ, one_smul]
    linarith
  have hG0 : ∀ r ω, 0 ≤ G r ω := fun r ω => le_max_right _ _
  have hRae := scrn_rem_aemeas hd hs0 hsd β hβ hN hF hTm0.le hsolT ts htsT ψ hψ2 f hf hC12 hfc
  -- per-test bound
  have hper : ∀ a, Integrable (fun ω => scrnRem D f ts X ω a) P ∧
      ∫ ω, |scrnRem D f ts X ω a| ∂P ≤
        Real.sqrt N * ((1 / 2) * Cq * (∫ r in Set.Icc 0 (ts a), Kf a r) * o) := by
    intro a
    have hRa : AEMeasurable (fun ω => scrnRem D f ts X ω a) P :=
      (EuclideanSpace.proj a : (ℝ^p) →L[ℝ] ℝ).measurable.comp_aemeasurable hRae
    set Kn : ℝ → ℝ := fun r => |Kf a r| with hKn
    have hKnm : Measurable Kn := continuous_abs.measurable.comp (hKm a)
    have hsub : ∀ r ∈ Set.Icc (0 : ℝ) (ts a), r ∈ Set.Icc (0 : ℝ) Tm := fun r hr =>
      ⟨hr.1, hr.2.trans (htsT a).2⟩
    have hKnint : IntegrableOn Kn (Set.Icc 0 (ts a)) := (hKint a).abs
    obtain ⟨hI1, hI2, -⟩ := scrn_time_integral_w P (hts0 a) (fun r ω => Kn r * G r ω)
      (((hKnm.comp measurable_fst).mul hGm))
      (Filter.Eventually.of_forall fun ω r _ => mul_nonneg (abs_nonneg _) (hG0 r ω))
      (fun r hr => (hGint r (hsub r hr)).const_mul _) (fun r => Kn r * o)
      (hKnint.mul_const o) (fun r hr => by
        rw [integral_const_mul]
        exact mul_le_mul_of_nonneg_left (hGmom r (hsub r hr)) (abs_nonneg _))
    have hcoef0 : 0 ≤ Real.sqrt N * ((1 / 2) * Cq) := by positivity
    -- pointwise bound
    have hpt : ∀ᵐ ω ∂P, |scrnRem D f ts X ω a| ≤
        Real.sqrt N * ((1 / 2) * Cq) * ∫ r in Set.Icc (0 : ℝ) (ts a), Kn r * G r ω := by
      filter_upwards [hnoc, hI1] with ω hno hint
      have hrest : ∀ᵐ r ∂(volume.restrict (Set.Ioc (0 : ℝ) (ts a))),
          ‖flucInteraction D (f a r) (X (Real.toNNReal r) ω) (fun _ => (1 : ℝ))‖ ≤
            (1 / 2) * Cq * (Kn r * G r ω) := by
        refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun r hrmem => ?_)
        have hr : r ∈ Set.Icc (0 : ℝ) (ts a) := ⟨hrmem.1.le, hrmem.2⟩
        have hrT := hsub r hr
        have hcoll : X (Real.toNNReal r) ω ∉ collisionSet d N := hno _ (by
          rw [Real.coe_toNNReal _ hr.1]; exact hrT.2)
        obtain ⟨ftt, hft⟩ := hC12 a
        have hCk2 : Torus.IsCk 2 (f a r) := hft.c2 r hr
        have hpt1 := a8p_rem_pointwise hd1 hs0 hsd hcom hCq (Λ := 1) le_rfl hN (D := D) rfl
          (ρ := fun _ => (1 : ℝ)) hρ (fun _ => le_rfl) hCk2 (hKtb a r hr) _ hcoll
        rw [scrn_withDensityReal_one, scrn_oNΛ_one] at hpt1
        rw [Real.norm_eq_abs]
        refine hpt1.trans ?_
        have hcl : Q54c.clampT Tm r = r := Q54c.clampT_of_mem hrT
        have hGge : rieszEnergy d s (X (Real.toNNReal r) ω) (volume : Measure (Torus d)) + o ≤ G r ω := by
          simp only [hG, hcl]; exact le_max_left _ _
        have hK0 := hKnn a r hr
        have hKe : Kn r = Kf a r := abs_of_nonneg hK0
        rw [hKe]
        have : (1 / 2 : ℝ) * (Cq * Kf a r) * (rieszEnergy d s (X (Real.toNNReal r) ω)
            (volume : Measure (Torus d)) + o) ≤ (1 / 2) * (Cq * Kf a r) * G r ω :=
          mul_le_mul_of_nonneg_left hGge (by positivity)
        linarith
      have hIoc : IntegrableOn (fun r => Kn r * G r ω) (Set.Ioc (0 : ℝ) (ts a)) :=
        hint.mono_set Set.Ioc_subset_Icc_self
      have hnorm : ‖∫ r in (0 : ℝ)..(ts a), flucInteraction D (f a r) (X (Real.toNNReal r) ω)
          (fun _ => (1 : ℝ))‖ ≤ (1 / 2) * Cq * ∫ r in Set.Icc (0 : ℝ) (ts a), Kn r * G r ω := by
        rw [intervalIntegral.integral_of_le (hts0 a)]
        refine (norm_integral_le_of_norm_le (hIoc.const_mul _) hrest).trans ?_
        rw [integral_const_mul, integral_Icc_eq_integral_Ioc]
      show |Real.sqrt N * ∫ r in (0 : ℝ)..(ts a), flucInteraction D (f a r) (X (Real.toNNReal r) ω)
          (fun _ => (1 : ℝ))| ≤ _
      rw [abs_mul, abs_of_pos (Real.sqrt_pos.2 (by exact_mod_cast hN0)), ← Real.norm_eq_abs]
      calc Real.sqrt N * ‖∫ r in (0 : ℝ)..(ts a), flucInteraction D (f a r) (X (Real.toNNReal r) ω)
            (fun _ => (1 : ℝ))‖ ≤ Real.sqrt N * ((1 / 2) * Cq * ∫ r in Set.Icc (0 : ℝ) (ts a),
              Kn r * G r ω) := mul_le_mul_of_nonneg_left hnorm (Real.sqrt_nonneg _)
        _ = _ := by ring
    -- the lintegral bound
    have hB0 : 0 ≤ Real.sqrt N * ((1 / 2) * Cq * (∫ r in Set.Icc 0 (ts a), Kf a r) * o) := by
      have h1 : 0 ≤ ∫ r in Set.Icc 0 (ts a), Kf a r :=
        setIntegral_nonneg measurableSet_Icc (hKnn a)
      have ho0 : 0 ≤ o := by
        have h0 := hGmom 0 ⟨le_rfl, hTm0.le⟩
        exact (integral_nonneg (hG0 0)).trans h0
      positivity
    have hlint : ∫⁻ ω, ENNReal.ofReal |scrnRem D f ts X ω a| ∂P ≤
        ENNReal.ofReal (Real.sqrt N * ((1 / 2) * Cq * (∫ r in Set.Icc 0 (ts a), Kf a r) * o)) := by
      calc ∫⁻ ω, ENNReal.ofReal |scrnRem D f ts X ω a| ∂P
          ≤ ∫⁻ ω, ENNReal.ofReal (Real.sqrt N * ((1 / 2) * Cq)) *
              ENNReal.ofReal (∫ r in Set.Icc (0 : ℝ) (ts a), Kn r * G r ω) ∂P := by
            refine lintegral_mono_ae ?_
            filter_upwards [hpt] with ω hω
            rw [← ENNReal.ofReal_mul hcoef0]
            exact ENNReal.ofReal_le_ofReal hω
        _ = ENNReal.ofReal (Real.sqrt N * ((1 / 2) * Cq)) *
              ∫⁻ ω, ENNReal.ofReal (∫ r in Set.Icc (0 : ℝ) (ts a), Kn r * G r ω) ∂P :=
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        _ ≤ ENNReal.ofReal (Real.sqrt N * ((1 / 2) * Cq)) *
              ENNReal.ofReal (∫ r in Set.Icc (0 : ℝ) (ts a), Kn r * o) :=
            mul_le_mul_right hI2 _
        _ = ENNReal.ofReal (Real.sqrt N * ((1 / 2) * Cq) *
              ∫ r in Set.Icc (0 : ℝ) (ts a), Kn r * o) := by
            rw [← ENNReal.ofReal_mul hcoef0]
        _ = _ := by
            congr 1
            have : ∫ r in Set.Icc (0 : ℝ) (ts a), Kn r * o = (∫ r in Set.Icc 0 (ts a), Kf a r) * o := by
              rw [integral_mul_const]
              congr 1
              exact setIntegral_congr_fun measurableSet_Icc fun r hr => abs_of_nonneg (hKnn a r hr)
            rw [this]; ring
    exact a8p_abs_integral_le hRa hB0 hlint
  -- assemble the vector
  have hbdd : ∀ ω, ‖scrnRem D f ts X ω‖ ≤ ∑ a, |scrnRem D f ts X ω a| := fun ω =>
    a8p_norm_le_sum_abs _
  have hsumint : Integrable (fun ω => ∑ a, |scrnRem D f ts X ω a|) P :=
    integrable_finsetSum _ fun a _ => (hper a).1.abs
  refine ⟨?_, ?_⟩
  · refine Integrable.mono' hsumint hRae.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
    exact hbdd ω
  · calc ∫ ω, ‖scrnRem D f ts X ω‖ ∂P ≤ ∫ ω, ∑ a, |scrnRem D f ts X ω a| ∂P :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => norm_nonneg _) hsumint
          (Filter.Eventually.of_forall hbdd)
      _ = ∑ a, ∫ ω, |scrnRem D f ts X ω a| ∂P := integral_finsetSum _ fun a _ => (hper a).1.abs
      _ ≤ _ := Finset.sum_le_sum fun a _ => (hper a).2

end HRS
