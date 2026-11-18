import HRS.MS.R2ChaosAux53

/-!
# HRS.MS.R2ChaosAux54 -- S9.6 (P2): the quadratic-process difference for polynomial kernels at a fixed time

Packet S94 (S9.6), namespace `HRS.MS.R2Chaos`, helper prefix `s94_`.

Polynomial analogue of `s94_time_bounds`, `s94_quad_sub_eq`, `s94_diff_bound_tail` (S9.5 replaces S9.2; `pairEnergy` additivity needs
only integrability of the rows and of `x ↦ ∫ k(x,y) dμ`, `s95_poly_integrable`).
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.deprecated false

open MeasureTheory ProbabilityTheory Function Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

namespace HRS.MS.R2Chaos

open HRS.Whole HRS.MS.R2Poly

variable {d : ℕ}

section PTime

variable {s T b p K M L C₀ c₀ Pw : ℝ} {ρ : Euc d → ℝ} {Ω : ℕ → Type} [∀ N, MeasurableSpace (Ω N)]
  {P : ∀ N, Measure (Ω N)} [∀ N, IsProbabilityMeasure (P N)] {X : ∀ N, ℝ≥0 → Ω N → EucConfig d N}
  {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
  {ξ : (Euc d → ℝ) → Ω' → C(Set.Icc (0 : ℝ) T, ℝ)}

theorem s94_ptime_bounds (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (hb : 0 < b) (hp : 1 < p)
    (hρ : IsRound2Density d s M L ρ) (hG : HasR2GaussianUpper C₀ c₀ ρ) (hPw : 0 ≤ Pw)
    (hset : IsRound2PathSetting d s T b p K (Whole.withDensityReal ρ) P X P' ξ) {r : ℝ} (hr : 1 ≤ r) :
    ∃ C : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ N : ℕ, 2 ≤ N → ∀ B' : ℝ, 0 ≤ B' → ∀ k : Euc d → Euc d → ℝ,
      IsR2PolyPairKernel s Pw B' k →
      eLpNorm (fun ζ => (N : ℝ) * pairEnergy k (X N t.toNNReal ζ) (Whole.withDensityReal ρ))
        (ENNReal.ofReal r) (P N) ≤ ENNReal.ofReal (C * B') ∧
      eLpNorm (fun ζ => (N : ℝ) * (pairEnergy k (X N t.toNNReal ζ) (Whole.withDensityReal ρ) -
        ∫ ζ', pairEnergy k (X N t.toNNReal ζ') (Whole.withDensityReal ρ) ∂(P N)))
        (ENNReal.ofReal r) (P N) ≤ ENNReal.ofReal (C * B') := by
  haveI : IsProbabilityMeasure (Whole.withDensityReal ρ) := HRS.Whole.U1.u1_isProb hρ.prob
  obtain ⟨C, hC⟩ := HRS.MS.R2Poly.round2_polynomial_moments_proof hd s hs0 hs M L C₀ c₀ b p K Pw hb hp hPw r hr
  refine ⟨C, fun t ht N hN B' hB' k hk => ?_⟩
  have hmX : Measurable (X N t.toNNReal) := s94_pushforward_prob hset N _
  have hF := ((hC ρ hρ hG (fun N' => (P N').map (X N' t.toNNReal))
    (fun N' hN' => hset.density N' hN' t ht)).1 B' hB' k hk) () N hN
  obtain ⟨hF1, hF2⟩ := hF
  have hmeas := s94_pE_meas_config (N := N) (μ := Whole.withDensityReal ρ) hk.measurable
  have hg1 : AEStronglyMeasurable (fun Z : EucConfig d N => (N : ℝ) * pairEnergy k Z (Whole.withDensityReal ρ))
      ((P N).map (X N t.toNNReal)) := (hmeas.const_mul _).aestronglyMeasurable
  have e1 : eLpNorm (fun ζ => (N : ℝ) * pairEnergy k (X N t.toNNReal ζ) (Whole.withDensityReal ρ))
      (ENNReal.ofReal r) (P N) = eLpNorm (fun Z : EucConfig d N => (N : ℝ) * pairEnergy k Z (Whole.withDensityReal ρ))
      (ENNReal.ofReal r) ((P N).map (X N t.toNNReal)) := by
    rw [eLpNorm_map_measure hg1 hmX.aemeasurable]; rfl
  exact ⟨e1.le.trans hF1, (s94_eLpNorm_centered_map hmX hk.measurable _).le.trans hF2⟩

theorem s94_poly_int_facts (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (hρ : IsRound2Density d s M L ρ)
    (hG : HasR2GaussianUpper C₀ c₀ ρ) (hPw : 0 ≤ Pw) {B : ℝ} (hB : 0 ≤ B) {k : Euc d → Euc d → ℝ}
    (hk : IsR2PolyPairKernel s Pw B k) :
    (∀ x, Integrable (k x) (Whole.withDensityReal ρ)) ∧
      Integrable (HRS.MS.Wr.wr14a_Hc k (Whole.withDensityReal ρ)) (Whole.withDensityReal ρ) := by
  haveI : IsProbabilityMeasure (Whole.withDensityReal ρ) := HRS.Whole.U1.u1_isProb hρ.prob
  obtain ⟨h1, h2⟩ := s95_poly_integrable (by omega) hs0 hs M C₀ c₀ hG.1 hPw ρ hρ.prob hρ.bdd hG.2 B hB k hk
  exact ⟨h1, h2.integral_prod_left⟩

theorem s94_pe_sub {μ : Measure (Euc d)} {k1 k2 : Euc d → Euc d → ℝ} {N : ℕ} (h1 : ∀ x, Integrable (k1 x) μ)
    (h2 : ∀ x, Integrable (k2 x) μ) (H1 : Integrable (HRS.MS.Wr.wr14a_Hc k1 μ) μ)
    (H2 : Integrable (HRS.MS.Wr.wr14a_Hc k2 μ) μ) (X : EucConfig d N) :
    pairEnergy (fun x y => k1 x y - k2 x y) X μ = pairEnergy k1 X μ - pairEnergy k2 X μ := by
  unfold pairEnergy
  have e1 : ∀ x, ∫ y, (k1 x y - k2 x y) ∂μ = ∫ y, k1 x y ∂μ - ∫ y, k2 x y ∂μ :=
    fun x => integral_sub (h1 x) (h2 x)
  simp only [e1, Finset.sum_sub_distrib]
  have e2 : ∫ x, (∫ y, k1 x y ∂μ - ∫ y, k2 x y ∂μ) ∂μ =
      (∫ x, ∫ y, k1 x y ∂μ ∂μ) - ∫ x, ∫ y, k2 x y ∂μ ∂μ := integral_sub H1 H2
  rw [e2]
  ring

theorem s94_pintegrable_pE (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (hb : 0 < b) (hp : 1 < p)
    (hρ : IsRound2Density d s M L ρ) (hG : HasR2GaussianUpper C₀ c₀ ρ) (hPw : 0 ≤ Pw)
    (hset : IsRound2PathSetting d s T b p K (Whole.withDensityReal ρ) P X P' ξ) {B' : ℝ} (hB' : 0 ≤ B')
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) {N : ℕ} (hN : 2 ≤ N) {k : Euc d → Euc d → ℝ}
    (hk : IsR2PolyPairKernel s Pw B' k) :
    Integrable (fun ζ => pairEnergy k (X N t.toNNReal ζ) (Whole.withDensityReal ρ)) (P N) := by
  haveI : IsProbabilityMeasure (Whole.withDensityReal ρ) := HRS.Whole.U1.u1_isProb hρ.prob
  obtain ⟨C, hC⟩ := s94_ptime_bounds hd hs0 hs hb hp hρ hG hPw hset (r := 1) le_rfl
  have h1 := (hC t ht N hN B' hB' k hk).1
  have hmX : Measurable (X N t.toNNReal) := s94_pushforward_prob hset N _
  have hmeas := s94_pE_meas_config (N := N) (μ := Whole.withDensityReal ρ) hk.measurable
  have hL : MemLp (fun ζ => (N : ℝ) * pairEnergy k (X N t.toNNReal ζ) (Whole.withDensityReal ρ)) 1 (P N) := by
    have : ENNReal.ofReal 1 = 1 := by norm_num
    rw [this] at h1
    exact lt_of_le_of_lt h1 ENNReal.ofReal_lt_top
  have hI := (memLp_one_iff_integrable.1 hL)
  have hN0 : (N : ℝ) ≠ 0 := by positivity
  refine (hI.const_mul (1 / (N : ℝ))).congr (ae_of_all _ fun ζ => ?_)
  simp only
  field_simp

theorem s94_pquad_sub_eq (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (hb : 0 < b) (hp : 1 < p)
    (hρ : IsRound2Density d s M L ρ) (hG : HasR2GaussianUpper C₀ c₀ ρ) (hPw : 0 ≤ Pw)
    (hset : IsRound2PathSetting d s T b p K (Whole.withDensityReal ρ) P X P' ξ) {B1 B2 : ℝ} (hB1 : 0 ≤ B1)
    (hB2 : 0 ≤ B2) {hm h : ℝ → Euc d → Euc d → ℝ} {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) {N : ℕ} (hN : 2 ≤ N)
    (h1 : IsR2PolyPairKernel s Pw B1 (hm t)) (h2 : IsR2PolyPairKernel s Pw B2 (h t)) (ζ : Ω N) :
    r2QuadFluct (Whole.withDensityReal ρ) hm (P N) (X N) t ζ -
        r2QuadFluct (Whole.withDensityReal ρ) h (P N) (X N) t ζ =
      (N : ℝ) * (pairEnergy (fun x y => hm t x y - h t x y) (X N t.toNNReal ζ) (Whole.withDensityReal ρ) -
        ∫ ζ', pairEnergy (fun x y => hm t x y - h t x y) (X N t.toNNReal ζ') (Whole.withDensityReal ρ) ∂(P N)) := by
  haveI : IsProbabilityMeasure (Whole.withDensityReal ρ) := HRS.Whole.U1.u1_isProb hρ.prob
  obtain ⟨r1, R1⟩ := s94_poly_int_facts hd hs0 hs hρ hG hPw hB1 h1
  obtain ⟨r2, R2⟩ := s94_poly_int_facts hd hs0 hs hρ hG hPw hB2 h2
  have i1 := s94_pintegrable_pE hd hs0 hs hb hp hρ hG hPw hset hB1 ht hN h1
  have i2 := s94_pintegrable_pE hd hs0 hs hb hp hρ hG hPw hset hB2 ht hN h2
  unfold r2QuadFluct
  simp_rw [s94_pe_sub r1 r2 R1 R2]
  rw [integral_sub i1 i2]
  ring

theorem s94_poly_diff_bound_tail (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (hb : 0 < b) (hp : 1 < p)
    (hρ : IsRound2Density d s M L ρ) (hG : HasR2GaussianUpper C₀ c₀ ρ) (hPw : 0 ≤ Pw)
    (hset : IsRound2PathSetting d s T b p K (Whole.withDensityReal ρ) P X P' ξ) {B : ℝ} (hB : 0 ≤ B)
    {hm : ℕ → ℝ → Euc d → Euc d → ℝ} {h : ℝ → Euc d → Euc d → ℝ}
    (hker : ∀ t ∈ Set.Icc (0 : ℝ) T, IsR2PolyPairKernel s Pw B (h t))
    (hhm : ∀ m, ∀ t ∈ Set.Icc (0 : ℝ) T, IsR2PolyPairKernel s Pw B (hm m t))
    (hconv : ∀ t ∈ Set.Icc (0 : ℝ) T, ∃ ε : ℝ, 0 < ε ∧ (2 + ε) * s < d ∧
      Tendsto (fun m => eLpNorm (fun q : Euc d × Euc d => hm m t q.1 q.2 - h t q.1 q.2)
        (ENNReal.ofReal (2 + ε)) ((Whole.withDensityReal ρ).prod (Whole.withDensityReal ρ))) atTop (𝓝 0)) :
    ∃ C : ℝ, (∀ t ∈ Set.Icc (0 : ℝ) T, ∀ m : ℕ, ∀ N : ℕ, 2 ≤ N →
      eLpNorm (fun ζ => r2QuadFluct (Whole.withDensityReal ρ) (hm m) (P N) (X N) t ζ -
        r2QuadFluct (Whole.withDensityReal ρ) h (P N) (X N) t ζ) 2 (P N) ≤ ENNReal.ofReal C) ∧
    ∀ t ∈ Set.Icc (0 : ℝ) T, Tendsto (fun m => ⨆ N : {N : ℕ // 2 ≤ N},
      eLpNorm (fun ζ => r2QuadFluct (Whole.withDensityReal ρ) (hm m) (P N) (X N) t ζ -
        r2QuadFluct (Whole.withDensityReal ρ) h (P N) (X N) t ζ) 2 (P N)) atTop (𝓝 0) := by
  haveI : IsProbabilityMeasure (Whole.withDensityReal ρ) := HRS.Whole.U1.u1_isProb hρ.prob
  obtain ⟨C, hC⟩ := s94_ptime_bounds hd hs0 hs hb hp hρ hG hPw hset (r := 2) (by norm_num)
  obtain ⟨C2, hC2⟩ := HRS.MS.R2Poly.round2_polynomial_moments_proof hd s hs0 hs M L C₀ c₀ b p K Pw hb hp hPw 2 (by norm_num)
  have hdk : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ m, IsR2PolyPairKernel s Pw (2 * B) (fun x y => hm m t x y - h t x y) :=
    fun t ht m => s95_diff_poly (hker t ht) (hhm m t ht)
  have hid : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ m, ∀ N : ℕ, 2 ≤ N →
      (fun ζ => r2QuadFluct (Whole.withDensityReal ρ) (hm m) (P N) (X N) t ζ -
        r2QuadFluct (Whole.withDensityReal ρ) h (P N) (X N) t ζ) =
      fun ζ => (N : ℝ) * (pairEnergy (fun x y => hm m t x y - h t x y) (X N t.toNNReal ζ) (Whole.withDensityReal ρ) -
        ∫ ζ', pairEnergy (fun x y => hm m t x y - h t x y) (X N t.toNNReal ζ') (Whole.withDensityReal ρ) ∂(P N)) :=
    fun t ht m N hN => funext fun ζ => s94_pquad_sub_eq hd hs0 hs hb hp hρ hG hPw hset hB hB (hm := hm m) ht hN
      (hhm m t ht) (hker t ht) ζ
  refine ⟨C * (2 * B), fun t ht m N hN => ?_, fun t ht => ?_⟩
  · rw [hid t ht m N hN]
    have := (hC t ht N hN (2 * B) (by positivity) _ (hdk t ht m)).2
    simpa using this
  · have hbT := ((hC2 ρ hρ hG (fun N' => (P N').map (X N' t.toNNReal))
      (fun N' hN' => hset.density N' hN' t ht)).2.1 B hB (h t) (fun m => hm m t) (hker t ht)
      (fun m => hhm m t ht) (hconv t ht)).2
    refine (tendsto_congr fun m => ?_).2 hbT
    have heN : ∀ N : {N : ℕ // 2 ≤ N},
        eLpNorm (fun ζ => r2QuadFluct (Whole.withDensityReal ρ) (hm m) (P N) (X N) t ζ -
          r2QuadFluct (Whole.withDensityReal ρ) h (P N) (X N) t ζ) 2 (P N) =
        eLpNorm (fun Z : EucConfig d N => (N : ℝ) * (pairEnergy (fun x y => hm m t x y - h t x y) Z
          (Whole.withDensityReal ρ) - ∫ Y, pairEnergy (fun x y => hm m t x y - h t x y) Y
          (Whole.withDensityReal ρ) ∂((P N).map (X N t.toNNReal)))) (ENNReal.ofReal 2)
          ((P N).map (X N t.toNNReal)) := by
      intro N
      have : ENNReal.ofReal 2 = 2 := by norm_num
      rw [this, hid t ht m N N.2]
      exact s94_eLpNorm_centered_map (s94_pushforward_prob hset N _) (hdk t ht m).measurable 2
    refine le_antisymm (iSup_le fun N => le_iSup_of_le () (le_iSup_of_le N (heN N).le))
      (iSup_le fun i => iSup_le fun N => le_iSup_of_le N (heN N).ge)

end PTime

end HRS.MS.R2Chaos
