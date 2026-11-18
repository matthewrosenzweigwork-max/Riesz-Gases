import HRS.MS.R2ChaosAux29

/-!
# HRS.MS.R2ChaosAux30 -- R3 (part 2): the quadratic-process difference at a fixed time

Packet S94, namespace `HRS.MS.R2Chaos`, helper prefix `s94_`.

For a kernel family `hm m` approximating `h` (`IsRound2Approx` at each `t ∈ [0,T]`):
* `s94_quad_sub_eq` : `B^{hm}_N(t) - B^{h}_N(t) = N (F^{hm - h} - E F^{hm - h})` pointwise in `ζ` (`N ≥ 2`);
* `s94_diff_bound` : `‖B^{hm m}_N(t) - B^{h}_N(t)‖_{L²(P_N)} ≤ C` uniformly in `m, N ≥ 2, t ∈ [0,T]`;
* `s94_diff_tail` : `sup_{N ≥ 2} ‖B^{hm m}_N(t) - B^{h}_N(t)‖_{L²(P_N)} → 0` as `m → ∞`, for every `t ∈ [0,T]`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.deprecated false

open MeasureTheory ProbabilityTheory Function Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

namespace HRS.MS.R2Chaos

open HRS.Whole

variable {d : ℕ}

section R3c0

theorem s94_eLpNorm_centered_map {N : ℕ} {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {Ω : Type*}
    [MeasurableSpace Ω] {Pm : Measure Ω} {Xt : Ω → EucConfig d N} (hX : Measurable Xt)
    {k : Euc d → Euc d → ℝ} (hk : Measurable fun q : Euc d × Euc d => k q.1 q.2) (r : ℝ≥0∞) :
    eLpNorm (fun ζ => (N : ℝ) * (pairEnergy k (Xt ζ) μ - ∫ ζ', pairEnergy k (Xt ζ') μ ∂Pm)) r Pm =
      eLpNorm (fun Z : EucConfig d N => (N : ℝ) * (pairEnergy k Z μ - ∫ Y, pairEnergy k Y μ ∂(Pm.map Xt)))
        r (Pm.map Xt) := by
  have hmeas := s94_pE_meas_config (N := N) (μ := μ) hk
  have hg2 : AEStronglyMeasurable (fun Z : EucConfig d N => (N : ℝ) * (pairEnergy k Z μ -
      ∫ Y, pairEnergy k Y μ ∂(Pm.map Xt))) (Pm.map Xt) :=
    ((hmeas.sub measurable_const).const_mul _).aestronglyMeasurable
  have hint : ∫ Y, pairEnergy k Y μ ∂(Pm.map Xt) = ∫ ζ', pairEnergy k (Xt ζ') μ ∂Pm :=
    integral_map hX.aemeasurable hmeas.aestronglyMeasurable
  rw [eLpNorm_map_measure hg2 hX.aemeasurable]
  simp only [Function.comp_def, hint]

end R3c0

section R3c

variable {s T b p K M L : ℝ} {ρ : Euc d → ℝ} {Ω : ℕ → Type} [∀ N, MeasurableSpace (Ω N)]
  {P : ∀ N, Measure (Ω N)} [∀ N, IsProbabilityMeasure (P N)] {X : ∀ N, ℝ≥0 → Ω N → EucConfig d N}
  {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
  {ξ : (Euc d → ℝ) → Ω' → C(Set.Icc (0 : ℝ) T, ℝ)}

theorem s94_integrable_pE (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (hb : 0 < b) (hp : 1 < p)
    (hρ : IsRound2Density d s M L ρ)
    (hset : IsRound2PathSetting d s T b p K (Whole.withDensityReal ρ) P X P' ξ) {B' : ℝ} {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) T) {N : ℕ} (hN : 2 ≤ N) {k : Euc d → Euc d → ℝ}
    (hk : IsBoundedPairKernel s B' k) :
    Integrable (fun ζ => pairEnergy k (X N t.toNNReal ζ) (Whole.withDensityReal ρ)) (P N) := by
  haveI : IsProbabilityMeasure (Whole.withDensityReal ρ) := HRS.Whole.U1.u1_isProb hρ.prob
  obtain ⟨C, hC⟩ := s94_time_bounds hd hs0 hs hb hp hρ hset B' (r := 1) le_rfl
  have h1 := (hC t ht N hN k hk).1
  have hmX : Measurable (X N t.toNNReal) := s94_pushforward_prob hset N _
  have hmeas := s94_pE_meas_config (N := N) (μ := Whole.withDensityReal ρ) hk.measurable
  have hm : AEStronglyMeasurable (fun ζ => (N : ℝ) * pairEnergy k (X N t.toNNReal ζ) (Whole.withDensityReal ρ)) (P N) :=
    (((hmeas.comp hmX).const_mul _)).aestronglyMeasurable
  have hL : MemLp (fun ζ => (N : ℝ) * pairEnergy k (X N t.toNNReal ζ) (Whole.withDensityReal ρ)) 1 (P N) := by
    have : ENNReal.ofReal 1 = 1 := by norm_num
    rw [this] at h1
    exact lt_of_le_of_lt h1 ENNReal.ofReal_lt_top
  have hI := (memLp_one_iff_integrable.1 hL)
  have hN0 : (N : ℝ) ≠ 0 := by positivity
  refine (hI.const_mul (1 / (N : ℝ))).congr (ae_of_all _ fun ζ => ?_)
  simp only
  field_simp

theorem s94_quad_sub_eq (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (hb : 0 < b) (hp : 1 < p)
    (hρ : IsRound2Density d s M L ρ)
    (hset : IsRound2PathSetting d s T b p K (Whole.withDensityReal ρ) P X P' ξ) {B1 B2 : ℝ}
    {hm h : ℝ → Euc d → Euc d → ℝ} {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) {N : ℕ} (hN : 2 ≤ N)
    (h1 : IsBoundedPairKernel s B1 (hm t)) (h2 : IsBoundedPairKernel s B2 (h t)) (ζ : Ω N) :
    r2QuadFluct (Whole.withDensityReal ρ) hm (P N) (X N) t ζ -
        r2QuadFluct (Whole.withDensityReal ρ) h (P N) (X N) t ζ =
      (N : ℝ) * (pairEnergy (fun x y => hm t x y - h t x y) (X N t.toNNReal ζ) (Whole.withDensityReal ρ) -
        ∫ ζ', pairEnergy (fun x y => hm t x y - h t x y) (X N t.toNNReal ζ') (Whole.withDensityReal ρ) ∂(P N)) := by
  haveI : IsProbabilityMeasure (Whole.withDensityReal ρ) := HRS.Whole.U1.u1_isProb hρ.prob
  have r1 := s94_rowOKE hd hs0 hs hρ h1
  have r2 := s94_rowOKE hd hs0 hs hρ h2
  have i1 := s94_integrable_pE hd hs0 hs hb hp hρ hset ht hN h1
  have i2 := s94_integrable_pE hd hs0 hs hb hp hρ hset ht hN h2
  unfold r2QuadFluct
  simp_rw [HRS.MS.Wr.pairEnergy_sub r1 r2]
  rw [integral_sub i1 i2]
  ring

theorem s94_sub_isBounded {B1 B2 : ℝ} {k1 k2 : Euc d → Euc d → ℝ} (h1 : IsBoundedPairKernel s B1 k1)
    (h2 : IsBoundedPairKernel s B2 k2) : IsBoundedPairKernel s (B1 + B2) (fun x y => k1 x y - k2 x y) := by
  refine ⟨h1.measurable.sub h2.measurable, fun x y => by rw [h1.symm, h2.symm], fun x y hxy => ?_⟩
  have a1 := h1.bound x y hxy
  have a2 := h2.bound x y hxy
  calc |k1 x y - k2 x y| ≤ |k1 x y| + |k2 x y| := abs_sub _ _
    _ ≤ _ := by nlinarith

/-- Uniform `L²(P_N)` bound and the `m → ∞` tail for the difference of the quadratic processes at a fixed time. -/
theorem s94_diff_bound_tail (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (hb : 0 < b) (hp : 1 < p)
    (hρ : IsRound2Density d s M L ρ)
    (hset : IsRound2PathSetting d s T b p K (Whole.withDensityReal ρ) P X P' ξ) {B C₁ : ℝ}
    {hm : ℕ → ℝ → Euc d → Euc d → ℝ} {h : ℝ → Euc d → Euc d → ℝ}
    (hker : ∀ t ∈ Set.Icc (0 : ℝ) T, IsBoundedPairKernel s B (h t))
    (hA : ∀ t ∈ Set.Icc (0 : ℝ) T, IsRound2Approx s C₁ B (Whole.withDensityReal ρ) (h t) (fun m => hm m t)) :
    ∃ C : ℝ, (∀ t ∈ Set.Icc (0 : ℝ) T, ∀ m : ℕ, ∀ N : ℕ, 2 ≤ N →
      eLpNorm (fun ζ => r2QuadFluct (Whole.withDensityReal ρ) (hm m) (P N) (X N) t ζ -
        r2QuadFluct (Whole.withDensityReal ρ) h (P N) (X N) t ζ) 2 (P N) ≤ ENNReal.ofReal C) ∧
    ∀ t ∈ Set.Icc (0 : ℝ) T, Tendsto (fun m => ⨆ N : {N : ℕ // 2 ≤ N},
      eLpNorm (fun ζ => r2QuadFluct (Whole.withDensityReal ρ) (hm m) (P N) (X N) t ζ -
        r2QuadFluct (Whole.withDensityReal ρ) h (P N) (X N) t ζ) 2 (P N)) atTop (𝓝 0) := by
  haveI : IsProbabilityMeasure (Whole.withDensityReal ρ) := HRS.Whole.U1.u1_isProb hρ.prob
  obtain ⟨C, hC⟩ := s94_time_bounds hd hs0 hs hb hp hρ hset (C₁ * B + B) (r := 2) (by norm_num)
  obtain ⟨C2, hC2⟩ := HRS.MS.R2Mt.round2_moment_transfer_proof hd s hs0 hs M L b p K B hb hp 2 (by norm_num)
  have hdk : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ m, IsBoundedPairKernel s (C₁ * B + B) (fun x y => hm m t x y - h t x y) :=
    fun t ht m => s94_sub_isBounded (s94_approx_bounded (hA t ht) m) (hker t ht)
  have hid : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ m, ∀ N : ℕ, 2 ≤ N →
      (fun ζ => r2QuadFluct (Whole.withDensityReal ρ) (hm m) (P N) (X N) t ζ -
        r2QuadFluct (Whole.withDensityReal ρ) h (P N) (X N) t ζ) =
      fun ζ => (N : ℝ) * (pairEnergy (fun x y => hm m t x y - h t x y) (X N t.toNNReal ζ) (Whole.withDensityReal ρ) -
        ∫ ζ', pairEnergy (fun x y => hm m t x y - h t x y) (X N t.toNNReal ζ') (Whole.withDensityReal ρ) ∂(P N)) :=
    fun t ht m N hN => funext fun ζ => s94_quad_sub_eq hd hs0 hs hb hp hρ hset (hm := hm m) ht hN
      (s94_approx_bounded (hA t ht) m) (hker t ht) ζ
  refine ⟨C, fun t ht m N hN => ?_, fun t ht => ?_⟩
  · rw [hid t ht m N hN]
    have := (hC t ht N hN _ (hdk t ht m)).2
    simpa using this
  · have hbT := ((hC2 ρ hρ (fun N' => (P N').map (X N' t.toNNReal))
      (fun N' hN' => hset.density N' hN' t ht)).2.2 C₁ (h t) (fun m => hm m t) (hker t ht) (hA t ht)).2
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

end R3c

end HRS.MS.R2Chaos
