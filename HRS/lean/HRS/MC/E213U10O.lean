import HRS.MC.E213U10N
import HRS.MC.E213U6

/-!
# Packet e213u10, part O: almost-sure identification of the particle integrals with the pair-space functionals

For `N ≥ 2`, a prepared realisation, `0 ≤ b ≤ a`, `a + T ≤ b + L`:

* `u10_particle_A`: a.s. `rsA(ζ_N^{0,a+T}; near_b ℬ_N) = FD(ζ_N^{b,L}, ℬ_N^{b,L})`;
* `u10_particle_J`: a.s. `rsJ(ζ_N^{0,a+T}; near_b η_N) = FJ(ζ_N^{b,L}, ζ_N^{b,L} + m_N)` where `m_N` is the mean shift of the window.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.E213U10

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Plan

variable {d : ℕ} {S : PreparedData d} {β₀ m : ℝ}

theorem u10_zetaAt_embed (hE : EdgeworthHyp S β₀ m) {N : ℕ} {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → Config d N) (hX : ∀ t : ℝ≥0, Measurable (X t)) (t : ℝ) (ω : Ω) :
    zetaAt m P X t ω = NegSobolev.embed m (zetaAt (rLvl d) P X t ω) := by
  haveI : IsProbabilityMeasure (P.map (X t.toNNReal)) :=
    (Measure.isProbabilityMeasure_map_iff (hX _).aemeasurable).2 inferInstance
  haveI : IsProbabilityMeasure (Measure.dirac (0 : Torus d)) := inferInstance
  exact (HRS.MC.E213U6.etaE_zetaE_embed_proof hE (P.map (X t.toNNReal)) (X t.toNNReal ω)
    (Measure.dirac (0 : Torus d))).2

theorem u10_etaE_embed (hE : EdgeworthHyp S β₀ m) {N : ℕ} (x : Config d N) (μ : Measure (Torus d))
    [IsProbabilityMeasure μ] : etaE m x μ = NegSobolev.embed m (etaE (rLvl d) x μ) := by
  haveI : IsProbabilityMeasure (Measure.dirac x) := inferInstance
  exact (HRS.MC.E213U6.etaE_zetaE_embed_proof hE (Measure.dirac x) x μ).1

theorem u10_embed_continuous (hE : EdgeworthHyp S β₀ m) :
    Continuous (NegSobolev.embed m : NegSobolev d (rLvl d) → NegSobolev d m) :=
  (HRS.MD.EQInterp.embedCLM (rLvl_le hE)).continuous

/-- The horizon-`(a+T)` particle window agrees on `[b,a+T]` with the lift of the level-`r` window starting at `b`. -/
theorem u10_particle_hW (hE : EdgeworthHyp S β₀ m) (T a b L : ℝ) (hb : 0 ≤ b) (hL : 0 ≤ L) (hH : a + T ≤ b + L)
    {N : ℕ} {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → Config d N) (hX : ∀ t : ℝ≥0, Measurable (X t)) (ω : Ω)
    (hz1 : Continuous fun t : Set.Icc (0 : ℝ) L => zetaAt (rLvl d) P X (b + (t : ℝ)) ω)
    (hz2 : Continuous fun t : Set.Icc (0 : ℝ) (a + T) => zetaAt (rLvl d) P X (0 + (t : ℝ)) ω) :
    ∀ t ∈ Set.Icc b (a + T), pathAt (zetaWin m (a + T) 0 P X ω) t =
      pathAt (u10_liftW hE b L (a + T) hL hH (zetaWin (rLvl d) L b P X ω)) t := by
  intro t ht
  have ht0 : t ∈ Set.Icc (0 : ℝ) (a + T) := ⟨hb.trans ht.1, ht.2⟩
  have htb : t - b ∈ Set.Icc (0 : ℝ) L := ⟨sub_nonneg.2 ht.1, by linarith [ht.2]⟩
  rw [u10_liftW_pathAt hE b L (a + T) hL hH _ ht0 ht.1]
  have e1 : pathAt (zetaWin m (a + T) 0 P X ω) t = zetaAt m P X (0 + t) ω := by
    show pathAt (toPath m (a + T) (fun t ω => zetaAt m P X (0 + t) ω) ω) t = _
    refine u10_pathAt_toPath m (a + T) (fun t ω => zetaAt m P X (0 + t) ω) ω ?_ ht0
    have : (fun t : Set.Icc (0 : ℝ) (a + T) => zetaAt m P X (0 + (t : ℝ)) ω) =
        fun t : Set.Icc (0 : ℝ) (a + T) => NegSobolev.embed m (zetaAt (rLvl d) P X (0 + (t : ℝ)) ω) :=
      funext fun t => u10_zetaAt_embed hE P X hX _ ω
    rw [this]
    exact (u10_embed_continuous hE).comp hz2
  have e2 : pathAt (zetaWin (rLvl d) L b P X ω) (t - b) = zetaAt (rLvl d) P X (b + (t - b)) ω := by
    show pathAt (toPath (rLvl d) L (fun t ω => zetaAt (rLvl d) P X (b + t) ω) ω) (t - b) = _
    exact u10_pathAt_toPath (rLvl d) L (fun t ω => zetaAt (rLvl d) P X (b + t) ω) ω hz1 htb
  rw [e1, e2, u10_zetaAt_embed hE P X hX]
  have : (0 : ℝ) + t = b + (t - b) := by ring
  rw [this]

theorem u10_particle_A (hE : EdgeworthHyp S β₀ m) (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a)
    (Φ : PathSpace d m T → ℝ) (hΦ : MemCb 5 Φ) (b L : ℝ) (hb : 0 ≤ b) (hba : b ≤ a) (hL : 0 < L)
    (hH : a + T ≤ b + L) {N : ℕ} (hN : 2 ≤ N) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N)
    (hprep : PreparedRealization (regime S β₀ hE).D P
      (modulatedGibbs (periodicRiesz d (regime S β₀ hE).D.s) N (regime S β₀ hE).β₀
        (withDensityReal (regime S β₀ hE).ρ₀)) X₀ W X) :
    ∀ᵐ ω ∂P, rsA (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) (zetaWin m (a + T) 0 P X ω)
        (nearCoef b (fun v => quadFieldAt m (regime S β₀ hE).D.s
          (fun t => withDensityReal ((regime S β₀ hE).ρ t)) P X v ω)) =
      u10_FD hE T a ha Φ b L hL.le hH
        (pairN (rLvl d) L b (regime S β₀ hE).D.s (regime S β₀ hE).ρ P X ω) := by
  have hr : rLvl d = 2 * (d : ℝ) + 6 := rfl
  have hN1 : 1 ≤ N := by omega
  have hB := u10_B_memLp_ae (regime S β₀ hE) (rLvl d) hr b L hb hL hN P X₀ W X hprep
  have hz1 := (HRS.MC.Sec7.S7UCD.S7UCD_honest (regime S β₀ hE) (rLvl d) hr L hN1 P X₀ W X hprep b hb).2
  have hz2 := (HRS.MC.Sec7.S7UCD.S7UCD_honest (regime S β₀ hE) (rLvl d) hr (a + T) hN1 P X₀ W X hprep 0 le_rfl).2
  have hadapt : ∀ t : ℝ≥0, Measurable (X t) := (hprep.solution 0).adapted
  filter_upwards [hB, hz1, hz2] with ω hBω hz1ω hz2ω
  have hW0 := u10_particle_hW hE T a b L hb hL.le hH P X hadapt ω hz1ω hz2ω
  have hc : ∀ v, nearCoef b (fun v => quadFieldAt m (regime S β₀ hE).D.s
        (fun t => withDensityReal ((regime S β₀ hE).ρ t)) P X v ω) v =
      if b ≤ v then NegSobolev.embed m (quadFieldAt (rLvl d) (regime S β₀ hE).D.s
        (fun t => withDensityReal ((regime S β₀ hE).ρ t)) P X v ω) else 0 := by
    intro v
    unfold nearCoef
    by_cases h : b ≤ v
    · simp only [if_pos h]
      exact HRS.MC.E213U6.quadFieldAt_embed_proof hE N hN P X₀ W X hprep v (hb.trans h) ω
    · simp only [if_neg h]
  exact u10_rsA_eq_FD hE T hT a ha Φ hΦ b L hb hba hL.le hH _ _ hW0 _ _
    (u10_cD_ae_eq hE T a b L hH (fun v => quadFieldAt (rLvl d) (regime S β₀ hE).D.s
      (fun t => withDensityReal ((regime S β₀ hE).ρ t)) P X v ω) hBω _ hc)

theorem u10_particle_J (hE : EdgeworthHyp S β₀ m) (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a)
    (Φ : PathSpace d m T → ℝ) (hΦ : MemCb 5 Φ) (b L : ℝ) (hb : 0 ≤ b) (hba : b ≤ a) (hL : 0 < L)
    (hH : a + T ≤ b + L) {N : ℕ} (hN : 2 ≤ N) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N)
    (hprep : PreparedRealization (regime S β₀ hE).D P
      (modulatedGibbs (periodicRiesz d (regime S β₀ hE).D.s) N (regime S β₀ hE).β₀
        (withDensityReal (regime S β₀ hE).ρ₀)) X₀ W X)
    (mm : PathSpace d (rLvl d) L)
    (hmm : ∀ᵐ ω ∂P, zetaWin (rLvl d) L b P X ω =
      HRS.Main.windowFluc (rLvl d) L b (Real.sqrt N) X (regime S β₀ hE).ρ ω - mm) :
    ∀ᵐ ω ∂P, rsJ (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) (zetaWin m (a + T) 0 P X ω)
        (nearCoef b (fun v => etaE m (X v.toNNReal ω) (withDensityReal ((regime S β₀ hE).ρ v)))) =
      u10_GJ hE T a ha Φ b L hL.le hH mm
        (pairN (rLvl d) L b (regime S β₀ hE).D.s (regime S β₀ hE).ρ P X ω) := by
  have hr : rLvl d = 2 * (d : ℝ) + 6 := rfl
  have hN1 : 1 ≤ N := by omega
  have hh := HRS.MC.Sec7.S7UCD.S7UCD_honest (regime S β₀ hE) (rLvl d) hr L hN1 P X₀ W X hprep b hb
  have hz2 := (HRS.MC.Sec7.S7UCD.S7UCD_honest (regime S β₀ hE) (rLvl d) hr (a + T) hN1 P X₀ W X hprep 0 le_rfl).2
  have hadapt : ∀ t : ℝ≥0, Measurable (X t) := (hprep.solution 0).adapted
  filter_upwards [hh.1, hh.2, hz2, hmm] with ω hηω hz1ω hz2ω hmmω
  have hW0 := u10_particle_hW hE T a b L hb hL.le hH P X hadapt ω hz1ω hz2ω
  have hsum : zetaWin (rLvl d) L b P X ω + mm = HRS.Main.windowFluc (rLvl d) L b (Real.sqrt N) X
      (regime S β₀ hE).ρ ω := by rw [hmmω]; abel
  refine u10_rsJ_eq_FJ hE T hT a ha Φ hΦ b L hb hba hL.le hH _ (zetaWin (rLvl d) L b P X ω) hW0 _
    (zetaWin (rLvl d) L b P X ω + mm) ?_
  intro v hv0 hva
  unfold nearCoef u10_cJ nearCoef
  by_cases hbv : b ≤ v
  · simp only [if_pos hbv]
    have hvb : v - b ∈ Set.Icc (0 : ℝ) L := ⟨sub_nonneg.2 hbv, by linarith⟩
    haveI := isProb_withDensityReal (HRS.MC.Sec7.S7FCD5B.S7FCD5B_hdens (regime S β₀ hE) v hv0)
    rw [u10_etaE_embed hE]
    congr 1
    unfold u10_zq
    rw [hsum, HRS.MC.Sec7.S7UCD.S7UCD_windowFluc_eq (regime S β₀ hE) (rLvl d) L X b hb ω]
    rw [u10_pathAt_toPath (rLvl d) L (fun t ω => etaE (rLvl d) (X (b + t).toNNReal ω)
      (withDensityReal ((regime S β₀ hE).ρ (b + t)))) ω hηω hvb]
    have e : b + (v - b) = v := by ring
    rw [e]
  · simp only [if_neg hbv]

end HRS.MC.E213U10

end
