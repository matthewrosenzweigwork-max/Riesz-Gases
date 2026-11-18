import HRS.Sections.AdjKGlueAux6

/-!
# ADJK-GLUE, part 7: honest paths, measurability and the finite-`n` modulus
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

universe u

namespace HRS.AdjK

open HRS.Uniform

variable {d : ℕ} {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}

theorem adjkg_coord_fourier {m : ℝ} (F : NegSobolev d m) (k : NonzeroLattice d) :
    NegSobolev.coord F k = Lattice.jp k.1 ^ (-m) * NegSobolev.fourierCoeff F k := by
  unfold NegSobolev.fourierCoeff
  rw [← mul_assoc, ← Real.rpow_add (Torus.jp_pos _)]
  simp

theorem adjkg_energy_eq_fourier {m m₁ : ℝ} (F : NegSobolev d m) :
    adjkEnergy m₁ m F = ∑' k : NonzeroLattice d,
      ENNReal.ofReal (Lattice.jp k.1 ^ (-2 * m₁) * NegSobolev.fourierCoeff F k ^ 2) := by
  unfold adjkEnergy
  refine tsum_congr fun k => ?_
  congr 1
  rw [adjkg_coord_fourier, mul_pow, Torus.jp_rpow_sq, ← mul_assoc, ← Real.rpow_add (Torus.jp_pos _)]
  congr 2
  ring

theorem adjkg_fourier_sub {m : ℝ} (F G : NegSobolev d m) (k : NonzeroLattice d) :
    NegSobolev.fourierCoeff (F - G) k = NegSobolev.fourierCoeff F k - NegSobolev.fourierCoeff G k := by
  unfold NegSobolev.fourierCoeff
  rw [adjkg_coord_sub, mul_sub]

theorem adjkg_fourier_add {m : ℝ} (F G : NegSobolev d m) (k : NonzeroLattice d) :
    NegSobolev.fourierCoeff (F + G) k = NegSobolev.fourierCoeff F k + NegSobolev.fourierCoeff G k := by
  unfold NegSobolev.fourierCoeff
  rw [adjkg_coord_add, mul_add]

theorem adjkg_flucPath_at {Ω : Type*} {N : ℕ} (m T σ : ℝ) (X : ℝ≥0 → Ω → Config d N)
    (ρ : ℝ → Torus d → ℝ) (ω : Ω)
    (hc : Continuous fun t : Set.Icc (0 : ℝ) T => σ • NegSobolev.ofMeasureDiff m
      (empirical (X (Real.toNNReal t) ω)) (withDensityReal (ρ t))) (t : Set.Icc (0 : ℝ) T) :
    (flucPath m T σ X ρ ω).at' t = σ • NegSobolev.ofMeasureDiff m
      (empirical (X (Real.toNNReal t) ω)) (withDensityReal (ρ t)) := by
  have e : flucPath m T σ X ρ ω = (show PathSpace d m T from
      (⟨fun t : Set.Icc (0 : ℝ) T => σ • NegSobolev.ofMeasureDiff m
        (empirical (X (Real.toNNReal t) ω)) (withDensityReal (ρ t)), hc⟩ :
        C(Set.Icc (0 : ℝ) T, NegSobolev d m))) := by
    unfold flucPath
    exact dif_pos hc
  rw [e]
  rfl

theorem adjkg_etaE_measurable {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} (m : ℝ) (hm : (d : ℝ) / 2 < m)
    (μ : Measure (Torus d)) (Y : Ω → Config d N) (hY : Measurable Y) :
    Measurable (fun ω => etaE m (Y ω) μ) := by
  unfold etaE flucE
  exact (measurable_const_smul _).comp ((GF.gf_measurable_ofMeasureDiff_proof (N := N) m hm μ).comp hY)

/-- For a measurable random path the probability of a large modulus tends to `0` with the window. -/
theorem adjkg_modulus_small {m T : ℝ} (hT : 0 ≤ T) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Ξ : Ω → PathSpace d m T) (hΞ : AEMeasurable Ξ P) {η : ℝ} (hη : 0 < η)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ P {ω | ∃ s t : Set.Icc (0 : ℝ) T, |(s : ℝ) - t| ≤ δ ∧
      η < ‖(Ξ ω).at' s - (Ξ ω).at' t‖} ≤ ENNReal.ofReal ε := by
  set U : ℕ → Set (PathSpace d m T) := fun k => {w | ∃ s t : Set.Icc (0 : ℝ) T,
    |(s : ℝ) - t| ≤ 1 / ((k : ℝ) + 1) ∧ η < ‖w.at' s - w.at' t‖} with hU
  have hUopen : ∀ k, IsOpen (U k) := by
    intro k
    have : U k = ⋃ (s : Set.Icc (0 : ℝ) T) (t : Set.Icc (0 : ℝ) T)
        (_ : |(s : ℝ) - t| ≤ 1 / ((k : ℝ) + 1)), {w : PathSpace d m T | η < ‖w.at' s - w.at' t‖} := by
      ext w
      simp only [hU, Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
    rw [this]
    refine isOpen_iUnion fun s => isOpen_iUnion fun t => isOpen_iUnion fun _ => ?_
    refine isOpen_lt continuous_const ?_
    have hev : ∀ r : Set.Icc (0 : ℝ) T, Continuous fun w : PathSpace d m T => w.at' r := fun r => by
      show Continuous fun w : C(Set.Icc (0 : ℝ) T, NegSobolev d m) => w r
      exact continuous_eval_const r
    exact ((hev s).sub (hev t)).norm
  have hanti : Antitone U := by
    intro k l hkl w ⟨s, t, hst, h⟩
    refine ⟨s, t, hst.trans ?_, h⟩
    have : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hkl 1)
  haveI : IsProbabilityMeasure (P.map Ξ) := (Measure.isProbabilityMeasure_map_iff hΞ).2 inferInstance
  have hinter : (⋂ k, U k) = ∅ := by
    ext w
    simp only [mem_iInter, mem_empty_iff_false, iff_false, not_forall]
    by_contra hall
    push_neg at hall
    haveI : CompactSpace (Set.Icc (0 : ℝ) T) := isCompact_iff_compactSpace.1 isCompact_Icc
    have hucont : UniformContinuous (show C(Set.Icc (0 : ℝ) T, NegSobolev d m) from w) :=
      CompactSpace.uniformContinuous_of_continuous (show C(Set.Icc (0 : ℝ) T, NegSobolev d m) from w).continuous
    rw [Metric.uniformContinuous_iff] at hucont
    obtain ⟨δ, hδ, hδw⟩ := hucont η hη
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hδ
    obtain ⟨s, t, hst, h⟩ := hall k
    have hd : dist s t < δ := by
      rw [Subtype.dist_eq, Real.dist_eq]
      exact lt_of_le_of_lt hst hk
    have := hδw hd
    rw [dist_eq_norm] at this
    exact absurd h (not_lt.2 this.le)
  have htend := tendsto_measure_iInter_atTop (μ := P.map Ξ) (s := U)
    (fun k => (hUopen k).measurableSet.nullMeasurableSet) hanti ⟨0, measure_ne_top _ _⟩
  rw [hinter, measure_empty] at htend
  have hev : ∀ᶠ k in atTop, (P.map Ξ) (U k) < ENNReal.ofReal ε :=
    (htend.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 hε)))
  obtain ⟨k, hk⟩ := hev.exists
  refine ⟨1 / ((k : ℝ) + 1), by positivity, ?_⟩
  have : P {ω | ∃ s t : Set.Icc (0 : ℝ) T, |(s : ℝ) - t| ≤ 1 / ((k : ℝ) + 1) ∧
      η < ‖(Ξ ω).at' s - (Ξ ω).at' t‖} = (P.map Ξ) (U k) := by
    rw [Measure.map_apply_of_aemeasurable hΞ (hUopen k).measurableSet]
    rfl
  rw [this]
  exact hk.le

end HRS.AdjK
