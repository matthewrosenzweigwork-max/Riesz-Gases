import HRS.MS.R2ChaosAux28

/-!
# HRS.MS.R2ChaosAux29 -- R3 (part 1): S9.2 along the time marginals for differences of kernels

Packet S94, namespace `HRS.MS.R2Chaos`, helper prefix `s94_`.

* `s94_rowOKE`: envelope-bounded kernels are `RowOKE` (so `pairEnergy` is additive in the kernel).
* `s94_time_bounds`: uniform `L^r(P_N)` bounds for `N F_N^k(X_N^t)` (and centered), `t ∈ [0,T]`, `k` in the class `B'`.
* `s94_time_tail`: for `IsRound2Approx` data at time `t`, `sup_N ‖N (F^{k_j - h_t} - E)‖_{L²(P_N)} → 0`.
* `s94_quad_diff`: `B^{k₁}_N(t) - B^{k₂}_N(t) = N (F^{k₁ - k₂} - E F^{k₁ - k₂})`.
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

section R3a

variable {s : ℝ}

theorem s94_rowOKE (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {M L B : ℝ} {ρ : Euc d → ℝ}
    (hρ : IsRound2Density d s M L ρ) {h : Euc d → Euc d → ℝ} (hh : IsBoundedPairKernel s B h) :
    HRS.MS.Wr.RowOKE (Whole.withDensityReal ρ) h := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hsd : s < (d : ℝ) := by linarith
  have hB := s94_B_nonneg hd hh
  haveI : IsProbabilityMeasure (Whole.withDensityReal ρ) := HRS.Whole.U1.u1_isProb hρ.prob
  have hle : Whole.withDensityReal ρ ≤ ENNReal.ofReal 1 • Whole.withDensityReal ρ := by simp
  refine ⟨hh.measurable, (s94_env_facts hd hs0 hs hρ hh).1, ?_⟩
  obtain ⟨c, hc0, hc⟩ := HRS.MS.Wr.wr14a_Hc_bound (d := d) (by omega) hs0 hsd M
  refine ⟨c * 1 * B, fun x => ?_⟩
  have := hc hρ.prob hρ.bdd hle zero_le_one hB (h := fun x y => |h x y|)
    (fun x y hxy => by simpa using hh.bound x y hxy) x
  simp only [HRS.MS.Wr.wr14a_Hc] at this
  exact (le_abs_self _).trans this

theorem s94_finiteRank_symm {m : ℕ} {c : Fin m → Fin m → ℝ} {u : Fin m → Euc d → ℝ}
    (hc : ∀ a b, c a b = c b a) (x y : Euc d) :
    r2FiniteRankKernel c u x y = r2FiniteRankKernel c u y x := by
  unfold r2FiniteRankKernel
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [hc a b]; ring

/-- An `IsRound2Approx` element is an `IsBoundedPairKernel` with constant `C B`. -/
theorem s94_approx_bounded {C₁ B : ℝ} {μ : Measure (Euc d)} {h : Euc d → Euc d → ℝ}
    {hj : ℕ → Euc d → Euc d → ℝ} (hA : IsRound2Approx s C₁ B μ h hj) (j : ℕ) :
    IsBoundedPairKernel s (C₁ * B) (hj j) := by
  obtain ⟨m, c, u, hd0, he⟩ := hA.finiteRank j
  have hut : ∀ a, IsR2Test (u a) := fun a => ⟨hd0.smooth a, hd0.compactSupport a⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [he]; exact s94_finiteRank_measurable hut
  · intro x y; rw [he]; exact s94_finiteRank_symm hd0.symm x y
  · intro x y hxy
    exact hA.envelope j x y hxy

end R3a

section R3b

variable {s T b p K M L : ℝ} {ρ : Euc d → ℝ} {Ω : ℕ → Type} [∀ N, MeasurableSpace (Ω N)]
  {P : ∀ N, Measure (Ω N)} [∀ N, IsProbabilityMeasure (P N)] {X : ∀ N, ℝ≥0 → Ω N → EucConfig d N}
  {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
  {ξ : (Euc d → ℝ) → Ω' → C(Set.Icc (0 : ℝ) T, ℝ)}

theorem s94_pushforward_prob (hset : IsRound2PathSetting d s T b p K (Whole.withDensityReal ρ) P X P' ξ) (N : ℕ)
    (t : ℝ≥0) : Measurable (X N t) := (hset.measX N).comp measurable_prodMk_left

theorem s94_pE_meas_config {N : ℕ} {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {k : Euc d → Euc d → ℝ}
    (hk : Measurable fun q : Euc d × Euc d => k q.1 q.2) :
    Measurable fun Z : EucConfig d N => pairEnergy k Z μ := by
  have h0 : Measurable fun q : ℝ × Euc d × Euc d => (fun (_ : ℝ) => k) q.1 q.2.1 q.2.2 :=
    Measurable.comp (g := fun q : Euc d × Euc d => k q.1 q.2) (f := fun q : ℝ × Euc d × Euc d => q.2) hk measurable_snd
  have h1 := s94_pairEnergy_measurable (N := N) (μ := μ) (h := fun _ => k) h0
  exact Measurable.comp (g := fun q : ℝ × EucConfig d N => pairEnergy ((fun (_ : ℝ) => k) q.1) q.2 μ)
    (f := fun Z : EucConfig d N => ((0 : ℝ), Z)) h1 (measurable_const.prodMk measurable_id)

/-- Uniform `L^r(P_N)` bounds for `N F_N^k(X_N^t)` and its centered version along the time marginals. -/
theorem s94_time_bounds (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (hb : 0 < b) (hp : 1 < p)
    (hρ : IsRound2Density d s M L ρ)
    (hset : IsRound2PathSetting d s T b p K (Whole.withDensityReal ρ) P X P' ξ) (B' : ℝ) {r : ℝ} (hr : 1 ≤ r) :
    ∃ C : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ N : ℕ, 2 ≤ N → ∀ k : Euc d → Euc d → ℝ, IsBoundedPairKernel s B' k →
      eLpNorm (fun ζ => (N : ℝ) * pairEnergy k (X N t.toNNReal ζ) (Whole.withDensityReal ρ))
        (ENNReal.ofReal r) (P N) ≤ ENNReal.ofReal C ∧
      eLpNorm (fun ζ => (N : ℝ) * (pairEnergy k (X N t.toNNReal ζ) (Whole.withDensityReal ρ) -
        ∫ ζ', pairEnergy k (X N t.toNNReal ζ') (Whole.withDensityReal ρ) ∂(P N)))
        (ENNReal.ofReal r) (P N) ≤ ENNReal.ofReal C := by
  haveI : IsProbabilityMeasure (Whole.withDensityReal ρ) := HRS.Whole.U1.u1_isProb hρ.prob
  obtain ⟨C, hC⟩ := HRS.MS.R2Mt.round2_moment_transfer_proof hd s hs0 hs M L b p K B' hb hp r hr
  refine ⟨C, fun t ht N hN k hk => ?_⟩
  have hmX : Measurable (X N t.toNNReal) := s94_pushforward_prob hset N _
  have hF := (hC ρ hρ (fun N' => (P N').map (X N' t.toNNReal)) (fun N' hN' => hset.density N' hN' t ht)).1 k hk
    () N hN
  obtain ⟨hF1, hF2⟩ := hF
  have hmeas := s94_pE_meas_config (N := N) (μ := Whole.withDensityReal ρ) hk.measurable
  have hg1 : AEStronglyMeasurable (fun Z : EucConfig d N => (N : ℝ) * pairEnergy k Z (Whole.withDensityReal ρ))
      ((P N).map (X N t.toNNReal)) := (hmeas.const_mul _).aestronglyMeasurable
  have hg2 : AEStronglyMeasurable (fun Z : EucConfig d N => (N : ℝ) * (pairEnergy k Z (Whole.withDensityReal ρ) -
      ∫ Y, pairEnergy k Y (Whole.withDensityReal ρ) ∂((P N).map (X N t.toNNReal))))
      ((P N).map (X N t.toNNReal)) := ((hmeas.sub measurable_const).const_mul _).aestronglyMeasurable
  have hint : ∫ Y, pairEnergy k Y (Whole.withDensityReal ρ) ∂((P N).map (X N t.toNNReal)) =
      ∫ ζ', pairEnergy k (X N t.toNNReal ζ') (Whole.withDensityReal ρ) ∂(P N) :=
    integral_map hmX.aemeasurable hmeas.aestronglyMeasurable
  have e1 : eLpNorm (fun ζ => (N : ℝ) * pairEnergy k (X N t.toNNReal ζ) (Whole.withDensityReal ρ))
      (ENNReal.ofReal r) (P N) = eLpNorm (fun Z : EucConfig d N => (N : ℝ) * pairEnergy k Z (Whole.withDensityReal ρ))
      (ENNReal.ofReal r) ((P N).map (X N t.toNNReal)) := by
    rw [eLpNorm_map_measure hg1 hmX.aemeasurable]; rfl
  have e2 : eLpNorm (fun ζ => (N : ℝ) * (pairEnergy k (X N t.toNNReal ζ) (Whole.withDensityReal ρ) -
        ∫ ζ', pairEnergy k (X N t.toNNReal ζ') (Whole.withDensityReal ρ) ∂(P N))) (ENNReal.ofReal r) (P N) =
      eLpNorm (fun Z : EucConfig d N => (N : ℝ) * (pairEnergy k Z (Whole.withDensityReal ρ) -
        ∫ Y, pairEnergy k Y (Whole.withDensityReal ρ) ∂((P N).map (X N t.toNNReal))))
        (ENNReal.ofReal r) ((P N).map (X N t.toNNReal)) := by
    rw [eLpNorm_map_measure hg2 hmX.aemeasurable]
    simp only [Function.comp_def, hint]
  exact ⟨e1.le.trans hF1, e2.le.trans hF2⟩

end R3b

end HRS.MS.R2Chaos
