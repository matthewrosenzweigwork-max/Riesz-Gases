import HRS.MS.R2ChaosAux42

/-!
# HRS.MS.R2ChaosAux43 -- (b) part 1: uniform `L²` bounds

Packet S94, namespace `HRS.MS.R2Chaos`, helper prefix `s94_`.

* `s94_env_L2_bound`: `‖k‖_{L²(μ⊗μ)} ≤ κ_B` for every `IsBoundedPairKernel s B k`.
* `s94_flim_bound`: `‖Φ_m(t,·)‖_{L²(P')} ≤ C` uniformly in `m` and `t ∈ [0,T]` (Wick isometry, `‖cen‖ ≤ 4`).
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

section Bounds

variable {s T b p K M L : ℝ} {ρ : Euc d → ℝ} {Ω : ℕ → Type} [∀ N, MeasurableSpace (Ω N)]
  {P : ∀ N, Measure (Ω N)} [∀ N, IsProbabilityMeasure (P N)] {X : ∀ N, ℝ≥0 → Ω N → EucConfig d N}
  {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
  {ξ : (Euc d → ℝ) → Ω' → C(Set.Icc (0 : ℝ) T, ℝ)}

theorem s94_env_L2_bound (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (hρ : IsRound2Density d s M L ρ)
    (B : ℝ) (hB : 0 ≤ B) :
    ∃ κ : ℝ, 0 ≤ κ ∧ ∀ {k : Euc d → Euc d → ℝ}, IsBoundedPairKernel s B k →
      eLpNorm (fun q : Euc d × Euc d => k q.1 q.2) 2
        ((Whole.withDensityReal ρ).prod (Whole.withDensityReal ρ)) ≤ ENNReal.ofReal κ := by
  haveI : IsProbabilityMeasure (Whole.withDensityReal ρ) := HRS.Whole.U1.u1_isProb hρ.prob
  have hG := s94_env_memLp hd hs0 hs hρ (s94_Gker (s := s) (d := d) B hB)
  set G : ℝ≥0∞ := eLpNorm (fun q : Euc d × Euc d => B * (1 + rieszWeight s (q.1 - q.2))) 2
    ((Whole.withDensityReal ρ).prod (Whole.withDensityReal ρ)) with hGdef
  have hGfin : G ≠ ⊤ := hG.eLpNorm_ne_top
  refine ⟨G.toReal, ENNReal.toReal_nonneg, fun {k} hk => ?_⟩
  rw [ENNReal.ofReal_toReal hGfin, hGdef]
  have hae : ∀ᵐ q ∂((Whole.withDensityReal ρ).prod (Whole.withDensityReal ρ)),
      ‖k q.1 q.2‖ ≤ ‖B * (1 + rieszWeight s (q.1 - q.2))‖ := by
    filter_upwards [s94_ae_offdiag hd hρ] with q hq
    have h1 := hk.bound q.1 q.2 hq
    have hW := HRS.MS.Wr.wr3_rieszWeight_nonneg (d := d) s (q.1 - q.2)
    have hpos : 0 ≤ B * (1 + rieszWeight s (q.1 - q.2)) := by positivity
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hpos]
    exact h1
  exact eLpNorm_mono_ae hk.measurable.aestronglyMeasurable hae

theorem s94_flim_bound (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (hρ : IsRound2Density d s M L ρ)
    (hset : IsRound2PathSetting d s T b p K (Whole.withDensityReal ρ) P X P' ξ) {Λ : ℝ}
    (hcov : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ a, IsR2Test a →
      ∫ ζ, (r2PathEval T (ξ a ζ) t) ^ 2 ∂P' ≤ Λ * ∫ x, (Whole.projMean (Whole.withDensityReal ρ) a x) ^ 2 ∂(Whole.withDensityReal ρ))
    (hΛ0 : 0 ≤ Λ) {a : ℕ → Euc d → ℝ} (ha : IsR2ZeroMeanONB (Whole.withDensityReal ρ) a) {B' : ℝ} (hB' : 0 ≤ B')
    {n : ℕ → ℕ} {u : ∀ m, Fin (n m) → Euc d → ℝ} {Cm : ∀ m, ℝ → Fin (n m) → Fin (n m) → ℝ}
    (hu : ∀ m a, IsR2Test (u m a)) (hCs : ∀ m t a b, Cm m t a b = Cm m t b a)
    (hbd : ∀ m t, t ∈ Set.Icc (0 : ℝ) T → IsBoundedPairKernel s B' (r2FiniteRankKernel (Cm m t) (u m))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ m, eLpNorm (fun ζ => s94Flim ξ P' (Cm m) (u m) t ζ) 2 P' ≤
      ENNReal.ofReal C := by
  haveI : IsProbabilityMeasure (Whole.withDensityReal ρ) := HRS.Whole.U1.u1_isProb hρ.prob
  obtain ⟨κ, hκ0, hκ⟩ := s94_env_L2_bound hd hs0 hs hρ B' hB'
  refine ⟨2 * Real.sqrt 2 * Λ * κ, by positivity, fun t ht m => ?_⟩
  obtain ⟨ha0, hon, hcomplete⟩ := ha
  have hz := s94_gseq_of_setting hset hcov hΛ0 ha0 hon ht
  set μ := Whole.withDensityReal ρ with hμ
  set ν := μ.prod μ with hν
  let Qm : Ω' → ℝ := fun ζ => ∑ α, ∑ β, Cm m t α β * (r2PathEval T (ξ (u m α) ζ) t *
    r2PathEval T (ξ (u m β) ζ) t - ∫ ζ', r2PathEval T (ξ (u m α) ζ') t * r2PathEval T (ξ (u m β) ζ') t ∂P')
  have hch := s94_wick_finiteRank hset hcov hΛ0 ha0 hon hcomplete (Cm m t) (hu m) ht
  have hF : ∀ ζ, s94Flim ξ P' (Cm m) (u m) t ζ = (1 / 2) * Qm ζ := by
    intro ζ
    unfold s94Flim
    rw [Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun β _ => ?_
    ring
  have hzero : s94WickL2 P' μ a (fun i ζ => r2PathEval T (ξ (a i) ζ) t) (fun _ _ => (0 : ℝ)) (fun _ => (0 : ℝ)) := by
    refine ⟨MemLp.zero, ?_⟩
    simp [s94Sec, r2WickCoeff]
  have hk := hbd m t ht
  have hm1 := s94_finiteRank_measurable (c := Cm m t) (u := u m) (hu m)
  have hlip := s94_wick_lipschitz hz hΛ0 ha0 hon
    (s94_center_measurable (μ := μ) hm1) (s94_center_symm (s94_finiteRank_symm (hCs m t)))
    (s94_center_memLp hd hs0 hs hρ hk) (k' := fun _ _ => (0 : ℝ)) measurable_const (fun _ _ => rfl)
    MemLp.zero hch hzero
  have hcen : eLpNorm (fun q : Euc d × Euc d => r2CenterKernel μ (r2FiniteRankKernel (Cm m t) (u m)) q.1 q.2 - 0) 2 ν
      ≤ ENNReal.ofReal (4 * κ) := by
    have := s94_eLpNorm_center_le (μ := μ) hm1
    simp only [sub_zero]
    refine this.trans ?_
    rw [ENNReal.ofReal_mul (by norm_num)]
    have e4 : ENNReal.ofReal 4 = 4 := by norm_num
    rw [e4]
    gcongr
    exact hκ hk
  have hsq := s94_integral_sq_le_of_eLpNorm
    (((s94_center_measurable (μ := μ) hm1).sub measurable_const).aestronglyMeasurable) (by positivity) hcen
  have hQQ : eLpNorm (fun ζ => Qm ζ - 0) 2 P' ≤ ENNReal.ofReal (Real.sqrt 2 * Λ * (4 * κ)) := by
    refine s94_eLpNorm_le_of_sq (hch.1.sub MemLp.zero) (by positivity) ?_
    calc _ ≤ 2 * Λ ^ 2 * ∫ q, (r2CenterKernel μ (r2FiniteRankKernel (Cm m t) (u m)) q.1 q.2 - 0) ^ 2 ∂ν := hlip
      _ ≤ 2 * Λ ^ 2 * (4 * κ) ^ 2 := mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = (Real.sqrt 2 * Λ * (4 * κ)) ^ 2 := by
        rw [show (Real.sqrt 2 * Λ * (4 * κ)) ^ 2 = Real.sqrt 2 ^ 2 * Λ ^ 2 * (4 * κ) ^ 2 by ring,
          Real.sq_sqrt (by norm_num)]
  have e2 : (fun ζ => s94Flim ξ P' (Cm m) (u m) t ζ) = (1 / 2 : ℝ) • (fun ζ => Qm ζ - 0) := by
    funext ζ
    simp only [hF, Pi.smul_apply, smul_eq_mul]
    ring
  rw [e2, eLpNorm_const_smul]
  calc ‖(1 / 2 : ℝ)‖ₑ * eLpNorm (fun ζ => Qm ζ - 0) 2 P'
      ≤ ‖(1 / 2 : ℝ)‖ₑ * ENNReal.ofReal (Real.sqrt 2 * Λ * (4 * κ)) := by gcongr
    _ = ENNReal.ofReal (2 * Real.sqrt 2 * Λ * κ) := by
      rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_mul (norm_nonneg _)]
      congr 1
      rw [Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      ring

end Bounds

end HRS.MS.R2Chaos
