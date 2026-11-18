import HRS.MS.R2ChaosAux36

/-!
# HRS.MS.R2ChaosAux37 -- R4 (part 2): the Gaussian-side finite-rank integrands are `L²(P')`-Cauchy at every time

Packet S94, namespace `HRS.MS.R2Chaos`, helper prefix `s94_`.

`s94_flim_cauchy`: if `(Cm m, u m)` approximate `h_t` as in R1 (`IsRound2Approx` at the time `t`) and an orthonormal basis `a`
of `L²_0(μ)` by projected tests exists, then `Φ_m(t,·) = s94Flim ξ P' (Cm m) (u m) t ·` is Cauchy in `L²(P')`
(chaos of `cen(FR_m)` is `2 Φ_m` for the basis `a`; the Wick chaos is `Λ`-Lipschitz in the kernel; `cen` is `4`-bounded).
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

theorem s94_eLpNorm_le_of_sq {α : Type*} [MeasurableSpace α] {ν : Measure α} {f : α → ℝ} (hf : MemLp f 2 ν)
    {a : ℝ} (ha : 0 ≤ a) (h : ∫ x, f x ^ 2 ∂ν ≤ a ^ 2) : eLpNorm f 2 ν ≤ ENNReal.ofReal a := by
  have h1 : eLpNorm f 2 ν ^ 2 = ENNReal.ofReal (∫ x, f x ^ 2 ∂ν) := by
    rw [← s94_lintegral_sq_eq hf.aestronglyMeasurable,
      ofReal_integral_eq_lintegral_ofReal hf.integrable_sq (ae_of_all _ fun x => sq_nonneg _)]
    refine lintegral_congr fun x => ?_
    rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _), Real.norm_eq_abs, sq_abs]
  by_contra hlt
  have h2 := ENNReal.pow_lt_pow_left two_ne_zero (not_le.1 hlt)
  rw [h1, ← ENNReal.ofReal_pow ha] at h2
  exact absurd (ENNReal.ofReal_le_ofReal h) (not_le.2 h2)

section Cauchy

variable {s T b p K M L : ℝ} {ρ : Euc d → ℝ} {Ω : ℕ → Type} [∀ N, MeasurableSpace (Ω N)]
  {P : ∀ N, Measure (Ω N)} [∀ N, IsProbabilityMeasure (P N)] {X : ∀ N, ℝ≥0 → Ω N → EucConfig d N}
  {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
  {ξ : (Euc d → ℝ) → Ω' → C(Set.Icc (0 : ℝ) T, ℝ)}

theorem s94_flim_cauchy (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (hρ : IsRound2Density d s M L ρ)
    (hset : IsRound2PathSetting d s T b p K (Whole.withDensityReal ρ) P X P' ξ) {Λ : ℝ}
    (hcov : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ a, IsR2Test a →
      ∫ ζ, (r2PathEval T (ξ a ζ) t) ^ 2 ∂P' ≤ Λ * ∫ x, (Whole.projMean (Whole.withDensityReal ρ) a x) ^ 2 ∂(Whole.withDensityReal ρ))
    (hΛ0 : 0 ≤ Λ) {a : ℕ → Euc d → ℝ} (ha : IsR2ZeroMeanONB (Whole.withDensityReal ρ) a) {B C₁ : ℝ}
    {h : ℝ → Euc d → Euc d → ℝ} (hker : ∀ t ∈ Set.Icc (0 : ℝ) T, IsBoundedPairKernel s B (h t))
    {n : ℕ → ℕ} {u : ∀ m, Fin (n m) → Euc d → ℝ} {Cm : ∀ m, ℝ → Fin (n m) → Fin (n m) → ℝ}
    (hu : ∀ m a, IsR2Test (u m a)) (hCs : ∀ m t a b, Cm m t a b = Cm m t b a)
    (hA : ∀ t ∈ Set.Icc (0 : ℝ) T, IsRound2Approx s C₁ B (Whole.withDensityReal ρ) (h t)
      (fun m => r2FiniteRankKernel (Cm m t) (u m)))
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    ∀ ε : ℝ≥0∞, 0 < ε → ∃ M : ℕ, ∀ m, M ≤ m → ∀ m', M ≤ m' →
      eLpNorm (fun ζ => s94Flim ξ P' (Cm m) (u m) t ζ - s94Flim ξ P' (Cm m') (u m') t ζ) 2 P' < ε := by
  haveI : IsProbabilityMeasure (Whole.withDensityReal ρ) := HRS.Whole.U1.u1_isProb hρ.prob
  obtain ⟨ha0, hon, hcomplete⟩ := ha
  have hz := s94_gseq_of_setting hset hcov hΛ0 ha0 hon ht
  let Qm : ∀ m, Ω' → ℝ := fun m ζ => ∑ α, ∑ β, Cm m t α β * (r2PathEval T (ξ (u m α) ζ) t *
    r2PathEval T (ξ (u m β) ζ) t - ∫ ζ', r2PathEval T (ξ (u m α) ζ') t * r2PathEval T (ξ (u m β) ζ') t ∂P')
  have hch : ∀ m, s94WickL2 P' (Whole.withDensityReal ρ) a (fun i ζ => r2PathEval T (ξ (a i) ζ) t)
      (r2CenterKernel (Whole.withDensityReal ρ) (r2FiniteRankKernel (Cm m t) (u m))) (Qm m) := fun m =>
    s94_wick_finiteRank hset hcov hΛ0 ha0 hon hcomplete (Cm m t) (hu m) ht
  have hF : ∀ m ζ, s94Flim ξ P' (Cm m) (u m) t ζ = (1 / 2) * Qm m ζ := by
    intro m ζ
    unfold s94Flim
    rw [Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun β _ => ?_
    ring
  have hbd : ∀ m, IsBoundedPairKernel s (C₁ * B) (r2FiniteRankKernel (Cm m t) (u m)) := fun m =>
    s94_approx_bounded (hA t ht) m
  set D : ℕ → ℝ≥0∞ := fun m => eLpNorm (fun q : Euc d × Euc d => r2FiniteRankKernel (Cm m t) (u m) q.1 q.2 -
    h t q.1 q.2) 2 ((Whole.withDensityReal ρ).prod (Whole.withDensityReal ρ)) with hD
  have hDlim : Tendsto D atTop (𝓝 0) := by
    have := (hA t ht).converges 2 (by norm_num) (by linarith [(by exact_mod_cast hd : (2 : ℝ) ≤ d)])
    simpa using this
  -- the key estimate
  set c0 : ℝ := 2 * Real.sqrt 2 * Λ with hc0
  have hkey : ∀ m m', eLpNorm (fun ζ => s94Flim ξ P' (Cm m) (u m) t ζ - s94Flim ξ P' (Cm m') (u m') t ζ) 2 P' ≤
      ENNReal.ofReal c0 * (D m + D m') := by
    intro m m'
    set ν := (Whole.withDensityReal ρ).prod (Whole.withDensityReal ρ) with hν
    have hm1 := s94_finiteRank_measurable (c := Cm m t) (u := u m) (hu m)
    have hm2 := s94_finiteRank_measurable (c := Cm m' t) (u := u m') (hu m')
    have hl1 : MemLp (fun q : Euc d × Euc d => r2FiniteRankKernel (Cm m t) (u m) q.1 q.2) 2 ν :=
      s94_finiteRank_memLp (hu m)
    have hl2 : MemLp (fun q : Euc d × Euc d => r2FiniteRankKernel (Cm m' t) (u m') q.1 q.2) 2 ν :=
      s94_finiteRank_memLp (hu m')
    set Δ : ℝ≥0∞ := eLpNorm (fun q : Euc d × Euc d => r2FiniteRankKernel (Cm m t) (u m) q.1 q.2 -
      r2FiniteRankKernel (Cm m' t) (u m') q.1 q.2) 2 ν with hΔ
    have hΔfin : Δ ≠ ⊤ := (hl1.sub hl2).eLpNorm_ne_top
    have hΔD : Δ ≤ D m + D m' := by
      have e : (fun q : Euc d × Euc d => r2FiniteRankKernel (Cm m t) (u m) q.1 q.2 -
          r2FiniteRankKernel (Cm m' t) (u m') q.1 q.2) =
          (fun q : Euc d × Euc d => r2FiniteRankKernel (Cm m t) (u m) q.1 q.2 - h t q.1 q.2) -
          (fun q : Euc d × Euc d => r2FiniteRankKernel (Cm m' t) (u m') q.1 q.2 - h t q.1 q.2) := by
        funext q; simp
      rw [hΔ, e]
      exact eLpNorm_sub_le (by norm_num)
    have hcd : eLpNorm (fun q : Euc d × Euc d => r2CenterKernel (Whole.withDensityReal ρ)
        (r2FiniteRankKernel (Cm m t) (u m)) q.1 q.2 - r2CenterKernel (Whole.withDensityReal ρ)
        (r2FiniteRankKernel (Cm m' t) (u m')) q.1 q.2) 2 ν ≤ ENNReal.ofReal (4 * Δ.toReal) := by
      refine (s94_center_diff_le hd hs0 hs hρ (hbd m) (hu m')).trans ?_
      have e4 : ENNReal.ofReal 4 = 4 := by norm_num
      rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_toReal hΔfin, e4]
    have hsq := s94_integral_sq_le_of_eLpNorm
      ((((s94_center_measurable (μ := Whole.withDensityReal ρ) hm1).sub
        (s94_center_measurable (μ := Whole.withDensityReal ρ) hm2))).aestronglyMeasurable)
      (by positivity) hcd
    have hlip := s94_wick_lipschitz hz hΛ0 ha0 hon
      (s94_center_measurable (μ := Whole.withDensityReal ρ) hm1)
      (s94_center_symm (s94_finiteRank_symm (hCs m t)))
      (s94_center_memLp hd hs0 hs hρ (hbd m))
      (s94_center_measurable (μ := Whole.withDensityReal ρ) hm2)
      (s94_center_symm (s94_finiteRank_symm (hCs m' t)))
      (s94_center_memLp hd hs0 hs hρ (hbd m')) (hch m) (hch m')
    have hQQ : eLpNorm (fun ζ => Qm m ζ - Qm m' ζ) 2 P' ≤ ENNReal.ofReal (Real.sqrt 2 * Λ * (4 * Δ.toReal)) := by
      refine s94_eLpNorm_le_of_sq ((hch m).1.sub (hch m').1) (by positivity) ?_
      calc _ ≤ 2 * Λ ^ 2 * ∫ q, (r2CenterKernel (Whole.withDensityReal ρ)
            (r2FiniteRankKernel (Cm m t) (u m)) q.1 q.2 - r2CenterKernel (Whole.withDensityReal ρ)
            (r2FiniteRankKernel (Cm m' t) (u m')) q.1 q.2) ^ 2 ∂ν := hlip
        _ ≤ 2 * Λ ^ 2 * (4 * Δ.toReal) ^ 2 := mul_le_mul_of_nonneg_left hsq (by positivity)
        _ = (Real.sqrt 2 * Λ * (4 * Δ.toReal)) ^ 2 := by
          rw [show (Real.sqrt 2 * Λ * (4 * Δ.toReal)) ^ 2 = Real.sqrt 2 ^ 2 * Λ ^ 2 * (4 * Δ.toReal) ^ 2 by ring,
            Real.sq_sqrt (by norm_num)]
    have e2 : (fun ζ => s94Flim ξ P' (Cm m) (u m) t ζ - s94Flim ξ P' (Cm m') (u m') t ζ) =
        (1 / 2 : ℝ) • (fun ζ => Qm m ζ - Qm m' ζ) := by
      funext ζ
      simp only [hF, Pi.smul_apply, smul_eq_mul]
      ring
    rw [e2, eLpNorm_const_smul]
    calc ‖(1 / 2 : ℝ)‖ₑ * eLpNorm (fun ζ => Qm m ζ - Qm m' ζ) 2 P'
        ≤ ‖(1 / 2 : ℝ)‖ₑ * ENNReal.ofReal (Real.sqrt 2 * Λ * (4 * Δ.toReal)) := by gcongr
      _ = ENNReal.ofReal c0 * Δ := by
        rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_mul (norm_nonneg _)]
        have : ‖(1 / 2 : ℝ)‖ * (Real.sqrt 2 * Λ * (4 * Δ.toReal)) = c0 * Δ.toReal := by
          rw [hc0, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]; ring
        rw [this, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hΔfin]
      _ ≤ _ := by gcongr
  intro ε hε
  have hc : ENNReal.ofReal c0 ≠ ⊤ := ENNReal.ofReal_ne_top
  have hu0 : Tendsto (fun m => ENNReal.ofReal c0 * D m) atTop (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul hDlim (Or.inr hc)
    simpa using this
  have hev := hu0.eventually_lt_const (ENNReal.half_pos hε.ne')
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.1 hev
  refine ⟨M, fun m hm m' hm' => lt_of_le_of_lt (hkey m m') ?_⟩
  calc ENNReal.ofReal c0 * (D m + D m') = ENNReal.ofReal c0 * D m + ENNReal.ofReal c0 * D m' := mul_add _ _ _
    _ < ε / 2 + ε / 2 := ENNReal.add_lt_add (hM m hm) (hM m' hm')
    _ = ε := ENNReal.add_halves ε

end Cauchy

end HRS.MS.R2Chaos
