import HRS.MS.R2ChaosAux55

/-!
# HRS.MS.R2ChaosAux56 -- S9.6 (P3, part 1): `L²` convergence of Wick chaoses along `L²`-convergent kernels

Packet S94 (S9.6), namespace `HRS.MS.R2Chaos`, helper prefix `s94_`.

* `S94KOK`: measurable symmetric `L²(μ⊗μ)` kernel with integrable rows and `x ↦ ∫ k(x,y) dμ(y)`.
* `s94_isWick_to_L2`: `IsR2WickChaos` implies `s94WickL2` (membership of the limit in `L²` from the sections).
* `s94_chaos_conv`: if `‖k_j - k₀‖_{L²(μ⊗μ)} → 0` and `Q_j` is the chaos of `cen k_j`, then the chaos `Q₀` of `cen k₀` exists
  and `Q_j → Q₀` in `L²(P')`.
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

structure S94KOK (μ : Measure (Euc d)) (k : Euc d → Euc d → ℝ) : Prop where
  meas : Measurable fun q : Euc d × Euc d => k q.1 q.2
  symm : ∀ x y, k x y = k y x
  memLp : MemLp (fun q : Euc d × Euc d => k q.1 q.2) 2 (μ.prod μ)
  row : ∀ x, Integrable (k x) μ
  hc : Integrable (fun x => ∫ y, k x y ∂μ) μ

theorem S94KOK.col {μ : Measure (Euc d)} {k : Euc d → Euc d → ℝ} (hk : S94KOK μ k) (y : Euc d) :
    Integrable (fun x => k x y) μ :=
  (hk.row y).congr (ae_of_all _ fun x => hk.symm y x)

section ChaosConv

variable {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'}
  [IsProbabilityMeasure P'] {z : ℕ → Ω' → ℝ} {Λ : ℝ}

theorem s94_isWick_to_L2 (hz : S94GSeq P' z Λ) {a : ℕ → Euc d → ℝ} {k : Euc d → Euc d → ℝ} {Q : Ω' → ℝ}
    (hW : IsR2WickChaos P' μ a z k Q) : s94WickL2 P' μ a z k Q := by
  have hmem := fun n => s94_sec_memLp hz (fun i j => r2WickCoeff μ a k i j) n
  have hT := HRS.TendstoL2.tendsto_eLpNorm (P := P')
    (Qn := fun n ζ => s94Sec P' z (fun i j => r2WickCoeff μ a k i j) n ζ)
    (fun n => (hmem n).aestronglyMeasurable) hW
  obtain ⟨n0, hn0⟩ := (hT.eventually (gt_mem_nhds ENNReal.zero_lt_top)).exists
  have hd0 : MemLp (s94Sec P' z (fun i j => r2WickCoeff μ a k i j) n0 - Q) 2 P' := hn0
  have hQ : MemLp Q 2 P' := by
    have := (hmem n0).sub hd0
    refine (memLp_congr_ae (Filter.EventuallyEq.of_eq ?_)).1 this
    funext ζ; simp
  refine ⟨hQ, ?_⟩
  have e : ∀ n, ∫ ζ, (s94Sec P' z (fun i j => r2WickCoeff μ a k i j) n ζ - Q ζ) ^ 2 ∂P' =
      (eLpNorm (s94Sec P' z (fun i j => r2WickCoeff μ a k i j) n - Q) 2 P').toReal ^ 2 := by
    intro n
    have hm : MemLp (s94Sec P' z (fun i j => r2WickCoeff μ a k i j) n - Q) 2 P' := (hmem n).sub hQ
    have hi : Integrable (fun ζ => (s94Sec P' z (fun i j => r2WickCoeff μ a k i j) n ζ - Q ζ) ^ 2) P' :=
      hm.integrable_sq
    have h1 := s94_lintegral_sq_eq hm.aestronglyMeasurable
    have h2 : ENNReal.ofReal (∫ ζ, (s94Sec P' z (fun i j => r2WickCoeff μ a k i j) n ζ - Q ζ) ^ 2 ∂P') =
        ∫⁻ ζ, ‖(s94Sec P' z (fun i j => r2WickCoeff μ a k i j) n - Q) ζ‖ₑ ^ 2 ∂P' := by
      rw [ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun x => sq_nonneg _)]
      refine lintegral_congr fun ω => ?_
      rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _), Real.norm_eq_abs, sq_abs]
      rfl
    have h3 : ENNReal.ofReal (∫ ζ, (s94Sec P' z (fun i j => r2WickCoeff μ a k i j) n ζ - Q ζ) ^ 2 ∂P') =
        eLpNorm (s94Sec P' z (fun i j => r2WickCoeff μ a k i j) n - Q) 2 P' ^ 2 := h2.trans h1
    rw [← ENNReal.toReal_pow, ← h3, ENNReal.toReal_ofReal (integral_nonneg fun x => sq_nonneg _)]
  simp_rw [e]
  have h4 := ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hT).pow 2
  simpa [Function.comp_def] using h4

theorem s94_chaos_conv (hz : S94GSeq P' z Λ) (hΛ0 : 0 ≤ Λ) {a : ℕ → Euc d → ℝ} (ha : ∀ i, IsR2Test (a i))
    (hon : ∀ i j, ∫ x, Whole.projMean μ (a i) x * Whole.projMean μ (a j) x ∂μ = if i = j then 1 else 0)
    {kk : ℕ → Euc d → Euc d → ℝ} {k0 : Euc d → Euc d → ℝ} (hk : ∀ j, S94KOK μ (kk j)) (hk0 : S94KOK μ k0)
    {Q : ℕ → Ω' → ℝ} (hQ : ∀ j, s94WickL2 P' μ a z (r2CenterKernel μ (kk j)) (Q j))
    (hconv : Tendsto (fun j => eLpNorm (fun q : Euc d × Euc d => kk j q.1 q.2 - k0 q.1 q.2) 2 (μ.prod μ))
      atTop (𝓝 0)) :
    ∃ Q0 : Ω' → ℝ, s94WickL2 P' μ a z (r2CenterKernel μ k0) Q0 ∧
      Tendsto (fun j => eLpNorm (fun ζ => Q j ζ - Q0 ζ) 2 P') atTop (𝓝 0) := by
  have cenmem : ∀ {k : Euc d → Euc d → ℝ}, S94KOK μ k →
      MemLp (fun q : Euc d × Euc d => r2CenterKernel μ k q.1 q.2) 2 (μ.prod μ) := fun {k} hk =>
    lt_of_le_of_lt (s94_eLpNorm_center_le (μ := μ) hk.meas) (ENNReal.mul_lt_top (by norm_num) hk.memLp)
  obtain ⟨Q0, hQ0, -⟩ := s94_wick_exists hz hΛ0 ha hon (k := r2CenterKernel μ k0)
    (s94_center_measurable (μ := μ) hk0.meas) (s94_center_symm hk0.symm) (cenmem hk0)
  refine ⟨Q0, hQ0, ?_⟩
  set c0 : ℝ := Real.sqrt 2 * Λ * 4 with hc0
  have hkey : ∀ j, eLpNorm (fun ζ => Q j ζ - Q0 ζ) 2 P' ≤ ENNReal.ofReal c0 *
      eLpNorm (fun q : Euc d × Euc d => kk j q.1 q.2 - k0 q.1 q.2) 2 (μ.prod μ) := by
    intro j
    set D : ℝ≥0∞ := eLpNorm (fun q : Euc d × Euc d => kk j q.1 q.2 - k0 q.1 q.2) 2 (μ.prod μ) with hD
    have hDm : MemLp (fun q : Euc d × Euc d => kk j q.1 q.2 - k0 q.1 q.2) 2 (μ.prod μ) :=
      (hk j).memLp.sub hk0.memLp
    have hDfin : D ≠ ⊤ := hDm.eLpNorm_ne_top
    have hlip := s94_wick_lipschitz hz hΛ0 ha hon
      (s94_center_measurable (μ := μ) (hk j).meas) (s94_center_symm (hk j).symm) (cenmem (hk j))
      (s94_center_measurable (μ := μ) hk0.meas) (s94_center_symm hk0.symm) (cenmem hk0) (hQ j) hQ0
    have hcs : ∀ q : Euc d × Euc d, r2CenterKernel μ (fun x y => kk j x y - k0 x y) q.1 q.2 =
        r2CenterKernel μ (kk j) q.1 q.2 - r2CenterKernel μ k0 q.1 q.2 := fun q =>
      s94_center_sub (hk j).row hk0.row (hk j).col hk0.col (hk j).hc hk0.hc q.1 q.2
    have hcd : eLpNorm (fun q : Euc d × Euc d => r2CenterKernel μ (kk j) q.1 q.2 -
        r2CenterKernel μ k0 q.1 q.2) 2 (μ.prod μ) ≤ ENNReal.ofReal (4 * D.toReal) := by
      have := s94_eLpNorm_center_le (μ := μ) (g := fun x y => kk j x y - k0 x y)
        ((hk j).meas.sub hk0.meas)
      have e : (fun q : Euc d × Euc d => r2CenterKernel μ (fun x y => kk j x y - k0 x y) q.1 q.2) =
          fun q => r2CenterKernel μ (kk j) q.1 q.2 - r2CenterKernel μ k0 q.1 q.2 := funext hcs
      rw [e] at this
      refine this.trans ?_
      have e4 : ENNReal.ofReal 4 = 4 := by norm_num
      rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_toReal hDfin, e4]
    have hsq := s94_integral_sq_le_of_eLpNorm
      (((s94_center_measurable (μ := μ) (hk j).meas).sub
        (s94_center_measurable (μ := μ) hk0.meas)).aestronglyMeasurable) (by positivity) hcd
    have hQQ : eLpNorm (fun ζ => Q j ζ - Q0 ζ) 2 P' ≤ ENNReal.ofReal (Real.sqrt 2 * Λ * (4 * D.toReal)) := by
      refine s94_eLpNorm_le_of_sq ((hQ j).1.sub hQ0.1) (by positivity) ?_
      calc _ ≤ 2 * Λ ^ 2 * ∫ q, (r2CenterKernel μ (kk j) q.1 q.2 -
            r2CenterKernel μ k0 q.1 q.2) ^ 2 ∂(μ.prod μ) := hlip
        _ ≤ 2 * Λ ^ 2 * (4 * D.toReal) ^ 2 := mul_le_mul_of_nonneg_left hsq (by positivity)
        _ = (Real.sqrt 2 * Λ * (4 * D.toReal)) ^ 2 := by
          rw [show (Real.sqrt 2 * Λ * (4 * D.toReal)) ^ 2 = Real.sqrt 2 ^ 2 * Λ ^ 2 * (4 * D.toReal) ^ 2 by ring,
            Real.sq_sqrt (by norm_num)]
    refine hQQ.trans (le_of_eq ?_)
    rw [show Real.sqrt 2 * Λ * (4 * D.toReal) = c0 * D.toReal by rw [hc0]; ring,
      ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hDfin]
  have hu0 : Tendsto (fun j => ENNReal.ofReal c0 * eLpNorm (fun q : Euc d × Euc d => kk j q.1 q.2 - k0 q.1 q.2) 2
      (μ.prod μ)) atTop (𝓝 0) := by
    have : Tendsto (fun j => ENNReal.ofReal c0 * eLpNorm (fun q : Euc d × Euc d => kk j q.1 q.2 - k0 q.1 q.2) 2
        (μ.prod μ)) atTop (𝓝 (ENNReal.ofReal c0 * 0)) :=
      ENNReal.Tendsto.const_mul hconv (Or.inr ENNReal.ofReal_ne_top)
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu0 (fun j => bot_le) hkey

end ChaosConv

end HRS.MS.R2Chaos
