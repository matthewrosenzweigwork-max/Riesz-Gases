import HRS.MS.MovEntAux6

/-!
# S6.6, packet P6 (part 2): clause (1) from the dissipation inequality (DISS)

* `s66_comm_bound`: `|∫ Comm_N(v) df| ≤ 2 K C₆ (H(f|Q) + Nδ_N)/N` for a `K`-Lipschitz field `v` (pair entropy inequality of S3.1 for the
  commutator kernel of `v/K`, `Comm_N = 2F^{h_v}`).
* `s66_clause1_core`: from `MfeDiss` along the class: `H(f_t|Q_t) ≤ C₅ (H(f_0|Q_0) + Nδ_N)` (split identity, pressure bound for `log K`, Grönwall).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.MovEnt

open HRS.Whole

local notation "wd" => Whole.withDensityReal

variable {d : ℕ}

theorem s66_comm_bound (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (M L β : ℝ) (hβ : 0 < β) :
    ∃ C₆ : ℝ, 0 ≤ C₆ ∧ ∀ ρ : Euc d → ℝ, Whole.IsProbDensity ρ → (∀ x, ρ x ≤ M) →
      (s = 0 → HasLogMoment (wd ρ) L) → ∀ N : ℕ, 2 ≤ N →
      ∀ f : Measure (EucConfig d N), IsProbabilityMeasure f →
      relEntropy f (Whole.modulatedGibbs (rieszKernel d s) N β (wd ρ)) < ⊤ →
      ∀ (v : Euc d → Euc d) (K : ℝ), HasLipBoundW v K →
        Integrable (fun X => commN d s v X (wd ρ)) f ∧
        |∫ X, commN d s v X (wd ρ) ∂f| ≤
          2 * K * C₆ * ((relEntropy f (Whole.modulatedGibbs (rieszKernel d s) N β (wd ρ))).toReal +
            N * deltaN d s N) / N := by
  obtain ⟨c, hc, C, hent⟩ := HRS.MS.Wr.euclidean_pair_entropy_proof hd hs0 hsd M L (β / 2) (2 * β) (s + 1)
    (by positivity) (by linarith)
  refine ⟨max C 0, le_max_right _ _, fun ρ hρ hM hL N hN f hf hH v K hv => ?_⟩
  haveI := hf
  obtain ⟨Lv, hLv, hLK⟩ := hv
  have hK0 : 0 ≤ K := (NNReal.coe_nonneg Lv).trans hLK
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hmem : β ∈ Set.Icc (β / 2) (2 * β) := ⟨by linarith, by linarith⟩
  rcases hK0.eq_or_lt with hK | hK
  · -- K = 0: v is constant
    have hLv0 : Lv = 0 := by
      have : (Lv : ℝ) ≤ 0 := by rw [hK]; exact hLK
      exact_mod_cast le_antisymm this (NNReal.coe_nonneg Lv)
    have hconst : ∀ x y, v x = v y := by
      intro x y
      have := hLv x y
      rw [hLv0] at this
      simpa using this
    have hz : ∀ X : EucConfig d N, commN d s v X (wd ρ) = 0 := by
      intro X
      have hk : commutatorKernel d s v = fun _ _ => 0 := by
        funext x y
        unfold commutatorKernel
        rw [hconst x y, sub_self, inner_zero_left]
      unfold commN centeredPairFunctional
      rw [hk]
      simp
    simp only [hz, integral_zero, abs_zero]
    refine ⟨integrable_zero _ _ _, ?_⟩
    rw [← hK]
    simp
  · set v' : Euc d → Euc d := fun x => K⁻¹ • v x with hv'
    have hv'L : LipschitzWith 1 v' := by
      refine LipschitzWith.of_dist_le_mul fun x y => ?_
      simp only [hv', dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hK)]
      have h1 := hLv.dist_le_mul x y
      rw [dist_eq_norm, dist_eq_norm] at h1
      have h2 : ‖v x - v y‖ ≤ K * ‖x - y‖ := h1.trans (mul_le_mul_of_nonneg_right hLK (norm_nonneg _))
      simp only [NNReal.coe_one, one_mul]
      calc K⁻¹ * ‖v x - v y‖ ≤ K⁻¹ * (K * ‖x - y‖) := mul_le_mul_of_nonneg_left h2 (inv_nonneg.2 hK0)
        _ = ‖x - y‖ := by field_simp
    have hbk := HRS.MS.PrepStat.s32_comm_isBounded hs0 hv'L
    have hkernel : commutatorKernel d s v = fun x y => K * commutatorKernel d s v' x y := by
      funext x y
      unfold commutatorKernel
      have e : v x - v y = K • (v' x - v' y) := by
        simp only [hv', ← smul_sub, smul_smul, mul_inv_cancel₀ hK.ne', one_smul]
      rw [e, inner_smul_left]
      simp
    have hcomm : ∀ X : EucConfig d N, commN d s v X (wd ρ) =
        2 * K * pairEnergy (commutatorKernel d s v') X (wd ρ) := by
      intro X
      rw [HRS.MS.PrepStat.s32_commN_eq, hkernel, HRS.MS.PrepStat.s32_pairEnergy_const_mul]
      ring
    obtain ⟨hi, hb⟩ := (hent ρ hρ hM hL (commutatorKernel d s v') hbk N hN β hmem).2 f hf hH
    haveI : IsProbabilityMeasure (wd ρ) := HRS.MS.Thm.cb_withDensityReal_isProb hρ
    have hFm : Measurable (fun X : EucConfig d N => pairEnergy (commutatorKernel d s v') X (wd ρ)) :=
      HRS.MS.Wr.wr9_measurable_pairEnergy hbk.measurable
    have hne : (N : ℝ) ≠ 0 := hN0.ne'
    have hiabs : Integrable (fun X : EucConfig d N => |pairEnergy (commutatorKernel d s v') X (wd ρ)|) f :=
      (integrable_const_mul_iff (isUnit_iff_ne_zero.2 hne) _).1 hi
    have hiF : Integrable (fun X : EucConfig d N => pairEnergy (commutatorKernel d s v') X (wd ρ)) f :=
      (integrable_norm_iff hFm.aestronglyMeasurable).1 (by simpa [Real.norm_eq_abs] using hiabs)
    have hint : Integrable (fun X => commN d s v X (wd ρ)) f := by
      simp only [hcomm]
      exact hiF.const_mul _
    refine ⟨hint, ?_⟩
    have h1 : |∫ X, commN d s v X (wd ρ) ∂f| ≤ ∫ X, |commN d s v X (wd ρ)| ∂f :=
      abs_integral_le_integral_abs
    have h2 : ∫ X, |commN d s v X (wd ρ)| ∂f =
        2 * K * ∫ X, |pairEnergy (commutatorKernel d s v') X (wd ρ)| ∂f := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
      simp only [hcomm, abs_mul, abs_of_pos hK]
      rw [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have h3 : (N : ℝ) * ∫ X, |pairEnergy (commutatorKernel d s v') X (wd ρ)| ∂f ≤
        max C 0 * ((relEntropy f (Whole.modulatedGibbs (rieszKernel d s) N β (wd ρ))).toReal +
          N * deltaN d s N) := by
      rw [← integral_const_mul]
      refine hb.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) ?_)
      have := ENNReal.toReal_nonneg (a := relEntropy f (Whole.modulatedGibbs (rieszKernel d s) N β (wd ρ)))
      obtain ⟨hd0, -, -, -⟩ := s66_delta_facts (by omega : 1 ≤ d) hs0 hsd (C₀ := 1) le_rfl hN
      have h' := mul_nonneg hN0.le hd0.le
      linarith
    rw [le_div_iff₀ hN0]
    calc |∫ X, commN d s v X (wd ρ) ∂f| * N
        ≤ (2 * K * ∫ X, |pairEnergy (commutatorKernel d s v') X (wd ρ)| ∂f) * N :=
          mul_le_mul_of_nonneg_right (h1.trans h2.le) hN0.le
      _ = 2 * K * ((N : ℝ) * ∫ X, |pairEnergy (commutatorKernel d s v') X (wd ρ)| ∂f) := by ring
      _ ≤ 2 * K * (max C 0 * ((relEntropy f (Whole.modulatedGibbs (rieszKernel d s) N β (wd ρ))).toReal +
          N * deltaN d s N)) := mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = _ := by ring

end HRS.MS.MovEnt

end
