import HRS.MS.R2MtAux3
import HRS.MS.S21F_S05

/-!
# S21F, packet R26-T3.S07: every finite static moment and singular approximation tail

The merged `round2_moment_transfer_proof` at `p = 2`, `K = 1`, `b = γ` for the actual laws `P_N = Q_{N,γ}(μ₀)` (density ratio `1`;
`Q_N` a probability measure by S05), `μ₀` the actual reference (`IsRound2Density` as in S05).  The bound `C B` for a kernel of size `B`
follows from the `B = 1` bound by homogeneity of `pairEnergy`; `B = 0` by letting the size `ε ↓ 0`; `B < 0` is impossible.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set InformationTheory
open scoped ENNReal NNReal BigOperators
open HRS HRS.Whole

namespace HRS.MS.R26T3

theorem s21f_pairEnergy_mul {d N : ℕ} (c : ℝ) (h : Euc d → Euc d → ℝ) (X : EucConfig d N)
    (μ : Measure (Euc d)) :
    pairEnergy (fun x y => c * h x y) X μ = c * pairEnergy h X μ := by
  unfold pairEnergy
  simp only [integral_const_mul, ← Finset.mul_sum]
  ring

theorem s21f_fbound_scale {d : ℕ} {s : ℝ} {μ : Measure (Euc d)} {P : ∀ N, Measure (EucConfig d N)} {r C1 : ℝ}
    (hC1 : 0 ≤ C1)
    (hF1 : ∀ h' : Euc d → Euc d → ℝ, IsBoundedPairKernel s 1 h' →
      R2ActualFBound (ι := Unit) (fun _ => μ) r C1 h' (fun _ => P))
    {B : ℝ} (hB : 0 < B) {h : Euc d → Euc d → ℝ} (hh : IsBoundedPairKernel s B h) :
    R2ActualFBound (ι := Unit) (fun _ => μ) r (C1 * B) h (fun _ => P) := by
  set h' : Euc d → Euc d → ℝ := fun x y => B⁻¹ * h x y with hh'
  have hb' : IsBoundedPairKernel s 1 h' :=
    { measurable := measurable_const.mul hh.measurable
      symm := fun x y => by simp only [hh', hh.symm x y]
      bound := fun x y hxy => by
        simp only [hh']
        rw [abs_mul, abs_of_pos (inv_pos.2 hB)]
        calc B⁻¹ * |h x y| ≤ B⁻¹ * (B * (1 + rieszWeight s (x - y))) :=
              mul_le_mul_of_nonneg_left (hh.bound x y hxy) (inv_pos.2 hB).le
          _ = 1 * (1 + rieszWeight s (x - y)) := by field_simp }
  have hhe : h = fun x y => B * h' x y := by
    funext x y; simp only [hh']; field_simp
  intro i N hN
  obtain ⟨e1, e2⟩ := hF1 h' hb' i N hN
  have hpe : ∀ X : EucConfig d N, pairEnergy h X μ = B * pairEnergy h' X μ := fun X => by
    conv_lhs => rw [hhe]
    exact s21f_pairEnergy_mul B h' X μ
  have hcen : ∫ Y, pairEnergy h Y μ ∂(P N) = B * ∫ Y, pairEnergy h' Y μ ∂(P N) := by
    simp_rw [hpe]; exact integral_const_mul _ _
  have hfun1 : (fun X : EucConfig d N => (N : ℝ) * pairEnergy h X μ) =
      B • fun X : EucConfig d N => (N : ℝ) * pairEnergy h' X μ := by
    funext X; simp only [Pi.smul_apply, smul_eq_mul, hpe]; ring
  have hfun2 : (fun X : EucConfig d N => (N : ℝ) * (pairEnergy h X μ - ∫ Y, pairEnergy h Y μ ∂(P N))) =
      B • fun X : EucConfig d N => (N : ℝ) * (pairEnergy h' X μ - ∫ Y, pairEnergy h' Y μ ∂(P N)) := by
    funext X; rw [hcen]; simp only [Pi.smul_apply, smul_eq_mul, hpe]; ring
  have hmul : ENNReal.ofReal B * ENNReal.ofReal C1 = ENNReal.ofReal (C1 * B) := by
    rw [← ENNReal.ofReal_mul hB.le, mul_comm]
  have hnb : ‖B‖ₑ = ENNReal.ofReal B := by rw [← ofReal_norm, Real.norm_of_nonneg hB.le]
  refine ⟨?_, ?_⟩
  · rw [hfun1, eLpNorm_const_smul, hnb, ← hmul]; exact mul_le_mul' le_rfl e1
  · rw [hfun2, eLpNorm_const_smul, hnb, ← hmul]; exact mul_le_mul' le_rfl e2

theorem s21f_round2Density_init {p : Parameters} {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    (R : Trajectory p δ) :
    ∃ M L : ℝ, IsRound2Density p.d p.s M L (R.ρ 0) := by
  obtain ⟨-, -, -, href⟩ := r26t3_reference_data p δ hδ hδh R
  obtain ⟨M₀, c, S, hc, hTc⟩ := href 0
  have hP : IsProbabilityMeasure (HRS.Whole.withDensityReal (R.ρ 0)) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu hTc.prob
  have hm2 : Integrable (fun y : Euc p.d => ‖y‖ ^ 2) (HRS.Whole.withDensityReal (R.ρ 0)) :=
    HRS.MS.TcF.tc4_sq_integrable hTc hc
  refine ⟨|M₀|, ∫ x, (2 + ‖x‖ ^ 2) ∂(HRS.Whole.withDensityReal (R.ρ 0)),
    hTc.prob, fun x => ?_, fun _ => s21f_logmoment hm2⟩
  calc R.ρ 0 x ≤ M₀ * Real.exp (-c * ‖x‖ ^ 2) := hTc.gauss x
    _ ≤ |M₀| * Real.exp (-c * ‖x‖ ^ 2) :=
        mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_pos _).le
    _ ≤ |M₀| * 1 := mul_le_mul_of_nonneg_left
        (Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg ‖x‖])) (abs_nonneg _)
    _ = |M₀| := mul_one _

theorem r26t3_static_moments {p : Parameters} {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    (R : Trajectory p δ) (hγ : 0 < p.γ) (r : ℝ) (hr : 1 ≤ r) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ B h, IsBoundedPairKernel p.s B h →
        R2ActualFBound (fun _ : Unit => r26t3_mu R 0) r (C * B) h (fun _ => r26t3_Q R)) ∧
      R2ActualLinearBound (fun _ : Unit => r26t3_mu R 0) r C (fun _ => r26t3_Q R) ∧
      (∀ B C₂ h hj, IsBoundedPairKernel p.s B h →
        IsRound2Approx p.s C₂ B (r26t3_mu R 0) h hj →
        R2ActualFTail (fun _ : Unit => r26t3_mu R 0) r h hj (fun _ => r26t3_Q R)) := by
  obtain ⟨M, L, hρ⟩ := s21f_round2Density_init hδ hδh R
  have hd := p.hd
  obtain ⟨hQprob, -⟩ := r26t3_static_pressure hδ hδh R hγ
  have hP : IsProbabilityMeasure (HRS.Whole.withDensityReal (R.ρ 0)) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu hρ.prob
  -- the actual laws have density ratio one
  have hdens : ∀ N : ℕ, 2 ≤ N → HasR2ActualDensity p.s p.γ 2 1 (HRS.Whole.withDensityReal (R.ρ 0))
      (r26t3_Q R N) := by
    intro N hN
    have := hQprob N hN
    refine ⟨inferInstance, Measure.AbsolutelyContinuous.refl _, ?_⟩
    have hae : (fun X : EucConfig p.d N => ((r26t3_Q R N).rnDeriv (r26t3_Q R N) X).toReal) =ᵐ[r26t3_Q R N]
        fun _ => (1 : ℝ) := (Measure.rnDeriv_self (r26t3_Q R N)).mono fun X hX => by simp [hX]
    show eLpNorm (fun X : EucConfig p.d N => ((r26t3_Q R N).rnDeriv (r26t3_Q R N) X).toReal)
      (ENNReal.ofReal 2) (r26t3_Q R N) ≤ ENNReal.ofReal 1
    rw [eLpNorm_congr_ae hae, eLpNorm_const _ (by simp) (IsProbabilityMeasure.ne_zero _)]
    simp
  obtain ⟨C1, hC1⟩ := HRS.MS.R2Mt.round2_moment_transfer_proof hd p.s p.hs0 p.hs M L p.γ 2 1 1 hγ (by norm_num) r hr
  obtain ⟨hF1, hL1, -⟩ := hC1 (R.ρ 0) hρ (fun N => r26t3_Q R N) hdens
  refine ⟨max C1 0, le_max_right _ _, fun B h hh => ?_, ?_, fun B C₂ h hj hh ha => ?_⟩
  · have hF : ∀ h' : Euc p.d → Euc p.d → ℝ, IsBoundedPairKernel p.s 1 h' →
        R2ActualFBound (ι := Unit) (fun _ => r26t3_mu R 0) r (max C1 0) h' (fun _ => r26t3_Q R) :=
      fun h' hh' i N hN => ⟨(hF1 h' hh' i N hN).1.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)),
        (hF1 h' hh' i N hN).2.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))⟩
    rcases lt_trichotomy B 0 with hB | hB | hB
    · exfalso
      have : Nontrivial (Euc p.d) := by
        rw [← Module.finrank_pos_iff (R := ℝ)]; simp; omega
      obtain ⟨y, hy⟩ := exists_ne (0 : Euc p.d)
      have h1 := hh.bound 0 y hy.symm
      have h2 : 0 ≤ rieszWeight p.s ((0 : Euc p.d) - y) := HRS.MS.Wr.wr3_rieszWeight_nonneg _ _
      nlinarith [abs_nonneg (h 0 y)]
    · subst hB
      intro i N hN
      have hz : ∀ ε : ℝ, 0 < ε → IsBoundedPairKernel p.s ε h := fun ε hε =>
        { measurable := hh.measurable
          symm := hh.symm
          bound := fun x y hxy => (hh.bound x y hxy).trans (by
            have := HRS.MS.Wr.wr3_rieszWeight_nonneg (d := p.d) p.s (x - y)
            nlinarith) }
      have hε := fun ε (hε : 0 < ε) => s21f_fbound_scale (le_max_right C1 0) hF hε (hz ε hε) i N hN
      set c := max C1 0 with hcdef
      have hc0 : 0 ≤ c := le_max_right _ _
      have key : ∀ x : ℝ≥0∞, (∀ ε : ℝ, 0 < ε → x ≤ ENNReal.ofReal (c * ε)) → x ≤ ENNReal.ofReal (c * 0) := by
        intro x hx
        refine ENNReal.le_of_forall_pos_le_add fun ε' hε' _ => ?_
        have hpos : (0 : ℝ) < c + 1 := by linarith
        have hε0 : (0 : ℝ) < (ε' : ℝ) / (c + 1) := by positivity
        calc x ≤ ENNReal.ofReal (c * ((ε' : ℝ) / (c + 1))) := hx _ hε0
          _ ≤ ENNReal.ofReal (ε' : ℝ) := by
              refine ENNReal.ofReal_le_ofReal ?_
              rw [← mul_div_assoc, div_le_iff₀ hpos]; nlinarith [(ε'.2 : (0 : ℝ) ≤ ε')]
          _ = (ε' : ℝ≥0∞) := ENNReal.ofReal_coe_nnreal
          _ ≤ ENNReal.ofReal (c * 0) + ε' := by simp
      exact ⟨key _ fun ε hε0 => (hε ε hε0).1, key _ fun ε hε0 => (hε ε hε0).2⟩
    · exact s21f_fbound_scale (le_max_right C1 0) hF hB hh
  · intro i N hN a A ha hA
    exact (hL1 i N hN a A ha hA).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_max_left _ _) ((abs_nonneg _).trans (hA 0))))
  · obtain ⟨C2, hC2⟩ := HRS.MS.R2Mt.round2_moment_transfer_proof hd p.s p.hs0 p.hs M L p.γ 2 1 B hγ (by norm_num) r hr
    exact (hC2 (R.ρ 0) hρ (fun N => r26t3_Q R N) hdens).2.2 C₂ h hj hh ha

end HRS.MS.R26T3
