import HRS.MS.R26T8AP11lb
import HRS.MS.R26T8AP11jc
import HRS.MS.R26T8AP11wt

/-!
# S8.2 nonlocal layer: the local Riesz gain for `0 <= sigma < d` (P11e, part 4 assembly)
`r26t8a_local_riesz_gain_nonneg`: the contract `r26t8a_local_riesz_gain` under the extra hypothesis `0 <= sigma`
(`sigma < 0` is the remaining part 5): integrability of the actual integrand off the diagonal and
`Conormal k (b+1) M (sigma-alpha) (C*A) (localRiesz alpha chi F)`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

theorem r26t8a_loc_integrand_integrable (d : ℕ) (hd : 2 ≤ d) (k b : ℕ) (alpha M sigma : ℝ)
    (halpha : 0 < alpha) (had : alpha < d) (hM : 0 ≤ M) (hsd : sigma < d)
    (chi : Euc d → ℝ) (hchi : NewtonCutoff chi) (A : ℝ) (hA : 0 ≤ A) (F : Euc d → Euc d → ℝ)
    (hF : Conormal k b M sigma A F) (x y : Euc d) (hxy : x ≠ y) :
    Integrable (fun v : Euc d => ‖x - y - v‖ ^ (alpha - (d : ℝ)) * chi v * F (y + v) y) := by
  haveI : Nontrivial (Euc d) := ⟨⟨0, EuclideanSpace.single ⟨0, by omega⟩ (1 : ℝ), by
    intro h; have := congrArg (fun v : Euc d => v ⟨0, by omega⟩) h; simp at this⟩⟩
  have hFc : ContDiffOn ℝ k (Function.uncurry F) {p | p.1 ≠ p.2} := hF.1
  have hzp : x - y ≠ 0 := sub_ne_zero.2 hxy
  have hFm : AEStronglyMeasurable (fun v : Euc d => F (y + v) y) volume := by
    have hcont : ContinuousOn (fun v : Euc d => F (y + v) y) {v : Euc d | v ≠ 0} := by
      have h1 := hFc.continuousOn
      refine h1.comp (f := fun v : Euc d => (y + v, y)) ((continuous_const.add continuous_id).prodMk
        continuous_const).continuousOn (fun v hv => ?_)
      simp only [Set.mem_setOf_eq] at hv ⊢
      intro h; apply hv; simpa using h
    have h := hcont.aestronglyMeasurable (μ := (volume : Measure (Euc d)))
      (isOpen_ne.measurableSet : MeasurableSet {v : Euc d | v ≠ 0})
    have e1 : (volume : Measure (Euc d)).restrict {v : Euc d | v ≠ 0} = volume := by
      have := restrict_compl_singleton (μ := (volume : Measure (Euc d))) (0 : Euc d)
      simpa [Set.compl_singleton_eq] using this
    rwa [e1] at h
  refine (r26t8a_loc_integrable d hd k b alpha M sigma halpha had hM hsd A hA F hF y (x - y) hzp).mono' ?_ ?_
  · exact ((((measurable_norm.comp (measurable_const.sub measurable_id)).pow_const _).aestronglyMeasurable).mul
      hchi.1.continuous.aestronglyMeasurable).mul hFm
  · refine Filter.Eventually.of_forall fun v => ?_
    have hK0 : 0 ≤ ‖x - y - v‖ ^ (alpha - (d : ℝ)) := Real.rpow_nonneg (norm_nonneg _) _
    have hch := hchi.2.2.1 v
    by_cases hv2 : ‖v‖ ≤ 2
    · rw [Set.indicator_of_mem (by simpa using hv2), norm_mul, norm_mul, Real.norm_of_nonneg hK0,
        Real.norm_of_nonneg hch.1]
      have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hch.2 hK0) (norm_nonneg (F (y + v) y))
      calc ‖x - y - v‖ ^ (alpha - (d : ℝ)) * chi v * ‖F (y + v) y‖
          ≤ ‖x - y - v‖ ^ (alpha - (d : ℝ)) * 1 * ‖F (y + v) y‖ := this
        _ = ‖x - y - v‖ ^ (alpha - (d : ℝ)) * ‖F (y + v) y‖ := by rw [mul_one]
    · rw [Set.indicator_of_notMem (by simpa using hv2), hchi.2.2.2.2 v (by linarith [not_le.1 hv2])]
      simp

theorem r26t8a_local_riesz_gain_nonneg (d : ℕ) (hd : 2 ≤ d) (k b : ℕ) (alpha M sigma : ℝ)
    (halpha : 0 < alpha) (had : alpha < d) (hM : 0 ≤ M) (hsigma : 0 ≤ sigma) (hsd : sigma < d)
    (chi : Euc d → ℝ) (hchi : NewtonCutoff chi) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ F : Euc d → Euc d → ℝ, ∀ A : ℝ, 0 ≤ A → Conormal k b M sigma A F →
      (∀ x y, x ≠ y → Integrable (fun v => ‖x - y - v‖ ^ (alpha - (d : ℝ)) * chi v * F (y + v) y)) ∧
      Conormal k (b + 1) M (sigma - alpha) (C * A) (r26t8a_localRiesz alpha chi F) := by
  obtain ⟨CS, hCS0, hCS⟩ := r26t8a_Sfun_nest d hd k b alpha M sigma halpha had hM hsigma hsd chi hchi
  obtain ⟨D, hD0, hD⟩ := r26t8a_chi_jet_bound hchi k
  set K : ℝ := 1 + 2 ^ (b + 1) * 2 ^ (|alpha - sigma| + k) with hK
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  refine ⟨3 ^ (2 * M) * (2 ^ k * (D * (CS * K))), by positivity, ?_⟩
  intro F A hA hF
  refine ⟨fun x y hxy => r26t8a_loc_integrand_integrable d hd k b alpha M sigma halpha had hM hsd chi hchi
    A hA F hF x y hxy, And.intro (r26t8a_localRiesz_contDiffOn d hd k b alpha M sigma halpha had hM hsd chi
    hchi A hA F hF) ?_⟩
  intro p q hpq X z hz
  have hpw0 : 0 ≤ pairWeight M (X + (1 / 2 : ℝ) • z) (X - (1 / 2 : ℝ) • z) :=
    mul_nonneg (Real.rpow_nonneg (s83_jb_pos _).le _) (Real.rpow_nonneg (s83_jb_pos _).le _)
  have hlb := r26t8a_mid_nest_leibniz d hd k b alpha M sigma halpha had hM hsd chi hchi A hA F hF X z hz p q hpq
  have hmj : mixedJet p q (r26t8a_localRiesz alpha chi F) X z = r26t8a_nest p q
      (fun Yw : Euc d × Euc d => midPair (r26t8a_localRiesz alpha chi F) Yw.1 Yw.2) X z := rfl
  rw [hmj]
  set Env : ℝ := 1 + (min 1 ‖z‖) ^ (-((sigma - alpha) + (q : ℝ))) * (1 + |Real.log (min 1 ‖z‖)|) ^ (b + 1) with hEnv
  have hEnv0 : 0 ≤ Env := by rw [hEnv]; positivity
  have hCA : 0 ≤ 3 ^ (2 * M) * (2 ^ k * (D * (CS * K))) * A := by positivity
  by_cases hz2 : ‖z‖ < 2
  · have hjb := r26t8a_jb_le_pairWeight hM X z hz2.le
    have hJ0 : 0 ≤ jbracket X ^ (2 * M) := Real.rpow_nonneg (s83_jb_pos X).le _
    have hterm : ∀ i ∈ Finset.range (q + 1), (q.choose i : ℝ) * ‖iteratedFDeriv ℝ i chi z‖ *
        ‖r26t8a_nest p (q - i) (fun Yw : Euc d × Euc d => r26t8a_Sfun alpha chi F Yw.1 Yw.2) X z‖ ≤
        (q.choose i : ℝ) * (D * (CS * A * jbracket X ^ (2 * M) * K * Env)) := by
      intro i hi
      have hiq : i ≤ q := by rw [Finset.mem_range] at hi; omega
      have h1 := hCS F A hA hF X z hz hz2 p (q - i) (by omega)
      have h2 := hD i (by omega) z
      have h3 := r26t8a_env_shift b k alpha sigma q i hiq (by omega) ‖z‖ (norm_pos_iff.2 hz) hz2
      have hS0 : 0 ≤ CS * A * jbracket X ^ (2 * M) := by positivity
      have h4 : ‖r26t8a_nest p (q - i) (fun Yw : Euc d × Euc d => r26t8a_Sfun alpha chi F Yw.1 Yw.2) X z‖ ≤
          CS * A * jbracket X ^ (2 * M) * K * Env :=
        h1.trans (by
          calc CS * A * jbracket X ^ (2 * M) * (1 + ‖z‖ ^ (alpha - sigma - ((q - i : ℕ) : ℝ)) *
                (1 + |Real.log ‖z‖|) ^ (b + 1))
              ≤ CS * A * jbracket X ^ (2 * M) * (K * Env) := mul_le_mul_of_nonneg_left h3 hS0
            _ = CS * A * jbracket X ^ (2 * M) * K * Env := by ring)
      have hch : (0 : ℝ) ≤ q.choose i := Nat.cast_nonneg _
      calc (q.choose i : ℝ) * ‖iteratedFDeriv ℝ i chi z‖ *
            ‖r26t8a_nest p (q - i) (fun Yw : Euc d × Euc d => r26t8a_Sfun alpha chi F Yw.1 Yw.2) X z‖
          ≤ (q.choose i : ℝ) * D * (CS * A * jbracket X ^ (2 * M) * K * Env) :=
            mul_le_mul (mul_le_mul_of_nonneg_left h2 hch) h4 (norm_nonneg _) (by positivity)
        _ = (q.choose i : ℝ) * (D * (CS * A * jbracket X ^ (2 * M) * K * Env)) := by ring
    refine hlb.trans ((Finset.sum_le_sum hterm).trans ?_)
    rw [← Finset.sum_mul]
    have hchoose : ∑ i ∈ Finset.range (q + 1), (q.choose i : ℝ) ≤ 2 ^ k := by
      have : ∑ i ∈ Finset.range (q + 1), (q.choose i : ℝ) = 2 ^ q := by exact_mod_cast Nat.sum_range_choose q
      rw [this]; exact pow_le_pow_right₀ (by norm_num) (by omega)
    have hR0 : 0 ≤ D * (CS * A * jbracket X ^ (2 * M) * K * Env) := by positivity
    calc (∑ i ∈ Finset.range (q + 1), (q.choose i : ℝ)) * (D * (CS * A * jbracket X ^ (2 * M) * K * Env))
        ≤ 2 ^ k * (D * (CS * A * jbracket X ^ (2 * M) * K * Env)) := mul_le_mul_of_nonneg_right hchoose hR0
      _ = 2 ^ k * (D * (CS * A * K * Env)) * jbracket X ^ (2 * M) := by ring
      _ ≤ 2 ^ k * (D * (CS * A * K * Env)) * (3 ^ (2 * M) * pairWeight M (X + (1 / 2 : ℝ) • z) (X - (1 / 2 : ℝ) • z)) :=
          mul_le_mul_of_nonneg_left hjb (by positivity)
      _ = 3 ^ (2 * M) * (2 ^ k * (D * (CS * K))) * A * pairWeight M (X + (1 / 2 : ℝ) • z) (X - (1 / 2 : ℝ) • z) * Env := by
          ring
  · push Not at hz2
    refine hlb.trans (le_trans (le_of_eq ?_) (by positivity))
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [r26t8a_chi_jet_zero hchi i hz2]
    simp

end HRS.MS.R26T8A
