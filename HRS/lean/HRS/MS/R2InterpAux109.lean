import HRS.MS.R2InterpAux108
import HRS.MS.CovMeasAux30

/-!
# S10.2 (worker S10R), part 109 (packet M2): the covariance measure of the mean-field fluctuation field `η_N` along the particle path

For almost every path: a cumulative path `Jc` with the interval values of `IsR2JValue` and total variation `≤ Vf ζ := K ∫_0^T √N C₀ (μ_N^u(⟨x⟩^P) + μ(⟨x⟩^P)) du`, `Vf` integrable
(S10.1 `r2_covariance_measure_proof` applied to `z = η_N`, admissible by Aux107-108, with the explicit dual-norm bound of Aux106).
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R2Interp

open HRS HRS.Whole HRS.MS.CovMeas

variable {d : ℕ} {C : WholeCoeff d} {m T : ℝ} {r : ℕ} {c : MultiIndex d → ℝ} {Pw : ℝ}

set_option maxSynthPendingDepth 3 in
set_option maxHeartbeats 800000 in
theorem s102_M2 (hd2 : 2 ≤ d) (hS : S102Std C m T r c) (hlin : S102Lin C m T) (hT : 0 < T)
    (horb : R2OrbitSummable C m T r) (hPd : (d : ℝ) / 2 < Pw) (hP0 : 0 ≤ Pw) (hr : (d : ℝ) / 2 < r)
    {N : ℕ} (hN : 0 < N) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure (Euc d)) [IsProbabilityMeasure μ] (hμ : Integrable (fun x => jbracket x ^ Pw) μ)
    (X : ℝ≥0 → Ω → EucConfig d N) (hcont : ∀ᵐ ζ ∂P, ∀ k, Continuous fun t : ℝ≥0 => X t ζ k)
    (hXjm : Measurable fun q : ℝ × Ω => X (min q.1 T).toNNReal q.2) (Cm : ℝ)
    (hmoz : ∀ u ∈ Icc (0 : ℝ) T, Integrable (fun ζ => (N : ℝ)⁻¹ * ∑ k, jbracket (X u.toNNReal ζ k) ^ Pw) P ∧
      ∫ ζ, (N : ℝ)⁻¹ * ∑ k, jbracket (X u.toNNReal ζ k) ^ Pw ∂P ≤ Cm) :
    ∃ Vf : Ω → ℝ, Integrable Vf P ∧ ∀ᵐ ζ ∂P, ∃ (Jc : ℝ → TensorDual (OscPath d m T) 2), Jc 0 = 0 ∧
      (∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ T → IsR2JValue C m T (s102_etaf μ X ζ) (Ioc a b) (Jc b - Jc a)) ∧
      BoundedVariationOn Jc (Icc 0 T) ∧ (eVariationOn Jc (Icc 0 T)).toReal ≤ Vf ζ := by
  classical
  obtain ⟨K0, Jm, hadd, -, hmain⟩ := r2_covariance_measure_proof hd2 C m T hT r Pw hPd horb hlin
  have hd1 : 1 ≤ d := by omega
  obtain ⟨C0, hC0, hb⟩ := s102_eta_bound hd1 hP0 r hr hN μ hμ
  set a0 : ℝ := Real.sqrt N * C0 with ha0
  set c0 : ℝ := ∫ x, jbracket x ^ Pw ∂μ with hc0
  have hc00 : 0 ≤ c0 := integral_nonneg fun x => Real.rpow_nonneg (by unfold jbracket; positivity) _
  set K : ℝ := max K0 0 with hK
  -- the clamped bound
  set Mt : ℝ × Ω → ℝ := fun q => s102_Meta C0 Pw μ (X (min q.1 T).toNNReal q.2) with hMt
  have hj : Measurable fun z : Euc d => jbracket z ^ Pw :=
    ((by unfold jbracket; fun_prop : Continuous fun z : Euc d => jbracket z).rpow_const
      (fun z => Or.inl (zero_lt_one.trans_le (HRS.MS.R2Poly.s95_one_le_jb z)).ne')).measurable
  have hMtm : Measurable Mt := by
    refine measurable_const.mul ((measurable_const.mul (Finset.measurable_sum _ fun k _ => ?_)).add measurable_const)
    exact hj.comp ((measurable_pi_apply k).comp hXjm)
  have hMt0 : ∀ q, 0 ≤ Mt q := by
    intro q
    simp only [hMt, s102_Meta]
    have h2 : 0 ≤ (N : ℝ)⁻¹ * ∑ k, jbracket (X (min q.1 T).toNNReal q.2 k) ^ Pw :=
      mul_nonneg (by positivity) (Finset.sum_nonneg fun k _ => Real.rpow_nonneg (by unfold jbracket; positivity) _)
    positivity
  refine ⟨fun ζ => K * ∫ u in Icc (0 : ℝ) T, Mt (u, ζ), ?_, ?_⟩
  · -- integrability of `Vf`
    have hprod : Integrable Mt ((volume.restrict (Icc (0 : ℝ) T)).prod P) := by
      refine s102_prodInt (C := a0 * (Cm + c0)) hMtm fun u hu => ?_
      obtain ⟨hi, hbd⟩ := hmoz u hu
      have e : ∀ ζ, ‖Mt (u, ζ)‖ₑ = ENNReal.ofReal (a0 * ((N : ℝ)⁻¹ * ∑ k, jbracket (X u.toNNReal ζ k) ^ Pw + c0)) := by
        intro ζ
        rw [Real.enorm_eq_ofReal (hMt0 _)]
        simp only [hMt, s102_Meta, min_eq_left hu.2, ha0, hc0]
      simp_rw [e]
      have hint : Integrable (fun ζ => a0 * ((N : ℝ)⁻¹ * ∑ k, jbracket (X u.toNNReal ζ k) ^ Pw + c0)) P :=
        (hi.add (integrable_const c0)).const_mul a0
      have hnn : ∀ ζ, 0 ≤ a0 * ((N : ℝ)⁻¹ * ∑ k, jbracket (X u.toNNReal ζ k) ^ Pw + c0) := by
        intro ζ
        have h2 : 0 ≤ (N : ℝ)⁻¹ * ∑ k, jbracket (X u.toNNReal ζ k) ^ Pw :=
          mul_nonneg (by positivity) (Finset.sum_nonneg fun k _ => Real.rpow_nonneg (by unfold jbracket; positivity) _)
        have : 0 ≤ a0 := by rw [ha0]; positivity
        positivity
      rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall hnn)]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [integral_const_mul, integral_add hi (integrable_const c0)]
      have : 0 ≤ a0 := by rw [ha0]; positivity
      have hcc : ∫ _ζ, c0 ∂P = c0 := by simp
      rw [hcc]
      exact mul_le_mul_of_nonneg_left (by linarith) this
    exact (hprod.integral_prod_right).const_mul K
  · filter_upwards [hcont] with ζ hcz
    have hL1 := s102_eta_L1F hd1 hP0 r hr hN T μ hμ X ζ hcz
    have hJm := s102_eta_JMeas hS hlin hN μ X ζ hcz
    obtain ⟨hadd', hself, -, hTV, hval⟩ := hmain (s102_etaf μ X ζ) hL1 hJm
    have hdiff : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ T →
        ((Jm (s102_etaf μ X ζ) 0 b : projTensor (OscPath d m T) 2) : TensorDual (OscPath d m T) 2) -
          ((Jm (s102_etaf μ X ζ) 0 a : projTensor (OscPath d m T) 2) : TensorDual (OscPath d m T) 2) =
          ((Jm (s102_etaf μ X ζ) a b : projTensor (OscPath d m T) 2) : TensorDual (OscPath d m T) 2) := by
      intro a b ha hab hb
      rw [hadd' 0 a b le_rfl ha hab hb]
      push_cast
      abel
    -- the variation bound
    have hcM : Continuous fun u : ℝ => Mt (u, ζ) :=
      (s102_Meta_continuous hP0 C0 μ X ζ hcz).comp (continuous_id.min continuous_const)
    have hint : IntegrableOn (fun u => Mt (u, ζ)) (Icc (0 : ℝ) T) := hcM.integrableOn_Icc
    have hK0 : 0 ≤ K := le_max_right _ _
    have hle : eVariationOn (fun u => Jm (s102_etaf μ X ζ) 0 u) (Icc 0 T) ≤
        ENNReal.ofReal (K * ∫ u in Icc (0 : ℝ) T, Mt (u, ζ)) := by
      calc eVariationOn (fun u => Jm (s102_etaf μ X ζ) 0 u) (Icc 0 T)
          ≤ ENNReal.ofReal K0 * ∫⁻ u in Icc (0 : ℝ) T, dualNormE r Pw (s102_etaf μ X ζ u) := hTV
        _ ≤ ENNReal.ofReal K0 * ∫⁻ u in Icc (0 : ℝ) T, ENNReal.ofReal (Mt (u, ζ)) := by
            refine mul_le_mul' le_rfl (lintegral_mono_ae ?_)
            refine (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun u hu => ?_)
            have hnn : 0 ≤ Mt (u, ζ) := hMt0 _
            have := s102_dualNormE_le hnn (fun f hf => by
              have h := hb (X u.toNNReal ζ) f hf
              simpa only [hMt, min_eq_left hu.2, s102_etaf] using h)
            exact this
        _ = ENNReal.ofReal K0 * ENNReal.ofReal (∫ u in Icc (0 : ℝ) T, Mt (u, ζ)) := by
            rw [ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun u => hMt0 (u, ζ))]
        _ ≤ ENNReal.ofReal K * ENNReal.ofReal (∫ u in Icc (0 : ℝ) T, Mt (u, ζ)) :=
            mul_le_mul' (ENNReal.ofReal_le_ofReal (le_max_left _ _)) le_rfl
        _ = ENNReal.ofReal (K * ∫ u in Icc (0 : ℝ) T, Mt (u, ζ)) := (ENNReal.ofReal_mul hK0).symm
    refine ⟨fun s' => ((Jm (s102_etaf μ X ζ) 0 s' : projTensor (OscPath d m T) 2) : TensorDual (OscPath d m T) 2),
      ?_, ?_, ?_, ?_⟩
    · simp [hself 0]
    · intro a b ha hab hb'
      simp only
      rw [hdiff a b ha hab hb']
      exact hval a b ha hab hb'
    · exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
    · exact ENNReal.toReal_le_of_le_ofReal (mul_nonneg hK0 (integral_nonneg fun u => hMt0 _)) hle

end HRS.MS.R2Interp

end
