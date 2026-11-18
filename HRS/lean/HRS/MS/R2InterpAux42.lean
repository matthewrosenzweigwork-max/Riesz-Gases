import HRS.MS.R2InterpAux41

/-!
# S10.2 (worker S102), part 42 (packet G2): the cumulative covariance path `Jc` is Lipschitz for bounded fields
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R2Interp

open HRS HRS.Whole

variable {d : ℕ} {C : WholeCoeff d} {m T : ℝ} {r : ℕ} {Pw : ℝ}

theorem s102_cut_lintegral_le {a b : ℝ} {z : ℝ → (Euc d → ℝ) → ℝ} {M : ℝ≥0∞}
    (hM : ∀ u ∈ Icc (0 : ℝ) T, dualNormE r Pw (z u) ≤ M) :
    ∫⁻ u in Icc (0 : ℝ) T, dualNormE r Pw (s102_cut a b z u) ≤ M * ENNReal.ofReal (b - a) := by
  calc ∫⁻ u in Icc (0 : ℝ) T, dualNormE r Pw (s102_cut a b z u)
      ≤ ∫⁻ u in Icc (0 : ℝ) T, (Ioc a b).indicator (fun _ => M) u := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
        by_cases hab : u ∈ Ioc a b
        · simpa [s102_cut, hab] using hM u hu
        · simp [s102_cut, hab, s102_dualNormE_zero]
    _ ≤ M * ENNReal.ofReal (b - a) := by
        rw [lintegral_indicator_const measurableSet_Ioc, Measure.restrict_apply measurableSet_Ioc]
        refine (mul_le_mul' le_rfl (measure_mono inter_subset_left)).trans ?_
        rw [Real.volume_Ioc]

/-- **G2**: a cumulative covariance path with the interval values of `IsR2JValue`, Lipschitz for a bounded field. -/
theorem s102_G2 (hT : 0 < T) {K : ℝ} (hK : 0 ≤ K)
    (Jm : (ℝ → (Euc d → ℝ) → ℝ) → ℝ → ℝ → projTensor (OscPath d m T) 2)
    (hint : ∀ z, IsR2L1F r Pw T z → R2JIntegrandMeas C m T z → ∀ a b c : ℝ, 0 ≤ a → a ≤ b → b ≤ c → c ≤ T →
      Jm z a c = Jm z a b + Jm z b c)
    (hself : ∀ z, IsR2L1F r Pw T z → R2JIntegrandMeas C m T z → ∀ a, Jm z a a = 0)
    (hTV : ∀ z, IsR2L1F r Pw T z → R2JIntegrandMeas C m T z →
      eVariationOn (fun u => Jm z 0 u) (Icc 0 T) ≤ ENNReal.ofReal K * ∫⁻ u in Icc (0 : ℝ) T, dualNormE r Pw (z u))
    (hval : ∀ z, IsR2L1F r Pw T z → R2JIntegrandMeas C m T z → ∀ a a' : ℝ, 0 ≤ a → a ≤ a' → a' ≤ T →
      IsR2JValue C m T z (Ioc a a') (Jm z a a'))
    (z : ℝ → (Euc d → ℝ) → ℝ) (hz : IsR2L1F r Pw T z) (hzm : R2JIntegrandMeas C m T z)
    {Mz : ℝ} (hMz : 0 ≤ Mz) (hbd : ∀ u ∈ Icc (0 : ℝ) T, dualNormE r Pw (z u) ≤ ENNReal.ofReal Mz) :
    ∃ Jc : ℝ → TensorDual (OscPath d m T) 2, Jc 0 = 0 ∧
      (∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ T → IsR2JValue C m T z (Ioc a b) (Jc b - Jc a)) ∧
      ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ T → ‖Jc b - Jc a‖ ≤ K * Mz * (b - a) := by
  have hdiff : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ T →
      ((Jm z 0 b : projTensor (OscPath d m T) 2) : TensorDual (OscPath d m T) 2) -
        ((Jm z 0 a : projTensor (OscPath d m T) 2) : TensorDual (OscPath d m T) 2) =
        ((Jm z a b : projTensor (OscPath d m T) 2) : TensorDual (OscPath d m T) 2) := by
    intro a b ha hab hb
    rw [hint z hz hzm 0 a b le_rfl ha hab hb]
    push_cast
    abel
  refine ⟨fun s => ((Jm z 0 s : projTensor (OscPath d m T) 2) : TensorDual (OscPath d m T) 2), ?_, ?_, ?_⟩
  · simp [hself z hz hzm]
  · intro a b ha hab hb
    simp only
    rw [hdiff a b ha hab hb]
    exact hval z hz hzm a b ha hab hb
  · intro a b ha hab hb
    simp only
    rw [hdiff a b ha hab hb]
    have hMt : ENNReal.ofReal Mz * ENNReal.ofReal (b - a) < ⊤ :=
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
    have hz' : IsR2L1F r Pw T (s102_cut a b z) := s102_cut_L1F hz hbd hMt
    have hzm' : R2JIntegrandMeas C m T (s102_cut a b z) := s102_cut_meas hzm
    have hv1 := hval (s102_cut a b z) hz' hzm' 0 T le_rfl hT.le le_rfl
    have hv2 := s102_cut_JValue (m := m) (C := C) (z := z) ha hb (hval z hz hzm a b ha hab hb)
    have heq := s102_J_unique C hT _ _ hv1 hv2
    have heq' : Jm (s102_cut a b z) 0 T = Jm z a b := Subtype.ext heq
    rw [← heq']
    have hedist := eVariationOn.edist_le (fun u => Jm (s102_cut a b z) 0 u) (s := Icc 0 T)
      (show T ∈ Icc (0 : ℝ) T from ⟨hT.le, le_rfl⟩) (show (0 : ℝ) ∈ Icc (0 : ℝ) T from ⟨le_rfl, hT.le⟩)
    have hTV' := hTV _ hz' hzm'
    have hl := s102_cut_lintegral_le (a := a) (b := b) (r := r) (Pw := Pw) hbd
    have h0 : Jm (s102_cut a b z) 0 0 = 0 := hself _ hz' hzm' 0
    have h1 : edist (Jm (s102_cut a b z) 0 T) (Jm (s102_cut a b z) 0 0) ≤
        ENNReal.ofReal (K * Mz * (b - a)) := by
      refine hedist.trans (hTV'.trans ?_)
      calc ENNReal.ofReal K * ∫⁻ u in Icc (0 : ℝ) T, dualNormE r Pw (s102_cut a b z u)
          ≤ ENNReal.ofReal K * (ENNReal.ofReal Mz * ENNReal.ofReal (b - a)) := by gcongr
        _ = ENNReal.ofReal (K * Mz * (b - a)) := by
          rw [← ENNReal.ofReal_mul hMz, ← ENNReal.ofReal_mul hK, mul_assoc]
    rw [h0, edist_zero_right] at h1
    have h2 : ‖(Jm (s102_cut a b z) 0 T : projTensor (OscPath d m T) 2)‖ ≤ K * Mz * (b - a) := by
      rw [← ofReal_norm_eq_enorm] at h1
      exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h1
    exact h2

end HRS.MS.R2Interp

end
