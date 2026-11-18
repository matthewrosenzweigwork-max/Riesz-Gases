import HRS.MC.CepP4Aux5

/-!
# Packet P4, Aux6: a measure carried by the complement of the collisions is determined by good test functions
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MC.CepP4

open HRS HRS.MC.CepP3

variable {d N : ℕ}

theorem collisionSet_nonempty (hN : 2 ≤ N) : (collisionSet d N).Nonempty :=
  ⟨fun _ => 0, ⟨0, by omega⟩, ⟨1, by omega⟩, by simp [Fin.ext_iff], rfl⟩

/-- The `k`-th cutoff: `0` within `1/(k+1)` of the collisions, `1` beyond `2/(k+1)`. -/
def chi (d N : ℕ) (k : ℕ) (x : Config d N) : ℝ :=
  max 0 (min 1 (((k : ℝ) + 1) * Metric.infDist x (collisionSet d N) - 1))

theorem continuous_chi (k : ℕ) : Continuous (chi d N k) := by
  unfold chi
  exact continuous_const.max (continuous_const.min
    ((continuous_const.mul (Metric.continuous_infDist_pt _)).sub continuous_const))

theorem chi_nonneg (k : ℕ) (x : Config d N) : 0 ≤ chi d N k x := le_max_left _ _

theorem chi_le_one (k : ℕ) (x : Config d N) : chi d N k x ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

theorem chi_mono (x : Config d N) : Monotone (fun k : ℕ => chi d N k x) := by
  intro k l hkl
  unfold chi
  have he : 0 ≤ Metric.infDist x (collisionSet d N) := Metric.infDist_nonneg
  have : ((k : ℝ) + 1) * Metric.infDist x (collisionSet d N) ≤ ((l : ℝ) + 1) * Metric.infDist x (collisionSet d N) :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.succ_le_succ hkl) he
  exact max_le_max le_rfl (min_le_min le_rfl (by linarith))

theorem chi_pos_imp {k : ℕ} {x : Config d N} (h : chi d N k x ≠ 0) :
    1 / ((k : ℝ) + 1) ≤ Metric.infDist x (collisionSet d N) := by
  unfold chi at h
  by_contra hlt
  push_neg at hlt
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have : ((k : ℝ) + 1) * Metric.infDist x (collisionSet d N) - 1 < 0 := by
    have := (lt_div_iff₀ hk).1 (show Metric.infDist x (collisionSet d N) < 1 / ((k : ℝ) + 1) from hlt)
    rw [mul_comm]; linarith [this]
  apply h
  rw [max_eq_left]
  exact (min_le_right _ _).trans this.le

theorem iSup_chi (hN : 2 ≤ N) (x : Config d N) :
    ⨆ k : ℕ, ENNReal.ofReal (chi d N k x) = (collisionSet d N)ᶜ.indicator 1 x := by
  by_cases hx : x ∈ collisionSet d N
  · rw [Set.indicator_of_notMem (by simpa using hx)]
    have : ∀ k : ℕ, chi d N k x = 0 := fun k => by
      unfold chi; rw [Metric.infDist_zero_of_mem hx]; simp
    simp [this]
  · rw [Set.indicator_of_mem (by simpa using hx)]
    have hpos : 0 < Metric.infDist x (collisionSet d N) :=
      ((isClosed_collisionSet d N).notMem_iff_infDist_pos (collisionSet_nonempty hN)).1 hx
    apply le_antisymm
    · refine iSup_le fun k => ?_
      simpa using ENNReal.ofReal_le_one.2 (chi_le_one k x)
    · obtain ⟨k, hk⟩ := exists_nat_gt (2 / Metric.infDist x (collisionSet d N))
      refine le_iSup_of_le k ?_
      have h2 : 2 ≤ ((k : ℝ) + 1) * Metric.infDist x (collisionSet d N) := by
        have := (div_lt_iff₀ hpos).1 hk
        nlinarith
      have : chi d N k x = 1 := by
        unfold chi
        rw [min_eq_left (by linarith), max_eq_right zero_le_one]
      simp [this]

theorem sup_cutoff (hN : 2 ≤ N) (lam : Measure (Config d N)) {B : Set (Config d N)} (hB : MeasurableSet B) :
    ⨆ k : ℕ, (lam.withDensity (fun x => ENNReal.ofReal (chi d N k x))) B = lam (B ∩ (collisionSet d N)ᶜ) := by
  have hCm : MeasurableSet (collisionSet d N)ᶜ := (isClosed_collisionSet d N).measurableSet.compl
  simp only [withDensity_apply _ hB]
  have hmeas : ∀ k : ℕ, Measurable (fun x => ENNReal.ofReal (chi d N k x)) := fun k =>
    ENNReal.measurable_ofReal.comp (continuous_chi k).measurable
  have hmono : Monotone (fun (k : ℕ) (x : Config d N) => ENNReal.ofReal (chi d N k x)) :=
    fun k l hkl x => ENNReal.ofReal_le_ofReal (chi_mono x hkl)
  rw [← lintegral_iSup hmeas hmono]
  simp only [iSup_chi hN]
  rw [lintegral_indicator_one hCm, Measure.restrict_apply hCm, Set.inter_comm]

theorem ext_of_good (hN : 2 ≤ N) (μ ν : Measure (Config d N)) [IsFiniteMeasure μ]
    (hν : ν (collisionSet d N) = 0)
    (h : ∀ (ψ : Config d N → ℝ) (δ : ℝ), Good ψ δ →
      ∫⁻ x, ENNReal.ofReal (ψ x) ∂μ = ∫⁻ x, ENNReal.ofReal (ψ x) ∂ν) :
    μ.restrict (collisionSet d N)ᶜ = ν := by
  haveI : BorelSpace (Config d N) := Pi.borelSpace
  have hCm : MeasurableSet (collisionSet d N)ᶜ := (isClosed_collisionSet d N).measurableSet.compl
  have hchi : ∀ k : ℕ, Measurable (fun x => ENNReal.ofReal (chi d N k x)) := fun k =>
    ENNReal.measurable_ofReal.comp (continuous_chi k).measurable
  have hk : ∀ k : ℕ, μ.withDensity (fun x => ENNReal.ofReal (chi d N k x)) =
      ν.withDensity (fun x => ENNReal.ofReal (chi d N k x)) := by
    intro k
    haveI : IsFiniteMeasure (μ.withDensity (fun x => ENNReal.ofReal (chi d N k x))) := by
      refine isFiniteMeasure_of_le μ (Measure.le_iff.2 fun s hs => ?_)
      rw [withDensity_apply _ hs]
      calc ∫⁻ a in s, ENNReal.ofReal (chi d N k a) ∂μ ≤ ∫⁻ a in s, 1 ∂μ :=
            lintegral_mono fun a => by simpa using ENNReal.ofReal_le_one.2 (chi_le_one k a)
        _ = μ s := by simp
    refine ext_of_forall_lintegral_eq_of_IsFiniteMeasure (fun φ => ?_)
    have hφ : Measurable (fun x => ((φ x : ℝ≥0) : ℝ≥0∞)) := φ.continuous.measurable.coe_nnreal_ennreal
    rw [lintegral_withDensity_eq_lintegral_mul _ (hchi k) hφ,
      lintegral_withDensity_eq_lintegral_mul _ (hchi k) hφ]
    have hgood : Good (fun x => (φ x : ℝ) * chi d N k x) (1 / ((k : ℝ) + 1)) := by
      refine ⟨(NNReal.continuous_coe.comp φ.continuous).mul (continuous_chi k),
        fun x => mul_nonneg (NNReal.coe_nonneg _) (chi_nonneg k x), by positivity, fun x hx => ?_⟩
      exact chi_pos_imp (fun h0 => hx (by simp [h0]))
    have := h _ _ hgood
    have e : ∀ x, ENNReal.ofReal ((φ x : ℝ) * chi d N k x) =
        (fun x => ENNReal.ofReal (chi d N k x)) x * (fun x => ((φ x : ℝ≥0) : ℝ≥0∞)) x := by
      intro x
      rw [ENNReal.ofReal_mul (NNReal.coe_nonneg _), ENNReal.ofReal_coe_nnreal, mul_comm]
    simp only [e] at this
    exact this
  ext B hB
  have h1 := sup_cutoff hN μ hB
  have h2 := sup_cutoff hN ν hB
  simp only [hk] at h1
  rw [Measure.restrict_apply hB, ← h1, h2]
  have : ν.restrict (collisionSet d N)ᶜ = ν := by
    refine Measure.restrict_eq_self_of_ae_mem ?_
    rw [ae_iff]
    simpa using hν
  conv_rhs => rw [← this]
  exact (Measure.restrict_apply hB).symm

end HRS.MC.CepP4
