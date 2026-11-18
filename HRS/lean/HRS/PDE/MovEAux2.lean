import HRS.PDE.MovEAux1

/-!
# MOVE Aux2: the duality core of `movT_lp_lsc`

`move_dual_core`: if `∫ φ dν ≤ A ‖φ‖_{L^q(Q)}` for all continuous `φ ≥ 0` (in `ℝ≥0∞` form), then `ν ≪ Q` and
`‖dν/dQ‖_{L^p(Q)} ≤ A` (`1/p + 1/q = 1`).
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

noncomputable section

namespace HRS

theorem move_dual_core {α : Type*} [MetricSpace α] [CompactSpace α] [MeasurableSpace α]
    [BorelSpace α] {ν Q : Measure α} [IsFiniteMeasure ν] [IsFiniteMeasure Q] {p q : ℝ}
    (hp : 1 < p) (hpq : 1 / p + 1 / q = 1) {A : ℝ≥0∞} (hA : A ≠ ⊤)
    (hφ : ∀ φ : α → ℝ, Continuous φ → (∀ x, 0 ≤ φ x) →
      ∫⁻ x, ENNReal.ofReal (φ x) ∂ν ≤ A * (∫⁻ x, ENNReal.ofReal (φ x) ^ q ∂Q) ^ (1 / q)) :
    ν ≪ Q ∧ eLpNorm (ν.rnDeriv Q) (ENNReal.ofReal p) Q ≤ A := by
  have hp0 : 0 < p := by linarith
  have hq : 0 < q := by
    have h1 : 0 < 1 / p := by positivity
    have h2 : 1 / q = 1 - 1 / p := by linarith
    have h3 : 0 < 1 / q := by
      have : 1 / p < 1 := by rw [div_lt_one hp0]; exact hp
      linarith
    exact one_div_pos.1 h3
  have hpq' : (p - 1) * q = p := by
    field_simp at hpq
    nlinarith
  -- absolute continuity
  have hac : ν ≪ Q := by
    refine Measure.AbsolutelyContinuous.mk fun s hs hQs => ?_
    have h := move_dual_ext hq hA hφ (ψ := s.indicator fun _ => (1 : ℝ))
      (measurable_const.indicator hs) (B := 1)
      (fun x => by by_cases hx : x ∈ s <;> simp [hx]) (fun x => by by_cases hx : x ∈ s <;> simp [hx])
    have e1 : ∀ x, ENNReal.ofReal (s.indicator (fun _ => (1 : ℝ)) x) =
        s.indicator (fun _ => (1 : ℝ≥0∞)) x := by
      intro x; by_cases hx : x ∈ s <;> simp [hx]
    have e2 : ∀ x, ENNReal.ofReal (s.indicator (fun _ => (1 : ℝ)) x) ^ q =
        s.indicator (fun _ => (1 : ℝ≥0∞)) x := by
      intro x; by_cases hx : x ∈ s <;> simp [hx, ENNReal.zero_rpow_of_pos hq]
    have i1 : ∫⁻ x, ENNReal.ofReal (s.indicator (fun _ => (1 : ℝ)) x) ∂ν = ν s := by
      simp_rw [e1]; exact lintegral_indicator_one hs
    have i2 : ∫⁻ x, ENNReal.ofReal (s.indicator (fun _ => (1 : ℝ)) x) ^ q ∂Q = Q s := by
      simp_rw [e2]; exact lintegral_indicator_one hs
    rw [i1, i2, hQs, ENNReal.zero_rpow_of_pos (one_div_pos.2 hq), mul_zero] at h
    exact nonpos_iff_eq_zero.1 h
  refine ⟨hac, ?_⟩
  set h : α → ℝ≥0∞ := ν.rnDeriv Q with hh
  have hhm : Measurable h := Measure.measurable_rnDeriv _ _
  have hEK : ∀ K : ℕ, ∫⁻ x, (min (h x) (K : ℝ≥0∞)) ^ p ∂Q ≤ A ^ p := by
    intro K
    set m : α → ℝ≥0∞ := fun x => min (h x) (K : ℝ≥0∞) with hm
    have hmm : Measurable m := hhm.min measurable_const
    have hmtop : ∀ x, m x ≠ ⊤ := fun x => ne_top_of_le_ne_top (ENNReal.natCast_ne_top K) (min_le_right _ _)
    set ψ : α → ℝ := fun x => (m x).toReal ^ (p - 1) with hψ
    have hψm : Measurable ψ := (hmm.ennreal_toReal).pow_const _
    have hψ0 : ∀ x, 0 ≤ ψ x := fun x => Real.rpow_nonneg ENNReal.toReal_nonneg _
    have hψB : ∀ x, ψ x ≤ (K : ℝ) ^ (p - 1) := by
      intro x
      refine Real.rpow_le_rpow ENNReal.toReal_nonneg ?_ (by linarith)
      have : (m x).toReal ≤ ((K : ℝ≥0∞)).toReal :=
        ENNReal.toReal_mono (ENNReal.natCast_ne_top K) (min_le_right _ _)
      simpa using this
    have hψe : ∀ x, ENNReal.ofReal (ψ x) = m x ^ (p - 1) := by
      intro x
      show ENNReal.ofReal ((m x).toReal ^ (p - 1)) = _
      rw [← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (by linarith),
        ENNReal.ofReal_toReal (hmtop x)]
    have key := move_dual_ext hq hA hφ hψm hψ0 hψB
    have hl : ∫⁻ x, ENNReal.ofReal (ψ x) ∂ν = ∫⁻ x, h x * ENNReal.ofReal (ψ x) ∂Q := by
      rw [hh, lintegral_rnDeriv_mul hac]
      exact (ENNReal.measurable_ofReal.comp hψm).aemeasurable
    have hr : ∀ x, (ENNReal.ofReal (ψ x)) ^ q = m x ^ p := by
      intro x
      rw [hψe, ← ENNReal.rpow_mul, hpq']
    simp only [hr] at key
    rw [hl] at key
    set E := ∫⁻ x, m x ^ p ∂Q with hE
    have hE1 : E ≤ ∫⁻ x, h x * ENNReal.ofReal (ψ x) ∂Q := by
      refine lintegral_mono fun x => ?_
      rw [hψe]
      calc m x ^ p = m x ^ (1 + (p - 1)) := by ring_nf
        _ = m x * m x ^ (p - 1) := by
          rw [ENNReal.rpow_add_of_nonneg _ _ zero_le_one (by linarith), ENNReal.rpow_one]
        _ ≤ h x * m x ^ (p - 1) := by gcongr; exact min_le_left _ _
    have hEtop : E ≠ ⊤ := by
      refine ne_top_of_le_ne_top (b := ∫⁻ _x, (K : ℝ≥0∞) ^ p ∂Q) ?_ (lintegral_mono fun x =>
        ENNReal.rpow_le_rpow (min_le_right _ _) hp0.le)
      rw [lintegral_const]
      exact (ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg hp0.le (ENNReal.natCast_ne_top K))
        (measure_lt_top _ _)).ne
    have hE2 : E ≤ A * E ^ (1 / q) := hE1.trans key
    by_cases hE0 : E = 0
    · rw [hE0]; exact bot_le
    have hsplit : E = E ^ (1 / p) * E ^ (1 / q) := by
      rw [← ENNReal.rpow_add_of_nonneg (1 / p) (1 / q) (by positivity) (by positivity), hpq, ENNReal.rpow_one]
    have hq0 : E ^ (1 / q) ≠ 0 := by
      intro h0; rcases ENNReal.rpow_eq_zero_iff.1 h0 with ⟨h1, _⟩ | ⟨_, h2⟩
      · exact hE0 h1
      · exact absurd h2 (not_lt.2 (by positivity))
    have hqt : E ^ (1 / q) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by positivity) hEtop
    have hle : E ^ (1 / p) ≤ A := by
      have h3 : E ^ (1 / p) * E ^ (1 / q) ≤ A * E ^ (1 / q) := hsplit.symm.le.trans hE2
      exact (ENNReal.mul_le_mul_iff_left hq0 hqt).1 h3
    calc E = (E ^ (1 / p)) ^ p := by
          rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hp0.ne', ENNReal.rpow_one]
      _ ≤ A ^ p := ENNReal.rpow_le_rpow hle hp0.le
  have hsup : ∫⁻ x, h x ^ p ∂Q ≤ A ^ p := by
    have hmono : Monotone fun (K : ℕ) x => (min (h x) (K : ℝ≥0∞)) ^ p := fun K L hKL x =>
      ENNReal.rpow_le_rpow (min_le_min le_rfl (by exact_mod_cast hKL)) hp0.le
    have heq : ∀ x, h x ^ p = ⨆ K : ℕ, (min (h x) (K : ℝ≥0∞)) ^ p := by
      intro x
      have hmon : Monotone fun y : ℝ≥0∞ => y ^ p := fun a b hab => ENNReal.rpow_le_rpow hab hp0.le
      have h1 : h x = ⨆ K : ℕ, min (h x) (K : ℝ≥0∞) := by
        rw [← inf_iSup_eq, ENNReal.iSup_natCast]; simp
      conv_lhs => rw [h1]
      exact hmon.map_iSup_of_continuousAt (ENNReal.continuous_rpow_const.continuousAt)
        (ENNReal.zero_rpow_of_pos hp0)
    calc ∫⁻ x, h x ^ p ∂Q = ∫⁻ x, ⨆ K : ℕ, (min (h x) (K : ℝ≥0∞)) ^ p ∂Q := by simp only [← heq]
      _ = ⨆ K : ℕ, ∫⁻ x, (min (h x) (K : ℝ≥0∞)) ^ p ∂Q :=
          lintegral_iSup (fun K => (hhm.min measurable_const).pow_const _) hmono
      _ ≤ A ^ p := iSup_le hEK
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hp0) ENNReal.ofReal_ne_top hhm.aestronglyMeasurable,
    ENNReal.toReal_ofReal hp0.le]
  calc (∫⁻ x, ‖h x‖ₑ ^ p ∂Q) ^ (1 / p) ≤ (A ^ p) ^ (1 / p) :=
        ENNReal.rpow_le_rpow (by simpa using hsup) (by positivity)
    _ = A := by rw [← ENNReal.rpow_mul, mul_one_div_cancel hp0.ne', ENNReal.rpow_one]

end HRS

end
