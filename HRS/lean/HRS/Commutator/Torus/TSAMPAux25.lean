import HRS.Commutator.Torus.TSAMPAux24

/-!
# T-SAMP helpers, part 25: the packaged sampling theorem
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ}

lemma tsamp_B_eq {p q : ℝ} (hpq : p.HolderConjugate q) {η C Ia a γ c₁ vb : ℝ} (hη : 0 < η) (hC : 0 ≤ C)
    (hIa : 0 ≤ Ia) (hc₁ : 0 ≤ c₁) :
    (η⁻¹) ^ d * (2 ^ (p - 1) * ((c₁ * η ^ γ) ^ p +
      ((C * η ^ (γ - d - a)) ^ q * η ^ (a * q) * η ^ d * Ia) ^ (p - 1) *
        (((2 * d + 1) * η) ^ d * vb))) =
    (2 ^ (p - 1) * (c₁ ^ p + C ^ p * Ia ^ (p - 1) * (vb * (2 * d + 1) ^ d))) * η ^ (p * γ - d) := by
  rw [tsamp_Zq_pow hpq hη hC hIa, Real.mul_rpow hc₁ (Real.rpow_nonneg hη.le _),
    ← Real.rpow_mul hη.le, mul_pow (2 * (d : ℝ) + 1) η d]
  have e1 : (η⁻¹) ^ d = η ^ (-(d : ℝ)) := by
    rw [Real.rpow_neg hη.le, Real.rpow_natCast, inv_pow]
  have e2 : η ^ (p * (γ - d) + d * (p - 1)) * η ^ d = η ^ (p * γ) := by
    rw [← Real.rpow_natCast η d, ← Real.rpow_add hη]; congr 1; ring
  have e3 : η ^ (γ * p) = η ^ (p * γ) := by rw [mul_comm]
  have e4 : η ^ (p * γ - d) = η ^ (p * γ) * η ^ (-(d : ℝ)) := by
    rw [← Real.rpow_add hη]; rfl
  rw [e1, e3, e4]
  calc η ^ (-(d : ℝ)) * (2 ^ (p - 1) * (c₁ ^ p * η ^ (p * γ) + C ^ p * Ia ^ (p - 1) *
          η ^ (p * (γ - d) + d * (p - 1)) * ((2 * d + 1) ^ d * η ^ d * vb)))
      = 2 ^ (p - 1) * (c₁ ^ p * η ^ (p * γ) + C ^ p * Ia ^ (p - 1) * ((2 * d + 1) ^ d * vb) *
          (η ^ (p * (γ - d) + d * (p - 1)) * η ^ d)) * η ^ (-(d : ℝ)) := by ring
    _ = _ := by rw [e2]; ring

set_option maxHeartbeats 1600000 in
theorem tsamp_profile_sampling (hd : 1 ≤ d) {p q : ℝ} (hpq : p.HolderConjugate q) {a γ C Cm : ℝ}
    (ha0 : a ≤ 0) (haq : -(d : ℝ) < a * q) (hC : 0 ≤ C) (hCm : 0 ≤ Cm) :
    ∃ Cs : ℝ, 0 < Cs ∧ ∀ η : ℝ, 0 < η → η ≤ 1 → ∀ k : Torus d → ℝ, Measurable k →
      (∀ x : Torus d, x ≠ 0 → KernelGrad.tdist x 0 ≤ η →
        |k x| ≤ C * η ^ (γ - d - a) * KernelGrad.tdist x 0 ^ a) →
      (∀ x : Torus d, η ≤ KernelGrad.tdist x 0 →
        |k x| ≤ Cm * η ^ (γ - d + ((d + 1 : ℕ) : ℝ)) * KernelGrad.tdist x 0 ^ (-((d + 1 : ℕ) : ℝ))) →
      ∀ g u : Torus d → ℝ≥0∞, Measurable g →
        (∀ x, u x ≤ ∫⁻ y, ENNReal.ofReal |k (x - y)| * g y) →
        (∑ j : Fin d → Fin (nCells η), (⨆ x ∈ cellT (nCells η) j, u x) ^ p) ^ (1 / p) ≤
          ENNReal.ofReal (Cs * η ^ (γ - d / p)) * (∫⁻ y, g y ^ p) ^ (1 / p) := by
  have hp1 : 1 < p := hpq.lt
  have hp0 : 0 < p := by linarith
  have hq0 : 0 < q := hpq.symm.pos
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  set M : ℕ := d + 1 with hM
  have hMd : d < M := by omega
  set J : ℝ := ∫ y : Euc d, (1 + ‖y‖) ^ (-(M : ℝ)) with hJ
  have hJ0 : 0 ≤ J := integral_nonneg fun y => by positivity
  set Ia : ℝ := tsampIa d (a * q) with hIa
  have hIa0 : 0 ≤ Ia := tsamp_Ia_nonneg _
  set vb : ℝ := (volume (Metric.ball (0 : Euc d) 1)).toReal with hvb
  have hvbt : volume (Metric.ball (0 : Euc d) 1) = ENNReal.ofReal vb := by
    rw [hvb, ENNReal.ofReal_toReal measure_ball_lt_top.ne]
  have hvb0 : 0 ≤ vb := ENNReal.toReal_nonneg
  set c₁ : ℝ := Cm * 2 ^ M * (1 + 2 * d) ^ M * J with hc₁
  set c₂ : ℝ := C ^ p * Ia ^ (p - 1) * (vb * (2 * d + 1) ^ d) with hc₂
  have hc₁0 : 0 ≤ c₁ := by positivity
  have hc₂0 : 0 ≤ c₂ := by positivity
  set κ : ℝ := 2 ^ (p - 1) * (c₁ ^ p + c₂) with hκ
  have hκ0 : 0 ≤ κ := by positivity
  refine ⟨κ ^ (1 / p) + 1, by positivity, fun η hη hη1 k hkm hnear hfar g u hg hu => ?_⟩
  obtain ⟨hm1, hηm, hm2⟩ := tsamp_nCells hη hη1
  set m := nCells η with hm
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
  have hδ : (d : ℝ) / m ≤ 2 * d * η := by
    have : 1 / (m : ℝ) ≤ 2 * η := hm2
    calc (d : ℝ) / m = d * (1 / m) := by ring
      _ ≤ d * (2 * η) := by gcongr
      _ = 2 * d * η := by ring
  have hδ0 : (0 : ℝ) ≤ d / m := by positivity
  set A : ℝ := Cm * 2 ^ M * (1 + 2 * d) ^ M * η ^ (γ - d) with hA
  have hA0 : 0 ≤ A := by positivity
  set Θ : Torus d → ℝ≥0∞ := fun z =>
    ENNReal.ofReal (A * (1 + KernelGrad.tdist z 0 / η) ^ (-(M : ℝ))) with hΘ
  set kn : Torus d → ℝ≥0∞ := fun z =>
    if 0 < KernelGrad.tdist z 0 ∧ KernelGrad.tdist z 0 < η then ENNReal.ofReal |k z| else 0 with hkn
  set kf : Torus d → ℝ≥0∞ := fun z => if η ≤ KernelGrad.tdist z 0 then ENNReal.ofReal |k z| else 0 with hkf
  have htd : Measurable fun z : Torus d => KernelGrad.tdist z 0 := tsamp_measurable_tdist 0
  have hΘm : Measurable Θ := by
    refine ENNReal.measurable_ofReal.comp (measurable_const.mul ?_)
    exact (measurable_const.add (htd.div_const η)).pow_const _
  have hknm : Measurable kn :=
    Measurable.ite ((measurableSet_lt measurable_const htd).inter (measurableSet_lt htd measurable_const))
      (ENNReal.measurable_ofReal.comp hkm.abs) measurable_const
  have hkfm : Measurable kf :=
    Measurable.ite (measurableSet_le measurable_const htd)
      (ENNReal.measurable_ofReal.comp hkm.abs) measurable_const
  -- far part
  have hfar_pt : ∀ x x' y : Torus d, KernelGrad.tdist x x' ≤ d / m → kf (x - y) ≤ Θ (x' - y) := by
    intro x x' y hxx
    simp only [hkf, hΘ]
    by_cases h : η ≤ KernelGrad.tdist (x - y) 0
    · rw [if_pos h]
      refine ENNReal.ofReal_le_ofReal ?_
      have h1 := hfar (x - y) h
      have h2 := tsamp_far_real (e := γ - d) (Cm := Cm) (D := 2 * d) (M := M) (t' := KernelGrad.tdist (x' - y) 0)
        hη hCm h (KernelGrad.tdist_nonneg _ _) (by positivity) (by
          have t1 := tsamp_tdist_triangle x' x y
          have e1 : KernelGrad.tdist x' y = KernelGrad.tdist (x' - y) 0 := KernelGrad.tdist_eq_sub_zero x' y
          have e2 : KernelGrad.tdist x y = KernelGrad.tdist (x - y) 0 := KernelGrad.tdist_eq_sub_zero x y
          rw [tsamp_tdist_symm x' x] at t1
          rw [← e1]
          linarith)
      exact h1.trans h2
    · rw [if_neg h]; exact zero_le
  -- the pointwise splitting
  have hsplit : ∀ z : Torus d, z ≠ 0 → ENNReal.ofReal |k z| ≤ kn z + kf z := by
    intro z hz
    have hpos : 0 < KernelGrad.tdist z 0 := text_tdist_pos hz
    by_cases h : KernelGrad.tdist z 0 < η
    · simp only [hkn, hkf, if_pos (And.intro hpos h), if_neg (not_le.2 h), add_zero, le_refl]
    · simp only [hkn, hkf, if_neg (fun hh : 0 < KernelGrad.tdist z 0 ∧ KernelGrad.tdist z 0 < η => h hh.2),
        if_pos (not_lt.1 h), zero_add, le_refl]
  have hu' : ∀ x x' : Torus d, KernelGrad.tdist x x' ≤ d / m →
      u x ≤ (∫⁻ y, Θ (x' - y) * g y) + ∫⁻ y, kn (x - y) * g y := by
    intro x x' hxx
    have hmeas1 : Measurable fun y => kn (x - y) * g y :=
      (hknm.comp (measurable_const.sub measurable_id)).mul hg
    calc u x ≤ ∫⁻ y, ENNReal.ofReal |k (x - y)| * g y := hu x
      _ ≤ ∫⁻ y, (kn (x - y) * g y + kf (x - y) * g y) := by
          refine lintegral_mono_ae ?_
          filter_upwards [text_ae_ne hd x] with y hy
          rw [← add_mul]
          exact mul_le_mul' (hsplit _ (sub_ne_zero.2 (Ne.symm hy))) le_rfl
      _ = (∫⁻ y, kn (x - y) * g y) + ∫⁻ y, kf (x - y) * g y := lintegral_add_left hmeas1 _
      _ ≤ (∫⁻ y, kn (x - y) * g y) + ∫⁻ y, Θ (x' - y) * g y :=
          add_le_add le_rfl (lintegral_mono fun y => mul_le_mul' (hfar_pt x x' y hxx) le_rfl)
      _ = _ := add_comm _ _
  have hsupp : ∀ z : Torus d, kn z ≠ 0 → KernelGrad.tdist z 0 < η := by
    intro z hz
    by_contra h
    exact hz (by simp only [hkn]; rw [if_neg (fun hh : 0 < KernelGrad.tdist z 0 ∧ KernelGrad.tdist z 0 < η => h hh.2)])
  -- bound for `∫ Θ`
  have hT : ∫⁻ z, Θ z ≤ ENNReal.ofReal (c₁ * η ^ γ) := by
    have h1 := tsamp_lintegral_profile hd hη hMd
    have e : ∀ z : Torus d, Θ z = ENNReal.ofReal A * ENNReal.ofReal ((1 + KernelGrad.tdist z 0 / η) ^ (-(M : ℝ))) := by
      intro z; simp only [hΘ]; rw [ENNReal.ofReal_mul hA0]
    simp_rw [e]
    rw [lintegral_const_mul _ (by
      refine ENNReal.measurable_ofReal.comp ?_
      exact (measurable_const.add (htd.div_const η)).pow_const _)]
    calc ENNReal.ofReal A * ∫⁻ z : Torus d, ENNReal.ofReal ((1 + KernelGrad.tdist z 0 / η) ^ (-(M : ℝ)))
        ≤ ENNReal.ofReal A * ENNReal.ofReal (η ^ d * J) := mul_le_mul' le_rfl h1
      _ = ENNReal.ofReal (c₁ * η ^ γ) := by
          rw [← ENNReal.ofReal_mul hA0]
          congr 1
          have : η ^ (γ - d) * η ^ d = η ^ γ := by
            rw [← Real.rpow_natCast η d, ← Real.rpow_add hη]; congr 1; ring
          simp only [hA, hc₁]
          calc Cm * 2 ^ M * (1 + 2 * d) ^ M * η ^ (γ - d) * (η ^ d * J)
              = Cm * 2 ^ M * (1 + 2 * d) ^ M * J * (η ^ (γ - d) * η ^ d) := by ring
            _ = _ := by rw [this]
  have hT1 : ∫⁻ z, Θ z ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hT
  -- bound for `∫ kn^q`
  set c : ℝ := C * η ^ (γ - d - a) with hc
  have hc0 : 0 ≤ c := by positivity
  set Zq : ℝ := c ^ q * η ^ (a * q) * η ^ d * Ia with hZq
  have hZq0 : 0 ≤ Zq := by positivity
  have hNq : ∫⁻ z, kn z ^ q ≤ ENNReal.ofReal Zq := by
    refine le_trans (lintegral_mono fun z => ?_) (tsamp_near_lintegral hd hη hq0 haq hc0)
    refine ENNReal.rpow_le_rpow ?_ hq0.le
    simp only [hkn]
    by_cases h : 0 < KernelGrad.tdist z 0 ∧ KernelGrad.tdist z 0 < η
    · rw [if_pos h, if_pos h.2]
      have hz : z ≠ 0 := by
        intro hz0; rw [hz0] at h
        simp [CoercAux.tdist_self] at h
      exact ENNReal.ofReal_le_ofReal (hnear z hz h.2.le)
    · rw [if_neg h]; exact zero_le
  -- volume of the ball
  have hV : volume {z : Torus d | KernelGrad.tdist z 0 ≤ d / m + η} ≤
      ENNReal.ofReal (((2 * d + 1) * η) ^ d * vb) := by
    refine (tsamp_ball_volume_le (by positivity)).trans ?_
    rw [hvbt, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_ hvb0)
    refine pow_le_pow_left₀ (by positivity) ?_ d
    nlinarith
  have habs := tsamp_sampling_abstract hm1 hpq hg hΘm hknm hT1 hsupp hu'
  have hq1 : 1 / q * p = p - 1 := by
    have h := hpq.inv_add_inv_eq_one
    have hp0' : p ≠ 0 := hp0.ne'
    have hq0' : q ≠ 0 := hq0.ne'
    field_simp at h ⊢
    nlinarith [h]
  have hN : ((∫⁻ z, kn z ^ q) ^ (1 / q)) ^ p ≤ ENNReal.ofReal (Zq ^ (p - 1)) := by
    rw [← ENNReal.rpow_mul, hq1, ← ENNReal.ofReal_rpow_of_nonneg hZq0 (by linarith)]
    exact ENNReal.rpow_le_rpow hNq (by linarith)
  have hTp : (∫⁻ z, Θ z) ^ p ≤ ENNReal.ofReal ((c₁ * η ^ γ) ^ p) := by
    rw [← ENNReal.ofReal_rpow_of_nonneg (by positivity) hp0.le]
    exact ENNReal.rpow_le_rpow hT hp0.le
  have hmd : (m : ℝ≥0∞) ^ d ≤ ENNReal.ofReal ((η⁻¹) ^ d) := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_pow hm0.le]
    refine ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ hm0.le ?_ d)
    rw [le_inv_comm₀ hm0 hη, inv_eq_one_div]
    exact hηm
  have h2p : (2 : ℝ≥0∞) ^ (p - 1) = ENNReal.ofReal (2 ^ (p - 1)) := by
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ENNReal.ofReal_rpow_of_nonneg (by norm_num) (by linarith)]
  set G : ℝ≥0∞ := ∫⁻ y, g y ^ p with hG
  set B : ℝ := (η⁻¹) ^ d * (2 ^ (p - 1) * ((c₁ * η ^ γ) ^ p + Zq ^ (p - 1) * (((2 * d + 1) * η) ^ d * vb))) with hB
  have hB0 : 0 ≤ B := by positivity
  have hS : ∑ j : Fin d → Fin m, (⨆ x ∈ cellT m j, u x) ^ p ≤ ENNReal.ofReal B * G := by
    refine habs.trans ?_
    have hNV : ((∫⁻ z, kn z ^ q) ^ (1 / q)) ^ p * volume {z : Torus d | KernelGrad.tdist z 0 ≤ d / m + η} ≤
        ENNReal.ofReal (Zq ^ (p - 1) * (((2 * d + 1) * η) ^ d * vb)) := by
      rw [ENNReal.ofReal_mul (by positivity)]
      exact mul_le_mul' hN hV
    calc (m : ℝ≥0∞) ^ d * (2 ^ (p - 1) * ((∫⁻ z, Θ z) ^ p + ((∫⁻ z, kn z ^ q) ^ (1 / q)) ^ p *
            volume {z : Torus d | KernelGrad.tdist z 0 ≤ d / m + η}) * G)
        ≤ ENNReal.ofReal ((η⁻¹) ^ d) * (ENNReal.ofReal (2 ^ (p - 1)) *
            (ENNReal.ofReal ((c₁ * η ^ γ) ^ p) +
              ENNReal.ofReal (Zq ^ (p - 1) * (((2 * d + 1) * η) ^ d * vb))) * G) := by
          rw [h2p]
          exact mul_le_mul' hmd (mul_le_mul' (mul_le_mul' le_rfl (add_le_add hTp hNV)) le_rfl)
      _ = ENNReal.ofReal B * G := by
          have e : ENNReal.ofReal B = ENNReal.ofReal ((η⁻¹) ^ d) * (ENNReal.ofReal (2 ^ (p - 1)) *
              (ENNReal.ofReal ((c₁ * η ^ γ) ^ p) +
                ENNReal.ofReal (Zq ^ (p - 1) * (((2 * d + 1) * η) ^ d * vb)))) := by
            rw [hB, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
              ENNReal.ofReal_add (by positivity) (by positivity)]
          rw [e]; ring
  have hBeq : B = κ * η ^ (p * γ - d) := by
    simp only [hB, hZq, hc, hκ, hc₂]
    exact tsamp_B_eq hpq hη hC hIa0 hc₁0
  have hBp : B ^ (1 / p) ≤ (κ ^ (1 / p) + 1) * η ^ (γ - d / p) := by
    rw [hBeq, Real.mul_rpow hκ0 (Real.rpow_nonneg hη.le _), ← Real.rpow_mul hη.le]
    have : (p * γ - d) * (1 / p) = γ - d / p := by field_simp
    rw [this]
    have : 0 ≤ η ^ (γ - d / p) := Real.rpow_nonneg hη.le _
    nlinarith
  calc (∑ j : Fin d → Fin m, (⨆ x ∈ cellT m j, u x) ^ p) ^ (1 / p)
      ≤ (ENNReal.ofReal B * G) ^ (1 / p) := ENNReal.rpow_le_rpow hS (by positivity)
    _ = ENNReal.ofReal (B ^ (1 / p)) * G ^ (1 / p) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
          ENNReal.ofReal_rpow_of_nonneg hB0 (by positivity)]
    _ ≤ ENNReal.ofReal ((κ ^ (1 / p) + 1) * η ^ (γ - d / p)) * G ^ (1 / p) :=
        mul_le_mul' (ENNReal.ofReal_le_ofReal hBp) le_rfl

end HRS.Commutator.TorusNote
