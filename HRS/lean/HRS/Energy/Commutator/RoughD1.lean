import HRS.Energy.Commutator.RoughLimit

/-!
# The one-dimensional torus: the force is `o(1/|z|)` and the time integrand is integrable at `0`
(packet CM-S3, helpers for `stress_rough`; only needed because for `d = 1` atoms are allowed)
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators
open HRS HRS.KernelAux HRS.Commutator.FourierAux HRS.Commutator.RoughAux HRS.Commutator.RoughHeat
  HRS.Commutator.RoughKernel HRS.Commutator.RoughLimit

namespace HRS.Commutator.RoughD1

theorem d1_intW {l : ℝ} (hl : 0 ≤ l) (w : Torus 1) : IntW l w := by
  obtain ⟨K, hK0, hK⟩ := HeatAux.abs_psiFn_le_exp 1
  obtain ⟨B, hB0, hB⟩ := RoughHeat.theta_sup 1
  have hc0 : 0 < 4 * Real.pi ^ 2 := by positivity
  set T : ℝ := 1 / (4 * Real.pi ^ 2) with hT
  have hT0 : 0 < T := by positivity
  have hfm := measurable_timeInt l w
  unfold IntW
  rw [← Set.Ioc_union_Ioi_eq_Ioi hT0.le]
  refine IntegrableOn.union ?_ ?_
  · -- small times
    have hI : IntegrableOn (fun t : ℝ => (Real.sqrt T + B * (4 * Real.pi ^ 2) ^ (-(1 / 2 : ℝ))) * t ^ (-(1 / 2 : ℝ)))
        (Ioc 0 T) := by
      have := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := T) (r := -(1 / 2 : ℝ)) (by norm_num))
      exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le hT0.le).mp this).const_mul _
    refine Integrable.mono' hI hfm.aestronglyMeasurable ?_
    rw [ae_restrict_iff' measurableSet_Ioc]
    refine Filter.Eventually.of_forall fun t ht => ?_
    have ht0 : 0 < t := ht.1
    have hu : 0 < 4 * Real.pi ^ 2 * t := by positivity
    have hu1 : 4 * Real.pi ^ 2 * t ≤ 1 := by
      have := ht.2; rw [hT, le_div_iff₀ hc0] at this; linarith
    have h1 := hB w hu hu1
    have h2 := EnergyAux.one_add_psiFn_nonneg' w hu
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    have hexp : Real.exp (-l * t) ≤ 1 := by rw [Real.exp_le_one_iff]; nlinarith
    have habs : |psiFn w (4 * Real.pi ^ 2 * t)| ≤ 1 + B * (4 * Real.pi ^ 2 * t) ^ (-(1 / 2 : ℝ)) := by
      have := h1
      simp only [Nat.cast_one] at this
      rw [abs_le]; constructor <;> linarith
    have hsq : (1 : ℝ) ≤ Real.sqrt T * t ^ (-(1 / 2 : ℝ)) := by
      rw [Real.rpow_neg ht0.le, ← Real.sqrt_eq_rpow, ← div_eq_mul_inv]
      rw [le_div_iff₀ (Real.sqrt_pos.mpr ht0)]
      simpa using Real.sqrt_le_sqrt ht.2
    have hmul : (4 * Real.pi ^ 2 * t) ^ (-(1 / 2 : ℝ)) = (4 * Real.pi ^ 2) ^ (-(1 / 2 : ℝ)) * t ^ (-(1 / 2 : ℝ)) :=
      Real.mul_rpow hc0.le ht0.le
    have hp : 0 ≤ t ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg ht0.le _
    calc Real.exp (-l * t) * |psiFn w (4 * Real.pi ^ 2 * t)| ≤ 1 * (1 + B * (4 * Real.pi ^ 2 * t) ^ (-(1 / 2 : ℝ))) :=
          mul_le_mul hexp habs (abs_nonneg _) zero_le_one
      _ ≤ (Real.sqrt T + B * (4 * Real.pi ^ 2) ^ (-(1 / 2 : ℝ))) * t ^ (-(1 / 2 : ℝ)) := by
          rw [one_mul, hmul]
          nlinarith [hsq]
  · -- large times
    have hI : IntegrableOn (fun t : ℝ => K * Real.exp (-(4 * Real.pi ^ 2 * t))) (Ioi T) :=
      (integrableOn_exp_Ioi hc0 T).const_mul K
    refine Integrable.mono' hI hfm.aestronglyMeasurable ?_
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Filter.Eventually.of_forall fun t ht => ?_
    have ht' : T < t := ht
    have hu1 : 1 ≤ 4 * Real.pi ^ 2 * t := by
      rw [hT, div_lt_iff₀ hc0] at ht'; linarith
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    have ht0 : 0 < t := lt_trans hT0 ht'
    have hexp : Real.exp (-l * t) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith [mul_nonneg hl ht0.le]
    calc Real.exp (-l * t) * |psiFn w (4 * Real.pi ^ 2 * t)| ≤ 1 * (K * Real.exp (-(4 * Real.pi ^ 2 * t))) :=
          mul_le_mul hexp (hK w _ hu1) (abs_nonneg _) zero_le_one
      _ = _ := one_mul _

theorem minsqrt {Φ a1 a2 ρ y : ℝ} (hΦ : 0 ≤ Φ) (ha1 : 0 ≤ a1) (ha2 : 0 ≤ a2) (hρ : 0 ≤ ρ) (hy : 0 ≤ y)
    (h1 : Φ ≤ a1 * y ^ 2) (h2 : Φ ≤ a2 * ρ * y ^ 4) : Φ ≤ Real.sqrt (a1 * a2) * Real.sqrt ρ * y ^ 3 := by
  have h3 : Φ ^ 2 ≤ (a1 * y ^ 2) * (a2 * ρ * y ^ 4) := by
    rw [sq]; exact mul_le_mul h1 h2 hΦ (by positivity)
  have h4 : Φ ≤ Real.sqrt ((a1 * y ^ 2) * (a2 * ρ * y ^ 4)) := Real.le_sqrt_of_sq_le h3
  refine h4.trans (le_of_eq ?_)
  have e : (a1 * y ^ 2) * (a2 * ρ * y ^ 4) = (a1 * a2) * ρ * (y ^ 3) ^ 2 := by ring
  rw [e, Real.sqrt_mul (by positivity : 0 ≤ (a1 * a2) * ρ), Real.sqrt_mul (by positivity : 0 ≤ a1 * a2),
    Real.sqrt_sq (by positivity : 0 ≤ y ^ 3)]

theorem d1_small_u : ∃ c1 : ℝ, 0 ≤ c1 ∧ ∀ (z : Torus 1) (t : ℝ), 0 < t → 4 * Real.pi ^ 2 * t ≤ 1 / 2 →
    KernelGrad.tdist z 0 * |psiG 0 z (4 * Real.pi ^ 2 * t)| ≤
      c1 * Real.sqrt (KernelGrad.tdist z 0) * t ^ (-(3 / 4 : ℝ)) := by
  obtain ⟨B, hB0, hB⟩ := RoughHeat.theta_sup 1
  set A1 : ℝ := 4 * Real.sqrt 2 * B * (2 : ℝ) ^ (-(1 / 2 : ℝ)) with hA1
  set A2 : ℝ := 2 * Real.pi * Real.sqrt 2 * B * (2 : ℝ) ^ (-(1 / 2 : ℝ)) with hA2
  have hA10 : 0 ≤ A1 := by positivity
  have hA20 : 0 ≤ A2 := by positivity
  refine ⟨Real.sqrt (A1 * A2) * (4 * Real.pi ^ 2) ^ (-(3 / 4 : ℝ)), by positivity, fun z t ht hu2 => ?_⟩
  have hc0 : 0 < 4 * Real.pi ^ 2 := by positivity
  have hu : 0 < 4 * Real.pi ^ 2 * t := by positivity
  set u : ℝ := 4 * Real.pi ^ 2 * t with hu_def
  have h2u : 2 * u ≤ 1 := by linarith
  have hθ := hB z (by positivity : 0 < 2 * u) h2u
  simp only [Nat.cast_one] at hθ
  have T3 := HeatAux.tdist_abs_psiG_theta (0 : Fin 1) z hu
  have T2 := HeatAux.abs_psiG_theta (0 : Fin 1) z hu
  set ρ := KernelGrad.tdist z 0 with hρ
  have hρ0 : 0 ≤ ρ := KernelGrad.tdist_nonneg z 0
  set y : ℝ := u ^ (-(1 / 4 : ℝ)) with hy
  have hy0 : 0 ≤ y := Real.rpow_nonneg hu.le _
  have hy2 : u ^ (-(1 / 2 : ℝ)) = y ^ 2 := by
    rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul hu.le]; norm_num
  have hy3 : u ^ (-(3 / 4 : ℝ)) = y ^ 3 := by
    rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul hu.le]; norm_num
  have hsq : 1 / Real.sqrt u = y ^ 2 := by
    rw [← hy2, Real.rpow_neg hu.le, ← Real.sqrt_eq_rpow, one_div]
  have h2 : (2 * u) ^ (-(1 / 2 : ℝ)) = (2 : ℝ) ^ (-(1 / 2 : ℝ)) * y ^ 2 := by
    rw [Real.mul_rpow (by norm_num) hu.le, hy2]
  have hθ' : 1 + psiFn z (2 * u) ≤ B * ((2 : ℝ) ^ (-(1 / 2 : ℝ)) * y ^ 2) := by rw [← h2]; exact hθ
  have hs2 : Real.sqrt 2 ^ 1 = Real.sqrt 2 := pow_one _
  have hΦ0 : 0 ≤ ρ * |psiG 0 z u| := mul_nonneg hρ0 (abs_nonneg _)
  have hb1 : ρ * |psiG 0 z u| ≤ A1 * y ^ 2 := by
    refine T3.trans ?_
    rw [hs2]
    calc 4 * Real.sqrt 2 * (1 + psiFn z (2 * u)) ≤ 4 * Real.sqrt 2 * (B * ((2 : ℝ) ^ (-(1 / 2 : ℝ)) * y ^ 2)) :=
          mul_le_mul_of_nonneg_left hθ' (by positivity)
      _ = A1 * y ^ 2 := by rw [hA1]; ring
  have hb2 : ρ * |psiG 0 z u| ≤ A2 * ρ * y ^ 4 := by
    have h3 : ρ * |psiG 0 z u| ≤ ρ * (2 * Real.pi / Real.sqrt u * Real.sqrt 2 ^ 1 * (1 + psiFn z (2 * u))) :=
      mul_le_mul_of_nonneg_left T2 hρ0
    refine h3.trans ?_
    rw [hs2]
    have : 2 * Real.pi / Real.sqrt u = 2 * Real.pi * y ^ 2 := by rw [div_eq_mul_one_div, hsq]
    rw [this]
    calc ρ * (2 * Real.pi * y ^ 2 * Real.sqrt 2 * (1 + psiFn z (2 * u)))
        ≤ ρ * (2 * Real.pi * y ^ 2 * Real.sqrt 2 * (B * ((2 : ℝ) ^ (-(1 / 2 : ℝ)) * y ^ 2))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hθ' (by positivity)) hρ0
      _ = A2 * ρ * y ^ 4 := by rw [hA2]; ring
  have key := minsqrt hΦ0 hA10 hA20 hρ0 hy0 hb1 hb2
  refine key.trans (le_of_eq ?_)
  rw [← hy3, hu_def, Real.mul_rpow hc0.le ht.le]
  ring

theorem d1_mid_u : ∃ c2 : ℝ, 0 ≤ c2 ∧ ∀ (z : Torus 1) (u : ℝ), 1 / 2 ≤ u → u ≤ 1 → |psiG 0 z u| ≤ c2 := by
  obtain ⟨K, hK0, hK⟩ := HeatAux.abs_psiFn_le_exp 1
  refine ⟨4 * Real.pi * (1 + K), by positivity, fun z u hu1 hu2 => ?_⟩
  have hu : 0 < u := by linarith
  have T2 := HeatAux.abs_psiG_theta (0 : Fin 1) z hu
  rw [pow_one] at T2
  have h1 : 1 + psiFn z (2 * u) ≤ 1 + K := by
    have := hK z (2 * u) (by linarith)
    have h2 : Real.exp (-(2 * u)) ≤ 1 := by rw [Real.exp_le_one_iff]; linarith
    have h3 : |psiFn z (2 * u)| ≤ K := this.trans (by nlinarith [Real.exp_pos (-(2 * u))])
    linarith [le_abs_self (psiFn z (2 * u))]
  have h2 : 1 / Real.sqrt u ≤ Real.sqrt 2 := by
    rw [div_le_iff₀ (Real.sqrt_pos.mpr hu), ← Real.sqrt_mul (by norm_num)]
    exact Real.one_le_sqrt.mpr (by linarith)
  have hpos : 0 ≤ 1 + psiFn z (2 * u) := EnergyAux.one_add_psiFn_nonneg' z (by linarith)
  refine T2.trans ?_
  have hπ := Real.pi_pos
  have hs2 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have e : 2 * Real.pi / Real.sqrt u * Real.sqrt 2 * (1 + psiFn z (2 * u)) =
      (2 * Real.pi * Real.sqrt 2) * (1 / Real.sqrt u) * (1 + psiFn z (2 * u)) := by ring
  rw [e]
  calc (2 * Real.pi * Real.sqrt 2) * (1 / Real.sqrt u) * (1 + psiFn z (2 * u))
      ≤ (2 * Real.pi * Real.sqrt 2) * Real.sqrt 2 * (1 + K) :=
        mul_le_mul (mul_le_mul_of_nonneg_left h2 (by positivity)) h1 hpos (by positivity)
    _ = 2 * Real.pi * (Real.sqrt 2 * Real.sqrt 2) * (1 + K) := by ring
    _ = 4 * Real.pi * (1 + K) := by
        rw [Real.mul_self_sqrt (by norm_num)]; ring

theorem tail_split_gen {f : ℝ → ℝ} {c a : ℝ} (hf : IntegrableOn f (Ioi c)) (hca : c ≤ a) :
    ∫ t in Ioi c, f t = (∫ t in Ioc c a, f t) + ∫ t in Ioi a, f t := by
  have hunion : Ioc c a ∪ Ioi a = Ioi c := Set.Ioc_union_Ioi_eq_Ioi hca
  conv_lhs => rw [← hunion]
  exact setIntegral_union (Set.disjoint_left.mpr fun x hx hx' => by
      simp only [mem_Ioc, mem_Ioi] at hx hx'; linarith [hx.2]) measurableSet_Ioi
    (hf.mono_set (by rw [← hunion]; exact subset_union_left))
    (hf.mono_set (by rw [← hunion]; exact subset_union_right))

theorem d1_main_est {l : ℝ} (hl : 0 ≤ l) : ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ z : Torus 1, z ≠ 0 →
    KernelGrad.tdist z 0 ≤ 1 → KernelGrad.tdist z 0 * ‖SliceAux.sgv l z‖ ≤ C₀ * Real.sqrt (KernelGrad.tdist z 0) := by
  obtain ⟨c1, hc10, hc1⟩ := d1_small_u
  obtain ⟨c2, hc20, hc2⟩ := d1_mid_u
  obtain ⟨M, hM0, hM⟩ := psiG_large_bound (d := 1) 0
  have hc0 : 0 < 4 * Real.pi ^ 2 := by positivity
  set T : ℝ := 1 / (4 * Real.pi ^ 2) with hT
  have hT0 : 0 < T := by positivity
  set a : ℝ := T / 2 with ha
  have ha0 : 0 < a := by positivity
  have hI1 : IntegrableOn (fun t : ℝ => t ^ (-(3 / 4 : ℝ))) (Ioc 0 a) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ha0.le).mp
      (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := a) (r := -(3 / 4 : ℝ)) (by norm_num))
  set I1 : ℝ := ∫ t in Ioc 0 a, t ^ (-(3 / 4 : ℝ)) with hI1def
  have hI1nn : 0 ≤ I1 := setIntegral_nonneg measurableSet_Ioc fun t ht => Real.rpow_nonneg ht.1.le _
  refine ⟨c1 * I1 + c2 * (T - a) + M / (4 * Real.pi ^ 2), by
    have : 0 ≤ T - a := by rw [ha]; linarith
    positivity, fun z hz hρ1 => ?_⟩
  set ρ := KernelGrad.tdist z 0 with hρ
  have hρ0 : 0 < ρ := KernelGrad.tdist_pos hz
  have hnorm : ‖SliceAux.sgv l z‖ ≤ |SliceAux.sgc 0 l z| := by
    refine (SliceAux.norm_sgv_le l z).trans ?_
    rw [Fin.sum_univ_one]
  have habs := SliceAux.abs_sgc_le (0 : Fin 1) (l := l) z
  set F : ℝ → ℝ := fun t => ρ * (Real.exp (-l * t) * |psiG 0 z (4 * Real.pi ^ 2 * t)|) with hF
  have hFi : IntegrableOn F (Ioi 0) := (HeatAux.integrableOn_exp_abs_psiG hl 0 hz).const_mul ρ
  have hFle : ρ * |SliceAux.sgc 0 l z| ≤ ∫ t in Ioi (0 : ℝ), F t := by
    rw [hF, integral_const_mul]
    exact mul_le_mul_of_nonneg_left habs hρ0.le
  have hFnn : ∀ t, 0 < t → 0 ≤ F t := fun t ht => by
    simp only [hF]; positivity
  -- the three pieces
  have hsplit1 := tail_split_gen hFi (le_of_lt ha0)
  have hFi2 : IntegrableOn F (Ioi a) := hFi.mono_set (Ioi_subset_Ioi ha0.le)
  have hsplit2 := tail_split_gen hFi2 (by rw [ha]; linarith : a ≤ T)
  have hexp1 : ∀ t : ℝ, 0 < t → Real.exp (-l * t) ≤ 1 := fun t ht => by
    rw [Real.exp_le_one_iff]; nlinarith
  have p1 : ∫ t in Ioc 0 a, F t ≤ c1 * Real.sqrt ρ * I1 := by
    have : ∫ t in Ioc 0 a, F t ≤ ∫ t in Ioc 0 a, c1 * Real.sqrt ρ * t ^ (-(3 / 4 : ℝ)) :=
      setIntegral_mono_on (hFi.mono_set Ioc_subset_Ioi_self) (hI1.const_mul _) measurableSet_Ioc (fun t ht => by
        have ht0 : 0 < t := ht.1
        have h1 : 4 * Real.pi ^ 2 * t ≤ 1 / 2 := by
          have := ht.2; rw [ha, hT] at this
          rw [div_div, le_div_iff₀ (by positivity)] at this
          nlinarith
        have := hc1 z t ht0 h1
        calc F t = Real.exp (-l * t) * (ρ * |psiG 0 z (4 * Real.pi ^ 2 * t)|) := by simp only [hF]; ring
          _ ≤ 1 * (ρ * |psiG 0 z (4 * Real.pi ^ 2 * t)|) :=
              mul_le_mul_of_nonneg_right (hexp1 t ht0) (by positivity)
          _ ≤ _ := by rw [one_mul]; exact this)
    have e : ∫ t in Ioc 0 a, c1 * Real.sqrt ρ * t ^ (-(3 / 4 : ℝ)) = c1 * Real.sqrt ρ * I1 :=
      integral_const_mul _ _
    exact this.trans (le_of_eq e)
  have p2 : ∫ t in Ioc a T, F t ≤ ρ * c2 * (T - a) := by
    have hc : IntegrableOn (fun _ : ℝ => ρ * c2) (Ioc a T) :=
      integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
    have : ∫ t in Ioc a T, F t ≤ ∫ t in Ioc a T, ρ * c2 :=
      setIntegral_mono_on (hFi.mono_set (fun t ht => lt_trans ha0 ht.1)) hc measurableSet_Ioc (fun t ht => by
        have ht0 : 0 < t := lt_trans ha0 ht.1
        have h1 : 1 / 2 ≤ 4 * Real.pi ^ 2 * t := by
          have := ht.1; rw [ha, hT] at this
          rw [div_div, div_lt_iff₀ (by positivity)] at this
          nlinarith
        have h2 : 4 * Real.pi ^ 2 * t ≤ 1 := by
          have := ht.2; rw [hT, le_div_iff₀ hc0] at this; linarith
        calc F t = Real.exp (-l * t) * (ρ * |psiG 0 z (4 * Real.pi ^ 2 * t)|) := by simp only [hF]; ring
          _ ≤ 1 * (ρ * |psiG 0 z (4 * Real.pi ^ 2 * t)|) :=
              mul_le_mul_of_nonneg_right (hexp1 t ht0) (by positivity)
          _ ≤ ρ * c2 := by rw [one_mul]; exact mul_le_mul_of_nonneg_left (hc2 z _ h1 h2) hρ0.le)
    rw [setIntegral_const, Real.volume_real_Ioc_of_le (by rw [ha]; linarith)] at this
    simpa [smul_eq_mul, mul_comm, mul_assoc, mul_left_comm] using this
  have p3 : ∫ t in Ioi T, F t ≤ ρ * M / (4 * Real.pi ^ 2) := by
    have hE : IntegrableOn (fun t : ℝ => ρ * (M * Real.exp (-(4 * Real.pi ^ 2 * t)))) (Ioi T) :=
      ((integrableOn_exp_Ioi hc0 T).const_mul M).const_mul ρ
    have : ∫ t in Ioi T, F t ≤ ∫ t in Ioi T, ρ * (M * Real.exp (-(4 * Real.pi ^ 2 * t))) :=
      setIntegral_mono_on (hFi.mono_set (Ioi_subset_Ioi hT0.le)) hE measurableSet_Ioi (fun t ht => by
        have ht' : T < t := ht
        have ht0 : 0 < t := lt_trans hT0 ht'
        have h1 : 1 ≤ 4 * Real.pi ^ 2 * t := by
          rw [hT, div_lt_iff₀ hc0] at ht'; linarith
        calc F t = Real.exp (-l * t) * (ρ * |psiG 0 z (4 * Real.pi ^ 2 * t)|) := by simp only [hF]; ring
          _ ≤ 1 * (ρ * |psiG 0 z (4 * Real.pi ^ 2 * t)|) :=
              mul_le_mul_of_nonneg_right (hexp1 t ht0) (by positivity)
          _ ≤ ρ * (M * Real.exp (-(4 * Real.pi ^ 2 * t))) := by
              rw [one_mul]; exact mul_le_mul_of_nonneg_left (hM z _ h1) hρ0.le)
    have e : ∫ t in Ioi T, ρ * (M * Real.exp (-(4 * Real.pi ^ 2 * t))) =
        ρ * (M * (Real.exp (-(4 * Real.pi ^ 2 * T)) / (4 * Real.pi ^ 2))) := by
      rw [integral_const_mul, integral_const_mul, integral_exp_Ioi hc0]
    refine this.trans ((le_of_eq e).trans ?_)
    have h1 : Real.exp (-(4 * Real.pi ^ 2 * T)) ≤ 1 := by rw [Real.exp_le_one_iff]; nlinarith [mul_pos hc0 hT0]
    have h2 : Real.exp (-(4 * Real.pi ^ 2 * T)) / (4 * Real.pi ^ 2) ≤ 1 / (4 * Real.pi ^ 2) :=
      div_le_div_of_nonneg_right h1 hc0.le
    calc ρ * (M * (Real.exp (-(4 * Real.pi ^ 2 * T)) / (4 * Real.pi ^ 2))) ≤ ρ * (M * (1 / (4 * Real.pi ^ 2))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hM0) hρ0.le
      _ = ρ * M / (4 * Real.pi ^ 2) := by ring
  -- assemble
  have hsum : ρ * |SliceAux.sgc 0 l z| ≤ c1 * Real.sqrt ρ * I1 + ρ * c2 * (T - a) + ρ * M / (4 * Real.pi ^ 2) := by
    refine hFle.trans ?_
    rw [hsplit1, hsplit2]
    linarith
  have hρs : ρ ≤ Real.sqrt ρ := by
    have h := Real.sqrt_le_sqrt hρ1
    rw [Real.sqrt_one] at h
    have := Real.mul_self_sqrt hρ0.le
    nlinarith [Real.sqrt_nonneg ρ]
  have hTa : 0 ≤ T - a := by rw [ha]; linarith
  calc ρ * ‖SliceAux.sgv l z‖ ≤ ρ * |SliceAux.sgc 0 l z| := mul_le_mul_of_nonneg_left hnorm hρ0.le
    _ ≤ _ := hsum
    _ ≤ (c1 * I1 + c2 * (T - a) + M / (4 * Real.pi ^ 2)) * Real.sqrt ρ := by
        have h1 : ρ * c2 * (T - a) ≤ Real.sqrt ρ * c2 * (T - a) := by
          gcongr
        have h2 : ρ * M / (4 * Real.pi ^ 2) ≤ Real.sqrt ρ * M / (4 * Real.pi ^ 2) := by
          gcongr
        calc c1 * Real.sqrt ρ * I1 + ρ * c2 * (T - a) + ρ * M / (4 * Real.pi ^ 2)
            ≤ c1 * Real.sqrt ρ * I1 + Real.sqrt ρ * c2 * (T - a) + Real.sqrt ρ * M / (4 * Real.pi ^ 2) := by
              linarith [h1, h2]
          _ = _ := by ring

theorem d1_force_small {l : ℝ} (hl : 0 ≤ l) : ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧
    ∀ z : Torus 1, z ≠ 0 → KernelGrad.tdist z 0 < δ → KernelGrad.tdist z 0 * ‖SliceAux.sgv l z‖ < η := by
  obtain ⟨C₀, hC0, hC⟩ := d1_main_est hl
  intro η hη
  have hq : 0 < η / (C₀ + 1) := by positivity
  refine ⟨min 1 ((η / (C₀ + 1)) ^ 2), lt_min one_pos (by positivity), fun z hz hρ => ?_⟩
  have hρ1 : KernelGrad.tdist z 0 ≤ 1 := ((lt_min_iff.mp hρ).1).le
  have hρ2 : KernelGrad.tdist z 0 < (η / (C₀ + 1)) ^ 2 := (lt_min_iff.mp hρ).2
  have h1 := hC z hz hρ1
  have h2 : Real.sqrt (KernelGrad.tdist z 0) < η / (C₀ + 1) := by
    rw [Real.sqrt_lt' hq]; exact hρ2
  calc KernelGrad.tdist z 0 * ‖SliceAux.sgv l z‖ ≤ C₀ * Real.sqrt (KernelGrad.tdist z 0) := h1
    _ ≤ C₀ * (η / (C₀ + 1)) := mul_le_mul_of_nonneg_left h2.le hC0
    _ < η := by
        rw [← mul_div_assoc, div_lt_iff₀ (by positivity)]
        nlinarith

theorem d1_kk_continuousAt {l : ℝ} (hl : 0 ≤ l) {L : ℝ} (hL : 0 ≤ L) {v : Torus 1 → Euc 1}
    (hv : IsLipschitzVF L v) (y : Torus 1) :
    ContinuousAt (fun p : Torus 1 × Torus 1 => kk l v p.1 p.2) (y, y) := by
  rw [ContinuousAt, kk_diag]
  rw [Metric.tendsto_nhds]
  intro η hη
  obtain ⟨δ, hδ, hsmall⟩ := d1_force_small hl (η / (L + 1)) (by positivity)
  have hc : Continuous fun p : Torus 1 × Torus 1 => KernelGrad.tdist p.1 p.2 := by
    have : (fun p : Torus 1 × Torus 1 => KernelGrad.tdist p.1 p.2) =
        fun p => Real.sqrt (∑ i, ‖(p.1 - p.2) i‖ ^ 2) := funext fun p => CoercAux.tdist_eq_sqrt p.1 p.2
    rw [this]; fun_prop
  have hev : ∀ᶠ p in 𝓝 (y, y), KernelGrad.tdist p.1 p.2 < δ := by
    have := hc.continuousAt (x := (y, y))
    have h0 : KernelGrad.tdist (y, y).1 (y, y).2 = 0 := CoercAux.tdist_self y
    exact this.eventually (gt_mem_nhds (show (fun p : Torus 1 × Torus 1 => KernelGrad.tdist p.1 p.2) (y, y) < δ by simp only [h0]; exact hδ))
  filter_upwards [hev] with p hp
  rw [Real.dist_eq, sub_zero]
  by_cases hxy : p.1 = p.2
  · rw [hxy, kk_diag, abs_zero]; exact hη
  · have hz : p.1 - p.2 ≠ 0 := sub_ne_zero.mpr hxy
    have h1 : |kk l v p.1 p.2| ≤ L * (KernelGrad.tdist p.1 p.2 * ‖SliceAux.sgv l (p.1 - p.2)‖) := by
      simp only [kk, commKernel, hxy, ite_false]
      calc |inner ℝ (v p.1 - v p.2) (SliceAux.sgv l (p.1 - p.2))|
          ≤ ‖v p.1 - v p.2‖ * ‖SliceAux.sgv l (p.1 - p.2)‖ := abs_real_inner_le_norm _ _
        _ ≤ (L * KernelGrad.tdist p.1 p.2) * ‖SliceAux.sgv l (p.1 - p.2)‖ :=
            mul_le_mul_of_nonneg_right (hv _ _) (norm_nonneg _)
        _ = _ := by ring
    have h2 : KernelGrad.tdist p.1 p.2 = KernelGrad.tdist (p.1 - p.2) 0 := EnergyAux.tdist_def _ _
    have h3 := hsmall (p.1 - p.2) hz (by rw [← h2]; exact hp)
    rw [← h2] at h3
    calc |kk l v p.1 p.2| ≤ L * (KernelGrad.tdist p.1 p.2 * ‖SliceAux.sgv l (p.1 - p.2)‖) := h1
      _ ≤ L * (η / (L + 1)) := mul_le_mul_of_nonneg_left h3.le hL
      _ < η := by
          rw [← mul_div_assoc, div_lt_iff₀ (by positivity)]
          nlinarith

end HRS.Commutator.RoughD1
