import HRS.Commutator.Whole.PositiveAux8

/-!
# Helpers for `Positive.lean` (packet `CMX-POS`), part I

Smoothness of `g_1`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff

namespace HRS.Commutator.Whole

open HRS HRS.Whole

variable {d : ℕ} {s : ℝ}

/-- Smoothness of a parametric integral, from a tower of derivatives with integrable bounds. -/
theorem contDiffOn_param_integral {ν : Measure ℝ} {U : Set ℝ} (hU : IsOpen U)
    (Q : ℕ → ℝ → ℝ → ℝ)
    (hmeas : ∀ k, ∀ u ∈ U, AEStronglyMeasurable (Q k u) ν)
    (hint : ∀ k, ∀ u ∈ U, Integrable (Q k u) ν)
    (hder : ∀ k, ∀ u ∈ U, ∃ V ∈ 𝓝 u, ∃ b : ℝ → ℝ, Integrable b ν ∧
      (∀ᵐ t ∂ν, ∀ v ∈ V, ‖Q (k + 1) v t‖ ≤ b t) ∧
      (∀ᵐ t ∂ν, ∀ v ∈ V, HasDerivAt (fun w => Q k w t) (Q (k + 1) v t) v)) :
    ContDiffOn ℝ ∞ (fun u => ∫ t, Q 0 u t ∂ν) U := by
  have hD : ∀ k, ∀ u ∈ U, HasDerivAt (fun w => ∫ t, Q k w t ∂ν) (∫ t, Q (k + 1) u t ∂ν) u := by
    intro k u hu
    obtain ⟨V, hV, b, hb, hbd, hdiff⟩ := hder k u hu
    have hmn : ∀ᶠ x in 𝓝 u, AEStronglyMeasurable (Q k x) ν :=
      Filter.eventually_of_mem (hU.mem_nhds hu) (fun x hx => hmeas k x hx)
    exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le hV hmn (hint k u hu) (hmeas (k + 1) u hu)
      hbd hb hdiff).2
  have key : ∀ n : ℕ, ∀ k, ContDiffOn ℝ n (fun u => ∫ t, Q k u t ∂ν) U := by
    intro n
    induction n with
    | zero =>
      intro k
      rw [Nat.cast_zero, contDiffOn_zero]
      exact fun u hu => (hD k u hu).continuousAt.continuousWithinAt
    | succ n ih =>
      intro k
      rw [Nat.cast_succ, contDiffOn_succ_iff_deriv_of_isOpen hU]
      refine ⟨fun u hu => (hD k u hu).differentiableAt.differentiableWithinAt, ?_, ?_⟩
      · intro h
        exact absurd h (by simp)
      · refine (ih (k + 1)).congr (fun u hu => ?_)
        exact (hD k u hu).deriv
  exact contDiffOn_infty.2 (fun n => key n 0)


/-- coefficients of the derivatives of `z ↦ z^{-(d+2)}`. -/
def qcoef (d : ℕ) : ℕ → ℝ
  | 0 => 1
  | (k + 1) => qcoef d k * (-((d : ℝ) + 2 + k))

/-- `1 + u / t²`. -/
def zz (u t : ℝ) : ℝ := 1 + u * (t ^ 2)⁻¹

/-- the `k`-th `u`-derivative of the integrand `w(t) (zz(u,t)^{-(d+2)} - ε)`. -/
def Qk (d : ℕ) (w : ℝ → ℝ) (ε : ℝ) (k : ℕ) (u t : ℝ) : ℝ :=
  w t * (qcoef d k * ((t ^ 2)⁻¹) ^ k * (zz u t) ^ (-((d : ℝ) + 2 + k)) - (if k = 0 then ε else 0))

lemma zz_ge {η u t : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (hu : -1 + η ≤ u) (ht : 1 ≤ t) : η ≤ zz u t := by
  unfold zz
  have ht2 : 1 ≤ t ^ 2 := by nlinarith
  have hc0 : 0 < (t ^ 2)⁻¹ := by positivity
  have hc1 : (t ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ ht2
  rcases le_total 0 u with h | h
  · have : 0 ≤ u * (t ^ 2)⁻¹ := mul_nonneg h hc0.le
    linarith
  · have : u ≤ u * (t ^ 2)⁻¹ := by nlinarith
    linarith

lemma zz_pos {u t : ℝ} (hu : -1 < u) (ht : 1 ≤ t) : 0 < zz u t := by
  have := zz_ge (η := min 1 ((u + 1) / 2)) (u := u) (t := t) (lt_min one_pos (by linarith)) (min_le_left _ _)
    (by have := min_le_right 1 ((u + 1) / 2); linarith) ht
  have h2 : 0 < min (1:ℝ) ((u + 1) / 2) := lt_min one_pos (by linarith)
  linarith

lemma hasDerivAt_Qk (w : ℝ → ℝ) (ε : ℝ) (k : ℕ) {u t : ℝ} (hz : 0 < zz u t) (ht : 0 < t) :
    HasDerivAt (fun v => Qk d w ε k v t) (Qk d w ε (k + 1) u t) u := by
  unfold Qk
  have h1 : HasDerivAt (fun v : ℝ => zz v t) ((t ^ 2)⁻¹) u := by
    unfold zz
    simpa using ((hasDerivAt_id u).mul_const ((t ^ 2)⁻¹)).const_add 1
  have h2 := h1.rpow_const (p := -((d : ℝ) + 2 + k)) (Or.inl hz.ne')
  have h3 := (h2.const_mul (qcoef d k * ((t ^ 2)⁻¹) ^ k)).sub_const (if k = 0 then ε else 0)
  have h4 := h3.const_mul (w t)
  convert h4 using 1
  simp only [qcoef, Nat.cast_add, Nat.cast_one, if_neg (Nat.succ_ne_zero k), sub_zero]
  have e : -((d : ℝ) + 2 + ((k : ℝ) + 1)) = -((d : ℝ) + 2 + k) - 1 := by ring
  rw [e, pow_succ]
  ring


lemma Qk_bound (w : ℝ → ℝ) (ε : ℝ) (k : ℕ) {η u t : ℝ} (hη : 0 < η) (hη1 : η ≤ 1)
    (hu : -1 + η ≤ u) (ht : 1 ≤ t) (hw : 0 ≤ w t) :
    |Qk d w ε (k + 1) u t| ≤
      w t * |qcoef d (k + 1)| * (t ^ 2)⁻¹ * η ^ (-((d : ℝ) + 2 + ((k + 1 : ℕ) : ℝ))) := by
  have hz := zz_ge hη hη1 hu ht
  have hzpos : 0 < zz u t := lt_of_lt_of_le hη hz
  have ht0 : 0 < t := by linarith
  have hc0 : 0 < (t ^ 2)⁻¹ := by positivity
  have hc1 : (t ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith)
  unfold Qk
  simp only [Nat.succ_ne_zero, if_false, sub_zero]
  rw [abs_mul, abs_of_nonneg hw, abs_mul, abs_mul, abs_of_pos (pow_pos hc0 _),
    abs_of_pos (Real.rpow_pos_of_pos hzpos _)]
  have h1 : ((t ^ 2)⁻¹) ^ (k + 1) ≤ (t ^ 2)⁻¹ := pow_le_of_le_one hc0.le hc1 (Nat.succ_ne_zero k)
  have h2 : zz u t ^ (-((d : ℝ) + 2 + ((k + 1 : ℕ) : ℝ))) ≤ η ^ (-((d : ℝ) + 2 + ((k + 1 : ℕ) : ℝ))) :=
    Real.rpow_le_rpow_of_nonpos hη hz (by
      have : (0:ℝ) ≤ (d : ℝ) + 2 + ((k + 1 : ℕ) : ℝ) := by positivity
      linarith)
  have hq : 0 ≤ |qcoef d (k + 1)| := abs_nonneg _
  calc w t * (|qcoef d (k + 1)| * ((t ^ 2)⁻¹) ^ (k + 1) * zz u t ^ (-((d : ℝ) + 2 + ((k + 1 : ℕ) : ℝ))))
      ≤ w t * (|qcoef d (k + 1)| * (t ^ 2)⁻¹ * η ^ (-((d : ℝ) + 2 + ((k + 1 : ℕ) : ℝ)))) := by
        refine mul_le_mul_of_nonneg_left ?_ hw
        exact mul_le_mul (mul_le_mul_of_nonneg_left h1 hq) h2 (Real.rpow_nonneg hzpos.le _) (by positivity)
    _ = _ := by ring

lemma zz_pow_sub_one_bound {η u t : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (hu : -1 + η ≤ u) (ht : 1 ≤ t) :
    |zz u t ^ (-((d : ℝ) + 2)) - 1| ≤ ((d : ℝ) + 2) * |u| * (t ^ 2)⁻¹ * η ^ (-((d : ℝ) + 2 + 1)) := by
  have ht0 : 0 < t := by linarith
  set P : ℝ → ℝ := fun v => Qk d (fun _ => (1:ℝ)) 0 0 v t with hP
  have hPe : ∀ v, P v = zz v t ^ (-((d : ℝ) + 2)) := by
    intro v; simp [hP, Qk, qcoef]
  have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := P) (f' := fun v => Qk d (fun _ => (1:ℝ)) 0 1 v t) (s := Set.Ici (-1 + η))
    (C := |qcoef d 1| * (t ^ 2)⁻¹ * η ^ (-((d : ℝ) + 2 + ((0 + 1 : ℕ) : ℝ))))
    (fun v hv => (hasDerivAt_Qk (d := d) (fun _ => (1:ℝ)) 0 0
      (lt_of_lt_of_le hη (zz_ge hη hη1 hv ht)) ht0).hasDerivWithinAt)
    (fun v hv => by
      have := Qk_bound (d := d) (fun _ => (1:ℝ)) 0 0 hη hη1 hv ht (by norm_num)
      simpa [Real.norm_eq_abs] using this)
    (convex_Ici _) (show (0:ℝ) ∈ Set.Ici (-1 + η) from by simp only [Set.mem_Ici]; linarith) (hu : u ∈ Set.Ici (-1 + η))
  rw [hPe, hPe] at hmv
  have h0 : zz 0 t ^ (-((d : ℝ) + 2)) = 1 := by simp [zz]
  rw [h0, Real.norm_eq_abs, Real.norm_eq_abs, sub_zero] at hmv
  have hq : |qcoef d 1| = (d : ℝ) + 2 := by
    have : qcoef d 1 = -((d : ℝ) + 2) := by simp [qcoef]
    rw [this, abs_neg, abs_of_nonneg (by positivity : (0:ℝ) ≤ (d : ℝ) + 2)]
  rw [hq] at hmv
  calc _ ≤ _ := hmv
    _ = _ := by ring_nf


section smooth

variable (d s)

/-- the weight `c_φ t^{-s-1}`. -/
def wts (t : ℝ) : ℝ := cPhi d s * t ^ (-s - 1)

/-- `1` for the logarithmic kernel, `0` otherwise. -/
def epsS : ℝ := if s = 0 then 1 else 0

variable {d s}

lemma measurable_wts : Measurable (wts d s) := by unfold wts; fun_prop

lemma wts_nonneg (hs0 : 0 ≤ s) (hs2 : s < 2 * (d : ℝ) + 4) {t : ℝ} (ht : 0 < t) : 0 ≤ wts d s t :=
  mul_nonneg (cPhi_pos d hs0 hs2).le (Real.rpow_nonneg ht.le _)

lemma integrableOn_wts_inv_sq (hs0 : 0 ≤ s) :
    IntegrableOn (fun t : ℝ => wts d s t * (t ^ 2)⁻¹) (Set.Ioi 1) := by
  have h : IntegrableOn (fun t : ℝ => cPhi d s * t ^ (-s - 3)) (Set.Ioi 1) :=
    (integrableOn_Ioi_one_rpow (a := -s - 3) (by linarith)).const_mul (cPhi d s)
  refine h.congr_fun (fun t ht => ?_) measurableSet_Ioi
  have ht0 : 0 < t := lt_trans one_pos ht
  simp only [wts]
  have : t ^ (-s - 3) = t ^ (-s - 1) * (t ^ 2)⁻¹ := by
    rw [show (t ^ 2)⁻¹ = t ^ (-2 : ℝ) by
      rw [Real.rpow_neg ht0.le, show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast], ← Real.rpow_add ht0]
    congr 1; ring
  rw [this]; ring

lemma integrableOn_wts (hs : 0 < s) : IntegrableOn (wts d s) (Set.Ioi 1) := by
  have h : IntegrableOn (fun t : ℝ => cPhi d s * t ^ (-s - 1)) (Set.Ioi 1) :=
    (integrableOn_Ioi_one_rpow (a := -s - 1) (by linarith)).const_mul (cPhi d s)
  exact h

/-- integrability of `Qk k u`. -/
lemma integrable_Qk (hs0 : 0 ≤ s) (hs2 : s < 2 * (d : ℝ) + 4) (k : ℕ) {u : ℝ} (hu : -1 < u) :
    Integrable (Qk d (wts d s) (epsS s) k u) (volume.restrict (Set.Ioi (1:ℝ))) := by
  set η : ℝ := min 1 ((u + 1) / 2) with hη
  have hη0 : 0 < η := lt_min one_pos (by linarith)
  have hη1 : η ≤ 1 := min_le_left _ _
  have hηu : -1 + η ≤ u := by have := min_le_right (1:ℝ) ((u + 1) / 2); linarith
  have hmeas : AEStronglyMeasurable (Qk d (wts d s) (epsS s) k u) (volume.restrict (Set.Ioi (1:ℝ))) := by
    have := measurable_wts (d := d) (s := s)
    exact (by unfold Qk zz; fun_prop : Measurable (Qk d (wts d s) (epsS s) k u)).aestronglyMeasurable
  have hae1 : ∀ᵐ t ∂(volume.restrict (Set.Ioi (1:ℝ))), 1 < t := self_mem_ae_restrict measurableSet_Ioi
  cases k with
  | succ k =>
    have hb : Integrable (fun t : ℝ => (|qcoef d (k + 1)| * η ^ (-((d : ℝ) + 2 + ((k + 1 : ℕ) : ℝ)))) *
        (wts d s t * (t ^ 2)⁻¹)) (volume.restrict (Set.Ioi (1:ℝ))) :=
      (integrableOn_wts_inv_sq hs0).const_mul _
    refine hb.mono' hmeas ?_
    filter_upwards [hae1] with t ht
    have := Qk_bound (d := d) (wts d s) (epsS s) k hη0 hη1 hηu ht.le (wts_nonneg hs0 hs2 (by linarith))
    rw [Real.norm_eq_abs]
    refine this.trans (le_of_eq ?_)
    ring
  | zero =>
    by_cases hs : s = 0
    · have hb : Integrable (fun t : ℝ => (((d : ℝ) + 2) * |u| * η ^ (-((d : ℝ) + 2 + 1))) *
          (wts d s t * (t ^ 2)⁻¹)) (volume.restrict (Set.Ioi (1:ℝ))) :=
        (integrableOn_wts_inv_sq hs0).const_mul _
      refine hb.mono' hmeas ?_
      filter_upwards [hae1] with t ht
      have ht0 : 0 < t := by linarith
      have h1 := zz_pow_sub_one_bound (d := d) hη0 hη1 hηu ht.le
      have hw := wts_nonneg hs0 hs2 ht0
      have hε : epsS s = 1 := by unfold epsS; simp [hs]
      simp only [Qk, qcoef, hε, ite_true, Nat.cast_zero, add_zero, pow_zero, one_mul]
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hw]
      calc wts d s t * |zz u t ^ (-((d : ℝ) + 2)) - 1|
          ≤ wts d s t * (((d : ℝ) + 2) * |u| * (t ^ 2)⁻¹ * η ^ (-((d : ℝ) + 2 + 1))) :=
            mul_le_mul_of_nonneg_left h1 hw
        _ = _ := by ring
    · have hs' : 0 < s := lt_of_le_of_ne hs0 (Ne.symm hs)
      have hb : Integrable (fun t : ℝ => η ^ (-((d : ℝ) + 2)) * wts d s t)
          (volume.restrict (Set.Ioi (1:ℝ))) := (integrableOn_wts hs').const_mul _
      refine hb.mono' hmeas ?_
      filter_upwards [hae1] with t ht
      have ht0 : 0 < t := by linarith
      have hw := wts_nonneg hs0 hs2 ht0
      have hz := zz_ge hη0 hη1 hηu ht.le
      have hzpos : 0 < zz u t := lt_of_lt_of_le hη0 hz
      have hε : epsS s = 0 := by unfold epsS; simp [hs]
      simp only [Qk, qcoef, hε, ite_true, Nat.cast_zero, add_zero, pow_zero, one_mul, sub_zero]
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hw, abs_of_pos (Real.rpow_pos_of_pos hzpos _)]
      have hp : (0:ℝ) ≤ (d : ℝ) + 2 := by positivity
      have : zz u t ^ (-((d : ℝ) + 2)) ≤ η ^ (-((d : ℝ) + 2)) :=
        Real.rpow_le_rpow_of_nonpos hη0 hz (by linarith)
      calc wts d s t * zz u t ^ (-((d : ℝ) + 2)) ≤ wts d s t * η ^ (-((d : ℝ) + 2)) :=
            mul_le_mul_of_nonneg_left this hw
        _ = _ := by ring


lemma aesm_Qk (k : ℕ) (u : ℝ) :
    AEStronglyMeasurable (Qk d (wts d s) (epsS s) k u) (volume.restrict (Set.Ioi (1:ℝ))) := by
  have := measurable_wts (d := d) (s := s)
  exact (by unfold Qk zz; fun_prop : Measurable (Qk d (wts d s) (epsS s) k u)).aestronglyMeasurable

theorem smooth_G (hs0 : 0 ≤ s) (hs2 : s < 2 * (d : ℝ) + 4) :
    ContDiffOn ℝ ∞ (fun u => ∫ t, Qk d (wts d s) (epsS s) 0 u t ∂(volume.restrict (Set.Ioi (1:ℝ))))
      (Set.Ioi (-1)) := by
  refine contDiffOn_param_integral isOpen_Ioi (Qk d (wts d s) (epsS s))
    (fun k u _ => aesm_Qk k u) (fun k u hu => integrable_Qk hs0 hs2 k hu) ?_
  intro k u hu
  have hu : -1 < u := hu
  set η : ℝ := min 1 ((u + 1) / 2) with hη
  have hη0 : 0 < η := lt_min one_pos (by linarith)
  have hη1 : η ≤ 1 := min_le_left _ _
  have hηu : η ≤ (u + 1) / 2 := min_le_right _ _
  refine ⟨Set.Ioi (-1 + η), Ioi_mem_nhds (by linarith), fun t => (|qcoef d (k + 1)| *
    η ^ (-((d : ℝ) + 2 + ((k + 1 : ℕ) : ℝ)))) * (wts d s t * (t ^ 2)⁻¹), ?_, ?_, ?_⟩
  · exact (integrableOn_wts_inv_sq hs0).const_mul _
  · filter_upwards [self_mem_ae_restrict (measurableSet_Ioi (a := (1:ℝ)))] with t ht v hv
    have ht' : 1 < t := ht
    have := Qk_bound (d := d) (wts d s) (epsS s) k hη0 hη1 (le_of_lt hv) ht'.le
      (wts_nonneg hs0 hs2 (by linarith))
    rw [Real.norm_eq_abs]
    refine this.trans (le_of_eq ?_)
    ring
  · filter_upwards [self_mem_ae_restrict (measurableSet_Ioi (a := (1:ℝ)))] with t ht v hv
    have ht' : 1 < t := ht
    exact hasDerivAt_Qk (wts d s) (epsS s) k
      (lt_of_lt_of_le hη0 (zz_ge hη0 hη1 (le_of_lt hv) ht'.le)) (by linarith)


lemma phiR_eq_zz (x : Euc d) (t : ℝ) : phiR d (‖x‖ / t) = zz (‖x‖ ^ 2) t ^ (-((d : ℝ) + 2)) := by
  unfold phiR zz
  rw [div_pow, div_eq_mul_inv]

lemma g1_eq_G (hs0 : 0 ≤ s) (hs2 : s < 2 * (d : ℝ) + 4) (x : Euc d) :
    g1 s x = (if s = 0 then g1Zero d s else 0) +
      ∫ t, Qk d (wts d s) (epsS s) 0 (‖x‖ ^ 2) t ∂(volume.restrict (Set.Ioi (1:ℝ))) := by
  by_cases hs : s = 0
  · subst hs
    have hε : epsS 0 = 1 := by unfold epsS; simp
    have hcp : cPhi d 0 = 1 := by simp [cPhi]
    rw [g1_repr_zero rfl x]
    simp only [ite_true]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    have ht0 : 0 < t := lt_trans one_pos ht
    simp only [Qk, qcoef, hε, ite_true, Nat.cast_zero, add_zero, pow_zero, one_mul, wts, hcp]
    rw [phiR_eq_zz]
    rw [neg_zero, zero_sub, Real.rpow_neg_one]
    ring
  · have hs' : 0 < s := lt_of_le_of_ne hs0 (Ne.symm hs)
    have hε : epsS s = 0 := by unfold epsS; simp [hs]
    rw [g1_repr_pos hs' hs2 x]
    simp only [hs, ite_false, zero_add]
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    simp only [Qk, qcoef, hε, ite_true, Nat.cast_zero, add_zero, pow_zero, one_mul, wts, sub_zero]
    rw [phiR_eq_zz]
    ring

theorem g1_smooth_aux (hs0 : 0 ≤ s) (hs2 : s < 2 * (d : ℝ) + 4) :
    ContDiff ℝ ∞ (g1 s : Euc d → ℝ) := by
  have hG := (smooth_G (d := d) hs0 hs2).comp_contDiff (contDiff_norm_sq ℝ (E := Euc d))
    (fun x => by simp only [Set.mem_Ioi]; have := sq_nonneg ‖x‖; linarith)
  have e : (g1 s : Euc d → ℝ) = fun x => (if s = 0 then g1Zero d s else 0) +
      (fun u => ∫ t, Qk d (wts d s) (epsS s) 0 u t ∂(volume.restrict (Set.Ioi (1:ℝ)))) (‖x‖ ^ 2) :=
    funext (g1_eq_G hs0 hs2)
  rw [e]
  exact contDiff_const.add hG

end smooth

end HRS.Commutator.Whole
