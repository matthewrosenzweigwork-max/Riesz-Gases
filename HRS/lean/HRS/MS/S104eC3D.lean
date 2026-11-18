import HRS.MS.S104eC3C

/-!
# S104E route C, packet C3, file D: the Duhamel estimate

For a family `u v ∈ HolB (N e^{λ(t-v)})` with jointly continuous jets, the Duhamel term `Φ u (r)` is in `HolB (θ(λ) N e^{λ(t-r)})`,
its jets are the integrals of the jets, and the time integrands are interval integrable.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff Interval

namespace HRS.MS.S104e.C

open HRS HRS.Whole HRS.MS.R2WinOrbNL

variable {d : ℕ} {j : ℕ} {η H : ℝ} {P A : ℝ → (Euc d → ℝ) → Euc d → ℝ}

theorem s104c3_cont0 {F : ℝ → Euc d → ℝ} {S : Set ℝ} {x : Euc d}
    (h : ContinuousOn (fun v => iteratedFDeriv ℝ 0 (F v) x) S) : ContinuousOn (fun v => F v x) S := by
  have := (continuousMultilinearCurryFin0 ℝ (Euc d) ℝ).continuous.comp_continuousOn h
  refine this.congr fun v _ => ?_
  simp [iteratedFDeriv_zero_eq_comp]

theorem s104c3_intgbl {G : Type*} [NormedAddCommGroup G] {f : ℝ → G} {b : ℝ → ℝ} {r t : ℝ}
    (hrt : r ≤ t) (hbi : IntervalIntegrable b volume r t) (hc : ContinuousOn f (Ioc r t))
    (hb : ∀ v ∈ Ioc r t, ‖f v‖ ≤ b v) : IntervalIntegrable f volume r t := by
  have hu : Ι r t = Ioc r t := Set.uIoc_of_le hrt
  refine IntervalIntegrable.mono_fun' hbi ?_ ((ae_restrict_iff' measurableSet_uIoc).2
    (ae_of_all _ fun v hv => hb v (by rwa [hu] at hv)))
  rw [hu]; exact hc.aestronglyMeasurable measurableSet_Ioc

theorem s104c3_int_b_le {η : ℝ} (hη1 : η < 1) (hη0 : 0 < η) {CP CA N lam r t H : ℝ} (hCP : 0 ≤ CP)
    (hCA : 0 ≤ CA) (hN : 0 ≤ N) (hr0 : 0 ≤ r) (hrt : r ≤ t) (htH : t ≤ H) :
    ∫ v in r..t, CP * s104c3_k η (v - r) * (CA * (N * Real.exp (lam * (t - v)))) ≤
      CP * CA * (∫ h in (0 : ℝ)..H, s104c3_k η h * Real.exp (-lam * h)) * N * Real.exp (lam * (t - r)) := by
  have e : ∀ v : ℝ, CP * s104c3_k η (v - r) * (CA * (N * Real.exp (lam * (t - v)))) =
      (CP * CA * N * Real.exp (lam * (t - r))) * (s104c3_k η (v - r) * Real.exp (-lam * (v - r))) := by
    intro v
    have : Real.exp (lam * (t - v)) = Real.exp (lam * (t - r)) * Real.exp (-lam * (v - r)) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [this]; ring
  simp_rw [e]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_sub_right (fun h => s104c3_k η h * Real.exp (-lam * h)) r]
  simp only [sub_self]
  have hmono : ∫ h in (0 : ℝ)..(t - r), s104c3_k η h * Real.exp (-lam * h) ≤
      ∫ h in (0 : ℝ)..H, s104c3_k η h * Real.exp (-lam * h) := by
    refine intervalIntegral.integral_mono_interval le_rfl (by linarith) (by linarith) ?_ ?_
    · refine (ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun h hh => ?_)
      exact mul_nonneg (s104c3_k_nonneg η hh.1.le) (Real.exp_pos _).le
    · refine (s104c3_k_int hη1 hη0 0 H).mul_continuousOn ?_
      exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn
  have hE : 0 ≤ CP * CA * N * Real.exp (lam * (t - r)) :=
    mul_nonneg (mul_nonneg (mul_nonneg hCP hCA) hN) (Real.exp_pos _).le
  calc _ ≤ (CP * CA * N * Real.exp (lam * (t - r))) *
        ∫ h in (0 : ℝ)..H, s104c3_k η h * Real.exp (-lam * h) := mul_le_mul_of_nonneg_left hmono hE
    _ = _ := by ring

theorem s104c3_hN {t : ℝ} (ht : 0 ≤ t) {N lam : ℝ} {u : ℝ → Euc d → ℝ}
    (hu : ∀ v ∈ Icc 0 t, HolB j η (N * Real.exp (lam * (t - v))) (u v)) : 0 ≤ N := by
  have := s104c3_HolB_nonneg (hu t ⟨ht, le_rfl⟩)
  simpa using this

theorem s104c3_hgb (hyp : VolHyp d j η H P A) {t : ℝ} (ht : t ∈ Icc 0 H) {N lam : ℝ}
    {u : ℝ → Euc d → ℝ} (hu : ∀ v ∈ Icc 0 t, HolB j η (N * Real.exp (lam * (t - v))) (u v)) :
    ∀ v ∈ Icc 0 t, Bd j (hyp.CA * (N * Real.exp (lam * (t - v)))) (A v (u v)) :=
  fun v hv => hyp.A_bd v ⟨hv.1, hv.2.trans ht.2⟩ _ _ (hu v hv)

theorem s104c3_hF (hyp : VolHyp d j η H P A) {t : ℝ} (ht : t ∈ Icc 0 H) {N lam : ℝ}
    {u : ℝ → Euc d → ℝ} (hu : ∀ v ∈ Icc 0 t, HolB j η (N * Real.exp (lam * (t - v))) (u v))
    {r : ℝ} (hr : r ∈ Icc 0 t) : ∀ v ∈ Ioc r t, HolB j η
      (hyp.CP * s104c3_k η (v - r) * (hyp.CA * (N * Real.exp (lam * (t - v))))) (P (v - r) (A v (u v))) := by
  intro v hv
  have hvt : v ∈ Icc 0 t := ⟨hr.1.trans hv.1.le, hv.2⟩
  exact hyp.P_gain (v - r) (by linarith [hv.1]) (by linarith [hv.2, hr.1, ht.2])
    _ _ (s104c3_hgb hyp ht hu v hvt)

theorem s104c3_hbi {η : ℝ} (hη1 : η < 1) (hη0 : 0 < η) (CP CA N lam t r : ℝ) :
    IntervalIntegrable (fun v => CP * s104c3_k η (v - r) * (CA * (N * Real.exp (lam * (t - v)))))
      volume r t := by
  have hbc : Continuous fun v : ℝ => CA * (N * Real.exp (lam * (t - v))) :=
    continuous_const.mul (continuous_const.mul
      (Real.continuous_exp.comp (continuous_const.mul (continuous_const.sub continuous_id))))
  exact ((s104c3_k_int_shift hη1 hη0 r r t).const_mul CP).mul_continuousOn hbc.continuousOn

theorem s104c3_hM (hyp : VolHyp d j η H P A) (hη0 : 0 < η) {t : ℝ} (ht : t ∈ Icc 0 H) {N lam : ℝ}
    (hlam : 0 ≤ lam) {u : ℝ → Euc d → ℝ}
    (hu : ∀ v ∈ Icc 0 t, HolB j η (N * Real.exp (lam * (t - v))) (u v))
    (huc : ∀ i ≤ j + 1, ContinuousOn (fun p : ℝ × Euc d => iteratedFDeriv ℝ i (u p.1) p.2)
      (Icc 0 t ×ˢ univ)) {r : ℝ} (hr : r ∈ Icc 0 t) :
    ∀ m ≤ j + 1, ∀ x : Euc d,
      ContinuousOn (fun v => iteratedFDeriv ℝ m (P (v - r) (A v (u v))) x) (Ioc r t) := by
  have hN := s104c3_hN ht.1 hu
  have hexp : ∀ v ∈ Icc 0 t, Real.exp (lam * (t - v)) ≤ Real.exp (lam * t) := fun v hv =>
    Real.exp_le_exp.2 (by nlinarith [hv.1])
  have hgb' : ∀ v ∈ Icc 0 t, Bd j (hyp.CA * (N * Real.exp (lam * t))) (A v (u v)) := fun v hv =>
    (s104c3_hgb hyp ht hu v hv).mono_A
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hexp v hv) hN) hyp.CA0)
  have hgj := hyp.A_jc t ht (N * Real.exp (lam * t)) u
    (fun v hv => (hu v hv).mono_B (mul_le_mul_of_nonneg_left (hexp v hv) hN) hη0.le) huc
  have hPj := hyp.P_jc t ht _ (fun v => A v (u v)) hgb' hgj
  intro m hm x
  have hc := (hPj m hm).comp (f := fun v : ℝ => (v - r, v, x))
    (by fun_prop : Continuous fun v : ℝ => (v - r, v, x)).continuousOn (s := Ioc r t) ?_
  · exact hc
  · intro v hv
    simp only [Set.mem_prod, Set.mem_Ioc, Set.mem_Icc, Set.mem_univ, and_true]
    exact ⟨⟨by linarith [hv.1], by linarith [hv.2, hr.1, ht.2]⟩, by linarith [hr.1, hv.1], hv.2⟩

/-- The Duhamel estimate. -/
theorem s104c3_duhamel (hyp : VolHyp d j η H P A) (hη0 : 0 < η) (hη1 : η < 1) {t : ℝ}
    (ht : t ∈ Icc 0 H) {N lam : ℝ} (hlam : 0 ≤ lam) {u : ℝ → Euc d → ℝ}
    (hu : ∀ v ∈ Icc 0 t, HolB j η (N * Real.exp (lam * (t - v))) (u v))
    (huc : ∀ i ≤ j + 1, ContinuousOn (fun p : ℝ × Euc d => iteratedFDeriv ℝ i (u p.1) p.2)
      (Icc 0 t ×ˢ univ)) :
    ∀ r ∈ Icc 0 t, (∀ x, IntervalIntegrable (fun v => P (v - r) (A v (u v)) x) volume r t) ∧
      ContDiff ℝ ((j + 1 : ℕ) : WithTop ℕ∞) (s104c3_Phi P A t u r) ∧
      (∀ m ≤ j + 1, ∀ x, iteratedFDeriv ℝ m (s104c3_Phi P A t u r) x =
        ∫ v in r..t, iteratedFDeriv ℝ m (P (v - r) (A v (u v))) x) ∧
      HolB j η (s104c3_theta hyp lam * N * Real.exp (lam * (t - r))) (s104c3_Phi P A t u r) := by
  intro r hr
  have hHt : t ≤ H := ht.2
  have hCP : 0 ≤ hyp.CP := by linarith [hyp.CP1]
  have hN := s104c3_hN ht.1 hu
  have hF := s104c3_hF hyp ht hu hr
  have hM := s104c3_hM hyp hη0 ht hlam hu huc hr
  have hbi := s104c3_hbi hη1 hη0 hyp.CP hyp.CA N lam t r
  set b : ℝ → ℝ := fun v => hyp.CP * s104c3_k η (v - r) * (hyp.CA * (N * Real.exp (lam * (t - v)))) with hb
  have hint : ∀ m ≤ j + 1, ∀ x : Euc d,
      IntervalIntegrable (fun v => iteratedFDeriv ℝ m (P (v - r) (A v (u v))) x) volume r t :=
    fun m hm x => s104c3_intgbl hr.2 hbi (hM m hm x) (fun v hv => (hF v hv).1.2 m hm x)
  have hJ := s104c3_jets_integral (a := r) (b := t) hr.2 (N := j + 1)
    (Fv := fun v => P (v - r) (A v (u v))) (bnd := b)
    (fun v hv => (hF v hv).1.1) (fun v hv m hm x => (hF v hv).1.2 m hm x) hbi hM
  have hIb := s104c3_int_b_le hη1 hη0 (CP := hyp.CP) (CA := hyp.CA) (N := N) (lam := lam) (r := r)
    (t := t) (H := H) hCP hyp.CA0 hN hr.1 hr.2 hHt
  have hΘ : s104c3_theta hyp lam * N * Real.exp (lam * (t - r)) =
      hyp.CP * hyp.CA * (∫ h in (0 : ℝ)..H, s104c3_k η h * Real.exp (-lam * h)) * N *
        Real.exp (lam * (t - r)) := by unfold s104c3_theta; ring
  refine ⟨fun x => ?_, hJ.1, hJ.2, ?_⟩
  · refine s104c3_intgbl hr.2 hbi (s104c3_cont0 (hM 0 (Nat.zero_le _) x)) (fun v hv => ?_)
    have := (hF v hv).1.2 0 (Nat.zero_le _) x
    rwa [norm_iteratedFDeriv_zero] at this
  · rw [hΘ]
    change HolB j η _ (fun x => ∫ v in r..t, P (v - r) (A v (u v)) x)
    refine ⟨⟨hJ.1, fun m hm x => ?_⟩, fun x z => ?_⟩
    · rw [hJ.2 m hm x]
      exact (intervalIntegral.norm_integral_le_of_norm_le hr.2
        (ae_of_all _ fun v hv => (hF v hv).1.2 m hm x) hbi).trans hIb
    · rw [hJ.2 _ le_rfl, hJ.2 _ le_rfl,
        ← intervalIntegral.integral_sub (hint _ le_rfl (x + z)) (hint _ le_rfl x)]
      have h1 : ‖∫ v in r..t, (iteratedFDeriv ℝ (j + 1) (P (v - r) (A v (u v))) (x + z) -
          iteratedFDeriv ℝ (j + 1) (P (v - r) (A v (u v))) x)‖ ≤ ∫ v in r..t, b v * ‖z‖ ^ η :=
        intervalIntegral.norm_integral_le_of_norm_le hr.2
          (ae_of_all _ fun v hv => (hF v hv).2 x z) (hbi.mul_const _)
      refine h1.trans ?_
      rw [intervalIntegral.integral_mul_const]
      exact mul_le_mul_of_nonneg_right hIb (Real.rpow_nonneg (norm_nonneg _) _)

end HRS.MS.S104e.C
