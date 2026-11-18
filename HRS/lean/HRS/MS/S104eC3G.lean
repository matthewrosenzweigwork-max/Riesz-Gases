import HRS.MS.S104eC3F

/-!
# S104E route C, packet C3, file G: vanishing at infinity and time continuity of the Duhamel term
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff Interval

namespace HRS.MS.S104e.C

open HRS HRS.Whole HRS.MS.R2WinOrbNL

variable {d : ℕ} {j : ℕ} {η H : ℝ} {P A : ℝ → (Euc d → ℝ) → Euc d → ℝ}

theorem s104c3_TC_mono {t : ℝ} {N N' : ℕ} {u : ℝ → Euc d → ℝ} (h : s104c3_TC t N u) (hN : N' ≤ N) :
    s104c3_TC t N' u := fun i hi => h i (hi.trans hN)

theorem s104c3_TC_unif_i {t : ℝ} {u : ℝ → Euc d → ℝ} :
    ∀ (N : ℕ), s104c3_TC t N u → ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ i ≤ N, ∀ r ∈ Icc 0 t,
      ∀ r' ∈ Icc 0 t, |r - r'| < δ → ∀ x : Euc d,
        ‖iteratedFDeriv ℝ i (u r) x - iteratedFDeriv ℝ i (u r') x‖ ≤ ε := by
  intro N
  induction N with
  | zero =>
    intro h ε hε
    obtain ⟨δ, hδ, hh⟩ := h 0 le_rfl ε hε
    exact ⟨δ, hδ, fun i hi => by
      have : i = 0 := Nat.le_zero.1 hi
      subst this; exact hh⟩
  | succ N ih =>
    intro h ε hε
    obtain ⟨δ1, hδ1, h1⟩ := ih (s104c3_TC_mono h (Nat.le_succ N)) ε hε
    obtain ⟨δ2, hδ2, h2⟩ := h (N + 1) le_rfl ε hε
    refine ⟨min δ1 δ2, lt_min hδ1 hδ2, fun i hi r hr r' hr' hrr x => ?_⟩
    rcases Nat.lt_or_ge i (N + 1) with hlt | hge
    · exact h1 i (Nat.lt_succ_iff.1 hlt) r hr r' hr' (lt_of_lt_of_le hrr (min_le_left _ _)) x
    · have : i = N + 1 := le_antisymm hi hge
      subst this
      exact h2 r hr r' hr' (lt_of_lt_of_le hrr (min_le_right _ _)) x

/-- The Duhamel term preserves vanishing at infinity of the jets. -/
theorem s104c3_phi_van (hyp : VolHyp d j η H P A) (hη0 : 0 < η) (hη1 : η < 1) {t : ℝ}
    (ht : t ∈ Icc 0 H) {N lam : ℝ} (hlam : 0 ≤ lam) {u : ℝ → Euc d → ℝ}
    (hu : ∀ v ∈ Icc 0 t, HolB j η (N * Real.exp (lam * (t - v))) (u v))
    (huc : ∀ i ≤ j + 1, ContinuousOn (fun p : ℝ × Euc d => iteratedFDeriv ℝ i (u p.1) p.2)
      (Icc 0 t ×ˢ univ))
    (hv : ∀ v ∈ Icc 0 t, VanB (j + 1) (u v)) :
    ∀ r ∈ Icc 0 t, VanB (j + 1) (s104c3_Phi P A t u r) := by
  intro r hr i hi
  have hD := s104c3_duhamel hyp hη0 hη1 ht hlam hu huc r hr
  have hF := s104c3_hF hyp ht hu hr
  have hM := s104c3_hM hyp hη0 ht hlam hu huc hr
  have hbi := s104c3_hbi hη1 hη0 hyp.CP hyp.CA N lam t r
  have hu' : Ι r t = Ioc r t := Set.uIoc_of_le hr.2
  haveI : (cocompact (Euc d)).IsCountablyGenerated := by
    rw [← Metric.cobounded_eq_cocompact, ← Metric.comap_dist_right_atTop (0 : Euc d)]
    infer_instance
  have hlim : Tendsto (fun x : Euc d => ∫ v in r..t, ‖iteratedFDeriv ℝ i (P (v - r) (A v (u v))) x‖)
      (cocompact (Euc d)) (𝓝 (∫ v in r..t, (fun _ : ℝ => (0 : ℝ)) v)) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun v => hyp.CP * s104c3_k η (v - r) * (hyp.CA * (N * Real.exp (lam * (t - v))))) ?_ ?_ hbi ?_
    · refine Eventually.of_forall fun x => ?_
      rw [hu']
      exact (hM i hi x).norm.aestronglyMeasurable measurableSet_Ioc
    · refine Eventually.of_forall fun x => ae_of_all _ fun v hv' => ?_
      rw [hu'] at hv'
      simpa using (hF v hv').1.2 i hi x
    · refine ae_of_all _ fun v hv' => ?_
      rw [hu'] at hv'
      have hvt : v ∈ Icc 0 t := ⟨hr.1.trans hv'.1.le, hv'.2⟩
      have hH := hyp.A_van v ⟨hvt.1, hvt.2.trans ht.2⟩ _ _ (hu v hvt) (hv v hvt)
      exact hyp.P_vgain (v - r) (by linarith [hv'.1]) (by linarith [hv'.2, hr.1, ht.2]) _ _
        (s104c3_hgb hyp ht hu v hvt) hH i hi
  simp only [intervalIntegral.integral_zero] at hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun x => norm_nonneg _)
    (fun x => ?_)
  rw [hD.2.2.1 i hi x]
  exact intervalIntegral.norm_integral_le_integral_norm hr.2

/-- The Duhamel term is uniformly time continuous in the sup norm of the jets (`≤ j+1`). -/
theorem s104c3_phi_TC (hyp : VolHyp d j η H P A) (hη0 : 0 < η) (hη1 : η < 1) {t : ℝ}
    (ht : t ∈ Icc 0 H) {N lam : ℝ} (hlam : 0 ≤ lam) {u : ℝ → Euc d → ℝ}
    (hu : ∀ v ∈ Icc 0 t, HolB j η (N * Real.exp (lam * (t - v))) (u v))
    (huc : ∀ i ≤ j + 1, ContinuousOn (fun p : ℝ × Euc d => iteratedFDeriv ℝ i (u p.1) p.2)
      (Icc 0 t ×ˢ univ))
    (hTC : s104c3_TC t (j + 1) u) : s104c3_TC t (j + 1) (s104c3_Phi P A t u) := by
  have hHt : t ≤ H := ht.2
  have hCP : 0 < hyp.CP := by linarith [hyp.CP1]
  have hN := s104c3_hN ht.1 hu
  have hexp : ∀ v ∈ Icc 0 t, Real.exp (lam * (t - v)) ≤ Real.exp (lam * t) := fun v hv =>
    Real.exp_le_exp.2 (by nlinarith [hv.1])
  have hgb' : ∀ v ∈ Icc 0 t, Bd j (hyp.CA * (N * Real.exp (lam * t))) (A v (u v)) := fun v hv =>
    (s104c3_hgb hyp ht hu v hv).mono_A
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hexp v hv) hN) hyp.CA0)
  have hgTC : s104c3_TC t j (fun v => A v (u v)) :=
    hyp.A_tc t ht (N * Real.exp (lam * t)) u
      (fun v hv => (hu v hv).mono_B (mul_le_mul_of_nonneg_left (hexp v hv) hN) hη0.le) hTC
  intro i hi ε hε
  -- the kernel `K`
  set Kt : Euc d → ℝ → ℝ → (Euc d [×i]→L[ℝ] ℝ) :=
    fun x h ρ => iteratedFDeriv ℝ i (P h (A ρ (u ρ))) x with hKt
  have hshift : ∀ r ∈ Icc 0 t, ∀ x : Euc d, iteratedFDeriv ℝ i (s104c3_Phi P A t u r) x =
      ∫ h in (0 : ℝ)..(t - r), Kt x h (h + r) := by
    intro r hr x
    have hD := s104c3_duhamel hyp hη0 hη1 ht hlam hu huc r hr
    rw [hD.2.2.1 i hi x]
    have := intervalIntegral.integral_comp_add_right
      (fun v => iteratedFDeriv ℝ i (P (v - r) (A v (u v))) x) (a := 0) (b := t - r) r
    simp only [zero_add, sub_add_cancel] at this
    rw [← this]
    simp only [hKt, add_sub_cancel_right]
  have hcore := s104c3_TC_core (G := Euc d [×i]→L[ℝ] ℝ) (Y := Euc d) hη1 hη0 ht.1 hHt Kt
    (C := hyp.CP * hyp.CA * N * Real.exp (lam * t))
    (mul_nonneg (mul_nonneg (mul_nonneg hCP.le hyp.CA0) hN) (Real.exp_pos _).le) ?_ ?_ ?_
  · obtain ⟨δ, hδ, hh⟩ := hcore ε hε
    refine ⟨δ, hδ, fun r hr r' hr' hrr x => ?_⟩
    rcases le_total r r' with hle | hle
    · rw [hshift r hr x, hshift r' hr' x]
      refine hh x r hr r' hr' hle ?_
      rw [abs_sub_comm, abs_of_nonneg (by linarith)] at hrr
      linarith [abs_sub_comm r r', abs_of_nonneg (sub_nonneg.2 hle)]
    · rw [norm_sub_rev, hshift r hr x, hshift r' hr' x]
      refine hh x r' hr' r hr hle ?_
      rw [abs_of_nonneg (sub_nonneg.2 hle)] at hrr
      linarith [abs_of_nonneg (sub_nonneg.2 hle)]
  · -- integrability
    intro x r hr
    have hF := s104c3_hF hyp ht hu hr
    have hM := s104c3_hM hyp hη0 ht hlam hu huc hr
    have hbi := s104c3_hbi hη1 hη0 hyp.CP hyp.CA N lam t r
    have := s104c3_intgbl hr.2 hbi (hM i hi x) (fun v hv => (hF v hv).1.2 i hi x)
    simpa [hKt] using this.comp_add_right r
  · -- pointwise bound
    intro x r hr h hh
    have hF := s104c3_hF hyp ht hu hr
    have hv : h + r ∈ Ioc r t := ⟨by linarith [hh.1], by linarith [hh.2]⟩
    have hb := (hF (h + r) hv).1.2 i hi x
    have e : h + r - r = h := by ring
    rw [e] at hb
    have hvt : h + r ∈ Icc 0 t := ⟨by linarith [hr.1, hh.1], hv.2⟩
    have hk : 0 ≤ s104c3_k η h := s104c3_k_nonneg η hh.1.le
    calc ‖Kt x h (h + r)‖ ≤ hyp.CP * s104c3_k η h * (hyp.CA * (N * Real.exp (lam * (t - (h + r))))) := hb
      _ ≤ hyp.CP * s104c3_k η h * (hyp.CA * (N * Real.exp (lam * t))) := by
        refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hCP.le hk)
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hexp _ hvt) hN) hyp.CA0
      _ = _ := by ring
  · -- difference bound
    intro ε' hε'
    obtain ⟨δ, hδ, hh⟩ := s104c3_TC_unif_i j hgTC (ε' / hyp.CP) (by positivity)
    refine ⟨δ, hδ, fun x r hr r' hr' hrr hd h hh' => ?_⟩
    have hhH : h ≤ H := by linarith [hh'.2, hr'.1, hr'.2]
    have hv1 : h + r ∈ Icc 0 t := ⟨by linarith [hr.1, hh'.1], by linarith [hh'.2, hrr]⟩
    have hv2 : h + r' ∈ Icc 0 t := ⟨by linarith [hr'.1, hh'.1], by linarith [hh'.2]⟩
    have hg1 := hgb' _ hv1
    have hg2 := hgb' _ hv2
    set g1 := A (h + r) (u (h + r)) with hg1def
    set g2 := A (h + r') (u (h + r')) with hg2def
    have hDd : Bd j (ε' / hyp.CP) (fun y => -1 * g2 y + g1 y) := by
      refine ⟨(contDiff_const.mul hg2.1).add hg1.1, fun m hm y => ?_⟩
      rw [s104c3_jets_lin_apply (-1) hg2.1 hg1.1 hm y]
      have := hh m hm (h + r) hv1 (h + r') hv2 (by
        rw [show h + r - (h + r') = r - r' by ring, abs_sub_comm, abs_of_nonneg (by linarith)]; linarith) y
      have e : (-1 : ℝ) • iteratedFDeriv ℝ m g2 y + iteratedFDeriv ℝ m g1 y =
          iteratedFDeriv ℝ m g1 y - iteratedFDeriv ℝ m g2 y := by rw [neg_one_smul]; abel
      rw [e]; exact this
    have hPg := hyp.P_gain h hh'.1 hhH _ _ hDd
    have hPl := hyp.P_lin h hh'.1.le (-1) _ _ g2 g1 (s104c3_Bd_zero_of hg2) (s104c3_Bd_zero_of hg1)
    have hP1 := hyp.P_gain h hh'.1 hhH _ _ hg1
    have hP2 := hyp.P_gain h hh'.1 hhH _ _ hg2
    rw [hPl] at hPg
    have hb := hPg.1.2 i hi x
    rw [s104c3_jets_lin_apply (-1) hP2.1.1 hP1.1.1 hi x] at hb
    have e : (-1 : ℝ) • iteratedFDeriv ℝ i (P h g2) x + iteratedFDeriv ℝ i (P h g1) x =
        Kt x h (h + r) - Kt x h (h + r') := by
      simp only [hKt]; rw [neg_one_smul]; abel
    rw [e] at hb
    refine hb.trans (le_of_eq ?_)
    unfold s104c3_k
    field_simp

end HRS.MS.S104e.C
