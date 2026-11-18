import HRS.MS.Fp81S21CovRS9

/-! The physical covariance RS statement, with coordinate integrability proved
locally from the moving-standard data on its small-radius range. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Filter Topology Set
open scoped BigOperators
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R2Interp HRS.MS.CovMeas
open HRS.MC.Sec7.PI HRS.MC.Sec7.S7PIF6

/-- The exact physical moving covariance RS contract. Its `hh2` coordinate
integrability follows from the moving-standard data available at the selected
small radius. -/
theorem fp81s21_moving_covariance_rs
    (p : Parameters) : fp81s21_moving_covariance_rs_statement p := by
  obtain ⟨δrs, hδrs, hhalfRs, hfamilies⟩ :=
    fp81s21_moving_covariance_rsbv_families p
  obtain ⟨δi, hδi, hhalfI, hinputs⟩ := fp81s21_moving_inputs_all p
  refine ⟨min δrs δi, lt_min hδrs hδi,
    (min_le_left _ _).trans hhalfRs, ?_⟩
  intro δ hδ hδle R
  have hδrs' : δ ≤ δrs := hδle.trans (min_le_left _ _)
  have hδi' : δ ≤ δi := hδle.trans (min_le_right _ _)
  obtain ⟨future, hfuture, hfor⟩ := hfamilies δ hδ hδrs' R
  refine ⟨future, hfuture, ?_⟩
  intro a ha hH N hN A F
  obtain ⟨c, hstd, hphys⟩ := hinputs δ hδ hδi' R a ha
  obtain ⟨Yh, Fj, V, hYm, hFm, hVi, hF0, hgood, hfamily⟩ :=
    hfor a ha hH N hN A F
  refine ⟨Yh, Fj, V, hYm, hFm, hVi, hF0, hgood, ?_⟩
  intro Φ hΦ
  obtain ⟨M, hMi, hlevels⟩ := hfamily Φ hΦ
  refine ⟨M, hMi, ?_⟩
  intro L
  obtain ⟨WS, hmajor⟩ := hlevels L
  refine ⟨WS, ?_⟩
  intro q r hq hqr hr
  obtain ⟨hMajInt, hMajBound⟩ := hmajor q r hq hqr hr
  refine ⟨hMajInt, ?_, hMajBound⟩
  let H : ℝ := a + p.T
  let C : WholeCoeff p.d := r26t3_coeff R
  let m : ℝ := (wholeSpaceIndex p.d : ℝ)
  let B_H := OscPath p.d m H
  let τ : Fin (s102_q p.d L) → Icc (0 : ℝ) H := s102_tauk hH L
  let α : Fin (s102_q p.d L) → MultiIndex p.d := s102_alk L
  let W : B_H →L[ℝ] Window p :=
    HRS.MS.ProClosureS111.physicalWindowRestriction
      (d := p.d) (m := (wholeSpaceIndex p.d : ℝ))
      (T := p.T) (H := a + p.T) ha le_rfl
  let Ψ : B_H → ℝ := fun w => Φ (W w)
  let G : EuclideanSpace ℝ (Fin (s102_q p.d L)) → ℝ :=
    fun x => Φ (W (s102_Lam (a + p.T) L x))
  have hG5 : MemCb 5 G := by
    have hΨ : MemCb 5 (fun w => Φ (W w)) :=
      (HRS.MC.Sec7.S7PIS2.s7_PIS_memCb_comp_proof W hΦ).1
    exact (HRS.MC.Sec7.S7PIS2.s7_PIS_memCb_comp_proof
      (s102_Lam (a + p.T) L) hΨ).1
  have hG : MemCb 2 G := ⟨hG5.1.of_le (by norm_num),
    fun j hj => hG5.2 j (by omega)⟩
  have hcov : ∀ i j, ContinuousOn
      (fun u => s102_obsCov C m τ α u i j) (Icc 0 H) :=
    fun i j => s102_obsCov_cont hH L (fp81s21_moving_gramInt hstd L) i j
  have hfun : (fun w => Ψ (s102_Pj H hH L w)) =
      fun w => G (s102_obs τ α w) := by
    funext w
    dsimp only [G, Ψ, W, τ, α, H, B_H]
    rw [s102_Pj_eq_Lam hH L w]
  let zA (ω : A.Ω) : ℝ → (Euc p.d → ℝ) → ℝ := fun v =>
    s102_etaf (r26t3_mu R v) A.X ω v
  let zF (ω : A.Ω) : ℝ → (Euc p.d → ℝ) → ℝ := fun v =>
    s102_etaf (r26t3_mu R v) F.X ω v
  filter_upwards [hgood,
    fp81s21_moving_hh2_integrable_of_movingStd p R hH hstd hN A L,
    F.indist, WS.value_isRS q r hq hqr hr] with ω hg hzi hind hRS
  have hzEq : zF ω = zA ω := by
    funext v f
    simp [zF, zA, s102_etaf, hind v.toNNReal]
  have hRS' : fp81s21_IsRSOn q r (fun t u v =>
      fp81s21_covariance_pairingCLM
        (iteratedFDeriv ℝ 2 (r2HeatFn (future H)
          (fun w => G (s102_obs τ α w)) t) (Yh ω t))
        (Fj ω v - Fj ω u)) (WS.value q r ω) := by
    change fp81s21_IsRSOn q r (fun t u v =>
      fp81s21_covariance_pairingCLM
        (iteratedFDeriv ℝ 2 (r2HeatFn (future H)
          (fun w => Ψ (s102_Pj H hH L w)) t) (Yh ω t))
        (Fj ω v - Fj ω u)) (WS.value q r ω) at hRS
    rw [hfun] at hRS
    exact hRS
  let dens : ℝ → ℝ := fun u => ∑ i, ∑ j,
    iteratedFDeriv ℝ 2 (gaussHeat (s102_obsCov C m τ α) G u)
      (s102_obs τ α (Yh ω u))
      ![EuclideanSpace.single i 1, EuclideanSpace.single j 1] *
    (2 * C.ν * s102_hh2 C m τ α (zA ω) i j u)
  have hval := fp81s21_cylindrical_covariance_rs_value
    (C := C) (m := m) (H := a + p.T) hH
    (future H) (hfuture.2.1 H hH) τ α hcov G hG (Yh ω) hg.2.1
    (zA ω) (Fj ω) hg.2.2.1
    (fun i j => hzi i j) q r hq hqr hr (WS.value q r ω) hRS'
  have hheq : ∀ i j,
      s102_hh2 C m τ α (zF ω) i j = s102_hh2 C m τ α (zA ω) i j := by
    intro i j
    rw [hzEq]
  have heq : ∀ u ∈ Ioc q r,
      dens u = fp81s21_moving_covariance_cyl_sum p R A F a ha hH L Φ ω u := by
    intro u hu
    have huH : u ∈ Icc (0 : ℝ) H :=
      ⟨hq.trans hu.1.le, hu.2.trans hr⟩
    simp only [dens, fp81s21_moving_covariance_cyl_sum]
    dsimp only [τ, α, H, C, m, W, Ψ, G, zA, zF]
    rw [hg.1 u huH]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hheq i j]
  have hout := hval.1.congr_fun heq measurableSet_Ioc
  exact ⟨hout, hval.2.trans (setIntegral_congr_fun measurableSet_Ioc heq)⟩

#print axioms HRS.Fp81.S21.fp81s21_moving_covariance_rs

end HRS.Fp81.S21
end
