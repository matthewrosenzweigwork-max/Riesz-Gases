import HRS.MS.Fp81S21FinProj3

/-! Finite projection identity for caller-supplied shared versions and RS values. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Filter Topology Set
open scoped BigOperators
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R2Interp
open HRS.MC.Sec7.PI HRS.MC.Sec7.S7PIF6

private theorem fp81s21_moving_g6_drift_value
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (a : ℝ) (ha : 0 ≤ a) (hH : 0 < a + p.T)
    {N : ℕ} (A : Particle R N) (F : FilteredParticle A)
    {c : MultiIndex p.d → ℝ}
    (hstd : Fp81MovingStd (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ)
      (a + p.T) (2 * p.d + 8) c hH)
    (hlin : S102Lin (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) (a + p.T))
    (hr0 : (p.d : ℝ) / 2 + 2 < (2 * p.d + 8 : ℕ))
    (future : (H : ℝ) → ℝ → Measure (OscPath p.d (wholeSpaceIndex p.d : ℝ) H))
    (hfuture : fp81s21_moving_heat_full_clause p R future)
    (L : ℕ) (Φ : Window p → ℝ) (hΦ : MemCb 5 Φ)
    (Yh Fd : A.Ω → ℝ → OscPath p.d (wholeSpaceIndex p.d : ℝ) (a + p.T))
    (hYae : ∀ᵐ ω ∂A.P, ∀ t ∈ Icc (0 : ℝ) (a + p.T),
      Yh ω t = s102_Y (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ)
        (a + p.T) A.P A.X ω t)
    (hYc : ∀ᵐ ω ∂A.P, ContinuousOn (Yh ω) (Icc 0 (a + p.T)))
    (hFdInc : ∀ᵐ ω ∂A.P,
      ∀ q r, 0 ≤ q → q ≤ r → r ≤ a + p.T →
        Fd ω r - Fd ω q = r2DriftInc (r26t3_coeff R)
          (wholeSpaceIndex p.d : ℝ) (a + p.T)
          (fun u f => r2QuadField p.s (r26t3_mu R u) A.P A.X u ω f) q r)
    (Mb : A.Ω → ℝ → ℝ)
    (hMb : ∀ᵐ ω ∂A.P,
      S102Drift (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) (a + p.T)
        (2 * p.d + 8) ((p.d : ℝ) + 2)
        (fun u f => r2QuadField p.s (r26t3_mu R u) A.P A.X u ω f) (Mb ω))
    (WSd : fp81s21_RSBVWindow A.P (a + p.T)
      (fp81s21_finproj_drift_adapter p R A a ha hH future L Φ Yh) Fd)
    (q r : ℝ) (hq : 0 ≤ q) (hqr : q ≤ r) (hr : r ≤ a + p.T) :
    ∀ᵐ ω ∂A.P,
      IntegrableOn (fp81s21_moving_drift_cyl_sum p R A F a ha hH L Φ ω)
        (Ioc q r) ∧
      WSd.value q r ω = ∫ u in Ioc q r,
        fp81s21_moving_drift_cyl_sum p R A F a ha hH L Φ ω u := by
  classical
  let H : ℝ := a + p.T
  let C : WholeCoeff p.d := r26t3_coeff R
  let m : ℝ := (wholeSpaceIndex p.d : ℝ)
  let W : OscPath p.d m H →L[ℝ] Window p :=
    HRS.MS.ProClosureS111.physicalWindowRestriction
      (d := p.d) (m := m) (T := p.T) (H := H) ha le_rfl
  let Ψ : OscPath p.d m H → ℝ := fun w => Φ (W w)
  let G : EuclideanSpace ℝ (Fin (s102_q p.d L)) → ℝ :=
    fun x => Φ (W (s102_Lam H L x))
  let τ : Fin (s102_q p.d L) → Icc (0 : ℝ) H := s102_tauk hH L
  let α : Fin (s102_q p.d L) → MultiIndex p.d := s102_alk L
  have hG5 : MemCb 5 G := by
    have hΨ : MemCb 5 Ψ := (HRS.MC.Sec7.S7PIS2.s7_PIS_memCb_comp_proof W hΦ).1
    exact (HRS.MC.Sec7.S7PIS2.s7_PIS_memCb_comp_proof (s102_Lam H L) hΨ).1
  have hG : MemCb 2 G :=
    ⟨hG5.1.of_le (by norm_num), fun j hj => hG5.2 j (by omega)⟩
  have hcov : ∀ i j, ContinuousOn
      (fun u => s102_obsCov C m τ α u i j) (Icc 0 H) :=
    fun i j => s102_obsCov_cont hH L (fp81s21_moving_gramInt hstd L) i j
  have hfun : (fun w => Ψ (s102_Pj H hH L w)) =
      fun w => G (s102_obs τ α w) := by
    funext w
    dsimp only [G, Ψ, W, τ, α]
    rw [s102_Pj_eq_Lam hH L w]
  filter_upwards [hYae, hYc, hFdInc, hMb, F.indist,
    WSd.value_isRS q r hq hqr hr] with ω hy hyc hinc hMbω hind hRS
  have hRS' : fp81s21_IsRSOn q r (fun t u v =>
      fderiv ℝ (r2HeatFn (future H)
        (fun w => G (s102_obs τ α w)) t) (Yh ω t) (Fd ω v - Fd ω u))
      (WSd.value q r ω) := by
    change fp81s21_IsRSOn q r (fun t u v =>
      fderiv ℝ (r2HeatFn (future H)
        (fun w => Ψ (s102_Pj H hH L w)) t) (Yh ω t) (Fd ω v - Fd ω u))
      (WSd.value q r ω) at hRS
    rw [hfun] at hRS
    exact hRS
  have hPdim : (p.d : ℝ) < 2 * ((p.d : ℝ) + 2) := by
    have hd0 : (0 : ℝ) ≤ p.d := Nat.cast_nonneg _
    linarith
  let bω : ℝ → (Euc p.d → ℝ) → ℝ := fun u f =>
    r2QuadField p.s (r26t3_mu R u) A.P A.X u ω f
  have hval := fp81s21_cylindrical_drift_rs_value hPdim hstd.hD hlin hMbω
    hH (future H) (hfuture.2.1 H hH) τ α hcov G hG (Yh ω) (Fd ω) hyc
    (fun u v hu huv hv => hinc u v hu huv hv) q r hq hqr hr
    (WSd.value q r ω) hRS'
  have hfield : (fun u f =>
      r2QuadField p.s (r26t3_mu R u) A.P F.X u ω f) = bω := by
    funext u f
    unfold r2QuadField
    have hInt : (fun ζ => pairEnergy
        (commutatorKernel p.d p.s (fun x => gradient f x))
        (F.X u.toNNReal ζ) (r26t3_mu R u)) =ᵐ[A.P]
        (fun ζ => pairEnergy
        (commutatorKernel p.d p.s (fun x => gradient f x))
        (A.X u.toNNReal ζ) (r26t3_mu R u)) := by
      filter_upwards [F.indist] with ζ hζ
      rw [hζ u.toNNReal]
    rw [hind u.toNNReal, integral_congr_ae hInt]
    rfl
  have heq : ∀ u ∈ Ioc q r,
      (∑ i, fderiv ℝ (gaussHeat (s102_obsCov C m τ α) G u)
        (s102_obs τ α (Yh ω u)) (EuclideanSpace.single i 1) *
        s102_hh C m τ α bω i u) =
      fp81s21_moving_drift_cyl_sum p R A F a ha hH L Φ ω u := by
    intro u hu
    have huH : u ∈ Icc (0 : ℝ) H := ⟨hq.trans hu.1.le, hu.2.trans hr⟩
    simp only [fp81s21_moving_drift_cyl_sum, ← hfield, hy u huH,
      H, C, m, τ, α, G, W]
  refine ⟨hval.1.congr_fun heq measurableSet_Ioc, ?_⟩
  exact hval.2.trans (setIntegral_congr_fun measurableSet_Ioc heq)

private theorem fp81s21_moving_g6_covariance_value
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (a : ℝ) (ha : 0 ≤ a) (hH : 0 < a + p.T)
    {N : ℕ} (hN : 2 ≤ N) (A : Particle R N) (F : FilteredParticle A)
    {c : MultiIndex p.d → ℝ}
    (hstd : Fp81MovingStd (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ)
      (a + p.T) (2 * p.d + 8) c hH)
    (future : (H : ℝ) → ℝ → Measure (OscPath p.d (wholeSpaceIndex p.d : ℝ) H))
    (hfuture : fp81s21_moving_heat_full_clause p R future)
    (L : ℕ) (Φ : Window p → ℝ) (hΦ : MemCb 5 Φ)
    (Yh : A.Ω → ℝ → OscPath p.d (wholeSpaceIndex p.d : ℝ) (a + p.T))
    (Fj : A.Ω → ℝ → projTensor
      (OscPath p.d (wholeSpaceIndex p.d : ℝ) (a + p.T)) 2)
    (V : A.Ω → ℝ)
    (hgood : ∀ᵐ ω ∂A.P,
      (∀ t ∈ Icc (0 : ℝ) (a + p.T),
        Yh ω t = s102_Y (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ)
          (a + p.T) A.P A.X ω t) ∧
      ContinuousOn (Yh ω) (Icc 0 (a + p.T)) ∧
      (∀ q r, 0 ≤ q → q ≤ r → r ≤ a + p.T →
        IsR2JValue (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) (a + p.T)
          (fp81s21_movingRawEtaField p R A ω) (Ioc q r)
          (((Fj ω r - Fj ω q : projTensor
            (OscPath p.d (wholeSpaceIndex p.d : ℝ) (a + p.T)) 2) : TensorDual
            (OscPath p.d (wholeSpaceIndex p.d : ℝ) (a + p.T)) 2))) ∧
      ContinuousOn (Fj ω) (Icc 0 (a + p.T)) ∧
      BoundedVariationOn (Fj ω) (Icc 0 (a + p.T)) ∧
      (eVariationOn (Fj ω) (Icc 0 (a + p.T))).toReal ≤ V ω)
    (hzi : ∀ᵐ ω ∂A.P, ∀ i j : Fin (s102_q p.d L),
      IntegrableOn
        (s102_hh2 (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ)
          (s102_tauk hH L) (s102_alk L)
          (fun v => s102_etaf (r26t3_mu R v) A.X ω v) i j)
        (Icc (0 : ℝ) (a + p.T)))
    (WSj : fp81s21_RSBVWindow A.P (a + p.T)
      (fp81s21_finproj_covariance_adapter p R A a ha hH future L Φ Yh) Fj)
    (q r : ℝ) (hq : 0 ≤ q) (hqr : q ≤ r) (hr : r ≤ a + p.T) :
    ∀ᵐ ω ∂A.P,
      IntegrableOn (fp81s21_moving_covariance_cyl_sum p R A F a ha hH L Φ ω)
        (Ioc q r) ∧
      WSj.value q r ω = ∫ u in Ioc q r,
        fp81s21_moving_covariance_cyl_sum p R A F a ha hH L Φ ω u := by
  classical
  let H : ℝ := a + p.T
  let C : WholeCoeff p.d := r26t3_coeff R
  let m : ℝ := (wholeSpaceIndex p.d : ℝ)
  let B_H := OscPath p.d m H
  let W : B_H →L[ℝ] Window p :=
    HRS.MS.ProClosureS111.physicalWindowRestriction
      (d := p.d) (m := m) (T := p.T) (H := H) ha le_rfl
  let Ψ : B_H → ℝ := fun w => Φ (W w)
  let G : EuclideanSpace ℝ (Fin (s102_q p.d L)) → ℝ :=
    fun x => Φ (W (s102_Lam H L x))
  let τ : Fin (s102_q p.d L) → Icc (0 : ℝ) H := s102_tauk hH L
  let α : Fin (s102_q p.d L) → MultiIndex p.d := s102_alk L
  have hG5 : MemCb 5 G := by
    have hΨ : MemCb 5 Ψ := (HRS.MC.Sec7.S7PIS2.s7_PIS_memCb_comp_proof W hΦ).1
    exact (HRS.MC.Sec7.S7PIS2.s7_PIS_memCb_comp_proof
      (s102_Lam H L) hΨ).1
  have hG : MemCb 2 G :=
    ⟨hG5.1.of_le (by norm_num), fun j hj => hG5.2 j (by omega)⟩
  have hcov : ∀ i j, ContinuousOn
      (fun u => s102_obsCov C m τ α u i j) (Icc 0 H) :=
    fun i j => s102_obsCov_cont hH L (fp81s21_moving_gramInt hstd L) i j
  have hfun : (fun w => Ψ (s102_Pj H hH L w)) =
      fun w => G (s102_obs τ α w) := by
    funext w
    dsimp only [G, Ψ, W, τ, α]
    rw [s102_Pj_eq_Lam hH L w]
  let zA (ω : A.Ω) : ℝ → (Euc p.d → ℝ) → ℝ := fun v =>
    s102_etaf (r26t3_mu R v) A.X ω v
  let zF (ω : A.Ω) : ℝ → (Euc p.d → ℝ) → ℝ := fun v =>
    s102_etaf (r26t3_mu R v) F.X ω v
  filter_upwards [hgood, hzi, F.indist,
    WSj.value_isRS q r hq hqr hr] with ω hg hziω hind hRS
  have hzEq : zF ω = zA ω := by
    funext v f
    simp [zF, zA, s102_etaf, hind v.toNNReal]
  have hRS' : fp81s21_IsRSOn q r (fun t u v =>
      fp81s21_covariance_pairingCLM
        (iteratedFDeriv ℝ 2 (r2HeatFn (future H)
          (fun w => G (s102_obs τ α w)) t) (Yh ω t))
        (Fj ω v - Fj ω u)) (WSj.value q r ω) := by
    change fp81s21_IsRSOn q r (fun t u v =>
      fp81s21_covariance_pairingCLM
        (iteratedFDeriv ℝ 2 (r2HeatFn (future H)
          (fun w => Ψ (s102_Pj H hH L w)) t) (Yh ω t))
        (Fj ω v - Fj ω u)) (WSj.value q r ω) at hRS
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
    (zA ω) (Fj ω) hg.2.2.1 (fun i j => hziω i j)
    q r hq hqr hr (WSj.value q r ω) hRS'
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
  refine ⟨hval.1.congr_fun heq measurableSet_Ioc, ?_⟩
  exact hval.2.trans (setIntegral_congr_fun measurableSet_Ioc heq)



theorem fp81s21_moving_heat_ito_finite_projection_expectation_identity_of_data
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    (a : ℝ) (ha : 0 ≤ a) (hH : 0 < a + p.T)
    {N : ℕ} (hN : 2 ≤ N) (A : Particle R N) (F : FilteredParticle A)
    {c : MultiIndex p.d → ℝ}
    (hstd : Fp81MovingStd (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ)
      (a + p.T) (2 * p.d + 8) c hH)
    (hlin : S102Lin (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) (a + p.T))
    (hphys : Fp81MovingPhysicalInputs R hN A (a + p.T))
    (future : (H : ℝ) → ℝ → Measure (OscPath p.d (wholeSpaceIndex p.d : ℝ) H))
    (hfuture : fp81s21_moving_heat_full_clause p R future) (D : fp81s21_finproj_shared_data p R a A F)
    (Φ : Window p → ℝ) (hΦ : MemCb 5 Φ)
    (WS : fp81s21_finproj_shared_RS_family p R a ha hH A future F Φ D) :
    ∀ L q r, 0 ≤ q → q ≤ r → r ≤ a + p.T →
      Real.sqrt N *
        ((∫ ω, fp81s21_moving_heat_ito_endpoint
            p R A a ha hH future L Φ r ω ∂A.P) -
          (∫ ω, fp81s21_moving_heat_ito_endpoint
            p R A a ha hH future L Φ q ω ∂A.P)) =
        fp81s21_WindowRS_corr (WS L) q r := by
  classical
  let H : ℝ := a + p.T
  let B_H := OscPath p.d (wholeSpaceIndex p.d : ℝ) H
  let Yh := D.Yh
  let Fd := D.Fd
  let Fj := D.Fj
  let Vd := D.Vd
  let Vj := D.Vj
  have hYm := D.Yh_measurable
  have hYae := D.Yh_ae
  have hYc := D.Yh_continuous
  have hFdGood := D.Fd_good
  have hFjGood := D.Fj_good
  let V : A.Ω → ℝ := fun ω => Vd ω + Vj ω
  have hVInt : Integrable V A.P := D.Vd_integrable.add D.Vj_integrable
  have hVdNonneg : ∀ᵐ ω ∂A.P, 0 ≤ Vd ω := by
    filter_upwards [hFdGood] with ω hg
    exact (ENNReal.toReal_nonneg).trans hg.2.2.2.1
  have hVjNonneg : ∀ᵐ ω ∂A.P, 0 ≤ Vj ω := by
    filter_upwards [hFjGood] with ω hg
    exact (ENNReal.toReal_nonneg).trans hg.2.2.2
  have hFdCont : ∀ᵐ ω ∂A.P, ContinuousOn (Fd ω) (Icc 0 H) :=
    hFdGood.mono fun _ hg => hg.2.1
  have hFdVar : ∀ᵐ ω ∂A.P,
      BoundedVariationOn (Fd ω) (Icc 0 H) ∧
        (eVariationOn (Fd ω) (Icc 0 H)).toReal ≤ V ω := by
    filter_upwards [hFdGood, hVjNonneg] with ω hd hvj
    refine ⟨hd.2.2.1, ?_⟩
    dsimp [V]
    linarith [hd.2.2.2.1]
  have hFjCont : ∀ᵐ ω ∂A.P, ContinuousOn (Fj ω) (Icc 0 H) :=
    hFjGood.mono fun _ hg => hg.2.1
  have hFjVar : ∀ᵐ ω ∂A.P,
      BoundedVariationOn (Fj ω) (Icc 0 H) ∧
        (eVariationOn (Fj ω) (Icc 0 H)).toReal ≤ V ω := by
    filter_upwards [hFjGood, hVdNonneg] with ω hj hvd
    refine ⟨hj.2.2.1, ?_⟩
    dsimp [V]
    linarith [hj.2.2.2]
  have hFdInc : ∀ᵐ ω ∂A.P,
      ∀ q r, 0 ≤ q → q ≤ r → r ≤ H →
        Fd ω r - Fd ω q = r2DriftInc (r26t3_coeff R)
          (wholeSpaceIndex p.d : ℝ) H
          (fun u f => r2QuadField p.s (r26t3_mu R u) A.P A.X u ω f) q r := by
    filter_upwards [hFdGood] with ω hg
    exact hg.2.2.2.2
  have hJGood : ∀ᵐ ω ∂A.P,
      (∀ t ∈ Icc (0 : ℝ) H,
        Yh ω t = s102_Y (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ)
          H A.P A.X ω t) ∧
      ContinuousOn (Yh ω) (Icc 0 H) ∧
      (∀ q r, 0 ≤ q → q ≤ r → r ≤ H →
        IsR2JValue (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) H
          (fp81s21_movingRawEtaField p R A ω) (Ioc q r)
          (((Fj ω r - Fj ω q : projTensor B_H 2) : TensorDual B_H 2))) ∧
      ContinuousOn (Fj ω) (Icc 0 H) ∧
      BoundedVariationOn (Fj ω) (Icc 0 H) ∧
      (eVariationOn (Fj ω) (Icc 0 H)).toReal ≤ V ω := by
    filter_upwards [hYae, hYc, hFjGood, hVdNonneg] with ω hy hyc hj hvd
    refine ⟨hy, hyc, hj.1, hj.2.1, hj.2.2.1, ?_⟩
    dsimp [V]
    linarith [hj.2.2.2]
  have hM1dim : (p.d : ℝ) / 2 + 2 < (2 * p.d + 8 : ℕ) := by
    have hd0 : (0 : ℝ) ≤ p.d := Nat.cast_nonneg _
    norm_num [Nat.cast_add, Nat.cast_mul]
    linarith
  obtain ⟨Mb, hMb, -⟩ := fp81s21_moving_M1 p R hH hN A hstd hM1dim hphys
  have hMb' : ∀ᵐ ω ∂A.P,
      S102Drift (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) H
        (2 * p.d + 8) ((p.d : ℝ) + 2)
        (fun u f => r2QuadField p.s (r26t3_mu R u) A.P A.X u ω f)
        (Mb ω) := by
    filter_upwards [hMb] with ω hb
    simpa [fp81s21_moving_r2QuadField] using hb
  have hDId : ∀ L q r, 0 ≤ q → q ≤ r → r ≤ H →
      ∀ᵐ ω ∂A.P,
        IntegrableOn (fp81s21_moving_drift_cyl_sum p R A F a ha hH L Φ ω)
          (Ioc q r) ∧
        (WS L).drift.value q r ω =
          ∫ u in Ioc q r, fp81s21_moving_drift_cyl_sum p R A F a ha hH L Φ ω u := by
    intro L q r hq hqr hr
    exact fp81s21_moving_g6_drift_value p R a ha hH A F hstd hlin hM1dim
      future hfuture L Φ hΦ Yh Fd hYae hYc hFdInc Mb hMb' ((WS L).drift)
      q r hq hqr hr
  have hJId : ∀ L q r, 0 ≤ q → q ≤ r → r ≤ H →
      ∀ᵐ ω ∂A.P,
        IntegrableOn (fp81s21_moving_covariance_cyl_sum p R A F a ha hH L Φ ω)
          (Ioc q r) ∧
        (WS L).covariance.value q r ω =
          ∫ u in Ioc q r,
            fp81s21_moving_covariance_cyl_sum p R A F a ha hH L Φ ω u := by
    intro L q r hq hqr hr
    exact
      (fp81s21_moving_g6_covariance_value p R a ha hH hN A F hstd future
      hfuture L Φ hΦ Yh Fj V hJGood
      (fp81s21_moving_hh2_integrable_of_movingStd p R hH hstd hN A L)
      ((WS L).covariance) q r hq hqr hr)
  have hDOn : ∀ L q r, 0 ≤ q → q ≤ r → r ≤ H → ∀ᵐ ω ∂A.P,
      IntegrableOn (fp81s21_moving_drift_cyl_sum p R A F a ha hH L Φ ω)
        (Ioc q r) := by
    intro L q r hq hqr hr
    exact (hDId L q r hq hqr hr).mono fun _ h => h.1
  have hJOn : ∀ L q r, 0 ≤ q → q ≤ r → r ≤ H → ∀ᵐ ω ∂A.P,
      IntegrableOn (fp81s21_moving_covariance_cyl_sum p R A F a ha hH L Φ ω)
        (Ioc q r) := by
    intro L q r hq hqr hr
    exact (hJId L q r hq hqr hr).mono fun _ h => h.1
  have hDval : ∀ L q r, 0 ≤ q → q ≤ r → r ≤ H → ∀ᵐ ω ∂A.P,
      (WS L).drift.value q r ω =
        ∫ u in Ioc q r, fp81s21_moving_drift_cyl_sum p R A F a ha hH L Φ ω u := by
    intro L q r hq hqr hr
    exact (hDId L q r hq hqr hr).mono fun _ h => h.2
  have hJval : ∀ L q r, 0 ≤ q → q ≤ r → r ≤ H → ∀ᵐ ω ∂A.P,
      (WS L).covariance.value q r ω =
        ∫ u in Ioc q r, fp81s21_moving_covariance_cyl_sum p R A F a ha hH L Φ ω u := by
    intro L q r hq hqr hr
    exact (hJId L q r hq hqr hr).mono fun _ h => h.2
  intro L q r hq hqr hr
  exact fp81s21_moving_heat_ito_finite_projection_expectation_identity
    p R hδ hδh a ha hH hN A F hstd hlin hM1dim hphys future hfuture Φ hΦ
    Yh Fd Fj hYm hYae WS hDOn hJOn hDval hJval L q r hq hqr hr

end HRS.Fp81.S21
#print axioms HRS.Fp81.S21.fp81s21_moving_heat_ito_finite_projection_expectation_identity_of_data
end
