import HRS.MS.Fp81S21CovRS4
import HRS.MS.Fp81S21CovRS7
import HRS.MS.Fp81S21CovRS9

/-! Covariance RS values on supplied, shared witnesses. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Filter Topology Set
open scoped BigOperators
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R2Interp HRS.MS.CovMeas
open HRS.MC.Sec7.PI HRS.MC.Sec7.S7PIF6

def fp81s21_moving_covariance_rs_on_selected_contract
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (a : ℝ) (ha : 0 ≤ a) (hH : 0 < a + p.T)
    {N : ℕ} (hN : 2 ≤ N) (A : Particle R N) (F : FilteredParticle A)
    {c : MultiIndex p.d → ℝ}
    (hstd : Fp81MovingStd (r26t3_coeff R)
      (wholeSpaceIndex p.d : ℝ) (a + p.T) (2 * p.d + 8) c hH)
    (future : (H : ℝ) → ℝ → Measure
      (OscPath p.d (wholeSpaceIndex p.d : ℝ) H))
    (hfuture : fp81s21_moving_heat_full_clause p R future)
    (Yh : A.Ω → ℝ → OscPath p.d (wholeSpaceIndex p.d : ℝ) (a + p.T))
    (Fj : A.Ω → ℝ → projTensor
      (OscPath p.d (wholeSpaceIndex p.d : ℝ) (a + p.T)) 2)
    (V : A.Ω → ℝ)
    (hYm : ∀ t, Measurable (fun ω => Yh ω t))
    (hJm : ∀ t, Measurable (fun ω => Fj ω t))
    (hVi : Integrable V A.P)
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
      (eVariationOn (Fj ω) (Icc 0 (a + p.T))).toReal ≤ V ω) : Prop :=
  let H : ℝ := a + p.T
  let B_H := OscPath p.d (wholeSpaceIndex p.d : ℝ) H
  letI : CompleteSpace (projTensor B_H 2) :=
    HRS.Fp81.V01.fp81v01_projTensorComplete B_H 2
  ∀ (Φ : Window p → ℝ), MemCb 5 Φ →
    let W : B_H →L[ℝ] Window p :=
      HRS.MS.ProClosureS111.physicalWindowRestriction
        (d := p.d) (m := (wholeSpaceIndex p.d : ℝ))
        (T := p.T) (H := H) ha le_rfl
    let Ψ : B_H → ℝ := fun w => Φ (W w)
    let Aj : ℕ → A.Ω → ℝ → (projTensor B_H 2 →L[ℝ] ℝ) :=
      fun L ω τ => fp81s21_covariance_pairingCLM
        (iteratedFDeriv ℝ 2
          (r2HeatFn (future H) (fun w => Ψ (s102_Pj H hH L w)) τ)
          (Yh ω τ))
    ∃ M : A.Ω → ℝ, Integrable M A.P ∧
      ∀ L : ℕ,
        ∃ WS : fp81s21_RSBVWindow A.P H (Aj L) Fj,
          ∀ q r, 0 ≤ q → q ≤ r → r ≤ H →
            Integrable (fp81s21_rs_bv_variation_majorant (Aj L) Fj q r) A.P ∧
            (∀ᵐ ω ∂A.P,
              IntegrableOn
                (fp81s21_moving_covariance_cyl_sum p R A F a ha hH L Φ ω)
                (Ioc q r) ∧
              WS.value q r ω =
                ∫ u in Ioc q r,
                  fp81s21_moving_covariance_cyl_sum p R A F a ha hH L Φ ω u) ∧
            (∀ᵐ ω ∂A.P,
              fp81s21_rs_bv_variation_majorant (Aj L) Fj q r ω ≤ M ω)

theorem fp81s21_moving_covariance_rs_on_selected
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (a : ℝ) (ha : 0 ≤ a) (hH : 0 < a + p.T)
    {N : ℕ} (hN : 2 ≤ N) (A : Particle R N) (F : FilteredParticle A)
    {c : MultiIndex p.d → ℝ}
    (hstd : Fp81MovingStd (r26t3_coeff R)
      (wholeSpaceIndex p.d : ℝ) (a + p.T) (2 * p.d + 8) c hH)
    (future : (H : ℝ) → ℝ → Measure
      (OscPath p.d (wholeSpaceIndex p.d : ℝ) H))
    (hfuture : fp81s21_moving_heat_full_clause p R future)
    (Yh : A.Ω → ℝ → OscPath p.d (wholeSpaceIndex p.d : ℝ) (a + p.T))
    (Fj : A.Ω → ℝ → projTensor
      (OscPath p.d (wholeSpaceIndex p.d : ℝ) (a + p.T)) 2)
    (V : A.Ω → ℝ)
    (hYm : ∀ t, Measurable (fun ω => Yh ω t))
    (hJm : ∀ t, Measurable (fun ω => Fj ω t))
    (hVi : Integrable V A.P)
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
      (eVariationOn (Fj ω) (Icc 0 (a + p.T))).toReal ≤ V ω) : fp81s21_moving_covariance_rs_on_selected_contract
      (p := p) (δ := δ) (R := R) (a := a) (ha := ha) (hH := hH)
      (N := N) (hN := hN) (A := A) (F := F) (c := c) (hstd := hstd)
      (future := future) (hfuture := hfuture) (Yh := Yh) (Fj := Fj)
      (V := V) (hYm := hYm) (hJm := hJm) (hVi := hVi) (hgood := hgood) := by
  classical
  delta fp81s21_moving_covariance_rs_on_selected_contract
  let H : ℝ := a + p.T
  let B := OscPath p.d (wholeSpaceIndex p.d : ℝ) H
  letI : CompleteSpace (projTensor B 2) :=
    HRS.Fp81.V01.fp81v01_projTensorComplete B 2
  let W : B →L[ℝ] Window p :=
    HRS.MS.ProClosureS111.physicalWindowRestriction
      (d := p.d) (m := (wholeSpaceIndex p.d : ℝ))
      (T := p.T) (H := H) ha le_rfl
  let Pj : ℕ → B →L[ℝ] B := fun L => s102_Pj H hH L
  have hLP : S102LipProj (future H) Pj := hfuture.2.2.1 H hH
  have hproj := hfuture.2.2.2 H hH
  have hYc : ∀ᵐ ω ∂A.P, ContinuousOn (Yh ω) (Icc (0 : ℝ) H) := by
    filter_upwards [hgood] with ω hg
    exact hg.2.1
  have hJc : ∀ᵐ ω ∂A.P, ContinuousOn (Fj ω) (Icc (0 : ℝ) H) := by
    filter_upwards [hgood] with ω hg
    exact hg.2.2.2.1
  have hV : ∀ᵐ ω ∂A.P,
      BoundedVariationOn (Fj ω) (Icc (0 : ℝ) H) ∧
        (eVariationOn (Fj ω) (Icc 0 H)).toReal ≤ V ω := by
    filter_upwards [hgood] with ω hg
    exact ⟨hg.2.2.2.2.1, hg.2.2.2.2.2⟩
  have hzi : ∀ L : ℕ, ∀ᵐ ω ∂A.P, ∀ i j : Fin (s102_q p.d L),
      IntegrableOn
        (s102_hh2 (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ)
          (s102_tauk hH L) (s102_alk L)
          (fun v => s102_etaf (r26t3_mu R v) A.X ω v) i j)
        (Icc (0 : ℝ) H) :=
    fp81s21_moving_hh2_integrable_of_movingStd p R hH hstd hN A
  dsimp only
  intro Φ hΦ
  let Ψ : B → ℝ := fun w => Φ (W w)
  let Aj' : ℕ → A.Ω → ℝ → (projTensor B 2 →L[ℝ] ℝ) :=
    fun L ω τ => fp81s21_covariance_pairingCLM
      (iteratedFDeriv ℝ 2
        (r2HeatFn (future H) (fun w => Ψ (s102_Pj H hH L w)) τ)
        (Yh ω τ))
  have hfamily := fp81s21_projected_heat_covariance_rsbv_window
    (μ := A.P) (γ := future H) (hγ := hfuture.1 H) Pj hproj.1 hproj.2.1
    hLP Ψ ((HRS.MC.Sec7.S7PIS2.s7_PIS_memCb_comp_proof W hΦ).1)
    Yh Fj V hYm hJm hYc hJc hVi hV
  change ∃ M : A.Ω → ℝ, Integrable M A.P ∧ ∀ L : ℕ,
      ∃ WS : fp81s21_RSBVWindow A.P H (Aj' L) Fj,
        ∀ q r, 0 ≤ q → q ≤ r → r ≤ H →
          Integrable (fp81s21_rs_bv_variation_majorant (Aj' L) Fj q r) A.P ∧
          (∀ᵐ ω ∂A.P,
            IntegrableOn
              (fp81s21_moving_covariance_cyl_sum p R A F a ha hH L Φ ω)
              (Ioc q r) ∧
            WS.value q r ω =
              ∫ u in Ioc q r,
                fp81s21_moving_covariance_cyl_sum p R A F a ha hH L Φ ω u) ∧
          ∀ᵐ ω ∂A.P,
            fp81s21_rs_bv_variation_majorant (Aj' L) Fj q r ω ≤ M ω
  obtain ⟨M, hMi, hlevels⟩ := hfamily
  refine ⟨M, hMi, ?_⟩
  intro L
  obtain ⟨hWS, hmajor⟩ := hlevels L
  let WS : fp81s21_RSBVWindow A.P H (Aj' L) Fj := Classical.choice hWS
  refine ⟨WS, ?_⟩
  intro q r hq hqr hr
  obtain ⟨hMajInt, hMajBound⟩ := hmajor q r hq hqr hr
  refine ⟨hMajInt, ?_, hMajBound⟩
  let C : WholeCoeff p.d := r26t3_coeff R
  let m : ℝ := (wholeSpaceIndex p.d : ℝ)
  let τ : Fin (s102_q p.d L) → Icc (0 : ℝ) H := s102_tauk hH L
  let α : Fin (s102_q p.d L) → MultiIndex p.d := s102_alk L
  let G : EuclideanSpace ℝ (Fin (s102_q p.d L)) → ℝ :=
    fun x => Φ (W (s102_Lam H L x))
  have hG5 : MemCb 5 G := by
    have hΨ : MemCb 5 (fun w => Φ (W w)) :=
      (HRS.MC.Sec7.S7PIS2.s7_PIS_memCb_comp_proof W hΦ).1
    exact (HRS.MC.Sec7.S7PIS2.s7_PIS_memCb_comp_proof
      (s102_Lam H L) hΨ).1
  have hG : MemCb 2 G := ⟨hG5.1.of_le (by norm_num),
    fun j hj => hG5.2 j (by omega)⟩
  have hcov : ∀ i j, ContinuousOn
      (fun u => s102_obsCov C m τ α u i j) (Icc 0 H) :=
    fun i j => s102_obsCov_cont hH L (fp81s21_moving_gramInt hstd L) i j
  have hfun : (fun w => Ψ (s102_Pj H hH L w)) =
      fun w => G (s102_obs τ α w) := by
    funext w
    dsimp only [G, Ψ, W, τ, α, H, B]
    rw [s102_Pj_eq_Lam hH L w]
  let zA (ω : A.Ω) : ℝ → (Euc p.d → ℝ) → ℝ := fun v =>
    s102_etaf (r26t3_mu R v) A.X ω v
  let zF (ω : A.Ω) : ℝ → (Euc p.d → ℝ) → ℝ := fun v =>
    s102_etaf (r26t3_mu R v) F.X ω v
  filter_upwards [hgood,
    hzi L,
    F.indist,
    WS.value_isRS q r hq hqr hr] with ω hg hziω hind hRS
  rcases hg with ⟨hYeq, hYcω, hJ, hJcω, hJBV, hJvar⟩
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
    (C := C) (m := m) (H := H) hH
    (future H) (hfuture.2.1 H hH) τ α hcov G hG (Yh ω) hYcω
    (zA ω) (Fj ω) (by
      intro u v hu huv hv
      exact hJ u v hu huv hv)
    (fun i j => hziω i j) q r hq hqr hr (WS.value q r ω) hRS'
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
    rw [hYeq u huH]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hheq i j]
  have hout := hval.1.congr_fun heq measurableSet_Ioc
  exact ⟨hout,
    hval.2.trans (setIntegral_congr_fun measurableSet_Ioc heq)⟩

#print axioms HRS.Fp81.S21.fp81s21_moving_covariance_rs_on_selected
end HRS.Fp81.S21
end
