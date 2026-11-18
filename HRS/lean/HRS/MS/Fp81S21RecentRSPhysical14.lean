import HRS.MS.Fp81S21RecentRSPhysical13

/-! Retained wrapper: the expanded statement and its proof are elaborated
separately to keep every declaration within 400000 heartbeats. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory Filter Topology Set
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.R2Interp
open HRS.MS.ProClosureS111 HRS.MS.CovMeas

local instance fp81s21_recentRS14_complete (p : Parameters) :
    CompleteSpace (projTensor (Window p) 2) :=
  HRS.Fp81.V01.fp81v01_projTensorComplete (Window p) 2
local instance fp81s21_recentRS14_CH_meas (H : ℝ) : MeasurableSpace (CH H) := borel _
local instance fp81s21_recentRS14_CH_borel (H : ℝ) : BorelSpace (CH H) := ⟨rfl⟩
local instance fp81s21_recentRS14_UH_meas (H : ℝ) : MeasurableSpace (UH H) := borel _
local instance fp81s21_recentRS14_UH_borel (H : ℝ) : BorelSpace (UH H) := ⟨rfl⟩
local instance fp81s21_recentRS14_YH_meas (p : Parameters) (H : ℝ) :
    MeasurableSpace (YH p H) := borel _
local instance fp81s21_recentRS14_YH_borel (p : Parameters) (H : ℝ) :
    BorelSpace (YH p H) := ⟨rfl⟩
local instance fp81s21_recentRS14_YH_countable (p : Parameters) (H : ℝ) :
    SecondCountableTopology (YH p H) := by
  change SecondCountableTopology C(I H, C(I p.T, OscDual p.d (wholeSpaceIndex p.d)))
  infer_instance

/-- Assembly on the exactly expanded proposition in RS13. -/
private theorem fp81s21_recentRS14_assembled (p : Parameters) :
    fp81s21_recentRS13_spec p := by
  obtain ⟨Es, E, εAvg, hεAvg, hεAvgT, δ33, hδ33, hδ33half, h33all⟩ :=
    fp81s21_recent_joint_physical p
  obtain ⟨δsel, hδsel, _, hsel⟩ := fp81s21_gaussian_physical_package_selected p Es E
  obtain ⟨δsrc, hδsrc, _, hsrc⟩ := fp81s21_gaussian_source_retained p
  obtain ⟨δreg, hδreg, _, hreg⟩ := fp81s21_recentRS13_regularity p
  let δ0 := min δ33 (min δsel (min δsrc δreg))
  refine ⟨Es, E, εAvg, hεAvg, hεAvgT, δ0,
    lt_min hδ33 (lt_min hδsel (lt_min hδsrc hδreg)),
    (min_le_left _ _).trans hδ33half, ?_⟩
  intro δ hδ hδle R
  have hle : δ ≤ δ33 ∧ δ ≤ δsel ∧ δ ≤ δsrc ∧ δ ≤ δreg := by
    simpa only [δ0, le_min_iff] using hδle
  rcases hle with ⟨h33le, hselle, hsrcle, hregle⟩
  obtain ⟨MUG, hMUG, canon, εN, εG, εB, hn, hnT, hg, hgT, hb, hbT,
    S31, c, hc, K, hK, Kpred, hKpred, O, h33⟩ := h33all δ hδ h33le R
  obtain ⟨src⟩ := hsrc δ hδ hsrcle R
  let Q0 := fp81s21_gaussian35_selection_of_selected Es E src εAvg εB
    hεAvg hεAvgT hb hbT MUG hMUG canon S31.gaussian.quadratic
  obtain ⟨Qexist, hparent⟩ := hsel δ hδ hselle R Q0 rfl rfl
  have hcompatible : ∃ Q : fp81s21_Physical35 p R,
      Q.Es = Es ∧ Q.E = E ∧ Q.MUG = MUG ∧ Q.εG = εAvg ∧ Q.εB = εB ∧
      HEq Q.canon canon ∧ HEq Q.S S31.gaussian.quadratic := by
    exact ⟨Qexist, fp81s21_recentRS13_compatible p R Es E src εAvg εB
      hεAvg hεAvgT hb hbT MUG hMUG canon S31.gaussian.quadratic Qexist hparent⟩
  obtain ⟨coef, coefStd, hDs, hDl, hmom, hstd⟩ := hreg δ hδ hregle R
  refine ⟨MUG, hMUG, canon, εN, εG, εB, hn, hnT, hg, hgT, hb, hbT,
    S31, c, hc, K, hK, Kpred, hKpred, O, ?_⟩
  constructor
  · exact h33
  refine ⟨hcompatible, ?_⟩
  intro Q hEs hE hM hAvg hB hcanon hquad future hf L hL
  obtain ⟨eL, heL, heLT, hall⟩ :=
    fp81s21_recent_rs_physical_supplied_of_heat p R Es E εAvg hεAvg hεAvgT
      MUG hMUG canon εN εG εB hn hnT hg hgT hb hbT S31 c hc K hK Kpred hKpred O h33
      coef hDs hDl hmom coefStd hstd Q hEs hE hM hAvg hB hcanon hquad future hf L hL
  refine ⟨eL, heL, heLT, hall, ?_⟩
  intro N hN A F a ha D20 Cmix cdec K20 hcov Φ hΦ WN W
  exact hall N hN A F Q.src.G0 a ha D20 Cmix cdec K20 hcov Φ hΦ
    (Q.UG a ha) (Q.UB a ha) (Q.hUG a ha) (Q.hUB a ha) W.Y W.physical WN W.WG

/-- Retain packet 33, extend its selected families, and compare every compatible
physical package on arbitrary supplied Gaussian realizations. The source GRS
specialization is the second conjunct of the same uniform error bound. -/
theorem fp81s21_recent_rs_physical (p : Parameters) :
    ∃ Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4),
    ∃ E : r26t6_WeightedChart p.d (r p) (Pw p),
    ∃ εAvg : ℕ → ℝ, (∀ k, 0 ≤ εAvg k) ∧ Tendsto εAvg atTop (𝓝 0) ∧
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
    ∃ MUG : ℝ, 0 ≤ MUG ∧
    ∃ canon : fp81s21_gaussian_V2_G_canonicalFamily p Es E R MUG εAvg,
    ∃ εN εG εB : ℕ → ℝ,
      (∀ k, 0 ≤ εN k) ∧ Tendsto εN atTop (𝓝 0) ∧
      (∀ k, 0 ≤ εG k) ∧ Tendsto εG atTop (𝓝 0) ∧
      (∀ k, 0 ≤ εB k) ∧ Tendsto εB atTop (𝓝 0) ∧
    ∃ S31 : fp81s21_Physical31 p R Es E εN εG εB,
    ∃ c : ℝ, ∃ hc : 0 < c, ∃ K : ℝ, ∃ hK : 0 ≤ K,
    ∃ Kpred : ℝ, 0 ≤ Kpred ∧
    ∃ O : (a : ℝ) → 0 ≤ a → r26t6_IntervalOperators E (r26t3_coeff R) p.T a c K,
    (∀ (L : ℝ) (hL : 0 < L),
      let H := L + p.T; let T := fp81s21_smoothPathToL2 H (add_pos hL p.hT)
      let dL := K * Real.sqrt H; let jL := K * |2 * (r26t3_coeff R).ν| * Real.sqrt H
      let CL := max Kpred (max dL (jL * ‖T‖)); let MBG := S31.gaussian.quadratic.Kstar ^ 4 * S31.gaussian.quadratic.B / 2
      ∃ e e33 : ℕ → ℝ, ∃ M33 : ℝ, 0 ≤ M33 ∧ (∀ N, 0 ≤ e N) ∧ Tendsto e atTop (𝓝 0) ∧ e33 = (fun N => 2 * CL * e N) ∧ (∀ N, 0 ≤ e33 N) ∧ Tendsto e33 atTop (𝓝 0) ∧
      ∃ P : (a : ℝ) → 0 ≤ a → CH H →L[ℝ] YH p H, (∀ a ha, ‖P a ha‖ ≤ Kpred ∧ PSpec p R E L a (P a ha)) ∧
      ∀ (N : ℕ) (hN : 2 ≤ N) (A : Particle R N) (G : GaussianRealization R) (a : ℝ) (ha : 0 ≤ a),
      let b := max (a - L) 0; let D := fp81s21_VDtransport p a ha L hL c K (O a ha) hK hc.le; let J := fp81s21_VJtransport p a ha L hL c K (O a ha) hK hc.le
      letI : MeasurableSpace (fp81s21_VD p a ha L hL c K (O a ha) hK hc.le) := borel _
      letI : MeasurableSpace (fp81s21_VJ p a ha L hL c K (O a ha) hK hc.le) := borel _
      ∃ XN : A.Ω → CH H, ∃ XG : G.Ω → CH H, ∃ UBN : A.Ω → UH H, ∃ UBG : G.Ω → UH H, ∃ YN : A.Ω → YH p H, ∃ YG : G.Ω → YH p H,
      CD E A.P (fp81s21_particleEmpField R N A) b H XN ∧ CD E G.P (fun u ω f => OscDual.eval (G.Z u ω) f) b H XG ∧
      fp81s21_TimeL2Rep A.P (fun u ω => fp81s21_particle_embedField p Es E (S31.qsBN N hN A u ω)) S31.MN b H UBN ∧ fp81s21_TimeL2Rep G.P (S31.gaussian.quadratic.qe G) MBG b H UBG ∧
      (∫ ω, XG ω ∂G.P) = 0 ∧ GA p R E G (S31.gaussian.quadratic.T G) b H XG ∧ YN = (fun ω => P a ha (cen A.P XN ω)) ∧ YG = (fun ω => P a ha (cen G.P XG ω)) ∧
      Measurable YN ∧ MemLp YN 2 A.P ∧ Measurable YG ∧ MemLp YG 2 G.P ∧ NId p R A L a YN ∧ GId p R E G L a XG YG ∧
      HRS.wassersteinE 2 (law A.P (fun ω => (XN ω, UBN ω))) (law G.P (fun ω => (XG ω, UBG ω))) ≤ ENNReal.ofReal (e N) ∧
      HRS.wassersteinE 2 (law A.P (fun ω => (cen A.P XN ω, cen A.P UBN ω))) (law G.P (fun ω => (cen G.P XG ω, cen G.P UBG ω))) ≤ ENNReal.ofReal (2 * e N) ∧
      HRS.wassersteinE 2 (law A.P (fun ω => (YN ω, cen A.P UBN ω))) (law G.P (fun ω => (YG ω, cen G.P UBG ω))) ≤ ENNReal.ofReal (max 1 Kpred * (2 * e N)) ∧
      fp81s21_BVLaw p R A.P E (fp81s21_particleEmpField R N A) (fp81s21_particleQuadField R N A) S31.MN S31.MN a L c K ha hL (O a ha) hK hc.le (fun ω => D (UBN ω)) (fun ω => J (T (XN ω))) ∧
      fp81s21_BVLaw p R G.P E (fun u ω f => fp81s21_chartAction E (fp81s21_gaussian_embedFamily p Es E (canon.q G) u ω) f) (fun u ω f => fp81s21_chartAction E (S31.gaussian.quadratic.qe G u ω) f) MUG MBG a L c K ha hL (O a ha) hK hc.le (fun ω => D (UBG ω)) (fun ω => J (T (XG ω))) ∧
      (∫ ω, (‖D (UBN ω)‖ ^ 2 + ‖J (T (XN ω))‖ ^ 2) ∂A.P) ≤ M33 ∧ (∫ ω, (‖D (UBG ω)‖ ^ 2 + ‖J (T (XG ω))‖ ^ 2) ∂G.P) ≤ M33 ∧
      HRS.wassersteinE 2 (law A.P (fun ω => (P a ha (cen A.P XN ω), (D (UBN ω), J (T (XN ω)))))) (law G.P (fun ω => (P a ha (cen G.P XG ω), (D (UBG ω), J (T (XG ω)))))) ≤ ENNReal.ofReal (e33 N)) ∧
    (∃ Q : fp81s21_Physical35 p R, Q.Es = Es ∧ Q.E = E ∧ Q.MUG = MUG ∧ Q.εG = εAvg ∧ Q.εB = εB ∧
      HEq Q.canon canon ∧ HEq Q.S S31.gaussian.quadratic) ∧
    ∀ (Q : fp81s21_Physical35 p R),
      Q.Es = Es → Q.E = E → Q.MUG = MUG → Q.εG = εAvg → Q.εB = εB →
      HEq Q.canon canon → HEq Q.S S31.gaussian.quadratic →
    ∀ (future : (H : ℝ) → ℝ → Measure (OscPath p.d (wholeSpaceIndex p.d : ℝ) H)),
      fp81s21_moving_heat_full_clause p R future →
    ∀ (L : ℝ) (hL : 0 < L), ∃ eL : ℕ → ℝ,
      (∀ N, 0 ≤ eL N) ∧ Tendsto eL atTop (𝓝 0) ∧
    (∀ (N : ℕ) (hN : 2 ≤ N) (A : Particle R N) (F : FilteredParticle A) (G : GaussianRealization R) (a : ℝ) (ha : 0 ≤ a)
      (D20 : fp81s21_finproj_shared_data p R a A F) (Cmix cdec : ℝ) (K20 : ℝ → ℝ)
      (hcov : fp81s21_shared_physical_window_covariance_identification p R a ha A Cmix cdec K20 D20.Fj)
      (Φ : Window p → ℝ) (hΦ : Φ ∈ CbUnitBall (Window p) 5)
      (UG UB : G.Ω → Lp r26t6_Coeff 2 (volume.restrict (Icc (0 : ℝ) (a + p.T))))
      (hUG : fp81s21_TimeL2Rep G.P (fp81s21_gaussian_embedFamily p Q.Es Q.E (Q.canon.q G)) Q.MUG 0 (a + p.T) UG)
      (hUB : fp81s21_TimeL2Rep G.P (Q.S.qe G) (Q.S.Kstar ^ 4 * Q.S.B / 2) 0 (a + p.T) UB)
      (Y : G.Ω → C(I (a + p.T), Window p))
      (hY : ∀ r : I (a + p.T), ∀ τ : I p.T, ∀ᵐ ω ∂G.P, OscPath.at' (Y ω r) τ = r2Vprop (r26t3_coeff R) (m p) (a + τ) (min (r : ℝ) (a + τ)) (fp81s21_chartAction Q.E (fp81s21_gaussian_embedFamily p Q.Es Q.E (Q.canon.q G) (min (r : ℝ) (a + τ)) ω)))
      (WN : fp81s21_WindowRS A.P (a + p.T)
        (fun ω t => fderiv ℝ (initialHeat future a ha Φ t) (physicalWindowRestriction ha le_rfl (D20.Yh ω t)))
        (fun ω t => fp81s21_weightedDrift_windowCum (m := m p) (T := p.T) (H := a + p.T) ha le_rfl (r26t3_coeff R) (fun u f => r2QuadField p.s (r26t3_mu R u) A.P A.X u ω f) t)
        (fun ω t => fp81s21_covariance_pairingCLM (iteratedFDeriv ℝ 2 (initialHeat future a ha Φ t) (physicalWindowRestriction ha le_rfl (D20.Yh ω t))))
        (fun ω t => fp81s21_windowCovarianceMap p a ha (D20.Fj ω t)))
      (WG : fp81s21_remote_G_RS_at Q future G a ha UG UB Φ (fp81s21_remote_G_extend G a ha Y)),
      |fp81s21_WindowRS_corr WN (max (a - L) 0) (a + p.T) - fp81s21_WindowRS_corr WG (max (a - L) 0) (a + p.T)| ≤ eL N) ∧
    (∀ (N : ℕ) (hN : 2 ≤ N) (A : Particle R N) (F : FilteredParticle A) (a : ℝ) (ha : 0 ≤ a)
      (D20 : fp81s21_finproj_shared_data p R a A F) (Cmix cdec : ℝ) (K20 : ℝ → ℝ)
      (hcov : fp81s21_shared_physical_window_covariance_identification p R a ha A Cmix cdec K20 D20.Fj)
      (Φ : Window p → ℝ) (hΦ : Φ ∈ CbUnitBall (Window p) 5)
      (WN : fp81s21_WindowRS A.P (a + p.T)
        (fun ω t => fderiv ℝ (initialHeat future a ha Φ t) (physicalWindowRestriction ha le_rfl (D20.Yh ω t)))
        (fun ω t => fp81s21_weightedDrift_windowCum (m := m p) (T := p.T) (H := a + p.T) ha le_rfl (r26t3_coeff R) (fun u f => r2QuadField p.s (r26t3_mu R u) A.P A.X u ω f) t)
        (fun ω t => fp81s21_covariance_pairingCLM (iteratedFDeriv ℝ 2 (initialHeat future a ha Φ t) (physicalWindowRestriction ha le_rfl (D20.Yh ω t))))
        (fun ω t => fp81s21_windowCovarianceMap p a ha (D20.Fj ω t)))
      (W : fp81s21_GRS Q future a ha Φ),
      |fp81s21_WindowRS_corr WN (max (a - L) 0) (a + p.T) - fp81s21_WindowRS_corr W.WG (max (a - L) 0) (a + p.T)| ≤ eL N) := by
  exact fp81s21_recentRS14_assembled p

end HRS.Fp81.S21
end
#print axioms HRS.Fp81.S21.fp81s21_recentRS14_assembled
#print axioms HRS.Fp81.S21.fp81s21_recent_rs_physical
