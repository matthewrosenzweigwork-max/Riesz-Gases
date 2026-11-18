import HRS.MS.Fp81S21RecentRSPhysical7
import HRS.MS.Fp81S21RecentRSPhysical10
import HRS.MS.Fp81S21RecentJointPhysical2

/-! Supplied-data scalar comparison, retaining the literal packet-33 telescope,
compatible physical Gaussian fields, and both supplied window RS records. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory Filter Topology Set
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.R2Interp
open HRS.MS.ProClosureS111 HRS.MS.CovMeas

local instance fp81s21_recentRS11_complete (p : Parameters) :
    CompleteSpace (projTensor (Window p) 2) :=
  HRS.Fp81.V01.fp81v01_projTensorComplete (Window p) 2
local instance fp81s21_recentRS11_CH_meas (H : ℝ) : MeasurableSpace (CH H) := borel _
local instance fp81s21_recentRS11_CH_borel (H : ℝ) : BorelSpace (CH H) := ⟨rfl⟩
local instance fp81s21_recentRS11_UH_meas (H : ℝ) : MeasurableSpace (UH H) := borel _
local instance fp81s21_recentRS11_UH_borel (H : ℝ) : BorelSpace (UH H) := ⟨rfl⟩
local instance fp81s21_recentRS11_YH_meas (p : Parameters) (H : ℝ) :
    MeasurableSpace (YH p H) := borel _
local instance fp81s21_recentRS11_YH_borel (p : Parameters) (H : ℝ) :
    BorelSpace (YH p H) := ⟨rfl⟩
local instance fp81s21_recentRS11_YH_countable (p : Parameters) (H : ℝ) :
    SecondCountableTopology (YH p H) := by
  change SecondCountableTopology C(I H, C(I p.T, OscDual p.d (wholeSpaceIndex p.d)))
  infer_instance

/-- The profile is selected before N, A, G, the window start and the unit test.
Compatibility retains HEq for the two dependent families; εAvg, rather than
packet 33's εG, identifies the canonical family's approximation profile. -/
theorem fp81s21_recent_rs_physical_supplied
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4)) (E : r26t6_WeightedChart p.d (r p) (Pw p))
    (εAvg : ℕ → ℝ) (hεAvg : ∀ k, 0 ≤ εAvg k) (hεAvgT : Tendsto εAvg atTop (𝓝 0))
    (MUG : ℝ) (hMUG : 0 ≤ MUG) (canon : fp81s21_gaussian_V2_G_canonicalFamily p Es E R MUG εAvg)
    (εN εG εB : ℕ → ℝ) (hn : ∀ k, 0 ≤ εN k) (hnT : Tendsto εN atTop (𝓝 0)) (hg : ∀ k, 0 ≤ εG k) (hgT : Tendsto εG atTop (𝓝 0)) (hb : ∀ k, 0 ≤ εB k) (hbT : Tendsto εB atTop (𝓝 0))
    (S31 : fp81s21_Physical31 p R Es E εN εG εB) (c : ℝ) (hc : 0 < c) (K : ℝ) (hK : 0 ≤ K) (Kpred : ℝ) (hKpred : 0 ≤ Kpred)
    (O : ∀ a, 0 ≤ a → r26t6_IntervalOperators E (r26t3_coeff R) p.T a c K)
    (h33 : ∀ (L : ℝ) (hL : 0 < L),
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
      HRS.wassersteinE 2 (law A.P (fun ω => (P a ha (cen A.P XN ω), (D (UBN ω), J (T (XN ω)))))) (law G.P (fun ω => (P a ha (cen G.P XG ω), (D (UBG ω), J (T (XG ω)))))) ≤ ENNReal.ofReal (e33 N))
    (coef : ℝ → ℝ → MultiIndex p.d → ℝ)
    (hDs : ∀ (L : ℝ) (hL : 0 < L) (a : ℝ) (ha : 0 ≤ a), S101Data (r26t3_coeff R) (m p) (a + p.T) (r p) (coef L a))
    (hDl : ∀ (L : ℝ) (hL : 0 < L) (a : ℝ) (ha : 0 ≤ a), S101Data (r26t3_coeff R) (m p) (max (a - L) 0 + (L + p.T)) (r p) (coef L a))
    (hmom : ∀ (N : ℕ) (hN : 2 ≤ N) (A : Particle R N) (L : ℝ) (hL : 0 < L) (a : ℝ) (ha : 0 ≤ a), ∀ u ∈ I (max (a - L) 0 + (L + p.T)), Integrable (fun x : Euc p.d => jbracket x ^ Pw p) (HRS.Whole.meanEmpirical (A.P.map (A.X u.toNNReal))))
    (coefStd : ℝ → MultiIndex p.d → ℝ) (hstd : ∀ (a : ℝ) (ha : 0 ≤ a), Fp81MovingStd (r26t3_coeff R) (m p) (a + p.T) (2 * p.d + 8) (coefStd a) (add_pos_of_nonneg_of_pos ha p.hT))
    (Q : fp81s21_Physical35 p R) (hEs : Q.Es = Es) (hE : Q.E = E) (hM : Q.MUG = MUG) (hAvg : Q.εG = εAvg) (hB : Q.εB = εB) (hcanon : HEq Q.canon canon) (hquad : HEq Q.S S31.gaussian.quadratic)
    (future : (H : ℝ) → ℝ → Measure (OscPath p.d (wholeSpaceIndex p.d : ℝ) H)) (hf : fp81s21_moving_heat_full_clause p R future)
    (KD KJ : (L : ℝ) → 0 < L → ℝ) (hKD : ∀ L hL, 0 < KD L hL) (hKJ : ∀ L hL, 0 < KJ L hL)
    (hker : ∀ (L : ℝ) (hL : 0 < L) (a : ℝ) (ha : 0 ≤ a) (Φ : Window p → ℝ), Φ ∈ CbUnitBall (Window p) 5 →
      ∃ FD : fp81s21_RecentRSKernel (YH p (L + p.T)) (fp81s21_VD p a ha L hL c K (O a ha) hK hc.le) (KD L hL),
      ∃ FJ : fp81s21_RecentRSKernel (YH p (L + p.T)) (fp81s21_VJ p a ha L hL c K (O a ha) hK hc.le) (KJ L hL), fp81s21_recentHeatKernelRS p future L hL a ha Φ FD FJ) :
    ∀ (L : ℝ) (hL : 0 < L), ∃ eL : ℕ → ℝ, (∀ N, 0 ≤ eL N) ∧ Tendsto eL atTop (𝓝 0) ∧
    ∀ (N : ℕ) (hN : 2 ≤ N) (A : Particle R N) (F : FilteredParticle A) (G : GaussianRealization R) (a : ℝ) (ha : 0 ≤ a)
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
      |fp81s21_WindowRS_corr WN (max (a - L) 0) (a + p.T) - fp81s21_WindowRS_corr WG (max (a - L) 0) (a + p.T)| ≤ eL N := by
  subst Es
  subst E
  subst MUG
  subst εAvg
  subst εB
  have hcanon' : Q.canon = canon := eq_of_heq hcanon
  subst canon
  have hquad' : Q.S = S31.gaussian.quadratic := eq_of_heq hquad
  intro L hL
  obtain ⟨e, e33, M33, hM33, he, heT, he33def, he33, he33T, P, hP, hall⟩ := h33 L hL
  refine ⟨(fun N => (KD L hL + KJ L hL / 2) * (1 + Real.sqrt M33) *
    (e33 N + 1 / ((N : ℝ) + 1))), ?_, ?_, ?_⟩
  · exact (fp81s21_recentRS_profile_properties (KD L hL) (KJ L hL) M33 e33
      (hKD L hL).le (hKJ L hL).le he33 he33T).1
  · exact (fp81s21_recentRS_profile_properties (KD L hL) (KJ L hL) M33 e33
      (hKD L hL).le (hKJ L hL).le he33 he33T).2
  intro N hN A F G a ha D20 Cmix cdec K20 hcov Φ hΦ UG UB hUG hUB Y hY WN WG
  obtain ⟨XN, XG, UBN, UBG, YN, YG, hNcd, hGcd, hBN, hBG, hmean, hGA,
    hYN, hYG, hYNm, hYN2, hYGm, hYG2, hNid, hGid, hraw, hcenter, hpair,
    hBVN, hBVG, hMN, hMG, hW⟩ := hall N hN A G a ha
  let T := fp81s21_smoothPathToL2 (L + p.T) (add_pos hL p.hT)
  let D := fp81s21_VDtransport p a ha L hL c K (O a ha) hK hc.le
  let J := fp81s21_VJtransport p a ha L hL c K (O a ha) hK hc.le
  let dN := fun ω => D (UBN ω)
  let jN := fun ω => J (T (XN ω))
  let dG := fun ω => D (UBG ω)
  let jG := fun ω => J (T (XG ω))
  obtain ⟨FD, FJ, hRS⟩ := hker L hL a ha Φ hΦ
  have hvaluesN := fp81s21_recentRS_particle_values p R hN A F a ha D20 L hL
    (coef L a) (hDs L hL a ha) (hDl L hL a ha) (hmom N hN A L hL a ha)
    Q.E S31.MN S31.MN c K hK hc.le (O a ha) dN jN hBVN YN hNid
    future Φ WN FD FJ hRS
  rw [← hquad'] at hBVG
  have hvaluesG := fp81s21_recentRS_gaussian_values_supplied p R a ha
    (coefStd a) (hstd a ha) Q G UG UB hUG hUB Y hY L hL XG hGcd hmean
    (P a ha) (hP a ha).2 YG hYG c K hK hc.le (O a ha) dG jG hBVG
    future Φ WG FD FJ hRS
  letI : MeasurableSpace (fp81s21_VD p a ha L hL c K (O a ha) hK hc.le) := borel _
  letI : BorelSpace (fp81s21_VD p a ha L hL c K (O a ha) hK hc.le) := ⟨rfl⟩
  letI : MeasurableSpace (fp81s21_VJ p a ha L hL c K (O a ha) hK hc.le) := borel _
  letI : BorelSpace (fp81s21_VJ p a ha L hL c K (O a ha) hK hc.le) := ⟨rfl⟩
  letI := fp81s21_VD_separable p a ha L hL c K (O a ha) hK hc.le
  letI := fp81s21_VJ_separable p a ha L hL c K (O a ha) hK hc.le
  have hmN : Measurable (fun ω => (YN ω, (dN ω, jN ω))) :=
    hYNm.prodMk (hBVN.1.prodMk hBVN.2.2.1)
  have hmG : Measurable (fun ω => (YG ω, (dG ω, jG ω))) :=
    hYGm.prodMk (hBVG.1.prodMk hBVG.2.2.1)
  have hW' : HRS.wassersteinE 2
      (A.P.map (fun ω => (YN ω, (dN ω, jN ω))))
      (G.P.map (fun ω => (YG ω, (dG ω, jG ω)))) ≤ ENNReal.ofReal (e33 N) := by
    simpa only [hYN, hYG] using hW
  exact fp81s21_recentRS_window_signed_of_values A.P G.P WN WG
    (max (a - L) 0) (a + p.T) YN dN jN YG dG jG hmN hmG
    hBVN.2.1 hBVN.2.2.2.1 hBVG.2.1 hBVG.2.2.2.1
    (hKD L hL) (hKJ L hL) (he33 N) hM33 (by positivity) FD FJ hW' hMG hvaluesN hvaluesG

end HRS.Fp81.S21
end
#print axioms HRS.Fp81.S21.fp81s21_recent_rs_physical_supplied
