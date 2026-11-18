import HRS.MS.Fp81S21CovMeasure2

/-!
# S2.1(iii), packet 16d: interval covariance coordinates

The summed interval tensor has the packet-15 coordinate formula on the whole
interval.  The scalar integrand is shown integrable from the localized trace
bound and `IsR2L1F`; no coordinate-integrability hypothesis is added.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Set Classical Filter
open scoped ENNReal NNReal BigOperators

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.Uniform HRS.Uniform.Q45 HRS.MS.CovMeas
open HRS.MS.GenPath HRS.MS.R26T3 HRS.MS.R2WinErr HRS.MS.R2WinOrbNL
open HRS.MS.R2WinOrb HRS.MS.FixEq Function

private theorem fp81s21_windowDm_entry_integrable
    {d : ℕ} {C : WholeCoeff d} {m H a : ℝ} {r : ℕ} {P : ℝ}
    {z : ℝ → (Euc d → ℝ) → ℝ} {Cmix cdec : ℝ}
    (D : fp81s21_WindowLocalInput C m H a r P z Cmix cdec)
    (u w : KSpace d m H) :
    IntegrableOn (fun v => fp81s21_windowDm C m H a z D.fp81s21_ha
      (le_of_lt D.fp81s21_hH) v u w) (Icc (0 : ℝ) (a + H)) := by
  let T : Set ℝ := Icc (0 : ℝ) (a + H)
  let B0 : ℝ := fp81s21_window_feature_Bpos d r H Cmix cdec a a
  let C0 : ℝ := s57pC d r P * ((d : ℝ) * 2 ^ r * B0 ^ 2)
  let K : ℝ≥0∞ := ENNReal.ofReal |2 * C.ν| * ENNReal.ofReal C0
  have hpos := fp81s21_windowLocalInput_hPosEnvelope D
  have hentries := fp81s21_windowDm_meas_entries D.fp81s21_hd D.fp81s21_hH
    D.fp81s21_ha D.fp81s21_horb D.fp81s21_hterminal D.fp81s21_hz
    D.fp81s21_hP D.fp81s21_hm hpos
  have htraceMeas : Measurable (fun v => HRS.traceNormForm
      (fp81s21_windowDm C m H a z D.fp81s21_ha
        (le_of_lt D.fp81s21_hH) v)) :=
    HRS.measurable_traceNormForm _ hentries
  have hK : K < ⊤ := by
    dsimp [K]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  have hB0 : 0 ≤ B0 := by
    dsimp [B0, fp81s21_window_feature_Bpos, fp81s21_window_Bpos]
    positivity [D.fp81s21_hCmix]
  have hC0 : 0 ≤ C0 := by
    dsimp [C0]
    exact mul_nonneg (s57pC_nonneg d r P) (by positivity)
  have htraceBound : ∀ v ∈ T,
      ENNReal.ofReal (HRS.traceNormForm
        (fp81s21_windowDm C m H a z D.fp81s21_ha
          (le_of_lt D.fp81s21_hH) v)) ≤ K * dualNormE r P (z v) := by
    intro v hv
    have hpoint := fp81s21_windowDm_trace_bound D.fp81s21_hd D.fp81s21_hH
      D.fp81s21_ha D.fp81s21_horb D.fp81s21_hterminal D.fp81s21_hz
      D.fp81s21_hP D.fp81s21_hm hpos v hv
    calc
      _ ≤ ENNReal.ofReal |2 * C.ν| * dualNormE r P (z v) * ENNReal.ofReal C0 := by
        simpa [C0, B0] using hpoint
      _ = K * dualNormE r P (z v) := by
        dsimp [K]
        ac_rfl
  have htraceFinite :
      (∫⁻ v in T, ENNReal.ofReal (HRS.traceNormForm
        (fp81s21_windowDm C m H a z D.fp81s21_ha
          (le_of_lt D.fp81s21_hH) v))) < ⊤ := by
    calc
      _ ≤ ∫⁻ v in T, K * dualNormE r P (z v) :=
        setLIntegral_mono' measurableSet_Icc htraceBound
      _ = K * ∫⁻ v in T, dualNormE r P (z v) := by
        rw [lintegral_const_mul' _ _ (ne_of_lt hK)]
      _ < ⊤ := ENNReal.mul_lt_top hK D.fp81s21_hz.2.2
  have htraceInt : IntegrableOn (fun v => HRS.traceNormForm
      (fp81s21_windowDm C m H a z D.fp81s21_ha
        (le_of_lt D.fp81s21_hH) v)) T := by
    refine ⟨htraceMeas.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal
      (Filter.Eventually.of_forall fun v => HRS.traceNormForm_nonneg _)]
    exact htraceFinite
  obtain ⟨G, hG, hspec⟩ := fp81s21_windowDm_good_spec
    D.fp81s21_hd D.fp81s21_hH D.fp81s21_ha D.fp81s21_horb
    D.fp81s21_hterminal D.fp81s21_hz D.fp81s21_hP D.fp81s21_hm hpos
  have htraceBdd : ∀ v ∈ T, BddAbove (Set.range fun p : HRS.OrthonormalPairs
      (KSpace d m H) => ∑ i, |fp81s21_windowDm C m H a z
        D.fp81s21_ha (le_of_lt D.fp81s21_hH) v (p.1.2.1 i) (p.1.2.2 i)|) := by
    intro v hv
    have hdata := fp81s21_windowD_data D.fp81s21_hd D.fp81s21_hH
      D.fp81s21_ha D.fp81s21_horb D.fp81s21_hterminal D.fp81s21_hz
      D.fp81s21_hP hv (hpos v hv)
    rw [hspec v]
    split_ifs with hvG
    · exact hdata.2.2.1
    · refine ⟨0, ?_⟩
      rintro x ⟨p, rfl⟩
      simp
  refine Integrable.mono' (htraceInt.mul_const (‖u‖ * ‖w‖))
    (hentries u w).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
  rw [Real.norm_eq_abs]
  exact HRS.MS.CovMeas.s101_abs_le_tn (htraceBdd v hv) u w

private theorem fp81s21_window_covariance_coordinate_integrable
    {d : ℕ} {C : WholeCoeff d} {m H a : ℝ} {r : ℕ} {P : ℝ}
    {z : ℝ → (Euc d → ℝ) → ℝ} {Cmix cdec : ℝ}
    (D : fp81s21_WindowLocalInput C m H a r P z Cmix cdec)
    (hlin : ∀ u t : ℝ, 0 ≤ u → u ≤ t → t ≤ a + H →
      ∀ φ ψ : Euc d → ℝ, ∀ c : ℝ,
        IsR2DualCombo m φ → IsR2DualCombo m ψ →
        propagatorW C u t (φ + c • ψ) =
          propagatorW C u t φ + c • propagatorW C u t ψ)
    (hν : C.ν ≠ 0)
    {q s ta tb : ℝ} (hq : 0 ≤ q) (hqs : q ≤ s)
    (hta : ta ∈ Icc (0 : ℝ) H) (htb : tb ∈ Icc (0 : ℝ) H)
    {φa φb : Euc d → ℝ} (hφa : IsR2DualCombo m φa)
    (hφb : IsR2DualCombo m φb) :
    IntegrableOn (fun v => z v (fun x => inner ℝ
      (gradient (propagatorW C v (a + ta) φa) x)
      (gradient (propagatorW C v (a + tb) φb) x)))
      (Ioc q s ∩ Icc (0 : ℝ) (min (a + ta) (a + tb))) := by
  obtain ⟨Sa, ca, rfl⟩ := hφa
  obtain ⟨Sb, cb, rfl⟩ := hφb
  let Pa := s101Pc m H ta Sa ca
  let Qa := s101Qc m H Sa ca
  let Pb := s101Pc m H tb Sb cb
  let Qb := s101Qc m H Sb cb
  let Ua := Pa + Qa
  let Ub := Pb + Qb
  let T : Set ℝ := Icc (0 : ℝ) (a + H)
  let S : Set ℝ := Ioc q s ∩ Icc (0 : ℝ) (min (a + ta) (a + tb))
  have hSsub : S ⊆ T := by
    intro v hv
    refine ⟨hv.2.1, ?_⟩
    exact hv.2.2.trans (min_le_left _ _ |>.trans (by linarith [D.fp81s21_ha, hta.2]))
  have hSmeas : MeasurableSet S := measurableSet_Ioc.inter measurableSet_Icc
  have hpos := fp81s21_windowLocalInput_hPosEnvelope D
  have hwindowDm := fp81s21_windowDm_ae_eq_windowD
    D.fp81s21_hd D.fp81s21_hH D.fp81s21_ha D.fp81s21_horb
    D.fp81s21_hterminal D.fp81s21_hz D.fp81s21_hP D.fp81s21_hm hpos
  have hwindowDmS : ∀ᵐ v ∂(volume.restrict S),
      fp81s21_windowDm C m H a z D.fp81s21_ha
        (le_of_lt D.fp81s21_hH) v = fp81s21_windowD C m H a z v :=
    ae_restrict_of_ae_restrict_of_subset hSsub hwindowDm
  have hentry := fp81s21_windowDm_entry_integrable D Ua Ub
  have hentryS : IntegrableOn (fun v => fp81s21_windowDm C m H a z
      D.fp81s21_ha (le_of_lt D.fp81s21_hH) v Ua Ub) S := hentry.mono_set hSsub
  have hentryEq : ∀ᵐ v ∂(volume.restrict S),
      fp81s21_windowDm C m H a z D.fp81s21_ha
        (le_of_lt D.fp81s21_hH) v Ua Ub =
      (2 * C.ν) * z v (fun x => inner ℝ
        (gradient (propagatorW C v (a + ta)
          (fun y => ∑ α ∈ Sa, ca α * oscTestFun m α y)) x)
        (gradient (propagatorW C v (a + tb)
          (fun y => ∑ β ∈ Sb, cb β * oscTestFun m β y)) x)) := by
    filter_upwards [hwindowDmS, ae_restrict_mem hSmeas] with v hDm hvS
    have hvT : v ∈ T := hSsub hvS
    have hvta : v ≤ a + ta := hvS.2.2.trans (min_le_left _ _)
    have hvtb : v ≤ a + tb := hvS.2.2.trans (min_le_right _ _)
    have hcut := fp81s21_windowD_combo_gradient_cutoff D hlin hvT hta htb
      Sa Sb ca cb
    rw [hDm]
    simpa [Ua, Ub, Pa, Qa, Pb, Qb, hvta, hvtb] using hcut
  have hscaled : IntegrableOn (fun v => (2 * C.ν) * z v (fun x => inner ℝ
      (gradient (propagatorW C v (a + ta)
        (fun y => ∑ α ∈ Sa, ca α * oscTestFun m α y)) x)
      (gradient (propagatorW C v (a + tb)
        (fun y => ∑ β ∈ Sb, cb β * oscTestFun m β y)) x))) S :=
    hentryS.congr hentryEq
  have hν2 : (2 * C.ν) ≠ 0 := by
    intro h
    apply hν
    linarith
  have hscaled' := hscaled.const_mul ((2 * C.ν)⁻¹)
  have hscaledEq : (fun v => (2 * C.ν)⁻¹ * ((2 * C.ν) *
      z v (fun x => inner ℝ
        (gradient (propagatorW C v (a + ta)
          (fun y => ∑ α ∈ Sa, ca α * oscTestFun m α y)) x)
        (gradient (propagatorW C v (a + tb)
          (fun y => ∑ β ∈ Sb, cb β * oscTestFun m β y)) x)))) =ᵐ[volume.restrict S]
      (fun v => z v (fun x => inner ℝ
        (gradient (propagatorW C v (a + ta)
          (fun y => ∑ α ∈ Sa, ca α * oscTestFun m α y)) x)
        (gradient (propagatorW C v (a + tb)
          (fun y => ∑ β ∈ Sb, cb β * oscTestFun m β y)) x))) := by
    filter_upwards with v
    simp [mul_assoc, hν]
  exact hscaled'.congr hscaledEq

/-- The summed interval covariance has the required shifted coordinate
formula on `(q,s]`.  The half-open unit blocks partition the positive line;
changing each closed packet-15 block at its left endpoint is harmless because
that endpoint is Lebesgue null. -/
theorem fp81s21_window_covariance_measure_isWindowJValue
    {d : ℕ} {C : WholeCoeff d} {m H a : ℝ} {r : ℕ} {P : ℝ}
    {z : ℝ → (Euc d → ℝ) → ℝ} {Cmix cdec : ℝ}
    (D : fp81s21_WindowLocalInput C m H a r P z Cmix cdec)
    (hlin : ∀ u t : ℝ, 0 ≤ u → u ≤ t → t ≤ a + H →
      ∀ φ ψ : Euc d → ℝ, ∀ c : ℝ,
        IsR2DualCombo m φ → IsR2DualCombo m ψ →
        propagatorW C u t (φ + c • ψ) =
          propagatorW C u t φ + c • propagatorW C u t ψ)
    (hblocks : ∀ I : Set ℝ, MeasurableSet I → ∀ k,
      fp81s21_WindowCovarianceBlockContract D hlin I k)
    (hdual : AEMeasurable (fun v => dualNormE r P (z v))
      (volume.restrict (Icc (0 : ℝ) (a + H))))
    {q s : ℝ} (hq : 0 ≤ q) (hqs : q ≤ s) :
    fp81s21_IsWindowJValue C m H a z (Ioc q s)
      ((fp81s21_window_covariance_measure D q s : projTensor (OscPath d m H) 2) :
        TensorDual (OscPath d m H) 2) := by
  constructor
  · exact (fp81s21_window_covariance_measure D q s :
      projTensor (OscPath d m H) 2).property
  · intro ta tb φa φb l₁ l₂ hφa hφb hta htb h₁ h₂
    let M : OscPath d m H [×2]→L[ℝ] ℝ :=
      (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 2) ℝ).compContinuousLinearMap ![l₁, l₂]
    let S : Set ℝ := Ioc q s ∩ Icc (0 : ℝ) (min (a + ta) (a + tb))
    let B : ℕ → Set ℝ := fun k => Ioc (k : ℝ) ((k : ℝ) + 1) ∩ S
    have hcoord := fp81s21_window_covariance_cumulative_coordinate_tsum
      D hlin hblocks hdual (q0 := q) (u := s) M
    have hSmeas : MeasurableSet S := measurableSet_Ioc.inter measurableSet_Icc
    have hSpos : S ⊆ Ioi (0 : ℝ) := by
      intro v hv
      exact lt_of_le_of_lt hq hv.1.1
    have hBmeas : ∀ k, MeasurableSet (B k) := by
      intro k
      exact measurableSet_Ioc.inter hSmeas
    have hBpair : Pairwise (Disjoint on B) := by
      intro i j hij
      change Disjoint (B i) (B j)
      rw [Set.disjoint_left]
      intro v hvi hvj
      rcases lt_or_gt_of_ne hij with hij' | hji
      · have hstep : (i : ℝ) + 1 ≤ (j : ℝ) := by
          exact_mod_cast Nat.succ_le_of_lt hij'
        linarith [hvi.1.2, hvj.1.1]
      · have hstep : (j : ℝ) + 1 ≤ (i : ℝ) := by
          exact_mod_cast Nat.succ_le_of_lt hji
        linarith [hvj.1.2, hvi.1.1]
    have hUnion : (⋃ k, B k) = S := by
      ext v
      constructor
      · intro hv
        rcases Set.mem_iUnion.mp hv with ⟨k, hk⟩
        exact hk.2
      · intro hv
        have hvpos := hSpos hv
        have hvunit : v ∈ ⋃ k : ℕ, Ioc (k : ℝ) ((k : ℝ) + 1) := by
          rw [fp81s21_natUnitBlocks_iUnion]
          exact hvpos
        rcases Set.mem_iUnion.mp hvunit with ⟨k, hk⟩
        exact Set.mem_iUnion.mpr ⟨k, ⟨hk, hv⟩⟩
    by_cases hν : C.ν = 0
    · have hblockZero : ∀ k : ℕ,
          ((fp81s21_blockValue D (Ioc q s) k : projTensor (OscPath d m H) 2) :
            TensorDual (OscPath d m H) 2) M = 0 := by
        intro k
        have hspec := (hblocks (Ioc q s) measurableSet_Ioc k).coordinate_spec.2
          ta tb φa φb l₁ l₂ hφa hφb hta htb h₁ h₂
        simp [hν] at hspec
        exact hspec
      change ((fp81s21_window_covariance_cumulative D q s : projTensor (OscPath d m H) 2) :
        TensorDual (OscPath d m H) 2) M = _
      rw [hcoord.2]
      rw [tsum_congr hblockZero]
      simp [hν]
    · have hfi := fp81s21_window_covariance_coordinate_integrable
        D hlin hν hq hqs hta htb hφa hφb
      have hfiUnion : IntegrableOn
          (fun v => z v (fun x => inner ℝ
            (gradient (propagatorW C v (a + ta) φa) x)
            (gradient (propagatorW C v (a + tb) φb) x))) (⋃ k, B k) := by
        rw [hUnion]
        exact hfi
      have hpart := integral_iUnion hBmeas hBpair hfiUnion
      have hclosed : ∀ k : ℕ,
          ∫ v in Icc (k : ℝ) ((k : ℝ) + 1) ∩ S,
            z v (fun x => inner ℝ
              (gradient (propagatorW C v (a + ta) φa) x)
              (gradient (propagatorW C v (a + tb) φb) x)) =
          ∫ v in B k, z v (fun x => inner ℝ
              (gradient (propagatorW C v (a + ta) φa) x)
              (gradient (propagatorW C v (a + tb) φb) x)) := by
        intro k
        have hAE : Icc (k : ℝ) ((k : ℝ) + 1) ∩ S =ᵐ[volume] B k := by
          filter_upwards [Ioc_ae_eq_Icc (a := (k : ℝ))
            (b := (k : ℝ) + 1) (μ := volume)] with v hv
          simpa [B] using (and_congr (Iff.of_eq hv.symm) Iff.rfl)
        exact setIntegral_congr_set hAE
      have hblock : ∀ k : ℕ,
          ((fp81s21_blockValue D (Ioc q s) k : projTensor (OscPath d m H) 2) :
            TensorDual (OscPath d m H) 2) M =
          (2 * C.ν) * ∫ v in Icc (k : ℝ) ((k : ℝ) + 1) ∩ S,
            z v (fun x => inner ℝ
              (gradient (propagatorW C v (a + ta) φa) x)
              (gradient (propagatorW C v (a + tb) φb) x)) := by
        intro k
        have hspec := (hblocks (Ioc q s) measurableSet_Ioc k).coordinate_spec.2
          ta tb φa φb l₁ l₂ hφa hφb hta htb h₁ h₂
        simpa [S, Set.inter_assoc, Set.inter_left_comm, Set.inter_comm, M] using hspec
      change ((fp81s21_window_covariance_cumulative D q s : projTensor (OscPath d m H) 2) :
        TensorDual (OscPath d m H) 2) M = _
      rw [hcoord.2]
      rw [tsum_congr hblock]
      rw [tsum_mul_left]
      congr 1
      calc
        _ = ∑' k, ∫ v in B k, z v (fun x => inner ℝ
            (gradient (propagatorW C v (a + ta) φa) x)
            (gradient (propagatorW C v (a + tb) φb) x)) := tsum_congr hclosed
        _ = ∫ v in S, z v (fun x => inner ℝ
            (gradient (propagatorW C v (a + ta) φa) x)
            (gradient (propagatorW C v (a + tb) φb) x)) := by
          rw [← hpart, hUnion]

#print axioms fp81s21_window_covariance_measure_isWindowJValue

end HRS.Fp81.S21

end
