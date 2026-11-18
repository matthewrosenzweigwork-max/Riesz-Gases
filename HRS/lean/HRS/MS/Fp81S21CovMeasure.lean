import HRS.MS.Fp81S21CovSum7

/-!
# S2.1(iii), packet 16d: interval covariance sums

The interval value is the convergent sum of the packet-15 block values on
`(q,r]`.  The physical wrapper exposes one localized input for all intervals;
`hdual` remains explicit wherever the summed source estimate is used.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Set Classical
open scoped ENNReal NNReal BigOperators

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.Uniform HRS.Uniform.Q45 HRS.MS.CovMeas
open HRS.MS.GenPath HRS.MS.R26T3 HRS.MS.R2WinErr HRS.MS.R2WinOrbNL
open HRS.MS.R2WinOrb HRS.MS.FixEq

/-- The physical block theorem's pointwise existential can be made uniform
in the measurable set and block index.  `WindowLocalInput` is a proposition,
so proof irrelevance identifies the input selected at one interval with the
input selected at every other interval. -/
theorem fp81s21_window_covariance_block_physical_one_input (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
      ∃ Cs0 cdec Cmix : ℝ,
        0 ≤ Cs0 ∧ 0 < cdec ∧ Summable (s104_b p.d) ∧
        0 ≤ Cmix ∧ Cs0 ≤ Cmix ∧
        ∀ a : ℝ, 0 ≤ a → ∀ P : ℝ,
          ∀ z : ℝ → (Euc p.d → ℝ) → ℝ,
          IsR2L1F (2 * p.d + 8) P (a + p.T) z →
          (p.d : ℝ) < 2 * P →
          R2JIntegrandMeas (r26t3_coeff R)
            (wholeSpaceIndex p.d : ℝ) (a + p.T) z →
          ∃ D : fp81s21_WindowLocalInput (r26t3_coeff R)
            (wholeSpaceIndex p.d : ℝ) p.T a (2 * p.d + 8) P z Cmix cdec,
            ∀ I : Set ℝ, MeasurableSet I → ∀ k : ℕ,
              fp81s21_WindowCovarianceBlockContract D
                (fp81s21_cov_block_linearity p R a) I k := by
  obtain ⟨δ0, hδ0, hδ0Half, hphysical⟩ :=
    fp81s21_window_covariance_block_physical p
  refine ⟨δ0, hδ0, hδ0Half, ?_⟩
  intro δ hδ hδle R
  obtain ⟨Cs0, cdec, Cmix, hCs0, hcdec, hsumb, hCmix, hCs0Cmix, hbody⟩ :=
    hphysical δ hδ hδle R
  refine ⟨Cs0, cdec, Cmix, hCs0, hcdec, hsumb, hCmix, hCs0Cmix, ?_⟩
  intro a ha P z hz hP hm
  obtain ⟨D, hD⟩ := hbody a ha P z hz hP hm
    ∅ MeasurableSet.empty 0
  refine ⟨D, ?_⟩
  intro I hI k
  obtain ⟨D', hD'⟩ := hbody a ha P z hz hP hm I hI k
  have hEq : D' = D := Subsingleton.elim _ _
  cases hEq
  exact hD'

/-- Summed covariance value on the interval `(q,r]`. -/
noncomputable def fp81s21_window_covariance_measure
    {d : ℕ} {C : WholeCoeff d} {m H a : ℝ} {r : ℕ} {P : ℝ}
    {z : ℝ → (Euc d → ℝ) → ℝ} {Cmix cdec : ℝ}
    (D : fp81s21_WindowLocalInput C m H a r P z Cmix cdec)
    (q s : ℝ) : projTensor (OscPath d m H) 2 :=
  ∑' k : ℕ, fp81s21_blockValue D (Ioc q s) k

/-- The summed interval map is additive on adjacent intervals.  Summability
of all three block series follows from the weighted source estimate, with its
necessary dual-norm measurability premise displayed. -/
theorem fp81s21_window_covariance_measure_add
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
    {q s t : ℝ} (hqs : q ≤ s) (hst : s ≤ t) :
    fp81s21_window_covariance_measure D q t =
      fp81s21_window_covariance_measure D q s +
        fp81s21_window_covariance_measure D s t := by
  let fqs : ℕ → projTensor (OscPath d m H) 2 :=
    fun k => fp81s21_blockValue D (Ioc q s) k
  let fst : ℕ → projTensor (OscPath d m H) 2 :=
    fun k => fp81s21_blockValue D (Ioc s t) k
  let fqt : ℕ → projTensor (OscPath d m H) 2 :=
    fun k => fp81s21_blockValue D (Ioc q t) k
  have hsumqs := fp81s21_window_covariance_blocks_tsum_weighted D hlin
    (Ioc q s) measurableSet_Ioc (fun k => hblocks (Ioc q s) measurableSet_Ioc k) hdual
  have hsumst := fp81s21_window_covariance_blocks_tsum_weighted D hlin
    (Ioc s t) measurableSet_Ioc (fun k => hblocks (Ioc s t) measurableSet_Ioc k) hdual
  have hsumqt := fp81s21_window_covariance_blocks_tsum_weighted D hlin
    (Ioc q t) measurableSet_Ioc (fun k => hblocks (Ioc q t) measurableSet_Ioc k) hdual
  have hsqs : Summable fqs := Summable.of_enorm (ne_top_of_lt hsumqs.2.1)
  have hsst : Summable fst := Summable.of_enorm (ne_top_of_lt hsumst.2.1)
  have hqt : Summable fqt := Summable.of_enorm (ne_top_of_lt hsumqt.2.1)
  have hunion : Ioc q s ∪ Ioc s t = Ioc q t :=
    Set.Ioc_union_Ioc_eq_Ioc hqs hst
  have hdisj : Disjoint (Ioc q s) (Ioc s t) :=
    Set.Ioc_disjoint_Ioc_of_le le_rfl
  have hoverlap : volume (Ioc q s ∩ Ioc s t) = 0 := by
    rw [Set.disjoint_iff_inter_eq_empty.mp hdisj]
    simp
  have hblock : ∀ k, fqt k = fqs k + fst k := by
    intro k
    change fp81s21_blockValue D (Ioc q t) k = _
    rw [← hunion]
    exact fp81s21_blockValue_union D measurableSet_Ioc measurableSet_Ioc
      hoverlap k
  change (∑' k, fqt k) = (∑' k, fqs k) + ∑' k, fst k
  calc
    (∑' k, fqt k) = ∑' k, (fqs k + fst k) := tsum_congr hblock
    _ = (∑' k, fqs k) + ∑' k, fst k := hsqs.tsum_add hsst

/-- The interval covariance vanishes on the diagonal. -/
theorem fp81s21_window_covariance_measure_diagonal
    {d : ℕ} {C : WholeCoeff d} {m H a : ℝ} {r : ℕ} {P : ℝ}
    {z : ℝ → (Euc d → ℝ) → ℝ} {Cmix cdec : ℝ}
    (D : fp81s21_WindowLocalInput C m H a r P z Cmix cdec)
    (q : ℝ) : fp81s21_window_covariance_measure D q q = 0 := by
  have hzero : ∀ k : ℕ, fp81s21_blockValue D (∅ : Set ℝ) k = 0 := by
    intro k
    have h := fp81s21_blockValue_union D (I := (∅ : Set ℝ)) (I' := ∅)
      MeasurableSet.empty MeasurableSet.empty (by simp) k
    have h' : fp81s21_blockValue D ∅ k + 0 =
        fp81s21_blockValue D ∅ k + fp81s21_blockValue D ∅ k := by
      simpa using h
    have hz : (0 : projTensor (OscPath d m H) 2) =
        fp81s21_blockValue D ∅ k := add_left_cancel h'
    exact hz.symm
  change (∑' k : ℕ, fp81s21_blockValue D (Ioc q q) k) = 0
  rw [show Ioc q q = (∅ : Set ℝ) by ext x; simp]
  simp [fp81s21_window_covariance_measure, hzero]

/-- Interval-local total-variation domination by one weighted source
integral.  The constant is exactly the product in the summed packet-15/16b
bound and is independent of `z`, `q`, and `s`. -/
theorem fp81s21_window_covariance_measure_norm_le
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
    {q s : ℝ} (hq : 0 ≤ q) (hqs : q ≤ s) (hs : s ≤ a + H) :
    ‖fp81s21_window_covariance_measure D q s‖ₑ ≤
      (ENNReal.ofReal ((3 + Real.sqrt H) ^ 2 * fp81s21_blockC0) *
        ENNReal.ofReal |2 * C.ν| *
        ENNReal.ofReal (s57pC d r P * ((d : ℝ) * 2 ^ r *
          (fp81s21_windowCovBlockAmp d r H Cmix) ^ 2))) *
      (∫⁻ v in Ioc q s, dualNormE r P (z v) *
        ENNReal.ofReal (Real.exp (-2 * cdec * max (a - v) 0))) := by
  letI : CompleteSpace (projTensor (OscPath d m H) 2) :=
    HRS.Fp81.V01.fp81v01_projTensorComplete (OscPath d m H) 2
  have hsum := fp81s21_window_covariance_blocks_tsum_weighted D hlin
    (Ioc q s) measurableSet_Ioc
    (fun k => hblocks (Ioc q s) measurableSet_Ioc k) hdual
  have hnorm := enorm_tsum_le_tsum_enorm
    (f := fun k : ℕ => fp81s21_blockValue D (Ioc q s) k)
  have hsubset : Ioc q s ⊆ Ioc (0 : ℝ) (a + H) := by
    intro v hv
    exact ⟨lt_of_le_of_lt hq hv.1, hv.2.trans hs⟩
  have hinter : Ioc q s ∩ Ioc (0 : ℝ) (a + H) = Ioc q s :=
    Set.inter_eq_left.mpr hsubset
  calc
    ‖fp81s21_window_covariance_measure D q s‖ₑ ≤
        ∑' k, ‖fp81s21_blockValue D (Ioc q s) k‖ₑ := by
      simpa [fp81s21_window_covariance_measure] using hnorm
    _ ≤ (ENNReal.ofReal ((3 + Real.sqrt H) ^ 2 * fp81s21_blockC0) *
        ENNReal.ofReal |2 * C.ν| *
        ENNReal.ofReal (s57pC d r P * ((d : ℝ) * 2 ^ r *
          (fp81s21_windowCovBlockAmp d r H Cmix) ^ 2))) *
        (∫⁻ v in Ioc q s ∩ Ioc (0 : ℝ) (a + H),
          dualNormE r P (z v) * ENNReal.ofReal
            (Real.exp (-2 * cdec * max (a - v) 0))) := hsum.1
    _ = _ := by rw [hinter]

/-- Continuity of the cumulative interval map on each bounded source interval.
The dual-norm AEMeasurability required by dominated convergence is explicit. -/
theorem fp81s21_window_covariance_measure_cumulative_continuousOn
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
    {q T : ℝ} (hq : 0 ≤ q) (hqT : q ≤ T) (hT : T ≤ a + H) :
    ContinuousOn (fun s => fp81s21_window_covariance_measure D q s) (Icc q T) := by
  letI : CompleteSpace (projTensor (OscPath d m H) 2) :=
    HRS.Fp81.V01.fp81v01_projTensorComplete (OscPath d m H) 2
  change ContinuousOn (fp81s21_window_covariance_cumulative D q) (Icc q T)
  exact fp81s21_window_covariance_cumulative_continuousOn D hlin hblocks hdual
    hq hqT hT

#print axioms fp81s21_window_covariance_block_physical_one_input
#print axioms fp81s21_window_covariance_measure
#print axioms fp81s21_window_covariance_measure_add
#print axioms fp81s21_window_covariance_measure_diagonal
#print axioms fp81s21_window_covariance_measure_norm_le
#print axioms fp81s21_window_covariance_measure_cumulative_continuousOn

end HRS.Fp81.S21

end
