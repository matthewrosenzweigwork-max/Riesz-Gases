import HRS.MS.ProClosureS111SourceIntegrability
import HRS.MS.ProClosureS111WindowRestriction
import HRS.MS.ProClosureS111ChartInterval

/-!
The exact frozen D02 SourceContractions predicate on the physical shared
path space. The full weighted-test field identifications supply both
pointwise-time formulas. Actual clamped adjoint bounds supply product-time
integrability. The final producer constructs the chart, probability law,
native basis, and both coefficient fields from thermal data.
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open Classical MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.ProClosureS111
open HRS HRS.Whole HRS.MS.R26T6 HRS.MS.S111T
open HRS.MC.QRSpec.Wick

variable {d : ℕ} {Pw : ℝ}

/-- Exact source contractions for the given physical fields. This
consumer permits the stronger paired-moment producer to use these same
fields, rather than constructing another unrelated realization. -/
theorem physical_source_contractions_of_fields (hd : 2 ≤ d)
    {s a beta gamma T u H : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (ha : 0 < a) (hbeta : 0 < beta) (hgamma : 0 ≤ gamma)
    (hu : 0 ≤ u) (hH : u + T ≤ H) (hH0 : 0 ≤ H)
    (hP : (d : ℝ) < 2 * Pw) {rho : Euc d → ℝ}
    (hrho : IsThermalEquilibrium d s a beta rho)
    (P : Measure (PathPair d (wholeSpaceIndex d) H)) [IsProbabilityMeasure P]
    (hZ : r26t6_SharedThermalLaw P s a beta gamma H rho
      (pairedProcess d (wholeSpaceIndex d) H hH0))
    (E : r26t6_WeightedChart d (2 * d + 8) Pw) (side : Fin 2)
    (basis : ℕ → Euc d → ℝ)
    (hbasis : IsR2ZeroMeanONB (HRS.Whole.withDensityReal rho) basis)
    (qLin qQuad : ℝ × PathPair d (wholeSpaceIndex d) H → r26t6_Coeff)
    (hfields : r26t6_PhysicalChartFields P rho s H E basis
      (pairedProcess d (wholeSpaceIndex d) H hH0 side) qLin qQuad) :
    r26t6_SourceContractions P s a beta (r26t6_preparation beta gamma side) rho T u
      (physicalPairedWindow hu hH side)
      (fun t w f => inner ℝ (qQuad (t,w)) (E.encode f))
      (fun t w f => inner ℝ (qLin (t,w)) (E.encode f)) := by
  letI : TopologicalSpace.SeparableSpace r26t6_Coeff :=
    HRS.StaticLimitAux.separable_lp (ι := ℕ)
  letI : SecondCountableTopology r26t6_Coeff :=
    UniformSpace.secondCountable_of_separable r26t6_Coeff
  let Omega := PathPair d (wholeSpaceIndex d) H
  let Z := pairedProcess d (wholeSpaceIndex d) H hH0
  let C := r26t6_thermalCoeff d s a beta rho
  have hsd : s < (d : ℝ) := by linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  have hr : (2 : ℝ) + (d : ℝ) / 2 < (2 * d + 8 : ℕ) := by
    push_cast
    linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  have hprep : 0 ≤ r26t6_preparation beta gamma side := by
    unfold r26t6_preparation
    split_ifs
    · exact hgamma
    · exact hbeta.le
  obtain ⟨Bop, hBop, hOp⟩ := physical_weighted_L2_operators hd s a beta Pw (2 * d + 8)
    hs0 hs ha hbeta hr hP rho hrho
  have hQ := physical_chart_quadratic_all_tests_ae hd s a beta
    (r26t6_preparation beta gamma side) H hs0 hs ha hbeta hprep hr hP rho hrho
    Omega P (Z side) (hZ.evolution side) E basis hbasis qLin qQuad hfields
  have hQ2 := coeff_field_sections_memLp (volume.restrict (Icc (0 : ℝ) H)) P qQuad
    hfields.quadratic_measurable hfields.quadratic_moment
  obtain ⟨G, hG, hmem⟩ := physical_observation_gaussian_space Z hZ
  constructor
  · intro tau phi hphi chi hchi i
    let t : ℝ := u + tau i
    have ht : t ∈ Icc (0 : ℝ) H :=
      ⟨add_nonneg hu (tau i).property.1,
        (add_le_add_right (tau i).property.2 u).trans hH⟩
    have hterm : ∀ j, u + (tau j : ℝ) ∈ Icc (0 : ℝ) H := fun j =>
      ⟨add_nonneg hu (tau j).property.1,
        (add_le_add_right (tau j).property.2 u).trans hH⟩
    let X : Fin 3 → Omega → ℝ := fun j w => OscDual.eval (Z side (u + tau j) w) (phi j)
    have hX4 : ∀ j, MemLp (X j) 4 P := fun j =>
      (hG (X j) (hmem side _ (hterm j) (phi j) (hphi j))).1
    have hobs : ∀ j w, r26t6_obs (physicalPairedWindow hu hH side w) (tau j) (phi j) = X j w := by
      intro j w
      unfold r26t6_obs
      rw [physicalPairedWindow_apply hu hH hH0]
    let F := fun v => propagatorW C (Set.projIcc 0 t ht.1 v) t (phi i)
    obtain ⟨hFm, hFw, B, hB, hb⟩ :=
      physical_encoded_clamped_orbit hd hs0 hsd ha hbeta hrho hP E ht (hphi i)
    let dt : Measure ℝ := volume.restrict (Icc (0 : ℝ) t)
    have hle : dt ≤ volume.restrict (Icc (0 : ℝ) H) :=
      Measure.restrict_mono
        (show Icc (0 : ℝ) t ⊆ Icc (0 : ℝ) H from
          fun _ hv => ⟨hv.1, hv.2.trans ht.2⟩) le_rfl
    have hq : MemLp qQuad 2 (dt.prod P) :=
      hfields.quadratic_moment.mono_measure (Measure.prod_mono hle le_rfl)
    have hXY : MemLp (fun w => X (i + 1) w * X (i + 2) w) 2 P :=
      qrpw_memLp2_mul (hX4 (i + 1)) (hX4 (i + 2))
    have hint := inner_bounded_family_mul_integrable dt P qQuad hq
      (fun v => E.encode (F v)) hFm B hB hb
      (fun w => X (i + 1) w * X (i + 2) w) hXY
    dsimp only
    refine ⟨?_, ?_⟩
    · refine hint.congr ?_
      filter_upwards [Measure.quasiMeasurePreserving_fst.ae
        (ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Icc)] with p hp
      dsimp [F]
      rw [Set.projIcc_of_mem ht.1 hp, hobs (i + 1), hobs (i + 2)]
      simp only [C, r26t6_thermalCoeff]
      simp only [t]
      ring_nf
    · filter_upwards [hQ.filter_mono (ae_mono hle), hQ2.filter_mono (ae_mono hle),
        ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Icc] with v hvQ hv2 hv
      have hvU : v ∈ Icc (0 : ℝ) (u + T) :=
        ⟨hv.1, hv.2.trans (add_le_add_right (tau i).property.2 u)⟩
      have hfw : IsR2WeightedTest (2 * d + 8) Pw (propagatorW C v t (phi i)) := by
        simpa only [Set.projIcc_of_mem ht.1 hv] using hFw v
      have hw := hvQ _ hfw
      have hp := physical_drift_wick_cross_density_pair hd hs0 hs ha hbeta hgamma hu hH
        hrho P Z hZ side tau phi hphi chi hchi hvU basis hbasis
        (fun w => inner ℝ (qQuad (v,w)) (E.encode (propagatorW C v t (phi i))))
        (hv2.inner_const _) (HRS.Whole.commutatorKernel d s (gradient (propagatorW C v t (phi i))))
        (HRS.MS.Comm.comm_symm _) (hOp _ hfw).2.2.1 hw (i + 1) (i + 2)
      simpa only [hobs, C, t, r26t6_thermalCoeff] using hp.2.2
  · intro tau phi hphi chi hchi i
    let ta : ℝ := u + tau i
    let tb : ℝ := u + tau (i + 1)
    let t : ℝ := min ta tb
    have hterm : ∀ j, u + (tau j : ℝ) ∈ Icc (0 : ℝ) H := fun j =>
      ⟨add_nonneg hu (tau j).property.1,
        (add_le_add_right (tau j).property.2 u).trans hH⟩
    have hta : ta ∈ Icc (0 : ℝ) H := hterm i
    have htb : tb ∈ Icc (0 : ℝ) H := hterm (i + 1)
    have ht : t ∈ Icc (0 : ℝ) H :=
      ⟨le_min hta.1 htb.1, (min_le_left _ _).trans hta.2⟩
    let X : Omega → ℝ := fun w => OscDual.eval (Z side (u + tau (i + 2)) w) (phi (i + 2))
    have hX2 : MemLp X 2 P :=
      ((hG X (hmem side _ (hterm (i + 2)) (phi (i + 2)) (hphi (i + 2)))).1).mono_exponent
        (by norm_num)
    have hobs : ∀ w, r26t6_obs (physicalPairedWindow hu hH side w)
        (tau (i + 2)) (phi (i + 2)) = X w := by
      intro w
      unfold r26t6_obs
      rw [physicalPairedWindow_apply hu hH hH0]
    let F := fun v => propagatorW C (Set.projIcc 0 ta hta.1 v) ta (phi i)
    let Gf := fun v => propagatorW C (Set.projIcc 0 tb htb.1 v) tb (phi (i + 1))
    let A := fun v x => inner ℝ (gradient (F v) x) (gradient (Gf v) x)
    obtain ⟨hAm, hAw, B, hB, hb⟩ := physical_encoded_clamped_gradient_pair
      hd hs0 hsd ha hbeta hrho hP E hta htb (hphi i) (hphi (i + 1))
    let dt : Measure ℝ := volume.restrict (Icc (0 : ℝ) t)
    have hle : dt ≤ volume.restrict (Icc (0 : ℝ) H) :=
      Measure.restrict_mono
        (show Icc (0 : ℝ) t ⊆ Icc (0 : ℝ) H from
          fun _ hv => ⟨hv.1, hv.2.trans ht.2⟩) le_rfl
    have hleU : dt ≤ volume.restrict (Icc (0 : ℝ) (u + T)) :=
      Measure.restrict_mono
        (show Icc (0 : ℝ) t ⊆ Icc (0 : ℝ) (u + T) from fun _ hv =>
          ⟨hv.1, (hv.2.trans (min_le_left _ _)).trans
            (add_le_add_right (tau i).property.2 u)⟩) le_rfl
    have hq : MemLp qLin 2 (dt.prod P) :=
      hfields.linear_moment.mono_measure (Measure.prod_mono hle le_rfl)
    have hint := inner_bounded_family_mul_integrable dt P qLin hq
      (fun v => E.encode (A v)) hAm B hB hb X hX2
    have hLin := physical_chart_linear_cross_density_all_tests_ae hd hs0 hs ha hbeta hgamma
      hu hH hr hP hrho P Z hZ E side basis qLin qQuad hfields tau phi hphi chi hchi
    dsimp only
    refine ⟨?_, ?_⟩
    · refine hint.congr ?_
      filter_upwards [Measure.quasiMeasurePreserving_fst.ae
        (ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Icc)] with p hp
      have hpa : p.1 ∈ Icc (0 : ℝ) ta := ⟨hp.1, hp.2.trans (min_le_left _ _)⟩
      have hpb : p.1 ∈ Icc (0 : ℝ) tb := ⟨hp.1, hp.2.trans (min_le_right _ _)⟩
      dsimp [A, F, Gf]
      rw [Set.projIcc_of_mem hta.1 hpa, Set.projIcc_of_mem htb.1 hpb, hobs]
      simp only [C, r26t6_thermalCoeff, ta, tb]
    · filter_upwards [hLin.filter_mono (ae_mono hleU),
        ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Icc] with v hvLin hv
      have hva : v ∈ Icc (0 : ℝ) ta := ⟨hv.1, hv.2.trans (min_le_left _ _)⟩
      have hvb : v ∈ Icc (0 : ℝ) tb := ⟨hv.1, hv.2.trans (min_le_right _ _)⟩
      have hfw : IsR2WeightedTest (2 * d + 8) Pw (fun x =>
          inner ℝ (gradient (propagatorW C v ta (phi i)) x)
            (gradient (propagatorW C v tb (phi (i + 1))) x)) := by
        simpa only [Set.projIcc_of_mem hta.1 hva, Set.projIcc_of_mem htb.1 hvb] using hAw v
      have hp := hvLin _ hfw (i + 2)
      simpa only [hobs, C, r26t6_thermalCoeff] using hp.2.2

/-- An actual joint source realization, from physical data. The chosen
fields satisfy both frozen PhysicalChartFields and SourceContractions on
the same shared law. The independent preparation gamma=0 is included. -/
theorem physical_shared_source_contractions (hd : 2 ≤ d)
    (s a beta gamma T u : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (ha : 0 < a) (hbeta : 0 < beta) (hgamma : 0 ≤ gamma)
    (hT : 0 < T) (hu : 0 ≤ u) (hP : (d : ℝ) < 2 * Pw)
    (rho : Euc d → ℝ) (hrho : IsThermalEquilibrium d s a beta rho)
    (E : r26t6_WeightedChart d (2 * d + 8) Pw) :
    ∃ P : Measure (PathPair d (wholeSpaceIndex d) (u + T)), ∃ hprob : IsProbabilityMeasure P,
      r26t6_SharedThermalLaw P s a beta gamma (u + T) rho
        (pairedProcess d (wholeSpaceIndex d) (u + T) (by linarith)) ∧
      ∃ basis : ℕ → Euc d → ℝ, IsR2ZeroMeanONB (HRS.Whole.withDensityReal rho) basis ∧
      ∃ qLin qQuad : Fin 2 → ℝ × PathPair d (wholeSpaceIndex d) (u + T) → r26t6_Coeff,
        ∀ side,
          @r26t6_PhysicalChartFields d (2 * d + 8) Pw (PathPair d (wholeSpaceIndex d) (u + T)) _
            P hprob rho s (u + T) E basis
            (pairedProcess d (wholeSpaceIndex d) (u + T) (by linarith) side)
            (qLin side) (qQuad side) ∧
          r26t6_SourceContractions P s a beta (r26t6_preparation beta gamma side) rho T u
            (physicalPairedWindow hu le_rfl side)
            (fun t w f => inner ℝ (qQuad side (t,w)) (E.encode f))
            (fun t w f => inner ℝ (qLin side (t,w)) (E.encode f)) := by
  have hH : 0 < u + T := by linarith
  have hr : (2 : ℝ) + (d : ℝ) / 2 < (2 * d + 8 : ℕ) := by
    push_cast
    linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  obtain ⟨P, hprob, hZ, basis, hbasis, qLin, qQuad, hfields⟩ :=
    physical_shared_chart_fields hd s a beta gamma (u + T) hs0 hs ha hbeta hgamma hH
      hr hP rho hrho E
  letI : IsProbabilityMeasure P := hprob
  refine ⟨P, hprob, hZ, basis, hbasis, qLin, qQuad, fun side => ⟨hfields side, ?_⟩⟩
  exact physical_source_contractions_of_fields hd hs0 hs ha hbeta hgamma hu le_rfl hH.le
    hP hrho P hZ E side basis hbasis (qLin side) (qQuad side) (hfields side)

/-- The exact core chart is chosen once, before the density and every
moving-window start. The subsequent source data are actual physical
constructions for both preparation sides. -/
theorem physical_core_source_data (hd : 2 ≤ d)
    (s a beta gamma T : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (ha : 0 < a) (hbeta : 0 < beta) (hgamma : 0 ≤ gamma) (hT : 0 < T) :
    ∃ E : r26t6_WeightedChart d (r26t6_coreOrder d) (r26t6_coreWeight d),
      ∀ rho : Euc d → ℝ, IsThermalEquilibrium d s a beta rho →
      ∀ u : ℝ, ∀ hu : 0 ≤ u,
      ∃ P : Measure (PathPair d (wholeSpaceIndex d) (u + T)), ∃ hprob : IsProbabilityMeasure P,
        r26t6_SharedThermalLaw P s a beta gamma (u + T) rho
          (pairedProcess d (wholeSpaceIndex d) (u + T) (by linarith)) ∧
        ∃ basis : ℕ → Euc d → ℝ, IsR2ZeroMeanONB (HRS.Whole.withDensityReal rho) basis ∧
        ∃ qLin qQuad : Fin 2 → ℝ × PathPair d (wholeSpaceIndex d) (u + T) → r26t6_Coeff,
          ∀ side,
            @r26t6_PhysicalChartFields d (r26t6_coreOrder d) (r26t6_coreWeight d)
              (PathPair d (wholeSpaceIndex d) (u + T)) _ P hprob rho s (u + T) E basis
              (pairedProcess d (wholeSpaceIndex d) (u + T) (by linarith) side)
              (qLin side) (qQuad side) ∧
            r26t6_SourceContractions P s a beta (r26t6_preparation beta gamma side) rho T u
              (physicalPairedWindow hu le_rfl side)
              (fun t w f => inner ℝ (qQuad side (t,w)) (E.encode f))
              (fun t w f => inner ℝ (qLin side (t,w)) (E.encode f)) := by
  obtain ⟨E⟩ := physical_core_weighted_chart (show 0 < d by omega)
  have hP : (d : ℝ) < 2 * r26t6_coreWeight d := by
    unfold r26t6_coreWeight
    linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  exact ⟨E, fun rho hrho u hu => physical_shared_source_contractions hd s a beta gamma T u
    hs0 hs ha hbeta hgamma hT hu hP rho hrho E⟩

end HRS.MS.ProClosureS111

#print axioms HRS.MS.ProClosureS111.physical_source_contractions_of_fields
#print axioms HRS.MS.ProClosureS111.physical_shared_source_contractions
#print axioms HRS.MS.ProClosureS111.physical_core_source_data
