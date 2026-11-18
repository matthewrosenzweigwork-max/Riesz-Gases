import HRS.MS.Fp81S21WickMomRep8
import HRS.MS.Fp81S21TimeRep15

/-! Canonical weak half-Wick field and its time sections. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory
open scoped ENNReal
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.ProClosureS111 HRS.MS.R2Interp

/-- The normalized embedding transports compact-test actions. -/
theorem fp81s21_embedField_normalized_action
    {d r r' : ℕ} {Pw Ps : ℝ}
    (hr : r + 2 = r') (hp : Pw + 2 = Ps)
    (hP : (d : ℝ) < 2 * Pw) (hPs : (d : ℝ) < 2 * Ps)
    (Es : r26t6_WeightedChart d r Ps) (E : r26t6_WeightedChart d r' Pw)
    (z : r26t6_Coeff) (f : Euc d → ℝ) (hf : IsR2Test f) :
    fp81s21_chartAction E (fp81s21_embedField_normalized hr hp hP hPs Es E z) f =
      fp81s21_chartAction Es z f := by
  subst r'
  subst Ps
  exact fp81s21_embedField_action hP hPs Es E z f hf

/-- The embedded chart action is a canonical weighted extension, with
measurable time sections and their weighted-test evaluations. -/
theorem fp81s21_wick_weak_TimeRep
    {d r r' : ℕ} {Pw Ps : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    (hr : r + 2 = r') (hp : Pw + 2 = Ps)
    (hP : (d : ℝ) < 2 * Pw) (hPs : (d : ℝ) < 2 * Ps)
    (Es : r26t6_WeightedChart d r Ps) (E : r26t6_WeightedChart d r' Pw)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (qs : ℝ → Ω → r26t6_Coeff) (M : ℝ)
    (hrep : fp81s21_MomentRep Es P (fp81s21_wickChartField Es qs) qs M) :
    ∃ qe : ℝ → Ω → r26t6_Coeff,
      (∀ u ω, qe u ω = fp81s21_embedField_normalized hr hp hP hPs Es E (qs u ω)) ∧
      fp81s21_MomentRep E P (fp81s21_wickChartField Es qs) qe M ∧
      (∀ u ω f, IsR2Test f →
        fp81s21_chartAction E (qe u ω) f = fp81s21_wickChartField Es qs u ω f) ∧
      (∀ u ω, S102Z r' Pw (fp81s21_chartAction E (qe u ω))) ∧
      ∀ a : ℝ, 0 ≤ a → ∀ H : ℝ, 0 ≤ H →
        ∃ U : Ω → Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H)),
          fp81s21_TimeL2Rep P qe M a H U ∧
          fp81s21_TimeRep E P (fun u ω => fp81s21_chartAction E (qe u ω)) qe M a H U := by
  let qe : ℝ → Ω → r26t6_Coeff := fun u ω =>
    fp81s21_embedField_normalized hr hp hP hPs Es E (qs u ω)
  have hw : fp81s21_MomentRep E P (fp81s21_wickChartField Es qs) qe M :=
    fp81s21_MomentRep_embedField_normalized hr hp hP hPs Es E P _ qs M hrep
  refine ⟨qe, (fun _ _ => rfl), hw, ?_, ?_, ?_⟩
  · intro u ω f hf
    exact fp81s21_embedField_normalized_action hr hp hP hPs Es E (qs u ω) f hf
  · intro u ω
    exact fp81s21_chartAction_S102Z E (qe u ω)
  · intro a ha H hH
    obtain ⟨U, hU⟩ := fp81s21_MomentRep_time_section E P _ qe M a H hw ha hH
    refine ⟨U, hU, ?_⟩
    apply fp81s21_TimeRep_of_TimeL2Rep_product hP E P _ qe M a H U hU
    · exact Filter.Eventually.of_forall (fun _ _ _ => rfl)
    · exact Filter.Eventually.of_forall (fun z => fp81s21_chartAction_S102Z E (qe (a + z.1) z.2))

/-- Physical half-Wick coefficients admit their canonical weak extension and
weighted time sections, with the same second-moment constant. -/
theorem fp81s21_wick_TimeRep_physical (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
      ∀ Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4),
      ∀ E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2),
      ∃ Kstar B : ℝ, 0 ≤ Kstar ∧ 0 ≤ B ∧ ∀ G : GaussianRealization R,
      ∃ T : ℝ → Lp ℝ 2 (HRS.Whole.withDensityReal R.ρβ) →L[ℝ] Lp ℝ 2 G.P,
      ∃ W : ℝ → Lp ℝ 2 ((HRS.Whole.withDensityReal R.ρβ).prod
        (HRS.Whole.withDensityReal R.ρβ)) →L[ℝ] Lp ℝ 2 G.P,
      ∃ qs qe : ℝ → G.Ω → r26t6_Coeff,
        (∀ u : ℝ, 0 ≤ u → ∃ hL : ‖T u‖ ≤ Kstar,
          ∃ hJoint : ∀ n (v : Fin n → Lp ℝ 2 (HRS.Whole.withDensityReal R.ρβ)),
            HRS.IsCenteredGaussian (G.P.map fun ω => fun i => (T u (v i)) ω),
            W u = fp81s21_wickFam_operator R G (T u) Kstar hL hJoint) ∧
        (∀ u : ℝ, 0 ≤ u → ∀ φ : Euc p.d → ℝ,
          IsOscTest (wholeSpaceIndex p.d : ℝ) φ →
          ∀ hφ : MemLp φ 2 (HRS.Whole.withDensityReal R.ρβ),
          (T u (hφ.toLp φ) : G.Ω → ℝ) =ᵐ[G.P]
            fun ω => OscDual.eval (G.Z u ω) φ) ∧
        (∀ u ω, qe u ω = fp81s21_gaussian_chartEmbed p Es E (qs u ω)) ∧
        fp81s21_MomentRep Es G.P (fp81s21_wickChartField Es qs) qs
          (Kstar ^ 4 * B / 2) ∧
        fp81s21_MomentRep E G.P (fp81s21_wickChartField Es qs) qe
          (Kstar ^ 4 * B / 2) ∧
        (∀ u ω f, IsR2Test f → fp81s21_chartAction E (qe u ω) f =
          fp81s21_wickChartField Es qs u ω f) ∧
        (∀ u ω, S102Z (2 * p.d + 8) ((p.d : ℝ) + 2)
          (fp81s21_chartAction E (qe u ω))) ∧
        (∀ u : ℝ, 0 ≤ u → ∀ f : Euc p.d → ℝ, IsR2Test f →
          ∃ hker : MemLp (fun xy : Euc p.d × Euc p.d =>
            commutatorKernel p.d p.s (gradient f) xy.1 xy.2) 2
            ((HRS.Whole.withDensityReal R.ρβ).prod (HRS.Whole.withDensityReal R.ρβ)),
          (fun ω => fp81s21_wickChartField Es qs u ω f) =ᵐ[G.P]
            (W u (hker.toLp (fun xy : Euc p.d × Euc p.d =>
              commutatorKernel p.d p.s (gradient f) xy.1 xy.2)) : G.Ω → ℝ)) ∧
        ∀ a : ℝ, 0 ≤ a → ∀ H : ℝ, 0 ≤ H →
          ∃ U : G.Ω → Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H)),
            fp81s21_TimeL2Rep G.P qe (Kstar ^ 4 * B / 2) a H U ∧
            fp81s21_TimeRep E G.P (fun u ω => fp81s21_chartAction E (qe u ω))
              qe (Kstar ^ 4 * B / 2) a H U := by
  obtain ⟨δ0, hδ0, hhalf, hphys⟩ := fp81s21_wick_momentRep_physical p
  refine ⟨δ0, hδ0, hhalf, ?_⟩
  intro δ hδ hδle R Es E
  obtain ⟨K, B, hK, hB, hG⟩ := hphys δ hδ hδle R Es E
  refine ⟨K, B, hK, hB, ?_⟩
  intro G
  obtain ⟨T, W, qs, hW, hT, hs, _, hag, _⟩ := hG G
  obtain ⟨qe, hqe, hw, hc, hz, ht⟩ :=
    fp81s21_wick_weak_TimeRep (by omega) (by ring) (by nlinarith) (by nlinarith)
      Es E G.P qs (K ^ 4 * B / 2) hs
  refine ⟨T, W, qs, qe, hW, hT, ?_, hs, hw, hc, hz, hag, ht⟩
  simpa [fp81s21_gaussian_chartEmbed] using hqe

#print axioms fp81s21_embedField_normalized_action
#print axioms fp81s21_wick_weak_TimeRep
#print axioms fp81s21_wick_TimeRep_physical
end HRS.Fp81.S21
end
