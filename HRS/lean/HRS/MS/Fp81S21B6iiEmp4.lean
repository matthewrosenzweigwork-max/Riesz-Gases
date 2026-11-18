import HRS.MS.Fp81S21B6iiEmp3

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory Filter
open scoped ENNReal RealInnerProductSpace
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.ProClosureS111

private theorem fp81s21_b6ii_six_normalized
    {d r r' : ℕ} {Pw Ps : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    (hr : r + 2 = r') (hp : Pw + 2 = Ps)
    (hP : (d : ℝ) < 2 * Pw) (hPs : (d : ℝ) < 2 * Ps)
    (Es : r26t6_WeightedChart d r Ps) (E : r26t6_WeightedChart d r' Pw)
    (P : Measure Ω) (qs : ℝ → Ω → r26t6_Coeff) (M : ℝ)
    (hs : fp81s21_Six P qs M) :
    fp81s21_Six P (fun u ω => fp81s21_embedField_normalized hr hp hP hPs Es E (qs u ω)) M := by
  subst r'
  subst Ps
  exact fp81s21_Six_embedField hP hPs Es E P qs M hs

/-- The three-field producer with common-time compact-test agreement for its
empirical witness and its embedded image. -/
theorem fp81s21_particleCoeffMoments_embedded_common (p : Parameters)
    (Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4)) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
        ∃ M2 M6 : ℝ, 0 ≤ M2 ∧ 0 ≤ M6 ∧
          ∀ E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2),
          ∀ N : ℕ, 2 ≤ N → ∀ A : Particle R N,
            ∀ Q ∈ ({fp81s21_particleEmpField R N A,
              fp81s21_particleQuadRawField R N A,
              fp81s21_particleQuadField R N A} :
              Set (ℝ → A.Ω → (Euc p.d → ℝ) → ℝ)),
              ∃ qs : ℝ → A.Ω → r26t6_Coeff,
                fp81s21_MomentRep Es A.P Q qs M2 ∧
                fp81s21_Six A.P qs M6 ∧
                fp81s21_MomentRep E A.P Q
                  (fun u ω => fp81s21_gaussian_chartEmbed p Es E (qs u ω)) M2 ∧
                fp81s21_Six A.P
                  (fun u ω => fp81s21_gaussian_chartEmbed p Es E (qs u ω)) M6 ∧
                (∀ u, 0 ≤ u →
                  AEMeasurable (fun ω => HRS.Whole.dualNormE
                    (2 * p.d + 8) ((p.d : ℝ) + 2) (Q u ω)) A.P ∧
                  (∫⁻ ω, HRS.Whole.dualNormE
                    (2 * p.d + 8) ((p.d : ℝ) + 2) (Q u ω) ∂A.P) ≤
                    ENNReal.ofReal (Real.sqrt M2)) ∧
                (Q = fp81s21_particleEmpField R N A →
                  (∀ᵐ ω ∂A.P, ∀ u : ℝ, 0 ≤ u → ∀ f : Euc p.d → ℝ,
                    IsR2Test f → fp81s21_chartAction Es (qs u ω) f = Q u ω f) ∧
                  (∀ᵐ ω ∂A.P, ∀ u : ℝ, 0 ≤ u → ∀ f : Euc p.d → ℝ,
                    IsR2Test f → fp81s21_chartAction E
                      (fp81s21_gaussian_chartEmbed p Es E (qs u ω)) f = Q u ω f)) := by
  obtain ⟨δa, hδa, hδah, ha⟩ := fp81s21_particleCoeffMoments_embedded p Es
  obtain ⟨δb, hδb, hδbh, hb⟩ := fp81s21_emp_reference_data p Es
  refine ⟨min δa δb, lt_min hδa hδb, (min_le_left _ _).trans hδah, ?_⟩
  intro δ hδ hδle R
  obtain ⟨M2, M6, hM2, hM6, hprod⟩ := ha δ hδ (hδle.trans (min_le_left _ _)) R
  obtain ⟨μ, hμ, hi, hm⟩ := hb δ hδ (hδle.trans (min_le_right _ _)) R
  refine ⟨M2, M6, hM2, hM6, ?_⟩
  intro E N hN A Q hQ
  obtain ⟨qold, hrep, hsix, hweak, hweak6, hfirst⟩ := hprod E N hN A Q hQ
  by_cases hQemp : Q = fp81s21_particleEmpField R N A
  · subst Q
    obtain ⟨qs, hrep', hsix', hweak', hweak6', hcommon, hcommonE⟩ :=
      fp81s21_emp_common_time_transfer p R N hN A Es E μ hμ hi hm qold M2 M6 hrep hsix
    exact ⟨qs, hrep', hsix', hweak', hweak6', hfirst, fun _ => ⟨hcommon, hcommonE⟩⟩
  · refine ⟨qold, hrep, hsix, ?_, ?_, hfirst, ?_⟩
    · simpa [fp81s21_gaussian_chartEmbed] using
        fp81s21_MomentRep_embedField_normalized (by omega) (by ring)
          (by nlinarith [p.hd]) (by nlinarith [p.hd]) Es E A.P Q qold M2 hrep
    · simpa [fp81s21_gaussian_chartEmbed] using
        fp81s21_b6ii_six_normalized (by omega) (by ring)
          (by nlinarith [p.hd]) (by nlinarith [p.hd]) Es E A.P qold M6 hsix
    · intro heq
      exact (hQemp heq).elim

#print axioms fp81s21_particleCoeffMoments_embedded_common
end HRS.Fp81.S21
end
