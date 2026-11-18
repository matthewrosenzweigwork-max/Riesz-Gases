import HRS.MS.Fp81S21RespIid2
import HRS.MS.S21H2_S09

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Filter Topology Set
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.S21 HRS.MS.S21E HRS.MC.E213O

/-- The endpoint synthesized cubic response tensor is the initial-window
tensor under the actual one-particle law. -/
theorem fp81s21_respIid_initialKappa (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ, p.γ = 0 →
        ∀ a : ℝ, 0 ≤ a → ∀ [IsProbabilityMeasure (r26t3_mu R 0)],
          tensorPow' 3
            (s21gPhi (r26t3_feature_enum p.d) p.hT
              ((wholeSpaceIndex p.d : ℕ) : ℝ))
            (s21eKappa0 (r26t3_mu R 0)
              (fp81s21_initial_ellv R (r26t3_qwin R a))) =
                initialKappa R a := by
  obtain ⟨δp, hp, hphalf, hpath⟩ := fp81s21_respIid_path p
  obtain ⟨δq, hq, hqhalf, hqwin⟩ := fp81s21_qwin_uniform p
  refine ⟨min δp δq, lt_min hp hq, (min_le_left _ _).trans hphalf,
    fun δ hδ hδle R hγ a ha hprob => ?_⟩
  have hδh := hδle.trans ((min_le_left δp δq).trans hphalf)
  obtain ⟨_, _, hfamily⟩ := hqwin δ hδ (hδle.trans (min_le_right _ _)) R
  have hreg := fp81s21_respIid_vector_regular hδ hδh R hγ a ha
    ((hfamily a ha).1)
  haveI hμ : IsProbabilityMeasure (r26t3_mu R 0) := hprob
  let S : SeqL2 →L[ℝ] Window p :=
    s21gPhi (r26t3_feature_enum p.d) p.hT
      ((wholeSpaceIndex p.d : ℕ) : ℝ)
  rw [fp81s21_respRecon_tensor_map (r26t3_mu R 0) S _
    hreg.1.aestronglyMeasurable hreg.2]
  change s21eKappa0 (r26t3_mu R 0) (fun x =>
      S (fp81s21_initial_ellv R (r26t3_qwin R a) x)) =
    s21eKappa0 (r26t3_mu R 0) (responseWindow R a)
  congr 1
  funext x
  exact hpath δ hδ (hδle.trans (min_le_left _ _)) R hγ a ha x

/-- The positive and zero-strength response path identities hold below one
common producer radius. -/
theorem fp81s21_respIid_path_common (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
        (0 < p.γ ∨ p.γ = 0) → ∀ a : ℝ, 0 ≤ a → ∀ x : Euc p.d,
          s21gPhi (r26t3_feature_enum p.d) p.hT
            ((wholeSpaceIndex p.d : ℕ) : ℝ)
            (fp81s21_initial_ellv R (r26t3_qwin R a) x) =
              responseWindow R a x := by
  obtain ⟨δp, hp, hphalf, hpath⟩ := fp81s21_respRecon_path p
  obtain ⟨δz, hz, hzhalf, hzpath⟩ := fp81s21_respIid_path p
  refine ⟨min δp δz, lt_min hp hz, (min_le_left _ _).trans hphalf,
    fun δ hδ hδle R hγ a ha x => ?_⟩
  rcases hγ with hγ | hγ
  · exact hpath δ hδ (hδle.trans (min_le_left δp δz)) R hγ a ha x
  · exact hzpath δ hδ (hδle.trans (min_le_right δp δz)) R hγ a ha x

/-- The positive and zero-strength initial-kappa identities hold below one
common producer radius. -/
theorem fp81s21_respIid_initialKappa_common (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
        (0 < p.γ ∨ p.γ = 0) → ∀ a : ℝ, 0 ≤ a →
          ∀ [IsProbabilityMeasure (r26t3_mu R 0)],
            tensorPow' 3
              (s21gPhi (r26t3_feature_enum p.d) p.hT
                ((wholeSpaceIndex p.d : ℕ) : ℝ))
              (s21eKappa0 (r26t3_mu R 0)
                (fp81s21_initial_ellv R (r26t3_qwin R a))) =
                  initialKappa R a := by
  obtain ⟨δp, hp, hphalf, hpositive⟩ :=
    fp81s21_respRecon_initialKappa p
  obtain ⟨δz, hz, hzhalf, hzero⟩ := fp81s21_respIid_initialKappa p
  refine ⟨min δp δz, lt_min hp hz, (min_le_left _ _).trans hphalf,
    fun δ hδ hδle R hγ a ha hμ => ?_⟩
  rcases hγ with hγ | hγ
  · exact hpositive δ hδ (hδle.trans (min_le_left δp δz)) R hγ a ha
  · exact hzero δ hδ (hδle.trans (min_le_right δp δz)) R hγ a ha

#print axioms fp81s21_respIid_initialKappa
#print axioms fp81s21_respIid_path_common
#print axioms fp81s21_respIid_initialKappa_common

end HRS.Fp81.S21
end
