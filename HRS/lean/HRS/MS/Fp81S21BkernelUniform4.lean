import HRS.MS.Fp81S21BkernelUniform3
import HRS.MS.Fp81S21FRUniform4

open MeasureTheory
open scoped BigOperators

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
noncomputable section

namespace HRS.Fp81.S21

open HRS (Euc)
open HRS.Whole
open HRS.MS.R26T3

/-- The bounded-test qwin Bkernel limit, with the compatible corrector family
and uniform finite-rank rates supplied by the staged constructions. -/
theorem fp81s21_initial_Bkernel_uniform_qwin_bd4 (p : Parameters)
    (hγ : 0 < p.γ) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
        ∀ E : InitialSteinEnv R,
          ∃ K C c : ℝ, 0 ≤ K ∧ 0 ≤ C ∧ 0 < c ∧
            ∃ F : fp81s21_CompatPotentialFamily R,
              (∀ a : Set.Ici (0 : ℝ), (F a).K ≤ K) ∧
              (∀ a : Set.Ici (0 : ℝ), ∀ j : ℕ,
                HasCbBound (fp81s21_k0 p.d)
                  (C * Real.exp (-c * (a : ℝ)) * r26t3_feature_weight p.d j)
                  (gradient ((F a).χ j))) ∧
              ∀ M : ℝ, 0 ≤ M → ∀ j : ℕ, ∀ ε : ℝ, 0 < ε →
                ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → 2 ≤ N →
                  ∀ a : ℝ, ∀ (ha : a ∈ Set.Icc (0 : ℝ) M),
                    ∀ {G : Measure SeqL2} [IsProbabilityMeasure G],
                      IsCenteredGaussianSeq G
                        (fun l q => HRS.Whole.susceptibilityCov
                          (rieszKernel p.d p.s) (r26t3_mu R 0) p.γ
                          (r26t3_qwin R a l) (r26t3_qwin R a q)) →
                      ∀ f : SeqL2 → ℝ, S99.Bd 4 f →
                        |fp81s21_initial_Bterm R (r26t3_qwin R a) N
                            (fun x y => commutatorKernel p.d p.s
                              (gradient ((F ⟨a, ha.1⟩).χ j)) x y) f -
                          fp81s21_initial_Blimit R (r26t3_qwin R a) G f
                            (fun x y => commutatorKernel p.d p.s
                              (gradient ((F ⟨a, ha.1⟩).χ j)) x y)| ≤ ε := by
  obtain ⟨δc, hδc, hδch, hcompat⟩ :=
    fp81s21_compatible_qwin_potentials p hγ
  obtain ⟨δfr, hδfr, hδfrh, hfrunif⟩ :=
    fp81s21_initial_FR_uniform_qwin p hγ
  obtain ⟨δq, hδq, hδqh, hqwin⟩ := fp81s21_qwin_uniform p
  obtain ⟨δs, hδs, hδsh, hfeatureSum⟩ :=
    fp81s21_qwin_featureSum_uniform p
  let δ0 : ℝ := min δc (min δfr (min δq δs))
  have hδ0 : 0 < δ0 := lt_min hδc (lt_min hδfr (lt_min hδq hδs))
  have hδ0h : δ0 ≤ 1 / 2 :=
    (min_le_left δc _).trans hδch
  refine ⟨δ0, hδ0, hδ0h, fun δ hδ hδle R E => ?_⟩
  have hδcR : δ ≤ δc := hδle.trans (min_le_left δc _)
  have hδfrR : δ ≤ δfr :=
    hδle.trans ((min_le_right δc _).trans (min_le_left δfr _))
  have hδqR : δ ≤ δq :=
    hδle.trans ((min_le_right δc _).trans
      ((min_le_right δfr _).trans (min_le_left δq δs)))
  have hδsR : δ ≤ δs :=
    hδle.trans ((min_le_right δc _).trans
      ((min_le_right δfr _).trans (min_le_right δq δs)))
  obtain ⟨K, C, c, hK, hC, hc, F, hFK, hdecay⟩ :=
    hcompat δ hδ hδcR R
  obtain ⟨Cq, hCq, hq⟩ := hqwin δ hδ hδqR R
  obtain ⟨Cs, hCs, hfsum⟩ := hfeatureSum δ hδ hδsR R
  let S : ℝ := Cs * (∑' j : ℕ, r26t3_feature_weight p.d j)
  have hweight0 : ∀ j, 0 ≤ r26t3_feature_weight p.d j := by
    intro j
    dsimp [r26t3_feature_weight]
    apply mul_nonneg
    · apply Real.rpow_nonneg
      positivity
    · exact Real.rpow_nonneg (oscEigenvalue_pos _).le _
  have hS : 0 ≤ S := by
    dsimp [S]
    exact mul_nonneg hCs (tsum_nonneg hweight0)
  have hJd : r26t3_J p.d = fp81s21_J1 p.d := rfl
  have hphi : ∀ a : Set.Ici (0 : ℝ),
      IsSummableFeatureFamily (fp81s21_J1 p.d) (r26t3_qwin R (a : ℝ)) := by
    intro a
    have hh := (hq a.1 a.2).1
    simpa [hJd] using hh
  have hSum : ∀ a : Set.Ici (0 : ℝ),
      featureSum (fp81s21_J1 p.d) (r26t3_qwin R (a : ℝ)) ≤ S := by
    intro a
    have hh := hfsum a.1 a.2
    simpa [hJd, S] using hh
  have hFR : ∀ D : fp81s21_RankKernel p.d,
      ∃ KFR : ℝ, 0 ≤ KFR ∧
        ∀ a : Set.Ici (0 : ℝ),
          ∀ {G : Measure SeqL2} [IsProbabilityMeasure G],
            IsCenteredGaussianSeq G
              (fun l q => HRS.Whole.susceptibilityCov
                (rieszKernel p.d p.s) (r26t3_mu R 0) p.γ
                (r26t3_qwin R (a : ℝ) l)
                (r26t3_qwin R (a : ℝ) q)) →
            ∀ N : ℕ, 2 ≤ N → ∀ ψ : SeqL2 → ℝ, S99.Bd 4 ψ →
              |fp81s21_initial_Bterm R (r26t3_qwin R (a : ℝ)) N D.kernel ψ -
                fp81s21_initial_Blimit R (r26t3_qwin R (a : ℝ)) G ψ D.kernel|
                  ≤ KFR / Real.sqrt N := by
    intro D
    obtain ⟨KFR, hKFR, hRate⟩ :=
      hfrunif δ hδ hδfrR R E F D
    refine ⟨KFR, hKFR, fun a G _ hG N hN ψ hψ => ?_⟩
    simpa [fp81s21_initial_Blimit] using hRate a hG N hN ψ hψ
  refine ⟨K, C, c, hK, hC, hc, F, hFK, hdecay, ?_⟩
  intro M hM j ε hε
  exact fp81s21_initial_Bkernel_uniform_qwin_bd4_of_FR hδ
    (hδle.trans hδ0h) R E hγ F hK hC hc.le hFK hdecay S hS hphi hSum hFR
    M hM j ε hε

#print axioms fp81s21_initial_Bkernel_uniform_qwin_bd4

end HRS.Fp81.S21

end
