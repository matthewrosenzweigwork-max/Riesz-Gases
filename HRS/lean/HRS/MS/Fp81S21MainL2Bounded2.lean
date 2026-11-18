import HRS.MS.Fp81S21MainL2Bounded

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
noncomputable section

namespace HRS.Fp81.S21

open S45 S99
open HRS.Whole
open HRS (Euc MemCb cbNorm)
open HRS.MS.R26T3

/-- The actual initial-law Edgeworth expansion is uniform over bounded qwin shifts.
The one particle cutoff is selected before the shift, Gaussian, and C⁵ test. -/
theorem fp81s21_initial_main_l2_bounded_shift (p : Parameters)
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
                  (gradient ((F a).χ j)) ) ∧
              ∀ M : ℝ, 0 ≤ M → ∀ ε : ℝ, 0 < ε →
                ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → 2 ≤ N →
                  ∀ a : ℝ, ∀ ha : a ∈ Set.Icc (0 : ℝ) M,
                    ∀ {G : Measure SeqL2} [IsProbabilityMeasure G],
                      IsCenteredGaussianSeq G (fun i j =>
                        HRS.Whole.susceptibilityCov (rieszKernel p.d p.s)
                          (r26t3_mu R 0) p.γ
                          (r26t3_qwin R a i) (r26t3_qwin R a j)) →
                      ∀ Φ : SeqL2 → ℝ, ContDiff ℝ 5 Φ →
                        (∀ i : ℕ, i ≤ 5 → ∀ z, ‖iteratedFDeriv ℝ i Φ z‖ ≤ 1) →
                        |Real.sqrt N *
                            ((∫ X, Φ (featureVec (r26t3_qwin R a)
                                (r26t3_marg R N) X) ∂(r26t3_Q R N)) -
                              ∫ z, Φ z ∂G) -
                          (1 / 6) * ∫ z, ∫ x,
                            iteratedFDeriv ℝ 3 Φ z
                              ![fp81s21_initial_ellv R (r26t3_qwin R a) x,
                                fp81s21_initial_ellv R (r26t3_qwin R a) x,
                                fp81s21_initial_ellv R (r26t3_qwin R a) x]
                            ∂(r26t3_mu R 0) ∂G| ≤ ε := by
  obtain ⟨δB, hδB, hδBh, hB⟩ :=
    fp81s21_initial_ULimB_uniform_qwin p hγ
  obtain ⟨δq, hδq, hδqh, hqwin⟩ := fp81s21_qwin_uniform p
  obtain ⟨δs, hδs, hδsh, hfeatureSum⟩ :=
    fp81s21_qwin_featureSum_uniform p
  let δ0 : ℝ := min δB (min δq δs)
  have hδ0 : 0 < δ0 := lt_min hδB (lt_min hδq hδs)
  have hδ0h : δ0 ≤ 1 / 2 :=
    (min_le_left δB (min δq δs)).trans hδBh
  refine ⟨δ0, hδ0, hδ0h, fun δ hδ hδle R E => ?_⟩
  have hδB' : δ ≤ δB := hδle.trans (min_le_left δB (min δq δs))
  have hδq' : δ ≤ δq :=
    hδle.trans ((min_le_right δB (min δq δs)).trans (min_le_left δq δs))
  have hδs' : δ ≤ δs :=
    hδle.trans ((min_le_right δB (min δq δs)).trans (min_le_right δq δs))
  obtain ⟨K, C, c, hK, hC, hc, F, hFK, hdecay, hBuniform⟩ :=
    hB δ hδ hδB' R E
  obtain ⟨Cwin, hCwin, hq⟩ := hqwin δ hδ hδq' R
  obtain ⟨Cs, hCs, hfsum⟩ := hfeatureSum δ hδ hδs' R
  have hJd : r26t3_J p.d = fp81s21_J1 p.d := rfl
  have hq' : ∀ a : ℝ, 0 ≤ a →
      IsSummableFeatureFamily (fp81s21_J1 p.d) (r26t3_qwin R a) ∧
      ∀ j, cbNorm (fp81s21_J1 p.d) (r26t3_qwin R a j) ≤
        Cwin * r26t3_feature_weight p.d j := by
    intro a ha
    obtain ⟨hphi, hbound⟩ := hq a ha
    refine ⟨?_, ?_⟩
    · simpa [hJd] using hphi
    · intro j
      simpa [hJd] using hbound j
  let S : ℝ := Cs * (∑' j : ℕ, r26t3_feature_weight p.d j)
  have hweight0 : ∀ j, 0 ≤ r26t3_feature_weight p.d j := by
    intro j
    dsimp [r26t3_feature_weight]
    apply mul_nonneg
    · apply Real.rpow_nonneg
      positivity
    · exact Real.rpow_nonneg (oscEigenvalue_pos _).le _
  have hS0 : 0 ≤ S := by
    dsimp [S]
    exact mul_nonneg hCs (tsum_nonneg hweight0)
  refine ⟨K, C, c, hK, hC, hc, F, hFK, hdecay, ?_⟩
  intro M hM ε hε
  have hphi : ∀ a : Set.Icc (0 : ℝ) M, IsSummableFeatureFamily
      (fp81s21_J1 p.d) (r26t3_qwin R (a : ℝ)) := by
    intro a
    exact (hq' a.1 a.2.1).1
  have hbound : ∀ a : Set.Icc (0 : ℝ) M, ∀ j : ℕ,
      cbNorm (fp81s21_J1 p.d) (r26t3_qwin R (a : ℝ) j) ≤
        Cwin * r26t3_feature_weight p.d j := by
    intro a j
    exact (hq' a.1 a.2.1).2 j
  have hSum : ∀ a : Set.Icc (0 : ℝ) M,
      featureSum (fp81s21_J1 p.d) (r26t3_qwin R (a : ℝ)) ≤ S := by
    intro a
    have hh := hfsum a.1 a.2.1
    simpa [hJd, S] using hh
  obtain ⟨NA, hA⟩ := fp81s21_initial_Aseries_uniform_qwin
    hδ (hδle.trans hδ0h) R E hγ F hK hFK hCwin hS0 M hM
    hphi hbound hSum (ε / 2) (by linarith)
  obtain ⟨NB, hNB⟩ := hBuniform M hM (ε / 2) (by linarith)
  let N0 : ℕ := max NA NB
  refine ⟨N0, ?_⟩
  intro N hN0 hN2 a ha G _ hG Φ hΦ hb
  let aI : Set.Icc (0 : ℝ) M := ⟨a, ha⟩
  let a0 : Set.Ici (0 : ℝ) := ⟨a, ha.1⟩
  obtain ⟨f, hf, hst, hthird⟩ :=
    fp81s21_initial_stein_package R hG hΦ hb
  have hAerr := hA N (le_trans (le_max_left NA NB) hN0) hN2 a ha
    (G := G) hG f hf
  have hBerr := hNB N (le_trans (le_max_right NA NB) hN0) hN2 a ha
    (G := G) hG f hf
  have hAerr' :
      |(∑' q : ℕ × ℕ, fp81s21_initial_Aterm (F a0) N f q) -
        (∑' q : ℕ × ℕ, fp81s21_initial_Alim (F a0) G f q)| ≤ ε / 2 := by
    simpa [a0, aI] using hAerr
  have hBerr' :
      |(∑' j, fp81s21_initial_Bterm R (r26t3_qwin R a) N
          (commutatorKernel p.d p.s (gradient ((F a0).χ j))) (S99.pd f j)) -
        (∑' j, fp81s21_initial_Blimit R (r26t3_qwin R a) G (S99.pd f j)
          (commutatorKernel p.d p.s (gradient ((F a0).χ j))))| ≤ ε / 2 := by
    simpa [a0, aI] using hBerr
  have hΦb : ∀ z, |Φ z| ≤ 1 := fun z => by
    have h := hb 0 (by norm_num) z
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h
  have hL := fp81s21_initial_D1_scaled E hγ (hphi aI) (F a0) hG
    hΦ.continuous hΦb hf hst hN2
  have hΦ3 : ContDiff ℝ 3 Φ := hΦ.of_le (by norm_num)
  have hser := fp81s21_initial_third_series hδ (hδle.trans hδ0h) R E hγ
    (hphi aI) (F a0) (G := G) hΦ3 (hb 3 (by norm_num))
  have hthirdT : ∀ j k m,
      ∫ z, iteratedFDeriv ℝ 3 Φ z
          ![s45_e1 m (1 : ℝ), s45_e1 k (1 : ℝ), s45_e1 j (1 : ℝ)] ∂G =
        -3 * S99.T3 G f j k m := by
    intro j k m
    let v : Fin 3 → SeqL2 :=
      ![s45_e1 m (1 : ℝ), s45_e1 k (1 : ℝ), s45_e1 j (1 : ℝ)]
    have h3 := hthird v
    have h2 :
        ∫ z, iteratedFDeriv ℝ 3 f z
            ![s45_e1 m (1 : ℝ), s45_e1 k (1 : ℝ), s45_e1 j (1 : ℝ)] ∂G =
          S99.T3 G f j k m := by
      unfold S99.T3
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      exact s99_third_apply (hf.1.of_le (by norm_num)) z j k m
    rw [h2] at h3
    exact h3
  have hlim := fp81s21_initial_limit_ident (G := G)
    hδ (hδle.trans hδ0h) R E hγ (hphi aI) (F a0) hf
  have hR :
      (1 / 6) * ∫ z, ∫ x,
          iteratedFDeriv ℝ 3 Φ z
            ![fp81s21_initial_ellv R (r26t3_qwin R a) x,
              fp81s21_initial_ellv R (r26t3_qwin R a) x,
              fp81s21_initial_ellv R (r26t3_qwin R a) x]
            ∂(r26t3_mu R 0) ∂G =
        (∑' q : ℕ × ℕ, fp81s21_initial_Alim (F a0) G f q) +
          (∑' j, (1 / 2) * ∑' l, ∑' q,
            fp81s21_initial_Qk R (r26t3_qwin R a)
              (commutatorKernel p.d p.s (gradient ((F a0).χ j))) l q *
              ∫ z, S99.pd (S99.pd (S99.pd f j) l) q z ∂G) := by
    rw [hser]
    have hT3pd : ∀ j l q,
        (∫ z, S99.pd (S99.pd (S99.pd f j) l) q z ∂G) =
          S99.T3 G f j l q := fun _ _ _ => rfl
    simp_rw [hT3pd]
    rw [hlim]
    simp_rw [hthirdT]
    have hmul : ∀ j k m : ℕ,
        fp81s21_initial_kap3 R (r26t3_qwin R (aI : ℝ)) j k m *
            (-3 * S99.T3 G f j k m) =
          -3 * (fp81s21_initial_kap3 R (r26t3_qwin R (aI : ℝ)) j k m *
            S99.T3 G f j k m) := fun j k m => by ring
    simp_rw [hmul, tsum_mul_left]
    ring
  rw [hL, hR]
  have hdecomp :
      ((∑' q : ℕ × ℕ, fp81s21_initial_Aterm (F a0) N f q) +
        ∑' j, fp81s21_initial_Bterm R (r26t3_qwin R a) N
          (commutatorKernel p.d p.s (gradient ((F a0).χ j))) (S99.pd f j)) -
      ((∑' q : ℕ × ℕ, fp81s21_initial_Alim (F a0) G f q) +
        ∑' j, fp81s21_initial_Blimit R (r26t3_qwin R a) G (S99.pd f j)
          (commutatorKernel p.d p.s (gradient ((F a0).χ j)))) =
      ((∑' q : ℕ × ℕ, fp81s21_initial_Aterm (F a0) N f q) -
        ∑' q : ℕ × ℕ, fp81s21_initial_Alim (F a0) G f q) +
      ((∑' j, fp81s21_initial_Bterm R (r26t3_qwin R a) N
          (commutatorKernel p.d p.s (gradient ((F a0).χ j))) (S99.pd f j)) -
        ∑' j, fp81s21_initial_Blimit R (r26t3_qwin R a) G (S99.pd f j)
          (commutatorKernel p.d p.s (gradient ((F a0).χ j)))) := by
    ring
  change |((∑' q : ℕ × ℕ, fp81s21_initial_Aterm (F a0) N f q) +
      ∑' j, fp81s21_initial_Bterm R (r26t3_qwin R a) N
        (commutatorKernel p.d p.s (gradient ((F a0).χ j))) (S99.pd f j)) -
    ((∑' q : ℕ × ℕ, fp81s21_initial_Alim (F a0) G f q) +
      ∑' j, fp81s21_initial_Blimit R (r26t3_qwin R a) G (S99.pd f j)
        (commutatorKernel p.d p.s (gradient ((F a0).χ j))))| ≤ ε
  rw [hdecomp]
  calc
    |((∑' q : ℕ × ℕ, fp81s21_initial_Aterm (F a0) N f q) -
        ∑' q : ℕ × ℕ, fp81s21_initial_Alim (F a0) G f q) +
      ((∑' j, fp81s21_initial_Bterm R (r26t3_qwin R a) N
          (commutatorKernel p.d p.s (gradient ((F a0).χ j))) (S99.pd f j)) -
        ∑' j, fp81s21_initial_Blimit R (r26t3_qwin R a) G (S99.pd f j)
          (commutatorKernel p.d p.s (gradient ((F a0).χ j))))| ≤
        |(∑' q : ℕ × ℕ, fp81s21_initial_Aterm (F a0) N f q) -
          ∑' q : ℕ × ℕ, fp81s21_initial_Alim (F a0) G f q| +
        |(∑' j, fp81s21_initial_Bterm R (r26t3_qwin R a) N
            (commutatorKernel p.d p.s (gradient ((F a0).χ j))) (S99.pd f j)) -
          ∑' j, fp81s21_initial_Blimit R (r26t3_qwin R a) G (S99.pd f j)
            (commutatorKernel p.d p.s (gradient ((F a0).χ j)))| := abs_add_le _ _
    _ ≤ ε / 2 + ε / 2 := add_le_add hAerr' hBerr'
    _ = ε := by ring

#print axioms fp81s21_initial_main_l2_bounded_shift

end HRS.Fp81.S21

end
