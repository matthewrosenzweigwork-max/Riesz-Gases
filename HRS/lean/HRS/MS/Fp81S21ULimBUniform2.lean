import HRS.MS.Fp81S21ULimBUniform

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
noncomputable section

namespace HRS.Fp81.S21

open S99
open HRS.Whole
open HRS (Euc cbNorm)
open HRS.MS.R26T3

/-- Uniform qwin convergence of the actual-law quadratic coefficient series.
The common compatible family is fixed before the bounded shift interval,
particle cutoff, Gaussian law, or Stein solution. -/
theorem fp81s21_initial_ULimB_uniform_qwin (p : Parameters)
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
              ∀ M : ℝ, 0 ≤ M → ∀ ε : ℝ, 0 < ε →
                ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → 2 ≤ N →
                  ∀ a : ℝ, ∀ ha : a ∈ Set.Icc (0 : ℝ) M,
                    ∀ {G : Measure SeqL2} [IsProbabilityMeasure G],
                      IsCenteredGaussianSeq G
                        (fun l q => HRS.Whole.susceptibilityCov
                          (rieszKernel p.d p.s) (r26t3_mu R 0) p.γ
                          (r26t3_qwin R a l) (r26t3_qwin R a q)) →
                      ∀ f : SeqL2 → ℝ, S99.SteinCl f →
                        |(∑' j, fp81s21_initial_Bterm R
                              (r26t3_qwin R a) N
                              (fun x y => commutatorKernel p.d p.s
                                (gradient ((F ⟨a, ha.1⟩).χ j)) x y)
                              (S99.pd f j)) -
                          (∑' j, fp81s21_initial_Blimit R
                              (r26t3_qwin R a) G (S99.pd f j)
                              (fun x y => commutatorKernel p.d p.s
                                (gradient ((F ⟨a, ha.1⟩).χ j)) x y))| ≤ ε := by
  obtain ⟨δB, hδB, hδBh, hB⟩ :=
    fp81s21_initial_Bkernel_uniform_qwin_bd4 p hγ
  obtain ⟨δq, hδq, hδqh, hqwin⟩ := fp81s21_qwin_uniform p
  let δ0 : ℝ := min δB δq
  have hδ0 : 0 < δ0 := lt_min hδB hδq
  have hδ0h : δ0 ≤ 1 / 2 :=
    (min_le_left δB δq).trans hδBh
  refine ⟨δ0, hδ0, hδ0h, fun δ hδ hδle R E => ?_⟩
  have hδBR : δ ≤ δB := hδle.trans (min_le_left δB δq)
  have hδqR : δ ≤ δq := hδle.trans (min_le_right δB δq)
  obtain ⟨K, C, c, hK, hC, hc, F, hFK, hdecay, hBuniform⟩ :=
    hB δ hδ hδBR R E
  obtain ⟨Cwin, hCwin, hq⟩ := hqwin δ hδ hδqR R
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
  obtain ⟨KB, hKB, hBterm⟩ :=
    fp81s21_initial_Bterm_qwin_envelope hδ (hδle.trans hδ0h)
      R E hγ F hK hCwin hFK hq'
  let m : ℕ → ℝ := fun j =>
    (KB * (K * Cwin)) * r26t3_feature_weight p.d j
  have hmCoeff : 0 ≤ KB * (K * Cwin) := by positivity
  have hm0 : ∀ j, 0 ≤ m j := by
    intro j
    dsimp [m]
    apply mul_nonneg hmCoeff
    dsimp [r26t3_feature_weight]
    apply mul_nonneg
    · apply Real.rpow_nonneg
      positivity
    · exact Real.rpow_nonneg (oscEigenvalue_pos _).le _
  have hms : Summable m := by
    simpa [m] using
      (fp81s21_qwin_weight_summable p).mul_left (KB * (K * Cwin))
  refine ⟨K, C, c, hK, hC, hc, F, hFK, hdecay, ?_⟩
  intro M hM ε hε
  obtain ⟨k, htail⟩ : ∃ k : ℕ, ∑' j, m (j + k) < ε / 3 := by
    have htend := tendsto_sum_nat_add m
    have hevent := htend.eventually
      (gt_mem_nhds (show 0 < ε / 3 by positivity))
    obtain ⟨k, hk⟩ := hevent.exists
    exact ⟨k, hk⟩
  let τ : ℝ := ε / (3 * ((k : ℝ) + 1))
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hcoordinateCut : ∀ j : ℕ, ∃ Nj : ℕ,
      ∀ N : ℕ, Nj ≤ N → 2 ≤ N →
        ∀ a : ℝ, ∀ ha : a ∈ Set.Icc (0 : ℝ) M,
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
                    (gradient ((F ⟨a, ha.1⟩).χ j)) x y)| ≤ τ := by
    intro j
    exact hBuniform M hM j τ hτ
  choose Ns hNs using hcoordinateCut
  let N0 : ℕ := max 2 ((Finset.range k).sup Ns)
  refine ⟨N0, ?_⟩
  intro N hN0 hN2 a ha G _ hG f hf
  let uN : ℕ → ℕ → ℝ := fun N' j =>
    fp81s21_initial_Bterm R (r26t3_qwin R a) N'
      (fun x y => commutatorKernel p.d p.s
        (gradient ((F ⟨a, ha.1⟩).χ j)) x y) (S99.pd f j)
  let u : ℕ → ℝ := fun j => uN N j
  let v : ℕ → ℝ := fun j =>
    fp81s21_initial_Blimit R (r26t3_qwin R a) G (S99.pd f j)
      (fun x y => commutatorKernel p.d p.s
        (gradient ((F ⟨a, ha.1⟩).χ j)) x y)
  have hactual : ∀ N' : ℕ, 2 ≤ N' → ∀ j, |uN N' j| ≤ m j := by
    intro N' hN' j
    dsimp [uN, m]
    exact hBterm N' hN' a ha.1 j (S99.pd f j)
      (S99.SteinCl.pd hf j)
  have hlimit : ∀ j, |v j| ≤ m j := by
    intro j
    refine le_of_forall_pos_le_add fun η hη => ?_
    obtain ⟨Nη, hNη⟩ := hBuniform M hM j η hη
    let n : ℕ := max Nη 2
    have hNη' : Nη ≤ n := le_max_left _ _
    have hn2 : 2 ≤ n := le_max_right _ _
    have hconv := hNη n hNη' hn2 a ha (G := G) hG
      (S99.pd f j) (S99.SteinCl.pd hf j)
    have hact := hactual n hn2 j
    have htriangle : |v j| ≤ |uN n j - v j| + |uN n j| := by
      calc
        |v j| = |-(uN n j - v j) + uN n j| := by congr 1 <;> ring
        _ ≤ |-(uN n j - v j)| + |uN n j| := abs_add_le _ _
        _ = |uN n j - v j| + |uN n j| := by rw [abs_neg]
    have hconv' : |uN n j - v j| ≤ η := by
      simpa [uN, v] using hconv
    linarith
  have hu : ∀ j, |u j| ≤ m j := by
    intro j
    simpa [u] using hactual N hN2 j
  have hus : Summable u :=
    Summable.of_norm_bounded hms (fun j => by
      rw [Real.norm_eq_abs]
      exact hu j)
  have hvs : Summable v :=
    Summable.of_norm_bounded hms (fun j => by
      rw [Real.norm_eq_abs]
      exact hlimit j)
  have hhead : |∑ j ∈ Finset.range k, (u j - v j)| ≤ ε / 3 := by
    calc
      |∑ j ∈ Finset.range k, (u j - v j)| ≤
          ∑ j ∈ Finset.range k, |u j - v j| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ Finset.range k, τ :=
        Finset.sum_le_sum fun j hj => by
          have hcut : Ns j ≤ N :=
            (Finset.le_sup hj).trans ((le_max_right _ _).trans hN0)
          have ht := hNs j N hcut hN2 a ha (G := G) hG
            (S99.pd f j) (S99.SteinCl.pd hf j)
          simpa [u, v] using ht
      _ = (k : ℝ) * τ := by simp [τ]
      _ ≤ ε / 3 := by
        dsimp [τ]
        rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
  have htailU : |∑' j, u (j + k)| ≤ ∑' j, m (j + k) := by
    have hsum : HasSum (fun j => m (j + k)) (∑' j, m (j + k)) :=
      (hms.comp_injective (add_left_injective k)).hasSum
    have hbound := tsum_of_norm_bounded (f := fun j => u (j + k))
      hsum (fun j => by
        rw [Real.norm_eq_abs]
        exact hu (j + k))
    rw [Real.norm_eq_abs] at hbound
    exact hbound
  have htailV : |∑' j, v (j + k)| ≤ ∑' j, m (j + k) := by
    have hsum : HasSum (fun j => m (j + k)) (∑' j, m (j + k)) :=
      (hms.comp_injective (add_left_injective k)).hasSum
    have hbound := tsum_of_norm_bounded (f := fun j => v (j + k))
      hsum (fun j => by
        rw [Real.norm_eq_abs]
        exact hlimit (j + k))
    rw [Real.norm_eq_abs] at hbound
    exact hbound
  have hsplit :
      (∑ j ∈ Finset.range k, u j + ∑' j, u (j + k)) -
          (∑ j ∈ Finset.range k, v j + ∑' j, v (j + k)) =
        (∑ j ∈ Finset.range k, (u j - v j)) +
          ((∑' j, u (j + k)) - (∑' j, v (j + k))) := by
    rw [Finset.sum_sub_distrib]
    ring
  change |(∑' j, u j) - (∑' j, v j)| ≤ ε
  rw [← Summable.sum_add_tsum_nat_add k hus,
    ← Summable.sum_add_tsum_nat_add k hvs, hsplit]
  calc
    |(∑ j ∈ Finset.range k, (u j - v j)) +
        ((∑' j, u (j + k)) - (∑' j, v (j + k)))| ≤
      |∑ j ∈ Finset.range k, (u j - v j)| +
        |(∑' j, u (j + k)) - (∑' j, v (j + k))| :=
      abs_add_le _ _
    _ ≤ ε / 3 +
        (|∑' j, u (j + k)| + |∑' j, v (j + k)|) :=
      add_le_add hhead (abs_sub _ _)
    _ ≤ ε := by
      have htu := htailU.trans htail.le
      have htv := htailV.trans htail.le
      linarith

#print axioms fp81s21_initial_ULimB_uniform_qwin

end HRS.Fp81.S21

end
