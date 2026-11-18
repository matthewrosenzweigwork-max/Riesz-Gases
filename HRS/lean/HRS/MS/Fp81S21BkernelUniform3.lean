import HRS.MS.Fp81S21BkernelUniform2
import HRS.MS.Fp81S21ShiftKernel4

open MeasureTheory Filter
open scoped ENNReal NNReal BigOperators

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
noncomputable section

namespace HRS.Fp81.S21

open S99
open HRS (Euc cbNorm)
open HRS.Whole
open HRS.MS.R26T3

/-- A common finite-rank rate and the bounded-start finite cover give one
particle cutoff for a fixed qwin coordinate. The test class here is `Bd 4`,
which is the class required by the staged finite-rank rate. -/
theorem fp81s21_initial_Bkernel_uniform_qwin_bd4_of_FR
    {p : Parameters} {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    (R : Trajectory p δ) (E : InitialSteinEnv R) (hγ : 0 < p.γ)
    (F : fp81s21_CompatPotentialFamily R)
    {K C c : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C) (hc : 0 ≤ c)
    (hFK : ∀ a : Set.Ici (0 : ℝ), (F a).K ≤ K)
    (hdecay : ∀ a : Set.Ici (0 : ℝ), ∀ j : ℕ,
      HasCbBound (fp81s21_k0 p.d)
        (C * Real.exp (-c * (a : ℝ)) * r26t3_feature_weight p.d j)
        (gradient ((F a).χ j)) )
    (S : ℝ) (hS : 0 ≤ S)
    (hphi : ∀ a : Set.Ici (0 : ℝ),
      IsSummableFeatureFamily (fp81s21_J1 p.d)
        (r26t3_qwin R (a : ℝ)))
    (hSum : ∀ a : Set.Ici (0 : ℝ),
      featureSum (fp81s21_J1 p.d) (r26t3_qwin R (a : ℝ)) ≤ S)
    (hFR : ∀ D : fp81s21_RankKernel p.d,
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
                  ≤ KFR / Real.sqrt N) :
    ∀ M : ℝ, 0 ≤ M → ∀ j : ℕ, ∀ ε : ℝ, 0 < ε →
      ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → 2 ≤ N →
        ∀ a : ℝ, ∀ (ha : a ∈ Set.Icc (0 : ℝ) M),
          ∀ {G : Measure SeqL2} [IsProbabilityMeasure G],
            IsCenteredGaussianSeq G
              (fun l q => HRS.Whole.susceptibilityCov
                (rieszKernel p.d p.s) (r26t3_mu R 0) p.γ
                (r26t3_qwin R a l) (r26t3_qwin R a q)) →
            ∀ ψ : SeqL2 → ℝ, S99.Bd 4 ψ →
              |fp81s21_initial_Bterm R (r26t3_qwin R a) N
                  (fun x y => commutatorKernel p.d p.s
                    (gradient ((F ⟨a, ha.1⟩).χ j)) x y) ψ -
                fp81s21_initial_Blimit R (r26t3_qwin R a) G ψ
                  (fun x y => commutatorKernel p.d p.s
                    (gradient ((F ⟨a, ha.1⟩).χ j)) x y)| ≤ ε := by
  intro M hM j ε hε
  classical
  let T : ℝ := K ^ 2 * S ^ 2
  have hT : 0 ≤ T := by dsimp [T]; positivity
  let Qc : ℝ := T + 1
  have hQc : 0 < Qc := by dsimp [Qc, T]; positivity
  let ρ : ℝ := ε / (3 * Qc)
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hρ0 : 0 ≤ ρ := hρ.le
  have hρeps : ρ ≤ ε / 3 := by
    dsimp [ρ, Qc, T]
    have hden : 0 < 3 * (K ^ 2 * S ^ 2 + 1) := by positivity
    rw [div_le_iff₀ hden]
    nlinarith [sq_nonneg K, sq_nonneg S]
  obtain ⟨B, C₂, hB, hC₂, hkernelBound, m, D, hDbound, hcover⟩ :=
    fp81s21_initial_shift_kernel_finite_cover hδ hδh R E hγ F hC hc
      hdecay M hM j ρ hρ
  choose KFR hKFR hrateFR using fun i : Fin m => hFR (D i)
  let Ktot : ℝ := ∑ i : Fin m, KFR i
  have hKtot : 0 ≤ Ktot := by
    dsimp [Ktot]
    exact Finset.sum_nonneg fun i hi => hKFR i
  let N0 : ℕ := max 2 (⌈(3 * Ktot / ε) ^ 2⌉₊ + 1)
  refine ⟨N0, ?_⟩
  intro N hN0 hN2 a ha G _ hG ψ hψ
  let aI : Set.Ici (0 : ℝ) := ⟨a, ha.1⟩
  have haM : (aI : ℝ) ≤ M := ha.2
  obtain ⟨i, hpairInt, hpairL1, hstat⟩ := hcover aI haM
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hsqrtN : 0 < Real.sqrt N := Real.sqrt_pos.2 hNpos
  have hKle : KFR i ≤ Ktot := by
    dsimp [Ktot]
    exact Finset.single_le_sum (fun k hk => hKFR k) (Finset.mem_univ i)
  have hceil : (3 * Ktot / ε) ^ 2 ≤ (⌈(3 * Ktot / ε) ^ 2⌉₊ : ℝ) :=
    Nat.le_ceil _
  have hceilN : ((⌈(3 * Ktot / ε) ^ 2⌉₊ + 1 : ℕ) : ℝ) ≤ N := by
    exact_mod_cast (le_max_right 2 (⌈(3 * Ktot / ε) ^ 2⌉₊ + 1)).trans hN0
  push_cast at hceilN
  have hsqN : (3 * Ktot / ε) ^ 2 ≤ (N : ℝ) := by linarith
  have hscale : 3 * Ktot / ε ≤ Real.sqrt N :=
    Real.le_sqrt_of_sq_le hsqN
  have hrateSmall : KFR i / Real.sqrt N ≤ ε / 3 := by
    calc
      KFR i / Real.sqrt N ≤ Ktot / Real.sqrt N :=
        div_le_div_of_nonneg_right hKle hsqrtN.le
      _ ≤ ε / 3 := by
        rw [div_le_iff₀ hsqrtN]
        have hscale' : 3 * Ktot ≤ ε * Real.sqrt N := by
          have hscale'' : 3 * Ktot ≤ Real.sqrt N * ε :=
            (div_le_iff₀ hε).1 hscale
          nlinarith [hscale'']
        nlinarith
  have hN1 : 1 ≤ N := by omega
  haveI hP : IsProbabilityMeasure (r26t3_Q R N) := by
    rw [← E.law_eq N]
    exact (E.static N hN2).prob
  haveI hν : IsProbabilityMeasure (r26t3_marg R N) := S99.s99_nu_prob hN1
  have hφa : IsSummableFeatureFamily (fp81s21_J1 p.d)
      (r26t3_qwin R (aI : ℝ)) := hphi aI
  have hkBound : IsBoundedPairKernel p.s B
      (fun x y => commutatorKernel p.d p.s
        (gradient ((F aI).χ j)) x y) := hkernelBound aI haM
  have hDdim : IsBoundedPairKernel p.s (C₂ * B) (D i).kernel := hDbound i
  have hstatN := hstat N hN2
  let k : Euc p.d → Euc p.d → ℝ := fun x y =>
    commutatorKernel p.d p.s (gradient ((F aI).χ j)) x y
  let ψW : EucConfig p.d N → ℝ := fun X =>
    ψ (featureVec (r26t3_qwin R (aI : ℝ)) (r26t3_marg R N) X)
  let dBh : EucConfig p.d N → ℝ := fun X =>
    fp81s21_initial_Bh R N k X - fp81s21_initial_Bh R N (D i).kernel X
  have hψWb : ∀ X, |ψW X| ≤ 1 := fun X => hψ.abs_le _
  have hIh := fp81s21_initial_Bterm_int hδ hδh R E hγ hφa hkBound hN2 hψ
  have hID := fp81s21_initial_Bterm_int hδ hδh R E hγ hφa hDdim hN2 hψ
  have hIntD : Integrable dBh (r26t3_Q R N) := by
    simpa [dBh, k] using hstatN.1
  have hIntProd : Integrable (fun X => dBh X * ψW X) (r26t3_Q R N) := by
    have hdiff := hIh.sub hID
    apply hdiff.congr
    filter_upwards with X
    simp [dBh, ψW, k, fp81s21_initial_Bh]
    ring
  have htermEq :
      fp81s21_initial_Bterm R (r26t3_qwin R (aI : ℝ)) N k ψ -
          fp81s21_initial_Bterm R (r26t3_qwin R (aI : ℝ)) N (D i).kernel ψ =
        ∫ X, dBh X * ψW X ∂(r26t3_Q R N) := by
    change (∫ X, fp81s21_initial_Bh R N k X * ψW X ∂(r26t3_Q R N)) -
        (∫ X, fp81s21_initial_Bh R N (D i).kernel X * ψW X ∂(r26t3_Q R N)) =
      ∫ X, dBh X * ψW X ∂(r26t3_Q R N)
    have he : (fun X => fp81s21_initial_Bh R N k X * ψW X -
          fp81s21_initial_Bh R N (D i).kernel X * ψW X) =
        (fun X => dBh X * ψW X) := by
      funext X
      simp [dBh]
      ring
    rw [← integral_sub hIh hID]
    rw [← he]
  have hAbsProd : Integrable (fun X => |dBh X * ψW X|) (r26t3_Q R N) :=
    hIntProd.abs
  have hAbsStat : Integrable (fun X => |dBh X|) (r26t3_Q R N) := hIntD.abs
  have hA :
      |fp81s21_initial_Bterm R (r26t3_qwin R (aI : ℝ)) N k ψ -
        fp81s21_initial_Bterm R (r26t3_qwin R (aI : ℝ)) N (D i).kernel ψ| ≤ ρ := by
    rw [htermEq]
    calc
      |∫ X, dBh X * ψW X ∂(r26t3_Q R N)| =
          ‖∫ X, dBh X * ψW X ∂(r26t3_Q R N)‖ := by rw [Real.norm_eq_abs]
      _ ≤ ∫ X, ‖dBh X * ψW X‖ ∂(r26t3_Q R N) := norm_integral_le_integral_norm _
      _ = ∫ X, |dBh X * ψW X| ∂(r26t3_Q R N) := by simp [Real.norm_eq_abs]
      _ ≤ ∫ X, |dBh X| ∂(r26t3_Q R N) := by
        refine integral_mono_ae hAbsProd hAbsStat ?_
        filter_upwards with X
        rw [abs_mul]
        calc
          |dBh X| * |ψW X| ≤ |dBh X| * 1 :=
            mul_le_mul_of_nonneg_left (hψWb X) (abs_nonneg _)
          _ = |dBh X| := mul_one _
      _ ≤ ρ := by simpa [dBh] using hstatN.2
  have hμD := (fp81s21_initial_kernel_wr8 hδ hδh R hDdim).prod
  have hμk := (fp81s21_initial_kernel_wr8 hδ hδh R hkBound).prod
  have hCraw := fp81s21_initial_Blimit_l1_bound E hφa (F aI) (G := G) hψ
    (h := (D i).kernel) (D := k) hμD hμk hρ0 (by
      simpa [k, Function.uncurry] using hpairL1)
  have hCswap :
      |fp81s21_initial_Blimit R (r26t3_qwin R (aI : ℝ)) G ψ (D i).kernel -
        fp81s21_initial_Blimit R (r26t3_qwin R (aI : ℝ)) G ψ k| ≤
          (1 / 2) * ((F aI).K ^ 2 * ρ *
            (featureSum (fp81s21_J1 p.d) (r26t3_qwin R (aI : ℝ))) ^ 2) := by
    simpa only [abs_sub_comm] using hCraw
  have hKa2 : (F aI).K ^ 2 ≤ K ^ 2 := by
    nlinarith [hFK aI, (F aI).hK, hK]
  have hfeat0 : 0 ≤ featureSum (fp81s21_J1 p.d) (r26t3_qwin R (aI : ℝ)) := by
    unfold featureSum
    exact tsum_nonneg fun l => HRS.MS.Tc5.tc5_cb_nonneg _ _
  have hfeat2 :
      (featureSum (fp81s21_J1 p.d) (r26t3_qwin R (aI : ℝ))) ^ 2 ≤ S ^ 2 := by
    nlinarith [hSum aI]
  have hC :
      |fp81s21_initial_Blimit R (r26t3_qwin R (aI : ℝ)) G ψ (D i).kernel -
        fp81s21_initial_Blimit R (r26t3_qwin R (aI : ℝ)) G ψ k| ≤ ε / 3 := by
    calc
      _ ≤ (1 / 2) * (K ^ 2 * ρ * S ^ 2) := by
        apply le_trans hCswap
        apply mul_le_mul_of_nonneg_left
        · calc
            (F aI).K ^ 2 * ρ *
                (featureSum (fp81s21_J1 p.d) (r26t3_qwin R (aI : ℝ))) ^ 2
                ≤ K ^ 2 * ρ *
                    (featureSum (fp81s21_J1 p.d) (r26t3_qwin R (aI : ℝ))) ^ 2 := by
                      exact mul_le_mul_of_nonneg_right
                        (mul_le_mul_of_nonneg_right hKa2 hρ0)
                        (sq_nonneg _)
            _ ≤ K ^ 2 * ρ * S ^ 2 :=
                  mul_le_mul_of_nonneg_left hfeat2 (mul_nonneg (sq_nonneg _) hρ0)
        · norm_num
      _ ≤ ε / 3 := by
        have hTle : T ≤ T + 1 := by linarith
        have hfrac0 : 0 ≤ ε / (3 * (T + 1)) := by positivity
        have hden : 0 < 3 * (T + 1) := by positivity
        calc
          (1 / 2) * (K ^ 2 * ρ * S ^ 2) =
              (1 / 2) * (T * (ε / (3 * (T + 1)))) := by
                dsimp [ρ, Qc, T]
                ring
          _ ≤ (1 / 2) * ((T + 1) * (ε / (3 * (T + 1)))) :=
                mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_right hTle hfrac0) (by norm_num)
          _ = ε / 6 := by field_simp [ne_of_gt hden]; norm_num
          _ ≤ ε / 3 := by linarith
  have hB := hrateFR i aI hG N hN2 ψ hψ
  have hNrate : KFR i / Real.sqrt N ≤ ε / 3 := hrateSmall
  have hthree := fp81s21_initial_Bkernel_three_term
    (R := R) (φ := r26t3_qwin R (aI : ℝ)) N k (D i).kernel G ψ
    ρ (KFR i / Real.sqrt N) (ε / 3) hA hB hC
  have hsum : ρ + KFR i / Real.sqrt N + ε / 3 ≤ ε := by linarith
  have hfinal := hthree.trans hsum
  change |fp81s21_initial_Bterm R (r26t3_qwin R (aI : ℝ)) N k ψ -
    fp81s21_initial_Blimit R (r26t3_qwin R (aI : ℝ)) G ψ k| ≤ ε
  exact hfinal

#print axioms fp81s21_initial_Bkernel_uniform_qwin_bd4_of_FR

end HRS.Fp81.S21

end
