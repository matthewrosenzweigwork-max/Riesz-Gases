import HRS.MS.Fp81S21InitialFR3

open MeasureTheory Filter Topology ProbabilityTheory
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

/-! The actual-marginal bias is O(N⁻¹) uniformly for the finite-rank observables.
The derivative-sensitive S4.8 bias estimate is reduced to its bounded Cᵏ norm by
`fp81s21_s48_Q_le_cb`. -/

theorem fp81s21_initial_FR_marginal_bias
    {p : Parameters} {δ : ℝ} {R : Trajectory p δ}
    (E : InitialSteinEnv R) {N : ℕ} (hN : 2 ≤ N)
    {u : Euc p.d → ℝ} (hu : MemCb (fp81s21_J1 p.d) u) :
    |HRS.Whole.pair (r26t3_marg R N) u - HRS.Whole.pair (r26t3_mu R 0) u| ≤
      (E.Cs * ((fp81s21_k0 p.d : ℝ) + 1) *
        cbNorm (fp81s21_J1 p.d) u) / (N : ℝ) := by
  haveI hμ : IsProbabilityMeasure (r26t3_mu R 0) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu E.reference.prob
  have hk0 : fp81s21_k0 p.d ≤ fp81s21_J1 p.d := by
    have h := fp81s21_J1_ge_k0 p.d
    omega
  have hu0 := HRS.MS.Tc5.tc5_cb_mono hk0 hu
  have hraw := fp81s21_initial_marginal_bias_s48 E hN hu0.1
  have hQ := fp81s21_s48_Q_le_cb (μ := r26t3_mu R 0) hu0.1
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hQ' : E.Cs * HRS.MS.S48.s48_Q (r26t3_mu R 0)
        (fp81s21_k0 p.d) u ≤
      E.Cs * ((fp81s21_k0 p.d : ℝ) + 1) *
        cbNorm (fp81s21_J1 p.d) u := by
    calc
      _ ≤ E.Cs * (((fp81s21_k0 p.d : ℝ) + 1) *
          cbNorm (fp81s21_k0 p.d) u) :=
        mul_le_mul_of_nonneg_left hQ E.Cs_nonneg
      _ ≤ E.Cs * ((fp81s21_k0 p.d : ℝ) + 1) *
          cbNorm (fp81s21_J1 p.d) u := by
        have hmono := hu0.2
        have hCs : 0 ≤ E.Cs := E.Cs_nonneg
        have hcoef : 0 ≤ E.Cs * ((fp81s21_k0 p.d : ℝ) + 1) :=
          mul_nonneg hCs (by positivity)
        calc
          _ = (E.Cs * ((fp81s21_k0 p.d : ℝ) + 1)) *
              cbNorm (fp81s21_k0 p.d) u := by ring
          _ ≤ (E.Cs * ((fp81s21_k0 p.d : ℝ) + 1)) *
              cbNorm (fp81s21_J1 p.d) u :=
            mul_le_mul_of_nonneg_left hmono hcoef
          _ = _ := by ring
  calc
    _ ≤ (E.Cs * HRS.MS.S48.s48_Q (r26t3_mu R 0)
        (fp81s21_k0 p.d) u) / (N : ℝ) := hraw
    _ ≤ _ := div_le_div_of_nonneg_right hQ' hNpos.le

/-! The actual mixed response limit plus the marginal centering correction gives
the pairwise centered covariance estimate used in the finite-rank assembly. -/

theorem fp81s21_initial_FR_pair_error
    {p : Parameters} {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    (R : Trajectory p δ) (E : InitialSteinEnv R) (hγ : 0 < p.γ)
    {φ : ℕ → Euc p.d → ℝ}
    (hφ : IsSummableFeatureFamily (fp81s21_J1 p.d) φ)
    {G : Measure SeqL2} [IsProbabilityMeasure G]
    {u v : Euc p.d → ℝ}
    (hu : MemCb (fp81s21_J1 p.d) u) (hv : MemCb (fp81s21_J1 p.d) v)
    (KM KY : ℝ) (hKM : 0 ≤ KM) (hKY : 0 ≤ KY)
    (hY2 : ∀ N : ℕ, 2 ≤ N → ∀ B : ℝ, 0 ≤ B →
      ∀ f : Euc p.d → ℝ, Measurable f → (∀ x, |f x| ≤ B) →
        Integrable (fun X : EucConfig p.d N =>
          (s45_Yi N f (HRS.Whole.pair (r26t3_marg R N) f) X) ^ 2) (r26t3_Q R N) ∧
        ∫ X, (s45_Yi N f (HRS.Whole.pair (r26t3_marg R N) f) X) ^ 2
          ∂(r26t3_Q R N) ≤ (KY * B) ^ 2)
    (hM : ∀ N : ℕ, 2 ≤ N → ∀ {ψ : SeqL2 → ℝ}, S99.Bd 4 ψ →
      |(∫ X, s45_Yi N u (HRS.Whole.pair (r26t3_marg R N) u) X *
          (s45_Yi N v (HRS.Whole.pair (r26t3_marg R N) v) X *
            ψ (featureVec φ (r26t3_marg R N) X)) ∂(r26t3_Q R N)) -
        (∫ X, s45_Yi N u (HRS.Whole.pair (r26t3_marg R N) u) X *
          s45_Yi N v (HRS.Whole.pair (r26t3_marg R N) v) X ∂(r26t3_Q R N)) *
          (∫ X, ψ (featureVec φ (r26t3_marg R N) X) ∂(r26t3_Q R N)) -
        ∑' l, ∑' q, fp81s21_initial_kap (R := R) u φ l *
          fp81s21_initial_kap (R := R) v φ q *
            ∫ z, S99.pd (S99.pd ψ l) q z ∂G| ≤ KM / Real.sqrt N)
    {N : ℕ} (hN : 2 ≤ N) {ψ : SeqL2 → ℝ} (hψ : S99.Bd 4 ψ) :
    |S99.Lc (r26t3_Q R N)
        (fun X => ψ (featureVec φ (r26t3_marg R N) X))
        (fun X =>
          (Real.sqrt N * (HRS.Whole.pair (HRS.Whole.empirical X) u - HRS.Whole.pair (r26t3_mu R 0) u)) *
          (Real.sqrt N * (HRS.Whole.pair (HRS.Whole.empirical X) v - HRS.Whole.pair (r26t3_mu R 0) v))) -
      ∑' l, ∑' q, fp81s21_initial_kap (R := R) u φ l *
        fp81s21_initial_kap (R := R) v φ q *
          ∫ z, S99.pd (S99.pd ψ l) q z ∂G| ≤
      (KM + 4 * (E.Cs * ((fp81s21_k0 p.d : ℝ) + 1)) * KY *
        (cbNorm (fp81s21_J1 p.d) u * cbNorm (fp81s21_J1 p.d) v)) /
          Real.sqrt N := by
  let P : Measure (EucConfig p.d N) := r26t3_Q R N
  let ν : Measure (Euc p.d) := r26t3_marg R N
  let μ : Measure (Euc p.d) := r26t3_mu R 0
  haveI hμ : IsProbabilityMeasure μ := by
    dsimp [μ]
    exact HRS.Whole.Q34.isProbabilityMeasure_nu E.reference.prob
  have hN1 : 1 ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hsqN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have hsq2 : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hN0.le
  haveI hP : IsProbabilityMeasure P := by
    dsimp [P]
    rw [← E.law_eq N]
    exact (E.static N hN).prob
  haveI hν : IsProbabilityMeasure ν := by
    dsimp [ν]
    exact S99.s99_nu_prob hN1
  let cu : ℝ := cbNorm (fp81s21_J1 p.d) u
  let cv : ℝ := cbNorm (fp81s21_J1 p.d) v
  have hcu0 : 0 ≤ cu := HRS.MS.Tc5.tc5_cb_nonneg _ _
  have hcv0 : 0 ≤ cv := HRS.MS.Tc5.tc5_cb_nonneg _ _
  have hubd : ∀ x, |u x| ≤ cu := fun x => by
    have h := HRS.MS.Tc5.tc5_cb_sup_le hu x
    simpa [cu, Real.norm_eq_abs] using h
  have hvbd : ∀ x, |v x| ≤ cv := fun x => by
    have h := HRS.MS.Tc5.tc5_cb_sup_le hv x
    simpa [cv, Real.norm_eq_abs] using h
  have hum : Measurable u := hu.1.continuous.measurable
  have hvm : Measurable v := hv.1.continuous.measurable
  have hJ1 : 1 ≤ fp81s21_J1 p.d := by unfold fp81s21_J1; omega
  have hWc : Continuous (fun X : EucConfig p.d N => featureVec φ ν X) :=
    (S99.s99_W_contDiff hN1 hJ1 hφ).continuous
  have hψ1 : S99.Bd 1 ψ := hψ.of_le (by norm_num)
  have hψWm : Measurable (fun X : EucConfig p.d N => ψ (featureVec φ ν X)) :=
    (hψ.1.continuous.comp hWc).measurable
  have hψWb : ∀ X : EucConfig p.d N, |ψ (featureVec φ ν X)| ≤ 1 :=
    fun X => hψ.abs_le _
  let ψW : EucConfig p.d N → ℝ := fun X => ψ (featureVec φ ν X)
  have hψBM : S99.BM ψW := ⟨hψWm, 1, hψWb⟩
  let Yu : EucConfig p.d N → ℝ := fun X => s45_Yi N u (HRS.Whole.pair ν u) X
  let Yv : EucConfig p.d N → ℝ := fun X => s45_Yi N v (HRS.Whole.pair ν v) X
  let Zu : EucConfig p.d N → ℝ := fun X =>
    Real.sqrt N * (HRS.Whole.pair (HRS.Whole.empirical X) u - HRS.Whole.pair μ u)
  let Zv : EucConfig p.d N → ℝ := fun X =>
    Real.sqrt N * (HRS.Whole.pair (HRS.Whole.empirical X) v - HRS.Whole.pair μ v)
  let βu : ℝ := Real.sqrt N * (HRS.Whole.pair ν u - HRS.Whole.pair μ u)
  let βv : ℝ := Real.sqrt N * (HRS.Whole.pair ν v - HRS.Whole.pair μ v)
  have hYum : Measurable Yu := by
    dsimp [Yu, s45_Yi]
    exact measurable_const.mul
      ((S45.s45_measurable_pair_empirical hN1 hum).sub measurable_const)
  have hYvm : Measurable Yv := by
    dsimp [Yv, s45_Yi]
    exact measurable_const.mul
      ((S45.s45_measurable_pair_empirical hN1 hvm).sub measurable_const)
  have hYub : ∀ X, |Yu X| ≤ 2 * Real.sqrt N * cu :=
    fun X => S99.s99_Yi_bd hN1 hubd X
  have hYvb : ∀ X, |Yv X| ≤ 2 * Real.sqrt N * cv :=
    fun X => S99.s99_Yi_bd hN1 hvbd X
  have hYumBM : S99.BM Yu := ⟨hYum, 2 * Real.sqrt N * cu, hYub⟩
  have hYvmBM : S99.BM Yv := ⟨hYvm, 2 * Real.sqrt N * cv, hYvb⟩
  have hZuBM : S99.BM Zu := by
    refine ⟨measurable_const.mul ((S45.s45_measurable_pair_empirical hN1 hum).sub measurable_const),
      2 * Real.sqrt N * cu, ?_⟩
    intro X
    dsimp [Zu]
    exact S99.s99_Yi_bd (ν := μ) hN1 hubd X
  have hZvBM : S99.BM Zv := by
    refine ⟨measurable_const.mul ((S45.s45_measurable_pair_empirical hN1 hvm).sub measurable_const),
      2 * Real.sqrt N * cv, ?_⟩
    intro X
    dsimp [Zv]
    exact S99.s99_Yi_bd (ν := μ) hN1 hvbd X
  have hZu : ∀ X, Zu X = Yu X + βu := by
    intro X
    simp only [Zu, Yu, βu, s45_Yi]
    ring
  have hZv : ∀ X, Zv X = Yv X + βv := by
    intro X
    simp only [Zv, Yv, βv, s45_Yi]
    ring
  have hLcZ : S99.Lc P ψW (fun X => Zu X * Zv X) =
      S99.Lc P ψW (fun X => Yu X * Yv X) +
        βv * S99.Lc P ψW Yu + βu * S99.Lc P ψW Yv := by
    have heq : (fun X => Zu X * Zv X) = fun X =>
        ((Yu X * Yv X + βv * Yu X) + βu * Yv X) + βu * βv := by
      funext X
      rw [hZu X, hZv X]
      ring
    have hb1 : S99.BM (fun X => Yu X * Yv X + βv * Yu X) :=
      (hYumBM.mul hYvmBM).add (hYumBM.const_mul _)
    have hb2 : S99.BM (fun X => (Yu X * Yv X + βv * Yu X) + βu * Yv X) :=
      hb1.add (hYvmBM.const_mul _)
    rw [heq, S99.Lc_add hψBM hb2 (S99.BM.const _), S99.Lc_const, add_zero,
      S99.Lc_add hψBM hb1 (hYvmBM.const_mul _),
      S99.Lc_add hψBM (hYumBM.mul hYvmBM) (hYumBM.const_mul _),
      S99.Lc_smul _ hψBM hYumBM, S99.Lc_smul _ hψBM hYvmBM]
  have hYul1 : |S99.Lc P ψW Yu| ≤ 2 * (KY * cu) := by
    have h1 := S99.Lc_abs_le (P := P) hψWb hψWm hYumBM
    have hmem : MemLp Yu 2 P := S99.s99_memLp_two_of_bdd hYumBM.meas
      (C := 2 * Real.sqrt N * cu) hYub
    have h2 := S99.s99_integral_abs_le_sqrt hmem
    have hY2u := hY2 N hN cu hcu0 u hum hubd
    have h3 : ∫ X, Yu X ^ 2 ∂P ≤ (KY * cu) ^ 2 := by
      simpa [P, ν, Yu] using hY2u.2
    have h4 : Real.sqrt (∫ X, Yu X ^ 2 ∂P) ≤ KY * cu :=
      (Real.sqrt_le_sqrt h3).trans_eq (Real.sqrt_sq (mul_nonneg hKY hcu0))
    exact h1.trans (mul_le_mul_of_nonneg_left (h2.trans h4) (by norm_num))
  have hYvl1 : |S99.Lc P ψW Yv| ≤ 2 * (KY * cv) := by
    have h1 := S99.Lc_abs_le (P := P) hψWb hψWm hYvmBM
    have hmem : MemLp Yv 2 P := S99.s99_memLp_two_of_bdd hYvmBM.meas
      (C := 2 * Real.sqrt N * cv) hYvb
    have h2 := S99.s99_integral_abs_le_sqrt hmem
    have hY2v := hY2 N hN cv hcv0 v hvm hvbd
    have h3 : ∫ X, Yv X ^ 2 ∂P ≤ (KY * cv) ^ 2 := by
      simpa [P, ν, Yv] using hY2v.2
    have h4 : Real.sqrt (∫ X, Yv X ^ 2 ∂P) ≤ KY * cv :=
      (Real.sqrt_le_sqrt h3).trans_eq (Real.sqrt_sq (mul_nonneg hKY hcv0))
    exact h1.trans (mul_le_mul_of_nonneg_left (h2.trans h4) (by norm_num))
  let Kb : ℝ := E.Cs * ((fp81s21_k0 p.d : ℝ) + 1)
  have hKb : 0 ≤ Kb := by
    dsimp [Kb]
    exact mul_nonneg E.Cs_nonneg (by positivity)
  have hβub : |βu| ≤ Kb * cu / Real.sqrt N := by
    have hbias := fp81s21_initial_FR_marginal_bias E hN hu
    have hsqrt : Real.sqrt N * Real.sqrt N = N := hsq2
    dsimp [βu, Kb, cu]
    rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    calc
      Real.sqrt N * |HRS.Whole.pair ν u - HRS.Whole.pair μ u| ≤
          Real.sqrt N * ((E.Cs * ((fp81s21_k0 p.d : ℝ) + 1) *
            cbNorm (fp81s21_J1 p.d) u) / N) :=
        mul_le_mul_of_nonneg_left hbias (Real.sqrt_nonneg _)
      _ = E.Cs * ((fp81s21_k0 p.d : ℝ) + 1) *
          cbNorm (fp81s21_J1 p.d) u / Real.sqrt N := by
        rw [eq_div_iff hsqN.ne']
        field_simp [hN0.ne']
        rw [Real.sq_sqrt hN0.le]
        ring
  have hβvb : |βv| ≤ Kb * cv / Real.sqrt N := by
    have hbias := fp81s21_initial_FR_marginal_bias E hN hv
    dsimp [βv, Kb, cv]
    rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    calc
      Real.sqrt N * |HRS.Whole.pair ν v - HRS.Whole.pair μ v| ≤
          Real.sqrt N * ((E.Cs * ((fp81s21_k0 p.d : ℝ) + 1) *
            cbNorm (fp81s21_J1 p.d) v) / N) :=
        mul_le_mul_of_nonneg_left hbias (Real.sqrt_nonneg _)
      _ = E.Cs * ((fp81s21_k0 p.d : ℝ) + 1) *
          cbNorm (fp81s21_J1 p.d) v / Real.sqrt N := by
        rw [eq_div_iff hsqN.ne']
        field_simp [hN0.ne']
        rw [Real.sq_sqrt hN0.le]
        ring
  let A : ℝ := (∫ X, Yu X * (Yv X * ψW X) ∂P) -
    (∫ X, Yu X * Yv X ∂P) * (∫ X, ψW X ∂P)
  let G0 : ℝ := ∑' l, ∑' q,
    fp81s21_initial_kap (R := R) u φ l *
      fp81s21_initial_kap (R := R) v φ q *
        ∫ z, S99.pd (S99.pd ψ l) q z ∂G
  let Bu : ℝ := βv * S99.Lc P ψW Yu
  let Bv : ℝ := βu * S99.Lc P ψW Yv
  have hCov :
      S99.Lc P ψW (fun X => Yu X * Yv X) =
        (∫ X, Yu X * (Yv X * ψW X) ∂P) -
          (∫ X, Yu X * Yv X ∂P) * (∫ X, ψW X ∂P) := by
    unfold S99.Lc
    congr 1
    congr 1
    funext X
    ring
  have hpair :
      |S99.Lc P ψW (fun X => Zu X * Zv X) -
        ∑' l, ∑' q, fp81s21_initial_kap (R := R) u φ l *
          fp81s21_initial_kap (R := R) v φ q *
            ∫ z, S99.pd (S99.pd ψ l) q z ∂G| ≤
        (KM + 4 * Kb * KY * (cu * cv)) / Real.sqrt N := by
    have hM' : |A - G0| ≤ KM / Real.sqrt N := by
      simpa [A, G0, P, ψW] using hM N hN hψ
    rw [hLcZ, hCov]
    calc
      _ = |(A - G0) + (Bu + Bv)| := by
        congr 1
        dsimp [A, G0, Bu, Bv]
        ring
      _ ≤ |A - G0| + |Bu + Bv| := abs_add_le _ _
      _ ≤ |A - G0| + (|Bu| + |Bv|) :=
        add_le_add le_rfl (abs_add_le Bu Bv)
      _ = |(∫ X, Yu X * (Yv X * ψW X) ∂P) -
          (∫ X, Yu X * Yv X ∂P) * (∫ X, ψW X ∂P) - G0| +
          |βv * S99.Lc P ψW Yu| + |βu * S99.Lc P ψW Yv| := by
        dsimp [A, Bu, Bv]
        ring_nf
      _ ≤ KM / Real.sqrt N +
          Kb * cv / Real.sqrt N * (2 * (KY * cu)) +
          Kb * cu / Real.sqrt N * (2 * (KY * cv)) := by
            refine add_le_add (add_le_add hM' ?_) ?_
            · rw [abs_mul]
              exact mul_le_mul hβvb hYul1 (abs_nonneg _) (by positivity)
            · rw [abs_mul]
              exact mul_le_mul hβub hYvl1 (abs_nonneg _) (by positivity)
      _ = (KM + 4 * Kb * KY * (cu * cv)) / Real.sqrt N := by ring
  simpa [P, ψW, Zu, Zv, μ, cu, cv, Kb] using hpair

/-! The full actual-initial-law finite-rank quadratic limit. Its proof follows the
compiled thermal `s99_FR` decomposition, replacing every thermal expectation and
response coefficient by the actual initial-law objects and the S4.7 exact-response
port. -/

theorem fp81s21_initial_FR
    {p : Parameters} {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    (R : Trajectory p δ) (E : InitialSteinEnv R) (hγ : 0 < p.γ)
    {φ : ℕ → Euc p.d → ℝ}
    (hφ : IsSummableFeatureFamily (fp81s21_J1 p.d) φ)
    (F : InitialFamData R φ)
    {G : Measure SeqL2} [IsProbabilityMeasure G]
    (hG : IsCenteredGaussianSeq G (fun i j =>
      HRS.Whole.susceptibilityCov (HRS.Whole.rieszKernel p.d p.s) (r26t3_mu R 0) p.γ
        (φ i) (φ j)))
    {m : ℕ} {cc : Fin m → Fin m → ℝ} {u : Fin m → Euc p.d → ℝ}
    (hcu : IsR2FiniteRankData cc u) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ, 2 ≤ N →
      ∀ {ψ : SeqL2 → ℝ}, S99.Bd 4 ψ →
        |fp81s21_initial_Bterm R φ N (r2FiniteRankKernel cc u) ψ -
          (1 / 2) * ∑' l, ∑' q,
            fp81s21_initial_Qk R φ (r2FiniteRankKernel cc u) l q *
              ∫ z, S99.pd (S99.pd ψ l) q z ∂G| ≤ K / Real.sqrt N := by
  have hcb : ∀ i, MemCb (fp81s21_J1 p.d) (u i) := fun i =>
    S99.s99_cb_of_cinf (hcu.smooth i) (hcu.compactSupport i) _
  choose KM hKM0 hKM using fun i j =>
    fp81s21_initial_Mab hδ hδh R E hγ hφ F hG (hcb i) (hcb j)
  obtain ⟨KY, hKY0, hY2⟩ := fp81s21_initial_Y_L2 hδ hδh E hγ
  obtain ⟨KT1, hKT10, hT1⟩ := fp81s21_initial_T_L1 hδ hδh E hγ
  let cu : Fin m → ℝ := fun i => cbNorm (fp81s21_J1 p.d) (u i)
  have hcu0 : ∀ i, 0 ≤ cu i := fun i => HRS.MS.Tc5.tc5_cb_nonneg _ _
  have hubd : ∀ i x, |u i x| ≤ cu i := fun i x => by
    have h := HRS.MS.Tc5.tc5_cb_sup_le (hcb i) x
    simpa [cu, Real.norm_eq_abs] using h
  have hucont : ∀ i, Continuous (u i) := fun i => (hcu.smooth i).continuous
  have hum : ∀ i, Measurable (u i) := fun i => (hucont i).measurable
  let Dg : Euc p.d → ℝ := fun x => ∑ i, ∑ j, cc i j * (u i x * u j x)
  let CD : ℝ := ∑ i, ∑ j, |cc i j| * (cu i * cu j)
  have hCD0 : 0 ≤ CD := by
    refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_
    have hi := hcu0 i
    have hj := hcu0 j
    positivity
  have hDgbd : ∀ x, |Dg x| ≤ CD := by
    intro x
    refine (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun i _ => ?_)
    refine (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun j _ => ?_)
    rw [abs_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul (hubd i x) (hubd j x) (abs_nonneg _) (hcu0 i))
      (abs_nonneg _)
  have hDgc : Continuous Dg := continuous_finset_sum _ fun i _ =>
    continuous_finset_sum _ fun j _ =>
      continuous_const.mul ((hucont i).mul (hucont j))
  have hDgm : Measurable Dg := hDgc.measurable
  obtain ⟨KT1', hKT1'0, hT1'⟩ :
      ∃ K1 : ℝ, 0 ≤ K1 ∧ ∀ N : ℕ, 2 ≤ N → ∀ B : ℝ, 0 ≤ B →
        ∀ w : Euc p.d → ℝ, Measurable w → (∀ x, |w x| ≤ B) →
          ∫ X, |HRS.Whole.pair (HRS.Whole.empirical X) w - HRS.Whole.pair (r26t3_mu R 0) w|
            ∂(r26t3_Q R N) ≤ K1 * B / Real.sqrt N :=
    ⟨KT1, hKT10, fun N hN B hB w hw hwb => hT1 N hN B hB w hw hwb⟩
  let Kb : ℝ := E.Cs * ((fp81s21_k0 p.d : ℝ) + 1)
  let K : ℝ :=
    (∑ i, ∑ j, (1 / 2) * |cc i j| *
      (KM i j + 4 * Kb * KY * (cu i * cu j))) + KT1' * CD
  have hK0 : 0 ≤ K := by
    dsimp [K, Kb]
    refine add_nonneg
      (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_) ?_
    · have hi := hKM0 i j
      have hci := hcu0 i
      have hcj := hcu0 j
      have : 0 ≤ E.Cs := E.Cs_nonneg
      positivity
    · exact mul_nonneg hKT1'0 hCD0
  refine ⟨K, hK0, fun N hN ψ hψ => ?_⟩
  have hN1 : 1 ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hsqN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have hsq2 : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hN0.le
  haveI hP : IsProbabilityMeasure (r26t3_Q R N) := by
    rw [← E.law_eq N]
    exact (E.static N hN).prob
  haveI hν : IsProbabilityMeasure (r26t3_marg R N) := S99.s99_nu_prob hN1
  haveI hμ : IsProbabilityMeasure (r26t3_mu R 0) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu E.reference.prob
  let P : Measure (EucConfig p.d N) := r26t3_Q R N
  let ν : Measure (Euc p.d) := r26t3_marg R N
  let μ : Measure (Euc p.d) := r26t3_mu R 0
  haveI hμLocal : IsProbabilityMeasure μ := by
    dsimp [μ]
    exact HRS.Whole.Q34.isProbabilityMeasure_nu E.reference.prob
  have hWc : Continuous (fun X : EucConfig p.d N => featureVec φ ν X) :=
    (S99.s99_W_contDiff hN1 (by unfold fp81s21_J1; omega) hφ).continuous
  let ψW : EucConfig p.d N → ℝ := fun X => ψ (featureVec φ ν X)
  have hψWm : Measurable ψW := (hψ.1.continuous.comp hWc).measurable
  have hψWb : ∀ X, |ψW X| ≤ 1 := fun X => hψ.abs_le _
  have hψBM : S99.BM ψW := ⟨hψWm, 1, hψWb⟩
  let Ya : Fin m → EucConfig p.d N → ℝ := fun i X =>
    s45_Yi N (u i) (HRS.Whole.pair ν (u i)) X
  let Z : Fin m → EucConfig p.d N → ℝ := fun i X =>
    Real.sqrt N * (HRS.Whole.pair (HRS.Whole.empirical X) (u i) - HRS.Whole.pair μ (u i))
  let βb : Fin m → ℝ := fun i =>
    Real.sqrt N * (HRS.Whole.pair ν (u i) - HRS.Whole.pair μ (u i))
  have hYaBM : ∀ i, S99.BM (Ya i) := by
    intro i
    exact ⟨measurable_const.mul
        ((S45.s45_measurable_pair_empirical hN1 (hum i)).sub measurable_const),
      2 * Real.sqrt N * cu i, fun X => S99.s99_Yi_bd hN1 (hubd i) X⟩
  have hZBM : ∀ i, S99.BM (Z i) := by
    intro i
    exact ⟨measurable_const.mul
        ((S45.s45_measurable_pair_empirical hN1 (hum i)).sub measurable_const),
      2 * Real.sqrt N * cu i, fun X => S99.s99_Yi_bd (ν := μ) hN1 (hubd i) X⟩
  have hZY : ∀ i X, Z i X = Ya i X + βb i := by
    intro i X
    simp only [Z, Ya, βb, s45_Yi]
    ring
  let Φ1 : EucConfig p.d N → ℝ := fun X =>
    ∑ i, ∑ j, ((1 / 2) * cc i j) * (Z i X * Z j X)
  let Φ2 : EucConfig p.d N → ℝ := fun X =>
    (-(1 / 2)) * HRS.Whole.pair (HRS.Whole.empirical X) Dg
  let ΦX : EucConfig p.d N → ℝ := fun X => Φ1 X + Φ2 X
  have hDgBound : ∀ x, |Dg x| ≤ CD := hDgbd
  have hΦ2BM : S99.BM (fun X : EucConfig p.d N => HRS.Whole.pair (HRS.Whole.empirical X) Dg) :=
    ⟨S45.s45_measurable_pair_empirical hN1 hDgm, CD,
      fun X => S45.s45_abs_pair_empirical_le hN1 hDgbd X⟩
  have hΦ1BM : S99.BM Φ1 := S99.BM.sum _ fun i _ => S99.BM.sum _ fun j _ =>
    S99.BM.const_mul _ ((hZBM i).mul (hZBM j))
  have hΦXBM : S99.BM ΦX := hΦ1BM.add (hΦ2BM.const_mul _)
  have hΦ : ∀ X, (N : ℝ) * pairEnergy (r2FiniteRankKernel cc u) X μ =
      Φ1 X + Φ2 X := by
    intro X
    rw [S99.s99_pe_finrank hcu μ hN1 X]
    have he : (∑ i, ∑ j, ((1 / 2) * cc i j) * (Z i X * Z j X)) =
        (1 / 2) * ∑ i, ∑ j, cc i j * (Z i X * Z j X) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    simp only [Φ1, Φ2, Dg]
    rw [he]
    simp only [Z]
    ring
  have hBh : ∀ X, (N : ℝ) *
      (pairEnergy (r2FiniteRankKernel cc u) X μ -
        ∫ Y, pairEnergy (r2FiniteRankKernel cc u) Y μ ∂P) =
      ΦX X - ∫ Y, ΦX Y ∂P := by
    have hmean : ∫ Y, ΦX Y ∂P = (N : ℝ) *
        ∫ Y, pairEnergy (r2FiniteRankKernel cc u) Y μ ∂P := by
      calc
        _ = ∫ Y, (N : ℝ) * pairEnergy (r2FiniteRankKernel cc u) Y μ ∂P :=
          integral_congr_ae (Filter.Eventually.of_forall fun Y => (hΦ Y).symm)
        _ = _ := integral_const_mul _ _
    intro X
    rw [show ΦX X = Φ1 X + Φ2 X from rfl]
    rw [← hΦ X, hmean]
    ring
  have hBterm : fp81s21_initial_Bterm R φ N (r2FiniteRankKernel cc u) ψ =
      S99.Lc P ψW ΦX := by
    unfold fp81s21_initial_Bterm S99.Lc
    have he : (fun X : EucConfig p.d N =>
        (N : ℝ) * (pairEnergy (r2FiniteRankKernel cc u) X μ -
          ∫ Y, pairEnergy (r2FiniteRankKernel cc u) Y μ ∂P) *
          ψ (featureVec φ ν X)) = fun X =>
        ΦX X * ψW X - (∫ Y, ΦX Y ∂P) * ψW X := by
      funext X
      rw [hBh X]
      simp only [ψW]
      ring
    rw [he, integral_sub (hΦXBM.mul hψBM).integrable
      (hψBM.integrable.const_mul _), integral_const_mul]
  have hZZ : ∀ i j X, Z i X * Z j X =
      Ya i X * Ya j X + βb j * Ya i X + βb i * Ya j X + βb i * βb j := by
    intro i j X
    rw [hZY i X, hZY j X]
    ring
  have hLcZ : ∀ i j, S99.Lc P ψW (fun X => Z i X * Z j X) =
      S99.Lc P ψW (fun X => Ya i X * Ya j X) +
        βb j * S99.Lc P ψW (Ya i) + βb i * S99.Lc P ψW (Ya j) := by
    intro i j
    have he : (fun X => Z i X * Z j X) = fun X =>
        ((Ya i X * Ya j X + βb j * Ya i X) + βb i * Ya j X) + βb i * βb j := by
      funext X
      rw [hZZ]
    have hb1 : S99.BM (fun X => Ya i X * Ya j X + βb j * Ya i X) :=
      ((hYaBM i).mul (hYaBM j)).add ((hYaBM i).const_mul _)
    have hb2 : S99.BM (fun X => (Ya i X * Ya j X + βb j * Ya i X) + βb i * Ya j X) :=
      hb1.add ((hYaBM j).const_mul _)
    rw [he, S99.Lc_add hψBM hb2 (S99.BM.const _), S99.Lc_const, add_zero,
      S99.Lc_add hψBM hb1 ((hYaBM j).const_mul _),
      S99.Lc_add hψBM ((hYaBM i).mul (hYaBM j)) ((hYaBM i).const_mul _),
      S99.Lc_smul _ hψBM (hYaBM i), S99.Lc_smul _ hψBM (hYaBM j)]
  have hLcΦ1 : S99.Lc P ψW Φ1 =
      ∑ i, ∑ j, ((1 / 2) * cc i j) *
        S99.Lc P ψW (fun X => Z i X * Z j X) := by
    have h1 : S99.Lc P ψW Φ1 = ∑ i, S99.Lc P ψW
        (fun X => ∑ j, ((1 / 2) * cc i j) * (Z i X * Z j X)) :=
      S99.Lc_sum _ hψBM (fun i _ => S99.BM.sum _ fun j _ =>
        S99.BM.const_mul _ ((hZBM i).mul (hZBM j)))
    rw [h1]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [S99.Lc_sum _ hψBM (fun j _ =>
      S99.BM.const_mul _ ((hZBM i).mul (hZBM j)))]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact S99.Lc_smul _ hψBM ((hZBM i).mul (hZBM j))
  have hLcΦ2 : |S99.Lc P ψW Φ2| ≤ KT1' * CD / Real.sqrt N := by
    have he : S99.Lc P ψW Φ2 = (-(1 / 2)) *
        S99.Lc P ψW (fun X => HRS.Whole.pair (HRS.Whole.empirical X) Dg) :=
      S99.Lc_smul _ hψBM hΦ2BM
    have hshift := S99.s99_Lc_shift (P := P) hψBM hΦ2BM (HRS.Whole.pair μ Dg)
    have hsubBM := hΦ2BM.sub_const (HRS.Whole.pair μ Dg)
    have hLc := S99.Lc_abs_le (P := P) hψWb hψWm hsubBM
    have hT := hT1' N hN CD hCD0 Dg hDgm hDgbd
    rw [he, hshift, abs_mul]
    have hbound : |S99.Lc P ψW
        (fun X => HRS.Whole.pair (HRS.Whole.empirical X) Dg - HRS.Whole.pair μ Dg)| ≤
        2 * (KT1' * CD / Real.sqrt N) := by
      exact hLc.trans (mul_le_mul_of_nonneg_left hT (by norm_num))
    calc
      |-(1 / 2 : ℝ)| * |S99.Lc P ψW
          (fun X => HRS.Whole.pair (HRS.Whole.empirical X) Dg - HRS.Whole.pair μ Dg)| ≤
        (1 / 2) * (2 * (KT1' * CD / Real.sqrt N)) := by
          rw [abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
          exact mul_le_mul_of_nonneg_left hbound (by norm_num)
      _ = KT1' * CD / Real.sqrt N := by ring
  let Gm : ℕ → ℕ → ℝ := fun l q =>
    ∫ z, S99.pd (S99.pd ψ l) q z ∂G
  have hconv : ∑' l, ∑' q,
      fp81s21_initial_Qk R φ (r2FiniteRankKernel cc u) l q * Gm l q =
      ∑ i, ∑ j, cc i j * ∑' l, ∑' q,
        fp81s21_initial_kap (R := R) (u i) φ l *
          fp81s21_initial_kap (R := R) (u j) φ q * Gm l q := by
    simpa [Gm] using fp81s21_initial_Qk_series E hφ F hcu hψ
  have hε : ∀ i j, |S99.Lc P ψW (fun X => Z i X * Z j X) -
      ∑' l, ∑' q, fp81s21_initial_kap (R := R) (u i) φ l *
        fp81s21_initial_kap (R := R) (u j) φ q * Gm l q| ≤
      (KM i j + 4 * Kb * KY * (cu i * cu j)) / Real.sqrt N := by
    intro i j
    have hMij : ∀ N : ℕ, 2 ≤ N → ∀ {ψ : SeqL2 → ℝ}, S99.Bd 4 ψ →
        |(∫ X, s45_Yi N (u i) (HRS.Whole.pair (r26t3_marg R N) (u i)) X *
            (s45_Yi N (u j) (HRS.Whole.pair (r26t3_marg R N) (u j)) X *
              ψ (featureVec φ (r26t3_marg R N) X)) ∂(r26t3_Q R N)) -
          (∫ X, s45_Yi N (u i) (HRS.Whole.pair (r26t3_marg R N) (u i)) X *
            s45_Yi N (u j) (HRS.Whole.pair (r26t3_marg R N) (u j)) X
              ∂(r26t3_Q R N)) *
            (∫ X, ψ (featureVec φ (r26t3_marg R N) X)
              ∂(r26t3_Q R N)) -
          ∑' l, ∑' q, fp81s21_initial_kap (R := R) (u i) φ l *
            fp81s21_initial_kap (R := R) (u j) φ q *
              ∫ z, S99.pd (S99.pd ψ l) q z ∂G| ≤ KM i j / Real.sqrt N :=
      hKM i j
    have hp := fp81s21_initial_FR_pair_error hδ hδh R E hγ hφ
      (hcb i) (hcb j) (KM i j) KY (hKM0 i j) hKY0 hY2 hMij hN hψ
    simpa [Kb, cu] using hp
  have hBsum : fp81s21_initial_Bterm R φ N
        (r2FiniteRankKernel cc u) ψ =
      S99.Lc P ψW Φ1 + S99.Lc P ψW Φ2 := by
    rw [hBterm, show ΦX = fun X => Φ1 X + Φ2 X from rfl,
      S99.Lc_add hψBM hΦ1BM (hΦ2BM.const_mul _)]
  rw [hBsum, hLcΦ1, hconv, Finset.mul_sum]
  have hfin :
      (∑ i, ∑ j, ((1 / 2) * cc i j) *
        S99.Lc P ψW (fun X => Z i X * Z j X) + S99.Lc P ψW Φ2) -
        ∑ i, (1 / 2) * ∑ j, cc i j *
          ∑' l, ∑' q, fp81s21_initial_kap (R := R) (u i) φ l *
            fp81s21_initial_kap (R := R) (u j) φ q * Gm l q =
      (∑ i, ∑ j, ((1 / 2) * cc i j) *
        (S99.Lc P ψW (fun X => Z i X * Z j X) -
          ∑' l, ∑' q, fp81s21_initial_kap (R := R) (u i) φ l *
            fp81s21_initial_kap (R := R) (u j) φ q * Gm l q)) +
        S99.Lc P ψW Φ2 := by
    simp only [Finset.mul_sum, mul_sub, Finset.sum_sub_distrib]
    have he : ∀ i j : Fin m,
        (1 / 2 : ℝ) * (cc i j *
          ∑' l, ∑' q, fp81s21_initial_kap (R := R) (u i) φ l *
            fp81s21_initial_kap (R := R) (u j) φ q * Gm l q) =
        1 / 2 * cc i j *
          ∑' l, ∑' q, fp81s21_initial_kap (R := R) (u i) φ l *
            fp81s21_initial_kap (R := R) (u j) φ q * Gm l q := by
      intro i j
      ring
    simp only [he]
    ring
  rw [hfin]
  refine (abs_add_le _ _).trans ?_
  have hsum :
      |∑ i, ∑ j, ((1 / 2) * cc i j) *
        (S99.Lc P ψW (fun X => Z i X * Z j X) -
          ∑' l, ∑' q, fp81s21_initial_kap (R := R) (u i) φ l *
            fp81s21_initial_kap (R := R) (u j) φ q * Gm l q)| ≤
        (∑ i, ∑ j, (1 / 2) * |cc i j| *
          (KM i j + 4 * Kb * KY * (cu i * cu j))) / Real.sqrt N := by
    rw [Finset.sum_div]
    refine (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun i _ => ?_)
    rw [Finset.sum_div]
    refine (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun j _ => ?_)
    rw [abs_mul, abs_mul,
      abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    calc
      1 / 2 * |cc i j| *
          |S99.Lc P ψW (fun X => Z i X * Z j X) -
            ∑' l, ∑' q, fp81s21_initial_kap (R := R) (u i) φ l *
              fp81s21_initial_kap (R := R) (u j) φ q * Gm l q|
          ≤ 1 / 2 * |cc i j| *
            ((KM i j + 4 * Kb * KY * (cu i * cu j)) / Real.sqrt N) :=
        mul_le_mul_of_nonneg_left (hε i j) (by positivity)
      _ = _ := by ring
  calc
    |∑ i, ∑ j, ((1 / 2) * cc i j) *
        (S99.Lc P ψW (fun X => Z i X * Z j X) -
          ∑' l, ∑' q, fp81s21_initial_kap (R := R) (u i) φ l *
            fp81s21_initial_kap (R := R) (u j) φ q * Gm l q)| +
        |S99.Lc P ψW Φ2| ≤
      (∑ i, ∑ j, (1 / 2) * |cc i j| *
          (KM i j + 4 * Kb * KY * (cu i * cu j))) / Real.sqrt N +
        KT1' * CD / Real.sqrt N := add_le_add hsum hLcΦ2
    _ = K / Real.sqrt N := by
      dsimp [K]
      ring

#print axioms fp81s21_initial_FR_marginal_bias
#print axioms fp81s21_initial_FR_pair_error
#print axioms fp81s21_initial_FR

end HRS.Fp81.S21

end
