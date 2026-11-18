import HRS.MS.Fp81S21InitialLinear3

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
noncomputable section

namespace HRS.Fp81.S21

open S45
open HRS.Whole
open HRS (Euc MemCb cbNorm)
open HRS.MS.R26T3

/-!
Audit helper for the staged coefficient estimate. With a common `Ylin` rate `KL` and a
family-data bound `F.K ≤ K`, the coefficient rate uses the explicit constant
`((J+1) * 2^J * (γ⁻¹*K)) * (KL + E.Cs*(J+1))`. Producing one `KL` for the shift-indexed
feature families is a separate uniformity step.
-/
theorem fp81s21_initial_A_rate_from_common_Ylin
    {p : Parameters} {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    (R : Trajectory p δ) (E : InitialSteinEnv R) (hγ : 0 < p.γ)
    {φ : ℕ → Euc p.d → ℝ} (hφ : IsSummableFeatureFamily (fp81s21_J1 p.d) φ)
    (F : InitialFamData R φ)
    {G : Measure SeqL2} [IsProbabilityMeasure G]
    (hG : IsCenteredGaussianSeq G (fun i j =>
      HRS.Whole.susceptibilityCov (rieszKernel p.d p.s) (r26t3_mu R 0) p.γ
        (φ i) (φ j)))
    (K KL : ℝ) (hK0 : 0 ≤ K) (hFK : F.K ≤ K) (hKL0 : 0 ≤ KL)
    (hYlin : ∀ N : ℕ, 2 ≤ N → ∀ {w : Euc p.d → ℝ},
      MemCb (fp81s21_k0 p.d) w → ∀ {ψ : SeqL2 → ℝ}, S99.Bd 3 ψ →
      |(∫ X, s45_Yi N w (HRS.Whole.pair (r26t3_marg R N) w) X *
          ψ (featureVec φ (r26t3_marg R N) X) ∂(r26t3_Q R N)) -
        ∑' m, fp81s21_initial_kap (R := R) w φ m *
          ∫ z, S99.pd ψ m z ∂G| ≤
        KL * cbNorm (fp81s21_k0 p.d) w / Real.sqrt N) :
    ∃ KA : ℝ, 0 ≤ KA ∧
      KA = (((((fp81s21_k0 p.d : ℝ) + 1) * 2 ^ fp81s21_k0 p.d) *
        (p.γ⁻¹ * K)) * (KL + E.Cs * ((fp81s21_k0 p.d : ℝ) + 1))) ∧
      ∀ N : ℕ, 2 ≤ N → ∀ f : SeqL2 → ℝ,
      S99.SteinCl f → ∀ q : ℕ × ℕ,
      |fp81s21_initial_Aterm F N f q - fp81s21_initial_Alim F G f q| ≤
        KA * (cbNorm (fp81s21_J1 p.d) (φ q.1) *
          cbNorm (fp81s21_J1 p.d) (φ q.2)) / Real.sqrt N := by
  let J : ℕ := fp81s21_k0 p.d
  let b : ℕ → ℝ := fun j => cbNorm (fp81s21_J1 p.d) (φ j)
  have hJ : 1 ≤ J := by dsimp [J]; exact fp81s21_k0_ge_one p.d
  have hb0 : ∀ j, 0 ≤ b j := fun j => HRS.MS.Tc5.tc5_cb_nonneg _ _
  have hFKn : 0 ≤ F.K := F.hK
  have hCs : 0 ≤ E.Cs := E.Cs_nonneg
  let Kw : ℝ := ((J : ℝ) + 1) * 2 ^ J * (p.γ⁻¹ * K)
  let KA : ℝ := Kw * (KL + E.Cs * ((J : ℝ) + 1))
  have hKw0 : 0 ≤ Kw := by
    dsimp [Kw]
    positivity
  have hKA0 : 0 ≤ KA := by
    dsimp [KA]
    positivity
  refine ⟨KA, hKA0, rfl, fun N hN f hf q => ?_⟩
  obtain ⟨j, k⟩ := q
  have hN1 : 1 ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hsqN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  haveI hP : IsProbabilityMeasure (r26t3_Q R N) := by
    rw [← E.law_eq N]
    exact (E.static N hN).prob
  haveI hμ : IsProbabilityMeasure (r26t3_mu R 0) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu E.reference.prob
  haveI hν : IsProbabilityMeasure (r26t3_marg R N) := S99.s99_nu_prob hN1
  let P : Measure (EucConfig p.d N) := r26t3_Q R N
  let ν : Measure (Euc p.d) := r26t3_marg R N
  let W : EucConfig p.d N → SeqL2 := fun X => featureVec φ ν X
  let w : Euc p.d → ℝ := InitialFamData.wF F j k
  let ψ : SeqL2 → ℝ := S99.pd (S99.pd f j) k
  let Y : EucConfig p.d N → ℝ := fun X =>
    s45_Yi N w (HRS.Whole.pair ν w) X
  let β0 : ℝ := Real.sqrt N *
    (HRS.Whole.pair ν w - fp81s21_initial_Cf F j k)
  have hψ : S99.Bd 3 ψ := (hf.pd j).pd k
  have hJ1 : 1 ≤ fp81s21_J1 p.d := by unfold fp81s21_J1; omega
  have hWc : Continuous W := (S99.s99_W_contDiff hN1 hJ1 hφ).continuous
  have hψWbd : ∀ X, |ψ (W X)| ≤ 1 := fun X => hψ.abs_le _
  have hψWm : Measurable fun X : EucConfig p.d N => ψ (W X) :=
    (hψ.1.continuous.comp hWc).measurable
  have hψWint : Integrable (fun X : EucConfig p.d N => ψ (W X)) P :=
    Integrable.of_bound hψWm.aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun X => by
        rw [Real.norm_eq_abs]
        exact hψWbd X)
  have hwcb := fp81s21_initial_wF_cb hφ.1 F hγ j k
  have hwbd : ∀ x, |w x| ≤ cbNorm J w := by
    intro x
    have hh := HRS.MS.Tc5.tc5_cb_sup_le hwcb.1 x
    rwa [Real.norm_eq_abs] at hh
  have hwm : Measurable w := hwcb.1.1.continuous.measurable
  have hcw : cbNorm J w ≤ Kw * (b j * b k) := by
    calc
      cbNorm J w ≤ ((J : ℝ) + 1) * 2 ^ J *
          (p.γ⁻¹ * F.K * b j) * b k := by
        simpa [J, b, w] using hwcb.2
      _ ≤ ((J : ℝ) + 1) * 2 ^ J *
          (p.γ⁻¹ * K * b j) * b k := by
        gcongr
        all_goals exact hb0 _
      _ = Kw * (b j * b k) := by dsimp [Kw]; ring
  have hcw0 : 0 ≤ cbNorm J w := HRS.MS.Tc5.tc5_cb_nonneg J w
  have hYbd : ∀ X, |Y X| ≤ 2 * Real.sqrt N * cbNorm J w := by
    intro X
    simp only [Y, s45_Yi]
    rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    have h1 := s45_abs_pair_empirical_le hN1 hwbd X
    have h2 : |HRS.Whole.pair ν w| ≤ cbNorm J w :=
      HRS.MS.Tc5.tc5_pair_le (fun x => by
        rw [Real.norm_eq_abs]
        exact hwbd x)
    calc
      Real.sqrt N * |HRS.Whole.pair (HRS.Whole.empirical X) w -
          HRS.Whole.pair ν w| ≤
        Real.sqrt N * (|HRS.Whole.pair (HRS.Whole.empirical X) w| +
          |HRS.Whole.pair ν w|) :=
        mul_le_mul_of_nonneg_left (abs_sub _ _) (Real.sqrt_nonneg _)
      _ ≤ Real.sqrt N * (cbNorm J w + cbNorm J w) :=
        mul_le_mul_of_nonneg_left (add_le_add h1 h2) (Real.sqrt_nonneg _)
      _ = 2 * Real.sqrt N * cbNorm J w := by ring
  have hYm : Measurable Y :=
    measurable_const.mul ((s45_measurable_pair_empirical hN1 hwm).sub measurable_const)
  have hYψint : Integrable (fun X : EucConfig p.d N => Y X * ψ (W X)) P :=
    Integrable.of_bound (hYm.mul hψWm).aestronglyMeasurable
      (2 * Real.sqrt N * cbNorm J w)
      (Filter.Eventually.of_forall fun X => by
        rw [Real.norm_eq_abs, abs_mul]
        calc
          |Y X| * |ψ (W X)| ≤ (2 * Real.sqrt N * cbNorm J w) * 1 :=
            mul_le_mul (hYbd X) (hψWbd X) (abs_nonneg _)
              (by positivity)
          _ = 2 * Real.sqrt N * cbNorm J w := mul_one _)
  have hCf : fp81s21_initial_Cf F j k =
      HRS.Whole.pair (r26t3_mu R 0) w := by
    calc
      fp81s21_initial_Cf F j k =
          ∫ x, w x ∂(r26t3_mu R 0) := by
        simpa [w] using fp81s21_initial_Cf_eq_wF E hγ hφ F j k
      _ = HRS.Whole.pair (r26t3_mu R 0) w := rfl
  have hA1 : fp81s21_initial_Aterm F N f (j, k) =
      -(∫ X, Y X * ψ (W X) ∂P) - β0 * ∫ X, ψ (W X) ∂P := by
    unfold fp81s21_initial_Aterm
    simp only
    rw [← integral_const_mul, ← integral_const_mul, ← integral_neg, ← integral_sub]
    · refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
      simp only [Y, β0, s45_Yi, hCf]
      ring
    · exact hYψint.neg
    · exact hψWint.const_mul _
  have hEx : HRS.Whole.IsExchangeable P := by
    dsimp [P]
    rw [← E.law_eq N]
    exact (E.static N hN).exch
  have hEmp : ∫ X, HRS.Whole.pair (HRS.Whole.empirical X) w ∂P =
      HRS.Whole.pair ν w :=
    s45_E_pair_empirical hN1 hEx hwm hwbd
  have hcfBias := fp81s21_initial_Cf_bias_s48 E hγ hφ F N hN j k
  have hcfBias' :
      |HRS.Whole.pair ν w - fp81s21_initial_Cf F j k| ≤
        E.Cs * HRS.MS.S48.s48_Q (r26t3_mu R 0) J w / (N : ℝ) := by
    dsimp [P, ν, w] at hEmp ⊢
    rw [← hEmp]
    exact hcfBias
  have hmargBias := fp81s21_initial_marginal_bias_s48 E hN (J := J) hwcb.1
  have hmargBias' :
      |HRS.Whole.pair ν w - fp81s21_initial_Cf F j k| ≤
        E.Cs * HRS.MS.S48.s48_Q (r26t3_mu R 0) J w / (N : ℝ) := by
    rw [hCf]
    simpa [ν, w] using hmargBias
  have hQcb : HRS.MS.S48.s48_Q (r26t3_mu R 0) J w ≤
      ((J : ℝ) + 1) * cbNorm J w := by
    simpa [J, w] using fp81s21_s48_Q_le_cb
      (μ := r26t3_mu R 0) (w := w) hwcb.1
  have hDiff : |HRS.Whole.pair ν w - fp81s21_initial_Cf F j k| ≤
      E.Cs * ((J : ℝ) + 1) * cbNorm J w / (N : ℝ) := by
    have hboth :
        max |HRS.Whole.pair ν w - fp81s21_initial_Cf F j k|
            |HRS.Whole.pair ν w - fp81s21_initial_Cf F j k| ≤
          E.Cs * HRS.MS.S48.s48_Q (r26t3_mu R 0) J w / (N : ℝ) :=
      max_le hmargBias' hcfBias'
    have hbase : |HRS.Whole.pair ν w - fp81s21_initial_Cf F j k| ≤
        E.Cs * HRS.MS.S48.s48_Q (r26t3_mu R 0) J w / (N : ℝ) :=
      (le_max_left _ _).trans hboth
    calc
      _ ≤ E.Cs * HRS.MS.S48.s48_Q (r26t3_mu R 0) J w / (N : ℝ) := hbase
      _ ≤ E.Cs * ((J : ℝ) + 1) * cbNorm J w / (N : ℝ) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        calc
          E.Cs * HRS.MS.S48.s48_Q (r26t3_mu R 0) J w ≤
              E.Cs * (((J : ℝ) + 1) * cbNorm J w) :=
            mul_le_mul_of_nonneg_left hQcb hCs
          _ = E.Cs * ((J : ℝ) + 1) * cbNorm J w := by ring
  have hβ0 : |β0| ≤ E.Cs * ((J : ℝ) + 1) * Kw *
      (b j * b k) / Real.sqrt N := by
    have hsq : Real.sqrt N * Real.sqrt N = (N : ℝ) :=
      Real.mul_self_sqrt hN0.le
    dsimp [β0]
    rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    calc
      Real.sqrt N * |HRS.Whole.pair ν w - fp81s21_initial_Cf F j k| ≤
          Real.sqrt N * (E.Cs * ((J : ℝ) + 1) * cbNorm J w / (N : ℝ)) :=
        mul_le_mul_of_nonneg_left hDiff (Real.sqrt_nonneg _)
      _ = E.Cs * ((J : ℝ) + 1) * cbNorm J w / Real.sqrt N := by
        rw [eq_div_iff hsqN.ne']
        calc
          Real.sqrt N * (E.Cs * ((J : ℝ) + 1) * cbNorm J w / (N : ℝ)) *
              Real.sqrt N =
            (Real.sqrt N * Real.sqrt N) *
              (E.Cs * ((J : ℝ) + 1) * cbNorm J w) / (N : ℝ) := by ring
          _ = E.Cs * ((J : ℝ) + 1) * cbNorm J w := by rw [hsq]; field_simp
      _ ≤ E.Cs * ((J : ℝ) + 1) * Kw * (b j * b k) / Real.sqrt N := by
        apply div_le_div_of_nonneg_right _ hsqN.le
        calc
          E.Cs * ((J : ℝ) + 1) * cbNorm J w ≤
              E.Cs * ((J : ℝ) + 1) * (Kw * (b j * b k)) :=
            mul_le_mul_of_nonneg_left hcw (by positivity)
          _ = E.Cs * ((J : ℝ) + 1) * Kw * (b j * b k) := by ring
  have hψint : |∫ X, ψ (W X) ∂P| ≤ 1 := by
    have hh := norm_integral_le_of_norm_le_const (μ := P)
      (f := fun X : EucConfig p.d N => ψ (W X)) (C := 1)
      (Filter.Eventually.of_forall fun X => by
        rw [Real.norm_eq_abs]
        exact hψWbd X)
    simpa [Real.norm_eq_abs] using hh
  have hYerr :
      |(∫ X, Y X * ψ (W X) ∂P) -
        ∑' m, fp81s21_initial_kap (R := R) w φ m *
          ∫ z, S99.pd ψ m z ∂G| ≤ KL * Kw * (b j * b k) / Real.sqrt N := by
    have hh := hYlin N hN (w := w) hwcb.1 (ψ := ψ) hψ
    have hh' :
        |(∫ X, Y X * ψ (W X) ∂P) -
          ∑' m, fp81s21_initial_kap (R := R) w φ m *
            ∫ z, S99.pd ψ m z ∂G| ≤ KL * cbNorm J w / Real.sqrt N := by
      simpa [Y, P, ν, W, w] using hh
    calc
      _ ≤ KL * cbNorm J w / Real.sqrt N := hh'
      _ ≤ KL * Kw * (b j * b k) / Real.sqrt N := by
        apply div_le_div_of_nonneg_right _ hsqN.le
        calc
          KL * cbNorm J w ≤ KL * (Kw * (b j * b k)) :=
            mul_le_mul_of_nonneg_left hcw hKL0
          _ = KL * Kw * (b j * b k) := by ring
  have hdecomp :
      fp81s21_initial_Aterm F N f (j, k) -
          fp81s21_initial_Alim F G f (j, k) =
        -((∫ X, Y X * ψ (W X) ∂P) -
          ∑' m, fp81s21_initial_kap (R := R) w φ m *
            ∫ z, S99.pd ψ m z ∂G) - β0 * ∫ X, ψ (W X) ∂P := by
    rw [hA1]
    simp only [fp81s21_initial_Alim, ψ]
    ring
  have htriangle :
      |-((∫ X, Y X * ψ (W X) ∂P) -
          ∑' m, fp81s21_initial_kap (R := R) w φ m *
            ∫ z, S99.pd ψ m z ∂G) - β0 * ∫ X, ψ (W X) ∂P| ≤
        |(∫ X, Y X * ψ (W X) ∂P) -
          ∑' m, fp81s21_initial_kap (R := R) w φ m *
            ∫ z, S99.pd ψ m z ∂G| + |β0| := by
    calc
      _ ≤ |(∫ X, Y X * ψ (W X) ∂P) -
            ∑' m, fp81s21_initial_kap (R := R) w φ m *
              ∫ z, S99.pd ψ m z ∂G| +
          |β0 * ∫ X, ψ (W X) ∂P| := by
        simpa only [abs_neg] using abs_sub
          (-(∫ X, Y X * ψ (W X) ∂P -
            ∑' m, fp81s21_initial_kap (R := R) w φ m *
              ∫ z, S99.pd ψ m z ∂G))
          (β0 * ∫ X, ψ (W X) ∂P)
      _ ≤ |(∫ X, Y X * ψ (W X) ∂P) -
            ∑' m, fp81s21_initial_kap (R := R) w φ m *
              ∫ z, S99.pd ψ m z ∂G| + |β0| * 1 :=
        add_le_add le_rfl (by
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left hψint (abs_nonneg β0))
      _ = _ := by rw [abs_mul]; ring
  calc
    |fp81s21_initial_Aterm F N f (j, k) - fp81s21_initial_Alim F G f (j, k)| =
        |-((∫ X, Y X * ψ (W X) ∂P) -
          ∑' m, fp81s21_initial_kap (R := R) w φ m *
            ∫ z, S99.pd ψ m z ∂G) - β0 * ∫ X, ψ (W X) ∂P| := by rw [hdecomp]
    _ ≤ KL * Kw * (b j * b k) / Real.sqrt N +
        E.Cs * ((J : ℝ) + 1) * Kw * (b j * b k) / Real.sqrt N := by
      exact htriangle.trans (add_le_add hYerr hβ0)
    _ = KA * (cbNorm (fp81s21_J1 p.d) (φ j) *
        cbNorm (fp81s21_J1 p.d) (φ k)) / Real.sqrt N := by
      simp only [KA, b]
      ring
#print axioms fp81s21_initial_A_rate_from_common_Ylin

end HRS.Fp81.S21

end
