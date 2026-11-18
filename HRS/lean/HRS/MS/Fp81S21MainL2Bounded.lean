import HRS.MS.Fp81S21UnifLinSeries5
import HRS.MS.Fp81S21ULimBUniform2
import HRS.MS.Fp81S21InitialMainL22

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
noncomputable section

namespace HRS.Fp81.S21

open S99
open HRS.Whole
open HRS (Euc MemCb cbNorm)
open HRS.MS.R26T3

/-- Uniform convergence of the linear coefficient series on a bounded qwin interval,
using the same compatible potential family as the quadratic series. -/
theorem fp81s21_initial_Aseries_uniform_qwin
    {p : Parameters} {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    (R : Trajectory p δ) (E : InitialSteinEnv R) (hγ : 0 < p.γ)
    (F : fp81s21_CompatPotentialFamily R)
    {K Cwin S : ℝ} (hK : 0 ≤ K) (hFK : ∀ a : Set.Ici (0 : ℝ), (F a).K ≤ K)
    (hCwin : 0 ≤ Cwin) (hS : 0 ≤ S)
    (M : ℝ) (hM : 0 ≤ M)
    (hphi : ∀ a : Set.Icc (0 : ℝ) M,
      IsSummableFeatureFamily (fp81s21_J1 p.d) (r26t3_qwin R (a : ℝ)))
    (hbound : ∀ a : Set.Icc (0 : ℝ) M, ∀ j : ℕ,
      cbNorm (fp81s21_J1 p.d) (r26t3_qwin R (a : ℝ) j) ≤
        Cwin * r26t3_feature_weight p.d j)
    (hSum : ∀ a : Set.Icc (0 : ℝ) M,
      featureSum (fp81s21_J1 p.d) (r26t3_qwin R (a : ℝ)) ≤ S) :
    ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ,
      ∀ N : ℕ, N0 ≤ N → 2 ≤ N →
        ∀ a : ℝ, ∀ ha : a ∈ Set.Icc (0 : ℝ) M,
          ∀ {G : Measure SeqL2} [IsProbabilityMeasure G],
            IsCenteredGaussianSeq G (fun i j =>
              HRS.Whole.susceptibilityCov (rieszKernel p.d p.s)
                (r26t3_mu R 0) p.γ
                (r26t3_qwin R a i) (r26t3_qwin R a j)) →
            ∀ f : SeqL2 → ℝ, SteinCl f →
              |(∑' q : ℕ × ℕ, fp81s21_initial_Aterm
                    (F ⟨a, ha.1⟩) N f q) -
                (∑' q : ℕ × ℕ, fp81s21_initial_Alim
                    (F ⟨a, ha.1⟩) G f q)| ≤ ε := by
  let φ : Set.Icc (0 : ℝ) M → ℕ → Euc p.d → ℝ :=
    fun a j => r26t3_qwin R (a : ℝ) j
  let Fam : ∀ a : Set.Icc (0 : ℝ) M, InitialFamData R (φ a) :=
    fun a => F ⟨(a : ℝ), a.2.1⟩
  have hphi' : ∀ a, IsSummableFeatureFamily (fp81s21_J1 p.d) (φ a) := by
    intro a
    simpa [φ] using hphi a
  have hFamK : ∀ a, (Fam a).K ≤ K := by
    intro a
    exact hFK ⟨(a : ℝ), a.2.1⟩
  obtain ⟨Kclt, hKclt, hCLT⟩ :=
    fp81s21_initial_clt_uniform_of_featureSum_bound hδh R hγ φ hphi' S hS
      (by intro a; simpa [φ] using hSum a)
  obtain ⟨KL, hKL, hYlin⟩ :=
    fp81s21_initial_Ylin_uniform_of_common_CLT hδ hδh R E hγ φ hphi' Fam
      S hS (by intro a; simpa [φ] using hSum a) Kclt hKclt hCLT
  obtain ⟨KA, hKA, -, hA⟩ :=
    fp81s21_initial_A_rate_uniform_of_common_Ylin hδ hδh R E hγ φ hphi' Fam
      K KL hK hKL hFamK hYlin
  let w : ℕ → ℝ := fun j => Cwin * r26t3_feature_weight p.d j
  have hw0 : ∀ j, 0 ≤ w j := by
    intro j
    dsimp [w]
    apply mul_nonneg hCwin
    dsimp [r26t3_feature_weight]
    apply mul_nonneg
    · apply Real.rpow_nonneg
      positivity
    · exact Real.rpow_nonneg (oscEigenvalue_pos _).le _
  have hwSum : Summable w :=
    (fp81s21_qwin_weight_summable p).mul_left Cwin
  have hpair : Summable (fun q : ℕ × ℕ => w q.1 * w q.2) :=
    Summable.mul_of_nonneg hwSum hwSum (fun j => hw0 j) (fun j => hw0 j)
  let P : ℝ := ∑' q : ℕ × ℕ, w q.1 * w q.2
  have hP0 : 0 ≤ P := by
    dsimp [P]
    exact tsum_nonneg fun q => mul_nonneg (hw0 q.1) (hw0 q.2)
  let Jfac : ℝ := ((fp81s21_k0 p.d : ℝ) + 1) *
    2 ^ fp81s21_k0 p.d
  let CAlim : ℝ := Jfac * (p.γ⁻¹ * K) * K * S
  have hJfac : 0 ≤ Jfac := by
    dsimp [Jfac]
    positivity
  have hCAlim : 0 ≤ CAlim := by
    dsimp [CAlim]
    positivity
  intro ε hε
  let D : ℝ := KA * P
  have hD : 0 ≤ D := by dsimp [D]; positivity
  let τ : ℝ := ε / 2
  have hτ : 0 < τ := by dsimp [τ]; positivity
  let N0 : ℕ := max 2 (⌈(D / τ) ^ 2⌉₊ + 1)
  refine ⟨N0, ?_⟩
  intro N hN0 hN2 a ha G _ hG f hf
  let aI : Set.Icc (0 : ℝ) M := ⟨a, ha⟩
  let a0 : Set.Ici (0 : ℝ) := ⟨a, ha.1⟩
  let Fa : InitialFamData R (r26t3_qwin R a) := F a0
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hsqrt : 0 < Real.sqrt N := Real.sqrt_pos.2 hNpos
  have hsqrt1 : (1 : ℝ) ≤ Real.sqrt N := by
    rw [Real.one_le_sqrt]
    exact_mod_cast (show 1 ≤ N by omega)
  have htermLim : ∀ q : ℕ × ℕ,
      |fp81s21_initial_Alim Fa G f q| ≤ CAlim * (w q.1 * w q.2) := by
    intro q
    have h := fp81s21_initial_Alim_bound E hγ
      (by simpa [φ] using hphi aI) Fa (G := G) hf q
    have hcoef :
        Jfac * (p.γ⁻¹ * Fa.K) * Fa.K *
          featureSum (fp81s21_J1 p.d) (r26t3_qwin R a) ≤ CAlim := by
      have hFaK : Fa.K ≤ K := hFK a0
      have hFaS : featureSum (fp81s21_J1 p.d) (r26t3_qwin R a) ≤ S := hSum aI
      have hFaS0 : 0 ≤ featureSum (fp81s21_J1 p.d) (r26t3_qwin R a) := by
        dsimp [featureSum]
        exact tsum_nonneg fun j => HRS.MS.Tc5.tc5_cb_nonneg _ _
      have hγinv : 0 ≤ p.γ⁻¹ := inv_nonneg.2 hγ.le
      have hFaK0 : 0 ≤ Fa.K := Fa.hK
      calc
        Jfac * (p.γ⁻¹ * Fa.K) * Fa.K *
            featureSum (fp81s21_J1 p.d) (r26t3_qwin R a) ≤
          Jfac * (p.γ⁻¹ * K) * Fa.K *
            featureSum (fp81s21_J1 p.d) (r26t3_qwin R a) := by
              gcongr
        _ ≤ Jfac * (p.γ⁻¹ * K) * K *
            featureSum (fp81s21_J1 p.d) (r26t3_qwin R a) := by
              gcongr
        _ ≤ Jfac * (p.γ⁻¹ * K) * K * S := by
              gcongr
    have hprod :
        cbNorm (fp81s21_J1 p.d) (r26t3_qwin R a q.1) *
            cbNorm (fp81s21_J1 p.d) (r26t3_qwin R a q.2) ≤
          w q.1 * w q.2 := by
      exact mul_le_mul (hbound aI q.1) (hbound aI q.2)
        (HRS.MS.Tc5.tc5_cb_nonneg _ _) (hw0 q.1)
    have h' :
        |fp81s21_initial_Alim Fa G f q| ≤
          (Jfac * (p.γ⁻¹ * Fa.K) * Fa.K *
            featureSum (fp81s21_J1 p.d) (r26t3_qwin R a)) *
            (cbNorm (fp81s21_J1 p.d) (r26t3_qwin R a q.1) *
              cbNorm (fp81s21_J1 p.d) (r26t3_qwin R a q.2)) := by
      simpa [φ, Fam, Fa, featureSum, Jfac] using h
    calc
      |fp81s21_initial_Alim Fa G f q| ≤ _ := h'
      _ ≤ CAlim * (w q.1 * w q.2) := by
        dsimp [CAlim]
        have hprod0 : 0 ≤
            cbNorm (fp81s21_J1 p.d) (r26t3_qwin R a q.1) *
              cbNorm (fp81s21_J1 p.d) (r26t3_qwin R a q.2) :=
          mul_nonneg (HRS.MS.Tc5.tc5_cb_nonneg _ _)
            (HRS.MS.Tc5.tc5_cb_nonneg _ _)
        exact mul_le_mul hcoef hprod hprod0 hCAlim
  have hcoeff : ∀ q : ℕ × ℕ,
      |fp81s21_initial_Aterm Fa N f q - fp81s21_initial_Alim Fa G f q| ≤
        (KA / Real.sqrt N) * (w q.1 * w q.2) := by
    intro q
    have hRate := hA aI hG N hN2 f hf q
    have hprod :
        cbNorm (fp81s21_J1 p.d) (r26t3_qwin R a q.1) *
            cbNorm (fp81s21_J1 p.d) (r26t3_qwin R a q.2) ≤
          w q.1 * w q.2 := by
      exact mul_le_mul (hbound aI q.1) (hbound aI q.2)
        (HRS.MS.Tc5.tc5_cb_nonneg _ _) (hw0 q.1)
    calc
      |fp81s21_initial_Aterm Fa N f q - fp81s21_initial_Alim Fa G f q| ≤
          KA * (cbNorm (fp81s21_J1 p.d) (r26t3_qwin R a q.1) *
            cbNorm (fp81s21_J1 p.d) (r26t3_qwin R a q.2)) /
              Real.sqrt N := hRate
      _ ≤ KA * (w q.1 * w q.2) / Real.sqrt N :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hprod hKA) hsqrt.le
      _ = (KA / Real.sqrt N) * (w q.1 * w q.2) := by ring
  have hAtermBound : ∀ q : ℕ × ℕ,
      |fp81s21_initial_Aterm Fa N f q| ≤
        (CAlim + KA) * (w q.1 * w q.2) := by
    intro q
    have hRate := hA aI hG N hN2 f hf q
    have hprod :
        cbNorm (fp81s21_J1 p.d) (r26t3_qwin R a q.1) *
            cbNorm (fp81s21_J1 p.d) (r26t3_qwin R a q.2) ≤
          w q.1 * w q.2 := by
      exact mul_le_mul (hbound aI q.1) (hbound aI q.2)
        (HRS.MS.Tc5.tc5_cb_nonneg _ _) (hw0 q.1)
    have hRate' :
        |fp81s21_initial_Aterm Fa N f q - fp81s21_initial_Alim Fa G f q| ≤
          KA * (w q.1 * w q.2) := by
      have hcoef0 : 0 ≤ KA * (w q.1 * w q.2) :=
        mul_nonneg hKA (mul_nonneg (hw0 q.1) (hw0 q.2))
      have hsmall : KA * (w q.1 * w q.2) / Real.sqrt N ≤
          KA * (w q.1 * w q.2) := by
        rw [div_le_iff₀ hsqrt]
        calc
          KA * (w q.1 * w q.2) =
              (KA * (w q.1 * w q.2)) * 1 := by rw [mul_one]
          _ ≤ (KA * (w q.1 * w q.2)) * Real.sqrt N :=
            mul_le_mul_of_nonneg_left hsqrt1 hcoef0
      calc
        |fp81s21_initial_Aterm Fa N f q - fp81s21_initial_Alim Fa G f q| ≤
            KA * (cbNorm (fp81s21_J1 p.d) (r26t3_qwin R a q.1) *
              cbNorm (fp81s21_J1 p.d) (r26t3_qwin R a q.2)) / Real.sqrt N := hRate
        _ ≤ KA * (w q.1 * w q.2) / Real.sqrt N :=
          div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hprod hKA) hsqrt.le
        _ ≤ KA * (w q.1 * w q.2) := hsmall
    have htri := abs_add_le (fp81s21_initial_Alim Fa G f q)
      (fp81s21_initial_Aterm Fa N f q - fp81s21_initial_Alim Fa G f q)
    have htri' : |fp81s21_initial_Aterm Fa N f q| ≤
        |fp81s21_initial_Alim Fa G f q| +
          |fp81s21_initial_Aterm Fa N f q - fp81s21_initial_Alim Fa G f q| := by
      simpa using htri
    calc
      |fp81s21_initial_Aterm Fa N f q| ≤ _ := htri'
      _ ≤ CAlim * (w q.1 * w q.2) + KA * (w q.1 * w q.2) :=
        add_le_add (htermLim q) hRate'
      _ = (CAlim + KA) * (w q.1 * w q.2) := by ring
  have hAtermSummable : Summable (fun q : ℕ × ℕ =>
      fp81s21_initial_Aterm Fa N f q) :=
    Summable.of_norm_bounded (hpair.mul_left (CAlim + KA)) (fun q => by
      rw [Real.norm_eq_abs]
      exact hAtermBound q)
  have hAlimSummable : Summable (fun q : ℕ × ℕ =>
      fp81s21_initial_Alim Fa G f q) :=
    Summable.of_norm_bounded (hpair.mul_left (CAlim + KA)) (fun q => by
      rw [Real.norm_eq_abs]
      have hh := htermLim q
      have hle : CAlim * (w q.1 * w q.2) ≤
          (CAlim + KA) * (w q.1 * w q.2) := by
        exact mul_le_mul_of_nonneg_right (by linarith [hKA])
          (mul_nonneg (hw0 q.1) (hw0 q.2))
      exact hh.trans hle)
  have hmajor : HasSum (fun q : ℕ × ℕ =>
      (KA / Real.sqrt N) * (w q.1 * w q.2))
      ((KA / Real.sqrt N) * P) := by
    simpa [P] using hpair.hasSum.mul_left (KA / Real.sqrt N)
  have hsumBound := tsum_of_norm_bounded (f := fun q : ℕ × ℕ =>
      fp81s21_initial_Aterm Fa N f q - fp81s21_initial_Alim Fa G f q)
    hmajor (fun q => by
      rw [Real.norm_eq_abs]
      exact hcoeff q)
  rw [Real.norm_eq_abs] at hsumBound
  have hseries :
      |(∑' q : ℕ × ℕ, fp81s21_initial_Aterm Fa N f q) -
        (∑' q : ℕ × ℕ, fp81s21_initial_Alim Fa G f q)| ≤ D / Real.sqrt N := by
    rw [← hAtermSummable.tsum_sub hAlimSummable]
    calc
      |∑' q : ℕ × ℕ, (fp81s21_initial_Aterm Fa N f q -
          fp81s21_initial_Alim Fa G f q)| ≤ (KA / Real.sqrt N) * P := hsumBound
      _ = D / Real.sqrt N := by dsimp [D]; ring
  have hceil : (D / τ) ^ 2 ≤ (⌈(D / τ) ^ 2⌉₊ : ℝ) := Nat.le_ceil _
  have hceilN : ((⌈(D / τ) ^ 2⌉₊ + 1 : ℕ) : ℝ) ≤ N := by
    exact_mod_cast (le_max_right 2 (⌈(D / τ) ^ 2⌉₊ + 1)).trans hN0
  push_cast at hceilN
  have hsqN : (D / τ) ^ 2 ≤ (N : ℝ) := by linarith
  have hscale : D / τ ≤ Real.sqrt N := Real.le_sqrt_of_sq_le hsqN
  have hsmall : D / Real.sqrt N ≤ τ := by
    rw [div_le_iff₀ hsqrt]
    have hh : D ≤ Real.sqrt N * τ := (div_le_iff₀ hτ).1 hscale
    nlinarith
  have hfinal := hseries.trans hsmall
  dsimp [τ] at hfinal
  linarith

#print axioms fp81s21_initial_Aseries_uniform_qwin

end HRS.Fp81.S21

end
