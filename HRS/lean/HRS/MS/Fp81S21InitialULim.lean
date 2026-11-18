import HRS.MS.Fp81S21InitialLinear3
import HRS.MS.Fp81S21InitialFR2
import HRS.MS.R2SeAux38

open MeasureTheory Filter Topology ProbabilityTheory
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

/-!
## SOL31 packet 25b: the nonthermal uniform limit for the linear series

The proof ports `S99.s99_ULimA`.  Its coefficientwise rate is the actual-law
`fp81s21_initial_A_rate`; absolute summability is controlled by the actual
response coefficients `fp81s21_initial_kap` and the `InitialFamData.wF`
envelope.  Both the limit coefficients and the finite-N terms use the actual
initial law.
-/

/-- Uniform convergence of the actual-initial-law linear coefficient series. -/
theorem fp81s21_initial_ULimA
    {p : Parameters} {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    (R : Trajectory p δ) (E : InitialSteinEnv R) (hγ : 0 < p.γ)
    {φ : ℕ → Euc p.d → ℝ}
    (hφ : IsSummableFeatureFamily (fp81s21_J1 p.d) φ)
    (F : InitialFamData R φ)
    {G : Measure SeqL2} [IsProbabilityMeasure G]
    (hG : IsCenteredGaussianSeq G (fun i j =>
      HRS.Whole.susceptibilityCov (HRS.Whole.rieszKernel p.d p.s)
        (r26t3_mu R 0) p.γ
        (φ i) (φ j))) :
    ULim
      (fun N f => if 2 ≤ N then ∑' q : ℕ × ℕ,
        fp81s21_initial_Aterm F N f q else 0)
      (fun f => ∑' q : ℕ × ℕ, fp81s21_initial_Alim F G f q) := by
  obtain ⟨KA, hKA0, hA⟩ :=
    fp81s21_initial_A_rate hδ hδh R E hγ hφ F hG
  let b : ℕ → ℝ := fun j => cbNorm (fp81s21_J1 p.d) (φ j)
  have hb0 : ∀ j, 0 ≤ b j := fun j => by
    dsimp [b]
    exact HRS.MS.Tc5.tc5_cb_nonneg _ _
  have hbs : Summable b := hφ.2
  have hbb : Summable (fun q : ℕ × ℕ => b q.1 * b q.2) := by
    exact Summable.mul_of_nonneg hbs hbs (fun j => hb0 j) (fun j => hb0 j)
  set Sb : ℝ := ∑' j, b j
  have hSb0 : 0 ≤ Sb := tsum_nonneg hb0
  have hFK0 : 0 ≤ F.K := F.hK
  let Kw : ℝ := ((fp81s21_k0 p.d : ℝ) + 1) * 2 ^ fp81s21_k0 p.d *
    (p.γ⁻¹ * F.K)
  have hKw0 : 0 ≤ Kw := by
    dsimp [Kw]
    positivity
  let C : ℝ := Kw * F.K
  have hC0 : 0 ≤ C := mul_nonneg hKw0 hFK0
  have hAlim : ∀ f, SteinCl f → ∀ q : ℕ × ℕ,
      |fp81s21_initial_Alim F G f q| ≤ C * Sb * (b q.1 * b q.2) := by
    intro f hf q
    obtain ⟨hw, hwbd⟩ := fp81s21_initial_wF_cb hφ.1 F hγ q.1 q.2
    have hkap : ∀ m, |fp81s21_initial_kap (R := R)
        (InitialFamData.wF F q.1 q.2) φ m| ≤
        Kw * (b q.1 * b q.2) * (F.K * b m) := by
      intro m
      haveI hμ : IsProbabilityMeasure (r26t3_mu R 0) :=
        HRS.Whole.Q34.isProbabilityMeasure_nu E.reference.prob
      let w := InitialFamData.wF F q.1 q.2
      let g : Euc p.d → ℝ := fun x => w x * r26t3_a R (φ m) x
      have hwabs : ∀ x, |w x| ≤ cbNorm (fp81s21_k0 p.d) w := by
        intro x
        exact HRS.MS.Tc5.tc5_cb_sup_le hw x
      have haabs : ∀ x, |r26t3_a R (φ m) x| ≤ F.K * b m := by
        intro x
        have h := F.anorm m
        have hs := HRS.MS.Tc5.tc5_cb_sup_le (F.amem m) x
        calc
          |r26t3_a R (φ m) x| ≤ cbNorm (fp81s21_k0 p.d) (r26t3_a R (φ m)) := by
            simpa [Real.norm_eq_abs] using hs
          _ ≤ F.K * b m := by simpa [b] using h
      have hK0 : 0 ≤ cbNorm (fp81s21_k0 p.d) w :=
        HRS.MS.Tc5.tc5_cb_nonneg _ _
      have hcb : cbNorm (fp81s21_k0 p.d) w * (F.K * b m) ≥ 0 :=
        mul_nonneg hK0 (mul_nonneg hFK0 (hb0 m))
      have hgmeas : Measurable g :=
        (hw.1.continuous.mul (F.amem m).1.continuous).measurable
      have hgbd : ∀ x, ‖g x‖ ≤ cbNorm (fp81s21_k0 p.d) w * (F.K * b m) := by
        intro x
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (hwabs x) (haabs x) (abs_nonneg _) hK0
      have hgint : Integrable g (r26t3_mu R 0) :=
        Integrable.of_bound hgmeas.aestronglyMeasurable _
          (Filter.Eventually.of_forall hgbd)
      have hnorm := norm_integral_le_of_norm_le_const (μ := r26t3_mu R 0)
        (f := g) (C := cbNorm (fp81s21_k0 p.d) w * (F.K * b m))
        (Filter.Eventually.of_forall hgbd)
      rw [Real.norm_eq_abs] at hnorm
      have hKwbd : cbNorm (fp81s21_k0 p.d) w ≤
          ((fp81s21_k0 p.d : ℝ) + 1) * 2 ^ fp81s21_k0 p.d *
            (p.γ⁻¹ * F.K * b q.1) * b q.2 := by
        simpa [b] using hwbd
      have hWnorm : cbNorm (fp81s21_k0 p.d) w ≤ Kw * (b q.1 * b q.2) := by
        calc
          _ ≤ ((fp81s21_k0 p.d : ℝ) + 1) * 2 ^ fp81s21_k0 p.d *
              (p.γ⁻¹ * F.K * b q.1) * b q.2 := hKwbd
          _ = Kw * (b q.1 * b q.2) := by dsimp [Kw]; ring
      calc
        |fp81s21_initial_kap (R := R) w φ m| ≤
            cbNorm (fp81s21_k0 p.d) w * (F.K * b m) := by
          simpa [g, fp81s21_initial_kap] using hnorm
        _ ≤ (Kw * (b q.1 * b q.2)) * (F.K * b m) := by
          exact mul_le_mul_of_nonneg_right hWnorm
            (mul_nonneg hFK0 (hb0 m))
        _ = Kw * (b q.1 * b q.2) * (F.K * b m) := by ring
    have hGb : ∀ m, |∫ z, S99.pd (S99.pd (S99.pd f q.1) q.2) m z ∂G| ≤ 1 := by
      intro m
      have h := norm_integral_le_of_norm_le_const (μ := G)
        (f := S99.pd (S99.pd (S99.pd f q.1) q.2) m) (C := 1)
        (Filter.Eventually.of_forall fun z => by
          rw [Real.norm_eq_abs]
          exact (((hf.pd q.1).pd q.2).pd m).abs_le z)
      simpa [Real.norm_eq_abs] using h
    unfold fp81s21_initial_Alim
    rw [abs_neg]
    have hg : HasSum (fun m => Kw * (b q.1 * b q.2) * F.K * b m)
        (Kw * (b q.1 * b q.2) * F.K * Sb) := hbs.hasSum.mul_left _
    have hsum := tsum_of_norm_bounded hg
      (f := fun m => fp81s21_initial_kap (R := R)
        (InitialFamData.wF F q.1 q.2) φ m *
          ∫ z, S99.pd (S99.pd (S99.pd f q.1) q.2) m z ∂G)
      (fun m => by
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
        calc
          _ ≤ (Kw * (b q.1 * b q.2) * (F.K * b m)) * 1 :=
            mul_le_mul (hkap m) (hGb m) (abs_nonneg _)
              (by have := hb0 m; have := hb0 q.1; have := hb0 q.2; positivity)
          _ = _ := by ring)
    rw [Real.norm_eq_abs] at hsum
    calc
      |∑' m, fp81s21_initial_kap (R := R)
          (InitialFamData.wF F q.1 q.2) φ m *
            ∫ z, S99.pd (S99.pd (S99.pd f q.1) q.2) m z ∂G| ≤
          Kw * (b q.1 * b q.2) * F.K * Sb := hsum
      _ = C * Sb * (b q.1 * b q.2) := by
        dsimp [C]
        ring
  obtain ⟨e⟩ : Nonempty (ℕ ≃ ℕ × ℕ) :=
    ⟨(Denumerable.eqv (ℕ × ℕ)).symm⟩
  let M : ℕ × ℕ → ℝ := fun q =>
    (KA + C * Sb) * (b q.1 * b q.2)
  have hMs : Summable (fun n => M (e n)) :=
    (e.summable_iff (f := M)).2 (hbb.mul_left _)
  have hMn : ∀ q, 0 ≤ M q := by
    intro q
    dsimp [M]
    exact mul_nonneg (add_nonneg hKA0 (mul_nonneg hC0 hSb0))
      (mul_nonneg (hb0 q.1) (hb0 q.2))
  have hu : ∀ n N f, SteinCl f →
      |(if 2 ≤ N then fp81s21_initial_Aterm F N f (e n) else 0)| ≤ M (e n) := by
    intro n N f hf
    by_cases hN : 2 ≤ N
    · simp only [hN, ite_true]
      have h1 := hA N hN f hf (e n)
      have h2 := hAlim f hf (e n)
      have hN0 : (1 : ℝ) ≤ Real.sqrt N := by
        rw [Real.one_le_sqrt]
        exact_mod_cast (show 1 ≤ N by omega)
      have hsq : 0 < Real.sqrt N := by positivity
      have h3 : KA * (b (e n).1 * b (e n).2) / Real.sqrt N ≤
          KA * (b (e n).1 * b (e n).2) := by
        rw [div_le_iff₀ hsq]
        have hcoef : 0 ≤ KA * (b (e n).1 * b (e n).2) :=
          mul_nonneg hKA0 (mul_nonneg (hb0 _) (hb0 _))
        nlinarith
      calc
        |fp81s21_initial_Aterm F N f (e n)| ≤
            |fp81s21_initial_Alim F G f (e n)| +
              |fp81s21_initial_Aterm F N f (e n) -
                fp81s21_initial_Alim F G f (e n)| := by
          have hh := abs_add_le (fp81s21_initial_Alim F G f (e n))
            (fp81s21_initial_Aterm F N f (e n) - fp81s21_initial_Alim F G f (e n))
          simpa using hh
        _ ≤ M (e n) := by
          dsimp [M]
          nlinarith [h2, h1, h3]
    · simp [hN, hMn]
  have hL : ∀ n f, SteinCl f →
      |fp81s21_initial_Alim F G f (e n)| ≤ M (e n) := by
    intro n f hf
    have h := hAlim f hf (e n)
    dsimp [M]
    have h0 : 0 ≤ KA * (b (e n).1 * b (e n).2) :=
      mul_nonneg hKA0 (mul_nonneg (hb0 _) (hb0 _))
    nlinarith
  have hpoint : ∀ n, ULim
      (fun N f => if 2 ≤ N then fp81s21_initial_Aterm F N f (e n) else 0)
      (fun f => fp81s21_initial_Alim F G f (e n)) := by
    intro n
    apply S99.ULim.of_rate_ge2 (K := KA * (b (e n).1 * b (e n).2))
    · exact mul_nonneg hKA0 (mul_nonneg (hb0 _) (hb0 _))
    · intro N hN f hf
      simp only [hN, ite_true]
      exact hA N hN f hf (e n)
  have hmain := S99.s99_ULim_tsum hMs hu hL hpoint
  refine S99.ULim.congr_L (fun f hf => e.tsum_eq
    (fun q => fp81s21_initial_Alim F G f q)) ?_
  apply S99.ULim.congr (fun N f hf => ?_) hmain
  by_cases hN : 2 ≤ N
  · simp only [hN, ite_true]
    exact e.tsum_eq (fun q => fp81s21_initial_Aterm F N f q)
  · simp [hN]

#print axioms fp81s21_initial_ULimA

end HRS.Fp81.S21

end
