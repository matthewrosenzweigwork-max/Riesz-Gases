import HRS.MS.QsfAsm7

/-!
# S4.5 packet B5 (assembly), part 8: the matrices `T_n` and the covariance comparison
-/

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal RealInnerProductSpace ContDiff

noncomputable section

namespace S45

open HRS.Whole
open HRS (Euc cbNorm MemCb)

variable {d N : ℕ}

section Ctx

variable (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β Cs C c BU KR KT : ℝ}
  (ha : 0 < a) (hβ : 0 < β) (hsu : S45Setup d s a β Cs C c BU KR KT) (hN : 2 ≤ N) {J : ℕ}
  (hJ : 1 ≤ J) {φ χ : ℕ → Euc d → ℝ} {Cc : ℝ} (hCc : 0 ≤ Cc)
  (hφ : HRS.Whole.IsSummableFeatureFamily J φ)
  (hfeat : ∀ i, S45Feat d s a β (φ i) (χ i) (Cc * cbNorm J (φ i)))
  {γ : Measure SeqL2} [IsProbabilityMeasure γ]

include hd hs0 hsd hsu hN hfeat hJ hφ hβ

theorem s45_fij_facts (i j : ℕ) :
    Continuous (fun x : Euc d => ⟪gradient (χ i) x, gradient (φ j) x⟫) ∧
      ∀ x, |⟪gradient (χ i) x, gradient (φ j) x⟫| ≤ (Cc * cbNorm J (φ i)) * cbNorm J (φ j) := by
  obtain ⟨hφ1, -, hφD⟩ := s45_phi_facts hJ hφ
  exact ⟨(s45_contDiff_gradient (hfeat i).smooth).continuous.inner (s45_gradient_continuous (hφ1 j)),
    fun x => s45_inner_grad_le (hfeat i).B1 (hφD j) x⟩

theorem s45_cmat_entry
    (hγ : IsCenteredGaussianSeq γ fun i j => susceptibilityCov (rieszKernel d s)
      (thermalMeasure d s a β) β (φ i) (φ j)) (i j : ℕ) :
    ∫ w, ⟪s45_seqBasis i, w.2⟫ * ⟪s45_seqBasis j, w.2⟫ ∂((s45_P d s a β N).prod γ) =
      β⁻¹ * pair (thermalMeasure d s a β) (fun x => ⟪gradient (χ i) x, gradient (φ j) x⟫) := by
  haveI : IsProbabilityMeasure (s45_P d s a β N) := (hsu.hS N hN).prob
  obtain ⟨hφ1, hφb, hφD⟩ := s45_phi_facts hJ hφ
  rw [s45_gauss_cov (P := s45_P d s a β N) hγ i j]
  haveI : IsProbabilityMeasure (thermalMeasure d s a β) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu hsu.hT.prob
  have hφi : MemLp (φ i) 2 (thermalMeasure d s a β) :=
    MemLp.of_bound (hφ1 i).continuous.aestronglyMeasurable (cbNorm J (φ i))
      (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hφb i x)
  exact s45_cov_identity hd hs0 hsd hβ hsu.hT (hfeat i).smooth (hfeat i).B1 (hfeat i).B2 hφi
    (hfeat i).r2 (hfeat i).corr (hφ1 j) (hφb j) (hφD j)

theorem s45_Tmat_tau
    (hγ : IsCenteredGaussianSeq γ fun i j => susceptibilityCov (rieszKernel d s)
      (thermalMeasure d s a β) β (φ i) (φ j)) (n : ℕ) :
    ∫ w, HRS.traceNormMatrix (s45_Tmat d β N n φ χ w - Matrix.of fun i j : Fin n =>
        ∫ w', ⟪s45_seqBasis i, w'.2⟫ * ⟪s45_seqBasis j, w'.2⟫ ∂((s45_P d s a β N).prod γ))
      ∂((s45_P d s a β N).prod γ) ≤
      β⁻¹ * KT * Cc * (∑ i : Fin n, cbNorm J (φ i)) ^ 2 * Real.sqrt (HRS.deltaN d s N) := by
  have hN1 : 1 ≤ N := by omega
  haveI : IsProbabilityMeasure (s45_P d s a β N) := (hsu.hS N hN).prob
  set P := s45_P d s a β N with hPdef
  set μ := thermalMeasure d s a β with hμdef
  haveI : IsProbabilityMeasure μ := HRS.Whole.Q34.isProbabilityMeasure_nu hsu.hT.prob
  set δ := Real.sqrt (HRS.deltaN d s N) with hδ
  have hcb0 : ∀ i, 0 ≤ cbNorm J (φ i) := fun i => HRS.MS.Tc5.tc5_cb_nonneg J (φ i)
  set ee : Fin n → Fin n → EucConfig d N → ℝ := fun i j X =>
    |β⁻¹ * (pair (empirical X) (fun x => ⟪gradient (χ i) x, gradient (φ j) x⟫) -
      pair μ (fun x => ⟪gradient (χ i) x, gradient (φ j) x⟫))| with hee
  have hpt : ∀ w : EucConfig d N × SeqL2, HRS.traceNormMatrix (s45_Tmat d β N n φ χ w -
      Matrix.of fun i j : Fin n => ∫ w', ⟪s45_seqBasis i, w'.2⟫ * ⟪s45_seqBasis j, w'.2⟫ ∂(P.prod γ)) ≤
      ∑ i : Fin n, ∑ j : Fin n, ee i j w.1 := by
    intro w
    refine (HRS.PDE.MFLinear.traceNormMatrix_le_sum _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [Matrix.sub_apply, s45_Tmat, Matrix.of_apply]
    rw [s45_cmat_entry hd hs0 hsd hβ hsu hN hJ hφ hfeat hγ]
    simp only [hee]
    congr 1; ring
  have heeI : ∀ i j : Fin n, Integrable (ee i j) P := by
    intro i j
    obtain ⟨hc, hb⟩ := s45_fij_facts hd hs0 hsd hβ hsu hN hJ hφ hfeat i j
    refine Integrable.of_bound (C := β⁻¹ * ((Cc * cbNorm J (φ i)) * cbNorm J (φ j) +
        (Cc * cbNorm J (φ i)) * cbNorm J (φ j)))
      ((((s45_measurable_pair_empirical hN1 hc.measurable).sub measurable_const).const_mul _).abs.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun X => ?_)
    rw [Real.norm_eq_abs, hee]
    simp only [abs_abs]
    rw [abs_mul, abs_of_pos (inv_pos.2 hβ)]
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hβ.le)
    refine (abs_sub _ _).trans (add_le_add (s45_abs_pair_empirical_le hN1 hb X) ?_)
    exact HRS.MS.Tc5.tc5_pair_le (fun x => by rw [Real.norm_eq_abs]; exact hb x)
  have heeS : ∀ i j : Fin n, Integrable (fun w : EucConfig d N × SeqL2 => ee i j w.1) (P.prod γ) :=
    fun i j => s45_integrable_fst (heeI i j)
  calc ∫ w, HRS.traceNormMatrix (s45_Tmat d β N n φ χ w - Matrix.of fun i j : Fin n =>
        ∫ w', ⟪s45_seqBasis i, w'.2⟫ * ⟪s45_seqBasis j, w'.2⟫ ∂(P.prod γ)) ∂(P.prod γ)
      ≤ ∫ w, ∑ i : Fin n, ∑ j : Fin n, ee i j w.1 ∂(P.prod γ) :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun w => HRS.traceNormMatrix_nonneg _)
          (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => heeS i j)
          (Filter.Eventually.of_forall hpt)
    _ = ∑ i : Fin n, ∑ j : Fin n, ∫ X, ee i j X ∂P := by
        rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => heeS i j]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [integral_finsetSum _ fun j _ => heeS i j]
        refine Finset.sum_congr rfl fun j _ => ?_
        exact s45_integral_fst (γ := γ) (g := ee i j) (heeI i j).aestronglyMeasurable
    _ ≤ ∑ i : Fin n, ∑ j : Fin n, β⁻¹ * KT * ((Cc * cbNorm J (φ i)) * cbNorm J (φ j)) * δ := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
        obtain ⟨hc, hb⟩ := s45_fij_facts hd hs0 hsd hβ hsu hN hJ hφ hfeat i j
        have h := hsu.hTb N hN hc.measurable hb
        have e : ∫ X, ee i j X ∂P = β⁻¹ * ∫ X, |pair (empirical X)
            (fun x => ⟪gradient (χ i) x, gradient (φ j) x⟫) - pair μ
            (fun x => ⟪gradient (χ i) x, gradient (φ j) x⟫)| ∂P := by
          rw [← integral_const_mul]
          congr 1; funext X
          simp only [hee, abs_mul, abs_of_pos (inv_pos.2 hβ)]
        rw [e]
        calc β⁻¹ * ∫ X, |pair (empirical X) (fun x => ⟪gradient (χ i) x, gradient (φ j) x⟫) - pair μ
              (fun x => ⟪gradient (χ i) x, gradient (φ j) x⟫)| ∂P
            ≤ β⁻¹ * (KT * ((Cc * cbNorm J (φ i)) * cbNorm J (φ j)) * δ) :=
              mul_le_mul_of_nonneg_left h (inv_nonneg.2 hβ.le)
          _ = _ := by ring
    _ = _ := by
        have : ∀ i j : Fin n, β⁻¹ * KT * ((Cc * cbNorm J (φ i)) * cbNorm J (φ j)) * δ =
            (β⁻¹ * KT * Cc * δ) * (cbNorm J (φ i) * cbNorm J (φ j)) := fun i j => by ring
        simp_rw [this]
        simp only [← Finset.mul_sum, ← Finset.sum_mul]
        ring

end Ctx

end S45

end
