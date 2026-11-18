import HRS.MS.TiltAux9

/-!
# S4.7 packet P6b: the finite-dimensional data `R_n, T_n` and the `hfin` data of `static_stein_hilbert` for `Q`

Copy of `QprepAux11` (itself a copy of `QsfAsm6`-`QsfAsm9`) for a reference density `ρ`.
-/

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

noncomputable section

namespace S47

open S45
open HRS.Whole
open HRS (Euc cbNorm MemCb)

variable {d N : ℕ}

/-- The `R`-bound of `s45_R_bound` as a predicate. -/
def S47RBound (d : ℕ) (s : ℝ) (ρ : Euc d → ℝ) (γ KR : ℝ) : Prop :=
  ∀ N : ℕ, 2 ≤ N → ∀ {χ : Euc d → ℝ}, ContDiff ℝ 2 χ → ∀ {B2 : ℝ},
    (∀ x, ‖fderiv ℝ (gradient χ) x‖ ≤ B2) →
    Real.sqrt N * ∫ X, |s45_Rp (withDensityReal ρ) (s47_nu d s ρ γ N) (s47_P d s ρ γ N)
        (commutatorKernel d s (gradient χ)) X| ∂(s47_P d s ρ γ N) ≤
      KR * B2 * Real.sqrt (HRS.deltaN d s N)

/-- The `T`-bound of `s45_T_bound` as a predicate. -/
def S47TBound (d : ℕ) (s : ℝ) (ρ : Euc d → ℝ) (γ KT : ℝ) : Prop :=
  ∀ N : ℕ, 2 ≤ N → ∀ {f : Euc d → ℝ}, Measurable f → ∀ {Bf : ℝ}, (∀ x, |f x| ≤ Bf) →
    ∫ X, |pair (empirical X) f - pair (withDensityReal ρ) f| ∂(s47_P d s ρ γ N) ≤
      KT * Bf * Real.sqrt (HRS.deltaN d s N)

/-- All the `d, s, a, β`-dependent inputs of the S4.5 assembly. -/
structure S47Setup (d : ℕ) (s : ℝ) (ρ : Euc d → ℝ) (q γ Cs C c BU BB KR KT : ℝ)
    (Bd : Euc d → Euc d) : Prop where
  hT : TRef d s ρ q C c BU BB Bd
  hCs : 0 ≤ Cs
  hS : ∀ N : ℕ, 2 ≤ N → S47Static d s ρ γ Cs N
  hKR : 0 ≤ KR
  hR : S47RBound d s ρ γ KR
  hKT : 0 ≤ KT
  hTb : S47TBound d s ρ γ KT


theorem s47_nu_prob {s : ℝ} {ρ : Euc d → ℝ} {γ : ℝ} (hN : 2 ≤ N) (hP : IsProbabilityMeasure (s47_P d s ρ γ N)) :
    IsProbabilityMeasure (s47_nu d s ρ γ N) := by
  have : s47_nu d s ρ γ N = (s47_P d s ρ γ N).map (fun X : EucConfig d N => X ⟨0, by omega⟩) := by
    unfold s47_nu firstMarginal; rw [dif_pos (by omega)]
  rw [this]
  constructor
  rw [Measure.map_apply (measurable_pi_apply _) MeasurableSet.univ]
  simp

/-- The remainder vector `R_n`. -/
def s47_Rvec (d : ℕ) (s : ℝ) (ρ : Euc d → ℝ) (γ : ℝ) (N n : ℕ) (χ : ℕ → Euc d → ℝ) {Zg : Type*}
    (w : EucConfig d N × Zg) : EuclideanSpace ℝ (Fin n) :=
  ∑ i : Fin n, (Real.sqrt N * s45_Rp (withDensityReal ρ) (s47_nu d s ρ γ N) (s47_P d s ρ γ N)
    (commutatorKernel d s (gradient (χ i))) w.1) • EuclideanSpace.single i (1 : ℝ)

/-- The matrix `T_n`. -/
def s47_Tmat (d : ℕ) (γ : ℝ) (N n : ℕ) (φ χ : ℕ → Euc d → ℝ) {Zg : Type*}
    (w : EucConfig d N × Zg) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => γ⁻¹ * pair (empirical w.1) (fun x => ⟪gradient (χ i) x, gradient (φ j) x⟫)

section Ctx

variable (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ρ : Euc d → ℝ} {q γ Cs C c BU BB KR KT : ℝ}
  {Bd : Euc d → Euc d} (hq : 0 < q) (hγ : 0 < γ) (hsu : S47Setup d s ρ q γ Cs C c BU BB KR KT Bd) (hN : 2 ≤ N) {J : ℕ}
  (hJ : 1 ≤ J) {φ χ : ℕ → Euc d → ℝ} {Cc : ℝ} (hCc : 0 ≤ Cc)
  (hφ : HRS.Whole.IsSummableFeatureFamily J φ)
  (hfeat : ∀ i, S47Feat d s ρ γ (φ i) (χ i) (Cc * cbNorm J (φ i)))
  {Zg : Measure SeqL2} [IsProbabilityMeasure Zg]

include hd hs0 hsd hsu hN hfeat

theorem s47_Rvec_integrable (n : ℕ) :
    Integrable (s47_Rvec d s ρ γ N n χ : EucConfig d N × SeqL2 → EuclideanSpace ℝ (Fin n))
      ((s47_P d s ρ γ N).prod Zg) := by
  haveI : IsProbabilityMeasure (s47_P d s ρ γ N) := (hsu.hS N hN).prob
  unfold s47_Rvec
  refine integrable_finsetSum _ fun i _ => ?_
  have h1 := s47_Rp_integrable hd hs0 hsd hsu.hT hN (hsu.hS N hN) (hfeat i).smooth (hfeat i).B2
  exact (s45_integrable_fst (γ := Zg) (h1.const_mul (Real.sqrt N))).smul_const _

theorem s47_Rvec_bound (n : ℕ) :
    ∫ w, ‖(s47_Rvec d s ρ γ N n χ w : EuclideanSpace ℝ (Fin n))‖ ∂((s47_P d s ρ γ N).prod Zg) ≤
      KR * Cc * (∑ i : Fin n, cbNorm J (φ i)) * Real.sqrt (HRS.deltaN d s N) := by
  have hN1 : 1 ≤ N := by omega
  haveI : IsProbabilityMeasure (s47_P d s ρ γ N) := (hsu.hS N hN).prob
  set P := s47_P d s ρ γ N with hPdef
  set δ := Real.sqrt (HRS.deltaN d s N) with hδ
  set rr : Fin n → EucConfig d N → ℝ := fun i X => s45_Rp (withDensityReal ρ)
    (s47_nu d s ρ γ N) P (commutatorKernel d s (gradient (χ i))) X with hrr
  have hri : ∀ i, Integrable (rr i) P := fun i =>
    s47_Rp_integrable hd hs0 hsd hsu.hT hN (hsu.hS N hN) (hfeat i).smooth (hfeat i).B2
  have hpt : ∀ w : EucConfig d N × SeqL2, ‖s47_Rvec d s ρ γ N n χ w‖ ≤
      ∑ i : Fin n, |Real.sqrt N * rr i w.1| := by
    intro w
    unfold s47_Rvec
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_smul, EuclideanSpace.norm_single]
    simp
    exact le_rfl
  have hint : ∀ i : Fin n, Integrable (fun w : EucConfig d N × SeqL2 => |Real.sqrt N * rr i w.1|)
      (P.prod Zg) := fun i =>
    (s45_integrable_fst (γ := Zg) ((hri i).const_mul (Real.sqrt N))).abs
  calc ∫ w, ‖s47_Rvec d s ρ γ N n χ w‖ ∂(P.prod Zg)
      ≤ ∫ w, ∑ i : Fin n, |Real.sqrt N * rr i w.1| ∂(P.prod Zg) :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun w => norm_nonneg _)
          (integrable_finsetSum _ fun i _ => hint i) (Filter.Eventually.of_forall hpt)
    _ = ∑ i : Fin n, ∫ w, |Real.sqrt N * rr i w.1| ∂(P.prod Zg) :=
        integral_finsetSum _ fun i _ => hint i
    _ = ∑ i : Fin n, Real.sqrt N * ∫ X, |rr i X| ∂P := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [s45_integral_fst (γ := Zg) (g := fun X => |Real.sqrt N * rr i X|)
          ((hri i).const_mul _).abs.aestronglyMeasurable]
        simp_rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg (N : ℝ))]
        rw [integral_const_mul]
    _ ≤ ∑ i : Fin n, KR * (Cc * cbNorm J (φ i)) * δ := Finset.sum_le_sum fun i _ =>
        hsu.hR N hN (hfeat i).smooth (hfeat i).B2
    _ = _ := by rw [← Finset.sum_mul, ← Finset.mul_sum, ← Finset.mul_sum]; ring

end Ctx


section Ctx

variable (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ρ : Euc d → ℝ} {q γ Cs C c BU BB KR KT : ℝ}
  {Bd : Euc d → Euc d} (hq : 0 < q) (hγ : 0 < γ) (hsu : S47Setup d s ρ q γ Cs C c BU BB KR KT Bd) (hN : 2 ≤ N) {J : ℕ}
  (hJ : 1 ≤ J) {φ χ : ℕ → Euc d → ℝ} {Cc : ℝ} (hCc : 0 ≤ Cc)
  (hφ : HRS.Whole.IsSummableFeatureFamily J φ)
  (hfeat : ∀ i, S47Feat d s ρ γ (φ i) (χ i) (Cc * cbNorm J (φ i)))
  {Zg : Measure SeqL2} [IsProbabilityMeasure Zg]

include hd hs0 hsd hsu hN hfeat hJ hφ hγ

theorem s47_fij_facts (i j : ℕ) :
    Continuous (fun x : Euc d => ⟪gradient (χ i) x, gradient (φ j) x⟫) ∧
      ∀ x, |⟪gradient (χ i) x, gradient (φ j) x⟫| ≤ (Cc * cbNorm J (φ i)) * cbNorm J (φ j) := by
  obtain ⟨hφ1, -, hφD⟩ := s45_phi_facts hJ hφ
  exact ⟨(s45_contDiff_gradient (hfeat i).smooth).continuous.inner (s45_gradient_continuous (hφ1 j)),
    fun x => s45_inner_grad_le (hfeat i).B1 (hφD j) x⟩

theorem s47_cmat_entry
    (hZg : IsCenteredGaussianSeq Zg fun i j => susceptibilityCov (rieszKernel d s)
      (withDensityReal ρ) γ (φ i) (φ j)) (i j : ℕ) :
    ∫ w, ⟪s45_seqBasis i, w.2⟫ * ⟪s45_seqBasis j, w.2⟫ ∂((s47_P d s ρ γ N).prod Zg) =
      γ⁻¹ * pair (withDensityReal ρ) (fun x => ⟪gradient (χ i) x, gradient (φ j) x⟫) := by
  haveI : IsProbabilityMeasure (s47_P d s ρ γ N) := (hsu.hS N hN).prob
  obtain ⟨hφ1, hφb, hφD⟩ := s45_phi_facts hJ hφ
  rw [s45_gauss_cov (P := s47_P d s ρ γ N) hZg i j]
  haveI : IsProbabilityMeasure (withDensityReal ρ) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu hsu.hT.prob
  have hφi : MemLp (φ i) 2 (withDensityReal ρ) :=
    MemLp.of_bound (hφ1 i).continuous.aestronglyMeasurable (cbNorm J (φ i))
      (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hφb i x)
  exact s47_cov_identity hd hs0 hsd hγ hsu.hT (hfeat i).smooth (hfeat i).B1 (hfeat i).B2 hφi
    (hfeat i).r2 (hfeat i).corr (hφ1 j) (hφb j) (hφD j)

theorem s47_Tmat_tau
    (hZg : IsCenteredGaussianSeq Zg fun i j => susceptibilityCov (rieszKernel d s)
      (withDensityReal ρ) γ (φ i) (φ j)) (n : ℕ) :
    ∫ w, HRS.traceNormMatrix (s47_Tmat d γ N n φ χ w - Matrix.of fun i j : Fin n =>
        ∫ w', ⟪s45_seqBasis i, w'.2⟫ * ⟪s45_seqBasis j, w'.2⟫ ∂((s47_P d s ρ γ N).prod Zg))
      ∂((s47_P d s ρ γ N).prod Zg) ≤
      γ⁻¹ * KT * Cc * (∑ i : Fin n, cbNorm J (φ i)) ^ 2 * Real.sqrt (HRS.deltaN d s N) := by
  have hN1 : 1 ≤ N := by omega
  haveI : IsProbabilityMeasure (s47_P d s ρ γ N) := (hsu.hS N hN).prob
  set P := s47_P d s ρ γ N with hPdef
  set μ := withDensityReal ρ with hμdef
  haveI : IsProbabilityMeasure μ := HRS.Whole.Q34.isProbabilityMeasure_nu hsu.hT.prob
  set δ := Real.sqrt (HRS.deltaN d s N) with hδ
  have hcb0 : ∀ i, 0 ≤ cbNorm J (φ i) := fun i => HRS.MS.Tc5.tc5_cb_nonneg J (φ i)
  set ee : Fin n → Fin n → EucConfig d N → ℝ := fun i j X =>
    |γ⁻¹ * (pair (empirical X) (fun x => ⟪gradient (χ i) x, gradient (φ j) x⟫) -
      pair μ (fun x => ⟪gradient (χ i) x, gradient (φ j) x⟫))| with hee
  have hpt : ∀ w : EucConfig d N × SeqL2, HRS.traceNormMatrix (s47_Tmat d γ N n φ χ w -
      Matrix.of fun i j : Fin n => ∫ w', ⟪s45_seqBasis i, w'.2⟫ * ⟪s45_seqBasis j, w'.2⟫ ∂(P.prod Zg)) ≤
      ∑ i : Fin n, ∑ j : Fin n, ee i j w.1 := by
    intro w
    refine (HRS.PDE.MFLinear.traceNormMatrix_le_sum _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [Matrix.sub_apply, s47_Tmat, Matrix.of_apply]
    rw [s47_cmat_entry hd hs0 hsd hγ hsu hN hJ hφ hfeat hZg]
    simp only [hee]
    congr 1; ring
  have heeI : ∀ i j : Fin n, Integrable (ee i j) P := by
    intro i j
    obtain ⟨hc, hb⟩ := s47_fij_facts hd hs0 hsd hγ hsu hN hJ hφ hfeat i j
    refine Integrable.of_bound (C := γ⁻¹ * ((Cc * cbNorm J (φ i)) * cbNorm J (φ j) +
        (Cc * cbNorm J (φ i)) * cbNorm J (φ j)))
      ((((s45_measurable_pair_empirical hN1 hc.measurable).sub measurable_const).const_mul _).abs.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun X => ?_)
    rw [Real.norm_eq_abs, hee]
    simp only [abs_abs]
    rw [abs_mul, abs_of_pos (inv_pos.2 hγ)]
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hγ.le)
    refine (abs_sub _ _).trans (add_le_add (s45_abs_pair_empirical_le hN1 hb X) ?_)
    exact HRS.MS.Tc5.tc5_pair_le (fun x => by rw [Real.norm_eq_abs]; exact hb x)
  have heeS : ∀ i j : Fin n, Integrable (fun w : EucConfig d N × SeqL2 => ee i j w.1) (P.prod Zg) :=
    fun i j => s45_integrable_fst (heeI i j)
  calc ∫ w, HRS.traceNormMatrix (s47_Tmat d γ N n φ χ w - Matrix.of fun i j : Fin n =>
        ∫ w', ⟪s45_seqBasis i, w'.2⟫ * ⟪s45_seqBasis j, w'.2⟫ ∂(P.prod Zg)) ∂(P.prod Zg)
      ≤ ∫ w, ∑ i : Fin n, ∑ j : Fin n, ee i j w.1 ∂(P.prod Zg) :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun w => HRS.traceNormMatrix_nonneg _)
          (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => heeS i j)
          (Filter.Eventually.of_forall hpt)
    _ = ∑ i : Fin n, ∑ j : Fin n, ∫ X, ee i j X ∂P := by
        rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => heeS i j]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [integral_finsetSum _ fun j _ => heeS i j]
        refine Finset.sum_congr rfl fun j _ => ?_
        exact s45_integral_fst (γ := Zg) (g := ee i j) (heeI i j).aestronglyMeasurable
    _ ≤ ∑ i : Fin n, ∑ j : Fin n, γ⁻¹ * KT * ((Cc * cbNorm J (φ i)) * cbNorm J (φ j)) * δ := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
        obtain ⟨hc, hb⟩ := s47_fij_facts hd hs0 hsd hγ hsu hN hJ hφ hfeat i j
        have h := hsu.hTb N hN hc.measurable hb
        have e : ∫ X, ee i j X ∂P = γ⁻¹ * ∫ X, |pair (empirical X)
            (fun x => ⟪gradient (χ i) x, gradient (φ j) x⟫) - pair μ
            (fun x => ⟪gradient (χ i) x, gradient (φ j) x⟫)| ∂P := by
          rw [← integral_const_mul]
          congr 1; funext X
          simp only [hee, abs_mul, abs_of_pos (inv_pos.2 hγ)]
        rw [e]
        calc γ⁻¹ * ∫ X, |pair (empirical X) (fun x => ⟪gradient (χ i) x, gradient (φ j) x⟫) - pair μ
              (fun x => ⟪gradient (χ i) x, gradient (φ j) x⟫)| ∂P
            ≤ γ⁻¹ * (KT * ((Cc * cbNorm J (φ i)) * cbNorm J (φ j)) * δ) :=
              mul_le_mul_of_nonneg_left h (inv_nonneg.2 hγ.le)
          _ = _ := by ring
    _ = _ := by
        have : ∀ i j : Fin n, γ⁻¹ * KT * ((Cc * cbNorm J (φ i)) * cbNorm J (φ j)) * δ =
            (γ⁻¹ * KT * Cc * δ) * (cbNorm J (φ i) * cbNorm J (φ j)) := fun i j => by ring
        simp_rw [this]
        simp only [← Finset.mul_sum, ← Finset.sum_mul]
        ring

end Ctx


section Ctx

variable (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ρ : Euc d → ℝ} {q γ Cs C c BU BB KR KT : ℝ}
  {Bd : Euc d → Euc d} (hq : 0 < q) (hγ : 0 < γ) (hsu : S47Setup d s ρ q γ Cs C c BU BB KR KT Bd) (hN : 2 ≤ N) {J : ℕ}
  (hJ : 1 ≤ J) {φ χ : ℕ → Euc d → ℝ} {Cc : ℝ} (hCc : 0 ≤ Cc)
  (hφ : HRS.Whole.IsSummableFeatureFamily J φ)
  (hfeat : ∀ i, S47Feat d s ρ γ (φ i) (χ i) (Cc * cbNorm J (φ i)))
  {Zg : Measure SeqL2} [IsProbabilityMeasure Zg]

include hd hs0 hsd hq hγ hsu hN hJ hCc hφ hfeat

theorem s47_hfin
    (hZg : IsCenteredGaussianSeq Zg fun i j => susceptibilityCov (rieszKernel d s)
      (withDensityReal ρ) γ (φ i) (φ j)) (n : ℕ) :
    ∃ (R : EucConfig d N × SeqL2 → EuclideanSpace ℝ (Fin n))
      (T : EucConfig d N × SeqL2 → Matrix (Fin n) (Fin n) ℝ),
      Integrable R ((s47_P d s ρ γ N).prod Zg) ∧
      (∀ i j, AEStronglyMeasurable (fun w => T w i j) ((s47_P d s ρ γ N).prod Zg)) ∧
      Integrable (fun w => HRS.traceNormMatrix (T w)) ((s47_P d s ρ γ N).prod Zg) ∧
      SteinIdentity ((s47_P d s ρ γ N).prod Zg)
        (fun w => hilbertCoords s45_seqBasis n (featureVec φ (s47_nu d s ρ γ N) w.1)) R T ∧
      ∫ w, ‖R w‖ ∂((s47_P d s ρ γ N).prod Zg) ≤
        KR * Cc * featureSum J φ * Real.sqrt (HRS.deltaN d s N) ∧
      ∫ w, HRS.traceNormMatrix (T w - Matrix.of fun i j : Fin n =>
          ∫ w', ⟪s45_seqBasis i, w'.2⟫ * ⟪s45_seqBasis j, w'.2⟫ ∂((s47_P d s ρ γ N).prod Zg))
        ∂((s47_P d s ρ γ N).prod Zg) ≤
        γ⁻¹ * KT * Cc * featureSum J φ ^ 2 * Real.sqrt (HRS.deltaN d s N) := by
  have hN1 : 1 ≤ N := by omega
  have hSN := hsu.hS N hN
  haveI hP : IsProbabilityMeasure (s47_P d s ρ γ N) := hSN.prob
  haveI hνprob : IsProbabilityMeasure (s47_nu d s ρ γ N) := s47_nu_prob hN hP
  obtain ⟨hφ1, hφb, hφD⟩ := s45_phi_facts hJ hφ
  have hδ0 : 0 ≤ Real.sqrt (HRS.deltaN d s N) := Real.sqrt_nonneg _
  have hSsum := s45_partial_sum_le hφ n
  have hSn0 : 0 ≤ ∑ i : Fin n, cbNorm J (φ i) :=
    Finset.sum_nonneg fun i _ => HRS.MS.Tc5.tc5_cb_nonneg J (φ i)
  refine ⟨s47_Rvec d s ρ γ N n χ, s47_Tmat d γ N n φ χ,
    s47_Rvec_integrable hd hs0 hsd hsu hN hfeat n, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j
    obtain ⟨hc, -⟩ := s47_fij_facts hd hs0 hsd hγ hsu hN hJ hφ hfeat i j
    exact ((measurable_const.mul ((s45_measurable_pair_empirical hN1 hc.measurable).comp
      measurable_fst)).aestronglyMeasurable)
  · refine s45_traceNorm_integrable (b := γ⁻¹ * ((Cc * featureSum J φ) * featureSum J φ)) ?_ ?_
    · intro i j
      obtain ⟨hc, -⟩ := s47_fij_facts hd hs0 hsd hγ hsu hN hJ hφ hfeat i j
      exact measurable_const.mul ((s45_measurable_pair_empirical hN1 hc.measurable).comp measurable_fst)
    · intro w i j
      obtain ⟨-, hb⟩ := s47_fij_facts hd hs0 hsd hγ hsu hN hJ hφ hfeat i j
      simp only [s47_Tmat, Matrix.of_apply]
      rw [abs_mul, abs_of_pos (inv_pos.2 hγ)]
      refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hγ.le)
      have hcbS : ∀ k : ℕ, cbNorm J (φ k) ≤ featureSum J φ := fun k =>
        hφ.2.le_tsum k fun m _ => HRS.MS.Tc5.tc5_cb_nonneg J (φ m)
      have h1 := s45_abs_pair_empirical_le hN1 hb w.1
      refine h1.trans ?_
      have hi := hcbS i
      have hj := hcbS j
      have hi0 := HRS.MS.Tc5.tc5_cb_nonneg (d := d) J (φ i)
      have hj0 := HRS.MS.Tc5.tc5_cb_nonneg (d := d) J (φ j)
      exact mul_le_mul (mul_le_mul_of_nonneg_left hi hCc) hj hj0
        (mul_nonneg hCc (hi0.trans hi))
  · -- the Stein identity
    set P := s47_P d s ρ γ N with hPdef
    set ν := s47_nu d s ρ γ N with hν
    set c' : ℕ → ℝ := fun j => pair ν (φ j) with hc'
    have hX : (fun w : EucConfig d N × SeqL2 => hilbertCoords s45_seqBasis n (featureVec φ ν w.1)) =
        fun w => s45_Yv n N φ c' w.1 := funext fun w => s45_hcoords hN1 hφ n w.1
    rw [hX]
    have hYm : Measurable (s45_Yv n N φ c' : EucConfig d N → EuclideanSpace ℝ (Fin n)) :=
      (s45_Yv_contDiff hN1 hφ1 c').continuous.measurable
    have hrm : ∀ i : Fin n, AEStronglyMeasurable (fun X => Real.sqrt N * s45_Rp
        (withDensityReal ρ) ν P (commutatorKernel d s (gradient (χ i))) X) P := fun i =>
      ((s47_Rp_integrable hd hs0 hsd hsu.hT hN hSN (hfeat i).smooth (hfeat i).B2).const_mul
        (Real.sqrt N)).aestronglyMeasurable
    have hTm : ∀ i j : Fin n, Measurable fun X : EucConfig d N => γ⁻¹ * pair (empirical X)
        (fun x => ⟪gradient (χ i) x, gradient (φ j) x⟫) := fun i j =>
      measurable_const.mul (s45_measurable_pair_empirical hN1
        (s47_fij_facts hd hs0 hsd hγ hsu hN hJ hφ hfeat i j).1.measurable)
    exact s45_stein_prod (γ := Zg) hYm hrm hTm fun f hf ⟨Cf, hCf⟩ ⟨Cf', hCf'⟩ i => by
      have h := s47_vec_stein hd hs0 hsd hq hγ hN hsu.hT hSN hφ1 hφb hφD hfeat hf hCf hCf' i
      have e : ∀ x, s45_Yv n N φ c' x i = s45_Yi N (φ i) (pair ν (φ i)) x := fun x =>
        s45_Yv_apply n N φ c' x i
      simp only [e]
      exact h
  · refine (s47_Rvec_bound hd hs0 hsd hsu hN hfeat n).trans ?_
    have : 0 ≤ KR * Cc := mul_nonneg hsu.hKR hCc
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hSsum this) hδ0
  · refine (s47_Tmat_tau hd hs0 hsd hγ hsu hN hJ hφ hfeat hZg n).trans ?_
    have : 0 ≤ γ⁻¹ * KT * Cc := mul_nonneg (mul_nonneg (inv_nonneg.2 hγ.le) hsu.hKT) hCc
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hSn0 hSsum 2) this) hδ0

end Ctx


end S47

end
