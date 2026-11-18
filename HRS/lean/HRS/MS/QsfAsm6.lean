import HRS.MS.QsfAsm5

/-!
# S4.5 packet B5 (assembly), part 6: the global setup and the product-coupling Stein identity
-/

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal RealInnerProductSpace ContDiff

noncomputable section

namespace S45

open HRS.Whole
open HRS (Euc cbNorm MemCb)

variable {d N : ℕ}

/-- The `R`-bound of `s45_R_bound` as a predicate. -/
def S45RBound (d : ℕ) (s a β KR : ℝ) : Prop :=
  ∀ N : ℕ, 2 ≤ N → ∀ {χ : Euc d → ℝ}, ContDiff ℝ 2 χ → ∀ {B2 : ℝ},
    (∀ x, ‖fderiv ℝ (gradient χ) x‖ ≤ B2) →
    Real.sqrt N * ∫ X, |s45_Rp (thermalMeasure d s a β) (s45_nu d s a β N) (s45_P d s a β N)
        (commutatorKernel d s (gradient χ)) X| ∂(s45_P d s a β N) ≤
      KR * B2 * Real.sqrt (HRS.deltaN d s N)

/-- The `T`-bound of `s45_T_bound` as a predicate. -/
def S45TBound (d : ℕ) (s a β KT : ℝ) : Prop :=
  ∀ N : ℕ, 2 ≤ N → ∀ {f : Euc d → ℝ}, Measurable f → ∀ {Bf : ℝ}, (∀ x, |f x| ≤ Bf) →
    ∫ X, |pair (empirical X) f - pair (thermalMeasure d s a β) f| ∂(s45_P d s a β N) ≤
      KT * Bf * Real.sqrt (HRS.deltaN d s N)

/-- All the `d, s, a, β`-dependent inputs of the S4.5 assembly. -/
structure S45Setup (d : ℕ) (s a β Cs C c BU KR KT : ℝ) : Prop where
  hT : ThermalData d s a β C c BU
  hCs : 0 ≤ Cs
  hS : ∀ N : ℕ, 2 ≤ N → S45Static d s a β Cs N
  hKR : 0 ≤ KR
  hR : S45RBound d s a β KR
  hKT : 0 ≤ KT
  hTb : S45TBound d s a β KT

theorem s45_setup (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β : ℝ} (ha : 0 < a)
    (hβ : 0 < β) : ∃ Cs C c BU KR KT : ℝ, S45Setup d s a β Cs C c BU KR KT := by
  obtain ⟨C, c, BU, hT⟩ := s45_thermal_data hd hs0 hsd ha hβ
  obtain ⟨Cs, hCs, hS⟩ := s45_static_all hd hs0 hsd ha hβ
  obtain ⟨KR, hKR, hR⟩ := s45_R_bound hd hs0 hsd hT hCs hS
  obtain ⟨KT, hKT, hTb⟩ := s45_T_bound hd hs0 hsd hT hCs hS
  exact ⟨Cs, C, c, BU, KR, KT, ⟨hT, hCs, hS, hKR, fun N hN _ hχ _ hB2 => hR N hN hχ hB2, hKT,
    fun N hN _ hf _ hbd => hTb N hN hf hbd⟩⟩

theorem s45_hcoords (hN : 1 ≤ N) {J : ℕ} {φ : ℕ → Euc d → ℝ}
    (hφ : HRS.Whole.IsSummableFeatureFamily J φ) {ν : Measure (Euc d)} [IsProbabilityMeasure ν]
    (n : ℕ) (X : EucConfig d N) :
    hilbertCoords s45_seqBasis n (featureVec φ ν X) = s45_Yv n N φ (fun j => pair ν (φ j)) X := by
  ext i
  have h1 : (hilbertCoords s45_seqBasis n (featureVec φ ν X)) i =
      ⟪s45_seqBasis i, featureVec φ ν X⟫ := rfl
  rw [h1, s45_inner_seqBasis, s45_Yv_apply]
  unfold featureVec
  rw [s45_coord_ofSeq (s45_feature_memℓp hN hφ X)]
  rfl

theorem s45_gauss_cov {α : Type*} [MeasurableSpace α] {P : Measure α} [IsProbabilityMeasure P]
    {γ : Measure SeqL2} [IsProbabilityMeasure γ] {C : ℕ → ℕ → ℝ} (hγ : IsCenteredGaussianSeq γ C)
    (i j : ℕ) :
    ∫ w, ⟪s45_seqBasis i, w.2⟫ * ⟪s45_seqBasis j, w.2⟫ ∂(P.prod γ) = C i j := by
  simp_rw [s45_inner_seqBasis]
  rw [s45_integral_snd (P := P) (g := fun z : SeqL2 => SeqL2.coord z i * SeqL2.coord z j)
    (hγ.2 i j).1.aestronglyMeasurable]
  exact (hγ.2 i j).2

/-- Transfer of a Stein identity from `P` to the product coupling `P ⊗ γ`. -/
theorem s45_stein_prod {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {P : Measure α}
    {γ : Measure β} [IsProbabilityMeasure P] [IsProbabilityMeasure γ] {n : ℕ}
    {Y : α → EuclideanSpace ℝ (Fin n)} (hY : Measurable Y) {r : Fin n → α → ℝ}
    (hr : ∀ i, AEStronglyMeasurable (r i) P) {Tm : α → Matrix (Fin n) (Fin n) ℝ}
    (hT : ∀ i j, Measurable fun x => Tm x i j)
    (h : ∀ f : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ ∞ f → (∃ Cf, ∀ x, |f x| ≤ Cf) →
      (∃ Cf, ∀ x, ‖fderiv ℝ f x‖ ≤ Cf) → ∀ i : Fin n,
        ∫ x, Y x i * f (Y x) ∂P = ∫ x, r i x * f (Y x) ∂P +
          ∑ j : Fin n, ∫ x, Tm x i j * fderiv ℝ f (Y x) (EuclideanSpace.single j 1) ∂P) :
    SteinIdentity (P.prod γ) (fun w => Y w.1)
      (fun w => ∑ i : Fin n, r i w.1 • EuclideanSpace.single i (1 : ℝ)) (fun w => Tm w.1) := by
  intro f hf hCf hCf' i
  have hfc : Continuous f := hf.continuous
  have hdc : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by simp)
  have hRi : ∀ w : α × β, (∑ k : Fin n, r k w.1 • EuclideanSpace.single k (1 : ℝ)) i = r i w.1 := by
    intro w
    simp [Pi.single_apply]
  simp_rw [hRi]
  have hYi : Measurable fun x => Y x i := ((EuclideanSpace.proj i : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ).continuous.measurable).comp hY
  rw [s45_integral_fst (P := P) (γ := γ) (g := fun x => Y x i * f (Y x))
      (hYi.mul (hfc.measurable.comp hY)).aestronglyMeasurable,
    s45_integral_fst (P := P) (γ := γ) (g := fun x => r i x * f (Y x))
      ((hr i).mul (hfc.measurable.comp hY).aestronglyMeasurable)]
  rw [h f hf hCf hCf' i]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  exact (s45_integral_fst (P := P) (γ := γ)
    (g := fun x => Tm x i j * fderiv ℝ f (Y x) (EuclideanSpace.single j 1))
    ((hT i j).mul ((hdc.clm_apply continuous_const).measurable.comp hY)).aestronglyMeasurable).symm

end S45

end
