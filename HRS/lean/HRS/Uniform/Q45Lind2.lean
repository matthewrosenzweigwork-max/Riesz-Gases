import HRS.Uniform.Q45Lind1

/-!
# Q45: one partition step of the generalised Lindeberg bound
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.Uniform.Q45

open HRS HRS.LindebergAux

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
variable {p : ℕ}

local notation "ℝ^" p => EuclideanSpace ℝ (Fin p)

/-- The properties of a Hessian-pairing seminorm `ν` on `p × p` matrices used by the Lindeberg bound. -/
structure PairNorm (ν : Matrix (Fin p) (Fin p) ℝ → ℝ) (Cν : ℝ) : Prop where
  Cν_nonneg : 0 ≤ Cν
  nonneg : ∀ Q, 0 ≤ ν Q
  le_s1 : ∀ Q, ν Q ≤ Cν * s1Norm Q
  cont : Continuous ν
  jensen : ∀ (Qf : ℝ → Matrix (Fin p) (Fin p) ℝ) (c d : ℝ),
    (∀ i j, IntegrableOn (fun σ => Qf σ i j) (Set.Icc c d)) →
    IntegrableOn (fun σ => s1Norm (Qf σ)) (Set.Icc c d) →
    ν (covBlock Qf c d) ≤ ∫ σ in Set.Icc c d, ν (Qf σ)

/-- The facts about a (vector) process `M` with covariation density `Sg` that the Lindeberg replacement uses on the
cells `[τ, τ']` satisfying `adm τ τ'`: adaptedness, square integrability, zero start, orthogonality of increments to
`ℱ_τ`-measurable `L²` variables, the covariation identity on increments, and integrability of the density. -/
structure CellIface (ℱ : Filtration ℝ mΩ) (t : ℝ) (M : ℝ → Ω → (ℝ^p))
    (Sg : ℝ → Ω → Matrix (Fin p) (Fin p) ℝ) (adm : ℝ → ℝ → Prop) : Prop where
  adapted : ∀ τ ∈ Set.Icc (0 : ℝ) t, ∀ i, StronglyMeasurable[ℱ τ] (fun ω => M τ ω i)
  sq_int : ∀ τ ∈ Set.Icc (0 : ℝ) t, MemLp (M τ) 2 P
  zero : ∀ᵐ ω ∂P, M 0 ω = 0
  orth : ∀ τ τ', 0 ≤ τ → τ ≤ τ' → τ' ≤ t → adm τ τ' → ∀ w : Ω → ℝ,
    StronglyMeasurable[ℱ τ] w → MemLp w 2 P → ∀ i, ∫ ω, w ω * M τ' ω i ∂P = ∫ ω, w ω * M τ ω i ∂P
  cov : ∀ τ τ', 0 ≤ τ → τ ≤ τ' → τ' ≤ t → adm τ τ' → ∀ z : Ω → ℝ, StronglyMeasurable[ℱ τ] z →
    ∀ K : ℝ, (∀ ω, |z ω| ≤ K) → ∀ a b : Fin p,
    Integrable (fun ω => z ω * ((M τ' ω - M τ ω) a * (M τ' ω - M τ ω) b)) P ∧
    Integrable (fun ω => z ω * (∫ σ in Set.Icc τ τ', Sg σ ω a b)) P ∧
    ∫ ω, z ω * ((M τ' ω - M τ ω) a * (M τ' ω - M τ ω) b) ∂P =
      ∫ ω, z ω * (∫ σ in Set.Icc τ τ', Sg σ ω a b) ∂P
  sigma_meas : Measurable (Function.uncurry Sg)
  sigma_int : Integrable (fun ω => ∫ σ in Set.Icc 0 t, s1Norm (Sg σ ω)) P
  sigma_pathint : ∀ᵐ ω ∂P, IntegrableOn (fun σ => s1Norm (Sg σ ω)) (Set.Icc 0 t)
  sigma_entry_int : ∀ᵐ ω ∂P, ∀ a b : Fin p, IntegrableOn (fun σ => Sg σ ω a b) (Set.Icc 0 t)

omit [IsProbabilityMeasure P] in
lemma s1_sub_intOn_gen {ℱ : Filtration ℝ mΩ} {t : ℝ} {M : ℝ → Ω → (ℝ^p)}
    {Sg : ℝ → Ω → Matrix (Fin p) (Fin p) ℝ} {adm : ℝ → ℝ → Prop} (hM : CellIface P ℱ t M Sg adm)
    {sb : ℝ → Matrix (Fin p) (Fin p) ℝ} (hsbmeas : Measurable sb)
    (hsbint : IntegrableOn (fun σ => s1Norm (sb σ)) (Set.Icc 0 t)) :
    ∀ᵐ ω ∂P, IntegrableOn (fun σ => s1Norm (Sg σ ω - sb σ)) (Set.Icc 0 t) := by
  filter_upwards [hM.sigma_pathint] with ω hω
  refine Integrable.mono' (hω.add hsbint) ?_ (ae_of_all _ fun σ => ?_)
  · have h1 : Measurable (fun σ => Sg σ ω) :=
      hM.sigma_meas.comp (measurable_id.prodMk measurable_const)
    exact (continuous_s1Norm.measurable.comp (measurable_mat_sub h1 hsbmeas)).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_nonneg (traceNormMatrix_nonneg _)]
    exact s1Norm_sub_le_add _ _

lemma Iblk_integrable_cell {ℱ : Filtration ℝ mΩ} {t : ℝ} {M : ℝ → Ω → (ℝ^p)}
    {Sg : ℝ → Ω → Matrix (Fin p) (Fin p) ℝ} {adm : ℝ → ℝ → Prop} (hM : CellIface P ℱ t M Sg adm)
    {sb : ℝ → Matrix (Fin p) (Fin p) ℝ} (hsbmeas : Measurable sb)
    (hsbint : IntegrableOn (fun σ => s1Norm (sb σ)) (Set.Icc 0 t)) {c d : ℝ} (hc : 0 ≤ c)
    (hd : d ≤ t) :
    Integrable (fun ω => ∫ σ in Set.Icc c d, s1Norm (Sg σ ω - sb σ)) P := by
  have hJ : Integrable (fun ω => (∫ σ in Set.Icc 0 t, s1Norm (Sg σ ω)) +
      ∫ σ in Set.Icc 0 t, s1Norm (sb σ)) P := hM.sigma_int.add (integrable_const _)
  refine Integrable.mono' hJ ?_ ?_
  · have hF := measurable_s1_sub hM.sigma_meas hsbmeas
    exact (hF.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Set.Icc c d))
      ).aestronglyMeasurable
  · filter_upwards [s1_sub_intOn_gen P hM hsbmeas hsbint, hM.sigma_pathint] with ω h1 h2
    have hsub : Set.Icc c d ⊆ Set.Icc 0 t := Set.Icc_subset_Icc hc hd
    have e0 : 0 ≤ ∫ σ in Set.Icc c d, s1Norm (Sg σ ω - sb σ) :=
      setIntegral_nonneg measurableSet_Icc fun σ _ => traceNormMatrix_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg e0]
    calc ∫ σ in Set.Icc c d, s1Norm (Sg σ ω - sb σ)
        ≤ ∫ σ in Set.Icc 0 t, s1Norm (Sg σ ω - sb σ) :=
          setIntegral_mono_set h1 (ae_of_all _ fun σ => traceNormMatrix_nonneg _)
            (Filter.Eventually.of_forall hsub)
      _ ≤ ∫ σ in Set.Icc 0 t, (s1Norm (Sg σ ω) + s1Norm (sb σ)) :=
          integral_mono h1 (h2.add hsbint) fun σ => s1Norm_sub_le_add _ _
      _ = _ := integral_add h2 hsbint

omit [IsProbabilityMeasure P] in
lemma pathwise_bound_gen (ℱ : Filtration ℝ mΩ) {t : ℝ} {M : ℝ → Ω → (ℝ^p)}
    {Sg : ℝ → Ω → Matrix (Fin p) (Fin p) ℝ} {adm : ℝ → ℝ → Prop} (hM : CellIface P ℱ t M Sg adm)
    {sb : ℝ → Matrix (Fin p) (Fin p) ℝ} (hsbmeas : Measurable sb)
    (hsbint : IntegrableOn (fun σ => s1Norm (sb σ)) (Set.Icc 0 t))
    (hsbpsd : ∀ σ ∈ Set.Icc 0 t, (sb σ).PosSemidef) {ν : Matrix (Fin p) (Fin p) ℝ → ℝ} {Cν : ℝ}
    (hν : PairNorm ν Cν) {c d : ℝ} (hc : 0 ≤ c) (hd : d ≤ t) {Hp : ℝ} (hHp : 0 ≤ Hp) :
    ∀ᵐ ω ∂P, ∀ (u : (ℝ^p) → ℝ), (∀ x Q', |hessPair u x Q'| ≤ Hp * ν Q') → ∀ x : ℝ^p,
      |∑ i, ∑ j, iteratedFDeriv ℝ 2 u x ![EuclideanSpace.single i 1, EuclideanSpace.single j 1] *
          ((∫ σ in Set.Icc c d, Sg σ ω i j) - covBlock sb c d i j)| ≤
        Hp * ∫ σ in Set.Icc c d, ν (Sg σ ω - sb σ) := by
  filter_upwards [hM.sigma_entry_int, s1_sub_intOn_gen P hM hsbmeas hsbint] with ω he hs u hu x
  have hsub : Set.Icc c d ⊆ Set.Icc 0 t := Set.Icc_subset_Icc hc hd
  have hsbe := sb_entry_integrableOn hsbmeas hsbint hsbpsd
  have hQent : ∀ i j, IntegrableOn (fun σ => (Sg σ ω - sb σ) i j) (Set.Icc c d) := fun i j =>
    ((he i j).sub (hsbe i j)).mono_set hsub
  have hQn : IntegrableOn (fun σ => s1Norm (Sg σ ω - sb σ)) (Set.Icc c d) := hs.mono_set hsub
  have hcov : ∀ i j, covBlock (fun σ => Sg σ ω - sb σ) c d i j =
      (∫ σ in Set.Icc c d, Sg σ ω i j) - covBlock sb c d i j := by
    intro i j
    simp only [covBlock, Matrix.of_apply, Matrix.sub_apply]
    exact integral_sub ((he i j).mono_set hsub) ((hsbe i j).mono_set hsub)
  have h1 := hu x (covBlock (fun σ => Sg σ ω - sb σ) c d)
  simp only [hessPair, hcov] at h1
  refine h1.trans ?_
  exact mul_le_mul_of_nonneg_left (hν.jensen _ c d hQent hQn) hHp

lemma Iblk_integrable_gen (ℱ : Filtration ℝ mΩ) {t : ℝ} {M : ℝ → Ω → (ℝ^p)}
    {Sg : ℝ → Ω → Matrix (Fin p) (Fin p) ℝ} {adm : ℝ → ℝ → Prop} (hM : CellIface P ℱ t M Sg adm)
    {sb : ℝ → Matrix (Fin p) (Fin p) ℝ} (hsbmeas : Measurable sb)
    (hsbint : IntegrableOn (fun σ => s1Norm (sb σ)) (Set.Icc 0 t))
    {ν : Matrix (Fin p) (Fin p) ℝ → ℝ} {Cν : ℝ} (hν : PairNorm ν Cν) {c d : ℝ} (hc : 0 ≤ c)
    (hd : d ≤ t) :
    Integrable (fun ω => ∫ σ in Set.Icc c d, ν (Sg σ ω - sb σ)) P := by
  have hF : Measurable (fun q : Ω × ℝ => ν (Sg q.2 q.1 - sb q.2)) := by
    have h1 : Measurable (fun q : Ω × ℝ => Sg q.2 q.1) := hM.sigma_meas.comp measurable_swap
    have h2 : Measurable (fun q : Ω × ℝ => sb q.2) := hsbmeas.comp measurable_snd
    exact hν.cont.measurable.comp (measurable_mat_sub h1 h2)
  have iI := Iblk_integrable_cell P hM hsbmeas hsbint hc hd (c := c) (d := d)
  refine Integrable.mono' (iI.const_mul Cν) ?_ ?_
  · exact (hF.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Set.Icc c d))
      ).aestronglyMeasurable
  · filter_upwards [s1_sub_intOn_gen P hM hsbmeas hsbint] with ω h1
    have hsub : Set.Icc c d ⊆ Set.Icc 0 t := Set.Icc_subset_Icc hc hd
    have e0 : 0 ≤ ∫ σ in Set.Icc c d, ν (Sg σ ω - sb σ) :=
      setIntegral_nonneg measurableSet_Icc fun σ _ => hν.nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg e0]
    have hmeasσ : Measurable (fun σ => ν (Sg σ ω - sb σ)) :=
      hF.comp (measurable_const.prodMk measurable_id)
    have hint : IntegrableOn (fun σ => ν (Sg σ ω - sb σ)) (Set.Icc c d) := by
      refine Integrable.mono' ((h1.mono_set hsub).const_mul Cν) hmeasσ.aestronglyMeasurable
        (ae_of_all _ fun σ => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (hν.nonneg _)]
      exact hν.le_s1 _
    calc ∫ σ in Set.Icc c d, ν (Sg σ ω - sb σ)
        ≤ ∫ σ in Set.Icc c d, Cν * s1Norm (Sg σ ω - sb σ) :=
          integral_mono hint ((h1.mono_set hsub).const_mul Cν) fun σ => hν.le_s1 _
      _ = Cν * ∫ σ in Set.Icc c d, s1Norm (Sg σ ω - sb σ) := integral_const_mul _ _

/-- A genuine vector martingale with covariation density gives the cell interface for all cells. -/
lemma CellIface.of_martingale {ℱ : Filtration ℝ mΩ} {t : ℝ} {M : ℝ → Ω → (ℝ^p)}
    {Sg : ℝ → Ω → Matrix (Fin p) (Fin p) ℝ} (hM : IsVectorMartingaleWithCovariation P ℱ t M Sg) :
    CellIface P ℱ t M Sg (fun _ _ => True) where
  adapted τ _ i := (hM.martingale i).1 τ
  sq_int := hM.sq_int
  zero := hM.zero
  orth τ τ' hτ hττ' hτ' _ w hw hw2 i := by
    have hm1 : MemLp (M τ') 2 P := hM.sq_int τ' ⟨hτ.trans hττ', hτ'⟩
    exact (integral_mul_martingale P ℱ (hM.martingale i) hττ' hw hw2 (memLp_coord P hm1 i)).symm.symm
  cov τ τ' hτ hττ' hτ' _ z hz K hzK a b := cov_pair P ℱ t M Sg hM τ τ' hτ hττ' hτ' z hz K hzK a b
  sigma_meas := hM.sigma_meas
  sigma_int := hM.sigma_int
  sigma_pathint := hM.sigma_pathint
  sigma_entry_int := hM.sigma_entry_int

end HRS.Uniform.Q45
