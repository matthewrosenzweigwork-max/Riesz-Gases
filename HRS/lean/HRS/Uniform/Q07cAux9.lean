import HRS.Uniform.Q07cAux8

/-!
# Q07c, part 9: Hilbert–Schmidt integrand bookkeeping for the coupling construction
-/

noncomputable section

open HRS HRS.MRep
open MeasureTheory Filter Topology HRS.HilbertCLTAux ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.Uniform.Q07c

section HS

universe u

variable {Ω' : Type u} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
  {ℱ' : Filtration ℝ mΩ'} {ι : Type u} [Countable ι]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
variable {κ : Type*} [Countable κ]

lemma measurable_hsSq_slice {g : ℝ → Ω' → κ → H} (hg : ∀ k, IsProgressive ℱ' (fun r ω => g r ω k))
    (S : ℝ) : Measurable fun ω' => ∫⁻ r in Set.Icc 0 S, ∑' k, ‖g r ω' k‖ₑ ^ 2 := by
  have hf : Measurable fun p : ℝ × Ω' => ∑' k, ‖g p.1 p.2 k‖ₑ ^ 2 :=
    Measurable.ennreal_tsum fun k =>
      ((isProgressive_measurable_uncurry (hg k)).enorm).pow_const 2
  exact (hf.comp measurable_swap).lintegral_prod_right' (ν := volume.restrict (Set.Icc 0 S))

theorem hsInt_comp_fst {g : ℝ → Ω' → κ → H} {S : ℝ} (hg : IsHSIntegrand P' ℱ' S g) :
    IsHSIntegrand (P'.prod (wMeasure ι))
      (prodFiltration P' (wMeasure ι) ℱ' (wFiltration ι)) S (fun r p k => g r p.1 k) := by
  have hπp : MeasurePreserving (Prod.fst : Ω' × (ι → WienerSeq) → Ω') (P'.prod (wMeasure ι)) P' :=
    measurePreserving_fst
  have hπm : ∀ s, Measurable[prodFiltration P' (wMeasure ι) ℱ' (wFiltration ι) s, ℱ' s]
      (Prod.fst : Ω' × (ι → WienerSeq) → Ω') := fun s =>
    Measurable.of_comap_le (le_sup_of_le_left le_sup_left)
  refine ⟨fun k => isProgressive_comp_π hπm (hg.prog k), fun r p => hg.summable r p.1, ?_⟩
  have h := hg.sq
  unfold hsSqIntegralOn at h ⊢
  rw [hπp.lintegral_comp (measurable_hsSq_slice hg.prog S)]
  exact h

end HS

section DetHS

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
variable {ιe : Type*} [Countable ιe] {e : HilbertBasis ιe ℝ H} {t : ℝ} {Sb : ℝ → H →L[ℝ] H}
  {Tf : ℝ → ℝ}

lemma _root_.HRS.PCDetData.summable_ite (hD : PCDetData e t Sb Tf) (r : ℝ) :
    Summable fun j => ‖if r ≤ t then Sb r (e j) else 0‖ ^ 2 := by
  by_cases hr : r ∈ Set.Icc 0 t
  · simpa [hr.2] using (hD.trace r hr).summable
  · have : Sb r = 0 := hD.zero r hr
    simp [this]

lemma _root_.HRS.PCDetData.tsum_ite_le (hD : PCDetData e t Sb Tf) (r : ℝ) :
    ∑' j, ‖(if r ≤ t then Sb r (e j) else 0 : H)‖ₑ ^ 2 ≤
      (Set.Icc 0 t).indicator (fun r => ENNReal.ofReal (Tf r)) r := by
  by_cases hr : r ∈ Set.Icc 0 t
  · simp only [hr, Set.indicator_of_mem, hr.2, ite_true]
    have h1 : ∀ j, ‖Sb r (e j)‖ₑ ^ 2 = ENNReal.ofReal (‖Sb r (e j)‖ ^ 2) := fun j => by
      rw [← ofReal_norm_eq_enorm, ENNReal.ofReal_pow (norm_nonneg _)]
    simp only [h1]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => sq_nonneg _) (hD.trace r hr).summable,
      (hD.trace r hr).tsum_eq]
  · have : Sb r = 0 := hD.zero r hr
    simp [this, hr]

theorem _root_.HRS.PCDetData.hsInt (hD : PCDetData e t Sb Tf) (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℝ mΩ) (S : ℝ) :
    IsHSIntegrand P ℱ S (fun r (_ : Ω) (j : ιe) => if r ≤ t then Sb r (e j) else 0) := by
  refine ⟨fun j => ?_, fun r ω => hD.summable_ite r, ?_⟩
  · exact pc_isProgressive_det (ℱ := ℱ) (Ω := Ω)
      (g := fun r => if r ≤ t then Sb r (e j) else 0)
      (Measurable.ite measurableSet_Iic (hD.meas (e j)) measurable_const)
  · unfold hsSqIntegralOn
    simp only [lintegral_const, measure_univ, mul_one]
    refine lt_of_le_of_lt (lintegral_mono' le_rfl (fun r => hD.tsum_ite_le r)) ?_
    refine lt_of_le_of_lt (lintegral_mono_set (Set.subset_univ _)) ?_
    rw [lintegral_indicator measurableSet_Icc, Measure.restrict_univ]
    exact hD.Tint.lintegral_lt_top

end DetHS

section ZBase

open Classical

variable {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
  {ℱ' : Filtration ℝ mΩ'}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
variable {ιe κ : Type*} [Countable ιe] [Countable κ] (e : HilbertBasis ιe ℝ H)
variable {Sb : ℝ → H →L[ℝ] H} {Φ : ℝ → Ω' → κ → H} {ψ : ιe → ℝ → Ω' → κ ⊕ ιe → ℝ}

lemma Zint_prog (hSbm : OpMeas Sb) (hΦp : ∀ k, IsProgressive ℱ' (fun r ω => Φ r ω k))
    (hψp : ∀ j a, IsProgressive ℱ' (fun r ω => ψ j r ω a))
    (hrow : ∀ r ω a, Summable fun j => ψ j r ω a ^ 2) (a : κ ⊕ ιe) :
    IsProgressive ℱ' (fun r ω => ZVec (e := e) (Sb r) (Φ r ω) (fun j => ψ j r ω) a) := by
  intro i
  letI : MeasurableSpace (Set.Iic i × Ω') := Subtype.instMeasurableSpace.prod (ℱ' i)
  have hv : Measurable fun z : Set.Iic i × Ω' => PsiVec e (fun j => ψ j z.1 z.2) a := by
    refine measurable_of_inner_basis e (fun m => ?_)
    have : (fun z : Set.Iic i × Ω' => inner ℝ (e m) (PsiVec e (fun j => ψ j z.1 z.2) a)) =
        fun z => ψ m z.1 z.2 a := by
      funext z; unfold PsiVec; rw [real_inner_comm]; exact pcVec_inner_basis e (hrow _ _ a) m
    rw [this]; exact hψp m a i
  have hSbz : OpMeas fun z : Set.Iic i × Ω' => Sb z.1.1 := fun x =>
    (hSbm x).comp (measurable_subtype_coe.comp measurable_fst)
  have h2 := hSbz.apply hv
  have h1 : Measurable fun z : Set.Iic i × Ω' => Sum.elim (Φ z.1 z.2) (fun _ => (0 : H)) a := by
    rcases a with k | l
    · exact hΦp k i
    · exact measurable_const
  exact h1.sub h2

omit [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] in
lemma norm_sub_sq_le (x y : H) : ‖x - y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
  have h := norm_sub_le x y
  nlinarith [norm_nonneg x, norm_nonneg y, norm_nonneg (x - y), sq_nonneg (‖x‖ - ‖y‖)]

lemma Zint_summable (hSbsymm : ∀ r x y, inner ℝ (Sb r x) y = inner ℝ x (Sb r y))
    (hSbHS : ∀ r, Summable fun i => ‖Sb r (e i)‖ ^ 2) (hΦs : ∀ r ω, Summable fun k => ‖Φ r ω k‖ ^ 2)
    (ho : ∀ r ω i j, HasSum (fun a => ψ i r ω a * ψ j r ω a) (if i = j then (1 : ℝ) else 0))
    (r : ℝ) (ω : Ω') :
    Summable fun a => ‖ZVec (e := e) (Sb r) (Φ r ω) (fun j => ψ j r ω) a‖ ^ 2 := by
  have h1 : Summable fun a : κ ⊕ ιe => ‖Sum.elim (Φ r ω) (fun _ => (0 : H)) a‖ ^ 2 :=
    (HasSum.sum (f := fun a : κ ⊕ ιe => ‖Sum.elim (Φ r ω) (fun _ => (0 : H)) a‖ ^ 2)
      (a := ∑' k, ‖Φ r ω k‖ ^ 2) (b := 0) (by exact (hΦs r ω).hasSum)
      (by convert (hasSum_zero : HasSum (fun _ : ιe => (0 : ℝ)) 0) using 1; funext l; simp)).summable
  have h2 := (psiVec_frame_hs (e := e) (ψ := fun j => ψ j r ω) (ho r ω) (hSbsymm r)
    (hSbHS r)).summable
  refine Summable.of_nonneg_of_le (fun a => sq_nonneg _) (fun a => ?_)
    ((h1.mul_left 2).add (h2.mul_left 2))
  exact norm_sub_sq_le _ _

lemma Zint_tsum_le (hSbsymm : ∀ r x y, inner ℝ (Sb r x) y = inner ℝ x (Sb r y))
    (hSbHS : ∀ r, Summable fun i => ‖Sb r (e i)‖ ^ 2) (hΦs : ∀ r ω, Summable fun k => ‖Φ r ω k‖ ^ 2)
    (ho : ∀ r ω i j, HasSum (fun a => ψ i r ω a * ψ j r ω a) (if i = j then (1 : ℝ) else 0))
    (r : ℝ) (ω : Ω') :
    ∑' a, ‖ZVec (e := e) (Sb r) (Φ r ω) (fun j => ψ j r ω) a‖ₑ ^ 2 ≤
      2 * ∑' k, ‖Φ r ω k‖ₑ ^ 2 + 2 * ENNReal.ofReal (∑' i, ‖Sb r (e i)‖ ^ 2) := by
  have hs := Zint_summable e hSbsymm hSbHS hΦs ho r ω
  have e1 : ∑' a, ‖ZVec (e := e) (Sb r) (Φ r ω) (fun j => ψ j r ω) a‖ₑ ^ 2 =
      ENNReal.ofReal (∑' a, ‖ZVec (e := e) (Sb r) (Φ r ω) (fun j => ψ j r ω) a‖ ^ 2) := by
    rw [ENNReal.ofReal_tsum_of_nonneg (fun a => sq_nonneg _) hs]
    exact tsum_congr fun a => by rw [← ofReal_norm_eq_enorm, ENNReal.ofReal_pow (norm_nonneg _)]
  have h1 : HasSum (fun a : κ ⊕ ιe => ‖Sum.elim (Φ r ω) (fun _ => (0 : H)) a‖ ^ 2)
      (∑' k, ‖Φ r ω k‖ ^ 2) :=
    HasSum.sum (f := fun a : κ ⊕ ιe => ‖Sum.elim (Φ r ω) (fun _ => (0 : H)) a‖ ^ 2)
      (a := ∑' k, ‖Φ r ω k‖ ^ 2) (b := 0) (by exact (hΦs r ω).hasSum)
      (by convert (hasSum_zero : HasSum (fun _ : ιe => (0 : ℝ)) 0) using 1; funext l; simp) |>
      fun h => by simpa using h
  have h2 := psiVec_frame_hs (e := e) (ψ := fun j => ψ j r ω) (ho r ω) (hSbsymm r) (hSbHS r)
  have hreal : ∑' a, ‖ZVec (e := e) (Sb r) (Φ r ω) (fun j => ψ j r ω) a‖ ^ 2 ≤
      2 * ∑' k, ‖Φ r ω k‖ ^ 2 + 2 * ∑' i, ‖Sb r (e i)‖ ^ 2 := by
    calc ∑' a, ‖ZVec (e := e) (Sb r) (Φ r ω) (fun j => ψ j r ω) a‖ ^ 2
        ≤ ∑' a, (2 * ‖Sum.elim (Φ r ω) (fun _ => (0 : H)) a‖ ^ 2 +
            2 * ‖Sb r (PsiVec e (fun j => ψ j r ω) a)‖ ^ 2) :=
          hs.tsum_le_tsum (fun a => norm_sub_sq_le _ _)
            ((h1.summable.mul_left 2).add (h2.summable.mul_left 2))
      _ = 2 * ∑' k, ‖Φ r ω k‖ ^ 2 + 2 * ∑' i, ‖Sb r (e i)‖ ^ 2 := by
          rw [Summable.tsum_add (h1.summable.mul_left 2) (h2.summable.mul_left 2), tsum_mul_left,
            tsum_mul_left, h1.tsum_eq, h2.tsum_eq]
  rw [e1]
  have hx : 0 ≤ ∑' k, ‖Φ r ω k‖ ^ 2 := tsum_nonneg fun k => sq_nonneg _
  have hy : 0 ≤ ∑' i, ‖Sb r (e i)‖ ^ 2 := tsum_nonneg fun k => sq_nonneg _
  calc ENNReal.ofReal (∑' a, ‖ZVec (e := e) (Sb r) (Φ r ω) (fun j => ψ j r ω) a‖ ^ 2)
      ≤ ENNReal.ofReal (2 * ∑' k, ‖Φ r ω k‖ ^ 2 + 2 * ∑' i, ‖Sb r (e i)‖ ^ 2) :=
        ENNReal.ofReal_le_ofReal hreal
    _ = 2 * ∑' k, ‖Φ r ω k‖ₑ ^ 2 + 2 * ENNReal.ofReal (∑' i, ‖Sb r (e i)‖ ^ 2) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by norm_num),
          ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_tsum_of_nonneg (fun k => sq_nonneg _)
            (hΦs r ω)]
        simp only [ENNReal.ofReal_ofNat]
        congr 2
        exact tsum_congr fun k => by rw [← ofReal_norm_eq_enorm, ENNReal.ofReal_pow (norm_nonneg _)]

theorem Zint_hsInt {S : ℝ} (hSbm : OpMeas Sb)
    (hSbsymm : ∀ r x y, inner ℝ (Sb r x) y = inner ℝ x (Sb r y))
    (hSbHS : ∀ r, Summable fun i => ‖Sb r (e i)‖ ^ 2) (hΦ : IsHSIntegrand P' ℱ' S Φ)
    (ho : ∀ r ω i j, HasSum (fun a => ψ i r ω a * ψ j r ω a) (if i = j then (1 : ℝ) else 0))
    (hψp : ∀ j a, IsProgressive ℱ' (fun r ω => ψ j r ω a))
    (hTr : ∫⁻ r in Set.Icc 0 S, ENNReal.ofReal (∑' i, ‖Sb r (e i)‖ ^ 2) < ⊤) :
    IsHSIntegrand P' ℱ' S (fun r ω a => ZVec (e := e) (Sb r) (Φ r ω) (fun j => ψ j r ω) a) := by
  have hrow : ∀ r ω a, Summable fun j => ψ j r ω a ^ 2 := fun r ω a =>
    rowsum_le_one (fun j => ψ j r ω) (ho r ω) a
  refine ⟨Zint_prog e hSbm hΦ.prog hψp hrow, fun r ω =>
    Zint_summable e hSbsymm hSbHS hΦ.summable ho r ω, ?_⟩
  unfold hsSqIntegralOn
  set A : ℝ → Ω' → ℝ≥0∞ := fun r ω => ∑' k, ‖Φ r ω k‖ₑ ^ 2 with hA
  set B : ℝ → ℝ≥0∞ := fun r => ENNReal.ofReal (∑' i, ‖Sb r (e i)‖ ^ 2) with hB
  have hAm : ∀ ω, Measurable fun r => A r ω := fun ω => by
    have : Measurable fun p : ℝ × Ω' => A p.1 p.2 :=
      Measurable.ennreal_tsum fun k =>
        ((isProgressive_measurable_uncurry (hΦ.prog k)).enorm).pow_const 2
    exact Measurable.of_uncurry_right this
  have hle : ∀ r ω, ∑' a, ‖ZVec (e := e) (Sb r) (Φ r ω) (fun j => ψ j r ω) a‖ₑ ^ 2 ≤
      2 * A r ω + 2 * B r := fun r ω => Zint_tsum_le e hSbsymm hSbHS hΦ.summable ho r ω
  have hAfin : ∫⁻ ω, (∫⁻ r in Set.Icc 0 S, A r ω) ∂P' < ⊤ := hΦ.sq
  refine lt_of_le_of_lt (lintegral_mono fun ω => lintegral_mono fun r => hle r ω) ?_
  have e1 : ∀ ω, ∫⁻ r in Set.Icc 0 S, (2 * A r ω + 2 * B r) =
      2 * (∫⁻ r in Set.Icc 0 S, A r ω) + 2 * (∫⁻ r in Set.Icc 0 S, B r) := fun ω => by
    rw [lintegral_add_left ((hAm ω).const_mul 2), lintegral_const_mul' _ _ (by simp),
      lintegral_const_mul' _ _ (by simp)]
  simp only [e1]
  have hXm : Measurable fun ω => ∫⁻ r in Set.Icc 0 S, A r ω := measurable_hsSq_slice hΦ.prog S
  rw [lintegral_add_left (hXm.const_mul 2), lintegral_const, measure_univ, mul_one,
    lintegral_const_mul' _ _ (by simp)]
  refine ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top (by simp) hAfin, ENNReal.mul_lt_top (by simp) hTr⟩

end ZBase

end HRS.Uniform.Q07c
