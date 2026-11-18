import Mathlib

open MeasureTheory ProbabilityTheory Function Set
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace HRS.External.Entropy

/-- The binary Pinsker function. -/
def binG (q p : ℝ) : ℝ :=
  p * Real.log p - p * Real.log q + (1 - p) * Real.log (1 - p) - (1 - p) * Real.log (1 - q)
    - 2 * (p - q) ^ 2

lemma binG_continuousOn (q : ℝ) : ContinuousOn (binG q) (Icc 0 1) := by
  unfold binG
  have h1 : Continuous fun p : ℝ => p * Real.log p := Real.continuous_mul_log
  have h2 : Continuous fun p : ℝ => (1 - p) * Real.log (1 - p) :=
    Real.continuous_mul_log.comp (continuous_const.sub continuous_id)
  have : Continuous fun p : ℝ => p * Real.log p - p * Real.log q + (1 - p) * Real.log (1 - p) - (1 - p) * Real.log (1 - q)
    - 2 * (p - q) ^ 2 := by fun_prop
  exact this.continuousOn

lemma binG_deriv (q p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    HasDerivAt (binG q) (Real.log p - Real.log q - Real.log (1 - p) + Real.log (1 - q) - 4 * (p - q)) p := by
  have h1 : HasDerivAt (fun p : ℝ => p * Real.log p) (Real.log p + 1) p :=
    Real.hasDerivAt_mul_log hp0.ne'
  have hp1' : (1 - p) ≠ 0 := by linarith
  have h2 : HasDerivAt (fun p : ℝ => (1 - p) * Real.log (1 - p)) (-Real.log (1 - p) - 1) p := by
    have h3 : HasDerivAt (fun p : ℝ => 1 - p) (-1) p := by simpa using (hasDerivAt_id p).const_sub 1
    have := (Real.hasDerivAt_mul_log hp1').comp p h3
    exact this.congr_deriv (by ring)
  have h4 : HasDerivAt (fun p : ℝ => 2 * (p - q) ^ 2) (4 * (p - q)) p := by
    have := ((hasDerivAt_id p).sub_const q).pow 2 |>.const_mul 2
    exact this.congr_deriv (by simp only [id]; push_cast; ring)
  have h5 : HasDerivAt (fun p : ℝ => p * Real.log q) (Real.log q) p := by
    simpa using (hasDerivAt_id p).mul_const (Real.log q)
  have h6 : HasDerivAt (fun p : ℝ => (1 - p) * Real.log (1 - q)) (-Real.log (1 - q)) p := by
    simpa using ((hasDerivAt_id p).const_sub 1).mul_const (Real.log (1 - q))
  have := (((h1.sub h5).add h2).sub h6).sub h4
  unfold binG
  convert this using 1
  ring

/-- Derivative of `binG`. -/
def binG' (q p : ℝ) : ℝ := Real.log p - Real.log q - Real.log (1 - p) + Real.log (1 - q) - 4 * (p - q)

lemma binG'_hasDeriv (q p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    HasDerivAt (binG' q) (1 / p + 1 / (1 - p) - 4) p := by
  have hp1' : (1 - p) ≠ 0 := by linarith
  have h1 : HasDerivAt Real.log (p⁻¹) p := Real.hasDerivAt_log hp0.ne'
  have h3 : HasDerivAt (fun p : ℝ => 1 - p) (-1) p := by simpa using (hasDerivAt_id p).const_sub 1
  have h2 := (Real.hasDerivAt_log hp1').comp p h3
  have h4 : HasDerivAt (fun p : ℝ => 4 * (p - q)) 4 p := by
    simpa using ((hasDerivAt_id p).sub_const q).const_mul 4
  have := (((h1.sub_const (Real.log q)).sub h2).add_const (Real.log (1 - q))).sub h4
  unfold binG'
  exact this.congr_deriv (by field_simp; ring)

lemma binG'_monotone (q : ℝ) : MonotoneOn (binG' q) (Ioo 0 1) := by
  refine monotoneOn_of_deriv_nonneg (convex_Ioo 0 1) ?_ ?_ ?_
  · intro p hp
    exact (binG'_hasDeriv q p hp.1 hp.2).continuousAt.continuousWithinAt
  · rw [interior_Ioo]
    intro p hp
    exact (binG'_hasDeriv q p hp.1 hp.2).differentiableAt.differentiableWithinAt
  · rw [interior_Ioo]
    intro p hp
    rw [(binG'_hasDeriv q p hp.1 hp.2).deriv]
    have h1 : 0 < 1 - p := by linarith [hp.2]
    have : 1 / p + 1 / (1 - p) - 4 = (1 - 2 * p) ^ 2 / (p * (1 - p)) := by
      field_simp [hp.1.ne', h1.ne']; ring
    rw [this]
    exact div_nonneg (sq_nonneg _) (mul_pos hp.1 h1).le

lemma binG'_q (q : ℝ) : binG' q q = 0 := by unfold binG'; ring

lemma binG_self (q : ℝ) : binG q q = 0 := by unfold binG; ring

lemma binG_nonneg {q p : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ binG q p := by
  rcases le_total q p with hqp | hpq
  · have hmono : MonotoneOn (binG q) (Icc q 1) := by
      refine monotoneOn_of_deriv_nonneg (convex_Icc q 1) ?_ ?_ ?_
      · exact (binG_continuousOn q).mono (Icc_subset_Icc hq0.le le_rfl)
      · rw [interior_Icc]
        intro x hx
        exact (binG_deriv q x (by linarith [hx.1]) hx.2).differentiableAt.differentiableWithinAt
      · rw [interior_Icc]
        intro x hx
        rw [(binG_deriv q x (by linarith [hx.1]) hx.2).deriv]
        have := binG'_monotone q (a := q) (b := x) ⟨hq0, hq1⟩ ⟨by linarith [hx.1], hx.2⟩ hx.1.le
        rw [binG'_q] at this
        unfold binG' at this
        linarith
    have := hmono (a := q) (b := p) ⟨le_rfl, hq1.le⟩ ⟨hqp, hp1⟩ hqp
    rw [binG_self] at this
    exact this
  · have hanti : AntitoneOn (binG q) (Icc 0 q) := by
      refine antitoneOn_of_deriv_nonpos (convex_Icc 0 q) ?_ ?_ ?_
      · exact (binG_continuousOn q).mono (Icc_subset_Icc le_rfl hq1.le)
      · rw [interior_Icc]
        intro x hx
        exact (binG_deriv q x hx.1 (by linarith [hx.2])).differentiableAt.differentiableWithinAt
      · rw [interior_Icc]
        intro x hx
        rw [(binG_deriv q x hx.1 (by linarith [hx.2])).deriv]
        have := binG'_monotone q (a := x) (b := q) ⟨hx.1, by linarith [hx.2]⟩ ⟨hq0, hq1⟩ hx.2.le
        rw [binG'_q] at this
        unfold binG' at this
        linarith
    have := hanti (a := p) (b := q) ⟨hp0, hpq⟩ ⟨hq0.le, le_rfl⟩ hpq
    rw [binG_self] at this
    exact this

open InformationTheory in
lemma klFun_binary {q p : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    q * klFun (p / q) + (1 - q) * klFun ((1 - p) / (1 - q)) = binG q p + 2 * (p - q) ^ 2 := by
  have hq1' : 1 - q ≠ 0 := by linarith
  have e1 : q * (p / q * Real.log (p / q)) = p * (Real.log p - Real.log q) := by
    rcases hp0.eq_or_lt with h | h
    · subst h; simp
    · rw [Real.log_div h.ne' hq0.ne']; field_simp
  have e2 : (1 - q) * ((1 - p) / (1 - q) * Real.log ((1 - p) / (1 - q))) =
      (1 - p) * (Real.log (1 - p) - Real.log (1 - q)) := by
    rcases (sub_nonneg.2 hp1).eq_or_lt with h | h
    · rw [← h]; simp
    · rw [Real.log_div h.ne' hq1']; field_simp
  unfold klFun binG
  have : q * (p / q * Real.log (p / q) + 1 - p / q) + (1 - q) * ((1 - p) / (1 - q) * Real.log ((1 - p) / (1 - q)) + 1 - (1 - p) / (1 - q))
      = q * (p / q * Real.log (p / q)) + (1 - q) * ((1 - p) / (1 - q) * Real.log ((1 - p) / (1 - q))) := by
    field_simp; ring
  rw [this, e1, e2]; ring

open InformationTheory in
lemma pinsker_bool (P Q : Measure Bool) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    ENNReal.ofReal (2 * (P.real {true} - Q.real {true}) ^ 2) ≤ klDiv P Q := by
  by_cases hac : P ≪ Q
  swap
  · rw [klDiv_of_not_ac hac]; exact le_top
  have hint : Integrable (llr P Q) P := Integrable.of_finite
  have hfin : klDiv P Q = ENNReal.ofReal (klDiv P Q).toReal := by
    rw [ENNReal.ofReal_toReal (klDiv_ne_top hac hint)]
  rw [hfin]
  apply ENNReal.ofReal_le_ofReal
  rw [toReal_klDiv_eq_integral_klFun hac, integral_fintype Integrable.of_finite]
  have hrn : ∀ b : Bool, Q.real {b} * (P.rnDeriv Q b).toReal = P.real {b} := by
    intro b
    have := Measure.setLIntegral_rnDeriv hac ({b} : Set Bool)
    rw [lintegral_singleton] at this
    simp only [measureReal_def]
    rw [← ENNReal.toReal_mul, mul_comm, this]
  have hsum : ∀ P : Measure Bool, IsProbabilityMeasure P → P.real {true} + P.real {false} = 1 := by
    intro P hP
    have h2 : ({true} : Set Bool)ᶜ = {false} := by ext x; cases x <;> simp
    have := probReal_compl_eq_one_sub (μ := P) (measurableSet_singleton true)
    rw [h2] at this
    linarith
  simp only [Fintype.univ_bool, Finset.sum_insert, Finset.mem_singleton, Bool.true_eq_false, not_false_eq_true, Finset.sum_singleton, smul_eq_mul]
  have hnn : 0 ≤ Q.real {true} * klFun ((P.rnDeriv Q true).toReal) + Q.real {false} * klFun ((P.rnDeriv Q false).toReal) :=
    add_nonneg (mul_nonneg measureReal_nonneg (klFun_nonneg ENNReal.toReal_nonneg))
      (mul_nonneg measureReal_nonneg (klFun_nonneg ENNReal.toReal_nonneg))
  have hP := hsum P inferInstance
  have hQ := hsum Q inferInstance
  have hp0 : 0 ≤ P.real {true} := measureReal_nonneg
  have hp1 : P.real {true} ≤ 1 := by linarith [measureReal_nonneg (μ := P) (s := {false})]
  have hq0' : 0 ≤ Q.real {true} := measureReal_nonneg
  rcases hq0'.eq_or_lt with hq0 | hq0
  · -- Q {true} = 0 ⇒ P {true} = 0
    have : P {true} = 0 := hac (by
      have := hq0.symm; rwa [measureReal_def, ENNReal.toReal_eq_zero_iff, or_iff_left (measure_ne_top _ _)] at this)
    have h' : P.real {true} = 0 := by simp [measureReal_def, this]
    refine le_trans (le_of_eq ?_) hnn
    rw [h', ← hq0]; norm_num
  rcases (show Q.real {true} ≤ 1 by linarith [measureReal_nonneg (μ := Q) (s := {false})]).eq_or_lt with hq1 | hq1
  · have hf : Q.real {false} = 0 := by linarith
    have : P {false} = 0 := hac (by rwa [measureReal_def, ENNReal.toReal_eq_zero_iff, or_iff_left (measure_ne_top _ _)] at hf)
    have h' : P.real {false} = 0 := by simp [measureReal_def, this]
    have : P.real {true} = 1 := by linarith
    refine le_trans (le_of_eq ?_) hnn
    rw [this, hq1]; norm_num
  · have hqf : Q.real {false} = 1 - Q.real {true} := by linarith
    have hpf : P.real {false} = 1 - P.real {true} := by linarith
    have e1 : (P.rnDeriv Q true).toReal = P.real {true} / Q.real {true} := by
      rw [eq_div_iff hq0.ne']; rw [mul_comm]; exact hrn true
    have e2 : (P.rnDeriv Q false).toReal = (1 - P.real {true}) / (1 - Q.real {true}) := by
      rw [eq_div_iff (by linarith)]; rw [← hqf, ← hpf, mul_comm]; exact hrn false
    rw [e1, e2, hqf]
    have := klFun_binary hq0 hq1 hp0 hp1
    have hb := binG_nonneg hq0 hq1 hp0 hp1
    linarith

section TV

variable {α : Type*} [MeasurableSpace α]

/-- Total variation distance of two measures: `sup_A |P A - Q A|` over measurable sets `A`
(real-valued). -/
def tvDist (P Q : Measure α) : ℝ :=
  ⨆ A : {A : Set α // MeasurableSet A}, |P.real A.1 - Q.real A.1|

lemma abs_measureReal_sub_le_one (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (A : Set α) : |P.real A - Q.real A| ≤ 1 := by
  have h1 : P.real A ≤ 1 := measureReal_le_one
  have h2 : Q.real A ≤ 1 := measureReal_le_one
  have h3 : 0 ≤ P.real A := measureReal_nonneg
  have h4 : 0 ≤ Q.real A := measureReal_nonneg
  rw [abs_le]; constructor <;> linarith

lemma bddAbove_tv (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    BddAbove (Set.range fun A : {A : Set α // MeasurableSet A} => |P.real A.1 - Q.real A.1|) :=
  ⟨1, by rintro _ ⟨A, rfl⟩; exact abs_measureReal_sub_le_one P Q A.1⟩

lemma abs_le_tvDist (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {A : Set α} (hA : MeasurableSet A) : |P.real A - Q.real A| ≤ tvDist P Q :=
  le_ciSup (bddAbove_tv P Q) (⟨A, hA⟩ : {A : Set α // MeasurableSet A})

lemma tvDist_nonneg (P Q : Measure α) : 0 ≤ tvDist P Q :=
  Real.iSup_nonneg fun _ => abs_nonneg _

lemma tvDist_le_one (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    tvDist P Q ≤ 1 :=
  ciSup_le fun A => abs_measureReal_sub_le_one P Q A.1

open InformationTheory in
/-- Pinsker for a single event. -/
lemma pinsker_event (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {A : Set α} (hA : MeasurableSet A) :
    ENNReal.ofReal (2 * (P.real A - Q.real A) ^ 2) ≤ klDiv P Q := by
  classical
  have hg : Measurable fun x => decide (x ∈ A) := measurable_to_bool (by
    have : (fun x => decide (x ∈ A)) ⁻¹' {true} = A := by ext x; simp
    rw [this]; exact hA)
  have : IsProbabilityMeasure (P.map fun x => decide (x ∈ A)) := inferInstance
  have : IsProbabilityMeasure (Q.map fun x => decide (x ∈ A)) := inferInstance
  have h := pinsker_bool (P.map fun x => decide (x ∈ A)) (Q.map fun x => decide (x ∈ A))
  have hP : (P.map fun x => decide (x ∈ A)).real {true} = P.real A := by
    rw [measureReal_def, measureReal_def, Measure.map_apply hg (measurableSet_singleton _)]
    congr 2; ext x; simp
  have hQ : (Q.map fun x => decide (x ∈ A)).real {true} = Q.real A := by
    rw [measureReal_def, measureReal_def, Measure.map_apply hg (measurableSet_singleton _)]
    congr 2; ext x; simp
  rw [hP, hQ] at h
  exact h.trans (klDiv_map_le P Q hg)

open InformationTheory in
/-- **Pinsker's inequality**, `‖P - Q‖_TV ≤ √(KL(P‖Q)/2)` with `‖P - Q‖_TV = sup_A |P A - Q A|`. -/
theorem tvDist_le_sqrt_klDiv (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (h : klDiv P Q ≠ ⊤) : tvDist P Q ≤ Real.sqrt ((klDiv P Q).toReal / 2) := by
  refine ciSup_le fun A => ?_
  have := pinsker_event P Q A.2
  have h2 : 2 * (P.real A.1 - Q.real A.1) ^ 2 ≤ (klDiv P Q).toReal := by
    have := (ENNReal.ofReal_le_iff_le_toReal h).1 this
    exact this
  apply Real.abs_le_sqrt
  linarith

open InformationTheory in
/-- Pinsker's inequality in squared, `ENNReal` form (no finiteness hypothesis). -/
theorem pinsker (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    ENNReal.ofReal (2 * tvDist P Q ^ 2) ≤ klDiv P Q := by
  by_cases h : klDiv P Q = ⊤
  · rw [h]; exact le_top
  have h1 := tvDist_le_sqrt_klDiv P Q h
  have h0 := tvDist_nonneg P Q
  rw [← ENNReal.ofReal_toReal h]
  apply ENNReal.ofReal_le_ofReal
  have := Real.sq_sqrt (show 0 ≤ (klDiv P Q).toReal / 2 from by positivity)
  nlinarith [sq_nonneg (tvDist P Q), Real.sqrt_nonneg ((klDiv P Q).toReal / 2)]

end TV

section Subadditivity

open InformationTheory

variable {E : Type*} [MeasurableSpace E]

/-- Chain rule consequence: `KL(ρ_1‖μ) + KL(ρ_2‖ν) ≤ KL(ρ‖μ⊗ν)`. -/
lemma klDiv_fst_add_snd_le {F : Type*} [MeasurableSpace F] [StandardBorelSpace F] [Nonempty F]
    (ρ : Measure (E × F)) [IsProbabilityMeasure ρ] (μ : Measure E) (ν : Measure F)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    klDiv ρ.fst μ + klDiv ρ.snd ν ≤ klDiv ρ (μ.prod ν) := by
  have hdis : ρ.fst ⊗ₘ ρ.condKernel = ρ := Measure.disintegrate ρ ρ.condKernel
  have h1 : klDiv ρ (μ.prod ν) = klDiv ρ.fst μ + klDiv (ρ.fst ⊗ₘ ρ.condKernel) (ρ.fst ⊗ₘ Kernel.const E ν) := by
    rw [← Measure.compProd_const, ← klDiv_compProd_eq_add, hdis]
  rw [h1]
  gcongr
  have := klDiv_map_le (ρ.fst ⊗ₘ ρ.condKernel) (ρ.fst ⊗ₘ Kernel.const E ν) measurable_snd
  rw [hdis] at this
  have h2 : (ρ.fst ⊗ₘ Kernel.const E ν).map Prod.snd = ν := by
    rw [Measure.compProd_const]; exact Measure.snd_prod
  rw [h2] at this
  rw [hdis]
  exact this

/-- **Subadditivity of relative entropy for a product reference measure**: for a probability measure
`P` on `Fin N → E` with marginals `P_i = P.map (eval i)`,
`∑ i, KL(P_i ‖ μ) ≤ KL(P ‖ μ^{⊗N})`. -/
theorem sum_klDiv_marginals_le [StandardBorelSpace E] [Nonempty E]
    (μ : Measure E) [IsProbabilityMeasure μ] :
    ∀ (N : ℕ) (P : Measure (Fin N → E)) [IsProbabilityMeasure P],
      ∑ i : Fin N, klDiv (P.map fun x => x i) μ ≤ klDiv P (Measure.pi fun _ : Fin N => μ) := by
  intro N
  induction N with
  | zero => intro P _; simp
  | succ N ih =>
    intro P _
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N + 1) => E) 0
    have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (N + 1) => μ) 0
    let P' : Measure (E × (Fin N → E)) := P.map e
    have hP' : IsProbabilityMeasure P' := inferInstanceAs (IsProbabilityMeasure (P.map e))
    have h1 : klDiv P' (μ.prod (Measure.pi fun _ : Fin N => μ)) ≤ klDiv P (Measure.pi fun _ : Fin (N + 1) => μ) := by
      have := klDiv_map_le P (Measure.pi fun _ : Fin (N + 1) => μ) e.measurable
      have h2 : (Measure.pi fun _ : Fin (N + 1) => μ).map e = μ.prod (Measure.pi fun _ : Fin N => μ) := by
        exact hmp.map_eq
      rwa [h2] at this
    have h3 := klDiv_fst_add_snd_le P' μ (Measure.pi fun _ : Fin N => μ)
    have hfst : P'.fst = P.map fun x => x 0 := by
      show (P.map e).map Prod.fst = _
      rw [Measure.map_map measurable_fst e.measurable]; rfl
    have hsnd : P'.snd = P.map fun x => Fin.tail x := by
      show (P.map e).map Prod.snd = _
      rw [Measure.map_map measurable_snd e.measurable]; rfl
    have hT : Measurable (fun x : Fin (N + 1) → E => Fin.tail x) :=
      measurable_pi_iff.2 fun j => measurable_pi_apply _
    have hsndP : IsProbabilityMeasure P'.snd := by rw [hsnd]; infer_instance
    have h4 := ih P'.snd
    rw [Fin.sum_univ_succ]
    have h5 : ∀ j : Fin N, (P.map fun x => x j.succ) = P'.snd.map fun y => y j := by
      intro j
      rw [hsnd, Measure.map_map (measurable_pi_apply j) hT]; rfl
    simp_rw [h5, ← hfst]
    calc _ ≤ klDiv P'.fst μ + klDiv P'.snd (Measure.pi fun _ : Fin N => μ) := by gcongr
      _ ≤ _ := h3
      _ ≤ _ := h1

end Subadditivity

section Exchangeable

open InformationTheory Filter Topology

variable {E : Type*} [MeasurableSpace E]

/-- A measure on `Fin N → E` is exchangeable if it is invariant under coordinate permutations. -/
def IsExchangeable {N : ℕ} (R : Measure (Fin N → E)) : Prop :=
  ∀ σ : Equiv.Perm (Fin N), R.map (fun x i => x (σ i)) = R

lemma IsExchangeable.marginal_eq {N : ℕ} {R : Measure (Fin N → E)} (hR : IsExchangeable R)
    (i j : Fin N) : R.map (fun x => x i) = R.map (fun x => x j) := by
  have hσ := hR (Equiv.swap i j)
  have hm : Measurable fun (x : Fin N → E) k => x (Equiv.swap i j k) :=
    measurable_pi_iff.2 fun k => measurable_pi_apply _
  conv_lhs => rw [← hσ]
  rw [Measure.map_map (measurable_pi_apply i) hm]
  have : ((fun x : Fin N → E => x i) ∘ fun (x : Fin N → E) k => x (Equiv.swap i j k)) = fun x => x j := by
    ext x; simp
  rw [this]

/-- For an exchangeable `P`, `N · KL(P_1 ‖ μ) ≤ KL(P ‖ μ^{⊗N})`. -/
theorem IsExchangeable.mul_klDiv_marginal_le [StandardBorelSpace E] [Nonempty E]
    (μ : Measure E) [IsProbabilityMeasure μ] {N : ℕ} (i : Fin N) (P : Measure (Fin N → E))
    [IsProbabilityMeasure P] (hP : IsExchangeable P) :
    (N : ℝ≥0∞) * klDiv (P.map fun x => x i) μ ≤ klDiv P (Measure.pi fun _ : Fin N => μ) := by
  refine le_trans ?_ (sum_klDiv_marginals_le μ N P)
  have : ∀ j : Fin N, klDiv (P.map fun x => x j) μ = klDiv (P.map fun x => x i) μ := by
    intro j; rw [hP.marginal_eq j i]
  simp [this]

/-- **Entropy `o(N)` ⇒ first marginal close to `μ` in total variation.**
If `R_N` is an exchangeable probability measure on `E^{N+1}` with `KL(R_N ‖ μ^{⊗(N+1)}) = o(N)`
then its first marginal `π_N` satisfies `‖π_N - μ‖_TV → 0`. -/
theorem tendsto_tvDist_firstMarginal [StandardBorelSpace E] [Nonempty E]
    (μ : Measure E) [IsProbabilityMeasure μ]
    (R : ∀ N : ℕ, Measure (Fin (N + 1) → E)) [∀ N, IsProbabilityMeasure (R N)]
    (hex : ∀ N, IsExchangeable (R N))
    (hent : Tendsto (fun N : ℕ => klDiv (R N) (Measure.pi fun _ : Fin (N + 1) => μ) / ((N : ℝ≥0∞) + 1))
      atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => tvDist ((R N).map fun x => x 0) μ) atTop (𝓝 0) := by
  set a : ℕ → ℝ≥0∞ := fun N => klDiv (R N) (Measure.pi fun _ : Fin (N + 1) => μ) / ((N : ℝ≥0∞) + 1) with ha
  have hk : ∀ N, klDiv ((R N).map fun x => x 0) μ ≤ a N := by
    intro N
    have h := (hex N).mul_klDiv_marginal_le μ 0 (R N)
    simp only [Nat.cast_add, Nat.cast_one] at h
    rw [ha]; simp only
    rw [ENNReal.le_div_iff_mul_le (Or.inl (by simp)) (Or.inl (by simp))]
    rw [mul_comm]; exact h
  have hfin : ∀ᶠ N in atTop, a N ≠ ⊤ :=
    (tendsto_order.1 hent).2 ⊤ (by simp) |>.mono fun N h => h.ne
  have hat : Tendsto (fun N => (a N).toReal) atTop (𝓝 0) := by
    have := (ENNReal.tendsto_toReal (ENNReal.zero_ne_top)).comp hent
    simpa [Function.comp_def] using this
  have hup : Tendsto (fun N => Real.sqrt ((a N).toReal / 2)) atTop (𝓝 0) := by
    have : Tendsto (fun N => (a N).toReal / 2) atTop (𝓝 0) := by simpa using hat.div_const 2
    have h2 := (Real.continuous_sqrt.tendsto 0).comp this
    simpa [Function.comp_def] using h2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
    (Eventually.of_forall fun N => tvDist_nonneg _ _) ?_
  filter_upwards [hfin] with N hN
  haveI : IsProbabilityMeasure ((R N).map fun x => x 0) := inferInstance
  have hne : klDiv ((R N).map fun x => x 0) μ ≠ ⊤ := ne_top_of_le_ne_top hN (hk N)
  refine (tvDist_le_sqrt_klDiv _ _ hne).trans ?_
  gcongr
  exact hk N

end Exchangeable

end HRS.External.Entropy
