import HRS.MS.S82P2Mom

/-!
# S8.2 observed-time layer, packet T8A.C03: measurable maximal coupling of two density kernels

`K e = (μ.withDensity (min f g))` on the diagonal `+ (μ.withDensity (f - min f g)) ⊗ (μ.withDensity ((g - min f g) c⁻¹))`
with `c = 1 - ∫ min f g`.  Both marginals are the prescribed ones (separately for `c = 0`, where the residuals vanish a.e.),
and the product part lives off the diagonal because `f - min f g` and `g - min f g` have disjoint supports.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal
namespace HRS.MS.R26T8A
open HRS HRS.Whole

theorem r26t8a_c03_fiber {d : ℕ} (mu : Measure (Euc d)) [IsProbabilityMeasure mu]
    (f g : Euc d → ℝ≥0∞) (hf : Measurable f) (hg : Measurable g)
    (hf1 : ∫⁻ x, f x ∂mu = 1) (hg1 : ∫⁻ x, g x ∂mu = 1) (ci : ℝ≥0∞)
    (hci : (1 - ∫⁻ x, min (f x) (g x) ∂mu) ≠ 0 → (1 - ∫⁻ x, min (f x) (g x) ∂mu) * ci = 1) :
    let m : Euc d → ℝ≥0∞ := fun x => min (f x) (g x)
    let c : ℝ≥0∞ := 1 - ∫⁻ x, m x ∂mu
    let ν1 : Measure (Euc d) := mu.withDensity (fun x => f x - m x)
    let ν2 : Measure (Euc d) := mu.withDensity (fun x => (g x - m x) * ci)
    (∫⁻ x, m x ∂mu ≤ 1) ∧
    ((mu.withDensity m).map (fun x => (x, x)) + ν1.prod ν2) Set.univ = 1 ∧
    ((mu.withDensity m).map (fun x => (x, x)) + ν1.prod ν2).map Prod.fst = mu.withDensity f ∧
    ((mu.withDensity m).map (fun x => (x, x)) + ν1.prod ν2).map Prod.snd = mu.withDensity g ∧
    ((mu.withDensity m).map (fun x => (x, x)) + ν1.prod ν2) {p : Euc d × Euc d | p.1 ≠ p.2} = c := by
  intro m c ν1 ν2
  have hm : Measurable m := hf.min hg
  have hrf : Measurable fun x => f x - m x := hf.sub hm
  have hrg : Measurable fun x => g x - m x := hg.sub hm
  have hmf : ∀ x, m x ≤ f x := fun x => min_le_left _ _
  have hmg : ∀ x, m x ≤ g x := fun x => min_le_right _ _
  have ha1 : ∫⁻ x, m x ∂mu ≤ 1 := hf1 ▸ lintegral_mono hmf
  have haT : ∫⁻ x, m x ∂mu ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top ha1
  have hirf : ∫⁻ x, (f x - m x) ∂mu = c := by
    rw [lintegral_sub hm haT (Eventually.of_forall hmf), hf1]
  have hirg : ∫⁻ x, (g x - m x) ∂mu = c := by
    rw [lintegral_sub hm haT (Eventually.of_forall hmg), hg1]
  have hcT : c ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self
  have hν2u : ν2 Set.univ = c * ci := by
    simp only [ν2]
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      lintegral_mul_const _ hrg, hirg]
  have hν1u : ν1 Set.univ = c := by
    simp only [ν1]
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hirf]
  -- the case `c = 0`: both residual measures vanish
  have hc0 : c = 0 → ν1 = 0 ∧ mu.withDensity (fun x => g x - m x) = 0 := by
    intro h0
    refine ⟨?_, ?_⟩
    · have : (fun x => f x - m x) =ᵐ[mu] 0 :=
        (lintegral_eq_zero_iff hrf).1 (hirf.trans h0)
      simp only [ν1]
      rw [withDensity_congr_ae this]; simp
    · have : (fun x => g x - m x) =ᵐ[mu] 0 :=
        (lintegral_eq_zero_iff hrg).1 (hirg.trans h0)
      rw [withDensity_congr_ae this]; simp
  have hdiag : Measurable fun x : Euc d => (x, x) := measurable_id.prodMk measurable_id
  -- marginals of the diagonal part
  have hdfst : ((mu.withDensity m).map (fun x => (x, x))).map Prod.fst = mu.withDensity m := by
    rw [Measure.map_map measurable_fst hdiag]; exact Measure.map_id
  have hdsnd : ((mu.withDensity m).map (fun x => (x, x))).map Prod.snd = mu.withDensity m := by
    rw [Measure.map_map measurable_snd hdiag]; exact Measure.map_id
  -- marginals of the product part
  have hpfst : (ν1.prod ν2).map Prod.fst = ν1 := by
    rw [Measure.map_fst_prod, hν2u]
    by_cases h0 : c = 0
    · rw [(hc0 h0).1]; simp
    · rw [hci h0, one_smul]
  have hpsnd : (ν1.prod ν2).map Prod.snd = mu.withDensity (fun x => g x - m x) := by
    rw [Measure.map_snd_prod, hν1u]
    by_cases h0 : c = 0
    · rw [(hc0 h0).2]; simp [h0]
    · simp only [ν2]
      have hg2 : Measurable fun x => (g x - m x) * ci := hrg.mul measurable_const
      rw [← withDensity_smul _ hg2]
      congr 1
      funext x
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [mul_left_comm, hci h0, mul_one]
  have hsum1 : mu.withDensity m + ν1 = mu.withDensity f := by
    show mu.withDensity m + mu.withDensity (fun x => f x - m x) = _
    rw [← withDensity_add_left hm]
    exact withDensity_congr_ae (Eventually.of_forall fun x => add_tsub_cancel_of_le (hmf x))
  have hsum2 : mu.withDensity m + mu.withDensity (fun x => g x - m x) = mu.withDensity g := by
    rw [← withDensity_add_left hm]
    exact withDensity_congr_ae (Eventually.of_forall fun x => add_tsub_cancel_of_le (hmg x))
  have hprodu : (ν1.prod ν2) Set.univ = c * (c * ci) := by
    have h := Measure.prod_prod (μ := ν1) (ν := ν2) Set.univ Set.univ
    rw [Set.univ_prod_univ] at h
    rw [h, hν1u, hν2u]
  have hcc : c * (c * ci) = c := by
    by_cases h0 : c = 0
    · simp [h0]
    · rw [hci h0, mul_one]
  have hac : (∫⁻ x, m x ∂mu) + c = 1 := add_tsub_cancel_of_le ha1
  -- off-diagonal
  have hEqm : MeasurableSet {p : Euc d × Euc d | p.1 = p.2} :=
    measurableSet_eq_fun measurable_fst measurable_snd
  have hset : ∀ x : Euc d, Prod.mk x ⁻¹' {p : Euc d × Euc d | p.1 = p.2} = {x} := fun x => by
    ext y; simp [eq_comm]
  have hat : ∀ x, g x - m x = 0 → ν2 {x} = 0 := fun x hx => by
    simp only [ν2]
    rw [withDensity_apply _ (measurableSet_singleton x)]
    rw [setLIntegral_congr_fun (measurableSet_singleton x) (g := fun _ => (g x - m x) * ci)
      (fun y hy => by rw [show y = x from hy])]
    rw [setLIntegral_const, hx, zero_mul, zero_mul]
  have hae : ∀ᵐ x ∂ν1, ν2 {x} = 0 := by
    show ∀ᵐ x ∂(mu.withDensity (fun x => f x - m x)), ν2 {x} = 0
    rw [ae_withDensity_iff hrf]
    refine Eventually.of_forall fun x hx => hat x ?_
    rcases le_total (f x) (g x) with h | h
    · exact absurd (by rw [show m x = f x from min_eq_left h, tsub_self]) hx
    · rw [show m x = g x from min_eq_right h, tsub_self]
  have hzero : (ν1.prod ν2) {p : Euc d × Euc d | p.1 = p.2} = 0 := by
    rw [Measure.prod_apply hEqm]
    simp only [hset]
    rw [lintegral_congr_ae hae, lintegral_zero]
  have hoff : (ν1.prod ν2) {p : Euc d × Euc d | p.1 ≠ p.2} = c := by
    have h1 := measure_add_measure_compl (μ := ν1.prod ν2) hEqm
    rw [hzero, zero_add, hprodu, hcc] at h1
    exact h1
  refine ⟨ha1, ?_, ?_, ?_, ?_⟩
  · rw [Measure.add_apply, Measure.map_apply hdiag MeasurableSet.univ, Set.preimage_univ,
      withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hprodu, hcc]
    exact hac
  · rw [Measure.map_add _ _ measurable_fst, hdfst, hpfst, hsum1]
  · rw [Measure.map_add _ _ measurable_snd, hdsnd, hpsnd, hsum2]
  · have hSm : MeasurableSet {p : Euc d × Euc d | p.1 ≠ p.2} := hEqm.compl
    rw [Measure.add_apply, Measure.map_apply hdiag hSm, hoff]
    have : (fun x : Euc d => (x, x)) ⁻¹' {p : Euc d × Euc d | p.1 ≠ p.2} = ∅ := by
      ext x; simp
    rw [this]; simp

theorem r26t8a_maximal_density_coupling {E : Type*} [MeasurableSpace E]
    {d : ℕ} (mu : Measure (Euc d)) [IsProbabilityMeasure mu]
    (f g : E → Euc d → ℝ≥0∞)
    (hf : Measurable (Function.uncurry f)) (hg : Measurable (Function.uncurry g))
    (hf1 : ∀ e, ∫⁻ x, f e x ∂mu = 1) (hg1 : ∀ e, ∫⁻ x, g e x ∂mu = 1) :
    ∃ K : ProbabilityTheory.Kernel E (Euc d × Euc d),
      (∀ e, IsProbabilityMeasure (K e)) ∧
      (∀ e, (K e).map Prod.fst = mu.withDensity (f e)) ∧
      (∀ e, (K e).map Prod.snd = mu.withDensity (g e)) ∧
      (∀ e, (K e) {p : Euc d × Euc d | p.1 ≠ p.2} =
        1 - ∫⁻ x, min (f e x) (g e x) ∂mu) := by
  classical
  -- finite versions of the densities (equal almost everywhere)
  set f' : E → Euc d → ℝ≥0∞ := fun e x => if f e x = ⊤ then 0 else f e x with hf'def
  set g' : E → Euc d → ℝ≥0∞ := fun e x => if g e x = ⊤ then 0 else g e x with hg'def
  have hfe : ∀ e, Measurable (f e) := fun e => hf.comp (measurable_const.prodMk measurable_id)
  have hge : ∀ e, Measurable (g e) := fun e => hg.comp (measurable_const.prodMk measurable_id)
  have hf' : Measurable (Function.uncurry f') := by
    have : Function.uncurry f' = fun p => if f p.1 p.2 = ⊤ then 0 else f p.1 p.2 := rfl
    rw [this]
    exact Measurable.ite (measurableSet_eq_fun hf measurable_const) measurable_const hf
  have hg' : Measurable (Function.uncurry g') := by
    have : Function.uncurry g' = fun p => if g p.1 p.2 = ⊤ then 0 else g p.1 p.2 := rfl
    rw [this]
    exact Measurable.ite (measurableSet_eq_fun hg measurable_const) measurable_const hg
  have hfae : ∀ e, f' e =ᵐ[mu] f e := fun e => by
    have := ae_lt_top (hfe e) (by rw [hf1 e]; exact ENNReal.one_ne_top)
    filter_upwards [this] with x hx
    simp [hf'def, hx.ne]
  have hgae : ∀ e, g' e =ᵐ[mu] g e := fun e => by
    have := ae_lt_top (hge e) (by rw [hg1 e]; exact ENNReal.one_ne_top)
    filter_upwards [this] with x hx
    simp [hg'def, hx.ne]
  have hf'1 : ∀ e, ∫⁻ x, f' e x ∂mu = 1 := fun e => (lintegral_congr_ae (hfae e)).trans (hf1 e)
  have hg'1 : ∀ e, ∫⁻ x, g' e x ∂mu = 1 := fun e => (lintegral_congr_ae (hgae e)).trans (hg1 e)
  have hf'top : ∀ e x, f' e x ≠ ⊤ := fun e x => by
    simp only [hf'def]; split_ifs with h
    · exact ENNReal.zero_ne_top
    · exact h
  have hg'top : ∀ e x, g' e x ≠ ⊤ := fun e x => by
    simp only [hg'def]; split_ifs with h
    · exact ENNReal.zero_ne_top
    · exact h
  have hf'e : ∀ e, Measurable (f' e) := fun e => hf'.comp (measurable_const.prodMk measurable_id)
  have hg'e : ∀ e, Measurable (g' e) := fun e => hg'.comp (measurable_const.prodMk measurable_id)
  have hmae : ∀ e, (fun x => min (f' e x) (g' e x)) =ᵐ[mu] (fun x => min (f e x) (g e x)) :=
    fun e => by filter_upwards [hfae e, hgae e] with x h1 h2; simp [h1, h2]
  -- the construction
  set m : E → Euc d → ℝ≥0∞ := fun e x => min (f' e x) (g' e x) with hmdef
  have hm : Measurable (Function.uncurry m) := hf'.min hg'
  set a : E → ℝ≥0∞ := fun e => ∫⁻ x, m e x ∂mu with hadef
  have ha : Measurable a := Measurable.lintegral_prod_right' (ν := mu) (f := Function.uncurry m) hm
  set c : E → ℝ≥0∞ := fun e => 1 - a e with hcdef
  have hc : Measurable c := measurable_const.sub ha
  set ci : E → ℝ≥0∞ := fun e => if c e = 0 then 0 else (c e)⁻¹ with hcidef
  have hci : Measurable ci :=
    Measurable.ite (measurableSet_eq_fun hc measurable_const) measurable_const hc.inv
  have hcitop : ∀ e, ci e ≠ ⊤ := fun e => by
    simp only [hcidef]; split_ifs with h
    · exact ENNReal.zero_ne_top
    · exact ENNReal.inv_ne_top.2 h
  set rf : E → Euc d → ℝ≥0∞ := fun e x => f' e x - m e x with hrfdef
  set g2 : E → Euc d → ℝ≥0∞ := fun e x => (g' e x - m e x) * ci e with hg2def
  have hrf : Measurable (Function.uncurry rf) := hf'.sub hm
  have hg2 : Measurable (Function.uncurry g2) := (hg'.sub hm).mul (hci.comp measurable_fst)
  have hrftop : ∀ e x, rf e x ≠ ⊤ := fun e x => ne_top_of_le_ne_top (hf'top e x) tsub_le_self
  have hg2top : ∀ e x, g2 e x ≠ ⊤ := fun e x =>
    ENNReal.mul_ne_top (ne_top_of_le_ne_top (hg'top e x) tsub_le_self) (hcitop e)
  have hdiag : Measurable fun x : Euc d => (x, x) := measurable_id.prodMk measurable_id
  haveI : ProbabilityTheory.IsSFiniteKernel (ProbabilityTheory.Kernel.withDensity
      (ProbabilityTheory.Kernel.const E mu) rf) :=
    ProbabilityTheory.Kernel.IsSFiniteKernel.withDensity _ hrftop
  haveI : ProbabilityTheory.IsSFiniteKernel (ProbabilityTheory.Kernel.withDensity
      (ProbabilityTheory.Kernel.const E mu) g2) :=
    ProbabilityTheory.Kernel.IsSFiniteKernel.withDensity _ hg2top
  refine ⟨ProbabilityTheory.Kernel.map (ProbabilityTheory.Kernel.withDensity
      (ProbabilityTheory.Kernel.const E mu) m) (fun x : Euc d => (x, x)) +
    (ProbabilityTheory.Kernel.withDensity (ProbabilityTheory.Kernel.const E mu) rf) ×ₖ
      (ProbabilityTheory.Kernel.withDensity (ProbabilityTheory.Kernel.const E mu) g2), ?_⟩
  have key : ∀ e, (ProbabilityTheory.Kernel.map (ProbabilityTheory.Kernel.withDensity
      (ProbabilityTheory.Kernel.const E mu) m) (fun x : Euc d => (x, x)) +
    (ProbabilityTheory.Kernel.withDensity (ProbabilityTheory.Kernel.const E mu) rf) ×ₖ
      (ProbabilityTheory.Kernel.withDensity (ProbabilityTheory.Kernel.const E mu) g2)) e =
      (mu.withDensity (m e)).map (fun x => (x, x)) +
        (mu.withDensity (rf e)).prod (mu.withDensity (g2 e)) := by
    intro e
    rw [ProbabilityTheory.Kernel.add_apply, ProbabilityTheory.Kernel.prod_apply,
      ProbabilityTheory.Kernel.map_apply _ hdiag, ProbabilityTheory.Kernel.withDensity_apply _ hm,
      ProbabilityTheory.Kernel.withDensity_apply _ hrf, ProbabilityTheory.Kernel.withDensity_apply _ hg2]
    simp only [ProbabilityTheory.Kernel.const_apply]
  have hcie : ∀ e, (1 - ∫⁻ x, min (f' e x) (g' e x) ∂mu) ≠ 0 →
      (1 - ∫⁻ x, min (f' e x) (g' e x) ∂mu) * ci e = 1 := fun e h0 => by
    have h0' : c e ≠ 0 := h0
    have hcT : c e ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self
    show c e * ci e = 1
    simp only [hcidef, if_neg h0']
    exact ENNReal.mul_inv_cancel h0' hcT
  have fib := fun e => r26t8a_c03_fiber mu (f' e) (g' e) (hf'e e) (hg'e e) (hf'1 e) (hg'1 e) (ci e) (hcie e)
  have hwd : ∀ e, mu.withDensity (f' e) = mu.withDensity (f e) := fun e => withDensity_congr_ae (hfae e)
  have hwd' : ∀ e, mu.withDensity (g' e) = mu.withDensity (g e) := fun e => withDensity_congr_ae (hgae e)
  have hmi : ∀ e, ∫⁻ x, min (f' e x) (g' e x) ∂mu = ∫⁻ x, min (f e x) (g e x) ∂mu :=
    fun e => lintegral_congr_ae (hmae e)
  refine ⟨fun e => ?_, fun e => ?_, fun e => ?_, fun e => ?_⟩
  · rw [key e]
    exact ⟨(fib e).2.1⟩
  · rw [key e, ← hwd e]
    exact (fib e).2.2.1
  · rw [key e, ← hwd' e]
    exact (fib e).2.2.2.1
  · rw [key e, ← hmi e]
    exact (fib e).2.2.2.2

end HRS.MS.R26T8A
