import HRS.Energy.Commutator.RenormLE

/-!
# Route S, packet S4: integrability of the energy kernels against charges

`G = sliceGfull d l`, `𝒢 = sliceG d l` are `L¹`; their pairings with finite measures and measures of bounded
density are integrable; the majorant of the commutator kernel turns this into integrability of `kern`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators
open HRS.Commutator.RoughLimit

namespace HRS.Commutator.Renorm

variable {d : ℕ}

theorem integrable_conv_vol {G : Torus d → ℝ} (hGm : Measurable G) (hG : Integrable G volume)
    (σ : Measure (Torus d)) [IsFiniteMeasure σ] :
    Integrable (fun p : Torus d × Torus d => G (p.1 - p.2)) (σ.prod volume) := by
  have hm : Measurable fun p : Torus d × Torus d => G (p.1 - p.2) := hGm.comp (measurable_fst.sub measurable_snd)
  rw [integrable_prod_iff hm.aestronglyMeasurable]
  refine ⟨Filter.Eventually.of_forall fun x => hG.comp_sub_left x, ?_⟩
  have : (fun x : Torus d => ∫ y, ‖G (x - y)‖ ∂(volume : Measure (Torus d))) = fun _ => ∫ y, ‖G y‖ := by
    funext x
    exact integral_sub_left_eq_self (fun y => ‖G y‖) volume x
  show Integrable (fun x : Torus d => ∫ y, ‖G (x - y)‖ ∂(volume : Measure (Torus d))) σ
  rw [this]
  exact integrable_const _

theorem integrable_conv_mu {G : Torus d → ℝ} (hGm : Measurable G) (hG : Integrable G volume)
    (σ : Measure (Torus d)) [IsFiniteMeasure σ] {μ : Measure (Torus d)} [IsFiniteMeasure μ] {c : ℝ≥0∞}
    (hc : c ≠ ⊤) (hμ : μ ≤ c • (volume : Measure (Torus d))) :
    Integrable (fun p : Torus d × Torus d => G (p.1 - p.2)) (σ.prod μ) := by
  have h := (integrable_conv_vol hGm hG σ).smul_measure hc
  have e : σ.prod (c • (volume : Measure (Torus d))) = c • σ.prod volume := Measure.prod_smul_right c
  rw [← e] at h
  exact h.mono_measure (Measure.prod_mono le_rfl hμ)

/-- swapping the two factors of a product for an even kernel -/
theorem integrable_swap_even {G : Torus d → ℝ} (hGe : ∀ z, G (-z) = G z) {α β : Measure (Torus d)}
    [SFinite α] [SFinite β] (h : Integrable (fun p : Torus d × Torus d => G (p.1 - p.2)) (α.prod β)) :
    Integrable (fun p : Torus d × Torus d => G (p.1 - p.2)) (β.prod α) := by
  have := h.swap
  refine this.congr (Filter.Eventually.of_forall fun p => ?_)
  simp only [Function.comp, Prod.fst_swap, Prod.snd_swap]
  rw [show p.2 - p.1 = -(p.1 - p.2) by abel, hGe]


theorem sliceGfull_even (l : ℝ) (z : Torus d) : sliceGfull d l (-z) = sliceGfull d l z := by
  unfold sliceGfull; rw [EnergyAux.sliceG_neg]

theorem integrable_sliceGfull_vol {l : ℝ} (hl : 0 ≤ l) : Integrable (sliceGfull d l : Torus d → ℝ) volume :=
  RoughKernel.integrable_sliceGfull hl

/-- The energy kernel pairs integrably with bounded densities. -/
theorem integrable_G_mu {l : ℝ} (hl : 0 ≤ l) (σ : Measure (Torus d)) [IsFiniteMeasure σ]
    {μ : Measure (Torus d)} [IsFiniteMeasure μ] {c : ℝ≥0∞} (hc : c ≠ ⊤)
    (hμ : μ ≤ c • (volume : Measure (Torus d))) :
    Integrable (fun p : Torus d × Torus d => sliceGfull d l (p.1 - p.2)) (σ.prod μ) :=
  integrable_conv_mu (EnergyAux.measurable_sliceGfull l) (integrable_sliceGfull_vol hl) σ hc hμ

theorem integrable_G_mu_swap {l : ℝ} (hl : 0 ≤ l) (σ : Measure (Torus d)) [IsFiniteMeasure σ]
    {μ : Measure (Torus d)} [IsFiniteMeasure μ] {c : ℝ≥0∞} (hc : c ≠ ⊤)
    (hμ : μ ≤ c • (volume : Measure (Torus d))) :
    Integrable (fun p : Torus d × Torus d => sliceGfull d l (p.1 - p.2)) (μ.prod σ) :=
  integrable_swap_even (sliceGfull_even l) (integrable_G_mu hl σ hc hμ)

/-- `𝒢` is integrable wherever `G` is. -/
theorem integrable_sliceG_of_full {l : ℝ} {α β : Measure (Torus d)} [IsFiniteMeasure α] [IsFiniteMeasure β]
    (h : Integrable (fun p : Torus d × Torus d => sliceGfull d l (p.1 - p.2)) (α.prod β)) :
    Integrable (fun p : Torus d × Torus d => sliceG d l (p.1 - p.2)) (α.prod β) := by
  have := h.sub (integrable_const (1 / l))
  refine this.congr (Filter.Eventually.of_forall fun p => ?_)
  simp [sliceGfull]

/-- Integrability of the commutator kernel from integrability of `G`. -/
theorem integrable_kern_of_G (hd : 1 ≤ d) {l : ℝ} (hl : 0 ≤ l) {L : ℝ} (hL : 0 ≤ L) {v : Torus d → Euc d}
    (hv : IsLipschitzVF L v) {α β : Measure (Torus d)} [IsFiniteMeasure α] [IsFiniteMeasure β]
    (h : Integrable (fun p : Torus d × Torus d => sliceGfull d l (p.1 - p.2)) (α.prod β)) :
    Integrable (fun p : Torus d × Torus d => kern (SliceAux.sgv l) v p.1 p.2) (α.prod β) := by
  obtain ⟨A, B, hA, hB, hmaj⟩ := kk_majorant hd hl (d := d)
  have hvc : Continuous v := lipschitzVF_continuous hL hv
  have h1 : Integrable (fun p : Torus d × Torus d => L * (A * sliceG d l (p.1 - p.2) + B)) (α.prod β) :=
    (((integrable_sliceG_of_full h).const_mul A).add (integrable_const B)).const_mul L
  have hkm : Measurable fun p : Torus d × Torus d => kern (SliceAux.sgv l) v p.1 p.2 :=
    measurable_kern (measurable_sgv_l l) hvc.measurable
  refine Integrable.mono' h1 hkm.aestronglyMeasurable (Filter.Eventually.of_forall fun p => ?_)
  rw [Real.norm_eq_abs]
  have := hmaj L v hL hv p.1 p.2
  rwa [kk, commKernel_eq_kern] at this


/-- Hypotheses on a family of charges `σ_i` carried by `B̄(X_i, η_i)` that reproduce the slice force. -/
structure SliceCharges {N : ℕ} (l : ℝ) (X : Fin N → Torus d) (η : Fin N → ℝ)
    (σ : Fin N → Measure (Torus d)) : Prop where
  η0 : ∀ i, 0 < η i
  fin : ∀ i, IsFiniteMeasure (σ i)
  supp : ∀ i, ∀ᵐ x ∂σ i, KernelGrad.tdist x (X i) ≤ η i
  rep : ∀ i y, η i < KernelGrad.tdist y (X i) → ∫ x, SliceAux.sgv l (y - x) ∂σ i = SliceAux.sgv l (y - X i)
  sep : ∀ i j, i ≠ j → η i + η j < KernelGrad.tdist (X i) (X j)
  atom : 2 ≤ d → ∀ i x, σ i {x} = 0
  mass_le : ∀ i, (σ i).real Set.univ ≤ 1
  neutral : l = 0 → ∀ i, σ i Set.univ = 1
  Gii : ∀ i, Integrable (fun p : Torus d × Torus d => sliceGfull d l (p.1 - p.2)) ((σ i).prod (σ i))

theorem integrable_G_pair {N : ℕ} {l : ℝ} (hl : 0 ≤ l) {X : Fin N → Torus d} {η : Fin N → ℝ}
    {σ : Fin N → Measure (Torus d)} (hS : SliceCharges l X η σ) {i j : Fin N} (hij : i ≠ j) :
    Integrable (fun p : Torus d × Torus d => sliceGfull d l (p.1 - p.2)) ((σ i).prod (σ j)) := by
  haveI : ∀ i, IsFiniteMeasure (σ i) := hS.fin
  have hδ : 0 < KernelGrad.tdist (X i) (X j) - η i - η j := by
    linarith [hS.sep i j hij]
  obtain ⟨B, hB⟩ := sliceGfull_bdd_away hl hδ
  refine Integrable.mono' (integrable_const B)
    ((EnergyAux.measurable_sliceGfull l).comp (measurable_fst.sub measurable_snd)).aestronglyMeasurable ?_
  filter_upwards [ae_far hS.supp hS.sep hij] with p hp
  rw [Real.norm_eq_abs]
  exact hB _ hp

theorem integrable_G_all {N : ℕ} {l : ℝ} (hl : 0 ≤ l) {X : Fin N → Torus d} {η : Fin N → ℝ}
    {σ : Fin N → Measure (Torus d)} (hS : SliceCharges l X η σ) (i j : Fin N) :
    Integrable (fun p : Torus d × Torus d => sliceGfull d l (p.1 - p.2)) ((σ i).prod (σ j)) := by
  by_cases h : i = j
  · subst h; exact hS.Gii i
  · exact integrable_G_pair hl hS h


theorem isFiniteMeasure_avgM {N : ℕ} (hN : N ≠ 0) (σ : Fin N → Measure (Torus d)) [∀ i, IsFiniteMeasure (σ i)] :
    IsFiniteMeasure (avgM σ) := by
  unfold avgM
  refine ⟨?_⟩
  simp only [Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply, smul_eq_mul]
  exact ENNReal.mul_lt_top (ENNReal.inv_lt_top.mpr (by simpa using Nat.pos_of_ne_zero hN))
    (ENNReal.sum_lt_top.mpr fun i _ => measure_lt_top _ _)

theorem G_int_sum {N : ℕ} (hN : N ≠ 0) {l : ℝ} (hl : 0 ≤ l) {X : Fin N → Torus d} {η : Fin N → ℝ}
    {σ : Fin N → Measure (Torus d)} (hS : SliceCharges l X η σ) {μ : Measure (Torus d)} [IsFiniteMeasure μ]
    {c : ℝ≥0∞} (hc : c ≠ ⊤) (hμ : μ ≤ c • (volume : Measure (Torus d))) :
    Integrable (fun p : Torus d × Torus d => sliceGfull d l (p.1 - p.2))
      ((avgM σ + μ).prod (avgM σ + μ)) := by
  haveI : ∀ i, IsFiniteMeasure (σ i) := hS.fin
  haveI := isFiniteMeasure_avgM hN σ
  have hνν : Integrable (fun p : Torus d × Torus d => sliceGfull d l (p.1 - p.2)) ((avgM σ).prod (avgM σ)) :=
    integrable_avg_left hN _ σ fun i => integrable_avg_right hN _ σ fun j => integrable_G_all hl hS i j
  have hνμ : Integrable (fun p : Torus d × Torus d => sliceGfull d l (p.1 - p.2)) ((avgM σ).prod μ) :=
    integrable_avg_left hN _ σ fun i => integrable_G_mu hl (σ i) hc hμ
  have hμν : Integrable (fun p : Torus d × Torus d => sliceGfull d l (p.1 - p.2)) (μ.prod (avgM σ)) :=
    integrable_avg_right hN _ σ fun i => integrable_G_mu_swap hl (σ i) hc hμ
  have hμμ := integrable_G_mu hl μ hc hμ
  rw [Measure.add_prod, Measure.prod_add, Measure.prod_add]
  refine (integrable_add_measure.mpr ⟨(integrable_add_measure.mpr ⟨hνν, hνμ⟩), (integrable_add_measure.mpr ⟨hμν, hμμ⟩)⟩)

end HRS.Commutator.Renorm
