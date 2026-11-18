import HRS.Energy.Commutator.RenormInt

/-!
# Route S, packet S4: the slice master identity `P_l = Q_l + R_l` for charges reproducing the slice force
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators
open HRS.Commutator.RoughLimit

namespace HRS.Commutator.Renorm

variable {d : ℕ}

theorem exists_bound_of_cont {v : Torus d → Euc d} (hv : Continuous v) : ∃ C : ℝ, ∀ x, ‖v x‖ ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hv.continuousOn
  exact ⟨C, fun x => hC x (mem_univ x)⟩

theorem sgv_odd (l : ℝ) (z : Torus d) : SliceAux.sgv l (-z) = -SliceAux.sgv l z := sgv_neg l z

/-- Notation for the three remainder pieces. -/
def selfB (l : ℝ) (v : Torus d → Euc d) (σ : Measure (Torus d)) : ℝ :=
  ∫ p : Torus d × Torus d, kern (SliceAux.sgv l) v p.1 p.2 ∂(σ.prod σ)

def muB (l : ℝ) (v : Torus d → Euc d) (σ μ : Measure (Torus d)) (a : Torus d) : ℝ :=
  ∫ y, inner ℝ (v a - v y) (SliceAux.sgv l (a - y) - ∫ x, SliceAux.sgv l (x - y) ∂σ) ∂μ

def fieldF {N : ℕ} (l : ℝ) (X : Fin N → Torus d) (μ : Measure (Torus d)) (i : Fin N) (x : Torus d) : Euc d :=
  (1 / (N : ℝ)) • ∑ j ∈ Finset.univ.erase i, SliceAux.sgv l (x - X j) - ∫ y, SliceAux.sgv l (x - y) ∂μ

def fieldT {N : ℕ} (l : ℝ) (v : Torus d → Euc d) (X : Fin N → Torus d) (σ : Measure (Torus d))
    (μ : Measure (Torus d)) (i : Fin N) : ℝ :=
  ∫ x, inner ℝ (v (X i) - v x) (fieldF l X μ i x) ∂σ

theorem slice_decomp {N : ℕ} (hd : 1 ≤ d) (hN : N ≠ 0) {l : ℝ} (hl : 0 ≤ l) {X : Fin N → Torus d}
    {η : Fin N → ℝ} {σ : Fin N → Measure (Torus d)} (hS : SliceCharges l X η σ)
    {μ : Measure (Torus d)} [IsFiniteMeasure μ] {c : ℝ≥0∞} (hc : c ≠ ⊤)
    (hμ : μ ≤ c • (volume : Measure (Torus d))) {L : ℝ} (hL : 0 ≤ L) {v : Torus d → Euc d}
    (hv : IsLipschitzVF L v) :
    offDiagPairing (commKernel (SliceAux.sgv l) v) X μ =
      quadForm (commKernel (SliceAux.sgv l) v) (avgM σ) μ
        - (1 / (N : ℝ)) ^ 2 * ∑ i, selfB l v (σ i)
        - (2 / (N : ℝ)) * ∑ i, muB l v (σ i) μ (X i)
        + (2 / (N : ℝ)) * ∑ i, fieldT l v X (σ i) μ i := by
  haveI : ∀ i, IsFiniteMeasure (σ i) := hS.fin
  have hvc : Continuous v := lipschitzVF_continuous hL hv
  obtain ⟨Cv, hCv⟩ := exists_bound_of_cont hvc
  have hη0 : ∀ i, 0 ≤ η i := fun i => (hS.η0 i).le
  have hGμ : ∀ i, Integrable (fun p : Torus d × Torus d => sliceGfull d l (p.1 - p.2)) ((σ i).prod μ) :=
    fun i => integrable_G_mu hl (σ i) hc hμ
  have hii := fun i => integrable_kern_of_G hd hl hL hv (hS.Gii i)
  have hiμ := fun i => integrable_kern_of_G hd hl hL hv (hGμ i)
  have hμμ := integrable_kern_of_G hd hl hL hv (integrable_G_mu hl μ hc hμ)
  exact comm_decomp hN (w := SliceAux.sgv l) (measurable_sgv_l l) (sgv_odd l) (sgv_integrable hl)
    (fun δ hδ => sgv_bdd_away hl hδ) hvc.measurable hCv hη0 hS.supp hS.rep hS.sep hc hμ hii hiμ hμμ


/-- Atomlessness of a measure with bounded density. -/
theorem atomless_of_le_vol (hd : 1 ≤ d) {μ : Measure (Torus d)} {c : ℝ≥0∞} (hc : c ≠ ⊤)
    (hμ : μ ≤ c • (volume : Measure (Torus d))) (x : Torus d) : μ {x} = 0 := by
  have h1 : μ {x} ≤ (c • (volume : Measure (Torus d))) {x} := hμ _
  rw [Measure.smul_apply, volume_singleton_torus hd x, smul_zero] at h1
  exact le_antisymm h1 bot_le

theorem withDensityReal_le_smul' {ρ : Torus d → ℝ} {Λ₀ : ℝ} (hρΛ : ∀ x, ρ x ≤ Λ₀) :
    withDensityReal ρ ≤ ENNReal.ofReal Λ₀ • (volume : Measure (Torus d)) := by
  unfold withDensityReal
  rw [← withDensity_const]
  exact withDensity_mono (Filter.Eventually.of_forall fun x => ENNReal.ofReal_le_ofReal (hρΛ x))


theorem avgM_apply {N : ℕ} (σ : Fin N → Measure (Torus d)) (A : Set (Torus d)) :
    avgM σ A = (N : ℝ≥0∞)⁻¹ * ∑ i, σ i A := by
  unfold avgM
  simp only [Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply, smul_eq_mul]

theorem avgM_univ_one {N : ℕ} (hN : N ≠ 0) (σ : Fin N → Measure (Torus d)) (h : ∀ i, σ i Set.univ = 1) :
    avgM σ Set.univ = 1 := by
  rw [avgM_apply]
  simp only [h, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast hN) (ENNReal.natCast_ne_top N)

theorem avgM_atomless {N : ℕ} (σ : Fin N → Measure (Torus d)) (h : ∀ i x, σ i {x} = 0) (x : Torus d) :
    avgM σ {x} = 0 := by
  rw [avgM_apply]
  simp [h]

/-- **Term 1**: the stress inequality for the smeared charge. -/
theorem Q_bound (d : ℕ) (hd : 1 ≤ d) : ∃ C : ℝ, 0 < C ∧ ∀ {N : ℕ} (hN : N ≠ 0) {l : ℝ} (hl : 0 ≤ l)
    {X : Fin N → Torus d} {η : Fin N → ℝ} {σ : Fin N → Measure (Torus d)} (hS : SliceCharges l X η σ)
    {μ : Measure (Torus d)} [IsFiniteMeasure μ] {c : ℝ≥0∞} (hc : c ≠ ⊤)
    (hμ : μ ≤ c • (volume : Measure (Torus d))) (hμ1 : μ Set.univ = 1) {L : ℝ} (hL : 0 ≤ L)
    {v : Torus d → Euc d} (hv : IsLipschitzVF L v),
    |quadForm (commKernel (SliceAux.sgv l) v) (avgM σ) μ| ≤
      C * L * quadForm (fun x y => sliceGfull d l (x - y)) (avgM σ) μ := by
  obtain ⟨C, hC, hstress⟩ := stress_rough d
  refine ⟨C, hC, fun {N} hN {l} hl {X} {η} {σ} hS {μ} _ {c} hc hμ hμ1 {L} hL {v} hv => ?_⟩
  haveI : ∀ i, IsFiniteMeasure (σ i) := hS.fin
  haveI := isFiniteMeasure_avgM hN σ
  have h := hstress l hl L v hL hv (avgM σ) μ inferInstance inferInstance
    (fun h0 => by rw [avgM_univ_one hN σ (hS.neutral h0), hμ1])
    (fun h2 => ⟨avgM_atomless σ (hS.atom h2), atomless_of_le_vol (by omega) hc hμ⟩)
    (G_int_sum hN hl hS hc hμ)
  rw [commKernel_sliceGrad hl v] at h
  exact h

end HRS.Commutator.Renorm
