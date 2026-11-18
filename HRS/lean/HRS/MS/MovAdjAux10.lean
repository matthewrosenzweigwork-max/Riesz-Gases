import HRS.MS.MovAdjAux9

/-!
# S6.7 (packet P2, part 5): the elements `ψ_r = √ρ Π f_r ∈ L²_0` and the identity `ψ_r = T(t-r)† ψ_t`

Namespace `HRS.MS.MovAdj`, helpers `s67_`.  Infrastructure for the supplement row `S:W:lem:r2mov-global-adjoint`; not a manuscript row.

* `s67psi ρ u = √ρ (u - ∫ u ρ)`;  `s67_psi_memLp`, `s67_psi_orth`: for `u` bounded measurable, `s67psi ρ u ∈ L²` and `⟨√ρ, ψ⟩ = 0`;
* `s67mk`: the element of `L²_0` represented by `s67psi ρ u`;
* `s67_psi_eq`: `s67mk (f r) = T(t-r)† s67mk φ` (density of the Schwartz core and `s67_bridge`).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MovAdj

open HRS HRS.Whole HRS.MH.DualityRd HRS.MS.MovLin HRS.MS.Mov63

variable {d : ℕ} {s β q : ℝ} {ρ : Euc d → ℝ}

local notation "𝓢R" => SchwartzMap (Euc d) ℝ

/-- `ψ[u] = √ρ (u - ∫ u ρ)` (the projection `Π` followed by the weight). -/
def s67psi (ρ : Euc d → ℝ) (u : Euc d → ℝ) (x : Euc d) : ℝ :=
  Real.sqrt (ρ x) * (u x - ∫ y, u y * ρ y)

theorem s67_psi_memLp (hgL : MemLp (fun x => Real.sqrt (ρ x)) 2 (volume : Measure (Euc d)))
    {u : Euc d → ℝ} (hu : AEStronglyMeasurable u (volume : Measure (Euc d))) {B : ℝ}
    (hb : ∀ x, |u x| ≤ B) : MemLp (s67psi ρ u) 2 (volume : Measure (Euc d)) := by
  set c : ℝ := ∫ y, u y * ρ y with hc
  have hm : AEStronglyMeasurable (fun x => u x - c) (volume : Measure (Euc d)) :=
    hu.sub aestronglyMeasurable_const
  have := s67_memLp_mul_bdd hgL hm (B := B + |c|)
    (fun x => by
      calc |u x - c| ≤ |u x| + |c| := abs_sub _ _
        _ ≤ B + |c| := add_le_add (hb x) le_rfl)
  refine this.ae_eq (Filter.Eventually.of_forall fun x => ?_)
  unfold s67psi
  rw [← hc]
  ring

theorem s67_psi_orth (H : Mov2dTh d s β q ρ) {u : Euc d → ℝ} (hu : AEStronglyMeasurable u (volume : Measure (Euc d)))
    {B : ℝ} (hb : ∀ x, |u x| ≤ B) : ∫ x, Real.sqrt (ρ x) * s67psi ρ u x = 0 := by
  obtain ⟨Bg, -, hR, -⟩ := HRS.MS.Mov0.mv0_gapref H.hd H.hs0 H.hsd H.hq H.hβ H.hρ
  set c : ℝ := ∫ y, u y * ρ y with hc
  have hρnn : ∀ x, 0 ≤ ρ x := fun x => (hR.pos x).le
  have e : ∀ x, Real.sqrt (ρ x) * s67psi ρ u x = ρ x * u x - c * ρ x := by
    intro x
    unfold s67psi
    rw [← hc, ← mul_assoc, Real.mul_self_sqrt (hρnn x)]
    ring
  have hI1 : Integrable (fun x => ρ x * u x) := by
    refine hR.integrable.mul_bdd (c := B) hu (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs]; exact hb x
  have hI2 : Integrable (fun x => c * ρ x) := hR.integrable.const_mul c
  simp_rw [e]
  rw [integral_sub hI1 hI2, integral_const_mul, hR.integral_one, hc]
  have : ∫ x, ρ x * u x = ∫ y, u y * ρ y :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _)
  rw [this]
  ring

/-- `√ρ ⊥ v` for `v ∈ L²_0` in function form. -/
theorem s67_orth_of_mem (H : Mov2dTh d s β q ρ) (ψ0 : 𝓢R) (hψ0 : (⇑ψ0 : Euc d → ℝ) = fun x => Real.sqrt (ρ x))
    (v : MovL2Zero ρ) : ∫ x, Real.sqrt (ρ x) * movFun v x = 0 := by
  have h := (mov2d_mem_zero_iff (ρ := ρ)).1 v.2
  rw [mov2d_sqrtLp H ψ0 hψ0] at h
  have hgL : MemLp (fun x => Real.sqrt (ρ x)) 2 (volume : Measure (Euc d)) := by
    rw [← hψ0]; exact ψ0.memLp 2
  have hm : movSqrtLp ρ = hgL.toLp (fun x => Real.sqrt (ρ x)) := by
    unfold movSqrtLp; rw [dif_pos hgL]
  rw [← mov2d_sqrtLp H ψ0 hψ0, hm] at h
  rw [s67_inner_toLp_left] at h
  exact h

/-- The element of `L²_0` represented by `s67psi ρ u`. -/
def s67mk (H : Mov2dTh d s β q ρ) (ψ0 : 𝓢R) (hψ0 : (⇑ψ0 : Euc d → ℝ) = fun x => Real.sqrt (ρ x))
    {u : Euc d → ℝ} (hu : AEStronglyMeasurable u (volume : Measure (Euc d))) {B : ℝ} (hb : ∀ x, |u x| ≤ B) :
    MovL2Zero ρ :=
  ⟨(s67_psi_memLp (by rw [← hψ0]; exact ψ0.memLp 2) hu hb).toLp (s67psi ρ u), by
    have hgL : MemLp (fun x => Real.sqrt (ρ x)) 2 (volume : Measure (Euc d)) := by
      rw [← hψ0]; exact ψ0.memLp 2
    rw [mov2d_mem_zero_iff, mov2d_sqrtLp H ψ0 hψ0]
    have hm : movSqrtLp ρ = hgL.toLp (fun x => Real.sqrt (ρ x)) := by
      unfold movSqrtLp; rw [dif_pos hgL]
    rw [← mov2d_sqrtLp H ψ0 hψ0, hm, s67_inner_toLp]
    exact s67_psi_orth H hu hb⟩

theorem s67mk_ae (H : Mov2dTh d s β q ρ) (ψ0 : 𝓢R) (hψ0 : (⇑ψ0 : Euc d → ℝ) = fun x => Real.sqrt (ρ x))
    {u : Euc d → ℝ} (hu : AEStronglyMeasurable u (volume : Measure (Euc d))) {B : ℝ} (hb : ∀ x, |u x| ≤ B) :
    ∀ᵐ x ∂(volume : Measure (Euc d)), movFun (s67mk H ψ0 hψ0 hu hb) x = s67psi ρ u x := by
  have hgL : MemLp (fun x => Real.sqrt (ρ x)) 2 (volume : Measure (Euc d)) := by
    rw [← hψ0]; exact ψ0.memLp 2
  exact (s67_psi_memLp hgL hu hb).coeFn_toLp

/-- Variant with the bound given as an existential. -/
def s67mk' (H : Mov2dTh d s β q ρ) (ψ0 : 𝓢R) (hψ0 : (⇑ψ0 : Euc d → ℝ) = fun x => Real.sqrt (ρ x))
    {u : Euc d → ℝ} (hu : AEStronglyMeasurable u (volume : Measure (Euc d))) (hbdd : ∃ B : ℝ, ∀ x, |u x| ≤ B) :
    MovL2Zero ρ :=
  s67mk H ψ0 hψ0 hu hbdd.choose_spec

theorem s67mk'_ae (H : Mov2dTh d s β q ρ) (ψ0 : 𝓢R) (hψ0 : (⇑ψ0 : Euc d → ℝ) = fun x => Real.sqrt (ρ x))
    {u : Euc d → ℝ} (hu : AEStronglyMeasurable u (volume : Measure (Euc d))) (hbdd : ∃ B : ℝ, ∀ x, |u x| ≤ B) :
    ∀ᵐ x ∂(volume : Measure (Euc d)), movFun (s67mk' H ψ0 hψ0 hu hbdd) x = s67psi ρ u x :=
  s67mk_ae H ψ0 hψ0 hu hbdd.choose_spec

end HRS.MS.MovAdj
