import HRS.MS.SA12X3C6C
import HRS.MS.SA12NearDefs

/-!
# S.A.12 C6 (SA12X3), part D: from lattice centres and regular densities to real centres and `C_b` densities

`sa12x3_bridge`: a lattice-centre bound `EucNlBoundPositive … Λ'' …` (any `E, A, κ, hreg`) implies the same bound
at every real centre `c` for densities `μ ∈ C_b^{m+3}` with `cbNorm ≤ Λ`, by the Galilean shift
(`Ψ'_σ x = Ψ_σ(x+c) - Ψ_σ c`, `F' = F(·+Ψ_τ c)`, `μ'' = ζ μ(·+Ψ_τ c)`).
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped BigOperators ContDiff ENNReal

namespace HRS.MH.AdjointRd.Phase2SA12Construction

open HRS HRS.Whole HRS.MH.AdjointRd HRS.MH.AdjointRd.Phase2SA12 HRS.MH.AdjointRd.Phase2SA12Near

variable {d : ℕ}

theorem sa12x3_cellPt_zero : cellPt d (0 : Fin d → ℤ) = 0 := by
  ext i
  simp [cellPt, latticePt]

theorem sa12x3_bridge (hd : 1 ≤ d) (m : ℕ) (Cb T : ℝ) (χ χh : Euc d → ℝ) (hχ : IsCutoffPair χ χh) (Λ : ℝ) :
    ∃ Λ'' : ℝ, 0 ≤ Λ'' ∧ ∀ (s : ℝ) (E : Finset (Fin d → ℤ)) (A κ : ℝ)
      (hreg : Matrix (Fin d) (Fin d) ℝ → Prop),
      EucNlBoundPositive d s m Λ'' Cb T χ χh E A κ hreg →
      ∀ (b : ℝ → Euc d → Euc d) (Ψ : ℝ → Euc d → Euc d),
      IsAdvectingDrift m Cb T b → IsNegDriftFlow T b Ψ →
      ∀ M : Matrix (Fin d) (Fin d) ℝ, hreg M →
      ∀ μ : Euc d → ℝ, MemCb (m + 3) μ → cbNorm (m + 3) μ ≤ Λ → (∀ x, 0 ≤ μ x) →
      ∀ F : Euc d → ℝ, BddJets m F → ∀ τ ∈ Icc (0 : ℝ) T, ∀ c : Euc d,
        -(2 * jetPair m (advCutoff χ Ψ τ c) F
          (eucNonlocal s M (fun y => advCutoff χh Ψ τ c y * μ y) F)) ≤
          κ * ∑ k ∈ E, cellDissip m χ Ψ τ (c + cellPt d k) F +
          A * ∑ k ∈ E, cellEnergy m χ Ψ τ (c + cellPt d k) F := by
  obtain ⟨B, R, hB, hR1, hfacts⟩ := advected_cutoff_jets d hd m Cb T χ χh hχ
  obtain ⟨ζ, Λ'', hΛ'', hζ, hζ0, hζ1, hreg⟩ := sa12x3_cutoff_density (d := d) m hR1 Λ
  refine ⟨Λ'', hΛ'', fun s E A κ hreg' hLat b Ψ hb hΨ M hM μ hμ hcb hμ0 F hF τ hτ c => ?_⟩
  set q : Euc d := Ψ τ c with hq
  have hb' := sa12x3_drift_adv hb hΨ c
  have hΨ' := sa12x3_flow hΨ c
  have hF' : BddJets m (fun y => F (y + q)) := by
    refine ⟨hF.1.comp (contDiff_id.add contDiff_const), fun j hj idx => ?_⟩
    obtain ⟨B1, hB1⟩ := hF.2 j hj idx
    exact ⟨B1, fun x => by rw [sa12x3_pd_shift]; exact hB1 _⟩
  have hμ0' : ∀ y, 0 ≤ ζ y * μ (y + q) := fun y => mul_nonneg (hζ0 y) (hμ0 _)
  have hcf := hfacts (sa12x3_drift b Ψ c) (sa12x3_Psi Ψ c) hb' hΨ' τ hτ (cellPt d 0)
  have hΨ0 : sa12x3_Psi Ψ c τ (cellPt d 0) = 0 := by
    simp [sa12x3_Psi, sa12x3_cellPt_zero]
  have hw : advCutoff χ (sa12x3_Psi Ψ c) τ (cellPt d 0) = fun y => advCutoff χ Ψ τ c (y + q) := by
    funext y
    rw [sa12x3_adv_shift hΨ hτ, sa12x3_cellPt_zero, add_zero]
  have ha : (fun y => advCutoff χh (sa12x3_Psi Ψ c) τ (cellPt d 0) y * (ζ y * μ (y + q))) =
      fun y => advCutoff χh Ψ τ c (y + q) * μ (y + q) := by
    funext y
    have hy : advCutoff χh (sa12x3_Psi Ψ c) τ (cellPt d 0) y = advCutoff χh Ψ τ c (y + q) := by
      rw [sa12x3_adv_shift hΨ hτ, sa12x3_cellPt_zero, add_zero]
    rw [hy]
    by_cases h0 : advCutoff χh Ψ τ c (y + q) = 0
    · simp [h0]
    · have hne : advCutoff χh (sa12x3_Psi Ψ c) τ (cellPt d 0) y ≠ 0 := by rw [hy]; exact h0
      have hs := hcf.2.2 (Function.mem_support.2 hne)
      rw [hΨ0] at hs
      rw [hζ1 y hs]
      ring
  have e1 : jetPair m (advCutoff χ (sa12x3_Psi Ψ c) τ (cellPt d 0)) (fun y => F (y + q))
      (eucNonlocal s M (fun y => advCutoff χh (sa12x3_Psi Ψ c) τ (cellPt d 0) y * (ζ y * μ (y + q)))
        (fun y => F (y + q))) =
      jetPair m (advCutoff χ Ψ τ c) F (eucNonlocal s M (fun y => advCutoff χh Ψ τ c y * μ y) F) := by
    rw [hw, ha]
    have hN : eucNonlocal s M (fun y => advCutoff χh Ψ τ c (y + q) * μ (y + q)) (fun y => F (y + q)) =
        fun y => eucNonlocal s M (fun y => advCutoff χh Ψ τ c y * μ y) F (y + q) :=
      funext fun y => sa12x3_eucNL_shift s M (fun y => advCutoff χh Ψ τ c y * μ y) F q y
    rw [hN]
    exact sa12x3_jetPair_shift m (advCutoff χ Ψ τ c) F _ q
  have e2 : ∀ k, cellDissip m χ (sa12x3_Psi Ψ c) τ (cellPt d (0 + k)) (fun y => F (y + q)) =
      cellDissip m χ Ψ τ (c + cellPt d k) F := by
    intro k
    unfold cellDissip
    have : advCutoff χ (sa12x3_Psi Ψ c) τ (cellPt d (0 + k)) =
        fun y => advCutoff χ Ψ τ (c + cellPt d k) (y + q) := by
      funext y
      rw [sa12x3_adv_shift hΨ hτ, zero_add]
    rw [this]
    exact sa12x3_dissipSq_shift m _ F q
  have e3 : ∀ k, cellEnergy m χ (sa12x3_Psi Ψ c) τ (cellPt d (0 + k)) (fun y => F (y + q)) =
      cellEnergy m χ Ψ τ (c + cellPt d k) F := by
    intro k
    unfold cellEnergy
    have : advCutoff χ (sa12x3_Psi Ψ c) τ (cellPt d (0 + k)) =
        fun y => advCutoff χ Ψ τ (c + cellPt d k) (y + q) := by
      funext y
      rw [sa12x3_adv_shift hΨ hτ, zero_add]
    rw [this]
    exact sa12x3_jetSq_shift m _ F q
  have hlat : -(2 * jetPair m (advCutoff χ (sa12x3_Psi Ψ c) τ (cellPt d 0)) (fun y => F (y + q))
      (eucNonlocal s M (fun y => advCutoff χh (sa12x3_Psi Ψ c) τ (cellPt d 0) y * (ζ y * μ (y + q)))
        (fun y => F (y + q)))) ≤
      κ * ∑ k ∈ E, cellDissip m χ (sa12x3_Psi Ψ c) τ (cellPt d (0 + k)) (fun y => F (y + q)) +
        A * ∑ k ∈ E, cellEnergy m χ (sa12x3_Psi Ψ c) τ (cellPt d (0 + k)) (fun y => F (y + q)) :=
    hLat (sa12x3_drift b Ψ c) (sa12x3_Psi Ψ c) hb' hΨ' M hM (fun y => ζ y * μ (y + q))
      (hreg μ q hμ hcb) hμ0' (fun y => F (y + q)) hF' τ hτ 0
  rw [e1] at hlat
  simp only [e2, e3] at hlat
  exact hlat

end HRS.MH.AdjointRd.Phase2SA12Construction
