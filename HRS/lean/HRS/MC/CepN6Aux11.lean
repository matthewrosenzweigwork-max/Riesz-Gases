import HRS.MC.CepN6Aux10
import HRS.MC.CepN4

/-!
# Packet CEPN6 (aux 11): pathwise package for a fixed ordering `σ`
-/

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped BigOperators ENNReal NNReal

noncomputable section

namespace HRS.MC.CepN6

open HRS HRS.MC.CepN4

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {N : ℕ}

/-- The pathwise facts about a solution path `y` (with noise path `w`) for a fixed ordering `σ`. -/
structure n6_PathOK (hN : 2 ≤ N) (D : DynData 1) (σ : Equiv.Perm (Fin N)) (a T r2 : ℝ)
    (c : ℝ → ℝ) (y : ℝ → Fin N → Euc 1) (w : ℝ → Fin N → ℝ) : Prop where
  free : ∀ v ∈ Set.Icc (0 : ℝ) T, y v ∈ liftedFree 1 N
  cont : ContinuousOn y (Set.Icc 0 T)
  ord : ∀ v ∈ Set.Icc (0 : ℝ) T, cep_StrictlyOrdered σ (y v)
  coord : ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ T → ∀ k : Fin N,
    IntervalIntegrable (fun u => (liftedDrift D (y u) k) 0) volume s t ∧
    y t k 0 - y s k 0 = (∫ u in s..t, (liftedDrift D (y u) k) 0) +
      Real.sqrt (2 * D.invβ) * (w t k - w s k)
  gap : ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ T →
    (∀ u ∈ Set.Icc s t, cep_StrictlyOrdered σ (y u) ∧ cep_PairIsolated hN σ (y u) r2 ∧
      0 < y u (σ (cep_i1 hN)) 0 - y u (σ (cep_i0 hN)) 0 ∧
      y u (σ (cep_i1 hN)) 0 - y u (σ (cep_i0 hN)) 0 < 1 / 4) →
    (y t (σ (cep_i1 hN)) 0 - y t (σ (cep_i0 hN)) 0) - (y s (σ (cep_i1 hN)) 0 - y s (σ (cep_i0 hN)) 0) =
      (∫ u in s..t, ((2 * a / N) / (y u (σ (cep_i1 hN)) 0 - y u (σ (cep_i0 hN)) 0) + c u)) +
        2 * Real.sqrt D.invβ *
          (((w t (σ (cep_i1 hN)) - w t (σ (cep_i0 hN))) - (w s (σ (cep_i1 hN)) - w s (σ (cep_i0 hN)))) /
            Real.sqrt 2)

theorem n6_pathOK_ae {D : DynData 1} (hN : 2 ≤ N) {ℱ : Filtration ℝ mΩ}
    {W' : ℝ≥0 → Ω → (Fin N × Fin 1) → ℝ} {Y₀ : Ω → Fin N → Euc 1} {τ : Ω → WithTop ℝ}
    {Y : ℝ → Ω → Fin N → Euc 1} (hsol : IsMaximalParticleSolution P ℱ W' D Y₀ τ Y)
    {π : Ω → Equiv.Perm (Fin N)} (hπ0 : ∀ ω, cep_StrictlyOrdered (π ω) (Y₀ ω)) {a T r2 : ℝ}
    (hT : 0 < T) {c : ℝ → Ω → ℝ}
    (hN4 : ∀ᵐ ω ∂P, ∀ s t : ℝ, 0 ≤ s → s ≤ t →
      (∀ u ∈ Set.Icc s t, ((u : ℝ) : WithTop ℝ) < τ ω ∧ cep_StrictlyOrdered (π ω) (Y u ω) ∧
        cep_PairIsolated hN (π ω) (Y u ω) r2 ∧
        0 < Y u ω (π ω (cep_i1 hN)) 0 - Y u ω (π ω (cep_i0 hN)) 0 ∧
        Y u ω (π ω (cep_i1 hN)) 0 - Y u ω (π ω (cep_i0 hN)) 0 < 1 / 4) →
      (Y t ω (π ω (cep_i1 hN)) 0 - Y t ω (π ω (cep_i0 hN)) 0) -
          (Y s ω (π ω (cep_i1 hN)) 0 - Y s ω (π ω (cep_i0 hN)) 0) =
        (∫ u in s..t, ((2 * a / N) / (Y u ω (π ω (cep_i1 hN)) 0 - Y u ω (π ω (cep_i0 hN)) 0) +
          c u ω)) +
          2 * Real.sqrt D.invβ *
            (((W' (Real.toNNReal t) ω (π ω (cep_i1 hN), 0) - W' (Real.toNNReal t) ω (π ω (cep_i0 hN), 0)) -
              (W' (Real.toNNReal s) ω (π ω (cep_i1 hN), 0) - W' (Real.toNNReal s) ω (π ω (cep_i0 hN), 0))) /
              Real.sqrt 2))
    (htop : ∀ᵐ ω ∂P, ((T : ℝ) : WithTop ℝ) < τ ω) (σ : Equiv.Perm (Fin N)) :
    ∀ᵐ ω ∂P, π ω = σ →
      n6_PathOK hN D σ a T r2 (fun u => c u ω) (fun v => Y v ω)
        (fun v k => W' (Real.toNNReal v) ω (k, 0)) := by
  filter_upwards [n6_coord_eq hsol, hN4, htop] with ω h1 h2 h3 hπσ
  have hlt : ∀ u : ℝ, u ≤ T → ((u : ℝ) : WithTop ℝ) < τ ω := fun u hu =>
    lt_of_le_of_lt (by exact_mod_cast hu) h3
  have hfree : ∀ v ∈ Set.Icc (0 : ℝ) T, Y v ω ∈ liftedFree 1 N := fun v hv =>
    hsol.mem ω v hv.1 (hlt v hv.2)
  have hcont : ContinuousOn (fun v => Y v ω) (Set.Icc 0 T) :=
    hsol.sol.cont ω T hT.le h3
  have h0 : cep_StrictlyOrdered σ (Y 0 ω) := by
    rw [hsol.sol.init ω, ← hπσ]
    exact hπ0 ω
  refine ⟨hfree, hcont, n6_persist hT.le hcont hfree h0, ?_, ?_⟩
  · intro s t hs hst htT k
    exact h1 s t hs hst (hlt t htT) k
  · intro s t hs hst htT hcond
    have key := h2 s t hs hst (by
      intro u hu
      obtain ⟨a1, a2, a3, a4⟩ := hcond u hu
      rw [hπσ]
      exact ⟨hlt u (hu.2.trans htT), a1, a2, a3, a4⟩)
    rw [hπσ] at key
    exact key

/-- The gap equation along a path which stays in the open good set on `[t₁, t)`. -/
theorem n6_dyn_of_pathOK {D : DynData 1} (hN : 2 ≤ N) {σ : Equiv.Perm (Fin N)} {a T r2 t₁ t : ℝ}
    {c : ℝ → ℝ} {y : ℝ → Fin N → Euc 1} {w : ℝ → Fin N → ℝ}
    (hP : n6_PathOK hN D σ a T r2 c y w) (ht₁ : 0 ≤ t₁) (hlt : t₁ < t) (htT : t ≤ T)
    (hU : ∀ v ∈ Set.Ico t₁ t, y v ∈ n6_Uo (σ (cep_i0 hN)) (σ (cep_i1 hN)) r2 (1 / 8))
    {s : ℝ} (hs : t₁ ≤ s) (hst : s ≤ t) :
    (y t (σ (cep_i1 hN)) 0 - y t (σ (cep_i0 hN)) 0) - (y s (σ (cep_i1 hN)) 0 - y s (σ (cep_i0 hN)) 0) =
      (∫ u in s..t, ((2 * a / N) / (y u (σ (cep_i1 hN)) 0 - y u (σ (cep_i0 hN)) 0) + c u)) +
        2 * Real.sqrt D.invβ *
          (((w t (σ (cep_i1 hN)) - w t (σ (cep_i0 hN))) - (w s (σ (cep_i1 hN)) - w s (σ (cep_i0 hN)))) /
            Real.sqrt 2) := by
  have hcx : ContinuousOn y (Set.Icc t₁ t) := hP.cont.mono (Set.Icc_subset_Icc ht₁ htT)
  have hKc := n6_closure_path hlt hcx hU
  refine hP.gap s t (ht₁.trans hs) hst htT (n6_condN4 hN σ (fun u hu => hKc u ⟨hs.trans hu.1, hu.2⟩)
    (fun u hu => hP.ord u ⟨(ht₁.trans hs).trans hu.1, hu.2.trans htT⟩))

end HRS.MC.CepN6
