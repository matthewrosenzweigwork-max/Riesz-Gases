import HRS.MS.SA16PRiesz9

/-!
# SA16P, part 10: weak compactness of paths in `WmpSpace` (replaces Rellich-Ehrling-Arzelà-Ascoli)

`sa16p_wmp_compact`: let `g_n : [0,t] → WmpSpace d m p` be paths bounded by `B` such that, for every component `i` and
every member `Ψ k` of a countable dense subset of `L^q`, the scalar functions `τ ↦ ∫ (g_n τ)_i Ψ_k` are
equi-Lipschitz in `n`.  Then there are a subsequence and ONE path `G : [0,t] → WmpSpace d m p` with
`‖G τ‖ ≤ card(WIndex) * B`, `ℓ (g_{φ j} τ) → ℓ (G τ)` for every `τ ∈ [0,t]` and every `ℓ ∈ StrongDual ℝ (WmpSpace d m p)`
(weak convergence at EVERY time) and `τ ↦ ℓ (G τ)` continuous on `[0,t]` (the frozen `IsWmpWeaklyContinuous`
quantifier).  The equi-Lipschitz hypothesis is exactly what the weak equation provides; no strong compactness is used.
-/

noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open MeasureTheory Filter Topology Set Function
open scoped ENNReal NNReal

namespace HRS.Whole.AppendixA.Phase2SA16P
open HRS HRS.Whole HRS.Whole.AppendixA

section Compact
variable {d m : ℕ} {p : ℝ} [Fact (2 ≤ p)]

theorem sa16p_wmp_compact {t : ℝ} (ht : 0 ≤ t) {B : ℝ}
    (Ψ : ℕ → Lp ℝ (ENNReal.ofReal (Real.conjExponent p)) (volume : Measure (Euc d)))
    (hΨ : Dense (Set.range Ψ))
    (g : ℕ → ℝ → WmpSpace d m p)
    (hB : ∀ n, ∀ τ ∈ Icc (0 : ℝ) t, ‖g n τ‖ ≤ B)
    (hL : ∀ (i : WIndex d m) (k : ℕ), ∃ L : ℝ≥0, ∀ n, LipschitzOnWith L
      (fun τ => sa16p_pair p i ((g n τ : WmpSpace d m p) : WLp d m p) (Ψ k)) (Icc (0 : ℝ) t)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ G : ℝ → WmpSpace d m p,
      (∀ τ ∈ Icc (0 : ℝ) t, ‖G τ‖ ≤ (Fintype.card (WIndex d m) : ℝ) * B) ∧
      (∀ τ ∈ Icc (0 : ℝ) t, ∀ ℓ : StrongDual ℝ (WmpSpace d m p),
        Tendsto (fun j => ℓ (g (φ j) τ)) atTop (𝓝 (ℓ (G τ)))) ∧
      (∀ ℓ : StrongDual ℝ (WmpSpace d m p), ContinuousOn (fun τ => ℓ (G τ)) (Icc (0 : ℝ) t)) := by
  classical
  have hpq := Real.HolderConjugate.conjExponent (sa16p_one_lt (p := p))
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 0 ⟨le_rfl, ht⟩)
  set κ := WIndex d m × ℕ with hκ
  let f : κ → ℕ → ℝ → ℝ := fun kk n τ =>
    sa16p_pair p kk.1 ((g n τ : WmpSpace d m p) : WLp d m p) (Ψ kk.2)
  have hb : ∀ kk : κ, ∃ M : ℝ, ∀ n, ∀ τ ∈ Icc (0 : ℝ) t, |f kk n τ| ≤ M := by
    intro kk
    refine ⟨B * ‖Ψ kk.2‖, fun n τ hτ => ?_⟩
    have := sa16p_pair_bound hpq kk.1 ((g n τ : WmpSpace d m p) : WLp d m p) (Ψ kk.2)
    exact this.trans (mul_le_mul_of_nonneg_right (hB n τ hτ) (norm_nonneg _))
  have hL' : ∀ kk : κ, ∃ L : ℝ≥0, ∀ n, LipschitzOnWith L (f kk n) (Icc (0 : ℝ) t) :=
    fun kk => hL kk.1 kk.2
  obtain ⟨φ, hφ, A, hA, hAL⟩ := sa16p_diag t f hb hL'
  -- weak limits at every time
  have hex : ∀ τ ∈ Icc (0 : ℝ) t, ∃ G₀ : WmpSpace d m p,
      ‖G₀‖ ≤ (Fintype.card (WIndex d m) : ℝ) * B ∧
      (∀ i : WIndex d m, ∀ ψ : Lp ℝ (ENNReal.ofReal (Real.conjExponent p)) (volume : Measure (Euc d)),
        Tendsto (fun j => sa16p_pair p i ((g (φ j) τ : WmpSpace d m p) : WLp d m p) ψ) atTop
          (𝓝 (sa16p_pair p i ((G₀ : WmpSpace d m p) : WLp d m p) ψ))) ∧
      ∀ ℓ : StrongDual ℝ (WmpSpace d m p), Tendsto (fun j => ℓ (g (φ j) τ)) atTop (𝓝 (ℓ G₀)) := by
    intro τ hτ
    refine sa16p_wmp_limit (Set.range Ψ) hΨ (B := B) (fun j => g (φ j) τ)
      (fun j => hB _ τ hτ) ?_
    rintro i ψ ⟨k, rfl⟩
    exact ⟨A (i, k) τ, hA (i, k) τ hτ⟩
  choose! G hGn hGp hGw using hex
  refine ⟨φ, hφ, G, hGn, hGw, fun ℓ => ?_⟩
  -- the pairings of the limit are the limits `A`
  have hpairA : ∀ i k, ∀ τ ∈ Icc (0 : ℝ) t,
      sa16p_pair p i ((G τ : WmpSpace d m p) : WLp d m p) (Ψ k) = A (i, k) τ := fun i k τ hτ =>
    tendsto_nhds_unique (hGp τ hτ i (Ψ k)) (hA (i, k) τ hτ)
  have hAcont : ∀ i k, ContinuousOn (A (i, k)) (Icc (0 : ℝ) t) := fun i k =>
    (hAL (i, k)).choose_spec.continuousOn
  intro τ₀ hτ₀
  -- continuity at `τ₀` along sequences
  rw [ContinuousWithinAt, Filter.tendsto_iff_seq_tendsto]
  intro x hx
  rw [tendsto_nhdsWithin_iff] at hx
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hx2
  have hxS : ∀ n, x (n + N) ∈ Icc (0 : ℝ) t := fun n => hN _ (Nat.le_add_left N n)
  have hx1' : Tendsto (fun n => x (n + N)) atTop (𝓝 τ₀) :=
    hx1.comp (tendsto_add_atTop_nat N)
  have hweak := sa16p_wmp_weak (d := d) (m := m) (p := p) (Set.range Ψ) hΨ
    (B := (Fintype.card (WIndex d m) : ℝ) * B) (fun n => G (x (n + N))) (G τ₀)
    (fun n => hGn _ (hxS n)) (hGn _ hτ₀)
    (by
      rintro i ψ ⟨k, rfl⟩
      have e1 : ∀ n, sa16p_pair p i ((G (x (n + N)) : WmpSpace d m p) : WLp d m p) (Ψ k) =
          A (i, k) (x (n + N)) := fun n => hpairA i k _ (hxS n)
      have e2 := hpairA i k τ₀ hτ₀
      simp only [e1, e2]
      exact ((hAcont i k τ₀ hτ₀).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hx1', Eventually.of_forall hxS⟩)))
    ℓ
  have := (tendsto_add_atTop_iff_nat (f := fun n => ℓ (G (x n))) N).1 hweak
  exact this

end Compact

end HRS.Whole.AppendixA.Phase2SA16P
