import HRS.MS.SA16Y3L5
import HRS.MS.SA16Y3Dn1
import HRS.MS.SA16Y3Dy2
import HRS.MS.SA16PRiesz10

/-!
# S.A.16 (SA16Y3) S4: weak compactness of paths from equi-Lipschitz pairings with test functions in `C_c^∞`

`sa16y3_compact_weak`: let `g_n : ℝ → WmpSpace d m p` be bounded by `Bm` on `[0,t]` and suppose for every `ψ ∈ C_c^∞`
the functions `τ ↦ ℓ_ψ(g_n τ)` (zeroth component pairing) are equi-Lipschitz on `[0,t]` with a constant `L_ψ` that may
depend on `ψ`.  Then (`sa16p_wmp_compact`) there are a subsequence and a path `G` with `‖G τ‖ ≤ card(WIndex) Bm`,
`ℓ (g_{φ j} τ) → ℓ (G τ)` for every `ℓ` and `τ ∈ [0,t]`, and `τ ↦ ℓ (G τ)` continuous.
The component pairings of `sa16p_wmp_compact` are reduced to zeroth-component pairings by `sa16y3_comp_ell`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section S4
variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)]

theorem sa16y3_compact_weak {m : ℕ} {t : ℝ} (ht : 0 ≤ t) {Bm : ℝ}
    (g : ℕ → ℝ → WmpSpace d m p) (hB : ∀ n, ∀ τ ∈ Icc (0 : ℝ) t, ‖g n τ‖ ≤ Bm)
    (hLip : ∀ {ψ : Euc d → ℝ} (hψ : IsCcInfty ψ), ∃ L : ℝ≥0, ∀ n,
      LipschitzOnWith L (fun τ => sa16r_ell d m p hψ (g n τ)) (Icc (0 : ℝ) t)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ G : ℝ → WmpSpace d m p,
      (∀ τ ∈ Icc (0 : ℝ) t, ‖G τ‖ ≤ (Fintype.card (WIndex d m) : ℝ) * Bm) ∧
      (∀ τ ∈ Icc (0 : ℝ) t, ∀ ℓ : StrongDual ℝ (WmpSpace d m p),
        Tendsto (fun j => ℓ (g (φ j) τ)) atTop (𝓝 (ℓ (G τ)))) ∧
      (∀ ℓ : StrongDual ℝ (WmpSpace d m p), ContinuousOn (fun τ => ℓ (G τ)) (Icc (0 : ℝ) t)) := by
  have hp2 : (2 : ℝ) ≤ p := Fact.out
  have hpq := Real.HolderConjugate.conjExponent (show 1 < p by linarith)
  have : Fact (1 ≤ ENNReal.ofReal (Real.conjExponent p)) := ⟨by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hpq.symm.lt.le⟩
  have hfin : ENNReal.ofReal (Real.conjExponent p) ≠ ⊤ := ENNReal.ofReal_ne_top
  obtain ⟨Ψ, hΨd, hΨ⟩ := sa16y3_dense_cc (d := d) (Real.conjExponent p) hfin
  refine Phase2SA16P.sa16p_wmp_compact ht Ψ hΨd g hB ?_
  intro i k
  obtain ⟨gk, hgk, hgks, hgkd⟩ := hΨ k
  have hcc : IsCcInfty gk := ⟨hgkd, hgks⟩
  obtain ⟨M, hM, hMeq⟩ := sa16y3_comp_ell (p := p) (m := m) hcc i
  obtain ⟨L, hL⟩ := hLip hM
  refine ⟨L, fun n => ?_⟩
  have heq : (fun τ => Phase2SA16P.sa16p_pair p i ((g n τ : WmpSpace d m p) : WLp d m p) (Ψ k)) =
      fun τ => sa16r_ell d m p hM (g n τ) := by
    funext τ
    unfold Phase2SA16P.sa16p_pair
    rw [sa16r_ell_apply, ← hMeq]
    refine integral_congr_ae ?_
    filter_upwards [hgk] with x hx
    rw [hx]
  rw [heq]
  exact hL n

end S4

end HRS.Whole.AppendixA.Phase2SA16R
