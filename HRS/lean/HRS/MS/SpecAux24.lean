import HRS.MS.SpecAux23
import HRS.MS.MovLinAux9

/-!
# S8P: compactness of the embeddings of the oscillator scale (S8.7)

Namespace `HRS.MS.Spec`, helper prefix `s8p_`.  `s8p_osc_embed_compact`: for `r' < r` (and `d ≥ 1`) the embedding
`mov2d_j : Σ^r → Σ^{r'}` is a compact operator (a diagonal operator with entries `λ_α^{(r'-r)/2} → 0`).
-/

noncomputable section

open Filter Topology
open scoped ENNReal

namespace HRS.MS.Spec

open HRS HRS.Whole HRS.MS.MovLin

variable {d : ℕ}

theorem s8p_osc_tendsto_atTop :
    Tendsto (fun α : MultiIndex d => oscEigenvalue d α) cofinite atTop := by
  rw [tendsto_atTop]
  intro b
  have hfin : {α : MultiIndex d | α.degree ≤ ⌈b⌉₊}.Finite := multiIndex_sublevel_finite d ⌈b⌉₊
  filter_upwards [hfin.compl_mem_cofinite] with α hα
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le] at hα
  unfold oscEigenvalue
  have h1 : (⌈b⌉₊ : ℝ) + 1 ≤ α.degree := by exact_mod_cast hα
  have h2 : b ≤ ⌈b⌉₊ := Nat.le_ceil b
  have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  linarith

theorem s8p_osc_rpow_neg {e : ℝ} (he : 0 < e) :
    Tendsto (fun α : MultiIndex d => oscEigenvalue d α ^ (-e)) cofinite (𝓝 0) :=
  (tendsto_rpow_neg_atTop he).comp s8p_osc_tendsto_atTop

theorem s8p_osc_embed_compact {r r' : ℝ} (h : r' < r) :
    IsCompactOperator (mov2d_j (d := d) h.le) := by
  have hD : ∀ (x : lp (fun _ : MultiIndex d => ℝ) 2) (α : MultiIndex d),
      (show lp (fun _ : MultiIndex d => ℝ) 2 from mov2d_j (d := d) h.le (show OscSpace d r from x)) α =
        oscEigenvalue d α ^ ((r' - r) / 2) * x α := by
    intro x α
    exact mov2d_j_coord h.le (show OscSpace d r from x) α
  have ha : Tendsto (fun α : MultiIndex d => oscEigenvalue d α ^ ((r' - r) / 2)) cofinite (𝓝 0) := by
    have := s8p_osc_rpow_neg (d := d) (e := (r - r') / 2) (by linarith)
    convert this using 3
    ring
  exact s8p_diag_compact _ ha (mov2d_j (d := d) h.le) hD

end HRS.MS.Spec
