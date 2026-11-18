import HRS.MS.R2ObsAux6
import HRS.MS.R2ObsAux3

/-!
# S9.10 path row, packet 7: identification of the path objects with images of vectors of `K = ℓ²(ℕ × ℕ^d)`

Worker S910, namespace `HRS.MS.R2Obs`.  Features `ψ_n = c_J f_{σ n}` (`f_q` the cosine orbit tests, `c_J = s11p_cJ T`), the
basis `e = s11p_basis σ` of `K`; `J = s11p_J` the cosine synthesis map `K → C([0,T];B_m)` of norm `≤ 1`.

* `s910_J_coord_series`: if `z_q = c_J y_q` then `coord (J z (t)) α = ∑_n κ_n e_n(t) y_{(n,α)}`;
* `s910_coord_symm`: `(Ψ⁻¹ w)_{σ n} = w_n`;
* `s910_ell_coord`: the coordinates of `r2EllH` are `c_J a_{f_q}(x)`; `s910_field_coord`: those of `r2FieldH`;
* `s910_data`: the orbit features as an `S11pData`.
-/

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

noncomputable section

namespace HRS.MS.R2Obs

open S99 S45 HRS.Whole
open HRS (Euc cbNorm MemCb)

variable {d : ℕ}

theorem s910_memCb_mono {k k' : ℕ} (h : k' ≤ k) {φ : Euc d → ℝ} (hφ : MemCb k φ) : MemCb k' φ :=
  ⟨hφ.1.of_le (by exact_mod_cast h), fun j hj => hφ.2 j (hj.trans h)⟩

theorem s910_cbNorm_mono {k k' : ℕ} (h : k' ≤ k) (φ : Euc d → ℝ) : cbNorm k' φ ≤ cbNorm k φ := by
  unfold cbNorm
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun j _ _ => Real.iSup_nonneg fun _ => norm_nonneg _)
  exact Finset.range_subset_range.2 (by omega)

theorem s910_J_coord_series {T : ℝ} (hT : 0 < T) (M : ℝ) (z : s11p_K d) (y : ℕ × MultiIndex d → ℝ)
    (hz : ∀ q, z.c q = s11p_cJ T * y q) (t : Set.Icc (0 : ℝ) T) (α : MultiIndex d) :
    OscDual.coord (OscPath.at' (s11p_J hT M z) t) α =
      ∑' n : ℕ, s11p_kap n * r2CosBasis T n t * y (n, α) := by
  rw [s11p_J_coord]
  have hc := (s11p_cJ_pos T).ne'
  simp_rw [hz]
  have : ∀ n : ℕ, s11p_kap n * r2CosBasis T n t * (s11p_cJ T * y (n, α)) =
      s11p_cJ T * (s11p_kap n * r2CosBasis T n t * y (n, α)) := fun n => by ring
  simp_rw [this]
  rw [tsum_mul_left]
  field_simp

theorem s910_coord_symm (σ : ℕ ≃ ℕ × MultiIndex d) (w : SeqL2) (n : ℕ) :
    ((s910_Psi (s11p_basis σ)).symm w).c (σ n) = SeqL2.coord w n := by
  rw [← s11p_inner_basis σ n, ← s910_Psi_coord, LinearIsometryEquiv.apply_symm_apply]

/-- The orbit features as an `S11pData`. -/
def s910_data {f : ℕ × MultiIndex d → Euc d → ℝ} (hf : ∀ q, MemCb (J1 d) (f q))
    (hsum : Summable fun q => cbNorm (J1 d) (f q)) : S11pData d where
  f := f
  w := fun q => cbNorm (J1 d) (f q)
  hw := hsum
  hfw q x := s11p_abs_le_cbNorm (hf q) x
  hfc q := (hf q).1.continuous

section Coord

variable (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {a β γ : ℝ} (ha : 0 < a) (hβ : 0 < β)
  (hγ : 0 < γ) {c : ℝ} {f : ℕ × MultiIndex d → Euc d → ℝ} (hf : ∀ q, MemCb (J1 d) (f q))
  (σ : ℕ ≃ ℕ × MultiIndex d) (E : Env d s a β γ (fun n x => c * f (σ n) x))

include hd hs0 hs ha hβ hγ hf E

theorem s910_ell_coord (x : Euc d) (q : ℕ × MultiIndex d) :
    (r2EllH (s11p_basis σ) (fun n x => c * f (σ n) x) (rieszKernel d s) (thermalMeasure d s a β) γ x).c q =
      c * aRep d s a β γ (f q) x := by
  have hsd : s < d := by
    have : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
    linarith
  obtain ⟨n, rfl⟩ := σ.surjective q
  rw [s910_ell_eq hd hs0 hs ha hβ hγ E (s11p_basis σ) x, s910_coord_symm,
    s99_ellv_coord hd hs0 hs ha hβ hγ E.hT E.hφ E.F x n]
  exact s910_resp_smul hd hs0 hsd ha hβ hγ (hf (σ n)) c x

end Coord

end HRS.MS.R2Obs

end
