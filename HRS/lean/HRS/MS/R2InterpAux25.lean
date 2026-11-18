import HRS.MS.R2InterpAux24

/-!
# S10.2 (worker S102), part 25 (packet B-grid): `P_L = Λ_L ∘ obs_L` with a `Fin q` enumeration

`q = |idx_L|`, the nodes `τ_k` and Hermite indices `α_k` enumerate the pairs `(i,α)` of `s102_idx d L`; `Λ_L c = ∑_k c_k b_{p(k)}`
is a continuous linear map `ℝ^q → 𝒳` and `P_L w = Λ_L (obs w)`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R2Interp

open HRS HRS.Whole

variable {d : ℕ} {m T : ℝ}

/-- The number of grid observations of `P_L`. -/
def s102_q (d L : ℕ) : ℕ := (s102_idx d L).card

/-- The enumeration of the index set. -/
def s102_pe (d L : ℕ) : Fin (s102_q d L) ≃ ↥(s102_idx d L) := ((s102_idx d L).equivFin).symm

/-- The `k`-th index. -/
def s102_pk (d L : ℕ) (k : Fin (s102_q d L)) : ℕ × MultiIndex d := ((s102_pe d L k) : ℕ × MultiIndex d)

theorem s102_pk_mem (d L : ℕ) (k : Fin (s102_q d L)) : s102_pk d L k ∈ s102_idx d L :=
  (s102_pe d L k).2

/-- The nodes of the observations. -/
def s102_tauk (hT : 0 < T) (L : ℕ) (k : Fin (s102_q d L)) : Set.Icc (0 : ℝ) T :=
  s102_node hT L (s102_pk d L k).1

/-- The Hermite indices of the observations. -/
def s102_alk (L : ℕ) (k : Fin (s102_q d L)) : MultiIndex d := (s102_pk d L k).2

/-- The synthesis map `Λ_L : ℝ^q → 𝒳`. -/
def s102_Lam (T : ℝ) (L : ℕ) : EuclideanSpace ℝ (Fin (s102_q d L)) →L[ℝ] OscPath d m T :=
  LinearMap.toContinuousLinearMap
    { toFun := fun c => ∑ k, c k • s102_bpath T L (s102_pk d L k)
      map_add' := fun c c' => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun a c => by simp [Finset.smul_sum, smul_smul, mul_comm] }

theorem s102_Lam_apply (T : ℝ) (L : ℕ) (c : EuclideanSpace ℝ (Fin (s102_q d L))) :
    (s102_Lam T L c : OscPath d m T) = ∑ k, c k • s102_bpath T L (s102_pk d L k) := rfl

theorem s102_Pj_eq_Lam (hT : 0 < T) (L : ℕ) (w : OscPath d m T) :
    s102_Pj T hT L w = s102_Lam T L (s102_obs (s102_tauk hT L) (s102_alk L) w) := by
  rw [s102_Pj_decomp hT L w, s102_Lam_apply]
  have : ∑ p ∈ s102_idx d L, s102_ellp hT L p w • s102_bpath (m := m) T L p =
      ∑ k : Fin (s102_q d L), s102_ellp hT L (s102_pk d L k) w • s102_bpath (m := m) T L (s102_pk d L k) := by
    rw [← Finset.sum_coe_sort]
    exact (Fintype.sum_equiv (s102_pe d L) _ _ (fun k => rfl)).symm
  rw [this]
  refine Finset.sum_congr rfl fun k _ => ?_
  rfl

end HRS.MS.R2Interp

end
