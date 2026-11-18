import HRS.MS.WsInitGAux5
import HRS.MS.QsfAsm11
import HRS.MS.QsfOsc8

/-!
# S21 packet G, part 6: the transport `SeqL2 ≅ K`, the synthesis map `Φ : SeqL2 → C([0,T];B_m)` and its coordinates

`s21gTheta σ : SeqL2 ≃ₗᵢ s11p_K d` (through the Hilbert basis `s11p_basis σ`, `σ : ℕ ≃ ℕ × MultiIndex d`), `s21gPhi = (c_J • s11p_J) ∘ Θ`
(`‖Φ‖ ≤ c_J`).  `s21gPhi_coord_inner`: `coord (Φ z)(t)_α = ⟪a_{t,α}, z⟫` with the explicit vector `a_{t,α} ∈ SeqL2`, whose coordinates are
`[σ j = (n,α)] κ_n e_n(t)`; `s21gPhi_coord`: the cosine series `∑_n κ_n e_n(t) (Θ z)_{n,α}`.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S21

open HRS HRS.Whole

variable {d : ℕ}

/-- The isometry `SeqL2 ≃ K = ℓ²(ℕ × ℕ^d)` through the Hilbert basis indexed by `ℕ`. -/
def s21gTheta (σ : ℕ ≃ ℕ × MultiIndex d) : SeqL2 ≃ₗᵢ[ℝ] s11p_K d :=
  S45.s45_seqRepr.trans (s11p_basis σ).repr.symm

theorem s21gTheta_c (σ : ℕ ≃ ℕ × MultiIndex d) (z : SeqL2) (j : ℕ) :
    (s21gTheta σ z).c (σ j) = SeqL2.coord z j := by
  rw [← s11p_inner_basis σ j, ← HilbertBasis.repr_apply_apply]
  have : (s11p_basis σ).repr (s21gTheta σ z) = S45.s45_seqRepr z := by
    unfold s21gTheta
    simp
  rw [this]
  rfl

/-- The synthesis map. -/
def s21gPhi (σ : ℕ ≃ ℕ × MultiIndex d) {T : ℝ} (hT : 0 < T) (M : ℝ) : SeqL2 →L[ℝ] OscPath d M T :=
  ((s11p_cJ T) • (s11p_J hT M : s11p_K d →L[ℝ] OscPath d M T)).comp
    (s21gTheta σ).toContinuousLinearEquiv.toContinuousLinearMap

theorem s21gPhi_norm_le (σ : ℕ ≃ ℕ × MultiIndex d) {T : ℝ} (hT : 0 < T) (M : ℝ) :
    ‖(s21gPhi σ hT M)‖ ≤ s11p_cJ T := by
  unfold s21gPhi
  have h1 : ‖(s11p_cJ T) • (s11p_J hT M : s11p_K d →L[ℝ] OscPath d M T)‖ ≤ s11p_cJ T := by
    refine (norm_smul_le (s11p_cJ T) (s11p_J hT M : s11p_K d →L[ℝ] OscPath d M T)).trans ?_
    rw [Real.norm_of_nonneg (s11p_cJ_pos T).le]
    calc s11p_cJ T * ‖(s11p_J hT M : s11p_K d →L[ℝ] OscPath d M T)‖ ≤ s11p_cJ T * 1 :=
          mul_le_mul_of_nonneg_left (s11p_J_norm_le hT M) (s11p_cJ_pos T).le
      _ = _ := mul_one _
  have h2 : ‖(s21gTheta σ).toContinuousLinearEquiv.toContinuousLinearMap‖ ≤ 1 :=
    (s21gTheta σ).toLinearIsometry.norm_toContinuousLinearMap_le
  calc _ ≤ ‖(s11p_cJ T) • (s11p_J hT M : s11p_K d →L[ℝ] OscPath d M T)‖ *
        ‖(s21gTheta σ).toContinuousLinearEquiv.toContinuousLinearMap‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ s11p_cJ T * 1 := mul_le_mul h1 h2 (norm_nonneg _) (s11p_cJ_pos T).le
    _ = _ := mul_one _

theorem s21gPhi_coord (σ : ℕ ≃ ℕ × MultiIndex d) {T : ℝ} (hT : 0 < T) (M : ℝ) (z : SeqL2)
    (t : Set.Icc (0 : ℝ) T) (α : MultiIndex d) :
    OscDual.coord (OscPath.at' (s21gPhi σ hT M z) t) α =
      ∑' n : ℕ, s11p_kap n * r2CosBasis T n t * (s21gTheta σ z).c (n, α) := by
  have h := s11p_J_coord hT M (s21gTheta σ z) t α
  have e : OscDual.coord (OscPath.at' (s21gPhi σ hT M z) t) α =
      s11p_cJ T * OscDual.coord (OscPath.at' (s11p_J hT M (s21gTheta σ z)) t) α := rfl
  rw [e, h, ← mul_assoc, mul_inv_cancel₀ (s11p_cJ_pos T).ne', one_mul]

/-- The coefficient vector of `coord (Φ z)(t)_α`. -/
def s21gVec (σ : ℕ ≃ ℕ × MultiIndex d) {T : ℝ} (hT : 0 < T) (t : ℝ) (α : MultiIndex d) : SeqL2 :=
  (s21gTheta σ).symm ((s11p_cJ T) • s11p_vec hT t α)

theorem s21gPhi_coord_inner (σ : ℕ ≃ ℕ × MultiIndex d) {T : ℝ} (hT : 0 < T) (M : ℝ) (z : SeqL2)
    (t : Set.Icc (0 : ℝ) T) (α : MultiIndex d) :
    OscDual.coord (OscPath.at' (s21gPhi σ hT M z) t) α = inner ℝ (s21gVec σ hT t α) z := by
  have e : OscDual.coord (OscPath.at' (s21gPhi σ hT M z) t) α =
      s11p_cJ T * OscDual.coord (OscPath.at' (s11p_J hT M (s21gTheta σ z)) t) α := rfl
  rw [e, ← s11p_inner_vec hT M (s21gTheta σ z) t α]
  unfold s21gVec
  rw [← (s21gTheta σ).inner_map_map, LinearIsometryEquiv.apply_symm_apply, inner_smul_left]
  simp

theorem s21gVec_coord (σ : ℕ ≃ ℕ × MultiIndex d) {T : ℝ} (hT : 0 < T) (t : ℝ) (α : MultiIndex d) (j : ℕ) :
    SeqL2.coord (s21gVec σ hT t α) j =
      if (σ j).2 = α then s11p_kap (σ j).1 * r2CosBasis T (σ j).1 t else 0 := by
  classical
  have h := s21gTheta_c σ (s21gVec σ hT t α) j
  rw [← h]
  unfold s21gVec
  rw [LinearIsometryEquiv.apply_symm_apply]
  show s11p_cJ T * (s11p_vec hT t α).c (σ j) = _
  unfold s11p_vec
  rw [s11p_K.c_mk]
  split_ifs with hα
  · rw [← mul_assoc, mul_inv_cancel₀ (s11p_cJ_pos T).ne', one_mul]
  · simp

end HRS.MS.S21
