import HRS.PDE.MovCAux14

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

variable {d N : ℕ}

theorem movc_srcReg_tendsto_core (hN : 2 ≤ N) {D : DynData d} {T : ℝ} {ρ ρt : ℝ → Torus d → ℝ}
    (h : MovTraj D T ρ) (hρt : IsC12Test T ρ ρt) (hT : 0 < T) {M : ℕ → ℝ}
    (hM : Tendsto M atTop atTop) (hM0 : ∀ n, 0 ≤ M n) {r : ℝ} (hr : r ∈ Set.Icc 0 T)
    {X : Config d N} (hX : X ∉ collisionSet d N) :
    Tendsto (fun n => movT_srcReg D N (M n) ρ ρt r X) atTop (𝓝 (movT_source D N ρ r X)) := by
  obtain ⟨Cι, hCι, hdec⟩ := movT_srcReg_decomp_proof_pos hN h hρt hT
  obtain ⟨hC1, hC2⟩ := movc_comm_tendsto hN h hM hM0 hr hX
  set A : ℕ → ℝ := fun n => -(D.invβ⁻¹ * N) * (movT_commReg D N (M n) (ρ r) X -
    ∫ Y, movT_commReg D N (M n) (ρ r) Y ∂(movT_Q (b15c_gReg d D.s (M n)) D N ρ r)) with hA
  have hAt : Tendsto A atTop (𝓝 (-(D.invβ⁻¹ * N) * (movT_commAt D N (ρ r) X -
      ∫ Y, movT_commAt D N (ρ r) Y ∂(movT_Q (periodicRiesz d D.s) D N ρ r)))) :=
    (hC1.sub hC2).const_mul _
  have hI : Tendsto (fun n => ∫ z : Torus d, |periodicRiesz d D.s z - b15c_gReg d D.s (M n) z|)
      atTop (𝓝 0) := movc_gReg_L1_tendsto (b15_one_le_d D) D.hs0 D.hsd hM hM0
  have hd : Tendsto (fun n => movT_srcReg D N (M n) ρ ρt r X - A n) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun n => ?_) (by simpa using hI.const_mul (Cι * N))
    rw [Real.norm_eq_abs]
    have := ((hdec (M n) (hM0 n) r hr).1 X)
    calc _ ≤ Cι * N * ∫ z : Torus d, |periodicRiesz d D.s z - b15c_gReg d D.s (M n) z| := this
      _ = _ := by ring
  have key := hd.add hAt
  have e : ∀ n, movT_srcReg D N (M n) ρ ρt r X - A n + A n = movT_srcReg D N (M n) ρ ρt r X :=
    fun n => sub_add_cancel _ _
  simp_rw [e] at key
  rw [zero_add] at key
  exact key

theorem movc_srcReg_tendsto_pos (hN : 2 ≤ N) {D : DynData d} {T : ℝ} {ρ ρt : ℝ → Torus d → ℝ}
    (h : MovTraj D T ρ) (hρt : IsC12Test T ρ ρt) (hT : 0 < T) {M : ℕ → ℝ}
    (hM : Tendsto M atTop atTop) {r : ℝ}
    (hr : r ∈ Set.Icc 0 T) {X : Config d N} (hX : X ∉ collisionSet d N) :
    Tendsto (fun n => movT_srcReg D N (M n) ρ ρt r X) atTop (𝓝 (movT_source D N ρ r X)) := by
  have hM' : Tendsto (fun n => max (M n) 0) atTop atTop :=
    tendsto_atTop_mono (fun n => le_max_left _ _) hM
  have := movc_srcReg_tendsto_core hN h hρt hT hM' (fun n => le_max_right _ _) hr hX
  refine this.congr' ?_
  filter_upwards [hM.eventually (eventually_ge_atTop 0)] with n hn
  simp [max_eq_left hn]

end HRS
