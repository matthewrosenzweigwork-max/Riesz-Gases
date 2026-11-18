import HRS.PDE.MovAAux23
import HRS.PDE.MovCAux15

/-!
# SPEC-GF3 repair auxiliary: a good test function `ρt` for every `T`

After the repairs of `movT_srcReg_decomp` / `movT_srcReg_tendsto` to `0 < T` (ISSUES "MOVA", "MOVC"), the consumers that
need the convergence `S^{M_n} → R_N` at `T = 0` use the mean-field right-hand side `ρt' = mova_pdeRHS` instead of the given
(arbitrary at `T = 0`) `ρt`.  `movrepair_good_test` returns a test function `ρt` for which the convergence holds on `[0,T]`.
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

variable {d N : ℕ}

/-- The convergence `S^{M_n} → R_N` off collisions from a decomposition (the argument of `movc_srcReg_tendsto_core`). -/
theorem movrepair_tendsto_of_dec (hN : 2 ≤ N) {D : DynData d} {T : ℝ} {ρ ρt : ℝ → Torus d → ℝ}
    (h : MovTraj D T ρ) {Cι : ℝ}
    (hdec : ∀ M : ℝ, 0 ≤ M → ∀ r ∈ Set.Icc 0 T,
      ∀ X : Config d N, |movT_srcReg D N M ρ ρt r X -
          (-(D.invβ⁻¹ * N) * (movT_commReg D N M (ρ r) X -
            ∫ Y, movT_commReg D N M (ρ r) Y ∂(movT_Q (b15c_gReg d D.s M) D N ρ r)))| ≤
        Cι * N * ∫ z : Torus d, |periodicRiesz d D.s z - b15c_gReg d D.s M z|)
    {M : ℕ → ℝ} (hM : Tendsto M atTop atTop) {r : ℝ} (hr : r ∈ Set.Icc 0 T)
    {X : Config d N} (hX : X ∉ collisionSet d N) :
    Tendsto (fun n => movT_srcReg D N (M n) ρ ρt r X) atTop (𝓝 (movT_source D N ρ r X)) := by
  have hM' : Tendsto (fun n => max (M n) 0) atTop atTop :=
    tendsto_atTop_mono (fun n => le_max_left _ _) hM
  have hM0 : ∀ n, 0 ≤ max (M n) 0 := fun n => le_max_right _ _
  obtain ⟨hC1, hC2⟩ := movc_comm_tendsto hN h hM' hM0 hr hX
  set A : ℕ → ℝ := fun n => -(D.invβ⁻¹ * N) * (movT_commReg D N (max (M n) 0) (ρ r) X -
    ∫ Y, movT_commReg D N (max (M n) 0) (ρ r) Y
      ∂(movT_Q (b15c_gReg d D.s (max (M n) 0)) D N ρ r)) with hA
  have hAt : Tendsto A atTop (𝓝 (-(D.invβ⁻¹ * N) * (movT_commAt D N (ρ r) X -
      ∫ Y, movT_commAt D N (ρ r) Y ∂(movT_Q (periodicRiesz d D.s) D N ρ r)))) :=
    (hC1.sub hC2).const_mul _
  have hI : Tendsto (fun n => ∫ z : Torus d, |periodicRiesz d D.s z - b15c_gReg d D.s (max (M n) 0) z|)
      atTop (𝓝 0) := movc_gReg_L1_tendsto (b15_one_le_d D) D.hs0 D.hsd hM' hM0
  have hd : Tendsto (fun n => movT_srcReg D N (max (M n) 0) ρ ρt r X - A n) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun n => ?_) (by simpa using hI.const_mul (Cι * N))
    rw [Real.norm_eq_abs]
    calc _ ≤ Cι * N * ∫ z : Torus d, |periodicRiesz d D.s z - b15c_gReg d D.s (max (M n) 0) z| :=
          hdec (max (M n) 0) (hM0 n) r hr X
      _ = _ := by ring
  have key := hd.add hAt
  have e : ∀ n, movT_srcReg D N (max (M n) 0) ρ ρt r X - A n + A n =
      movT_srcReg D N (max (M n) 0) ρ ρt r X := fun n => sub_add_cancel _ _
  simp_rw [e] at key
  rw [zero_add] at key
  refine key.congr' ?_
  filter_upwards [hM.eventually (eventually_ge_atTop 0)] with n hn
  simp [max_eq_left hn]

/-- For every trajectory there is a test function `ρt` (`IsC12Test T ρ ρt`) with the convergence `S^{M_n} → R_N` off
collisions on all of `[0,T]`, including `T = 0` (there `ρt` is the mean-field right-hand side; for `0 < T` any test function
works, `movT_srcReg_tendsto`). -/
theorem movrepair_good_test (hN : 2 ≤ N) {D : DynData d} {T : ℝ} {ρ : ℝ → Torus d → ℝ}
    (h : MovTraj D T ρ) :
    ∃ ρt : ℝ → Torus d → ℝ, IsC12Test T ρ ρt ∧
      ∀ {M : ℕ → ℝ}, Tendsto M atTop atTop → ∀ {r : ℝ}, r ∈ Set.Icc 0 T →
        ∀ {X : Config d N}, X ∉ collisionSet d N →
          Tendsto (fun n => movT_srcReg D N (M n) ρ ρt r X) atTop (𝓝 (movT_source D N ρ r X)) := by
  obtain ⟨ρt, hρt⟩ := h.classical
  rcases lt_trichotomy 0 T with hT | hT | hT
  · exact ⟨ρt, hρt, fun hM _ hr _ hX => movc_srcReg_tendsto_pos hN h hρt hT hM hr hX⟩
  · subst hT
    set ρt' : ℝ → Torus d → ℝ := fun r x => mova_pdeRHS D (ρ r) x with hρt'
    have hcP := mova_cont_pde D hρt h.V_reg
    have hρt'c : ∀ r ∈ Set.Icc (0 : ℝ) 0, Continuous (ρt' r) := fun r hr =>
      hcP.comp (continuous_const.prodMk continuous_id :
        Continuous fun x : Torus d => ((⟨r, hr⟩ : Set.Icc (0 : ℝ) 0), x))
    have hρt'T : IsC12Test 0 ρ ρt' :=
      ⟨hρt.c2, hρt.cont_c2, fun x r hr => absurd (hr.1.trans hr.2) (lt_irrefl _), hcP⟩
    obtain ⟨Cι, hCι, hdec⟩ := mova_srcReg_decomp_gen hN h hρt le_rfl hρt'c (fun r hr x => rfl)
    exact ⟨ρt', hρt'T, fun hM _ hr _ hX =>
      movrepair_tendsto_of_dec hN h (fun M hM0 r hr => (hdec M hM0 r hr).1) hM hr hX⟩
  · exact ⟨ρt, hρt, fun _ _ hr => absurd (hr.1.trans hr.2) (not_le.2 hT)⟩

end HRS

end
