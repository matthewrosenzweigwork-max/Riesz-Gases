import HRS.Equilibrium.Parametrix.PX4bAuxL

/-!
# Packet PX4b auxiliaries M: the Poisson cancellation in the chart
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.Parx

variable {d : ℕ}

local notation "∞'" => ((⊤ : ℕ∞) : WithTop ℕ∞)

lemma px4b_lap_eq (f : Euc d → ℝ) (x : Euc d) :
    Laplacian.laplacian f x = ∑ i : Fin d, iteratedFDeriv ℝ 2 f x ![px4b_e i, px4b_e i] := by
  have := congrFun (InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f
    (EuclideanSpace.basisFun (Fin d) ℝ)) x
  rw [this]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [EuclideanSpace.basisFun_apply]

/-- The Laplacian of `z' ↦ f (X + s z')`. -/
lemma px4b_laplacian_aff {f : Euc d → ℝ} (hf : ContDiff ℝ 2 f) (X z : Euc d) (s : ℝ) :
    Laplacian.laplacian (fun z' => f (X + s • z')) z = s ^ 2 * Laplacian.laplacian f (X + s • z) := by
  rw [px4b_lap_eq (fun z' => f (X + s • z')) z, px4b_lap_eq f (X + s • z), Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : ContDiff ℝ 2 (fun w : Euc d => f (X + w)) := hf.comp (contDiff_const.add contDiff_id)
  have e1 : iteratedFDeriv ℝ 2 (fun z' : Euc d => f (X + s • z')) =
      fun x => s ^ 2 • iteratedFDeriv ℝ 2 (fun w : Euc d => f (X + w)) (s • x) :=
    by
      have := iteratedFDeriv_comp_const_smul (𝕜 := ℝ) (i := 2) (f := fun w : Euc d => f (X + w)) s h1
      exact this
  rw [e1]
  have e2 : iteratedFDeriv ℝ 2 (fun w : Euc d => f (X + w)) (s • z) =
      iteratedFDeriv ℝ 2 f (X + s • z) := iteratedFDeriv_comp_add_left 2 X (s • z)
  simp only [e2, ContinuousMultilinearMap.smul_apply, smul_eq_mul]

lemma px4b_laplacian_lift_periodic (a : Torus d → ℝ) (w : Euc d) :
    Laplacian.laplacian (Torus.lift a) w = Torus.laplacian a (Torus.mk w) := by
  unfold Torus.laplacian
  rw [px4b_lap_eq (Torus.lift a) w, px4b_lap_eq (Torus.lift a) (Torus.rep (Torus.mk w))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [iteratedFDeriv_lift_eq_of_mk_eq a 2 (Torus.mk_rep (Torus.mk w)).symm]


/-- The kernel `F + ν ∑_i (∂_{x_i}² N + ∂_{y_i}² N - ½ ∂_{X_i}² N)`, whose chart function is
`F̃ + 2ν Δ_z Ñ`. -/
def px4b_Z0 (ν : ℝ) (F N : Torus d → Torus d → ℝ) : Torus d → Torus d → ℝ := fun x y =>
  F x y + ν * ∑ i : Fin d, (px4b_K1 i (px4b_K1 i N) x y + px4b_dy i (px4b_dy i N) x y -
    (1 / 2 : ℝ) * px4b_dX i (px4b_dX i N) x y)

theorem px4b_Z0_chart {ν : ℝ} {F N : Torus d → Torus d → ℝ} {m : ℕ}
    (hN : ContDiffOn ℝ (m : WithTop ℕ∞) (lift2 N) (offDiag d)) (hm : 2 ≤ m) {X z : Euc d}
    (hz : z ≠ 0) (hzr : ‖z‖ < r0) :
    toChart (px4b_Z0 ν F N) (X, z) =
      toChart F (X, z) + 2 * ν * Laplacian.laplacian (fun z' => toChart N (X, z')) z := by
  have hq : (X, z) ∈ Uc d := mem_Uc hz hzr
  have hf : ContDiffAt ℝ 2 (toChart N) (X, z) :=
    ((toChart_contDiffOn hN).contDiffAt (isOpen_Uc.mem_nhds hq)).of_le (by exact_mod_cast hm)
  rw [px4b_laplacian_chart hf]
  show F (Torus.mk (X + (1 / 2 : ℝ) • z)) (Torus.mk (X - (1 / 2 : ℝ) • z)) + ν * ∑ i : Fin d,
    (toChart (px4b_K1 i (px4b_K1 i N)) (X, z) + toChart (px4b_dy i (px4b_dy i N)) (X, z) -
      (1 / 2 : ℝ) * toChart (px4b_dX i (px4b_dX i N)) (X, z)) = _
  have := fun i => px4b_Z_chart hN hm i hq
  simp_rw [this]
  rw [← Finset.mul_sum]
  have eF : F (Torus.mk (X + (1 / 2 : ℝ) • z)) (Torus.mk (X - (1 / 2 : ℝ) • z)) = toChart F (X, z) := rfl
  rw [eF]
  ring

/-- Poisson cancellation: near the diagonal `F̃ + 2ν Δ_z Ñ` is a smooth kernel. -/
theorem px4b_Z0_poisson {ν : ℝ} {F N G : Torus d → Torus d → ℝ} {a a' : Torus d → ℝ} {c0 : ℝ}
    {m : ℕ} (hN : ContDiffOn ℝ (m : WithTop ℕ∞) (lift2 N) (offDiag d)) (hm : 2 ≤ m)
    (hNeq : ∀ x y, x ≠ y → N x y = G x y - a x - a' y + c0)
    (hG : ContDiffOn ℝ (2 : ℕ) (lift2 G) (offDiag d))
    (ha : ContDiff ℝ 2 (Torus.lift a)) (ha' : ContDiff ℝ 2 (Torus.lift a'))
    (hP : ∀ X z : Euc d, z ≠ 0 → ‖z‖ < 1 / 32 →
      toChart F (X, z) + 2 * ν * Laplacian.laplacian (fun z' => toChart G (X, z')) z = 0)
    {X z : Euc d} (hz : z ≠ 0) (hzr : ‖z‖ < 1 / 32) :
    toChart (px4b_Z0 ν F N) (X, z) =
      -(ν / 2) * (Torus.laplacian a (Torus.mk (X + (1 / 2 : ℝ) • z)) +
        Torus.laplacian a' (Torus.mk (X - (1 / 2 : ℝ) • z))) := by
  have hzr' : ‖z‖ < r0 := by unfold r0; linarith
  rw [px4b_Z0_chart hN hm hz hzr']
  have hq : (X, z) ∈ Uc d := mem_Uc hz hzr'
  have hGc : ContDiffAt ℝ 2 (toChart G) (X, z) :=
    ((toChart_contDiffOn hG).contDiffAt (isOpen_Uc.mem_nhds hq))
  have g1 : ContDiffAt ℝ 2 (fun z' : Euc d => toChart G (X, z')) z :=
    hGc.comp z (contDiffAt_const.prodMk contDiffAt_id)
  have g2 : ContDiff ℝ 2 (fun z' : Euc d => Torus.lift a (X + (1 / 2 : ℝ) • z')) :=
    ha.comp (contDiff_const.add (contDiff_id.const_smul _))
  have g3 : ContDiff ℝ 2 (fun z' : Euc d => Torus.lift a' (X + (-(1 / 2 : ℝ)) • z')) :=
    ha'.comp (contDiff_const.add (contDiff_id.const_smul _))
  obtain ⟨A, hA⟩ : ∃ A : Euc d → ℝ, A = fun z' => toChart G (X, z') := ⟨_, rfl⟩
  obtain ⟨P, hP'⟩ : ∃ P : Euc d → ℝ, P = fun z' => Torus.lift a (X + (1 / 2 : ℝ) • z') := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : Euc d → ℝ, Q = fun z' => Torus.lift a' (X + (-(1 / 2 : ℝ)) • z') := ⟨_, rfl⟩
  have hAc : ContDiffAt ℝ 2 A z := by rw [hA]; exact g1
  have hPc : ContDiffAt ℝ 2 P z := by rw [hP']; exact g2.contDiffAt
  have hQc : ContDiffAt ℝ 2 Q z := by rw [hQ]; exact g3.contDiffAt
  have hev : (fun z' : Euc d => toChart N (X, z')) =ᶠ[𝓝 z] ((A - P - Q) + (fun _ : Euc d => c0) : Euc d → ℝ) := by
    have hU : {z' : Euc d | z' ≠ 0 ∧ ‖z'‖ < r0} ∈ 𝓝 z :=
      (isOpen_ne.inter (isOpen_lt continuous_norm continuous_const)).mem_nhds ⟨hz, hzr'⟩
    filter_upwards [hU] with z' hz'
    have hne : Torus.mk (X + (1 / 2 : ℝ) • z') ≠ Torus.mk (X - (1 / 2 : ℝ) • z') :=
      mem_Uc (X := X) hz'.1 hz'.2
    have h1 : toChart N (X, z') = N (Torus.mk (X + (1 / 2 : ℝ) • z')) (Torus.mk (X - (1 / 2 : ℝ) • z')) := rfl
    have h2 : A z' = G (Torus.mk (X + (1 / 2 : ℝ) • z')) (Torus.mk (X - (1 / 2 : ℝ) • z')) := by
      rw [hA]; rfl
    have h3 : P z' = a (Torus.mk (X + (1 / 2 : ℝ) • z')) := by rw [hP']; rfl
    have h4 : Q z' = a' (Torus.mk (X - (1 / 2 : ℝ) • z')) := by
      rw [hQ]
      show a' (Torus.mk (X + (-(1 / 2 : ℝ)) • z')) = _
      rw [show X + (-(1 / 2 : ℝ)) • z' = X - (1 / 2 : ℝ) • z' by module]
    show toChart N (X, z') = A z' - P z' - Q z' + c0
    rw [h1, h2, h3, h4, hNeq _ _ hne]
  rw [(InnerProductSpace.laplacian_congr_nhds hev).eq_of_nhds]
  have l1 : Laplacian.laplacian (A - P) z = Laplacian.laplacian A z - Laplacian.laplacian P z :=
    hAc.laplacian_sub hPc
  have l2 : Laplacian.laplacian (A - P - Q) z =
      Laplacian.laplacian (A - P) z - Laplacian.laplacian Q z := (hAc.sub hPc).laplacian_sub hQc
  have l3 : Laplacian.laplacian (A - P - Q + (fun _ : Euc d => c0) : Euc d → ℝ) z =
      Laplacian.laplacian (A - P - Q) z + Laplacian.laplacian (fun _ : Euc d => c0) z :=
    ((hAc.sub hPc).sub hQc).laplacian_add (contDiffAt_const (c := c0))
  have hc0 : Laplacian.laplacian (fun _ : Euc d => c0) = 0 := InnerProductSpace.laplacian_const
  have hPl : Laplacian.laplacian P z = (1 / 2 : ℝ) ^ 2 * Torus.laplacian a (Torus.mk (X + (1 / 2 : ℝ) • z)) := by
    rw [hP', px4b_laplacian_aff ha X z (1 / 2 : ℝ), px4b_laplacian_lift_periodic]
  have hQl : Laplacian.laplacian Q z = (-(1 / 2 : ℝ)) ^ 2 * Torus.laplacian a' (Torus.mk (X - (1 / 2 : ℝ) • z)) := by
    rw [hQ, px4b_laplacian_aff ha' X z (-(1 / 2 : ℝ)), px4b_laplacian_lift_periodic]
    rw [show X + (-(1 / 2 : ℝ)) • z = X - (1 / 2 : ℝ) • z by module]
  have hPoi := hP X z hz hzr
  have hAeq : (fun z' => toChart G (X, z')) = A := hA.symm
  rw [hAeq] at hPoi
  rw [l3, l2, l1, hc0, hPl, hQl]
  simp only [Pi.zero_apply, add_zero]
  linarith

end HRS.Parx
end
