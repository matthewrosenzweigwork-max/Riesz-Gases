import HRS.MS.SuppU8Aux2
import HRS.MS.SuppU8Aux5

/-!
# Worker U8 aux 6: the step lists `L_y`, continuity in `y`, and rpow algebra
-/

noncomputable section

open MeasureTheory Metric Set

namespace HRS.U8

section Lists

variable {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup E]
  [NormedSpace ℝ E]

/-- The step list `y, …, y, -y, …, -y` (`m` copies each). -/
def u8_L (m : ℕ) (y : V) : List V :=
  (List.replicate m (1 : ℤ) ++ List.replicate m (-1 : ℤ)).map (fun s => s • y)

theorem u8_L_length (m : ℕ) (y : V) : (u8_L m y).length = 2 * m := by
  simp [u8_L]; ring

theorem u8_L_mem (m : ℕ) (y : V) : ∀ h ∈ u8_L m y, h = y ∨ h = -y := by
  intro h hh
  simp only [u8_L, List.mem_map, List.mem_append, List.mem_replicate] at hh
  obtain ⟨s, (⟨_, rfl⟩ | ⟨_, rfl⟩), rfl⟩ := hh
  · left; simp
  · right; simp

theorem u8_L_norm (m : ℕ) (y : V) : ∀ h ∈ u8_L m y, ‖h‖ ≤ ‖y‖ := by
  intro h hh
  rcases u8_L_mem m y h hh with rfl | rfl
  · exact le_rfl
  · simp

theorem u8_fd_perm {L₁ L₂ : List V} (hp : L₁.Perm L₂) :
    ∀ (u : V → E), u8_fd L₁ u = u8_fd L₂ u := by
  induction hp with
  | nil => intro u; rfl
  | cons a _ ih => intro u; rw [u8_fd_cons, u8_fd_cons, ih]
  | swap a b l =>
    intro u
    rw [u8_fd_cons, u8_fd_cons, u8_fd_cons, u8_fd_cons]
    congr 1
    funext z
    beta_reduce
    simp only [add_right_comm z a b]
    abel
  | trans _ _ ih1 ih2 => intro u; rw [ih1, ih2]

theorem u8_L_neg_perm (m : ℕ) (y : V) : ((u8_L m y).map Neg.neg).Perm (u8_L m y) := by
  have : (u8_L m y).map Neg.neg =
      (List.replicate m (-1 : ℤ) ++ List.replicate m (1 : ℤ)).map (fun s => s • y) := by
    simp only [u8_L, List.map_map, List.map_append, List.map_replicate, Function.comp]
    simp
  rw [this]
  exact (List.perm_append_comm).map _

theorem u8_fd_cont_param (σ : List ℤ) {U : V → V → E} (hU : Continuous (fun p : V × V => U p.1 p.2))
    (x : V) :
    Continuous (fun y => u8_fd (σ.map (fun s => s • y)) (U y) x) := by
  induction σ generalizing U with
  | nil =>
    simp only [List.map_nil, u8_fd_nil]
    exact hU.comp (continuous_id.prodMk continuous_const)
  | cons s σ ih =>
    simp only [List.map_cons, u8_fd_cons]
    apply ih (U := fun y z => U y (z + s • y) - U y z)
    have h0 : Continuous (fun p : V × V => (p.1, p.2 + s • p.1)) := by fun_prop
    exact (hU.comp h0).sub hU

theorem u8_L_cont (m : ℕ) {u : V → E} (hu : Continuous u) (x : V) :
    Continuous (fun y => u8_fd (u8_L m y) u x) :=
  u8_fd_cont_param _ (U := fun _ z => u z) (hu.comp continuous_snd) x

end Lists

end HRS.U8
