import HRS.Main.HeadlineEdgeworth
import HRS.Sections.AdjKGlue
import HRS.Sections.Sec7Setting

/-!
# Packet E213A: the standing `Regime` of Section 7 from `PreparedData` and `EdgeworthHyp`

`regimeOfPrepared S β₀ hE : Regime d` (D := `S.dyn`, `β := S.β`, `β₀`, `ρ₀ := S.ρ0`, `ρ := S.ρ`), together with
the projection lemmas and `IsSmoothPositiveTrajectory d S.s S.β S.V S.ρ0 S.ρ` (needed by
`adjk_evolution_along_trajectory`).  No use of `Regime.reg`/`Regime.relax`.
-/

noncomputable section

open HRS HRS.Main HRS.Sec7

namespace HRS.MC.E213A

variable {d : ℕ}

/-- The regime of Section 7 attached to a prepared setting `S` and the Edgeworth hypotheses `hE`. -/
def regimeOfPrepared (S : PreparedData d) (β₀ : ℝ) {m : ℝ} (hE : EdgeworthHyp S β₀ m) : Regime d where
  D := S.dyn
  β := S.β
  β₀ := β₀
  ρ₀ := S.ρ0
  ρ := S.ρ
  hd := S.hd
  hM := rfl
  hs := hE.s_lt
  hβ := S.hβ
  hDβ := rfl
  hβ₀ := by
    rcases hE.β₀_pos with h | h
    · exact Or.inl h
    · rcases hE.β₀_nonneg.lt_or_eq with h' | h'
      · exact Or.inl h'
      · exact Or.inr ⟨h, h'.symm⟩
  hV := S.hV
  hρ₀ := S.hρ0
  init := S.hρ_init
  sol := fun K hK => by
    obtain ⟨ρc, h1, h2⟩ := S.hρ K hK
    exact ⟨ρc, h1, fun t _ => by rw [← h2]⟩

section simp_lemmas

variable (S : PreparedData d) (β₀ : ℝ) {m : ℝ} (hE : EdgeworthHyp S β₀ m)

@[simp] theorem regimeOfPrepared_D : (regimeOfPrepared S β₀ hE).D = S.dyn := rfl
@[simp] theorem regimeOfPrepared_ρ : (regimeOfPrepared S β₀ hE).ρ = S.ρ := rfl
@[simp] theorem regimeOfPrepared_ρ₀ : (regimeOfPrepared S β₀ hE).ρ₀ = S.ρ0 := rfl
@[simp] theorem regimeOfPrepared_β : (regimeOfPrepared S β₀ hE).β = S.β := rfl
@[simp] theorem regimeOfPrepared_β₀ : (regimeOfPrepared S β₀ hE).β₀ = β₀ := rfl
@[simp] theorem regimeOfPrepared_D_s : (regimeOfPrepared S β₀ hE).D.s = S.s := rfl
@[simp] theorem regimeOfPrepared_D_V : (regimeOfPrepared S β₀ hE).D.V = S.V := rfl
@[simp] theorem regimeOfPrepared_D_invβ : (regimeOfPrepared S β₀ hE).D.invβ = S.β⁻¹ := rfl
@[simp] theorem regimeOfPrepared_D_M : (regimeOfPrepared S β₀ hE).D.M = -1 := rfl

end simp_lemmas

/-- The prepared trajectory `S.ρ` is a smooth positive trajectory in the sense of `IsSmoothPositiveTrajectory`. -/
theorem isSmoothPositiveTrajectory_of_prepared (S : PreparedData d) :
    IsSmoothPositiveTrajectory d S.s S.β S.V S.ρ0 S.ρ where
  hs0 := S.hs0
  hsd := S.hsd
  hβ := S.hβ
  V_smooth := S.hV
  init := S.hρ0
  global := fun K hK => by
    obtain ⟨ρc, h1, h2⟩ := S.hρ K hK
    exact ⟨ρc, h1, fun t _ => by rw [h2]⟩

/-- The dynamics of the trajectory is `S.dyn`. -/
theorem isSmoothPositiveTrajectory_of_prepared_dyn (S : PreparedData d) :
    (isSmoothPositiveTrajectory_of_prepared S).dyn = S.dyn := rfl

end HRS.MC.E213A

end
