import HRS.MC.E214O6
import HRS.MC.E213U11j

/-!
# Packet E214O, part 7: `Kwin_relax_cond_proof` (the deterministic reduction)
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.E214O

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Plan HRS.MC.E213Final
open HRS.MC.E214Plan

variable {d : ℕ}

theorem o_norm_combo {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] (A A' B B' Cc Cc' : G) :
    ‖(A - (3 : ℝ) • B + (3 : ℝ) • Cc) - (A' - (3 : ℝ) • B' + (3 : ℝ) • Cc')‖ ≤
      (‖A‖ + ‖A'‖) + 3 * ‖B - B'‖ + 3 * ‖Cc - Cc'‖ := by
  have e : (A - (3 : ℝ) • B + (3 : ℝ) • Cc) - (A' - (3 : ℝ) • B' + (3 : ℝ) • Cc') =
      (A - A') - (3 : ℝ) • (B - B') + (3 : ℝ) • (Cc - Cc') := by
    simp only [smul_sub]; abel
  rw [e]
  have h1 := norm_add_le (A - A' - (3 : ℝ) • (B - B')) ((3 : ℝ) • (Cc - Cc'))
  have h2 := norm_sub_le (A - A') ((3 : ℝ) • (B - B'))
  have h3 := norm_sub_le A A'
  have h4 : ‖(3 : ℝ) • (B - B')‖ = 3 * ‖B - B'‖ := by rw [norm_smul]; norm_num
  have h5 : ‖(3 : ℝ) • (Cc - Cc')‖ = 3 * ‖Cc - Cc'‖ := by rw [norm_smul]; norm_num
  linarith

section Reduction

variable {m : ℝ}

theorem o_Kproj_coe {S : PreparedData d} {β₀ : ℝ} {hE : EdgeworthHyp S β₀ m} (gd : GaussData S β₀ hE)
    (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a) :
    ((gd.Kproj T a : projTensor (PathSpace d m T) 3) : TensorDual (PathSpace d m T) 3) = gd.Kwin T a := by
  unfold GaussData.Kproj
  rw [max_eq_left ha, dif_pos (HRS.MC.E213U11.Kwin_mem_proof gd T hT a ha)]

theorem o_Kproj_sub_le {S S' : PreparedData d} {β₀ β₀' : ℝ} {hE : EdgeworthHyp S β₀ m}
    {hE' : EdgeworthHyp S' β₀' m} (gd : GaussData S β₀ hE) (gd' : GaussData S' β₀' hE') (T : ℝ) (hT : 0 < T)
    (a : ℝ) (ha : 0 ≤ a) :
    ‖gd.Kproj T a - gd'.Kproj T a‖ ≤
      (‖pushforward3 (Iwin S β₀ hE T a) (Kinit0 S β₀)‖ + ‖pushforward3 (Iwin S' β₀' hE' T a) (Kinit0 S' β₀')‖) +
      3 * ‖bochTensor3 gd.P₀ (gd.Dwin T a) (gd.Zwin T a) (gd.Zwin T a) -
        bochTensor3 gd'.P₀ (gd'.Dwin T a) (gd'.Zwin T a) (gd'.Zwin T a)‖ +
      3 * ‖bochTensor21 gd.P₀ (gd.Jwin T a) (gd.Zwin T a) - bochTensor21 gd'.P₀ (gd'.Jwin T a) (gd'.Zwin T a)‖ := by
  have h1 := o_Kproj_coe gd T hT a ha
  have h2 := o_Kproj_coe gd' T hT a ha
  have e : ‖gd.Kproj T a - gd'.Kproj T a‖ = ‖gd.Kwin T a - gd'.Kwin T a‖ := by
    change ‖((gd.Kproj T a : projTensor (PathSpace d m T) 3) : TensorDual (PathSpace d m T) 3) -
      ((gd'.Kproj T a : projTensor (PathSpace d m T) 3) : TensorDual (PathSpace d m T) 3)‖ = _
    rw [h1, h2]
  rw [e]
  unfold GaussData.Kwin
  generalize (pushforward3 (Iwin S β₀ hE T a) (Kinit0 S β₀)) = A
  generalize (pushforward3 (Iwin S' β₀' hE' T a) (Kinit0 S' β₀')) = A'
  generalize (bochTensor3 gd.P₀ (gd.Dwin T a) (gd.Zwin T a) (gd.Zwin T a)) = B
  generalize (bochTensor3 gd'.P₀ (gd'.Dwin T a) (gd'.Zwin T a) (gd'.Zwin T a)) = B'
  generalize (bochTensor21 gd.P₀ (gd.Jwin T a) (gd.Zwin T a)) = Cc
  generalize (bochTensor21 gd'.P₀ (gd'.Jwin T a) (gd'.Zwin T a)) = Cc'
  have hsub : ∀ X X' : TensorDual (PathSpace d m T) 3,
      symm3 (PathSpace d m T) X - symm3 (PathSpace d m T) X' = symm3 (PathSpace d m T) (X - X') :=
    fun X X' => (map_sub (symm3 (PathSpace d m T)) X X').symm
  rw [hsub]
  refine (HRS.MC.E213U11.u11_norm_symm3_apply_le _).trans ?_
  exact o_norm_combo (G := TensorDual (PathSpace d m T) 3) _ _ _ _ _ _

end Reduction

end HRS.MC.E214O

end
