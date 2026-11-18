import HRS.MC.E213U4
import HRS.MC.E213U6
import HRS.MC.E213U9b
import HRS.MC.E213U11j
import HRS.MC.E213U18o
import HRS.MC.E213U20
import HRS.MC.E213U21i

/-!
# Theorem 2.13 (`edgeworth_window`): final assembly

The proof modules `E213U1`–`E213U21` prove, one by one, the 42 lemmas of `HRS.MC.E213Plan`.  This file repeats the
glue of `E213Plan` (`Kproj_symmetric`, `core_family`, `uniform_over_realisations`, `edgeworth_window_chain`), which is
proved there from the sorried lemmas, with the proved versions, so that `edgeworth_window_proof` depends only on the
standard axioms.  The statement of `edgeworth_window_proof` is the statement of `HRS.Main.edgeworth_window` (checked in
`E213FinalTie`).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.E213Final

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Plan

variable {d : ℕ} {S : PreparedData d} {β₀ m : ℝ}

theorem Kproj_val_final {hE : EdgeworthHyp S β₀ m} (gd : GaussData S β₀ hE) (T : ℝ) (hT : 0 < T) (a : ℝ)
    (ha : 0 ≤ a) :
    ((gd.Kproj T a : projTensor (PathSpace d m T) 3) : TensorDual (PathSpace d m T) 3) = gd.Kwin T a := by
  classical
  unfold GaussData.Kproj
  rw [max_eq_left ha, dif_pos (HRS.MC.E213U11.Kwin_mem_proof gd T hT a ha)]

theorem Kproj_symmetric_final {hE : EdgeworthHyp S β₀ m} (gd : GaussData S β₀ hE) (T : ℝ) (hT : 0 < T) (a : ℝ)
    (ha : 0 ≤ a) (M : (PathSpace d m T) [×3]→L[ℝ] ℝ) (σ : Equiv.Perm (Fin 3)) :
    ((gd.Kproj T a : projTensor (PathSpace d m T) 3) : TensorDual (PathSpace d m T) 3) (M.domDomCongr σ) =
      ((gd.Kproj T a : projTensor (PathSpace d m T) 3) : TensorDual (PathSpace d m T) 3) M := by
  rw [Kproj_val_final gd T hT a ha]
  exact symm3_symmetric _ M σ

theorem core_family_final (hE : EdgeworthHyp S β₀ m) (gd : GaussData S β₀ hE) (T : ℝ) (hT : 0 < T)
    (fam : PrepFamily S β₀ hE) :
    ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → 2 ≤ N → ∀ (a : ℝ), 0 ≤ a →
      ∀ Φ ∈ CbUnitBall (PathSpace d m T) 5, gd.errVal T N a Φ (fam.P N) (fam.X N) ≤ η := by
  obtain ⟨A, B, C, e, hA, hB, he, hA0, hB0, hCe0, hbd⟩ :=
    HRS.MC.E213U21.core_bound_of_heat gd hE T hT fam (fun T hT a ha Φ hΦ =>
      HRS.MC.E213U20.gaussian_heat_identity_proof gd T hT a ha Φ hΦ)
  classical
  let H : ℕ → ({a : ℝ // 0 ≤ a} × {Φ : PathSpace d m T → ℝ // Φ ∈ CbUnitBall (PathSpace d m T) 5}) → ℝ :=
    fun N x => if 2 ≤ N then gd.errVal T N x.1.1 x.2.1 (fam.P N) (fam.X N) else 0
  have hH : ∀ R : ℕ, 1 ≤ R → ∀ N x, |H N x| ≤ A N + B R + C R * e R N := by
    intro R hR N x
    by_cases hN : 2 ≤ N
    · have h1 := hbd R hR N hN x.1.1 x.1.2 x.2.1 x.2.2
      have h2 : 0 ≤ gd.errVal T N x.1.1 x.2.1 (fam.P N) (fam.X N) := abs_nonneg _
      simp only [H, if_pos hN]
      rw [abs_of_nonneg h2]
      exact h1
    · simp only [H, if_neg hN, abs_zero]
      exact add_nonneg (add_nonneg (hA0 N) (hB0 R)) (hCe0 R N)
  intro η hη
  obtain ⟨N₀, hN₀⟩ := E213B.e213b_double_limit
    (ι := ({a : ℝ // 0 ≤ a} × {Φ : PathSpace d m T → ℝ // Φ ∈ CbUnitBall (PathSpace d m T) 5}))
    A hA B hB C e he H hH η hη
  refine ⟨N₀, fun N hN hN2 a ha Φ hΦ => ?_⟩
  have h := hN₀ N hN (⟨a, ha⟩, ⟨Φ, hΦ⟩)
  simp only [H, if_pos hN2] at h
  exact (le_abs_self _).trans h

theorem uniform_over_realisations_final (hE : EdgeworthHyp S β₀ m) (T : ℝ) (hT : 0 < T) (gd : GaussData S β₀ hE) :
    ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ x : ExpData S β₀ m T, N₀ ≤ x.N → x.expr (gd.Kproj T) ≤ η := by
  intro η hη
  by_contra hcon
  push_neg at hcon
  choose f hf1 hf2 using hcon
  let xs : ℕ → ExpData S β₀ m T := fun k => Nat.rec (f 0) (fun _ y => f (y.N + 1)) k
  have hxs : ∀ k, xs (k + 1) = f ((xs k).N + 1) := fun k => rfl
  have hbad : ∀ k, η < (xs k).expr (gd.Kproj T) := by
    intro k
    cases k with
    | zero => exact hf2 0
    | succ k => rw [hxs]; exact hf2 _
  have hmono : StrictMono fun k => (xs k).N := by
    refine strictMono_nat_of_lt_succ fun k => ?_
    rw [hxs]
    exact hf1 _
  obtain ⟨fam, hfam⟩ := HRS.MC.E213U9.exists_family_of_sequence_proof hE T hT gd xs hmono
  obtain ⟨N₀, hN₀⟩ := core_family_final hE gd T hT fam η hη
  have hk : N₀ ≤ (xs N₀).N := hmono.id_le N₀
  have h2 : 2 ≤ (xs N₀).N := (xs N₀).hN
  have h := hN₀ (xs N₀).N hk h2 (xs N₀).a (xs N₀).ha (xs N₀).Φ (xs N₀).hΦ
  rw [← hfam N₀] at h
  exact absurd h (not_le.mpr (hbad N₀))

theorem edgeworth_window_proof (S : PreparedData d) (β₀ m T : ℝ) (hE : EdgeworthHyp S β₀ m) (hT : 0 < T) :
    ∃ (K : ℝ → projTensor (PathSpace d m T) 3) (ε : ℕ → ℝ), IsWindowEdgeworth S β₀ m T K ε := by
  obtain ⟨gd⟩ := HRS.MC.E213U4.exists_gaussData_proof hE
  obtain ⟨CK, hCK⟩ := HRS.MC.E213U11.Kproj_bounded_proof gd T hT
  have hqual : ∀ η : ℝ, η > 0 → ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ x : ExpData S β₀ m T,
      |(fun (N : ℕ) (x : ExpData S β₀ m T) => if x.N = N then x.expr (gd.Kproj T) else 0) N x| ≤ η := by
    intro η hη
    obtain ⟨N₀, hN₀⟩ := uniform_over_realisations_final hE T hT gd η hη
    refine ⟨N₀, fun N hN x => ?_⟩
    by_cases hx : x.N = N
    · simp only [hx, if_true]
      have h0 : 0 ≤ x.expr (gd.Kproj T) := abs_nonneg _
      rw [abs_of_nonneg h0]
      exact hN₀ x (hx ▸ hN)
    · simp only [hx, if_false, abs_zero]
      exact hη.le
  have hbdd : ∀ N : ℕ, ∃ C : ℝ, ∀ x : ExpData S β₀ m T,
      |(fun (N : ℕ) (x : ExpData S β₀ m T) => if x.N = N then x.expr (gd.Kproj T) else 0) N x| ≤ C := by
    intro N
    refine ⟨2 * Real.sqrt N + CK / 6 + |CK| / 6, fun x => ?_⟩
    by_cases hx : x.N = N
    · simp only [hx, if_true]
      have h0 : 0 ≤ x.expr (gd.Kproj T) := abs_nonneg _
      rw [abs_of_nonneg h0]
      have h1 := HRS.MC.E213U6.expr_le_proof T (gd.Kproj T) CK (fun a ha => hCK a ha) x
      subst hx
      have h2 : CK / 6 ≤ |CK| / 6 := by
        have := le_abs_self CK
        linarith
      linarith [abs_nonneg CK]
    · simp only [hx, if_false, abs_zero]
      have := Real.sqrt_nonneg (N : ℝ)
      linarith [abs_nonneg CK, neg_abs_le CK]
  obtain ⟨ε, hε0, -, hεbd⟩ := E213B.e213b_exists_eps (ι := ExpData S β₀ m T)
    (fun (N : ℕ) (x : ExpData S β₀ m T) => if x.N = N then x.expr (gd.Kproj T) else 0) hqual hbdd
  refine ⟨gd.Kproj T, ε, ?_⟩
  refine ⟨fun a ha M σ => Kproj_symmetric_final gd T hT a ha M σ, ⟨CK, fun a ha => hCK a ha⟩, hε0, ?_,
    fun a ha => HRS.MC.E213U18.Kproj_formula_proof gd T hT a ha⟩
  intro a ha N hN Ω _ P _ X₀ W X hSel hfilt hlaw ν hν Ω' _ P' _ Z₀ Z hZ Φ hΦ
  have h := hεbd N hN ⟨a, ha, N, hN, Ω, P, X₀, W, X, hSel, hfilt, hlaw, ν, hν, Ω', P', Z₀, Z, hZ, Φ, hΦ⟩
  simp only [if_true] at h
  have h0 : 0 ≤ (ExpData.mk a ha N hN Ω P X₀ W X hSel hfilt hlaw ν hν Ω' P' Z₀ Z hZ Φ hΦ).expr (gd.Kproj T) :=
    abs_nonneg _
  rw [abs_of_nonneg h0] at h
  exact h

end HRS.MC.E213Final

end
