import HRS.MC.E213U5a
import HRS.MC.E213E2
import HRS.MC.E213H
import HRS.MC.E213Defs

/-!
# Packet e213u9 (Theorem 2.13, part): `exists_family_of_sequence`

Family assembly from a sequence of bad instances: one `PrepFamily` realising all instances `xs k`
(`e213e_prepared_of_selected` for `N = (xs k).N`, `e213h_exists_prepared_realization` for the other `N ≥ 1`,
a trivial dummy for `N = 0`), and `Z_universal` to replace the given Gaussian by `gd.Zwin`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.E213U9

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Plan

variable {d : ℕ}

section Final

variable {S : PreparedData d} {β₀ m : ℝ}

theorem exists_family_of_sequence_proof (hE : EdgeworthHyp S β₀ m) (T : ℝ) (hT : 0 < T) (gd : GaussData S β₀ hE)
    (xs : ℕ → ExpData S β₀ m T) (hs : StrictMono fun k => (xs k).N) :
    ∃ fam : PrepFamily S β₀ hE, ∀ k, (xs k).expr (gd.Kproj T) =
      gd.errVal T (xs k).N (xs k).a (xs k).Φ (fam.P (xs k).N) (fam.X (xs k).N) := by
  classical
  have hex : ∀ N : ℕ, ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
      (1 ≤ N → PreparedRealization (regime S β₀ hE).D P
        (modulatedGibbs (periodicRiesz d (regime S β₀ hE).D.s) N (regime S β₀ hE).β₀
          (withDensityReal (regime S β₀ hE).ρ₀)) X₀ W X) ∧
      ∀ k, (xs k).N = N →
        law P (windowZeta m T (xs k).a P X) =
          law (xs k).P (windowZeta m T (xs k).a (xs k).P (xs k).X) := by
    intro N
    by_cases hk : ∃ k, (xs k).N = N
    · obtain ⟨k, hkN⟩ := hk
      subst hkN
      obtain ⟨Xc, hXc, hae⟩ := HRS.MC.E213E.e213e_prepared_of_selected (regime S β₀ hE).D S.hd
        (HRS.MC.E213H.e213h_symNonpos_neg_one d) (HRS.MC.E213H.e213h_isCk_two (regime S β₀ hE))
        (xs k).P (( xs k).a + T) (xs k).X₀ (xs k).W (xs k).X (xs k).hSel _ (xs k).hlaw
      refine ⟨(xs k).Ω, (xs k).mΩ, (xs k).P, (xs k).pP, (xs k).X₀, (xs k).W, Xc, fun _ => hXc,
        fun k' hk' => ?_⟩
      have hkk : k' = k := hs.injective hk'
      subst hkk
      exact (HRS.MC.E213E.e213e_windowZeta_congr m T (xs k').a (xs k').ha (xs k').P (xs k').X Xc hae).2.symm
    · by_cases hN : 1 ≤ N
      · obtain ⟨Ω, mΩ, P, pP, X₀, W, X, hX⟩ :=
          HRS.MC.E213H.e213h_exists_prepared_realization (regime S β₀ hE) N hN
        exact ⟨Ω, mΩ, P, pP, X₀, W, X, fun _ => hX, fun k hk' => absurd ⟨k, hk'⟩ hk⟩
      · refine ⟨PUnit, inferInstance, Measure.dirac PUnit.unit, inferInstance, fun _ _ => 0,
          fun _ _ _ => 0, fun _ _ _ => 0, fun h => absurd h hN, fun k hk' => ?_⟩
        exact absurd ⟨k, hk'⟩ hk
  choose Ω mΩ P pP X₀ W X hreal hlaw using hex
  refine ⟨{ Ω := Ω, mΩ := mΩ, P := P, pP := pP, X₀ := X₀, W := W, X := X, hreal := hreal }, fun k => ?_⟩
  have hZ := HRS.MC.E213U5.Z_universal_proof gd T hT (xs k).a (xs k).ha (xs k).ν (xs k).hν (xs k).P'
    (xs k).Z₀ (xs k).Z (xs k).hZ
  have hl := hlaw (xs k).N k rfl
  have hg : Continuous fun w : PathSpace d m T =>
      ((gd.Kproj T (xs k).a : projTensor (PathSpace d m T) 3) : TensorDual (PathSpace d m T) 3)
        (iteratedFDeriv ℝ 3 (xs k).Φ w) :=
    ((gd.Kproj T (xs k).a : projTensor (PathSpace d m T) 3) : TensorDual (PathSpace d m T) 3).continuous.comp
      ((xs k).hΦ.1.continuous_iteratedFDeriv (by norm_num))
  have h2 : ∫ ω, ((gd.Kproj T (xs k).a : projTensor (PathSpace d m T) 3) : TensorDual (PathSpace d m T) 3)
        (iteratedFDeriv ℝ 3 (xs k).Φ (HRS.Main.windowPath m T (xs k).a (xs k).Z ω)) ∂(xs k).P' =
      ∫ ω, ((gd.Kproj T (xs k).a : projTensor (PathSpace d m T) 3) : TensorDual (PathSpace d m T) 3)
        (iteratedFDeriv ℝ 3 (xs k).Φ (gd.Zwin T (xs k).a ω)) ∂gd.P₀ := hZ.2.2.2 _ hg
  unfold ExpData.expr GaussData.errVal
  dsimp only
  rw [hZ.2.2.1, hl, h2]

end Final

end HRS.MC.E213U9

end
