/-
# HRS.ME.FamVA: the rate family `V_θ = -θφ/β` is a bounded smooth potential family (packet V1)

For `φ = cos(2πk·x)` and fixed `β ≠ 0`, the rate-family potentials `V_θ = HRS.rateV k β θ`
(`H:eq:rate-family`, see `HRS/Equilibrium/Response.lean`) are constant multiples
`(-θ/β) • φ` of a single mode.  This file proves, for `{d : ℕ}`:

* `rateV_isSmooth`: each `V_θ` is `C^∞` on the torus;
* `cbNorm_rateV_le`: `cbNorm j V_θ ≤ |θ|/|β| · cbNorm j φ` (homogeneity of `cbNorm`);
* `rateFamily_bounded`: the family `{V_θ : θ ∈ [0,R]}` is `PotentialFamilyBounded`
  (`HRS/Main/HeadlineEquilibrium.lean`), with the uniform constant `Λ = R/|β| · cbNorm j φ`.

Smoothness of `cosMode` is proved locally (as `HRS.d1_isSmooth_cosMode` in `HRS/PDE/TorusFPSpec.lean`); the scalar
homogeneity of `cbNorm` is `HRS.PDE.MFPair.cbNorm_smul_le_ps` (`HRS/PDE/MeanFieldPairSeries.lean`).
-/
import HRS.Main.HeadlineEquilibrium

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.ME.FamV

variable {d : ℕ}

/-- `V_θ = -θφ/β` is the constant `(-θ/β)` times `φ = cosMode k` (pointwise identity). -/
theorem rateV_eq_smul (k : Lattice d) (β θ : ℝ) :
    HRS.rateV k β θ = fun x => (-θ / β) * Torus.cosMode k x := by
  funext x
  unfold HRS.rateV
  ring

/-- `cosMode k` is `C^∞` on the torus (same proof as `HRS.d1_isSmooth_cosMode`, which is not in
the import closure of this file). -/
theorem cosMode_isSmooth (k : Lattice d) : Torus.IsSmooth (Torus.cosMode k) := by
  unfold Torus.IsSmooth Torus.IsCk
  have : Torus.lift (Torus.cosMode k) = fun y => Real.cos (2 * Real.pi * Lattice.dot k y) :=
    funext fun y => Torus.cosMode_mk k y
  rw [this]
  refine Real.contDiff_cos.comp (contDiff_const.mul ?_)
  unfold Lattice.dot
  exact ContDiff.sum fun i _ => contDiff_const.mul (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).contDiff

/-- Each rate-family potential is `C^∞` on the torus. -/
theorem rateV_isSmooth (k : Lattice d) (β θ : ℝ) : Torus.IsSmooth (HRS.rateV k β θ) := by
  rw [rateV_eq_smul]
  have hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift (Torus.cosMode k)) :=
    cosMode_isSmooth k
  have e : Torus.lift (fun x => (-θ / β) * Torus.cosMode k x) =
      fun y => (-θ / β) * Torus.lift (Torus.cosMode k) y := rfl
  unfold Torus.IsSmooth Torus.IsCk
  rw [e]
  exact contDiff_const.mul hc

/-- Homogeneity of the `C^j` norm: `cbNorm j V_θ ≤ |θ|/|β| · cbNorm j φ`. -/
theorem cbNorm_rateV_le (k : Lattice d) (β θ : ℝ) (j : ℕ) :
    Torus.cbNorm j (HRS.rateV k β θ) ≤ |θ| / |β| * Torus.cbNorm j (Torus.cosMode k) := by
  rw [rateV_eq_smul]
  have hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift (Torus.cosMode k)) :=
    cosMode_isSmooth k
  have hc : ContDiff ℝ ((j : ℕ∞) : WithTop ℕ∞) (Torus.lift (Torus.cosMode k)) :=
    hs.of_le (by exact_mod_cast le_top)
  have h := HRS.PDE.MFPair.cbNorm_smul_le_ps (d := d) (L := j) hc (-θ / β)
  have e2 : |-θ / β| = |θ| / |β| := by rw [abs_div, abs_neg]
  rw [e2] at h
  exact h

/-- The rate family `{V_θ : θ ∈ [0,R]}` is bounded in every `C^j` norm, uniformly in `θ`. -/
theorem rateFamily_bounded (k : Lattice d) (β R : ℝ) :
    HRS.Main.PotentialFamilyBounded
      {V : Torus d → ℝ | ∃ θ ∈ Set.Icc (0 : ℝ) R, V = HRS.rateV k β θ} := by
  unfold HRS.Main.PotentialFamilyBounded
  refine ⟨fun V hV => ?_, fun j => ?_⟩
  · obtain ⟨θ, _, rfl⟩ := hV
    exact rateV_isSmooth k β θ
  · refine ⟨R / |β| * Torus.cbNorm j (Torus.cosMode k), ?_⟩
    rintro V ⟨θ, ⟨h0, hR⟩, rfl⟩
    have hnn : 0 ≤ Torus.cbNorm j (Torus.cosMode k) :=
      Finset.sum_nonneg fun i _ => Real.iSup_nonneg fun x => norm_nonneg _
    have hθR : |θ| ≤ R := by
      rw [abs_of_nonneg h0]
      exact hR
    have hdiv : |θ| / |β| ≤ R / |β| := by
      gcongr
    exact (cbNorm_rateV_le k β θ j).trans (mul_le_mul_of_nonneg_right hdiv hnn)

end HRS.ME.FamV
