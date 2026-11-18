import Mathlib
import HRS.MS.SA12BuildC13
import HRS.MS.UniqG1Gronwall

/-!
# S.A.12 C14: weighted dissipation with a time-dependent Schur kernel

The weighted series `Φ(τ) = ∑_z w_z f_z(τ)` is continuous and satisfies the integrated inequality
`Φ(τ) ≤ Φ(0) + ∫_0^τ (A Q Φ + H)`; the integral Gronwall lemma finishes.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Construction

/-- The integrated form of a uniformly dominated weighted series of cell derivatives. -/
theorem sa12c14_series_ftc {ι : Type*} [Countable ι] (t B : ℝ) (w : ι → ℝ) (hw : ∀ z, 0 ≤ w z)
    (hws : Summable w) (f g : ι → ℝ → ℝ)
    (hcont : ∀ z, ContinuousOn (f z) (Icc (0 : ℝ) t))
    (hgcont : ∀ z, ContinuousOn (g z) (Icc (0 : ℝ) t))
    (hderiv : ∀ z, ∀ τ ∈ Icc (0 : ℝ) t, HasDerivWithinAt (f z) (g z τ) (Icc (0 : ℝ) t) τ)
    (hfB : ∀ z, ∀ τ ∈ Icc (0 : ℝ) t, |f z τ| ≤ B) (hgB : ∀ z, ∀ τ ∈ Icc (0 : ℝ) t, |g z τ| ≤ B) :
    ∀ τ ∈ Icc (0 : ℝ) t, (∑' z, w z * f z τ) - (∑' z, w z * f z 0) =
      ∫ σ in Icc (0 : ℝ) τ, ∑' z, w z * g z σ := by
  intro τ hτ
  have ht : 0 ≤ t := hτ.1.trans hτ.2
  have h0t : (0 : ℝ) ∈ Icc (0 : ℝ) t := ⟨le_rfl, ht⟩
  have hsub : Icc (0 : ℝ) τ ⊆ Icc (0 : ℝ) t := Icc_subset_Icc_right hτ.2
  have hsumf : ∀ s ∈ Icc (0 : ℝ) t, Summable fun z => w z * f z s := fun s hs =>
    Summable.of_norm_bounded (hws.mul_right B) (fun z => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw z)]
      exact mul_le_mul_of_nonneg_left (hfB z s hs) (hw z))
  have hint : ∀ z, Integrable (fun σ => w z * g z σ) (volume.restrict (Icc (0 : ℝ) τ)) := fun z =>
    (((hgcont z).mono hsub).integrableOn_Icc).const_mul (w z)
  have hnormle : ∀ z, ∫ σ in Icc (0 : ℝ) τ, ‖w z * g z σ‖ ≤ w z * B * τ := by
    intro z
    calc ∫ σ in Icc (0 : ℝ) τ, ‖w z * g z σ‖ ≤ ∫ _σ in Icc (0 : ℝ) τ, w z * B := by
          refine setIntegral_mono_on (hint z).norm (integrable_const _) measurableSet_Icc fun σ hσ => ?_
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw z)]
          exact mul_le_mul_of_nonneg_left (hgB z σ (hsub hσ)) (hw z)
      _ = w z * B * τ := by
          rw [setIntegral_const, Real.volume_real_Icc_of_le hτ.1, smul_eq_mul]
          ring
  have hsumint : Summable fun z => ∫ σ in Icc (0 : ℝ) τ, ‖w z * g z σ‖ :=
    Summable.of_nonneg_of_le (fun z => integral_nonneg fun σ => norm_nonneg _) hnormle
      (hws.mul_right (B * τ) |>.congr fun z => by ring)
  rw [← integral_tsum_of_summable_integral_norm hint hsumint,
    ← (hsumf τ hτ).tsum_sub (hsumf 0 h0t)]
  refine tsum_congr fun z => ?_
  rw [integral_const_mul]
  have := sa12c13_ftc t (f z) (g z) (hcont z) (hderiv z) (hgcont z) τ hτ
  rw [this]; ring


/-- The pointwise-in-time summed inequality of the weighted cell energies. -/
theorem sa12c14_pointwise {d : ℕ} (A Q ν κ cw B : ℝ)
    (hA : 0 ≤ A) (hQ : 0 ≤ Q) (hν : 0 ≤ ν) (hκ : 0 ≤ κ) (hcw : 0 ≤ cw)
    (w : (Fin d → ℤ) → ℝ) (hw : ∀ z, 0 ≤ w z) (hws : Summable w)
    (E : Finset (Fin d → ℤ)) (hshift : ∀ z, ∀ k ∈ E, w z ≤ cw * w (z + k))
    (hspill : κ * E.card * cw ≤ ν)
    (K : (Fin d → ℤ) → (Fin d → ℤ) → ℝ) (hK : ∀ z z', 0 ≤ K z z')
    (hcol : ∀ z', ∑' z, ENNReal.ofReal (w z) * ENNReal.ofReal (K z z') ≤
        ENNReal.ofReal Q * ENNReal.ofReal (w z'))
    (f g D h : (Fin d → ℤ) → ℝ)
    (hf0 : ∀ z, 0 ≤ f z) (hD0 : ∀ z, 0 ≤ D z) (hh0 : ∀ z, 0 ≤ h z)
    (hfB : ∀ z, f z ≤ B) (hgB : ∀ z, |g z| ≤ B) (hDB : ∀ z, D z ≤ B) (hhB : ∀ z, h z ≤ B)
    (hsum : ∀ z, Summable (fun z' => K z z' * f z'))
    (hineq : ∀ z, g z ≤ -ν * D z + κ * ∑ k ∈ E, D (z + k) +
      A * (∑' z', K z z' * f z') + h z) :
    ∑' z, w z * g z ≤ A * Q * (∑' z, w z * f z) + ∑' z, w z * h z := by
  have hsw : ∀ (u : (Fin d → ℤ) → ℝ), (∀ z, |u z| ≤ B) → Summable fun z => w z * u z := fun u hu =>
    Summable.of_norm_bounded (hws.mul_right B) (fun z => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw z)]
      exact mul_le_mul_of_nonneg_left (hu z) (hw z))
  have hsf : Summable fun z => w z * f z :=
    hsw f fun z => by rw [abs_of_nonneg (hf0 z)]; exact hfB z
  have hsD : Summable fun z => w z * D z :=
    hsw D fun z => by rw [abs_of_nonneg (hD0 z)]; exact hDB z
  have hsh : Summable fun z => w z * h z :=
    hsw h fun z => by rw [abs_of_nonneg (hh0 z)]; exact hhB z
  have hsg : Summable fun z => w z * g z := hsw g hgB
  set S : (Fin d → ℤ) → ℝ := fun z => ∑' z', K z z' * f z' with hS
  have hS0 : ∀ z, 0 ≤ S z := fun z => tsum_nonneg fun z' => mul_nonneg (hK z z') (hf0 z')
  -- the Schur column estimate
  have hSbound : ENNReal.ofReal (∑' z, w z * S z) ≤ ENNReal.ofReal (Q * ∑' z, w z * f z) ∧
      Summable fun z => w z * S z := by
    have h1 : ∀ z, ENNReal.ofReal (w z * S z) = ∑' z', ENNReal.ofReal (w z) *
        (ENNReal.ofReal (K z z') * ENNReal.ofReal (f z')) := by
      intro z
      rw [ENNReal.ofReal_mul (hw z), hS]
      simp only
      rw [ENNReal.ofReal_tsum_of_nonneg (fun z' => mul_nonneg (hK z z') (hf0 z')) (hsum z),
        ← ENNReal.tsum_mul_left]
      refine tsum_congr fun z' => ?_
      rw [ENNReal.ofReal_mul (hK z z')]
    have h2 : ∑' z, ENNReal.ofReal (w z * S z) ≤ ENNReal.ofReal Q * ∑' z', ENNReal.ofReal (w z' * f z') := by
      calc ∑' z, ENNReal.ofReal (w z * S z)
          = ∑' z, ∑' z', ENNReal.ofReal (w z) * (ENNReal.ofReal (K z z') * ENNReal.ofReal (f z')) :=
            tsum_congr h1
        _ = ∑' z', ∑' z, ENNReal.ofReal (w z) * (ENNReal.ofReal (K z z') * ENNReal.ofReal (f z')) :=
            ENNReal.tsum_comm
        _ = ∑' z', ENNReal.ofReal (f z') * ∑' z, ENNReal.ofReal (w z) * ENNReal.ofReal (K z z') := by
            refine tsum_congr fun z' => ?_
            rw [← ENNReal.tsum_mul_left]
            refine tsum_congr fun z => ?_
            ring
        _ ≤ ∑' z', ENNReal.ofReal (f z') * (ENNReal.ofReal Q * ENNReal.ofReal (w z')) :=
            ENNReal.tsum_le_tsum fun z' => mul_le_mul' le_rfl (hcol z')
        _ = ENNReal.ofReal Q * ∑' z', ENNReal.ofReal (w z' * f z') := by
            rw [← ENNReal.tsum_mul_left]
            refine tsum_congr fun z' => ?_
            rw [ENNReal.ofReal_mul (hw z')]
            ring
    have h3 : ∑' z', ENNReal.ofReal (w z' * f z') = ENNReal.ofReal (∑' z, w z * f z) :=
      (ENNReal.ofReal_tsum_of_nonneg (fun z => mul_nonneg (hw z) (hf0 z)) hsf).symm
    rw [h3, ← ENNReal.ofReal_mul hQ] at h2
    have hfin : ∑' z, ENNReal.ofReal (w z * S z) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top h2
    have hsm : Summable fun z => w z * S z := by
      have := ENNReal.summable_toReal hfin
      refine this.congr fun z => ?_
      exact ENNReal.toReal_ofReal (mul_nonneg (hw z) (hS0 z))
    refine ⟨?_, hsm⟩
    rw [ENNReal.ofReal_tsum_of_nonneg (fun z => mul_nonneg (hw z) (hS0 z)) hsm]
    exact h2
  obtain ⟨hSle, hsS⟩ := hSbound
  have hSle' : ∑' z, w z * S z ≤ Q * ∑' z, w z * f z :=
    (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hQ (tsum_nonneg fun z => mul_nonneg (hw z) (hf0 z)))).1 hSle
  -- the spill estimate
  have hshiftsum : ∀ k ∈ E, Summable (fun z => w z * D (z + k)) ∧
      ∑' z, w z * D (z + k) ≤ cw * ∑' z, w z * D z := by
    intro k hk
    have hsD' : Summable fun z => w (z + k) * D (z + k) :=
      (Equiv.summable_iff (Equiv.addRight k)).2 hsD
    have hle : ∀ z, w z * D (z + k) ≤ cw * (w (z + k) * D (z + k)) := fun z => by
      calc w z * D (z + k) ≤ (cw * w (z + k)) * D (z + k) :=
            mul_le_mul_of_nonneg_right (hshift z k hk) (hD0 _)
        _ = _ := by ring
    have hsm : Summable fun z => w z * D (z + k) :=
      Summable.of_nonneg_of_le (fun z => mul_nonneg (hw z) (hD0 _)) hle (hsD'.mul_left cw)
    refine ⟨hsm, ?_⟩
    calc ∑' z, w z * D (z + k) ≤ ∑' z, cw * (w (z + k) * D (z + k)) :=
          hsm.tsum_le_tsum hle (hsD'.mul_left cw)
      _ = cw * ∑' z, w z * D z := by
          rw [tsum_mul_left]
          congr 1
          exact (Equiv.addRight k).tsum_eq (fun z => w z * D z)
  have hsspill : Summable fun z => w z * ∑ k ∈ E, D (z + k) := by
    refine (summable_sum fun k hk => (hshiftsum k hk).1).congr fun z => ?_
    rw [Finset.mul_sum]
  have hsU : Summable fun z => w z * (-ν * D z + κ * ∑ k ∈ E, D (z + k) +
      A * (∑' z', K z z' * f z') + h z) := by
    have := ((hsD.mul_left (-ν)).add (hsspill.mul_left κ)).add (hsS.mul_left A) |>.add hsh
    refine this.congr fun z => ?_
    simp only [hS]
    ring
  have hmono := hsg.tsum_le_tsum (fun z => mul_le_mul_of_nonneg_left (hineq z) (hw z)) hsU
  refine hmono.trans ?_
  have hsplit : ∑' z, w z * (-ν * D z + κ * ∑ k ∈ E, D (z + k) + A * (∑' z', K z z' * f z') + h z) =
      -ν * ∑' z, w z * D z + κ * ∑' z, w z * ∑ k ∈ E, D (z + k) + A * ∑' z, w z * S z +
        ∑' z, w z * h z := by
    have e : ∀ z, w z * (-ν * D z + κ * ∑ k ∈ E, D (z + k) + A * (∑' z', K z z' * f z') + h z) =
        (-ν * (w z * D z) + κ * (w z * ∑ k ∈ E, D (z + k)) + A * (w z * S z)) + w z * h z := fun z => by
      simp only [hS]; ring
    simp_rw [e]
    rw [((hsD.mul_left (-ν)).add (hsspill.mul_left κ) |>.add (hsS.mul_left A)).tsum_add hsh,
      ((hsD.mul_left (-ν)).add (hsspill.mul_left κ)).tsum_add (hsS.mul_left A),
      (hsD.mul_left (-ν)).tsum_add (hsspill.mul_left κ), tsum_mul_left, tsum_mul_left, tsum_mul_left]
  rw [hsplit]
  have hspill' : ∑' z, w z * ∑ k ∈ E, D (z + k) ≤ E.card * (cw * ∑' z, w z * D z) := by
    have e : ∀ z, w z * ∑ k ∈ E, D (z + k) = ∑ k ∈ E, w z * D (z + k) := fun z => Finset.mul_sum _ _ _
    simp_rw [e]
    rw [Summable.tsum_finsetSum fun k hk => (hshiftsum k hk).1]
    calc ∑ k ∈ E, ∑' z, w z * D (z + k) ≤ ∑ _k ∈ E, cw * ∑' z, w z * D z :=
          Finset.sum_le_sum fun k hk => (hshiftsum k hk).2
      _ = E.card * (cw * ∑' z, w z * D z) := by rw [Finset.sum_const, nsmul_eq_mul]
  have hX0 : 0 ≤ ∑' z, w z * D z := tsum_nonneg fun z => mul_nonneg (hw z) (hD0 z)
  have hAS : A * ∑' z, w z * S z ≤ A * (Q * ∑' z, w z * f z) := mul_le_mul_of_nonneg_left hSle' hA
  have hκY : κ * ∑' z, w z * ∑ k ∈ E, D (z + k) ≤ κ * (E.card * (cw * ∑' z, w z * D z)) :=
    mul_le_mul_of_nonneg_left hspill' hκ
  have hkey : κ * (E.card * (cw * ∑' z, w z * D z)) ≤ ν * ∑' z, w z * D z := by
    calc κ * (E.card * (cw * ∑' z, w z * D z)) = (κ * E.card * cw) * ∑' z, w z * D z := by ring
      _ ≤ ν * ∑' z, w z * D z := mul_le_mul_of_nonneg_right hspill hX0
  nlinarith [hAS, hκY, hkey]


-- BEGIN SA12.C14
theorem cell_weighted_dissipation {d : ℕ} (t A Q ν κ cw : ℝ)
    (hA : 0 ≤ A) (hQ : 0 ≤ Q) (hν : 0 ≤ ν) (hκ : 0 ≤ κ) (hcw : 0 ≤ cw)
    (w : (Fin d → ℤ) → ℝ) (hw : ∀ z, 0 ≤ w z) (hws : Summable w)
    (E : Finset (Fin d → ℤ)) (hshift : ∀ z, ∀ k ∈ E, w z ≤ cw*w (z+k))
    (hspill : κ*E.card*cw ≤ ν)
    (K : ℝ → (Fin d → ℤ) → (Fin d → ℤ) → ℝ)
    (hK : ∀ τ z z', 0 ≤ K τ z z')
    (hcol : ∀ τ ∈ Icc (0 : ℝ) t, ∀ z',
      ∑' z, ENNReal.ofReal (w z)*ENNReal.ofReal (K τ z z') ≤
        ENNReal.ofReal Q*ENNReal.ofReal (w z'))
    (f g D h : (Fin d → ℤ) → ℝ → ℝ)
    (hnn : ∀ z, ∀ τ ∈ Icc (0 : ℝ) t, 0 ≤ f z τ ∧ 0 ≤ D z τ ∧ 0 ≤ h z τ)
    (hcont : ∀ z, ContinuousOn (f z) (Icc (0 : ℝ) t) ∧
      ContinuousOn (g z) (Icc (0 : ℝ) t) ∧ ContinuousOn (h z) (Icc (0 : ℝ) t))
    (hderiv : ∀ z, ∀ τ ∈ Icc (0 : ℝ) t,
      HasDerivWithinAt (f z) (g z τ) (Icc (0 : ℝ) t) τ)
    (hdom : ∃ B : ℝ, ∀ z, ∀ τ ∈ Icc (0 : ℝ) t,
      f z τ+|g z τ|+D z τ+h z τ ≤ B)
    (hsum : ∀ z, ∀ τ ∈ Icc (0 : ℝ) t, Summable (fun z' => K τ z z'*f z' τ))
    (hineq : ∀ z, ∀ τ ∈ Icc (0 : ℝ) t,
      g z τ ≤ -ν*D z τ+κ*∑ k ∈ E, D (z+k) τ+
        A*(∑' z', K τ z z'*f z' τ)+h z τ) :
    ∀ τ ∈ Icc (0 : ℝ) t, (∑' z, w z*f z τ) ≤
      Real.exp (A*Q*τ)*((∑' z, w z*f z 0)+
        ∫ σ in Icc (0 : ℝ) τ, ∑' z, w z*h z σ) := by
  intro T0 hT0
  have ht : 0 ≤ t := hT0.1.trans hT0.2
  have h0t : (0 : ℝ) ∈ Icc (0 : ℝ) t := ⟨le_rfl, ht⟩
  obtain ⟨B, hB⟩ := hdom
  have hgabs : ∀ z, ∀ τ ∈ Icc (0 : ℝ) t, 0 ≤ |g z τ| := fun z τ _ => abs_nonneg _
  have hfB : ∀ z, ∀ τ ∈ Icc (0 : ℝ) t, f z τ ≤ B := fun z τ hτ => by
    have := hB z τ hτ; have := hnn z τ hτ; have := hgabs z τ hτ; linarith
  have hgB : ∀ z, ∀ τ ∈ Icc (0 : ℝ) t, |g z τ| ≤ B := fun z τ hτ => by
    have := hB z τ hτ; have := hnn z τ hτ; linarith
  have hDB : ∀ z, ∀ τ ∈ Icc (0 : ℝ) t, D z τ ≤ B := fun z τ hτ => by
    have := hB z τ hτ; have := hnn z τ hτ; have := hgabs z τ hτ; linarith
  have hhB : ∀ z, ∀ τ ∈ Icc (0 : ℝ) t, h z τ ≤ B := fun z τ hτ => by
    have := hB z τ hτ; have := hnn z τ hτ; have := hgabs z τ hτ; linarith
  have hfabs : ∀ z, ∀ τ ∈ Icc (0 : ℝ) t, |f z τ| ≤ B := fun z τ hτ => by
    rw [abs_of_nonneg (hnn z τ hτ).1]; exact hfB z τ hτ
  have hB0 : 0 ≤ B := le_trans (hnn 0 0 h0t).1 (hfB 0 0 h0t)
  have hsuma : ∀ u : (Fin d → ℤ) → ℝ → ℝ, (∀ z, ∀ τ ∈ Icc (0 : ℝ) t, |u z τ| ≤ B) →
      ∀ τ ∈ Icc (0 : ℝ) t, Summable fun z => w z * u z τ := fun u hu τ hτ =>
    Summable.of_norm_bounded (hws.mul_right B) (fun z => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw z)]
      exact mul_le_mul_of_nonneg_left (hu z τ hτ) (hw z))
  have hcontS : ∀ u : (Fin d → ℤ) → ℝ → ℝ, (∀ z, ContinuousOn (u z) (Icc (0 : ℝ) t)) →
      (∀ z, ∀ τ ∈ Icc (0 : ℝ) t, |u z τ| ≤ B) →
      ContinuousOn (fun τ => ∑' z, w z * u z τ) (Icc (0 : ℝ) t) := fun u hu hbd =>
    continuousOn_tsum (u := fun z => w z * B) (fun z => continuousOn_const.mul (hu z))
      (hws.mul_right B) (fun z τ hτ => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw z)]
        exact mul_le_mul_of_nonneg_left (hbd z τ hτ) (hw z))
  have hhabs : ∀ z, ∀ τ ∈ Icc (0 : ℝ) t, |h z τ| ≤ B := fun z τ hτ => by
    rw [abs_of_nonneg (hnn z τ hτ).2.2]; exact hhB z τ hτ
  set Φ : ℝ → ℝ := fun τ => ∑' z, w z * f z τ with hΦ
  set G : ℝ → ℝ := fun τ => ∑' z, w z * g z τ with hG
  set H : ℝ → ℝ := fun τ => ∑' z, w z * h z τ with hH
  have hΦc : ContinuousOn Φ (Icc (0 : ℝ) t) := hcontS f (fun z => (hcont z).1) hfabs
  have hGc : ContinuousOn G (Icc (0 : ℝ) t) := hcontS g (fun z => (hcont z).2.1) hgB
  have hHc : ContinuousOn H (Icc (0 : ℝ) t) := hcontS h (fun z => (hcont z).2.2) hhabs
  have hftc := sa12c14_series_ftc t B w hw hws f g (fun z => (hcont z).1) (fun z => (hcont z).2.1)
    hderiv hfabs hgB
  have hΦ0 : ∀ τ ∈ Icc (0 : ℝ) t, 0 ≤ Φ τ := fun τ hτ =>
    tsum_nonneg fun z => mul_nonneg (hw z) (hnn z τ hτ).1
  have hH0 : ∀ τ ∈ Icc (0 : ℝ) t, 0 ≤ H τ := fun τ hτ =>
    tsum_nonneg fun z => mul_nonneg (hw z) (hnn z τ hτ).2.2
  -- the pointwise inequality
  have hpt : ∀ σ ∈ Icc (0 : ℝ) t, G σ ≤ A * Q * Φ σ + H σ := by
    intro σ hσ
    exact sa12c14_pointwise A Q ν κ cw B hA hQ hν hκ hcw w hw hws E hshift hspill (K σ) (hK σ)
      (hcol σ hσ) (fun z => f z σ) (fun z => g z σ) (fun z => D z σ) (fun z => h z σ)
      (fun z => (hnn z σ hσ).1) (fun z => (hnn z σ hσ).2.1) (fun z => (hnn z σ hσ).2.2)
      (fun z => hfB z σ hσ) (fun z => hgB z σ hσ) (fun z => hDB z σ hσ) (fun z => hhB z σ hσ)
      (fun z => hsum z σ hσ) (fun z => hineq z σ hσ)
  -- the integrated inequality on every `[0, τ]`
  have hint : ∀ τ ∈ Icc (0 : ℝ) t, Φ τ ≤ Φ 0 + A * Q * (∫ σ in Icc (0 : ℝ) τ, Φ σ) +
      ∫ σ in Icc (0 : ℝ) τ, H σ := by
    intro τ hτ
    have hsub : Icc (0 : ℝ) τ ⊆ Icc (0 : ℝ) t := Icc_subset_Icc_right hτ.2
    have hIΦ : IntegrableOn Φ (Icc (0 : ℝ) τ) := (hΦc.mono hsub).integrableOn_Icc
    have hIH : IntegrableOn H (Icc (0 : ℝ) τ) := (hHc.mono hsub).integrableOn_Icc
    have hIG : IntegrableOn G (Icc (0 : ℝ) τ) := (hGc.mono hsub).integrableOn_Icc
    have hle : ∫ σ in Icc (0 : ℝ) τ, G σ ≤ ∫ σ in Icc (0 : ℝ) τ, (A * Q * Φ σ + H σ) :=
      setIntegral_mono_on hIG ((hIΦ.const_mul (A * Q)).add hIH) measurableSet_Icc
        fun σ hσ => hpt σ (hsub hσ)
    rw [integral_add (hIΦ.const_mul (A * Q)) hIH, integral_const_mul] at hle
    have := hftc τ hτ
    simp only [hΦ, hG] at this hle ⊢
    linarith
  -- Gronwall on `[0, T0]`
  have hsub0 : Icc (0 : ℝ) T0 ⊆ Icc (0 : ℝ) t := Icc_subset_Icc_right hT0.2
  set δ : ℝ := Φ 0 + ∫ σ in Icc (0 : ℝ) T0, H σ with hδ
  have hHint0 : 0 ≤ ∫ σ in Icc (0 : ℝ) T0, H σ :=
    setIntegral_nonneg measurableSet_Icc fun σ hσ => hH0 σ (hsub0 hσ)
  have hδ0 : 0 ≤ δ := add_nonneg (hΦ0 0 h0t) hHint0
  have hAQ : 0 ≤ A * Q := mul_nonneg hA hQ
  have hbnd : ∀ τ ∈ Icc (0 : ℝ) T0, Φ τ ≤ (∑' z, w z * B) := by
    intro τ hτ
    have hτt := hsub0 hτ
    exact Summable.tsum_le_tsum (fun z => mul_le_mul_of_nonneg_left (hfB z τ hτt) (hw z))
      (hsuma f hfabs τ hτt) (hws.mul_right B)
  have hgron := HRS.MS.UniqG1.g1_gronwall_source_paren Φ T0 (A * Q) δ hAQ hδ0
    (fun τ hτ => hΦ0 τ (hsub0 hτ)) ⟨∑' z, w z * B, hbnd⟩
    ((hΦc.mono hsub0).aestronglyMeasurable measurableSet_Icc)
    (fun τ hτ => by
      have hτt := hsub0 hτ
      have h1 := hint τ hτt
      have hτσ : Icc (0 : ℝ) τ ⊆ Icc (0 : ℝ) T0 := Icc_subset_Icc_right hτ.2
      have hHle : ∫ σ in Icc (0 : ℝ) τ, H σ ≤ ∫ σ in Icc (0 : ℝ) T0, H σ :=
        setIntegral_mono_set ((hHc.mono hsub0).integrableOn_Icc)
          ((ae_restrict_iff' measurableSet_Icc).2
            (Filter.Eventually.of_forall fun σ hσ => hH0 σ (hsub0 hσ)))
          (Filter.Eventually.of_forall hτσ)
      have hconv : ∫ s in (0 : ℝ)..τ, Φ s = ∫ s in Icc (0 : ℝ) τ, Φ s := by
        rw [intervalIntegral.integral_of_le hτ.1, integral_Icc_eq_integral_Ioc]
      rw [hconv, hδ]
      linarith)
  have := hgron T0 ⟨hT0.1, le_rfl⟩
  calc Φ T0 ≤ δ * Real.exp (A * Q * T0) := this
    _ = Real.exp (A * Q * T0) * (Φ 0 + ∫ σ in Icc (0 : ℝ) T0, H σ) := by rw [hδ]; ring
-- END SA12.C14

end HRS.MH.AdjointRd.Phase2SA12Construction
