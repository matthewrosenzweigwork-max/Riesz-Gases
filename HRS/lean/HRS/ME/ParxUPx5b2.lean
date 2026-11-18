import HRS.ME.ParxU
import HRS.ME.ParxUPx7

/-!
# Packet P4b (part 2): uniform `pair_inverse_small`

`pair_inverse_small` (Packets:1314) is `PairInverseSpec H (parxJ d)`, i.e. `∃ Cinv, 0 ≤ Cinv ∧ W`
where `W` is the four-clause content.  `PairInverseSpecWith H J Cinv` is `W` with the constant
given explicitly.  `pair_inverse_small_unif` chooses `Cinv` before `β, V, ρ`.

`px7_spec_unif` (ParxUPx7) is stated for a fixed `V`.  Its constant is `3 (A M0² K)/(2 c0)`,
where `M0, c0` come from `px7_decay`, `A` from `px7_ev_C2` and `K` from `px7_parseval`; none of
these involves `V`.  So `px7_spec_unifV` re-runs the same proof with `V` quantified inside the
constant: the proof of `px7_spec_unif` with the `∀ β V ρ` moved after the constant, and with the
standing hypotheses `hβ, hV, hρC, hpos, H` read off the bundle `U : ParxU`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.ME.ParxU

open HRS.PDE HRS.PDE.PX7 HRS.PDE.MFAdjoint

variable {d : ℕ}

/-- `PairInverseSpec H J` with the constant `Cinv` given explicitly: the four clauses of
`HRS.Parx.PairInverseSpec` after `∃ Cinv, 0 ≤ Cinv ∧`. -/
def PairInverseSpecWith {d : ℕ} {s : ℝ} {V : Torus d → ℝ} {β : ℝ} {ρ : Torus d → ℝ}
    (H : HRS.Parx.ParxHyp d s V β ρ) (J : ℕ) (Cinv : ℝ) : Prop :=
  (∀ R : Torus d → Torus d → ℝ, HRS.PDE.IsCk2 J R → HRS.PDE.DoublyCentered (withDensityReal ρ) R →
      HRS.PDE.IsCk2 2 (HRS.PDE.pairInverse H.dyn ρ R) ∧
      HRS.PDE.DoublyCentered (withDensityReal ρ) (HRS.PDE.pairInverse H.dyn ρ R) ∧
      HRS.PDE.cbNorm2 2 (HRS.PDE.pairInverse H.dyn ρ R) ≤ Cinv * HRS.PDE.cbNorm2 J R ∧
      ∀ x y, -(HRS.PDE.centeredGen H.dyn ρ (fun x' => HRS.PDE.pairInverse H.dyn ρ R x' y) x +
        HRS.PDE.centeredGen H.dyn ρ (fun y' => HRS.PDE.pairInverse H.dyn ρ R x y') y) = R x y) ∧
  (∀ (R R' : Torus d → Torus d → ℝ) (a b : ℝ), HRS.PDE.IsCk2 J R → HRS.PDE.IsCk2 J R' →
      HRS.PDE.pairInverse H.dyn ρ (fun x y => a * R x y + b * R' x y) =
        fun x y => a * HRS.PDE.pairInverse H.dyn ρ R x y + b * HRS.PDE.pairInverse H.dyn ρ R' x y) ∧
  (∀ R : Torus d → Torus d → ℝ, HRS.PDE.IsCk2 J R → (∀ x y, R x y = R y x) →
      ∀ x y, HRS.PDE.pairInverse H.dyn ρ R x y = HRS.PDE.pairInverse H.dyn ρ R y x) ∧
  (∀ Δ R' : Torus d → Torus d → ℝ, HRS.PDE.IsCk2 (J + 2) Δ → HRS.PDE.IsCk2 J R' →
      HRS.PDE.DoublyCentered (withDensityReal ρ) Δ → HRS.PDE.DoublyCentered (withDensityReal ρ) R' →
      (∀ x y, HRS.PDE.centeredGen H.dyn ρ (fun x' => Δ x' y) x +
        HRS.PDE.centeredGen H.dyn ρ (fun y' => Δ x y') y = R' x y) →
      HRS.PDE.pairInverse H.dyn ρ R' = fun x y => -Δ x y)

/-- `px7_spec_unif` with the constant chosen before `β, V, ρ`, and with `V` quantified inside the
constant (the constant of `px7_spec_unif` does not involve `V`).  The conclusion is the content of
`PairInverseSpecWith U.H J Cinv` for the bundle `U`. -/
theorem px7_spec_unifV (hd2 : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d)
    (N : ℕ) (hN : px7_m d + 2 + mStar d + 3 ≤ N)
    (νm νp c₀ Λ₀ : ℝ) (J : ℕ) (hJ : px7_m d + px7_m d + 2 ≤ J) :
    ∃ Cinv : ℝ, 0 ≤ Cinv ∧ ∀ (β : ℝ) (V ρ : Torus d → ℝ) (U : ParxU d s N νm νp c₀ Λ₀ β V ρ),
      PairInverseSpecWith U.H J Cinv := by
  have hd1 : 1 ≤ d := by omega
  have hm : mStar d + 2 ≤ px7_m d := (px7_m_eq d).ge
  have hj0 : (d : ℝ) / 2 + 4 < ((px7_m d : ℕ) : ℝ) := by
    have : (d : ℝ) / 2 < (⌊(d : ℝ) / 2⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
    have e : ((px7_m d : ℕ) : ℝ) = (⌊(d : ℝ) / 2⌋₊ : ℝ) + 5 := by
      unfold px7_m; push_cast; ring
    rw [e]; linarith
  -- constants fixed before `β`, `V` and `ρ`: decay of the one-variable operator, ev and parseval
  obtain ⟨M0, c0, hM0, hc0, hdec⟩ := px7_decay hd1 s (px7_m d) (px7_m d) hm le_rfl hj0 νm νp c₀ Λ₀
  have hm2 : (d : ℝ) + 4 < 2 * ((px7_m d : ℕ) : ℝ) := by linarith
  obtain ⟨A, hA, hev⟩ := px7_ev_C2 (d := d) (m := px7_m d) hm2
  obtain ⟨K, hK, hK'⟩ := px7_parseval (d := d) (px7_m d) (px7_m d)
  have hdata : ∀ R : Torus d → Torus d → ℝ, IsCk2 (px7_m d + px7_m d) R →
      Mem2 (px7_m d : ℝ) (px7_m d : ℝ) (arr R) ∧ RS (arr R) ∧
        nrm2 (px7_m d : ℝ) (px7_m d : ℝ) (arr R) ≤ K * cbNorm2 (px7_m d + px7_m d) R := by
    intro R hR
    obtain ⟨h1, h2⟩ := hK' R hR
    have hc : Continuous (HRS.PDE.lift2 R) := by
      have : IsCk2 0 R := hR.of_le (by exact_mod_cast Nat.zero_le _)
      simpa [IsCk2] using this.continuous
    exact ⟨h1, px7_arr_RS hc, h2⟩
  have hC0 : 0 ≤ A * (M0 ^ 2 * K) := mul_nonneg hA (mul_nonneg (sq_nonneg _) hK)
  have hc2 : 0 < 2 * c0 := by linarith
  have hCpos : 0 ≤ 3 * (A * (M0 ^ 2 * K)) / (2 * c0) :=
    div_nonneg (mul_nonneg (by norm_num) hC0) hc2.le
  refine ⟨3 * (A * (M0 ^ 2 * K)) / (2 * c0), hCpos, fun β V ρ U => ?_⟩
  have hβ : 0 < β := U.H.beta_pos
  have hV : Torus.IsSmooth V := U.H.V_smooth
  have hρC : Torus.IsSmooth ρ := U.H.rho_smooth.smooth
  have hpos : ∀ x, 0 < ρ x := U.H.rho_smooth.pos
  have H : FrozenHyp d s N νm νp c₀ Λ₀ β V ρ := U.F
  have hρβ : IsThermalDensity (periodicRiesz d s) V β ρ := H.thermal
  have hOV := px7_oneVar_H hd1 s hs0 hsd β hβ V ρ N hN νm νp c₀ Λ₀ H
  -- the decay of the operator at this `β`, `ρ` with the constants fixed above
  have hop : ∀ τ : ℝ, 0 ≤ τ → OpOK ((px7_m d : ℕ) : ℝ)
      (px7_T (mfData d s hs0 hsd V β hβ) ρ (px7_m d) τ) (M0 * Real.exp (-c0 * τ)) := by
    intro τ hτ
    have Hd : FrozenHyp d s (px7_m d + mStar d + 3) νm νp c₀ Λ₀ β V ρ := H.mono (by omega)
    have Hm : FrozenHyp d s (px7_m d + 3) νm νp c₀ Λ₀ β V ρ := H.mono (by omega)
    exact ⟨fun x hx => (hdec β V ρ Hd x hx τ hτ).1, fun x hx => (hdec β V ρ Hd x hx τ hτ).2,
      fun x y hx hy => px7_T_add hd1 (px7_m d) hm Hm hx hy hτ,
      fun a x hx => px7_T_smul hd1 (px7_m d) hm Hm hx a hτ⟩
  have hC2 : ∀ R : Torus d → Torus d → ℝ, IsCk2 (px7_m d + px7_m d) R → ∀ τ : ℝ, 0 ≤ τ →
      IsCk2 2 (pairSemigroup (mfData d s hs0 hsd V β hβ) ρ τ R) ∧
        cbNorm2 2 (pairSemigroup (mfData d s hs0 hsd V β hβ) ρ τ R) ≤
          (A * (M0 ^ 2 * K) * cbNorm2 (px7_m d + px7_m d) R) * Real.exp (-(2 * c0) * τ) :=
    fun R hR τ hτ => px7_pair_C2_of hOV hM0 hop hA hev hdata R hR τ hτ
  have hinv := px7_inv_C2_of (C0 := A * (M0 ^ 2 * K)) (c0 := 2 * c0) hOV hc2 hC2
  have hJm : ∀ R : Torus d → Torus d → ℝ, IsCk2 J R → IsCk2 (px7_m d + px7_m d) R :=
    fun R hR => hR.of_le (by exact_mod_cast (by omega : px7_m d + px7_m d ≤ J))
  unfold PairInverseSpecWith
  refine ⟨fun R hR hcen => ?_, fun R R' a b hR hR' => px7_inv_lin hOV (hJm R hR) (hJm R' hR') a b,
    fun R hR hs x y => px7_inv_symm hOV (hJm R hR) hs x y,
    fun Δ R' hΔ hR' hΔc hR'c heq => ?_⟩
  · obtain ⟨h1, h2, -⟩ := hinv R (hJm R hR)
    refine ⟨h1, px7_inv_cen hOV (hJm R hR), ?_, fun x y => px7_inv_pde hd2 s hs0 hsd β hβ V hV hρβ hρC
      hpos hOV (hR.of_le (by exact_mod_cast (by omega : px7_m d + px7_m d + 2 ≤ J))) hcen x y⟩
    exact h2.trans (mul_le_mul_of_nonneg_left (px7_cbNorm2_mono (by omega) R) hCpos)
  · exact px7_left_inverse hd2 s hs0 hsd β hβ V hV hρβ hρC hpos hOV
      (hΔ.of_le (by exact_mod_cast (by omega : px7_m d + px7_m d + 2 ≤ J + 2))) (hJm R' hR') hΔc heq

/-- **Uniform `pair_inverse_small`.** The constant `Cinv` depends only on `(d, s, N, νm, νp, c₀, Λ₀)`
and is chosen before `β, V, ρ`; for every bundle `U` the pair inverse satisfies the content of
`PairInverseSpec U.H (parxJ d)` with this constant. -/
theorem pair_inverse_small_unif (hd2 : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d)
    (N : ℕ) (hN : px7_m d + 2 + mStar d + 3 ≤ N) (νm νp c₀ Λ₀ : ℝ) :
    ∃ Cinv : ℝ, 0 ≤ Cinv ∧ ∀ (β : ℝ) (V ρ : Torus d → ℝ) (U : ParxU d s N νm νp c₀ Λ₀ β V ρ),
      PairInverseSpecWith U.H (HRS.Parx.parxJ d) Cinv := by
  have hJ : px7_m d + px7_m d + 2 ≤ HRS.Parx.parxJ d := by
    unfold HRS.Parx.parxJ; exact px7_m_le d
  exact px7_spec_unifV hd2 s hs0 hsd N hN νm νp c₀ Λ₀ (HRS.Parx.parxJ d) hJ

end HRS.ME.ParxU

end
