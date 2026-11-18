import HRS.Equilibrium.Parametrix.Defs
import HRS.PDE.MeanFieldAdjointFrozen
import HRS.PDE.MeanFieldVelocityTools
import HRS.PDE.MeanFieldPairSeries
import HRS.PDE.ClassicalPart
import HRS.MD.EQEvoUnif

/-!
# Packet P0 (uniform Parametrix bundle)

`ParxU d s N νm νp c₀ Λ₀ β V ρ` bundles the standing hypotheses of the Parametrix pair-Poisson
theorem (`HRS.Parx.ParxHyp`) with the uniform frozen bounds (`HRS.PDE.MFAdjoint.FrozenHyp`).
The parameters `N, νm, νp, c₀, Λ₀` are fixed before `β, V, ρ`; the extractors below give the
pointwise and `C^k` bounds on `ρ`, `1/ρ`, `∂ⱼρ/ρ` and on `β` in terms of these parameters only.

`parxU_of_eqevo` produces the bundle for every thermal density at `β ∈ [βm, βp]`, with the
constants chosen before `β` and `ρ`, from `HRS.MD.EQEvoUnif.eqevo_thermal_unif`.
-/

noncomputable section

open MeasureTheory Filter Topology Set

namespace HRS.ME.ParxU

variable {d : ℕ} {s : ℝ} {N : ℕ} {νm νp c₀ Λ₀ : ℝ}

/-- The standing hypotheses of the Parametrix theorem together with the uniform frozen bounds. -/
structure ParxU (d : ℕ) (s : ℝ) (N : ℕ) (νm νp c₀ Λ₀ : ℝ) (β : ℝ) (V ρ : Torus d → ℝ) : Prop where
  H : HRS.Parx.ParxHyp d s V β ρ
  F : HRS.PDE.MFAdjoint.FrozenHyp d s N νm νp c₀ Λ₀ β V ρ

/-! ### Extractors -/

/-- Lower bound `c₀ ≤ ρ`. -/
theorem ParxU.rho_ge {β : ℝ} {V ρ : Torus d → ℝ} (U : ParxU d s N νm νp c₀ Λ₀ β V ρ) (x : Torus d) :
    c₀ ≤ ρ x :=
  U.F.hlow x

/-- Upper bound `ρ ≤ Λ₀`, from the `C^0` part of the `C^N` bound. -/
theorem ParxU.rho_le {β : ℝ} {V ρ : Torus d → ℝ} (U : ParxU d s N νm νp c₀ Λ₀ β V ρ) (x : Torus d) :
    ρ x ≤ Λ₀ := by
  have h := HRS.PDE.MFPair.norm_iter_le_cb_ps (L := N) U.F.hρC (i := 0) (Nat.zero_le N) (Torus.rep x)
  rw [norm_iteratedFDeriv_zero] at h
  have hx : Torus.lift ρ (Torus.rep x) = ρ x := by
    simp [Torus.lift, Torus.mk_rep]
  rw [hx] at h
  calc ρ x ≤ |ρ x| := le_abs_self _
    _ = ‖ρ x‖ := (Real.norm_eq_abs _).symm
    _ ≤ Torus.cbNorm N ρ := h
    _ ≤ Λ₀ := U.F.hρb

/-- `C^k` bound of `ρ` for `k ≤ N`. -/
theorem ParxU.cbNorm_rho_le {β : ℝ} {V ρ : Torus d → ℝ} (U : ParxU d s N νm νp c₀ Λ₀ β V ρ)
    {k : ℕ} (hk : k ≤ N) : Torus.cbNorm k ρ ≤ Λ₀ :=
  (U.F.mono hk).hρb

/-- `C^k` bound of the potential `V` for `k ≤ N`. -/
theorem ParxU.cbNorm_V_le {β : ℝ} {V ρ : Torus d → ℝ} (U : ParxU d s N νm νp c₀ Λ₀ β V ρ)
    {k : ℕ} (hk : k ≤ N) : Torus.cbNorm k V ≤ Λ₀ :=
  (U.F.mono hk).hVb

/-- The inverse temperature: `νm ≤ β⁻¹ ≤ νp`, `β ≤ νm⁻¹`, `νp⁻¹ ≤ β`. -/
theorem ParxU.beta_bounds {β : ℝ} {V ρ : Torus d → ℝ} (U : ParxU d s N νm νp c₀ Λ₀ β V ρ) :
    νm ≤ β⁻¹ ∧ β⁻¹ ≤ νp ∧ β ≤ νm⁻¹ ∧ νp⁻¹ ≤ β := by
  obtain ⟨h1, h2⟩ := U.F.hν
  have hβ : 0 < β := U.F.hβ
  have hbi : 0 < β⁻¹ := inv_pos.mpr hβ
  refine ⟨h1, h2, ?_, ?_⟩
  · have := inv_anti₀ U.F.hνm h1
    rwa [inv_inv] at this
  · have := inv_anti₀ hbi h2
    rwa [inv_inv] at this

/-- Auxiliary: `C^k` regularity and bound of `1/ρ`, uniform in `β, V, ρ`. -/
theorem ParxU.inv_data (k : ℕ) (hk : k ≤ N) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (β : ℝ) (V ρ : Torus d → ℝ), ParxU d s N νm νp c₀ Λ₀ β V ρ →
      Torus.IsCk (k : WithTop ℕ∞) (fun x => 1 / ρ x) ∧
        Torus.cbNorm k (fun x => 1 / ρ x) ≤ A := by
  by_cases hc : 0 < c₀
  · obtain ⟨C, hC0, hC⟩ := HRS.PDE.MFVelocity.exists_cbNorm_inv_le (d := d) k c₀ (max c₀ Λ₀) hc
      (le_max_left _ _)
    refine ⟨C * (1 + |Λ₀|) ^ k, mul_nonneg hC0 (by positivity), fun β V ρ U => ?_⟩
    have e : (fun x => 1 / ρ x) = fun x => (ρ x)⁻¹ := funext fun x => one_div (ρ x)
    have hbd : ∀ x, c₀ ≤ ρ x ∧ ρ x ≤ max c₀ Λ₀ := fun x =>
      ⟨U.rho_ge x, (U.rho_le x).trans (le_max_right _ _)⟩
    obtain ⟨hI, hB⟩ := hC ρ (U.F.mono hk).hρC hbd
    rw [e]
    refine ⟨hI, hB.trans ?_⟩
    have hcb := U.cbNorm_rho_le hk
    have hn := HRS.KernelGrad.cbNorm_nonneg' ρ k
    have h1 : 0 ≤ 1 + Torus.cbNorm k ρ := by linarith
    have h2 : 1 + Torus.cbNorm k ρ ≤ 1 + |Λ₀| := by linarith [le_abs_self Λ₀]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h1 h2 k) hC0
  · exact ⟨0, le_rfl, fun β V ρ U => absurd U.F.hc₀ hc⟩

/-- **(2d)** `C^k` bound of `1/ρ` for `k ≤ N`: the constant depends only on `(d, k, c₀, Λ₀)`. -/
theorem ParxU.inv_cbNorm_bound (k : ℕ) (hk : k ≤ N) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (β : ℝ) (V ρ : Torus d → ℝ), ParxU d s N νm νp c₀ Λ₀ β V ρ →
      Torus.cbNorm k (fun x => 1 / ρ x) ≤ A := by
  obtain ⟨A, hA0, hA⟩ := ParxU.inv_data (d := d) (s := s) (N := N) (νm := νm) (νp := νp)
    (c₀ := c₀) (Λ₀ := Λ₀) k hk
  exact ⟨A, hA0, fun β V ρ U => (hA β V ρ U).2⟩

/-- **(2d)** `C^k` bound of `∂ⱼρ / ρ` for `k + 1 ≤ N`: the constant depends only on `(d, j, k, c₀, Λ₀)`. -/
theorem ParxU.partial_div_cbNorm_bound (j : Fin d) (k : ℕ) (hk : k + 1 ≤ N) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (β : ℝ) (V ρ : Torus d → ℝ), ParxU d s N νm νp c₀ Λ₀ β V ρ →
      Torus.cbNorm k (fun x => Torus.partialDeriv j ρ x / ρ x) ≤ A := by
  obtain ⟨Ai, hAi0, hAi⟩ := ParxU.inv_data (d := d) (s := s) (N := N) (νm := νm) (νp := νp)
    (c₀ := c₀) (Λ₀ := Λ₀) k (by omega)
  obtain ⟨C, hC0, hC⟩ := HRS.PDE.MFVelocity.exists_cbNorm_mul_le (d := d) k
  refine ⟨C * |Λ₀| * Ai, mul_nonneg (mul_nonneg hC0 (abs_nonneg _)) hAi0, fun β V ρ U => ?_⟩
  have hρk1 : Torus.IsCk ((k + 1 : ℕ) : WithTop ℕ∞) ρ := (U.F.mono hk).hρC
  obtain ⟨hDk, hDb⟩ := HRS.PDE.ClassicalPart.cbNorm_partialDeriv_le k ρ hρk1 j
  obtain ⟨hI, hIb⟩ := hAi β V ρ U
  have e : (fun x => Torus.partialDeriv j ρ x / ρ x) =
      fun x => Torus.partialDeriv j ρ x * (fun x => 1 / ρ x) x := by
    funext x
    simp only [div_eq_mul_inv, one_mul]
  obtain ⟨hM, hMb⟩ := hC (Torus.partialDeriv j ρ) (fun x => 1 / ρ x) hDk hI
  rw [e]
  refine hMb.trans ?_
  have ha : Torus.cbNorm k (Torus.partialDeriv j ρ) ≤ |Λ₀| :=
    hDb.trans ((U.cbNorm_rho_le hk).trans (le_abs_self _))
  have ha0 := HRS.KernelGrad.cbNorm_nonneg' (Torus.partialDeriv j ρ) k
  have hb0 := HRS.KernelGrad.cbNorm_nonneg' (fun x => 1 / ρ x) k
  exact mul_le_mul (mul_le_mul_of_nonneg_left ha hC0) hIb hb0 (mul_nonneg hC0 (abs_nonneg _))

/-! ### From the equilibrium (EQEvo) uniform bounds -/

/-- The bundle for every thermal density at `β ∈ [βm, βp]`, with constants fixed before `β` and `ρ`
(from `HRS.MD.EQEvoUnif.eqevo_thermal_unif`). -/
theorem parxU_of_eqevo (hd : 2 ≤ d) (s βm βp : ℝ) (hs : s = (d : ℝ) / 2) (hs0 : 0 ≤ s) (hsd : s < d)
    (hβm : 0 < βm) (hββ : βm ≤ βp) (V : Torus d → ℝ) (hV : Torus.IsSmooth V) :
    ∀ (n K : ℕ), 2 * n + 6 * d + 30 ≤ K →
      ∃ c₀ Λ₀ : ℝ, 0 < c₀ ∧ ∀ (β : ℝ), β ∈ Icc βm βp → ∀ ρ : Torus d → ℝ,
        IsThermalDensity (periodicRiesz d s) V β ρ → Torus.IsSmooth ρ → (∀ x, 0 < ρ x) →
          ParxU d s n βp⁻¹ βm⁻¹ c₀ Λ₀ β V ρ := by
  intro n K hK
  obtain ⟨Λ₀, c₀, lam, Lam, B, hc₀, -, -, hmain⟩ :=
    HRS.MD.EQEvoUnif.eqevo_thermal_unif hd s βm βp hs0 hsd hβm hββ V hV n K hK
  refine ⟨c₀, Λ₀, hc₀, fun β hβ ρ hρ hsm hpos => ?_⟩
  have hβpos : 0 < β := lt_of_lt_of_le hβm hβ.1
  have hF := (hmain β hβ ρ hρ).1
  refine ⟨⟨hd, hs, hβpos, hV, hρ, ⟨hρ.1, hsm, hpos⟩⟩, hF⟩

end HRS.ME.ParxU
