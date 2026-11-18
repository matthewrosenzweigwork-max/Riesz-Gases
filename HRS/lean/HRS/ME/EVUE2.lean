import HRS.ME.EVUA
import HRS.ME.EVUC
import HRS.ME.EVUD
import HRS.ME.EVUE1
import HRS.MD.EQEvoUnif

/-!
# Chunk E, packet EVE2: final assembly of the V-uniform frozen data (`eqevo_thermal_unifV`)

`HRS.ME.EVU.eqevo_thermal_unifV` is the V-uniform copy of `HRS.MD.EQEvoUnif.eqevo_thermal_unif`
(`HRS/MD/EQEvoUnif.lean:63`, P7.1). The original statement is kept, with `(Bv : ℝ)` fixed before the
constants and the hypothesis on the potential `V` replaced by `Torus.IsSmooth V → Torus.cbNorm (K+2) V ≤ Bv`.
The constants are chosen in this order: the sup bound `Λ` (`exists_sup_bound_unifV`, EVUA), the `H^K`
bound `C` of the global solutions (`exists_hK_bound_unifV`, EVUC), the thermal bounds `lam, Lam`
(`exists_thermal_bounds_unifV`, EVUD), and the `C^n` constant `Cn` (`frozenHyp_of_bounds`, EVUE1).
Then `Λ₀ := max Bv (Cn * √(C^2))`, `c₀ := lam`, `B := C^2`.

The reference datum is `ρ₀ ≡ 1` (as in the original), with `νm := βp⁻¹`, `νp := βm⁻¹`.
Per `V`, only qualitative facts are used (`HRS.Q41.q41_thermal_pos_cont`,
`HRS.PDE.MFThermalAssembly.thermal_memSobolev_all`, `eqevo_finiteRegHyp_one`, the real-coefficient
lemma `HRS.PDE.MFGlobal.isRealCoeff_of_isMFSolutionHK`), and `|V x| ≤ Bv` comes from `cbNorm (K+2) V ≤ Bv`.
-/

noncomputable section

open MeasureTheory Filter Topology Set

namespace HRS.ME.EVU

open HRS HRS.PDE HRS.PDE.MFAdjoint HRS.Uniform.Q54

variable {d : ℕ}

/-- **EVE2 (P7.1, V-uniform).** Uniform frozen-data bounds: the constants `Λ₀, c₀, lam, Lam, B` are
fixed before `V`, `β` and `ρβ`; the hypothesis on `V` is `IsSmooth V` and `cbNorm (K+2) V ≤ Bv`. -/
theorem eqevo_thermal_unifV (hd : 2 ≤ d) (s βm βp : ℝ) (hs0 : 0 ≤ s) (hsd : s < d)
    (hβm : 0 < βm) (hββ : βm ≤ βp) (Bv : ℝ) :
    ∀ (n K : ℕ), 2 * n + 6 * d + 30 ≤ K →
      ∃ Λ₀ c₀ lam Lam B : ℝ, 0 < c₀ ∧ 0 < lam ∧ 0 ≤ B ∧
        ∀ V : Torus d → ℝ, Torus.IsSmooth V → Torus.cbNorm (K + 2) V ≤ Bv →
        ∀ β ∈ Set.Icc βm βp, ∀ ρβ : Torus d → ℝ, IsThermalDensity (periodicRiesz d s) V β ρβ →
            FrozenHyp d s n βp⁻¹ βm⁻¹ c₀ Λ₀ β V ρβ ∧ (∀ x, lam ≤ ρβ x ∧ ρβ x ≤ Lam) ∧
              hsNormSq (K : ℝ) (coeffOf ρβ) ≤ B := by
  intro n K hK
  have hd1 : 1 ≤ d := by omega
  have hKr : 2 * (n : ℝ) + 6 * (d : ℝ) + 30 ≤ K := by exact_mod_cast hK
  have hdr : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hnr : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hKd2 : (d : ℝ) / 2 + 2 < K := by linarith
  have hnK : (d : ℝ) / 2 + n < K := by linarith
  have hβp : 0 < βp := lt_of_lt_of_le hβm hββ
  have hνm : 0 < βp⁻¹ := inv_pos.2 hβp
  have hνν : βp⁻¹ ≤ βm⁻¹ := inv_anti₀ hβm hββ
  have hρ₀ : IsProbDensity (fun _ : Torus d => (1 : ℝ)) := HRS.MD.EQEvoUnif.eqevo_isProb_one
  have hρH : MemSobolev (K : ℝ) (fun _ : Torus d => (1 : ℝ)) :=
    HRS.MD.EQEvoUnif.eqevo_memSobolev_one K
  have hpos : ∃ c : ℝ, 0 < c ∧ ∀ x : Torus d, c ≤ (fun _ : Torus d => (1 : ℝ)) x :=
    ⟨1, one_pos, fun _ => le_refl _⟩
  obtain ⟨Λ, hΛ0, hΛ⟩ :=
    exists_sup_bound_unifV hd1 s hs0 hsd K hKd2 βp⁻¹ βm⁻¹ hνm hνν (fun _ : Torus d => (1 : ℝ))
      hρ₀ hρH hpos Bv
  obtain ⟨C, hC0, hC⟩ :=
    exists_hK_bound_unifV hd1 s hs0 hsd K hKd2 βp⁻¹ βm⁻¹ hνm hνν (fun _ : Torus d => (1 : ℝ))
      hρH Λ Bv
  obtain ⟨lam, Lam, hlam, hbd⟩ := exists_thermal_bounds_unifV hd1 s hs0 hsd βm βp hβm hββ Bv
  obtain ⟨Cn, hCn0, hF⟩ := frozenHyp_of_bounds (d := d) s βm βp hs0 hsd hβm hββ n K hnK
  refine ⟨max Bv (Cn * Real.sqrt (C ^ 2)), lam, lam, Lam, C ^ 2, hlam, hlam, sq_nonneg C, ?_⟩
  intro V hV hVB β hβ ρβ hρβ
  have hβpos : 0 < β := lt_of_lt_of_le hβm hβ.1
  have hVL : Torus.IsCk ((K + 2 : ℕ) : WithTop ENat) V :=
    HRS.MD.EQEvoUnif.eqevo_isCk_nat hV (K + 2)
  have hVL' : Torus.IsCk (K + 2) V := by exact_mod_cast HRS.MD.EQEvoUnif.eqevo_isCk_nat hV (K + 2)
  have hVc : Continuous V :=
    HRS.PDE.continuous_of_isCk (by exact_mod_cast HRS.MD.EQEvoUnif.eqevo_isCk_nat hV 1)
  -- `|V x| ≤ Bv` from `cbNorm (K+2) V ≤ Bv` (the `C^0` part of the `C^{K+2}` norm)
  have hVb : ∀ x, |V x| ≤ Bv := fun x => by
    have h := HRS.PDE.MFPair.norm_iter_le_cb_ps (L := K + 2) hVL (i := 0) (Nat.zero_le _)
      (Torus.rep x)
    rw [norm_iteratedFDeriv_zero] at h
    have hx : Torus.lift V (Torus.rep x) = V x := by
      simp [Torus.lift, Torus.mk_rep]
    rw [hx, Real.norm_eq_abs] at h
    exact h.trans hVB
  have H0 : FiniteRegHyp d s βm βp K V (fun _ : Torus d => (1 : ℝ)) :=
    HRS.MD.EQEvoUnif.eqevo_finiteRegHyp_one hd s βm βp hs0 hsd hβm hββ V hV K (by omega)
  -- the uniform `H^K` bound of every global solution of this `V`, for `t ≥ 0`
  have hsol : ∀ β' ∈ Set.Icc βm βp, ∀ ρc : ℝ → Coeff d,
      IsMFSolutionHK d s V β'⁻¹ (K : ℝ) (fun _ : Torus d => (1 : ℝ)) ρc →
        ∀ t, 0 ≤ t → HRS.PDE.hsNorm (K : ℝ) (ρc t) ≤ C := by
    intro β' hβ' ρc hρc t ht
    have hβ'pos : 0 < β' := lt_of_lt_of_le hβm hβ'.1
    have hν : β'⁻¹ ∈ Set.Icc βp⁻¹ βm⁻¹ := ⟨inv_anti₀ hβ'pos hβ'.2, inv_anti₀ hβm hβ'.1⟩
    have hreal := HRS.PDE.MFGlobal.isRealCoeff_of_isMFSolutionHK hd1 s βm βp K V
      (fun _ : Torus d => (1 : ℝ)) H0 β' hβ' ρc hρc
    have hR : MFApriori.MFSolRealOn d s V β'⁻¹ K (fun _ : Torus d => (1 : ℝ)) ρc t :=
      ⟨MFApriori.IsMFSolutionHK.toSolOn hρc t, fun τ hτ => hreal τ hτ.1⟩
    have hΛb : ∀ τ ∈ Set.Icc 0 t, ∀ x, |mfPath ρc τ x| ≤ Λ := fun τ hτ x => by
      obtain ⟨h0, h1⟩ := hΛ V hVL' hVB β'⁻¹ hν t ρc hR τ hτ x
      rw [abs_of_nonneg h0]
      exact h1
    exact hC V hVL' hVB β'⁻¹ hν t ρc hR hΛb t ⟨ht, le_rfl⟩
  obtain ⟨hpos, hc⟩ := HRS.Q41.q41_thermal_pos_cont hd hs0 hsd hβpos hVc hρβ
  have hSob : MemSobolev (K : ℝ) ρβ :=
    HRS.PDE.MFThermalAssembly.thermal_memSobolev_all hd1 s hs0 hsd K V hVL' β hβpos ρβ hρβ hc hpos
  have hB : hsNormSq (K : ℝ) (coeffOf ρβ) ≤ C ^ 2 :=
    thermal_hK_of_bound hd1 s βm βp K V (fun _ : Torus d => (1 : ℝ)) H0 C hsol β hβ ρβ hρβ hc
      hpos hSob
  have hlb := hbd V hVc hVb β hβ ρβ hρβ hc hpos
  have hFz := hF Bv lam (C ^ 2) V ρβ β hβ (HRS.MD.EQEvoUnif.eqevo_isCk_nat hV n)
    (le_trans (HRS.PDE.ET.cbNorm_mono' (by omega) V) hVB) hρβ hc hSob hlam
    (fun x => (hlb x).1) (sq_nonneg C) hB
  exact ⟨hFz, hlb, hB⟩

end HRS.ME.EVU
