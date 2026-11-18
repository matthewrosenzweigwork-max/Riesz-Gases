import HRS.MS.TiltAux1

/-!
# S4.7 packet P2: the corrector at the perturbed reference

`S47Feat`: a corrector `χ` of `φ` for the susceptibility `A = γ⁻¹ I + K_μ` about the reference `μ = ρ dx`, with respect to the
weighted generator `L_ρ = -Δ - ∇log ρ · ∇` (`weightedGen`).
`s47_corrector`: for `J > d/2 + 2`, `a, β, γ` in compact positive intervals, `ρ` the thermal density or a compact relative
perturbation `(1+εψ)ρ_*` (`IsStaticReference`) and `φ ∈ C_b^J`: `χ ∈ C²` with `‖∇χ‖, ‖D²χ‖ ≤ C ‖φ‖_{C_b^J}`,
`L_ρ χ ∈ L²(μ)` and `A L_ρ χ = P_μ φ` `μ`-a.e.  No new Poisson theory is used: the generic resolvent representative
(`tc5_resolvent_rep`, hypothesis `TcRef`) and the generic affine Poisson solve (`s48_poisson_deriv`, hypotheses of `GapRef`)
are combined exactly as in `derivative_corrector_proof` (S4.8) with `m = 2`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

noncomputable section

namespace S47

open HRS.Whole
open HRS (Euc cbNorm MemCb)

variable {d : ℕ}

/-- The data of one corrected feature (temperature `γ`, reference `ρ`). -/
structure S47Feat (d : ℕ) (s : ℝ) (ρ : Euc d → ℝ) (γ : ℝ) (φ χ : Euc d → ℝ) (B : ℝ) : Prop where
  smooth : ContDiff ℝ 2 χ
  B1 : ∀ x, ‖gradient χ x‖ ≤ B
  B2 : ∀ x, ‖fderiv ℝ (gradient χ) x‖ ≤ B
  corr : ∀ᵐ x ∂(withDensityReal ρ),
    susceptibilityOp (rieszKernel d s) (withDensityReal ρ) γ (weightedGen ρ χ) x =
      projMean (withDensityReal ρ) φ x
  r2 : MemLp (weightedGen ρ χ) 2 (withDensityReal ρ)

theorem S47Feat.mono {s : ℝ} {ρ : Euc d → ℝ} {γ : ℝ} {φ χ : Euc d → ℝ} {B B' : ℝ}
    (h : S47Feat d s ρ γ φ χ B) (hB : B ≤ B') : S47Feat d s ρ γ φ χ B' :=
  ⟨h.smooth, fun x => (h.B1 x).trans hB, fun x => (h.B2 x).trans hB, h.corr, h.r2⟩

/-- **The corrector at the perturbed reference, uniform over the tilt class** (ED15R): `C` depends on `ε_*` but not on `(ε, ψ)`. -/
theorem s47_corrector_unif (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (J : ℕ)
    (hJ : (d : ℝ) / 2 + 2 < J) (am ap βm βp γm γp : ℝ) (ham : 0 < am) (hβm : 0 < βm) (hγm : 0 < γm)
    (εstar : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a ∈ Set.Icc am ap, ∀ β ∈ Set.Icc βm βp, ∀ γ ∈ Set.Icc γm γp,
      ∀ ρ : Euc d → ℝ, HRS.MS.S48.UnifRef d s a β εstar ρ → ∀ φ : Euc d → ℝ, MemCb J φ →
        ∃ χ : Euc d → ℝ, S47Feat d s ρ γ φ χ (C * cbNorm J φ) := by
  by_cases hint : am ≤ ap ∧ βm ≤ βp
  swap
  · refine ⟨0, le_rfl, fun a ha β hβ => ?_⟩
    exact absurd ⟨ha.1.trans ha.2, hβ.1.trans hβ.2⟩ hint
  obtain ⟨hap, hβp⟩ := hint
  have hd1 : 1 ≤ d := by omega
  have hα : 0 < (d : ℝ) - s := by linarith
  set m : ℕ := 2 with hm
  have hmJ : m ≤ J := by
    have : ((m : ℕ) : ℝ) ≤ J := by
      rw [hm]; push_cast; have : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
      linarith
    exact_mod_cast this
  set M : ℕ := ⌈((m : ℝ) + d / 2) / ((d : ℝ) - s)⌉₊ + 1 with hM
  have hMs : (m : ℝ) + d / 2 < M * ((d : ℝ) - s) := HRS.MS.Tc5.tc5_M_spec hsd m
  set N0 : ℕ := m + ⌈(M : ℝ) * ((d : ℝ) - s) + d⌉₊ + 1 with hN0
  have hmN : m ≤ N0 := by omega
  have hN : (M : ℝ) * ((d : ℝ) - s) + d < N0 := by
    have h1 := Nat.le_ceil ((M : ℝ) * ((d : ℝ) - s) + d)
    have : ((⌈(M : ℝ) * ((d : ℝ) - s) + d⌉₊ : ℕ) : ℝ) + 1 ≤ N0 - m := by
      rw [hN0]; push_cast; ring_nf; linarith
    have h2 : (0 : ℝ) ≤ m := by positivity
    linarith
  have hN0le : N0 + m + 1 ≤ 100 * d + 1001 := by
    have hy : 0 ≤ ((m : ℝ) + d / 2) / ((d : ℝ) - s) := div_nonneg (by positivity) hα.le
    have h1 := Nat.ceil_lt_add_one hy
    have hMlt : (M : ℝ) < ((m : ℝ) + d / 2) / ((d : ℝ) - s) + 2 := by rw [hM]; push_cast; linarith
    have h2 : (M : ℝ) * ((d : ℝ) - s) < ((m : ℝ) + d / 2) + 2 * ((d : ℝ) - s) := by
      calc (M : ℝ) * ((d : ℝ) - s) < (((m : ℝ) + d / 2) / ((d : ℝ) - s) + 2) * ((d : ℝ) - s) :=
            mul_lt_mul_of_pos_right hMlt hα
        _ = ((m : ℝ) + d / 2) + 2 * ((d : ℝ) - s) := by field_simp
    have h3 := Nat.ceil_lt_add_one
      (add_nonneg (mul_nonneg (Nat.cast_nonneg M) hα.le) (Nat.cast_nonneg d) :
        (0 : ℝ) ≤ (M : ℝ) * ((d : ℝ) - s) + d)
    have hcast : ((N0 + m + 1 : ℕ) : ℝ) = 2 * m + (⌈(M : ℝ) * ((d : ℝ) - s) + d⌉₊ : ℝ) + 2 := by
      rw [hN0]; push_cast; ring
    have hm2 : (m : ℝ) = 2 := by rw [hm]; norm_num
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    have : ((N0 + m + 1 : ℕ) : ℝ) ≤ ((100 * d + 1001 : ℕ) : ℝ) := by
      rw [hcast]; push_cast; rw [hm2] at h2 ⊢; linarith
    exact_mod_cast this
  obtain ⟨c, M₀, m₂, hc, hM₀, hpk⟩ := HRS.MS.S48.s48_ref_data_unif hd hs0 hsd ham hβm hap hβp εstar
  obtain ⟨S, Mb, hpkS⟩ := hpk N0 m hN0le
  have hqm : 0 < am * βm := mul_pos ham hβm
  obtain ⟨C5, hC50, hC5⟩ := HRS.MS.Tc5.tc5_resolvent_rep (d := d) hs0 hsd m J M hmJ hMs γp M₀ c S hc N0 hmN hN
  obtain ⟨Cm, hCm0, hCm⟩ := HRS.MS.S48.s48_poisson_deriv hd1 (am * βm) (ap * βp) Mb (3 / 2 * |m₂|) hqm m
    (le_refl 2)
  refine ⟨Cm * C5, by positivity, fun a ha β hβ γ hγ ρ hρ φ hφ => ?_⟩
  have ha0 : 0 < a := ham.trans_le ha.1
  have hβ0 : 0 < β := hβm.trans_le hβ.1
  have hγ0 : 0 < γ := hγm.trans_le hγ.1
  have hqa : am * βm ≤ a * β := mul_le_mul ha.1 hβ.1 hβm.le ha0.le
  have hqb : a * β ≤ ap * βp := mul_le_mul ha.2 hβ.2 hβ0.le (ham.le.trans hap)
  have hp := hpkS a β ha.1 ha.2 hβ.1 hβ.2 ρ hρ
  obtain ⟨B, hR, hcb⟩ := hp.drift
  obtain ⟨r₀, r, hr0, hreq, hr, hrn, hrae⟩ := hC5 ρ hp.ref γ hγ0 hγ.2 φ hφ
  obtain ⟨hprob, hint2, hmom⟩ := HRS.MS.Gap.gap_moment hR
  set μ := withDensityReal ρ with hμ
  have hrint : ∫ x, r x ∂μ = 0 := (integral_congr_ae hrae).trans hr0.2
  have hrder : ∀ j : ℕ, 1 ≤ j → j ≤ m → ∀ x, ‖iteratedFDeriv ℝ j r x‖ ≤ cbNorm m r := fun j _ hj x =>
    HRS.MS.UniqF.uniqf_norm_le_cbNorm hr hj x
  obtain ⟨χ, hχcd, hχi, hχ0, hχeq, hχder⟩ := hCm (a * β) ⟨hqa, hqb⟩ B hcb μ
    (HRS.MS.Gap.gap_invariant hR) hint2 (by
      rw [hmom]
      calc ∫ x, ‖x‖ ^ 2 * ρ x ≤ m₂ := hp.moment
        _ ≤ 3 / 2 * |m₂| := by linarith [le_abs_self m₂, abs_nonneg m₂]) r hr.1 (cbNorm m r) hrder hrint
  have hCb0 : 0 ≤ cbNorm m r := Finset.sum_nonneg fun j _ => Real.iSup_nonneg fun _ => norm_nonneg _
  have hbd : Cm * cbNorm m r ≤ Cm * C5 * cbNorm J φ := by
    calc Cm * cbNorm m r ≤ Cm * (C5 * cbNorm J φ) := mul_le_mul_of_nonneg_left hrn hCm0
      _ = Cm * C5 * cbNorm J φ := by ring
  have hgen : ∀ x, weightedGen ρ χ x = r x := fun x => by
    have hgl := HRS.MS.Gap.gap_gradient_log hR x
    show -Laplacian.laplacian χ x - inner ℝ (gradient (fun y => Real.log (ρ y)) x) (gradient χ x) = r x
    rw [hgl]
    have := hχeq x
    unfold poissonOp at this
    exact this
  have hgenf : weightedGen ρ χ = r := funext hgen
  refine ⟨χ, hχcd, fun x => ?_, fun x => ?_, ?_, ?_⟩
  · rw [S45.s45_norm_gradient, ← norm_iteratedFDeriv_one]
    exact (hχder 1 le_rfl (by omega) x).trans hbd
  · rw [← norm_iteratedFDeriv_one, HRS.MS.Gap.gap1_norm_iter_gradient]
    exact (hχder 2 (by omega) le_rfl x).trans hbd
  · rw [hgenf]
    filter_upwards [hreq, hrae] with x h1 h2
    unfold susceptibilityOp
    rw [HRS.MS.S98.s98_kop_congr_ae hrae, h2]
    have : γ ≠ 0 := hγ0.ne'
    have h3 : r₀ x + γ * Kop (rieszKernel d s) μ r₀ x = γ * projMean μ φ x := h1
    calc γ⁻¹ * r₀ x + Kop (rieszKernel d s) μ r₀ x = γ⁻¹ * (r₀ x + γ * Kop (rieszKernel d s) μ r₀ x) := by
          field_simp
      _ = _ := by rw [h3]; field_simp; rfl
  · rw [hgenf]
    exact HRS.MS.Tc5.tc5_memLp_of_cb hr

/-- **The corrector at the perturbed reference** (fixed `ψ`; a corollary of `s47_corrector_unif`). -/
theorem s47_corrector (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (J : ℕ)
    (hJ : (d : ℝ) / 2 + 2 < J) (am ap βm βp γm γp : ℝ) (ham : 0 < am) (hβm : 0 < βm) (hγm : 0 < γm)
    (ψ : Euc d → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a ∈ Set.Icc am ap, ∀ β ∈ Set.Icc βm βp, ∀ γ ∈ Set.Icc γm γp,
      ∀ ρ : Euc d → ℝ, IsStaticReference d s a β ψ ρ → ∀ φ : Euc d → ℝ, MemCb J φ →
        ∃ χ : Euc d → ℝ, S47Feat d s ρ γ φ χ (C * cbNorm J φ) := by
  obtain ⟨εstar, hε⟩ := HRS.MS.S48.s48_static_to_unif (d := d) ψ
  obtain ⟨C, hC0, h⟩ := s47_corrector_unif hd hs0 hsd J hJ am ap βm βp γm γp ham hβm hγm εstar
  exact ⟨C, hC0, fun a ha β hβ γ hγ ρ hρ φ hφ => h a ha β hβ γ hγ ρ (hε s a β ρ hρ) φ hφ⟩

end S47

end
