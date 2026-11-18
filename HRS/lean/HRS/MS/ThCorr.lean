import HRS.MS.ThCorrAux1

/-!
# TC-6: the thermal corrector (S4.4, step 10)

`thermal_corrector_proof` and `thermal_corrector_sobolev_proof` have exactly the types of the frozen statements
`HRS.Whole.thermal_corrector` and `HRS.Whole.thermal_corrector_sobolev` (ties in `ThCorrTie.lean`).

Proof structure (`tc6_core`, generic in the data class `P φ` and its norm `nf φ`):
1. `tc6_unif`: uniform thermal data `TcRef`/`TcDrift` (constants before `a, β`), `0 ≤ s < d`;
2. a resolvent hypothesis `hres` (instance: `tc5_resolvent_rep` for `C_b^J`, `tc5_resolvent_rep_sob` for `H^J`):
   `r₀ + γ K r₀ = γ P_μ φ` a.e. with a `C_b^{k+1}` representative `r =ᵐ r₀`, `‖r‖_{C_b^{k+1}} ≤ C5 nf φ`;
3. `tc1_poisson_thermal` (Poisson solve, uniform in `q = a β ∈ [am βm, ap βp]`): `χ` with `thermalGen χ = r`;
4. `tc6_corrector_of_data` (the six conjuncts of `IsThermalCorrector`).
No statement was adjusted.  If an interval is empty (`ap < am` or `βp < βm`) the statement is vacuous (`C = 0`).
-/

open MeasureTheory Set Filter Topology
open scoped ContDiff
open HRS.Whole

noncomputable section

namespace HRS.MS.Tc6

variable {d : ℕ}

/-- the generic assembly. -/
theorem tc6_core (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (k : ℕ) (hk : 1 ≤ k)
    (am ap βm βp γm γp : ℝ) (ham : 0 < am) (hβm : 0 < βm) (hγm : 0 < γm) (P : (Euc d → ℝ) → Prop)
    (nf : (Euc d → ℝ) → ℝ) (hnf : ∀ φ, P φ → 0 ≤ nf φ)
    (hres : ∃ N0 : ℕ, ∀ M₀ c S : ℝ, 0 < c → ∃ C5 : ℝ, 0 ≤ C5 ∧
      ∀ ρ : Euc d → ℝ, HRS.MS.TcDefs.TcRef d ρ M₀ c S N0 → ∀ γ : ℝ, 0 < γ → γ ≤ γp →
        ∀ φ : Euc d → ℝ, P φ →
          ∃ r₀ r : Euc d → ℝ, HRS.Whole.MemL2Zero (HRS.Whole.withDensityReal ρ) r₀ ∧
            (∀ᵐ x ∂(HRS.Whole.withDensityReal ρ),
              r₀ x + γ * HRS.Whole.Kop (rieszKernel d s) (HRS.Whole.withDensityReal ρ) r₀ x =
                γ * HRS.Whole.projMean (HRS.Whole.withDensityReal ρ) φ x) ∧
            HRS.MemCb (k + 1) r ∧ HRS.cbNorm (k + 1) r ≤ C5 * nf φ ∧
            r =ᵐ[HRS.Whole.withDensityReal ρ] r₀) :
    ∃ C : ℝ, ∀ a ∈ Set.Icc am ap, ∀ β ∈ Set.Icc βm βp, ∀ γ ∈ Set.Icc γm γp,
      ∀ φ : Euc d → ℝ, P φ → ∃ χ : Euc d → ℝ, IsThermalCorrector d s a β γ k φ (nf φ) C χ := by
  by_cases hint : am ≤ ap ∧ βm ≤ βp
  swap
  · refine ⟨0, fun a ha β hβ => ?_⟩
    exact absurd ⟨ha.1.trans ha.2, hβ.1.trans hβ.2⟩ hint
  obtain ⟨hap, hβp⟩ := hint
  obtain ⟨N0, hN0⟩ := hres
  obtain ⟨c, M₀, m₂, hc, hM₀, hS, hMb⟩ := tc6_unif hd hs0 hsd ham hβm hap hβp
  obtain ⟨S, hS0, hSρ⟩ := hS N0
  obtain ⟨Mb, hMb0, hMbρ⟩ := hMb (k + 1)
  obtain ⟨C5, hC5, hC5ρ⟩ := hN0 M₀ c S hc
  have hqm : 0 < am * βm := mul_pos ham hβm
  obtain ⟨C, Cm, hP⟩ := HRS.MS.Tc1.tc1_poisson_thermal hd (am * βm) (ap * βp) Mb m₂ hqm (k + 1)
    (by omega)
  refine ⟨|C| * C5 + |Cm| * C5, fun a ha β hβ γ hγ φ hφ => ?_⟩
  have ha0 : 0 < a := ham.trans_le ha.1
  have hβ0 : 0 < β := hβm.trans_le hβ.1
  have hγ0 : 0 < γ := hγm.trans_le hγ.1
  have hqa : am * βm ≤ a * β := mul_le_mul ha.1 hβ.1 hβm.le ha0.le
  have hqb : a * β ≤ ap * βp := mul_le_mul ha.2 hβ.2 hβ0.le (ham.le.trans hap)
  have hρ := hSρ a β ha.1 ha.2 hβ.1 hβ.2
  have hdr := hMbρ a β ha.1 ha.2 hβ.1 hβ.2
  obtain ⟨r₀, r, hr₀, hae, hr, hbd, hrr⟩ := hC5ρ _ hρ γ hγ0 hγ.2 φ hφ
  have hprob : IsProbabilityMeasure (thermalMeasure d s a β) := HRS.MS.TcF.tc4_isProb hρ.prob
  obtain ⟨-, -, hint2, -⟩ := HRS.MS.Tc1.tc1_drift_data hd hs0 hsd ha0 hβ0 hdr
  have hri : Integrable r (thermalMeasure d s a β) :=
    (HRS.MS.Tc5.tc5_memLp_of_cb hr).integrable one_le_two
  have hr0 : ∫ x, r x ∂(thermalMeasure d s a β) = 0 := by
    exact (integral_congr_ae hrr).trans hr₀.2
  obtain ⟨χ, hχc, hχi, hχ0, hgen, hlog, -, hder⟩ := hP s a β hs0 hsd ha0 hβ0 hqa hqb hdr r hr hri hr0
  exact ⟨χ, tc6_corrector_of_data hk (hnf φ hφ) hγ0 hprob hint2 hC5 hr hrr hae hχc hχ0 hgen hlog hder hbd⟩

/-- **S4.4, `C_b^J` version.** -/
theorem thermal_corrector_proof : type_of% @HRS.Whole.thermal_corrector := by
  intro d s hd hs0 hsd k hk J hJ am ap βm βp γm γp ham hβm hγm
  have hα : 0 < (d : ℝ) - s := by linarith
  set m : ℕ := k + 1 with hm
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
    have : ((⌈(M : ℝ) * ((d : ℝ) - s) + d⌉₊ : ℕ) : ℝ) + 1 ≤ N0 := by
      rw [hN0]; push_cast; have : (0 : ℝ) ≤ m := by positivity
      linarith
    linarith
  exact tc6_core hd hs0 hsd k hk am ap βm βp γm γp ham hβm hγm (HRS.MemCb J) (HRS.cbNorm J)
    (fun φ _ => HRS.MS.Tc5.tc5_cb_nonneg J φ)
    ⟨N0, fun M₀ c S hc => HRS.MS.Tc5.tc5_resolvent_rep (d := d) hs0 hsd m J M hmJ hMs γp M₀ c S hc N0 hmN hN
      |>.imp fun C hC => hC⟩

/-- **S4.4, `H^J` version.** -/
theorem thermal_corrector_sobolev_proof : type_of% @HRS.Whole.thermal_corrector_sobolev := by
  intro d s hd hs0 hsd k hk J hJ am ap βm βp γm γp ham hβm hγm
  have hα : 0 < (d : ℝ) - s := by linarith
  set m : ℕ := k + 1 with hm
  have hJm : (m : ℝ) + d / 2 < J := by rw [hm]; push_cast; exact hJ
  set M : ℕ := ⌈((m : ℝ) + d / 2) / ((d : ℝ) - s)⌉₊ + 1 with hM
  have hMs : (m : ℝ) + d / 2 < M * ((d : ℝ) - s) := HRS.MS.Tc5.tc5_M_spec hsd m
  set N0 : ℕ := J + ⌈(M : ℝ) * ((d : ℝ) - s) + d⌉₊ + 1 with hN0
  have hN : (J : ℝ) + M * ((d : ℝ) - s) + d < N0 := by
    have h1 := Nat.le_ceil ((M : ℝ) * ((d : ℝ) - s) + d)
    have : ((⌈(M : ℝ) * ((d : ℝ) - s) + d⌉₊ : ℕ) : ℝ) + 1 + J ≤ N0 := by
      rw [hN0]; push_cast; linarith
    linarith
  obtain ⟨Cs, hCs0, hCs⟩ := HRS.MS.TcS.tcs_sobolevNorm_le_hsmooth d J
  obtain ⟨C1, hC10, hC1⟩ := HRS.MS.TcS.tcs_sobolev_of_hsmooth d J
  have hW : ∀ φ : Euc d → ℝ, 0 ≤ HRS.Whole.sobolevWNorm J 2 φ := fun φ => by
    unfold HRS.Whole.sobolevWNorm
    exact Finset.sum_nonneg fun n _ => Real.rpow_nonneg (integral_nonneg fun x => by positivity) _
  refine tc6_core hd hs0 hsd k hk am ap βm βp γm γp ham hβm hγm (HRS.Whole.MemHSmooth J)
    (HRS.Whole.sobolevWNorm J 2) (fun φ _ => hW φ) ⟨N0, fun M₀ c S hc => ?_⟩
  obtain ⟨C, hC0, hCρ⟩ := HRS.MS.Tc5.tc5_resolvent_rep_sob (d := d) hs0 hsd m J M hJm hMs γp M₀ c S hc N0 hN
  refine ⟨C * Cs, mul_nonneg hC0 hCs0, fun ρ hρ γ hγ hγp φ hφ => ?_⟩
  obtain ⟨r₀, r, h1, h2, h3, h4, h5⟩ := hCρ ρ hρ γ hγ hγp φ (hC1 φ hφ).1
  refine ⟨r₀, r, h1, h2, h3, ?_, h5⟩
  have hs : Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq (J : ℝ) φ) ≤ Cs * HRS.Whole.sobolevWNorm J 2 φ :=
    hCs φ hφ
  calc HRS.cbNorm m r ≤ C * Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq (J : ℝ) φ) := h4
    _ ≤ C * (Cs * HRS.Whole.sobolevWNorm J 2 φ) := mul_le_mul_of_nonneg_left hs hC0
    _ = C * Cs * HRS.Whole.sobolevWNorm J 2 φ := by ring

end HRS.MS.Tc6

end
