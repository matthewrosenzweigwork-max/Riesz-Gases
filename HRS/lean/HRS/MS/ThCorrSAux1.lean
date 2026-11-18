import HRS.MP.RdGenSob
import HRS.MS.QMul

/-!
# TC-S, part 1: continuous representative of `H^q` functions and the `C_b^J` multiplier

Packet TCS (supplement foundation, `docs/TC_PLAN.md` brief TC-S), namespace `HRS.MS.TcS`.

* `tcs_inversion_ae`: for `φ ∈ L²` with `û(-·) ∈ L¹`, the pointwise Fourier integral `𝓕 (û(-·))` agrees
  a.e. with `φ` (the proof of `rg_inversion` without the continuity hypothesis on `φ`).
* `tcs_rep` (statement S3): for `u ∈ H^q(ℝ^d)` and `j + d/2 < q` there is a representative
  `R ∈ C_b^j` with `R =ᵐ u` and `‖R‖_{C_b^j} ≤ C ‖u‖_{H^q}`; `C = C(d, j, q)` only.
  (`rg_sobolev_embedding` needs `ContDiff ℝ ∞ φ`; here only `HRS.PDE.ToolboxRd.MemSobolev q u` is assumed.)
* `tcs_cb_mul`: the finite-valued version of `sobolevNormE_mul_cb_le`:
  `‖φ ρ‖_{H^J} ≤ C ‖φ‖_{C_b^J} ‖ρ‖_{H^J}` for `φ ∈ C_b^J`, `ρ ∈ H^J`.
-/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal ComplexConjugate FourierTransform ContDiff

namespace HRS.MS.TcS
open HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux HRS.MP.RdGen

variable {d : ℕ}

/-- Fourier inversion a.e. for `φ ∈ L²` whose reflected transform is integrable. -/
theorem tcs_inversion_ae {φ : Euc d → ℝ} (hφ : MemLp φ 2 volume)
    (hF1 : Integrable (fun ξ : Euc d => fourierL2 φ (-ξ))) :
    𝓕 (fun ξ : Euc d => fourierL2 φ (-ξ)) =ᵐ[volume] fun x => ((φ x : ℝ) : ℂ) := by
  set F' : Euc d → ℂ := fun ξ => fourierL2 φ (-ξ) with hF'
  set ψ : Euc d → ℂ := 𝓕 F' with hψ
  have hψc : Continuous ψ :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar continuous_inner hF1
  have hφloc : LocallyIntegrable (fun x => ((φ x : ℝ) : ℂ)) volume :=
    (hφ.ofReal (K := ℂ)).locallyIntegrable (by norm_num)
  have hψloc : LocallyIntegrable ψ volume := hψc.locallyIntegrable
  have key : ∀ g : Euc d → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g →
      ∫ x, g x • (ψ x - ((φ x : ℝ) : ℂ)) = 0 := by
    intro g hg hsupp
    have hgC : ContDiff ℝ ∞ (fun x => ((g x : ℝ) : ℂ)) := Complex.ofRealCLM.contDiff.comp hg
    have hsC : HasCompactSupport (fun x => ((g x : ℝ) : ℂ)) :=
      hsupp.comp_left (g := fun t : ℝ => (t : ℂ)) (by simp)
    set s : SchwartzMap (Euc d) ℂ := hsC.toSchwartzMap hgC with hsdef
    have hs : ⇑s = fun x => ((g x : ℝ) : ℂ) := rfl
    set t : SchwartzMap (Euc d) ℂ := 𝓕⁻ s with htdef
    have ht : 𝓕 t = s := FourierInvPair.fourier_fourierInv_eq s
    have htapply : ∀ ξ, t ξ = 𝓕 (⇑s) (-ξ) := by
      intro ξ
      rw [htdef, SchwartzMap.fourierInv_coe, Real.fourierInv_eq_fourier_neg]
    have h1 : ∫ x, g x • ψ x = ∫ ξ, 𝓕 (⇑s) (-ξ) * fourierL2 φ ξ := by
      have hflip : (innerₗ (Euc d)).flip = innerₗ (Euc d) := by
        ext x y
        simp
      have e0 := VectorFourier.integral_fourierIntegral_smul_eq_flip (μ := volume) (ν := volume)
        (L := innerₗ (Euc d)) (f := F') (g := ⇑s)
        Real.continuous_fourierChar continuous_inner hF1 s.integrable
      rw [hflip] at e0
      simp only [smul_eq_mul] at e0
      have e1 : ∫ x, g x • ψ x = ∫ ξ, ψ ξ * s ξ := by
        refine integral_congr_ae (ae_of_all _ fun x => ?_)
        simp only [hs, Complex.real_smul]
        ring
      rw [e1]
      have e2 : (∫ ξ, ψ ξ * s ξ) = ∫ ξ, F' ξ * 𝓕 (⇑s) ξ := e0
      rw [e2]
      have e3 := integral_neg_eq_self (fun ξ : Euc d => F' ξ * 𝓕 (⇑s) ξ) (volume : Measure (Euc d))
      rw [← e3]
      refine integral_congr_ae (ae_of_all _ fun ξ => ?_)
      simp only [hF', neg_neg]
      ring
    have h2 : ∫ x, g x • ((φ x : ℝ) : ℂ) = ∫ ξ, 𝓕 (⇑s) (-ξ) * fourierL2 φ ξ := by
      have e0 := rg_fourierL2_dual hφ t
      rw [ht] at e0
      have e1 : ∫ x, g x • ((φ x : ℝ) : ℂ) = ∫ x, s x * ((φ x : ℝ) : ℂ) := by
        refine integral_congr_ae (ae_of_all _ fun x => ?_)
        simp only [hs, Complex.real_smul]
      rw [e1, ← e0]
      refine integral_congr_ae (ae_of_all _ fun ξ => ?_)
      show t ξ * fourierL2 φ ξ = _
      rw [htapply ξ]
    have hsplit : ∫ x, g x • (ψ x - ((φ x : ℝ) : ℂ)) =
        (∫ x, g x • ψ x) - ∫ x, g x • ((φ x : ℝ) : ℂ) := by
      rw [← integral_sub]
      · simp only [smul_sub]
      · exact Continuous.integrable_of_hasCompactSupport (hg.continuous.smul hψc) hsupp.smul_right
      · exact hφloc.integrable_smul_left_of_hasCompactSupport hg.continuous hsupp
    rw [hsplit, h1, h2, sub_self]
  have hzero := ae_eq_zero_of_integral_contDiff_smul_eq_zero (hψloc.sub hφloc) key
  filter_upwards [hzero] with x hx
  simpa [sub_eq_zero] using hx

theorem tcs_norm_reCLM_le : ‖(Complex.reCLM : ℂ →L[ℝ] ℝ)‖ ≤ 1 := by
  rw [Complex.reCLM_norm]

/-- (S3) Sobolev embedding with a representative: `H^q ⊂ C_b^j` for `j + d/2 < q`, no smoothness
assumption on `u`. The constant depends on `d, j, q` only. -/
theorem tcs_rep (j : ℕ) {q : ℝ} (hq : (j : ℝ) + d / 2 < q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : Euc d → ℝ, HRS.PDE.ToolboxRd.MemSobolev q u →
      ∃ R : Euc d → ℝ, HRS.MemCb j R ∧ R =ᵐ[volume] u ∧
        HRS.cbNorm j R ≤ C * Real.sqrt (sobolevNormSq q u) := by
  have hall : ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ (k ≤ j → ∀ u : Euc d → ℝ, HRS.PDE.ToolboxRd.MemSobolev q u →
      Integrable (fun ξ : Euc d => ‖ξ‖ ^ k * ‖fourierL2 u ξ‖) ∧
      ∫ ξ, ‖ξ‖ ^ k * ‖fourierL2 u ξ‖ ≤ C * Real.sqrt (sobolevNormSq q u)) := by
    intro k
    by_cases hk : k ≤ j
    · have hkq : (k : ℝ) + d / 2 < q := by
        have : (k : ℝ) ≤ j := by exact_mod_cast hk
        linarith
      obtain ⟨C, hC0, hC⟩ := rg_moment_bound (d := d) k hkq
      exact ⟨C, hC0, fun _ u hu => hC u hu⟩
    · exact ⟨0, le_rfl, fun h => absurd h hk⟩
  choose Cf hCf0 hCf using hall
  refine ⟨∑ k ∈ Finset.range (j + 1), (2 * Real.pi) ^ k * Cf k, ?_, fun u hu => ?_⟩
  · exact Finset.sum_nonneg fun k _ => mul_nonneg (by positivity) (hCf0 k)
  have hF := aestronglyMeasurable_fourierL2 hu.1
  have hF'm : AEStronglyMeasurable (fun ξ : Euc d => fourierL2 u (-ξ)) volume :=
    hF.comp_quasiMeasurePreserving
      (Measure.measurePreserving_neg (volume : Measure (Euc d))).quasiMeasurePreserving
  have hF'int : ∀ n : ℕ, n ≤ j →
      Integrable (fun ξ : Euc d => ‖ξ‖ ^ n * ‖fourierL2 u (-ξ)‖) := by
    intro n hn
    have := ((hCf n hn u hu).1).comp_neg
    refine this.congr (Eventually.of_forall fun ξ => ?_)
    simp
  have hF1 : Integrable (fun ξ : Euc d => fourierL2 u (-ξ)) := by
    have := hF'int 0 (Nat.zero_le _)
    simp only [pow_zero, one_mul] at this
    exact (integrable_norm_iff hF'm).1 this
  set R0 : Euc d → ℂ := 𝓕 (fun ξ : Euc d => fourierL2 u (-ξ)) with hR0
  have hR0cd : ContDiff ℝ (j : ℕ∞) R0 :=
    Real.contDiff_fourier (N := (j : ℕ∞)) (fun n hn => hF'int n (by exact_mod_cast hn))
  have hR0cd' : ContDiff ℝ j R0 := by exact_mod_cast hR0cd
  set R : Euc d → ℝ := fun x => (R0 x).re with hRdef
  have hRcomp : R = (Complex.reCLM : ℂ →L[ℝ] ℝ) ∘ R0 := by
    funext x; rfl
  have hRcd : ContDiff ℝ j R := by
    rw [hRcomp]; exact Complex.reCLM.contDiff.comp hR0cd'
  have hbound : ∀ k, k ≤ j → ∀ x, ‖iteratedFDeriv ℝ k R x‖ ≤
      (2 * Real.pi) ^ k * (Cf k * Real.sqrt (sobolevNormSq q u)) := by
    intro k hk x
    have h1 : ‖iteratedFDeriv ℝ k R x‖ ≤ ‖(Complex.reCLM : ℂ →L[ℝ] ℝ)‖ * ‖iteratedFDeriv ℝ k R0 x‖ := by
      rw [hRcomp]
      exact Complex.reCLM.norm_iteratedFDeriv_comp_left (hR0cd'.contDiffAt) (by exact_mod_cast hk)
    have h2 := rg_norm_iteratedFDeriv_fourier_le (f := fun ξ : Euc d => fourierL2 u (-ξ)) (j := k)
      (fun n hn => hF'int n (hn.trans hk)) hF'm x
    have e2 : ∫ v : Euc d, ‖v‖ ^ k * ‖fourierL2 u (-v)‖ = ∫ v : Euc d, ‖v‖ ^ k * ‖fourierL2 u v‖ := by
      have := integral_neg_eq_self (fun ξ : Euc d => ‖ξ‖ ^ k * ‖fourierL2 u ξ‖)
        (volume : Measure (Euc d))
      rw [← this]
      refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
      simp
    rw [e2] at h2
    have h3 := (hCf k hk u hu).2
    calc ‖iteratedFDeriv ℝ k R x‖ ≤ 1 * ‖iteratedFDeriv ℝ k R0 x‖ :=
          h1.trans (by gcongr; exact tcs_norm_reCLM_le)
      _ ≤ (2 * Real.pi) ^ k * ∫ v : Euc d, ‖v‖ ^ k * ‖fourierL2 u v‖ := by rw [one_mul]; exact h2
      _ ≤ _ := by gcongr
  have hMem : HRS.MemCb j R := ⟨hRcd, fun k hk =>
    ⟨(2 * Real.pi) ^ k * (Cf k * Real.sqrt (sobolevNormSq q u)), by
      rintro _ ⟨x, rfl⟩
      exact hbound k hk x⟩⟩
  refine ⟨R, hMem, ?_, ?_⟩
  · filter_upwards [tcs_inversion_ae hu.1 hF1] with x hx
    show (R0 x).re = u x
    rw [hR0, hx]; simp
  · unfold HRS.cbNorm
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun k hk => ?_
    have hk' : k ≤ j := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
    calc (⨆ z : Euc d, ‖iteratedFDeriv ℝ k R z‖)
        ≤ (2 * Real.pi) ^ k * (Cf k * Real.sqrt (sobolevNormSq q u)) :=
          ciSup_le fun x => hbound k hk' x
      _ = _ := by ring

/-- `tcs_cb_mul` (finite-valued form of `sobolevNormE_mul_cb_le`): for `φ ∈ C_b^J` and `ρ ∈ H^J`,
`φ ρ ∈ H^J` and `‖φ ρ‖²_{H^J} ≤ (C ‖φ‖_{C_b^J})² ‖ρ‖²_{H^J}`, `C = C(d, J)`. -/
theorem tcs_cb_mul (J : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ φ : Euc d → ℝ, HRS.MemCb J φ → ∀ ρ : Euc d → ℝ, HRS.PDE.ToolboxRd.MemSobolev (J : ℝ) ρ →
      HRS.PDE.ToolboxRd.MemSobolev (J : ℝ) (fun x => φ x * ρ x) ∧
        sobolevNormSq (J : ℝ) (fun x => φ x * ρ x) ≤
          (C * HRS.cbNorm J φ) ^ 2 * sobolevNormSq (J : ℝ) ρ := by
  obtain ⟨C, hC, h⟩ := HRS.MS.QMul.sobolevNormE_mul_cb_le d J
  refine ⟨C, hC, fun φ hφ ρ hρ => ?_⟩
  have h1 := h φ hφ ρ
  have hE : HRS.Whole.sobolevNormE (J : ℝ) ρ =
      ENNReal.ofReal (Real.sqrt (sobolevNormSq (J : ℝ) ρ)) := by
    unfold HRS.Whole.sobolevNormE; rw [if_pos hρ]
  have hcb : 0 ≤ HRS.cbNorm J φ := by
    unfold HRS.cbNorm
    exact Finset.sum_nonneg fun j _ => Real.iSup_nonneg fun _ => norm_nonneg _
  have hlt : HRS.Whole.sobolevNormE (J : ℝ) (fun x => φ x * ρ x) < ⊤ := by
    refine lt_of_le_of_lt h1 ?_
    rw [hE]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  have hmem : HRS.PDE.ToolboxRd.MemSobolev (J : ℝ) (fun x => φ x * ρ x) := by
    by_contra hn
    have : HRS.Whole.sobolevNormE (J : ℝ) (fun x => φ x * ρ x) = ⊤ := by
      unfold HRS.Whole.sobolevNormE; rw [if_neg hn]
    rw [this] at hlt
    exact lt_irrefl _ hlt
  refine ⟨hmem, ?_⟩
  have hE2 : HRS.Whole.sobolevNormE (J : ℝ) (fun x => φ x * ρ x) =
      ENNReal.ofReal (Real.sqrt (sobolevNormSq (J : ℝ) (fun x => φ x * ρ x))) := by
    unfold HRS.Whole.sobolevNormE; rw [if_pos hmem]
  rw [hE2, hE, ← ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at h1
  have hnn : ∀ w : Euc d → ℝ, 0 ≤ sobolevNormSq (J : ℝ) w := fun w => by
    unfold sobolevNormSq
    exact integral_nonneg fun ξ => by
      have := wt_pos (d := d) ξ
      unfold wt at this
      positivity
  calc sobolevNormSq (J : ℝ) (fun x => φ x * ρ x)
      = Real.sqrt (sobolevNormSq (J : ℝ) (fun x => φ x * ρ x)) ^ 2 :=
        (Real.sq_sqrt (hnn _)).symm
    _ ≤ (C * HRS.cbNorm J φ * Real.sqrt (sobolevNormSq (J : ℝ) ρ)) ^ 2 :=
        pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
    _ = (C * HRS.cbNorm J φ) ^ 2 * sobolevNormSq (J : ℝ) ρ := by
        rw [mul_pow, Real.sq_sqrt (hnn _)]

end HRS.MS.TcS
