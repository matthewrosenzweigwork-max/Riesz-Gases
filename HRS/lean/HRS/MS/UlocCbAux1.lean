import HRS.MP.RdGenSob

/-!
# MS-ULOC-CB, part 1: local Sobolev embedding for non-smooth `f ∈ H^q(ℝ^d)`

Fourier inversion without continuity (`ucb_inversion`: `𝓕 (f̂(-·)) = f` a.e.), and the continuous
`C^j` representative with uniform derivative bounds (`ucb_local_embedding`).
-/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform SchwartzMap

namespace HRS.MS.UlocCb
open HRS HRS.Whole HRS.PDE HRS.PDE.ToolboxRd HRS.MP.RdGen

variable {d : ℕ}

/-- `rg_inversion` without continuity of `φ`: a.e. equality. -/
lemma ucb_inversion {φ : Euc d → ℝ} (hφ : MemLp φ 2 volume)
    (hF1 : Integrable (fun ξ : Euc d => fourierL2 φ (-ξ))) :
    (𝓕 (fun ξ : Euc d => fourierL2 φ (-ξ))) =ᵐ[volume] fun x => ((φ x : ℝ) : ℂ) := by
  set F' : Euc d → ℂ := fun ξ => fourierL2 φ (-ξ) with hF'
  set ψ : Euc d → ℂ := 𝓕 F' with hψ
  have hψc : Continuous ψ :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar continuous_inner hF1
  have hφl : MemLp (fun x => ((φ x : ℝ) : ℂ)) 2 volume := hφ.ofReal
  have hψloc : LocallyIntegrable ψ volume := hψc.locallyIntegrable
  have hφloc : LocallyIntegrable (fun x => ((φ x : ℝ) : ℂ)) volume :=
    hφl.locallyIntegrable (by norm_num)
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

/-- Local embedding: a function in `H^q`, `j + d/2 < q`, has a `C^j` representative with
uniformly bounded derivatives (by a constant times the `H^q` norm). -/
theorem ucb_local_embedding (j : ℕ) {q : ℝ} (hq : (j : ℝ) + d / 2 < q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : Euc d → ℝ, ToolboxRd.MemSobolev q f →
      ∃ g : Euc d → ℝ, g =ᵐ[volume] f ∧ ContDiff ℝ j g ∧
        ∀ i ≤ j, ∀ x, ‖iteratedFDeriv ℝ i g x‖ ≤ C * Real.sqrt (ToolboxRd.sobolevNormSq q f) := by
  have hex : ∀ i : Fin (j + 1), ∃ Ci : ℝ, 0 ≤ Ci ∧ ∀ u : Euc d → ℝ, ToolboxRd.MemSobolev q u →
      Integrable (fun ξ : Euc d => ‖ξ‖ ^ (i : ℕ) * ‖fourierL2 u ξ‖) ∧
      ∫ ξ, ‖ξ‖ ^ (i : ℕ) * ‖fourierL2 u ξ‖ ≤ Ci * Real.sqrt (ToolboxRd.sobolevNormSq q u) := by
    intro i
    have : ((i : ℕ) : ℝ) + d / 2 < q := by
      have : ((i : ℕ) : ℝ) ≤ j := by exact_mod_cast Nat.lt_succ_iff.mp i.2
      linarith
    exact rg_moment_bound (d := d) (i : ℕ) this
  choose Cf hCf0 hCf using hex
  refine ⟨∑ i : Fin (j + 1), (2 * Real.pi) ^ (i : ℕ) * Cf i,
    Finset.sum_nonneg fun i _ => mul_nonneg (by positivity) (hCf0 i), fun f hf => ?_⟩
  have hFm := FourierAux.aestronglyMeasurable_fourierL2 hf.1
  have hmom : ∀ n : ℕ, n ≤ j → Integrable (fun ξ : Euc d => ‖ξ‖ ^ n * ‖fourierL2 f ξ‖) := by
    intro n hn
    exact (hCf ⟨n, Nat.lt_succ_of_le hn⟩ f hf).1
  set F' : Euc d → ℂ := fun ξ => fourierL2 f (-ξ) with hF'
  have hF'm : AEStronglyMeasurable F' volume :=
    hFm.comp_quasiMeasurePreserving
      (Measure.measurePreserving_neg (volume : Measure (Euc d))).quasiMeasurePreserving
  have hF'int : ∀ n : ℕ, n ≤ j → Integrable (fun ξ : Euc d => ‖ξ‖ ^ n * ‖F' ξ‖) := by
    intro n hn
    have := (hmom n hn).comp_neg
    refine this.congr (Eventually.of_forall fun ξ => ?_)
    simp [hF']
  have hF1 : Integrable F' := by
    have := hF'int 0 (Nat.zero_le _)
    simp only [pow_zero, one_mul] at this
    exact (integrable_norm_iff hF'm).1 this
  have hae := ucb_inversion hf.1 hF1
  have hcd : ContDiff ℝ j (𝓕 F') := Real.contDiff_fourier (N := (j : ℕ∞)) (by
    intro n hn; exact hF'int n (by exact_mod_cast hn))
  refine ⟨fun x => (𝓕 F' x).re, ?_, ?_, ?_⟩
  · filter_upwards [hae] with x hx
    have hx' : 𝓕 F' x = ((f x : ℝ) : ℂ) := hx
    show (𝓕 F' x).re = f x
    rw [hx', Complex.ofReal_re]
  · exact Complex.reCLM.contDiff.comp hcd
  · intro i hi x
    have h1 := Complex.reCLM.norm_iteratedFDeriv_comp_left (n := i)
      (f := 𝓕 F') (hcd.contDiffAt (x := x)) (by exact_mod_cast hi)
    rw [Complex.reCLM_norm, one_mul] at h1
    refine h1.trans ?_
    refine (rg_norm_iteratedFDeriv_fourier_le (fun n hn => hF'int n (hn.trans hi)) hF'm x).trans ?_
    have e2 : ∫ v : Euc d, ‖v‖ ^ i * ‖F' v‖ = ∫ v : Euc d, ‖v‖ ^ i * ‖fourierL2 f v‖ := by
      have := integral_neg_eq_self (fun ξ : Euc d => ‖ξ‖ ^ i * ‖fourierL2 f ξ‖)
        (volume : Measure (Euc d))
      rw [← this]
      refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
      simp [hF']
    rw [e2]
    have hb := (hCf ⟨i, Nat.lt_succ_of_le hi⟩ f hf).2
    have hle : (2 * Real.pi) ^ i * Cf ⟨i, Nat.lt_succ_of_le hi⟩ ≤
        ∑ i : Fin (j + 1), (2 * Real.pi) ^ (i : ℕ) * Cf i :=
      Finset.single_le_sum (f := fun i : Fin (j + 1) => (2 * Real.pi) ^ (i : ℕ) * Cf i)
        (fun i _ => mul_nonneg (by positivity) (hCf0 i))
        (Finset.mem_univ (⟨i, Nat.lt_succ_of_le hi⟩ : Fin (j + 1)))
    calc (2 * Real.pi) ^ i * ∫ v : Euc d, ‖v‖ ^ i * ‖fourierL2 f v‖
        ≤ (2 * Real.pi) ^ i * (Cf ⟨i, Nat.lt_succ_of_le hi⟩ * Real.sqrt (ToolboxRd.sobolevNormSq q f)) := by
          gcongr
      _ = ((2 * Real.pi) ^ i * Cf ⟨i, Nat.lt_succ_of_le hi⟩) * Real.sqrt (ToolboxRd.sobolevNormSq q f) := by ring
      _ ≤ _ := by gcongr

end HRS.MS.UlocCb
