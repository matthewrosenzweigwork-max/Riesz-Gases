import HRS.Main.GFEVMAux6
import HRS.Uniform.Q54cAux56

/-!
# Packet GFEVM, part 7: the generator in the setting of `GeneralSetup`: coefficient hypotheses, dual hypotheses, continuity in time
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.GF

open HRS HRS.PDE HRS.PDE.ET HRS.Uniform HRS.Uniform.Q54 HRS.Uniform.Q48b

variable {d : ℕ}

/-- Increments of the generator in the density path (Lipschitz in `C^{m+2}`; cf. `GFPde.generatorOp_cont`). -/
theorem gfm_bg_diff (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) (MB Λ : ℝ) :
    ∃ Kd : ℝ, 0 ≤ Kd ∧ ∀ (D : DynData d), D.s = s → MatBound MB D.M → Torus.IsCk 1 D.V →
      ∀ (K Bμ BV : ℝ), 0 ≤ MB → 0 ≤ Bμ → 0 ≤ BV → (d : ℝ) / 2 + 1 < K → (d : ℝ) + |(m : ℝ)| + 4 ≤ K →
      ∀ ρ₁ ρ₂ : Torus d → ℝ, IsProbDensity ρ₁ → IsProbDensity ρ₂ →
        Torus.IsCk ((m + 3 : ℕ) : WithTop ℕ∞) ρ₁ → Torus.IsCk ((m + 3 : ℕ) : WithTop ℕ∞) ρ₂ →
        Torus.cbNorm (m + 3) ρ₁ ≤ Λ → Torus.cbNorm (m + 3) ρ₂ ≤ Λ →
        GenHyp d s K MB Bμ BV D ρ₁ → GenHyp d s K MB Bμ BV D ρ₂ →
        ∀ φ : Torus d → ℝ, gfmCls ((m : ℝ) + 2) φ →
          MemSobolev (m : ℝ) (fun x => backwardGenerator D ρ₁ φ x - backwardGenerator D ρ₂ φ x) ∧
            sobolevNorm (m : ℝ) (fun x => backwardGenerator D ρ₁ φ x - backwardGenerator D ρ₂ φ x) ≤
              Kd * Torus.cbNorm (m + 2) (fun x => ρ₁ x - ρ₂ x) * sobolevNorm ((m : ℝ) + 2) φ := by
  obtain ⟨Kd, hKd0, hKd⟩ := StabAux.forwardGen_diff_bound hd s hs0 hsd m MB Λ
  refine ⟨Kd, hKd0, fun D hDs hMBd hV1 K Bμ BV hMB hBμ hBV hK1 hKa ρ₁ ρ₂ hp₁ hp₂ h₁ h₂ hΛ₁ hΛ₂ hG₁ hG₂ φ hφ => ?_⟩
  set δ : ℝ := Torus.cbNorm (m + 2) (fun x => ρ₁ x - ρ₂ x) with hδ
  have hδ0 : 0 ≤ δ := R2Aux.cbNorm_nonneg' _ _
  have hρ11 : Torus.IsCk 1 ρ₁ :=
    ClassicalAux.isCk_of_le (by exact_mod_cast (show 1 ≤ m + 3 by omega)) h₁
  have hρ12 : Torus.IsCk 1 ρ₂ :=
    ClassicalAux.isCk_of_le (by exact_mod_cast (show 1 ≤ m + 3 by omega)) h₂
  obtain ⟨h0₁, hdr₁⟩ := genHyp_memHs0 hsd hG₁ hK1 hMB hBμ hBV
  obtain ⟨h0₂, hdr₂⟩ := genHyp_memHs0 hsd hG₂ hK1 hMB hBμ hBV
  have hm1 : (1 : ℝ) ≤ (m : ℝ) + 2 := by
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  obtain ⟨hc1, hco1, -⟩ := gfm_bg_facts D hd hsd (m : ℝ) hm1 hMB hBμ hBV hKa hρ11 hV1 hG₁ hφ
  obtain ⟨hc2, hco2, -⟩ := gfm_bg_facts D hd hsd (m : ℝ) hm1 hMB hBμ hBV hKa hρ12 hV1 hG₂ hφ
  have hcφ : MemHs ((m : ℝ) + 2) (coeffOf φ) := (hsNormSq_coeffOf _ φ hφ.2).1
  obtain ⟨hmem, hnorm⟩ := hKd D D hDs hDs rfl hMBd rfl ρ₁ ρ₂ hp₁ hp₂ h₁ h₂ hΛ₁ hΛ₂ h0₁ h0₂ hdr₁ hdr₂
    δ le_rfl (coeffOf φ) hcφ
  simp only [sub_self, abs_zero, zero_add] at hnorm
  have hdc : Continuous (fun x => backwardGenerator D ρ₁ φ x - backwardGenerator D ρ₂ φ x) := hco1.sub hco2
  have hcoef : coeffOf (fun x => backwardGenerator D ρ₁ φ x - backwardGenerator D ρ₂ φ x) =
      forwardGen D ρ₁ (coeffOf φ) - forwardGen D ρ₂ (coeffOf φ) := by
    have e : (fun x => backwardGenerator D ρ₁ φ x - backwardGenerator D ρ₂ φ x) =
        fun x => 1 * backwardGenerator D ρ₁ φ x + (-1) * backwardGenerator D ρ₂ φ x := by
      funext x; ring
    rw [e, Q54.coeffOf_lin hco1 hco2 1 (-1), hc1, hc2]
    funext k; simp [sub_eq_add_neg]
  have hmemS : MemSobolev (m : ℝ) (fun x => backwardGenerator D ρ₁ φ x - backwardGenerator D ρ₂ φ x) :=
    memSobolev_of_memHs _ _ (ClassicalAux.memLp_two_of_continuous hdc) (by rw [hcoef]; exact hmem)
  refine ⟨hmemS, ?_⟩
  have e1 := (hsNormSq_coeffOf (m : ℝ) _ hmemS).2
  rw [hcoef] at e1
  obtain ⟨-, hcφ2⟩ := hsNormSq_coeffOf ((m : ℝ) + 2) φ hφ.2
  rw [hcφ2] at hnorm
  have hs0' : 0 ≤ Kd * δ * sobolevNorm ((m : ℝ) + 2) φ :=
    mul_nonneg (mul_nonneg hKd0 hδ0) (Real.sqrt_nonneg _)
  refine le_of_sq_le_sq ?_ hs0'
  rw [← e1]
  calc hsNormSq (m : ℝ) (forwardGen D ρ₁ (coeffOf φ) - forwardGen D ρ₂ (coeffOf φ))
      ≤ (Kd * δ) ^ 2 * sobolevNorm ((m : ℝ) + 2) φ ^ 2 := hnorm
    _ = _ := by ring

section Setup

variable (S : GeneralSetup d) (M : Matrix (Fin d) (Fin d) ℝ) (N : ℕ)

theorem gfm_hd (S : GeneralSetup d) : 1 ≤ d := by have := S.hd; omega

theorem gfm_rho_reg (hMF : S.MFHypM M) {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) S.T) :
    IsProbDensity (S.ρ N r) ∧ Torus.IsCk ((S.γ + 2 * d + 12 : ℕ) : WithTop ℕ∞) (S.ρ N r) ∧
      Torus.cbNorm (S.γ + 2 * d + 12) (S.ρ N r) ≤ S.Λ :=
  ⟨((hMF N).1).density r hr, ((hMF N).2 r hr).1, ((hMF N).2 r hr).2⟩

theorem gfm_V_reg : Torus.IsCk ((S.γ + 2 * d + 12 : ℕ) : WithTop ℕ∞) S.V := S.V_reg

theorem gfm_V1 : Torus.IsCk 1 (S.dynM M N).V := by
  have h1 : (1 : WithTop ℕ∞) ≤ ((S.γ + 2 * d + 12 : ℕ) : WithTop ℕ∞) := by
    exact_mod_cast (show 1 ≤ S.γ + 2 * d + 12 by omega)
  exact ContDiff.of_le S.V_reg h1

theorem gfm_rho1 (hMF : S.MFHypM M) {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) S.T) : Torus.IsCk 1 (S.ρ N r) := by
  have h1 : (1 : WithTop ℕ∞) ≤ ((S.γ + 2 * d + 12 : ℕ) : WithTop ℕ∞) := by
    exact_mod_cast (show 1 ≤ S.γ + 2 * d + 12 by omega)
  exact ContDiff.of_le (gfm_rho_reg S M N hMF hr).2.1 h1

theorem gfm_weak (hMF : S.MFHypM M) :
    ∀ ψ : Torus d → ℝ, Continuous ψ → ContinuousOn (fun t => ∫ x, ψ x * S.ρ N t x) (Set.Icc 0 S.T) := by
  obtain ⟨hMFN, hReg⟩ := hMF N
  have hK : d + 1 ≤ S.γ + 2 * d + 12 := by omega
  exact Q54c.weak_continuity (S.dynM M N) (gfm_hd S) S.T S.Λ S.hT.le (S.γ + 2 * d + 12) hK (S.ρ N) hMFN hReg
    (gfm_V1 S M N)

theorem gfm_genHyp (hMF : S.MFHypM M) :
    ∃ MB Bμ BV : ℝ, 0 ≤ MB ∧ 0 ≤ Bμ ∧ 0 ≤ BV ∧ ∀ r ∈ Set.Icc (0 : ℝ) S.T,
      GenHyp d S.s ((S.γ + 2 * d + 11 : ℕ) : ℝ) MB Bμ BV (S.dynM M N) (S.ρ N r) := by
  set n : ℕ := S.γ + 2 * d + 12 with hn
  set c1 : ℝ := ((1 + 2 * Real.pi) / (2 * Real.pi)) ^ n with hc1
  have hc10 : 0 ≤ c1 := by positivity
  have hΛ0 : 0 ≤ S.Λ := (R2Aux.cbNorm_nonneg' n (S.ρ N 0)).trans
    (gfm_rho_reg S M N hMF ⟨le_rfl, S.hT.le⟩).2.2
  set VB : ℝ := Torus.cbNorm n S.V with hVB
  have hVB0 : 0 ≤ VB := R2Aux.cbNorm_nonneg' n S.V
  set MB : ℝ := ∑ i, ∑ j, |M i j| with hMB
  have hMB0 : 0 ≤ MB := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  refine ⟨MB, S.Λ * c1 + S.Λ, VB * c1 + VB, hMB0, by positivity, by positivity, fun r hr => ⟨rfl, ?_, ?_, ?_⟩⟩
  · intro i j
    show |M i j| ≤ MB
    calc |M i j| ≤ ∑ j', |M i j'| :=
          Finset.single_le_sum (f := fun j' => |M i j'|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
      _ ≤ ∑ i', ∑ j', |M i' j'| :=
          Finset.single_le_sum (f := fun i' => ∑ j', |M i' j'|)
            (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i)
  · intro m
    have hr' := gfm_rho_reg S M N hMF hr
    have := gfev_coeff_decay (S.ρ N r) n S.Λ hr'.2.1 hr'.2.2 m
    refine this.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    exact gfev_jp_rpow_le (a := ((S.γ + 2 * d + 11 : ℕ) : ℝ)) (b := (n : ℝ)) (by rw [hn]; push_cast; linarith) m
  · intro m
    have := gfev_coeff_decay S.V n VB (gfm_V_reg S) le_rfl m
    have e : -(((S.γ + 2 * d + 11 : ℕ) : ℝ) + 1) = -(n : ℝ) := by simp [hn]; ring
    show ‖coeffOf S.V m‖ ≤ (VB * c1 + VB) * Lattice.jp m ^ (-(((S.γ + 2 * d + 11 : ℕ) : ℝ) + 1))
    rw [e]
    exact this

theorem gfm_K_facts : (d : ℝ) / 2 + 1 < ((S.γ + 2 * d + 11 : ℕ) : ℝ) ∧
    (d : ℝ) + |(S.γ : ℝ)| + 4 ≤ ((S.γ + 2 * d + 11 : ℕ) : ℝ) := by
  have h0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hγ : (0 : ℝ) ≤ S.γ := Nat.cast_nonneg _
  push_cast
  rw [abs_of_nonneg hγ]
  constructor <;> linarith

theorem gfm_gen_dual (hMF : S.MFHypM M) {K₀ K : ℝ} (hAI : S.AdjointInput M K₀) (hK : K₀ ≤ K) (hK0 : 0 ≤ K)
    {σ : ℝ} (hσ : σ ∈ Set.Icc (0 : ℝ) S.T) :
    GfDualHyp (gfmCls ((S.γ : ℝ) + 2)) ((S.γ : ℝ) + 2) (S.γ : ℝ)
      (backwardGenerator (S.dynM M N) (S.ρ N σ)) K := by
  obtain ⟨MB, Bμ, BV, hMB, hBμ, hBV, hG⟩ := gfm_genHyp S M N hMF
  obtain ⟨hK1, hKa⟩ := gfm_K_facts S
  have hd := gfm_hd S
  have hγ0 : (0 : ℝ) ≤ S.γ := Nat.cast_nonneg _
  have hm1 : (1 : ℝ) ≤ (S.γ : ℝ) + 2 := by linarith
  have hρ1 := gfm_rho1 S M N hMF hσ
  have hV1 := gfm_V1 S M N
  refine ⟨hK0, fun φ hφ => gfmCls_smooth _ hφ, fun φ hφ => hφ.2, fun φ ψ hφ hψ α β => gfmCls_lin hφ hψ α β,
    fun φ ψ hφ hψ α β => ?_, fun c => gfm_bg_const _ hd hρ1 hV1 c, fun φ hφ => ?_⟩
  · exact gfm_bg_lin (S.dynM M N) hd S.hsd hMB hBμ hBV hK1 hρ1 hV1 (hG σ hσ) hφ.1 hψ.1
      (gfm_memSobolev_mono hφ.2 (by linarith)) (gfm_memSobolev_mono hψ.2 (by linarith)) α β
  · obtain ⟨-, -, hmem⟩ := gfm_bg_facts (S.dynM M N) hd S.hsd (S.γ : ℝ) hm1 hMB hBμ hBV hKa hρ1 hV1 (hG σ hσ) hφ
    refine ⟨hmem, ?_⟩
    have h3 := ((hAI.2 N σ σ hσ.1 le_rfl hσ.2).2 φ hφ.1 hφ.2).2.2
    exact h3.trans (mul_le_mul_of_nonneg_right hK (Real.sqrt_nonneg _))

theorem gfm_gencont (hMF : S.MFHypM M) (σ₀ : ℝ) (hσ₀ : σ₀ ∈ Set.Icc (0 : ℝ) S.T) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ σ : ℝ, 0 ≤ σ → σ ≤ S.T → |σ - σ₀| < δ → ∀ φ : Torus d → ℝ,
      gfmCls ((S.γ : ℝ) + 2) φ →
        MemSobolev (S.γ : ℝ) (fun x => backwardGenerator (S.dynM M N) (S.ρ N σ) φ x -
          backwardGenerator (S.dynM M N) (S.ρ N σ₀) φ x) ∧
        sobolevNorm (S.γ : ℝ) (fun x => backwardGenerator (S.dynM M N) (S.ρ N σ) φ x -
          backwardGenerator (S.dynM M N) (S.ρ N σ₀) φ x) ≤ ε * sobolevNorm ((S.γ : ℝ) + 2) φ := by
  obtain ⟨MB, Bμ, BV, hMB, hBμ, hBV, hG⟩ := gfm_genHyp S M N hMF
  obtain ⟨hK1, hKa⟩ := gfm_K_facts S
  have hd := gfm_hd S
  obtain ⟨Kd, hKd0, hKd⟩ := gfm_bg_diff hd S.s S.hs0 S.hsd S.γ MB S.Λ
  have hMBd : MatBound MB (S.dynM M N).M := (hG σ₀ hσ₀).hM
  set f : ℝ → Torus d → ℝ := gfevMu S.T (S.ρ N) with hf
  have hreg : ∀ t, IsProbDensity (f t) ∧ Torus.IsCk ((S.γ + 2 * d + 12 : ℕ) : WithTop ℕ∞) (f t) ∧
      Torus.cbNorm (S.γ + 2 * d + 12) (f t) ≤ S.Λ :=
    fun t => gfm_rho_reg S M N hMF (gfevClamp_mem S.hT.le t)
  have hc : ∀ ψ : Torus d → ℝ, Continuous ψ → Continuous fun t => ∫ x, ψ x * f t x := by
    intro ψ hψ
    have hco : ContinuousOn ((fun r => ∫ x, ψ x * S.ρ N r x) ∘ gfevClamp S.T) Set.univ :=
      ContinuousOn.comp (g := fun r => ∫ x, ψ x * S.ρ N r x) (s := Set.univ) (gfm_weak S M N hMF ψ hψ)
        (continuous_gfevClamp S.T).continuousOn (fun r _ => gfevClamp_mem S.hT.le r)
    exact continuousOn_univ.1 hco
  have hcb : Tendsto (fun t => Torus.cbNorm (S.γ + 2) (fun x => f t x - f σ₀ x)) (𝓝 σ₀) (𝓝 0) :=
    gfev_cb_tendsto (f := f) (n := S.γ + 2 * d + 12) (j := S.γ + 2) (Λ := S.Λ) (c₀ := 1) hd (by omega)
      (fun t => (hreg t).2.1) (fun t => (hreg t).2.2) (fun t => (hreg t).1.integral_one) hc σ₀
  have hKdc : Tendsto (fun t => Kd * Torus.cbNorm (S.γ + 2) (fun x => f t x - f σ₀ x)) (𝓝 σ₀) (𝓝 0) := by
    simpa using hcb.const_mul Kd
  obtain ⟨δ, hδ, hδ'⟩ := Metric.eventually_nhds_iff.1 (hKdc.eventually (gt_mem_nhds hε))
  refine ⟨δ, hδ, fun σ hσ0 hσT hσδ φ hφ => ?_⟩
  have hσ : σ ∈ Set.Icc (0 : ℝ) S.T := ⟨hσ0, hσT⟩
  have hlt := hδ' (show dist σ σ₀ < δ by rwa [Real.dist_eq])
  have e1 : f σ = S.ρ N σ := gfevMu_of_mem hσ
  have e2 : f σ₀ = S.ρ N σ₀ := gfevMu_of_mem hσ₀
  have hle : S.γ + 3 ≤ S.γ + 2 * d + 12 := by omega
  have hr1 := gfm_rho_reg S M N hMF hσ
  have hr2 := gfm_rho_reg S M N hMF hσ₀
  obtain ⟨hm, hn⟩ := hKd (S.dynM M N) rfl hMBd (gfm_V1 S M N) _ Bμ BV hMB hBμ hBV hK1 hKa (S.ρ N σ) (S.ρ N σ₀)
    hr1.1 hr2.1 (ET.isCk_mono' hle hr1.2.1) (ET.isCk_mono' hle hr2.2.1)
    ((ET.cbNorm_mono' hle _).trans hr1.2.2) ((ET.cbNorm_mono' hle _).trans hr2.2.2)
    (hG σ hσ) (hG σ₀ hσ₀) φ hφ
  refine ⟨hm, hn.trans ?_⟩
  have e3 : (fun x => f σ x - f σ₀ x) = fun x => S.ρ N σ x - S.ρ N σ₀ x := by rw [e1, e2]
  rw [e3] at hlt
  exact mul_le_mul_of_nonneg_right hlt.le (Real.sqrt_nonneg _)

end Setup

end HRS.GF
