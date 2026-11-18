import HRS.Main.GFEVAux25

/-!
# Packet GFEVG, part 26: `gf_ev_grad_proof`
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.GF

open HRS HRS.PDE HRS.PDE.ET HRS.Uniform HRS.Uniform.Q54 HRS.Uniform.Q48b

variable {d : ℕ}

theorem gf_ev_grad_proof (b : GeneralBounds d) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ S : GeneralSetup d, S.Within { b with C₀ := S.C₀ } → S.MFHyp →
      S.PosDensityWith b.c → ∀ N : ℕ,
      ∃ EV : EvolData (NegSobolev d (S.γ : ℝ)) (NegSobolev d (S.γ : ℝ)),
        GFEvo S (-1) N (S.γ : ℝ) K EV := by
  classical
  by_cases hex : ∃ S : GeneralSetup d, S.Within { b with C₀ := S.C₀ } ∧ S.MFHyp ∧ S.PosDensityWith b.c
  swap
  · exact ⟨0, le_rfl, fun S hW hM hP => absurd ⟨S, hW, hM, hP⟩ hex⟩
  obtain ⟨S₀, hW₀, -, -⟩ := hex
  have hd2 : 2 ≤ d := S₀.hd
  have hd1 : 1 ≤ d := by omega
  have hs0 : 0 ≤ b.s := by
    have h1 : S₀.s = b.s := hW₀.1
    linarith [S₀.hs0]
  have hsd : b.s < d := by
    have h1 : S₀.s = b.s := hW₀.1
    linarith [S₀.hsd]
  have hγb : 2 * d + 10 < b.γ := by
    have h1 : S₀.γ = b.γ := hW₀.2.2.1
    have := S₀.hγ
    omega
  have hJm : mStar d ≤ b.γ + 2 := by have := gfev_mStar_le d; omega
  have hm : mStar d ≤ b.γ := by have := gfev_mStar_le d; omega
  let R : Regime := if b.s ≤ (d : ℝ) - 2 then Regime.R1 else Regime.R2b b.c
  have hR : ∀ C ν θ : ℝ, R.lambdaM C ν θ = C := by
    intro C ν θ
    by_cases h : b.s ≤ (d : ℝ) - 2 <;> simp [R, h, Regime.lambdaM]
  set VB : ℝ := Torus.cbNorm (b.γ + 2 * d + 12) b.V with hVB
  obtain ⟨Cs, hCs0, hCsq⟩ := gfev_quasi_levels hd1 b.s hs0 hsd (b.γ + 2) hJm R hR 1 b.Λ VB
  obtain ⟨C', Cs', -, hCs'0, hmain'⟩ := adjoint_torus_classical hd1 b.s hs0 hsd b.γ hm R 1 b.Λ VB
  refine ⟨2 * |Cs b.γ| + 1 + Real.exp (|Cs' b.γ| * b.T), by positivity, fun S hW hMF hPos N => ?_⟩
  obtain ⟨hs, hT, hγ, hΛ, -, -, hV⟩ := hW
  have hs' : S.s = b.s := hs
  have hγ' : S.γ = b.γ := hγ
  have hΛ' : S.Λ = b.Λ := hΛ
  have hV' : S.V = b.V := hV
  obtain ⟨hMFN, hReg⟩ := hMF N
  have hγS : 2 * d + 10 < S.γ := S.hγ
  set D : DynData d := S.dynM (-1) N with hD
  set ρ : ℝ → Torus d → ℝ := S.ρ N with hρdef
  have hreg : ∀ T' : ℝ, 0 < T' → R.Holds d S.s D.M D.invβ 0 T' (gfevMu S.T ρ) := by
    intro T' hT'
    by_cases hb : b.s ≤ (d : ℝ) - 2
    · have e : R = Regime.R1 := if_pos hb
      rw [e]
      show S.s ≤ (d : ℝ) - 2
      rw [hs']; exact hb
    · have e : R = Regime.R2b b.c := if_neg hb
      rw [e]
      refine ⟨by rw [hs']; linarith [not_le.1 hb], gfev_symNonpos_neg_one, hPos.1, fun r hr x => ?_⟩
      exact hPos.2 N _ (gfevClamp_mem S.hT.le r) x
  have h : GFPde d S.s S.γ R VB S.Λ D S.T ρ :=
    { hd := hd1, hs0 := S.hs0, hsd := S.hsd, hγ5 := by omega, hm := by have := gfev_mStar_le d; omega,
      hT := S.hT, hDs := rfl, hDM := rfl,
      hV := ⟨S.V_reg, by
        show Torus.cbNorm (S.γ + 2 * d + 12) S.V ≤ VB
        rw [hγ', hV']⟩,
      hρ := fun r hr => ⟨hMFN.density r hr, (hReg r hr).1, (hReg r hr).2⟩,
      hweak := gfb2_weak S (-1) hMF N,
      hreg := hreg }
  have hμ : ∀ r ∈ Set.Icc (0 : ℝ) S.T, gfevMu S.T ρ r = ρ r := fun r hr => gfevMu_of_mem hr
  have hA : ∀ T' : ℝ, 0 < T' → AdjointData b.s (b.γ + 2) R 1 b.Λ VB D 0 T' (gfevMu S.T ρ) := by
    intro T' hT'
    have := h.adjointData (m := S.γ + 2) (by omega) hT'
    rw [hs', hγ', hΛ'] at this
    exact this
  have hq := hCsq D 0 (gfevMu S.T ρ) hA
  have hγ2 : 2 ≤ b.γ := by omega
  have hq0 : QuasiAt (S.γ + 2) (UpF D (gfevMu S.T ρ)) (S.γ : ℝ) (Cs b.γ) := by
    have := hq b.γ (by omega) (by omega)
    rw [hγ']; exact this
  have hq2 : QuasiAt (S.γ + 2) (UpF D (gfevMu S.T ρ)) ((S.γ : ℝ) - 2) (Cs (b.γ - 2)) := by
    have := hq (b.γ - 2) (by omega) (by omega)
    have e : ((b.γ - 2 : ℕ) : ℝ) = (b.γ : ℝ) - 2 := by rw [Nat.cast_sub hγ2]; norm_num
    rw [e] at this
    rw [hγ']; exact this
  have hq4 : QuasiAt (S.γ + 2) (UpF D (gfevMu S.T ρ)) ((S.γ : ℝ) - 4) (Cs (b.γ - 4)) := by
    have := hq (b.γ - 4) (by omega) (by omega)
    have e : ((b.γ - 4 : ℕ) : ℝ) = (b.γ : ℝ) - 4 := by rw [Nat.cast_sub (by omega)]; norm_num
    rw [e] at this
    rw [hγ']; exact this
  obtain ⟨EV, hEvo, hDiss, hj, hdual⟩ := h.evolData (Cs b.γ) (Cs (b.γ - 2)) (Cs (b.γ - 4)) hq0 hq2 hq4
  have hK : 2 * Cs b.γ ≤ 2 * |Cs b.γ| + 1 + Real.exp (|Cs' b.γ| * b.T) := by
    have := le_abs_self (Cs b.γ)
    have := Real.exp_pos (|Cs' b.γ| * b.T)
    linarith
  refine ⟨EV, ⟨hEvo, Or.inr (hDiss _ hK)⟩, hj, ?_, ?_⟩
  · -- duality with the true propagator
    intro u t hu hut htT z φ hφ
    rw [hdual u t hu hut htT z φ hφ]
    have hJm' : mStar d ≤ S.γ + 2 := by have := gfev_mStar_le d; omega
    have hcore : UpF D (gfevMu S.T ρ) u t φ = propagator D ρ u t φ := by
      by_cases hne : u = t
      · subst hne
        rw [upF_self]
        rw [gfev_propagator_congr htT hμ φ u]
        rcases hu.eq_or_lt with h0 | h0
        · rw [← h0]
          exact (prop_self_zero hd1 S.s S.hs0 S.hsd (S.γ + 2) R 1 S.Λ VB D 0 1 (gfevMu S.T ρ)
            (h.adjointData (m := S.γ + 2) (by omega) one_pos) hφ).symm
        · exact (prop_self_pos hd1 S.s S.hs0 S.hsd (S.γ + 2) hJm' R 1 S.Λ VB D 0 u (gfevMu S.T ρ)
            (h.adjointData (m := S.γ + 2) (by omega) h0) ⟨h0, le_rfl⟩ (dom_smooth hφ)).symm
      · rw [upF_of_ne D _ hne, gfev_propagator_congr htT hμ φ u]
    rw [hcore]
  · -- the adjoint bound
    intro r t hr hrt htT φ hφ2 hφM
    have hφc : Continuous φ := Torus.continuous_of_continuous_lift hφ2.continuous
    have hKge : Real.exp (|Cs' b.γ| * b.T) ≤ 2 * |Cs b.γ| + 1 + Real.exp (|Cs' b.γ| * b.T) := by
      have := abs_nonneg (Cs b.γ); linarith
    have hK1 : 1 ≤ 2 * |Cs b.γ| + 1 + Real.exp (|Cs' b.γ| * b.T) := by
      have := abs_nonneg (Cs b.γ); have := Real.exp_pos (|Cs' b.γ| * b.T); linarith
    by_cases ht0 : t = 0
    · have hr0 : r = 0 := le_antisymm (ht0 ▸ hrt) hr
      subst ht0 hr0
      have hK' : ClassicalAux.ConvKernelFacts d D.s := ClassicalAux.convKernelFacts hd1 D
      have hV1 : Torus.IsCk 1 D.V := ET.isCk_mono' (by omega : 1 ≤ S.γ + 2 * d + 12) S.V_reg
      have hρ1 : Torus.IsCk 1 (ρ 0) :=
        ET.isCk_mono' (by omega : 1 ≤ S.γ + 2 * d + 12) (hReg 0 ⟨le_rfl, S.hT.le⟩).1
      refine ⟨⟨fun _ => φ, MFSemigroup.isClassical_zero D hK' hV1 ρ hρ1 hφ2⟩, ?_, ?_⟩
      · rw [MFSemigroup.propagator_zero D hK' hV1 ρ hρ1 hφ2]; exact hφM
      · rw [MFSemigroup.propagator_zero D hK' hV1 ρ hρ1 hφ2]
        exact le_mul_of_one_le_left (Real.sqrt_nonneg _) hK1
    · have ht : 0 < t := lt_of_le_of_ne (hr.trans hrt) (Ne.symm ht0)
      have hA1 : AdjointData b.s b.γ R 1 b.Λ VB D 0 t (gfevMu S.T ρ) := by
        have := h.adjointData (m := S.γ) (by omega) ht
        rw [hs', hγ', hΛ'] at this
        exact this
      have hφM' : MemSobolev (b.γ : ℝ) φ := by rw [← hγ']; exact hφM
      obtain ⟨hcl, -, h3, -⟩ := hmain' D 0 t (gfevMu S.T ρ) hA1 t ⟨ht, le_rfl⟩ φ hφc hφM'
      have hcongr := gfev_propagator_congr (D := D) (ρ := ρ) (μ' := gfevMu S.T ρ) htT hμ φ r
      obtain ⟨f, hf⟩ : ∃ f, IsClassicalAdjointSolution D (gfevMu S.T ρ) t φ f := ⟨_, hcl⟩
      refine ⟨⟨f, ?_⟩, ?_, ?_⟩
      · rw [gfev_classical_congr htT hμ φ]; exact hf
      · obtain ⟨hm1, -⟩ := h3 b.γ (by omega) le_rfl r ⟨hr, hrt⟩
        rw [hcongr, hγ']; exact hm1
      · obtain ⟨-, hb1⟩ := h3 b.γ (by omega) le_rfl r ⟨hr, hrt⟩
        rw [hR] at hb1
        rw [hcongr, hγ']
        refine hb1.trans (mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _))
        refine le_trans ?_ hKge
        refine Real.exp_le_exp.2 ?_
        calc Cs' b.γ * (t - r) ≤ |Cs' b.γ| * (t - r) :=
              mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith)
          _ ≤ |Cs' b.γ| * b.T := by
              refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
              have : S.T = b.T := hT
              linarith

example := (@gf_ev_grad_proof : type_of% @HRS.GF.gf_ev_grad)

end HRS.GF
