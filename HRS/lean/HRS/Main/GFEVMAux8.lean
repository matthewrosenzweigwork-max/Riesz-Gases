import HRS.Main.GFEVMAux7

/-!
# Packet GFEVM, part 8: the Duhamel pairing, the hypotheses `GfmAbs` in the setting of `GeneralSetup`, and `gf_ev_mat_proof`
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.GF

open HRS HRS.PDE HRS.PDE.ET HRS.Uniform HRS.Uniform.Q54 HRS.Uniform.Q48b

variable {d : ℕ}

theorem gfm_sol_coeff_incr {D : DynData d} {ρ : ℝ → Torus d → ℝ} {t : ℝ} {φ : Torus d → ℝ}
    {f : ℝ → Torus d → ℝ} (hf : IsClassicalAdjointSolution D ρ t φ f) (k : Lattice d) {u u' : ℝ}
    (hu : 0 ≤ u) (huu' : u ≤ u') (hu't : u' ≤ t) :
    coeffOf (f u) k - coeffOf (f u') k = ∫ s in u..u', coeffOf (backwardGenerator D (ρ s) (f s)) k := by
  rcases huu'.eq_or_lt with rfl | hlt
  · simp
  have hsub : Set.Icc u u' ⊆ Set.Icc 0 t := Set.Icc_subset_Icc hu hu't
  have hcont : ContinuousOn (fun s => coeffOf (f s) k) (Set.Icc u u') :=
    (ClassicalAux.continuousOn_coeff hf k).mono hsub
  have hint : IntervalIntegrable (fun s => -(coeffOf (backwardGenerator D (ρ s) (f s)) k)) volume u u' :=
    (((ClassicalAux.continuousOn_coeff_bg hf k).mono hsub).neg).intervalIntegrable_of_Icc huu'
  have h := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le huu' hcont
    (fun s hs => (ClassicalAux.hasDerivAt_coeff hf k ⟨hu.trans_lt hs.1, hs.2.trans_le hu't⟩).hasDerivWithinAt)
    hint
  rw [intervalIntegral.integral_neg] at h
  linear_combination h

theorem gfm_up_dualHyp {D : DynData d} {ρ : ℝ → Torus d → ℝ} {T : ℝ} (hU : GfmUniq D ρ T)
    (hbl : ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ u v : Torus d → ℝ, Torus.IsCk 2 u → Torus.IsCk 2 v →
      MemSobolev 1 u → MemSobolev 1 v → ∀ α β : ℝ,
      backwardGenerator D (ρ r) (fun x => α * u x + β * v x) =
        fun x => α * backwardGenerator D (ρ r) u x + β * backwardGenerator D (ρ r) v x)
    (hbc : ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ c : ℝ, backwardGenerator D (ρ r) (fun _ => c) = fun _ => 0)
    {m K₀ K : ℝ} (hK : K₀ ≤ K) (hK0 : 0 ≤ K)
    (hex : ∀ t : ℝ, 0 ≤ t → t ≤ T → ∀ φ : Torus d → ℝ, gfmCls m φ →
      ∃ f, IsClassicalAdjointSolution D ρ t φ f)
    (hbd : ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ T → ∀ φ : Torus d → ℝ, gfmCls m φ →
      MemSobolev m (propagator D ρ r t φ) ∧ sobolevNorm m (propagator D ρ r t φ) ≤ K₀ * sobolevNorm m φ)
    {r t : ℝ} (hr : 0 ≤ r) (hrt : r ≤ t) (htT : t ≤ T) :
    DualHyp (gfmCls m) m (propagator D ρ r t) K := by
  have ht0 : 0 ≤ t := hr.trans hrt
  refine ⟨hK0, fun φ hφ => gfmCls_smooth m hφ, fun φ hφ => hφ.2,
    fun φ ψ hφ hψ α β => gfmCls_lin hφ hψ α β, fun φ ψ hφ hψ α β => ?_, fun c => ?_, fun φ hφ => ?_⟩
  · obtain ⟨f, hf⟩ := hex t ht0 htT φ hφ
    obtain ⟨g, hg⟩ := hex t ht0 htT ψ hψ
    exact gfm_prop_lin hU hbl ht0 htT hf hg α β ⟨hr, hrt⟩
  · exact gfm_prop_const hU hbc ht0 htT c ⟨hr, hrt⟩
  · obtain ⟨h1, h2⟩ := hbd r t hr hrt htT φ hφ
    exact ⟨h1, h2.trans (mul_le_mul_of_nonneg_right hK (Real.sqrt_nonneg _))⟩

theorem gfm_duh {D : DynData d} {ρ : ℝ → Torus d → ℝ} {T : ℝ} (hU : GfmUniq D ρ T) {γ K : ℝ} {t u u' : ℝ}
    (hu : 0 ≤ u) (huu' : u ≤ u') (hu't : u' ≤ t) (htT : t ≤ T) {φ : Torus d → ℝ}
    (hex : ∃ f, IsClassicalAdjointSolution D ρ t φ f)
    (hcE : ∀ σ : ℝ, 0 ≤ σ → σ ≤ t → gfmCls (γ + 2) (propagator D ρ σ t φ))
    (hnorm : ∀ σ : ℝ, 0 ≤ σ → σ ≤ t →
      sobolevNorm (γ + 2) (propagator D ρ σ t φ) ≤ K * sobolevNorm (γ + 2) φ)
    (hgen : ∀ σ : ℝ, 0 ≤ σ → σ ≤ T →
      GfDualHyp (gfmCls (γ + 2)) (γ + 2) γ (backwardGenerator D (ρ σ)) K)
    (z : NegSobolev d γ) :
    NegSobolev.eval z (propagator D ρ u t φ) - NegSobolev.eval z (propagator D ρ u' t φ) =
      ∫ σ in u..u', NegSobolev.eval z (backwardGenerator D (ρ σ) (propagator D ρ σ t φ)) := by
  obtain ⟨f, hf⟩ := hex
  have ht0 : 0 ≤ t := hu.trans (huu'.trans hu't)
  have hpe : ∀ σ ∈ Set.Icc (0 : ℝ) t, propagator D ρ σ t φ = f σ :=
    fun σ hσ => gfm_prop_eq hU ht0 htT hf hσ
  have hu0 : u ∈ Set.Icc (0 : ℝ) t := ⟨hu, huu'.trans hu't⟩
  have hu'0 : u' ∈ Set.Icc (0 : ℝ) t := ⟨hu.trans huu', hu't⟩
  have hcongr : (∫ σ in u..u', NegSobolev.eval z (backwardGenerator D (ρ σ) (propagator D ρ σ t φ))) =
      ∫ σ in u..u', NegSobolev.eval z (backwardGenerator D (ρ σ) (f σ)) := by
    refine intervalIntegral.integral_congr fun σ hσ => ?_
    rw [Set.uIcc_of_le huu'] at hσ
    simp only [hpe σ ⟨hu.trans hσ.1, hσ.2.trans hu't⟩]
  rw [hcongr, hpe u hu0, hpe u' hu'0]
  have hK0 : 0 ≤ K := (hgen u hu (huu'.trans hu't |>.trans htT)).hM
  have hIc : ∀ σ ∈ Set.Icc (0 : ℝ) t, Integrable (backwardGenerator D (ρ σ) (f σ)) := fun σ hσ =>
    ClassicalAux.integrable_of_continuous (ClassicalAux.continuous_bg_apply hf hσ)
  have hsubu : Set.uIcc u u' ⊆ Set.Icc (0 : ℝ) t := by
    rw [Set.uIcc_of_le huu']; exact Set.Icc_subset_Icc hu hu't
  refine gfev_eval_duhamel_abs (m := γ) (f := f) (g := fun σ => backwardGenerator D (ρ σ) (f σ))
    (B := K * (K * sobolevNorm (γ + 2) φ)) huu' ?_ ?_ ?_ ?_ ?_ z
  · have := (hcE u hu (huu'.trans hu't)).2
    rw [hpe u hu0] at this
    exact gfm_memSobolev_mono this (by linarith)
  · have := (hcE u' (hu.trans huu') hu't).2
    rw [hpe u' hu'0] at this
    exact gfm_memSobolev_mono this (by linarith)
  · intro s hs
    have hs0 : 0 ≤ s := hu.trans hs.1
    have hst : s ≤ t := hs.2.trans hu't
    have hc := hcE s hs0 hst
    rw [hpe s ⟨hs0, hst⟩] at hc
    obtain ⟨hm, hn⟩ := (hgen s hs0 (hst.trans htT)).bd _ hc
    refine ⟨hm, hn.trans ?_⟩
    have := hnorm s hs0 hst
    rw [hpe s ⟨hs0, hst⟩] at this
    exact mul_le_mul_of_nonneg_left this hK0
  · intro k
    have hcont : ContinuousOn (fun s => gfevRc k (coeffOf (backwardGenerator D (ρ s) (f s)) k.1))
        (Set.Icc 0 t) :=
      (gfevRc k).continuous.comp_continuousOn (ClassicalAux.continuousOn_coeff_bg hf k.1)
    have h0 : IntervalIntegrable (fun s => gfevRc k (coeffOf (backwardGenerator D (ρ s) (f s)) k.1))
        volume u u' := (hcont.mono hsubu).intervalIntegrable
    refine h0.congr fun s hs => ?_
    rw [Set.uIoc_of_le huu'] at hs
    have hs' : s ∈ Set.Icc (0 : ℝ) t := ⟨hu.trans hs.1.le, hs.2.trans hu't⟩
    exact (gfev_funRealCoeff_eq_rc _ (hIc s hs') k).symm
  · intro k
    rw [gfev_funRealCoeff_eq_rc _ (ClassicalAux.integrable_of_continuous (ClassicalAux.continuous_f_apply hf hu0)) k,
      gfev_funRealCoeff_eq_rc _ (ClassicalAux.integrable_of_continuous (ClassicalAux.continuous_f_apply hf hu'0)) k,
      ← map_sub, gfm_sol_coeff_incr hf k.1 hu huu' hu't]
    have hintc : IntervalIntegrable (fun s => coeffOf (backwardGenerator D (ρ s) (f s)) k.1) volume u u' :=
      ((ClassicalAux.continuousOn_coeff_bg hf k.1).mono hsubu).intervalIntegrable
    rw [← (gfevRc k).intervalIntegral_comp_comm hintc]
    refine intervalIntegral.integral_congr fun s hs => ?_
    exact (gfev_funRealCoeff_eq_rc _ (hIc s (hsubu hs)) k).symm

theorem gfm_abs_setup (S : GeneralSetup d) (M : Matrix (Fin d) (Fin d) ℝ) (K₀ : ℝ) (hMF : S.MFHypM M)
    (hAI : S.AdjointInput M K₀) (N : ℕ) :
    GfmAbs (S.γ : ℝ) S.T (max K₀ 1) (propagator (S.dynM M N) (S.ρ N))
      (fun σ => backwardGenerator (S.dynM M N) (S.ρ N σ)) := by
  have hK1 : 1 ≤ max K₀ 1 := le_max_right _ _
  have hK0 : 0 ≤ max K₀ 1 := by linarith
  have hKK : K₀ ≤ max K₀ 1 := le_max_left _ _
  have hU : GfmUniq (S.dynM M N) (S.ρ N) S.T := hAI.1 N
  have hd := gfm_hd S
  obtain ⟨MB, Bμ, BV, hMB, hBμ, hBV, hG⟩ := gfm_genHyp S M N hMF
  obtain ⟨hK1', hKa⟩ := gfm_K_facts S
  have hγ0 : (0 : ℝ) ≤ S.γ := Nat.cast_nonneg _
  have hbl : ∀ r ∈ Set.Icc (0 : ℝ) S.T, ∀ u v : Torus d → ℝ, Torus.IsCk 2 u → Torus.IsCk 2 v →
      MemSobolev 1 u → MemSobolev 1 v → ∀ α β : ℝ,
      backwardGenerator (S.dynM M N) (S.ρ N r) (fun x => α * u x + β * v x) =
        fun x => α * backwardGenerator (S.dynM M N) (S.ρ N r) u x +
          β * backwardGenerator (S.dynM M N) (S.ρ N r) v x :=
    fun r hr u v hu hv hu1 hv1 α β => gfm_bg_lin (S.dynM M N) hd S.hsd hMB hBμ hBV hK1'
      (gfm_rho1 S M N hMF hr) (gfm_V1 S M N) (hG r hr) hu hv hu1 hv1 α β
  have hbc : ∀ r ∈ Set.Icc (0 : ℝ) S.T, ∀ c : ℝ,
      backwardGenerator (S.dynM M N) (S.ρ N r) (fun _ => c) = fun _ => 0 :=
    fun r hr c => gfm_bg_const (S.dynM M N) hd (gfm_rho1 S M N hMF hr) (gfm_V1 S M N) c
  have hexH : ∀ t : ℝ, 0 ≤ t → t ≤ S.T → ∀ φ : Torus d → ℝ, gfmCls (S.γ : ℝ) φ →
      ∃ f, IsClassicalAdjointSolution (S.dynM M N) (S.ρ N) t φ f :=
    fun t ht0 htT φ hφ => ((hAI.2 N t t ht0 le_rfl htT).1 φ hφ.1 hφ.2).1
  have hexE : ∀ t : ℝ, 0 ≤ t → t ≤ S.T → ∀ φ : Torus d → ℝ, gfmCls ((S.γ : ℝ) + 2) φ →
      ∃ f, IsClassicalAdjointSolution (S.dynM M N) (S.ρ N) t φ f :=
    fun t ht0 htT φ hφ => hexH t ht0 htT φ (gfmCls_mono hφ (by linarith))
  have hbdH : ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ S.T → ∀ φ : Torus d → ℝ, gfmCls (S.γ : ℝ) φ →
      MemSobolev (S.γ : ℝ) (propagator (S.dynM M N) (S.ρ N) r t φ) ∧
        sobolevNorm (S.γ : ℝ) (propagator (S.dynM M N) (S.ρ N) r t φ) ≤ K₀ * sobolevNorm (S.γ : ℝ) φ :=
    fun r t hr hrt htT φ hφ =>
      ⟨((hAI.2 N r t hr hrt htT).1 φ hφ.1 hφ.2).2.1, ((hAI.2 N r t hr hrt htT).1 φ hφ.1 hφ.2).2.2⟩
  have hbdE : ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ S.T → ∀ φ : Torus d → ℝ, gfmCls ((S.γ : ℝ) + 2) φ →
      MemSobolev ((S.γ : ℝ) + 2) (propagator (S.dynM M N) (S.ρ N) r t φ) ∧
        sobolevNorm ((S.γ : ℝ) + 2) (propagator (S.dynM M N) (S.ρ N) r t φ) ≤
          K₀ * sobolevNorm ((S.γ : ℝ) + 2) φ :=
    fun r t hr hrt htT φ hφ =>
      ⟨((hAI.2 N r t hr hrt htT).2 φ hφ.1 hφ.2).1, ((hAI.2 N r t hr hrt htT).2 φ hφ.1 hφ.2).2.1⟩
  have upH : ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ S.T →
      DualHyp (gfmCls (S.γ : ℝ)) (S.γ : ℝ) (propagator (S.dynM M N) (S.ρ N) r t) (max K₀ 1) :=
    fun r t hr hrt htT => gfm_up_dualHyp hU hbl hbc hKK hK0 hexH hbdH hr hrt htT
  have upE : ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ S.T →
      DualHyp (gfmCls ((S.γ : ℝ) + 2)) ((S.γ : ℝ) + 2) (propagator (S.dynM M N) (S.ρ N) r t) (max K₀ 1) :=
    fun r t hr hrt htT => gfm_up_dualHyp hU hbl hbc hKK hK0 hexE hbdE hr hrt htT
  have clsH : ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ S.T → ∀ φ : Torus d → ℝ, gfmCls (S.γ : ℝ) φ →
      gfmCls (S.γ : ℝ) (propagator (S.dynM M N) (S.ρ N) r t φ) := by
    intro r t hr hrt htT φ hφ
    obtain ⟨f, hf⟩ := hexH t (hr.trans hrt) htT φ hφ
    refine ⟨?_, (hbdH r t hr hrt htT φ hφ).1⟩
    rw [gfm_prop_eq hU (hr.trans hrt) htT hf ⟨hr, hrt⟩]
    exact hf.c2 r ⟨hr, hrt⟩
  have clsE : ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ S.T → ∀ φ : Torus d → ℝ, gfmCls ((S.γ : ℝ) + 2) φ →
      gfmCls ((S.γ : ℝ) + 2) (propagator (S.dynM M N) (S.ρ N) r t φ) := by
    intro r t hr hrt htT φ hφ
    obtain ⟨f, hf⟩ := hexE t (hr.trans hrt) htT φ hφ
    refine ⟨?_, (hbdE r t hr hrt htT φ hφ).1⟩
    rw [gfm_prop_eq hU (hr.trans hrt) htT hf ⟨hr, hrt⟩]
    exact hf.c2 r ⟨hr, hrt⟩
  refine ⟨hK1, upH, upE, clsH, clsE, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht0 htT φ hφ
    obtain ⟨f, hf⟩ := hexH t ht0 htT φ hφ
    exact gfm_prop_self hU ht0 htT hf
  · intro t ht0 htT φ hφ
    obtain ⟨f, hf⟩ := hexE t ht0 htT φ hφ
    exact gfm_prop_self hU ht0 htT hf
  · intro s r t hs hsr hrt htT φ hφ
    obtain ⟨f, hf⟩ := hexH t (hs.trans (hsr.trans hrt)) htT φ hφ
    exact gfm_cocycle hU (hs.trans (hsr.trans hrt)) htT hf hs hsr hrt
  · intro s r t hs hsr hrt htT φ hφ
    obtain ⟨f, hf⟩ := hexE t (hs.trans (hsr.trans hrt)) htT φ hφ
    exact gfm_cocycle hU (hs.trans (hsr.trans hrt)) htT hf hs hsr hrt
  · intro σ h0 hT
    exact gfm_gen_dual S M N hMF hAI hKK hK0 ⟨h0, hT⟩
  · intro σ₀ h0 hT ε hε
    exact gfm_gencont S M N hMF σ₀ ⟨h0, hT⟩ ε hε
  · intro t u u' hu huu' hu't htT φ hφ z
    have hφE : gfmCls ((S.γ : ℝ) + 2) φ := gfmCls_smooth _ hφ
    refine gfm_duh (K := max K₀ 1) hU hu huu' hu't htT (hexE t (hu.trans (huu'.trans hu't)) htT φ hφE) ?_ ?_ ?_ z
    · intro σ hσ0 hσt
      exact clsE σ t hσ0 hσt htT φ hφE
    · intro σ hσ0 hσt
      exact (upE σ t hσ0 hσt htT).bd φ hφE |>.2
    · intro σ hσ0 hσT
      exact gfm_gen_dual S M N hMF hAI hKK hK0 ⟨hσ0, hσT⟩

end HRS.GF
