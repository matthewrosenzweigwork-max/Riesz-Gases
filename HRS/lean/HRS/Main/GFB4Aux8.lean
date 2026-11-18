import HRS.Main.GFB4Aux7

/-!
# GFB4, part 8: the pullback vector is the Riesz vector of the adjoint propagator, and the covariance identity
-/

noncomputable section

open MeasureTheory Filter Topology Finset ProbabilityTheory Complex
open scoped ENNReal NNReal BigOperators Matrix RealInnerProductSpace

namespace HRS.GF

open HRS HRS.Uniform HRS.Uniform.Q54c HRS.Uniform.Q45

variable {d : ℕ}

theorem gfb4_gamma_gt (S : GeneralSetup d) : (d : ℝ) / 2 + 2 < (S.γ : ℝ) := by
  have h' : ((2 * d + 10 : ℕ) : ℝ) < (S.γ : ℝ) := by exact_mod_cast S.hγ
  push_cast at h'
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  linarith

theorem gfb4_isCk2_of_smooth {φ : Torus d → ℝ} (h : Torus.IsSmooth φ) : Torus.IsCk 2 φ := by
  have h' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift φ) := h
  exact ContDiff.of_le h' (by simp)

theorem gfb4_qN_nonneg (S : GeneralSetup d) (N : ℕ) : 0 ≤ qN S N := by
  unfold qN qScale
  split_ifs with h
  · exact le_rfl
  · exact div_nonneg (mul_nonneg (sq_nonneg _) (S.hinvβ N)) (Nat.cast_nonneg N)

/-- The adjoint propagator of a classical adjoint solution is `C²` at times `r ∈ [0,t]`. -/
theorem gfb4_prop_isCk2 {D : DynData d} {ρ : ℝ → Torus d → ℝ} {t : ℝ} {φ : Torus d → ℝ}
    (h : ∃ f, IsClassicalAdjointSolution D ρ t φ f) {r : ℝ} (hr : r ∈ Set.Icc 0 t) :
    Torus.IsCk 2 (propagator D ρ r t φ) := by
  unfold propagator
  rw [dif_pos h]
  exact h.choose_spec.c2 r hr

theorem gfb4_pullback_eq_lpFun (S : GeneralSetup d) (M : Matrix (Fin d) (Fin d) ℝ) (N : ℕ) {m K : ℝ}
    (hm : (S.γ : ℝ) ≤ m) (EV : EvolData (NegSobolev d (S.γ : ℝ)) (NegSobolev d m))
    (hEV : GFEvo S M N m K EV) {r t : ℝ} (hr : 0 ≤ r) (hrt : r ≤ t) (ht : t ≤ S.T)
    {φ : Torus d → ℝ} (hφs : Torus.IsSmooth φ) (hφm : MemSobolev m φ) :
    pullbackVec EV t r (gfb4_ell m φ) =
      lpFun (S.γ : ℝ) (propagator (S.dynM M N) (S.ρ N) r t φ) := by
  have hφ2 : Torus.IsCk 2 φ := gfb4_isCk2_of_smooth hφs
  obtain ⟨hex, hmem, -⟩ := hEV.adjoint r t hr hrt ht φ hφ2 hφm
  have hmemγ : MemSobolev (S.γ : ℝ) (propagator (S.dynM M N) (S.ρ N) r t φ) :=
    HRS.PDE.MFAdjoint.memSobolev_mono_idx hmem hm
  refine ext_inner_right ℝ fun x => ?_
  rw [pullback_inner, gfb4_ell_apply hφm, hEV.dual r t hr hrt ht (EV.j x) φ hφs, hEV.j_eq,
    eval_embed hm x, eval_lpFun x hmemγ, real_inner_comm]

theorem gfb4_cov_eq (S : GeneralSetup d) (M : Matrix (Fin d) (Fin d) ℝ) (hMF : S.MFHypM M) (N : ℕ)
    {m K : ℝ} (hm : (S.γ : ℝ) ≤ m) (EV : EvolData (NegSobolev d (S.γ : ℝ)) (NegSobolev d m))
    (hEV : GFEvo S M N m K EV) {ta tb σ : ℝ} (hta : ta ∈ Set.Icc 0 S.T) (htb : tb ∈ Set.Icc 0 S.T)
    (hσ : σ ∈ Set.Icc 0 (min ta tb)) {φa φb : Torus d → ℝ} (hφa : Torus.IsSmooth φa)
    (hφb : Torus.IsSmooth φb) :
    covDensT (S.γ : ℝ) (qN S N) S.T (S.ρ N) σ
      (pullbackVec EV ta σ (gfb4_ell m φa)) (pullbackVec EV tb σ (gfb4_ell m φb)) =
    2 * qN S N * ∫ x, inner ℝ (Torus.grad (propagator (S.dynM M N) (S.ρ N) σ ta φa) x)
      (Torus.grad (propagator (S.dynM M N) (S.ρ N) σ tb φb) x) * S.ρ N σ x := by
  have hσa : σ ∈ Set.Icc 0 ta := ⟨hσ.1, hσ.2.trans (min_le_left _ _)⟩
  have hσb : σ ∈ Set.Icc 0 tb := ⟨hσ.1, hσ.2.trans (min_le_right _ _)⟩
  have hσT : σ ∈ Set.Icc 0 S.T := ⟨hσ.1, hσa.2.trans hta.2⟩
  have hmemφ : ∀ φ : Torus d → ℝ, Torus.IsSmooth φ → MemSobolev m φ := fun φ hφ =>
    HRS.PDE.MFSemigroup.memSobolev_of_isSmooth hφ m
  have hφ2 : ∀ φ : Torus d → ℝ, Torus.IsSmooth φ → Torus.IsCk 2 φ := fun φ hφ =>
    gfb4_isCk2_of_smooth hφ
  simp only [covDensT, if_pos hσT]
  rw [gfb4_pullback_eq_lpFun S M N hm EV hEV hσ.1 hσa.2 hta.2 hφa (hmemφ φa hφa),
    gfb4_pullback_eq_lpFun S M N hm EV hEV hσ.1 hσb.2 htb.2 hφb (hmemφ φb hφb)]
  obtain ⟨hMFN, hReg⟩ := hMF N
  have hρc : Continuous (S.ρ N σ) := by
    have h1 : (1 : WithTop ℕ∞) ≤ ((S.γ + 2 * d + 12 : ℕ) : WithTop ℕ∞) := by
      exact_mod_cast (show 1 ≤ S.γ + 2 * d + 12 by omega)
    have hC1 : ContDiff ℝ 1 (Torus.lift (S.ρ N σ)) := ContDiff.of_le (hReg σ hσT).1 h1
    exact Torus.continuous_of_continuous_lift hC1.continuous
  have hρ0 := (hMFN.density σ hσT).nonneg
  have hprop : ∀ {t : ℝ}, t ∈ Set.Icc 0 S.T → σ ∈ Set.Icc 0 t → ∀ φ : Torus d → ℝ, Torus.IsSmooth φ →
      MemSobolev (S.γ : ℝ) (propagator (S.dynM M N) (S.ρ N) σ t φ) ∧
      Continuous (propagator (S.dynM M N) (S.ρ N) σ t φ) ∧
      Torus.IsCk 1 (propagator (S.dynM M N) (S.ρ N) σ t φ) := by
    intro t ht hσt φ hφ
    obtain ⟨hex, hmem, -⟩ := hEV.adjoint σ t hσt.1 hσt.2 ht.2 φ (hφ2 φ hφ) (hmemφ φ hφ)
    have hck := gfb4_prop_isCk2 hex hσt
    refine ⟨HRS.PDE.MFAdjoint.memSobolev_mono_idx hmem hm,
      Torus.continuous_of_continuous_lift hck.continuous, ?_⟩
    exact ContDiff.of_le hck (by norm_num)
  obtain ⟨ha1, ha2, ha3⟩ := hprop hta hσa φa hφa
  obtain ⟨hb1, hb2, hb3⟩ := hprop htb hσb φb hφb
  exact covForm_lpFun (gfb4_gamma_gt S) (gfb4_qN_nonneg S N) hρc hρ0 ha1 ha2 ha3 hb1 hb2 hb3

end HRS.GF
