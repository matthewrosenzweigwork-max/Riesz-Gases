import HRS.MS.SA16Y9Cr1
import HRS.MS.SA16Y4Un1

/-!
# S.A.16 (SA16Y9) Cr2: `sa16y9_sub_stability` (stability, G2d, part 5)

Under `Sa16SubSrc`, the stability estimate of `adjoint_lp_stability` holds in the `LpCase.sub` regime.  The two solutions are identified
(level-`m+2` uniqueness) with the weak limits `G¹, G²` of the approximation families on a common subsequence; the difference of the
approximations is estimated at level `m` by `sa16y9_mild_diff_low` and the bound passes to the weak limit.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer
open HRS.Whole.AppendixA.Phase2SA16Q

section Cr2
variable {d : ℕ}

lemma sa16y9_derCoef_mono {k k' : ℕ} (h : k' ≤ k) {B : ℝ} {bc : Fin d → EuclideanSpace ℝ (Fin d) → ℝ}
    (hb : SA16DerCoef k B bc) : SA16DerCoef k' B bc :=
  ⟨hb.nonneg, hb.smooth, fun i j hj1 hj2 x => hb.bound i j hj1 (by omega) x⟩

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem sa16y9_sub_stability (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) (hm : 1 ≤ m) (p : ℝ)
    [Fact (2 ≤ p)] (MB Λ ΛV G₀ νbar T : ℝ) (χ : EuclideanSpace ℝ (Fin d) → ℝ) (hχ : IsUlocCutoff χ)
    (hsub : s ≤ (d : ℝ) - 2 ∧ (d : ℝ) < p * (s + 1)) (hsrc : Sa16SubSrc d s m p MB Λ ΛV G₀ νbar T) :
    ∃ C : ℝ, 0 < C ∧ ∀ (D₁ D₂ : WholeDyn d) (μ₁ μ₂ : ℝ → EuclideanSpace ℝ (Fin d) → ℝ),
      AdjointRdData s (m + 2) MB Λ ΛV G₀ νbar D₁ T μ₁ → AdjointRdData s (m + 2) MB Λ ΛV G₀ νbar D₂ T μ₂ →
      D₁.M = D₂.M → D₁.V = D₂.V → ∀ δ : ℝ, 0 ≤ δ →
      (∀ r ∈ Icc (0 : ℝ) T, coeffNormE d s m (μ₁ r - μ₂ r) ≤ ENNReal.ofReal δ) →
      ∀ t ∈ Ioc (0 : ℝ) T, ∀ φ : EuclideanSpace ℝ (Fin d) → ℝ, wNormE (m + 2) p φ < ⊤ →
      ∀ F₁ F₂ : ℝ → EuclideanSpace ℝ (Fin d) → ℝ,
        IsLpSolutionRd (m + 2) p χ (D₁.coeff μ₁) t φ F₁ → IsLpSolutionRd (m + 2) p χ (D₂.coeff μ₂) t φ F₂ →
        ∀ τ ∈ Icc (0 : ℝ) t, wNormE m p (fun x => F₁ τ x - F₂ τ x) ≤
          ENNReal.ofReal (C * τ * Real.exp (C * τ) * (|D₁.invβ - D₂.invβ| + δ)) * wNormE (m + 2) p φ := by
  have hp2 : (2 : ℝ) ≤ p := Fact.out
  have hp1 : 1 ≤ p := by linarith
  have hm2 : 1 ≤ m + 2 := by omega
  obtain ⟨Ks, hKs0, hsrc'⟩ := hsrc
  obtain ⟨cE, CN, B, CG, hCN, hB0, hCG, hfam⟩ :=
    sa16y9_sub_fam hd s hs0 hsd (m + 2) hm2 p MB Λ ΛV G₀ νbar T hsub
  obtain ⟨Cl, hCl0, hlift⟩ := sa16y4_data_lifts (d := d) (p := p) hp1 (m + 2)
  obtain ⟨CGl, hCGl0, hGl⟩ := sa16y9_GInt_low hd s hs0 m p MB Λ hsub
  obtain ⟨-, ⟨Cj, hCj0, hCj⟩, -, -⟩ := closed_jet_energy_calculus d m p
  set c0 : ℝ := max (p * sa16sz_cTr d m p B + p * sa16y3_CJ d m p * CGl) 0 / p with hc0
  have hp0 : 0 < p := by linarith
  have hc00 : 0 ≤ c0 := div_nonneg (le_max_right _ _) hp0.le
  set K0 : ℝ := Cj * Ks * CN * Cl * Real.exp (|cE| * T) with hK0
  have hK00 : 0 ≤ K0 := by positivity
  refine ⟨max K0 (max c0 1) + 1, by positivity, ?_⟩
  intro D₁ D₂ μ₁ μ₂ hD1 hD2 hM hV δ hδ0 hδ t ht φ hφ F₁ F₂ h1 h2 τ hτ
  set C : ℝ := max K0 (max c0 1) + 1 with hC
  have hKC : K0 ≤ C := by rw [hC]; linarith [le_max_left K0 (max c0 1)]
  have hcC : c0 ≤ C := by rw [hC]; linarith [le_max_left c0 1, le_max_right K0 (max c0 1)]
  have hτ0 : 0 ≤ τ := hτ.1
  have htT : t ≤ T := ht.2
  set w : ℝ := (wNormE (m + 2) p φ).toReal with hw
  have hw0 : 0 ≤ w := ENNReal.toReal_nonneg
  obtain ⟨Φ, hΦbd, hΦlim⟩ := hlift φ hφ
  have hCφ0 : 0 ≤ Cl * w := mul_nonneg hCl0 hw0
  obtain ⟨A1, e1φ, e1ν, e1bc, -, e1T0, -, e1bd, e1der, e1div, e1νb⟩ :=
    hfam D₁ μ₁ hD1 t ht (Cl * w) hCφ0 Φ hΦbd
  obtain ⟨A2, e2φ, e2ν, e2bc, -, e2T0, -, e2bd, e2der, e2div, e2νb⟩ :=
    hfam D₂ μ₂ hD2 t ht (Cl * w) hCφ0 Φ hΦbd
  obtain ⟨φs, hφs, G1, G2, hGn1, hGn2, hGc1, hGc2, hL1, hL2⟩ :=
    sa16y9_weak_pair ht.1 A1 A2 hCG e1div e2div e1νb e2νb
  have hΦl1 : ∀ {ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hψ : IsCcInfty ψ),
      Tendsto (fun n => sa16r_ell d (m + 2 + 1 + 1) p hψ (A1.φ n)) atTop (𝓝 (∫ x, φ x * ψ x)) := by
    intro ψ hψ
    have : (fun n => sa16r_ell d (m + 2 + 1 + 1) p hψ (A1.φ n)) = fun n => sa16r_ell d (m + 2 + 1 + 1) p hψ (Φ n) :=
      funext fun n => by rw [e1φ]
    rw [this]; exact hΦlim hψ
  have hΦl2 : ∀ {ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hψ : IsCcInfty ψ),
      Tendsto (fun n => sa16r_ell d (m + 2 + 1 + 1) p hψ (A2.φ n)) atTop (𝓝 (∫ x, φ x * ψ x)) := by
    intro ψ hψ
    have : (fun n => sa16r_ell d (m + 2 + 1 + 1) p hψ (A2.φ n)) = fun n => sa16r_ell d (m + 2 + 1 + 1) p hψ (Φ n) :=
      funext fun n => by rw [e2φ]
    rw [this]; exact hΦlim hψ
  -- norm bounds of the limits
  have hexp : ∀ r ∈ Icc (0 : ℝ) t, Real.exp (cE * r) ≤ Real.exp (|cE| * t) := fun r hr =>
    Real.exp_le_exp.2 (by
      calc cE * r ≤ |cE| * r := mul_le_mul_of_nonneg_right (le_abs_self _) hr.1
        _ ≤ |cE| * t := mul_le_mul_of_nonneg_left hr.2 (abs_nonneg _))
  have hvb : ∀ (A : SA16Approx d (m + 2) p t CG (CN * (Cl * w) * Real.exp (|cE| * t))) (n : ℕ),
      (∀ r ∈ Icc (0 : ℝ) t, ‖sa16sz_iota2 d (m + 2) p (A.u n r)‖ ≤
        CN * ‖sa16sz_iota2 d (m + 2) p (Φ n)‖ * Real.exp (cE * r)) →
      ∀ r ∈ Icc (0 : ℝ) t, ‖sa16sz_iota2 d (m + 2) p (A.u n r)‖ ≤ CN * (Cl * w) * Real.exp (|cE| * t) := by
    intro A n hb r hr
    refine (hb r hr).trans ?_
    exact mul_le_mul (mul_le_mul_of_nonneg_left (hΦbd n) hCN.le) (hexp r hr) (Real.exp_pos _).le (by positivity)
  have hbd1 : ∀ τ' ∈ Icc (0 : ℝ) t, ‖G1 τ'‖ ≤ CN * (Cl * w) * Real.exp (|cE| * t) := fun τ' hτ' =>
    sa16y4_norm_le_of_weak (fun j => sa16sz_iota2 d (m + 2) p (A1.u (φs j) τ')) (G1 τ')
      (fun j => hvb A1 (φs j) (e1bd (φs j)) τ' hτ') (fun ℓ => hGn1 τ' hτ' ℓ)
  have hbd2 : ∀ τ' ∈ Icc (0 : ℝ) t, ‖G2 τ'‖ ≤ CN * (Cl * w) * Real.exp (|cE| * t) := fun τ' hτ' =>
    sa16y4_norm_le_of_weak (fun j => sa16sz_iota2 d (m + 2) p (A2.u (φs j) τ')) (G2 τ')
      (fun j => hvb A2 (φs j) (e2bd (φs j)) τ' hτ') (fun ℓ => hGn2 τ' hτ' ℓ)
  have hS1 := sa16y9_isLp_of_path hd s hs0 hsd (m + 2) hm2 p MB Λ ΛV G₀ νbar T χ hχ D₁ μ₁ hD1 t ht φ G1 _ hbd1
    hGc1 (fun {ψ} hψ => sa16y9_sub_tail hd s hs0 hsd (m + 2) hm2 p MB Λ ΛV G₀ νbar T hsub D₁ μ₁ hD1 t ht φ A1
      e1ν e1bc e1T0 φs hφs G1 hGn1 hΦl1 hL1 hψ)
  have hS2 := sa16y9_isLp_of_path hd s hs0 hsd (m + 2) hm2 p MB Λ ΛV G₀ νbar T χ hχ D₂ μ₂ hD2 t ht φ G2 _ hbd2
    hGc2 (fun {ψ} hψ => sa16y9_sub_tail hd s hs0 hsd (m + 2) hm2 p MB Λ ΛV G₀ νbar T hsub D₂ μ₂ hD2 t ht φ A2
      e2ν e2bc e2T0 φs hφs G2 hGn2 hΦl2 hL2 hψ)
  have hu1 := Phase2SA16Assembly.sa16y4_lp_unique d hd s hs0 hsd (m + 2) hm2 p LpCase.sub MB Λ ΛV G₀ νbar T χ D₁ μ₁ hD1 hsub t ht φ
    F₁ _ h1 hS1
  have hu2 := Phase2SA16Assembly.sa16y4_lp_unique d hd s hs0 hsd (m + 2) hm2 p LpCase.sub MB Λ ΛV G₀ νbar T χ D₂ μ₂ hD2 hsub t ht φ
    F₂ _ h2 hS2
  -- the difference of the approximations at level m
  set ssrc : ℝ := Cj * (Ks * (|D₁.invβ - D₂.invβ| + δ) * (CN * (Cl * w) * Real.exp (|cE| * t))) with hssrc
  have hdn : 0 ≤ |D₁.invβ - D₂.invβ| + δ := add_nonneg (abs_nonneg _) hδ0
  have hss0 : 0 ≤ ssrc := by positivity
  have hreg1 : ∀ r ∈ Icc (0 : ℝ) t, IsRegularDensityW (m + 4) Λ (μ₁ r) := fun r hr =>
    sa16y9_regDensity_mono (by omega) (sa16so_regDensity_of_MF hD1.hμ.regular ⟨hr.1, hr.2.trans htT⟩)
  have hreg2 : ∀ r ∈ Icc (0 : ℝ) t, IsRegularDensityW (m + 4) Λ (μ₂ r) := fun r hr =>
    sa16y9_regDensity_mono (by omega) (sa16so_regDensity_of_MF hD2.hμ.regular ⟨hr.1, hr.2.trans htT⟩)
  have hkey : ∀ n : ℕ, ∀ τ' ∈ Icc (0 : ℝ) t,
      jetEnergy d m p (sa16sz_iota2 d m p (sa16sz_iota2 d (m + 2) p (A1.u n τ') -
        sa16sz_iota2 d (m + 2) p (A2.u n τ'))) ^ (1 / p) ≤
      Real.exp (max (p * sa16sz_cTr d m p B + p * sa16y3_CJ d m p * CGl) 0 / p * τ') * (ssrc * τ') := by
    intro n
    refine sa16y9_mild_diff_low (m := m) (B := B) (s := ssrc) (CGl := CGl) A1 A2
      (fun n σ => sa16y4_GInt d m (n + 1) p s D₁.M t μ₁ σ) (fun n σ => sa16y4_GInt d m (n + 1) p s D₂.M t μ₂ σ)
      ht.1 n (by rw [e1φ, e2φ]) hss0 ?_ ?_ ?_ ?_ ?_
    · intro σ hσ
      rw [e1T0 n]
      exact (hGl D₁.M hD1.hM μ₁ t ht.1 hreg1 (n + 1) (by omega) σ hσ).1
    · intro σ hσ
      rw [e2T0 n]
      exact (hGl D₂.M hD2.hM μ₂ t ht.1 hreg2 (n + 1) (by omega) σ hσ).1
    · intro σ hσ
      exact (hGl D₁.M hD1.hM μ₁ t ht.1 hreg1 (n + 1) (by omega) σ hσ).2
    · intro σ hσ
      exact sa16y9_derCoef_mono (by omega) (e1der n σ hσ)
    · intro τ' hτ'
      have hτ'c : τ' ∈ Icc (0 : ℝ) t := ⟨hτ'.1.le, hτ'.2.le⟩
      have hv := hvb A2 n (e2bd n) τ' hτ'c
      have hνd : A1.ν n - A2.ν n = D₁.invβ - D₂.invβ := by rw [e1ν, e2ν]; ring
      have hb := hsrc' D₁ D₂ μ₁ μ₂ hD1 hD2 hM hV δ hδ0 hδ t ht n τ' hτ'c (sa16sz_iota2 d (m + 2) p (A2.u n τ'))
      have e : sa16y9_srcl A1 A2 (fun n σ => sa16y4_GInt d m (n + 1) p s D₁.M t μ₁ σ)
          (fun n σ => sa16y4_GInt d m (n + 1) p s D₂.M t μ₂ σ) n τ' =
          (D₁.invβ - D₂.invβ) • sa16so_Lap d m p (sa16sz_iota2 d (m + 2) p (A2.u n τ')) +
            sa16r_iota d m p (sa16so_B d (m + 1) p (sa16y4_bcInt d (n + 1) t (fun r => meanFieldDriftW D₁ (μ₁ r)) τ')
              (sa16sz_iota2 d (m + 2) p (A2.u n τ')) -
              sa16so_B d (m + 1) p (sa16y4_bcInt d (n + 1) t (fun r => meanFieldDriftW D₂ (μ₂ r)) τ')
                (sa16sz_iota2 d (m + 2) p (A2.u n τ'))) -
            (sa16y4_GInt d m (n + 1) p s D₁.M t μ₁ τ' - sa16y4_GInt d m (n + 1) p s D₂.M t μ₂ τ')
              (sa16sz_iota2 d m p (sa16sz_iota2 d (m + 2) p (A2.u n τ'))) := by
        unfold sa16y9_srcl
        rw [hνd, e1bc n, e2bc n]
      show jetNorm d m p _ ≤ ssrc
      rw [e]
      calc jetNorm d m p _ ≤ Cj * ‖(D₁.invβ - D₂.invβ) • sa16so_Lap d m p (sa16sz_iota2 d (m + 2) p (A2.u n τ')) +
            sa16r_iota d m p (sa16so_B d (m + 1) p (sa16y4_bcInt d (n + 1) t (fun r => meanFieldDriftW D₁ (μ₁ r)) τ')
              (sa16sz_iota2 d (m + 2) p (A2.u n τ')) -
              sa16so_B d (m + 1) p (sa16y4_bcInt d (n + 1) t (fun r => meanFieldDriftW D₂ (μ₂ r)) τ')
                (sa16sz_iota2 d (m + 2) p (A2.u n τ'))) -
            (sa16y4_GInt d m (n + 1) p s D₁.M t μ₁ τ' - sa16y4_GInt d m (n + 1) p s D₂.M t μ₂ τ')
              (sa16sz_iota2 d m p (sa16sz_iota2 d (m + 2) p (A2.u n τ')))‖ := (hCj _).2
        _ ≤ Cj * (Ks * (|D₁.invβ - D₂.invβ| + δ) * ‖sa16sz_iota2 d (m + 2) p (A2.u n τ')‖) :=
            mul_le_mul_of_nonneg_left hb hCj0.le
        _ ≤ ssrc := by
            rw [hssrc]
            exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hv (by positivity)) hCj0.le
  -- pass to the weak limit
  have hbτ : ‖sa16sz_iota2 d m p (G1 τ - G2 τ)‖ ≤ Real.exp (c0 * τ) * (ssrc * τ) := by
    refine sa16y4_norm_le_of_weak (fun j => sa16sz_iota2 d m p (sa16sz_iota2 d (m + 2) p (A1.u (φs j) τ) -
        sa16sz_iota2 d (m + 2) p (A2.u (φs j) τ))) _ (fun j => ?_) (fun ℓ => ?_)
    · exact (hkey (φs j) τ hτ).trans' (by
        have := (closed_jet_energy_calculus d m p).2.1
        obtain ⟨C', -, hC'⟩ := this
        exact (hC' _).1)
    · have hℓ1 := hGn1 τ hτ (ℓ.comp (sa16sz_iota2 d m p))
      have hℓ2 := hGn2 τ hτ (ℓ.comp (sa16sz_iota2 d m p))
      have := hℓ1.sub hℓ2
      simp only [ContinuousLinearMap.comp_apply] at this
      simpa [map_sub] using this
  -- identify the difference
  have hae : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))),
      wrep d m p (sa16sz_iota2 d m p (G1 τ - G2 τ)) x = (fun x => F₁ τ x - F₂ τ x) x := by
    filter_upwards [sa16y9_wrep_iota2 (p := p) m (G1 τ - G2 τ), sa16y3_wrep_sub (G1 τ) (G2 τ), hu1 τ hτ,
      hu2 τ hτ] with x h1' h2' h3' h4'
    rw [h1', h2', h3', h4']
  have hw1 : wNormE m p (fun x => F₁ τ x - F₂ τ x) ≤ ENNReal.ofReal ‖sa16sz_iota2 d m p (G1 τ - G2 τ)‖ :=
    iInf₂_le (sa16sz_iota2 d m p (G1 τ - G2 τ)) hae
  refine hw1.trans ?_
  have hwe : wNormE (m + 2) p φ = ENNReal.ofReal w := (ENNReal.ofReal_toReal hφ.ne).symm
  rw [hwe]
  have hnn : 0 ≤ C * τ * Real.exp (C * τ) * (|D₁.invβ - D₂.invβ| + δ) := by positivity
  rw [← ENNReal.ofReal_mul hnn]
  refine ENNReal.ofReal_le_ofReal (hbτ.trans ?_)
  have hexpC : Real.exp (c0 * τ) ≤ Real.exp (C * τ) := Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hcC hτ0)
  have hexpT : Real.exp (|cE| * t) ≤ Real.exp (|cE| * T) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left htT (abs_nonneg _))
  have hrhs : Real.exp (c0 * τ) * (ssrc * τ) = Real.exp (c0 * τ) * τ * (Cj * Ks * CN * Cl * Real.exp (|cE| * t)) *
      ((|D₁.invβ - D₂.invβ| + δ) * w) := by rw [hssrc]; ring
  rw [hrhs]
  have hK1 : Cj * Ks * CN * Cl * Real.exp (|cE| * t) ≤ C := by
    refine le_trans ?_ hKC
    rw [hK0]
    exact mul_le_mul_of_nonneg_left hexpT (by positivity)
  calc Real.exp (c0 * τ) * τ * (Cj * Ks * CN * Cl * Real.exp (|cE| * t)) * ((|D₁.invβ - D₂.invβ| + δ) * w)
      ≤ Real.exp (C * τ) * τ * C * ((|D₁.invβ - D₂.invβ| + δ) * w) := by
        gcongr
    _ = C * τ * Real.exp (C * τ) * (|D₁.invβ - D₂.invβ| + δ) * w := by ring

end Cr2

end HRS.Whole.AppendixA.Phase2SA16R
