import HRS.Main.ThermLin2Fu4

/-!
# THERMLIN2 Fu5: second moments of the pairings (`tl2_cov_mixed` instances) for the variance computation of B4
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.ThermLin.Plan2

open HRS HRS.Uniform HRS.GF HRS.AdjK HRS.T25P HRS.Uniform.Q54c HRS.Uniform.Q45 Classical

variable {d : ℕ}

/-- The pullback vector restricted to `[0,t]` (zero elsewhere). -/
def tl2fuPb {m : ℝ} (V : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m) (t : ℝ)
    (ℓ : NegSobolev d m →L[ℝ] ℝ) (σ : ℝ) : NegSobolev d m :=
  if σ ∈ Set.Icc (0 : ℝ) t then pullbackVec (HRS.Uniform.Comp28.plainData V) t σ ℓ else 0

theorem tl2fuA_eq {m : ℝ} (Vev Wev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m) (t : ℝ) (φ : Torus d → ℝ)
    (σ : ℝ) : tl2fuA Vev Wev t φ σ = tl2fuPb Vev t (gfb4_ell m φ) σ - tl2fuPb Wev t (gfb4_ell m φ) σ := by
  by_cases h : σ ∈ Set.Icc (0 : ℝ) t <;> simp [tl2fuA, tl2fuPb, h]

section Cov

variable {m T' K : ℝ} {Vev Wev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m}
  {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ}
  {G : ℝ → Ω → NegSobolev d m} {Cd : ℝ → NegSobolev d m →L[ℝ] NegSobolev d m →L[ℝ] ℝ}
  {Zs Zw : ℝ → Ω → NegSobolev d m} {t : ℝ} {φ : Torus d → ℝ} {ψ : ℝ → Torus d → ℝ} {B : ℝ}

/-- Integrability of `σ ↦ Cd σ (x σ) (y σ)` for bounded measurable vector functions. -/
theorem tl2fu_form_int (D : Tl2FuSetup m T' K Vev Wev P ℱ G Cd Zs Zw) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) T')
    {x y : ℝ → NegSobolev d m} (hx : Measurable x) (hy : Measurable y) {Bx By : ℝ}
    (hxB : ∀ σ ∈ Set.Icc (0 : ℝ) s, ‖x σ‖ ≤ Bx) (hyB : ∀ σ ∈ Set.Icc (0 : ℝ) s, ‖y σ‖ ≤ By) :
    IntegrableOn (fun σ => Cd σ (x σ) (y σ)) (Set.Icc 0 s) := by
  obtain ⟨hTC, hτ, hCm⟩ := D.cov_facts
  have hsub : Set.Icc (0 : ℝ) s ⊆ Set.Icc 0 T' := Set.Icc_subset_Icc_right hs.2
  have hbd : IntegrableOn (fun σ => traceNormForm (Cd σ) * (Bx * By)) (Set.Icc 0 s) :=
    (hτ.mono_set hsub).mul_const _
  refine hbd.mono' ?_ ?_
  · have h1 : Measurable fun σ : ℝ => ((x σ, y σ), σ) := (hx.prodMk hy).prodMk measurable_id
    exact ((measurable_form_apply hCm).comp h1).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun σ hσ => ?_)
    rw [Real.norm_eq_abs]
    refine (abs_apply_le_tn (hTC σ (hsub hσ)) _ _).trans ?_
    have hx0 := (norm_nonneg _).trans (hxB σ hσ)
    have hy0 := (norm_nonneg _).trans (hyB σ hσ)
    exact mul_le_mul_of_nonneg_left (mul_le_mul (hxB σ hσ) (hyB σ hσ) (norm_nonneg _) hx0)
      (traceNormForm_nonneg _)

/-- Covariance of a difference with a third variable. -/
theorem tl2fu_cov_left {s : ℝ} {Xa Xb Xc : Ω → ℝ} (ha : MemLp Xa 2 P) (hb : MemLp Xb 2 P) (hc : MemLp Xc 2 P)
    {ua ub uc : ℝ → NegSobolev d m}
    (hac : ∫ ω, Xa ω * Xc ω ∂P = ∫ σ in Set.Icc 0 s, Cd σ (ua σ) (uc σ))
    (hbc : ∫ ω, Xb ω * Xc ω ∂P = ∫ σ in Set.Icc 0 s, Cd σ (ub σ) (uc σ))
    (hia : IntegrableOn (fun σ => Cd σ (ua σ) (uc σ)) (Set.Icc 0 s))
    (hib : IntegrableOn (fun σ => Cd σ (ub σ) (uc σ)) (Set.Icc 0 s)) :
    ∫ ω, (Xa ω - Xb ω) * Xc ω ∂P = ∫ σ in Set.Icc 0 s, Cd σ (ua σ - ub σ) (uc σ) := by
  have e1 : ∀ ω, (Xa ω - Xb ω) * Xc ω = Xa ω * Xc ω - Xb ω * Xc ω := fun ω => by ring
  simp_rw [e1]
  rw [integral_sub (f := fun ω => Xa ω * Xc ω) (g := fun ω => Xb ω * Xc ω) (ha.integrable_mul hc)
    (hb.integrable_mul hc), hac, hbc,
    ← integral_sub (f := fun σ => Cd σ (ua σ) (uc σ)) (g := fun σ => Cd σ (ub σ) (uc σ)) hia hib]
  refine integral_congr_ae (Eventually.of_forall fun σ => ?_)
  simp only [map_sub, ContinuousLinearMap.sub_apply]

theorem tl2fu_cov_vv (D : Tl2FuSetup m T' K Vev Wev P ℱ G Cd Zs Zw) {t₁ t₂ : ℝ}
    (ht₁ : t₁ ∈ Set.Icc (0 : ℝ) T') (ht₂ : t₂ ∈ Set.Icc (0 : ℝ) T') {φ₁ φ₂ : Torus d → ℝ}
    (hφ₁ : MemSobolev m φ₁) (hφ₂ : MemSobolev m φ₂) :
    ∫ ω, NegSobolev.eval (Zs t₁ ω) φ₁ * NegSobolev.eval (Zs t₂ ω) φ₂ ∂P =
      ∫ σ in Set.Icc 0 (min t₁ t₂),
        Cd σ (pullbackVec (HRS.Uniform.Comp28.plainData Vev) t₁ σ (gfb4_ell m φ₁))
          (pullbackVec (HRS.Uniform.Comp28.plainData Vev) t₂ σ (gfb4_ell m φ₂)) :=
  tl2_cov_mixed_proof D.hK D.hK D.hT0 Vev Vev D.hVc D.hVc D.hVb D.hVb P G Cd D.hG D.hGc D.hGz Zs Zs D.hZs D.hZs
    D.hZsm D.hZsm ht₁ ht₂ hφ₁ hφ₂

theorem tl2fu_cov_vw (D : Tl2FuSetup m T' K Vev Wev P ℱ G Cd Zs Zw) {t₁ t₂ : ℝ}
    (ht₁ : t₁ ∈ Set.Icc (0 : ℝ) T') (ht₂ : t₂ ∈ Set.Icc (0 : ℝ) T') {φ₁ φ₂ : Torus d → ℝ}
    (hφ₁ : MemSobolev m φ₁) (hφ₂ : MemSobolev m φ₂) :
    ∫ ω, NegSobolev.eval (Zs t₁ ω) φ₁ * NegSobolev.eval (Zw t₂ ω) φ₂ ∂P =
      ∫ σ in Set.Icc 0 (min t₁ t₂),
        Cd σ (pullbackVec (HRS.Uniform.Comp28.plainData Vev) t₁ σ (gfb4_ell m φ₁))
          (pullbackVec (HRS.Uniform.Comp28.plainData Wev) t₂ σ (gfb4_ell m φ₂)) :=
  tl2_cov_mixed_proof D.hK D.hK D.hT0 Vev Wev D.hVc D.hWc D.hVb D.hWb P G Cd D.hG D.hGc D.hGz Zs Zw D.hZs D.hZw
    D.hZsm D.hZwm ht₁ ht₂ hφ₁ hφ₂

theorem tl2fu_cov_wv (D : Tl2FuSetup m T' K Vev Wev P ℱ G Cd Zs Zw) {t₁ t₂ : ℝ}
    (ht₁ : t₁ ∈ Set.Icc (0 : ℝ) T') (ht₂ : t₂ ∈ Set.Icc (0 : ℝ) T') {φ₁ φ₂ : Torus d → ℝ}
    (hφ₁ : MemSobolev m φ₁) (hφ₂ : MemSobolev m φ₂) :
    ∫ ω, NegSobolev.eval (Zw t₁ ω) φ₁ * NegSobolev.eval (Zs t₂ ω) φ₂ ∂P =
      ∫ σ in Set.Icc 0 (min t₁ t₂),
        Cd σ (pullbackVec (HRS.Uniform.Comp28.plainData Wev) t₁ σ (gfb4_ell m φ₁))
          (pullbackVec (HRS.Uniform.Comp28.plainData Vev) t₂ σ (gfb4_ell m φ₂)) :=
  tl2_cov_mixed_proof D.hK D.hK D.hT0 Wev Vev D.hWc D.hVc D.hWb D.hVb P G Cd D.hG D.hGc D.hGz Zw Zs D.hZw D.hZs
    D.hZwm D.hZsm ht₁ ht₂ hφ₁ hφ₂

theorem tl2fu_cov_ww (D : Tl2FuSetup m T' K Vev Wev P ℱ G Cd Zs Zw) {t₁ t₂ : ℝ}
    (ht₁ : t₁ ∈ Set.Icc (0 : ℝ) T') (ht₂ : t₂ ∈ Set.Icc (0 : ℝ) T') {φ₁ φ₂ : Torus d → ℝ}
    (hφ₁ : MemSobolev m φ₁) (hφ₂ : MemSobolev m φ₂) :
    ∫ ω, NegSobolev.eval (Zw t₁ ω) φ₁ * NegSobolev.eval (Zw t₂ ω) φ₂ ∂P =
      ∫ σ in Set.Icc 0 (min t₁ t₂),
        Cd σ (pullbackVec (HRS.Uniform.Comp28.plainData Wev) t₁ σ (gfb4_ell m φ₁))
          (pullbackVec (HRS.Uniform.Comp28.plainData Wev) t₂ σ (gfb4_ell m φ₂)) :=
  tl2_cov_mixed_proof D.hK D.hK D.hT0 Wev Wev D.hWc D.hWc D.hWb D.hWb P G Cd D.hG D.hGc D.hGz Zw Zw D.hZw D.hZw
    D.hZwm D.hZwm ht₁ ht₂ hφ₁ hφ₂

theorem tl2fu_memLp_s (D : Tl2FuSetup m T' K Vev Wev P ℱ G Cd Zs Zw) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) T')
    {χ : Torus d → ℝ} (hχ : MemSobolev m χ) : MemLp (fun ω => NegSobolev.eval (Zs s ω) χ) 2 P :=
  tl2fu_memLp_of_conv D.hK D.hT0 Vev D.hVc D.hVb D.hG D.hGc D.hGz Zs D.hZs D.hZsm hs hχ

theorem tl2fu_memLp_w (D : Tl2FuSetup m T' K Vev Wev P ℱ G Cd Zs Zw) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) T')
    {χ : Torus d → ℝ} (hχ : MemSobolev m χ) : MemLp (fun ω => NegSobolev.eval (Zw s ω) χ) 2 P :=
  tl2fu_memLp_of_conv D.hK D.hT0 Wev D.hWc D.hWb D.hG D.hGc D.hGz Zw D.hZw D.hZwm hs hχ

theorem tl2fu_Pb_norm (V : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m)
    (hVb : ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ T' → ‖V t r‖ ≤ K) (hK : 0 ≤ K) (ht : t ∈ Set.Icc (0 : ℝ) T')
    (ℓ : NegSobolev d m →L[ℝ] ℝ) (σ : ℝ) : ‖tl2fuPb V t ℓ σ‖ ≤ K * ‖ℓ‖ := by
  by_cases h : σ ∈ Set.Icc (0 : ℝ) t
  · simp only [tl2fuPb, h, ↓reduceIte]
    exact t25p_norm_pullback_le V hVb hK h.1 h.2 ht.2 ℓ
  · simp only [tl2fuPb, h, ↓reduceIte, norm_zero]
    exact mul_nonneg hK (norm_nonneg _)

theorem tl2fu_Pb_meas (V : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m)
    (hVc : ∀ y : NegSobolev d m, ContinuousOn (fun p : ℝ × ℝ => V p.1 p.2 y) {p | 0 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ T'})
    (ht : t ∈ Set.Icc (0 : ℝ) T') (ℓ : NegSobolev d m →L[ℝ] ℝ) : Measurable (tl2fuPb V t ℓ) :=
  tl2fu_meas_pb (T' := T') V hVc ht ℓ

theorem tl2fuW_eq {r σ : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) t) (hσ : σ ∈ Set.Icc (0 : ℝ) r) :
    tl2fuW Wev t ψ (r, σ) = pullbackVec (HRS.Uniform.Comp28.plainData Wev) r σ (gfb4_ell m (ψ r)) := by
  have : 0 ≤ σ ∧ σ ≤ r ∧ r ≤ t := ⟨hσ.1, hσ.2, hr.2⟩
  simp only [tl2fuW, this, and_self, ↓reduceIte]

theorem tl2fuPb_eq {σ : ℝ} (V : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m) (ℓ : NegSobolev d m →L[ℝ] ℝ)
    (hσ : σ ∈ Set.Icc (0 : ℝ) t) :
    tl2fuPb V t ℓ σ = pullbackVec (HRS.Uniform.Comp28.plainData V) t σ ℓ := by
  simp only [tl2fuPb, hσ, ↓reduceIte]

/-- `E[A F_r] = ∫_0^r Cd(a, w_r)`. -/
theorem tl2fu_cov_AF (D : Tl2FuSetup m T' K Vev Wev P ℱ G Cd Zs Zw) (ht : t ∈ Set.Icc (0 : ℝ) T')
    (E : Tl2FuTest Vev Wev t φ ψ B) {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) t) :
    ∫ ω, (NegSobolev.eval (Zs t ω) φ - NegSobolev.eval (Zw t ω) φ) * NegSobolev.eval (Zw r ω) (ψ r) ∂P =
      ∫ σ in Set.Icc 0 r, Cd σ (tl2fuA Vev Wev t φ σ) (tl2fuW Wev t ψ (r, σ)) := by
  have hrT : r ∈ Set.Icc (0 : ℝ) T' := ⟨hr.1, hr.2.trans ht.2⟩
  have hψr := E.hψm r hr
  have mV := tl2fu_cov_vw D ht hrT E.hφ hψr
  have mW := tl2fu_cov_ww D ht hrT E.hφ hψr
  rw [min_eq_right hr.2] at mV mW
  have hsub : Set.Icc (0 : ℝ) r ⊆ Set.Icc 0 t := Set.Icc_subset_Icc_right hr.2
  have hwm : Measurable fun σ => tl2fuW Wev t ψ (r, σ) :=
    (tl2fu_W_meas D ht E).comp measurable_prodMk_left
  have hwB : ∀ σ ∈ Set.Icc (0 : ℝ) r, ‖tl2fuW Wev t ψ (r, σ)‖ ≤ K * B := fun σ hσ => tl2fu_W_bound D ht E hr hσ
  have key := tl2fu_cov_left (P := P) (s := r) (Cd := Cd)
    (tl2fu_memLp_s D ht E.hφ) (tl2fu_memLp_w D ht E.hφ) (tl2fu_memLp_w D hrT hψr)
    (ua := tl2fuPb Vev t (gfb4_ell m φ)) (ub := tl2fuPb Wev t (gfb4_ell m φ))
    (uc := fun σ => tl2fuW Wev t ψ (r, σ))
    (by
      rw [mV]
      refine setIntegral_congr_fun measurableSet_Icc fun σ hσ => ?_
      rw [tl2fuPb_eq Vev _ (hsub hσ), tl2fuW_eq hr hσ])
    (by
      rw [mW]
      refine setIntegral_congr_fun measurableSet_Icc fun σ hσ => ?_
      rw [tl2fuPb_eq Wev _ (hsub hσ), tl2fuW_eq hr hσ])
    (tl2fu_form_int D hrT (tl2fu_Pb_meas Vev D.hVc ht _) hwm
      (fun σ _ => tl2fu_Pb_norm Vev D.hVb D.hK ht _ σ) hwB)
    (tl2fu_form_int D hrT (tl2fu_Pb_meas Wev D.hWc ht _) hwm
      (fun σ _ => tl2fu_Pb_norm Wev D.hWb D.hK ht _ σ) hwB)
  rw [key]
  refine setIntegral_congr_fun measurableSet_Icc fun σ hσ => ?_
  rw [tl2fuA_eq]

/-- `E[F_r F_{r'}] = ∫_0^{r∧r'} Cd(w_r, w_{r'})`. -/
theorem tl2fu_cov_FF (D : Tl2FuSetup m T' K Vev Wev P ℱ G Cd Zs Zw) (ht : t ∈ Set.Icc (0 : ℝ) T')
    (E : Tl2FuTest Vev Wev t φ ψ B) {r r' : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) t) (hr' : r' ∈ Set.Icc (0 : ℝ) t) :
    ∫ ω, NegSobolev.eval (Zw r ω) (ψ r) * NegSobolev.eval (Zw r' ω) (ψ r') ∂P =
      ∫ σ in Set.Icc 0 (min r r'), Cd σ (tl2fuW Wev t ψ (r, σ)) (tl2fuW Wev t ψ (r', σ)) := by
  have hrT : r ∈ Set.Icc (0 : ℝ) T' := ⟨hr.1, hr.2.trans ht.2⟩
  have hrT' : r' ∈ Set.Icc (0 : ℝ) T' := ⟨hr'.1, hr'.2.trans ht.2⟩
  rw [tl2fu_cov_ww D hrT hrT' (E.hψm r hr) (E.hψm r' hr')]
  refine setIntegral_congr_fun measurableSet_Icc fun σ hσ => ?_
  rw [tl2fuW_eq hr ⟨hσ.1, hσ.2.trans (min_le_left _ _)⟩, tl2fuW_eq hr' ⟨hσ.1, hσ.2.trans (min_le_right _ _)⟩]

/-- `E[A²] = ∫_0^t Cd(a, a)`. -/
theorem tl2fu_cov_AA (D : Tl2FuSetup m T' K Vev Wev P ℱ G Cd Zs Zw) (ht : t ∈ Set.Icc (0 : ℝ) T')
    (E : Tl2FuTest Vev Wev t φ ψ B) :
    ∫ ω, (NegSobolev.eval (Zs t ω) φ - NegSobolev.eval (Zw t ω) φ) *
        (NegSobolev.eval (Zs t ω) φ - NegSobolev.eval (Zw t ω) φ) ∂P =
      ∫ σ in Set.Icc 0 t, Cd σ (tl2fuA Vev Wev t φ σ) (tl2fuA Vev Wev t φ σ) := by
  have hLs := tl2fu_memLp_s D ht E.hφ
  have hLw := tl2fu_memLp_w D ht E.hφ
  have vv := tl2fu_cov_vv D ht ht E.hφ E.hφ
  have vw := tl2fu_cov_vw D ht ht E.hφ E.hφ
  have wv := tl2fu_cov_wv D ht ht E.hφ E.hφ
  have ww := tl2fu_cov_ww D ht ht E.hφ E.hφ
  rw [min_self] at vv vw wv ww
  have hx : ∀ σ ∈ Set.Icc (0 : ℝ) t, ∀ V, pullbackVec (HRS.Uniform.Comp28.plainData V) t σ (gfb4_ell m φ) =
      tl2fuPb V t (gfb4_ell m φ) σ := fun σ hσ V => (tl2fuPb_eq V _ hσ).symm
  have iV := tl2fu_form_int D ht (tl2fu_Pb_meas Vev D.hVc ht (gfb4_ell m φ)) (tl2fu_Pb_meas Vev D.hVc ht (gfb4_ell m φ))
    (fun σ _ => tl2fu_Pb_norm Vev D.hVb D.hK ht _ σ) (fun σ _ => tl2fu_Pb_norm Vev D.hVb D.hK ht _ σ)
  have iVW := tl2fu_form_int D ht (tl2fu_Pb_meas Vev D.hVc ht (gfb4_ell m φ)) (tl2fu_Pb_meas Wev D.hWc ht (gfb4_ell m φ))
    (fun σ _ => tl2fu_Pb_norm Vev D.hVb D.hK ht _ σ) (fun σ _ => tl2fu_Pb_norm Wev D.hWb D.hK ht _ σ)
  have iWV := tl2fu_form_int D ht (tl2fu_Pb_meas Wev D.hWc ht (gfb4_ell m φ)) (tl2fu_Pb_meas Vev D.hVc ht (gfb4_ell m φ))
    (fun σ _ => tl2fu_Pb_norm Wev D.hWb D.hK ht _ σ) (fun σ _ => tl2fu_Pb_norm Vev D.hVb D.hK ht _ σ)
  have iW := tl2fu_form_int D ht (tl2fu_Pb_meas Wev D.hWc ht (gfb4_ell m φ)) (tl2fu_Pb_meas Wev D.hWc ht (gfb4_ell m φ))
    (fun σ _ => tl2fu_Pb_norm Wev D.hWb D.hK ht _ σ) (fun σ _ => tl2fu_Pb_norm Wev D.hWb D.hK ht _ σ)
  have conv : ∀ (V₁ V₂ : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m),
      ∫ σ in Set.Icc 0 t, Cd σ (pullbackVec (HRS.Uniform.Comp28.plainData V₁) t σ (gfb4_ell m φ))
        (pullbackVec (HRS.Uniform.Comp28.plainData V₂) t σ (gfb4_ell m φ)) =
      ∫ σ in Set.Icc 0 t, Cd σ (tl2fuPb V₁ t (gfb4_ell m φ) σ) (tl2fuPb V₂ t (gfb4_ell m φ) σ) :=
    fun V₁ V₂ => setIntegral_congr_fun measurableSet_Icc fun σ hσ => by
      rw [hx σ hσ V₁, hx σ hσ V₂]
  rw [conv] at vv vw wv ww
  -- (Xa - Xb) * Xs and (Xa - Xb) * Xw
  have c1 := tl2fu_cov_left (P := P) (s := t) (Cd := Cd) hLs hLw hLs vv wv iV iWV
  have c2 := tl2fu_cov_left (P := P) (s := t) (Cd := Cd) hLs hLw hLw vw ww iVW iW
  have e : ∀ ω, (NegSobolev.eval (Zs t ω) φ - NegSobolev.eval (Zw t ω) φ) *
        (NegSobolev.eval (Zs t ω) φ - NegSobolev.eval (Zw t ω) φ) =
      (NegSobolev.eval (Zs t ω) φ - NegSobolev.eval (Zw t ω) φ) * NegSobolev.eval (Zs t ω) φ -
      (NegSobolev.eval (Zs t ω) φ - NegSobolev.eval (Zw t ω) φ) * NegSobolev.eval (Zw t ω) φ :=
    fun ω => by ring
  simp_rw [e]
  have hAs : Integrable (fun ω => (NegSobolev.eval (Zs t ω) φ - NegSobolev.eval (Zw t ω) φ) *
      NegSobolev.eval (Zs t ω) φ) P := (hLs.sub hLw).integrable_mul hLs
  have hAw : Integrable (fun ω => (NegSobolev.eval (Zs t ω) φ - NegSobolev.eval (Zw t ω) φ) *
      NegSobolev.eval (Zw t ω) φ) P := (hLs.sub hLw).integrable_mul hLw
  rw [integral_sub hAs hAw, c1, c2]
  have j1 : IntegrableOn (fun σ => Cd σ (tl2fuPb Vev t (gfb4_ell m φ) σ - tl2fuPb Wev t (gfb4_ell m φ) σ)
      (tl2fuPb Vev t (gfb4_ell m φ) σ)) (Set.Icc 0 t) := by
    simp only [map_sub, ContinuousLinearMap.sub_apply]; exact iV.sub iWV
  have j2 : IntegrableOn (fun σ => Cd σ (tl2fuPb Vev t (gfb4_ell m φ) σ - tl2fuPb Wev t (gfb4_ell m φ) σ)
      (tl2fuPb Wev t (gfb4_ell m φ) σ)) (Set.Icc 0 t) := by
    simp only [map_sub, ContinuousLinearMap.sub_apply]; exact iVW.sub iW
  rw [← integral_sub j1 j2]
  refine setIntegral_congr_fun measurableSet_Icc fun σ hσ => ?_
  rw [tl2fuA_eq]
  simp only [map_sub]

end Cov

end HRS.ThermLin.Plan2
