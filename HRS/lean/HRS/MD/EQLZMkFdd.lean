import HRS.MD.EQLZMkMarkov

/-!
# EQ-LZ packet MK-2: finite-dimensional distributions of the level-`lev` flow (`eqlz_mk_fdd`), proof

Induction on the list of (gap, function) pairs, for a bounded `ℱ_s`-measurable weight `h` instead of `g₀(Z_0)`:
`E[h ∏ g_i(Z_{s+δ_1+...+δ_i})] = E[h · fddKer l (Z_s)]`.  The inductive step multiplies `h` by `g_1(Z_{s+δ_1})`
(`ℱ_{s+δ_1}`-measurable), applies the induction hypothesis at time `s+δ_1`, and the Markov property
(`eqlz_mk_markov_proof`) with the smooth function `g_1 · fddKer l` to come back to time `s`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal
open HRS HRS.MD.EQLZ

namespace HRS.MD.EQLZMk

variable {d N n : ℕ}

theorem lzmk_smooth_const (c : ℝ) : Torus.IsSmooth (fun _ : Torus n => c) := by
  unfold Torus.IsSmooth Torus.IsCk Torus.lift
  exact contDiff_const

theorem lzmk_smooth_mul {ψ₁ ψ₂ : Torus n → ℝ} (h₁ : Torus.IsSmooth ψ₁) (h₂ : Torus.IsSmooth ψ₂) :
    Torus.IsSmooth (fun x => ψ₁ x * ψ₂ x) := by
  have e1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift ψ₁) := h₁
  have e2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift ψ₂) := h₂
  exact e1.mul e2

theorem lzmk_bdd {g : Torus n → ℝ} (hg : Continuous g) : ∃ C : ℝ, ∀ x, |g x| ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_univ (X := Torus n)).exists_bound_of_continuousOn hg.continuousOn
  exact ⟨C, fun x => by simpa using hC x (Set.mem_univ x)⟩

/-- The iterated kernel of an admissible list is smooth (given smoothness of `P_t` on smooth data). -/
theorem lzmk_fddKer_smooth (hn : 1 ≤ n) {κ : ℝ} (hκ : 0 < κ) {U : Torus n → ℝ} (hU : Torus.IsSmooth U)
    (hsm : ∀ t : ℝ, 0 ≤ t → ∀ φ : Torus n → ℝ, Torus.IsSmooth φ → Torus.IsSmooth (d1_P hn hκ hU t φ)) :
    ∀ l : List (ℝ × (Torus n → ℝ)), (∀ p ∈ l, 0 ≤ p.1 ∧ Torus.IsSmooth p.2) →
      Torus.IsSmooth (fddKer hn hκ hU l)
  | [], _ => by
    show Torus.IsSmooth (fun _ : Torus n => (1 : ℝ))
    exact lzmk_smooth_const 1
  | p :: l, hl => by
    have hp := hl p (List.mem_cons_self)
    have hrest := lzmk_fddKer_smooth hn hκ hU hsm l (fun q hq => hl q (List.mem_cons_of_mem _ hq))
    exact hsm p.1 hp.1 _ (lzmk_smooth_mul hp.2 hrest)

section Flow

variable (hNd : 1 ≤ N * d) (D : DynData d) (hM : D.M = -(1 : Matrix (Fin d) (Fin d) ℝ))
    (hV : Torus.IsSmooth D.V) (hβ : 0 < D.invβ) (lev : ℝ)
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℝ mΩ) (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ) (Y₀ : Ω → Fin N → Euc d)
    (Y : ℝ → Ω → Fin N → Euc d) (hY : IsLevelFlow D lev P ℱ W' Y₀ Y)

include hM hY in
theorem lzmk_markov_mul {ψ : Torus (N * d) → ℝ} (hψ : Torus.IsSmooth ψ) {s a : ℝ} (hs : 0 ≤ s) (hsa : s ≤ a)
    {h : Ω → ℝ} (hh : Measurable[ℱ s] h) (hbd : ∃ C : ℝ, ∀ ω, |h ω| ≤ C) :
    ∫ ω, h ω * ψ (levelProc Y a ω) ∂P =
      ∫ ω, h ω * d1_P hNd hβ (b15d_U_isSmooth_proof (N := N) D hV lev) (a - s) ψ (levelProc Y s ω) ∂P := by
  obtain ⟨C, hC⟩ := hbd
  have hψc : Continuous ψ := StaticLimitAux.continuous_of_smooth hψ
  have hZa : Measurable (levelProc Y a) := (lzmk_levelProc_meas hY.sol.adapted a).mono (ℱ.le a) le_rfl
  have hG : Integrable (fun ω => ψ (levelProc Y a ω)) P := lzmk_integrable_comp hψc hZa
  have hhm : Measurable h := hh.mono (ℱ.le s) le_rfl
  have hhG : Integrable (h * fun ω => ψ (levelProc Y a ω)) P :=
    hG.bdd_mul (c := C) hhm.aestronglyMeasurable (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hC ω)
  have h1 := condExp_mul_of_stronglyMeasurable_left (m := ℱ s) (μ := P) hh.stronglyMeasurable hhG hG
  have h2 := eqlz_mk_markov_proof hNd D hM hV hβ lev P ℱ W' Y₀ Y hY hψ hs hsa
  calc ∫ ω, h ω * ψ (levelProc Y a ω) ∂P
      = ∫ ω, (P[h * fun ω => ψ (levelProc Y a ω) | ℱ s]) ω ∂P := (integral_condExp (ℱ.le s)).symm
    _ = ∫ ω, (h * P[fun ω => ψ (levelProc Y a ω) | ℱ s]) ω ∂P := integral_congr_ae h1
    _ = ∫ ω, h ω * d1_P hNd hβ (b15d_U_isSmooth_proof (N := N) D hV lev) (a - s) ψ (levelProc Y s ω) ∂P := by
      refine integral_congr_ae ?_
      filter_upwards [h2] with ω hω
      simp only [Pi.mul_apply, hω]

include hM hY in
theorem lzmk_fdd_claim
    (hsm : ∀ t : ℝ, 0 ≤ t → ∀ φ : Torus (N * d) → ℝ, Torus.IsSmooth φ →
      Torus.IsSmooth (d1_P hNd hβ (b15d_U_isSmooth_proof (N := N) D hV lev) t φ)) :
    ∀ l : List (ℝ × (Torus (N * d) → ℝ)), (∀ p ∈ l, 0 ≤ p.1 ∧ Torus.IsSmooth p.2) →
      ∀ s : ℝ, 0 ≤ s → ∀ h : Ω → ℝ, Measurable[ℱ s] h → (∃ C : ℝ, ∀ ω, |h ω| ≤ C) →
        ∫ ω, h ω * fddProd (levelProc Y) s l ω ∂P =
          ∫ ω, h ω * fddKer hNd hβ (b15d_U_isSmooth_proof (N := N) D hV lev) l (levelProc Y s ω) ∂P := by
  intro l
  induction l with
  | nil =>
    intro _ s _ h _ _
    simp [fddProd, fddKer]
  | cons p l ih =>
    intro hl s hs h hh hbd
    have hp := hl p List.mem_cons_self
    have hl' : ∀ q ∈ l, 0 ≤ q.1 ∧ Torus.IsSmooth q.2 := fun q hq => hl q (List.mem_cons_of_mem _ hq)
    have hKs := lzmk_fddKer_smooth hNd hβ (b15d_U_isSmooth_proof (N := N) D hV lev) hsm l hl'
    have hpc : Continuous p.2 := StaticLimitAux.continuous_of_smooth hp.2
    obtain ⟨Cp, hCp⟩ := lzmk_bdd hpc
    obtain ⟨C, hC⟩ := hbd
    have hsa : s ≤ s + p.1 := by linarith [hp.1]
    have ha : 0 ≤ s + p.1 := by linarith [hp.1]
    -- the weight at time `a = s + δ`
    have hh' : Measurable[ℱ (s + p.1)] (fun ω => h ω * p.2 (levelProc Y (s + p.1) ω)) :=
      (hh.mono (ℱ.mono hsa) le_rfl).mul (hpc.measurable.comp (lzmk_levelProc_meas hY.sol.adapted _))
    have hbd' : ∃ C' : ℝ, ∀ ω, |h ω * p.2 (levelProc Y (s + p.1) ω)| ≤ C' :=
      ⟨C * Cp, fun ω => by
        rw [abs_mul]
        exact mul_le_mul (hC ω) (hCp _) (abs_nonneg _) ((abs_nonneg _).trans (hC ω))⟩
    have step1 := ih hl' (s + p.1) ha _ hh' hbd'
    have step2 := lzmk_markov_mul hNd D hM hV hβ lev P ℱ W' Y₀ Y hY
      (lzmk_smooth_mul hp.2 hKs) hs hsa hh ⟨C, hC⟩
    have e1 : ∫ ω, h ω * fddProd (levelProc Y) s (p :: l) ω ∂P =
        ∫ ω, (h ω * p.2 (levelProc Y (s + p.1) ω)) * fddProd (levelProc Y) (s + p.1) l ω ∂P := by
      refine integral_congr_ae (ae_of_all _ fun ω => ?_)
      simp only [fddProd]
      ring
    rw [e1, step1]
    have e2 : ∫ ω, (h ω * p.2 (levelProc Y (s + p.1) ω)) *
        fddKer hNd hβ (b15d_U_isSmooth_proof (N := N) D hV lev) l (levelProc Y (s + p.1) ω) ∂P =
        ∫ ω, h ω * ((fun x => p.2 x * fddKer hNd hβ (b15d_U_isSmooth_proof (N := N) D hV lev) l x)
          (levelProc Y (s + p.1) ω)) ∂P := by
      refine integral_congr_ae (ae_of_all _ fun ω => ?_)
      simp only
      ring
    rw [e2, step2, show s + p.1 - s = p.1 by ring]
    rfl

end Flow

/-- (MK-2, `eqlz_mk_fdd`.)  Statement copied verbatim from `HRS.MD.EQLZ.eqlz_mk_fdd`. -/
theorem eqlz_mk_fdd_proof (hNd : 1 ≤ N * d) (D : DynData d) (hM : D.M = -(1 : Matrix (Fin d) (Fin d) ℝ))
    (hV : Torus.IsSmooth D.V) (hβ : 0 < D.invβ) (lev : ℝ)
    (hsm : ∀ t : ℝ, 0 ≤ t → ∀ φ : Torus (N * d) → ℝ, Torus.IsSmooth φ →
      Torus.IsSmooth (d1_P hNd hβ (b15d_U_isSmooth_proof (N := N) D hV lev) t φ))
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℝ mΩ) (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ) (Y₀ : Ω → Fin N → Euc d)
    (Y : ℝ → Ω → Fin N → Euc d) (hY : IsLevelFlow D lev P ℱ W' Y₀ Y) :
    HasFDD hNd hβ (b15d_U_isSmooth_proof (N := N) D hV lev) P (levelProc Y) (P.map (levelProc Y 0)) := by
  intro l hl g₀ hg₀ hbd
  have hKs := lzmk_fddKer_smooth hNd hβ (b15d_U_isSmooth_proof (N := N) D hV lev) hsm l hl
  have hKc : Continuous (fddKer hNd hβ (b15d_U_isSmooth_proof (N := N) D hV lev) l) :=
    StaticLimitAux.continuous_of_smooth hKs
  have hZ0 : Measurable[ℱ 0] (levelProc Y 0) := lzmk_levelProc_meas hY.sol.adapted 0
  have hZ0' : Measurable (levelProc Y 0) := hZ0.mono (ℱ.le 0) le_rfl
  have h1 := lzmk_fdd_claim hNd D hM hV hβ lev P ℱ W' Y₀ Y hY hsm l hl 0 le_rfl
    (fun ω => g₀ (levelProc Y 0 ω)) (hg₀.comp hZ0)
    (by obtain ⟨C, hC⟩ := hbd; exact ⟨C, fun ω => hC _⟩)
  rw [h1]
  exact (integral_map (f := fun x => g₀ x * fddKer hNd hβ (b15d_U_isSmooth_proof (N := N) D hV lev) l x)
    hZ0'.aemeasurable (hg₀.mul hKc.measurable).aestronglyMeasurable).symm

end HRS.MD.EQLZMk

end
