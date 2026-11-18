import HRS.MC.CepE5bAux13
import HRS.MC.CepE5bAux14

/-!
# Packet CEPE5B, auxiliary 15: the per-`n` bound for the defect of the original solutions
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace

noncomputable section

namespace HRS.MC.CepE5b

open HRS HRS.MC.Cepa HRS.MC.CepE4

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {N : ℕ}

/-- The constants of the Lyapunov estimate: `K1`. -/
def e5b_K1 (a : ℝ) (N : ℕ) : ℝ := 2 * Real.pi * a * (N : ℝ) ^ 2

/-- `cF1`. -/
def e5b_cF1 (F : Ch N → Ch N) : ℝ := (1 / 2) * ‖F (e4_rho N)‖ ^ 2

/-- `cF2`. -/
def e5b_cF2 (L : ℝ≥0) : ℝ := 1 + 2 * (L : ℝ)

/-- The second-moment constant. -/
def e5b_Mc (N : ℕ) (R ρn σ' T K1 cF1 cF2 : ℝ) : ℝ :=
  Real.exp (cF2 * T) * (((1 / 2) * (R + ρn) ^ 2 + (1 / 2) * σ' ^ 2 * (N * T)) + (K1 + cF1) * T)

/-- The Lyapunov-integral constant. -/
def e5b_Bc (N : ℕ) (R ρn σ' T K1 cF1 cF2 : ℝ) : ℝ :=
  (1 / 2) * (R + ρn) ^ 2 + (1 / 2) * σ' ^ 2 * (N * T) + cF1 * T +
    cF2 * e5b_Mc N R ρn σ' T K1 cF1 cF2 * T

theorem e5b_perN [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ}
    {W' : ℝ≥0 → Ω → (Fin N × Fin 1) → ℝ} (hW' : IsBrownianFiltration P ℱ W')
    {π : Ω → Equiv.Perm (Fin N)} (hπ : ∀ σ, MeasurableSet[ℱ 0] {ω | π ω = σ})
    {a : ℝ} (ha : 0 < a) {J : ℝ → Ch N → Ch N} (hJ : cep_Yosida a N J)
    {F : Ch N → Ch N} {L : ℝ≥0} (hF : LipschitzWith L F) (σ' : ℝ)
    {z₀ : Ω → Ch N} (hz₀ : Measurable[ℱ 0] z₀) {R : ℝ} (hR : ∀ ω, ‖z₀ ω‖ ≤ R)
    {Z : ℕ → ℝ → Ω → Ch N}
    (hZ : ∀ n : ℕ, 1 ≤ n → cep_IsChamberSolution P ℱ W' π σ'
      (fun z => -((n : ℝ) • (z - J n z)) + F z) z₀ (Z n)) (T : ℝ) (hT : 0 ≤ T)
    {n : ℕ} (hn : 1 ≤ n) {r : ℝ} (hr : 0 < r) (hr2 : r ≤ 1 / 2) :
    ∫ ω, (∫ s in (0 : ℝ)..T, (1 / (n : ℝ)) * ‖(n : ℝ) • (Z n s ω - J n (Z n s ω))‖ ^ 2) ∂P ≤
      (1 / (n : ℝ)) * (2 * (∫ ω, e5b_Pn a N J n (z₀ ω) ∂P +
          (a / N) * HRS.MC.CepE2.cepe2_npairs N * Real.log 2) +
        ((2 * ‖F 0‖ ^ 2 + 4 * (L : ℝ) ^ 2 * ‖e4_rho N‖ ^ 2) * T +
          8 * (L : ℝ) ^ 2 * (e5b_Mc N R ‖e4_rho N‖ σ' T (e5b_K1 a N) (e5b_cF1 F) (e5b_cF2 L) * T)) +
        σ' ^ 2 * (((n : ℝ) * (8 * (N : ℝ) ^ 3 * r / (a * Real.pi))) *
            e5b_Bc N R ‖e4_rho N‖ σ' T (e5b_K1 a N) (e5b_cF1 F) (e5b_cF2 L) +
          ((n : ℝ) * (16 * (N : ℝ) ^ 5 * r) + 2 * a * Real.pi ^ 2 * N / r ^ 2) * T)) := by
  classical
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨hZc, hZF, heq⟩ := hZ n hn
  set nR : ℝ := (n : ℝ) with hnR
  set ρ : Ch N := e4_rho N with hρ
  set G : Ch N → Ch N := e5b_G J nR with hGdef
  have hGc : Continuous G := e5b_G_cont hJ hnpos
  have hFc : Continuous F := hF.continuous
  have hGb : ∀ z, ‖G z‖ ≤ ‖G 0‖ + nR * ‖z‖ := e5b_G_growth hJ hnpos
  have hFb : ∀ z, ‖F z‖ ≤ ‖F 0‖ + (L : ℝ) * ‖z‖ := e4_lip_growth hF
  have hLp : (0 : ℝ) ≤ L := L.2
  have hBc : Continuous fun z => -G z + F z := hGc.neg.add hFc
  have hBb : ∀ z, ‖-G z + F z‖ ≤ (‖G 0‖ + ‖F 0‖) + (nR + L) * ‖z‖ := fun z => by
    have h1 := norm_add_le (-G z) (F z)
    rw [norm_neg] at h1
    have h2 := hGb z
    have h3 := hFb z
    nlinarith
  obtain ⟨A, hS⟩ := e4_setup_of_solution hW' hπ (σ' := σ') hR hBc (by positivity) (by positivity) hBb
    (Z := Z n) hZc hZF heq hT
  have hS' : E4Setup P ℱ N T σ' (cep_noise π W') (e4_clamp (Z n)) A := hS
  have heq' : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → e4_clamp (Z n) t ω = z₀ ω +
      (∫ s in (0 : ℝ)..t, (-G (e4_clamp (Z n) s ω) + F (e4_clamp (Z n) s ω))) +
        σ' • cep_noise π W' t ω := by
    filter_upwards [heq] with ω hω t ht
    have e1 : e4_clamp (Z n) t ω = Z n t ω := by simp [e4_clamp, max_eq_left ht]
    rw [e1, hω t ht]
    congr 2
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [Set.uIcc_of_le ht] at hs
    simp [e4_clamp, max_eq_left hs.1, hGdef, e5b_G]
  have hK1p : 0 ≤ e5b_K1 a N := by unfold e5b_K1; have := Real.pi_pos; positivity
  have hc1p : 0 ≤ e5b_cF1 F := by unfold e5b_cF1; positivity
  have hc2p : 0 ≤ e5b_cF2 L := by unfold e5b_cF2; positivity
  obtain ⟨hIG, hIq⟩ := e5b_lyap hS' hz₀ hR ρ hGc hFc (norm_nonneg _) hnpos.le (norm_nonneg _) hLp hGb hFb
    heq' hK1p hc1p hc2p
    (fun z => by
      have := (e4_yosida_pointwise ha hJ hnpos z).1
      simpa [hGdef, e5b_G, e5b_K1] using this)
    (fun z => by
      have := e4_F_pointwise hF ρ z
      simpa [e5b_cF1, e5b_cF2, hρ] using this) hT
  have hstep := e5b_step hW' hπ ha hJ hF hnpos hS' hT hz₀ hR heq'
    (B1 := e5b_Bc N R ‖ρ‖ σ' T (e5b_K1 a N) (e5b_cF1 F) (e5b_cF2 L))
    (M := e5b_Mc N R ‖ρ‖ σ' T (e5b_K1 a N) (e5b_cF1 F) (e5b_cF2 L)) hIG hIq hr hr2
  have hL : ∀ ω, (∫ s in (0 : ℝ)..T, (1 / nR) * ‖nR • (Z n s ω - J nR (Z n s ω))‖ ^ 2) =
      (1 / nR) * ∫ s in (0 : ℝ)..T, ‖G (e4_clamp (Z n) s ω)‖ ^ 2 := by
    intro ω
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [Set.uIcc_of_le hT] at hs
    simp [e4_clamp, max_eq_left hs.1, hGdef, e5b_G]
  simp_rw [hL]
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left hstep (by positivity)

end HRS.MC.CepE5b
