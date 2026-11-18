import HRS.MS.S111K4R6
import HRS.MS.S111K4Q5
import HRS.Whole.Window
import HRS.MS.S111K4V07

/-!
# S11.1 / V02 (S11K4): `stationary_cubic_reinterpretation` (Pro `R26-T6C.V07/V08`), concrete assembly

For the thermal reference and `γ = β`, the cubic tensor of the window `[0,T]` is the cubic tensor of the window `[u,u+T]`.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S111K4

open HRS HRS.Whole
open HRS.MS.S111X2
open HRS.MS.TcR (tc2_integrable_nu tc2_integral_nu)
open HRS.MS.S111X1 (KData)

variable {d : ℕ}

/-- Responses (with `C_b²` representatives) of the orbit data `U^{r,t}φ`, `0 ≤ r ≤ t`. -/
theorem k4_resp_exists (hd : 2 ≤ d) (s a β : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (ha : 0 < a)
    (hβ : 0 < β) (ρ : Euc d → ℝ) (hρ : IsThermalEquilibrium d s a β ρ) {t r : ℝ} (ht : 0 ≤ t)
    (hr : r ∈ Icc (0 : ℝ) t) {φ : Euc d → ℝ} (hφ : IsOscTest (wholeSpaceIndex d) φ) :
    ∃ h : Euc d → ℝ, HRS.Whole.IsResponse (HRS.Whole.rieszKernel d s) (HRS.Whole.withDensityReal ρ) β
      (propagatorW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) r t φ) h ∧ MemCb 2 h := by
  obtain ⟨Cr, -, hCr⟩ := k4_resp_rep hd s a β hs0 hs ha hβ ρ hρ
  obtain ⟨F, hF⟩ := HRS.MS.S111X1.exist_of_thermal hd hs0 hs ha hβ hρ t ht φ hφ
  have hp : propagatorW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) r t φ = F r :=
    s111x2_prop_eq hd hs0 hs ha hβ hρ ht hF hr
  obtain ⟨Bf, hBf⟩ := k4_cb_of_classical hF
  obtain ⟨h, h1, h2, -⟩ := hCr (F r) (hBf r hr).1
  exact ⟨h, by rw [hp]; exact h1, h2⟩


theorem k4_v02 (hd : 2 ≤ d) (s a β : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (ha : 0 < a) (hβ : 0 < β)
    (T : ℝ) (u : ℝ) (hu : 0 ≤ u) (ρ : Euc d → ℝ) (hρ : IsThermalEquilibrium d s a β ρ)
    (Kb : projTensor (R2X d T) 3) (hKb : IsR2PathCubic d s a β β ρ T 0 Kb) :
    IsR2PathCubic d s a β β ρ T u Kb := by
  classical
  obtain ⟨hsym, hex0, hform0⟩ := hKb
  obtain ⟨M, TD⟩ := s111x2_td_of_thermal hd hs0 hs ha hβ hρ
  haveI := HRS.Whole.Q34.isProbabilityMeasure_nu TD.prob
  set ν := HRS.Whole.withDensityReal ρ with hν
  set C := (quadraticGradientDyn d s a β).coeff (fun _ => ρ) with hC
  have hKd := TD.en.K
  have hex := HRS.MS.S111X1.exist_of_thermal hd hs0 hs ha hβ hρ
  have hpos : ∀ x, 0 < ρ x := TD.pos
  have hτ0 : ∀ τ : Fin 3 → Icc (0 : ℝ) T, ∀ i, 0 ≤ (τ i : ℝ) := fun τ i => (τ i).2.1
  have hτT : ∀ τ : Fin 3 → Icc (0 : ℝ) T, ∀ i, (τ i : ℝ) ≤ T := fun τ i => (τ i).2.2
  unfold IsR2PathCubic
  refine ⟨hsym, ?_, ?_⟩
  · -- existence of the cross-covariance densities on the window `[u, u+T]`
    intro τ φ hφ
    obtain ⟨χ0, hχ0⟩ := hex0 τ φ hφ
    have hrep : ∀ j : Fin 3, ∀ r : ℝ, ∃ h : Euc d → ℝ, r ∈ Icc (0 : ℝ) u →
        (HRS.Whole.IsResponse (HRS.Whole.rieszKernel d s) ν β
          (propagatorW C r (u + (τ j : ℝ)) (φ j)) h ∧ MemCb 2 h) := by
      intro j r
      by_cases hr : r ∈ Icc (0 : ℝ) u
      · obtain ⟨h, hh⟩ := k4_resp_exists hd s a β hs0 hs ha hβ ρ hρ (t := u + (τ j : ℝ))
          (by linarith [hτ0 τ j]) (r := r) ⟨hr.1, hr.2.trans (by linarith [hτ0 τ j])⟩ (hφ j)
        exact ⟨h, fun _ => hh⟩
      · exact ⟨0, fun h => absurd h hr⟩
    choose hh hhspec using hrep
    refine ⟨fun j r => if r < u then (fun x => ρ x * hh j r x) else χ0 j (r - u), ?_⟩
    intro j r hr
    by_cases hru : r < u
    · have hr0 : r ∈ Icc (0 : ℝ) u := ⟨hr.1, hru.le⟩
      obtain ⟨hresp, hcb⟩ := hhspec j r hr0
      have hhm : MemLp (hh j r) 2 ν := HRS.MS.Tc5.tc5_memLp_of_cb hcb
      simp only [hru, if_true]
      refine ⟨?_, fun ψ hψ => ?_⟩
      · have : (fun x => ρ x * hh j r x / ρ x) = hh j r := by
          funext x
          rw [mul_div_cancel_left₀ _ (hpos x).ne']
        rw [this]
        exact hhm
      · have := k4_cross_core hd s a β hs0 hs ha hβ ρ hρ hr.1 (by linarith [hτ0 τ j, hru] : r ≤ u + (τ j : ℝ))
          (hφ j) hresp hhm hψ
        exact this
    · push_neg at hru
      have hra : r - u ∈ Icc (0 : ℝ) (0 + T) := ⟨by linarith, by linarith [hr.2]⟩
      obtain ⟨hm, hcov⟩ := hχ0 j (r - u) hra
      simp only [not_lt.2 hru, if_false]
      refine ⟨hm, fun ψ hψ => ?_⟩
      obtain ⟨hi, he⟩ := hcov ψ hψ
      refine ⟨hi, ?_⟩
      have hsh := k4_lgc_shift hd s a β hs0 hs ha hβ ρ hρ hu (r := r - u) (t := (τ j : ℝ))
        (by linarith [hr.1, hru]) (hτ0 τ j) hψ (hφ j)
      rw [show u + (r - u) = r by ring] at hsh
      rw [he, zero_add, ← hsh]
  · -- the formula
    intro τ φ hφ χ hχ M' hM'
    obtain ⟨χ0, hχ0⟩ := hex0 τ φ hφ
    obtain ⟨hk1, hk2⟩ := hform0 τ φ hφ χ0 hχ0 M' hM'
    have e0 : (fun i => (0 : ℝ) + (τ i : ℝ)) = fun i => (τ i : ℝ) := funext fun i => zero_add _
    rw [e0] at hk1 hk2
    obtain ⟨h1, h2⟩ := k4_v07 hd s a β T u hs0 hs ha hβ hu ρ hρ τ φ hφ χ χ0 hχ hχ0 hk2
    exact ⟨hk1.trans h1.symm, h2⟩

end HRS.MS.S111K4
