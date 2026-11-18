import HRS.MS.FcauAux2
import HRS.MS.UniqG2
import HRS.MS.UniqC1c

/-!
# F-CAU: uniqueness of classical adjoint solutions and of `propagatorW`

New infrastructure statements (no manuscript row; consumers S5.3, S5.5, S5.6, S6.7, S6.11).

* `propagatorW_isClassical`: if some classical adjoint solution with terminal datum `φ` exists, then
  `r ↦ propagatorW C r t φ` is one (no hypothesis on `C`).
* `propagatorW_unique`: two classical adjoint solutions (`IsClassicalAdjointW`, i.e. of class `C_b²`)
  with the same terminal datum agree on `[0,t]`; `propagatorW_eq`: hence `propagatorW C r t φ = f r`
  for every classical solution `f`.
  Hypotheses: the coefficient hypotheses of S.A.33 (`CoeffHypRd`, `VHypRd`, `MatBound`, viscosity range)
  and one of its regimes (`RdRegimeHolds`: R1, R2a, R2c, R3).  They are exactly those of
  `uloc_uniqueness` and are NOT implied by the standing hypotheses `WholeSetup` of S5 (which records
  no regime): see the report.

Not provided: `oscAdjointInput_of_ulAdjointInput` (derivation of `OscAdjointInput`, `HRS/Whole/Orbits.lean`).
Uniqueness gives `U^{r,t} φ = f(r)` for every classical solution, but the Duhamel identity
`U^{r,t}φ_α - φ_α = ∫_r^t U^{r,s} 𝓛_sφ_α ds` also needs differentiability of `s ↦ U^{r,s}φ_α`
(stability in the terminal time), and the `feature` field needs `ℓ²`-summability over the Hermite
index `α` of `∂_a U^{r,t}𝓛_tφ_α`, neither of which follows from `UlAdjointInput` (bounds in `C_b^j`
for one datum at a time).

Route: the difference `w = f₁ - f₂` is a classical solution with terminal datum `0`; its time reversal
`z(σ) = w(t-σ)` is in `L^∞([0,t];H¹_uloc)` (`fcau_ul_bound`) and a distributional solution of the
forward equation (`fcau_slice`: integration by parts of the local terms and of the nonlocal term
with the cancellation convention, `fcau_nonlocal_duality`; time integration `fcau_ftc_integral`),
so `uloc_uniqueness_proof` (`HRS/MS/UniqG2.lean`) gives `z = 0`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal ContDiff

namespace HRS.MS.Fcau

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.DualityRd HRS.MP.RdGen

variable {d : ℕ}

/-! ### `propagatorW` is a classical solution when one exists -/

/-- If a classical adjoint solution exists, `r ↦ propagatorW C r t φ` is one. -/
theorem propagatorW_isClassical {C : WholeCoeff d} {t : ℝ} {φ : Euc d → ℝ}
    (h : ∃ f, IsClassicalAdjointW C t φ f) :
    IsClassicalAdjointW C t φ (fun r => propagatorW C r t φ) := by
  have : (fun r => propagatorW C r t φ) = h.choose := by
    funext r; unfold propagatorW; rw [dif_pos h]
  rw [this]
  exact h.choose_spec

/-! ### The slice hypotheses -/

theorem fcau_weightedSupE_mono {k k' : ℕ} (hk : k ≤ k') (L : ℝ) (f : Euc d → ℝ) :
    weightedSupE k L f ≤ weightedSupE k' L f := by
  unfold weightedSupE derivSupE
  refine iSup_le fun j => iSup_le fun i => iSup_le fun x => ?_
  exact le_iSup_of_le (⟨j, by omega⟩ : Fin (k' + 1)) (le_iSup_of_le i (le_iSup_of_le x le_rfl))

/-- The regularity of the density slices and of the drift used by the slice identity. -/
def FcauSlices (D : WholeDyn d) (ρ : ℝ → Euc d → ℝ) (t : ℝ) : Prop :=
  ∀ r ∈ Set.Icc (0 : ℝ) t, RegSliceRd (ρ r) ∧
    ∀ i : Fin d, ContDiff ℝ 1 (fun y => meanFieldDriftW D (ρ r) y i)

theorem fcau_slices_of_hyp (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) (hm : 1 ≤ m)
    (MB Λ ΛV G₀ : ℝ) {D : WholeDyn d} {ρ : ℝ → Euc d → ℝ} {T : ℝ} (hDs : D.s = s)
    (hMB : HRS.PDE.MatBound MB D.M) (hV : VHypRd (m + 3) ΛV G₀ D.V)
    (hcoef : CoeffHypRd s m Λ T ρ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    FcauSlices D ρ t := by
  intro r hr
  have hrT : r ∈ Set.Icc (0 : ℝ) T := ⟨hr.1, hr.2.trans ht.2⟩
  refine ⟨?_, fun i => ?_⟩
  · obtain ⟨hcb, hfin, -⟩ := hcoef.regular.1 r hrT
    refine ⟨hcoef.prob r hrT, ⟨hcb.1.of_le (by exact_mod_cast (by omega : 3 ≤ m + 3)),
      fun j hj => hcb.2 j (hj.trans (by omega))⟩, ?_⟩
    exact lt_of_le_of_lt (fcau_weightedSupE_mono (by omega) _ _) hfin
  · have h := (HRS.MS.UniqC1.c1_drift_single hd hs0 hsd m MB Λ ΛV G₀ hDs hMB hV hcoef hrT).smooth
    have h1 : ContDiff ℝ 1 (meanFieldDriftW D (ρ r)) := h.of_le (by exact_mod_cast (by omega : 1 ≤ m + 1))
    exact (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).contDiff.comp h1

/-! ### Linearity of the generator on `C_b²` -/

theorem fcau_memCb_sub {f g : Euc d → ℝ} (hf : MemCb 2 f) (hg : MemCb 2 g) :
    MemCb 2 (fun x => f x - g x) := by
  refine ⟨hf.1.sub hg.1, fun j hj => ?_⟩
  obtain ⟨B₁, hB₁⟩ := hf.2 j hj
  obtain ⟨B₂, hB₂⟩ := hg.2 j hj
  refine ⟨B₁ + B₂, ?_⟩
  rintro _ ⟨x, rfl⟩
  have e : iteratedFDeriv ℝ j (fun x => f x - g x) x =
      iteratedFDeriv ℝ j f x - iteratedFDeriv ℝ j g x :=
    iteratedFDeriv_sub_apply (hf.1.of_le (by exact_mod_cast hj)).contDiffAt
      (hg.1.of_le (by exact_mod_cast hj)).contDiffAt
  show ‖iteratedFDeriv ℝ j (fun x => f x - g x) x‖ ≤ B₁ + B₂
  rw [e]
  exact (norm_sub_le _ _).trans (add_le_add (hB₁ ⟨x, rfl⟩) (hB₂ ⟨x, rfl⟩))

theorem fcau_gradient_sub {f g : Euc d → ℝ} (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) (y : Euc d) :
    gradient (fun x => f x - g x) y = gradient f y - gradient g y := by
  ext i
  rw [PiLp.sub_apply, q09_gradient_apply, q09_gradient_apply, q09_gradient_apply]
  rw [fderiv_fun_sub (hf.differentiable one_ne_zero y) (hg.differentiable one_ne_zero y)]
  rfl

theorem fcau_nl_sub (hd : 1 ≤ d) (D : WholeDyn d) (hs0 : 0 ≤ D.s) (hsd : D.s < d)
    {ρ' : Euc d → ℝ} (hρ' : RegSliceRd ρ') {u₁ u₂ : Euc d → ℝ} (h₁ : MemCb 2 u₁) (h₂ : MemCb 2 u₂)
    (x : Euc d) :
    nlTermRd D ρ' (fun y => u₁ y - u₂ y) x = nlTermRd D ρ' u₁ x - nlTermRd D ρ' u₂ x := by
  obtain ⟨C, hC0, hρW⟩ := dc1a_rho_rgW hd hρ'
  unfold nlTermRd
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hW : ∀ {u : Euc d → ℝ}, MemCb 2 u → ∃ c, 0 ≤ 2 ^ 1 * C * c ∧ RgW (fun y : Euc d =>
      (1 + ‖y‖) ^ (-((d : ℝ) + 1))) 1 (2 ^ 1 * C * c)
        (fun y => ρ' y * (Torus.matVec D.M.transpose (gradient u y)) j) := by
    intro u hu
    obtain ⟨c, hc0, hvW⟩ := dc1a_v_rgW hu D.M j
    exact ⟨c, mul_nonneg (mul_nonneg (by norm_num) hC0) hc0, dc1a_mul_rgW hC0 hc0 hρW hvW⟩
  obtain ⟨c₁, hc₁, hW₁⟩ := hW h₁
  obtain ⟨c₂, hc₂, hW₂⟩ := hW h₂
  obtain ⟨c₃, hc₃, hW₃⟩ := hW (fcau_memCb_sub h₁ h₂)
  have hfun : (fun y => ρ' y * (Torus.matVec D.M.transpose (gradient (fun x => u₁ x - u₂ x) y)) j) =
      fun y => ρ' y * (Torus.matVec D.M.transpose (gradient u₁ y)) j -
        ρ' y * (Torus.matVec D.M.transpose (gradient u₂ y)) j := by
    funext y
    rw [fcau_gradient_sub (h₁.1.of_le (by norm_num)) (h₂.1.of_le (by norm_num)) y]
    simp only [Torus.matVec, map_sub, PiLp.sub_apply]; ring
  rw [hfun] at hW₃ ⊢
  rw [dc1a_force_eq hd hs0 hsd hc₁ hW₁ x j, dc1a_force_eq hd hs0 hsd hc₂ hW₂ x j]
  rw [dc1a_force_eq hd hs0 hsd hc₃ hW₃ x j, ← integral_sub (dc1a_kernel_int hd hs0 hsd hc₁ hW₁
    (rgKerComp_ok hs0 j) x) (dc1a_kernel_int hd hs0 hsd hc₂ hW₂ (rgKerComp_ok hs0 j) x)]
  congr 1; funext z
  unfold movtr_R
  split_ifs <;> ring

theorem fcau_gen_sub (hd : 1 ≤ d) (D : WholeDyn d) (hs0 : 0 ≤ D.s) (hsd : D.s < d)
    (ρ : ℝ → Euc d → ℝ) (r : ℝ) (hρ : RegSliceRd (ρ r)) {u₁ u₂ : Euc d → ℝ} (h₁ : MemCb 2 u₁)
    (h₂ : MemCb 2 u₂) (x : Euc d) :
    generatorW (D.coeff ρ) r (fun y => u₁ y - u₂ y) x =
      generatorW (D.coeff ρ) r u₁ x - generatorW (D.coeff ρ) r u₂ x := by
  unfold generatorW
  show D.invβ * Laplacian.laplacian (fun y => u₁ y - u₂ y) x +
      inner ℝ (meanFieldDriftW D (ρ r) x) (gradient (fun y => u₁ y - u₂ y) x) -
        nlTermRd D (ρ r) (fun y => u₁ y - u₂ y) x =
      (D.invβ * Laplacian.laplacian u₁ x + inner ℝ (meanFieldDriftW D (ρ r) x) (gradient u₁ x) -
        nlTermRd D (ρ r) u₁ x) -
      (D.invβ * Laplacian.laplacian u₂ x + inner ℝ (meanFieldDriftW D (ρ r) x) (gradient u₂ x) -
        nlTermRd D (ρ r) u₂ x)
  rw [fcau_nl_sub hd D hs0 hsd hρ h₁ h₂ x,
    fcau_gradient_sub (h₁.1.of_le (by norm_num)) (h₂.1.of_le (by norm_num)) x, inner_sub_right]
  have := (h₁.1.contDiffAt (x := x)).laplacian_sub (h₂.1.contDiffAt (x := x))
  have e : Laplacian.laplacian (fun y => u₁ y - u₂ y) x =
      Laplacian.laplacian u₁ x - Laplacian.laplacian u₂ x := this
  rw [e]
  ring

/-- The difference of two classical adjoint solutions with the same terminal datum is a classical
adjoint solution with terminal datum `0`. -/
theorem fcau_sub (hd : 1 ≤ d) (D : WholeDyn d) (hs0 : 0 ≤ D.s) (hsd : D.s < d)
    (ρ : ℝ → Euc d → ℝ) (t : ℝ) (hS : FcauSlices D ρ t) {φ : Euc d → ℝ} {f₁ f₂ : ℝ → Euc d → ℝ}
    (h₁ : IsClassicalAdjointW (D.coeff ρ) t φ f₁) (h₂ : IsClassicalAdjointW (D.coeff ρ) t φ f₂) :
    IsClassicalAdjointW (D.coeff ρ) t 0 (fun r x => f₁ r x - f₂ r x) := by
  have hm₁ := fun r (hr : r ∈ Set.Icc (0 : ℝ) t) => h₁.isC12TestRd.memCb hr
  have hm₂ := fun r (hr : r ∈ Set.Icc (0 : ℝ) t) => h₂.isC12TestRd.memCb hr
  have hgs : ∀ r ∈ Set.Icc (0 : ℝ) t, ∀ x, generatorW (D.coeff ρ) r (fun y => f₁ r y - f₂ r y) x =
      generatorW (D.coeff ρ) r (f₁ r) x - generatorW (D.coeff ρ) r (f₂ r) x := fun r hr x =>
    fcau_gen_sub hd D hs0 hsd ρ r (hS r hr).1 (hm₁ r hr) (hm₂ r hr) x
  refine ⟨fun r hr => (h₁.c2 r hr).sub (h₂.c2 r hr), fun j hj => ?_, fun j hj => ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨B₁, hB₁⟩ := h₁.bdd j hj
    obtain ⟨B₂, hB₂⟩ := h₂.bdd j hj
    refine ⟨B₁ + B₂, fun r hr x => ?_⟩
    have e : iteratedFDeriv ℝ j (fun y => f₁ r y - f₂ r y) x =
        iteratedFDeriv ℝ j (f₁ r) x - iteratedFDeriv ℝ j (f₂ r) x :=
      iteratedFDeriv_sub_apply ((h₁.c2 r hr).of_le (by exact_mod_cast hj)).contDiffAt
        ((h₂.c2 r hr).of_le (by exact_mod_cast hj)).contDiffAt
    rw [e]
    exact (norm_sub_le _ _).trans (add_le_add (hB₁ r hr x) (hB₂ r hr x))
  · refine ((h₁.cont_c2 j hj).sub (h₂.cont_c2 j hj)).congr fun p => ?_
    exact (iteratedFDeriv_sub_apply ((h₁.c2 p.1 p.1.2).of_le (by exact_mod_cast hj)).contDiffAt
      ((h₂.c2 p.1 p.1.2).of_le (by exact_mod_cast hj)).contDiffAt).symm
  · funext x
    simp [h₁.terminal, h₂.terminal]
  · intro x r hr
    have hr' : r ∈ Set.Icc (0 : ℝ) t := ⟨hr.1.le, hr.2.le⟩
    have := (h₁.time_deriv x r hr).sub (h₂.time_deriv x r hr)
    rw [hgs r hr' x]
    convert this using 1
    ring
  · refine ((h₁.cont_time_deriv).sub (h₂.cont_time_deriv)).congr fun p => ?_
    exact (hgs p.1 p.1.2 p.2).symm
  · obtain ⟨B₁, hB₁⟩ := h₁.bdd_time_deriv
    obtain ⟨B₂, hB₂⟩ := h₂.bdd_time_deriv
    refine ⟨B₁ + B₂, fun r hr x => ?_⟩
    rw [hgs r hr x]
    calc |generatorW (D.coeff ρ) r (f₁ r) x - generatorW (D.coeff ρ) r (f₂ r) x|
        ≤ |generatorW (D.coeff ρ) r (f₁ r) x| + |generatorW (D.coeff ρ) r (f₂ r) x| := abs_sub _ _
      _ ≤ B₁ * (1 + ‖x‖) + B₂ * (1 + ‖x‖) := add_le_add (hB₁ r hr x) (hB₂ r hr x)
      _ = (B₁ + B₂) * (1 + ‖x‖) := by ring

/-! ### The time reversal is a distributional forward solution -/

/-- A classical adjoint solution with terminal datum `0`, time reversed, solves the forward equation
`B:eq:adjoint-forward` in the distributional sense with initial datum `0`. -/
theorem fcau_forward (hd : 1 ≤ d) (D : WholeDyn d) (hs0 : 0 ≤ D.s) (hsd : D.s < d)
    (ρ : ℝ → Euc d → ℝ) (t : ℝ) (hS : FcauSlices D ρ t) {w : ℝ → Euc d → ℝ}
    (hw : IsClassicalAdjointW (D.coeff ρ) t 0 w) :
    IsForwardDistSolutionW D ρ t (fun σ => w (t - σ)) := by
  have hw2 := hw.isC12TestRd
  set ft : ℝ → Euc d → ℝ := fun r x => -(generatorW (D.coeff ρ) r (w r) x) with hft
  have hmem : ∀ r ∈ Set.Icc (0 : ℝ) t, MemCb 2 (w r) := fun r hr => hw2.memCb hr
  have hfp : ∀ (ψ : Euc d → ℝ), ContDiff ℝ ∞ ψ → HasCompactSupport ψ → ∀ σ ∈ Set.Icc (0 : ℝ) t,
      forwardPairing D ρ t σ (w (t - σ)) ψ = -∫ x, ψ x * ft (t - σ) x := by
    intro ψ hψ hψc σ hσ
    have hσ' : t - σ ∈ Set.Icc (0 : ℝ) t := ⟨by linarith [hσ.2], by linarith [hσ.1]⟩
    rw [← fcau_slice hd D hs0 hsd ρ t σ (hS (t - σ) hσ').1 (hS (t - σ) hσ').2 (hmem _ hσ') hψ hψc]
    simp only [hft, mul_neg, integral_neg, neg_neg]
  refine ⟨?_, fun ψ hψ hψc => ?_, fun ψ hψ hψc τ hτ => ?_⟩
  · show w (t - 0) =ᵐ[volume] 0
    rw [sub_zero, hw.terminal]
  · have hGc := fcau_Gcont hw2 hψ.continuous hψc
    have hcont : ContinuousOn (fun σ => -∫ x, ψ x * ft (t - σ) x) (Set.Icc (0 : ℝ) t) :=
      (hGc.comp (continuousOn_const.sub continuousOn_id) (fun σ hσ =>
        (⟨by linarith [hσ.2], by linarith [hσ.1]⟩ : t - σ ∈ Set.Icc (0 : ℝ) t))).neg
    exact hcont.integrableOn_Icc.congr_fun (fun σ hσ => (hfp ψ hψ hψc σ hσ).symm) measurableSet_Icc
  · show ∫ x, w (t - τ) x * ψ x = (∫ x, w (t - 0) x * ψ x) +
      ∫ σ in Set.Icc (0 : ℝ) τ, forwardPairing D ρ t σ (w (t - σ)) ψ
    have hftc := fcau_ftc_integral hw2 hψ.continuous hψc (a := t - τ) (b := t)
      (by linarith [hτ.2]) (by linarith [hτ.1]) le_rfl
    have h0 : ∫ x, ψ x * w t x = 0 := by simp [hw.terminal]
    rw [h0, zero_sub] at hftc
    have hI : ∫ σ in Set.Icc (0 : ℝ) τ, forwardPairing D ρ t σ (w (t - σ)) ψ =
        -∫ u in (t - τ)..t, ∫ x, ψ x * ft u x := by
      rw [setIntegral_congr_fun measurableSet_Icc (fun σ hσ =>
        hfp ψ hψ hψc σ ⟨hσ.1, hσ.2.trans hτ.2⟩), integral_neg, integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le hτ.1]
      congr 1
      have := intervalIntegral.integral_comp_sub_left (fun u => ∫ x, ψ x * ft u x) (a := 0) (b := τ) t
      simpa using this
    rw [hI, ← hftc, sub_zero, hw.terminal]
    simp only [Pi.zero_apply, zero_mul, integral_zero, zero_add, neg_neg]
    congr 1; funext x; ring

theorem fcau_ulBounded {χ : Euc d → ℝ} (hχ : IsUlocCutoff χ) {C : WholeCoeff d} {t : ℝ}
    {φ : Euc d → ℝ} {w : ℝ → Euc d → ℝ} (hw : IsClassicalAdjointW C t φ w) :
    IsUlBounded χ 1 t (fun σ => w (t - σ)) := by
  obtain ⟨Cχ, hCχ0, hCχ⟩ := fcau_ul_bound hχ
  obtain ⟨B₀, hB₀⟩ := hw.bdd 0 (by norm_num)
  obtain ⟨B₁, hB₁⟩ := hw.bdd 1 (by norm_num)
  refine ⟨Cχ * max B₀ B₁, fun τ hτ => ?_⟩
  have hr : t - τ ∈ Set.Icc (0 : ℝ) t := ⟨by linarith [hτ.2], by linarith [hτ.1]⟩
  refine hCχ (w (t - τ)) (max B₀ B₁) ((hw.c2 _ hr).of_le (by norm_num)) (fun x => ?_) (fun x => ?_)
  · have := hB₀ _ hr x
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)
  · have := hB₁ _ hr x
    rw [norm_iteratedFDeriv_one] at this
    exact this.trans (le_max_right _ _)

/-! ### Uniqueness -/

/-- **Uniqueness of classical adjoint solutions (F-CAU).**  Under the coefficient hypotheses of
S.A.33 `uloc_uniqueness` (`D.s = s`, `0 ≤ s < d`, `m ≥ 1`, `MatBound`, `VHypRd (m+3)`, `0 ≤ ν ≤ ν̄`,
`CoeffHypRd s m Λ T ρ`) and one of its regimes (`RdRegimeHolds`), two classical adjoint solutions
(`IsClassicalAdjointW`, class `C_b²`) of `D.coeff ρ` on `[0,t]`, `t ≤ T`, with the same terminal
datum agree on `[0,t]`. -/
theorem propagatorW_unique (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) (hm : 1 ≤ m)
    (Rg : PDE.Regime) (T Λ ΛV G₀ MB νbar ν₀ : ℝ) (D : WholeDyn d) (ρ : ℝ → Euc d → ℝ)
    (hDs : D.s = s) (hM : PDE.MatBound MB D.M) (hV : VHypRd (m + 3) ΛV G₀ D.V)
    (hν : 0 ≤ D.invβ ∧ D.invβ ≤ νbar) (hρ : CoeffHypRd s m Λ T ρ)
    (hRg : RdRegimeHolds Rg d s D.M D.invβ ν₀) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T)
    {φ : Euc d → ℝ} {f₁ f₂ : ℝ → Euc d → ℝ} (h₁ : IsClassicalAdjointW (D.coeff ρ) t φ f₁)
    (h₂ : IsClassicalAdjointW (D.coeff ρ) t φ f₂) :
    ∀ r ∈ Set.Icc (0 : ℝ) t, f₁ r = f₂ r := by
  subst hDs
  obtain ⟨χ, hχ⟩ := fcau_exists_cutoff (d := d)
  have hS := fcau_slices_of_hyp hd hs0 hsd m hm MB Λ ΛV G₀ rfl hM hV hρ ht
  have hw := fcau_sub hd D hs0 hsd ρ t hS h₁ h₂
  have hz := fcau_forward hd D hs0 hsd ρ t hS hw
  have hzb := fcau_ulBounded hχ hw
  have key := HRS.MS.UniqG2.uloc_uniqueness_proof hd D.s hs0 hsd m hm Rg T Λ ΛV G₀ MB νbar ν₀ χ hχ
    D.M D.V D.invβ ρ hM hV hν hρ hRg t ht (fun σ => (fun r x => f₁ r x - f₂ r x) (t - σ)) hzb hz
  intro r hr
  have hae := key (t - r) ⟨by linarith [hr.2], by linarith [hr.1]⟩
  simp only [sub_sub_cancel] at hae
  have hc : Continuous (fun x => f₁ r x - f₂ r x) :=
    (h₁.c2 r hr).continuous.sub (h₂.c2 r hr).continuous
  have h0 : (fun x => f₁ r x - f₂ r x) = 0 :=
    (Continuous.ae_eq_iff_eq volume hc continuous_const).1 hae
  funext x
  have := congrFun h0 x
  simp only [Pi.zero_apply] at this
  linarith

/-- If a classical adjoint solution `f` exists, `propagatorW` is `f` on `[0,t]`. -/
theorem propagatorW_eq (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) (hm : 1 ≤ m)
    (Rg : PDE.Regime) (T Λ ΛV G₀ MB νbar ν₀ : ℝ) (D : WholeDyn d) (ρ : ℝ → Euc d → ℝ)
    (hDs : D.s = s) (hM : PDE.MatBound MB D.M) (hV : VHypRd (m + 3) ΛV G₀ D.V)
    (hν : 0 ≤ D.invβ ∧ D.invβ ≤ νbar) (hρ : CoeffHypRd s m Λ T ρ)
    (hRg : RdRegimeHolds Rg d s D.M D.invβ ν₀) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T)
    {φ : Euc d → ℝ} {f : ℝ → Euc d → ℝ} (hf : IsClassicalAdjointW (D.coeff ρ) t φ f) :
    ∀ r ∈ Set.Icc (0 : ℝ) t, propagatorW (D.coeff ρ) r t φ = f r :=
  propagatorW_unique hd hs0 hsd m hm Rg T Λ ΛV G₀ MB νbar ν₀ D ρ hDs hM hV hν hρ hRg ht
    (propagatorW_isClassical ⟨f, hf⟩) hf

end HRS.MS.Fcau
