import HRS.MS.ZeroTempAux4
import HRS.MS.StarTie
import HRS.MS.GoFeatAux3
import HRS.MS.GoCommAux1

/-!
# SA11, packet B1: uniqueness of classical adjoint solutions from `RdStanding`, linearity of `propagatorW`

* `sa11_regular_mono`: `IsRegularMFRd` at level `r` implies it at every smaller level.
* `sa11_coeffHyp`: `CoeffHypRd s m Λ T (S.ρ N)` from `RdStanding` at level `m + 3` (weak continuity from the weak form of the
  mean-field equation, `s55_weak_cont` and `s55f_weak_cont_bdd`).
* `sa11_regime`: the three cases of `FieldDensityRd.HoldsAt` with `wParams = some _` give `R1` or `UlocStarRegime`.
* `sa11_uniq`: classical adjoint solutions of `S.coeff N` are unique on `[0,t]`, `t ≤ T` (`propagatorW_eq_star`).
* linearity of `generatorW` on `C_b²`, closure of classical solutions under linear combinations,
  `sa11_propagatorW_lin`: `φ ↦ U^{r,t}φ` is linear on the functions admitting a classical solution.
-/

noncomputable section

open MeasureTheory Filter Topology
open HRS HRS.Whole HRS.Whole.AppendixA
open scoped ENNReal ContDiff

namespace HRS.MS.ZeroTemp

variable {d : ℕ}

theorem sa11_memCb_cc (k : ℕ) {φ : Euc d → ℝ} (hφ : IsCcInfty φ) : MemCb k φ := by
  refine ⟨hφ.1.of_le (by exact_mod_cast le_top), fun j _ => ?_⟩
  have hc : Continuous (iteratedFDeriv ℝ j φ) :=
    hφ.1.continuous_iteratedFDeriv (by exact_mod_cast le_top)
  obtain ⟨C, hC⟩ := hc.norm.bounded_above_of_compact_support (hφ.2.iteratedFDeriv j).norm
  exact ⟨C, by rintro _ ⟨z, rfl⟩; simpa using hC z⟩

theorem sa11_regular_mono {s : ℝ} {r r' : ℕ} {Λ T : ℝ} {ρ : ℝ → Euc d → ℝ} (h : IsRegularMFRd s r Λ T ρ)
    (hr : r' ≤ r) : IsRegularMFRd s r' Λ T ρ := by
  refine ⟨fun t ht => ?_, h.2⟩
  obtain ⟨hcb, hfin, hle⟩ := h.1 t ht
  refine ⟨⟨hcb.1.of_le (by exact_mod_cast hr), fun j hj => hcb.2 j (hj.trans hr)⟩,
    lt_of_le_of_lt (HRS.MS.Fcau.fcau_weightedSupE_mono hr _ _) hfin, ?_⟩
  have h1 : HRS.cbNorm r' (ρ t) ≤ HRS.cbNorm r (ρ t) := by
    unfold HRS.cbNorm
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) fun j _ _ =>
      Real.iSup_nonneg fun z => norm_nonneg _
  have h2 : (weightedSupE r' ((d : ℝ) + 3) (ρ t)).toReal ≤ (weightedSupE r ((d : ℝ) + 3) (ρ t)).toReal :=
    ENNReal.toReal_mono hfin.ne (HRS.MS.Fcau.fcau_weightedSupE_mono hr _ _)
  linarith

/-- `CoeffHypRd` from `RdStanding` (the mean-field regularity at level `m + 3`). -/
theorem sa11_coeffHyp {S : WholeMainData d} {R : ∀ N, RealizationRd d N} {MB Λ ΛV G₀ m20 C₀ : ℝ} {m : ℕ}
    {𝔈 : ℕ → ℝ} (hS : RdStanding S R MB Λ ΛV G₀ m20 (m + 3) (m + 3) C₀ 𝔈) {N : ℕ} (hN : 1 ≤ N) :
    CoeffHypRd S.s m Λ S.T (S.ρ N) := by
  have hd1 : 1 ≤ d := S.hd
  have hmf := hS.mean_field
  have hsol := hmf.solution N hN
  have hreg3 : IsRegularMFRd S.s 3 Λ S.T (S.ρ N) :=
    sa11_regular_mono (hmf.regular N hN) (by omega)
  obtain ⟨ΛV', G₀', hV2⟩ : ∃ ΛV' G₀' : ℝ, VHypRd 2 ΛV' G₀' S.V :=
    ⟨ΛV, G₀, HRS.MP.RdGen.rg_VHyp_mono hS.potential (by omega) le_rfl le_rfl⟩
  have hMF : HRS.MH.DualityRd.MFData S.s Λ S.T ΛV' G₀' (S.dyn N) (S.ρ N) :=
    ⟨rfl, S.hs0, S.hsd, S.hinvβ N, hV2, hsol, hreg3⟩
  refine ⟨hsol.density, hmf.regular N hN, ?_⟩
  have hreg3' : ∀ t ∈ Set.Icc (0 : ℝ) S.T, MemCb 3 (S.ρ N t) ∧ weightedSupE 3 ((d : ℝ) + 3) (S.ρ N t) < ⊤ ∧
      HRS.cbNorm 3 (S.ρ N t) + (weightedSupE 3 ((d : ℝ) + 3) (S.ρ N t)).toReal ≤ Λ := fun t ht => hreg3.1 t ht
  exact HRS.MS.Go.s55f_weak_cont_bdd hd1 Λ hreg3' fun ψ hψ hcs =>
    HRS.MS.Go.s55_weak_cont hMF (sa11_memCb_cc 2 ⟨hψ, hcs⟩)

/-- The regime of the decaying field densities: `R1` (sub-Coulomb) or the corner `UlocStarRegime`. -/
theorem sa11_regime {s : ℝ} (fd : FieldDensityRd d s) {m : ℕ} {p : ℝ}
    (hfd : fd.wParams = some (m, p)) {s' : ℝ} {M : Matrix (Fin d) (Fin d) ℝ} {invβ ν₀ : ℝ}
    (h : fd.HoldsAt s' M invβ ν₀) :
    RdRegimeHolds PDE.Regime.R1 d s' M invβ ν₀ ∨ HRS.MS.Star.UlocStarRegime d s' M := by
  cases fd with
  | nd Rg => simp [FieldDensityRd.wParams] at hfd
  | decSub c =>
    left
    unfold FieldDensityRd.HoldsAt at h
    unfold RdRegimeHolds
    simp only
    linarith
  | decSuperIso m' p' =>
    right
    obtain ⟨h1, -, -, lam, hlam, hM⟩ := h
    refine ⟨h1, HRS.MS.Star.star_matrix_symNonpos_of_lam hlam.le (A := 0) (by simp) ?_⟩
    rw [hM]; simp
  | decSuperHilb m' =>
    right
    obtain ⟨h1, -, lam, hlam, A, hA, hM⟩ := h
    exact ⟨h1, HRS.MS.Star.star_matrix_symNonpos_of_lam hlam hA hM⟩

/-- Uniqueness of classical adjoint solutions of `S.coeff N` on `[0,t]`, `t ≤ T`. -/
theorem sa11_uniq {S : WholeMainData d} {R : ∀ N, RealizationRd d N} {MB Λ ΛV G₀ m20 C₀ : ℝ} {m : ℕ}
    (hm1 : 1 ≤ m) {𝔈 : ℕ → ℝ} (hS : RdStanding S R MB Λ ΛV G₀ m20 (m + 3) (m + 3) C₀ 𝔈) {N : ℕ} (hN : 1 ≤ N)
    {νbar ν₀ : ℝ} (hν : S.invβ N ≤ νbar)
    (hRg : RdRegimeHolds PDE.Regime.R1 d S.s S.M (S.invβ N) ν₀ ∨ HRS.MS.Star.UlocStarRegime d S.s S.M)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) S.T) {φ : Euc d → ℝ} {f : ℝ → Euc d → ℝ}
    (hf : IsClassicalAdjointW (S.coeff N) t φ f) :
    ∀ r ∈ Set.Icc (0 : ℝ) t, propagatorW (S.coeff N) r t φ = f r :=
  HRS.MS.Fcau.propagatorW_eq_star S.hd S.hs0 S.hsd m hm1 PDE.Regime.R1 S.T Λ ΛV G₀ MB νbar ν₀ (S.dyn N) (S.ρ N) rfl
    hS.matrix_bound hS.potential ⟨S.hinvβ N, hν⟩ (sa11_coeffHyp hS hN) hRg ht hf

/-! ### Linearity of the generator and of classical solutions -/

open HRS.MH.DualityRd in
theorem sa11_gradient_const_mul {f : Euc d → ℝ} (hf : ContDiff ℝ 1 f) (c : ℝ) (y : Euc d) :
    gradient (fun z => c * f z) y = c • gradient f y := by
  ext i
  rw [q09_gradient_apply, PiLp.smul_apply, q09_gradient_apply, smul_eq_mul,
    fderiv_const_mul (hf.differentiable one_ne_zero y)]
  rfl

open HRS.MH.DualityRd in
theorem sa11_nl_smul (D : WholeDyn d) (ρ' : Euc d → ℝ) (c : ℝ) {u : Euc d → ℝ} (hu : ContDiff ℝ 1 u) (x : Euc d) :
    nlTermRd D ρ' (fun y => c * u y) x = c * nlTermRd D ρ' u x := by
  unfold nlTermRd
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  set g : Euc d → ℝ := fun y => ρ' y * (Torus.matVec D.M.transpose (gradient u y)) j with hg
  have e : (fun y => ρ' y * (Torus.matVec D.M.transpose (gradient (fun z => c * u z) y)) j) = fun y => c * g y := by
    funext y
    rw [sa11_gradient_const_mul hu c y]
    simp only [hg, Torus.matVec, map_smul, PiLp.smul_apply, smul_eq_mul]
    ring
  rw [e]
  have : convGradConvW (rieszKernelGrad d D.s) (fun y => c * g y) x = c • convGradConvW (rieszKernelGrad d D.s) g x := by
    unfold convGradConvW
    rw [← integral_smul]
    congr 1
    funext y
    split_ifs <;> simp only [smul_smul, mul_sub]
  rw [this]
  simp

open HRS.MH.DualityRd in
theorem sa11_gen_smul (D : WholeDyn d) (ρ' : ℝ → Euc d → ℝ) (r : ℝ) (c : ℝ) {f : Euc d → ℝ} (hf : ContDiff ℝ 2 f)
    (x : Euc d) :
    generatorW (D.coeff ρ') r (fun y => c * f y) x = c * generatorW (D.coeff ρ') r f x := by
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  rw [generatorW_coeff, generatorW_coeff]
  have hl : Laplacian.laplacian (fun y => c * f y) x = c * Laplacian.laplacian f x := by
    have := InnerProductSpace.laplacian_smul c (hf.contDiffAt (x := x))
    exact this
  rw [hl, sa11_gradient_const_mul hf1 c x, sa11_nl_smul D (ρ' r) c hf1 x, inner_smul_right]
  ring

theorem sa11_memCb_const_mul {k : ℕ} {g : Euc d → ℝ} (hg : MemCb k g) (c : ℝ) : MemCb k (fun y => c * g y) := by
  refine ⟨contDiff_const.mul hg.1, fun j hj => ?_⟩
  obtain ⟨B, hB⟩ := hg.2 j hj
  refine ⟨|c| * B, ?_⟩
  rintro _ ⟨x, rfl⟩
  have e : iteratedFDeriv ℝ j (fun y => c * g y) x = c • iteratedFDeriv ℝ j g x :=
    iteratedFDeriv_const_smul_apply (a := c) (i := j) (f := g) (hg.1.of_le (by exact_mod_cast hj)).contDiffAt
  show ‖iteratedFDeriv ℝ j (fun y => c * g y) x‖ ≤ |c| * B
  rw [e, norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (hB ⟨x, rfl⟩) (abs_nonneg c)

open HRS.MH.DualityRd in
theorem sa11_gen_add_smul (hd : 1 ≤ d) (D : WholeDyn d) (hs0 : 0 ≤ D.s) (hsd : D.s < d) (ρ : ℝ → Euc d → ℝ) (r : ℝ)
    (hρ : RegSliceRd (ρ r)) {f g : Euc d → ℝ} (hf : MemCb 2 f) (hg : MemCb 2 g) (c : ℝ) (x : Euc d) :
    generatorW (D.coeff ρ) r (fun y => f y + c * g y) x =
      generatorW (D.coeff ρ) r f x + c * generatorW (D.coeff ρ) r g x := by
  have h1 := HRS.MS.Fcau.fcau_gen_sub hd D hs0 hsd ρ r hρ hf (sa11_memCb_const_mul hg (-c)) x
  have h2 := sa11_gen_smul D ρ r (-c) (hg.1.of_le (by norm_num)) x
  have e : (fun y => f y + c * g y) = fun y => f y - (-c * g y) := by funext y; ring
  rw [e, h1, h2]; ring

/-- classical adjoint solutions are closed under the linear combination `φ₁ + c φ₂` -/
theorem sa11_isClassical_comb (hd : 1 ≤ d) (D : WholeDyn d) (hs0 : 0 ≤ D.s) (hsd : D.s < d) (ρ : ℝ → Euc d → ℝ) (t : ℝ)
    (hS : HRS.MS.Fcau.FcauSlices D ρ t) {φ₁ φ₂ : Euc d → ℝ} {f₁ f₂ : ℝ → Euc d → ℝ} (c : ℝ)
    (h₁ : IsClassicalAdjointW (D.coeff ρ) t φ₁ f₁) (h₂ : IsClassicalAdjointW (D.coeff ρ) t φ₂ f₂) :
    IsClassicalAdjointW (D.coeff ρ) t (fun x => φ₁ x + c * φ₂ x) (fun r x => f₁ r x + c * f₂ r x) := by
  have hm₁ := fun r (hr : r ∈ Set.Icc (0 : ℝ) t) => h₁.isC12TestRd.memCb hr
  have hm₂ := fun r (hr : r ∈ Set.Icc (0 : ℝ) t) => h₂.isC12TestRd.memCb hr
  have hgs : ∀ r ∈ Set.Icc (0 : ℝ) t, ∀ x, generatorW (D.coeff ρ) r (fun y => f₁ r y + c * f₂ r y) x =
      generatorW (D.coeff ρ) r (f₁ r) x + c * generatorW (D.coeff ρ) r (f₂ r) x := fun r hr x =>
    sa11_gen_add_smul hd D hs0 hsd ρ r (hS r hr).1 (hm₁ r hr) (hm₂ r hr) c x
  have hit : ∀ r ∈ Set.Icc (0 : ℝ) t, ∀ j ≤ 2, ∀ x,
      iteratedFDeriv ℝ j (fun y => f₁ r y + c * f₂ r y) x =
        iteratedFDeriv ℝ j (f₁ r) x + c • iteratedFDeriv ℝ j (f₂ r) x := by
    intro r hr j hj x
    have a1 : ContDiffAt ℝ (j : WithTop ℕ∞) (f₁ r) x := ((h₁.c2 r hr).of_le (by exact_mod_cast hj)).contDiffAt
    have a2 : ContDiffAt ℝ (j : WithTop ℕ∞) (f₂ r) x := ((h₂.c2 r hr).of_le (by exact_mod_cast hj)).contDiffAt
    have e1 := iteratedFDeriv_const_smul_apply (a := c) (i := j) (f := f₂ r) (x := x) a2
    have e2 := iteratedFDeriv_add_apply (i := j) (f := f₁ r) (g := c • f₂ r) (x := x) a1 (a2.const_smul c)
    exact e2.trans (by rw [e1])
  refine ⟨fun r hr => (h₁.c2 r hr).add (contDiff_const.mul (h₂.c2 r hr)), fun j hj => ?_, fun j hj => ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨B₁, hB₁⟩ := h₁.bdd j hj
    obtain ⟨B₂, hB₂⟩ := h₂.bdd j hj
    refine ⟨B₁ + |c| * B₂, fun r hr x => ?_⟩
    rw [hit r hr j hj x]
    refine (norm_add_le _ _).trans (add_le_add (hB₁ r hr x) ?_)
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hB₂ r hr x) (abs_nonneg c)
  · refine ((h₁.cont_c2 j hj).add ((continuous_const : Continuous fun _ : Set.Icc (0 : ℝ) t × Euc d => c).smul (h₂.cont_c2 j hj))).congr fun p => ?_
    exact (hit p.1 p.1.2 j hj p.2).symm
  · funext x
    simp [h₁.terminal, h₂.terminal]
  · intro x r hr
    have hr' : r ∈ Set.Icc (0 : ℝ) t := ⟨hr.1.le, hr.2.le⟩
    have := (h₁.time_deriv x r hr).add ((h₂.time_deriv x r hr).const_mul c)
    rw [hgs r hr' x]
    convert this using 1
    ring
  · refine ((h₁.cont_time_deriv).add ((continuous_const : Continuous fun _ : Set.Icc (0 : ℝ) t × Euc d => c).mul h₂.cont_time_deriv)).congr fun p => ?_
    exact (hgs p.1 p.1.2 p.2).symm
  · obtain ⟨B₁, hB₁⟩ := h₁.bdd_time_deriv
    obtain ⟨B₂, hB₂⟩ := h₂.bdd_time_deriv
    refine ⟨B₁ + |c| * B₂, fun r hr x => ?_⟩
    rw [hgs r hr x]
    calc |generatorW (D.coeff ρ) r (f₁ r) x + c * generatorW (D.coeff ρ) r (f₂ r) x|
        ≤ |generatorW (D.coeff ρ) r (f₁ r) x| + |c * generatorW (D.coeff ρ) r (f₂ r) x| := abs_add_le _ _
      _ ≤ B₁ * (1 + ‖x‖) + |c| * (B₂ * (1 + ‖x‖)) := by
          rw [abs_mul]
          exact add_le_add (hB₁ r hr x) (mul_le_mul_of_nonneg_left (hB₂ r hr x) (abs_nonneg c))
      _ = (B₁ + |c| * B₂) * (1 + ‖x‖) := by ring

/-- Linearity of `φ ↦ U^{r,t}φ` on the functions with a classical adjoint solution (from uniqueness). -/
theorem sa11_propagatorW_lin {S : WholeMainData d} {R : ∀ N, RealizationRd d N} {MB Λ ΛV G₀ m20 C₀ : ℝ} {m : ℕ}
    (hm1 : 1 ≤ m) {𝔈 : ℕ → ℝ} (hS : RdStanding S R MB Λ ΛV G₀ m20 (m + 3) (m + 3) C₀ 𝔈) {N : ℕ} (hN : 1 ≤ N)
    {νbar ν₀ : ℝ} (hν : S.invβ N ≤ νbar)
    (hRg : RdRegimeHolds PDE.Regime.R1 d S.s S.M (S.invβ N) ν₀ ∨ HRS.MS.Star.UlocStarRegime d S.s S.M)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) S.T) {φ ψ : Euc d → ℝ} (c : ℝ)
    (hφ : ∃ f, IsClassicalAdjointW (S.coeff N) t φ f) (hψ : ∃ f, IsClassicalAdjointW (S.coeff N) t ψ f)
    {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) t) :
    propagatorW (S.coeff N) r t (fun x => φ x + c * ψ x) =
      fun x => propagatorW (S.coeff N) r t φ x + c * propagatorW (S.coeff N) r t ψ x := by
  obtain ⟨f₁, h₁⟩ := hφ
  obtain ⟨f₂, h₂⟩ := hψ
  have hslice := HRS.MS.Fcau.fcau_slices_of_hyp S.hd S.hs0 S.hsd m hm1 MB Λ ΛV G₀ (D := S.dyn N) (ρ := S.ρ N)
    (T := S.T) rfl hS.matrix_bound hS.potential (sa11_coeffHyp hS hN) ht
  have hcomb := sa11_isClassical_comb S.hd (S.dyn N) S.hs0 S.hsd (S.ρ N) t hslice c h₁ h₂
  have e := sa11_uniq hm1 hS hN hν hRg ht hcomb r hr
  rw [e, sa11_uniq hm1 hS hN hν hRg ht h₁ r hr, sa11_uniq hm1 hS hN hν hRg ht h₂ r hr]

end HRS.MS.ZeroTemp
