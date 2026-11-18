import HRS.MS.R2SeAux9

/-!
# S9.9 `r2_static_edgeworth`, packet 10: family data, the observables `w_{jl} = v_j · ∇φ_l`, covariance identities

Worker S99, namespace `S99`.  Fixed orders: `J1 = 4d+40` (the class of the features) and `k0 = 2d+10` (the order of the correctors).

* `FamData`: for a feature family `φ ⊂ C_b^{J1}` the correctors `χ_j ∈ C^{k0+1}` of `s99_chi`, with uniform bounds
  `‖D^{i+1}χ_j‖_∞ ≤ K ‖φ_j‖_{C_b^{J1}}` and `L_μ χ_j = γ a_j`, `a_j = responseRepW φ_j ∈ C_b^{k0}`;
* `wF F j l = γ⁻¹ ⟨∇χ_j, ∇φ_l⟩` (`= v_j · ∇φ_l`), `wF ∈ C_b^{k0}` with `‖wF‖ ≤ K' b_j b_l` (`s99_wF_cb`);
* `s99_cov_ibp`: `Cov(w, φ_m) = ∫ w a_m dμ` for a bounded `C¹` observable `w` (symmetry of `R_γ` and integration by parts);
* `s99_cov_corr`: `Cov(w, φ') = ∫ γ⁻¹⟨∇χ_w, ∇φ'⟩ dμ` for a corrected observable `w` (`s46_cov_identity`).
-/

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

noncomputable section

namespace S99

open S45
open HRS.Whole
open HRS (Euc cbNorm MemCb)

variable {d N : ℕ}

/-- The class `C_b^{J1}`, `J1 = 4d + 40`, of the features. -/
def J1 (d : ℕ) : ℕ := 4 * d + 40

/-- The order of the correctors. -/
def k0 (d : ℕ) : ℕ := 2 * d + 10

theorem k0_ge_one (d : ℕ) : 1 ≤ k0 d := by unfold k0; omega

theorem J1_ge_k0 (d : ℕ) : k0 d + 1 ≤ J1 d := by unfold k0 J1; omega

theorem k0_lt_J1 (d : ℕ) : ((k0 d : ℕ) : ℝ) + 1 + (d : ℝ) / 2 < (J1 d : ℝ) := by
  unfold k0 J1
  push_cast
  have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  linarith

theorem one_lt_k0 (d : ℕ) : ((1 : ℕ) : ℝ) + 1 + (d : ℝ) / 2 < (k0 d : ℝ) := by
  unfold k0
  push_cast
  have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  linarith

theorem J1_gt (d : ℕ) : (d : ℝ) / 2 + 2 < (J1 d : ℝ) := by
  unfold J1
  push_cast
  have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  linarith

/-- `a_ψ = responseRepW ψ`. -/
def aRep (d : ℕ) (s a β γ : ℝ) (ψ : Euc d → ℝ) : Euc d → ℝ :=
  responseRepW (rieszKernel d s) (thermalMeasure d s a β) γ ψ

/-- Correctors of a feature family. -/
structure FamData (d : ℕ) (s a β γ : ℝ) (φ : ℕ → Euc d → ℝ) where
  K : ℝ
  hK : 0 ≤ K
  χ : ℕ → Euc d → ℝ
  smooth : ∀ j, ContDiff ℝ ((k0 d + 1 : ℕ) : WithTop ℕ∞) (χ j)
  deriv : ∀ j x, ∀ i ≤ k0 d, ‖iteratedFDeriv ℝ (i + 1) (χ j) x‖ ≤ K * cbNorm (J1 d) (φ j)
  gen : ∀ j x, thermalGen d s a β (χ j) x = γ * aRep d s a β γ (φ j) x
  resp : ∀ j, IsResponse (rieszKernel d s) (thermalMeasure d s a β) γ (φ j) (aRep d s a β γ (φ j))
  amem : ∀ j, MemCb (k0 d) (aRep d s a β γ (φ j))
  anorm : ∀ j, cbNorm (k0 d) (aRep d s a β γ (φ j)) ≤ K * cbNorm (J1 d) (φ j)

theorem s99_famData (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β γ : ℝ} (ha : 0 < a)
    (hβ : 0 < β) (hγ : 0 < γ) {φ : ℕ → Euc d → ℝ} (hφ : ∀ j, MemCb (J1 d) (φ j)) :
    Nonempty (FamData d s a β γ φ) := by
  obtain ⟨K, hK, h⟩ := s99_chi hd hs0 hsd (k0 d) (k0_ge_one d) a β γ ha hβ hγ (J1 d) (k0_lt_J1 d)
  have := fun j => h (φ j) (hφ j)
  choose χ h1 h2 h3 h4 h5 h6 using this
  exact ⟨⟨K, hK, χ, h1, h2, h3, h4, h5, h6⟩⟩

namespace FamData

variable {s a β γ C c BU : ℝ} {φ : ℕ → Euc d → ℝ}

theorem feat (F : FamData d s a β γ φ) (hT : ThermalData d s a β C c BU) (hγ : 0 < γ) (j : ℕ) :
    S46.S46Feat d s a β γ (φ j) (F.χ j) (F.K * cbNorm (J1 d) (φ j)) :=
  s99_feat_S46 hT hγ (k0_ge_one d) (F.smooth j) (F.deriv j) (F.gen j) (F.resp j) (F.amem j)

end FamData

/-- The observable `w_{jl} = γ⁻¹ ⟨∇χ_j, ∇φ_l⟩ = v_j · ∇φ_l`. -/
def wF {φ : ℕ → Euc d → ℝ} {s a β γ : ℝ} (F : FamData d s a β γ φ) (j l : ℕ) (x : Euc d) : ℝ :=
  γ⁻¹ * ⟪gradient (F.χ j) x, gradient (φ l) x⟫

theorem s99_pair_wF (hN : 1 ≤ N) {φ : ℕ → Euc d → ℝ} {s a β γ : ℝ} (F : FamData d s a β γ φ)
    (j l : ℕ) (X : EucConfig d N) :
    pair (empirical X) (wF F j l) =
      γ⁻¹ * pair (empirical X) (fun x => ⟪gradient (F.χ j) x, gradient (φ l) x⟫) := by
  have hN' : 0 < N := hN
  rw [pair_empirical hN', pair_empirical hN']
  unfold wF
  rw [← Finset.mul_sum]
  ring

theorem s99_wF_cb (hd : 2 ≤ d) {s a β γ : ℝ} (hγ : 0 < γ) {φ : ℕ → Euc d → ℝ}
    (hφ : ∀ j, MemCb (J1 d) (φ j)) (F : FamData d s a β γ φ) (j l : ℕ) :
    MemCb (k0 d) (wF F j l) ∧ cbNorm (k0 d) (wF F j l) ≤
      ((k0 d : ℝ) + 1) * 2 ^ k0 d * (γ⁻¹ * F.K * cbNorm (J1 d) (φ j)) * cbNorm (J1 d) (φ l) := by
  have hv : ContDiff ℝ (k0 d : WithTop ℕ∞) (fun y => γ⁻¹ • gradient (F.χ j) y) :=
    HRS.MS.S98.s98_gL_contDiff (F.smooth j) γ⁻¹
  have hBv : ∀ x, ∀ i ≤ k0 d, ‖iteratedFDeriv ℝ i (fun y => γ⁻¹ • gradient (F.χ j) y) x‖ ≤
      γ⁻¹ * F.K * cbNorm (J1 d) (φ j) := by
    intro x i hi
    refine (HRS.MS.S98.s98_gL_iter (F.smooth j) γ⁻¹ hi x).trans ?_
    rw [abs_of_nonneg (inv_nonneg.2 hγ.le), mul_assoc]
    exact mul_le_mul_of_nonneg_left (F.deriv j x i hi) (inv_nonneg.2 hγ.le)
  have hψ := HRS.MS.Tc5.tc5_cb_mono (J1_ge_k0 d) (hφ l)
  obtain ⟨h1, h2⟩ := s99_inner_cb hv hBv hψ.1
  have e : wF F j l = fun x => inner ℝ (γ⁻¹ • gradient (F.χ j) x) (gradient (φ l) x) := by
    funext x; unfold wF; rw [real_inner_smul_left]
  rw [e]
  refine ⟨h1, h2.trans ?_⟩
  have hB0 : 0 ≤ γ⁻¹ * F.K * cbNorm (J1 d) (φ j) := by
    have := HRS.MS.Tc5.tc5_cb_nonneg (d := d) (J1 d) (φ j)
    have := F.hK
    positivity
  refine mul_le_mul_of_nonneg_left hψ.2 (by positivity)

end S99

end
