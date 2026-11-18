import HRS.MS.SA16SEn6
import HRS.MS.SA16V2Calc

/-!
# S.A.16 (SA16S) En7: the jet energy pairing on `C_c^∞` and the diffusion term (packet P7, step 8)

`sa16sz_dens m p φ ψ x = ∑_{j ≤ m} |D^jφ(x)|^{p-2} ∑_idx ∂^idxφ ∂^idxψ`; for `φ, ψ ∈ C_c^∞`,
`fderiv (jetEnergy m) (J φ) (J ψ) = p ∫ sa16sz_dens` (`sa16sz_fderiv_cc`), `jetEnergy m (J φ) = ∑_j ∫ |D^jφ|^p`
(`sa16sz_energy_cc`), and `sa16sz_diffusion`: `∫ sa16sz_dens m p φ (Δφ) ≤ 0`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section En7
variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)]

/-- `|D^jφ(x)|` as a Euclidean norm over the coordinate derivatives of order `j` -/
def sa16sz_vn (φ : Euc d → ℝ) (j : ℕ) (x : Euc d) : ℝ :=
  vnorm (fun idx : Fin j → Fin d => partialDeriv idx φ x)

/-- the integrand of the energy pairing -/
def sa16sz_dens (m : ℕ) (p : ℝ) (φ ψ : Euc d → ℝ) (x : Euc d) : ℝ :=
  ∑ j : Fin (m + 1), sa16sz_vn φ j x ^ (p - 2) *
    ∑ idx : Fin (j : ℕ) → Fin d, partialDeriv idx φ x * partialDeriv idx ψ x

lemma sa16sz_pairDensity_cc (m : ℕ) (φ ψ : ccSub d) :
    closedPairDensity d m p (sa16r_Jcc d m p φ) (sa16r_Jcc d m p ψ) =ᵐ[volume]
      sa16sz_dens m p φ.1 ψ.1 := by
  rw [sa16r_Jcc_eq, sa16r_Jcc_eq]
  filter_upwards [sa16r_cc_elt_coe (p := p) φ.2 m, sa16r_cc_elt_coe (p := p) ψ.2 m] with x hx hy
  unfold closedPairDensity sa16sz_dens sa16sz_vn closedTensor
  refine Finset.sum_congr rfl fun j _ => ?_
  have h1 : ∀ idx : Fin (j : ℕ) → Fin d,
      ((sa16r_cc_elt φ.2 m : WmpSpace d m p) : WLp d m p) x ⟨j, idx⟩ = partialDeriv idx φ.1 x := by
    intro idx; rw [hx]; rfl
  have h2 : ∀ idx : Fin (j : ℕ) → Fin d,
      ((sa16r_cc_elt ψ.2 m : WmpSpace d m p) : WLp d m p) x ⟨j, idx⟩ = partialDeriv idx ψ.1 x := by
    intro idx; rw [hy]; rfl
  simp only [h1, h2]

lemma sa16sz_energy_cc (m : ℕ) (φ : ccSub d) :
    jetEnergy d m p (sa16r_Jcc d m p φ) = ∑ j : Fin (m + 1), ∫ x, sa16sz_vn φ.1 j x ^ p := by
  unfold jetEnergy
  rw [sa16r_Jcc_eq]
  refine Finset.sum_congr rfl fun j _ => ?_
  refine integral_congr_ae ?_
  filter_upwards [sa16r_cc_elt_coe (p := p) φ.2 m] with x hx
  unfold sa16sz_vn closedTensor
  have h1 : ∀ idx : Fin (j : ℕ) → Fin d,
      ((sa16r_cc_elt φ.2 m : WmpSpace d m p) : WLp d m p) x ⟨j, idx⟩ = partialDeriv idx φ.1 x := by
    intro idx; rw [hx]; rfl
  simp only [h1]

lemma sa16sz_fderiv_cc (m : ℕ) (φ ψ : ccSub d) :
    fderiv ℝ (jetEnergy d m p) (sa16r_Jcc d m p φ) (sa16r_Jcc d m p ψ) =
      p * ∫ x, sa16sz_dens m p φ.1 ψ.1 x := by
  rw [(closed_jet_energy_calculus d m p).2.2.2 _ _ |>.2]
  congr 1
  exact integral_congr_ae (sa16sz_pairDensity_cc m φ ψ)

lemma sa16sz_vn_cont (φ : Euc d → ℝ) (hφ : ContDiff ℝ ∞ φ) (j : ℕ) :
    Continuous (sa16sz_vn φ j) := by
  unfold sa16sz_vn vnorm
  exact (continuous_finsetSum _ fun idx _ => ((sa16j_pd_smooth hφ idx).continuous.pow 2)).sqrt

lemma sa16sz_vn_pow_cont (φ : Euc d → ℝ) (hφ : ContDiff ℝ ∞ φ) (j : ℕ) {q : ℝ} (hq : 0 ≤ q) :
    Continuous (fun x => sa16sz_vn φ j x ^ q) :=
  (sa16sz_vn_cont φ hφ j).rpow_const (fun _ => Or.inr hq)

lemma sa16sz_vn_nonneg (φ : Euc d → ℝ) (j : ℕ) (x : Euc d) : 0 ≤ sa16sz_vn φ j x := Real.sqrt_nonneg _

/-- the diffusion term of the energy is non-positive -/
theorem sa16sz_diffusion (m : ℕ) (φ : ccSub d) :
    ∫ x, sa16sz_dens m p φ.1 (sa16r_lap φ.1) x ≤ 0 := by
  have hp2 : 0 ≤ p - 2 := by linarith [Fact.out (p := 2 ≤ p)]
  have hW : ∀ (j : ℕ) (idx : Fin j → Fin d), IsCcInfty (partialDeriv idx φ.1) :=
    fun j idx => sa16s_cc_partialDeriv φ.2 idx
  -- pointwise form of the integrand
  set D : (j : ℕ) → (Fin j → Fin d) → Fin d → Euc d → ℝ := fun j idx i x =>
    fderiv ℝ (fun y => fderiv ℝ (partialDeriv idx φ.1) y (EuclideanSpace.single i 1)) x
      (EuclideanSpace.single i 1) with hD
  have hDcc : ∀ j idx i, IsCcInfty (D j idx i) := fun j idx i =>
    sa16s_cc_fderiv (sa16s_cc_fderiv (hW j idx) _) _
  have hpt : ∀ x, sa16sz_dens m p φ.1 (sa16r_lap φ.1) x = ∑ j : Fin (m + 1), ∑ i : Fin d,
      ∑ idx : Fin (j : ℕ) → Fin d, sa16sz_vn φ.1 j x ^ (p - 2) * partialDeriv idx φ.1 x * D j idx i x := by
    intro x
    unfold sa16sz_dens
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    simp_rw [mul_assoc]
    have : ∀ idx : Fin (j : ℕ) → Fin d, partialDeriv idx (sa16r_lap φ.1) x = ∑ i : Fin d, D j idx i x := by
      intro idx
      rw [sa16sy_pd_lap φ.2.1 idx x]
      rfl
    simp_rw [this, Finset.mul_sum]
    rw [Finset.sum_comm]
  simp_rw [hpt]
  have hint : ∀ (j : Fin (m + 1)) (i : Fin d), Integrable (fun x => ∑ idx : Fin (j : ℕ) → Fin d,
      sa16sz_vn φ.1 j x ^ (p - 2) * partialDeriv idx φ.1 x * D j idx i x) := by
    intro j i
    refine integrable_finsetSum _ fun idx _ => ?_
    exact (((sa16sz_vn_pow_cont φ.1 φ.2.1 j hp2).mul (hW j idx).1.continuous).mul
      (hDcc j idx i).1.continuous).integrable_of_hasCompactSupport (((hW j idx).2.mul_left).mul_right)
  have hint2 : ∀ j : Fin (m + 1), Integrable (fun x => ∑ i : Fin d, ∑ idx : Fin (j : ℕ) → Fin d,
      sa16sz_vn φ.1 j x ^ (p - 2) * partialDeriv idx φ.1 x * D j idx i x) :=
    fun j => integrable_finsetSum _ fun i _ => hint j i
  rw [integral_finsetSum _ (fun j _ => hint2 j)]
  refine Finset.sum_nonpos fun j _ => ?_
  rw [integral_finsetSum _ (fun i _ => hint j i)]
  refine Finset.sum_nonpos fun i _ => ?_
  have := sa16sy_diffusion (W := fun idx : Fin (j : ℕ) → Fin d => partialDeriv idx φ.1) (hW j) (p := p)
    (Fact.out : 2 ≤ p) (EuclideanSpace.single i 1)
  exact this

end En7

end HRS.Whole.AppendixA.Phase2SA16R
