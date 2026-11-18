import HRS.MC.Q714GWLimit
import HRS.Sections.QuenchAux5

/-!
# Packet GW (row 7.14): Gaussianity of linear functionals of finitely many time slices

For a mode field `Z` (the coordinates `Z^t(e_j)` are jointly Gaussian and centred), every continuous linear functional of finitely many
time slices `Z^{τ_1}, ..., Z^{τ_n}` is a centred real Gaussian: it is the pointwise limit of finite combinations of coordinates
(`lp.hasSum_single`), which are centred Gaussian by `isGaussianProcess_Xmode`; then `gw_gauss_limit`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.Q714.GW

open HRS HRS.Sec7 HRS.Qch

variable {d : ℕ}

/-- The coordinate vector `e_j ∈ E_m`. -/
def gwE (m : ℝ) (j : NonzeroLattice d) : NegSobolev d m :=
  lp.single (E := fun _ : NonzeroLattice d => ℝ) 2 j 1

theorem gw_dual_hasSum_lp (L' : lp (fun _ : NonzeroLattice d => ℝ) 2 →L[ℝ] ℝ)
    (F : lp (fun _ : NonzeroLattice d => ℝ) 2) :
    HasSum (fun j : NonzeroLattice d => F j *
      L' (lp.single (E := fun _ : NonzeroLattice d => ℝ) 2 j (1 : ℝ))) (L' F) := by
  have h := lp.hasSum_single (p := 2) (E := fun _ : NonzeroLattice d => ℝ) (by simp) F
  have h2 := h.mapL L'
  have key : ∀ j : NonzeroLattice d, F j *
      L' (lp.single (E := fun _ : NonzeroLattice d => ℝ) 2 j (1 : ℝ)) =
      L' (lp.single (E := fun _ : NonzeroLattice d => ℝ) 2 j (F j)) := by
    intro j
    have e := lp.single_smul (E := fun _ : NonzeroLattice d => ℝ) 2 j (F j) (1 : ℝ)
    rw [smul_eq_mul, mul_one] at e
    rw [e, map_smul, smul_eq_mul]
  simp_rw [key]
  exact h2

/-- A continuous linear functional on `E_m` is the sum of its action on the coordinate vectors. -/
theorem gw_dual_hasSum {m : ℝ} (L : StrongDual ℝ (NegSobolev d m)) (F : NegSobolev d m) :
    HasSum (fun j : NonzeroLattice d => NegSobolev.coord F j * L (gwE m j)) (L F) :=
  gw_dual_hasSum_lp L F

section Proc

variable {s β β₀ m : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {Z : ℝ → Ω → NegSobolev d m} {Y : Ω → NegSobolev d m}

/-- The Fourier coordinate process `(j, t) ↦ Ẑ^t(j)`. -/
def gwFc (Z : ℝ → Ω → NegSobolev d m) (p : NonzeroLattice d × ℝ≥0) (ω : Ω) : ℝ :=
  NegSobolev.fourierCoeff (Z p.2 ω) p.1

theorem gw_Fc_process (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hβ : 0 < β)
    (mf : ModeField d s β β₀ m P Z Y) : IsGaussianProcess (gwFc Z) P := by
  have h := isGaussianProcess_Xmode hd hs0 hsd hβ mf
  have h1 := (h.comp_right (fun p : NonzeroLattice d × ℝ≥0 =>
    (⟨(equiv d).symm p.1, p.2⟩ : (_ : PosHalf d × Bool) × ℝ≥0))).smul
    (fun p => sgn ((equiv d).symm p.1).2)
  have e : gwFc Z = fun (p : NonzeroLattice d × ℝ≥0) ω => sgn ((equiv d).symm p.1).2 •
      ((fun (q : (_ : PosHalf d × Bool) × ℝ≥0) ω => Xmode Z q.1 q.2 ω) ∘
        (fun p : NonzeroLattice d × ℝ≥0 =>
          (⟨(equiv d).symm p.1, p.2⟩ : (_ : PosHalf d × Bool) × ℝ≥0))) p ω := by
    funext p ω
    simp only [gwFc, Function.comp_apply, Xmode_eq, smul_eq_mul]
    rw [← mul_assoc, ← sq, sgn_sq, one_mul, ← equiv_apply, Equiv.apply_symm_apply]
  rw [e]
  exact h1

/-- Finite combinations of coordinates of finitely many time slices are centred Gaussian. -/
theorem gw_comb_gaussian (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hβ : 0 < β)
    (mf : ModeField d s β β₀ m P Z Y) {ι : Type} [Fintype ι] (τ : ι → ℝ≥0)
    (c : ι → NonzeroLattice d → ℝ) (S : Finset (NonzeroLattice d)) :
    HasGaussianLaw (fun ω => ∑ k, ∑ j ∈ S, c k j * NegSobolev.fourierCoeff (Z (τ k) ω) j) P ∧
    ∫ ω, ∑ k, ∑ j ∈ S, c k j * NegSobolev.fourierCoeff (Z (τ k) ω) j ∂P = 0 := by
  classical
  have hQ : IsGaussianProcess (fun (q : ι × NonzeroLattice d) ω => c q.1 q.2 • gwFc Z (q.2, τ q.1) ω) P :=
    ((gw_Fc_process hd hs0 hsd hβ mf).comp_right (fun q : ι × NonzeroLattice d => (q.2, τ q.1))).smul
      (fun q => c q.1 q.2)
  have hsum := hQ.hasGaussianLaw_fun_sum (I := (Finset.univ : Finset ι) ×ˢ S)
  have e : (fun ω => ∑ k, ∑ j ∈ S, c k j * NegSobolev.fourierCoeff (Z (τ k) ω) j) =
      fun ω => ∑ q ∈ (Finset.univ : Finset ι) ×ˢ S, c q.1 q.2 • gwFc Z (q.2, τ q.1) ω := by
    funext ω
    rw [Finset.sum_product]
    rfl
  rw [e]
  refine ⟨hsum, ?_⟩
  rw [integral_finsetSum]
  · refine Finset.sum_eq_zero fun q _ => ?_
    simp only [smul_eq_mul, gwFc]
    rw [integral_const_mul, mean_fcZ hd hs0 hsd hβ mf q.2 (NNReal.coe_nonneg _), mul_zero]
  · intro q _
    exact (((memLp2_fcZ hd hs0 hsd hβ mf q.2 (NNReal.coe_nonneg (τ q.1))).integrable one_le_two).const_mul
      (c q.1 q.2))

/-- A continuous linear functional of finitely many time slices of the mode field is a centred real Gaussian. -/
theorem gw_lin_gaussian (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hβ : 0 < β)
    (mf : ModeField d s β β₀ m P Z Y) {ι : Type} [Fintype ι] (τ : ι → ℝ≥0)
    (L : ι → StrongDual ℝ (NegSobolev d m)) (W : Ω → ℝ) (hW : AEMeasurable W P)
    (hWeq : ∀ᵐ ω ∂P, W ω = ∑ k, L k (Z (τ k) ω)) :
    ∃ v : ℝ≥0, P.map W = gaussianReal 0 v := by
  classical
  obtain ⟨S, hS⟩ := (Filter.atTop : Filter (Finset (NonzeroLattice d))).exists_seq_tendsto
  set c : ι → NonzeroLattice d → ℝ := fun k j => L k (gwE m j) * (Lattice.jp j.1 ^ m)⁻¹ with hc
  set U : ℕ → Ω → ℝ := fun N ω => ∑ k, ∑ j ∈ S N, c k j * NegSobolev.fourierCoeff (Z (τ k) ω) j with hU
  have hG : ∀ N, HasGaussianLaw (U N) P ∧ ∫ ω, U N ω ∂P = 0 :=
    fun N => gw_comb_gaussian hd hs0 hsd hβ mf τ c (S N)
  have hmap : ∀ N, P.map (U N) = gaussianReal 0 (Var[U N; P]).toNNReal := by
    intro N
    rw [(hG N).1.map_eq_gaussianReal]
    congr 2
    exact (hG N).2
  refine gw_gauss_limit P hmap ?_ hW (fun N => (hG N).1.aemeasurable)
  filter_upwards [hWeq] with ω hω
  rw [hω]
  refine tendsto_finsetSum _ fun k _ => ?_
  have h1 := (gw_dual_hasSum (L k) (Z (τ k) ω))
  have h2 : Tendsto (fun N => ∑ j ∈ S N, NegSobolev.coord (Z (τ k) ω) j * L k (gwE m j)) atTop
      (𝓝 (L k (Z (τ k) ω))) := h1.comp hS
  refine h2.congr fun N => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  have hp : Lattice.jp j.1 ^ m ≠ 0 := (Real.rpow_pos_of_pos (Torus.jp_pos _) _).ne'
  simp only [hc, NegSobolev.fourierCoeff]
  field_simp
end Proc

end HRS.MC.Q714.GW
