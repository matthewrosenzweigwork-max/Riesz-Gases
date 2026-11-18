import HRS.MS.SA16SOp1

/-!
# S.A.16 (SA16S) Op2: the transport operator `b·∇ : W^{k+1,p} → W^{k,p}` and the Laplacian `Δ : W^{k+2,p} → W^{k,p}`

Coefficients `b_i` smooth with bounded derivatives up to order `k` (`SA16BddCoef`).  Both are obtained from
`sa16so_extend`; the zeroth component on the jet of `φ ∈ C_c^∞` is `∑ b_i ∂_iφ`, resp. `Δφ`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section Op2
variable {d : ℕ}

lemma sa16so_norm_iter_dir {f : Euc d → ℝ} (hf : ContDiff ℝ ∞ f) (e : Euc d) (n : ℕ) (x : Euc d) :
    ‖iteratedFDeriv ℝ n (fun y => fderiv ℝ f y e) x‖ ≤ ‖e‖ * ‖iteratedFDeriv ℝ (n + 1) f x‖ := by
  have h1 := norm_iteratedFDeriv_clm_apply_const (𝕜 := ℝ) (f := fderiv ℝ f) (c := e) (N := ∞) (n := n)
    (x := x) (hf.fderiv_right (m := ∞) (by simp)).contDiffAt (by exact_mod_cast le_top)
  rwa [norm_iteratedFDeriv_fderiv] at h1

lemma sa16so_dir_smooth {f : Euc d → ℝ} (hf : ContDiff ℝ ∞ f) (e : Euc d) :
    ContDiff ℝ ∞ (fun y => fderiv ℝ f y e) :=
  (hf.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const

/-- smooth coefficients with bounded derivatives of order `≤ k` -/
structure SA16BddCoef (k : ℕ) (B : ℝ) (bc : Fin d → Euc d → ℝ) : Prop where
  nonneg : 0 ≤ B
  smooth : ∀ i, ContDiff ℝ ∞ (bc i)
  bound : ∀ i, ∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j (bc i) x‖ ≤ B

/-- the transport field `∑ b_i ∂_i φ` -/
def sa16so_transportFun (bc : Fin d → Euc d → ℝ) (φ : Euc d → ℝ) (x : Euc d) : ℝ :=
  ∑ i, bc i x * fderiv ℝ φ x (EuclideanSpace.single i 1)

/-- the constant of the transport estimate -/
def sa16so_cB (d k : ℕ) (B : ℝ) : ℝ :=
  ((k : ℝ) + 1) * ((d : ℝ) * (2 ^ k * (B * ((d : ℝ) + 1) ^ (k + 1))))

lemma sa16so_cB_nonneg (d k : ℕ) {B : ℝ} (hB : 0 ≤ B) : 0 ≤ sa16so_cB d k B := by
  unfold sa16so_cB; positivity

lemma sa16so_transportFun_smooth {k : ℕ} {B : ℝ} {bc : Fin d → Euc d → ℝ} (hb : SA16BddCoef k B bc)
    {φ : Euc d → ℝ} (hφ : ContDiff ℝ ∞ φ) : ContDiff ℝ ∞ (sa16so_transportFun bc φ) := by
  unfold sa16so_transportFun
  exact ContDiff.sum fun i _ => (hb.smooth i).mul (sa16so_dir_smooth hφ _)

lemma sa16so_prod_iter {k : ℕ} {B : ℝ} {bc : Fin d → Euc d → ℝ} (hb : SA16BddCoef k B bc) {φ : Euc d → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (i : Fin d) {j : ℕ} (hj : j ≤ k) (x : Euc d) :
    ‖iteratedFDeriv ℝ j (fun y => bc i y * fderiv ℝ φ y (EuclideanSpace.single i 1)) x‖ ≤
      2 ^ k * (B * ((d : ℝ) + 1) ^ (k + 1)) * ‖wJet (k + 1) φ x‖ := by
  have hB0 : 0 ≤ B := hb.nonneg
  have hJ0 := norm_nonneg (wJet (k + 1) φ x)
  have hL := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) ((hb.smooth i).of_le (by exact_mod_cast le_top))
    ((sa16so_dir_smooth hφ (EuclideanSpace.single i 1)).of_le (by exact_mod_cast le_top)) x (n := j)
    (N := (j : ℕ∞ω)) le_rfl
  refine hL.trans ?_
  have hterm : ∀ l ∈ Finset.range (j + 1), (j.choose l : ℝ) * ‖iteratedFDeriv ℝ l (bc i) x‖ *
      ‖iteratedFDeriv ℝ (j - l) (fun y => fderiv ℝ φ y (EuclideanSpace.single i 1)) x‖ ≤
      (j.choose l : ℝ) * (B * ((d : ℝ) + 1) ^ (k + 1) * ‖wJet (k + 1) φ x‖) := by
    intro l hl
    have hl' : l ≤ j := by have := Finset.mem_range.1 hl; omega
    have h1 := hb.bound i l (hl'.trans hj) x
    have h2 := sa16so_norm_iter_dir hφ (EuclideanSpace.single i 1) (j - l) x
    rw [PiLp.norm_single, norm_one, one_mul] at h2
    have h3 := sa16y_iter_le_jet φ x (n := k + 1) (l := j - l + 1) (by omega)
    have h4 : ((d : ℝ)) ^ (j - l + 1) ≤ ((d : ℝ) + 1) ^ (k + 1) := by
      calc ((d : ℝ)) ^ (j - l + 1) ≤ ((d : ℝ) + 1) ^ (j - l + 1) :=
            pow_le_pow_left₀ (Nat.cast_nonneg d) (by linarith) _
        _ ≤ ((d : ℝ) + 1) ^ (k + 1) :=
            pow_le_pow_right₀ (by have : (0 : ℝ) ≤ d := Nat.cast_nonneg d; linarith) (by omega)
    have h5 : ‖iteratedFDeriv ℝ (j - l) (fun y => fderiv ℝ φ y (EuclideanSpace.single i 1)) x‖ ≤
        ((d : ℝ) + 1) ^ (k + 1) * ‖wJet (k + 1) φ x‖ :=
      h2.trans (h3.trans (mul_le_mul_of_nonneg_right h4 hJ0))
    have hc : (0 : ℝ) ≤ j.choose l := Nat.cast_nonneg _
    calc (j.choose l : ℝ) * ‖iteratedFDeriv ℝ l (bc i) x‖ *
          ‖iteratedFDeriv ℝ (j - l) (fun y => fderiv ℝ φ y (EuclideanSpace.single i 1)) x‖
        ≤ (j.choose l : ℝ) * B * (((d : ℝ) + 1) ^ (k + 1) * ‖wJet (k + 1) φ x‖) :=
          mul_le_mul (mul_le_mul_of_nonneg_left h1 hc) h5 (norm_nonneg _) (mul_nonneg hc hB0)
      _ = _ := by ring
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.sum_mul]
  have hsum : ∑ l ∈ Finset.range (j + 1), (j.choose l : ℝ) = 2 ^ j := by
    exact_mod_cast Nat.sum_range_choose j
  rw [hsum]
  have : (2 : ℝ) ^ j ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hj
  have hBJ : 0 ≤ B * ((d : ℝ) + 1) ^ (k + 1) * ‖wJet (k + 1) φ x‖ := by positivity
  calc (2 : ℝ) ^ j * (B * ((d : ℝ) + 1) ^ (k + 1) * ‖wJet (k + 1) φ x‖)
      ≤ 2 ^ k * (B * ((d : ℝ) + 1) ^ (k + 1) * ‖wJet (k + 1) φ x‖) := mul_le_mul_of_nonneg_right this hBJ
    _ = _ := by ring

lemma sa16so_transport_jet {k : ℕ} {B : ℝ} {bc : Fin d → Euc d → ℝ} (hb : SA16BddCoef k B bc)
    {φ : Euc d → ℝ} (hφ : ContDiff ℝ ∞ φ) (x : Euc d) :
    ‖wJet k (sa16so_transportFun bc φ) x‖ ≤ sa16so_cB d k B * ‖wJet (k + 1) φ x‖ := by
  refine (sa16j_jet_norm_le k _ x).trans ?_
  have hterm : ∀ j ∈ Finset.range (k + 1), ‖iteratedFDeriv ℝ j (sa16so_transportFun bc φ) x‖ ≤
      (d : ℝ) * (2 ^ k * (B * ((d : ℝ) + 1) ^ (k + 1)) * ‖wJet (k + 1) φ x‖) := by
    intro j hj
    have hj' : j ≤ k := by have := Finset.mem_range.1 hj; omega
    have hfun : sa16so_transportFun bc φ =
        fun y => ∑ i, bc i y * fderiv ℝ φ y (EuclideanSpace.single i 1) := rfl
    rw [hfun, iteratedFDeriv_fun_sum_apply (fun i _ => (((hb.smooth i).mul
      (sa16so_dir_smooth hφ (EuclideanSpace.single i 1))).contDiffAt).of_le (by exact_mod_cast le_top))]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ i : Fin d, ‖iteratedFDeriv ℝ j (fun y => bc i y * fderiv ℝ φ y (EuclideanSpace.single i 1)) x‖
        ≤ ∑ i : Fin d, 2 ^ k * (B * ((d : ℝ) + 1) ^ (k + 1)) * ‖wJet (k + 1) φ x‖ :=
          Finset.sum_le_sum fun i _ => sa16so_prod_iter hb hφ i hj' x
      _ = _ := by simp
  refine (Finset.sum_le_sum hterm).trans ?_
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  unfold sa16so_cB
  push_cast
  ring_nf
  exact le_refl _

/-- the linear map `φ ↦ ∑ b_i ∂_iφ` on `C_c^∞` -/
def sa16so_transportL {k : ℕ} {B : ℝ} {bc : Fin d → Euc d → ℝ} (hb : SA16BddCoef k B bc) :
    ccSub d →ₗ[ℝ] (Euc d → ℝ) where
  toFun φ := sa16so_transportFun bc φ.1
  map_add' φ ψ := by
    funext x
    have h1 : DifferentiableAt ℝ φ.1 x := φ.2.1.differentiable (by simp) x
    have h2 : DifferentiableAt ℝ ψ.1 x := ψ.2.1.differentiable (by simp) x
    simp only [sa16so_transportFun, Submodule.coe_add, Pi.add_apply]
    rw [fderiv_add h1 h2]
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' c φ := by
    funext x
    have h1 : DifferentiableAt ℝ φ.1 x := φ.2.1.differentiable (by simp) x
    simp only [sa16so_transportFun, Submodule.coe_smul, Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
    rw [fderiv_const_smul h1]
    simp [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring

theorem sa16so_transport_exists (k : ℕ) (p : ℝ) [Fact (2 ≤ p)] {B : ℝ} {bc : Fin d → Euc d → ℝ}
    (hb : SA16BddCoef k B bc) :
    ∃ T : WmpSpace d (k + 1) p →L[ℝ] WmpSpace d k p, ‖T‖ ≤ sa16so_cB d k B ∧
      ∀ φ : ccSub d, wrep d k p (T (sa16r_Jcc d (k + 1) p φ)) =ᵐ[volume] sa16so_transportFun bc φ.1 := by
  exact sa16so_extend d k (k + 1) p (sa16so_transportL hb) (fun φ => sa16so_transportFun_smooth hb φ.2.1)
    (sa16so_cB_nonneg d k hb.nonneg) (fun φ x => sa16so_transport_jet hb φ.2.1 x)

end Op2

end HRS.Whole.AppendixA.Phase2SA16R
