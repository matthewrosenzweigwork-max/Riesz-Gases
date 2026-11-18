import HRS.MS.MfeConfAux97

/-!
# S.B.1, packet F9 (part 1): the exact decomposition of the level-`k` source

For `r ∈ [0,T]` the source `S^k_r` of `sb1_lv_ineq` (`sb1_lv_Src`, Aux94) splits exactly as
`S^k_r(Z) = -βN (C^k_r(Z) - E_{Q^k_r} C^k_r) + ∑_i B^k_r(Z_i, Z)` with
* `C^k_r = pairEnergy h_k` (`h_k(x,y) = ∇k(x-y)·(v(x)-v(y))`, `v` = exact transport),
* `B^k_r(x, Z) = (Θ(x) - (∂G v - Ġ)(x))/θ - ⟨e(x), N⁻¹∑_{j≠i}∇k(x-Z_j)⟩/θ`, `e = u^k - v = ∇G^k - F`.
-/

open MeasureTheory Filter Topology InformationTheory
open HRS HRS.Whole HRS.MP.SelfSimP4 HRS.MP.SelfSimP4Mol HRS.MP.SelfSimP4Impl
open scoped ENNReal NNReal BigOperators ContDiff

noncomputable section

namespace HRS.MS.MfeConf

variable {d N : ℕ}

/-- the commutator energy of the level-`k` pair kernel `h_k(x,y) = ∇k(x-y)·(v(x)-v(y))` -/
def sb1_lv_Ck (D : Whole.WholeDyn d) (k : Euc d → ℝ) (N : ℕ) (ρ : ℝ → Euc d → ℝ) (r : ℝ) (Z : EucConfig d N) : ℝ :=
  Whole.pairEnergy (fun x y => fderiv ℝ k (x - y) (Whole.mfeTransportW D (ρ r) x - Whole.mfeTransportW D (ρ r) y)) Z
    (Whole.withDensityReal (ρ r))

/-- `E_{Q^k_r} C^k_r` -/
def sb1_lv_EQ (D : Whole.WholeDyn d) (k : Euc d → ℝ) (N : ℕ) (ρ : ℝ → Euc d → ℝ) (r : ℝ) : ℝ :=
  ∫ Z, sb1_lv_Ck D k N ρ r Z ∂(Whole.modulatedGibbs k N D.invβ⁻¹ (Whole.withDensityReal (ρ r)))

/-- the remainder field `e = u^k - v` -/
def sb1_lv_e (D : Whole.WholeDyn d) (k : Euc d → ℝ) {T : ℝ} (hT : 0 ≤ T) (ρ : ℝ → Euc d → ℝ) (s : ℝ) (x : Euc d) :
    Euc d :=
  sb1_lv_U D k hT ρ s x - Whole.mfeTransportW D (sb1_lv_rb hT ρ s) x

/-- the one-body part of the remainder -/
def sb1_lv_Bone (D : Whole.WholeDyn d) (k : Euc d → ℝ) {T : ℝ} (hT : 0 ≤ T) (ρ : ℝ → Euc d → ℝ) (s : ℝ) (x : Euc d) :
    ℝ :=
  (sb1_lv_Th D k hT ρ s x - (fderiv ℝ (sb1G k (sb1_lv_rb hT ρ s)) x (Whole.mfeTransportW D (sb1_lv_rb hT ρ s) x) -
    sb1_lv_cv k (sb1At D hT ρ s) x)) / D.invβ

/-- the pair part of the remainder -/
def sb1_lv_Bpair (D : Whole.WholeDyn d) (k : Euc d → ℝ) {T : ℝ} (hT : 0 ≤ T) (ρ : ℝ → Euc d → ℝ) (s : ℝ)
    (Z : EucConfig d N) (i : Fin N) : ℝ :=
  -(sb1_lv_pairV (gradient k) (sb1_lv_e D k hT ρ s) Z i) / D.invβ

/-- the remainder `∑_i B(Z_i, Z)` -/
def sb1_lv_B (D : Whole.WholeDyn d) (k : Euc d → ℝ) {T : ℝ} (hT : 0 ≤ T) (ρ : ℝ → Euc d → ℝ) (s : ℝ)
    (Z : EucConfig d N) : ℝ :=
  ∑ i, (sb1_lv_Bone D k hT ρ s (Z i) + sb1_lv_Bpair D k hT ρ s Z i)

section Decomp

variable {D : Whole.WholeDyn d} {T C B C3 : ℝ} {ρ : ℝ → Euc d → ℝ} (H : Sb1Tr3 D T C B C3 ρ) (hT : 0 ≤ T)
  {r₀ : ℝ} {k : Euc d → ℝ}

include H hT

/-- `κ'/θ = βN E_Q C + (βN/2) ċ` at the level `k` -/
theorem sb1_lv_kappa'_div (hk4 : IsP4Kernel d D.s r₀ k) (hθ : 0 < D.invβ) (hN : 1 ≤ N) {r : ℝ}
    (hr : r ∈ Set.Icc (0 : ℝ) T) :
    sb1_lv_kappa' D k N hT ρ r / D.invβ =
      D.invβ⁻¹ * N * sb1_lv_EQ D k N ρ r + (D.invβ⁻¹ * N / 2) * sb1cdot D ρ k r := by
  obtain ⟨Lg, hRg⟩ := sb1_lv_kerR hk4 H.tr.hs0
  have hk := sb1KerU_of_p4 H.tr.hs0 hk4
  have hβ : 0 ≤ D.invβ⁻¹ := (inv_pos.2 hθ).le
  have hcl : sb1_lv_cl' hT r = r := sb1_lv_cl'_of_mem hT hr
  have hρd := (H.tr.slice r hr).dens
  have hK := sb1_lv_Kb_eq H hT (k := k) (β := D.invβ⁻¹) (N := N) r
  rw [hcl] at hK
  have hKpos := sb1_lv_Kb_pos H hT hk hβ hN r (N := N)
  have hdK := sb1_dK_eq H hk hRg hr hβ hN (N := N)
  have hEQ : sb1_lv_EQ D k N ρ r = (∫ X : EucConfig d N, sb1Wf k D.invβ⁻¹ N ρ r X)⁻¹ *
      ∫ X : EucConfig d N, sb1Wf k D.invβ⁻¹ N ρ r X * sb1_lv_Ck D k N ρ r X := by
    unfold sb1_lv_EQ
    rw [sb1_integral_modGibbs hk4.smooth.continuous.measurable hρd]
    have : sb1_lv_Kb k D.invβ⁻¹ N hT ρ r = Whole.gibbsNormalizer k N D.invβ⁻¹ (Whole.withDensityReal (ρ r)) := by
      unfold sb1_lv_Kb; rw [sb1_lv_rb_eq, hcl]
    rw [← this, hK]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun X => ?_)
    simp only [sb1Wf, mul_assoc]
  have hK0 : (∫ X : EucConfig d N, sb1Wf k D.invβ⁻¹ N ρ r X) ≠ 0 := by
    rw [← hK]; exact hKpos.ne'
  unfold sb1_lv_kappa' sb1_lv_Kdot sb1_lv_cdot
  rw [hcl]
  have e1 : sb1_lv_Kb k D.invβ⁻¹ N hT ρ r = ∫ X : EucConfig d N, sb1Wf k D.invβ⁻¹ N ρ r X := hK
  rw [e1, hEQ]
  have hdK' : ∫ X : EucConfig d N, sb1Wdot D ρ k D.invβ⁻¹ N r X =
      D.invβ⁻¹ * N * ∫ X : EucConfig d N, sb1Wf k D.invβ⁻¹ N ρ r X * sb1_lv_Ck D k N ρ r X := hdK
  rw [hdK']
  have hθ0 := hθ.ne'
  field_simp

end Decomp

section Pairs

variable {k : Euc d → ℝ} {Lg : ℝ}

/-- the symmetrisation `∑_{i≠j} ∇k(Z_i-Z_j)·(v_i - v_j) = 2 ∑_{i≠j} ∇k(Z_i-Z_j)·v_i` -/
theorem sb1_lv_pair_sym (hR : Sb1KerR d k Lg) (v : Euc d → Euc d) (Z : EucConfig d N) :
    ∑ i, ∑ j ∈ Finset.univ.erase i, fderiv ℝ k (Z i - Z j) (v (Z i) - v (Z j)) =
      2 * ∑ i, ∑ j ∈ Finset.univ.erase i, fderiv ℝ k (Z i - Z j) (v (Z i)) := by
  set S1 : ℝ := ∑ i, ∑ j ∈ Finset.univ.erase i, fderiv ℝ k (Z i - Z j) (v (Z i)) with hS1
  have hS2 : ∑ i, ∑ j ∈ Finset.univ.erase i, fderiv ℝ k (Z i - Z j) (v (Z j)) = -S1 := by
    rw [MP.SelfSimP4Impl.p4k_sum_swap (fun i j => fderiv ℝ k (Z i - Z j) (v (Z j)))]
    rw [hS1, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← neg_sub (Z i) (Z j)]
    exact sb1_fderiv_odd hR.diff hR.even _ _
  simp only [map_sub, Finset.sum_sub_distrib]
  rw [hS2, ← hS1]
  ring

theorem sb1_lv_pairV_sum (v : Euc d → Euc d) (Z : EucConfig d N) :
    ∑ i, sb1_lv_pairV (gradient k) v Z i =
      (1 / (N : ℝ)) * ∑ i, ∑ j ∈ Finset.univ.erase i, fderiv ℝ k (Z i - Z j) (v (Z i)) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold sb1_lv_pairV
  rw [inner_smul_right, inner_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [real_inner_comm, p4k_inner_grad]

end Pairs

section Main

variable {D : Whole.WholeDyn d} {T C B C3 : ℝ} {ρ : ℝ → Euc d → ℝ} (H : Sb1Tr3 D T C B C3 ρ) (hT : 0 ≤ T)
  {r₀ : ℝ} {k : Euc d → ℝ}

include H hT

/-- **The exact decomposition of the level-`k` source** (E07 of the Pro note SB1-SignedEntropy):
`S^k_r = -βN (C^k_r - E_{Q^k_r} C^k_r) + ∑_i B^k_r(Z_i,Z)`. -/
theorem sb1_lv_S_decomp (hk4 : IsP4Kernel d D.s r₀ k) (hθ : 0 < D.invβ) (hN : 1 ≤ N) {r : ℝ}
    (hr : r ∈ Set.Icc (0 : ℝ) T) (Z : EucConfig d N) :
    sb1S D.invβ (fun _ => sb1DriftM D k N) (fun r => sb1wOne (sb1_lv_U D k hT ρ r))
      (fun s Z => ∑ i, sb1_lv_W D k hT ρ s (Z i) + sb1_lv_kappa' D k N hT ρ s) r Z =
    -(D.invβ⁻¹ * N) * (sb1_lv_Ck D k N ρ r Z - sb1_lv_EQ D k N ρ r) + sb1_lv_B D k hT ρ r Z := by
  obtain ⟨Lg, hRg⟩ := sb1_lv_kerR hk4 H.tr.hs0
  have hk := sb1KerU_of_p4 H.tr.hs0 hk4
  have hρd := (H.tr.slice r hr).dens
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hθ0 := hθ.ne'
  rw [sb1_lv_S_eq H hT hk4 hθ r Z, sb1_lv_kappa'_div H hT hk4 hθ hN hr]
  -- the one-body identity
  have hone : ∀ x, fderiv ℝ (sb1G k (ρ r)) x (Whole.mfeTransportW D (ρ r) x) - sb1Gd D ρ k r x =
      sb1PG (fun x y => fderiv ℝ k (x - y) (Whole.mfeTransportW D (ρ r) x - Whole.mfeTransportW D (ρ r) y)) (ρ r) x :=
    fun x => (sb1_oneBody H hk hRg hr x).symm
  have hrb : sb1_lv_rb hT ρ r = ρ r := sb1_lv_rb_mem hT ρ hr
  have hAt : sb1At D hT ρ r = sb1A D (ρ r) := funext fun x => sb1At_eq hT hr x
  have hcv : ∀ x, sb1_lv_cv k (sb1At D hT ρ r) x = sb1Gd D ρ k r x := fun x => by
    rw [hAt]; rfl
  have hTh : ∀ x, sb1_lv_Th D k hT ρ r x = D.invβ * sb1_lv_Bone D k hT ρ r x +
      sb1PG (fun x y => fderiv ℝ k (x - y) (Whole.mfeTransportW D (ρ r) x - Whole.mfeTransportW D (ρ r) y)) (ρ r) x := by
    intro x
    unfold sb1_lv_Bone
    rw [hrb, hcv, hone x]
    field_simp
    ring
  -- linearity of the pair term
  have hU : ∀ x, sb1_lv_U D k hT ρ r x = Whole.mfeTransportW D (ρ r) x + sb1_lv_e D k hT ρ r x := fun x => by
    unfold sb1_lv_e; rw [hrb]; abel
  have hpV : ∀ i, sb1_lv_pairV (gradient k) (sb1_lv_U D k hT ρ r) Z i =
      sb1_lv_pairV (gradient k) (Whole.mfeTransportW D (ρ r)) Z i +
        sb1_lv_pairV (gradient k) (sb1_lv_e D k hT ρ r) Z i := fun i => by
    unfold sb1_lv_pairV
    rw [hU (Z i), inner_add_left]
  -- the pair energy
  have hC : sb1_lv_Ck D k N ρ r Z = (1 / (N : ℝ) ^ 2) * ∑ i, ∑ j ∈ Finset.univ.erase i, fderiv ℝ k (Z i - Z j) (Whole.mfeTransportW D (ρ r) (Z i)) -
      (1 / (N : ℝ)) * ∑ i, sb1PG (fun x y => fderiv ℝ k (x - y) (Whole.mfeTransportW D (ρ r) x - Whole.mfeTransportW D (ρ r) y)) (ρ r) (Z i) +
      (1 / 2) * ∫ x, ρ r x * sb1PG (fun x y => fderiv ℝ k (x - y) (Whole.mfeTransportW D (ρ r) x - Whole.mfeTransportW D (ρ r) y)) (ρ r) x := by
    unfold sb1_lv_Ck
    rw [sb1_pairEnergy_eq hρd, sb1_lv_pair_sym hRg (Whole.mfeTransportW D (ρ r)) Z]
    field_simp
  have hcd : sb1cdot D ρ k r = -(∫ x, ρ r x * sb1PG (fun x y => fderiv ℝ k (x - y) (Whole.mfeTransportW D (ρ r) x - Whole.mfeTransportW D (ρ r) y)) (ρ r) x) :=
    sb1_cd_eq H hk hRg hr
  have hsum := sb1_lv_pairV_sum (k := k) (Whole.mfeTransportW D (ρ r)) Z
  unfold sb1_lv_Src sb1_lv_B sb1_lv_Bpair
  simp only [hTh, hpV]
  rw [hC, hcd]
  have key : ∑ i, (D.invβ * sb1_lv_Bone D k hT ρ r (Z i) +
        sb1PG (fun x y => fderiv ℝ k (x - y) (Whole.mfeTransportW D (ρ r) x - Whole.mfeTransportW D (ρ r) y)) (ρ r) (Z i) -
        (sb1_lv_pairV (gradient k) (Whole.mfeTransportW D (ρ r)) Z i +
          sb1_lv_pairV (gradient k) (sb1_lv_e D k hT ρ r) Z i)) / D.invβ =
      ∑ i, (sb1_lv_Bone D k hT ρ r (Z i) + -(sb1_lv_pairV (gradient k) (sb1_lv_e D k hT ρ r) Z i) / D.invβ) +
        ((∑ i, sb1PG (fun x y => fderiv ℝ k (x - y) (Whole.mfeTransportW D (ρ r) x - Whole.mfeTransportW D (ρ r) y)) (ρ r) (Z i)) -
          ∑ i, sb1_lv_pairV (gradient k) (Whole.mfeTransportW D (ρ r)) Z i) / D.invβ := by
    rw [← Finset.sum_sub_distrib, Finset.sum_div, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    field_simp
    ring
  rw [key, hsum]
  generalize (∑ i, (sb1_lv_Bone D k hT ρ r (Z i) + -(sb1_lv_pairV (gradient k) (sb1_lv_e D k hT ρ r) Z i) / D.invβ)) = SA
  generalize (∑ i, sb1PG (fun x y => fderiv ℝ k (x - y) (Whole.mfeTransportW D (ρ r) x - Whole.mfeTransportW D (ρ r) y)) (ρ r) (Z i)) = SP
  generalize (∑ i, ∑ j ∈ Finset.univ.erase i, fderiv ℝ k (Z i - Z j) (Whole.mfeTransportW D (ρ r) (Z i))) = S1
  generalize (∫ x, ρ r x * sb1PG (fun x y => fderiv ℝ k (x - y) (Whole.mfeTransportW D (ρ r) x - Whole.mfeTransportW D (ρ r) y)) (ρ r) x) = I
  generalize sb1_lv_EQ D k N ρ r = E
  field_simp
  ring

end Main

end HRS.MS.MfeConf
