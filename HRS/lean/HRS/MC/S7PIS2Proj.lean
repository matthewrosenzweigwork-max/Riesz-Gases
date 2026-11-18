import HRS.MC.S7PIDefs
import HRS.Main.A33Aux14
import HRS.Sections.Q17Aux4

/-!
# Packet piS2, part 4: `s7_PIS_obs_proj` (the Fourier/polygonal projection is a finite-rank observation)
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7PIS2

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.Sec7.PI

variable {d : ℕ}

theorem S7PIS2_box_finite (L : ℕ) : {k : NonzeroLattice d | ∀ i, |k.1 i| ≤ (L : ℤ)}.Finite := by
  have h1 : Set.Finite {x : Lattice d | ∀ i, |x i| ≤ (L : ℤ)} := by
    refine (Set.Finite.pi (t := fun _ : Fin d => Set.Icc (-(L : ℤ)) L)
      (fun _ => Set.finite_Icc _ _)).subset ?_
    intro x hx i _
    exact abs_le.1 (hx i)
  exact h1.preimage Subtype.val_injective.injOn

/-- The frequencies of the box `|k_i| ≤ L`. -/
def S7PIS2_K (d L : ℕ) : Finset (NonzeroLattice d) := (S7PIS2_box_finite (d := d) L).toFinset

theorem S7PIS2_mem_K {L : ℕ} (l : NonzeroLattice d) : l ∈ S7PIS2_K d L ↔ ∀ i, |l.1 i| ≤ (L : ℤ) := by
  unfold S7PIS2_K
  rw [Set.Finite.mem_toFinset]
  rfl

/-- The index set `(j, k)` of the observations. -/
def S7PIS2_S (d L : ℕ) : Finset (Fin (2 ^ L + 1) × NonzeroLattice d) := Finset.univ ×ˢ S7PIS2_K d L

def S7PIS2_q (d L : ℕ) : ℕ := (S7PIS2_S d L).card

/-- Enumeration of the observations. -/
def S7PIS2_p (d L : ℕ) (i : Fin (S7PIS2_q d L)) : Fin (2 ^ L + 1) × NonzeroLattice d :=
  ((S7PIS2_S d L).equivFin.symm i).1

def S7PIS2_t (d L : ℕ) (T : ℝ) (i : Fin (S7PIS2_q d L)) : ℝ := (((S7PIS2_p d L i).1 : ℕ) : ℝ) * T / 2 ^ L

def S7PIS2_phi (d L : ℕ) (i : Fin (S7PIS2_q d L)) : Torus d → ℝ := Torus.realMode (S7PIS2_p d L i).2

/-- The basis vector of `E_m` dual to the `k`-th Fourier coordinate. -/
def S7PIS2_bvec (m : ℝ) (k : NonzeroLattice d) : NegSobolev d m :=
  (lp.single 2 k (Lattice.jp k.1 ^ (-m)) : lp (fun _ : NonzeroLattice d => ℝ) 2)

theorem S7PIS2_coord_bvec (m : ℝ) (k l : NonzeroLattice d) :
    NegSobolev.coord (S7PIS2_bvec m k) l = if l = k then Lattice.jp k.1 ^ (-m) else 0 := by
  unfold NegSobolev.coord S7PIS2_bvec
  rw [lp.single_apply, Pi.single_apply]

/-- The hat function times the basis vector, as a path. -/
def S7PIS2_hatPath (m T : ℝ) (L : ℕ) (j : ℕ) (k : NonzeroLattice d) : PathSpace d m T :=
  show C(Set.Icc (0 : ℝ) T, NegSobolev d m) from
    ⟨fun s => max 0 (1 - |(s : ℝ) * 2 ^ L / T - j|) • S7PIS2_bvec m k, by fun_prop⟩

/-- The synthesis operator `Λ`. -/
def S7PIS2_Lam (d : ℕ) (m T : ℝ) (L : ℕ) :
    EuclideanSpace ℝ (Fin (S7PIS2_q d L)) →L[ℝ] PathSpace d m T :=
  ∑ i : Fin (S7PIS2_q d L), (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin (S7PIS2_q d L)) →L[ℝ] ℝ).smulRight
    (S7PIS2_hatPath m T L ((S7PIS2_p d L i).1 : ℕ) (S7PIS2_p d L i).2)

/-- Evaluation at a time as an additive homomorphism. -/
def S7PIS2_atHom (m T : ℝ) (s : Set.Icc (0 : ℝ) T) : PathSpace d m T →+ NegSobolev d m where
  toFun w := PathSpace.at' w s
  map_zero' := rfl
  map_add' _ _ := rfl

/-- A coordinate of `E_m` as an additive homomorphism. -/
def S7PIS2_coordHom (m : ℝ) (k : NonzeroLattice d) : NegSobolev d m →+ ℝ where
  toFun F := NegSobolev.coord F k
  map_zero' := by unfold NegSobolev.coord; rfl
  map_add' F G := q17_coord_add F G k

theorem S7PIS2_coord_smul (m : ℝ) (c : ℝ) (F : NegSobolev d m) (k : NonzeroLattice d) :
    NegSobolev.coord (c • F) k = c * NegSobolev.coord F k := by
  unfold NegSobolev.coord; rfl

theorem S7PIS2_Lam_apply (m T : ℝ) (L : ℕ) (c : EuclideanSpace ℝ (Fin (S7PIS2_q d L)))
    (s : Set.Icc (0 : ℝ) T) :
    (show C(Set.Icc (0 : ℝ) T, NegSobolev d m) from S7PIS2_Lam d m T L c) s =
      ∑ i : Fin (S7PIS2_q d L), (c i * max 0 (1 - |(s : ℝ) * 2 ^ L / T - ((S7PIS2_p d L i).1 : ℕ)|)) •
        S7PIS2_bvec m (S7PIS2_p d L i).2 := by
  unfold S7PIS2_Lam
  rw [ContinuousLinearMap.sum_apply]
  show S7PIS2_atHom m T s _ = _
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  show (c i) • (max 0 (1 - |(s : ℝ) * 2 ^ L / T - ((S7PIS2_p d L i).1 : ℕ)|) •
    S7PIS2_bvec m (S7PIS2_p d L i).2) = _
  rw [smul_smul]

theorem S7PIS2_t_mem (T : ℝ) (hT : 0 < T) (L : ℕ) (i : Fin (S7PIS2_q d L)) :
    S7PIS2_t d L T i ∈ Set.Icc (0 : ℝ) T := by
  unfold S7PIS2_t
  have hj : (((S7PIS2_p d L i).1 : ℕ) : ℝ) ≤ 2 ^ L := by
    have := (S7PIS2_p d L i).1.2
    exact_mod_cast Nat.lt_succ_iff.mp this
  have h2 : (0 : ℝ) < 2 ^ L := by positivity
  constructor
  · positivity
  · rw [div_le_iff₀ h2]; nlinarith

theorem S7PIS2_at_projIcc {m T : ℝ} (hT : 0 < T) (w : PathSpace d m T) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) T) :
    PathSpace.at' w (Set.projIcc 0 T hT.le x) = pathAt w x := by
  unfold pathAt
  rw [dif_pos hx, Set.projIcc_of_mem _ hx]

theorem S7PIS2_proj_eq (m T : ℝ) (hT : 0 < T) (L : ℕ) (w : PathSpace d m T) :
    projPoly m T hT.le L w =
      S7PIS2_Lam d m T L (obsVec m T (S7PIS2_t d L T) (S7PIS2_phi d L) w) := by
  classical
  refine ContinuousMap.ext fun s => ?_
  have hL : PathSpace.at' (projPoly m T hT.le L w) s = ∑ j ∈ Finset.range (2 ^ L + 1),
      max 0 (1 - |(s : ℝ) * 2 ^ L / T - j|) •
        fourierProj m L (PathSpace.at' w (Set.projIcc 0 T hT.le (j * T / 2 ^ L))) := rfl
  have hR := S7PIS2_Lam_apply m T L (obsVec m T (S7PIS2_t d L T) (S7PIS2_phi d L) w) s
  refine hL.trans (Eq.trans ?_ hR.symm)
  apply q17_ext
  intro l
  show S7PIS2_coordHom m l _ = S7PIS2_coordHom m l _
  rw [map_sum, map_sum]
  simp only [S7PIS2_coordHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, S7PIS2_coord_smul,
    q17_coord_fourierProj, S7PIS2_coord_bvec]
  -- the common form
  set hat : ℕ → ℝ := fun j => max 0 (1 - |(s : ℝ) * 2 ^ L / T - j|) with hhat
  set G : Fin (2 ^ L + 1) × NonzeroLattice d → ℝ := fun x =>
    if l = x.2 then hat x.1 * NegSobolev.coord (pathAt w ((x.1 : ℕ) * T / 2 ^ L)) l else 0 with hG
  have hjmem : ∀ j : Fin (2 ^ L + 1), ((j : ℕ) : ℝ) * T / 2 ^ L ∈ Set.Icc (0 : ℝ) T := fun j => by
    have hj : ((j : ℕ) : ℝ) ≤ 2 ^ L := by exact_mod_cast Nat.lt_succ_iff.mp j.2
    have h2 : (0 : ℝ) < 2 ^ L := by positivity
    constructor
    · positivity
    · rw [div_le_iff₀ h2]; nlinarith
  have hRHS : ∑ i : Fin (S7PIS2_q d L), (obsVec m T (S7PIS2_t d L T) (S7PIS2_phi d L) w i *
        max 0 (1 - |(s : ℝ) * 2 ^ L / T - ((S7PIS2_p d L i).1 : ℕ)|)) *
        (if l = (S7PIS2_p d L i).2 then Lattice.jp (S7PIS2_p d L i).2.1 ^ (-m) else 0) =
      ∑ j : Fin (2 ^ L + 1), if l ∈ S7PIS2_K d L then
        hat j * NegSobolev.coord (pathAt w ((j : ℕ) * T / 2 ^ L)) l else 0 := by
    have h1 : ∀ i : Fin (S7PIS2_q d L), (obsVec m T (S7PIS2_t d L T) (S7PIS2_phi d L) w i *
        max 0 (1 - |(s : ℝ) * 2 ^ L / T - ((S7PIS2_p d L i).1 : ℕ)|)) *
        (if l = (S7PIS2_p d L i).2 then Lattice.jp (S7PIS2_p d L i).2.1 ^ (-m) else 0) =
        G (S7PIS2_p d L i) := fun i => by
      by_cases hl : l = (S7PIS2_p d L i).2
      · have hobs : obsVec m T (S7PIS2_t d L T) (S7PIS2_phi d L) w i =
            Lattice.jp (S7PIS2_p d L i).2.1 ^ m *
              NegSobolev.coord (pathAt w ((((S7PIS2_p d L i).1 : ℕ) : ℝ) * T / 2 ^ L)) (S7PIS2_p d L i).2 := by
          show NegSobolev.eval (pathAt w (S7PIS2_t d L T i)) (S7PIS2_phi d L i) = _
          unfold S7PIS2_phi
          rw [HRS.A33.a33_eval_realMode]
          rfl
        simp only [hG, hl, if_true, hobs, hhat]
        have hjp := q17_jp_mul_rpow (m := m) (S7PIS2_p d L i).2 
          (NegSobolev.coord (pathAt w ((((S7PIS2_p d L i).1 : ℕ) : ℝ) * T / 2 ^ L)) (S7PIS2_p d L i).2)
        linear_combination (max 0 (1 - |(s : ℝ) * 2 ^ L / T - (((S7PIS2_p d L i).1 : ℕ) : ℝ)|)) * hjp
      · simp [hG, hl]
    rw [Finset.sum_congr rfl fun i _ => h1 i]
    rw [show ∑ i : Fin (S7PIS2_q d L), G (S7PIS2_p d L i) = ∑ x ∈ S7PIS2_S d L, G x from ?_]
    · rw [S7PIS2_S, Finset.sum_product]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [hG]
      rw [Finset.sum_ite_eq]
    · rw [← Finset.sum_coe_sort (S7PIS2_S d L) G]
      exact Fintype.sum_equiv (S7PIS2_S d L).equivFin.symm
        (fun i : Fin (S7PIS2_q d L) => G (S7PIS2_p d L i)) (fun x => G x.1) (fun i => rfl)
  rw [hRHS]
  rw [← Fin.sum_univ_eq_sum_range (fun j : ℕ => max 0 (1 - |(s : ℝ) * 2 ^ L / T - (j : ℝ)|) *
    (q17_ind L l * NegSobolev.coord (PathSpace.at' w (Set.projIcc 0 T hT.le ((j : ℝ) * T / 2 ^ L))) l)) (2 ^ L + 1)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [S7PIS2_at_projIcc hT w (hjmem j)]
  by_cases hl : l ∈ S7PIS2_K d L
  · have : q17_ind L l = 1 := by rw [q17_ind, if_pos ((S7PIS2_mem_K l).1 hl)]
    simp [hl, this, hhat]
  · have : q17_ind L l = 0 := by rw [q17_ind, if_neg (fun h => hl ((S7PIS2_mem_K l).2 h))]
    simp [hl, this]
theorem s7_PIS_obs_proj_proof (m T : ℝ) (hT : 0 < T) (L : ℕ) :
    ∃ (q : ℕ) (t : Fin q → ℝ) (φ : Fin q → Torus d → ℝ) (Λ : EuclideanSpace ℝ (Fin q) →L[ℝ] PathSpace d m T),
      IsGridData m T hT.le L q t φ Λ :=
  ⟨S7PIS2_q d L, S7PIS2_t d L T, S7PIS2_phi d L, S7PIS2_Lam d m T L,
    S7PIS2_t_mem T hT L, fun i => ⟨(S7PIS2_p d L i).2, rfl⟩, S7PIS2_proj_eq m T hT L⟩

end HRS.MC.Sec7.S7PIS2

end
