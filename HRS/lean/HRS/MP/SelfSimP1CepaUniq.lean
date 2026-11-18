import HRS.Whole.AppendixAAdjoint

/-!
# MPP1CEPA (a): deterministic uniqueness of ordered null-occupation solutions of the Cépa-Lépingle equation on the line

Part of packet P1 of the S.A.28 plan (`HRS/MP/SelfSimSpec.lean`), Cépa branch (`d = 1`, `s = 0`, `M = -1`, `V = 0`).

For a fixed driving path `w` and a fixed starting configuration `x₀` with pairwise distinct coordinates, any two
paths `x`, `y` that (i) solve the integrated equation `x_t = x₀ + ∫_0^t b(x_r) dr + √(2ν)(w_t - w_0)` on `[0,T]`
with `b = particleDriftW ⟨0,-1,0,ν⟩` locally integrable, (ii) have Lebesgue-null contact occupation on `[0,T]` and
(iii) are ordered on `[0,T]` by some permutation (`ssp1c_OrdBy`; the clauses of `IsWholeCepaLepingleFlow` for a fixed
sample point) coincide on `[0,T]`.  The noise cancels, `x - y` is absolutely continuous, `b = -∇U` is monotone on the
open Weyl chamber, and `|x - y|²` is nonincreasing.  The ordering permutation is forced by `x₀`
(`ssp1c_perm_unique`).
-/

noncomputable section

open MeasureTheory Filter Topology Set
open HRS.Whole HRS.Whole.AppendixA
open scoped BigOperators

namespace HRS.MP.SelfSimP1

/-- The Cépa-Lépingle dynamics on the line: `s = 0`, `M = -1`, `V = 0`, `invβ = ν`. -/
def ssp1c_D (invβ : ℝ) : WholeDyn 1 := ⟨0, -1, fun _ => 0, invβ⟩

/-! ### The drift in coordinates -/

theorem ssp1c_rkg_apply {u : Euc 1} (hu : u ≠ 0) : rieszKernelGrad 1 0 u 0 = -(1 / u 0) := by
  unfold rieszKernelGrad
  rw [q09_gradient_apply]
  have := q09_H_eq_fderiv 0 0 hu
  rw [this]
  have hn : ‖u‖ = |u 0| := by
    rw [EuclideanSpace.norm_eq]; simp [Real.sqrt_sq_eq_abs]
  have h0 : u 0 ≠ 0 := by
    intro h; apply hu; ext i; fin_cases i; simpa using h
  simp only [q09_H, q09_c, ite_true, hn]
  rw [show (-(0:ℝ) - 2) = -((2:ℕ):ℝ) by norm_num, Real.rpow_neg (abs_nonneg _), Real.rpow_natCast,
    sq_abs]
  field_simp

theorem ssp1c_matVec_neg (v : Euc 1) : Torus.matVec (-1 : Matrix (Fin 1) (Fin 1) ℝ) v = -v := by
  simp [Torus.matVec]

/-- Coordinate formula for the drift away from collisions: `b_i(x) = N⁻¹ ∑_{j≠i} 1/(x_i - x_j)`. -/
theorem ssp1c_drift_apply {N : ℕ} (invβ : ℝ) (x : EucConfig 1 N) (i : Fin N)
    (hx : ∀ j, j ≠ i → x i ≠ x j) :
    particleDriftW (ssp1c_D invβ) x i 0 =
      (1 / (N : ℝ)) * ∑ j ∈ Finset.univ.erase i, 1 / (x i 0 - x j 0) := by
  have h0 : gradient (fun _ : Euc 1 => (0 : ℝ)) (x i) = 0 := by simp [gradient]
  simp only [particleDriftW, ssp1c_D, h0, sub_zero, ssp1c_matVec_neg]
  rw [PiLp.smul_apply, WithLp.ofLp_sum]
  simp only [smul_eq_mul, Finset.sum_apply]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  have hne : x i - x j ≠ 0 := sub_ne_zero.2 (hx j (Finset.ne_of_mem_erase hj))
  simp [ssp1c_rkg_apply hne]

section Defs

variable {N : ℕ}

/-- The path `p` is ordered on `[0,T]` by the permutation `π` (`IsWholeCepaLepingleFlow.ordered`, `d = 1`). -/
def ssp1c_OrdBy (T : ℝ) (p : ℝ → EucConfig 1 N) (π : Equiv.Perm (Fin N)) : Prop :=
  ∀ t ∈ Icc (0 : ℝ) T, ∀ j : Fin 1, ∀ k k' : Fin N, k ≤ k' → p t (π k) j ≤ p t (π k') j

/-- `p` (the real-time path `r ↦ X (toNNReal r) ζ`) is an ordered null-occupation solution on `[0,T]` of the
integrated Cépa-Lépingle equation started at `x₀` and driven by `w`: the clauses `init`, `eqn`, `occupation`,
`ordered` of `IsWholeCepaLepingleFlow` for a fixed sample point. -/
structure ssp1c_Sol (invβ T : ℝ) (x₀ : EucConfig 1 N) (w p : ℝ → EucConfig 1 N) : Prop where
  init : p 0 = x₀
  eqn : ∀ t ∈ Icc (0 : ℝ) T,
    (∀ i, IntegrableOn (fun r : ℝ => particleDriftW (ssp1c_D invβ) (p r) i) (Icc 0 t)) ∧
    ∀ i, p t i = p 0 i + (∫ r in Icc (0 : ℝ) t, particleDriftW (ssp1c_D invβ) (p r) i) +
      Real.sqrt (2 * invβ) • (w t i - w 0 i)
  occ : volume {r : ℝ | r ∈ Icc (0 : ℝ) T ∧ p r ∈ eucCollisionSet 1 N} = 0
  ord : ∃ π : Equiv.Perm (Fin N), ssp1c_OrdBy T p π

end Defs

/-! ### The ordering permutation is forced -/

section Perm

variable {N : ℕ}

theorem ssp1c_coord_injective {x₀ : EucConfig 1 N} (hx : x₀ ∉ eucCollisionSet 1 N) :
    Function.Injective (fun i => x₀ i 0) := by
  intro i j hij
  by_contra hne
  apply hx
  refine ⟨i, j, hne, ?_⟩
  ext k
  fin_cases k
  simpa using hij

theorem ssp1c_strict_of_ord {x : EucConfig 1 N} (hx : x ∉ eucCollisionSet 1 N) {π : Equiv.Perm (Fin N)}
    (h : ∀ k k' : Fin N, k ≤ k' → x (π k) 0 ≤ x (π k') 0) {k k' : Fin N} (hk : k < k') :
    x (π k) 0 < x (π k') 0 :=
  lt_of_le_of_ne (h k k' hk.le) fun he =>
    (ne_of_lt hk) (π.injective ((ssp1c_coord_injective hx) he))

theorem ssp1c_perm_unique {x₀ : EucConfig 1 N} (hx : x₀ ∉ eucCollisionSet 1 N)
    {π π' : Equiv.Perm (Fin N)} (h : ∀ k k' : Fin N, k ≤ k' → x₀ (π k) 0 ≤ x₀ (π k') 0)
    (h' : ∀ k k' : Fin N, k ≤ k' → x₀ (π' k) 0 ≤ x₀ (π' k') 0) : π = π' := by
  classical
  set s : Finset ℝ := Finset.univ.image (fun i => x₀ i 0) with hs
  have hcard : s.card = N := by
    rw [hs, Finset.card_image_of_injective _ (ssp1c_coord_injective hx)]
    simp
  have h1 : (fun k => x₀ (π k) 0) = s.orderEmbOfFin hcard :=
    Finset.orderEmbOfFin_unique hcard (fun k => by simp [hs])
      (fun k k' hk => ssp1c_strict_of_ord hx h hk)
  have h2 : (fun k => x₀ (π' k) 0) = s.orderEmbOfFin hcard :=
    Finset.orderEmbOfFin_unique hcard (fun k => by simp [hs])
      (fun k k' hk => ssp1c_strict_of_ord hx h' hk)
  ext k
  have := congrFun (h1.trans h2.symm) k
  exact congrArg Fin.val (ssp1c_coord_injective hx this)

end Perm


/-! ### Monotonicity of the drift on the open Weyl chamber -/

section Mono

variable {N : ℕ}

theorem ssp1c_pair_pos {a c : Fin N → ℝ} {π : Equiv.Perm (Fin N)}
    (ha : ∀ k k' : Fin N, k < k' → a (π k) < a (π k'))
    (hc : ∀ k k' : Fin N, k < k' → c (π k) < c (π k')) {i j : Fin N} (hij : i ≠ j) :
    0 < (a i - a j) * (c i - c j) := by
  have hk : π.symm i ≠ π.symm j := fun h => hij (π.symm.injective h)
  rcases lt_or_gt_of_ne hk with h | h
  · have h1 := ha _ _ h
    have h2 := hc _ _ h
    simp only [Equiv.apply_symm_apply] at h1 h2
    exact mul_pos_of_neg_of_neg (by linarith) (by linarith)
  · have h1 := ha _ _ h
    have h2 := hc _ _ h
    simp only [Equiv.apply_symm_apply] at h1 h2
    exact mul_pos (by linarith) (by linarith)

/-- `-∇U` is monotone: `∑_i (b_i(a) - b_i(c)) (a_i - c_i) ≤ 0` for `b_i(a) = N⁻¹ ∑_{j≠i} 1/(a_i - a_j)`
when `a, c` are in a common open chamber. -/
theorem ssp1c_monotone_sum (a c : Fin N → ℝ) (hp : ∀ i j : Fin N, i ≠ j → 0 < (a i - a j) * (c i - c j)) :
    ∑ i, ((1 / (N : ℝ)) * ∑ j ∈ Finset.univ.erase i, 1 / (a i - a j) -
      (1 / (N : ℝ)) * ∑ j ∈ Finset.univ.erase i, 1 / (c i - c j)) * (a i - c i) ≤ 0 := by
  classical
  set T : Fin N → Fin N → ℝ := fun i j => (1 / (a i - a j) - 1 / (c i - c j)) * (a i - c i) with hT
  set U : Fin N → Fin N → ℝ := fun i j => if i = j then 0 else T i j with hU
  have hS : ∑ i, ((1 / (N : ℝ)) * ∑ j ∈ Finset.univ.erase i, 1 / (a i - a j) -
      (1 / (N : ℝ)) * ∑ j ∈ Finset.univ.erase i, 1 / (c i - c j)) * (a i - c i) =
      (1 / (N : ℝ)) * ∑ i, ∑ j, U i j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 : ∑ j, U i j = ∑ j ∈ Finset.univ.erase i, T i j := by
      rw [← Finset.sum_erase _ (show U i i = 0 by simp [hU])]
      refine Finset.sum_congr rfl fun j hj => ?_
      simp [hU, (Finset.ne_of_mem_erase hj).symm]
    rw [h1]
    simp only [hT, ← Finset.sum_mul, Finset.sum_sub_distrib]
    ring
  have hpair : ∀ i j, U i j + U j i ≤ 0 := by
    intro i j
    by_cases hij : i = j
    · subst hij; simp [hU]
    · have hji : j ≠ i := Ne.symm hij
      have hpos := hp i j hij
      have hu : a i - a j ≠ 0 := by
        intro h; rw [h] at hpos; simp at hpos
      have hv : c i - c j ≠ 0 := by
        intro h; rw [h] at hpos; simp at hpos
      have : U i j + U j i = -((a i - a j - (c i - c j)) ^ 2 / ((a i - a j) * (c i - c j))) := by
        simp only [hU, hT, hij, hji, ↓reduceIte]
        have hu' : a j - a i ≠ 0 := by intro h; apply hu; linarith
        have hv' : c j - c i ≠ 0 := by intro h; apply hv; linarith
        field_simp
        ring
      rw [this]
      exact neg_nonpos.2 (div_nonneg (sq_nonneg _) hpos.le)
  have h2 : 2 * ∑ i, ∑ j, U i j ≤ 0 := by
    have : ∑ i, ∑ j, U i j = ∑ i, ∑ j, U j i := Finset.sum_comm
    calc 2 * ∑ i, ∑ j, U i j = ∑ i, ∑ j, U i j + ∑ i, ∑ j, U j i := by rw [← this]; ring
      _ = ∑ i, ∑ j, (U i j + U j i) := by
          simp only [Finset.sum_add_distrib]
      _ ≤ 0 := Finset.sum_nonpos fun i _ => Finset.sum_nonpos fun j _ => hpair i j
  rw [hS]
  have hN : (0 : ℝ) ≤ 1 / (N : ℝ) := by positivity
  nlinarith

end Mono


/-! ### The energy identity for an integral of an integrable function -/

section Energy

theorem ssp1c_sq_integral {g : ℝ → ℝ} {t : ℝ} (hg : IntervalIntegrable g volume 0 t) :
    (∫ r in (0 : ℝ)..t, g r) ^ 2 = 2 * ∫ r in (0 : ℝ)..t, g r * ∫ s in (0 : ℝ)..r, g s := by
  set Z : ℝ → ℝ := fun x => ∫ s in (0 : ℝ)..x, g s with hZdef
  have hZ : AbsolutelyContinuousOnInterval Z 0 t :=
    hg.absolutelyContinuousOnInterval_intervalIntegral (c := 0) (by simp)
  have h1 := hZ.integral_deriv_mul_eq_sub hZ
  have hae := hg.ae_hasDerivAt_integral
  have h2 : ∫ x in (0 : ℝ)..t, (deriv Z x * Z x + Z x * deriv Z x) =
      ∫ x in (0 : ℝ)..t, 2 * (g x * Z x) := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hae] with x hx hxI
    have hxu : x ∈ uIcc 0 t := uIoc_subset_uIcc hxI
    have hd : deriv Z x = g x := (hx hxu 0 (by simp)).deriv
    rw [hd]; ring
  have hZ0 : Z 0 = 0 := by simp [hZdef]
  rw [h2, hZ0, intervalIntegral.integral_const_mul] at h1
  simp only [mul_zero, sub_zero] at h1
  have : (∫ r in (0 : ℝ)..t, g r) = Z t := rfl
  rw [this, sq]
  exact h1.symm


theorem ssp1c_energy_nonpos {N : ℕ} {t : ℝ} (ht : 0 ≤ t) (g : Fin N → ℝ → ℝ)
    (hg : ∀ i, IntegrableOn (g i) (Icc 0 t))
    (hneg : ∀ᵐ r ∂(volume.restrict (Icc (0 : ℝ) t)),
      ∑ i, g i r * ∫ s in (0 : ℝ)..r, g i s ≤ 0) :
    ∑ i, (∫ r in (0 : ℝ)..t, g i r) ^ 2 ≤ 0 := by
  have hgi : ∀ i, IntervalIntegrable (g i) volume 0 t := fun i =>
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ht).2 ((hg i).mono_set Ioc_subset_Icc_self)
  have hZc : ∀ i, ContinuousOn (fun x => ∫ s in (0 : ℝ)..x, g i s) (uIcc 0 t) := fun i =>
    ((hgi i).absolutelyContinuousOnInterval_intervalIntegral (c := 0) (by simp)).continuousOn
  have hprod : ∀ i, IntervalIntegrable (fun r => g i r * ∫ s in (0 : ℝ)..r, g i s) volume 0 t :=
    fun i => (hgi i).mul_continuousOn (hZc i)
  have h1 : ∑ i, (∫ r in (0 : ℝ)..t, g i r) ^ 2 =
      2 * ∫ r in (0 : ℝ)..t, ∑ i, g i r * ∫ s in (0 : ℝ)..r, g i s := by
    rw [intervalIntegral.integral_finsetSum (fun i _ => hprod i), Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => ssp1c_sq_integral (hgi i)
  rw [h1]
  have h2 : 0 ≤ ∫ r in (0 : ℝ)..t, -∑ i, g i r * ∫ s in (0 : ℝ)..r, g i s := by
    refine intervalIntegral.integral_nonneg_of_ae_restrict ht ?_
    filter_upwards [hneg] with r hr
    simpa using hr
  rw [intervalIntegral.integral_neg] at h2
  linarith

end Energy

/-! ### Uniqueness -/

section Uniq

variable {N : ℕ}

/-- The coordinate of a Bochner integral of `Euc 1`-valued functions. -/
theorem ssp1c_integral_coord {f : ℝ → Euc 1} {S : Set ℝ} (hf : IntegrableOn f S) :
    (∫ r in S, f r) 0 = ∫ r in S, f r 0 := by
  have := (EuclideanSpace.proj (0 : Fin 1) : Euc 1 →L[ℝ] ℝ).integral_comp_comm hf
  simpa using this.symm

theorem ssp1c_integrableOn_coord {f : ℝ → Euc 1} {S : Set ℝ} (hf : IntegrableOn f S) :
    IntegrableOn (fun r => f r 0) S := by
  have := (EuclideanSpace.proj (0 : Fin 1) : Euc 1 →L[ℝ] ℝ).integrable_comp hf
  simpa [IntegrableOn] using this

/-- **Deterministic uniqueness (Cépa-Lépingle flow on the line).**  Two ordered null-occupation solutions of the
integrated equation with the same driving path and the same collision-free starting point coincide on `[0,T]`. -/
theorem ssp1c_unique (invβ T : ℝ) (hT : 0 ≤ T) {x₀ : EucConfig 1 N} (hx₀ : x₀ ∉ eucCollisionSet 1 N)
    {w x y : ℝ → EucConfig 1 N} (hx : ssp1c_Sol invβ T x₀ w x) (hy : ssp1c_Sol invβ T x₀ w y) :
    ∀ t ∈ Icc (0 : ℝ) T, x t = y t := by
  classical
  obtain ⟨πx, hπx⟩ := hx.ord
  obtain ⟨πy, hπy⟩ := hy.ord
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_rfl, hT⟩
  have hπ : πy = πx := by
    refine ssp1c_perm_unique hx₀ ?_ ?_
    · intro k k' hk
      have := hπy 0 h0 0 k k' hk
      rwa [hy.init] at this
    · intro k k' hk
      have := hπx 0 h0 0 k k' hk
      rwa [hx.init] at this
  subst hπ
  intro t ht
  set b : (ℝ → EucConfig 1 N) → ℝ → Fin N → ℝ := fun p r i => particleDriftW (ssp1c_D invβ) (p r) i 0
    with hb
  set g : Fin N → ℝ → ℝ := fun i r => b x r i - b y r i with hg
  have htT : ∀ s ∈ Icc (0 : ℝ) t, s ∈ Icc (0 : ℝ) T := fun s hs => ⟨hs.1, hs.2.trans ht.2⟩
  have hint : ∀ s ∈ Icc (0 : ℝ) T, ∀ i, IntegrableOn (g i) (Icc 0 s) := by
    intro s hs i
    exact (ssp1c_integrableOn_coord ((hx.eqn s hs).1 i)).sub (ssp1c_integrableOn_coord ((hy.eqn s hs).1 i))
  -- the difference of the two integrated equations
  have hdiff : ∀ s ∈ Icc (0 : ℝ) T, ∀ i, x s i 0 - y s i 0 = ∫ r in (0 : ℝ)..s, g i r := by
    intro s hs i
    have e1 := (hx.eqn s hs).2 i
    have e2 := (hy.eqn s hs).2 i
    have e1' := congrArg (fun v : Euc 1 => v 0) e1
    have e2' := congrArg (fun v : Euc 1 => v 0) e2
    simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul] at e1' e2'
    rw [ssp1c_integral_coord ((hx.eqn s hs).1 i)] at e1'
    rw [ssp1c_integral_coord ((hy.eqn s hs).1 i)] at e2'
    rw [hx.init, ← hy.init] at e1'
    rw [intervalIntegral.integral_of_le hs.1, ← integral_Icc_eq_integral_Ioc]
    simp only [hg]
    rw [integral_sub (ssp1c_integrableOn_coord ((hx.eqn s hs).1 i))
      (ssp1c_integrableOn_coord ((hy.eqn s hs).1 i))]
    linarith
  have hneg : ∀ᵐ r ∂(volume.restrict (Icc (0 : ℝ) t)),
      ∑ i, g i r * ∫ s in (0 : ℝ)..r, g i s ≤ 0 := by
    rw [ae_restrict_iff' measurableSet_Icc]
    have hnx : ∀ᵐ r : ℝ, ¬ (r ∈ Icc (0 : ℝ) T ∧ x r ∈ eucCollisionSet 1 N) := by
      have := hx.occ
      rw [measure_eq_zero_iff_ae_notMem] at this
      exact this
    have hny : ∀ᵐ r : ℝ, ¬ (r ∈ Icc (0 : ℝ) T ∧ y r ∈ eucCollisionSet 1 N) := by
      have := hy.occ
      rw [measure_eq_zero_iff_ae_notMem] at this
      exact this
    filter_upwards [hnx, hny] with r hrx hry hr
    have hrT := htT r hr
    have hxr : x r ∉ eucCollisionSet 1 N := fun h => hrx ⟨hrT, h⟩
    have hyr : y r ∉ eucCollisionSet 1 N := fun h => hry ⟨hrT, h⟩
    have hordx := hπx r hrT 0
    have hordy := hπy r hrT 0
    have hsx := fun k k' (hk : k < k') => ssp1c_strict_of_ord hxr hordx hk
    have hsy := fun k k' (hk : k < k') => ssp1c_strict_of_ord hyr hordy hk
    have hp := fun i j (hij : i ≠ j) => ssp1c_pair_pos (a := fun i => x r i 0) (c := fun i => y r i 0) hsx hsy hij
    have hmono := ssp1c_monotone_sum (fun i => x r i 0) (fun i => y r i 0) hp
    have hxi : ∀ i j : Fin N, j ≠ i → x r i ≠ x r j := fun i j hji he => hxr ⟨i, j, hji.symm, he⟩
    have hyi : ∀ i j : Fin N, j ≠ i → y r i ≠ y r j := fun i j hji he => hyr ⟨i, j, hji.symm, he⟩
    have hz : ∀ i, ∫ s in (0 : ℝ)..r, g i s = x r i 0 - y r i 0 := fun i => (hdiff r hrT i).symm
    simp only [hz]
    simp only [hg, hb, ssp1c_drift_apply invβ (x r) _ (hxi _), ssp1c_drift_apply invβ (y r) _ (hyi _)]
    exact hmono
  have hE := ssp1c_energy_nonpos ht.1 g (fun i => hint t ht i) hneg
  have hz0 : ∀ i, (∫ r in (0 : ℝ)..t, g i r) = 0 := by
    intro i
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (∫ r in (0 : ℝ)..t, g j r))).1
      (le_antisymm hE (Finset.sum_nonneg fun j _ => sq_nonneg _)) i (Finset.mem_univ i)
    exact pow_eq_zero_iff (two_ne_zero) |>.1 this
  ext i k
  fin_cases k
  have := hdiff t ht i
  rw [hz0 i] at this
  simpa [sub_eq_zero] using this

end Uniq

end HRS.MP.SelfSimP1
