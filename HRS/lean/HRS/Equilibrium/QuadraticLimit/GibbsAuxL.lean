import HRS.Equilibrium.QuadraticLimit.GibbsAuxJ
import HRS.Equilibrium.QuadraticLimit.GibbsAuxK

/-!
# Lemma 7.5, `q08_gibbs_approx`: coordinates of the bounded family in the basis `e` (prefix `q08gl_`)
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators Matrix

noncomputable section

namespace HRS.Q08

open ResponseAux InnerProductSpace

variable {d : ℕ} (D : Q08Data d)

section Coord

variable {m : ℕ} {u : Fin m → Torus d → ℝ}

/-- `c_{ki} = ⟨u_k, e_i⟩`. -/
def q08gl_cf (u : Fin m → Torus d → ℝ) (k : Fin m) (i : ℕ) : ℝ := ∫ x, u k x * D.e i x ∂D.μ

theorem q08gl_cf_eq (hu : q08gl_UData D.μ u) (k : Fin m) (i : ℕ) :
    inner ℝ (q08s_E D i) (q08gl_ub D hu k) = q08gl_cf D u k i := by
  rw [q08s_inner_E]
  unfold q08gl_cf
  refine integral_congr_ae ?_
  filter_upwards [q08gl_ub_coe D hu k] with x hx
  rw [hx]

/-- The finite sections `Σ_L = c_L C_L c_Lᵀ`. -/
def q08gl_SL (u : Fin m → Torus d → ℝ) (L : ℕ) : Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun k l => ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L,
    q08gl_cf D u k i * q08gl_cf D u l j * D.Cmat i j

theorem q08gl_Cmat_inner (i j : ℕ) : D.Cmat i j = inner ℝ (q08s_E D i) (q08gl_R D (q08s_E D j)) := by
  rw [q08s_Cmat_eq, q08gl_U_eq]

theorem q08gl_SL_tendsto (hu : q08gl_UData D.μ u) (k l : Fin m) :
    Tendsto (fun L => q08gl_SL D u L k l) atTop (𝓝 (q08gl_Sig D hu k l)) := by
  have A := q08s_abs D
  have hcent : ∀ k, inner ℝ (oneL D.hρ.density) (q08gl_ub D hu k) = 0 := fun k =>
    (projL_eq_self_iff (norm_oneL D.hρ.density)).1 (q08gl_ub_P D hu k)
  set xL : Fin m → ℕ → Lp ℝ 2 (withDensityReal D.ρ) := fun k L =>
    ∑ i ∈ Finset.range L, inner ℝ (q08s_E D i) (q08gl_ub D hu k) • q08s_E D i with hxL
  have hlim : ∀ k, Tendsto (xL k) atTop (𝓝 (q08gl_ub D hu k)) := fun k =>
    (q08s_expand A (q08gl_ub D hu k) (hcent k)).tendsto_sum_nat
  have h1 := (hlim k).inner (𝕜 := ℝ) (((q08gl_R D).continuous.tendsto _).comp (hlim l))
  refine h1.congr (fun L => ?_)
  simp only [Function.comp, hxL, map_sum, map_smul, sum_inner, inner_sum, real_inner_smul_left,
    real_inner_smul_right, q08gl_SL, Matrix.of_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [q08gl_cf_eq D hu, q08gl_cf_eq D hu, q08gl_Cmat_inner]
  ring

theorem q08gl_SL_symm (k l : Fin m) (L : ℕ) : q08gl_SL D u L k l = q08gl_SL D u L l k := by
  unfold q08gl_SL
  simp only [Matrix.of_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [(q08_Cmat_spec D).1 j i]
  ring

/-- Quadratic form of `Σ_L`. -/
theorem q08gl_SL_form (v : Fin m → ℝ) (L : ℕ) :
    v ⬝ᵥ (q08gl_SL D u L) *ᵥ v = ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L,
      (∑ k, v k * q08gl_cf D u k i) * (∑ l, v l * q08gl_cf D u l j) * D.Cmat i j := by
  have h0 : v ⬝ᵥ (q08gl_SL D u L) *ᵥ v = ∑ k, ∑ l, v k * v l * q08gl_SL D u L k l := by
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  have comm4 : ∀ (f : Fin m → Fin m → ℕ → ℕ → ℝ),
      ∑ k, ∑ l, ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L, f k l i j =
        ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L, ∑ k, ∑ l, f k l i j := by
    intro f
    calc ∑ k, ∑ l, ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L, f k l i j
        = ∑ k, ∑ i ∈ Finset.range L, ∑ l, ∑ j ∈ Finset.range L, f k l i j :=
          Finset.sum_congr rfl fun k _ => Finset.sum_comm
      _ = ∑ i ∈ Finset.range L, ∑ k, ∑ l, ∑ j ∈ Finset.range L, f k l i j := Finset.sum_comm
      _ = ∑ i ∈ Finset.range L, ∑ k, ∑ j ∈ Finset.range L, ∑ l, f k l i j :=
          Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => Finset.sum_comm
      _ = ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L, ∑ k, ∑ l, f k l i j :=
          Finset.sum_congr rfl fun i _ => Finset.sum_comm
  rw [h0]
  have h1 : ∀ k l : Fin m, v k * v l * q08gl_SL D u L k l = ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L,
      v k * v l * (q08gl_cf D u k i * q08gl_cf D u l j * D.Cmat i j) := by
    intro k l
    unfold q08gl_SL
    rw [Matrix.of_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
  rw [Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => h1 k l, comm4]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

theorem q08gl_memLp_comb (hu : q08gl_UData D.μ u) (v : Fin m → ℝ) :
    MemLp (fun x => ∑ k, v k * u k x) 2 D.μ := by
  refine memLp_finsetSum (ε' := ℝ) Finset.univ fun k _ => ?_
  exact (q08gl_memLp_u D hu k).const_mul (v k)

/-- Bessel for the coordinates of the combination `∑ v_k u_k` in the basis `e`. -/
theorem q08gl_bessel_fin (hu : q08gl_UData D.μ u) (v : Fin m → ℝ) (L : ℕ) :
    ∑ i ∈ Finset.range L, (∑ k, v k * q08gl_cf D u k i) ^ 2 ≤ ∑ k, v k ^ 2 := by
  have hG := q08gl_memLp_comb D hu v
  obtain ⟨hs, hle⟩ := q08s_bessel D.μ D.e D.he.memLp (q08s_e_ortho D) _ hG
  have hco : ∀ i, ∫ x, (∑ k, v k * u k x) * D.e i x ∂D.μ = ∑ k, v k * q08gl_cf D u k i := by
    intro i
    have hint : ∀ k, Integrable (fun x => v k * (u k x * D.e i x)) D.μ := fun k =>
      ((q08gl_memLp_u D hu k).integrable_mul (D.he.memLp i)).const_mul (v k)
    simp_rw [Finset.sum_mul]
    rw [integral_finsetSum _ fun k _ => by
      simpa [mul_assoc] using hint k]
    refine Finset.sum_congr rfl fun k _ => ?_
    unfold q08gl_cf
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun x => by ring)
  have hsq : ∫ x, (∑ k, v k * u k x) ^ 2 ∂D.μ = ∑ k, v k ^ 2 := by
    have := q08gl_orth_comb hu v v
    simp_rw [sq]
    simpa [sq] using this
  simp_rw [hco] at hs hle
  rw [hsq] at hle
  exact (hs.sum_le_tsum _ fun _ _ => sq_nonneg _).trans hle

theorem q08gl_SL_psd (v : Fin m → ℝ) (L : ℕ) :
    0 ≤ v ⬝ᵥ (q08gl_SL D u L) *ᵥ v := by
  rw [q08gl_SL_form]
  exact (q08_Cmat_spec D).2.1 L (fun i => ∑ k, v k * q08gl_cf D u k i)

theorem q08gl_SL_le (hu : q08gl_UData D.μ u) (v : Fin m → ℝ) (L : ℕ) :
    v ⬝ᵥ (q08gl_SL D u L) *ᵥ v ≤ ∑ k, v k ^ 2 := by
  rw [q08gl_SL_form]
  exact ((q08_Cmat_spec D).2.2.1 L (fun i => ∑ k, v k * q08gl_cf D u k i)).trans
    (q08gl_bessel_fin D hu v L)

end Coord

end HRS.Q08

end
