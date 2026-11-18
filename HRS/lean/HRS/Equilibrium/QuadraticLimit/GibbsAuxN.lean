import HRS.Equilibrium.QuadraticLimit.GibbsAuxM
import HRS.Equilibrium.QuadraticLimit.GibbsAuxE

/-!
# Lemma 7.5, `q08_gibbs_approx`: the Gaussian comparison (prefix `q08gl_`)
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators Matrix

noncomputable section

namespace HRS.Q08

section LipL1

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {p : ℕ}

/-- Lipschitz test functions: `L²` closeness of the statistics gives closeness of the integrals. -/
theorem q08gl_lip_L1 (F : ℝ × (Fin p → ℝ) → ℝ) (M : ℝ) (hM : ∀ z, |F z| ≤ M) (K : ℝ≥0)
    (hF : LipschitzWith K F) (Q1 Q2 : Ω → ℝ) (l1 l2 : Fin p → Ω → ℝ)
    (hQ1 : Measurable Q1) (hQ2 : Measurable Q2) (hl1 : ∀ b, Measurable (l1 b))
    (hl2 : ∀ b, Measurable (l2 b))
    (hQ : MemLp (fun ω => Q1 ω - Q2 ω) 2 P) (hl : ∀ b, MemLp (fun ω => l1 b ω - l2 b ω) 2 P)
    (ε0 : ℝ) (hQb : ∫ ω, (Q1 ω - Q2 ω) ^ 2 ∂P ≤ ε0 ^ 2)
    (hlb : ∀ b, ∫ ω, (l1 b ω - l2 b ω) ^ 2 ∂P ≤ ε0 ^ 2) (hε0 : 0 ≤ ε0) :
    |∫ ω, F (Q1 ω, fun b => l1 b ω) ∂P - ∫ ω, F (Q2 ω, fun b => l2 b ω) ∂P| ≤
      K * (ε0 + p * ε0) := by
  have hFm : Measurable F := hF.continuous.measurable
  have hint : ∀ (Q : Ω → ℝ) (l : Fin p → Ω → ℝ), Measurable Q → (∀ b, Measurable (l b)) →
      Integrable (fun ω => F (Q ω, fun b => l b ω)) P := fun Q l hQ hl =>
    Integrable.of_bound (hFm.comp (hQ.prodMk (measurable_pi_iff.2 hl))).aestronglyMeasurable M
      (Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs] using hM _)
  have i1 := hint Q1 l1 hQ1 hl1
  have i2 := hint Q2 l2 hQ2 hl2
  -- pointwise Lipschitz bound
  have hpt : ∀ ω, |F (Q1 ω, fun b => l1 b ω) - F (Q2 ω, fun b => l2 b ω)| ≤
      K * (|Q1 ω - Q2 ω| + ∑ b, |l1 b ω - l2 b ω|) := by
    intro ω
    have h1 : dist (F (Q1 ω, fun b => l1 b ω)) (F (Q2 ω, fun b => l2 b ω)) ≤
        K * dist (Q1 ω, fun b => l1 b ω) (Q2 ω, fun b => l2 b ω) := hF.dist_le_mul _ _
    have h2 : dist (Q1 ω, fun b => l1 b ω) (Q2 ω, fun b => l2 b ω) ≤
        |Q1 ω - Q2 ω| + ∑ b, |l1 b ω - l2 b ω| := by
      rw [Prod.dist_eq]
      have h0 : 0 ≤ ∑ b, |l1 b ω - l2 b ω| := Finset.sum_nonneg fun _ _ => abs_nonneg _
      refine max_le ?_ ?_
      · rw [Real.dist_eq]; linarith
      · rw [dist_pi_le_iff (by positivity)]
        intro b
        rw [Real.dist_eq]
        have : |l1 b ω - l2 b ω| ≤ ∑ b, |l1 b ω - l2 b ω| :=
          Finset.single_le_sum (f := fun b => |l1 b ω - l2 b ω|) (fun _ _ => abs_nonneg _)
            (Finset.mem_univ b)
        linarith [abs_nonneg (Q1 ω - Q2 ω)]
    rw [← Real.dist_eq]
    exact h1.trans (mul_le_mul_of_nonneg_left h2 K.2)
  have hQa : Integrable (fun ω => |Q1 ω - Q2 ω|) P := hQ.integrable one_le_two |>.abs
  have hla : ∀ b, Integrable (fun ω => |l1 b ω - l2 b ω|) P := fun b =>
    (hl b).integrable one_le_two |>.abs
  have hsum : Integrable (fun ω => ∑ b, |l1 b ω - l2 b ω|) P := integrable_finsetSum _ fun b _ => hla b
  have hdiff : Integrable (fun ω => F (Q1 ω, fun b => l1 b ω) - F (Q2 ω, fun b => l2 b ω)) P := i1.sub i2
  calc |∫ ω, F (Q1 ω, fun b => l1 b ω) ∂P - ∫ ω, F (Q2 ω, fun b => l2 b ω) ∂P|
      = |∫ ω, (F (Q1 ω, fun b => l1 b ω) - F (Q2 ω, fun b => l2 b ω)) ∂P| := by
        rw [integral_sub i1 i2]
    _ ≤ ∫ ω, |F (Q1 ω, fun b => l1 b ω) - F (Q2 ω, fun b => l2 b ω)| ∂P := abs_integral_le_integral_abs
    _ ≤ ∫ ω, K * (|Q1 ω - Q2 ω| + ∑ b, |l1 b ω - l2 b ω|) ∂P :=
        integral_mono hdiff.abs ((hQa.add hsum).const_mul _) hpt
    _ = K * (∫ ω, |Q1 ω - Q2 ω| ∂P + ∑ b, ∫ ω, |l1 b ω - l2 b ω| ∂P) := by
        rw [integral_const_mul, integral_add hQa hsum, integral_finsetSum _ fun b _ => hla b]
    _ ≤ K * (ε0 + p * ε0) := by
        refine mul_le_mul_of_nonneg_left ?_ K.2
        have e1 : ∫ ω, |Q1 ω - Q2 ω| ∂P ≤ ε0 :=
          (q08gl_integral_le_sqrt P hQ).trans (Real.sqrt_le_iff.2 ⟨hε0, hQb⟩)
        have e2 : ∀ b, ∫ ω, |l1 b ω - l2 b ω| ∂P ≤ ε0 := fun b =>
          (q08gl_integral_le_sqrt P (hl b)).trans (Real.sqrt_le_iff.2 ⟨hε0, hlb b⟩)
        have e3 : ∑ b, ∫ ω, |l1 b ω - l2 b ω| ∂P ≤ p * ε0 := by
          refine (Finset.sum_le_sum fun b _ => e2 b).trans ?_
          simp
        linarith

end LipL1

section Couple

variable {d : ℕ} (D : Q08Data d) {m : ℕ} (u : Fin m → Torus d → ℝ)

/-- The coordinate matrix `c_{ki} = ⟨u_k, e_i⟩` (`i < L`). -/
def q08gl_cc (L : ℕ) : Matrix (Fin m) (Fin L) ℝ := Matrix.of fun k i => q08gl_cf D u k i.1

/-- The finite section `C_L` of the response matrix. -/
def q08gl_CL (L : ℕ) : Matrix (Fin L) (Fin L) ℝ := Matrix.of fun i j => D.Cmat i j

theorem q08gl_SL_eq (L : ℕ) : q08gl_SL D u L = q08gl_cc D u L * q08gl_CL D L * (q08gl_cc D u L)ᵀ := by
  ext k l
  simp only [q08gl_SL, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, q08gl_cc, q08gl_CL,
    Finset.sum_mul]
  simp only [Finset.sum_range]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem q08gl_comm4F {L : ℕ} (f : Fin m → Fin m → Fin L → Fin L → ℝ) :
    ∑ k, ∑ l, ∑ i, ∑ j, f k l i j = ∑ i, ∑ j, ∑ k, ∑ l, f k l i j := by
  calc ∑ k, ∑ l, ∑ i, ∑ j, f k l i j = ∑ k, ∑ i, ∑ l, ∑ j, f k l i j :=
        Finset.sum_congr rfl fun k _ => Finset.sum_comm
    _ = ∑ i, ∑ k, ∑ l, ∑ j, f k l i j := Finset.sum_comm
    _ = ∑ i, ∑ k, ∑ j, ∑ l, f k l i j :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => Finset.sum_comm
    _ = ∑ i, ∑ j, ∑ k, ∑ l, f k l i j := Finset.sum_congr rfl fun i _ => Finset.sum_comm

/-- The pulled back Wick statistic in the coordinates of `e`. -/
theorem q08gl_Q_expand (H' : Matrix (Fin m) (Fin m) ℝ) (L : ℕ) (g : EuclideanSpace ℝ (Fin L)) :
    (1 / 2 : ℝ) * ∑ k, ∑ l, H' k l * ((q08gl_cc D u L *ᵥ g.ofLp) k * (q08gl_cc D u L *ᵥ g.ofLp) l -
        q08gl_SL D u L k l) =
      (1 / 2 : ℝ) * ∑ i : Fin L, ∑ j : Fin L,
        (∑ k, ∑ l, q08gl_cf D u k i * H' k l * q08gl_cf D u l j) * (g i * g j - D.Cmat i j) := by
  congr 1
  have hs : ∀ k l, (q08gl_cc D u L *ᵥ g.ofLp) k * (q08gl_cc D u L *ᵥ g.ofLp) l - q08gl_SL D u L k l =
      ∑ i : Fin L, ∑ j : Fin L, q08gl_cf D u k i * q08gl_cf D u l j * (g i * g j - D.Cmat i j) := by
    intro k l
    simp only [Matrix.mulVec, dotProduct, q08gl_cc, Matrix.of_apply, q08gl_SL]
    rw [Finset.sum_mul_sum, Finset.sum_range]
    simp_rw [Finset.sum_range]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  simp_rw [hs, Finset.mul_sum]
  rw [q08gl_comm4F (fun k l i j => H' k l * (q08gl_cf D u k i * q08gl_cf D u l j * (g i * g j - D.Cmat i j)))]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

end Couple

section Couple2

variable {d : ℕ} (D : Q08Data d) {m : ℕ} {u : Fin m → Torus d → ℝ}

/-- The Gaussian law `N(0, C_L)` on `ℝ^L`. -/
abbrev q08gl_PL (L : ℕ) : Measure (EuclideanSpace ℝ (Fin L)) :=
  multivariateGaussian (0 : EuclideanSpace ℝ (Fin L)) (q08gl_CL D L)

theorem q08gl_CL_psd (L : ℕ) : (q08gl_CL D L).PosSemidef ∧
    ∀ w : Fin L → ℝ, q08c_ch_q (q08gl_CL D L) w ≤ ∑ i, w i ^ 2 := by
  obtain ⟨hCs, hCp, hCle, -⟩ := q08_Cmat_spec D
  exact q08c_ch_cov_fin D.Cmat hCs hCp hCle L

/-- `L²` bound of the Wick quadratic statistic under `N(0, C_L)`. -/
theorem q08gl_wick_L2 (L : ℕ) (A : Fin L → Fin L → ℝ) (hA : ∀ i j, A i j = A j i) :
    MemLp (fun g : EuclideanSpace ℝ (Fin L) => (1 / 2 : ℝ) * ∑ i : Fin L, ∑ j : Fin L,
        A i j * (g i * g j - D.Cmat i j)) 2 (q08gl_PL D L) ∧
      ∫ g : EuclideanSpace ℝ (Fin L), ((1 / 2 : ℝ) * ∑ i : Fin L, ∑ j : Fin L,
        A i j * (g i * g j - D.Cmat i j)) ^ 2 ∂(q08gl_PL D L) ≤ (1 / 2) * ∑ i : Fin L, ∑ j : Fin L, A i j ^ 2 := by
  obtain ⟨hCs, hCp, hCle, -⟩ := q08_Cmat_spec D
  have hC : q08_IsCov D.Cmat := ⟨hCs, hCp, hCle⟩
  refine ⟨?_, ?_⟩
  · have hterm : ∀ i j : Fin L, MemLp (fun g : EuclideanSpace ℝ (Fin L) => A i j * (g i * g j - D.Cmat i j)) 2
        (q08gl_PL D L) := fun i j =>
      ((q08gl_gauss_prod_memLp (q08gl_CL D L) i j).sub (memLp_const (D.Cmat i j))).const_mul (A i j)
    have hrow : ∀ i : Fin L, MemLp (fun g : EuclideanSpace ℝ (Fin L) => ∑ j : Fin L,
        A i j * (g i * g j - D.Cmat i j)) 2 (q08gl_PL D L) := fun i =>
      memLp_finsetSum (ε' := ℝ) _ fun j _ => hterm i j
    have hsum : MemLp (fun g : EuclideanSpace ℝ (Fin L) => ∑ i : Fin L, ∑ j : Fin L,
        A i j * (g i * g j - D.Cmat i j)) 2 (q08gl_PL D L) :=
      memLp_finsetSum (ε' := ℝ) _ fun i _ => hrow i
    exact hsum.const_mul (1 / 2 : ℝ)
  · set Gf : ℕ → EuclideanSpace ℝ (Fin L) → ℝ := fun i g => if h : i < L then g ⟨i, h⟩ else 0 with hGf
    have hproj : ∀ i : Fin L, Measurable (fun g : EuclideanSpace ℝ (Fin L) => g i) := fun i =>
      measurable_pi_apply i |>.comp (PiLp.continuous_ofLp 2 _ |>.measurable)
    have hGm : ∀ i, Measurable (Gf i) := by
      intro i
      by_cases h : i < L
      · have : Gf i = fun g => g ⟨i, h⟩ := by ext g; simp [hGf, h]
        rw [this]; exact hproj ⟨i, h⟩
      · have : Gf i = fun _ => 0 := by ext g; simp [hGf, h]
        rw [this]; exact measurable_const
    have hGfi : ∀ (i : Fin L) (g : EuclideanSpace ℝ (Fin L)), Gf i.1 g = g i := by
      intro i g; simp [hGf, i.2]
    have hlawG : law (q08gl_PL D L) (fun ω => (WithLp.toLp 2 fun i : Fin L => Gf i ω :
        EuclideanSpace ℝ (Fin L))) = multivariateGaussian 0 (Matrix.of fun i j : Fin L => D.Cmat i j) := by
      have : (fun ω => (WithLp.toLp 2 fun i : Fin L => Gf i ω : EuclideanSpace ℝ (Fin L))) = id := by
        ext ω i
        simp [hGfi]
      rw [this]
      unfold law
      exact Measure.map_id
    have hbound := q08c_chaos_l2_bound_meas (q08gl_PL D L) Gf hGm D.Cmat hC L hlawG A hA
    refine le_trans (le_of_eq ?_) hbound
    refine integral_congr_ae (Eventually.of_forall fun g => ?_)
    simp only [hGfi]

/-- `L²` bound of linear statistics under `N(0, C_L)` (`C_L ≤ I`). -/
theorem q08gl_lin2 (L : ℕ) (w : Fin L → ℝ) :
    MemLp (q08c_ch_lin w) 2 (q08gl_PL D L) ∧
      ∫ g, (q08c_ch_lin w g) ^ 2 ∂(q08gl_PL D L) ≤ ∑ i, w i ^ 2 := by
  obtain ⟨hPSD, hq⟩ := q08gl_CL_psd D L
  refine ⟨?_, ?_⟩
  · have hi := q08c_ch_lin_int hPSD w 2
    exact (memLp_two_iff_integrable_sq (q08c_ch_lin_meas w).aestronglyMeasurable).2 hi
  · rw [q08c_ch_second hPSD w]
    exact hq w

end Couple2

section Couple3

variable {d : ℕ} (D : Q08Data d) {m : ℕ} (u : Fin m → Torus d → ℝ)

/-- The finite-rank quadratic statistic pulled back by the coupling `s = c_L g`. -/
def q08gl_Q1 (H' : Matrix (Fin m) (Fin m) ℝ) (L : ℕ) (g : EuclideanSpace ℝ (Fin L)) : ℝ :=
  (1 / 2) * ∑ k, ∑ l, H' k l * ((q08gl_cc D u L *ᵥ g.ofLp) k * (q08gl_cc D u L *ᵥ g.ofLp) l -
    q08gl_SL D u L k l)

/-- The Wick statistic of the limit chaos. -/
def q08gl_Q2 (L : ℕ) (g : EuclideanSpace ℝ (Fin L)) : ℝ :=
  (1 / 2) * ∑ i : Fin L, ∑ j : Fin L, D.Hmat i j * (g i * g j - D.Cmat i j)

/-- The pulled back linear statistic. -/
def q08gl_l1 (α : Fin D.p → Fin m → ℝ) (L : ℕ) (b : Fin D.p) (g : EuclideanSpace ℝ (Fin L)) : ℝ :=
  ∑ k, α b k * (q08gl_cc D u L *ᵥ g.ofLp) k

/-- The linear statistic of the limit chaos. -/
def q08gl_l2 (L : ℕ) (b : Fin D.p) (g : EuclideanSpace ℝ (Fin L)) : ℝ :=
  ∑ i : Fin L, D.coef b i * g i

theorem q08gl_proj_meas {L : ℕ} (i : Fin L) : Measurable (fun g : EuclideanSpace ℝ (Fin L) => g i) :=
  measurable_pi_apply i |>.comp (PiLp.continuous_ofLp 2 _ |>.measurable)

theorem q08gl_coord_meas (L : ℕ) (k : Fin m) :
    Measurable (fun g : EuclideanSpace ℝ (Fin L) => (q08gl_cc D u L *ᵥ g.ofLp) k) := by
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.measurable_sum _ fun i _ => measurable_const.mul (q08gl_proj_meas i)

theorem q08gl_Q1_meas (H' : Matrix (Fin m) (Fin m) ℝ) (L : ℕ) : Measurable (q08gl_Q1 D u H' L) := by
  unfold q08gl_Q1
  refine Measurable.const_mul (Finset.measurable_sum _ fun k _ => Finset.measurable_sum _ fun l _ => ?_) _
  exact measurable_const.mul (((q08gl_coord_meas D u L k).mul (q08gl_coord_meas D u L l)).sub measurable_const)

theorem q08gl_Q2_meas (L : ℕ) : Measurable (q08gl_Q2 D L) := by
  unfold q08gl_Q2
  refine Measurable.const_mul (Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_) _
  exact measurable_const.mul (((q08gl_proj_meas i).mul (q08gl_proj_meas j)).sub measurable_const)

theorem q08gl_l1_meas (α : Fin D.p → Fin m → ℝ) (L : ℕ) (b : Fin D.p) : Measurable (q08gl_l1 D u α L b) := by
  unfold q08gl_l1
  exact Finset.measurable_sum _ fun k _ => measurable_const.mul (q08gl_coord_meas D u L k)

theorem q08gl_l2_meas (L : ℕ) (b : Fin D.p) : Measurable (q08gl_l2 D L b) := by
  unfold q08gl_l2
  exact Finset.measurable_sum _ fun i _ => measurable_const.mul (q08gl_proj_meas i)

variable {u}

theorem q08gl_Q_diff (hu : q08gl_UData D.μ u) (H' : Matrix (Fin m) (Fin m) ℝ) (hH' : ∀ i j, H' i j = H' j i)
    (ε0 : ℝ) (hε0 : 0 ≤ ε0)
    (hH : ∫ z : Torus d × Torus d, (q08e_kt D.μ D.h z.1 z.2 - q08gl_kap u H' z.1 z.2) ^ 2
      ∂(D.μ.prod D.μ) ≤ ε0 ^ 2) (L : ℕ) :
    MemLp (fun g => q08gl_Q1 D u H' L g - q08gl_Q2 D L g) 2 (q08gl_PL D L) ∧
      ∫ g, (q08gl_Q1 D u H' L g - q08gl_Q2 D L g) ^ 2 ∂(q08gl_PL D L) ≤ ε0 ^ 2 := by
  set A : Fin L → Fin L → ℝ := fun i j =>
    ∑ k, ∑ l, q08gl_cf D u k i * H' k l * q08gl_cf D u l j - D.Hmat i j with hA
  have hAsymm : ∀ i j, A i j = A j i := by
    intro i j
    simp only [hA]
    rw [(q08_Hmat_spec D).1 i j]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
    rw [hH' l k]; ring
  have hdiff : ∀ g : EuclideanSpace ℝ (Fin L), q08gl_Q1 D u H' L g - q08gl_Q2 D L g =
      (1 / 2 : ℝ) * ∑ i : Fin L, ∑ j : Fin L, A i j * (g i * g j - D.Cmat i j) := by
    intro g
    unfold q08gl_Q1 q08gl_Q2
    rw [q08gl_Q_expand D u H' L g, ← mul_sub, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hA]
    ring
  obtain ⟨hmem, hint⟩ := q08gl_wick_L2 D L A hAsymm
  have hAsum : ∑ i : Fin L, ∑ j : Fin L, A i j ^ 2 ≤ ε0 ^ 2 := by
    have := q08gl_Hbound D hu H' ε0 hH L
    simp only [Finset.sum_range] at this
    exact this
  have hfun : (fun g => q08gl_Q1 D u H' L g - q08gl_Q2 D L g) = fun g : EuclideanSpace ℝ (Fin L) =>
      (1 / 2 : ℝ) * ∑ i : Fin L, ∑ j : Fin L, A i j * (g i * g j - D.Cmat i j) := funext hdiff
  refine ⟨by rw [hfun]; exact hmem, ?_⟩
  simp only [hdiff]
  refine hint.trans ?_
  nlinarith [hAsum, sq_nonneg ε0]

theorem q08gl_lin_diff (hu : q08gl_UData D.μ u) (α : Fin D.p → Fin m → ℝ) (ε0 : ℝ)
    (hα : ∀ b, ∫ x, (D.φ b x - pair D.μ (D.φ b) - ∑ k, α b k * u k x) ^ 2 ∂D.μ ≤ ε0 ^ 2)
    (L : ℕ) (b : Fin D.p) :
    MemLp (fun g => q08gl_l1 D u α L b g - q08gl_l2 D L b g) 2 (q08gl_PL D L) ∧
      ∫ g, (q08gl_l1 D u α L b g - q08gl_l2 D L b g) ^ 2 ∂(q08gl_PL D L) ≤ ε0 ^ 2 := by
  have hlinid : ∀ g : EuclideanSpace ℝ (Fin L), q08gl_l1 D u α L b g - q08gl_l2 D L b g =
      q08c_ch_lin (fun i : Fin L => ∑ k, α b k * q08gl_cf D u k i - D.coef b i) g := by
    intro g
    simp only [q08gl_l1, q08gl_l2, q08c_ch_lin, Matrix.mulVec, dotProduct, q08gl_cc, Matrix.of_apply,
      Finset.mul_sum, sub_mul, Finset.sum_sub_distrib, Finset.sum_mul]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    ring
  have hfun : (fun g => q08gl_l1 D u α L b g - q08gl_l2 D L b g) =
      q08c_ch_lin (fun i : Fin L => ∑ k, α b k * q08gl_cf D u k i - D.coef b i) := funext hlinid
  obtain ⟨hmem, hint⟩ := q08gl_lin2 D L (fun i : Fin L => ∑ k, α b k * q08gl_cf D u k i - D.coef b i)
  refine ⟨by rw [hfun]; exact hmem, ?_⟩
  simp only [hlinid]
  refine hint.trans ?_
  have := q08gl_phibound D hu b (α b) ε0 (hα b) L
  simp only [Finset.sum_range] at this
  refine le_trans (le_of_eq ?_) this
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

end Couple3

section Couple4

variable {d : ℕ} (D : Q08Data d) {m : ℕ} {u : Fin m → Torus d → ℝ}

/-- Comparison of the Gaussian functional of the finite-rank statistics (law `N(0, Σ_L)`) with the
finite-dimensional Wick chaos functional (law `N(0, C_L)`), through the coupling `s = c_L g`. -/
theorem q08gl_couple (hu : q08gl_UData D.μ u) (H' : Matrix (Fin m) (Fin m) ℝ)
    (hH' : ∀ i j, H' i j = H' j i) (α : Fin D.p → Fin m → ℝ) (ε0 : ℝ) (hε0 : 0 ≤ ε0)
    (hH : ∫ z : Torus d × Torus d, (q08e_kt D.μ D.h z.1 z.2 - q08gl_kap u H' z.1 z.2) ^ 2
      ∂(D.μ.prod D.μ) ≤ ε0 ^ 2)
    (hα : ∀ b, ∫ x, (D.φ b x - pair D.μ (D.φ b) - ∑ k, α b k * u k x) ^ 2 ∂D.μ ≤ ε0 ^ 2)
    (F : ℝ × (Fin D.p → ℝ) → ℝ) (M : ℝ) (hM : ∀ z, |F z| ≤ M) (K : ℝ≥0) (hF : LipschitzWith K F)
    (L : ℕ) :
    |∫ s : EuclideanSpace ℝ (Fin m), F ((1 / 2) * ∑ k, ∑ l, H' k l * (s k * s l - q08gl_SL D u L k l),
          fun b => ∑ k, α b k * s k)
        ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) (q08gl_SL D u L)) -
      ∫ g : EuclideanSpace ℝ (Fin L), F ((1 / 2) * ∑ i : Fin L, ∑ j : Fin L,
          D.Hmat i j * (g i * g j - D.Cmat i j), fun b => ∑ i : Fin L, D.coef b i * g i)
        ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin L)) (Matrix.of fun i j : Fin L => D.Cmat i j))| ≤
      K * (ε0 + D.p * ε0) := by
  obtain ⟨hPSD, -⟩ := q08gl_CL_psd D L
  have hFm : Measurable F := hF.continuous.measurable
  have hmeasS : Measurable (fun g : EuclideanSpace ℝ (Fin L) =>
      (WithLp.toLp 2 (q08gl_cc D u L *ᵥ (WithLp.ofLp g)) : EuclideanSpace ℝ (Fin m))) := by fun_prop
  have hmap : (q08gl_PL D L).map (fun g : EuclideanSpace ℝ (Fin L) =>
      (WithLp.toLp 2 (q08gl_cc D u L *ᵥ (WithLp.ofLp g)) : EuclideanSpace ℝ (Fin m))) =
      multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) (q08gl_SL D u L) := by
    rw [q08gl_SL_eq]; exact q08gl_push (q08gl_cc D u L) (q08gl_CL D L) hPSD
  have hΦm : Measurable (fun s : EuclideanSpace ℝ (Fin m) => F ((1 / 2) * ∑ k, ∑ l,
      H' k l * (s k * s l - q08gl_SL D u L k l), fun b => ∑ k, α b k * s k)) := by
    refine hFm.comp (Measurable.prodMk ?_ ?_)
    · refine Measurable.const_mul (Finset.measurable_sum _ fun k _ => Finset.measurable_sum _ fun l _ => ?_) _
      refine measurable_const.mul ?_
      exact ((measurable_pi_apply k |>.comp (PiLp.continuous_ofLp 2 _ |>.measurable)).mul
        (measurable_pi_apply l |>.comp (PiLp.continuous_ofLp 2 _ |>.measurable))).sub measurable_const
    · refine measurable_pi_iff.2 fun b => Finset.measurable_sum _ fun k _ => ?_
      exact measurable_const.mul (measurable_pi_apply k |>.comp (PiLp.continuous_ofLp 2 _ |>.measurable))
  rw [← hmap, integral_map hmeasS.aemeasurable hΦm.aestronglyMeasurable]
  have key := q08gl_lip_L1 (q08gl_PL D L) F M hM K hF (q08gl_Q1 D u H' L) (q08gl_Q2 D L)
    (q08gl_l1 D u α L) (q08gl_l2 D L) (q08gl_Q1_meas D u H' L) (q08gl_Q2_meas D L)
    (q08gl_l1_meas D u α L) (q08gl_l2_meas D L)
    (q08gl_Q_diff D hu H' hH' ε0 hε0 hH L).1 (fun b => (q08gl_lin_diff D hu α ε0 hα L b).1) ε0
    (q08gl_Q_diff D hu H' hH' ε0 hε0 hH L).2 (fun b => (q08gl_lin_diff D hu α ε0 hα L b).2) hε0
  exact key

end Couple4

end HRS.Q08

end
