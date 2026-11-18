import HRS.MS.SpecAux46

/-!
# S8P: Rayleigh bound on the span of the profiles `w_i = √ρ e_i` (S8.7, packet b6)

Namespace `HRS.MS.Spec`, helper prefix `s8p_`.  `s8p_rayleigh`: with `S = ∑_{i ≤ l} a_i w_i`,
`oscNorm 1 S ^ 2 ≤ Cr (ω_l + 1) ∫ S²`.  Inputs: `s8p_osc1_dir` (`‖S‖²_{Σ^1} ≲ ∑_j ∫ (D_j S)² + ∫ S²`), `D_j w_i = Z^{φ_i}_j`,
`∑_j ∫ Z^k_j Z^i_j = ω_i δ_{ik}` and `∑ a_i² ≤ β ∫ S²` (biorthogonality of `w_i` and `φ_k` against `A`-coercivity).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal RealInnerProductSpace ContDiff

namespace HRS.MS.Spec

open HRS HRS.Whole HRS.MS.MovDec HRS.MS.MovLin HRS.MS.MovOsc

variable {d : ℕ} {s β q : ℝ} {ρ : Euc d → ℝ} {M : ℝ} {h : S8pRho d s ρ M}

local notation "𝓢R" => SchwartzMap (Euc d) ℝ

theorem s8p_sum_sq_integral {ι : Type*} (t : Finset ι) (a : ι → ℝ) (Z : ι → Fin d → Euc d → ℝ)
    (hZ : ∀ i k j, Integrable (fun x => Z i j x * Z k j x)) :
    ∑ j : Fin d, ∫ x, (∑ i ∈ t, a i * Z i j x) ^ 2 =
      ∑ i ∈ t, ∑ k ∈ t, a i * a k * ∑ j : Fin d, ∫ x, Z i j x * Z k j x := by
  have e1 : ∀ j x, (∑ i ∈ t, a i * Z i j x) ^ 2 =
      ∑ i ∈ t, ∑ k ∈ t, (a i * a k) * (Z i j x * Z k j x) := fun j x => by
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
  have e2 : ∀ j, ∫ x, (∑ i ∈ t, a i * Z i j x) ^ 2 =
      ∑ i ∈ t, ∑ k ∈ t, (a i * a k) * ∫ x, Z i j x * Z k j x := fun j => by
    simp_rw [e1]
    rw [integral_finset_sum _ fun i _ => integrable_finsetSum _ fun k _ => (hZ i k j).const_mul _]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finset_sum _ fun k _ => (hZ i k j).const_mul _]
    exact Finset.sum_congr rfl fun k _ => integral_const_mul _ _
  simp_rw [e2]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum]

theorem s8p_sqrtM_memLp (hρ : Mov2eRho d ρ) : MemLp (fun x => Real.sqrt (ρ x)) 2 (volume : Measure (Euc d)) := by
  refine (memLp_two_iff_integrable_sq (hρ.data.sqrt_smooth.continuous.aestronglyMeasurable)).2 ?_
  exact ((hρ.psi_GD.mul hρ.psi_GD).integrable).congr (Filter.Eventually.of_forall fun x => by simp [sq])

theorem s8p_inner_sum_orth {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (B : E →L[ℝ] E)
    (v : ℕ → E) (l : ℕ) (a : Fin (l + 1) → ℝ) (horth : ∀ n m, ⟪v n, B (v m)⟫ = if n = m then 1 else 0) :
    ⟪∑ i : Fin (l + 1), a i • v ↑i, B (∑ k : Fin (l + 1), a k • v ↑k)⟫ = ∑ i : Fin (l + 1), a i ^ 2 := by
  rw [map_sum, sum_inner]
  calc ∑ i : Fin (l + 1), ⟪a i • v ↑i, ∑ k : Fin (l + 1), B (a k • v ↑k)⟫
      = ∑ i : Fin (l + 1), ∑ k : Fin (l + 1), a i * a k * ⟪v ↑i, B (v ↑k)⟫ := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [inner_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [map_smul, real_inner_smul_left, real_inner_smul_right]
        ring
    _ = ∑ i : Fin (l + 1), a i ^ 2 := by
        simp_rw [horth, Fin.val_inj]
        simp [sq]

set_option maxHeartbeats 3200000 in
theorem s8p_rayleigh (H : Mov2dTh d s β q ρ) (ψ0 : 𝓢R)
    (hψ0 : (⇑ψ0 : Euc d → ℝ) = fun x => Real.sqrt (ρ x)) (D : S8pEigData d s β ρ h) :
    ∃ wS : ℕ → 𝓢R, (∀ n m, ∫ x, wS n x * D.φ m x = if n = m then 1 else 0) ∧
      ∃ Cr : ℝ, 0 < Cr ∧ ∀ (l : ℕ) (a : Fin (l + 1) → ℝ),
        oscNorm 1 (∑ i, a i • wS i : 𝓢R) ^ 2 ≤
          Cr * (D.om l + 1) * ∫ x, (∑ i, a i • wS i : 𝓢R) x ^ 2 := by
  have hd1 : 1 ≤ d := by have := H.hd; omega
  obtain ⟨hρ, hE, -⟩ := mov2e_thermal H.hd H.hs0 H.hsd H.hβ H.hq H.hρ
  choose wS hwS using fun n => s8p_w_schwartz H ψ0 hψ0 (D.φ n) (s8p_Cc d s ρ (D.φ n))
  have hwE : ∀ n, (⇑(wS n) : Euc d → ℝ) = fun x => Real.sqrt (ρ x) * s8p_E d s β ρ (D.φ n) x := by
    intro n; rw [hwS n]; funext x; exact s8p_w_eq hρ (D.φ n) _ rfl x β
  have hmean : ∀ n, ∫ x, Real.sqrt (ρ x) * D.φ n x = 0 := fun n =>
    s8p_mean_zero H ψ0 hψ0 (D.v n) (D.φ n) (D.hv n)
  have hsq := s8p_sqrtM_memLp hρ
  have hpair : ∀ n m, ∫ x, wS n x * D.φ m x = if n = m then 1 else 0 := by
    intro n m
    have I1 : Integrable (fun x => mov2eW d s β ρ (D.φ n) x * D.φ m x) :=
      (mov2e_W_memLp hd1 H.hs0 H.hsd hρ hE β (D.φ n)).integrable_mul ((D.φ m).memLp 2)
    have I2 : Integrable (fun x => Real.sqrt (ρ x) * D.φ m x) := hsq.integrable_mul ((D.φ m).memLp 2)
    have e : (fun x => wS n x * D.φ m x) = fun x => mov2eW d s β ρ (D.φ n) x * D.φ m x -
        s8p_Cc d s ρ (D.φ n) * (Real.sqrt (ρ x) * D.φ m x) := by
      funext x; rw [congrFun (hwS n) x]; ring
    rw [e, integral_sub I1 (I2.const_mul _), integral_const_mul, hmean m, mul_zero, sub_zero]
    exact D.pair H n m
  obtain ⟨K, hK0, hK⟩ := s8p_osc1_dir H hE
  refine ⟨wS, hpair, K * (β + 1) + 1, by have := H.hβ; positivity, fun l a => ?_⟩
  set S : 𝓢R := ∑ i : Fin (l + 1), a i • wS i with hSdef
  set T : 𝓢R := ∑ i : Fin (l + 1), a i • D.φ i with hTdef
  have hSx : ∀ x, S x = ∑ i : Fin (l + 1), a i * wS i x := fun x => by
    simp [hSdef, SchwartzMap.sum_apply]
  have hTx : ∀ x, T x = ∑ i : Fin (l + 1), a i * D.φ i x := fun x => by
    simp [hTdef, SchwartzMap.sum_apply]
  have hpdS : ∀ (j : Fin d) x, s8p_pd (⇑S) j x = ∑ i : Fin (l + 1), a i * s8p_pd (⇑(wS i)) j x := by
    intro j x
    show mova1_D j S x = _
    rw [hSdef, map_sum]
    simp [SchwartzMap.sum_apply, map_smul]
  have hDj : ∀ (j : Fin d) x, s8p_Dj ρ (⇑S) j x =
      ∑ i : Fin (l + 1), a i * mov2eZ d s β ρ (D.φ i) j x := by
    intro j x
    calc s8p_Dj ρ (⇑S) j x = ∑ i : Fin (l + 1), a i * s8p_Dj ρ (⇑(wS i)) j x := by
          unfold s8p_Dj
          rw [hpdS, hSx, Finset.mul_sum, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun i _ => ?_
          ring
      _ = _ := Finset.sum_congr rfl fun i _ => by
          rw [s8p_Dj_w hd1 H.hs0 H.hsd hρ hE β (D.φ i) (wS i) (hwE i) j x]
  have hZint : ∀ (i k : Fin (l + 1)) (j : Fin d), Integrable (fun x =>
      mov2eZ d s β ρ (D.φ i) j x * mov2eZ d s β ρ (D.φ k) j x) := fun i k j =>
    ((mov2e_Z_GD hd1 H.hs0 H.hsd hρ hE β (D.φ i) j).mul
      (mov2e_Z_GD hd1 H.hs0 H.hsd hρ hE β (D.φ k) j)).integrable
  have hDsum : ∑ j : Fin d, ∫ x, s8p_Dj ρ (⇑S) j x ^ 2 = ∑ i : Fin (l + 1), a i ^ 2 * D.om i := by
    simp_rw [hDj]
    rw [s8p_sum_sq_integral Finset.univ a (fun i j x => mov2eZ d s β ρ (D.φ i) j x) hZint]
    have hin : ∀ i k : Fin (l + 1), ∑ j : Fin d, ∫ x, mov2eZ d s β ρ (D.φ i) j x *
        mov2eZ d s β ρ (D.φ k) j x = D.om i * (if (k : ℕ) = (i : ℕ) then 1 else 0) := by
      intro i k
      rw [← integral_finset_sum _ fun j _ => hZint i k j]
      rw [← D.zz_orth H i k]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    simp_rw [hin, Fin.val_inj]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [mul_comm, sq]
  -- the bound `∑ a_i² ≤ β ∫ S²`
  have hX : ∑ i : Fin (l + 1), a i ^ 2 ≤ β * ∫ x, S x ^ 2 := by
    have hvL : ∀ i, ((D.v i : MovL2Zero ρ) : Lp ℝ 2 (volume : Measure (Euc d))) =
        (D.φ i).toLp 2 volume := fun i =>
      Lp.ext (by
        filter_upwards [D.hv i, SchwartzMap.coeFn_toLp (D.φ i) 2 volume] with x h1 h2
        exact h1.trans h2.symm)
    set tv : MovL2Zero ρ := ∑ i : Fin (l + 1), a i • D.v ↑i with htv
    have hTL : T.toLp 2 volume = ∑ i : Fin (l + 1), a i • (D.φ i).toLp 2 volume := by
      have := map_sum (SchwartzMap.toLpCLM ℝ ℝ 2 (volume : Measure (Euc d))) (fun i : Fin (l + 1) => a i • D.φ i)
        Finset.univ
      simp only [map_smul, SchwartzMap.toLpCLM_apply] at this
      rw [hTdef]
      exact this
    have htvL : (tv : Lp ℝ 2 (volume : Measure (Euc d))) = T.toLp 2 volume := by
      rw [htv, Submodule.coe_sum, hTL]
      simp only [Submodule.coe_smul, hvL]
    have hinner : ⟪tv, s8p_Asub h (MovL2Zero ρ) β⁻¹ tv⟫ = ∑ i : Fin (l + 1), a i ^ 2 :=
      s8p_inner_sum_orth (s8p_Asub h (MovL2Zero ρ) β⁻¹) D.v l a D.orth
    have hlow := s8p_Asub_low h (MovL2Zero ρ) hd1 β⁻¹ tv
    have hnorm : ‖tv‖ ^ 2 = ∫ x, T x ^ 2 := by
      have : ‖tv‖ = ‖(tv : Lp ℝ 2 (volume : Measure (Euc d)))‖ := rfl
      rw [this, htvL, mov2e_toLp_norm_sq]
    have hST : ∫ x, S x * T x = ∑ i : Fin (l + 1), a i ^ 2 := by
      have e : ∀ x, S x * T x = ∑ i : Fin (l + 1), ∑ k : Fin (l + 1), (a i * a k) * (wS i x * D.φ k x) :=
        fun x => by rw [hSx, hTx, Finset.sum_mul_sum]; exact Finset.sum_congr rfl fun i _ =>
          Finset.sum_congr rfl fun k _ => by ring
      have hI : ∀ i k : Fin (l + 1), Integrable (fun x => wS i x * D.φ k x) := fun i k =>
        ((wS i).memLp 2).integrable_mul ((D.φ k).memLp 2)
      simp_rw [e]
      rw [integral_finset_sum _ fun i _ => integrable_finsetSum _ fun k _ => (hI i k).const_mul _]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_finset_sum _ fun k _ => (hI i k).const_mul _]
      simp_rw [integral_const_mul, hpair, Fin.val_inj]
      simp [sq]
    have hCS : (∫ x, S x * T x) ^ 2 ≤ (∫ x, S x ^ 2) * ∫ x, T x ^ 2 := by
      have h1 : ⟪S.toLp 2 volume, T.toLp 2 volume⟫ = ∫ x, S x * T x :=
        mov2e_inner_toLp (S.memLp 2) (T.memLp 2)
      have h2 := abs_real_inner_le_norm (S.toLp 2 volume) (T.toLp 2 volume)
      rw [h1] at h2
      have h3 : (∫ x, S x * T x) ^ 2 ≤ (‖S.toLp 2 volume‖ * ‖T.toLp 2 volume‖) ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h2 2
      rwa [mul_pow, mov2e_toLp_norm_sq, mov2e_toLp_norm_sq] at h3
    -- algebra
    set X : ℝ := ∑ i : Fin (l + 1), a i ^ 2 with hXdef
    have hX0 : 0 ≤ X := Finset.sum_nonneg fun i _ => sq_nonneg _
    have hT0 : 0 ≤ ∫ x, T x ^ 2 := integral_nonneg fun x => sq_nonneg _
    have hlow' : β⁻¹ * ∫ x, T x ^ 2 ≤ X := by rw [← hnorm, ← hinner]; exact hlow
    have hTb : ∫ x, T x ^ 2 ≤ β * X := by
      have := mul_le_mul_of_nonneg_left hlow' H.hβ.le
      rwa [← mul_assoc, mul_inv_cancel₀ H.hβ.ne', one_mul] at this
    rw [hST] at hCS
    by_contra hlt
    push Not at hlt
    have hXpos : 0 < X := by
      by_contra hx0
      push Not at hx0
      have : X = 0 := le_antisymm hx0 hX0
      rw [this] at hlt
      have : 0 ≤ β * ∫ x, S x ^ 2 := mul_nonneg H.hβ.le (integral_nonneg fun x => sq_nonneg _)
      linarith
    have h5 : X ^ 2 ≤ (∫ x, S x ^ 2) * (β * X) := hCS.trans (mul_le_mul_of_nonneg_left hTb (integral_nonneg fun x => sq_nonneg _))
    nlinarith [mul_pos hXpos hXpos]
  have hS0 : 0 ≤ ∫ x, S x ^ 2 := integral_nonneg fun x => sq_nonneg _
  have hDle : ∑ i : Fin (l + 1), a i ^ 2 * D.om i ≤ D.om l * (β * ∫ x, S x ^ 2) := by
    calc ∑ i : Fin (l + 1), a i ^ 2 * D.om i ≤ ∑ i : Fin (l + 1), a i ^ 2 * D.om l := by
          refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (D.mono ?_) (sq_nonneg _)
          exact Nat.lt_succ_iff.1 i.2
      _ = D.om l * ∑ i : Fin (l + 1), a i ^ 2 := by rw [← Finset.sum_mul, mul_comm]
      _ ≤ D.om l * (β * ∫ x, S x ^ 2) :=
          mul_le_mul_of_nonneg_left hX ((D.lam_pos.le).trans (D.lam_le l))
  have hom0 : 0 ≤ D.om l := D.lam_pos.le.trans (D.lam_le l)
  have hβ0 := H.hβ
  calc oscNorm 1 S ^ 2 ≤ K * ((∑ j : Fin d, ∫ x, s8p_Dj ρ (⇑S) j x ^ 2) + ∫ x, S x ^ 2) := hK S
    _ ≤ K * (D.om l * (β * ∫ x, S x ^ 2) + ∫ x, S x ^ 2) := by
        refine mul_le_mul_of_nonneg_left ?_ hK0
        rw [hDsum]; linarith
    _ ≤ (K * (β + 1) + 1) * (D.om l + 1) * ∫ x, S x ^ 2 := by
        have h1 : D.om l * (β * ∫ x, S x ^ 2) + ∫ x, S x ^ 2 ≤ (β + 1) * (D.om l + 1) * ∫ x, S x ^ 2 := by
          nlinarith [mul_nonneg hom0 hS0, mul_nonneg hβ0.le hS0, mul_nonneg (mul_nonneg hβ0.le hom0) hS0]
        nlinarith [mul_le_mul_of_nonneg_left h1 hK0, mul_nonneg (add_nonneg hom0 zero_le_one) hS0]

end HRS.MS.Spec
