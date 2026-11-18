import HRS.Equilibrium.Parametrix.PX1AuxExt
import HRS.Equilibrium.Parametrix.PX1AuxMul
import HRS.Equilibrium.Parametrix.PX1AuxPartial

/-!
# Prop 4.13 parametrix, packet PX1: extension of conormal kernels of negative order

`conormal_extend` (source line 4848): if `σ + J + 1 < 0` and `F` is conormal with `J + 1` derivatives,
then all derivatives of `lift2 F` of order `≤ J + 1` are bounded on the off-diagonal set
(`full_bound_offDiag`: typed bounds on `∂_X^a ∂_z^c` give full bounds by peeling one derivative at
a time, `full_of_tb`; the weight `r^{-(σ+c)} (1 + |log r|)^b` is bounded, `rpow_log_pow_le`;
periodicity reduces to the chart region), so that `lift2 F` extends to a `C^J` function
(`ext_theorem`); the extension is `diagExt F` (`lift2_diagExt_eq`).
-/

open MeasureTheory Filter Topology
noncomputable section

namespace HRS.Parx

variable {d : ℕ}

theorem prod_norm_init_pair {c : ℕ} (w : Fin (c + 1) → Euc d × Euc d) :
    ∏ j, ‖w j‖ = (∏ j, ‖Fin.init w j‖) * ‖w (Fin.last c)‖ := by
  rw [Fin.prod_univ_castSucc]
  rfl

theorem prod_norm_snoc_pair {c : ℕ} (v : Fin c → Euc d × Euc d) (h : Euc d × Euc d) :
    ∏ j, ‖(Fin.snoc v h : Fin (c + 1) → Euc d × Euc d) j‖ = (∏ j, ‖v j‖) * ‖h‖ := by
  rw [Fin.prod_univ_castSucc]
  simp

theorem tb_dirD_fst_gen {G : Euc d × Euc d → ℝ} {q : Euc d × Euc d} {a c : ℕ} {W : ℝ} (x : Euc d)
    (hG : ContDiffAt ℝ ((a + c + 1 : ℕ) : WithTop ℕ∞) G q) (hT : TB G q (a + 1) c W) :
    TB (dirD (x, (0 : Euc d)) G) q a c (W * ‖x‖) := by
  intro u v
  rw [iteratedFDeriv_dirD hG, ← iteratedFDeriv_cons_eq_snoc hG]
  have := hT (Fin.cons x u) v
  rw [pat_cons_left, iteratedFDeriv_cast, prod_norm_cons] at this
  calc _ ≤ _ := this
    _ = _ := by ring

theorem full_of_tb {q : Euc d × Euc d} : ∀ (k : ℕ) (G : Euc d × Euc d → ℝ) (M : ℝ), 0 ≤ M →
    ContDiffAt ℝ (k : WithTop ℕ∞) G q → (∀ a c, a + c = k → TB G q a c M) →
    ∀ w : Fin k → Euc d × Euc d, |iteratedFDeriv ℝ k G q w| ≤ 2 ^ k * M * ∏ i, ‖w i‖ := by
  intro k
  induction k with
  | zero =>
    intro G M hM _ hT w
    have := hT 0 0 rfl Fin.elim0 Fin.elim0
    have e : w = pat (Fin.elim0 : Fin 0 → Euc d) (Fin.elim0 : Fin 0 → Euc d) :=
      Subsingleton.elim _ _
    rw [e]
    simpa using this
  | succ k ih =>
    intro G M hM hG hT w
    have hv : w = Fin.snoc (Fin.init w) (w (Fin.last k)) := (Fin.snoc_init_self w).symm
    set h := w (Fin.last k) with hh
    set w' := Fin.init w with hw'
    have hGk : ContDiffAt ℝ (k : WithTop ℕ∞) G q := hG.of_le (by exact_mod_cast Nat.le_succ k)
    have hG1 : ContDiffAt ℝ (k : WithTop ℕ∞) (dirD (h.1, (0 : Euc d)) G) q :=
      (hG.fderiv_right_succ (n := k)).clm_apply contDiffAt_const
    have hG2 : ContDiffAt ℝ (k : WithTop ℕ∞) (dirD ((0 : Euc d), h.2) G) q :=
      (hG.fderiv_right_succ (n := k)).clm_apply contDiffAt_const
    have hsplit : dirD h G = dirD (h.1, (0 : Euc d)) G + dirD ((0 : Euc d), h.2) G := by
      funext p
      simp only [dirD, Pi.add_apply]
      have : h = (h.1, (0 : Euc d)) + ((0 : Euc d), h.2) := by ext <;> simp
      conv_lhs => rw [this, map_add]
    rw [hv, ← iteratedFDeriv_dirD hG, hsplit, iteratedFDeriv_add_apply hG1 hG2]
    simp only [add_apply]
    have T1 : ∀ a c, a + c = k → TB (dirD (h.1, (0 : Euc d)) G) q a c (M * ‖h.1‖) := by
      intro a c hac
      exact tb_dirD_fst_gen h.1 (by subst hac; exact hG) (hT (a + 1) c (by omega))
    have T2 : ∀ a c, a + c = k → TB (dirD ((0 : Euc d), h.2) G) q a c (M * ‖h.2‖) := by
      intro a c hac
      exact tb_dirD_snd h.2 (by subst hac; exact hG) (hT a (c + 1) (by omega))
    have I1 := ih _ (M * ‖h.1‖) (by positivity) hG1 T1 w'
    have I2 := ih _ (M * ‖h.2‖) (by positivity) hG2 T2 w'
    have hP : 0 ≤ ∏ i, ‖w' i‖ := Finset.prod_nonneg fun i _ => norm_nonneg _
    have hprod : ∏ i, ‖(Fin.snoc w' h : Fin (k + 1) → Euc d × Euc d) i‖ = (∏ i, ‖w' i‖) * ‖h‖ :=
      prod_norm_snoc_pair w' h
    have hx : ‖h.1‖ ≤ ‖h‖ := norm_fst_le h
    have hz : ‖h.2‖ ≤ ‖h‖ := norm_snd_le h
    refine (abs_add_le _ _).trans ?_
    rw [hprod]
    calc _ ≤ 2 ^ k * (M * ‖h.1‖) * (∏ i, ‖w' i‖) + 2 ^ k * (M * ‖h.2‖) * ∏ i, ‖w' i‖ :=
          add_le_add I1 I2
      _ = 2 ^ k * M * (∏ i, ‖w' i‖) * (‖h.1‖ + ‖h.2‖) := by ring
      _ ≤ 2 ^ k * M * (∏ i, ‖w' i‖) * (2 * ‖h‖) :=
          mul_le_mul_of_nonneg_left (by linarith)
            (mul_nonneg (mul_nonneg (pow_nonneg (by norm_num) _) hM) hP)
      _ = _ := by ring

theorem rpow_log_pow_le (ε : ℝ) (hε : 0 < ε) (b : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 < r → r ≤ 1 → r ^ ε * (1 + |Real.log r|) ^ b ≤ C := by
  set δ : ℝ := ε / ((b : ℝ) + 1) with hδ
  have hδ0 : 0 < δ := by positivity
  set K : ℝ := max 1 (1 / δ) with hK
  have hK1 : 1 ≤ K := le_max_left _ _
  have hKδ : 1 ≤ K * δ := by
    have : 1 / δ ≤ K := le_max_right _ _
    calc (1 : ℝ) = 1 / δ * δ := by field_simp
      _ ≤ K * δ := mul_le_mul_of_nonneg_right this hδ0.le
  refine ⟨K ^ b, by positivity, fun r hr0 hr1 => ?_⟩
  set t : ℝ := |Real.log r| with ht
  have ht0 : 0 ≤ t := abs_nonneg _
  have hlog : Real.log r = -t := by
    rw [ht, abs_of_nonpos (Real.log_nonpos hr0.le hr1)]; ring
  have h1 : r ^ ε = Real.exp (-(t * ε)) := by
    rw [Real.rpow_def_of_pos hr0, hlog]; ring_nf
  have h2 : 1 + t ≤ K * Real.exp (δ * t) := by
    have := Real.add_one_le_exp (δ * t)
    nlinarith [mul_nonneg ht0 (by linarith : 0 ≤ K * δ - 1), mul_nonneg (by linarith : (0:ℝ) ≤ K) (Real.exp_pos (δ * t)).le]
  have h3 : (1 + t) ^ b ≤ K ^ b * Real.exp (b * (δ * t)) := by
    calc (1 + t) ^ b ≤ (K * Real.exp (δ * t)) ^ b := pow_le_pow_left₀ (by linarith) h2 b
      _ = K ^ b * Real.exp (b * (δ * t)) := by rw [mul_pow, ← Real.exp_nat_mul]
  have h4 : (b : ℝ) * δ ≤ ε := by
    rw [hδ]
    have : (b : ℝ) / ((b : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith
    calc (b : ℝ) * (ε / ((b : ℝ) + 1)) = ε * ((b : ℝ) / ((b : ℝ) + 1)) := by ring
      _ ≤ ε * 1 := mul_le_mul_of_nonneg_left this hε.le
      _ = ε := by ring
  rw [h1]
  calc Real.exp (-(t * ε)) * (1 + t) ^ b ≤ Real.exp (-(t * ε)) * (K ^ b * Real.exp (b * (δ * t))) :=
        mul_le_mul_of_nonneg_left h3 (Real.exp_pos _).le
    _ = K ^ b * Real.exp (-(t * ε) + b * (δ * t)) := by rw [Real.exp_add]; ring
    _ ≤ K ^ b * 1 := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [Real.exp_le_one_iff]
        nlinarith [mul_le_mul_of_nonneg_right h4 ht0]
    _ = K ^ b := by ring

/-- The inverse chart `(x, y) ↦ ((x + y)/2, x - y)`. -/
def chartTinv (d : ℕ) : Euc d × Euc d →L[ℝ] Euc d × Euc d :=
  ((1 / 2 : ℝ) • (ContinuousLinearMap.fst ℝ (Euc d) (Euc d) + ContinuousLinearMap.snd ℝ (Euc d) (Euc d))).prod
    (ContinuousLinearMap.fst ℝ (Euc d) (Euc d) - ContinuousLinearMap.snd ℝ (Euc d) (Euc d))

theorem chartTinv_apply (p : Euc d × Euc d) :
    chartTinv d p = ((1 / 2 : ℝ) • (p.1 + p.2), p.1 - p.2) := by
  simp [chartTinv]

theorem chartTinv_chartT (p : Euc d × Euc d) : chartTinv d (chartT d p) = p := by
  rw [chartT_apply, chartTinv_apply]
  refine Prod.ext ?_ ?_
  · show (1 / 2 : ℝ) • (p.1 + (1 / 2 : ℝ) • p.2 + (p.1 - (1 / 2 : ℝ) • p.2)) = p.1
    module
  · show p.1 + (1 / 2 : ℝ) • p.2 - (p.1 - (1 / 2 : ℝ) • p.2) = p.2
    module

theorem chartT_chartTinv (p : Euc d × Euc d) : chartT d (chartTinv d p) = p := by
  rw [chartTinv_apply, chartT_apply]
  refine Prod.ext ?_ ?_
  · show (1 / 2 : ℝ) • (p.1 + p.2) + (1 / 2 : ℝ) • (p.1 - p.2) = p.1
    module
  · show (1 / 2 : ℝ) • (p.1 + p.2) - (1 / 2 : ℝ) • (p.1 - p.2) = p.2
    module

def chartE (d : ℕ) : (Euc d × Euc d) ≃L[ℝ] (Euc d × Euc d) :=
  ContinuousLinearEquiv.equivOfInverse (chartT d) (chartTinv d) chartTinv_chartT chartT_chartTinv

theorem chartE_apply (p : Euc d × Euc d) : chartE d p = chartT d p := rfl

theorem norm_chartTinv_le : ‖chartTinv d‖ ≤ 2 := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) fun p => ?_
  rw [chartTinv_apply, Prod.norm_def]
  have h1 : ‖p.1‖ ≤ ‖p‖ := norm_fst_le p
  have h2 : ‖p.2‖ ≤ ‖p‖ := norm_snd_le p
  refine max_le ?_ ?_
  · calc ‖(1 / 2 : ℝ) • (p.1 + p.2)‖ = (1 / 2) * ‖p.1 + p.2‖ := by
          rw [norm_smul, Real.norm_of_nonneg (by norm_num)]
      _ ≤ (1 / 2) * (‖p.1‖ + ‖p.2‖) := mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num)
      _ ≤ _ := by linarith [norm_nonneg p]
  · calc ‖p.1 - p.2‖ ≤ ‖p.1‖ + ‖p.2‖ := norm_sub_le _ _
      _ ≤ _ := by linarith

theorem norm_iteratedFDeriv_chart_le (Φ : Euc d × Euc d → ℝ) (k : ℕ) (q : Euc d × Euc d) :
    ‖iteratedFDeriv ℝ k Φ (chartT d q)‖ ≤ 2 ^ k * ‖iteratedFDeriv ℝ k (Φ ∘ chartT d) q‖ := by
  have h := (chartE d).iteratedFDerivWithin_comp_right Φ (s := Set.univ) uniqueDiffOn_univ
    (x := q) (Set.mem_univ _) k
  simp only [iteratedFDerivWithin_univ, Set.preimage_univ] at h
  have h' : iteratedFDeriv ℝ k (Φ ∘ chartT d) q =
      (iteratedFDeriv ℝ k Φ (chartT d q)).compContinuousLinearMap fun _ => (chartE d : _ →L[ℝ] _) :=
    h
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun w => ?_
  have e1 : (iteratedFDeriv ℝ k Φ (chartT d q)) w =
      (iteratedFDeriv ℝ k (Φ ∘ chartT d) q) (fun i => chartTinv d (w i)) := by
    rw [h']
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
    congr 1
    funext i
    show w i = chartT d (chartTinv d (w i))
    rw [chartT_chartTinv]
  rw [e1]
  refine ((iteratedFDeriv ℝ k (Φ ∘ chartT d) q).le_opNorm _).trans ?_
  have : ∏ i : Fin k, ‖chartTinv d (w i)‖ ≤ ∏ i : Fin k, (2 * ‖w i‖) :=
    Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ =>
      (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right norm_chartTinv_le (norm_nonneg _)))
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at this
  calc ‖iteratedFDeriv ℝ k (Φ ∘ chartT d) q‖ * ∏ i, ‖chartTinv d (w i)‖
      ≤ ‖iteratedFDeriv ℝ k (Φ ∘ chartT d) q‖ * (2 ^ k * ∏ i, ‖w i‖) :=
        mul_le_mul_of_nonneg_left this (norm_nonneg _)
    _ = _ := by ring

theorem near_full_bound {σ : ℝ} {b J : ℕ} (hσ : σ + ((J : ℝ) + 1) < 0) :
    ∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ {B : ℝ} {F : Torus d → Torus d → ℝ}, 0 ≤ B → Conormal σ b (J + 1) B F →
      ∀ {X z : Euc d}, z ≠ 0 → ‖z‖ < r0 → ∀ {k : ℕ}, k ≤ J + 1 →
        ‖iteratedFDeriv ℝ k (lift2 F) (chartT d (X, z))‖ ≤ C0 * B := by
  have hε : 0 < -(σ + ((J : ℝ) + 1)) := by linarith
  obtain ⟨C, hC0, hC⟩ := rpow_log_pow_le (-(σ + ((J : ℝ) + 1))) hε b
  refine ⟨4 ^ (J + 1) * (1 + C), by positivity, ?_⟩
  intro B F hB hF X z hz hzr k hk
  have hq : (X, z) ∈ Uc d := mem_Uc hz hzr
  set r := ‖z‖ with hr
  have hr0 : 0 < r := norm_pos_iff.mpr hz
  have hr1 : r ≤ 1 := by unfold r0 at hzr; linarith
  have hGd : ∀ n ≤ J + 1, ContDiffOn ℝ (n : WithTop ℕ∞) (toChart F) (Uc d) := fun n hn =>
    (toChart_contDiffOn hF.smooth).of_le (by exact_mod_cast hn)
  have hnear : ∀ a c, a + c = k → ‖mixedDeriv a c (toChart F) X z‖ ≤ B * (1 + C) := by
    intro a c hac
    refine (hF.near a c (by omega) X z hz hzr).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ hB
    have h1 : r ^ (-(σ + (c : ℝ))) ≤ r ^ (-(σ + ((J : ℝ) + 1))) :=
      Real.rpow_le_rpow_of_exponent_ge hr0 hr1 (by
        have : (c : ℝ) ≤ J + 1 := by exact_mod_cast (by omega : c ≤ J + 1)
        linarith)
    have h2 := hC r hr0 hr1
    have h3 : r ^ (-(σ + (c : ℝ))) * (1 + |Real.log r|) ^ (fun _ : ℕ => b) c ≤ C :=
      (mul_le_mul_of_nonneg_right h1 (by positivity)).trans h2
    linarith
  have hTB : ∀ a c, a + c = k → TB (toChart F) (X, z) a c (B * (1 + C)) := fun a c hac =>
    tb_of_norm_le isOpen_Uc (hGd (a + c) (by omega)) hq (hnear a c hac)
  have hfull := full_of_tb k (toChart F) (B * (1 + C)) (by positivity)
    ((hGd k hk).contDiffAt (isOpen_Uc.mem_nhds hq)) hTB
  have hnorm : ‖iteratedFDeriv ℝ k (toChart F) (X, z)‖ ≤ 2 ^ k * (B * (1 + C)) := by
    refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun w => ?_
    have := hfull w
    rw [Real.norm_eq_abs]
    linarith
  have hconv := norm_iteratedFDeriv_chart_le (lift2 F) k (X, z)
  rw [← toChart_eq] at hconv
  have hk4 : (4 : ℝ) ^ k ≤ 4 ^ (J + 1) := pow_le_pow_right₀ (by norm_num) hk
  have h2k : (2 : ℝ) ^ k * 2 ^ k = 4 ^ k := by rw [← mul_pow]; norm_num
  calc ‖iteratedFDeriv ℝ k (lift2 F) (chartT d (X, z))‖
      ≤ 2 ^ k * ‖iteratedFDeriv ℝ k (toChart F) (X, z)‖ := hconv
    _ ≤ 2 ^ k * (2 ^ k * (B * (1 + C))) := mul_le_mul_of_nonneg_left hnorm (by positivity)
    _ = 4 ^ k * (B * (1 + C)) := by rw [← mul_assoc, h2k]
    _ ≤ 4 ^ (J + 1) * (B * (1 + C)) := mul_le_mul_of_nonneg_right hk4 (by positivity)
    _ = _ := by ring

theorem lift2_periodic_fst (F : Torus d → Torus d → ℝ) (v : Euc d × Euc d) (n : Lattice d) :
    lift2 F (v + (Lattice.toEuc n, (0 : Euc d))) = lift2 F v := by
  simp only [lift2, Prod.fst_add, Prod.snd_add, add_zero]
  rw [mk_add', mk_toEuc', add_zero]

theorem iteratedFDeriv_lift2_periodic (F : Torus d → Torus d → ℝ) (k : ℕ) (v : Euc d × Euc d)
    (n : Lattice d) :
    iteratedFDeriv ℝ k (lift2 F) (v + (Lattice.toEuc n, (0 : Euc d))) = iteratedFDeriv ℝ k (lift2 F) v := by
  rw [← iteratedFDeriv_comp_add_right]
  congr 1
  funext w
  exact lift2_periodic_fst F w n

theorem near_rep {p : Euc d × Euc d} (hp : p ∈ offDiag d)
    (hdist : Torus.eucDist (Torus.mk p.1) (Torus.mk p.2) < r0) :
    ∃ (X z : Euc d) (n : Lattice d), z ≠ 0 ∧ ‖z‖ < r0 ∧
      p = chartT d (X, z) + (Lattice.toEuc n, (0 : Euc d)) := by
  set nv : Lattice d := fun i => round (p.1 i - p.2 i) with hnv
  set z0 : Euc d := WithLp.toLp 2 fun i => (p.1 i - p.2 i) - (round (p.1 i - p.2 i) : ℝ) with hz0
  have hsplit : p.1 - p.2 = Lattice.toEuc nv + z0 := by
    ext i; simp [Lattice.toEuc, hz0, hnv]
  have hnorm : ‖z0‖ = Torus.eucDist (Torus.mk p.1) (Torus.mk p.2) := by
    rw [EuclideanSpace.norm_eq, Torus.eucDist]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    have : (Torus.mk p.1) i - (Torus.mk p.2) i = (((p.1 i - p.2 i : ℝ)) : UnitAddCircle) := by
      simp [Torus.mk]
    rw [this, UnitAddCircle.norm_eq]
    simp [hz0, sq_abs]
  have hz0ne : z0 ≠ 0 := by
    intro h
    apply (mem_offDiag_iff p).1 hp
    show Torus.mk (p.1 - p.2) = 0
    rw [hsplit, h, add_zero, mk_toEuc']
  refine ⟨p.2 + (1 / 2 : ℝ) • z0, z0, nv, hz0ne, by rw [hnorm]; exact hdist, ?_⟩
  rw [chartT_apply]
  ext1
  · show p.1 = p.2 + (1 / 2 : ℝ) • z0 + (1 / 2 : ℝ) • z0 + Lattice.toEuc nv
    have : p.1 = p.2 + (Lattice.toEuc nv + z0) := by rw [← hsplit]; abel
    rw [this]; module
  · show p.2 = p.2 + (1 / 2 : ℝ) • z0 - (1 / 2 : ℝ) • z0 + 0
    module

theorem dense_nonlat (hd : 0 < d) : Dense {u : Euc d | Torus.mk u ≠ 0} := by
  rw [Metric.dense_iff]
  intro x r hr
  set e : Euc d := EuclideanSpace.single ⟨0, hd⟩ (1 : ℝ) with he
  have hne : ‖e‖ = 1 := by simp [he]
  have he0 : e ≠ 0 := by intro h; rw [h] at hne; simp at hne
  set r' := min r (1 / 2) with hr'
  have hr'0 : 0 < r' := lt_min hr (by norm_num)
  have hr'r : r' ≤ r := min_le_left _ _
  have hr'h : r' ≤ 1 / 2 := min_le_right _ _
  have hdist : ∀ η : ℝ, 0 < η → η < r' → x + η • e ∈ Metric.ball x r := by
    intro η h0 h1
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, hne, Real.norm_of_nonneg h0.le,
      mul_one]
    linarith
  by_contra hcon
  rw [Set.not_nonempty_iff_eq_empty] at hcon
  have hmem : ∀ η : ℝ, 0 < η → η < r' → Torus.mk (x + η • e) = 0 := by
    intro η h0 h1
    by_contra hnot
    have : x + η • e ∈ Metric.ball x r ∩ {u : Euc d | Torus.mk u ≠ 0} := ⟨hdist η h0 h1, hnot⟩
    rw [hcon] at this; exact this
  have a1 := hmem (r' / 2) (by linarith) (by linarith)
  have a2 := hmem (r' / 4) (by linarith) (by linarith)
  have := lat_eq_of_close a1 a2 (by
    have : x + (r' / 2) • e - (x + (r' / 4) • e) = (r' / 4) • e := by
      rw [add_sub_add_left_eq_sub, ← sub_smul]; congr 1; ring
    rw [this, norm_smul, hne, Real.norm_eq_abs, abs_of_pos (by linarith)]
    linarith)
  have h3 : (r' / 2) • e = (r' / 4) • e := add_left_cancel this
  have h4 : ((r' / 2) - (r' / 4)) • e = 0 := by rw [sub_smul, h3, sub_self]
  rcases smul_eq_zero.mp h4 with h | h
  · linarith
  · exact he0 h

theorem dense_ne_mk (hd : 0 < d) (a : Euc d) : Dense {v : Euc d | Torus.mk v ≠ Torus.mk a} := by
  have h := (dense_nonlat hd).preimage (Homeomorph.subRight a).isOpenMap
  convert h using 1
  ext v
  simp [Homeomorph.subRight, mk_eq_iff]

theorem neBot_punctured_torus (hd : 0 < d) (a b : Euc d) :
    (𝓝[{v : Euc d | Torus.mk v ≠ Torus.mk a}] b).NeBot :=
  mem_closure_iff_nhdsWithin_neBot.mp (by rw [(dense_ne_mk hd a).closure_eq]; trivial)

theorem lift2_diagExt_eq (hd : 0 < d) {F : Torus d → Torus d → ℝ} {g : Euc d × Euc d → ℝ}
    (hg : Continuous g) (hgF : ∀ p ∈ offDiag d, g p = lift2 F p) : lift2 (diagExt F) = g := by
  funext p
  by_cases hp : p ∈ offDiag d
  · have hne : Torus.mk p.1 ≠ Torus.mk p.2 := hp
    simp only [lift2, diagExt, if_neg hne]
    exact (hgF p hp).symm
  have hS : Torus.mk p.1 = Torus.mk p.2 := by
    by_contra h; exact hp h
  set x : Torus d := Torus.mk p.1 with hx
  set S' : Set (Euc d) := {v | Torus.mk v ≠ Torus.mk p.1} with hS'
  have hmk := isOpenQuotientMap_mk (d := d)
  have hmkc : Continuous (Torus.mk : Euc d → Torus d) := hmk.continuous
  have hNe : (𝓝[≠] x).NeBot := by
    have h1 : Filter.map Torus.mk (𝓝[S'] p.2) ≤ 𝓝[≠] x := by
      rw [nhdsWithin, nhdsWithin]
      refine (Filter.map_inf_le).trans (inf_le_inf ?_ ?_)
      · show Filter.map Torus.mk (𝓝 p.2) ≤ 𝓝 x
        rw [hS]; exact hmkc.continuousAt
      · rw [Filter.map_principal]
        refine Filter.principal_mono.2 ?_
        rintro _ ⟨v, hv, rfl⟩
        exact hv
    have hne : (𝓝[S'] p.2).NeBot := neBot_punctured_torus hd p.1 p.2
    have : (Filter.map Torus.mk (𝓝[S'] p.2)).NeBot := hne.map _
    exact Filter.NeBot.mono this h1
  have hle : 𝓝[≠] x ≤ Filter.map Torus.mk (𝓝[S'] p.2) := by
    rw [nhdsWithin, nhdsWithin]
    have : Filter.map Torus.mk (𝓝 p.2 ⊓ 𝓟 S') = Filter.map Torus.mk (𝓝 p.2) ⊓ 𝓟 {x}ᶜ := by
      exact Filter.map_inf_principal_preimage (f := Torus.mk) (s := {x}ᶜ) (l := 𝓝 p.2)
    rw [this]
    refine inf_le_inf ?_ le_rfl
    have := hmk.isOpenMap.nhds_le p.2
    rw [← hS] at this
    exact this
  have hlim : Tendsto (fun y' => F x y') (𝓝[≠] x) (𝓝 (g p)) := by
    refine Tendsto.mono_left ?_ hle
    rw [Filter.tendsto_map'_iff]
    have h1 : Tendsto (fun v : Euc d => g (p.1, v)) (𝓝[S'] p.2) (𝓝 (g p)) := by
      have : Tendsto (fun v : Euc d => g (p.1, v)) (𝓝 p.2) (𝓝 (g (p.1, p.2))) :=
        (hg.comp (continuous_const.prodMk continuous_id)).tendsto p.2
      exact this.mono_left nhdsWithin_le_nhds
    refine h1.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with v hv
    have hvU : (p.1, v) ∈ offDiag d := fun h => hv h.symm
    rw [hgF _ hvU]
    rfl
  have : lift2 (diagExt F) p = limUnder (𝓝[≠] x) (fun y' => F x y') := by
    show diagExt F (Torus.mk p.1) (Torus.mk p.2) = _
    unfold diagExt
    rw [if_pos hS]
  rw [this]
  exact hlim.limUnder_eq

theorem full_bound_offDiag {σ : ℝ} {b J : ℕ} (hσ : σ + ((J : ℝ) + 1) < 0) :
    ∃ K0 : ℝ, 0 ≤ K0 ∧ ∀ {B : ℝ} {F : Torus d → Torus d → ℝ}, 0 ≤ B → Conormal σ b (J + 1) B F →
      ∀ p ∈ offDiag d, ∀ k ≤ J + 1, ‖iteratedFDeriv ℝ k (lift2 F) p‖ ≤ K0 * B := by
  obtain ⟨C0, hC0, hC⟩ := near_full_bound (d := d) hσ (b := b)
  refine ⟨max C0 1, le_max_of_le_right zero_le_one, ?_⟩
  intro B F hB hF p hp k hk
  by_cases hdist : Torus.eucDist (Torus.mk p.1) (Torus.mk p.2) < r0
  · obtain ⟨X, z, n, hz, hzr, hpe⟩ := near_rep hp hdist
    have := hC (X := X) hB hF hz hzr hk
    rw [hpe, iteratedFDeriv_lift2_periodic]
    exact this.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hB)
  · push Not at hdist
    have := hF.far k hk p hp hdist
    calc _ ≤ B := this
      _ = 1 * B := (one_mul B).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hB

/-- Extension across the diagonal (`conormal_extend`). -/
theorem conormal_extend_aux (hd : 2 ≤ d) (J : ℕ) (σ : ℝ) (b : ℕ) (hσ : σ + ((J : ℝ) + 1) < 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (B : ℝ) (F : Torus d → Torus d → ℝ), 0 ≤ B →
      Conormal σ b (J + 1) B F →
        PDE.IsCk2 J (diagExt F) ∧ PDE.cbNorm2 J (diagExt F) ≤ C * B ∧
        ∀ x y, x ≠ y → diagExt F x y = F x y := by
  obtain ⟨K0, hK0, hK⟩ := full_bound_offDiag (d := d) (b := b) hσ
  refine ⟨((J : ℝ) + 1) * K0, by positivity, ?_⟩
  intro B F hB hF
  have hbd := hK hB hF
  obtain ⟨g, hg, hgF⟩ := ext_theorem hd J (lift2 F) (K0 * B) hF.smooth
    (fun j hj p hp => hbd p hp j hj)
  have hdiag : lift2 (diagExt F) = g := lift2_diagExt_eq (by omega) hg.continuous hgF
  refine ⟨?_, ?_, ?_⟩
  · show ContDiff ℝ (J : WithTop ℕ∞) (lift2 (diagExt F))
    rw [hdiag]; exact hg
  · -- the `C^J` norm
    have hKB : 0 ≤ K0 * B := mul_nonneg hK0 hB
    have hpt : ∀ j ≤ J, ∀ p : Euc d × Euc d, ‖iteratedFDeriv ℝ j g p‖ ≤ K0 * B := by
      intro j hj
      have hclosed : IsClosed {p : Euc d × Euc d | ‖iteratedFDeriv ℝ j g p‖ ≤ K0 * B} :=
        isClosed_le (hg.continuous_iteratedFDeriv (by exact_mod_cast hj)).norm continuous_const
      have hsub : offDiag d ⊆ {p : Euc d × Euc d | ‖iteratedFDeriv ℝ j g p‖ ≤ K0 * B} := by
        intro p hp
        have hev : g =ᶠ[𝓝 p] lift2 F := by
          filter_upwards [isOpen_offDiag.mem_nhds hp] with y hy using hgF y hy
        show ‖iteratedFDeriv ℝ j g p‖ ≤ K0 * B
        rw [(hev.iteratedFDeriv ℝ j).eq_of_nhds]
        exact hbd p hp j (by omega)
      have hdense := dense_offDiag (d := d) (by omega)
      intro p
      exact (closure_minimal hsub hclosed) (hdense.closure_eq ▸ Set.mem_univ p)
    unfold PDE.cbNorm2
    have e : PDE.lift2 (diagExt F) = g := hdiag
    rw [e]
    calc ∑ j ∈ Finset.range (J + 1), ⨆ p : Euc d × Euc d, ‖iteratedFDeriv ℝ j g p‖
        ≤ ∑ _j ∈ Finset.range (J + 1), K0 * B := by
          refine Finset.sum_le_sum fun j hj => ?_
          have hj' : j ≤ J := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
          exact Real.iSup_le (fun p => hpt j hj' p) hKB
      _ = ((J : ℝ) + 1) * K0 * B := by simp; ring
  · intro x y hxy
    unfold diagExt
    rw [if_neg hxy]

end HRS.Parx

end
