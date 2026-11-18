import HRS.MC.WinJSpecDefs
import HRS.MC.WinJP1

/-!
# WJ10: P10a `p10a_norm_tensorPow2_sub_le`, P10b `p10b_theta_sub_le`, P10c `p10c_vev_compare`

The statements are copied verbatim from `HRS/MC/WinJSpec.lean` (the sorried spec, not imported).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.WinJ

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Plan HRS.MC.E213Final
open HRS.MC.E214Plan HRS.MC.Sec7.PID HRS.MC.E213U3

section TensorAlgebra

variable {d : ℕ}

/-- Telescoping for a bilinear form on `Fin 2`. -/
lemma p_wj10_telescope2 {B' : Type*} [NormedAddCommGroup B'] [NormedSpace ℝ B']
    (M : B' [×2]→L[ℝ] ℝ) (a b : Fin 2 → B') :
    M a - M b = M (Function.update a 0 (a 0 - b 0)) + M (Function.update b 1 (a 1 - b 1)) := by
  have h1 : M (Function.update a 0 (a 0 - b 0)) = M a - M (Function.update a 0 (b 0)) := by
    rw [M.map_update_sub, Function.update_eq_self]
  have h2 : M (Function.update b 1 (a 1 - b 1)) = M (Function.update a 0 (b 0)) - M b := by
    have e : Function.update b 1 (a 1) = Function.update a 0 (b 0) := by
      funext i
      fin_cases i <;> simp [Function.update_apply]
    rw [M.map_update_sub, e, Function.update_eq_self]
  rw [h1, h2]
  abel

/-- Bound on the difference of the two restrictions of a bilinear form. -/
lemma p_wj10_comp_sub_le {B B' : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup B'] [NormedSpace ℝ B'] (P P' : B →L[ℝ] B') (M : B' [×2]→L[ℝ] ℝ) :
    ‖M.compContinuousLinearMap (fun _ : Fin 2 => P) - M.compContinuousLinearMap (fun _ : Fin 2 => P')‖ ≤
      (‖P‖ + ‖P'‖) * ‖P - P'‖ * ‖M‖ := by
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) (fun x => ?_)
  simp only [ContinuousMultilinearMap.sub_apply, ContinuousMultilinearMap.compContinuousLinearMap_apply]
  rw [p_wj10_telescope2 M (fun i => P (x i)) (fun i => P' (x i))]
  beta_reduce
  have e0 : ‖P (x 0) - P' (x 0)‖ ≤ ‖P - P'‖ * ‖x 0‖ := by
    have := (P - P').le_opNorm (x 0)
    rwa [ContinuousLinearMap.sub_apply] at this
  have e2 : ‖P (x 1) - P' (x 1)‖ ≤ ‖P - P'‖ * ‖x 1‖ := by
    have := (P - P').le_opNorm (x 1)
    rwa [ContinuousLinearMap.sub_apply] at this
  have e1 : ‖P (x 1)‖ ≤ ‖P‖ * ‖x 1‖ := P.le_opNorm (x 1)
  have e1' : ‖P' (x 0)‖ ≤ ‖P'‖ * ‖x 0‖ := P'.le_opNorm (x 0)
  have h1 := M.le_opNorm (Function.update (fun i => P (x i)) 0 (P (x 0) - P' (x 0)))
  rw [Fin.prod_univ_two] at h1
  simp only [Function.update_self, Function.update_of_ne (show (1 : Fin 2) ≠ 0 by decide)] at h1
  have h2 := M.le_opNorm (Function.update (fun i => P' (x i)) 1 (P (x 1) - P' (x 1)))
  rw [Fin.prod_univ_two] at h2
  simp only [Function.update_self, Function.update_of_ne (show (0 : Fin 2) ≠ 1 by decide)] at h2
  rw [Fin.prod_univ_two]
  calc ‖M (Function.update (fun i => P (x i)) 0 (P (x 0) - P' (x 0))) +
        M (Function.update (fun i => P' (x i)) 1 (P (x 1) - P' (x 1)))‖
      ≤ ‖M (Function.update (fun i => P (x i)) 0 (P (x 0) - P' (x 0)))‖ +
          ‖M (Function.update (fun i => P' (x i)) 1 (P (x 1) - P' (x 1)))‖ := norm_add_le _ _
    _ ≤ ‖M‖ * (‖P (x 0) - P' (x 0)‖ * ‖P (x 1)‖) + ‖M‖ * (‖P' (x 0)‖ * ‖P (x 1) - P' (x 1)‖) :=
        add_le_add h1 h2
    _ ≤ ‖M‖ * ((‖P - P'‖ * ‖x 0‖) * (‖P‖ * ‖x 1‖)) + ‖M‖ * ((‖P'‖ * ‖x 0‖) * (‖P - P'‖ * ‖x 1‖)) := by
        gcongr
    _ = (‖P‖ + ‖P'‖) * ‖P - P'‖ * ‖M‖ * (‖x 0‖ * ‖x 1‖) := by ring

/-- Splitting a difference of two values of `J`, `J'` at two points. -/
lemma p_wj10_split {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (J J' : E →L[ℝ] ℝ) (p q : E) : J p - J' q = (J - J') p + J' (p - q) := by
  rw [ContinuousLinearMap.sub_apply, map_sub]
  abel

/-- `pathAt` is linear on the values in `[0, T]`. -/
lemma p_wj10_pathAt_sub {m T : ℝ} (w₁ w₂ : PathSpace d m T) (t : ℝ) :
    pathAt (w₁ - w₂) t = pathAt w₁ t - pathAt w₂ t := by
  unfold pathAt
  by_cases h : t ∈ Set.Icc (0 : ℝ) T
  · rw [dif_pos h, dif_pos h, dif_pos h]; rfl
  · rw [dif_neg h, dif_neg h, dif_neg h, sub_zero]

/-- **P10a.**  Tensor algebra for block propagation: `‖P^{⊗2} J - P'^{⊗2} J'‖ ≤ ‖P‖² ‖J - J'‖ + (‖P‖ + ‖P'‖) ‖P - P'‖ ‖J'‖`
for bounded operators `P, P' : B →L B'` and tensors `J, J'` on `B` (the norm of `TensorDual B 2` is the dual norm of the
bounded bilinear forms).  Proof route: `P^{⊗2}J - P'^{⊗2}J' = P^{⊗2}(J - J') + (P^{⊗2} - P'^{⊗2})J'`, `tensorPow'_norm_le`,
and `M(Px,Py) - M(P'x,P'y) = M((P-P')x,Py) + M(P'x,(P-P')y)` for the second term (`tensorPow'_apply`). -/
theorem p10a_norm_tensorPow2_sub_le {B B' : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup B'] [NormedSpace ℝ B'] (P P' : B →L[ℝ] B') (J J' : TensorDual B 2) :
    ‖tensorPow' 2 P J - tensorPow' 2 P' J'‖ ≤
      ‖P‖ * ‖P‖ * ‖J - J'‖ + (‖P‖ + ‖P'‖) * ‖P - P'‖ * ‖J'‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun M => ?_)
  simp only [ContinuousLinearMap.sub_apply, tensorPow'_apply]
  set Mp := M.compContinuousLinearMap (fun _ : Fin 2 => P) with hMp
  set Mq := M.compContinuousLinearMap (fun _ : Fin 2 => P') with hMq
  have hb1 : ‖Mp‖ ≤ ‖M‖ * (‖P‖ * ‖P‖) := by
    have := ContinuousMultilinearMap.norm_compContinuousLinearMap_le M (fun _ : Fin 2 => P)
    rw [Fin.prod_univ_two] at this
    exact this
  have hb2 : ‖Mp - Mq‖ ≤ (‖P‖ + ‖P'‖) * ‖P - P'‖ * ‖M‖ := p_wj10_comp_sub_le P P' M
  rw [p_wj10_split J J' Mp Mq]
  calc ‖(J - J') Mp + J' (Mp - Mq)‖ ≤ ‖(J - J') Mp‖ + ‖J' (Mp - Mq)‖ := norm_add_le _ _
    _ ≤ ‖J - J'‖ * ‖Mp‖ + ‖J'‖ * ‖Mp - Mq‖ :=
        add_le_add ((J - J').le_opNorm Mp) (J'.le_opNorm (Mp - Mq))
    _ ≤ ‖J - J'‖ * (‖M‖ * (‖P‖ * ‖P‖)) + ‖J'‖ * ((‖P‖ + ‖P'‖) * ‖P - P'‖ * ‖M‖) :=
        add_le_add (mul_le_mul_of_nonneg_left hb1 (norm_nonneg (J - J')))
          (mul_le_mul_of_nonneg_left hb2 (norm_nonneg J'))
    _ = (‖P‖ * ‖P‖ * ‖J - J'‖ + (‖P‖ + ‖P'‖) * ‖P - P'‖ * ‖J'‖) * ‖M‖ := by ring

/-- **P10b.**  The propagation operators `Θ x = (t ↦ V(a+t, s) x)` of `E213U3.u3_theta_exists` for two evolutions differ in
operator norm by at most the sup over `t ∈ [0,T]` of `‖V(a+t,s) - V'(a+t,s)‖` (here a uniform bound `K ≥ 0`).  Proof route:
`‖(Θ - Θ')x‖ = sup_t ‖(V(a+t,s) - V'(a+t,s)) x‖` (`pathAt` is linear, the norm of `PathSpace` is the sup norm). -/
theorem p10b_theta_sub_le (m T a s K : ℝ) (hK : 0 ≤ K)
    (V V' : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m)
    (Θ Θ' : NegSobolev d m →L[ℝ] PathSpace d m T)
    (hΘ : ∀ x t, t ∈ Set.Icc (0 : ℝ) T → pathAt (Θ x) t = V (a + t) s x)
    (hΘ' : ∀ x t, t ∈ Set.Icc (0 : ℝ) T → pathAt (Θ' x) t = V' (a + t) s x)
    (hbd : ∀ t ∈ Set.Icc (0 : ℝ) T, ‖V (a + t) s - V' (a + t) s‖ ≤ K) :
    ‖Θ - Θ'‖ ≤ K := by
  refine ContinuousLinearMap.opNorm_le_bound _ hK (fun x => ?_)
  rw [ContinuousLinearMap.sub_apply]
  refine (ContinuousMap.norm_le
    (show ContinuousMap (Set.Icc (0 : ℝ) T) (NegSobolev d m) from (Θ x - Θ' x))
    (mul_nonneg hK (norm_nonneg _))).2 fun t => ?_
  have ht : (t : ℝ) ∈ Set.Icc (0 : ℝ) T := t.2
  have key : (show ContinuousMap (Set.Icc (0 : ℝ) T) (NegSobolev d m) from (Θ x - Θ' x)) t =
      pathAt (Θ x - Θ' x) (t : ℝ) := by
    unfold pathAt
    rw [dif_pos ht]
    rfl
  rw [key, p_wj10_pathAt_sub, hΘ x (t : ℝ) ht, hΘ' x (t : ℝ) ht,
    ← ContinuousLinearMap.sub_apply (V (a + (t : ℝ)) s) (V' (a + (t : ℝ)) s) x]
  exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right (hbd (t : ℝ) ht) (norm_nonneg _))

end TensorAlgebra

section Packets

variable {d : ℕ} {S : PreparedData d} {β₀ m : ℝ} {hE : EdgeworthHyp S β₀ m}

/-- **P10c** (uses P1 at `b = 0`, `σ = m`).  The two dual evolutions on `E_m` (of the prepared trajectory and of the stationary
regime; any two operator families with `IsDualEvolution`, which determines them on `0 ≤ u ≤ t`) differ by
`‖Vev t u - Vev' t u‖_{E_m → E_m} ≤ C e^{-c(t-u)} e^{-κ u}`.  Proof route: `E213D.vprop_eq_vev` identifies `Vev t u` with `Vprop`
on `E_m`, then P1 with `b = 0` (`shift R 0` has the same `ρ`), `σ = m`.  This is the input of the `Θ`-difference in the unit blocks (P11b). -/
theorem p10c_vev_compare (sd : StatDatum S β₀ m hE) :
    ∃ C c κ : ℝ, 0 < C ∧ 0 < c ∧ 0 < κ ∧
      ∀ Vev Vev' : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m,
        IsDualEvolution (regime S β₀ hE).D (regime S β₀ hE).ρ m Vev →
        IsDualEvolution (regime sd.Ss S.β sd.hEs).D (regime sd.Ss S.β sd.hEs).ρ m Vev' →
        ∀ u t : ℝ, 0 ≤ u → u ≤ t →
          ‖Vev t u - Vev' t u‖ ≤ C * Real.exp (-c * (t - u)) * Real.exp (-κ * u) := by
  have hm : rLvl d ≤ m := by
    have h1 := hE.m_gt
    have h2 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    unfold rLvl
    linarith
  obtain ⟨C, c, κ, hC, hc, hκ, h⟩ := p1_vprop_compare_op sd m hm
  refine ⟨C, c, κ, hC, hc, hκ, fun Vev Vev' hV hV' u t hu hut => ?_⟩
  have h0 : (0 : ℝ) ≤ 0 := le_refl _
  have hρp : (Rp sd 0 h0).ρ = (regime S β₀ hE).ρ :=
    funext fun t => HRS.MC.E213F.shift_zero (regime S β₀ hE) h0 t
  have hρs : (Rs sd 0 h0).ρ = (regime sd.Ss S.β sd.hEs).ρ :=
    funext fun t => HRS.MC.E213F.shift_zero (regime sd.Ss S.β sd.hEs) h0 t
  have hDp : (Rp sd 0 h0).D = (regime S β₀ hE).D := rfl
  have hDs : (Rs sd 0 h0).D = (regime sd.Ss S.β sd.hEs).D := rfl
  have eV : ∀ F : NegSobolev d m, Vev t u F =
      Vprop (regime S β₀ hE).D (regime S β₀ hE).ρ m t u F := fun F =>
    (HRS.MC.E213D.vprop_eq_vev _ _ m Vev hV hu hut F).symm
  have eV' : ∀ F : NegSobolev d m, Vev' t u F =
      Vprop (regime sd.Ss S.β sd.hEs).D (regime sd.Ss S.β sd.hEs).ρ m t u F := fun F =>
    (HRS.MC.E213D.vprop_eq_vev _ _ m Vev' hV' hu hut F).symm
  refine ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (mul_nonneg hC.le (Real.exp_pos _).le) (Real.exp_pos _).le) (fun F => ?_)
  have e := h 0 h0 u t hu hut F
  rw [hDp, hρp, hDs, hρs, ← eV, ← eV', zero_add] at e
  rw [ContinuousLinearMap.sub_apply]
  exact e

end Packets

end HRS.MC.WinJ

end
