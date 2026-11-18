import HRS.MC.E213U13m

/-!
# E213U13n: the window drift `D_a` lies in the second chaos
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false

noncomputable section

namespace HRS.MC.E213U13

section DChaos

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Plan HRS.MC.E213U11
  HRS.MC.E213U1

variable {d : ℕ} {S : PreparedData d} {β₀ m : ℝ} {hE : EdgeworthHyp S β₀ m} (gd : GaussData S β₀ hE)

theorem gd_B_measurable_at (v : ℝ) : Measurable (fun ω => gd.B v ω) :=
  gd.B_meas.comp (measurable_const.prodMk measurable_id)

theorem gd_B_coord_InQ2 {ξ : ℕ → gd.Ω₀ → ℝ} {hm : ∀ i, Measurable (ξ i)} {hξ : IsStdGaussianSeq gd.P₀ ξ}
    (hX : ∀ t : ℝ, 0 ≤ t → ∀ k : NonzeroLattice d,
      InQ1 hξ hm (fun ω => NegSobolev.fourierCoeff (gd.η t ω) k)) :
    ∀ᵐ v ∂(volume.restrict (Set.Ici (0 : ℝ))), ∀ k : NonzeroLattice d,
      InQ2 hξ (fun ω => NegSobolev.fourierCoeff (gd.B v ω) k) := by
  filter_upwards [gd.B_wick, ae_restrict_mem measurableSet_Ici] with v hv hv0 k
  have hv0' : 0 ≤ v := hv0
  have hQeq : (fun ω => NegSobolev.eval (gd.B v ω) (Torus.realMode k)) =
      fun ω => NegSobolev.fourierCoeff (gd.B v ω) k := by
    funext ω; exact q38b_eval_realMode _ _
  have hmeas : Measurable (fun ω => NegSobolev.fourierCoeff (gd.B v ω) k) :=
    (HRS.FieldSingAux.coordCLM (rLvl d) k).continuous.measurable.comp (gd_B_measurable_at gd v)
  have hk := hv k
  rw [hQeq] at hk
  exact InQ2.of_halfWick (hξ := hξ) (hm := hm) (η := fun ω => gd.η v ω) (fun k => hX v hv0' k)
    hmeas.aestronglyMeasurable hk

theorem gd_B_int (H : ℝ) (hH : 0 < H) :
    ∀ᵐ ω ∂gd.P₀, Integrable (fun v => ‖gd.B v ω‖) (volume.restrict (Set.Ioc 0 H)) := by
  filter_upwards [u11_B_integrable gd H hH] with ω hω
  exact hω.mono_set Set.Ioc_subset_Icc_self

theorem gd_B_L2 (H : ℝ) (hH : 0 < H) :
    MemLp (fun ω => ∫ v in Set.Ioc 0 H, ‖gd.B v ω‖) 2 gd.P₀ := by
  set N : ℕ := ⌈H⌉₊ with hN
  have hn : (0 : ℝ) < N := by
    have : 0 < ⌈H⌉₊ := Nat.ceil_pos.2 hH
    exact_mod_cast this
  have hHn : H ≤ N := Nat.le_ceil H
  obtain ⟨CB, -, hCB⟩ := u11_B_moment gd 1 one_pos 2 (by norm_num)
  have hterm : ∀ k : ℕ, MemLp (fun ω => ‖toL2 (rLvl d) 1 (fun t => gd.B ((k : ℝ) + t) ω)‖) 2 gd.P₀ := by
    intro k
    obtain ⟨hmk, hik, -⟩ := hCB (k : ℝ) (Nat.cast_nonneg k)
    have hf : MemLp (fun ω => toL2 (rLvl d) 1 (fun t => gd.B ((k : ℝ) + t) ω)) 2 gd.P₀ := by
      have := (integrable_norm_rpow_iff (μ := gd.P₀) hmk.aestronglyMeasurable (p := 2) (by norm_num)
        (by norm_num)).1 (by simpa using hik)
      exact this
    exact hf.norm
  set G : gd.Ω₀ → ℝ := fun ω => ∑ k ∈ Finset.range N, ‖toL2 (rLvl d) 1 (fun t => gd.B ((k : ℝ) + t) ω)‖ with hG
  have hGL : MemLp G 2 gd.P₀ := memLp_finsetSum _ fun k _ => hterm k
  have hmeasI : AEStronglyMeasurable (fun ω => ∫ v in Set.Ioc 0 H, ‖gd.B v ω‖) gd.P₀ := by
    have hjm : Measurable (Function.uncurry fun (ω : gd.Ω₀) (v : ℝ) => ‖gd.B v ω‖) :=
      (gd.B_meas.comp measurable_swap).norm
    exact (hjm.stronglyMeasurable.integral_prod_right (ν := volume.restrict (Set.Ioc 0 H))).aestronglyMeasurable
  refine hGL.of_le hmeasI ?_
  filter_upwards [u11_B_integrable gd (N : ℝ) hn, u11_B_blocks gd] with ω hint hblk
  have h1 := u11_weighted_block (fun v => ‖gd.B v ω‖) (fun v => norm_nonneg _) N hint 0 0 H le_rfl hHn
  simp only [neg_zero, zero_mul, Real.exp_zero, one_mul] at h1
  have h2 : ∫ v in Set.Ioc 0 H, ‖gd.B v ω‖ ≤ G ω := by
    refine h1.trans (Finset.sum_le_sum fun k _ => ?_)
    exact u11_block_integral_le (fun v => gd.B v ω) k (hblk k)
  have h3 : 0 ≤ ∫ v in Set.Ioc 0 H, ‖gd.B v ω‖ := integral_nonneg fun v => norm_nonneg _
  rw [Real.norm_eq_abs, abs_of_nonneg h3]
  exact h2.trans (le_abs_self _) |>.trans (by rw [Real.norm_eq_abs])

theorem gd_D_coord_repr (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a) {C c : ℝ}
    {Vev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m} (hC : 0 < C) (hc : 0 < c)
    (hsp : U1Spec hE C c Vev) (t : Set.Icc (0 : ℝ) T) (k : NonzeroLattice d) :
    ∀ᵐ ω ∂gd.P₀, NegSobolev.fourierCoeff (PathSpace.at' (gd.Dwin T a ω) t) k =
      ∫ v in Set.Ioc 0 (a + T), (if v ≤ a + t.1 then
        HRS.FieldSingAux.coordCLM m k (Vev (a + t.1) (u1_cl (a + t.1) v)
          (HRS.MD.EQInterp.embedCLM (rLvl_le hE) (gd.B v ω))) else 0) := by
  have hH : 0 < a + T := by linarith
  filter_upwards [u11_B_integrable gd (a + T) hH] with ω hω
  have hmeasB := u11_B_nearCoef_measurable gd ω
  have hcontω := HRS.MC.E213U1.winDrift_cont_proof hE T hT a ha (fun v => gd.B v ω) hmeasB hω 0 (a + T)
    le_rfl hH.le le_rfl
  have hD : gd.Dwin T a ω = winRestr a ha (Sec7.pathOf m (a + T) (fun s => ∫ v in Set.Ioc 0 (min (a + T) s),
      Vprop (regime S β₀ hE).D (regime S β₀ hE).ρ m s v (NegSobolev.embed m (gd.B v ω)))) := by
    unfold GaussData.Dwin winDrift driftInc
    rw [dif_pos ha]
  rw [hD, winRestr_at', e213o_pathOf_at' _ hcontω]
  have hs : (e213o_shift ha t : ℝ) ∈ Set.Icc (0 : ℝ) (a + T) := (e213o_shift ha t).2
  have hF := HRS.MC.E213U1.u1_Fint hE hC hc hsp T a hT ha (fun v => gd.B v ω) hmeasB hω 0 (a + T)
    le_rfl le_rfl _ hs
  rw [hF.1]
  have e : (e213o_shift ha t : ℝ) = a + t.1 := rfl
  show HRS.FieldSingAux.coordCLM m k _ = _
  rw [← ContinuousLinearMap.integral_comp_comm _ hF.2.1]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only [u1_F, Set.indicator_apply, Set.mem_Iic, e]
  split_ifs
  · rfl
  · exact map_zero _

theorem gd_D_coord_InQ2 {ξ : ℕ → gd.Ω₀ → ℝ} {hm : ∀ i, Measurable (ξ i)} {hξ : IsStdGaussianSeq gd.P₀ ξ}
    (hX : ∀ t : ℝ, 0 ≤ t → ∀ k : NonzeroLattice d,
      InQ1 hξ hm (fun ω => NegSobolev.fourierCoeff (gd.η t ω) k))
    (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a) (t : Set.Icc (0 : ℝ) T) (k : NonzeroLattice d) :
    InQ2 hξ (fun ω => NegSobolev.fourierCoeff (PathSpace.at' (gd.Dwin T a ω) t) k) := by
  classical
  obtain ⟨C, c, hC, hc, Vev, hsp⟩ := HRS.MC.E213U1.u1_vev hE
  have hH : 0 < a + T := by linarith
  have hs0 : 0 ≤ a + t.1 := by linarith [t.2.1]
  have hsH : a + t.1 ≤ a + T := by linarith [t.2.2]
  set s : ℝ := a + t.1 with hs
  set ι := HRS.MD.EQInterp.embedCLM (rLvl_le hE) with hι
  set Lk : NegSobolev d m →L[ℝ] ℝ := HRS.FieldSingAux.coordCLM m k with hLk
  let Λ : ℝ → NegSobolev d (rLvl d) →L[ℝ] ℝ := fun v =>
    if v ≤ s then Lk.comp ((Vev s (u1_cl s v)).comp ι) else 0
  have hΛapp : ∀ v x, Λ v x = if v ≤ s then Lk (Vev s (u1_cl s v) (ι x)) else 0 := by
    intro v x
    by_cases hv : v ≤ s <;> simp [Λ, hv]
  have hιnorm : ‖ι‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
    rw [one_mul]
    exact NegSobolev.norm_embed_le m (rLvl_le hE) x
  have hΛnorm : ∀ v, ‖Λ v‖ ≤ ‖Lk‖ * C := by
    intro v
    by_cases hv : v ≤ s
    · have : Λ v = Lk.comp ((Vev s (u1_cl s v)).comp ι) := by simp [Λ, hv]
      rw [this]
      have hcl := u1_cl_mem (t := s) v hs0
      have hV : ‖Vev s (u1_cl s v)‖ ≤ C := by
        refine (hsp.1 _ _ hcl.1 hcl.2).trans ?_
        have : Real.exp (-c * (s - u1_cl s v)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [hcl.2])
        calc C * Real.exp (-c * (s - u1_cl s v)) ≤ C * 1 := by gcongr
          _ = C := mul_one C
      calc ‖Lk.comp ((Vev s (u1_cl s v)).comp ι)‖ ≤ ‖Lk‖ * ‖(Vev s (u1_cl s v)).comp ι‖ :=
            ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ ‖Lk‖ * (‖Vev s (u1_cl s v)‖ * ‖ι‖) := by
            gcongr; exact ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ ‖Lk‖ * (C * 1) := by
            gcongr
        _ = ‖Lk‖ * C := by rw [mul_one]
    · have : Λ v = 0 := by simp [Λ, hv]
      rw [this, norm_zero]
      exact mul_nonneg (norm_nonneg _) hC.le
  have hΛm : Measurable (fun p : ℝ × NegSobolev d (rLvl d) => Λ p.1 p.2) := by
    have hcont : Continuous fun p : ℝ × NegSobolev d (rLvl d) => Lk (Vev s (u1_cl s p.1) (ι p.2)) :=
      Lk.continuous.comp ((u1_clamp_joint (H := a + T) hC hc hsp hs0 hsH).comp
        (continuous_fst.prodMk (ι.continuous.comp continuous_snd)))
    have : (fun p : ℝ × NegSobolev d (rLvl d) => Λ p.1 p.2) =
        fun p => if p.1 ≤ s then Lk (Vev s (u1_cl s p.1) (ι p.2)) else 0 := by
      funext p; exact hΛapp _ _
    rw [this]
    exact Measurable.ite (measurableSet_le measurable_fst measurable_const) hcont.measurable measurable_const
  have hZ2 : MemLp (fun ω => NegSobolev.fourierCoeff (PathSpace.at' (gd.Dwin T a ω) t) k) 2 gd.P₀ := by
    have h2 : MemLp (gd.Dwin T a) (ENNReal.ofReal 2) gd.P₀ := gd_D_memLp gd T hT a ha 2 (by norm_num)
    rw [show ENNReal.ofReal 2 = 2 by norm_num] at h2
    exact memLp_clm_comp h2 (HRS.MC.Sec7.S7PIC.S7PIC_lf m T t k)
  refine InQ2.of_linear_integral (ν := volume.restrict (Set.Ioc 0 (a + T))) (Bf := gd.B) ?_ ?_ (gd_B_int gd _ hH)
    (gd_B_L2 gd _ hH) Λ (‖Lk‖ * C) (mul_nonneg (norm_nonneg _) hC.le) hΛnorm hΛm hZ2 ?_
  · exact gd.B_meas.comp measurable_swap
  · exact ae_restrict_of_ae_restrict_of_subset (fun v hv => (hv.1.le : v ∈ Set.Ici (0 : ℝ)))
      (gd_B_coord_InQ2 gd hX)
  · filter_upwards [gd_D_coord_repr gd T hT a ha hC hc hsp t k] with ω h
    rw [h]
    refine integral_congr_ae (Eventually.of_forall fun v => ?_)
    exact (hΛapp v (gd.B v ω)).symm

theorem gd_D_chaos {ξ : ℕ → gd.Ω₀ → ℝ} {hm : ∀ i, Measurable (ξ i)} {hξ : IsStdGaussianSeq gd.P₀ ξ}
    (hX : ∀ t : ℝ, 0 ≤ t → ∀ k : NonzeroLattice d,
      InQ1 hξ hm (fun ω => NegSobolev.fourierCoeff (gd.η t ω) k))
    (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a) {q : ℝ} (hq : 2 ≤ q) :
    InSecondChaos gd.P₀ ξ q (gd.Dwin T a) := by
  obtain ⟨Pn, Ss, ℓ, b, hPn, hlim, hfin, hs⟩ := pathproj_data (d := d) m T hT
  refine inSecondChaos_of_approx hξ hm (u11_Dwin_aesm gd T hT a ha) hq (lt_add_one q)
    (gd_D_memLp gd T hT a ha (q + 1) (by linarith)) Pn hPn hlim Ss ℓ b hfin fun n s _ => ?_
  obtain ⟨t, k, h⟩ := hs s
  simp_rw [h]
  exact gd_D_coord_InQ2 gd hX T hT a ha t k

end DChaos

end HRS.MC.E213U13
