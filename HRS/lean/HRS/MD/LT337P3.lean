import HRS.MD.LT337P2
import HRS.Appendix.B15CAux1
import HRS.Energy.Coercivity

/-!
# Packet LT3 (chunk D): the diffusion term of the Coulomb energy identity

`lt3_diffusion_limit_proof`, `lt3_diffusion_bound_proof`, `lt3_diffLimit_le_proof` are the statements
`HRS.MD.LT337.lt3_diffusion_limit`, `lt3_diffusion_bound`, `lt3_diffLimit_le` (M L3140-3147).
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ComplexConjugate
open HRS HRS.MD.LT337P2

namespace HRS.MD.LT337P3

variable {d N : ℕ}

/-- The limit of the diffusion correction (same definition as `HRS.MD.LT337.diffLimit`). -/
def diffLimit (d : ℕ) {N : ℕ} (ρ : Torus d → ℝ) (X : Config d N) : ℝ :=
  cd d * (-(1 / (N : ℝ)) + 2 * ((1 / (N : ℝ)) * ∑ i, ρ (X i)) - ∫ x, ρ x ^ 2)

theorem lt3_norm_mk_le (v : Euc d) : ‖Torus.mk v‖ ≤ ‖v‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
  show ‖((v i : ℝ) : UnitAddCircle)‖ ≤ ‖v‖
  rw [UnitAddCircle.norm_eq]
  have h1 := round_le (v i) 0
  have h2 : |v i| ≤ ‖v‖ := by simpa using PiLp.norm_apply_le v i
  simp only [Int.cast_zero, sub_zero] at h1
  exact h1.trans h2

/-- `Δ g_M = c_d` at all points of torus-norm `≥ a`, for `M` large. -/
theorem lt3_lap_eq_cd (hd : 2 ≤ d) {a : ℝ} (ha : 0 < a) :
    ∃ M₀ : ℝ, ∀ M : ℝ, M₀ ≤ M → ∀ z : Torus d, a ≤ ‖z‖ →
      Torus.laplacian (b15c_gReg d ((d : ℝ) - 2) M) z = cd d := by
  have h2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : (0 : ℝ) ≤ (d : ℝ) - 2 := by linarith
  have hsd : (d : ℝ) - 2 < d := by linarith
  obtain ⟨M₀, hM₀⟩ := b15c_gReg_eventually_eq_off_ball (d := d) (by omega) hs0 hsd (r := a / 2)
    (by linarith)
  refine ⟨M₀, fun M hM z hz => ?_⟩
  have hz0 : z ≠ 0 := by
    intro h; rw [h, norm_zero] at hz; linarith
  have hev : Torus.lift (b15c_gReg d ((d : ℝ) - 2) M) =ᶠ[𝓝 (Torus.rep z)]
      Torus.lift (periodicRiesz d ((d : ℝ) - 2)) := by
    filter_upwards [Metric.ball_mem_nhds (Torus.rep z) (show 0 < a / 2 by linarith)] with u' hu'
    have hu'' : ‖u' - Torus.rep z‖ < a / 2 := by rwa [Metric.mem_ball, dist_eq_norm] at hu'
    have h1 : ‖Torus.mk u' - z‖ ≤ ‖u' - Torus.rep z‖ := by
      have := lt3_norm_mk_le (u' - Torus.rep z)
      rwa [KernelGrad.mk_sub, Torus.mk_rep] at this
    have h3 : a / 2 ≤ ‖Torus.mk u'‖ := by
      have := norm_sub_norm_le z (z - Torus.mk u')
      have e : z - (z - Torus.mk u') = Torus.mk u' := by abel
      rw [e, norm_sub_rev] at this
      linarith
    have h4 : a / 2 ≤ Torus.tdist (Torus.mk u') 0 := h3.trans (KernelGrad.norm_le_tdist _)
    exact hM₀ M hM _ h4
  have e1 : Torus.laplacian (b15c_gReg d ((d : ℝ) - 2) M) z =
      Laplacian.laplacian (Torus.lift (b15c_gReg d ((d : ℝ) - 2) M)) (Torus.rep z) := by
    conv_lhs => rw [← Torus.mk_rep z]
    exact lt2_laplacian_mk _ _
  have e2 : Torus.laplacian (periodicRiesz d ((d : ℝ) - 2)) z =
      Laplacian.laplacian (Torus.lift (periodicRiesz d ((d : ℝ) - 2))) (Torus.rep z) := by
    conv_lhs => rw [← Torus.mk_rep z]
    exact lt2_laplacian_mk _ _
  rw [e1, (InnerProductSpace.laplacian_congr_nhds hev).self_of_nhds, ← e2]
  exact (lt2_green_proof hd).2.2 z hz0

/-! #### Reflection -/

theorem lt3_lap_comp_sub (G : Euc d → ℝ) (hG : ContDiff ℝ 2 G) (a v : Euc d) :
    Laplacian.laplacian (fun w => G (a - w)) v = Laplacian.laplacian G (a - v) := by
  have e : (fun w => G (a - w)) = (fun u => G (u + a)) ∘ (-(ContinuousLinearMap.id ℝ (Euc d))) := by
    funext w; simp [sub_eq_neg_add]
  have hF : ContDiff ℝ 2 (fun u => G (u + a)) := hG.comp (contDiff_id.add contDiff_const)
  have key : ∀ m : Fin 2 → Euc d, iteratedFDeriv ℝ 2 (fun w => G (a - w)) v m =
      iteratedFDeriv ℝ 2 G (a - v) m := by
    intro m
    rw [e, ContinuousLinearMap.iteratedFDeriv_comp_right _ hF v le_rfl]
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, ContinuousLinearMap.neg_apply,
      ContinuousLinearMap.id_apply]
    have h1 : iteratedFDeriv ℝ 2 (fun u => G (u + a)) (-v) = iteratedFDeriv ℝ 2 G (-v + a) :=
      iteratedFDeriv_comp_add_right 2 a (-v)
    rw [h1, show -v + a = a - v by abel]
    rw [iteratedFDeriv_two_apply, iteratedFDeriv_two_apply]
    simp
  simp only [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis, key]

/-- The reflected translate `y ↦ h (x - y)`. -/
def reflT (h : Torus d → ℝ) (x : Torus d) : Torus d → ℝ := fun y => h (x - y)

theorem lt3_refl_lift (h : Torus d → ℝ) (x : Torus d) :
    Torus.lift (reflT h x) = fun w => Torus.lift h (Torus.rep x - w) := by
  funext w
  simp only [Torus.lift, Function.comp, reflT]
  congr 1
  rw [KernelGrad.mk_sub, Torus.mk_rep]

theorem lt3_isCk_refl {h : Torus d → ℝ} {k : WithTop ℕ∞} (hh : Torus.IsCk k h) (x : Torus d) :
    Torus.IsCk k (reflT h x) := by
  unfold Torus.IsCk
  rw [lt3_refl_lift]
  exact (show ContDiff ℝ k (Torus.lift h) from hh).comp (contDiff_const.sub contDiff_id)

theorem lt3_laplacian_refl {h : Torus d → ℝ} (hh : Torus.IsCk 2 h) (x y : Torus d) :
    Torus.laplacian (reflT h x) y = Torus.laplacian h (x - y) := by
  have e : x - y = Torus.mk (Torus.rep x - Torus.rep y) := by
    rw [KernelGrad.mk_sub, Torus.mk_rep, Torus.mk_rep]
  conv_lhs => rw [← Torus.mk_rep y]
  rw [e, lt2_laplacian_mk, lt2_laplacian_mk, lt3_refl_lift,
    lt3_lap_comp_sub _ (show ContDiff ℝ 2 (Torus.lift h) from hh)]

/-- Integration by parts for the (smooth) truncated kernels: `∫ Δh(x-y) ρ(y) = ∫ h(x-y) Δρ(y)`. -/
theorem lt3_ibp_kernel {h ρ : Torus d → ℝ} (hh : Torus.IsCk 2 h) (hρ : Torus.IsCk 2 ρ) (x : Torus d) :
    ∫ y, Torus.laplacian h (x - y) * ρ y = ∫ y, h (x - y) * Torus.laplacian ρ y := by
  have := lt2_ibp (lt3_isCk_refl hh x) hρ
  simp only [lt3_laplacian_refl hh x, reflT] at this
  exact this.symm

/-! #### The truncated kernels -/

theorem lt3_abs_gReg_le {M : ℝ} (hM : 0 ≤ M) {x : Torus d} (hx : x ≠ 0) (s : ℝ) :
    |b15c_gReg d s M x| ≤ |periodicRiesz d s x| := by
  rw [b15c_gReg_of_ne s M hx]
  have h1 := b15c_trunc_le M (periodicRiesz d s x)
  have h2 := b15c_min_le_trunc M (periodicRiesz d s x)
  set u := periodicRiesz d s x
  set t := b15c_trunc M u
  rcases le_or_gt 0 u with hu | hu
  · have : 0 ≤ min u M := le_min hu hM
    rw [abs_of_nonneg (this.trans h2), abs_of_nonneg hu]; exact h1
  · have : min u M = u := min_eq_left (by linarith)
    rw [this] at h2
    have : t = u := le_antisymm h1 h2
    rw [this]

theorem lt3_gReg_tendsto (s : ℝ) {x : Torus d} (hx : x ≠ 0) :
    Tendsto (fun n : ℕ => b15c_gReg d s (n : ℝ) x) atTop (𝓝 (periodicRiesz d s x)) := by
  have h := b15c_gReg_eventuallyEq (d := d) s hx
  have h2 : ∀ᶠ n : ℕ in atTop, b15c_gReg d s (n : ℝ) x = periodicRiesz d s x :=
    tendsto_natCast_atTop_atTop.eventually h
  exact tendsto_const_nhds.congr' (h2.mono fun n hn => hn.symm)

theorem lt3_ae_sub_ne (hd : 0 < d) (x : Torus d) : ∀ᵐ y : Torus d, x - y ≠ 0 :=
  (Measure.measurePreserving_sub_left (volume : Measure (Torus d)) x).quasiMeasurePreserving.ae
    (HRS.KernelAux.torus_ae_ne hd)

theorem lt3_abs_lap_le {ρ : Torus d → ℝ} (hρ : Torus.IsCk 3 ρ) (y : Torus d) :
    |Torus.laplacian ρ y| ≤ d * Torus.cbNorm 3 ρ := by
  unfold Torus.laplacian
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis (Torus.lift ρ)
    (EuclideanSpace.basisFun (Fin d) ℝ)]
  have hb : ∀ i, |iteratedFDeriv ℝ 2 (Torus.lift ρ) (Torus.rep y)
      ![EuclideanSpace.basisFun (Fin d) ℝ i, EuclideanSpace.basisFun (Fin d) ℝ i]| ≤
      Torus.cbNorm 3 ρ := by
    intro i
    have h1 := KernelGrad.norm_iteratedFDeriv_le_cbNorm hρ (j := 2) (by norm_num) (Torus.rep y)
    have h2 := (iteratedFDeriv ℝ 2 (Torus.lift ρ) (Torus.rep y)).le_opNorm
      ![EuclideanSpace.basisFun (Fin d) ℝ i, EuclideanSpace.basisFun (Fin d) ℝ i]
    have h3 : ∏ j : Fin 2, ‖(![EuclideanSpace.basisFun (Fin d) ℝ i,
        EuclideanSpace.basisFun (Fin d) ℝ i] : Fin 2 → Euc d) j‖ = 1 := by
      simp [Fin.prod_univ_two]
    rw [h3, mul_one] at h2
    rw [← Real.norm_eq_abs]
    exact h2.trans h1
  calc |∑ i, iteratedFDeriv ℝ 2 (Torus.lift ρ) (Torus.rep y)
        ![EuclideanSpace.basisFun (Fin d) ℝ i, EuclideanSpace.basisFun (Fin d) ℝ i]|
      ≤ ∑ i, |iteratedFDeriv ℝ 2 (Torus.lift ρ) (Torus.rep y)
        ![EuclideanSpace.basisFun (Fin d) ℝ i, EuclideanSpace.basisFun (Fin d) ℝ i]| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin d, Torus.cbNorm 3 ρ := Finset.sum_le_sum fun i _ => hb i
    _ = d * Torus.cbNorm 3 ρ := by simp

section Estimates

variable (d) in
/-- The Coulomb kernel `g`. -/
abbrev gC : Torus d → ℝ := periodicRiesz d ((d : ℝ) - 2)

theorem lt3_gC_integrable (hd : 2 ≤ d) : Integrable (gC d) := by
  have h2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  exact PDE.MFOneLe.integrable_periodicRiesz (by omega) _ (by linarith) (by linarith)

theorem lt3_gReg_continuous (hd : 2 ≤ d) (M : ℝ) : Continuous (b15c_gReg d ((d : ℝ) - 2) M) := by
  have h2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs := b15c_gReg_isSmooth (d := d) (by omega) (s := (d : ℝ) - 2) (by linarith) (by linarith) M
  have h' : Torus.IsCk ((⊤ : ℕ∞) : WithTop ℕ∞) (b15c_gReg d ((d : ℝ) - 2) M) := hs
  exact PDE.MFAux.continuous_of_isCk (h'.of_le (WithTop.coe_le_coe.2 le_top))

theorem lt3_T_bound (hd : 2 ≤ d) {M : ℝ} (hM : 0 ≤ M) {ρ : Torus d → ℝ} {B : ℝ}
    (hB : ∀ y, |Torus.laplacian ρ y| ≤ B) (x : Torus d) :
    |∫ y, b15c_gReg d ((d : ℝ) - 2) M (x - y) * Torus.laplacian ρ y| ≤ (∫ y, |gC d y|) * B := by
  have hgi := lt3_gC_integrable hd
  have hint : Integrable (fun y => |gC d (x - y)| * B) :=
    ((hgi.norm.comp_sub_left x).mul_const B)
  have h1 := norm_integral_le_of_norm_le hint (f := fun y =>
    b15c_gReg d ((d : ℝ) - 2) M (x - y) * Torus.laplacian ρ y) (by
    filter_upwards [lt3_ae_sub_ne (by omega) x] with y hy
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (lt3_abs_gReg_le hM hy _) (hB y) (abs_nonneg _) (abs_nonneg _))
  rw [Real.norm_eq_abs] at h1
  refine h1.trans (le_of_eq ?_)
  rw [integral_mul_const]
  congr 1
  exact integral_sub_left_eq_self (fun y => |gC d y|) volume x

theorem lt3_T_tendsto (hd : 2 ≤ d) {ρ : Torus d → ℝ} (hρ2 : Torus.IsCk 2 ρ) (x : Torus d) :
    Tendsto (fun n : ℕ => ∫ y, b15c_gReg d ((d : ℝ) - 2) (n : ℝ) (x - y) * Torus.laplacian ρ y)
      atTop (𝓝 (∫ y, gC d (x - y) * Torus.laplacian ρ y)) := by
  have hgi := lt3_gC_integrable hd
  have hlc : Continuous (Torus.laplacian ρ) := PDE.ClassicalAux.continuous_laplacian hρ2
  obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn hlc.continuousOn
  refine tendsto_integral_of_dominated_convergence (fun y => |gC d (x - y)| * max B 0) ?_ ?_ ?_ ?_
  · intro n
    exact ((lt3_gReg_continuous hd (n : ℝ)).comp (continuous_const.sub continuous_id)).mul hlc
      |>.aestronglyMeasurable
  · exact (hgi.norm.comp_sub_left x).mul_const _
  · intro n
    filter_upwards [lt3_ae_sub_ne (by omega) x] with y hy
    rw [Real.norm_eq_abs, abs_mul]
    refine mul_le_mul (lt3_abs_gReg_le (Nat.cast_nonneg n) hy _) ?_ (abs_nonneg _) (abs_nonneg _)
    exact ((hB y (mem_univ _)).trans (le_max_left _ _) : _)
  · filter_upwards [lt3_ae_sub_ne (by omega) x] with y hy
    exact (lt3_gReg_tendsto _ hy).mul_const _

end Estimates

section Pairing

theorem lt3_wd_integral {ρ : Torus d → ℝ} (hρ : IsProbDensity ρ) (f : Torus d → ℝ) :
    ∫ y, f y ∂(withDensityReal ρ) = ∫ y, ρ y * f y := by
  unfold withDensityReal
  rw [integral_withDensity_eq_integral_toReal_smul (f := fun x => ENNReal.ofReal (ρ x))
    (ENNReal.measurable_ofReal.comp hρ.measurable)
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp [ENNReal.toReal_ofReal (hρ.nonneg y)]

/-- Expansion of the off-diagonal pairing of `Δ h` with `μ = ρ dx`, for smooth even-or-not `h`. -/
theorem lt3_pairing_eq (hd : 2 ≤ d) {ρ : Torus d → ℝ} (hρ : IsProbDensity ρ) (hρ2 : Torus.IsCk 2 ρ)
    {h : Torus d → ℝ} (hh : Torus.IsCk 2 h) (X : Config d N) :
    offDiagDiffPairing (Torus.laplacian h) X (withDensityReal ρ) =
      (1 / (N : ℝ) ^ 2) * ∑ i, ∑ j ∈ Finset.univ.erase i,
          (if X i = X j then 0 else Torus.laplacian h (X i - X j))
        - (2 / (N : ℝ)) * ∑ i, (∫ y, h (X i - y) * Torus.laplacian ρ y)
        + ∫ x, ρ x * (∫ y, h (x - y) * Torus.laplacian ρ y) := by
  have hK : ∀ x : Torus d, ∫ y, (if x = y then (0 : ℝ) else Torus.laplacian h (x - y))
      ∂(withDensityReal ρ) = ∫ y, h (x - y) * Torus.laplacian ρ y := by
    intro x
    rw [lt3_wd_integral hρ, ← lt3_ibp_kernel hh hρ2 x]
    refine integral_congr_ae ?_
    filter_upwards [lt3_ae_sub_ne (by omega) x] with y hy
    have : x ≠ y := fun e => hy (by rw [e, sub_self])
    simp [this, mul_comm]
  unfold offDiagDiffPairing offDiagPairing
  simp only [hK]
  rw [lt3_wd_integral hρ]

end Pairing

section Limit

theorem lt3_gReg_isCk2 (hd : 2 ≤ d) (M : ℝ) : Torus.IsCk 2 (b15c_gReg d ((d : ℝ) - 2) M) := by
  have h2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs := b15c_gReg_isSmooth (d := d) (by omega) (s := (d : ℝ) - 2) (by linarith) (by linarith) M
  have h' : Torus.IsCk ((⊤ : ℕ∞) : WithTop ℕ∞) (b15c_gReg d ((d : ℝ) - 2) M) := hs
  exact h'.of_le (WithTop.coe_le_coe.2 le_top)

theorem lt3_T_continuous (hd : 2 ≤ d) {ρ : Torus d → ℝ} (hρ2 : Torus.IsCk 2 ρ) (M : ℝ) :
    Continuous fun x => ∫ y, b15c_gReg d ((d : ℝ) - 2) M (x - y) * Torus.laplacian ρ y := by
  have hlc : Continuous (Torus.laplacian ρ) := PDE.ClassicalAux.continuous_laplacian hρ2
  have hgi : Integrable (b15c_gReg d ((d : ℝ) - 2) M) :=
    (lt3_gReg_continuous hd M).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  exact PDE.MFAux.continuous_convFun hgi hlc

theorem lt3_T_limit (hd : 2 ≤ d) {ρ : Torus d → ℝ} (hρ : IsProbDensity ρ) (hρ2 : Torus.IsCk 2 ρ)
    (x : Torus d) :
    Tendsto (fun n : ℕ => ∫ y, b15c_gReg d ((d : ℝ) - 2) (n : ℝ) (x - y) * Torus.laplacian ρ y)
      atTop (𝓝 (cd d * (1 - ρ x))) := by
  have h := lt3_T_tendsto hd hρ2 x
  have e := (lt2_green_proof hd).2.1 ρ hρ2 x
  rw [hρ.integral_one] at e
  rw [← e]
  exact h

theorem lt3_diffusion_limit_proof (hd : 2 ≤ d) (hN : 0 < N) {ρ : Torus d → ℝ} (hρ : IsProbDensity ρ)
    (hρ2 : Torus.IsCk 2 ρ) {X : Config d N} (hX : X ∉ collisionSet d N) :
    Tendsto (fun n : ℕ => offDiagDiffPairing (Torus.laplacian (b15c_gReg d ((d : ℝ) - 2) (n : ℝ))) X
        (withDensityReal ρ)) atTop (𝓝 (diffLimit d ρ X)) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hcd : 0 < cd d := lt2_cd_pos hd
  set T : ℕ → Torus d → ℝ := fun n x =>
    ∫ y, b15c_gReg d ((d : ℝ) - 2) (n : ℝ) (x - y) * Torus.laplacian ρ y with hT
  have hrw : ∀ n : ℕ, offDiagDiffPairing (Torus.laplacian (b15c_gReg d ((d : ℝ) - 2) (n : ℝ))) X
      (withDensityReal ρ) =
      (1 / (N : ℝ) ^ 2) * ∑ i, ∑ j ∈ Finset.univ.erase i,
          (if X i = X j then 0 else Torus.laplacian (b15c_gReg d ((d : ℝ) - 2) (n : ℝ)) (X i - X j))
        - (2 / (N : ℝ)) * ∑ i, T n (X i) + ∫ x, ρ x * T n x :=
    fun n => lt3_pairing_eq hd hρ hρ2 (lt3_gReg_isCk2 hd (n : ℝ)) X
  simp_rw [hrw]
  -- term 1
  have hsep : ∀ i j : Fin N, i ≠ j → X i ≠ X j := by
    intro i j hij hEq
    exact hX ⟨i, j, hij, hEq⟩
  have h1 : Tendsto (fun n : ℕ => (1 / (N : ℝ) ^ 2) * ∑ i, ∑ j ∈ Finset.univ.erase i,
      (if X i = X j then 0 else
        Torus.laplacian (b15c_gReg d ((d : ℝ) - 2) (n : ℝ)) (X i - X j)))
      atTop (𝓝 ((1 / (N : ℝ) ^ 2) * ∑ i : Fin N, ∑ j ∈ Finset.univ.erase i, cd d)) := by
    refine Tendsto.const_mul _ (tendsto_finset_sum _ fun i _ => tendsto_finset_sum _ fun j hj => ?_)
    have hij : i ≠ j := fun h => (Finset.mem_erase.1 hj).1 h.symm
    have hne : X i ≠ X j := hsep i j hij
    have hpos : 0 < ‖X i - X j‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
    obtain ⟨M₀, hM₀⟩ := lt3_lap_eq_cd hd hpos
    have hev : ∀ᶠ n : ℕ in atTop, (if X i = X j then 0 else
        Torus.laplacian (b15c_gReg d ((d : ℝ) - 2) (n : ℝ)) (X i - X j)) = cd d := by
      filter_upwards [tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop M₀)] with n hn
      rw [if_neg hne]
      exact hM₀ _ hn _ le_rfl
    exact tendsto_const_nhds.congr' (hev.mono fun n hn => hn.symm)
  -- term 2
  have h2 : Tendsto (fun n : ℕ => (2 / (N : ℝ)) * ∑ i, T n (X i)) atTop
      (𝓝 ((2 / (N : ℝ)) * ∑ i, cd d * (1 - ρ (X i)))) :=
    Tendsto.const_mul _ (tendsto_finset_sum _ fun i _ => lt3_T_limit hd hρ hρ2 (X i))
  -- term 3
  have hlc : Continuous (Torus.laplacian ρ) := PDE.ClassicalAux.continuous_laplacian hρ2
  obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn hlc.continuousOn
  have hρc : Continuous ρ := PDE.MFAux.continuous_of_isCk (hρ2.of_le (by norm_num))
  have hint : ∀ {u : Torus d → ℝ}, Continuous u → Integrable u := fun hu =>
    hu.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h3 : Tendsto (fun n : ℕ => ∫ x, ρ x * T n x) atTop
      (𝓝 (∫ x, ρ x * (cd d * (1 - ρ x)))) := by
    refine tendsto_integral_of_dominated_convergence
      (fun x => ρ x * ((∫ y, |gC d y|) * max B 0)) ?_ ?_ ?_ ?_
    · intro n
      exact (hρc.mul (lt3_T_continuous hd hρ2 (n : ℝ))).aestronglyMeasurable
    · exact (hint hρc).mul_const _
    · intro n
      refine Eventually.of_forall fun x => ?_
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hρ.nonneg x)]
      refine mul_le_mul_of_nonneg_left ?_ (hρ.nonneg x)
      exact lt3_T_bound hd (Nat.cast_nonneg n) (fun y => by
        have := hB y (mem_univ _)
        rw [Real.norm_eq_abs] at this
        exact this.trans (le_max_left _ _)) x
    · exact Eventually.of_forall fun x => (lt3_T_limit hd hρ hρ2 x).const_mul _
  have hall := (h1.sub h2).add h3
  convert hall using 2
  -- identify the limit
  have hs1 : ∑ i : Fin N, ∑ j ∈ Finset.univ.erase i, cd d = (N : ℝ) * ((N : ℝ) - 1) * cd d := by
    have : ∀ i : Fin N, ∑ j ∈ Finset.univ.erase i, cd d = ((N : ℝ) - 1) * cd d := by
      intro i
      rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, Nat.cast_sub hN]
      simp
    simp [this]
    ring
  have hs2 : ∑ i, cd d * (1 - ρ (X i)) = cd d * ((N : ℝ) - ∑ i, ρ (X i)) := by
    rw [← Finset.mul_sum, Finset.sum_sub_distrib]
    simp
  have hs3 : ∫ x, ρ x * (cd d * (1 - ρ x)) = cd d * (1 - ∫ x, ρ x ^ 2) := by
    have e : (fun x => ρ x * (cd d * (1 - ρ x))) = fun x => cd d * (ρ x - ρ x ^ 2) := by
      funext x; ring
    have hsub : ∫ x, (ρ x - ρ x ^ 2) = (∫ x, ρ x) - ∫ x, ρ x ^ 2 :=
      integral_sub (hint hρc) (hint (hρc.pow 2))
    rw [e, integral_const_mul, hsub, hρ.integral_one]
  unfold diffLimit
  rw [hs1, hs2, hs3]
  field_simp
  ring

end Limit

section Bound

theorem lt3_diffusion_bound_proof (hd : 2 ≤ d) (Λ : ℝ) {a : ℝ} (ha : 0 < a) :
    ∃ (n₀ : ℕ) (B : ℝ), ∀ n : ℕ, n₀ ≤ n → ∀ (N : ℕ), 0 < N → ∀ ρ : Torus d → ℝ, IsProbDensity ρ →
      Torus.IsCk 3 ρ → Torus.cbNorm 3 ρ ≤ Λ → ∀ X : Config d N, (∀ i j, i ≠ j → a ≤ ‖X i - X j‖) →
        |offDiagDiffPairing (Torus.laplacian (b15c_gReg d ((d : ℝ) - 2) (n : ℝ))) X
          (withDensityReal ρ)| ≤ B := by
  obtain ⟨M₀, hM₀⟩ := lt3_lap_eq_cd hd ha
  have hcd : 0 < cd d := lt2_cd_pos hd
  set Cb : ℝ := ∫ y, |gC d y| with hCb
  have hCb0 : 0 ≤ Cb := integral_nonneg fun y => abs_nonneg _
  refine ⟨⌈M₀⌉₊, cd d + 3 * (Cb * (d * |Λ|)), fun n hn N hN ρ hρ hρ3 hΛ X hX => ?_⟩
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hnM : M₀ ≤ (n : ℝ) := (Nat.le_ceil M₀).trans (by exact_mod_cast hn)
  have hρ2 : Torus.IsCk 2 ρ := hρ3.of_le (by norm_num)
  have hρc : Continuous ρ := PDE.MFAux.continuous_of_isCk (hρ3.of_le (by norm_num))
  rw [lt3_pairing_eq hd hρ hρ2 (lt3_gReg_isCk2 hd (n : ℝ)) X]
  set T : Torus d → ℝ := fun x =>
    ∫ y, b15c_gReg d ((d : ℝ) - 2) (n : ℝ) (x - y) * Torus.laplacian ρ y with hT
  set C : ℝ := Cb * (d * |Λ|) with hC
  have hC0 : 0 ≤ C := by positivity
  have hTb : ∀ x, |T x| ≤ C := by
    intro x
    refine lt3_T_bound hd (Nat.cast_nonneg n) (B := d * |Λ|) (fun y => ?_) x
    have h1 := lt3_abs_lap_le hρ3 y
    have h2 : Torus.cbNorm 3 ρ ≤ |Λ| := hΛ.trans (le_abs_self Λ)
    calc |Torus.laplacian ρ y| ≤ d * Torus.cbNorm 3 ρ := h1
      _ ≤ d * |Λ| := mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg d)
  -- term 1
  have hA : (1 / (N : ℝ) ^ 2) * ∑ i, ∑ j ∈ Finset.univ.erase i,
      (if X i = X j then 0 else
        Torus.laplacian (b15c_gReg d ((d : ℝ) - 2) (n : ℝ)) (X i - X j)) =
      cd d * (1 - 1 / (N : ℝ)) := by
    have : ∀ i : Fin N, ∑ j ∈ Finset.univ.erase i,
        (if X i = X j then 0 else
          Torus.laplacian (b15c_gReg d ((d : ℝ) - 2) (n : ℝ)) (X i - X j)) =
        ((N : ℝ) - 1) * cd d := by
      intro i
      have h1 : ∀ j ∈ Finset.univ.erase i, (if X i = X j then 0 else
          Torus.laplacian (b15c_gReg d ((d : ℝ) - 2) (n : ℝ)) (X i - X j)) = cd d := by
        intro j hj
        have hij : i ≠ j := fun h => (Finset.mem_erase.1 hj).1 h.symm
        have hpos : 0 < ‖X i - X j‖ := ha.trans_le (hX i j hij)
        have hne : X i ≠ X j := sub_ne_zero.1 (norm_pos_iff.1 hpos)
        rw [if_neg hne]
        exact hM₀ _ hnM _ (hX i j hij)
      rw [Finset.sum_congr rfl h1, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i),
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_sub hN]
      simp
    simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hA' : |cd d * (1 - 1 / (N : ℝ))| ≤ cd d := by
    have h1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have h2 : 0 ≤ 1 / (N : ℝ) := by positivity
    have h3 : 1 / (N : ℝ) ≤ 1 := by rw [div_le_one hNr]; exact h1
    rw [abs_of_nonneg (mul_nonneg hcd.le (by linarith))]
    nlinarith
  -- term 2
  have h2 : |(2 / (N : ℝ)) * ∑ i, T (X i)| ≤ 2 * C := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 / (N : ℝ))]
    have : |∑ i, T (X i)| ≤ N * C := by
      calc |∑ i, T (X i)| ≤ ∑ i, |T (X i)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i : Fin N, C := Finset.sum_le_sum fun i _ => hTb _
        _ = N * C := by simp
    calc 2 / (N : ℝ) * |∑ i, T (X i)| ≤ 2 / (N : ℝ) * (N * C) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = 2 * C := by field_simp
  -- term 3
  have hint : ∀ {u : Torus d → ℝ}, Continuous u → Integrable u := fun hu =>
    hu.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h3 : |∫ x, ρ x * T x| ≤ C := by
    have h := norm_integral_le_of_norm_le ((hint hρc).mul_const C) (f := fun x => ρ x * T x)
      (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hρ.nonneg x)]
        exact mul_le_mul_of_nonneg_left (hTb x) (hρ.nonneg x))
    rw [Real.norm_eq_abs, integral_mul_const, hρ.integral_one, one_mul] at h
    exact h
  rw [hA]
  have := abs_add_le (cd d * (1 - 1 / (N : ℝ)) - 2 / (N : ℝ) * ∑ i, T (X i)) (∫ x, ρ x * T x)
  have h4 := abs_sub (cd d * (1 - 1 / (N : ℝ))) (2 / (N : ℝ) * ∑ i, T (X i))
  linarith

end Bound

/-- `𝒟_N^t ≤ 2 c_d ‖μ‖_∞` (M L3147), elementary. -/
theorem lt3_diffLimit_le_proof (hd : 2 ≤ d) (hN : 0 < N) {ρ : Torus d → ℝ} (Λ : ℝ)
    (hρ : ∀ x, ρ x ≤ Λ) (hρ0 : ∀ x, 0 ≤ ρ x) (X : Config d N) :
    diffLimit d ρ X ≤ 2 * cd d * Λ := by
  have hc : 0 < cd d := lt2_cd_pos hd
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 : (1 / (N : ℝ)) * ∑ i, ρ (X i) ≤ Λ := by
    have : ∑ i, ρ (X i) ≤ N * Λ := by
      calc ∑ i, ρ (X i) ≤ ∑ _i : Fin N, Λ := Finset.sum_le_sum fun i _ => hρ _
        _ = N * Λ := by simp
    calc (1 / (N : ℝ)) * ∑ i, ρ (X i) ≤ (1 / (N : ℝ)) * (N * Λ) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = Λ := by field_simp
  have h2 : 0 ≤ ∫ x : Torus d, ρ x ^ 2 := integral_nonneg fun x => sq_nonneg _
  have h3 : 0 ≤ 1 / (N : ℝ) := by positivity
  unfold diffLimit
  have : -(1 / (N : ℝ)) + 2 * ((1 / (N : ℝ)) * ∑ i, ρ (X i)) - ∫ x, ρ x ^ 2 ≤ 2 * Λ := by linarith
  calc cd d * (-(1 / (N : ℝ)) + 2 * ((1 / (N : ℝ)) * ∑ i, ρ (X i)) - ∫ x, ρ x ^ 2)
      ≤ cd d * (2 * Λ) := mul_le_mul_of_nonneg_left this hc.le
    _ = 2 * cd d * Λ := by ring

end HRS.MD.LT337P3
