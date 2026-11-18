import HRS.PDE.MovFAux16
import HRS.PDE.MovAAux19
import HRS.PDE.MovAFinal
import HRS.PDE.MovSXFinal

/-!
# MOVG Aux1: chain plan for `movT_logK_integral` and kernel facts

## Statement and its truth
`movT_logK_integral` (MovSpec3.lean:64).  Checked: for `T < 0` the sets `Icc 0 T` are empty (both clauses trivial); for `T = 0`
the only time is `t = 0` and both sides are `0` (`log K - log K = 0`, `∫_{Icc 0 0} = 0`), so `IsC12Test.time_deriv` being vacuous
there is harmless; for `T > 0` `ρt` is pinned down on `Icc 0 T` by `mova_pde_pointwise` (`ρt = ∑_j ∂_j(ρ u_j)`).  No junk
integrals: every integrand below is shown integrable (`Q` bounded, pair weights dominated by `Ga(z) ‖∇g(z)‖ ∈ L¹`).  TRUE as written.

## Notation
`g = periodicRiesz d s`, `β = D.invβ⁻¹`, `N = n+1 ≥ 2`, `a = β/N`, `G_ρ = g*ρ = convFun g ρ`, `b = β G_ρ`, `π = ρ e^{b}`,
`Ga a z = if z = 0 then 0 else e^{-a g(z)}` (continuous, `0` exactly at `0`, bounded; `Ga a z ‖∇g z‖ ∈ L¹` = `movf_E_integrable`),
`u = mfeTransport D ρ`, `f_j = ρ u_j = mova_fj`, `K = convGradConv ∇g ρ = ∇G_ρ` (`mova_F`),
`q(X) = ∏_{i≠j} Ga(β/2N)(x_i - x_j) · ∏_i π(x_i)`, so that off collisions (a null set, `b15_volume_collisionSet`)
`e^{-βN F_N(X,ρ)} ∏ρ(x_i) = e^{-(βN/2) c₃} q(X)`, `c₃ = ∬ g(x-y) ρρ` (`mova_modEnergy_expand`, `mova_integral_pi_withDensityReal`).

## Chain plan (files MovGAux1..., then MovGFinal)
1. (Aux1) kernel facts: `movg_g_large` (`g → +∞` at `0`), `Ga` continuous / positive off `0` / bounded, `Ga·‖∇g‖` integrable (from
   MovFAux15), translation of integrals on the torus.
2. (Aux2) slice IBP on `𝕋^d`: weight `wt(x) = ∏_k Ga(a)(x - Y_k) e^{b(x)}` (vanishing exactly on `S = {Y_k}`), `C¹` vector field `V`:
   `∫ (div V) wt = ∫ ⟨V, a ∑_k ∇g(x-Y_k) - ∇b⟩ wt`  (MovFAux16 `movf_libp`, MovFAux15 for `∂_j wt ∈ L¹`).
3. (Aux3) configuration slicing: `Fin.insertNth` / `MeasurableEquiv.piFinSuccAbove`, pair-sum decomposition of `q`, and the
   Q-IBP identity `∫ q R(x_i) = ∫ q ⟨u(x_i), a ∑_{k≠i} ∇g(x_i-x_k) - βK(x_i)⟩` for `R = ρt/ρ = div(ρu)/ρ`.
4. (Aux4) one-body identity (OB) with the singular kernel: `convFun g ρt x = ⟨u x, K x⟩ - ob x`,
   `ob x = ∫ ⟨u x - u y, ∇g(x-y)⟩ ρ(y) dy` (absolutely convergent since `u` Lipschitz).  Proof: IBP with the smooth truncations
   `g_M` (`b15c_gReg`, `movsx_grad_gReg`) for the `C¹` field `F^x = ρ(u - u(x))` vanishing at `x`, `M → ∞` by dominated convergence
   (`|∇g||F| ≲ |z|^{-s}`).  Also `∫ G_ρ ρt = -∫ ρ ⟨u,K⟩` (torus IBP) hence `c₃' = -∫ρ ob`.
5. (Aux5) time derivative: `s ↦ G_s(x)`, `c₃(s)`, `K(s) = ∫ Q(s,X) dX` are differentiable on `Ioo 0 T`
   (`hasDerivAt_integral_of_dominated_loc_of_deriv_le`; all `∂_s` are bounded by constants since `ρ, ρt` jointly continuous on the
   compact `[0,T] × 𝕋^d`, `ρ ≥ c₀`, `‖g‖_{L¹} < ∞`, pair weight `≤ const`), `K` continuous on `Icc 0 T`, `K > 0`.
6. (Aux6) algebra: `K'(t) = ∫ Q T_t`, `T_t = ∑_i [β g*ρt + ρt/ρ](x_i) - (βN/2) c₃'`; with steps 3, 4:
   `K'(t) = βN ∫ Q C_N` (the `⟨u,K⟩` terms cancel; `-(βN/2)c₃' = (βN/2)∫ρ ob`; pair part by oddness of `∇g`).
   Hence `(log K)'(t) = βN E_{Q_t}[C_N]` (`mova_integral_modulatedGibbs`) and `|(log K)'| ≤ B/m`.
7. (Final, MovGFinal) FTC `intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le` on `[0,t]` (continuity on `Icc`, derivative on `Ioo`),
   integrability from boundedness + measurability of the derivative; `movT_logK_integral_proof` verbatim, `type_of%` tie.

Prefix `movg_`; no existing file is edited.

Status: steps 1-7 DONE (Aux1-9, MovGFinal); `#print axioms movT_logK_integral_proof` = propext, Classical.choice, Quot.sound.
Aux1 (kernel facts) ... Aux2 (slice IBP) ... Aux3 (config slicing, Q-IBP) ... Aux4 (OB core) ... Aux5 (OB, c₃ identity) ...
Aux6 (time-slice identity) ... Aux7 (K, E_Q via q) ... Aux8 (time derivatives) ... Aux9 (continuity, bounds, Φ').
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

variable {d N : ℕ}

theorem movg_g_large (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (B : ℝ) :
    ∃ η : ℝ, 0 < η ∧ ∀ z : Torus d, z ≠ 0 → Torus.tdist z 0 < η → B ≤ periodicRiesz d s z := by
  obtain ⟨δ, R, hδ, hR, hloc⟩ := movf_local_lower hd hs0 hsd
  have hsing : ∀ᶠ u in 𝓝[>] (0 : ℝ), B + R ≤ (if s = 0 then -Real.log u else u ^ (-s)) := by
    by_cases h0 : s = 0
    · simp only [h0, ite_true]
      exact (Filter.tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero).eventually_ge_atTop _
    · simp only [h0, ite_false]
      have : 0 < s := lt_of_le_of_ne hs0 (Ne.symm h0)
      exact (tendsto_rpow_neg_nhdsGT_zero (by linarith : -s < 0)).eventually_ge_atTop _
  have hev : ∀ᶠ u in 𝓝[>] (0 : ℝ), B + R ≤ (if s = 0 then -Real.log u else u ^ (-s)) ∧ u < δ := by
    refine hsing.and ?_
    exact eventually_nhdsWithin_of_eventually_nhds (gt_mem_nhds hδ)
  obtain ⟨ε, hε, hεP⟩ := Metric.eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1 hev)
  refine ⟨ε, hε, fun z hz hlt => ?_⟩
  have hu0 : 0 < Torus.tdist z 0 := KernelGrad.tdist_pos hz
  have hP := hεP (y := Torus.tdist z 0) (by rw [Real.dist_eq, sub_zero, abs_of_pos hu0]; exact hlt) hu0
  obtain ⟨y, hyz, hybox⟩ := KernelGrad.exists_mk_box z
  have hnorm : ‖y‖ = Torus.tdist z 0 := by rw [← hyz]; exact (KernelGrad.tdist_mk hybox).symm
  have hy0 : y ≠ 0 := by
    intro h; apply hz; rw [← hyz, h]; exact b15c_mk_zero
  have := hloc y hy0 (by rw [hnorm]; exact hP.2)
  rw [hyz, hnorm] at this
  linarith [hP.1]

/-- `g` is continuous at every `z ≠ 0`. -/
theorem movg_g_continuousAt (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {z : Torus d} (hz : z ≠ 0) :
    ContinuousAt (periodicRiesz d s) z := by
  have hy : Torus.mk (Torus.rep z) ≠ 0 := by rw [Torus.mk_rep]; exact hz
  have h1 := (b15c_contDiffAt_lift_periodicRiesz hd hs0 hsd hy).continuousAt
  have h2 := (KernelGrad.isOpenQuotientMap_mk (d := d)).continuousAt_comp_iff
    (g := periodicRiesz d s) (x := Torus.rep z)
  rw [Torus.mk_rep] at h2
  exact h2.1 h1

/-- The pair weight `Ga(z) = e^{-a g(z)}` off `0`, extended by `0` at the collision. -/
def movg_Ga (d : ℕ) (s a : ℝ) (z : Torus d) : ℝ :=
  if z = 0 then 0 else Real.exp (-a * periodicRiesz d s z)

theorem movg_Ga_zero (s a : ℝ) : movg_Ga d s a 0 = 0 := by simp [movg_Ga]

theorem movg_Ga_of_ne {s a : ℝ} {z : Torus d} (hz : z ≠ 0) :
    movg_Ga d s a z = Real.exp (-a * periodicRiesz d s z) := by simp [movg_Ga, hz]

theorem movg_Ga_nonneg (s a : ℝ) (z : Torus d) : 0 ≤ movg_Ga d s a z := by
  unfold movg_Ga; split_ifs
  · exact le_rfl
  · exact (Real.exp_pos _).le

theorem movg_Ga_pos {s a : ℝ} {z : Torus d} (hz : z ≠ 0) : 0 < movg_Ga d s a z := by
  rw [movg_Ga_of_ne hz]; exact Real.exp_pos _

theorem movg_Ga_neg (s a : ℝ) (z : Torus d) : movg_Ga d s a (-z) = movg_Ga d s a z := by
  by_cases hz : z = 0
  · subst hz; simp
  · have : -z ≠ 0 := neg_ne_zero.mpr hz
    rw [movg_Ga_of_ne this, movg_Ga_of_ne hz, periodicRiesz_neg]

theorem movg_Ga_mul_neg (s a : ℝ) (z : Torus d) :
    movg_Ga d s a z * movg_Ga d s a (-z) = movg_Ga d s (2 * a) z := by
  by_cases hz : z = 0
  · subst hz; simp [movg_Ga_zero]
  · rw [movg_Ga_neg, movg_Ga_of_ne hz, movg_Ga_of_ne hz, ← Real.exp_add]
    congr 1; ring

theorem movg_Ga_le {s a B : ℝ} (ha : 0 ≤ a) (hg : ∀ z : Torus d, -B ≤ periodicRiesz d s z) (z : Torus d) :
    movg_Ga d s a z ≤ Real.exp (a * B) := by
  by_cases hz : z = 0
  · subst hz; rw [movg_Ga_zero]; exact (Real.exp_pos _).le
  · rw [movg_Ga_of_ne hz]
    refine Real.exp_le_exp.2 ?_
    have := hg z
    nlinarith

theorem movg_Ga_continuous (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a : ℝ} (ha : 0 < a) :
    Continuous (movg_Ga d s a) := by
  rw [continuous_iff_continuousAt]
  intro z0
  by_cases hz : z0 = 0
  · subst hz
    rw [ContinuousAt, movg_Ga_zero, Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨η, hη, hηg⟩ := movg_g_large hd hs0 hsd (-Real.log (ε / 2) / a)
    have hct : ContinuousAt (fun z : Torus d => KernelGrad.tdist z 0) 0 :=
      CoercAux.continuous_tdist_zero.continuousAt
    have hev : ∀ᶠ z : Torus d in 𝓝 0, KernelGrad.tdist z 0 < η := by
      have h0 : KernelGrad.tdist (0 : Torus d) 0 = 0 := CoercAux.tdist_self 0
      exact hct.eventually (gt_mem_nhds (by show KernelGrad.tdist (0 : Torus d) 0 < η; rw [h0]; exact hη))
    filter_upwards [hev] with z hz
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (movg_Ga_nonneg s a z)]
    by_cases hz0 : z = 0
    · subst hz0; rw [movg_Ga_zero]; exact hε
    · rw [movg_Ga_of_ne hz0]
      have h1 := hηg z hz0 hz
      have h2 : -Real.log (ε / 2) / a ≤ periodicRiesz d s z := h1
      have h3 : -Real.log (ε / 2) ≤ a * periodicRiesz d s z := by
        rw [div_le_iff₀ ha] at h2; linarith
      calc Real.exp (-a * periodicRiesz d s z) ≤ Real.exp (Real.log (ε / 2)) :=
            Real.exp_le_exp.2 (by linarith)
        _ = ε / 2 := Real.exp_log (by linarith)
        _ < ε := by linarith
  · have hev : movg_Ga d s a =ᶠ[𝓝 z0] fun z => Real.exp (-a * periodicRiesz d s z) := by
      filter_upwards [isOpen_ne.mem_nhds hz] with z hz'
      exact movg_Ga_of_ne hz'
    refine ContinuousAt.congr ?_ hev.symm
    exact (Real.continuous_exp.continuousAt).comp ((continuousAt_const.mul (movg_g_continuousAt hd hs0 hsd hz)))

theorem movg_Ga_grad_integrable (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a : ℝ} (ha : 0 < a) :
    Integrable (fun z : Torus d => movg_Ga d s a z * ‖periodicRieszGrad d s z‖) := by
  refine (movf_E_integrable hd hs0 hsd ha).congr ?_
  filter_upwards [KernelGrad.torus_ae_ne' (by omega : 0 < d)] with z hz
  rw [movg_Ga_of_ne hz]

/-! ### Derivatives of lifts (no regularity needed) -/

theorem movg_mk_sub (x y : Euc d) : Torus.mk (x - y) = Torus.mk x - Torus.mk y := by
  funext i
  simp [Torus.mk]

theorem movg_exists_lattice {x y : Euc d} (h : Torus.mk x = Torus.mk y) :
    ∃ n : Lattice d, x = y + Lattice.toEuc n := by
  have : ∀ i, ∃ m : ℤ, x i = y i + m := by
    intro i
    have h1 : ((x i : ℝ) : UnitAddCircle) = ((y i : ℝ) : UnitAddCircle) := congrFun h i
    have h2 := (QuotientAddGroup.eq (a := x i) (b := y i)).1 h1
    obtain ⟨m, hm⟩ := AddSubgroup.mem_zmultiples_iff.1 h2
    refine ⟨-m, ?_⟩
    simp at hm
    push_cast
    linarith
  choose n hn using this
  refine ⟨n, ?_⟩
  ext i
  simp [Lattice.toEuc, hn i]

theorem movg_fderiv_lift_mk (u : Torus d → ℝ) {p q : Euc d} (h : Torus.mk p = Torus.mk q) :
    fderiv ℝ (Torus.lift u) p = fderiv ℝ (Torus.lift u) q := by
  obtain ⟨n, rfl⟩ := movg_exists_lattice h
  rw [← fderiv_comp_add_right]
  congr 1
  funext z
  exact Torus.lift_periodic u z n

theorem movg_partialDeriv_mk (j : Fin d) (u : Torus d → ℝ) (p : Euc d) :
    Torus.partialDeriv j u (Torus.mk p) = fderiv ℝ (Torus.lift u) p (EuclideanSpace.single j 1) := by
  unfold Torus.partialDeriv
  rw [movg_fderiv_lift_mk u (Torus.mk_rep (Torus.mk p))]

end HRS
