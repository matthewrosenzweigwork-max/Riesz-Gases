import HRS.MS.Fp81S21EnergyIdentity

/-!
# Fp81 S2.1(iii), packet 4: reversed-time energy identity

This file differentiates the response energy along the reversed moving adjoint.  The stationary
part is identified through the classical response-generator formula; the remaining term is the
covariance pairing with the difference of the moving and thermal generators.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS (Euc)
open HRS.Whole
open HRS.MS.R26T3
open HRS.MS.S111X2

private theorem sol13_toLp_add {d : ℕ} {μ : Measure (Euc d)}
    {f g : Euc d → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    s111x2_toLp μ (f + g) = s111x2_toLp μ f + s111x2_toLp μ g := by
  apply Lp.ext
  filter_upwards [s111x2_toLp_ae (hf.add hg), s111x2_toLp_ae hf, s111x2_toLp_ae hg,
    Lp.coeFn_add (s111x2_toLp μ f) (s111x2_toLp μ g)] with x hsum hf' hg' hadd
  calc
    (s111x2_toLp μ (f + g) : Euc d → ℝ) x = (f + g) x := hsum
    _ = ((s111x2_toLp μ f : Euc d → ℝ) x + (s111x2_toLp μ g : Euc d → ℝ) x) := by
      change f x + g x = (s111x2_toLp μ f : Euc d → ℝ) x +
        (s111x2_toLp μ g : Euc d → ℝ) x
      rw [← hf', ← hg']
    _ = (((s111x2_toLp μ f : Euc d → ℝ) + (s111x2_toLp μ g : Euc d → ℝ)) x) := by
      rw [Pi.add_apply]
    _ = ((s111x2_toLp μ f + s111x2_toLp μ g : Lp ℝ 2 μ) : Euc d → ℝ) x := by
      exact hadd.symm

private theorem sol13_toLp_eta {d : ℕ} {μ : Measure (Euc d)}
    {f : Euc d → ℝ} (hf : MemLp f 2 μ) :
    s111x2_toLp μ (fun x => f x) = s111x2_toLp μ f := by
  apply Lp.ext
  filter_upwards [s111x2_toLp_ae hf, s111x2_toLp_ae hf] with x h₁ h₂
  exact h₁.trans h₂.symm

private theorem sol13_susc_add_right {d : ℕ} {g : Euc d → ℝ}
    {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {β : ℝ}
    {K : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ} {Mg : ℝ}
    (hK : KRep g μ K Mg) (hβ : 0 ≤ β)
    {f h k : Euc d → ℝ} (hf : MemLp f 2 μ) (hh : MemLp h 2 μ) (hk : MemLp k 2 μ) :
    HRS.Whole.susceptibilityCov g μ β f (h + k) =
      HRS.Whole.susceptibilityCov g μ β f h +
        HRS.Whole.susceptibilityCov g μ β f k := by
  rw [s111x2_susc_eq_inner hK hβ hf (hh.add hk), s111x2_susc_eq_inner hK hβ hf hh,
    s111x2_susc_eq_inner hK hβ hf hk]
  rw [sol13_toLp_add hh hk]
  simp only [map_add, inner_add_right]

/-- Exact derivative of the reversed response energy, including the moving-generator correction. -/
theorem sol13_reversed_energy_deriv
    {p : Parameters} {δ H : ℝ} (R : Trajectory p δ)
    (hH : 0 < H) {φ : Euc p.d → ℝ} {u : ℝ → Euc p.d → ℝ}
    (hu : IsClassicalAdjointW (r26t3_coeff R) H φ u)
    {τ : ℝ} (hτ : τ ∈ Ioo 0 H) :
    let μstar := HRS.Whole.withDensityReal R.ρβ
    let D : ℝ → (Euc p.d → ℝ) → Euc p.d → ℝ := fun t f x =>
      generatorW (r26t3_coeff R) t f x -
        generatorW ((quadraticGradientDyn p.d p.s p.a p.β).coeff (fun _ => R.ρβ)) 0 f x
    HasDerivAt
      (fun q => r26t3_energy R (u (H - q)))
      (-2 * (∫ x, ‖gradient (u (H - τ)) x‖ ^ 2 ∂μstar) +
        2 * p.β * HRS.Whole.susceptibilityCov (rieszKernel p.d p.s) μstar p.β
          (u (H - τ)) (D (H - τ) (u (H - τ)))) τ := by
  dsimp only
  let μ := HRS.Whole.withDensityReal R.ρβ
  have hρ : IsThermalEquilibrium p.d p.s p.a p.β R.ρβ := R.thermal
  obtain ⟨M, T⟩ := s111x2_td_of_thermal p.hd p.hs0 p.hs p.ha p.hβ hρ
  letI := HRS.Whole.Q34.isProbabilityMeasure_nu T.prob
  obtain ⟨M₀, c, S, hc, hTc⟩ := HRS.MS.TransOp.s611_tcref_of_thermal
    p.hd p.hs0 (by linarith [p.hs]) p.ha p.hβ hρ
  obtain ⟨Mg, K, hK⟩ := s111x2_krep_of_tcref
    (Nat.le_trans (by decide : 1 ≤ 2) p.hd) p.hs0 (by linarith [p.hs]) hc hTc
  have hRF := s111x2_responseForm hK p.hβ.le le_rfl
  obtain ⟨B0, B1, B2, hB0, hB1, hB2, huB⟩ := HRS.MS.S111X1.classical_bounds hu
  have hτr : H - τ ∈ Ioo (0 : ℝ) H := by
    constructor <;> linarith [hτ.1, hτ.2]
  have hτI : H - τ ∈ Icc (0 : ℝ) H := ⟨hτr.1.le, hτr.2.le⟩
  have huL : ∀ r ∈ Icc (0 : ℝ) H, MemLp (u r) 2 μ := by
    intro r hr
    exact (MemLp.of_bound (hu.c2 r hr).continuous.aestronglyMeasurable B0
      (Filter.Eventually.of_forall fun x => (huB r hr x).1)).mono_exponent le_top
  have huCb : MemCb 2 (u (H - τ)) := by
    refine ⟨hu.c2 (H - τ) hτI, fun j hj => ?_⟩
    obtain ⟨B, hB⟩ := hu.bdd j hj
    refine ⟨B, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact hB (H - τ) hτI x
  obtain ⟨B1', B2', huD⟩ := s111x2_cbD_of_memCb2 huCb
  have huC1 : MemCb 1 (u (H - τ)) :=
    ⟨huCb.1.of_le (by norm_num), fun j hj => huCb.2 j (by omega)⟩
  have hU : MemLp (u (H - τ)) 2 μ := huL (H - τ) hτI
  have hmoveLp : MemLp (generatorW (r26t3_coeff R) (H - τ) (u (H - τ))) 2 μ := by
    obtain ⟨A, hA⟩ := hu.bdd_time_deriv
    have hG := s111x2_lin_memLp T A
    let r : Icc (0 : ℝ) H := ⟨H - τ, hτI.1, hτI.2⟩
    have hmap : Continuous
        (fun x : Euc p.d => (r, x) : Euc p.d → Icc (0 : ℝ) H × Euc p.d) :=
      continuous_const.prodMk continuous_id
    have hjoint : Continuous (fun z : Icc (0 : ℝ) H × Euc p.d =>
        generatorW (r26t3_coeff R) z.1 (u z.1) z.2) := hu.cont_time_deriv
    have hcont' : Continuous (fun x : Euc p.d =>
        generatorW (r26t3_coeff R) r.1 (u r.1) x) := by
      have h := hjoint.comp hmap
      change Continuous (fun x : Euc p.d => generatorW (r26t3_coeff R) r.1 (u r.1) x) at h
      exact h
    have hcont : Continuous (fun x : Euc p.d =>
        generatorW (r26t3_coeff R) (H - τ) (u (H - τ)) x) := by
      simpa [r] using hcont'
    refine hG.mono' hcont.aestronglyMeasurable ?_
    filter_upwards with x
    rw [Real.norm_eq_abs]
    exact hA (H - τ) hτI x
  have hstatLp : MemLp
      (generatorW ((quadraticGradientDyn p.d p.s p.a p.β).coeff (fun _ => R.ρβ)) 0
        (u (H - τ))) 2 μ := by
    exact s111x2_gen_memLp T huD
  let Dτ : Euc p.d → ℝ := fun x =>
    generatorW (r26t3_coeff R) (H - τ) (u (H - τ)) x -
      generatorW ((quadraticGradientDyn p.d p.s p.a p.β).coeff (fun _ => R.ρβ)) 0
        (u (H - τ)) x
  have hDlp : MemLp Dτ 2 μ := by
    exact hmoveLp.sub hstatLp
  have hmoveEq : (fun x => generatorW (r26t3_coeff R) (H - τ) (u (H - τ)) x) =
      (fun x => generatorW ((quadraticGradientDyn p.d p.s p.a p.β).coeff
        (fun _ => R.ρβ)) 0 (u (H - τ)) x) + Dτ := by
    funext x
    dsimp [Dτ]
    ring
  have hstatResp := s111x2_response_generator p.hd p.s p.a p.β p.hs0 p.hs p.ha p.hβ
    R.ρβ hρ (u (H - τ)) (u (H - τ)) huC1 huCb
  have hderLp := sol13_reversed_lp_hasDerivAt R hH hu hτ
  let F : ℝ → Lp ℝ 2 μ := fun q =>
    HRS.Whole.Q34.Pc μ (s111x2_toLp μ (fun x => u (H - q) x))
  let dF : Lp ℝ 2 μ := HRS.Whole.Q34.Pc μ
    (s111x2_toLp μ (fun x => generatorW (r26t3_coeff R) (H - τ) (u (H - τ)) x))
  have hA := (HRS.Whole.Q34.Pc μ).hasFDerivAt.comp_hasDerivAt τ hderLp
  let G : ℝ → Lp ℝ 2 μ := fun q => s111x2_Rm hK.posOp p.hβ.le (F q)
  let dG : Lp ℝ 2 μ := s111x2_Rm hK.posOp p.hβ.le dF
  have hB := (s111x2_Rm hK.posOp p.hβ.le).hasFDerivAt.comp_hasDerivAt τ hA
  have hAB := hA.inner ℝ hB
  let gMoveτ : Euc p.d → ℝ := fun x =>
    generatorW (r26t3_coeff R) (H - τ) (u (H - τ)) x
  have hEquiv :
      (fun q => r26t3_energy R (u (H - q))) =ᶠ[nhds τ]
        fun q => p.β * inner ℝ (F q) (G q) := by
    filter_upwards [Ioo_mem_nhds hτ.1 hτ.2] with q hq
    rw [r26t3_energy]
    have hqI : H - q ∈ Icc (0 : ℝ) H := ⟨by linarith [hq.2], by linarith [hq.1]⟩
    have hqU := huL (H - q) hqI
    have hrep := s111x2_susc_eq_inner hK p.hβ.le hqU hqU
    rw [← sol13_toLp_eta hqU, ← sol13_toLp_eta hqU] at hrep
    simpa [F, G] using congrArg (fun z => p.β * z) hrep
  have hder0 : HasDerivAt (fun q => p.β * inner ℝ (F q) (G q))
      (p.β * (inner ℝ (F τ) dG + inner ℝ dF (G τ))) τ := by
    simpa [F, dF, G, dG, μ, Function.comp_apply] using hAB.const_mul p.β
  have hmoveRep := s111x2_susc_eq_inner hK p.hβ.le hmoveLp hU
  have hUmoveRep := s111x2_susc_eq_inner hK p.hβ.le hU hmoveLp
  have hderEq :
      p.β * (inner ℝ dF (G τ) + inner ℝ (F τ) dG) =
      2 * p.β * HRS.Whole.susceptibilityCov (rieszKernel p.d p.s) μ p.β
        (u (H - τ)) (generatorW (r26t3_coeff R) (H - τ) (u (H - τ))) := by
    change p.β * (inner ℝ
        (HRS.Whole.Q34.Pc μ (s111x2_toLp μ gMoveτ))
        (s111x2_Rm hK.posOp p.hβ.le
          (HRS.Whole.Q34.Pc μ (s111x2_toLp μ (u (H - τ))))) +
        inner ℝ (HRS.Whole.Q34.Pc μ (s111x2_toLp μ (u (H - τ))))
          (s111x2_Rm hK.posOp p.hβ.le
            (HRS.Whole.Q34.Pc μ (s111x2_toLp μ gMoveτ)))) = _
    rw [← hmoveRep, ← hUmoveRep]
    have hs := hRF.symmetry (u (H - τ))
      (generatorW (r26t3_coeff R) (H - τ) (u (H - τ))) hU hmoveLp
    rw [hs]
    ring
  have hsplit := sol13_susc_add_right hK p.hβ.le hU hstatLp hDlp
  have hcov : HRS.Whole.susceptibilityCov (rieszKernel p.d p.s) μ p.β
      (u (H - τ)) (generatorW (r26t3_coeff R) (H - τ) (u (H - τ))) =
      HRS.Whole.susceptibilityCov (rieszKernel p.d p.s) μ p.β (u (H - τ))
        (generatorW ((quadraticGradientDyn p.d p.s p.a p.β).coeff (fun _ => R.ρβ)) 0
          (u (H - τ))) +
      HRS.Whole.susceptibilityCov (rieszKernel p.d p.s) μ p.β (u (H - τ)) Dτ := by
    have hmoveEq' : generatorW (r26t3_coeff R) (H - τ) (u (H - τ)) =
        generatorW ((quadraticGradientDyn p.d p.s p.a p.β).coeff (fun _ => R.ρβ)) 0
          (u (H - τ)) + Dτ := by
      funext x
      exact congrFun hmoveEq x
    rw [hmoveEq']
    exact hsplit
  have henergy : HRS.Whole.susceptibilityCov (rieszKernel p.d p.s) μ p.β
      (u (H - τ)) (generatorW ((quadraticGradientDyn p.d p.s p.a p.β).coeff
        (fun _ => R.ρβ)) 0 (u (H - τ))) =
      -p.β⁻¹ * s111x2_dirichlet μ (u (H - τ)) (u (H - τ)) := hstatResp.2.2.2.2
  have hderValue : p.β * (inner ℝ dF (G τ) + inner ℝ (F τ) dG) =
      -2 * (∫ x, ‖gradient (u (H - τ)) x‖ ^ 2 ∂μ) +
        2 * p.β * HRS.Whole.susceptibilityCov (rieszKernel p.d p.s) μ p.β
          (u (H - τ)) Dτ := by
    rw [hderEq, hcov, henergy]
    have hdir : s111x2_dirichlet μ (u (H - τ)) (u (H - τ)) =
        ∫ x, ‖gradient (u (H - τ)) x‖ ^ 2 ∂μ := by
      unfold s111x2_dirichlet
      simp only [real_inner_self_eq_norm_sq]
    rw [hdir]
    field_simp [p.hβ.ne'] <;> ring
  have hfinal := hder0.congr_of_eventuallyEq hEquiv
  have hderValue' : p.β * (inner ℝ (F τ) dG + inner ℝ dF (G τ)) =
      -2 * (∫ x, ‖gradient (u (H - τ)) x‖ ^ 2 ∂μ) +
        2 * p.β * HRS.Whole.susceptibilityCov (rieszKernel p.d p.s) μ p.β
          (u (H - τ)) Dτ := by
    calc
      p.β * (inner ℝ (F τ) dG + inner ℝ dF (G τ)) =
          p.β * (inner ℝ dF (G τ) + inner ℝ (F τ) dG) := by ring
      _ = _ := by simpa [Dτ, μ, F, dF, G, dG] using hderValue
  exact hfinal.congr_deriv hderValue'

end HRS.Fp81.S21

namespace HRS.Fp81.S21

open HRS (Euc)
open HRS.Whole
open HRS.MS.R26T3
open HRS.MS.S111X2

/-- The reversed response energy is absolutely continuous on the closed time interval. -/
theorem sol13_reversed_energy_ac
    {p : Parameters} {δ H : ℝ} (R : Trajectory p δ)
    (hH : 0 < H) {φ : Euc p.d → ℝ} {u : ℝ → Euc p.d → ℝ}
    (hu : IsClassicalAdjointW (r26t3_coeff R) H φ u) :
    AbsolutelyContinuousOnInterval (fun q => r26t3_energy R (u (H - q))) 0 H := by
  let μ := HRS.Whole.withDensityReal R.ρβ
  have hρ : IsThermalEquilibrium p.d p.s p.a p.β R.ρβ := R.thermal
  obtain ⟨M, T⟩ := s111x2_td_of_thermal p.hd p.hs0 p.hs p.ha p.hβ hρ
  letI := HRS.Whole.Q34.isProbabilityMeasure_nu T.prob
  obtain ⟨M₀, c, S, hc, hTc⟩ := HRS.MS.TransOp.s611_tcref_of_thermal
    p.hd p.hs0 (by linarith [p.hs]) p.ha p.hβ hρ
  obtain ⟨Mg, K, hK⟩ := s111x2_krep_of_tcref
    (Nat.le_trans (by decide : 1 ≤ 2) p.hd) p.hs0 (by linarith [p.hs]) hc hTc
  have hRF := s111x2_responseForm hK p.hβ.le le_rfl
  obtain ⟨B0, B1, B2, hB0, hB1, hB2, huB⟩ := HRS.MS.S111X1.classical_bounds hu
  have hrev : ∀ q ∈ Icc (0 : ℝ) H, H - q ∈ Icc (0 : ℝ) H := by
    intro q hq
    exact ⟨by linarith [hq.2], by linarith [hq.1]⟩
  have huL : ∀ r ∈ Icc (0 : ℝ) H, MemLp (u r) 2 μ := by
    intro r hr
    exact (MemLp.of_bound (hu.c2 r hr).continuous.aestronglyMeasurable B0
      (Filter.Eventually.of_forall fun x => (huB r hr x).1)).mono_exponent le_top
  have hpointCont : ∀ x : Euc p.d,
      ContinuousOn (fun r => u r x) (Icc (0 : ℝ) H) := by
    intro x
    have h0 := hu.cont_c2 0 (by norm_num)
    have h1 : Continuous fun r : Icc (0 : ℝ) H => iteratedFDeriv ℝ 0 (u r) x :=
      h0.comp (continuous_id.prodMk continuous_const)
    have h2 : Continuous fun r : Icc (0 : ℝ) H => u r x := by
      have h := (continuousMultilinearCurryFin0 ℝ (Euc p.d) ℝ).continuous.comp h1
      refine h.congr fun r => ?_
      simp [iteratedFDeriv_zero_eq_comp]
    exact continuousOn_iff_continuous_restrict.2 h2
  have hpointRev : ∀ x : Euc p.d,
      ContinuousOn (fun q => u (H - q) x) (Icc (0 : ℝ) H) := by
    intro x
    exact (hpointCont x).comp
      (by fun_prop : ContinuousOn (fun q : ℝ => H - q) (Icc (0 : ℝ) H)) hrev
  have hLpCont : ∀ q ∈ Icc (0 : ℝ) H,
      ContinuousWithinAt
        (fun v => s111x2_toLp μ (fun x => u (H - v) x)) (Icc 0 H) q := by
    intro q hq
    exact s111x2_lp_continuousWithinAt (μ := μ) (w := fun v x => u (H - v) x) hq
      (fun v hv => huL (H - v) (hrev v hv)) hpointRev
      (G := fun _ : Euc p.d => B0)
      (fun v hv x => by
        have hbound := (huB (H - v) (hrev v hv) x).1
        rw [Real.norm_eq_abs] at hbound
        exact hbound)
      (memLp_const _)
  let F : ℝ → Lp ℝ 2 μ := fun q =>
    HRS.Whole.Q34.Pc μ (s111x2_toLp μ (fun x => u (H - q) x))
  let G : ℝ → Lp ℝ 2 μ := fun q => s111x2_Rm hK.posOp p.hβ.le (F q)
  have hFcont : ∀ q ∈ Icc (0 : ℝ) H, ContinuousWithinAt F (Icc 0 H) q := by
    intro q hq
    exact (HRS.Whole.Q34.Pc μ).continuous.continuousAt.comp_continuousWithinAt
      (hLpCont q hq)
  have hGcont : ∀ q ∈ Icc (0 : ℝ) H, ContinuousWithinAt G (Icc 0 H) q := by
    intro q hq
    exact (s111x2_Rm hK.posOp p.hβ.le).continuous.continuousAt.comp_continuousWithinAt
      (hFcont q hq)
  have hEnergyEq : ∀ q ∈ Icc (0 : ℝ) H,
      r26t3_energy R (u (H - q)) = p.β * inner ℝ (F q) (G q) := by
    intro q hq
    rw [r26t3_energy]
    have hqU := huL (H - q) (hrev q hq)
    have hrep := s111x2_susc_eq_inner hK p.hβ.le hqU hqU
    rw [← sol13_toLp_eta hqU, ← sol13_toLp_eta hqU] at hrep
    simpa [F, G] using congrArg (fun z => p.β * z) hrep
  have hcontEnergy : ContinuousOn
      (fun q => r26t3_energy R (u (H - q))) (Icc (0 : ℝ) H) := by
    have hcontPair : ContinuousOn (fun q => p.β * inner ℝ (F q) (G q)) (Icc 0 H) :=
      fun q hq => (hFcont q hq).inner (hGcont q hq) |>.const_mul p.β
    exact hcontPair.congr hEnergyEq

  let Cstar := (quadraticGradientDyn p.d p.s p.a p.β).coeff (fun _ => R.ρβ)
  obtain ⟨c0, hc0⟩ := T.en.dgrow
  have hc00 : 0 ≤ c0 := by
    have h := hc0 0 (0 : Euc p.d)
    simpa using (norm_nonneg (Cstar.drift 0 0)).trans h
  let L0 : ℝ := (p.d : ℝ) * B2 + p.β * (c0 * B1)
  let L1 : ℝ := p.β * (c0 * B1)
  have hd0 : 0 ≤ (p.d : ℝ) := Nat.cast_nonneg p.d
  have hcB1 : 0 ≤ c0 * B1 := mul_nonneg hc00 hB1
  have hL0 : 0 ≤ L0 := by
    dsimp [L0]
    exact add_nonneg (mul_nonneg hd0 hB2) (mul_nonneg p.hβ.le hcB1)
  have hL1 : 0 ≤ L1 := by
    dsimp [L1]
    exact mul_nonneg p.hβ.le hcB1
  have hcbD : ∀ r ∈ Icc (0 : ℝ) H, CbD (u r) B1 B2 := by
    intro r hr
    refine ⟨hu.c2 r hr, ?_, ?_⟩
    · intro x
      exact (huB r hr x).2.1
    · intro x
      exact (huB r hr x).2.2
  have hLbound : ∀ r ∈ Icc (0 : ℝ) H, ∀ x,
      |s111x2_L R.ρβ (u r) x| ≤ L0 + L1 * ‖x‖ := by
    intro r hr x
    have hC := hcbD r hr
    rw [s111x2_L_eq T (u r) x]
    have hLap := s111x2_laplacian_bound hC x
    have hDrift : |inner ℝ (Cstar.drift 0 x) (gradient (u r) x)| ≤
        c0 * (1 + ‖x‖) * B1 := by
      refine (abs_real_inner_le_norm _ _).trans ?_
      have hgrad : ‖gradient (u r) x‖ ≤ B1 := by
        rw [s111x2_norm_gradient]
        exact hC.d1 x
      exact mul_le_mul (hc0 0 x) hgrad (norm_nonneg _)
        (mul_nonneg hc00 (by positivity))
    calc
      |-Laplacian.laplacian (u r) x - p.β *
          inner ℝ (Cstar.drift 0 x) (gradient (u r) x)|
          ≤ |Laplacian.laplacian (u r) x| +
              p.β * |inner ℝ (Cstar.drift 0 x) (gradient (u r) x)| := by
            refine (abs_sub _ _).trans ?_
            rw [abs_neg, abs_mul, abs_of_pos p.hβ]
      _ ≤ (p.d : ℝ) * B2 + p.β * (c0 * (1 + ‖x‖) * B1) :=
            add_le_add hLap (mul_le_mul_of_nonneg_left hDrift p.hβ.le)
      _ = L0 + L1 * ‖x‖ := by dsimp [L0, L1]; ring
  let Knl : ℝ := B1 * HRS.MS.S111X1.kA p.d p.s M R.ρβ
  have hNbound : ∀ r ∈ Icc (0 : ℝ) H, ∀ x,
      |HRS.MS.S111X1.Nnl p.d p.s R.ρβ (gradient (u r)) x| ≤ Knl := by
    intro r hr x
    exact (s111x2_N_facts T (hcbD r hr)).2 x
  have hKnl : 0 ≤ Knl := by
    have h := hNbound H ⟨hH.le, le_rfl⟩ 0
    dsimp [Knl] at h ⊢
    exact (abs_nonneg _).trans h
  let Kbase : ℝ := p.β⁻¹ * (L0 + L1) + Knl
  have hKbase : 0 ≤ Kbase := by
    dsimp [Kbase]
    exact add_nonneg
      (mul_nonneg (inv_pos.mpr p.hβ).le (add_nonneg hL0 hL1)) hKnl
  have hBaseBound : ∀ r ∈ Icc (0 : ℝ) H, ∀ x,
      |generatorW Cstar 0 (u r) x| ≤ Kbase * (1 + ‖x‖) := by
    intro r hr x
    have hC := hcbD r hr
    have hGenEq := congrFun (s111x2_gen_eq T hC) x
    have hN := hNbound r hr x
    have hL := hLbound r hr x
    calc
      |generatorW Cstar 0 (u r) x| =
          |-p.β⁻¹ * s111x2_L R.ρβ (u r) x +
            HRS.MS.S111X1.Nnl p.d p.s R.ρβ (gradient (u r)) x| := by
              rw [hGenEq]
      _ ≤ p.β⁻¹ * |s111x2_L R.ρβ (u r) x| +
            |HRS.MS.S111X1.Nnl p.d p.s R.ρβ (gradient (u r)) x| := by
              calc
                _ ≤ |-p.β⁻¹ * s111x2_L R.ρβ (u r) x| +
                    |HRS.MS.S111X1.Nnl p.d p.s R.ρβ (gradient (u r)) x| := abs_add_le _ _
                _ = _ := by rw [abs_mul, abs_neg, abs_of_pos (inv_pos.mpr p.hβ)]
      _ ≤ p.β⁻¹ * (L0 + L1 * ‖x‖) + Knl := by
            exact add_le_add
              (mul_le_mul_of_nonneg_left hL (inv_pos.mpr p.hβ).le)
              (by dsimp [Knl]; exact hN)
      _ ≤ Kbase * (1 + ‖x‖) := by
            have hfac : L0 + L1 * ‖x‖ ≤ (L0 + L1) * (1 + ‖x‖) := by
              nlinarith [hL0, hL1, norm_nonneg x]
            calc
              p.β⁻¹ * (L0 + L1 * ‖x‖) + Knl ≤
                  p.β⁻¹ * ((L0 + L1) * (1 + ‖x‖)) + Knl := by
                    exact add_le_add
                      (mul_le_mul_of_nonneg_left hfac (inv_pos.mpr p.hβ).le) le_rfl
              _ ≤ p.β⁻¹ * ((L0 + L1) * (1 + ‖x‖)) +
                    Knl * (1 + ‖x‖) := by
                    have hx : (1 : ℝ) ≤ 1 + ‖x‖ := by
                      linarith [norm_nonneg x]
                    have hKnlx : Knl ≤ Knl * (1 + ‖x‖) := by
                      calc
                        Knl = Knl * 1 := by ring
                        _ ≤ Knl * (1 + ‖x‖) := mul_le_mul_of_nonneg_left hx hKnl
                    exact add_le_add le_rfl
                      hKnlx
              _ = Kbase * (1 + ‖x‖) := by dsimp [Kbase]; ring
  obtain ⟨A, hA⟩ := hu.bdd_time_deriv
  have hA_nonneg : 0 ≤ A := by
    have h := hA 0 ⟨le_rfl, hH.le⟩ (0 : Euc p.d)
    norm_num at h
    exact (abs_nonneg _).trans h
  let Genv : Euc p.d → ℝ := fun x => (A + Kbase) * (1 + ‖x‖)
  have hGenv : MemLp Genv 2 μ := by
    simpa [Genv] using s111x2_lin_memLp T (A + Kbase)
  have hDgrowth : ∀ q ∈ Icc (0 : ℝ) H, ∀ x,
      |generatorW (r26t3_coeff R) (H - q) (u (H - q)) x -
        generatorW Cstar 0 (u (H - q)) x| ≤ Genv x := by
    intro q hq x
    have htime := hrev q hq
    calc
      _ ≤ |generatorW (r26t3_coeff R) (H - q) (u (H - q)) x| +
            |generatorW Cstar 0 (u (H - q)) x| := abs_sub _ _
      _ ≤ A * (1 + ‖x‖) + Kbase * (1 + ‖x‖) := by
            exact add_le_add (hA (H - q) htime x) (hBaseBound (H - q) htime x)
      _ = Genv x := by dsimp [Genv]; ring
  have hDmem : ∀ q ∈ Icc (0 : ℝ) H,
      MemLp (fun x => generatorW (r26t3_coeff R) (H - q) (u (H - q)) x -
        generatorW Cstar 0 (u (H - q)) x) 2 μ := by
    intro q hq
    have hmove : MemLp (fun x => generatorW (r26t3_coeff R) (H - q) (u (H - q)) x) 2 μ := by
      have hdom : ∀ x, |generatorW (r26t3_coeff R) (H - q) (u (H - q)) x| ≤
          A * (1 + ‖x‖) := hA (H - q) (hrev q hq)
      let r : Icc (0 : ℝ) H := ⟨H - q, (hrev q hq).1, (hrev q hq).2⟩
      have hmap : Continuous
          (fun x : Euc p.d => (r, x) : Euc p.d → Icc (0 : ℝ) H × Euc p.d) :=
        continuous_const.prodMk continuous_id
      have hjoint : Continuous (fun z : Icc (0 : ℝ) H × Euc p.d =>
          generatorW (r26t3_coeff R) z.1 (u z.1) z.2) := hu.cont_time_deriv
      have hcont' : Continuous (fun x : Euc p.d =>
          generatorW (r26t3_coeff R) r.1 (u r.1) x) := by
        have h := hjoint.comp hmap
        change Continuous (fun x : Euc p.d => generatorW (r26t3_coeff R) r.1 (u r.1) x) at h
        exact h
      have hcont : Continuous (fun x : Euc p.d =>
          generatorW (r26t3_coeff R) (H - q) (u (H - q)) x) := by
        simpa [r] using hcont'
      refine (s111x2_lin_memLp T A).mono' hcont.aestronglyMeasurable ?_
      filter_upwards with x
      rw [Real.norm_eq_abs]
      exact hdom x
    have hstat : MemLp (fun x => generatorW Cstar 0 (u (H - q)) x) 2 μ :=
      s111x2_gen_memLp T (hcbD (H - q) (hrev q hq))
    exact hmove.sub hstat
  let Kder : ℝ := 2 * B1 ^ 2 +
    2 * p.β * B0 * Real.sqrt (∫ x, Genv x ^ 2 ∂μ)
  have hIntG : 0 ≤ ∫ x, Genv x ^ 2 ∂μ := integral_nonneg (fun x => sq_nonneg _)
  have hKder : 0 ≤ Kder := by
    dsimp [Kder]
    apply add_nonneg
    · positivity
    · exact mul_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) p.hβ.le) hB0)
        (Real.sqrt_nonneg _)
  have hderBound : ∀ q ∈ Ioo (0 : ℝ) H,
      |(-2 * (∫ x, ‖gradient (u (H - q)) x‖ ^ 2 ∂μ) +
        2 * p.β * HRS.Whole.susceptibilityCov (rieszKernel p.d p.s) μ p.β
          (u (H - q)) (fun x => generatorW (r26t3_coeff R) (H - q) (u (H - q)) x -
            generatorW Cstar 0 (u (H - q)) x))| ≤ Kder := by
    intro q hq
    have htime : H - q ∈ Icc (0 : ℝ) H := ⟨by linarith [hq.2], by linarith [hq.1]⟩
    let f : Euc p.d → ℝ := u (H - q)
    let Dq : Euc p.d → ℝ := fun x =>
      generatorW (r26t3_coeff R) (H - q) (u (H - q)) x -
        generatorW Cstar 0 (u (H - q)) x
    have hf : MemLp f 2 μ := huL (H - q) htime
    have hqcc : q ∈ Icc (0 : ℝ) H := ⟨hq.1.le, hq.2.le⟩
    have hD : MemLp Dq 2 μ := by
      simpa [Dq] using hDmem q hqcc
    have hcentF : s111x2_centeredSquare μ f ≤ B0 ^ 2 := by
      have hcs := s111x2_cs_le_sq hf
      have hsqInt : ∫ x, f x ^ 2 ∂μ ≤ B0 ^ 2 := by
        have hconst : Integrable (fun _ : Euc p.d => B0 ^ 2) μ := integrable_const _
        have hmono : ∀ᵐ x ∂μ, f x ^ 2 ≤ B0 ^ 2 := by
          filter_upwards with x
          have hfx : |f x| ≤ B0 := by
            have := huB (H - q) htime x |>.1
            rwa [Real.norm_eq_abs] at this
          have hsquare : |f x| ^ 2 ≤ B0 ^ 2 := by
            calc
              |f x| ^ 2 = |f x| * |f x| := by ring
              _ ≤ B0 * B0 := mul_le_mul hfx hfx (abs_nonneg _) hB0
              _ = B0 ^ 2 := by ring
          calc
            f x ^ 2 = |f x| ^ 2 := (sq_abs _).symm
            _ ≤ B0 ^ 2 := hsquare
        calc
          ∫ x, f x ^ 2 ∂μ ≤ ∫ x, B0 ^ 2 ∂μ :=
            integral_mono_ae hf.integrable_sq hconst hmono
          _ = B0 ^ 2 := by simp
      exact hcs.trans hsqInt
    have hcentD : s111x2_centeredSquare μ Dq ≤ ∫ x, Genv x ^ 2 ∂μ := by
      calc
        s111x2_centeredSquare μ Dq ≤ ∫ x, Dq x ^ 2 ∂μ := s111x2_cs_le_sq hD
        _ ≤ ∫ x, Genv x ^ 2 ∂μ := by
          refine integral_mono_ae hD.integrable_sq hGenv.integrable_sq ?_
          filter_upwards with x
          have hG0 : 0 ≤ Genv x := mul_nonneg (add_nonneg hA_nonneg hKbase) (by positivity)
          have hpow := pow_le_pow_left₀ (abs_nonneg (Dq x)) (hDgrowth q hqcc x) 2
          have hsq : Dq x ^ 2 = |Dq x| ^ 2 := (sq_abs _).symm
          rw [hsq]
          exact hpow
    have hsqrtF : Real.sqrt (s111x2_centeredSquare μ f) ≤ B0 := by
      calc
        Real.sqrt (s111x2_centeredSquare μ f) ≤ Real.sqrt (B0 ^ 2) := Real.sqrt_le_sqrt hcentF
        _ = B0 := Real.sqrt_sq hB0
    have hsqrtD : Real.sqrt (s111x2_centeredSquare μ Dq) ≤
        Real.sqrt (∫ x, Genv x ^ 2 ∂μ) := Real.sqrt_le_sqrt hcentD
    have hcov := hRF.schwarz f Dq hf hD
    have hcovBound : |HRS.Whole.susceptibilityCov (rieszKernel p.d p.s) μ p.β f Dq| ≤
        B0 * Real.sqrt (∫ x, Genv x ^ 2 ∂μ) := by
      calc
        _ ≤ Real.sqrt (s111x2_centeredSquare μ f) *
            Real.sqrt (s111x2_centeredSquare μ Dq) := hcov
        _ ≤ B0 * Real.sqrt (∫ x, Genv x ^ 2 ∂μ) := by
          exact mul_le_mul hsqrtF hsqrtD (Real.sqrt_nonneg _) hB0
    have hdirEq : s111x2_dirichlet μ f f =
        ∫ x, ‖gradient f x‖ ^ 2 ∂μ := by
      unfold s111x2_dirichlet
      simp only [real_inner_self_eq_norm_sq]
    have hgradBound : ∀ x, ‖gradient f x‖ ≤ B1 := by
      intro x
      rw [s111x2_norm_gradient]
      exact (huB (H - q) htime x).2.1
    have hderivBound : ∀ x, ‖fderiv ℝ f x‖ ≤ B1 := by
      intro x
      rw [← s111x2_norm_gradient]
      exact hgradBound x
    have hdirBound : |s111x2_dirichlet μ f f| ≤ B1 ^ 2 :=
      by simpa [pow_two] using s111x2_dirichlet_bound T hderivBound hderivBound
    rw [← hdirEq]
    have hβ2 : 0 < 2 * p.β := by positivity [p.hβ]
    calc
      _ ≤ |-2 * s111x2_dirichlet μ f f| +
          |2 * p.β * HRS.Whole.susceptibilityCov (rieszKernel p.d p.s) μ p.β f Dq| :=
            abs_add_le _ _
      _ = 2 * |s111x2_dirichlet μ f f| +
          (2 * p.β) * |HRS.Whole.susceptibilityCov (rieszKernel p.d p.s) μ p.β f Dq| := by
            rw [abs_mul, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 2),
              abs_mul, abs_of_pos hβ2]
      _ ≤ 2 * B1 ^ 2 + 2 * p.β * B0 * Real.sqrt (∫ x, Genv x ^ 2 ∂μ) := by
            nlinarith [hdirBound, hcovBound]
      _ = Kder := by rfl
  have hder : ∀ q ∈ Ioo (0 : ℝ) H,
      HasDerivAt (fun v => r26t3_energy R (u (H - v)))
        (-2 * (∫ x, ‖gradient (u (H - q)) x‖ ^ 2 ∂μ) +
          2 * p.β * HRS.Whole.susceptibilityCov (rieszKernel p.d p.s) μ p.β
            (u (H - q)) (fun x => generatorW (r26t3_coeff R) (H - q) (u (H - q)) x -
              generatorW Cstar 0 (u (H - q)) x)) q := by
    intro q hq
    simpa [μ, Cstar] using sol13_reversed_energy_deriv R hH hu hq
  exact s111x2_ac_of_deriv_bdd hH hcontEnergy hder hderBound

end HRS.Fp81.S21

#print axioms HRS.Fp81.S21.sol13_reversed_energy_deriv
#print axioms HRS.Fp81.S21.sol13_reversed_energy_ac
