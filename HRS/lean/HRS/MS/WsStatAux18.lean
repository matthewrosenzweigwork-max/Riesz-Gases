import HRS.MS.WsStatAux17

/-!
# S21 packet F3d: the centred initial state and the centred remainder

For the stationary particle system with `nubar = meanEmpirical (law X_0)`:

* `s21K0c`: the centred initial `K`-state `s56k0 C m T sigma (empirical X_0) nubar` (coordinates
  `sigma (pair emp_0 U^{0,t} phi_alpha - pair nubar U^{0,t} phi_alpha)`, `s21_k0_eval_gen2`);
* `s21Xi`: the exactly centred field `sigma (mu_N^t - nubar)`;
* `s21Rt = s21Xi - A(s21K0c) - T M`: the centred remainder (continuous, measurable).

`s21_k0_eval_gen2` generalises `s21_k0_eval_gen` (packet F3a) to an arbitrary probability measure in place of the thermal density.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace HRS.MS.S21

open HRS.Whole HRS.MS.GenPath HRS.MP.RdRem
open HRS (Euc)

variable {d : ℕ}

theorem s21_k0_eval_gen2 (b : WholeBounds d) (hbv : b.Valid) (S : WholeSetup b) (N : ℕ)
    (hC : OscAdjointInput (S.coeff N) b.m b.T) (σ : ℝ) (ν μρ : Measure (Euc d))
    [IsProbabilityMeasure ν] [IsProbabilityMeasure μρ]
    (hν : Integrable (fun x : Euc d => ‖x‖) ν) (hμ : Integrable (fun x : Euc d => ‖x‖) μρ)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) b.T) (α : MultiIndex d) :
    OscDual.coord ((s56k0 (S.coeff N) b.m b.T σ ν μρ).evalA t) α =
      σ * (HRS.Whole.pair ν (propagatorW (S.coeff N) 0 t (oscTestFun b.m α)) -
        HRS.Whole.pair μρ (propagatorW (S.coeff N) 0 t (oscTestFun b.m α))) := by
  have hT : 0 ≤ b.T := hbv.hT.le
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) b.T := ⟨le_rfl, hT⟩
  obtain ⟨Cf, hCf⟩ := HRS.MS.Star.general_orbits_features_proof b hbv
  have hbd : ∀ (a : Fin d) (z : Euc d), ‖gradFeature (S.coeff N) b.m b.T a 0 z‖ ≤ |Cf| := fun a z => by
    have := (hCf S N a 0 h0).2 0 (Nat.zero_le _) z
    rw [norm_iteratedFDeriv_zero] at this
    exact this.trans (le_abs_self _)
  have hmeas : ∀ a : Fin d, Measurable fun z : Euc d => gradFeature (S.coeff N) b.m b.T a 0 z := by
    intro a
    have := (s56_feat_meas b hbv S N hC a).comp (measurable_const (a := (0 : ℝ)).prodMk measurable_id)
    have e := mrrClamp_of_mem h0
    simp only [Function.comp_def, e] at this
    exact this
  have hcl := s56_osc_classical b hbv S N ht α
  obtain ⟨B, hB⟩ := hcl.bdd 0 (Nat.zero_le _)
  have hh : ContDiff ℝ 1 (propagatorW (S.coeff N) 0 t (oscTestFun b.m α)) :=
    (hcl.c2 0 ⟨le_rfl, ht.1⟩).of_le (by norm_num)
  rw [HRS.MS.S52.s52_coord_evalA ht.1 ht.2]
  rw [s56_k0_inner (S.coeff N) b.m b.T σ |Cf| (abs_nonneg _) hmeas hbd ν μρ hν hμ
    (HRS.MS.S52.s52y1 b.m b.T t α)
    (propagatorW (S.coeff N) 0 t (oscTestFun b.m α)) hh B
    (fun z => by
      have := hB 0 ⟨le_rfl, ht.1⟩ z
      rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this)
    (fun a z => by
      rw [HRS.MS.S52.s52_pair_grad_y1 hC ht.2 a h0 z α]
      simp [ht.1])]
  rfl

end HRS.MS.S21
