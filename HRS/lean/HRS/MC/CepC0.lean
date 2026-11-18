import HRS.Stochastic.Particle

/-!
# Packet CEPC0: locally Lipschitz lifted drift under a `C^{1,1}` potential

Copy-adapted from `HRS.contDiffOn_liftedDrift` / `HRS.liftedDrift_locLipschitz`
(`HRS/Stochastic/Particle.lean`): the pair part is `C¹` on `liftedFree`, the potential part
`Y ↦ (∇V (Y i))_i` is globally Lipschitz.  The predicate `cep_IsC11` is duplicated from
`HRS/MC/CepaSpec.lean` (same body) so that this file does not import the spec file.
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.CepC0

open HRS

/-- `V` is `C¹` with Lipschitz gradient on the covering line.  Same body as
`HRS.MC.Cepa.cep_IsC11`; duplicated so that this packet does not import the spec file. -/
def cep_IsC11 {d : ℕ} (V : Torus d → ℝ) : Prop :=
  Torus.IsCk 1 V ∧ ∃ L : ℝ≥0, LipschitzWith L (gradient (Torus.lift V))

variable {d N : ℕ}

/-- The pair part of the lifted drift. -/
def cepc0_pair (D : DynData d) (Y : Fin N → Euc d) : Fin N → Euc d := fun i =>
  (1 / (N : ℝ)) • ∑ j ∈ Finset.univ.erase i,
    Torus.matVec D.M (Torus.lift (periodicRieszGrad d D.s) (Y i - Y j))

/-- The potential part of the lifted drift. -/
def cepc0_pot (D : DynData d) (Y : Fin N → Euc d) : Fin N → Euc d := fun i =>
  gradient (Torus.lift D.V) (Y i)

theorem cepc0_drift_eq (D : DynData d) (Y : Fin N → Euc d) :
    liftedDrift D Y = cepc0_pair D Y - cepc0_pot D Y := by
  funext i
  rw [liftedDrift_apply]
  rfl

theorem cepc0_contDiffOn_pair (D : DynData d)
    (hK : Torus.IsSmoothOffZero (periodicRieszGrad d D.s)) :
    ContDiffOn ℝ 1 (cepc0_pair (N := N) D) (liftedFree d N) := by
  have hK1 : ContDiffOn ℝ 1 (Torus.lift (periodicRieszGrad d D.s)) {x : Euc d | Torus.mk x ≠ 0} :=
    hK.of_le (by exact_mod_cast le_top)
  have hMv : ContDiff ℝ 1 (Torus.matVec D.M) :=
    (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin D.M)).contDiff
  refine contDiffOn_pi.2 fun i => ?_
  show ContDiffOn ℝ 1 (fun Y : Fin N → Euc d => (1 / (N : ℝ)) • ∑ j ∈ Finset.univ.erase i,
        Torus.matVec D.M (Torus.lift (periodicRieszGrad d D.s) (Y i - Y j))) (liftedFree d N)
  refine ContDiffOn.const_smul _ (ContDiffOn.sum fun j hj => ?_)
  have hij : i ≠ j := fun h => (Finset.mem_erase.1 hj).1 h.symm
  refine hMv.comp_contDiffOn (hK1.comp (f := fun Y : Fin N → Euc d => Y i - Y j) ?_ ?_)
  · exact ((contDiff_apply ℝ (Euc d) i).sub (contDiff_apply ℝ (Euc d) j)).contDiffOn
  · intro Y hY
    exact mk_sub_ne_zero_of_mem_liftedFree hY hij

theorem cepc0_lipschitz_pot (D : DynData d) {L : ℝ≥0}
    (hL : LipschitzWith L (gradient (Torus.lift D.V))) :
    LipschitzWith L (cepc0_pot (N := N) D) := by
  refine LipschitzWith.of_dist_le_mul fun Y Z => ?_
  refine (dist_pi_le_iff (by positivity)).2 fun i => ?_
  have h1 := hL.dist_le_mul (Y i) (Z i)
  have h2 : dist (Y i) (Z i) ≤ dist Y Z := dist_le_pi_dist Y Z i
  calc dist (cepc0_pot D Y i) (cepc0_pot D Z i) ≤ L * dist (Y i) (Z i) := h1
    _ ≤ L * dist Y Z := by gcongr

theorem cepc0_locLipschitz (D : DynData d)
    (hK : Torus.IsSmoothOffZero (periodicRieszGrad d D.s)) (hV : cep_IsC11 D.V) :
    IsLocLipschitzDrift (liftedFree d N) (fun _ Z => liftedDrift D Z) := by
  obtain ⟨_, LV, hLV⟩ := hV
  have hC := cepc0_contDiffOn_pair (N := N) D hK
  have hP := cepc0_lipschitz_pot (N := N) D hLV
  refine ⟨?_, fun K hKc hKU T => ?_⟩
  · have e : (Function.uncurry fun (_ : ℝ) (Z : Fin N → Euc d) => liftedDrift D Z) =
        fun p => cepc0_pair D p.2 - cepc0_pot D p.2 := funext fun p => cepc0_drift_eq D p.2
    rw [e]
    exact (hC.continuousOn.comp continuousOn_snd (fun p hp => hp.2)).sub
      (hP.continuous.comp_continuousOn continuousOn_snd)
  · have hloc : LocallyLipschitzOn K (cepc0_pair (N := N) D) := by
      intro x hx
      obtain ⟨L, t, ht, hL⟩ := ((hC x (hKU hx)).contDiffAt
        ((isOpen_liftedFree d N).mem_nhds (hKU hx))).exists_lipschitzOnWith
      exact ⟨L, t, mem_nhdsWithin_of_mem_nhds ht, hL⟩
    obtain ⟨L, hL⟩ := hloc.exists_lipschitzOnWith_of_compact hKc
    refine ⟨L + LV, fun _ _ => ?_⟩
    have := hL.sub (hP.lipschitzOnWith (s := K))
    have e : (fun Z : Fin N → Euc d => liftedDrift D Z) =
        (cepc0_pair (N := N) D) - cepc0_pot D := funext fun Z => cepc0_drift_eq D Z
    rw [e]
    exact this

/-- **C0 (local Lipschitz drift under `C^{1,1}` potentials)**.  Statement verbatim from
`HRS.MC.Cepa.cep_C0_locLipschitz` (with the duplicated predicate `cep_IsC11`). -/
theorem cep_C0_locLipschitz_proof (D : DynData d) (hK : Torus.IsSmoothOffZero (periodicRieszGrad d D.s))
    (hV : cep_IsC11 D.V) : IsLocLipschitzDrift (liftedFree d N) (fun _ Z => liftedDrift D Z) :=
  cepc0_locLipschitz D hK hV

end HRS.MC.CepC0
