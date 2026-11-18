import HRS.MC.CepP2
import HRS.Stochastic.SelectedLawFKE
import HRS.Appendix.CepaFlow

/-!
# Packet P3, Aux1: lattice shifts, the unit cube, and the covering `mkC : (Fin N → Euc d) → Config d N`
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.CepP3

open HRS

variable {d N : ℕ}

/-- The lattice shift of the covering space by `w : Fin N → ℤ^d`. -/
def lat (w : Fin N → Lattice d) : Fin N → Euc d := fun i => Lattice.toEuc (w i)

/-- The covering map `(Fin N → Euc d) → Config d N`. -/
def mkC (Y : Fin N → Euc d) : Config d N := fun i => Torus.mk (Y i)

theorem lat_add (w u : Fin N → Lattice d) : lat (w + u) = lat w + lat u := by
  funext i
  ext j
  simp [lat, Lattice.toEuc]

theorem lat_zero : lat (0 : Fin N → Lattice d) = 0 := by
  funext i
  ext j
  simp [lat, Lattice.toEuc]

theorem lat_neg (w : Fin N → Lattice d) : lat (-w) = -lat w := by
  funext i
  ext j
  simp [lat, Lattice.toEuc]

theorem lat_injective : Function.Injective (lat : (Fin N → Lattice d) → Fin N → Euc d) := by
  intro w u h
  funext i j
  have := congrFun h i
  have h2 := congrArg (fun v : Euc d => v j) this
  simpa [lat, Lattice.toEuc] using h2

theorem isLatticeVec_lat (w : Fin N → Lattice d) : IsLatticeVec (lat w) := fun i => ⟨w i, rfl⟩

theorem mkC_add_lat (Y : Fin N → Euc d) (w : Fin N → Lattice d) : mkC (Y + lat w) = mkC Y :=
  mk_add_lattice_vec (isLatticeVec_lat w) Y

theorem measurable_mkC : Measurable (mkC : (Fin N → Euc d) → Config d N) :=
  measurable_pi_iff.2 fun j => Torus.continuous_mk.measurable.comp (measurable_pi_apply j)

theorem continuous_mkC : Continuous (mkC : (Fin N → Euc d) → Config d N) := continuous_mkPi d N

theorem mkC_eq_iff {Y Y' : Fin N → Euc d} (h : mkC Y = mkC Y') :
    ∃ w : Fin N → Lattice d, Y' = Y + lat w := by
  obtain ⟨v, hv, hY⟩ := exists_lattice_shift (Y := Y) (Y' := Y') (fun i => congrFun h i)
  choose n hn using hv
  exact ⟨n, by rw [hY]; congr 1; funext i; exact hn i⟩

/-! ### The unit cube -/

/-- The half-open unit cube `[0,1)^{N d}` in the covering space. -/
def cubeQ (d N : ℕ) : Set (Fin N → Euc d) := {Y | ∀ i j, Y i j ∈ Ico (0 : ℝ) 1}

/-- The coordinatewise integer parts. -/
def flo (Y : Fin N → Euc d) : Fin N → Lattice d := fun i j => ⌊Y i j⌋

theorem measurableSet_cubeQ : MeasurableSet (cubeQ d N) := by
  have : cubeQ d N = ⋂ i, ⋂ j, {Y : Fin N → Euc d | Y i j ∈ Ico (0 : ℝ) 1} := by
    ext Y; simp [cubeQ]
  rw [this]
  refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => ?_
  have hm : Measurable fun Y : Fin N → Euc d => Y i j :=
    (measurable_pi_apply j).comp ((PiLp.volume_preserving_ofLp (Fin d)).measurable.comp
      (measurable_pi_apply i))
  exact measurableSet_Ico.preimage hm

theorem sub_lat_flo_mem (Y : Fin N → Euc d) : Y - lat (flo Y) ∈ cubeQ d N := by
  intro i j
  simp only [lat, flo, Lattice.toEuc, Pi.sub_apply, PiLp.sub_apply]
  exact ⟨by simpa using Int.fract_nonneg (Y i j), by simpa using Int.fract_lt_one (Y i j)⟩

theorem rep_mk_apply (y : Euc d) (j : Fin d) : Torus.rep (Torus.mk y) j = Int.fract (y j) := by
  have h : (AddCircle.equivIco (1 : ℝ) 0 ((y j : ℝ) : UnitAddCircle) : ℝ) = Int.fract (y j) := by
    simp
  exact h

theorem repC_mkC (Y : Fin N → Euc d) : repC (mkC Y) = Y - lat (flo Y) := by
  funext i
  ext j
  show Torus.rep (Torus.mk (Y i)) j = (Y - lat (flo Y)) i j
  rw [rep_mk_apply]
  simp only [lat, flo, Lattice.toEuc, Pi.sub_apply, PiLp.sub_apply, Int.fract]

theorem repC_mem_cubeQ (x : Config d N) : repC x ∈ cubeQ d N := by
  intro i j
  have h := (AddCircle.equivIco (1 : ℝ) 0 (x i j)).2
  simpa [repC, Torus.rep] using h

theorem repC_mkC_of_mem {Y : Fin N → Euc d} (hY : Y ∈ cubeQ d N) : repC (mkC Y) = Y := by
  rw [repC_mkC]
  have : flo Y = 0 := by
    funext i j
    simp only [flo, Pi.zero_apply]
    exact Int.floor_eq_zero_iff.2 (hY i j)
  rw [this, lat_zero, sub_zero]

theorem flo_add_lat (Y : Fin N → Euc d) (w : Fin N → Lattice d) : flo (Y + lat w) = flo Y + w := by
  funext i j
  simp [flo, lat, Lattice.toEuc]

theorem flo_eq_iff {Y : Fin N → Euc d} {w : Fin N → Lattice d} :
    flo Y = w ↔ Y - lat w ∈ cubeQ d N := by
  constructor
  · rintro rfl; exact sub_lat_flo_mem Y
  · intro h
    funext i j
    have := h i j
    simp only [lat, Lattice.toEuc, Pi.sub_apply, PiLp.sub_apply] at this
    simp only [flo]
    refine Int.floor_eq_iff.2 ⟨by linarith [this.1], by linarith [this.2]⟩

theorem repC_mkC_add_lat (Y : Fin N → Euc d) (w : Fin N → Lattice d) :
    repC (mkC Y) = repC (mkC (Y + lat w)) := by
  rw [mkC_add_lat]

/-! ### The cube measure -/

/-- The cube in a single copy of `ℝ^d`. -/
def cubeE (d : ℕ) : Set (Euc d) := {w | ∀ i, w i ∈ Ico (0 : ℝ) 1}

theorem measurableSet_cubeE : MeasurableSet (cubeE d) := by
  have : cubeE d = (fun w : Euc d => w.ofLp) ⁻¹' (Set.pi univ fun _ : Fin d => Ico (0 : ℝ) 1) := by
    ext w; simp [cubeE]
  rw [this]
  exact (MeasurableSet.pi countable_univ fun _ _ => measurableSet_Ico).preimage
    (PiLp.volume_preserving_ofLp (Fin d)).measurable

theorem mk_measurePreserving_cubeE :
    MeasurePreserving (Torus.mk : Euc d → Torus d) (volume.restrict (cubeE d)) volume := by
  have hIco : (volume : Measure ℝ).restrict (Ico (0 : ℝ) 1) = (volume : Measure ℝ).restrict (Ioc (0 : ℝ) (0 + 1)) := by
    rw [zero_add]; exact Measure.restrict_congr_set Ico_ae_eq_Ioc
  have h1 := measurePreserving_pi (fun _ : Fin d => (volume : Measure ℝ).restrict (Ico (0 : ℝ) 1))
    (fun _ : Fin d => (volume : Measure UnitAddCircle))
    (f := fun _ => ((↑) : ℝ → UnitAddCircle)) (fun _ => by
      rw [hIco]; exact UnitAddCircle.measurePreserving_mk 0)
  rw [← Measure.restrict_pi_pi] at h1
  have h2 := (PiLp.volume_preserving_ofLp (Fin d)).restrict_preimage
    (s := Set.pi univ fun _ : Fin d => Ico (0 : ℝ) 1)
    (MeasurableSet.pi countable_univ fun _ _ => measurableSet_Ico)
  have hc : (fun w : Euc d => w.ofLp) ⁻¹' (Set.pi univ fun _ : Fin d => Ico (0 : ℝ) 1) = cubeE d := by
    ext w; simp [cubeE]
  rw [hc] at h2
  exact h1.comp h2

theorem cubeQ_eq_pi : cubeQ d N = Set.pi univ (fun _ : Fin N => cubeE d) := by
  ext Y; simp [cubeQ, cubeE]

theorem mkC_measurePreserving_cube :
    MeasurePreserving (mkC : (Fin N → Euc d) → Config d N) (volume.restrict (cubeQ d N)) volume := by
  have h1 := measurePreserving_pi (fun _ : Fin N => (volume : Measure (Euc d)).restrict (cubeE d))
    (fun _ : Fin N => (volume : Measure (Torus d)))
    (f := fun _ => (Torus.mk : Euc d → Torus d)) (fun _ => mk_measurePreserving_cubeE)
  rw [← Measure.restrict_pi_pi] at h1
  rw [cubeQ_eq_pi]
  exact h1

end HRS.MC.CepP3
