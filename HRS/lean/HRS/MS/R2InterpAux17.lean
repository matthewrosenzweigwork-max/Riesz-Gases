import HRS.MS.R2InterpAux16
import HRS.MS.CovMeasAux4

/-!
# S10.2 (worker S102), part 17 (packet I4): the drift integrand `u ↦ V^{t,u}b(u)`

Under the structural hypotheses `S102Drift` (admissible functionals `b(u)` with an integrable norm bound `Mb(u)` and coordinate
measurability), `u ↦ V^{t,u}b(u)` is a.e.-strongly measurable on `[0,t]`, bounded by `Mb(u) K_V`, hence integrable on `(a,a'] ⊆ [0,t]`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R2Interp

open HRS HRS.Whole HRS.MS.CovMeas HRS.MS.FixEq

variable {d : ℕ}

/-- The structural hypotheses on the drift density `b`. -/
structure S102Drift (C : WholeCoeff d) (m T : ℝ) (r : ℕ) (Pw : ℝ) (b : ℝ → (Euc d → ℝ) → ℝ)
    (Mb : ℝ → ℝ) : Prop where
  hZ : ∀ u ∈ Icc (0 : ℝ) T, S102Z r Pw (b u)
  hM : ∀ u ∈ Icc (0 : ℝ) T, ∀ f, IsR2WeightedTest r Pw f →
    |b u f| ≤ Mb u * (weightedSobolevE r Pw f).toReal
  Mb_nonneg : ∀ u, 0 ≤ Mb u
  Mb_int : IntegrableOn Mb (Icc 0 T)
  meas : ∀ t ∈ Icc (0 : ℝ) T, ∀ α : MultiIndex d,
    AEStronglyMeasurable (fun u => b u (propagatorW C u t (oscTestFun m α))) (volume.restrict (Icc 0 t))

/-- The integrand `V^{t,u}b(u)`. -/
def s102_w (C : WholeCoeff d) (m : ℝ) (b : ℝ → (Euc d → ℝ) → ℝ) (u t : ℝ) : OscDual d m :=
  r2Vprop C m t u (b u)

variable {C : WholeCoeff d} {m T : ℝ} {r : ℕ} {c : MultiIndex d → ℝ} {Pw : ℝ} {b : ℝ → (Euc d → ℝ) → ℝ}
  {Mb : ℝ → ℝ}

theorem s102_w_norm_le (hP : (d : ℝ) < 2 * Pw) (hD : S101Data C m T r c) (hlin : S102Lin C m T)
    (hb : S102Drift C m T r Pw b Mb) {t u : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (hu : u ∈ Icc 0 t) :
    ‖s102_w C m b u t‖ ≤ Mb u * s102_KV d r Pw c := by
  have huT : u ∈ Icc (0 : ℝ) T := ⟨hu.1, hu.2.trans ht.2⟩
  have := s102_Vprop_norm_M hP hD (hb.hZ u huT) hlin (hb.hM u huT) huT (t := t) ⟨hu.2, ht.2⟩
  rwa [abs_of_nonneg (hb.Mb_nonneg u)] at this

theorem s102_w_aesm (hP : (d : ℝ) < 2 * Pw) (hD : S101Data C m T r c) (hlin : S102Lin C m T)
    (hb : S102Drift C m T r Pw b Mb) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    AEStronglyMeasurable (fun u => s102_w C m b u t) (volume.restrict (Icc 0 t)) := by
  classical
  set v : MultiIndex d → ℝ → ℝ := fun α u =>
    Set.indicator (Icc 0 t) (fun u => b u (propagatorW C u t (oscTestFun m α))) u with hv
  have hmeas : ∀ α, AEStronglyMeasurable (v α) (volume.restrict (Icc 0 t)) := fun α =>
    (hb.meas t ht α).indicator measurableSet_Icc
  have hmem : ∀ u, Memℓp (fun α => v α u) 2 := by
    intro u
    by_cases hu : u ∈ Icc 0 t
    · have huT : u ∈ Icc (0 : ℝ) T := ⟨hu.1, hu.2.trans ht.2⟩
      have := s102_z_orbit_memℓp hP hD (hb.hZ u huT) huT (t := t) ⟨hu.2, ht.2⟩
      simpa [hv, hu] using this
    · have h0 : (fun α => v α u) = (0 : MultiIndex d → ℝ) := by
        funext α; simp [hv, hu]
      rw [h0]
      exact zero_memℓp
  have h1 := s101_aesm_ellVec (d := d) (m := m) v hmeas hmem
  refine h1.congr ?_
  refine (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun u hu => ?_)
  have huT : u ∈ Icc (0 : ℝ) T := ⟨hu.1, hu.2.trans ht.2⟩
  apply s102_ext
  intro α
  rw [s101_ellVec_coord (hmem u)]
  show v α u = _
  rw [hv]
  simp only [hu, Set.indicator_of_mem]
  exact (s102_Vprop_coord hP hD (hb.hZ u huT) hlin huT (t := t) ⟨hu.2, ht.2⟩ α).symm

theorem s102_w_integrableOn (hP : (d : ℝ) < 2 * Pw) (hD : S101Data C m T r c) (hlin : S102Lin C m T)
    (hb : S102Drift C m T r Pw b Mb) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) {s : Set ℝ} (hs : s ⊆ Icc 0 t)
    (hsm : MeasurableSet s) : IntegrableOn (fun u => s102_w C m b u t) s := by
  have hI : IntegrableOn Mb s := hb.Mb_int.mono_set (hs.trans (Icc_subset_Icc le_rfl ht.2))
  refine Integrable.mono' (hI.mul_const (s102_KV d r Pw c))
    ((s102_w_aesm hP hD hlin hb ht).mono_measure (Measure.restrict_mono hs le_rfl))
    ((ae_restrict_iff' hsm).2 (Filter.Eventually.of_forall fun u hu => ?_))
  exact s102_w_norm_le hP hD hlin hb ht (hs hu)

end HRS.MS.R2Interp

end
