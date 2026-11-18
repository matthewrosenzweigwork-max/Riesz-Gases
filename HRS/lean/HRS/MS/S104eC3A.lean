import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Module.Multilinear.Curry

/-!
# S104E route C, packet C3, file A: generic jet lemmas (parametric integrals and uniform limits)
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ContDiff Interval

namespace HRS.MS.S104e.C

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem s104c3_ftaylor_of_jets {N : ℕ} {f : E → ℝ} {p : E → FormalMultilinearSeries ℝ E ℝ}
    (h0 : ∀ x, (p x 0).curry0 = f x)
    (hd : ∀ m : ℕ, m < N → ∀ x, HasFDerivAt (fun y => p y m) (p x m.succ).curryLeft x)
    (hc : ∀ m : ℕ, m ≤ N → Continuous fun x => p x m) :
    ContDiff ℝ (N : WithTop ℕ∞) f ∧ ∀ m : ℕ, m ≤ N → ∀ x, iteratedFDeriv ℝ m f x = p x m := by
  have h : HasFTaylorSeriesUpTo (N : ℕ∞) f p :=
    ⟨h0, fun m hm x => hd m (by exact_mod_cast hm) x, fun m hm => hc m (by exact_mod_cast hm)⟩
  exact ⟨h.contDiff, fun m hm x => (h.eq_iteratedFDeriv (by exact_mod_cast hm) x).symm⟩

theorem s104c3_gen_comm {G H : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup H] [NormedSpace ℝ H] (L : G ≃L[ℝ] H) (μ : Measure ℝ) (φ : ℝ → G) :
    ∫ v, L (φ v) ∂μ = L (∫ v, φ v ∂μ) := ContinuousLinearEquiv.integral_comp_comm (𝕜 := ℝ) L φ

theorem s104c3_gen_meas {G H : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup H] [NormedSpace ℝ H] (L : G ≃L[ℝ] H) (μ : Measure ℝ) {φ : ℝ → G}
    (h : AEStronglyMeasurable φ μ) : AEStronglyMeasurable (fun v => L (φ v)) μ :=
  L.continuous.comp_aestronglyMeasurable h

theorem s104c3_curryLeft_integral (m : ℕ) (μ : Measure ℝ) (φ : ℝ → E [×(m+1)]→L[ℝ] ℝ) :
    ∫ v, (φ v).curryLeft ∂μ = (∫ v, φ v ∂μ).curryLeft :=
  s104c3_gen_comm (G := E [×(m+1)]→L[ℝ] ℝ) (H := E →L[ℝ] E [×m]→L[ℝ] ℝ)
    (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => E) ℝ).toContinuousLinearEquiv μ φ

theorem s104c3_curryLeft_meas (m : ℕ) (μ : Measure ℝ) {φ : ℝ → E [×(m+1)]→L[ℝ] ℝ}
    (h : AEStronglyMeasurable φ μ) : AEStronglyMeasurable (fun v => (φ v).curryLeft) μ :=
  s104c3_gen_meas (G := E [×(m+1)]→L[ℝ] ℝ) (H := E →L[ℝ] E [×m]→L[ℝ] ℝ)
    (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => E) ℝ).toContinuousLinearEquiv μ h

/-- Differentiation of a parametric interval integral up to order `N`. -/
theorem s104c3_jets_integral {a b : ℝ} (hab : a ≤ b) {N : ℕ} {Fv : ℝ → E → ℝ} {bnd : ℝ → ℝ}
    (hC : ∀ v ∈ Ioc a b, ContDiff ℝ (N : WithTop ℕ∞) (Fv v))
    (hB : ∀ v ∈ Ioc a b, ∀ m ≤ N, ∀ x, ‖iteratedFDeriv ℝ m (Fv v) x‖ ≤ bnd v)
    (hbi : IntervalIntegrable bnd volume a b)
    (hM : ∀ m ≤ N, ∀ x, ContinuousOn (fun v => iteratedFDeriv ℝ m (Fv v) x) (Ioc a b)) :
    ContDiff ℝ (N : WithTop ℕ∞) (fun x => ∫ v in a..b, Fv v x) ∧
      ∀ m ≤ N, ∀ x, iteratedFDeriv ℝ m (fun x => ∫ v in a..b, Fv v x) x =
        ∫ v in a..b, iteratedFDeriv ℝ m (Fv v) x := by
  have hu : Ι a b = Ioc a b := Set.uIoc_of_le hab
  have hmeas : ∀ m ≤ N, ∀ x, AEStronglyMeasurable (fun v => iteratedFDeriv ℝ m (Fv v) x)
      (volume.restrict (Ι a b)) := fun m hm x => by
    rw [hu]; exact (hM m hm x).aestronglyMeasurable measurableSet_Ioc
  have hbd : ∀ m ≤ N, ∀ x, ∀ᵐ v ∂(volume : Measure ℝ), v ∈ Ι a b →
      ‖iteratedFDeriv ℝ m (Fv v) x‖ ≤ bnd v := fun m hm x =>
    ae_of_all _ fun v hv => hB v (by rwa [hu] at hv) m hm x
  have hint : ∀ m ≤ N, ∀ x, IntervalIntegrable (fun v => iteratedFDeriv ℝ m (Fv v) x) volume a b :=
    fun m hm x => IntervalIntegrable.mono_fun' hbi (hmeas m hm x)
      ((ae_restrict_iff' measurableSet_uIoc).2 (hbd m hm x))
  set p : E → FormalMultilinearSeries ℝ E ℝ :=
    fun x m => ∫ v in a..b, iteratedFDeriv ℝ m (Fv v) x with hp
  have key := s104c3_ftaylor_of_jets (N := N) (f := fun x => ∫ v in a..b, Fv v x) (p := p) ?_ ?_ ?_
  · refine ⟨key.1, fun m hm x => ?_⟩
    rw [key.2 m hm x]
  · intro x
    have h1 := (continuousMultilinearCurryFin0 ℝ E ℝ).toLinearIsometry.integral_comp_comm
      (μ := volume.restrict (Ι a b)) (fun v => iteratedFDeriv ℝ 0 (Fv v) x)
    have h2 : ∀ v, (continuousMultilinearCurryFin0 ℝ E ℝ).toLinearIsometry
        (iteratedFDeriv ℝ 0 (Fv v) x) = Fv v x := fun v => by
      simp [iteratedFDeriv_zero_eq_comp]
    simp_rw [h2] at h1
    simp only [hp, intervalIntegral.integral_of_le hab]
    rw [hu] at h1
    rw [ContinuousMultilinearMap.curry0_apply]
    simpa using h1.symm
  · intro m hm x
    have hmN : m < N := hm
    have hd := intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
      (μ := volume) (s := Set.univ) (x₀ := x) (a := a) (b := b)
      (F := fun y v => iteratedFDeriv ℝ m (Fv v) y)
      (F' := fun y v => (iteratedFDeriv ℝ (m + 1) (Fv v) y).curryLeft)
      (bound := bnd) Filter.univ_mem
      (Eventually.of_forall fun y => hmeas m hmN.le y) (hint m hmN.le x) ?_ ?_ hbi ?_
    · have hc := s104c3_curryLeft_integral m (volume.restrict (Ι a b))
        (fun v => iteratedFDeriv ℝ (m + 1) (Fv v) x)
      simp only [hp, intervalIntegral.integral_of_le hab] at hd ⊢
      rw [hu] at hc
      rw [← hc]
      exact hd
    · exact s104c3_curryLeft_meas m _ (hmeas (m + 1) hm x)
    · refine ae_of_all _ fun v hv y _ => ?_
      rw [ContinuousMultilinearMap.curryLeft_norm]
      exact hB v (by rwa [hu] at hv) (m + 1) hm y
    · refine ae_of_all _ fun v hv y _ => ?_
      have hv' : v ∈ Ioc a b := by rwa [hu] at hv
      have h := ((hC v hv').differentiable_iteratedFDeriv (m := m) (by exact_mod_cast hmN) y).hasFDerivAt
      rw [fderiv_iteratedFDeriv] at h
      exact h
  · intro m hm
    exact intervalIntegral.continuous_of_dominated_interval (bound := bnd)
      (fun x => hmeas m hm x) (fun x => hbd m hm x) hbi
      (ae_of_all _ fun v hv => ((hC v (by rwa [hu] at hv)).continuous_iteratedFDeriv
        (by exact_mod_cast hm)))

theorem s104c3_gen_unif {G H : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup H] [NormedSpace ℝ H] (L : G ≃L[ℝ] H) {ι X : Type*} {l : Filter ι}
    {F : ι → X → G} {g : X → G} (h : TendstoUniformly F g l) :
    TendstoUniformly (fun n x => L (F n x)) (fun x => L (g x)) l :=
  L.toContinuousLinearMap.uniformContinuous.comp_tendstoUniformly h

/-- Uniform limits of jets: if the jets of `C^N` functions `fn n` converge uniformly (all orders `≤ N`) and
`fn n → f` pointwise, then `f` is `C^N` with the limit jets. -/
theorem s104c3_jets_limit {N : ℕ} {fn : ℕ → E → ℝ} {f : E → ℝ}
    {q : ∀ m : ℕ, E → (E [×m]→L[ℝ] ℝ)}
    (hC : ∀ n, ContDiff ℝ (N : WithTop ℕ∞) (fn n))
    (hlim : ∀ m ≤ N, TendstoUniformly (fun n x => iteratedFDeriv ℝ m (fn n) x) (q m) atTop)
    (hf : ∀ x, Tendsto (fun n => fn n x) atTop (𝓝 (f x))) :
    ContDiff ℝ (N : WithTop ℕ∞) f ∧ ∀ m ≤ N, ∀ x, iteratedFDeriv ℝ m f x = q m x := by
  refine s104c3_ftaylor_of_jets (N := N) (f := f) (p := fun x m => q m x) ?_ ?_ ?_
  · intro x
    have h1 : Tendsto (fun n => iteratedFDeriv ℝ 0 (fn n) x) atTop (𝓝 (q 0 x)) :=
      (hlim 0 (Nat.zero_le _)).tendsto_at x
    have h2 := ((continuousMultilinearCurryFin0 ℝ E ℝ).continuous.tendsto _).comp h1
    have h3 : ∀ n, (continuousMultilinearCurryFin0 ℝ E ℝ) (iteratedFDeriv ℝ 0 (fn n) x) = fn n x :=
      fun n => by simp [iteratedFDeriv_zero_eq_comp]
    have h4 : Tendsto (fun n => fn n x) atTop (𝓝 ((continuousMultilinearCurryFin0 ℝ E ℝ) (q 0 x))) := by
      simpa [Function.comp_def, h3] using h2
    rw [ContinuousMultilinearMap.curry0_apply]
    have := tendsto_nhds_unique h4 (hf x)
    simpa using this
  · intro m hm x
    have hmN : m < N := hm
    have hu : TendstoUniformly (fun n y => (iteratedFDeriv ℝ (m + 1) (fn n) y).curryLeft)
        (fun y => (q (m + 1) y).curryLeft) atTop :=
      s104c3_gen_unif (G := E [×(m+1)]→L[ℝ] ℝ) (H := E →L[ℝ] E [×m]→L[ℝ] ℝ)
        (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => E) ℝ).toContinuousLinearEquiv
        (hlim (m + 1) hm)
    refine hasFDerivAt_of_tendstoUniformly (f := fun n y => iteratedFDeriv ℝ m (fn n) y)
      (f' := fun n y => (iteratedFDeriv ℝ (m + 1) (fn n) y).curryLeft) hu ?_
      (fun y => (hlim m hmN.le).tendsto_at y) x
    intro n y
    have h := ((hC n).differentiable_iteratedFDeriv (m := m) (by exact_mod_cast hmN) y).hasFDerivAt
    rw [fderiv_iteratedFDeriv] at h
    exact h
  · intro m hm
    exact (hlim m hm).continuous (Eventually.of_forall fun n =>
      (hC n).continuous_iteratedFDeriv (by exact_mod_cast hm)).frequently

end HRS.MS.S104e.C
