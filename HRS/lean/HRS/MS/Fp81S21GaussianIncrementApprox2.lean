import HRS.MS.Fp81S21GaussianIncrementApprox

/-! Packet 36: the exact approximation payload, integrability of literal
increments, finite drift approximants, and algebraic tensor approximants. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxSynthPendingDepth 3
noncomputable section
open Classical MeasureTheory Filter Topology TopologicalSpace Set
open scoped ENNReal BigOperators
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6

/-- Algebraic tensors inside the completed projective tensor subspace. -/
def fp81s21_algebraicTensor2 (B : Type*) [NormedAddCommGroup B] [NormedSpace ℝ B] :
    Set (projTensor B 2) :=
  {x | (x : TensorDual B 2) ∈ Submodule.span ℝ (Set.range (elemTensor (B := B) (k := 2)))}

/-- Density follows from the actual definition of `projTensor`. -/
theorem fp81s21_algebraicTensor2_dense
    (B : Type*) [NormedAddCommGroup B] [NormedSpace ℝ B] :
    Dense (fp81s21_algebraicTensor2 B) := by
  intro x
  apply closure_subtype.2
  have he : Subtype.val '' fp81s21_algebraicTensor2 B =
      (Submodule.span ℝ (Set.range (elemTensor (B := B) (k := 2))) : Set (TensorDual B 2)) := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hz
    · intro hy
      exact ⟨⟨y, show y ∈ closure (↑(Submodule.span ℝ (Set.range (elemTensor (B := B) (k := 2)))) : Set (TensorDual B 2)) from subset_closure hy⟩, hy, rfl⟩
  rw [he]
  exact x.property

variable {p : Parameters} {δ : ℝ} {R : Trajectory p δ}

/-- The literal retained cumulative drift difference. -/
def fp81s21_incrementD36 (Q : fp81s21_Physical35 p R) (a : ℝ) (ha : 0 ≤ a)
    (u v : ℝ) : Q.src.G0.Ω → Window p := fun ω =>
  fp81s21_gaussian_Dcum (Q.OD a ha) (add_nonneg ha p.hT.le) (Q.UB a ha) v ω -
  fp81s21_gaussian_Dcum (Q.OD a ha) (add_nonneg ha p.hT.le) (Q.UB a ha) u ω

/-- The literal retained cumulative covariance difference, in the subtype norm. -/
def fp81s21_incrementJ36 (Q : fp81s21_Physical35 p R) (a : ℝ) (ha : 0 ≤ a)
    (u v : ℝ) : Q.src.G0.Ω → projTensor (Window p) 2 := fun ω =>
  fp81s21_gaussian_Jcum (Q.OJ a ha) (add_nonneg ha p.hT.le) (Q.UG a ha) v ω -
  fp81s21_gaussian_Jcum (Q.OJ a ha) (add_nonneg ha p.hT.le) (Q.UG a ha) u ω

/-- The exact retained past sigma-algebra at the right endpoint. -/
def fp81s21_incrementPast36 (Q : fp81s21_Physical35 p R) (v : ℝ) :
    MeasurableSpace Q.src.G0.Ω :=
  MeasurableSpace.comap (fp81s21_predictionPast Q.tofp81s21_Gaussian35Selection v) inferInstance

/-- Exact common-direction payload for both conditioned limit consumers.
The covariance lift is the same literal finite tensor used by those consumers. -/
structure fp81s21_IncrementApprox36 (Q : fp81s21_Physical35 p R)
    (a : ℝ) (ha : 0 ≤ a) (u v : ℝ) where
  integrableD : Integrable (fp81s21_incrementD36 Q a ha u v) Q.src.G0.P
  integrableJ : Integrable (fp81s21_incrementJ36 Q a ha u v) Q.src.G0.P
  k : ℕ → ℕ
  h : ∀ n, Fin (k n) → Window p
  cD : ∀ n, Fin (k n) → Q.src.G0.Ω → ℝ
  cJ : ∀ n, Fin (k n) → Fin (k n) → Q.src.G0.Ω → ℝ
  hcD : ∀ n i, Integrable (cD n i) Q.src.G0.P
  hcJ : ∀ n i j, Integrable (cJ n i j) Q.src.G0.P
  hcpastD : ∀ n i, AEStronglyMeasurable[fp81s21_incrementPast36 Q v] (cD n i) Q.src.G0.P
  hcpastJ : ∀ n i j, AEStronglyMeasurable[fp81s21_incrementPast36 Q v] (cJ n i j) Q.src.G0.P
  hlimD : Tendsto (fun n => ∫ ω,
    ‖(∑ i, cD n i ω • h n i) - fp81s21_incrementD36 Q a ha u v ω‖ ∂Q.src.G0.P)
      atTop (𝓝 0)
  hlimJ : Tendsto (fun n => ∫ ω,
    ‖(⟨fp81s21_finiteRandomTensor2 (k n) (h n) (cJ n) ω,
      fp81s21_finiteRandomTensor2_mem_projTensor (k n) (h n) (cJ n) ω⟩ :
        projTensor (Window p) 2) - fp81s21_incrementJ36 Q a ha u v ω‖ ∂Q.src.G0.P)
      atTop (𝓝 0)

/-- The actual drift increment admits the exact finite-direction L¹
approximation required by the conditioned drift limit. -/
theorem fp81s21_gaussian_drift_increment_approx
    (Q : fp81s21_Physical35 p R) (a : ℝ) (ha : 0 ≤ a)
    (u v : ℝ) (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ a + p.T) :
    ∃ (k : ℕ → ℕ) (h : ∀ n, Fin (k n) → Window p)
      (c : ∀ n, Fin (k n) → Q.src.G0.Ω → ℝ),
      (∀ n i, Integrable (c n i) Q.src.G0.P) ∧
      (∀ n i, AEStronglyMeasurable[fp81s21_incrementPast36 Q v] (c n i) Q.src.G0.P) ∧
      Tendsto (fun n => ∫ ω,
        ‖(∑ i, c n i ω • h n i) - fp81s21_incrementD36 Q a ha u v ω‖ ∂Q.src.G0.P)
        atTop (𝓝 0) := by
  letI : MeasurableSpace Q.src.G0.Ω := Q.src.G0.mΩ
  letI : IsProbabilityMeasure Q.src.G0.P := Q.src.G0.prob
  have hp : Measurable (fp81s21_predictionPast Q.tofp81s21_Gaussian35Selection v) :=
    measurable_pi_iff.2 fun i => Q.src.rawBundle.2.2.2.1 _
  obtain ⟨k, h, c, _, hc, hcpast, hlim⟩ := fp81s21_past_finite_dense_approx
    Q.src.G0.P (fp81s21_incrementD36 Q a ha u v)
    (fp81s21_gaussian_increments_integrable Q a ha u v).1
    (fp81s21_incrementPast36 Q v) hp.comap_le
    (fp81s21_gaussian_increments_past_adapted Q a ha u v hu huv hv).1
    Set.univ dense_univ (Set.mem_univ _)
  exact ⟨k, h, c, hc, hcpast, hlim⟩

/-- The actual covariance increment has L¹ approximants with algebraic tensor
directions. Flattening these directions to a common finite grid is separate. -/
theorem fp81s21_gaussian_covariance_increment_algebraic_approx
    (Q : fp81s21_Physical35 p R) (a : ℝ) (ha : 0 ≤ a)
    (u v : ℝ) (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ a + p.T) :
    ∃ (k : ℕ → ℕ) (h : ∀ n, Fin (k n) → projTensor (Window p) 2)
      (c : ∀ n, Fin (k n) → Q.src.G0.Ω → ℝ),
      (∀ n i, h n i ∈ fp81s21_algebraicTensor2 (Window p)) ∧
      (∀ n i, Integrable (c n i) Q.src.G0.P) ∧
      (∀ n i, AEStronglyMeasurable[fp81s21_incrementPast36 Q v] (c n i) Q.src.G0.P) ∧
      Tendsto (fun n => ∫ ω,
        ‖(∑ i, c n i ω • h n i) - fp81s21_incrementJ36 Q a ha u v ω‖ ∂Q.src.G0.P)
        atTop (𝓝 0) := by
  letI : MeasurableSpace Q.src.G0.Ω := Q.src.G0.mΩ
  letI : IsProbabilityMeasure Q.src.G0.P := Q.src.G0.prob
  letI : SecondCountableTopology (projTensor (Window p) 2) := s21g2_k06_sc 2
  have hp : Measurable (fp81s21_predictionPast Q.tofp81s21_Gaussian35Selection v) :=
    measurable_pi_iff.2 fun i => Q.src.rawBundle.2.2.2.1 _
  exact fp81s21_past_finite_dense_approx
    Q.src.G0.P (fp81s21_incrementJ36 Q a ha u v)
    (fp81s21_gaussian_increments_integrable Q a ha u v).2
    (fp81s21_incrementPast36 Q v) hp.comap_le
    (fp81s21_gaussian_increments_past_adapted Q a ha u v hu huv hv).2
    (fp81s21_algebraicTensor2 (Window p)) (fp81s21_algebraicTensor2_dense (Window p))
    (by
      change (0 : TensorDual (Window p) 2) ∈
        Submodule.span ℝ (Set.range (elemTensor (B := Window p) (k := 2)))
      exact Submodule.zero_mem _)

#print axioms fp81s21_algebraicTensor2_dense
#print axioms fp81s21_gaussian_drift_increment_approx
#print axioms fp81s21_gaussian_covariance_increment_algebraic_approx
end HRS.Fp81.S21
end
