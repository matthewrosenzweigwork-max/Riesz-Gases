import HRS.MS.R2SeAux25

/-!
# S9.9 `r2_static_edgeworth`, packet 26: bounded measurable calculus and the kernel coefficients

Worker S99, namespace `S99`.

* `BM`, `Lc`: bounded measurable functions and the centered covariance functional
  `L_ψ f = ∫ f ψ - (∫ f)(∫ ψ)` (linear in `f`);
* `Bh`, `Bterm`: the quadratic statistic `N(F^h_N - E F^h_N)` and its expectation against `ψ(W_N)`;
* `Qk`: the limit coefficients `Q_h(l,q) = ∬ h(x,y) a_l(x) a_q(y) dμ dμ`, and their value for a finite-rank kernel.
-/

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

noncomputable section

namespace S99

open S45
open HRS.Whole
open HRS (Euc cbNorm MemCb)

variable {d N : ℕ}

/-- Bounded measurable functions. -/
structure BM {α : Type*} [MeasurableSpace α] (f : α → ℝ) : Prop where
  meas : Measurable f
  bd : ∃ C : ℝ, ∀ x, |f x| ≤ C

namespace BM

variable {α : Type*} [MeasurableSpace α] {f g : α → ℝ}

theorem integrable {P : Measure α} [IsFiniteMeasure P] (h : BM f) : Integrable f P := by
  obtain ⟨C, hC⟩ := h.bd
  exact Integrable.of_bound h.meas.aestronglyMeasurable C (Filter.Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs]; exact hC x)

theorem add (hf : BM f) (hg : BM g) : BM (fun x => f x + g x) := by
  obtain ⟨C1, h1⟩ := hf.bd
  obtain ⟨C2, h2⟩ := hg.bd
  exact ⟨hf.meas.add hg.meas, C1 + C2, fun x => (abs_add_le _ _).trans (add_le_add (h1 x) (h2 x))⟩

theorem const_mul (c : ℝ) (hf : BM f) : BM (fun x => c * f x) := by
  obtain ⟨C1, h1⟩ := hf.bd
  exact ⟨hf.meas.const_mul c, |c| * C1, fun x => by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (h1 x) (abs_nonneg _)⟩

theorem mul (hf : BM f) (hg : BM g) : BM (fun x => f x * g x) := by
  obtain ⟨C1, h1⟩ := hf.bd
  obtain ⟨C2, h2⟩ := hg.bd
  exact ⟨hf.meas.mul hg.meas, C1 * C2, fun x => by
    rw [abs_mul]
    exact mul_le_mul (h1 x) (h2 x) (abs_nonneg _) ((abs_nonneg _).trans (h1 x))⟩

theorem const (c : ℝ) : BM (fun _ : α => c) := ⟨measurable_const, |c|, fun _ => le_rfl⟩

theorem sum {ι : Type*} (s : Finset ι) {f : ι → α → ℝ} (h : ∀ i ∈ s, BM (f i)) :
    BM (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using BM.const (α := α) 0
  | insert a s ha ih =>
    have := (h a (Finset.mem_insert_self a s)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
    simpa [Finset.sum_insert ha] using this

end BM

/-- `L_ψ f = ∫ f ψ - (∫ f) (∫ ψ)`. -/
def Lc {α : Type*} [MeasurableSpace α] (P : Measure α) (ψ f : α → ℝ) : ℝ :=
  (∫ x, f x * ψ x ∂P) - (∫ x, f x ∂P) * ∫ x, ψ x ∂P

section Lc

variable {α : Type*} [MeasurableSpace α] {P : Measure α} [IsProbabilityMeasure P] {ψ f g : α → ℝ}

theorem Lc_add (hψ : BM ψ) (hf : BM f) (hg : BM g) :
    Lc P ψ (fun x => f x + g x) = Lc P ψ f + Lc P ψ g := by
  unfold Lc
  have h1 : Integrable (fun x => f x * ψ x) P := (hf.mul hψ).integrable
  have h2 : Integrable (fun x => g x * ψ x) P := (hg.mul hψ).integrable
  have e : (fun x => (f x + g x) * ψ x) = fun x => f x * ψ x + g x * ψ x := funext fun x => by ring
  rw [e, integral_add h1 h2, integral_add hf.integrable hg.integrable]
  ring

theorem Lc_smul (c : ℝ) (hψ : BM ψ) (hf : BM f) :
    Lc P ψ (fun x => c * f x) = c * Lc P ψ f := by
  unfold Lc
  have e : (fun x => c * f x * ψ x) = fun x => c * (f x * ψ x) := funext fun x => by ring
  rw [e, integral_const_mul, integral_const_mul]
  ring

theorem Lc_const (c : ℝ) : Lc P ψ (fun _ => c) = 0 := by
  unfold Lc
  show (∫ x, c * ψ x ∂P) - (∫ _x, c ∂P) * ∫ x, ψ x ∂P = 0
  rw [integral_const_mul, integral_const]
  simp only [Measure.real, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul]
  ring

theorem Lc_sum {ι : Type*} (s : Finset ι) {f : ι → α → ℝ} (hψ : BM ψ) (h : ∀ i ∈ s, BM (f i)) :
    Lc P ψ (fun x => ∑ i ∈ s, f i x) = ∑ i ∈ s, Lc P ψ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa using Lc_const (P := P) (ψ := ψ) 0
  | insert a s ha ih =>
    have hs := BM.sum s (fun i hi => h i (Finset.mem_insert_of_mem hi))
    have e : (fun x => ∑ i ∈ insert a s, f i x) = fun x => f a x + ∑ i ∈ s, f i x :=
      funext fun x => Finset.sum_insert ha
    rw [e, Lc_add hψ (h a (Finset.mem_insert_self a s)) hs, ih fun i hi => h i (Finset.mem_insert_of_mem hi),
      Finset.sum_insert ha]

theorem Lc_abs_le (hψ : ∀ x, |ψ x| ≤ 1) (hψm : Measurable ψ) (hf : BM f) :
    |Lc P ψ f| ≤ 2 * ∫ x, |f x| ∂P := by
  unfold Lc
  have hψi : BM ψ := ⟨hψm, 1, hψ⟩
  have h1 : |∫ x, f x * ψ x ∂P| ≤ ∫ x, |f x| ∂P := by
    rw [← Real.norm_eq_abs]
    refine (norm_integral_le_integral_norm _).trans ?_
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => norm_nonneg _) hf.integrable.abs
      (Filter.Eventually.of_forall fun x => ?_)
    show ‖f x * ψ x‖ ≤ |f x|
    rw [Real.norm_eq_abs, abs_mul]
    calc |f x| * |ψ x| ≤ |f x| * 1 := mul_le_mul_of_nonneg_left (hψ x) (abs_nonneg _)
      _ = |f x| := mul_one _
  have h2 : |∫ x, ψ x ∂P| ≤ 1 := by
    have := norm_integral_le_of_norm_le_const (μ := P) (f := ψ) (C := 1)
      (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hψ x)
    simpa [Real.norm_eq_abs] using this
  have h3 : |∫ x, f x ∂P| ≤ ∫ x, |f x| ∂P := by
    rw [← Real.norm_eq_abs]; exact norm_integral_le_integral_norm _
  calc |(∫ x, f x * ψ x ∂P) - (∫ x, f x ∂P) * ∫ x, ψ x ∂P|
      ≤ |∫ x, f x * ψ x ∂P| + |∫ x, f x ∂P| * |∫ x, ψ x ∂P| := by
        refine (abs_sub _ _).trans ?_; rw [abs_mul]
    _ ≤ (∫ x, |f x| ∂P) + (∫ x, |f x| ∂P) * 1 :=
        add_le_add h1 (mul_le_mul h3 h2 (abs_nonneg _) ((abs_nonneg _).trans h3))
    _ = 2 * ∫ x, |f x| ∂P := by ring

end Lc

/-- The quadratic statistic `N (F^h_N - E F^h_N)` for the law `Q_{N,γ}`. -/
def Bh (d : ℕ) (s a β γ : ℝ) (N : ℕ) (h : Euc d → Euc d → ℝ) (X : EucConfig d N) : ℝ :=
  (N : ℝ) * (pairEnergy h X (thermalMeasure d s a β) -
    ∫ Y, pairEnergy h Y (thermalMeasure d s a β) ∂(S46.s46_P d s a β γ N))

theorem Bq_eq_Bh (d : ℕ) (s a β γ : ℝ) (N : ℕ) (χ : Euc d → ℝ) :
    Bq d s a β γ N χ = Bh d s a β γ N (commutatorKernel d s (gradient χ)) := rfl

/-- `E[B_h ψ(W_N)]`. -/
def Bterm (d : ℕ) (s a β γ : ℝ) (φ : ℕ → Euc d → ℝ) (N : ℕ) (h : Euc d → Euc d → ℝ)
    (ψ : SeqL2 → ℝ) : ℝ :=
  ∫ X, Bh d s a β γ N h X * ψ (featureVec φ (S46.s46_nu d s a β γ N) X) ∂(S46.s46_P d s a β γ N)

/-- The coefficient `Q_h(l,q) = ∬ h(x,y) a_l(x) a_q(y) dμ(x) dμ(y)`. -/
def Qk (d : ℕ) (s a β γ : ℝ) (φ : ℕ → Euc d → ℝ) (h : Euc d → Euc d → ℝ) (l q : ℕ) : ℝ :=
  ∫ p : Euc d × Euc d, h p.1 p.2 * aRep d s a β γ (φ l) p.1 * aRep d s a β γ (φ q) p.2
    ∂((thermalMeasure d s a β).prod (thermalMeasure d s a β))

section Qfin

variable {s : ℝ} {a β γ : ℝ} {φ : ℕ → Euc d → ℝ}

theorem s99_Qk_finrank {C c BU : ℝ} (hT : ThermalData d s a β C c BU) {m : ℕ} {cc : Fin m → Fin m → ℝ}
    {u : Fin m → Euc d → ℝ} (hu : ∀ a, Continuous (u a)) {B : ℝ} (hub : ∀ a x, |u a x| ≤ B)
    (l q : ℕ) (hal : Continuous (aRep d s a β γ (φ l))) (haq : Continuous (aRep d s a β γ (φ q)))
    {Bl Bq' : ℝ} (hBl : ∀ x, |aRep d s a β γ (φ l) x| ≤ Bl) (hBq : ∀ x, |aRep d s a β γ (φ q) x| ≤ Bq') :
    Qk d s a β γ φ (r2FiniteRankKernel cc u) l q =
      ∑ i, ∑ j, cc i j * (kap d s a β γ (u i) φ l * kap d s a β γ (u j) φ q) := by
  haveI hμ : IsProbabilityMeasure (thermalMeasure d s a β) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu hT.prob
  unfold Qk r2FiniteRankKernel
  set μ := thermalMeasure d s a β with hμdef
  have hint : ∀ i j, Integrable (fun p : Euc d × Euc d =>
      cc i j * u i p.1 * u j p.2 * aRep d s a β γ (φ l) p.1 * aRep d s a β γ (φ q) p.2) (μ.prod μ) := by
    intro i j
    refine Integrable.of_bound (C := |cc i j| * B * B * Bl * Bq') ?_ (Filter.Eventually.of_forall fun p => ?_)
    · exact (((((continuous_const.mul ((hu i).comp continuous_fst)).mul ((hu j).comp continuous_snd)).mul
        (hal.comp continuous_fst)).mul (haq.comp continuous_snd))).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_mul]
      have hB0 : 0 ≤ B := (abs_nonneg _).trans (hub i 0)
      have hBl0 : 0 ≤ Bl := (abs_nonneg _).trans (hBl 0)
      have hBq0 : 0 ≤ Bq' := (abs_nonneg _).trans (hBq 0)
      exact mul_le_mul (mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left (hub i _) (abs_nonneg _))
        (hub j _) (abs_nonneg _) (by positivity)) (hBl _) (abs_nonneg _) (by positivity)) (hBq _)
        (abs_nonneg _) (by positivity)
  have e1 : (fun p : Euc d × Euc d => (∑ i, ∑ j, cc i j * u i p.1 * u j p.2) *
      aRep d s a β γ (φ l) p.1 * aRep d s a β γ (φ q) p.2) =
      fun p => ∑ i, ∑ j, cc i j * u i p.1 * u j p.2 * aRep d s a β γ (φ l) p.1 *
        aRep d s a β γ (φ q) p.2 := by
    funext p
    simp only [Finset.sum_mul]
  rw [e1, integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => hint i j]
  refine Finset.sum_congr rfl fun j _ => ?_
  have e2 : (fun p : Euc d × Euc d => cc i j * u i p.1 * u j p.2 * aRep d s a β γ (φ l) p.1 *
      aRep d s a β γ (φ q) p.2) =
      fun p => cc i j * ((u i p.1 * aRep d s a β γ (φ l) p.1) * (u j p.2 * aRep d s a β γ (φ q) p.2)) := by
    funext p; ring
  rw [e2, integral_const_mul]
  congr 1
  exact integral_prod_mul (μ := μ) (ν := μ) (fun x => u i x * aRep d s a β γ (φ l) x)
    (fun y => u j y * aRep d s a β γ (φ q) y)

end Qfin

end S99

end
