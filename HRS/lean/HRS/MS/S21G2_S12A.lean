import Mathlib

/-!
# S21G2 S12 (part A) -- one i.i.d. sequence for the product measures, scalar CLT (R26-T3.S12)

`P0 = infinitePi μ` on `ℕ → E`; its first-`N`-coordinate law is `Measure.pi (fun _ : Fin N => μ)`, and the scalar CLT of Mathlib
applies to `g(ω_k)` for mean-zero `g ∈ L²(μ)`.  Helper names carry the prefix `s21g2_s12_`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R26T3

section A

variable {E : Type*} [MeasurableSpace E] (μ : Measure E) [IsProbabilityMeasure μ]

/-- First `N` coordinates of an infinite sequence. -/
def s21g2_s12_restr (N : ℕ) (ω : ℕ → E) : Fin N → E := fun i => ω i

theorem s21g2_s12_restr_law (N : ℕ) :
    (Measure.infinitePi fun _ : ℕ => μ).map (s21g2_s12_restr N) = Measure.pi fun _ : Fin N => μ := by
  refine (Measure.pi_eq fun s hs => ?_).symm
  have hm : Measurable (s21g2_s12_restr (E := E) N) := measurable_pi_iff.2 fun i => measurable_pi_apply _
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  let t : ℕ → Set E := fun k => if h : k < N then s ⟨k, h⟩ else Set.univ
  have hpre : s21g2_s12_restr N ⁻¹' (Set.pi Set.univ s) = Set.pi (Finset.range N : Set ℕ) t := by
    ext ω
    simp only [s21g2_s12_restr, Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left,
      Finset.coe_range, Set.mem_Iio, t]
    constructor
    · intro h k hk; simpa [hk] using h ⟨k, hk⟩
    · intro h i; simpa using h i.1 i.2
  rw [hpre, Measure.infinitePi_pi _ (fun k _ => by
    by_cases h : k < N <;> simp [t, h, hs, MeasurableSet.univ])]
  rw [← Fin.prod_univ_eq_prod_range]
  exact Finset.prod_congr rfl fun i _ => by simp [t, i.2]

/-- Transfer of convergence in distribution from the single sequence space to the product measures
(sizes `K N`). -/
theorem s21g2_s12_transfer {V : Type*} [TopologicalSpace V] [MeasurableSpace V] [OpensMeasurableSpace V]
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P'] {Z : Ω' → V}
    (K : ℕ → ℕ) (F : ∀ N, (Fin (K N) → E) → V) (hF : ∀ N, AEMeasurable (F N) (Measure.pi fun _ : Fin (K N) => μ))
    (h : TendstoInDistribution (fun N ω => F N (s21g2_s12_restr (K N) ω)) atTop Z
      (fun _ => Measure.infinitePi fun _ : ℕ => μ) P') :
    TendstoInDistribution F atTop Z (fun N => Measure.pi fun _ : Fin (K N) => μ) P' := by
  refine ⟨hF, h.aemeasurable_limit, ?_⟩
  have := h.tendsto
  refine this.congr fun N => ?_
  refine Subtype.ext ?_
  show (Measure.infinitePi fun _ : ℕ => μ).map (fun ω => F N (s21g2_s12_restr (K N) ω)) =
    (Measure.pi fun _ : Fin (K N) => μ).map (F N)
  have hr : Measurable (s21g2_s12_restr (E := E) (K N)) := measurable_pi_iff.2 fun i => measurable_pi_apply _
  have := AEMeasurable.map_map_of_aemeasurable (μ := Measure.infinitePi fun _ : ℕ => μ) (f := s21g2_s12_restr (K N))
    (g := F N) (by rw [s21g2_s12_restr_law μ (K N)]; exact hF N) hr.aemeasurable
  rw [s21g2_s12_restr_law μ (K N)] at this
  exact this.symm

/-- Scalar CLT for the coordinates of `P0`. -/
theorem s21g2_s12_clt {g : E → ℝ} (hg : Measurable g) (hg2 : MemLp g 2 μ) (hg0 : ∫ x, g x ∂μ = 0)
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P'] {Y : Ω' → ℝ}
    (hY : HasLaw Y (gaussianReal 0 (Real.toNNReal (∫ x, g x ^ 2 ∂μ))) P') :
    TendstoInDistribution (fun (N : ℕ) (ω : ℕ → E) => (Real.sqrt N)⁻¹ * ∑ k ∈ Finset.range N, g (ω k))
      atTop Y (fun _ => Measure.infinitePi fun _ : ℕ => μ) P' := by
  set P0 : Measure (ℕ → E) := Measure.infinitePi fun _ : ℕ => μ with hP0
  have hind : iIndepFun (fun (k : ℕ) (ω : ℕ → E) => g (ω k)) P0 :=
    iIndepFun_infinitePi (P := fun _ : ℕ => μ) (X := fun _ => g) (fun _ => hg)
  have hlaw : ∀ k, P0.map (fun ω => ω k) = μ := fun k => Measure.infinitePi_map_eval _ k
  have hid : ∀ k : ℕ, IdentDistrib (fun ω : ℕ → E => g (ω k)) (fun ω : ℕ → E => g (ω 0)) P0 P0 := fun k => by
    refine ⟨(hg.comp (measurable_pi_apply k)).aemeasurable, (hg.comp (measurable_pi_apply 0)).aemeasurable, ?_⟩
    have e : ∀ k : ℕ, P0.map (fun ω : ℕ → E => g (ω k)) = μ.map g := fun k => by
      rw [← hlaw k, Measure.map_map hg (measurable_pi_apply k)]; rfl
    rw [e k, e 0]
  have hm0 : P0[fun ω : ℕ → E => g (ω 0)] = 0 := by
    rw [← integral_map (measurable_pi_apply 0).aemeasurable hg.aestronglyMeasurable, hlaw 0, hg0]
  have hmem : MemLp (fun ω : ℕ → E => g (ω 0)) 2 P0 := by
    refine (memLp_map_measure_iff (f := fun ω : ℕ → E => ω 0) (μ := P0) hg.aestronglyMeasurable
      (measurable_pi_apply 0).aemeasurable).1 ?_
    rw [hlaw 0]; exact hg2
  have hvar : Var[fun ω : ℕ → E => g (ω 0); P0] = ∫ x, g x ^ 2 ∂μ := by
    have hmeas0 : AEMeasurable (fun ω : ℕ → E => g (ω 0)) P0 := (hg.comp (measurable_pi_apply 0)).aemeasurable
    rw [variance_of_integral_eq_zero (X := fun ω : ℕ → E => g (ω 0)) hmeas0 hm0]
    have := integral_map (μ := P0) (φ := fun ω : ℕ → E => ω 0) (f := fun x => g x ^ 2)
      (measurable_pi_apply 0).aemeasurable (hg.pow_const 2).aestronglyMeasurable
    rw [hlaw 0] at this
    exact this.symm
  have := tendstoInDistribution_inv_sqrt_mul_sum_sub (X := fun k ω => g (ω k)) (P := P0) (Y := Y) (P' := P')
    (by simpa [hvar] using hY) hmem hind hid
  simpa [hm0] using this

end A

end HRS.MS.R26T3
