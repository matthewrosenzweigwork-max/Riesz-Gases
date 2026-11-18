import Mathlib
import HRS.MS.SuppU5Aux8

/-!
# Packet U5 (aux 9): the finite Hilbert direct sum (multi-time case)
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace Matrix

noncomputable section

namespace HRS.U5

open HRS HRS.Whole HRS.MP.RdProp HRS.MP.HNegInfra

variable {d : ℕ}

lemma u5_mul_mul_apply {k : ℕ} {ι : Type} [Fintype ι] (M : Matrix (Fin k) ι ℝ) (S : Matrix ι ι ℝ)
    (c c' : Fin k) : (M * S * Mᵀ) c c' = ∑ j, ∑ j', M c j * S j j' * M c' j' := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]

/-- The coordinates of a linear image of the bridge, for an arbitrary finite index type. -/
lemma u5_bridge_vec_gen {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (μ : Measure (Euc d)) [IsProbabilityMeasure μ] (η : Ω' → (Euc d → ℝ) → ℝ)
    (hη : ∀ (p : ℕ) (ψ : Fin p → Euc d → ℝ), (∀ a, MemCb 1 (ψ a)) →
      P'.map (fun ζ => (WithLp.toLp 2 fun a => η ζ (ψ a) : Ek p)) =
        multivariateGaussian 0 (Matrix.of fun a b => iidCovW μ (ψ a) (ψ b)))
    (hηm : ∀ ψ : Euc d → ℝ, MemCb 1 ψ → Measurable fun ζ => η ζ ψ)
    {ι : Type} [Fintype ι] {k : ℕ} (ψ : ι → Euc d → ℝ) (hψ : ∀ j, MemCb 1 (ψ j))
    (M : Matrix (Fin k) ι ℝ) :
    P'.map (fun ζ => (WithLp.toLp 2 fun c : Fin k => ∑ j, M c j * η ζ (ψ j) : Ek k)) =
      multivariateGaussian 0 (Matrix.of fun c c' =>
        ∑ j, ∑ j', M c j * M c' j' * iidCovW μ (ψ j) (ψ j')) := by
  set e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι with he
  set ψ' : Fin (Fintype.card ι) → Euc d → ℝ := fun j => ψ (e.symm j) with hψ'
  set M' : Matrix (Fin k) (Fin (Fintype.card ι)) ℝ := Matrix.of fun c j => M c (e.symm j) with hM'
  have h := u5_bridge_vec P' μ η hη hηm ψ' (fun j => hψ _) M'
  have e1 : (fun ζ => (WithLp.toLp 2 fun c : Fin k => ∑ j, M c j * η ζ (ψ j) : Ek k)) =
      fun ζ => (WithLp.toLp 2 fun c : Fin k => ∑ j, M' c j * η ζ (ψ' j) : Ek k) := by
    ext ζ c
    simp only [hM', hψ', Matrix.of_apply]
    exact (Equiv.sum_comp e.symm (fun j => M c j * η ζ (ψ j))).symm
  rw [e1, h]
  congr 1
  ext c c'
  rw [u5_mul_mul_apply]
  simp only [Matrix.of_apply, hM', hψ']
  refine Fintype.sum_equiv e.symm _ _ fun j => ?_
  exact Fintype.sum_equiv e.symm _ _ fun j' => by ring

/-- Vectors of the direct sum all of whose components represent tests. -/
def u5_Rpi (Γ : ℝ) (p : ℕ) : Submodule ℝ (PiLp 2 (fun _ : Fin p => HNeg d Γ)) where
  carrier := {w | ∀ a, w a ∈ LinearMap.range (rpk_J (d := d) Γ)}
  add_mem' := fun {x y} hx hy a => by
    simpa using (LinearMap.range (rpk_J (d := d) Γ)).add_mem (hx a) (hy a)
  zero_mem' := fun a => by simp
  smul_mem' := fun c x hx a => by
    simpa using (LinearMap.range (rpk_J (d := d) Γ)).smul_mem c (hx a)

lemma u5_Rpi_orth (Γ : ℝ) (p : ℕ) : (u5_Rpi (d := d) Γ p)ᗮ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro F hF
  ext a : 1
  show F a = 0
  refine hneg_eq_zero_of_pairing_zero (F a) fun φ hφ => ?_
  rw [← rpk_J_inner (⟨φ, hφ⟩ : rpk_Tst d Γ) (F a)]
  classical
  have hmem : (WithLp.toLp 2 (Pi.single a (rpk_J Γ ⟨φ, hφ⟩)) :
      PiLp 2 (fun _ : Fin p => HNeg d Γ)) ∈ u5_Rpi (d := d) Γ p := by
    intro b
    by_cases hb : b = a
    · subst hb; simp only [Pi.single_eq_same]; exact ⟨⟨φ, hφ⟩, rfl⟩
    · simp [Pi.single_eq_of_ne hb]
  have := (Submodule.mem_orthogonal _ _).1 hF _ hmem
  rw [PiLp.inner_apply, Finset.sum_eq_single a] at this
  · simpa using this
  · intro b _ hb; simp [Pi.single_eq_of_ne hb]
  · simp

lemma u5_cov_integrable {f g : Euc d → ℝ} (hf : MemCb 1 f) (hg : MemCb 1 g) (μ : Measure (Euc d))
    [IsProbabilityMeasure μ] :
    Integrable (fun x => (f x - HRS.Whole.pair μ f) * (g x - HRS.Whole.pair μ g)) μ := by
  have e : (fun x => (f x - HRS.Whole.pair μ f) * (g x - HRS.Whole.pair μ g)) =
      fun x => (f x * g x - HRS.Whole.pair μ g * f x) -
        (HRS.Whole.pair μ f * g x - HRS.Whole.pair μ f * HRS.Whole.pair μ g) := by
    ext x; ring
  rw [e]
  exact ((u5_prod_integrable hf hg μ).sub ((u5_cb_integrable hf μ).const_mul _)).sub
    (((u5_cb_integrable hg μ).const_mul _).sub (integrable_const _))

lemma u5_int_prod_sum {p : ℕ} (μ : Measure (Euc d)) [IsProbabilityMeasure μ] (f g : Fin p → Euc d → ℝ)
    (hf : ∀ a, MemCb 1 (f a)) (hg : ∀ a, MemCb 1 (g a)) :
    ∫ x, (∑ a, (f a x - HRS.Whole.pair μ (f a))) * (∑ a, (g a x - HRS.Whole.pair μ (g a))) ∂μ =
      ∑ a, ∑ a', iidCovW μ (f a) (g a') := by
  simp_rw [Finset.sum_mul_sum]
  rw [integral_finsetSum _ fun a _ => integrable_finsetSum _ fun a' _ => u5_cov_integrable (hf a) (hg a') μ]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [integral_finsetSum _ fun a' _ => u5_cov_integrable (hf a) (hg a') μ]
  exact Finset.sum_congr rfl fun a' _ => u5_cov_eq (hf a) (hg a') μ

/-- The law of the coordinates of the vector of Gaussian fields along tests. -/
lemma u5_coords_law_multi {Γ : ℝ} {p : ℕ} (A : ℝ) (μ : Measure (Euc d)) [IsProbabilityMeasure μ]
    (ψ : Fin p → (Euc d → ℝ) → (Euc d → ℝ))
    (hψc : ∀ a φ, IsSobolevTest Γ φ → MemCb 1 (ψ a φ))
    (J : Fin p → Euc d → HNeg d Γ)
    (hJ : ∀ a x φ, IsSobolevTest Γ φ →
      HNeg.pairing φ (J a x) = A * (ψ a φ x - HRS.Whole.pair μ (ψ a φ)))
    {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (η : Ω' → (Euc d → ℝ) → ℝ)
    (hηm : ∀ ψ : Euc d → ℝ, MemCb 1 ψ → Measurable fun ζ => η ζ ψ)
    (hη : ∀ (p : ℕ) (ψ : Fin p → Euc d → ℝ), (∀ a, MemCb 1 (ψ a)) →
      P'.map (fun ζ => (WithLp.toLp 2 fun a => η ζ (ψ a) : Ek p)) =
        multivariateGaussian 0 (Matrix.of fun a b => iidCovW μ (ψ a) (ψ b)))
    (I : Ω' → PiLp 2 (fun _ : Fin p => HNeg d Γ))
    (hI : ∀ a φ, IsSobolevTest Γ φ → ∀ᵐ ζ ∂P', HNeg.pairing φ (I ζ a) = A * η ζ (ψ a φ))
    (L : ℕ) (w : Fin L → PiLp 2 (fun _ : Fin p => HNeg d Γ)) (hw : ∀ c, w c ∈ u5_Rpi (d := d) Γ p) :
    P'.map (fun ζ => (WithLp.toLp 2 fun c : Fin L => inner ℝ (w c) (I ζ) : Ek L)) =
      multivariateGaussian 0 (Matrix.of fun c c' =>
        ∫ x, inner ℝ (w c) (WithLp.toLp 2 fun a => J a x : PiLp 2 (fun _ : Fin p => HNeg d Γ)) *
          inner ℝ (w c') (WithLp.toLp 2 fun a => J a x : PiLp 2 (fun _ : Fin p => HNeg d Γ)) ∂μ) := by
  classical
  choose φ hφ using fun c a => LinearMap.mem_range.1 (hw c a)
  have hφt : ∀ c a, IsSobolevTest Γ (φ c a).1 := fun c a => (φ c a).2
  have hin : ∀ (c : Fin L) (a : Fin p) (F : HNeg d Γ), inner ℝ (w c a) F = HNeg.pairing (φ c a).1 F :=
    fun c a F => by rw [← hφ c a]; exact rpk_J_inner (φ c a) F
  set ψf : Fin L × Fin p → Euc d → ℝ := fun j => ψ j.2 (φ j.1 j.2).1 with hψf
  have hψfm : ∀ j, MemCb 1 (ψf j) := fun j => hψc _ _ (hφt _ _)
  set M : Matrix (Fin L) (Fin L × Fin p) ℝ := Matrix.of fun c j => if j.1 = c then A else 0 with hM
  have hY : ∀ (ζ : Ω') (c : Fin L), ∑ j, M c j * η ζ (ψf j) = ∑ a, A * η ζ (ψ a (φ c a).1) := by
    intro ζ c
    rw [Fintype.sum_prod_type]
    simp only [hM, Matrix.of_apply, hψf]
    rw [Finset.sum_eq_single c]
    · simp
    · intro c' _ hc'; simp [hc']
    · simp
  have hae : ∀ᵐ ζ ∂P', ∀ c : Fin L, inner ℝ (w c) (I ζ) = ∑ a, A * η ζ (ψ a (φ c a).1) := by
    rw [ae_all_iff]
    intro c
    have : ∀ᵐ ζ ∂P', ∀ a, HNeg.pairing (φ c a).1 (I ζ a) = A * η ζ (ψ a (φ c a).1) :=
      ae_all_iff.2 fun a => hI a _ (hφt c a)
    filter_upwards [this] with ζ hζ
    rw [PiLp.inner_apply]
    exact Finset.sum_congr rfl fun a _ => by rw [hin]; exact hζ a
  rw [Measure.map_congr (g := fun ζ => (WithLp.toLp 2 fun c : Fin L => ∑ j, M c j * η ζ (ψf j) : Ek L))
    (by
      filter_upwards [hae] with ζ hζ
      ext c
      show inner ℝ (w c) (I ζ) = ∑ j, M c j * η ζ (ψf j)
      rw [hY ζ c]; exact hζ c)]
  rw [u5_bridge_vec_gen P' μ η hη hηm ψf hψfm M]
  congr 1
  ext c c'
  simp only [Matrix.of_apply]
  -- the right-hand side
  have hcoord : ∀ x c, inner ℝ (w c) (WithLp.toLp 2 fun a => J a x : PiLp 2 (fun _ : Fin p => HNeg d Γ)) =
      ∑ a, A * (ψ a (φ c a).1 x - HRS.Whole.pair μ (ψ a (φ c a).1)) := fun x c => by
    rw [PiLp.inner_apply]
    exact Finset.sum_congr rfl fun a _ => by
      rw [hin]; exact hJ a x _ (hφt c a)
  simp_rw [hcoord]
  have e1 : ∀ x, (∑ a, A * (ψ a (φ c a).1 x - HRS.Whole.pair μ (ψ a (φ c a).1))) *
      (∑ a, A * (ψ a (φ c' a).1 x - HRS.Whole.pair μ (ψ a (φ c' a).1))) =
      A ^ 2 * ((∑ a, (ψ a (φ c a).1 x - HRS.Whole.pair μ (ψ a (φ c a).1))) *
        (∑ a, (ψ a (φ c' a).1 x - HRS.Whole.pair μ (ψ a (φ c' a).1)))) := fun x => by
    rw [← Finset.mul_sum, ← Finset.mul_sum]; ring
  simp_rw [e1]
  rw [integral_const_mul, u5_int_prod_sum μ (fun a => ψ a (φ c a).1) (fun a => ψ a (φ c' a).1)
    (fun a => hψc _ _ (hφt c a)) (fun a => hψc _ _ (hφt c' a))]
  rw [Fintype.sum_prod_type]
  simp only [hM, Matrix.of_apply, hψf, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single c (fun x _ hx => by simp [hx]) (by simp)]
  simp only [if_true]
  rw [Finset.sum_comm, Finset.sum_eq_single c' (fun x _ hx => by simp [hx]) (by simp)]
  simp only [if_true, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ => ?_
  ring

end HRS.U5
