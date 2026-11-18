import HRS.Main.A8PAux5
import HRS.PDE.MeanFieldAprioriParaproduct
import HRS.PDE.MeanFieldAux

/-!
# Packet A8P, part 6: `‖∇f·∇g‖_{Ḣ^{(d-s)/2}} ≲ ‖f‖_{H^{m_*}} ‖g‖_{H^{m_*}}` (Sobolev algebra)
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators MeasureTheory

namespace HRS.Main.A8P

open HRS.GF HRS.Uniform HRS.PDE HRS.PDE.MFProduct

variable {d : ℕ}

/-- `μ = m_* - 1`. -/
def a8pμ (d : ℕ) : ℝ := (PDE.mStar d : ℝ) - 1

theorem a8pμ_gt (d : ℕ) : (d : ℝ) / 2 + 1 < a8pμ d := by
  have := a8p_mStar_gt d
  unfold a8pμ; linarith

/-- The partial derivatives of an `H^{m_*}` function lie in `H^{m_*-1}` with no larger norm. -/
theorem a8p_deriv_memHs {f : Torus d → ℝ} (hf : Torus.IsCk 2 f) (hm : MemSobolev (PDE.mStar d : ℝ) f)
    (j : Fin d) :
    MemHs (a8pμ d) (coeffOf (Torus.partialDeriv j f)) ∧
      hsNormSq (a8pμ d) (coeffOf (Torus.partialDeriv j f)) ≤ sobolevNorm (PDE.mStar d : ℝ) f ^ 2 := by
  have hf1 : Torus.IsCk 1 f := hf.of_le (by exact_mod_cast (by norm_num : 1 ≤ 2))
  obtain ⟨hmem, hnorm⟩ := hsNormSq_coeffOf (PDE.mStar d : ℝ) f hm
  rw [coeffOf_partialDeriv j f hf1]
  obtain ⟨h1, h2⟩ := MFApriori.hsNormSq_derivCoeff_le (PDE.mStar d : ℝ) j hmem
  exact ⟨h1, by rw [← hnorm]; exact h2⟩

theorem a8p_wiener_bound (d : ℕ) :
    ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∀ c : Coeff d, MemHs (a8pμ d) c →
      Summable (fun k => ‖c k‖) ∧ wienerNorm c ≤ C₁ * PDE.hsNorm (a8pμ d) c := by
  obtain ⟨C, hC0, hC⟩ := exists_wienerW_le_hsNorm (d := d) (a8pμ d) 0 le_rfl
    (by have := a8pμ_gt d; linarith)
  refine ⟨C, hC0, fun c hc => ?_⟩
  obtain ⟨h1, h2⟩ := hC c hc
  simp only [zero_div, sobWeight_zero, one_mul] at h1
  refine ⟨h1, ?_⟩
  simpa [wienerNormW, wienerNorm, sobWeight_zero] using h2


theorem a8p_hsNormSq_sum_le {c : Fin d → Coeff d} {μ : ℝ} (hc : ∀ j, MemHs μ (c j)) :
    MemHs μ (fun k => ∑ j, c j k) ∧
      hsNormSq μ (fun k => ∑ j, c j k) ≤ d * ∑ j, hsNormSq μ (c j) := by
  have hpt : ∀ k, sobWeight μ k * ‖∑ j, c j k‖ ^ 2 ≤ d * ∑ j, sobWeight μ k * ‖c j k‖ ^ 2 := by
    intro k
    have hw := MFProduct.sobWeight_nonneg μ k
    have h1 : ‖∑ j, c j k‖ ^ 2 ≤ d * ∑ j, ‖c j k‖ ^ 2 := by
      have h2 := norm_sum_le Finset.univ (fun j => c j k)
      have h3 : (∑ j, ‖c j k‖) ^ 2 ≤ (Finset.univ : Finset (Fin d)).card * ∑ j, ‖c j k‖ ^ 2 :=
        sq_sum_le_card_mul_sum_sq
      calc ‖∑ j, c j k‖ ^ 2 ≤ (∑ j, ‖c j k‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
        _ ≤ _ := by simpa using h3
    calc sobWeight μ k * ‖∑ j, c j k‖ ^ 2 ≤ sobWeight μ k * (d * ∑ j, ‖c j k‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h1 hw
      _ = d * ∑ j, sobWeight μ k * ‖c j k‖ ^ 2 := by
          rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => by ring
  have hsum : Summable fun k => (d : ℝ) * ∑ j, sobWeight μ k * ‖c j k‖ ^ 2 :=
    (summable_sum fun j _ => hc j).mul_left _
  have hs : MemHs μ (fun k => ∑ j, c j k) :=
    Summable.of_nonneg_of_le (fun k => mul_nonneg (MFProduct.sobWeight_nonneg μ k) (sq_nonneg _)) hpt hsum
  refine ⟨hs, ?_⟩
  unfold hsNormSq
  calc ∑' k, sobWeight μ k * ‖∑ j, c j k‖ ^ 2 ≤ ∑' k, (d : ℝ) * ∑ j, sobWeight μ k * ‖c j k‖ ^ 2 :=
        hs.tsum_le_tsum hpt hsum
    _ = d * ∑ j, ∑' k, sobWeight μ k * ‖c j k‖ ^ 2 := by
        rw [tsum_mul_left, Summable.tsum_finsetSum (fun j _ => hc j)]

theorem a8p_mulCoeff_bound (d : ℕ) :
    ∃ C₂ : ℝ, 0 ≤ C₂ ∧ ∀ u v : Coeff d, MemHs (a8pμ d) u → MemHs (a8pμ d) v →
      MemHs (a8pμ d) (mulCoeff u v) ∧
        PDE.hsNorm (a8pμ d) (mulCoeff u v) ≤ C₂ * PDE.hsNorm (a8pμ d) u * PDE.hsNorm (a8pμ d) v := by
  obtain ⟨C₁, hC₁, hW⟩ := a8p_wiener_bound d
  have hμ0 : 0 ≤ a8pμ d := by have := a8pμ_gt d; have : (0 : ℝ) ≤ d := Nat.cast_nonneg d; linarith
  refine ⟨2 ^ (a8pμ d) * (2 * C₁), by positivity, fun u v hu hv => ?_⟩
  obtain ⟨hu1, hwu⟩ := hW u hu
  obtain ⟨hv1, hwv⟩ := hW v hv
  obtain ⟨hmem, hbd⟩ := hsNorm_mulCoeff_le (a8pμ d) hμ0 u v hu hv hu1 hv1
  refine ⟨hmem, hbd.trans ?_⟩
  have hnu : 0 ≤ PDE.hsNorm (a8pμ d) u := Real.sqrt_nonneg _
  have hnv : 0 ≤ PDE.hsNorm (a8pμ d) v := Real.sqrt_nonneg _
  have h1 : PDE.hsNorm (a8pμ d) u * wienerNorm v ≤ PDE.hsNorm (a8pμ d) u * (C₁ * PDE.hsNorm (a8pμ d) v) :=
    mul_le_mul_of_nonneg_left hwv hnu
  have h2 : wienerNorm u * PDE.hsNorm (a8pμ d) v ≤ (C₁ * PDE.hsNorm (a8pμ d) u) * PDE.hsNorm (a8pμ d) v :=
    mul_le_mul_of_nonneg_right hwu hnv
  have h3 : (0 : ℝ) ≤ 2 ^ (a8pμ d) := by positivity
  calc 2 ^ (a8pμ d) * (PDE.hsNorm (a8pμ d) u * wienerNorm v + wienerNorm u * PDE.hsNorm (a8pμ d) v)
      ≤ 2 ^ (a8pμ d) * (PDE.hsNorm (a8pμ d) u * (C₁ * PDE.hsNorm (a8pμ d) v) +
          (C₁ * PDE.hsNorm (a8pμ d) u) * PDE.hsNorm (a8pμ d) v) :=
        mul_le_mul_of_nonneg_left (add_le_add h1 h2) h3
    _ = _ := by ring


theorem a8p_hom_le_hs {a μ : ℝ} (ha0 : 0 ≤ a) (haμ : a ≤ μ) {ψ : Torus d → ℝ}
    (hmem : MemHs μ (coeffOf ψ)) :
    HasFiniteHomSobolev a ψ ∧ homSobolevSq a ψ ≤ hsNormSq μ (coeffOf ψ) := by
  set F : Lattice d → ℝ := fun k => sobWeight μ k * ‖coeffOf ψ k‖ ^ 2 with hF
  have hterm : ∀ k : NonzeroLattice d,
      (2 * Real.pi * Lattice.enorm k.1) ^ (2 * a) * ‖Torus.fcoef ψ k.1‖ ^ 2 ≤ F k.1 := by
    intro k
    have hE0 : 0 ≤ Lattice.enorm k.1 := norm_nonneg _
    have hA0 : 0 ≤ 2 * Real.pi * Lattice.enorm k.1 := by positivity
    have h1 : (2 * Real.pi * Lattice.enorm k.1) ^ (2 * a) ≤ sobWeight μ k.1 := by
      unfold sobWeight
      have hb : (1 : ℝ) ≤ 1 + 4 * Real.pi ^ 2 * Lattice.enorm k.1 ^ 2 := by
        have : 0 ≤ 4 * Real.pi ^ 2 * Lattice.enorm k.1 ^ 2 := by positivity
        linarith
      calc (2 * Real.pi * Lattice.enorm k.1) ^ (2 * a)
          = ((2 * Real.pi * Lattice.enorm k.1) ^ 2) ^ a := by
            rw [Real.rpow_mul hA0, Real.rpow_two]
        _ ≤ (1 + 4 * Real.pi ^ 2 * Lattice.enorm k.1 ^ 2) ^ a := by
            refine Real.rpow_le_rpow (by positivity) ?_ ha0
            nlinarith
        _ ≤ (1 + 4 * Real.pi ^ 2 * Lattice.enorm k.1 ^ 2) ^ μ :=
            Real.rpow_le_rpow_of_exponent_le hb haμ
    have h2 : ‖Torus.fcoef ψ k.1‖ = ‖coeffOf ψ k.1‖ := by rw [coeffOf_eq_fcoef]
    rw [h2]
    exact mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
  have hsF : Summable fun k : NonzeroLattice d => F k.1 := (Torus.summable_lattice_iff F).1 hmem
  have hfin : HasFiniteHomSobolev a ψ :=
    Summable.of_nonneg_of_le (fun k => mul_nonneg (Real.rpow_nonneg (by
      have : 0 ≤ Lattice.enorm k.1 := norm_nonneg _
      positivity) _) (sq_nonneg _)) hterm hsF
  refine ⟨hfin, ?_⟩
  unfold homSobolevSq hsNormSq
  rw [Torus.tsum_lattice F hmem]
  have h0 : 0 ≤ F 0 := mul_nonneg (MFProduct.sobWeight_nonneg μ 0) (sq_nonneg _)
  calc ∑' k : NonzeroLattice d, (2 * Real.pi * Lattice.enorm k.1) ^ (2 * a) * ‖Torus.fcoef ψ k.1‖ ^ 2
      ≤ ∑' k : NonzeroLattice d, F k.1 := hfin.tsum_le_tsum hterm hsF
    _ ≤ F 0 + ∑' k : NonzeroLattice d, F k.1 := by linarith

theorem a8p_grad_apply (f : Torus d → ℝ) (x : Torus d) (j : Fin d) :
    (Torus.grad f x) j = Torus.partialDeriv j f x := by
  unfold Torus.grad Torus.partialDeriv
  have h := InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (x := EuclideanSpace.single j (1 : ℝ))
    (y := fderiv ℝ (Torus.lift f) (Torus.rep x))
  have e : gradient (Torus.lift f) (Torus.rep x) = (InnerProductSpace.toDual ℝ (Euc d)).symm
      (fderiv ℝ (Torus.lift f) (Torus.rep x)) := rfl
  rw [e]
  generalize (InnerProductSpace.toDual ℝ (Euc d)).symm (fderiv ℝ (Torus.lift f) (Torus.rep x)) = G at h ⊢
  rw [EuclideanSpace.inner_single_right] at h
  simpa using h


theorem a8p_inner_grad (f g : Torus d → ℝ) (x : Torus d) :
    inner ℝ (Torus.grad f x) (Torus.grad g x) = ∑ j, Torus.partialDeriv j f x * Torus.partialDeriv j g x := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [a8p_grad_apply f x j, a8p_grad_apply g x j]
  simp [mul_comm]


theorem a8p_hom_prod (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ Cp : ℝ, 0 ≤ Cp ∧ ∀ f g : Torus d → ℝ, Torus.IsCk 2 f → Torus.IsCk 2 g →
      MemSobolev (PDE.mStar d : ℝ) f → MemSobolev (PDE.mStar d : ℝ) g →
      HasFiniteHomSobolev (((d : ℝ) - s) / 2) (fun x => inner ℝ (Torus.grad f x) (Torus.grad g x)) ∧
      homSobolev (((d : ℝ) - s) / 2) (fun x => inner ℝ (Torus.grad f x) (Torus.grad g x)) ≤
        Cp * sobolevNorm (PDE.mStar d : ℝ) f * sobolevNorm (PDE.mStar d : ℝ) g := by
  obtain ⟨C₂, hC₂, hprod⟩ := a8p_mulCoeff_bound d
  refine ⟨d * C₂, by positivity, fun f g hf hg hmf hmg => ?_⟩
  have hf1 : Torus.IsCk 1 f := hf.of_le (by exact_mod_cast (by norm_num : 1 ≤ 2))
  have hg1 : Torus.IsCk 1 g := hg.of_le (by exact_mod_cast (by norm_num : 1 ≤ 2))
  set Kf : ℝ := sobolevNorm (PDE.mStar d : ℝ) f with hKf
  set Kg : ℝ := sobolevNorm (PDE.mStar d : ℝ) g with hKg
  have hKf0 : 0 ≤ Kf := Real.sqrt_nonneg _
  have hKg0 : 0 ≤ Kg := Real.sqrt_nonneg _
  set h : Torus d → ℝ := fun x => inner ℝ (Torus.grad f x) (Torus.grad g x) with hh
  have hh' : h = fun x => ∑ j, Torus.partialDeriv j f x * Torus.partialDeriv j g x :=
    funext fun x => a8p_inner_grad f g x
  have hu := fun j => a8p_deriv_memHs hf hmf j
  have hv := fun j => a8p_deriv_memHs hg hmg j
  have hcont : ∀ j, Continuous fun x => Torus.partialDeriv j f x * Torus.partialDeriv j g x := fun j =>
    (HRS.PDE.continuous_partialDeriv j f hf1).mul (HRS.PDE.continuous_partialDeriv j g hg1)
  have hcoef : coeffOf h = fun k => ∑ j, mulCoeff (coeffOf (Torus.partialDeriv j f))
      (coeffOf (Torus.partialDeriv j g)) k := by
    funext k
    rw [hh', MFAux.coeffOf_sum Finset.univ _ hcont k]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [coeffOf_mul _ _ (MFProduct.memLp_two_real (HRS.PDE.continuous_partialDeriv j f hf1))
      (MFProduct.memLp_two_real (HRS.PDE.continuous_partialDeriv j g hg1))]
  have hmc : ∀ j, MemHs (a8pμ d) (mulCoeff (coeffOf (Torus.partialDeriv j f))
      (coeffOf (Torus.partialDeriv j g))) ∧
      PDE.hsNorm (a8pμ d) (mulCoeff (coeffOf (Torus.partialDeriv j f)) (coeffOf (Torus.partialDeriv j g)))
        ≤ C₂ * Kf * Kg := by
    intro j
    obtain ⟨hm1, hb1⟩ := hprod _ _ (hu j).1 (hv j).1
    refine ⟨hm1, hb1.trans ?_⟩
    have hnu : PDE.hsNorm (a8pμ d) (coeffOf (Torus.partialDeriv j f)) ≤ Kf := by
      unfold PDE.hsNorm
      calc Real.sqrt _ ≤ Real.sqrt (Kf ^ 2) := Real.sqrt_le_sqrt (hu j).2
        _ = Kf := Real.sqrt_sq hKf0
    have hnv : PDE.hsNorm (a8pμ d) (coeffOf (Torus.partialDeriv j g)) ≤ Kg := by
      unfold PDE.hsNorm
      calc Real.sqrt _ ≤ Real.sqrt (Kg ^ 2) := Real.sqrt_le_sqrt (hv j).2
        _ = Kg := Real.sqrt_sq hKg0
    have hn0 : 0 ≤ PDE.hsNorm (a8pμ d) (coeffOf (Torus.partialDeriv j f)) := Real.sqrt_nonneg _
    exact mul_le_mul (mul_le_mul_of_nonneg_left hnu hC₂) hnv (Real.sqrt_nonneg _) (mul_nonneg hC₂ hKf0)
  obtain ⟨hsm, hsb⟩ := a8p_hsNormSq_sum_le (μ := a8pμ d) (fun j => (hmc j).1)
  rw [← hcoef] at hsm hsb
  have hsq : hsNormSq (a8pμ d) (coeffOf h) ≤ ((d : ℝ) * (C₂ * Kf * Kg)) ^ 2 := by
    refine hsb.trans ?_
    have hj : ∀ j, hsNormSq (a8pμ d) (mulCoeff (coeffOf (Torus.partialDeriv j f))
        (coeffOf (Torus.partialDeriv j g))) ≤ (C₂ * Kf * Kg) ^ 2 := by
      intro j
      have h0 : 0 ≤ hsNormSq (a8pμ d) (mulCoeff (coeffOf (Torus.partialDeriv j f))
          (coeffOf (Torus.partialDeriv j g))) :=
        tsum_nonneg fun k => mul_nonneg (MFProduct.sobWeight_nonneg _ k) (sq_nonneg _)
      have := (hmc j).2
      unfold PDE.hsNorm at this
      calc _ = (Real.sqrt (hsNormSq (a8pμ d) (mulCoeff (coeffOf (Torus.partialDeriv j f))
            (coeffOf (Torus.partialDeriv j g))))) ^ 2 := (Real.sq_sqrt h0).symm
        _ ≤ _ := pow_le_pow_left₀ (Real.sqrt_nonneg _) this 2
    calc (d : ℝ) * ∑ j, hsNormSq (a8pμ d) (mulCoeff (coeffOf (Torus.partialDeriv j f))
          (coeffOf (Torus.partialDeriv j g)))
        ≤ d * ∑ _j : Fin d, (C₂ * Kf * Kg) ^ 2 := by
          gcongr with j _
          exact hj j
      _ = ((d : ℝ) * (C₂ * Kf * Kg)) ^ 2 := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  have ha0 : 0 ≤ ((d : ℝ) - s) / 2 := by linarith
  have haμ : ((d : ℝ) - s) / 2 ≤ a8pμ d := by have := a8pμ_gt d; linarith
  obtain ⟨hfin, hhom⟩ := a8p_hom_le_hs ha0 haμ hsm
  refine ⟨hfin, ?_⟩
  unfold homSobolev
  calc Real.sqrt (homSobolevSq (((d : ℝ) - s) / 2) h) ≤ Real.sqrt (((d : ℝ) * (C₂ * Kf * Kg)) ^ 2) :=
        Real.sqrt_le_sqrt (hhom.trans hsq)
    _ = (d : ℝ) * (C₂ * Kf * Kg) := Real.sqrt_sq (by positivity)
    _ = _ := by ring

end HRS.Main.A8P
