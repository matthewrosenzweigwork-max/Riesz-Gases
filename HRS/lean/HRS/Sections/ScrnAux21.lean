import HRS.Sections.ScrnAux20
import HRS.PDE.MeanFieldProduct
import HRS.PDE.MeanFieldAux
import HRS.Energy.Coercivity

/-!
# Packet SCRN, part 21: `‖∇f·∇g‖_{Ḣ^a}` from `ℓ¹` and weighted `ℓ²` sums of the coefficients

`scrn_hom_prod`: for `C²` tests `f, g` with `∑ 2π|k| ‖f̂(k)‖ ≤ W_f`, `∑ (2π|k|)^{2a+2} ‖f̂(k)‖² ≤ H_f²` (and
the same for `g`), the product `⟨∇f, ∇g⟩` has `‖·‖_{Ḣ^a} ≤ d 2^{3a/2}(H_f W_g + W_f H_g)`
(Fourier-Moser product bound `hsNorm_mulCoeff_le`).  This is the sharp-in-`ℓ` version of the Sobolev
algebra estimate used for the covariance discrepancy.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ComplexConjugate

namespace HRS

variable {d : ℕ}

open PDE PDE.MFProduct

lemma scrn_hsNormSq_sum_le {c : Fin d → Coeff d} {μ : ℝ} (hc : ∀ j, MemHs μ (c j)) :
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

theorem scrn_hom_le_hs {a : ℝ} (ha0 : 0 ≤ a) {ψ : Torus d → ℝ}
    (hmem : MemHs a (coeffOf ψ)) :
    HasFiniteHomSobolev a ψ ∧ homSobolevSq a ψ ≤ hsNormSq a (coeffOf ψ) := by
  set F : Lattice d → ℝ := fun k => sobWeight a k * ‖coeffOf ψ k‖ ^ 2 with hF
  have hterm : ∀ k : NonzeroLattice d,
      (2 * Real.pi * Lattice.enorm k.1) ^ (2 * a) * ‖Torus.fcoef ψ k.1‖ ^ 2 ≤ F k.1 := by
    intro k
    have hE0 : 0 ≤ Lattice.enorm k.1 := norm_nonneg _
    have hA0 : 0 ≤ 2 * Real.pi * Lattice.enorm k.1 := by positivity
    have h1 : (2 * Real.pi * Lattice.enorm k.1) ^ (2 * a) ≤ sobWeight a k.1 := by
      unfold sobWeight
      calc (2 * Real.pi * Lattice.enorm k.1) ^ (2 * a)
          = ((2 * Real.pi * Lattice.enorm k.1) ^ 2) ^ a := by
            rw [Real.rpow_mul hA0, Real.rpow_two]
        _ ≤ (1 + 4 * Real.pi ^ 2 * Lattice.enorm k.1 ^ 2) ^ a := by
            refine Real.rpow_le_rpow (by positivity) ?_ ha0
            nlinarith
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
  have h0 : 0 ≤ F 0 := mul_nonneg (MFProduct.sobWeight_nonneg a 0) (sq_nonneg _)
  calc ∑' k : NonzeroLattice d, (2 * Real.pi * Lattice.enorm k.1) ^ (2 * a) * ‖Torus.fcoef ψ k.1‖ ^ 2
      ≤ ∑' k : NonzeroLattice d, F k.1 := hfin.tsum_le_tsum hterm hsF
    _ ≤ F 0 + ∑' k : NonzeroLattice d, F k.1 := by linarith

lemma scrn_single_deriv {a : ℝ} (ha : 0 ≤ a) : ∀ (h : Torus d → ℝ) (hh : Torus.IsCk 1 h) (W H : ℝ) (j : Fin d),
    Summable (fun k : Lattice d => 2 * Real.pi * Lattice.enorm k * ‖coeffOf h k‖) →
    ∑' k : Lattice d, 2 * Real.pi * Lattice.enorm k * ‖coeffOf h k‖ ≤ W →
    Summable (fun k : Lattice d => (2 * Real.pi * Lattice.enorm k) ^ (2 * a + 2) * ‖coeffOf h k‖ ^ 2) →
    ∑' k : Lattice d, (2 * Real.pi * Lattice.enorm k) ^ (2 * a + 2) * ‖coeffOf h k‖ ^ 2 ≤ H ^ 2 →
    0 ≤ H →
    (Summable fun k => ‖coeffOf (Torus.partialDeriv j h) k‖) ∧
    wienerNorm (coeffOf (Torus.partialDeriv j h)) ≤ W ∧
    MemHs a (coeffOf (Torus.partialDeriv j h)) ∧
    PDE.hsNorm a (coeffOf (Torus.partialDeriv j h)) ≤ 2 ^ (a / 2) * H := by
  intro h hh W H j hs1 hs1' hs2 hs2' hH
  have hu : ∀ k, ‖coeffOf (Torus.partialDeriv j h) k‖ ≤ 2 * Real.pi * Lattice.enorm k * ‖coeffOf h k‖ := by
    intro k
    rw [coeffOf_partialDeriv j h hh]
    simp only [derivCoeff, norm_mul, Complex.norm_real, Complex.norm_I, Complex.norm_ofNat,
      mul_one, Real.norm_eq_abs]
    have hkj : |((k j : ℤ) : ℝ)| ≤ Lattice.enorm k := by
      have := PiLp.norm_apply_le (Lattice.toEuc k) j
      simpa [Lattice.toEuc, Lattice.enorm, Real.norm_eq_abs] using this
    rw [abs_of_pos Real.pi_pos]
    have : ‖((k j : ℤ) : ℂ)‖ = |((k j : ℤ) : ℝ)| := by
      rw [show (((k j : ℤ)) : ℂ) = (((k j : ℤ) : ℝ) : ℂ) by simp, Complex.norm_real, Real.norm_eq_abs]
    rw [this]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hkj (by positivity)) (norm_nonneg _)
  have hsu : Summable (fun k => ‖coeffOf (Torus.partialDeriv j h) k‖) :=
    (Summable.of_nonneg_of_le (fun k => norm_nonneg _) hu hs1)
  refine ⟨hsu, ?_, ?_⟩
  · unfold wienerNorm
    exact (hsu.tsum_le_tsum hu hs1).trans hs1'
  · -- weighted square bound
    have hw : ∀ k, sobWeight a k * ‖coeffOf (Torus.partialDeriv j h) k‖ ^ 2 ≤
        2 ^ a * ((2 * Real.pi * Lattice.enorm k) ^ (2 * a + 2) * ‖coeffOf h k‖ ^ 2) := by
      intro k
      by_cases hk : k = 0
      · subst hk
        have : coeffOf (Torus.partialDeriv j h) 0 = 0 := by
          rw [coeffOf_partialDeriv j h hh]
          simp [derivCoeff]
        rw [this]
        simp only [norm_zero]
        rw [scrn_enorm_zero]
        have : (2 * Real.pi * 0 : ℝ) = 0 := by ring
        rw [this, Real.zero_rpow (by linarith)]
        simp
      · have he : 1 ≤ Lattice.enorm k := one_le_enorm_of_ne_zero hk
        set x : ℝ := 2 * Real.pi * Lattice.enorm k with hx
        have hx1 : 1 ≤ x ^ 2 := by
          have : 1 ≤ x := by have := Real.pi_gt_three; nlinarith
          nlinarith
        have hx0 : 0 < x := by have := Real.pi_gt_three; positivity
        have hsw : sobWeight a k ≤ 2 ^ a * x ^ (2 * a) := by
          unfold sobWeight
          have : 1 + 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2 ≤ 2 * x ^ 2 := by
            rw [hx]; nlinarith [Real.pi_gt_three]
          calc (1 + 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2) ^ a ≤ (2 * x ^ 2) ^ a :=
                Real.rpow_le_rpow (by positivity) this ha
            _ = 2 ^ a * x ^ (2 * a) := by
                rw [Real.mul_rpow (by norm_num) (by positivity), Real.rpow_mul hx0.le,
                  Real.rpow_two]
        have hsq : ‖coeffOf (Torus.partialDeriv j h) k‖ ^ 2 ≤ x ^ 2 * ‖coeffOf h k‖ ^ 2 := by
          have := pow_le_pow_left₀ (norm_nonneg _) (hu k) 2
          calc _ ≤ (x * ‖coeffOf h k‖) ^ 2 := this
            _ = _ := by ring
        have hpow : x ^ (2 * a) * x ^ 2 = x ^ (2 * a + 2) := by
          rw [← Real.rpow_two, ← Real.rpow_add hx0]
        calc sobWeight a k * ‖coeffOf (Torus.partialDeriv j h) k‖ ^ 2
            ≤ (2 ^ a * x ^ (2 * a)) * (x ^ 2 * ‖coeffOf h k‖ ^ 2) :=
              mul_le_mul hsw hsq (sq_nonneg _) (by positivity)
          _ = 2 ^ a * (x ^ (2 * a + 2) * ‖coeffOf h k‖ ^ 2) := by rw [← hpow]; ring
    have hsm : MemHs a (coeffOf (Torus.partialDeriv j h)) :=
      Summable.of_nonneg_of_le (fun k => mul_nonneg (MFProduct.sobWeight_nonneg a k) (sq_nonneg _))
        hw (hs2.mul_left _)
    refine ⟨hsm, ?_⟩
    unfold PDE.hsNorm hsNormSq
    have hle : ∑' k, sobWeight a k * ‖coeffOf (Torus.partialDeriv j h) k‖ ^ 2 ≤ (2 ^ (a / 2) * H) ^ 2 := by
      calc _ ≤ ∑' k : Lattice d, 2 ^ a * ((2 * Real.pi * Lattice.enorm k) ^ (2 * a + 2) *
            ‖coeffOf h k‖ ^ 2) := hsm.tsum_le_tsum hw (hs2.mul_left _)
        _ = 2 ^ a * ∑' k : Lattice d, (2 * Real.pi * Lattice.enorm k) ^ (2 * a + 2) *
            ‖coeffOf h k‖ ^ 2 := tsum_mul_left
        _ ≤ 2 ^ a * H ^ 2 := mul_le_mul_of_nonneg_left hs2' (by positivity)
        _ = (2 ^ (a / 2) * H) ^ 2 := by
            rw [mul_pow, ← Real.rpow_natCast ((2 : ℝ) ^ (a / 2)) 2, ← Real.rpow_mul (by norm_num)]
            congr 2; push_cast; ring
    calc Real.sqrt _ ≤ Real.sqrt ((2 ^ (a / 2) * H) ^ 2) := Real.sqrt_le_sqrt hle
      _ = _ := Real.sqrt_sq (by positivity)


/-- The `Ḣ^a` seminorm of `⟨∇f, ∇g⟩`. -/
theorem scrn_hom_prod {a : ℝ} (ha : 0 ≤ a) {f g : Torus d → ℝ} (hf : Torus.IsCk 2 f)
    (hg : Torus.IsCk 2 g) {Wf Wg Hf Hg : ℝ} (hWf0 : 0 ≤ Wf) (hWg0 : 0 ≤ Wg) (hHf0 : 0 ≤ Hf)
    (hHg0 : 0 ≤ Hg)
    (hWf : Summable fun k : Lattice d => 2 * Real.pi * Lattice.enorm k * ‖coeffOf f k‖)
    (hWf' : ∑' k : Lattice d, 2 * Real.pi * Lattice.enorm k * ‖coeffOf f k‖ ≤ Wf)
    (hWg : Summable fun k : Lattice d => 2 * Real.pi * Lattice.enorm k * ‖coeffOf g k‖)
    (hWg' : ∑' k : Lattice d, 2 * Real.pi * Lattice.enorm k * ‖coeffOf g k‖ ≤ Wg)
    (hHf : Summable fun k : Lattice d =>
      (2 * Real.pi * Lattice.enorm k) ^ (2 * a + 2) * ‖coeffOf f k‖ ^ 2)
    (hHf' : ∑' k : Lattice d, (2 * Real.pi * Lattice.enorm k) ^ (2 * a + 2) * ‖coeffOf f k‖ ^ 2 ≤ Hf ^ 2)
    (hHg : Summable fun k : Lattice d =>
      (2 * Real.pi * Lattice.enorm k) ^ (2 * a + 2) * ‖coeffOf g k‖ ^ 2)
    (hHg' : ∑' k : Lattice d, (2 * Real.pi * Lattice.enorm k) ^ (2 * a + 2) * ‖coeffOf g k‖ ^ 2 ≤ Hg ^ 2) :
    HasFiniteHomSobolev a (fun x => inner ℝ (Torus.grad f x) (Torus.grad g x)) ∧
    homSobolev a (fun x => inner ℝ (Torus.grad f x) (Torus.grad g x)) ≤
      d * (2 ^ (3 * a / 2) * (Hf * Wg + Wf * Hg)) := by
  have hf1 : Torus.IsCk 1 f := hf.of_le (by exact_mod_cast (by norm_num : 1 ≤ 2))
  have hg1 : Torus.IsCk 1 g := hg.of_le (by exact_mod_cast (by norm_num : 1 ≤ 2))
  have single := scrn_single_deriv (d := d) ha
  have hcont : ∀ j, Continuous fun x => Torus.partialDeriv j f x * Torus.partialDeriv j g x := fun j =>
    (HRS.PDE.continuous_partialDeriv j f hf1).mul (HRS.PDE.continuous_partialDeriv j g hg1)
  set h : Torus d → ℝ := fun x => inner ℝ (Torus.grad f x) (Torus.grad g x) with hh
  have hh' : h = fun x => ∑ j, Torus.partialDeriv j f x * Torus.partialDeriv j g x :=
    funext fun x => scrn_inner_grad f g x
  have hcoef : coeffOf h = fun k => ∑ j, mulCoeff (coeffOf (Torus.partialDeriv j f))
      (coeffOf (Torus.partialDeriv j g)) k := by
    funext k
    rw [hh', MFAux.coeffOf_sum Finset.univ _ hcont k]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [coeffOf_mul _ _ (MFProduct.memLp_two_real (HRS.PDE.continuous_partialDeriv j f hf1))
      (MFProduct.memLp_two_real (HRS.PDE.continuous_partialDeriv j g hg1))]
  have hmc : ∀ j, MemHs a (mulCoeff (coeffOf (Torus.partialDeriv j f))
      (coeffOf (Torus.partialDeriv j g))) ∧
      PDE.hsNorm a (mulCoeff (coeffOf (Torus.partialDeriv j f)) (coeffOf (Torus.partialDeriv j g))) ≤
        2 ^ (3 * a / 2) * (Hf * Wg + Wf * Hg) := by
    intro j
    obtain ⟨s1, w1, m1, n1⟩ := single f hf1 Wf Hf j hWf hWf' hHf hHf' hHf0
    obtain ⟨s2, w2, m2, n2⟩ := single g hg1 Wg Hg j hWg hWg' hHg hHg' hHg0
    obtain ⟨hm, hb⟩ := hsNorm_mulCoeff_le a ha _ _ m1 m2 s1 s2
    refine ⟨hm, hb.trans ?_⟩
    have hp : (0 : ℝ) ≤ 2 ^ (a / 2) := by positivity
    have hn1 : 0 ≤ PDE.hsNorm a (coeffOf (Torus.partialDeriv j f)) := Real.sqrt_nonneg _
    have hn2 : 0 ≤ PDE.hsNorm a (coeffOf (Torus.partialDeriv j g)) := Real.sqrt_nonneg _
    have hwn1 : 0 ≤ wienerNorm (coeffOf (Torus.partialDeriv j f)) := tsum_nonneg fun k => norm_nonneg _
    have hwn2 : 0 ≤ wienerNorm (coeffOf (Torus.partialDeriv j g)) := tsum_nonneg fun k => norm_nonneg _
    have e1 : PDE.hsNorm a (coeffOf (Torus.partialDeriv j f)) * wienerNorm (coeffOf (Torus.partialDeriv j g)) ≤
        (2 ^ (a / 2) * Hf) * Wg := mul_le_mul n1 w2 hwn2 (by positivity)
    have e2 : wienerNorm (coeffOf (Torus.partialDeriv j f)) * PDE.hsNorm a (coeffOf (Torus.partialDeriv j g)) ≤
        Wf * (2 ^ (a / 2) * Hg) := mul_le_mul w1 n2 hn2 hWf0
    have e3 : (2 : ℝ) ^ a * (2 ^ (a / 2)) = 2 ^ (3 * a / 2) := by
      rw [← Real.rpow_add (by norm_num)]; congr 1; ring
    calc 2 ^ a * (PDE.hsNorm a (coeffOf (Torus.partialDeriv j f)) * wienerNorm (coeffOf (Torus.partialDeriv j g)) +
          wienerNorm (coeffOf (Torus.partialDeriv j f)) * PDE.hsNorm a (coeffOf (Torus.partialDeriv j g)))
        ≤ 2 ^ a * ((2 ^ (a / 2) * Hf) * Wg + Wf * (2 ^ (a / 2) * Hg)) :=
          mul_le_mul_of_nonneg_left (add_le_add e1 e2) (by positivity)
      _ = (2 ^ a * 2 ^ (a / 2)) * (Hf * Wg + Wf * Hg) := by ring
      _ = _ := by rw [e3]
  obtain ⟨hsm, hsb⟩ := scrn_hsNormSq_sum_le (μ := a) (fun j => (hmc j).1)
  rw [← hcoef] at hsm hsb
  set M : ℝ := 2 ^ (3 * a / 2) * (Hf * Wg + Wf * Hg) with hM
  have hsq : hsNormSq a (coeffOf h) ≤ ((d : ℝ) * M) ^ 2 := by
    refine hsb.trans ?_
    have hj : ∀ j, hsNormSq a (mulCoeff (coeffOf (Torus.partialDeriv j f))
        (coeffOf (Torus.partialDeriv j g))) ≤ M ^ 2 := by
      intro j
      have h0 : 0 ≤ hsNormSq a (mulCoeff (coeffOf (Torus.partialDeriv j f))
          (coeffOf (Torus.partialDeriv j g))) :=
        tsum_nonneg fun k => mul_nonneg (MFProduct.sobWeight_nonneg _ k) (sq_nonneg _)
      have := (hmc j).2
      unfold PDE.hsNorm at this
      calc _ = (Real.sqrt (hsNormSq a (mulCoeff (coeffOf (Torus.partialDeriv j f))
            (coeffOf (Torus.partialDeriv j g))))) ^ 2 := (Real.sq_sqrt h0).symm
        _ ≤ _ := pow_le_pow_left₀ (Real.sqrt_nonneg _) this 2
    calc (d : ℝ) * ∑ j, hsNormSq a (mulCoeff (coeffOf (Torus.partialDeriv j f))
          (coeffOf (Torus.partialDeriv j g)))
        ≤ d * ∑ _j : Fin d, M ^ 2 := by
          gcongr with j _
          exact hj j
      _ = ((d : ℝ) * M) ^ 2 := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  obtain ⟨hfin, hhom⟩ := scrn_hom_le_hs ha hsm
  refine ⟨hfin, ?_⟩
  unfold homSobolev
  have hM0 : 0 ≤ M := by positivity
  calc Real.sqrt (homSobolevSq a h) ≤ Real.sqrt (((d : ℝ) * M) ^ 2) :=
        Real.sqrt_le_sqrt (hhom.trans hsq)
    _ = (d : ℝ) * M := Real.sqrt_sq (by positivity)

end HRS
