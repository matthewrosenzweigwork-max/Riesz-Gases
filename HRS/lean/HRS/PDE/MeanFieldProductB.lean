import HRS.PDE.Toolbox

/-!
# Mean-field package (MF-01), packet P3b: Sobolev product and Lipschitz composition

* `MFProduct.exists_product_bound`: the symmetric Sobolev product `H^a × H^b → H^c`
  (`c ≤ a`, `c ≤ b`, `a + b - c > d/2`) in coefficients.
* `MFProduct.exists_lipschitz_comp_bound_nnreal` / `exists_lipschitz_comp_bound_of_nonneg`:
  Lipschitz composition in `H^σ`, `0 ≤ σ < 1`, via the dyadic difference characterisation
  (`ProdAux.upper_vec`, `ProdAux.lower_vec'`, `ProdAux.diff_parseval`).
  (The plan's statement with a real `L` and `LipschitzWith (Real.toNNReal L) F` is false for
  `L < 0`; see the docstring of `exists_lipschitz_comp_bound_of_nonneg`.)
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.PDE.MFProduct

variable {d : ℕ}

/-! ### Young's inequality `ℓ¹ ∗ ℓ² ⊂ ℓ²` for nonnegative sequences (private copy) -/

private lemma summable_sub_left {A : Lattice d → ℝ} (hA : Summable A) (k : Lattice d) :
    Summable fun j => A (k - j) :=
  (Equiv.summable_iff (Equiv.subLeft k)).2 hA

private lemma summable_sub_right {A : Lattice d → ℝ} (hA : Summable A) (j : Lattice d) :
    Summable fun k => A (k - j) :=
  (Equiv.summable_iff (Equiv.subRight j)).2 hA

private lemma tsum_sub_left (A : Lattice d → ℝ) (k : Lattice d) :
    ∑' j, A (k - j) = ∑' j, A j :=
  (Equiv.subLeft k).tsum_eq A

private lemma tsum_sub_right (A : Lattice d → ℝ) (j : Lattice d) :
    ∑' k, A (k - j) = ∑' k, A k :=
  (Equiv.subRight j).tsum_eq A

private lemma young_real {A B : Lattice d → ℝ} (hA0 : ∀ k, 0 ≤ A k) (hB0 : ∀ k, 0 ≤ B k)
    (hA : Summable A) (hB : Summable fun j => B j ^ 2) :
    (∀ k, Summable fun j => A (k - j) * B j) ∧
    Summable (fun k => (∑' j, A (k - j) * B j) ^ 2) ∧
    ∑' k, (∑' j, A (k - j) * B j) ^ 2 ≤ (∑' k, A k) ^ 2 * ∑' j, B j ^ 2 := by
  set SA := ∑' k, A k with hSA
  have hSA0 : 0 ≤ SA := tsum_nonneg hA0
  have hAle : ∀ k, A k ≤ SA := fun k => hA.le_tsum k (fun j _ => hA0 j)
  -- the inner weighted square sums
  have hTs : ∀ k, Summable fun j => A (k - j) * B j ^ 2 := fun k =>
    Summable.of_nonneg_of_le (fun j => mul_nonneg (hA0 _) (sq_nonneg _))
      (fun j => mul_le_mul_of_nonneg_right (hAle _) (sq_nonneg _)) (hB.mul_left SA)
  set T : Lattice d → ℝ := fun k => ∑' j, A (k - j) * B j ^ 2 with hT
  have hT0 : ∀ k, 0 ≤ T k := fun k => tsum_nonneg fun j => mul_nonneg (hA0 _) (sq_nonneg _)
  -- Cauchy-Schwarz for fixed `k`
  have hcs : ∀ k, Summable (fun j => A (k - j) * B j) ∧
      (∑' j, A (k - j) * B j) ^ 2 ≤ SA * T k := by
    intro k
    have h1 : Summable fun j => (Real.sqrt (A (k - j))) ^ 2 := by
      simpa [Real.sq_sqrt (hA0 _)] using summable_sub_left hA k
    have h2 : Summable fun j => (Real.sqrt (A (k - j)) * B j) ^ 2 := by
      simpa [mul_pow, Real.sq_sqrt (hA0 _)] using hTs k
    obtain ⟨hs, hle⟩ := HRS.Torus.cs_tsum (fun j => Real.sqrt (A (k - j)))
      (fun j => Real.sqrt (A (k - j)) * B j) (fun j => Real.sqrt_nonneg _)
      (fun j => mul_nonneg (Real.sqrt_nonneg _) (hB0 j)) h1 h2
    have e1 : ∀ j, Real.sqrt (A (k - j)) * (Real.sqrt (A (k - j)) * B j) = A (k - j) * B j := by
      intro j
      rw [← mul_assoc, Real.mul_self_sqrt (hA0 _)]
    simp only [e1] at hs hle
    refine ⟨hs, ?_⟩
    have e2 : ∑' j, Real.sqrt (A (k - j)) ^ 2 = SA := by
      simp only [Real.sq_sqrt (hA0 _)]; exact tsum_sub_left A k
    have e3 : ∑' j, (Real.sqrt (A (k - j)) * B j) ^ 2 = T k := by
      simp only [mul_pow, Real.sq_sqrt (hA0 _), hT]
    rw [e2, e3] at hle
    have h0 : 0 ≤ ∑' j, A (k - j) * B j := tsum_nonneg fun j => mul_nonneg (hA0 _) (hB0 _)
    calc (∑' j, A (k - j) * B j) ^ 2 ≤ (Real.sqrt SA * Real.sqrt (T k)) ^ 2 :=
          pow_le_pow_left₀ h0 hle 2
      _ = SA * T k := by
          rw [mul_pow, Real.sq_sqrt hSA0, Real.sq_sqrt (hT0 k)]
  -- Tonelli
  have hprod : Summable (fun p : Lattice d × Lattice d => A (p.2 - p.1) * B p.1 ^ 2) := by
    have hf0 : (0 : Lattice d × Lattice d → ℝ) ≤ fun p : Lattice d × Lattice d => A (p.2 - p.1) * B p.1 ^ 2 := by
      intro p; exact mul_nonneg (hA0 _) (sq_nonneg _)
    refine (summable_prod_of_nonneg hf0).2 ⟨fun j => ?_, ?_⟩
    · show Summable fun k : Lattice d => A (k - j) * B j ^ 2
      exact (summable_sub_right hA j).mul_right _
    · have : (fun j : Lattice d => ∑' k, A (k - j) * B j ^ 2) = fun j => SA * B j ^ 2 := by
        funext j
        rw [tsum_mul_right, tsum_sub_right]
      simp only [this]
      exact hB.mul_left SA
  have hTsum : Summable T := by
    have hf0 : (0 : Lattice d × Lattice d → ℝ) ≤ fun p : Lattice d × Lattice d => A (p.1 - p.2) * B p.2 ^ 2 := by
      intro p; exact mul_nonneg (hA0 _) (sq_nonneg _)
    exact ((summable_prod_of_nonneg hf0).1 (hprod.prod_symm)).2
  have hTval : ∑' k, T k = SA * ∑' j, B j ^ 2 := by
    simp only [hT]
    rw [Summable.tsum_comm (f := fun j k => A (k - j) * B j ^ 2) hprod]
    have : (fun j : Lattice d => ∑' k, A (k - j) * B j ^ 2) = fun j => SA * B j ^ 2 := by
      funext j
      rw [tsum_mul_right, tsum_sub_right]
    simp only [this]
    rw [tsum_mul_left]
  refine ⟨fun k => (hcs k).1, ?_, ?_⟩
  · exact Summable.of_nonneg_of_le (fun k => sq_nonneg _) (fun k => (hcs k).2) (hTsum.mul_left SA)
  · calc ∑' k, (∑' j, A (k - j) * B j) ^ 2 ≤ ∑' k, SA * T k :=
          Summable.tsum_le_tsum (fun k => (hcs k).2) (by
            exact Summable.of_nonneg_of_le (fun k => sq_nonneg _) (fun k => (hcs k).2) (hTsum.mul_left SA))
            (hTsum.mul_left SA)
      _ = SA * (SA * ∑' j, B j ^ 2) := by rw [tsum_mul_left, hTval]
      _ = SA ^ 2 * ∑' j, B j ^ 2 := by ring

/-! ### Weight comparisons -/

private lemma sw_le_four_pow {s : ℝ} (hs : 0 ≤ s) {k l : Lattice d}
    (h : Lattice.enorm k ≤ 2 * Lattice.enorm l) :
    sobWeight s k ≤ (4 : ℝ) ^ s * sobWeight s l := by
  unfold sobWeight
  have h0 : 0 ≤ Lattice.enorm k := norm_nonneg _
  have h2 : Lattice.enorm k ^ 2 ≤ 4 * Lattice.enorm l ^ 2 := by
    have := pow_le_pow_left₀ h0 h 2
    nlinarith
  have hpi : 0 ≤ 4 * Real.pi ^ 2 := by positivity
  have h1 : 1 + 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2 ≤
      4 * (1 + 4 * Real.pi ^ 2 * Lattice.enorm l ^ 2) := by
    have := mul_le_mul_of_nonneg_left h2 hpi
    nlinarith
  have hpos : 0 < 1 + 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2 := sobWeight_base_pos k
  calc (1 + 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2) ^ s
      ≤ (4 * (1 + 4 * Real.pi ^ 2 * Lattice.enorm l ^ 2)) ^ s := Real.rpow_le_rpow hpos.le h1 hs
    _ = (4 : ℝ) ^ s * (1 + 4 * Real.pi ^ 2 * Lattice.enorm l ^ 2) ^ s :=
        Real.mul_rpow (by norm_num) (sobWeight_base_pos l).le

private lemma sw_anti {s : ℝ} (hs : s ≤ 0) {j l : Lattice d}
    (h : Lattice.enorm j ≤ Lattice.enorm l) : sobWeight s l ≤ sobWeight s j := by
  unfold sobWeight
  apply Real.rpow_le_rpow_of_nonpos (sobWeight_base_pos j) _ hs
  have h0 : 0 ≤ Lattice.enorm j := norm_nonneg _
  have := pow_le_pow_left₀ h0 h 2
  have hpi : 0 ≤ 4 * Real.pi ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left this hpi]

private lemma enorm_le_two_mul_of_le {k j : Lattice d}
    (h : Lattice.enorm j ≤ Lattice.enorm (k - j)) : Lattice.enorm k ≤ 2 * Lattice.enorm (k - j) := by
  have := enorm_le_add k j
  linarith

private lemma enorm_le_two_mul_of_le' {k j : Lattice d}
    (h : Lattice.enorm (k - j) ≤ Lattice.enorm j) : Lattice.enorm k ≤ 2 * Lattice.enorm j := by
  have := enorm_le_add k j
  linarith

/-- `sobWeight s k` squared. -/
private lemma sw_sq (s : ℝ) (k : Lattice d) : sobWeight s k ^ 2 = sobWeight (2 * s) k := by
  rw [two_mul, sobWeight_add, sq]

private lemma sw_inv_mul (s : ℝ) (k : Lattice d) (x : ℝ) :
    ‖x‖ = sobWeight (-s) k * (sobWeight s k * ‖x‖) := by
  rw [← mul_assoc, mul_comm (sobWeight (-s) k), sobWeight_mul_neg, one_mul]

private lemma alg_aux (X Y pa qa pb qb : ℝ) (ha : pa * qa = 1) (hb : pb * qb = 1) :
    X * Y = pa * pb * ((qa * X) * (qb * Y)) := by
  linear_combination (-(X * Y)) * ha + (-(X * Y * (pa * qa))) * hb

/-- the key pointwise inequality of the symmetric product bound -/
private lemma term_le (a b c : ℝ) (hc0 : 0 ≤ c) (hac : c ≤ a) (hbc : c ≤ b)
    (f g : Coeff d) (k j : Lattice d) :
    sobWeight (c / 2) k * (‖f (k - j)‖ * ‖g j‖) ≤
      (4 : ℝ) ^ (c / 2) * ((sobWeight (a / 2) (k - j) * ‖f (k - j)‖) *
          (sobWeight (-((a + b - c) / 2)) j * (sobWeight (b / 2) j * ‖g j‖)) +
        (sobWeight (-((a + b - c) / 2)) (k - j) * (sobWeight (a / 2) (k - j) * ‖f (k - j)‖)) *
          (sobWeight (b / 2) j * ‖g j‖)) := by
  set l := k - j with hl
  set X := ‖f l‖ with hX
  set Y := ‖g j‖ with hY
  have hX0 : 0 ≤ X := norm_nonneg _
  have hY0 : 0 ≤ Y := norm_nonneg _
  have hFn : 0 ≤ sobWeight (a / 2) l * X := mul_nonneg (sobWeight_pos _ _).le hX0
  have hGn : 0 ≤ sobWeight (b / 2) j * Y := mul_nonneg (sobWeight_pos _ _).le hY0
  have hE : ∀ x : Lattice d, 0 ≤ sobWeight (-((a + b - c) / 2)) x := fun x => (sobWeight_pos _ _).le
  have ha : sobWeight (-(a / 2)) l * sobWeight (a / 2) l = 1 := by
    rw [mul_comm]; exact sobWeight_mul_neg _ _
  have hb : sobWeight (-(b / 2)) j * sobWeight (b / 2) j = 1 := by
    rw [mul_comm]; exact sobWeight_mul_neg _ _
  have hXY := alg_aux X Y _ _ _ _ ha hb
  have hc2 : 0 ≤ c / 2 := by linarith
  have h4 : 0 ≤ (4 : ℝ) ^ (c / 2) := by positivity
  rcases le_total (Lattice.enorm j) (Lattice.enorm l) with h | h
  · -- `|j| ≤ |k - j|`
    have h1 : sobWeight (c / 2) k ≤ (4 : ℝ) ^ (c / 2) * sobWeight (c / 2) l :=
      sw_le_four_pow hc2 (enorm_le_two_mul_of_le h)
    have hmon : sobWeight (c / 2 + -(a / 2)) l ≤ sobWeight (c / 2 + -(a / 2)) j :=
      sw_anti (by linarith) h
    have hW : sobWeight (c / 2) l * sobWeight (-(a / 2)) l * sobWeight (-(b / 2)) j ≤
        sobWeight (-((a + b - c) / 2)) j := by
      rw [← sobWeight_add]
      calc sobWeight (c / 2 + -(a / 2)) l * sobWeight (-(b / 2)) j
          ≤ sobWeight (c / 2 + -(a / 2)) j * sobWeight (-(b / 2)) j :=
            mul_le_mul_of_nonneg_right hmon (sobWeight_pos _ _).le
        _ = sobWeight (-((a + b - c) / 2)) j := by
            rw [← sobWeight_add]; congr 1; ring
    have hFG : 0 ≤ (sobWeight (a / 2) l * X) * (sobWeight (b / 2) j * Y) := mul_nonneg hFn hGn
    calc sobWeight (c / 2) k * (X * Y)
        ≤ ((4 : ℝ) ^ (c / 2) * sobWeight (c / 2) l) * (X * Y) :=
          mul_le_mul_of_nonneg_right h1 (mul_nonneg hX0 hY0)
      _ = (4 : ℝ) ^ (c / 2) * (sobWeight (c / 2) l * sobWeight (-(a / 2)) l *
            sobWeight (-(b / 2)) j) * ((sobWeight (a / 2) l * X) * (sobWeight (b / 2) j * Y)) := by
          rw [hXY]; ring
      _ ≤ (4 : ℝ) ^ (c / 2) * sobWeight (-((a + b - c) / 2)) j *
            ((sobWeight (a / 2) l * X) * (sobWeight (b / 2) j * Y)) := by
          gcongr
      _ ≤ _ := by
          have h2 : 0 ≤ (sobWeight (-((a + b - c) / 2)) l * (sobWeight (a / 2) l * X)) *
              (sobWeight (b / 2) j * Y) := mul_nonneg (mul_nonneg (hE l) hFn) hGn
          nlinarith [mul_nonneg h4 h2]
  · -- `|k - j| ≤ |j|`
    have h1 : sobWeight (c / 2) k ≤ (4 : ℝ) ^ (c / 2) * sobWeight (c / 2) j :=
      sw_le_four_pow hc2 (enorm_le_two_mul_of_le' h)
    have hmon : sobWeight (c / 2 + -(b / 2)) j ≤ sobWeight (c / 2 + -(b / 2)) l :=
      sw_anti (by linarith) h
    have hW : sobWeight (c / 2) j * sobWeight (-(b / 2)) j * sobWeight (-(a / 2)) l ≤
        sobWeight (-((a + b - c) / 2)) l := by
      rw [← sobWeight_add]
      calc sobWeight (c / 2 + -(b / 2)) j * sobWeight (-(a / 2)) l
          ≤ sobWeight (c / 2 + -(b / 2)) l * sobWeight (-(a / 2)) l :=
            mul_le_mul_of_nonneg_right hmon (sobWeight_pos _ _).le
        _ = sobWeight (-((a + b - c) / 2)) l := by
            rw [← sobWeight_add]; congr 1; ring
    have hFG : 0 ≤ (sobWeight (a / 2) l * X) * (sobWeight (b / 2) j * Y) := mul_nonneg hFn hGn
    calc sobWeight (c / 2) k * (X * Y)
        ≤ ((4 : ℝ) ^ (c / 2) * sobWeight (c / 2) j) * (X * Y) :=
          mul_le_mul_of_nonneg_right h1 (mul_nonneg hX0 hY0)
      _ = (4 : ℝ) ^ (c / 2) * (sobWeight (c / 2) j * sobWeight (-(b / 2)) j *
            sobWeight (-(a / 2)) l) * ((sobWeight (a / 2) l * X) * (sobWeight (b / 2) j * Y)) := by
          rw [hXY]; ring
      _ ≤ (4 : ℝ) ^ (c / 2) * sobWeight (-((a + b - c) / 2)) l *
            ((sobWeight (a / 2) l * X) * (sobWeight (b / 2) j * Y)) := by
          gcongr
      _ ≤ _ := by
          have h2 : 0 ≤ (sobWeight (-((a + b - c) / 2)) j * (sobWeight (b / 2) j * Y)) *
              (sobWeight (a / 2) l * X) := mul_nonneg (mul_nonneg (hE j) hGn) hFn
          have h3 : 0 ≤ (sobWeight (a / 2) l * X) *
              (sobWeight (-((a + b - c) / 2)) j * (sobWeight (b / 2) j * Y)) := by
            rw [mul_comm]; exact h2
          nlinarith [mul_nonneg h4 h3]

/-! ### The symmetric Sobolev product bound -/

private lemma conv_swap_summable {F G : Lattice d → ℝ} (k : Lattice d)
    (h : Summable fun j => G (k - j) * F j) : Summable fun j => F (k - j) * G j := by
  have := (Equiv.summable_iff (Equiv.subLeft k)).2 h
  refine this.congr fun j => ?_
  simp [Equiv.subLeft_apply, mul_comm]

private lemma conv_swap_tsum (F G : Lattice d → ℝ) (k : Lattice d) :
    ∑' j, F (k - j) * G j = ∑' j, G (k - j) * F j := by
  rw [← (Equiv.subLeft k).tsum_eq (fun j => G (k - j) * F j)]
  refine tsum_congr fun j => ?_
  simp [Equiv.subLeft_apply, mul_comm]

private lemma summable_sw_neg_sq (m : ℝ) (hm : (d : ℝ) < 2 * m) :
    Summable fun l : Lattice d => (sobWeight (-(m / 2)) l) ^ 2 := by
  rw [Torus.summable_lattice_iff]
  refine (summable_jp_rpow (d := d) m hm).congr fun k => ?_
  rw [sw_sq, sobWeight_eq_jp]
  congr 1
  ring

private lemma sw_half_sq (a : ℝ) (l : Lattice d) (x : ℂ) :
    (sobWeight (a / 2) l * ‖x‖) ^ 2 = sobWeight a l * ‖x‖ ^ 2 := by
  rw [mul_pow, sw_sq]; congr 2; ring

theorem exists_product_bound (a b c : ℝ) (hc : 0 ≤ c) (hac : c ≤ a) (hbc : c ≤ b)
    (hsum : (d : ℝ) / 2 < a + b - c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f g : Coeff d, MemHs a f → MemHs b g →
      MemHs c (mulCoeff f g) ∧ hsNorm c (mulCoeff f g) ≤ C * hsNorm a f * hsNorm b g := by
  have hm : (d : ℝ) < 2 * (a + b - c) := by linarith
  set E : Lattice d → ℝ := fun l => sobWeight (-((a + b - c) / 2)) l with hEdef
  have hE0 : ∀ l, 0 ≤ E l := fun l => (sobWeight_pos _ _).le
  have hE2 : Summable fun l => E l ^ 2 := summable_sw_neg_sq _ hm
  set SE : ℝ := ∑' l, E l ^ 2 with hSE
  have hSE0 : 0 ≤ SE := tsum_nonneg fun l => sq_nonneg _
  set K : ℝ := (4 : ℝ) ^ (c / 2) with hK
  have hK0 : 0 ≤ K := by positivity
  refine ⟨2 * K * Real.sqrt SE, by positivity, fun f g hf hg => ?_⟩
  set Fn : Lattice d → ℝ := fun l => sobWeight (a / 2) l * ‖f l‖ with hFn
  set Gn : Lattice d → ℝ := fun l => sobWeight (b / 2) l * ‖g l‖ with hGn
  have hFn0 : ∀ l, 0 ≤ Fn l := fun l => mul_nonneg (sobWeight_pos _ _).le (norm_nonneg _)
  have hGn0 : ∀ l, 0 ≤ Gn l := fun l => mul_nonneg (sobWeight_pos _ _).le (norm_nonneg _)
  have hFn2 : Summable fun l => Fn l ^ 2 := hf.congr fun l => (sw_half_sq a l (f l)).symm
  have hGn2 : Summable fun l => Gn l ^ 2 := hg.congr fun l => (sw_half_sq b l (g l)).symm
  have hFnS : ∑' l, Fn l ^ 2 = hsNormSq a f := tsum_congr fun l => sw_half_sq a l (f l)
  have hGnS : ∑' l, Gn l ^ 2 = hsNormSq b g := tsum_congr fun l => sw_half_sq b l (g l)
  set H1 : Lattice d → ℝ := fun l => E l * Gn l with hH1
  set H2 : Lattice d → ℝ := fun l => E l * Fn l with hH2
  have hH10 : ∀ l, 0 ≤ H1 l := fun l => mul_nonneg (hE0 l) (hGn0 l)
  have hH20 : ∀ l, 0 ≤ H2 l := fun l => mul_nonneg (hE0 l) (hFn0 l)
  obtain ⟨hH1s, hH1le⟩ := Torus.cs_tsum E Gn hE0 hGn0 hE2 hGn2
  obtain ⟨hH2s, hH2le⟩ := Torus.cs_tsum E Fn hE0 hFn0 hE2 hFn2
  -- squares of the `ℓ¹` norms
  have hH1sq : (∑' l, H1 l) ^ 2 ≤ SE * hsNormSq b g := by
    have h0 : 0 ≤ ∑' l, H1 l := tsum_nonneg hH10
    calc (∑' l, H1 l) ^ 2 ≤ (Real.sqrt SE * Real.sqrt (hsNormSq b g)) ^ 2 := by
          rw [← hGnS]; exact pow_le_pow_left₀ h0 hH1le 2
      _ = SE * hsNormSq b g := by
          rw [mul_pow, Real.sq_sqrt hSE0, Real.sq_sqrt (hsNormSq_nonneg _ _)]
  have hH2sq : (∑' l, H2 l) ^ 2 ≤ SE * hsNormSq a f := by
    have h0 : 0 ≤ ∑' l, H2 l := tsum_nonneg hH20
    calc (∑' l, H2 l) ^ 2 ≤ (Real.sqrt SE * Real.sqrt (hsNormSq a f)) ^ 2 := by
          rw [← hFnS]; exact pow_le_pow_left₀ h0 hH2le 2
      _ = SE * hsNormSq a f := by
          rw [mul_pow, Real.sq_sqrt hSE0, Real.sq_sqrt (hsNormSq_nonneg _ _)]
  -- Young
  obtain ⟨hPs, hP2, hPle⟩ := young_real hH10 hFn0 hH1s hFn2
  obtain ⟨hQs, hQ2, hQle⟩ := young_real hH20 hGn0 hH2s hGn2
  set P : Lattice d → ℝ := fun k => ∑' j, H1 (k - j) * Fn j with hP
  set Q : Lattice d → ℝ := fun k => ∑' j, H2 (k - j) * Gn j with hQ
  have hP0 : ∀ k, 0 ≤ P k := fun k => tsum_nonneg fun j => mul_nonneg (hH10 _) (hFn0 _)
  have hQ0 : ∀ k, 0 ≤ Q k := fun k => tsum_nonneg fun j => mul_nonneg (hH20 _) (hGn0 _)
  set m := mulCoeff f g with hmdef
  -- the pointwise bound `S k ≤ K (P k + Q k)`
  have hS : ∀ k, sobWeight (c / 2) k * ‖m k‖ ≤ K * (P k + Q k) := by
    intro k
    have hw : 0 < sobWeight (c / 2) k := sobWeight_pos _ _
    have key : ∀ j, sobWeight (c / 2) k * (‖f (k - j)‖ * ‖g j‖) ≤
        K * (Fn (k - j) * H1 j + H2 (k - j) * Gn j) := fun j =>
      term_le a b c hc hac hbc f g k j
    have hs1 : Summable fun j => Fn (k - j) * H1 j := conv_swap_summable k (hPs k)
    have hs2 : Summable fun j => H2 (k - j) * Gn j := hQs k
    have hs12 : Summable fun j => K * (Fn (k - j) * H1 j + H2 (k - j) * Gn j) :=
      (hs1.add hs2).mul_left K
    have hsn : Summable fun j => ‖f (k - j)‖ * ‖g j‖ := by
      refine Summable.of_nonneg_of_le (fun j => mul_nonneg (norm_nonneg _) (norm_nonneg _))
        (fun j => ?_) (hs12.div_const (sobWeight (c / 2) k))
      rw [le_div_iff₀ hw]
      linarith [key j]
    have hsn' : Summable fun j => ‖f (k - j) * g j‖ := hsn.congr fun j => (norm_mul _ _).symm
    have h1 : ‖m k‖ ≤ ∑' j, ‖f (k - j)‖ * ‖g j‖ := by
      refine (norm_tsum_le_tsum_norm hsn').trans (le_of_eq (tsum_congr fun j => norm_mul _ _))
    calc sobWeight (c / 2) k * ‖m k‖ ≤ sobWeight (c / 2) k * ∑' j, ‖f (k - j)‖ * ‖g j‖ :=
          mul_le_mul_of_nonneg_left h1 hw.le
      _ = ∑' j, sobWeight (c / 2) k * (‖f (k - j)‖ * ‖g j‖) := (tsum_mul_left).symm
      _ ≤ ∑' j, K * (Fn (k - j) * H1 j + H2 (k - j) * Gn j) :=
          Summable.tsum_le_tsum key (hsn.mul_left _) hs12
      _ = K * (P k + Q k) := by
          rw [tsum_mul_left, (hs1.hasSum.add hs2.hasSum).tsum_eq, conv_swap_tsum]
  -- the summable majorant
  have hmaj : ∀ k, sobWeight c k * ‖m k‖ ^ 2 ≤ 2 * K ^ 2 * (P k ^ 2 + Q k ^ 2) := by
    intro k
    have h0 : 0 ≤ sobWeight (c / 2) k * ‖m k‖ := mul_nonneg (sobWeight_pos _ _).le (norm_nonneg _)
    have h2 : (sobWeight (c / 2) k * ‖m k‖) ^ 2 ≤ (K * (P k + Q k)) ^ 2 :=
      pow_le_pow_left₀ h0 (hS k) 2
    rw [← sw_half_sq c k (m k)]
    refine h2.trans ?_
    nlinarith [sq_nonneg (P k - Q k), sq_nonneg K]
  have hmajS : Summable fun k => 2 * K ^ 2 * (P k ^ 2 + Q k ^ 2) :=
    (hP2.add hQ2).mul_left _
  have hmem : MemHs c m :=
    Summable.of_nonneg_of_le (fun k => mul_nonneg (sobWeight_pos _ _).le (sq_nonneg _)) hmaj hmajS
  refine ⟨hmem, ?_⟩
  have hnormsq : hsNormSq c m ≤ 4 * K ^ 2 * SE * hsNormSq a f * hsNormSq b g := by
    have h1 : hsNormSq c m ≤ ∑' k, 2 * K ^ 2 * (P k ^ 2 + Q k ^ 2) :=
      hmem.tsum_le_tsum hmaj hmajS
    refine h1.trans ?_
    rw [tsum_mul_left, (hP2.hasSum.add hQ2.hasSum).tsum_eq]
    have hFa := hsNormSq_nonneg a f
    have hGb := hsNormSq_nonneg b g
    have hPb : ∑' k, P k ^ 2 ≤ SE * hsNormSq b g * hsNormSq a f := by
      refine hPle.trans ?_
      rw [hFnS]
      exact mul_le_mul_of_nonneg_right hH1sq hFa
    have hQb : ∑' k, Q k ^ 2 ≤ SE * hsNormSq a f * hsNormSq b g := by
      refine hQle.trans ?_
      rw [hGnS]
      exact mul_le_mul_of_nonneg_right hH2sq hGb
    have hK2 : 0 ≤ 2 * K ^ 2 := by positivity
    calc 2 * K ^ 2 * (∑' k, P k ^ 2 + ∑' k, Q k ^ 2)
        ≤ 2 * K ^ 2 * (SE * hsNormSq b g * hsNormSq a f + SE * hsNormSq a f * hsNormSq b g) :=
          mul_le_mul_of_nonneg_left (add_le_add hPb hQb) hK2
      _ = _ := by ring
  have hFs := hsNormSq_nonneg a f
  have hGs := hsNormSq_nonneg b g
  unfold hsNorm
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  have e : (2 * K * Real.sqrt SE * Real.sqrt (hsNormSq a f) * Real.sqrt (hsNormSq b g)) ^ 2 =
      4 * K ^ 2 * SE * hsNormSq a f * hsNormSq b g := by
    rw [mul_pow, mul_pow, mul_pow, mul_pow, Real.sq_sqrt hSE0, Real.sq_sqrt hFs, Real.sq_sqrt hGs]
    ring
  rw [e]
  exact hnormsq

/-! ### Lipschitz composition: `L²` and difference estimates -/

section Comp

variable {F : ℝ → ℝ} {L : ℝ≥0} {u : Torus d → ℝ}

private lemma memLp_ofReal_cont {φ : Torus d → ℝ} (hφ : Continuous φ) :
    MemLp (fun x => (φ x : ℂ)) 2 volume :=
  memLp_two_of_continuous (Complex.continuous_ofReal.comp hφ)

private lemma abs_comp_le (hF : LipschitzWith L F) (t : ℝ) : |F t| ≤ (L : ℝ) * |t| + |F 0| := by
  have h1 : |F t - F 0| ≤ (L : ℝ) * |t| := by
    have := hF.dist_le_mul t 0
    simpa [Real.dist_eq] using this
  calc |F t| = |(F t - F 0) + F 0| := by ring_nf
    _ ≤ |F t - F 0| + |F 0| := abs_add_le _ _
    _ ≤ _ := by linarith

private lemma l2_comp_le (hF : LipschitzWith L F) (hu : Continuous u) :
    ∫ x, ‖((F (u x) : ℝ) : ℂ)‖ ^ 2 ≤ 2 * (L : ℝ) ^ 2 * (∫ x, ‖(u x : ℂ)‖ ^ 2) + 2 * F 0 ^ 2 := by
  have hG : Continuous fun x => F (u x) := hF.continuous.comp hu
  have hint1 := (memLp_ofReal_cont hG).norm.integrable_sq
  have hint2 := (memLp_ofReal_cont hu).norm.integrable_sq
  calc ∫ x, ‖((F (u x) : ℝ) : ℂ)‖ ^ 2
      ≤ ∫ x, (2 * (L : ℝ) ^ 2 * ‖(u x : ℂ)‖ ^ 2 + 2 * F 0 ^ 2) := by
        refine integral_mono hint1 ((hint2.const_mul _).add (integrable_const _)) fun x => ?_
        simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]
        have h1 := abs_comp_le hF (u x)
        have h0 := abs_nonneg (F (u x))
        have h2 : (F (u x)) ^ 2 ≤ ((L : ℝ) * |u x| + |F 0|) ^ 2 := by
          rw [← sq_abs (F (u x))]
          exact pow_le_pow_left₀ h0 h1 2
        nlinarith [sq_nonneg ((L : ℝ) * |u x| - |F 0|), sq_abs (u x), sq_abs (F 0)]
    _ = 2 * (L : ℝ) ^ 2 * (∫ x, ‖(u x : ℂ)‖ ^ 2) + 2 * F 0 ^ 2 := by
        rw [integral_add (hint2.const_mul _) (integrable_const _), integral_const_mul]
        simp

private lemma diff_comp_le (hF : LipschitzWith L F) (hu : Continuous u) (h : Torus d) :
    Summable (fun k => ‖Torus.mode k h - 1‖ ^ 2 * ‖coeffOf (F ∘ u) k‖ ^ 2) ∧
    ∑' k, ‖Torus.mode k h - 1‖ ^ 2 * ‖coeffOf (F ∘ u) k‖ ^ 2 ≤
      (L : ℝ) ^ 2 * ∑' k, ‖Torus.mode k h - 1‖ ^ 2 * ‖coeffOf u k‖ ^ 2 := by
  have hG : Continuous (F ∘ u) := hF.continuous.comp hu
  obtain ⟨s1, e1⟩ := ProdAux.diff_parseval (memLp_ofReal_cont hG) h
  obtain ⟨s2, e2⟩ := ProdAux.diff_parseval (memLp_ofReal_cont hu) h
  refine ⟨s1, ?_⟩
  show ∑' k, ‖Torus.mode k h - 1‖ ^ 2 *
      ‖coeffOfC (fun x => (((F ∘ u) x : ℝ) : ℂ)) k‖ ^ 2 ≤ (L : ℝ) ^ 2 * ∑' k, ‖Torus.mode k h - 1‖ ^ 2 *
      ‖coeffOfC (fun x => ((u x : ℝ) : ℂ)) k‖ ^ 2
  rw [e1, e2, ← integral_const_mul]
  have hG1 := memLp_ofReal_cont hG
  have hu1 := memLp_ofReal_cont hu
  have hD1 := ((ProdAux.memLp_translate hG1 h).sub hG1).norm.integrable_sq
  have hD2 := ((ProdAux.memLp_translate hu1 h).sub hu1).norm.integrable_sq
  refine integral_mono hD1 (hD2.const_mul _) fun x => ?_
  simp only [Function.comp_apply]
  rw [← Complex.ofReal_sub, ← Complex.ofReal_sub, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]
  have := hF.dist_le_mul (u (x + h)) (u x)
  rw [Real.dist_eq, Real.dist_eq] at this
  have h2 := pow_le_pow_left₀ (abs_nonneg _) this 2
  rw [mul_pow, sq_abs, sq_abs] at h2
  exact h2

end Comp

/-! ### Lipschitz composition in `H^σ`, `0 ≤ σ < 1` -/

section Comp2

variable {F : ℝ → ℝ} {L : ℝ≥0} {u : Torus d → ℝ}

/-- `L²` part: `‖F ∘ u‖_{L²}² ≤ 2 L² ‖u‖²_{L²} + 2 F(0)²`, in coefficients. -/
private lemma l2_comp_coeff (hF : LipschitzWith L F) (hu : Continuous u) :
    MemHs 0 (coeffOf (F ∘ u)) ∧
      hsNormSq 0 (coeffOf (F ∘ u)) ≤
        2 * (L : ℝ) ^ 2 * hsNormSq 0 (coeffOf u) + 2 * F 0 ^ 2 := by
  have hG : Continuous (F ∘ u) := hF.continuous.comp hu
  obtain ⟨h1, h2⟩ := hsNormSq_zero_coeffOfC _ (memLp_ofReal_cont hG)
  obtain ⟨h3, h4⟩ := hsNormSq_zero_coeffOfC _ (memLp_ofReal_cont hu)
  refine ⟨h1, ?_⟩
  show hsNormSq 0 (coeffOfC (fun x => (((F ∘ u) x : ℝ) : ℂ))) ≤
    2 * (L : ℝ) ^ 2 * hsNormSq 0 (coeffOfC (fun x => ((u x : ℝ) : ℂ))) + 2 * F 0 ^ 2
  rw [h2, h4]
  exact l2_comp_le hF hu

private lemma comp_sq_trivial {σ : ℝ} (hW : ∀ k : Lattice d, sobWeight σ k = 1)
    (hF : LipschitzWith L F) (hu : Continuous u) (_hv : MemHs σ (coeffOf u)) :
    MemHs σ (coeffOf (F ∘ u)) ∧
      hsNormSq σ (coeffOf (F ∘ u)) ≤ 2 * ((L : ℝ) ^ 2 * hsNormSq σ (coeffOf u) + F 0 ^ 2) := by
  have e1 : ∀ c : Coeff d, hsNormSq σ c = hsNormSq 0 c := fun c => by
    simp [hsNormSq, hW, sobWeight_zero]
  have e2 : ∀ c : Coeff d, MemHs σ c ↔ MemHs 0 c := fun c => by
    simp [MemHs, hW, sobWeight_zero]
  obtain ⟨h1, h2⟩ := l2_comp_coeff hF hu
  refine ⟨(e2 _).2 h1, ?_⟩
  rw [e1, e1]
  linarith

private theorem comp_core (hd : 1 ≤ d) (σ : ℝ) (h0 : 0 < σ) (h1 : σ < 1) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (L : ℝ≥0) (F : ℝ → ℝ), LipschitzWith L F → ∀ u : Torus d → ℝ,
      Continuous u → MemHs σ (coeffOf u) →
      MemHs σ (coeffOf (F ∘ u)) ∧
        hsNormSq σ (coeffOf (F ∘ u)) ≤ M * ((L : ℝ) ^ 2 * hsNormSq σ (coeffOf u) + F 0 ^ 2) := by
  obtain ⟨U, hU0, hU⟩ := ProdAux.upper_vec (d := d) σ h0 h1
  obtain ⟨L₀, hL1, hL⟩ := ProdAux.lower_vec' hd σ h0.le
  set r : ℝ := (4 : ℝ) ^ σ with hr
  have hL0 : 0 ≤ L₀ := by linarith
  refine ⟨L₀ * (2 + U), by positivity, fun L F hF u hu hv => ?_⟩
  set v := coeffOf u with hvdef
  set m := coeffOf (F ∘ u) with hmdef
  set X := hsNormSq σ v with hX
  have hX0 : 0 ≤ X := hsNormSq_nonneg _ _
  have hv0 := ProdAux.memHs_zero_of_memHs h0.le hv
  have hvσ := ProdAux.hsNormSq_zero_le h0.le hv
  obtain ⟨hm0, hmA'⟩ := l2_comp_coeff hF hu
  have hmA : hsNormSq 0 m ≤ 2 * (L : ℝ) ^ 2 * X + 2 * F 0 ^ 2 := by
    refine hmA'.trans ?_
    have : 0 ≤ (L : ℝ) ^ 2 := sq_nonneg _
    nlinarith
  have hbound : ∀ S : Finset (Lattice d), ∑ k ∈ S, sobWeight σ k * ‖m k‖ ^ 2 ≤
      L₀ * (2 + U) * ((L : ℝ) ^ 2 * X + F 0 ^ 2) := by
    intro S
    obtain ⟨N, hN⟩ := hL S
    have step1 : ∑ k ∈ S, sobWeight σ k * ‖m k‖ ^ 2 ≤
        ∑ k ∈ S, L₀ * (1 + ∑ i : Fin d, ∑ n ∈ Finset.range N,
          r ^ n * ‖Torus.mode k (ProdAux.shift n i) - 1‖ ^ 2) * ‖m k‖ ^ 2 :=
      Finset.sum_le_sum fun k hk => by
        have := hN k hk
        calc sobWeight σ k * ‖m k‖ ^ 2 ≤ (L₀ * (1 + ∑ i : Fin d, ∑ n ∈ Finset.range N,
            r ^ n * ‖Torus.mode k (ProdAux.shift n i) - 1‖ ^ 2)) * ‖m k‖ ^ 2 :=
              mul_le_mul_of_nonneg_right this (sq_nonneg _)
          _ = _ := by ring
    have step2 : ∑ k ∈ S, L₀ * (1 + ∑ i : Fin d, ∑ n ∈ Finset.range N,
        r ^ n * ‖Torus.mode k (ProdAux.shift n i) - 1‖ ^ 2) * ‖m k‖ ^ 2 =
        L₀ * (∑ k ∈ S, ‖m k‖ ^ 2 + ∑ i : Fin d, ∑ n ∈ Finset.range N,
          r ^ n * ∑ k ∈ S, ‖Torus.mode k (ProdAux.shift n i) - 1‖ ^ 2 * ‖m k‖ ^ 2) := by
      rw [← ProdAux.finset_rearrange r m S N, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => by ring
    have hE : ∀ (i : Fin d) (n : ℕ), ∑ k ∈ S, ‖Torus.mode k (ProdAux.shift n i) - 1‖ ^ 2 * ‖m k‖ ^ 2 ≤
        (L : ℝ) ^ 2 * ∑' k, ‖Torus.mode k (ProdAux.shift n i) - 1‖ ^ 2 * ‖v k‖ ^ 2 := by
      intro i n
      obtain ⟨hs, hle⟩ := diff_comp_le hF hu (ProdAux.shift n i)
      exact (hs.sum_le_tsum S (fun k _ => by positivity)).trans hle
    have step3 : ∑ i : Fin d, ∑ n ∈ Finset.range N,
        r ^ n * ∑ k ∈ S, ‖Torus.mode k (ProdAux.shift n i) - 1‖ ^ 2 * ‖m k‖ ^ 2 ≤
        (L : ℝ) ^ 2 * (U * X) := by
      calc _ ≤ ∑ i : Fin d, ∑ n ∈ Finset.range N, r ^ n *
            ((L : ℝ) ^ 2 * ∑' k, ‖Torus.mode k (ProdAux.shift n i) - 1‖ ^ 2 * ‖v k‖ ^ 2) :=
            Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun n _ =>
              mul_le_mul_of_nonneg_left (hE i n) (by positivity)
        _ = (L : ℝ) ^ 2 * ∑ i : Fin d, ∑ n ∈ Finset.range N,
              r ^ n * ∑' k, ‖Torus.mode k (ProdAux.shift n i) - 1‖ ^ 2 * ‖v k‖ ^ 2 := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun n _ => ?_
            ring
        _ ≤ (L : ℝ) ^ 2 * (U * X) :=
            mul_le_mul_of_nonneg_left (ProdAux.claim1 h0.le hU hv N) (sq_nonneg _)
    have hS0 : ∑ k ∈ S, ‖m k‖ ^ 2 ≤ hsNormSq 0 m := ProdAux.sum_le_tsum_sq hm0 S
    have hL2 : 0 ≤ (L : ℝ) ^ 2 := sq_nonneg _
    have hF2 : 0 ≤ F 0 ^ 2 := sq_nonneg _
    calc ∑ k ∈ S, sobWeight σ k * ‖m k‖ ^ 2
        ≤ L₀ * (hsNormSq 0 m + (L : ℝ) ^ 2 * (U * X)) := by
          refine step1.trans (le_of_eq step2 |>.trans ?_)
          exact mul_le_mul_of_nonneg_left (add_le_add hS0 step3) hL0
      _ ≤ L₀ * (2 * (L : ℝ) ^ 2 * X + 2 * F 0 ^ 2 + (L : ℝ) ^ 2 * (U * X)) := by
          apply mul_le_mul_of_nonneg_left _ hL0
          linarith
      _ ≤ L₀ * (2 + U) * ((L : ℝ) ^ 2 * X + F 0 ^ 2) := by
          have h1 : 0 ≤ U * F 0 ^ 2 := mul_nonneg hU0 hF2
          have h2 : 2 * (L : ℝ) ^ 2 * X + 2 * F 0 ^ 2 + (L : ℝ) ^ 2 * (U * X) ≤
              (2 + U) * ((L : ℝ) ^ 2 * X + F 0 ^ 2) := by nlinarith
          calc _ ≤ L₀ * ((2 + U) * ((L : ℝ) ^ 2 * X + F 0 ^ 2)) :=
                mul_le_mul_of_nonneg_left h2 hL0
            _ = _ := by ring
  exact memHs_of_sum_le hbound

/-- Lipschitz composition, squared form, for all `0 ≤ σ < 1`. -/
private theorem comp_sq (σ : ℝ) (hσ0 : 0 ≤ σ) (hσ1 : σ < 1) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (L : ℝ≥0) (F : ℝ → ℝ), LipschitzWith L F → ∀ u : Torus d → ℝ,
      Continuous u → MemHs σ (coeffOf u) →
      MemHs σ (coeffOf (F ∘ u)) ∧
        hsNormSq σ (coeffOf (F ∘ u)) ≤ M * ((L : ℝ) ^ 2 * hsNormSq σ (coeffOf u) + F 0 ^ 2) := by
  by_cases hcase : σ = 0 ∨ d = 0
  · refine ⟨2, by norm_num, fun L F hF u hu hv => ?_⟩
    refine comp_sq_trivial (fun k => ?_) hF hu hv
    rcases hcase with h | h
    · rw [h, sobWeight_zero]
    · subst h
      have h0 : Lattice.toEuc k = 0 := Subsingleton.elim _ _
      have : Lattice.enorm k = 0 := by
        simp [Lattice.enorm, h0]
      simp [sobWeight, this]
  · push Not at hcase
    exact comp_core (Nat.one_le_iff_ne_zero.2 hcase.2) σ (lt_of_le_of_ne hσ0 (Ne.symm hcase.1)) hσ1

end Comp2

/-- **Lipschitz composition in `H^σ`** (`0 ≤ σ < 1`), `ℝ≥0`-Lipschitz-constant form: if `F` is
`L`-Lipschitz and `u` is continuous with `û ∈ H^σ`, then `\widehat{F ∘ u} ∈ H^σ` and
`‖F ∘ u‖_{H^σ} ≤ C (L ‖u‖_{H^σ} + |F 0|)`. -/
theorem exists_lipschitz_comp_bound_nnreal (σ : ℝ) (hσ0 : 0 ≤ σ) (hσ1 : σ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (L : ℝ≥0) (F : ℝ → ℝ), LipschitzWith L F →
      ∀ u : Torus d → ℝ, Continuous u → MemHs σ (coeffOf u) →
        MemHs σ (coeffOf (F ∘ u)) ∧
          hsNorm σ (coeffOf (F ∘ u)) ≤ C * ((L : ℝ) * hsNorm σ (coeffOf u) + |F 0|) := by
  obtain ⟨M, hM0, hM⟩ := comp_sq (d := d) σ hσ0 hσ1
  refine ⟨Real.sqrt M, Real.sqrt_nonneg _, fun L F hF u hu hv => ?_⟩
  obtain ⟨hmem, hle⟩ := hM L F hF u hu hv
  refine ⟨hmem, ?_⟩
  unfold hsNorm
  rw [Real.sqrt_le_iff]
  have hX := hsNormSq_nonneg σ (coeffOf u)
  have hLr : 0 ≤ (L : ℝ) := L.2
  refine ⟨by positivity, ?_⟩
  have e : (Real.sqrt M * ((L : ℝ) * Real.sqrt (hsNormSq σ (coeffOf u)) + |F 0|)) ^ 2 =
      M * (((L : ℝ) * Real.sqrt (hsNormSq σ (coeffOf u)) + |F 0|) ^ 2) := by
    rw [mul_pow, Real.sq_sqrt hM0]
  rw [e]
  refine hle.trans (mul_le_mul_of_nonneg_left ?_ hM0)
  have hs : Real.sqrt (hsNormSq σ (coeffOf u)) ^ 2 = hsNormSq σ (coeffOf u) := Real.sq_sqrt hX
  have h1 : 0 ≤ (L : ℝ) * Real.sqrt (hsNormSq σ (coeffOf u)) := by positivity
  nlinarith [sq_abs (F 0), abs_nonneg (F 0), mul_nonneg h1 (abs_nonneg (F 0))]

/-- **Lipschitz composition in `H^σ`**, in the form of packet P3 with a nonnegative real
Lipschitz constant.  The plan's statement quantifies over *all* real `L` with
`LipschitzWith (Real.toNNReal L) F` and is false for `L < 0` (take `F` constant, `L = -1000`,
`u ≡ 1000`: then `‖F ∘ u‖ = |F 0| > 0 > C (L ‖u‖ + |F 0|)`); the hypothesis `0 ≤ L` repairs it. -/
theorem exists_lipschitz_comp_bound_of_nonneg (σ : ℝ) (hσ0 : 0 ≤ σ) (hσ1 : σ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (L : ℝ) (F : ℝ → ℝ), 0 ≤ L → LipschitzWith (Real.toNNReal L) F →
      ∀ u : Torus d → ℝ, Continuous u → MemHs σ (coeffOf u) →
        MemHs σ (coeffOf (F ∘ u)) ∧
          hsNorm σ (coeffOf (F ∘ u)) ≤ C * (L * hsNorm σ (coeffOf u) + |F 0|) := by
  obtain ⟨C, hC0, hC⟩ := exists_lipschitz_comp_bound_nnreal (d := d) σ hσ0 hσ1
  refine ⟨C, hC0, fun L F hL hF u hu hv => ?_⟩
  have := hC (Real.toNNReal L) F hF u hu hv
  rwa [Real.coe_toNNReal L hL] at this

end HRS.PDE.MFProduct

