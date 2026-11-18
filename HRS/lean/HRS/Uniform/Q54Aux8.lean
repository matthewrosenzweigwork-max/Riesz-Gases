import HRS.Uniform.Q54Aux7
import HRS.PDE.EnergyTorusLimit

/-!
# Q54, part 8: from trigonometric polynomials to `H^{a+2}` (real index `a`)

* `gen_hs_bound` (E1 extended): `𝓛` maps `H^{a+2} ∩ H^1` into `H^a`, `‖𝓛u‖²_a ≤ (2ν²+C) ‖u‖²_{a+2}`;
* `gen_form` (E2 extended): `Re ⟨𝓛u, u⟩_a ≤ C ‖u‖²_a - (ν₀/2) ‖u‖²_{a+1}` for `u ∈ H^{a+2} ∩ H^1`.

(`H^1` is only needed to define the nonlocal terms by absolutely convergent sums; for `a ≥ -1` it is automatic.)
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.Uniform.Q54

open HRS HRS.PDE HRS.PDE.ET

variable {d : ℕ}

theorem summable_jp_neg {q : ℝ} (hq : (d : ℝ) < q) : Summable fun k : Lattice d => Lattice.jp k ^ (-q) := by
  rw [Torus.summable_lattice_iff]
  have := HRS.summable_jp_rpow (d := d) (q / 2) (by linarith)
  refine this.congr fun k => ?_
  congr 1
  ring

theorem memHs_of_decay {c : Coeff d} {B q r : ℝ} (hdec : ∀ m, ‖c m‖ ≤ B * Lattice.jp m ^ (-q))
    (hq : (d : ℝ) / 2 + r < q) : MemHs r c := by
  have hs := (summable_jp_neg (d := d) (q := 2 * q - 2 * r) (by linarith)).mul_left (B ^ 2)
  refine Summable.of_nonneg_of_le (fun k => mul_nonneg (sobWeight_nonnegE r k) (sq_nonneg _))
    (fun k => ?_) hs
  have hjp := Torus.jp_pos k
  rw [sobWeight_eq_jp]
  have h1 : ‖c k‖ ^ 2 ≤ (B * Lattice.jp k ^ (-q)) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (hdec k) 2
  calc Lattice.jp k ^ (2 * r) * ‖c k‖ ^ 2 ≤ Lattice.jp k ^ (2 * r) * (B * Lattice.jp k ^ (-q)) ^ 2 :=
        mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hjp.le _)
    _ = B ^ 2 * Lattice.jp k ^ (-(2 * q - 2 * r)) := by
        rw [mul_pow, Torus.jp_rpow_sq]
        have e : Lattice.jp k ^ (2 * r) * Lattice.jp k ^ (2 * (-q)) = Lattice.jp k ^ (-(2 * q - 2 * r)) := by
          rw [← Real.rpow_add hjp]; congr 1; ring
        calc Lattice.jp k ^ (2 * r) * (B ^ 2 * Lattice.jp k ^ (2 * (-q)))
            = B ^ 2 * (Lattice.jp k ^ (2 * r) * Lattice.jp k ^ (2 * (-q))) := by ring
          _ = _ := by rw [e]

theorem genHyp_memHs0 {s K MB Bμ BV : ℝ} (hsd : s < d) {D : DynData d} {μ : Torus d → ℝ}
    (h : GenHyp d s K MB Bμ BV D μ) (hK : (d : ℝ) / 2 + 1 < K) (hMB : 0 ≤ MB) (hBμ : 0 ≤ Bμ)
    (hBV : 0 ≤ BV) :
    MemHs 0 (coeffOf μ) ∧ ∀ j, MemHs 0 (driftCoeff D μ j) := by
  refine ⟨memHs_of_decay h.hμ (by linarith), fun j => ?_⟩
  refine memHs_of_decay (B := ((d : ℝ) * MB * Cg d s * Bμ + BV)) (q := K - 1) (fun m => ?_) (by linarith)
  have := drift_bound hsd h j m
  rwa [show -(K - 1) = 1 - K by ring]

theorem gen_hs_bound (s : ℝ) (hsd : s < d) (K MB Bμ BV : ℝ) (hMB : 0 ≤ MB) (hBμ : 0 ≤ Bμ)
    (hBV : 0 ≤ BV) (a : ℝ) (hK : (d : ℝ) + |a| + 4 ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : DynData d) (μ : Torus d → ℝ), GenHyp d s K MB Bμ BV D μ →
      ∀ u : Coeff d, MemHs (a + 2) u → MemHs 1 u →
        MemHs a (forwardGen D μ u) ∧
          hsNormSq a (forwardGen D μ u) ≤ (2 * D.invβ ^ 2 + C) * hsNormSq (a + 2) u := by
  obtain ⟨C, hC, hE1⟩ := gen_trig_bound s hsd K MB Bμ BV hMB hBμ hBV a hK
  refine ⟨C, hC, fun D μ h u hu hu1 => ?_⟩
  obtain ⟨h0, hdr⟩ := genHyp_memHs0 hsd h (by linarith [abs_nonneg a, Nat.cast_nonneg (α := ℝ) d]) hMB hBμ hBV
  have hc0 : 0 ≤ 2 * D.invβ ^ 2 + C := by positivity
  have hS : ∀ S : Finset (Lattice d), ∑ k ∈ S, sobWeight a k * ‖forwardGen D μ u k‖ ^ 2 ≤
      (2 * D.invβ ^ 2 + C) * hsNormSq (a + 2) u := by
    intro S
    have hlim : Tendsto (fun n : ℕ => ∑ k ∈ S, sobWeight a k *
        ‖forwardGen D μ (truncCoeff n u) k‖ ^ 2) atTop
        (𝓝 (∑ k ∈ S, sobWeight a k * ‖forwardGen D μ u k‖ ^ 2)) := by
      refine tendsto_finsetSum S fun k _ => ?_
      refine Tendsto.const_mul _ (Tendsto.pow (Tendsto.norm ?_) 2)
      refine tendsto_forwardGen D μ h0 hdr (fun n : ℕ => truncCoeff n u) u
        (Real.sqrt (hsNormSq 1 u)) (Real.sqrt_nonneg _) ?_ (tendsto_truncCoeff_coord u) k
      refine Filter.Eventually.of_forall fun n T => ?_
      rw [Real.sq_sqrt (hsNormSq_nonnegE _ _)]
      refine le_trans (Finset.sum_le_sum fun k _ => ?_) (sum_le_hsNormSq hu1 T)
      by_cases hk : InBox n k
      · simp [truncCoeff, hk]
      · simp [truncCoeff, hk]
        exact mul_nonneg (sobWeight_nonnegE _ _) (sq_nonneg _)
    refine le_of_tendsto' hlim fun n => ?_
    refine (hE1 D μ h n (truncCoeff n u) (isTrigPoly_truncCoeff n u) S).trans ?_
    exact mul_le_mul_of_nonneg_left (hsNormSq_truncCoeff_le n hu) hc0
  exact memHs_of_sum_le hS

/-- **L1** at a real index. -/
theorem tendsto_hsInner_gen_trunc' (s : ℝ) (hsd : s < d) (K MB Bμ BV : ℝ) (hMB : 0 ≤ MB) (hBμ : 0 ≤ Bμ)
    (hBV : 0 ≤ BV) (a : ℝ) (hK : (d : ℝ) + |a| + 4 ≤ K) (D : DynData d) (μ : Torus d → ℝ)
    (h : GenHyp d s K MB Bμ BV D μ) (G : Coeff d) (hG : MemHs (a + 2) G) (hG1 : MemHs 1 G) :
    Tendsto (fun n : ℕ => (hsInner a (forwardGen D μ (truncCoeff n G)) (truncCoeff n G)).re)
      atTop (𝓝 (hsInner a (forwardGen D μ G) G).re) := by
  obtain ⟨C, hC, hE1⟩ := gen_trig_bound s hsd K MB Bμ BV hMB hBμ hBV a hK
  have ha2 : a ≤ a + 2 := by linarith
  have hGm : MemHs a G := hG.mono ha2
  set P : ℕ → Coeff d := fun n => truncCoeff n G with hP
  have hPm2 : ∀ n, MemHs (a + 2) (P n) := fun n => memHs_of_isTrigPolyE (isTrigPoly_truncCoeff n G) _
  have hPm : ∀ n, MemHs a (P n) := fun n => (hPm2 n).mono ha2
  have hP1 : ∀ n, MemHs 1 (P n) := fun n => memHs_of_isTrigPolyE (isTrigPoly_truncCoeff n G) _
  have hgen : ∀ n, MemHs a (forwardGen D μ (P n)) ∧
      hsNormSq a (forwardGen D μ (P n)) ≤ (2 * D.invβ ^ 2 + C) * hsNormSq (a + 2) (P n) := fun n =>
    memHs_of_sum_le fun S => hE1 D μ h n (P n) (isTrigPoly_truncCoeff n G) S
  set c3 := 2 * D.invβ ^ 2 + C with hc3
  have hc30 : 0 ≤ c3 := by positivity
  set B := Real.sqrt (c3 * hsNormSq (a + 2) G) with hBdef
  have hB0 : 0 ≤ B := Real.sqrt_nonneg _
  have hbd : ∀ n, hsNormSq a (forwardGen D μ (P n)) ≤ B ^ 2 := by
    intro n
    rw [hBdef, Real.sq_sqrt (mul_nonneg hc30 (hsNormSq_nonnegE _ _))]
    refine (hgen n).2.trans (mul_le_mul_of_nonneg_left ?_ hc30)
    exact (truncCoeff_tendsto _ G hG).1 n
  obtain ⟨h0, hdr⟩ := genHyp_memHs0 hsd h (by linarith [abs_nonneg a, Nat.cast_nonneg (α := ℝ) d]) hMB hBμ hBV
  set Kc := hsNormSq 0 (coeffOf μ) + ∑ j, hsNormSq 0 (driftCoeff D μ j) with hKc
  have hKc0 : 0 ≤ Kc := add_nonneg (hsNormSq_nonnegE _ _)
    (Finset.sum_nonneg fun j _ => hsNormSq_nonnegE _ _)
  have hcoord : ∀ k, Tendsto (fun n => forwardGen D μ (P n) k) atTop (𝓝 (forwardGen D μ G k)) := by
    intro k
    refine tendsto_forwardGen_both (l := atTop) D (fun _ : ℕ => μ) μ Kc hKc0 (fun _ => h0)
      (fun _ => le_add_of_nonneg_right (Finset.sum_nonneg fun j _ => hsNormSq_nonnegE _ _))
      (fun _ => tendsto_const_nhds) (fun _ j => hdr j)
      (fun _ j => (Finset.single_le_sum (f := fun j => hsNormSq 0 (driftCoeff D μ j))
        (fun j _ => hsNormSq_nonnegE _ _) (Finset.mem_univ j)).trans
        (le_add_of_nonneg_left (hsNormSq_nonnegE _ _)))
      (fun j q => tendsto_const_nhds) P G hP1 hG1 ?_ k
    have := tendsto_hsNormSq_sub_trunc 1 G hG1
    exact this.congr fun n => (hsNormSq_trunc_sub 1 G n).symm
  have hweak := tendsto_hsInner_weak (fun n => forwardGen D μ (P n)) (forwardGen D μ G) G B hB0 hbd
    (fun n => (hgen n).1) hGm hcoord
  have hrem : Tendsto (fun n => hsInner a (forwardGen D μ (P n)) (G - P n)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have h1 := tendsto_hsNormSq_sub_trunc a G hGm
    have h2 : Tendsto (fun n => B * Real.sqrt (hsNormSq a (G - P n))) atTop (𝓝 0) := by
      have := ((Real.continuous_sqrt.tendsto 0).comp h1).const_mul B
      simpa using this
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) h2
    obtain ⟨hmem, -⟩ := memHs_sub_sq hGm (hPm n)
    refine (norm_hsInner_le (hgen n).1 hmem).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
    calc Real.sqrt (hsNormSq a (forwardGen D μ (P n))) ≤ Real.sqrt (B ^ 2) :=
          Real.sqrt_le_sqrt (hbd n)
      _ = B := Real.sqrt_sq hB0
  have hdiff := hweak.sub hrem
  rw [sub_zero] at hdiff
  refine (Complex.continuous_re.tendsto _ |>.comp hdiff).congr fun n => ?_
  simp only [Function.comp]
  congr 1
  rw [hsInner_sub_right (hgen n).1 hGm (hPm n)]
  ring

theorem gen_form (s : ℝ) (hsd : s < d) (K MB Bμ BV : ℝ) (hMB : 0 ≤ MB) (hBμ : 0 ≤ Bμ)
    (hBV : 0 ≤ BV) (a : ℝ) (hK : (d : ℝ) + |a| + 4 ≤ K) (ν₀ : ℝ) (hν₀ : 0 < ν₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : DynData d) (μ : Torus d → ℝ), GenHyp d s K MB Bμ BV D μ → ν₀ ≤ D.invβ →
      ∀ u : Coeff d, MemHs (a + 2) u → MemHs 1 u →
        (hsInner a (forwardGen D μ u) u).re ≤ C * hsNormSq a u - (ν₀ / 2) * hsNormSq (a + 1) u := by
  obtain ⟨C, hC, hE2⟩ := gen_form_trig s hsd K MB Bμ BV hMB hBμ hBV a hK ν₀ hν₀
  refine ⟨C, hC, fun D μ h hν u hu hu1 => ?_⟩
  have hua : MemHs a u := hu.mono (by linarith)
  have hua1 : MemHs (a + 1) u := hu.mono (by linarith)
  have hlim := tendsto_hsInner_gen_trunc' s hsd K MB Bμ BV hMB hBμ hBV a hK D μ h u hu hu1
  have h1 := tendsto_hsNormSq_trunc a u hua
  have h2 := tendsto_hsNormSq_trunc (a + 1) u hua1
  have hR : Tendsto (fun n : ℕ => C * hsNormSq a (truncCoeff n u) -
      (ν₀ / 2) * hsNormSq (a + 1) (truncCoeff n u)) atTop
      (𝓝 (C * hsNormSq a u - (ν₀ / 2) * hsNormSq (a + 1) u)) :=
    (h1.const_mul C).sub (h2.const_mul (ν₀ / 2))
  exact le_of_tendsto_of_tendsto hlim hR (Filter.Eventually.of_forall fun n =>
    hE2 D μ h hν n (truncCoeff n u) (isTrigPoly_truncCoeff n u))

end HRS.Uniform.Q54
