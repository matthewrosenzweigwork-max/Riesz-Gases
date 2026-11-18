import HRS.PDE.MeanFieldProduct
import HRS.PDE.MeanFieldProductB
import HRS.PDE.MeanFieldInputs
import HRS.PDE.MeanFieldThermalUnique

/-!
# Regularity of the thermal density (package MF-01, packet P4)

For a continuous positive thermal density `ρ` (`log ρ = -β (V + g ⋆ ρ) + c`, `MFThermal.log_thermal`)
with `V ∈ C^{K+2}` and `s < d/2 + 1` we prove `ρ ∈ H^K` (`thermal_memSobolev_of_lt`) and, for
smooth `V`, `ρ ∈ C^∞` (`thermal_isSmooth_of_lt`).

Route (all coefficient-side):

* smoothing: `ρ ∈ H^a ⇒ g ⋆ ρ ∈ H^{a+δ}`, `δ = d - s > 0` (`|ĝ(k)| ≲ ⟨k⟩^{-δ}`);
* Lipschitz stage: `ρ = exp(w)` with `w` bounded, `w ∈ H^τ`, `τ < 1`, gives `ρ ∈ H^τ`
  (`exists_lipschitz_comp_bound_of_nonneg`); iterating reaches `H^{σ₁}`, `σ₁ + δ > d/2`
  (this is where `s < d/2 + 1` enters);
* Moser stage: `ρ = e^{-βV} · exp(c - β g⋆ρ)`; the second factor lies in `H^{a+δ}` (`exp` in `H^b`,
  `b > d/2`, by the series and the Fourier–Moser product bound), the first one in `H^{K+2}`
  (`V ∈ C^{K+2}`), and `exists_product_bound` gives `ρ ∈ H^{min(a+δ, K+2)}`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.PDE.MFThermalReg

variable {d : ℕ}

/-! ### Elementary coefficient facts -/

theorem integrable_of_cont {φ : Torus d → ℝ} (h : Continuous φ) : Integrable φ :=
  MFThermal.integrable_of_continuous h

theorem coeffOf_add_fun {φ ψ : Torus d → ℝ} (hφ : Continuous φ) (hψ : Continuous ψ)
    (k : Lattice d) :
    coeffOf (fun x => φ x + ψ x) k = coeffOf φ k + coeffOf ψ k := by
  unfold coeffOf
  rw [funFourierCoeff_eq_int, funFourierCoeff_eq_int, funFourierCoeff_eq_int]
  push_cast
  simp_rw [mul_add]
  exact integral_add (MFAux.integrable_mode_mul_real' (-k) (integrable_of_cont hφ))
    (MFAux.integrable_mode_mul_real' (-k) (integrable_of_cont hψ))

theorem coeffOf_const_mul_fun (a : ℝ) (φ : Torus d → ℝ) (k : Lattice d) :
    coeffOf (fun x => a * φ x) k = (a : ℂ) * coeffOf φ k := by
  unfold coeffOf
  rw [funFourierCoeff_eq_int, funFourierCoeff_eq_int]
  push_cast
  simp_rw [mul_left_comm _ (a : ℂ)]
  exact integral_const_mul _ _

theorem memHs_smul {m : ℝ} {c : Coeff d} (hc : MemHs m c) (a : ℂ) :
    MemHs m (fun k => a * c k) := by
  unfold MemHs at *
  refine (hc.mul_left (‖a‖ ^ 2)).congr fun k => ?_
  simp only [norm_mul]
  ring

theorem memHs_add {m : ℝ} {x y : Coeff d} (hx : MemHs m x) (hy : MemHs m y) :
    MemHs m (fun k => x k + y k) :=
  (ProdAux.hsNormSq_add_le m hx hy).1

theorem toFun_coeffOf {φ : Torus d → ℝ} (hφ : Continuous φ)
    (hs : Summable fun k => ‖coeffOf φ k‖) : toFun (coeffOf φ) = φ := by
  have hr : IsRealCoeff (coeffOf φ) := isRealCoeff_coeffOf φ (integrable_of_cont hφ)
  have h1 := coeffOf_toFun (coeffOf φ) hr hs
  exact MFAux.eq_of_funFourierCoeff_eq (MFProduct.continuous_toFun _ hs) hφ (fun k => by
    have := congrFun h1 k
    exact this)

/-- `C^n` functions have coefficients in `H^n`. -/
theorem memHs_of_isCk : ∀ (n : ℕ) (b : Torus d → ℝ), Torus.IsCk (n : WithTop ℕ∞) b →
    MemHs (n : ℝ) (coeffOf b)
  | 0, b, hb => by
    have hc : Continuous b := continuous_of_lift' hb.continuous
    simpa using (coeffOf_memHs_zero hc).1
  | n + 1, b, hb => by
    have hb1 : Torus.IsCk 1 b := hb.of_le (by exact_mod_cast Nat.le_add_left 1 n)
    have hbn : Torus.IsCk (n : WithTop ℕ∞) b := hb.of_le (by exact_mod_cast Nat.le_succ n)
    have e : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    rw [e, ProdAux.memHs_succ_iff]
    refine ⟨memHs_of_isCk n b hbn, fun j => ?_⟩
    rw [← coeffOf_partialDeriv_eq j b hb1]
    exact memHs_of_isCk n _ (ProdAux.isCk_partialDeriv hb j)


/-! ### The smoothing estimate for the Riesz coefficients -/

theorem abs_rieszCoeff_le_sobWeight (s : ℝ) (hsd : s < d) (k : Lattice d) :
    |rieszCoeff d s k| ≤ |rieszConst d s| * (2 : ℝ) ^ (((d : ℝ) - s) / 2) *
      sobWeight (-(((d : ℝ) - s) / 2)) k := by
  by_cases hk : k = 0
  · have : rieszCoeff d s k = 0 := by simp [rieszCoeff, hk]
    rw [this, abs_zero]
    have := MFProduct.sobWeight_nonneg (-(((d : ℝ) - s) / 2)) k
    positivity
  · have h1 : 1 ≤ Lattice.enorm k := one_le_enorm k hk
    set r : ℝ := 2 * Real.pi * Lattice.enorm k with hr
    have hr1 : 1 ≤ r := by nlinarith [Real.pi_gt_three]
    have hr0 : 0 < r := by linarith
    have hB : 1 + 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2 = 1 + r ^ 2 := by rw [hr]; ring
    set e : ℝ := -(((d : ℝ) - s) / 2) with he
    have he0 : e ≤ 0 := by have : (0 : ℝ) < d - s := by linarith
                           rw [he]; linarith
    have hrc : rieszCoeff d s k = rieszConst d s * r ^ (s - (d : ℝ)) := by
      simp [rieszCoeff, hk, hr]
    have hbase : 2 * r ^ 2 ≥ 1 + r ^ 2 := by nlinarith
    have hmono : (2 * r ^ 2) ^ e ≤ (1 + r ^ 2) ^ e :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hbase he0
    have hexp : (2 * r ^ 2) ^ e = (2 : ℝ) ^ e * r ^ (s - (d : ℝ)) := by
      rw [Real.mul_rpow (by norm_num) (by positivity)]
      congr 1
      rw [← Real.rpow_natCast, ← Real.rpow_mul hr0.le]
      congr 1
      rw [he]; push_cast; ring
    have h2e : (2 : ℝ) ^ (((d : ℝ) - s) / 2) * (2 : ℝ) ^ e = 1 := by
      rw [← Real.rpow_add (by norm_num)]
      rw [he]; simp
    have hsw : sobWeight e k = (1 + r ^ 2) ^ e := by
      unfold sobWeight; rw [hB]
    rw [hrc, abs_mul, abs_of_nonneg (Real.rpow_nonneg hr0.le _), hsw]
    have hpos : 0 ≤ (2 : ℝ) ^ (((d : ℝ) - s) / 2) := by positivity
    calc |rieszConst d s| * r ^ (s - (d : ℝ))
        = |rieszConst d s| * ((2 : ℝ) ^ (((d : ℝ) - s) / 2) * ((2 : ℝ) ^ e * r ^ (s - (d : ℝ)))) := by
          rw [← mul_assoc ((2 : ℝ) ^ (((d : ℝ) - s) / 2)), h2e, one_mul]
      _ ≤ |rieszConst d s| * ((2 : ℝ) ^ (((d : ℝ) - s) / 2) * (1 + r ^ 2) ^ e) := by
          rw [← hexp]; gcongr
      _ = _ := by ring

/-- Smoothing by the Riesz kernel: `ρ ∈ H^a ⇒ g ⋆ ρ ∈ H^{a + (d - s)}`. -/
theorem memHs_convFun {s : ℝ} (hsd : s < d) (F : MFInputs.MFKernelFacts d s) {h : Torus d → ℝ}
    (hh : Continuous h) (a : ℝ) (hmem : MemHs a (coeffOf h)) :
    MemHs (a + ((d : ℝ) - s)) (coeffOf (convFun (periodicRiesz d s) h)) := by
  set C0 : ℝ := |rieszConst d s| * (2 : ℝ) ^ (((d : ℝ) - s) / 2) with hC0
  have hC00 : 0 ≤ C0 := by positivity
  have hcoef : ∀ k, coeffOf (convFun (periodicRiesz d s) h) k = (rieszCoeff d s k : ℂ) * coeffOf h k := by
    intro k
    unfold coeffOf
    rw [MFAux.funFourierCoeff_convFun F.integrable hh k, F.fourierCoeff k]
  unfold MemHs
  refine (hmem.mul_left (C0 ^ 2)).of_nonneg_of_le (fun k => mul_nonneg (MFProduct.sobWeight_nonneg _ k) (sq_nonneg _))
    (fun k => ?_)
  rw [hcoef k, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hb := abs_rieszCoeff_le_sobWeight (d := d) s hsd k
  set W : ℝ := sobWeight (-(((d : ℝ) - s) / 2)) k with hW
  have hW0 : 0 ≤ W := MFProduct.sobWeight_nonneg _ k
  have hWW : sobWeight (a + ((d : ℝ) - s)) k * W ^ 2 = sobWeight a k := by
    rw [hW, sq, MFProduct.sobWeight_mul, MFProduct.sobWeight_mul]
    congr 1
    ring
  have hg2 : |rieszCoeff d s k| ^ 2 ≤ (C0 * W) ^ 2 := by
    have : |rieszCoeff d s k| ≤ C0 * W := hb
    exact pow_le_pow_left₀ (abs_nonneg _) this 2
  have hw0 : 0 ≤ sobWeight (a + ((d : ℝ) - s)) k := MFProduct.sobWeight_nonneg _ k
  calc sobWeight (a + ((d : ℝ) - s)) k * (|rieszCoeff d s k| * ‖coeffOf h k‖) ^ 2
      = sobWeight (a + ((d : ℝ) - s)) k * (|rieszCoeff d s k| ^ 2 * ‖coeffOf h k‖ ^ 2) := by ring
    _ ≤ sobWeight (a + ((d : ℝ) - s)) k * ((C0 * W) ^ 2 * ‖coeffOf h k‖ ^ 2) := by gcongr
    _ = C0 ^ 2 * (sobWeight a k * ‖coeffOf h k‖ ^ 2) := by
        rw [← hWW]; ring


/-! ### Linear combinations and the Lipschitz stage -/

theorem coeffOf_lincomb {V u : Torus d → ℝ} (hV : Continuous V) (hu : Continuous u) (A B c : ℝ) :
    coeffOf (fun x => A * V x + B * u x + c) =
      fun k => (A : ℂ) * coeffOf V k + (B : ℂ) * coeffOf u k + (c : ℂ) * deltaCoeff 0 k := by
  funext k
  have h1 := coeffOf_add_fun (φ := fun x => A * V x + B * u x) (ψ := fun _ => c)
    ((continuous_const.mul hV).add (continuous_const.mul hu)) continuous_const k
  have h2 := coeffOf_add_fun (φ := fun x => A * V x) (ψ := fun x => B * u x)
    (continuous_const.mul hV) (continuous_const.mul hu) k
  have h3 := coeffOf_const (d := d) c k
  rw [h1, h2, coeffOf_const_mul_fun, coeffOf_const_mul_fun, h3]

theorem memHs_lincomb {m : ℝ} {V u : Torus d → ℝ} (hV : Continuous V) (hu : Continuous u)
    (hVm : MemHs m (coeffOf V)) (hum : MemHs m (coeffOf u)) (A B c : ℝ) :
    MemHs m (coeffOf (fun x => A * V x + B * u x + c)) := by
  rw [coeffOf_lincomb hV hu]
  exact memHs_add (memHs_add (memHs_smul hVm _) (memHs_smul hum _)) (memHs_smul (deltaCoeff_memHs m 0) _)

/-- `exp` is Lipschitz on `(-∞, M]` with constant `exp M`. -/
theorem abs_exp_sub_le {M x y : ℝ} (hx : x ≤ M) (hy : y ≤ M) :
    |Real.exp x - Real.exp y| ≤ Real.exp M * |x - y| := by
  have key : ∀ x y : ℝ, x ≤ y → y ≤ M → Real.exp y - Real.exp x ≤ Real.exp M * (y - x) := by
    intro x y hxy hyM
    have h1 : 1 + (x - y) ≤ Real.exp (x - y) := by linarith [Real.add_one_le_exp (x - y)]
    have h2 : Real.exp x = Real.exp y * Real.exp (x - y) := by rw [← Real.exp_add]; congr 1; ring
    have h3 : Real.exp y ≤ Real.exp M := Real.exp_le_exp.2 hyM
    have h4 : 0 ≤ y - x := by linarith
    have : Real.exp y - Real.exp x ≤ Real.exp y * (y - x) := by
      rw [h2]; nlinarith [Real.exp_pos y]
    exact this.trans (mul_le_mul_of_nonneg_right h3 h4)
  rcases le_total x y with h | h
  · have h1 : Real.exp x ≤ Real.exp y := Real.exp_le_exp.2 h
    rw [abs_of_nonpos (by linarith : Real.exp x - Real.exp y ≤ 0),
      abs_of_nonpos (by linarith : x - y ≤ 0)]
    have := key x y h hy
    linarith
  · have h1 : Real.exp y ≤ Real.exp x := Real.exp_le_exp.2 h
    rw [abs_of_nonneg (by linarith : 0 ≤ Real.exp x - Real.exp y),
      abs_of_nonneg (by linarith : 0 ≤ x - y)]
    exact key y x h hx

theorem lipschitz_clampExp {M : ℝ} (hM : 0 ≤ M) :
    LipschitzWith (Real.toNNReal (Real.exp M)) (fun t : ℝ => Real.exp (max (min t M) (-M))) := by
  have hcl : LipschitzWith 1 (fun t : ℝ => max (min t M) (-M)) :=
    (LipschitzWith.id.min_const M).max_const (-M)
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ (Real.exp_pos M).le]
  have hle : ∀ t : ℝ, max (min t M) (-M) ≤ M := fun t => max_le (min_le_right _ _) (by linarith)
  refine (abs_exp_sub_le (hle x) (hle y)).trans ?_
  have := hcl.dist_le_mul x y
  rw [Real.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul] at this
  exact mul_le_mul_of_nonneg_left this (Real.exp_pos M).le


theorem memHs_exp_lip {w : Torus d → ℝ} (hw : Continuous w) {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ < 1)
    (hmem : MemHs σ (coeffOf w)) : MemHs σ (coeffOf (fun x => Real.exp (w x))) := by
  obtain ⟨B, hB⟩ := (isCompact_univ (X := Torus d)).exists_bound_of_continuousOn hw.continuousOn
  set M : ℝ := max B 0 with hMdef
  have hM : 0 ≤ M := le_max_right _ _
  obtain ⟨C, hC0, hC⟩ := MFProduct.exists_lipschitz_comp_bound_of_nonneg (d := d) σ hσ0 hσ1
  have h := (hC (Real.exp M) _ (Real.exp_pos M).le (lipschitz_clampExp hM) w hw hmem).1
  have e : ((fun t : ℝ => Real.exp (max (min t M) (-M))) ∘ w) = fun x => Real.exp (w x) := by
    funext x
    have hx : |w x| ≤ M := by
      have := hB x (Set.mem_univ x)
      rw [Real.norm_eq_abs] at this
      exact this.trans (le_max_left _ _)
    simp only [Function.comp]
    rw [min_eq_left (le_trans (le_abs_self _) hx), max_eq_left (by linarith [neg_abs_le (w x)])]
  rwa [e] at h

/-- The Lipschitz stage: `ρ ∈ H^a ⇒ ρ ∈ H^τ` for `0 ≤ τ < 1`, `τ ≤ a + (d - s)`, `τ ≤ 1`. -/
theorem lip_stage {s : ℝ} (hsd : s < d) (F : MFInputs.MFKernelFacts d s) {V : Torus d → ℝ}
    (hV : Torus.IsCk 1 V) {β c : ℝ} {ρ : Torus d → ℝ} (hc : Continuous ρ)
    (hρe : ∀ x, ρ x = Real.exp (-β * V x + -β * convFun (periodicRiesz d s) ρ x + c))
    (a : ℝ) (hmem : MemHs a (coeffOf ρ)) {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ < 1)
    (hτa : τ ≤ a + ((d : ℝ) - s)) : MemHs τ (coeffOf ρ) := by
  have hVc : Continuous V := continuous_of_isCk hV
  have huc : Continuous (convFun (periodicRiesz d s) ρ) := MFAux.continuous_convFun F.integrable hc
  have hu := (memHs_convFun hsd F hc a hmem).mono hτa
  have hVm : MemHs τ (coeffOf V) := (memHs_one_coeffOf V hV).1.mono hτ1.le
  have hw := memHs_lincomb hVc huc hVm hu (-β) (-β) c
  have := memHs_exp_lip (w := fun x => -β * V x + -β * convFun (periodicRiesz d s) ρ x + c)
    (((continuous_const.mul hVc).add (continuous_const.mul huc)).add continuous_const) hτ0 hτ1 hw
  have e : (fun x => Real.exp (-β * V x + -β * convFun (periodicRiesz d s) ρ x + c)) = ρ :=
    funext fun x => (hρe x).symm
  rwa [e] at this


/-! ### Triangle inequality and finite sums in `H^a` -/

theorem hsNormSq_eq_tsum_sq (a : ℝ) (x : Coeff d) :
    hsNormSq a x = ∑' k, (sobWeight (a / 2) k * ‖x k‖) ^ 2 := by
  unfold hsNormSq
  exact tsum_congr fun k => by rw [mul_pow, MFProduct.sobWeight_half_sq]

theorem summable_sq_of_memHs {a : ℝ} {x : Coeff d} (hx : MemHs a x) :
    Summable fun k => (sobWeight (a / 2) k * ‖x k‖) ^ 2 :=
  hx.congr fun k => by rw [mul_pow, MFProduct.sobWeight_half_sq]

theorem hsNorm_add_le (a : ℝ) {x y : Coeff d} (hx : MemHs a x) (hy : MemHs a y) :
    hsNorm a (fun k => x k + y k) ≤ hsNorm a x + hsNorm a y := by
  have hxy : MemHs a (fun k => x k + y k) := memHs_add hx hy
  set p : Lattice d → ℝ := fun k => sobWeight (a / 2) k * ‖x k‖ with hp
  set q : Lattice d → ℝ := fun k => sobWeight (a / 2) k * ‖y k‖ with hq
  have hp0 : ∀ k, 0 ≤ p k := fun k => mul_nonneg (MFProduct.sobWeight_nonneg _ k) (norm_nonneg _)
  have hq0 : ∀ k, 0 ≤ q k := fun k => mul_nonneg (MFProduct.sobWeight_nonneg _ k) (norm_nonneg _)
  have hp2 : Summable fun k => p k ^ 2 := summable_sq_of_memHs hx
  have hq2 : Summable fun k => q k ^ 2 := summable_sq_of_memHs hy
  obtain ⟨hpq, hcs⟩ := Torus.cs_tsum p q hp0 hq0 hp2 hq2
  have hle : ∀ k, (sobWeight (a / 2) k * ‖x k + y k‖) ^ 2 ≤ (p k + q k) ^ 2 := by
    intro k
    have h1 : ‖x k + y k‖ ≤ ‖x k‖ + ‖y k‖ := norm_add_le _ _
    have h2 := MFProduct.sobWeight_nonneg (a / 2) k
    have : sobWeight (a / 2) k * ‖x k + y k‖ ≤ p k + q k := by
      simp only [hp, hq]; nlinarith
    exact pow_le_pow_left₀ (mul_nonneg h2 (norm_nonneg _)) this 2
  have hsum2 : Summable fun k => (p k + q k) ^ 2 :=
    (hp2.add hq2).add (hpq.mul_left 2) |>.congr fun k => by ring
  have hmain : hsNormSq a (fun k => x k + y k) ≤ (hsNorm a x + hsNorm a y) ^ 2 := by
    rw [hsNormSq_eq_tsum_sq]
    have hS : Summable fun k => (sobWeight (a / 2) k * ‖x k + y k‖) ^ 2 := summable_sq_of_memHs hxy
    calc ∑' k, (sobWeight (a / 2) k * ‖x k + y k‖) ^ 2 ≤ ∑' k, (p k + q k) ^ 2 :=
          hS.tsum_le_tsum hle hsum2
      _ = ∑' k, p k ^ 2 + 2 * ∑' k, p k * q k + ∑' k, q k ^ 2 := by
          have e : ∀ k, (p k + q k) ^ 2 = (p k ^ 2 + q k ^ 2) + 2 * (p k * q k) := fun k => by ring
          simp_rw [e]
          rw [(hp2.add hq2).tsum_add (hpq.mul_left 2), hp2.tsum_add hq2, tsum_mul_left]
          ring
      _ ≤ (hsNorm a x + hsNorm a y) ^ 2 := by
          have hA : hsNorm a x = Real.sqrt (∑' k, p k ^ 2) := by
            unfold hsNorm; rw [hsNormSq_eq_tsum_sq]
          have hB : hsNorm a y = Real.sqrt (∑' k, q k ^ 2) := by
            unfold hsNorm; rw [hsNormSq_eq_tsum_sq]
          have sA : Real.sqrt (∑' k, p k ^ 2) ^ 2 = ∑' k, p k ^ 2 :=
            Real.sq_sqrt (tsum_nonneg fun k => sq_nonneg (p k))
          have sB : Real.sqrt (∑' k, q k ^ 2) ^ 2 = ∑' k, q k ^ 2 :=
            Real.sq_sqrt (tsum_nonneg fun k => sq_nonneg (q k))
          rw [hA, hB]
          nlinarith [hcs]
  unfold hsNorm
  calc Real.sqrt (hsNormSq a fun k => x k + y k) ≤ Real.sqrt ((hsNorm a x + hsNorm a y) ^ 2) :=
        Real.sqrt_le_sqrt hmain
    _ = hsNorm a x + hsNorm a y := Real.sqrt_sq (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

theorem hsNorm_smul (a : ℝ) (r : ℂ) (x : Coeff d) :
    hsNorm a (fun k => r * x k) = ‖r‖ * hsNorm a x := by
  unfold hsNorm hsNormSq
  have : ∀ k, sobWeight a k * ‖r * x k‖ ^ 2 = ‖r‖ ^ 2 * (sobWeight a k * ‖x k‖ ^ 2) := fun k => by
    rw [norm_mul]; ring
  simp_rw [this]
  rw [tsum_mul_left, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]

theorem hsNorm_sum_le (a : ℝ) (x : ℕ → Coeff d) (hx : ∀ n, MemHs a (x n)) (N : ℕ) :
    MemHs a (fun k => ∑ n ∈ Finset.range N, x n k) ∧
      hsNorm a (fun k => ∑ n ∈ Finset.range N, x n k) ≤ ∑ n ∈ Finset.range N, hsNorm a (x n) := by
  induction N with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty]
    refine ⟨?_, ?_⟩
    · unfold MemHs; simp
    · unfold hsNorm hsNormSq; simp
  | succ N ih =>
    simp only [Finset.sum_range_succ]
    refine ⟨memHs_add ih.1 (hx N), ?_⟩
    exact (hsNorm_add_le a ih.1 (hx N)).trans (by linarith [ih.2])


/-! ### The exponential in `H^a`, `a ≥ 0`, for ℓ¹ coefficients -/

theorem hsNorm_delta (a : ℝ) : hsNorm a (deltaCoeff (0 : Lattice d)) = 1 := by
  unfold hsNorm hsNormSq
  have : ∑' k : Lattice d, sobWeight a k * ‖deltaCoeff (0 : Lattice d) k‖ ^ 2 = 1 := by
    rw [tsum_eq_single 0]
    · simp [deltaCoeff, MFProduct.sobWeight_zero_lattice]
    · intro k hk; simp [deltaCoeff, hk]
  rw [this]; simp

theorem hasSum_norm_delta : HasSum (fun k : Lattice d => ‖deltaCoeff (0 : Lattice d) k‖) 1 := by
  have := MFProduct.hasSum_weighted_delta (d := d) 0
  simpa [sobWeight_zero] using this

/-- Powers of an `H^a ∩ ℓ¹` function: `‖c^n‖_{H^a} ≤ T Q^n`. -/
theorem pow_bounds (a : ℝ) (ha : 0 ≤ a) (c : Coeff d) (hreal : IsRealCoeff c)
    (hs : Summable fun k => ‖c k‖) (hc : MemHs a c) :
    ∃ Q T : ℝ, 0 ≤ Q ∧ 0 ≤ T ∧ ∀ n : ℕ,
      MemHs a (coeffOf (fun x => toFun c x ^ n)) ∧
        hsNorm a (coeffOf (fun x => toFun c x ^ n)) ≤ T * Q ^ n := by
  set P : ℕ → Coeff d := fun n => coeffOf (fun x => toFun c x ^ n) with hP
  set X : ℝ := MFProduct.wienerNorm c with hX
  set Y : ℝ := hsNorm a c with hY
  set α : ℝ := (2 : ℝ) ^ a with hα
  set R : ℝ := max X 1 with hR
  set Q : ℝ := 2 * α * R with hQ
  set T : ℝ := max 1 Y with hT
  have hX0 : 0 ≤ X := tsum_nonneg fun k => norm_nonneg _
  have hY0 : 0 ≤ Y := Real.sqrt_nonneg _
  have hα1 : 1 ≤ α := Real.one_le_rpow (by norm_num) ha
  have hR1 : 1 ≤ R := le_max_right _ _
  have hXR : X ≤ R := le_max_left _ _
  have hRQ : R ≤ Q := by rw [hQ]; nlinarith
  have hT1 : 1 ≤ T := le_max_left _ _
  have hYT : Y ≤ T := le_max_right _ _
  have hQ0 : 0 ≤ Q := by linarith
  have key : ∀ n, (Summable fun k => ‖P n k‖) ∧ MFProduct.wienerNorm (P n) ≤ X ^ n ∧
      MemHs a (P n) ∧ hsNorm a (P n) ≤ T * Q ^ n := by
    intro n
    induction n with
    | zero =>
      have e : P 0 = deltaCoeff 0 := MFProduct.coeffOf_pow_zero (toFun c)
      rw [e]
      refine ⟨hasSum_norm_delta.summable, ?_, deltaCoeff_memHs a 0, ?_⟩
      · unfold MFProduct.wienerNorm
        rw [hasSum_norm_delta.tsum_eq]; simp
      · rw [hsNorm_delta]; simpa using hT1
    | succ n ih =>
      obtain ⟨h1, h2, h3, h4⟩ := ih
      have e : P (n + 1) = mulCoeff c (P n) := MFProduct.coeffOf_pow_succ c hreal hs n
      rw [e]
      obtain ⟨w1, w2⟩ := MFProduct.wienerNorm_mulCoeff_le c (P n) hs h1
      obtain ⟨m1, m2⟩ := MFProduct.hsNorm_mulCoeff_le a ha c (P n) hc h3 hs h1
      refine ⟨w1, ?_, m1, ?_⟩
      · calc MFProduct.wienerNorm (mulCoeff c (P n)) ≤ X * MFProduct.wienerNorm (P n) := w2
          _ ≤ X * X ^ n := mul_le_mul_of_nonneg_left h2 hX0
          _ = X ^ (n + 1) := by ring
      · have hXn : X ^ n ≤ Q ^ n := pow_le_pow_left₀ hX0 (hXR.trans hRQ) n
        have hQn : 0 ≤ Q ^ n := pow_nonneg hQ0 n
        have hwn : 0 ≤ MFProduct.wienerNorm (P n) := tsum_nonneg fun k => norm_nonneg _
        have hα0 : 0 ≤ α := by linarith
        calc hsNorm a (mulCoeff c (P n))
            ≤ α * (Y * MFProduct.wienerNorm (P n) + X * hsNorm a (P n)) := m2
          _ ≤ α * (T * Q ^ n + R * (T * Q ^ n)) := by
              have hY' : Y * MFProduct.wienerNorm (P n) ≤ T * Q ^ n :=
                mul_le_mul hYT (h2.trans hXn) hwn (by linarith)
              have hX' : X * hsNorm a (P n) ≤ R * (T * Q ^ n) :=
                mul_le_mul hXR h4 (Real.sqrt_nonneg _) (by linarith)
              exact mul_le_mul_of_nonneg_left (add_le_add hY' hX') hα0
          _ = α * T * Q ^ n * (1 + R) := by ring
          _ ≤ α * T * Q ^ n * (2 * R) := by gcongr; linarith
          _ = T * Q ^ (n + 1) := by rw [hQ]; ring
  exact ⟨Q, T, hQ0, by linarith, fun n => ⟨(key n).2.2.1, (key n).2.2.2⟩⟩

theorem memHs_exp_of_memHs (a : ℝ) (ha : 0 ≤ a) (c : Coeff d) (hreal : IsRealCoeff c)
    (hs : Summable fun k => ‖c k‖) (hc : MemHs a c) :
    MemHs a (coeffOf (fun x => Real.exp (toFun c x))) := by
  obtain ⟨Q, T, hQ0, hT0, hPQ⟩ := pow_bounds a ha c hreal hs hc
  set P : ℕ → Coeff d := fun n => coeffOf (fun x => toFun c x ^ n) with hP
  set x : ℕ → Coeff d := fun n k => ((n.factorial : ℂ))⁻¹ * P n k with hx
  have hxm : ∀ n, MemHs a (x n) := fun n => memHs_smul (hPQ n).1 _
  have hxn : ∀ n, hsNorm a (x n) ≤ T * Q ^ n / (n.factorial : ℝ) := by
    intro n
    simp only [hx]
    rw [hsNorm_smul]
    have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
    have : ‖((n.factorial : ℂ))⁻¹‖ = ((n.factorial : ℝ))⁻¹ := by simp
    rw [this, inv_mul_eq_div]
    exact div_le_div_of_nonneg_right (hPQ n).2 hf.le
  set B : ℝ := T * Real.exp Q with hB
  have hB0 : 0 ≤ B := by positivity
  have hpart : ∀ N : ℕ, hsNormSq a (fun k => ∑ n ∈ Finset.range N, x n k) ≤ B ^ 2 := by
    intro N
    obtain ⟨hm, hn⟩ := hsNorm_sum_le a x hxm N
    have h1 : ∑ n ∈ Finset.range N, hsNorm a (x n) ≤ B := by
      calc ∑ n ∈ Finset.range N, hsNorm a (x n)
          ≤ ∑ n ∈ Finset.range N, T * Q ^ n / (n.factorial : ℝ) := Finset.sum_le_sum fun n _ => hxn n
        _ ≤ B := by
            have hs' : HasSum (fun n : ℕ => T * Q ^ n / (n.factorial : ℝ)) B := by
              convert (MFProduct.hasSum_exp_real Q).mul_left T using 2 with n
              ring
            exact sum_le_hasSum (Finset.range N) (fun n _ => by positivity) hs'
    have h2 := hn.trans h1
    have h0 : 0 ≤ hsNorm a (fun k => ∑ n ∈ Finset.range N, x n k) := Real.sqrt_nonneg _
    have : hsNormSq a (fun k => ∑ n ∈ Finset.range N, x n k) =
        hsNorm a (fun k => ∑ n ∈ Finset.range N, x n k) ^ 2 := by
      unfold hsNorm; rw [Real.sq_sqrt (hsNormSq_nonneg _ _)]
    rw [this]
    exact pow_le_pow_left₀ h0 h2 2
  refine (memHs_of_sum_le (C := B ^ 2) fun S => ?_).1
  set E : Coeff d := coeffOf (fun x => Real.exp (toFun c x)) with hE
  have hlim : Tendsto (fun N : ℕ => ∑ k ∈ S, sobWeight a k * ‖∑ n ∈ Finset.range N, x n k‖ ^ 2)
      atTop (𝓝 (∑ k ∈ S, sobWeight a k * ‖E k‖ ^ 2)) := by
    refine tendsto_finsetSum S fun k _ => ?_
    have hk := MFProduct.hasSum_coeffOf_exp c hs k
    have hk' : HasSum (fun n : ℕ => x n k) (E k) := by
      convert hk using 2 with n
      simp only [hx, hP, div_eq_inv_mul]
    exact ((hk'.tendsto_sum_nat.norm).pow 2).const_mul _
  refine le_of_tendsto hlim (Eventually.of_forall fun N => ?_)
  exact (sum_le_hsNormSq (hsNorm_sum_le a x hxm N).1 S).trans (hpart N)


/-! ### The Moser stage -/

theorem coeffOf_affine {u : Torus d → ℝ} (hu : Continuous u) (B c : ℝ) :
    coeffOf (fun x => B * u x + c) =
      fun k => (B : ℂ) * coeffOf u k + (c : ℂ) * deltaCoeff 0 k := by
  funext k
  rw [coeffOf_add_fun (φ := fun x => B * u x) (ψ := fun _ => c) (continuous_const.mul hu)
    continuous_const k, coeffOf_const_mul_fun, coeffOf_const (d := d) c k]

theorem isCk_exp_neg_mul {V : Torus d → ℝ} {n : WithTop ℕ∞} (hV : Torus.IsCk n V) (β : ℝ) :
    Torus.IsCk n (fun x => Real.exp (-β * V x)) := by
  unfold Torus.IsCk at *
  have : Torus.lift (fun x => Real.exp (-β * V x)) =
      fun y => Real.exp (-β * Torus.lift V y) := rfl
  rw [this]
  exact Real.contDiff_exp.comp (contDiff_const.mul hV)

/-- Moser stage: if `ρ ∈ H^a` with `a + (d - s) > d/2`, then `ρ ∈ H^{min(a + (d-s), m)}`,
where `V ∈ C^m`. -/
theorem moser_stage {s : ℝ} (hsd : s < d) (F : MFInputs.MFKernelFacts d s) {V : Torus d → ℝ}
    (m : ℕ) (hV : Torus.IsCk (m : WithTop ℕ∞) V) {β c : ℝ} {ρ : Torus d → ℝ}
    (hc : Continuous ρ)
    (hρe : ∀ x, ρ x = Real.exp (-β * V x + -β * convFun (periodicRiesz d s) ρ x + c))
    (a : ℝ) (ha : 0 ≤ a) (hda : (d : ℝ) / 2 < a + ((d : ℝ) - s)) (hmem : MemHs a (coeffOf ρ)) :
    MemHs (min (a + ((d : ℝ) - s)) m) (coeffOf ρ) := by
  have hδ : 0 < (d : ℝ) - s := by linarith
  set u : Torus d → ℝ := convFun (periodicRiesz d s) ρ with hu
  have huc : Continuous u := MFAux.continuous_convFun F.integrable hc
  have hum : MemHs (a + ((d : ℝ) - s)) (coeffOf u) := memHs_convFun hsd F hc a hmem
  set b : ℝ := a + ((d : ℝ) - s) with hb
  have hb0 : 0 ≤ b := by linarith
  set φ : Torus d → ℝ := fun x => -β * u x + c with hφ
  have hφc : Continuous φ := (continuous_const.mul huc).add continuous_const
  have hφm : MemHs b (coeffOf φ) := by
    rw [hφ, coeffOf_affine huc]
    exact memHs_add (memHs_smul hum _) (memHs_smul (deltaCoeff_memHs b 0) _)
  have hφs : Summable fun k => ‖coeffOf φ k‖ := summable_norm_of_memHs b hda _ hφm
  have hφr : IsRealCoeff (coeffOf φ) := isRealCoeff_coeffOf φ (integrable_of_cont hφc)
  have hE := memHs_exp_of_memHs b hb0 (coeffOf φ) hφr hφs hφm
  rw [toFun_coeffOf hφc hφs] at hE
  set f : Torus d → ℝ := fun x => Real.exp (-β * V x) with hf
  have hfk : Torus.IsCk (m : WithTop ℕ∞) f := isCk_exp_neg_mul hV β
  have hfc : Continuous f := continuous_of_lift' hfk.continuous
  have hfm : MemHs (m : ℝ) (coeffOf f) := memHs_of_isCk m f hfk
  have hEc : Continuous fun x => Real.exp (φ x) := Real.continuous_exp.comp hφc
  have hρf : ρ = fun x => f x * Real.exp (φ x) := by
    funext x
    rw [hρe x, hf, hφ]
    simp only
    rw [← Real.exp_add]; congr 1; ring
  have hco : coeffOf ρ = mulCoeff (coeffOf f) (coeffOf fun x => Real.exp (φ x)) := by
    conv_lhs => rw [hρf]
    exact coeffOf_mul f _ (MFProduct.memLp_two_real hfc) (MFProduct.memLp_two_real hEc)
  have hmn : (0 : ℝ) ≤ min (m : ℝ) b := le_min (Nat.cast_nonneg m) hb0
  obtain ⟨C, hC0, hC⟩ := MFProduct.exists_product_bound (d := d) (m : ℝ) b (min (m : ℝ) b) hmn
    (min_le_left _ _) (min_le_right _ _) (by
      have h1 := min_add_max (m : ℝ) b
      have h2 := le_max_right (m : ℝ) b
      linarith)
  rw [hco, min_comm]
  exact (hC _ _ hfm hE).1


/-! ### The bootstrap -/

/-- Core of the bootstrap: `ρ ∈ H^K` (coefficient form). -/
theorem thermal_memHs {s : ℝ} (hsd : s < d) (F : MFInputs.MFKernelFacts d s)
    (hs : s < (d : ℝ) / 2 + 1) (K : ℕ) {V : Torus d → ℝ}
    (hV : Torus.IsCk ((K + 2 : ℕ) : WithTop ℕ∞) V) {β : ℝ} {ρ : Torus d → ℝ}
    (hρ : IsThermalDensity (periodicRiesz d s) V β ρ) (hc : Continuous ρ) (hp : ∀ x, 0 < ρ x) :
    MemHs (K : ℝ) (coeffOf ρ) := by
  obtain ⟨c, hlog⟩ := MFThermal.log_thermal hρ hp
  have hρe : ∀ x, ρ x = Real.exp (-β * V x + -β * convFun (periodicRiesz d s) ρ x + c) := by
    intro x
    rw [← Real.exp_log (hp x), hlog x]
    congr 1; ring
  have hδ : 0 < (d : ℝ) - s := by linarith
  set δ : ℝ := (d : ℝ) - s with hδdef
  have hV1 : Torus.IsCk 1 V := hV.of_le (by exact_mod_cast (by omega : 1 ≤ K + 2))
  -- the target index `σ₁ ∈ [0,1)` with `σ₁ + δ > d/2`
  set t0 : ℝ := max 0 ((d : ℝ) / 2 - δ) with ht0
  have ht01 : t0 < 1 := max_lt one_pos (by rw [hδdef]; linarith)
  set σ1 : ℝ := (t0 + 1) / 2 with hσ1
  have hσ1a : 0 ≤ σ1 := by have : 0 ≤ t0 := le_max_left _ _
                           rw [hσ1]; linarith
  have hσ1b : σ1 < 1 := by rw [hσ1]; linarith
  have hσ1c : (d : ℝ) / 2 < σ1 + δ := by
    have : (d : ℝ) / 2 - δ ≤ t0 := le_max_right _ _
    rw [hσ1]; linarith
  -- Lipschitz stage
  have hL : ∀ j : ℕ, MemHs (min (j * δ) σ1) (coeffOf ρ) := by
    intro j
    induction j with
    | zero =>
      have := (coeffOf_memHs_zero hc).1
      have e : min (((0 : ℕ) : ℝ) * δ) σ1 = 0 := by
        rw [Nat.cast_zero, zero_mul]; exact min_eq_left hσ1a
      rw [e]; exact this
    | succ j ih =>
      refine lip_stage hsd F hV1 hc hρe _ ih (τ := min (((j + 1 : ℕ) : ℝ) * δ) σ1)
        (le_min (by positivity) hσ1a) (lt_of_le_of_lt (min_le_right _ _) hσ1b) ?_
      push_cast
      rcases le_total ((j : ℝ) * δ) σ1 with h | h
      · rw [min_eq_left h]
        exact (min_le_left _ _).trans_eq (by ring)
      · rw [min_eq_right h]
        exact (min_le_right _ _).trans (by linarith)
  obtain ⟨j0, hj0⟩ := exists_nat_ge (σ1 / δ)
  have hσ1m : MemHs σ1 (coeffOf ρ) := by
    have := hL j0
    rwa [min_eq_right (by rwa [div_le_iff₀ hδ] at hj0)] at this
  -- Moser stage
  set m : ℕ := K + 2 with hm
  have hmσ : σ1 ≤ (m : ℝ) := by
    have : (2 : ℝ) ≤ m := by rw [hm]; push_cast; linarith [(Nat.cast_nonneg K : (0 : ℝ) ≤ K)]
    linarith
  have hM : ∀ j : ℕ, MemHs (min (σ1 + j * δ) (m : ℝ)) (coeffOf ρ) := by
    intro j
    induction j with
    | zero => simpa using hσ1m.mono (min_le_left _ _)
    | succ j ih =>
      have ha0 : σ1 ≤ min (σ1 + j * δ) (m : ℝ) :=
        le_min (by nlinarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]) hmσ
      have := moser_stage hsd F m hV hc hρe _ (hσ1a.trans ha0) (by linarith) ih
      refine this.mono (le_min ?_ (min_le_right _ _))
      push_cast
      rcases le_total (σ1 + (j : ℝ) * δ) (m : ℝ) with h | h
      · rw [min_eq_left h]
        exact (min_le_left _ _).trans_eq (by ring)
      · rw [min_eq_right h]
        exact (min_le_right _ _).trans (by linarith)
  obtain ⟨j1, hj1⟩ := exists_nat_ge (((m : ℝ) - σ1) / δ)
  have hmm : MemHs (m : ℝ) (coeffOf ρ) := by
    have := hM j1
    rwa [min_eq_right (by rw [div_le_iff₀ hδ] at hj1; linarith)] at this
  exact hmm.mono (by rw [hm]; push_cast; linarith)


set_option linter.unusedVariables false in
/-- **Finite regularity of the thermal density** (packet P4; (I7) in the range `s < d/2 + 1`): a
continuous positive thermal density with `V ∈ C^{K+2}` lies in `H^K`.  This is
`MFInputs.thermal_memSobolev` with the extra hypotheses `F : MFKernelFacts d s` and
`s < d/2 + 1`. -/
theorem thermal_memSobolev_of_lt (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d)
    (F : MFInputs.MFKernelFacts d s) (hs : s < (d : ℝ) / 2 + 1) (K : ℕ)
    (V : Torus d → ℝ) (hV : Torus.IsCk (K + 2) V) (β : ℝ) (hβ : 0 < β) (ρ : Torus d → ℝ)
    (hρ : IsThermalDensity (periodicRiesz d s) V β ρ) (hc : Continuous ρ) (hp : ∀ x, 0 < ρ x) :
    MemSobolev K ρ := by
  have hV' : Torus.IsCk ((K + 2 : ℕ) : WithTop ℕ∞) V := by exact_mod_cast hV
  exact memSobolev_of_memHs (K : ℝ) ρ (MFProduct.memLp_two_real hc)
    (thermal_memHs hsd F hs K hV' hρ hc hp)

set_option linter.unusedVariables false in
/-- **Smoothness of the thermal density** (packet P4): for `C^∞` potential `V` (and
`s < d/2 + 1`) a continuous positive thermal density is `C^∞`. -/
theorem thermal_isSmooth_of_lt (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d)
    (F : MFInputs.MFKernelFacts d s) (hs : s < (d : ℝ) / 2 + 1)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (β : ℝ) (hβ : 0 < β) (ρ : Torus d → ℝ)
    (hρ : IsThermalDensity (periodicRiesz d s) V β ρ) (hc : Continuous ρ) (hp : ∀ x, 0 < ρ x) :
    Torus.IsSmooth ρ := by
  have hdec : ∀ N : ℕ, MemHs (N : ℝ) (coeffOf ρ) := fun N =>
    thermal_memHs hsd F hs N (ContDiff.of_le (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift V) from hV)
      (WithTop.coe_le_coe.2 le_top)) hρ hc hp
  have hr : IsRealCoeff (coeffOf ρ) := isRealCoeff_coeffOf ρ (integrable_of_cont hc)
  have hsum : Summable fun k => ‖coeffOf ρ k‖ :=
    summable_norm_of_memHs ((d + 1 : ℕ) : ℝ) (by push_cast; linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)])
      _ (hdec (d + 1))
  have := isSmooth_toFun_of_decay (coeffOf ρ) hr hdec
  rwa [toFun_coeffOf hc hsum] at this

end HRS.PDE.MFThermalReg
