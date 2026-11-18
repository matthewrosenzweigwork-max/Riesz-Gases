import HRS.MC.WCI
import HRS.MC.S7FCDefs
import HRS.MC.S7FCH1B1
import HRS.Equilibrium.FieldSingAux

/-!
# S7FCH3B: Wick coefficients of a kernel difference and their Hilbert-Schmidt bound (H3, part B)

Sorry-free helpers for `s7_FC_H3_gauss_approx` (`HRS/MC/S7FCPlan.lean`), no regime:

* `S7FCH3_bessel`: Bessel's inequality for an orthonormal family (copy of `q08s_bessel`, whose home file
  contains sorried skeleton statements);
* `S7FCH3_hs_bessel`: for `g ∈ L²(𝕋^d × 𝕋^d)`, `∑_{a,b} (⟨g, e_a ⊗ e_b⟩)² ≤ ‖g‖²`;
* `S7FCH3_wick_eq_prod`: the Wick coefficients of a kernel dominated by `K(‖x-y‖^{-s}+1)` are the product integrals
  `∬ u e_a e_b` (via `WCI.wci_core`, the centring is invisible);
* `S7FCH3_wick_diff`, `S7FCH3_hs_diff`: for `g = h_{∇e_k} - K` (`K` a smooth finite-rank kernel) the Wick coefficients
  subtract and the Hilbert-Schmidt mass is bounded by `∬ g²`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7FCH3

open HRS HRS.Sec7 HRS.MC.QRSpec HRS.MC.WCI HRS.MC.Sec7.FCPlan

variable {d : ℕ}

theorem S7FCH3_inner_toLp {X : Type*} [MeasurableSpace X] (ν : Measure X) {f g : X → ℝ}
    (hf : MemLp f 2 ν) (hg : MemLp g 2 ν) :
    inner ℝ (hf.toLp f) (hg.toLp g) = ∫ x, f x * g x ∂ν := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x h1 h2
  simp [h1, h2, mul_comm]

theorem S7FCH3_bessel {X : Type*} [MeasurableSpace X] (ν : Measure X) {ι : Type*} [DecidableEq ι]
    (f : ι → X → ℝ) (hf : ∀ i, MemLp (f i) 2 ν)
    (ho : ∀ i j, ∫ x, f i x * f j x ∂ν = if i = j then 1 else 0) (G : X → ℝ) (hG : MemLp G 2 ν) :
    Summable (fun i => (∫ x, G x * f i x ∂ν) ^ 2) ∧
      ∑' i, (∫ x, G x * f i x ∂ν) ^ 2 ≤ ∫ x, G x ^ 2 ∂ν := by
  set v : ι → MeasureTheory.Lp ℝ 2 ν := fun i => (hf i).toLp (f i) with hv
  have hon : Orthonormal ℝ v := by
    rw [orthonormal_iff_ite]
    intro i j
    rw [hv]
    simp only
    rw [S7FCH3_inner_toLp ν (hf i) (hf j), ho]
  set Gl := hG.toLp G with hGl
  have hin : ∀ i, inner ℝ (v i) Gl = ∫ x, G x * f i x ∂ν := by
    intro i
    rw [hv, hGl]
    simp only
    rw [S7FCH3_inner_toLp ν (hf i) hG]
    refine integral_congr_ae (Eventually.of_forall fun x => by ring)
  have h1 := hon.inner_products_summable Gl
  have h2 := hon.tsum_inner_products_le Gl
  have hn : ‖Gl‖ ^ 2 = ∫ x, G x ^ 2 ∂ν := by
    rw [← real_inner_self_eq_norm_sq, hGl, S7FCH3_inner_toLp ν hG hG]
    refine integral_congr_ae (Eventually.of_forall fun x => by ring)
  simp only [hin, Real.norm_eq_abs, sq_abs] at h1 h2
  rw [hn] at h2
  exact ⟨h1, h2⟩

/-- The product-integral coefficient `∬ u(x,y) e_a(x) e_b(y) dx dy`. -/
def S7FCH3_Jc (u : Torus d → Torus d → ℝ) (a b : NonzeroLattice d) : ℝ :=
  ∫ z : Torus d × Torus d, u z.1 z.2 * (Torus.realMode a z.1 * Torus.realMode b z.2)
    ∂((volume : Measure (Torus d)).prod volume)

theorem S7FCH3_realMode_bound (a : NonzeroLattice d) (x : Torus d) : ‖Torus.realMode a x‖ ≤ Real.sqrt 2 := by
  rw [Real.norm_eq_abs]; exact Torus.abs_realMode_le a x

theorem S7FCH3_hs_bessel (g : Torus d → Torus d → ℝ)
    (hg : MemLp (fun p : Torus d × Torus d => g p.1 p.2) 2 ((volume : Measure (Torus d)).prod volume)) :
    Summable (fun p : NonzeroLattice d × NonzeroLattice d => S7FCH3_Jc g p.1 p.2 ^ 2) ∧
      ∑' p : NonzeroLattice d × NonzeroLattice d, S7FCH3_Jc g p.1 p.2 ^ 2 ≤
        ∫ z : Torus d × Torus d, g z.1 z.2 ^ 2 ∂((volume : Measure (Torus d)).prod volume) := by
  classical
  set ν : Measure (Torus d × Torus d) := (volume : Measure (Torus d)).prod volume with hν
  set f : NonzeroLattice d × NonzeroLattice d → Torus d × Torus d → ℝ :=
    fun p z => Torus.realMode p.1 z.1 * Torus.realMode p.2 z.2 with hf
  have hfc : ∀ p, Continuous (f p) := fun p =>
    ((Torus.continuous_realMode p.1).comp continuous_fst).mul ((Torus.continuous_realMode p.2).comp continuous_snd)
  have hfb : ∀ p z, ‖f p z‖ ≤ 2 := by
    intro p z
    rw [hf]
    simp only [norm_mul]
    calc ‖Torus.realMode p.1 z.1‖ * ‖Torus.realMode p.2 z.2‖ ≤ Real.sqrt 2 * Real.sqrt 2 :=
          mul_le_mul (S7FCH3_realMode_bound _ _) (S7FCH3_realMode_bound _ _) (norm_nonneg _) (Real.sqrt_nonneg _)
      _ = 2 := Real.mul_self_sqrt (by norm_num)
  have hfm : ∀ p, MemLp (f p) 2 ν := fun p =>
    MemLp.of_bound (hfc p).aestronglyMeasurable 2 (Eventually.of_forall (hfb p))
  have ho : ∀ i j, ∫ x, f i x * f j x ∂ν = if i = j then 1 else 0 := by
    intro i j
    have e : ∀ z : Torus d × Torus d, f i z * f j z =
        (Torus.realMode i.1 z.1 * Torus.realMode j.1 z.1) * (Torus.realMode i.2 z.2 * Torus.realMode j.2 z.2) := by
      intro z; simp only [hf]; ring
    simp_rw [e]
    rw [hν, integral_prod_mul (fun x => Torus.realMode i.1 x * Torus.realMode j.1 x)
      (fun y => Torus.realMode i.2 y * Torus.realMode j.2 y), Torus.realMode_orthonormal, Torus.realMode_orthonormal]
    by_cases h1 : i.1 = j.1 <;> by_cases h2 : i.2 = j.2 <;> simp [h1, h2, Prod.ext_iff]
  obtain ⟨hs, hle⟩ := S7FCH3_bessel ν f hfm ho _ hg
  have hint : ∀ p, Integrable (fun z : Torus d × Torus d => g z.1 z.2 * f p z) ν := by
    intro p
    exact (hg.integrable (by norm_num)).mul_bdd (hfc p).aestronglyMeasurable (c := 2) (Eventually.of_forall (hfb p))
  have hJ : ∀ p, S7FCH3_Jc g p.1 p.2 = ∫ z, g z.1 z.2 * f p z ∂ν := fun p => rfl
  simp_rw [hJ]
  exact ⟨hs, hle⟩

theorem S7FCH3_integrable_comp_sub {G : Torus d → ℝ} (hG : Integrable G volume) (hGm : Measurable G) :
    Integrable (fun z : Torus d × Torus d => G (z.1 - z.2)) ((volume : Measure (Torus d)).prod volume) := by
  have hm : Measurable (fun z : Torus d × Torus d => G (z.1 - z.2)) :=
    hGm.comp (measurable_fst.sub measurable_snd)
  rw [integrable_prod_iff hm.aestronglyMeasurable]
  refine ⟨Eventually.of_forall fun x => hG.comp_sub_left x, ?_⟩
  have e : (fun x : Torus d => ∫ y, ‖G (x - y)‖) = fun _ => ∫ z, ‖G z‖ := by
    funext x
    exact integral_sub_left_eq_self (fun z => ‖G z‖) volume x
  simp only [e]
  exact integrable_const _

theorem S7FCH3_wciG_meas (s Kc : ℝ) : Measurable (fun z : Torus d => wciG s Kc z) := by
  unfold wciG
  exact measurable_const.mul ((measurable_norm.pow_const _).add measurable_const)

theorem S7FCH3_integrable_prod_term {s Kc : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hK0 : 0 ≤ Kc)
    {u : Torus d → Torus d → ℝ}
    (hum : Measurable (fun p : Torus d × Torus d => u p.1 p.2))
    (hub : ∀ x y, ‖u x y‖ ≤ wciG s Kc (x - y)) (a b : NonzeroLattice d) :
    Integrable (fun z : Torus d × Torus d => u z.1 z.2 * (Torus.realMode a z.1 * Torus.realMode b z.2))
      ((volume : Measure (Torus d)).prod volume) := by
  have hd : 0 < d := by
    have h0 : (0 : ℝ) < d := by linarith
    exact_mod_cast h0
  have hGi : Integrable (wciG (d := d) s Kc) volume := wciG_integrable hd hsd Kc
  have hI := (S7FCH3_integrable_comp_sub hGi (S7FCH3_wciG_meas s Kc)).const_mul 2
  have hfm : Measurable (fun z : Torus d × Torus d => u z.1 z.2 * (Torus.realMode a z.1 * Torus.realMode b z.2)) :=
    hum.mul (((Torus.continuous_realMode a).measurable.comp measurable_fst).mul
      ((Torus.continuous_realMode b).measurable.comp measurable_snd))
  refine Integrable.mono' hI hfm.aestronglyMeasurable (Eventually.of_forall fun z => ?_)
  rw [norm_mul, norm_mul]
  have h1 := hub z.1 z.2
  have h2 : ‖Torus.realMode a z.1‖ * ‖Torus.realMode b z.2‖ ≤ 2 := by
    calc ‖Torus.realMode a z.1‖ * ‖Torus.realMode b z.2‖ ≤ Real.sqrt 2 * Real.sqrt 2 :=
          mul_le_mul (S7FCH3_realMode_bound _ _) (S7FCH3_realMode_bound _ _) (norm_nonneg _) (Real.sqrt_nonneg _)
      _ = 2 := Real.mul_self_sqrt (by norm_num)
  have hG0 : 0 ≤ wciG s Kc (z.1 - z.2) := wciG_nonneg hK0 _
  calc ‖u z.1 z.2‖ * (‖Torus.realMode a z.1‖ * ‖Torus.realMode b z.2‖) ≤ wciG s Kc (z.1 - z.2) * 2 :=
        mul_le_mul h1 h2 (by positivity) hG0
    _ = 2 * wciG s Kc (z.1 - z.2) := by ring

/-- The Wick coefficients of a dominated kernel are the product integrals (the `μ`-centring is invisible). -/
theorem S7FCH3_wick_eq_prod {s Kc : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hK0 : 0 ≤ Kc) {ρ : Torus d → ℝ} {Λ : ℝ}
    (hΛ : ∀ x, ρ x ≤ Λ) {u : Torus d → Torus d → ℝ}
    (hum : Measurable (fun p : Torus d × Torus d => u p.1 p.2))
    (hub : ∀ x y, ‖u x y‖ ≤ wciG s Kc (x - y)) (a b : NonzeroLattice d) :
    wickCoeff (withDensityReal ρ) u a b = S7FCH3_Jc u a b := by
  have hB0 : 0 ≤ max Λ 0 := le_max_right _ _
  have hΛB : ∀ x, ρ x ≤ max Λ 0 := fun x => (hΛ x).trans (le_max_left _ _)
  haveI := HRS.Commutator.absConv_isFiniteMeasure hΛB
  unfold wickCoeff
  rw [wci_core hs0 hsd hK0 hB0 (fun g hg => HRS.Commutator.absConv_integrable_mu hΛB hg)
    (fun g hg0 hg => HRS.Commutator.absConv_integral_mu_le hΛB hB0 hg0 hg) hum hub a b]
  unfold S7FCH3_Jc
  rw [integral_prod _ (S7FCH3_integrable_prod_term hs0 hsd hK0 hum hub a b)]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only
  ring

theorem S7FCH3_Jc_sub {u v : Torus d → Torus d → ℝ}
    (hu : ∀ a b, Integrable (fun z : Torus d × Torus d => u z.1 z.2 * (Torus.realMode a z.1 * Torus.realMode b z.2))
      ((volume : Measure (Torus d)).prod volume))
    (hv : ∀ a b, Integrable (fun z : Torus d × Torus d => v z.1 z.2 * (Torus.realMode a z.1 * Torus.realMode b z.2))
      ((volume : Measure (Torus d)).prod volume)) (a b : NonzeroLattice d) :
    S7FCH3_Jc (fun x y => u x y - v x y) a b = S7FCH3_Jc u a b - S7FCH3_Jc v a b := by
  unfold S7FCH3_Jc
  simp_rw [sub_mul]
  exact integral_sub (hu a b) (hv a b)

theorem S7FCH3_wciG_add (s K1 K2 : ℝ) (z : Torus d) : wciG s K1 z + wciG s K2 z = wciG s (K1 + K2) z := by
  unfold wciG; ring

/-- Wick coefficients subtract for two dominated kernels. -/
theorem S7FCH3_wick_sub {s K1 K2 : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hK1 : 0 ≤ K1) (hK2 : 0 ≤ K2)
    {ρ : Torus d → ℝ} {Λ : ℝ} (hΛ : ∀ x, ρ x ≤ Λ) {u v : Torus d → Torus d → ℝ}
    (hum : Measurable (fun p : Torus d × Torus d => u p.1 p.2))
    (hvm : Measurable (fun p : Torus d × Torus d => v p.1 p.2))
    (hub : ∀ x y, ‖u x y‖ ≤ wciG s K1 (x - y)) (hvb : ∀ x y, ‖v x y‖ ≤ wciG s K2 (x - y))
    (a b : NonzeroLattice d) :
    wickCoeff (withDensityReal ρ) (fun x y => u x y - v x y) a b =
      wickCoeff (withDensityReal ρ) u a b - wickCoeff (withDensityReal ρ) v a b := by
  have hwb : ∀ x y, ‖u x y - v x y‖ ≤ wciG s (K1 + K2) (x - y) := by
    intro x y
    refine (norm_sub_le _ _).trans ?_
    rw [← S7FCH3_wciG_add]
    exact add_le_add (hub x y) (hvb x y)
  rw [S7FCH3_wick_eq_prod hs0 hsd (add_nonneg hK1 hK2) hΛ (hum.sub hvm) hwb,
    S7FCH3_wick_eq_prod hs0 hsd hK1 hΛ hum hub, S7FCH3_wick_eq_prod hs0 hsd hK2 hΛ hvm hvb]
  exact S7FCH3_Jc_sub (fun a b => S7FCH3_integrable_prod_term hs0 hsd hK1 hum hub a b)
    (fun a b => S7FCH3_integrable_prod_term hs0 hsd hK2 hvm hvb a b) a b

/-! ### The kernel difference `h_{∇e_k} - K` -/

theorem S7FCH3_FR_cont (K : FRKernel d) :
    Continuous (fun p : Torus d × Torus d => K.toFun p.1 p.2) := by
  unfold FRKernel.toFun
  refine continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_
  have hi := (HRS.MC.Sec7.S7FCH1.S7FCH1_smooth_props (K.smooth i)).1
  have hj := (HRS.MC.Sec7.S7FCH1.S7FCH1_smooth_props (K.smooth j)).1
  exact (continuous_const.mul (hi.comp continuous_fst)).mul (hj.comp continuous_snd)

theorem S7FCH3_wciG_ge {s M : ℝ} (hM : 0 ≤ M) (z : Torus d) : M ≤ wciG s M z := by
  unfold wciG
  have : 0 ≤ ‖z‖ ^ (-s) := Real.rpow_nonneg (norm_nonneg _) _
  nlinarith

theorem S7FCH3_FR_bound (s : ℝ) (K : FRKernel d) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x y, ‖K.toFun x y‖ ≤ wciG s M (x - y) := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn (S7FCH3_FR_cont K).continuousOn
    (s := (Set.univ : Set (Torus d × Torus d)))
  refine ⟨max C 0, le_max_right _ _, fun x y => ?_⟩
  exact ((hC (x, y) (Set.mem_univ _)).trans (le_max_left _ _)).trans (S7FCH3_wciG_ge (le_max_right _ _) _)

theorem S7FCH3_bounds {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (hd2 : 2 ≤ d) (k : NonzeroLattice d)
    (Kf : FRKernel d) :
    ∃ K1 K2 : ℝ, 0 ≤ K1 ∧ 0 ≤ K2 ∧
      (∀ x y, ‖hTransport d s (Torus.realMode k) x y‖ ≤ wciG s K1 (x - y)) ∧
      (∀ x y, ‖Kf.toFun x y‖ ≤ wciG s K2 (x - y)) ∧
      Measurable (fun p : Torus d × Torus d => hTransport d s (Torus.realMode k) p.1 p.2) ∧
      Measurable (fun p : Torus d × Torus d => Kf.toFun p.1 p.2) := by
  have hsd : s < d := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd2
    linarith
  have hsm := HRS.FieldSingAux.isSmooth_realMode k
  obtain ⟨K1, hK1, hb1⟩ := wci_hT_bound hs0 hsd hsm
  obtain ⟨K2, hK2, hb2⟩ := S7FCH3_FR_bound s Kf
  exact ⟨K1, K2, hK1, hK2, fun x y => hb1 x y, hb2, wci_hT_measurable hsd hsm,
    (S7FCH3_FR_cont Kf).measurable⟩

theorem S7FCH3_wciG_sq_integrable {s : ℝ} (hd : 0 < d) (hs2 : 2 * s < d) (Kc : ℝ) :
    Integrable (fun z : Torus d => wciG s Kc z ^ 2) volume := by
  have h1 : Integrable (fun z : Torus d => 2 * Kc ^ 2 * (‖z‖ ^ (-(2 * s)) + 1)) volume :=
    (((HRS.KernelGrad.integrable_norm_rpow_neg hd hs2).add (integrable_const (1 : ℝ))).const_mul _)
  refine Integrable.mono' h1 ((S7FCH3_wciG_meas s Kc).pow_const 2).aestronglyMeasurable
    (Eventually.of_forall fun z => ?_)
  have ha : 0 ≤ ‖z‖ ^ (-s) := Real.rpow_nonneg (norm_nonneg _) _
  have hsq : (‖z‖ ^ (-s)) ^ 2 = ‖z‖ ^ (-(2 * s)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg z)]
    congr 1
    push_cast; ring
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  unfold wciG
  rw [← hsq]
  nlinarith [sq_nonneg (Kc * (‖z‖ ^ (-s) - 1)), sq_nonneg Kc, mul_nonneg (sq_nonneg Kc) (sq_nonneg (‖z‖ ^ (-s) - 1))]

theorem S7FCH3_diff_wick {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (hd2 : 2 ≤ d) {ρ : Torus d → ℝ} {Λ : ℝ}
    (hΛ : ∀ x, ρ x ≤ Λ) (k : NonzeroLattice d) (Kf : FRKernel d) (a b : NonzeroLattice d) :
    wickCoeff (withDensityReal ρ) (fun x y => hTransport d s (Torus.realMode k) x y - Kf.toFun x y) a b =
      wickCoeff (withDensityReal ρ) (hTransport d s (Torus.realMode k)) a b -
        wickCoeff (withDensityReal ρ) Kf.toFun a b := by
  have hsd : s < d := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd2
    linarith
  obtain ⟨K1, K2, hK1, hK2, hb1, hb2, hm1, hm2⟩ := S7FCH3_bounds hs0 hs hd2 k Kf
  exact S7FCH3_wick_sub hs0 hsd hK1 hK2 hΛ hm1 hm2 hb1 hb2 a b

theorem S7FCH3_diff_hs {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (hd2 : 2 ≤ d) {ρ : Torus d → ℝ} {Λ : ℝ}
    (hΛ : ∀ x, ρ x ≤ Λ) (k : NonzeroLattice d) (Kf : FRKernel d) :
    Summable (fun p : NonzeroLattice d × NonzeroLattice d =>
      wickCoeff (withDensityReal ρ) (fun x y => hTransport d s (Torus.realMode k) x y - Kf.toFun x y) p.1 p.2 ^ 2) ∧
    tailHS (wickCoeff (withDensityReal ρ) (fun x y => hTransport d s (Torus.realMode k) x y - Kf.toFun x y)) ∅ ≤
      ∫ z : Torus d × Torus d, (hTransport d s (Torus.realMode k) z.1 z.2 - Kf.toFun z.1 z.2) ^ 2
        ∂((volume : Measure (Torus d)).prod volume) := by
  have hsd : s < d := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd2
    linarith
  have hd : 0 < d := by omega
  have hs2 : 2 * s < d := by linarith
  obtain ⟨K1, K2, hK1, hK2, hb1, hb2, hm1, hm2⟩ := S7FCH3_bounds hs0 hs hd2 k Kf
  set g : Torus d → Torus d → ℝ := fun x y => hTransport d s (Torus.realMode k) x y - Kf.toFun x y with hg
  have hgm : Measurable (fun p : Torus d × Torus d => g p.1 p.2) := hm1.sub hm2
  have hgb : ∀ x y, ‖g x y‖ ≤ wciG s (K1 + K2) (x - y) := by
    intro x y
    refine (norm_sub_le _ _).trans ?_
    rw [← S7FCH3_wciG_add]
    exact add_le_add (hb1 x y) (hb2 x y)
  have hgL2 : MemLp (fun p : Torus d × Torus d => g p.1 p.2) 2 ((volume : Measure (Torus d)).prod volume) := by
    refine (memLp_two_iff_integrable_sq hgm.aestronglyMeasurable).2 ?_
    have hI := S7FCH3_integrable_comp_sub (S7FCH3_wciG_sq_integrable hd hs2 (K1 + K2))
      ((S7FCH3_wciG_meas s (K1 + K2)).pow_const 2)
    refine Integrable.mono' hI (hgm.pow_const 2).aestronglyMeasurable (Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have := hgb z.1 z.2
    rw [Real.norm_eq_abs] at this
    exact sq_le_sq' (abs_le.1 this).1 (abs_le.1 this).2
  obtain ⟨hsum, hle⟩ := S7FCH3_hs_bessel g hgL2
  have hcoef : ∀ a b, wickCoeff (withDensityReal ρ) g a b = S7FCH3_Jc g a b :=
    fun a b => S7FCH3_wick_eq_prod hs0 hsd (add_nonneg hK1 hK2) hΛ hgm hgb a b
  have htail : tailHS (wickCoeff (withDensityReal ρ) g) ∅ =
      ∑' p : NonzeroLattice d × NonzeroLattice d, S7FCH3_Jc g p.1 p.2 ^ 2 := by
    unfold tailHS
    refine tsum_congr fun p => ?_
    simp [hcoef]
  refine ⟨?_, ?_⟩
  · simpa only [hcoef] using hsum
  · rw [htail]; exact hle

end HRS.MC.Sec7.S7FCH3

end
