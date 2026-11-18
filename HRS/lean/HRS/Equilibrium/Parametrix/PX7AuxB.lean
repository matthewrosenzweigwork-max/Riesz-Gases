import HRS.PDE.MeanFieldPairInverse

/-!
# Packet PX7, file B: arrays of Fourier coefficients of `C^{a+b}` kernels

`arr R k l` is the `(k,l)` Fourier coefficient of a kernel `R` on `𝕋^d × 𝕋^d`.  This file proves the
mixed-Sobolev (Parseval) bound `∑ ⟨k⟩^{2a} ⟨l⟩^{2b} |arr R k l|² ≤ C ‖R‖²_{C^{a+b}}`, Fourier inversion
`R = ev (arr R)`, and the transposition and reality symmetries.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.PDE.PX7

variable {d : ℕ}

/-! ### Generic weighted `ℓ²` -/

section Generic

variable {ι : Type*}

theorem px7_wn_add (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (u v : ι → ℂ)
    (hu : Summable fun i => w i * ‖u i‖ ^ 2) (hv : Summable fun i => w i * ‖v i‖ ^ 2) :
    Summable (fun i => w i * ‖u i + v i‖ ^ 2) ∧
      Real.sqrt (∑' i, w i * ‖u i + v i‖ ^ 2) ≤
        Real.sqrt (∑' i, w i * ‖u i‖ ^ 2) + Real.sqrt (∑' i, w i * ‖v i‖ ^ 2) := by
  set f : ι → ℝ := fun i => Real.sqrt (w i) * ‖u i‖ with hf
  set g : ι → ℝ := fun i => Real.sqrt (w i) * ‖v i‖ with hg
  have hf0 : ∀ i, 0 ≤ f i := fun i => mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  have hg0 : ∀ i, 0 ≤ g i := fun i => mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  have hf2 : ∀ i, f i ^ 2 = w i * ‖u i‖ ^ 2 := fun i => by
    simp only [hf, mul_pow, Real.sq_sqrt (hw i)]
  have hg2 : ∀ i, g i ^ 2 = w i * ‖v i‖ ^ 2 := fun i => by
    simp only [hg, mul_pow, Real.sq_sqrt (hw i)]
  have hfs : Summable fun i => f i ^ (2 : ℝ) := by
    refine hu.congr fun i => ?_
    rw [Real.rpow_two, hf2]
  have hgs : Summable fun i => g i ^ (2 : ℝ) := by
    refine hv.congr fun i => ?_
    rw [Real.rpow_two, hg2]
  obtain ⟨hs, hle⟩ := Real.Lp_add_le_tsum_of_nonneg (p := 2) (by norm_num) hf0 hg0 hfs hgs
  have hpt : ∀ i, w i * ‖u i + v i‖ ^ 2 ≤ (f i + g i) ^ (2 : ℝ) := by
    intro i
    rw [Real.rpow_two]
    have h1 : Real.sqrt (w i) * ‖u i + v i‖ ≤ f i + g i := by
      simp only [hf, hg]
      rw [← mul_add]
      exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (Real.sqrt_nonneg _)
    calc w i * ‖u i + v i‖ ^ 2 = (Real.sqrt (w i) * ‖u i + v i‖) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt (hw i)]
      _ ≤ (f i + g i) ^ 2 := pow_le_pow_left₀ (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)) h1 2
  have hsum : Summable (fun i => w i * ‖u i + v i‖ ^ 2) :=
    Summable.of_nonneg_of_le (fun i => mul_nonneg (hw i) (sq_nonneg _)) hpt hs
  refine ⟨hsum, ?_⟩
  have h2 : ∑' i, w i * ‖u i + v i‖ ^ 2 ≤ ∑' i, (f i + g i) ^ (2 : ℝ) :=
    Summable.tsum_le_tsum hpt hsum hs
  have h3 : Real.sqrt (∑' i, w i * ‖u i + v i‖ ^ 2) ≤ Real.sqrt (∑' i, (f i + g i) ^ (2 : ℝ)) :=
    Real.sqrt_le_sqrt h2
  refine h3.trans ?_
  have e1 : ∑' i, f i ^ (2 : ℝ) = ∑' i, w i * ‖u i‖ ^ 2 := tsum_congr fun i => by
    rw [Real.rpow_two, hf2]
  have e2 : ∑' i, g i ^ (2 : ℝ) = ∑' i, w i * ‖v i‖ ^ 2 := tsum_congr fun i => by
    rw [Real.rpow_two, hg2]
  calc Real.sqrt (∑' i, (f i + g i) ^ (2 : ℝ)) = (∑' i, (f i + g i) ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) :=
        Real.sqrt_eq_rpow _
    _ ≤ (∑' i, f i ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) + (∑' i, g i ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := hle
    _ = _ := by
        rw [e1, e2, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]

theorem px7_wn_smul (w : ι → ℝ) (u : ι → ℂ) (a : ℂ) :
    Real.sqrt (∑' i, w i * ‖a * u i‖ ^ 2) = ‖a‖ * Real.sqrt (∑' i, w i * ‖u i‖ ^ 2) := by
  have : ∀ i, w i * ‖a * u i‖ ^ 2 = ‖a‖ ^ 2 * (w i * ‖u i‖ ^ 2) := fun i => by
    rw [norm_mul]; ring
  simp_rw [this]
  rw [tsum_mul_left, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]

end Generic


/-! ### Arrays -/

/-- A doubly indexed coefficient array. -/
abbrev Arr (d : ℕ) := Lattice d → Lattice d → ℂ

/-- Transposition. -/
def tr (u : Arr d) : Arr d := fun k l => u l k

/-- The weighted square sum is finite. -/
def Mem2 (a b : ℝ) (u : Arr d) : Prop :=
  Summable fun p : Lattice d × Lattice d => sobWeight a p.1 * sobWeight b p.2 * ‖u p.1 p.2‖ ^ 2

/-- The weighted `ℓ²` norm. -/
def nrm2 (a b : ℝ) (u : Arr d) : ℝ :=
  Real.sqrt (∑' p : Lattice d × Lattice d, sobWeight a p.1 * sobWeight b p.2 * ‖u p.1 p.2‖ ^ 2)

theorem px7_w_nonneg (a b : ℝ) (p : Lattice d × Lattice d) : 0 ≤ sobWeight a p.1 * sobWeight b p.2 :=
  mul_nonneg (sobWeight_pos a _).le (sobWeight_pos b _).le

theorem px7_nrm2_nonneg (a b : ℝ) (u : Arr d) : 0 ≤ nrm2 a b u := Real.sqrt_nonneg _

theorem Mem2.add {a b : ℝ} {u v : Arr d} (hu : Mem2 a b u) (hv : Mem2 a b v) :
    Mem2 a b (u + v) ∧ nrm2 a b (u + v) ≤ nrm2 a b u + nrm2 a b v := by
  have := px7_wn_add (fun p : Lattice d × Lattice d => sobWeight a p.1 * sobWeight b p.2)
    (px7_w_nonneg a b) (fun p => u p.1 p.2) (fun p => v p.1 p.2) hu hv
  exact this

theorem Mem2.smul {a b : ℝ} {u : Arr d} (hu : Mem2 a b u) (c : ℂ) :
    Mem2 a b (c • u) ∧ nrm2 a b (c • u) = ‖c‖ * nrm2 a b u := by
  have h1 : ∀ p : Lattice d × Lattice d, sobWeight a p.1 * sobWeight b p.2 * ‖(c • u) p.1 p.2‖ ^ 2 =
      ‖c‖ ^ 2 * (sobWeight a p.1 * sobWeight b p.2 * ‖u p.1 p.2‖ ^ 2) := fun p => by
    simp only [Pi.smul_apply, smul_eq_mul, norm_mul]; ring
  refine ⟨?_, ?_⟩
  · unfold Mem2; simp_rw [h1]; exact hu.mul_left _
  · unfold nrm2; simp_rw [h1]
    rw [tsum_mul_left, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]

theorem Mem2.neg {a b : ℝ} {u : Arr d} (hu : Mem2 a b u) :
    Mem2 a b (-u) ∧ nrm2 a b (-u) = nrm2 a b u := by
  have := hu.smul (-1)
  have e : (-1 : ℂ) • u = -u := by simp
  rw [e] at this
  simpa using this

theorem Mem2.sub {a b : ℝ} {u v : Arr d} (hu : Mem2 a b u) (hv : Mem2 a b v) :
    Mem2 a b (u - v) ∧ nrm2 a b (u - v) ≤ nrm2 a b u + nrm2 a b v := by
  obtain ⟨h1, h2⟩ := hv.neg
  obtain ⟨h3, h4⟩ := hu.add h1
  rw [← sub_eq_add_neg] at h3 h4
  exact ⟨h3, by rw [h2] at h4; exact h4⟩

theorem Mem2.mono {a b a' b' : ℝ} (ha : a ≤ a') (hb : b ≤ b') {u : Arr d} (hu : Mem2 a' b' u) :
    Mem2 a b u ∧ nrm2 a b u ≤ nrm2 a' b' u := by
  have hpt : ∀ p : Lattice d × Lattice d, sobWeight a p.1 * sobWeight b p.2 * ‖u p.1 p.2‖ ^ 2 ≤
      sobWeight a' p.1 * sobWeight b' p.2 * ‖u p.1 p.2‖ ^ 2 := fun p => by
    have h1 := sobWeight_mono ha p.1
    have h2 := sobWeight_mono hb p.2
    have h3 := sobWeight_pos b p.2
    have h4 := sobWeight_pos a p.1
    exact mul_le_mul_of_nonneg_right (mul_le_mul h1 h2 h3.le (sobWeight_pos a' _).le) (sq_nonneg _)
  have hs : Mem2 a b u := Summable.of_nonneg_of_le
    (fun p => mul_nonneg (px7_w_nonneg a b p) (sq_nonneg _)) hpt hu
  exact ⟨hs, Real.sqrt_le_sqrt (Summable.tsum_le_tsum hpt hs hu)⟩

theorem Mem2.transp {a b : ℝ} {u : Arr d} (hu : Mem2 a b u) : Mem2 b a (PX7.tr u) ∧ nrm2 b a (PX7.tr u) = nrm2 a b u := by
  have e : ∀ p : Lattice d × Lattice d, sobWeight b p.1 * sobWeight a p.2 * ‖PX7.tr u p.1 p.2‖ ^ 2 =
      sobWeight a p.swap.1 * sobWeight b p.swap.2 * ‖u p.swap.1 p.swap.2‖ ^ 2 := fun p => by
    simp only [PX7.tr, Prod.fst_swap, Prod.snd_swap]; ring
  refine ⟨?_, ?_⟩
  · unfold Mem2; simp_rw [e]
    exact (Equiv.prodComm (Lattice d) (Lattice d)).summable_iff.2 hu
  · unfold nrm2; simp_rw [e]
    congr 1
    exact (Equiv.prodComm (Lattice d) (Lattice d)).tsum_eq
      (fun p : Lattice d × Lattice d => sobWeight a p.1 * sobWeight b p.2 * ‖u p.1 p.2‖ ^ 2)


/-! ### Kernels, their coefficient arrays, derivatives, transposition -/

section Kernels

open MFPair

/-- The `(k,l)` Fourier coefficient of a kernel. -/
def arr (R : Torus d → Torus d → ℝ) : Arr d := fun k l =>
  coeffOfC (fun y => sliceCoeff R k y) l

/-- Transposed kernel. -/
def trK (R : Torus d → Torus d → ℝ) : Torus d → Torus d → ℝ := fun x y => R y x

/-- Derivative in the first variable in direction `e`. -/
def dxK (e : Euc d) (R : Torus d → Torus d → ℝ) : Torus d → Torus d → ℝ :=
  fun x y => dX e (lift2 R) (Torus.rep x, Torus.rep y)

theorem px7_coeffOfC_const_mul (z : ℂ) (f : Torus d → ℂ) (l : Lattice d) :
    coeffOfC (fun y => z * f y) l = z * coeffOfC f l := by
  unfold coeffOfC Torus.funFourierCoeff UnitAddTorus.mFourierCoeff
  simp_rw [smul_eq_mul, mul_left_comm _ z]
  exact integral_const_mul _ _

theorem px7_lift2_rep (g : Euc d × Euc d → ℝ) (hx : PerX g) (hy : PerY g) :
    lift2 (fun x y : Torus d => g (Torus.rep x, Torus.rep y)) = g := by
  funext p
  obtain ⟨n1, h1⟩ := Torus.rep_mk p.1
  obtain ⟨n2, h2⟩ := Torus.rep_mk p.2
  simp only [lift2, h1, h2]
  have a1 : g (p.1 + Lattice.toEuc n1, p.2 + Lattice.toEuc n2) = g (p.1, p.2 + Lattice.toEuc n2) := by
    simpa using hx n1 (p.1, p.2 + Lattice.toEuc n2)
  have a2 : g (p.1, p.2 + Lattice.toEuc n2) = g p := by
    have := hy n2 p
    have e : p + (0, Lattice.toEuc n2) = (p.1, p.2 + Lattice.toEuc n2) := by ext <;> simp
    rw [e] at this
    exact this
  rw [a1, a2]

theorem px7_lift2_dxK (e : Euc d) (R : Torus d → Torus d → ℝ) :
    lift2 (dxK e R) = dX e (lift2 R) :=
  px7_lift2_rep _ (perX_dX (perX_lift2 R) e) (perY_dX (perY_lift2 R) e)

theorem px7_isCk2_dxK (e : Euc d) {n : ℕ} {R : Torus d → Torus d → ℝ} (hR : IsCk2 (n + 1) R) :
    IsCk2 n (dxK e R) := by
  unfold IsCk2
  rw [px7_lift2_dxK]
  exact contDiff_dX e (by exact_mod_cast hR)

theorem px7_cbNorm2_dxK_le (e : Euc d) {n : ℕ} {R : Torus d → Torus d → ℝ} (hR : IsCk2 (n + 1) R) :
    cbNorm2 n (dxK e R) ≤ ‖e‖ * cbNorm2 (n + 1) R := by
  have hg : ContDiff ℝ ((n + 1 : ℕ)) (lift2 R) := by exact_mod_cast hR
  unfold cbNorm2
  rw [px7_lift2_dxK, Finset.mul_sum]
  have : ∑ i ∈ Finset.range (n + 1), ⨆ p : Euc d × Euc d, ‖iteratedFDeriv ℝ i (dX e (lift2 R)) p‖ ≤
      ∑ i ∈ Finset.range (n + 1), ‖e‖ * ⨆ p : Euc d × Euc d, ‖iteratedFDeriv ℝ (i + 1) (lift2 R) p‖ := by
    refine Finset.sum_le_sum fun i hi => ?_
    have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hbdd := bddAbove_norm_iteratedFDeriv hg (perX_lift2 R) (perY_lift2 R) (i := i + 1) (by omega)
    refine ciSup_le fun p => ?_
    exact (norm_iteratedFDeriv_dX e hg hi' p).trans (mul_le_mul_of_nonneg_left
      (le_ciSup hbdd p) (norm_nonneg e))
  refine this.trans ?_
  set S : ℕ → ℝ := fun i => ‖e‖ * ⨆ p : Euc d × Euc d, ‖iteratedFDeriv ℝ i (lift2 R) p‖ with hS
  have h0 : 0 ≤ S 0 := mul_nonneg (norm_nonneg e) (Real.iSup_nonneg fun _ => norm_nonneg _)
  have := Finset.sum_range_succ' S (n + 1)
  show ∑ i ∈ Finset.range (n + 1), S (i + 1) ≤ ∑ i ∈ Finset.range (n + 1 + 1), S i
  linarith


theorem px7_sliceCoeff_dxK (e : Euc d) {R : Torus d → Torus d → ℝ} (hR : IsCk2 1 R) (k : Lattice d)
    (y : Torus d) :
    sliceCoeff (dxK e R) k y = Complex.I * ((2 * Real.pi * Lattice.dot k e : ℝ) : ℂ) * sliceCoeff R k y := by
  have hg : ContDiff ℝ 1 (lift2 R) := by exact_mod_cast hR
  have hcont : Continuous (lift2 R) := hg.continuous
  have hcont' : Continuous (lift2 (dxK e R)) := by
    rw [px7_lift2_dxK]; exact continuous_dX hg e
  set v := Torus.rep y with hv
  have hy : y = Torus.mk v := (Torus.mk_rep y).symm
  rw [hy]
  have h := acas_dX k (lift2 R) hg (perX_lift2 R) e v
  rw [sliceCoeff_mk _ hcont' k v, px7_lift2_dxK, h.1, h.2, sliceCoeff_mk _ hcont k v]
  push_cast
  linear_combination ((2 * (Real.pi : ℂ) * Lattice.dot k e) * (MFPair.asF k (lift2 R) v : ℂ)) * Complex.I_sq


theorem px7_arr_dxK (e : Euc d) {R : Torus d → Torus d → ℝ} (hR : IsCk2 1 R) (k l : Lattice d) :
    arr (dxK e R) k l = Complex.I * ((2 * Real.pi * Lattice.dot k e : ℝ) : ℂ) * arr R k l := by
  unfold arr
  have : (fun y => sliceCoeff (dxK e R) k y) =
      fun y => (Complex.I * ((2 * Real.pi * Lattice.dot k e : ℝ) : ℂ)) * sliceCoeff R k y :=
    funext fun y => px7_sliceCoeff_dxK e hR k y
  rw [this, px7_coeffOfC_const_mul]

theorem px7_arr_eq (R : Torus d → Torus d → ℝ) (hR : Continuous (lift2 R)) (k l : Lattice d) :
    arr R k l = ∫ p : Torus d × Torus d, Torus.mode (-k) p.1 * Torus.mode (-l) p.2 * ((R p.1 p.2 : ℝ) : ℂ)
      ∂((volume : Measure (Torus d)).prod (volume : Measure (Torus d))) := by
  have hRc := continuous_pair_of_continuous_lift2 hR
  have hf : Continuous fun p : Torus d × Torus d =>
      Torus.mode (-k) p.1 * Torus.mode (-l) p.2 * ((R p.1 p.2 : ℝ) : ℂ) :=
    (((Torus.continuous_mode _).comp continuous_fst).mul ((Torus.continuous_mode _).comp continuous_snd)).mul
      (Complex.continuous_ofReal.comp hRc)
  have hint : Integrable (fun p : Torus d × Torus d =>
      Torus.mode (-k) p.1 * Torus.mode (-l) p.2 * ((R p.1 p.2 : ℝ) : ℂ))
      ((volume : Measure (Torus d)).prod (volume : Measure (Torus d))) :=
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [integral_prod_symm (fun p : Torus d × Torus d =>
    Torus.mode (-k) p.1 * Torus.mode (-l) p.2 * ((R p.1 p.2 : ℝ) : ℂ)) hint]
  unfold arr coeffOfC sliceCoeff coeffOf
  simp_rw [funFourierCoeff_eq_int]
  simp only [Torus.mode]
  refine integral_congr_ae (G := ℂ) (μ := (volume : Measure (Torus d))) ?_
  filter_upwards with y
  have e : ∀ x : Torus d, UnitAddTorus.mFourier (-k) x * UnitAddTorus.mFourier (-l) y * ((R x y : ℝ) : ℂ) =
      UnitAddTorus.mFourier (-l) y * (UnitAddTorus.mFourier (-k) x * ((R x y : ℝ) : ℂ)) := fun x => by ring
  simp_rw [e]
  rw [integral_const_mul]

theorem px7_continuous_trK {R : Torus d → Torus d → ℝ} (hR : Continuous (lift2 R)) :
    Continuous (lift2 (trK R)) := by
  have : lift2 (trK R) = lift2 R ∘ Prod.swap := by
    funext p; rfl
  rw [this]
  exact hR.comp continuous_swap

theorem px7_arr_trK {R : Torus d → Torus d → ℝ} (hR : Continuous (lift2 R)) (k l : Lattice d) :
    arr (trK R) k l = arr R l k := by
  rw [px7_arr_eq _ (px7_continuous_trK hR), px7_arr_eq _ hR]
  rw [← integral_prod_swap]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  simp only [trK, Prod.fst_swap, Prod.snd_swap]
  ring


theorem px7_lift2_trK (R : Torus d → Torus d → ℝ) :
    lift2 (trK R) = lift2 R ∘ (LinearIsometryEquiv.prodComm ℝ (Euc d) (Euc d)) := by
  funext p; rfl

theorem px7_isCk2_trK {n : ℕ} {R : Torus d → Torus d → ℝ} (hR : IsCk2 n R) : IsCk2 n (trK R) := by
  unfold IsCk2
  rw [px7_lift2_trK]
  exact hR.comp (LinearIsometryEquiv.prodComm ℝ (Euc d) (Euc d)).contDiff

theorem px7_cbNorm2_trK (n : ℕ) (R : Torus d → Torus d → ℝ) : cbNorm2 n (trK R) = cbNorm2 n R := by
  unfold cbNorm2
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [px7_lift2_trK]
  have : ∀ p : Euc d × Euc d,
      ‖iteratedFDeriv ℝ i (lift2 R ∘ (LinearIsometryEquiv.prodComm ℝ (Euc d) (Euc d))) p‖ =
        ‖iteratedFDeriv ℝ i (lift2 R) p.swap‖ := fun p =>
    (LinearIsometryEquiv.prodComm ℝ (Euc d) (Euc d)).norm_iteratedFDeriv_comp_right (lift2 R) p i
  simp_rw [this]
  exact Equiv.iSup_comp (g := fun p : Euc d × Euc d => ‖iteratedFDeriv ℝ i (lift2 R) p‖) (Equiv.prodComm (Euc d) (Euc d))


/-! ### Base Parseval -/

theorem px7_parseval_real (F : Torus d → ℂ) (hF : MemLp F 2 volume) :
    HasSum (fun n : Lattice d => ‖Torus.funFourierCoeff F n‖ ^ 2) (∫ t, ‖F t‖ ^ 2) := by
  have h := hasSum_parseval F F hF hF
  have e1 : ∀ n : Lattice d, conj (Torus.funFourierCoeff F n) * Torus.funFourierCoeff F n =
      ((‖Torus.funFourierCoeff F n‖ ^ 2 : ℝ) : ℂ) := fun n => by
    rw [Complex.conj_mul']; push_cast; ring
  have e2 : ∫ t, conj (F t) * F t = ((∫ t, ‖F t‖ ^ 2 : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only
    rw [Complex.conj_mul']; push_cast; ring
  simp_rw [e1] at h
  rw [e2] at h
  exact Complex.hasSum_ofReal.1 h

theorem px7_continuous_sliceCoeff {R : Torus d → Torus d → ℝ} (hR : IsCk2 0 R) (k : Lattice d) :
    Continuous fun y => sliceCoeff R k y := by
  obtain ⟨C, hC, h⟩ := MFPair.exists_sliceCoeff_bound (d := d) 0 0
  obtain ⟨h1, h2, -, -⟩ := h 0 (by omega) R hR k
  have c1 : Continuous fun y => (sliceCoeff R k y).re :=
    Torus.continuous_of_continuous_lift (by simpa [Torus.IsCk] using h1.continuous)
  have c2 : Continuous fun y => (sliceCoeff R k y).im :=
    Torus.continuous_of_continuous_lift (by simpa [Torus.IsCk] using h2.continuous)
  have : (fun y => sliceCoeff R k y) = fun y =>
      (((sliceCoeff R k y).re : ℝ) : ℂ) + (((sliceCoeff R k y).im : ℝ) : ℂ) * Complex.I := by
    funext y; exact (Complex.re_add_im _).symm
  rw [this]
  exact (Complex.continuous_ofReal.comp c1).add ((Complex.continuous_ofReal.comp c2).mul continuous_const)


theorem px7_integral_sq_le {f : Torus d → ℝ} (hf : ∀ t, 0 ≤ f t) (B : ℝ) (hB : ∀ t, f t ≤ B) :
    ∫ t, f t ≤ B := by
  have h1 : ‖∫ t, f t‖ ≤ B * (volume : Measure (Torus d)).real Set.univ :=
    norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hf t)]; exact hB t)
  rw [probReal_univ, mul_one] at h1
  exact (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using h1)

theorem px7_parseval0 {R : Torus d → Torus d → ℝ} (hR : IsCk2 0 R) (B : ℝ)
    (hB : ∀ x y, |R x y| ≤ B) :
    Summable (fun p : Lattice d × Lattice d => ‖arr R p.1 p.2‖ ^ 2) ∧
      ∑' p : Lattice d × Lattice d, ‖arr R p.1 p.2‖ ^ 2 ≤ B ^ 2 := by
  have hcont : Continuous (lift2 R) := by simpa [IsCk2] using hR.continuous
  have hRc := continuous_pair_of_continuous_lift2 hcont
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0 0)
  -- the slices in `x`
  have hx : ∀ (y : Torus d) (S : Finset (Lattice d)), ∑ k ∈ S, ‖sliceCoeff R k y‖ ^ 2 ≤ B ^ 2 := by
    intro y S
    have hcy : Continuous fun x => R x y :=
      hRc.comp (continuous_id.prodMk continuous_const)
    have hF : MemLp (fun x => ((R x y : ℝ) : ℂ)) 2 volume :=
      MFThermal.memLp_two_of_continuous (Complex.continuous_ofReal.comp hcy)
    have h := px7_parseval_real _ hF
    have e : ∀ k, sliceCoeff R k y = Torus.funFourierCoeff (fun x => ((R x y : ℝ) : ℂ)) k :=
      fun k => rfl
    simp_rw [e]
    refine (sum_le_hasSum S (fun k _ => sq_nonneg _) h).trans ?_
    refine px7_integral_sq_le (fun t => sq_nonneg _) (B ^ 2) (fun t => ?_)
    simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    exact sq_le_sq' (by linarith [abs_le.1 (hB t y)]) (abs_le.1 (hB t y)).2
  -- the slices in `y`
  have hk : ∀ k : Lattice d, HasSum (fun l => ‖arr R k l‖ ^ 2) (∫ y, ‖sliceCoeff R k y‖ ^ 2) := by
    intro k
    have hg := px7_continuous_sliceCoeff hR k
    exact px7_parseval_real _ (MFThermal.memLp_two_of_continuous hg)
  have hint : ∀ k : Lattice d, Integrable (fun y : Torus d => ‖sliceCoeff R k y‖ ^ 2) := fun k =>
    (((px7_continuous_sliceCoeff hR k).norm.pow 2)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hsum : ∀ S : Finset (Lattice d), ∑ k ∈ S, ∫ y, ‖sliceCoeff R k y‖ ^ 2 ≤ B ^ 2 := by
    intro S
    rw [← integral_finsetSum _ (fun k _ => hint k)]
    exact px7_integral_sq_le (fun t => Finset.sum_nonneg fun k _ => sq_nonneg _) (B ^ 2)
      (fun y => hx y S)
  have hnn : ∀ p : Lattice d × Lattice d, 0 ≤ ‖arr R p.1 p.2‖ ^ 2 := fun p => sq_nonneg _
  have hs1 : Summable fun k => ∑' l, ‖arr R k l‖ ^ 2 := by
    have : (fun k => ∑' l, ‖arr R k l‖ ^ 2) = fun k => ∫ y, ‖sliceCoeff R k y‖ ^ 2 :=
      funext fun k => (hk k).tsum_eq
    rw [this]
    exact summable_of_sum_le (fun k => integral_nonneg fun y => sq_nonneg _) hsum
  have hs : Summable (fun p : Lattice d × Lattice d => ‖arr R p.1 p.2‖ ^ 2) :=
    (summable_prod_of_nonneg (fun p => hnn p)).2 ⟨fun k => (hk k).summable, hs1⟩
  refine ⟨hs, ?_⟩
  rw [hs.tsum_prod]
  have : (fun k => ∑' l, ‖arr R k l‖ ^ 2) = fun k => ∫ y, ‖sliceCoeff R k y‖ ^ 2 :=
    funext fun k => (hk k).tsum_eq
  simp only [this]
  exact tsum_le_of_sum_le' (sq_nonneg B) hsum


/-! ### Mixed Sobolev bound by induction -/

theorem px7_cbNorm2_mono {n n' : ℕ} (h : n ≤ n') (R : Torus d → Torus d → ℝ) :
    cbNorm2 n R ≤ cbNorm2 n' R := by
  unfold cbNorm2
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) fun i _ _ =>
    Real.iSup_nonneg fun _ => norm_nonneg _

theorem px7_dot_single (k : Lattice d) (j : Fin d) :
    Lattice.dot k (EuclideanSpace.single j (1 : ℝ)) = (k j : ℝ) := by
  unfold Lattice.dot
  simp [EuclideanSpace.single_apply]

/-- The mixed Sobolev bound at weights `(a, b)`. -/
def PSV (d : ℕ) (a b : ℕ) : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ R : Torus d → Torus d → ℝ, IsCk2 (a + b) R →
    Mem2 (a : ℝ) (b : ℝ) (arr R) ∧
      ∑' p : Lattice d × Lattice d, sobWeight (a : ℝ) p.1 * sobWeight (b : ℝ) p.2 * ‖arr R p.1 p.2‖ ^ 2 ≤
        K * cbNorm2 (a + b) R ^ 2

theorem px7_PSV_zero : PSV d 0 0 := by
  refine ⟨1, zero_le_one, fun R hR => ?_⟩
  have hR0 : IsCk2 0 R := by simpa using hR
  have hB : ∀ x y, |R x y| ≤ cbNorm2 0 R := by
    intro x y
    have := norm_iteratedFDeriv_le_cbNorm2 hR0 (i := 0) le_rfl (Torus.rep x, Torus.rep y)
    rw [norm_iteratedFDeriv_zero] at this
    simpa [lift2, Torus.mk_rep] using this
  obtain ⟨h1, h2⟩ := px7_parseval0 hR0 _ hB
  have e : ∀ p : Lattice d × Lattice d, sobWeight ((0 : ℕ) : ℝ) p.1 * sobWeight ((0 : ℕ) : ℝ) p.2 *
      ‖arr R p.1 p.2‖ ^ 2 = ‖arr R p.1 p.2‖ ^ 2 := fun p => by
    simp [sobWeight_zero]
  refine ⟨?_, ?_⟩
  · unfold Mem2; simp_rw [e]; exact h1
  · simp_rw [e]; simpa using h2

theorem px7_PSV_succ {a b : ℕ} (h : PSV d a b) : PSV d (a + 1) b := by
  obtain ⟨K, hK, hP⟩ := h
  refine ⟨K * (1 + d), by positivity, fun R hR => ?_⟩
  have hR1 : IsCk2 (a + b + 1) R := by
    have : a + 1 + b = a + b + 1 := by omega
    rwa [this] at hR
  have hRab : IsCk2 (a + b) R := hR1.of_le (by exact_mod_cast Nat.le_succ _)
  set e : Fin d → Euc d := fun j => EuclideanSpace.single j (1 : ℝ) with he
  have hej : ∀ j, ‖e j‖ = 1 := fun j => by simp [he]
  have hRj : ∀ j, IsCk2 (a + b) (dxK (e j) R) := fun j => px7_isCk2_dxK (e j) hR1
  obtain ⟨m0, s0'⟩ := hP R hRab
  have mj : ∀ j, Mem2 (a : ℝ) (b : ℝ) (arr (dxK (e j) R)) ∧
      ∑' p : Lattice d × Lattice d, sobWeight (a : ℝ) p.1 * sobWeight (b : ℝ) p.2 *
        ‖arr (dxK (e j) R) p.1 p.2‖ ^ 2 ≤ K * cbNorm2 (a + b) (dxK (e j) R) ^ 2 := fun j => hP _ (hRj j)
  -- pointwise identity
  have hid : ∀ p : Lattice d × Lattice d, sobWeight ((a + 1 : ℕ) : ℝ) p.1 * sobWeight (b : ℝ) p.2 *
      ‖arr R p.1 p.2‖ ^ 2 = sobWeight (a : ℝ) p.1 * sobWeight (b : ℝ) p.2 * ‖arr R p.1 p.2‖ ^ 2 +
      ∑ j : Fin d, sobWeight (a : ℝ) p.1 * sobWeight (b : ℝ) p.2 * ‖arr (dxK (e j) R) p.1 p.2‖ ^ 2 := by
    intro p
    have h1 : sobWeight ((a + 1 : ℕ) : ℝ) p.1 = sobWeight (a : ℝ) p.1 *
        (1 + ∑ j : Fin d, (2 * Real.pi * (p.1 j : ℝ)) ^ 2) := by
      have : ((a + 1 : ℕ) : ℝ) = (a : ℝ) + 1 := by push_cast; ring
      rw [this, sobWeight_add, sobWeight_one, enorm_sq_eq_sum]
      congr 1
      rw [Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl (fun j _ => by ring)
    have h2 : ∀ j : Fin d, ‖arr (dxK (e j) R) p.1 p.2‖ ^ 2 =
        (2 * Real.pi * (p.1 j : ℝ)) ^ 2 * ‖arr R p.1 p.2‖ ^ 2 := by
      intro j
      have hR1' : IsCk2 1 R := hR1.of_le (by exact_mod_cast (show 1 ≤ a + b + 1 by omega))
      rw [px7_arr_dxK (e j) hR1', norm_mul, norm_mul, Complex.norm_I, he, px7_dot_single]
      simp only [one_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
    rw [h1]
    simp_rw [h2]
    rw [← Finset.mul_sum, ← Finset.sum_mul]
    ring
  have s0 : Summable (fun p : Lattice d × Lattice d => sobWeight (a : ℝ) p.1 * sobWeight (b : ℝ) p.2 *
      ‖arr R p.1 p.2‖ ^ 2) := m0
  have sj : ∀ j : Fin d, Summable (fun p : Lattice d × Lattice d => sobWeight (a : ℝ) p.1 *
      sobWeight (b : ℝ) p.2 * ‖arr (dxK (e j) R) p.1 p.2‖ ^ 2) := fun j => (mj j).1
  have hsumj : Summable (fun p : Lattice d × Lattice d => ∑ j : Fin d, sobWeight (a : ℝ) p.1 *
      sobWeight (b : ℝ) p.2 * ‖arr (dxK (e j) R) p.1 p.2‖ ^ 2) := summable_sum fun j _ => sj j
  have hsum1 : Summable (fun p : Lattice d × Lattice d => sobWeight ((a + 1 : ℕ) : ℝ) p.1 *
      sobWeight (b : ℝ) p.2 * ‖arr R p.1 p.2‖ ^ 2) :=
    (s0.add hsumj).congr fun p => (hid p).symm
  refine ⟨hsum1, ?_⟩
  have e1 : ∑' p : Lattice d × Lattice d, sobWeight ((a + 1 : ℕ) : ℝ) p.1 * sobWeight (b : ℝ) p.2 *
      ‖arr R p.1 p.2‖ ^ 2 = (∑' p : Lattice d × Lattice d, sobWeight (a : ℝ) p.1 * sobWeight (b : ℝ) p.2 *
      ‖arr R p.1 p.2‖ ^ 2) + ∑ j : Fin d, ∑' p : Lattice d × Lattice d, sobWeight (a : ℝ) p.1 *
      sobWeight (b : ℝ) p.2 * ‖arr (dxK (e j) R) p.1 p.2‖ ^ 2 := by
    rw [tsum_congr hid, s0.tsum_add hsumj, Summable.tsum_finsetSum (fun j _ => sj j)]
  rw [e1]
  have c0 : cbNorm2 (a + b) R ≤ cbNorm2 (a + 1 + b) R := px7_cbNorm2_mono (by omega) R
  have cj : ∀ j, cbNorm2 (a + b) (dxK (e j) R) ≤ cbNorm2 (a + 1 + b) R := fun j => by
    have := px7_cbNorm2_dxK_le (e j) hR1
    rw [hej j, one_mul] at this
    have e2 : a + b + 1 = a + 1 + b := by omega
    rwa [e2] at this
  have n0 := cbNorm2_nonneg (a + b) R
  have nj : ∀ j, 0 ≤ cbNorm2 (a + b) (dxK (e j) R) := fun j => cbNorm2_nonneg _ _
  have b0 : K * cbNorm2 (a + b) R ^ 2 ≤ K * cbNorm2 (a + 1 + b) R ^ 2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ n0 c0 2) hK
  have bj : ∀ j, K * cbNorm2 (a + b) (dxK (e j) R) ^ 2 ≤ K * cbNorm2 (a + 1 + b) R ^ 2 := fun j =>
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (nj j) (cj j) 2) hK
  calc _ ≤ K * cbNorm2 (a + 1 + b) R ^ 2 + ∑ j : Fin d, K * cbNorm2 (a + 1 + b) R ^ 2 := by
        refine add_le_add (s0'.trans b0) (Finset.sum_le_sum fun j _ => (mj j).2.trans (bj j))
    _ = _ := by simp; ring


theorem px7_PSV_a0 : ∀ a : ℕ, PSV d a 0
  | 0 => px7_PSV_zero
  | a + 1 => px7_PSV_succ (px7_PSV_a0 a)

theorem px7_tsum_transp (a b : ℝ) (u : Arr d) :
    ∑' p : Lattice d × Lattice d, sobWeight b p.1 * sobWeight a p.2 * ‖PX7.tr u p.1 p.2‖ ^ 2 =
      ∑' p : Lattice d × Lattice d, sobWeight a p.1 * sobWeight b p.2 * ‖u p.1 p.2‖ ^ 2 := by
  have e : ∀ p : Lattice d × Lattice d, sobWeight b p.1 * sobWeight a p.2 * ‖PX7.tr u p.1 p.2‖ ^ 2 =
      sobWeight a p.swap.1 * sobWeight b p.swap.2 * ‖u p.swap.1 p.swap.2‖ ^ 2 := fun p => by
    simp only [PX7.tr, Prod.fst_swap, Prod.snd_swap]; ring
  simp_rw [e]
  exact (Equiv.prodComm (Lattice d) (Lattice d)).tsum_eq
    (fun p : Lattice d × Lattice d => sobWeight a p.1 * sobWeight b p.2 * ‖u p.1 p.2‖ ^ 2)

theorem px7_PSV_0b (b : ℕ) : PSV d 0 b := by
  obtain ⟨K, hK, hP⟩ := px7_PSV_a0 (d := d) b
  refine ⟨K, hK, fun R hR => ?_⟩
  have hR' : IsCk2 (b + 0) (trK R) := by
    have : IsCk2 b R := by simpa using hR
    simpa using px7_isCk2_trK this
  obtain ⟨m1, s1⟩ := hP (trK R) hR'
  have hc : Continuous (lift2 R) := by
    have : IsCk2 0 R := hR.of_le (by exact_mod_cast Nat.zero_le _)
    simpa [IsCk2] using this.continuous
  have hat : arr (trK R) = PX7.tr (arr R) := by
    funext k l; exact px7_arr_trK hc k l
  rw [hat] at m1 s1
  have m2 := (Mem2.transp m1).1
  have e : PX7.tr (PX7.tr (arr R)) = arr R := by funext k l; rfl
  rw [e] at m2
  refine ⟨m2, ?_⟩
  have := px7_tsum_transp (b : ℝ) ((0 : ℕ) : ℝ) (PX7.tr (arr R))
  rw [e] at this
  rw [this]
  have e2 : cbNorm2 (b + 0) (trK R) = cbNorm2 (0 + b) R := by
    rw [px7_cbNorm2_trK]; simp
  rw [e2] at s1
  exact s1


theorem px7_PSV (a b : ℕ) : PSV d a b := by
  induction a with
  | zero => exact px7_PSV_0b b
  | succ a ih => exact px7_PSV_succ ih

/-- The mixed Sobolev bound in norm form. -/
theorem px7_parseval (a b : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ R : Torus d → Torus d → ℝ, IsCk2 (a + b) R →
      Mem2 (a : ℝ) (b : ℝ) (arr R) ∧ nrm2 (a : ℝ) (b : ℝ) (arr R) ≤ K * cbNorm2 (a + b) R := by
  obtain ⟨K, hK, hP⟩ := px7_PSV (d := d) a b
  refine ⟨Real.sqrt K, Real.sqrt_nonneg _, fun R hR => ?_⟩
  obtain ⟨h1, h2⟩ := hP R hR
  refine ⟨h1, ?_⟩
  unfold nrm2
  calc _ ≤ Real.sqrt (K * cbNorm2 (a + b) R ^ 2) := Real.sqrt_le_sqrt h2
    _ = _ := by rw [Real.sqrt_mul hK, Real.sqrt_sq (cbNorm2_nonneg _ _)]


/-! ### Absolute summability from weighted `ℓ²` -/

theorem px7_sqrt_sobWeight (a : ℝ) (k : Lattice d) : Real.sqrt (sobWeight a k) = Lattice.jp k ^ a := by
  rw [sobWeight_eq_jp, ← Torus.jp_rpow_sq]
  exact Real.sqrt_sq (Real.rpow_nonneg (Torus.jp_pos k).le _)

theorem px7_cs (a b : ℝ) (s t : ℕ) (h1 : (d : ℝ) < 2 * a - 2 * s) (h2 : (d : ℝ) < 2 * b - 2 * t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : Arr d, Mem2 a b u →
      Summable (fun p : Lattice d × Lattice d => Lattice.jp p.1 ^ s * Lattice.jp p.2 ^ t * ‖u p.1 p.2‖) ∧
      ∑' p : Lattice d × Lattice d, Lattice.jp p.1 ^ s * Lattice.jp p.2 ^ t * ‖u p.1 p.2‖ ≤
        C * nrm2 a b u := by
  set F1 : Lattice d → ℝ := fun k => Lattice.jp k ^ ((s : ℝ) - a) with hF1
  set F2 : Lattice d → ℝ := fun k => Lattice.jp k ^ ((t : ℝ) - b) with hF2
  have s1 : Summable fun k : Lattice d => F1 k ^ 2 := by
    refine (MFPair.summable_jp_rpow_ps (d := d) (2 * ((s : ℝ) - a)) (by linarith)).congr fun k => ?_
    simp only [hF1]; rw [Torus.jp_rpow_sq]
  have s2 : Summable fun k : Lattice d => F2 k ^ 2 := by
    refine (MFPair.summable_jp_rpow_ps (d := d) (2 * ((t : ℝ) - b)) (by linarith)).congr fun k => ?_
    simp only [hF2]; rw [Torus.jp_rpow_sq]
  have n1 : ∀ k, 0 ≤ F1 k ^ 2 := fun k => sq_nonneg _
  have n2 : ∀ k, 0 ≤ F2 k ^ 2 := fun k => sq_nonneg _
  have hf2 : Summable fun p : Lattice d × Lattice d => (F1 p.1 * F2 p.2) ^ 2 := by
    refine (Summable.mul_of_nonneg s1 s2 n1 n2).congr fun p => ?_
    simp [mul_pow]
  refine ⟨Real.sqrt (∑' p : Lattice d × Lattice d, (F1 p.1 * F2 p.2) ^ 2), Real.sqrt_nonneg _, fun u hu => ?_⟩
  set g : Lattice d × Lattice d → ℝ := fun p => Real.sqrt (sobWeight a p.1 * sobWeight b p.2) * ‖u p.1 p.2‖ with hg
  have hg2 : ∀ p, g p ^ 2 = sobWeight a p.1 * sobWeight b p.2 * ‖u p.1 p.2‖ ^ 2 := fun p => by
    simp only [hg, mul_pow, Real.sq_sqrt (px7_w_nonneg a b p)]
  have hgs : Summable fun p => g p ^ 2 := hu.congr fun p => (hg2 p).symm
  have f0 : ∀ p : Lattice d × Lattice d, 0 ≤ F1 p.1 * F2 p.2 := fun p =>
    mul_nonneg (Real.rpow_nonneg (Torus.jp_pos _).le _) (Real.rpow_nonneg (Torus.jp_pos _).le _)
  have g0 : ∀ p, 0 ≤ g p := fun p => mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  obtain ⟨hs, hle⟩ := Torus.cs_tsum (fun p : Lattice d × Lattice d => F1 p.1 * F2 p.2) g f0 g0 hf2 hgs
  have hfg : ∀ p : Lattice d × Lattice d, F1 p.1 * F2 p.2 * g p =
      Lattice.jp p.1 ^ s * Lattice.jp p.2 ^ t * ‖u p.1 p.2‖ := by
    intro p
    have e1 : Real.sqrt (sobWeight a p.1 * sobWeight b p.2) = Lattice.jp p.1 ^ a * Lattice.jp p.2 ^ b := by
      rw [Real.sqrt_mul (sobWeight_pos a _).le, px7_sqrt_sobWeight, px7_sqrt_sobWeight]
    have e2 : Lattice.jp p.1 ^ ((s : ℝ) - a) * Lattice.jp p.1 ^ a = Lattice.jp p.1 ^ s := by
      rw [← Real.rpow_add (Torus.jp_pos _)]; simp
    have e3 : Lattice.jp p.2 ^ ((t : ℝ) - b) * Lattice.jp p.2 ^ b = Lattice.jp p.2 ^ t := by
      rw [← Real.rpow_add (Torus.jp_pos _)]; simp
    simp only [hg, hF1, hF2, e1]
    calc _ = (Lattice.jp p.1 ^ ((s : ℝ) - a) * Lattice.jp p.1 ^ a) *
          (Lattice.jp p.2 ^ ((t : ℝ) - b) * Lattice.jp p.2 ^ b) * ‖u p.1 p.2‖ := by ring
      _ = _ := by rw [e2, e3]
  refine ⟨hs.congr fun p => hfg p, ?_⟩
  have e4 : ∑' p : Lattice d × Lattice d, Lattice.jp p.1 ^ s * Lattice.jp p.2 ^ t * ‖u p.1 p.2‖ =
      ∑' p, F1 p.1 * F2 p.2 * g p := tsum_congr fun p => (hfg p).symm
  rw [e4]
  refine hle.trans (le_of_eq ?_)
  unfold nrm2
  congr 2
  exact tsum_congr hg2


/-! ### Evaluation of arrays as kernels -/

/-- The kernel `(x, y) ↦ Re ∑ u k l e_k(x) e_l(y)`. -/
def ev (u : Arr d) (x y : Torus d) : ℝ :=
  (∑' p : Lattice d × Lattice d, u p.1 p.2 * Torus.mode p.1 x * Torus.mode p.2 y).re

/-- Real symmetry `u(-k,-l) = conj u(k,l)`. -/
def RS (u : Arr d) : Prop := ∀ k l, u (-k) (-l) = conj (u k l)

/-- Fixed-`y` coefficients in `x`. -/
def acol (u : Arr d) (y : Torus d) : Coeff d := fun k => ∑' l, u k l * Torus.mode l y

/-- Fixed-`x` coefficients in `y`. -/
def arow (u : Arr d) (x : Torus d) : Coeff d := fun l => ∑' k, u k l * Torus.mode k x

theorem px7_term_summable {u : Arr d} (hu : Summable fun p : Lattice d × Lattice d => ‖u p.1 p.2‖)
    (x y : Torus d) :
    Summable fun p : Lattice d × Lattice d => u p.1 p.2 * Torus.mode p.1 x * Torus.mode p.2 y := by
  refine Summable.of_norm_bounded hu fun p => ?_
  simp [norm_mul, Torus.norm_mode]

theorem px7_ev_add {u v : Arr d} (hu : Summable fun p : Lattice d × Lattice d => ‖u p.1 p.2‖)
    (hv : Summable fun p : Lattice d × Lattice d => ‖v p.1 p.2‖) (x y : Torus d) :
    ev (u + v) x y = ev u x y + ev v x y := by
  unfold ev
  rw [← Complex.add_re, ← (px7_term_summable hu x y).tsum_add (px7_term_summable hv x y)]
  congr 1
  exact tsum_congr fun p => by simp [add_mul]

theorem px7_ev_neg (u : Arr d) (x y : Torus d) : ev (-u) x y = -ev u x y := by
  unfold ev
  rw [← Complex.neg_re, ← tsum_neg]
  congr 1
  exact tsum_congr fun p => by simp

theorem px7_ev_sub {u v : Arr d} (hu : Summable fun p : Lattice d × Lattice d => ‖u p.1 p.2‖)
    (hv : Summable fun p : Lattice d × Lattice d => ‖v p.1 p.2‖) (x y : Torus d) :
    ev (u - v) x y = ev u x y - ev v x y := by
  have hnv : Summable fun p : Lattice d × Lattice d => ‖(-v) p.1 p.2‖ := by simpa using hv
  have := px7_ev_add hu hnv x y
  rw [px7_ev_neg] at this
  rw [sub_eq_add_neg, this]; ring

theorem px7_abs_ev_le {u : Arr d} (hu : Summable fun p : Lattice d × Lattice d => ‖u p.1 p.2‖)
    (x y : Torus d) : |ev u x y| ≤ ∑' p : Lattice d × Lattice d, ‖u p.1 p.2‖ := by
  unfold ev
  refine (Complex.abs_re_le_norm _).trans ?_
  refine (norm_tsum_le_tsum_norm (px7_term_summable hu x y).norm).trans (le_of_eq ?_)
  exact tsum_congr fun p => by simp [norm_mul, Torus.norm_mode]

theorem px7_ev_tr (u : Arr d) (x y : Torus d) : ev (PX7.tr u) x y = ev u y x := by
  unfold ev
  congr 1
  rw [← (Equiv.prodComm (Lattice d) (Lattice d)).tsum_eq]
  exact tsum_congr fun p => by simp only [PX7.tr, Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap]; ring

theorem px7_ev_eq_toFun {u : Arr d} (hu : Summable fun p : Lattice d × Lattice d => ‖u p.1 p.2‖)
    (x y : Torus d) : ev u x y = toFun (acol u y) x := by
  unfold ev toFun series acol
  congr 1
  rw [(px7_term_summable hu x y).tsum_prod]
  refine tsum_congr fun k => ?_
  rw [← tsum_mul_right]
  exact tsum_congr fun l => by ring

theorem px7_ev_eq_toFun' {u : Arr d} (hu : Summable fun p : Lattice d × Lattice d => ‖u p.1 p.2‖)
    (x y : Torus d) : ev u x y = toFun (arow u x) y := by
  have hu' : Summable fun p : Lattice d × Lattice d => ‖PX7.tr u p.1 p.2‖ := by
    have := (Equiv.prodComm (Lattice d) (Lattice d)).summable_iff.2 hu
    exact this
  have h := px7_ev_eq_toFun hu' y x
  rw [px7_ev_tr] at h
  exact h


/-! ### Inversion and reality -/

theorem px7_arr_RS {R : Torus d → Torus d → ℝ} (hR : Continuous (lift2 R)) : RS (arr R) := by
  intro k l
  rw [px7_arr_eq R hR, px7_arr_eq R hR, ← integral_conj]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  simp only [neg_neg, map_mul, Complex.conj_ofReal, Torus.mode_neg, Complex.conj_conj]

theorem px7_summable_arr {m : ℕ} (hm : (d : ℝ) < 2 * m) {R : Torus d → Torus d → ℝ}
    (hR : IsCk2 (m + m) R) : Summable fun p : Lattice d × Lattice d => ‖arr R p.1 p.2‖ := by
  obtain ⟨K, hK, hP⟩ := px7_parseval (d := d) m m
  obtain ⟨h1, -⟩ := hP R hR
  obtain ⟨C, hC, hCS⟩ := px7_cs (d := d) (m : ℝ) (m : ℝ) 0 0 (by simpa using hm) (by simpa using hm)
  simpa using (hCS (arr R) h1).1

theorem px7_inversion {m : ℕ} (hm : (d : ℝ) < 2 * m) {R : Torus d → Torus d → ℝ}
    (hR : IsCk2 (m + m) R) (x y : Torus d) : R x y = ev (arr R) x y := by
  have hs := px7_summable_arr hm hR
  have hR0 : IsCk2 0 R := hR.of_le (by exact_mod_cast Nat.zero_le _)
  have hJ : (d : ℝ) / 2 < ((m + m : ℕ) : ℝ) := by push_cast; linarith [(by positivity : (0 : ℝ) ≤ (d : ℝ) / 2)]
  obtain ⟨h1, -⟩ := MFPair.eq_toFun_sliceCoeff (m + m) hJ R hR x y
  rw [h1, px7_ev_eq_toFun hs x y]
  unfold toFun series
  congr 1
  refine tsum_congr fun k => ?_
  congr 1
  -- the series in `y` of the slice coefficient
  have hcont := px7_continuous_sliceCoeff hR0 k
  have hsk : Summable fun l => ‖arr R k l‖ := hs.prod_factor k
  let f : C(UnitAddTorus (Fin d), ℂ) := ⟨fun y => sliceCoeff R k y, hcont⟩
  have hsum : Summable (UnitAddTorus.mFourierCoeff (⇑f)) := Summable.of_norm hsk
  have := UnitAddTorus.hasSum_mFourier_series_apply_of_summable hsum y
  have e : ∀ l, UnitAddTorus.mFourierCoeff (⇑f) l • UnitAddTorus.mFourier l y = arr R k l * Torus.mode l y := fun l => by
    simp [arr, coeffOfC, Torus.funFourierCoeff, Torus.mode, f]
  simp_rw [e] at this
  exact this.tsum_eq.symm


/-! ### `C²` bound for `ev` -/

section EvCk

/-- The linear functional `(x, y) ↦ 2π (k·x + l·y)`. -/
def lq (q : Lattice d × Lattice d) : (Euc d × Euc d) →L[ℝ] ℝ :=
  (Torus.freqFunctional q.1).comp (ContinuousLinearMap.fst ℝ (Euc d) (Euc d)) +
    (Torus.freqFunctional q.2).comp (ContinuousLinearMap.snd ℝ (Euc d) (Euc d))

theorem px7_lq_apply (q : Lattice d × Lattice d) (p : Euc d × Euc d) :
    lq q p = 2 * Real.pi * Lattice.dot q.1 p.1 + 2 * Real.pi * Lattice.dot q.2 p.2 := by
  simp [lq, Torus.freqFunctional_apply]

theorem px7_norm_lq_le (q : Lattice d × Lattice d) : ‖lq q‖ ≤ Lattice.jp q.1 + Lattice.jp q.2 := by
  have h1 : ‖(Torus.freqFunctional q.1).comp (ContinuousLinearMap.fst ℝ (Euc d) (Euc d))‖ ≤
      Lattice.jp q.1 := by
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    calc _ ≤ ‖Torus.freqFunctional q.1‖ * 1 := by
          gcongr; exact ContinuousLinearMap.norm_fst_le ℝ (Euc d) (Euc d)
      _ ≤ Lattice.jp q.1 := by
          rw [mul_one]; exact (Torus.norm_freqFunctional_le _).trans (Torus.two_pi_enorm_le_jp _)
  have h2 : ‖(Torus.freqFunctional q.2).comp (ContinuousLinearMap.snd ℝ (Euc d) (Euc d))‖ ≤
      Lattice.jp q.2 := by
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    calc _ ≤ ‖Torus.freqFunctional q.2‖ * 1 := by
          gcongr; exact ContinuousLinearMap.norm_snd_le ℝ (Euc d) (Euc d)
      _ ≤ Lattice.jp q.2 := by
          rw [mul_one]; exact (Torus.norm_freqFunctional_le _).trans (Torus.two_pi_enorm_le_jp _)
  exact (norm_add_le _ _).trans (add_le_add h1 h2)

theorem px7_norm_iter_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (g : ℝ → ℝ)
    (hg : ContDiff ℝ ⊤ g) (B : ℝ) (hB : ∀ (i : ℕ) (t : ℝ), ‖iteratedFDeriv ℝ i g t‖ ≤ B)
    (ℓ : E →L[ℝ] ℝ) (i : ℕ) (x : E) : ‖iteratedFDeriv ℝ i (g ∘ ℓ) x‖ ≤ B * ‖ℓ‖ ^ i := by
  rw [ℓ.iteratedFDeriv_comp_right hg x (le_top)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  gcongr
  exact hB i _

/-- The `q`-th real term of `ev u` as a function on `ℝ^d × ℝ^d`. -/
def tq (u : Arr d) (q : Lattice d × Lattice d) : Euc d × Euc d → ℝ := fun p =>
  (u q.1 q.2).re * Real.cos (lq q p) + (-(u q.1 q.2).im) * Real.sin (lq q p)

theorem px7_lift2_ev {u : Arr d} (hu : Summable fun p : Lattice d × Lattice d => ‖u p.1 p.2‖) :
    lift2 (ev u) = fun p => ∑' q, tq u q p := by
  funext p
  unfold lift2 ev
  have h := Complex.reCLM.hasSum (px7_term_summable hu (Torus.mk p.1) (Torus.mk p.2)).hasSum
  calc (∑' q : Lattice d × Lattice d, u q.1 q.2 * Torus.mode q.1 (Torus.mk p.1) *
        Torus.mode q.2 (Torus.mk p.2)).re
      = Complex.reCLM (∑' q : Lattice d × Lattice d, u q.1 q.2 * Torus.mode q.1 (Torus.mk p.1) *
        Torus.mode q.2 (Torus.mk p.2)) := rfl
    _ = ∑' q : Lattice d × Lattice d, Complex.reCLM (u q.1 q.2 * Torus.mode q.1 (Torus.mk p.1) *
        Torus.mode q.2 (Torus.mk p.2)) := h.tsum_eq.symm
    _ = ∑' q, tq u q p := by
      refine tsum_congr fun q => ?_
      simp only [Complex.reCLM_apply, tq, Torus.mode_mk]
      rw [mul_assoc, ← Complex.exp_add, ← add_mul, ← Complex.ofReal_add, ← px7_lq_apply,
        Complex.mul_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
      ring


theorem px7_ev_C2 {m : ℕ} (hm : (d : ℝ) + 4 < 2 * m) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ u : Arr d, Mem2 (m : ℝ) (m : ℝ) u →
      IsCk2 2 (ev u) ∧ cbNorm2 2 (ev u) ≤ A * nrm2 (m : ℝ) (m : ℝ) u := by
  have hcs : ∀ k : ℕ, k ≤ 2 → ∃ C : ℝ, 0 ≤ C ∧ ∀ u : Arr d, Mem2 (m : ℝ) (m : ℝ) u →
      Summable (fun p : Lattice d × Lattice d => Lattice.jp p.1 ^ k * Lattice.jp p.2 ^ k * ‖u p.1 p.2‖) ∧
      ∑' p : Lattice d × Lattice d, Lattice.jp p.1 ^ k * Lattice.jp p.2 ^ k * ‖u p.1 p.2‖ ≤
        C * nrm2 (m : ℝ) (m : ℝ) u := by
    intro k hk
    have hk' : (k : ℝ) ≤ 2 := by exact_mod_cast hk
    exact px7_cs (m : ℝ) (m : ℝ) k k (by linarith) (by linarith)
  obtain ⟨C0, hC0, h0⟩ := hcs 0 (by norm_num)
  obtain ⟨C1, hC1, h1⟩ := hcs 1 (by norm_num)
  obtain ⟨C2, hC2, h2⟩ := hcs 2 le_rfl
  refine ⟨2 * C0 + 4 * C1 + 8 * C2, by positivity, fun u hu => ?_⟩
  have hs0 : Summable fun p : Lattice d × Lattice d => ‖u p.1 p.2‖ := by
    simpa using (h0 u hu).1
  set v : ℕ → Lattice d × Lattice d → ℝ := fun k q =>
    2 * 2 ^ k * (Lattice.jp q.1 ^ k * Lattice.jp q.2 ^ k * ‖u q.1 q.2‖) with hv
  have hvs : ∀ k : ℕ, k ≤ 2 → Summable (v k) := by
    intro k hk
    have : Summable fun q : Lattice d × Lattice d =>
        Lattice.jp q.1 ^ k * Lattice.jp q.2 ^ k * ‖u q.1 q.2‖ := by
      interval_cases k
      · exact (h0 u hu).1
      · exact (h1 u hu).1
      · exact (h2 u hu).1
    exact this.mul_left _
  have hcomb : ∀ q : Lattice d × Lattice d, ContDiff ℝ ⊤ (tq u q) := fun q =>
    ((contDiff_const.mul Real.contDiff_cos).add (contDiff_const.mul Real.contDiff_sin)).comp
      (lq q).contDiff
  have hbd : ∀ (k : ℕ) (q : Lattice d × Lattice d) (p : Euc d × Euc d), k ≤ 2 →
      ‖iteratedFDeriv ℝ k (tq u q) p‖ ≤ v k q := by
    intro k q p hk
    have hb := px7_norm_iter_comp (fun t => (u q.1 q.2).re * Real.cos t + (-(u q.1 q.2).im) * Real.sin t)
      ((contDiff_const.mul Real.contDiff_cos).add (contDiff_const.mul Real.contDiff_sin))
      (|(u q.1 q.2).re| + |-(u q.1 q.2).im|) (fun i t => norm_iteratedFDeriv_trig_comb _ _ i t)
      (lq q) k p
    refine hb.trans ?_
    have h1' : |(u q.1 q.2).re| + |-(u q.1 q.2).im| ≤ 2 * ‖u q.1 q.2‖ := by
      rw [abs_neg]
      have := Complex.abs_re_le_norm (u q.1 q.2)
      have := Complex.abs_im_le_norm (u q.1 q.2)
      linarith
    have h2' : ‖lq q‖ ^ k ≤ 2 ^ k * (Lattice.jp q.1 ^ k * Lattice.jp q.2 ^ k) := by
      have j1 := Torus.jp_ge_one q.1
      have j2 := Torus.jp_ge_one q.2
      have : Lattice.jp q.1 + Lattice.jp q.2 ≤ 2 * (Lattice.jp q.1 * Lattice.jp q.2) := by nlinarith
      calc ‖lq q‖ ^ k ≤ (Lattice.jp q.1 + Lattice.jp q.2) ^ k :=
            pow_le_pow_left₀ (norm_nonneg _) (px7_norm_lq_le q) k
        _ ≤ (2 * (Lattice.jp q.1 * Lattice.jp q.2)) ^ k :=
            pow_le_pow_left₀ (by positivity) this k
        _ = _ := by rw [mul_pow, mul_pow]
    simp only [hv]
    calc (|(u q.1 q.2).re| + |-(u q.1 q.2).im|) * ‖lq q‖ ^ k
        ≤ (2 * ‖u q.1 q.2‖) * (2 ^ k * (Lattice.jp q.1 ^ k * Lattice.jp q.2 ^ k)) :=
          mul_le_mul h1' h2' (by positivity) (by positivity)
      _ = _ := by ring
  have hlift := px7_lift2_ev hs0
  refine ⟨?_, ?_⟩
  · unfold IsCk2
    rw [hlift]
    exact contDiff_tsum (N := 2) (fun q => (hcomb q).of_le le_top) (fun k hk => hvs k (by exact_mod_cast hk))
      (fun k q p hk => hbd k q p (by exact_mod_cast hk))
  · have hsupi : ∀ i : ℕ, i ≤ 2 → ∀ p : Euc d × Euc d,
        ‖iteratedFDeriv ℝ i (lift2 (ev u)) p‖ ≤ ∑' q, v i q := by
      intro i hi p
      rw [hlift]
      have hf : ∀ q, ContDiff ℝ (((2 : ℕ) : ℕ∞) : WithTop ℕ∞) (tq u q) := fun q => (hcomb q).of_le le_top
      rw [iteratedFDeriv_tsum_apply (N := 2) hf (fun k hk => hvs k (by exact_mod_cast hk))
        (fun k q p hk => hbd k q p (by exact_mod_cast hk)) (by exact_mod_cast hi) p]
      have hns : Summable fun q => ‖iteratedFDeriv ℝ i (tq u q) p‖ :=
        Summable.of_nonneg_of_le (fun q => norm_nonneg _) (fun q => hbd i q p hi) (hvs i hi)
      exact (norm_tsum_le_tsum_norm hns).trans
        (Summable.tsum_le_tsum (fun q => hbd i q p hi) hns (hvs i hi))
    have hvi : ∀ i : ℕ, i ≤ 2 → ∀ C : ℝ, (∑' q : Lattice d × Lattice d,
        Lattice.jp q.1 ^ i * Lattice.jp q.2 ^ i * ‖u q.1 q.2‖ ≤ C * nrm2 (m : ℝ) (m : ℝ) u) →
        ∑' q, v i q ≤ 2 * 2 ^ i * C * nrm2 (m : ℝ) (m : ℝ) u := by
      intro i hi C hC
      simp only [hv]
      rw [tsum_mul_left]
      calc 2 * 2 ^ i * ∑' q : Lattice d × Lattice d, Lattice.jp q.1 ^ i * Lattice.jp q.2 ^ i * ‖u q.1 q.2‖
          ≤ 2 * 2 ^ i * (C * nrm2 (m : ℝ) (m : ℝ) u) := mul_le_mul_of_nonneg_left hC (by positivity)
        _ = _ := by ring
    have hsi : ∀ i : ℕ, i ≤ 2 → ∀ C : ℝ,
        (∑' q : Lattice d × Lattice d, Lattice.jp q.1 ^ i * Lattice.jp q.2 ^ i * ‖u q.1 q.2‖ ≤
          C * nrm2 (m : ℝ) (m : ℝ) u) →
        (⨆ p : Euc d × Euc d, ‖iteratedFDeriv ℝ i (lift2 (ev u)) p‖) ≤
          2 * 2 ^ i * C * nrm2 (m : ℝ) (m : ℝ) u := fun i hi C hC =>
      ciSup_le fun p => (hsupi i hi p).trans (hvi i hi C hC)
    unfold cbNorm2
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
    have b0 := hsi 0 (by norm_num) C0 (by simpa using (h0 u hu).2)
    have b1 := hsi 1 (by norm_num) C1 (by simpa using (h1 u hu).2)
    have b2 := hsi 2 le_rfl C2 (h2 u hu).2
    nlinarith [b0, b1, b2]

end EvCk


theorem px7_arr_lin {R R' : Torus d → Torus d → ℝ} (hR : Continuous (lift2 R))
    (hR' : Continuous (lift2 R')) (a b : ℝ) (k l : Lattice d) :
    arr (fun x y => a * R x y + b * R' x y) k l = (a : ℂ) * arr R k l + (b : ℂ) * arr R' k l := by
  have hc : Continuous (lift2 (fun x y => a * R x y + b * R' x y)) := by
    have e : lift2 (fun x y => a * R x y + b * R' x y) = fun p => a * lift2 R p + b * lift2 R' p := rfl
    rw [e]; exact (continuous_const.mul hR).add (continuous_const.mul hR')
  have c1 := continuous_pair_of_continuous_lift2 hR
  have c2 := continuous_pair_of_continuous_lift2 hR'
  have hm : Continuous fun p : Torus d × Torus d => Torus.mode (-k) p.1 * Torus.mode (-l) p.2 :=
    ((Torus.continuous_mode _).comp continuous_fst).mul ((Torus.continuous_mode _).comp continuous_snd)
  have i1 : Integrable (fun p : Torus d × Torus d =>
      Torus.mode (-k) p.1 * Torus.mode (-l) p.2 * ((R p.1 p.2 : ℝ) : ℂ))
      ((volume : Measure (Torus d)).prod (volume : Measure (Torus d))) :=
    (hm.mul (Complex.continuous_ofReal.comp c1)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have i2 : Integrable (fun p : Torus d × Torus d =>
      Torus.mode (-k) p.1 * Torus.mode (-l) p.2 * ((R' p.1 p.2 : ℝ) : ℂ))
      ((volume : Measure (Torus d)).prod (volume : Measure (Torus d))) :=
    (hm.mul (Complex.continuous_ofReal.comp c2)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [px7_arr_eq _ hc, px7_arr_eq R hR, px7_arr_eq R' hR', ← integral_const_mul, ← integral_const_mul,
    ← integral_add (i1.const_mul _) (i2.const_mul _)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  simp only
  push_cast
  ring

end Kernels

end HRS.PDE.PX7

end
