import HRS.PDE.Galerkin
import HRS.PDE.EnergyEstimate
import HRS.PDE.Convention

/-!
# Uniqueness of `C_w([0,t];H^1)` forward solutions: helper lemmas

Helpers for `forward_unique_H1` (Step 5 of the proof of Prop 3.9, lines 1936-1939): the operator
bound `H^1 -> H^{-1}` of the forward generator, the `l^2`-multiplier bound of a bounded
coefficient function, absolutely continuous primitives, Gronwall in integral form, and the
energy argument for the Fourier truncations `P_n z`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.PDE

variable {d : ℕ}


theorem cbNorm_monoU {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {k k' : ℕ} (h : k ≤ k')
    (φ : Torus d → E) : Torus.cbNorm k φ ≤ Torus.cbNorm k' φ := by
  unfold Torus.cbNorm
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (by omega)) ?_
  intro j _ _
  exact Real.iSup_nonneg fun x => norm_nonneg _

theorem adjointData_zero {s : ℝ} {m : ℕ} {R : Regime} {MB Λ VB : ℝ} {D : DynData d} {ν₀ T : ℝ}
    {μ : ℝ → Torus d → ℝ} (h : AdjointData s m R MB Λ VB D ν₀ T μ) :
    AdjointData s 0 R MB Λ VB D ν₀ T μ := by
  have hle : ((0 : ℕ) : WithTop ℕ∞) + 3 ≤ (m : WithTop ℕ∞) + 3 := by
    gcongr; exact_mod_cast Nat.zero_le m
  refine ⟨h.hs, h.hM, ⟨?_, ?_⟩, ⟨h.hμ.prob, fun r hr => ?_, fun r hr => ?_, h.hμ.cont⟩, h.hT, h.regime⟩
  · exact (h.hV.1).of_le hle
  · exact (cbNorm_monoU (by omega) _).trans h.hV.2
  · exact (h.hμ.smooth r hr).of_le hle
  · exact (cbNorm_monoU (by omega) _).trans (h.hμ.bound r hr)




theorem memℓp_of_memHs0 (w : Coeff d) (hw : MemHs 0 w) : Memℓp w 2 := by
  rw [memℓp_gen_iff (by simp)]
  have := (memHs_zero_iff w).1 hw
  simpa using this

theorem exists_L2_fun (w : Coeff d) (hw : MemHs 0 w) :
    ∃ u : Torus d → ℂ, MemLp u 2 volume ∧ ∀ n, Torus.funFourierCoeff u n = w n := by
  let lw : lp (fun _ : Lattice d => ℂ) 2 := ⟨w, memℓp_of_memHs0 w hw⟩
  let f := UnitAddTorus.mFourierBasis.repr.symm lw
  have hf : MemLp (f : Torus d → ℂ) 2 (Measure.pi fun _ : Fin d =>
      (AddCircle.haarAddCircle : Measure UnitAddCircle)) := Lp.memLp f
  refine ⟨f, ?_, fun n => ?_⟩
  · rw [Torus.volume_eq_pi_haar]; exact hf
  · have h1 : UnitAddTorus.mFourierBasis.repr f n = UnitAddTorus.mFourierCoeff f n :=
      UnitAddTorus.mFourierBasis_repr f n
    have h2 : UnitAddTorus.mFourierBasis.repr f = lw := by
      simp [f]
    have h3 : UnitAddTorus.mFourierBasis.repr f n = w n := by
      rw [h2]
    rw [← h3, h1]
    rfl

/-- Coefficients of `a · u` for a real `L²` function `a` and complex `L²` function `u`. -/
theorem coeffC_mul (a : Torus d → ℝ) (u : Torus d → ℂ) (ha : MemLp a 2 volume)
    (hu : MemLp u 2 volume) (k : Lattice d) :
    Torus.funFourierCoeff (fun x => (a x : ℂ) * u x) k =
      mulCoeff (coeffOf a) (Torus.funFourierCoeff u) k := by
  set F : Torus d → ℂ := fun x => (a x : ℂ) with hF
  set G : Torus d → ℂ := fun x => Torus.mode (-k) x * u x with hG
  have hFm : MemLp F 2 volume := ha.ofReal
  have hGm : MemLp G 2 volume := by
    refine hu.of_le_mul (c := 1)
      ((Torus.continuous_mode (-k)).aestronglyMeasurable.mul hu.aestronglyMeasurable) ?_
    refine Filter.Eventually.of_forall fun x => ?_
    simp [hG, Torus.norm_mode]
  have hP := hasSum_parseval F G hFm hGm
  have e1 : ∀ n : Lattice d, conj (Torus.funFourierCoeff F n) * Torus.funFourierCoeff G n =
      coeffOf a (k - (n + k)) * Torus.funFourierCoeff u (n + k) := by
    intro n
    have h1 : Torus.funFourierCoeff F n = coeffOf a n := rfl
    have h2 : Torus.funFourierCoeff G n = Torus.funFourierCoeff u (n + k) := by
      rw [funFourierCoeff_eq_int, funFourierCoeff_eq_int]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      have := Torus.mode_add (-n) (-k) x
      rw [← neg_add] at this
      simp only [hG, Torus.mode] at this ⊢
      rw [← mul_assoc, ← this]
    have h3 : conj (coeffOf a n) = coeffOf a (-n) := (isRealCoeff_coeffOf a (ha.integrable one_le_two) n).symm
    rw [h1, h2, h3]
    congr 2
    abel
  have e2 : ∫ t, conj (F t) * G t = Torus.funFourierCoeff (fun x => (a x : ℂ) * u x) k := by
    rw [funFourierCoeff_eq_int]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [hF, hG, Torus.mode, Complex.conj_ofReal]
    ring
  simp_rw [e1, e2] at hP
  have hP2 : HasSum (fun j : Lattice d => coeffOf a (k - j) * Torus.funFourierCoeff u j)
      (Torus.funFourierCoeff (fun x => (a x : ℂ) * u x) k) :=
    (Equiv.addRight k).hasSum_iff.mp hP
  exact hP2.tsum_eq.symm

/-- Parseval for `‖·‖²`. -/
theorem parseval_sq (F : Torus d → ℂ) (hF : MemLp F 2 volume) :
    HasSum (fun n : Lattice d => ‖Torus.funFourierCoeff F n‖ ^ 2) (∫ t, ‖F t‖ ^ 2) := by
  have h := hasSum_parseval F F hF hF
  have e : ∀ z : ℂ, conj z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    intro z; rw [Complex.conj_mul']; push_cast; ring
  simp_rw [e] at h
  rw [integral_complex_ofReal] at h
  exact (Complex.hasSum_ofReal).1 h


/-- `ℓ²`-boundedness of the convolution operator `w ↦ a * w` with constant `K`. -/
def MultBound (a : Coeff d) (K : ℝ) : Prop :=
  ∀ w : Coeff d, MemHs 0 w → MemHs 0 (mulCoeff a w) ∧ hsNormSq 0 (mulCoeff a w) ≤ K ^ 2 * hsNormSq 0 w

theorem multBound_of_sup (f : Torus d → ℝ) (hc : Continuous f) (B : ℝ) (hB : ∀ x, |f x| ≤ B) :
    MultBound (coeffOf f) B := by
  intro w hw
  obtain ⟨u, hu, hcu⟩ := exists_L2_fun w hw
  have hfL : MemLp f 2 volume := MemLp.of_bound hc.aestronglyMeasurable B
    (Filter.Eventually.of_forall fun x => by simpa using hB x)
  set G : Torus d → ℂ := fun x => (f x : ℂ) * u x with hG
  have hGm : MemLp G 2 volume := by
    refine hu.of_le_mul (c := B)
      ((Complex.continuous_ofReal.comp hc).aestronglyMeasurable.mul hu.aestronglyMeasurable) ?_
    refine Filter.Eventually.of_forall fun x => ?_
    simp only [hG, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hB x) (norm_nonneg _)
  have hco : ∀ k, Torus.funFourierCoeff G k = mulCoeff (coeffOf f) w k := by
    intro k
    have := coeffC_mul f u hfL hu k
    have e : Torus.funFourierCoeff u = w := funext hcu
    rw [e] at this
    exact this
  have hPG := parseval_sq G hGm
  have hPu := parseval_sq u hu
  simp_rw [hco] at hPG
  simp_rw [hcu] at hPu
  have hsw : hsNormSq 0 w = ∫ t, ‖u t‖ ^ 2 := by
    unfold hsNormSq
    simp_rw [sobWeight_zero, one_mul]
    exact hPu.tsum_eq
  have hsG : hsNormSq 0 (mulCoeff (coeffOf f) w) = ∫ t, ‖G t‖ ^ 2 := by
    unfold hsNormSq
    simp_rw [sobWeight_zero, one_mul]
    exact hPG.tsum_eq
  refine ⟨?_, ?_⟩
  · rw [memHs_zero_iff]; exact hPG.summable
  · rw [hsG, hsw, ← integral_const_mul]
    refine integral_mono (hGm.integrable_norm_pow (by norm_num)) ?_ fun x => ?_
    · exact (hu.integrable_norm_pow (by norm_num)).const_mul _
    · simp only [hG, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have := hB x
      have h0 := norm_nonneg (u x)
      calc (|f x| * ‖u x‖) ^ 2 = |f x| ^ 2 * ‖u x‖ ^ 2 := by ring
        _ ≤ B ^ 2 * ‖u x‖ ^ 2 := by gcongr





theorem sobWeight_oneU (k : Lattice d) : sobWeight 1 k = 1 + 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2 := by
  simp [sobWeight]

theorem one_le_sobWeight_one (k : Lattice d) : 1 ≤ sobWeight 1 k := by
  rw [sobWeight_oneU]; nlinarith [sq_nonneg (Lattice.enorm k), sq_nonneg Real.pi]

/-- `W k = √(1 + 4π²|k|²)`. -/
def sw (k : Lattice d) : ℝ := Real.sqrt (sobWeight 1 k)

theorem sw_sq (k : Lattice d) : sw k ^ 2 = sobWeight 1 k :=
  Real.sq_sqrt (sobWeight_nonneg 1 k)

theorem one_le_sw (k : Lattice d) : 1 ≤ sw k := by
  unfold sw
  exact Real.le_sqrt_of_sq_le (by simpa using one_le_sobWeight_one k)

theorem sw_nonneg (k : Lattice d) : 0 ≤ sw k := (zero_le_one.trans (one_le_sw k))

theorem memHs_zero_of_memHs_one {c : Coeff d} (hc : MemHs 1 c) : MemHs 0 c ∧ hsNormSq 0 c ≤ hsNormSq 1 c := by
  have hle : ∀ k : Lattice d, sobWeight 0 k * ‖c k‖ ^ 2 ≤ sobWeight 1 k * ‖c k‖ ^ 2 := by
    intro k
    rw [sobWeight_zero]
    nlinarith [one_le_sobWeight_one k, sq_nonneg ‖c k‖]
  have hs : MemHs 0 c := Summable.of_nonneg_of_le
    (fun k => mul_nonneg (sobWeight_nonneg 0 k) (sq_nonneg _)) hle hc
  exact ⟨hs, hs.tsum_le_tsum hle hc⟩

theorem enorm_sq_ge_sq (k : Lattice d) (j : Fin d) : ((k j : ℤ) : ℝ) ^ 2 ≤ Lattice.enorm k ^ 2 := by
  rw [enorm_sq_eq_sum]
  exact Finset.single_le_sum (f := fun i => ((k i : ℤ) : ℝ) ^ 2) (fun i _ => sq_nonneg _)
    (Finset.mem_univ j)

theorem norm_derivCoeff_le (j : Fin d) (c : Coeff d) (k : Lattice d) :
    ‖derivCoeff j c k‖ ≤ sw k * ‖c k‖ := by
  unfold derivCoeff
  rw [norm_mul]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  have : ‖(2 * (Real.pi : ℂ) * Complex.I * ((k j : ℤ) : ℂ))‖ = 2 * Real.pi * |((k j : ℤ) : ℝ)| := by
    simp [Complex.norm_I, abs_of_pos Real.pi_pos]
  rw [this]
  unfold sw
  apply Real.le_sqrt_of_sq_le
  rw [sobWeight_oneU]
  have h := enorm_sq_ge_sq k j
  have : (2 * Real.pi * |((k j : ℤ) : ℝ)|) ^ 2 = 4 * Real.pi ^ 2 * ((k j : ℤ) : ℝ) ^ 2 := by
    rw [mul_pow, mul_pow, sq_abs]; ring
  rw [this]
  nlinarith [sq_nonneg Real.pi]

theorem memHs_zero_deriv {c : Coeff d} (hc : MemHs 1 c) (j : Fin d) :
    MemHs 0 (derivCoeff j c) ∧ hsNormSq 0 (derivCoeff j c) ≤ hsNormSq 1 c := by
  have hle : ∀ k : Lattice d, sobWeight 0 k * ‖derivCoeff j c k‖ ^ 2 ≤ sobWeight 1 k * ‖c k‖ ^ 2 := by
    intro k
    rw [sobWeight_zero, one_mul, ← sw_sq]
    have := norm_derivCoeff_le j c k
    calc ‖derivCoeff j c k‖ ^ 2 ≤ (sw k * ‖c k‖) ^ 2 := by gcongr
      _ = _ := by ring
  have hs : MemHs 0 (derivCoeff j c) := Summable.of_nonneg_of_le
    (fun k => mul_nonneg (sobWeight_nonneg 0 k) (sq_nonneg _)) hle hc
  exact ⟨hs, hs.tsum_le_tsum hle hc⟩

/-! ### Dual bounds: `X` is bounded as a functional on `H^1` -/

/-- `Σ_k X k ‖v k‖ ≤ c ‖v‖_{H^1}` for all `v ∈ H^1` (with summability). -/
def DualBound (X : Lattice d → ℝ) (c : ℝ) : Prop :=
  ∀ v : Coeff d, MemHs 1 v → Summable (fun k => X k * ‖v k‖) ∧ ∑' k, X k * ‖v k‖ ≤ c * hsNorm 1 v

theorem DualBound.mono {X Y : Lattice d → ℝ} {c : ℝ} (h : DualBound X c)
    (hY : ∀ k, 0 ≤ Y k ∧ Y k ≤ X k) : DualBound Y c := by
  intro v hv
  obtain ⟨hs, hle⟩ := h v hv
  have hle' : ∀ k, Y k * ‖v k‖ ≤ X k * ‖v k‖ := fun k =>
    mul_le_mul_of_nonneg_right (hY k).2 (norm_nonneg _)
  have hs' : Summable (fun k => Y k * ‖v k‖) :=
    Summable.of_nonneg_of_le (fun k => mul_nonneg (hY k).1 (norm_nonneg _)) hle' hs
  exact ⟨hs', (hs'.tsum_le_tsum hle' hs).trans hle⟩

theorem DualBound.add {X Y : Lattice d → ℝ} {c c' : ℝ} (hX : DualBound X c) (hY : DualBound Y c') :
    DualBound (fun k => X k + Y k) (c + c') := by
  intro v hv
  obtain ⟨hs, hle⟩ := hX v hv
  obtain ⟨hs', hle'⟩ := hY v hv
  have hsum : Summable (fun k => (X k + Y k) * ‖v k‖) := by
    simpa [add_mul] using hs.add hs'
  refine ⟨hsum, ?_⟩
  have : ∑' k, (X k + Y k) * ‖v k‖ = ∑' k, X k * ‖v k‖ + ∑' k, Y k * ‖v k‖ := by
    simp_rw [add_mul]; exact hs.tsum_add hs'
  rw [this, add_mul]
  linarith

theorem DualBound.zero : DualBound (fun _ : Lattice d => (0 : ℝ)) 0 := by
  intro v hv
  simp

theorem DualBound.sum {ι : Type*} (S : Finset ι) {X : ι → Lattice d → ℝ} {c : ι → ℝ}
    (h : ∀ i ∈ S, DualBound (X i) (c i)) :
    DualBound (fun k => ∑ i ∈ S, X i k) (∑ i ∈ S, c i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using (DualBound.zero (d := d))
  | insert a S ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem DualBound.const_mul {X : Lattice d → ℝ} {c : ℝ} (h : DualBound X c) {a : ℝ} (ha : 0 ≤ a) :
    DualBound (fun k => a * X k) (a * c) := by
  intro v hv
  obtain ⟨hs, hle⟩ := h v hv
  have hs' : Summable (fun k => a * X k * ‖v k‖) := by
    simpa [mul_assoc] using hs.mul_left a
  refine ⟨hs', ?_⟩
  have : ∑' k, a * X k * ‖v k‖ = a * ∑' k, X k * ‖v k‖ := by
    simp_rw [mul_assoc]; exact tsum_mul_left
  rw [this, mul_assoc]
  exact mul_le_mul_of_nonneg_left hle ha

theorem dual_of_l2 (F X : Lattice d → ℝ) (hF0 : ∀ k, 0 ≤ F k) (hF : Summable fun k => F k ^ 2)
    (A C : ℝ) (hA : ∑' k, F k ^ 2 ≤ A ^ 2) (hA0 : 0 ≤ A) (hC : 0 ≤ C)
    (hX : ∀ k, 0 ≤ X k ∧ X k ≤ C * sw k * F k) : DualBound X (C * A) := by
  intro v hv
  set g : Lattice d → ℝ := fun k => sw k * ‖v k‖ with hg
  have hg2 : ∀ k, g k ^ 2 = sobWeight 1 k * ‖v k‖ ^ 2 := by
    intro k; simp only [hg]; rw [mul_pow, sw_sq]
  have hgs : Summable fun k => g k ^ 2 := hv.congr (fun k => (hg2 k).symm)
  have hcs := Torus.cs_tsum F g hF0 (fun k => mul_nonneg (sw_nonneg k) (norm_nonneg _)) hF hgs
  have hle : ∀ k, X k * ‖v k‖ ≤ C * (F k * g k) := by
    intro k
    have := mul_le_mul_of_nonneg_right (hX k).2 (norm_nonneg (v k))
    calc X k * ‖v k‖ ≤ C * sw k * F k * ‖v k‖ := this
      _ = C * (F k * g k) := by simp only [hg]; ring
  have hs : Summable fun k => X k * ‖v k‖ :=
    Summable.of_nonneg_of_le (fun k => mul_nonneg (hX k).1 (norm_nonneg _)) hle
      (hcs.1.mul_left C)
  refine ⟨hs, ?_⟩
  have h1 : ∑' k, X k * ‖v k‖ ≤ ∑' k, C * (F k * g k) :=
    hs.tsum_le_tsum hle (hcs.1.mul_left C)
  rw [tsum_mul_left] at h1
  have h2 : ∑' k, g k ^ 2 = hsNormSq 1 v := tsum_congr hg2
  have h3 : Real.sqrt (∑' k, F k ^ 2) ≤ A := by
    calc _ ≤ Real.sqrt (A ^ 2) := Real.sqrt_le_sqrt hA
      _ = A := Real.sqrt_sq hA0
  calc ∑' k, X k * ‖v k‖ ≤ C * ∑' k, F k * g k := h1
    _ ≤ C * (Real.sqrt (∑' k, F k ^ 2) * Real.sqrt (∑' k, g k ^ 2)) :=
        mul_le_mul_of_nonneg_left hcs.2 hC
    _ ≤ C * (A * hsNorm 1 v) := by
        rw [h2]
        gcongr
        exact le_rfl
    _ = C * A * hsNorm 1 v := by ring


/-! ### The operator bound `H^1 → H^{-1}` -/

theorem MultBound.memHs0 {a : Coeff d} {K : ℝ} (h : MultBound a K) : MemHs 0 a := by
  have h0 : MemHs 0 (deltaCoeff (0 : Lattice d)) := by
    rw [memHs_zero_iff]
    refine summable_of_ne_finset_zero (s := {0}) fun k hk => ?_
    have : k ≠ 0 := by simpa using hk
    simp [deltaCoeff, this]
  have := (h _ h0).1
  have e : mulCoeff a (deltaCoeff (0 : Lattice d)) = a := by
    funext k
    unfold mulCoeff
    rw [tsum_eq_single 0]
    · simp [deltaCoeff]
    · intro j hj; simp [deltaCoeff, hj]
  rwa [e] at this

theorem mulCoeff_add_of_memHs0 {a c₁ c₂ : Coeff d} (ha : MemHs 0 a) (h₁ : MemHs 0 c₁)
    (h₂ : MemHs 0 c₂) : mulCoeff a (c₁ + c₂) = mulCoeff a c₁ + mulCoeff a c₂ := by
  funext k
  unfold mulCoeff
  simp only [Pi.add_apply, mul_add]
  exact (summable_mulCoeff a c₁ ha h₁ k).tsum_add (summable_mulCoeff a c₂ ha h₂ k)

theorem one_le_enorm_of_ne_zeroU {k : Lattice d} (hk : k ≠ 0) : 1 ≤ Lattice.enorm k := by
  obtain ⟨i, hi⟩ : ∃ i, k i ≠ 0 := by
    by_contra h
    push Not at h
    exact hk (funext h)
  have h1 : (1 : ℝ) ≤ ((k i : ℤ) : ℝ) ^ 2 := by
    have : (1 : ℤ) ≤ (k i) ^ 2 := by nlinarith [sq_pos_of_ne_zero hi]
    exact_mod_cast this
  have h2 := enorm_sq_ge_sq k i
  have h3 : 0 ≤ Lattice.enorm k := norm_nonneg _
  nlinarith

theorem abs_rieszCoeff_leU {s : ℝ} (hsd : s < d) (k : Lattice d) :
    |rieszCoeff d s k| ≤ |rieszConst d s| := by
  unfold rieszCoeff
  split_ifs with hk
  · simp
  · rw [abs_mul]
    have hpos : 0 < 2 * Real.pi * Lattice.enorm k := by
      have := one_le_enorm_of_ne_zeroU hk
      positivity
    rw [abs_of_pos (Real.rpow_pos_of_pos hpos _)]
    have h1 : 1 ≤ 2 * Real.pi * Lattice.enorm k := by
      have := one_le_enorm_of_ne_zeroU hk
      nlinarith [Real.pi_gt_three]
    have h2 : (2 * Real.pi * Lattice.enorm k) ^ (s - (d : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos h1 (by linarith)
    calc |rieszConst d s| * (2 * Real.pi * Lattice.enorm k) ^ (s - (d : ℝ))
        ≤ |rieszConst d s| * 1 := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
      _ = _ := mul_one _

theorem norm_gradRieszCoeff_le {s : ℝ} (hsd : s < d) (i : Fin d) (c : Coeff d) (k : Lattice d) :
    ‖gradRieszCoeff d s i c k‖ ≤ |rieszConst d s| * sw k * ‖c k‖ := by
  unfold gradRieszCoeff
  refine (norm_derivCoeff_le i (rieszMult d s c) k).trans ?_
  unfold rieszMult
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have := abs_rieszCoeff_leU hsd k
  calc sw k * (|rieszCoeff d s k| * ‖c k‖) ≤ sw k * (|rieszConst d s| * ‖c k‖) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right this (norm_nonneg _)) (sw_nonneg k)
    _ = _ := by ring

/-- Constant of the operator bound. -/
def opConst (D : DynData d) (K : ℝ) : ℝ :=
  D.invβ + d * K + (∑ i : Fin d, ∑ j : Fin d, |D.M j i|) * |rieszConst d D.s| * K

theorem hsNormSq_one_eq_sq (u : Coeff d) :
    hsNormSq 1 u = hsNorm 1 u ^ 2 := by
  unfold hsNorm
  exact (Real.sq_sqrt (by unfold hsNormSq; exact tsum_nonneg fun k => mul_nonneg (sobWeight_nonneg 1 k) (sq_nonneg _))).symm

theorem hsNormSq_zero_eq (c : Coeff d) : hsNormSq 0 c = ∑' k, ‖c k‖ ^ 2 := by
  unfold hsNormSq; exact tsum_congr fun k => by rw [sobWeight_zero, one_mul]

theorem dual_mult (a : Coeff d) (K : ℝ) (hK0 : 0 ≤ K) (ha : MultBound a K) (j : Fin d)
    (u : Coeff d) (hu : MemHs 1 u) (symC : ℝ) (hsymC : 0 ≤ symC) (X : Lattice d → ℝ)
    (hX : ∀ k, 0 ≤ X k ∧ X k ≤ symC * sw k * ‖mulCoeff a (derivCoeff j u) k‖) :
    DualBound X (symC * (K * hsNorm 1 u)) := by
  obtain ⟨hd0, hd1⟩ := memHs_zero_deriv hu j
  obtain ⟨hm0, hm1⟩ := ha _ hd0
  have hNN : hsNormSq 1 u = hsNorm 1 u ^ 2 := hsNormSq_one_eq_sq u
  refine dual_of_l2 (fun k => ‖mulCoeff a (derivCoeff j u) k‖) X (fun k => norm_nonneg _)
    ((memHs_zero_iff _).1 hm0) (K * hsNorm 1 u) symC ?_ (mul_nonneg hK0 (Real.sqrt_nonneg _))
    hsymC hX
  rw [← hsNormSq_zero_eq]
  calc hsNormSq 0 (mulCoeff a (derivCoeff j u)) ≤ K ^ 2 * hsNormSq 0 (derivCoeff j u) := hm1
    _ ≤ K ^ 2 * hsNormSq 1 u := by gcongr
    _ = (K * hsNorm 1 u) ^ 2 := by rw [hNN]; ring

/-- **Operator bound**: `𝓛 : H^1 → H^{-1}` is bounded, in the dual form. -/
theorem forwardGen_dual (D : DynData d) (ρ : Torus d → ℝ) (K : ℝ) (hK0 : 0 ≤ K)
    (hρ : MultBound (coeffOf ρ) K) (hb : ∀ j, MultBound (driftCoeff D ρ j) K)
    (u : Coeff d) (hu : MemHs 1 u) :
    DualBound (fun k => ‖forwardGen D ρ u k‖) (opConst D K * hsNorm 1 u) := by
  have hN0 : 0 ≤ hsNorm 1 u := Real.sqrt_nonneg _
  have hNN : hsNormSq 1 u = hsNorm 1 u ^ 2 := hsNormSq_one_eq_sq u
  -- Laplacian
  have DL : DualBound (fun k => D.invβ * (4 * Real.pi ^ 2 * Lattice.enorm k ^ 2 * ‖u k‖))
      (D.invβ * hsNorm 1 u) := by
    have h := dual_of_l2 (fun k => sw k * ‖u k‖)
      (fun k => 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2 * ‖u k‖)
      (fun k => mul_nonneg (sw_nonneg k) (norm_nonneg _))
      (hu.congr fun k => by rw [mul_pow, sw_sq]) (hsNorm 1 u) 1 (by
        have : ∑' k, (sw k * ‖u k‖) ^ 2 = hsNormSq 1 u := by
          unfold hsNormSq; exact tsum_congr fun k => by rw [mul_pow, sw_sq]
        rw [this, hNN]) hN0 zero_le_one (fun k => by
        refine ⟨by positivity, ?_⟩
        have h1 := sw_sq k
        rw [sobWeight_oneU] at h1
        have h2 := one_le_sw k
        nlinarith [norm_nonneg (u k), mul_nonneg (sw_nonneg k) (norm_nonneg (u k)),
          sq_nonneg (Lattice.enorm k), sq_nonneg Real.pi])
    have := h.const_mul D.hβ
    simpa using this
  -- transport
  have DT : ∀ j : Fin d, DualBound (fun k => ‖mulCoeff (driftCoeff D ρ j) (derivCoeff j u) k‖)
      (1 * (K * hsNorm 1 u)) := fun j =>
    dual_mult _ K hK0 (hb j) j u hu 1 zero_le_one _ (fun k => ⟨norm_nonneg _, by
      have := one_le_sw k
      nlinarith [norm_nonneg (mulCoeff (driftCoeff D ρ j) (derivCoeff j u) k)]⟩)
  -- nonlocal
  have DN : ∀ i j : Fin d, DualBound (fun k => |D.M j i| *
      ‖gradRieszCoeff d D.s i (mulCoeff (coeffOf ρ) (derivCoeff j u)) k‖)
      ((|D.M j i| * |rieszConst d D.s|) * (K * hsNorm 1 u)) := fun i j =>
    dual_mult _ K hK0 hρ j u hu _ (mul_nonneg (abs_nonneg _) (abs_nonneg _)) _ (fun k => ⟨by positivity, by
      have := norm_gradRieszCoeff_le D.hsd i (mulCoeff (coeffOf ρ) (derivCoeff j u)) k
      calc |D.M j i| * ‖gradRieszCoeff d D.s i (mulCoeff (coeffOf ρ) (derivCoeff j u)) k‖
          ≤ |D.M j i| * (|rieszConst d D.s| * sw k *
            ‖mulCoeff (coeffOf ρ) (derivCoeff j u) k‖) :=
            mul_le_mul_of_nonneg_left this (abs_nonneg _)
        _ = _ := by ring⟩)
  have DTs := DualBound.sum (Finset.univ : Finset (Fin d)) (fun j _ => DT j)
  have DNs := DualBound.sum (Finset.univ : Finset (Fin d)) (fun i _ =>
    DualBound.sum (Finset.univ : Finset (Fin d)) (fun j _ => DN i j))
  have Dtot := (DL.add DTs).add DNs
  have hconst : D.invβ * hsNorm 1 u + ∑ j : Fin d, 1 * (K * hsNorm 1 u) +
      ∑ i : Fin d, ∑ j : Fin d, (|D.M j i| * |rieszConst d D.s|) * (K * hsNorm 1 u) =
      opConst D K * hsNorm 1 u := by
    unfold opConst
    have e2 : ∑ i : Fin d, ∑ j : Fin d, |D.M j i| * |rieszConst d D.s| * (K * hsNorm 1 u) =
        (∑ i, ∑ j, |D.M j i|) * |rieszConst d D.s| * K * hsNorm 1 u := by
      simp only [Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    rw [e2]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, one_mul]
    ring
  rw [hconst] at Dtot
  refine Dtot.mono fun k => ⟨norm_nonneg _, ?_⟩
  -- pointwise bound
  have hlap : ‖laplaceCoeff u k‖ = 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2 * ‖u k‖ := by
    unfold laplaceCoeff
    rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  unfold forwardGen
  calc ‖(D.invβ : ℂ) * laplaceCoeff u k + transportCoeff D ρ u k - nonlocalCoeff D ρ u k‖
      ≤ ‖(D.invβ : ℂ) * laplaceCoeff u k‖ + ‖transportCoeff D ρ u k‖ + ‖nonlocalCoeff D ρ u k‖ :=
        (norm_sub_le _ _).trans (by gcongr; exact norm_add_le _ _)
    _ ≤ _ := by
        gcongr
        · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg D.hβ, hlap]
        · exact (norm_sum_le _ _).trans (le_of_eq rfl)
        · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]




theorem sq_primitive (h : ℝ → ℝ) (τ : ℝ) (hh : IntervalIntegrable h volume 0 τ) :
    (∫ s in (0:ℝ)..τ, h s) ^ 2 = ∫ σ in (0:ℝ)..τ, 2 * (∫ s in (0:ℝ)..σ, h s) * h σ := by
  set f : ℝ → ℝ := fun x => ∫ s in (0:ℝ)..x, h s with hf
  have hac : AbsolutelyContinuousOnInterval f 0 τ :=
    hh.absolutelyContinuousOnInterval_intervalIntegral (c := 0) Set.left_mem_uIcc
  have h1 := hac.integral_deriv_mul_eq_sub hac
  have h0 : f 0 = 0 := by simp [hf]
  rw [h0] at h1
  have h2 : ∫ x in (0:ℝ)..τ, (deriv f x * f x + f x * deriv f x) =
      ∫ σ in (0:ℝ)..τ, 2 * f σ * h σ := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hh.ae_hasDerivAt_integral] with x hx hxI
    have hxI' : x ∈ Set.uIcc 0 τ := Set.uIoc_subset_uIcc hxI
    have := (hx hxI' 0 Set.left_mem_uIcc).deriv
    simp only [hf] at this ⊢
    rw [this]; ring
  rw [h2] at h1
  simpa [hf, sq] using h1.symm

theorem norm_sq_primitive (g : ℝ → ℂ) (τ : ℝ) (hg : IntervalIntegrable g volume 0 τ) :
    ‖∫ s in (0:ℝ)..τ, g s‖ ^ 2 = ∫ σ in (0:ℝ)..τ, 2 * (g σ * conj (∫ s in (0:ℝ)..σ, g s)).re := by
  have hre : IntervalIntegrable (fun s => (g s).re) volume 0 τ :=
    intervalIntegrable_iff.2 (Complex.reCLM.integrable_comp (intervalIntegrable_iff.1 hg))
  have him : IntervalIntegrable (fun s => (g s).im) volume 0 τ :=
    intervalIntegrable_iff.2 (Complex.imCLM.integrable_comp (intervalIntegrable_iff.1 hg))
  have e1 := sq_primitive _ τ hre
  have e2 := sq_primitive _ τ him
  have hpre : ∀ σ ∈ Set.uIcc 0 τ, ∫ s in (0:ℝ)..σ, (g s).re = (∫ s in (0:ℝ)..σ, g s).re := by
    intro σ hσ
    have hgσ : IntervalIntegrable g volume 0 σ :=
      hg.mono_set (Set.uIcc_subset_uIcc Set.left_mem_uIcc hσ)
    exact Complex.reCLM.intervalIntegral_comp_comm hgσ
  have hpim : ∀ σ ∈ Set.uIcc 0 τ, ∫ s in (0:ℝ)..σ, (g s).im = (∫ s in (0:ℝ)..σ, g s).im := by
    intro σ hσ
    have hgσ : IntervalIntegrable g volume 0 σ :=
      hg.mono_set (Set.uIcc_subset_uIcc Set.left_mem_uIcc hσ)
    exact Complex.imCLM.intervalIntegral_comp_comm hgσ
  have hcre := intervalIntegral.continuousOn_primitive_interval' hre (a := 0) Set.left_mem_uIcc
  have hcim := intervalIntegral.continuousOn_primitive_interval' him (a := 0) Set.left_mem_uIcc
  have i1 : IntervalIntegrable (fun σ => 2 * (∫ s in (0:ℝ)..σ, (g s).re) * (g σ).re) volume 0 τ := by
    have := hre.continuousOn_mul (hcre.const_smul (2:ℝ))
    simpa [mul_assoc] using this
  have i2 : IntervalIntegrable (fun σ => 2 * (∫ s in (0:ℝ)..σ, (g s).im) * (g σ).im) volume 0 τ := by
    have := him.continuousOn_mul (hcim.const_smul (2:ℝ))
    simpa [mul_assoc] using this
  have hF : ‖∫ s in (0:ℝ)..τ, g s‖ ^ 2 = (∫ s in (0:ℝ)..τ, (g s).re) ^ 2 +
      (∫ s in (0:ℝ)..τ, (g s).im) ^ 2 := by
    rw [hpre τ Set.right_mem_uIcc, hpim τ Set.right_mem_uIcc, Complex.sq_norm, Complex.normSq_apply]
    ring
  rw [hF, e1, e2, ← intervalIntegral.integral_add i1 i2]
  refine intervalIntegral.integral_congr fun σ hσ => ?_
  rw [hpre σ hσ, hpim σ hσ]
  simp [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring




theorem gronwall_integral (φ : ℝ → ℝ) (t B a : ℝ) (ha : 0 ≤ a)
    (hφ0 : ∀ τ ∈ Set.Icc 0 t, 0 ≤ φ τ) (hφB : ∀ τ ∈ Set.Icc 0 t, φ τ ≤ B)
    (hmeas : AEStronglyMeasurable φ (volume.restrict (Set.Icc 0 t)))
    (hle : ∀ τ ∈ Set.Icc 0 t, φ τ ≤ a * ∫ σ in (0:ℝ)..τ, φ σ) :
    ∀ τ ∈ Set.Icc 0 t, φ τ = 0 := by
  have hint : ∀ τ ∈ Set.Icc 0 t, IntervalIntegrable φ volume 0 τ := by
    intro τ hτ
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hτ.1]
    have hsub : Set.Icc 0 τ ⊆ Set.Icc 0 t := Set.Icc_subset_Icc_right hτ.2
    refine Integrable.of_bound (hmeas.mono_set hsub) |B| ?_
    refine (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun x hx => ?_)
    have hx' : x ∈ Set.Icc 0 t := hsub hx
    rw [Real.norm_eq_abs, abs_of_nonneg (hφ0 x hx')]
    exact (hφB x hx').trans (le_abs_self B)
  have key : ∀ n : ℕ, ∀ τ ∈ Set.Icc 0 t, φ τ ≤ B * (a * τ) ^ n / (n.factorial : ℝ) := by
    intro n
    induction n with
    | zero => intro τ hτ; simpa using hφB τ hτ
    | succ n ih =>
      intro τ hτ
      refine (hle τ hτ).trans ?_
      have hI := hint τ hτ
      have h1 : ∫ σ in (0:ℝ)..τ, φ σ ≤ ∫ σ in (0:ℝ)..τ, B * (a * σ) ^ n / (n.factorial : ℝ) := by
        refine intervalIntegral.integral_mono_on hτ.1 hI ?_ fun σ hσ => ih σ ⟨hσ.1, hσ.2.trans hτ.2⟩
        exact (continuous_const.mul ((continuous_const.mul continuous_id).pow n)
          |>.div_const _).intervalIntegrable _ _
      have h2 : ∫ σ in (0:ℝ)..τ, B * (a * σ) ^ n / (n.factorial : ℝ) =
          B * a ^ n * (τ ^ (n + 1) / (n + 1)) / (n.factorial : ℝ) := by
        have : ∀ σ : ℝ, B * (a * σ) ^ n / (n.factorial : ℝ) = (B * a ^ n / (n.factorial : ℝ)) * σ ^ n := by
          intro σ; rw [mul_pow]; ring
        simp_rw [this]
        rw [intervalIntegral.integral_const_mul, integral_pow]
        simp
        ring
      calc a * ∫ σ in (0:ℝ)..τ, φ σ ≤ a * (B * a ^ n * (τ ^ (n + 1) / (n + 1)) / (n.factorial : ℝ)) :=
            mul_le_mul_of_nonneg_left (h1.trans_eq h2) ha
        _ = B * (a * τ) ^ (n + 1) / ((n + 1).factorial : ℝ) := by
            rw [Nat.factorial_succ]
            push_cast
            field_simp
            ring
  intro τ hτ
  have hlim : Tendsto (fun n : ℕ => B * ((a * τ) ^ n / (n.factorial : ℝ))) atTop (𝓝 (B * 0)) :=
    (FloorSemiring.tendsto_pow_div_factorial_atTop (a * τ)).const_mul B
  rw [mul_zero] at hlim
  have : φ τ ≤ 0 := by
    refine le_of_tendsto_of_tendsto' tendsto_const_nhds hlim fun n => ?_
    have := key n τ hτ
    rwa [mul_div_assoc] at this
  exact le_antisymm this (hφ0 τ hτ)




theorem memHs_truncCoeff (n : ℕ) {m : ℝ} {c : Coeff d} (hc : MemHs m c) :
    MemHs m (truncCoeff n c) := by
  refine Summable.of_nonneg_of_le (fun k => mul_nonneg (sobWeight_nonneg m k) (sq_nonneg _))
    (fun k => ?_) hc
  by_cases hk : InBox n k <;> simp [truncCoeff, hk, mul_nonneg (sobWeight_nonneg m k) (sq_nonneg _)]

theorem memHs_sub_truncCoeff (n : ℕ) {m : ℝ} {c : Coeff d} (hc : MemHs m c) :
    MemHs m (c - truncCoeff n c) := by
  refine Summable.of_nonneg_of_le (fun k => mul_nonneg (sobWeight_nonneg m k) (sq_nonneg _))
    (fun k => ?_) hc
  by_cases hk : InBox n k <;> simp [truncCoeff, hk, mul_nonneg (sobWeight_nonneg m k) (sq_nonneg _)]

theorem energy_step {L : Coeff d → Coeff d} {K Λ₀ : ℝ} (hK0 : 0 ≤ K)
    (hadd : ∀ u v, MemHs 1 u → MemHs 1 v → L (u + v) = L u + L v)
    (hdual : ∀ u, MemHs 1 u → DualBound (fun k => ‖L u k‖) (K * hsNorm 1 u))
    (hen : ∀ n w, IsTrigPoly n w → (hsInner 0 (L w) w).re ≤ Λ₀ * hsNormSq 0 w)
    (z : Coeff d) (hz : MemHs 1 z) (n : ℕ) :
    2 * (hsInner 0 (L z) (truncCoeff n z)).re ≤
      2 * Λ₀ * (∑ k ∈ boxFinset d n, ‖z k‖ ^ 2) + 2 * K * hsNorm 1 (z - truncCoeff n z) * hsNorm 1 z := by
  set P := truncCoeff n z with hP
  set R := z - P with hR
  have hPm : MemHs 1 P := memHs_truncCoeff n hz
  have hRm : MemHs 1 R := memHs_sub_truncCoeff n hz
  have hzPR : z = P + R := by simp [hR]
  have hPtrig : IsTrigPoly n P := isTrigPoly_truncCoeff n z
  have hLz : L z = L P + L R := by
    conv_lhs => rw [hzPR]
    exact hadd P R hPm hRm
  have hPk : ∀ k ∈ boxFinset d n, P k = z k := fun k hk => by
    simp [hP, truncCoeff, mem_boxFinset.1 hk]
  -- inner product as a finite sum
  have h1 : hsInner 0 (L z) P = hsInner 0 (L P) P +
      ∑ k ∈ boxFinset d n, L R k * conj (P k) := by
    rw [hsInner_trig hPtrig 0, hsInner_trig hPtrig 0, hLz]
    simp only [sobWeight_zero, Complex.ofReal_one, one_mul, Pi.add_apply, add_mul,
      Finset.sum_add_distrib]
  have h2 : (hsInner 0 (L P) P).re ≤ Λ₀ * (∑ k ∈ boxFinset d n, ‖z k‖ ^ 2) := by
    refine (hen n P hPtrig).trans ?_
    rw [hsNormSq_trig hPtrig 0]
    refine le_of_eq (congrArg (Λ₀ * ·) (Finset.sum_congr rfl fun k hk => ?_))
    rw [sobWeight_zero, one_mul, hPk k hk]
  have h3 : ‖∑ k ∈ boxFinset d n, L R k * conj (P k)‖ ≤ K * hsNorm 1 R * hsNorm 1 P := by
    obtain ⟨hs, hle⟩ := hdual R hRm P hPm
    refine (norm_sum_le _ _).trans ?_
    calc ∑ k ∈ boxFinset d n, ‖L R k * conj (P k)‖
        = ∑ k ∈ boxFinset d n, ‖L R k‖ * ‖P k‖ := by simp
      _ ≤ ∑' k, ‖L R k‖ * ‖P k‖ := Summable.sum_le_tsum _ (fun k _ => by positivity) hs
      _ ≤ _ := hle
  have h4 : hsNorm 1 P ≤ hsNorm 1 z := by
    unfold hsNorm
    exact Real.sqrt_le_sqrt (hsNormSq_truncCoeff_le n hz)
  have h5 : (∑ k ∈ boxFinset d n, L R k * conj (P k)).re ≤ K * hsNorm 1 R * hsNorm 1 z := by
    refine (Complex.re_le_norm _).trans (h3.trans ?_)
    exact mul_le_mul_of_nonneg_left h4 (mul_nonneg hK0 (Real.sqrt_nonneg _))
  rw [h1, Complex.add_re]
  nlinarith [h2, h5]



theorem pairing_real {n : ℕ} {a b : Coeff d} (ha : IsRealCoeff a) (hb : IsRealCoeff b) :
    (∑ k ∈ boxFinset d n, a k * conj (b k)).im = 0 := by
  set T := ∑ k ∈ boxFinset d n, a k * conj (b k) with hT
  have h : conj T = T := by
    rw [hT, map_sum]
    refine Finset.sum_nbij' (fun k => -k) (fun k => -k) ?_ ?_ ?_ ?_ ?_
    · intro k hk; rw [mem_boxFinset] at hk ⊢; exact hk.neg
    · intro k hk; rw [mem_boxFinset] at hk ⊢; exact hk.neg
    · intro k _; simp
    · intro k _; simp
    · intro k _
      simp only [map_mul, Complex.conj_conj]
      rw [← ha k, show b k = conj (b (-k)) by have := hb (-k); rwa [neg_neg] at this]

  exact Complex.conj_eq_iff_im.1 h

theorem complex_form {n : ℕ} {L : Coeff d → Coeff d} {Λ₀ : ℝ}
    (hadd : ∀ a b, IsTrigPoly n a → IsTrigPoly n b → L (a + b) = L a + L b)
    (hsmul : ∀ (c : ℂ) a, L (c • a) = c • L a)
    (hrefl : ∀ a, L (reflConj a) = reflConj (L a))
    (hreal : ∀ G, IsRealCoeff G → IsTrigPoly n G → (hsInner 0 (L G) G).re ≤ Λ₀ * hsNormSq 0 G)
    (w : Coeff d) (hw : IsTrigPoly n w) : (hsInner 0 (L w) w).re ≤ Λ₀ * hsNormSq 0 w := by
  set u : Coeff d := fun k => (w k + conj (w (-k))) / 2 with hu
  set v : Coeff d := fun k => (w k - conj (w (-k))) / (2 * Complex.I) with hv
  have hur : IsRealCoeff u := by
    intro k; simp only [hu, map_div₀, map_add, Complex.conj_conj, neg_neg, map_ofNat]; simp [add_comm]
  have hvr : IsRealCoeff v := by
    intro k
    simp only [hv, map_div₀, map_sub, Complex.conj_conj, neg_neg, map_mul, Complex.conj_I,
      map_ofNat]
    field_simp
    ring
  have hut : IsTrigPoly n u := by
    intro k hk
    by_contra hb
    apply hk
    have h1 : w k = 0 := hw.eq_zero hb
    have h2 : w (-k) = 0 := hw.eq_zero (fun h => hb (inBox_neg_iff.1 h))
    simp [hu, h1, h2]
  have hvt : IsTrigPoly n v := by
    intro k hk
    by_contra hb
    apply hk
    have h1 : w k = 0 := hw.eq_zero hb
    have h2 : w (-k) = 0 := hw.eq_zero (fun h => hb (inBox_neg_iff.1 h))
    simp [hv, h1, h2]
  have hwuv : w = u + Complex.I • v := by
    funext k
    simp only [hu, hv, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    ring
  have hIv : IsTrigPoly n (Complex.I • v) := hvt.smul _
  have hLw : L w = L u + Complex.I • L v := by
    conv_lhs => rw [hwuv]
    rw [hadd u _ hut hIv, hsmul]
  have hLur : IsRealCoeff (L u) := by
    rw [isRealCoeff_iff_reflConj, ← hrefl, (isRealCoeff_iff_reflConj u).1 hur]
  have hLvr : IsRealCoeff (L v) := by
    rw [isRealCoeff_iff_reflConj, ← hrefl, (isRealCoeff_iff_reflConj v).1 hvr]
  -- finite sums
  have hQ : ∀ a b : Coeff d, IsTrigPoly n b → hsInner 0 a b = ∑ k ∈ boxFinset d n, a k * conj (b k) := by
    intro a b hb
    rw [hsInner_trig hb 0]
    simp [sobWeight_zero]
  have hN : ∀ a : Coeff d, IsTrigPoly n a → hsNormSq 0 a = ∑ k ∈ boxFinset d n, ‖a k‖ ^ 2 := by
    intro a ha
    rw [hsNormSq_trig ha 0]
    simp [sobWeight_zero]
  have hwt := hw
  have hwk : ∀ k, w k = u k + Complex.I * v k := fun k => by
    have := congrFun hwuv k
    simpa using this
  have e1 : ∑ k ∈ boxFinset d n, L w k * conj (w k) =
      (∑ k ∈ boxFinset d n, L u k * conj (u k)) + (∑ k ∈ boxFinset d n, L v k * conj (v k)) +
        Complex.I * ((∑ k ∈ boxFinset d n, L v k * conj (u k)) -
          (∑ k ∈ boxFinset d n, L u k * conj (v k))) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hLw, hwk k]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul, Complex.conj_I]
    have hI := Complex.I_sq
    linear_combination (L v k * conj (v k)) * (-hI) + 0 * hI
  have e2 : ∑ k ∈ boxFinset d n, ‖w k‖ ^ 2 =
      (∑ k ∈ boxFinset d n, ‖u k‖ ^ 2) + (∑ k ∈ boxFinset d n, ‖v k‖ ^ 2) +
        2 * (∑ k ∈ boxFinset d n, u k * conj (v k)).im := by
    rw [Complex.im_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hwk k]
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.conj_re,
      Complex.conj_im]
    ring
  have hp1 : (∑ k ∈ boxFinset d n, L v k * conj (u k)).im = 0 := pairing_real hLvr hur
  have hp2 : (∑ k ∈ boxFinset d n, L u k * conj (v k)).im = 0 := pairing_real hLur hvr
  have hp3 : (∑ k ∈ boxFinset d n, u k * conj (v k)).im = 0 := pairing_real hur hvr
  have hre : (hsInner 0 (L w) w).re = (hsInner 0 (L u) u).re + (hsInner 0 (L v) v).re := by
    rw [hQ _ _ hw, hQ _ _ hut, hQ _ _ hvt, e1]
    simp [Complex.add_re, Complex.sub_im, hp1, hp2]
  have hnorm : hsNormSq 0 w = hsNormSq 0 u + hsNormSq 0 v := by
    rw [hN w hw, hN u hut, hN v hvt, e2, hp3]; ring
  rw [hre, hnorm]
  have := hreal u hur hut
  have := hreal v hvr hvt
  nlinarith



theorem forwardGen_add_H1 (D : DynData d) (ρ : Torus d → ℝ) (hρ : MemHs 0 (coeffOf ρ))
    (hb : ∀ j, MemHs 0 (driftCoeff D ρ j)) {u v : Coeff d} (hu : MemHs 1 u) (hv : MemHs 1 v) :
    forwardGen D ρ (u + v) = forwardGen D ρ u + forwardGen D ρ v := by
  funext k
  have e : ∀ j, derivCoeff j (u + v) = derivCoeff j u + derivCoeff j v := by
    intro j; funext k; simp [PDE.derivCoeff, mul_add]
  have k1 : ∀ j, mulCoeff (driftCoeff D ρ j) (derivCoeff j u + derivCoeff j v) =
      mulCoeff (driftCoeff D ρ j) (derivCoeff j u) + mulCoeff (driftCoeff D ρ j) (derivCoeff j v) :=
    fun j => mulCoeff_add_of_memHs0 (hb j) (memHs_zero_deriv hu j).1 (memHs_zero_deriv hv j).1
  have k2 : ∀ j, mulCoeff (coeffOf ρ) (derivCoeff j u + derivCoeff j v) =
      mulCoeff (coeffOf ρ) (derivCoeff j u) + mulCoeff (coeffOf ρ) (derivCoeff j v) :=
    fun j => mulCoeff_add_of_memHs0 hρ (memHs_zero_deriv hu j).1 (memHs_zero_deriv hv j).1
  simp only [forwardGen, transportCoeff, nonlocalCoeff, e, k1, k2, Pi.add_apply]
  simp only [laplaceCoeff, gradRieszCoeff, rieszMult, PDE.derivCoeff, Pi.add_apply]
  simp only [mul_add, Finset.sum_add_distrib]
  ring



theorem tendsto_box_sum {f : Lattice d → ℝ} (hf : Summable f) :
    Tendsto (fun N : ℕ => ∑ k ∈ boxFinset d N, f k) atTop (𝓝 (∑' k, f k)) := by
  have h : ∀ N : ℕ, ∑ k ∈ boxFinset d N, f k = ∑' k, (if InBox N k then f k else 0) := by
    intro N
    rw [tsum_eq_sum (s := boxFinset d N)]
    · exact Finset.sum_congr rfl fun k hk => by simp [mem_boxFinset.1 hk]
    · intro k hk
      have : ¬ InBox N k := fun h => hk (mem_boxFinset.2 h)
      simp [this]
  simp_rw [h]
  refine tendsto_tsum_of_dominated_convergence (bound := fun k => ‖f k‖) hf.norm (fun k => ?_)
    (Filter.Eventually.of_forall fun N k => ?_)
  · have hev : ∀ᶠ n : ℕ in atTop, InBox n k := by
      unfold InBox
      rw [Filter.eventually_all]
      intro i
      filter_upwards [Filter.eventually_ge_atTop (k i).natAbs] with n hn
      have : ((k i).natAbs : ℤ) ≤ n := by exact_mod_cast hn
      rwa [Int.natCast_natAbs] at this
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hev] with n hn
    simp [hn]
  · by_cases hk : InBox N k <;> simp [hk]

theorem aesm_tsum_box {a : ℝ → Lattice d → ℝ} {S : Set ℝ} (hS : MeasurableSet S)
    (ha : ∀ k, ContinuousOn (fun σ => a σ k) S) (hsum : ∀ σ ∈ S, Summable (a σ)) :
    AEStronglyMeasurable (fun σ => ∑' k, a σ k) (volume.restrict S) := by
  refine aestronglyMeasurable_of_tendsto_ae (u := atTop)
    (f := fun (N : ℕ) σ => ∑ k ∈ boxFinset d N, a σ k) (fun N => ?_) ?_
  · exact (continuousOn_finsetSum _ fun k _ => ha k).aestronglyMeasurable hS
  · exact (ae_restrict_iff' hS).2 (Filter.Eventually.of_forall fun σ hσ =>
      tendsto_box_sum (hsum σ hσ))

theorem ii_of_bdd {f : ℝ → ℝ} {t M : ℝ} (hmeas : AEStronglyMeasurable f (volume.restrict (Set.Icc 0 t)))
    (hb : ∀ σ ∈ Set.Icc 0 t, ‖f σ‖ ≤ M) {τ : ℝ} (hτ : τ ∈ Set.Icc 0 t) :
    IntervalIntegrable f volume 0 τ := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hτ.1]
  have hsub : Set.Icc 0 τ ⊆ Set.Icc 0 t := Set.Icc_subset_Icc_right hτ.2
  refine Integrable.of_bound (hmeas.mono_set hsub) M ?_
  exact (ae_restrict_iff' measurableSet_Icc).2
    (Filter.Eventually.of_forall fun x hx => hb x (hsub hx))

theorem hsNormSq_sub_truncCoeff_le (n : ℕ) {m : ℝ} {c : Coeff d} (hc : MemHs m c) :
    hsNormSq m (c - truncCoeff n c) ≤ hsNormSq m c := by
  have hle : ∀ k, sobWeight m k * ‖(c - truncCoeff n c) k‖ ^ 2 ≤ sobWeight m k * ‖c k‖ ^ 2 := by
    intro k
    by_cases hk : InBox n k
    · simp [truncCoeff, hk, mul_nonneg (sobWeight_nonneg m k) (sq_nonneg _)]
    · simp [truncCoeff, hk]
  exact (memHs_sub_truncCoeff n hc).tsum_le_tsum hle hc



theorem abstract_unique (t B K Λ₀ : ℝ) (ht : 0 ≤ t) (hK0 : 0 ≤ K)
    (z g : ℝ → Coeff d) (L : ℝ → Coeff d → Coeff d)
    (hz1 : ∀ σ ∈ Set.Icc 0 t, MemHs 1 (z σ))
    (hzB : ∀ σ ∈ Set.Icc 0 t, hsNormSq 1 (z σ) ≤ B)
    (hint : ∀ k, IntegrableOn (fun σ => g σ k) (Set.Icc 0 t))
    (heq : ∀ k, ∀ τ ∈ Set.Icc 0 t, z τ k = ∫ σ in (0:ℝ)..τ, g σ k)
    (hg : ∀ σ ∈ Set.Icc 0 t, g σ = L σ (z σ))
    (hadd : ∀ σ ∈ Set.Icc 0 t, ∀ u v, MemHs 1 u → MemHs 1 v → L σ (u + v) = L σ u + L σ v)
    (hdual : ∀ σ ∈ Set.Icc 0 t, ∀ u, MemHs 1 u → DualBound (fun k => ‖L σ u k‖) (K * hsNorm 1 u))
    (hen : ∀ σ ∈ Set.Icc 0 t, ∀ n w, IsTrigPoly n w →
      (hsInner 0 (L σ w) w).re ≤ Λ₀ * hsNormSq 0 w) :
    ∀ τ ∈ Set.Icc 0 t, z τ = 0 := by
  set I : Set ℝ := Set.Icc 0 t with hI
  have hB0 : 0 ≤ B := (tsum_nonneg fun k => mul_nonneg (sobWeight_nonneg 1 k) (sq_nonneg _)).trans
    (hzB 0 ⟨le_rfl, ht⟩)
  -- continuity of the coordinates
  have hzk : ∀ k, ContinuousOn (fun σ => z σ k) I := by
    intro k
    have h := intervalIntegral.continuousOn_primitive_interval (a := 0) (b := t) (μ := volume)
      (f := fun σ => g σ k) (by rw [Set.uIcc_of_le ht]; exact hint k)
    rw [Set.uIcc_of_le ht] at h
    exact h.congr fun τ hτ => heq k τ hτ
  have hgint : ∀ k, ∀ τ ∈ I, IntervalIntegrable (fun σ => g σ k) volume 0 τ := by
    intro k τ hτ
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hτ.1]
    exact (hint k).mono_set (Set.Icc_subset_Icc_right hτ.2)
  -- per-mode identity
  have hmode : ∀ k, ∀ τ ∈ I, ‖z τ k‖ ^ 2 = ∫ σ in (0:ℝ)..τ, 2 * (g σ k * conj (z σ k)).re := by
    intro k τ hτ
    rw [heq k τ hτ, norm_sq_primitive (fun σ => g σ k) τ (hgint k τ hτ)]
    refine intervalIntegral.integral_congr fun σ hσ => ?_
    have hσI : σ ∈ I := Set.uIcc_subset_Icc (show (0:ℝ) ∈ I from ⟨le_rfl, ht⟩) hτ hσ
    rw [← heq k σ hσI]
  -- the integrands
  have hY1 : ∀ k, ∀ τ ∈ I, IntervalIntegrable
      (fun σ => 2 * (g σ k * conj (z σ k)).re) volume 0 τ := by
    intro k τ hτ
    have hsub : Set.uIcc 0 τ ⊆ I := Set.uIcc_subset_Icc (show (0:ℝ) ∈ I from ⟨le_rfl, ht⟩) hτ
    have hc : ContinuousOn (fun σ => conj (z σ k)) (Set.uIcc 0 τ) :=
      (Complex.continuous_conj.comp_continuousOn (hzk k)).mono hsub
    have h1 := (hgint k τ hτ).mul_continuousOn hc
    have h2 : IntervalIntegrable (fun σ => (g σ k * conj (z σ k)).re) volume 0 τ :=
      intervalIntegrable_iff.2 (Complex.reCLM.integrable_comp (intervalIntegrable_iff.1 h1))
    exact h2.const_mul 2
  set Y : ℕ → ℝ → ℝ := fun n σ => ∑ k ∈ boxFinset d n, 2 * (g σ k * conj (z σ k)).re with hY
  set S : ℕ → ℝ → ℝ := fun n σ => ∑ k ∈ boxFinset d n, ‖z σ k‖ ^ 2 with hS
  have hSY : ∀ n, ∀ τ ∈ I, S n τ = ∫ σ in (0:ℝ)..τ, Y n σ := by
    intro n τ hτ
    simp only [hS, hY]
    rw [intervalIntegral.integral_finsetSum fun k _ => hY1 k τ hτ]
    exact Finset.sum_congr rfl fun k _ => hmode k τ hτ
  have hYint : ∀ n, ∀ τ ∈ I, IntervalIntegrable (Y n) volume 0 τ := by
    intro n τ hτ
    simp only [hY]
    have := IntervalIntegrable.sum (boxFinset d n) fun k _ => hY1 k τ hτ
    convert this using 1
    funext σ
    simp [Finset.sum_apply]
  -- the error term
  set e : ℕ → ℝ → ℝ := fun n σ =>
    2 * K * hsNorm 1 (z σ - truncCoeff n (z σ)) * hsNorm 1 (z σ) with he
  have hYle : ∀ n, ∀ σ ∈ I, Y n σ ≤ 2 * Λ₀ * S n σ + e n σ := by
    intro n σ hσ
    have hstep := energy_step (L := L σ) (K := K) (Λ₀ := Λ₀) hK0 (hadd σ hσ) (hdual σ hσ)
      (hen σ hσ) (z σ) (hz1 σ hσ) n
    have hYeq : Y n σ = 2 * (hsInner 0 (L σ (z σ)) (truncCoeff n (z σ))).re := by
      rw [hsInner_trig (isTrigPoly_truncCoeff n (z σ)) 0, Complex.re_sum, Finset.mul_sum, ← hg σ hσ]
      refine Finset.sum_congr rfl fun k hk => ?_
      simp [sobWeight_zero, truncCoeff, mem_boxFinset.1 hk]
    rw [hYeq]
    exact hstep
  -- measurability and bounds
  have hSc : ∀ n, ContinuousOn (S n) I := fun n =>
    continuousOn_finsetSum _ fun k _ => ((hzk k).norm).pow 2
  set φ : ℝ → ℝ := fun σ => hsNormSq 0 (z σ) with hφ
  have hsum0 : ∀ σ ∈ I, Summable fun k => ‖z σ k‖ ^ 2 := fun σ hσ =>
    (memHs_zero_iff _).1 (memHs_zero_of_memHs_one (hz1 σ hσ)).1
  have hφ_eq : ∀ σ, φ σ = ∑' k, ‖z σ k‖ ^ 2 := fun σ => hsNormSq_zero_eq _
  have hφ0 : ∀ σ, 0 ≤ φ σ := fun σ => by
    rw [hφ_eq]; exact tsum_nonneg fun k => sq_nonneg _
  have hφ_meas : AEStronglyMeasurable φ (volume.restrict I) := by
    have := aesm_tsum_box (a := fun σ k => ‖z σ k‖ ^ 2) measurableSet_Icc
      (fun k => (hzk k).norm.pow 2) hsum0
    exact this.congr (Filter.Eventually.of_forall fun σ => (hφ_eq σ).symm)
  have hφB : ∀ σ ∈ I, φ σ ≤ B := fun σ hσ =>
    (memHs_zero_of_memHs_one (hz1 σ hσ)).2.trans (hzB σ hσ)
  have hS0 : ∀ n σ, 0 ≤ S n σ := fun n σ => Finset.sum_nonneg fun k _ => sq_nonneg _
  have hSφ : ∀ n, ∀ σ ∈ I, S n σ ≤ φ σ := by
    intro n σ hσ
    rw [hφ_eq]
    exact Summable.sum_le_tsum _ (fun k _ => sq_nonneg _) (hsum0 σ hσ)
  have he0 : ∀ n σ, 0 ≤ e n σ := fun n σ => by
    simp only [he]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hK0) (Real.sqrt_nonneg _))
      (Real.sqrt_nonneg _)
  have heB : ∀ n, ∀ σ ∈ I, e n σ ≤ 2 * K * B := by
    intro n σ hσ
    have h1 : hsNorm 1 (z σ - truncCoeff n (z σ)) ≤ Real.sqrt B :=
      Real.sqrt_le_sqrt ((hsNormSq_sub_truncCoeff_le n (hz1 σ hσ)).trans (hzB σ hσ))
    have h2 : hsNorm 1 (z σ) ≤ Real.sqrt B := Real.sqrt_le_sqrt (hzB σ hσ)
    have h3 : 0 ≤ hsNorm 1 (z σ - truncCoeff n (z σ)) := Real.sqrt_nonneg _
    have h4 : 0 ≤ hsNorm 1 (z σ) := Real.sqrt_nonneg _
    simp only [he]
    calc 2 * K * hsNorm 1 (z σ - truncCoeff n (z σ)) * hsNorm 1 (z σ)
        ≤ 2 * K * Real.sqrt B * Real.sqrt B := by
          have : 0 ≤ 2 * K := by positivity
          gcongr
      _ = 2 * K * B := by rw [mul_assoc, Real.mul_self_sqrt hB0]
  have he_meas : ∀ n, AEStronglyMeasurable (e n) (volume.restrict I) := by
    intro n
    have h1 : AEStronglyMeasurable (fun σ => hsNorm 1 (z σ - truncCoeff n (z σ)))
        (volume.restrict I) := by
      have := aesm_tsum_box (a := fun σ k => sobWeight 1 k * ‖(z σ - truncCoeff n (z σ)) k‖ ^ 2)
        measurableSet_Icc (fun k => by
          by_cases hk : InBox n k
          · simp only [Pi.sub_apply, truncCoeff, hk, ite_true, sub_self, norm_zero]
            exact continuousOn_const
          · simp only [Pi.sub_apply, truncCoeff, hk, ite_false, sub_zero]
            exact continuousOn_const.mul ((hzk k).norm.pow 2))
          (fun σ hσ => memHs_sub_truncCoeff n (hz1 σ hσ))
      exact Real.continuous_sqrt.comp_aestronglyMeasurable this
    have h2 : AEStronglyMeasurable (fun σ => hsNorm 1 (z σ)) (volume.restrict I) := by
      have := aesm_tsum_box (a := fun σ k => sobWeight 1 k * ‖z σ k‖ ^ 2) measurableSet_Icc
        (fun k => continuousOn_const.mul ((hzk k).norm.pow 2)) (fun σ hσ => hz1 σ hσ)
      exact Real.continuous_sqrt.comp_aestronglyMeasurable this
    exact (h1.const_mul (2 * K)).mul h2
  have he_ii : ∀ n, ∀ τ ∈ I, IntervalIntegrable (e n) volume 0 τ := fun n τ hτ =>
    ii_of_bdd (he_meas n) (fun σ hσ => by
      rw [Real.norm_of_nonneg (he0 n σ)]; exact heB n σ hσ) hτ
  have hS_ii : ∀ n, ∀ τ ∈ I, IntervalIntegrable (S n) volume 0 τ := fun n τ hτ =>
    ((hSc n).mono (Set.uIcc_subset_Icc (show (0:ℝ) ∈ I from ⟨le_rfl, ht⟩) hτ)).intervalIntegrable
  have hineq : ∀ n, ∀ τ ∈ I, S n τ ≤ ∫ σ in (0:ℝ)..τ, (2 * Λ₀ * S n σ + e n σ) := by
    intro n τ hτ
    rw [hSY n τ hτ]
    exact intervalIntegral.integral_mono_on hτ.1 (hYint n τ hτ)
      (((hS_ii n τ hτ).const_mul (2 * Λ₀)).add (he_ii n τ hτ))
      (fun σ hσ => hYle n σ ⟨hσ.1, hσ.2.trans hτ.2⟩)
  have hlim : ∀ τ ∈ I, φ τ ≤ 2 * Λ₀ * ∫ σ in (0:ℝ)..τ, φ σ := by
    intro τ hτ
    have hsubIoc : Set.uIoc 0 τ ⊆ I := by
      rw [Set.uIoc_of_le hτ.1]; exact fun x hx => ⟨hx.1.le, hx.2.trans hτ.2⟩
    have ta : Tendsto (fun n => S n τ) atTop (𝓝 (φ τ)) := by
      rw [hφ_eq]; exact tendsto_box_sum (hsum0 τ hτ)
    have tb : Tendsto (fun n => ∫ σ in (0:ℝ)..τ, S n σ) atTop (𝓝 (∫ σ in (0:ℝ)..τ, φ σ)) := by
      refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => B) ?_ ?_ ?_ ?_
      · exact Filter.Eventually.of_forall fun n =>
          ((hSc n).mono hsubIoc).aestronglyMeasurable measurableSet_uIoc
      · refine Filter.Eventually.of_forall fun n => Filter.Eventually.of_forall fun σ hσ => ?_
        have hσI := hsubIoc hσ
        rw [Real.norm_of_nonneg (hS0 n σ)]
        exact (hSφ n σ hσI).trans (hφB σ hσI)
      · exact intervalIntegrable_const
      · refine Filter.Eventually.of_forall fun σ hσ => ?_
        have hσI := hsubIoc hσ
        rw [hφ_eq]; exact tendsto_box_sum (hsum0 σ hσI)
    have tc : Tendsto (fun n => ∫ σ in (0:ℝ)..τ, e n σ) atTop (𝓝 0) := by
      have := intervalIntegral.tendsto_integral_filter_of_dominated_convergence (μ := volume)
        (l := (atTop : Filter ℕ)) (F := fun n σ => e n σ) (f := fun _ => (0:ℝ)) (a := 0) (b := τ)
        (fun _ => 2 * K * B) ?_ ?_ intervalIntegrable_const ?_
      · simpa using this
      · exact Filter.Eventually.of_forall fun n =>
          (he_meas n).mono_set hsubIoc
      · refine Filter.Eventually.of_forall fun n => Filter.Eventually.of_forall fun σ hσ => ?_
        have hσI := hsubIoc hσ
        rw [Real.norm_of_nonneg (he0 n σ)]
        exact heB n σ hσI
      · refine Filter.Eventually.of_forall fun σ hσ => ?_
        have hσI := hsubIoc hσ
        have h := (truncCoeff_tendsto 1 (z σ) (hz1 σ hσI)).2
        have := (h.const_mul (2 * K)).mul_const (hsNorm 1 (z σ))
        simpa [he, mul_assoc] using this
    have td : Tendsto (fun n => ∫ σ in (0:ℝ)..τ, (2 * Λ₀ * S n σ + e n σ)) atTop
        (𝓝 ((2 * Λ₀ * ∫ σ in (0:ℝ)..τ, φ σ) + 0)) := by
      have : ∀ n, ∫ σ in (0:ℝ)..τ, (2 * Λ₀ * S n σ + e n σ) =
          (2 * Λ₀ * ∫ σ in (0:ℝ)..τ, S n σ) + ∫ σ in (0:ℝ)..τ, e n σ := by
        intro n
        rw [intervalIntegral.integral_add ((hS_ii n τ hτ).const_mul (2 * Λ₀)) (he_ii n τ hτ),
          intervalIntegral.integral_const_mul]
      simp_rw [this]
      exact (tb.const_mul _).add tc
    rw [add_zero] at td
    exact le_of_tendsto_of_tendsto' ta td (fun n => hineq n τ hτ)
  -- Gronwall
  have hgr := gronwall_integral φ t B (max (2 * Λ₀) 0) (le_max_right _ _)
    (fun τ _ => hφ0 τ) hφB hφ_meas (fun τ hτ => by
      refine (hlim τ hτ).trans ?_
      have h0 : 0 ≤ ∫ σ in (0:ℝ)..τ, φ σ :=
        intervalIntegral.integral_nonneg hτ.1 fun σ _ => hφ0 σ
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) h0)
  intro τ hτ
  have h0 : ∑' k, ‖z τ k‖ ^ 2 = 0 := by rw [← hφ_eq]; exact hgr τ hτ
  have h1 := (hasSum_zero_iff_of_nonneg (fun k => sq_nonneg ‖z τ k‖)).1
    (h0 ▸ (hsum0 τ hτ).hasSum)
  funext k
  have := congrFun h1 k
  simpa using this




theorem summable_sq_of_lp (x : lp (fun _ : Lattice d => ℂ) 2) : Summable fun k => ‖x k‖ ^ 2 := by
  have := (memℓp_gen_iff (by simp : 0 < (2 : ℝ≥0∞).toReal)).1 x.2
  simpa using this

theorem memℓp_yLp (c : Coeff d) (hc : MemHs 1 c) :
    Memℓp (fun k : Lattice d => (sw k : ℂ) * conj (c k)) 2 := by
  rw [memℓp_gen_iff (by simp : 0 < (2 : ℝ≥0∞).toReal)]
  have : Summable fun k => ‖(sw k : ℂ) * conj (c k)‖ ^ 2 := by
    refine hc.congr fun k => ?_
    rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, sw_sq]
    simp
  simpa using this

/-- The `ℓ²` vector `(√w_k conj c_k)_k` attached to `c ∈ H^1`. -/
def yLp (c : Coeff d) (hc : MemHs 1 c) : lp (fun _ : Lattice d => ℂ) 2 :=
  ⟨fun k => (sw k : ℂ) * conj (c k), memℓp_yLp c hc⟩

theorem yLp_norm_sq (c : Coeff d) (hc : MemHs 1 c) : ‖yLp c hc‖ ^ 2 = hsNormSq 1 c := by
  have h := lp.norm_rpow_eq_tsum (by simp : 0 < (2 : ℝ≥0∞).toReal) (yLp c hc)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h
  rw [h]
  unfold hsNormSq
  refine tsum_congr fun k => ?_
  simp only [yLp]
  rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, sw_sq]
  simp

theorem inner_yLp (c : Coeff d) (hc : MemHs 1 c) (x : lp (fun _ : Lattice d => ℂ) 2) :
    inner ℂ (yLp c hc) x = ∑' k, (sw k : ℂ) * c k * x k := by
  rw [lp.inner_eq_tsum]
  refine tsum_congr fun k => ?_
  simp [yLp, mul_comm, mul_assoc]

theorem weak_bounded {t : ℝ} {F : ℝ → Coeff d} (hF : WeakContinuousInHs 1 F t) :
    ∃ B, ∀ τ ∈ Set.Icc 0 t, hsNormSq 1 (F τ) ≤ B := by
  let g : Set.Icc (0:ℝ) t → (lp (fun _ : Lattice d => ℂ) 2 →L[ℂ] ℂ) :=
    fun τ => innerSL ℂ (yLp (F τ) (hF.1 τ τ.2))
  have hbdd : ∀ x : lp (fun _ : Lattice d => ℂ) 2, ∃ C, ∀ i, ‖g i x‖ ≤ C := by
    intro x
    set G : Coeff d := fun k => conj (x k) / (sw k : ℂ) with hG
    have hGm : MemHs 1 G := by
      refine (summable_sq_of_lp x).congr fun k => ?_
      have h0 : sw k ≠ 0 := (zero_lt_one.trans_le (one_le_sw k)).ne'
      simp only [hG, norm_div, Complex.norm_real, Real.norm_eq_abs, RCLike.norm_conj]
      rw [← sw_sq, div_pow, sq_abs]
      field_simp
    have hcont := hF.2 G hGm
    have heq : ∀ τ : Set.Icc (0:ℝ) t, g τ x = hsInner 1 (F τ) G := by
      intro τ
      simp only [g, innerSL_apply_apply]
      rw [inner_yLp]
      unfold hsInner
      refine tsum_congr fun k => ?_
      have h0 : sw k ≠ 0 := (zero_lt_one.trans_le (one_le_sw k)).ne'
      simp only [hG, map_div₀, Complex.conj_conj, Complex.conj_ofReal]
      rw [← sw_sq]
      push_cast
      field_simp
    have hc : Continuous fun τ : Set.Icc (0:ℝ) t => hsInner 1 (F τ) G :=
      continuousOn_iff_continuous_domRestrict.1 hcont
    obtain ⟨C, hC⟩ := (isCompact_range hc).isBounded.exists_norm_le
    exact ⟨C, fun i => by rw [heq]; exact hC _ ⟨i, rfl⟩⟩
  obtain ⟨C, hC⟩ := banach_steinhaus hbdd
  refine ⟨C ^ 2, fun τ hτ => ?_⟩
  have h1 := hC ⟨τ, hτ⟩
  simp only [g, innerSL_apply_norm] at h1
  rw [← yLp_norm_sq (F τ) (hF.1 τ hτ)]
  have h2 := norm_nonneg (yLp (F τ) (hF.1 τ hτ))
  exact pow_le_pow_left₀ h2 h1 2



theorem norm_le_cbNorm_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ : Torus d → E) (hφ : Continuous φ) (x : Torus d) : ‖φ x‖ ≤ Torus.cbNorm 0 φ := by
  unfold Torus.cbNorm
  simp only [zero_add, Finset.range_one, Finset.sum_singleton, norm_iteratedFDeriv_zero]
  obtain ⟨M, hM⟩ := (isCompact_univ (X := Torus d)).exists_bound_of_continuousOn hφ.continuousOn
  have hb : BddAbove (Set.range fun y : Euc d => ‖Torus.lift φ y‖) :=
    ⟨M, by
      rintro _ ⟨y, rfl⟩
      exact hM _ (Set.mem_univ _)⟩
  calc ‖φ x‖ = ‖Torus.lift φ (Torus.rep x)‖ := by simp [Torus.lift, Torus.mk_rep]
    _ ≤ _ := le_ciSup hb (Torus.rep x)

theorem abs_partialDeriv_le_cbNorm_one (j : Fin d) (φ : Torus d → ℝ) (hφ : Torus.IsCk 1 φ)
    (x : Torus d) : |Torus.partialDeriv j φ x| ≤ Torus.cbNorm 1 φ := by
  have hb := Torus.bddAbove_norm_iteratedFDeriv_lift 1 φ (by simpa [Torus.IsCk] using hφ)
  have h1 : ‖iteratedFDeriv ℝ 1 (Torus.lift φ) (Torus.rep x)‖ ≤
      ⨆ y : Euc d, ‖iteratedFDeriv ℝ 1 (Torus.lift φ) y‖ := le_ciSup hb (Torus.rep x)
  have h2 : |Torus.partialDeriv j φ x| ≤ ‖iteratedFDeriv ℝ 1 (Torus.lift φ) (Torus.rep x)‖ := by
    rw [norm_iteratedFDeriv_one]
    have := (fderiv ℝ (Torus.lift φ) (Torus.rep x)).le_opNorm (EuclideanSpace.single j (1 : ℝ))
    simpa [Torus.partialDeriv, PiLp.norm_single] using this
  refine h2.trans (h1.trans ?_)
  unfold Torus.cbNorm
  refine Finset.single_le_sum (f := fun i => ⨆ y : Euc d, ‖iteratedFDeriv ℝ i (Torus.lift φ) y‖)
    (fun i _ => Real.iSup_nonneg fun y => norm_nonneg _) (Finset.mem_range.2 (by norm_num))

theorem coeffOf_combo (c : Fin d → ℝ) (h : Fin d → Torus d → ℝ) (p : Torus d → ℝ)
    (hh : ∀ i, Continuous (h i)) (hp : Continuous p) :
    coeffOf (fun x => (∑ i, c i * h i x) - p x) =
      fun k => (∑ i, (c i : ℂ) * coeffOf (h i) k) - coeffOf p k := by
  funext k
  have hint : ∀ f : Torus d → ℝ, Continuous f → Integrable fun x => Torus.mode (-k) x * (f x : ℂ) :=
    fun f hf => ((Torus.continuous_mode (-k)).mul (Complex.continuous_ofReal.comp hf)
      ).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  simp only [coeffOf_eq_integral]
  have e : ∀ x, Torus.mode (-k) x * (((∑ i, c i * h i x) - p x : ℝ) : ℂ) =
      (∑ i, (c i : ℂ) * (Torus.mode (-k) x * (h i x : ℂ))) - Torus.mode (-k) x * (p x : ℂ) := by
    intro x
    push_cast
    rw [mul_sub, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring
  simp_rw [e]
  rw [integral_sub (integrable_finsetSum _ fun i _ => (hint (h i) (hh i)).const_mul _)
    (hint p hp), integral_finsetSum _ fun i _ => (hint (h i) (hh i)).const_mul _]
  simp_rw [integral_const_mul]


/-- For `d ≥ 2` (kernel facts of `Convention.lean`): the drift coefficients are those of a bounded
continuous function, with a bound uniform over the densities of norm `≤ Λ`. -/
theorem drift_fn (hd : 2 ≤ d) (D : DynData d) (MB VB Λ : ℝ) (m : ℕ) (hM : MatBound MB D.M)
    (hV : VHyp m VB D.V) :
    ∃ K : ℝ, ∀ ρ : Torus d → ℝ, Torus.IsCk (m + 3) ρ → Torus.cbNorm (m + 3) ρ ≤ Λ →
      ∀ j : Fin d, ∃ f : Torus d → ℝ, Continuous f ∧ (∀ x, |f x| ≤ K) ∧
        coeffOf f = driftCoeff D ρ j := by
  obtain ⟨C0, hC0⟩ := convGradConv_cbNorm hd D.hs0 D.hsd 0
  refine ⟨d * MB * (|C0| * Λ) + VB, fun ρ hρ hρΛ j => ?_⟩
  have hle3 : ((1 : ℕ) : WithTop ℕ∞) ≤ (m : WithTop ℕ∞) + 3 := by
    have : ((1 : ℕ) : WithTop ℕ∞) ≤ ((m + 3 : ℕ) : WithTop ℕ∞) := by exact_mod_cast (by omega)
    simpa using this
  have hle2 : ((2 : ℕ) : WithTop ℕ∞) ≤ (m : WithTop ℕ∞) + 3 := by
    have : ((2 : ℕ) : WithTop ℕ∞) ≤ ((m + 3 : ℕ) : WithTop ℕ∞) := by exact_mod_cast (by omega)
    simpa using this
  have hρ1 : Torus.IsCk 1 ρ := hρ.of_le (by simpa using hle3)
  have hV1 : Torus.IsCk 1 D.V := hV.1.of_le (by simpa using hle3)
  have hV2 : Torus.IsCk 2 D.V := hV.1.of_le (by simpa using hle2)
  obtain ⟨hconv0, hconvb⟩ := hC0 ρ hρ1
  have hconvc : Continuous (convGradConv (periodicRieszGrad d D.s) ρ) :=
    Torus.continuous_of_continuous_lift (by simpa [Torus.IsCk] using hconv0.continuous)
  have hcb1 : Torus.cbNorm 1 ρ ≤ Λ := (cbNorm_monoU (by omega) _).trans hρΛ
  have hcb0 : 0 ≤ Torus.cbNorm 1 ρ := Finset.sum_nonneg fun i _ => Real.iSup_nonneg fun y => norm_nonneg _
  -- components of the force
  set h : Fin d → Torus d → ℝ := fun i x => (convGradConv (periodicRieszGrad d D.s) ρ x) i with hh
  have hhc : ∀ i, Continuous (h i) := fun i =>
    (EuclideanSpace.proj i).continuous.comp hconvc
  have hhb : ∀ i x, |h i x| ≤ |C0| * Λ := by
    intro i x
    have h1 : |h i x| ≤ ‖convGradConv (periodicRieszGrad d D.s) ρ x‖ := by
      simpa [hh] using PiLp.norm_apply_le (convGradConv (periodicRieszGrad d D.s) ρ x) i
    refine h1.trans ((norm_le_cbNorm_zero _ hconvc x).trans (hconvb.trans ?_))
    calc C0 * Torus.cbNorm 1 ρ ≤ |C0| * Torus.cbNorm 1 ρ :=
          mul_le_mul_of_nonneg_right (le_abs_self _) hcb0
      _ ≤ |C0| * Λ := mul_le_mul_of_nonneg_left hcb1 (abs_nonneg _)
  have hhco : ∀ i, coeffOf (h i) = gradRieszCoeff d D.s i (coeffOf ρ) := fun i =>
    convGradConv_coeff hd D.hs0 D.hsd ρ hρ1 i
  -- the potential part
  have hpc : Continuous (Torus.partialDeriv j D.V) := by
    have h1 : Torus.IsCk 1 (Torus.partialDeriv j D.V) := isCk_one_partialDeriv j D.V hV2
    exact Torus.continuous_of_continuous_lift (by simpa [Torus.IsCk] using h1.continuous)
  have hpb : ∀ x, |Torus.partialDeriv j D.V x| ≤ VB := fun x =>
    (abs_partialDeriv_le_cbNorm_one j D.V hV1 x).trans
      ((cbNorm_monoU (by omega) _).trans hV.2)
  refine ⟨fun x => (∑ i, D.M j i * h i x) - Torus.partialDeriv j D.V x, ?_, fun x => ?_, ?_⟩
  · exact (continuous_finsetSum _ fun i _ => continuous_const.mul (hhc i)).sub hpc
  · refine (abs_sub _ _).trans ?_
    refine add_le_add ?_ (hpb x)
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i, |D.M j i * h i x| ≤ ∑ _i : Fin d, MB * (|C0| * Λ) := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [abs_mul]
          exact mul_le_mul (hM j i) (hhb i x) (abs_nonneg _) ((abs_nonneg _).trans (hM j i))
      _ = d * MB * (|C0| * Λ) := by simp; ring
  · rw [coeffOf_combo _ h _ hhc hpc]
    funext k
    simp only [hhco, coeffOf_partialDeriv j D.V hV1, driftCoeff]


theorem fcoef_decay_of_bound {φ : Torus d → ℝ} {n : ℕ} (hd : ContDiff ℝ n (Torus.lift φ)) {B₀ : ℝ}
    (hB₀ : ∀ y : Euc d, ‖iteratedFDeriv ℝ n (Torus.lift φ) y‖ ≤ B₀) (k : NonzeroLattice d) :
    ‖Torus.fcoef φ k.1‖ * Lattice.jp k.1 ^ n ≤ B₀ * ((1 + 2 * Real.pi) / (2 * Real.pi)) ^ n := by
  have hG : Torus.Per (Torus.lift φ) := fun y n => Torus.lift_periodic φ y n
  have hpi := Real.pi_pos
  have hk0 : 0 < Lattice.enorm k.1 := by
    have := (jp_le_enorm k)
    have h1 := Torus.jp_ge_one k.1
    by_contra h
    have : Lattice.enorm k.1 ≤ 0 := not_lt.mp h
    nlinarith
  set e : Euc d := (Lattice.enorm k.1)⁻¹ • Lattice.toEuc k.1 with he
  have hne : ‖e‖ = 1 := by
    rw [he, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hk0]
    exact inv_mul_cancel₀ hk0.ne'
  have hdot : Lattice.dot k.1 e = Lattice.enorm k.1 := by
    rw [Torus.dot_eq_inner, he, real_inner_smul_right, real_inner_self_eq_norm_sq]
    unfold Lattice.enorm
    field_simp
  let m : Fin n → Euc d := fun _ => e
  set g := Torus.descend (fun z => iteratedFDeriv ℝ n (Torus.lift φ) z m) with hg
  have hper : Torus.Per (fun z => iteratedFDeriv ℝ n (Torus.lift φ) z m) := hG.iteratedFDeriv_apply m
  have hbd : ∀ x, |g x| ≤ B₀ := by
    intro x
    rw [hg, ← Torus.mk_rep x, Torus.descend_mk hper]
    have h1 := (iteratedFDeriv ℝ n (Torus.lift φ) (Torus.rep x)).le_opNorm m
    have h2 : ∏ i, ‖m i‖ = 1 := by simp [m, hne]
    rw [h2, mul_one] at h1
    exact (Real.norm_eq_abs _ ▸ h1).trans (hB₀ _)
  have h1 := Torus.norm_fcoef_le_of_bound hbd k.1
  rw [hg, Torus.fcoef_iteratedFDeriv hG hd k.1 n le_rfl m, Torus.descend_lift] at h1
  have h2 : ‖(2 * (Real.pi : ℂ) * Complex.I)‖ = 2 * Real.pi := by simp [Complex.norm_I]
  rw [norm_mul, norm_mul, norm_pow, h2, norm_prod] at h1
  simp only [m, hdot, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hk0] at h1
  have h3 : Lattice.jp k.1 ^ n ≤ ((1 + 2 * Real.pi) / (2 * Real.pi)) ^ n * (2 * Real.pi) ^ n * Lattice.enorm k.1 ^ n := by
    rw [← mul_pow, ← mul_pow]
    refine pow_le_pow_left₀ (Torus.jp_pos _).le ?_ n
    have := jp_le_enorm k
    calc Lattice.jp k.1 ≤ (1 + 2 * Real.pi) * Lattice.enorm k.1 := this
      _ = _ := by field_simp
  calc ‖Torus.fcoef φ k.1‖ * Lattice.jp k.1 ^ n
      ≤ ‖Torus.fcoef φ k.1‖ * (((1 + 2 * Real.pi) / (2 * Real.pi)) ^ n * (2 * Real.pi) ^ n * Lattice.enorm k.1 ^ n) :=
        mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
    _ = ((1 + 2 * Real.pi) / (2 * Real.pi)) ^ n * ((2 * Real.pi) ^ n * Lattice.enorm k.1 ^ n * ‖Torus.fcoef φ k.1‖) := by ring
    _ ≤ ((1 + 2 * Real.pi) / (2 * Real.pi)) ^ n * B₀ := by gcongr
    _ = _ := by ring





theorem sw_eq_jp (k : Lattice d) : sw k = Lattice.jp k := by
  unfold sw
  rw [sobWeight_eq_jp]
  have h := Torus.jp_pos k
  rw [show (2 * (1:ℝ)) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
  exact Real.sqrt_sq h.le

theorem iSup_iter_le_cbNorm {m n : ℕ} (hn : n ≤ m) (ρ : Torus d → ℝ) :
    (⨆ y : Euc d, ‖iteratedFDeriv ℝ n (Torus.lift ρ) y‖) ≤ Torus.cbNorm m ρ := by
  unfold Torus.cbNorm
  exact Finset.single_le_sum (f := fun i => ⨆ y : Euc d, ‖iteratedFDeriv ℝ i (Torus.lift ρ) y‖)
    (fun i _ => Real.iSup_nonneg fun y => norm_nonneg _) (Finset.mem_range.2 (by omega))

theorem coeffOf_decay {m : ℕ} (ρ : Torus d → ℝ) (hρ : Torus.IsCk m ρ) (k : Lattice d)
    (hk : k ≠ 0) :
    ‖coeffOf ρ k‖ * Lattice.jp k ^ m ≤
      Torus.cbNorm m ρ * ((1 + 2 * Real.pi) / (2 * Real.pi)) ^ m := by
  have hb := Torus.bddAbove_norm_iteratedFDeriv_lift m ρ hρ
  have := fcoef_decay_of_bound (n := m) hρ (B₀ := Torus.cbNorm m ρ)
    (fun y => ((le_ciSup hb y).trans (iSup_iter_le_cbNorm le_rfl ρ))) ⟨k, hk⟩
  rwa [coeffOf_eq_fcoef]

theorem l1_of_decay (hd : d < 2) (a : Coeff d) (ha0 : a 0 = 0) (B : ℝ)
    (hB : ∀ k : Lattice d, k ≠ 0 → ‖a k‖ * Lattice.jp k ^ 2 ≤ B) :
    Summable (fun k => ‖a k‖) ∧
      ∑' k, ‖a k‖ ≤ B * ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * (1:ℝ))) := by
  have hS := summable_jp_rpow (d := d) 1
    (by have : (d:ℝ) < 2 := by exact_mod_cast hd
        linarith)
  have hle : ∀ k : NonzeroLattice d, ‖a k.1‖ ≤ B * Lattice.jp k.1 ^ (-(2 * (1:ℝ))) := by
    intro k
    have hj := Torus.jp_pos k.1
    have h := hB k.1 k.2
    have e : Lattice.jp k.1 ^ (-(2 * (1:ℝ))) = (Lattice.jp k.1 ^ 2)⁻¹ := by
      rw [show -(2*(1:ℝ)) = -((2:ℕ):ℝ) by norm_num, Real.rpow_neg hj.le, Real.rpow_natCast]
    rw [e, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    exact h
  have hs : Summable (fun k : NonzeroLattice d => ‖a k.1‖) :=
    Summable.of_nonneg_of_le (fun k => norm_nonneg _) hle (hS.mul_left B)
  have hsum : Summable (fun k => ‖a k‖) := (Torus.summable_lattice_iff _).mpr hs
  refine ⟨hsum, ?_⟩
  rw [Torus.tsum_lattice _ hsum, ha0, norm_zero, zero_add, ← tsum_mul_left]
  exact hs.tsum_le_tsum hle (hS.mul_left B)

theorem continuous_series (c : Coeff d) (hs : Summable fun k => ‖c k‖) :
    Continuous (series c) := by
  unfold series
  exact continuous_tsum (u := fun k => ‖c k‖)
    (fun k => continuous_const.mul (Torus.continuous_mode k)) hs (fun k x => by
      simp [Torus.norm_mode])

theorem continuous_toFun (c : Coeff d) (hs : Summable fun k => ‖c k‖) :
    Continuous (toFun c) :=
  Complex.continuous_re.comp (continuous_series c hs)

theorem abs_toFun_le (c : Coeff d) (hs : Summable fun k => ‖c k‖) (x : Torus d) :
    |toFun c x| ≤ ∑' k, ‖c k‖ := by
  unfold toFun
  refine (Complex.abs_re_le_norm _).trans ?_
  unfold series
  have hn : Summable fun k => ‖c k * Torus.mode k x‖ :=
    hs.congr (fun k => by simp [Torus.norm_mode])
  refine (norm_tsum_le_tsum_norm hn).trans (le_of_eq (tsum_congr fun k => ?_))
  simp [Torus.norm_mode]

theorem driftCoeff_zero (D : DynData d) (ρ : Torus d → ℝ) (j : Fin d) :
    driftCoeff D ρ j 0 = 0 := by
  simp [driftCoeff, gradRieszCoeff, derivCoeff]



theorem continuous_of_isCkU {m : ℕ} {ρ : Torus d → ℝ} (h : Torus.IsCk m ρ) : Continuous ρ :=
  Torus.continuous_of_continuous_lift (by simpa [Torus.IsCk] using h.continuous)

theorem isRealCoeff_coeffOf_of_isCk {m : ℕ} {ρ : Torus d → ℝ} (h : Torus.IsCk m ρ) :
    IsRealCoeff (coeffOf ρ) :=
  isRealCoeff_coeffOf ρ ((continuous_of_isCkU h).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _))

/-- For `d < 2` (so `d = 1` when `d ≥ 1`): the drift coefficients are those of a bounded continuous
function (via absolutely summable Fourier series), uniformly over densities of norm `≤ Λ`. -/
theorem drift_fn_one (hd : d < 2) (D : DynData d) (MB VB Λ : ℝ) (m : ℕ) (hM : MatBound MB D.M)
    (hV : VHyp m VB D.V) :
    ∃ K : ℝ, ∀ ρ : Torus d → ℝ, Torus.IsCk (m + 3) ρ → Torus.cbNorm (m + 3) ρ ≤ Λ →
      ∀ j : Fin d, ∃ f : Torus d → ℝ, Continuous f ∧ (∀ x, |f x| ≤ K) ∧
        coeffOf f = driftCoeff D ρ j := by
  set c3 : ℝ := ((1 + 2 * Real.pi) / (2 * Real.pi)) ^ 3 with hc3
  set S := ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * (1:ℝ))) with hS
  set rc := |rieszConst d D.s| with hrc
  have hV3 : Torus.IsCk (3 : ℕ) D.V := hV.1.of_le (by
    have : ((3 : ℕ) : WithTop ℕ∞) ≤ ((m + 3 : ℕ) : WithTop ℕ∞) := by exact_mod_cast (by omega)
    simpa using this)
  have hVd : ∀ k : Lattice d, k ≠ 0 → ‖coeffOf D.V k‖ * Lattice.jp k ^ 3 ≤ VB * c3 := by
    intro k hk
    refine (coeffOf_decay D.V hV3 k hk).trans ?_
    exact mul_le_mul_of_nonneg_right ((cbNorm_monoU (by omega) _).trans hV.2) (by positivity)
  refine ⟨(d * (MB * (rc * (Λ * c3))) + VB * c3) * S, fun ρ hρ hρΛ j => ?_⟩
  have hρ3 : Torus.IsCk (3 : ℕ) ρ := hρ.of_le (by
    have : ((3 : ℕ) : WithTop ℕ∞) ≤ ((m + 3 : ℕ) : WithTop ℕ∞) := by exact_mod_cast (by omega)
    simpa using this)
  have hρd : ∀ k : Lattice d, k ≠ 0 → ‖coeffOf ρ k‖ * Lattice.jp k ^ 3 ≤ Λ * c3 := by
    intro k hk
    refine (coeffOf_decay ρ hρ3 k hk).trans ?_
    exact mul_le_mul_of_nonneg_right ((cbNorm_monoU (by omega) _).trans hρΛ) (by positivity)
  have hdr : ∀ k : Lattice d, k ≠ 0 →
      ‖driftCoeff D ρ j k‖ * Lattice.jp k ^ 2 ≤ d * (MB * (rc * (Λ * c3))) + VB * c3 := by
    intro k hk
    have hj := Torus.jp_pos k
    have h1 : ‖driftCoeff D ρ j k‖ ≤
        (∑ i : Fin d, |D.M j i| * (rc * (Lattice.jp k * ‖coeffOf ρ k‖))) +
          Lattice.jp k * ‖coeffOf D.V k‖ := by
      unfold driftCoeff
      refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
      · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        have := norm_gradRieszCoeff_le (s := D.s) D.hsd i (coeffOf ρ) k
        rwa [sw_eq_jp, mul_assoc] at this
      · have := norm_derivCoeff_le j (coeffOf D.V) k
        rwa [sw_eq_jp] at this
    have h2 : ‖driftCoeff D ρ j k‖ * Lattice.jp k ^ 2 ≤
        (∑ i : Fin d, |D.M j i| * (rc * (‖coeffOf ρ k‖ * Lattice.jp k ^ 3))) +
          ‖coeffOf D.V k‖ * Lattice.jp k ^ 3 := by
      calc ‖driftCoeff D ρ j k‖ * Lattice.jp k ^ 2
          ≤ ((∑ i : Fin d, |D.M j i| * (rc * (Lattice.jp k * ‖coeffOf ρ k‖))) +
            Lattice.jp k * ‖coeffOf D.V k‖) * Lattice.jp k ^ 2 :=
            mul_le_mul_of_nonneg_right h1 (by positivity)
        _ = _ := by rw [add_mul, Finset.sum_mul]; congr 1 <;> [refine Finset.sum_congr rfl fun i _ => ?_; skip] <;> ring
    refine h2.trans (add_le_add ?_ (hVd k hk))
    calc (∑ i : Fin d, |D.M j i| * (rc * (‖coeffOf ρ k‖ * Lattice.jp k ^ 3)))
        ≤ ∑ _i : Fin d, MB * (rc * (Λ * c3)) := by
          refine Finset.sum_le_sum fun i _ => ?_
          have hr0 : 0 ≤ rc * (‖coeffOf ρ k‖ * Lattice.jp k ^ 3) := by positivity
          exact mul_le_mul (hM j i) (mul_le_mul_of_nonneg_left (hρd k hk) (abs_nonneg _))
            (by positivity) ((abs_nonneg _).trans (hM j i))
      _ = _ := by simp
  obtain ⟨hsum, hbound⟩ := l1_of_decay hd (driftCoeff D ρ j) (driftCoeff_zero D ρ j) _ hdr
  have hreal := isRealCoeff_driftCoeff D ρ (isRealCoeff_coeffOf_of_isCk hρ)
    (isRealCoeff_coeffOf_of_isCk hV.1) j
  exact ⟨toFun (driftCoeff D ρ j), continuous_toFun _ hsum,
    fun x => (abs_toFun_le _ hsum x).trans hbound, coeffOf_toFun _ hreal hsum⟩



theorem memHs_sub {m : ℝ} {a b : Coeff d} (ha : MemHs m a) (hb : MemHs m b) :
    MemHs m (a - b) := by
  refine Summable.of_nonneg_of_le (fun k => mul_nonneg (sobWeight_nonneg m k) (sq_nonneg _))
    (fun k => ?_) ((ha.mul_left 2).add (hb.mul_left 2))
  have h := norm_sub_le (a k) (b k)
  have h0 := norm_nonneg (a k)
  have h1 := norm_nonneg (b k)
  have h2 : ‖(a - b) k‖ ^ 2 ≤ 2 * ‖a k‖ ^ 2 + 2 * ‖b k‖ ^ 2 := by
    simp only [Pi.sub_apply]
    nlinarith [sq_nonneg (‖a k‖ - ‖b k‖), norm_nonneg (a k - b k)]
  have hw := sobWeight_nonneg m k
  nlinarith [mul_le_mul_of_nonneg_left h2 hw]

theorem hsNormSq_sub_le {m : ℝ} {a b : Coeff d} (ha : MemHs m a) (hb : MemHs m b) :
    hsNormSq m (a - b) ≤ 2 * hsNormSq m a + 2 * hsNormSq m b := by
  unfold hsNormSq
  rw [← tsum_mul_left, ← tsum_mul_left, ← (ha.mul_left 2).tsum_add (hb.mul_left 2)]
  refine (memHs_sub ha hb).tsum_le_tsum (fun k => ?_) ((ha.mul_left 2).add (hb.mul_left 2))
  have h := norm_sub_le (a k) (b k)
  have h0 := norm_nonneg (a k)
  have h1 := norm_nonneg (b k)
  have h2 : ‖(a - b) k‖ ^ 2 ≤ 2 * ‖a k‖ ^ 2 + 2 * ‖b k‖ ^ 2 := by
    simp only [Pi.sub_apply]
    nlinarith [sq_nonneg (‖a k‖ - ‖b k‖), norm_nonneg (a k - b k)]
  have hw := sobWeight_nonneg m k
  nlinarith [mul_le_mul_of_nonneg_left h2 hw]

theorem forwardGen_sub_H1 (D : DynData d) (ρ : Torus d → ℝ) (hρ : MemHs 0 (coeffOf ρ))
    (hb : ∀ j, MemHs 0 (driftCoeff D ρ j)) {u v : Coeff d} (hu : MemHs 1 u) (hv : MemHs 1 v) :
    forwardGen D ρ (u - v) = forwardGen D ρ u - forwardGen D ρ v := by
  have h := forwardGen_add_H1 D ρ hρ hb (memHs_sub hu hv) hv
  rw [sub_add_cancel] at h
  rw [h]; abel

theorem opConst_nonneg (D : DynData d) {K : ℝ} (hK : 0 ≤ K) : 0 ≤ opConst D K := by
  unfold opConst
  have := D.hβ
  positivity

theorem uniform_multBound (hd : 1 ≤ d) {s : ℝ} {m : ℕ} {R : Regime} {MB Λ VB : ℝ}
    {D : DynData d} {ν₀ T : ℝ} {μ : ℝ → Torus d → ℝ}
    (hA : AdjointData s m R MB Λ VB D ν₀ T μ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ r ∈ Set.Icc (0:ℝ) T,
      MultBound (coeffOf (μ r)) K ∧ ∀ j, MultBound (driftCoeff D (μ r) j) K := by
  obtain ⟨K', hK'⟩ : ∃ K' : ℝ, ∀ ρ : Torus d → ℝ, Torus.IsCk (m + 3) ρ →
      Torus.cbNorm (m + 3) ρ ≤ Λ → ∀ j : Fin d, ∃ f : Torus d → ℝ, Continuous f ∧
        (∀ x, |f x| ≤ K') ∧ coeffOf f = driftCoeff D ρ j := by
    by_cases h2 : 2 ≤ d
    · exact drift_fn h2 D MB VB Λ m hA.hM hA.hV
    · exact drift_fn_one (by omega) D MB VB Λ m hA.hM hA.hV
  refine ⟨|Λ| + |K'|, by positivity, fun r hr => ⟨?_, fun j => ?_⟩⟩
  · have hcont := continuous_of_isCkU (hA.hμ.smooth r hr)
    refine multBound_of_sup _ hcont _ (fun x => ?_)
    have h1 := norm_le_cbNorm_zero (μ r) hcont x
    have h2 := (cbNorm_monoU (Nat.zero_le (m + 3)) (μ r)).trans (hA.hμ.bound r hr)
    rw [Real.norm_eq_abs] at h1
    have := le_abs_self Λ
    have := abs_nonneg K'
    linarith
  · obtain ⟨f, hfc, hfb, hfe⟩ := hK' (μ r) (hA.hμ.smooth r hr) (hA.hμ.bound r hr) j
    rw [← hfe]
    refine multBound_of_sup f hfc _ (fun x => ?_)
    have := (hfb x).trans (le_abs_self K')
    have := abs_nonneg Λ
    linarith



/-- The level-`0` energy hypothesis for all (complex) trigonometric polynomials, from
`energy_form_estimate` at `m = 0` and the real/imaginary splitting `complex_form`. -/
theorem uniq_energy (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d)
    (R : Regime) (MB Λ VB : ℝ) :
    ∃ C : ℝ, ∀ (D : DynData d) (ν₀ T : ℝ) (μ : ℝ → Torus d → ℝ)
      (_ : AdjointData s 0 R MB Λ VB D ν₀ T μ) (r : ℝ) (_ : r ∈ Set.Icc 0 T) (n : ℕ)
      (w : Coeff d) (_ : IsTrigPoly n w),
      (hsInner 0 (forwardGen D (μ r) w) w).re ≤
        R.lambdaM C ν₀ (thetaOrder d s) * hsNormSq 0 w := by
  obtain ⟨C, hC, hmain⟩ := energy_form_estimate hd s hs0 hsd 0 R MB Λ VB
  refine ⟨C, fun D ν₀ T μ hA r hr n w hw => ?_⟩
  obtain ⟨lam, q, hlq⟩ : ∃ (lam : Fin d → ℝ) (q : Fin d → Euc d),
      R.IsR2 → IsSymDiag D.M lam q := by
    by_cases hR : R.IsR2
    · obtain ⟨lam, q, h⟩ := exists_symDiag (regime_symNonpos hR hA.regime)
      exact ⟨lam, q, fun _ => h⟩
    · exact ⟨0, fun _ => 0, fun h => absurd h hR⟩
  have hreal : ∀ G, IsRealCoeff G → IsTrigPoly n G →
      (hsInner 0 (forwardGen D (μ r) G) G).re ≤
        R.lambdaM C ν₀ (thetaOrder d s) * hsNormSq 0 G := by
    intro G hG hGt
    have h1 := (hmain D ν₀ T μ hA lam q hlq r hr n G hG hGt).2.trans
      (energyRHS_le hd R _ D 0 lam q (fun hR l => (hlq hR).nonneg l) (μ r) G)
    simpa using h1
  have hρ := isRealCoeff_coeffOf_of_isCk (hA.hμ.smooth r hr)
  have hV := isRealCoeff_coeffOf_of_isCk hA.hV.1
  exact complex_form (L := forwardGen D (μ r))
    (fun a b ha hb => forwardGen_add D (μ r) a b ha hb)
    (fun c a => forwardGen_smul D (μ r) a c)
    (fun a => forwardGen_reflConj D (μ r) hρ hV a) hreal w hw

theorem forward_unique_core (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ)
    (R : Regime) (MB Λ VB : ℝ) (D : DynData d) (ν₀ T : ℝ) (μ : ℝ → Torus d → ℝ)
    (hA : AdjointData s m R MB Λ VB D ν₀ T μ) (t : ℝ) (ht : t ∈ Set.Ioc 0 T) (φc : Coeff d)
    (F₁ F₂ : ℝ → Coeff d) (h₁ : IsForwardSolution D μ t φc F₁) (w₁ : WeakContinuousInHs 1 F₁ t)
    (h₂ : IsForwardSolution D μ t φc F₂) (w₂ : WeakContinuousInHs 1 F₂ t) :
    ∀ τ ∈ Set.Icc 0 t, F₁ τ = F₂ τ := by
  have hA0 := adjointData_zero hA
  obtain ⟨C, hen⟩ := uniq_energy hd s hs0 hsd R MB Λ VB
  obtain ⟨K, hK0, hKm⟩ := uniform_multBound hd hA
  have ht0 : 0 ≤ t := ht.1.le
  have hrT : ∀ σ ∈ Set.Icc (0:ℝ) t, t - σ ∈ Set.Icc (0:ℝ) T := fun σ hσ =>
    ⟨by linarith [hσ.2], by linarith [hσ.1, ht.2]⟩
  obtain ⟨B₁, hB₁⟩ := weak_bounded w₁
  obtain ⟨B₂, hB₂⟩ := weak_bounded w₂
  have hmem0 : ∀ σ ∈ Set.Icc (0:ℝ) t, MemHs 0 (coeffOf (μ (t - σ))) := fun σ hσ =>
    (hKm _ (hrT σ hσ)).1.memHs0
  have hmemb : ∀ σ ∈ Set.Icc (0:ℝ) t, ∀ j, MemHs 0 (driftCoeff D (μ (t - σ)) j) :=
    fun σ hσ j => ((hKm _ (hrT σ hσ)).2 j).memHs0
  have key := abstract_unique t (2 * B₁ + 2 * B₂) (opConst D K)
    (R.lambdaM C ν₀ (thetaOrder d s)) ht0 (opConst_nonneg D hK0)
    (fun σ => F₁ σ - F₂ σ)
    (fun σ => forwardGen D (μ (t - σ)) (F₁ σ) - forwardGen D (μ (t - σ)) (F₂ σ))
    (fun σ => forwardGen D (μ (t - σ)))
    (fun σ hσ => memHs_sub (h₁.h1 σ hσ) (h₂.h1 σ hσ))
    (fun σ hσ => by
      have := hsNormSq_sub_le (h₁.h1 σ hσ) (h₂.h1 σ hσ)
      have := hB₁ σ hσ
      have := hB₂ σ hσ
      show hsNormSq 1 (F₁ σ - F₂ σ) ≤ _
      linarith)
    (fun k => (h₁.integrable k).sub (h₂.integrable k))
    (fun k τ hτ => by
      have hi : ∀ F : ℝ → Coeff d, (∀ k, IntegrableOn (fun σ => forwardGen D (μ (t - σ)) (F σ) k)
          (Set.Icc 0 t)) → IntervalIntegrable (fun σ => forwardGen D (μ (t - σ)) (F σ) k)
            volume 0 τ := fun F hF => by
        rw [intervalIntegrable_iff_integrableOn_Icc_of_le hτ.1]
        exact (hF k).mono_set (Set.Icc_subset_Icc_right hτ.2)
      show F₁ τ k - F₂ τ k = ∫ σ in (0:ℝ)..τ, (forwardGen D (μ (t - σ)) (F₁ σ) k -
        forwardGen D (μ (t - σ)) (F₂ σ) k)
      rw [h₁.eq k τ hτ, h₂.eq k τ hτ, intervalIntegral.integral_sub (hi F₁ h₁.integrable)
        (hi F₂ h₂.integrable)]
      ring)
    (fun σ hσ => (forwardGen_sub_H1 D _ (hmem0 σ hσ) (hmemb σ hσ) (h₁.h1 σ hσ) (h₂.h1 σ hσ)).symm)
    (fun σ hσ u v hu hv => forwardGen_add_H1 D _ (hmem0 σ hσ) (hmemb σ hσ) hu hv)
    (fun σ hσ u hu => forwardGen_dual D _ K hK0 (hKm _ (hrT σ hσ)).1 (hKm _ (hrT σ hσ)).2 u hu)
    (fun σ hσ n w hw => hen D ν₀ T μ hA0 (t - σ) (hrT σ hσ) n w hw)
  intro τ hτ
  exact sub_eq_zero.mp (key τ hτ)

end HRS.PDE
