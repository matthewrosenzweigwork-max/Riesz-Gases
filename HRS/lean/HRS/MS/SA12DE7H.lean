import HRS.MS.SA12DE7G

/-!
# S.A.12(c), packet E7.07 (worker S82Z2), part H: the exact Plancherel identity for ordered weak jets

`SA12WeakJet m u g`: `g j idx` (`j ≤ m`, `idx : Fin j → Fin d`) is an ordered family of `L²` functions with `g 0 = u` and
`g (j+1) (cons i idx) = ∂_i (g j idx)` in the weak sense against real `C_c^∞` tests.  (This is the form in which the limit of
the box jets of `∂^idx F_n` is identified with the weak derivatives of `F(τ)`; for smooth `F`, `partialDeriv (cons i idx) F =
∂_i (partialDeriv idx F)`.)

`sa12de7_sobolev_jet_weak`: then `u ∈ H^m` and `‖u‖²_{H^m} = ∑_{j ≤ m} C(m,j) ∑_{idx} ∫ (g j idx)²`, with ordered indices and
binomial weights (`WD.fourier`, Plancherel, the weight identity of part A).  `sa12de7_sobolevNormE_le_of_weak_jet`: the
resulting bound on `sobolevNormE`.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform

namespace HRS.MS.SA12DE7

open HRS HRS.Whole HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux HRS.MH.AdjointRd HRS.MH.AdjointRd.Phase2SA12Limit
  HRS.Whole.AppendixA HRS.Whole.Q09A

variable {d : ℕ}

/-- Ordered weak jet chain of order `m` of `u` (real `C_c^∞` tests). -/
structure SA12WeakJet (m : ℕ) (u : Euc d → ℝ) (g : (j : ℕ) → (Fin j → Fin d) → Euc d → ℝ) : Prop where
  zero : ∀ idx : Fin 0 → Fin d, g 0 idx = u
  memLp : ∀ j, j ≤ m → ∀ idx : Fin j → Fin d, MemLp (g j idx) 2 volume
  step : ∀ j, j < m → ∀ (i : Fin d) (idx : Fin j → Fin d) (ψ : Euc d → ℝ), IsCcInfty ψ →
    ∫ x, g (j + 1) (Fin.cons i idx : Fin (j + 1) → Fin d) x * ψ x =
      -∫ x, g j idx x * fderiv ℝ ψ x (EuclideanSpace.single i (1 : ℝ))

theorem sa12de7_norm_prod_sq {j : ℕ} (idx : Fin j → Fin d) (ξ : Euc d) :
    ‖∏ l : Fin j, (2 * (Real.pi : ℂ) * Complex.I * ((ξ (idx l) : ℝ) : ℂ))‖ ^ 2 =
      (2 * Real.pi) ^ (2 * j) * ∏ l : Fin j, (ξ (idx l)) ^ 2 := by
  rw [norm_prod, ← Finset.prod_pow]
  have : ∀ l : Fin j, ‖(2 * (Real.pi : ℂ) * Complex.I * ((ξ (idx l) : ℝ) : ℂ))‖ ^ 2 =
      (2 * Real.pi) ^ 2 * (ξ (idx l)) ^ 2 := by
    intro l
    rw [norm_mul, norm_mul, mul_pow, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    simp [abs_of_pos Real.pi_pos]
  rw [Finset.prod_congr rfl fun l _ => this l, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, ← pow_mul]

/-- The Fourier transform of the `(j, idx)` jet is `∏ (2πi ξ_{idx l}) û`. -/
theorem sa12de7_jet_fourier {m : ℕ} {u : Euc d → ℝ} {g : (j : ℕ) → (Fin j → Fin d) → Euc d → ℝ}
    (hg : SA12WeakJet m u g) (hu : MemLp (fun x => ((u x : ℝ) : ℂ)) 2 volume) :
    ∀ j (hj : j ≤ m) (idx : Fin j → Fin d),
      fcL ((hg.memLp j hj idx).ofReal (K := ℂ)) =ᵐ[volume]
        fun ξ => (∏ l : Fin j, (2 * (Real.pi : ℂ) * Complex.I * ((ξ (idx l) : ℝ) : ℂ))) * fcL hu ξ := by
  intro j
  induction j with
  | zero =>
    intro hj idx
    have e : (fun x => ((g 0 idx x : ℝ) : ℂ)) = fun x => ((u x : ℝ) : ℂ) := by
      funext x; rw [hg.zero idx]
    have := fcL_congr ((hg.memLp 0 hj idx).ofReal (K := ℂ)) hu e
    exact Filter.Eventually.of_forall fun ξ => by simp [this]
  | succ j ih =>
    intro hj idx
    have hjm : j < m := Nat.lt_of_succ_le hj
    have hstep := hg.step j hjm (idx 0) (Fin.tail idx)
    simp only [Fin.cons_self_tail] at hstep
    have hWD := sa12de7_WD_of_cc (hg.memLp j hjm.le (Fin.tail idx)) (hg.memLp (j + 1) hj idx) (idx 0) hstep
    have h1 := hWD.fourier
    have h2 := ih hjm.le (Fin.tail idx)
    filter_upwards [h1, h2] with ξ e1 e2
    rw [Fin.prod_univ_succ]
    have e1' : fcL ((hg.memLp (j + 1) hj idx).ofReal (K := ℂ)) ξ =
        (2 * Real.pi * Complex.I * ((ξ (idx 0) : ℝ) : ℂ)) *
          fcL ((hg.memLp j hjm.le (Fin.tail idx)).ofReal (K := ℂ)) ξ := e1
    rw [e1', e2]
    simp only [Fin.tail]
    ring

/-- **Exact Plancherel identity for ordered weak jets**. -/
theorem sa12de7_sobolev_jet_weak {m : ℕ} {u : Euc d → ℝ} {g : (j : ℕ) → (Fin j → Fin d) → Euc d → ℝ}
    (hg : SA12WeakJet m u g) :
    HRS.PDE.ToolboxRd.MemSobolev (m : ℝ) u ∧
      sobolevNormSq (m : ℝ) u = ∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ) *
        ∑ idx : Fin j → Fin d, ∫ x, (g j idx x) ^ 2 := by
  have hu2 : MemLp u 2 volume := by
    have := hg.memLp 0 (Nat.zero_le _) Fin.elim0
    rwa [hg.zero Fin.elim0] at this
  have hu : MemLp (fun x => ((u x : ℝ) : ℂ)) 2 volume := hu2.ofReal (K := ℂ)
  have hfL : fourierL2 u = fcL hu := fourierL2_eq hu2
  have hjf := sa12de7_jet_fourier hg hu
  have hmj : ∀ j ∈ Finset.range (m + 1), j ≤ m := fun j hj => Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  classical
  let Φ : (j : ℕ) → (Fin j → Fin d) → Euc d → ℂ := fun j idx ξ =>
    if h : j ≤ m then fcL ((hg.memLp j h idx).ofReal (K := ℂ)) ξ else 0
  have hΦ : ∀ j (hj : j ≤ m) (idx : Fin j → Fin d) (ξ : Euc d),
      Φ j idx ξ = fcL ((hg.memLp j hj idx).ofReal (K := ℂ)) ξ := fun j hj idx ξ => by
    simp only [Φ, dif_pos hj]
  have hall : ∀ᵐ ξ ∂(volume : Measure (Euc d)), ∀ j ∈ Finset.range (m + 1), ∀ idx : Fin j → Fin d,
      ‖Φ j idx ξ‖ ^ 2 =
        (2 * Real.pi) ^ (2 * j) * (∏ l, (ξ (idx l)) ^ 2) * ‖fourierL2 u ξ‖ ^ 2 :=
    (Filter.eventually_all_finset (Finset.range (m + 1))).2 fun j hj =>
      Filter.eventually_all.2 fun idx => by
        filter_upwards [hjf j (hmj j hj) idx] with ξ e
        rw [hΦ j (hmj j hj) idx ξ, e, hfL, norm_mul, mul_pow, sa12de7_norm_prod_sq]
  have hint : ∀ j ∈ Finset.range (m + 1), ∀ idx : Fin j → Fin d,
      Integrable (fun ξ => ‖Φ j idx ξ‖ ^ 2) volume := by
    intro j hj idx
    have hm := fcL_memLp ((hg.memLp j (hmj j hj) idx).ofReal (K := ℂ))
    have := (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).1 hm
    exact this.congr (Filter.Eventually.of_forall fun ξ => by simp only [hΦ j (hmj j hj) idx ξ])
  have hwae : ∀ᵐ ξ ∂(volume : Measure (Euc d)),
      (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (m : ℝ) * ‖fourierL2 u ξ‖ ^ 2 =
        ∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ) *
          ∑ idx : Fin j → Fin d, ‖Φ j idx ξ‖ ^ 2 := by
    filter_upwards [hall] with ξ hξ
    rw [sa12de7_weight]
    refine Finset.sum_congr rfl fun j hj => ?_
    congr 1
    exact Finset.sum_congr rfl fun idx _ => (hξ j hj idx).symm
  have hsum : Integrable (fun ξ : Euc d => ∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ) *
      ∑ idx : Fin j → Fin d, ‖Φ j idx ξ‖ ^ 2) volume :=
    integrable_finset_sum _ fun j hj => (integrable_finset_sum _ fun idx _ => hint j hj idx).const_mul _
  refine ⟨⟨hu2, hsum.congr (hwae.mono fun ξ hξ => hξ.symm)⟩, ?_⟩
  unfold sobolevNormSq
  rw [integral_congr_ae hwae, integral_finset_sum _ fun j hj =>
    (integrable_finset_sum _ fun idx _ => hint j hj idx).const_mul _]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [integral_const_mul, integral_finset_sum _ fun idx _ => hint j hj idx]
  congr 1
  refine Finset.sum_congr rfl fun idx _ => ?_
  have e1 : ∫ ξ, ‖Φ j idx ξ‖ ^ 2 = ∫ ξ, ‖fcL ((hg.memLp j (hmj j hj) idx).ofReal (K := ℂ)) ξ‖ ^ 2 :=
    integral_congr_ae (Filter.Eventually.of_forall fun ξ => by simp only [hΦ j (hmj j hj) idx ξ])
  rw [e1, integral_norm_sq_fcL ((hg.memLp j (hmj j hj) idx).ofReal (K := ℂ))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [Complex.norm_real, sq_abs]

/-- The norm bound: if the jet energy is at most `B²` (`0 ≤ B`), then `‖u‖_{H^m} ≤ B`. -/
theorem sa12de7_sobolevNormE_le_of_weak_jet {m : ℕ} {u : Euc d → ℝ}
    {g : (j : ℕ) → (Fin j → Fin d) → Euc d → ℝ} (hg : SA12WeakJet m u g) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ) * ∑ idx : Fin j → Fin d, ∫ x, (g j idx x) ^ 2 ≤ B ^ 2) :
    sobolevNormE (m : ℝ) u ≤ ENNReal.ofReal B := by
  obtain ⟨hmem, hnorm⟩ := sa12de7_sobolev_jet_weak hg
  unfold sobolevNormE
  rw [if_pos hmem]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [hnorm]
  exact Real.sqrt_le_iff.2 ⟨hB0, hB⟩

end HRS.MS.SA12DE7
