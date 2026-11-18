import HRS.MS.MovAdjAux26
import HRS.MS.GradSmTie
import HRS.MS.Mov63Tie
import HRS.MS.MovOpAux5
import HRS.MS.MovLinTie
import HRS.MS.MovOscAux3
import HRS.MS.MovOscAux5
import HRS.MS.S67NlBD03

/-!
# S6.7 nonlinear breakdown, packet 09: non-Schwartz weighted integer norm converse

`s67bd_integer_converse`: induction on `n`.  Level `n + 1` is obtained from level `n` applied to `u`,
`x_i u` and `D_i u` (packet 03).  Jets of `D_i u` are jets of `u` with an appended index
(`s67bd_jet_D`); jets of `x_i u` obey the one-direction Leibniz rule (`s67bd_jet_xmul`), proved by
induction on the order through the same appending identity.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.BreakdownS67

open HRS HRS.Whole HRS.MS.MovLin HRS.MS.MovOsc HRS.MS.MovAdj
open HRS.MS.Mov63 HRS.MS.MovForce HRS.MS.MovC2
open HRS.MS.PoisFlow HRS.MS.PoisSg HRS.MS.PoisKolm HRS.MS.PoisHigh

variable {d : ℕ} {s β q : ℝ} {ρ₀ : Euc d → ℝ}

def s67bd_jet (k : ℕ) (γ : Fin k → Fin d) (u : Euc d → ℝ) (x : Euc d) : ℝ :=
  iteratedFDeriv ℝ k u x (fun l => EuclideanSpace.single (γ l) 1)

def s67bd_xpow (a : MultiIndex d) (x : Euc d) : ℝ := ∏ i, x i ^ a i

/-! ### Weighted `L²` bounds: closure properties -/

theorem s67bd_good_add {f g : Euc d → ℝ} {A B : ℝ}
    (hf : MemLp f 2 (volume : Measure (Euc d)) ∧ (eLpNorm f 2 (volume : Measure (Euc d))).toReal ≤ A)
    (hg : MemLp g 2 (volume : Measure (Euc d)) ∧ (eLpNorm g 2 (volume : Measure (Euc d))).toReal ≤ B) :
    MemLp (fun x => f x + g x) 2 (volume : Measure (Euc d)) ∧
      (eLpNorm (fun x => f x + g x) 2 (volume : Measure (Euc d))).toReal ≤ A + B := by
  refine ⟨hf.1.add hg.1, ?_⟩
  have h1 : eLpNorm (fun x => f x + g x) 2 (volume : Measure (Euc d)) ≤
      eLpNorm f 2 volume + eLpNorm g 2 volume :=
    eLpNorm_add_le (by norm_num)
  have hfin : eLpNorm f 2 (volume : Measure (Euc d)) + eLpNorm g 2 volume ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨hf.1.eLpNorm_ne_top, hg.1.eLpNorm_ne_top⟩
  calc (eLpNorm (fun x => f x + g x) 2 (volume : Measure (Euc d))).toReal
      ≤ (eLpNorm f 2 (volume : Measure (Euc d)) + eLpNorm g 2 volume).toReal :=
        ENNReal.toReal_mono hfin h1
    _ = (eLpNorm f 2 (volume : Measure (Euc d))).toReal + (eLpNorm g 2 (volume : Measure (Euc d))).toReal :=
        ENNReal.toReal_add hf.1.eLpNorm_ne_top hg.1.eLpNorm_ne_top
    _ ≤ A + B := add_le_add hf.2 hg.2

theorem s67bd_good_mul {f : Euc d → ℝ} {A : ℝ} (c : ℝ)
    (hf : MemLp f 2 (volume : Measure (Euc d)) ∧ (eLpNorm f 2 (volume : Measure (Euc d))).toReal ≤ A) :
    MemLp (fun x => c * f x) 2 (volume : Measure (Euc d)) ∧
      (eLpNorm (fun x => c * f x) 2 (volume : Measure (Euc d))).toReal ≤ |c| * A := by
  refine ⟨hf.1.const_mul c, ?_⟩
  have h1 : eLpNorm (fun x => c * f x) 2 (volume : Measure (Euc d)) =
      ‖c‖ₑ * eLpNorm f 2 (volume : Measure (Euc d)) := by
    have := eLpNorm_const_smul (p := (2 : ℝ≥0∞)) (μ := (volume : Measure (Euc d))) c f
    have e : (fun x => c * f x) = c • f := by funext x; simp
    rw [e]; simpa using this
  rw [h1, ENNReal.toReal_mul, toReal_enorm, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left hf.2 (abs_nonneg _)

theorem s67bd_good_mono {f : Euc d → ℝ} {A A' : ℝ} (h : A ≤ A')
    (hf : MemLp f 2 (volume : Measure (Euc d)) ∧ (eLpNorm f 2 (volume : Measure (Euc d))).toReal ≤ A) :
    MemLp f 2 (volume : Measure (Euc d)) ∧ (eLpNorm f 2 (volume : Measure (Euc d))).toReal ≤ A' :=
  ⟨hf.1, hf.2.trans h⟩

theorem s67bd_good_list {ι : Type*} (L : List ι) (f : ι → Euc d → ℝ) {B : ℝ}
    (hf : ∀ p ∈ L, MemLp (f p) 2 (volume : Measure (Euc d)) ∧
      (eLpNorm (f p) 2 (volume : Measure (Euc d))).toReal ≤ B) :
    MemLp (fun x => (L.map (fun p => f p x)).sum) 2 (volume : Measure (Euc d)) ∧
      (eLpNorm (fun x => (L.map (fun p => f p x)).sum) 2 (volume : Measure (Euc d))).toReal ≤
        L.length * B := by
  induction L with
  | nil =>
    simp only [List.map_nil, List.sum_nil, List.length_nil, Nat.cast_zero, zero_mul]
    simp
  | cons a L ih =>
    have h1 := ih (fun p hp => hf p (List.mem_cons_of_mem a hp))
    have h2 := s67bd_good_add (hf a List.mem_cons_self) h1
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    refine ⟨h2.1, h2.2.trans (le_of_eq ?_)⟩
    ring

/-! ### Jets -/

/-- Jets of the coordinate derivative are jets with an appended index. -/
theorem s67bd_jet_D (k : ℕ) (i : Fin d) (u : Euc d → ℝ)
    (hu : ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞) u) (γ : Fin k → Fin d) (x : Euc d) :
    s67bd_jet k γ (s67bd_D i u) x = s67bd_jet (k + 1) (Fin.snoc γ i) u x := by
  have hdu : ContDiff ℝ (k : WithTop ℕ∞) (fderiv ℝ u) := hu.fderiv_right (by norm_cast)
  unfold s67bd_jet s67bd_D
  rw [iteratedFDeriv_succ_apply_right]
  have h : iteratedFDeriv ℝ k (fun y => fderiv ℝ u y (EuclideanSpace.single i (1 : ℝ))) x =
      (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i (1 : ℝ) : Euc d)).compContinuousMultilinearMap
        (iteratedFDeriv ℝ k (fderiv ℝ u) x) :=
    ContinuousLinearMap.iteratedFDeriv_comp_left
      (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i (1 : ℝ) : Euc d)) hdu.contDiffAt le_rfl
  rw [h]
  have hinit : (Fin.init fun l : Fin (k + 1) =>
        (EuclideanSpace.single (Fin.snoc (α := fun _ => Fin d) γ i l) (1 : ℝ) : Euc d)) =
      fun l => EuclideanSpace.single (γ l) 1 := by
    funext l; simp [Fin.init]
  simp [hinit, Fin.snoc_last]

/-- The same, peeling off the last index. -/
theorem s67bd_jet_succ (m : ℕ) (γ : Fin (m + 1) → Fin d) (f : Euc d → ℝ)
    (hf : ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) f) (x : Euc d) :
    s67bd_jet (m + 1) γ f x = s67bd_jet m (Fin.init γ) (s67bd_D (γ (Fin.last m)) f) x := by
  rw [s67bd_jet_D m (γ (Fin.last m)) f hf (Fin.init γ) x, Fin.snoc_init_self]

theorem s67bd_jet_zero (γ : Fin 0 → Fin d) (f : Euc d → ℝ) (x : Euc d) :
    s67bd_jet 0 γ f x = f x := by
  simp [s67bd_jet]

theorem s67bd_jet_lin (k : ℕ) (γ : Fin k → Fin d) (c : ℝ) {f g : Euc d → ℝ}
    (hf : ContDiff ℝ (k : WithTop ℕ∞) f) (hg : ContDiff ℝ (k : WithTop ℕ∞) g) (x : Euc d) :
    s67bd_jet k γ (fun y => c * f y + g y) x = c * s67bd_jet k γ f x + s67bd_jet k γ g x := by
  have e1 : (fun y => c * f y + g y) = (c • f) + g := by funext y; simp
  have hcf : ContDiff ℝ (k : WithTop ℕ∞) (c • f) := hf.const_smul c
  unfold s67bd_jet
  rw [e1, iteratedFDeriv_add_apply hcf.contDiffAt hg.contDiffAt,
    iteratedFDeriv_const_smul_apply hf.contDiffAt]
  simp

theorem s67bd_D_xmul (i j : Fin d) {w : Euc d → ℝ} (hw : Differentiable ℝ w) (y : Euc d) :
    s67bd_D j (fun y => y i * w y) y =
      (if j = i then 1 else 0) * w y + y i * s67bd_D j w y := by
  have h : HasFDerivAt (fun y : Euc d => y i * w y)
      ((y i) • fderiv ℝ w y + (w y) • (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ)) y :=
    (EuclideanSpace.proj (𝕜 := ℝ) i : Euc d →L[ℝ] ℝ).hasFDerivAt.mul (hw y).hasFDerivAt
  unfold s67bd_D
  rw [h.fderiv]
  simp [eq_comm]
  ring

/-- One-direction Leibniz rule for jets of `x_i w`. -/
theorem s67bd_jet_xmul (i : Fin d) : ∀ (m : ℕ) (γ : Fin (m + 1) → Fin d),
    ∃ L : List (ℝ × (Fin m → Fin d)), L.length ≤ m + 1 ∧ (∀ p ∈ L, 0 ≤ p.1 ∧ p.1 ≤ 1) ∧
      ∀ w : Euc d → ℝ, ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) w → ∀ x : Euc d,
        s67bd_jet (m + 1) γ (fun y => y i * w y) x = x i * s67bd_jet (m + 1) γ w x +
          (L.map (fun p => p.1 * s67bd_jet m p.2 w x)).sum := by
  have hcd : ∀ (n : ℕ) (w : Euc d → ℝ), ContDiff ℝ (n : WithTop ℕ∞) w →
      ContDiff ℝ (n : WithTop ℕ∞) (fun y : Euc d => y i * w y) := fun n w hw =>
    ((EuclideanSpace.proj (𝕜 := ℝ) i : Euc d →L[ℝ] ℝ).contDiff.mul hw)
  have hcdD : ∀ (n : ℕ) (j : Fin d) (w : Euc d → ℝ), ContDiff ℝ ((n + 1 : ℕ) : WithTop ℕ∞) w →
      ContDiff ℝ (n : WithTop ℕ∞) (s67bd_D j w) := fun n j w hw =>
    (hw.fderiv_right (by norm_cast)).clm_apply contDiff_const
  intro m
  induction m with
  | zero =>
    intro γ
    refine ⟨[((if γ 0 = i then 1 else 0), fun l => l.elim0)], by simp, ?_, ?_⟩
    · intro p hp
      simp only [List.mem_singleton] at hp
      subst hp
      split_ifs <;> simp
    · intro w hw x
      have hxw := hcd 1 w (by simpa using hw)
      rw [s67bd_jet_succ 0 γ _ (by simpa using hxw) x, s67bd_jet_succ 0 γ w hw x,
        s67bd_jet_zero, s67bd_jet_zero, s67bd_D_xmul i _ (hw.differentiable (by norm_num)) x]
      simp [s67bd_jet_zero]
      ring
  | succ m ih =>
    intro γ
    obtain ⟨L0, hlen, hcoef, hL0⟩ := ih (Fin.init γ)
    obtain ⟨j, hj⟩ : ∃ j, j = γ (Fin.last (m + 1)) := ⟨_, rfl⟩
    refine ⟨((if j = i then 1 else 0), Fin.init γ) ::
      L0.map (fun p => (p.1, Fin.snoc (α := fun _ => Fin d) p.2 j)), ?_, ?_, ?_⟩
    · simp only [List.length_cons, List.length_map]
      omega
    · intro p hp
      simp only [List.mem_cons, List.mem_map] at hp
      rcases hp with rfl | ⟨p', hp', rfl⟩
      · split_ifs <;> simp
      · exact hcoef p' hp'
    · intro w hw x
      have hw1 : ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) w := hw.of_le (by norm_cast; omega)
      have hxw := hcd (m + 1 + 1) w hw
      have hDw := hcdD (m + 1) j w hw
      rw [s67bd_jet_succ (m + 1) γ _ hxw x, ← hj]
      have hD : s67bd_D j (fun y => y i * w y) =
          fun y => (if j = i then 1 else 0) * w y + y i * s67bd_D j w y :=
        funext (s67bd_D_xmul i j (hw.differentiable (by norm_cast)))
      rw [hD, s67bd_jet_lin (m + 1) (Fin.init γ) _ hw1 (hcd _ _ hDw) x, hL0 (s67bd_D j w) hDw x]
      rw [s67bd_jet_succ (m + 1) γ w hw x, ← hj]
      have hterm : (L0.map (fun p => p.1 * s67bd_jet m p.2 (s67bd_D j w) x)) =
          L0.map (fun p => p.1 * s67bd_jet (m + 1) (Fin.snoc (α := fun _ => Fin d) p.2 j) w x) :=
        List.map_congr_left fun p _ => by rw [s67bd_jet_D m j w hw1 p.2 x]
      simp only [List.map_cons, List.map_map, List.sum_cons, Function.comp_def]
      rw [hterm]
      ring

/-! ### Weights -/

theorem s67bd_xpow_add (a : MultiIndex d) (i : Fin d) (x : Euc d) :
    s67bd_xpow (a + Pi.single i 1) x = s67bd_xpow a x * x i := by
  unfold s67bd_xpow
  simp only [Pi.add_apply, pow_add, Finset.prod_mul_distrib]
  congr 1
  rw [Finset.prod_eq_single i]
  · simp
  · intro j _ hj
    simp [Pi.single_eq_of_ne hj]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem s67bd_degree_add (a : MultiIndex d) (i : Fin d) :
    MultiIndex.degree (a + Pi.single i 1) = MultiIndex.degree a + 1 := by
  unfold MultiIndex.degree
  simp [Finset.sum_add_distrib, Finset.sum_pi_single']

/-! ### Closure of the weighted-jet hypothesis -/

theorem s67bd_hyp_xmul (n : ℕ) (i : Fin d) (u : Euc d → ℝ)
    (hu : ContDiff ℝ ((n + 1 : ℕ) : WithTop ℕ∞) u) (A : ℝ) (hA : 0 ≤ A)
    (h : ∀ (k : ℕ) (a : MultiIndex d) (γ : Fin k → Fin d), MultiIndex.degree a + k ≤ n + 1 →
      MemLp (fun x => s67bd_xpow a x * s67bd_jet k γ u x) 2 (volume : Measure (Euc d)) ∧
        (eLpNorm (fun x => s67bd_xpow a x * s67bd_jet k γ u x) 2
          (volume : Measure (Euc d))).toReal ≤ A) :
    ∀ (k : ℕ) (a : MultiIndex d) (γ : Fin k → Fin d), MultiIndex.degree a + k ≤ n →
      MemLp (fun x => s67bd_xpow a x * s67bd_jet k γ (fun y => y i * u y) x) 2
        (volume : Measure (Euc d)) ∧
        (eLpNorm (fun x => s67bd_xpow a x * s67bd_jet k γ (fun y => y i * u y) x) 2
          (volume : Measure (Euc d))).toReal ≤ ((n : ℝ) + 2) * A := by
  intro k a γ hk
  have hn2 : (0 : ℝ) ≤ (n : ℝ) + 2 := by positivity
  have hAA : A ≤ ((n : ℝ) + 2) * A := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
  cases k with
  | zero =>
    have h1 := h 0 (a + Pi.single i 1) γ (by rw [s67bd_degree_add]; omega)
    have e : (fun x => s67bd_xpow a x * s67bd_jet 0 γ (fun y => y i * u y) x) =
        fun x => s67bd_xpow (a + Pi.single i 1) x * s67bd_jet 0 γ u x := by
      funext x
      rw [s67bd_jet_zero, s67bd_jet_zero, s67bd_xpow_add]
      ring
    rw [e]
    exact s67bd_good_mono hAA h1
  | succ m =>
    obtain ⟨L, hlen, hc, hL⟩ := s67bd_jet_xmul i m γ
    have hu1 : ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) u := hu.of_le (by norm_cast; omega)
    have e : (fun x => s67bd_xpow a x * s67bd_jet (m + 1) γ (fun y => y i * u y) x) =
        fun x => s67bd_xpow (a + Pi.single i 1) x * s67bd_jet (m + 1) γ u x +
          (L.map (fun p => p.1 * (s67bd_xpow a x * s67bd_jet m p.2 u x))).sum := by
      funext x
      rw [hL u hu1 x, mul_add, s67bd_xpow_add, ← List.sum_map_mul_left]
      simp only [mul_comm, mul_left_comm]
      ring_nf
    rw [e]
    have h1 := h (m + 1) (a + Pi.single i 1) γ (by rw [s67bd_degree_add]; omega)
    have h2 := s67bd_good_list L (fun p x => p.1 * (s67bd_xpow a x * s67bd_jet m p.2 u x))
      (B := A) (fun p hp => by
        have := s67bd_good_mul (A := A) p.1 (h m a p.2 (by omega))
        refine s67bd_good_mono ?_ this
        have := hc p hp
        rw [abs_of_nonneg this.1]
        nlinarith [this.2])
    have h3 := s67bd_good_add h1 h2
    refine ⟨h3.1, h3.2.trans ?_⟩
    have hlen' : (L.length : ℝ) ≤ n := by exact_mod_cast (by omega : L.length ≤ n)
    nlinarith [mul_le_mul_of_nonneg_right hlen' hA]

theorem s67bd_hyp_D (n : ℕ) (i : Fin d) (u : Euc d → ℝ)
    (hu : ContDiff ℝ ((n + 1 : ℕ) : WithTop ℕ∞) u) (A : ℝ)
    (h : ∀ (k : ℕ) (a : MultiIndex d) (γ : Fin k → Fin d), MultiIndex.degree a + k ≤ n + 1 →
      MemLp (fun x => s67bd_xpow a x * s67bd_jet k γ u x) 2 (volume : Measure (Euc d)) ∧
        (eLpNorm (fun x => s67bd_xpow a x * s67bd_jet k γ u x) 2
          (volume : Measure (Euc d))).toReal ≤ A) :
    ∀ (k : ℕ) (a : MultiIndex d) (γ : Fin k → Fin d), MultiIndex.degree a + k ≤ n →
      MemLp (fun x => s67bd_xpow a x * s67bd_jet k γ (s67bd_D i u) x) 2
        (volume : Measure (Euc d)) ∧
        (eLpNorm (fun x => s67bd_xpow a x * s67bd_jet k γ (s67bd_D i u) x) 2
          (volume : Measure (Euc d))).toReal ≤ A := by
  intro k a γ hk
  have hu1 : ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞) u := hu.of_le (by norm_cast; omega)
  have e : (fun x => s67bd_xpow a x * s67bd_jet k γ (s67bd_D i u) x) =
      fun x => s67bd_xpow a x * s67bd_jet (k + 1) (Fin.snoc (α := fun _ => Fin d) γ i) u x := by
    funext x
    rw [s67bd_jet_D k i u hu1 γ x]
  rw [e]
  exact h (k + 1) a _ (by omega)

theorem s67bd_integer_converse (d n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : Euc d → ℝ) (A : ℝ), 0 ≤ A →
      ContDiff ℝ (n : WithTop ℕ∞) u →
      (∀ (k : ℕ) (a : MultiIndex d) (γ : Fin k → Fin d),
        MultiIndex.degree a + k ≤ n →
        MemLp (fun x => s67bd_xpow a x * s67bd_jet k γ u x) 2 volume ∧
        (eLpNorm (fun x => s67bd_xpow a x * s67bd_jet k γ u x) 2 volume).toReal ≤ A) →
      MemOsc (n : ℝ) u ∧ oscNorm (n : ℝ) u ≤ C * A := by
  induction n with
  | zero =>
    refine ⟨1, zero_le_one, fun u A hA hu h => ?_⟩
    have h0 := h 0 0 (fun l => l.elim0) (by simp [MultiIndex.degree])
    have e : (fun x => s67bd_xpow (0 : MultiIndex d) x * s67bd_jet 0 (fun l => l.elim0) u x) = u := by
      funext x
      simp [s67bd_xpow, s67bd_jet_zero]
    rw [e] at h0
    have hmem : MemOsc ((0 : ℕ) : ℝ) u := by
      refine ⟨h0.1, ?_⟩
      simpa using (hermite_parseval_aux u h0.1).1
    refine ⟨hmem, ?_⟩
    have h1 := mova2_eLpNorm_two h0.1
    have h2 : oscNorm 0 u = (eLpNorm u 2 (volume : Measure (Euc d))).toReal := by
      rw [h1, ENNReal.toReal_ofReal (by unfold oscNorm; exact Real.sqrt_nonneg _)]
    simpa [h2] using h0.2
  | succ n ih =>
    obtain ⟨Cn, hCn, hIH⟩ := ih
    obtain ⟨C3, hC3, h3⟩ := s67bd_ladder_converse d (n : ℝ)
    refine ⟨C3 * (Cn + d * (Cn * ((n : ℝ) + 2) + Cn)), by positivity, fun u A hA hu h => ?_⟩
    have hun : ContDiff ℝ (n : WithTop ℕ∞) u := hu.of_le (by norm_cast; omega)
    have hu1 : ContDiff ℝ 1 u := hu.of_le (by norm_cast; omega)
    have hyp0 : ∀ (k : ℕ) (a : MultiIndex d) (γ : Fin k → Fin d), MultiIndex.degree a + k ≤ n →
        MemLp (fun x => s67bd_xpow a x * s67bd_jet k γ u x) 2 volume ∧
        (eLpNorm (fun x => s67bd_xpow a x * s67bd_jet k γ u x) 2 volume).toReal ≤ A :=
      fun k a γ hk => h k a γ (by omega)
    obtain ⟨hm0, hn0⟩ := hIH u A hA hun hyp0
    have hX : ∀ i : Fin d, MemOsc (n : ℝ) (fun x => x i * u x) ∧
        oscNorm (n : ℝ) (fun x => x i * u x) ≤ Cn * (((n : ℝ) + 2) * A) := by
      intro i
      refine hIH _ _ (by positivity) ?_ (s67bd_hyp_xmul n i u hu A hA h)
      exact ((EuclideanSpace.proj (𝕜 := ℝ) i : Euc d →L[ℝ] ℝ).contDiff.mul hun)
    have hDD : ∀ i : Fin d, MemOsc (n : ℝ) (s67bd_D i u) ∧
        oscNorm (n : ℝ) (s67bd_D i u) ≤ Cn * A := by
      intro i
      refine hIH _ _ hA ?_ (s67bd_hyp_D n i u hu A h)
      exact (hu.fderiv_right (by norm_cast)).clm_apply contDiff_const
    obtain ⟨hm3, hn3⟩ := h3 u hu1 hm0 (fun i => (hX i).1) (fun i => (hDD i).1)
    push_cast
    refine ⟨hm3, hn3.trans ?_⟩
    have hs : ∑ i : Fin d, (oscNorm (n : ℝ) (fun x => x i * u x) + oscNorm (n : ℝ) (s67bd_D i u)) ≤
        ∑ _i : Fin d, (Cn * (((n : ℝ) + 2) * A) + Cn * A) :=
      Finset.sum_le_sum fun i _ => add_le_add (hX i).2 (hDD i).2
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
    have hb : oscNorm (n : ℝ) u + ∑ i : Fin d, (oscNorm (n : ℝ) (fun x => x i * u x) +
        oscNorm (n : ℝ) (s67bd_D i u)) ≤ (Cn + d * (Cn * ((n : ℝ) + 2) + Cn)) * A := by
      nlinarith [hs, hn0]
    calc C3 * (oscNorm (n : ℝ) u + ∑ i : Fin d, (oscNorm (n : ℝ) (fun x => x i * u x) +
          oscNorm (n : ℝ) (s67bd_D i u))) ≤ C3 * ((Cn + d * (Cn * ((n : ℝ) + 2) + Cn)) * A) :=
          mul_le_mul_of_nonneg_left hb hC3
      _ = _ := by ring

end HRS.MS.BreakdownS67
