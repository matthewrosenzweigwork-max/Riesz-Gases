import HRS.Whole.Q09AAux3
open MeasureTheory Filter Topology
open scoped ENNReal NNReal ComplexConjugate FourierTransform ComplexInnerProductSpace ContDiff

/-!
# Packet Q09-A, part 4: Leibniz rule for chains of weak derivatives

`WD.mul` (product with a smooth compactly supported function), the coefficients `coef` of the iterated
Leibniz rule, chains `Chain` of weak derivatives, their Fourier symbols, and the construction of a chain
from the Fourier decay of `f`.
-/

noncomputable section

namespace HRS.Whole.Q09A
open HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux LineDeriv

variable {d : ℕ}

/-- the coordinate vector `e_i` -/
abbrev ei (i : Fin d) : Euc d := EuclideanSpace.single i (1 : ℝ)

/-- the partial derivative `∂_i a` of a function (pointwise `fderiv`) -/
def dirv (i : Fin d) (a : Euc d → ℂ) : Euc d → ℂ := fun x => fderiv ℝ a x (ei i)

/-- smooth with compact support -/
structure IsCc (a : Euc d → ℂ) : Prop where
  smooth : ContDiff ℝ ∞ a
  supp : HasCompactSupport a

theorem IsCc.dirv {a : Euc d → ℂ} (ha : IsCc a) (i : Fin d) : IsCc (dirv i a) := by
  refine ⟨?_, ?_⟩
  · have h1 : ContDiff ℝ ∞ (fderiv ℝ a) := ha.smooth.fderiv_right le_rfl
    exact h1.clm_apply contDiff_const
  · have h1 : HasCompactSupport (fderiv ℝ a) := ha.supp.fderiv ℝ
    exact h1.comp_left (g := fun L : Euc d →L[ℝ] ℂ => L (ei i)) (by simp)

theorem IsCc.continuous {a : Euc d → ℂ} (ha : IsCc a) : Continuous a := ha.smooth.continuous

theorem IsCc.memLp {a : Euc d → ℂ} (ha : IsCc a) : MemLp a ⊤ volume := by
  obtain ⟨C, hC⟩ := ha.supp.exists_bound_of_continuous ha.continuous
  exact memLp_top_of_bound ha.continuous.aestronglyMeasurable C (Eventually.of_forall hC)

theorem IsCc.mul_schwartz {a : Euc d → ℂ} (ha : IsCc a) (ψ : SchwartzMap (Euc d) ℂ) :
    IsCc (fun x => a x * ψ x) :=
  ⟨ha.smooth.mul ψ.smooth', ha.supp.mul_right⟩

theorem WD.memLp_left {i : Fin d} {f g : Euc d → ℂ} (h : WD i f g) : MemLp f 2 volume := h.1
theorem WD.memLp_right {i : Fin d} {f g : Euc d → ℂ} (h : WD i f g) : MemLp g 2 volume := h.2.1

theorem integrable_mul_schwartz {u : Euc d → ℂ} (hu : MemLp u 2 volume)
    (ψ : SchwartzMap (Euc d) ℂ) : Integrable (fun x => u x * ψ x) volume :=
  hu.integrable_mul (ψ.memLp 2 volume)

theorem WD.add {i : Fin d} {f g f' g' : Euc d → ℂ} (h : WD i f g) (h' : WD i f' g') :
    WD i (fun x => f x + f' x) (fun x => g x + g' x) := by
  refine ⟨h.1.add h'.1, h.2.1.add h'.2.1, fun ψ => ?_⟩
  have i1 := integrable_mul_schwartz h.2.1 ψ
  have i2 := integrable_mul_schwartz h'.2.1 ψ
  have i3 := integrable_mul_schwartz h.1 (∂_{ei i} ψ)
  have i4 := integrable_mul_schwartz h'.1 (∂_{ei i} ψ)
  simp only [add_mul]
  rw [integral_add i1 i2, integral_add i3 i4, h.2.2 ψ, h'.2.2 ψ]
  ring

theorem WD.smul {i : Fin d} {f g : Euc d → ℂ} (h : WD i f g) (c : ℂ) :
    WD i (fun x => c * f x) (fun x => c * g x) := by
  refine ⟨h.1.const_mul c, h.2.1.const_mul c, fun ψ => ?_⟩
  simp only [mul_assoc]
  rw [integral_const_mul, integral_const_mul, h.2.2 ψ]
  ring

theorem WD.zero (i : Fin d) : WD i (fun _ => (0 : ℂ)) (fun _ => (0 : ℂ)) := by
  refine ⟨MemLp.zero, MemLp.zero, fun ψ => ?_⟩
  simp

theorem WD.sum {ι : Type*} (s : Finset ι) {i : Fin d} {f g : ι → Euc d → ℂ}
    (h : ∀ k ∈ s, WD i (f k) (g k)) :
    WD i (fun x => ∑ k ∈ s, f k x) (fun x => ∑ k ∈ s, g k x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using WD.zero i
  | insert a s ha ih =>
    have h1 := h a (Finset.mem_insert_self a s)
    have h2 := ih fun k hk => h k (Finset.mem_insert_of_mem hk)
    simpa [Finset.sum_insert ha] using h1.add h2


theorem IsCc.memLp_mul {a : Euc d → ℂ} (ha : IsCc a) {f : Euc d → ℂ} (hf : MemLp f 2 volume) :
    MemLp (fun x => a x * f x) 2 volume := by
  obtain ⟨C, hC⟩ := ha.supp.exists_bound_of_continuous ha.continuous
  refine hf.of_le_mul (c := C) (ha.continuous.aestronglyMeasurable.mul hf.aestronglyMeasurable) ?_
  refine Eventually.of_forall fun x => ?_
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _)

/-- `a ψ` as a Schwartz function -/
def IsCc.mulSchwartz {a : Euc d → ℂ} (ha : IsCc a) (ψ : SchwartzMap (Euc d) ℂ) :
    SchwartzMap (Euc d) ℂ :=
  (ha.mul_schwartz ψ).supp.toSchwartzMap (ha.mul_schwartz ψ).smooth

theorem IsCc.mulSchwartz_apply {a : Euc d → ℂ} (ha : IsCc a) (ψ : SchwartzMap (Euc d) ℂ)
    (x : Euc d) : ha.mulSchwartz ψ x = a x * ψ x := rfl

theorem WD.mul {i : Fin d} {f g : Euc d → ℂ} (h : WD i f g) {a : Euc d → ℂ} (ha : IsCc a) :
    WD i (fun x => a x * f x) (fun x => a x * g x + dirv i a x * f x) := by
  have hda : IsCc (dirv i a) := ha.dirv i
  refine ⟨ha.memLp_mul h.1, (ha.memLp_mul h.2.1).add (hda.memLp_mul h.1), fun ψ => ?_⟩
  have hd1 : ∀ x, (∂_{ei i} (ha.mulSchwartz ψ)) x =
      dirv i a x * ψ x + a x * (∂_{ei i} ψ) x := by
    intro x
    rw [SchwartzMap.lineDerivOp_apply_eq_fderiv, SchwartzMap.lineDerivOp_apply_eq_fderiv]
    have h1 : (⇑(ha.mulSchwartz ψ) : Euc d → ℂ) = fun x => a x * ψ x := rfl
    rw [h1]
    have ha' : DifferentiableAt ℝ a x := (ha.smooth.differentiable (by simp)) x
    have hψ' : DifferentiableAt ℝ (⇑ψ) x := ψ.differentiableAt
    rw [fderiv_fun_mul ha' hψ']
    simp [dirv]
    ring
  have e1 := h.2.2 (ha.mulSchwartz ψ)
  simp only [IsCc.mulSchwartz_apply, hd1] at e1
  have iA : Integrable (fun x => g x * (a x * ψ x)) volume :=
    integrable_mul_schwartz h.2.1 (ha.mulSchwartz ψ)
  have iB : Integrable (fun x => f x * (dirv i a x * ψ x)) volume :=
    integrable_mul_schwartz h.1 (hda.mulSchwartz ψ)
  have iC : Integrable (fun x => f x * (a x * (∂_{ei i} ψ) x)) volume :=
    integrable_mul_schwartz h.1 (ha.mulSchwartz (∂_{ei i} ψ))
  have e2 : ∫ x, f x * (dirv i a x * ψ x + a x * (∂_{ei i} ψ) x) =
      (∫ x, f x * (dirv i a x * ψ x)) + ∫ x, f x * (a x * (∂_{ei i} ψ) x) := by
    rw [← integral_add iB iC]; congr 1; ext x; ring
  have e3 : ∫ x, (a x * g x + dirv i a x * f x) * ψ x =
      (∫ x, g x * (a x * ψ x)) + ∫ x, f x * (dirv i a x * ψ x) := by
    rw [← integral_add iA iB]; congr 1; ext x; ring
  have e4 : ∫ x, (a x * f x) * (∂_{ei i} ψ) x = ∫ x, f x * (a x * (∂_{ei i} ψ) x) := by
    congr 1; ext x; ring
  rw [e3, e4, e1, e2]
  ring


theorem IsCc.zero : IsCc (fun _ : Euc d => (0 : ℂ)) := ⟨contDiff_const, HasCompactSupport.zero⟩

theorem IsCc.add {a b : Euc d → ℂ} (ha : IsCc a) (hb : IsCc b) : IsCc (fun x => a x + b x) :=
  ⟨ha.smooth.add hb.smooth, ha.supp.add hb.supp⟩

theorem dirv_zero (i : Fin d) : dirv i (fun _ : Euc d => (0 : ℂ)) = fun _ => 0 := by
  ext x; simp [dirv]

/-- coefficients of the iterated Leibniz rule: `∂_i^j (a u) = ∑_k coef j k * ∂_i^k u` -/
def coef (i : Fin d) (a : Euc d → ℂ) : ℕ → ℕ → Euc d → ℂ
  | 0, 0 => a
  | 0, _ + 1 => fun _ => 0
  | j + 1, 0 => dirv i (coef i a j 0)
  | j + 1, k + 1 => fun x => dirv i (coef i a j (k + 1)) x + coef i a j k x

theorem coef_isCc {i : Fin d} {a : Euc d → ℂ} (ha : IsCc a) : ∀ j k, IsCc (coef i a j k)
  | 0, 0 => ha
  | 0, _ + 1 => IsCc.zero
  | j + 1, 0 => (coef_isCc ha j 0).dirv i
  | j + 1, k + 1 => ((coef_isCc ha j (k + 1)).dirv i).add (coef_isCc ha j k)

theorem coef_eq_zero (i : Fin d) (a : Euc d → ℂ) :
    ∀ j k, j < k → coef i a j k = fun _ => 0
  | 0, 0, h => absurd h (lt_irrefl _)
  | 0, _ + 1, _ => rfl
  | j + 1, 0, h => absurd h (by omega)
  | j + 1, k + 1, h => by
    have h1 : coef i a j (k + 1) = fun _ => 0 := coef_eq_zero i a j (k + 1) (by omega)
    have h2 : coef i a j k = fun _ => 0 := coef_eq_zero i a j k (by omega)
    ext x
    simp only [coef, h1, h2, dirv_zero]
    simp

/-- `u` has the chain of weak derivatives `G 0 = u, G (j+1) = ∂_i (G j)`, `j < m`. -/
def Chain (i : Fin d) (m : ℕ) (u : Euc d → ℂ) (G : ℕ → Euc d → ℂ) : Prop :=
  G 0 = u ∧ ∀ j < m, WD i (G j) (G (j + 1))

theorem Chain.mul {i : Fin d} {m : ℕ} {u : Euc d → ℂ} {G : ℕ → Euc d → ℂ} (hc : Chain i m u G)
    {a : Euc d → ℂ} (ha : IsCc a) :
    Chain i m (fun x => a x * u x)
      (fun j x => ∑ k ∈ Finset.range (j + 1), coef i a j k x * G k x) := by
  refine ⟨?_, fun j hj => ?_⟩
  · ext x; simp [coef, hc.1]
  · have hsum := WD.sum (Finset.range (j + 1)) (i := i)
      (f := fun k x => coef i a j k x * G k x)
      (g := fun k x => coef i a j k x * G (k + 1) x + dirv i (coef i a j k) x * G k x)
      (fun k hk => (hc.2 k (by have := Finset.mem_range.mp hk; omega)).mul (coef_isCc ha j k))
    have heq : (fun x => ∑ k ∈ Finset.range (j + 1),
        (coef i a j k x * G (k + 1) x + dirv i (coef i a j k) x * G k x)) =
        fun x => ∑ k ∈ Finset.range (j + 1 + 1), coef i a (j + 1) k x * G k x := by
      ext x
      rw [Finset.sum_add_distrib, Finset.sum_range_succ' _ (j + 1)]
      simp only [coef]
      rw [Finset.sum_range_succ' (fun k => dirv i (coef i a j k) x * G k x) j]
      have h0 : dirv i (coef i a j (j + 1)) x = 0 := by
        rw [coef_eq_zero i a j (j + 1) (by omega), dirv_zero]
      simp only [add_mul, Finset.sum_add_distrib]
      rw [Finset.sum_range_succ (fun k => dirv i (coef i a j (k + 1)) x * G (k + 1) x) j, h0,
        zero_mul, add_zero]
      ring
    rw [heq] at hsum
    exact hsum


theorem Chain.sum {ι : Type*} (s : Finset ι) {i : Fin d} {m : ℕ} {u : ι → Euc d → ℂ}
    {G : ι → ℕ → Euc d → ℂ} (hc : ∀ n ∈ s, Chain i m (u n) (G n)) :
    Chain i m (fun x => ∑ n ∈ s, u n x) (fun j x => ∑ n ∈ s, G n j x) := by
  refine ⟨?_, fun j hj => ?_⟩
  · ext x
    exact Finset.sum_congr rfl fun n hn => by rw [(hc n hn).1]
  · exact WD.sum s (fun n hn => (hc n hn).2 j hj)

theorem fcL_congr {u v : Euc d → ℂ} (hu : MemLp u 2 volume) (hv : MemLp v 2 volume) (e : u = v) :
    fcL hu = fcL hv := by subst e; rfl

theorem Chain.fourier {i : Fin d} {m : ℕ} {u : Euc d → ℂ} {G : ℕ → Euc d → ℂ}
    (hc : Chain i m u G) (hu : MemLp u 2 volume) :
    ∀ j ≤ m, ∃ hj : MemLp (G j) 2 volume,
      fcL hj =ᵐ[volume] fun ξ => (2 * Real.pi * Complex.I * (ξ i : ℂ)) ^ j * fcL hu ξ := by
  intro j
  induction j with
  | zero =>
    intro _
    have h0 : MemLp (G 0) 2 volume := hc.1 ▸ hu
    refine ⟨h0, Eventually.of_forall fun ξ => ?_⟩
    simp [fcL_congr h0 hu hc.1]
  | succ j ih =>
    intro hj
    obtain ⟨hGj, hfj⟩ := ih (by omega)
    have hw := hc.2 j (by omega)
    refine ⟨hw.2.1, ?_⟩
    filter_upwards [hw.fourier, hfj] with ξ h1 h2
    have e1 : fcL hw.2.1 ξ = (2 * Real.pi * Complex.I * (ξ i : ℂ)) * fcL hw.1 ξ := h1
    have e2 : fcL hw.1 ξ = fcL hGj ξ := by rw [fcL_congr hw.1 hGj rfl]
    rw [e1, e2, h2]
    ring


theorem memLp_pow_mul {f : Euc d → ℂ} (hf : MemLp f 2 volume) (i : Fin d) (m : ℕ)
    (hΞ : MemLp (fun ξ : Euc d => ((ξ i : ℂ)) ^ m * fcL hf ξ) 2 volume) :
    ∀ j ≤ m, MemLp (fun ξ : Euc d => ((ξ i : ℂ)) ^ j * fcL hf ξ) 2 volume := by
  intro j hj
  have hF := fcL_memLp hf
  refine MemLp.mono (g := fun ξ => (‖fcL hf ξ‖ + ‖((ξ i : ℂ)) ^ m * fcL hf ξ‖ : ℝ)) ?_ ?_ ?_
  · exact hF.norm.add hΞ.norm
  · have hc : Continuous fun ξ : Euc d => ((ξ i : ℂ)) ^ j := by fun_prop
    exact hc.aestronglyMeasurable.mul hF.aestronglyMeasurable
  · refine Eventually.of_forall fun ξ => ?_
    have h1 : ‖((ξ i : ℂ)) ^ j‖ ≤ 1 + ‖((ξ i : ℂ)) ^ m‖ := by
      simp only [norm_pow, Complex.norm_real, Real.norm_eq_abs]
      rcases le_or_gt |ξ i| 1 with h | h
      · have := pow_le_one₀ (abs_nonneg (ξ i)) h (n := j)
        have := pow_nonneg (abs_nonneg (ξ i)) m
        linarith
      · have := pow_le_pow_right₀ h.le hj
        have := pow_nonneg (abs_nonneg (ξ i)) 1
        linarith
    calc ‖((ξ i : ℂ)) ^ j * fcL hf ξ‖ = ‖((ξ i : ℂ)) ^ j‖ * ‖fcL hf ξ‖ := norm_mul _ _
      _ ≤ (1 + ‖((ξ i : ℂ)) ^ m‖) * ‖fcL hf ξ‖ := by gcongr
      _ = ‖fcL hf ξ‖ + ‖((ξ i : ℂ)) ^ m * fcL hf ξ‖ := by rw [norm_mul]; ring
      _ ≤ ‖(‖fcL hf ξ‖ + ‖((ξ i : ℂ)) ^ m * fcL hf ξ‖ : ℝ)‖ := by
          rw [Real.norm_eq_abs]; exact le_abs_self _

theorem exists_chain {f : Euc d → ℂ} (hf : MemLp f 2 volume) (i : Fin d) (m : ℕ)
    (hΞ : MemLp (fun ξ : Euc d => ((ξ i : ℂ)) ^ m * fcL hf ξ) 2 volume) :
    ∃ G : ℕ → Euc d → ℂ, Chain i m f G ∧ ∀ j ≤ m, ∃ hj : MemLp (G j) 2 volume,
      fcL hj =ᵐ[volume] fun ξ => (2 * Real.pi * Complex.I * (ξ i : ℂ)) ^ j * fcL hf ξ := by
  classical
  have key : ∀ j ≤ m, ∃ G : ℕ → Euc d → ℂ, G 0 = f ∧ (∀ l < j, WD i (G l) (G (l + 1))) ∧
      ∃ hj : MemLp (G j) 2 volume,
        fcL hj =ᵐ[volume] fun ξ => (2 * Real.pi * Complex.I * (ξ i : ℂ)) ^ j * fcL hf ξ := by
    intro j
    induction j with
    | zero =>
      intro _
      refine ⟨fun _ => f, rfl, fun l hl => absurd hl (by omega), hf, ?_⟩
      exact Eventually.of_forall fun ξ => by simp
    | succ j ih =>
      intro hj
      obtain ⟨G, hG0, hGw, hGj, hGf⟩ := ih (by omega)
      have hm : MemLp (fun ξ : Euc d => (ξ i : ℂ) * fcL hGj ξ) 2 volume := by
        have h1 := (memLp_pow_mul hf i m hΞ (j + 1) hj).const_mul ((2 * Real.pi * Complex.I) ^ j)
        refine h1.ae_eq ?_
        filter_upwards [hGf] with ξ hξ
        rw [hξ]; ring
      obtain ⟨g, hg, hgw, hgf⟩ := exists_WD hGj i hm
      refine ⟨Function.update G (j + 1) g, by simpa using hG0, fun l hl => ?_, ?_⟩
      · rcases Nat.lt_succ_iff_lt_or_eq.mp hl with h | h
        · have h1 : l ≠ j + 1 := by omega
          have h2 : l + 1 ≠ j + 1 := by omega
          simpa [Function.update_of_ne h1, Function.update_of_ne h2] using hGw l h
        · subst h
          have h1 : l ≠ l + 1 := by omega
          simpa [Function.update_of_ne h1] using hgw
      · have hup : MemLp (Function.update G (j + 1) g (j + 1)) 2 volume := by simpa using hg
        refine ⟨hup, ?_⟩
        have e := fcL_congr hup hg (by simp)
        filter_upwards [hgf, hGf] with ξ h1 h2
        rw [e, h1, h2]; ring
  obtain ⟨G, hG0, hGw, -⟩ := key m le_rfl
  exact ⟨G, ⟨hG0, hGw⟩, Chain.fourier ⟨hG0, hGw⟩ hf⟩

end HRS.Whole.Q09A
