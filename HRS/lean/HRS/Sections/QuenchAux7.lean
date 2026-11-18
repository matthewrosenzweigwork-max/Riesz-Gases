import HRS.Sections.QuenchAux6

/-!
# Packet QUENCH (Q27), part 7: OU-type Gaussian noise, discrete innovations

`OUNoise lam v vY P Y G`: `G` is a centred Gaussian process with the OU covariance
`E[G_t G_r] = v (e^{-λ|t-r|} - e^{-λ(t+r)})`, jointly Gaussian with and uncorrelated to a centred Gaussian `Y`,
with continuous paths and `G_0 = 0`.  Gaussianity of finite combinations, and the exact covariance of the
discrete innovations `ξ_k = G_{(k+1)h} - e^{-λh} G_{kh}` (orthogonal, variance `v(1 - e^{-2λh})`).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS

namespace Qch

section BM

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

structure OUNoise (lam v vY : ℝ) (P : Measure Ω) (Y : Ω → ℝ) (G : ℝ → Ω → ℝ) : Prop where
  proc : IsGaussianProcess (fun (p : Option ℝ≥0) ω => p.elim (Y ω) (fun t => G (t : ℝ) ω)) P
  meanY : ∫ ω, Y ω ∂P = 0
  meanG : ∀ t : ℝ≥0, ∫ ω, G (t : ℝ) ω ∂P = 0
  covYY : ∫ ω, Y ω * Y ω ∂P = vY
  covYG : ∀ t : ℝ≥0, ∫ ω, Y ω * G (t : ℝ) ω ∂P = 0
  covGG : ∀ t r : ℝ≥0, ∫ ω, G (t : ℝ) ω * G (r : ℝ) ω ∂P = v * ouK lam t r
  cont : ∀ᵐ ω ∂P, Continuous fun u : ℝ => G (max u 0) ω
  zero : ∀ᵐ ω ∂P, G 0 ω = 0

variable {lam v vY : ℝ} {Y : Ω → ℝ} {G : ℝ → Ω → ℝ}

lemma OUNoise.memLpY (hN : OUNoise lam v vY P Y G) : MemLp Y 2 P :=
  (hN.proc.hasGaussianLaw_eval none).memLp_two

lemma OUNoise.memLpG (hN : OUNoise lam v vY P Y G) (t : ℝ≥0) : MemLp (G (t : ℝ)) 2 P :=
  (hN.proc.hasGaussianLaw_eval (some t)).memLp_two

lemma OUNoise.meanG' (hN : OUNoise lam v vY P Y G) {t : ℝ} (ht : 0 ≤ t) : ∫ ω, G t ω ∂P = 0 :=
  hN.meanG ⟨t, ht⟩

lemma OUNoise.covGG' (hN : OUNoise lam v vY P Y G) {t r : ℝ} (ht : 0 ≤ t) (hr : 0 ≤ r) :
    ∫ ω, G t ω * G r ω ∂P = v * ouK lam t r :=
  hN.covGG ⟨t, ht⟩ ⟨r, hr⟩

lemma OUNoise.memLpG' (hN : OUNoise lam v vY P Y G) {t : ℝ} (ht : 0 ≤ t) : MemLp (G t) 2 P :=
  hN.memLpG ⟨t, ht⟩

/-- Finite linear combinations of `Y` and values of `G` are Gaussian. -/
lemma OUNoise.gauss_comb (hN : OUNoise lam v vY P Y G) {ι : Type*} (S : Finset ι) (τ : ι → ℝ≥0)
    (a : ι → ℝ) (c₀ : ℝ) :
    HasGaussianLaw (fun ω => c₀ * Y ω + ∑ q ∈ S, a q * G (τ q : ℝ) ω) P := by
  have h1 := (hN.proc.comp_right (Option.map τ)).smul (fun q : Option ι => q.elim c₀ a)
  have h2 := h1.hasGaussianLaw_fun_sum (I := Finset.insertNone S)
  refine h2.congr (Eventually.of_forall fun ω => ?_)
  simp only [Finset.sum_insertNone, Function.comp_apply, Option.map_none, Option.map_some,
    Option.elim_none, Option.elim_some, smul_eq_mul]

end BM

/-! ### The grid -/

lemma ouK_grid {lam h : ℝ} (hh : 0 ≤ h) (a b : ℕ) :
    ouK lam ((a : ℝ) * h) ((b : ℝ) * h) =
      Real.exp (-lam * h) ^ (max a b - min a b) - Real.exp (-lam * h) ^ (a + b) := by
  unfold ouK
  have e1 : Real.exp (-lam * h) ^ (a + b) = Real.exp (-lam * ((a : ℝ) * h + (b : ℝ) * h)) := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [e1]
  congr 1
  rw [← Real.exp_nat_mul]
  congr 1
  rcases le_total a b with hab | hab
  · rw [max_eq_right hab, min_eq_left hab, abs_of_nonpos (by
      have : (a : ℝ) ≤ b := by exact_mod_cast hab
      nlinarith)]
    rw [Nat.cast_sub hab]; ring
  · rw [max_eq_left hab, min_eq_right hab, abs_of_nonneg (by
      have : (b : ℝ) ≤ a := by exact_mod_cast hab
      nlinarith)]
    rw [Nat.cast_sub hab]; ring

lemma integral_AmBmCpD {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} (A B C D : Ω → ℝ)
    (hA : Integrable A P) (hB : Integrable B P) (hC : Integrable C P) (hD : Integrable D P) :
    ∫ ω, (A ω - B ω - C ω + D ω) ∂P = ∫ ω, A ω ∂P - ∫ ω, B ω ∂P - ∫ ω, C ω ∂P + ∫ ω, D ω ∂P := by
  have h1 : Integrable (fun ω => A ω - B ω) P := hA.sub hB
  have h2 : Integrable (fun ω => A ω - B ω - C ω) P := h1.sub hC
  rw [integral_add (f := fun ω => A ω - B ω - C ω) (g := D) h2 hD,
    integral_sub (f := fun ω => A ω - B ω) (g := C) h1 hC,
    integral_sub (f := A) (g := B) hA hB]

/-- The discrete innovation `ξ_k = G_{(k+1)h} - x G_{kh}`. -/
def xi {Ω : Type*} (G : ℝ → Ω → ℝ) (h x : ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  G (((k : ℝ) + 1) * h) ω - x * G ((k : ℝ) * h) ω

section Innov

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {lam v vY : ℝ} {Y : Ω → ℝ} {G : ℝ → Ω → ℝ}

lemma OUNoise.memLp_xi (hN : OUNoise lam v vY P Y G) {h : ℝ} (hh : 0 ≤ h) (x : ℝ) (k : ℕ) :
    MemLp (xi G h x k) 2 P := by
  have h1 := hN.memLpG' (t := ((k : ℝ) + 1) * h) (by positivity)
  have h2 := hN.memLpG' (t := (k : ℝ) * h) (by positivity)
  exact h1.sub (h2.const_mul x)

lemma OUNoise.integral_xi (hN : OUNoise lam v vY P Y G) {h : ℝ} (hh : 0 ≤ h) (x : ℝ) (k : ℕ) :
    ∫ ω, xi G h x k ω ∂P = 0 := by
  have h1 := hN.memLpG' (t := ((k : ℝ) + 1) * h) (by positivity)
  have h2 := hN.memLpG' (t := (k : ℝ) * h) (by positivity)
  unfold xi
  rw [integral_sub (h1.integrable one_le_two) ((h2.const_mul x).integrable one_le_two),
    integral_const_mul, hN.meanG' (by positivity), hN.meanG' (by positivity)]
  simp

/-- `E[ξ_kξ_l] = δ_{kl} v (1 - x²)` on the grid `h`, `x = e^{-λh}`. -/
lemma OUNoise.integral_xi_mul (hN : OUNoise lam v vY P Y G) {h : ℝ} (hh : 0 ≤ h) (k l : ℕ) :
    ∫ ω, xi G h (Real.exp (-lam * h)) k ω * xi G h (Real.exp (-lam * h)) l ω ∂P =
      if k = l then v * (1 - Real.exp (-lam * h) ^ 2) else 0 := by
  set x := Real.exp (-lam * h) with hx
  have hint : ∀ a b : ℕ, Integrable (fun ω => G ((a : ℝ) * h) ω * G ((b : ℝ) * h) ω) P := fun a b =>
    (hN.memLpG' (t := (a : ℝ) * h) (by positivity)).integrable_mul
      (hN.memLpG' (t := (b : ℝ) * h) (by positivity))
  have hc : ∀ a b : ℕ, ∫ ω, G ((a : ℝ) * h) ω * G ((b : ℝ) * h) ω ∂P =
      v * (x ^ (max a b - min a b) - x ^ (a + b)) := fun a b => by
    rw [hN.covGG' (by positivity) (by positivity), ouK_grid hh]
  have e : ∀ ω, xi G h x k ω * xi G h x l ω =
      G (((k + 1 : ℕ) : ℝ) * h) ω * G (((l + 1 : ℕ) : ℝ) * h) ω
      - x * (G (((k + 1 : ℕ) : ℝ) * h) ω * G ((l : ℝ) * h) ω)
      - x * (G ((k : ℝ) * h) ω * G (((l + 1 : ℕ) : ℝ) * h) ω)
      + x ^ 2 * (G ((k : ℝ) * h) ω * G ((l : ℝ) * h) ω) := by
    intro ω; unfold xi; push_cast; ring
  simp_rw [e]
  rw [integral_AmBmCpD _ _ _ _ (hint (k + 1) (l + 1)) ((hint (k + 1) l).const_mul x)
      ((hint k (l + 1)).const_mul x) ((hint k l).const_mul (x ^ 2)),
    integral_const_mul, integral_const_mul, integral_const_mul, hc, hc, hc, hc]
  rcases lt_trichotomy k l with hkl | hkl | hkl
  · obtain ⟨d, rfl⟩ : ∃ d, l = k + 1 + d := ⟨l - k - 1, by omega⟩
    have h1 : max (k + 1) (k + 1 + d + 1) - min (k + 1) (k + 1 + d + 1) = d + 1 := by omega
    have h2 : max (k + 1) (k + 1 + d) - min (k + 1) (k + 1 + d) = d := by omega
    have h3 : max k (k + 1 + d + 1) - min k (k + 1 + d + 1) = d + 2 := by omega
    have h4 : max k (k + 1 + d) - min k (k + 1 + d) = d + 1 := by omega
    rw [h1, h2, h3, h4, if_neg (by omega)]
    ring_nf
  · subst hkl
    rw [if_pos rfl]
    have h1 : max (k + 1) (k + 1) - min (k + 1) (k + 1) = 0 := by omega
    have h2 : max (k + 1) k - min (k + 1) k = 1 := by omega
    have h3 : max k (k + 1) - min k (k + 1) = 1 := by omega
    have h4 : max k k - min k k = 0 := by omega
    rw [h1, h2, h3, h4]
    ring_nf
  · obtain ⟨d, rfl⟩ : ∃ d, k = l + 1 + d := ⟨k - l - 1, by omega⟩
    have h1 : max (l + 1 + d + 1) (l + 1) - min (l + 1 + d + 1) (l + 1) = d + 1 := by omega
    have h2 : max (l + 1 + d + 1) l - min (l + 1 + d + 1) l = d + 2 := by omega
    have h3 : max (l + 1 + d) (l + 1) - min (l + 1 + d) (l + 1) = d := by omega
    have h4 : max (l + 1 + d) l - min (l + 1 + d) l = d + 1 := by omega
    rw [h1, h2, h3, h4, if_neg (by omega)]
    ring_nf

end Innov

end Qch

end HRS
