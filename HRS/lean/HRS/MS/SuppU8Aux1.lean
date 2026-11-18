import Mathlib

/-!
# Worker U8 aux 1: iterated forward differences

`u8_fd L u` is the iterated forward difference of `u` along the list `L` of steps (head first).
Algebraic rules (linearity, shifts, exponentials, integrals), the mixed Taylor-type bound
`‖fd L u x‖ ≤ 2^(|L|-ℓ) r^ℓ sup ‖D^ℓ u‖`, the crude bound by shifted values, and the adjoint
identity under the integral.
-/

noncomputable section

open MeasureTheory Metric Set

namespace HRS.U8

section Algebra

variable {V E : Type*} [AddCommGroup V] [AddCommGroup E]

/-- Iterated forward differences, head step first. -/
def u8_fd : List V → (V → E) → V → E
  | [], u => u
  | h :: hs, u => u8_fd hs (fun x => u (x + h) - u x)

theorem u8_fd_nil (u : V → E) : u8_fd [] u = u := rfl

theorem u8_fd_cons (h : V) (hs : List V) (u : V → E) :
    u8_fd (h :: hs) u = u8_fd hs (fun x => u (x + h) - u x) := rfl

theorem u8_fd_sub (L : List V) (u w : V → E) :
    u8_fd L (fun x => u x - w x) = fun x => u8_fd L u x - u8_fd L w x := by
  induction L generalizing u w with
  | nil => rfl
  | cons h hs ih =>
    rw [u8_fd_cons, u8_fd_cons, u8_fd_cons]
    have : (fun x => (u (x + h) - w (x + h)) - (u x - w x)) =
        fun x => (u (x + h) - u x) - (w (x + h) - w x) := by
      funext x; abel
    rw [this, ih]

theorem u8_fd_add (L : List V) (u w : V → E) :
    u8_fd L (fun x => u x + w x) = fun x => u8_fd L u x + u8_fd L w x := by
  induction L generalizing u w with
  | nil => rfl
  | cons h hs ih =>
    rw [u8_fd_cons, u8_fd_cons, u8_fd_cons]
    have : (fun x => (u (x + h) + w (x + h)) - (u x + w x)) =
        fun x => (u (x + h) - u x) + (w (x + h) - w x) := by
      funext x; abel
    rw [this, ih]

theorem u8_fd_smul {R : Type*} [Semiring R] [Module R E] (L : List V) (c : R) (u : V → E) :
    u8_fd L (fun x => c • u x) = fun x => c • u8_fd L u x := by
  induction L generalizing u with
  | nil => rfl
  | cons h hs ih =>
    rw [u8_fd_cons, u8_fd_cons]
    have : (fun x => c • u (x + h) - c • u x) = fun x => c • (u (x + h) - u x) := by
      funext x; rw [smul_sub]
    rw [this, ih]

theorem u8_fd_shift (L : List V) (u : V → E) (a : V) :
    u8_fd L (fun x => u (x + a)) = fun x => u8_fd L u (x + a) := by
  induction L generalizing u with
  | nil => rfl
  | cons h hs ih =>
    rw [u8_fd_cons, u8_fd_cons]
    have e : (fun x => (fun z => u (z + a)) (x + h) - (fun z => u (z + a)) x) =
        fun x => (fun x => u (x + h) - u x) (x + a) := by
      funext x; simp only [add_right_comm x h a]
    rw [e]
    exact ih (fun x => u (x + h) - u x)

theorem u8_fd_comm (L : List V) (u : V → E) (a : V) :
    u8_fd L (fun x => u (x + a) - u x) = fun x => u8_fd L u (x + a) - u8_fd L u x := by
  rw [u8_fd_sub, u8_fd_shift]

/-- Exponentials: `u (x + h) = χ h * u x` gives a multiplicative action. -/
theorem u8_fd_exp (L : List V) (χ : V → ℂ) (u : V → ℂ) (hu : ∀ x h, u (x + h) = χ h * u x) :
    ∀ x, u8_fd L u x = (L.map (fun h => χ h - 1)).prod * u x := by
  induction L generalizing u with
  | nil => intro x; simp [u8_fd_nil]
  | cons h hs ih =>
    intro x
    rw [u8_fd_cons]
    have hu' : ∀ x g, (fun x => u (x + h) - u x) (x + g) = χ g * (fun x => u (x + h) - u x) x := by
      intro x g
      show u (x + g + h) - u (x + g) = χ g * (u (x + h) - u x)
      rw [hu (x + g) h, hu x g, hu x h]; ring
    rw [ih _ hu' x]
    show _ = ((χ h - 1) * (hs.map (fun h => χ h - 1)).prod) * u x
    rw [hu x h]
    ring

end Algebra

section Integral

variable {V E ι : Type*} [AddCommGroup V] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace ι]

/-- Forward differences commute with an integral over a parameter. -/
theorem u8_fd_integral (μ : Measure ι) (L : List V) (F : ι → V → E)
    (hF : ∀ x, Integrable (fun ξ => F ξ x) μ) :
    u8_fd L (fun x => ∫ ξ, F ξ x ∂μ) = fun x => ∫ ξ, u8_fd L (F ξ) x ∂μ := by
  induction L generalizing F with
  | nil => rfl
  | cons h hs ih =>
    rw [u8_fd_cons]
    have e : (fun x => (∫ ξ, F ξ (x + h) ∂μ) - ∫ ξ, F ξ x ∂μ) =
        fun x => ∫ ξ, (fun x => F ξ (x + h) - F ξ x) x ∂μ := by
      funext x
      show (∫ ξ, F ξ (x + h) ∂μ) - ∫ ξ, F ξ x ∂μ = ∫ ξ, (F ξ (x + h) - F ξ x) ∂μ
      rw [integral_sub (hF (x + h)) (hF x)]
    rw [e]
    exact ih (fun ξ x => F ξ (x + h) - F ξ x) (fun x => (hF (x + h)).sub (hF x))

end Integral

section Normed

variable {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup E]
  [NormedSpace ℝ E]

theorem u8_fd_sup (L : List V) (r B : ℝ) : ∀ (u : V → E) (x : V), (∀ h ∈ L, ‖h‖ ≤ r) →
    (∀ z ∈ closedBall x (L.length * r), ‖u z‖ ≤ B) → ‖u8_fd L u x‖ ≤ 2 ^ L.length * B := by
  induction L generalizing B with
  | nil =>
    intro u x _ hB
    rw [u8_fd_nil]
    simpa using hB x (by simp)
  | cons h hs ih =>
    intro u x hL hB
    have hr : 0 ≤ r := (norm_nonneg h).trans (hL h (by simp))
    rw [u8_fd_cons]
    have hmem : ∀ z ∈ closedBall x (hs.length * r), z ∈ closedBall x ((h :: hs).length * r) ∧
        z + h ∈ closedBall x ((h :: hs).length * r) := by
      intro z hz
      rw [mem_closedBall, dist_eq_norm] at hz
      have hlen : (((h :: hs).length : ℕ) : ℝ) * r = hs.length * r + r := by
        simp [add_mul]
      constructor
      · rw [mem_closedBall, dist_eq_norm, hlen]; linarith
      · rw [mem_closedBall, dist_eq_norm, hlen]
        have := norm_add_le (z - x) h
        have e : z + h - x = (z - x) + h := by abel
        rw [e]
        linarith [hL h (by simp)]
    have := ih (2 * B) (fun x => u (x + h) - u x) x (fun g hg => hL g (by simp [hg])) (by
      intro z hz
      obtain ⟨h1, h2⟩ := hmem z hz
      calc ‖u (z + h) - u z‖ ≤ ‖u (z + h)‖ + ‖u z‖ := norm_sub_le _ _
        _ ≤ B + B := add_le_add (hB _ h2) (hB _ h1)
        _ = 2 * B := by ring)
    calc ‖u8_fd hs (fun x => u (x + h) - u x) x‖ ≤ 2 ^ hs.length * (2 * B) := this
      _ = 2 ^ (h :: hs).length * B := by simp [pow_succ]; ring

theorem u8_fd_taylor (ℓ : ℕ) : ∀ (L : List V) (r B : ℝ) (u : V → E) (x : V),
    ContDiff ℝ ℓ u → (∀ h ∈ L, ‖h‖ ≤ r) → ℓ ≤ L.length →
    (∀ z ∈ closedBall x (L.length * r), ‖iteratedFDeriv ℝ ℓ u z‖ ≤ B) →
    ‖u8_fd L u x‖ ≤ 2 ^ (L.length - ℓ) * r ^ ℓ * B := by
  induction ℓ with
  | zero =>
    intro L r B u x _ hL _ hB
    have := u8_fd_sup L r B u x hL (fun z hz => by simpa using hB z hz)
    simpa using this
  | succ ℓ ih =>
    intro L r B u x hu hL hlen hB
    cases L with
    | nil => simp at hlen
    | cons h hs =>
      have hr : 0 ≤ r := (norm_nonneg h).trans (hL h (by simp))
      have hlen' : ℓ ≤ hs.length := by simpa using hlen
      have hu0 : ContDiff ℝ ℓ u := hu.of_le (by exact_mod_cast Nat.le_succ ℓ)
      have hsh : ContDiff ℝ ℓ (fun z => u (z + h)) :=
        hu0.comp (contDiff_id.add contDiff_const)
      have hw : ContDiff ℝ ℓ (fun z => u (z + h) - u z) := hsh.sub hu0
      have hlenR : (((h :: hs).length : ℕ) : ℝ) * r = hs.length * r + r := by
        simp [add_mul]
      have key := ih hs r (r * B) (fun z => u (z + h) - u z) x hw
        (fun g hg => hL g (by simp [hg])) hlen' (by
          intro z hz
          rw [mem_closedBall, dist_eq_norm] at hz
          have hz1 : z ∈ closedBall x ((h :: hs).length * r) := by
            rw [mem_closedBall, dist_eq_norm, hlenR]; linarith
          have hz2 : z + h ∈ closedBall x ((h :: hs).length * r) := by
            rw [mem_closedBall, dist_eq_norm, hlenR]
            have := norm_add_le (z - x) h
            have e : z + h - x = (z - x) + h := by abel
            rw [e]
            linarith [hL h (by simp)]
          have e1 : iteratedFDeriv ℝ ℓ (fun z => u (z + h) - u z) z =
              iteratedFDeriv ℝ ℓ u (z + h) - iteratedFDeriv ℝ ℓ u z := by
            have := iteratedFDeriv_sub_apply (𝕜 := ℝ) (x := z) (i := ℓ)
              (f := fun z => u (z + h)) (g := u) hsh.contDiffAt hu0.contDiffAt
            have e2 : ((fun z => u (z + h)) - u) = fun z => u (z + h) - u z := rfl
            rw [e2] at this
            rw [this, iteratedFDeriv_comp_add_right]
          rw [e1]
          have hdiff : Differentiable ℝ (fun z => iteratedFDeriv ℝ ℓ u z) :=
            hu.differentiable_iteratedFDeriv (by exact_mod_cast Nat.lt_succ_self ℓ)
          have := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ)
            (f := fun z => iteratedFDeriv ℝ ℓ u z) (C := B)
            (s := closedBall x ((h :: hs).length * r)) (x := z) (y := z + h)
            (fun y _ => hdiff y) (fun y hy => by
              rw [norm_fderiv_iteratedFDeriv]; exact hB y hy)
            (convex_closedBall _ _) hz1 hz2
          calc ‖iteratedFDeriv ℝ ℓ u (z + h) - iteratedFDeriv ℝ ℓ u z‖
              ≤ B * ‖z + h - z‖ := this
            _ ≤ B * r := by
              have hB0 : 0 ≤ B := by
                have := hB x (by rw [mem_closedBall, dist_self]; positivity)
                exact (norm_nonneg _).trans this
              have : ‖z + h - z‖ ≤ r := by
                have e : z + h - z = h := by abel
                rw [e]; exact hL h (by simp)
              exact mul_le_mul_of_nonneg_left this hB0
            _ = r * B := mul_comm _ _)
      rw [u8_fd_cons]
      calc ‖u8_fd hs (fun x => u (x + h) - u x) x‖
          ≤ 2 ^ (hs.length - ℓ) * r ^ ℓ * (r * B) := key
        _ = 2 ^ ((h :: hs).length - (ℓ + 1)) * r ^ (ℓ + 1) * B := by
          simp only [List.length_cons, Nat.add_sub_add_right, pow_succ]; ring

end Normed

end HRS.U8
