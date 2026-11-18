import HRS.Sections.AdjKBAux2

/-!
# ADJKB Aux3: deterministic dyadic chaining (Kolmogorov-Chentsov, deterministic part)
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.AdjK

lemma adjkb_chain {E : Type*} [NormedAddCommGroup E] (f : ℝ → E) (τ₀ r : ℝ) (hr0 : 0 < r)
    (hr1 : r < 1) (N : ℕ)
    (hinc : ∀ n : ℕ, N ≤ n → ∀ a : ℕ,
      ‖f (((a : ℝ) + 1) * (τ₀ / 2 ^ n)) - f ((a : ℝ) * (τ₀ / 2 ^ n))‖ ≤ r ^ n) :
    ∀ L : ℕ, N ≤ L → ∀ a b : ℕ, a ≤ b + 2 ^ (L - N) → b ≤ a + 2 ^ (L - N) →
      ‖f ((a : ℝ) * (τ₀ / 2 ^ L)) - f ((b : ℝ) * (τ₀ / 2 ^ L))‖ ≤
        r ^ N * (1 + r) / (1 - r) - 2 * r ^ (L + 1) / (1 - r) := by
  have h1r : 0 < 1 - r := by linarith
  intro L hL
  induction L, hL using Nat.le_induction with
  | base =>
    intro a b hab hba
    simp only [Nat.sub_self, pow_zero] at hab hba
    have hval : r ^ N * (1 + r) / (1 - r) - 2 * r ^ (N + 1) / (1 - r) = r ^ N := by
      field_simp; ring
    rw [hval]
    have hrN : 0 ≤ r ^ N := by positivity
    rcases (by omega : a = b ∨ a = b + 1 ∨ b = a + 1) with h | h | h
    · subst h; simpa using hrN
    · subst h
      have := hinc N le_rfl b
      push_cast
      exact this
    · subst h
      have := hinc N le_rfl a
      rw [norm_sub_rev]
      push_cast
      exact this
  | succ L hL ih =>
    intro a b hab hba
    have hP : 2 ^ (L + 1 - N) = 2 * 2 ^ (L - N) := by
      rw [show L + 1 - N = (L - N) + 1 by omega, pow_succ]; ring
    rw [hP] at hab hba
    have hround : ∀ c : ℕ, ‖f ((c : ℝ) * (τ₀ / 2 ^ (L + 1))) -
        f (((c / 2 : ℕ) : ℝ) * (τ₀ / 2 ^ L))‖ ≤ r ^ (L + 1) := by
      intro c
      rcases Nat.even_or_odd' c with ⟨e, rfl | rfl⟩
      · have : (2 * e) / 2 = e := by omega
        rw [this]
        have : ((2 * e : ℕ) : ℝ) * (τ₀ / 2 ^ (L + 1)) = (e : ℝ) * (τ₀ / 2 ^ L) := by
          push_cast; rw [pow_succ]; field_simp
        rw [this, sub_self, norm_zero]; positivity
      · have : (2 * e + 1) / 2 = e := by omega
        rw [this]
        have h2 : ((e : ℕ) : ℝ) * (τ₀ / 2 ^ L) = ((2 * e : ℕ) : ℝ) * (τ₀ / 2 ^ (L + 1)) := by
          push_cast; rw [pow_succ]; field_simp
        rw [h2]
        have := hinc (L + 1) (by omega) (2 * e)
        push_cast at this ⊢
        exact this
    have hmid := ih (a / 2) (b / 2) (by omega) (by omega)
    have ha := hround a
    have hb := hround b
    calc ‖f ((a : ℝ) * (τ₀ / 2 ^ (L + 1))) - f ((b : ℝ) * (τ₀ / 2 ^ (L + 1)))‖
        ≤ ‖f ((a : ℝ) * (τ₀ / 2 ^ (L + 1))) - f (((a / 2 : ℕ) : ℝ) * (τ₀ / 2 ^ L))‖ +
          ‖f (((a / 2 : ℕ) : ℝ) * (τ₀ / 2 ^ L)) - f (((b / 2 : ℕ) : ℝ) * (τ₀ / 2 ^ L))‖ +
          ‖f ((b : ℝ) * (τ₀ / 2 ^ (L + 1))) - f (((b / 2 : ℕ) : ℝ) * (τ₀ / 2 ^ L))‖ := by
          rw [norm_sub_rev (f ((b : ℝ) * (τ₀ / 2 ^ (L + 1))))]
          calc _ = ‖(f ((a : ℝ) * (τ₀ / 2 ^ (L + 1))) - f (((a / 2 : ℕ) : ℝ) * (τ₀ / 2 ^ L))) +
                (f (((a / 2 : ℕ) : ℝ) * (τ₀ / 2 ^ L)) - f (((b / 2 : ℕ) : ℝ) * (τ₀ / 2 ^ L))) +
                (f (((b / 2 : ℕ) : ℝ) * (τ₀ / 2 ^ L)) - f ((b : ℝ) * (τ₀ / 2 ^ (L + 1))))‖ := by
                congr 1; abel
            _ ≤ _ := norm_add₃_le
      _ ≤ r ^ (L + 1) + (r ^ N * (1 + r) / (1 - r) - 2 * r ^ (L + 1) / (1 - r)) + r ^ (L + 1) := by
          gcongr
      _ = r ^ N * (1 + r) / (1 - r) - 2 * r ^ (L + 1 + 1) / (1 - r) := by
          rw [pow_succ r (L + 1)]; field_simp; ring

lemma adjkb_tendsto_floor (s τ₀ : ℝ) (hs : 0 ≤ s) (hτ : 0 < τ₀) :
    Tendsto (fun L : ℕ => (⌊s / (τ₀ / 2 ^ L)⌋₊ : ℝ) * (τ₀ / 2 ^ L)) atTop (𝓝 s) := by
  have hτL : ∀ L : ℕ, 0 < τ₀ / 2 ^ L := fun L => by positivity
  have h0 : Tendsto (fun L : ℕ => τ₀ / 2 ^ L) atTop (𝓝 0) := by
    have : Tendsto (fun L : ℕ => (2 : ℝ) ^ L) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
    exact tendsto_const_nhds.div_atTop this
  rw [← tendsto_sub_nhds_zero_iff]
  refine squeeze_zero_norm (fun L => ?_) h0
  have hτ' := hτL L
  have h1 : (⌊s / (τ₀ / 2 ^ L)⌋₊ : ℝ) ≤ s / (τ₀ / 2 ^ L) := Nat.floor_le (div_nonneg hs hτ'.le)
  have h2 : s / (τ₀ / 2 ^ L) < (⌊s / (τ₀ / 2 ^ L)⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  rw [le_div_iff₀ hτ'] at h1
  rw [div_lt_iff₀ hτ'] at h2
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> nlinarith

lemma adjkb_modulus {E : Type*} [NormedAddCommGroup E] (f : ℝ → E) (hf : Continuous f)
    (T : ℝ) (hT : 0 < T) (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) (N : ℕ)
    (hinc : ∀ n : ℕ, N ≤ n → ∀ a : ℕ,
      ‖f (((a : ℝ) + 1) * (T / 2 ^ n)) - f ((a : ℝ) * (T / 2 ^ n))‖ ≤ r ^ n) :
    ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → |s - t| < T / 2 ^ N →
      ‖f s - f t‖ ≤ r ^ N * (1 + r) / (1 - r) := by
  intro s t hs ht hst
  have h1r : 0 < 1 - r := by linarith
  have hchain := adjkb_chain f T r hr0 hr1 N hinc
  have hlim : Tendsto (fun L : ℕ => ‖f ((⌊s / (T / 2 ^ L)⌋₊ : ℝ) * (T / 2 ^ L)) -
      f ((⌊t / (T / 2 ^ L)⌋₊ : ℝ) * (T / 2 ^ L))‖) atTop (𝓝 ‖f s - f t‖) :=
    (((hf.tendsto s).comp (adjkb_tendsto_floor s T hs hT)).sub
      ((hf.tendsto t).comp (adjkb_tendsto_floor t T ht hT))).norm
  refine le_of_tendsto hlim ?_
  filter_upwards [eventually_ge_atTop N] with L hL
  have hτ' : 0 < T / 2 ^ L := by positivity
  have hP : (2 : ℝ) ^ L = 2 ^ N * 2 ^ (L - N) := by rw [← pow_add]; congr 1; omega
  have hτN : T / 2 ^ N = 2 ^ (L - N) * (T / 2 ^ L) := by
    rw [hP]; field_simp
  have hfs1 : (⌊s / (T / 2 ^ L)⌋₊ : ℝ) ≤ s / (T / 2 ^ L) :=
    Nat.floor_le (div_nonneg hs hτ'.le)
  have hfs2 : s / (T / 2 ^ L) < (⌊s / (T / 2 ^ L)⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  have hft1 : (⌊t / (T / 2 ^ L)⌋₊ : ℝ) ≤ t / (T / 2 ^ L) :=
    Nat.floor_le (div_nonneg ht hτ'.le)
  have hft2 : t / (T / 2 ^ L) < (⌊t / (T / 2 ^ L)⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  rw [le_div_iff₀ hτ'] at hfs1 hft1
  rw [div_lt_iff₀ hτ'] at hfs2 hft2
  have habs := abs_lt.1 hst
  rw [hτN] at habs
  set a := ⌊s / (T / 2 ^ L)⌋₊
  set b := ⌊t / (T / 2 ^ L)⌋₊
  set P : ℕ := 2 ^ (L - N) with hPdef
  have hPR : ((P : ℕ) : ℝ) = 2 ^ (L - N) := by simp [hPdef]
  rw [← hPR] at habs
  have hab : a ≤ b + P := by
    have : (a : ℝ) < b + P + 1 := by
      by_contra hcon
      push_neg at hcon
      nlinarith [habs.1, habs.2]
    exact_mod_cast Nat.lt_succ_iff.1 (by exact_mod_cast this)
  have hba : b ≤ a + P := by
    have : (b : ℝ) < a + P + 1 := by
      by_contra hcon
      push_neg at hcon
      nlinarith [habs.1, habs.2]
    exact_mod_cast Nat.lt_succ_iff.1 (by exact_mod_cast this)
  have := hchain L hL a b hab hba
  refine this.trans ?_
  have : 0 ≤ 2 * r ^ (L + 1) / (1 - r) := by positivity
  linarith

end HRS.AdjK
