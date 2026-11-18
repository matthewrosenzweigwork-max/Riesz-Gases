import HRS.MS.R2SeAux7

/-!
# S9.9 `r2_static_edgeworth`, packet 8: the Stein class, partial derivatives, uniform limits, the CLT wrapper

Worker S99, namespace `S99`.

* `pd ψ j z = Dψ(z)[e_j]` (partial derivative in `ℓ²`), `Bd n ψ` (`C^n`, all derivatives of order `≤ n` bounded by `1`),
  `SteinCl f` (`C⁵`, `‖D^i f‖ ≤ 1` for `1 ≤ i ≤ 5`; contains `steinSolution P G Φ` for `Φ` in the `C_b^5` unit ball);
  `pd` lowers the regularity by one (`Bd.pd`, `SteinCl.pd`);
* `ULim u L`: `u N f → L f` as `N → ∞`, uniformly over the Stein class; `s99_ULim_tsum`: Tannery for series with summable bounds;
* `s99_clt`: the CLT of S4.6 for `ℓ²` test functions `F ∈ Bd 2`, with rate `K/√N`.
-/

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

noncomputable section

namespace S99

open S45
open HRS.Whole
open HRS (Euc cbNorm MemCb)

variable {d N : ℕ}

/-- The partial derivative `∂_j ψ(z) = Dψ(z)[e_j]`. -/
def pd (ψ : SeqL2 → ℝ) (j : ℕ) (z : SeqL2) : ℝ := fderiv ℝ ψ z (s45_e1 j (1 : ℝ))

/-- `C^n` with every derivative of order `≤ n` bounded by `1`. -/
def Bd (n : ℕ) (ψ : SeqL2 → ℝ) : Prop :=
  ContDiff ℝ n ψ ∧ ∀ i : ℕ, i ≤ n → ∀ z, ‖iteratedFDeriv ℝ i ψ z‖ ≤ 1

/-- The Stein class. -/
def SteinCl (f : SeqL2 → ℝ) : Prop :=
  ContDiff ℝ 5 f ∧ ∀ i : ℕ, 1 ≤ i → i ≤ 5 → ∀ z, ‖iteratedFDeriv ℝ i f z‖ ≤ 1

theorem s99_pd_eq (ψ : SeqL2 → ℝ) (j : ℕ) :
    pd ψ j = fun z => (ContinuousLinearMap.apply ℝ ℝ (s45_e1 j (1 : ℝ))) (fderiv ℝ ψ z) := rfl

theorem s99_pd_iter {n : ℕ} {ψ : SeqL2 → ℝ} (hψ : ContDiff ℝ ((n + 1 : ℕ) : WithTop ℕ∞) ψ)
    (hD : ∀ i : ℕ, 1 ≤ i → i ≤ n + 1 → ∀ z, ‖iteratedFDeriv ℝ i ψ z‖ ≤ 1) (j : ℕ) :
    ContDiff ℝ n (pd ψ j) ∧ ∀ i : ℕ, i ≤ n → ∀ z, ‖iteratedFDeriv ℝ i (pd ψ j) z‖ ≤ 1 := by
  have hfd : ContDiff ℝ (n : WithTop ℕ∞) (fderiv ℝ ψ) := hψ.fderiv_right (m := n) (by push_cast; rfl)
  set g : (SeqL2 →L[ℝ] ℝ) →L[ℝ] ℝ := ContinuousLinearMap.apply ℝ ℝ (s45_e1 j (1 : ℝ)) with hg
  have hgn : ‖g‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun L => ?_
    rw [hg, ContinuousLinearMap.apply_apply, one_mul]
    refine (L.le_opNorm _).trans ?_
    rw [s99_e1_norm, mul_one]
  rw [s99_pd_eq]
  refine ⟨g.contDiff.comp hfd, fun i hi z => ?_⟩
  have := g.norm_iteratedFDeriv_comp_left (f := fderiv ℝ ψ) (x := z) (N := (n : WithTop ℕ∞)) (n := i)
    hfd.contDiffAt (by exact_mod_cast hi)
  rw [norm_iteratedFDeriv_fderiv] at this
  calc ‖iteratedFDeriv ℝ i (fun z => g (fderiv ℝ ψ z)) z‖
      = ‖iteratedFDeriv ℝ i (g ∘ fderiv ℝ ψ) z‖ := rfl
    _ ≤ ‖g‖ * ‖iteratedFDeriv ℝ (i + 1) ψ z‖ := this
    _ ≤ 1 * 1 := mul_le_mul hgn (hD (i + 1) (by omega) (by omega) z) (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

theorem Bd.pd {n : ℕ} {ψ : SeqL2 → ℝ} (h : Bd (n + 1) ψ) (j : ℕ) : Bd n (pd ψ j) :=
  s99_pd_iter h.1 (fun i _ hi z => h.2 i hi z) j

theorem SteinCl.pd {f : SeqL2 → ℝ} (h : SteinCl f) (j : ℕ) : Bd 4 (pd f j) :=
  s99_pd_iter (n := 4) h.1 (fun i h1 h2 z => h.2 i h1 h2 z) j

theorem Bd.contDiff {n : ℕ} {ψ : SeqL2 → ℝ} (h : Bd n ψ) : ContDiff ℝ n ψ := h.1

theorem Bd.of_le {m n : ℕ} {ψ : SeqL2 → ℝ} (h : Bd n ψ) (hmn : m ≤ n) : Bd m ψ :=
  ⟨h.1.of_le (by exact_mod_cast hmn), fun i hi z => h.2 i (hi.trans hmn) z⟩

theorem Bd.fderiv_le {n : ℕ} {ψ : SeqL2 → ℝ} (h : Bd (n + 1) ψ) (z : SeqL2) :
    ‖fderiv ℝ ψ z‖ ≤ 1 := by
  rw [← norm_iteratedFDeriv_one]; exact h.2 1 (by omega) z

theorem Bd.abs_le {n : ℕ} {ψ : SeqL2 → ℝ} (h : Bd n ψ) (z : SeqL2) : |ψ z| ≤ 1 := by
  have := h.2 0 (Nat.zero_le _) z
  rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this

/-! ### Uniform limits over the Stein class -/

/-- `u N f → L f` uniformly over the Stein class. -/
def ULim (u : ℕ → (SeqL2 → ℝ) → ℝ) (L : (SeqL2 → ℝ) → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ f, SteinCl f → |u N f - L f| ≤ ε

theorem ULim.add {u v : ℕ → (SeqL2 → ℝ) → ℝ} {L M : (SeqL2 → ℝ) → ℝ} (hu : ULim u L) (hv : ULim v M) :
    ULim (fun N f => u N f + v N f) (fun f => L f + M f) := by
  intro ε hε
  obtain ⟨N₁, h1⟩ := hu (ε / 2) (by positivity)
  obtain ⟨N₂, h2⟩ := hv (ε / 2) (by positivity)
  refine ⟨max N₁ N₂, fun N hN f hf => ?_⟩
  have a := h1 N (le_trans (le_max_left _ _) hN) f hf
  have b := h2 N (le_trans (le_max_right _ _) hN) f hf
  calc |u N f + v N f - (L f + M f)| = |(u N f - L f) + (v N f - M f)| := by ring_nf
    _ ≤ |u N f - L f| + |v N f - M f| := abs_add_le _ _
    _ ≤ ε := by linarith

theorem ULim.neg {u : ℕ → (SeqL2 → ℝ) → ℝ} {L : (SeqL2 → ℝ) → ℝ} (hu : ULim u L) :
    ULim (fun N f => -u N f) (fun f => -L f) := by
  intro ε hε
  obtain ⟨N₁, h1⟩ := hu ε hε
  refine ⟨N₁, fun N hN f hf => ?_⟩
  have := h1 N hN f hf
  rwa [show -u N f - -L f = -(u N f - L f) by ring, abs_neg]

theorem ULim.mul_const {u : ℕ → (SeqL2 → ℝ) → ℝ} {L : (SeqL2 → ℝ) → ℝ} (hu : ULim u L) (c : ℝ) :
    ULim (fun N f => c * u N f) (fun f => c * L f) := by
  intro ε hε
  obtain ⟨N₁, h1⟩ := hu (ε / (|c| + 1)) (by positivity)
  refine ⟨N₁, fun N hN f hf => ?_⟩
  have := h1 N hN f hf
  rw [← mul_sub, abs_mul]
  calc |c| * |u N f - L f| ≤ |c| * (ε / (|c| + 1)) := mul_le_mul_of_nonneg_left this (abs_nonneg _)
    _ ≤ ε := by
      rw [mul_div_assoc', div_le_iff₀ (by positivity)]
      nlinarith [abs_nonneg c]

theorem ULim.congr {u v : ℕ → (SeqL2 → ℝ) → ℝ} {L : (SeqL2 → ℝ) → ℝ}
    (h : ∀ N f, SteinCl f → u N f = v N f) (hu : ULim u L) : ULim v L := by
  intro ε hε
  obtain ⟨N₁, h1⟩ := hu ε hε
  exact ⟨N₁, fun N hN f hf => by rw [← h N f hf]; exact h1 N hN f hf⟩

/-- Convergence at a uniform rate: `|u N f - L f| ≤ K r_N`, `r_N → 0`. -/
theorem ULim.of_rate {u : ℕ → (SeqL2 → ℝ) → ℝ} {L : (SeqL2 → ℝ) → ℝ} {K : ℝ} {r : ℕ → ℝ}
    (hr : Tendsto r atTop (𝓝 0)) (h : ∀ N f, SteinCl f → |u N f - L f| ≤ K * r N) : ULim u L := by
  intro ε hε
  have hK : 0 < |K| + 1 := by positivity
  have := (hr.eventually (gt_mem_nhds (show (0 : ℝ) < ε / (|K| + 1) by positivity))).and
    (hr.eventually (lt_mem_nhds (show (-(1 : ℝ)) < 0 by norm_num)))
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 (hr.eventually (Metric.ball_mem_nhds 0 (show 0 < ε / (|K| + 1) by positivity)))
  refine ⟨N₀, fun N hN f hf => ?_⟩
  have hrN : |r N| < ε / (|K| + 1) := by simpa using hN₀ N hN
  calc |u N f - L f| ≤ K * r N := h N f hf
    _ ≤ |K| * |r N| := by
        rw [← abs_mul]; exact le_abs_self _
    _ ≤ (|K| + 1) * (ε / (|K| + 1)) := by
        apply mul_le_mul (by linarith) hrN.le (abs_nonneg _) hK.le
    _ = ε := by field_simp

/-- Tannery for series with summable bounds. -/
theorem s99_ULim_tsum {u : ℕ → ℕ → (SeqL2 → ℝ) → ℝ} {L : ℕ → (SeqL2 → ℝ) → ℝ} {M : ℕ → ℝ}
    (hM : Summable M) (hu : ∀ i N f, SteinCl f → |u i N f| ≤ M i)
    (hL : ∀ i f, SteinCl f → |L i f| ≤ M i) (h : ∀ i, ULim (u i) (L i)) :
    ULim (fun N f => ∑' i, u i N f) (fun f => ∑' i, L i f) := by
  intro ε hε
  have hM0 : ∀ i, 0 ≤ M i := fun i => (abs_nonneg _).trans (hu i 0 (fun _ => 0) ⟨contDiff_const, fun i _ _ z => by
    simp [iteratedFDeriv_const_of_ne (by omega : i ≠ 0)]⟩)
  -- choose the cut
  obtain ⟨k, hk⟩ : ∃ k : ℕ, ∑' i, M (i + k) < ε / 4 := by
    have := (tendsto_sum_nat_add M)
    have h2 := this.eventually (gt_mem_nhds (show (0 : ℝ) < ε / 4 by positivity))
    obtain ⟨k, hk⟩ := h2.exists
    exact ⟨k, hk⟩
  -- finite part
  have hfin : ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ f, SteinCl f → ∀ i ∈ Finset.range k,
      |u i N f - L i f| ≤ ε / (2 * (k + 1)) := by
    have : ∀ i : ℕ, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ f, SteinCl f → |u i N f - L i f| ≤ ε / (2 * (k + 1)) :=
      fun i => h i _ (by positivity)
    choose Ns hNs using this
    refine ⟨(Finset.range k).sup Ns, fun N hN f hf i hi => ?_⟩
    exact hNs i N (le_trans (Finset.le_sup hi) hN) f hf
  obtain ⟨N₀, hN₀⟩ := hfin
  refine ⟨N₀, fun N hN f hf => ?_⟩
  have hsu : Summable fun i => u i N f := Summable.of_norm_bounded hM (fun i => by
    rw [Real.norm_eq_abs]; exact hu i N f hf)
  have hsL : Summable fun i => L i f := Summable.of_norm_bounded hM (fun i => by
    rw [Real.norm_eq_abs]; exact hL i f hf)
  beta_reduce
  rw [← Summable.sum_add_tsum_nat_add k hsu, ← Summable.sum_add_tsum_nat_add k hsL]
  have e1 : |∑ i ∈ Finset.range k, (u i N f - L i f)| ≤ ε / 2 := by
    calc |∑ i ∈ Finset.range k, (u i N f - L i f)| ≤ ∑ i ∈ Finset.range k, |u i N f - L i f| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ Finset.range k, ε / (2 * (k + 1)) :=
          Finset.sum_le_sum fun i hi => hN₀ N hN f hf i hi
      _ = k * (ε / (2 * (k + 1))) := by simp
      _ ≤ ε / 2 := by
          have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
          rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
  have e2 : |∑' i, u (i + k) N f| ≤ ε / 4 := by
    have hg : HasSum (fun i => M (i + k)) (∑' i, M (i + k)) := (hM.comp_injective (add_left_injective k)).hasSum
    have := tsum_of_norm_bounded (f := fun i => u (i + k) N f) hg (fun i => by
      rw [Real.norm_eq_abs]; exact hu (i + k) N f hf)
    rw [Real.norm_eq_abs] at this
    exact this.trans hk.le
  have e3 : |∑' i, L (i + k) f| ≤ ε / 4 := by
    have hg : HasSum (fun i => M (i + k)) (∑' i, M (i + k)) := (hM.comp_injective (add_left_injective k)).hasSum
    have := tsum_of_norm_bounded (f := fun i => L (i + k) f) hg (fun i => by
      rw [Real.norm_eq_abs]; exact hL (i + k) f hf)
    rw [Real.norm_eq_abs] at this
    exact this.trans hk.le
  have hsplit : (∑ i ∈ Finset.range k, u i N f + ∑' i, u (i + k) N f) -
      (∑ i ∈ Finset.range k, L i f + ∑' i, L (i + k) f) =
      ∑ i ∈ Finset.range k, (u i N f - L i f) + (∑' i, u (i + k) N f - ∑' i, L (i + k) f) := by
    rw [Finset.sum_sub_distrib]; ring
  rw [hsplit]
  calc |∑ i ∈ Finset.range k, (u i N f - L i f) + (∑' i, u (i + k) N f - ∑' i, L (i + k) f)|
      ≤ |∑ i ∈ Finset.range k, (u i N f - L i f)| + |∑' i, u (i + k) N f - ∑' i, L (i + k) f| :=
        abs_add_le _ _
    _ ≤ ε / 2 + (|∑' i, u (i + k) N f| + |∑' i, L (i + k) f|) := by
        gcongr; exact abs_sub _ _
    _ ≤ ε := by linarith

end S99

end
