import HRS.Main.A34Aux25

/-!
# Packet A34, helper 26: compactness of the embedding `E_γ ↪ E_{γ'}` on bounded sets with coordinatewise
convergence (head/tail argument)
-/

noncomputable section

open MeasureTheory Filter Topology Finset ProbabilityTheory
open scoped ENNReal NNReal BigOperators ComplexConjugate RealInnerProductSpace

namespace HRS.A34

open HRS HRS.Main

variable {d : ℕ}

/-- head/tail: weights tending to `0` along the cofinite filter, uniformly bounded `ℓ²` sequences
converging coordinatewise to `0`. -/
theorem a34_tail_head {κ : Type*} (w : κ → ℝ) (hw0 : ∀ k, 0 ≤ w k) (hw1 : ∀ k, w k ≤ 1)
    (hw : Tendsto w cofinite (𝓝 0)) (x : ℕ → κ → ℝ) (B : ℝ)
    (hxs : ∀ N, Summable fun k => x N k ^ 2)
    (hB : ∀ᶠ N in atTop, ∑' k, x N k ^ 2 ≤ B)
    (hx : ∀ k, Tendsto (fun N => x N k) atTop (𝓝 0)) :
    Tendsto (fun N => ∑' k, w k * x N k ^ 2) atTop (𝓝 0) := by
  classical
  rw [Metric.tendsto_nhds]
  intro ε hε
  set η : ℝ := ε / (4 * (|B| + 1)) with hη
  have hηpos : 0 < η := by positivity
  have hfin : {k | ¬ w k < η}.Finite :=
    Filter.eventually_cofinite.1 ((tendsto_order.1 hw).2 η hηpos)
  set s : Finset κ := hfin.toFinset with hs
  have hhead : Tendsto (fun N => ∑ k ∈ s, x N k ^ 2) atTop (𝓝 0) := by
    have := tendsto_finset_sum s (fun k _ => (hx k).pow 2)
    simpa using this
  have hsmall : ∀ᶠ N in atTop, ∑ k ∈ s, x N k ^ 2 < ε / 2 :=
    (tendsto_order.1 hhead).2 _ (by positivity)
  filter_upwards [hB, hsmall] with N hBN hsN
  have hsum := hxs N
  have hpt : ∀ k, w k * x N k ^ 2 ≤ η * x N k ^ 2 + (if k ∈ s then x N k ^ 2 else 0) := by
    intro k
    by_cases hk : k ∈ s
    · rw [if_pos hk]
      have h1 : w k * x N k ^ 2 ≤ x N k ^ 2 := mul_le_of_le_one_left (sq_nonneg _) (hw1 k)
      have h2 : 0 ≤ η * x N k ^ 2 := mul_nonneg hηpos.le (sq_nonneg _)
      linarith
    · rw [if_neg hk, add_zero]
      have : w k < η := by
        by_contra hcon
        exact hk (by simpa [hs] using hcon)
      exact mul_le_mul_of_nonneg_right this.le (sq_nonneg _)
  have hite : Summable fun k => if k ∈ s then x N k ^ 2 else 0 :=
    summable_of_ne_finset_zero (s := s) (fun k hk => if_neg hk)
  have hsum2 : Summable fun k => w k * x N k ^ 2 :=
    Summable.of_nonneg_of_le (fun k => mul_nonneg (hw0 k) (sq_nonneg _))
      (fun k => mul_le_of_le_one_left (sq_nonneg _) (hw1 k)) hsum
  have h1 : ∑' k, w k * x N k ^ 2 ≤
      ∑' k, (η * x N k ^ 2 + (if k ∈ s then x N k ^ 2 else 0)) :=
    hsum2.tsum_le_tsum hpt ((hsum.mul_left η).add hite)
  rw [(hsum.mul_left η).tsum_add hite, tsum_mul_left,
    tsum_eq_sum (s := s) (fun k hk => if_neg hk)] at h1
  have h2 : ∑ k ∈ s, (if k ∈ s then x N k ^ 2 else 0) = ∑ k ∈ s, x N k ^ 2 :=
    Finset.sum_congr rfl fun k hk => if_pos hk
  rw [h2] at h1
  have h3 : 0 ≤ ∑' k, w k * x N k ^ 2 := tsum_nonneg fun k => mul_nonneg (hw0 k) (sq_nonneg _)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg h3]
  have h4 : η * ∑' k, x N k ^ 2 ≤ ε / 4 := by
    have h5 : ∑' k, x N k ^ 2 ≤ |B| + 1 := by linarith [le_abs_self B]
    have h6 : 0 ≤ ∑' k, x N k ^ 2 := tsum_nonneg fun k => sq_nonneg _
    calc η * ∑' k, x N k ^ 2 ≤ η * (|B| + 1) := mul_le_mul_of_nonneg_left h5 hηpos.le
      _ = ε / 4 := by rw [hη]; field_simp
  linarith

theorem a34_w_tendsto {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun k : NonzeroLattice d => (Lattice.jp k.1 ^ (-δ)) ^ 2) cofinite (𝓝 0) := by
  obtain ⟨n, hn⟩ := exists_nat_gt ((d : ℝ) / δ)
  have hn' : (d : ℝ) < n * δ := by rwa [div_lt_iff₀ hδ] at hn
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hsum := summable_jp_rpow (d := d) ((n : ℝ) * δ) (by linarith)
  have h0 := hsum.tendsto_cofinite_zero
  have hxn : ∀ k : NonzeroLattice d, ((Lattice.jp k.1 ^ (-δ)) ^ 2) ^ n =
      Lattice.jp k.1 ^ (-(2 * ((n : ℝ) * δ))) := by
    intro k
    have hj := (Torus.jp_pos k.1).le
    rw [Torus.jp_rpow_sq, ← Real.rpow_natCast, ← Real.rpow_mul hj]
    congr 1; ring
  rw [tendsto_order]
  refine ⟨fun a ha => Filter.Eventually.of_forall fun k => lt_of_lt_of_le ha (sq_nonneg _),
    fun a ha => ?_⟩
  have hnpos : n ≠ 0 := by
    rintro rfl
    simp at hn'
    linarith
  have := (tendsto_order.1 (h0.congr (fun k => (hxn k).symm))).2 (a ^ n) (pow_pos ha n)
  filter_upwards [this] with k hk
  exact lt_of_pow_lt_pow_left₀ n ha.le hk

theorem a34_coord_embed' {m m' : ℝ} (hmm' : m ≤ m') (v : NegSobolev d m) (k : NonzeroLattice d) :
    NegSobolev.coord (NegSobolev.embed m' v) k =
      Lattice.jp k.1 ^ (-(m' - m)) * NegSobolev.coord v k := by
  have hj := Torus.jp_pos k.1
  rw [a34_coord_embed hmm']
  unfold NegSobolev.fourierCoeff
  rw [← mul_assoc, ← Real.rpow_add hj]
  congr 2
  ring

theorem a34_embed_norm_sq {m m' : ℝ} (hmm' : m ≤ m') (v : NegSobolev d m) :
    ‖NegSobolev.embed m' v‖ ^ 2 =
      ∑' k, (Lattice.jp k.1 ^ (-(m' - m))) ^ 2 * NegSobolev.coord v k ^ 2 := by
  rw [(NegSobolev.coord_sq (NegSobolev.embed m' v)).2]
  refine tsum_congr fun k => ?_
  rw [a34_coord_embed' hmm', mul_pow]

theorem a34_weight_le_one {δ : ℝ} (hδ : 0 ≤ δ) (k : NonzeroLattice d) :
    (Lattice.jp k.1 ^ (-δ)) ^ 2 ≤ 1 := by
  have h1 : Lattice.jp k.1 ^ (-δ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (Torus.jp_ge_one _) (by linarith)
  have h2 : 0 ≤ Lattice.jp k.1 ^ (-δ) := Real.rpow_nonneg (Torus.jp_pos _).le _
  nlinarith

/-- Bounded coordinatewise convergent sequences converge in the weaker topology. -/
theorem a34_embed_tendsto {γ γ' : ℝ} (hγ : γ < γ') (u : ℕ → NegSobolev d γ) (u₀ : NegSobolev d γ)
    (B : ℝ) (hB : ∀ᶠ N in atTop, ‖u N - u₀‖ ^ 2 ≤ B)
    (hx : ∀ k, Tendsto (fun N => NegSobolev.coord (u N) k) atTop (𝓝 (NegSobolev.coord u₀ k))) :
    Tendsto (fun N => ‖NegSobolev.embed γ' (u N) - NegSobolev.embed γ' u₀‖) atTop (𝓝 0) := by
  have hγ' : γ ≤ γ' := hγ.le
  have key : Tendsto (fun N => ‖NegSobolev.embed γ' (u N) - NegSobolev.embed γ' u₀‖ ^ 2) atTop
      (𝓝 0) := by
    have := a34_tail_head (fun k : NonzeroLattice d => (Lattice.jp k.1 ^ (-(γ' - γ))) ^ 2)
      (fun k => sq_nonneg _) (fun k => a34_weight_le_one (by linarith) k)
      (a34_w_tendsto (by linarith)) (fun N k => NegSobolev.coord (u N - u₀) k) B
      (fun N => (NegSobolev.coord_sq _).1)
      (hB.mono fun N hN => by rw [← (NegSobolev.coord_sq (u N - u₀)).2]; exact hN)
      (fun k => by
        have := (hx k).sub_const (NegSobolev.coord u₀ k)
        simpa [a34_coord_sub] using this)
    refine this.congr fun N => ?_
    rw [← a34_embed_sub hγ', a34_embed_norm_sq hγ']
  have := key.sqrt
  simpa [Real.sqrt_sq (norm_nonneg _)] using this

end HRS.A34
