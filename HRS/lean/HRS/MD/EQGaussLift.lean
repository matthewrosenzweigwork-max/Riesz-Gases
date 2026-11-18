import HRS.Sections.Sec3

/-!
# EQ-GAUSS: `eq_gauss_lift`

`NegSobolev.embed m₁ ∘ Z` is again an `IsStationaryGaussianField` (on `E_{m₁}`) when `Z` is one on `E_m`, `m ≤ m₁`:
the embedding is linear, a contraction, and preserves the pairing with every test function
(`eval (embed F) φ = eval F φ`, since `embed` does not change the unweighted Fourier coefficients).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MD.EQGaussLift

variable {d : ℕ}

theorem eqgl_embed_memℓp {m m' : ℝ} (hmm' : m ≤ m') (F : NegSobolev d m) :
    Memℓp (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-m') * NegSobolev.fourierCoeff F k) 2 := by
  have hcoord : ∀ k, |Lattice.jp k.1 ^ (-m') * NegSobolev.fourierCoeff F k| ≤ |NegSobolev.coord F k| := by
    intro k
    have hj := Torus.jp_pos k.1
    have : Lattice.jp k.1 ^ (-m') * NegSobolev.fourierCoeff F k =
        Lattice.jp k.1 ^ (m - m') * NegSobolev.coord F k := by
      unfold NegSobolev.fourierCoeff
      rw [← mul_assoc, ← Real.rpow_add hj]
      ring_nf
    rw [this, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hj _)]
    have h1 : Lattice.jp k.1 ^ (m - m') ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (Torus.jp_ge_one _) (by linarith)
    exact mul_le_of_le_one_left (abs_nonneg _) h1
  obtain ⟨h3, -⟩ := NegSobolev.coord_sq F
  rw [Torus.memℓp_two_iff]
  refine Summable.of_nonneg_of_le (fun k => sq_nonneg _) (fun k => ?_) h3
  calc _ = |Lattice.jp k.1 ^ (-m') * NegSobolev.fourierCoeff F k| ^ 2 := (sq_abs _).symm
    _ ≤ |NegSobolev.coord F k| ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hcoord k) 2
    _ = _ := sq_abs _

theorem eqgl_coord_embed {m m' : ℝ} (hmm' : m ≤ m') (F : NegSobolev d m) (k : NonzeroLattice d) :
    NegSobolev.coord (NegSobolev.embed m' F) k =
      Lattice.jp k.1 ^ (-m') * NegSobolev.fourierCoeff F k :=
  NegSobolev.coord_ofSeq_of_mem _ (eqgl_embed_memℓp hmm' F) k

theorem eqgl_fourierCoeff_embed {m m' : ℝ} (hmm' : m ≤ m') (F : NegSobolev d m) (k : NonzeroLattice d) :
    NegSobolev.fourierCoeff (NegSobolev.embed m' F) k = NegSobolev.fourierCoeff F k := by
  have h := eqgl_coord_embed hmm' F k
  unfold NegSobolev.fourierCoeff at h ⊢
  rw [h, ← mul_assoc, ← Real.rpow_add (Torus.jp_pos k.1)]
  simp

/-- The embedding does not change the pairing with any test function. -/
theorem eqgl_eval_embed {m m' : ℝ} (hmm' : m ≤ m') (F : NegSobolev d m) (φ : Torus d → ℝ) :
    NegSobolev.eval (NegSobolev.embed m' F) φ = NegSobolev.eval F φ := by
  unfold NegSobolev.eval
  exact tsum_congr fun k => by rw [eqgl_fourierCoeff_embed hmm']

theorem eqgl_ext {m : ℝ} {F G : NegSobolev d m}
    (h : ∀ k, NegSobolev.coord F k = NegSobolev.coord G k) : F = G := by
  have : (F : lp (fun _ : NonzeroLattice d => ℝ) 2) = G := lp.ext (funext h)
  exact this

theorem eqgl_embed_sub {m m' : ℝ} (hmm' : m ≤ m') (F G : NegSobolev d m) :
    NegSobolev.embed m' (F - G) = NegSobolev.embed m' F - NegSobolev.embed m' G := by
  refine eqgl_ext fun k => ?_
  have hs : NegSobolev.coord (F - G) k = NegSobolev.coord F k - NegSobolev.coord G k := rfl
  have hs' : ∀ (A B : NegSobolev d m'), NegSobolev.coord (A - B) k =
      NegSobolev.coord A k - NegSobolev.coord B k := fun A B => rfl
  rw [hs', eqgl_coord_embed hmm', eqgl_coord_embed hmm', eqgl_coord_embed hmm']
  unfold NegSobolev.fourierCoeff
  rw [hs]; ring

theorem eqgl_embed_lip {m m' : ℝ} (hmm' : m ≤ m') :
    LipschitzWith 1 (NegSobolev.embed m' : NegSobolev d m → NegSobolev d m') := by
  refine LipschitzWith.of_dist_le_mul fun F G => ?_
  rw [dist_eq_norm, dist_eq_norm, ← eqgl_embed_sub hmm']
  simpa using NegSobolev.norm_embed_le m' hmm' (F - G)

theorem eq_gauss_lift_proof (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (V : Torus d → ℝ) {β : ℝ} (hβ : 0 < β) (ρβ : Torus d → ℝ) (m m₁ : ℝ) (hm : (d : ℝ) / 2 < m) (hmm₁ : m ≤ m₁)
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Z : ℝ → Ω' → NegSobolev d m) (hZ : IsStationaryGaussianField P' s β hs0 hsd hβ V ρβ m Z) :
    IsStationaryGaussianField P' s β hs0 hsd hβ V ρβ m₁ (fun t ω => NegSobolev.embed m₁ (Z t ω)) := by
  have hlip := eqgl_embed_lip (d := d) hmm₁
  refine ⟨fun t => hlip.continuous.measurable.comp (hZ.meas t), ?_, ?_⟩
  · filter_upwards [hZ.cont] with ω hω
    exact hlip.continuous.comp_continuousOn hω
  · intro p τ φ hτ hφ
    have := hZ.gaussian p τ φ hτ hφ
    simpa only [eqgl_eval_embed hmm₁] using this

end HRS.MD.EQGaussLift
