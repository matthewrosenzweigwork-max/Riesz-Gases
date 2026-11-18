import HRS.Main.A34Aux24

/-!
# Packet A34, helper 25: the embedding `E_γ ↪ E_{γ'}` is a linear contraction
-/

noncomputable section

open MeasureTheory Filter Topology Finset ProbabilityTheory
open scoped ENNReal NNReal BigOperators ComplexConjugate RealInnerProductSpace

namespace HRS.A34

open HRS HRS.Main

variable {d : ℕ}

theorem a34_embed_memℓp {m m' : ℝ} (hmm' : m ≤ m') (F : NegSobolev d m) :
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

theorem a34_coord_embed {m m' : ℝ} (hmm' : m ≤ m') (F : NegSobolev d m) (k : NonzeroLattice d) :
    NegSobolev.coord (NegSobolev.embed m' F) k = Lattice.jp k.1 ^ (-m') * NegSobolev.fourierCoeff F k :=
  NegSobolev.coord_ofSeq_of_mem _ (a34_embed_memℓp hmm' F) k

theorem a34_ext {m : ℝ} {F G : NegSobolev d m}
    (h : ∀ k, NegSobolev.coord F k = NegSobolev.coord G k) : F = G := by
  have : (F : lp (fun _ : NonzeroLattice d => ℝ) 2) = G := lp.ext (funext h)
  exact this

theorem a34_coord_add {m : ℝ} (F G : NegSobolev d m) (k : NonzeroLattice d) :
    NegSobolev.coord (F + G) k = NegSobolev.coord F k + NegSobolev.coord G k := by
  unfold NegSobolev.coord
  exact lp.coeFn_add (F : lp (fun _ : NonzeroLattice d => ℝ) 2) G ▸ rfl

theorem a34_fc_sub {m : ℝ} (F G : NegSobolev d m) (k : NonzeroLattice d) :
    NegSobolev.fourierCoeff (F - G) k = NegSobolev.fourierCoeff F k - NegSobolev.fourierCoeff G k := by
  unfold NegSobolev.fourierCoeff
  rw [a34_coord_sub]; ring

theorem a34_fc_add {m : ℝ} (F G : NegSobolev d m) (k : NonzeroLattice d) :
    NegSobolev.fourierCoeff (F + G) k = NegSobolev.fourierCoeff F k + NegSobolev.fourierCoeff G k := by
  unfold NegSobolev.fourierCoeff
  rw [a34_coord_add]; ring

theorem a34_embed_sub {m m' : ℝ} (hmm' : m ≤ m') (F G : NegSobolev d m) :
    NegSobolev.embed m' (F - G) = NegSobolev.embed m' F - NegSobolev.embed m' G := by
  refine a34_ext fun k => ?_
  rw [a34_coord_sub, a34_coord_embed hmm', a34_coord_embed hmm', a34_coord_embed hmm', a34_fc_sub]
  ring

theorem a34_embed_add {m m' : ℝ} (hmm' : m ≤ m') (F G : NegSobolev d m) :
    NegSobolev.embed m' (F + G) = NegSobolev.embed m' F + NegSobolev.embed m' G := by
  refine a34_ext fun k => ?_
  rw [a34_coord_add, a34_coord_embed hmm', a34_coord_embed hmm', a34_coord_embed hmm', a34_fc_add]
  ring

theorem a34_embed_lip {m m' : ℝ} (hmm' : m ≤ m') :
    LipschitzWith 1 (NegSobolev.embed m' : NegSobolev d m → NegSobolev d m') := by
  refine LipschitzWith.of_dist_le_mul fun F G => ?_
  rw [dist_eq_norm, dist_eq_norm, ← a34_embed_sub hmm']
  simpa using NegSobolev.norm_embed_le m' hmm' (F - G)

theorem a34_embed_meas {m m' : ℝ} (hmm' : m ≤ m') :
    Measurable (NegSobolev.embed m' : NegSobolev d m → NegSobolev d m') :=
  (a34_embed_lip hmm').continuous.measurable

end HRS.A34
