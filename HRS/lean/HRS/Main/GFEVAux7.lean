import HRS.Main.GFEVAux6

/-!
# Packet GFEVG, part 7: the embeddings `E_a ↪ E_b` (algebra), the evolution on `E_γ` and `E_{γ-4}`
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.GF

open HRS HRS.PDE HRS.PDE.ET HRS.Uniform HRS.Uniform.Q54

variable {d : ℕ}

/-! ### Embeddings -/

theorem gfev_embed_memℓp {m m' : ℝ} (hmm' : m ≤ m') (F : NegSobolev d m) :
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

theorem gfev_coord_embed {m m' : ℝ} (hmm' : m ≤ m') (F : NegSobolev d m) (k : NonzeroLattice d) :
    NegSobolev.coord (NegSobolev.embed m' F) k = Lattice.jp k.1 ^ (-m') * NegSobolev.fourierCoeff F k :=
  NegSobolev.coord_ofSeq_of_mem _ (gfev_embed_memℓp hmm' F) k

theorem gfev_fourierCoeff_embed {m m' : ℝ} (hmm' : m ≤ m') (F : NegSobolev d m) (k : NonzeroLattice d) :
    NegSobolev.fourierCoeff (NegSobolev.embed m' F) k = NegSobolev.fourierCoeff F k := by
  have h := gfev_coord_embed hmm' F k
  unfold NegSobolev.fourierCoeff at h ⊢
  rw [h, ← mul_assoc, ← Real.rpow_add (Torus.jp_pos k.1)]
  simp

theorem gfev_ext {m : ℝ} {F G : NegSobolev d m}
    (h : ∀ k, NegSobolev.coord F k = NegSobolev.coord G k) : F = G := by
  have : (F : lp (fun _ : NonzeroLattice d => ℝ) 2) = G := lp.ext (funext h)
  exact this

theorem gfev_coord_add {m : ℝ} (F G : NegSobolev d m) (k : NonzeroLattice d) :
    NegSobolev.coord (F + G) k = NegSobolev.coord F k + NegSobolev.coord G k := by
  unfold NegSobolev.coord
  exact lp.coeFn_add (F : lp (fun _ : NonzeroLattice d => ℝ) 2) G ▸ rfl

theorem gfev_coord_smul {m : ℝ} (c : ℝ) (F : NegSobolev d m) (k : NonzeroLattice d) :
    NegSobolev.coord (c • F) k = c * NegSobolev.coord F k := rfl

theorem gfev_fc_add {m : ℝ} (F G : NegSobolev d m) (k : NonzeroLattice d) :
    NegSobolev.fourierCoeff (F + G) k = NegSobolev.fourierCoeff F k + NegSobolev.fourierCoeff G k := by
  unfold NegSobolev.fourierCoeff
  rw [gfev_coord_add]; ring

theorem gfev_fc_smul {m : ℝ} (c : ℝ) (F : NegSobolev d m) (k : NonzeroLattice d) :
    NegSobolev.fourierCoeff (c • F) k = c * NegSobolev.fourierCoeff F k := by
  unfold NegSobolev.fourierCoeff
  rw [gfev_coord_smul]; ring

theorem gfev_embed_add {m m' : ℝ} (hmm' : m ≤ m') (F G : NegSobolev d m) :
    NegSobolev.embed m' (F + G) = NegSobolev.embed m' F + NegSobolev.embed m' G := by
  refine gfev_ext fun k => ?_
  rw [gfev_coord_add, gfev_coord_embed hmm', gfev_coord_embed hmm', gfev_coord_embed hmm', gfev_fc_add]
  ring

theorem gfev_embed_smul {m m' : ℝ} (hmm' : m ≤ m') (c : ℝ) (F : NegSobolev d m) :
    NegSobolev.embed m' (c • F) = c • NegSobolev.embed m' F := by
  refine gfev_ext fun k => ?_
  rw [gfev_coord_smul, gfev_coord_embed hmm', gfev_coord_embed hmm', gfev_fc_smul]
  ring

/-- the embedding as a linear map -/
def gfevEmbL {m m' : ℝ} (hmm' : m ≤ m') : NegSobolev d m →ₗ[ℝ] NegSobolev d m' where
  toFun := NegSobolev.embed m'
  map_add' := gfev_embed_add hmm'
  map_smul' := gfev_embed_smul hmm'

theorem gfev_embed_injective {m m' : ℝ} (hmm' : m ≤ m') :
    Function.Injective (NegSobolev.embed m' : NegSobolev d m → NegSobolev d m') := by
  intro F G h
  refine gfev_ext fun k => ?_
  have h1 : NegSobolev.fourierCoeff F k = NegSobolev.fourierCoeff G k := by
    rw [← gfev_fourierCoeff_embed hmm' F, ← gfev_fourierCoeff_embed hmm' G, h]
  unfold NegSobolev.fourierCoeff at h1
  exact mul_left_cancel₀ (Real.rpow_pos_of_pos (Torus.jp_pos k.1) _).ne' h1

theorem gfev_eval_embed {m m' : ℝ} (hmm' : m ≤ m') (F : NegSobolev d m) (φ : Torus d → ℝ) :
    NegSobolev.eval (NegSobolev.embed m' F) φ = NegSobolev.eval F φ := by
  unfold NegSobolev.eval
  exact tsum_congr fun k => by rw [gfev_fourierCoeff_embed hmm']

/-- `E_m ↪ E_m` is the identity -/
theorem gfev_embed_self (m : ℝ) (F : NegSobolev d m) : NegSobolev.embed m F = F := by
  refine gfev_ext fun k => ?_
  rw [gfev_coord_embed le_rfl]
  unfold NegSobolev.fourierCoeff
  rw [← mul_assoc, ← Real.rpow_add (Torus.jp_pos k.1)]
  simp

end HRS.GF
