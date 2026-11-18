import HRS.Main.GFB3Aux7
import HRS.Main.GFB1Aux1

/-!
# Packet GFB3, part 8: `GFEvo` forces `m ≥ γ`; the Riemann-sum pairing identity

* `gfb3_m_ge_gamma`: `GFEvo S M N m K EV` is unsatisfiable for `m < γ` (the embedding `E_γ → E_m` would be unbounded and
  not an isometry), so `γ ≤ m` may be used for free.
* `gfb3_eval_embed`: pairing commutes with the embedding.
* `gfb3_riemann_eval`: pairing of the Riemann sums of the stochastic convolution with a smooth test function.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.GF

open HRS HRS.Uniform HRS.Uniform.Q54c

variable {d : ℕ}

/-- The basis vector `e_k ∈ E_γ`. -/
def gfb3_e (γ : ℝ) (k : NonzeroLattice d) : NegSobolev d γ :=
  ((lp.single 2 k (1 : ℝ) : lp (fun _ : NonzeroLattice d => ℝ) 2) : NegSobolev d γ)

lemma gfb3_norm_e (γ : ℝ) (k : NonzeroLattice d) : ‖gfb3_e γ k‖ = 1 := by
  show ‖(lp.single 2 k (1 : ℝ) : lp (fun _ : NonzeroLattice d => ℝ) 2)‖ = 1
  rw [lp.norm_single (by norm_num)]; simp

lemma gfb3_coord_e (γ : ℝ) (k k' : NonzeroLattice d) :
    NegSobolev.coord (gfb3_e γ k) k' = if k' = k then 1 else 0 := by
  unfold NegSobolev.coord gfb3_e
  show (lp.single 2 k (1 : ℝ) : lp (fun _ : NonzeroLattice d => ℝ) 2) k' = _
  rw [lp.single_apply]
  by_cases h : k' = k
  · subst h; simp
  · simp [h]

lemma gfb3_embed_e (γ m : ℝ) (k : NonzeroLattice d) :
    NegSobolev.embed m (gfb3_e γ k) = (Lattice.jp k.1 ^ (γ - m)) • gfb3_e m k := by
  have hmem : Memℓp (fun k' : NonzeroLattice d => Lattice.jp k'.1 ^ (-m) *
      NegSobolev.fourierCoeff (gfb3_e γ k) k') 2 := by
    rw [Torus.memℓp_two_iff]
    refine summable_of_ne_finset_zero (s := {k}) fun k' hk' => ?_
    have : k' ≠ k := by simpa using hk'
    simp [NegSobolev.fourierCoeff, gfb3_coord_e, this]
  refine NegSobolev_ext fun k' => ?_
  unfold NegSobolev.embed
  rw [NegSobolev.coord_ofSeq_of_mem _ hmem]
  have hj := Torus.jp_pos k'.1
  show _ = Lattice.jp k.1 ^ (γ - m) * NegSobolev.coord (gfb3_e m k) k'
  rw [gfb3_coord_e]
  by_cases h : k' = k
  · subst h
    simp only [NegSobolev.fourierCoeff, gfb3_coord_e, if_true, mul_one]
    rw [← Real.rpow_add hj]
    congr 1; ring
  · simp [NegSobolev.fourierCoeff, gfb3_coord_e, h]

lemma gfb3_norm_embed_e (γ m : ℝ) (hm : m < γ) (k : NonzeroLattice d) :
    ‖NegSobolev.embed m (gfb3_e γ k)‖ = Lattice.jp k.1 ^ (γ - m) := by
  rw [gfb3_embed_e, norm_smul, gfb3_norm_e, mul_one, Real.norm_of_nonneg
    (Real.rpow_nonneg (Torus.jp_pos k.1).le _)]

theorem gfb3_m_ge_gamma (S : GeneralSetup d) (M : Matrix (Fin d) (Fin d) ℝ) (N : ℕ) (m K : ℝ)
    (EV : EvolData (NegSobolev d (S.γ : ℝ)) (NegSobolev d m)) (hEV : GFEvo S M N m K EV) :
    (S.γ : ℝ) ≤ m := by
  by_contra hlt
  push_neg at hlt
  have hs0 : 0 < (S.γ : ℝ) - m := by linarith
  obtain ⟨n, hn1, hn⟩ : ∃ n : ℕ, 1 ≤ n ∧ max K 1 + 1 < (n : ℝ) ^ ((S.γ : ℝ) - m) := by
    have h := (tendsto_rpow_atTop hs0).comp tendsto_natCast_atTop_atTop
    obtain ⟨n, hn⟩ := ((h.eventually (eventually_gt_atTop (max K 1 + 1))).and
      (eventually_ge_atTop 1)).exists
    exact ⟨n, hn.2, hn.1⟩
  have hd0 : 0 < d := by have := S.hd; omega
  set i₀ : Fin d := ⟨0, hd0⟩ with hi₀
  set k₀ : Lattice d := Pi.single i₀ (n : ℤ) with hk₀def
  have hk₀ : k₀ ≠ 0 := by
    intro h
    have := congrFun h i₀
    simp [hk₀def] at this
    omega
  set k : NonzeroLattice d := ⟨k₀, hk₀⟩ with hkdef
  have hjp : (n : ℝ) ≤ Lattice.jp k₀ := by
    have h := HRS.Uniform.Q14.q14_two_pi_k_le k₀ i₀
    have h2 : |((k₀ i₀ : ℤ) : ℝ)| = n := by simp [hk₀def]
    rw [h2] at h
    have hpi := Real.pi_gt_three
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  have hnorm : ‖EV.j (gfb3_e (S.γ : ℝ) k)‖ = Lattice.jp k₀ ^ ((S.γ : ℝ) - m) := by
    rw [hEV.j_eq]
    exact gfb3_norm_embed_e (S.γ : ℝ) m hlt k
  have hbig : max K 1 + 1 < Lattice.jp k₀ ^ ((S.γ : ℝ) - m) :=
    hn.trans_le (Real.rpow_le_rpow (Nat.cast_nonneg _) hjp hs0.le)
  rcases hEV.maxHyp.2 with htwo | hdis
  · have h1 := htwo.2.1
    have h2 := EV.j.le_opNorm (gfb3_e (S.γ : ℝ) k)
    rw [gfb3_norm_e, mul_one, hnorm] at h2
    linarith [le_max_left K 1]
  · have h1 := hdis.1 (gfb3_e (S.γ : ℝ) k)
    rw [gfb3_norm_e, hnorm] at h1
    linarith [le_max_right K 1]

lemma gfb3_fourierCoeff_embed (m m' : ℝ) (hmm' : m ≤ m') (F : NegSobolev d m) (k : NonzeroLattice d) :
    NegSobolev.fourierCoeff (NegSobolev.embed m' F) k = NegSobolev.fourierCoeff F k := by
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
  have hmem : Memℓp (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-m') *
      NegSobolev.fourierCoeff F k) 2 := by
    rw [Torus.memℓp_two_iff]
    refine Summable.of_nonneg_of_le (fun k => sq_nonneg _) (fun k => ?_) h3
    calc _ = |Lattice.jp k.1 ^ (-m') * NegSobolev.fourierCoeff F k| ^ 2 := (sq_abs _).symm
      _ ≤ |NegSobolev.coord F k| ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hcoord k) 2
      _ = _ := sq_abs _
  unfold NegSobolev.fourierCoeff
  rw [NegSobolev.embed]
  rw [show NegSobolev.coord (NegSobolev.ofSeq m' (NegSobolev.fourierCoeff F)) k =
      Lattice.jp k.1 ^ (-m') * NegSobolev.fourierCoeff F k from NegSobolev.coord_ofSeq_of_mem _ hmem k]
  have hj := Torus.jp_pos k.1
  rw [← mul_assoc, ← Real.rpow_add hj]
  simp [NegSobolev.fourierCoeff]

lemma gfb3_eval_embed (m m' : ℝ) (hmm' : m ≤ m') (F : NegSobolev d m) (ψ : Torus d → ℝ) :
    NegSobolev.eval (NegSobolev.embed m' F) ψ = NegSobolev.eval F ψ := by
  unfold NegSobolev.eval
  exact tsum_congr fun k => by rw [gfb3_fourierCoeff_embed m m' hmm' F k]

lemma gfb3_riemann_eval (S : GeneralSetup d) (M : Matrix (Fin d) (Fin d) ℝ) (N : ℕ) (m K : ℝ)
    (EV : EvolData (NegSobolev d (S.γ : ℝ)) (NegSobolev d m)) (hEV : GFEvo S M N m K EV)
    {Ω : Type*} (Mart : ℝ → Ω → NegSobolev d (S.γ : ℝ)) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) S.T)
    (φ : Torus d → ℝ) (hφ : Torus.IsSmooth φ) {n : ℕ} (r : Fin (n + 1) → ℝ) (hr0 : r 0 = 0)
    (hrt : r (Fin.last n) = t) (hmono : Monotone r) (ω : Ω) :
    NegSobolev.eval (riemannSum EV.VE EV.j Mart t r ω) φ =
      ∑ i : Fin n, NegSobolev.eval (Mart (r i.succ) ω - Mart (r i.castSucc) ω)
        (propagator (S.dynM M N) (S.ρ N) (r i.castSucc) t φ) := by
  have hγm := gfb3_m_ge_gamma S M N m K EV hEV
  have hmem : MemSobolev m φ := (gf_smooth_mem_proof hφ m).2
  unfold riemannSum
  rw [eval_lpFun _ hmem, sum_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← eval_lpFun _ hmem]
  have h0 : 0 ≤ r i.castSucc := by
    rw [← hr0]; exact hmono (Fin.zero_le _)
  have h1 : r i.castSucc ≤ t := by
    rw [← hrt]; exact hmono (Fin.le_last _)
  rw [hEV.dual (r i.castSucc) t h0 h1 ht.2 _ φ hφ, hEV.j_eq, gfb3_eval_embed _ _ hγm]

end HRS.GF
