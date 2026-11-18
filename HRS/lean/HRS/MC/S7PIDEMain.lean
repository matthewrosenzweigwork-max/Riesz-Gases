import HRS.MC.S7PIDEMat
import HRS.MC.S7PIDEGrad
import HRS.MC.S7PIDR

/-!
# Packet PI-D, sub-packet E: `s7_PID_expansion` (Fourier expansion of the gradient product)

Proof of `HRS.MC.Sec7.PIDPlan.s7_PID_expansion` (statement copied verbatim; the tie is in `S7PIDETie.lean`).

Route (D6c).  Write `c^a_k = (V^{t_a,u} e_k)(φ_a) = (U^{u,t_a}φ_a)^(k)` (`S7PIDE_eval_V`), `U^a = U^{u,t_a}φ_a ∈ H^L` with `L` large.
Then `∇U^a = ∑_k c^a_k ∇e_k` pointwise (`S7PIDE_grad_series`), so the real Fourier coefficient `Ĝ_j` of `G = ∇U^a·∇U^b` is
`∑_{k,l} c^a_k c^b_l (∇e_k·∇e_l)^(j)` (`S7PIDE_coeff_hasSum`).  With `F(k,l,j) = ẑ_j (∇e_k·∇e_l)^(j) c^a_k c^b_l`, Cauchy--Schwarz
in `j` (`S7PIDE_cs`, `s7_PID_gradprod_proof`) and the decay of `c^a_k` give `∑ |F| < ∞`; summing in `j` first or in `(k,l)` first
gives the claimed `HasSum` (and `z(G) = ∑_j ẑ_j Ĝ_j`).
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7PIDE

open HRS HRS.Sec7 HRS.MC.Sec7.PID

variable {d : ℕ}

/-- Coefficient decay of an `H^L` function, summed against a polynomial weight. -/
theorem S7PIDE_coeff_summable {L : ℕ} {U : Torus d → ℝ} (hU : MemSobolev (L : ℝ) U) (q : ℝ)
    (hq : (d : ℝ) + q < L) :
    Summable fun k : NonzeroLattice d => |Torus.funRealCoeff U k| * Lattice.jp k.1 ^ q := by
  have hs := summable_jp_rpow (d := d) (((L : ℝ) - q) / 2) (by linarith)
  refine Summable.of_nonneg_of_le
    (fun k => mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (Torus.jp_pos k.1).le _)) (fun k => ?_)
    (hs.mul_left (sobolevNorm (L : ℝ) U))
  have h1 := S7PIDM.S7PIDM_coeff_le hU k
  have hj := Torus.jp_pos k.1
  calc |Torus.funRealCoeff U k| * Lattice.jp k.1 ^ q
      ≤ (Lattice.jp k.1 ^ (-(L : ℝ)) * sobolevNorm (L : ℝ) U) * Lattice.jp k.1 ^ q :=
        mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hj.le _)
    _ = sobolevNorm (L : ℝ) U * Lattice.jp k.1 ^ (-(2 * (((L : ℝ) - q) / 2))) := by
        rw [show -(2 * (((L : ℝ) - q) / 2)) = -(L : ℝ) + q by ring, Real.rpow_add hj]
        ring

/-- Cauchy--Schwarz for the pairing of `z ∈ E_r` (given by its coefficients) with an `H^r` function. -/
theorem S7PIDE_cs {r : ℝ} (zc : NonzeroLattice d → ℝ)
    (hz : Summable fun j : NonzeroLattice d => (Lattice.jp j.1 ^ (-r) * zc j) ^ 2) (g : Torus d → ℝ)
    (hg : Summable fun j : NonzeroLattice d => Lattice.jp j.1 ^ (2 * r) * Torus.funRealCoeff g j ^ 2) :
    Summable (fun j : NonzeroLattice d => |zc j * Torus.funRealCoeff g j|) ∧
      ∑' j : NonzeroLattice d, |zc j * Torus.funRealCoeff g j| ≤
        Real.sqrt (∑' j : NonzeroLattice d, (Lattice.jp j.1 ^ (-r) * zc j) ^ 2) *
          Real.sqrt (∑' j : NonzeroLattice d, Lattice.jp j.1 ^ (2 * r) * Torus.funRealCoeff g j ^ 2) := by
  have hy2 : Summable fun j : NonzeroLattice d => |Lattice.jp j.1 ^ r * Torus.funRealCoeff g j| ^ 2 := by
    refine hg.congr fun j => ?_
    rw [sq_abs, mul_pow, Torus.jp_rpow_sq]
  have hx2 : Summable fun j : NonzeroLattice d => |Lattice.jp j.1 ^ (-r) * zc j| ^ 2 := by
    simpa only [sq_abs] using hz
  have hcs := Torus.cs_tsum (fun j : NonzeroLattice d => |Lattice.jp j.1 ^ (-r) * zc j|)
    (fun j : NonzeroLattice d => |Lattice.jp j.1 ^ r * Torus.funRealCoeff g j|)
    (fun _ => abs_nonneg _) (fun _ => abs_nonneg _) hx2 hy2
  have hxy : ∀ j : NonzeroLattice d, |Lattice.jp j.1 ^ (-r) * zc j| *
      |Lattice.jp j.1 ^ r * Torus.funRealCoeff g j| = |zc j * Torus.funRealCoeff g j| := by
    intro j
    have hj := Torus.jp_pos j.1
    have h1 : Lattice.jp j.1 ^ (-r) * Lattice.jp j.1 ^ r = 1 := by
      rw [← Real.rpow_add hj]; simp
    rw [← abs_mul]
    congr 1
    linear_combination (zc j * Torus.funRealCoeff g j) * h1
  simp_rw [hxy] at hcs
  refine ⟨hcs.1, hcs.2.trans (le_of_eq ?_)⟩
  congr 2
  · simp_rw [sq_abs]
  · refine tsum_congr fun j => ?_
    rw [sq_abs, mul_pow, Torus.jp_rpow_sq]

/-- **Proof of `s7_PID_expansion`** (statement verbatim from `HRS.MC.Sec7.PIDPlan`). -/
theorem s7_PID_expansion_proof (R : Regime d) (r : ℝ) (hr : r = 2 * (d : ℝ) + 6) (m : ℝ)
    (hm : 3 * (d : ℝ) + 8 < m)
    (T : ℝ) (hT : 0 < T) (φa φb : Torus d → ℝ) (hφa : Torus.IsSmooth φa) (hφb : Torus.IsSmooth φb)
    (u ta tb : ℝ) (hu : 0 ≤ u) (hua : u ≤ ta) (hub : u ≤ tb) (hta : ta ≤ T) (htb : tb ≤ T)
    (z : NegSobolev d m)
    (hz : Memℓp (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-r) * NegSobolev.fourierCoeff z k) 2) :
    HasSum (fun p : NonzeroLattice d × NonzeroLattice d =>
        NegSobolev.eval z (gradProd p.1 p.2) *
          NegSobolev.eval (Vprop R.D R.ρ m ta u (modeVec m p.1)) φa *
          NegSobolev.eval (Vprop R.D R.ρ m tb u (modeVec m p.2)) φb)
      (NegSobolev.eval z (fun x => inner ℝ (Torus.grad (propagator R.D R.ρ u ta φa) x)
        (Torus.grad (propagator R.D R.ρ u tb φb) x))) := by
  classical
  -- the level `L`
  obtain ⟨L, hLdef⟩ : ∃ L : ℕ, L = ⌈m⌉₊ + 3 * d + 12 + PDE.mStar d := ⟨_, rfl⟩
  have hL : PDE.mStar d ≤ L := by omega
  have hLm : ⌊m⌋₊ ≤ L := by
    have := Nat.floor_le_ceil m
    omega
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hLr : 3 * (d : ℝ) + 12 ≤ (L : ℝ) := by
    have : ((3 * d + 12 : ℕ) : ℝ) ≤ (L : ℝ) := by exact_mod_cast (by omega : 3 * d + 12 ≤ L)
    push_cast at this
    linarith
  have H := S7PIDM.S7PIDM_pie R T hT L hL
  -- the propagated test functions
  have hdoma := S7PIDE_dom H hu hua hta (HRS.A33.dom_smooth (J := L) hφa)
  have hdomb := S7PIDE_dom H hu hub htb (HRS.A33.dom_smooth (J := L) hφb)
  set Ua := propagator R.D R.ρ u ta φa with hUa
  set Ub := propagator R.D R.ρ u tb φb with hUb
  have hCk1a : Torus.IsCk 1 Ua := HRS.PDE.ClassicalAux.isCk_of_le (by norm_num)
    (HRS.A34.a34_isCk2 L hL hdoma.1 hdoma.2)
  have hCk1b : Torus.IsCk 1 Ub := HRS.PDE.ClassicalAux.isCk_of_le (by norm_num)
    (HRS.A34.a34_isCk2 L hL hdomb.1 hdomb.2)
  have hn : (d : ℝ) / 2 + 2 < (L : ℝ) := by linarith
  -- the coefficients
  set ca : NonzeroLattice d → ℝ := fun k => Torus.funRealCoeff Ua k with hca
  set cb : NonzeroLattice d → ℝ := fun k => Torus.funRealCoeff Ub k with hcb
  have hVa : ∀ k, NegSobolev.eval (Vprop R.D R.ρ m ta u (modeVec m k)) φa = ca k := fun k =>
    S7PIDE_eval_V R m hm T hT L hL hLm hφa hu hua hta k
  have hVb : ∀ k, NegSobolev.eval (Vprop R.D R.ρ m tb u (modeVec m k)) φb = cb k := fun k =>
    S7PIDE_eval_V R m hm T hT L hL hLm hφb hu hub htb k
  have hr0 : 0 ≤ r := by rw [hr]; linarith
  -- summability of the weighted coefficients
  have hsa1 : Summable fun k : NonzeroLattice d => |ca k| * Lattice.jp k.1 := by
    have := S7PIDE_coeff_summable hdoma.2 1 (by linarith)
    simpa using this
  have hsb1 : Summable fun k : NonzeroLattice d => |cb k| * Lattice.jp k.1 := by
    have := S7PIDE_coeff_summable hdomb.2 1 (by linarith)
    simpa using this
  have hsa : Summable fun k : NonzeroLattice d => |ca k| * Lattice.jp k.1 ^ (r + 1) :=
    S7PIDE_coeff_summable hdoma.2 (r + 1) (by rw [hr]; linarith)
  have hsb : Summable fun k : NonzeroLattice d => |cb k| * Lattice.jp k.1 ^ (r + 1) :=
    S7PIDE_coeff_summable hdomb.2 (r + 1) (by rw [hr]; linarith)
  -- gradient expansions
  have hGa : ∀ (x : Torus d) (i : Fin d), HasSum (fun k => ca k * Torus.grad (Torus.realMode k) x i)
      (Torus.grad Ua x i) := fun x i =>
    S7PIDE_grad_series hn hdoma.2 hdoma.1 hCk1a x i
  have hGb : ∀ (x : Torus d) (i : Fin d), HasSum (fun k => cb k * Torus.grad (Torus.realMode k) x i)
      (Torus.grad Ub x i) := fun x i =>
    S7PIDE_grad_series hn hdomb.2 hdomb.1 hCk1b x i
  -- the Fourier product bound
  obtain ⟨Cg, hCg0, hCg⟩ := S7PIDR.s7_PID_gradprod_proof (d := d) r hr0
  -- the coefficients of `z`
  set zc : NonzeroLattice d → ℝ := fun j => NegSobolev.fourierCoeff z j with hzc
  have hzsq : Summable fun j : NonzeroLattice d => (Lattice.jp j.1 ^ (-r) * zc j) ^ 2 :=
    (Torus.memℓp_two_iff _).1 hz
  set Z : ℝ := Real.sqrt (∑' j : NonzeroLattice d, (Lattice.jp j.1 ^ (-r) * zc j) ^ 2) with hZ
  -- the summand `F` on `(k,l) × j`
  set F : (NonzeroLattice d × NonzeroLattice d) × NonzeroLattice d → ℝ := fun q =>
    (zc q.2 * Torus.funRealCoeff (gradProd q.1.1 q.1.2) q.2) * (ca q.1.1 * cb q.1.2) with hF
  -- bound in `j` for fixed `(k,l)`
  have hCS : ∀ p : NonzeroLattice d × NonzeroLattice d,
      Summable (fun j : NonzeroLattice d => |zc j * Torus.funRealCoeff (gradProd p.1 p.2) j|) ∧
      ∑' j : NonzeroLattice d, |zc j * Torus.funRealCoeff (gradProd p.1 p.2) j| ≤
        Z * (Cg * Lattice.jp p.1.1 ^ (r + 1) * Lattice.jp p.2.1 ^ (r + 1)) := by
    intro p
    obtain ⟨hmem, hnorm⟩ := hCg p.1 p.2
    obtain ⟨h1, h2⟩ := S7PIDE_cs (r := r) zc hzsq (gradProd p.1 p.2) hmem.2
    refine ⟨h1, h2.trans ?_⟩
    refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
    refine le_trans ?_ hnorm
    unfold sobolevNorm
    exact Real.sqrt_le_sqrt (by linarith [sq_nonneg (Torus.mean (gradProd p.1 p.2))])
  -- summability of `F`
  have hFsum : Summable F := by
    refine Summable.of_norm ?_
    have hnn : 0 ≤ fun q => ‖F q‖ := fun q => norm_nonneg _
    refine (summable_prod_of_nonneg hnn).2 ⟨fun p => ?_, ?_⟩
    · have := (hCS p).1.mul_right (|ca p.1| * |cb p.2|)
      refine this.congr fun j => ?_
      simp only [hF, Real.norm_eq_abs, abs_mul]
    · have hrhs : Summable fun p : NonzeroLattice d × NonzeroLattice d =>
          (Z * Cg) * ((|ca p.1| * Lattice.jp p.1.1 ^ (r + 1)) * (|cb p.2| * Lattice.jp p.2.1 ^ (r + 1))) :=
        (Summable.mul_of_nonneg hsa hsb
          (fun k => mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (Torus.jp_pos k.1).le _))
          (fun k => mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (Torus.jp_pos k.1).le _))).mul_left _
      refine Summable.of_nonneg_of_le (fun p => tsum_nonneg fun j => norm_nonneg _) (fun p => ?_) hrhs
      have e : ∀ j, ‖F (p, j)‖ = |zc j * Torus.funRealCoeff (gradProd p.1 p.2) j| *
          (|ca p.1| * |cb p.2|) := fun j => by
        simp only [hF, Real.norm_eq_abs, abs_mul]
      simp_rw [e]
      rw [tsum_mul_right]
      calc (∑' j, |zc j * Torus.funRealCoeff (gradProd p.1 p.2) j|) * (|ca p.1| * |cb p.2|)
          ≤ (Z * (Cg * Lattice.jp p.1.1 ^ (r + 1) * Lattice.jp p.2.1 ^ (r + 1))) *
            (|ca p.1| * |cb p.2|) :=
            mul_le_mul_of_nonneg_right (hCS p).2 (mul_nonneg (abs_nonneg _) (abs_nonneg _))
        _ = (Z * Cg) * ((|ca p.1| * Lattice.jp p.1.1 ^ (r + 1)) * (|cb p.2| * Lattice.jp p.2.1 ^ (r + 1))) := by
            ring
  -- fibres over `(k,l)`
  have hfib1 : ∀ p : NonzeroLattice d × NonzeroLattice d, HasSum (fun j => F (p, j))
      (NegSobolev.eval z (gradProd p.1 p.2) * (ca p.1 * cb p.2)) := by
    intro p
    have hs : Summable fun j : NonzeroLattice d => zc j * Torus.funRealCoeff (gradProd p.1 p.2) j :=
      Summable.of_norm ((hCS p).1.congr fun j => by rw [Real.norm_eq_abs])
    exact hs.hasSum.mul_right (ca p.1 * cb p.2)
  -- fibres over `j`
  have hfib2 : ∀ j : NonzeroLattice d, HasSum (fun p => F (p, j))
      (zc j * Torus.funRealCoeff (fun x => inner ℝ (Torus.grad Ua x) (Torus.grad Ub x)) j) := by
    intro j
    have h := (S7PIDE_coeff_hasSum ca cb Ua Ub hsa1 hsb1 hGa hGb j).mul_left (zc j)
    have e : (fun p : NonzeroLattice d × NonzeroLattice d => F (p, j)) = fun p =>
        zc j * (ca p.1 * cb p.2 * Torus.funRealCoeff (gradProd p.1 p.2) j) := by
      funext p; simp only [hF]; ring
    rw [e]
    exact h
  have hA := hFsum.hasSum
  have h1 : HasSum (fun p : NonzeroLattice d × NonzeroLattice d =>
      NegSobolev.eval z (gradProd p.1 p.2) * (ca p.1 * cb p.2)) (∑' q, F q) := hA.prod_fiberwise hfib1
  have h2 : HasSum (fun j : NonzeroLattice d =>
      zc j * Torus.funRealCoeff (fun x => inner ℝ (Torus.grad Ua x) (Torus.grad Ub x)) j) (∑' q, F q) :=
    ((Equiv.prodComm (NonzeroLattice d) (NonzeroLattice d × NonzeroLattice d)).hasSum_iff.2 hA).prod_fiberwise
      (fun j => hfib2 j)
  have hev : NegSobolev.eval z (fun x => inner ℝ (Torus.grad Ua x) (Torus.grad Ub x)) = ∑' q, F q := by
    unfold NegSobolev.eval
    exact h2.tsum_eq
  rw [hev]
  have e : (fun p : NonzeroLattice d × NonzeroLattice d =>
      NegSobolev.eval z (gradProd p.1 p.2) *
        NegSobolev.eval (Vprop R.D R.ρ m ta u (modeVec m p.1)) φa *
        NegSobolev.eval (Vprop R.D R.ρ m tb u (modeVec m p.2)) φb) = fun p =>
      NegSobolev.eval z (gradProd p.1 p.2) * (ca p.1 * cb p.2) := by
    funext p
    rw [hVa, hVb, mul_assoc]
  rw [e]
  exact h1

end HRS.MC.Sec7.S7PIDE

end
