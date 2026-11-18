import HRS.Uniform.Q54cAux13
import HRS.Uniform.Q54Aux14

/-!
# Q54c, part 14: functions and coefficient sequences as elements of `E_j`

* `lpFun a ψ` is the element of `E_a` representing a function `ψ ∈ H^a` (coordinates `⟨k⟩^a ψ̂(k)`);
  `0` when `ψ ∉ H^a`.  It is linear on `H^a`, kills constants, and `eval F ψ = ⟨F, lpFun a ψ⟩`.
* `Adm j c`: a real, absolutely summable coefficient sequence in `H^j`.
* `Sv j c = (Re c(0), lpFun j (toFun c)) ∈ ℝ × E_j`: the full Sobolev vector; `‖Sv j c‖ ≤ ‖c‖_{H^j}
  ≤ 2 ‖Sv j c‖`, and `Sv` is linear on admissible sequences.
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.Uniform.Q54c

open HRS HRS.PDE

variable {d : ℕ}

open Classical in
/-- the element of `E_a` representing `ψ ∈ H^a` (coordinates `⟨k⟩^a ψ̂(k)`), `0` otherwise. -/
def lpFun (a : ℝ) (ψ : Torus d → ℝ) : NegSobolev d a :=
  if h : MemSobolev a ψ then HRS.Uniform.Q54.lpOf a h else 0

theorem lpFun_of_mem {a : ℝ} {ψ : Torus d → ℝ} (h : MemSobolev a ψ) :
    lpFun a ψ = HRS.Uniform.Q54.lpOf a h := by
  unfold lpFun; rw [dif_pos h]

theorem lpFun_of_not {a : ℝ} {ψ : Torus d → ℝ} (h : ¬ MemSobolev a ψ) : lpFun a ψ = 0 := by
  unfold lpFun; rw [dif_neg h]

theorem coord_lpFun {a : ℝ} {ψ : Torus d → ℝ} (h : MemSobolev a ψ) (k : NonzeroLattice d) :
    NegSobolev.coord (lpFun a ψ) k = Lattice.jp k.1 ^ a * Torus.funRealCoeff ψ k := by
  rw [lpFun_of_mem h]; rfl

theorem norm_lpFun_le (a : ℝ) (ψ : Torus d → ℝ) : ‖lpFun a ψ‖ ≤ sobolevNorm a ψ := by
  by_cases h : MemSobolev a ψ
  · rw [lpFun_of_mem h]; exact HRS.Uniform.Q54.norm_lpOf_le_sobolev a h
  · rw [lpFun_of_not h, norm_zero]; exact Real.sqrt_nonneg _

theorem eval_lpFun {a : ℝ} (F : NegSobolev d a) {ψ : Torus d → ℝ} (h : MemSobolev a ψ) :
    NegSobolev.eval F ψ = inner ℝ F (lpFun a ψ) := by
  rw [lpFun_of_mem h]; exact HRS.Uniform.Q54.eval_eq_inner a F h

theorem NegSobolev_ext {m : ℝ} {F G : NegSobolev d m}
    (h : ∀ k, NegSobolev.coord F k = NegSobolev.coord G k) : F = G := by
  refine lp.ext (funext fun k => ?_)
  exact h k

theorem coord_add' {m : ℝ} (F G : NegSobolev d m) (k : NonzeroLattice d) :
    NegSobolev.coord (F + G) k = NegSobolev.coord F k + NegSobolev.coord G k :=
  congrFun (lp.coeFn_add (E := fun _ : NonzeroLattice d => ℝ) (p := 2)
    (show lp (fun _ : NonzeroLattice d => ℝ) 2 from F) (show lp (fun _ : NonzeroLattice d => ℝ) 2 from G)) k

theorem coord_smul' {m : ℝ} (c : ℝ) (F : NegSobolev d m) (k : NonzeroLattice d) :
    NegSobolev.coord (c • F) k = c * NegSobolev.coord F k := rfl

theorem funRealCoeff_comb {f g : Torus d → ℝ} (hf : MemLp f 2 (volume : Measure (Torus d)))
    (hg : MemLp g 2 (volume : Measure (Torus d))) (α β : ℝ) (k : NonzeroLattice d) :
    Torus.funRealCoeff (fun x => α * f x + β * g x) k =
      α * Torus.funRealCoeff f k + β * Torus.funRealCoeff g k := by
  have h := HRS.Uniform.Q54.funRealCoeff_finset_sum (Finset.univ : Finset (Fin 2))
    (fun i => if i = 0 then α else β) (fun i => if i = 0 then f else g)
    (fun l _ => by split_ifs <;> assumption) k
  simpa [Fin.sum_univ_two] using h

theorem memSobolev_comb {a : ℝ} {f g : Torus d → ℝ} (hf : MemSobolev a f) (hg : MemSobolev a g)
    (α β : ℝ) : MemSobolev a (fun x => α * f x + β * g x) := by
  refine ⟨(hf.1.const_mul α).add (hg.1.const_mul β), ?_⟩
  have h1 := hf.2
  have h2 := hg.2
  refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_)
    (((h1.mul_left (2 * α ^ 2)).add (h2.mul_left (2 * β ^ 2))))
  · exact mul_nonneg (Real.rpow_nonneg (Torus.jp_pos k.1).le _) (sq_nonneg _)
  · rw [funRealCoeff_comb hf.1 hg.1]
    have hw : 0 ≤ Lattice.jp k.1 ^ (2 * a) := Real.rpow_nonneg (Torus.jp_pos k.1).le _
    have := mul_le_mul_of_nonneg_left
      (show (α * Torus.funRealCoeff f k + β * Torus.funRealCoeff g k) ^ 2 ≤
        2 * α ^ 2 * Torus.funRealCoeff f k ^ 2 + 2 * β ^ 2 * Torus.funRealCoeff g k ^ 2 by
        nlinarith [sq_nonneg (α * Torus.funRealCoeff f k - β * Torus.funRealCoeff g k)]) hw
    refine this.trans (le_of_eq ?_)
    ring

theorem lpFun_comb {a : ℝ} {f g : Torus d → ℝ} (hf : MemSobolev a f) (hg : MemSobolev a g)
    (α β : ℝ) :
    lpFun a (fun x => α * f x + β * g x) = α • lpFun a f + β • lpFun a g := by
  have hc := memSobolev_comb hf hg α β
  refine NegSobolev_ext fun k => ?_
  rw [coord_lpFun hc, coord_add', coord_smul', coord_smul', coord_lpFun hf, coord_lpFun hg,
    funRealCoeff_comb hf.1 hg.1]
  ring

theorem funRealCoeff_const (c : ℝ) (k : NonzeroLattice d) :
    Torus.funRealCoeff (fun _ : Torus d => c) k = 0 := by
  have h := HRS.Uniform.Q48b.q48b_funRealCoeff_add_const (d := d) (g := fun _ => (0 : ℝ))
    (memLp_const 0) c k
  have h0 : Torus.funRealCoeff (fun _ : Torus d => (0 : ℝ)) k = 0 := by
    unfold Torus.funRealCoeff; simp
  simpa [h0] using h

theorem memSobolev_const (a c : ℝ) : MemSobolev a (fun _ : Torus d => c) := by
  refine ⟨memLp_const c, ?_⟩
  simp only [funRealCoeff_const]
  simpa using (summable_zero : Summable fun _ : NonzeroLattice d => (0 : ℝ))

theorem lpFun_const (a c : ℝ) : lpFun a (fun _ : Torus d => c) = 0 := by
  refine NegSobolev_ext fun k => ?_
  rw [coord_lpFun (memSobolev_const a c), funRealCoeff_const, mul_zero]
  rfl

end HRS.Uniform.Q54c
