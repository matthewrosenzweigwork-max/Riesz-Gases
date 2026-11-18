import HRS.Uniform.Q54cAux42

/-!
# Q54c, part 43: identification of the finite-dimensional laws of `Y` and of `Ŷ`
-/

noncomputable section

open MeasureTheory Filter Topology Finset ProbabilityTheory
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.Uniform.Q54c

open HRS HRS.PDE

variable {d : ℕ}

theorem measurable_Asmul_embed {a : ℝ} (A : ℝ) :
    Measurable (fun z : NegSobolev d (a + 2) => A • NegSobolev.embed (a + 4) z) := by
  refine measurable_of_coord fun k => ?_
  have : (fun z : NegSobolev d (a + 2) => NegSobolev.coord (A • NegSobolev.embed (a + 4) z) k) =
      fun z => A * (Lattice.jp k.1 ^ (-(a + 4)) *
        (Lattice.jp k.1 ^ (a + 2) * NegSobolev.coord z k)) := by
    funext z
    have e1 : NegSobolev.coord (A • NegSobolev.embed (a + 4) z) k =
        A * NegSobolev.coord (NegSobolev.embed (a + 4) z) k := rfl
    rw [e1, coord_embed (by linarith) z k]
    rfl
  rw [this]
  exact (((continuous_coord (a + 2) k).measurable.const_mul _).const_mul _).const_mul _

theorem continuous_eval_const {m : ℝ} {ψ : Torus d → ℝ} (hψ : MemSobolev m ψ) :
    Continuous fun F : NegSobolev d m => NegSobolev.eval F ψ := by
  have : (fun F : NegSobolev d m => NegSobolev.eval F ψ) = fun F => inner ℝ F (lpFun m ψ) :=
    funext fun F => eval_lpFun F hψ
  rw [this]
  exact continuous_id.inner continuous_const

theorem coord_eq_eval {m : ℝ} (F : NegSobolev d m) (k : NonzeroLattice d) :
    NegSobolev.coord F k = Lattice.jp k.1 ^ (-m) * NegSobolev.eval F (Torus.realMode k) := by
  rw [eval_realMode]
  unfold NegSobolev.fourierCoeff
  have : Lattice.jp k.1 ^ (-m) * Lattice.jp k.1 ^ m = 1 := by
    rw [← Real.rpow_add (Torus.jp_pos k.1)]; simp
  calc NegSobolev.coord F k = (Lattice.jp k.1 ^ (-m) * Lattice.jp k.1 ^ m) * NegSobolev.coord F k := by
        rw [this, one_mul]
    _ = _ := by ring

theorem measurable_toLp_eval {p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {f : Fin p → Ω → ℝ}
    (hf : ∀ a, Measurable (f a)) : Measurable fun ω => (WithLp.toLp 2 fun a => f a ω : EuclideanSpace ℝ (Fin p)) :=
  (PiLp.continuous_toLp 2 (fun _ : Fin p => ℝ)).measurable.comp (measurable_pi_iff.2 hf)

namespace PdeSetup

variable {P : PdeSetup d} {D : DynData d} {ν₀ : ℝ} {μ : ℝ → Torus d → ℝ} (h : P.Data D ν₀ μ)

include h

theorem Data.cov_integrand_eq (hn2 : (d : ℝ) / 2 + 2 < (P.n : ℝ)) {q : ℝ} (hq : 0 ≤ q) {ta tb : ℝ}
    (hta : ta ∈ Set.Icc 0 P.T) (htb : tb ∈ Set.Icc 0 P.T) {φa φb : Torus d → ℝ}
    (hφa : Torus.IsSmooth φa) (hφb : Torus.IsSmooth φb) {σ : ℝ} (hσ : σ ∈ Set.Icc 0 (min ta tb)) :
    covDens (P.n : ℝ) q P.T μ σ ((P.pd D μ).y ta φa σ) ((P.pd D μ).y tb φb σ) =
      2 * q * ∫ x, inner ℝ (Torus.grad (propagator D μ σ ta φa) x)
        (Torus.grad (propagator D μ σ tb φb) x) * μ σ x := by
  have hσa : σ ∈ Set.Icc 0 ta := ⟨hσ.1, hσ.2.trans (min_le_left _ _)⟩
  have hσb : σ ∈ Set.Icc 0 tb := ⟨hσ.1, hσ.2.trans (min_le_right _ _)⟩
  have hσT : σ ∈ Set.Icc 0 P.T := ⟨hσ.1, hσa.2.trans hta.2⟩
  rw [covDens_of_mem hσT, h.y_eq hta hφa hσa, h.y_eq htb hφb hσb]
  have hle : (P.n : ℝ) ≤ P.lev := by have := lev_ge_n2 (P := P); linarith
  have ra := h.prop_regular hta hφa hσa
  have rb := h.prop_regular htb hφb hσb
  have hρ := h.hA.hμ.prob σ hσT
  have hρc : Continuous (μ σ) :=
    HRS.PDE.ClassicalAux.continuous_of_isCk (HRS.PDE.ClassicalAux.isCk_of_le
      (by exact_mod_cast (by omega : 1 ≤ P.n + 4 + 3)) (h.hA.hμ.smooth σ hσT))
  exact covForm_lpFun hn2 hq hρc hρ.nonneg (h.memSob_prop hta hφa hσa hle) ra.1 ra.2
    (h.memSob_prop htb hφb hσb hle) rb.1 rb.2

end PdeSetup

end HRS.Uniform.Q54c
