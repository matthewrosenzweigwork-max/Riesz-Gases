import HRS.Uniform.Q54cAux17

/-!
# Q54c, part 18: bounds, derivative and Lipschitz estimate of the coefficient flow

(All at integer Sobolev levels; see `Q54cAux17`.)
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.Uniform.Q54c

open HRS HRS.PDE

variable {d : ℕ}

theorem quot_adm {j : ℝ} {F G : ℝ → Coeff d} {s : Set ℝ} {τ τ' : ℝ} (hF' : Adm j (F τ'))
    (hF : Adm j (F τ)) (hG : Adm j (G τ)) :
    Adm j (fun k => (F τ' k - F τ k) / ((τ' - τ : ℝ) : ℂ) - G τ k) := by
  have := ((hF'.comb hF ((τ' - τ)⁻¹) (-(τ' - τ)⁻¹)).comb hG 1 (-1))
  convert this using 1
  funext k
  push_cast
  ring

/-- `hasDerivWithinAt_Sv` with the convergence assumed at a higher level `j'`. -/
theorem hasDerivWithinAt_Sv' {j j' : ℝ} (hjj : j ≤ j') {F G : ℝ → Coeff d} {s : Set ℝ} {τ : ℝ}
    (hF : ∀ τ' ∈ s, Adm j' (F τ')) (hG : Adm j' (G τ)) (hτ : τ ∈ s)
    (hlim : Tendsto (fun τ' => HRS.PDE.hsNorm j' (fun k => (F τ' k - F τ k) / ((τ' - τ : ℝ) : ℂ) - G τ k))
      (𝓝[s \ {τ}] τ) (𝓝 0)) :
    HasDerivWithinAt (fun τ' => Sv j (F τ')) (Sv j (G τ)) s τ := by
  refine hasDerivWithinAt_Sv (fun τ' h' => (hF τ' h').mono hjj) (hG.mono hjj) hτ ?_
  refine squeeze_zero' (Eventually.of_forall fun _ => hsNorm_nonneg_q _ _) ?_ hlim
  filter_upwards [self_mem_nhdsWithin] with τ' hτ'
  exact hsNorm_mono_q hjj (quot_adm (s := s) (hF τ' hτ'.1) (hF τ hτ) hG).2.2

namespace PdeSetup

variable {P : PdeSetup d} {D : DynData d} {ν₀ : ℝ} {μ : ℝ → Torus d → ℝ} (h : P.Data D ν₀ μ)

include h

theorem Data.flow_hsNorm {t : ℝ} (ht : t ∈ Set.Ioc 0 P.T) {φ : Torus d → ℝ}
    (hφ : HRS.Uniform.Q54.Dom (P.n + 4) φ) {τ : ℝ} (hτ : τ ∈ Set.Icc 0 t) {j : ℕ} (hj1 : 1 ≤ j)
    (hjn : j ≤ P.n + 4) :
    HRS.PDE.hsNorm (j : ℝ) (P.flow D μ t φ τ) ≤ P.c.Cop j * sobolevNorm (j : ℝ) φ := by
  have hu : t - τ ∈ Set.Icc 0 t := ⟨by linarith [hτ.2], by linarith [hτ.1]⟩
  obtain ⟨-, hp2⟩ := h.flow_prop ht hφ hu
  rw [sub_sub_cancel] at hp2
  have hdom := HRS.Uniform.Q54.prop_dom P.hd P.s P.hs0 P.hsd (P.n + 4) P.hn P.R P.MB P.Λ P.VB D ν₀ P.T μ
    h.hA ht hφ hu
  have hms : MemSobolev (j : ℝ) (propagator D μ (t - τ) t φ) :=
    HRS.PDE.MFAdjoint.memSobolev_mono_idx hdom.2 (by exact_mod_cast hjn)
  rw [← hp2, ← HRS.PDE.ClassicalPart.sobolevNorm_eq_hsNorm hms]
  exact P.c.op D ν₀ μ h.hA t ht φ hφ j hj1 hjn (t - τ) hu

theorem Data.gen_real {t : ℝ} (ht : t ∈ Set.Ioc 0 P.T) {φ : Torus d → ℝ}
    (hφ : HRS.Uniform.Q54.Dom (P.n + 4) φ) {τ : ℝ} (hτ : τ ∈ Set.Icc 0 t) :
    IsRealCoeff (P.gen D μ t φ τ) ∧ Summable fun k => ‖P.gen D μ t φ τ k‖ := by
  obtain ⟨hsol, hw⟩ := h.spec ht hφ
  have hreal : ∀ τ ∈ Set.Icc 0 t, IsRealCoeff (P.flow D μ t φ τ) := fun τ hτ =>
    (HRS.Uniform.Q54.pc_data P.hd P.s P.hs0 P.hsd (P.n + 4) P.hJ1 P.hJd P.R P.MB P.Λ P.VB D ν₀ P.T μ
      h.hA ht hφ hτ).1
  obtain ⟨m'', hm1, hm2⟩ := HRS.PDE.ClassicalPart.exists_mid (d := d) P.hn
  have hcont : ContinuousInHs m'' (P.flow D μ t φ) t :=
    forward_strong_continuity P.lev t _ hw m'' hm2
  obtain ⟨hg, -⟩ := HRS.PDE.ClassicalPart.gen_path_facts h.hA P.hJd ht hsol hreal hm1 hcont
  obtain ⟨h1, h2⟩ := hg τ hτ
  exact ⟨h2, (HRS.PDE.ClassicalPart.WS_zero_iff _).1 h1⟩

theorem Data.gen_adm {t : ℝ} (ht : t ∈ Set.Ioc 0 P.T) {φ : Torus d → ℝ}
    (hφ : HRS.Uniform.Q54.Dom (P.n + 4) φ) {τ : ℝ} (hτ : τ ∈ Set.Icc 0 t) {j : ℕ}
    (hj : j + 2 ≤ P.n + 4) : Adm (j : ℝ) (P.gen D μ t φ τ) := by
  obtain ⟨hre, hsum⟩ := h.gen_real ht hφ hτ
  have hr : t - τ ∈ Set.Icc 0 P.T := ⟨by linarith [hτ.2], by linarith [hτ.1, ht.2]⟩
  have hmem : MemHs ((j : ℝ) + 2) (P.flow D μ t φ τ) :=
    memHs_mono_q (by exact_mod_cast hj) (h.flow_memHs ht hφ hτ)
  exact ⟨hre, hsum, (P.c.gen D ν₀ μ h.hA h.hν (t - τ) hr j hj _ hmem).1⟩

theorem Data.gen_bd {t : ℝ} (ht : t ∈ Set.Ioc 0 P.T) {φ : Torus d → ℝ}
    (hφ : HRS.Uniform.Q54.Dom (P.n + 4) φ) {τ : ℝ} (hτ : τ ∈ Set.Icc 0 t) {j : ℕ}
    (hj : j + 2 ≤ P.n + 4) :
    ‖Sv (j : ℝ) (P.gen D μ t φ τ)‖ ≤ P.c.Cg j * (P.c.Cop (j + 2) * sobolevNorm ((j : ℝ) + 2) φ) := by
  have hr : t - τ ∈ Set.Icc 0 P.T := ⟨by linarith [hτ.2], by linarith [hτ.1, ht.2]⟩
  have hmem : MemHs ((j : ℝ) + 2) (P.flow D μ t φ τ) :=
    memHs_mono_q (by exact_mod_cast hj) (h.flow_memHs ht hφ hτ)
  have h1 := (h.gen_adm ht hφ hτ hj).norm_Sv_le
  have h2 := (P.c.gen D ν₀ μ h.hA h.hν (t - τ) hr j hj _ hmem).2
  have h3 := h.flow_hsNorm ht hφ hτ (j := j + 2) (by omega) hj
  have hcast : ((j + 2 : ℕ) : ℝ) = (j : ℝ) + 2 := by push_cast; ring
  rw [hcast] at h3
  refine h1.trans (h2.trans ?_)
  exact mul_le_mul_of_nonneg_left h3 (P.c.Cg_nonneg j)

theorem Data.gen_cont {t : ℝ} (ht : t ∈ Set.Ioc 0 P.T) {φ : Torus d → ℝ}
    (hφ : HRS.Uniform.Q54.Dom (P.n + 4) φ) :
    ContinuousInHs (P.lev - 2) (P.gen D μ t φ) t :=
  (adjoint_torus_time_regularity P.hd P.s P.hs0 P.hsd (P.n + 4) P.hJ1 P.R P.MB P.Λ P.VB D ν₀ P.T μ h.hA
    t ht (coeffOf φ) (h.memHsφ hφ)).1

theorem Data.hasDeriv {t : ℝ} (ht : t ∈ Set.Ioc 0 P.T) {φ : Torus d → ℝ}
    (hφ : HRS.Uniform.Q54.Dom (P.n + 4) φ) {τ : ℝ} (hτ : τ ∈ Set.Icc 0 t) {j : ℕ}
    (hj : j + 2 ≤ P.n + 4) :
    HasDerivWithinAt (fun τ' => Sv (j : ℝ) (P.flow D μ t φ τ')) (Sv (j : ℝ) (P.gen D μ t φ τ))
      (Set.Icc 0 t) τ := by
  have hlev : P.lev - 2 = (((P.n + 2 : ℕ)) : ℝ) := by push_cast; ring
  have hlim := (adjoint_torus_time_regularity P.hd P.s P.hs0 P.hsd (P.n + 4) P.hJ1 P.R P.MB P.Λ P.VB D ν₀
    P.T μ h.hA t ht (coeffOf φ) (h.memHsφ hφ)).2 τ hτ
  refine hasDerivWithinAt_Sv' (j' := P.lev - 2) ?_ (F := P.flow D μ t φ) (G := P.gen D μ t φ)
    (fun τ' hτ' => h.flow_adm ht hφ hτ' (by linarith)) ?_ hτ hlim
  · rw [hlev]; exact_mod_cast (by omega : j ≤ P.n + 2)
  · rw [hlev]; exact h.gen_adm ht hφ hτ (by omega)

theorem Data.flow_lip {t : ℝ} (ht : t ∈ Set.Ioc 0 P.T) {φ : Torus d → ℝ}
    (hφ : HRS.Uniform.Q54.Dom (P.n + 4) φ) {j : ℕ} (hj : j + 2 ≤ P.n + 4) {τ τ' : ℝ}
    (hτ : τ ∈ Set.Icc 0 t) (hτ' : τ' ∈ Set.Icc 0 t) :
    ‖Sv (j : ℝ) (P.flow D μ t φ τ') - Sv (j : ℝ) (P.flow D μ t φ τ)‖ ≤
      (P.c.Cg j * (P.c.Cop (j + 2) * sobolevNorm ((j : ℝ) + 2) φ)) * |τ' - τ| :=
  Sv_lip (fun τ'' hτ'' => h.hasDeriv ht hφ hτ'' hj) (fun τ'' hτ'' => h.gen_bd ht hφ hτ'' hj) hτ hτ'

end PdeSetup

end HRS.Uniform.Q54c
