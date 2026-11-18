import HRS.Main.GFEVAux8

/-!
# Packet GFEVG, part 9: the two-level dual operator

Copy of `Q54.exists_dual_op` (Q54Aux10) for a map `Up` from a class of functions with the `H^a` norm into `H^b`:
the dual operator `V : E_b →L E_a`, `⟨V z, φ⟩ = ⟨z, Up φ⟩`, `‖V‖ ≤ M`.  Moreover `Up (const) = 0` is allowed
(the generator kills constants), in contrast with the propagator.
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators

namespace HRS.GF

open HRS HRS.PDE HRS.Uniform HRS.Uniform.Q54 HRS.Uniform.Q48b

variable {d : ℕ}

/-- hypotheses on `Up : (class, `H^a`-norm) → H^b`, `Up (const) = 0`. -/
structure GfDualHyp (P : (Torus d → ℝ) → Prop) (a b : ℝ) (Up : (Torus d → ℝ) → Torus d → ℝ) (M : ℝ) : Prop where
  hM : 0 ≤ M
  smooth : ∀ φ : Torus d → ℝ, Torus.IsSmooth φ → P φ
  memS : ∀ φ : Torus d → ℝ, P φ → MemSobolev a φ
  closed : ∀ φ ψ : Torus d → ℝ, P φ → P ψ → ∀ α β : ℝ, P (fun x => α * φ x + β * ψ x)
  lin : ∀ φ ψ : Torus d → ℝ, P φ → P ψ → ∀ α β : ℝ,
    Up (fun x => α * φ x + β * ψ x) = fun x => α * Up φ x + β * Up ψ x
  const : ∀ c : ℝ, Up (fun _ => c) = fun _ => 0
  bd : ∀ φ : Torus d → ℝ, P φ → MemSobolev b (Up φ) ∧ sobolevNorm b (Up φ) ≤ M * sobolevNorm a φ

theorem GfDualHyp.finsum {a b : ℝ} {Up : (Torus d → ℝ) → Torus d → ℝ} {M : ℝ} {P : (Torus d → ℝ) → Prop}
    (h : GfDualHyp P a b Up M) (T : Finset (NonzeroLattice d)) (α : NonzeroLattice d → ℝ) :
    Up (fun x => ∑ l ∈ T, α l * Torus.realMode l x) =
      fun x => ∑ l ∈ T, α l * Up (Torus.realMode l) x := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact h.const 0
  | insert l T hl ih =>
    have e1 : (fun x => ∑ k ∈ insert l T, α k * Torus.realMode k x) =
        fun x => α l * Torus.realMode l x + 1 * ∑ k ∈ T, α k * Torus.realMode k x := by
      funext x; rw [Finset.sum_insert hl]; ring
    have hs : Torus.IsSmooth (fun x => ∑ k ∈ T, α k * Torus.realMode k x) := q48bTest_smooth T α
    rw [e1, h.lin (Torus.realMode l) (fun x => ∑ k ∈ T, α k * Torus.realMode k x)
      (h.smooth _ (q48b_isSmooth_realMode l)) (h.smooth _ hs) (α l) 1, ih]
    funext x
    rw [Finset.sum_insert hl]; ring

variable {a b : ℝ} {Up : (Torus d → ℝ) → Torus d → ℝ} {M : ℝ} {P : (Torus d → ℝ) → Prop}

/-- the image of the basis vector `l` (weighted input coordinates at level `a`, output at level `b`). -/
def gfColSeq (h : GfDualHyp P a b Up M) (l : NonzeroLattice d) : L2 d :=
  (Lattice.jp l.1 ^ (-a)) • (show L2 d from
    lpOf b (h.bd (Torus.realMode l) (h.smooth _ (q48b_isSmooth_realMode l))).1)

def gfMap (h : GfDualHyp P a b Up M) : (NonzeroLattice d →₀ ℝ) →ₗ[ℝ] L2 d :=
  Finsupp.linearCombination ℝ (gfColSeq h)

theorem gfMap_eq (h : GfDualHyp P a b Up M) (c : NonzeroLattice d →₀ ℝ) :
    gfMap h c = (show L2 d from lpOf b (h.bd (phiOf a c) (h.smooth _ (phiOf_smooth a c))).1) := by
  classical
  ext k
  show (gfMap h c) k = Lattice.jp k.1 ^ b * Torus.funRealCoeff (Up (phiOf a c)) k
  unfold gfMap
  rw [Finsupp.linearCombination_apply, Finsupp.sum, lp.coeFn_sum, Finset.sum_apply]
  have hU : Up (phiOf a c) = fun x => ∑ l ∈ c.support, (c l / Lattice.jp l.1 ^ a) * Up (Torus.realMode l) x :=
    h.finsum c.support (fun l => c l / Lattice.jp l.1 ^ a)
  rw [hU, funRealCoeff_finset_sum c.support _ _ (fun l _ => (h.bd _ (h.smooth _ (q48b_isSmooth_realMode l))).1.1) k,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  show c l * (Lattice.jp l.1 ^ (-a) * (Lattice.jp k.1 ^ b * Torus.funRealCoeff (Up (Torus.realMode l)) k)) =
    Lattice.jp k.1 ^ b * (c l / Lattice.jp l.1 ^ a * Torus.funRealCoeff (Up (Torus.realMode l)) k)
  have : Lattice.jp l.1 ^ (-a) = (Lattice.jp l.1 ^ a)⁻¹ := Real.rpow_neg (Torus.jp_pos _).le a
  rw [this]
  ring

theorem gfMap_norm_le (h : GfDualHyp P a b Up M) (c : NonzeroLattice d →₀ ℝ) :
    ‖gfMap h c‖ ≤ M * ‖eFin d c‖ := by
  classical
  have hbd := h.bd (phiOf a c) (h.smooth _ (phiOf_smooth a c))
  have e1 : ‖gfMap h c‖ = ‖lpOf b hbd.1‖ := by rw [gfMap_eq]; rfl
  have e2 : ‖lpOf b hbd.1‖ ≤ sobolevNorm b (Up (phiOf a c)) := norm_lpOf_le_sobolev b hbd.1
  have e3 : sobolevNorm a (phiOf a c) = ‖eFin d c‖ := by
    unfold phiOf
    rw [q48bTest_sobolevNorm, norm_eFin]
    congr 1
    refine Finset.sum_congr rfl fun l _ => ?_
    have hj := Torus.jp_pos l.1
    show Lattice.jp l.1 ^ (2 * a) * (c l / Lattice.jp l.1 ^ a) ^ 2 = c l ^ 2
    rw [div_pow, Torus.jp_rpow_sq]
    field_simp
  rw [e1]
  calc ‖lpOf b hbd.1‖ ≤ sobolevNorm b (Up (phiOf a c)) := e2
    _ ≤ M * sobolevNorm a (phiOf a c) := hbd.2
    _ = M * ‖eFin d c‖ := by rw [e3]

theorem gfMap_sec_bound (h : GfDualHyp P a b Up M) {φ : Torus d → ℝ} (hφ : P φ)
    (F : Finset (NonzeroLattice d)) :
    ‖gfMap h (secFin (wseqF a φ) F) - (show L2 d from lpOf b (h.bd φ hφ).1)‖ ≤
      M * Real.sqrt (∑' k : NonzeroLattice d, (if k ∈ F then 0 else
        Lattice.jp k.1 ^ (2 * a) * Torus.funRealCoeff φ k ^ 2)) := by
  classical
  have hφS : MemSobolev a φ := h.memS φ hφ
  set c := secFin (wseqF a φ) F with hc
  set φF := phiOf a c with hφF
  have hFsm : Torus.IsSmooth φF := phiOf_smooth a c
  have hFS : MemSobolev a φF := HRS.PDE.MFSemigroup.memSobolev_of_isSmooth hFsm a
  set m := Torus.mean φ with hm
  set ψ : Torus d → ℝ := fun x => φF x - φ x + m with hψ
  have hFP : P φF := h.smooth _ hFsm
  have e1 : (fun x => φF x - φ x) = fun x => 1 * φF x + (-1) * φ x := by funext x; ring
  have e2 : ψ = fun x => 1 * (φF x - φ x) + m * 1 := by funext x; simp only [hψ]; ring
  have hPd : P (fun x => φF x - φ x) := by rw [e1]; exact h.closed φF φ hFP hφ 1 (-1)
  have hP1 : P (fun _ : Torus d => (1 : ℝ)) := h.smooth _ (isSmooth_const' 1)
  have hψP : P ψ := by rw [e2]; exact h.closed _ _ hPd hP1 1 m
  have hbF := h.bd φF hFP
  have hb := h.bd φ hφ
  have hbψ := h.bd ψ hψP
  have hC1 : ∀ x, Up ψ x = Up φF x - Up φ x := by
    have s1 := h.lin φF φ hFP hφ 1 (-1)
    have s2 := h.lin (fun x => φF x - φ x) (fun _ => (1 : ℝ)) hPd hP1 1 m
    intro x
    have s2' := congrFun s2 x
    have s1' := congrFun s1 x
    have c1 := congrFun (h.const 1) x
    rw [e2, s2']
    rw [e1, s1'] at *
    simp only [c1]
    ring
  have hC2 : ∀ k, Torus.funRealCoeff (Up φF) k - Torus.funRealCoeff (Up φ) k =
      Torus.funRealCoeff (Up ψ) k := by
    intro k
    have : Up ψ = fun x => (Up φF x - Up φ x) := funext hC1
    have hg : MemLp (fun x => Up φF x - Up φ x) 2 (volume : Measure (Torus d)) := hbF.1.1.sub hb.1.1
    rw [this, funRealCoeff_sub' hbF.1.1 hb.1.1]
  have hdiff : gfMap h c - (show L2 d from lpOf b hb.1) = (show L2 d from lpOf b hbψ.1) := by
    rw [gfMap_eq]
    ext k
    show Lattice.jp k.1 ^ b * Torus.funRealCoeff (Up φF) k - Lattice.jp k.1 ^ b * Torus.funRealCoeff (Up φ) k =
      Lattice.jp k.1 ^ b * Torus.funRealCoeff (Up ψ) k
    rw [← hC2 k]; ring
  rw [hdiff]
  refine (norm_lpOf_le_sobolev b hbψ.1).trans (hbψ.2.trans ?_)
  refine mul_le_mul_of_nonneg_left (le_of_eq ?_) h.hM
  have hint : Integrable φ := hφS.1.integrable one_le_two
  have hmean : Torus.mean ψ = 0 := by
    have hFint : Integrable φF := q48b_integrable_cont (q48bTest_continuous _ _)
    rw [hψ, mean_sub_add_const' (f := φF) (g := φ) hFint hint m]
    rw [show Torus.mean φF = 0 from q48bTest_mean _ _]
    simp [hm]
  have hcoef : ∀ k, Torus.funRealCoeff ψ k = - (if k ∈ F then 0 else Torus.funRealCoeff φ k) := by
    intro k
    have h1 : Torus.funRealCoeff ψ k = Torus.funRealCoeff (fun x => φF x - φ x) k :=
      q48b_funRealCoeff_add_const (hFS.1.sub hφS.1) m k
    rw [h1, funRealCoeff_sub' hFS.1 hφS.1, hφF, coeff_phiOf_sec]
    by_cases hk : k ∈ F <;> simp [hk]
  unfold sobolevNorm
  rw [hmean]
  congr 1
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_add]
  refine tsum_congr fun k => ?_
  rw [hcoef k]
  by_cases hk : k ∈ F <;> simp [hk]

theorem gfMap_sec_tendsto (h : GfDualHyp P a b Up M) {φ : Torus d → ℝ} (hφ : P φ) :
    Tendsto (fun F : Finset (NonzeroLattice d) => gfMap h (secFin (wseqF a φ) F)) atTop
      (𝓝 (show L2 d from lpOf b (h.bd φ hφ).1)) := by
  classical
  have hφS : MemSobolev a φ := h.memS φ hφ
  have ht := tail_tendsto (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (2 * a) * Torus.funRealCoeff φ k ^ 2)
    (fun k => mul_nonneg (Real.rpow_nonneg (Torus.jp_pos _).le _) (sq_nonneg _)) hφS.2
  have hs : Tendsto (fun F : Finset (NonzeroLattice d) => M * Real.sqrt (∑' k : NonzeroLattice d,
      (if k ∈ F then 0 else Lattice.jp k.1 ^ (2 * a) * Torus.funRealCoeff φ k ^ 2))) atTop (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp ht
    simpa using this.const_mul M
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero (fun F => norm_nonneg _) (fun F => gfMap_sec_bound h hφ F) hs

theorem gfev_exists_dual_op2 (h : GfDualHyp P a b Up M) :
    ∃ V : NegSobolev d b →L[ℝ] NegSobolev d a, ‖V‖ ≤ M ∧
      ∀ (z : NegSobolev d b) (φ : Torus d → ℝ), P φ →
        NegSobolev.eval (V z) φ = NegSobolev.eval z (Up φ) := by
  classical
  set T : L2 d →L[ℝ] L2 d := (gfMap h).extendOfNorm (eFin d) with hT
  have hTe : ∀ c, T (eFin d c) = gfMap h c := fun c =>
    LinearMap.extendOfNorm_eq (denseRange_eFin d) ⟨M, gfMap_norm_le h⟩ c
  have hTn : ‖T‖ ≤ M := LinearMap.opNorm_extendOfNorm_le (denseRange_eFin d) h.hM (gfMap_norm_le h)
  let T' : NegSobolev d a →L[ℝ] NegSobolev d b := T
  let V : NegSobolev d b →L[ℝ] NegSobolev d a := ContinuousLinearMap.adjoint T'
  refine ⟨V, ?_, fun z φ hφ => ?_⟩
  · have : ‖V‖ = ‖T'‖ := ContinuousLinearMap.adjoint.norm_map T'
    rw [this]
    exact hTn
  · have hφS : MemSobolev a φ := h.memS φ hφ
    have hb := h.bd φ hφ
    have hkey : T' (lpOf a hφS) = lpOf b hb.1 := by
      have hs := lp.hasSum_single (E := fun _ : NonzeroLattice d => ℝ) (p := 2) (by norm_num)
        (show L2 d from lpOf a hφS)
      have h1 : Tendsto (fun F : Finset (NonzeroLattice d) => eFin d (secFin (wseqF a φ) F)) atTop
          (𝓝 (show L2 d from lpOf a hφS)) :=
        Tendsto.congr (fun F => (eFin_secFin (wseqF a φ) F).symm) hs
      have h2 : Tendsto (fun F : Finset (NonzeroLattice d) => T (eFin d (secFin (wseqF a φ) F))) atTop
          (𝓝 (T (show L2 d from lpOf a hφS))) := (T.continuous.tendsto _).comp h1
      have h3 : Tendsto (fun F : Finset (NonzeroLattice d) => gfMap h (secFin (wseqF a φ) F)) atTop
          (𝓝 (T (show L2 d from lpOf a hφS))) :=
        Tendsto.congr (fun F => hTe _) h2
      have heq : T (show L2 d from lpOf a hφS) = (show L2 d from lpOf b hb.1) :=
        tendsto_nhds_unique h3 (gfMap_sec_tendsto h hφ)
      exact heq
    rw [eval_eq_inner a (V z) hφS, eval_eq_inner b z hb.1, ContinuousLinearMap.adjoint_inner_left, hkey]

end HRS.GF
