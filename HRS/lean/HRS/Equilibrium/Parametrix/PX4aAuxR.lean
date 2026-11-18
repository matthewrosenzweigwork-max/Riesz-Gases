import HRS.Equilibrium.Parametrix.PX4aAuxQ

/-!
# Packet PX4a auxiliaries R: the divergence form of `Jop`

`jop_formula`: for `x ≠ y`, `Jop(Ψ(·, y))(x) = Φ_k[S_N] + Φ_Λ[S_N] + farConv[S_F]` evaluated at
`(Y, z0) = (rep y, centeredRep (x - y))`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.Parx

variable {d : ℕ}

local notation "∞'" => ((⊤ : ℕ∞) : WithTop ℕ∞)

lemma div_of_coords (W : Euc d → Euc d) (x0 : Euc d) (D : Fin d → Euc d →L[ℝ] ℝ)
    (hD : ∀ i, HasFDerivAt (fun x => W x i) (D i) x0) :
    ∑ i, fderiv ℝ W x0 (EuclideanSpace.single i 1) i = ∑ i, D i (EuclideanSpace.single i 1) := by
  have hdiff : DifferentiableAt ℝ W x0 := differentiableAt_euclidean.2 fun i => (hD i).differentiableAt
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : HasFDerivAt (fun x => W x i) ((EuclideanSpace.proj i : StrongDual ℝ (Euc d)).comp (fderiv ℝ W x0)) x0 :=
    (EuclideanSpace.proj i : StrongDual ℝ (Euc d)).hasFDerivAt.comp x0 hdiff.hasFDerivAt
  have := (hD i).unique h1
  rw [this]
  rfl

lemma kPot_sum_int {ι : Type*} (k : Euc d → ℝ) (t : Finset ι) (g : ι → Euc d × Euc d → ℝ) (Y z : Euc d)
    (hint : ∀ i ∈ t, Integrable (fun w => k (z - w) * g i (Y, w))) :
    kPot d k (fun p => ∑ i ∈ t, g i p) (Y, z) = ∑ i ∈ t, kPot d k (g i) (Y, z) := by
  unfold kPot
  simp only [Finset.mul_sum]
  exact integral_finset_sum t hint

lemma farConv_sum_int {ι : Type*} (s : ℝ) (t : Finset ι) (S : ι → Euc d × Euc d → ℝ) (p : Euc d × Euc d)
    (hint : ∀ i ∈ t, Integrable (fun w => ghat d s w * S i (p.1, p.2 - w))
      (volume.restrict (LocalDivAux.cube d))) :
    farConv d s (fun q => ∑ i ∈ t, S i q) p = ∑ i ∈ t, farConv d s (S i) p := by
  unfold farConv
  simp only [Finset.mul_sum]
  exact integral_finset_sum t hint

lemma measurable_Psii {ρ : Torus d → ℝ} (hρ : Torus.IsSmooth ρ) (Ψ : Torus d → Torus d → ℝ) (i : Fin d) (y : Torus d) :
    Measurable (fun u : Torus d => Psii ρ Ψ i u y) := by
  have hρ' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift ρ) := hρ
  have h1 : Measurable ρ := by
    have : ρ = fun u => Torus.lift ρ (Torus.rep u) := by
      funext u; simp [Torus.lift, Torus.mk_rep]
    rw [this]
    exact hρ'.continuous.measurable.comp (px4a_measurable_rep d)
  have h2 : Measurable (fun u : Torus d => Torus.partialDeriv i (fun z => Ψ z y) u) := by
    have : (fun u : Torus d => Torus.partialDeriv i (fun z => Ψ z y) u) =
        fun u => fderiv ℝ (Torus.lift (fun z => Ψ z y)) (Torus.rep u) (EuclideanSpace.single i 1) := rfl
    rw [this]
    exact (measurable_fderiv_apply_const ℝ (Torus.lift (fun z => Ψ z y)) _).comp (px4a_measurable_rep d)
  exact h1.mul h2

set_option maxHeartbeats 3200000 in
theorem jop_formula (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 < s) (hsd : s < d) {ρ : Torus d → ℝ}
    (hρ : Torus.IsSmooth ρ) {Ψ : Torus d → Torus d → ℝ} {σ : ℝ} {b m : ℕ} {A : ℝ} (hA : 0 ≤ A)
    (hσ : σ < (d : ℝ) - 1) (hG : ∀ i, SrcCls d σ b (m + 1) A (Gsrc (Psii ρ Ψ i)))
    (hFs : ∀ i, ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) (Fsrc (Psii ρ Ψ i))) {N : ℕ → ℝ}
    (hN : ∀ i, ∀ j ≤ m + 1, ∀ p : Euc d × Euc d, ‖iteratedFDeriv ℝ j (Fsrc (Psii ρ Ψ i)) p‖ ≤ N j)
    (x y : Torus d) (hxy : x ≠ y) :
    Jop d s ρ (fun z => Ψ z y) x =
      kPot d (rieszK d s) (SNsrc ρ Ψ) (Torus.rep y, Torus.centeredRep (x - y)) +
      kPot d (Lam d s) (SNsrc ρ Ψ) (Torus.rep y, Torus.centeredRep (x - y)) +
      farConv d s (SFsrc ρ Ψ) (Torus.rep y, Torus.centeredRep (x - y)) := by
  classical
  have hd1 : 1 ≤ d := by omega
  have hσd : σ < d := by linarith
  set Y : Euc d := Torus.rep y with hYdef
  set z0 : Euc d := Torus.centeredRep (x - y) with hz0def
  have hY : Torus.mk Y = y := Torus.mk_rep y
  have hz0mk : Torus.mk z0 = x - y := px3a_mk_cR _
  have hz0 : z0 ≠ 0 := by
    intro h
    rw [h] at hz0mk
    have : Torus.mk (0 : Euc d) = 0 := by funext i; simp [Torus.mk]
    rw [this] at hz0mk
    exact hxy (sub_eq_zero.mp hz0mk.symm)
  have hz0b : ∀ i, |z0 i| ≤ 1 / 2 := fun i => px3a_abs_cR_le _ i
  -- derivatives of the coordinates
  have hVi : ∀ i : Fin d, ∃ D : Euc d →L[ℝ] ℝ,
      HasFDerivAt (fun z => convFun (periodicRiesz d s) (fun u => Psii ρ Ψ i u (Torus.mk Y)) (Torus.mk (Y + z))) D z0 ∧
      ∀ e : Euc d, D e = kPot d (rieszK d s) (dirD ((0 : Euc d), e) (Gsrc (Psii ρ Ψ i))) (Y, z0) +
        kPot d (Lam d s) (dirD ((0 : Euc d), e) (Gsrc (Psii ρ Ψ i))) (Y, z0) +
        farConv d s (dirD ((0 : Euc d), e) (Fsrc (Psii ρ Ψ i))) (Y, z0) := fun i =>
    Vi_hasFDerivAt hd hs0 hsd hA hσ (hG i) Y z0 hz0 hz0b (measurable_Psii hρ Ψ i (Torus.mk Y))
      (hFs i) (hN i)
  choose D hD hDe using hVi
  -- the vector field
  set W : Euc d → Euc d := Torus.lift (fun z : Torus d => (WithLp.toLp 2 (fun j : Fin d =>
    convFun (periodicRiesz d s) (fun y' => ρ y' * Torus.partialDeriv j (fun z' => Ψ z' y) y') z) : Euc d)) with hW
  have hJ : Jop d s ρ (fun z => Ψ z y) x = ∑ i, fderiv ℝ W (Torus.rep x) (EuclideanSpace.single i 1) i := rfl
  -- periodicity: derivative at `rep x` equals derivative at `Y + z0`
  set x0 : Euc d := Y + z0 with hx0
  have hx0mk : Torus.mk x0 = x := by
    rw [hx0, mk_add_eq, hY, hz0mk]; abel
  obtain ⟨k, hk, hkrep⟩ := rep_exists_lat x0
  have hrep : Torus.rep x = x0 + k := by rw [← hx0mk]; exact hkrep
  have hWper : ∀ v : Euc d, W (v + k) = W v := by
    intro v
    have hm : Torus.mk (v + k) = Torus.mk v := by rw [mk_add_eq, mk_isLat hk, add_zero]
    simp only [hW, Torus.lift, Function.comp]
    rw [hm]
  have hfd : fderiv ℝ W (Torus.rep x) = fderiv ℝ W x0 := by
    have := fderiv_comp_add_right (𝕜 := ℝ) (f := W) (x := x0) k
    have e : (fun v => W (v + k)) = W := funext hWper
    rw [e] at this
    rw [hrep]; exact this.symm
  -- the coordinates have the derivatives `D i`
  have hcoord : ∀ i : Fin d, HasFDerivAt (fun v => W v i) (D i) x0 := by
    intro i
    have h1 : HasFDerivAt (fun v : Euc d => v - Y) (ContinuousLinearMap.id ℝ (Euc d)) x0 :=
      (hasFDerivAt_id x0).sub_const Y
    have h2 : HasFDerivAt (fun z => convFun (periodicRiesz d s) (fun u => Psii ρ Ψ i u (Torus.mk Y)) (Torus.mk (Y + z)))
        (D i) (x0 - Y) := by
      have : x0 - Y = z0 := by rw [hx0]; abel
      rw [this]; exact hD i
    have h3 := h2.comp x0 h1
    have e : ((fun z => convFun (periodicRiesz d s) (fun u => Psii ρ Ψ i u (Torus.mk Y)) (Torus.mk (Y + z))) ∘
        (fun v : Euc d => v - Y)) = fun v => W v i := by
      funext v
      have : Y + (v - Y) = v := by abel
      simp only [Function.comp, this, hW, Torus.lift]
      rw [← hY]
      rfl
    rw [e] at h3
    simpa using h3
  rw [hJ, hfd, div_of_coords W x0 D hcoord]
  simp only [hDe]
  -- linearity of the three potentials in the source
  have hk := locKer_riesz hd hs0 hsd
  have hS : ∀ i : Fin d, SrcCls d (σ + 1) b m (A * ‖eVec d i‖) (Ssrc (Gsrc (Psii ρ Ψ i)) i) :=
    fun i => (hG i).dirD_snd hA (eVec d i)
  have hSz : ∀ (i : Fin d) (X w : Euc d), 1 / 32 < ‖w‖ → Ssrc (Gsrc (Psii ρ Ψ i)) i (X, w) = 0 :=
    fun i X w hw => dirD_zero_of_far (fun X' w' hw' => Gsrc_zero_of_ge _ X' w' hw'.le) (eVec d i) X w hw
  have h1 : kPot d (rieszK d s) (SNsrc ρ Ψ) (Y, z0) =
      ∑ i, kPot d (rieszK d s) (Ssrc (Gsrc (Psii ρ Ψ i)) i) (Y, z0) :=
    kPot_sum hd1 hk (σ := σ + 1) (by linarith) Finset.univ (fun i => A * ‖eVec d i‖)
      (fun i => Ssrc (Gsrc (Psii ρ Ψ i)) i) (fun i _ => by positivity) (fun i _ => hS i)
      (fun i _ => hSz i) Y z0 hz0
  have h2 : kPot d (Lam d s) (SNsrc ρ Ψ) (Y, z0) =
      ∑ i, kPot d (Lam d s) (Ssrc (Gsrc (Psii ρ Ψ i)) i) (Y, z0) :=
    kPot_sum_int (Lam d s) Finset.univ (fun i => Ssrc (Gsrc (Psii ρ Ψ i)) i) Y z0
      (fun i _ => Lam_mul_integrable hd hs0.le hsd (by linarith) (hS i) Y z0)
  have hSF : ∀ i : Fin d, Integrable (fun w => ghat d s w * Ssrc (Fsrc (Psii ρ Ψ i)) i (Y, z0 - w))
      (volume.restrict (LocalDivAux.cube d)) := by
    intro i
    have hcS : Continuous (Ssrc (Fsrc (Psii ρ Ψ i)) i) := by
      unfold Ssrc dirD
      exact ((hFs i).continuous_fderiv (by exact_mod_cast Nat.succ_ne_zero m)).clm_apply continuous_const
    have hc : Continuous (fun w : Euc d => Ssrc (Fsrc (Psii ρ Ψ i)) i (Y, z0 - w)) :=
      hcS.comp (by fun_prop)
    have hb : ∀ q : Euc d × Euc d, ‖Ssrc (Fsrc (Psii ρ Ψ i)) i q‖ ≤ N 1 := by
      intro q
      have h1' := hN i 1 (by omega) q
      rw [norm_iteratedFDeriv_one] at h1'
      unfold Ssrc dirD
      refine ((fderiv ℝ (Fsrc (Psii ρ Ψ i)) q).le_opNorm _).trans ?_
      have : ‖((0 : Euc d), eVec d i)‖ = 1 := by
        rw [Prod.norm_def]; simp [norm_eVec]
      rw [this, mul_one]
      exact h1'
    have := (integrable_ghat_cube hd hs0.le hsd).bdd_mul hc.aestronglyMeasurable
      (Eventually.of_forall fun w => hb _)
    simpa [mul_comm] using this
  have h3 : farConv d s (SFsrc ρ Ψ) (Y, z0) = ∑ i, farConv d s (Ssrc (Fsrc (Psii ρ Ψ i)) i) (Y, z0) :=
    farConv_sum_int s Finset.univ (fun i => Ssrc (Fsrc (Psii ρ Ψ i)) i) (Y, z0) (fun i _ => hSF i)
  rw [h1, h2, h3, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  rfl

end HRS.Parx

end
