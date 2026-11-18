import HRS.MS.SA16SOp2

/-!
# S.A.16 (SA16S) Op3: the canonical operators `B_b = b·∇`, `Δ_J` on `WmpSpace` and their weak identities

* `sa16so_B d k p bc : W^{k+1,p} → W^{k,p}` (zero unless `bc` is smooth with bounded derivatives up to order `k`):
  `wrep (B (jet φ)) = ∑ b_i ∂_iφ`, `‖B‖ ≤ sa16so_cB`, `B_{b-b'} = B_b - B_{b'}`;
  weak identity `ℓ_ψ(B G) = -ℓ_{div(bψ)}(G)` (`sa16so_ell_B`).
* `sa16so_Lap d k p : W^{k+2,p} → W^{k,p}`: `wrep (Δ(jet φ)) = Δφ`, `ℓ_ψ(Δ G) = ℓ_{Δψ}(G)` (`sa16so_ell_Lap`).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section Op3
variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)]

lemma sa16so_clm_ext {l k : ℕ} {T T' : WmpSpace d l p →L[ℝ] WmpSpace d k p}
    (h : ∀ φ : ccSub d, T (sa16r_Jcc d l p φ) = T' (sa16r_Jcc d l p φ)) : T = T' := by
  ext1 G
  exact (sa16r_Jcc_dense d l p).induction_on G (isClosed_eq T.continuous T'.continuous) h

lemma sa16so_wrep_sub (k : ℕ) (G H : WmpSpace d k p) :
    wrep d k p (G - H) =ᵐ[volume] fun x => wrep d k p G x - wrep d k p H x := by
  have h1 : G - H = G + (-1 : ℝ) • H := by
    rw [sub_eq_add_neg]; congr 1; exact (neg_one_smul ℝ H).symm
  rw [h1]
  filter_upwards [sa16r_wrep_add d k p G ((-1 : ℝ) • H), sa16r_wrep_smul d k p (-1) H] with x h2 h3
  rw [h2, h3]
  ring

open Classical in
/-- the transport operator `b·∇ : W^{k+1,p} → W^{k,p}` (zero if the coefficients are not admissible) -/
def sa16so_B (d k : ℕ) (p : ℝ) [Fact (2 ≤ p)] (bc : Fin d → Euc d → ℝ) :
    WmpSpace d (k + 1) p →L[ℝ] WmpSpace d k p :=
  if h : ∃ B, SA16BddCoef k B bc then Classical.choose (sa16so_transport_exists k p h.choose_spec) else 0

lemma sa16so_B_Jcc {k : ℕ} {B : ℝ} {bc : Fin d → Euc d → ℝ} (hb : SA16BddCoef k B bc) (φ : ccSub d) :
    wrep d k p (sa16so_B d k p bc (sa16r_Jcc d (k + 1) p φ)) =ᵐ[volume] sa16so_transportFun bc φ.1 := by
  have h : ∃ B, SA16BddCoef k B bc := ⟨B, hb⟩
  unfold sa16so_B
  rw [dif_pos h]
  exact (Classical.choose_spec (sa16so_transport_exists k p h.choose_spec)).2 φ

lemma sa16so_B_norm {k : ℕ} {B : ℝ} {bc : Fin d → Euc d → ℝ} (hb : SA16BddCoef k B bc) :
    ‖sa16so_B d k p bc‖ ≤ sa16so_cB d k B := by
  obtain ⟨T, hT, hTs⟩ := sa16so_transport_exists k p (d := d) hb
  have : sa16so_B d k p bc = T := by
    refine sa16so_clm_ext fun φ => sa16r_wrep_inj d k p _ _ ?_
    filter_upwards [sa16so_B_Jcc (p := p) hb φ, hTs φ] with x h1 h2
    rw [h1, h2]
  rw [this]; exact hT

lemma SA16BddCoef.sub {k : ℕ} {B B' : ℝ} {bc bc' : Fin d → Euc d → ℝ} (hb : SA16BddCoef k B bc)
    (hb' : SA16BddCoef k B' bc') : SA16BddCoef k (B + B') (fun i x => bc i x - bc' i x) where
  nonneg := add_nonneg hb.nonneg hb'.nonneg
  smooth := fun i => (hb.smooth i).sub (hb'.smooth i)
  bound := fun i j hj x => by
    have := iteratedFDeriv_sub_apply (𝕜 := ℝ) (i := j) (x := x)
      (f := bc i) (g := bc' i) ((hb.smooth i).contDiffAt.of_le (by exact_mod_cast le_top))
      ((hb'.smooth i).contDiffAt.of_le (by exact_mod_cast le_top))
    rw [show (fun x => bc i x - bc' i x) = bc i - bc' i from rfl, this]
    exact (norm_sub_le _ _).trans (add_le_add (hb.bound i j hj x) (hb'.bound i j hj x))

lemma sa16so_transportFun_sub {bc bc' : Fin d → Euc d → ℝ} (φ : Euc d → ℝ) :
    sa16so_transportFun (fun i x => bc i x - bc' i x) φ =
      fun x => sa16so_transportFun bc φ x - sa16so_transportFun bc' φ x := by
  funext x
  simp only [sa16so_transportFun, sub_mul, Finset.sum_sub_distrib]

/-- the transport operator is linear in the coefficients -/
lemma sa16so_B_sub {k : ℕ} {B B' : ℝ} {bc bc' : Fin d → Euc d → ℝ} (hb : SA16BddCoef k B bc)
    (hb' : SA16BddCoef k B' bc') :
    sa16so_B d k p (fun i x => bc i x - bc' i x) = sa16so_B d k p bc - sa16so_B d k p bc' := by
  refine sa16so_clm_ext fun φ => sa16r_wrep_inj d k p _ _ ?_
  filter_upwards [sa16so_B_Jcc (p := p) (hb.sub hb') φ, sa16so_B_Jcc (p := p) hb φ, sa16so_B_Jcc (p := p) hb' φ,
    sa16so_wrep_sub k (sa16so_B d k p bc (sa16r_Jcc d (k + 1) p φ))
      (sa16so_B d k p bc' (sa16r_Jcc d (k + 1) p φ))] with x h1 h2 h3 h4
  rw [ContinuousLinearMap.sub_apply, h4, h2, h3, h1]
  exact congrFun (sa16so_transportFun_sub (bc := bc) (bc' := bc') φ.1) x

/-! ### the divergence form and the weak identity of the transport operator -/

/-- `div(b ψ)` -/
def sa16so_divFun (bc : Fin d → Euc d → ℝ) (ψ : Euc d → ℝ) (x : Euc d) : ℝ :=
  ∑ i, fderiv ℝ (fun y => bc i y * ψ y) x (EuclideanSpace.single i 1)

lemma sa16so_cc_div {k : ℕ} {B : ℝ} {bc : Fin d → Euc d → ℝ} (hb : SA16BddCoef k B bc) {ψ : Euc d → ℝ}
    (hψ : IsCcInfty ψ) : IsCcInfty (sa16so_divFun bc ψ) := by
  have h : sa16so_divFun bc ψ = ∑ i : Fin d, fun x => fderiv ℝ (fun y => bc i y * ψ y) x
      (EuclideanSpace.single i 1) := by
    funext x; simp [sa16so_divFun, Finset.sum_apply]
  rw [h]
  exact (ccSub d).sum_mem (fun i _ => sa16s_cc_fderiv ⟨(hb.smooth i).mul hψ.1, hψ.2.mul_left⟩ _)

theorem sa16so_ell_B {k : ℕ} {B : ℝ} {bc : Fin d → Euc d → ℝ} (hb : SA16BddCoef k B bc) {ψ : Euc d → ℝ}
    (hψ : IsCcInfty ψ) (G : WmpSpace d (k + 1) p) :
    sa16r_ell d k p hψ (sa16so_B d k p bc G) = -sa16r_ell d (k + 1) p (sa16so_cc_div hb hψ) G := by
  refine (sa16r_Jcc_dense d (k + 1) p).induction_on G (isClosed_eq ?_ ?_) (fun φ => ?_)
  · exact (sa16r_ell d k p hψ).continuous.comp (sa16so_B d k p bc).continuous
  · exact (sa16r_ell d (k + 1) p (sa16so_cc_div hb hψ)).continuous.neg
  · rw [sa16r_Jcc_eq, sa16r_ell_apply, sa16r_ell_apply]
    have hφ := φ.2
    have e1 : ∫ x, wrep d k p (sa16so_B d k p bc (sa16r_cc_elt hφ (k + 1))) x * ψ x =
        ∫ x, sa16so_transportFun bc φ.1 x * ψ x := by
      refine integral_congr_ae ?_
      have := sa16so_B_Jcc (p := p) hb φ
      rw [sa16r_Jcc_eq] at this
      filter_upwards [this] with x hx
      rw [hx]
    have e2 : ∫ x, wrep d (k + 1) p (sa16r_cc_elt hφ (k + 1)) x * sa16so_divFun bc ψ x =
        ∫ x, φ.1 x * sa16so_divFun bc ψ x := by
      refine integral_congr_ae ?_
      filter_upwards [sa16r_cc_elt_wrep (p := p) hφ (k + 1)] with x hx
      rw [hx]
    rw [e1, e2]
    unfold sa16so_transportFun sa16so_divFun
    have hbψ : ∀ i, IsCcInfty (fun y => bc i y * ψ y) := fun i => ⟨(hb.smooth i).mul hψ.1, hψ.2.mul_left⟩
    have hint1 : ∀ i : Fin d, Integrable (fun x => bc i x * fderiv ℝ φ.1 x (EuclideanSpace.single i 1) * ψ x) := by
      intro i
      have hc : Continuous (fun x => bc i x * fderiv ℝ φ.1 x (EuclideanSpace.single i 1) * ψ x) :=
        ((hb.smooth i).continuous.mul (sa16s_cc_fderiv hφ _).1.continuous).mul hψ.1.continuous
      exact hc.integrable_of_hasCompactSupport (hψ.2.mul_left)
    have hint2 : ∀ i : Fin d, Integrable (fun x => φ.1 x * fderiv ℝ (fun y => bc i y * ψ y) x
        (EuclideanSpace.single i 1)) := by
      intro i
      exact ((hφ.1.continuous).mul (sa16s_cc_fderiv (hbψ i) _).1.continuous).integrable_of_hasCompactSupport
        (hφ.2.mul_right)
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    rw [integral_finsetSum _ (fun i _ => hint1 i), integral_finsetSum _ (fun i _ => hint2 i), ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := sa16s_ibp1 hφ (hbψ i) (EuclideanSpace.single i 1)
    rw [← this]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    ring

end Op3

end HRS.Whole.AppendixA.Phase2SA16R
