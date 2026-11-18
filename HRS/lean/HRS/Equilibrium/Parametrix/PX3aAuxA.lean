import HRS.Equilibrium.Parametrix.PX3bAux
import HRS.Equilibrium.Parametrix.PX1AuxExtApply
import HRS.Equilibrium.Parametrix.PX2AuxE

open MeasureTheory Filter Topology
noncomputable section
namespace HRS.Parx
variable {d : ℕ}

lemma px3a_chi_neg (w : Euc d) : chi d (-w) = chi d w := by
  unfold chi
  rw [ContDiffBump.apply, ContDiffBump.apply]
  simp only [sub_zero, smul_neg]
  exact (someContDiffBumpBase (Euc d)).symmetric _ _

lemma px3a_newtonKernel_neg (ν : ℝ) (w : Euc d) : newtonKernel d ν (-w) = newtonKernel d ν w := by
  simp [newtonKernel]

lemma px3a_mk_int (k : Euc d) (hk : ∀ i, ∃ n : ℤ, k i = n) : Torus.mk k = 0 := by
  funext i
  obtain ⟨n, hn⟩ := hk i
  simp only [Torus.mk, hn]
  simp


lemma px3a_toChart_neg {F : Torus d → Torus d → ℝ} (hF : IsSymmPair F) (X w : Euc d) :
    toChart F (X, -w) = toChart F (X, w) := by
  simp only [toChart, smul_neg, ← sub_eq_add_neg]
  rw [hF]
  simp [sub_eq_add_neg]

lemma px3a_newtonChart_neg {F : Torus d → Torus d → ℝ} (hF : IsSymmPair F) (ν : ℝ) (X w : Euc d) :
    newtonChart d ν (toChart F) (X, -w) = newtonChart d ν (toChart F) (X, w) := by
  unfold newtonChart
  simp only [px3a_chi_neg]
  congr 1
  rw [← integral_neg_eq_self (fun w' => newtonKernel d ν (w - w') * (chi d w' * toChart F (X, w')))]
  refine integral_congr_ae (Eventually.of_forall fun w' => ?_)
  simp only [px3a_chi_neg, px3a_toChart_neg hF]
  rw [← px3a_newtonKernel_neg ν (w - -w')]
  congr 2
  abel


lemma px3a_mk_cR (z : Torus d) : Torus.mk (Torus.centeredRep z) = z :=
  KernelGrad.mk_centeredRep z

lemma px3a_abs_cR_le (z : Torus d) (i : Fin d) : |Torus.centeredRep z i| ≤ 1 / 2 :=
  KernelGrad.abs_centeredRep_le z i

lemma px3a_mk_add (x y : Euc d) : Torus.mk (x + y) = Torus.mk x + Torus.mk y :=
  KernelGrad.mk_add x y

lemma px3a_exists_int_of_mk_eq {a b : Euc d} (h : Torus.mk a = Torus.mk b) (i : Fin d) :
    ∃ n : ℤ, a i = b i + n := by
  have h1 := congr_fun h i
  simp only [Torus.mk] at h1
  have h2 := (QuotientAddGroup.eq).mp h1
  rw [AddSubgroup.mem_zmultiples_iff] at h2
  obtain ⟨k, hk⟩ := h2
  refine ⟨-k, ?_⟩
  have hk' : (k : ℝ) = -a i + b i := by
    have : ((k • (1 : ℝ) : ℝ)) = (k : ℝ) := by simp
    rw [← this, hk]
  push_cast
  linarith

lemma px3a_mk_neg (w : Euc d) : Torus.mk (-w) = - Torus.mk w := by
  funext i
  simp [Torus.mk]

lemma px3a_cR_neg_of_small (z : Torus d) (hz : ‖Torus.centeredRep z‖ < 1 / 16) :
    Torus.centeredRep (-z) = - Torus.centeredRep z := by
  set w := Torus.centeredRep z with hw
  set w' := Torus.centeredRep (-z) with hw'
  have h1 : Torus.mk w' = Torus.mk (-w) := by
    rw [hw', px3a_mk_cR, px3a_mk_neg, hw, px3a_mk_cR]
  ext i
  obtain ⟨n, hn⟩ := px3a_exists_int_of_mk_eq h1 i
  have hwi : |w i| < 1 / 16 := by
    have := PiLp.norm_apply_le w i
    rw [Real.norm_eq_abs] at this
    linarith
  have hw'i : |w' i| ≤ 1 / 2 := px3a_abs_cR_le _ i
  have hn' : |(n : ℝ)| < 1 := by
    have : (n : ℝ) = w' i + w i := by simp at hn; linarith
    rw [this]
    calc |w' i + w i| ≤ |w' i| + |w i| := abs_add_le _ _
      _ < 1 := by linarith
  have hn0 : n = 0 := by
    have h3 : |n| < 1 := by exact_mod_cast hn'
    exact Int.abs_lt_one_iff.mp h3
  subst hn0
  simp at hn
  simpa using hn


lemma px3a_rep_eq (x y : Torus d) (i : Fin d) :
    ∃ n : ℤ, Torus.rep x i = Torus.rep y i + Torus.centeredRep (x - y) i + n := by
  have h : Torus.mk (Torus.rep x) = Torus.mk (Torus.rep y + Torus.centeredRep (x - y)) := by
    rw [Torus.mk_rep, px3a_mk_add, Torus.mk_rep, px3a_mk_cR]
    abel
  obtain ⟨n, hn⟩ := px3a_exists_int_of_mk_eq h i
  exact ⟨n, by simpa using hn⟩

lemma px3a_ofChart_symm {G : Euc d × Euc d → ℝ}
    (hper : ∀ (X z k : Euc d), (∀ i, ∃ n : ℤ, k i = n) → G (X + k, z) = G (X, z))
    (heven : ∀ X w, G (X, -w) = G (X, w)) (hsupp : ∀ X w, 1 / 16 ≤ ‖w‖ → G (X, w) = 0)
    (x y : Torus d) : ofChart G x y = ofChart G y x := by
  by_cases hxy : x = y
  · subst hxy; rfl
  have hyx : y ≠ x := Ne.symm hxy
  simp only [ofChart, if_neg hxy, if_neg hyx]
  set w := Torus.centeredRep (x - y) with hw
  set w' := Torus.centeredRep (y - x) with hw'
  by_cases hbig : 1 / 16 ≤ ‖w‖
  · rw [hsupp _ _ hbig]
    have : 1 / 16 ≤ ‖w'‖ := by
      by_contra hlt
      push Not at hlt
      have := px3a_cR_neg_of_small (y - x) hlt
      rw [neg_sub] at this
      rw [← hw, ← hw'] at this
      have h2 : w = -w' := this
      rw [h2, norm_neg] at hbig
      linarith
    rw [hsupp _ _ this]
  · push Not at hbig
    have h2 : w' = -w := by
      have := px3a_cR_neg_of_small (x - y) hbig
      rw [neg_sub] at this
      exact this
    rw [h2]
    obtain ⟨k, hk⟩ : ∃ k : Euc d, (∀ i, ∃ n : ℤ, k i = n) ∧ Torus.rep x = Torus.rep y + w + k := by
      refine ⟨Torus.rep x - (Torus.rep y + w), ?_, by abel⟩
      intro i
      obtain ⟨n, hn⟩ := px3a_rep_eq x y i
      exact ⟨n, by simp; linarith⟩
    obtain ⟨hk1, hk2⟩ := hk
    have e : Torus.rep x + (1 / 2 : ℝ) • (-w) = (Torus.rep y + (1 / 2 : ℝ) • w) + k := by
      rw [hk2]; module
    rw [e, hper _ _ _ hk1, heven]


lemma px3a_toChart_periodic (F : Torus d → Torus d → ℝ) (X z k : Euc d)
    (hk : ∀ i, ∃ n : ℤ, k i = n) : toChart F (X + k, z) = toChart F (X, z) := by
  have h0 := px3a_mk_int k hk
  have e1 : Torus.mk (X + k + (1 / 2 : ℝ) • z) = Torus.mk (X + (1 / 2 : ℝ) • z) := by
    have : X + k + (1 / 2 : ℝ) • z = (X + (1 / 2 : ℝ) • z) + k := by abel
    rw [this, px3a_mk_add, h0, add_zero]
  have e2 : Torus.mk (X + k - (1 / 2 : ℝ) • z) = Torus.mk (X - (1 / 2 : ℝ) • z) := by
    have : X + k - (1 / 2 : ℝ) • z = (X - (1 / 2 : ℝ) • z) + k := by abel
    rw [this, px3a_mk_add, h0, add_zero]
  simp only [toChart, e1, e2]

lemma px3a_newtonChart_periodic (F : Torus d → Torus d → ℝ) (ν : ℝ) (X z k : Euc d)
    (hk : ∀ i, ∃ n : ℤ, k i = n) :
    newtonChart d ν (toChart F) (X + k, z) = newtonChart d ν (toChart F) (X, z) := by
  simp only [newtonChart, px3a_toChart_periodic F X _ k hk]

lemma px3a_newtonChart_supp (F : Torus d → Torus d → ℝ) (ν : ℝ) (X w : Euc d)
    (hw : 1 / 16 ≤ ‖w‖) : newtonChart d ν (toChart F) (X, w) = 0 := by
  simp [newtonChart, chi_eq_zero hw]

lemma px3a_cc_symm (μ : Measure (Torus d)) {h : Torus d → Torus d → ℝ}
    (hs : ∀ x y, h x y = h y x) (x y : Torus d) :
    canonicalCenter μ h x y = canonicalCenter μ h y x := by
  unfold canonicalCenter
  have e1 : ∫ x', h x' y ∂μ = ∫ y', h y y' ∂μ := integral_congr_ae (Eventually.of_forall fun x' => hs x' y)
  have e2 : ∫ x', h x' x ∂μ = ∫ y', h x y' ∂μ := integral_congr_ae (Eventually.of_forall fun x' => hs x' x)
  rw [e1, e2, hs x y]
  ring

theorem px3a_newton_symm {β : ℝ} {ρ : Torus d → ℝ} (F : Torus d → Torus d → ℝ) (hF : IsSymmPair F) :
    IsSymmPair (newtonOp d β ρ F) := by
  intro x y
  by_cases hxy : x = y
  · subst hxy; rfl
  have hyx : y ≠ x := Ne.symm hxy
  unfold newtonOp
  simp only [ite_eq_right_iff, hxy, hyx, if_false]
  exact px3a_cc_symm _ (px3a_ofChart_symm (px3a_newtonChart_periodic F _)
    (px3a_newtonChart_neg hF _) (px3a_newtonChart_supp F _)) x y

end HRS.Parx
