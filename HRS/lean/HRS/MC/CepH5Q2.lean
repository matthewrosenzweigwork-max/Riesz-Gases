import HRS.MC.CepH5Q1

/-!
# Packet CEPH5FISH, part 2: continuity of the test integrand (for `V ∈ C¹`)
-/

noncomputable section

namespace HRS.MC.CepH5Pf

open HRS MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

variable {N : ℕ}

lemma q2_wsq_pos {y0 : Euc 1} (h : Torus.mk y0 ≠ 0) (m : Lattice 1) :
    0 < HRS.KernelAux.wsq (fun i => y0 i) m := by
  have h1 := KernelD1Aux.off_int_of_mk_ne h
  have h2 := KernelD1Aux.wsq_ev_pos h1 m
  have h3 : y0 = KernelD1Aux.ev (y0 0) := KernelD1Aux.ev_eq y0
  rw [h3]
  simpa using h2

lemma q2_U_contDiffAt (D : DynData 1) (hV : Torus.IsCk 1 D.V) (Y : Fin N → Euc 1)
    (hfree : ∀ i j, i ≠ j → Torus.mk (Y i) ≠ Torus.mk (Y j)) :
    ContDiffAt ℝ 1 (fun Z : Fin N → Euc 1 => totalPotential D (q1mk N Z)) Y := by
  unfold totalPotential
  refine ContDiffAt.add (contDiffAt_const.mul (ContDiffAt.sum fun i _ => ContDiffAt.sum fun j hj => ?_))
    (ContDiffAt.sum fun i _ => ?_)
  · have hij : i ≠ j := (Finset.ne_of_mem_erase hj).symm
    have hne : Torus.mk (Y i - Y j) ≠ 0 := by
      intro h0
      apply hfree i j hij
      have : Torus.mk (Y i) - Torus.mk (Y j) = 0 := by
        rw [← h0]; funext k; simp [Torus.mk]
      exact sub_eq_zero.mp this
    have hg : ContDiffAt ℝ 1 (Torus.lift (periodicRiesz 1 D.s)) (Y i - Y j) :=
      (KernelD1Aux.contDiffAt_lift_g (d := 1) (s := D.s) le_rfl D.hs0 (by simpa using D.hsd)
        (Y i - Y j) (q2_wsq_pos hne)).of_le (by exact_mod_cast le_top)
    have hsub : ContDiffAt ℝ 1 (fun Z : Fin N → Euc 1 => Z i - Z j) Y :=
      ((contDiff_apply ℝ (Euc 1) i).sub (contDiff_apply ℝ (Euc 1) j)).contDiffAt
    refine (hg.comp Y hsub).congr_of_eventuallyEq (Filter.Eventually.of_forall fun Z => ?_)
    simp only [Function.comp, Torus.lift]
    congr 1
  · have := (hV.contDiffAt (x := Y i)).comp Y ((contDiff_apply ℝ (Euc 1) i).contDiffAt)
    exact this


lemma q2_phi_contDiff {ζ : Config 1 N → (Fin N → Euc 1)} (hζ : IsFisherTestField ζ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun Y : Fin N → Euc 1 => ζ (q1mk N Y)) := hζ.smooth

lemma q2_DU_cont (D : DynData 1) (hV : Torus.IsCk 1 D.V) {ζ : Config 1 N → (Fin N → Euc 1)}
    (hζ : IsFisherTestField ζ) :
    Continuous fun Y : Fin N → Euc 1 =>
      fderiv ℝ (fun Z : Fin N → Euc 1 => totalPotential D (q1mk N Z)) Y (ζ (q1mk N Y)) := by
  obtain ⟨K, hKc, hKd, hK0⟩ := hζ.support
  have hΦ : Continuous fun Y : Fin N → Euc 1 => ζ (q1mk N Y) :=
    (q2_phi_contDiff hζ).continuous
  rw [continuous_iff_continuousAt]
  intro Y0
  by_cases h : q1mk N Y0 ∈ K
  · have hfree : ∀ i j, i ≠ j → Torus.mk (Y0 i) ≠ Torus.mk (Y0 j) := by
      intro i j hij hEq
      exact Set.disjoint_left.mp hKd h ⟨i, j, hij, hEq⟩
    have hU := q2_U_contDiffAt D hV Y0 hfree
    have hd : ContinuousAt (fderiv ℝ (fun Z : Fin N → Euc 1 => totalPotential D (q1mk N Z))) Y0 :=
      (hU.fderiv_right (m := 0) (by norm_num)).continuousAt
    exact hd.clm_apply hΦ.continuousAt
  · have hopen : IsOpen {Y : Fin N → Euc 1 | q1mk N Y ∉ K} :=
      (hKc.isClosed.isOpen_compl).preimage q1mk_cont
    have hev : (fun Y : Fin N → Euc 1 =>
        fderiv ℝ (fun Z : Fin N → Euc 1 => totalPotential D (q1mk N Z)) Y (ζ (q1mk N Y))) =ᶠ[𝓝 Y0]
        fun _ => 0 := by
      filter_upwards [hopen.mem_nhds h] with Y hY
      simp [hK0 _ hY]
    exact (continuousAt_const).congr hev.symm

lemma q2_G_cont (D : DynData 1) (hV : Torus.IsCk 1 D.V) {ζ : Config 1 N → (Fin N → Euc 1)}
    (hζ : IsFisherTestField ζ) : Continuous (q1G D ζ) := by
  have hΦ := q2_phi_contDiff hζ
  unfold q1G
  refine Continuous.sub (Continuous.add (continuous_const.mul (continuous_finsetSum _ fun k _ => ?_))
    (continuous_const.mul (q2_DU_cont D hV hζ))) (continuous_finsetSum _ fun i _ => ?_)
  · have hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun Z : Fin N → Euc 1 => (ζ (q1mk N Z) k.1) k.2) :=
      (EuclideanSpace.proj (𝕜 := ℝ) k.2).contDiff.comp
        ((contDiff_apply ℝ (Euc 1) k.1).comp hΦ)
    exact (hf.continuous_fderiv (by simp)).clm_apply continuous_const
  · have : Continuous fun Y : Fin N → Euc 1 => ζ (q1mk N Y) i :=
      (continuous_apply i).comp hΦ.continuous
    exact (this.norm).pow 2

lemma q2_F_cont (D : DynData 1) (hV : Torus.IsCk 1 D.V) {ζ : Config 1 N → (Fin N → Euc 1)}
    (hζ : IsFisherTestField ζ) : Continuous (q1F D ζ) := by
  rw [q1mk_quot.continuous_iff]
  have : (q1F D ζ ∘ q1mk N) = q1G D ζ := funext fun Y => q1F_mk D ζ Y
  rw [this]
  exact q2_G_cont D hV hζ

end HRS.MC.CepH5Pf
