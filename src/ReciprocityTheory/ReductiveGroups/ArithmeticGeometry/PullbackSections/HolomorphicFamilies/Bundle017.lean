module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle011
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.LocalToGlobal.LatticeGeometry.CmTypeMeetsConjugatePair
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle032
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle001

@[expose] public section

section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem weight_floor_inequalities (a aW Dm c1 c2 T T' : ℤ) (hT' : T' = T + Dm + 2) (hD : 0 ≤ Dm) (h40 : 40 * (Dm + 2) ≤ T)
    (hc : c1 + c2 ≤ T) (ha : 2 * T ^ 2 ≤ a) (hW : aW = Int.fdiv (a - c1 - c2) T') :
    T' ≤ aW ∧ a + 1 ≤ (T + Dm + 4) * aW := by
  have hTp : 0 < T' := by omega
  rw [Int.fdiv_eq_ediv, if_pos (Or.inl hTp.le), sub_zero] at hW
  have h1 : (a - c1 - c2) % T' + T' * ((a - c1 - c2) / T') = a - c1 - c2 := by
    first
      | exact Int.emod_add_ediv _ _
      | exact Int.emod_add_mul_ediv _ _
      | (rw [Int.emod_def]; ring)
      | (rw [Int.mul_comm]; exact Int.emod_add_ediv' _ _)
      | exact (by simp [Int.emod_def])
  have h2 : 0 ≤ (a - c1 - c2) % T' := Int.emod_nonneg _ hTp.ne'
  have h3 : (a - c1 - c2) % T' < T' := Int.emod_lt_of_pos _ hTp
  rw [← hW] at h1
  have hN : T' * T' ≤ a - c1 - c2 := by
    subst hT'
    nlinarith [mul_nonneg (sub_nonneg.2 h40) (by omega : (0:ℤ) ≤ T), mul_nonneg (sub_nonneg.2 h40) (by omega : (0:ℤ) ≤ Dm + 2), mul_nonneg hD (by omega : (0:ℤ) ≤ T)]
  have hq : T' ≤ aW := by
    by_contra hc'
    have h4 : aW ≤ T' - 1 := by omega
    nlinarith [mul_le_mul_of_nonneg_left h4 hTp.le]
  refine ⟨hq, ?_⟩
  subst hT'
  nlinarith

theorem degP_le_mul {D : D7} {j : ℕ} (x z : WeightFamilies.Wt D j) (c : ℕ) (h1 : ∀ τ i, x.aP τ i ≤ c * z.aP τ i)
    (h2 : ∀ τ i, x.aM τ i ≤ c * z.aM τ i) : degP x ≤ c * degP z := by
  unfold degP
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun τ _ => ?_
  rw [mul_add, Finset.mul_sum, Finset.mul_sum]
  exact add_le_add (Finset.sum_le_sum fun i _ => h1 τ i) (Finset.sum_le_sum fun i _ => h2 τ i)

theorem exists_tau_of_inPsi {D : D7} (Q : Par D) (hp : Q.PinHost) (τ : D.host.E →+* ℂ) (hτ : InPsi Q.H τ) :
    ∃ t : D.what₂.Tau, τ = DV.tauEmb D t := by
  obtain ⟨g, hg⟩ := (factEmb D.R D.host).1.2 τ
  by_cases hgP : g ∈ D.R.Psi
  · obtain ⟨t, ht⟩ := (Formalism.L2.Geo.exists_tauEmb_iff D g).2 hgP
    exact ⟨t, hg.symm.trans ht⟩
  · exfalso
    have h2 : g * D.R.cc ∈ D.R.Psi := by
      by_contra h
      exact hgP ((Formalism.L2.Geo.mem_Psi_iff_mul_cc_notMem g).2 h)
    obtain ⟨t, ht⟩ := (Formalism.L2.Geo.exists_tauEmb_iff D (g * D.R.cc)).2 h2
    have h3 : DV.tauEmb D t (Q.H.rt : D.host.E) = Q.H.rt0 := hp.2.2.2 t
    rw [← ht, Formalism.L2.Geo.emb_mul_cc_comp, hg, RingHom.comp_apply] at h3
    have h4 : τ (D.host.conj (Q.H.rt : D.host.E)) = star (τ (Q.H.rt : D.host.E)) := Formalism.MainNotions.WeightFamilies.emb_conj D τ _
    have hτ' : τ (Q.H.rt : D.host.E) = Q.H.rt0 := hτ
    have h5 : (starRingEnd ℂ) Q.H.rt0 = Q.H.rt0 := by
      have : star Q.H.rt0 = Q.H.rt0 :=
        calc star Q.H.rt0 = star (τ (Q.H.rt : D.host.E)) := by rw [hτ']
          _ = τ (D.host.conj (Q.H.rt : D.host.E)) := h4.symm
          _ = Q.H.rt0 := h3
      exact this
    obtain ⟨x, hx⟩ := Complex.conj_eq_iff_real.1 h5
    have h6 := Q.H.sqrt_neg_disc_sq
    rw [hx] at h6
    have h7 : x ^ 2 = -(Q.H.d : ℝ) := by exact_mod_cast h6
    have h8 : (0 : ℝ) < Q.H.d := by exact_mod_cast Q.H.d_prime.pos
    nlinarith [sq_nonneg x]

theorem lastPos_wtA {D : D7} {T : Top D} (h : LawsP T) {j : ℕ} (hj : InR D j) (w : WeightFamilies.Wt D j) (hw : w.LastPos) :
    Formalism.L2.Pj.LastPos (T.Q.Dw j) (wtA w) := by
  intro τ hτ hm
  obtain ⟨t, rfl⟩ := exists_tau_of_inPsi T.Q h.pins.1 τ hτ
  have hmult : (T.Q.Dw j).mult (DV.tauEmb D t) = (D.R.sigW j).1 := by
    unfold Datum.mult
    have hτ' : (DV.tauEmb D t) (T.Q.H.rt : D.host.E) = T.Q.H.rt0 := hτ
    rw [if_pos hτ']
    exact (h.pins.2.2.2 j hj).1
  rw [hmult] at hm ⊢
  have h1 : 1 ≤ w.aP t ⟨(D.R.sigW j).1 - 1, by omega⟩ := hw t _ (by show (D.R.sigW j).1 - 1 + 1 = _; omega)
  have h2 : ext0 (w.aP t) ((D.R.sigW j).1 - 1) = w.aP t ⟨(D.R.sigW j).1 - 1, by omega⟩ := by
    unfold ext0
    rw [dite_eq_left (by omega)]
  unfold wtA
  classical
  refine lt_of_lt_of_le ?_ (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ t))
  simp only [if_true]
  omega

theorem theta_weight_bounds : ReciprocityTheory.ChartRestriction.G.PullbackSections.ThetaWeightBounds := by
  intro D T h large₂ H C2 A2 CR CT j hj ka wL wF Tn nP nW h0 hP
  obtain ⟨-, hS, hH3, -, -⟩ := hP
  obtain ⟨-, -, -, h4, -, h6, -, -, -, h10, h11, -, -, -, hL, hF, -, hT, -, h40, h21, h22, -⟩ := hS
  have hq : ((WeightFamilies.dimY D j + 4) * WeightAlgebra.DF wL : ℝ) ≤ (qq D : ℝ) - 2 := hH3.2.2.2.2.2
  have hq' : (WeightFamilies.dimY D j + 4) * WeightAlgebra.DF wL + 2 ≤ qq D := by
    have : (((WeightFamilies.dimY D j + 4) * WeightAlgebra.DF wL + 2 : ℕ) : ℝ) ≤ (qq D : ℝ) := by push_cast; linarith
    exact_mod_cast this
  have hf : 1 ≤ D.R.f := by
    have hm := D.R.two_le_m
    have hmf := D.R.m_le_f
    unfold Ranks.f Ranks.n
    omega
  have hr : D.R.r ≤ nP := by
    have : 1 * D.R.r ≤ 8 * D.R.f * D.R.r := Nat.mul_le_mul_right _ (by omega)
    omega

  have key : ∀ τ (i : Fin (D.R.sigW j).1), i.1 + 1 = (D.R.sigW j).1 →
      ((Tp D j Tn : ℕ) : ℤ) ≤ wL.aP τ i ∧ (ka.aP τ i : ℤ) + 1 ≤ ((Tn : ℤ) + WeightFamilies.dimY D j + 4) * wL.aP τ i := by
    intro τ i hi
    have hn : ¬ i.1 + 1 < (D.R.sigW j).1 := by omega
    have h3 := hL.2.1 τ i
    rw [if_neg hn] at h3
    unfold gapZ at h3
    rw [dite_eq_right hn] at h3
    have hc : (2 * (Tn : ℝ) ^ 2) ≤ (ka.aP τ i : ℝ) := by have := h6 τ i hi; linarith
    have hc' : 2 * Tn ^ 2 ≤ ka.aP τ i := by exact_mod_cast hc
    exact weight_floor_inequalities (ka.aP τ i) (wL.aP τ i) (WeightFamilies.dimY D j) (((WeightFamilies.dimY D j : ℤ) + 2) * nW) (2 * D.R.r) Tn (Tp D j Tn)
      (by unfold Tp; push_cast; ring) (Int.natCast_nonneg _) (by exact_mod_cast h40) (by exact_mod_cast h21)
      (by exact_mod_cast hc') h3
  refine ⟨fun w2 hG => ⟨?_, lastPos_wtA h hj w2 ?_, ?_⟩, fun _ w1 hG => ⟨?_, lastPos_wtA h hj w1 ?_, ?_⟩⟩
  · have e := hG.1
    rw [hL.1, hF.1] at e
    have : 1 * nW ≤ (WeightFamilies.dimY D j + 3) * nW := Nat.mul_le_mul_right _ (by omega)
    have e2 : (WeightFamilies.dimY D j + 4) * nW = (WeightFamilies.dimY D j + 3) * nW + nW := by ring
    omega
  · intro τ i hi
    obtain ⟨-, k2⟩ := key τ i hi
    have e1 : (w2.aP τ i : ℤ) + wF.aP τ i = ((WeightFamilies.dimY D j : ℤ) + 4) * wL.aP τ i := by exact_mod_cast hG.2.1 τ i
    have e2 := hF.2.1 τ i
    have : (1 : ℤ) ≤ w2.aP τ i := by nlinarith
    exact_mod_cast this
  · have : WeightAlgebra.DF w2 ≤ (WeightFamilies.dimY D j + 4) * WeightAlgebra.DF wL :=
      degP_le_mul w2 wL _ (fun τ i => by have := hG.2.1 τ i; omega) (fun τ i => by have := hG.2.2 τ i; omega)
    omega
  · have e := hG.1
    omega
  · intro τ i hi
    obtain ⟨k1, -⟩ := key τ i hi
    have e1 := hG.2.1 τ i
    have k3 : (1 : ℤ) ≤ wL.aP τ i := by
      have : (1 : ℤ) ≤ ((Tp D j Tn : ℕ) : ℤ) := by unfold Tp; push_cast; omega
      omega
    have k4 : 1 ≤ wL.aP τ i := by exact_mod_cast k3
    omega
  · have h1 : WeightAlgebra.DF w1 ≤ 2 * WeightAlgebra.DF wL :=
      degP_le_mul w1 wL 2 (fun τ i => (hG.2.1 τ i).le) (fun τ i => (hG.2.2 τ i).le)
    have h2 : 2 * WeightAlgebra.DF wL ≤ (WeightFamilies.dimY D j + 4) * WeightAlgebra.DF wL := Nat.mul_le_mul_right _ (by omega)
    omega

end ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf
end
end

section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.PfTies1

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem cuspTie : CuspTieSt := by
  intro D T h j hj w hlast x P hP f hf
  exact h.thCusp j hj _ _ (dom_wtA w) hlast f ⟨x, P, hP, hf⟩

lemma sum_extendByZero_le_sum {p : ℕ} (g : Fin p → ℕ) (m : ℕ) : ∑ i : Fin m, ext0 g i ≤ ∑ i : Fin p, g i := by
  unfold ext0
  have hF : ∀ n : ℕ, (∑ i : Fin n, (if h : (i : ℕ) < p then g ⟨i, h⟩ else 0)) =
      ∑ k ∈ Finset.range n, (if h : k < p then g ⟨k, h⟩ else 0) := fun n =>
    Fin.sum_univ_eq_sum_range (fun k => if h : k < p then g ⟨k, h⟩ else 0) n
  have hg : (∑ i : Fin p, g i) = ∑ i : Fin p, (if h : (i : ℕ) < p then g ⟨i, h⟩ else 0) :=
    Finset.sum_congr rfl (fun i _ => by simp)
  rw [hg, hF m, hF p]
  calc ∑ k ∈ Finset.range m, (if h : k < p then g ⟨k, h⟩ else 0)
      ≤ ∑ k ∈ Finset.range (max m p), (if h : k < p then g ⟨k, h⟩ else 0) :=
        Finset.sum_le_sum_of_subset (Finset.range_mono (le_max_left m p))
    _ = ∑ k ∈ Finset.range p, (if h : k < p then g ⟨k, h⟩ else 0) := by
        symm
        apply Finset.sum_subset (Finset.range_mono (le_max_right m p))
        intro k _ hk
        rw [Finset.mem_range] at hk
        rw [dite_eq_right hk]

open Classical in
lemma sum_single_embedding_extend_le {E : Type} [Field E] [NumberField E] (e : E →+* ℂ) (mult : (E →+* ℂ) → ℕ) {p : ℕ}
    (g : Fin p → ℕ) :
    ∑ τ : E →+* ℂ, ∑ i : Fin (mult τ), (if τ = e then ext0 g i else 0) ≤ ∑ i, g i := by
  rw [Finset.sum_eq_single e]
  · simp only [eq_self_iff_true, if_true]
    exact sum_extendByZero_le_sum g (mult e)
  · intro τ _ hτ
    exact Finset.sum_eq_zero (fun i _ => if_neg hτ)
  · intro h
    exact absurd (Finset.mem_univ e) h

open Classical in
lemma DF_wtA_le {D : D7} {j : ℕ} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} (Dw : Datum H)
    (w : WeightFamilies.Wt D j) :
    DF Dw (wtA w) ≤ ∑ t, ((∑ i, w.aP t i) + ∑ i, w.aM t i) := by
  have hswap : ∀ F : (τ : D.host.E →+* ℂ) → Fin (Dw.mult τ) → D.what₂.Tau → ℕ,
      ∑ τ, ∑ i : Fin (Dw.mult τ), ∑ t, F τ i t = ∑ t, ∑ τ, ∑ i : Fin (Dw.mult τ), F τ i t := by
    intro F
    calc ∑ τ, ∑ i : Fin (Dw.mult τ), ∑ t, F τ i t = ∑ τ, ∑ t, ∑ i : Fin (Dw.mult τ), F τ i t :=
          Finset.sum_congr rfl (fun τ _ => Finset.sum_comm)
      _ = ∑ t, ∑ τ, ∑ i : Fin (Dw.mult τ), F τ i t := Finset.sum_comm
  unfold Formalism.L2.Pj.DF wtA
  rw [hswap]
  apply Finset.sum_le_sum
  intro t _
  simp only [Finset.sum_add_distrib]
  exact add_le_add (by convert sum_single_embedding_extend_le (DV.tauEmb D t) Dw.mult (w.aP t))
    (by convert sum_single_embedding_extend_le (conjEmb (DV.tauEmb D t)) Dw.mult (w.aM t))

theorem dimPos_fr (D : D7) : 1 ≤ D.R.f ∧ 1 ≤ D.R.r := by
  refine ⟨?_, ?_⟩
  · have h1 := D.R.two_le_m
    have h2 := D.R.m_le_f
    exact le_trans (by omega : 1 ≤ D.R.m) h2
  · have h3 := D.R.m_add_three_le_k
    unfold Formalism.BasicNotions.Ranks.r
    omega

end ReciprocityTheory.ChartRestriction.G.PullbackSections.PfTies1
end
end

section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf

open NumberField Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions

theorem nzdOfComp_of_conn
    (hc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r), IsPreconnected X.dom) :
    ReciprocityTheory.ChartRestriction.G.PullbackSections.NZDOfCompSt := by
  intro D T h j hj w F σ hσ hne w' G hFG
  have hFc : (F : T.R j) ∈ T.C j w := cutR_le T.C j w F.2
  have hGc : (G : T.R j) ∈ T.C j w' := cutR_le T.C j w' G.2
  have hmem : (F : T.R j) * (G : T.R j) ∈ cutR T.C j (WeightAlgebra.wadd w w') := by
    rw [cutR_eq T.C hj]; exact h.toLawsCore.mul j hj w w' _ hFc _ hGc
  have hval : (F : T.R j) * (G : T.R j) = 0 := by
    have h1 : incG deg (cutR T.C j) w F * incG deg (cutR T.C j) w' G = 0 := hFG
    rw [incG_mul deg (cutR T.C j) (deg_wadd w w') F G hmem] at h1
    have h2 := incG_inj deg (cutR T.C j) _ (h1.trans (map_zero _).symm)
    exact congrArg Subtype.val h2
  have hU := h.unf j hj σ hσ
  have hrd : rdU (T.U j σ) (F : T.R j) * rdU (T.U j σ) (G : T.R j) = 0 := by
    rw [← rdU_mul, hval, map_zero]
  have hFs := fun k => (hU.2.2.2.2.1 _ _ (dom_wtA w) _ (cusp_le_sec _ _ _ _ _ hFc) k).1
  have hGs := fun k => (hU.2.2.2.2.1 _ _ (dom_wtA w') _ (cusp_le_sec _ _ _ _ _ hGc) k).1
  have hG0 : ∀ k, ∀ y ∈ ((T.U j σ).X k).dom, rdU (T.U j σ) (G : T.R j) k y = 0 := by
    intro k
    obtain ⟨x0, hx0, hx0ne⟩ := hne k
    exact eq_zero_of_mul_eq_zero (FourierCoefficientDomain.isOpen_dom _) (hc _ _ _) (hFs k) (hGs k)
      (fun y _ => congrFun (congrFun hrd k) y) hx0 hx0ne
  have hsup : supN (T.U j σ).X (laU (T.U j σ) (wtA w') w'.n) (rdU (T.U j σ) (G : T.R j)) = 0 := by
    unfold supN supE
    have h0 : ∀ p : FPt (T.U j σ).X, ENNReal.ofReal (((T.U j σ).X p.1).pnorm (laU (T.U j σ) (wtA w') w'.n p.1)
        (rdU (T.U j σ) (G : T.R j) p.1) p.2) = 0 := by
      intro p
      unfold Data.pnorm
      rw [hG0 p.1 p.2 p.2.2]
      simp
    simp [h0]
  exact Subtype.ext (h.supDef j hj _ _ (dom_wtA w') σ hσ _ hGc hsup)

end ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf
end
end
