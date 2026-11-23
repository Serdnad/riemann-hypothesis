module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle048
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsFrameOfForallExists
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1706
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle049
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1708
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1707
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPolyRepInducedBundleAndMetric
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle008
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle050
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CompactHaarRightInvariantInst
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.KoszulLowersPower
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.Bundle001
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.Bundle002
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.LayerLeGeneratedTensorFock
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.SupTrace
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.Bundle004
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.TraceIntegralRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle481
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.DiracSquareMemLayer

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory

namespace GlobalTheory.HSKerRes

section Dictionary

variable {Y : Scheme.{0}} {M N : LB Y} {O W : Y.Opens}

theorem coord_resM (h : W ≤ O) (s : Γ(LB.toMod M, O)) (i : M.ι) :
    LB.coord (Twist.resM (LB.toMod M) h s) i = resG Y (inf_le_inf_right _ h) (LB.coord s i) :=
  LB.coord_map h s i

theorem le_tens (O : Y.Opens) (q : (tens M N).ι) : O ⊓ (tens M N).U q ≤ O ⊓ N.U q.2 ⊓ M.U q.1 :=
  fun _ hy => ⟨⟨hy.1, hy.2.2⟩, hy.2.1⟩

def ofTwistFun (s : Γ(twist (LB.toMod M) N, O)) : Γ(LB.toMod (tens M N), O) :=
  LB.mkSec (fun q => resG Y (le_tens O q) (LB.coord (Twist.coord s q.2) q.1)) fun p q => by
    have h₁ : O ⊓ (tens M N).U p ⊓ (tens M N).U q ≤ O ⊓ N.U p.2 := fun _ hy => ⟨hy.1.1, hy.1.2.2⟩
    have h₂ : O ⊓ (tens M N).U p ⊓ (tens M N).U q ≤ O ⊓ N.U q.2 := fun _ hy => ⟨hy.1.1, hy.2.2⟩
    have h₃ : O ⊓ (tens M N).U p ⊓ (tens M N).U q ≤ M.U p.1 := fun _ hy => hy.1.2.1
    have h₄ : O ⊓ (tens M N).U p ⊓ (tens M N).U q ≤ M.U q.1 := fun _ hy => hy.2.1
    have e₁ := congrArg (fun r => resG Y (le_inf le_rfl h₄) (LB.coord r q.1))
      (Twist.coord_rel s p.2 q.2 h₁ h₂ (le_inf (h₁.trans inf_le_right) (h₂.trans inf_le_right)))
    have e₂ := LB.coord_rel (Twist.coord s p.2) p.1 q.1 (le_inf h₁ h₃) (le_inf h₁ h₄) (le_inf h₃ h₄)
    simp only [coord_resM, LB.coord_smul, map_mul, LB.resG_resG] at e₁
    simp only [LB.resG_resG]
    refine e₂.trans ?_
    rw [e₁, ← mul_assoc]
    refine congrArg (· * _) ?_
    exact ((map_mul _ _ _).trans (congrArg₂ (· * ·) (LB.resG_resG _ _ _) (LB.resG_resG _ _ _))).symm

theorem coord_ofTwistFun (s : Γ(twist (LB.toMod M) N, O)) (q : (tens M N).ι) :
    LB.coord (ofTwistFun s) q = resG Y (le_tens O q) (LB.coord (Twist.coord s q.2) q.1) := rfl

def ofTwist : Γ(twist (LB.toMod M) N, O) →+ Γ(LB.toMod (tens M N), O) where
  toFun := ofTwistFun
  map_zero' := LB.sec_ext fun q => by
    rw [coord_ofTwistFun, Twist.coord_zero, LB.coord_zero, map_zero, LB.coord_zero]
  map_add' s t := LB.sec_ext fun q => by
    rw [LB.coord_add, coord_ofTwistFun, coord_ofTwistFun, coord_ofTwistFun, Twist.coord_add, LB.coord_add, map_add (f := _)]

theorem tens_le (O : Y.Opens) (i : M.ι) (j : N.ι) : O ⊓ N.U j ⊓ M.U i ≤ O ⊓ (tens M N).U (i, j) :=
  fun _ hy => ⟨hy.1.1, hy.2, hy.1.2⟩

theorem tens_rel (f : Γ(LB.toMod (tens M N), O)) (i i' : M.ι) (j j' : N.ι) (h : W ≤ O ⊓ (tens M N).U (i, j))
    (h' : W ≤ O ⊓ (tens M N).U (i', j')) (hM : W ≤ M.U i ⊓ M.U i') (hN : W ≤ N.U j ⊓ N.U j') :
    resG Y h (LB.coord f (i, j)) = resG Y hM (M.g i i' : Γ(Y, M.U i ⊓ M.U i')) *
      resG Y hN (N.g j j' : Γ(Y, N.U j ⊓ N.U j')) * resG Y h' (LB.coord f (i', j')) := by
  refine (LB.coord_rel f (i, j) (i', j') h h' (le_inf (h.trans inf_le_right) (h'.trans inf_le_right))).trans ?_
  refine congrArg (· * _) ?_
  exact (map_mul _ _ _).trans (congrArg₂ (· * ·) (LB.resG_resG _ _ _) (LB.resG_resG _ _ _))

theorem surjective_ofTwist (hM : M.IsLB) (hN : N.IsLB) :
    Function.Surjective (ofTwist : Γ(twist (LB.toMod M) N, O) → Γ(LB.toMod (tens M N), O)) := fun f => by
  let a : ∀ j : N.ι, Γ(LB.toMod M, O ⊓ N.U j) := fun j =>
    LB.mkSec (fun i => resG Y (tens_le O i j) (LB.coord f (i, j))) fun i i' => by
      simp only [LB.resG_resG]
      refine (tens_rel f i i' j j _ (by exact fun _ hy => ⟨hy.1.1.1, hy.2, hy.1.1.2⟩)
        (by exact fun _ hy => ⟨hy.1.2, hy.2⟩) (by exact fun _ hy => ⟨hy.1.1.2, hy.1.1.2⟩)).trans ?_
      exact congrArg (· * _) ((congrArg (_ * ·) (LB.resG_g_self hN _ _)).trans (mul_one _))
  have ha : ∀ j i, LB.coord (a j) i = resG Y (tens_le O i j) (LB.coord f (i, j)) := fun _ _ => rfl
  refine ⟨Twist.mkSec a fun j j' => LB.sec_ext fun i => ?_, LB.sec_ext fun q => ?_⟩
  · simp only [coord_resM, LB.coord_smul, ha, LB.resG_resG]
    refine (tens_rel f i i j j' _ (by exact fun _ hy => ⟨hy.1.1.1, hy.2, hy.1.2⟩)
      (by exact fun _ hy => ⟨hy.2, hy.2⟩) (by exact fun _ hy => ⟨hy.1.1.2, hy.1.2⟩)).trans ?_
    exact congrArg (· * _) ((congrArg (· * _) (LB.resG_g_self hM _ _)).trans (one_mul _))
  · refine (coord_ofTwistFun _ q).trans ?_
    exact (LB.resG_resG (tens_le O q.1 q.2) (le_tens O q) (LB.coord f q)).trans (LB.resG_self _ _)

variable {k : Type} [CommRing k] (p : Y ⟶ Sp k) {L : LB Y} {n l : ℤ}

def toH0 : Γ(twistZ (LB.toMod M) L n, O) →+ Vanishing.H0 p (tw M L n) O := ofTwist

theorem restricted_section_chart_coords (s : Γ(twistZ (LB.toMod M) L n, O)) (i : M.ι) (j : L.ι)
    (h : W ≤ O ⊓ (tw M L n).U (twIdx n i j)) (h' : W ≤ O ⊓ L.U j ⊓ M.U i) :
    resG Y h ((toH0 p s).loc (twIdx n i j)) = resG Y h' (LB.coord (Twist.zcoord s j) i) := by
  rw [Twist.zcoord, coord_resM, LB.resG_resG]
  exact LB.resG_resG _ _ _

theorem germ_of_global_section (s : Γ(twistZ (LB.toMod M) L n, O)) (i : M.ι) (j : L.ι) (y : Y) (hy : y ∈ O)
    (hi : y ∈ M.U i) (hj : y ∈ L.U j) :
    H0.germ (twIdx n i j) y hy (mem_tw_U.2 ⟨hi, hj⟩) (toH0 p s) =
      ger y (memInf (memInf hy hj) hi) (LB.coord (Twist.zcoord s j) i) := by
  have h : O ⊓ L.U j ⊓ M.U i ≤ O ⊓ (tw M L n).U (twIdx n i j) := fun _ hz => ⟨hz.1.1, mem_tw_U.2 ⟨hz.2, hz.1.2⟩⟩
  have e := congrArg (ger y (memInf (memInf hy hj) hi)) (restricted_section_chart_coords p s i j h le_rfl)
  rwa [ger_resG, ger_resG] at e

theorem global_section_mul (hM : M.IsLB) (hL : L.IsLB) (w : L.Sec) (h : n + 1 = l) (s : Γ(twistZ (LB.toMod M) L n, O)) :
    toH0 p ((Twist.mulSecOfEq (LB.toMod M) (Twist.zofSec w) h).app O s) = mulSec hM hL w h (toH0 p s) :=
  tw_ext hM hL fun i j y hy hi hj => by
    rw [germ_mulSec _ _ _ _ _ _ _ _ _ hi hj, germ_of_global_section p _ i j y hy hi hj, germ_of_global_section p _ i j y hy hi hj,
      Twist.zcoord_mulSecOfEq_app, LB.coord_smul, map_mul, ger_resG, ger_resG, Twist.zfun_zofSec]

theorem exists_local (hM : M.IsLB) (hL : L.IsLB) {d : ℕ} (t : Fin d → L.Sec) (h : n + 1 = l)
    (s : Γ(twistZ (LB.toMod M) L l, ⊤)) (hs : VanishesTo (cutIdeal hL t) 1 (toH0 p s)) (y : Y) :
    ∃ (W : Y.Opens) (_ : y ∈ W) (m : Fin d → Γ(twistZ (LB.toMod M) L n, W)),
      (twistZ (LB.toMod M) L l).presheaf.map (homOfLE le_top).op s =
        ∑ i, (Twist.mulSecOfEq (LB.toMod M) (Twist.zofSec (t i)) h).app W (m i) := by
  obtain ⟨i, hi⟩ := exists_chart hM y
  obtain ⟨j, hj⟩ := exists_chart hL y
  obtain ⟨V, hV, e⟩ := exists_affine (memInf hi hj)
  have hVi : V.1 ≤ M.U i := e.trans inf_le_left
  have hVj : V.1 ≤ L.U j := e.trans inf_le_right
  have h₁ : V.1 ≤ ⊤ ⊓ (tw M L l).U (twIdx l i j) := fun _ hz => ⟨trivial, mem_tw_U.2 ⟨hVi hz, hVj hz⟩⟩
  have h₂ := vanishesTo_iff_affine.1 hs V _ h₁
  rw [pow_one, ideal_cutIdeal hL t V j hVj, restricted_section_chart_coords p s i j h₁ (le_inf (le_inf le_top hVj) hVi)] at h₂
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.1 h₂
  refine ⟨V.1, hV, fun a => (Twist.zchartEquiv hL n j hVj).symm ((LB.chartEquiv hM i hVi).symm (c a)), ?_⟩
  refine (Twist.zchartEquiv hL l j hVj).injective ((LB.chartEquiv hM i hVi).injective ?_)

  simp only [map_sum, Twist.zchartEquiv_mulSecOfEq_app, map_smul, LinearEquiv.apply_symm_apply, Twist.zfun_zofSec,
  smul_eq_mul]
  rw [LB.chartEquiv_apply, Twist.zchartEquiv_apply]
  refine Eq.trans ?_ (hc.symm.trans (Finset.sum_congr rfl fun a _ => mul_comm _ _))
  rw [coord_resM]
  erw [Twist.zcoord_resM]
  rw [coord_resM, LB.resG_resG, LB.resG_resG]

end Dictionary

section Main

variable {K : Type} [Field K] [NumberField K] (G : Geo K)

theorem ger_comb_sum {ι : Type} [Fintype ι] (a : ι → K) (u : ι → Fin G.N → K) (j : G.L.ι) (y : G.Y) (hj : y ∈ G.L.U j) :
    ger y hj ((G.comb (∑ i, a i • u i)).f j) = ∑ i, H0.const G.str y (a i) * ger y hj ((G.comb (u i)).f j) := by
  have key (v : Fin G.N → K) : H0.ofSec G.str ⊤ (G.comb v) =
      Fintype.linearCombination K (fun c => H0.ofSec G.str ⊤ (G.b c)) v := G.ofSec_comb ⊤ v

  rw [← H0.germ_ofSec (p := G.str) j y (TopologicalSpace.Opens.mem_top y) hj, key, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, H0.germ_smul, ← key, H0.germ_ofSec]

theorem vanishesTo_of_isUnit (s : Fin G.D → Fin G.N → K) (g : Matrix (Fin G.D) (Fin G.D) K) (hg : IsUnit g.det)
    {B : LB G.Y} {O : G.Y.Opens} {f : Vanishing.H0 G.str B O} (hf : VanishesTo (G.ideal s) 1 f) :
    VanishesTo (G.ideal fun i => ∑ j, g i j • s j) 1 f := fun y _ hy c hc => by
  have h := vanishesTo_iff_forall.1 hf y hy c hc
  obtain ⟨j, hj⟩ := exists_chart G.isLB y
  rw [pow_one, stalkId_cutIdeal G.isLB _ j y hj] at h ⊢
  refine Ideal.span_le.2 (Set.range_subset_iff.2 fun a => ?_) h
  have e : s a = ∑ i, g⁻¹ a i • ∑ j, g i j • s j := by
    simp only [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul, ← Matrix.mul_apply, Matrix.nonsing_inv_mul g hg, Matrix.one_apply, ite_smul, one_smul,
      zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  change ger y hj ((G.comb (s a)).f j) ∈ Ideal.span _
  rw [e, ger_comb_sum]
  exact sum_mem fun i _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)

end Main

theorem exists_global {k : Type} [Field k] {Y : Scheme.{0}} [Algebra k Γ(Y, ⊤)] (hY : IsProjOver (GlobalTheory.strHom k (X := Y)))
    (p : Y ⟶ Sp k) {M L : LB Y} (hM : M.IsLB) (hL : L.IsLB) {d : ℕ} (t : Fin d → L.Sec) {n l : ℤ} (h : n + 1 = l)
    (hreg : RegSeq hL (LB.toMod M) (List.ofFn t)) (hvan : VanishFrom L (LB.toMod M) 0) (hd : (d : ℤ) ≤ n + 1)
    (f : Vanishing.H0 p (tw M L l) ⊤) (hf : VanishesTo (cutIdeal hL t) 1 f) :
    ∃ μ : Fin d → Vanishing.H0 p (tw M L n) ⊤, f = ∑ i, mulSec hM hL (t i) h (μ i) := by
  subst h
  obtain ⟨σ, rfl⟩ : ∃ σ : Γ(twistZ (LB.toMod M) L (n + 1), ⊤), toH0 p σ = f :=
    surjective_ofTwist hM (Twist.isLB_lbZPow hL _) f
  have := (VB.isVB_toMod hM).isFiniteQC
  obtain ⟨m, hm⟩ := GlobalTheory.T.exists_global_combination_of_local_regular_ideal k Y hY L hL d t (LB.toMod M) 0 n hreg hvan ((zero_add _).trans_le hd) σ
    (exists_local p hM hL t rfl σ hf)
  refine ⟨fun i => toH0 p (m i), (congrArg (toH0 p) hm).trans ?_⟩
  exact (map_sum (toH0 p) _ _).trans (Finset.sum_congr rfl fun i _ => global_section_mul p hM hL _ rfl (m i))

theorem kerRes : Quoted → KerRes := by
  intro Q K _ _ G hnef hbig s hs l hl f hf
  obtain ⟨⟨f, rfl⟩, hv⟩ := mem_Fil.1 hf
  have hB : (tens G.K.bundle G.LA).IsLB := isLB_tens G.K.isLB G.isLBA
  obtain ⟨g, hg, hreg⟩ := GlobalTheory.T.exists_basis_regular_sequence_of_common_zeros K G s hs _ hB
  have hv' := vanishesTo_of_isUnit G s g hg ((vanishesTo_restr_iff hs.inU le_top).1 hv)
  have hproj : IsProjOver (GlobalTheory.strHom K (X := G.Y)) := by
    rw [GlobalTheory.strHom_eq (f := G.str) fun _ => rfl]
    exact G.geom.alg.variety.proj
  obtain ⟨μ, e⟩ := exists_global hproj G.str hB G.isLB _ (Nat.cast_succ l).symm hreg (GlobalTheory.T.kawamataViehweg_vanishing_numberField_twist Q K G hnef hbig)
    (by exact_mod_cast hl) f hv'
  refine ⟨fun j => H0.restr le_top (∑ i, g i j • μ i), fun j => ⟨_, rfl⟩, ?_⟩
  have e' (i) : H0.restr (le_top : G.U ≤ ⊤) (mulSec hB G.isLB (G.comb (∑ j, g i j • s j)) (Nat.cast_succ l).symm (μ i)) =
      G.mulW l (∑ j, g i j • s j) (H0.restr le_top (μ i)) := by
    rw [G.mulW_apply, mulSec, mulSec, ProdChart.restr_mul, H0.restr_ofSec]

  rw [e, map_sum]

  simp only [e', map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
  exact Finset.sum_comm

end GlobalTheory.HSKerRes
end
end

section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

namespace GlobalTheory.ChernCalc

theorem isMetricFr_smoothUnitAt : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) [Finite ι] (m k : ι → ℕ) (E : Fr (ratOf X) m k) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ), IsMetricFr E H → ∀ (y : CxPts X.str σ), ∀ A ∈ E.S (under y), ∀ τ, SmoothUnitAt (atlas X σ) (fun z => H A z τ) y ∧ ∀ c : AlgChart X.str σ X.dim, y ∈ c.e.source → ∀ᶠ v in 𝓝 (c.e y), MContDiffAt ∞ (fun u => H A (c.e.symm u) τ) v ∧ (H A (c.e.symm v) τ).PosDef := by
  intro F _ σ X ι _ m k E H hH y A hA τ
  set U : Set (CxPts X.str σ) := interior {z : CxPts X.str σ | A ∈ E.S (under z)} with hU
  have hyU : y ∈ U := mem_interior_iff_mem_nhds.2 (GlobalTheory.T.adaptedFrame_eventually_frame_near_complex_point F σ X ι m k E y A hA)
  have hUo : IsOpen U := isOpen_interior
  have hUS : ∀ z ∈ U, A ∈ E.S (under z) := fun z hz => interior_subset (s := {z : CxPts X.str σ | A ∈ E.S (under z)}) hz
  have key : ∀ c : AlgChart X.str σ X.dim, y ∈ c.e.source → ∀ᶠ v in 𝓝 (c.e y),
      MContDiffAt ∞ (fun u => H A (c.e.symm u) τ) v ∧ (H A (c.e.symm v) τ).PosDef := by
    intro c hc
    have ho : IsOpen (c.e.target ∩ c.e.symm ⁻¹' U) := c.e.isOpen_inter_preimage_symm hUo
    have hm : c.e y ∈ c.e.target ∩ c.e.symm ⁻¹' U :=
      ⟨c.e.map_source hc, by simpa [Set.mem_preimage, c.e.left_inv hc] using hyU⟩
    filter_upwards [ho.mem_nhds hm] with v hv
    refine ⟨fun i j => ?_, hH.posDef _ A (hUS _ hv.2) τ⟩
    have hre := contDiffOn_chart (S := U) (f := fun z => (H A z τ i j).re)
      (fun z hz => (hH.smooth z A (hUS z hz) τ i j).1) c
    have him := contDiffOn_chart (S := U) (f := fun z => (H A z τ i j).im)
      (fun z hz => (hH.smooth z A (hUS z hz) τ i j).2) c
    have h1 := (hre.contDiffAt (ho.mem_nhds hv))
    have h2 := (him.contDiffAt (ho.mem_nhds hv))
    have h3 : ContDiffAt ℝ ∞ (fun u => ((((H A (c.e.symm u) τ i j).re : ℝ) : ℂ) +
        (((H A (c.e.symm u) τ i j).im : ℝ) : ℂ) * Complex.I)) v :=
      (Complex.ofRealCLM.contDiff.contDiffAt.comp v h1).add
        ((Complex.ofRealCLM.contDiff.contDiffAt.comp v h2).mul contDiffAt_const)
    refine h3.congr_of_eventuallyEq (Eventually.of_forall fun u => ?_)
    simp [Complex.re_add_im]
  refine ⟨⟨?_, fun c hc => (key c hc).mono fun v hv => hv.1⟩, key⟩
  exact (Matrix.isUnit_iff_isUnit_det _).1 (hH.posDef y A hA τ).isUnit

end GlobalTheory.ChernCalc
end

section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
open GlobalTheory.GoodMetric.RepBundle

namespace GlobalTheory.ChernCalc

theorem isMetricFr_pullGram : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X Y : Var F) (ι : Type) [Finite ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X) (hf : f ≫ X.str = Y.str), Refines E E' φ f → ∀ H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ, IsMetricOn E ⊤ H → IsMetricFr E' (pullGram E H φ f hf) := by
  intro F _ σ X Y ι _ m E E' φ f hf hR H hH
  have key := GlobalTheory.T.pulled_back_gram_matrices_independent_of_frame F σ X Y ι m E E' φ f hf hR H hH
  refine ⟨fun y B hB τ => ?_, fun y B hB τ i j => ?_, fun y B hB B' hB' τ => ?_⟩
  · obtain ⟨ψ, hψ⟩ := exists_ratVal_hom (X := Y) (σ := σ) y
    obtain ⟨A, hA⟩ := E.nonempty (f (under y))
    have hT := ((hR.sub _ B hB A hA).map_of (ratVal · y) ψ hψ).det_ne τ
    rw [(key y).2 A hA B hB τ]
    exact (hH.posDef _ mem_ptsIn_top A ((key y).1 ▸ hA) τ).mul_mul_conjTranspose_same
      (Matrix.vecMul_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det _).2 hT.isUnit))
  · obtain ⟨A, hA⟩ := E.nonempty (f (under y))
    have hA' : A ∈ E.S (under (ptMap σ f hf y)) := (key y).1 ▸ hA
    have hC := hR.sub _ B hB A hA
    have hc : Continuous (ptMap σ f hf) := GlobalTheory.Points.PtsOver.continuous_map f hf _
    have hev : ∀ᶠ z in 𝓝 y, pullGram E H φ f hf B z τ = (B * (A.map φ)⁻¹).map (ratVal · z) τ *
        H A (ptMap σ f hf z) τ * ((B * (A.map φ)⁻¹).map (ratVal · z) τ)ᴴ := by
      filter_upwards [hc.continuousAt.eventually (GlobalTheory.T.adaptedFrame_eventually_frame_near_complex_point F σ X ι m 0 E _ A hA'),
        GlobalTheory.T.adaptedFrame_eventually_frame_near_complex_point F σ Y ι m m E' y B hB] with z hAz hBz
      exact (key z).2 A ((key z).1 ▸ hAz) B hBz τ
    have hT : ∀ k l, CS (fun z => (B * (A.map φ)⁻¹).map (ratVal · z) τ k l) y := fun k l =>
      cs_ratVal (mem_O_ratOf.1 ((hC τ).1 k l))
    have hS : ∀ k l, CS (fun z => H A (ptMap σ f hf z) τ k l) y := fun k l =>
      ⟨CInfAt.pull f hf (hH.smooth _ mem_ptsIn_top A hA' τ k l).1,
        CInfAt.pull f hf (hH.smooth _ mem_ptsIn_top A hA' τ k l).2⟩
    exact CS.congr (v := fun z => pullGram E H φ f hf B z τ i j) (cs_conj_entry hT hS i j)
      (hev.mono fun z hz => by simp only [hz])
  · obtain ⟨ψ, hψ⟩ := exists_ratVal_hom (X := Y) (σ := σ) y
    obtain ⟨A, hA⟩ := E.nonempty (f (under y))
    have e := Par.map_mul_of ((Fr.mem_iff hB).1 hB') (hR.sub _ B hB A hA) (ratVal · y) ψ hψ
    rw [mul_assoc, ← mul_assoc B⁻¹, Mat.inv_mul (Fr.det_ne hB), one_mul] at e
    rw [(key y).2 A hA B hB τ, (key y).2 A hA B' hB' τ, e, Pi.mul_apply, Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]

end GlobalTheory.ChernCalc
end

section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open GlobalTheory.HSShort GlobalTheory.HSChoice MvPolynomial

theorem _root_.GlobalTheory.T.hilbertSamuelSectionShift_comm_single_monomial : ∀ (F : Type) [Field F] [NumberField F] (G : Geo F), (∀ u v, shift G u * shift G v = shift G v * shift G u) ∧ (∀ (j : ℕ) u (m : G.Sec j), shift G u (Pi.single j m) = Pi.single (j + 1) (G.mulW j u m)) ∧ ∀ (s : Fin G.D → Fin G.N → F) (a j l : ℕ) (h : j + a = l) (α : MonoDeg (Fin G.D) a) (m : G.Sec j), pw (shift G) s α.1 (Pi.single j m) = Pi.single l (mulPow G s h α m) := by
  first | exact @GlobalTheory.HSShort.shift_comm_single_mono | exact GlobalTheory.HSShort.shift_comm_single_mono | (intros; apply GlobalTheory.HSShort.shift_comm_single_mono <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open GlobalTheory.HSShort GlobalTheory.HSChoice MvPolynomial

theorem _root_.GlobalTheory.T.productOfVectorMultiplications_global_residues : ∀ (K : Type) [Field K] [NumberField K] (G : Geo K) (t j : ℕ) (u : Fin t → Fin G.N → K), ∀ x ∈ G.global j, ∃ x' ∈ G.global (j + t), word (shift G) u (Pi.single j x) = Pi.single (j + t) x' ∧ ∀ (s : Fin G.D → Fin G.N → K) (hs : G.IsGood s) (δ : ℕ) (Co : Coord G hs δ) (p : Fin δ), Co.ev (j + t) (hs.res (j + t) x') p = (∏ q, ∑ k, u q k * Co.y p k) * Co.ev j (hs.res j x) p := by
  first | exact @GlobalTheory.HSShort.GlobWord.word_global | exact GlobalTheory.HSShort.GlobWord.word_global | (intros; apply GlobalTheory.HSShort.GlobWord.word_global <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open GlobalTheory.HSShort GlobalTheory.HSChoice MvPolynomial

theorem _root_.GlobalTheory.T.hilbertSamuelLatticeSystem_hyp : ∀ (F : Type) [Field F] [NumberField F] (X : Data F) (Λ₀ : ℝ), GeoHyp X Λ₀ → (sysOf X Λ₀).Hyp := by
  first | exact @GlobalTheory.HSShort.GeoHyp.sysOf_hyp | exact GlobalTheory.HSShort.GeoHyp.sysOf_hyp | (intros; apply GlobalTheory.HSShort.GeoHyp.sysOf_hyp <;> assumption)
end

section

section
open GlobalTheory.PsCo.PcEG

noncomputable section

open MeasureTheory ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.TRGap
open Formalism.REAL (KG toMK muK)
open GlobalTheory.PsCo.Pc1 (Mat Poly ev)

namespace GlobalTheory.PsCo.PcEF

theorem StrIdx_proof2 : StrIdx := by
  intro n ε P
  choose Qm hQm using fun s s' : Finset (Fin (n * n)) => ffMat_poly (ε := ε) s s'
  set Q : Poly n := ∑ s ∈ Finset.univ.filter (IsPhysSet ε), ((-1 : ℂ) ^ s.card) • Qm s s with hQdef
  have hQ : ∀ m : Mat n, ev m Q = physDet ε m := by
    intro m
    show MvPolynomial.eval (entVar m) Q = _

    rw [← strPhys_eq_physDet, strPhys, hQdef, map_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [MvPolynomial.smul_eval, hQm]
    rfl
  obtain ⟨d2, hd2⟩ : ∃ d2 : ℕ, ∀ s s' : Finset (Fin (n * n)), (P * Qm s s').totalDegree ≤ d2 :=
    ⟨∑ s, ∑ s', (P * Qm s s').totalDegree, fun s s' =>
      le_trans (Finset.single_le_sum (f := fun s' => (P * Qm s s').totalDegree) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ s'))
      (Finset.single_le_sum (f := fun s => ∑ s', (P * Qm s s').totalDegree) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ s))⟩
  refine ⟨max (P * Q).totalDegree d2, ?_⟩
  intro H _ _ _ σ D E hσ hD L _ hLK hLd Y _ hY0Y hYP hG hK B hB
  have hdeg1 : (P * Q).totalDegree ≤ max (P * Q).totalDegree d2 := le_max_left _ _
  have hdeg2 : ∀ s s', (P * Qm s s').totalDegree ≤ max (P * Q).totalDegree d2 := fun s s' =>
    (hd2 s s').trans (le_max_right _ _)
  have hemb : Topology.IsEmbedding (fun k : KG ε => toMK k) :=
    (Formalism.REAL.isClosedEmbeddingMatrix n ε).1.isEmbedding.comp Topology.IsEmbedding.subtypeVal
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
  have : SecondCountableTopology (KG ε) := hemb.isInducing.secondCountableTopology
  have hφc : Continuous (fun k : KG ε => toMK k) := hemb.continuous
  have hφK : ∀ g : KG ε, toMK g ∈ Kset ε := fun g => g.2
  have hent : ∀ R : Poly n, Continuous fun k : KG ε => ev (toMK k) R := by
    intro R
    refine (MvPolynomial.continuous_eval R).comp (continuous_pi fun p => ?_)
    rcases p with p | p
    · exact (continuous_apply p.2).comp ((continuous_apply p.1).comp hφc)
    · exact continuous_star.comp ((continuous_apply p.2).comp ((continuous_apply p.1).comp hφc))
  have hBL : ∀ w, B w ∈ L.map D.subtype := by
    intro w
    rw [hB]
    have := hLd (P * Q) hdeg1 w
    simpa only [map_mul, hQ] using this
  refine ⟨hBL, ?_⟩
  have hAL : ∀ k : KG ε, ∀ x ∈ L.map D.subtype, σ (toMK k) x ∈ L.map D.subtype := by
    rintro k _ ⟨y, hy, rfl⟩
    exact ⟨sigD hD (hφK k) y, hLK _ (hφK k) y hy, rfl⟩
  have hAc : ∀ v, Continuous fun k : KG ε => σ (toMK k) v := fun v =>
    (hσ.2.2 v).comp_continuous hφc fun g => kset_mem_UJset (hφK g)
  have hcont : Continuous fun k : KG ε => ev (toMK k) P * physDet ε (toMK k) := by
    have := hent (P * Q)
    simpa only [map_mul, hQ] using this
  rw [trace_integral_restrict (μ := muK ε) (L.map D.subtype) hcont (fun k => σ (toMK k)) hAc hAL B hB
    (fun x _ => hBL x)]
  have hY0G : ∀ y ∈ tensFock (n := n) L ⊓ physicalSubspace (N := D) ε, gradT y ∈ tensFock (n := n) L ⊓ physicalSubspace (N := D) ε :=
    fun y hy => ⟨tensFock_lTensor_stable _ hy.1, (physSub_stable ε E).2.2.2.2 y hy.2⟩
  have hY0K : ∀ (k : Matrix (Fin n) (Fin n) ℂ) (hk : k ∈ Kset ε), ∀ y ∈ tensFock (n := n) L ⊓ physicalSubspace (N := D) ε,
      wK hD hk y ∈ tensFock (n := n) L ⊓ physicalSubspace (N := D) ε := fun k hk y hy =>
    ⟨wK_tensFock hD hk (hLK k hk) hy.1, wK_physSub hD hk hy.2⟩
  have hpt : ∀ k : KG ε, ev (toMK k) P * physDet ε (toMK k) *
      LinearMap.trace ℂ (L.map D.subtype) (((σ (toMK k) : H →L[ℂ] H) : H →ₗ[ℂ] H).restrict (hAL k)) =
      ev (toMK k) P * LinearMap.trace ℂ ↥(tensFock (n := n) L ⊓ physicalSubspace (N := D) ε)
        ((gradT ∘ₗ wK hD (hφK k)).restrict (fun y hy => hY0G _ (hY0K _ (hφK k) y hy))) := by
    intro k
    rw [trace_map_subtype (sigD hD (hφK k)) (fun x hx => hLK _ (hφK k) x hx) _ _ (fun x => rfl)]
    have := str_tensFock_physSub hD (hφK k) (fun x hx => hLK _ (hφK k) x hx)
      (fun y hy => hY0G _ (hY0K _ (hφK k) y hy))
    rw [show LinearMap.trace ℂ ↥(tensFock (n := n) L ⊓ physicalSubspace (N := D) ε)
        ((gradT ∘ₗ wK hD (hφK k)).restrict (fun y hy => hY0G _ (hY0K _ (hφK k) y hy))) = _ from this]
    ring
  simp_rw [hpt]
  have hcP := hent P
  have hrange := fun y => btot_range (μ := muK ε) hσ hD hK (L := L) hφc hφK hcP
    (fun s s' u => by
      have h1 := hLd (P * Qm s s') (hdeg2 s s') u
      have h2 : ∫ k : KG ε, (ev (toMK k) P * ffMat ε (toMK k) s s') • σ (toMK k) u ∂(muK ε) =
          ∫ k : KG ε, ev (toMK k) (P * Qm s s') • σ (toMK k) u ∂(muK ε) := by
        congr 1
        funext k
        rw [map_mul, hQm]
        rfl
      rw [h2]
      exact h1) hYP y
  exact (int_str_eq (μ := muK ε) hσ hD hY0Y hK hY0K hG hY0G hφc hφK hcP hrange).symm

end GlobalTheory.PsCo.PcEF

end
end
end
