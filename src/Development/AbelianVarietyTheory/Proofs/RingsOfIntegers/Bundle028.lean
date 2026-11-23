module

public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle021
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle015
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle011
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.GmCharPow
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SquareRes
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.BoxSymIsSymmetry
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GtCoordCompatOfPull
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle024
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle022
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PulledComparisonEven
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle008
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationMultiplicationInvariance
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle026
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle004
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle027
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.Divisibility.WeightAlgebra
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Mathlib.NumberTheory.NumberField.CMField
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.PowUnif

local instance (priority := high) grpObjPullback {S T : Scheme.{0}} (f : T ⟶ S)
    (H : Over S) [GrpObj H] : GrpObj ((Over.pullback f).obj H) :=
  Functor.grpObjObj (F := Over.pullback f)

section Level

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.BoxFamily GlobalTheory.UnifPullRig GlobalTheory.WCub

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {j : ℕ} {D D' : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G G' : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']

omit [IsDomain R] [IsCommMonObj G] [IsCommMonObj G'] in
theorem rho_fst (pG : IsPowGrp G' G j) (e : ℕ) (i : Fin j) :
    rhoE I pG e i ≫ fGl I G e = fGl I G' e ≫ (pG.pr i).left := pullback.lift_fst _ _ _

omit [IsCommMonObj G] [IsCommMonObj G'] in
theorem thickMap_rho (pG : IsPowGrp G' G j) (e : ℕ) (i : Fin j) :
    thickMap R I e G' ≫ rhoE I pG (e + 1) i = rhoE I pG e i ≫ thickMap R I e G := by
  have : Mono (fGl I G (e + 1)) := mono_fstG I (e + 1) G
  have a : thickMap R I e G ≫ fGl I G (e + 1) = fGl I G e := thickMap_fstG I e G
  have a' : thickMap R I e G' ≫ fGl I G' (e + 1) = fGl I G' e := thickMap_fstG I e G'
  rw [← cancel_mono (fGl I G (e + 1)), Category.assoc, Category.assoc, rho_fst, a, rho_fst, ← Category.assoc, a']

theorem thickMap_pG (pD : IsPowDeg D'.toPre D.toPre j) (pG : IsPowGrp G' G j) (U : UnifPre I D A G) (e : ℕ)
    (g₀ : GtCoord I D'.toPre e G') (g₁ : GtCoord I D'.toPre (e + 1) G')
    (h₀ : ∀ i, g₀.pG.left ≫ (pD.pw.pr i).left = rhoE I pG e i ≫ (U.gt e).pG.left)
    (h₁ : ∀ i, g₁.pG.left ≫ (pD.pw.pr i).left = rhoE I pG (e + 1) i ≫ (U.gt (e + 1)).pG.left) :
    thickMap R I e G' ≫ g₁.pG.left = g₀.pG.left := by
  have h : LevelCompat.thickMapOver I e G' ≫ g₁.pG = g₀.pG := pD.pw.lim.hom_ext fun ⟨i⟩ =>
    Over.OverMorphism.ext ((Category.assoc _ _ _).trans ((congrArg (thickMap R I e G' ≫ ·) (h₁ i)).trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (U.gt (e + 1)).pG.left) (thickMap_rho pG e i)).trans
        ((Category.assoc _ _ _).trans ((congrArg (rhoE I pG e i ≫ ·) (U.gt_q e)).trans (h₀ i).symm))))))
  exact congrArg (fun z => z.left) h

variable (pD : IsPowDeg D'.toPre D.toPre j) (pG : IsPowGrp G' G j) (U : UnifPre I D A G)
    (e : ℕ) (g' : GtCoord I D'.toPre e G')
    (hq : ∀ i, g'.pG.left ≫ (pD.pw.pr i).left = rhoE I pG e i ≫ (U.gt e).pG.left)
    (w' : LB.Iso ((boxLB U.LG.L pG.pr).pull (fstG I e G').left) (D'.toPre.P.L.pull g'.pG.left))
    (Q : BoxSquare (T := (thickObj R I e G).left) (T' := (thickObj R I e G').left) pD.w (U.w e) w' (rhoE I pG e))
include hq Q

theorem rig_level : RigAlong (T := (thickObj R I e G').left) w' (eSec (thickObj R I e G')) (thick R I e)
    (boxRig pG U.LG.L U.LG.rig) D'.toPre.rig := by
  obtain ⟨b, b₁, b₂⟩ := pD.w_rig
  exact rig_box (T := (thickObj R I e G).left) (T' := (thickObj R I e G').left) D.toPre.P.isLB D'.toPre.P.isLB
    U.LG.isLB (U.w_gen e) Q (rho_fst pG e) hq U.LG.rigGen (U.w_rig e)
    (fun i => by
      have := pG.hom i
      exact BoxSymmetry.eSec_comp_hom ((Over.pullback (thick R I e)).map (pG.pr i)))
    (eSec_fstG I e G) (eSec_pG I (U.gt e)) (eSec_pG I g')
    (fun i _ => letI := pG.hom i; (CubeMap.ofHom (pG.pr i)).e_comm) b b₁ b₂

theorem even_level (hG : GlobalFnsSt) : EvenAlong (T := (thickObj R I e G').left) w' (ι[thickObj R I e G']).left
    (boxSym pG U.LG.L U.symG) D'.toPre.sym := by
  have := g'.q_hom
  have := (U.gt e).q_hom
  exact even_box (T := (thickObj R I e G).left) (T' := (thickObj R I e G').left) D.toPre.P.isLB D'.toPre.P.isLB
    U.LG.isLB (U.w_gen e) Q (rho_fst pG e) hq
    (fun i => by
      have := pG.hom i
      exact EvenPull.inv_left_comp ((Over.pullback (thick R I e)).map (pG.pr i)))
    (EvenPull.inv_fst _ G) (EvenPull.inv_hom_fst _ _ (U.gt e).q) (EvenPull.inv_hom_fst _ _ g'.q) (inv_pr pG)
    U.symG U.symG_gen D.toPre.sym D'.toPre.sym
    (fun y J J' hJ hJ' => PsiEvenBox.sym_box hG pD g'.pG.left y hJ hJ') (U.w_even e)

end Level


open GlobalTheory.WCub in

theorem main : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (j : ℕ) (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G G' : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] (pD : IsPowDeg D'.toPre D.toPre j) (pA : IsPowPolAV A' A j) (pG : IsPowGrp G' G j) (U : UnifPre I D A G), ∃ (U' : UnifPre I D' A' G') (wL : LB.Iso U'.LG.L (boxLB U.LG.L pG.pr)), (∀ i, U'.gen.hom ≫ pA.pr i = (Over.pullback (jK R)).map (pG.pr i) ≫ U.gen.hom) ∧ wL.IsGen ∧ (∃ b : LB.Gen (LB.LinComb U.LG.L (K := Fin j) (fun i => eSec G' ≫ (pG.pr i).left) (fun _ => 1)), GeneratorPullback.MapsAt U.LG.L U'.LG.L (fun i => (pG.pr i).left) wL (eSec G') 1 U'.LG.rig b ∧ LB.Gen.Corr U.LG.L _ _ _ _ b (GeneratorPullback.finProdGen U.LG.L (J := Fin j) (fun _ _ => eSec G) (fun _ _ => 1) (fun _ => U.LG.rig))) ∧ (∀ (e : ℕ) (i : Fin j), (U'.gt e).q ≫ (Over.pullback (thick R I e)).map (pD.pw.pr i) = (Over.pullback (thick R I e)).map (pG.pr i) ≫ (U.gt e).q) ∧ (∀ (e : ℕ) (x : D'.toPre.X), ∃ hψ : ∀ (i : Fin j) (k : Fin 4), D'.toPre.Oφ ((Over.map (thick R I e)).map (U'.gt e).q ≫ D'.toPre.prBe I e) x k ≫ (pD.pw.pr i).left = ((Over.pullback (thick R I e)).map (pG.pr i)).left ≫ D.toPre.Oφ ((Over.map (thick R I e)).map (U.gt e).q ≫ D.toPre.prBe I e) (pD.xe x i) k, LB.Gen.Maps (LB.linCombIso pD.w _ Oinvε) ((U'.gt e).t x) (GeneratorPullback.boxGen D.toPre.P.L (fun i => (pD.pw.pr i).left) _ Oinvε (fun i => GeneratorPullback.pullAlong D.toPre.P.L (pD.pw.pr i).left ((Over.pullback (thick R I e)).map (pG.pr i)).left _ Oinvε _ (hψ i) ((U.gt e).t (pD.xe x i))))) ∧ (∀ (e : ℕ) (jNM : Fin j → D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL' : U'.LG.L.ι) (jNL : Fin j → U.LG.L.ι), res (X := (thickObj R I e G').left) (inf_le_left.trans (inf_le_left.trans inf_le_left) : (U'.gt e).pG.left ⁻¹ᵁ (LB.div (boxLB D.toPre.P.L pD.pw.pr) D'.toPre.P.L).U (jNM, jM') ⊓ (LB.div (D'.toPre.P.L.pull (U'.gt e).pG.left) (U'.LG.L.pull (fstG I e G').left)).U (fun _ => jM', fun _ => jL') ⊓ (⨅ i, ((Over.pullback (thick R I e)).map (pG.pr i)).left ⁻¹ᵁ (LB.div (D.toPre.P.L.pull (U.gt e).pG.left) (U.LG.L.pull (fstG I e G).left)).U (fun _ => jNM i, fun _ => jNL i)) ⊓ (fstG I e G').left ⁻¹ᵁ (LB.div (boxLB U.LG.L pG.pr) U'.LG.L).U (jNL, jL') ≤ (U'.gt e).pG.left ⁻¹ᵁ (LB.div (boxLB D.toPre.P.L pD.pw.pr) D'.toPre.P.L).U (jNM, jM')) (pullU (U'.gt e).pG.left _ (pD.w.s (jNM, jM'))) * res (X := (thickObj R I e G').left) (inf_le_left.trans (inf_le_left.trans inf_le_right)) ((U'.w e).s (fun _ => jM', fun _ => jL')) = (∏ i, res (X := (thickObj R I e G').left) (inf_le_left.trans (inf_le_right.trans (iInf_le _ i))) (pullU ((Over.pullback (thick R I e)).map (pG.pr i)).left _ ((U.w e).s (fun _ => jNM i, fun _ => jNL i)))) * res (X := (thickObj R I e G').left) inf_le_right (pullU (Y := (thickObj R I e G').left) (fstG I e G').left _ (wL.s (jNL, jL')))) := by
  intro hG R _ _ I j D D' A A' G G' _ _ _ _ pD pA pG U
  obtain ⟨gen, gen_hom, gen_pr, ext⟩ := exists_gen_pow R I j D D' A A' G G' pD pA pG U
  choose gt q_pr t_pr using fun e => GlobalTheory.PowTorusCoord.main hG R I j D D' A A' G G' pD pA pG e (U.gt e)
  have hq : ∀ e i, (gt e).pG.left ≫ (pD.pw.pr i).left = rhoE I pG e i ≫ (U.gt e).pG.left :=
    fun e i => (t_pr e 0).choose i 2
  choose w w_gen Q using fun e => PowerThickIso.main R I j D D' A A' G G' pD pA pG e (U.gt e) (gt e) (hq e)
    U.LG.L U.LG.isLB (U.w e) (U.w_gen e)
  have hL := boxIsLB _ G' G j pG U.LG.L U.LG.isLB
  have hr := boxRigIsGen _ G' G j pG U.LG.L U.LG.rig U.LG.isLB U.LG.rigGen
  obtain ⟨c, hc⟩ := boxCubical _ G' G j pG U.LG U.cubG hL hr
  obtain ⟨s₁, s₂⟩ := boxSym_isSymmetry _ G' G j pG U.LG.L U.symG U.LG.isLB U.symG_gen U.symG_rig
  have gq := fun e => thickMap_pG pD pG U e (gt e) (gt (e + 1)) (hq e) (hq (e + 1))
  refine ⟨{
      smooth := (PowGrp.powers _ G' G j pG).1 U.smooth
      separated := (PowGrp.powers _ G' G j pG).2.1 U.separated
      gen := gen
      gen_hom := gen_hom
      LG := ⟨boxLB U.LG.L pG.pr, boxRig pG U.LG.L U.LG.rig, hL, hr⟩
      cubG := c
      symG := boxSym pG U.LG.L U.symG
      symG_gen := s₁
      symG_rig := s₂
      ext := ext
      gt := gt
      gt_q := gq
      gt_t := fun e χ => corr_box (T := (thickObj R I e G).left) (T' := (thickObj R I e G').left)
        (T₁ := (thickObj R I (e + 1) G).left) (T₁' := (thickObj R I (e + 1) G').left)
        D.toPre.P.isLB D'.toPre.P.isLB pD.w (thickMap_rho pG e) (t_pr e χ).choose
        (t_pr (e + 1) χ).choose (LevelCompat.thickMap_Oφ (gt e) (gt (e + 1)) (gq e) χ) (t_pr e χ).choose_spec
        (t_pr (e + 1) χ).choose_spec (fun i => U.gt_t e _)
      w := w
      w_gen := w_gen
      w_rig := fun e => rig_level pD pG U e (gt e) (hq e) (w e) (Q e)
      w_even := fun e => even_level pD pG U e (gt e) (hq e) (w e) (Q e) hG
      w_cub := fun e T x jL jM _ cM => (clause_iff (tri (thick R I e) (gt e).pG x) (tri (thick R I e) (fstG I e G') x)
        (fun k : thK => (psum (thickObj R I e G') x k.down).left) _ _ _ (D'.toPre.cub.t.s jM) (c.t.s jL)
        (fun k => (w e).s (fun _ => jM k, fun _ => jL k)) thε).2 fun y hB hL _ => by
          rw [hc]
          exact cub_box hG pD pG U e (gt e) (hq e) (w e) (Q e) T x jL jM cM y hB hL
      w_compat := fun e => compat_box (T := (thickObj R I e G).left) (T' := (thickObj R I e G').left)
        (T₁ := (thickObj R I (e + 1) G).left) (T₁' := (thickObj R I (e + 1) G').left)
        D.toPre.P.isLB (Q e) (Q (e + 1)) (U.w_compat e) (UnifPullRig.thickMap_fstG I e G) (U.gt_q e)
        (UnifPullRig.thickMap_fstG I e G') (gq e) (rho_fst pG e) (hq e) (thickMap_rho pG e) },
    Geo.Tor.idIso _, gen_pr, Geo.Tor.idIso_isGen hL, ?_, q_pr, t_pr, fun e jNM jM' jL' jNL => ?_⟩
  · exact idIso_rig U.LG.isLB U.LG.rig (fun i _ => letI := pG.hom i; (CubeMap.ofHom (pG.pr i)).e_comm) hr
  · exact square_res (T := (thickObj R I e G).left) (T' := (thickObj R I e G').left) D'.toPre.P.isLB (w_gen e) (Q e)
      jNM jM' jL' jNL _ _ _ _ _

end GlobalTheory.PowUnif
end
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ThetaValueIdentityCompare

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections

attribute [local instance] Over.cartesianMonoidalCategory

section Valuations

open IsLocalRing Polynomial

variable {V K : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K]
  [IsFractionRing V K]

theorem vV_zpow (x : K) (n : ℤ) : vV V (x ^ n) = n * vV V x := by
  simp only [vV, map_zpow₀, WithZero.log_zpow, smul_eq_mul]
  ring

theorem exists_unit {x : K} (hx : x ≠ 0) (h : vV V x = 0) : ∃ u : V, IsUnit u ∧ algebraMap V K u = x := by
  have h1 : valV V x = 1 := by
    have h2 : WithZero.log (valV V x) = 0 := by simp only [vV] at h; omega
    rw [← WithZero.exp_log (valV_ne_zero (V := V) hx), h2, WithZero.exp_zero]
  obtain ⟨u, rfl⟩ := IsDiscreteValuationRing.exists_lift_of_le_one (A := V) (K := K) (x := x) h1.le
  refine ⟨u, ?_, rfl⟩
  by_contra hu
  exact ((HeightOneSpectrum.valuation_lt_one_iff_mem (K := K) (IsDiscreteValuationRing.maximalIdeal V) u).2 hu).ne h1

variable {W L : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field L] [Algebra W L]
  [IsFractionRing W L]

end Valuations

section Clauses

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

variable [StarRing (𝓞 E)]

end Clauses

end GlobalTheory.ThetaValueIdentityCompare
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj
theorem _root_.GlobalTheory.T.mixed_cross_identity_genericFibre : Laws → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (H : Geo.Tor.Host E) (t : Geo.Tor.SAB H (Spec (CommRingCat.of V))) (P : Geo.Tor.PELUnif (maximalIdeal V) t) (a : NumberField.RingOfIntegers E) (N : ℕ), (letI := H.starRing; a * star a = (N : NumberField.RingOfIntegers E)) → 0 < N → letI := H.starRing;  ∀ (k₁ : ℕ) (s₁ : P.U.SecK k₁) (F₁ : Fam P.D.toPre (FractionRing V) k₁) (u₁ : P.U.SecK (k₁ * N)) (F₁' : Fam P.D.toPre (FractionRing V) (k₁ * N)), P.U.Expands k₁ s₁ F₁ → P.U.Expands (k₁ * N) u₁ F₁' → PullAl P.D (FractionRing V) P.oD a k₁ N F₁ F₁' → ∀ (k₂ : ℕ) (s₂ : P.U.SecK k₂) (F₂ : Fam P.D.toPre (FractionRing V) k₂) (u₂ : P.U.SecK (k₂ * N)) (F₂' : Fam P.D.toPre (FractionRing V) (k₂ * N)), P.U.Expands k₂ s₂ F₂ → P.U.Expands (k₂ * N) u₂ F₂' → PullAl P.D (FractionRing V) P.oD a k₂ N F₂ F₂' → ∀ m₁ m₂ : ℕ, m₁ * k₁ = m₂ * k₂ → ∀ (y : (pullback t.G.hom (jK V) : Scheme.{0})) (J), Geo.Tor.Good P.U.LG.L y J → Geo.Tor.sval u₁ (𝟙 _) y J ^ m₁ * Geo.Tor.sval s₂ (endK (t.act.act a)) y J ^ m₂ = Geo.Tor.sval u₂ (𝟙 _) y J ^ m₂ * Geo.Tor.sval s₁ (endK (t.act.act a)) y J ^ m₁ := by
  first | exact @GlobalTheory.GenericCross.main | exact GlobalTheory.GenericCross.main | (intros; apply GlobalTheory.GenericCross.main <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj
theorem _root_.GlobalTheory.T.expansion_integralSection_integral_noetherianLocal : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R), I ≤ maximalIdeal R → ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (k : ℕ) (σ : H0 U.LG.L k) (s : U.SecK k), GeneratorPullback.SecScal U.LG.L (fun _ : Fin 1 => pullback.fst G.hom (jK R)) (fun _ => ((k : ℕ) : ℤ)) s (fun _ : Fin 1 => 𝟙 G.left) (fun _ => ((k : ℕ) : ℤ)) σ (pullback.fst G.hom (jK R)) 1 → ∀ E : Fam D.toPre (FractionRing R) k, U.Expands k s E → ∃ g : ∀ α : D.toPre.X, D.toPre.SecB k α, (∀ e, U.ExpandsAt e k σ g) ∧ ∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) α) (DegPre.famε k) (E.s α) (D.toPre.famφB α) (DegPre.famε k) (g α) (DegPre.prB D.toPre (FractionRing R)).left 1 := by
  first | exact @GlobalTheory.IntegralExpansionLocal.main | exact GlobalTheory.IntegralExpansionLocal.main | (intros; apply GlobalTheory.IntegralExpansionLocal.main <;> assumption)
end
