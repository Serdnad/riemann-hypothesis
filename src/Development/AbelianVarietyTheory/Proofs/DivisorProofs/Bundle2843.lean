module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle633
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle644
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1535
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2748
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle011
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle053
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2747
public import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.PolarizationDescentAlongQuasiIsogenyCompat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle714
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Development.AbelianVarietyTheory.Counterexamples.UniformisationSurvey.NeTopOfAdmissibleBase
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle032
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle040
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle014
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle017
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RosatiAdjointAbelianPartAndClassifyingMapLinear
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1120
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle674
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle025
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle839
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle082
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle037
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianPartValuesTorsionPairingSeparationIntegra
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DegenerationDataTorsionStructureAlgClosed
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle126
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle019
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
namespace GlobalTheory.Mum

theorem actsAs_unique : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G) (b : D.toPre.P.A ⟶ D.toPre.P.A) (h : D.toPre.X → D.toPre.X) (g g' : G ⟶ G), IsMonHom g → IsMonHom g' → ActsAs U.toUnifPre b h g → ActsAs U.toUnifPre b h g' → g = g' := by
  intro R _ _ _ hR D A G _ _ hG U b h g g' hg hg' H H'
  have : IsNoetherianRing R := hR.1.1
  have : Smooth G.hom := hG.smooth
  have : GeometricallyConnected G.hom := hG.geomConnected
  have : IsSeparated G.hom := hG.separated
  refine GlobalTheory.AbelianPartIso.hom_eq_of_map_eq (IsLocalRing.maximalIdeal_le_jacobson _) G g g' fun e => ?_
  obtain ⟨q1, t, ht, i1⟩ := H e
  obtain ⟨q2, t', ht', i2⟩ := H' e
  have htt : t = t' := GlobalTheory.LinearUnifCheck.torusEndOf_unique ht ht'
  have := (U.gt e).i_hom
  exact GlobalTheory.LinearUnifIso.hom_ext_torus (U.gt e) (U.gt e) GlobalTheory.globalFns_holds _ _
    (q1.trans q2.symm) (i1.trans (htt ▸ i2.symm))

end GlobalTheory.Mum
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.RosGeneric

theorem linEnd_of_actsAs {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
    (U : UnifPre I D A G) {b : D.toPre.P.A ⟶ D.toPre.P.A} {h : D.toPre.X →+ D.toPre.X} {g : G ⟶ G} [IsMonHom g]
    (hg : ActsAs U b h g) : LinEnd U b h g :=
  ⟨inferInstance, fun _ => inferInstance, fun e => GlobalTheory.Mum.EndModel.thickMap_map g e, fun e => (hg e).1,
    fun e => (hg e).2⟩

theorem rosatiAdj_generic_of_cube (hcube : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ g g' : G ⟶ G, LinEnd U.toUnifPre a h' g → LinEnd U.toUnifPre a' h g' → LBIso (cubeLB G ![fst G G ≫ g, snd G G] U.LG.L) (cubeLB G ![fst G G, snd G G ≫ g'] U.LG.L)) : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G) (O : Type) [Ring O] [StarRing O] [Module O D.toPre.X] (o : D.toPre.OAct O) (a : O) (g g' : G ⟶ G), IsMonHom g → IsMonHom g' → ActsAs U.toUnifPre (o.onB.act a) (fun χ => star a • χ) g → ActsAs U.toUnifPre (o.onB.act (star a)) (fun χ => star (star a) • χ) g' → RosatiAdj A.A A.L (U.gen.inv ≫ (Over.pullback (jK R)).map g ≫ U.gen.hom) (U.gen.inv ≫ (Over.pullback (jK R)).map g' ≫ U.gen.hom) := by
  intro R _ _ _ hR D A G _ _ hG U O _ _ _ o a g g' hg hg' ag ag'
  have hE := GlobalTheory.Mum.EndModel.endData_of_oAct O D.toPre o a
  have l1 : LinEnd U.toUnifPre (o.onB.act a) (DistribSMul.toAddMonoidHom D.toPre.X (star a)) g :=
    linEnd_of_actsAs U.toUnifPre ag
  have l2 : LinEnd U.toUnifPre (o.onB.act (star a)) (DistribSMul.toAddMonoidHom D.toPre.X a) g' := by
    have := linEnd_of_actsAs (h := DistribSMul.toAddMonoidHom D.toPre.X (star (star a))) U.toUnifPre ag'
    simpa only [star_star] using this
  have H := hcube R hR D A G hG U _ _ _ _ hE g g' l1 l2
  obtain ⟨u, hu⟩ := (GlobalTheory.NormRos.normRos_of_lbIso _ G U.LG.L U.LG.isLB g g' H).1
  have := U.gen_hom
  exact GlobalTheory.EndRosati.rosatiAdj_generic U.toUnifPre (by simp) (by simp) u hu.1

end GlobalTheory.Mum.RosGeneric
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.GalUniq

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']

theorem abPart_eq {ρ : R →+* R'} {s : R' →+* R'} {D : DegPre R} {D' : DegPre R'}
    (hD : IsPullDeg ρ D D') (h h' : IsPullDeg s D' D') (H : PullOver hD h) (H' : PullOver hD h') :
    h.e.hom.left ≫ pullback.fst D'.P.A.hom (specOf s) =
      h'.e.hom.left ≫ pullback.fst D'.P.A.hom (specOf s) := by
  have hcb := H.2 _ _ rfl rfl
  have hcb' := H'.2 _ _ rfl rfl
  have hov : ∀ k : IsPullDeg s D' D', (k.e.hom.left ≫ pullback.fst D'.P.A.hom (specOf s)) ≫ D'.P.A.hom =
      D'.P.A.hom ≫ specOf s := by
    intro k
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    congr 1
    exact Over.w k.e.hom
  have : IsIso hD.e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map hD.e.hom))
  rw [← cancel_mono hD.e.hom.left]
  refine pullback.hom_ext ?_ ?_
  · simp only [Category.assoc]
    simp only [Category.assoc] at hcb hcb'
    rw [hcb, hcb']
  · simp only [Category.assoc]
    have w0 : hD.e.hom.left ≫ pullback.snd D.P.A.hom (specOf ρ) = D'.P.A.hom := Over.w hD.e.hom
    rw [w0, ← Category.assoc, hov h, ← Category.assoc, hov h']

theorem iso_eq_of_rig {s : R' →+* R'} {D' : DegPre R'} (F : D'.P.A.left ⟶ D'.P.A.left)
    (he : eSec D'.P.A ≫ F = specOf s ≫ eSec D'.P.A)
    (w w' : LB.Iso D'.P.L (D'.P.L.pull F)) (hw : w.IsGen) (hw' : w'.IsGen)
    (hr : LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec D'.P.A) (fun _ => 1)) D'.rig
      (rigPullOf F (specOf s) he D'.P.L D'.rig))
    (hr' : LB.Gen.Maps (LB.linCombIso w' (K := PUnit) (fun _ => eSec D'.P.A) (fun _ => 1)) D'.rig
      (rigPullOf F (specOf s) he D'.P.L D'.rig)) : w = w' :=
  iso_unique_of_rig GlobalTheory.globalFns_holds D'.P.A D'.P.isAb D'.P.isLB D'.P.isLB hw hw' hr hr'

theorem level_eq {I' : Ideal R'} {D' : DegPre R'} {e : ℕ} {G' : Over (Sp R')} [GrpObj G']
    [IsCommMonObj G'] (g : GtCoord I' D' e G') (F : D'.P.A.left ⟶ D'.P.A.left)
    (w : LB.Iso D'.P.L (D'.P.L.pull F)) (hw : w.IsGen)
    (f f' : (thickObj R' I' e G').left ⟶ (thickObj R' I' e G').left)
    (hb : f ≫ pullback.snd G'.hom (thick R' I' e) = f' ≫ pullback.snd G'.hom (thick R' I' e))
    (hp : g.pG.left ≫ F = f ≫ g.pG.left) (hp' : g.pG.left ≫ F = f' ≫ g.pG.left)
    (ht : ∀ x : D'.X, ∃ hψ : ∀ k : Fin 4, D'.Oφ g.pG x k ≫ F = f ≫ D'.Oφ g.pG x k,
      LB.Gen.Maps (LB.linCombIso w _ Oinvε) (g.t x)
        (GeneratorPullback.pullAlong D'.P.L F f _ Oinvε _ hψ (g.t x)))
    (ht' : ∀ x : D'.X, ∃ hψ : ∀ k : Fin 4, D'.Oφ g.pG x k ≫ F = f' ≫ D'.Oφ g.pG x k,
      LB.Gen.Maps (LB.linCombIso w _ Oinvε) (g.t x)
        (GeneratorPullback.pullAlong D'.P.L F f' _ Oinvε _ hψ (g.t x))) : f = f' := by
  exact GlobalTheory.T.thickenedUniformisedGroup_point_ext g f f' hb (hp.symm.trans hp') fun z J hJ χ => by
    obtain ⟨hψ, hm⟩ := ht χ
    obtain ⟨hψ', hm'⟩ := ht' χ
    exact GlobalTheory.T.torusCoordinate_value_eq_of_maps g F w f f' χ hψ hψ' hm hm' z J hJ

end GlobalTheory.Mum.GalUniq

namespace GlobalTheory.Mum.GalUniq

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']

theorem level_eq_two {s : R' →+* R'} {I' : Ideal R'} {D' : DegPre R'} {e : ℕ} {G' : Over (Sp R')} [GrpObj G']
    [IsCommMonObj G'] (g : GtCoord I' D' e G') (F F' : D'.P.A.left ⟶ D'.P.A.left) (hF : F = F')
    (he : eSec D'.P.A ≫ F = specOf s ≫ eSec D'.P.A) (he' : eSec D'.P.A ≫ F' = specOf s ≫ eSec D'.P.A)
    (w : LB.Iso D'.P.L (D'.P.L.pull F)) (hw : w.IsGen)
    (w' : LB.Iso D'.P.L (D'.P.L.pull F')) (hw' : w'.IsGen)
    (hr : LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec D'.P.A) (fun _ => 1)) D'.rig
      (rigPullOf F (specOf s) he D'.P.L D'.rig))
    (hr' : LB.Gen.Maps (LB.linCombIso w' (K := PUnit) (fun _ => eSec D'.P.A) (fun _ => 1)) D'.rig
      (rigPullOf F' (specOf s) he' D'.P.L D'.rig))
    (xe xe' : D'.X → D'.X) (hxe : xe = id) (hxe' : xe' = id)
    (f f' : (thickObj R' I' e G').left ⟶ (thickObj R' I' e G').left)
    (hb : f ≫ pullback.snd G'.hom (thick R' I' e) = f' ≫ pullback.snd G'.hom (thick R' I' e))
    (hp : g.pG.left ≫ F = f ≫ g.pG.left) (hp' : g.pG.left ≫ F' = f' ≫ g.pG.left)
    (ht : ∀ x : D'.X, ∃ hψ : ∀ k : Fin 4, D'.Oφ g.pG x k ≫ F = f ≫ D'.Oφ g.pG (xe x) k,
      LB.Gen.Maps (LB.linCombIso w _ Oinvε) (g.t x)
        (GeneratorPullback.pullAlong D'.P.L F f _ Oinvε _ hψ (g.t (xe x))))
    (ht' : ∀ x : D'.X, ∃ hψ : ∀ k : Fin 4, D'.Oφ g.pG x k ≫ F' = f' ≫ D'.Oφ g.pG (xe' x) k,
      LB.Gen.Maps (LB.linCombIso w' _ Oinvε) (g.t x)
        (GeneratorPullback.pullAlong D'.P.L F' f' _ Oinvε _ hψ (g.t (xe' x)))) : f = f' := by
  subst hF hxe hxe'
  obtain rfl := iso_eq_of_rig F he w w' hw hw' hr hr'
  exact level_eq g F w hw f f' hb hp hp' ht ht'

end GlobalTheory.Mum.GalUniq


open GlobalTheory.Mum.GalUniq in
theorem GlobalTheory.Mum.galMap_unique : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G') (σ : Gal ρ) (a a' : G'.left ⟶ G'.left), GalMap hD U' σ a → GalMap hD U' σ a' → a = a' := by
  intro R _ _ _ _ R' _ _ _ ρ hρ D D' hD A' G' _ _ hG U' σ a a' ha ha'
  obtain ⟨-, h, bc, rfl, P, PO⟩ := ha
  obtain ⟨-, h', bc', rfl, P', PO'⟩ := ha'
  have hc := abPart_eq hD h h' PO PO'
  have hxe : (⇑h.xe : D'.toPre.X → D'.toPre.X) = id := funext PO.1
  have hxe' : (⇑h'.xe : D'.toPre.X → D'.toPre.X) = id := funext PO'.1
  have hov : ∀ (b : G' ≅ (Over.pullback (specOf (Gal.hom σ))).obj G'),
      b.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ)) ≫ G'.hom = G'.hom ≫ specOf (Gal.hom σ) := by
    intro b
    rw [pullback.condition, ← Category.assoc]
    congr 1
    exact Over.w b.hom
  have lev : ∀ n : ℕ, (fstG (maximalIdeal R') n G').left ≫ bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ)) =
      (fstG (maximalIdeal R') n G').left ≫ bc'.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ)) := by
    intro n
    obtain ⟨wL, -, he1, -, hl⟩ := P.lg
    obtain ⟨wL', -, he1', -, hl'⟩ := P'.lg
    obtain ⟨f, hf, hpG, hT, -⟩ := hl n
    obtain ⟨f', hf', hpG', hT', -⟩ := hl' n
    have hb : f ≫ pullback.snd G'.hom (thick R' (maximalIdeal R') n) =
        f' ≫ pullback.snd G'.hom (thick R' (maximalIdeal R') n) := by
      have : IsClosedImmersion (thick R' (maximalIdeal R') n) :=
        IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
      rw [← cancel_mono (thick R' (maximalIdeal R') n), Category.assoc, Category.assoc,
        ← pullback.condition]
      have e1 : f ≫ (fstG (maximalIdeal R') n G').left ≫ G'.hom =
          (fstG (maximalIdeal R') n G').left ≫ G'.hom ≫ specOf (Gal.hom σ) := by
        rw [← Category.assoc, hf]; simp only [Category.assoc]; rw [hov bc]
      have e2 : f' ≫ (fstG (maximalIdeal R') n G').left ≫ G'.hom =
          (fstG (maximalIdeal R') n G').left ≫ G'.hom ≫ specOf (Gal.hom σ) := by
        rw [← Category.assoc, hf']; simp only [Category.assoc]; rw [hov bc']
      exact e1.trans e2.symm
    have := level_eq_two (U'.gt n) _ _ hc h.he h'.he h.w h.w_gen h'.w h'.w_gen h.w_rig h'.w_rig _ _ hxe hxe' f f' hb hpG hpG' hT hT'
    rw [← hf, ← hf', this]
  have hI : maximalIdeal R' ≤ Ideal.jacobson ⊥ := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
  have : IsNoetherianRing R' := hρ.1.1
  have : Smooth G'.hom := hG.smooth
  have : GeometricallyConnected G'.hom := hG.geomConnected
  have : IsSeparated G'.hom := hG.separated
  have : IsIso (CommRingCat.ofHom (Gal.hom σ)) := σ.1.toCommRingCatIso.isIso_hom
  have : IsIso (specOf (Gal.hom σ)) := inferInstanceAs (IsIso (Spec.map _))
  let Y : Over (Sp R') := Over.mk (G'.hom ≫ inv (specOf (Gal.hom σ)))
  have : IsSeparated Y.hom := inferInstanceAs (IsSeparated (G'.hom ≫ inv (specOf (Gal.hom σ))))
  have hov2 : ∀ (b : G' ≅ (Over.pullback (specOf (Gal.hom σ))).obj G'),
      (b.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ))) ≫ Y.hom = G'.hom := by
    intro b
    change _ ≫ G'.hom ≫ inv (specOf (Gal.hom σ)) = _
    simp only [Category.assoc]
    rw [reassoc_of% (hov b), IsIso.hom_inv_id, Category.comp_id]
  have key := (sec_eq_zero_and_hom_eq_of_thickenings R' (maximalIdeal R') hI G').2 Y
    (Over.homMk (bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ))) (hov2 bc))
    (Over.homMk (bc'.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ))) (hov2 bc')) lev
  exact congrArg CommaMorphism.left key
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum


open GlobalTheory.TorsionFormCompare in
theorem galMap_one : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G'), GalMap hD U' 1 (𝟙 _) := by
  intro R _ _ _ _ R' _ _ _ ρ hρ D D' hD A' G' _ _ _ U'
  obtain ⟨W, hW, hψ⟩ := GlobalTheory.psiOnExists R' (maximalIdeal R') hρ.1 D'
  obtain ⟨h, hid⟩ := exists_isIdPull R' D'.toPre W hW hψ
  have gp : IsGrpPullback G' G' (specOf (RingHom.id R')) (𝟙 _) :=
    (@isGrpPullback_of_iso _ _ _ _ _ (Iso.refl G') (inferInstanceAs (IsMonHom (𝟙 G')))).congr (specOf_id R').symm rfl
  obtain ⟨bc, -, hbc⟩ := grpPullback_iso gp (isGrpPullback_pullback G' (specOf (RingHom.id R')))
  have hP : PullOver hD h := ⟨hid.1, fun b c _ hc => by rw [hc, hid.2.1, Category.id_comp]⟩
  exact ⟨gp, h, bc, hbc, isPullUnif_refl U' h hid bc hbc, hP⟩

end GlobalTheory.Mum
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace GlobalTheory.QuasiInvPull

theorem root_symm : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (c : ℕ) (Y : Scheme.{0}) (s : Y ⟶ Sp R) (o : Obj b N s) (B : Over Y) [GrpObj B] [IsCommMonObj B] (ψ : o.A ⟶ B) (ψ' : B ⟶ o.A), IsUnit ((p : ℕ) : R) → (∃ e : ℕ, c = p ^ e) → IsAbelianScheme B → IsQuasiInv c ψ ψ' → ∀ P' : LB (G2 B).left, IsAxesTriv B P' → LBIso (o.P.pull (Hecke.sq2 ψ')) (Hecke.lbPow P' c) → LBIso (Hecke.lbPow o.P c) (P'.pull (Hecke.sq2 ψ)) → LBIso P' (P'.pull (lift (snd B B) (fst B B)).left) := by
  intro p _ D R _ b N c Y s o B _ _ ψ ψ' hp hc hB hq P' hP' _ H
  obtain ⟨e, rfl⟩ := hc
  have hpos : 0 < p ^ e := pow_pos (Fact.out : p.Prime).pos e
  have hunit : IsUnit (((p ^ e : ℕ)) : Γ(Y, ⊤)) := by
    have := (hp.pow e).map (s.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
    rwa [← Nat.cast_pow, map_natCast] at this
  obtain ⟨hL, r₁, r₂⟩ := hP'
  set sw' := (lift (snd B B) (fst B B)).left with hsw'
  set sw := (lift (snd o.A o.A) (fst o.A o.A)).left with hsw
  set q := Hecke.sq2 ψ with hqdef
  have hQ : (P'.pull sw').IsLB := pull_isLB hL sw'
  have ax : ∀ (e₁ e₂ : B ⟶ G2 B), e₁ ≫ lift (snd B B) (fst B B) = e₂ →
      (∃ t : (P'.pull e₂.left).Gen, t.IsGen) → ∃ t : ((P'.pull sw').pull e₁.left).Gen, t.IsGen := by
    intro e₁ e₂ he ⟨t, ht⟩
    have hc : ∀ k : PUnit, (fun _ : PUnit => e₁.left) k ≫ sw' = 𝟙 _ ≫ (fun _ : PUnit => e₂.left) k := by
      intro _
      rw [Category.id_comp, hsw', ← Over.comp_left, he]
    have iso : LBIso ((P'.pull sw').pull e₁.left) (P'.pull e₂.left) :=
      LBIso.chartPull (chartPullLinComb P' sw' (fun _ => e₁.left) (fun _ => e₂.left) (fun _ => 1) (𝟙 _) hc)
        (chartPullId _) (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB hL _))
    exact GlobalTheory.RigidTranslate.gen_of_lbIso (pull_isLB hL _) (pull_isLB hQ _) iso.symm t ht
  have a₁ := ax (lift (1 : B ⟶ B) (𝟙 B)) (lift (𝟙 B) (1 : B ⟶ B)) (by ext <;> simp) r₂
  have a₂ := ax (lift (𝟙 B) (1 : B ⟶ B)) (lift (1 : B ⟶ B) (𝟙 B)) (by ext <;> simp) r₁
  have E := GlobalTheory.HeckeSym.grpSchemeSquareProductMap_comm_swap ψ
  have hPow : (Hecke.lbPow o.P (p ^ e)).IsLB := DVR.linComb_isLB _ o.isLB _ _
  have step1 : LBIso (Hecke.lbPow o.P (p ^ e))
      (LB.LinComb (o.P.pull sw) (K := Fin (p ^ e)) (fun _ => 𝟙 _) (fun _ => 1)) :=
    GlobalTheory.PowPrimitive.lbIso_linComb o.symm _ _
  have step2 : LBIso (LB.LinComb (o.P.pull sw) (K := Fin (p ^ e)) (fun _ => 𝟙 _) (fun _ => 1))
      ((P'.pull sw').pull q) := by
    refine LBIso.chartPull (h := sw)
      (chartPullLinComb o.P sw (fun _ => 𝟙 _) (fun _ => 𝟙 _) (fun _ => 1) sw (fun _ => by simp))
      (chartPullLinComb P' sw' (fun _ : PUnit => q) (fun _ : PUnit => q) (fun _ => 1) sw (fun _ => E)) H
  have hmid : (LB.LinComb (o.P.pull sw) (K := Fin (p ^ e)) (fun _ => 𝟙 _) (fun _ => 1)).IsLB :=
    DVR.linComb_isLB _ (pull_isLB o.isLB _) _ _
  have key : LBIso (P'.pull q) ((P'.pull sw').pull q) :=
    LBIso.trans (pull_isLB hL q) hPow (pull_isLB hQ q) H.symm
      (LBIso.trans hPow hmid (pull_isLB hQ q) step1 step2)
  exact lbIso_of_pullback_quasiInverseIsogeny_trivial_axes Y o.A B (p ^ e) ψ ψ' P' (P'.pull sw') hB hpos hunit hq ⟨hL, r₁, r₂⟩ ⟨hQ, a₁, a₂⟩ key

end GlobalTheory.QuasiInvPull
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES


theorem _root_.GlobalTheory.T.relAmple_diag_root_pullback_quasiInverse : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (c : ℕ) (Y : Scheme.{0}) [IsLocallyNoetherian Y] (s : Y ⟶ Sp R) (o : Obj b N s) (B : Over Y) [GrpObj B] [IsCommMonObj B] (ψ : o.A ⟶ B) (ψ' : B ⟶ o.A), IsUnit ((p : ℕ) : R) → (∃ e : ℕ, c = p ^ e) → IsAbelianScheme B → IsQuasiInv c ψ ψ' → ∀ P' : LB (G2 B).left, IsAxesTriv B P' → LBIso (o.P.pull (Hecke.sq2 ψ')) (Hecke.lbPow P' c) → LBIso (Hecke.lbPow o.P c) (P'.pull (Hecke.sq2 ψ)) → Out.RelAmple B (P'.pull (lift (𝟙 B) (𝟙 B)).left) := by
  first | (exact @GlobalTheory.UPel.HT.ES.relAmple_diag_root_pull) | (exact GlobalTheory.UPel.HT.ES.relAmple_diag_root_pull) | (intros; apply GlobalTheory.UPel.HT.ES.relAmple_diag_root_pull  <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

theorem _root_.GlobalTheory.T.polarization_descent_along_quasi_isogeny_compat : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (c : ℕ) (Y : Scheme.{0}) (s : Y ⟶ Sp R) (o : Obj b N s) (B : Over Y) [GrpObj B] [IsCommMonObj B] (ψ : o.A ⟶ B) (ψ' : B ⟶ o.A), IsUnit ((p : ℕ) : R) → (∃ e : ℕ, c = p ^ e) → IsAbelianScheme B → IsQuasiInv c ψ ψ' → PolKerAt o ψ' c (𝟙 Y) → ∀ P' : LB (G2 B).left, IsAxesTriv B P' → LBIso (o.P.pull (Hecke.sq2 ψ')) (Hecke.lbPow P' c) → LBIso (Hecke.lbPow o.P c) (P'.pull (Hecke.sq2 ψ)) → ∃ e : ℕ, e.Coprime p ∧ ∀ (T : Over Y) (x : T ⟶ B), (∃ t : (P'.pull (lift (snd B T ≫ x) (fst B T)).left).Gen, t.IsGen) → x ^ e = 1 := by
  first | exact @UpperTheory.Cb.polarization_descent_along_quasi_isogeny_compat | exact UpperTheory.Cb.polarization_descent_along_quasi_isogeny_compat
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.SympQ
open GlobalTheory.Ex

theorem qq_free_of_torsion {C : Type} [Field C] [IsAlgClosed C] (N : NumD C) {k : ℕ} (hk : (k : C) ≠ 0) (a : ℕ)
    (hdiv : ∀ x : N.A, ∃ y, y ^ k = x)
    (e : (powMonoidHom k : N.A →* N.A).ker ≃* Multiplicative (Fin a → ZMod k)) :
    Nonempty (Qq N k ≃* Multiplicative (Fin (Module.finrank ℤ N.X + (a + Module.finrank ℤ N.X)) → ZMod k)) := by
  haveI : NeZero k := ⟨by rintro rfl; simp at hk⟩
  have hk0 : k ≠ 0 := NeZero.ne k
  obtain ⟨f⟩ := QStr.ker_struct N hk a e
  let v := Module.finBasis ℤ N.X
  let i₀ : (powMonoidHom k : N.Gt →* N.Gt).ker →* N.QT k := MonoidHom.mk'
    (fun g => ⟨(1, g.1), (show g.1 ^ k = 1 from g.2).trans N.io_zero.symm⟩)
    fun g g' => Subtype.ext (Prod.ext (_root_.mul_one _).symm rfl)
  let π₀ : N.QT k →* Multiplicative (Fin (Module.finrank ℤ N.X) → ZMod k) := MonoidHom.mk'
    (fun p => Multiplicative.ofAdd fun i => (v.repr p.1.1.toAdd i : ZMod k)) fun p q => by
      refine Multiplicative.toAdd.injective (funext fun i => ?_)
      simp
  have hπ₀ : ∀ p, π₀ p = 1 ↔ ∃ z : N.X, p.1.1.toAdd = k • z := fun p => by
    constructor
    · intro h
      have hd : ∀ i, (k : ℤ) ∣ v.repr p.1.1.toAdd i := fun i =>
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 (congrFun (congrArg Multiplicative.toAdd h) i)
      choose c hc using hd
      refine ⟨∑ i, c i • v i, ?_⟩
      conv_lhs => rw [← v.sum_repr p.1.1.toAdd]
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hc, mul_smul, natCast_zsmul]
    · rintro ⟨z, hz⟩
      refine Multiplicative.toAdd.injective (funext fun i => ?_)
      change ((v.repr p.1.1.toAdd i : ℤ) : ZMod k) = 0
      rw [hz]
      simp
  let π : Qq N k →* Multiplicative (Fin (Module.finrank ℤ N.X) → ZMod k) :=
    QuotientGroup.lift _ π₀ (by
      rintro _ ⟨z, rfl⟩
      exact (hπ₀ _).2 ⟨z.toAdd, rfl⟩)
  refine QStr.split_ext k _ _ ?_ (((QuotientGroup.mk' _).comp i₀).comp f.symm.toMonoidHom) π ?_ ?_ ?_
  · intro x
    obtain ⟨p, rfl⟩ := QuotientGroup.mk_surjective x
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact ⟨p.1.1, Subtype.ext (Prod.ext rfl (N.mem_QT.1 p.2).symm)⟩
  · refine Function.Injective.comp (g := (QuotientGroup.mk' _).comp i₀) ?_ f.symm.injective
    rw [injective_iff_map_eq_one]
    intro g hg
    obtain ⟨z, hz⟩ := (QuotientGroup.eq_one_iff _).1 hg
    have h1 : k • z.toAdd = 0 := congrArg (fun q : N.QT k => q.1.1.toAdd) hz
    have h2 : N.io z.toAdd = g.1 := congrArg (fun q : N.QT k => q.1.2) hz
    have h3 : z.toAdd = 0 := (smul_eq_zero.1 ((natCast_zsmul _ _).trans h1)).resolve_left (Nat.cast_ne_zero.2 hk0)
    exact Subtype.ext (by rw [← h2, h3, N.io_zero]; rfl)
  · intro c
    let y : N.X := ∑ i, ((c.toAdd i).val : ℤ) • v i
    obtain ⟨b, hb⟩ := hdiv (N.io y).b
    obtain ⟨u, -, hu⟩ := QStr.root_over N hk0 (N.io y) b hb
    refine ⟨QuotientGroup.mk ⟨(Multiplicative.ofAdd y, u), hu⟩, Multiplicative.toAdd.injective (funext fun i => ?_)⟩
    change ((v.repr y i : ℤ) : ZMod k) = c.toAdd i
    have : v.repr y i = ((c.toAdd i).val : ℤ) := congrFun (v.repr_sum_self _) i
    rw [this]
    simp
  · intro x
    obtain ⟨p, rfl⟩ := QuotientGroup.mk_surjective x
    constructor
    · intro h
      obtain ⟨z, hz⟩ := (hπ₀ p).1 h
      have hg : (p.1.2 * (N.io z)⁻¹) ^ k = 1 := by
        rw [mul_pow, inv_pow, N.mem_QT.1 p.2, hz, N.io_nsmul, mul_inv_cancel]
      refine ⟨f ⟨_, hg⟩, ?_⟩
      change QuotientGroup.mk (i₀ (f.symm (f ⟨_, hg⟩))) = _
      rw [f.symm_apply_apply, ← qEq_iff_mk_eq]
      exact ⟨z, hz.trans (zero_add _).symm, (inv_mul_cancel_right _ _).symm⟩
    · rintro ⟨y, hy⟩
      rw [← hy]
      exact (hπ₀ (i₀ (f.symm y))).2 ⟨0, (smul_zero _).symm⟩

theorem qq_free : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (D : DegData R (maximalIdeal R)) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N : GlobalTheory.Ex.NumD F) (ν : GlobalTheory.Ex.NumOf D.toPre F N) (n : ℕ), 0 < n → Nonempty (Additive (GlobalTheory.SympQ.Qq N n) ≃+ (Fin (2 * (D.toPre.P.g + Module.finrank ℤ D.toPre.X)) → ZMod n)) := by
  intro R _ _ _ hR D F _ _ _ N ν n hn
  have hL : Laws := GlobalTheory.allSixLaws.1
  haveI : IsNoetherianRing R := hR.1.1
  haveI : CharZero R := hR.2
  haveI : CharZero (FractionRing R) := charZero_of_injective_algebraMap (IsFractionRing.injective R _)
  haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap (FractionRing R) F).injective
  have hk : (n : F) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  have tor : ∀ (b : N.A) (k : ℕ), ν.eA b ^ k = 1 ↔ b ^ k = 1 := fun b k => by
    rw [← map_pow, MulEquiv.map_eq_one_iff]
  have hdiv : ∀ x : N.A, ∃ y, y ^ n = x := fun x => by
    obtain ⟨y, hy⟩ := ValuesTorsion.exists_pow_eq hL D.toPre.P (jFK (R := R) F ≫ jK R) (ν.eA x) hn
    exact ⟨ν.eA.symm y, by rw [← map_pow, hy, MulEquiv.symm_apply_apply]⟩
  obtain ⟨e⟩ : Nonempty ((powMonoidHom n : N.A →* N.A).ker ≃* Multiplicative (Fin (2 * D.toPre.P.g) → ZMod n)) := by
    obtain ⟨v, hv, h⟩ := ValuesTorsion.exists_basis hL D.toPre.P (jFK (R := R) F ≫ jK R) hk
    refine ValuesTorsion.nonempty_equiv_of_basis hn.ne' (fun i => ν.eA.symm (v i))
      (fun i => by rw [← map_pow, hv, map_one]) fun y hy => ?_
    refine (existsUnique_congr fun c => ?_).1 (h (ν.eA y) ((tor _ _).2 hy))
    simp only [List.prod_ofFn, ← map_pow, ← map_prod, MulEquiv.symm_apply_eq]
  obtain ⟨f⟩ := qq_free_of_torsion N hk _ hdiv e
  have hr : Module.finrank ℤ N.X = Module.finrank ℤ D.toPre.X := ν.eX.toIntLinearEquiv.finrank_eq
  have h2 : Module.finrank ℤ N.X + (2 * D.toPre.P.g + Module.finrank ℤ N.X) =
      2 * (D.toPre.P.g + Module.finrank ℤ D.toPre.X) := by rw [hr]; ring
  rw [← h2]
  exact ⟨MulEquiv.toAdditiveLeft f⟩

end GlobalTheory.SympQ
end
end
