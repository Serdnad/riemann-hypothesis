module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1221
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1220
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1306
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1278
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2681
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1564
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1219
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1217
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1402
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle015
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle074
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TorusExtensionOverCompleteLocalDvr
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.ExistsIsAddFundamentalDomain
import Mathlib.Algebra.Module.Torsion.Prod
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle024
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle022
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle015
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle018
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LocGenOfTrivial
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle013
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SymmetricLiftOddOrderExistsUnique
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle016
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle160
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle147
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2643
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.ExistsGeneratorOfIsField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2645
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2644
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle710
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow.Adapt


theorem main : AllVC fun {V} _ _ _ {D} {A} {G} _ _ U {C} _ _ {N} ν => ∃ (vB : Fin D.toPre.P.g → (epsR V ⟶ D.toPre.P.A)) (r : ℕ) (bX : Module.Basis (Fin r) ℤ N.X) (σ : Fin A.g ≃ Fin D.toPre.P.g ⊕ Fin r) (y : Fin A.g → (epsR V ⟶ G)) (gm₀ : Fin A.g → GtPt D.toPre (epsR V)) (gm : Fin A.g → GtPt D.toPre (TE V C)), IsLieBasis y ∧ Adapted ν vB bX σ gm ∧ ∀ j, TanRel U.toUnifPre (y j) (gm₀ j) ∧ GtTan (gm₀ j) ∧ GtPt.IsPull (spMap (dualMap (toF V C))) (gm₀ j) (gm j) := by
  intro V _ _ _ _ hV D A G _ _ hS U C _ _ _ _ _ _ hC N ν hν
  haveI := hV
  have hG : GlobalFnsSt := GlobalTheory.SemiRigid.globalFns
  obtain ⟨H, _, _, hH⟩ := GlobalTheory.TorusModel.exists_isGt hG (GlobalTheory.TorusModel.splitExt D.toPre)
  obtain ⟨Φ, hp, ha⟩ := GlobalTheory.TorusModel.exists_points hG hH
  have hΦ : GlobalTheory.TorusModel.Represents Φ := ⟨hp, ha⟩
  obtain ⟨vB, hvB⟩ := GlobalTheory.KeyPow.exists_isLieBasis D.toPre.P.A D.toPre.P.smoothDim
  let r := Module.finrank ℤ N.X
  let bX : Module.Basis (Fin r) ℤ N.X := Module.finBasis ℤ N.X
  let bD : Module.Basis (Fin r) ℤ D.toPre.X := bX.map ν.eX.toIntLinearEquiv
  choose lf hlf using fun i => (GlobalTheory.MBLow.GtVec.main V D.toPre).1 (vB i) (hvB.1 i)
  choose tv htv using fun l : Fin r => GlobalTheory.T.exists_torusExtensionTangent_of_additiveMap V D.toPre ((Int.castAddHom V).comp (bD.coord l).toAddMonoidHom)
  have hco : ∀ (l : Fin r) (χ : D.toPre.X), ((Int.castAddHom V).comp (bD.coord l).toAddMonoidHom) χ = ((bD.repr χ l : ℤ) : V) :=
    fun l χ => by simp [Module.Basis.coord_apply]
  let gm₀ : Fin D.toPre.P.g ⊕ Fin r → GtPt D.toPre (epsR V) := Sum.elim lf tv
  have hgt : ∀ j, GtTan (gm₀ j) := fun j => by
    cases j with
    | inl i => exact (hlf i).1
    | inr l => exact (htv l).1
  let x : Fin D.toPre.P.g ⊕ Fin r → (epsR V ⟶ H) := fun j => (Φ _).symm (gm₀ j)
  have hx : ∀ j, Φ _ (x j) = gm₀ j := fun j => Equiv.apply_symm_apply _ _
  have hxB : ∀ (n : ℕ) (σ : Fin n ≃ Fin D.toPre.P.g ⊕ Fin r), IsLieBasis (fun k => x (σ k)) := fun n σ =>
    GlobalTheory.T.lieBasis_torusExtension_of_lifts_and_duals V D.toPre H Φ hΦ r vB bD x hvB (fun j => by rw [hx]; exact hgt j) (fun i => by rw [hx]; exact (hlf i).2)
      (fun l => by
        rw [hx]
        refine ⟨(htv l).2.1, fun χ Z q z J hJ => ?_⟩
        rw [← hco]
        exact (htv l).2.2 χ Z q z J hJ) n σ
  have hz : ∀ T, (Φ T 1).IsZero := fun T => GlobalTheory.MBLow.GtVec.isZero_of_isAdd (by simpa using ha T 1 1)
  let red : baseOver (Sp V) ⟶ epsR V := Over.homMk (redE V) GlobalTheory.MBLow.GtVec.red_comp
  have tanG : ∀ w : epsR V ⟶ H, GtTan (Φ _ w) ↔ red ≫ w = 1 := fun w =>
    ⟨fun ⟨o, ho, h⟩ => (Φ _).injective ((GlobalTheory.TorusModel.isPull_unique (hp _ _ red w) h).trans
      (GlobalTheory.MBLow.GtVec.isZero_unique ho (hz _))), fun h => ⟨Φ _ 1, hz _, h ▸ hp _ _ red w⟩⟩
  have tanH : ∀ w : epsR V ⟶ H, IsTangent w ↔ red ≫ w = 1 := fun w => by
    constructor
    · intro h
      apply Over.OverMorphism.ext
      refine h.trans ?_
      show _ = (toUnit _ ≫ η[H]).left
      simp
    · intro h
      have := congrArg (·.left) h
      refine this.trans ?_
      show (toUnit _ ≫ η[H]).left = _
      simp
  have : Module.Finite V (DualNumber V) := inferInstanceAs (Module.Finite V (V × V))
  have : Module.Flat V (DualNumber V) := inferInstanceAs (Module.Flat V (V × V))
  have := isAdicComplete_map_of_finite (IsLocalRing.maximalIdeal V) (DualNumber V)
  have := GlobalTheory.MBLow.TanLift.isLocalRing_dualNumber V
  have hT : GlobalTheory.AdicColimit.IsAdicColimit (IsLocalRing.maximalIdeal V) (epsR V) :=
    GlobalTheory.TorusModel.isAdicColimit_of_finite_flat (IsLocalRing.maximalIdeal V) (RingHom.id V) (by rwa [Ideal.map_id])
      (fun a ha => ⟨1, by rw [Ideal.map_id, pow_one]; exact ha⟩) (DualNumber V)
  let Rel : (epsR V ⟶ G) → (epsR V ⟶ H) → Prop := fun y w => TanRel U.toUnifPre y (Φ _ w)
  have h1 : Rel 1 1 := (tanRel_iff_isPointOf U.toUnifPre 1 (Φ _ 1)).2 (GlobalTheory.FormalPoint.isPointOf_one U.toUnifPre (hz _))
  have hmul : ∀ y y' w w', Rel y w → Rel y' w' → Rel (y * y') (w * w') := fun y y' w w' h h' =>
    GlobalTheory.MBLow.TanAdd.tanRel_mul U.toUnifPre y y' _ _ _ h h' (ha _ w w')
  have hsc : ∀ (c : V) (y : epsR V ⟶ G) (w : epsR V ⟶ H) (y' : epsR V ⟶ G) (w' : epsR V ⟶ H),
      y'.left = spMap (epsScaleR c) ≫ y.left → w'.left = spMap (epsScaleR c) ≫ w.left → Rel y w → Rel y' w' := by
    intro c y w y' w' e e' h
    obtain rfl : y' = GlobalTheory.SecJet.epsScale V c ≫ y := Over.OverMorphism.ext e
    obtain rfl : w' = GlobalTheory.SecJet.epsScale V c ≫ w := Over.OverMorphism.ext e'
    exact GlobalTheory.MBLow.TanAdd.tanRel_scale U.toUnifPre c y _ _ h (hp _ _ _ w)
  have hex : ∀ y, IsTangent y → ∃ w, IsTangent w ∧ Rel y w := fun y hy => by
    obtain ⟨gm, h₁, h₂, -⟩ := GlobalTheory.MBLow.TanLift.exists_tan U.toUnifPre y hy
    refine ⟨(Φ _).symm gm, (tanH _).2 ((tanG _).1 (by rw [Equiv.apply_symm_apply]; exact h₂)), ?_⟩
    show TanRel _ _ _
    rw [Equiv.apply_symm_apply]; exact h₁
  have huy : ∀ y y' w, IsTangent y → IsTangent y' → Rel y w → Rel y' w → y = y' := fun y y' w _ _ h h' =>
    ((tanRel_iff_isPointOf _ _ _).1 h).unique ((tanRel_iff_isPointOf _ _ _).1 h')
  have hux : ∀ y w w', Rel y w → Rel y w' → w = w' := fun y w w' h h' =>
    (GlobalTheory.TorusModel.existsUnique_lift U.toUnifPre hΦ hT y).unique ((tanRel_iff_isPointOf _ _ _).1 h)
      ((tanRel_iff_isPointOf _ _ _).1 h')
  choose yy hyy using fun j => (existsUnique_tangent_of_gtTan V hV D A G hS U (gm₀ j) (hgt j)).exists
  have hyB : ∀ (n : ℕ) (σ : Fin n ≃ Fin D.toPre.P.g ⊕ Fin r), IsLieBasis (fun k => yy (σ k)) := fun n σ =>
    GlobalTheory.T.isLieBasis_of_compatible_tangentRelation V G H Rel h1 hmul hsc hex huy hux n _ _ (hxB n σ) fun k => ⟨(hyy _).1, by
      show TanRel _ _ _
      rw [hx]; exact (hyy _).2⟩
  have hdim : D.toPre.P.g + r = A.g := GlobalTheory.T.lieBasis_card_eq_dim_uniformisation_dvr V D A G U.toUnifPre _ _ (hyB _ finSumFinEquiv.symm)
  let σ : Fin A.g ≃ Fin D.toPre.P.g ⊕ Fin r := (finCongr hdim.symm).trans finSumFinEquiv.symm
  choose gmC hgmC using fun j => GlobalTheory.T.torusExtensionTangent_pullback_complexDualNumbers V D.toPre C N ν (gm₀ j) (hgt j)
  refine ⟨vB, r, bX, σ, fun k => yy (σ k), fun k => gm₀ (σ k), fun k => gmC (σ k), hyB _ σ,
    ⟨hvB, fun j => (hgmC _).2.1, fun i => ?_, fun l => ?_⟩, fun k => ⟨(hyy _).2, hgt _, (hgmC _).1⟩⟩
  · dsimp only
    rw [σ.apply_symm_apply (Sum.inl i), (hgmC _).1.1]
    show _ ≫ (lf i).b.left = _
    rw [(hlf i).2]
  · dsimp only
    rw [σ.apply_symm_apply (Sum.inr l)]
    refine ⟨(hgmC _).2.2.1 (htv l).2.1, fun χ => ?_⟩
    refine ((hgmC _).2.2.2 (((bD.repr (ν.eX χ) l : ℤ) : V)) (ν.eX χ) fun Z q z J hJ => ?_).trans ?_
    · have hv := (htv l).2.2 (ν.eX χ) Z q z J hJ
      rw [hco] at hv
      exact hv
    · have e : bD.repr (ν.eX χ) l = bX.repr χ l := by
        show (bX.map ν.eX.toIntLinearEquiv).repr (ν.eX χ) l = _
        rw [Module.Basis.map_repr]
        simp
      rw [e, map_intCast]

end GlobalTheory.MBLow.Adapt

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UMin.ThLocal
open GlobalTheory.ThetaPtMove GlobalTheory.ThetaPtExist

theorem sec_eq {X : Scheme.{0}} {M : LB X} {s s' : LB.Sec M} (h : ∀ j, s.f j = s'.f j) : s = s' := by
  cases s; cases s'
  simp only [LB.Sec.mk.injEq]
  exact funext h

theorem pullS_comp {S : Scheme.{0}} (G : Over S) [GrpObj G] {L : LB G.left} (hL : L.IsLB) (a : ℤ) {T T' T'' : Over S}
    (h : T' ⟶ T) (h' : T'' ⟶ T') (s : LB.Sec (LPow G L a T)) :
    VVRank.pullS G a h' (VVRank.pullS G a h s) = VVRank.pullS G a (h' ≫ h) s := by
  refine sec_eq (sec_ext_val hL (fun y J hJ => ?_))
  refine (VVRank.sv_pullS G a h' _ (𝟙 _) y hJ).trans ((VVRank.sv_pullS G a h s _ y hJ).trans ?_)
  refine Eq.trans ?_ (VVRank.sv_pullS G a (h' ≫ h) s (𝟙 _) y hJ).symm
  rw [MonoidalCategory.comp_whiskerRight, Over.comp_left, Category.assoc]

theorem exists_local : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (g m : ℕ) (R : Type) [CommRing R] [IsNoetherianRing R] (x : Sp R ⟶ S) (θ : SecAt G L x) (R₁ : Type) [CommRing R₁] [Algebra R R₁] [IsNoetherianRing R₁] (N : ℕ) (q : Fin N → (Over.mk (spMap (algebraMap R R₁) ≫ x) ⟶ G)), Odd m → IsUnit (m : R) → PolFib G L g x → (∀ a, q a ^ (m ^ 2) = 1) → ∀ p : Ideal R₁, p.IsPrime → ∃ f ∉ p, ∃ c : Fin N → Localization.Away f, ∀ (K : Type) [Field K] (j : Localization.Away f →+* K) (a : Fin N) (pt : Over.mk (spMap ((j.comp (algebraMap R₁ (Localization.Away f))).comp (algebraMap R R₁)) ≫ x) ⟶ G), pt.left = spMap (j.comp (algebraMap R₁ (Localization.Away f))) ≫ (q a).left → ThG G L ρ m (SecAt.pull G L θ ((j.comp (algebraMap R₁ (Localization.Away f))).comp (algebraMap R R₁))) pt (fn (j (c a))) := by
  intro S G _ _ L ρ hL hρ g m R _ _ x θ R₁ _ _ _ N q hm hmu hP hq p hp
  obtain ⟨P, α, -, hpb, w, hw⟩ := hP
  have hL₁ := P.isLB
  haveI := P.isAb.comm
  obtain ⟨ρ₁, hρ₁, hr⟩ := exists_rigidificationPullbackCompatibleIso hpb hw hL hL₁ hρ
  have hG : GlobalFnsSt := GlobalTheory.abelianSchemeLaws_all.1.globalFns
  have cg := GlobalTheory.AbLaw.CubeAssembly.cube_gen
  have neg := GlobalTheory.exists_gen_negLB hG
  obtain ⟨α₀, hα₀⟩ := (GlobalTheory.MulPull.mulPull_of_cube_of_symm cg neg).1 (Sp R) P m
  have sym := (GlobalTheory.symLift_odd hG (GlobalTheory.kerPow_of_square (GlobalTheory.AbSquare.square_of_cube cg).1).2.2 neg).1
  let T : Over (Sp R) := Over.mk (spMap (algebraMap R R₁))
  let T₁ : Over S := Over.mk (spMap (algebraMap R R₁) ≫ x)
  have hτ₁ : 𝟙 T.left ≫ T₁.hom = T.hom ≫ x := Category.id_comp _
  choose y hy hym using fun a => exists_torsion_down hpb (𝟙 T.left) (T₀ := T₁) hτ₁ (q a) (hq a)
  let pt₀ : T.left := (⟨p, hp⟩ : PrimeSpectrum R₁)
  choose V hV U hU using fun a => (sym (Sp R) P (m ^ 2) hm.pow T (y a) (hym a)).1 pt₀
  have hO : IsOpen (⋂ a, ((V a : T.left.Opens) : Set T.left)) := isOpen_iInter_of_finite fun a => (V a).2
  obtain ⟨_, ⟨f, rfl⟩, hf, hfO⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
    (show pt₀ ∈ ⋂ a, ((V a : T.left.Opens) : Set T.left) from Set.mem_iInter.2 hV) hO
  refine ⟨f, hf, ?_⟩
  let Lf := Localization.Away f
  let af : R₁ →+* Lf := algebraMap R₁ Lf
  let i_f : R →+* Lf := af.comp (algebraMap R R₁)
  let Tf : Over (Sp R) := Over.mk (spMap i_f)
  let β : Tf ⟶ T := Over.homMk (spMap af) (by
    show spMap af ≫ spMap (algebraMap R R₁) = spMap (af.comp (algebraMap R R₁))
    exact (spMap_comp _ _).symm)
  have hrange : ∀ a, Set.range (spMap af) ⊆ Set.range (V a).ι := by
    intro a
    rintro _ ⟨p', rfl⟩
    rw [Scheme.Opens.range_ι]
    exact Set.mem_iInter.1 (hfO ((PrimeSpectrum.localization_away_comap_range Lf f).le ⟨p', rfl⟩)) a
  have hsym : ∀ a, ∃ θ' : ThetaGrp P.A P.L ((m : ℤ) ^ 2) Tf,
      SymLift P.A P.L ((m : ℤ) ^ 2) (m ^ 2) (β ≫ y a) θ' := by
    intro a
    let u := IsOpenImmersion.lift (V a).ι (spMap af) (hrange a)
    have hu : u ≫ (V a).ι = spMap af := IsOpenImmersion.lift_fac _ _ _
    let r : Tf ⟶ overRes (V a) := Over.homMk u (by
      show u ≫ (V a).ι ≫ T.hom = Tf.hom
      rw [← Category.assoc, hu]
      exact Over.w β)
    obtain ⟨θ', h'⟩ := GlobalLift.exists_symLift_pull hL₁ r (hU a)
    have e : r ≫ overResι (V a) = β := Over.OverMorphism.ext hu
    rw [← Category.assoc, e] at h'
    rw [← Nat.cast_pow]
    exact ⟨θ', h'⟩
  let T₀ : Over S := Over.mk (spMap i_f ≫ x)
  have hτ : 𝟙 Tf.left ≫ T₀.hom = Tf.hom ≫ x := Category.id_comp _
  obtain ⟨th, hth⟩ := exists_secRel hpb (𝟙 Tf.left) (T₀ := T₀) hτ hw hL hL₁ (SecAt.pull G L θ i_f)
  have e₁ : (snd Tf P.A).left ≫ (mulA P.A m).left = (snd Tf P.A ^ m).left := by
    rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id]
  obtain ⟨αf, hαf, -⟩ := exists_gen hL₁ (φ' := ![(snd Tf P.A).left, (snd Tf P.A ^ m).left]) (ε' := ![(m : ℤ) ^ 2, -1])
    (fun U _ f => by
      refine Finset.prod_congr rfl fun i _ => ?_
      fin_cases i
      · exact congrArg (fun q => f q ^ ((m : ℤ) ^ 2)) (Category.comp_id _)
      · exact congrArg (fun q => f q ^ (-1 : ℤ)) e₁)
    (LB.pullGen P.L ![𝟙 P.A.left, (mulA P.A m).left] ![(m : ℤ) ^ 2, -1] α₀ (snd Tf P.A).left)
    (DVR.pullGen_isGen _ _ _ _ hα₀ _)
  obtain ⟨τf, hτf, -⟩ := exists_gen hL₁ (φ' := fun _ : Fin 1 => (1 : Tf ⟶ P.A).left) (ε' := fun _ => (m : ℤ) ^ 2)
    (fun U _ f => by
      rw [Fintype.prod_unique, Fin.prod_univ_one]
      exact congrArg₂ (fun q n => f q ^ n) rfl (by simp))
    (GeneratorPullback.powGen P.L _ _ (LB.pullGen P.L (fun _ : PUnit => eSec P.A) (fun _ => 1) ρ₁ (toUnit Tf).left) (m ^ 2))
    (DVR.powGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hρ₁ _) _)
  obtain ⟨s₁, hs₁⟩ := ThetaPtExist.exists_isTwistPull hL₁ (mulT P.A Tf m) (snd Tf P.A ^ m) (lift_snd _ _)
    ((m : ℤ) ^ 2) 1 αf hαf th
  choose Uf hUf using hsym
  choose s₂ hs₂ using fun a => ThetaPtExist.exists_isTwistPull hL₁ (translT P.A (Uf a).pt) (translPt P.A (Uf a).pt)
    (lift_snd _ _) ((m : ℤ) ^ 2) ((m : ℤ) ^ 2) (Uf a).φ (Uf a).isGen s₁
  choose wv hwv using fun a => ThetaPtExist.exists_isValueAt hL₁ (s₂ a) 1 τf hτf
  have hyf : ∀ a, (β ≫ y a) ^ (m ^ 2) = 1 := fun a => by rw [← MonObj.comp_pow, hym a, MonObj.comp_one]
  obtain ⟨e, he⟩ := exists_thG hL₁ hρ₁ m ((m : ℤ) ^ 2) (Nat.cast_pow m 2).symm hyf (th := th) (α := αf)
    hαf hτf hs₁ hUf hs₂ hwv
  refine ⟨fun a => (Scheme.ΓSpecIso (CommRingCat.of Lf)).hom.hom ((e : Γ(Tf.left, ⊤)) * wv a), ?_⟩
  intro K _ j a pt hpt
  clear hUf hs₂ hwv hs₁ sym hU hV hfO hO cg neg hG hrange
  let ξ : T₀ ⟶ T₁ := Over.homMk (spMap af) (by
    show spMap af ≫ spMap (algebraMap R R₁) ≫ x = spMap (af.comp (algebraMap R R₁)) ≫ x
    rw [← Category.assoc, ← spMap_comp])
  have hx₀ : 𝟙 Tf.left ≫ (ξ ≫ q a).left = (β ≫ y a).left ≫ α := by
    have h := hy a
    rw [Category.id_comp] at h
    rw [Category.id_comp, Over.comp_left, Over.comp_left, Category.assoc, ← h]
    rfl
  have hn₀ : (ξ ≫ q a) ^ (m ^ 2) = 1 := by rw [← MonObj.comp_pow, hq a, MonObj.comp_one]
  have up := ThG.up hpb (T := Tf) (T₀ := T₀) (𝟙 Tf.left) hτ hw hL hL₁ hr hx₀ hn₀ hth (he a)
  let δ : Over.mk (spMap ((j.comp af).comp (algebraMap R R₁)) ≫ x) ⟶ T₀ := Over.homMk (spMap j) (by
    show spMap j ≫ spMap (af.comp (algebraMap R R₁)) ≫ x = spMap ((j.comp af).comp (algebraMap R R₁)) ≫ x
    rw [← Category.assoc, ← spMap_comp])
  have down := ThPull.thG_pull hL hρ δ up
  have ept : pt = δ ≫ ξ ≫ q a := by
    refine Over.OverMorphism.ext ?_
    rw [hpt, Over.comp_left, Over.comp_left, ← Category.assoc]
    exact congrArg (· ≫ (q a).left) (spMap_comp af j)
  have eθ : SecAt.pull G L θ ((j.comp af).comp (algebraMap R R₁)) = VVRank.pullS G _ δ (SecAt.pull G L θ i_f) := by
    unfold SecAt.pull
    rw [pullS_comp G hL]
    congr 1
    refine Over.OverMorphism.ext ?_
    exact spMap_comp i_f j
  have ec : δ.left.appTop.hom ((inv (𝟙 Tf.left)).appTop.hom ((e : Γ(Tf.left, ⊤)) * wv a)) =
      fn (j ((Scheme.ΓSpecIso (CommRingCat.of Lf)).hom.hom ((e : Γ(Tf.left, ⊤)) * wv a))) := by
    have h1 : (inv (𝟙 Tf.left)).appTop.hom ((e : Γ(Tf.left, ⊤)) * wv a) =
        fn ((Scheme.ΓSpecIso (CommRingCat.of Lf)).hom.hom ((e : Γ(Tf.left, ⊤)) * wv a)) := by
      simp only [IsIso.inv_id, Scheme.Hom.id_appTop, CommRingCat.hom_id, RingHom.id_apply]
      exact ((Scheme.ΓSpecIso (CommRingCat.of Lf)).hom_inv_id_apply _).symm
    rw [h1]
    exact (congrArg (fun q => q.hom ((Scheme.ΓSpecIso (CommRingCat.of Lf)).hom.hom ((e : Γ(Tf.left, ⊤)) * wv a)))
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom j))).symm
  rw [ept, eθ, ← ec]
  exact down

end GlobalTheory.UMin.ThLocal
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.isThetaConstantListOfFibre_pullback_field_extension : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (m N : ℕ) (K K' : Type) [Field K] [Field K'] (i : K →+* K') (x : Sp K ⟶ S) (θ : SecAt G L x) (pt : Fin N → (Over.mk x ⟶ G)) (c : Fin N → K), ThList G L ρ m x θ pt c → ∃ pt' : Fin N → (Over.mk (spMap i ≫ x) ⟶ G), (∀ a, (pt' a).left = spMap i ≫ (pt a).left) ∧ ThList G L ρ m (spMap i ≫ x) (SecAt.pull G L θ i) pt' (fun a => i (c a)) := by
  first | exact @GlobalTheory.UMin.ThPull.thList_pull | exact GlobalTheory.UMin.ThPull.thList_pull | (intros; apply GlobalTheory.UMin.ThPull.thList_pull <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.thetaConstant_kth_root_labelled_point_up_to_root : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (K : Type) [Field K] (i : S.R →+* K) (b : S.Gam) (y : Over.mk (spMap i ≫ 𝟙 (Sp S.R)) ⟶ ρ.P.A) (v : K), y ^ (S.r * S.N) = (Over.homMk (spMap i) (by simp) : Over.mk (spMap i ≫ 𝟙 (Sp S.R)) ⟶ baseOver (Sp S.R)) ≫ ρ.pt b → ThG ρ.P.A ρ.P.L ρ.rig (S.r * S.N) (SecAt.pull ρ.P.A ρ.P.L (x := 𝟙 (Sp S.R)) ρ.th₁ i) y (GlobalTheory.ZH.fn v) → v ^ ((S.r * S.N) ^ 2) = i ⟨S.th b, S.th_mem b⟩ ^ ((S.r * S.N) ^ 2) := by
  first | exact @GlobalTheory.thetaConst_pow_eq_at_root | exact GlobalTheory.thetaConst_pow_eq_at_root | (intros; apply GlobalTheory.thetaConst_pow_eq_at_root <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.thetaConstant_unique_field_point_polarisedFibre : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (g m : ℕ) (R : Type) [CommRing R] [IsNoetherianRing R] (x : Sp R ⟶ S) (K : Type) [Field K] (i : R →+* K), Odd m → IsUnit (m : R) → PolFib G L g x → ∀ (th : SecAt G L (spMap i ≫ x)) (pt : Over.mk (spMap i ≫ x) ⟶ G) (c c' : K), ThG G L ρ m th pt (fn c) → ThG G L ρ m th pt (fn c') → c = c' := by
  first | exact @GlobalTheory.UMin.thG_unique_of_polFib | exact GlobalTheory.UMin.thG_unique_of_polFib | (intros; apply GlobalTheory.UMin.thG_unique_of_polFib <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UMin.GalConj
open GlobalTheory.UMin.GalTh

theorem coe_mul {Ω K : Type} [Field Ω] [Field K] [Algebra Ω K] (τ₁ τ₂ : K ≃ₐ[Ω] K) :
    ((τ₁ * τ₂ : K ≃ₐ[Ω] K) : K →+* K) = (τ₁ : K →+* K).comp (τ₂ : K →+* K) := RingHom.ext fun _ => rfl

theorem coe_one {Ω K : Type} [Field Ω] [Field K] [Algebra Ω K] :
    ((1 : K ≃ₐ[Ω] K) : K →+* K) = RingHom.id K := RingHom.ext fun _ => rfl

theorem comp_alg {Ω K : Type} [Field Ω] [Field K] [Algebra Ω K] (τ : K ≃ₐ[Ω] K) :
    (τ : K →+* K).comp (algebraMap Ω K) = algebraMap Ω K := RingHom.ext fun r => τ.commutes r

theorem thList_conj : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (g m N : ℕ) (Ω K : Type) [Field Ω] [Field K] [IsAlgClosed K] [Algebra Ω K] (x : Sp Ω ⟶ S) (θ : SecAt G L x) (pt : Fin N → (Over.mk (spMap (algebraMap Ω K) ≫ x) ⟶ G)) (c : Fin N → K), Odd m → (m : K) ≠ 0 → PolFib G L g (spMap (algebraMap Ω K) ≫ x) → ThList G L ρ m (spMap (algebraMap Ω K) ≫ x) (SecAt.pull G L θ (algebraMap Ω K)) pt c → ∃ φ : (K ≃ₐ[Ω] K) →* Equiv.Perm (Fin N), ∀ (τ : K ≃ₐ[Ω] K) (a : Fin N), spMap (τ : K →+* K) ≫ (pt a).left = (pt (φ τ a)).left ∧ τ (c a) = c (φ τ a) := by
  intro S G _ _ L ρ hL hρ g m N Ω K _ _ _ _ x θ pt c hm hmK hpol hK
  classical
  have hfix : ∀ τ : K ≃ₐ[Ω] K, spMap (τ : K →+* K) ≫ (Over.mk (spMap (algebraMap Ω K) ≫ x)).hom = (Over.mk (spMap (algebraMap Ω K) ≫ x)).hom := fun τ => by
    show spMap (τ : K →+* K) ≫ spMap (algebraMap Ω K) ≫ x = spMap (algebraMap Ω K) ≫ x
    rw [← Category.assoc, ← GalTh.sp_comp, comp_alg]
  let u : (K ≃ₐ[Ω] K) → (Over.mk (spMap (algebraMap Ω K) ≫ x) ⟶ Over.mk (spMap (algebraMap Ω K) ≫ x)) := fun τ => Over.homMk (spMap (τ : K →+* K)) (hfix τ)
  have hul : ∀ τ, (u τ).left = spMap (τ : K →+* K) := fun τ => Over.homMk_left _ _
  have hu1 : u 1 = 𝟙 _ := Over.OverMorphism.ext (by rw [hul, coe_one, GalTh.sp_id]; rfl)
  have humul : ∀ τ₁ τ₂, u (τ₁ * τ₂) = u τ₁ ≫ u τ₂ := fun τ₁ τ₂ =>
    Over.OverMorphism.ext (by rw [Over.comp_left, hul, hul, hul, coe_mul, GalTh.sp_comp])
  have htor : ∀ τ a, (u τ ≫ pt a) ^ (m ^ 2) = 1 := fun τ a => by
    rw [← MonObj.comp_pow, (hK.2.1 a).1, MonObj.comp_one]
  choose f hf using fun τ a => thList_exh hK (u τ ≫ pt a) (htor τ a)
  have hf1 : ∀ a, f 1 a = a := fun a => hK.1 (by rw [← hf, hu1, Category.id_comp])
  have hfmul : ∀ τ₁ τ₂ a, f (τ₁ * τ₂) a = f τ₁ (f τ₂ a) := fun τ₁ τ₂ a => hK.1 (by
    rw [← hf, ← hf, ← hf, humul, Category.assoc])
  let P : (K ≃ₐ[Ω] K) → Equiv.Perm (Fin N) := fun τ =>
    { toFun := f τ, invFun := f τ⁻¹
      left_inv := fun a => by rw [← hfmul, inv_mul_cancel, hf1]
      right_inv := fun a => by rw [← hfmul, mul_inv_cancel, hf1] }
  let φ : (K ≃ₐ[Ω] K) →* Equiv.Perm (Fin N) :=
    { toFun := P
      map_one' := Equiv.ext fun a => hf1 a
      map_mul' := fun τ₁ τ₂ => Equiv.ext fun a => hfmul τ₁ τ₂ a }
  have hφ : ∀ τ a, φ τ a = f τ a := fun _ _ => rfl
  have hleft : ∀ (τ : K ≃ₐ[Ω] K) a, spMap (τ : K →+* K) ≫ (pt a).left = (pt (f τ a)).left := fun τ a => by
    rw [← hf, Over.comp_left, hul]
  refine ⟨φ, fun τ a => ⟨by rw [hφ]; exact hleft τ a, ?_⟩⟩
  rw [hφ]
  obtain ⟨pt', hpt', h'⟩ := GlobalTheory.UMin.ThPull.thList_pull S G L ρ hL hρ m N K K (τ : K →+* K) (spMap (algebraMap Ω K) ≫ x)
    (SecAt.pull G L θ (algebraMap Ω K)) pt c hK
  obtain ⟨pt₃, hpt₃, h₃⟩ := thList_comp m (algebraMap Ω K) (τ : K →+* K) (algebraMap Ω K) (comp_alg τ) x θ pt' _ h'
  have e3 : pt₃ a = pt (f τ a) := Over.OverMorphism.ext (by rw [hpt₃, hpt', hleft])
  have q := h₃.2.1 a
  rw [e3] at q
  have hθ : SecM.ofSec G (SecAt.pull G L θ (algebraMap Ω K)) =
      @id Γ((Over.mk (spMap (algebraMap Ω K) ≫ x)).left, ⊤) (GlobalTheory.ZH.fn (1 : K)) • SecM.ofSec G (SecAt.pull G L θ (algebraMap Ω K)) := by
    rw [id, show GlobalTheory.ZH.fn (1 : K) = 1 from map_one _, one_smul]
  have r := (GlobalTheory.UMin.thG_smul_iff S G L ρ hL hρ g m K (spMap (algebraMap Ω K) ≫ x) _ _ (pt (f τ a)) 1 (c (f τ a)) (τ (c a)) hm hmK hpol hθ
    (hK.2.1 (f τ a))).1 q
  rw [r, _root_.one_mul]

end GlobalTheory.UMin.GalConj
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_basicOpen_generating_section_all_fibres : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (L : LB G.left), L.IsLB → ∀ (g : ℕ) (R : Type) [CommRing R] [IsNoetherianRing R] (x : Sp R ⟶ S), PolFib G L g x → ∀ p : PrimeSpectrum R, ∃ r : R, r ∉ p.asIdeal ∧ ∃ θ : SecAt G L (spMap (algebraMap R (Localization.Away r)) ≫ x), ∀ (K : Type) [Field K] (i : Localization.Away r →+* K), IsGenSec G L _ (SecAt.pull G L θ i) := by
  first | exact @GlobalTheory.UMin.exists_basicOpen_genSec_fibres | exact GlobalTheory.UMin.exists_basicOpen_genSec_fibres | (intros; apply GlobalTheory.UMin.exists_basicOpen_genSec_fibres <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_projectiveSpace_map_of_model_hasDiv : ∀ (k Ω : Type) [CommRing k] [Field Ω] [Algebra k Ω] (M : RatModel k Ω) (n : ℕ) (c : Fin (n + 1) → Ω), M.HasDiv c → ∃ h : M.Z ⟶ PSpace k n, h ≫ PSpace.str k n = M.s ∧ PCrd (M.pt ≫ h) c := by
  first | exact @GlobalTheory.UMin.CrdMap.exists_map_of_hasDiv | exact GlobalTheory.UMin.CrdMap.exists_map_of_hasDiv | (intros; apply GlobalTheory.UMin.CrdMap.exists_map_of_hasDiv <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.model_hasDiv_of_genericPoint_projectiveCoords : ∀ (k Ω o : Type) [CommRing k] [Field Ω] [Algebra k Ω] [CommRing o] (M : RatModel k Ω) (n : ℕ) (g : M.Z ⟶ PSpace o n) (e : Fin (n + 1) → Ω), PCrd (M.pt ≫ g) e → M.HasDiv e := by
  first | exact @GlobalTheory.UMin.hasDiv_of_pCrd_pt | exact GlobalTheory.UMin.hasDiv_of_pCrd_pt | (intros; apply GlobalTheory.UMin.hasDiv_of_pCrd_pt <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.principallyPolarisedFibre_exists_generator_stable : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (L : LB G.left), L.IsLB → ∀ (g : ℕ) (K : Type) [Field K] (x : Sp K ⟶ S), PolFib G L g x → (∃ θ : SecAt G L x, IsGenSec G L _ θ) ∧ ∀ θ : SecAt G L x, IsGenSec G L _ θ → ∀ (K' : Type) [Field K'] (i : K →+* K'), IsGenSec G L _ (SecAt.pull G L θ i) := by
  first | exact @GlobalTheory.UMin.gen_of_polFib | exact GlobalTheory.UMin.gen_of_polFib | (intros; apply GlobalTheory.UMin.gen_of_polFib <;> assumption)
end
