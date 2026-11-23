module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3113
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle848
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle009
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle011
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3351
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle067
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveLatticeTwistGenerated
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle046
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle849
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle790
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle070
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle143
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2794
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2795
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3312
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2917
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3349
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3022
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle061
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle032
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.RingTheory.AdicCompletion.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3352
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle819
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle214
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.PullGt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.SpecChain

theorem eqvGen_specializes {X : Type*} [TopologicalSpace X] [TopologicalSpace.NoetherianSpace X] [QuasiSober X]
    [PreconnectedSpace X] (x y : X) : Relation.EqvGen (· ⤳ ·) x y := by
  classical
  let C : Set X := {y | Relation.EqvGen (· ⤳ ·) x y}
  have hsub : ∀ K ∈ irreducibleComponents X, (K ∩ C).Nonempty → K ⊆ C := by
    rintro K hK ⟨w, hwK, hwC⟩ v hv
    have hI : IsIrreducible K := hK.1
    have hcl : IsClosed K := isClosed_of_mem_irreducibleComponents K hK
    have hg := hI.isGenericPoint_genericPoint hcl
    have h1 : hI.genericPoint ⤳ w := hg.specializes hwK
    have h2 : hI.genericPoint ⤳ v := hg.specializes hv
    exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.trans _ _ _ hwC (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ h1)))
      (Relation.EqvGen.rel _ _ h2)
  have hfin := TopologicalSpace.NoetherianSpace.finite_irreducibleComponents (α := X)
  have hC : C = ⋃ K ∈ {K ∈ irreducibleComponents X | (K ∩ C).Nonempty}, K := by
    ext v
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]
    constructor
    · intro hv
      exact ⟨irreducibleComponent v, ⟨irreducibleComponent_mem_irreducibleComponents v,
        ⟨v, mem_irreducibleComponent, hv⟩⟩, mem_irreducibleComponent⟩
    · rintro ⟨K, ⟨hK, hne⟩, hvK⟩
      exact hsub K hK hne hvK
  have hCc : Cᶜ = ⋃ K ∈ {K ∈ irreducibleComponents X | ¬ (K ∩ C).Nonempty}, K := by
    ext v
    simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]
    constructor
    · intro hv
      refine ⟨irreducibleComponent v, ⟨irreducibleComponent_mem_irreducibleComponents v, ?_⟩, mem_irreducibleComponent⟩
      intro hne
      exact hv (hsub _ (irreducibleComponent_mem_irreducibleComponents v) hne mem_irreducibleComponent)
    · rintro ⟨K, ⟨hK, hne⟩, hvK⟩ hv
      exact hne ⟨v, hvK, hv⟩
  have hC1 : IsClosed C := by
    rw [hC]
    exact (hfin.subset (Set.sep_subset _ _)).isClosed_biUnion fun K hK => isClosed_of_mem_irreducibleComponents K hK.1
  have hC2 : IsClosed Cᶜ := by
    rw [hCc]
    exact (hfin.subset (Set.sep_subset _ _)).isClosed_biUnion fun K hK => isClosed_of_mem_irreducibleComponents K hK.1
  have hclo : IsClopen C := ⟨hC1, isClosed_compl_iff.mp hC2⟩
  have hx : x ∈ C := Relation.EqvGen.refl x
  have := hclo.eq_univ ⟨x, hx⟩
  have hy : y ∈ C := this ▸ Set.mem_univ y
  exact hy

theorem quasiSober_of_generalization {X : Type*} [TopologicalSpace X] [QuasiSober X] (S : Set X)
    (hS : ∀ x s, s ∈ S → x ⤳ s → x ∈ closure S → x ∈ S) : QuasiSober S := by
  constructor
  intro T hT hTc
  have hT' : IsIrreducible (((↑) : S → X) '' T) := hT.image _ continuous_subtype_val.continuousOn
  have hξ := hT'.isGenericPoint_genericPoint_closure
  obtain ⟨t, ht⟩ := hT.nonempty
  have hξt : hT'.genericPoint ⤳ (t : X) := hξ.specializes (subset_closure ⟨t, ht, rfl⟩)
  have hξS : hT'.genericPoint ∈ S :=
    hS _ t t.2 hξt (closure_mono (Subtype.coe_image_subset S T) hξ.mem)
  refine ⟨⟨hT'.genericPoint, hξS⟩, ?_⟩
  show closure {(⟨hT'.genericPoint, hξS⟩ : S)} = T
  rw [Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image, Set.image_singleton]
  change ((↑) : S → X) ⁻¹' closure {hT'.genericPoint} = T
  rw [hξ.def, ← Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image, hTc.closure_eq]

theorem eqvGen_of_isPreconnected {X : Type*} [TopologicalSpace X] [TopologicalSpace.NoetherianSpace X] [QuasiSober X]
    (S : Set X) (hc : IsPreconnected S) (hS : ∀ x s, s ∈ S → x ⤳ s → x ∈ closure S → x ∈ S) :
    ∀ a ∈ S, ∀ b ∈ S, Relation.EqvGen (fun u v : X => u ∈ S ∧ v ∈ S ∧ u ⤳ v) a b := by
  intro a ha b hb
  haveI := quasiSober_of_generalization S hS
  haveI : PreconnectedSpace S := Subtype.preconnectedSpace hc
  have h := eqvGen_specializes (⟨a, ha⟩ : S) ⟨b, hb⟩
  have key : ∀ u v : S, Relation.EqvGen (· ⤳ ·) u v →
      Relation.EqvGen (fun u v : X => u ∈ S ∧ v ∈ S ∧ u ⤳ v) u v := by
    intro u v huv
    induction huv with
    | rel p q hpq => exact Relation.EqvGen.rel _ _ ⟨p.2, q.2, hpq.map continuous_subtype_val⟩
    | refl p => exact Relation.EqvGen.refl _
    | symm p q _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans p q r _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2
  exact key _ _ h

end GlobalTheory.SpecChain

namespace GlobalTheory.SpecChain

theorem fibre_chain : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (Y : RatModel X₁.o₁ X₁.Ω₁) (πY : Y.Z ⟶ X₁.M.Z), Cmp.ZHAbove X₁ Y πY → ∀ y y' : Y.Z, πY y = z₁ → πY y' = z₁ → Relation.EqvGen (fun a b : Y.Z => πY a = z₁ ∧ πY b = z₁ ∧ a ⤳ b) y y' := by
  intro g n F W Z i X₁ z₁ Y πY hZH y y' hy hy'
  obtain ⟨U₀, EE, -, -, -, hHom, hProp⟩ := hZH
  obtain ⟨U, hU, hiso⟩ := GlobalTheory.T.exists_nonempty_isIso_morphismRestrict_of_isHom_id X₁.o₁ X₁.Ω₁ Y X₁.M πY hHom
  haveI : IsDedekindDomain X₁.o₁ := X₁.ar.ded
  haveI : IsLocallyNoetherian (Sp X₁.o₁) :=
    inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of X₁.o₁)))
  haveI := X₁.M.lft
  haveI := Y.lft
  haveI := Y.qc
  haveI : IsLocallyNoetherian X₁.M.Z := LocallyOfFiniteType.isLocallyNoetherian X₁.M.s
  haveI : IsLocallyNoetherian Y.Z := LocallyOfFiniteType.isLocallyNoetherian Y.s
  haveI : CompactSpace Y.Z := by
    constructor
    have := QuasiCompact.isCompact_preimage (f := Y.s) (U := Set.univ) isOpen_univ isCompact_univ
    simpa using this
  haveI : IsNoetherian Y.Z := {}
  haveI : IsProper πY := hProp
  have hN : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X₁.M.Z := (GlobalTheory.isNormalScheme_iff_pred _).1 X₁.normal
  have hc := GlobalTheory.ZariskiConn.fibre_preconnected Y.Z X₁.M.Z πY hN U hU hiso z₁
  have hS : ∀ x s, s ∈ πY.base ⁻¹' {z₁} → x ⤳ s → x ∈ closure (πY.base ⁻¹' {z₁}) → x ∈ πY.base ⁻¹' {z₁} := by
    intro x s hs hxs hx
    have h1 : πY.base x ⤳ z₁ := by
      have := hxs.map πY.base.hom.continuous
      rwa [show πY.base s = z₁ from hs] at this
    have h2 : z₁ ⤳ πY.base x := by
      rw [specializes_iff_mem_closure]
      have hcont := πY.base.hom.continuous
      have : closure (πY.base ⁻¹' {z₁}) ⊆ πY.base ⁻¹' closure {z₁} :=
        closure_minimal (Set.preimage_mono subset_closure) (isClosed_closure.preimage hcont)
      exact this hx
    exact (h1.antisymm h2).eq
  exact eqvGen_of_isPreconnected _ hc hS y hy y' hy'

end GlobalTheory.SpecChain
end

section


theorem _root_.GlobalTheory.T.chernNumbers_eq_integral_chernForms_smoothMetric : GlobalTheory.Published.ChernWeilNumbers := by
  first | exact @GlobalTheory.ChernDegree.chernWeilNumbers_holds | exact GlobalTheory.ChernDegree.chernWeilNumbers_holds | (intros; apply GlobalTheory.ChernDegree.chernWeilNumbers_holds <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.poincareDeRhamDuality_of_hodgeDeRham_dual : GlobalTheory.Published.AbelianHodgeDeRham → GlobalTheory.Published.DualAbelianScheme → GlobalTheory.Published.PoincareDeRhamDuality := by
  first | exact @GlobalTheory.PoincareDeRhamDualityProof.poincareDeRhamDuality_of_hodge | exact GlobalTheory.PoincareDeRhamDualityProof.poincareDeRhamDuality_of_hodge | (intros; apply GlobalTheory.PoincareDeRhamDualityProof.poincareDeRhamDuality_of_hodge <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.dualPoincare_left_kernel_trivial_algClosed : ∀ (K : Type) [Field K] [IsAlgClosed K] (A B : Over (Sp K)) [GrpObj A] [GrpObj B] (g : ℕ) (P : LB (A ⊗ B).left), IsAbelianScheme A → IsAbelianScheme B → SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g B.hom → IsDual A B P → ∀ (T : Over (Sp K)) (x : T ⟶ A), Triv (ev P (fst T B ≫ x) (snd T B)) → x = 1 := by
  first | exact @GlobalTheory.DualKer.leftKer_eq_one | exact GlobalTheory.DualKer.leftKer_eq_one | (intros; apply GlobalTheory.DualKer.leftKer_eq_one <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open Classical
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.Poinc.exists_zhModel_proper_over_setup : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∃ (Y : RatModel X₁.o₁ X₁.Ω₁) (U₀ : Y.Z.Opens) (EE : Y.Lat X₁.S.J) (_ : ZHOut X₁.ρ Y U₀ EE) (q : Y.Z ⟶ X₁.M.Z), X₁.S.Over₀ Y U₀ ∧ X₁.S.IsEE Y U₀ EE ∧ IsProper q ∧ Y.pt ≫ q = X₁.M.pt ∧ (∀ z₁ : X₁.M.Z, _root_.IsPreconnected (q.base ⁻¹' {z₁})) ∧ ∀ (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (c : CTrait X₁ p z₁), ∃ y : Sp (OO p) ⟶ Y.Z, y ≫ q = c.y := by
  intro g n F W Z i X₁ hg hn hodd himm he8 hti hproj
  obtain ⟨m, c, hc⟩ := RatModel.exists_isCl_of_isProjOver hproj
  have hc0 : ∃ j, c j ≠ 0 := by
    obtain ⟨j, hj⟩ := hc.1 (genericPoint X₁.M.Z)
    exact ⟨j, hj.1⟩
  obtain ⟨Y, U₀, EE, hO, hdiv, hE, ⟨G⟩⟩ := GlobalTheory.zhSt_holds X₁.o₁ X₁.Ω₁ X₁.S X₁.ρ X₁.big (Fin (m + 1)) c hc0
    (GlobalTheory.T.finite_closure_theta_ratios_of_isCl' X₁.o₁ X₁.Ω₁ X₁.S X₁.M (Fin (m + 1)) c hc)
  obtain ⟨q, hq⟩ := hc.exists_isHom (M' := Y) (φ := AlgHom.id X₁.o₁ X₁.Ω₁) hdiv
  have hYp : IsProper Y.s := ((GlobalTheory.isProjOver_iff_isProper_and_exists_isAmpleLB _).1 hO.proj).1
  have hsep : IsSeparated X₁.M.s := X₁.M.sep
  have hqp : IsProper q := by
    haveI : IsProper (q ≫ X₁.M.s) := by rw [hq.inducedModelMorphism_comp_structureMap]; exact hYp
    exact IsProper.of_comp q X₁.M.s
  have hpt : Y.pt ≫ q = X₁.M.pt :=
    hq.trans ((congrArg (· ≫ X₁.M.pt) (Spec.map_id _)).trans (Category.id_comp _))
  refine ⟨Y, U₀, EE, G, q, hO, hE, hqp, hpt, ?_, ?_⟩
  · obtain ⟨U, hU, hiso⟩ := GlobalTheory.T.exists_nonempty_isIso_morphismRestrict_of_isProjOver X₁.o₁ X₁.Ω₁ Y X₁.M hO.proj q hq
    have : IsDedekindDomain X₁.o₁ := (inferInstance : ArithBase X₁.o₁ X₁.Ω₁).ded
    have := X₁.M.lft
    have : IsLocallyNoetherian X₁.M.Z := LocallyOfFiniteType.isLocallyNoetherian X₁.M.s
    exact GlobalTheory.ZariskiConn.fibre_preconnected Y.Z X₁.M.Z q (fun x => ⟨X₁.normal.isDomain_stalk x, X₁.normal.isIntegrallyClosed_stalk x⟩) U hU hiso
  · intro p _ z₁ c
    exact GlobalTheory.T.exists_lift_of_isProper_of_isHom_id' X₁.o₁ X₁.Ω₁ Y X₁.M q hq hqp p c.y
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.Poinc.Eq8.TraitOne

theorem factor_stalk (X : Scheme.{0}) (x : X) (V : Type) [CommRing V] [IsLocalRing V] (ξ : Sp V ⟶ X)
    (hx : ξ (IsLocalRing.closedPoint V) ⤳ x) :
    ∃ f : X.presheaf.stalk x →+* V, spMap f ≫ X.fromSpecStalk x = ξ := by
  refine ⟨(Scheme.stalkClosedPointTo ξ).hom.comp (X.presheaf.stalkSpecializes hx).hom, ?_⟩
  have e1 := Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ
  have e2 := Scheme.SpecMap_stalkSpecializes_fromSpecStalk hx
  conv_rhs => rw [← e1, ← e2]
  show Spec.map (CommRingCat.ofHom _) ≫ _ = _
  rw [← Category.assoc, ← Spec.map_comp]
  rfl

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (a : A →+* B) (b : B →+* C) :
    spMap (b.comp a) = spMap b ≫ spMap a := by
  rw [← Spec.map_comp]
  rfl

theorem subset_abLocus {o' Ω : Type} [CommRing o'] [Field Ω] [Algebra o' Ω] {S : ThetaSys o' Ω} {ρ : S.Real}
    {M : RatModel o' Ω} {U₀ : M.Z.Opens} {EE : M.Lat S.J} (FinalForm : ZHOut ρ M U₀ EE) :
    (U₀ : Set M.Z) ⊆ abLocus FinalForm.G := by
  intro z hz
  obtain ⟨z', rfl⟩ : z ∈ Set.range U₀.ι := by rw [Scheme.Opens.range_ι]; exact hz
  rw [abLocus_pullback (G' := (Over.pullback FinalForm.u₀).obj ρ.P.A) abLocusOne FinalForm.semi FinalForm.cart.1]
  intro K _ _ t _
  haveI := ρ.P.isAb.proper
  show IsProper (pullback.snd (pullback.snd ρ.P.A.hom FinalForm.u₀) t)
  infer_instance

theorem main : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real), S.Big → ∀ (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), S.admitted M U₀ → S.IsEE M U₀ EE → ∀ x : M.Z, IsClosed ({x} : Set M.Z) → ∀ (u : Sp S.R ⟶ F.X) c pr, SharpBy F W ρ.P u c pr → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (j : M.Z.presheaf.stalk x →+* R), GlobalTheory.Mum.Base R → IsCpl j → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (gm : G.left ⟶ FinalForm.G.left), IsGrpPullback G FinalForm.G (spMap j ≫ M.Z.fromSpecStalk x) gm → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G), LBIso U.LG.L (FinalForm.L.L.pull gm) → (∀ y, PsiUnitOn D.toPre y ((spMap j ≫ M.Z.fromSpecStalk x) ⁻¹' abLocus FinalForm.G)) → ∀ m : Fin 8 → Fin 8 → (D.toPre.X →+ D.toPre.X), (∀ a b, ∃ (f : FinalForm.G ⟶ FinalForm.G) (fR : G ⟶ G), MatOn FinalForm pr a b f ∧ IsMonHom fR ∧ fR.left ≫ gm = gm ≫ f.left ∧ EndChar U fR (m a b)) → ∀ (T : Trait F) (ξ : Sp T.V ⟶ M.Z), ThroughU M U₀ FinalForm.u₀ u T ξ → ξ (IsLocalRing.closedPoint T.V) ⤳ x → ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsDiscreteValuationRing V') (h : T.V →+* V') (g' : R →+* V') (ρT : D.toPre.X →+ (Fin 8 → T.D.toPre.X)), Function.Injective h ∧ Irreducible (h T.ϖ) ∧ spMap g' ≫ (spMap j ≫ M.Z.fromSpecStalk x) = spMap h ≫ ξ ∧ Function.Surjective ρT ∧ (∀ y r, PsiCoord D.toPre y r → 0 ≤ qW W T.β (ρT y) ∧ Associated (g' r) (h T.ϖ ^ (qW W T.β (ρT y)).toNat)) ∧ ∀ a b y, MatRel W a b (ρT y) (ρT (m a b y)) := by
  intro g n hg hn hodd F W hW o' Ω _ _ _ hA S ρ hBig M U₀ EE FinalForm hAdm hEE x hx u c pr hS R _ _ _ j hR hj G _ _ gm hgm
    D A U hLB hPsi m hm T ξ hξU hsp
  set ξR : Sp R ⟶ M.Z := spMap j ≫ M.Z.fromSpecStalk x with hξR
  obtain ⟨hft, hpj⟩ := GlobalTheory.UPoinc.ClosedPt.closedPoint_cpl_residueChar o' Ω M x hx
  obtain ⟨-, p, hp, hpm⟩ := hpj R j hj
  obtain ⟨f, hf⟩ := factor_stalk M.Z x T.V ξ hsp
  obtain ⟨V', _, _, _, h, g', hc, hinj, hloc, hcomp, hirr⟩ :=
    GlobalTheory.TraitLift.exists_lift_of_isCpl (M.Z.presheaf.stalk x) R T.V j hj f
  have heq : spMap g' ≫ ξR = spMap h ≫ ξ := by
    rw [hξR, ← hf, ← Category.assoc, ← Category.assoc, ← spMap_comp', ← spMap_comp', hcomp]
  haveI : CharZero V' := (RingHom.charZero_iff hinj).1 inferInstance
  have hBV : GlobalTheory.Mum.Base V' := ⟨⟨inferInstance, inferInstance, inferInstance, hc⟩, inferInstance⟩
  have hle : nonZeroDivisors T.V ≤ (nonZeroDivisors V').comap h :=
    nonZeroDivisors_le_comap_nonZeroDivisors_of_injective h hinj
  let hK : FractionRing T.V →+* FractionRing V' := IsLocalization.map (FractionRing V') h hle
  have hKc : ∀ a, hK (algebraMap T.V _ a) = algebraMap V' _ (h a) := IsLocalization.map_eq hle
  have hjK : spMap hK ≫ jK T.V = jK V' ≫ spMap h := by
    show spMap hK ≫ spMap (algebraMap T.V (FractionRing T.V)) = spMap (algebraMap V' (FractionRing V')) ≫ spMap h
    rw [← spMap_comp', ← spMap_comp']
    congr 1
    ext a
    exact hKc a
  obtain ⟨ξ₀, hξ₀, hξ₀y⟩ := hξU
  set ξ' : Sp V' ⟶ M.Z := spMap g' ≫ ξR with hξ'
  have hξ₀' : (spMap hK ≫ ξ₀) ≫ U₀.ι = jK V' ≫ ξ' := by
    rw [Category.assoc, hξ₀, ← Category.assoc, hjK, Category.assoc, heq]
  have hsub := subset_abLocus FinalForm
  let w' : Sp V' := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum V')
  have hw'U : ξ' w' ∈ (U₀ : Set M.Z) := by
    have e1 : w' = jK V' (IsLocalRing.closedPoint (FractionRing V')) := by
      apply PrimeSpectrum.ext
      show (⊥ : Ideal V') = Ideal.comap (algebraMap V' (FractionRing V')) (IsLocalRing.closedPoint (FractionRing V')).asIdeal
      rw [Ideal.eq_bot_of_prime (IsLocalRing.closedPoint (FractionRing V')).asIdeal, ← RingHom.ker_eq_comap_bot]
      exact ((RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective V' (FractionRing V'))).symm
    rw [e1]
    show (jK V' ≫ ξ') (IsLocalRing.closedPoint (FractionRing V')) ∈ (U₀ : Set M.Z)
    rw [← hξ₀']
    show U₀.ι ((spMap hK ≫ ξ₀) (IsLocalRing.closedPoint (FractionRing V'))) ∈ (U₀ : Set M.Z)
    rw [← Scheme.Opens.range_ι]
    exact ⟨_, rfl⟩
  obtain ⟨D', A', U', hLB', hPsi'⟩ := FinalForm.unif V' inferInstance inferInstance hc ξ' ⟨w', hsub hw'U⟩
  have hG'semi : IsSemiAbelian ((Over.pullback ξ').obj FinalForm.G) := IsSemiAbelian.pullback ξ' FinalForm.G FinalForm.semi
  have hpb' := isGrpPullback_pullback FinalForm.G ξ'
  have h'' : IsGrpPullback ((Over.pullback (spMap g')).obj G) FinalForm.G ξ' (pullback.fst G.hom (spMap g') ≫ gm) :=
    (isGrpPullback_pullback G (spMap g')).comp hgm
  obtain ⟨e, he1, he2⟩ := grpPullback_iso hpb' h''
  haveI := he1
  set β : ((Over.pullback ξ').obj FinalForm.G).left ⟶ G.left := e.hom.left ≫ pullback.fst G.hom (spMap g') with hβdef
  have hβ : IsGrpPullback ((Over.pullback ξ').obj FinalForm.G) G (spMap g') β :=
    ((isGrpPullback_of_iso e).comp (isGrpPullback_pullback G (spMap g'))).congr (Category.id_comp _) rfl
  have hβgm : β ≫ gm = pullback.fst FinalForm.G.hom ξ' := by
    rw [hβdef, Category.assoc, he2]
  clear_value β
  have hGsemi : IsSemiAbelian G := by
    obtain ⟨e2, he21, -⟩ := grpPullback_iso hgm (isGrpPullback_pullback FinalForm.G ξR)
    haveI := he21
    exact GlobalTheory.isSemiAbelian_of_grpIso e2 (IsSemiAbelian.pullback ξR FinalForm.G FinalForm.semi)
  have hLBβ : LBIso U'.LG.L (U.LG.L.pull β) := by
    have h1 : LBIso (U.LG.L.pull β) (FinalForm.L.L.pull (pullback.fst FinalForm.G.hom ξ')) :=
      GlobalTheory.Ex.GenericFibre.lbIso_pull hLB β hβgm.symm
    exact LBIso.trans U'.LG.isLB (pull_isLB FinalForm.L.isLB _) (pull_isLB U.LG.isLB _) hLB' (LBIso.symm h1)
  have hWo : IsOpen (ξR ⁻¹' (U₀ : Set M.Z)) := U₀.isOpen.preimage ξR.continuous
  have hPsiWo : ∀ y, PsiUnitOn D.toPre y (ξR ⁻¹' (U₀ : Set M.Z)) := fun y j' V hV hVW =>
    hPsi y j' V hV (hVW.trans (Set.preimage_mono hsub))
  have hker : (⟨RingHom.ker g', RingHom.ker_isPrime g'⟩ : PrimeSpectrum R) ∈ ξR ⁻¹' (U₀ : Set M.Z) := by
    have e3 : (⟨RingHom.ker g', RingHom.ker_isPrime g'⟩ : PrimeSpectrum R) = spMap g' w' :=
      PrimeSpectrum.ext (RingHom.ker_eq_comap_bot g')
    show ξR _ ∈ (U₀ : Set M.Z)
    rw [e3]
    exact hw'U
  obtain ⟨ρ0, hsurj, hcoord, hequiv⟩ := GlobalTheory.T.exists_surjective_lattice_coordMap_equivariant_dvr R hR G hGsemi D A U V' hBV inferInstance
    ((Over.pullback ξ').obj FinalForm.G) hG'semi D' A' U' g' β p hp hpm _ hWo hPsiWo hker hβ hLBβ
  obtain ⟨c', pr', hS', hmat⟩ := GlobalTheory.Poinc.Eq8.PullAlong.main g n _ _ F W o' Ω S ρ u c pr hS M U₀ EE FinalForm V' hBV
    ((Over.pullback ξ').obj FinalForm.G) hG'semi D' A' U' ξ' (pullback.fst FinalForm.G.hom ξ') hpb' hLB' (spMap hK ≫ ξ₀) hξ₀'
  have hpt : (spMap hK ≫ ξ₀) ≫ FinalForm.u₀ ≫ u = spMap hK ≫ T.y := by
    rw [Category.assoc, hξ₀y]
  have key : ∀ (v : Sp (FractionRing V') ⟶ F.X), v = spMap hK ≫ T.y → ∀ c₁ pr₁, SharpBy F W A' v c₁ pr₁ →
      ∃ e : D'.toPre.X ≃+ (Fin 8 → T.D.toPre.X), (∀ y r, PsiCoord D'.toPre y r → 0 ≤ qW W T.β (e y) ∧
        Associated r (h T.ϖ ^ (qW W T.β (e y)).toNat)) ∧ ∀ (a b : Fin 8) (f : (Over.pullback ξ').obj FinalForm.G ⟶ (Over.pullback ξ').obj FinalForm.G)
        (f₁ : A'.A ⟶ A'.A) (m : D'.toPre.X →+ D'.toPre.X), IsMonHom f → MatEnd pr₁ a b f₁ →
        (Over.pullback (jK V')).map f ≫ U'.gen.hom = U'.gen.hom ≫ f₁ → EndChar U' f m → ∀ y, MatRel W a b (e y) (e (m y)) := by
    rintro v rfl c₁ pr₁ hS₁
    exact GlobalTheory.T.exists_eighthPowerTrait_lattice_equiv_localExt g n _ _ F W hW T V' hBV inferInstance _ hG'semi D' A' U' h hK hloc hKc c₁ pr₁ hS₁
  obtain ⟨e8, hord, hrel⟩ := key _ hpt c' pr' hS'
  refine ⟨V', inferInstance, inferInstance, inferInstance, h, g', e8.toAddMonoidHom.comp ρ0, hinj, hirr _ T.irr, heq,
    e8.surjective.comp hsurj, ?_, ?_⟩
  · intro y r hr
    obtain ⟨⟨r', hr', -⟩, -⟩ := GlobalTheory.PsiCoordLocal.main V' D' inferInstance (ρ0 y)
    obtain ⟨h0, has⟩ := hord (ρ0 y) r' hr'
    exact ⟨h0, (hcoord y r r' hr hr').trans has⟩
  · intro a b y
    obtain ⟨f, fR, hMO, hfR, hcomm, hEC⟩ := hm a b
    haveI : IsMonHom f := hMO.1
    let f' : (Over.pullback ξ').obj FinalForm.G ⟶ (Over.pullback ξ').obj FinalForm.G := (Over.pullback ξ').map f
    have hf'fst : f'.left ≫ pullback.fst FinalForm.G.hom ξ' = pullback.fst FinalForm.G.hom ξ' ≫ f.left := pullback.lift_fst _ _ _
    have hf' : IsMonHom f' := PullGtPf.isMonHom_of_grpPullback hpb' hpb' f f' hf'fst
    have hf'β : f'.left ≫ β = β ≫ fR.left := by
      apply hgm.1.hom_ext
      · calc (f'.left ≫ β) ≫ gm = f'.left ≫ (β ≫ gm) := Category.assoc _ _ _
          _ = pullback.fst FinalForm.G.hom ξ' ≫ f.left := by rw [hβgm, hf'fst]
          _ = (β ≫ gm) ≫ f.left := by rw [hβgm]
          _ = (β ≫ fR.left) ≫ gm := by rw [Category.assoc, Category.assoc, hcomm]
      · calc (f'.left ≫ β) ≫ G.hom = f'.left ≫ (β ≫ G.hom) := Category.assoc _ _ _
          _ = ((Over.pullback ξ').obj FinalForm.G).hom ≫ spMap g' := by rw [hβ.1.w, ← Category.assoc, Over.w f']
          _ = β ≫ G.hom := hβ.1.w.symm
          _ = (β ≫ fR.left) ≫ G.hom := by rw [Category.assoc, Over.w fR]
    obtain ⟨m', hm'⟩ := endChar_exists_of_isMonHom V' hBV _ hG'semi D' A' U' f' hf'
    have hq := hequiv fR f' hfR hf' hf'β (m a b) m' hEC hm' y
    obtain ⟨f₁, hf₁, hf₁c⟩ := hmat a b f f' hMO hf'fst
    have hr := hrel a b f' f₁ m' hf' hf₁ hf₁c hm' (ρ0 y)
    simpa [hq] using hr

end GlobalTheory.Poinc.Eq8.TraitOne
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.isPreconnected_closedFibre_proper_completeLocalNoetherian : ∀ (A : Type) [CommRing A] [IsNoetherianRing A] [IsLocalRing A], IsAdicComplete (maximalIdeal A) A → ∀ (X : Scheme.{0}) (f : X ⟶ Sp A), IsProper f → PreconnectedSpace X → _root_.IsPreconnected {x : X | f x = closedPoint A} := by
  first | exact @GlobalTheory.ClosedFibreConn.isPreconnected_closedFibre | exact GlobalTheory.ClosedFibreConn.isPreconnected_closedFibre | (intros; apply GlobalTheory.ClosedFibreConn.isPreconnected_closedFibre <;> assumption)
end
