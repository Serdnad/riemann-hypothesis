module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsUniqueLbIsoPullEqOfCoheightLeOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2336
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle043
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle047
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2328
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.ValuativeCriterion
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle021
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle057
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCoprimeOfNatCast
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRightActFunPull
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnitaryWeightExponentVectorSignatureWeightMuZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1092
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2325
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle002

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

namespace GlobalTheory

theorem germToFunctionField_mem_range_stalk_of_mul_pull : ∀ (k : Type) [CommRing k] (Y X : Scheme.{0}) [IsIntegral Y] [IsIntegral X]
    (p : Y ⟶ Sp k) (σ : X ⟶ Y) (U : Y.Opens) [IsIso (σ ∣_ U)] [Nonempty U] (L : LB Y) (P N : LB X)
    (C : ProdChart P (L.pull σ) N) (J : H0 (σ ≫ p) P ⊤) (g : H0 (σ ≫ p) N ⊤) (s : H0 p L U),
    C.mul (H0.restr le_top J) (H0.pull σ le_rfl s) = H0.restr le_top g → ∀ x : X,
      Function.Bijective (σ.stalkMap x).hom → (∀ (a : P.ι) (ha : x ∈ P.U a), IsUnit (H0.germ a x (memTop x) ha J)) →
      ∀ (i : L.ι) (hi : σ x ∈ L.U i) [Nonempty (U ⊓ L.U i : Y.Opens)],
        Y.germToFunctionField (U ⊓ L.U i) (s.loc i) ∈ (algebraMap (Y.presheaf.stalk (σ x)) Y.functionField).range := by
  intro k _ Y X _ _ p σ U _ _ L P N C J g s hrel x hbij hJ i hi _
  obtain ⟨t, ha, hb, hc⟩ := C.cover x
  have hjx : σ x ∈ L.U (C.b t PUnit.unit) := mem_pull.1 hb
  have hξx : genericPoint X ⤳ x := (genericPoint_spec X).specializes trivial
  have hne : Nonempty (σ ⁻¹ᵁ U) := by
    obtain ⟨⟨y, hy⟩⟩ := ‹Nonempty U›
    obtain ⟨z, -⟩ := (σ ∣_ U).surjective ⟨y, hy⟩
    exact ⟨z⟩
  have hξU : genericPoint X ∈ σ ⁻¹ᵁ U := genericPoint_mem_opens _
  have hσξη : σ (genericPoint X) ⤳ genericPoint Y := by
    obtain ⟨z, hz⟩ := (σ ∣_ U).surjective ⟨genericPoint Y, genericPoint_mem_opens U⟩
    have e : σ z.1 = genericPoint Y := (morphismRestrict_base_coe σ U z).symm.trans (congrArg Subtype.val hz)
    rw [← e]
    exact σ.base.hom.map_specializes ((genericPoint_spec X).specializes trivial)
  have hσξ : σ (genericPoint X) ∈ U ⊓ L.U (C.b t PUnit.unit) :=
    ⟨hξU, (σ.base.hom.map_specializes hξx).mem_open (L.U _).isOpen hjx⟩
  have haξ := hξx.mem_open (P.U (C.a t)).isOpen ha
  have hbξ := hξx.mem_open ((L.pull σ).U (C.b t)).isOpen hb
  have hcξ := hξx.mem_open (N.U (C.c t)).isOpen hc
  have e1 := congrArg (H0.germ (C.c t) (genericPoint X) hξU hcξ) hrel
  rw [C.germ_mul _ _ t _ hξU haξ hbξ hcξ, H0.germ_restr, H0.germ_restr, H0.germ_pull] at e1
  have hsp (B : LB X) (f : H0 (σ ≫ p) B ⊤) (a : B.ι) (hx : x ∈ B.U a) (hξ : genericPoint X ∈ B.U a) :
      H0.germ a (genericPoint X) (memTop _) hξ f =
        X.presheaf.stalkSpecializes hξx (H0.germ a x (memTop x) hx f) := by
    rw [H0.germ_apply, H0.germ_apply]
    exact (X.presheaf.germ_stalkSpecializes_apply _ hξx _).symm
  have hJu := hJ (C.a t) ha
  obtain ⟨h, hh⟩ := hbij.2 (H0.germ (C.c t) x (memTop x) hc g * ↑hJu.unit⁻¹)
  have : Nonempty (L.U (C.b t PUnit.unit)) := ⟨⟨σ x, hjx⟩⟩
  have := nonempty_inf_of_isIntegral U (L.U (C.b t PUnit.unit))
  refine germToFunctionField_mem_range_stalk_of_secOn (LB.coord_mem s) hi hjx ⟨h, ?_⟩
  let φ : Y.functionField →+* X.presheaf.stalk (genericPoint X) :=
    (σ.stalkMap (genericPoint X)).hom.comp (Y.presheaf.stalkSpecializes hσξη).hom
  refine φ.injective ?_
  have eA : φ (algebraMap _ _ h) = X.presheaf.stalkSpecializes hξx (σ.stalkMap x h) := by
    change (σ.stalkMap _).hom ((Y.presheaf.stalkSpecializes ((genericPoint_spec Y).specializes trivial) ≫
      Y.presheaf.stalkSpecializes hσξη).hom h) = _
    rw [TopCat.Presheaf.stalkSpecializes_comp]
    exact Scheme.Hom.stalkSpecializes_stalkMap_apply σ _ _ hξx h
  have eB : φ (Y.germToFunctionField _ (LB.coord s (C.b t PUnit.unit))) =
      (σ.stalkMap (genericPoint X)).hom (H0.germ (C.b t PUnit.unit) (σ (genericPoint X)) hσξ.1 hσξ.2 s) := by
    change (σ.stalkMap _).hom (Y.presheaf.stalkSpecializes hσξη
      (Y.presheaf.germ _ (genericPoint Y) _ (LB.coord s _))) = _
    rw [Y.presheaf.germ_stalkSpecializes_apply _ hσξη]
    rfl
  rw [eA, eB, hh]
  rw [hsp P J (C.a t) ha haξ, hsp N g (C.c t) hc hcξ] at e1
  have hu : IsUnit (X.presheaf.stalkSpecializes hξx (H0.germ (C.a t) x (memTop x) ha J)) := hJu.map _
  apply hu.mul_left_cancel
  rw [e1, ← map_mul]
  exact congrArg _ (by rw [mul_left_comm, hJu.mul_val_inv, mul_one])

end GlobalTheory
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompHS.Modif

theorem exists_bijective_stalkMap_of_dvr : ∀ (F : Type) [Field F] (Y : Scheme.{0}) [IsIntegral Y] (p : Y ⟶ Sp F)
    (U : Y.Opens) (d : ℕ) (M : Modif p U d), IsProjOver p → (U : Set Y).Nonempty → ∀ y : Y,
      IsDiscreteValuationRing (Y.presheaf.stalk y) →
      ∃ x : M.X, M.σ x = y ∧ Function.Bijective (M.σ.stalkMap x).hom := by
  intro F _ Y _ p U d M hp hU y hR
  have hprop : ∀ {Z : Scheme.{0}} {s : Z ⟶ Sp F}, IsProjOver s → IsProper s := by
    intro Z s hs
    obtain ⟨N, c, hc, rfl⟩ := hs
    have := isProper_str F N
    infer_instance
  haveI : IsProper p := hprop hp
  haveI : IsProper (M.σ ≫ p) := hprop M.proj
  haveI : IsProper M.σ := IsProper.of_comp M.σ p
  haveI : Nonempty M.X := by
    haveI := M.iso
    obtain ⟨u, hu⟩ := hU
    obtain ⟨z, -⟩ := (M.σ ∣_ U).surjective ⟨u, hu⟩
    exact ⟨z.1⟩
  haveI : IsIntegral M.X := HSApp.ValCrit.isIntegral_X M
  let R := Y.presheaf.stalk y
  haveI : IsDomain R := inferInstanceAs (IsDomain (Y.presheaf.stalk y))
  haveI : IsDiscreteValuationRing R := hR
  let η := genericPoint Y
  have hηU : η ∈ U := ((genericPoint_spec Y).mem_open_set_iff U.isOpen).2 (by simpa using hU)
  let i₂ : Spec R ⟶ Y := Y.fromSpecStalk y

  have hgen : ∀ w : Spec R, (∀ u, w ⤳ u) → i₂ w = η := by
    intro w hw
    have hq : η ∈ Set.range i₂ := by
      rw [Scheme.range_fromSpecStalk]; exact (genericPoint_spec Y).specializes (Set.mem_univ y)
    obtain ⟨q, hq⟩ := hq
    have h1 : i₂ w ⤳ η := hq ▸ (hw q).map i₂.continuous
    exact (h1.antisymm ((genericPoint_spec Y).specializes (Set.mem_univ _))).eq
  let K := FractionRing R
  let j : Spec (.of K) ⟶ Spec R := Spec.map (CommRingCat.ofHom (algebraMap R K))
  have hj : ∀ s : Spec (.of K), ∀ u : Spec R, j s ⤳ u := by
    intro s u
    refine (PrimeSpectrum.le_iff_specializes _ _).1 ?_
    change Ideal.comap (algebraMap R K) s.asIdeal ≤ u.asIdeal
    haveI : s.asIdeal.IsPrime := s.isPrime
    rw [Ideal.eq_bot_of_prime s.asIdeal, ← RingHom.ker_eq_comap_bot,
      (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R K)]
    exact bot_le
  have hKU : ⊤ ≤ (j ≫ i₂) ⁻¹ᵁ U := fun s _ => by
    show i₂ (j s) ∈ U
    rw [hgen (j s) (hj s)]
    exact hηU
  obtain ⟨i₁, hi₁, -⟩ := M.existsUnique_lift (j ≫ i₂) hKU
  have hE : ValuativeCriterion.Existence M.σ := by
    have h : UniversallyClosed M.σ := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at h
    exact h.1
  obtain ⟨⟨L⟩⟩ := hE (@ValuativeCommSq.mk _ _ M.σ R inferInstance ‹IsDomain R› inferInstance K inferInstance
    inferInstance inferInstance i₁ i₂ ⟨hi₁⟩)
  let c := IsLocalRing.closedPoint R
  have hfr : L.l ≫ M.σ = i₂ := L.fac_right
  refine ⟨L.l c, ?_, ?_⟩
  · show (L.l ≫ M.σ) c = y
    rw [hfr]
    exact Scheme.fromSpecStalk_closedPoint

  have key : ∀ g : Spec R ⟶ Y, g = i₂ → Function.Bijective (g.stalkMap c).hom := by
    rintro _ rfl
    have e : i₂.stalkMap c ≫ (stalkClosedPointIso R).hom = (Y.presheaf.stalkCongr _).hom :=
      Scheme.stalkClosedPointTo_fromSpecStalk y
    haveI : IsIso (i₂.stalkMap c ≫ (stalkClosedPointIso R).hom) := by rw [e]; infer_instance
    haveI : IsIso (i₂.stalkMap c) := IsIso.of_isIso_comp_right _ (stalkClosedPointIso R).hom
    exact ConcreteCategory.bijective_of_isIso _
  have hb := key _ hfr
  have e₀ := Scheme.Hom.stalkMap_comp L.l M.σ c
  have hb2 : Function.Bijective (M.σ.stalkMap (L.l c) ≫ L.l.stalkMap c).hom := by rw [← e₀]; exact hb
  replace hb : Function.Bijective ((L.l.stalkMap c).hom ∘ (M.σ.stalkMap (L.l c)).hom) := hb2

  let t := genericPoint (Spec R)
  have ht : ∀ u : Spec R, t ⤳ u := fun u => (genericPoint_spec (Spec R)).specializes (Set.mem_univ u)
  have hσt : M.σ (L.l t) = η := by
    show (L.l ≫ M.σ) t = η
    rw [hfr]; exact hgen t ht
  have hσg : M.σ (genericPoint M.X) = η := by
    have h1 : M.σ (genericPoint M.X) ⤳ η :=
      hσt ▸ ((genericPoint_spec M.X).specializes (Set.mem_univ (L.l t))).map M.σ.continuous
    exact (h1.antisymm ((genericPoint_spec Y).specializes (Set.mem_univ _))).eq
  have hlt : L.l t = genericPoint M.X := by
    haveI := M.iso
    have m1 : L.l t ∈ M.opn := show M.σ (L.l t) ∈ U from hσt ▸ hηU
    have m2 : genericPoint M.X ∈ M.opn := show M.σ (genericPoint M.X) ∈ U from hσg ▸ hηU
    have e : (M.σ ∣_ U) ⟨L.l t, m1⟩ = (M.σ ∣_ U) ⟨genericPoint M.X, m2⟩ :=
      Subtype.ext ((morphismRestrict_base_coe M.σ U ⟨L.l t, m1⟩).trans
        ((hσt.trans hσg.symm).trans (morphismRestrict_base_coe M.σ U ⟨genericPoint M.X, m2⟩).symm))
    exact congrArg Subtype.val ((M.σ ∣_ U).isOpenEmbedding.injective e)

  have hBinj : Function.Injective (L.l.stalkMap c).hom := by
    have hsp : t ⤳ c := ht c
    have nat := Scheme.Hom.stalkSpecializes_stalkMap L.l t c hsp
    have hf : IsField (M.X.presheaf.stalk (L.l t)) := by
      rw [hlt]; exact Field.toIsField M.X.functionField
    have i1 : Function.Injective (L.l.stalkMap t).hom := by
      letI := hf.toField
      exact RingHom.injective _
    have i2 : Function.Injective (M.X.presheaf.stalkSpecializes (hsp.map L.l.continuous)).hom := by
      refine (injective_iff_map_eq_zero _).2 fun a ha => ?_
      obtain ⟨V, hV, f, rfl⟩ := M.X.presheaf.germ_exist a
      have e := congrArg (fun φ => φ.hom f) (M.X.presheaf.germ_stalkSpecializes hV (hsp.map L.l.continuous))
      simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
      rw [e] at ha
      rw [germ_injective_of_isIntegral M.X _ _ (ha.trans (map_zero _).symm), map_zero]
    have i3 : Function.Injective (((Spec R).presheaf.stalkSpecializes hsp).hom ∘ (L.l.stalkMap c).hom) := by
      have h4 : Function.Injective (M.X.presheaf.stalkSpecializes (hsp.map L.l.continuous) ≫ L.l.stalkMap t).hom :=
        i1.comp i2
      rw [nat] at h4
      exact h4
    exact i3.of_comp
  refine ⟨hb.1.of_comp, fun a => ?_⟩
  obtain ⟨b, hb'⟩ := hb.2 ((L.l.stalkMap c).hom a)
  exact ⟨b, hBinj hb'⟩

end GlobalTheory.CompHS.Modif
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

namespace GlobalTheory.OrbitSep

theorem val_ofSec_ne_zero {F : Type} [Field F] {X : Scheme.{0}} (p : X ⟶ Sp F) {B : LB X} (θ : B.Sec) (z : Sp ℂ ⟶ X)
    (k : B.ι) (hk : ⊤ ≤ z ⁻¹ᵁ B.U k) (hz : ∀ s, z s ∈ nonzeroLocus θ) :
    H0.val z k le_top hk (H0.ofSec p ⊤ θ) ≠ 0 := by
  refine (H0.val_ofSec z k le_top hk θ).trans_ne ?_
  have h : ⊤ ≤ z ⁻¹ᵁ X.basicOpen (θ.f k) := fun s hs =>
    (X.mem_basicOpen _ _ (hk hs)).2 ((isUnit_ger_iff θ (hk hs)).2 (hz s))
  rw [← TangentOrigin.evalPt_res z (X.basicOpen_le _) hk h]
  exact ((X.toRingedSpace.isUnit_res_basicOpen (θ.f k)).map _).ne_zero

theorem exists_chart_pt {X : Scheme.{0}} {B : LB X} (hB : B.IsLB) (z : Sp ℂ ⟶ X) : ∃ k, ⊤ ≤ z ⁻¹ᵁ B.U k := by
  obtain ⟨k, hk⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_chart hB (z (IsLocalRing.closedPoint ℂ))
  refine ⟨k, fun s _ => ?_⟩
  obtain rfl : s = IsLocalRing.closedPoint ℂ := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
  exact hk

theorem cls_nsmul {Y : Scheme.{0}} {Λ : Type} [AddCommGroup Λ] {B : Λ → LB Y} (C : Common B) (n : ℕ) (a : Λ) :
    cls (B (n • a)) (C.isLB (n • a)) = n • cls (B a) (C.isLB a) := by
  induction n with
  | zero =>
    have h := GlobalTheory.HSApp.cls_common_add C 0 0
    simp only [add_zero] at h
    simp only [zero_nsmul]
    exact left_eq_add.1 h
  | succ n ih => rw [succ_nsmul, GlobalTheory.HSApp.cls_common_add C, ih, succ_nsmul]


end GlobalTheory.OrbitSep

namespace GlobalTheory.OrbitSep

open Formalism.MainNotions Formalism.L2.Theta GlobalTheory.DegVal GlobalTheory.DegCmp GlobalTheory.BadCount

end GlobalTheory.OrbitSep
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic
open GlobalTheory.ThickeningDetermines (secIdeal)
open scoped TensorProduct
open NumberField Formalism.L2.Pj Formalism.BasicNotions GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.HSApp
open GlobalTheory.AllWt (wtOf cuspOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)

theorem _root_.GlobalTheory.T.modification_globalSectionsDim_pull_eq : ∀ (k : Type) [Field k] (Y : Scheme.{0}) [IsIntegral Y] (p : Y ⟶ Sp k) (U : Y.Opens) (D : ℕ), SmoothOfRelativeDimension D p → IsProjOver p → ∀ (M : Modif p U D) [IsIntegral M.X] (B : LB Y), B.IsLB → letI := algebraΓOfHom p; letI := algebraΓOfHom M.str; lbH0 k (B.pull M.σ) = lbH0 k B := by
  first | exact @GlobalTheory.ModifSections.modification_lineBundleGlobalSectionsDim_pull_eq | exact GlobalTheory.ModifSections.modification_lineBundleGlobalSectionsDim_pull_eq | (intros; apply GlobalTheory.ModifSections.modification_lineBundleGlobalSectionsDim_pull_eq <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

namespace GlobalTheory

theorem isIntegral_of_nonempty_modif : ∀ (F : Type) [Field F] (Y : Scheme.{0}) [IsIntegral Y] (p : Y ⟶ Sp F) (U : Y.Opens) (d : ℕ)
    (M : Modif p U d), (U : Set Y).Nonempty → IsIntegral M.X := by
  intro F _ Y _ p U d M hU
  have hUi : IsIrreducible (U : Set Y) :=
    ⟨hU, (IrreducibleSpace.isIrreducible_univ Y).isPreirreducible.open_subset U.isOpen (Set.subset_univ _)⟩
  have := M.iso
  let g : (U : Scheme) ⟶ M.X := inv (M.σ ∣_ U) ≫ (M.σ ⁻¹ᵁ U).ι
  have hrange : Set.range g.base = ((M.σ ⁻¹ᵁ U : M.X.Opens) : Set M.X) := by
    have hs : Function.Surjective (inv (M.σ ∣_ U)).base := (inv (M.σ ∣_ U)).surjective
    simp only [g, Scheme.Hom.comp_base, TopCat.hom_comp, ContinuousMap.coe_comp, Set.range_comp, hs.range_eq,
      Set.image_univ]
    exact Scheme.Opens.range_ι _
  have hopn : IsIrreducible ((M.σ ⁻¹ᵁ U : M.X.Opens) : Set M.X) := by
    rw [← hrange, ← Set.image_univ]
    have : IrreducibleSpace (U : Scheme) := Subtype.irreducibleSpace hUi
    exact (IrreducibleSpace.isIrreducible_univ (U : Scheme)).image _ g.base.hom.continuous.continuousOn
  have hcl : IsIrreducible (Set.univ : Set M.X) := by
    rw [← M.dense.closure_eq]; exact hopn.closure
  have : IrreducibleSpace M.X := irreducibleSpace_def _ |>.mpr hcl
  have : Smooth M.str := SmoothOfRelativeDimension.smooth d _
  exact isIntegral_of_smooth_field M.str

end GlobalTheory
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR.Cx
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim

namespace GlobalTheory.BigTop.Fun

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

theorem out_sum_tw {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (s : Bool) {n : ℕ}
    (f : E →ₗ[ℂ] ℂ) (φ : (Fin n → ℂ) →ₗ[ℂ] Tw s E) (z : Fin n → ℂ) :
    f (Tw.out (φ z)) = ∑ k, cj s (z k) * f (Tw.out (φ (Pi.single k 1))) := by
  let o : Tw s E →+ E := ⟨⟨Tw.out, rfl⟩, Tw.out_add⟩
  have e : z = ∑ k, z k • (Pi.single k 1 : Fin n → ℂ) := by
    conv_lhs => rw [← Finset.univ_sum_single z]
    refine Finset.sum_congr rfl fun k _ => ?_
    ext j; by_cases hj : j = k <;> simp [hj]

  conv_lhs => rw [e, map_sum]

  rw [show Tw.out (∑ k, φ (z k • Pi.single k 1)) = ∑ k, Tw.out (φ (z k • (Pi.single k 1 : Fin n → ℂ))) from
  map_sum o (fun k => φ (z k • (Pi.single k 1 : Fin n → ℂ))) Finset.univ, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, Tw.out_smul, map_smul, smul_eq_mul]

theorem twist_conj_base_embedding_eq (p : PtAt ex Csz) (a : D.what₂.LL) :
    cj (twAt D.what₂.embLL p.P.A3.A.v0) (p.P.A3.fam3.base3.v0.embedding a) = D.what₂.embLL a := by
  rw [show p.P.A3.fam3.base3.v0 = p.P.A3.A.v0 from rfl, emb_eq D.what₂.embLL p.P.A3.A.v0 a, cj_cj, sgAt_mk _ p.R.hv0]

theorem mul_eq_one_of_covolume_identity (κ zt z0 ct c0 v : ℂ) (hκ : κ ≠ 0) (hzt : zt ≠ 0) (hz0 : z0 ≠ 0) (hct : ct ≠ 0) (hc0 : c0 ≠ 0) :
    κ⁻¹ * z0 * c0 * (κ * v / (zt * ct)) = (zt / z0 * (ct / c0))⁻¹ * v := by
  field_simp


end GlobalTheory.BigTop.Fun
end
end

section

open NumberField

namespace GlobalTheory.CovTop

open GlobalTheory.BigTop Formalism.IndefR.FWT

variable {D : Formalism.BasicNotions.D7} {L : Formalism.BasicNotions.SizeData₂ D} {hT : Formalism.BasicNotions.GatTies D} {Gi : Formalism.MainNotions.G.Inst D L}
  {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y0 : Formalism.BasicNotions.DivX D} {cX : Formalism.BasicNotions.ExtraC}
  {ex : Formalism.BasicNotions.Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ}

theorem rho_mem_WK (p : PtAt ex Csz) (i : Fin D.R.m) (g) (f) (hf : f ∈ (p.R.toRealDat.FW i).WK) :
    (p.R.toRealDat.FW i).ρ g f ∈ (p.R.toRealDat.FW i).WK := by
  by_cases hk : ActKeeps (κ := p.κ) p.O i
  · obtain ⟨c, hc⟩ := (p.fw.e i).surjective ⟨f, hf⟩
    obtain ⟨_, h2⟩ := (p.rhoGeo i).1 hk g c
    rw [hc] at h2
    rw [← h2]
    exact Subtype.property _
  · rw [(p.rhoGeo i).2 hk g]
    exact hf

end GlobalTheory.CovTop
end

section

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.thetaKernel_oneClass_eq_classicalShortSeries : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), VStd D i → ∀ (H : Geo.Tor.Host D.host.E) (Dw : Datum H) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)), LatEmb (Wc D i) ι → LatIsom (Wc D i) Dw.EF ι → ∃ δ : ℤˣ, ∀ (t : T0) (l₂ : Geo.Tor.Level H) (φ : (Fin (Vc D i).rank → LevQc Dw l₂) → ℂ), PhiIs R i (RingHom.id ℂ) t ι (Mfr l₂ • ⊤) φ → (∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → l₂.Mb ≤ PP.asIdeal ∧ ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → (H.rt : D.host.E) = D.host.sqrtMinusD → ∀ (g q0 : ℕ) (X : Data D.host.E D.R.r) (hq : X.p0 + q0 = D.R.r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin D.R.r) (x₀ : Frame X.Ψ D.R.r) (vr : Harm.Var X.Ψ q0 X.p0 (Fin (Vc D i).rank) ≃ FVar D (Wc D i).rank (Vc D i).rank), IsMod (Wc D i) (rank_Wc i) X → IsSympl X bas → IsONFr X x₀ → IsInvOf (Wc D i) (rank_Wc i) X x₀ (cart (R.MW i (sg0 D A))) → IsBasOf (Wc D i) (rank_Wc i) X hq x₀ (onb (R.MW i (sg0 D A))) → IsVarOf (Vc D i) (Wc D i) X q0 vr → ∀ (bad N : ℕ) (h : GA D (Vc D i)) (k : GA D (Wc D i)) (Λ : GenLat D.host.E (Vc D i).rank) (mk : Dw.La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E)) (e : AE D) (Ps : Finset (Formalism.L2.DIV.Pl D.host.E)) (y : (AE D)ˣ), (∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → ((bad : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → IsIdemSum e Ps → (∀ PP ∈ Ps, ((bad : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → h ∈ GfC (Vc D i) → SuppAt e (Vc D i) h → IsDetAt e (Vc D i) h y → (∀ v, v ∈ Λ.La ↔ (fun j => star (v j)) ∈ Bridge.hLat (Vc D i) (fin (Vc D i) h)) → Λ.TrivAt l₂.M → Λ.LevOK N l₂.M → MarkAd l₂ (Wc D i) (rank_Wc i) ι k mk → ∀ Y : (Fin (Vc D i).rank → LevQ Dw l₂) → Matrix (Fin (Vc D i).rank) (Fin D.R.r) D.host.E, IsRoots l₂ (latR (rank_Wc i) (latG (Wc D i) k)) mk N Y → ∀ (v : TF (Vc D i).rank g) (a : ℂ), IsVac X bas (H.w0 : D.host.E) (tens (stdL D.host.E (Vc D i).rank) (latR (rank_Wc i) (latG (Wc D i) k))) v → Reads R.θ (Vc D i) (Wc D i) (rank_Wc i) X bas idx (R.ωP i t (1, k) (R.vacP i)) (a • v) (frMove R.θ (Wc D i) (rank_Wc i) X k x₀) → ∀ (P : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin (Vc D i).rank)) (d : ℕ), P.IsHomogeneous d → thetaKO (R.ωP i t) h k (pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (fun _ => 1) (onb (R.MW i (sg0 D A))) (R.vP i t) (MvPolynomial.rename vr P)) = ((δ : ℤ) : ℂ) ^ d * (-1) ^ d * ((Real.sqrt (2 * Real.pi * xiR D) : ℝ) : ℂ)⁻¹ ^ d * a * ((((Lift.chrTh (R.toLevCh.mu t) R.eta ((i : ℕ) + 1)).2 y : Circle) : ℂ)⁻¹ * (Real.sqrt ((((Λ.La ⊓ Formalism.L2.Pj.stdLat D.host.E (Vc D i).rank).toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup).index : ℝ) ^ D.R.r) : ℂ)) * ((Nat.card (Fin (Vc D i).rank → LevQ Dw l₂) : ℂ))⁻¹ * thP X hq bas idx (gphi X bas (H.w0 : D.host.E) Λ.La (latR (rank_Wc i) (latG (Wc D i) k)) v (hatC l₂ φ) Y) P (frMove R.θ (Wc D i) (rank_Wc i) X k x₀) := by
  first | exact @GlobalTheory.AdTh.ShortSeriesCore.thetaKO_eq_short_series_core | exact GlobalTheory.AdTh.ShortSeriesCore.thetaKO_eq_short_series_core | (intros; apply GlobalTheory.AdTh.ShortSeriesCore.thetaKO_eq_short_series_core <;> assumption)
end
