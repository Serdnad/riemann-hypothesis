module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle004
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle023
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle087
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsogenyOfNcard
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle191
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle116
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle060
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsPrimitiveRootUnitOnIff
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle067
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle002
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle007
public import Development.AbelianVarietyTheory.Definitions.Degenerations.MorAlgSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle118
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle012
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle192
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle091
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle041
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle195
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle105
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle193
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle194
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle176
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle084
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle184
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle166
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SectionValueAtTorsionPointEqSumTerms
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValuationsTorusPointsFramesFamilyTerms
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
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.BOfNsmulLeft
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen

@[expose] public section

section

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.FiniteData

def Pair {S : Scheme.{0}} (A B : Over S) [GrpObj A] [GrpObj B] (m : ℕ) : Prop :=
  ∃ (i : A ⟶ B) (r : B ⟶ A), IsMonHom i ∧ IsMonHom r ∧ r ≫ i = 𝟙 B ^ m

theorem Pair.of_iso {S : Scheme.{0}} {A B A' B' : Over S} [GrpObj A] [GrpObj B] [GrpObj A'] [GrpObj B'] {m : ℕ}
    (a : A' ≅ A) (b : B' ≅ B) [IsMonHom a.hom] [IsMonHom b.hom] (h : Pair A B m) : Pair A' B' m := by
  obtain ⟨i, r, hi, hr, e⟩ := h
  refine ⟨a.hom ≫ i ≫ b.inv, b.hom ≫ r ≫ a.inv, inferInstance, inferInstance, ?_⟩
  have : (b.hom ≫ r ≫ a.inv) ≫ a.hom ≫ i ≫ b.inv = b.hom ≫ (r ≫ i) ≫ b.inv := by simp
  rw [this, e, MonObj.pow_comp, MonObj.comp_pow]
  simp

theorem isMonHom_symm {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] (a : A ≅ B) [IsMonHom a.hom] :
    IsMonHom a.symm.hom := inferInstanceAs (IsMonHom a.inv)

theorem isMonHom_refl {S : Scheme.{0}} (A : Over S) [GrpObj A] : IsMonHom (Iso.refl A).hom :=
  inferInstanceAs (IsMonHom (𝟙 A))

attribute [local instance] isMonHom_symm isMonHom_refl

theorem relDim_pullback {S S' : Scheme.{0}} (f : S' ⟶ S) (X : Over S) {g : ℕ} (h : SmoothOfRelativeDimension g X.hom) :
    SmoothOfRelativeDimension g ((Over.pullback f).obj X).hom :=
  (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback (IsPullback.of_hasPullback _ _) h

theorem Pair.pullback {S S' : Scheme.{0}} (f : S' ⟶ S) {A B : Over S} [GrpObj A] [GrpObj B] {m : ℕ}
    (h : Pair A B m) : Pair ((Over.pullback f).obj A) ((Over.pullback f).obj B) m := by
  obtain ⟨i, r, hi, hr, e⟩ := h
  refine ⟨(Over.pullback f).map i, (Over.pullback f).map r, inferInstance, inferInstance, ?_⟩
  rw [← Functor.map_comp, e, ← CategoryTheory.Functor.map_id]
  exact map_pow ((Over.pullback f).homMonoidHom) _ _

theorem spMap_comp {R₁ R₂ R₃ : Type} [CommRing R₁] [CommRing R₂] [CommRing R₃] (f : R₁ →+* R₂) (g : R₂ →+* R₃)
    (h : R₁ →+* R₃) (e : ∀ x, g (f x) = h x) : spMap g ≫ spMap f = spMap h := by
  obtain rfl : h = g.comp f := RingHom.ext fun x => (e x).symm
  rw [← Spec.map_comp]; rfl

theorem Pair.descend {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] [Algebra.IsAlgebraic F Ω]
    {A B : Over (Sp F)} {A' B' : Over (Sp Ω)} [GrpObj A] [GrpObj B] [GrpObj A'] [GrpObj B']
    (hA : IsAbelianScheme A) (hB : IsAbelianScheme B) {m : ℕ} {φ : A'.left ⟶ A.left} {ψ : B'.left ⟶ B.left}
    (pA : IsGrpPullback A' A (spMap (algebraMap F Ω)) φ) (pB : IsGrpPullback B' B (spMap (algebraMap F Ω)) ψ)
    (h : Pair A' B' m) : ∃ (L : IntermediateField F Ω), FiniteDimensional F L ∧
      ∀ (L' : IntermediateField F Ω), L ≤ L' → ∀ (A'' B'' : Over (Sp L')) [GrpObj A''] [GrpObj B'']
        (φ' : A''.left ⟶ A.left) (ψ' : B''.left ⟶ B.left), IsGrpPullback A'' A (spMap (algebraMap F L')) φ' →
        IsGrpPullback B'' B (spMap (algebraMap F L')) ψ' → Pair A'' B'' m := by
  obtain ⟨a, ha, -⟩ := grpPullback_iso (isGrpPullback_pullback A _) pA
  obtain ⟨b, hb, -⟩ := grpPullback_iso (isGrpPullback_pullback B _) pB
  obtain ⟨i, r, hi, hr, e⟩ := h.of_iso a b
  obtain ⟨L, hL, i', r', hi', hr', e'⟩ := GlobalTheory.homPair_descends_to_finite F Ω A B hA hB i r hi hr
  refine ⟨L, hL, fun L' hle A'' B'' _ _ φ' ψ' qA qB => ?_⟩
  have h₁ : Pair ((Over.pullback (spMap (algebraMap F L))).obj A) ((Over.pullback (spMap (algebraMap F L))).obj B) m :=
    ⟨i', r', hi', hr', (e' m).2 e⟩
  let τ : L →+* L' := (IntermediateField.inclusion hle).toRingHom
  have hτ : spMap τ ≫ spMap (algebraMap F L) = spMap (algebraMap F L') := spMap_comp _ _ _ fun x => rfl
  obtain ⟨a', ha', -⟩ := grpPullback_iso qA
    (((isGrpPullback_pullback _ (spMap τ)).comp (isGrpPullback_pullback A _)).congr hτ rfl)
  obtain ⟨b', hb', -⟩ := grpPullback_iso qB
    (((isGrpPullback_pullback _ (spMap τ)).comp (isGrpPullback_pullback B _)).congr hτ rfl)
  exact (h₁.pullback (spMap τ)).of_iso a' b'

theorem finite_of_fg {o Ω₀ : Type} [Field o] [Field Ω₀] [Algebra o Ω₀] [Algebra.IsAlgebraic o Ω₀] (R₀ : Subalgebra o Ω₀)
    (hfg : R₀.FG) (hfr : ∀ x : Ω₀, ∃ a ∈ R₀, ∃ b ∈ R₀, x = a / b) : FiniteDimensional o Ω₀ := by
  have ht : R₀ = ⊤ := by
    refine eq_top_iff.2 fun x _ => ?_
    obtain ⟨a, ha, b, hb, rfl⟩ := hfr x
    rw [div_eq_mul_inv]
    exact R₀.mul_mem ha (R₀.inv_mem_of_algebraic (x := ⟨b, hb⟩) (Algebra.IsAlgebraic.isAlgebraic _))
  have : Algebra.FiniteType o Ω₀ := ⟨ht ▸ hfg⟩
  exact Algebra.IsIntegral.finite

theorem exists_pol_baseChange {S S' : Scheme.{0}} (f : S' ⟶ S) (P : Out.PolAV S)
    (h : letI := P.isAb.comm; GlobalTheory.ZH.HypS P.A P.L) :
    ∃ (P' : Out.PolAV S') (φ : P'.A.left ⟶ P.A.left), IsGrpPullback P'.A P.A f φ ∧
      (letI := P'.isAb.comm; GlobalTheory.ZH.HypS P'.A P'.L) := by
  obtain ⟨P', φ, hφ, hg, hm, t, ht⟩ := polBaseChange_holds S S' f P
  have gp : IsGrpPullback P'.A P.A f φ := ⟨hφ, fun T x y x₀ y₀ hx hy => by
    rw [(Over.OverMorphism.ext hx : x₀ = Out.toBase hφ.w x), (Over.OverMorphism.ext hy : y₀ = Out.toBase hφ.w y), ← hm]
    rfl⟩
  letI := P.isAb.comm
  letI := P'.isAb.comm
  exact ⟨P', φ, gp, GlobalTheory.SymBaseChange.hypS_baseChange S S' P.A P'.A f φ P.L P'.L P.isLB P'.isLB gp
    (LBIso.symm ⟨t, ht⟩) h⟩

theorem exists_finite_pairs {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] [Algebra.IsAlgebraic F Ω]
    {A B : Over (Sp F)} {A' B' C' : Over (Sp Ω)} [GrpObj A] [GrpObj B] [GrpObj A'] [GrpObj B'] [GrpObj C']
    (Q : Out.PolAV (Sp F)) (hQ : letI := Q.isAb.comm; GlobalTheory.ZH.HypS Q.A Q.L)
    (hA : IsAbelianScheme A) (hB : IsAbelianScheme B) {m : ℕ} {φ : A'.left ⟶ A.left} {ψ : B'.left ⟶ B.left}
    {χ : C'.left ⟶ Q.A.left}
    (pA : IsGrpPullback A' A (spMap (algebraMap F Ω)) φ) (pB : IsGrpPullback B' B (spMap (algebraMap F Ω)) ψ)
    (pC : IsGrpPullback C' Q.A (spMap (algebraMap F Ω)) χ)
    (h : Pair A' B' m) (h' : Pair C' B' 1) : ∃ (L : IntermediateField F Ω) (Q' : Out.PolAV (Sp L)),
      FiniteDimensional F L ∧ (letI := Q'.isAb.comm; GlobalTheory.ZH.HypS Q'.A Q'.L) ∧
      Pair ((Over.pullback (spMap (algebraMap F L))).obj A) ((Over.pullback (spMap (algebraMap F L))).obj B) m ∧
      Pair Q'.A ((Over.pullback (spMap (algebraMap F L))).obj B) 1 := by
  obtain ⟨L₁, f₁, h₁⟩ := h.descend hA hB pA pB
  obtain ⟨L₂, f₂, h₂⟩ := h'.descend Q.isAb hB pC pB
  obtain ⟨Q', χ', gp, hS⟩ := exists_pol_baseChange (spMap (algebraMap F (L₁ ⊔ L₂ : IntermediateField F Ω))) Q hQ
  exact ⟨L₁ ⊔ L₂, Q', inferInstance, hS,
    h₁ _ le_sup_left _ _ _ _ (isGrpPullback_pullback _ _) (isGrpPullback_pullback _ _),
    h₂ _ le_sup_right _ _ _ _ gp (isGrpPullback_pullback _ _)⟩

theorem exists_finite_data (K : Type) [Field K] [CharZero K] (A : Over (Sp K)) [GrpObj A] (hA : IsAbelianScheme A)
    (g : ℕ) (hg : SmoothOfRelativeDimension g A.hom) :
    ∃ (L : Type) (_ : Field L) (c : K →+* L) (B : Over (Sp L)) (_ : GrpObj B) (Q : Out.PolAV (Sp L)) (m : ℕ),
      c.Finite ∧ SmoothOfRelativeDimension g B.hom ∧ 1 ≤ m ∧ Pair ((Over.pullback (spMap c)).obj A) B m ∧
      Pair Q.A B 1 ∧ (letI := Q.isAb.comm; GlobalTheory.ZH.HypS Q.A Q.L) := by
  let Ω := AlgebraicClosure K
  obtain ⟨B, _, M, i, r, m, hB, hgB, hM, hM₁, hM₂, hi, hr, hm, e⟩ :=
    GlobalTheory.SS.PrincIsog.exists_isogeny_kTriv Ω ((Over.pullback (spMap (algebraMap K Ω))).obj A) g (isAbelianScheme_pullback_obj _ A hA) (relDim_pullback _ A hg)
  obtain ⟨Q, i', r', hQ, hi', hr', e'⟩ := GlobalTheory.EighthPowerFactor.exists_polAV_hypS_retract Ω B g hB hgB M hM hM₁ hM₂
  obtain ⟨L₁, f₁, B₁, _, eB, hB₁, heB⟩ := GlobalTheory.exists_finite_isAbelianScheme_descends K Ω B hB
  have lev := GlobalTheory.nonempty_level_of_isAlgClosed Ω Q 1 (Units.map (algebraMap L₁ Ω).toMonoidHom 1) (by simp)
    (by rw [map_one]; exact IsPrimitiveRoot.one)
  obtain ⟨F, _, _, j, R₀, Q₀, χ, hfg, hfr, -, pC, hQ₀, -⟩ := GlobalTheory.SymLevelDescent.descends_to_fg_field L₁ Ω Q 1 1 hQ lev
  letI : Algebra F Ω := j.toRingHom.toAlgebra
  haveI : IsScalarTower L₁ F Ω := IsScalarTower.of_algebraMap_eq fun x => (j.commutes x).symm
  haveI : Algebra.IsAlgebraic L₁ Ω := Algebra.IsAlgebraic.tower_top (K := K) L₁
  haveI : Algebra.IsAlgebraic L₁ F := Algebra.IsAlgebraic.of_injective j j.toRingHom.injective
  haveI : Algebra.IsAlgebraic F Ω := Algebra.IsAlgebraic.tower_top (K := L₁) F
  have f₂ : FiniteDimensional L₁ F := finite_of_fg R₀ hfg hfr
  let c₀ : K →+* F := (algebraMap L₁ F).comp (algebraMap K L₁)
  have pB₁ : IsGrpPullback B B₁ (spMap (algebraMap L₁ Ω)) _ :=
    ((isGrpPullback_of_iso eB.symm).comp (isGrpPullback_pullback B₁ _)).congr (Category.id_comp _) rfl
  have hgB₁ : SmoothOfRelativeDimension g B₁.hom :=
    (GlobalTheory.FieldDescentAb.isAbelianScheme_and_relDim_descend L₁ Ω _ B₁ B _ pB₁ hB).2 g hgB
  obtain ⟨a, ha, -⟩ := grpPullback_iso (isGrpPullback_pullback A (spMap (algebraMap K Ω)))
    (((isGrpPullback_pullback _ (spMap (algebraMap F Ω))).comp (isGrpPullback_pullback A (spMap c₀))).congr
      (spMap_comp _ _ _ fun x => j.commutes (algebraMap K L₁ x)) rfl)
  obtain ⟨b, hb, -⟩ := grpPullback_iso pB₁
    (((isGrpPullback_pullback _ (spMap (algebraMap F Ω))).comp
      (isGrpPullback_pullback B₁ (spMap (algebraMap L₁ F)))).congr (spMap_comp _ _ _ fun x => j.commutes x) rfl)
  have P₁ : Pair _ B m := ⟨i, r, hi, hr, e⟩
  have P₂ : Pair Q.A B 1 := ⟨r', i', hr', hi', by rw [e', pow_one]⟩
  obtain ⟨L, Q', f₃, hQ', P₃, P₄⟩ := exists_finite_pairs Q₀ hQ₀ (isAbelianScheme_pullback_obj (spMap c₀) A hA)
    (isAbelianScheme_pullback_obj (spMap (algebraMap L₁ F)) B₁ hB₁) (isGrpPullback_pullback _ _)
    (isGrpPullback_pullback _ _) pC (P₁.of_iso a.symm b.symm) (P₂.of_iso (Iso.refl _) b.symm)
  obtain ⟨a', ha', -⟩ := grpPullback_iso (isGrpPullback_pullback A (spMap ((algebraMap F L).comp c₀)))
    (((isGrpPullback_pullback _ (spMap (algebraMap F L))).comp (isGrpPullback_pullback A (spMap c₀))).congr
      (spMap_comp _ _ _ fun x => rfl) rfl)
  exact ⟨L, inferInstance, (algebraMap F L).comp c₀, _, inferInstance, Q', m,
    (RingHom.finite_algebraMap.2 f₃).comp ((RingHom.finite_algebraMap.2 f₂).comp (RingHom.finite_algebraMap.2 f₁)),
    relDim_pullback _ _ (relDim_pullback _ _ hgB₁), hm, P₃.of_iso a' (Iso.refl _), P₄, hQ'⟩

theorem exists_isogenous_retract : ∀ (K : Type) [Field K] [CharZero K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∃ (L : Type) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L) (B : Over (Sp L)) (_ : GrpObj B) (Q : Out.PolAV (Sp L)) (g m : ℕ) (i : (Over.pullback (spMap (algebraMap K L))).obj A ⟶ B) (r : B ⟶ (Over.pullback (spMap (algebraMap K L))).obj A) (i' : B ⟶ Q.A) (r' : Q.A ⟶ B), GlobalTheory.AbLaw.IsProjBy ((Over.pullback (spMap (algebraMap K L))).obj A).hom ∧ SmoothOfRelativeDimension g ((Over.pullback (spMap (algebraMap K L))).obj A).hom ∧ SmoothOfRelativeDimension g B.hom ∧ IsMonHom i ∧ IsMonHom r ∧ 1 ≤ m ∧ r ≫ i = 𝟙 _ ^ m ∧ IsMonHom i' ∧ IsMonHom r' ∧ i' ≫ r' = 𝟙 B ∧ (letI := Q.isAb.comm; GlobalTheory.ZH.HypS Q.A Q.L) := by
  intro K _ _ A _ hA
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim K A hA
  obtain ⟨L₀, _, _, f₀, hP⟩ := GlobalTheory.ProjFinite.exists_finite_isProjBy K A hA
  haveI : CharZero L₀ := charZero_of_injective_algebraMap (algebraMap K L₀).injective
  obtain ⟨L, _, c, B, _, Q, m, hc, hgB, hm, P₁, ⟨r', i', hr', hi', e'⟩, hQ⟩ := exists_finite_data L₀ _
    (isAbelianScheme_pullback_obj (spMap (algebraMap K L₀)) A hA) g
    (relDim_pullback _ _ hg)
  letI : Algebra K L := (c.comp (algebraMap K L₀)).toAlgebra
  have f : FiniteDimensional K L := hc.comp (RingHom.finite_algebraMap.2 f₀)
  obtain ⟨a, ha, -⟩ := grpPullback_iso (isGrpPullback_pullback A (spMap (algebraMap K L)))
    (((isGrpPullback_pullback _ (spMap c)).comp (isGrpPullback_pullback A (spMap (algebraMap K L₀)))).congr
      (spMap_comp _ _ _ fun x => rfl) rfl)
  obtain ⟨i, r, hi, hr, e⟩ := P₁.of_iso a (Iso.refl _)
  have gp := ((isGrpPullback_of_iso a).comp (isGrpPullback_pullback _ (spMap c))).congr (Category.id_comp _) rfl
  exact ⟨L, inferInstance, inferInstance, f, B, inferInstance, Q, g, m, i, r, i', r',
    GlobalTheory.AbLaw.isProjBy_baseChange L₀ L c _ _ _ _ _ gp.1 hP,
    relDim_pullback _ _ hg, hgB, hi, hr, hm, e, hi', hr',
    by rw [e', pow_one], hQ⟩

end GlobalTheory.FiniteData
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

theorem _root_.GlobalTheory.T.isProper_of_theta_unit_in_every_coset : HV → Laws6 → GlobalTheory.LN.UDvrSt → GlobalTheory.LN.HomExtSt → ThetaPtDeterminesSt → EndDeterminedOnTorsionSt → ThetaUnifAV → AllD fun D => ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [CharZero C] (o : Full D C) (M : Mdl o) (n j : ℕ), n.Prime → Odd n → ‖(n : C)‖ = 1 → 2 ≤ j → ∀ v, o.Theta (n ^ j) v → (∀ x, ‖v x‖ ≤ 1) → (∀ x, ∃ h, ‖v (x + n ^ (j - 1) • h)‖ = 1) → IsProper M.t.G.hom := by
  first | exact @GlobalTheory.CosetGood.isProper_of_unit_in_cosets | exact GlobalTheory.CosetGood.isProper_of_unit_in_cosets | (intros; apply GlobalTheory.CosetGood.isProper_of_unit_in_cosets <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN

theorem GlobalTheory.LN.ega_of_laws : Laws → Laws2 → Ega := fun h₁ h₂ =>
  ⟨GlobalTheory.T.compatible_line_bundles_formal_thickening h₁ h₂, GlobalTheory.T.existsUnique_hom_of_thickenings' h₁ h₂, GlobalTheory.SecAlg.existsUnique_sec, GlobalTheory.T.exists_section_primitiveBundle_translate_localRing h₁ h₂⟩
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TestFibre

theorem _root_.GlobalTheory.T.symmetricLift_normalisedPullback_theta_smul : LL → ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (F : Type) [Field F] [Algebra (FractionRing R) F] (ρ : LB.Gen (A.L.pull (eSec A.A))), ρ.IsGen → ∀ (m : ℕ), Odd m → ∀ (th th' : SecA A F 1) (c : F), (∀ j, th.f j = liftFun A.A _ (cF R c) * th'.f j) → ∀ (s₁ σ t : SecA A F (m ^ 2)) (x : TFK (R := R) F ⟶ A.A) (θ : ThetaGrp A.A A.L ((m ^ 2 : ℕ) : ℤ) (TFK (R := R) F)) (c' : F), x ^ (m ^ 2) = 1 → IsNormPull A ρ m (m ^ 2) th s₁ → SymLift A.A A.L ((m ^ 2 : ℕ) : ℤ) (m ^ 2) x θ → IsActOf A.A A.L ((m ^ 2 : ℕ) : ℤ) θ s₁ σ → ThC A ρ m th' x t c' → ∀ j, σ.f j = liftFun A.A _ (cF R c) * t.f j := by
  first | exact @GlobalTheory.TestFibre.act_normPull_smul | exact GlobalTheory.TestFibre.act_normPull_smul | (intros; apply GlobalTheory.TestFibre.act_normPull_smul <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis

theorem _root_.GlobalTheory.T.exists_torsionPoint_unit_value_primitive_integral_family : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllUV fun {V} _ _ _ {ϖ} hϖ {D} Q {F} _ _ {v} hv {A} {G} _ _ U => ∀ w₀ ρ, NormW U.toUnifPre w₀ ρ → ∀ k n : ℕ, 4 ≤ k → n.Prime → IsUnit (n : V) → ∀ (t : SecA A F k) (s : Fam D.toPre F k) (α : D.toPre.X), U.ExpandsF F k w₀ t s → IntGe D v s 0 → (∀ q : ℚ, 0 < q → ¬ VGe D F v k α (s.s α) q) → ∃ (j : ℕ) (x : TFK (R := V) F ⟶ A.A), 2 ≤ j ∧ FromGt U.toUnifPre (n ^ j) x ∧ ∀ e (c : F), IsTorsFrame A ρ (n ^ j) x e → ValAt t x e c → v c = 0 := by
  first | exact @GlobalTheory.OneBasis.UnitValue.exists_unit_value | exact GlobalTheory.OneBasis.UnitValue.exists_unit_value | (intros; apply GlobalTheory.OneBasis.UnitValue.exists_unit_value <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis

theorem _root_.GlobalTheory.T.integral_family_values_torsion_torusExtension : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllUV fun {V} _ _ _ {ϖ} hϖ {D} Q {F} _ _ {v} hv {A} {G} _ _ U => ∀ w₀ ρ, NormW U.toUnifPre w₀ ρ → ∀ n k : ℕ, 1 ≤ n → 1 ≤ k → ∀ (x : TFK (R := V) F ⟶ A.A) e (t : SecA A F k) (s : Fam D.toPre F k) (c : F), FromGt U.toUnifPre n x → IsTorsFrame A ρ n x e → U.ExpandsF F k w₀ t s → IntGe D v s 0 → ValAt t x e c → 0 ≤ v c := by
  first | exact @GlobalTheory.OneBasis.integral_value_at_torsion | exact GlobalTheory.OneBasis.integral_value_at_torsion | (intros; apply GlobalTheory.OneBasis.integral_value_at_torsion <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TestFibre

theorem _root_.GlobalTheory.T.exists_thetaSystem_test_sections_on_geometric_fibre : Laws → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (x : S.Gam → (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A)), PtsOver u x → ∃ rig e th s, SecsOver u x rig e th s := by
  first | exact @GlobalTheory.TestFibre.exists_secsOver | exact GlobalTheory.TestFibre.exists_secsOver | (intros; apply GlobalTheory.TestFibre.exists_secsOver <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TestFibre

theorem _root_.GlobalTheory.T.fibreSection_linearComb_exists_unique_thetaAction : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) (J : Type) [Fintype J] (s : J → SecA A F k) (b : J → F), (∃ t, IsComb A s b t) ∧ (∀ t t', IsComb A s b t → IsComb A s b t' → t = t') ∧ (∀ (θ : ThetaGrp A.A A.L (k : ℤ) (TFK (R := R) F)) (s' : J → SecA A F k) t t', (∀ i, IsActOf A.A A.L k θ (s i) (s' i)) → IsComb A s b t → (IsActOf A.A A.L k θ t t' ↔ IsComb A s' b t')) ∧ (∀ (θ : ThetaGrp A.A A.L (k : ℤ) (TFK (R := R) F)) (t : SecA A F k), ∃! t', IsActOf A.A A.L k θ t t') ∧ ∀ (I : Type) [Fintype I] (M : I → J → F) (r : I → SecA A F k) (a : I → F) (t : SecA A F k), (∀ i, IsComb A s (M i) (r i)) → IsComb A r a t → IsComb A s (fun j => ∑ i, M i j * a i) t := by
  first | exact @GlobalTheory.secComb_thetaAct | exact GlobalTheory.secComb_thetaAct | (intros; apply GlobalTheory.secComb_thetaAct <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TestFibre

theorem _root_.GlobalTheory.T.isFibreSectionLinearComb_iff_expansion_sum : LL → AllU fun {R} _ _ {I} {D} {A} {G} _ _ U => ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ), 1 ≤ k → ∀ (w₀ : W0 U.toUnifPre), w₀.IsGen → ∀ (J : Type) [Fintype J] (s : J → SecA A F k) (Φ : J → Fam D.toPre F k) (b : J → F) (t : SecA A F k), (∀ i, U.ExpandsF F k w₀ (s i) (Φ i)) → (IsComb A s b t ↔ U.ExpandsF F k w₀ t (∑ i, b i • Φ i)) := by
  first | exact @GlobalTheory.TestFibre.isComb_iff_expandsF_sum | exact GlobalTheory.TestFibre.isComb_iff_expandsF_sum | (intros; apply GlobalTheory.TestFibre.isComb_iff_expandsF_sum <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TestFibre

theorem _root_.GlobalTheory.T.isFibreSectionValueInFrame_linear_unique_exists : Laws → ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) (x : TFK (R := R) F ⟶ A.A) (e : FrameAt A x), (∀ (J : Type) [Fintype J] (s : J → SecA A F k) (b c : J → F) (t : SecA A F k), IsComb A s b t → (∀ i, ValIs A (s i) x e (c i)) → ValIs A t x e (∑ i, b i * c i)) ∧ (∀ (t t' : SecA A F k) (a c : F), (∀ j, t'.f j = liftFun A.A _ (cF R a) * t.f j) → ValIs A t x e c → ValIs A t' x e (a * c)) ∧ (∀ (t : SecA A F k) c c', ValIs A t x e c → ValIs A t x e c' → c = c') ∧ (e.IsGen → ∀ t : SecA A F k, ∃ c, ValIs A t x e c) := by
  first | exact @GlobalTheory.TestFibre.CombValue.valIs_linear | exact GlobalTheory.TestFibre.CombValue.valIs_linear | (intros; apply GlobalTheory.TestFibre.CombValue.valIs_linear <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH

theorem utest_nonempty_mod : GlobalTheory.UT.LL → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (σ : S.J → (u.H S.N).Sec) (cls : S.J → u.D.toPre.X) (f : S.J → ∀ α, u.D.toPre.SecB S.N α), u.Basis l S.N σ cls f → Nonempty (Mod p u.j u.G S.g S.N l.q (u.H S.N) σ cls) := by
  intro hL hT o Ω _ _ _ _ S ρ p _ y₀ u l σ cls f hb
  obtain ⟨-, hdim, hsm, h4, -⟩ := utest_dim_and_split hL o Ω S ρ p y₀ u
  have h1 : 1 ≤ S.N := le_trans (by norm_num) h4
  obtain ⟨fb⟩ := GlobalTheory.T.nonempty_geometric_special_fibre_uniformised hL o Ω S ρ p y₀ u S.N h1
  obtain ⟨F, hF, hred⟩ := fb.exp S.J σ f (fun i => hb.2.2.2.1 i 0)
  refine ⟨{ isLB := LB.isLB_linComb u.U.LG.isLB _ _
            smooth := hsm
            Φ := fb.Φ
            r := fb.r
            cart := fb.cart
            xe := fb.xe
            F := F
            good := GlobalTheory.T.good_reduction_adapted_basis hL o Ω S ρ p y₀ u l S.N fb h1 S.J σ cls f hb F hF
            pol := fb.pol
            dim := ?_
            red := hred
            ser := GlobalTheory.T.theta_series_at_point_integral_of_period_valuation hL hT o Ω S ρ p y₀ u l σ cls f hb }⟩
  rw [fb.dim, fb.xe.toIntLinearEquiv.finrank_eq]
  exact hdim

end GlobalTheory.ZH
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TestFibre

noncomputable section

namespace GlobalTheory.ThetaBound

theorem le_of_sum {F : Type} [Field F] {v : AddValuation F (WithTop ℚ)} {Ix : Type} {x : Ix → F} {s : F}
    (h : SumV v x s) {q : ℚ} (hq : ∀ i, (q : WithTop ℚ) ≤ v (x i)) : (q : WithTop ℚ) ≤ v s := by
  obtain ⟨T, hT⟩ := h q
  have := v.map_le_add (hT T le_rfl) (v.map_le_sum (s := T) fun i _ => hq i)
  rwa [sub_add_cancel] at this

theorem square_nonneg {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
    {D : DegData V (IsLocalRing.maximalIdeal V)} {Q : D.toPre.X → ℤ} (hϖ : Irreducible ϖ)
    (hQ : QForm.IsQ D.toPre ϖ Q) (n : ℕ) (hn : 1 ≤ n) (y χ : D.toPre.X) :
    (0 : ℚ) ≤ 0 + (Q χ : ℚ) / (1 : ℕ) + (QForm.bOf D.toPre Q y χ : ℚ) / n + (Q y : ℚ) / (n : ℚ) ^ 2 := by
  have h0 : 0 ≤ Q (n • χ + y) := by
    by_cases h : n • χ + y = 0
    · rw [h, QForm.Q_zero hϖ D hQ]
    · exact le_trans zero_le_one (QForm.Q_pos hϖ D hQ h)
  have e : Q (n • χ + y) = n ^ 2 * Q χ + n * QForm.bOf D.toPre Q y χ + Q y := by
    have e₁ : Q (n • χ + y) = Q (n • χ) + Q y + QForm.bOf D.toPre Q (n • χ) y := by
      simp only [QForm.bOf]; ring
    have e₂ : QForm.bOf D.toPre Q χ y = QForm.bOf D.toPre Q y χ := by
      simp only [QForm.bOf, add_comm χ y]; ring
    rw [e₁, DVR.Q_nsmul hϖ hQ, DVR.bOf_nsmul_left hϖ hQ, e₂]; ring
  have hn' : (0 : ℚ) < n := by exact_mod_cast hn
  have h1 : (0 : ℚ) ≤ (n : ℚ) ^ 2 * Q χ + n * (QForm.bOf D.toPre Q y χ : ℚ) + Q y := by
    rw [e] at h0; exact_mod_cast h0
  have e₃ : 0 + (Q χ : ℚ) / (1 : ℕ) + (QForm.bOf D.toPre Q y χ : ℚ) / n + (Q y : ℚ) / (n : ℚ) ^ 2 =
      ((n : ℚ) ^ 2 * Q χ + n * (QForm.bOf D.toPre Q y χ : ℚ) + Q y) / (n : ℚ) ^ 2 := by
    field_simp
    push_cast
    ring
  rw [e₃]
  positivity

theorem norm_theta_le : Laws → Laws2 → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → ∀ (x : S.Gam → (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A)) (rig : LB.Gen (u.A.L.pull (eSec u.A.A))) (e : ∀ a, FrameAt u.A (x a)) (th : SecA u.A (PadicAlgCl p) 1) (s : S.J → SecA u.A (PadicAlgCl p) S.N), PtsOver u x → SecsOver u x rig e th s → ∀ (ϖ : u.V) (Q : u.D.toPre.X → ℤ) (v : AddValuation (PadicAlgCl p) (WithTop ℚ)) (lam : ℝ), Irreducible ϖ → ValOver ϖ (PadicAlgCl p) v → NormIs u l ϖ Q v lam → ∀ (w₀ : W0 u.U.toUnifPre) (th' : SecA u.A (PadicAlgCl p) 1) (ϑ : Fam u.D.toPre (PadicAlgCl p) 1) (c : PadicAlgCl p), NormW u.U.toUnifPre w₀ rig → u.U.ExpandsF (PadicAlgCl p) 1 w₀ th' ϑ → Prim u.D Q v ϑ → (∀ j, th.f j = liftFun u.A.A _ (cF u.V c) * th'.f j) → ∀ a, ‖y₀ ⟨S.th a, S.th_mem a⟩‖ ≤ ‖c‖ := by
  intro hL hL₂ hT o Ω _ _ _ _ S ρ p _ y₀ u l _ x rig e th s _ hS ϖ Q v lam hϖ hv hN w₀ th' ϑ c hW hE hP hc a
  obtain ⟨-, htf, hth, -⟩ := hS
  obtain ⟨-, hQ, -, hle, -⟩ := hN
  obtain ⟨hLL, h₁, h₂, h₃, h₄⟩ := laws_all hL hL₂
  have : CharZero u.V :=
    ((algebraMap (FractionRing u.V) (PadicAlgCl p)).comp (algebraMap u.V (FractionRing u.V))).charZero
  have hn : 1 ≤ S.r * S.N := Nat.mul_pos S.r_pos (le_trans one_le_two S.N_ge)
  obtain ⟨f, hf, hsurj, -⟩ := hT u.V u.complete u.A u.G u.D u.U (PadicAlgCl p) (S.r * S.N) hn
  obtain ⟨q, hq⟩ := hsurj (x a) (htf a).1
  have hqx := (hf q (x a)).2 hq.symm
  obtain ⟨-, hmul, huniq, hex⟩ := GlobalTheory.TestFibre.CombValue.valIs_linear hL u.V u.A (PadicAlgCl p) 1 (x a) (e a)
  obtain ⟨c', hc'⟩ := hex (htf a).2.1 th'
  have hval : y₀ ⟨S.th a, S.th_mem a⟩ = c * c' := huniq th _ _ (hth a) (hmul th' th c c' hc hc')
  obtain ⟨w₁, hw₁, hv₁, hsum⟩ := GlobalTheory.T.section_value_at_torsionPoint_eq_sum_terms hLL h₁ h₂ h₃ h₄ u.V u.complete ϖ hϖ u.D Q hQ (PadicAlgCl p) v hv
    u.A u.G u.semi u.U w₀ rig hW (S.r * S.N) hn q (x a) hqx (e a) (htf a)
  obtain ⟨-, -, -, -, hqk, -, hterm⟩ := GlobalTheory.UT.CoefVal.main hLL h₁ h₂ h₃ h₄ u.V u.complete ϖ hϖ u.D Q hQ
    (PadicAlgCl p) v hv q.g
  have hsv := hsum 1 le_rfl w₁ ⟨hw₁, fun z J _ => (pow_one _).symm⟩ th' ϑ c' hE hc'
  have h0 : ((0 : ℚ) : WithTop ℚ) ≤ v c' := le_of_sum hsv fun χ =>
    le_trans (WithTop.coe_le_coe.2 (square_nonneg hϖ hQ (S.r * S.N) hn q.y χ))
      ((hterm 1 le_rfl w₁ ϑ hw₁).2 _ _ 0 (hqk _ hn q) hv₁ hP.1 χ)
  have h1 : ‖c'‖ ≤ 1 := by simpa using (hle c' 0).1 h0
  rw [hval, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) h1

end GlobalTheory.ThetaBound
end
end
