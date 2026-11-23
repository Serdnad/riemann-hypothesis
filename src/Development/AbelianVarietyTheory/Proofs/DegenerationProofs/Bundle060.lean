module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle001
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle015
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SymmetricLiftOddOrderExistsUnique
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle016
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MorphismsSpreadOutToFgSubalgebra
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle064
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle039
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle050
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle044
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle049
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle048
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle047
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
import Mathlib.Tactic.ENatToNat
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
import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle001

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TestFibre

theorem _root_.GlobalTheory.T.exists_val_le_of_valuedSum_against_characters : ∀ (F : Type) [Field F] (v : AddValuation F (WithTop ℚ)) (X T : Type) [Fintype T] (χ : T → X → F) (cf : X → F) (ζ w : T → F) (α : X) (q : ℚ), (∀ t, SumV v (fun β => χ t β * cf β) (ζ t * w t)) → (∀ t, v (ζ t) = 0) → (∀ t β, v (χ t β) = 0) → v ((Fintype.card T : ℕ) : F) = 0 → v (cf α) = (q : WithTop ℚ) → (∀ β, β ≠ α → ∑ t, (χ t α)⁻¹ * χ t β = 0 ∨ (q : WithTop ℚ) < v (cf β)) → ∃ t, v (w t) ≤ (q : WithTop ℚ) := by
  first | exact @GlobalTheory.TestFibre.exists_val_le_of_sumV_characters | exact GlobalTheory.TestFibre.exists_val_le_of_sumV_characters | (intros; apply GlobalTheory.TestFibre.exists_val_le_of_sumV_characters <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SymLiftGlobal

open CommPairing GlobalLift

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {k : ℤ}

theorem exists_symLift_pull_val (hL : L.IsLB) {n : ℕ} {T T' : Over S} (h : T' ⟶ T) {x : T ⟶ A}
    {θ : ThetaGrp A L k T} (H : SymLift A L k n x θ) :
    ∃ θ' : ThetaGrp A L k T', SymLift A L k n (h ≫ x) θ' ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (T' ⊗ A).left) (z : Z) (J),
      Good L z J → tval θ' r z J = tval θ (r ≫ (h ▷ A).left) z J := by
  obtain ⟨rfl, hp, ν, hν, hs⟩ := H
  obtain ⟨θ', e, v⟩ := exists_pull hL h θ
  obtain ⟨ν', hν', w⟩ := exists_neg_pull hL h ν hν
  have t : ∀ (r : (T' ⊗ A).left ⟶ (T' ⊗ A).left) (x : T ⟶ A), (r ≫ (translT A (h ≫ x)).left) ≫ (h ▷ A).left =
      (r ≫ (h ▷ A).left) ≫ (translT A x).left := fun r x => by
    rw [Category.assoc, Category.assoc, ← Over.comp_left, ← Over.comp_left, whisker_translT]
  have u : ∀ (r : (T' ⊗ A).left ⟶ (T' ⊗ A).left), (r ≫ (negT A T').left) ≫ (h ▷ A).left =
      (r ≫ (h ▷ A).left) ≫ (negT A T).left := fun r => by
    rw [Category.assoc, Category.assoc, ← Over.comp_left, ← Over.comp_left, whisker_negT]
  refine ⟨θ', ⟨e, corr_of_val hL fun y J hJ => ?_, ν', hν', corr_of_val hL fun y J hJ => ?_⟩, v⟩
  · have q := val_corr hJ hp (𝟙 _ ≫ (h ▷ A).left)
    rw [val_powGen _ _ _ hJ, val_one] at q ⊢
    refine Eq.trans (Finset.prod_congr rfl fun i _ => ?_) q
    rw [v _ _ y J hJ, e, ← MonObj.comp_pow, t]
  · have q := val_corr hJ hs (𝟙 _ ≫ (h ▷ A).left)
    rw [val_symGen _ _ _ hJ, val_one] at q ⊢
    rw [v _ _ y J hJ, v _ _ y J hJ, w _ _ y J hJ, w _ _ y J hJ, e, ← GrpObj.comp_inv, t, u]
    exact q


omit [GrpObj A] in
theorem exists_lift_res {T : Over S} (V : T.left.Opens) {Z : Scheme.{0}} (ρ : Z ⟶ (T ⊗ A).left)
    (hρ : ∀ z, (fst T A).left (ρ z) ∈ V) :
    ∃ n : Z ⟶ (overRes V ⊗ A).left, n ≫ (overResι V ▷ A).left = ρ := by
  obtain ⟨v, hv⟩ : ∃ v : Z ⟶ V.toScheme, v ≫ V.ι = ρ ≫ (fst T A).left :=
    ⟨IsOpenImmersion.lift V.ι (ρ ≫ (fst T A).left) (by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact hρ y), IsOpenImmersion.lift_fac _ _ _⟩
  let ρ' : Over.mk (ρ ≫ (T ⊗ A).hom) ⟶ T ⊗ A := Over.homMk ρ rfl
  let v' : Over.mk (ρ ≫ (T ⊗ A).hom) ⟶ overRes V := Over.homMk v (by
    show v ≫ V.ι ≫ T.hom = ρ ≫ (T ⊗ A).hom
    rw [← Category.assoc, hv, Category.assoc, Over.w (fst T A)])
  have e : v' ≫ overResι V = ρ' ≫ fst T A := Over.OverMorphism.ext hv
  have e' : lift v' (ρ' ≫ snd T A) ≫ overResι V ▷ A = ρ' := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, whiskerRight_fst, lift_fst_assoc, e]
    · rw [Category.assoc, whiskerRight_snd, lift_snd]
  exact ⟨(lift v' (ρ' ≫ snd T A)).left, congrArg (fun q => q.left) e'⟩

omit [GrpObj A] in
theorem mono_res {T : Over S} (V : T.left.Opens) : Mono (overResι V ▷ A).left := by
  have : Mono (overResι V).left := inferInstanceAs (Mono V.ι)
  have : Mono (overResι V) := Over.mono_of_mono_left _
  have : Mono (overResι V ▷ A) := ⟨fun a b e => by
    apply CartesianMonoidalCategory.hom_ext
    · rw [← cancel_mono (overResι V), Category.assoc, Category.assoc, ← whiskerRight_fst, ← Category.assoc, e,
        Category.assoc]
    · rw [← whiskerRight_snd (overResι V), ← Category.assoc, e, Category.assoc]⟩
  infer_instance

theorem tval_agree (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) {n : ℕ} (hn : Odd n) {T : Over S}
    {x : T ⟶ A} {V V' : T.left.Opens} {θ : ThetaGrp A L k (overRes V)} {θ' : ThetaGrp A L k (overRes V')}
    (H : SymLift A L k n (overResι V ≫ x) θ) (H' : SymLift A L k n (overResι V' ≫ x) θ')
    {Z : Scheme.{0}} (r : Z ⟶ (overRes V ⊗ A).left) (r' : Z ⟶ (overRes V' ⊗ A).left)
    (hr : r ≫ (overResι V ▷ A).left = r' ≫ (overResι V' ▷ A).left) (z : Z) (J) (hJ : Good L z J) :
    tval θ r z J = tval θ' r' z J := by
  have mem : ∀ (W : T.left.Opens) (s : Z ⟶ (overRes W ⊗ A).left) (y : Z),
      (fst T A).left ((s ≫ (overResι W ▷ A).left) y) ∈ W := fun W s y => by
    have e : (overResι W ▷ A).left ≫ (fst T A).left = (fst (overRes W) A).left ≫ W.ι := by
      rw [← Over.comp_left, whiskerRight_fst]; rfl
    exact (congrArg (fun q => q (s y) ∈ W) e).mpr ((fst (overRes W) A).left (s y)).2
  obtain ⟨m, hm⟩ := exists_lift_res (V ⊓ V') (r ≫ (overResι V ▷ A).left)
    (fun y => ⟨mem V r y, hr ▸ mem V' r' y⟩)
  have inc : ∀ (W : T.left.Opens), V ⊓ V' ≤ W → ∃ i : overRes (V ⊓ V') ⟶ overRes W,
      i ≫ overResι W = overResι (V ⊓ V') := fun W hW =>
    ⟨Over.homMk (T.left.homOfLE hW) (by
      show T.left.homOfLE hW ≫ W.ι ≫ T.hom = (V ⊓ V').ι ≫ T.hom
      rw [← Category.assoc, Scheme.homOfLE_ι]), Over.OverMorphism.ext (T.left.homOfLE_ι hW)⟩
  obtain ⟨i, hi⟩ := inc V inf_le_left
  obtain ⟨i', hi'⟩ := inc V' inf_le_right
  obtain ⟨ξ, Hξ, vξ⟩ := exists_symLift_pull_val hL i H
  obtain ⟨ξ', Hξ', vξ'⟩ := exists_symLift_pull_val hL i' H'
  rw [← Category.assoc, hi] at Hξ
  rw [← Category.assoc, hi'] at Hξ'
  have := mono_res (A := A) V
  have := mono_res (A := A) V'
  have e : m ≫ (i ▷ A).left = r := by
    rw [← cancel_mono (overResι V ▷ A).left, Category.assoc, ← Over.comp_left, ← comp_whiskerRight, hi, hm]
  have e' : m ≫ (i' ▷ A).left = r' := by
    rw [← cancel_mono (overResι V' ▷ A).left, Category.assoc, ← Over.comp_left, ← comp_whiskerRight, hi', hm, hr]
  rw [← e, ← e', ← vξ _ _ z J hJ, ← vξ' _ _ z J hJ]
  exact val_corr hJ (SymLiftOdd.symLift_unique hG hA hL hn ξ ξ' Hξ Hξ') m

theorem exists_lift_of_local (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) {n : ℕ} (hn : Odd n)
    {T : Over S} {x : T ⟶ A}
    (h : ∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧
      ∃ θ : ThetaGrp A L k (overRes V), SymLift A L k n (overResι V ≫ x) θ) :
    ∃ θ : ThetaGrp A L k T, θ.pt = x := by
  choose V hV θ hθ using h
  choose m hm using fun p => exists_lift_res (A := A) (V p) ((fst T A).left ⁻¹ᵁ V p).ι (fun z => z.2)
  have loc : ∀ p, ∃ t : LB.Gen (LB.LinComb L (K := Fin 2)
      (fun b => ((fst T A).left ⁻¹ᵁ V p).ι ≫ ![(snd T A).left, (translPt A x).left] b) ![k, -k]), t.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ ((fst T A).left ⁻¹ᵁ V p).toScheme) (z : Z) (J), Good L z J →
        val t r z J = tval (θ p) (r ≫ m p) z J := fun p => by
    have e₀ : m p ≫ (snd (overRes (V p)) A).left = ((fst T A).left ⁻¹ᵁ V p).ι ≫ (snd T A).left := by
      rw [← hm p, Category.assoc, ← Over.comp_left, whiskerRight_snd]
    have e₁ : m p ≫ (translPt A (θ p).pt).left = ((fst T A).left ⁻¹ᵁ V p).ι ≫ (translPt A x).left := by
      rw [← hm p, Category.assoc, ← Over.comp_left, whisker_translPt, (hθ p).pt_eq]
    obtain ⟨t, ht, hv⟩ := exists_gen hL (K' := Fin 2)
      (φ' := fun b => ((fst T A).left ⁻¹ᵁ V p).ι ≫ ![(snd T A).left, (translPt A x).left] b) (ε' := ![k, -k])
      (fun U _ f => by
        refine Finset.prod_congr rfl fun i _ => ?_
        fin_cases i
        · exact congrArg (fun q => f q ^ k) e₀
        · exact congrArg (fun q => f q ^ (-k)) e₁)
      (LB.pullGen L ![(snd (overRes (V p)) A).left, (translPt A (θ p).pt).left] ![k, -k] (θ p).φ (m p))
      (DVR.pullGen_isGen _ _ _ _ (θ p).isGen _)
    exact ⟨t, ht, fun Z r z J hJ => (hv Z r z J hJ).trans (val_pull hJ _ _ _)⟩
  choose t ht hv using loc
  obtain ⟨u, hu, -⟩ := glue_gen hL (K := Fin 2) ![(snd T A).left, (translPt A x).left] ![k, -k]
    (fun p => (fst T A).left ⁻¹ᵁ V p) (fun y => ⟨(fst T A).left y, hV _⟩) t ht
    (fun p q Z r r' z J hJ e => by
      rw [hv p Z r z J hJ, hv q Z r' z J hJ]
      exact tval_agree hG hA hL hn (hθ p) (hθ q) _ _ (by rw [Category.assoc, Category.assoc, hm, hm, e]) z J hJ)
  exact ⟨⟨x, u, hu⟩, rfl⟩

end GlobalTheory.SymLiftGlobal

namespace GlobalTheory

theorem exists_symLift_global : Laws → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (k : ℕ), Odd k →
    IsUnit (k : Γ(S, ⊤)) → ∀ (T : Over S) (x : T ⟶ P.A), x ^ k = 1 →
      ∃ θ : ThetaGrp P.A P.L k T, SymLift P.A P.L k k x θ := by
  intro hLaw S _ P k hk hu T x hx
  obtain ⟨θ, hθ⟩ := SymLiftGlobal.exists_lift_of_local hLaw.globalFns P.isAb P.isLB hk
    (hLaw.symLift S P k hk hu T x hx).1
  obtain ⟨nu, hnu⟩ := exists_gen_negLB hLaw.globalFns S P k T
  exact SymLiftOdd.exists_symLift hLaw.globalFns P.isAb P.isLB hk hx θ hθ hnu

end GlobalTheory
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.HomPairDescent

open GlobalTheory.Spread

theorem id_pow_left_comm {S S' : Scheme.{0}} {j : S' ⟶ S} {G : Over S} [GrpObj G] {G' : Over S'} [GrpObj G']
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G j φ) (m : ℕ) :
    (𝟙 G' ^ m : G' ⟶ G').left ≫ φ = φ ≫ (𝟙 G ^ m : G ⟶ G).left := by
  have e₁ := congrArg (fun a => a.left) (map_pow (pushHom h G') (𝟙 G') m)
  have e₂ := congrArg (fun a => a.left) (MonObj.comp_pow (𝟙 G) m (pushHom h G' (𝟙 G')))
  rw [Category.comp_id] at e₂
  refine e₁.trans (e₂.symm.trans ?_)
  change (𝟙 _ ≫ φ) ≫ _ = _
  rw [Category.id_comp]

theorem isGrpPullback_bcMap {k R S : Type} [CommRing k] [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]
    (A : Over (Sp k)) [GrpObj A] (ρ : R →ₐ[k] S) :
    IsGrpPullback ((Over.pullback (spMap (algebraMap k S))).obj A) ((Over.pullback (spMap (algebraMap k R))).obj A)
      (spMap ρ.toRingHom) (bcMap A.hom ρ) :=
  (isGrpPullback_pullback A _).cancel
    ((isGrpPullback_pullback A _).congr (spMap_algHom_comp ρ).symm (bcMap_fst A.hom ρ).symm) (bcMap_snd A.hom ρ)

theorem exists_descend {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] (A B : Over (Sp K))
    [QuasiCompact A.hom] [QuasiSeparated A.hom] [LocallyOfFinitePresentation B.hom]
    (f : (Over.pullback (spMap (algebraMap K Ω))).obj A ⟶ (Over.pullback (spMap (algebraMap K Ω))).obj B) :
    ∃ s : Finset Ω, ∀ L : IntermediateField K Ω, (s : Set Ω) ⊆ L →
      ∃ g : (Over.pullback (spMap (algebraMap K L))).obj A ⟶ (Over.pullback (spMap (algebraMap K L))).obj B,
        bcMap A.hom L.val ≫ g.left = f.left ≫ bcMap B.hom L.val := by
  have hfw : f.left ≫ pullback.snd _ _ = pullback.snd _ _ := Over.w f
  obtain ⟨R, ψ, ⟨s, rfl⟩, hψ, hψf⟩ := exists_fg_comp_eq A.hom B.hom (f.left ≫ pullback.fst _ _) (by
    rw [Category.assoc, pullback.condition, pullback.condition, ← Category.assoc]
    exact congrArg (· ≫ _) hfw)
  refine ⟨s, fun L hL => ?_⟩
  have hle : Algebra.adjoin K (s : Set Ω) ≤ L.toSubalgebra := Algebra.adjoin_le hL
  let ρ : Algebra.adjoin K (s : Set Ω) →ₐ[K] L := Subalgebra.inclusion hle
  have hw : (bcMap A.hom ρ ≫ ψ) ≫ B.hom = pullback.snd _ _ ≫ spMap (algebraMap K L) := by
    rw [Category.assoc, hψ, bcMap_fst_assoc, pullback.condition]
  let g₀ : pullback A.hom (spMap (algebraMap K L)) ⟶ pullback B.hom (spMap (algebraMap K L)) :=
    pullback.lift (bcMap A.hom ρ ≫ ψ) (pullback.snd _ _) hw
  let f₀ : pullback A.hom (spMap (algebraMap K Ω)) ⟶ pullback B.hom (spMap (algebraMap K Ω)) := f.left
  have hf₀ : f₀ ≫ pullback.snd _ _ = pullback.snd _ _ := hfw
  have hψ₀ : bcMap A.hom (Algebra.adjoin K (s : Set Ω)).val ≫ ψ = f₀ ≫ pullback.fst _ _ := hψf
  refine ⟨Over.homMk g₀ (pullback.lift_snd _ _ _), ?_⟩
  change bcMap A.hom L.val ≫ g₀ = f₀ ≫ bcMap B.hom L.val
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, bcMap_fst, pullback.lift_fst,
      bcMap_comp_of_eq_assoc A.hom ρ L.val (Algebra.adjoin K (s : Set Ω)).val fun _ ↦ rfl, hψ₀]
  · rw [Category.assoc, Category.assoc, bcMap_snd, pullback.lift_snd, bcMap_snd, reassoc_of% hf₀]

theorem comp_eq_pow_of_epi {S S' : Scheme.{0}} {j : S' ⟶ S} {G H : Over S} [GrpObj G] {G' H' : Over S'}
    [GrpObj G'] {φ : G'.left ⟶ G.left} {ψ : H'.left ⟶ H.left} (h : IsGrpPullback G' G j φ) [Epi φ]
    {a' : G' ⟶ H'} {b' : H' ⟶ G'} {a : G ⟶ H} {b : H ⟶ G}
    (ha : φ ≫ a.left = a'.left ≫ ψ) (hb : ψ ≫ b.left = b'.left ≫ φ) (m : ℕ)
    (e : a' ≫ b' = 𝟙 _ ^ m) : a ≫ b = 𝟙 _ ^ m := by
  apply Over.OverMorphism.ext
  rw [← cancel_epi φ, ← id_pow_left_comm h m, ← e, Over.comp_left, Over.comp_left, reassoc_of% ha, hb,
    Category.assoc]

end GlobalTheory.HomPairDescent

namespace GlobalTheory

open HomPairDescent Spread

theorem homPair_descends_to_finite : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω] (A B : Over (Sp K)) [GrpObj A] [GrpObj B], IsAbelianScheme A → IsAbelianScheme B → ∀ (i : (Over.pullback (spMap (algebraMap K Ω))).obj A ⟶ (Over.pullback (spMap (algebraMap K Ω))).obj B) (r : (Over.pullback (spMap (algebraMap K Ω))).obj B ⟶ (Over.pullback (spMap (algebraMap K Ω))).obj A), IsMonHom i → IsMonHom r → ∃ (L : IntermediateField K Ω) (_ : FiniteDimensional K L) (i' : (Over.pullback (spMap (algebraMap K L))).obj A ⟶ (Over.pullback (spMap (algebraMap K L))).obj B) (r' : (Over.pullback (spMap (algebraMap K L))).obj B ⟶ (Over.pullback (spMap (algebraMap K L))).obj A), IsMonHom i' ∧ IsMonHom r' ∧ ∀ m : ℕ, (i ≫ r = 𝟙 _ ^ m → i' ≫ r' = 𝟙 _ ^ m) ∧ (r ≫ i = 𝟙 _ ^ m → r' ≫ i' = 𝟙 _ ^ m) := by
  classical
  intro K Ω _ _ _ _ A B _ _ hA hB i r hi hr
  have := hA.proper
  have := hB.proper
  have := hA.smooth
  have := hB.smooth
  obtain ⟨s, hs⟩ := exists_descend A B i
  obtain ⟨t, ht⟩ := exists_descend B A r
  let L : IntermediateField K Ω := IntermediateField.adjoin K ((s ∪ t : Finset Ω) : Set Ω)
  have hL : ((s ∪ t : Finset Ω) : Set Ω) ⊆ L := IntermediateField.subset_adjoin _ _
  obtain ⟨i', hi'⟩ := hs L ((Finset.coe_subset.2 Finset.subset_union_left).trans hL)
  obtain ⟨r', hr'⟩ := ht L ((Finset.coe_subset.2 Finset.subset_union_right).trans hL)
  have hfin : FiniteDimensional K L :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  have gA := isGrpPullback_bcMap A L.val
  have gB := isGrpPullback_bcMap B L.val
  obtain ⟨hepi, hmon⟩ := FieldBaseChange.epi_and_isMonHom_iff L Ω L.val.toRingHom
  have eA := (hepi _ _ _ _ _ gA.1).1
  have eB := (hepi _ _ _ _ _ gB.1).1
  exact ⟨L, hfin, i', r', (hmon _ _ _ _ _ _ i' i gA gB hi').1 hi, (hmon _ _ _ _ _ _ r' r gB gA hr').1 hr,
    fun m => ⟨comp_eq_pow_of_epi gA hi' hr' m, comp_eq_pow_of_epi gB hr' hi' m⟩⟩

end GlobalTheory
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
open GlobalTheory.ModelData

theorem _root_.GlobalTheory.T.degenerationIso_comm_induced_label_maps : ∀ (C : Type) [NormedField C] (N N' : NumD C) (La : Type) [AddCommGroup La] (EF : LinearMap.BilinForm ℤ La) (ζ ζ' : ℕ → Cˣ) (lab : ∀ k : ℕ, La → N.QT k) (lab' : ∀ k : ℕ, La → N'.QT k) (n : ℕ), 1 < n → Labels N EF ζ lab → Labels N' EF ζ' lab' → ∀ J : NumD.Iso N N', (∀ j (p : N.QT (n ^ j)) (p' : N'.QT (n ^ j)), p'.1.1.toAdd = J.e p.1.1.toAdd → J.Rel p.1.2 p'.1.2 → ∃ x, N.QEq (lab _ x) p ∧ N'.QEq (lab' _ x) p') → (∀ j (y : N.X), ∃ p : N.QT (n ^ j), p.1.1.toAdd = y) → ∀ (α : N.X →+ N.X) (α' : N'.X →+ N'.X) (gam : La → La), (∀ j x, ∃ z, (lab (n ^ j) (gam x)).1.1.toAdd = α (lab (n ^ j) x).1.1.toAdd + n ^ j • z) → (∀ j x, ∃ z, (lab' (n ^ j) (gam x)).1.1.toAdd = α' (lab' (n ^ j) x).1.1.toAdd + n ^ j • z) → ∀ y, J.e (α y) = α' (J.e y) := by
  first | exact @GlobalTheory.ModelData.iso_comm_of_labels | exact GlobalTheory.ModelData.iso_comm_of_labels | (intros; apply GlobalTheory.ModelData.iso_comm_of_labels <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite

theorem _root_.GlobalTheory.T.exists_section_pullback_mul_generator : ∀ (k : Type) [Field k] [IsAlgClosed k] (Φ : FibPre k) (Y : Scheme.{0}) (L : LB Y), L.IsLB → ∀ (π : Φ.E.B.left ⟶ Y) (N : ℕ) (c : ChartPull Φ.N₀ (npw L N) π) (K K' : Type) [Fintype K] [Fintype K'] (ψ : K → (Φ.E.B.left ⟶ Y)) (ε : K → ℤ) (φt : K' → (Φ.G.left ⟶ Y)) (εt : K' → ℤ) (t : LB.Gen (LB.LinComb L φt εt)), t.IsGen → FormEq (Sum.elim (fun a => Φ.D.q.left ≫ ψ a) φt) (Sum.elim ε εt) (fun _ : Fin 1 => Φ.D.q.left ≫ π) (fun _ => (N : ℤ)) → ∀ b : LB.Sec (LB.LinComb L ψ ε), ∃ φ : (Φ.H 1).Sec, UFib.Red Φ c t b φ := by
  first | exact @GlobalTheory.ZH.UFib.exists_red | exact GlobalTheory.ZH.UFib.exists_red | (intros; apply GlobalTheory.ZH.UFib.exists_red <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite

theorem _root_.GlobalTheory.T.isLinComb_iff_pullback_mul_generator : ∀ (k : Type) [Field k] [IsAlgClosed k] (Φ : FibPre k) (Y : Scheme.{0}) (L : LB Y), L.IsLB → ∀ (π : Φ.E.B.left ⟶ Y) (N : ℕ) (c : ChartPull Φ.N₀ (npw L N) π) (K K' : Type) [Fintype K] [Fintype K'] (ψ : K → (Φ.E.B.left ⟶ Y)) (ε : K → ℤ) (φt : K' → (Φ.G.left ⟶ Y)) (εt : K' → ℤ) (t : LB.Gen (LB.LinComb L φt εt)), t.IsGen → ∀ (I : Type) [Fintype I] (b : I → LB.Sec (LB.LinComb L ψ ε)) (φ : I → (Φ.H 1).Sec) (b₀ : LB.Sec (LB.LinComb L ψ ε)) (φ₀ : (Φ.H 1).Sec) (a : I → k), (∀ i, UFib.Red Φ c t (b i) (φ i)) → UFib.Red Φ c t b₀ φ₀ → (IsLin Φ.E.B.hom b a b₀ ↔ IsLin Φ.G.hom φ a φ₀) := by
  first | exact @GlobalTheory.ZH.UFib.isLin_iff_of_red | exact GlobalTheory.ZH.UFib.isLin_iff_of_red | (intros; apply GlobalTheory.ZH.UFib.isLin_iff_of_red <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH

noncomputable section
namespace GlobalTheory.ZH.RatModel

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω)

theorem eq_of_res_eq_of_nonempty {U : M.Z.Opens} {f g : Γ(M.Z, U)}
    (h : ∀ hU : (U : Set M.Z).Nonempty, M.res U hU f = M.res U hU g) : f = g := by
  by_cases hU : (U : Set M.Z).Nonempty
  · exact M.res_injective U hU (h hU)
  · obtain rfl : U = ⊥ := SetLike.coe_injective (Set.not_nonempty_iff_eq_empty.1 hU)
    exact Subsingleton.elim _ _

theorem exists_unit_res_eq {U : M.Z.Opens} {x : Ω} (hx : x ≠ 0) (h : ∀ z ∈ U, x ∈ M.O z)
    (h' : ∀ z ∈ U, x⁻¹ ∈ M.O z) :
    ∃ g : Γ(M.Z, U)ˣ, ∀ hU : (U : Set M.Z).Nonempty, M.res U hU (g : Γ(M.Z, U)) = x := by
  by_cases hU : (U : Set M.Z).Nonempty
  · obtain ⟨a, ha⟩ := (mem_ringOn_iff_exists hU).1 (mem_ringOn.2 h)
    obtain ⟨b, hb⟩ := (mem_ringOn_iff_exists hU).1 (mem_ringOn.2 h')
    have hab : a * b = 1 := M.res_injective U hU (by
      rw [map_mul, map_one, res_apply, res_apply, ha, hb, mul_inv_cancel₀ hx])
    exact ⟨⟨a, b, hab, (mul_comm _ _).trans hab⟩, fun _ => (M.res_apply U hU a).trans ha⟩
  · exact ⟨1, fun h => (hU h).elim⟩

theorem exists_isLB_genTriv_of_ratios : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (ι : Type) (U : ι → M.Z.Opens) (d : ι → Ω), ⨆ k, U k = ⊤ → (∀ k, d k ≠ 0) → (∀ k k', ∀ z ∈ U k ⊓ U k', d k' / d k ∈ M.O z) → ∃ g : ∀ k k', Γ(M.Z, U k ⊓ U k')ˣ, (⟨ι, U, g⟩ : LB M.Z).IsLB ∧ M.GenTriv ⟨ι, U, g⟩ d := by
  intro o Ω _ _ _ M ι U d hU hd hr
  have key : ∀ k k', ∃ g : Γ(M.Z, U k ⊓ U k')ˣ, ∀ h : ((U k ⊓ U k' : M.Z.Opens) : Set M.Z).Nonempty,
      M.res _ h (g : Γ(M.Z, U k ⊓ U k')) = d k' / d k := fun k k' =>
    M.exists_unit_res_eq (div_ne_zero (hd k') (hd k)) (hr k k') fun z hz => by
      rw [inv_div]
      exact hr k' k z ⟨hz.2, hz.1⟩
  choose g hg using key
  have hres : ∀ k k' {V : M.Z.Opens} (h : V ≤ U k ⊓ U k') (hV : (V : Set M.Z).Nonempty),
      M.res V hV ((Semi.res h (g k k') : Γ(M.Z, V)ˣ) : Γ(M.Z, V)) = d k' / d k := fun k k' V h hV =>
    (M.res_resG h hV _).trans (hg k k' _)
  refine ⟨g, ⟨hU, fun i => Units.ext (M.eq_of_res_eq_of_nonempty fun hV => ?_),
    fun i j k => Units.ext (M.eq_of_res_eq_of_nonempty fun hV => ?_)⟩,
    ⟨hd, fun k k' h => (M.res_apply _ h _).symm.trans (hg k k' h)⟩⟩
  · refine (hres i i _ hV).trans ?_
    rw [div_self (hd i), Units.val_one, map_one]
  · rw [Units.val_mul, map_mul]
    refine (congrArg₂ (· * ·) (hres i j _ hV) (hres j k _ hV)).trans (Eq.trans ?_ (hres i k _ hV).symm)
    have := hd i
    have := hd j
    field_simp

end GlobalTheory.ZH.RatModel
end
end

section

open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH

noncomputable section
namespace GlobalTheory.ZH.RatModel

open GlobalTheory.Points

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M : RatModel o Ω} {H : LB M.Z} {d : H.ι → Ω}

theorem GenTriv.exists_sec_hasVal (h : M.GenTriv H d) (x : Ω) (hx : ∀ k, ∀ z ∈ H.U k, x / d k ∈ M.O z) :
    ∃ σ : H.Sec, M.HasVal d σ x := by
  have hf : ∀ k, ∃ f : Γ(M.Z, H.U k), (H.U k : Set M.Z).Nonempty → valF M.pt (H.U k) f = x / d k := fun k => by
    by_cases hk : (H.U k : Set M.Z).Nonempty
    · obtain ⟨f, hf⟩ := (mem_ringOn_iff_exists hk).1 (mem_ringOn.2 (hx k))
      exact ⟨f, fun _ => hf⟩
    · exact ⟨0, fun h => (hk h).elim⟩
  choose f hf using hf
  refine ⟨⟨f, fun i j => ?_⟩, hf⟩
  by_cases hij : ((H.U i ⊓ H.U j : M.Z.Opens) : Set M.Z).Nonempty
  · refine M.res_injective _ hij ?_
    have h1 := (M.res_apply _ hij _).trans ((M.valF_resG inf_le_left hij (f i)).trans
      (hf i (hij.mono (fun _ hz => (show _ ∈ H.U i ∧ _ ∈ H.U j from hz).1))))
    have h2 := (M.res_apply _ hij _).trans ((M.valF_resG inf_le_right hij (f j)).trans
      (hf j (hij.mono (fun _ hz => (show _ ∈ H.U i ∧ _ ∈ H.U j from hz).2))))
    have h3 := (M.res_apply _ hij _).trans (h.g_eq i j hij)
    rw [map_mul, h3]
    refine h1.trans (Eq.trans ?_ (congrArg (d j / d i * ·) h2.symm))
    have := h.ne i
    have := h.ne j
    field_simp
  · have e : (H.U i ⊓ H.U j : M.Z.Opens) = ⊥ :=
      SetLike.coe_injective (Set.not_nonempty_iff_eq_empty.1 hij)
    have : Subsingleton Γ(M.Z, H.U i ⊓ H.U j) := by
      rw [e]; infer_instance
    exact Subsingleton.elim _ _

theorem GenTriv.pull (h : M.GenTriv H d) {Ω' : Type} [Field Ω'] [Algebra o Ω'] {φ : Ω →ₐ[o] Ω'}
    {N : RatModel o Ω'} {a : N.Z ⟶ M.Z} (ha : M.IsHom N φ a) :
    N.GenTriv (H.pull a) fun k => φ (d (k PUnit.unit)) := by
  refine ⟨fun k => (map_ne_zero φ).2 (h.ne _), fun k k' hk => ?_⟩
  have hle : (H.pull a).U k ⊓ (H.pull a).U k' ≤ a ⁻¹ᵁ (H.U (k PUnit.unit) ⊓ H.U (k' PUnit.unit)) :=
    le_inf (inf_le_left.trans (LB.wchart_le H (fun _ => a) k PUnit.unit))
      (inf_le_right.trans (LB.wchart_le H (fun _ => a) k' PUnit.unit))
  have hne : ((H.U (k PUnit.unit) ⊓ H.U (k' PUnit.unit) : M.Z.Opens) : Set M.Z).Nonempty := by
    obtain ⟨z, hz⟩ := hk
    exact ⟨a z, hle hz⟩
  have e : ((H.pull a).g k k' : Γ(N.Z, (H.pull a).U k ⊓ (H.pull a).U k')) =
      resG N.Z hle (a.app _ (H.g (k PUnit.unit) (k' PUnit.unit) : Γ(M.Z, _))) := by
    have e0 : (H.pull a).g k k' = Semi.res hle (pullU a _ (H.g (k PUnit.unit) (k' PUnit.unit))) :=
      (Fintype.prod_unique (ι := PUnit) fun _ =>
        Semi.res hle (pullU a _ (H.g (k PUnit.unit) (k' PUnit.unit))) ^ (1 : ℤ)).trans (zpow_one _)
    exact congrArg Units.val e0
  rw [e, N.valF_resG hle hk, ha.valF_app hne, h.g_eq _ _ hne, map_div₀]

theorem genTriv_sec_and_pull : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (H : LB M.Z)
    (d : H.ι → Ω), M.GenTriv H d →
    (∀ x : Ω, (∀ k, ∀ z ∈ H.U k, x / d k ∈ M.O z) → ∃ σ : H.Sec, M.HasVal d σ x) ∧
    ∀ (Ω' : Type) [Field Ω'] [Algebra o Ω'] (φ : Ω →ₐ[o] Ω') (N : RatModel o Ω') (a : N.Z ⟶ M.Z),
      M.IsHom N φ a → N.GenTriv (H.pull a) fun k => φ (d (k PUnit.unit)) :=
  fun _ _ _ _ _ _ _ _ h => ⟨h.exists_sec_hasVal, fun _ _ _ _ _ _ ha => h.pull ha⟩

end GlobalTheory.ZH.RatModel
end
end
