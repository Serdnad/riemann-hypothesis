module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle561
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle562
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle730
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologyRestrictBasisExtendedBijective
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle019
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle117
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle026
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianUnobstructed
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle028
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle985
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AbelianVarietyTheory.PublishedTheorems.AbelianLaws.PrincipalPolarisationOneSection
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.LBObs

theorem isObU_pull : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R₀) (L : Pre I π F) (C' : Type) [Category.{0} C'] (F' : C' ⥤ CommAlgCat.{0} R₀) (L' : Pre I π F') (n : CoefMap (RingHom.id R₀) F F') (l : ∀ T : C', L.B (n.G.obj T) →ₐ[R] L'.B T) (u : ∀ (T T' : C) (_ : T ⟶ T'), (F.obj T')ˣ) (u' : ∀ (T T' : C') (_ : T ⟶ T'), (F'.obj T')ˣ) (c : GlobalTheory.CatCoh.H2 (ext R₁ F)), L.IsLift L' n l → L.IsNat L' n l → (∀ T T' a, (u' T T' a : F'.obj T') = n.α T' (u _ _ (n.G.map a) : F.obj (n.G.obj T'))) → IsObU L α u c → IsObU L' α u' ((extMap R₁ n).pull2 c) := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α C _ F L C' _ F' L' n l u u' c hL hN hu hob
  obtain ⟨v, σ, z, hv, hσ, hc, hz⟩ := hob
  have hex : ∀ T, ∃ s : R₁ ⊗[R₀] F'.obj T →+ L'.B T, α.IsSig (L'.p T) s := fun T =>
    GlobalTheory.Obs.exists_isSig R R₀ I hI π hπ hk R₁ α (L'.B T) (F'.obj T) (L'.p T) (L'.semi T) (L'.surj T) (L'.ker T)
  choose σ' hσ' using hex
  have hnat : ∀ T : C', (∀ y, l T (σ (n.G.obj T) y) = σ' T (extHom R₁ (coefHom n T) y)) ∧
      ∀ y, α.KerQ y → α.KerQ (extHom R₁ (coefHom n T) y) := fun T =>
    GlobalTheory.Obs.sig_natural R R₀ I hI π hπ hk R₁ α _ _ (L.p (n.G.obj T)) (L.semi _) (L.surj _) (L.ker _)
      _ _ (L'.p T) (L'.semi T) (L'.surj T) (L'.ker T) (l T) (coefHom n T) (fun b => hL T b) _ _ (hσ _) (hσ' T)
  refine ⟨fun T T' a => Units.map (l T').toRingHom.toMonoidHom (v _ _ (n.G.map a)), σ', (extMap R₁ n).pullbackTwoCocycle z,
    ?_, hσ', ?_, ?_⟩
  · intro T T' a
    change L'.p T' (l T' _) = _
    rw [hL, hv, hu]
  · rw [hc]; rfl
  · intro T T' T'' a b
    obtain ⟨hk1, hk2⟩ := hz _ _ _ (n.G.map a) (n.G.map b)
    refine ⟨(hnat T'').2 _ hk1, ?_⟩
    change L'.ρ b (l T' _) * l T'' _ = (1 + σ' T'' (extHom R₁ (coefHom n T'') _)) * l T'' _
    rw [hN, ← map_mul, hk2, map_mul, map_add (f := _), map_one, (hnat T'').1, Functor.map_comp]
    rfl

end GlobalTheory.LBObs
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LBObs.PairInj

theorem pull2_pairRes_restrict (R₀ R₁ : Type) [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁] {X₀ Z₀ : Scheme.{0}}
    (t₀ : Z₀ ⟶ Sp R₀) (f₀ : Z₀ ⟶ X₀) {D : Type} [Category.{0} D] (K : D ⥤ (Pair f₀)ᵒᵖ)
    (c : CatCoh.H2 (ext R₁ (OAff t₀))) :
    (extMap R₁ (CoefMap.restrict (OPair f₀ t₀) K)).pull2 ((extMap R₁ (pairRes f₀ t₀)).pull2 c) =
      (extMap R₁ (CoefMap.restrict (OAff t₀) (K ⋙ pairFst f₀))).pull2 c := by
  obtain ⟨z, rfl⟩ := H2.mk_surjective _ c
  rw [CoefMap.pullCohomologyTwo_class, CoefMap.pullCohomologyTwo_class, CoefMap.pullCohomologyTwo_class]
  refine congrArg _ (Subtype.ext ?_)
  funext T T' T'' a b
  show extHom R₁ (coefHom (CoefMap.restrict (OPair f₀ t₀) K) T'')
      (extHom R₁ (coefHom (pairRes f₀ t₀) (K.obj T'')) _) =
    extHom R₁ (coefHom (CoefMap.restrict (OAff t₀) (K ⋙ pairFst f₀)) T'') _
  exact (PairExt.extHom_of_id R₁ _ (fun _ ↦ rfl) _).trans ((PairExt.extHom_of_id R₁ _ (fun _ ↦ rfl) _).trans
    (PairExt.extHom_of_id R₁ _ (fun _ ↦ rfl) _).symm)

theorem restrict_pair_injective : ∀ (R₀ R₁ : Type) [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁] (X₀ Z₀ : Scheme.{0}) (t₀ : Z₀ ⟶ Sp R₀) (f₀ : Z₀ ⟶ X₀) (D : Type) [Category.{0} D] [Quiver.IsThin D] (K : D ⥤ (Pair f₀)ᵒᵖ), IsBas (opOf (K ⋙ pairFst f₀)) → Function.Injective (extMap R₁ (CoefMap.restrict (OPair f₀ t₀) K)).pull2 := by
  intro R₀ R₁ _ _ _ X₀ Z₀ t₀ f₀ D _ _ K hB x y e
  have hG := (BasisExt.restrict_ext_bijective R₀ R₁ Z₀ t₀ D (K ⋙ pairFst f₀) hB.1 hB.2).2.1
  have hP := ((PairExt.pairRes_ext_bijective R₀ R₁ X₀ Z₀ t₀ f₀).1.2).2
  obtain ⟨x0, rfl⟩ := hP x
  obtain ⟨y0, rfl⟩ := hP y
  rw [pull2_pairRes_restrict, pull2_pairRes_restrict] at e
  rw [hG e]

end GlobalTheory.LBObs.PairInj
end
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LBObs

theorem isFrame_tens : ∀ (X : Scheme.{0}) (C : Type) [Category.{0} C] (V : C → X.Opens)
    (hV : ∀ ⦃T T' : C⦄, (T ⟶ T') → V T' ≤ V T) (L L' : LB X) (u u' : ∀ (T T' : C) (_ : T ⟶ T'), Γ(X, V T')ˣ),
    IsFrame L V hV u → IsFrame L' V hV u' → IsFrame (tens L L') V hV fun T T' a ↦ u T T' a * u' T T' a := by
  intro X C _ V hV L L' u u' ⟨τ, hτg, hτf⟩ ⟨τ', hτ'g, hτ'f⟩
  dsimp only [IsFrame, IsGenOn, tens]
  refine ⟨fun T p ↦ res (inf_le_inf_left (V T) (inf_le_left : L.U p.1 ⊓ L'.U p.2 ≤ L.U p.1)) (τ T p.1) *
      res (inf_le_inf_left (V T) (inf_le_right : L.U p.1 ⊓ L'.U p.2 ≤ L'.U p.2)) (τ' T p.2), ?_, ?_⟩
  · intro T p q
    refine unit_ext fun y hy ↦ ?_
    have h1 := congrArg (gm (𝟙 X) y _) (hτg T p.1 q.1)
    have h2 := congrArg (gm (𝟙 X) y _) (hτ'g T p.2 q.2)
    have m1 : (𝟙 X : X ⟶ X) y ∈ V T ⊓ L.U p.1 ⊓ L.U q.1 := ⟨⟨hy.1.1, hy.1.2.1⟩, hy.2.1⟩
    have m2 : (𝟙 X : X ⟶ X) y ∈ V T ⊓ L'.U p.2 ⊓ L'.U q.2 := ⟨⟨hy.1.1, hy.1.2.2⟩, hy.2.2⟩
    have m3 : (𝟙 X : X ⟶ X) y ∈ L.U p.1 ⊓ L'.U p.2 ⊓ (L.U q.1 ⊓ L'.U q.2) := ⟨hy.1.2, hy.2⟩
    have m4 : (𝟙 X : X ⟶ X) y ∈ V T ⊓ (L.U p.1 ⊓ L'.U p.2) := hy.1
    have m5 : (𝟙 X : X ⟶ X) y ∈ V T ⊓ (L.U q.1 ⊓ L'.U q.2) := ⟨hy.1.1, hy.2⟩
    simp only [map_mul, gm_res (𝟙 X) y _ m1] at h1
    simp only [map_mul, gm_res (𝟙 X) y _ m2] at h2
    simp only [map_mul, gm_res (𝟙 X) y _ hy, gm_res (𝟙 X) y _ m3, gm_res (𝟙 X) y _ m4, gm_res (𝟙 X) y _ m5]
    rw [h1, h2]
    ac_rfl
  · intro T T' a p
    refine unit_ext fun y hy ↦ ?_
    have h1 := congrArg (gm (𝟙 X) y _) (hτf T T' a p.1)
    have h2 := congrArg (gm (𝟙 X) y _) (hτ'f T T' a p.2)
    have m1 : (𝟙 X : X ⟶ X) y ∈ V T' ⊓ L.U p.1 := ⟨hy.1, hy.2.1⟩
    have m2 : (𝟙 X : X ⟶ X) y ∈ V T' ⊓ L'.U p.2 := ⟨hy.1, hy.2.2⟩
    have m3 : (𝟙 X : X ⟶ X) y ∈ V T ⊓ (L.U p.1 ⊓ L'.U p.2) := ⟨hV a hy.1, hy.2⟩
    simp only [map_mul, gm_res (𝟙 X) y _ m1] at h1
    simp only [map_mul, gm_res (𝟙 X) y _ m2] at h2
    simp only [map_mul, gm_res (𝟙 X) y _ hy, gm_res (𝟙 X) y _ m1, gm_res (𝟙 X) y _ m2, gm_res (𝟙 X) y _ m3]
    rw [h1, h2]
    ac_rfl

end GlobalTheory.LBObs
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.LBObs

theorem gm_id_res' {X : Scheme.{0}} {U V : X.Opens} (hle : V ≤ U) {x : X} (hx : x ∈ V) (a : Γ(X, U)ˣ) :
    gm (𝟙 X) x V (ReciprocityTheory.ChartRestriction.G.Semi.res hle a) = gm (𝟙 X) x U a :=
  gm_res (𝟙 X) x hle hx a

theorem lbIso_of_isFrame : ∀ (X : Scheme.{0}) (C : Type) [Category.{0} C] (V : C → X.Opens) (hV : ∀ ⦃T T' : C⦄, (T ⟶ T') → V T' ≤ V T) [Quiver.IsThin C] (L L' : LB X) (u : ∀ (T T' : C) (_ : T ⟶ T'), Γ(X, V T')ˣ), IsBas V → L.IsLB → L'.IsLB → IsFrame L V hV u → IsFrame L' V hV u → LBIso L L' := by
  intro X C _ V hV _ L L' u hB _ _ hF hF'
  obtain ⟨τ, hτg, hτ⟩ := hF
  obtain ⟨τ', hτ'g, hτ'⟩ := hF'

  have e : ∀ (T T' : C) (a : T ⟶ T') (m : L.ι) (x : X) (hx : x ∈ V T' ⊓ L.U m),
      gm (𝟙 X) x _ (τ T m) = gm (𝟙 X) x _ (u T T' a) * gm (𝟙 X) x _ (τ T' m) := by
    intro T T' a m x hx
    have h := congrArg (gm (𝟙 X) x (V T' ⊓ L.U m)) (hτ T T' a m)
    rwa [map_mul, gm_id_res' _ hx, gm_id_res' _ hx] at h
  have e' : ∀ (T T' : C) (a : T ⟶ T') (m : L'.ι) (x : X) (hx : x ∈ V T' ⊓ L'.U m),
      gm (𝟙 X) x _ (τ' T m) = gm (𝟙 X) x _ (u T T' a) * gm (𝟙 X) x _ (τ' T' m) := by
    intro T T' a m x hx
    have h := congrArg (gm (𝟙 X) x (V T' ⊓ L'.U m)) (hτ' T T' a m)
    rwa [map_mul, gm_id_res' _ hx, gm_id_res' _ hx] at h

  have key : ∀ (T₁ T₂ : C) (m : L.ι) (m' : L'.ι) (x : X), x ∈ V T₁ → x ∈ V T₂ → x ∈ L.U m → x ∈ L'.U m' →
      gm (𝟙 X) x (V T₁ ⊓ L'.U m') (τ' T₁ m') / gm (𝟙 X) x (V T₁ ⊓ L.U m) (τ T₁ m) =
        gm (𝟙 X) x (V T₂ ⊓ L'.U m') (τ' T₂ m') / gm (𝟙 X) x (V T₂ ⊓ L.U m) (τ T₂ m) := by
    intro T₁ T₂ m m' x h1 h2 hm hm'
    obtain ⟨T₃, ⟨a⟩, ⟨b⟩, h3, -⟩ := hB.2 T₁ T₂ x ⊤ trivial h1 h2
    rw [e T₁ T₃ a m x ⟨h3, hm⟩, e' T₁ T₃ a m' x ⟨h3, hm'⟩, e T₂ T₃ b m x ⟨h3, hm⟩, e' T₂ T₃ b m' x ⟨h3, hm'⟩,
      mul_div_mul_left_eq_div, mul_div_mul_left_eq_div]

  have hglue : ∀ p : L'.ι × L.ι, ∃ s : Γ(X, L'.U p.1 ⊓ L.U p.2)ˣ, ∀ (T : C) (x : X),
      x ∈ V T → x ∈ L'.U p.1 ⊓ L.U p.2 →
        gm (𝟙 X) x _ s = gm (𝟙 X) x (V T ⊓ L'.U p.1) (τ' T p.1) / gm (𝟙 X) x (V T ⊓ L.U p.2) (τ T p.2) := by
    intro p
    obtain ⟨s, hs⟩ := glue_unit (L'.U p.1 ⊓ L.U p.2) (fun T => V T ⊓ (L'.U p.1 ⊓ L.U p.2)) (fun T => inf_le_right)
      (fun x hx => by
        obtain ⟨T, hT, -⟩ := hB.1 x ⊤ trivial
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨T, hT, hx⟩)
      (fun T => ReciprocityTheory.ChartRestriction.G.Semi.res (inf_le_inf_left (V T) inf_le_left) (τ' T p.1) /
        ReciprocityTheory.ChartRestriction.G.Semi.res (inf_le_inf_left (V T) inf_le_right) (τ T p.2))
      (fun T₁ T₂ x hx => by
        simp only [map_div]
        rw [gm_id_res' _ hx.1, gm_id_res' _ hx.1, gm_id_res' _ hx.2, gm_id_res' _ hx.2]
        exact key T₁ T₂ p.2 p.1 x hx.1.1 hx.2.1 hx.1.2.2 hx.1.2.1)
    refine ⟨s, fun T x hT hx => ?_⟩
    have h := congrArg (gm (𝟙 X) x (V T ⊓ (L'.U p.1 ⊓ L.U p.2))) (hs T)
    simp only [map_div] at h
    have hTx : x ∈ V T ⊓ (L'.U p.1 ⊓ L.U p.2) := ⟨hT, hx⟩
    rwa [gm_id_res' _ hTx, gm_id_res' _ hTx, gm_id_res' _ hTx] at h
  choose w hw using hglue
  refine ⟨⟨w⟩, fun p q => ?_⟩
  apply ReciprocityTheory.ChartRestriction.G.Geo.Tor.unit_ext
  intro x hx
  obtain ⟨T, hT, -⟩ := hB.1 x ⊤ trivial
  have hp : x ∈ L'.U p.1 ⊓ L.U p.2 := hx.1
  have hq : x ∈ L'.U q.1 ⊓ L.U q.2 := hx.2

  have g1 := congrArg (gm (𝟙 X) x _) (hτ'g T p.1 q.1)
  have g2 := congrArg (gm (𝟙 X) x _) (hτg T p.2 q.2)
  have hx1 : x ∈ V T ⊓ L'.U p.1 ⊓ L'.U q.1 := ⟨⟨hT, hp.1⟩, hq.1⟩
  have hx2 : x ∈ V T ⊓ L.U p.2 ⊓ L.U q.2 := ⟨⟨hT, hp.2⟩, hq.2⟩
  rw [map_mul, gm_id_res' _ hx1, gm_id_res' _ hx1, gm_id_res' _ hx1] at g1
  rw [map_mul, gm_id_res' _ hx2, gm_id_res' _ hx2, gm_id_res' _ hx2] at g2
  have hwp : gm (𝟙 X) x ((L'.div L).U p ⊓ (L'.div L).U q)
      (ReciprocityTheory.ChartRestriction.G.Semi.res (inf_le_left : (L'.div L).U p ⊓ (L'.div L).U q ≤ (L'.div L).U p) (w p)) =
      gm (𝟙 X) x ((L'.div L).U p) (w p) := gm_id_res' _ hx _
  have hwq : gm (𝟙 X) x ((L'.div L).U p ⊓ (L'.div L).U q)
      (ReciprocityTheory.ChartRestriction.G.Semi.res (inf_le_right : (L'.div L).U p ⊓ (L'.div L).U q ≤ (L'.div L).U q) (w q)) =
      gm (𝟙 X) x ((L'.div L).U q) (w q) := gm_id_res' _ hx _
  have hx' : x ∈ L'.U p.1 ⊓ L.U p.2 ⊓ (L'.U q.1 ⊓ L.U q.2) := hx
  have hg : gm (𝟙 X) x ((L'.div L).U p ⊓ (L'.div L).U q) ((L'.div L).g p q) =
      gm (𝟙 X) x (L'.U p.1 ⊓ L'.U q.1) (L'.g p.1 q.1) * (gm (𝟙 X) x (L.U p.2 ⊓ L.U q.2) (L.g p.2 q.2))⁻¹ := by
    show gm (𝟙 X) x (L'.U p.1 ⊓ L.U p.2 ⊓ (L'.U q.1 ⊓ L.U q.2))
      (ReciprocityTheory.ChartRestriction.G.Semi.res _ (L'.g p.1 q.1) * (ReciprocityTheory.ChartRestriction.G.Semi.res _ (L.g p.2 q.2))⁻¹) = _
    rw [map_mul, map_inv, gm_id_res' _ hx', gm_id_res' _ hx']
  rw [map_mul, hwp, hwq, hg]
  erw [hw p T x hT hp, hw q T x hT hq]
  rw [g1, g2]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ac_rfl

end GlobalTheory.LBObs
end
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GenRatio

variable {X : Scheme.{0}}

theorem comm_identity {M : Type} [CommGroup M] (B G G' Q Q' : M) :
    G' * G⁻¹ * B * (G * Q) * (G' * Q')⁻¹ = B * Q * Q'⁻¹ := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem gm_isGenOn {L : LB X} {W : X.Opens} {τ : ∀ m : L.ι, Γ(X, W ⊓ L.U m)ˣ} (hτ : IsGenOn L W τ)
    {x : X} {m n : L.ι} (hx : x ∈ W) (hm : x ∈ L.U m) (hn : x ∈ L.U n) :
    gm (𝟙 X) x _ (τ m) = gm (𝟙 X) x _ (L.g m n) * gm (𝟙 X) x _ (τ n) := by
  have hmem : x ∈ W ⊓ L.U m ⊓ L.U n := ⟨⟨hx, hm⟩, hn⟩
  have := congrArg (gm (𝟙 X) x _) (hτ m n)
  rwa [map_mul, gm_res _ x _ hmem, gm_res _ x _ hmem, gm_res _ x _ hmem] at this

def isoAt {L L' : LB X} (w : LB.Iso L L') (m' : L'.ι) (m : L.ι) : Γ(X, L'.U m' ⊓ L.U m)ˣ := w.s (m', m)

theorem isoAt_compat {L L' : LB X} {w : LB.Iso L L'} (hw : w.IsGen) (m n : L.ι) (m' n' : L'.ι) :
    res (inf_le_left : L'.U m' ⊓ L.U m ⊓ (L'.U n' ⊓ L.U n) ≤ L'.U m' ⊓ L.U m) (isoAt w m' m) =
      res (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left) :
        L'.U m' ⊓ L.U m ⊓ (L'.U n' ⊓ L.U n) ≤ L'.U m' ⊓ L'.U n') (L'.g m' n') *
      (res (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) :
        L'.U m' ⊓ L.U m ⊓ (L'.U n' ⊓ L.U n) ≤ L.U m ⊓ L.U n) (L.g m n))⁻¹ *
      res (inf_le_right : L'.U m' ⊓ L.U m ⊓ (L'.U n' ⊓ L.U n) ≤ L'.U n' ⊓ L.U n) (isoAt w n' n) :=
  hw (m', m) (n', n)

theorem gm_iso {L L' : LB X} {w : LB.Iso L L'} (hw : w.IsGen) {x : X} {m n : L.ι} {m' n' : L'.ι}
    (hm : x ∈ L.U m) (hn : x ∈ L.U n) (hm' : x ∈ L'.U m') (hn' : x ∈ L'.U n') :
    gm (𝟙 X) x _ (isoAt w m' m) =
      gm (𝟙 X) x _ (L'.g m' n') * (gm (𝟙 X) x _ (L.g m n))⁻¹ * gm (𝟙 X) x _ (isoAt w n' n) := by
  have hmem : x ∈ L'.U m' ⊓ L.U m ⊓ (L'.U n' ⊓ L.U n) := ⟨⟨hm', hm⟩, ⟨hn', hn⟩⟩
  have := congrArg (gm (𝟙 X) x _) (isoAt_compat hw m n m' n')
  rwa [map_mul, map_mul, map_inv, gm_res _ x _ hmem, gm_res _ x _ hmem, gm_res _ x _ hmem,
    gm_res _ x _ hmem] at this

def ratioLoc (L L' : LB X) (W : X.Opens) (w : LB.Iso L L') (τ : ∀ m : L.ι, Γ(X, W ⊓ L.U m)ˣ)
    (τ' : ∀ m : L'.ι, Γ(X, W ⊓ L'.U m)ˣ) (m' : L'.ι) (m : L.ι) : Γ(X, W ⊓ (L'.U m' ⊓ L.U m))ˣ :=
  res (inf_le_right : W ⊓ (L'.U m' ⊓ L.U m) ≤ L'.U m' ⊓ L.U m) (isoAt w m' m) *
    res (inf_le_inf_left W inf_le_right : W ⊓ (L'.U m' ⊓ L.U m) ≤ W ⊓ L.U m) (τ m) *
    (res (inf_le_inf_left W inf_le_left : W ⊓ (L'.U m' ⊓ L.U m) ≤ W ⊓ L'.U m') (τ' m'))⁻¹

theorem gm_ratioLoc (L L' : LB X) (W : X.Opens) (w : LB.Iso L L') (τ : ∀ m : L.ι, Γ(X, W ⊓ L.U m)ˣ)
    (τ' : ∀ m : L'.ι, Γ(X, W ⊓ L'.U m)ˣ) (m : L.ι) (m' : L'.ι) {x : X} (hx : x ∈ W ⊓ (L'.U m' ⊓ L.U m)) :
    gm (𝟙 X) x _ (ratioLoc L L' W w τ τ' m' m) =
      gm (𝟙 X) x _ (isoAt w m' m) * gm (𝟙 X) x _ (τ m) * (gm (𝟙 X) x _ (τ' m'))⁻¹ := by
  rw [ratioLoc, map_mul, map_mul, map_inv, gm_res _ x _ hx, gm_res _ x _ hx, gm_res _ x _ hx]

theorem exists_unique_ratio : ∀ (X : Scheme.{0}) (L L' : LB X) (W : X.Opens) (w : LB.Iso L L') (τ : ∀ m : L.ι, Γ(X, W ⊓ L.U m)ˣ) (τ' : ∀ m : L'.ι, Γ(X, W ⊓ L'.U m)ˣ), L.IsLB → L'.IsLB → w.IsGen → IsGenOn L W τ → IsGenOn L' W τ' → ∃! t : Γ(X, W)ˣ, ∀ (m : L.ι) (m' : L'.ι), res (inf_le_left : W ⊓ (L'.U m' ⊓ L.U m) ≤ W) t * res (inf_le_inf_left W inf_le_left : W ⊓ (L'.U m' ⊓ L.U m) ≤ W ⊓ L'.U m') (τ' m') = res (inf_le_right : W ⊓ (L'.U m' ⊓ L.U m) ≤ L'.U m' ⊓ L.U m) (w.s (m', m)) * res (inf_le_inf_left W inf_le_right : W ⊓ (L'.U m' ⊓ L.U m) ≤ W ⊓ L.U m) (τ m) := by
  intro X L L' W w τ τ' hL hL' hw hτ hτ'
  have hc : W ≤ ⨆ p : L'.ι × L.ι, W ⊓ (L'.U p.1 ⊓ L.U p.2) := by
    intro x hx
    obtain ⟨i, hi⟩ := exists_chart hL x
    obtain ⟨i', hi'⟩ := exists_chart hL' x
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨(i', i), hx, hi', hi⟩
  have hagree : ∀ (p q : L'.ι × L.ι), ∀ x ∈ (W ⊓ (L'.U p.1 ⊓ L.U p.2)) ⊓ (W ⊓ (L'.U q.1 ⊓ L.U q.2)),
      gm (𝟙 X) x _ (ratioLoc L L' W w τ τ' p.1 p.2) = gm (𝟙 X) x _ (ratioLoc L L' W w τ τ' q.1 q.2) := by
    rintro ⟨m', m⟩ ⟨n', n⟩ x ⟨⟨hx, hm', hm⟩, ⟨-, hn', hn⟩⟩
    rw [gm_ratioLoc L L' W w τ τ' m m' ⟨hx, hm', hm⟩, gm_ratioLoc L L' W w τ τ' n n' ⟨hx, hn', hn⟩,
      gm_iso hw hm hn hm' hn', gm_isGenOn hτ hx hm hn, gm_isGenOn hτ' hx hm' hn']
    exact comm_identity _ _ _ _ _
  obtain ⟨t, ht⟩ := glue_unit W (fun p : L'.ι × L.ι ↦ W ⊓ (L'.U p.1 ⊓ L.U p.2)) (fun p ↦ inf_le_left) hc
    (fun p ↦ ratioLoc L L' W w τ τ' p.1 p.2) hagree
  refine ⟨t, fun m m' ↦ ?_, fun t' ht' ↦ ?_⟩
  · rw [ht (m', m)]
    exact inv_mul_cancel_right _ _
  · apply unit_ext
    intro x hx
    obtain ⟨m, hm⟩ := exists_chart hL x
    obtain ⟨m', hm'⟩ := exists_chart hL' x
    have hmem : x ∈ W ⊓ (L'.U m' ⊓ L.U m) := ⟨hx, hm', hm⟩
    have e0 : res (inf_le_left : W ⊓ (L'.U m' ⊓ L.U m) ≤ W) t' *
        res (inf_le_inf_left W inf_le_left : W ⊓ (L'.U m' ⊓ L.U m) ≤ W ⊓ L'.U m') (τ' m') =
        res (inf_le_right : W ⊓ (L'.U m' ⊓ L.U m) ≤ L'.U m' ⊓ L.U m) (isoAt w m' m) *
        res (inf_le_inf_left W inf_le_right : W ⊓ (L'.U m' ⊓ L.U m) ≤ W ⊓ L.U m) (τ m) := ht' m m'
    have e1 := congrArg (gm (𝟙 X) x _) e0
    rw [map_mul, map_mul, gm_res _ x _ hmem, gm_res _ x _ hmem, gm_res _ x _ hmem, gm_res _ x _ hmem] at e1
    have e2 := congrArg (gm (𝟙 X) x _) (ht (m', m))
    dsimp only at e2
    rw [gm_res _ x _ hmem, gm_ratioLoc L L' W w τ τ' m m' hmem] at e2
    rw [e2]
    exact eq_mul_inv_of_mul_eq e1

end GlobalTheory.GenRatio
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace GlobalTheory.UPel.HT.ES

theorem isTj_of_objMap_factor : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (r : ℤ) (w : Ideal (𝓞 D.F)) (j : ℕ) (Y₀ Y : Scheme.{0}) (i : Y₀ ⟶ Y) (σ₀ : Y₀ ⟶ Sp R) (σ : Y ⟶ Sp R) (o o' : Obj b N σ) (o₀ o₀' : Obj b N σ₀) (m : ObjMap o₀ o i) (m' : ObjMap o₀' o' i) (ψ₀ : o₀.A ⟶ o₀'.A) (ψ : o.A ⟶ o'.A), m.φ ≫ ψ.left = ψ₀.left ≫ m'.φ → (∀ (S : Scheme.{0}) (f : S ⟶ Y), IsUnit ((p : ℕ) : Γ(S, ⊤)) → ∃ f₀ : S ⟶ Y₀, f₀ ≫ i = f) → IsTj r w j o₀ o₀' ψ₀ → IsTj r w j o o' ψ := by
  intro p _ D R _ b N r w j Y₀ Y i σ₀ σ o o' o₀ o₀' m m' ψ₀ ψ hψ hfac h k _ _ _ x
  have hpu : IsUnit ((p : ℕ) : Γ(Sp k, ⊤)) := by
    have hk : IsUnit ((p : ℕ) : k) := (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero).isUnit
    have := hk.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
    rwa [map_natCast] at this
  obtain ⟨x₀, hx₀⟩ := hfac (Sp k) x hpu
  obtain ⟨e, he, -⟩ := m.exists_ptEquiv (Over.mk x) x₀ hx₀
  obtain ⟨e', he', -⟩ := m'.exists_ptEquiv (Over.mk x) x₀ hx₀
  have hcomp : ∀ g₀ : Over.mk x₀ ⟶ o₀.A, e g₀ ≫ ψ = e' (g₀ ≫ ψ₀) := fun g₀ => by
    ext
    rw [Over.comp_left, he, he', Over.comp_left, Category.assoc, hψ, Category.assoc]
  have hker : ∀ g₀ : Over.mk x₀ ⟶ o₀.A, e g₀ ≫ ψ = 1 ↔ g₀ ≫ ψ₀ = 1 := fun g₀ => by
    rw [hcomp]; exact map_eq_one_iff _ e'.injective
  have hact : ∀ (g₀ : Over.mk x₀ ⟶ o₀.A) (c : D.O), e g₀ ≫ o.act.act c = e (g₀ ≫ o₀.act.act c) := fun g₀ c => by
    ext
    rw [Over.comp_left, he, he, Over.comp_left, Category.assoc, Category.assoc, m.act]
  have hkill : ∀ (v : Ideal (𝓞 D.F)) (g₀ : Over.mk x₀ ⟶ o₀.A), KilledBy o v (e g₀) ↔ KilledBy o₀ v g₀ :=
    fun v g₀ => forall₂_congr fun a _ => by rw [hact]; exact map_eq_one_iff _ e.injective
  obtain ⟨h1, h2⟩ := h k x₀
  refine ⟨fun g hg hu => ?_, ?_⟩
  · obtain ⟨g₀, rfl⟩ := e.surjective g
    rw [hkill]
    rw [hker] at hg
    obtain ⟨n, hn⟩ := hu
    exact h1 g₀ hg ⟨n, (hkill _ g₀).1 hn⟩
  · rw [← h2]
    exact Nat.card_congr ((Equiv.subtypeEquiv e.toEquiv fun g₀ => by
      change _ ↔ e g₀ ≫ ψ = 1 ∧ KilledBy o w (e g₀)
      rw [hker, hkill]).symm)

end GlobalTheory.UPel.HT.ES
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.liftAbelianScheme_along_squareZero_factorization : AbelianDeRham → AbelianUnobstructed → ∀ (R R₁ R₀ : Type) [CommRing R] [CommRing R₁] [CommRing R₀] (I J : Ideal R) (I₁ : Ideal R₁) (κ : DividedPowers I) (π : R →+* R₀)
    (hJ : J ^ 2 = 0) (ρ : R →+* R₁) (κ₁ : DividedPowers I₁) (π₁ : R₁ →+* R₀), IsStep κ π hJ ρ κ₁ π₁ →
    LiftObj (divided₂ hJ) ρ → LiftObj κ₁ π₁ → LiftObj κ π := by
  first | exact @GlobalTheory.SqLift.liftObj_step | exact GlobalTheory.SqLift.liftObj_step | (intros; apply GlobalTheory.SqLift.liftObj_step <;> assumption)
end

section

open GlobalTheory GlobalTheory.LogDR

namespace GlobalTheory.LogDR.WedgeMul

theorem prod_perm_sign {A : Type} [Ring A] {α : Type} (f : α → A)
    (hf : ∀ a b, f a * f b = -(f b * f a)) {l₁ l₂ : List α} (h : l₁.Perm l₂) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ (l₁.map f).prod = ε • (l₂.map f).prod := by
  induction h with
  | nil => exact ⟨1, Or.inl rfl, by simp⟩
  | cons x _ ih =>
    obtain ⟨ε, hε, e⟩ := ih
    exact ⟨ε, hε, by simp only [List.map_cons, List.prod_cons, e, mul_smul_comm]⟩
  | swap x y l =>
    refine ⟨-1, Or.inr rfl, ?_⟩
    simp only [List.map_cons, List.prod_cons, ← mul_assoc, hf y x, neg_mul, neg_smul, one_smul]
  | trans _ _ ih₁ ih₂ =>
    obtain ⟨ε₁, h₁, e₁⟩ := ih₁
    obtain ⟨ε₂, h₂, e₂⟩ := ih₂
    refine ⟨ε₁ * ε₂, ?_, by rw [e₁, e₂, smul_smul]⟩
    rcases h₁ with rfl | rfl <;> rcases h₂ with rfl | rfl <;> simp

end GlobalTheory.LogDR.WedgeMul


open GlobalTheory.LogDR.WedgeMul in
theorem GlobalTheory.LogDR.dlog_mul_logWedge : ∀ (K : Type) [Field K] (n : ℕ) (x : Fin n → Kˣ) (i : Fin n) (I : Finset (Fin n)), (i ∈ I → ExteriorAlgebra.ι K (dlog (x i)) * logWedge x I = 0) ∧ (i ∉ I → ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ExteriorAlgebra.ι K (dlog (x i)) * logWedge x I = ε • logWedge x (insert i I)) := by
  intro K _ n x i I
  set f : Fin n → abelian₂ K := fun j => ExteriorAlgebra.ι K (dlog (x j)) with hfdef
  have hf : ∀ a b, f a * f b = -(f b * f a) := fun a b =>
    eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap _ _)
  constructor
  · intro hi
    have hp : (I.sort (· ≤ ·)).Perm (i :: (I.erase i).sort (· ≤ ·)) := by
      refine (List.perm_ext_iff_of_nodup (Finset.sort_nodup _ _) ?_).2 fun a => ?_
      · refine List.nodup_cons.2 ⟨?_, Finset.sort_nodup _ _⟩
        simp
      · by_cases ha : a = i
        · subst ha; simp [hi]
        · simp [ha]
    obtain ⟨ε, -, e⟩ := prod_perm_sign f hf hp
    show f i * ((I.sort (· ≤ ·)).map f).prod = 0
    rw [e, mul_smul_comm, List.map_cons, List.prod_cons, ← mul_assoc]
    simp [hfdef, ExteriorAlgebra.ι_sq_zero]
  · intro hi
    have hp : ((insert i I).sort (· ≤ ·)).Perm (i :: I.sort (· ≤ ·)) := by
      refine (List.perm_ext_iff_of_nodup (Finset.sort_nodup _ _) ?_).2 fun a => ?_
      · exact List.nodup_cons.2 ⟨by simpa using hi, Finset.sort_nodup _ _⟩
      · simp
    obtain ⟨ε, hε, e⟩ := prod_perm_sign f hf hp
    refine ⟨ε, hε, ?_⟩
    show f i * ((I.sort (· ≤ ·)).map f).prod = ε • (((insert i I).sort (· ≤ ·)).map f).prod
    rw [e, List.map_cons, List.prod_cons, smul_smul]
    rcases hε with rfl | rfl <;> simp
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.cupProduct_gradedCommRingAxioms_hold : GlobalTheory.EtC.DivisorRingCompatibility := by
  first | (exact @GlobalTheory.EtC.a6ring_holds) | (exact GlobalTheory.EtC.a6ring_holds) | (intros; apply GlobalTheory.EtC.a6ring_holds  <;> assumption)
end
