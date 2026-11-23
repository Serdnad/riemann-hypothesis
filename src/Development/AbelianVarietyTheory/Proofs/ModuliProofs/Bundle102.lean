module

import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsGrpPullbackOfLoc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.Bundle001
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Mathlib.RingTheory.Valuation.ValuationRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle002
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle023
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SectionsHaveFiniteDimensionInvarianceIsomorphism
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle003
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle095
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle094
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle089
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle096
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaEmbeddingSectionsBaseChangeAffine
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle100
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle087
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsPullCubicalOfIso
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLineBundleDescentToSubfield
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle098
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.GrpLoc

theorem hom_ext_loc {X Y : Scheme.{0}} {f g : X ⟶ Y}
    (h : ∀ p : X, ∃ (W : Scheme.{0}) (a : W ⟶ X), IsOpenImmersion a ∧ p ∈ Set.range a ∧ a ≫ f = a ≫ g) : f = g := by
  choose W a ha hp hfg using h
  exact Scheme.Cover.hom_ext (Scheme.Cover.mkOfCovers (P := @IsOpenImmersion) X W a
    (fun x => by obtain ⟨y, hy⟩ := hp x; exact ⟨x, y, hy⟩) ha) f g hfg

theorem range_of_isPullback {P X Y Z : Scheme.{0}} {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback a b f g) (x : X) : x ∈ Set.range a ↔ f x ∈ Set.range g := by
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨b p, by rw [← Scheme.Hom.comp_apply, ← h.w, Scheme.Hom.comp_apply]⟩
  · rintro ⟨y, hy⟩
    obtain ⟨q, hq₁, -⟩ := Scheme.Pullback.exists_preimage_pullback x y hy.symm
    refine ⟨h.isoPullback.inv q, ?_⟩
    rw [← Scheme.Hom.comp_apply, h.isoPullback_inv_fst, hq₁]

theorem mul_left_pre {S : Scheme.{0}} {G : Over S} [GrpObj G] {T T' : Over S} (k : T'.left ⟶ T.left)
    (hk : k ≫ T.hom = T'.hom) (x y : T ⟶ G) (x' y' : T' ⟶ G) (hx : x'.left = k ≫ x.left)
    (hy : y'.left = k ≫ y.left) : (x' * y').left = k ≫ (x * y).left := by
  have ex : x' = Over.homMk k hk ≫ x := by ext; simp [hx]
  have ey : y' = Over.homMk k hk ≫ y := by ext; simp [hy]
  rw [ex, ey, ← MonObj.comp_mul, Over.comp_left]
  rfl

theorem isGrpPullback_id_of_loc {S : Scheme.{0}} {A A' : Over S} [GrpObj A] [GrpObj A'] (φ : A.left ⟶ A'.left) [IsIso φ]
    (w : φ ≫ A'.hom = A.hom)
    (h : ∀ p : S, ∃ (W : Scheme.{0}) (x : W ⟶ S) (B : Over W) (_ : GrpObj B) (a : B.left ⟶ A.left),
      IsOpenImmersion x ∧ p ∈ Set.range x ∧ IsGrpPullback B A x a ∧ IsGrpPullback B A' x (a ≫ φ)) :
    IsGrpPullback A A' (𝟙 S) φ := by
  apply GlobalTheory.FamRep.isGrpPullback_of_loc <;> assumption

theorem isGrpPullback_local_on_base : ∀ (S : Scheme.{0}) (A A' : Over S) [GrpObj A] [GrpObj A'] (φ : A.left ⟶ A'.left), IsIso φ → φ ≫ A'.hom = A.hom → (∀ p : S, ∃ (V : Scheme.{0}) (x : V ⟶ S) (B : Over V) (_ : GrpObj B) (a : B.left ⟶ A.left), IsOpenImmersion x ∧ p ∈ Set.range x ∧ IsGrpPullback B A x a ∧ IsGrpPullback B A' x (a ≫ φ)) → IsGrpPullback A A' (𝟙 S) φ := by
  intro S A A' _ _ φ hφ w h
  exact isGrpPullback_id_of_loc φ w h

end GlobalTheory.GrpLoc
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Published

def EndCharPolySt : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Sp K)) (ψ : P.A ⟶ P.A), IsMonHom ψ →
    ∃ χ : Polynomial ℤ, χ.Monic ∧ χ.natDegree = 2 * P.g ∧ ∀ l r : ℕ, l.Prime → (l : K) ≠ 0 →
      ∀ y : Fin (2 * P.g) → (baseOver (Sp K) ⟶ P.A), (∀ i, y i ^ l ^ r = 1) →
        (∀ z : baseOver (Sp K) ⟶ P.A, z ^ l ^ r = 1 → ∃ c : Fin (2 * P.g) → ℕ, linComb y c = z) →
        ∀ B : Matrix (Fin (2 * P.g)) (Fin (2 * P.g)) (ZMod (l ^ r)),
          (∀ i, y i ≫ ψ = linComb y fun k => (B k i).val) → B.charpoly = χ.map (Int.castRingHom (ZMod (l ^ r)))

def RosatiPositiveSt : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Sp K)) (φ φ' : P.A ⟶ P.A), IsMonHom φ → IsMonHom φ' →
    RosatiAdj P.A P.L φ φ' → φ ≠ 1 → ∀ t : ℤ, IndefiniteRowSideFullHecke.FirstOrderRigidityLevel.HasTrace P (φ' ≫ φ) t → 0 < t

end GlobalTheory.Published

namespace GlobalTheory.ThetaDetCompare

open GlobalTheory.IndefiniteRowSideFullHecke

section AdjRing

open CechPic MulOpposite

variable {K : Type} [Field K] {P : PolAV (Sp K)}





end AdjRing

section Trace

open ThetaCoord

variable {K : Type} [Field K] {P : PolAV (Sp K)} {M : ℕ} {y : Fin (2 * P.g) → (baseOver (Sp K) ⟶ P.A)}
  {O : Type} [Ring O]

variable [IsAlgClosed K]

end Trace

section Positive

variable {K : Type} [Field K] [IsAlgClosed K] {P : PolAV (Sp K)} {O : Type} [Ring O] [StarRing O]

end Positive

end GlobalTheory.ThetaDetCompare
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct

theorem _root_.GlobalTheory.T.exists_sections_generate_square_bundle : ∀ (O K : Type) [CommRing O] [IsDomain O] [ValuationRing O] [Field K] [IsAlgClosed K] [Algebra O K] [IsFractionRing O K] (A : Over (Sp O)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ H : LB A.left, H.IsLB → Triv (Theta A H) → ∀ s : LB.Sec H, (∃ x ∈ Out.nonzeroLocus s, A.hom x = IsLocalRing.closedPoint O) → ∃ (m : ℕ) (u : Fin (m + 1) → LB.Sec (pw H 2)), ⨆ i, Out.nonzeroLocus (u i) = ⊤ := by
  first | exact @GlobalTheory.SquareGenerated.exists_secs_sq_generate | exact GlobalTheory.SquareGenerated.exists_secs_sq_generate | (intros; apply GlobalTheory.SquareGenerated.exists_secs_sq_generate <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.ModelRelCompare

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ModelCompare GlobalTheory.Models

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

section Dominates

variable {O' : Type} [CommRing O'] {β' : O' →+* c.F} (Y : Model Xo c β) (Y' : Model Xo c β') (b : O →+* O')
  (hb : β'.comp b = β)

end Dominates

section Dense

variable (Y : Model Xo c β)

theorem densePart (h : IsDedFrac β) : IsLocallyNoetherian Y.X ∧ IsReduced Y.X ∧ Y.X.IsSeparated ∧
    IsPreimmersion Y.j ∧ Flat Y.j ∧ IsDominant Y.j ∧ QuasiCompact Y.j := by
  obtain ⟨⟨_, _⟩, -, hfr⟩ := h
  letI := β.toAlgebra
  obtain ⟨h₁, -, h₂, h₃⟩ :=
    GlobalTheory.genericPart_dense_proOpen O c.F Y.X _ Y.s Y.jQ Y.flat Y.proj Y.jQ_open Y.jQ_dense
  have : ∀ x : Y.X, _root_.IsReduced (Y.X.presheaf.stalk x) := fun x ↦
    have := (Y.normal x).1
    inferInstance
  exact ⟨h₁, isReduced_of_isReduced_stalk Y.X, h₂, h₃⟩

end Dense

section Transition

variable {l₂ : Level H} {Xo₂ : Moduli D l₂} {c₂ : Coeff l₂} {O₂ : Type} [CommRing O₂] {β₂ : O₂ →+* c₂.F}
  (Y : Model Xo c β) (Y₂ : Model Xo₂ c₂ β₂) (hl : l.Dvd l₂) (hF : c.F ≤ c₂.F) (b : O →+* O₂)
  (hb : β₂.comp b = (IntermediateField.inclusion hF).toRingHom.comp β) (π : Y₂.X ⟶ Y.X)

end Transition

section Algebra

end Algebra

section Action

variable (Y : Model Xo c β)

variable {Y}

variable (Y)

end Action

end GlobalTheory.ModelRelCompare
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV
theorem _root_.GlobalTheory.T.sectionsHaveFiniteDimension_invariance_isomorphisms : ∀ (K : Type) [Field K] (X : Scheme.{0}) (p : X ⟶ Sp K) (M : LB X), M.IsLB → (∀ r r', SectionsHaveFiniteDimension p M r → SectionsHaveFiniteDimension p M r' → r = r') ∧ (∀ M' : LB X, M'.IsLB → LBIso M M' → (∀ r, SectionsHaveFiniteDimension p M r → SectionsHaveFiniteDimension p M' r) ∧ ∀ e, LBIso (lbPow M e) (lbPow M' e)) ∧ (∀ a e, LBIso (lbPow (lbPow M a) e) (lbPow M (a * e))) ∧ LBIso (lbPow M 1) M ∧ (∀ (Y : Scheme.{0}) (φ : Y ⟶ X) (e : ℕ), LBIso (lbPow (M.pull φ) e) ((lbPow M e).pull φ)) ∧ ∀ (Y : Scheme.{0}) (φ : Y ≅ X) (r : ℕ), SectionsHaveFiniteDimension p M r ↔ SectionsHaveFiniteDimension (φ.hom ≫ p) (M.pull φ.hom) r := by
  first | exact @GlobalTheory.SecDim.lbPow_mul_and_pull_and_sectionsFiniteDim_iso_invariant | exact GlobalTheory.SecDim.lbPow_mul_and_pull_and_sectionsFiniteDim_iso_invariant | (intros; apply GlobalTheory.SecDim.lbPow_mul_and_pull_and_sectionsFiniteDim_iso_invariant <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV

theorem _root_.GlobalTheory.T.principalPolarisation_volume_form_symmetric_ample : Out.Laws → Out.Laws2 → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)), Vol P.A.hom P.L P.g 1 ∧ FormIs P P.L (𝟙 P.A) ∧ SymB P.L ∧ MapDeg (𝟙 P.A.left) 1 ∧ (∃ (m : ℕ) (th : Fin (m + 1) → (lbPow P.L 4).Sec), VAmp P.A.hom (lbPow P.L 4) th) ∧ ∀ k : ℕ, (k : K) ≠ 0 → ∃ pt : Fin (2 * P.g) → (Out.baseOver (Sp K) ⟶ P.A), TorsBasis P.A k pt ∧ (k ≠ 1 → ActsBy pt (𝟙 P.A) (1 : Matrix _ _ (ZMod k))) := by
  first | exact @GlobalTheory.principal_polarisation_numerics | exact GlobalTheory.principal_polarisation_numerics | (intros; apply GlobalTheory.principal_polarisation_numerics <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.KS.Lin

section
variable {g : ℕ} {A₀ : Over (Sp ℂ)} [GrpObj A₀] {L₀ : LB A₀.left} {u : HolUnif A₀ L₀ g} {X : Scheme.{0}}
  {R : Type} [CommRing R] {p : X ⟶ Sp R} {m : A₀.left ⟶ X}

theorem ksRel_add {D D' : R → ℂ} {Θ Θ' : Matrix (Fin g) (Fin g) ℂ}
    {s s' : (Fin g → ℂ) → ∀ W : X.Opens, Γ(X, W) → ℂ}
    (h : KSRel u p m D Θ s) (h' : KSRel u p m D' Θ' s') :
    KSRel u p m (fun r => D r + D' r) (Θ + Θ') (fun z W f => s z W f + s' z W f) := by
  refine { der := ?_, base := ?_, hol := ?_, per := ?_ }
  · intro z
    refine { add := ?_, mul := ?_, res := ?_ }
    · intro W hW f f'
      simp only [(h.der z).add W hW, (h'.der z).add W hW]
      ring
    · intro W hW f f'
      simp only [(h.der z).mul W hW, (h'.der z).mul W hW]
      ring
    · intro W W' hle hW' f
      simp only [(h.der z).res W W' hle hW', (h'.der z).res W W' hle hW']
  · intro z r
    simp only [h.base, h'.base]
  · intro W f
    exact (h.hol W f).add (h'.hol W f)
  · intro l W f z hz
    simp only [h.per l W f z hz, h'.per l W f z hz, Matrix.add_mulVec, map_add (f := _)]
    ring

theorem ksRel_smul (c : ℂ) {D : R → ℂ} {Θ : Matrix (Fin g) (Fin g) ℂ}
    {s : (Fin g → ℂ) → ∀ W : X.Opens, Γ(X, W) → ℂ} (h : KSRel u p m D Θ s) :
    KSRel u p m (fun r => c * D r) (c • Θ) (fun z W f => c * s z W f) := by
  refine { der := ?_, base := ?_, hol := ?_, per := ?_ }
  · intro z
    refine { add := ?_, mul := ?_, res := ?_ }
    · intro W hW f f'
      simp only [(h.der z).add W hW]
      ring
    · intro W hW f f'
      simp only [(h.der z).mul W hW]
      ring
    · intro W W' hle hW' f
      simp only [(h.der z).res W W' hle hW']
  · intro z r
    simp only [h.base]
  · intro W f
    exact (h.hol W f).const_mul c
  · intro l W f z hz
    simp only [h.per l W f z hz, Matrix.smul_mulVec, map_smul, smul_eq_mul]
    ring
end

theorem ks_linear : ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ (o R : Type) [CommRing o] [CommRing R] [Algebra o R] [Algebra o ℂ] [Algebra R ℂ] [IsScalarTower o R ℂ] (X : Scheme.{0}) (p : X ⟶ Sp R) (m : P₀.A.left ⟶ X), Smooth p → IsPullback m P₀.A.hom p (spMap (algebraMap R ℂ)) → ∃ κ : Derivation o R ℂ →ₗ[ℂ] Matrix (Fin P₀.g) (Fin P₀.g) ℂ, ∀ D : Derivation o R ℂ, ∃ s, KSRel u p m (fun r => D r) (κ D) s := by
  intro P₀ u Hm χ hG o R _ _ _ _ _ _ X p m hs hpb
  have hder : ∀ D : Derivation o R ℂ, IsDer (algebraMap R ℂ) (fun r => D r) := fun D =>
    ⟨fun a b => D.map_add a b, fun a b => by
      show D (a * b) = _
      rw [D.leibniz, Algebra.smul_def, Algebra.smul_def]⟩
  have hex : ∀ D : Derivation o R ℂ, ∃ Θ s, KSRel u p m (fun r => D r) Θ s := fun D =>
    GlobalTheory.T.exists_analytic_kodairaSpencer_class P₀ u Hm χ hG R (algebraMap R ℂ) X p m hs hpb _ (hder D)
  choose Θ s hΘ using hex
  have huniq : ∀ (D : Derivation o R ℂ) Θ' s', KSRel u p m (fun r => D r) Θ' s' → Θ D = Θ' :=
    fun D Θ' s' h => GlobalTheory.KS.Uniq.ks_unique P₀ u Hm χ hG R (algebraMap R ℂ) X p m hs hpb _ _ _ _ _ (hΘ D) h
  refine ⟨{ toFun := Θ, map_add' := ?_, map_smul' := ?_ }, fun D => ⟨s D, hΘ D⟩⟩
  · intro D D'
    apply huniq (D + D')
    have e : (fun r => (D + D') r) = fun r => D r + D' r := funext (add_apply D D')
    rw [e]
    exact ksRel_add (hΘ D) (hΘ D')
  · intro c D
    rw [RingHom.id_apply]
    apply huniq (c • D)
    have e : (fun r => (c • D) r) = fun r => c * D r := funext fun r => by
      rw [smul_apply, smul_eq_mul]
    rw [e]
    exact ksRel_smul c (hΘ D)

end GlobalTheory.KS.Lin
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

theorem _root_.GlobalTheory.T.exists_isogeny_pullback_heckeModuliObject : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (p : ℕ) (S S' : Scheme.{0}) (s : S ⟶ Sp (KA l)) (s' : S' ⟶ Sp (KA l)) (f : S' ⟶ S) (o₁ o₂ : Ob D l s) (o₁' o₂' : Ob D l s') (n₁ : ObjMap o₁' o₁ f) (n₂ : ObjMap o₂' o₂ f) (ψ : o₁.t.G ⟶ o₂.t.G), (∃! ψ' : o₁'.t.G ⟶ o₂'.t.G, ψ'.left ≫ n₂.toSABMap.φ = n₁.toSABMap.φ ≫ ψ.left) ∧ ∀ ψ' : o₁'.t.G ⟶ o₂'.t.G, ψ'.left ≫ n₂.toSABMap.φ = n₁.toSABMap.φ ≫ ψ.left → (IsIsog o₁ o₂ p ψ → IsIsog o₁' o₂' p ψ') ∧ ∀ K, IsMonHom ψ → KerSet ψ K → KerSet ψ' (n₁.toSABMap.φ ⁻¹' K) := by
  first | exact @GlobalTheory.HkFam.isog_pull | exact GlobalTheory.HkFam.isog_pull | (intros; apply GlobalTheory.HkFam.isog_pull <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
theorem _root_.GlobalTheory.T.thetaEmbeddingSections_baseChange_affine : Out.Laws2 → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (S : Scheme.{0}) (s : S ⟶ Sp o) (t : TObj g (N' ^ 2) J b s) (m : ℕ) (T T' : Over S) (h : T' ⟶ T) σ, IsAffine T.left → IsAffine T'.left → t.Emb m T σ → ∃ σ', t.Emb m T' σ' ∧ ∀ (R : Type) [CommRing R] (y : Sp R ⟶ (T' ⊗ t.A).left) (w : Ix g (N' ^ 2) → R), SecCoord _ σ' y w ↔ SecCoord _ σ (y ≫ (h ▷ t.A).left) w := by
  first | exact @GlobalTheory.emb_baseChange | exact GlobalTheory.emb_baseChange | (intros; apply GlobalTheory.emb_baseChange <;> assumption)
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.HeckePoint

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {B : Type} [CommRing B] {b : Base l B} {k : Type} [Field k] {s : Sp k ⟶ Sp B}

theorem exists_torsion_lift {Q Q' : Type} [CommGroup Q] [CommGroup Q'] (ψ : Q →* Q') (hs : Function.Surjective ψ)
    {q n : ℕ} (hq : ∀ x, ψ x = 1 → x ^ q = 1) (hn : 0 < n) (hc : n.Coprime q) (y : Q') (hy : y ^ n = 1) :
    ∃ x, x ^ n = 1 ∧ ψ x = y := by
  obtain ⟨u, rfl⟩ := hs y
  obtain ⟨r, -, hr⟩ := Nat.exists_mul_mod_eq_of_coprime 1 hc.symm hn.ne'
  refine ⟨u ^ (q * r), ?_, ?_⟩
  · rw [← pow_mul, mul_comm, pow_mul, pow_mul, hq _ ((map_pow _ _ _).trans hy), one_pow]
  · rw [map_pow, pow_eq_pow_of_modEq (show q * r ≡ 1 [MOD n] from hr) hy, pow_one]

theorem objMap_of_isHeckeIsog [IsAlgClosed k] [CharZero k] (hL : Out.Laws)
    (hfacts : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B : Type) [CommRing B] (b : Base l B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o : Obj D l b s), IsAbelianScheme o.t.G ∧ SmoothOfRelativeDimension (Module.finrank ℚ E / 2 * (D.p + D.q)) o.t.G.hom ∧ Out.Rigidified o.t.G o.t.PP.L ∧ Out.Sym o.t.G o.t.PP.L)
    (hDet : ∀ (k : Type) [Field k] [IsAlgClosed k] (P P' : Out.PolAV (Sp k)) (α : P.A ⟶ P'.A) (p d : ℕ), IsMonHom α → p.Prime → CharZero k → (∀ (n : ℕ) (x y : 𝟙_ (Over (Sp k)) ⟶ P.A) (c : kˣ), 0 < n → n.Coprime p → x ^ n = 1 → y ^ n = 1 → Out.WeilIs P.A P.L n x y (unitOn c) → Out.WeilIs P'.A P'.L n (x ≫ α) (y ≫ α) (unitOn (c ^ d))) → LBIso (abelian₂ P.A (lbPow P.L d)) (abelian₂ P.A (P'.L.pull α.left)))
    {o o₁ o₂ : Obj D l b s} {p : ℕ} (hp : p.Prime) (hpM : ¬ p ∣ l.M') {C : Subgroup (𝟙_ (Over (Sp k)) ⟶ o.t.G)}
    (hC : ∀ x ∈ C, x ^ p ^ 2 = 1) {ψ₁ : o.t.G ⟶ o₁.t.G} {ψ₂ : o.t.G ⟶ o₂.t.G} (h₁ : IsHeckeIsog o o₁ p C ψ₁)
    [IsFinite ψ₁.left] [Etale ψ₁.left] [Surjective ψ₁.left] (h₂ : IsHeckeIsog o o₂ p C ψ₂) :
    Nonempty (ObjMap o₁ o₂ (𝟙 _)) := by
  obtain ⟨hom₁, lin₁, sur₁, ker₁, weil₁, lev₁⟩ := h₁
  obtain ⟨hom₂, lin₂, sur₂, ker₂, weil₂, lev₂⟩ := h₂
  obtain ⟨hab, hdim, hrig, hsym⟩ := hfacts E H D l B b _ s o
  obtain ⟨hab₁, hdim₁, hrig₁, hsym₁⟩ := hfacts E H D l B b _ s o₁
  obtain ⟨hab₂, hdim₂, hrig₂, hsym₂⟩ := hfacts E H D l B b _ s o₂
  let P : Out.PolAV (Sp k) :=
    { A := o.t.G, isAb := hab, g := _, smoothDim := hdim,
      L := o.t.PP.L, isLB := o.t.PP.isLB, rigid := hrig, sym := hsym,
      ample := o.ample, ktriv := o.ktriv }
  let P₁ : Out.PolAV (Sp k) :=
    { A := o₁.t.G, isAb := hab₁, g := _, smoothDim := hdim₁,
      L := o₁.t.PP.L, isLB := o₁.t.PP.isLB, rigid := hrig₁, sym := hsym₁,
      ample := o₁.ample, ktriv := o₁.ktriv }
  let P₂ : Out.PolAV (Sp k) :=
    { A := o₂.t.G, isAb := hab₂, g := _, smoothDim := hdim₂,
      L := o₂.t.PP.L, isLB := o₂.t.PP.isLB, rigid := hrig₂, sym := hsym₂,
      ample := o₂.ample, ktriv := o₂.ktriv }
  have := o₁.proper
  have := o₂.proper
  obtain ⟨α, hα⟩ := exists_fac hab.smooth ψ₁ ψ₂ fun x hx => (ker₂ x).2 ((ker₁ x).1 hx)
  have homα : IsMonHom α := hL.rigidity _ _ _ hab₁ hab₂ α (by
    rw [← IsMonHom.one_hom ψ₁, Category.assoc, hα, IsMonHom.one_hom])
  have : Epi ψ₁.left := Flat.epi_of_flat_of_surjective _
  have : Epi ψ₁ := Over.epi_of_epi_left ψ₁
  have linα : ∀ a, o₁.t.act.act a ≫ α = α ≫ o₂.t.act.act a := fun a => by
    rw [← cancel_epi ψ₁, ← reassoc_of% lin₁, hα, reassoc_of% hα, lin₂]
  let ρ : (𝟙_ (Over (Sp k)) ⟶ o.t.G) →* (𝟙_ (Over (Sp k)) ⟶ o₁.t.G) :=
    MonoidHom.mk' (fun z => z ≫ ψ₁) fun a c => MonObj.mul_comp a c ψ₁
  have hlam : LBIso (abelian₂ o₁.t.G (lbPow o₁.t.PP.L 1)) (abelian₂ o₁.t.G (o₂.t.PP.L.pull α.left)) :=
    hDet k P₁ P₂ α p 1 homα hp inferInstance fun n x y c hn hc hx hy h => by
      have lift := exists_torsion_lift ρ sur₁ (fun x hx => hC x ((ker₁ x).1 hx)) hn (hc.pow_right 2)
      obtain ⟨x₀, tx, ex⟩ := lift x hx
      obtain ⟨y₀, ty, ey⟩ := lift y hy
      obtain rfl : x₀ ≫ ψ₁ = x := ex
      obtain rfl : y₀ ≫ ψ₁ = y := ey
      obtain ⟨c₀, hc₀, -⟩ := (hL.weil _ P n _).1 x₀ y₀ tx ty
      obtain ⟨c₀, rfl⟩ := (unitOn_bijective k).2 c₀
      have e : c = c₀ ^ p ^ 2 := (unitOn_bijective k).1
        (((hL.weil _ P₁ n _).1 _ _ hx hy).unique h (weil₁ n x₀ y₀ c₀ hc hc₀))
      have w := weil₂ n x₀ y₀ c₀ hc hc₀
      rw [← hα, ← Category.assoc, ← Category.assoc, ← e] at w
      rw [pow_one]
      exact w
  have hiso := iso_of_lam o₁.t o₂.t α linα hlam
  have := mono_of_kTriv α o₁.t.PP.isLB o₂.t.PP.isLB hiso o₁.ktriv
  have : IsIso α := isIso_of_mono α hab₂.smooth fun y => by
    obtain ⟨x, rfl⟩ := sur₂ y
    exact ⟨x ≫ ψ₁, by rw [Category.assoc, hα]⟩
  have : IsMonHom (asIso α).hom := homα
  obtain ⟨p₀, hp₀⟩ := exists_inv_mod hp hpM
  refine ⟨{ cm := CubeMap.ofHom α, cart := isGrpPullback_of_iso (asIso α), base := rfl
            act := fun a => congrArg (fun q => q.left) (linα a)
            lin := isPullCubical_of_iso hL.globalFns hab₁ α _ _ hiso
            eta := fun a => ?_, etaA := fun a => ?_ }⟩
  · rw [Category.id_comp, ← (lev₁ p₀ hp₀ a).1, ← (lev₂ p₀ hp₀ a).1, ← hα, ← Category.assoc]; rfl
  · rw [Category.id_comp, ← (lev₁ p₀ hp₀ a).2, ← (lev₂ p₀ hp₀ a).2, ← hα, ← Category.assoc]; rfl

end GlobalTheory.HeckePoint
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

theorem _root_.GlobalTheory.T.exists_lineBundle_descent_to_subfield : ∀ (K : Type) [Field K] (K₀ : Subfield K) (X₀ X : Scheme.{0}) (p₀ : X₀ ⟶ Sp K₀) (p : X ⟶ Sp K) (φ : X ⟶ X₀) [QuasiCompact p₀] [QuasiSeparated p₀] (L : LB X), L.IsLB → IsPullback φ p p₀ (spMap K₀.subtype) → ∃ s : Finset K, ∀ (K₁ : Subfield K) (h : K₀ ≤ K₁), (s : Set K) ⊆ K₁ → ∀ (X₁ : Scheme.{0}) (p₁ : X₁ ⟶ Sp K₁) (φ₁ : X₁ ⟶ X₀) (ψ : X ⟶ X₁), IsPullback φ₁ p₁ p₀ (spMap (Subfield.inclusion h)) → ψ ≫ φ₁ = φ → ψ ≫ p₁ = p ≫ spMap K₁.subtype → ∃ L₁ : LB X₁, L₁.IsLB ∧ LBIso L (L₁.pull ψ) := by
  first | exact @GlobalTheory.LBDescent.exists_lb_subfield | exact GlobalTheory.LBDescent.exists_lb_subfield | (intros; apply GlobalTheory.LBDescent.exists_lb_subfield <;> assumption)
end
