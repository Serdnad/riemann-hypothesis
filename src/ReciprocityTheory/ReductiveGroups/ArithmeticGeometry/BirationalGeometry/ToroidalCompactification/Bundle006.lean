module

public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.WeightedChartPullback.TorusInj
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ConstGen
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle002
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CMField
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle005

@[expose] public section

section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l}

theorem mem_range_jK {k : Type} [Field k] (x : Sp (PowerSeries k)) (hx : PowerSeries.X ∉ x.asIdeal) :
    x ∈ Set.range (Out.jK (PowerSeries k)) := by
  have hXu : ¬ IsUnit (PowerSeries.X : PowerSeries k) := by
    intro hu
    first
      | (have h1 := hu.map (PowerSeries.constantCoeff k); simp at h1)
      | (have h1 := hu.map (PowerSeries.constantCoeff (R := k)); simp at h1)
  have hbot : x.asIdeal = ⊥ := by
    by_contra hne
    have hmax : x.asIdeal.IsMaximal := x.isPrime.isMaximal hne
    apply hx
    rw [IsLocalRing.eq_maximalIdeal hmax, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact hXu
  have hx' : x ∈ Set.range (PrimeSpectrum.comap
      (algebraMap (PowerSeries k) (FractionRing (PowerSeries k)))) := by
    rw [PrimeSpectrum.localization_comap_range (FractionRing (PowerSeries k))
      (nonZeroDivisors (PowerSeries k))]
    show Disjoint _ _
    rw [hbot, Set.disjoint_left]
    intro a ha ha'
    exact nonZeroDivisors.ne_zero ha ((Submodule.mem_bot _).1 ha')
  obtain ⟨y, hy⟩ := hx'
  exact ⟨y, hy⟩

theorem mono_spMap_subtype {F : Type} [Field F] (V : ValuationSubring F) : Mono (spMap V.subtype) := by
  have h : Epi (CommRingCat.ofHom (algebraMap V F)) := IsLocalization.epi (nonZeroDivisors V) F
  show Mono (Spec.map (CommRingCat.ofHom (algebraMap V F)))
  exact Scheme.Spec.map_mono (CommRingCat.ofHom (algebraMap V F)).op

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
end
end

section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi

abbrev lbPow {X : Scheme.{0}} (L : LB X) (n : ℕ) : LB X :=
  LB.LinComb L (K := PUnit) (fun _ => 𝟙 X) (fun _ => (n : ℤ))

def hermForm {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) : ℂ := z ⬝ᵥ Hm.mulVec (star w)

namespace HolUnif

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)

def IsFnPow (n : ℕ) (s : (lbPow L n).Sec) (θ : (Fin g → ℂ) → ℂ) : Prop :=
  ∀ (j : (lbPow L n).ι) z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ (lbPow L n).U j →
    valAt' (u.ex z).left ((lbPow L n).U j) (s.f j) = θ z * u.fr (j PUnit.unit) z ^ n

def IsThetaFn (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ) (n : ℕ) (θ : (Fin g → ℂ) → ℂ) : Prop :=
  Differentiable ℂ θ ∧ ∀ (l : u.Λ) z, θ (z + l) =
    (χ l * Complex.exp (Real.pi * hermForm Hm z l + Real.pi / 2 * hermForm Hm l l)) ^ n * θ z

end HolUnif

def ThetaUnifAV : Prop :=
  ∀ (P : Out.PolAV (Sp ℂ)) (rig : LB.Gen (P.L.pull (eSec P.A))), rig.IsGen →
    ∃ (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (Ef : LinearMap.BilinForm ℤ u.Λ),
      u.IsAH Hm χ ∧ u.IsRig rig ∧
      (∀ v, IsTangent v → ∃! w, u.IsDiff w v) ∧ (∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) ∧
      (∀ f : P.A ⟶ P.A, IsMonHom f → ∃ F : (Fin P.g → ℂ) →ₗ[ℂ] (Fin P.g → ℂ), ∀ z, u.ex (F z) = u.ex z ≫ f) ∧
      (∀ n : ℕ, (∀ s, ∃! θ, u.IsThetaFn Hm χ n θ ∧ u.IsFnPow n s θ) ∧
        ∀ θ, u.IsThetaFn Hm χ n θ → ∃! s, u.IsFnPow n s θ) ∧
      (∀ a b : u.Λ, (Ef a b : ℝ) = (hermForm Hm a b).im) ∧ Function.Bijective Ef ∧
      ∀ (k : ℕ) (a b : u.Λ) (c : ℂˣ), 0 < k →
        (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (Ef a b : ℂ) / k) →
        Out.WeilIs P.A P.L k (u.ex ((k : ℂ)⁻¹ • (a : Fin P.g → ℂ))) (u.ex ((k : ℂ)⁻¹ • (b : Fin P.g → ℂ))) (unitOn c)

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
end
end

section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj

def LatFinOrdSt : Prop :=
  ∀ (Y : Type) [AddCommGroup Y] [Module.Free ℤ Y] [Module.Finite ℤ Y] (b : LinearMap.BilinForm ℤ Y),
    (∀ y z, b y z = b z y) → (∀ y, y ≠ 0 → 0 < b y y) →
    ∀ σ : Y ≃ₗ[ℤ] Y, (∀ y z, b (σ y) (σ z) = b y z) → ∃ n : ℕ, 0 < n ∧ σ ^ n = 1

def LatMinkowskiSt : Prop :=
  ∀ (Y : Type) [AddCommGroup Y] [Module.Free ℤ Y] [Module.Finite ℤ Y] (σ : Y ≃ₗ[ℤ] Y) (n M : ℕ), 0 < n →
    σ ^ n = 1 → 3 ≤ M → (∀ y, ∃ z, σ y = y + M • z) → σ = 1

section Gt

open ReciprocityTheory.ChartRestriction.G.Out

def GtCoordToGtSt : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (e : ℕ) (G : Over (Spec (CommRingCat.of R)))
    [GrpObj G] [IsCommMonObj G], Nonempty (GtCoord I D e G) →
    ∃ (E : SplitExt (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))
      (β : E.B ≅ thickObj R I e D.P.A) (xe : D.X ≃+ E.X), IsMonHom β.hom ∧
      (∀ χ : D.X, ∃ w : LB.Iso (E.O (xe χ)).L (LB.LinComb D.P.L
          (fun k => ((Over.map (thick R I e)).map β.hom ≫ D.prBe I e).left ≫
            D.Oφ (𝟙 _) χ k) Oε), w.IsGen) ∧
      E.IsGt (thickObj R I e G)

end Gt

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace ReciprocityTheory.ChartRestriction.G.Semi.TorusPts

open TorusInj

variable {S : Scheme.{0}} {X : Type} [AddCommGroup X]

theorem charUnit_appTop {Z : Scheme.{0}} (τ : Z ⟶ (splitTorus S X).left) (χ : X) :
    τ.appTop.hom (charUnit S X χ).val =
      (τ ≫ tFst X).appTop.hom ((Scheme.ΓSpecIso (torusRing ZU X)).inv.hom (AddMonoidAlgebra.single χ 1)) := by
  rw [charUnit_val, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
  congr 2
  first
  | (rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; simp only [Scheme.Hom.preimage_top])
  | (simp [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE, Scheme.Hom.preimage_top])
  | (ext1; simp [Scheme.Hom.appLE, Scheme.Hom.appTop])

theorem ringHom_ext_ZU {A : Type} [CommRing A] {f g : AddMonoidAlgebra ZU.{0} X →+* A}
    (h : ∀ χ, f (AddMonoidAlgebra.single χ 1) = g (AddMonoidAlgebra.single χ 1)) : f = g := by
  refine AddMonoidAlgebra.ringHom_ext (fun b => ?_) h
  have e : (AddMonoidAlgebra.single 0 b : AddMonoidAlgebra ZU.{0} X) = ((b.down : ℤ) : AddMonoidAlgebra ZU.{0} X) := by
    rw [AddMonoidAlgebra.intCast_def]
    congr 1
  rw [e, map_intCast, map_intCast]

theorem torusPt_ext {Z : Over S} {τ₁ τ₂ : Z ⟶ splitTorus S X}
    (h : ∀ χ, τ₁.left.appTop.hom (charUnit S X χ).val = τ₂.left.appTop.hom (charUnit S X χ).val) :
    τ₁ = τ₂ := by
  have key : ∀ f g : Z.left ⟶ Spec (torusRing ZU X),
      (Scheme.ΓSpecIso (torusRing ZU X)).inv ≫ f.appTop = (Scheme.ΓSpecIso (torusRing ZU X)).inv ≫ g.appTop →
        f = g := by
    intro f g hfg
    have hh : ∀ f' : Z.left ⟶ Spec (torusRing ZU X), (Scheme.ΓSpecIso (torusRing ZU X)).inv ≫ f'.appTop =
        ((ΓSpec.adjunction.homEquiv Z.left (Opposite.op (torusRing ZU X))).symm f').unop := by
      intro f'
      have h0 := ΓSpecIso_inv_ΓSpec_adjunction_homEquiv
        ((ΓSpec.adjunction.homEquiv Z.left (Opposite.op (torusRing ZU X))).symm f').unop
      have hf : f' = ΓSpec.adjunction.homEquiv Z.left (Opposite.op (torusRing ZU X))
          ((ΓSpec.adjunction.homEquiv Z.left (Opposite.op (torusRing ZU X))).symm f').unop.op :=
        ((ΓSpec.adjunction.homEquiv Z.left (Opposite.op (torusRing ZU X))).apply_symm_apply f').symm
      conv_lhs => rw [hf]
      exact h0
    have hψ := (hh f).symm.trans (hfg.trans (hh g))
    exact (ΓSpec.adjunction.homEquiv Z.left (Opposite.op (torusRing ZU X))).symm.injective
      (congrArg Quiver.Hom.op hψ)
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · apply key
    apply CommRingCat.hom_ext
    apply ringHom_ext_ZU
    intro χ
    have e1 := charUnit_appTop τ₁.left χ
    have e2 := charUnit_appTop τ₂.left χ
    simp only [CommRingCat.hom_comp, RingHom.comp_apply]
    erw [← e1, ← e2]
    exact h χ
  · exact (Over.w τ₁).trans (Over.w τ₂).symm

end ReciprocityTheory.ChartRestriction.G.Semi.TorusPts
end
end

section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {D : Datum H} {l : Level H} {c : Coeff l}

def WeilRosatiSt : Prop :=
  ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : Out.PolAV S) (O : Type) [Ring O] [StarRing O] (o : P.OAct O)
    (k : ℕ) (T : Over S) (x y : T ⟶ P.A) (a : O) (c : Γ(T.left, ⊤)ˣ), x ^ k = 1 → y ^ k = 1 →
    (Out.WeilIs P.A P.L k (x ≫ o.act a) y c ↔ Out.WeilIs P.A P.L k x (y ≫ o.act (star a)) c)

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
end
end
