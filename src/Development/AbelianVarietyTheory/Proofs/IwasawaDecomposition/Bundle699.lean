module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle206
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqAddOfRedVEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle685
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle686
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DominatesLinearFormsOnBalancedFormsCm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsStrictFaceOfSmoothConePolyhedralFan
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinearOnIsFineOfLinearOnPolarisationBaseFunction
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLieEigenpartsFrameFamilyOverVariety
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle008
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle243
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle682
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf

@[expose] public section

section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix


theorem _root_.GlobalTheory.T.chernPolyTopDensity_grassmannRelation_origin_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) {n : ℕ} (ix : Fin n ≃ GlobalTheory.AllWt.Psi H × Fin Dw.p × Fin Dw.q) (τ : GlobalTheory.AllWt.Psi H) (k : ℕ), 1 ≤ k → ∀ P : MvPolynomial ((E →+* ℂ) × ℕ) ℝ, chernTop (relPoly τ k * P) (fun u => modelGram H Dw (coordOf ix u)) 0 = 0 := by
  first | exact @GlobalTheory.PointChernRel.relation_top_zero | exact GlobalTheory.PointChernRel.relation_top_zero | (intros; apply GlobalTheory.PointChernRel.relation_top_zero <;> assumption)
end

section

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef

namespace GlobalTheory.PolFan

section Round

variable {O : Type} [CommRing O] (bar : O → O)

def IsMultCell (φ : InvFun O) (M : ℕ) {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X] {m : ℕ}
    (δ : Fin m → LinearMap.BilinForm ℤ X) : Prop :=
  ∃ h : IsCell bar φ δ, LinearIndependent ℤ δ ∧ (∀ i, IsPrim bar (⟨δ i, h.mem i⟩ : balForms bar X)) ∧
    cellMult bar (fun i => (⟨δ i, h.mem i⟩ : balForms bar X)) = M


variable (O) in
structure FormFamily : Type 1 where

  X : Type
  [acg : AddCommGroup X]
  [mod : Module O X]

  m : ℕ

  δ : Fin m → LinearMap.BilinForm ℤ X

attribute [instance] FormFamily.acg FormFamily.mod

variable {bar}

def FormFamily.Carries (c : FormFamily O) {X : Type} [AddCommGroup X] [Module O X] {m : ℕ}
    (δ : Fin m → LinearMap.BilinForm ℤ X) : Prop :=
  ∃ (e : X ≃ₗ[O] c.X) (s : Fin m ≃ Fin c.m), ∀ i, δ i = pull e.toLinearMap (c.δ (s i))


variable (bar) in
def MultCellsAmong (q : ℕ) (φ : InvFun O) (M n : ℕ) : Prop :=
  ∃ R : Fin n → FormFamily O, ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X],
    Module.finrank O X ≤ q → ∀ (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X), IsMultCell bar φ M δ → ∃ k, (R k).Carries δ

end Round

end GlobalTheory.PolFan
end
end

section

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef

namespace GlobalTheory.PolFan

section Defs

variable {O : Type} [CommRing O] (bar : O → O) (q : ℕ)

def InRCone {X : Type} [AddCommGroup X] {m : ℕ} (γ : Fin m → LinearMap.BilinForm ℤ X) (β : LinearMap.BilinForm ℤ X) :
    Prop :=
  ∃ c : Fin m → ℝ, (∀ i, 0 ≤ c i) ∧ toReal β = ∑ i, c i • toReal (γ i)

def genRank {X : Type} [AddCommGroup X] {m : ℕ} (γ : Fin m → LinearMap.BilinForm ℤ X) : ℕ :=
  Module.finrank ℤ (Submodule.span ℤ (Set.range γ))

def IsCarrierDim (ψ lab : InvFun O) : Prop :=
  ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q →
    ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) →
      lab.evalZ β = ((sInf {k : ℕ | ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ γ ∧ InRCone γ β ∧
        genRank γ = k} : ℕ) : ℝ)

def IsBaryStage (ψ lab φ : InvFun O) (i : ℕ) : Prop :=
  IsPolyFan bar q φ ∧ Subordinate bar q φ ψ ∧
  ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q →
    ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar φ γ →
      ∃ (b a : ℕ) (v : Fin b → LinearMap.BilinForm ℤ X) (u : Fin a → LinearMap.BilinForm ℤ X),
        IsCell bar φ (Fin.append v u) ∧ IsCell bar ψ v ∧ (∀ j, InRCone (Fin.append v u) (γ j)) ∧
        Function.Injective (fun j => lab.evalZ (u j)) ∧ (∀ j, (i : ℝ) < lab.evalZ (u j)) ∧
        (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone v β → lab.evalZ β ≤ i) ∧
        (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone (Fin.append v u) β → ¬ InRCone v β → (i : ℝ) < lab.evalZ β) ∧
        ∀ (d : Fin b → ℤ) (c : Fin a → ℤ), ∑ j, c j • u j = ∑ k, d k • v k → c = 0

def IsCentreSet (ψ w : InvFun O) : Prop :=
  ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q →
    (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → w.evalZ β = 0 ∨ w.evalZ β = 1) ∧
    (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → w.evalZ β = 1 →
      ∀ (k : ℕ) (β' : LinearMap.BilinForm ℤ X), (k : ℤ) • β' = β → k = 1) ∧
    ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ γ →
      ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → ∀ β' ∈ balForms bar X, (∀ y, 0 ≤ β' y y) →
        w.evalZ β = 1 → w.evalZ β' = 1 → InRCone γ β → InRCone γ β' → β = β'

def IsFaceCut {X : Type} [AddCommGroup X] {m m' : ℕ} (γ : Fin m → LinearMap.BilinForm ℤ X) (s : Fin m' ↪ Fin m)
    (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ) : Prop :=
  (∀ j, 0 ≤ h (γ j)) ∧ ∀ j, h (γ j) = 0 ↔ j ∈ Set.range s

def IsStarOf (ψ w ψ' : InvFun O) : Prop :=
  (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q →
    ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ γ →
      (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone γ β → w.evalZ β = 0) → IsCell bar ψ' γ) ∧
  (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q →
    ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ γ →
      ∀ β₀ ∈ balForms bar X, (∀ y, 0 ≤ β₀ y y) → w.evalZ β₀ = 1 → InRCone γ β₀ →
        ∀ (m' : ℕ) (s : Fin m' ↪ Fin m) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsFaceCut γ s h → 0 < h β₀ →
          IsCell bar ψ' (Fin.cons β₀ fun j => γ (s j))) ∧
  ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q →
    ∀ (n : ℕ) (γ' : Fin n → LinearMap.BilinForm ℤ X), IsCell bar ψ' γ' →
      (∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ γ ∧
        (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone γ β → w.evalZ β = 0) ∧ ∀ j, InRCone γ (γ' j)) ∨
      ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (β₀ : LinearMap.BilinForm ℤ X) (m' : ℕ) (s : Fin m' ↪ Fin m)
        (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsCell bar ψ γ ∧ β₀ ∈ balForms bar X ∧ (∀ y, 0 ≤ β₀ y y) ∧
        w.evalZ β₀ = 1 ∧ InRCone γ β₀ ∧ IsFaceCut γ s h ∧ 0 < h β₀ ∧
        ∀ j, InRCone (Fin.cons β₀ fun j => γ (s j)) (γ' j)

end Defs

section Basic

variable {O : Type} [CommRing O] {bar : O → O} {q : ℕ}

theorem inRCone_self {X : Type} [AddCommGroup X] {m : ℕ} (γ : Fin m → LinearMap.BilinForm ℤ X) (j : Fin m) :
    InRCone γ (γ j) :=
  ⟨Pi.single j 1, fun i => by by_cases h : i = j <;> simp [Pi.single_apply, h], by
    rw [Finset.sum_eq_single j (fun i _ hi => by simp [Pi.single_apply, hi]) (by simp)]
    simp⟩

theorem isBaryStage_start {ψ lab : InvFun O} (hψ : IsPolyFan bar q ψ) {N : ℕ}
    (hN : ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q →
      ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → lab.evalZ β ≤ N) :
    IsBaryStage bar q ψ lab ψ N := by
  refine ⟨hψ, Subordinate.refl ψ, fun X _ _ _ _ hX m γ hγ => ?_⟩
  have e : Fin.append γ (Fin.elim0 : Fin 0 → LinearMap.BilinForm ℤ X) = γ := by
    funext i; simp [Fin.append_elim0]
  refine ⟨m, 0, γ, Fin.elim0, by rw [e]; exact hγ, hγ, fun j => by rw [e]; exact inRCone_self γ j,
    fun i => i.elim0, fun i => i.elim0, fun β hβ hp _ => hN X hX β hβ hp, fun β _ _ h h' => (h' (e ▸ h)).elim,
    fun d c _ => funext fun i => i.elim0⟩

end Basic

end GlobalTheory.PolFan
end
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

theorem _root_.GlobalTheory.T.cell_generators_smul_mem_other_cellCone : ∀ {O : Type} [CommRing O] (bar : O → O) (φ : InvFun O) {X : Type} [AddCommGroup X] [Module O X]
    [Module.Finite O X] {m m' : ℕ} (δ : Fin m → LinearMap.BilinForm ℤ X) (γ : Fin m' → LinearMap.BilinForm ℤ X)
    (c : Fin m' → ℝ), IsCell bar φ δ → IsCell bar φ γ → (∀ j, 0 ≤ c j) →
    ∑ i, toReal (δ i) = ∑ j, c j • toReal (γ j) →
    ∀ i, ∃ (k : ℕ) (a : Fin m' → ℕ), 0 < k ∧ k • δ i = ∑ j, a j • γ j := by
  first | exact @GlobalTheory.PolFan.exists_smul_eq_sum_of_sum_toReal_eq | exact GlobalTheory.PolFan.exists_smul_eq_sum_of_sum_toReal_eq | (intros; apply GlobalTheory.PolFan.exists_smul_eq_sum_of_sum_toReal_eq <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

theorem _root_.GlobalTheory.T.polarisationBaseFunction_properties : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (g q : ℕ) (φs : InvFun ℤ) (𝓜 : Finset ℕ) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], IsPolFan (id : ℤ → ℤ) g φs → Module.finrank ℚ E * q ≤ g → Module.finrank (𝓞 E) X ≤ q → (∀ B ∈ psdCone (bar := H.bar) (X := X), ∀ t : ℝ, 0 ≤ t → evalR (baseFun (𝓞 E) (fineDen g 𝓜) φs 𝓜) (t • B) = t * evalR (baseFun (𝓞 E) (fineDen g 𝓜) φs 𝓜) B) ∧ (∀ B ∈ psdCone (bar := H.bar) (X := X), ∀ B' ∈ psdCone (bar := H.bar) (X := X), evalR (baseFun (𝓞 E) (fineDen g 𝓜) φs 𝓜) B + evalR (baseFun (𝓞 E) (fineDen g 𝓜) φs 𝓜) B' ≤ evalR (baseFun (𝓞 E) (fineDen g 𝓜) φs 𝓜) (B + B')) ∧ (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → ∃ n : ℤ, (baseFun (𝓞 E) (fineDen g 𝓜) φs 𝓜).evalZ β = n) ∧ (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → β ≠ 0 → 0 < (baseFun (𝓞 E) (fineDen g 𝓜) φs 𝓜).evalZ β) := by
  first | exact @GlobalTheory.PolFan.baseFun_props | exact GlobalTheory.PolFan.baseFun_props | (intros; apply GlobalTheory.PolFan.baseFun_props <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

theorem _root_.GlobalTheory.T.cellGenerator_on_ray_of_linIndep_subcell : ∀ (O : Type) [CommRing O] (bar : O → O) (φ : InvFun O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] (m n : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X) (γ : Fin n → LinearMap.BilinForm ℤ X) (c : Fin n → ℝ), IsCell bar φ δ → IsCell bar φ γ → LinearIndependent ℤ δ → (∀ j, 0 ≤ c j) → ∑ i, toReal (δ i) = ∑ j, c j • toReal (γ j) → ∀ i, ∃ (j : Fin n) (a b : ℕ), 0 < a ∧ 0 < b ∧ a • δ i = b • γ j := by
  first | exact @GlobalTheory.PolFan.cell_gen_on_ray | exact GlobalTheory.PolFan.cell_gen_on_ray | (intros; apply GlobalTheory.PolFan.cell_gen_on_ray <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

theorem _root_.GlobalTheory.T.dominatesLinearFormsOnBalancedForms_cm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Dominates H.bar X := by
  first | exact @GlobalTheory.DomBal.dominates | exact GlobalTheory.DomBal.dominates | (intros; apply GlobalTheory.DomBal.dominates <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

theorem _root_.GlobalTheory.T.isStrict_face_of_smoothCone_polyhedralFan : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (φ : InvFun O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X], IsPolyFanOn bar φ X → Dominates bar X → ∀ (m m' : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (s : Fin m' ↪ Fin m), IsCone bar φ γ → IsStrict bar φ fun i => γ (s i) := by
  first | exact @GlobalTheory.PolFan.FaceStrict.isStrict_face_of_isCone | exact GlobalTheory.PolFan.FaceStrict.isStrict_face_of_isCone | (intros; apply GlobalTheory.PolFan.FaceStrict.isStrict_face_of_isCone <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

theorem _root_.GlobalTheory.T.linearOn_isFine_of_linearOn_polarisationBaseFunction : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (g q D : ℕ) (φs : InvFun ℤ) (𝓜 : Finset ℕ) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], 0 < D → IsPolFan (id : ℤ → ℤ) g φs → Module.finrank ℚ E * q ≤ g → Module.finrank (𝓞 E) X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), (∀ i, γ i ∈ balForms H.bar X) → (∀ i y, 0 ≤ γ i y y) → (baseFun (𝓞 E) D φs 𝓜).LinearOn γ → (restr (𝓞 E) φs).LinearOn γ ∧ ∀ M ∈ 𝓜, IsFine (M + 1) γ := by
  first | exact @GlobalTheory.PolFan.linearOn_and_isFine_of_linearOn_baseFun | exact GlobalTheory.PolFan.linearOn_and_isFine_of_linearOn_baseFun | (intros; apply GlobalTheory.PolFan.linearOn_and_isFine_of_linearOn_baseFun <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical

set_option autoImplicit false

noncomputable section

open GlobalTheory.Cartier

namespace GlobalTheory.ShFam.FlagTie

section Tri

variable {ι : Type} {m : ι → ℕ} {K : Type} [Field K]

def Lower (g : Mat m K) : Prop := ∀ τ (i k : Fin (m τ)), i < k → g τ i k = 0

theorem lower_iff_blockTriangular (g : Mat m K) (τ : ι) :
    (∀ i k : Fin (m τ), i < k → g τ i k = 0) ↔ (g τ).BlockTriangular OrderDual.toDual :=
  ⟨fun h _ _ hik => h _ _ hik, fun h _ _ hik => h hik⟩

theorem Lower.mul {g h : Mat m K} (hg : Lower g) (hh : Lower h) : Lower (g * h) := fun τ =>
  (lower_iff_blockTriangular (g * h) τ).2
    (((lower_iff_blockTriangular g τ).1 (hg τ)).mul ((lower_iff_blockTriangular h τ).1 (hh τ)))

theorem Lower.inv {g : Mat m K} (hg : Lower g) : Lower g⁻¹ := fun τ => by
  by_cases hd : (g τ).det = 0
  · intro i k _
    show (g τ)⁻¹ i k = 0
    rw [Matrix.nonsing_inv_apply_not_isUnit _ (by simp [hd])]
    rfl
  · have := (g τ).invertibleOfIsUnitDet (Ne.isUnit hd)
    exact (lower_iff_blockTriangular g⁻¹ τ).2
      (Matrix.blockTriangular_inv_of_blockTriangular ((lower_iff_blockTriangular g τ).1 (hg τ)))

theorem Lower.det_eq {g : Mat m K} (hg : Lower g) (τ : ι) : (g τ).det = ∏ i, g τ i i :=
  Matrix.det_of_lowerTriangular _ ((lower_iff_blockTriangular g τ).1 (hg τ))

theorem lower_one : Lower (1 : Mat m K) := fun _ _ _ hik => Matrix.one_apply_ne hik.ne

theorem par_full_iff {O : Subring K} {g : Mat m K} : Par m O g ↔ Par 0 O g ∧ Lower g := by
  constructor
  · intro h
    exact ⟨h.mono (fun _ => Nat.zero_le _) le_rfl, fun τ i k hik => (h τ).2.2.2 i k i.2 hik⟩
  · rintro ⟨h, hl⟩ τ
    exact ⟨(h τ).1, (h τ).2.1, (h τ).2.2.1, fun i k _ hik => hl τ i k hik⟩

theorem lower_mul_iff {B L : Mat m K} (hl : Lower L) (hL : ∀ τ, (L τ).det ≠ 0) : Lower (B * L) ↔ Lower B := by
  refine ⟨fun h => ?_, fun h => h.mul hl⟩
  have := h.mul hl.inv
  rwa [mul_assoc, Mat.mul_inv hL, mul_one] at this

end Tri

section Nhds

variable {F : Type} [Field F] {ι : Type} [Finite ι] {m : ι → ℕ}

theorem mem_O_generic (Y : Var F) (x : Y.Fn) : x ∈ ((ratOf Y).O (genericPoint Y.X)).toSubring :=
  (mem_O_ratOf (Y := Y) (y := genericPoint Y.X) (g := x)).2 ⟨x, by
    show (Y.X.presheaf.stalkSpecializes _).hom x = x
    rw [TopCat.Presheaf.stalkSpecializes_refl]; rfl⟩

theorem eventually_mem_O {Y : Var F} {z : Y.X} {g : Y.Fn} (h : g ∈ ((ratOf Y).O z).toSubring) :
    ∀ᶠ z' in nhds z, g ∈ ((ratOf Y).O z').toSubring := by
  obtain ⟨U, hz, a, rfl⟩ := (mem_O_ratOf.1 h).exists_fnOf
  exact Filter.eventually_of_mem (U.isOpen.mem_nhds hz) fun z' hz' => mem_O_ratOf.2 (regAt_fnOf hz' _ a)

theorem eventually_par {Y : Var F} {z : Y.X} {g : Mat m Y.Fn} (h : Par 0 ((ratOf Y).O z).toSubring g) :
    ∀ᶠ z' in nhds z, Par 0 ((ratOf Y).O z').toSubring g := by
  have h1 : ∀ᶠ z' in nhds z, ∀ τ i j, g τ i j ∈ ((ratOf Y).O z').toSubring :=
    Filter.eventually_all.2 fun τ => Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j =>
      eventually_mem_O ((h τ).1 i j)
  have h2 : ∀ᶠ z' in nhds z, ∀ τ, (g τ).det⁻¹ ∈ ((ratOf Y).O z').toSubring :=
    Filter.eventually_all.2 fun τ => eventually_mem_O (h τ).2.2.1
  filter_upwards [h1, h2] with z' h1 h2 τ
  exact ⟨h1 τ, (h τ).2.1, h2 τ, fun i j hi => absurd hi (Nat.not_lt_zero _)⟩

end Nhds

section Main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {F : Type} [Field F] {e : F ≃+* c.F}

abbrev base (C : FlagCpt Z e) : Fr (ratOf C.Y) Dw.mult 0 := TieBase.fam e C.Y C.π C.π_str C.f0

theorem exists_lower (C : FlagCpt Z e) (y : C.Y.X) :
    ∃ (L : Mat Dw.mult C.Y.Fn) (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → C.Y.Fnˣ),
      L⁻¹ ∈ (base C).S y ∧ (∀ τ, (L τ).det ≠ 0) ∧ Lower L ∧ (∀ τ i, L τ i i = t τ i) ∧
        ∀ τ i, (C.gr τ i).IsEqn y (t τ i) := by
  obtain ⟨φ, f, t, htri, hgr⟩ := C.gr_spec y
  obtain ⟨L, hc, hd, hl⟩ := (EigFrame.tri_iff f _ C.f0 t).1 htri
  have hL : ∀ τ, (L τ).det ≠ 0 := fun τ => by
    rw [Lower.det_eq hl τ]
    exact Finset.prod_ne_zero_iff.2 fun i _ => by rw [hd]; exact (t τ i).ne_zero
  refine ⟨L, t, ?_, hL, hl, hd, hgr⟩
  show (∀ τ, (L⁻¹ τ).det ≠ 0) ∧ _
  refine ⟨fun τ => (Matrix.isUnit_det_of_right_inverse (congrFun (Mat.inv_mul hL) τ)).ne_zero, φ, f, ?_⟩
  rw [Mat.inv_inv hL]
  exact hc

theorem one_mem_base (C : FlagCpt Z e) : (1 : Mat Dw.mult C.Y.Fn) ∈ (base C).S (genericPoint C.Y.X) := by
  obtain ⟨A, hA⟩ := (base C).nonempty (genericPoint C.Y.X)
  refine (Fr.mem_iff hA).2 fun τ => ?_
  refine ⟨fun _ _ => mem_O_generic _ _, ?_, mem_O_generic _ _, fun i j hi => absurd hi (Nat.not_lt_zero _)⟩
  rw [one_mul]
  exact (Matrix.isUnit_det_of_right_inverse (congrFun (Mat.inv_mul (Fr.det_ne hA)) τ)).ne_zero

def flagFam (C : FlagCpt Z e) (A₁ : Mat Dw.mult C.Y.Fn) (hA₁ : ∀ τ, (A₁ τ).det ≠ 0) : Fr (ratOf C.Y) Dw.mult Dw.mult where
  S y := {A' | A' * A₁⁻¹ ∈ (base C).S y ∧ Lower (A' * A₁⁻¹)}
  loc z := by
    obtain ⟨L, -, hLS, hL, hl, -, -⟩ := exists_lower C z
    obtain ⟨U₀, T, hz, -, hU₀⟩ := (base C).loc z
    have hev : ∀ᶠ z' in nhds z, L⁻¹ ∈ (base C).S z' :=
      (Filter.eventually_and.2 ⟨Filter.eventually_of_mem (U₀.isOpen.mem_nhds hz) fun _ h => h,
        eventually_par ((hU₀ z hz L⁻¹).1 hLS)⟩).mono fun z' h => (hU₀ z' h.1 L⁻¹).2 h.2
    obtain ⟨W, hW, hWo, hzW⟩ := eventually_nhds_iff.1 hev
    refine ⟨⟨W, hWo⟩, L⁻¹ * A₁, hzW, fun τ => ?_, fun z' hz' A' => ?_⟩
    · rw [Pi.mul_apply, Matrix.det_mul]
      exact mul_ne_zero (Fr.det_ne hLS τ) (hA₁ τ)
    · have hz'' : L⁻¹ ∈ (base C).S z' := hW z' hz'
      show (A' * A₁⁻¹ ∈ (base C).S z' ∧ Lower (A' * A₁⁻¹)) ↔ _
      rw [Fr.mem_iff hz'', Mat.mul_inv_rev, Mat.inv_inv hL, ← mul_assoc, par_full_iff, lower_mul_iff hl hL]

theorem exists_tied_isGraded : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type)
    [Field F] (e : F ≃+* c.F) (C : FlagCpt Z e) (A₁ : Mat Dw.mult C.Y.Fn), (∀ τ, (A₁ τ).det ≠ 0) →
    ∃ E' : Fr (ratOf C.Y) Dw.mult Dw.mult, Tied e C.Y C.π C.f0 E' A₁ ∧ IsGraded E' (fun x : Root Dw.mult => C.gr x.1 x.2) := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e C A₁ hA₁
  have hA : A₁ ∈ (flagFam C A₁ hA₁).S (genericPoint C.Y.X) := by
    show A₁ * A₁⁻¹ ∈ (base C).S _ ∧ Lower (A₁ * A₁⁻¹)
    rw [Mat.mul_inv hA₁]
    exact ⟨one_mem_base C, lower_one⟩
  refine ⟨flagFam C A₁ hA₁, ⟨hA, fun y A h => ?_⟩, ⟨A₁, hA, fun y x => ?_⟩⟩
  · obtain ⟨-, φ, f, hf⟩ := h.1
    rw [Mat.mul_inv_rev, Mat.inv_inv hA₁] at hf
    exact ⟨φ, f, hf⟩
  · obtain ⟨L, t, hLS, hL, hl, hd, hgr⟩ := exists_lower C y
    refine ⟨L⁻¹ * A₁, ?_, t x.1 x.2, ?_, hgr x.1 x.2⟩
    · show L⁻¹ * A₁ * A₁⁻¹ ∈ (base C).S y ∧ Lower (L⁻¹ * A₁ * A₁⁻¹)
      rw [mul_assoc, Mat.mul_inv hA₁, mul_one]
      exact ⟨hLS, hl.inv⟩
    · rw [Mat.mul_inv_rev, Mat.inv_inv hL, ← mul_assoc, Mat.mul_inv hA₁, one_mul]
      exact hd _ _

end Main

end GlobalTheory.ShFam.FlagTie
end
end

section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame

namespace GlobalTheory.GoodMetric

open Polynomial in
theorem chernPoly_zero' {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (G : ReciprocityTheory.L2DbarEstimates.V n → Matrix r r ℂ)
    (v : ReciprocityTheory.L2DbarEstimates.V n) : chernPoly G v 0 = 1 := by
  rw [chernPoly, Polynomial.coeff_zero_eq_eval_zero, Matrix.eval_charpolyRev]

open Polynomial in
theorem chernPoly_above {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (G : ReciprocityTheory.L2DbarEstimates.V n → Matrix r r ℂ)
    (v : ReciprocityTheory.L2DbarEstimates.V n) (k : ℕ) (hk : Fintype.card r < k) : chernPoly G v k = 0 := by
  rw [chernPoly]
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  rw [← Matrix.reverse_charpoly]
  calc _ ≤ (Matrix.charpoly (-curvPoly G v)).natDegree := Polynomial.reverse_natDegree_le _
    _ = Fintype.card r := Matrix.charpoly_natDegree_eq_dim _
    _ < k := hk

theorem chernTop_unit : ∀ (n : ℕ) (ι : Type) (m : ι → ℕ) (G : ReciprocityTheory.L2DbarEstimates.V n → FlagBundle.Mat m ℂ) (v : ReciprocityTheory.L2DbarEstimates.V n) (τ : ι) (Q : MvPolynomial (ι × ℕ) ℝ), chernTop ((MvPolynomial.X (τ, 0) - 1) * Q) G v = 0 ∧ ∀ k : ℕ, m τ < k → chernTop (MvPolynomial.X (τ, k) * Q) G v = 0 := by
  intro n ι m G v τ Q
  refine ⟨?_, fun k hk => ?_⟩
  · simp only [chernTop, map_mul, map_sub, map_one, MvPolynomial.aeval_X, chernPoly_zero', sub_self, zero_mul,
      topCoeff, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply, mul_zero, Finset.sum_const_zero, Complex.zero_re]
  · have h := chernPoly_above (fun u => G u τ) v k (by simpa using hk)
    simp only [chernTop, map_mul, MvPolynomial.aeval_X, h, zero_mul,
      topCoeff, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply, mul_zero, Finset.sum_const_zero, Complex.zero_re]

end GlobalTheory.GoodMetric
end

section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology

namespace GlobalTheory.GoodMetric

theorem goodBound_congr_nhds (n : ℕ) (r : Type) [Fintype r] [DecidableEq r] (S : Finset (Fin n)) (c : ℝ) (N : ℕ)
    (G G' : ReciprocityTheory.L2DbarEstimates.V n → Matrix r r ℂ) (v : ReciprocityTheory.L2DbarEstimates.V n) :
    G =ᶠ[nhds v] G' → GlobalTheory.GoodMetric.GoodBound S c N G v → GlobalTheory.GoodMetric.GoodBound S c N G' v := by
  intro h hb
  have hv : G v = G' v := h.eq_of_nhds
  have hc : ∀ ξ, (fun u => GlobalTheory.HermFrame.conn G u ξ) =ᶠ[nhds v] (fun u => GlobalTheory.HermFrame.conn G' u ξ) :=
    fun ξ => h.eventuallyEq_nhds.mono fun x hx => GlobalTheory.HermFrame.conn_congr hx ξ
  refine ⟨fun i j => ?_, ?_, fun a i j => ?_, fun a b i j => ?_, fun a b i j => ?_⟩
  · rw [← hv]; exact hb.entry i j
  · rw [← hv]; exact hb.det
  · rw [← GlobalTheory.HermFrame.conn_congr h]; exact hb.form a i j
  · rw [← GlobalTheory.HermFrame.curv_congr h]; exact hb.dbar a b i j
  · rw [← GlobalTheory.HermFrame.mdel_congr (hc _), ← GlobalTheory.HermFrame.mdel_congr (hc _)]; exact hb.del a b i j

end GlobalTheory.GoodMetric
end
