module

public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.NumberTheory.NumberField.Units.Basic
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open NumberField

namespace PositivityTheory.KB.SplitAffineSpectral.EigenLocalizationShapes

variable (L : Type) [Field L] [NumberField L]

def embLin (σ : L →+* ℂ) : 𝓞 L →ₗ[ℤ] ℂ := (σ.comp (algebraMap (𝓞 L) L)).toAddMonoidHom.toIntLinearMap

def coeLin : (𝓞 L →ₗ[ℤ] ℂ) →ₗ[ℂ] (𝓞 L → ℂ) where
  toFun f := ⇑f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem embLin_linIndep : LinearIndependent ℂ (embLin L) := by
  have hinj : Function.Injective
      (fun σ : L →+* ℂ => ((σ.comp (algebraMap (𝓞 L) L)).toMonoidHom : 𝓞 L →* ℂ)) := by
    intro σ τ h
    apply IsFractionRing.ringHom_ext (A := 𝓞 L)
    intro x
    exact DFunLike.congr_fun h x
  have h1 := (linearIndependent_monoidHom (𝓞 L) ℂ).comp _ hinj
  apply LinearIndependent.of_comp (coeLin L)
  exact h1

theorem finrank_lin : Module.finrank ℂ (𝓞 L →ₗ[ℤ] ℂ) = Fintype.card (L →+* ℂ) := by
  rw [Module.finrank_linearMap_self, NumberField.RingOfIntegers.rank, NumberField.Embeddings.card]

theorem emb_span (α : 𝓞 L →+ ℝ) :
    ∃ c : (L →+* ℂ) → ℂ, ∀ x : 𝓞 L, (α x : ℂ) = ∑ σ, c σ * σ (algebraMap (𝓞 L) L x) := by
  have hspan := (embLin_linIndep L).span_eq_top_of_card_eq_finrank' (finrank_lin L).symm
  let f : 𝓞 L →ₗ[ℤ] ℂ := ((Complex.ofRealHom : ℝ →+* ℂ).toAddMonoidHom.comp α).toIntLinearMap
  have hf : f ∈ Submodule.span ℂ (Set.range (embLin L)) := by
    rw [hspan]
    exact Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hf
  refine ⟨c, fun x => ?_⟩
  have hx := LinearMap.congr_fun hc x
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul] at hx
  exact hx.symm

theorem mat_span (n r : ℕ) (α : Additive (Multiplicative (Matrix (Fin n) (Fin r) (𝓞 L))) →+ ℝ) :
    ∃ c : Fin n × Fin r × (L →+* ℂ) → ℂ, ∀ x,
      (α x : ℂ) = ∑ j, c j * j.2.2 (algebraMap (𝓞 L) L
        (Multiplicative.toAdd (Additive.toMul x) j.1 j.2.1)) := by
  let e : Matrix (Fin n) (Fin r) (𝓞 L) →+ Additive (Multiplicative (Matrix (Fin n) (Fin r) (𝓞 L))) :=
    { toFun := fun m => Additive.ofMul (Multiplicative.ofAdd m)
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hc : ∀ i j, ∃ c : (L →+* ℂ) → ℂ, ∀ y : 𝓞 L,
      ((α.comp (e.comp (Matrix.singleAddMonoidHom i j))) y : ℂ) =
        ∑ σ, c σ * σ (algebraMap (𝓞 L) L y) :=
    fun i j => emb_span L _
  choose c hc using hc
  refine ⟨fun j => c j.1 j.2.1 j.2.2, fun x => ?_⟩
  have lhs : (α x : ℂ) = ∑ i, ∑ j, ((α.comp (e.comp (Matrix.singleAddMonoidHom i j)))
      (Multiplicative.toAdd (Additive.toMul x) i j) : ℂ) := by
    have hx : x = e (Multiplicative.toAdd (Additive.toMul x)) := rfl
    conv_lhs => rw [hx, Matrix.matrix_eq_sum_single (Multiplicative.toAdd (Additive.toMul x))]

    simp only [map_sum, Complex.ofReal_sum]
    rfl
  rw [lhs]
  simp only [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  exact hc i j _

end PositivityTheory.KB.SplitAffineSpectral.EigenLocalizationShapes
end
end

section

noncomputable section

open NumberField

namespace PositivityTheory.KB.SplitAffineSpectral

def dc {Y : Type} {m : ℕ} (F : (Fin (m + 1) → Y) → ℝ) : (Fin (m + 2) → Y) → ℝ :=
  fun y => ∑ i : Fin (m + 2), (-1 : ℝ) ^ (i : ℕ) * F fun j => y (i.succAbove j)

def InvS {P : Type} [Group P] (S : Set P) {m : ℕ} (F : (Fin m → P) → ℝ) : Prop :=
  ∀ g ∈ S, ∀ y, F (fun j => g * y j) = F y

def mapOp {A : Type} (φ : A → A) (m : ℕ) : Module.End ℝ ((Fin m → A) → ℝ) where
  toFun c y := c fun i => φ (y i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def ColPoly {P Q : Type} [Group P] [Group Q] (pr : P →* Q) (s : Q →* P) (u : Q) (m : ℕ) : Prop :=
  ∀ q : ℕ, q + 1 ≤ m → ∃ f : Polynomial ℝ, f.eval 1 ≠ 0 ∧
    ∀ c : (Fin (q + 2) → P) → ℝ, InvS (pr.ker : Set P) c → dc c = 0 →
      ∃ e : (Fin (q + 1) → P) → ℝ, InvS (pr.ker : Set P) e ∧
        Polynomial.aeval (mapOp (fun y => (s u)⁻¹ * y * s u) (q + 2)) f c = dc e

def Core : Prop :=
  ∀ (P Q : Type) [Group P] [Group Q] (pr : P →* Q) (s : Q →* P), (∀ g, pr (s g) = g) →
    ∀ u : Q, (∀ g, g * u = u * g) → ∀ m : ℕ, ColPoly pr s u m →
    ∀ j : ℕ, j + 1 ≤ m → ∀ c : (Fin (j + 2) → P) → ℝ, InvS Set.univ c → dc c = 0 →
      (∀ y : Fin (j + 2) → Q, c (fun i => s (y i)) = 0) →
      ∃ e : (Fin (j + 1) → P) → ℝ, InvS Set.univ e ∧ c = dc e

def APoly (A : Type) [Group A] (φ : A → A) (m : ℕ) : Prop :=
  ∀ q : ℕ, q + 1 ≤ m → ∃ f : Polynomial ℝ, f.eval 1 ≠ 0 ∧
    ∀ c : (Fin (q + 2) → A) → ℝ, InvS Set.univ c → dc c = 0 →
      ∃ e : (Fin (q + 1) → A) → ℝ, InvS Set.univ e ∧ Polynomial.aeval (mapOp φ (q + 2)) f c = dc e

def Transfer : Prop :=
  ∀ (P Q A : Type) [Group P] [Group Q] [Group A] (pr : P →* Q) (s : Q →* P), (∀ g, pr (s g) = g) →
    ∀ u : Q, (∀ g, g * u = u * g) → ∀ (ι : A →* P), Function.Injective ι → (∀ x, pr x = 1 ↔ x ∈ ι.range) →
    ∀ φ : A →* A, (∀ a, ι (φ a) = (s u)⁻¹ * ι a * s u) → ∀ m : ℕ, APoly A φ m → ColPoly pr s u m

def cupH {A : Type} [Group A] {q : ℕ} (α : Fin q → (Additive A →+ ℝ)) (y : Fin (q + 1) → A) : ℝ :=
  ∏ i : Fin q, α i (Additive.ofMul ((y i.castSucc)⁻¹ * y i.succ))

def Span : Prop :=
  ∀ (A : Type) [CommGroup A] [Module.Free ℤ (Additive A)] [Module.Finite ℤ (Additive A)] (q : ℕ)
    (c : (Fin (q + 2) → A) → ℝ), InvS Set.univ c → dc c = 0 →
      ∃ (k : ℕ) (a : Fin k → ℝ) (α : Fin k → Fin (q + 1) → (Additive A →+ ℝ))
        (e : (Fin (q + 1) → A) → ℝ), InvS Set.univ e ∧ c = (∑ i, a i • cupH (α i)) + dc e

def Unit : Prop :=
  ∀ (L : Type) [Field L] [NumberField L], IsTotallyComplex L → ∀ m : ℕ, m < InfinitePlace.nrComplexPlaces L →
    ∃ v : (𝓞 L)ˣ, ∀ a : InfinitePlace L → ℕ, 0 < ∑ w, a w → ∑ w, a w ≤ m →
      ∏ w, (w (v : L)) ^ a w ≠ 1

def mulV {L : Type} [Field L] [NumberField L] (n r : ℕ) (v : 𝓞 L) :
    Multiplicative (Matrix (Fin n) (Fin r) (𝓞 L)) → Multiplicative (Matrix (Fin n) (Fin r) (𝓞 L)) :=
  fun B => Multiplicative.ofAdd (v • Multiplicative.toAdd B)

def Eigen : Prop :=
  ∀ (L : Type) [Field L] [NumberField L], IsTotallyComplex L → ∀ (m : ℕ) (v : (𝓞 L)ˣ),
    (∀ a : InfinitePlace L → ℕ, 0 < ∑ w, a w → ∑ w, a w ≤ m → ∏ w, (w (v : L)) ^ a w ≠ 1) →
    ∀ n r q : ℕ, q + 1 ≤ m → ∃ f : Polynomial ℝ, f.eval 1 ≠ 0 ∧
      ∀ α : Fin (q + 1) → (Additive (Multiplicative (Matrix (Fin n) (Fin r) (𝓞 L))) →+ ℝ),
        Polynomial.aeval (mapOp (mulV n r (v : 𝓞 L)) (q + 2)) f (cupH α) = 0

end PositivityTheory.KB.SplitAffineSpectral

end
end
