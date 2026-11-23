module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Multilinear.Basic
public import Mathlib.Tactic.Continuity
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.RingTheory.Length
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
import Mathlib.Order.CompletePartialOrder
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

namespace ReciprocityTheory.ChartRestriction.G.AI

open Polynomial

end ReciprocityTheory.ChartRestriction.G.AI
end

section

namespace ReciprocityTheory.ChartRestriction.G.AI

open MeasureTheory

abbrev E3 := EuclideanSpace ℝ (Fin 3)

noncomputable abbrev S2 := Metric.sphere (0 : E3) 1

noncomputable def sphereMeasure : Measure S2 :=
  ((volume : Measure E3).toSphere Set.univ)⁻¹ • (volume : Measure E3).toSphere

noncomputable def gPoly (k : ℕ) : MvPolynomial (Fin 2) ℝ :=
  MvPolynomial.X 1 * ∑ j ∈ Finset.range (2 * k),
    (-1 : ℝ) ^ j • (MvPolynomial.X 0 ^ (2 * k - 1 - j) * MvPolynomial.X 1 ^ j)

noncomputable def dgPoly (k : ℕ) : MvPolynomial (Fin 2) ℝ :=
  MvPolynomial.pderiv 0 (MvPolynomial.pderiv 1 (gPoly k))

noncomputable def kappa (k : ℕ) : ℝ :=
  -∫ n₁ : S2, ∫ n₂ : S2, (1 / 2 : ℝ) * Real.log ((1 - inner ℝ (n₁ : E3) (n₂ : E3)) / 2) *
      MvPolynomial.eval ![(n₁ : E3) 2, (n₂ : E3) 2] (dgPoly k) ∂sphereMeasure ∂sphereMeasure

def SphereInvStatement : Prop :=
  IsProbabilityMeasure sphereMeasure ∧
  ∀ L : E3 ≃ₗᵢ[ℝ] E3,
    MeasurePreserving (fun n : S2 => (⟨L n, by simp⟩ : S2)) sphereMeasure sphereMeasure

def ArchimedesStatement : Prop :=
  ∀ (u v w : E3) (f : ℝ → ℝ), ‖u‖ = 1 → IntervalIntegrable f volume (-1) 1 →
    Integrable (fun n : S2 => f (inner ℝ (n : E3) u)) sphereMeasure ∧
    (∫ n : S2, f (inner ℝ (n : E3) u) ∂sphereMeasure = (1 / 2) * ∫ t in (-1 : ℝ)..1, f t) ∧
    (∫ n : S2, f (inner ℝ (n : E3) u) * inner ℝ (n : E3) v ∂sphereMeasure =
      (1 / 2) * ∫ t in (-1 : ℝ)..1, f t * t * inner ℝ u v) ∧
    (∫ n : S2, f (inner ℝ (n : E3) u) * inner ℝ (n : E3) v * inner ℝ (n : E3) w ∂sphereMeasure =
      (1 / 2) * ∫ t in (-1 : ℝ)..1, f t * (t ^ 2 * (inner ℝ u v * inner ℝ u w) +
        (1 - t ^ 2) / 2 * (inner ℝ v w - inner ℝ u v * inner ℝ u w)))

end ReciprocityTheory.ChartRestriction.G.AI
end

section

namespace ReciprocityTheory.ChartRestriction.G.AI

universe u

open Polynomial

def mix {V : Type*} {n : ℕ} (k : ℕ) (x y : V) : Fin n → V :=
  fun i => if (i : ℕ) < k then x else y

def IsSymmForm {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ}
    (I : MultilinearMap (RingHom.id ℝ) (fun _ : Fin n => V) ℝ) : Prop :=
  ∀ (σ : Equiv.Perm (Fin n)) (v : Fin n → V), I (v ∘ σ) = I v

def word {VW : Type*} (D k i : ℕ) (x₁ x₂ a : VW) : Fin D → VW :=
  fun j => if (j : ℕ) = 0 then x₂ else if (j : ℕ) < 1 + 2 * i then x₁ else
    if (j : ℕ) < 2 * k - 1 then x₂ else a

noncomputable def volPoly (D : ℕ) (J : ℕ → ℝ) : ℝ[X] :=
  ∑ j ∈ Finset.range (D + 1), C ((D.choose j : ℝ) * J j) * (-X) ^ j

noncomputable def tsgPoly (D : ℕ) (κ : ℕ → ℝ) (P : ℝ[X]) : ℝ[X] :=
  ∑ n ∈ Finset.range (P.natDegree + 1),
    if Odd n then C (((D : ℝ) + 1) * κ ((n + 1) / 2) / (((n + 1) / 2 : ℕ) : ℝ) * P.coeff n) * X ^ (n + 1)
    else 0

structure FibreSquare (D : ℕ) where
  V : Type u
  [acgV : AddCommGroup V]
  [modV : Module ℝ V]
  VW : Type u
  [acgW : AddCommGroup VW]
  [modW : Module ℝ VW]
  I : MultilinearMap (RingHom.id ℝ) (fun _ : Fin (D + 1) => V) ℝ
  IW : MultilinearMap (RingHom.id ℝ) (fun _ : Fin (D + 2) => VW) ℝ
  p₁ : V →ₗ[ℝ] VW
  p₂ : V →ₗ[ℝ] VW
  ξ : V
  A : V
  Φ : MultilinearMap (RingHom.id ℝ) (fun _ : Fin D => VW) ℝ
  symm : IsSymmForm I
  symmW : IsSymmForm IW
  comp_right_eq_zero_alt : ∀ v : Fin (D + 2) → V, IW (fun j => p₂ (v j)) = 0
  cons_comp_left : ∀ v : Fin (D + 1) → V, IW (Fin.cons (-(p₂ ξ)) (fun j => p₁ (v j))) = I v
  base : p₁ A = p₂ A
  diag : ∀ T : Fin D → VW,
    IW (Fin.cons (p₁ ξ) (Fin.cons (p₁ ξ) T)) - IW (Fin.cons (p₂ ξ) (Fin.cons (p₂ ξ) T)) = Φ T

attribute [instance] FibreSquare.acgV FibreSquare.modV FibreSquare.acgW FibreSquare.modW

end ReciprocityTheory.ChartRestriction.G.AI
end

section

namespace ReciprocityTheory.ChartRestriction.G.AI

def IndexStatement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (O : Subring K),
    Module.Free ℤ O → Module.Finite ℤ O → Module.finrank ℤ O = Module.finrank ℚ K →
    ∀ f : O, f ≠ 0 →
      (Nat.card (O ⧸ Ideal.span {f}) : ℝ) = |(Algebra.norm ℚ (f : K) : ℝ)| ∧
      Real.log (Nat.card (O ⧸ Ideal.span {f})) = ∑ σ : K →+* ℂ, Real.log ‖σ f‖

end ReciprocityTheory.ChartRestriction.G.AI
end

section

namespace ReciprocityTheory.ChartRestriction.G.AI

open Module

theorem length_eq_ker_add_range {A : Type*} [Ring A] {M N : Type*} [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] (φ : M →ₗ[A] N) :
    length A M = length A (LinearMap.ker φ) + length A (LinearMap.range φ) := by
  exact Module.length_eq_add_of_exact (LinearMap.ker φ).subtype φ.rangeRestrict
    (Submodule.injective_subtype _) φ.surjective_rangeRestrict
    (by rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict, Submodule.range_subtype])

theorem length_eq_sub_add_quot {A : Type*} [Ring A] {M : Type*} [AddCommGroup M] [Module A M]
    (P : Submodule A M) : length A M = length A P + length A (M ⧸ P) :=
  Module.length_eq_add_of_exact P.subtype P.mkQ (Submodule.injective_subtype _) (Submodule.mkQ_surjective _)
    (LinearMap.exact_subtype_mkQ P)

theorem length_eq_range_add_range {A : Type*} [Ring A] {L M N : Type*}
    [AddCommGroup L] [Module A L] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] {ψ : L →ₗ[A] M} {φ : M →ₗ[A] N} (h : Function.Exact ψ φ) :
    length A M = length A (LinearMap.range ψ) + length A (LinearMap.range φ) := by
  rw [length_eq_ker_add_range φ, h.linearMap_ker_eq]

theorem length_six_term {A : Type*} [Ring A] {M₁ M₂ M₃ M₄ M₅ M₆ : Type*}
    [AddCommGroup M₁] [Module A M₁] [AddCommGroup M₂] [Module A M₂]
    [AddCommGroup M₃] [Module A M₃] [AddCommGroup M₄] [Module A M₄]
    [AddCommGroup M₅] [Module A M₅] [AddCommGroup M₆] [Module A M₆]
    {f₁ : M₁ →ₗ[A] M₂} {f₂ : M₂ →ₗ[A] M₃} {f₃ : M₃ →ₗ[A] M₄} {f₄ : M₄ →ₗ[A] M₅}
    {f₅ : M₅ →ₗ[A] M₆} (h₁ : Function.Injective f₁) (h₂ : Function.Exact f₁ f₂)
    (h₃ : Function.Exact f₂ f₃) (h₄ : Function.Exact f₃ f₄) (h₅ : Function.Exact f₄ f₅)
    (h₆ : Function.Surjective f₅) :
    length A M₁ + length A M₃ + length A M₅ = length A M₂ + length A M₄ + length A M₆ := by
  have e1 : length A M₁ = length A (LinearMap.range f₁) := (LinearEquiv.ofInjective f₁ h₁).length_eq
  have e6 : length A (LinearMap.range f₅) = length A M₆ :=
    (LinearEquiv.ofTop _ (LinearMap.range_eq_top.2 h₆)).length_eq
  rw [e1, length_eq_range_add_range h₂, length_eq_range_add_range h₃, length_eq_range_add_range h₄,
    length_eq_range_add_range h₅, ← e6]
  ring

def kerSmulMap {A : Type*} [CommRing A] {M N : Type*} [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] (f : M →ₗ[A] N) (x : A) :
    LinearMap.ker (LinearMap.lsmul A M x) →ₗ[A] LinearMap.ker (LinearMap.lsmul A N x) :=
  f.restrict (fun m hm => by
    rw [LinearMap.mem_ker, LinearMap.lsmul_apply] at hm ⊢
    rw [← map_smul, hm, map_zero])

def cokerSmulMap {A : Type*} [CommRing A] {M N : Type*} [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] (f : M →ₗ[A] N) (x : A) :
    (M ⧸ LinearMap.range (LinearMap.lsmul A M x)) →ₗ[A]
      (N ⧸ LinearMap.range (LinearMap.lsmul A N x)) :=
  Submodule.mapQ _ _ f (by
    rintro _ ⟨m, rfl⟩
    exact ⟨f m, by simp⟩)

theorem euler_ses {A : Type*} [CommRing A] {M' M M'' : Type*} [AddCommGroup M'] [Module A M']
    [AddCommGroup M] [Module A M] [AddCommGroup M''] [Module A M'']
    (f : M' →ₗ[A] M) (g : M →ₗ[A] M'') (hf : Function.Injective f) (hg : Function.Surjective g)
    (hex : Function.Exact f g) (x : A) :
    length A (LinearMap.ker (LinearMap.lsmul A M' x)) + length A (LinearMap.ker (LinearMap.lsmul A M'' x)) +
        length A (M ⧸ LinearMap.range (LinearMap.lsmul A M x)) =
      length A (LinearMap.ker (LinearMap.lsmul A M x)) +
        length A (M' ⧸ LinearMap.range (LinearMap.lsmul A M' x)) +
        length A (M'' ⧸ LinearMap.range (LinearMap.lsmul A M'' x)) := by
  have key : ∀ z : LinearMap.ker (LinearMap.lsmul A M'' x), ∃ (m : M) (m' : M'),
      g m = (z : M'') ∧ f m' = x • m := by
    intro z
    obtain ⟨m, hm⟩ := hg z
    have hz : x • (z : M'') = 0 := z.2
    obtain ⟨m', hm'⟩ := (hex (x • m)).1 (by rw [map_smul, hm, hz])
    exact ⟨m, m', hm, hm'⟩
  have indep : ∀ (m₁ : M) (m₁' : M') (m₂ : M) (m₂' : M'), g m₁ = g m₂ → f m₁' = x • m₁ →
      f m₂' = x • m₂ →
      Submodule.mkQ (LinearMap.range (LinearMap.lsmul A M' x)) m₁' =
        Submodule.mkQ (LinearMap.range (LinearMap.lsmul A M' x)) m₂' := by
    intro m₁ m₁' m₂ m₂' h h1 h2
    obtain ⟨n, hn⟩ := (hex (m₁ - m₂)).1 (by rw [map_sub, h, sub_self])
    have e : m₁' - m₂' = x • n := hf (by rw [map_sub, map_smul, hn, h1, h2, smul_sub])
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, e]
    exact ⟨n, rfl⟩
  choose lift liftP hlift using key
  obtain ⟨δ, hδ⟩ : ∃ δ : LinearMap.ker (LinearMap.lsmul A M'' x) →ₗ[A]
      (M' ⧸ LinearMap.range (LinearMap.lsmul A M' x)),
      ∀ (z : LinearMap.ker (LinearMap.lsmul A M'' x)) (m : M) (m' : M'), g m = (z : M'') → f m' = x • m →
        δ z = Submodule.mkQ (LinearMap.range (LinearMap.lsmul A M' x)) m' := by
    refine ⟨{ toFun := fun z => Submodule.mkQ (LinearMap.range (LinearMap.lsmul A M' x)) (liftP z),
              map_add' := ?_, map_smul' := ?_ }, ?_⟩
    · intro z₁ z₂
      show Submodule.mkQ _ (liftP (z₁ + z₂)) = Submodule.mkQ _ (liftP z₁) + Submodule.mkQ _ (liftP z₂)
      rw [← map_add (f := _)]
      exact indep _ _ (lift z₁ + lift z₂) _
        (by rw [(hlift _).1, map_add (f := _), (hlift z₁).1, (hlift z₂).1, Submodule.coe_add]) (hlift _).2
        (by rw [map_add (f := _), (hlift z₁).2, (hlift z₂).2, smul_add])
    · intro a z
      show Submodule.mkQ _ (liftP (a • z)) = a • Submodule.mkQ _ (liftP z)
      rw [← map_smul]
      exact indep _ _ (a • lift z) _
        (by rw [(hlift _).1, map_smul, (hlift z).1, Submodule.coe_smul]) (hlift _).2
        (by rw [map_smul, (hlift z).2, smul_comm])
    · intro z m m' h h'
      exact indep _ _ m m' (by rw [(hlift z).1, h]) (hlift z).2 h'
  have h₁ : Function.Injective (kerSmulMap f x) := by
    intro a b h
    apply Subtype.ext
    apply hf
    exact congrArg Subtype.val h
  have h₂ : Function.Exact (kerSmulMap f x) (kerSmulMap g x) := by
    intro y
    constructor
    · intro hy
      have hy0 : g y = 0 := congrArg Subtype.val hy
      obtain ⟨m', hm'⟩ := (hex y).1 hy0
      have hyx : x • (y : M) = 0 := y.2
      refine ⟨⟨m', ?_⟩, Subtype.ext hm'⟩
      show x • m' = 0
      apply hf
      rw [map_smul, hm', hyx, map_zero]
    · rintro ⟨w, rfl⟩
      apply Subtype.ext
      exact (hex _).2 ⟨w, rfl⟩
  have h₃ : Function.Exact (kerSmulMap g x) δ := by
    intro z
    constructor
    · intro hz
      obtain ⟨m, hm⟩ := hg z
      have hzx : x • (z : M'') = 0 := z.2
      obtain ⟨m', hm'⟩ := (hex (x • m)).1 (by rw [map_smul, hm, hzx])
      rw [hδ z m m' hm hm', Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hz
      obtain ⟨n, hn⟩ := LinearMap.mem_range.1 hz
      have hn' : x • n = m' := hn
      refine ⟨⟨m - f n, ?_⟩, Subtype.ext ?_⟩
      · show x • (m - f n) = 0
        rw [smul_sub, ← map_smul, hn', hm', sub_self]
      · show g (m - f n) = z
        rw [map_sub, hm, (hex _).2 ⟨n, rfl⟩, sub_zero]
    · rintro ⟨y, rfl⟩
      have hyx : x • (y : M) = 0 := y.2
      rw [hδ _ y 0 rfl (by rw [map_zero, hyx]), map_zero]
  have h₄ : Function.Exact δ (cokerSmulMap f x) := by
    intro w
    obtain ⟨m', rfl⟩ := Submodule.mkQ_surjective _ w
    constructor
    · intro hw
      have hw' : Submodule.mkQ (LinearMap.range (LinearMap.lsmul A M x)) (f m') = 0 := hw
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hw'
      obtain ⟨m, hm⟩ := LinearMap.mem_range.1 hw'
      have hm2 : x • m = f m' := hm
      refine ⟨⟨g m, ?_⟩, hδ _ m m' rfl hm2.symm⟩
      show x • g m = 0
      rw [← map_smul, hm2]
      exact (hex _).2 ⟨m', rfl⟩
    · rintro ⟨z, hz⟩
      obtain ⟨m, hm⟩ := hg z
      have hzx : x • (z : M'') = 0 := z.2
      obtain ⟨n', hn'⟩ := (hex (x • m)).1 (by rw [map_smul, hm, hzx])
      rw [← hz, hδ z m n' hm hn']
      show Submodule.mkQ (LinearMap.range (LinearMap.lsmul A M x)) (f n') = 0
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hn']
      exact ⟨m, rfl⟩
  have h₅ : Function.Exact (cokerSmulMap f x) (cokerSmulMap g x) := by
    intro w
    obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective _ w
    constructor
    · intro hw
      have hw' : Submodule.mkQ (LinearMap.range (LinearMap.lsmul A M'' x)) (g m) = 0 := hw
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hw'
      obtain ⟨m'', hm''⟩ := LinearMap.mem_range.1 hw'
      have hm2 : x • m'' = g m := hm''
      obtain ⟨t, ht⟩ := hg m''
      obtain ⟨m', hm'⟩ := (hex (m - x • t)).1 (by rw [map_sub, map_smul, ht, hm2, sub_self])
      refine ⟨Submodule.mkQ _ m', ?_⟩
      show Submodule.mkQ (LinearMap.range (LinearMap.lsmul A M x)) (f m') = Submodule.mkQ _ m
      rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, hm']
      refine ⟨-t, ?_⟩
      show x • -t = m - x • t - m
      rw [smul_neg]
      abel
    · rintro ⟨w', hw'⟩
      obtain ⟨m', rfl⟩ := Submodule.mkQ_surjective _ w'
      rw [← hw']
      show Submodule.mkQ (LinearMap.range (LinearMap.lsmul A M'' x)) (g (f m')) = 0
      rw [(hex _).2 ⟨m', rfl⟩, map_zero]
  have h₆ : Function.Surjective (cokerSmulMap g x) := by
    intro w
    obtain ⟨m'', rfl⟩ := Submodule.mkQ_surjective _ w
    obtain ⟨m, rfl⟩ := hg m''
    exact ⟨Submodule.mkQ _ m, rfl⟩
  exact length_six_term h₁ h₂ h₃ h₄ h₅ h₆

theorem euler_finLength {A : Type*} [CommRing A] {N : Type*} [AddCommGroup N] [Module A N]
    (hN : length A N ≠ ⊤) (x : A) :
    length A (N ⧸ LinearMap.range (LinearMap.lsmul A N x)) =
      length A (LinearMap.ker (LinearMap.lsmul A N x)) := by
  have h1 := length_eq_ker_add_range (LinearMap.lsmul A N x)
  have h2 := length_eq_sub_add_quot (LinearMap.range (LinearMap.lsmul A N x))
  have hle : length A (LinearMap.range (LinearMap.lsmul A N x)) ≤ length A N := by
    rw [h1]
    exact le_add_self
  have hR := ne_top_of_le_ne_top hN hle
  rw [h1, add_comm] at h2
  exact (WithTop.add_left_cancel hR h2).symm

end ReciprocityTheory.ChartRestriction.G.AI
end

section

namespace ReciprocityTheory.ChartRestriction.G.AI

universe u

theorem length_eq_of_surj_of_ker_eq {A C M N : Type*} [CommRing A] [AddCommGroup C] [Module A C]
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] (f : C →ₗ[A] M) (g : C →ₗ[A] N)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (h : LinearMap.ker f = LinearMap.ker g) : Module.length A M = Module.length A N := ((f.quotKerEquivOfSurjective hf).symm.trans ((Submodule.quotEquivOfEq _ _ h).trans
      (g.quotKerEquivOfSurjective hg))).length_eq

theorem mem_ker_lsmul_mk {A : Type u} [CommRing A] (a b x : A) :
    Ideal.Quotient.mk (Ideal.span {a}) x ∈
        LinearMap.ker (LinearMap.lsmul A (A ⧸ Ideal.span {a}) b) ↔ ∃ y, b * x = a * y := by
  rw [LinearMap.mem_ker, LinearMap.lsmul_apply, Algebra.smul_def, Ideal.Quotient.algebraMap_eq,
    ← map_mul, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  rfl

theorem length_ker_swap {A : Type u} [CommRing A] [IsDomain A] (a b : A) (ha : a ≠ 0) (hb : b ≠ 0) :
    Module.length A (LinearMap.ker (LinearMap.lsmul A (A ⧸ Ideal.span {a}) b)) =
      Module.length A (LinearMap.ker (LinearMap.lsmul A (A ⧸ Ideal.span {b}) a)) := by
  set S : Submodule A (A × A) :=
    LinearMap.ker (b • LinearMap.fst A A A - a • LinearMap.snd A A A) with hSdef
  have hS : ∀ p : A × A, p ∈ S ↔ b * p.1 = a * p.2 := by
    intro p
    rw [hSdef, LinearMap.mem_ker]
    simp [sub_eq_zero]
  have hf0 : ∀ p : S, (Ideal.span {a}).mkQ (p : A × A).1 ∈
      LinearMap.ker (LinearMap.lsmul A (A ⧸ Ideal.span {a}) b) := by
    intro p
    exact (mem_ker_lsmul_mk a b _).mpr ⟨_, (hS _).mp p.2⟩
  have hg0 : ∀ p : S, (Ideal.span {b}).mkQ (p : A × A).2 ∈
      LinearMap.ker (LinearMap.lsmul A (A ⧸ Ideal.span {b}) a) := by
    intro p
    exact (mem_ker_lsmul_mk b a _).mpr ⟨(p : A × A).1, ((hS _).mp p.2).symm⟩
  let f := LinearMap.codRestrict _
    ((Ideal.span {a}).mkQ ∘ₗ LinearMap.fst A A A ∘ₗ S.subtype) hf0
  let g := LinearMap.codRestrict _
    ((Ideal.span {b}).mkQ ∘ₗ LinearMap.snd A A A ∘ₗ S.subtype) hg0
  apply length_eq_of_surj_of_ker_eq f g
  · rintro ⟨k, hk⟩
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective k
    obtain ⟨y, hy⟩ := (mem_ker_lsmul_mk a b x).mp hk
    exact ⟨⟨(x, y), (hS _).mpr hy⟩, rfl⟩
  · rintro ⟨k, hk⟩
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective k
    obtain ⟨x, hx⟩ := (mem_ker_lsmul_mk b a y).mp hk
    exact ⟨⟨(x, y), (hS _).mpr hx.symm⟩, rfl⟩
  · ext ⟨⟨x, y⟩, hp⟩
    have hp' := (hS _).mp hp
    rw [LinearMap.mem_ker, LinearMap.mem_ker, ← Submodule.coe_eq_zero, ← Submodule.coe_eq_zero]
    show (Ideal.span {a}).mkQ x = 0 ↔ (Ideal.span {b}).mkQ y = 0
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
      Submodule.Quotient.mk_eq_zero, Ideal.mem_span_singleton, Ideal.mem_span_singleton]
    simp only at hp'
    constructor
    · rintro ⟨z, rfl⟩
      refine ⟨z, ?_⟩
      apply mul_left_cancel₀ ha
      rw [← hp']
      ring
    · rintro ⟨w, rfl⟩
      refine ⟨w, ?_⟩
      apply mul_left_cancel₀ hb
      rw [hp']
      ring

theorem length_ne_top_of_killed {A N : Type*} [CommRing A] [AddCommGroup N] [Module A N]
    [Module.Finite A N] (I : Ideal A) (hI : ∀ r ∈ I, ∀ x : N, r • x = 0)
    (hfin : Module.length A (A ⧸ I) ≠ ⊤) : Module.length A N ≠ ⊤ := by
  rw [Module.length_ne_top_iff, isFiniteLength_iff_isNoetherian_isArtinian] at hfin ⊢
  obtain ⟨hN, hA⟩ := hfin
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := A) (M := N)
  let φ : Fin n → (A ⧸ I) →ₗ[A] N := fun i =>
    Submodule.liftQ I (LinearMap.toSpanSingleton A N (s i)) (by
      intro r hr
      rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]
      exact hI r hr (s i))
  let Φ : (Fin n → A ⧸ I) →ₗ[A] N := ∑ i, (φ i).comp (LinearMap.proj i)
  have hΦ : Function.Surjective Φ := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hs, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    refine ⟨Pi.single i (Submodule.Quotient.mk 1), ?_⟩
    simp only [Φ, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]
    rw [Finset.sum_eq_single i]
    · rw [Pi.single_eq_same]
      simp only [φ, Submodule.liftQ_apply, LinearMap.toSpanSingleton_apply, one_smul]
    · intro j _ hj
      simp [Pi.single_eq_of_ne hj]
    · simp
  exact ⟨isNoetherian_of_surjective Φ (LinearMap.range_eq_top.mpr hΦ),
    isArtinian_of_surjective _ Φ hΦ⟩

theorem length_ker_ne_top {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A] (a b : A)
    (ha : a ≠ 0) (hb : b ≠ 0) (hfin : Module.length A (A ⧸ Ideal.span {a, b}) ≠ ⊤) :
    Module.length A (LinearMap.ker (LinearMap.lsmul A (A ⧸ Ideal.span {a}) b)) ≠ ⊤ := by
  apply length_ne_top_of_killed (Ideal.span {a, b}) _ hfin
  rintro r hr ⟨k, hk⟩
  apply Subtype.ext
  simp only [Submodule.coe_smul, Submodule.coe_zero]
  obtain ⟨u, v, rfl⟩ := Ideal.mem_span_pair.mp hr
  have hbk : b • k = 0 := by simpa using hk
  have hak : a • k = 0 := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective k
    rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self a)
  rw [add_smul, mul_smul, mul_smul, hak, hbk, smul_zero, smul_zero, add_zero]

end ReciprocityTheory.ChartRestriction.G.AI
end
