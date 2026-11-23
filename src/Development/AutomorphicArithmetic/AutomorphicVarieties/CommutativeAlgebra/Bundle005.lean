module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Mathlib.Basic.Real.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal

@[expose] public section

section

noncomputable section

open IsLocalRing MvPowerSeries

namespace UpperTheory.V.Alg

structure IsNVal (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    (v : K → ℝ) : Prop where
  mul : ∀ x y, x ≠ 0 → y ≠ 0 → v (x * y) = v x + v y
  add : ∀ x y, x ≠ 0 → y ≠ 0 → x + y ≠ 0 → min (v x) (v y) ≤ v (x + y)
  base : ∀ c : O, c ≠ 0 → v (algebraMap O K c) = ((IsDiscreteValuationRing.addVal O c).toNat : ℝ)

abbrev tz {K : Type} [CommRing K] (t : Kˣ) : Multiplicative ℤ →* Kˣ := zpowersHom Kˣ t

section Data

variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜]

structure IsWRing [IsLocalRing O] (x : A →ₐ[O] O) : Prop where
  co : IsCO O (𝒜 0)
  gen : ∃ s : Finset A, (∀ z ∈ s, z ∈ 𝒜 (-2) ∨ z ∈ 𝒜 (-1) ∨ z ∈ 𝒜 1 ∨ z ∈ 𝒜 2) ∧
    Algebra.adjoin O ((𝒜 0 : Set A) ∪ s) = ⊤
  fixed : ∀ j, j ≠ 0 → ∀ f ∈ 𝒜 j, x f = 0

variable {K : Type} [Field K] [Algebra O K]

def OnS (I : Ideal A) (ξ : A →ₐ[O] K) : Prop := ∀ f ∈ I, ξ f = 0

def NegZero (ξ : A →ₐ[O] K) : Prop := ∀ j < 0, ∀ f ∈ 𝒜 j, ξ f = 0

def PosZero (ξ : A →ₐ[O] K) : Prop := ∀ j > 0, ∀ f ∈ 𝒜 j, ξ f = 0

def TwoSigned (ξ : A →ₐ[O] K) : Prop := ¬ NegZero 𝒜 ξ ∧ ¬ PosZero 𝒜 ξ

def Same0 (ξ ξ' : A →ₐ[O] K) : Prop := ∀ b ∈ 𝒜 0, ξ b = ξ' b

def SameOrbit (ξ ξ' : A →ₐ[O] K) : Prop := ∃ t : Kˣ, ξ' = act 𝒜 (tz t) ξ

def M2 (I : Ideal A) : Prop := ((𝒜 0).map (Ideal.Quotient.mkₐ O I).toLinearMap).FG


variable (K)

def M3 (x : A →ₐ[O] O) (I : Ideal A) : Prop :=
  ∀ x₁ : A →ₐ[O] K, OnS I x₁ → NegZero 𝒜 x₁ → PosZero 𝒜 x₁ → x₁ ≠ (Algebra.ofId O K).comp x →
    (¬ ∃ ξ : A →ₐ[O] K, OnS I ξ ∧ NegZero 𝒜 ξ ∧ ¬ PosZero 𝒜 ξ ∧ Same0 𝒜 ξ x₁) ∨
    (¬ ∃ ξ : A →ₐ[O] K, OnS I ξ ∧ PosZero 𝒜 ξ ∧ ¬ NegZero 𝒜 ξ ∧ Same0 𝒜 ξ x₁)


def M4 (I : Ideal A) : Prop :=
  ∀ ξ : A →ₐ[O] K, OnS I ξ → TwoSigned 𝒜 ξ → ∀ D ∈ PtDer ξ K, ∀ D' ∈ PtDer ξ K, (∀ f ∈ I, D f = 0) →
    (∀ f ∈ I, D' f = 0) → ∃ c c' : K, (c ≠ 0 ∨ c' ≠ 0) ∧ c • D + c' • D' = 0



def M5 (x : A →ₐ[O] O) (I : Ideal A) (a : A) : Prop :=
  a ∈ 𝒜 0 ∧ x a = 0 ∧ ∀ ξ : A →ₐ[O] K, OnS I ξ → TwoSigned 𝒜 ξ → ξ a ≠ 0

variable {K}

def Covers (I : Ideal A) (T : Finset (A →ₐ[O] K)) : Prop :=
  (∀ ξ ∈ T, OnS I ξ ∧ TwoSigned 𝒜 ξ) ∧ ∀ ξ, OnS I ξ → TwoSigned 𝒜 ξ → ∃ ξ' ∈ T, SameOrbit 𝒜 ξ' ξ

end Data

structure IsChart {O A X τ : Type} [CommRing O] [IsDomain O] [CommRing A] [Algebra O A] [AddCommGroup X]
    (𝒜 : X → Submodule O A) (x : A →ₐ[O] O) (wt : τ → X) (φ : A →ₐ[O] MvPowerSeries τ (FractionRing O)) : Prop where
  graded : ∀ j, ∀ f ∈ 𝒜 j, φ f ∈ wtPart (FractionRing O) wt j
  const : ∀ f, constantCoeff (φ f) = algebraMap O (FractionRing O) (x f)
  onto : ∀ i, ∃ f : A, coeff (Finsupp.single i 1) (φ f) ≠ 0 ∧ ∀ i', i' ≠ i → coeff (Finsupp.single i' 1) (φ f) = 0
  inj : ∀ f, x f = 0 → (∀ i, coeff (Finsupp.single i 1) (φ f) = 0) → f ∈ satSq x

def SmoothPt {O A X : Type} [CommRing O] [IsDomain O] [CommRing A] [Algebra O A] [AddCommGroup X]
    (𝒜 : X → Submodule O A) (x : A →ₐ[O] O) (n : X → ℕ) : Prop :=
  ∃ (τ : Type) (_ : Fintype τ) (wt : τ → X) (φ : A →ₐ[O] MvPowerSeries τ (FractionRing O)),
    IsChart 𝒜 x wt φ ∧ ∀ j, Nat.card {i // wt i = j} = n j

structure Eqns {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) (x : A →ₐ[O] O)
    (r s r' s' m : ℕ) where
  F : Fin (r + 1) → A
  G : Fin s → A
  E : Fin r' → A
  E' : Fin s' → A
  Z : Fin m → A
  hF : ∀ i, F i ∈ 𝒜 (-1)
  hG : ∀ i, G i ∈ 𝒜 (-2)
  hE : ∀ i, E i ∈ 𝒜 1
  hE' : ∀ i, E' i ∈ 𝒜 2
  hZ : ∀ i, Z i ∈ 𝒜 0 ∧ x (Z i) = 0

def Eqns.ideal {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {𝒜 : ℤ → Submodule O A} {x : A →ₐ[O] O}
    {r s r' s' m : ℕ} (Q : Eqns 𝒜 x r s r' s' m) : Ideal A :=
  Ideal.span (Set.range Q.F ∪ Set.range Q.G ∪ Set.range Q.E ∪ Set.range Q.E' ∪ Set.range Q.Z)

def mDims (r s r' s' m : ℕ) (j : ℤ) : ℕ :=
  if j = -1 then r else if j = -2 then s else if j = 1 then r' + 1 else if j = 2 then s' + 1 else
    if j = 0 then m else 0

def M1 {O A : Type} [CommRing O] [IsDomain O] [CommRing A] [Algebra O A] {𝒜 : ℤ → Submodule O A} {x : A →ₐ[O] O}
    {r s r' s' m : ℕ} (Q : Eqns 𝒜 x r s r' s' m) : Prop :=
  1 ≤ r ∧ SmoothPt 𝒜 x (mDims r s r' s' m) ∧ SpansCot x 𝒜 (-1) Q.F ∧ SpansCot x 𝒜 (-2) Q.G ∧ SpansCot x 𝒜 0 Q.Z

def LemmaM : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O]
    (K : Type) [Field K] [Algebra O K] [IsAlgClosed K] [FaithfulSMul O K] (v : K → ℝ), IsNVal O K v →
  ∀ (A : Type) [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] (x : A →ₐ[O] O), IsWRing 𝒜 x →
  ∀ (r s r' s' m : ℕ) (Q : Eqns 𝒜 x r s r' s' m) (a : A),
    M1 Q → M2 𝒜 Q.ideal → M3 𝒜 K x Q.ideal → M4 𝒜 K Q.ideal → M5 𝒜 K x Q.ideal a →
    (∃ T : Finset (A →ₐ[O] K), Covers 𝒜 Q.ideal T) ∧ cotLen x 𝒜 (-1) Q.F ≠ ⊤ ∧
    ∀ T : Finset (A →ₐ[O] K), Covers 𝒜 Q.ideal T → ((cotLen x 𝒜 (-1) Q.F).toNat : ℝ) ≤ 2 * ∑ ξ ∈ T, v (ξ a)

def LemmaM' : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (ResidueField O)]
    (A X : Type) [CommRing A] [Algebra O A] [AddCommGroup X] [DecidableEq X] (𝒜 : X → Submodule O A) [GradedAlgebra 𝒜]
    (x : A →ₐ[O] O) (j : X), (∀ f ∈ 𝒜 j, x f = 0) →
  ∀ (ι : Type) (F : ι → A), (∀ i, F i ∈ 𝒜 j) →
  ∀ (c : O), c ≠ 0 → ∀ (M : Type) [AddCommGroup M] [Module O M] (D : M →+ (A →ₗ[O] O ⧸ Ideal.span {c})),
    Function.Injective D → (∀ μ i, D μ (F i) = 0) →
    (∀ μ, ∃ D' ∈ PtDer x O, HasWt 𝒜 j D' ∧ ∀ f, D μ f = Ideal.Quotient.mk _ (D' f)) →
    Module.length O M ≤ cotLen x 𝒜 j F

end UpperTheory.V.Alg
end
end

section

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private theorem UpperTheory.V.Alg.exists_form_of_not_torsion {O L : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [AddCommGroup L] [Module O L] [Module.Finite O L] (S : Submodule O L) (p : L)
    (hp : ∀ c : O, c ≠ 0 → c • p ∉ S) : ∃ φ : L →ₗ[O] O, (∀ s ∈ S, φ s = 0) ∧ φ p ≠ 0 := by
  have hne : (Submodule.torsion O (L ⧸ S)).mkQ (S.mkQ p) ≠ 0 := by
    intro h
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h
    obtain ⟨⟨c, hc⟩, hcp⟩ := h
    refine hp c (nonZeroDivisors.ne_zero hc) ?_
    rw [← Submodule.Quotient.mk_eq_zero]
    exact hcp
  obtain ⟨ψ, hψ⟩ := Module.Projective.exists_dual_ne_zero O hne
  refine ⟨ψ ∘ₗ (Submodule.torsion O (L ⧸ S)).mkQ ∘ₗ S.mkQ, fun s hs => ?_, hψ⟩
  have : S.mkQ s = 0 := (Submodule.Quotient.mk_eq_zero S).2 hs
  simp only [LinearMap.comp_apply, this, map_zero]

private theorem UpperTheory.V.Alg.ker_isHomogeneous {O A X : Type} [CommRing O] [CommRing A] [Algebra O A]
    [AddCommGroup X] [DecidableEq X] (𝒜 : X → Submodule O A) [GradedAlgebra 𝒜] (x : A →ₐ[O] O)
    (hx : ∀ i, i ≠ 0 → ∀ f ∈ 𝒜 i, x f = 0) : (RingHom.ker x).IsHomogeneous 𝒜 := by
  have h0 : ∀ f : A, x (DirectSum.decompose 𝒜 f 0 : A) = x f := by
    intro f
    induction f using DirectSum.Decomposition.inductionOn 𝒜 with
    | zero => simp
    | @homogeneous i m =>
      by_cases hi : i = 0
      · subst hi
        rw [DirectSum.decompose_of_mem_same 𝒜 m.2]
      · rw [DirectSum.decompose_of_mem_ne 𝒜 m.2 hi, map_zero, hx i hi m m.2]
    | add a b ha hb => simp [ha, hb]
  intro i f hf
  rw [RingHom.mem_ker] at hf ⊢
  by_cases hi : i = 0
  · subst hi
    rw [h0, hf]
  · exact hx i hi _ (DirectSum.decompose 𝒜 f i).2

theorem UpperTheory.V.Alg.spans_of_der :
    ∀ (O A X : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing A] [Algebra O A] [AddCommGroup X] [DecidableEq X] (𝒜 : X → Submodule O A) [GradedAlgebra 𝒜] (x : A →ₐ[O] O),
      (∀ i, i ≠ 0 → ∀ f ∈ 𝒜 i, x f = 0) → ∀ (j : X), (cotLat x 𝒜 j).FG → ∀ (ι : Type) (F : ι → A), (∀ i, F i ∈ 𝒜 j ∧ x (F i) = 0) →
      (∀ D ∈ PtDer x O, HasWt 𝒜 j D → (∀ i, D (F i) = 0) → D = 0) → SpansCot x 𝒜 j F := by
  intro O A X _ _ _ _ _ _ _ 𝒜 _ x hx j hfg ι F hF hD p hp
  by_contra hcon
  haveI : Module.Finite O (cotLat x 𝒜 j) := Module.Finite.iff_fg.2 hfg
  obtain ⟨φ, hφS, hφp⟩ := exists_form_of_not_torsion ((cotSpan x F).comap (cotLat x 𝒜 j).subtype) ⟨p, hp⟩
    (fun c hc h => hcon ⟨c, hc, h⟩)
  have hq := ker_isHomogeneous 𝒜 x hx
  have hq2 : (RingHom.ker x ^ 2).IsHomogeneous 𝒜 := by rw [pow_two]; exact hq.mul hq
  let r : A →ₗ[O] A := LinearMap.id - Algebra.linearMap O A ∘ₗ x.toLinearMap
  have hr : ∀ f, r f = f - algebraMap O A (x f) := fun f => rfl
  have hrq : ∀ f, r f ∈ RingHom.ker x := fun f => by
    rw [RingHom.mem_ker, hr, map_sub, AlgHom.commutes]; simp
  let T : A →ₗ[O] A ⧸ satSq x := (satSq x).mkQ ∘ₗ GradedAlgebra.proj 𝒜 j ∘ₗ r
  have hT : ∀ f, T f = (satSq x).mkQ (DirectSum.decompose 𝒜 (r f) j : A) := fun f => rfl
  have hTL : ∀ f, T f ∈ cotLat x 𝒜 j := fun f =>
    ⟨_, ⟨(DirectSum.decompose 𝒜 (r f) j).2, hq j (hrq f)⟩, (hT f).symm⟩
  have hTj : ∀ f ∈ 𝒜 j, x f = 0 → T f = (satSq x).mkQ f := fun f hf h0 => by
    rw [hT, hr, h0, map_zero, sub_zero, DirectSum.decompose_of_mem_same 𝒜 hf]
  have hTi : ∀ i, i ≠ j → ∀ f ∈ 𝒜 i, T f = 0 := fun i hi f hf => by
    have : r f ∈ 𝒜 i := by
      by_cases h0 : i = 0
      · subst h0
        rw [hr]
        exact sub_mem hf (SetLike.algebraMap_mem_graded 𝒜 _)
      · rw [hr, hx i h0 f hf, map_zero, sub_zero]; exact hf
    rw [hT, DirectSum.decompose_of_mem_ne 𝒜 this hi, map_zero]
  have hTm : ∀ f g, T (f * g) = x f • T g + x g • T f := fun f g => by
    have e : r (f * g) = r f * r g + (x f • r g + x g • r f) := by
      simp only [hr, Algebra.smul_def, map_mul]; ring
    have hz : (satSq x).mkQ (GradedAlgebra.proj 𝒜 j (r f * r g)) = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      refine ⟨1, one_ne_zero, ?_⟩
      rw [one_smul]
      refine hq2 j ?_
      rw [pow_two]
      exact Ideal.mul_mem_mul (hrq f) (hrq g)
    show (satSq x).mkQ (GradedAlgebra.proj 𝒜 j (r (f * g))) =
      x f • (satSq x).mkQ (GradedAlgebra.proj 𝒜 j (r g)) + x g • (satSq x).mkQ (GradedAlgebra.proj 𝒜 j (r f))
    rw [e]
    simp only [map_add (f := _), map_smul, hz, zero_add]
  let T' : A →ₗ[O] cotLat x 𝒜 j := T.codRestrict _ hTL
  have hD0 : φ ∘ₗ T' = 0 := by
    refine hD _ (fun f g => ?_) (fun i hi f hf => ?_) (fun i => ?_)
    · have : T' (f * g) = x f • T' g + x g • T' f := Subtype.ext (hTm f g)
      simp only [LinearMap.comp_apply, this, map_add (f := _), map_smul]
    · have : T' f = 0 := Subtype.ext (hTi i hi f hf)
      simp only [LinearMap.comp_apply, this, map_zero]
    · refine hφS _ ?_
      show T (F i) ∈ cotSpan x F
      rw [hTj _ (hF i).1 (hF i).2]
      exact Submodule.subset_span ⟨i, rfl⟩
  obtain ⟨a, ⟨ha1, ha2⟩, rfl⟩ := hp
  apply hφp
  have h1 : φ (T' a) = 0 := LinearMap.congr_fun hD0 a
  rw [← h1]
  congr 1
  exact Subtype.ext (hTj a ha1 ha2).symm
end
