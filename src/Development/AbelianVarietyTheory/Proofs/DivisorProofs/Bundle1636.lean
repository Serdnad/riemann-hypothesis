module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle112
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1580
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1212
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1289
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1586
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1298
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1587
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1460
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle369
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1602
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1512
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1589
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle040
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle710
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle012
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import GroundTheory.AutomorphicForms.LocallyProfinite
import GroundTheory.AutomorphicForms.Bundle003
import GroundTheory.GlobalFields.KummerTheory.LocalIndex

@[expose] public section

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.ConjInt

section Coords

variable (v : HeightOneSpectrum ℤ) {M : Type} [AddCommGroup M] [Module ℚ M] {κ : Type} (b : Module.Basis κ ℚ M)

theorem isIntB_add {x y : v.adicCompletion ℚ ⊗[ℚ] M} (hx : IsIntB v b x) (hy : IsIntB v b y) :
    IsIntB v b (x + y) := fun i => by
  rw [map_add (f := _), Finsupp.add_apply]; exact add_mem (hx i) (hy i)

theorem isIntB_smul {a : v.adicCompletion ℚ} (ha : a ∈ v.adicCompletionIntegers ℚ)
    {x : v.adicCompletion ℚ ⊗[ℚ] M} (hx : IsIntB v b x) : IsIntB v b (a • x) := fun i => by
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul]; exact mul_mem ha (hx i)

theorem isIntB_sum {ι : Type} (s : Finset ι) (f : ι → v.adicCompletion ℚ ⊗[ℚ] M)
    (h : ∀ i ∈ s, IsIntB v b (f i)) : IsIntB v b (∑ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => simpa using isIntB_zero v b
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact isIntB_add v b (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem isIntB_tmul_iff (c : M) : IsIntB v b ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] c) ↔
    ∀ i, algebraMap ℚ (v.adicCompletion ℚ) (b.repr c i) ∈ v.adicCompletionIntegers ℚ := by
  unfold IsIntB
  simp only [Algebra.TensorProduct.basis_repr_tmul, one_smul, Finsupp.mapRange_apply]

theorem eventually_isIntB_tmul [Finite κ] (c : M) :
    ∀ᶠ v : HeightOneSpectrum ℤ in Filter.cofinite, IsIntB v b ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] c) := by
  have h : ∀ᶠ v : HeightOneSpectrum ℤ in Filter.cofinite, ∀ i,
      algebraMap ℚ (v.adicCompletion ℚ) (b.repr c i) ∈ v.adicCompletionIntegers ℚ :=
    Filter.eventually_all.2 fun i => (algebraMap ℚ (FiniteAdeleRing ℤ ℚ) (b.repr c i)).2
  exact h.mono fun v hv => (isIntB_tmul_iff v b c).2 hv

theorem eq_sum_basis [Fintype κ] (x : v.adicCompletion ℚ ⊗[ℚ] M) :
    x = ∑ i, (Algebra.TensorProduct.basis (v.adicCompletion ℚ) b).repr x i •
      ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] b i) := by
  conv_lhs => rw [← (Algebra.TensorProduct.basis (v.adicCompletion ℚ) b).sum_repr x]
  simp only [Algebra.TensorProduct.basis_apply]

end Coords

section Alg

variable (v : HeightOneSpectrum ℤ) {A : Type} [Ring A] [Algebra ℚ A] {κ : Type} (b : Module.Basis κ ℚ A)

theorem isIntB_mul [Finite κ] (hb : ∀ i j, IsIntB v b ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] (b i * b j)))
    {x y : v.adicCompletion ℚ ⊗[ℚ] A} (hx : IsIntB v b x) (hy : IsIntB v b y) : IsIntB v b (x * y) := by
  haveI := Fintype.ofFinite κ
  rw [eq_sum_basis v b x, eq_sum_basis v b y, Finset.sum_mul]
  refine isIntB_sum v b _ _ fun i _ => ?_
  rw [Finset.mul_sum]
  refine isIntB_sum v b _ _ fun j _ => ?_
  rw [smul_mul_smul_comm, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  exact isIntB_smul v b (mul_mem (hx i) (hy j)) (hb i j)

theorem isIntB_pow [Finite κ] (hb : ∀ i j, IsIntB v b ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] (b i * b j)))
    (h1 : IsIntB v b ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] (1 : A)))
    {x : v.adicCompletion ℚ ⊗[ℚ] A} (hx : IsIntB v b x) (k : ℕ) : IsIntB v b (x ^ k) := by
  induction k with
  | zero => rw [pow_zero]; exact h1
  | succ k ih => rw [pow_succ]; exact isIntB_mul v b hb ih hx

theorem tmul_central_comm {R : Type} [CommRing R] [Algebra ℚ R] (z : A) (hz : ∀ c, z * c = c * z)
    (y : R ⊗[ℚ] A) : ((1 : R) ⊗ₜ[ℚ] z) * y = y * ((1 : R) ⊗ₜ[ℚ] z) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a c => simp [Algebra.TensorProduct.tmul_mul_tmul, hz c]
  | add x y hx hy => rw [mul_add, add_mul, hx, hy]

end Alg

end GlobalTheory.ConjInt

namespace GlobalTheory.ConjInt

variable {p : ℕ} [Fact p.Prime]

theorem mem_adjoin_of_centralizer (G : HTGroup p) (γ : G.C) (hdeg : (minpoly G.F γ).natDegree = G.n)
    (L : Type) [Field L] (ι : L →+* G.C) (hι : Function.Injective ι)
    (hc : ∀ z : G.C, z * γ = γ * z ↔ ∃ w, ι w = z) (w : L) :
    ι w ∈ Algebra.adjoin G.F ({γ} : Set G.C) := by
  set B := Algebra.adjoin G.F ({γ} : Set G.C) with hB
  have hBc : B ≤ Subalgebra.centralizer G.F ({γ} : Set G.C) := by
    refine Algebra.adjoin_le ?_
    rw [Set.singleton_subset_iff, SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
    intro g hg; rw [Set.mem_singleton_iff] at hg; rw [hg]
  have hof : ∀ x : B, ∃ w, ι w = (x : G.C) := by
    intro x
    have hx := hBc x.2
    rw [Subalgebra.mem_centralizer_iff] at hx
    exact (hc x).1 (hx γ (Set.mem_singleton γ)).symm
  haveI : NoZeroDivisors B := by
    refine ⟨fun {x y} hxy => ?_⟩
    obtain ⟨wx, hwx⟩ := hof x
    obtain ⟨wy, hwy⟩ := hof y
    have h0 : ι (wx * wy) = 0 := by
      rw [map_mul, hwx, hwy]; exact congrArg Subtype.val hxy
    rcases mul_eq_zero.1 (hι (h0.trans (map_zero ι).symm)) with h | h
    · left; apply Subtype.ext; rw [← hwx, h, map_zero]; rfl
    · right; apply Subtype.ext; rw [← hwy, h, map_zero]; rfl
  haveI : IsDomain B := NoZeroDivisors.to_isDomain B
  have hγB : γ ∈ B := Algebra.self_mem_adjoin_singleton G.F γ
  have hint : IsIntegral G.F (⟨γ, hγB⟩ : B) := Algebra.IsIntegral.isIntegral _
  have hirr : Irreducible (minpoly G.F γ) := by
    have e := minpoly.algHom_eq B.val Subtype.val_injective ⟨γ, hγB⟩
    rw [show B.val ⟨γ, hγB⟩ = γ from rfl] at e
    rw [e]; exact minpoly.irreducible hint
  have hcom : Commute (ι w) γ := (hc (ι w)).2 ⟨w, rfl⟩
  exact (GlobalTheory.CentIrr.commute_iff_mem_adjoin G.F G.C G.n G.n_pos G.rankC γ hirr hdeg (ι w)).1 hcom

end GlobalTheory.ConjInt

namespace GlobalTheory.ConjInt

variable {p : ℕ} [Fact p.Prime]

theorem conj_tmul_smul_pow (G : HTGroup p) (R : Type) [CommRing R] [Algebra ℚ R] (X : (R ⊗[ℚ] G.C)ˣ)
    (c : G.F) (γ : G.C) (k : ℕ) :
    (X : R ⊗[ℚ] G.C) * ((1 : R) ⊗ₜ[ℚ] (c • γ ^ k)) * ↑X⁻¹ =
      ((1 : R) ⊗ₜ[ℚ] algebraMap G.F G.C c) * (↑X * ((1 : R) ⊗ₜ[ℚ] γ) * ↑X⁻¹) ^ k := by
  have hz : ∀ y : G.C, algebraMap G.F G.C c * y = y * algebraMap G.F G.C c := fun y => Algebra.commutes c y
  rw [Units.conj_pow, Algebra.smul_def, ← one_mul (1 : R), ← Algebra.TensorProduct.tmul_mul_tmul, one_mul,
    Algebra.TensorProduct.tmul_pow, one_pow, ← mul_assoc, ← mul_assoc,
    ← tmul_central_comm _ hz (X : R ⊗[ℚ] G.C)]
  simp only [mul_assoc]

theorem isIntB_conj_map_of_isIntB_conj : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (γ : G.Cˣ), (minpoly G.F (γ : G.C)).natDegree = G.n →
    ∀ (L : Type) [Field L] [NumberField L] (ι : L →ₐ[ℚ] G.C), Function.Injective ι →
    (∀ z : G.C, z * γ = γ * z ↔ ∃ w, ι w = z) → ∀ (κ : Type) (b : Module.Basis κ ℚ G.C)
    (κ' : Type) (ℓ : Module.Basis κ' ℚ L),
    ∃ S : Finset (HeightOneSpectrum ℤ), ∀ v ∉ S, ∀ X : (v.adicCompletion ℚ ⊗[ℚ] G.C)ˣ,
      IsIntB v b (↑X * ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] (γ : G.C)) * ↑X⁻¹) →
      ∀ ρ, IsIntB v ℓ ρ →
        IsIntB v b (↑X * Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) ι ρ * ↑X⁻¹) := by
  intro p _ G γ hdeg L _ _ ι hι hc κ b κ' ℓ
  haveI : Finite κ := Module.Finite.finite_basis b
  haveI : Finite κ' := Module.Finite.finite_basis ℓ
  haveI := Fintype.ofFinite κ'
  have hq : ∀ a, ∃ q : Polynomial G.F, Polynomial.aeval (γ : G.C) q = ι (ℓ a) := by
    intro a
    have h := mem_adjoin_of_centralizer G (γ : G.C) hdeg L ι.toRingHom hι hc (ℓ a)
    rw [Algebra.adjoin_singleton_eq_range_aeval] at h
    exact h
  choose q hq using hq
  have hev : ∀ᶠ v : HeightOneSpectrum ℤ in Filter.cofinite,
      (∀ i j, IsIntB v b ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] (b i * b j))) ∧
      IsIntB v b ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] (1 : G.C)) ∧
      ∀ a, ∀ k ∈ Finset.range ((q a).natDegree + 1),
        IsIntB v b ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] algebraMap G.F G.C ((q a).coeff k)) :=
    (Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => eventually_isIntB_tmul b _).and
      ((eventually_isIntB_tmul b _).and
        (Filter.eventually_all.2 fun a => (Filter.eventually_all_finset _).2 fun k _ =>
          eventually_isIntB_tmul b _))
  refine ⟨(Filter.eventually_cofinite.1 hev).toFinset, fun v hv X hX ρ hρ => ?_⟩
  have hP := hv
  simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at hP
  obtain ⟨hb, h1, hcoef⟩ := hP
  set ιv := Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) ι
  have hmap : ∀ (r : v.adicCompletion ℚ) (m : L),
      ιv (r • ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] m)) = r • ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] ι m) := by
    intro r m
    rw [TensorProduct.smul_tmul', Algebra.TensorProduct.map_tmul, TensorProduct.smul_tmul']
    rfl
  have hterm : ∀ a, IsIntB v b (↑X * ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] ι (ℓ a)) * ↑X⁻¹) := by
    intro a
    rw [← hq a, Polynomial.aeval_eq_sum_range, TensorProduct.tmul_sum, Finset.mul_sum, Finset.sum_mul]
    refine isIntB_sum v b _ _ fun k hk => ?_
    rw [conj_tmul_smul_pow]
    exact isIntB_mul v b hb (hcoef a k hk) (isIntB_pow v b hb h1 hX k)

  rw [eq_sum_basis v ℓ ρ, map_sum, Finset.mul_sum, Finset.sum_mul]
  refine isIntB_sum v b _ _ fun a _ => ?_
  rw [hmap, mul_smul_comm, smul_mul_assoc]
  exact isIntB_smul v b (hρ a) (hterm a)

end GlobalTheory.ConjInt
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

noncomputable section
namespace GlobalTheory.MBLow.Cl

section Analytic

variable {B : NumB ℂ} {g : ℕ} (d : AB B g)

theorem ex_zero' : d.ex 0 = 1 := by
  have h := d.ex_add 0 0
  rw [add_zero] at h
  exact mul_eq_left.1 h.symm

theorem autV_cube (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (M N : Fin g → ℤ) (x y z : Fin g → ℂ) :
    autV τ a b M N (x + y + z) * autV τ a b M N z = autV τ a b M N (x + z) * autV τ a b M N (y + z) := by
  simp only [autV, ← Complex.exp_add]
  congr 1
  simp only [dotProduct_add]
  ring

theorem autV_ne (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (M N : Fin g → ℤ) (w : Fin g → ℂ) :
    autV τ a b M N w ≠ 0 := Complex.exp_ne_zero _

theorem fr_shift (M N : Fin g → ℤ) (w : Fin g → ℂ) :
    (d.fr (w + perV d.τ M N) : ℂ) = d.fr w / autV d.τ d.a d.b M N w := by
  rw [d.fr_per M N w, mul_div_cancel_left₀ _ (autV_ne _ _ _ _ _ _)]

theorem cubF_per (x y : Fin g → ℂ) (M N : Fin g → ℤ) (z : Fin g → ℂ) :
    cubF d x y (z + perV d.τ M N) = cubF d x y z := by
  have hP : d.ex (perV d.τ M N) = 1 := (d.ker _).2 ⟨M, N, rfl⟩
  have e1 : x + (z + perV d.τ M N) = x + z + perV d.τ M N := by abel
  have e2 : y + (z + perV d.τ M N) = y + z + perV d.τ M N := by abel
  have e3 : x + y + (z + perV d.τ M N) = x + y + z + perV d.τ M N := by abel
  unfold cubF
  rw [d.ex_add, hP, _root_.mul_one, e1, e2, e3, fr_shift, fr_shift, fr_shift, fr_shift]
  have A := autV_cube d.τ d.a d.b M N x y z
  have h1 := autV_ne d.τ d.a d.b M N (x + z)
  have h2 := autV_ne d.τ d.a d.b M N (y + z)
  have h3 := autV_ne d.τ d.a d.b M N (x + y + z)
  have h4 := autV_ne d.τ d.a d.b M N z
  have u1 := (d.fr (x + y + z)).ne_zero
  have u2 := (d.fr x).ne_zero
  have u3 := (d.fr y).ne_zero
  have u4 := (d.fr z).ne_zero
  field_simp
  linear_combination A

end Analytic

section Bound

variable {B : NumB ℂ} {g : ℕ}

def rv (s : Fin g → ℝ) : Fin g → ℂ := fun i => (s i : ℂ)

theorem exists_real_coords (τ : Matrix (Fin g) (Fin g) ℂ) (hpos : (τ.map Complex.im).PosDef) (z : Fin g → ℂ) :
    ∃ s t : Fin g → ℝ, z = rv s + τ *ᵥ rv t := by
  have hT : IsUnit (τ.map Complex.im).det := isUnit_iff_ne_zero.2 hpos.det_pos.ne'
  set t : Fin g → ℝ := (τ.map Complex.im)⁻¹ *ᵥ (fun i => (z i).im) with ht
  refine ⟨(fun i => (z i).re) - (τ.map Complex.re) *ᵥ t, t, ?_⟩
  have hIm : (τ.map Complex.im) *ᵥ t = fun i => (z i).im := by
    rw [ht, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hT, Matrix.one_mulVec]
  funext i
  have hi := congrFun hIm i
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply] at hi
  apply Complex.ext
  · simp [rv, Matrix.mulVec, dotProduct, Complex.re_sum]
  · simp [rv, Matrix.mulVec, dotProduct, Complex.im_sum, hi]

theorem exists_reduce (d : AB B g) (z : Fin g → ℂ) : ∃ (M N : Fin g → ℤ) (s t : Fin g → ℝ),
    (∀ i, s i ∈ Set.Icc (0 : ℝ) 1) ∧ (∀ i, t i ∈ Set.Icc (0 : ℝ) 1) ∧ z = rv s + d.τ *ᵥ rv t + perV d.τ M N := by
  obtain ⟨s, t, rfl⟩ := exists_real_coords d.τ d.pos z
  refine ⟨fun i => ⌊s i⌋, fun i => ⌊t i⌋, fun i => Int.fract (s i), fun i => Int.fract (t i),
    fun i => ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩, fun i => ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩, ?_⟩
  have hs : rv s = rv (fun i => Int.fract (s i)) + cv (fun i => ⌊s i⌋) := by
    funext i; simp only [rv, cv, Pi.add_apply, Int.fract]; push_cast; ring
  have ht : rv t = rv (fun i => Int.fract (t i)) + cv (fun i => ⌊t i⌋) := by
    funext i; simp only [rv, cv, Pi.add_apply, Int.fract]; push_cast; ring
  rw [hs, ht, perV, Matrix.mulVec_add]
  abel

theorem bounded_of_per (d : AB B g) (F : (Fin g → ℂ) → ℂ) (hc : Continuous F)
    (hper : ∀ M N z, F (z + perV d.τ M N) = F z) : Bornology.IsBounded (Set.range F) := by
  have hrv : Continuous (fun s : Fin g → ℝ => rv s) :=
    continuous_pi fun i => Complex.continuous_ofReal.comp (continuous_apply i)
  have hΦ : Continuous (fun p : (Fin g → ℝ) × (Fin g → ℝ) => rv p.1 + d.τ *ᵥ rv p.2) :=
    (hrv.comp continuous_fst).add (continuous_const.matrix_mulVec (hrv.comp continuous_snd))
  have hK : IsCompact ((Set.univ.pi fun _ : Fin g => Set.Icc (0 : ℝ) 1) ×ˢ (Set.univ.pi fun _ : Fin g => Set.Icc (0 : ℝ) 1)) :=
    (isCompact_univ_pi fun _ => isCompact_Icc).prod (isCompact_univ_pi fun _ => isCompact_Icc)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hc.comp hΦ).continuousOn
  refine isBounded_iff_forall_norm_le.2 ⟨C, ?_⟩
  rintro _ ⟨z, rfl⟩
  obtain ⟨M, N, s, t, hs, ht, rfl⟩ := exists_reduce d z
  rw [hper]
  exact hC (s, t) ⟨fun i _ => hs i, fun i _ => ht i⟩

theorem cub_of_diff (d : AB B g) (h : ∀ x y : Fin g → ℂ, Differentiable ℂ (cubF d x y)) : d.Cub := by
  intro x y z
  have hb := bounded_of_per d _ (h x y).continuous (cubF_per d x y)
  have e := (h x y).apply_eq_apply_of_bounded hb z 0
  have u1 := (d.fr (x + y + z)).ne_zero
  have u2 := (d.fr x).ne_zero
  have u3 := (d.fr y).ne_zero
  have u4 := (d.fr z).ne_zero
  have u5 := (d.fr (x + y)).ne_zero
  have h0 : cubF d x y 0 = 1 := by
    unfold cubF
    rw [ex_zero', B.cub.face₃, add_zero, add_zero, add_zero, d.fr_zero]
    simp only [Units.val_one, _root_.one_mul, _root_.mul_one]
    field_simp
  rw [h0] at e
  unfold cubF at e
  rw [div_eq_one_iff_eq (by simp [u1, u2, u3, u4])] at e
  apply Units.ext
  simpa only [Units.val_mul] using e

end Bound

theorem cub_of_geo : AllC fun {R} _ _ {D} _ {N} ν => ∀ (g : ℕ) (d : AB N.toNumB g), Nonempty (Geo ν d) → d.Cub := by
  intro R _ _ _ _ D hψ hτ _ N ν g d hG
  exact cub_of_diff d (GlobalTheory.T.cubeValueTimesThetaFrames_entire R D hψ hτ N ν g d hG)

end GlobalTheory.MBLow.Cl
end
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.DoublingEv

theorem _root_.GlobalTheory.T.tame_part_left : ∀ (F : Type) [Field F] [NumberField F] (κ κ₁ κ' : Type) [Fintype κ] [Fintype κ₁] [Fintype κ']
    (T : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ₁ → AF F) → ℂ)), IsTame F T → IsTame F (partL (κ' := κ') T) := by
  first | exact @GlobalTheory.DoublingEv.PartLTame.isTame_partL | exact GlobalTheory.DoublingEv.PartLTame.isTame_partL | (intros; apply GlobalTheory.DoublingEv.PartLTame.isTame_partL <;> assumption)
end

section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

theorem _root_.GlobalTheory.T.exists_smoothing_norm_le_height_pow : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ν : Measure (Lie E a)) [ν.IsAddHaarMeasure] (α : Lie E a → ℂ), IsTest (invSet E a) α → ∀ (f : GA E a → ℂ) (C : ℝ) (N : ℕ), (∀ y, ‖f (infGL E a y)‖ ≤ C * height y ^ N) → ∃ C' : ℝ, ∀ y, ‖smoothing ν α f (infGL E a y)‖ ≤ C' * height y ^ N := by
  first | exact @GlobalTheory.AutGrowth.smoothing_growth_exponent | exact GlobalTheory.AutGrowth.smoothing_growth_exponent | (intros; apply GlobalTheory.AutGrowth.smoothing_growth_exponent <;> assumption)
end

section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

theorem _root_.GlobalTheory.T.exists_test_word_eq_smoothing : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ν : Measure (Lie E a)) [ν.IsAddHaarMeasure] (α : Lie E a → ℂ), IsTest (invSet E a) α → ∀ φ : Sm E a, smoothing ν α φ.1 = φ.1 → ∀ l : List (Lie E a), ∃ β : Lie E a → ℂ, IsTest (invSet E a) β ∧ ((l.map (lie E a)).prod φ).1 = smoothing ν β φ.1 := by
  first | exact @GlobalTheory.AutGrowth.word_eq_smoothing_of_reproduced | exact GlobalTheory.AutGrowth.word_eq_smoothing_of_reproduced | (intros; apply GlobalTheory.AutGrowth.word_eq_smoothing_of_reproduced <;> assumption)
end

section

open scoped TensorProduct Matrix ComplexConjugate
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section
namespace GlobalTheory.DblHeis
open Formalism.IndefR.DatumF GlobalTheory.DblTargetDelta GlobalTheory.WeilSchrodinger.DblTargetF

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sum_fin_add_add {M : Type} [AddCommMonoid M] {n : ℕ} (f : Fin (n + n) → M) :
    ∑ d, f d = ∑ d, f (finSumFinEquiv (Sum.inl d)) + ∑ d, f (finSumFinEquiv (Sum.inr d)) := by
  rw [← Equiv.sum_comp finSumFinEquiv, Fintype.sum_sum_type]

theorem hOF_dblG (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E)
    (x y : WOF F E nS (nT + nT)) :
    hOF σ JS (dblG JT) x y = hOF σ JS JT (topR x) (topR y) - hOF σ JS JT (botR x) (botR y) := by
  simp only [hOF, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [sum_fin_add_add (n := nT), dblG, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, dbl,
    Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
    Matrix.zero_apply, Matrix.neg_apply, map_zero, map_neg, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, zero_add,
    mul_neg, neg_mul, Finset.sum_neg_distrib, ← sub_eq_add_neg, topR, botR, Function.comp_apply, id, Finset.sum_sub_distrib]
  ring

theorem hOF_neg_neg (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E)
    (x y : WOF F E nS nT) : hOF σ JS JT (-x) (-y) = hOF σ JS JT x y := by
  simp only [hOF, Matrix.neg_apply, map_neg, mul_neg, neg_mul, neg_neg]

theorem symplOHF_dblG (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E)
    (ξ₀ : E) (x y : WOF F E nS (nT + nT)) :
    symplOHF σ JS (dblG JT) ξ₀ x y =
      symplOHF σ JS JT ξ₀ (topR x) (topR y) - symplOHF σ JS JT ξ₀ (-botR x) (-botR y) := by
  simp only [symplOHF, symplOF, hOF_dblG, hOF_neg_neg, mul_sub, map_sub]

theorem conj_psi {ψ : AddChar (AF F) ℂ} (h : ∀ x, ‖ψ x‖ = 1) (s : AF F) : conj (ψ s) = ψ (-s) := by
  rw [AddChar.map_neg_eq_inv, Complex.inv_def, Complex.normSq_eq_norm_sq, h s]
  simp

theorem heisOF_dblG_deltaT : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (w : Formalism.IndefR.DatumF.WOF F E nS (nT + nT)) (f₁ f₂ : Formalism.IndefR.DatumF.WOF F E nS nT → ℂ),
        Formalism.IndefR.DatumF.heisOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ w (GlobalTheory.DblTargetDelta.deltaT f₁ f₂) =
          GlobalTheory.DblTargetDelta.deltaT (Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ (GlobalTheory.DblTargetDelta.topR w) f₁)
            (Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ (-GlobalTheory.DblTargetDelta.botR w) f₂) := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT _ _ ξ₀ _ _ w f₁ f₂
  have hn : ∀ x, ‖B.ψ x‖ = 1 := (GlobalTheory.StdCharWeilDatum.isStdCharF_of_isGood F E σ B hB).1.2.1
  funext x
  have ht : topR (x + w) = topR x + topR w := rfl
  have hb : -botR (x + w) = -botR x + -botR w := by
    rw [← neg_add]; rfl
  simp only [heisOF, deltaT_apply, ht, hb, symplOHF_dblG, map_mul, conj_psi hn, sub_eq_add_neg, AddChar.map_add_eq_mul]
  ring

end GlobalTheory.DblHeis

end
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.StabFin
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.exists_common_eigenvector_rho_adjoinRoot_embedding : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (i : Fin G.m) (τ : FM P →+* PadicAlgCl p), τ.comp (algebraMap G.F (FM P)) = G.emb i → ∃ v : Fin G.n → PadicAlgCl p, v ≠ 0 ∧ ∀ a : FM P, (G.rho i (jM P a)).map (fun x => (x : PadicAlgCl p)) *ᵥ v = τ a • v := by
  first | (exact @GlobalTheory.StabFin.rho_jM_common_eigvec) | (exact GlobalTheory.StabFin.rho_jM_common_eigvec) | (intros; apply GlobalTheory.StabFin.rho_jM_common_eigvec  <;> assumption)
end
