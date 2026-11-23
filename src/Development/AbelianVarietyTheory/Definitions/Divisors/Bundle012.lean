module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle005
public import Development.AbelianVarietyTheory.Definitions.Divisors.EntireEqOfHalfPlane
public import Mathlib.RingTheory.DedekindDomain.Different
public import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.CountSt
import Mathlib.Algebra.Module.StablyFree.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle002
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
public import Mathlib.LinearAlgebra.LinearIndependent.BaseChange
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.Bundle002
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open WittVector Ideal CategoryTheory Opposite

namespace GlobalTheory.PDivLat

open GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (span {(p : O)}) O]


variable (p O) in
def ghost (n : ℕ) (a : Ainf p O) : O :=
  fontaineTheta O p ((WittVector.frobenius : Ainf p O →+* Ainf p O)^[n] a)

set_option autoImplicit false in
open WittVector Ideal CategoryTheory Opposite in
variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (span {(p : O)}) O] in
theorem _root_.GlobalTheory.PDivLat.ghost_add (n : ℕ) (a b : _root_.GlobalTheory.Sandwich.Ainf p O) :
    _root_.GlobalTheory.PDivLat.ghost p O n (a + b) = _root_.GlobalTheory.PDivLat.ghost p O n a + _root_.GlobalTheory.PDivLat.ghost p O n b := by
  simp only [_root_.GlobalTheory.PDivLat.ghost, iterate_map_add, map_add (f := _)]

set_option autoImplicit false in
open WittVector Ideal CategoryTheory Opposite in
variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (span {(p : O)}) O] in
theorem _root_.GlobalTheory.PDivLat.ghost_mul (n : ℕ) (a b : _root_.GlobalTheory.Sandwich.Ainf p O) :
    _root_.GlobalTheory.PDivLat.ghost p O n (a * b) = _root_.GlobalTheory.PDivLat.ghost p O n a * _root_.GlobalTheory.PDivLat.ghost p O n b := by
  simp only [_root_.GlobalTheory.PDivLat.ghost, iterate_map_mul, map_mul]

set_option autoImplicit false in
open WittVector Ideal CategoryTheory Opposite in
variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (span {(p : O)}) O] in
theorem _root_.GlobalTheory.PDivLat.ghost_zero (n : ℕ) : _root_.GlobalTheory.PDivLat.ghost p O n 0 = 0 := by
  simp only [_root_.GlobalTheory.PDivLat.ghost, iterate_map_zero, map_zero]

theorem ghost_frobenius (n : ℕ) (a : Ainf p O) :
    ghost p O n (WittVector.frobenius a) = ghost p O (n + 1) a := rfl

abbrev TDual (G : PDivGroup p O) : Type := G.Tate →ₛₗ[ofPadic p O] Ainf p O

def latt (G : PDivGroup p O) : Submodule (Ainf p O) (TDual G) where
  carrier := {y | ∀ n, ∃ x : G.dual.Lie, ∀ t, ghost p O n (y t) = x (hodgeTate G t)}
  zero_mem' n := ⟨0, fun _ => ghost_zero n⟩
  add_mem' {y z} hy hz n := by
    obtain ⟨x, hx⟩ := hy n
    obtain ⟨x', hx'⟩ := hz n
    exact ⟨x + x', fun t => by rw [LinearMap.add_apply, ghost_add, hx, hx', LinearMap.add_apply]⟩
  smul_mem' a y hy n := by
    obtain ⟨x, hx⟩ := hy n
    exact ⟨ghost p O n a • x, fun t => by
      rw [LinearMap.smul_apply, smul_eq_mul, ghost_mul, hx, LinearMap.smul_apply, smul_eq_mul]⟩

def lattMap {G H : PDivGroup p O} (f : G ⟶ H) : latt H →ₗ[Ainf p O] latt G where
  toFun y := ⟨y.1.comp (tateMap G H O f), fun n => by
    obtain ⟨x, hx⟩ := y.2 n
    exact ⟨x ∘ₗ omegaDualMap G H f, fun t => by
      rw [LinearMap.comp_apply, hx, hodgeTate_tateMap, LinearMap.comp_apply]⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl


variable (p O) in
def lattFunctor : (PDivGroup p O)ᵒᵖ ⥤ ModuleCat.{0} (Ainf p O) where
  obj G := ModuleCat.of _ (latt G.unop)
  map f := ModuleCat.ofHom (lattMap f.unop)
  map_id _ := rfl
  map_comp _ _ := rfl

def HasDatum [IsDomain O] {ε : PreTilt O p} (hε : IsPrimitiveSystem ε) (G : PDivGroup p O) : Prop :=
  ∃ (D : Datum ε G.height ℤ_[p]) (e : G.Tate ≃ₗ[ℤ_[p]] (Fin G.height → ℤ_[p]))
    (fil : G.dual.omega ≃ₗ[O] D.Fil) (lie : ((Fin G.height → O) ⧸ D.Fil) ≃ₗ[O] G.Lie),
    (∀ t, D.al (toO e t) = (fil (hodgeTate G t) : Fin G.height → O)) ∧
      ∀ (x : G.Lie) (χ : G.dual.Tate), pairingO hε e (bQuot D (lie.symm x)) χ = x (dlog G χ)

def IsConn (G : PDivGroup p O) : Prop := ∀ n, IsLocalRing (G.A n)

def IsConst (G : PDivGroup p O) : Prop :=
  ∀ n, Nonempty (G.A n ≃ₐ[O] (Fin (p ^ (n * G.height)) → O))

def IsSum (G G₁ G₂ : PDivGroup p O) : Prop :=
  ∃ (i₁ : G₁ ⟶ G) (i₂ : G₂ ⟶ G) (q₁ : G ⟶ G₁) (q₂ : G ⟶ G₂), i₁ ≫ q₁ = 𝟙 _ ∧ i₂ ≫ q₂ = 𝟙 _ ∧
    i₁ ≫ q₂ = 0 ∧ i₂ ≫ q₁ = 0 ∧ q₁ ≫ i₁ + q₂ ≫ i₂ = 𝟙 _

end GlobalTheory.PDivLat
end
end

section

set_option autoImplicit false

noncomputable section

open NumberField GlobalTheory.CMVal

namespace GlobalTheory.RoadE

variable {E : Type} [Field E] [NumberField E]

def ptE (t : E) (x : Fin 2 → maximalRealSubfield E) : E := ((x 0 : maximalRealSubfield E) : E) * t + ((x 1 : maximalRealSubfield E) : E)

theorem ptE_smul (t : E) (a : OF E) (x : Fin 2 → maximalRealSubfield E) :
    ptE t (a • x) = algebraMap (OF E) E a * ptE t x := by
  simp only [ptE, Pi.smul_apply]
  rw [Algebra.smul_def, Algebra.smul_def]
  push_cast
  have h : (((algebraMap (OF E) (maximalRealSubfield E) a) : maximalRealSubfield E) : E) = algebraMap (OF E) E a := rfl
  rw [h]; ring

end GlobalTheory.RoadE
end
end

section

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.HeckeGal

namespace GlobalTheory.WpFam

def Tr {K : Type} [Field K] [NumberField K] (t : (Af K)ˣ) (x x' : K) : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 K), Valued.v (((t : Af K) * algebraMap K (Af K) x' - algebraMap K (Af K) x) v) ≤ 1

structure IsTr {K : Type} [Field K] (ι : K →+* ℂ) (Λ₀ Λ₁ : PeriodPair) (T : K → K → Prop) : Prop where

  sub : ∀ x x' y y', T x x' → T y y' → T (x - y) (x' - y')

  mem_iff : ∀ x x', T x x' → (ι x ∈ Λ₀.lattice ↔ ι x' ∈ Λ₁.lattice)

  triv : ∀ x x', ι x ∈ Λ₀.lattice → ι x' ∈ Λ₁.lattice → T x x'

  left : ∀ x, ∃ x', T x x'

  right : ∀ x', ∃ x, T x x'

  rat₀ : ∀ z ∈ Λ₀.lattice, ∃ k, ι k = z

  rat₁ : ∀ z ∈ Λ₁.lattice, ∃ k, ι k = z

end GlobalTheory.WpFam
end
end

section

noncomputable section

open NumberField IsDedekindDomain

namespace GlobalTheory.CMVal

variable {E : Type} [Field E] [NumberField E]

def IsCMType {I : Type} (φ : I → E →+* ℂ) : Prop :=
  ∀ σ : E →+* ℂ, ∃! i, σ = φ i ∨ σ = ComplexEmbedding.conjugate (φ i)

def UnramFin (E : Type) [Field E] [NumberField E] : Prop := differentIdeal (OF E) (𝓞 E) = ⊤

def Over (P : HeightOneSpectrum (𝓞 E)) (v : HeightOneSpectrum (OF E)) : Prop :=
  P.asIdeal.comap (algebraMap (OF E) (𝓞 E)) = v.asIdeal

def Splits (v : HeightOneSpectrum (OF E)) : Prop := ∃ P P' : HeightOneSpectrum (𝓞 E), P ≠ P' ∧ Over P v ∧ Over P' v

def expIn (𝔣 : Ideal (OF E)) (v : HeightOneSpectrum (OF E)) : ℕ := multiplicity v.asIdeal 𝔣

def IsBaseCond (𝔣 : Ideal (OF E)) : Prop :=
  𝔣 ≠ ⊥ ∧ 𝔣 ≠ ⊤ ∧ ∀ v : HeightOneSpectrum (OF E), v.asIdeal ∣ 𝔣 → Splits v ∧ expIn 𝔣 v ≤ 2 ∧
    ∃ l : ℕ, l.Prime ∧ l ≠ 2 ∧ (l : OF E) ∈ v.asIdeal ∧ ¬ (l : ℤ) ∣ discr E ∧
      ∀ P : HeightOneSpectrum (𝓞 E), (l : 𝓞 E) ∈ P.asIdeal → Ideal.absNorm P.asIdeal = l

def IsFinSetSplitPlacesCoprimeConductor (𝔣 : Ideal (OF E)) (Q : Finset (HeightOneSpectrum (OF E))) : Prop :=
  ∀ q ∈ Q, Splits q ∧ ¬ q.asIdeal ∣ 𝔣

def condQ (𝔣 : Ideal (OF E)) (Q : Finset (HeightOneSpectrum (OF E))) : Ideal (OF E) := 𝔣 * ∏ q ∈ Q, q.asIdeal

def IsValChar {I : Type} [Fintype I] (φ : I → E →+* ℂ) (s : ℕ) (κ : I → ℕ) (𝔣 : Ideal (OF E))
    (Q : Finset (HeightOneSpectrum (OF E))) (χ : HChar E) : Prop :=
  IsUnitary χ ∧ TrivOnF χ ∧ HasInf χ φ (fun i => (κ i : ℤ) + s) ∧
    ∀ (v : HeightOneSpectrum (OF E)) (P : HeightOneSpectrum (𝓞 E)), Over P v →
      (v ∈ Q → LevelLe χ P 1) ∧ (v ∉ Q → ExpAt χ P (expIn 𝔣 v))

def IntAt (l : ℕ) (a : ℂ) : Prop := ∃ n : ℕ, n.Coprime l ∧ IsIntegral ℤ ((n : ℂ) * a)

def UnitAt (l : ℕ) (a : ℂ) : Prop := a ≠ 0 ∧ IntAt l a ∧ IntAt l a⁻¹

def LInf {I : Type} [Fintype I] (m : I → ℤ) (s : ℂ) : ℂ :=
  ∏ i, (2 * (2 * (Real.pi : ℂ)) ^ (-(s + (|m i| : ℤ))) * Complex.Gamma (s + (|m i| : ℤ)))

end GlobalTheory.CMVal
end
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HermTools

open ReciprocityTheory.GeometryOfNumbersTheory Matrix NumberField
open scoped ComplexOrder ComplexConjugate

variable {K E : Type*} [Field K] [Field E] {V V' : Type*} [AddCommGroup V] [Module K V]

section Complex

variable (h : HermFam K V) (σ : K →+* ℂ) {ι : Type*} [Fintype ι]

def csq (c : ι → ℂ) (v : ι → V) : ℝ := (∑ i, ∑ k, conj (c i) * c k * h.form σ (v i) (v k)).re

def cnrm (c : ι → ℂ) (v : ι → V) : ℝ := Real.sqrt (csq h σ c v)

theorem csq_map (a : ι → K) (v : ι → V) :
    csq h σ (fun i => σ (a i)) v = (h.form σ (∑ i, a i • v i) (∑ i, a i • v i)).re := by
  rw [csq, h.form_sum_left]
  refine congrArg _ (Finset.sum_congr rfl fun i _ => ?_)
  rw [h.form_sum_right]
  exact Finset.sum_congr rfl fun k _ => by rw [h.form_smul_left, h.smul_right, mul_assoc]

theorem cnrm_map (a : ι → K) (v : ι → V) : cnrm h σ (fun i => σ (a i)) v = h.nrm σ (∑ i, a i • v i) :=
  congrArg Real.sqrt (csq_map h σ a v)

theorem csq_comb {κ : Type*} [Fintype κ] (c : ι → ℂ) (a : ι → κ → K) (b : κ → V) :
    csq h σ c (fun i => ∑ k, a i k • b k) = csq h σ (fun k => ∑ i, c i * σ (a i k)) b := by

  simp only [csq, h.form_sum_left, h.form_sum_right, h.form_smul_left, h.smul_right, map_sum, map_mul,
  Finset.mul_sum, Finset.sum_mul]
  refine congrArg _ ?_
  simp only [← Fintype.sum_prod_type']
  exact Fintype.sum_equiv ⟨fun t => (t.2.2.1, t.2.2.2, t.2.1, t.1), fun t => (t.2.2.2, t.2.2.1, t.1, t.2.1),
    fun _ => rfl, fun _ => rfl⟩ _ _ fun t => by simp only [Equiv.coe_fn_mk]; ring

theorem csq_nonneg (c : ι → ℂ) (v : ι → V) : 0 ≤ csq h σ c v := by
  let S := Submodule.span K (Set.range v)
  have : FiniteDimensional K S := FiniteDimensional.span_of_finite K (Set.finite_range v)
  let b := Module.finBasis K S
  have e : v = fun i => ∑ k, b.repr ⟨v i, Submodule.subset_span ⟨i, rfl⟩⟩ k • (b k : V) := funext fun i => by
    exact (congrArg S.subtype (b.sum_repr ⟨v i, Submodule.subset_span ⟨i, rfl⟩⟩).symm).trans (map_sum _ _ _)
  rw [e, csq_comb]
  generalize (fun k => ∑ i, c i * σ _) = x
  have := (h.posDef σ _ _ (b.linearIndependent.map' S.subtype S.ker_subtype)).posSemidef.dotProduct_mulVec_nonneg x
  refine (Complex.nonneg_iff.1 this).1.trans_eq (congrArg _ ?_)
  simp [dotProduct, mulVec, Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm]

end Complex

def ofCoords {P : (K →+* ℂ) → Type*} [∀ σ, Fintype (P σ)] (φ : ∀ σ, V →ₛₗ[σ] (P σ → ℂ))
    (G : ∀ σ, Matrix (P σ) (P σ) ℂ) (hG : ∀ σ, (G σ).PosDef)
    (hφ : ∀ σ n (v : Fin n → V), LinearIndependent K v → LinearIndependent ℂ fun i => φ σ (v i)) :
    HermFam K V where
  form σ x y := star (φ σ x) ⬝ᵥ G σ *ᵥ φ σ y
  add_right σ x y z := by rw [map_add (f := _), mulVec_add, dotProduct_add]
  smul_right σ a x y := by rw [map_smulₛₗ, mulVec_smul, dotProduct_smul, smul_eq_mul]
  conj_symm σ x y := by
    rw [starRingEnd_apply, ← star_dotProduct_star, star_star, star_mulVec, (hG σ).1.eq, ← dotProduct_mulVec]
  posDef σ n v hv := by
    classical
    have := (hG σ).conjTranspose_mul_mul_same (B := Matrix.of fun p i => φ σ (v i) p)
      (Matrix.mulVec_injective_iff.2 (hφ σ n v hv))
    convert this using 1
    ext i j
    simp [dotProduct, mulVec, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, mul_assoc]
    exact Finset.sum_comm

def comap [AddCommGroup V'] [Module K V'] (h : HermFam K V) (f : V' →ₗ[K] V) (hf : Function.Injective f) :
    HermFam K V' where
  form σ x y := h.form σ (f x) (f y)
  add_right σ x y z := by rw [map_add (f := _), h.add_right]
  smul_right σ a x y := by rw [map_smul, h.smul_right]
  conj_symm σ x y := h.conj_symm σ _ _
  posDef σ n v hv := h.posDef σ n _ (hv.map' f (LinearMap.ker_eq_bot.2 hf))

theorem isConjInv_comap [AddCommGroup V'] [Module K V'] {h : HermFam K V} (hh : h.IsConjInv) (f : V' →ₗ[K] V)
    (hf : Function.Injective f) : (comap h f hf).IsConjInv := fun σ _ _ => hh σ _ _

def basisCoords {n : Type*} [Finite n] (b : Module.Basis n K V) (σ : K →+* ℂ) : V →ₛₗ[σ] (n → ℂ) where
  toFun x i := σ (b.repr x i)
  map_add' x y := funext fun i => by simp
  map_smul' a x := funext fun i => by simp

theorem linearIndependent_basisCoords {n ι : Type*} [Finite n] (b : Module.Basis n K V) (σ : K →+* ℂ) {v : ι → V}
    (hv : LinearIndependent K v) : LinearIndependent ℂ fun i => basisCoords b σ (v i) :=
  letI := σ.toAlgebra
  linearIndependent_algebraMap_comp_iff.2 (hv.map' b.equivFun.toLinearMap b.equivFun.ker)

def ofGram {n : Type*} [Fintype n] (b : Module.Basis n K V) (G : (K →+* ℂ) → Matrix n n ℂ)
    (hG : ∀ σ, (G σ).PosDef) : HermFam K V :=
  ofCoords (P := fun _ => n) (basisCoords b) G hG fun σ _ _ => linearIndependent_basisCoords b σ

theorem form_ofGram {n : Type*} [Fintype n] (b : Module.Basis n K V) (G : (K →+* ℂ) → Matrix n n ℂ)
    (hG : ∀ σ, (G σ).PosDef) (σ : K →+* ℂ) (i j : n) : (ofGram b G hG).form σ (b i) (b j) = G σ i j := by
  classical
  simp [ofGram, ofCoords, basisCoords, dotProduct, mulVec, Finsupp.single_apply, apply_ite]

theorem isConjInv_ofGram {n : Type*} [Fintype n] (b : Module.Basis n K V) {G : (K →+* ℂ) → Matrix n n ℂ}
    (hG : ∀ σ, (G σ).PosDef) (hc : ∀ σ i j, G (ComplexEmbedding.conjugate σ) i j = conj (G σ i j)) :
    (ofGram b G hG).IsConjInv := fun σ x y => by
  simp [ofGram, ofCoords, basisCoords, dotProduct, mulVec, hc]

def ofBasis {n : Type*} [Fintype n] [DecidableEq n] (b : Module.Basis n K V) : HermFam K V :=
  ofGram b (fun _ => 1) fun _ => PosDef.one

theorem nrm_ofBasis {n : Type*} [Fintype n] [DecidableEq n] (b : Module.Basis n K V) (σ : K →+* ℂ) (i : n) :
    (ofBasis b).nrm σ (b i) = 1 := by
  simp [HermFam.nrm, ofBasis, form_ofGram]

theorem isConjInv_ofBasis {n : Type*} [Fintype n] [DecidableEq n] (b : Module.Basis n K V) :
    (ofBasis b).IsConjInv := isConjInv_ofGram b _ fun _ i j => by simp [Matrix.one_apply, apply_ite]

section Extend

variable [AddCommGroup V'] [Module E V'] {j : K →+* E}

structure IsExtension (ι : V →ₛₗ[j] V') : Prop where

  indep : ∀ (n : ℕ) (v : Fin n → V), LinearIndependent K v → LinearIndependent E fun i => ι (v i)

  span : Submodule.span E (Set.range ι) = ⊤

variable {ι : V →ₛₗ[j] V'} (hι : IsExtension ι)

def IsExtension.basis {n : ℕ} (b : Module.Basis (Fin n) K V) : Module.Basis (Fin n) E V' :=
  Module.Basis.mk (hι.indep n b b.linearIndependent) (hι.span.ge.trans (Submodule.span_le.2 (by
    rintro _ ⟨x, rfl⟩

    rw [← b.sum_repr x, map_sum]
    exact Submodule.sum_mem _ fun i _ => by
      rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))))

variable [FiniteDimensional K V]


def extend (h : HermFam K V) : HermFam E V' :=
  ofGram (hι.basis (Module.finBasis K V)) (fun τ => h.gram (τ.comp j) (Module.finBasis K V))
    fun _ => h.posDef _ _ _ (Module.finBasis K V).linearIndependent

theorem isConjInv_extend {h : HermFam K V} (hh : h.IsConjInv) : (extend hι h).IsConjInv :=
  isConjInv_ofGram _ _ fun τ _ _ => hh (τ.comp j) _ _

end Extend

end GlobalTheory.HermTools
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.EndLoc

variable {S : Scheme.{0}} {O : Type} [Ring O]

def IsRAct (A : Over S) [GrpObj A] (act : O → (A ⟶ A)) : Prop :=
  (∀ a, IsMonHom (act a)) ∧ act 1 = 𝟙 A ∧ (∀ a b, act (a * b) = act a ≫ act b) ∧
    ∀ a b, act (a + b) = act a * act b

def Adj (A : Over S) [GrpObj A] (Q : LB (A ⊗ A).left) (bar : O → O) (act : O → (A ⟶ A)) : Prop :=
  ∀ a, LBIso (Q.pull (lift (fst A A ≫ act a) (snd A A)).left) (Q.pull (lift (fst A A) (snd A A ≫ act (bar a))).left)

structure ActRep (A : Over S) [GrpObj A] (Q : LB (A ⊗ A).left) (bar : O → O) where
  H : Scheme.{0}
  π : H ⟶ S
  AH : Over H
  [grp : GrpObj AH]
  φ : AH.left ⟶ A.left
  φ₂ : (AH ⊗ AH).left ⟶ (A ⊗ A).left
  pb : IsGrpPullback AH A π φ
  sq : IsSquare φ φ₂
  act : O → (AH ⟶ AH)
  isAct : IsRAct AH act
  adj : Adj AH (Q.pull φ₂) bar act
  rep : ∀ (T : Scheme.{0}) (t : T ⟶ S) (A' : Over T) [GrpObj A'] (φ' : A'.left ⟶ A.left)
    (φ₂' : (A' ⊗ A').left ⟶ (A ⊗ A).left) (act' : O → (A' ⟶ A')), IsGrpPullback A' A t φ' → IsSquare φ' φ₂' →
    IsRAct A' act' → Adj A' (Q.pull φ₂') bar act' →
    ∃! h : T ⟶ H, h ≫ π = t ∧ ∃ ψ : A'.left ⟶ AH.left, IsGrpPullback A' AH h ψ ∧ ψ ≫ φ = φ' ∧
      ∀ a, (act' a).left ≫ ψ = ψ ≫ (act a).left

attribute [instance] ActRep.grp

theorem IsRAct.of_oAct {O : Type} [CommRing O] {A : Over S} [GrpObj A] (i : OAct O A) : IsRAct A i.act :=
  ⟨i.hom, i.one, i.mul, i.add⟩

theorem IsRAct.op_of_ringAct {A : Over S} [GrpObj A] [IsCommMonObj A] (ρ : Out.RingAct A O) :
    IsRAct A (fun a : Oᵐᵒᵖ => ρ.act a.unop) :=
  ⟨fun _ => ρ.hom _, ρ.map_one, fun _ _ => ρ.map_mul _ _, fun _ _ => ρ.map_add _ _⟩

def IsRAct.toOAct {O : Type} [CommRing O] {A : Over S} [GrpObj A] {act : O → (A ⟶ A)} (h : IsRAct A act) :
    OAct O A :=
  ⟨act, h.1, h.2.1, h.2.2.1, h.2.2.2⟩

end GlobalTheory.EndLoc
end
end
