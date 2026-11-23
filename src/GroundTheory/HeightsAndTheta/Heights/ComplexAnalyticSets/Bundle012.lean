module

public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle008
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle001
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle002
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.Spectrum.Prime.Defs
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle003
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Countable
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
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Statements
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial
open scoped nonZeroDivisors

noncomputable section

theorem SliceIdeal.isHomogeneous_linForm {n : ℕ} (u : Fin n → ℂ) : (linForm u).IsHomogeneous 1 :=
  IsHomogeneous.sum _ _ _ fun j _ => isHomogeneous_C_mul_X (u j) j

theorem SliceIdeal.exists_homogeneous_sub_mem {n : ℕ} (ℓ : Fin n → ℂ) (f : MvPolynomial (Fin n) ℂ) :
    ∃ d, ∃ G : MvPolynomial (Fin n) ℂ, G.IsHomogeneous d ∧ G - f ∈ Ideal.span {linForm ℓ - 1} := by
  classical
  refine ⟨f.totalDegree, ∑ i ∈ Finset.range (f.totalDegree + 1),
      linForm ℓ ^ (f.totalDegree - i) * homogeneousComponent i f, ?_, ?_⟩
  · refine IsHomogeneous.sum _ _ _ fun i hi => ?_
    have hi' : i ≤ f.totalDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have h := ((SliceIdeal.isHomogeneous_linForm ℓ).pow (f.totalDegree - i)).mul
      (homogeneousComponent_isHomogeneous i f)
    convert h using 1
    omega
  · have hsum : (∑ i ∈ Finset.range (f.totalDegree + 1),
          linForm ℓ ^ (f.totalDegree - i) * homogeneousComponent i f) - f =
        ∑ i ∈ Finset.range (f.totalDegree + 1),
          (linForm ℓ ^ (f.totalDegree - i) - 1) * homogeneousComponent i f := by
      conv_lhs => arg 2; rw [← sum_homogeneousComponent f]
      rw [← Finset.sum_sub_distrib]
      simp only [sub_one_mul]
    rw [hsum]
    refine Ideal.sum_mem _ fun i _ => ?_
    refine Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton.mpr ?_)
    simpa using sub_dvd_pow_sub_pow (linForm ℓ) 1 (f.totalDegree - i)

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def SliceDim.Statement : Prop :=
  ∀ (n e : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (ℓ : Fin n → ℂ),
    IsProjPrime J → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = ((e + 1 : ℕ) : WithBot ℕ∞) →
    linForm ℓ ∉ J →
      ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ (J ⊔ Ideal.span {linForm ℓ - 1})) =
        ((e : ℕ) : WithBot ℕ∞)

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

noncomputable section

def NormalModelDivisorGoodPoint {n : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)}
    (M : IndefiniteRowSideFullHecke.ComplexSets.NormalModel J) (u : Fin n → ℂ) (d : ℕ) (w : Fin n ⊕ Fin M.m → ℂ) : Prop :=
  w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal ∧
  ∃ (c : ℕ) (f : Fin c → MvPolynomial (Fin n ⊕ Fin M.m) ℂ) (h g a b : MvPolynomial (Fin n ⊕ Fin M.m) ℂ) (k : ℕ),
    c + (d + 1) = n + M.m ∧ (∀ j, f j ∈ M.ideal) ∧
    eval w h ≠ 0 ∧ (∀ p ∈ M.ideal, ∃ e : ℕ, h ^ e * p ∈ Ideal.span (Set.range f)) ∧
    eval w g = 0 ∧
    LinearIndependent ℂ (Fin.cons (fun s ↦ eval w (pderiv s g)) (fun j s ↦ eval w (pderiv s (f j))) :
      Fin (c + 1) → Fin n ⊕ Fin M.m → ℂ) ∧
    0 < k ∧ eval w a ≠ 0 ∧ eval w b ≠ 0 ∧
    b * rename (Sum.inl : Fin n → Fin n ⊕ Fin M.m) (linForm u) - a * g ^ k ∈ M.ideal ∧
    ∀ v : Fin n ⊕ Fin M.m → ℂ, (∀ i : Fin n, v (Sum.inl i) = 0) →
      ∑ s, eval w (pderiv s g) * v s = 0 → (∀ j, ∑ s, eval w (pderiv s (f j)) * v s = 0) → v = 0

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix

open scoped ENNReal

noncomputable section

def AreaLinear.Statement : Prop :=
  ∀ (k m : ℕ) (L : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)),
    Function.Injective L → ∀ A : Set (EuclideanSpace ℝ (Fin k)),
      μH[(k : ℝ)] (L '' A) =
        ENNReal.ofReal (√(LinearMap.det (LinearMap.adjoint L ∘ₗ L))) * μH[(k : ℝ)] A


def realGraphPt {k m : ℕ} (F : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin m))
    (x : EuclideanSpace ℝ (Fin k)) : EuclideanSpace ℝ (Fin k ⊕ Fin m) :=
  WithLp.toLp 2 (Sum.elim (fun i => x i) (fun i => F x i))

def AreaGraph.Statement : Prop :=
  ∀ (k m : ℕ) (U : Set (EuclideanSpace ℝ (Fin k)))
    (F : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin m)),
    IsOpen U → ContDiffOn ℝ 1 F U → ∀ A ⊆ U, MeasurableSet A →
      μH[(k : ℝ)] (realGraphPt F '' A) =
        ∫⁻ x in A, ENNReal.ofReal (√(LinearMap.det
          ((1 : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin k)) +
            LinearMap.adjoint (fderiv ℝ F x : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) ∘ₗ
              (fderiv ℝ F x : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))))) ∂(μH[(k : ℝ)])

def graphPt {d m n : ℕ} (e : Fin n ≃ Fin d ⊕ Fin m)
    (F : EuclideanSpace ℂ (Fin d) → EuclideanSpace ℂ (Fin m)) (x : EuclideanSpace ℂ (Fin d)) :
    EuclideanSpace ℂ (Fin n) :=
  WithLp.toLp 2 fun j => Sum.elim (fun i => x i) (fun i => F x i) (e j)

def frameProj {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (I : Finset (Fin n)) (z : EuclideanSpace ℂ (Fin n)) : I → ℂ :=
  fun i => inner ℂ (b i) z

def frameFibreCount {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (I : Finset (Fin n)) (S : Set (EuclideanSpace ℂ (Fin n))) (x : I → ℂ) : ℝ≥0∞ :=
  (({z ∈ S | frameProj b I z = x}.encard : ℕ∞) : ℝ≥0∞)

def ProjectionFormula.Statement : Prop :=
  ∀ (d m n : ℕ) (e : Fin n ≃ Fin d ⊕ Fin m) (Ω : Set (EuclideanSpace ℂ (Fin d)))
    (F : EuclideanSpace ℂ (Fin d) → EuclideanSpace ℂ (Fin m)),
    IsOpen Ω → DifferentiableOn ℂ F Ω →
    ∀ (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
      (B : Set (EuclideanSpace ℂ (Fin n))), MeasurableSet B →
      μH[((2 * d : ℕ) : ℝ)] (graphPt e F '' Ω ∩ B) =
        ∑ I ∈ Finset.univ.powersetCard d, ∫⁻ x : EuclideanSpace ℂ I,
          frameFibreCount b I (graphPt e F '' Ω ∩ B) (WithLp.ofLp x) ∂(μH[((2 * d : ℕ) : ℝ)])

def zeroSetEuc {n : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) : Set (EuclideanSpace ℂ (Fin n)) :=
  {z | ∀ q ∈ J, eval (fun i => z i) q = 0}

def NullSmaller.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)),
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) < d →
      μH[((2 * d : ℕ) : ℝ)] (zeroSetEuc J) = 0

def MassFinite.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)), J.IsPrime →
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d → ∀ R : ℝ,
      μH[((2 * d : ℕ) : ℝ)] (zeroSetEuc J ∩ Metric.ball 0 R) < ⊤

def PolySublevel.Statement : Prop :=
  ∀ (d : ℕ) (Q : MvPolynomial (Fin d) ℂ), Q ≠ 0 → ∀ R : ℝ, 0 < R →
    ∃ C α : ℝ, 0 < C ∧ 0 < α ∧ ∀ η : ℝ, 0 < η → η ≤ 1 →
      volume {x : Fin d → ℂ | x ∈ Metric.ball 0 R ∧ ‖eval x Q‖ ≤ η} ≤ ENNReal.ofReal (C * η ^ α)

def linProjHom {n d : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ) :
    MvPolynomial (Fin d) ℂ →ₐ[ℂ] MvPolynomial (Fin n) ℂ ⧸ J :=
  (Ideal.Quotient.mkₐ ℂ J).comp (aeval fun i => ∑ j, C (A i j) * X j)

structure IsFiniteLinProj {n d : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ))
    (A : Matrix (Fin d) (Fin n) ℂ) : Prop where

  injective : Function.Injective (linProjHom J A)

  finite : (linProjHom J A : MvPolynomial (Fin d) ℂ →+* MvPolynomial (Fin n) ℂ ⧸ J).Finite

def SlabBound.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ) (u : Fin n → ℂ),
    J.IsPrime → IsFiniteLinProj J A → linForm u ∉ J →
      ∃ Q : MvPolynomial (Fin d) ℂ, Q ≠ 0 ∧ ∀ R : ℝ, ∃ C : ℝ, ∀ z ∈ zeroSetEuc J, ‖z‖ ≤ R →
        ‖eval (A *ᵥ fun j => z j) Q‖ ≤ C * ‖∑ j, u j * z j‖

section Inhabitants

end Inhabitants

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

theorem map_inf_eq_of_sup_inf_ker_le {R R' : Type*} [CommRing R] [CommRing R'] (φ : R →+* R')
    (hφ : Function.Surjective φ) (I J : Ideal R)
    (h : (I ⊔ J) ⊓ RingHom.ker φ ≤ RingHom.ker φ * (I ⊔ J)) :
    (I ⊓ J).map φ = I.map φ ⊓ J.map φ := by
  refine le_antisymm (Ideal.map_inf_le φ) ?_
  rintro y ⟨hyI, hyJ⟩
  obtain ⟨a, ha, rfl⟩ := (Ideal.mem_map_iff_of_surjective φ hφ).1 hyI
  obtain ⟨b, hb, hab⟩ := (Ideal.mem_map_iff_of_surjective φ hφ).1 hyJ
  have hmem : a - b ∈ (I ⊔ J) ⊓ RingHom.ker φ :=
    ⟨Ideal.sub_mem _ (Ideal.mem_sup_left ha) (Ideal.mem_sup_right hb),
      RingHom.mem_ker.2 (by rw [map_sub, hab, sub_self])⟩
  have h2 : a - b ∈ RingHom.ker φ * I ⊔ RingHom.ker φ * J := by
    rw [← Ideal.mul_sup]; exact h hmem
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.1 h2
  have hu' : u ∈ RingHom.ker φ ⊓ I := Ideal.mul_le_inf hu
  have hv' : v ∈ RingHom.ker φ ⊓ J := Ideal.mul_le_inf hv
  refine (Ideal.mem_map_iff_of_surjective φ hφ).2 ⟨a - u, ⟨Ideal.sub_mem _ ha hu'.2, ?_⟩, ?_⟩
  · have e : a - u = b + v := by linear_combination -huv
    rw [e]
    exact Ideal.add_mem _ hb hv'.2
  · rw [map_sub, RingHom.mem_ker.1 hu'.1, sub_zero]

theorem GenericFibreRadical.proof (hT : GenericFibreTor.Statement)
    (hP : GenericFibreRadicalPrime.Statement) : GenericFibreRadical.Statement := by
  intro σ _ ι _ K hK
  have hsurj : ∀ t : σ → ℂ, Function.Surjective
      (MvPolynomial.map (eval t) : MvPolynomial ι (MvPolynomial σ ℂ) →+* MvPolynomial ι ℂ) :=
    fun t => MvPolynomial.map_surjective _ (fun c => ⟨C c, eval_C c⟩)
  classical
  have key : ∀ s : Finset (Ideal (MvPolynomial ι (MvPolynomial σ ℂ))), (∀ p ∈ s, p.IsPrime) →
      ∃ F : MvPolynomial σ ℂ, F ≠ 0 ∧ ∀ t : σ → ℂ, eval t F ≠ 0 →
        ((s.inf id).map (MvPolynomial.map (eval t))).IsRadical := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro _
      refine ⟨1, one_ne_zero, fun t _ => ?_⟩
      rw [Finset.inf_empty, Ideal.map_top]
      exact fun _ _ => Submodule.mem_top
    | insert p s hps ih =>
      intro hs
      obtain ⟨F₁, hF₁, h₁⟩ := ih (fun q hq => hs q (Finset.mem_insert_of_mem hq))
      obtain ⟨F₂, hF₂, h₂⟩ := hP σ ι p (hs p (Finset.mem_insert_self p s))
      obtain ⟨F₃, hF₃, h₃⟩ := hT σ ι (p ⊔ s.inf id)
      refine ⟨F₁ * F₂ * F₃, mul_ne_zero (mul_ne_zero hF₁ hF₂) hF₃, fun t ht => ?_⟩
      simp only [map_mul, ne_eq, mul_eq_zero, not_or] at ht
      obtain ⟨⟨ht₁, ht₂⟩, ht₃⟩ := ht
      rw [Finset.inf_insert, id, map_inf_eq_of_sup_inf_ker_le _ (hsurj t) _ _ (h₃ t ht₃)]
      exact (h₂ t ht₂).inf (h₁ t ht₁)
  have hfin := Ideal.finite_minimalPrimes_of_isNoetherianRing _ K
  obtain ⟨F, hF, hFt⟩ := key hfin.toFinset (fun p hp => ((hfin.mem_toFinset).1 hp).1.1)
  refine ⟨F, hF, fun t ht => ?_⟩
  have hK' : K = hfin.toFinset.inf id := by
    rw [Finset.inf_id_eq_sInf, Set.Finite.coe_toFinset, Ideal.sInf_minimalPrimes]
    exact le_antisymm Ideal.le_radical hK
  rw [hK']
  exact hFt t ht

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

universe u v w

namespace GenericFreeness

theorem isGenericallyFree_of_primes {A : Type u} [CommRing A] [IsDomain A] {R : Type u} [CommRing R]
    [IsNoetherianRing R] [Algebra A R] (hq : ∀ p : PrimeSpectrum R, IsGenericallyFree A (R ⧸ p.asIdeal))
    (M : Type w) [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower A R M] [Module.Finite R M] :
    IsGenericallyFree A M := by
  refine IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime R (M := M) inferInstance
    (motive := fun N _ _ _ ↦ ∀ (_ : Module A N) (_ : IsScalarTower A R N), IsGenericallyFree A N)
    ?_ ?_ ?_ ‹Module A M› ‹IsScalarTower A R M›
  · intro N _ _ _ _ _ _
    exact ⟨1, one_ne_zero, inferInstance⟩
  · intro N _ _ _ p e _ _
    exact (hq p).of_linearEquiv (e.restrictScalars A).symm
  · intro N₁ _ _ _ N₂ _ _ _ N₃ _ _ _ f g hf hg hfg h₁ h₃ _ _
    letI : Module A N₁ := Module.compHom N₁ (algebraMap A R)
    letI : Module A N₃ := Module.compHom N₃ (algebraMap A R)
    have t₁ : IsScalarTower A R N₁ := ⟨fun a r n ↦ by
      show (a • r) • n = algebraMap A R a • r • n
      rw [Algebra.smul_def, mul_smul]⟩
    have t₃ : IsScalarTower A R N₃ := ⟨fun a r n ↦ by
      show (a • r) • n = algebraMap A R a • r • n
      rw [Algebra.smul_def, mul_smul]⟩
    exact IsGenericallyFree.of_exact (f.restrictScalars A) (g.restrictScalars A) hf hg hfg
      (h₁ inferInstance t₁) (h₃ inferInstance t₃)

theorem isGenericallyFree_of_comap_ne_bot {A : Type u} [CommRing A] {σ : Type*} (q : Ideal (MvPolynomial σ A))
    (h : q.comap (C : A →+* MvPolynomial σ A) ≠ ⊥) : IsGenericallyFree A (MvPolynomial σ A ⧸ q) := by
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  refine isGenericallyFree_of_smul_eq_zero a ha0 fun d ↦ ?_
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective d
  have e : a • Ideal.Quotient.mk q x = Ideal.Quotient.mk q (a • x) :=
    (map_smul (Ideal.Quotient.mkₐ A q) a x).symm
  rw [e, Ideal.Quotient.eq_zero_iff_mem, smul_eq_C_mul]
  exact q.mul_mem_right x ha

theorem isGenericallyFree_quotient_bot {A : Type u} [CommRing A] [IsDomain A] (σ : Type*) :
    IsGenericallyFree A (MvPolynomial σ A ⧸ (⊥ : Ideal (MvPolynomial σ A))) :=
  (isGenericallyFree_of_free (M := MvPolynomial σ A)).of_linearEquiv
    (AlgEquiv.quotientBot A (MvPolynomial σ A)).toLinearEquiv.symm

theorem isGenericallyFree_quotient (hNN : GenericNoetherNormalisation.Statement.{u}) (n : ℕ) :
    ∀ (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A] (q : Ideal (MvPolynomial (Fin n) A)),
      q.IsPrime → IsGenericallyFree A (MvPolynomial (Fin n) A ⧸ q) := by
  set_option synthInstance.maxHeartbeats 400000 in
  induction n with
  | zero =>
    intro A _ _ _ q _
    by_cases hc : q.comap (C : A →+* MvPolynomial (Fin 0) A) = ⊥
    · have hq : q = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        have hx' : C (AddMonoidAlgebra.coeff x 0) ∈ q := by rwa [← eq_C_of_isEmpty x]
        have : AddMonoidAlgebra.coeff x 0 ∈ q.comap (C : A →+* MvPolynomial (Fin 0) A) := hx'
        rw [hc, Ideal.mem_bot] at this
        rw [Ideal.mem_bot, eq_C_of_isEmpty x, this, map_zero]
      subst hq
      exact isGenericallyFree_quotient_bot _
    · exact isGenericallyFree_of_comap_ne_bot q hc
  | succ n ih =>
    intro A _ _ _ q hqp
    by_cases hc : q.comap (C : A →+* MvPolynomial (Fin (n + 1)) A) = ⊥
    · by_cases hq : q = ⊥
      · subst hq
        exact isGenericallyFree_quotient_bot _
      obtain ⟨a, ha, z, s, hspan⟩ := hNN A n q hqp hq hc
      let D := MvPolynomial (Fin (n + 1)) A ⧸ q
      let Rn := MvPolynomial (Fin n) A
      letI : Algebra Rn D := (aeval z : Rn →ₐ[A] D).toRingHom.toAlgebra
      have : IsScalarTower A Rn D := IsScalarTower.of_algebraMap_eq (R := A) (S := Rn) (A := D)
        fun x ↦ ((aeval z : Rn →ₐ[A] D).commutes x).symm
      let N : Submodule Rn D := Submodule.span Rn (s : Set D)
      have hN : IsGenericallyFree A N :=
        isGenericallyFree_of_primes (R := Rn) (fun p ↦ ih A p.asIdeal p.isPrime) N
      refine hN.of_injective (N.subtype.restrictScalars A) Subtype.val_injective a ha fun d ↦ ?_
      obtain ⟨k, c, hk⟩ := hspan d
      refine ⟨k, ⟨⟨a ^ k • d, ?_⟩, rfl⟩⟩
      rw [hk]
      exact Submodule.sum_mem _ fun t ht ↦ Submodule.smul_mem _ (c t) (Submodule.subset_span ht)
    · exact isGenericallyFree_of_comap_ne_bot q hc

end GenericFreeness

theorem GenericFreeness.proof (hNN : GenericNoetherNormalisation.Statement.{u}) :
    GenericFreeness.Statement.{u, v, w} := by
  intro A _ _ _ B _ _ _ M _ _ _ _ _
  obtain ⟨n, g, hg⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp ‹Algebra.FiniteType A B›
  letI : Algebra (MvPolynomial (Fin n) A) B := g.toRingHom.toAlgebra
  letI : Module (MvPolynomial (Fin n) A) M := Module.compHom M (algebraMap (MvPolynomial (Fin n) A) B)
  have : IsScalarTower (MvPolynomial (Fin n) A) B M := ⟨fun x b m ↦ by
    show (g x * b) • m = g x • b • m
    rw [mul_smul]⟩
  have : IsScalarTower A (MvPolynomial (Fin n) A) M := ⟨fun a x m ↦ by
    show g (a • x) • m = a • g x • m
    rw [map_smul, smul_assoc]⟩
  have : Module.Finite (MvPolynomial (Fin n) A) B := RingHom.Finite.of_surjective g.toRingHom hg
  have : Module.Finite (MvPolynomial (Fin n) A) M := Module.Finite.trans B M
  exact GenericFreeness.isGenericallyFree_of_primes (R := MvPolynomial (Fin n) A)
    (fun p ↦ GenericFreeness.isGenericallyFree_quotient hNN n A p.asIdeal p.isPrime) M

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

def AnalyticGermComponents.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X : Set (σ → ℂ)) (w : σ → ℂ), IsAnalyticNear X w → w ∈ X →
    ∃ (n : ℕ) (Y : Fin n → Set (σ → ℂ)), (∀ i, IsAnalyticNear (Y i) w ∧ GermIrreducibleAt (Y i) w) ∧
      ∃ W ∈ 𝓝 w, X ∩ W = (⋃ i, Y i) ∩ W

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

def FibreDiscriminantHolomorphic.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (Y : Set (σ → ℂ)) (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) (D : Set (Fin d → ℂ))
    (N : ℕ) (l : (σ → ℂ) →L[ℂ] ℂ),
    IsOpen D → Set.MapsTo A Y D →
    (∀ K ⊆ D, IsCompact K → IsCompact {x | x ∈ Y ∧ A x ∈ K}) →
    (∀ x ∈ Y, ∀ V ∈ 𝓝 x, A '' (Y ∩ V) ∈ 𝓝 (A x)) →
    IsGenericCountCover Y A D N →
    AnalyticOnNhd ℂ (fibreDiscr Y A l N) D

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

def FiniteFibreCentredEquation.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X : Set (σ → ℂ)) (w : σ → ℂ) (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)),
    IsAnalyticNear X w → (∃ W ∈ 𝓝 w, ∀ x ∈ X ∩ W, A x = A w → x = w) →
    ∀ g : (σ → ℂ) → ℂ, AnalyticAt ℂ g w →
      ∃ (n : ℕ) (b : Fin n → (Fin d → ℂ) → ℂ), (∀ j, AnalyticAt ℂ (b j) (A w)) ∧
        (∀ T : ℂ, T ^ n + ∑ j, b j (A w) * T ^ (j : ℕ) = (T - g w) ^ n) ∧
        ∀ᶠ z in 𝓝 w, z ∈ X → g z ^ n + ∑ j, b j (A z) * g z ^ (j : ℕ) = 0

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end
