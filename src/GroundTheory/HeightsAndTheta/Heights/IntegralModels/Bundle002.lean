module

public import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Bundle001
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.Tactic.Linter.HaveILetI
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle001
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.RingTheory.HopkinsLevitzki
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ModulesTensor
public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.RingTheory.Ideal.Basic
public import Mathlib.RingTheory.Ideal.BigOperators
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

theorem KrullAkizukiQuotientLength.proof (h : TorsionFreeQuotientLength.Statement) :
    KrullAkizukiQuotientLength.Statement := by
  intro R _ _ _ hdim K _ _ _ L _ _ _ _ _ S b hb

  have hinj : Function.Injective (algebraMap R S) := by
    intro x y hxy
    have h1 : algebraMap R L x = algebraMap R L y := by
      simpa using congrArg (fun s : S => (s : L)) hxy
    rw [IsScalarTower.algebraMap_apply R K L, IsScalarTower.algebraMap_apply R K L] at h1
    exact IsFractionRing.injective R K ((algebraMap K L).injective h1)
  have : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective R S).mpr hinj
  have : Module.IsTorsionFree R S := inferInstance

  have hrankL : Module.rank R L = Module.rank K L :=
    (IsLocalization.rank_eq K (nonZeroDivisors R) le_rfl).symm
  have hlt : Module.rank R S < Cardinal.aleph0 :=
    lt_of_le_of_lt (by rw [← hrankL]; exact Submodule.rank_le (Subalgebra.toSubmodule S))
      (Module.rank_lt_aleph0 K L)
  obtain ⟨r, hr⟩ := Cardinal.lt_aleph0.mp hlt

  have hdim0 : Ring.KrullDimLE 0 (R ⧸ Ideal.span {b}) := by
    rw [Ring.krullDimLE_iff]
    have h2 := ringKrullDim_quotient_succ_le_of_nonZeroDivisor (mem_nonZeroDivisors_of_ne_zero hb)
    rw [hdim] at h2
    generalize ringKrullDim (R ⧸ Ideal.span {b}) = d at h2 ⊢
    cases d with
    | bot => exact bot_le
    | coe n =>
      have h3 : n + 1 ≤ 1 := by exact_mod_cast h2
      induction n using ENat.recTopCoe with
      | top => simp at h3
      | coe k =>
        have hk : k + 1 ≤ 1 := by exact_mod_cast h3
        obtain rfl : k = 0 := by omega
        simp
  have : IsArtinianRing (R ⧸ Ideal.span {b}) :=
    IsNoetherianRing.isArtinianRing_of_krullDimLE_zero
  have hRlen : Module.length R (R ⧸ Ideal.span {b}) ≠ ⊤ := by
    rw [Module.length_ne_top_iff, isFiniteLength_iff_isNoetherian_isArtinian]
    exact ⟨inferInstance, isArtinian_of_surjective_algebraMap
      (Ideal.Quotient.mk_surjective (I := Ideal.span {b}))⟩

  have hle := h R hdim S r hr b hb
  have hfin : IsFiniteLength R (S ⧸ (Ideal.span {b} • ⊤ : Submodule R S)) :=
    Module.length_ne_top_iff.mp
      (ne_top_of_le_ne_top (WithTop.mul_ne_top (ENat.natCast_ne_top r) hRlen) hle)

  have heq : (Ideal.span {b} • ⊤ : Submodule R S) =
      (Ideal.span {algebraMap R S b}).restrictScalars R := by
    ext x
    simp only [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists,
      Submodule.mem_top, true_and, Submodule.restrictScalars_mem, Ideal.mem_span_singleton',
      Algebra.smul_def, mul_comm]
  rw [heq] at hfin
  exact hfin.of_surjective (f := (Submodule.Quotient.restrictScalarsEquiv R _).toLinearMap)
    (Submodule.Quotient.restrictScalarsEquiv R _).surjective

end GroundTheory.Heights₂.Heights.Model
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model

open CategoryTheory Opposite AlgebraicGeometry Limits TopologicalSpace MonoidalCategory
open GroundTheory.Arith.SchemeCoh

noncomputable section

universe u

section VectorBundle

variable {X : Scheme.{u}}

end VectorBundle

section OverZ

def toSpecZ (X : Scheme.{0}) : X ⟶ Spec (.of ℤ) := specZIsTerminal.from X

theorem specZ_hom_ext {X : Scheme.{0}} (f g : X ⟶ Spec (.of ℤ)) : f = g :=
  specZIsTerminal.hom_ext f g

def IsFiniteTypeOverZ (X : Scheme.{0}) : Prop :=
  LocallyOfFiniteType (toSpecZ X) ∧ QuasiCompact (toSpecZ X)

end OverZ

section Pullbacks

variable {A B C D : Scheme.{u}}

end Pullbacks

section Generic

variable {X : Scheme.{u}} [IrreducibleSpace X]

end Generic

section Opens

end Opens

section Generic

variable {X : Scheme.{u}} [IrreducibleSpace X]

end Generic

section Unit

variable {X Y : Scheme.{u}}


end Unit

section SchemeStatements

end SchemeStatements

section AlgebraStatements

def Dominates (A : Type*) {K : Type*} [CommRing A] [IsLocalRing A] [Field K] [Algebra A K]
    (V : Subring K) : Prop :=
  ∃ h : ∀ a : A, algebraMap A K a ∈ V,
    ∀ a : A, (⟨_, h a⟩ : V) ∈ nonunits V ↔ a ∈ IsLocalRing.maximalIdeal A

def DominatingDVR.Statement : Prop :=
  (∀ (A K : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [Field K]
    [Algebra A K] [IsFractionRing A K], ¬ IsField A →
      ∃ V : Subring K, IsDiscreteValuationRing V ∧ Dominates A V) ∧
  (∀ (Z : Scheme.{0}) [IsIntegral Z] [IsLocallyNoetherian Z] (z : Z), z ≠ genericPoint Z →
      ∃ V : Subring Z.functionField, IsDiscreteValuationRing V ∧ Dominates (Z.presheaf.stalk z) V)

def blowUpChart (A K : Type*) [CommRing A] [Field K] [Algebra A K] {n : ℕ} (x : Fin n → A)
    (i : Fin n) : Subalgebra A K :=
  Algebra.adjoin A (Set.range fun j => algebraMap A K (x j) / algebraMap A K (x i))

def BlowUpChart.Statement : Prop :=
  ∀ (A K : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [Field K]
    [Algebra A K] [IsFractionRing A K] (n : ℕ) (x : Fin n → A),
    Ideal.span (Set.range x) = IsLocalRing.maximalIdeal A → (∃ i, x i ≠ 0) →
    ∃ i, x i ≠ 0 ∧ ¬ IsUnit (algebraMap A (blowUpChart A K x i) (x i)) ∧
      ∀ P : Ideal (blowUpChart A K x i), P.IsPrime → algebraMap A _ (x i) ∈ P →
        P.comap (algebraMap A (blowUpChart A K x i)) = IsLocalRing.maximalIdeal A

def KrullAkizuki.Statement : Prop :=
  ∀ (R K L : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra R L]
    [IsScalarTower R K L], ringKrullDim R = 1 →
    (∀ S : Subalgebra R L, IsNoetherianRing S ∧ ringKrullDim S ≤ 1) ∧
      IsDedekindDomain (integralClosure R K)

def FiniteIntegralClosure.Statement : Prop :=
  (∀ (A K L : Type) [CommRing A] [IsDomain A] [Algebra.FiniteType ℤ A] [Field K] [Algebra A K]
    [IsFractionRing A K] [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra A L]
    [IsScalarTower A K L], Module.Finite A (integralClosure A L)) ∧
  (∀ (X : Scheme.{0}) [IsIntegral X], IsFiniteTypeOverZ X →
    ∀ (L : Type) [Field L] [Algebra X.functionField L] [FiniteDimensional X.functionField L]
      (U : X.Opens), IsAffineOpen U → ∀ hU : Nonempty U,
      letI : Algebra Γ(X, U) L :=
        ((algebraMap X.functionField L).comp (@algebraMap Γ(X, U) X.functionField _ _ (by
          haveI := hU; infer_instance))).toAlgebra
      Module.Finite Γ(X, U) (integralClosure Γ(X, U) L))

end AlgebraStatements

section NumberStatements


def MertensUpper.Statement : Prop :=
  ∃ C : ℝ, ∀ B : ℝ, 2 ≤ B →
    ∑ p ∈ Finset.filter Nat.Prime (Finset.range (⌊B⌋₊ + 1)), Real.log p / p ≤ Real.log B + C

def cp (p : ℕ) : ℝ := if p = 2 then 2 else 1 / ((p : ℝ) - 1)

def SumCp.Statement : Prop :=
  ∀ d : ℤ, d ≠ 0 → ∃ C : ℝ, ∀ B : ℝ, 2 ≤ B → ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime ∧ (p : ℝ) ≤ B) →
    ∑ p ∈ S, (cp p + 2 * (padicValInt p d : ℝ)) * Real.log p ≤ C * Real.log B

end NumberStatements

section Inhabitants


end Inhabitants

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open ReciprocityTheory.ChartRestriction.G.Geo

section Sat

variable {Ω : Type*} [Field Ω] {E : Type*} [AddCommGroup E] [Module Ω E]
variable {S : Type*} [SetLike S Ω] [SubringClass S Ω]

theorem exists_sum_mul_pow_eq_one (A : S) {k : ℕ} (f c : Fin k → Ω) (hf : ∀ l, f l ∈ A)
    (hc : ∀ l, c l ∈ A) (h1 : ∑ l, c l * f l = 1) (N : ℕ) :
    ∃ d : Fin k → Ω, (∀ l, d l ∈ A) ∧ ∑ l, d l * f l ^ N = 1 := by
  let f' : Fin k → A := fun l => ⟨f l, hf l⟩
  have hspan : Ideal.span (Set.range f') = ⊤ := by
    rw [Ideal.eq_top_iff_one]
    have : (1 : A) = ∑ l, (⟨c l, hc l⟩ : A) * f' l := Subtype.ext (by simp [f', h1])
    rw [this]
    exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨l, rfl⟩)
  have hpow := Ideal.span_pow_eq_top _ hspan N
  rw [← Set.range_comp] at hpow
  have h1' : (1 : A) ∈ Ideal.span (Set.range ((fun y => y ^ N) ∘ f')) := by
    rw [hpow]; exact Submodule.mem_top
  obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun A).1 h1'
  refine ⟨fun l => d l, fun l => (d l).2, ?_⟩
  have := congrArg Subtype.val hd
  simpa [f'] using this

end Sat

section Gens

variable {Ω : Type*} [Field Ω] {E : Type*} [AddCommGroup E] [Module Ω E]
variable {R : Type*} [CommRing R] [Algebra R Ω] {τ : Type*} {x : τ → Ω} {r : ℕ}

theorem chartBundle_pow_smul_mem (B : ChartBundle R x r E) {i : τ} {a : Ω}
    (ha : a ∈ chartRing R x i) (m : ℕ) {e : E} (he : e ∈ B.lat i) : a ^ m • e ∈ B.lat i :=
  B.stable i _ (pow_mem ha m) e he

theorem chartBundle_exists_gens (B : ChartBundle R x r E) {i : τ} (hi : x i ≠ 0) :
    ∃ (k : ℕ) (G : Fin k × Fin r → E), (∀ j, G j ∈ B.lat i) ∧
      ∀ e ∈ B.lat i, ∃ β : Fin k × Fin r → Ω, (∀ j, β j ∈ chartRing R x i) ∧
        e = ∑ j, β j • G j := by
  classical
  obtain ⟨k, f, c, hf, hc, hsum, hb⟩ := B.frame i hi
  choose b _ _ hiff using hb
  have hbsat : ∀ l q, ∃ n : ℕ, f l ^ n • b l q ∈ B.lat i := by
    intro l q
    refine (hiff l (b l q)).2 ⟨Pi.single q 1, fun q' => ⟨0, ?_⟩, by simp [Pi.single_apply]⟩
    rw [pow_zero, one_mul]
    by_cases h : q' = q
    · subst h; simp only [Pi.single_eq_same]; exact one_mem _
    · rw [Pi.single_eq_of_ne h]; exact zero_mem _
  choose n hn using hbsat
  set n₀ := Finset.univ.sup fun lq : Fin k × Fin r => n lq.1 lq.2 with hn₀
  have hle : ∀ l q, n l q ≤ n₀ := fun l q =>
    Finset.le_sup (f := fun lq : Fin k × Fin r => n lq.1 lq.2) (Finset.mem_univ (l, q))
  refine ⟨k, fun lq => f lq.1 ^ n₀ • b lq.1 lq.2, fun lq => ?_, fun e he => ?_⟩
  · have : f lq.1 ^ n₀ • b lq.1 lq.2 = f lq.1 ^ (n₀ - n lq.1 lq.2) • f lq.1 ^ n lq.1 lq.2 • b lq.1 lq.2 := by
      rw [smul_smul, pow_sub_mul_pow _ (hle _ _)]
    show f lq.1 ^ n₀ • b lq.1 lq.2 ∈ B.lat i
    rw [this]
    exact chartBundle_pow_smul_mem B (hf _) _ (hn _ _)
  · have hco : ∀ l, ∃ a : Fin r → Ω, (∀ q, ∃ n : ℕ, f l ^ n * a q ∈ chartRing R x i) ∧
        e = ∑ q, a q • b l q := fun l => (hiff l e).1 ⟨0, by simpa using he⟩
    choose a ha he' using hco
    choose m hm using ha
    set M := Finset.univ.sup fun lq : Fin k × Fin r => m lq.1 lq.2 with hM
    have hleM : ∀ l q, m l q ≤ M := fun l q =>
      Finset.le_sup (f := fun lq : Fin k × Fin r => m lq.1 lq.2) (Finset.mem_univ (l, q))
    have hfa : ∀ l q, f l ^ M * a l q ∈ chartRing R x i := fun l q => by
      rw [← pow_sub_mul_pow _ (hleM l q), mul_assoc]
      exact mul_mem (pow_mem (hf l) _) (hm l q)
    obtain ⟨d, hd, hd1⟩ := exists_sum_mul_pow_eq_one (chartRing R x i) f c hf hc hsum (M + n₀)
    refine ⟨fun lq => d lq.1 * (f lq.1 ^ M * a lq.1 lq.2), fun lq => mul_mem (hd _) (hfa _ _), ?_⟩
    rw [Fintype.sum_prod_type]
    calc e = (∑ l, d l * f l ^ (M + n₀)) • e := by rw [hd1, one_smul]
      _ = ∑ l, d l • (f l ^ (M + n₀) • e) := by
        rw [Finset.sum_smul]; exact Finset.sum_congr rfl fun l _ => by rw [mul_smul]
      _ = ∑ l, ∑ q, (d l * (f l ^ M * a l q)) • f l ^ n₀ • b l q := by
        refine Finset.sum_congr rfl fun l _ => ?_
        conv_lhs => rw [he' l]
        rw [Finset.smul_sum, Finset.smul_sum]
        refine Finset.sum_congr rfl fun q _ => ?_
        simp only [smul_smul]
        congr 1
        ring

end Gens

end GroundTheory.Heights₂.Heights.Model
end
