module

public import Mathlib.Basic.NNReal.Defs
public import Mathlib.FieldTheory.Fixed
public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.NumberTheory.FunctionField
public import Mathlib.RingTheory.ClassGroup.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.NumberTheory.BernoulliPolynomials
public import Mathlib.NumberTheory.DirichletCharacter.Basic
public import Mathlib.NumberTheory.NumberField.AdeleRing
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace GlobalTheory.AlmostEt

open scoped NNReal

variable {L : Type*} [Field L]

def ApproxRoot (p : ℕ) (v : Valuation L ℝ≥0) (F : Subfield L) : Prop :=
  ∃ θ : ℝ≥0, θ < 1 ∧ ∀ u ∈ F, ∃ w ∈ F, v (u - w ^ p) ≤ θ * v u

variable {G : Type*} [Group G] [MulSemiringAction G L]

abbrev Fix (L : Type*) [Field L] {G : Type*} [Group G] [MulSemiringAction G L] (N : Subgroup G) :
    Subfield L := FixedPoints.subfield N L

def Moves (v : Valuation L ℝ≥0) (F : Subfield L) (σ : G) : Prop :=
  ∀ r : ℝ≥0, r < 1 → ∃ x ∈ F, v x ≤ 1 ∧ r < v (σ • x - x)

structure IsSep (v : Valuation L ℝ≥0) (N : Subgroup G) {n : ℕ} (a b : Fin n → L) (c : L) : Prop where
  a_mem : ∀ i, a i ∈ Fix L N
  b_mem : ∀ i, b i ∈ Fix L N
  c_mem : c ∈ Fix L N
  a_le : ∀ i, v (a i) ≤ 1
  b_le : ∀ i, v (b i) ≤ 1
  c_le : v c ≤ 1
  sum_in : ∀ σ : G, σ ∈ N → ∑ i, a i * σ • b i = c
  sum_out : ∀ σ : G, σ ∉ N → ∑ i, a i * σ • b i = 0

def AlmostSep (v : Valuation L ℝ≥0) (N : Subgroup G) : Prop :=
  ∀ r : ℝ≥0, r < 1 → ∃ (n : ℕ) (a b : Fin n → L) (c : L), IsSep v N a b c ∧ r < v c

def cosetTrace (N : Subgroup G) [Fintype (G ⧸ N)] (x : L) : L := ∑ q : G ⧸ N, q.out • x

end GlobalTheory.AlmostEt
end
end

section

noncomputable section

open scoped Matrix

namespace GlobalTheory.KA

variable {Γ : Type*} [Group Γ] {R : Type*} [CommRing R]

def ShCoc {X : Type*} [Monoid X] (ρ : Γ → Matrix (Fin 2) (Fin 2) R) (κ : Γ →* X) (Y : Γ → X → Fin 2 → R) : Prop :=
  ∀ s t x, Y (s * t) x = Y s x + ρ s *ᵥ Y t (x * κ s)

def push {X X' : Type*} [Fintype X'] [DecidableEq X] {M : Type*} [AddCommMonoid M] (π : X' → X) (Y : Γ → X' → M) :
    Γ → X → M :=
  fun s x => ∑ x' ∈ Finset.univ.filter (fun x' => π x' = x), Y s x'

def spec {X : Type*} [Fintype X] (η : X → R) (Y : Γ → X → Fin 2 → R) : Γ → Fin 2 → R :=
  fun s => ∑ x, η x • Y s x

end GlobalTheory.KA

end
end

section

noncomputable section

open Polynomial

namespace GlobalTheory.NeedB

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]

def kum {N : ℕ} (ζ θ : Ω) (g : Ω ≃ₐ[K] Ω) : ZMod N :=
  open Classical in
  if h : ∃ i : ZMod N, g θ = ζ ^ i.val * θ then h.choose else 0

def Inert (B : ValuationSubring Ω) (g : Ω ≃ₐ[K] Ω) : Prop :=
  ∀ x : Ω, B.valuation x ≤ 1 → B.valuation (g x - x) < 1

def Over (R : Subring K) (B : ValuationSubring Ω) : Prop :=
  ∀ x ∈ R, algebraMap K Ω x ∈ B

def RY (R : Subring K) : Subgroup (Ω ≃ₐ[K] Ω) :=
  (Subgroup.normalClosure {g | ∃ B : ValuationSubring Ω, Over R B ∧ Inert B g}).topologicalClosure

def ThmA : Prop :=
  ∀ (k K Ω : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k[X] K] [Algebra (RatFunc k) K]
    [IsScalarTower k[X] (RatFunc k) K] [FiniteDimensional (RatFunc k) K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (N : ℕ) (ζ : Ω), 0 < N → IsPrimitiveRoot ζ N →
    ∀ (a b : K) (α β : Ω), a ≠ 0 → b ≠ 0 →
      a ∈ FunctionField.ringOfIntegers k K → a⁻¹ ∈ FunctionField.ringOfIntegers k K →
      b ∈ FunctionField.ringOfIntegers k K → b⁻¹ ∈ FunctionField.ringOfIntegers k K →
      α ^ N = algebraMap K Ω a → β ^ N = algebraMap K Ω b →
      (∀ g h : Ω ≃ₐ[K] Ω, kum (N := N) ζ α (g * h) = kum ζ α g + kum ζ α h) ∧
      IsLocallyConstant (kum (K := K) (N := N) ζ α) ∧
      (∀ g h : Ω ≃ₐ[K] Ω, kum (N := N) ζ β (g * h) = kum ζ β g + kum ζ β h) ∧
      IsLocallyConstant (kum (K := K) (N := N) ζ β) ∧
      ∃ η : (Ω ≃ₐ[K] Ω) → ZMod N, IsLocallyConstant η ∧
        (∀ g h, kum ζ α g * kum ζ β h = η h - η (g * h) + η g) ∧
        ∀ B : ValuationSubring Ω, Over (FunctionField.ringOfIntegers k K).toSubring B → ∀ g, Inert B g → η g = 0

def IsFirstChernClassOfLineBundle (K : Type*) [Field K] : Prop :=
  ∀ (n d : ℕ) (f : MvPolynomial (Fin n) K), f.IsHomogeneous d → 0 < d → d < n →
    ∃ x : Fin n → K, x ≠ 0 ∧ MvPolynomial.eval x f = 0

def Tsen : Prop :=
  ∀ (k K : Type) [Field k] [IsAlgClosed k] [Field K] [Algebra (RatFunc k) K] [FiniteDimensional (RatFunc k) K], IsFirstChernClassOfLineBundle K

def ClDiv : Prop :=
  ∀ (k K : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k[X] K] [Algebra (RatFunc k) K]
    [IsScalarTower k[X] (RatFunc k) K] [FiniteDimensional (RatFunc k) K] (N : ℕ), 0 < N →
    ∀ c : ClassGroup (FunctionField.ringOfIntegers k K), ∃ d, c = d ^ N

theorem kum_choose_spec {N : ℕ} {ζ θ : Ω} {g : Ω ≃ₐ[K] Ω} (h : ∃ i : ZMod N, g θ = ζ ^ i.val * θ) :
    g θ = ζ ^ (kum (N := N) ζ θ g).val * θ := by
  classical
  unfold kum
  rw [dite_eq_left h]
  exact h.choose_spec

theorem kum_eq_of {N : ℕ} [NeZero N] {ζ θ : Ω} (hζ : IsPrimitiveRoot ζ N) (hθ : θ ≠ 0) {g : Ω ≃ₐ[K] Ω}
    (i : ZMod N) (hi : g θ = ζ ^ i.val * θ) : kum (N := N) ζ θ g = i := by
  have hs := kum_choose_spec (N := N) ⟨i, hi⟩
  rw [hi] at hs
  have h2 : ζ ^ i.val = ζ ^ (kum (N := N) ζ θ g).val := mul_right_cancel₀ hθ hs
  exact (ZMod.val_injective N (hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h2)).symm

theorem kum_one {N : ℕ} [NeZero N] {ζ θ : Ω} (hζ : IsPrimitiveRoot ζ N) (hθ : θ ≠ 0) :
    kum (N := N) ζ θ (1 : Ω ≃ₐ[K] Ω) = 0 :=
  kum_eq_of hζ hθ 0 (by simp)

theorem inert_one (B : ValuationSubring Ω) : Inert B (1 : Ω ≃ₐ[K] Ω) := by
  intro x _
  simp

theorem mem_RY_of_inert (R : Subring K) {B : ValuationSubring Ω} (hB : Over R B) {g : Ω ≃ₐ[K] Ω} (hg : Inert B g) :
    g ∈ RY R :=
  Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure ⟨B, hB, hg⟩)

theorem over_top (R : Subring K) : Over R (⊤ : ValuationSubring Ω) := fun _ _ => trivial

end GlobalTheory.NeedB
end
end

section

noncomputable section

open Finset
open scoped Classical

namespace GlobalTheory.KummerEisensteinGalois

variable {K : Type*} [Field K] [CharZero K]

def frc (M : ℕ) (a : ℤ) : ℚ := ((a % (M : ℤ) : ℤ) : ℚ) / M

def const0 (j M : ℕ) (ζ : K) (a₁ a₂ : ℤ) : K :=
  if j = 1 then
    (if (M : ℤ) ∣ a₁ then (1 / 2 : K) * (1 + ζ ^ a₂) / (1 - ζ ^ a₂) else ((1 / 2 - frc M a₁ : ℚ) : K))
  else -(((Polynomial.bernoulli j).eval (frc M a₁) / j : ℚ) : K)

def coefPos (j M : ℕ) (ζ : K) (a₁ a₂ : ℤ) (n : ℕ) : K :=
  ∑ d ∈ n.divisors,
    ((if ((n / d : ℕ) : ℤ) ≡ a₁ [ZMOD M] then (((n / d : ℕ) : K) / M) ^ (j - 1) * ζ ^ (a₂ * d) else 0) -
     (if (-((n / d : ℕ) : ℤ)) ≡ a₁ [ZMOD M] then (-(((n / d : ℕ) : K) / M)) ^ (j - 1) * ζ ^ (-(a₂ * d)) else 0))

def eisF (j M : ℕ) (ζ : K) (a₁ a₂ : ℤ) (n : ℕ) : K :=
  if n = 0 then const0 j M ζ a₁ a₂ else coefPos j M ζ a₁ a₂ n

def smF (c : ℤ) (j M : ℕ) (ζ : K) (a₁ a₂ : ℤ) (n : ℕ) : K :=
  (c : K) ^ 2 * eisF j M ζ a₁ a₂ n - (c : K) ^ ((2 : ℤ) - j) * eisF j M ζ (c * a₁) (c * a₂) n

def cmul (f g : ℕ → K) (n : ℕ) : K := ∑ i ∈ range (n + 1), f i * g (n - i)

def up (p : ℕ) (f : ℕ → K) (n : ℕ) : K := f (p * n)

def vp (p : ℕ) (f : ℕ → K) (n : ℕ) : K := if p ∣ n then f (n / p) else 0

def rowIdx (N p n : ℕ) (γ : GL (Fin 2) (ZMod (p ^ n))) (i : Fin 2) (y : ℤ) : ℤ × ℤ :=
  ((N : ℤ) * ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) i 0).val,
   (N : ℤ) * ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) i 1).val + (p : ℤ) ^ n * y)

def unitSet (p n : ℕ) [NeZero p] : Finset (GL (Fin 2) (ZMod (p ^ n))) :=
  Finset.univ.filter fun γ => ¬ (p : ℕ) ∣ ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 0 0).val ∧
    ¬ (p : ℕ) ∣ ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 1 0).val

def gaussS (p m : ℕ) [NeZero p] (ψ : DirichletCharacter K (p ^ m)) (ζm : K) : K :=
  ∑ a : ZMod (p ^ m), ψ a * ζm ^ a.val

def ffPos (N p m k : ℕ) (ψ : DirichletCharacter K (p ^ m)) (x t : ℤ) (ζ : K) (full : Bool) (n : ℕ) : K :=
  ∑ d ∈ n.divisors, if (full || ¬ p ∣ d) && ¬ p ∣ (n / d) then
    (ψ ((n / d : ℕ) : ZMod (p ^ m)) * ((n / d : ℕ) : K) ^ (k - 2) * (ζ ^ (p ^ m)) ^ (x * t * d) -
     ψ (-((n / d : ℕ) : ZMod (p ^ m))) * (-((n / d : ℕ) : K)) ^ (k - 2) * (ζ ^ (p ^ m)) ^ (-(x * t * d)))
    else 0

def eePos (N p m : ℕ) (ψ : DirichletCharacter K (p ^ m)) (t : ℤ) (ζ : K) (full : Bool) (n : ℕ) : K :=
  ∑ d ∈ n.divisors, if (full || ¬ p ∣ (n / d)) && ¬ p ∣ d then
    (ψ⁻¹ ((d : ℕ) : ZMod (p ^ m)) * (ζ ^ (p ^ m)) ^ (t * d) -
     ψ⁻¹ (-((d : ℕ) : ZMod (p ^ m))) * (ζ ^ (p ^ m)) ^ (-(t * d)))
    else 0

def toQ (M : ℕ) (f : ℕ → K) (n : ℕ) : K := f (M * n)

def Integral (M : ℕ) (f : ℕ → K) : Prop := ∀ n, ¬ M ∣ n → f n = 0

end GlobalTheory.KummerEisensteinGalois
end
end

section

noncomputable section

open NumberField IsDedekindDomain

namespace GlobalTheory.Mem.Chr

variable (L : Type) [Field L] [NumberField L]

abbrev Ideles : Type := (AdeleRing (𝓞 L) L)ˣ

def diagUnits : Lˣ →* Ideles L := Units.map (algebraMap L (AdeleRing (𝓞 L) L)).toMonoidHom


open Classical in
def finSingle (v : HeightOneSpectrum (𝓞 L)) : v.adicCompletion L →* FiniteAdeleRing (𝓞 L) L := by
  classical
  exact {
    toFun x := ⟨Pi.mulSingle v x, by
      refine Filter.eventually_cofinite.mpr ((Set.finite_singleton v).subset ?_)
      intro w hw
      by_contra h
      apply hw
      have h' : w ≠ v := h
      rw [Pi.mulSingle_eq_of_ne h']
      exact one_mem _⟩
    map_one' := by
      apply Subtype.ext
      exact Pi.mulSingle_one v
    map_mul' x y := by
      apply Subtype.ext
      exact Pi.mulSingle_mul v x y }

def localIdele (v : HeightOneSpectrum (𝓞 L)) : (v.adicCompletion L)ˣ →* Ideles L :=
  Units.map ((MonoidHom.inr (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)).comp (finSingle L v))


open Classical in
def infIdele (w : InfinitePlace L) : (w.Completion)ˣ →* Ideles L := by
  classical
  exact Units.map ((MonoidHom.inl (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)).comp
    (MonoidHom.mulSingle (fun w : InfinitePlace L => w.Completion) w))

theorem valued_algebraMap_eq_one (v : HeightOneSpectrum (𝓞 L)) (x : 𝓞 L) (hx : x ∉ v.asIdeal) :
    Valued.v (algebraMap L (v.adicCompletion L) (algebraMap (𝓞 L) L x)) = 1 := by
  show Valued.v ((algebraMap (𝓞 L) L x : L) : v.adicCompletion L) = _
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_of_algebraMap]
  exact (HeightOneSpectrum.intValuation_eq_one_iff).mpr hx

end GlobalTheory.Mem.Chr
end
end
