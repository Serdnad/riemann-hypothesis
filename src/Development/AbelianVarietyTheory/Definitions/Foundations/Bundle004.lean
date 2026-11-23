module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle002
public import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
public import Mathlib.Analysis.CStarAlgebra.Matrix
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.FieldTheory.Galois.Infinite
import Formalism.FormalDegreeBessel.StatementWR
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001

@[expose] public section

section

noncomputable section

open scoped UpperHalfPlane MatrixGroups
open GlobalTheory.QFam GlobalTheory.KZ
open ReciprocityTheory.ChartRestriction.L1 (DD jT)

namespace GlobalTheory.FN

def Lv (E : Subring ℂ) (N w : ℕ) (f : ℍ → ℂ) : Prop :=
  (∀ γ ∈ CongruenceSubgroup.Gamma N, ∀ τ : ℍ, f (γ • τ) = f τ) ∧
    ∀ γ : SL(2, ℤ), QAll (· ∈ E) N fun τ => DD τ ^ w * f (γ • τ)

def InR (E : Subring ℂ) (f : ℍ → ℂ) : Prop := ∃ N w : ℕ, 0 < N ∧ Lv E N w f

def ring (E : Subring ℂ) : Subring (ℍ → ℂ) := Subring.closure {f | InR E f}

def up (f : ℍ → ℂ) : ℂ → ℂ := fun z => f (UpperHalfPlane.ofComplex z)

def germ (f : ℍ → ℂ) : Mero := ((up f : ℂ → ℂ) : Mero)

def cmp (g : GQ) (f : ℍ → ℂ) : ℍ → ℂ := fun τ => up f (mob g τ)

def HS {Ω : Type} [Field Ω] (ε : Ω →+* ℂ) (C : ℝ) (φ : ℂ → ℂ) (h : HahnSeries ℚ Ω) : Prop :=
  ∀ z : ℂ, C < z.im →
    HasSum (fun r : ℚ => ε (h.coeff r) * Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * z)) (φ z)

def Den {Ω : Type} [Field Ω] (h : HahnSeries ℚ Ω) : Prop :=
  ∃ N : ℕ, 0 < N ∧ ∀ r : ℚ, h.coeff r ≠ 0 → ∃ n : ℤ, r = (n : ℚ) / N

def IsExp {Ω : Type} [Field Ω] (ε : Ω →+* ℂ) (f : ℍ → ℂ) (h : HahnSeries ℚ Ω) : Prop :=
  Den h ∧ ∃ C : ℝ, HS ε C (up f) h

def Cong (M : ℕ) (d : ℤ) (γ γ' : SL(2, ℤ)) : Prop :=
  (en γ' 0 0 : ZMod M) = en γ 0 0 ∧ (en γ' 0 1 : ZMod M) = d * en γ 0 1 ∧
    (d : ZMod M) * en γ' 1 0 = en γ 1 0 ∧ (en γ' 1 1 : ZMod M) = en γ 1 1

def IsStd {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (T : Tower Ω ε) : Prop := T.an T.jK = germ jT

structure Frac (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) where

  K : Type
  [fld : Field K]
  [alg : Algebra Ω K]

  io : ring ε.range →+* K
  io_inj : Function.Injective io
  io_surj : ∀ f : K, ∃ a b : ring ε.range, b ≠ 0 ∧ f * io b = io a
  io_c : ∀ (c : Ω) (a : ring ε.range), (a : ℍ → ℂ) = (fun _ => ε c) → io a = algebraMap Ω K c

  exp : K →ₐ[Ω] HahnSeries ℚ Ω
  exp_io : ∀ a : ring ε.range, IsExp ε a (exp (io a))

  sl : GQ → (K ≃ₐ[Ω] K)
  sl_io : ∀ (g : GQ) (a a' : ring ε.range), (a' : ℍ → ℂ) = cmp g a → sl g (io a) = io a'

  gal : (Ω ≃ₐ[ℚ] Ω) → (K ≃+* K)
  gal_exp : ∀ s f r, (exp (gal s f)).coeff r = s ((exp f).coeff r)

  an : K →+* Mero
  an_io : ∀ a : ring ε.range, an (io a) = germ a

attribute [instance] Frac.fld Frac.alg

theorem mem_ring_of_inR {E : Subring ℂ} {f : ℍ → ℂ} (h : InR E f) : f ∈ ring E := Subring.subset_closure h

end GlobalTheory.FN
end
end

section

noncomputable section

open scoped MatrixGroups

namespace GlobalTheory.K4

open GlobalTheory.KZ

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

def lev (X : Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) : Subfield X.K :=
  ⨅ γ ∈ Γ', RingHom.eqLocusField (X.sl (ofSL γ)).toRingEquiv.toRingHom (RingHom.id X.K)

def mdl (X : Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) (S : Subgroup (Ω ≃ₐ[ℚ] Ω)) : Subfield X.K :=
  lev X Γ' ⊓ ⨅ s ∈ S, RingHom.eqLocusField (X.gal s).toRingHom (RingHom.id X.K)

end GlobalTheory.K4
end
end

section

noncomputable section

open Finset ArithmeticFunction NumberField IsDedekindDomain
open scoped nonZeroDivisors

namespace GlobalTheory.Mem.An.Model

theorem mem_rayI_of_coprime {K : Type} [Field K] [NumberField K] (𝔮 : Ideal (𝓞 K)) (J : Ideal (𝓞 K)) :
    J ≠ 0 → J ⊔ 𝔮 = ⊤ → ∀ I : (FractionalIdeal (𝓞 K)⁰ K)ˣ,
      (I : FractionalIdeal (𝓞 K)⁰ K) = (J : FractionalIdeal (𝓞 K)⁰ K) → I ∈ rayI 𝔮 := by
  induction J using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => intro h; exact absurd rfl h
  | h₂ u hu =>
    intro _ _ I hI
    rw [Ideal.isUnit_iff] at hu
    subst hu
    have hI1 : I = 1 := Units.ext (by rw [hI, FractionalIdeal.coeIdeal_top, Units.val_one])
    rw [hI1]
    exact one_mem _
  | h₃ a P ha hP ih =>
    intro _ hcop I hI
    have hP0 : P ≠ 0 := hP.ne_zero
    have hPq : ¬ P ∣ 𝔮 := by
      intro hd
      apply hP.not_isUnit
      rw [Ideal.isUnit_iff, eq_top_iff, ← hcop]
      exact sup_le Ideal.mul_le_left (Ideal.le_of_dvd hd)
    have hacop : a ⊔ 𝔮 = ⊤ := by
      rw [eq_top_iff, ← hcop]
      exact sup_le_sup_right Ideal.mul_le_right _
    have hPf : (P : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := by
      rw [Ne, FractionalIdeal.coeIdeal_eq_zero]; exact hP0
    have haf : (a : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := by
      rw [Ne, FractionalIdeal.coeIdeal_eq_zero]; exact ha
    have hI' : I = Units.mk0 _ hPf * Units.mk0 _ haf := Units.ext (by
      rw [hI, Units.val_mul, Units.val_mk0, Units.val_mk0, FractionalIdeal.coeIdeal_mul])
    have hu : Units.mk0 _ hPf ∈ rayI 𝔮 :=
      Subgroup.subset_closure ⟨⟨P, Ideal.isPrime_of_prime hP, hP0⟩, hPq, rfl⟩
    rw [hI']
    exact Subgroup.mul_mem _ hu (ih ha hacop _ rfl)

end GlobalTheory.Mem.An.Model
end
end

section

noncomputable section

open scoped UpperHalfPlane MatrixGroups

namespace GlobalTheory.KZ

def sgC (c : ℕ) (x : Fin 2 → ℚ) (z : ℂ) : ℂ := GlobalTheory.Sieg.sg c x (UpperHalfPlane.ofComplex z)


open scoped Classical in
open Classical in
def siegel {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (T : Tower Ω ε) (c : ℕ) (x : Fin 2 → ℚ) : T.K :=
  if h : ∃ f : T.K, T.an f = ((sgC c x : ℂ → ℂ) : Mero) then h.choose else 0

end GlobalTheory.KZ
end
end

section

noncomputable section

namespace GlobalTheory.K4

open GlobalTheory.KEdge GlobalTheory.NeedB

variable {F K Ω : Type*} [Field F] [Field K] [Field Ω] [Algebra F K] [Algebra F Ω] [Algebra K Ω] [IsScalarTower F K Ω]

def geo (F K Ω : Type*) [Field F] [Field K] [Field Ω] [Algebra F K] [Algebra F Ω] [Algebra K Ω] [IsScalarTower F K Ω] :
    Subgroup (Ω ≃ₐ[F] Ω) :=
  (IsScalarTower.toAlgHom F K Ω).fieldRange.fixingSubgroup

def IsTopW {N : ℕ} (ζ : Ω) (x y : (Ω ≃ₐ[F] Ω) →* Multiplicative (ZMod N)) (η : (Ω ≃ₐ[F] Ω) → ZMod N) (σ : Ω ≃ₐ[F] Ω) (w : K) :
    Prop :=
  w ≠ 0 ∧ ∃ θ : Ω, θ ^ N = algebraMap K Ω w ∧ ∀ g ∈ geo F K Ω, kum (K := F) (N := N) ζ θ g = edge x y η σ g


open Classical in
def topW {N : ℕ} (ζ : Ω) (x y : (Ω ≃ₐ[F] Ω) →* Multiplicative (ZMod N)) (η : (Ω ≃ₐ[F] Ω) → ZMod N) (σ : Ω ≃ₐ[F] Ω) : K := by
  classical
  exact if h : ∃ w : K, IsTopW ζ x y η σ w then h.choose else 1

namespace TopW

variable {N : ℕ} {ζ : Ω} {x y : (Ω ≃ₐ[F] Ω) →* Multiplicative (ZMod N)} {η : (Ω ≃ₐ[F] Ω) → ZMod N}

theorem mem_geo (g : Ω ≃ₐ[F] Ω) : g ∈ geo F K Ω ↔ ∀ z : K, g (algebraMap K Ω z) = algebraMap K Ω z := by
  unfold geo
  rw [IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro h z
    exact h _ ⟨z, rfl⟩
  · rintro h _ ⟨z, rfl⟩
    exact h z

theorem conj_mem_geo [Normal F K] (σ : Ω ≃ₐ[F] Ω) {h : Ω ≃ₐ[F] Ω} (hh : h ∈ geo F K Ω) : σ * h * σ⁻¹ ∈ geo F K Ω := by
  rw [mem_geo] at hh ⊢
  intro z
  have h1 : σ⁻¹ (algebraMap K Ω z) = algebraMap K Ω ((σ⁻¹).restrictNormal K z) :=
    (AlgEquiv.restrictNormal_commutes σ⁻¹ K z).symm
  rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, h1, hh, ← h1]
  exact σ.apply_symm_apply _

theorem exists_of_fixed [IsGalois K Ω] {z : Ω} (hz : ∀ g ∈ geo F K Ω, g z = z) : ∃ c : K, algebraMap K Ω c = z :=
  (InfiniteGalois.mem_range_algebraMap_iff_fixed (k := K) z).2 fun g =>
    hz (AlgEquiv.restrictScalarsHom F g) ((mem_geo _).2 fun w => g.commutes w)

theorem apply_eq_kum [NeZero N] (hζ : IsPrimitiveRoot ζ N) {θ : Ω} {w : K} (hw0 : w ≠ 0)
    (hw : θ ^ N = algebraMap K Ω w) {g : Ω ≃ₐ[F] Ω} (hg : g ∈ geo F K Ω) :
    g θ = ζ ^ (kum (K := F) (N := N) ζ θ g).val * θ := by
  have hw1 : algebraMap K Ω w ≠ 0 := by simpa using hw0
  have hθ : θ ≠ 0 := by
    rintro rfl
    rw [zero_pow (NeZero.ne N)] at hw
    exact hw1 hw.symm
  have h1 : (g θ / θ) ^ N = 1 := by
    rw [div_pow, ← map_pow, hw, (mem_geo g).1 hg, div_self hw1]
  obtain ⟨i, hi, he⟩ := hζ.eq_pow_of_pow_eq_one h1
  refine kum_choose_spec ⟨(i : ZMod N), ?_⟩
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt hi, he, div_mul_cancel₀ _ hθ]

theorem pow_val_add [NeZero N] (hζ : IsPrimitiveRoot ζ N) (a b : ZMod N) :
    ζ ^ (a + b).val = ζ ^ a.val * ζ ^ b.val := by
  rw [← pow_add, ZMod.val_add]
  conv_rhs => rw [← Nat.mod_add_div (a.val + b.val) N, pow_add, pow_mul, hζ.pow_eq_one, one_pow, mul_one]

theorem pow_val_mul [NeZero N] (hζ : IsPrimitiveRoot ζ N) (a b : ZMod N) :
    ζ ^ (a * b).val = (ζ ^ b.val) ^ a.val := by
  rw [← pow_mul, mul_comm b.val, ZMod.val_mul]
  conv_rhs => rw [← Nat.mod_add_div (a.val * b.val) N, pow_add, pow_mul, hζ.pow_eq_one, one_pow, mul_one]

theorem edge_mul_conj {Γ : Type*} [Group Γ] (x y : Γ →* Multiplicative (ZMod N)) (η : Γ → ZMod N) (σ τ h : Γ) :
    edge x y η (σ * τ) h = edge x y η σ (τ * h * τ⁻¹) + edge x y η τ h := by
  simp only [edge, map_mul, map_inv, toAdd_mul, toAdd_inv, mul_inv_rev]
  have : σ * τ * h * (τ⁻¹ * σ⁻¹) = σ * (τ * h * τ⁻¹) * σ⁻¹ := by group
  rw [this]; ring

theorem edge_inv {Γ : Type*} [Group Γ] (x y : Γ →* Multiplicative (ZMod N)) (η : Γ → ZMod N) (σ h : Γ) :
    edge x y η σ⁻¹ h = η (σ⁻¹ * h * σ) - η h + (x h).toAdd * (y σ).toAdd - (x σ).toAdd * (y h).toAdd := by
  simp only [edge, map_inv, toAdd_inv, inv_inv]
  ring

theorem isTopW_topW_of_exists {σ : Ω ≃ₐ[F] Ω} (h : ∃ w : K, IsTopW ζ x y η σ w) :
    IsTopW ζ x y η σ (topW (K := K) ζ x y η σ) := by
  unfold topW
  rw [dite_eq_left h]
  exact h.choose_spec

theorem topW_ne_zero (σ : Ω ≃ₐ[F] Ω) : topW (K := K) ζ x y η σ ≠ 0 := by
  by_cases h : ∃ w : K, IsTopW ζ x y η σ w
  · exact (isTopW_topW_of_exists h).1
  · unfold topW
    rw [dite_eq_right h]
    exact one_ne_zero

theorem unique [NeZero N] [IsGalois K Ω] (hζ : IsPrimitiveRoot ζ N) {σ : Ω ≃ₐ[F] Ω} {w v : K}
    (hw : IsTopW ζ x y η σ w) (hv : IsTopW ζ x y η σ v) : ∃ c : K, c ≠ 0 ∧ w = v * c ^ N := by
  obtain ⟨hw0, θ, hθ, hθk⟩ := hw
  obtain ⟨hv0, ψ, hψ, hψk⟩ := hv
  have hv1 : algebraMap K Ω v ≠ 0 := by simpa using hv0
  have hz : ζ ≠ 0 := hζ.ne_zero (NeZero.ne N)
  obtain ⟨c, hc⟩ := exists_of_fixed (F := F) (K := K) (z := θ / ψ) fun g hg => by
    rw [map_div₀, apply_eq_kum hζ hw0 hθ hg, apply_eq_kum hζ hv0 hψ hg, hθk g hg, hψk g hg,
      mul_div_mul_left _ _ (pow_ne_zero _ hz)]
  have key : w = v * c ^ N := by
    apply (algebraMap K Ω).injective
    rw [map_mul, map_pow, hc, div_pow, hθ, hψ, mul_div_cancel₀ _ hv1]
  refine ⟨c, ?_, key⟩
  rintro rfl
  rw [zero_pow (NeZero.ne N), mul_zero] at key
  exact hw0 key

end TopW

end GlobalTheory.K4
end
end

section

noncomputable section

open scoped UpperHalfPlane MatrixGroups

namespace GlobalTheory.Sieg

def th (z : ℂ) (τ : ℍ) : ℂ :=
  ee ((τ : ℂ) / 12) * (ee (z / 2) - ee (-z / 2)) *
    ∏' n : ℕ, (1 - ee (τ : ℂ) ^ (n + 1) * ee z) * (1 - ee (τ : ℂ) ^ (n + 1) * (ee z)⁻¹)

def act (x : Fin 2 → ℚ) (γ : SL(2, ℤ)) : Fin 2 → ℚ := fun i => ∑ j, x j * (((γ : Matrix (Fin 2) (Fin 2) ℤ) j i : ℤ) : ℚ)

end GlobalTheory.Sieg
end
end

section

noncomputable section
open NumberField IsDedekindDomain GlobalTheory.Mem.Chr
namespace GlobalTheory.Mem.Chr.Model
variable (L : Type) [Field L] [NumberField L]

theorem localIdele_snd_self (v : HeightOneSpectrum (𝓞 L)) (x : (v.adicCompletion L)ˣ) :
    ((localIdele L v x : Ideles L) : AdeleRing (𝓞 L) L).2 v = x := by
  classical
  change Pi.mulSingle (M := fun w : HeightOneSpectrum (𝓞 L) => w.adicCompletion L) v
    (x : v.adicCompletion L) v = x
  exact Pi.mulSingle_eq_same _ _

theorem localIdele_snd_ne (v w : HeightOneSpectrum (𝓞 L)) (h : w ≠ v) (x : (v.adicCompletion L)ˣ) :
    ((localIdele L v x : Ideles L) : AdeleRing (𝓞 L) L).2 w = 1 := by
  classical
  change Pi.mulSingle (M := fun w : HeightOneSpectrum (𝓞 L) => w.adicCompletion L) v
    (x : v.adicCompletion L) w = 1
  exact Pi.mulSingle_eq_of_ne h _

theorem infIdele_fst_self (w : InfinitePlace L) (x : (w.Completion)ˣ) :
    ((infIdele L w x : Ideles L) : AdeleRing (𝓞 L) L).1 w = x := by
  classical
  change Pi.mulSingle (M := fun u : InfinitePlace L => u.Completion) w (x : w.Completion) w = x
  exact Pi.mulSingle_eq_same _ _

theorem infIdele_fst_ne (w u : InfinitePlace L) (h : u ≠ w) (x : (w.Completion)ˣ) :
    ((infIdele L w x : Ideles L) : AdeleRing (𝓞 L) L).1 u = 1 := by
  classical
  change Pi.mulSingle (M := fun u : InfinitePlace L => u.Completion) w (x : w.Completion) u = 1
  exact Pi.mulSingle_eq_of_ne h _

theorem finSingle_continuous (v : HeightOneSpectrum (𝓞 L)) : Continuous (finSingle L v) := by
  classical
  have hS : Filter.cofinite ≤ Filter.principal ({v}ᶜ : Set (HeightOneSpectrum (𝓞 L))) := by
    rw [Filter.le_principal_iff]
    exact (Set.finite_singleton v).compl_mem_cofinite
  let g : v.adicCompletion L → RestrictedProduct (fun w : HeightOneSpectrum (𝓞 L) => w.adicCompletion L)
      (fun w => (w.adicCompletionIntegers L : Set (w.adicCompletion L))) (Filter.principal {v}ᶜ) :=
    fun x => ⟨Pi.mulSingle v x, Filter.eventually_principal.2 fun w hw => by
      rw [Pi.mulSingle_eq_of_ne (Set.mem_compl_singleton_iff.mp hw)]
      exact one_mem _⟩
  have hg : Continuous g :=
    RestrictedProduct.continuous_rng_of_principal.2 (continuous_mulSingle v)
  have hfg : (finSingle L v : v.adicCompletion L → FiniteAdeleRing (𝓞 L) L) =
      RestrictedProduct.inclusion _ _ hS ∘ g := by
    funext x
    rfl
  rw [hfg]
  exact (RestrictedProduct.continuous_inclusion hS).comp hg

theorem localIdele_continuous (v : HeightOneSpectrum (𝓞 L)) : Continuous (localIdele L v) := by
  exact Continuous.units_map _ (continuous_const.prodMk (finSingle_continuous L v))

end GlobalTheory.Mem.Chr.Model
end
end

section

noncomputable section

open Finset

namespace GlobalTheory.KummerEisensteinGalois

variable {K : Type*} [Field K] [CharZero K]

def ffMu (N p m k : ℕ) (ψ : DirichletCharacter K (p ^ m)) (a : ℤ) (s : ℕ) : K :=
  ∑ d ∈ s.divisors, if ¬ p ∣ d ∧ ¬ p ∣ (s / d) then
    ((if ((s / d : ℕ) : ℤ) ≡ a [ZMOD N] then ψ ((s / d : ℕ) : ZMod (p ^ m)) * ((s / d : ℕ) : K) ^ (k - 2) else 0) -
     (if (-((s / d : ℕ) : ℤ)) ≡ a [ZMOD N] then ψ (-((s / d : ℕ) : ZMod (p ^ m))) * (-((s / d : ℕ) : K)) ^ (k - 2) else 0))
    else 0

def eeMu (N p m : ℕ) (ψ : DirichletCharacter K (p ^ m)) (b : ℤ) (s : ℕ) : K :=
  ∑ d ∈ s.divisors, if ¬ p ∣ d ∧ ¬ p ∣ (s / d) then
    ((if ((s / d : ℕ) : ℤ) ≡ b [ZMOD N] then ψ⁻¹ ((d : ℕ) : ZMod (p ^ m)) else 0) -
     (if (-((s / d : ℕ) : ℤ)) ≡ b [ZMOD N] then ψ⁻¹ (-((d : ℕ) : ZMod (p ^ m))) else 0))
    else 0

def coPtMu (N p m k : ℕ) (ψ : DirichletCharacter K (p ^ m)) (a b : ℤ) : ℕ → K :=
  cmul (ffMu N p m k ψ a) (eeMu N p m ψ b)

def coPtS (N p m k : ℕ) (ψ : DirichletCharacter K (p ^ m)) (c d x : ℤ) (s : ℕ) : K :=
  (c : K) ^ 2 * (d : K) ^ 2 * coPtMu N p m k ψ x 1 s
    - (c : K) ^ ((3 : ℤ) - k) * ψ⁻¹ (c : ZMod (p ^ m)) * (d : K) ^ 2 * coPtMu N p m k ψ (c * x) 1 s
    - (c : K) ^ 2 * (d : K) * ψ⁻¹ (d : ZMod (p ^ m)) * coPtMu N p m k ψ x d s
    + (c : K) ^ ((3 : ℤ) - k) * ψ⁻¹ (c : ZMod (p ^ m)) * (d : K) * ψ⁻¹ (d : ZMod (p ^ m)) * coPtMu N p m k ψ (c * x) d s

end GlobalTheory.KummerEisensteinGalois
end
end

section

noncomputable section

namespace GlobalTheory.K5

variable {p : ℕ} [Fact p.Prime] {Ω : Type*} [Field Ω] [Algebra (O0 p) Ω]

def IntegralLocallyConstCochainModPow (k : ℕ) (H : Subgroup (Gal p Ω)) (w : Gal p Ω → Ω) : Prop :=
  (∀ g ∈ H, IsInt (p := p) (w g)) ∧
    ∀ g ∈ H, ∃ S : Finset Ω, ∀ h ∈ H,
      (∀ x ∈ S, h x = g x) → Cong (p := p) k (w h) (w g)

def IsTwistedOneCocycle (j k : ℕ) (H : Subgroup (Gal p Ω)) (χ : Gal p Ω → ZMod (p ^ k)) (c : Gal p Ω → Ω) : Prop :=
  ∀ g ∈ H, ∀ h ∈ H, Cong (p := p) k (c (g * h)) (c g + ((χ g).val : Ω) ^ j * g (c h))

def IsTwistedOneCoboundary (j k : ℕ) (H : Subgroup (Gal p Ω)) (χ : Gal p Ω → ZMod (p ^ k)) (c : Gal p Ω → Ω) : Prop :=
  ∃ x : Ω, IsInt (p := p) x ∧ ∀ g ∈ H, Cong (p := p) k (c g) (((χ g).val : Ω) ^ j * g x - x)

end GlobalTheory.K5
end
end

section

open Matrix MeasureTheory
open scoped ContDiff

noncomputable section

namespace GlobalTheory.SOrb

open Formalism.QuantumDeterminants Formalism.MainNotions.S

def opn {m : ℕ} (g : Matrix (Fin m) (Fin m) ℂ) : ℝ :=
  ‖(Matrix.toEuclideanCLM (n := Fin m) (𝕜 := ℂ) g : EuclideanSpace ℂ (Fin m) →L[ℂ] EuclideanSpace ℂ (Fin m))‖


variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

end GlobalTheory.SOrb
end
end
