module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
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

open NumberField IsDedekindDomain Module

noncomputable section

namespace PI.TwChrOne

section LocS

variable {R : Type*} [CommRing R]

def locS {W : Type*} [AddCommGroup W] [Module R W] (S : Submonoid R) (L : Submodule R W) :
    Submodule R W where
  carrier := {x | ∃ s ∈ S, s • x ∈ L}
  zero_mem' := ⟨1, S.one_mem, by simp⟩
  add_mem' := by
    rintro x y ⟨s, hs, hx⟩ ⟨t, ht, hy⟩
    refine ⟨s * t, S.mul_mem hs ht, ?_⟩
    have e : (s * t) • (x + y) = t • (s • x) + s • (t • y) := by
      rw [smul_add, mul_smul, smul_comm s t x, mul_smul]
    rw [e]
    exact L.add_mem (L.smul_mem t hx) (L.smul_mem s hy)
  smul_mem' := by
    rintro r x ⟨s, hs, hx⟩
    refine ⟨s, hs, ?_⟩
    rw [smul_comm]
    exact L.smul_mem r hx

def localization₂ {W : Type*} [AddCommGroup W] [Module R W] (p : Ideal R) [p.IsPrime] (L : Submodule R W) :
    Submodule R W :=
  locS p.primeCompl L

end LocS

abbrev Sp (E : Type) (n : ℕ) : Type := Fin n → E

section Red

variable {E : Type} [Field E] [NumberField E]

def redP (P : HeightOneSpectrum (𝓞 E)) (a : E) : 𝓞 E ⧸ P.asIdeal :=
  open Classical in
  if h : ∃ c : 𝓞 E ⧸ P.asIdeal, ∃ r s : 𝓞 E, s ∉ P.asIdeal ∧ algebraMap (𝓞 E) E s * a = algebraMap (𝓞 E) E r ∧
      Ideal.Quotient.mk P.asIdeal s * c = Ideal.Quotient.mk P.asIdeal r
  then h.choose else 0

def IntAt (P : HeightOneSpectrum (𝓞 E)) (a : E) : Prop :=
  ∃ r s : 𝓞 E, s ∉ P.asIdeal ∧ algebraMap (𝓞 E) E s * a = algebraMap (𝓞 E) E r

end Red

section Deco

variable (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ)

def stdLat : Submodule (𝓞 E) (Sp E n) := Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 E) E)

end Deco

section Frames

variable (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ)

def stabL (M : Submodule (𝓞 E) (Sp E n)) : Subgroup (Sp E n ≃ₗ[E] Sp E n) where
  carrier := {c | ∀ x, c x ∈ M ↔ x ∈ M}
  one_mem' := fun _ => Iff.rfl
  mul_mem' := fun {a b} ha hb x => (ha (b x)).trans (hb x)
  inv_mem' := fun {a} ha x => by
    have h := ha (a⁻¹ x)
    rw [show a (a⁻¹ x) = x from LinearEquiv.apply_symm_apply a x] at h
    exact h.symm

def stdAt (P : HeightOneSpectrum (𝓞 E)) : Submodule (𝓞 E) (Sp E n) := localization₂ P.asIdeal (stdLat E n)

end Frames

namespace Loc

section Groups

variable (k : Type) [CommRing k] (n c : ℕ)

def atN {k : Type} [CommRing k] {N : ℕ} (v : Fin N → k) (i : ℕ) : k := if h : i < N then v ⟨i, h⟩ else 0

def eN (N i : ℕ) : Fin N → k := fun l => if l.1 = i then 1 else 0

def supp (N : ℕ) (s : Set ℕ) : Submodule k (Fin N → k) where
  carrier := {v | ∀ l : Fin N, l.1 ∉ s → v l = 0}
  add_mem' := fun {a b} ha hb l hl => by simp [ha l hl, hb l hl]
  zero_mem' := fun _ _ => rfl
  smul_mem' := fun r a ha l hl => by simp [ha l hl]

def Ufl (i : ℕ) : Submodule k (Fin (n + c) → k) := supp k (n + c) {l | l < n + i}

def inX : (Fin n → k) →ₗ[k] (Fin (n + c) → k) :=
  LinearMap.pi fun l => if h : l.1 < n then LinearMap.proj ⟨l.1, h⟩ else 0

def R1cond (r : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)) : Prop :=
  (∀ i, ∀ v ∈ Ufl k n c i, r v ∈ Ufl k n c i) ∧ r (eN k (n + c) n) = eN k (n + c) n ∧
    ∀ i, r (eN k (n + c) (n + i)) - eN k (n + c) (n + i) ∈ Ufl k n c i

variable {k n c} in
theorem R1cond.mul {r s : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)} (hr : R1cond k n c r) (hs : R1cond k n c s) :
    R1cond k n c (r * s) := by
  refine ⟨fun i v hv => hr.1 i _ (hs.1 i v hv), ?_, fun i => ?_⟩
  · show r (s _) = _
    rw [hs.2.1, hr.2.1]
  · have h1 : (r * s) (eN k (n + c) (n + i)) - eN k (n + c) (n + i) =
        r (s (eN k (n + c) (n + i)) - eN k (n + c) (n + i)) + (r (eN k (n + c) (n + i)) - eN k (n + c) (n + i)) := by
      rw [map_sub]
      show r (s _) - _ = _
      abel
    rw [h1]
    exact add_mem (hr.1 i _ (hs.2.2 i)) (hr.2.2 i)

theorem R1cond_one : R1cond k n c 1 :=
  ⟨fun _ _ hv => hv, rfl, fun i => by
    show eN k (n + c) (n + i) - eN k (n + c) (n + i) ∈ _
    rw [sub_self]
    exact zero_mem _⟩

def R1 : Subgroup ((Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)) where
  carrier := {r | R1cond k n c r ∧ R1cond k n c r⁻¹}
  one_mem' := ⟨R1cond_one k n c, by rw [inv_one]; exact R1cond_one k n c⟩
  mul_mem' := fun {a b} ha hb => ⟨ha.1.mul hb.1, by rw [mul_inv_rev]; exact hb.2.mul ha.2⟩
  inv_mem' := fun {a} ha => ⟨ha.2, by rw [inv_inv]; exact ha.1⟩

variable {k n c}

def n1Arg (r : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)) : k :=
  ∑ i ∈ Finset.range (c - 1), atN (r (eN k (n + c) (n + i + 1))) (n + i)

def Cbe (J : Subgroup ((Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k))) (h : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)) :
    Subgroup ((Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)) :=
  R1 k n c ⊓ J.comap (MulAut.conj h⁻¹).toMonoidHom

end Groups

end Loc

abbrev HomE (E : Type) [Field E] (a b : ℕ) : Type := Sp E a →ₗ[E] Sp E b

namespace LocE

open Loc

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] (P : HeightOneSpectrum (𝓞 E)) (q : ℕ)

variable {P} in
open Classical in
def unitV (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (a : E) : K := if h : IsUnit (redP P a) then ((χ h.unit : Kˣ) : K) else 0


def sclLat (N : ℕ) (e : ℕ → ℤ) : Submodule (𝓞 E) (Sp E N) :=
  (stdAt E N P).comap
    ((LinearMap.pi fun l : Fin N => ((q : E) ^ e l.1)⁻¹ • (LinearMap.proj l : Sp E N →ₗ[E] E)).restrictScalars (𝓞 E))

section AtQ

variable (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ)

def parL (kj n c : ℕ) : Submodule (𝓞 E) (Sp E (n + c)) := sclLat P q (n + c) fun l => if kj ≤ l ∧ l < n then 1 else 0

def JQ (kj n c : ℕ) : Subgroup (Sp E (n + c) ≃ₗ[E] Sp E (n + c)) :=
  stabL E (n + c) (stdAt E (n + c) P) ⊓ stabL E (n + c) (parL P q kj n c)

variable {P}

def lamQB (kj n : ℕ) {N : ℕ} (h : HomE E N N) : K :=
  (unitV ξ (Matrix.det (Matrix.of fun s t : Fin (n - kj) => atN (h (eN E N (kj + t.1))) (kj + s.1))))⁻¹

end AtQ

end LocE

section Target

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K]

def ChiL (P : HeightOneSpectrum (𝓞 E)) (psi : E → K) (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (kj N c : ℕ)
    (h r : Sp E (N + c) ≃ₗ[E] Sp E (N + c)) : K :=
  (psi (Loc.n1Arg r))⁻¹ * LocE.lamQB ξ kj N ((h⁻¹ * r * h : Sp E (N + c) ≃ₗ[E] Sp E (N + c))).toLinearMap

def ChrOkL (P : HeightOneSpectrum (𝓞 E)) (psi : E → K) (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (kj N c : ℕ)
    (h : Sp E (N + c) ≃ₗ[E] Sp E (N + c)) : Prop :=
  (∀ r ∈ Loc.Cbe (LocE.JQ P (Ideal.absNorm P.asIdeal) kj N c) h, ChiL P psi ξ kj N c h r ≠ 0) ∧
  ∀ r ∈ Loc.Cbe (LocE.JQ P (Ideal.absNorm P.asIdeal) kj N c) h, ∀ r' ∈ Loc.Cbe (LocE.JQ P (Ideal.absNorm P.asIdeal) kj N c) h,
    ∀ r'' ∈ Loc.Cbe (LocE.JQ P (Ideal.absNorm P.asIdeal) kj N c) h,
    (∀ x, r'' (Loc.inX E N c x) = r (r' (Loc.inX E N c x))) →
      ChiL P psi ξ kj N c h r'' = ChiL P psi ξ kj N c h r * ChiL P psi ξ kj N c h r'

end Target

def TwChrOne : Prop :=
  ∀ (E K : Type) [Field E] [NumberField E] [StarRing E] [Field K] (P : HeightOneSpectrum (𝓞 E)) (psi : E → K)
    (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (kj N c : ℕ), (∀ x, IntAt P x → psi x = 1) → ChrOkL P psi ξ kj N c 1

end PI.TwChrOne
end
end

section

noncomputable section

namespace PI

open NumberField

def IsCMUnram (K : Type*) [Field K] [NumberField K] [StarRing K] : Prop :=
  IsTotallyComplex K ∧ (∀ (φ : K →+* ℂ) (a : K), φ (star a) = starRingEnd ℂ (φ a)) ∧
    ∀ P : Ideal (RingOfIntegers K), P.IsMaximal →
      ∃ θ t : RingOfIntegers K, algebraMap (RingOfIntegers K) K t =
        star (algebraMap (RingOfIntegers K) K θ) ∧ θ - t ∉ P

def CMTraceOnto : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K], IsCMUnram K →
    ∀ a : 𝓞 K, star (a : K) = (a : K) → ∃ x y : 𝓞 K, (y : K) = star (x : K) ∧ x + y = a

end PI

end
end

section

noncomputable section

namespace PI

def IsIntP {p : ℕ} [Fact p.Prime] (x : ℂ_[p]) : Prop := ‖x‖ ≤ 1

def IntegralMv {σ : Type*} {p : ℕ} [Fact p.Prime] (F : MvPowerSeries σ ℂ_[p]) : Prop :=
  ∀ n, IsIntP (MvPowerSeries.coeff n F)

def expMv {σ : Type*} {p : ℕ} [Fact p.Prime] (F : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  fun α => ∑ n ∈ Finset.range ((α.sum fun _ k => k) + 1),
    MvPowerSeries.coeff α (F ^ n) / (n.factorial : ℂ_[p])

def Wp (p : ℕ) [Fact p.Prime] : Subring ℂ_[p] :=
  (Subring.closure {ζ : ℂ_[p] | ∃ n : ℕ, 0 < n ∧ Nat.Coprime n p ∧ ζ ^ n = 1}).topologicalClosure

def InWf {p : ℕ} [Fact p.Prime] (x : ℂ_[p]) : Prop := ∃ k : ℕ, (p : ℂ_[p]) ^ k * x ∈ Wp p

def IntegralW {σ : Type*} {p : ℕ} [Fact p.Prime] (F : MvPowerSeries σ ℂ_[p]) : Prop :=
  ∀ n, MvPowerSeries.coeff n F ∈ Wp p

def CoefWf {σ : Type*} {p : ℕ} [Fact p.Prime] (F : MvPowerSeries σ ℂ_[p]) : Prop :=
  ∀ n, InWf (MvPowerSeries.coeff n F)

def Simeq {σ : Type*} {p : ℕ} [Fact p.Prime] (f g : MvPowerSeries σ ℂ_[p]) : Prop :=
  MvPowerSeries.constantCoeff (f - g) = 0 ∧ IntegralMv (expMv (f - g))

def SimeqW {σ : Type*} {p : ℕ} [Fact p.Prime] (f g : MvPowerSeries σ ℂ_[p]) : Prop :=
  MvPowerSeries.constantCoeff (f - g) = 0 ∧ IntegralW (expMv (f - g))

def ExpIntW : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (f : MvPowerSeries σ ℂ_[p]), CoefWf f → Simeq f 0 → SimeqW f 0

end PI

end
end

section

noncomputable section

namespace PI.FinExtTop

structure PadicCoeff (p : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] : Prop where
  ring : IsTopologicalRing O
  compact : CompactSpace O
  t2 : T2Space O
  adic : IsAdic (IsLocalRing.maximalIdeal O)
  p_mem : (p : O) ∈ IsLocalRing.maximalIdeal O
  p_ne : (p : O) ≠ 0

structure FracTop (O : Type) [CommRing O] [IsDomain O] [TopologicalSpace O]
    [TopologicalSpace (FractionRing O)] : Prop where
  emb : Topology.IsOpenEmbedding (algebraMap O (FractionRing O))

structure IsFGTop (O M : Type) [CommRing O] [TopologicalSpace O] [AddCommGroup M] [Module O M]
    [TopologicalSpace M] : Prop where
  fg : Module.Finite O M
  t2 : T2Space M
  csmul : ContinuousSMul O M

end PI.FinExtTop

namespace PI


open PI.FinExtTop in
def FinExtTop : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (O O' : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [Algebra ℤ_[ℓ] O] [Module.Finite ℤ_[ℓ] O]
    [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O'] [Module.Free O O']
    [Module.Finite O O'],
    PadicCoeff ℓ O →
    ∃ (_ : Algebra ℤ_[ℓ] O') (_ : IsScalarTower ℤ_[ℓ] O O') (_ : Module.Finite ℤ_[ℓ] O')
      (_ : TopologicalSpace O') (_ : IsModuleTopology O O')
      (_ : TopologicalSpace (FractionRing O')) (_ : IsTopologicalAddGroup (FractionRing O'))
      (_ : ContinuousSMul O' (FractionRing O')),
      Function.Injective (algebraMap ℤ_[ℓ] O') ∧ PadicCoeff ℓ O' ∧ FracTop O' ∧
      ∀ (X' d : Type) [Fintype d] [DecidableEq d]
        (R' : Subalgebra O' (X' → Matrix d d (FractionRing O'))), Module.Finite O' R' →
        ∃ (_ : TopologicalSpace R') (_ : IsModuleTopology O' R'),
          IsTopologicalAddGroup R' ∧ ContinuousConstSMul O' R' ∧ ContinuousMul R' ∧
          IsTopologicalRing R' ∧ IsFGTop O' R'

end PI
end
end

section

open NumberField IsDedekindDomain

namespace PI

def LocalEndHomeo : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (τ : v.adicCompletion F →+* v.adicCompletion F),
    Continuous τ ∧ ∃ τ' : v.adicCompletion F →+* v.adicCompletion F, Continuous τ' ∧ ∀ a, τ (τ' a) = a

end PI
end

section

open Matrix NumberField IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace PI.SelfDualLoc

section Defs

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

def hform (σ : A →+* A) (J : Matrix n n A) (x y : n → A) : A := ∑ i, ∑ j, σ (x i) * J i j * y j

end Defs

section Points

variable {F E : Type} [Field F] [CommRing E] [Algebra F E] {n : Type} [Fintype n] [DecidableEq n]

def sigR (σ : E →ₐ[F] E) (R : Type) [CommRing R] [Algebra F R] : E ⊗[F] R →+* E ⊗[F] R :=
  (Algebra.TensorProduct.map σ (AlgHom.id F R)).toRingHom

def inclE (R : Type) [CommRing R] [Algebra F R] : E →+* E ⊗[F] R :=
  Algebra.TensorProduct.includeLeftRingHom

def tensInt (R : Type) [CommRing R] [Algebra F R] (S₁ : Subring E) (S₂ : Subring R) :
    Subring (E ⊗[F] R) :=
  Subring.closure (Set.range (fun x : S₁ => (x : E) ⊗ₜ[F] (1 : R)) ∪
    Set.range (fun y : S₂ => (1 : E) ⊗ₜ[F] (y : R)))

def latS (R : Type) [CommRing R] [Algebra F R] (S : Subring (E ⊗[F] R)) {O : Type} [CommRing O]
    [Algebra O E] (Λ : Submodule O (n → E)) : Submodule S (n → E ⊗[F] R) :=
  Submodule.span S ((fun x : n → E => fun i => inclE (F := F) R (x i)) '' (Λ : Set (n → E)))

end Points

def intOE (E : Type) [Field E] [NumberField E] : Subring E := (algebraMap (𝓞 E) E).range

end PI.SelfDualLoc

namespace PI

open PI.SelfDualLoc in
def SelfDualLoc : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
    (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F))
    (Lb : Submodule (𝓞 E) (Fin n → E)) (T : ℕ),
    Module.Finite (𝓞 E) Lb →
    (∀ x ∈ Lb, ∀ y ∈ Lb, hform (σ : E →+* E) J x y ∈ intOE E) →
    (∀ y : Fin n → E, (∀ x ∈ Lb, hform (σ : E →+* E) J x y ∈ intOE E) → (T : E) • y ∈ Lb) →
    (T : 𝓞 F) ∉ v.asIdeal →
    ∀ y, y ∈ latS (F := F) (v.adicCompletion F)
        (tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring) Lb ↔
      ∀ z ∈ latS (F := F) (v.adicCompletion F)
        (tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring) Lb,
        hform (sigR σ (v.adicCompletion F)) (J.map (inclE (F := F) (v.adicCompletion F))) z y ∈
          tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring

end PI
end
end

section

open Matrix NumberField IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace PI.SplitIntLoc

section Defs

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

end Defs

section Points

variable {F E : Type} [Field F] [CommRing E] [Algebra F E] {n : Type} [Fintype n] [DecidableEq n]

def tensInt (R : Type) [CommRing R] [Algebra F R] (S₁ : Subring E) (S₂ : Subring R) :
    Subring (E ⊗[F] R) :=
  Subring.closure (Set.range (fun x : S₁ => (x : E) ⊗ₜ[F] (1 : R)) ∪
    Set.range (fun y : S₂ => (1 : E) ⊗ₜ[F] (y : R)))

end Points

def intOE (E : Type) [Field E] [NumberField E] : Subring E := (algebraMap (𝓞 E) E).range

end PI.SplitIntLoc

namespace PI

open PI.SplitIntLoc in
def SplitIntLoc : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F))
    (spl : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F),
    (∀ a : v.adicCompletion F, spl ((1 : E) ⊗ₜ[F] a) = (a, a)) →
    ∀ x, x ∈ tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring ↔
      (spl x).1 ∈ v.adicCompletionIntegers F ∧ (spl x).2 ∈ v.adicCompletionIntegers F

end PI
end
end
