module

public import Mathlib.Basic.Real.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.Data.Matrix.Mul
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.WittVector.Frobenius
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.MeasureTheory.Group.Measure
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField IsDedekindDomain

noncomputable section

namespace PI.UnipVal

variable {K : Type} [Field K] [NumberField K]

def vw (w : HeightOneSpectrum (𝓞 K)) (a : K) : ℤ :=
  FractionalIdeal.count K w (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) a)

def plc (w : HeightOneSpectrum (𝓞 K)) : ℕ := ringChar (𝓞 K ⧸ w.asIdeal)

def ramw (w : HeightOneSpectrum (𝓞 K)) : ℤ := vw w ((plc w : ℕ) : K)

def UnipVal : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)),
    (∀ n : ℕ, n ≠ 0 → vw w ((n : ℕ) : K) = ramw w * (padicValNat (plc w) n : ℤ)) ∧
    ∀ g₁ g₂ a : ℕ, g₁.Prime → g₂.Prime → g₁ ≠ g₂ →
      (vw w (((g₁ ^ a * g₂ ^ a : ℕ)) : K) : ℝ) = (ramw w : ℝ) * (if plc w = g₁ ∨ plc w = g₂ then (a : ℝ) else 0)

end PI.UnipVal

end
end

section

namespace PI

open Matrix

def SmithDiag.{u} : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] (n : ℕ)
    (A : Matrix (Fin n) (Fin n) R),
    ∃ (U V : Matrix (Fin n) (Fin n) R) (d : Fin n → R),
      IsUnit U ∧ IsUnit V ∧ U * A * V = diagonal d

def SmithMat.{u} : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] (n : ℕ)
    (A : Matrix (Fin n) (Fin n) R),
    ∃ (U V : Matrix (Fin n) (Fin n) R) (d : Fin n → R),
      IsUnit U ∧ IsUnit V ∧ U * A * V = diagonal d ∧ ∀ i j, i ≤ j → d i ∣ d j

end PI
end

section

noncomputable section

namespace PI

abbrev WF (p f : ℕ) [Fact p.Prime] := WittVector p (GaloisField p f)

def IsWittIdent {p f : ℕ} [Fact p.Prime] {W Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq] (σ : Qq ≃+* Qq)
    (φ : WF p f ≃+* W) : Prop :=
  ∀ x : WF p f, σ (algebraMap W Qq (φ x)) = algebraMap W Qq (φ (WittVector.frobenius x))

def WittUnram : Prop :=
  ∀ (p f : ℕ) [Fact p.Prime] (W Qq : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] (σ : Qq ≃+* Qq),
    IsFractionRing W Qq → Irreducible (p : W) → Nat.card (W ⧸ Ideal.span {(p : W)}) = p ^ f →
    IsAdicComplete (Ideal.span {(p : W)}) W →
    (∀ x : W, ∃ y : W, σ (algebraMap W Qq x) = algebraMap W Qq (x ^ p + (p : W) * y)) →
    ∃ φ : WF p f ≃+* W, IsWittIdent σ φ

end PI
end
end

section

namespace PI

open MvPolynomial

def LatMin : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (B : MvPolynomial σ ℚ_[p] → MvPolynomial σ ℚ_[p] → ℚ_[p])
    (L : Submodule ℤ_[p] (MvPolynomial σ ℚ_[p])) (W : Submodule ℚ_[p] (MvPolynomial σ ℚ_[p])),
    p ≠ 2 → FiniteDimensional ℚ_[p] W → (∀ x ∈ L, x ∈ W) → L.FG →
    (∀ (c : ℚ_[p]) u v, B (c • u) v = c * B u v) → (∀ u u' v, B (u + u') v = B u v + B u' v) →
    (∀ u ∈ L, ∀ v ∈ L, B u v = B v u) → (∃ u ∈ L, ∃ v ∈ L, B u v ≠ 0) →
    ∃ x ∈ L, B x x ≠ 0 ∧ ∀ u ∈ L, ∃ c : ℤ_[p], B u x = (c : ℚ_[p]) * B x x

end PI
end

section

noncomputable section

namespace PI.NormGramAtOrigin

section G

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

def hform (σ : A →+* A) (J : Matrix n n A) (x y : n → A) : A := ∑ i, ∑ j, σ (x i) * J i j * y j

end G

def gram {E : Type} [Field E] (σ : E →+* E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E) (X : Fin r → Fin n → E) :
    Matrix (Fin r) (Fin r) E := fun a b => hform σ J (X a) (X b)

def Statement : Prop :=
  ∀ (E : Type) [Field E] [StarRing E] [CharZero E] (n r : ℕ), r ≤ n →
    ∀ J : Matrix (Fin n) (Fin n) E, (∀ i j, star (J j i) = J i j) → J.det ≠ 0 →
      ∃ X : Fin r → Fin n → E, (gram (starRingEnd E) J X).det ≠ 0

end PI.NormGramAtOrigin
end
end

section

namespace PI

def minkowskiExp (N p : ℕ) : ℕ := ∑ i ∈ Finset.range (N + 1), N / (p ^ i * (p - 1))

def minkowskiM (N : ℕ) : ℕ := ∏ p ∈ (Finset.range (N + 2)).filter Nat.Prime, p ^ minkowskiExp N p

def MinkowskiBound : Prop :=
  ∀ (N : ℕ) (G : Subgroup (Matrix.GeneralLinearGroup (Fin N) ℤ)), Finite G →
    Nat.card G ∣ minkowskiM N

end PI
end

section

namespace PI.MirabIndex

def IsMirab {k : Type} [Field k] {n : ℕ} (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k) : Prop :=
  ∀ j, h (Fin.last n) j = if j = Fin.last n then 1 else 0

def IsUniU {k : Type} [Field k] {n : ℕ} (u : Matrix (Fin (n + 1)) (Fin (n + 1)) k) : Prop :=
  (∀ i, u i i = 1) ∧ ∀ i j, j < i → u i j = 0

def MirabIndex : Prop :=
  ∀ (k : Type) [Field k] [Fintype k] (n : ℕ),
    Nat.card {h : GL (Fin (n + 1)) k // IsMirab (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k)} =
      Nat.card {u : GL (Fin (n + 1)) k // IsUniU (u : Matrix (Fin (n + 1)) (Fin (n + 1)) k)} *
        ∏ i ∈ Finset.Ico 1 (n + 1), (Fintype.card k ^ i - 1)

end PI.MirabIndex
end

section

namespace PI

namespace SSAscent

section Rep

variable {Γ : Type} [Group Γ] {k : Type} [Field k] {a : ℕ}

def IsInv (ρ : Γ →* GL (Fin a) k) (W : Submodule k (Fin a → k)) : Prop :=
  ∀ g, ∀ v ∈ W, (ρ g : Matrix (Fin a) (Fin a) k).mulVec v ∈ W

def IsSSRep (ρ : Γ →* GL (Fin a) k) : Prop :=
  ∀ W, IsInv ρ W → ∃ W', IsInv ρ W' ∧ IsCompl W W'

end Rep

def mapRep {Γ : Type} [Group Γ] {A B : Type} [CommRing A] [CommRing B] {a : ℕ} (f : A →+* B)
    (ρ : Γ →* GL (Fin a) A) : Γ →* GL (Fin a) B :=
  (Units.map (f.mapMatrix : Matrix (Fin a) (Fin a) A →+* Matrix (Fin a) (Fin a) B).toMonoidHom).comp ρ

end SSAscent

open SSAscent

def SSAscent : Prop :=
  ∀ (K L : Type) [Field K] [CharZero K] [Field L] [Algebra K L] (Γ : Type) [Group Γ] (a : ℕ)
    (ρ : Γ →* GL (Fin a) K), IsSSRep ρ → IsSSRep (mapRep (algebraMap K L) ρ)

end PI
end

section

open MvPolynomial Matrix

noncomputable section

namespace PI.OddDualWeyl

def rowAct (R : Type*) [CommRing R] {r n : ℕ} (g : Matrix (Fin r) (Fin r) R) :
    MvPolynomial (Fin r × Fin n) R →ₐ[R] MvPolynomial (Fin r × Fin n) R :=
  aeval fun v => ∑ b : Fin r, C (g v.1 b) * X (b, v.2)

def rowGen (R : Type*) [CommRing R] {r n : ℕ} (a b : Fin r) :
    MvPolynomial (Fin r × Fin n) R →ₐ[R] Polynomial (MvPolynomial (Fin r × Fin n) R) :=
  aeval fun v => Polynomial.C (X v) +
    (if v.1 = b then Polynomial.X * Polynomial.C (X (a, v.2)) else 0)

def rowDiv (R : Type*) [CommRing R] {r n : ℕ} (a b : Fin r) (k : ℕ)
    (f : MvPolynomial (Fin r × Fin n) R) : MvPolynomial (Fin r × Fin n) R :=
  (rowGen R a b f).coeff k

def lpMinor (R : Type*) [CommRing R] {r n : ℕ} (s : ℕ) (hr : s ≤ r) (hn : s ≤ n) :
    MvPolynomial (Fin r × Fin n) R :=
  (Matrix.of fun p q : Fin s =>
    (X (Fin.castLE hr p, Fin.castLE hn q) : MvPolynomial (Fin r × Fin n) R)).det

def nuNext {n : ℕ} (ν : Fin n → ℕ) (s : Fin n) : ℕ :=
  if h : s.val + 1 < n then ν ⟨s.val + 1, h⟩ else 0

def hw (R : Type*) [CommRing R] {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) :
    MvPolynomial (Fin r × Fin n) R :=
  ∏ s : Fin n, (lpMinor R (s.val + 1) (by omega) (by omega)) ^ (ν s - nuNext ν s)

def applyWord (R : Type*) [CommRing R] {r n : ℕ} (w : List (Fin r × Fin r × ℕ))
    (f : MvPolynomial (Fin r × Fin n) R) : MvPolynomial (Fin r × Fin n) R :=
  w.foldr (fun x g => rowDiv R x.1 x.2.1 x.2.2 g) f

def weyl (R : Type*) [CommRing R] (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ) :
    Submodule R (MvPolynomial (Fin r × Fin n) R) :=
  Submodule.span R (Set.range fun w : List (Fin r × Fin r × ℕ) => applyWord R w (hw R hn ν))

def colSpan (R : Type*) {K : Type*} [CommRing R] [Field K] [Algebra R K] {k : ℕ}
    (g : Matrix (Fin k) (Fin k) K) : Submodule R (Fin k → K) :=
  Submodule.span R (Set.range fun c : Fin k => fun i => g i c)

def nuOf {m : ℕ} (lam : Fin (m + 1) → ℤ) : Fin (m + 1) → ℕ :=
  fun t => (lam t - lam (Fin.last m)).toNat

def deltaL (R K : Type*) [CommRing R] [Field K] [Algebra R K] (k : ℕ) (ν : Fin k → ℕ)
    (g : Matrix (Fin k) (Fin k) K) : Submodule R (MvPolynomial (Fin k × Fin k) K) :=
  Submodule.comap ((rowAct K (n := k) g).toLinearMap.restrictScalars R)
    (Submodule.map (mapAlgHom (Algebra.ofId R K)).toLinearMap (weyl R k k le_rfl ν))

def deltaLTw (R K : Type*) [CommRing R] [Field K] [Algebra R K] (m : ℕ) (lam : Fin (m + 1) → ℤ)
    (g : Matrix (Fin (m + 1)) (Fin (m + 1)) K) : Submodule R (MvPolynomial (Fin (m + 1) × Fin (m + 1)) K) :=
  Submodule.map ((LinearMap.lsmul K (MvPolynomial (Fin (m + 1) × Fin (m + 1)) K)
      (g.det ^ (-(lam (Fin.last m))))).restrictScalars R)
    (deltaL R K (m + 1) (nuOf lam) g)

def Dl0 (O : Type*) {Kf : Type*} [CommRing O] [Field Kf] [Algebra O Kf] (m : ℕ) (lam : Fin (m + 1) → ℤ)
    (Λ : Submodule O (Fin (m + 1) → Kf)) : Submodule O (MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf) :=
  if Antitone lam then
    ⨅ (g : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf) (_ : IsUnit g.det ∧ Λ = colSpan O g), deltaLTw O Kf m lam g
  else ⊥

section GlobalTheory

variable {K : Type} [Field K]

def lamStar {m : ℕ} (lam : Fin (m + 1) → ℤ) : Fin (m + 1) → ℤ := fun i => -lam i.rev

def revCol {m : ℕ} (z : Matrix (Fin (m + 1)) (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K :=
  z.submatrix id Fin.rev

def OddFact (O : Type) [CommRing O] [Algebra O K] (m : ℕ) (lam : Fin (m + 1) → ℤ) : Prop :=
  ∀ g : Matrix (Fin (m + 1)) (Fin (m + 1)) K, IsUnit g.det →
    (∀ F ∈ Dl0 O m lam (colSpan O g), ∃ F' ∈ Dl0 O m (lamStar lam) (colSpan O (g⁻¹)ᵀ),
      ∀ z : Matrix (Fin (m + 1)) (Fin (m + 1)) K, IsUnit z.det →
        z.det ^ lam (Fin.last m) * eval (fun x => z x.1 x.2) F =
          (revCol (z⁻¹)ᵀ).det ^ lamStar lam (Fin.last m) * eval (fun x => revCol (z⁻¹)ᵀ x.1 x.2) F') ∧
    (∀ F' ∈ Dl0 O m (lamStar lam) (colSpan O (g⁻¹)ᵀ), ∃ F ∈ Dl0 O m lam (colSpan O g),
      ∀ z : Matrix (Fin (m + 1)) (Fin (m + 1)) K, IsUnit z.det →
        z.det ^ lam (Fin.last m) * eval (fun x => z x.1 x.2) F =
          (revCol (z⁻¹)ᵀ).det ^ lamStar lam (Fin.last m) * eval (fun x => revCol (z⁻¹)ᵀ x.1 x.2) F')

end GlobalTheory

end PI.OddDualWeyl
end
end

section

open NumberField IsDedekindDomain Module MvPolynomial

noncomputable section

namespace PI.UnfoldEquiv

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


variable {k n c}

def n1Arg (r : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)) : k :=
  ∑ i ∈ Finset.range (c - 1), atN (r (eN k (n + c) (n + i + 1))) (n + i)

end Groups

section Data

variable {k K : Type} [CommRing k] [Field K]

variable (n' c' n c : ℕ)

def IsFree (l s : ℕ) : Prop := n' ≤ s ∧ (s - n' = c ∨ (1 ≤ s - n' ∧ (l < n ∨ l - n < s - n')))

instance (l s : ℕ) : Decidable (IsFree n' n c l s) := by unfold IsFree; infer_instance

abbrev FC : Type := {p : Fin (n + c) × Fin (n' + c') // IsFree n' n c p.1.1 p.2.1}

variable {n' c' n c}

def xx1 (xj : (Fin n' → k) →ₗ[k] (Fin n → k)) (t : FC n' c' n c → k) : (Fin (n' + c') → k) →ₗ[k] (Fin (n + c) → k) :=
  Matrix.toLin' (Matrix.of fun (l : Fin (n + c)) (s : Fin (n' + c')) =>
    if hf : IsFree n' n c l.1 s.1 then t ⟨(l, s), hf⟩
    else if hs : s.1 < n' then (if hl : l.1 < n then LinearMap.toMatrix' xj ⟨l.1, hl⟩ ⟨s.1, hs⟩ else 0)
    else if l.1 = n + (s.1 - n') then 1 else 0)

def chArg (x : (Fin (n' + c') → k) →ₗ[k] (Fin (n + c) → k)) : k :=
  ∑ i ∈ Finset.range c, atN (x (eN k (n' + c') (n' + i + 1))) (n + i)

end Data

end Loc

end PI.UnfoldEquiv

end
end

section

open MeasureTheory Topology

noncomputable section

namespace PI

def UnimodIdx : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [SigmaFinite μ], μ.IsHaarMeasure →
    ∀ (U : ℕ → Subgroup G), (∀ n, IsOpen (U n : Set G)) → (∀ V ∈ 𝓝 (1 : G), ∃ n, (U n : Set G) ⊆ V) →
    ∀ K : Subgroup G, IsOpen (K : Set G) → IsCompact (K : Set G) →
    (∀ x : G, (K.map (MulAut.conj x).toMonoidHom).relIndex K = (K.map (MulAut.conj x⁻¹).toMonoidHom).relIndex K) →
    μ.IsMulRightInvariant

end PI

end
end

section

noncomputable section

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct ENNReal Matrix

namespace PI.WeilQuotMeas

def WeilQuotient : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (H : Subgroup G), IsClosed (H : Set G) →
    ∀ (μ : Measure G) (ν : Measure H), μ.IsHaarMeasure → μ.IsMulRightInvariant → ν.IsHaarMeasure →
      ν.IsMulRightInvariant →
      ∃ ρ : Measure (G ⧸ H), ρ ≠ 0 ∧ (∀ K : Set (G ⧸ H), IsCompact K → ρ K < ⊤) ∧
        (∀ (g : G) (s : Set (G ⧸ H)), MeasurableSet s → ρ ((fun y => g • y) ⁻¹' s) = ρ s) ∧
        (∀ f : G → ℝ≥0∞, Measurable f → ∫⁻ g, f g ∂μ = ∫⁻ y, (∫⁻ h, f (y.out * h) ∂ν) ∂ρ) ∧
        ∀ ρ' : Measure (G ⧸ H), (∀ K : Set (G ⧸ H), IsCompact K → ρ' K < ⊤) →
          (∀ (g : G) (s : Set (G ⧸ H)), MeasurableSet s → ρ' ((fun y => g • y) ⁻¹' s) = ρ' s) →
          ∃ c : ℝ≥0∞, ρ' = c • ρ

def WqUnique : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (H : Subgroup G), IsClosed (H : Set G) →
    ∀ ρ ρ' : Measure (G ⧸ H), ρ ≠ 0 →
      (∀ K : Set (G ⧸ H), IsCompact K → ρ K < ⊤) →
      (∀ (g : G) (s : Set (G ⧸ H)), MeasurableSet s → ρ ((fun y => g • y) ⁻¹' s) = ρ s) →
      (∀ K : Set (G ⧸ H), IsCompact K → ρ' K < ⊤) →
      (∀ (g : G) (s : Set (G ⧸ H)), MeasurableSet s → ρ' ((fun y => g • y) ⁻¹' s) = ρ' s) →
      ∃ c : ℝ≥0∞, ρ' = c • ρ

end PI.WeilQuotMeas
end
end
