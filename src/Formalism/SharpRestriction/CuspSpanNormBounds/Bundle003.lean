module

public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Mathlib.Algebra.AffineMonoid.Basic
public import Formalism.SharpRestriction.CuspSpanNormBounds.LinQRawRange
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.S

open NumberField Formalism.BasicNotions

section Generic

variable {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E)

def brS (x y : S.V) : E := S.hT y x

def perpS (U : Submodule E S.V) : Submodule E S.V where
  carrier := {y | ∀ x ∈ U, S.hT x y = 0}
  add_mem' := by
    intro a b ha hb x hx
    simp [map_add (f := _), ha x hx, hb x hx]
  zero_mem' := by intro x _; simp
  smul_mem' := by
    intro c a ha x hx
    simp [map_smul, ha x hx]

structure FlagG (r : ℕ) (T : E) where
  e : Fin r → S.V
  z : S.V
  e_indep : LinearIndependent E e
  e_iso : ∀ a b, S.hT (e a) (e b) = 0
  z_orth : ∀ a, S.hT (e a) z = 0
  z_norm : S.hT z z = -T

variable {S} {r : ℕ} {T : E}

def FlagG.fvec (F : FlagG S r T) : Fin (r + 1) → S.V := Fin.snoc (α := fun _ => S.V) F.e F.z

def FlagG.Xa (F : FlagG S r T) (a : ℕ) : Submodule E S.V :=
  Submodule.span E (F.e '' {i | i.1 < a})

def FlagG.X (F : FlagG S r T) : Submodule E S.V := Submodule.span E (Set.range F.e)

def FlagG.Xplus (F : FlagG S r T) : Submodule E S.V := F.X ⊔ Submodule.span E {F.z}

def FlagG.XplusPerp (F : FlagG S r T) : Submodule E S.V := perpS S F.Xplus

def FlagG.coefX (F : FlagG S r T) (y : S.V) (a : Fin r) : E := by
  classical
  exact if h : y ∈ Submodule.span E (Set.range F.e) then (F.e_indep.repr ⟨y, h⟩) a else 0

def FlagG.level (F : FlagG S r T) (x : S.V) : ℕ := sInf {a | x ∈ F.Xa a}

def Zhat {T' : E} (F : FlagG S r T) (F' : FlagG S r T') : Matrix (Fin (r + 1)) (Fin (r + 1)) E :=
  fun a b => brS S (F'.fvec b) (F.fvec a)

def leadMinorE {N : ℕ} (A : Matrix (Fin N) (Fin N) E) (l : ℕ) : E := by
  classical
  exact if h : l ≤ N then (A.submatrix (Fin.castLE h) (Fin.castLE h)).det else 0

def Dl {T' : E} (F : FlagG S r T) (F' : FlagG S r T') (l : ℕ) : E := leadMinorE (Zhat F F') l

def Gflag {T' : E} (F : FlagG S r T) (F' : FlagG S r T') : E :=
  Dl F F' (r + 1) * star (Dl F F' (r + 1)) - T * T' * (Dl F F' r * star (Dl F F' r))

def Isp {T' : E} (F : FlagG S r T) (F' : FlagG S r T') : Submodule E S.V := F.X ⊓ F'.X

def LieU (S : HSpace E) : Set (S.V →ₗ[E] S.V) := {Y | ∀ x y, S.hT (Y x) y + S.hT x (Y y) = 0}

def FlagG.LieN (F : FlagG S r T) : Set (S.V →ₗ[E] S.V) :=
  {Y | Y ∈ LieU S ∧ (∀ a : ℕ, 1 ≤ a → a ≤ r → ∀ x ∈ F.Xa a, Y x ∈ F.Xa (a - 1)) ∧
    ∀ x ∈ perpS S F.X, Y x ∈ F.X}

def FlagG.ell (F : FlagG S r T) (Y : S.V →ₗ[E] S.V) : E :=
  ∑ i : Fin r, F.coefX (Y (F.fvec i.succ)) i

def FlagG.dpsi (K : Type) [Field K] [Algebra K E] (F : FlagG S r T) (Y : S.V →ₗ[E] S.V) : K :=
  Algebra.trace K E (F.ell Y)

def Relevant (K : Type) [Field K] [Algebra K E] {T' : E} (F : FlagG S r T) (F' : FlagG S r T') :
    Prop :=
  ∀ Y ∈ F.LieN ∩ F'.LieN, F.dpsi K Y = F'.dpsi K Y

def xv (S : HSpace E) (x v : S.V) : S.V →ₗ[E] S.V where
  toFun y := brS S y v • x - brS S y x • v
  map_add' y y' := by simp only [brS, map_add (f := _), add_smul]; abel
  map_smul' c y := by simp [brS, map_smul, smul_sub, mul_smul]

def blockEnds {T' : E} (F : FlagG S r T) (F' : FlagG S r T') (j : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 j).filter (fun l => Dl F F' l ≠ 0)

def frameExp (r l : ℕ) : ℕ := ∑ a ∈ Finset.Icc 1 l, (r + 1 - a)

def Nloc (dd : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (r l : ℕ) (x : E) : ℚ :=
  FractionalIdeal.absNorm (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) x *
    dd ^ (-(2 * (frameExp r l : ℤ))))

def absReal (rd : ℝ) (τ : E →+* ℂ) (r l : ℕ) (x : E) : ℝ :=
  ‖τ x‖ * rd ^ (-(2 * (frameExp r l : ℝ)))

end Generic

section D7

variable (D : D7)

@[reducible] def starE : StarRing D.host.E := D.host.cmStar

attribute [local instance] starE

abbrev VS : HSpace D.host.E := D.sp.Y 0

abbrev FlagS (u : D.what₂.Word) : Type :=
  FlagG (VS D) D.R.rS ((((D.mem u).A.T : ℕ) : D.host.E))

def ddS : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E :=
  ((Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F)) :
    Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)

def embS (τ : D.what₂.Tau) : D.host.E →+* ℂ :=
  D.host.emb ((D.eTau τ : D.R.Psi) : D.R.GG)

end D7

end Formalism.MainNotions.S
end
end

section

noncomputable section

open ValuativeRel MeasureTheory ComplexConjugate ComplexOrder
open Formalism.MainNotions.S.Loc

namespace Formalism.MainNotions.ThinScalesBound


open scoped Classical in
def ThOK {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E) (m : ℕ) (s : ℕ+) (N : ℕ) (h : Fin N → Pt E m)
    (Th : E ⧸ M.Rsub → Fin N → Fin N → ℂ) : Prop :=
  let N0 := M.Kk m
  let Ns (t : Eˣ) (p q : Pt E m) :=
    ((M.modK ((t : E) * t) ^ ((s : ℕ) * ((s : ℕ) - 1) / 2) : ℝ) : ℂ) *
      M.Kk (m + s) (p.snoc t s) (q.snoc t s)

  (∀ x, (Matrix.of fun a b => Th x a b).PosSemidef) ∧

  (∀ x a b, M.detMod (h a) ≠ M.detMod (h b) → Th x a b = 0) ∧

  (∃ Λ : Submodule M.R E, IsCompact (Λ : Set E) ∧ IsOpen (Λ : Set E) ∧
    ∀ t ∉ Λ, ∀ a b, Th (Submodule.Quotient.mk t) a b = 0) ∧

  (∀ t : Eˣ, (Matrix.of fun a b => Th (Submodule.Quotient.mk (t : E)) a b -
      Ns t (h a) (h b)).PosSemidef) ∧

  (∀ c : ℝ, (Matrix.of fun (a b : {a : Fin N // M.detMod (h a) = c}) =>
      ((c⁻¹ ^ (2 * (s : ℕ)) : ℝ) : ℂ) * N0 (h a) (h b) - ∑' x : E ⧸ M.Rsub, Th x a b).PosSemidef) ∧

  ((s : ℕ) = 1 →
    (∀ (t : Eˣ) a b, Th (Submodule.Quotient.mk (t : E)) a b = Ns t (h a) (h b)) ∧
    ∀ a b, M.detMod (h a) = M.detMod (h b) →
      ∑' x : E ⧸ M.Rsub, Th x a b = ((M.detMod (h a))⁻¹ ^ 2 : ℝ) * N0 (h a) (h b)) ∧

  ((∀ a, M.InGLR (h a)) →
    (∀ a b, N0 (h a) (h b) = 1) ∧
    ∀ x, (Matrix.of fun a b => (if x = 0 then (1 : ℂ) else 0) * N0 (h a) (h b) -
      Th x a b).PosSemidef)

def FamilyTheoremThreePassage {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E) (r n : ℕ) : Prop :=
  ∀ (g : SplitG M.L), M.split = some g →
  ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V), Module.finrank E V = n →
  ∀ (t : Term V M r), H.IsTerm t →
  ∀ nn ∈ H.NGrp t.abelian₂ t.f, ∀ nn' ∈ H.NGrp t.abelian₂ t.f',
    (∀ x ∈ t.abelian₂, nn x - nn' x ∈ H.smulLat (algebraMap F E (g.q : F)) t.abelian₂) →
    ∃ uL uU : Matrix (Fin (r + 1)) (Fin (r + 1)) E,
      (∀ a b, uL a b ∈ M.R ∧ uU a b ∈ M.R) ∧
      (∀ a, uL a a = 1 ∧ uU a a = 1) ∧ (∀ a b, a < b → uL a b = 0 ∧ uU b a = 0) ∧
      H.ZZplus ⟨t.abelian₂, fun a => nn (t.f a), fun a => nn' (t.f' a), t.T, t.T'⟩ =
        uL * H.ZZplus t * uU

def FrameK {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ}
    (f : Fin (r + 1) → V) (T : F) : Prop :=
  (∀ a b : Fin (r + 1), (a ≠ Fin.last r ∨ b ≠ Fin.last r) → H.h (f a) (f b) = 0) ∧
    H.h (f (Fin.last r)) (f (Fin.last r)) = - algebraMap F E T

def FamilyLocalModel {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E) (r n : ℕ) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V), Module.finrank E V = n →
  ∀ (t₁ : Term V M r), H.IsGeneric t₁ →
  ∀ (f₂ f₂' : Fin (r + 1) → V)
    (φ : H.Wb t₁.f ≃ₗ[E] H.Wb f₂) (φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb f₂'),
    FrameK H f₂ t₁.T → FrameK H f₂' t₁.T' →
    H.Ident t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ φ φ' →
    H.SendsTo φ.toLinearMap 1 1 (t₁.f (Fin.last r)) (f₂ (Fin.last r)) →
    H.SendsTo φ'.toLinearMap 1 1 (t₁.f' (Fin.last r)) (f₂' (Fin.last r)) →
  let S : Set (Submodule M.L.O V) := {Λ₂ | H.IsGeneric ⟨Λ₂, f₂, f₂', t₁.T, t₁.T'⟩ ∧
    H.Respects t₁ ⟨Λ₂, f₂, f₂', t₁.T, t₁.T'⟩ φ φ'}
  let P₁ := H.ZZplus t₁
  let P₂ := HermSp.ZZplusOf M (H.Zhat f₂ f₂') t₁.T t₁.T'
  (H.Dl t₁.f t₁.f' r = 0 →
    ∀ (Z₁ Z₂ : M.Mat (r + 1)), Z₁.Z.map M.R.subtype = P₁ → Z₂.Z.map M.R.subtype = P₂ →
      Nat.card S = M.nIso Z₁ Z₂) ∧
  (IsUnit (H.Dl t₁.f t₁.f' r) →
    ∀ (Y₁ Y₂ : M.Mat r) (be₁ be₂ al₁ al₂ : Fin r → M.R),
      (∀ a b : Fin r, (Y₁.Z a b : E) = P₁ a.castSucc b.castSucc ∧
        (Y₂.Z a b : E) = P₂ a.castSucc b.castSucc) →
      (∀ a : Fin r, (be₁ a : E) = P₁ a.castSucc (Fin.last r) ∧ (be₂ a : E) = P₂ a.castSucc (Fin.last r) ∧
        (al₁ a : E) = P₁ (Fin.last r) a.castSucc ∧ (al₂ a : E) = P₂ (Fin.last r) a.castSucc) →
      Nat.card S = M.nIsoBA Y₁ Y₂ be₁ be₂ al₁ al₂)

def AllLoc (P : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E],
    Model F E → Prop) : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E), M.OK → P M

def T2 (D : Formalism.BasicNotions.D7) : Prop := AllLoc (fun M => FamilyLocalModel M D.R.rS D.R.r)

end Formalism.MainNotions.ThinScalesBound

end
end
