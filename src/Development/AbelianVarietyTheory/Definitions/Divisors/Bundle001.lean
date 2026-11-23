module

public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Basic.Complex.Basic
public import Mathlib.GroupTheory.Coset.Defs
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
public import Mathlib.NumberTheory.ModularForms.SlashActions
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Lean.Elab.AutoBound
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

set_option autoImplicit false
noncomputable section
open MvPolynomial NumberField
namespace GlobalTheory.ChowHt.Model


end GlobalTheory.ChowHt.Model
end
end

section

noncomputable section

namespace GlobalTheory.LKTorus

variable (k : Type) [Field k] {A : Type} [CommRing A] [Algebra k A]

def simT (c : A →ₐ[k] A) : Subgroup Aˣ where
  carrier := {x | ∃ t : kˣ, (x : A) * c x = algebraMap k A t}
  one_mem' := ⟨1, by simp⟩
  mul_mem' := by
    rintro x y ⟨s, hs⟩ ⟨t, ht⟩
    refine ⟨s * t, ?_⟩
    simp only [Units.val_mul, map_mul]
    rw [show (x : A) * y * (c x * c y) = (x * c x) * (y * c y) by ring, hs, ht]
  inv_mem' := by
    rintro x ⟨s, hs⟩
    refine ⟨s⁻¹, ?_⟩
    have h1 : ((x⁻¹ : Aˣ) : A) * c ((x⁻¹ : Aˣ) : A) * algebraMap k A s = 1 := by
      rw [← hs, show ((x⁻¹ : Aˣ) : A) * c ((x⁻¹ : Aˣ) : A) * ((x : A) * c x)
          = (((x⁻¹ : Aˣ) : A) * x) * c (((x⁻¹ : Aˣ) : A) * x) by rw [map_mul]; ring]
      simp
    calc ((x⁻¹ : Aˣ) : A) * c ((x⁻¹ : Aˣ) : A)
        = ((x⁻¹ : Aˣ) : A) * c ((x⁻¹ : Aˣ) : A) * (algebraMap k A s * algebraMap k A ((s⁻¹ : kˣ) : k)) := by
          rw [← map_mul, Units.mul_inv, map_one, mul_one]
      _ = algebraMap k A ((s⁻¹ : kˣ) : k) := by rw [← mul_assoc, h1, one_mul]

end GlobalTheory.LKTorus
end
end

section

noncomputable section

namespace GlobalTheory.LKRes

variable {H : Type} [Group H]

def conv (K : Subgroup H) (f f' : H → ℂ) (x : H) : ℂ :=
  ∑ᶠ q : H ⧸ K, f (Quotient.out q) * f' ((Quotient.out q)⁻¹ * x)

end GlobalTheory.LKRes
end
end

section

noncomputable section

open MvPolynomial
open scoped ContDiff

namespace GlobalTheory.PsCo.Pc1

abbrev Mat (n : ℕ) : Type := Matrix (Fin n) (Fin n) ℂ

abbrev Poly (n : ℕ) : Type := MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) ℂ

variable {n : ℕ}

def ev (g : Mat n) : Poly n →+* ℂ :=
  MvPolynomial.eval (Sum.elim (fun x : Fin n × Fin n => g x.1 x.2) (fun x => star (g x.1 x.2)))

abbrev Mode (ε : Fin n → Bool) : Type := {x : Fin n × Fin n // ε x.1 = true ∧ ε x.2 = false}

def nMode (ε : Fin n → Bool) : ℕ := Fintype.card (Mode ε)

def sg (ε : Fin n → Bool) (a : Fin n) : ℂ := if ε a then 1 else -1

def barM (ε : Fin n → Bool) (Z : Mat n) : Mat n := fun a b => -(sg ε a * sg ε b * Z b a)

def LieU (ε : Fin n → Bool) (Z : Mat n) : Prop := ∀ a b, (starRingEnd ℂ) (Z a b) = barM ε Z a b

def dZ (ε : Fin n → Bool) (Z : Mat n) : Derivation ℂ (Poly n) (Poly n) :=
  mkDerivation ℂ (Sum.elim
    (fun x : Fin n × Fin n => ∑ c, (X (Sum.inl (x.1, c)) * C (Z c x.2) - C (Z x.1 c) * X (Sum.inl (c, x.2))))
    (fun x : Fin n × Fin n =>
      ∑ c, (X (Sum.inr (x.1, c)) * C (barM ε Z c x.2) - C (barM ε Z x.1 c) * X (Sum.inr (c, x.2)))))

def dM (ε : Fin n → Bool) (x : Mode ε) : Derivation ℂ (Poly n) (Poly n) := dZ ε (Matrix.single x.1.2 x.1.1 1)

def rM (ε : Fin n → Bool) (g : Mat n) : ℝ := ∑ x : Mode ε, ‖g x.1.1 x.1.2‖ ^ 2

def rP (ε : Fin n → Bool) : Poly n := ∑ x : Mode ε, X (Sum.inl x.1) * X (Sum.inr x.1)

def OmP (ε : Fin n → Bool) : Matrix (Mode ε) (Mode ε) (Poly n) := fun x y => dM ε x (X (Sum.inr y.1))

def detbP (n : ℕ) : Poly n := (Matrix.of fun a b : Fin n => (X (Sum.inr (a, b)) : Poly n)).det

def blockAlg (ε : Fin n → Bool) : Subalgebra ℂ (Poly n) :=
  Algebra.adjoin ℂ {P | ∃ a b, ε a = ε b ∧ P = X (Sum.inl (a, b))}

def topP (ε : Fin n → Bool) (M : ℕ) (P : Poly n) : Poly n := detbP n ^ M * P * (OmP ε).det

def prev (q : ℕ → Poly n) : ℕ → Poly n
  | 0 => 0
  | k + 1 => q k

def IsKoszul (ε : Fin n → Bool) (p : ℕ → Poly n) (q : Mode ε → ℕ → Poly n) : Prop :=
  (∀ k : ℕ, ((k : Poly n) + 1) * p (k + 1) + rP ε * p k = ∑ x, (dM ε x (q x k) + dM ε x (rP ε) * prev (q x) k)) ∧
    (∀ k, nMode ε < k → p k = 0) ∧ ∀ x k, nMode ε ≤ k → q x k = 0

def IsCutFn (H : ℝ → ℝ) : Prop := ContDiff ℝ ∞ H ∧ ∃ R : ℝ, ∀ x, R ≤ x → H x = 0

def bas (ε : Fin n → Bool) (H : ℝ → ℝ) (P : Poly n) : Mat n → ℂ := fun g => (H (rM ε g) : ℂ) * ev g P

def adBas (ε : Fin n → Bool) (Z : Mat n) (H : ℝ → ℝ) (P : Poly n) : Mat n → ℂ := fun g =>
  bas ε (deriv H) (dZ ε Z (rP ε) * P) g + bas ε H (dZ ε Z P) g

def ShapeM (ε : Fin n → Bool) (d : ℕ) : Submodule ℂ (Mat n → ℂ) :=
  Submodule.span ℂ {φ | ∃ (H : ℝ → ℝ) (P : Poly n), IsCutFn H ∧ P.totalDegree ≤ d ∧ φ = bas ε H P}

def AdSpanM (ε : Fin n → Bool) : Submodule ℂ (Mat n → ℂ) :=
  Submodule.span ℂ {φ | ∃ (Z : Mat n) (H : ℝ → ℝ) (P : Poly n), LieU ε Z ∧ IsCutFn H ∧ φ = adBas ε Z H P}

def IsProfile (N : ℕ) (G : ℝ → ℝ) : Prop :=
  ContDiff ℝ ∞ G ∧ (∀ x, 1 ≤ x → G x = 0) ∧ (∀ x, 0 ≤ iteratedDeriv N G x) ∧ 0 < iteratedDeriv N G 0

def famF (ε : Fin n → Bool) (G : ℝ → ℝ) (p : ℕ → Poly n) (t : ℝ) : Mat n → ℂ := fun g =>
  ∑ k ∈ Finset.range (nMode ε + 1), bas ε (iteratedDeriv k fun x => G (t * x)) (p k) g

def dMode (ε : Fin n → Bool) (θ : Fin n → ℝ) : ℝ :=
  ∏ x : Mode ε, ‖Complex.exp (θ x.1.1 * Complex.I) - Complex.exp (θ x.1.2 * Complex.I)‖ ^ 2

def StAlg : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (M : ℕ) (P : Poly n), P ∈ blockAlg ε →
    ∃ (p : ℕ → Poly n) (q : Mode ε → ℕ → Poly n), IsKoszul ε p q ∧ p (nMode ε) = topP ε M P

def StProfile : Prop := ∀ N : ℕ, ∃ G : ℝ → ℝ, IsProfile N G

def StFam : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (G : ℝ → ℝ) (p : ℕ → Poly n), IsProfile (nMode ε) G →
    ∃ d : ℕ, (∀ k, k ≤ nMode ε → (p k).totalDegree ≤ d) ∧
      ∀ t : ℝ, 0 < t → famF ε G p t ∈ ShapeM ε d ∧ ∀ g : Mat n, 1 < t * rM ε g → famF ε G p t g = 0

def StHomot : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (G : ℝ → ℝ) (p : ℕ → Poly n) (q : Mode ε → ℕ → Poly n), IsProfile (nMode ε) G →
    IsKoszul ε p q → ∀ t : ℝ, 1 ≤ t → famF ε G p 1 - famF ε G p t ∈ AdSpanM ε

def StBasDeriv : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (Z : Mat n) (H : ℝ → ℝ) (P : Poly n), LieU ε Z → IsCutFn H →
    adBas ε Z H P ∈ ShapeM ε (P.totalDegree + 2) ∧ ∀ (g : Mat n) (s : ℝ),
      HasDerivAt (fun u : ℝ => bas ε H P (NormedSpace.exp (-((u : ℂ) • Z)) * g * NormedSpace.exp ((u : ℂ) • Z)))
        (adBas ε Z H P (NormedSpace.exp (-((s : ℂ) • Z)) * g * NormedSpace.exp ((s : ℂ) • Z))) s

end GlobalTheory.PsCo.Pc1

end

section

noncomputable section

open MvPolynomial

namespace GlobalTheory.PsCo.Pc1.A

abbrev EntIdx (n : ℕ) := (Fin n × Fin n) ⊕ (Fin n × Fin n)

abbrev PolyL (n L : ℕ) := MvPolynomial (Fin L ⊕ EntIdx n) ℂ

abbrev PolyM (n L : ℕ) := MvPolynomial (Option (Fin L ⊕ EntIdx n)) ℂ

variable {n L : ℕ}

def inL (n L : ℕ) : Poly n →ₐ[ℂ] PolyL n L := rename Sum.inr

def inM (n L : ℕ) : PolyL n L →ₐ[ℂ] PolyM n L := rename some

def laL (n : ℕ) (i : Fin L) : PolyL n L := X (Sum.inl i)

def muM (n L : ℕ) : PolyM n L := X none

def dL (L : ℕ) (ε : Fin n → Bool) (x : Mode ε) : Derivation ℂ (PolyL n L) (PolyL n L) :=
  mkDerivation ℂ (Sum.elim (fun _ => 0) (fun v => inL n L (dM ε x (X v))))

def dMu (L : ℕ) (ε : Fin n → Bool) (x : Mode ε) : Derivation ℂ (PolyM n L) (PolyM n L) :=
  mkDerivation ℂ (fun w => match w with
    | none => 0
    | some v => inM n L (dL L ε x (X v)))

def coefM (n L : ℕ) (k : ℕ) : PolyM n L →ₗ[ℂ] PolyL n L :=
  ((Polynomial.lcoeff (PolyL n L) k).restrictScalars ℂ).comp (optionEquivLeft ℂ (Fin L ⊕ EntIdx n)).toLinearMap

def allOnes (L : ℕ) : Fin L →₀ ℕ := Finsupp.equivFunOnFinite.symm fun _ => 1

def exL (n L : ℕ) : PolyL n L →ₗ[ℂ] Poly n :=
  ((MvPolynomial.lcoeff (Poly n) (allOnes L)).restrictScalars ℂ).comp (sumAlgEquiv ℂ (Fin L) (EntIdx n)).toLinearMap

end GlobalTheory.PsCo.Pc1.A

end
end

section

noncomputable section

open MvPolynomial GlobalTheory.PsCo.Pc1 GlobalTheory.PsCo.Pc1.A

namespace GlobalTheory.PsCo.Cw2a

def T_dual_prod : Prop := ∀ {A : Type} [CommRing A] [Algebra ℂ A] (D : Derivation ℂ A A) {L : ℕ} (la m : Fin L → A)
    (J : Ideal A), (∀ i, D (la i) = 0) → (∀ i, la i ^ 2 ∈ J) →
    D (∏ i, (1 + la i * m i)) - (∏ i, (1 + la i * m i)) * ∑ i, la i * D (m i) ∈ J

def T_dM_comm : Prop := ∀ {n : ℕ} (ε : Fin n → Bool) (w x : Mode ε) (P : Poly n), dM ε w (dM ε x P) = dM ε x (dM ε w P)

def BlockDeterminantCondition : Prop := ∀ {n : ℕ} (ε : Fin n → Bool) (a b : Fin n), ε a = ε b →
    ∃ c : Mode ε → Mode ε → ℂ, ∀ x, dM ε x (X (Sum.inl (a, b))) = ∑ y, C (c x y) * X (Sum.inl y.1)

def T_dM_detb : Prop := ∀ {n : ℕ} (ε : Fin n → Bool) (x : Mode ε), dM ε x (detbP n) = 0

def T_exL_dL : Prop := ∀ {n L : ℕ} (ε : Fin n → Bool) (x : Mode ε) (b : PolyL n L),
    exL n L (dL L ε x b) = dM ε x (exL n L b)

def T_exL_dual : Prop := ∀ {n L : ℕ} (m : Fin L → Poly n) (a : Poly n),
    exL n L ((∏ i, (1 + laL n i * inL n L (m i))) * inL n L a) = (∏ i, m i) * a

def T_coefM_dMu : Prop := ∀ {n L : ℕ} (ε : Fin n → Bool) (x : Mode ε) (k : ℕ) (s : PolyM n L),
    coefM n L k (dMu L ε x s) = dL L ε x (coefM n L k s)

def T_coefM_pderiv : Prop := ∀ {n L : ℕ} (k : ℕ) (s : PolyM n L),
    coefM n L k (pderiv none s) = ((k : ℂ) + 1) • coefM n L (k + 1) s

def T_coefM_pencil : Prop := ∀ {n L : ℕ} {I : Type} [Fintype I] [DecidableEq I] (A0 B0 : Matrix I I (PolyL n L)),
    let Z : Matrix I I (PolyM n L) := fun x y => muM n L * inM n L (A0 x y) + inM n L (B0 x y)
    (∀ k, Fintype.card I < k → coefM n L k Z.det = 0) ∧ coefM n L (Fintype.card I) Z.det = A0.det ∧
      ∀ k x y, Fintype.card I ≤ k → coefM n L k (Z.adjugate y x) = 0

end GlobalTheory.PsCo.Cw2a

end
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace GlobalTheory.SSG

def ChartAt {O : Type} [CommRing O] (ϖ : O) {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of O)) (x : X) : Prop :=
  ∃ (U : X.Opens) (_ : IsAffineOpen U) (_ : x ∈ U) (m r : ℕ) (_ : 1 ≤ r) (_ : r ≤ m)
    (ψ : (MvPolynomial (Fin m) O ⧸ Ideal.span (Set.singleton
      ((∏ i ∈ Finset.univ.filter (fun i : Fin m => (i : ℕ) < r), MvPolynomial.X i) -
        MvPolynomial.C ϖ))) →+* Γ(X, U)),
    ψ.Etale ∧ ψ.comp (algebraMap O _) = ((Scheme.ΓSpecIso (CommRingCat.of O)).inv ≫ p.appLE ⊤ U le_top).hom

end GlobalTheory.SSG

end
end

section

noncomputable section

open scoped UpperHalfPlane MatrixGroups ModularForm

namespace GlobalTheory.QFam

def HasQ (N : ℕ) (f : ℍ → ℂ) (a : ℕ → ℂ) : Prop :=
  ∀ τ : ℍ, HasSum (fun n : ℕ => a n * Complex.exp (2 * Real.pi * Complex.I * n * τ / N)) (f τ)

def IsFam {ι : Type} (act : ι → SL(2, ℤ) → ι) (w : ℤ) (f : ι → ℍ → ℂ) : Prop :=
  ∀ (i : ι) (γ : SL(2, ℤ)), (f i) ∣[w] γ = f (act i γ)

def IsRAct {ι : Type} (act : ι → SL(2, ℤ) → ι) : Prop :=
  (∀ i, act i 1 = i) ∧ ∀ i γ δ, act (act i γ) δ = act i (γ * δ)

def ActBij {ι : Type} (act : ι → SL(2, ℤ) → ι) : Prop :=
  ∀ γ, Function.Bijective fun i => act i γ

def conv (a b : ℕ → ℂ) (n : ℕ) : ℂ := ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, a p.1 * b p.2

def spread (M : ℕ) (a : ℕ → ℂ) (n : ℕ) : ℂ := if M ∣ n then a (n / M) else 0

def QAll (p : ℂ → Prop) (N : ℕ) (f : ℍ → ℂ) : Prop := ∃ a, HasQ N f a ∧ ∀ n, p (a n)

def QConj (g : ℂ ≃+* ℂ) (N : ℕ) (f f' : ℍ → ℂ) : Prop := ∃ a, HasQ N f a ∧ HasQ N f' fun n => g (a n)

def tauPair (τ : ℍ) : PeriodPair where
  ω₁ := τ
  ω₂ := 1
  indep := by
    rw [LinearIndependent.pair_iff]
    intro s t h
    have him := congrArg Complex.im h
    have hre := congrArg Complex.re h
    have hs : s = 0 := by
      have : s * τ.im = 0 := by simpa using him
      exact (mul_eq_zero.mp this).resolve_right τ.im_pos.ne'
    subst hs
    exact ⟨rfl, by simpa using hre⟩

theorem IsRAct.actBij {ι : Type} {act : ι → SL(2, ℤ) → ι} (h : IsRAct act) : ActBij act := by
  obtain ⟨hone, hmul⟩ := h
  intro γ
  refine Function.bijective_iff_has_inverse.mpr ⟨fun i => act i γ⁻¹, fun i => ?_, fun i => ?_⟩
  · show act (act i γ) γ⁻¹ = i
    rw [hmul, mul_inv_cancel, hone]
  · show act (act i γ⁻¹) γ = i
    rw [hmul, inv_mul_cancel, hone]

theorem hasQ_iff (N : ℕ) (f : ℍ → ℂ) (a : ℕ → ℂ) :
    HasQ N f a ↔ ∀ τ : ℍ, HasSum (fun n : ℕ => a n * Complex.exp (2 * Real.pi * Complex.I * τ / N) ^ n) (f τ) := by
  have key : ∀ (τ : ℍ) (n : ℕ), Complex.exp (2 * Real.pi * Complex.I * n * τ / N)
      = Complex.exp (2 * Real.pi * Complex.I * τ / N) ^ n := by
    intro τ n
    rw [← Complex.exp_nat_mul]
    congr 1
    ring
  simp only [HasQ, key]

end GlobalTheory.QFam
end
end

section

noncomputable section

open NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.HenQ

def eulerL (K : Type) [Field K] [NumberField K] (B : HeightOneSpectrum (𝓞 K) → Multiset ℂ)
    (S : Set (HeightOneSpectrum (𝓞 K))) (s : ℂ) : ℂ :=
  ∏' w : {w : HeightOneSpectrum (𝓞 K) // w ∉ S},
    ((B w.1).map fun b => (1 - b * ((Ideal.absNorm w.1.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹).prod

def eulerLd (K : Type) [Field K] [NumberField K] (B : HeightOneSpectrum (𝓞 K) → Multiset ℂ)
    (S : Set (HeightOneSpectrum (𝓞 K))) (s : ℂ) : ℂ :=
  eulerL K (fun w => (B w).map (·⁻¹)) S (1 - s)

end GlobalTheory.HenQ
end
end

section

noncomputable section

namespace GlobalTheory.JSW

def colGL {R : Type} [CommRing R] {a : ℕ} (r : ℕ) (x : Fin a → R) : GL (Fin a) R :=
  ⟨1 + Matrix.of (fun i j : Fin a => if (j : ℕ) = r ∧ (i : ℕ) < r then x i else 0),
   1 - Matrix.of (fun i j : Fin a => if (j : ℕ) = r ∧ (i : ℕ) < r then x i else 0),
   by
    have h : Matrix.of (fun i j : Fin a => if (j : ℕ) = r ∧ (i : ℕ) < r then x i else 0) *
        Matrix.of (fun i j : Fin a => if (j : ℕ) = r ∧ (i : ℕ) < r then x i else 0) = 0 := by
      refine Matrix.ext fun i j => ?_
      simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.zero_apply]
      refine Finset.sum_eq_zero fun k _ => ?_
      by_cases hk : (k : ℕ) = r
      · simp [hk]
      · simp [hk]
    rw [mul_sub, add_mul, add_mul, one_mul, mul_one, one_mul, h]; abel,
   by
    have h : Matrix.of (fun i j : Fin a => if (j : ℕ) = r ∧ (i : ℕ) < r then x i else 0) *
        Matrix.of (fun i j : Fin a => if (j : ℕ) = r ∧ (i : ℕ) < r then x i else 0) = 0 := by
      refine Matrix.ext fun i j => ?_
      simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.zero_apply]
      refine Finset.sum_eq_zero fun k _ => ?_
      by_cases hk : (k : ℕ) = r
      · simp [hk]
      · simp [hk]
    rw [sub_mul, mul_add, mul_add, one_mul, mul_one, one_mul, h]; abel⟩

def mirSet (R : Type) [CommRing R] (m : ℕ) : Set (GL (Fin (m + 1)) R) :=
  {g | ∀ j, (g : Matrix (Fin (m + 1)) (Fin (m + 1)) R) (Fin.last m) j = if j = Fin.last m then 1 else 0}


end GlobalTheory.JSW
end
end
