module

public import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle032
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle004
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsIsoQuotToImOmegaLieOfSplit
public import Mathlib.RingTheory.LaurentSeries
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsUnitaryMulTriangular
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
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle029
import Mathlib.Tactic.Polynomial.Basic

@[expose] public section

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompHt.Test

open MvPolynomial NumberField IsDedekindDomain Module Filter GlobalTheory.ChowHt GlobalTheory.AllWt GlobalTheory.CompHt
open scoped ENNReal


set_option autoImplicit false in
open MvPolynomial NumberField IsDedekindDomain Module Filter in
open scoped ENNReal in
theorem _root_.GlobalTheory.CompHt.Test.imageDeg_zero {K V Ω : Type} [Field K] [AddCommGroup V] [Module K V]
    [Field Ω] [Algebra K Ω] (D : ℕ) :
    _root_.GlobalTheory.CompHt.imageDeg (0 : V →ₗ[K] Ω) D = 0 := by
  by_contra hne
  obtain ⟨N, b, f, hf⟩ := (_root_.GlobalTheory.CompHt.imageDeg_pos_iff _ D).1 (Nat.pos_of_ne_zero hne)
  obtain ⟨y, hy, hI⟩ := hf.exists_point
  apply hy
  funext i
  have hX : (X i : MvPolynomial (Fin N) K) ∈ _root_.GlobalTheory.CompHt.imageIdeal (0 : V →ₗ[K] Ω) b := by
    unfold _root_.GlobalTheory.CompHt.imageIdeal
    rw [_root_.GlobalTheory.CompHt.mem_coneIdeal_of_isHomogeneous _ (isHomogeneous_X K i)]
    simp
  simpa using hI _ hX

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

variable (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)

end GlobalTheory.CompHt.Test
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

namespace GlobalTheory.Nef

def evAt {R : Type} [CommRing R] {X : Scheme.{0}} (ξ : Sp R ⟶ X) {U : X.Opens} (h : ⊤ ≤ ξ ⁻¹ᵁ U) : Γ(X, U) →+* R :=
  (Scheme.ΓSpecIso (.of R)).hom.hom.comp (ξ.appLE U ⊤ h).hom

section Path

variable {S : Scheme.{0}} (G : Over S) [GrpObj G] {R : Type} [CommRing R]

def sqr : G.left ⟶ G.left := (𝟙 G * 𝟙 G : G ⟶ G).left

def triv (b : Sp R ⟶ S) : Sp (PowerSeries R) ⟶ G.left := spMap (PowerSeries.C (R := R)) ≫ b ≫ unitSec G

structure IsPath (c : R) (b : Sp R ⟶ S) (ξ : Sp (PowerSeries R) ⟶ G.left) : Prop where

  base : ξ ≫ G.hom = spMap (PowerSeries.C (R := R)) ≫ b

  zero : spMap (PowerSeries.constantCoeff (R := R)) ≫ ξ = b ≫ unitSec G

  scale : spMap (PowerSeries.rescale c) ≫ ξ = ξ ≫ sqr G

def HasTan {n : ℕ} (b : Sp R ⟶ S) (ξ : Sp (PowerSeries R) ⟶ G.left) {V : S.Opens} (τ : Fin n → Γ(Lie G, V))
    (w : Fin n → R) : Prop :=
  ∀ (U : G.left.Opens) (hU : ⊤ ≤ ξ ⁻¹ᵁ U) (V' : S.Opens) (hV : V' ≤ V) (he : V' ≤ unitSec G ⁻¹ᵁ U)
    (hb : ⊤ ≤ b ⁻¹ᵁ V') (f : Γ(G.left, U)),
    PowerSeries.coeff 1 (evAt ξ hU f) = ∑ i, w i * evAt b hb (dualApp (τ i) hV (dUnit G he f))

structure StalkData (s : S) (π : S.presheaf.stalk s →+* G.left.presheaf.stalk (unitSec G s))
    (ε : G.left.presheaf.stalk (unitSec G s) →+* S.presheaf.stalk s)
    (m : G.left.presheaf.stalk (unitSec G s) →+* G.left.presheaf.stalk (unitSec G s)) : Prop where

  str : Spec.map (CommRingCat.ofHom π) ≫ S.fromSpecStalk s = G.left.fromSpecStalk _ ≫ G.hom

  unit : Spec.map (CommRingCat.ofHom ε) ≫ G.left.fromSpecStalk _ = S.fromSpecStalk s ≫ unitSec G

  sq : Spec.map (CommRingCat.ofHom m) ≫ G.left.fromSpecStalk _ = G.left.fromSpecStalk _ ≫ sqr G

end Path

def IsRatPath {F : Type} [Field F] {Y : Scheme.{0}} (ξ : Sp (PowerSeries F) ⟶ Y) : Prop :=
  ∃ β : Sp (RatFunc F) ⟶ Y, spMap (algebraMap (RatFunc F) (LaurentSeries F)) ≫ β =
    spMap (algebraMap (PowerSeries F) (LaurentSeries F)) ≫ ξ

def RatRigid {S : Scheme.{0}} (G : Over S) [GrpObj G] {F : Type} [Field F] (b : Sp F ⟶ S) : Prop :=
  ∀ ξ : Sp (PowerSeries F) ⟶ G.left, IsPath G 2 b ξ → IsRatPath ξ → ξ = triv G b

def LocFrame {k K : Type} [Field k] [Field K] [Algebra k K] {C : Scheme.{0}} (x : Sp K ⟶ C) {W : C.Modules} {r : ℕ}
    {V₀ : C.Opens} (s : Fin r → Γ(W, V₀)) (v : Place k K) (g : Matrix (Fin r) (Fin r) K) : Prop :=
  ∃ (b : Sp v.O ⟶ C) (V : C.Opens) (t : Fin r → Γ(W, V)) (V' : C.Opens) (h₀ : V' ≤ V₀) (h₁ : V' ≤ V)
    (hx : ⊤ ≤ x ⁻¹ᵁ V') (M : Matrix (Fin r) (Fin r) Γ(C, V')),
    spMap v.O.subtype ≫ b = x ∧ ⊤ ≤ b ⁻¹ᵁ V ∧ IsFrame t ∧
      (∀ j, resM W h₀ (s j) = ∑ i, M i j • resM W h₁ (t i)) ∧ g = M.map (evAt x hx)

def IsGenOver (k : Type) {K : Type} [Field k] [Field K] [Algebra k K] {C : Scheme.{0}} [Algebra k Γ(C, ⊤)]
    (x : Sp K ⟶ C) : Prop :=
  NeronCurve.IsCurve k C ∧ NeronCurve.IsGen x ∧ x ≫ strHom k C = spMap (algebraMap k K)

theorem triv_over {S : Scheme.{0}} (G : Over S) [GrpObj G] {R : Type} [CommRing R] (b : Sp R ⟶ S) :
    triv G b ≫ G.hom = spMap (PowerSeries.C (R := R)) ≫ b := by
  rw [triv, Category.assoc, Category.assoc, sec_hom, Category.comp_id]

end GlobalTheory.Nef
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap)
open GlobalTheory.DeRham GlobalTheory.PDiv

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

variable {R : Type} [CommRing R]

abbrev RootFn (X : Over (Sp R)) (D : Type) [CommRing D] [Algebra R D] : Type 1 :=
  ∀ (D' : Type) [CommRing D'] [Algebra R D'], (D →ₐ[R] D') → Pt X D' → D'

variable {A : Over (Sp R)} [GrpObj A]


def HasRoots (A : Over (Sp R)) [GrpObj A] (n : ℕ) : Prop :=
  ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt A D), ∃ (D' : Type) (_ : CommRing D') (_ : Algebra R D')
    (ψ : D →ₐ[R] D') (z : Pt A D'), (ψ : D →+* D').FaithfullyFlat ∧ (z ^ n : Pt A D') = spOver ψ ≫ x

def IsTorsChar (n : ℕ) (b : Fn0 A) : Prop :=
  (∀ (D : Type) [CommRing D] [Algebra R D] (D' : Type) [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D') (w : Pt A D),
    w ^ n = 1 → b D' (spOver φ ≫ w) = φ (b D w)) ∧
  ∀ (D : Type) [CommRing D] [Algebra R D] (w w' : Pt A D), w ^ n = 1 → w' ^ n = 1 → b D (w * w') = b D w + b D w'

def IsSec (n : ℕ) (b : Fn0 A) {D : Type} [CommRing D] [Algebra R D] (x : Pt A D) (s : RootFn A D) : Prop :=
  (∀ (D' : Type) [CommRing D'] [Algebra R D'] (D'' : Type) [CommRing D''] [Algebra R D''] (φ : D →ₐ[R] D')
    (ψ : D' →ₐ[R] D'') (z : Pt A D'), z ^ n = spOver φ ≫ x → s D'' (ψ.comp φ) (spOver ψ ≫ z) = ψ (s D' φ z)) ∧
  ∀ (D' : Type) [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D') (z w : Pt A D'),
    z ^ n = spOver φ ≫ x → w ^ n = 1 → s D' φ (z * w) = s D' φ z + b D' w

abbrev SecFam (X : Over (Sp R)) : Type 1 := ∀ (D : Type) [CommRing D] [Algebra R D], Pt X D → RootFn X D

def IsSecDiff (n : ℕ) (S : SecFam A) (u : Fn1 A) : Prop :=
  ∀ (D : Type) [CommRing D] [Algebra R D] (D' : Type) [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D') (x : Pt A D)
    (E : Type) [CommRing E] [Algebra R E] (ψ : D' →ₐ[R] E) (z : Pt A E), z ^ n = spOver ψ ≫ spOver φ ≫ x →
    ψ (u D D' φ x) = S D' (spOver φ ≫ x) E ψ z - S D x E (ψ.comp φ) z

def IsSecAdd (n : ℕ) (S : SecFam A) (g : Fn2 A) : Prop :=
  ∀ (D : Type) [CommRing D] [Algebra R D] (x y : Pt A D) (E : Type) [CommRing E] [Algebra R E] (ψ : D →ₐ[R] E)
    (z w : Pt A E), z ^ n = spOver ψ ≫ x → w ^ n = spOver ψ ≫ y →
    ψ (g D x y) = S D (x * y) E ψ (z * w) - S D x E ψ z - S D y E ψ w


variable (R) in
def diagSum (D : Type) [CommRing D] [Bialgebra R D] [Coalgebra.IsCocomm R D] (m : ℕ) : D ⊗[R] D →ₗ[R] D :=
  ∑ i ∈ Finset.range m, (Algebra.TensorProduct.lift (mulBy R D i : D →ₐ[R] D) (AlgHom.id R D)
    fun _ _ ↦ Commute.all _ _).toLinearMap

theorem diagSum_tmul (D : Type) [CommRing D] [Bialgebra R D] [Coalgebra.IsCocomm R D] (m : ℕ) (a b : D) :
    diagSum R D m (a ⊗ₜ b) = ∑ i ∈ Finset.range m, mulBy R D i a * b := by
  simp [diagSum, LinearMap.sum_apply]

end GlobalTheory.PtExt
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

variable {R : Type} [CommRing R]

def Fn1.pull {X Y : Over (Sp R)} (q : Y ⟶ X) (u : Fn1 X) : Fn1 Y := fun D _ _ D' _ _ φ y ↦ u D D' φ (y ≫ q)

section Alg

variable {D E E' : Type} [CommRing D] [Algebra R D] [CommRing E] [Algebra R E] [CommRing E'] [Algebra R E']

def ptAlg (z : Pt (SpAlg R D) E) : D →ₐ[R] E :=
  { (Spec.preimage (R := CommRingCat.of D) (S := CommRingCat.of E) z.left).hom with
    commutes' := fun r ↦ by
      have h : CommRingCat.ofHom (algebraMap R D) ≫
          Spec.preimage (R := CommRingCat.of D) (S := CommRingCat.of E) z.left =
          CommRingCat.ofHom (algebraMap R E) := by
        apply Spec.map_injective
        rw [Spec.map_comp, Spec.map_preimage]
        exact Over.w z
      exact congrArg (fun f ↦ CommRingCat.Hom.hom f r) h }

theorem spOver_ptAlg (z : Pt (SpAlg R D) E) : spOver (ptAlg z) = z := by
  apply Over.OverMorphism.ext
  rw [spOver_left]
  exact Spec.map_preimage (R := CommRingCat.of D) (S := CommRingCat.of E) z.left

theorem ptAlg_spOver (α : D →ₐ[R] E) : ptAlg (spOver α) = α := by
  refine AlgHom.ext fun r ↦ ?_
  change (Spec.preimage (R := CommRingCat.of D) (S := CommRingCat.of E) (spOver α).left).hom r = α r
  rw [spOver_left]
  exact congrArg (fun f ↦ CommRingCat.Hom.hom f r) (Spec.preimage_map (CommRingCat.ofHom (α : D →+* E)))

theorem ptAlg_comp (ψ : E →ₐ[R] E') (z : Pt (SpAlg R D) E) : ptAlg (spOver ψ ≫ z) = ψ.comp (ptAlg z) := by
  conv_lhs => rw [← spOver_ptAlg z, spOver_comp]
  exact ptAlg_spOver _

def epsEv (e : Pt (epsR R) E) : DualNumber E →ₐ[R] E :=
  DualNumber.lift ⟨(AlgHom.id R E, ptAlg (D := DualNumber R) e DualNumber.eps), by
    rw [← map_mul, DualNumber.eps_mul_eps, map_zero], fun _ ↦ Commute.all _ _⟩

end Alg

section Param

variable {A B : Over (Sp R)} {J : Type} [Fintype J] {D : Type} [CommRing D] [Algebra R D]

def sumMul (d : J → D) (b : J → Fn1 B) : Fn1 (SpAlg R D ⊗ B) := fun E _ _ E' _ _ ψ z ↦
  ∑ i, ψ (ptAlg (z ≫ fst _ _) (d i)) * b i E E' ψ (z ≫ snd _ _)

def IsCupCob {K : Type} (W : K → (A ⊗ B).left.Opens) (a : J → Fn1 A) (b : J → Fn1 B) (n : Fn1 (A ⊗ B)) : Prop :=
  ∀ (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E'] (E'' : Type) [CommRing E'']
    [Algebra R E''] (φ : E →ₐ[R] E') (ψ : E' →ₐ[R] E'') (z : Pt (A ⊗ B) E), Sm W z →
    ψ (n E E' φ z) - n E E'' (ψ.comp φ) z + n E' E'' ψ (spOver φ ≫ z) =
      ∑ i, ψ (a i E E' φ (z ≫ fst _ _)) * b i E' E'' ψ (spOver φ ≫ z ≫ snd _ _)

def parCoc (a : J → Fn1 A) (b : J → Fn1 B) (n : Fn1 (A ⊗ B)) (x : Pt A D) : Fn1 (SpAlg R D ⊗ B) :=
  fun E _ _ E' _ _ ψ z ↦ n E E' ψ (z ≫ x ▷ B) -
    ∑ i, ψ (a i D E (ptAlg (z ≫ fst _ _)) x) * b i E E' ψ (z ≫ snd _ _)

def parCov {K : Type} (W : K → (A ⊗ B).left.Opens) (x : Pt A D) : K → (SpAlg R D ⊗ B).left.Opens :=
  fun i ↦ (x ▷ B).left ⁻¹ᵁ W i

end Param

section Change

variable {R' : Type} [CommRing R'] (σ : R →+* R')

@[reducible] def algVia (E : Type) [CommRing E] [Algebra R' E] : Algebra R E :=
  ((algebraMap R' E).comp σ).toAlgebra

def homVia {E E' : Type} [CommRing E] [Algebra R' E] [CommRing E'] [Algebra R' E'] (ψ : E →ₐ[R'] E') :
    @AlgHom R E E' _ _ _ (algVia σ E) (algVia σ E') :=
  @AlgHom.mk R E E' _ _ _ (algVia σ E) (algVia σ E') (ψ : E →+* E') fun r ↦ ψ.commutes (σ r)

variable {σ} {X : Over (Sp R)} {X' : Over (Sp R')} {q : X'.left ⟶ X.left}

def ptVia (w : q ≫ X.hom = X'.hom ≫ spMap σ) {E : Type} [CommRing E] [Algebra R' E] (y : Pt X' E) :
    @Pt R _ X E _ (algVia σ E) :=
  Over.homMk (y.left ≫ q) (by
    have h : y.left ≫ X'.hom = spMap (algebraMap R' E) := Over.w y
    change (y.left ≫ q) ≫ X.hom = spMap ((algebraMap R' E).comp σ)
    rw [Category.assoc, w, ← Category.assoc, h, Cris.spMap_comp])

def bcPull (w : q ≫ X.hom = X'.hom ≫ spMap σ) (u : Fn1 X) : Fn1 X' := fun E _ _ E' _ _ ψ y ↦
  @u E _ (algVia σ E) E' _ (algVia σ E') (homVia σ ψ) (ptVia w y)

end Change

section Gen

variable {X Y : Over (Sp R)}

def IsPtGen (L : LB X.left) (q : Y ⟶ X)
    (t : ∀ (E : Type) [CommRing E] [Algebra R E], Pt Y E → L.ι → E) : Prop :=
  (∀ (E : Type) [CommRing E] [Algebra R E] (z : Pt Y E) (i : L.ι), ⊤ ≤ (z ≫ q).left ⁻¹ᵁ L.U i → IsUnit (t E z i)) ∧
  (∀ (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E'] (ψ : E →ₐ[R] E') (z : Pt Y E)
    (i : L.ι), ⊤ ≤ (z ≫ q).left ⁻¹ᵁ L.U i → t E' (spOver ψ ≫ z) i = ψ (t E z i)) ∧
  ∀ (E : Type) [CommRing E] [Algebra R E] (z : Pt Y E) (i j : L.ι), ⊤ ≤ (z ≫ q).left ⁻¹ᵁ L.U i →
    ⊤ ≤ (z ≫ q).left ⁻¹ᵁ L.U j → t E z i = evU (z ≫ q).left (L.U i ⊓ L.U j) (L.g i j).val * t E z j

variable {A B : Over (Sp R)} [GrpObj A] [GrpObj B]

def IsEpsGen (P : LB (A ⊗ B).left) (v : epsR R ⟶ B)
    (T : ∀ (E : Type) [CommRing E] [Algebra R E], Pt A E → P.ι → DualNumber E) : Prop :=
  (∀ (E : Type) [CommRing E] [Algebra R E] (x : Pt A E) (i : P.ι), ⊤ ≤ x.left ⁻¹ᵁ chartsA P i → IsUnit (T E x i)) ∧
  (∀ (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E'] (ψ : E →ₐ[R] E') (x : Pt A E)
    (i : P.ι), ⊤ ≤ x.left ⁻¹ᵁ chartsA P i → T E' (spOver ψ ≫ x) i = epsHom ψ (T E x i)) ∧
  ∀ (E : Type) [CommRing E] [Algebra R E] (x : Pt A E) (i j : P.ι), ⊤ ≤ x.left ⁻¹ᵁ chartsA P i →
    ⊤ ≤ x.left ⁻¹ᵁ chartsA P j → T E x i = evU (ptV v x).left (P.U i ⊓ P.U j) (P.g i j).val * T E x j

end Gen

end GlobalTheory.PtExt
end
end

section

noncomputable section

namespace GlobalTheory.DefPt

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl MvPolynomial
open scoped Matrix

section Adelic

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] [DecidableEq ι]

def IntAt (w : HeightOneSpectrum (𝓞 K)) {κ : Type} (M : Matrix ι κ K) : Prop := ∀ i j, w.valuation K (M i j) ≤ 1

def IsAdelic (A : HeightOneSpectrum (𝓞 K) → Matrix ι ι K) : Prop :=
  (∀ w, (A w).det ≠ 0) ∧ {w | ¬ (IntAt w (A w) ∧ IntAt w (A w)⁻¹)}.Finite

def locLat (A : HeightOneSpectrum (𝓞 K) → Matrix ι ι K) : Submodule (𝓞 K) (ι → K) where
  carrier := {x | ∀ (w : HeightOneSpectrum (𝓞 K)) (i : ι), w.valuation K ((A w *ᵥ x) i) ≤ 1}
  zero_mem' := fun w i => by simp
  add_mem' := fun {x y} hx hy w i => by
    rw [Matrix.mulVec_add, Pi.add_apply]
    exact (Valuation.map_add _ _ _).trans (max_le (hx w i) (hy w i))
  smul_mem' := fun a x hx w i => by
    have h : a • x = (a : K) • x := by
      funext j
      simp [Algebra.smul_def]
    rw [h, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, map_mul]
    exact mul_le_one' (w.valuation_le_one a) (hx w i)

def matNorm (Y : (K →+* ℂ) → Matrix ι ι ℂ) (σ : K →+* ℂ) (x : ι → K) : ℝ :=
  Real.sqrt (∑ i, ‖(Y σ *ᵥ fun j => σ (x j)) i‖ ^ 2)

def detDeg (A : HeightOneSpectrum (𝓞 K) → Matrix ι ι K) (Y : (K →+* ℂ) → Matrix ι ι ℂ) : ℝ :=
  GlobalTheory.FlatLine.lineDeg (fun σ => ‖(Y σ).det‖) (fun w => (vAdd w (A w).det : ℝ))

end Adelic

section Tensor

variable {T : Type} [Fintype T] [DecidableEq T] {N : T → ℕ} {n : ℕ}

abbrev TIdx (la : ∀ t, Fin (N t) → ℕ) : Type := ∀ t, Idx (la t)

def tval (la : ∀ t, Fin (N t) → ℕ) {S : Type} [CommRing S] (x : TIdx la → S) (y : ∀ t, Matrix (Fin (N t)) (Fin (N t)) S) : S :=
  ∑ I : TIdx la, x I * ∏ t, evalAt (y t) (map (Int.castRingHom S) (intVec (la t) (I t)))

def rhoMat (la : Fin n → ℕ) {K : Type} [Field K] [CharZero K] (g : Matrix (Fin n) (Fin n) K) : Matrix (Idx la) (Idx la) K :=
  LinearMap.toMatrix (basis la K) (basis la K) (rho la K gᵀ)

def kron {J : T → Type} {R : Type} [CommRing R] (M : ∀ t, Matrix (J t) (J t) R) : Matrix (∀ t, J t) (∀ t, J t) R :=
  Matrix.of fun I I' => ∏ t, M t (I t) (I' t)

def onMat (la : Fin n → ℕ) : Matrix (Idx la) (Idx la) ℂ :=
  Matrix.of fun i j => (onBasis la).repr (toSpace la (basis la ℂ j)) i

def fibA (la : ∀ t, Fin (N t) → ℕ) {K : Type} [Field K] [CharZero K] (a : K) (B : ∀ t, Matrix (Fin (N t)) (Fin (N t)) K) :
    Matrix (TIdx la) (TIdx la) K := a • kron fun t => rhoMat (la t) (B t)

def fibY (la : ∀ t, Fin (N t) → ℕ) (s : ℝ) (X : ∀ t, Matrix (Fin (N t)) (Fin (N t)) ℂ) : Matrix (TIdx la) (TIdx la) ℂ :=
  (s : ℂ) • kron fun t => onMat (la t) * rhoMat (la t) (X t)

end Tensor

end GlobalTheory.DefPt

end
end
