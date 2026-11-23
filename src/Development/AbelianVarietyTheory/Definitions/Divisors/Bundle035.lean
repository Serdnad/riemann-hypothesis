module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle033
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle034
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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

@[expose] public section

section

noncomputable section

namespace GlobalTheory.DefPt.Model

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl MvPolynomial GlobalTheory.DefPt
open scoped Matrix

section Adelic

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] [DecidableEq ι]


end Adelic

section Tensor

variable {T : Type} [Fintype T] [DecidableEq T] {N : T → ℕ} {n : ℕ}

theorem rhoMat_one (la : Fin n → ℕ) (K : Type) [Field K] [CharZero K] : rhoMat la (1 : Matrix _ _ K) = 1 := by
  simp [rhoMat, ← Module.End.one_eq_id, LinearMap.toMatrix_one]

theorem rhoMat_mul (la : Fin n → ℕ) {K : Type} [Field K] [CharZero K] (g h : Matrix (Fin n) (Fin n) K) :
    rhoMat la (g * h) = rhoMat la h * rhoMat la g := by
  simp [rhoMat, Matrix.transpose_mul, LinearMap.toMatrix_mul]

theorem rhoMat_scalar (la : Fin n → ℕ) {K : Type} [Field K] [CharZero K] (t : K) :
    rhoMat la (t • (1 : Matrix _ _ K)) = t ^ size la • 1 := by
  have : rho la K (t • 1) = t ^ size la • LinearMap.id := LinearMap.ext fun f => rho_scalar t f
  simp [rhoMat, this]

end Tensor

end GlobalTheory.DefPt.Model

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KeyCl GlobalTheory.Ex Matrix
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow.Cl

section Classical

variable {g : ℕ}

def cv (M : Fin g → ℤ) : Fin g → ℂ := fun i => (M i : ℂ)

def perV (τ : Matrix (Fin g) (Fin g) ℂ) (M N : Fin g → ℤ) : Fin g → ℂ := cv M + τ *ᵥ cv N

def Half (a : Fin g → ℂ) : Prop := ∀ i, a i = 0 ∨ a i = 1 / 2

def autV (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (M N : Fin g → ℤ) (z : Fin g → ℂ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (a ⬝ᵥ cv M - b ⬝ᵥ cv N) - Real.pi * Complex.I * (cv N ⬝ᵥ τ *ᵥ cv N) -
    2 * Real.pi * Complex.I * (cv N ⬝ᵥ z))

def trFac (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (m : ℕ) (M N : Fin g → ℤ) (z : Fin g → ℂ) : ℂ :=
  Complex.exp (Real.pi * Complex.I * (cv N ⬝ᵥ cv M) + Real.pi * Complex.I * (cv N ⬝ᵥ cv M) / (m : ℂ) ^ 2 +
    2 * Real.pi * Complex.I * (a ⬝ᵥ cv M - b ⬝ᵥ cv N) + 2 * Real.pi * Complex.I * (cv N ⬝ᵥ z) +
    Real.pi * Complex.I * (cv N ⬝ᵥ τ *ᵥ cv N) / (m : ℂ) ^ 2)

def trF (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (m : ℕ) (M N : Fin g → ℤ) (z : Fin g → ℂ) : ℂ :=
  trFac τ a b m M N z * thetaChar τ a b ((m : ℂ) • z + (m : ℂ)⁻¹ • perV τ M N)

def NF (x : KeyIn ℂ) (hg : x.P.g = g) (u : HolUnif x.P.A x.P.L g) (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (c : ℂ)
    (W : Fin g → Fin g → ℂ) : Prop :=
  τ.IsSymm ∧ (τ.map Complex.im).PosDef ∧ Half a ∧ Half b ∧ c ≠ 0 ∧ (∀ z, z ∈ u.Λ ↔ ∃ M N, z = perV τ M N) ∧
    u.IsRig x.rig ∧ u.IsFn x.th (fun z => c * thetaChar τ a b z) ∧ ∀ j, u.IsDiff (W j) (x.v (j.cast hg.symm))

def FnT {P : PolAV (Sp ℂ)} (u : HolUnif P.A P.L g) (k : ℕ) (t : LB.Sec (LPow P.A P.L (k : ℤ) (baseOver (Sp ℂ))))
    (f : (Fin g → ℂ) → ℂ) : Prop :=
  ∀ (i : P.L.ι) z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U i →
    valR (ptSecT P.A (T := baseOver (Sp ℂ)) (u.ex z)).left ((LPow P.A P.L (k : ℤ) (baseOver (Sp ℂ))).U fun _ => i)
      (t.f fun _ => i) = f z * u.fr i z ^ k

end Classical

structure AB (B : NumB ℂ) (g : ℕ) where

  τ : Matrix (Fin g) (Fin g) ℂ

  a : Fin g → ℂ

  b : Fin g → ℂ

  c : ℂ
  symm : τ.IsSymm
  pos : (τ.map Complex.im).PosDef
  ha : Half a
  hb : Half b
  hc : c ≠ 0

  ex : (Fin g → ℂ) → B.A
  ex_add : ∀ z w, ex (z + w) = ex z * ex w
  onto : Function.Surjective ex
  ker : ∀ z, ex z = 1 ↔ ∃ M N, z = perV τ M N

  fr : (Fin g → ℂ) → ℂˣ
  fr_zero : fr 0 = 1
  fr_per : ∀ M N z, (fr z : ℂ) = autV τ a b M N z * fr (z + perV τ M N)
  th : ∀ z, B.th (ex z) = c * thetaChar τ a b z * fr z

def AB.Cub {B : NumB ℂ} {g : ℕ} (d : AB B g) : Prop := ∀ x y z,
  B.θ (d.ex x) (d.ex y) (d.ex z) * d.fr (x + y) * d.fr (x + z) * d.fr (y + z) = d.fr (x + y + z) * d.fr x * d.fr y * d.fr z

def AB.Sym {B : NumB ℂ} {g : ℕ} (d : AB B g) : Prop := ∀ x, B.σ (d.ex x) * d.fr x = d.fr (-x)

def co {X : Type} [AddCommGroup X] {r : ℕ} (bX : Module.Basis (Fin r) ℤ X) (χ : X) : Fin r → ℂ := fun l => (bX.repr χ l : ℂ)

structure CD (N : NumD ℂ) (g r : ℕ) (bX : Module.Basis (Fin r) ℤ N.X) extends AB N.toNumB g where
  cub : toAB.Cub
  sym : toAB.Sym

  t12 : Matrix (Fin g) (Fin r) ℂ

  t22 : Matrix (Fin r) (Fin r) ℂ

  b2 : Fin r → ℂ
  toricPeriodBlock_isSymm : t22.IsSymm
  hb2 : Half b2
  c_eq : ∀ χ, N.c χ = ex (t12 *ᵥ co bX χ)
  ψ_eq : ∀ χ, (N.ψ χ : ℂ) * fr (t12 *ᵥ co bX χ) =
    Complex.exp (Real.pi * Complex.I * (co bX χ ⬝ᵥ t22 *ᵥ co bX χ) + 2 * Real.pi * Complex.I * (co bX χ ⬝ᵥ b2))

namespace CD

variable {N : NumD ℂ} {g' r g : ℕ} {bX : Module.Basis (Fin r) ℤ N.X} (d : CD N g' r bX) (σ : Fin g ≃ Fin g' ⊕ Fin r)

def full (S : Matrix (Fin r) (Fin r) ℂ) : Matrix (Fin g) (Fin g) ℂ :=
  (Matrix.fromBlocks d.τ d.t12 d.t12ᵀ (d.t22 + S)).submatrix σ σ

def aF : Fin g → ℂ := fun j => Sum.elim d.a 0 (σ j)

def bF : Fin g → ℂ := fun j => Sum.elim d.b d.b2 (σ j)

end CD

def zP {g' r g : ℕ} {A : Type} (σ : Fin g ≃ Fin g' ⊕ Fin r) (Z : Fin g → A) : Fin g' → A := fun i => Z (σ.symm (Sum.inl i))

def tP {g' r g : ℕ} {A : Type} (σ : Fin g ≃ Fin g' ⊕ Fin r) (Z : Fin g → A) : Fin r → A := fun l => Z (σ.symm (Sum.inr l))

namespace CD

variable {N : NumD ℂ} {g' r g : ℕ} {bX : Module.Basis (Fin r) ℤ N.X} (d : CD N g' r bX) (σ : Fin g ≃ Fin g' ⊕ Fin r)

def IsPt (Z : Fin g → ℂ) (h : N.Gt) : Prop :=
  h.b = d.ex (zP σ Z) ∧ ∀ χ, (h.s χ : ℂ) * d.fr (d.t12 *ᵥ co bX χ + zP σ Z) =
    Complex.exp (2 * Real.pi * Complex.I * (co bX χ ⬝ᵥ tP σ Z)) * d.fr (d.t12 *ᵥ co bX χ) * d.fr (zP σ Z)

def Rep (k : ℕ) (M Nn : Fin g → ℤ) (p : N.QT k) : Prop :=
  p.1.1.toAdd = ∑ l, tP σ Nn l • bX l ∧ d.IsPt σ ((k : ℂ)⁻¹ • perV (d.full σ 0) M Nn) p.1.2

def fj (S : Matrix (Fin r) (Fin r) ℂ) (χ : N.X) (Z : Fin g → ℂ) : ℂ :=
  Complex.exp (Real.pi * Complex.I * (co bX χ ⬝ᵥ (d.t22 + S) *ᵥ co bX χ) +
    2 * Real.pi * Complex.I * (co bX χ ⬝ᵥ (tP σ Z + d.b2))) * thetaChar d.τ d.a d.b (zP σ Z + d.t12 *ᵥ co bX χ)

def term (S : Matrix (Fin r) (Fin r) ℂ) (m : ℕ) (M Nn : Fin g → ℤ) (χ : N.X) (Z : Fin g → ℂ) : ℂ :=
  trFac (d.full σ S) (d.aF σ) (d.bF σ) m M Nn Z * d.fj σ S χ ((m : ℂ) • Z + (m : ℂ)⁻¹ • perV (d.full σ S) M Nn)

end CD

def bmat {N : NumD ℂ} {r k : ℕ} (bX : Module.Basis (Fin r) ℤ N.X) (β : N.Form k) : Matrix (Fin r) (Fin r) ℂ :=
  Matrix.of fun l l' => (β.be (bX l) (bX l') : ℂ)

section Geo

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} [Algebra (FractionRing R) ℂ] {N : NumD ℂ} {g : ℕ}

def ptB (ν : NumOf D ℂ N) (d : AB N.toNumB g) (z : Fin g → ℂ) : Sp ℂ ⟶ (DegPre.BF D ℂ).left :=
  (lift (𝟙 (TF (R := R) ℂ)) (ν.eA (d.ex z))).left

def IsD (ν : NumOf D ℂ N) (d : AB N.toNumB g) (W : Fin g → ℂ) (b : TE R ℂ ⟶ D.P.A) : Prop :=
  ∀ (U : (DegPre.BF D ℂ).left.Opens) (f : Γ((DegPre.BF D ℂ).left, U)), ⊤ ≤ ptB ν d 0 ⁻¹ᵁ U →
    valR (lift (Over.homMk (spMap (algebraMap ℂ (DualNumber ℂ))) rfl : TE R ℂ ⟶ TF (R := R) ℂ) b).left U f =
      TrivSqZeroExt.inl (valF (ptB ν d 0) U f) + TrivSqZeroExt.inr (fderiv ℂ (fun z => valF (ptB ν d z) U f) 0 W)

structure Geo (ν : NumOf D ℂ N) (d : AB N.toNumB g) where

  frG : D.P.L.ι → (Fin g → ℂ) → ℂ
  hol : ∀ (U : (DegPre.BF D ℂ).left.Opens) (f : Γ((DegPre.BF D ℂ).left, U)), IsOpen {z | ⊤ ≤ ptB ν d z ⁻¹ᵁ U} ∧
    DifferentiableOn ℂ (fun z => valF (ptB ν d z) U f) {z | ⊤ ≤ ptB ν d z ⁻¹ᵁ U}
  fr_hol : ∀ i, DifferentiableOn ℂ (frG i) {z | ⊤ ≤ (ν.eA (d.ex z)).left ⁻¹ᵁ D.P.L.U i}
  fr_compat : ∀ i j z, ⊤ ≤ (ν.eA (d.ex z)).left ⁻¹ᵁ (D.P.L.U i ⊓ D.P.L.U j) →
    frG i z = valF (ν.eA (d.ex z)).left (D.P.L.U i ⊓ D.P.L.U j) (D.P.L.g i j).val * frG j z
  fr_eq : ∀ z, (d.fr z : ℂ) * ν.rg = frG (ν.J (ν.eA (d.ex z)).left) z
  dif : ∀ b : TE R ℂ ⟶ D.P.A, redE ℂ ≫ b.left = (DegPre.zeroF D ℂ).left → ∃ W, IsD ν d W b

def KeyOK (κ : Rule) (ν : NumOf D ℂ N) (d : AB N.toNumB D.P.g) : Prop :=
  ∀ (vB : Fin D.P.g → (epsR R ⟶ D.P.A)) (b : Fin D.P.g → (TE R ℂ ⟶ D.P.A)) (MB : Matrix (Fin D.P.g) (Fin D.P.g) ℂ) (k₀ : ℂ),
    IsLieBasis vB → (∀ i, (b i).left =
      spMap (dualMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R)))) ≫ (vB i).left) →
    (∀ i, IsD ν d ((2 * Real.pi * Complex.I : ℂ)⁻¹ • MB i) (b i)) → BKey κ ν vB k₀ → MB.det ≠ 0 ∧ k₀ * d.c ^ 8 = MB.det ^ 4

end Geo

def AllC (P : ∀ {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} [Algebra (FractionRing R) ℂ] {N : NumD ℂ},
    NumOf D ℂ N → Prop) : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R] (D : DegPre R), D.PsiEven → D.TauBimult →
    ∀ [Algebra (FractionRing R) ℂ] (N : NumD ℂ) (ν : NumOf D ℂ N), P ν

def AllCD (P : ∀ {N : NumD ℂ} {g' r g : ℕ} {bX : Module.Basis (Fin r) ℤ N.X}, CD N g' r bX → (Fin g ≃ Fin g' ⊕ Fin r) → Prop) :
    Prop :=
  ∀ (N : NumD ℂ) (g' r g : ℕ) (bX : Module.Basis (Fin r) ℤ N.X) (d : CD N g' r bX) (σ : Fin g ≃ Fin g' ⊕ Fin r), P d σ

end GlobalTheory.MBLow.Cl

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KeyCl GlobalTheory.Ex
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I} {A : PolAV (Sp (FractionRing R))}
  {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]

def TanRel (U : UnifPre I D A G) (y : epsR R ⟶ G) (gm : GtPt D.toPre (epsR R)) : Prop :=
  ∀ e : ℕ, ∃ ye : Sp (DualNumber (R ⧸ I ^ (e + 1))) ⟶ (thickObj R I e G).left,
    ye ≫ (fstG I e G).left = spMap (dualMap (Ideal.Quotient.mk (I ^ (e + 1)))) ≫ y.left ∧
    ye ≫ (U.gt e).pG.left = spMap (dualMap (Ideal.Quotient.mk (I ^ (e + 1)))) ≫ gm.b.left ∧
    ∀ χ, LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ ((U.gt e).t χ) ye)
      (LB.pullGen D.toPre.P.L _ _ (gm.s χ) (spMap (dualMap (Ideal.Quotient.mk (I ^ (e + 1))))))

def GtTan {D₀ : DegPre R} (gm : GtPt D₀ (epsR R)) : Prop :=
  ∃ o : GtPt D₀ (baseOver (Sp R)), o.IsZero ∧ GtPt.IsPull (redE R) gm o

abbrev toF (R : Type) [CommRing R] [IsDomain R] (F : Type) [Field F] [Algebra (FractionRing R) F] : R →+* F :=
  (algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R))

def VecAt (U : UnifPre I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F] (y : epsR R ⟶ G)
    (yA : Sp (DualNumber F) ⟶ (TFK (R := R) F ⊗ A.A).left) : Prop :=
  yA ≫ (fst (TFK (R := R) F) A.A).left = spMap (algebraMap F (DualNumber F)) ∧
  yA ≫ (snd (TFK (R := R) F) A.A).left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R) = spMap (dualMap (toF R F)) ≫ y.left

def ArchF (κ : Rule) : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R] (D : DegPre R), D.PsiEven → D.TauBimult →
    ∀ (F : Type) [Field F] [CharZero F] [Algebra (FractionRing R) F] (e : F ≃+* ℂ) (N : NumD F) (ν : NumOf D F N) (g r m k : ℕ),
    1 ≤ g → Odd m → m ^ 2 ∣ k →
    ∀ (β : N.Form k) (ζ : Fˣ) (q : (Fin (2 * g) → ZMod (m ^ 2)) → N.QT (m ^ 2)), QLevel N g (m ^ 2) ζ q →
    ∀ (s : (Fin (2 * g) → ZMod (m ^ 2)) → Fam D F (m ^ 2)), (∀ a, ∃ f, ν.FamV (s a) f ∧ IsEvFam N m (q a) f) →
    ∀ (vB : Fin D.P.g → (epsR R ⟶ D.P.A)) (bX : Module.Basis (Fin r) ℤ N.X) (σ : Fin g ≃ Fin D.P.g ⊕ Fin r)
      (gm : Fin g → GtPt D (TE R F)), Adapted ν vB bX σ gm → ∀ k₀ : F, BKey κ ν vB k₀ →
    ∃ ε : ℝ, 0 < ε ∧ ∀ u : ℂ, u ≠ 0 → ‖u‖ < ε →
      (∀ a j, (Summable fun α => ‖e ((jc ν (s a) (gm j) α).fst / ν.rg ^ (m ^ 2)) * u ^ (β.be α α / (2 * m ^ 2)).toNat‖) ∧
        Summable fun α => ‖e ((jc ν (s a) (gm j) α).snd / ν.rg ^ (m ^ 2)) * u ^ (β.be α α / (2 * m ^ 2)).toNat‖) ∧
      ∃ (x₀ : KeyIn ℂ) (hg₀ : x₀.P.g = g) (lev₀ : Out.Level x₀.P (m ^ 2) (unitOn (Units.map (e : F →+* ℂ).toMonoidHom ζ)))
        (ϑ : _ → ℂ),
        (∀ a j, ϑ a = ∑' α, e ((jc ν (s a) (gm j) α).fst / ν.rg ^ (m ^ 2)) * u ^ (β.be α α / (2 * m ^ 2)).toNat) ∧
        ThJet x₀ hg₀ m (levelPoint lev₀ hg₀) ϑ
          (fun a j => ∑' α, e ((jc ν (s a) (gm j) α).snd / ν.rg ^ (m ^ 2)) * u ^ (β.be α α / (2 * m ^ 2)).toNat) ∧
        (κ ℂ x₀ : ℂ) = e k₀

def AllV (P : ∀ {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {D : DegData V (IsLocalRing.maximalIdeal V)}
    {A : PolAV (Sp (FractionRing V))} {G : Over (Sp V)} [GrpObj G] [IsCommMonObj G],
    Unif (IsLocalRing.maximalIdeal V) D A G → Prop) : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V],
    IsAdicComplete (IsLocalRing.maximalIdeal V) V → ∀ (D : DegData V (IsLocalRing.maximalIdeal V))
    (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G →
    ∀ U : Unif (IsLocalRing.maximalIdeal V) D A G, P U

def AllVC (P : ∀ {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {D : DegData V (IsLocalRing.maximalIdeal V)}
    {A : PolAV (Sp (FractionRing V))} {G : Over (Sp V)} [GrpObj G] [IsCommMonObj G]
    (_ : Unif (IsLocalRing.maximalIdeal V) D A G) {C : Type} [NontriviallyNormedField C] [Algebra (FractionRing V) C]
    {N : NumD C}, NumOf D.toPre C N → Prop) : Prop :=
  AllV fun {V} _ _ _ {D} {_} {_} _ _ U =>
    ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [CharZero C]
      [Algebra (FractionRing V) C], CExt V (IsLocalRing.maximalIdeal V) C →
      ∀ (N : NumD C) (ν : NumOf D.toPre C N), ν.IntN → P U ν

end GlobalTheory.MBLow

end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Points GlobalTheory.ChartGlue GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.CechPic

namespace GlobalTheory.Mix

variable {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}

structure MLine (p : X ⟶ Sp k) (σ : k →+* ℂ) where

  B : LB X

  φ : Weight p σ B

  cInf : φ.IsCInf

namespace MLine

def ofHerm (L : HermLB p) (σ : k →+* ℂ) : MLine p σ := ⟨L.B, L.φ σ, L.cInf σ⟩

def tens (A B : MLine p σ) : MLine p σ := ⟨CechPic.tens A.B B.B, A.φ.tens B.φ, A.cInf.tens B.cInf⟩

def pull (A : MLine p σ) {q : Y ⟶ Sp k} (π : Y ⟶ X) (hπ : π ≫ p = q) : MLine q σ :=
  ⟨A.B.pull π, A.φ.pull π hπ, A.cInf.pull π hπ⟩

def ofFun (u : CxPts p σ → ℝ) (hu : ∀ y, CInfAt u y) : MLine p σ :=
  ⟨LB.triv X, Weight.ofFun u, Weight.isCInf_ofFun hu⟩

def addFn (A : MLine p σ) (u : CxPts p σ → ℝ) (hu : ∀ y, CInfAt u y) : MLine p σ :=
  ⟨A.B, A.φ.addFn u, A.cInf.addFn hu⟩

def Isom (L M : MLine p σ) : Prop :=
  ∃ w : LB.Iso L.B M.B, w.IsGen ∧ ∀ (a : M.B.ι) (b : L.B.ι) (y : CxPts p σ),
    y ∈ ptsIn p σ (M.B.U a) → y ∈ ptsIn p σ (L.B.U b) →
      M.φ.φ a y = L.φ.φ b y + Real.log (‖ev p σ _ (w.s (a, b)).val y‖ ^ 2)

def logSec (M : MLine p σ) (s : M.B.Sec) (y : CxPts p σ) : ℝ := Real.log (M.φ.nsq (secVal p σ s) y) / 2

end MLine

abbrev ptMap {q : Y ⟶ Sp k} (π : Y ⟶ X) (hπ : π ≫ p = q) (σ : k →+* ℂ) : CxPts q σ → CxPts p σ :=
  PtsOver.map π hπ (spMap σ)

def dens (L : Fin D → MLine p σ) (c : AlgChart p σ D) (y : CxPts p σ) : ℝ :=
  (Real.pi ^ D)⁻¹ * (∑ τ : Equiv.Perm (Fin D), (Matrix.of fun j l =>
    c.hess (L (τ l)).φ (pick (L (τ l)).φ.isLB y) y j l).det).re

def part (L : Fin D → MLine p σ) (ε : ℤˣ) : Measure (CxPts p σ) :=
  glueMeas (fun c : AlgChart p σ D => c.e) fun c y => ENNReal.ofReal ((ε : ℤ) * dens L c y)

def Intg (L : Fin D → MLine p σ) (f : CxPts p σ → ℝ) : Prop := Integrable f (part L 1) ∧ Integrable f (part L (-1))

def int (L : Fin D → MLine p σ) (f : CxPts p σ → ℝ) : ℝ := ∫ y, f y ∂part L 1 - ∫ y, f y ∂part L (-1)

def clos (z : X) : Scheme.{0} := (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {z})).subscheme

def closι (z : X) : clos z ⟶ X := (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {z})).subschemeι

instance (z : X) : IsClosedImmersion (closι z) :=
  inferInstanceAs (IsClosedImmersion (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {z})).subschemeι)

def CycIntg (L : Fin D → MLine p σ) (f : CxPts p σ → ℝ) (z : X) : Prop :=
  Intg (fun i => (L i).pull (closι z) rfl) fun y => f (ptMap (closι z) rfl σ y)

def cycInt (L : Fin D → MLine p σ) (f : CxPts p σ → ℝ) (z : X) : ℝ :=
  int (fun i => (L i).pull (closι z) rfl) fun y => f (ptMap (closι z) rfl σ y)

def side [IsIntegral X] [IsLocallyNoetherian X] (N : MLine p σ) (L : Fin D → MLine p σ) (f g : CxPts p σ → ℝ)
    (Δ : CartierDiv X) : ℝ :=
  int (Fin.cons N L : Fin (D + 1) → MLine p σ) f + ∑ᶠ z, (Δ.mult z : ℝ) * cycInt L g z

theorem dens_const (N : MLine p σ) (c : AlgChart p σ D) (y : CxPts p σ) :
    dens (fun _ => N) c y = c.chernDens N.φ y := by
  have e : (Matrix.of fun j l => c.hess N.φ (pick N.φ.isLB y) y j l) = c.hess N.φ (pick N.φ.isLB y) y := rfl
  simp only [dens, AlgChart.chernDens, e, Finset.sum_const, Finset.card_univ, Fintype.card_perm,
    Fintype.card_fin, nsmul_eq_mul, Complex.mul_re, Complex.natCast_re, Complex.natCast_im]
  ring

theorem part_const (N : MLine p σ) (ε : ℤˣ) : part (fun _ : Fin D => N) ε = N.φ.chernPart D ε := by
  simp only [part, Weight.chernPart, dens_const]

section Generic

variable (t : X ⟶ Sp ℤ)

variable {t}

end Generic

end GlobalTheory.Mix
end
end

section

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.ArInt

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {ι : Type} [Fintype ι]

def zp (L : HermLB p) (n : ℤ) : HermLB p := (L.pow n.toNat).tens (L.pow (-n).toNat).dual

def comb (L : ι → HermLB p) (n : ι → ℤ) : HermLB p :=
  (Finset.univ : Finset ι).toList.foldr (fun i M => (zp (L i) (n i)).tens M) (HermLB.triv p)

def lin (n : ι → ℝ) : MvPolynomial ι ℝ := ∑ i, C (n i) * MvPolynomial.X i

def fnB (u : ∀ σ : k →+* ℂ, CxPts p σ → ℝ) (hu : ∀ σ y, CxPts.CInfAt (u σ) y)
    (hc : ∀ σ σ', (Weight.ofFun (u σ)).IsConj (Weight.ofFun (u σ'))) : HermLB p where
  B := LB.triv X
  isLB := LB.isLB_triv X
  φ σ := Weight.ofFun (u σ)
  cInf σ := fun _ y _ => hu σ y
  conj := hc

def chInt (L : HermLB p) (D : ℕ) (f : ∀ σ : k →+* ℂ, CxPts p σ → ℝ) : ℝ :=
  ∑ᶠ σ, (L.φ σ).chernInt D Set.univ (f σ)

def gdeg (L : HermLB p) (D : ℕ) : ℝ := chInt L D fun _ _ => 1

def IsArFun [IsIntegral X] (L : ι → HermLB p) (D : ℕ) (Φ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ) : Prop :=
  (∀ n : ι → ℤ, (comb L n).IsSelfInter (Φ (lin (fun i => (n i : ℝ)) ^ (D + 1)))) ∧
    ∀ (P : MvPolynomial ι ℝ) (d : ℕ), d ≠ D + 1 → P.IsHomogeneous d → Φ P = 0

def IsGeoFun (L : ι → HermLB p) (D : ℕ) (Ψ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ) : Prop :=
  (∀ n : ι → ℤ, Ψ (lin (fun i => (n i : ℝ)) ^ D) = gdeg (comb L n) D) ∧
    ∀ (P : MvPolynomial ι ℝ) (d : ℕ), d ≠ D → P.IsHomogeneous d → Ψ P = 0

def IsAlgPt (x : X) : Prop :=
  CharZero (X.residueField x) ∧ topologicalKrullDim (closure ({x} : Set X)) = 1

def IsPtHt (L : HermLB p) (x : X) (a : ℝ) : Prop :=
  ∃ h, L.IsArithHeight h ∧ h x = a * Nat.card (X.residueField x →+* ℂ)

def NefFib (L : HermLB p) : Prop :=
  ∀ (Z : Scheme.{0}) (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z] (κ : Type)
    [Field κ] [Finite κ] [Algebra κ Γ(Z, ⊤)], topologicalKrullDim Z = 1 → 0 ≤ topSelfIntersection κ (L.B.pull i) 1

def arVol (L : HermLB p) (D : ℕ) : EReal :=
  limsup (fun m : ℕ => ENNReal.log ((L.pow m).smallSec.encard : ENNReal) *
    ((((D + 1).factorial : ℝ) / (m : ℝ) ^ (D + 1) : ℝ) : EReal)) atTop

theorem nefFib_of_isNef {L : HermLB p} {D : ℕ} (h : L.IsNef D) : NefFib L := h.vertical

end GlobalTheory.ArInt
end
end
