module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle016
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.ArchFrame
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.IsCoordA
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

@[expose] public section

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical

namespace UpperTheory.Gal.W2

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) {gb : GBase D.toG ℂ}

abbrev TIs {S : Scheme.{0}} {s : S ⟶ Sp ℂ} {N : ℕ} (o : GObj gb N s) {k : Type} [Field k] (t : Sp k ⟶ S) : Type :=
  GTateIso D.toG k (Over.mk t ⟶ o.A) (fun c g => g ≫ o.act.act c)
    (fun n g g' z => Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) n g g' (unitOn z))

def IsTr (h : G.GAf) {S : Scheme.{0}} {s : S ⟶ Sp ℂ} {N N' : ℕ} (o' : GObj gb N' s) (o'' : GObj gb N s) (ψ : o'.A ⟶ o''.A) : Prop :=
  IsMonHom ψ ∧ (∀ c : D.O, o'.act.act c ≫ ψ = ψ ≫ o''.act.act c) ∧
    (∃ (ψ' : o''.A ⟶ o'.A) (d : ℕ), IsMonHom ψ' ∧ (∀ c : D.O, o''.act.act c ≫ ψ' = ψ' ≫ o'.act.act c) ∧
      ψ ≫ ψ' = (𝟙 o'.A) ^ d ∧ ψ' ≫ ψ = (𝟙 o''.A) ^ d ∧ d.Coprime p) ∧
    ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ S) (β : ℂ →+* k), t ≫ s = spMap β →
      ∃ (I' : TIs o' t) (I'' : TIs o'' t), (∀ y, toUnit _ ≫ o'.eta y = I'.ev N' y) ∧ (∀ y, toUnit _ ≫ o''.eta y = I''.ev N y) ∧
        ∀ n : ℕ, 0 < n → n.Coprime p → ∀ x y : D.La,
          I'.ev n x ≫ ψ = I''.ev n y ↔ ∃ v ∈ LaHat D, L.actG h (inAf D x) = inAf D y + n • v

structure Leg (h : G.GAf) {N N' : ℕ} (X' : GenModel gb N') (X : GenModel gb N) where
  q : X'.X ⟶ X.X
  o : GObj gb N X'.s
  ψ : X'.univ.A ⟶ o.A
  φ : GObjMap o X.univ q
  ov : q ≫ X.s = X'.s
  tr : IsTr L h X'.univ o ψ

variable {L} {h : G.GAf} {N N' : ℕ} {X' : GenModel gb N'} {X : GenModel gb N}

def Leg.tot (c : Leg L h X' X) : X'.univ.A.left ⟶ X.univ.A.left := c.ψ.left ≫ c.φ.φ

theorem Leg.tot_w (c : Leg L h X' X) : c.tot ≫ X.univ.A.hom = X'.univ.A.hom ≫ c.q := by
  change (c.ψ.left ≫ c.φ.φ) ≫ X.univ.A.hom = X'.univ.A.hom ≫ c.q
  rw [Category.assoc, c.φ.cart.1.w, ← Category.assoc, Over.w]

def Leg.pw (c : Leg L h X' X) (k : ℕ) : (GlobalTheory.KS.pow X'.univ.A k).left ⟶ (GlobalTheory.KS.pow X.univ.A k).left :=
  GlobalTheory.KS.powMap c.q c.tot c.tot_w k

def Leg.tw (c : Leg L h X' X) {k : ℕ} (α : Fin k → 𝓞 D.F) : (GlobalTheory.KS.pow X'.univ.A k).left ⟶ (GlobalTheory.KS.pow X.univ.A k).left :=
  c.pw k ≫ (GlobalTheory.KS.matEnd X.univ.act (Matrix.diagonal fun s => algebraMap (𝓞 D.F) D.O (α s))).left

abbrev sZ {N : ℕ} (X : GenModel gb N) (k : ℕ) : (GlobalTheory.KS.pow X.univ.A k).left ⟶ Sp ℂ := (GlobalTheory.KS.pow X.univ.A k).hom ≫ X.s

def gfamD {N : ℕ} (X : GenModel gb N) (hX : SmoothOfRelativeDimension D.g X.univ.A.hom)
    (hL : (X.univ.P.pull (lift (𝟙 X.univ.A) (𝟙 X.univ.A)).left).IsLB) : Fam ℂ D.O D.La D.g := gfam X.univ hX hL

def LevOk (L : Link D G) (N N' : ℕ) (h : G.GAf) : Prop :=
  3 ≤ N ∧ N.Coprime p ∧ 3 ≤ N' ∧ N'.Coprime p ∧ N ∣ N' ∧ ∀ u ∈ L.KN N', h * u * h⁻¹ ∈ L.KN N

end UpperTheory.Gal.W2
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical

namespace UpperTheory.Gal.W2

def FMat : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G), D.m = 1 → ∃ kp σ, IsFMat L kp σ

def FForm : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) kp σ, IsFMat L kp σ → ∃ A : Matrix (Fin G.n) (Fin G.n) G.F, A.det ≠ 0 ∧ (A.map (IsCMField.complexConj G.F))ᵀ = -A ∧
    (∀ u w, D.EF.baseChange ℚ u w = Algebra.trace ℚ G.F ((fun i => IsCMField.complexConj G.F (kp w i)) ⬝ᵥ (A *ᵥ kp u))) ∧
    ∀ c, A * σ (sh G c) = ((σ c).map (IsCMField.complexConj G.F))ᵀ * A

def SN : Prop :=
  ∀ (F K : Type) [Field F] [Field K] (n : ℕ) (τ : F →+* K) (ψ : Matrix (Fin n) (Fin n) F →+* Matrix (Fin n) (Fin n) K),
    (∀ x : F, ψ (Matrix.scalar (Fin n) x) = Matrix.scalar (Fin n) (τ x)) →
    ∃ S : Matrix (Fin n) (Fin n) K, S.det ≠ 0 ∧ ∀ M, ψ M * S = S * M.map τ

def ArchSpan : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsCMField F] (n : ℕ),
    Submodule.span ℝ (Set.range fun (x : Fin n → F) (v : InfinitePlace F) (i : Fin n) => v.embedding (x i)) = ⊤ ∧
    Module.finrank ℝ (InfinitePlace F → Fin n → ℂ) = n * Module.finrank ℚ F ∧
    ∀ x : F, ((Algebra.trace ℚ F x : ℚ) : ℝ) = ∑ v : InfinitePlace F, 2 * (v.embedding x).re

def ArchEx : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G), D.m = 1 → Nonempty (ArchFrame L)

def SigB : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (B : GlobalTheory.LKCx.Form G) (v : InfinitePlace G.F), (GlobalTheory.LKCx.herm G v B.β).IsHermitian ∧
    (sigPosH (G.gram_herm v) = 1 → (∃ z, 0 < (hv (GlobalTheory.LKCx.herm G v B.β) z z).re) ∧ ∀ z x, 0 < (hv (GlobalTheory.LKCx.herm G v B.β) z z).re →
      x ≠ 0 → hv (GlobalTheory.LKCx.herm G v B.β) x z = 0 → (hv (GlobalTheory.LKCx.herm G v B.β) x x).re < 0) ∧
    (sigPosH (G.gram_herm v) ≠ 1 → ∀ x, x ≠ 0 → (hv (GlobalTheory.LKCx.herm G v B.β) x x).re < 0)

def PerExt : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (A : ArchFrame L) (β : G.Cˣ) (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) (Q : VQ D →+ (Fin D.g → ℂ)), IsPerQ L β ρ Q →
    ∃ R : Arch G ≃ₗ[ℝ] (Fin D.g → ℂ), ∀ w, Q w = R (A.th w)

def JStruct : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (A : ArchFrame L) (β : G.Cˣ) (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) (Q : VQ D →+ (Fin D.g → ℂ)), IsPerQ L β ρ Q →
    (∀ v, (GlobalTheory.LKCx.herm G v β).IsHermitian) → ∀ R : Arch G ≃ₗ[ℝ] (Fin D.g → ℂ), (∀ w, Q w = R (A.th w)) →
    ∃ J : InfinitePlace G.F → Matrix (Fin G.n) (Fin G.n) ℂ, (∀ x : Arch G, R (fun v => J v *ᵥ x v) = Complex.I • R x) ∧
      ∀ v, IsPosJ (GlobalTheory.LKCx.herm G v β) (J v) (sgnV L v)

def JLine : Prop :=
  ∀ (n : ℕ) (M J : Matrix (Fin n) (Fin n) ℂ) (s : ℂ), M.IsHermitian → (s = 1 ∨ s = -1) → IsPosJ M J s →
    (∀ z, z ≠ 0 → J *ᵥ z = (s * Complex.I) • z → 0 < (hv M z z).re) ∧
    ((∀ x, x ≠ 0 → (hv M x x).re < 0) → J = -(s * Complex.I) • (1 : Matrix (Fin n) (Fin n) ℂ)) ∧
    ((∃ z, 0 < (hv M z z).re) → ∃ z, z ≠ 0 ∧ J *ᵥ z = (s * Complex.I) • z) ∧
    ∀ z, 0 < (hv M z z).re → (∀ x, x ≠ 0 → hv M x z = 0 → (hv M x x).re < 0) → J *ᵥ z = (s * Complex.I) • z →
      ∀ x, J *ᵥ x = (s * Complex.I) • ((2 * (hv M x z / hv M z z)) • z - x)

def HermOfJ : Prop :=
  ∀ (g : ℕ) (E : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) →ₗ[ℝ] ℝ), (∀ x, E x x = 0) → (∀ x y, E (Complex.I • x) (Complex.I • y) = E x y) →
    (∀ x, x ≠ 0 → 0 < E (Complex.I • x) x) → ∃ Hm : Matrix (Fin g) (Fin g) ℂ, Hm.IsHermitian ∧
      (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧ ∀ x y, (hermForm Hm x y).im = E x y

def LineBasis : Prop :=
  ∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℂ) (z : Fin n → ℂ), M.IsHermitian → 0 < (hv M z z).re →
    ∃ (i₀ : Fin n) (S : Matrix (Fin n) (Fin n) ℂ), S.det ≠ 0 ∧ S *ᵥ Pi.single i₀ 1 = z ∧ ∀ i, i ≠ i₀ → hv M (S *ᵥ Pi.single i 1) z = 0

def PlaceT : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G), D.a = 1 → ∀ (v : InfinitePlace G.F), sigPosH (G.gram_herm v) = 1 → ∀ t₀ : D.F →+* ℂ, (∀ i, D.tau i = t₀) →
    (∀ v', sigPosH (G.gram_herm v') = 1 → v' = v) ∧ t₀ (D.ω : D.F) = D.ρc ∧ (starRingEnd ℂ) D.ρc ≠ D.ρc ∧
    ((sgnV L v = 1 ∧ ∀ x, v.embedding (L.e x) = t₀ x) ∨
      (sgnV L v = -1 ∧ (¬ ∀ x, v.embedding (L.e x) = t₀ x) ∧ ∀ x, (starRingEnd ℂ) (v.embedding (L.e x)) = t₀ x))

def TypeIso : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G), D.a = 1 → ∀ (v : InfinitePlace G.F), sigPosH (G.gram_herm v) = 1 → ∀ t₀ : D.F →+* ℂ, (∀ i, D.tau i = t₀) →
    ∀ ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ, IsSigD D ρ t₀ → ∀ i₀ : Fin G.n, ∃ R : Arch G ≃ₗ[ℝ] (Fin D.g → ℂ),
      (∀ x : Arch G, R (fun v' i => (if v' = v ∧ i = i₀ then 1 else -1) * (sgnV L v' * Complex.I) * x v' i) = Complex.I • R x) ∧
      ∀ (c : 𝓞 D.F) (x : Arch G), R (fun v' => v'.embedding (L.e (c : D.F)) • x v') = ρ (algebraMap (𝓞 D.F) D.O c) *ᵥ R x

def RPer : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G), D.a = 1 → ∀ (v : InfinitePlace G.F), sigPosH (G.gram_herm v) = 1 → ∀ t₀ : D.F →+* ℂ, (∀ i, D.tau i = t₀) →
    ∀ ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ, IsSigD D ρ t₀ → ∀ (A : ArchFrame L) (B : GlobalTheory.LKCx.Form G) (z : GlobalTheory.LKCx.PosV G v B.β),
    ∃ (Q : VQ D →+ (Fin D.g → ℂ)) (R : Arch G →ₗ[ℝ] (Fin D.g → ℂ)), IsPerQ L B.β ρ Q ∧ (∀ w, Q w = R (A.th w)) ∧
      R (Pi.single v (Complex.I • z.1)) = (sgnV L v * Complex.I) • R (Pi.single v z.1)

end UpperTheory.Gal.W2
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical

namespace UpperTheory.Gal.W2

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G)

abbrev Loc (G : HTGroup p) : Type := (w : Fin G.m) → Fin G.n → G.Fw w

def IntL (z : Loc G) : Prop := ∀ w i, ‖(z w i : PadicAlgCl p)‖ ≤ 1

def pairL (a b : Loc G) : ℚ_[p] := ∑ w, Algebra.trace ℚ_[p] (G.Fw w) (a w ⬝ᵥ b w)

structure PFrame (β : G.Cˣ) where
  T : VQ D →+ Loc G
  T' : VQ D →+ Loc G
  act : ∀ (c : G.C) x w, T (L.rep c x) w = G.rho w c *ᵥ T x w
  act' : ∀ (c : G.C) x w, T' (L.rep c x) w = (G.rho w ((β : G.C) * sh G c * ((β⁻¹ : G.Cˣ) : G.C)))ᵀ *ᵥ T' x w
  form : ∀ u x, ((formB L β u x : ℚ) : ℚ_[p]) = pairL (T' x) (T u) - pairL (T' u) (T x)
  dense : ∀ (a b : Loc G) (k : ℕ), ∃ x a' b', IntL a' ∧ IntL b' ∧ T x = a + p ^ k • a' ∧ T' x = b + p ^ k • b'
  bound : ∃ (s : Finset (VQ D)) (k : ℕ), Submodule.span ℚ (s : Set (VQ D)) = ⊤ ∧
    ∀ x, IntL (T x) → IntL (T' x) → ∃ m : ℕ, m.Coprime p ∧ (m * p ^ k) • x ∈ AddSubgroup.closure (s : Set (VQ D))

variable {L}

def PFrame.Mem {β : G.Cˣ} (A : PFrame L β) (g : Gp G) (x : VQ D) : Prop :=
  IntL (fun w => (((g.2 w)⁻¹ : GL (Fin G.n) (G.Fw w)) : Matrix (Fin G.n) (Fin G.n) (G.Fw w)) *ᵥ A.T x w) ∧
    ∀ z : Loc G, IntL z → ‖((g.1⁻¹ : ℚ_[p]ˣ) : ℚ_[p]) * pairL (A.T' x) (fun w => (g.2 w : Matrix (Fin G.n) (Fin G.n) (G.Fw w)) *ᵥ z w)‖ ≤ 1

def IntPt (g : Gp G) : Prop :=
  ‖(g.1 : ℚ_[p])‖ = 1 ∧ ∀ w i j, ‖((g.2 w : Matrix (Fin G.n) (Fin G.n) (G.Fw w)) i j : PadicAlgCl p)‖ ≤ 1 ∧
    ‖((((g.2 w)⁻¹ : GL (Fin G.n) (G.Fw w)) : Matrix (Fin G.n) (Fin G.n) (G.Fw w)) i j : PadicAlgCl p)‖ ≤ 1

end UpperTheory.Gal.W2
end
end
