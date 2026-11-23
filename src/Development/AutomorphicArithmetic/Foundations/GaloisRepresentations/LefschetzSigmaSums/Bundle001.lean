module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenModelBaseChangeUniv
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.IntegOfMem
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.InvPol
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.MapWopWmap
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MarkWeightedFixedPointEqDefinitePairOdd
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PerCApply
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle015

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo
open GlobalTheory.UPel.HT.Gen.BaseChange (down)
open GlobalTheory.GalV (Splits)
open UpperTheory.Gal.Int.Geo (KS Lv Mem IsTrans TIso)

namespace UpperTheory.Gal.LocalSmoothExtension

def MapEq : Prop :=
  ∀ (G : GDatum) (R : Type) [CommRing R] [Algebra ℚ R] (b : GBase G R) (N : ℕ) (S₁ S₂ S₃ : Scheme.{0}) (s₁ : S₁ ⟶ Sp R)
    (s₂ : S₂ ⟶ Sp R) (s₃ : S₃ ⟶ Sp R) (o₁ : GObj b N s₁) (o₂ : GObj b N s₂) (o₃ : GObj b N s₃) (f : S₁ ⟶ S₂) (g : S₂ ⟶ S₃)
    (m₂ : GObjMap o₂ o₃ g),
    (∀ m₁ : GObjMap o₁ o₂ f, ∃ n : GObjMap o₁ o₃ (f ≫ g), n.φ = m₁.φ ≫ m₂.φ) ∧
    ∀ m : GObjMap o₁ o₃ (f ≫ g), ∃ n : GObjMap o₁ o₂ f, n.φ ≫ m₂.φ = m.φ

def ModelBc : Prop :=
  ∀ (G : GDatum) (R₁ R₂ : Type) [CommRing R₁] [CommRing R₂] [Algebra ℚ R₁] [Algebra ℚ R₂] (τ : R₁ →+* R₂) (gb₁ : GBase G R₁)
    (gb₂ : GBase G R₂) (hρ : gb₂.ρ = τ gb₁.ρ) (ht : ∀ i, gb₂.t i = τ.comp (gb₁.t i)) (N : ℕ) (M : GenModel gb₁ N),
    ∃ (M' : GenModel gb₂ N) (f : M'.X ⟶ M.X), IsPullback f M'.s M.s (spMap τ) ∧
      Nonempty (GObjMap (down hρ ht rfl M'.univ) M.univ f)

def HomEx : Prop :=
  ∀ (G : GDatum) (R : Type) [CommRing R] [Algebra ℚ R] (b : GBase G R) (N N' : ℕ) (S S₁ : Scheme.{0}) (s : S ⟶ Sp R)
    (s₁ : S₁ ⟶ Sp R) (f : S₁ ⟶ S) (o' : GObj b N' s) (o'' : GObj b N s) (o₁' : GObj b N' s₁) (o₁'' : GObj b N s₁)
    (m' : GObjMap o₁' o' f) (m'' : GObjMap o₁'' o'' f),
    (∀ ψ : o'.A ⟶ o''.A, IsMonHom ψ → ∃ ψ₁ : o₁'.A ⟶ o₁''.A, IsMonHom ψ₁ ∧ ψ₁.left ≫ m''.φ = m'.φ ≫ ψ.left) ∧
    (∀ ψ₁ ψ₂ : o₁'.A ⟶ o₁''.A, ψ₁.left ≫ m''.φ = ψ₂.left ≫ m''.φ → ψ₁ = ψ₂) ∧
    ∀ d : ℕ, ((𝟙 o₁'.A) ^ d).left ≫ m'.φ = m'.φ ≫ ((𝟙 o'.A) ^ d).left

def PolPull : Prop :=
  ∀ (G : GDatum) (R : Type) [CommRing R] [Algebra ℚ R] (b : GBase G R) (N N' : ℕ) (S S₁ : Scheme.{0}) (s : S ⟶ Sp R)
    (s₁ : S₁ ⟶ Sp R) (f : S₁ ⟶ S) (o' : GObj b N' s) (o'' : GObj b N s) (o₁' : GObj b N' s₁) (o₁'' : GObj b N s₁)
    (m' : GObjMap o₁' o' f) (m'' : GObjMap o₁'' o'' f) (ψ : o'.A ⟶ o''.A) (ψ₁ : o₁'.A ⟶ o₁''.A),
    ψ₁.left ≫ m''.φ = m'.φ ≫ ψ.left → ∀ c : ℕ, Nonempty (LBIso (Hecke.lbPow o'.P c) (o''.P.pull (Hecke.sq2 ψ))) →
      Nonempty (LBIso (Hecke.lbPow o₁'.P c) (o₁''.P.pull (Hecke.sq2 ψ₁)))

def TatePull : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [Algebra ℚ R] (b : GBase D.toG R) (N : ℕ) (S S₁ : Scheme.{0})
    (s : S ⟶ Sp R) (s₁ : S₁ ⟶ Sp R) (f : S₁ ⟶ S) (o : GObj b N s) (o₁ : GObj b N s₁) (m : GObjMap o₁ o f)
    (k : Type) [Field k] (t : Sp k ⟶ S₁) (I : TIso o (t ≫ f)),
    ∃ I₁ : TIso o₁ t, ∀ n y, (I₁.ev n y).left ≫ m.φ = (I.ev n y).left

def TransPull : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (R : Type) [CommRing R] [Algebra ℚ R]
    (b : GBase D.toG R) (N N' : ℕ) (S S₁ : Scheme.{0}) (s : S ⟶ Sp R) (s₁ : S₁ ⟶ Sp R) (f : S₁ ⟶ S), f ≫ s = s₁ →
    ∀ (o' : GObj b N' s) (o'' : GObj b N s) (o₁' : GObj b N' s₁) (o₁'' : GObj b N s₁)
    (m' : GObjMap o₁' o' f) (m'' : GObjMap o₁'' o'' f) (h : G.GAf) (ψ : o'.A ⟶ o''.A), IsTrans L h o' o'' ψ →
      ∃ ψ₁ : o₁'.A ⟶ o₁''.A, ψ₁.left ≫ m''.φ = m'.φ ≫ ψ.left ∧ IsTrans L h o₁' o₁'' ψ₁

def LegBc : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (R₁ R₂ : Type) [CommRing R₁] [CommRing R₂]
    [Algebra ℚ R₁] [Algebra ℚ R₂] (τ : R₁ →+* R₂) (gb₁ : GBase D.toG R₁) (gb₂ : GBase D.toG R₂) (hρ : gb₂.ρ = τ gb₁.ρ)
    (ht : ∀ i, gb₂.t i = τ.comp (gb₁.t i)) (N N' : ℕ) (M : GenModel gb₁ N) (M' : GenModel gb₁ N') (P : GenModel gb₂ N)
    (P' : GenModel gb₂ N') (f : P.X ⟶ M.X) (f' : P'.X ⟶ M'.X), IsPullback f P.s M.s (spMap τ) →
    IsPullback f' P'.s M'.s (spMap τ) → ∀ (m : GObjMap (down hρ ht rfl P.univ) M.univ f)
    (m' : GObjMap (down hρ ht rfl P'.univ) M'.univ f') (h : G.GAf) (π : M'.X ⟶ M.X) (o : GObj gb₁ N M'.s)
    (ψ : M'.univ.A ⟶ o.A) (φ : GObjMap o M.univ π), π ≫ M.s = M'.s → IsTrans L h M'.univ o ψ →
    ∃ (π₁ : P'.X ⟶ P.X) (o₁ : GObj gb₂ N P'.s) (ψ₁ : P'.univ.A ⟶ o₁.A) (φ₁ : GObjMap o₁ P.univ π₁),
      π₁ ≫ P.s = P'.s ∧ IsTrans L h P'.univ o₁ ψ₁ ∧ π₁ ≫ f = f' ≫ π ∧
        (ψ₁.left ≫ φ₁.φ) ≫ m.φ = m'.φ ≫ ψ.left ≫ φ.φ

def PowComp : Prop :=
  ∀ (S₁ S₂ S₃ : Scheme.{0}) (A₁ : Over S₁) (A₂ : Over S₂) (A₃ : Over S₃) (f : S₁ ⟶ S₂) (g : S₂ ⟶ S₃) (e : S₁ ⟶ S₃)
    (φ : A₁.left ⟶ A₂.left) (χ : A₂.left ⟶ A₃.left) (ω : A₁.left ⟶ A₃.left) (h₁ : φ ≫ A₂.hom = A₁.hom ≫ f)
    (h₂ : χ ≫ A₃.hom = A₂.hom ≫ g) (h₃ : ω ≫ A₃.hom = A₁.hom ≫ e), f ≫ g = e → φ ≫ χ = ω → ∀ k : ℕ,
    GlobalTheory.KS.powMap f φ h₁ k ≫ GlobalTheory.KS.powMap g χ h₂ k = GlobalTheory.KS.powMap e ω h₃ k

def KNNormal : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (M : ℕ),
    (∀ k ∈ L.KN 1, ∀ u ∈ L.KN M, k * u * k⁻¹ ∈ L.KN M) ∧ (0 < M → (L.KN M).relIndex (L.KN 1) ≠ 0)

def cntFn {Γ : Type} [Group Γ] (K K' M : Subgroup Γ) (h y : Γ) : ℂ :=
  (Nat.card {k : K' ⧸ M.subgroupOf K' // h * (k.out : Γ) * y ∈ K} : ℕ)

def CntFn : Prop :=
  ∀ (Γ : Type) [Group Γ] (K K' M : Subgroup Γ) (h : Γ), K ≤ K' → (∀ k ∈ K', ∀ u ∈ M, k * u * k⁻¹ ∈ M) →
    M.relIndex K' ≠ 0 → (∀ k ∈ K', ∀ u ∈ M, h * k * u * (h * k)⁻¹ ∈ K) →
    (∀ k ∈ K, ∀ y, cntFn K K' M h (k * y) = cntFn K K' M h y ∧ cntFn K K' M h (y * k) = cntFn K K' M h y) ∧
    (∀ y, cntFn K K' M h y ≠ 0 → ∃ k ∈ K, ∃ c ∈ K', y⁻¹ = k * (h * c)) ∧
    {y : Γ ⧸ K | cntFn K K' M h y.out ≠ 0}.Finite

def CntSum : Prop :=
  ∀ (Γ : Type) [Group Γ] (K K' M : Subgroup Γ) (h : Γ), M ≤ K → K ≤ K' → (∀ k ∈ K', ∀ u ∈ M, k * u * k⁻¹ ∈ M) →
    (∀ k ∈ K', ∀ u ∈ M, h * k * u * (h * k)⁻¹ ∈ K) →
    ∀ [Fintype (K' ⧸ K.subgroupOf K')] (Δ : Type) [Fintype Δ] (r : Δ → Γ), (∀ x, r x ∈ K) →
    (∀ k ∈ K, ∃! x, k * (r x)⁻¹ ∈ M) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (P : Γ → V),
    (∀ k ∈ K, ∀ c ∈ K', P (k * (h * c)) = P (h * c)) →
      ∑ z : (K' ⧸ K.subgroupOf K') × Δ, P (h * (z.1.out : Γ) * r z.2) = ∑ᶠ y : Γ ⧸ K, cntFn K K' M h y.out • P y.out⁻¹

def SigmaFEt : Prop :=
  ∀ (Y Z : Scheme.{0}) (s : Y ⟶ Z) [IsFinite s] [Etale s] (I : Type) [Finite I],
    IsFinite (Sigma.desc fun _ : I => s) ∧ Etale (Sigma.desc fun _ : I => s)

def SigmaSplit : Prop :=
  ∀ (Y Z W : Scheme.{0}) (s : Y ⟶ Z) [IsFinite s] [Etale s] (I : Type) [Finite I] (c : W ⟶ Z) (Δ : Type) [Finite Δ]
    (σ : Δ → (W ⟶ Y)), Splits s c σ →
    Splits (Sigma.desc fun _ : I => s) c fun z : I × Δ => σ z.2 ≫ Sigma.ι (fun _ : I => Y) z.1

end UpperTheory.Gal.LocalSmoothExtension
end
end

section

set_option autoImplicit false

noncomputable section

open Matrix NumberField Polynomial GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCx GlobalTheory.LKDef GlobalTheory.RootSumWeights GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open UpperTheory.Gal.W2 (rts locW lefTerm)
open UpperTheory.Gal.CertificateRingHomMap (wop wmul wmap)
open scoped TensorProduct Classical

namespace UpperTheory.Gal.LocalSmoothExtension

def wordFn {H J : Type} [Group H] (K : Subgroup H) (ψ : J → H → ℂ) (w : List J) (f : H → ℂ) : H → ℂ :=
  w.foldr (fun j g => Formalism.UG.conv K (ψ j) g) f

def polyFn {H J : Type} [Group H] (K : Subgroup H) (ψ : J → H → ℂ) (s : List J →₀ ℂ) (f : H → ℂ) : H → ℂ :=
  s.sum fun w c => c • wordFn K ψ w f

def Spec {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : GlobalTheory.LKGeo.Link D G) (lam : (D.F →+* ℂ) → Fin G.n → ℕ)
    (K : Subgroup G.GAf) {J : Type} (ψ : J → G.GAf → ℂ) (θ : J → ℂ) (f : G.GAf → ℂ) : Prop :=
  (∀ j j' w, wordFn K ψ (j :: j' :: w) f = wordFn K ψ (j' :: j :: w) f) ∧
  ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (_ : FiniteDimensional ℂ V) (ξ : Representation ℂ (G.Cˣ × ℚˣ) V),
    IsWt L lam ξ ∧ ∀ s : List J →₀ ℂ, wop θ s ≠ 0 → ∃ a : List J →₀ ℂ,
      Good G K (polyFn K ψ (wmul a s) f) ∧ dTrace G ξ K (polyFn K ψ (wmul a s) f) (Kp G) (oneP G) ≠ 0

def summ {p : ℕ} [Fact p.Prime] (G : HTGroup p) (v : InfinitePlace G.F) (c : G.F[X] → ℂ → ℂ) (K : Subgroup G.GAf)
    (f : G.GAf → ℂ) (z : Σ q : FCls G, PtsOf G v K q × grp G (Quot.out q).β) : ℂ :=
  ((Nat.card (Stab G v (Quot.out z.1).β (Quot.out z.1).trivAf.choose (Quot.out z.1).trivAf.choose_spec.choose
      (Quot.out z.1).trivAf.choose_spec.choose_spec K (Kp G) (Quot.out z.2.1)) : ℕ) : ℂ)⁻¹ *
    if FixL G v (Quot.out z.1).β z.2.2 (Quot.out z.2.1).2.1 then
      f ((Quot.out z.2.1).1.1⁻¹ * toAfF G (Quot.out z.1).β (Quot.out z.1).trivAf.choose
          (Quot.out z.1).trivAf.choose_spec.choose (Quot.out z.1).trivAf.choose_spec.choose_spec z.2.2 *
          (Quot.out z.2.1).1.1) *
        oneP G ((Quot.out z.2.1).1.2⁻¹ * toP1 G (Quot.out z.1).β z.2.2 * (Quot.out z.2.1).1.2) *
        c (minpoly G.F (((z.2.2 : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) (eigL G v (Quot.out z.1).β z.2.2 (Quot.out z.2.1).2.1)
    else 0

def InvRoots : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (P : F[X]), P.coeff 0 ≠ 0 → ∀ τ : F →+* ℂ,
    rts (invPol P) τ = (rts P τ).map fun z => z⁻¹

def InvPolProps : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (P : F[X]), P.coeff 0 ≠ 0 →
    (invPol P).natDegree = P.natDegree ∧ (invPol P).coeff 0 ≠ 0 ∧ (P.Separable → (invPol P).Separable)

def ListsEx : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (n : ℕ) (χ : F[X]), χ.natDegree = n → ∃ g : (F →+* ℂ) → Fin n → ℂ, Lists χ g

def SchWEq : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (n : ℕ) (lam : (F →+* ℂ) → Fin n → ℕ) (χ : F[X]) (g : (F →+* ℂ) → Fin n → ℂ),
    Lists χ g → schW lam χ = ∏ τ, UpperTheory.Gal.Schur.sch (lam τ) (g τ)

def RootW : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (n : ℕ) (t₀ : F →+* ℂ) (ε : (F →+* ℂ) → ℕ) (lam : (F →+* ℂ) → Fin n → ℕ)
    (h : Fin n → ℕ), ComplexEmbedding.conjugate t₀ ≠ t₀ → IsHExp t₀ ε lam h →
    ∃ k₀, ∀ k, k₀ ≤ k → ∃ c : (Fin k → 𝓞 F) →₀ ℂ, (∀ α ∈ c.support, ∀ s, α s ≠ 0 ∧ (2 : 𝓞 F) ∣ α s) ∧
      ∀ χ : F[X], χ.natDegree = n → χ.Separable → χ.coeff 0 ≠ 0 →
        (∃ q : ℝ, ∀ z ∈ rts χ t₀, z * (starRingEnd ℂ) z = q) → ∀ y : ℂ,
        (c.sum fun α w => w * ((rts χ t₀).map fun mu => locW t₀ ε α y χ mu).sum) = schW lam χ * ∑ i, y ^ h i

def HExpInj : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (n : ℕ) (t₀ : F →+* ℂ) (ε : (F →+* ℂ) → ℕ) (lam : (F →+* ℂ) → Fin n → ℕ)
    (h : Fin n → ℕ), (∀ τ, Antitone (lam τ)) → IsHExp t₀ ε lam h → Function.Injective h

def UnifBound : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (n : ℕ) (I : Type) [Finite I] (t : I → (F →+* ℂ)) (ε : (F →+* ℂ) → ℕ)
    (lam : (F →+* ℂ) → Fin n → ℕ) (κ : ((F →+* ℂ) → Fin n → ℕ) → I → (Fin n → ℕ) → ℕ),
    ∃ k₀, ∀ (σ : ℂ ≃+* ℂ) (i : I) (h : Fin n → ℕ), IsHExp (t i) ε (conjWt σ lam) h → κ (conjWt σ lam) i h ≤ k₀

def LefSum : Prop :=
  ∀ (d : ℕ) (A : Matrix (Fin d) (Fin d) ℂ) (y : ℂ),
    ∑ a ∈ Finset.range (d + 1), (-y) ^ a * ((Matrix.det (1 + (X : ℂ[X]) • A.map C)).coeff a / (1 - A).det) = lefTerm A y

def CoeffOcc : Prop :=
  ∀ (d n : ℕ) (t : ℕ → ℂ) (c : ℂ) (h : Fin n → ℕ), Function.Injective h → c ≠ 0 →
    (∀ y : ℂ, ∑ a ∈ Finset.range (d + 1), (-y) ^ a * t a = c * ∑ i, y ^ h i) → ∀ i, t (h i) ≠ 0

def EigOf : Prop :=
  ∀ (B J : Type) [Finite B] (W : B → Type) [∀ b, AddCommGroup (W b)] [∀ b, Module ℂ (W b)] [∀ b, FiniteDimensional ℂ (W b)]
    (T : ∀ b, J → Module.End ℂ (W b)) (u : ∀ b, Module.End ℂ (W b)) (θ : J → ℂ),
    (∀ b j j' (w : List J), T b j * T b j' * (w.map (T b)).prod * u b = T b j' * T b j * (w.map (T b)).prod * u b) →
    ∃ s : List J →₀ ℂ, wop θ s = 1 ∧ ∀ b, wop (T b) s * u b ≠ 0 → ∃ x : W b, x ≠ 0 ∧ ∀ j, T b j x = θ j • x

def MarkRoots : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : GlobalTheory.LKGeo.Link D G), D.a = 1 → ∀ (i₀ : Fin D.a)
    (v : InfinitePlace G.F), sigPosH (G.gram_herm v) = 1 → InvRoots → ∀ P : G.F[X], P.coeff 0 ≠ 0 →
      ((P.map v.embedding).roots).map (markOf L v) = rts (endPol L P) (D.tau i₀)

def DPairPol : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : DPair G) (v : InfinitePlace G.F),
    P.pol.coeff 0 ≠ 0 ∧ ∃ q : ℝ, ∀ z ∈ (P.pol.map v.embedding).roots, z * (starRingEnd ℂ) z = q

def DSumCongr : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (wt wt' : G.F[X] → ℂ) (s : ℂ), (∀ P : DPair G, wt P.pol = wt' P.pol * s) →
    ∀ (K : Subgroup G.GAf) (f : G.GAf → ℂ) (r : ℕ) (K' : Subgroup (Gr G r)) (φ : Gr G r → ℂ),
      dSumIrr G wt K f r K' φ = dSumIrr G wt' K f r K' φ * s

def CxFlat : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : InfinitePlace G.F) (c : G.F[X] → ℂ → ℂ) (K : Subgroup G.GAf) (f : G.GAf → ℂ)
    (S : Finset (Σ q : FCls G, PtsOf G v K q × grp G (Quot.out q).β)), (∀ z, Seen G v K f z.1 z.2.1 z.2.2 → z ∈ S) →
      cxTotalM G v c K f (Kp G) (oneP G) = ∑ z ∈ S, summ G v c K f z

def CxLin : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : InfinitePlace G.F) (K : Subgroup G.GAf) (m : ℕ) (f : Fin m → G.GAf → ℂ)
    (a : Fin m → ℂ), (∀ i, CxFin G v K (f i)) → ∀ (A : Type) (w : A →₀ ℂ) (c : A → G.F[X] → ℂ → ℂ),
      cxTotalM G v (fun P μ => w.sum fun α r => r * c α P μ) K (∑ i, a i • f i) (Kp G) (oneP G) =
        ∑ i, a i * w.sum fun α r => r * cxTotalM G v (c α) K (f i) (Kp G) (oneP G)

def TestOf : Prop :=
  ∀ (H : Type) [Group H] (K : Subgroup H) (f : H → ℂ), f ∈ Formalism.UG.Hecke ℂ K →
    IsTest (MonoidHom.id H) K K f ∧ ∀ k ∈ K, ∀ k' ∈ K, ∀ g, f (k * g * k') = f g

def TestOne : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) (Kp G) (oneP G) ∧
    ∀ k ∈ Kp G, ∀ k' ∈ Kp G, ∀ g, oneP G (k * g * k') = oneP G g

def GroupTop : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : GlobalTheory.LKGeo.Link D G) (lam : (D.F →+* ℂ) → Fin G.n → ℕ)
    (i₀ : Fin D.a) (h : Fin G.n → ℕ), IsHExp (D.tau i₀) (epsOf D) lam h →
    ∃ k₀, ∀ k, k₀ ≤ k → ∃ c : (Fin k → 𝓞 D.F) →₀ ℂ, (∀ α ∈ c.support, ∀ s, α s ≠ 0 ∧ (2 : 𝓞 D.F) ∣ α s) ∧
      (D.a = 1 → G.a = 1 → Odd G.n → ∀ v : InfinitePlace G.F, sigPosH (G.gram_herm v) = 1 →
      ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (ξ : Representation ℂ (G.Cˣ × ℚˣ) V),
        IsWt L lam ξ → ∀ (Lv : G.Level) (f : G.GAf → ℂ), f ∈ Formalism.UG.Hecke ℂ Lv.K.toSubgroup → Good G Lv.K.toSubgroup f →
        ∀ y : ℂ, cxTotalM G v (fun P μ => c.sum fun α r => r * cW L i₀ v α y P μ) Lv.K.toSubgroup f (Kp G) (oneP G) =
          dTrace G ξ Lv.K.toSubgroup f (Kp G) (oneP G) * ∑ i, y ^ h i)

def IsSemi (σ : ℂ ≃+* ℂ) {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (e : V ≃+ V') : Prop :=
  ∀ (c : ℂ) (x : V), e (c • x) = σ c • e x

def TraceSemi : Prop :=
  ∀ (σ : ℂ ≃+* ℂ) (V V' : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (e : V ≃+ V'), IsSemi σ e →
    ∀ (T : Module.End ℂ V) (T' : Module.End ℂ V'), (∀ x, e (T x) = T' (e x)) →
      LinearMap.trace ℂ V' T' = σ (LinearMap.trace ℂ V T)

def ConjRep : Prop :=
  ∀ (σ : ℂ ≃+* ℂ) (Γ V : Type) [Group Γ] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (ξ : Representation ℂ Γ V),
    ∃ (V' : Type) (_ : AddCommGroup V') (_ : Module ℂ V') (_ : FiniteDimensional ℂ V') (ξ' : Representation ℂ Γ V')
      (e : V ≃+ V'), IsSemi σ e ∧ ∀ g x, e (ξ g x) = ξ' g (e x)

def HeckeTraceSemi : Prop :=
  ∀ (σ : ℂ ≃+* ℂ) (Γ H V V' : Type) [Group Γ] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    (ξ : Representation ℂ Γ V) (ξ' : Representation ℂ Γ V') (e : V ≃+ V'), IsSemi σ e → (∀ g x, e (ξ g x) = ξ' g (e x)) →
    ∀ (ι : Γ →* H) (K : Subgroup H) (F : H → ℂ),
      HeckeTraceForms.heckeTrace ι K ξ' (fun h => σ (F h)) = σ (HeckeTraceForms.heckeTrace ι K ξ F)

def GoodConj : Prop :=
  ∀ (σ : ℂ ≃+* ℂ) (p : ℕ) [Fact p.Prime] (G : HTGroup p) (K : Subgroup G.GAf) (f : G.GAf → ℂ),
    Good G K f → Good G K fun g => σ (f g)

def SchWConj : Prop :=
  ∀ (σ : ℂ ≃+* ℂ) (F : Type) [Field F] [NumberField F] (n : ℕ) (lam : (F →+* ℂ) → Fin n → ℕ) (χ : F[X]),
    schW (conjWt σ lam) χ = σ (schW lam χ)

def PolyFnConj : Prop :=
  ∀ (σ : ℂ ≃+* ℂ) (H J : Type) [Group H] (K : Subgroup H) (ψ : J → H → ℂ) (f : H → ℂ),
    (∀ w : List J, wordFn K (fun j g => σ (ψ j g)) w (fun g => σ (f g)) = fun g => σ (wordFn K ψ w f g)) ∧
    (∀ s : List J →₀ ℂ, polyFn K (fun j g => σ (ψ j g)) (wmap σ.toRingHom s) (fun g => σ (f g)) =
      fun g => σ (polyFn K ψ s f g)) ∧
    ∀ a s : List J →₀ ℂ, wmap σ.toRingHom (wmul a s) = wmul (wmap σ.toRingHom a) (wmap σ.toRingHom s)

def SpecConj : Prop :=
  ∀ (σ : ℂ ≃+* ℂ) (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : GlobalTheory.LKGeo.Link D G)
    (lam : (D.F →+* ℂ) → Fin G.n → ℕ) (K : Subgroup G.GAf) (J : Type) (ψ : J → G.GAf → ℂ) (θ : J → ℂ) (f : G.GAf → ℂ),
    Spec L lam K ψ θ f → Spec L (conjWt σ lam) K (fun j g => σ (ψ j g)) (fun j => σ (θ j)) fun g => σ (f g)

end UpperTheory.Gal.LocalSmoothExtension
end
end
