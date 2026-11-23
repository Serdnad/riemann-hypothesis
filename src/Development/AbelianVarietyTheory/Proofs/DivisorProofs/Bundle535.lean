module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.RingHom.Flat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle488
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle489
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle325
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle490
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle438
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.IsStrictDom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle002

@[expose] public section

section

open IsLocalRing TensorProduct

theorem _root_.GlobalTheory.T.isOpen_regularLocus_of_nagata' : ∀ (B : Type) [CommRing B] [IsNoetherianRing B], (∀ (p : Ideal B) [p.IsPrime], ∃ g, g ∉ p ∧ ∀ (q : Ideal B) [q.IsPrime], p ≤ q → g ∉ q → IsRegularLocalRing (Localization.AtPrime q ⧸ p.map (algebraMap B (Localization.AtPrime q)))) → IsOpen {Q : PrimeSpectrum B | IsRegularLocalRing (Localization.AtPrime Q.asIdeal)} := by
  first | exact @GlobalTheory.isOpen_regularLocus_of_nagata | exact GlobalTheory.isOpen_regularLocus_of_nagata | (intros; apply GlobalTheory.isOpen_regularLocus_of_nagata <;> assumption)
end

section

open IsLocalRing

theorem _root_.GlobalTheory.T.exists_regular_local_extension_with_simple_root : ∀ (A Ω : Type) [CommRing A] [IsRegularLocalRing A] [Field Ω] (u : A →+* Ω) (p : Polynomial A) (α : Ω), RingHom.ker u = maximalIdeal A → IsAdicComplete (maximalIdeal A) A → p.Monic → (p.map u).eval α = 0 → (p.map u).derivative.eval α ≠ 0 → ∃ (E : Type) (_ : CommRing E) (_ : IsRegularLocalRing E) (a : A →+* E) (v : E →+* Ω), a.Flat ∧ (maximalIdeal A).map a = maximalIdeal E ∧ IsAdicComplete (maximalIdeal E) E ∧ RingHom.ker v = maximalIdeal E ∧ v.comp a = u ∧ α ∈ v.range := by
  first | exact @GlobalTheory.MonicRootExtension.exists_extension | exact GlobalTheory.MonicRootExtension.exists_extension | (intros; apply GlobalTheory.MonicRootExtension.exists_extension <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
noncomputable section

namespace GlobalTheory.HomFixMat

abbrev powPull {X Y : Scheme.{0}} (L : LB X) (φ : Y ⟶ X) (a : ℤ) : LB Y :=
  LB.LinComb L (K := Fin 1) (fun _ => φ) (fun _ => a)

theorem wchart_comp_le {X Y Z : Scheme.{0}} (L : LB X) (f : Z ⟶ Y) (φ : Y ⟶ X) (j : Fin 1 → L.ι) :
    LB.wchart L (fun _ : Fin 1 => f ≫ φ) j ≤ f ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => φ) j := by
  intro y hy
  exact Set.mem_iInter.2 fun k => by
    have := Set.mem_iInter.1 hy k
    simpa using this

variable {Rg : Type} [CommRing Rg] {A B : Over (Sp Rg)} [GrpObj A] [GrpObj B] {L : LB A.left} {M : LB B.left}

abbrev topS (Rg : Type) [CommRing Rg] : Over (Sp Rg) := overRes (T := baseOver (Sp Rg)) ⊤

def coord {X : Scheme.{0}} {N : ℕ} (g : X ⟶ Sp (MvPolynomial (Fin N) Rg)) (n : Fin N) : Γ(X, ⊤) :=
  g.appTop ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin N) Rg))).inv (MvPolynomial.X n))

def matOf {X : Scheme.{0}} {mA mB : ℕ} (g : X ⟶ Sp (MvPolynomial (Fin (mA * mB)) Rg)) :
    Fin mA → Fin mB → Γ(X, ⊤) :=
  fun i j => coord g (finProdFinEquiv (i, j))

abbrev affπ (Rg : Type) [CommRing Rg] (N : ℕ) : Sp (MvPolynomial (Fin N) Rg) ⟶ Sp Rg :=
  Spec.map (CommRingCat.ofHom (algebraMap Rg (MvPolynomial (Fin N) Rg)))


variable (A B L M) in
def IsTest {T : Scheme.{0}} (t : T ⟶ Sp Rg) (A' B' : Over T) [GrpObj A'] [GrpObj B'] (φA' : A'.left ⟶ A.left)
    (φB' : B'.left ⟶ B.left) (Φ' : A' ⟶ B') : Prop :=
  IsGrpPullback A' A t φA' ∧ IsGrpPullback B' B t φB' ∧ IsMonHom Φ' ∧
    LBIso (L.pull φA') ((M.pull φB').pull Φ'.left)

def IsPullD {T₁ T₂ : Scheme.{0}} {A₁ B₁ : Over T₁} [GrpObj A₁] [GrpObj B₁] (φA₁ : A₁.left ⟶ A.left)
    (φB₁ : B₁.left ⟶ B.left) (Φ₁ : A₁ ⟶ B₁) {A₂ B₂ : Over T₂} [GrpObj A₂] [GrpObj B₂] (φA₂ : A₂.left ⟶ A.left)
    (φB₂ : B₂.left ⟶ B.left) (Φ₂ : A₂ ⟶ B₂) (h : T₂ ⟶ T₁) : Prop :=
  ∃ (ψA : A₂.left ⟶ A₁.left) (ψB : B₂.left ⟶ B₁.left), IsGrpPullback A₂ A₁ h ψA ∧
    IsGrpPullback B₂ B₁ h ψB ∧ ψA ≫ φA₁ = φA₂ ∧ ψB ≫ φB₁ = φB₂ ∧ Φ₂.left ≫ ψB = ψA ≫ Φ₁.left


variable (A L) in
def IsBCBasis (k : ℕ) {m : ℕ} (b : Fin m → LB.Sec (LPow A L (k : ℤ) (topS Rg))) : Prop :=
  ∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ (topS Rg).left)
    (b' : Fin m → LB.Sec (LPow A L (k : ℤ) (baseAt t))),
    (∀ i, IsPullSec A L (k : ℤ) (homAt t ▷ A) (whiskerRight_snd (homAt t) A) (b i) (b' i)) →
    LinearIndependent Γ((baseAt t).left, ⊤) (fun i => (SecM.ofSec A (b' i) : SecM A L (k : ℤ) (baseAt t))) ∧
    Submodule.span Γ((baseAt t).left, ⊤)
      (Set.range fun i => (SecM.ofSec A (b' i) : SecM A L (k : ℤ) (baseAt t))) = ⊤

end GlobalTheory.HomFixMat

namespace GlobalTheory.HomFixMat

variable {Rg : Type} [CommRing Rg] {A B : Over (Sp Rg)} [GrpObj A] [GrpObj B] {L : LB A.left} {M : LB B.left}

abbrev isoLB (k : ℕ) {R : Type} [CommRing R] {A' B' : Over (Sp R)} (Φ' : A' ⟶ B')
    (ψA : A'.left ⟶ (topS Rg ⊗ A).left) (ψB : B'.left ⟶ (topS Rg ⊗ B).left) : LB A'.left :=
  LB.div (powPull M ((Φ'.left ≫ ψB) ≫ (snd (topS Rg) B).left) (k : ℤ))
    (powPull L (ψA ≫ (snd (topS Rg) A).left) (k : ℤ))

abbrev zeroPt {R : Type} [CommRing R] (A' : Over (Sp R)) [GrpObj A'] : Sp R ⟶ A'.left := η[A'].left


variable (L M) in
def IsMat (k : ℕ) {mA mB : ℕ} (bA : Fin mA → LB.Sec (LPow A L (k : ℤ) (topS Rg)))
    (bB : Fin mB → LB.Sec (LPow B M (k : ℤ) (topS Rg))) (eA : LB.Gen (L.pull (eSec A)))
    (eB : LB.Gen (M.pull (eSec B))) {R : Type} [CommRing R] (t : Sp R ⟶ Sp Rg) (A' B' : Over (Sp R)) [GrpObj A']
    [GrpObj B'] (φA' : A'.left ⟶ A.left) (φB' : B'.left ⟶ B.left) (Φ' : A' ⟶ B')
    (c : Fin mA → Fin mB → Γ(Sp R, ⊤)) : Prop :=
  ∃ (ψA : A'.left ⟶ (topS Rg ⊗ A).left) (ψB : B'.left ⟶ (topS Rg ⊗ B).left)
    (α : LB.Gen (isoLB (L := L) (M := M) k Φ' ψA ψB)),
    ψA ≫ (snd (topS Rg) A).left = φA' ∧ ψB ≫ (snd (topS Rg) B).left = φB' ∧ α.IsGen ∧
    (∀ p : (Fin 1 → M.ι) × (Fin 1 → L.ι),
      ((zeroPt A').appLE ((isoLB (L := L) (M := M) k Φ' ψA ψB).U p)
          ((zeroPt A') ⁻¹ᵁ (isoLB (L := L) (M := M) k Φ' ψA ψB).U p ⊓
            t ⁻¹ᵁ LB.wchart L (fun _ : PUnit => eSec A) (fun _ => p.2 0) ⊓
            t ⁻¹ᵁ LB.wchart M (fun _ : PUnit => eSec B) (fun _ => p.1 0))
          (inf_le_left.trans inf_le_left)).hom (α.s p).val *
        ((t.appLE (LB.wchart L (fun _ : PUnit => eSec A) (fun _ => p.2 0))
          ((zeroPt A') ⁻¹ᵁ (isoLB (L := L) (M := M) k Φ' ψA ψB).U p ⊓
            t ⁻¹ᵁ LB.wchart L (fun _ : PUnit => eSec A) (fun _ => p.2 0) ⊓
            t ⁻¹ᵁ LB.wchart M (fun _ : PUnit => eSec B) (fun _ => p.1 0))
          (inf_le_left.trans inf_le_right)).hom (eA.s (fun _ => p.2 0)).val) ^ k =
      ((t.appLE (LB.wchart M (fun _ : PUnit => eSec B) (fun _ => p.1 0))
          ((zeroPt A') ⁻¹ᵁ (isoLB (L := L) (M := M) k Φ' ψA ψB).U p ⊓
            t ⁻¹ᵁ LB.wchart L (fun _ : PUnit => eSec A) (fun _ => p.2 0) ⊓
            t ⁻¹ᵁ LB.wchart M (fun _ : PUnit => eSec B) (fun _ => p.1 0))
          inf_le_right).hom (eB.s (fun _ => p.1 0)).val) ^ k) ∧
    ∀ (j : Fin mB) (p : (Fin 1 → M.ι) × (Fin 1 → L.ι)),
      ((Φ'.left ≫ ψB).appLE (LB.wchart M (fun _ : Fin 1 => (snd (topS Rg) B).left) p.1)
          ((isoLB (L := L) (M := M) k Φ' ψA ψB).U p)
          (inf_le_left.trans (wchart_comp_le M _ _ p.1))).hom ((bB j).f p.1) =
        (α.s p).val * ∑ i, (A'.hom.appLE ⊤ ((isoLB (L := L) (M := M) k Φ' ψA ψB).U p) (by simp)).hom (c i j) *
          (ψA.appLE (LB.wchart L (fun _ : Fin 1 => (snd (topS Rg) A).left) p.2)
            ((isoLB (L := L) (M := M) k Φ' ψA ψB).U p)
            (inf_le_right.trans (wchart_comp_le L _ _ p.2))).hom ((bA i).f p.2)

end GlobalTheory.HomFixMat

namespace GlobalTheory.HomFixMat

variable {Rg : Type} [CommRing Rg] {A B : Over (Sp Rg)} [GrpObj A] [GrpObj B] {L : LB A.left} {M : LB B.left}


variable (L M) in
def Hyps (k : ℕ) {mA mB : ℕ} (bA : Fin mA → LB.Sec (LPow A L (k : ℤ) (topS Rg)))
    (bB : Fin mB → LB.Sec (LPow B M (k : ℤ) (topS Rg))) (eA : LB.Gen (L.pull (eSec A)))
    (eB : LB.Gen (M.pull (eSec B))) : Prop :=
  IsAbelianScheme A ∧ IsAbelianScheme B ∧ L.IsLB ∧ M.IsLB ∧ eA.IsGen ∧ eB.IsGen ∧ RelAmple A L ∧ 1 ≤ k ∧
    VeryAmpleAt B M k ∧ IsBCBasis A L k bA ∧ IsBCBasis B M k bB

end GlobalTheory.HomFixMat

namespace GlobalTheory.HomFixMat
variable {Rg : Type} [CommRing Rg] {A B : Over (Sp Rg)} [GrpObj A] [GrpObj B]

theorem IsPullD.comp {T₁ T₂ T₃ : Scheme.{0}} {A₁ B₁ : Over T₁} [GrpObj A₁] [GrpObj B₁] {φA₁ : A₁.left ⟶ A.left}
    {φB₁ : B₁.left ⟶ B.left} {Φ₁ : A₁ ⟶ B₁} {A₂ B₂ : Over T₂} [GrpObj A₂] [GrpObj B₂] {φA₂ : A₂.left ⟶ A.left}
    {φB₂ : B₂.left ⟶ B.left} {Φ₂ : A₂ ⟶ B₂} {A₃ B₃ : Over T₃} [GrpObj A₃] [GrpObj B₃] {φA₃ : A₃.left ⟶ A.left}
    {φB₃ : B₃.left ⟶ B.left} {Φ₃ : A₃ ⟶ B₃} {h₁ : T₂ ⟶ T₁} {h₂ : T₃ ⟶ T₂}
    (p₁ : IsPullD φA₁ φB₁ Φ₁ φA₂ φB₂ Φ₂ h₁) (p₂ : IsPullD φA₂ φB₂ Φ₂ φA₃ φB₃ Φ₃ h₂) :
    IsPullD φA₁ φB₁ Φ₁ φA₃ φB₃ Φ₃ (h₂ ≫ h₁) := by
  obtain ⟨ψA, ψB, qA, qB, eA, eB, eΦ⟩ := p₁
  obtain ⟨ψA', ψB', qA', qB', eA', eB', eΦ'⟩ := p₂
  refine ⟨ψA' ≫ ψA, ψB' ≫ ψB, qA'.comp qA, qB'.comp qB, by rw [Category.assoc, eA, eA'],
    by rw [Category.assoc, eB, eB'], ?_⟩
  rw [← Category.assoc, eΦ', Category.assoc, eΦ, Category.assoc]

end GlobalTheory.HomFixMat

namespace GlobalTheory.HomFixMat

theorem hom_ext_affine (Rg : Type) [CommRing Rg] (N : ℕ) (X : Scheme.{0}) (g g' : X ⟶ Sp (MvPolynomial (Fin N) Rg))
    (h0 : g ≫ affπ Rg N = g' ≫ affπ Rg N) (h1 : ∀ n, coord g n = coord g' n) : g = g' := by
  apply ext_of_isAffine
  refine (Iso.cancel_iso_inv_left (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin N) Rg))) _ _).1 ?_
  ext1
  apply MvPolynomial.ringHom_ext
  · intro r
    have e := congrArg (fun f => f.appTop ((Scheme.ΓSpecIso (CommRingCat.of Rg)).inv r)) h0
    simp only [Scheme.Hom.comp_appTop] at e
    have n2 : (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin N) Rg))).inv (MvPolynomial.C r) =
        (affπ Rg N).appTop ((Scheme.ΓSpecIso (CommRingCat.of Rg)).inv r) := by
      rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality]; rfl
    simp only [RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_comp]
    rw [n2]
    simpa using e
  · intro n
    exact h1 n

end GlobalTheory.HomFixMat
end
end

section

set_option autoImplicit false

namespace GlobalTheory.ConjugateMultiplicitySum

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem conj_eq_iff {z w : ℂ} {d : ℕ} (hd : 0 < d) (hz : z ^ 2 = -(d : ℂ)) (hw : w ^ 2 = -(d : ℂ)) :
    starRingEnd ℂ z = w ↔ ¬ z = w := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hre : z.re * z.re - z.im * z.im = -(d : ℝ) := by
    have := congrArg Complex.re hz
    simpa [pow_two] using this
  have him : z.re * z.im = 0 := by
    have := congrArg Complex.im hz
    simp [pow_two] at this
    linarith
  have hre0 : z.re = 0 := by
    rcases mul_eq_zero.1 him with h | h
    · exact h
    · rw [h] at hre
      nlinarith [mul_self_nonneg z.re]
  have hc : starRingEnd ℂ z = -z := by
    apply Complex.ext <;> simp [hre0]
  have hz0 : z ≠ 0 := by
    rintro rfl
    simp at hre
    exact hd.ne' hre
  rw [hc]
  constructor
  · intro h1 h2
    apply hz0
    have : (2 : ℂ) * z = 0 := by linear_combination h2 - h1
    simpa using this
  · intro h
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 (hz.trans hw.symm) with h1 | h1
    · exact absurd h1 h
    · rw [h1, neg_neg]

theorem mult_add_mult_conj {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)
    (τ : E →+* ℂ) : Datum.mult D τ + Datum.mult D (conjEmb τ) = D.p + D.q := by
  have hsq : (τ (H.rt : E)) ^ 2 = -(H.d : ℂ) := by
    have h := congrArg (fun a : 𝓞 E => τ (algebraMap (𝓞 E) E a)) H.rt_sq
    simpa using h
  have key : conjEmb τ (H.rt : E) = H.rt0 ↔ ¬ τ (H.rt : E) = H.rt0 :=
    conj_eq_iff H.d_prime.pos hsq H.sqrt_neg_disc_sq
  unfold Datum.mult
  by_cases h : τ (H.rt : E) = H.rt0
  · rw [if_pos h, if_neg (fun h' => key.1 h' h)]
  · rw [if_neg h, if_pos (key.2 h), add_comm]

end GlobalTheory.ConjugateMultiplicitySum
end

section

open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.extend_affineLine_morphism_to_proper_across_point : ∀ (k : Type) [Field k] (B : Over (Sp k)) [IsProper B.hom] [LocallyOfFinitePresentation B.hom] (P : Polynomial k) (c : k), P ≠ 0 → ∀ u : Sp (Localization.Away (P * (Polynomial.X - Polynomial.C c))) ⟶ B.left, u ≫ B.hom = spMap (algebraMap k (Localization.Away (P * (Polynomial.X - Polynomial.C c)))) → ∃ v : Sp (Localization.Away P) ⟶ B.left, v ≫ B.hom = spMap (algebraMap k (Localization.Away P)) ∧ spMap (IsLocalization.Away.awayToAwayRight (S := Localization.Away P) (P := Localization.Away (P * (Polynomial.X - Polynomial.C c))) P (Polynomial.X - Polynomial.C c)) ≫ v = u := by
  first | exact @GlobalTheory.AffineLineExt.extend | exact GlobalTheory.AffineLineExt.extend | (intros; apply GlobalTheory.AffineLineExt.extend <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

theorem _root_.GlobalTheory.T.chow_lemma_projective_modification : ∀ (R : Type) [CommRing R] [IsNoetherianRing R], ∀ (W : Scheme.{0}) (f : W ⟶ Spec (CommRingCat.of R)), IsSeparated f → LocallyOfFiniteType f → QuasiCompact f → Nonempty W → ∃ (W' P : Scheme.{0}) (π : W' ⟶ W) (q : W' ⟶ P) (s : P ⟶ Spec (CommRingCat.of R)) (U : W.Opens), IsProper π ∧ (U : Set W).Nonempty ∧ IsIso (π ∣_ U) ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver s ∧ IsImmersion q ∧ q ≫ s = π ≫ f := by
  first | exact @GlobalTheory.FormalAlg.exists_isProper_isImmersion_isProjOver | exact GlobalTheory.FormalAlg.exists_isProper_isImmersion_isProjOver | (intros; apply GlobalTheory.FormalAlg.exists_isProper_isImmersion_isProjOver <;> assumption)
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MumCmp

section Maps

variable {X Y X' : Scheme.{0}} (L : LB X) (L' : LB X') {J : Type} [Fintype J]

lemma mapsAtExp_le_b (pr : J → (X' ⟶ X)) (ε : J → ℤ) (p : Y ⟶ X') (jN : J → L.ι) (jL : L'.ι) :
    p ⁻¹ᵁ (LB.div (LB.LinComb L pr ε) L').U (jN, jL) ≤ LB.wchart L (fun i => p ≫ pr i) jN := by
  intro y hy
  refine Set.mem_iInter.2 fun i => ?_
  have h1 : p.base y ∈ LB.wchart L pr jN := hy.1
  exact Set.mem_iInter.1 h1 i

lemma mapsAtExp_le_a (pr : J → (X' ⟶ X)) (ε : J → ℤ) (p : Y ⟶ X') (jN : J → L.ι) (jL : L'.ι) :
    p ⁻¹ᵁ (LB.div (LB.LinComb L pr ε) L').U (jN, jL) ≤ LB.wchart L' (fun _ : PUnit => p) (fun _ => jL) :=
  fun _ hy => Set.mem_iInter.2 fun _ => hy.2

def MapsAtExp (pr : J → (X' ⟶ X)) (ε : J → ℤ) (w : LB.Iso L' (LB.LinComb L pr ε)) (p : Y ⟶ X') (n : ℤ)
    (a : LB.Gen (LB.LinComb L' (K := PUnit) (fun _ => p) (fun _ => n)))
    (b : LB.Gen (LB.LinComb L (K := J) (fun i => p ≫ pr i) (fun i => n * ε i))) : Prop :=
  ∀ (jN : J → L.ι) (jL : L'.ι),
    res (mapsAtExp_le_b L L' pr ε p jN jL) (b.s jN) =
      (pullU p _ (w.s (jN, jL))) ^ n * res (mapsAtExp_le_a L L' pr ε p jN jL) (a.s (fun _ => jL))

end Maps

variable {R : Type} [CommRing R] [IsDomain R]

def twφ (D₀ D : DegPre R) (β : D₀.P.A ⟶ D.P.A) (b : 𝟙_ (Over (Sp R)) ⟶ D.P.A) : Fin 3 → (D₀.P.A.left ⟶ D.P.A.left) :=
  ![(padd D.P.A β (toUnit D₀.P.A ≫ b)).left, (toUnit D₀.P.A ≫ b).left, (toUnit D₀.P.A ≫ η[D.P.A]).left]

def twε : Fin 3 → ℤ := ![1, -1, 1]

def IsTwist (D₀ D : DegPre R) (g : GtPt D (𝟙_ (Over (Sp R)))) : Prop :=
  ∃ (β : D₀.P.A ≅ D.P.A) (xe : D₀.X ≃+ D.X), IsMonHom β.hom ∧ (∀ χ, D₀.c χ ≫ β.hom = D.c (xe χ)) ∧
    ∃ w : LB.Iso D₀.P.L (LB.LinComb D.P.L (twφ D₀ D β.hom g.b) twε), w.IsGen ∧
      ∀ χ : D₀.X, ∃ t : LB.Gen (LB.LinComb D.P.L (fun i => D₀.xK χ ≫ twφ D₀ D β.hom g.b i) (fun i => -1 * twε i)),
        MapsAtExp D.P.L D₀.P.L (twφ D₀ D β.hom g.b) twε w (D₀.xK χ) (-1) (D₀.psi χ) t ∧
        LB.Gen.Corr D.P.L _ _ _ _ t
          (LB.mulGen D.P.L _ _ _ _ (D.psi (xe χ)) (LB.pullGen D.P.L _ _ (g.s (xe χ)) (toUnit (TK R)).left))

end GlobalTheory.MumCmp
end
end

section

open AlgebraicGeometry CategoryTheory IsLocalRing ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out

namespace GlobalTheory

theorem proper_lift_trait : ∀ {X Y : Scheme.{0}} (π : Y ⟶ X), IsProper π → ∀ (V V' : Type) [CommRing V] [IsDomain V] [CommRing V'] [IsDomain V'] [IsDiscreteValuationRing V'] (f : V →+* V') (fK : FractionRing V →+* FractionRing V'), (∀ a, fK (algebraMap V _ a) = algebraMap V' _ (f a)) → ∀ (ξ : Sp V ⟶ X) (y : Sp (FractionRing V') ⟶ Y), y ≫ π = spMap fK ≫ jK V ≫ ξ → ∃ ξ' : Sp V' ⟶ Y, ξ' ≫ π = spMap f ≫ ξ ∧ jK V' ≫ ξ' = y := by
  intro X Y π hπ V V' _ _ _ _ _ f fK hf ξ y hy
  have hsq : jK V' ≫ spMap f = spMap fK ≫ jK V := by
    have e : fK.comp (algebraMap V (FractionRing V)) = (algebraMap V' (FractionRing V')).comp f :=
      RingHom.ext hf
    exact (spMap_comp f (algebraMap V' (FractionRing V'))).symm.trans
      ((congrArg spMap e.symm).trans (spMap_comp (algebraMap V (FractionRing V)) fK))
  have h : y ≫ π = jK V' ≫ (spMap f ≫ ξ) := by
    rw [hy, ← Category.assoc, ← hsq, Category.assoc]
  obtain ⟨x, hx1, hx2⟩ := val_exists (R := V') π y (spMap f ≫ ξ) h
  exact ⟨x, hx2, hx1⟩

end GlobalTheory
end

section

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.LBDescent

variable {X Y : Scheme.{0}} (f : X ⟶ Y)

abbrev Triple : Scheme.{0} := pullback (pullback.snd f f) (pullback.fst f f)

def pr13 : Triple f ⟶ pullback f f :=
  pullback.lift (pullback.fst _ _ ≫ pullback.fst f f) (pullback.snd _ _ ≫ pullback.snd f f) (by
    calc (pullback.fst _ _ ≫ pullback.fst f f) ≫ f = pullback.fst (pullback.snd f f) (pullback.fst f f) ≫
          pullback.snd f f ≫ f := by rw [Category.assoc, pullback.condition]
      _ = pullback.snd (pullback.snd f f) (pullback.fst f f) ≫ pullback.fst f f ≫ f := pullback.condition_assoc _
      _ = (pullback.snd _ _ ≫ pullback.snd f f) ≫ f := by rw [pullback.condition, Category.assoc])

def chart (L : LB X) (i j : L.ι) : (pullback f f).Opens :=
  pullback.fst f f ⁻¹ᵁ L.U i ⊓ pullback.snd f f ⁻¹ᵁ L.U j

def DescCompat (L : LB X) (φ : ∀ i j, Γ(pullback f f, chart f L i j)ˣ) : Prop :=
  ∀ (z : ↥(pullback f f)) (i i' j j' : L.ι), pullback.fst f f z ∈ L.U i → pullback.fst f f z ∈ L.U i' →
    pullback.snd f f z ∈ L.U j → pullback.snd f f z ∈ L.U j' →
    gm (𝟙 _) z _ (φ i' j') =
      gm (pullback.fst f f) z _ (L.g i i') * gm (𝟙 _) z _ (φ i j) * gm (pullback.snd f f) z _ (L.g j' j)

def DescCocycle (L : LB X) (φ : ∀ i j, Γ(pullback f f, chart f L i j)ˣ) : Prop :=
  ∀ (w : ↥(Triple f)) (i j k : L.ι), pullback.fst f f (pullback.fst (pullback.snd f f) (pullback.fst f f) w) ∈ L.U i →
    pullback.snd f f (pullback.fst (pullback.snd f f) (pullback.fst f f) w) ∈ L.U j → pullback.snd f f (pullback.snd (pullback.snd f f) (pullback.fst f f) w) ∈ L.U k →
    gm (pullback.fst (pullback.snd f f) (pullback.fst f f)) w _ (φ i j) *
      gm (pullback.snd (pullback.snd f f) (pullback.fst f f)) w _ (φ j k) = gm (pr13 f) w _ (φ i k)

end GlobalTheory.LBDescent
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Mum

def FrameAlong {X Y : Scheme.{0}} (L : LB X) (x : Y ⟶ X) (W : Y.Opens) (τ : ∀ k, Γ(Y, W ⊓ x ⁻¹ᵁ L.U k)ˣ) : Prop :=
  ∀ (z : Y) (k k' : L.ι), z ∈ W → x z ∈ L.U k → x z ∈ L.U k' →
    gm (𝟙 Y) z (W ⊓ x ⁻¹ᵁ L.U k) (τ k) =
      gm x z (L.U k ⊓ L.U k') (L.g k k') * gm (𝟙 Y) z (W ⊓ x ⁻¹ᵁ L.U k') (τ k')

def FrameCarriedAlong {X Y : Scheme.{0}} (L : LB X) (x : Y ⟶ X) (W : Y.Opens) (τ : ∀ k, Γ(Y, W ⊓ x ⁻¹ᵁ L.U k)ˣ)
    (f : X ⟶ X) (w : LB.Iso L (L.pull f)) (h : Y ⟶ Y) : Prop :=
  ∀ (z : Y) (j k : L.ι), z ∈ W → h z ∈ W → x z ∈ L.U k → x (h z) ∈ L.U j →
    gm h z (W ⊓ x ⁻¹ᵁ L.U j) (τ j) = gw w x z j k * gm (𝟙 Y) z (W ⊓ x ⁻¹ᵁ L.U k) (τ k)

end GlobalTheory.Mum
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Mum

def SecCarried {X : Scheme.{0}} (L : LB X) (θ : L.Sec) (f : X ⟶ X) (w : LB.Iso L (L.pull f)) : Prop :=
  ∀ (z : X) (j k : L.ι) (hk : z ∈ L.U k) (hj : f z ∈ L.U j),
    (X.presheaf.germ (f ⁻¹ᵁ L.U j) z hj).hom ((f.app (L.U j)).hom (θ.f j)) =
      (gw w (𝟙 X) z j k).val * (X.presheaf.germ (L.U k) z hk).hom (θ.f k)

end GlobalTheory.Mum
end
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.ChartGraph

theorem _root_.GlobalTheory.T.majorant_eq_of_firstColumns_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x' y : Frame X.Ψ r)
    (τ : X.Ψ) (C : Matrix (Fin X.p0) (Fin X.p0) ℂ), C.det ≠ 0 → (X.gramPos y τ).det ≠ 0 →
    (∀ a : Fin X.p0, col (mat x' τ) (Fin.castLE X.p0_le a) =
      ∑ c : Fin X.p0, C c a • col (mat y τ) (Fin.castLE X.p0_le c)) →
    ∀ v : Fin r → ℂ, X.maj x' τ v = X.maj y τ v := by
  first | exact @GlobalTheory.MajCols.maj_eq_of_cols | exact GlobalTheory.MajCols.maj_eq_of_cols | (intros; apply GlobalTheory.MajCols.maj_eq_of_cols <;> assumption)
end
