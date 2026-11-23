module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle061
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle029
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTrivialisationsCorrespond
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle003
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.LN GlobalTheory
open scoped CategoryTheory.Obj

set_option autoImplicit false

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RigSymBaseChange

theorem rigidified_and_sym_pull : ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (G : Over S) [GrpObj G] (B : Over S') [GrpObj B] (β : B.left ⟶ G.left), IsGrpPullback B G f β → ∀ (L : RigLB G) (σ : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(GrpObj.inv : G ⟶ G).left, 𝟙 G.left] ![1, -1])), σ.IsGen → Rigidified B (L.L.pull β) ∧ Out.Sym B (L.L.pull β) := by
  intro S S' f G _ B _ β gp L σ hσ
  refine ⟨PolBaseChange.rigidified_pull gp ⟨L.rig, L.rigGen⟩, fun _ => ⟨⊤, trivial, ?_⟩⟩
  refine gen_chartPull (chartPullLinComb L.L β (K := Fin 2) _
    ![(GrpObj.inv : G ⟶ G).left, 𝟙 G.left] ![1, -1] ((B.hom ⁻¹ᵁ ⊤).ι ≫ β) fun k => ?_) σ hσ
  fin_cases k
  · show ((B.hom ⁻¹ᵁ ⊤).ι ≫ (GrpObj.inv : B ⟶ B).left) ≫ β = ((B.hom ⁻¹ᵁ ⊤).ι ≫ β) ≫ (GrpObj.inv : G ⟶ G).left
    rw [Category.assoc, PolBaseChange.inv_comm gp, Category.assoc]
  · show (B.hom ⁻¹ᵁ ⊤).ι ≫ β = ((B.hom ⁻¹ᵁ ⊤).ι ≫ β) ≫ 𝟙 G.left
    rw [Category.comp_id]

end GlobalTheory.RigSymBaseChange
end
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.LN GlobalTheory
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.SiegLoc.TraitOrd

section Specialise

variable {o : Type} [CommRing o] {ζ : o} {g n : ℕ} {F : SFam g n ζ} {S : Scheme.{0}} {j : F.X ⟶ S} [IsOpenImmersion j]
  {G : Over S} [GrpObj G] {e : F.univ.A.left ⟶ G.left}

theorem isSemiAbelian_of_isGrpPullback {T : Scheme.{0}} {f : T ⟶ S} {G' : Over T} [GrpObj G'] [IsCommMonObj G']
    {π : G'.left ⟶ G.left} (h : IsGrpPullback G' G f π) (hG : IsSemiAbelian G) : IsSemiAbelian G' := by
  obtain ⟨bc, mbc, -⟩ := grpPullback_iso h (isGrpPullback_pullback G f)
  exact isSemiAbelian_of_grpIso bc (IsSemiAbelian.pullback f G hG)

end Specialise

theorem eq_of_associated_pow {V : Type} [CommRing V] [IsDomain V] {ϖ : V} (hϖ : Irreducible ϖ) {a b : ℕ}
    (h : Associated (ϖ ^ a) (ϖ ^ b)) : a = b :=
  le_antisymm ((pow_dvd_pow_iff hϖ.ne_zero hϖ.not_isUnit).1 h.dvd) ((pow_dvd_pow_iff hϖ.ne_zero hϖ.not_isUnit).1 h.symm.dvd)


end GlobalTheory.SiegLoc.TraitOrd
end
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.LN GlobalTheory
open scoped CategoryTheory.Obj

noncomputable section

open MonoidalCategory CartesianMonoidalCategory MonObj

namespace GlobalTheory.UnifLamFibre

open GlobalTheory.CechPic

theorem isSquare_unique {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} {φ : G'.left ⟶ G.left}
    {a b : (G' ⊗ G').left ⟶ (G ⊗ G).left} (ha : IsSquare φ a) (hb : IsSquare φ b) : a = b :=
  (IsPullback.of_hasPullback G.hom G.hom).hom_ext (ha.1.trans hb.1.symm) (ha.2.trans hb.2.symm)


end GlobalTheory.UnifLamFibre
end
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.LN GlobalTheory
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PsiCompare

open ReciprocityTheory.ChartRestriction.G.DVR

theorem prod_famB_wtTwo {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) {T : Over (Spec (CommRingCat.of R))}
    (y : T ⟶ D.P.A) (α : D.X) {U : Type} [CommGroup U] (h : (T.left ⟶ D.P.A.left) → U) :
    ∏ i, h (y.left ≫ D.famφB α i) ^ DegPre.famε 2 i =
      h y.left * h (y * cP D T α).left * (h (cP D T α).left)⁻¹ * h (1 : T ⟶ D.P.A).left := by
  have a₀ : y.left ≫ D.famφB α 0 = y.left := Category.comp_id _
  have a₁ : y.left ≫ D.famφB α 1 = (y * cP D T α).left := congrArg (fun z => z.left)
    ((MonObj.comp_mul y (𝟙 _) (cP D _ α)).trans (congrArg₂ (· * ·) (Category.comp_id _) (comp_cP D _ α)))
  have a₂ : y.left ≫ D.famφB α 2 = (cP D T α).left := congrArg (fun z => z.left) (comp_cP D y α)
  have a₃ : y.left ≫ D.famφB α 3 = (1 : T ⟶ D.P.A).left :=
    congrArg (fun z : _ ⟶ D.P.A => z.left) (MonObj.comp_one (M := D.P.A) y)
  rw [Fin.prod_univ_four, a₀, a₁, a₂, a₃]
  show _ ^ (((2 : ℕ) : ℤ) - 1) * _ ^ (1 : ℤ) * _ ^ (-1 : ℤ) * _ ^ (1 : ℤ) = _
  norm_num

theorem sq_unit_cancel {A : Type} [CommRing A] [IsDomain A] {s s' F₁ F₁' : A}
    {θ θ' V V' ωx ωam ωm2 ω1 ωa ωm : Aˣ} (hs : s ≠ 0)
    (h₁ : F₁ = s * (θ * V).val) (h₂ : F₁' = s' * (θ' * V').val)
    (h₃ : F₁ ^ 2 = (ωx * ωam * ωm2⁻¹ * ω1).val * F₁' ^ 2)
    (h₄ : s ^ 2 = (ωa * ωa * ω1⁻¹ * ω1).val * s' ^ 2)
    (h₅ : θ ^ 2 = ωam * ωm2⁻¹ * ωa⁻¹ * ωa⁻¹ * ωm * ωm * ωx * ω1⁻¹ * θ' ^ 2) :
    V' ^ 2 = (ωm * ω1⁻¹) ^ 2 * V ^ 2 := by
  have hs' : s' ≠ 0 := by
    rintro rfl
    rw [zero_pow two_ne_zero, MulZeroClass.mul_zero] at h₄
    exact hs (pow_eq_zero_iff two_ne_zero |>.1 h₄)
  have E : ωa * ωa * ω1⁻¹ * ω1 * (θ * V) ^ 2 = ωx * ωam * ωm2⁻¹ * ω1 * (θ' * V') ^ 2 :=
    Units.ext (mul_left_cancel₀ (pow_ne_zero 2 hs') (by
      rw [h₁, h₂] at h₃
      simp only [Units.val_mul, Units.val_pow_eq_pow_val] at h₃ h₄ ⊢
      linear_combination h₃ - ((θ : A) * V) ^ 2 * h₄))
  apply Additive.ofMul.injective
  have E' := congrArg Additive.ofMul E
  have h₅' := congrArg Additive.ofMul h₅
  simp only [ofMul_mul, ofMul_inv, ofMul_pow] at E' h₅' ⊢
  linear_combination (norm := abel) h₅' - E'

end GlobalTheory.PsiCompare


open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.PsiCompare in
theorem GlobalTheory.PsiCompare.famMult_sq_corr : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], ∀ (D D' : DegData R (maximalIdeal R)), ∀ (Φ : D'.toPre.P.A ≅ D.toPre.P.A) (w : LB.Iso (LB.LinComb D'.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D'.toPre.P.A.left) (fun _ => 2)) ((LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left) (fun _ => 2)).pull Φ.hom.left)), IsMonHom Φ.hom → ∀ xe : D'.toPre.X ≃+ D.toPre.X, (∀ x : D'.toPre.X, D'.toPre.c (2 • x) ≫ Φ.hom = D.toPre.c (xe (2 • x))) → ∀ (f : ∀ α : D.toPre.X, D.toPre.SecB 2 α) (f' : ∀ α : D'.toPre.X, D'.toPre.SecB 2 α), (∀ (mu α : D.toPre.X) (T : Over (Sp R)) (κ : T ⟶ TF (R := R) (FractionRing R)) (y : T ⟶ D.toPre.P.A) (z : T.left) (J : (T.left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → sval (f (α + 2 • mu)) y.left z J = sval (f α) (y * ReciprocityTheory.ChartRestriction.G.DVR.cP D.toPre T mu).left z J * (ReciprocityTheory.ChartRestriction.G.DVR.uVal D.toPre (FractionRing R) 2 α (ReciprocityTheory.ChartRestriction.G.DVR.cP D.toPre _ mu) (CartesianMonoidalCategory.lift κ y) z J * val (DegPre.famMult D.toPre (FractionRing R) 2 mu α) κ.left z J).val) → (∀ (mu α : D'.toPre.X) (T : Over (Sp R)) (κ : T ⟶ TF (R := R) (FractionRing R)) (y : T ⟶ D'.toPre.P.A) (z : T.left) (J : (T.left ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Geo.Tor.Good D'.toPre.P.L z J → sval (f' (α + 2 • mu)) y.left z J = sval (f' α) (y * ReciprocityTheory.ChartRestriction.G.DVR.cP D'.toPre T mu).left z J * (ReciprocityTheory.ChartRestriction.G.DVR.uVal D'.toPre (FractionRing R) 2 α (ReciprocityTheory.ChartRestriction.G.DVR.cP D'.toPre _ mu) (CartesianMonoidalCategory.lift κ y) z J * val (DegPre.famMult D'.toPre (FractionRing R) 2 mu α) κ.left z J).val) → (∀ (β : D'.toPre.X) (Z : Scheme.{0}) (ρ : Z ⟶ D'.toPre.P.A.left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D'.toPre.P.L z J' → sval (f (xe (2 • β))) (ρ ≫ Φ.hom.left) z J ^ 2 = (∏ κ, ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) (ρ ≫ D'.toPre.famφB (2 • β) κ) ^ DegPre.famε 2 κ).val * sval (f' (2 • β)) ρ z J' ^ 2) → (∀ (T : Over (Sp R)) (z : T.left) (J : (T.left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (T.left ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D'.toPre.P.L z J' → ∀ (Ω : (T ⟶ D'.toPre.P.A) → (T.left.presheaf.stalk z)ˣ), Ω = (fun x => ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) x.left) → ∀ (a b c : T ⟶ D'.toPre.P.A), cubV D.toPre.cub z J (a ≫ Φ.hom) (b ≫ Φ.hom) (c ≫ Φ.hom) ^ 2 = Ω (a * b * c) * (Ω (a * b))⁻¹ * (Ω (a * c))⁻¹ * (Ω (b * c))⁻¹ * Ω a * Ω b * Ω c * (Ω 1)⁻¹ * cubV D'.toPre.cub z J' a b c ^ 2) → ∀ (y : D'.toPre.X) (z : (DegPre.BF D.toPre (FractionRing R)).left) (J : ((DegPre.BF D.toPre (FractionRing R)).left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : ((DegPre.BF D.toPre (FractionRing R)).left ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D'.toPre.P.L z J' → IsDomain ((DegPre.BF D.toPre (FractionRing R)).left.presheaf.stalk z) → sval (f 0) (DegPre.prB D.toPre (FractionRing R)).left z J ≠ 0 → val (DegPre.famMult D'.toPre (FractionRing R) 2 (2 • y) 0) (fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left z J' ^ 2 = (ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) (ReciprocityTheory.ChartRestriction.G.DVR.cP D'.toPre (DegPre.BF D.toPre (FractionRing R)) (2 • y)).left * (ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) (1 : (DegPre.BF D.toPre (FractionRing R)) ⟶ D'.toPre.P.A).left)⁻¹) ^ 2 * val (DegPre.famMult D.toPre (FractionRing R) 2 (xe (2 • y)) 0) (fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left z J ^ 2 := by
  intro R _ _ _ D D' Φ w hΦ xe hc f f' hf hf' hcorr hcub y z J J' hJ hJ' hdom h0
  haveI := hΦ
  haveI := hdom
  set κ : DegPre.BF D.toPre (FractionRing R) ⟶ TF (R := R) (FractionRing R) := fst (TF (R := R) (FractionRing R)) D.toPre.P.A with hκ
  set pB : DegPre.BF D.toPre (FractionRing R) ⟶ D.toPre.P.A := DegPre.prB D.toPre (FractionRing R) with hpB
  set m' : DegPre.BF D.toPre (FractionRing R) ⟶ D'.toPre.P.A := cP D'.toPre (DegPre.BF D.toPre (FractionRing R)) (2 • y) with hm'
  set a : DegPre.BF D.toPre (FractionRing R) ⟶ D'.toPre.P.A := pB ≫ Φ.inv with ha
  set x' : DegPre.BF D.toPre (FractionRing R) ⟶ D'.toPre.P.A := a * m'⁻¹ with hx'
  let T := DegPre.BF D.toPre (FractionRing R)
  have hxm : x' * m' = a := inv_mul_cancel_right _ _
  have hmΦ : m' ≫ Φ.hom = cP D.toPre T (xe (2 • y)) := cP_comp Φ.hom (hc y) T
  have haΦ : a ≫ Φ.hom = pB := by rw [ha, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hx'Φ : (x' ≫ Φ.hom) * cP D.toPre T (xe (2 • y)) = pB := by
    rw [← hmΦ, ← MonObj.mul_comp, hxm, haΦ]

  have e₁ := hf (xe (2 • y)) 0 T κ (x' ≫ Φ.hom) z J hJ
  have u₁ : uVal D.toPre (FractionRing R) 2 0 (cP D.toPre _ (xe (2 • y))) (lift κ (x' ≫ Φ.hom)) z J =
      cubV D.toPre.cub z J (cP D.toPre T (xe (2 • y))) (cP D.toPre T (xe (2 • y))) (x' ≫ Φ.hom) := by
    have C := isCub_cubV D.toPre.cub hJ
    have ρ₂ : lift κ (x' ≫ Φ.hom) ≫ DegPre.prB D.toPre (FractionRing R) = x' ≫ Φ.hom := lift_snd _ _
    rw [uVal, cPoint_zero, cubN, ρ₂, comp_cP, comp_cP]
    simp only [Finset.prod_range_succ, Finset.prod_range_zero, pow_zero, pow_one, _root_.one_mul,
      _root_.mul_one, C.face, inv_one]
    rfl
  rw [u₁, hx'Φ, zero_add] at e₁

  have e₂ := hf' (2 • y) 0 T κ x' z J' hJ'
  have u₂ : uVal D'.toPre (FractionRing R) 2 0 (cP D'.toPre _ (2 • y)) (lift κ x') z J' =
      cubV D'.toPre.cub z J' m' m' x' := by
    have C := isCub_cubV D'.toPre.cub hJ'
    have ρ₂ : lift κ x' ≫ DegPre.prB D'.toPre (FractionRing R) = x' := lift_snd _ _
    rw [uVal, cPoint_zero, cubN, ρ₂, comp_cP, comp_cP]
    simp only [Finset.prod_range_succ, Finset.prod_range_zero, pow_zero, pow_one, _root_.one_mul,
      _root_.mul_one, C.face, inv_one]
    rfl
  rw [u₂, hxm, zero_add] at e₂

  have e₃ := hcorr (2 • y) T.left x'.left z J J' hJ hJ'
  have p₄ : x' * m' ^ 2 = a * m' := by rw [pow_two, ← _root_.mul_assoc, hxm]
  rw [prod_famB_wtTwo, cPoint_nsmul, ← hm', p₄, map_nsmul] at e₃

  have e₄ := hcorr 0 T.left a.left z J J' hJ hJ'
  rw [prod_famB_wtTwo, smul_zero, map_zero, cPoint_zero, _root_.mul_one,
    show a.left ≫ Φ.hom.left = pB.left from congrArg (fun q => q.left) haΦ] at e₄

  have e₅ := hcub T z J J' hJ hJ' _ rfl m' m' x'
  have p₁ : m' * m' * x' = a * m' := by rw [mul_comm (m' * m') x', ← _root_.mul_assoc, hxm]
  have p₃ : m' * x' = a := by rw [mul_comm, hxm]
  rw [hmΦ, p₁, p₃, ← sq] at e₅
  exact sq_unit_cancel h0 e₁ e₂ e₃ e₄ e₅
end
end
