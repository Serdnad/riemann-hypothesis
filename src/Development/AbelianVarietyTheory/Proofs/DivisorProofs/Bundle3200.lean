module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantToUnitLeft
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle028
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsGenVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsAffineHomOfFlatQuotientOfAffineKernel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2984
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3141
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3139
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.GtPtsVal
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2339
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3104
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle020
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle070
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle077
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle001
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.UT GlobalTheory.FieldBaseChange
open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.Poinc.Sep.Frames GlobalTheory.UT.CoefBasic

namespace GlobalTheory.Poinc.Sep.CubInt

theorem cubProd_of_generic : ∀ (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (N : ℕ) (b cχ : 𝟙_ (Over (Sp V)) ⟶ D.P.A),
    b ^ N = 1 → ∀ (χt : LB.Gen (LB.LinComb D.P.L ![(cχ * b).left, cχ.left, b.left, (η[D.P.A]).left] DegPre.gtε)),
    χt.IsGen →
    (∀ z J, Good D.P.L z J → ∏ i ∈ Finset.range N, cubV D.cub z J (toUnit (TF (R := V) (FractionRing V)) ≫ cχ)
        (toUnit (TF (R := V) (FractionRing V)) ≫ b ^ i) (toUnit (TF (R := V) (FractionRing V)) ≫ b) =
      val χt (toUnit (TF (R := V) (FractionRing V))).left z J ^ N) →
    ∀ (T : Over (Sp V)) (z : T.left) J, Good D.P.L z J →
      ∏ i ∈ Finset.range N, cubV D.cub z J (toUnit T ≫ cχ) (toUnit T ≫ b ^ i) (toUnit T ≫ b) = val χt T.hom z J ^ N := by
  intro V _ _ D N b cχ hbN χt ht hgen T z J hJ
  have G := (grep_cubProd cχ b N).mul ((SymFrame.grep_gen χt ht (𝟙 _)).pow N).inv
  obtain ⟨s, hs, vs⟩ := G.out D.P.isLB (K := PEmpty) PEmpty.elim PEmpty.elim
    (fun U _ h => Eq.trans (by
      have hK : ∏ k : Fin 4, h (𝟙 _ ≫ ![(cχ * b).left, cχ.left, b.left, (η[D.P.A]).left] k) ^ DegPre.gtε k =
          (h (cχ * b).left)⁻¹ * h cχ.left * h b.left *
            (h (1 : 𝟙_ (Over (Spec (CommRingCat.of V))) ⟶ D.P.A).left)⁻¹ := by
        rw [Fin.prod_univ_four, ← SymFrame.eta_eq]
        simp [DegPre.gtε, zpow_neg, zpow_one]
      have hP : ∀ i, h (cχ * b ^ i * b).left * (h (cχ * b ^ i).left)⁻¹ * (h (cχ * b).left)⁻¹ *
          (h (b ^ i * b).left)⁻¹ * h cχ.left * h (b ^ i).left * h b.left *
          (h (1 : 𝟙_ (Over (Spec (CommRingCat.of V))) ⟶ D.P.A).left)⁻¹ =
          (h (cχ * b ^ (i + 1)).left / h (b ^ (i + 1)).left) / (h (cχ * b ^ i).left / h (b ^ i).left) *
            ((h (cχ * b).left)⁻¹ * h cχ.left * h b.left *
              (h (1 : 𝟙_ (Over (Spec (CommRingCat.of V))) ⟶ D.P.A).left)⁻¹) := by
        intro i
        rw [_root_.mul_assoc cχ, ← pow_succ]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv, ofMul_div]
        abel
      rw [Finset.prod_congr rfl (fun i _ => hP i), Finset.prod_mul_distrib,
        Finset.prod_range_div (fun i => h (cχ * b ^ i).left / h (b ^ i).left), Finset.prod_const, Finset.card_range, hK,
        hbN, pow_zero]
      simp) (Fintype.prod_empty _).symm)
  obtain ⟨ρ, hρ⟩ := exists_ratio D.P.isLB rfl s (LB.oneGen D.P.L) hs (oneGen_gen _)
  have hρ1 : ρ = 1 := by
    obtain ⟨z₀⟩ := exists_pt (R := V) (F := FractionRing V)
    obtain ⟨J₀, hJ₀⟩ := exists_good' D.P.isLB z₀
    have a := vs _ (toUnit (TF (R := V) (FractionRing V))) z₀ J₀ hJ₀
    rw [hρ _ _ z₀ J₀ hJ₀, val_one, _root_.mul_one] at a
    simp only [Category.comp_id] at a
    have a1 : gm (toUnit (TF (R := V) (FractionRing V))).left z₀ ⊤ ρ = 1 := by
      rw [a]
      exact mul_inv_eq_one.mpr (hgen z₀ J₀ hJ₀)
    have c := gm_top_eq ρ z₀
    rw [a1, Units.val_one, cst_eq, ← map_one (cstH z₀)] at c
    have d := cstH_inj z₀ c
    rw [← map_one (algebraMap V (FractionRing V))] at d
    have e := IsFractionRing.injective V (FractionRing V) d
    apply Units.ext
    have hinj : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom :=
      (Scheme.ΓSpecIso (CommRingCat.of V)).commRingCatIsoToRingEquiv.injective
    apply hinj
    rw [Units.val_one, map_one]
    exact e.symm
  have a := vs T (toUnit T) z J hJ
  rw [hρ _ _ z J hJ, val_one, _root_.mul_one, hρ1, map_one] at a
  simp only [Category.comp_id] at a
  exact mul_inv_eq_one.mp a.symm

end GlobalTheory.Poinc.Sep.CubInt
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.TorsLiftRoot

open ReciprocityTheory.ChartRestriction.G.DVR

section Alg

variable {A U : Type} [CommGroup A] [CommGroup U] {θ : A → A → A → U} (h : IsCub θ)
include h

theorem cubN_succ' (k : ℕ) (a m x : A) : cubN θ (k + 1) a m x = cubN θ k a m x * θ (a * m ^ k) m x :=
  Finset.prod_range_succ _ _

theorem ex_pow (c x : A) (w : U) (k : ℕ) :
    (⟨x, w⟩ : Ex h c) ^ k = ⟨x ^ k, w ^ k * (cubN θ k 1 x c)⁻¹⟩ := by
  induction k with
  | zero => exact Ex.ext (pow_zero x).symm (by simp [cubN]; rfl)
  | succ k ih =>
    rw [pow_succ, ih]
    refine Ex.ext (pow_succ x k).symm ?_
    rw [Ex.mul_u, cubN_succ' h]
    show _ = _ * (_ * θ (1 * x ^ k) x c)⁻¹
    rw [_root_.one_mul, h.s01 c, h.s12 (x ^ k) c x, pow_succ]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel

theorem cubN_pow (a x : A) (n k : ℕ) :
    cubN θ n 1 a (x ^ k) * cubN θ k 1 x a ^ n = cubN θ n 1 a x ^ k * cubN θ k 1 x (a ^ n) := by
  induction k with
  | zero => rw [pow_zero, pow_zero, h.N_one]; simp [cubN]
  | succ k ih =>
    have e := h.N_add n 1 a (x ^ k) x
    rw [h.face, _root_.mul_one, _root_.one_mul] at e
    rw [cubN_succ' h, cubN_succ' h, _root_.one_mul, pow_succ x k, h.s12 (x ^ k) x a, h.s01 (x ^ k) a x,
      h.s12 (x ^ k) x (a ^ n), h.s01 (x ^ k) (a ^ n) x]
    apply Additive.ofMul.injective
    have e' := congrArg Additive.ofMul e
    have ih' := congrArg Additive.ofMul ih
    simp only [ofMul_mul, ofMul_inv, ofMul_pow] at e' ih' ⊢
    simp only [add_nsmul, one_nsmul, nsmul_add]
    linear_combination (norm := abel) e' + ih'

end Alg

section Key

variable {A U X : Type} [CommGroup A] [CommGroup U] [AddCommGroup X] [Module.Free ℤ X] {θ : A → A → A → U}
  (h : IsCub θ)
include h

theorem exists_mult_pow_eq_one {c : X → A} (hc : ∀ χ χ', c (χ + χ') = c χ * c χ') {n : ℕ} (c' : X → A)
    (hc' : ∀ χ, c' χ ^ n = c χ) {b : A} (hb : b ^ n = 1) :
    ∃ v, Mult θ c b v ∧ ∀ χ, ((⟨b, v χ⟩ : Ex h (c χ)) ^ n).u = 1 := by
  let e := Module.Free.chooseBasis ℤ X
  let f : X →ₗ[ℤ] Additive (Ex h b) := e.constr ℤ fun i => Additive.ofMul ⟨c' (e i), 1⟩
  let p : Additive (Ex h b) →+ Additive A := AddMonoidHom.mk' (fun x => Additive.ofMul x.toMul.b) fun _ _ => rfl
  have fb : ∀ χ, (f χ).toMul.b ^ n = c χ := fun χ => by
    have := LinearMap.congr_fun (e.ext (f₁ := n • (p.toIntLinearMap ∘ₗ f))
      (f₂ := (AddMonoidHom.mk' (fun χ => Additive.ofMul (c χ)) hc).toIntLinearMap) fun i => by
        show n • p (f (e i)) = Additive.ofMul (c (e i))
        rw [show f (e i) = Additive.ofMul ⟨c' (e i), 1⟩ from e.constr_basis ℤ _ i, ← hc', ofMul_pow]; rfl) χ
    exact Additive.ofMul.injective (by rw [ofMul_pow]; exact this)
  have fadd : ∀ χ χ', (f (χ + χ')).toMul = (f χ).toMul * (f χ').toMul := fun χ χ' => by rw [map_add (f := _)]; rfl
  let g : X → Ex h b := fun χ => (f χ).toMul ^ n
  have gadd : ∀ χ χ', g (χ + χ') = g χ * g χ' := fun χ χ' => by simp only [g, fadd, mul_pow]
  have gb : ∀ χ, (g χ).b = c χ := fun χ => (Ex.pow_b _ _).trans (fb χ)
  have m : Mult θ c b fun χ => (g χ).u := by
    refine ⟨?_, fun χ χ' => ?_⟩
    · show ((f 0).toMul ^ n).u = 1
      rw [map_zero, toMul_zero, one_pow]; rfl
    · show (g (χ + χ')).u * _ = _
      rw [gadd, Ex.mul_u, gb, gb, h.s01 b, h.s12 (c χ) b, inv_mul_cancel_right]
  have mp := m.pow (h := h) hc n
  have wadd : ∀ χ χ', ((⟨b, (g (χ + χ')).u⟩ : Ex h (c (χ + χ'))) ^ n).u =
      ((⟨b, (g χ).u⟩ : Ex h (c χ)) ^ n).u * ((⟨b, (g χ').u⟩ : Ex h (c χ')) ^ n).u := fun χ χ' => by
    have := mp.2 χ χ'
    rwa [hb, h.face₃, _root_.mul_one] at this
  have wroot : ∀ χ, ∃ r : U, r ^ n = ((⟨b, (g χ).u⟩ : Ex h (c χ)) ^ n).u := fun χ => by
    refine ⟨(f χ).toMul.u ^ n * (cubN θ n 1 b (f χ).toMul.b)⁻¹, ?_⟩
    have e₁ : (g χ).u = (f χ).toMul.u ^ n * (cubN θ n 1 (f χ).toMul.b b)⁻¹ := by
      show ((f χ).toMul ^ n).u = _
      rw [show (f χ).toMul = ⟨(f χ).toMul.b, (f χ).toMul.u⟩ from rfl, ex_pow h]
    rw [ex_pow h, ← fb χ]
    show _ = (g χ).u ^ n * (cubN θ n 1 b ((f χ).toMul.b ^ n))⁻¹
    have e₂ := cubN_pow h (f χ).toMul.b b n n
    rw [hb, h.N_one, _root_.one_mul] at e₂
    rw [e₁]
    apply Additive.ofMul.injective
    have e₂' := congrArg Additive.ofMul e₂
    simp only [ofMul_mul, ofMul_inv, ofMul_pow, nsmul_add, nsmul_neg] at e₂' ⊢
    rw [smul_neg, smul_neg, e₂']
    abel
  choose r hr using wroot
  let W : X →ₗ[ℤ] Additive U := (AddMonoidHom.mk' (fun χ => Additive.ofMul ((⟨b, (g χ).u⟩ : Ex h (c χ)) ^ n).u)
    wadd).toIntLinearMap
  let ro : X →ₗ[ℤ] Additive U := e.constr ℤ fun i => Additive.ofMul (r (e i))⁻¹
  have roW : ∀ χ, (ro χ).toMul ^ n * ((⟨b, (g χ).u⟩ : Ex h (c χ)) ^ n).u = 1 := fun χ => by
    have := LinearMap.congr_fun (e.ext (f₁ := n • ro) (f₂ := -W) fun i => by
      show n • ro (e i) = -W (e i)
      rw [show ro (e i) = Additive.ofMul (r (e i))⁻¹ from e.constr_basis ℤ _ i, ← ofMul_pow, inv_pow, hr]; rfl) χ
    apply Additive.ofMul.injective
    rw [ofMul_mul, ofMul_pow, ofMul_one]
    exact eq_neg_iff_add_eq_zero.1 this
  have roadd : ∀ χ χ', (ro (χ + χ')).toMul = (ro χ).toMul * (ro χ').toMul := fun χ χ' => by rw [map_add (f := _)]; rfl
  refine ⟨fun χ => (g χ).u * (ro χ).toMul, ⟨?_, fun χ χ' => ?_⟩, fun χ => ?_⟩
  · show (g 0).u * (ro 0).toMul = 1
    rw [show (g 0).u = 1 from m.1, map_zero, toMul_zero, _root_.mul_one]
  · show (g (χ + χ')).u * (ro (χ + χ')).toMul * _ = (g χ).u * (ro χ).toMul * ((g χ').u * (ro χ').toMul)
    rw [roadd, mul_right_comm, m.2, _root_.mul_mul_mul_comm]
  · rw [ex_pow h, ← roW χ, ex_pow h, mul_pow]
    show (g χ).u ^ n * (ro χ).toMul ^ n * _ = (ro χ).toMul ^ n * ((g χ).u ^ n * _)
    rw [mul_comm ((g χ).u ^ n), _root_.mul_assoc]

end Key

section Main

theorem exists_qk_zero_of_pow_eq : ∀ {R : Type} [CommRing R] [IsDomain R] (D : DegPre R), D.TauBimult → ∀ (n : ℕ), 1 ≤ n →
    ∀ (c' : D.X → (𝟙_ (Over (Sp R)) ⟶ D.P.A)), (∀ χ, c' χ ^ n = D.c χ) →
    ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (b : TF (R := R) F ⟶ D.P.A), b ^ n = 1 →
    ∃ p : QkPt D F n, p.y = 0 ∧ p.g.b = b := by
  intro R _ _ D hB n _ c' hc' F _ _ b hb
  obtain ⟨J, hJ⟩ := good_pt D.P.isLB (default : PrimeSpectrum F)
  have C := isCub_cubV D.cub (T := TF (R := R) F) hJ
  have cpw : ∀ (x : 𝟙_ (Over (Sp R)) ⟶ D.P.A) (k : ℕ), toUnit (TF (R := R) F) ≫ x ^ k = (toUnit _ ≫ x) ^ k :=
    fun x k => by
      induction k with
      | zero => rw [pow_zero, pow_zero]; exact MonObj.comp_one _
      | succ k ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih]
  have cpow : ∀ χ, (toUnit (TF (R := R) F) ≫ c' χ) ^ n = cP D (TF (R := R) F) χ := fun χ => by
    rw [← cpw, hc']; rfl
  obtain ⟨v, m, hv⟩ := exists_mult_pow_eq_one C (cPoint_add D (TF (R := R) F)) (fun χ => toUnit _ ≫ c' χ) cpow hb
  have i0 : ∀ χ, ix (𝟙 _) hJ (0 : D.X) χ = 1 := fun χ => by
    have := ix_add (𝟙 (TF (R := R) F)) hJ hB 0 0 χ
    rw [add_zero] at this
    exact mul_eq_left.1 this.symm
  obtain ⟨q, h₁, h₂, -⟩ := exists_qk hJ (n := n) 0 b v m fun χ => by
    rw [i0]; exact Ex.ext ((Ex.pow_b _ _).trans hb) (hv χ)
  exact ⟨q, h₁, h₂⟩

end Main

end GlobalTheory.TorsLiftRoot
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_isAffineOpen_of_preimage_le_affine : ∀ (R R₁ : Type) [CommRing R] [CommRing R₁] [Algebra R R₁]
    [Module.Finite R R₁] [Module.Free R R₁] [Nontrivial R₁] [IsLocalRing R] (X X₁ : Scheme.{0})
    (p : X ⟶ Sp R) (p₁ : X₁ ⟶ Sp R₁) (b : X₁ ⟶ X), IsPullback b p₁ p (spMap (algebraMap R R₁)) →
    IsSeparated p → QuasiCompact p → ∀ (W : X₁.Opens), IsAffineOpen W → ∀ s : Finset X,
    (∀ z : X₁, b z ∈ s → z ∈ W) → ∃ O : X.Opens, IsAffineOpen O ∧ ∀ x ∈ s, x ∈ O := by
  intro R R₁ _ _ _ _ _ _ _ X X₁ p p₁ b H _ _ W hW s hs
  classical

  have hg : IsFinite (spMap (algebraMap R R₁)) := by
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.2 inferInstance
  have hff : Flat (spMap (algebraMap R R₁)) ∧ Surjective (spMap (algebraMap R R₁)) := by
    rw [flat_and_surjective_SpecMap_iff]
    exact RingHom.faithfullyFlat_algebraMap_iff.2 inferInstance
  have : Flat (spMap (algebraMap R R₁)) := hff.1
  have : Surjective (spMap (algebraMap R R₁)) := hff.2
  have : IsFinite b := MorphismProperty.of_isPullback H.flip hg
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated p

  let O' : X.Opens := ⟨(b '' (W : Set X₁)ᶜ)ᶜ, (b.isClosedMap _ W.isOpen.isClosed_compl).isOpen_compl⟩
  have hsO' : ∀ x ∈ s, x ∈ O' := by
    rintro x hx ⟨z, hz, rfl⟩
    exact hz (hs z hx)
  have key : ∀ x ∈ s, ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧ U ≤ O' := by
    intro x hx
    obtain ⟨U, hU, hxU, hUO⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens) (hsO' x hx)
    exact ⟨U, hU, hxU, hUO⟩
  choose U hU hxU hUO using key
  let V : X.Opens := ⨆ x : s, U x.1 x.2
  have hVO : V ≤ O' := iSup_le fun x => hUO x.1 x.2
  have hsV : ∀ x ∈ s, x ∈ V := fun x hx => TopologicalSpace.Opens.mem_iSup.2 ⟨⟨x, hx⟩, hxU x hx⟩
  have hVc : IsCompact (V : Set X) := by
    rw [TopologicalSpace.Opens.coe_iSup]
    exact isCompact_iUnion fun x => (hU x.1 x.2).isCompact
  have hVq : IsQuasiSeparated (V : Set X) := IsQuasiSeparated.of_quasiSeparatedSpace _
  have hVW : b ⁻¹ᵁ V ≤ W := by
    intro z hz
    by_contra h
    exact hVO hz ⟨z, h, rfl⟩

  have hfin : (b ⁻¹' (s : Set X)).Finite :=
    s.finite_toSet.preimage' fun x _ => b.finite_preimage_singleton x
  obtain ⟨f, hfV, hft⟩ := GlobalTheory.T.exists_basicOpen_between_finset_and_open' X₁ W hW (b ⁻¹ᵁ V) hVW hfin.toFinset
    (fun z hz => hsV _ ((hfin.mem_toFinset).1 hz))
  let f' : Γ(X₁, b ⁻¹ᵁ V) := X₁.presheaf.map (homOfLE hVW).op f
  have hf' : X₁.basicOpen f' = X₁.basicOpen f := by
    rw [Scheme.basicOpen_res]
    exact inf_eq_right.2 hfV
  obtain ⟨n, hn⟩ := GlobalTheory.T.exists_norm_basicOpen_finiteFree_baseChange R R₁ X X₁ p p₁ b H V hVc hVq f'
  refine ⟨X.basicOpen n, ?_, fun x hx => (hn x).2 ⟨hsV x hx, fun z hz => ?_⟩⟩
  swap
  · rw [hf']
    exact hft z ((hfin.mem_toFinset).2 (by simpa [hz] using hx))

  have hle : b ⁻¹ᵁ X.basicOpen n ≤ X₁.basicOpen f := by
    intro z hz
    rw [← hf']
    exact ((hn (b z)).1 hz).2 z rfl
  have hA : IsAffineOpen (b ⁻¹ᵁ X.basicOpen n) := by
    let g : Γ(X₁, X₁.basicOpen f) := X₁.presheaf.map (homOfLE hfV).op (b.app V n)
    have e : X₁.basicOpen g = b ⁻¹ᵁ X.basicOpen n := by
      rw [Scheme.basicOpen_res, ← Scheme.preimage_basicOpen]
      exact inf_eq_right.2 hle
    rw [← e]
    exact (hW.basicOpen f).basicOpen g
  have : IsAffine (b ⁻¹ᵁ X.basicOpen n).toScheme := hA
  exact isAffine_of_isPullback_of_flat_surjective
    ((isPullback_morphismRestrict b (X.basicOpen n)).paste_vert H)

end GlobalTheory.Mum
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.Cover

theorem comp_one_pt {S : Scheme.{0}} {G X Y : Over S} [GrpObj G] (f : X ⟶ Y) : f ≫ (1 : Y ⟶ G) = 1 := by
  rw [Hom.one_def, Hom.one_def, ← Category.assoc, comp_toUnit]

theorem exists_section_translate_mem : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (O : G.left.Opens), (∀ g : G.left, G.hom g = closedPoint R → g ∈ O) → ∀ x : G.left, ∃ a : 𝟙_ (Over (Sp R)) ⟶ G, (𝟙 G * (toUnit G ≫ a)).left x ∈ O := by
  intro R _ _ _ hB G _ _ hG O hO x
  obtain ⟨hN, -, -, hC⟩ := hB
  have : Smooth G.hom := hG.smooth
  have : GeometricallyConnected G.hom := hG.geomConnected
  have hGI : GeometricallyIntegral G.hom := GlobalTheory.geometricallyIntegral_of_smooth G.hom

  have hη : ∀ P : Sp R, (η[G] : 𝟙_ (Over (Sp R)) ⟶ G).left P ∈ O := by
    intro P
    have hc : G.hom ((η[G] : 𝟙_ (Over (Sp R)) ⟶ G).left (closedPoint R)) = closedPoint R := by
      change ((η[G] : 𝟙_ (Over (Sp R)) ⟶ G).left ≫ G.hom) (closedPoint R) = closedPoint R
      rw [Over.w]
      rfl
    exact ((IsLocalRing.specializes_closedPoint P).map (η[G] : 𝟙_ (Over (Sp R)) ⟶ G).left.continuous).mem_open
      O.2 (hO _ hc)
  by_cases hx : G.hom x = closedPoint R
  · refine ⟨η[G], ?_⟩
    have : toUnit G ≫ (η[G] : 𝟙_ (Over (Sp R)) ⟶ G) = 1 := (Hom.one_def).symm
    rw [this, _root_.mul_one]
    exact hO x hx

  haveI := hN
  let k := G.left.residueField x
  let xp : Sp k ⟶ G.left := G.left.fromSpecResidueField x
  let s : Sp k ⟶ Sp R := xp ≫ G.hom
  have hrange : Set.range xp = {x} := Scheme.range_fromSpecResidueField x
  have hxp : ∀ p, xp p = x := fun p => by
    have h : xp p ∈ Set.range xp := ⟨p, rfl⟩
    rw [hrange] at h
    exact h
  obtain ⟨p0⟩ : Nonempty (Sp k) := inferInstance
  have hs : closedPoint R ∉ Set.range s := by
    rintro ⟨p, hp⟩
    apply hx
    rw [← hp, ← hxp p]
    rfl
  have hirr : IrreducibleSpace (pullback G.hom s : Scheme.{0}) := by
    have : IsIntegral (pullback G.hom s) := hGI.geometrically_isIntegral s _ _ (IsPullback.of_hasPullback _ _)
    infer_instance
  let Sx : Over (Sp R) := Over.mk s
  let T : Over (Sp R) := Over.mk (pullback.snd G.hom s ≫ s)
  let X' : Sx ⟶ G := Over.homMk xp rfl
  let p1 : T ⟶ G := Over.homMk (pullback.snd G.hom s ≫ xp) (by simp [T, s])
  let p2 : T ⟶ G := Over.homMk (pullback.fst G.hom s) (by simp [T, pullback.condition])
  let m : T ⟶ G := p1 * p2
  let l : Sp k ⟶ pullback G.hom s := pullback.lift (X'⁻¹).left (𝟙 _) (by simpa [Sx] using Over.w (X'⁻¹))
  have hl1 : l ≫ pullback.fst G.hom s = (X'⁻¹).left := pullback.lift_fst _ _ _
  have hl2 : l ≫ pullback.snd G.hom s = 𝟙 _ := pullback.lift_snd _ _ _
  let σ : Sx ⟶ T := Over.homMk l (by
    change l ≫ pullback.snd G.hom s ≫ s = s
    rw [reassoc_of% hl2])
  have hσ : σ ≫ m = 1 := by
    have e1 : σ ≫ p1 = X' := by
      ext
      change l ≫ pullback.snd G.hom s ≫ xp = xp
      rw [reassoc_of% hl2]
    have e2 : σ ≫ p2 = X'⁻¹ := by
      ext
      exact hl1
    rw [comp_mul, e1, e2, _root_.mul_inv_cancel]
  have hne : ((m.left ⁻¹ᵁ O : (pullback G.hom s).Opens) : Set (pullback G.hom s : Scheme.{0})).Nonempty := by
    refine ⟨σ.left p0, ?_⟩
    change (σ.left ≫ m.left) p0 ∈ O
    rw [← Over.comp_left, hσ, Hom.one_def, Over.comp_left]
    exact hη _
  have he : (η[G] : 𝟙_ (Over (Sp R)) ⟶ G).left ≫ G.hom = 𝟙 _ := (Over.w _).trans (by simp)
  obtain ⟨a, aΩ, ha, h1, h2, h3⟩ := GlobalTheory.T.smoothGroup_sections_dense_in_fibres R hC G ‹_› _ he k s hs hirr _ hne
  let A : 𝟙_ (Over (Sp R)) ⟶ G := Over.homMk a (ha.trans (by simp))
  let AΩ : Sx ⟶ T := Over.homMk aΩ (by simp [T, Sx, reassoc_of% h2])
  have f1 : AΩ ≫ p1 = X' := by ext; simp [AΩ, p1, X', reassoc_of% h2]
  have f2 : AΩ ≫ p2 = toUnit Sx ≫ A := by ext; simp [AΩ, p2, A, h1, Sx]
  have key : X' ≫ (𝟙 G * (toUnit G ≫ A)) = AΩ ≫ m := by
    rw [comp_mul, comp_mul, f1, f2, Category.comp_id, comp_toUnit_assoc]
  refine ⟨A, ?_⟩
  rw [← hxp p0]
  change (X' ≫ (𝟙 G * (toUnit G ≫ A))).left p0 ∈ O
  rw [key]
  exact h3 ⟨p0, rfl⟩

end GlobalTheory.Mum.Cover
end
