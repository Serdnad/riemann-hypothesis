module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle073
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2801
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2802
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2806
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.CstDvdOfCstMulEqZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle074
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSpecialisationWithThetaPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2670
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.BiadditiveOfTrivAxes
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle031
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushEquivSymmLeft
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle034
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsFiniteEtaleCoverConstantTorsion
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2937
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.TotallySplit
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.LevelFrameOfLaws
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle067
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.Rescale

theorem gs_comp_stalk {X Y Z : Scheme.{0}} (g : Z ⟶ Y) (f : Y ⟶ X) (z : Z) (U : X.Opens) (h : f (g z) ∈ U)
    (a : Γ(X, U)) : gs (g ≫ f) z U a = (g.stalkMap z).hom (gs f (g z) U a) := by
  rw [gs_stalkMap (g ≫ f) z U h, gs_stalkMap f (g z) U h, Scheme.Hom.stalkMap_comp]
  rfl

theorem cst_zero' {V : Type} [CommRing V] {Z : Scheme.{0}} (q : Z ⟶ Sp V) (z : Z) : cst q z 0 = 0 := by
  simp only [cst, gs_eq q z ⊤ trivial, map_zero]

theorem sval_secScale {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (c : Γ(Y, ⊤)) (s : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y) (z : Z) {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    sval (ReciprocityTheory.ChartRestriction.G.DVR.SecOps.secScale c s) r z J = gs r z ⊤ c * sval s r z J :=
  (gs_mul r z _ (hJ.mem φ r) _ _).trans (congrArg (· * _) (gs_res r z le_top (hJ.mem φ r) c))

theorem gs_scal {V : Type} [CommRing V] {Y Z : Scheme.{0}} (q : Y ⟶ Sp V) (r : Z ⟶ Y) (z : Z) (a : V) :
    gs r z ⊤ (scal q a) = cst (r ≫ q) z a :=
  gs_pull r q z ⊤ trivial _

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {D : DegData R (maximalIdeal R)}

theorem cancel (C : LabCover D) {W : Type} [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W)
    (hα : Flat C.α) (b : W) (hb : b ≠ 0) (s₁ : SecK C.P.L.L T.β 1) (s₂ : SecK C.P.L.L C.α 1)
    (h : ∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ C.A.A.left), p ≫ T.β = p' ≫ C.α → ∀ z J,
      Good C.P.L.L z J → cst (p ≫ T.G.hom) z b * sval s₁ p z J = cst (p ≫ T.G.hom) z b * sval s₂ p' z J)
    (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ C.A.A.left) (hp : p ≫ T.β = p' ≫ C.α) (z : Z)
    (J : (Z ⟶ C.G.left) → C.P.L.L.ι) (hJ : Good C.P.L.L z J) : sval s₁ p z J = sval s₂ p' z J := by
  haveI := T.U.smooth
  haveI : Flat (pullback.fst T.β C.α ≫ T.G.hom) := inferInstance
  obtain ⟨g, rfl, rfl⟩ : ∃ g, g ≫ pullback.fst T.β C.α = p ∧ g ≫ pullback.snd T.β C.α = p' :=
    ⟨pullback.lift p p' hp, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  obtain ⟨J₀, hJ₀, e₀⟩ := exists_good C.P.L.L C.P.L.isLB (g z) (K := Unit)
    (fun _ => pullback.fst T.β C.α ≫ T.β) (fun _ => J ((g ≫ pullback.fst T.β C.α) ≫ T.β)) (fun _ _ _ => rfl)
    (fun _ => hJ ((g ≫ pullback.fst T.β C.α) ≫ T.β))
  have key := h _ (pullback.fst T.β C.α) (pullback.snd T.β C.α) pullback.condition (g z) J₀ hJ₀
  have eJ : J₀ (pullback.snd T.β C.α ≫ C.α) = J₀ (pullback.fst T.β C.α ≫ T.β) :=
    congrArg J₀ pullback.condition.symm
  have A₁ : sval s₁ (g ≫ pullback.fst T.β C.α) z J = (g.stalkMap z).hom (sval s₁ (pullback.fst T.β C.α) (g z) J₀) := by
    rw [sval_of s₁ _ z J (fun _ => J₀ (pullback.fst T.β C.α ≫ T.β)) (fun _ => (e₀ ()).symm),
      sval_of s₁ _ (g z) J₀ (fun _ => J₀ (pullback.fst T.β C.α ≫ T.β)) (fun _ => rfl)]
    exact gs_comp_stalk g _ z _ (hJ₀.mem _ _) _
  have A₂ : sval s₂ (g ≫ pullback.snd T.β C.α) z J = (g.stalkMap z).hom (sval s₂ (pullback.snd T.β C.α) (g z) J₀) := by
    have e₁ : J ((g ≫ pullback.snd T.β C.α) ≫ C.α) = J₀ (pullback.fst T.β C.α ≫ T.β) := by
      rw [e₀ (), Category.assoc, Category.assoc, pullback.condition]
    rw [sval_of s₂ _ z J (fun _ => J₀ (pullback.fst T.β C.α ≫ T.β)) (fun _ => e₁),
      sval_of s₂ _ (g z) J₀ (fun _ => J₀ (pullback.fst T.β C.α ≫ T.β)) (fun _ => eJ)]
    refine gs_comp_stalk g _ z _ ?_ _
    exact Set.mem_iInter.2 fun _ => by rw [← eJ]; exact hJ₀ (pullback.snd T.β C.α ≫ C.α)
  have hz : sval s₁ (pullback.fst T.β C.α) (g z) J₀ = sval s₂ (pullback.snd T.β C.α) (g z) J₀ := by
    have h0 : cst (pullback.fst T.β C.α ≫ T.G.hom) (g z) b *
        (sval s₁ (pullback.fst T.β C.α) (g z) J₀ - sval s₂ (pullback.snd T.β C.α) (g z) J₀) = 0 := by
      rw [mul_sub, key, sub_self]
    have := GlobalTheory.cst_dvd_of_cst_mul_eq_zero (pullback.fst T.β C.α ≫ T.G.hom) (g z) (a := b) (b := 0)
      (fun c hc => zero_dvd_iff.2 ((mul_eq_zero.1 hc).resolve_left hb)) h0
    rw [cst_zero', zero_dvd_iff, sub_eq_zero] at this
    exact this
  rw [A₁, A₂, hz]

end GlobalTheory.Mum.Rescale

namespace GlobalTheory.Mum.Rescale

theorem cst_unit {V : Type} [CommRing V] {Z : Scheme.{0}} (q : Z ⟶ Sp V) (z : Z) {u : V} (hu : IsUnit u) :
    IsUnit (cst q z u) := by
  obtain ⟨w, rfl⟩ := hu
  refine ⟨⟨cst q z w, cst q z ↑w⁻¹, ?_, ?_⟩, rfl⟩
  · rw [← ReciprocityTheory.ChartRestriction.G.H1.cst_mul, Units.mul_inv, ReciprocityTheory.ChartRestriction.G.H1.cst_one]
  · rw [← ReciprocityTheory.ChartRestriction.G.H1.cst_mul, Units.inv_mul, ReciprocityTheory.ChartRestriction.G.H1.cst_one]

theorem rescale : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (F₁ : IntFam (maximalIdeal R) D.toPre 1) (θ₀ : SecK C.P.L.L C.α 1) (r t : R) (x : FractionRing R), r ≠ 0 → x * algebraMap R (FractionRing R) r = algebraMap R (FractionRing R) t → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (a b : W) (v : Wˣ), a ≠ 0 → b ≠ 0 → T.Exp a b θ₀ F₁ → b * T.φ t = a * T.φ r * v → T.Exp 1 (v : W) (ReciprocityTheory.ChartRestriction.G.DVR.SecOps.secScale (scal C.A.A.hom x) θ₀) F₁ := by
  intro R _ _ _ _ D C F₁ θ₀ r t x hr hx W _ _ _ T a b v ha hb hE hbt
  obtain ⟨σ, ⟨σ', f', hC, hP, hX⟩, hσ⟩ := hE
  have hw : PGen T.ℓ := (isGen_iff T.ℓ).1 T.ℓ_gen
  obtain ⟨s, hs⟩ := sec_upK hw C.P.L.isLB T.U.LG.isLB (φ' := fun _ : Fin 1 => 𝟙 T.G.left)
    (ε := fun _ => ((1 : ℕ) : ℤ)) σ'
  have gen : ∀ ψ : Fin 1 → (T.G.left ⟶ C.G.left), ψ = (fun _ => T.β) →
      ∀ s : LB.Sec (LB.LinComb C.P.L.L ψ (fun _ => ((1 : ℕ) : ℤ))), ∃ s' : SecK C.P.L.L T.β 1,
        ∀ (Z : Scheme.{0}) (r : Z ⟶ T.G.left) z J, sval s' r z J = sval s r z J := by
    rintro ψ rfl s
    exact ⟨s, fun _ _ _ _ => rfl⟩
  obtain ⟨s', hs'⟩ := gen _ (funext fun _ => Category.id_comp _) s
  have hs₁ : ∀ (Z : Scheme.{0}) (r : Z ⟶ T.G.left) (z : Z) J J', Good C.P.L.L z J → Good T.U.LG.L z J' →
      sval s' r z J = (gw T.ℓ r z (J (r ≫ T.β)) (J' r)).val * sval σ' r z J' := by
    intro Z r z J J' hJ hJ'
    rw [hs', hs Z r z J J' hJ hJ']
    simp [pw, Fin.prod_univ_one]
  let σ₁ : SecK C.P.L.L T.β 1 := ReciprocityTheory.ChartRestriction.G.DVR.SecOps.secScale (scal T.G.hom (v : W)) s'
  have hC₁ : T.Carries (v : W) σ' σ₁ := by
    intro Z r z J J' hJ hJ'
    rw [sval_secScale _ _ _ _ hJ, hs₁ Z r z J J' hJ hJ', pow_one, _root_.mul_assoc]
  have hα : Flat C.α := MorphismProperty.of_isPullback (P := @Flat) C.α_cart.1.flip (GlobalTheory.T.genericPoint_flat_of_modification_of_domain R C.toModif)
  refine ⟨σ₁, ⟨σ', f', hC₁, hP, hX⟩, fun Z p p' hpp z J hJ => ?_⟩
  rw [gs_scal, ReciprocityTheory.ChartRestriction.G.H1.cst_one, _root_.one_mul]
  refine cancel C T hα b hb σ₁ _ (fun Z p p' hpp z J hJ => ?_) Z p p' hpp z J hJ
  choose I hI using fun χ : Z ⟶ T.G.left => exists_chart T.U.LG.isLB (χ z)
  have hI' : Good T.U.LG.L z I := hI
  have e1 := hC Z p z J I hJ hI'
  have e2 := hσ Z p p' hpp z J hJ
  rw [e1, gs_scal, gs_scal, pow_one] at e2
  rw [sval_secScale _ _ _ _ hJ, sval_secScale _ _ _ _ hJ, hs₁ Z p z J I hJ hI', gs_scal, gs_scal]

  have hρ : ∀ c : R, cst (p ≫ T.G.hom) z (T.φ c) = cst (p' ≫ C.A.A.hom) z (algebraMap R (FractionRing R) c) := by
    intro c
    have hm : (p ≫ T.G.hom) ≫ spMap T.φ = (p' ≫ C.A.A.hom) ≫ spMap (algebraMap R (FractionRing R)) := by
      have h1 : T.β ≫ C.G.hom = T.G.hom ≫ T.ξ := T.cart.1.w
      have h2 : C.α ≫ C.G.hom = C.A.A.hom ≫ C.gp := C.α_cart.1.w
      calc (p ≫ T.G.hom) ≫ spMap T.φ = p ≫ T.G.hom ≫ T.ξ ≫ C.π := by rw [T.ξ_π, Category.assoc]
        _ = (p ≫ T.β) ≫ C.G.hom ≫ C.π := by rw [← Category.assoc T.G.hom, ← h1]; simp only [Category.assoc]
        _ = (p' ≫ C.α) ≫ C.G.hom ≫ C.π := by rw [hpp]
        _ = p' ≫ C.A.A.hom ≫ C.gp ≫ C.π := by rw [Category.assoc, ← Category.assoc C.α, h2]; simp only [Category.assoc]
        _ = (p' ≫ C.A.A.hom) ≫ spMap (algebraMap R (FractionRing R)) := by rw [C.gp_π, Category.assoc]
    rw [← cst_comp, hm, cst_comp]
  have hrU : IsUnit (cst (p' ≫ C.A.A.hom) z (algebraMap R (FractionRing R) r)) :=
    cst_unit _ _ (isUnit_iff_ne_zero.2 ((map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 hr))
  have hx' : cst (p' ≫ C.A.A.hom) z x * cst (p' ≫ C.A.A.hom) z (algebraMap R (FractionRing R) r) =
      cst (p' ≫ C.A.A.hom) z (algebraMap R (FractionRing R) t) := by
    rw [← ReciprocityTheory.ChartRestriction.G.H1.cst_mul, hx]
  have hbt' : cst (p ≫ T.G.hom) z b * cst (p ≫ T.G.hom) z (T.φ t) =
      cst (p ≫ T.G.hom) z a * cst (p ≫ T.G.hom) z (T.φ r) * cst (p ≫ T.G.hom) z (v : W) := by
    rw [← ReciprocityTheory.ChartRestriction.G.H1.cst_mul, ← ReciprocityTheory.ChartRestriction.G.H1.cst_mul, ← ReciprocityTheory.ChartRestriction.G.H1.cst_mul, hbt]
  rw [hρ, hρ, ← hx'] at hbt'
  have hsc : cst (p ≫ T.G.hom) z b * cst (p' ≫ C.A.A.hom) z x =
      cst (p ≫ T.G.hom) z a * cst (p ≫ T.G.hom) z (v : W) := by
    apply hrU.mul_right_cancel
    linear_combination hbt'
  linear_combination (cst (p ≫ T.G.hom) z (v : W)) * e2 - sval θ₀ p' z J * hsc

end GlobalTheory.Mum.Rescale
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.WeilRoot

theorem eq_zpow_of_map_eq {O K : Type} [CommRing O] [IsDomain O] [Field K] (κ : O →+* K) {N : ℕ} (hN : 0 < N)
    (hu : IsUnit (N : O)) {ζ w : Oˣ} (hζ : IsPrimitiveRoot ζ N) (hw : w ^ N = 1) (m : ℤ)
    (h : Units.map κ.toMonoidHom w = Units.map κ.toMonoidHom (ζ ^ m)) : w = ζ ^ m := by
  have : NeZero N := ⟨hN.ne'⟩
  set y : Oˣ := w * (ζ ^ m)⁻¹ with hy
  have hyN : y ^ N = 1 := by
    rw [hy, _root_.mul_pow, hw, _root_.one_mul, inv_pow, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
      hζ.pow_eq_one, one_zpow, inv_one]
  have hζ' : IsPrimitiveRoot (ζ : O) N := IsPrimitiveRoot.coe_units_iff.2 hζ
  obtain ⟨i, hi, hiy⟩ := hζ'.eq_pow_of_pow_eq_one (ξ := (y : O)) (by rw [← Units.val_pow_eq_pow_val, hyN, Units.val_one])
  have hκ : IsPrimitiveRoot (κ ζ) N := by
    have : NeZero (N : K) := ⟨by simpa using (hu.map κ).ne_zero⟩
    rw [← (Polynomial.isRoot_cyclotomic_iff (R := K) (n := N)), ← Polynomial.map_cyclotomic N κ]
    exact (hζ'.isRoot_cyclotomic hN).map κ
  have hκy : κ (y : O) = 1 := by
    have h' : κ (w : O) = κ ((ζ ^ m : Oˣ) : O) := congrArg (fun u : Kˣ => (u : K)) h
    rw [hy, Units.val_mul, map_mul, h', ← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]
  have hi0 : i = 0 := by
    have h1 : κ (ζ : O) ^ i = 1 := by rw [← map_pow, hiy, hκy]
    have := hκ.dvd_of_pow_eq_one i h1
    exact Nat.eq_zero_of_dvd_of_lt this hi
  have hy1 : y = 1 := Units.ext (by rw [← hiy, hi0, pow_zero, Units.val_one])
  rw [hy] at hy1
  exact mul_inv_eq_one.1 hy1

end GlobalTheory.WeilRoot
end

noncomputable section
namespace GlobalTheory.WeilRoot

open GlobalTheory.CechPic GlobalTheory.DiagPairing

theorem weilIs_zpow_of_fieldPoint : ∀ (O : Type) [CommRing O] [IsDomain O] (A : Over (Sp O)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (P : LB (G2 A).left), IsPPol A P → ∀ (N : ℕ), 0 < N → IsUnit (N : O) → ∀ (u v : 𝟙_ (Over (Sp O)) ⟶ A), u ^ N = 1 → v ^ N = 1 → ∀ (ζ : Oˣ), IsPrimitiveRoot ζ N → ∀ (m : ℤ) (K : Type) [Field K] (κ : O →+* K), Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) N (toUnit (Over.mk (spMap κ)) ≫ u) (toUnit (Over.mk (spMap κ)) ≫ v) (unitOn (Units.map κ.toMonoidHom (ζ ^ m))) → ∀ (k : Type) [Field k] (ρ : O →+* k), Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) N (toUnit (Over.mk (spMap ρ)) ≫ u) (toUnit (Over.mk (spMap ρ)) ≫ v) (unitOn (Units.map ρ.toMonoidHom (ζ ^ m))) := by
  intro O _ _ A _ _ hA P hPP N hN hNu u v hu hv ζ hζ m K _ κ H k _ ρ
  obtain ⟨⟨hP, h₁, h₂, -⟩, hamp, -⟩ := hPP
  have hG : Out.GlobalFnsSt := GlobalTheory.globalFns_holds
  have hD : (P.pull (lift (𝟙 A) (𝟙 A)).left).IsLB := pull_isLB hP _
  have hB : ∀ (T : Over (Sp O)) (x x' y : T ⟶ A), pc hP (x * x') y = pc hP x y + pc hP x' y :=
    fun T x x' y => by
      obtain ⟨t, ht⟩ := (GlobalTheory.Biadditive.biadditive_of_triv_axes hG (Sp O) A _ hA hD hamp P hP h₁ h₂
        T x x' y).1
      have e := (cls_eq_zero_iff (LB.isLB_linComb hP _ _)).2 ⟨t, ht⟩
      rw [cls_linComb hP, Fin.sum_univ_three] at e
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons, one_smul, neg_smul] at e
      unfold pc
      rw [← sub_eq_zero, ← e]
      abel
  have hB' : ∀ (T : Over (Sp O)) (x y y' : T ⟶ A), pc hP x (y * y') = pc hP x y + pc hP x y' :=
    fun T x y y' => by
      obtain ⟨t, ht⟩ := (GlobalTheory.Biadditive.biadditive_of_triv_axes hG (Sp O) A _ hA hD hamp P hP h₁ h₂
        T y y' x).2
      have e := (cls_eq_zero_iff (LB.isLB_linComb hP _ _)).2 ⟨t, ht⟩
      rw [cls_linComb hP, Fin.sum_univ_three] at e
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons, one_smul, neg_smul] at e
      unfold pc
      rw [← sub_eq_zero, ← e]
      abel
  have lifts : ∀ z : 𝟙_ (Over (Sp O)) ⟶ A, z ^ N = 1 → ∀ p : (𝟙_ (Over (Sp O))).left, ∃ V : (𝟙_ (Over (Sp O))).left.Opens,
      p ∈ V ∧ ∃ θ : Out.ThetaGrp A (P.pull (lift (𝟙 A) (𝟙 A)).left) N (Out.overRes V), θ.pt = Out.overResι V ≫ z :=
    fun z hz p => by
      obtain ⟨θ, hθ⟩ := exists_theta_diag hP hB hB' (k := N) (Out.overResι ⊤ ≫ z)
        (by rw [← MonObj.comp_pow, hz, MonObj.comp_one])
      exact ⟨⊤, trivial, θ, hθ⟩
  obtain ⟨c₀, hc₀⟩ := CommutatorPairing.exists_weilIs hG hA hD (lifts u hu) (lifts v hv)
  obtain ⟨c₁, hc₁⟩ := CommutatorPairing.exists_weilIs hG hA hD (lifts 1 (one_pow N)) (lifts v hv)
  have h11 := GlobalTheory.DiagPairing.weilIs_mul_left hG hA hD hc₁ hc₁
  rw [_root_.mul_one] at h11
  have e₁ : c₁ = 1 := mul_eq_left.1 (CommutatorPairing.weilIs_unique hG hA hD h11 hc₁)
  have pw : ∀ n : ℕ, Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) N (u ^ (n + 1)) v (c₀ ^ (n + 1)) := by
    intro n
    induction n with
    | zero => simpa using hc₀
    | succ n ih =>
      rw [pow_succ u (n + 1), pow_succ c₀ (n + 1)]
      exact GlobalTheory.DiagPairing.weilIs_mul_left hG hA hD ih hc₀
  have hp := pw (N - 1)
  rw [Nat.sub_add_cancel hN, hu] at hp
  have hc₀N : c₀ ^ N = 1 := CommutatorPairing.weilIs_unique hG hA hD hp (e₁ ▸ hc₁)
  obtain ⟨w, rfl⟩ := GlobalTheory.Ex.Specialise.unitOn_bijective.2 c₀
  have hwN : w ^ N = 1 := by
    apply GlobalTheory.Ex.Specialise.unitOn_bijective.1
    have e : unitOn (w ^ N) = unitOn w ^ N := by unfold unitOn; exact map_pow _ _ _
    rw [e, hc₀N]
    unfold unitOn; exact (map_one _).symm
  have spec : ∀ (F : Type) [Field F] (σ : O →+* F), Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) N
      (toUnit (Over.mk (spMap σ)) ≫ u) (toUnit (Over.mk (spMap σ)) ≫ v) (unitOn (Units.map σ.toMonoidHom w)) := by
    intro F _ σ
    have hN' := CommPairing.weilIs_pull hG hA hD (toUnit (Over.mk (spMap σ))) hc₀
    have hl : (toUnit (Over.mk (spMap σ))).left = spMap σ := rfl
    rw [hl, GlobalTheory.Ex.Specialise.map_unitOn] at hN'
    exact hN'
  have e := GlobalTheory.Ex.Specialise.unitOn_bijective.1 (CommutatorPairing.weilIs_unique hG hA hD (spec K κ) H)
  have hw : w = ζ ^ m := eq_zpow_of_map_eq κ hN hNu hζ hwN m e
  rw [← hw]
  exact spec k ρ

end GlobalTheory.WeilRoot
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorsConst

theorem exists_factor_generic {R : Type} [CommRing R] [IsDomain R] {k : Type} [Field k] (τ : Sp k ⟶ Sp R)
    (w : Sp k) (hw : τ w = (⊥ : PrimeSpectrum R)) : ∃ κ : FractionRing R →+* k, τ = spMap κ ≫ jK R := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective τ
  have hφ : Function.Injective φ.hom := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    have h1 : PrimeSpectrum.comap φ.hom w = ⊥ := hw
    have h2 : a ∈ (PrimeSpectrum.comap φ.hom w).asIdeal := by
      show φ.hom a ∈ (w : PrimeSpectrum k).asIdeal
      rw [ha]; exact Ideal.zero_mem _
    rw [h1] at h2
    exact h2
  refine ⟨IsFractionRing.lift hφ, ?_⟩
  rw [← Spec.map_comp]
  congr 1
  ext a
  simp

theorem exists_section_generic {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] {n : ℕ} (hA : IsAbelianScheme A) (hn : IsUnit (n : Γ(Sp R, ⊤)))
    (h : TorsRat A n) {K : Type} [Field K] [IsAlgClosed K] (κ : FractionRing R →+* K)
    (x : Over.mk (spMap κ ≫ jK R) ⟶ A) (hx : x ^ n = 1) :
    ∃ σ : 𝟙_ (Over (Sp R)) ⟶ A, σ ^ n = 1 ∧ toUnit _ ≫ σ = x := by
  obtain ⟨x₀, h₀⟩ := h K κ x hx
  let ρ : Over.mk (spMap κ ≫ jK R) ⟶ Over.mk (jK R) := Over.homMk (spMap κ) rfl
  have e₀ : x = ρ ≫ x₀ := Over.OverMorphism.ext h₀
  have hfl : Flat (spMap κ) := by
    letI := κ.toAlgebra
    exact (HasRingHomProperty.Spec_iff (P := @Flat)).2 (RingHom.flat_algebraMap_iff.2 inferInstance)
  have hsu : Surjective (spMap κ) := ⟨fun p => ⟨Classical.arbitrary _, Subsingleton.elim (α := Sp (FractionRing R)) _ _⟩⟩
  have hepi : Epi ρ.left := Flat.epi_of_flat_of_surjective (spMap κ)
  have hx₀ : x₀ ^ n = 1 := by
    have : ρ ≫ x₀ ^ n = ρ ≫ 1 := by rw [MonObj.comp_pow, ← e₀, hx, MonObj.comp_one]
    exact Over.OverMorphism.ext ((cancel_epi ρ.left).1 congr(($this).left))
  have hT : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (Sp R) := fun p => by
    refine ⟨inferInstance, ?_⟩
    have : (PrimeSpectrum.asIdeal p).IsPrime := PrimeSpectrum.isPrime p
    have h := StructureSheaf.IsLocalization.to_stalk R p
    exact @isIntegrallyClosed_of_isLocalization R ((Spec.structureSheaf R).presheaf.stalk p) _ _ (_) _ _
      (PrimeSpectrum.asIdeal p).primeCompl (Ideal.primeCompl_le_nonZeroDivisors _) h
  have j₁ : IsPreimmersion (jK R) := IsPreimmersion.of_isLocalization (nonZeroDivisors R)
  have j₂ : Flat (jK R) :=
    (HasRingHomProperty.Spec_iff (P := @Flat)).2 (RingHom.flat_algebraMap_iff.2 inferInstance)
  have j₃ : IsDominant (jK R) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2 (by
    intro a ha
    have : a = 0 := IsFractionRing.injective R (FractionRing R) (ha.trans (map_zero _).symm)
    rw [this]; exact Ideal.zero_mem _)⟩
  have hp : IsProper A.hom := hA.proper
  obtain ⟨s, hs₁, hs₂⟩ := exists_section_of_pow_eq_one hT (jK R) A n hn _ x₀ hx₀ (𝟙 _) (Category.id_comp _)
  let σ : 𝟙_ (Over (Sp R)) ⟶ A := Over.homMk s hs₁
  have e₁ : toUnit (Over.mk (jK R)) ≫ σ = x₀ := by
    apply Over.OverMorphism.ext
    rw [Over.comp_left, GlobalTheory.ObjPull.toUnit_left']
    exact hs₂.trans (Category.id_comp _)
  refine ⟨σ, ?_, ?_⟩
  · have : toUnit (Over.mk (jK R)) ≫ σ ^ n = toUnit (Over.mk (jK R)) ≫ 1 := by
      rw [MonObj.comp_pow, e₁, hx₀, MonObj.comp_one]
    apply Over.OverMorphism.ext
    have h2 := congr(($this).left)
    rw [Over.comp_left, Over.comp_left, GlobalTheory.ObjPull.toUnit_left'] at h2
    have : AlgebraicGeometry.IsReduced (𝟙_ (Over (Sp R))).left := inferInstanceAs (AlgebraicGeometry.IsReduced (Sp R))
    exact ext_of_isDominant_of_isSeparated A.hom (by rw [Over.w, Over.w]) (jK R) h2
  · rw [e₀, ← e₁, ← Category.assoc, comp_toUnit]

theorem exists_section_of_torsRat : ∀ (R₀ : Type) [CommRing R₀] [IsDomain R₀] [IsNoetherianRing R₀] [IsIntegrallyClosed R₀] (A : Over (Sp R₀)) [GrpObj A] [IsCommMonObj A] (n : ℕ), IsAbelianScheme A → IsUnit (n : R₀) → TorsRat A n → ∀ (K : Type) [Field K] [IsAlgClosed K] (t : Sp K ⟶ Sp R₀) (x : Over.mk t ⟶ A), x ^ n = 1 → ∃ σ : 𝟙_ (Over (Sp R₀)) ⟶ A, σ ^ n = 1 ∧ toUnit (Over.mk t) ≫ σ = x := by
  intro R _ _ _ _ A _ _ n hA hn h K _ _ t x hx
  have hn' : IsUnit (n : Γ(Sp R, ⊤)) := by
    have := hn.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
    rwa [map_natCast] at this
  obtain ⟨-, hfin, het⟩ := GrpTangent.finiteEtale_mulN_torsion A hn'
  obtain ⟨y, hy, -⟩ := LatticeTorsion.existsUnique_torsion A n x hx
  obtain ⟨w⟩ : Nonempty (Sp K) := inferInstance
  have hs : (⊥ : PrimeSpectrum R) ⤳ (torsion A n).hom (y.left w) :=
    (PrimeSpectrum.le_iff_specializes _ _).1 bot_le
  obtain ⟨z, hz, ez⟩ := Flat.generalizingMap (torsion A n).hom hs
  let k := AlgebraicClosure ((torsion A n).left.residueField z)
  let u : Sp k ⟶ (torsion A n).left :=
    spMap (algebraMap ((torsion A n).left.residueField z) k) ≫ (torsion A n).left.fromSpecResidueField z
  obtain ⟨v⟩ : Nonempty (Sp k) := inferInstance
  have hu : u v = z := by
    have : u v ∈ Set.range ((torsion A n).left.fromSpecResidueField z) := ⟨_, (Scheme.Hom.comp_apply _ _ _).symm⟩
    rwa [Scheme.range_fromSpecResidueField] at this
  obtain ⟨κ, hκ⟩ := exists_factor_generic (u ≫ (torsion A n).hom) v
    ((Scheme.Hom.comp_apply _ _ _).trans (by rw [hu]; exact ez))
  let u' : Over.mk (spMap κ ≫ jK R) ⟶ torsion A n := Over.homMk u hκ
  obtain ⟨σ, hσ, eσ⟩ := exists_section_generic A hA hn' h κ (u' ≫ torsion.ι A n) (by
    rw [← MonObj.comp_pow, LatticeTorsion.torsionι_pow_eq_one, MonObj.comp_one])
  obtain ⟨C, hC, hCz⟩ := TorsionCover.exists_clopen_eq_one A hA hn'
    (torsion.ι A n * (toUnit _ ≫ σ)⁻¹) (by
      rw [mul_pow, inv_pow, ← MonObj.comp_pow, hσ, MonObj.comp_one, LatticeTorsion.torsionι_pow_eq_one, inv_one,
        _root_.mul_one])
  have key : ∀ (T : Over (Sp R)) (a : T ⟶ torsion A n),
      a ≫ (torsion.ι A n * (toUnit _ ≫ σ)⁻¹) = 1 ↔ toUnit T ≫ σ = a ≫ torsion.ι A n := fun T a => by
    rw [MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc, comp_toUnit, mul_inv_eq_one, eq_comm]
  have hzC : z ∈ C := (hCz _ u').1 ((key _ _).2 eσ) ⟨v, hu⟩
  have hyC : y.left w ∈ C := hz.mem_closed hC.isClosed hzC
  refine ⟨σ, hσ, ?_⟩
  rw [← hy]
  refine (key _ _).1 ((hCz _ y).2 ?_)
  rintro _ ⟨w', rfl⟩
  rwa [Subsingleton.elim (α := Sp K) w' w]

end GlobalTheory.TorsConst
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.UPoinc

theorem uOrdEq_stalkHom_of_associated : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] (M : RatModel o' Ω) (x : M.Z) (T : UTrait Xo c) (ξ : Sp T.V ⟶ M.Z), ξ (IsLocalRing.closedPoint T.V) ⤳ x → ∀ (R : Type) [CommRing R] (j : M.Z.presheaf.stalk x →+* R) (V' : Type) [CommRing V'] [IsDomain V'] [IsDiscreteValuationRing V'] (h : T.V →+* V') (g' : R →+* V'), Function.Injective h → Irreducible (h T.ϖ) → spMap g' ≫ (spMap j ≫ M.Z.fromSpecStalk x) = spMap h ≫ ξ → ∀ (a : M.Z.presheaf.stalk x) (k : ℕ), Associated (g' (j a)) (h T.ϖ ^ k) → UOrdEq M T ξ (M.stalkHom x a) k := by
  intro E _ _ _ H Dw l Xo c o' Ω _ _ _ M x T ξ hx R _ j V' _ _ _ h g' hinj hirr hcomm a k ha
  haveI : IsDiscreteValuationRing T.V := T.cdvr.1
  let v : M.Z.presheaf.stalk x ⟶ CommRingCat.of T.V :=
    M.Z.presheaf.stalkSpecializes hx ≫ Scheme.stalkClosedPointTo (R := CommRingCat.of T.V) ξ
  have hv : Spec.map v ≫ M.Z.fromSpecStalk x = ξ := by
    rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
      Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
  have e1 : Spec.map (CommRingCat.ofHom j ≫ CommRingCat.ofHom g') = Spec.map (v ≫ CommRingCat.ofHom h) := by
    rw [← cancel_mono (M.Z.fromSpecStalk x), Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc, hv]
    exact hcomm
  have e2 : g' (j a) = h (v.hom a) := congrArg (fun φ => φ.hom a) (Spec.map_injective e1)
  have e3 : M.val (jK T.V ≫ ξ) (M.stalkHom x a) = algebraMap T.V (FractionRing T.V) (v.hom a) := by
    refine (RatModel.val_spMap_comp (algebraMap T.V (FractionRing T.V)) ξ hx (M.stalkEquiv x a)).trans ?_
    rw [RatModel.valLoc, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      RingEquiv.symm_apply_apply]
  rw [e2] at ha
  have h0 : v.hom a ≠ 0 := fun h0 => by
    rw [h0, map_zero] at ha
    exact pow_ne_zero k hirr.ne_zero (associated_zero_iff_eq_zero _ |>.1 ha.symm)
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h0 T.irr
  have h1 : Associated (h T.ϖ ^ n) (h T.ϖ ^ k) := by
    refine Associated.trans ?_ ha
    rw [hu, map_mul, map_pow]
    exact (associated_unit_mul_left _ _ (u.isUnit.map h)).symm
  have hn : n = k := le_antisymm ((pow_dvd_pow_iff hirr.ne_zero hirr.not_isUnit).1 h1.dvd)
    ((pow_dvd_pow_iff hirr.ne_zero hirr.not_isUnit).1 h1.symm.dvd)
  exact ⟨u, by rw [e3, hu, hn, mul_comm]⟩

end GlobalTheory.UPoinc
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points

theorem _root_.GlobalTheory.T.chernIntegrableOn_descend_genericallyFinite : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp k) (e : ℕ), IsArithVar q e → ∀ (Y' : Scheme.{0}) [IsIntegral Y'] (ρ : Y' ⟶ Y), IsArithVar (ρ ≫ q) e → ρ (genericPoint Y') = genericPoint Y → ρ.residueDegree (genericPoint Y') ≠ 0 → ∀ (N : HermLB q) (σ : k →+* ℂ) (U : Y.Opens) (f : CxPts q σ → ℝ), ContinuousOn f (ptsIn q σ U) → ((N.restr ρ).φ σ).ChernIntegrableOn e (ptsIn (ρ ≫ q) σ (ρ ⁻¹ᵁ U)) (fun y => f (PtsOver.map ρ rfl _ y)) → (N.φ σ).ChernIntegrableOn e (ptsIn q σ U) f := by
  first | exact @GlobalTheory.ChernDescend.chernIntegrableOn_descend | exact GlobalTheory.ChernDescend.chernIntegrableOn_descend | (intros; apply GlobalTheory.ChernDescend.chernIntegrableOn_descend <;> assumption)
end
