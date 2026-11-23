module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle073
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle070
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRatPointOfFiniteType
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2802
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2815
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2889
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCocycleUnit
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068

@[expose] public section

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum

section

variable {R : Type} [CommRing R] [IsDomain R]

def mulφB (D : DegPre R) (m : ℕ) (χ : D.X) : Fin 4 ⊕ Fin 4 → (D.P.A.left ⟶ D.P.A.left) :=
  Sum.elim (D.famφB (m • χ)) (fun i => (mulA D.P.A m).left ≫ D.famφB χ i)

def mulεB (k k' : ℕ) : Fin 4 ⊕ Fin 4 → ℤ :=
  Sum.elim (DegPre.famε k') (fun i => - DegPre.famε k i)

def MulSecB (D : DegPre R) (m : ℕ) {k k' : ℕ} (χ : D.X) (b : D.SecB k χ) (b' : D.SecB k' (m • χ)) : Prop :=
  ∃ u : LB.Gen (LB.LinComb D.P.L (mulφB D m χ) (mulεB k k')), u.IsGen ∧
    LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (eSec D.P.A)) (GeneratorPullback.powGen D.P.L _ _ D.rig (k' - k)) ∧
    GeneratorPullback.SecRel D.P.L (D.famφB (m • χ)) (DegPre.famε k') b' (D.famφB χ) (DegPre.famε k) b (mulA D.P.A m).left
      (mulφB D m χ) (mulεB k k') u

def MulFam {I : Ideal R} {D : DegPre R} (m : ℕ) {k k' : ℕ} (F : IntFam I D k) (G : IntFam I D k') : Prop :=
  (∀ χ, MulSecB D m χ (F.f χ) (G.f (m • χ))) ∧ ∀ β : D.X, (∀ χ, β ≠ m • χ) → ∀ j, (G.f β).f j = 0

end

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {D : DegData R (maximalIdeal R)}

def MulSecK (C : LabCover D) (m : ℕ) {k k' : ℕ} (θ : SecK C.P.L.L C.α k) (S : SecK C.P.L.L C.α k') : Prop :=
  ∃ u : LB.Gen (LB.LinComb C.P.L.L (K := Fin 2) ![𝟙 C.G.left, (mulA C.G m).left] ![(k' : ℤ), -(k : ℤ)]), u.IsGen ∧
    ∀ (Z : Scheme.{0}) (p : Z ⟶ C.A.A.left) (z : Z) J, Good C.P.L.L z J →
      sval S p z J = (val u (p ≫ C.α) z J).val * sval θ (p ≫ (mulA C.A.A m).left) z J

end GlobalTheory.Mum
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.Poinc.Sep

theorem valPt_lies_over : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (i : F.X ⟶ Z) (W : Matrix (Fin 8) (Fin 8) ℤ) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V₁) (y : Sp (FractionRing V₁) ⟶ F.X), RegAt X₁ z₁ ev → jK V₁ ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁ ≫ X₁.π = y ≫ i → ∃ yK : X₁.S.R →+* FractionRing V₁, (∀ a, yK a = X₁.M.val (jK V₁ ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) a) ∧ spMap yK ≫ X₁.u = y := by
  intro g n F Z i W X₁ z₁ V₁ _ _ _ ev y hreg hy
  set yw := jK V₁ ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁ with hyw
  set w := yw (IsLocalRing.closedPoint (FractionRing V₁)) with hw
  have hle : X₁.S.R ≤ X₁.M.O w := fun a ha => hreg a ha
  have hsp : yw (IsLocalRing.closedPoint (FractionRing V₁)) ⤳ w := specializes_rfl
  let ψ : X₁.S.R →+* X₁.M.Z.presheaf.stalk w :=
    (X₁.M.stalkEquiv w).symm.toRingHom.comp (Subalgebra.inclusion hle).toRingHom
  let φ : X₁.M.Z.presheaf.stalk w →+* FractionRing V₁ := (X₁.M.Z.presheaf.stalkSpecializes hsp ≫
    Scheme.stalkClosedPointTo (R := CommRingCat.of (FractionRing V₁)) yw).hom
  refine ⟨(RatModel.valHom yw w (RatModel.range_eq_singleton yw _)).comp (Subalgebra.inclusion hle).toRingHom,
    fun a => rfl, ?_⟩
  have hK : (RatModel.valHom yw w (RatModel.range_eq_singleton yw _)).comp (Subalgebra.inclusion hle).toRingHom =
      φ.comp ψ :=
    RingHom.ext fun a => (RatModel.valLoc_eq_val yw hsp (Subalgebra.inclusion hle a)).symm
  haveI := X₁.imm
  haveI : IsProper X₁.z := X₁.isProper_compactificationMap
  haveI : Z.IsSeparated := by
    constructor
    rw [← terminal.comp_from X₁.z]
    infer_instance
  haveI : IsDominant (spMap (X₁.M.stalkHom w)) := by
    refine ⟨?_⟩
    change DenseRange (PrimeSpectrum.comap (X₁.M.stalkHom w))
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
      (RingHom.injective_iff_ker_eq_bot _).1 (X₁.M.stalkHom_injective w)]
    exact bot_le
  have hfs : ∀ {C : Type} [CommRing C] [IsLocalRing C] (q : Sp C ⟶ X₁.M.Z) (h : q (IsLocalRing.closedPoint C) ⤳ w),
      spMap (X₁.M.Z.presheaf.stalkSpecializes h ≫ Scheme.stalkClosedPointTo (R := CommRingCat.of C) q).hom ≫
        X₁.M.Z.fromSpecStalk w = q := by
    intro C _ _ q h
    simp only [spMap, CommRingCat.ofHom_hom, Spec.map_comp, Category.assoc,
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
    exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := CommRingCat.of C) q
  have e1 : spMap (X₁.M.stalkHom w) ≫ spMap ψ = spMap X₁.S.R.val.toRingHom := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext fun a => congrArg Subtype.val ((X₁.M.stalkEquiv w).apply_symm_apply (Subalgebra.inclusion hle a))
  have e2 : spMap (X₁.M.stalkHom w) ≫ X₁.M.Z.fromSpecStalk w = X₁.M.pt :=
    hfs X₁.M.pt (X₁.M.pt_specializes _ w)
  have hab : spMap ψ ≫ X₁.u ≫ i = X₁.M.Z.fromSpecStalk w ≫ X₁.π := by
    refine ext_of_isDominant (spMap (X₁.M.stalkHom w)) ?_
    rw [reassoc_of% e1, reassoc_of% e2, X₁.comp]
  have e3 : spMap φ ≫ X₁.M.Z.fromSpecStalk w = yw := hfs yw hsp
  rw [← cancel_mono i, Category.assoc, hK]
  change spMap (φ.comp ψ) ≫ X₁.u ≫ i = y ≫ i
  rw [show spMap (φ.comp ψ) = spMap φ ≫ spMap ψ by
    simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp], Category.assoc, hab, reassoc_of% e3, ← hy]
  simp only [hyw, Category.assoc]

end GlobalTheory.Poinc.Sep
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.CancelField

theorem isIso_jK {R : Type} [CommRing R] [IsDomain R] (hR : IsField R) : IsIso (jK R) := by
  have hb : Function.Bijective (algebraMap R (FractionRing R)) :=
    ⟨IsFractionRing.injective R (FractionRing R), IsFractionRing.surjective_iff_isField.2 hR⟩
  have : IsIso (CommRingCat.ofHom (algebraMap R (FractionRing R))) :=
    (ConcreteCategory.isIso_iff_bijective _).2 hb
  infer_instance

theorem isIso_gp {R : Type} [CommRing R] [IsDomain R] (M : Modif R) (hR : IsField R) : IsIso M.gp := by
  haveI := isIso_jK hR
  haveI := M.integral
  haveI := M.proper
  haveI := M.dominant
  haveI : IsClosedImmersion M.gp :=
    isClosedImmersion_of_comp_eq_id (M.π ≫ inv (jK R)) M.gp (by rw [← Category.assoc, M.gp_π, IsIso.hom_inv_id])
  haveI : Surjective M.gp := ⟨by
    have h1 := M.gp.isClosedEmbedding.isClosed_range
    have h2 := M.gp.denseRange
    exact Set.range_eq_univ.1 (h1.closure_eq ▸ h2.closure_range)⟩
  exact isIso_of_isClosedImmersion_of_surjective M.gp

theorem sval_comp {X Y₀ Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y₀ ⟶ X)} {ε : K → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) (p : Z ⟶ Y) (r : Y ⟶ Y₀) (z : Z) (J : (Z ⟶ X) → L.ι) (hJ : Good L z J) :
    sval s (p ≫ r) z J = (p.stalkMap z).hom (sval s r (p z) (fun ψ => J (p ≫ ψ))) := by
  have hJ' : Good L (p z) (fun ψ => J (p ≫ ψ)) := fun ψ => hJ (p ≫ ψ)
  rw [sval_of s (p ≫ r) z J (fun k => J (p ≫ r ≫ φ k)) (fun k => by rw [Category.assoc])]
  exact gs_comp p r z _ (hJ'.mem φ r) _

theorem scal_cancel {W : Type} [CommRing W] [IsDomain W] {Y : Scheme.{0}} (f : Y ⟶ Sp W) [Flat f] (y : Y) {b : W}
    (hb : b ≠ 0) {u v : Y.presheaf.stalk y}
    (h : gs (𝟙 Y) y ⊤ (scal f b) * u = gs (𝟙 Y) y ⊤ (scal f b) * v) : u = v := by
  set c : Γ(Sp W, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom b with hc
  have e1 : gs (𝟙 Y) y ⊤ (scal f b) = (f.stalkMap y).hom (gs (𝟙 (Sp W)) (f y) ⊤ c) := by
    have := gs_pull (𝟙 Y) f y ⊤ trivial c
    rw [Category.id_comp] at this
    refine this.trans ?_
    have := gs_comp f (𝟙 (Sp W)) y ⊤ trivial c
    rwa [Category.comp_id] at this
  have hc0 : c ≠ 0 := by
    intro h0
    apply hb
    have hi : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom :=
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of W)).inv).1
    exact hi (h0.trans (map_zero _).symm)
  have he0 : gs (𝟙 (Sp W)) (f y) ⊤ c ≠ 0 := by
    rw [gs_eq (𝟙 (Sp W)) (f y) ⊤ trivial]
    intro h0
    apply hc0
    have hi := germ_injective_of_isIntegral (Sp W) (U := (𝟙 (Sp W)) ⁻¹ᵁ ⊤) (f y) trivial
    have := hi (h0.trans (map_zero _).symm)
    exact this
  letI := (f.stalkMap y).hom.toAlgebra
  haveI : Module.Flat _ (Y.presheaf.stalk y) := Flat.stalkMap f y
  have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := Y.presheaf.stalk y) (mem_nonZeroDivisors_of_ne_zero he0)
  apply hreg
  simp only [Algebra.smul_def, RingHom.algebraMap_toAlgebra]
  rw [← e1]
  exact h

end GlobalTheory.Mum.CancelField

namespace GlobalTheory.Mum


open GlobalTheory.Mum.CancelField in
theorem cancel_field : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (k : ℕ) (σ : SecK C.P.L.L T.β k) (s : SecK C.P.L.L C.α k) (b : W) (c : FractionRing R), IsField R → b ≠ 0 → (∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ C.A.A.left), p ≫ T.β = p' ≫ C.α → ∀ z J, Good C.P.L.L z J → gs p z ⊤ (scal T.G.hom b) * sval σ p z J = gs p z ⊤ (scal T.G.hom b) * (gs p' z ⊤ (scal C.A.A.hom c) * sval s p' z J)) → ∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ C.A.A.left), p ≫ T.β = p' ≫ C.α → ∀ z J, Good C.P.L.L z J → sval σ p z J = gs p' z ⊤ (scal C.A.A.hom c) * sval s p' z J := by
  intro R _ _ _ _ D C W _ _ _ T k σ s b c hR hb H Z p p' hp z J hJ
  haveI : IsIso C.α := C.α_cart.1.isIso_fst_of_isIso (isIso_gp C.toModif hR)
  haveI : Smooth C.G.hom := C.semi.smooth
  haveI : Flat C.G.hom := inferInstance
  haveI : Flat T.G.hom := MorphismProperty.of_isPullback (P := @Flat) T.cart.1 inferInstance
  obtain ⟨q, hq⟩ : ∃ q : T.G.left ⟶ C.A.A.left, q ≫ C.α = T.β := ⟨T.β ≫ inv C.α, by simp⟩
  have key : ∀ y J', Good C.P.L.L y J' → sval σ (𝟙 _) y J' = gs q y ⊤ (scal C.A.A.hom c) * sval s q y J' := by
    intro y J' hJ'
    exact scal_cancel T.G.hom y hb (H _ (𝟙 _) q (by rw [hq, Category.id_comp]) y J' hJ')
  obtain rfl : p' = p ≫ q := (cancel_mono C.α).1 (by rw [Category.assoc, hq]; exact hp.symm)
  have hJ' : Good C.P.L.L (p z) (fun ψ => J (p ≫ ψ)) := fun ψ => hJ (p ≫ ψ)
  have e1 := sval_comp σ p (𝟙 _) z J hJ
  rw [Category.comp_id] at e1
  rw [e1, sval_comp s p q z J hJ, gs_comp p q z ⊤ trivial, ← map_mul, key (p z) _ hJ']

end GlobalTheory.Mum
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.TermLocus

theorem isUnit_sval_iff {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y) (z : Z) {J} (hJ : Good L z J) :
    IsUnit (sval s r z J) ↔ r z ∈ nonzeroLocus s := by
  have key : ∀ (U : Y.Opens) (_ : r z ∈ U) (f : Γ(Y, U)), IsUnit (gs r z U f) ↔ IsUnit (gs (𝟙 Y) (r z) U f) :=
    fun U h f => by rw [gs_stalkMap r z U h, isUnit_map_iff]
  refine ⟨fun h => (mem_nonzeroLocus s _).2 ⟨_, hJ.mem φ r, (key _ (hJ.mem φ r) _).1 h⟩, fun h => ?_⟩
  obtain ⟨j, hj, hu⟩ := (mem_nonzeroLocus s _).1 h
  rw [sval, sec_trans s r z (hJ.mem φ r) hj]
  exact (Units.isUnit _).mul ((key _ hj _).2 hu)

theorem nonzeroLocus_eq : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (Y : Ext D) (k : ℕ) (α : D.X) (b : D.SecB k α)
    (τ : SecK D.P.L Y.q.left k), IsTermOf Y b τ → nonzeroLocus τ = Y.q.left ⁻¹ᵁ nonzeroLocus b := by
  intro R _ _ D Y k α b τ h
  ext y
  choose J hJ using fun χ : Y.H.left ⟶ D.P.A.left => exists_chart D.P.isLB (χ y)
  have hJ' : Good D.P.L y J := hJ
  have e := h Y.H (𝟙 Y.H) y J hJ'
  rw [Over.id_left, Category.id_comp] at e
  change y ∈ nonzeroLocus τ ↔ Y.q.left y ∈ nonzeroLocus b
  refine (isUnit_sval_iff τ (𝟙 _) y hJ').symm.trans ?_
  rw [e, IsUnit.mul_iff, isUnit_sval_iff b _ y hJ']
  exact and_iff_left (Units.isUnit _)

end GlobalTheory.Mum.TermLocus
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Poinc.Sep

theorem isThetaTerms_of_mul_eq_one : ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] (D : DegPre V₁) (N₁ : ℕ) (X C : Type) [AddCommGroup X] (e : X ≃+ D.X) (T : X → C → V₁) (v : V₁) (c₀ : C), IsThetaTerms₀ D N₁ e T → T 0 c₀ * v = 1 → IsThetaTerms D N₁ e (fun mu c => T mu c * v) := by
  intro V₁ _ _ D N₁ X C _ e T v c₀ h hv
  obtain ⟨th, g, b, w, h₁, h₂, h₃, h₄, h₅⟩ := h
  refine ⟨(algebraMap V₁ (FractionRing V₁) v) • th, g, b, w, h₁, h₂, h₃, h₄, ?_, ⟨c₀, hv⟩⟩
  intro mu c z J hJ
  have H := h₅ mu c z J hJ
  rw [ReciprocityTheory.ChartRestriction.G.DVR.sval_smul _ _ _ _ z hJ]
  have e₁ : (lift (𝟙 (TF (R := V₁) (FractionRing V₁))) (g c).b).left ≫
      (fst (TF (R := V₁) (FractionRing V₁)) D.P.A).left = 𝟙 _ := by
    rw [← Over.comp_left, lift_fst, Over.id_left]
  rw [e₁]
  have e₂ : GlobalTheory.UT.cst (FractionRing V₁) z (algebraMap V₁ (FractionRing V₁) (T mu c * v)) =
      GlobalTheory.UT.cst (FractionRing V₁) z (algebraMap V₁ (FractionRing V₁) v) *
        GlobalTheory.UT.cst (FractionRing V₁) z (algebraMap V₁ (FractionRing V₁) (T mu c)) := by
    simp only [GlobalTheory.UT.cst, map_mul]
    rw [gs_mul _ z ⊤ trivial, mul_comm]
  rw [e₂, _root_.mul_assoc, H]
  simp only [GlobalTheory.UT.cst, _root_.mul_assoc]

end GlobalTheory.Poinc.Sep
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.USep

open GlobalTheory.Poinc.Sep

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {C : UCompact Xo c}

section

variable {A : Type} [CommRing A] [IsLocalRing A] (ζ : Sp A ⟶ pullback C.z (spMap C.b))
  (Φ : VPre (H.bar : 𝓞 E → 𝓞 E) (min Dw.p Dw.q) !![(1 : ℤ)] A)

def HasTraitsP : Prop :=
  ∀ (T : UTrait Xo c) (ev : A →+* T.V), IsLocalHom ev → jK T.V ≫ spMap ev ≫ ζ = T.y ≫ C.iF →
    ∃ (y : Φ.Y) (f : T.V →+* Φ.V y) (e : Φ.X y ≃ₗ[𝓞 E] T.P.D.toPre.X), Φ.m y = 1 ∧ IsPrincipalIdealRing (Φ.V y) ∧
      Function.Injective f ∧ IsLocalHom f ∧ f.comp ev = Φ.ev y ∧
      ∀ k, Φ.t y k ^ 2 = f T.ϖ ∧ ∀ a b, Φ.δ y k a b = T.be (e a) (e b)

def IsMemberP (N₁ : ℕ) {φ : InvFun (𝓞 E)} {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V]
    (Cm : GlobalTheory.UChart.MonoFam Xo c φ V) (ξ : Sp V ⟶ pullback C.z (spMap C.b)) (y : Φ.Y) (ρ : V →+* Φ.V y)
    (e : Φ.X y ≃ₗ[𝓞 E] Cm.P.D.toPre.X) (h : Fin (Φ.m y) ≃ Fin Cm.m) : Prop :=
  Function.Injective ρ ∧ ρ.Finite ∧ spMap (Φ.ev y) ≫ ζ = spMap ρ ≫ ξ ∧
    (∀ k, Φ.t y k ^ 2 = ρ (Cm.s (h k)) ∧ ∀ a b, Φ.δ y k a b = ((l.M' : ℤ) • Cm.δ (h k)) (e a) (e b)) ∧
    ∃ (D : DegPre (Φ.V y)) (p : IsPullDeg ρ Cm.P.D.toPre D),
      IsThetaTerms₀ D N₁ p.xe.symm fun mu c => Φ.term y (fun _ => e.symm mu) c

end

end GlobalTheory.USep
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem Trait.exists_fibre_iso : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F], (∀ r, algebraMap (FractionRing R) F (algebraMap R _ r) = algebraMap (FractionRing W) F (algebraMap W _ (T.φ r))) → ∃ f : (TFK (R := W) F ⊗ T.A.A).left ⟶ (TFK (R := R) F ⊗ C.A.A).left, IsIso f ∧ f ≫ (fst (TFK (R := R) F) C.A.A).left = (fst (TFK (R := W) F) T.A.A).left ∧ f ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α = (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β := by
  intro R _ _ _ _ D C W _ _ _ T F _ _ _ hF

  have hρ : Function.Injective ((algebraMap (FractionRing W) F).comp ((algebraMap W (FractionRing W)).comp T.φ)) :=
    (algebraMap (FractionRing W) F).injective.comp ((IsFractionRing.injective W (FractionRing W)).comp T.inj)
  obtain ⟨ga, hga, hy⟩ := Modif.factor_gp R C.toModif F _ (jFK (R := W) F ≫ jK W ≫ T.ξ) hρ (by
    rw [Category.assoc, Category.assoc, T.ξ_π]
    simp only [jK, jFK, spMap, ← Spec.map_comp]
    rfl)
  have hga' : ga = algebraMap (FractionRing R) F :=
    IsLocalization.ringHom_ext (nonZeroDivisors R) (RingHom.ext fun r => (hga r).trans (hF r).symm)
  subst hga'
  have hu : jFK (R := W) F ≫ jK W ≫ T.ξ = jFK (R := R) F ≫ C.gp := hy

  have s₁ : IsPullback (pullback.snd (jFK (R := W) F) T.A.A.hom) (pullback.fst (jFK (R := W) F) T.A.A.hom)
      T.A.A.hom (jFK (R := W) F) := (IsPullback.of_hasPullback _ _).flip
  haveI : IsIso T.U.gen.inv.left := ⟨⟨T.U.gen.hom.left, by rw [← Over.comp_left, T.U.gen.inv_hom_id, Over.id_left],
    by rw [← Over.comp_left, T.U.gen.hom_inv_id, Over.id_left]⟩⟩
  have s₂ : IsPullback T.U.gen.inv.left T.A.A.hom (pullback.snd T.G.hom (jK W)) (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id]; exact Over.w T.U.gen.inv⟩
  have s₃ : IsPullback (pullback.fst T.G.hom (jK W)) (pullback.snd T.G.hom (jK W)) T.G.hom (jK W) :=
    IsPullback.of_hasPullback _ _
  have hW : IsPullback ((pullback.snd (jFK (R := W) F) T.A.A.hom) ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β)
      (pullback.fst (jFK (R := W) F) T.A.A.hom) C.G.hom (jFK (R := R) F ≫ C.gp) := by
    have := ((s₁.paste_horiz s₂).paste_horiz s₃).paste_horiz T.cart.1
    rw [← hu]
    simpa only [Category.assoc, Category.id_comp, Category.comp_id] using this

  have t₁ : IsPullback (pullback.snd (jFK (R := R) F) C.A.A.hom) (pullback.fst (jFK (R := R) F) C.A.A.hom)
      C.A.A.hom (jFK (R := R) F) := (IsPullback.of_hasPullback _ _).flip
  have hR : IsPullback (pullback.snd (jFK (R := R) F) C.A.A.hom ≫ C.α) (pullback.fst (jFK (R := R) F) C.A.A.hom)
      C.G.hom (jFK (R := R) F ≫ C.gp) := t₁.paste_horiz C.α_cart.1
  refine ⟨(hW.isoIsPullback _ _ hR).hom, inferInstance, hW.isoIsPullback_hom_snd _ _ hR, ?_⟩
  exact hW.isoIsPullback_hom_fst _ _ hR

end GlobalTheory.Mum
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem scalar_pullback_spec_mul {A : Type} [CommRing A] {Y : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of A)) (x y : A) :
    scal p (x * y) = scal p x * scal p y := by
  unfold scal; rw [map_mul, map_mul]

theorem Trait.exp_mul_left : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R)) (C : LabCover D) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (k : ℕ) (s : SecK C.P.L.L C.α k) (F : IntFam (maximalIdeal R) D.toPre k) (a b c : W), T.Exp a b s F → T.Exp (c * a) (c * b) s F := by
  intro R _ _ _ D C W _ _ _ T k s F a b c ⟨σ, ⟨σ', f', hC, hP, hE⟩, hs⟩
  refine ⟨DVR.SecOps.secScale (scal T.G.hom c) σ, ⟨σ', f', ?_, hP, hE⟩, ?_⟩
  · intro Z r z J J' hJ hJ'
    rw [GlobalTheory.IntegralFamTriple.sval_secScale _ _ _ _ hJ, hC Z r z J J' hJ hJ', scalar_pullback_spec_mul, gs_mul _ z ⊤ trivial]
    ring
  · intro Z p p' hp z J hJ
    rw [GlobalTheory.IntegralFamTriple.sval_secScale _ _ _ _ hJ, hs Z p p' hp z J hJ, scalar_pullback_spec_mul, gs_mul _ z ⊤ trivial]
    ring

end GlobalTheory.Mum
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum


open GlobalTheory.TorusCoordPull in
theorem isPullPt_of_carries : ∀ {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {ρ : R →+* R'} {D : DegPre R} {I : Ideal R'} {E : DegData R' I} (hE : IsPullDeg ρ D E.toPre) {A' : PolAV (Sp (FractionRing R'))} {G' : Over (Sp R')} [GrpObj G'] [IsCommMonObj G'] (U : UnifPre I E A' G') (Y : Ext D) {e : ℕ} {φ : (thickObj R' I e G').left ⟶ Y.H.left}, GlobalTheory.FormalModel.Carries hE (U.gt e) (Y.Φ Y.H (𝟙 Y.H)) φ → ∀ (Z : Scheme.{0}) (g : Z ⟶ (thickObj R' I e G').left), ∃ ξ' : GtPt E.toPre (Over.mk (g ≫ (thickObj R' I e G').hom ≫ thick R' I e)), GlobalTheory.TorusCoord.IsPointOf (U.gt e) g ξ' ∧ IsPullPt hE (𝟙 Z) (Y.Φ (Over.mk ((g ≫ φ) ≫ Y.H.hom)) (Over.homMk (g ≫ φ) rfl)) ξ' := by
  intro R R' _ _ _ _ ρ D I E hE A' G' _ _ U Y e φ h Z g
  obtain ⟨ξ', hξ⟩ := GlobalTheory.TorusCoord.exists_isPointOf (U.gt e)
    (T := Over.mk (g ≫ (thickObj R' I e G').hom ≫ thick R' I e)) g rfl
  have hp := Y.rep.1 (Over.mk ((g ≫ φ) ≫ Y.H.hom)) Y.H (Over.homMk (g ≫ φ) rfl) (𝟙 Y.H)
  rw [Category.comp_id] at hp
  set Yξ := Y.Φ (Over.mk ((g ≫ φ) ≫ Y.H.hom)) (Over.homMk (g ≫ φ) rfl) with hYξ
  have hb : ξ'.b.left ≫ hE.e.hom.left ≫ pullback.fst D.P.A.hom (specOf ρ) = 𝟙 Z ≫ Yξ.b.left := by
    rw [hξ.1, Category.assoc, h.1, hp.1, Category.id_comp]
    rfl
  refine ⟨ξ', hξ, hb, fun χ => ?_⟩
  have hψ : ∀ κ : Fin 4, DegPre.gtφT E.toPre _ ξ'.b χ κ ≫ hE.e.hom.left ≫ pullback.fst D.P.A.hom (specOf ρ) =
      𝟙 Z ≫ DegPre.gtφT D _ Yξ.b (hE.xe χ) κ := fun κ => by
    rw [GlobalTheory.TorusCoord.gtφT_eq, GlobalTheory.TorusCoord.gtφT_eq]
    exact Oφ_pull hE Yξ.b ξ'.b (𝟙 Z) hb χ κ
  refine ⟨hψ, maps_of_good ((isGen_iff hE.w).1 hE.w_gen) D.P.isLB E.toPre.P.isLB (ξ'.s χ) (ξ'.isGen χ) _
    (Yξ.isGen _) hψ fun z J J' hJ hJ' => ?_⟩
  have o := (GlobalTheory.TorusCoord.comp_eq_of_left ξ'.b (U.gt e).pG (𝟙 Z) g (by rw [Category.id_comp]; exact hξ.1)).1 χ
  have r1 : val (Yξ.s (hE.xe χ)) (𝟙 Z) z J = val ((Y.Φ Y.H (𝟙 Y.H)).s (hE.xe χ)) (g ≫ φ) z J :=
    (val_corr hJ (hp.2 _) (𝟙 _)).trans ((val_pull hJ _ _ _).trans
      (congrArg (fun r => val ((Y.Φ Y.H (𝟙 Y.H)).s (hE.xe χ)) r z J) (Category.id_comp _)))
  have r3 : val (ξ'.s χ) (𝟙 Z) z J' = val ((U.gt e).t χ) g z J' :=
    (val_corr hJ' (hξ.2 χ) (𝟙 _)).trans ((val_pull hJ' _ _ _).trans
      (congrArg (fun r => val ((U.gt e).t χ) r z J') (Category.id_comp _)))
  refine r1.trans ((h.2 χ Z g z J J' hJ hJ').trans (congrArg₂ (· * ·) (Finset.prod_congr rfl fun k _ => ?_) r3.symm))
  have ok := o k
  rw [Category.id_comp] at ok
  rw [← ok]
  rfl

end GlobalTheory.Mum
end
end
