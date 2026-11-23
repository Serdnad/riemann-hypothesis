module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle940
public import Mathlib.Tactic.ENatToNat
public import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueZpowMulAppLE
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle987
public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle081
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Formalism.SharpRestriction.ParConsts
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OtherLossSum
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
import Development.AbelianVarietyTheory.PublishedTheorems.AbelianLaws.PrincipalPolarisationOneSection
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.Obs GlobalTheory.LBLift
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.LBLift

theorem appLE_comp_spMap_hom (R C : Type) [CommRing R] [CommRing C] (σ : R →+* C) (X : Scheme.{0})
    (s : X ⟶ Sp C) (U : X.Opens) :
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (s ≫ spMap σ).appLE ⊤ U le_top).hom =
      (algebraMap C (Sec s U)).comp σ := by
  ext r
  have k1 := congr($(Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom σ)).hom r)
  have k2 := congr($(Scheme.Hom.comp_appLE s (spMap σ) ⊤ U le_top).hom
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))
  refine k2.trans ?_
  exact (congrArg (s.appLE ⊤ U le_top).hom k1).symm

theorem isThick_of_isPullback_quotient : ∀ (R C : Type) [CommRing R] [CommRing C] (σ : R →+* C) (J : Ideal R),
    J ^ 2 = ⊥ → ∀ (X X₀ : Scheme.{0}) (s : X ⟶ Sp C) (s₀ : X₀ ⟶ Sp (R ⧸ J)) (i : X₀ ⟶ X),
    IsPullback i s₀ (s ≫ spMap σ) (spMap (Ideal.Quotient.mk J)) → IsThick (J.map σ) s i := by
  intro R C _ _ σ J hJ X X₀ s s₀ i h
  have hβ : Function.Surjective (CommRingCat.ofHom (Ideal.Quotient.mk J)).hom := Ideal.Quotient.mk_surjective
  have hpo : ∀ U : X.affineOpens, IsPushout
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (s ≫ spMap σ).appLE ⊤ U.1 le_top)
      (CommRingCat.ofHom (Ideal.Quotient.mk J)) (i.app U.1)
      ((Scheme.ΓSpecIso (CommRingCat.of (R ⧸ J))).inv ≫ s₀.appLE ⊤ (i ⁻¹ᵁ U.1) le_top) := by
    intro U
    have hpo := (isIso_pushoutSection_iff h (US := ⊤) (UT := ⊤) (UX := U.1) (UY := i ⁻¹ᵁ U.1) le_top
      le_top (by simp)).1 (isIso_pushoutSection_of_isAffineOpen h _ _ _ (isAffineOpen_top _)
        (isAffineOpen_top _) U.2)
    refine hpo.of_iso (Scheme.ΓSpecIso _) (Iso.refl _) (Scheme.ΓSpecIso _) (Iso.refl _)
      (by simp) ?_ (by simp [Scheme.Hom.appLE_eq_app]) (by simp)
    rw [← Scheme.ΓSpecIso_naturality]
    congr 1
  haveI := IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom (Ideal.Quotient.mk J))
    Ideal.Quotient.mk_surjective
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact MorphismProperty.of_isPullback (P := @IsClosedImmersion) h.flip inferInstance
  · exact LiftSys.surjective_of_isPullback_sqZero (I := J) (by rw [hJ]; rfl) Ideal.Quotient.mk_surjective
      (Ideal.mk_ker) h
  · intro U
    have P := hpo U
    have htop := CommRingCat.closure_range_union_range_eq_top_of_isPushout P
    rw [← RingHom.range_eq_top, ← top_le_iff, ← htop, Subring.closure_le]
    rintro _ (⟨y, rfl⟩ | ⟨z, rfl⟩)
    · exact ⟨y, rfl⟩
    · obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
      exact ⟨_, congr($(P.w).hom r)⟩
  · intro U b
    have hk := GlobalTheory.PrimeSection.ker_eq_map_of_isPushout (hpo U) hβ
    have hk' : RingHom.ker (CommRingCat.ofHom (Ideal.Quotient.mk J)).hom = J := Ideal.mk_ker
    rw [hk', appLE_comp_spMap_hom] at hk
    rw [Ideal.map_map]
    exact RingHom.mem_ker.symm.trans (by rw [hk]; exact Iff.rfl)

end GlobalTheory.LBLift
end
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.AbDual
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CechDR.FrobKill

variable (p : ℕ) [Fact p.Prime] {R : Type} [CommRing R] (hR : (p : R) = 0) {X : Scheme.{0}}
  {s : X ⟶ Sp R}

abbrev tU (s : X ⟶ Sp R) (U : AffOp X) : Thick (dp0 R) s :=
  Thick.triv (Sec s U.unop.1) (affPt s U.unop) (affPt_w s U.unop)


include hR in
theorem cast_sec (U : X.Opens) : (p : Sec s U) = 0 := by
  rw [← map_natCast (algebraMap R (Sec s U)), hR, map_zero]

abbrev resHom (s : X ⟶ Sp R) {U V : AffOp X} (a : U ⟶ V) : tU s U ⟶ tU s V :=
  Thick.trivHom (hx := affPt_w s U.unop) (T := tU s V) (Sec.res s (leOfHom a.unop))
    (affPt_res s (leOfHom a.unop))

variable {hX : (p : Γ(X, ⊤)) = 0}
  (h : IsMor (dp0 R) s (dp0 R) s (frobR p R hR) (GlobalTheory.VB.frob X p hX))

def eta (U : AffOp X) : tU s U ⟶ h.obj (tU s U) :=
  Thick.trivHom (hx := affPt_w s U.unop) (T := h.obj (tU s U))
    { frobR p (Sec s U.unop.1) (cast_sec p hR U.unop.1) with
      commutes' := fun r ↦ by
        show frobR p (Sec s U.unop.1) (cast_sec p hR U.unop.1) (algebraMap R (Sec s U.unop.1) r) = _
        rw [frobR_apply]
        change _ = algebraMap R (Sec s U.unop.1) (frobR p R hR r)
        rw [frobR_apply, map_pow] }
    (by
      have h0 : (p : Γ(Sp (Sec s U.unop.1), ⊤)) = 0 :=
        GlobalTheory.SS.FrobField.cast_zero_sp _ (cast_sec p hR U.unop.1)
      change spMap (frobR p (Sec s U.unop.1) (cast_sec p hR U.unop.1)) ≫ affPt s U.unop =
        affPt s U.unop ≫ GlobalTheory.VB.frob X p hX
      rw [← frob_sp p _ _ h0, GlobalTheory.VB.frob_naturality p hX _ h0])

theorem eta_φ (U : AffOp X) (b : Sec s U.unop.1) : (eta p hR h U).φ b = b ^ p :=
  frobR_apply p _ (cast_sec p hR U.unop.1) b

attribute [local instance] opModule isCentralScalar_kaehler isScalarTower_kaehler

theorem exists_closed_pow : ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (hR : (p : R) = 0) (X : Scheme.{0}) (s : X ⟶ Sp R) (hX : (p : Γ(X, ⊤)) = 0) (h : IsMor (dp0 R) s (dp0 R) s (frobR p R hR) (GlobalTheory.VB.frob X p hX)) (f : Z1 (O (dp0 R) s)), h.pull1 (GlobalTheory.CatCoh.H1.mk _ f) = 0 → ∃ u : ∀ U : GlobalTheory.CechDR.AffOp X, GlobalTheory.CechDR.Sec s U.unop.1, (∀ U, KaehlerDifferential.D R (GlobalTheory.CechDR.Sec s U.unop.1) (u U) = 0) ∧ ∀ (U V : GlobalTheory.CechDR.AffOp X) (a : U ⟶ V), (show GlobalTheory.CechDR.Sec s V.unop.1 from (GlobalTheory.CechDR.cmpZZ s f).1.1 U V a) ^ p = u V - GlobalTheory.CechDR.Sec.res s (leOfHom a.unop) (u U) := by
  intro p _ R _ hR X s hX h f hf
  obtain ⟨g, hg⟩ := H1.mk_eq_zero.1 hf
  have hg' : ∀ {T T' : Thick (dp0 R) s} (φ : T ⟶ T'), g T' - φ.φ (g T) = ev f (h.functor.map φ) :=
    fun {T T'} φ ↦ congrFun (congrFun (congrFun hg T) T') φ
  refine ⟨fun U ↦ (show Sec s U.unop.1 from g (tU s U)) - (show Sec s U.unop.1 from ev f (eta p hR h U)),
    fun U ↦ ?_, fun U V a ↦ ?_⟩
  · let p₁ := (diagExt R (Sec s U.unop.1)).secHom (affPt_w s U.unop) (diagExt R (Sec s U.unop.1)).i
      fun _ ↦ rfl
    let p₂ := (diagExt R (Sec s U.unop.1)).secHom (affPt_w s U.unop) (diagSec R (Sec s U.unop.1))
      (fst_derSec _)
    let P := (diagExt R (Sec s U.unop.1)).thick (affPt s U.unop) (affPt_w s U.unop)
    have e : eta p hR h U ≫ h.functor.map p₁ = eta p hR h U ≫ h.functor.map p₂ :=
      Thick.hom_ext fun b ↦ by
        change (diagExt R (Sec s U.unop.1)).i ((eta p hR h U).φ b) =
          diagSec R (Sec s U.unop.1) ((eta p hR h U).φ b)
        rw [eta_φ]
        ext
        · simp
        · rw [snd_derSec, Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul (Sec s U.unop.1),
            cast_sec p hR, zero_smul]
          simp
    have k := (ev_comp f (eta p hR h U) (h.functor.map p₁)).symm.trans
      ((congrArg (ev f) e).trans (ev_comp f (eta p hR h U) (h.functor.map p₂)))
    have k' : p₁.φ (show Sec s U.unop.1 from ev f (eta p hR h U)) +
        (show TrivSqZeroExt (Sec s U.unop.1) Ω[Sec s U.unop.1⁄R] from ev f (h.functor.map p₁)) =
        p₂.φ (show Sec s U.unop.1 from ev f (eta p hR h U)) +
        (show TrivSqZeroExt (Sec s U.unop.1) Ω[Sec s U.unop.1⁄R] from ev f (h.functor.map p₂)) := k
    have h1 : (show TrivSqZeroExt (Sec s U.unop.1) Ω[Sec s U.unop.1⁄R] from g P) -
        p₁.φ (show Sec s U.unop.1 from g (tU s U)) =
        (show TrivSqZeroExt (Sec s U.unop.1) Ω[Sec s U.unop.1⁄R] from ev f (h.functor.map p₁)) := hg' p₁
    have h2 : (show TrivSqZeroExt (Sec s U.unop.1) Ω[Sec s U.unop.1⁄R] from g P) -
        p₂.φ (show Sec s U.unop.1 from g (tU s U)) =
        (show TrivSqZeroExt (Sec s U.unop.1) Ω[Sec s U.unop.1⁄R] from ev f (h.functor.map p₂)) := hg' p₂
    have key : p₁.φ ((show Sec s U.unop.1 from g (tU s U)) - (show Sec s U.unop.1 from ev f (eta p hR h U))) =
        p₂.φ ((show Sec s U.unop.1 from g (tU s U)) - (show Sec s U.unop.1 from ev f (eta p hR h U))) := by
      rw [map_sub, map_sub]
      linear_combination -h1 + h2 - k'
    have l := congrArg (TrivSqZeroExt.snd (R := Sec s U.unop.1)) key
    change ((diagExt R (Sec s U.unop.1)).i _).snd = (diagSec R (Sec s U.unop.1) _).snd at l
    rw [snd_derSec] at l
    exact l.symm.trans (by simp)
  · have k := ev_sq f (eta p hR h U) (h.functor.map (resHom s a)) (resHom s a) (eta p hR h V)
      fun c ↦ by
        change Sec.res s (leOfHom a.unop) ((eta p hR h U).φ c) = (eta p hR h V).φ (Sec.res s (leOfHom a.unop) c)
        rw [eta_φ, eta_φ, map_pow]
    have k' : Sec.res s (leOfHom a.unop) (show Sec s U.unop.1 from ev f (eta p hR h U)) +
        (show Sec s V.unop.1 from ev f (h.functor.map (resHom s a))) =
        (ev f (resHom s a)) ^ p + (show Sec s V.unop.1 from ev f (eta p hR h V)) := by
      rw [← eta_φ p hR h V]; exact k
    have hg'' : (show Sec s V.unop.1 from g (tU s V)) - Sec.res s (leOfHom a.unop) (show Sec s U.unop.1 from g (tU s U)) =
        (show Sec s V.unop.1 from ev f (h.functor.map (resHom s a))) :=
      hg' (resHom s a)
    change (ev f (resHom s a)) ^ p = _
    rw [map_sub]
    linear_combination -hg'' - k'

end GlobalTheory.CechDR.FrobKill
end
end

section

open MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Ker

noncomputable section

namespace GlobalTheory.JetCharScale

variable {K : Type} [Field K]

def scaleVar {σ : Type} (u : σ → K) : MvPolynomial σ K →ₐ[K] MvPolynomial σ K := aeval fun v => C (u v) * X v

theorem scaleVar_monomial {σ : Type} (u : σ → K) (m : σ →₀ ℕ) (c : K) :
    scaleVar u (monomial m c) = (m.prod fun v e => u v ^ e) • monomial m c := by
  rw [scaleVar, aeval_monomial, smul_eq_C_mul, monomial_eq]
  simp only [mul_pow, Finsupp.prod, Finset.prod_mul_distrib, map_prod, map_pow, algebraMap_eq]
  ring

variable {ι : Type} {a b : ℕ}

theorem jetLin_monomial (J : (DVar ι a b →₀ ℕ) → K) (m : (ι × Fin b × Fin b) ⊕ DVar ι a b →₀ ℕ) :
    jetLin J (monomial m 1) = monomial (m.comapDomain Sum.inl Sum.inl_injective.injOn)
      (J (m.comapDomain Sum.inr Sum.inr_injective.injOn)) := by
  have := (basisMonomials ((ι × Fin b × Fin b) ⊕ DVar ι a b) K).constr_basis K (fun m =>
    (monomial (m.comapDomain Sum.inl Sum.inl_injective.injOn) (J (m.comapDomain Sum.inr Sum.inr_injective.injOn)) : Pol K ι b)) m
  rw [coe_basisMonomials] at this
  exact this

theorem subD_scale (w : ι → K) (P : Pol K ι a) :
    scaleVar (Sum.elim (fun _ => 1) fun k => w k.1) (subD K ι a b P) =
      scaleVar (Sum.elim (fun v => w v.1) fun _ => 1) (subD K ι a b P) := by
  refine AlgHom.congr_fun (φ₁ := (scaleVar _).comp (subD K ι a b)) (φ₂ := (scaleVar _).comp (subD K ι a b))
    (MvPolynomial.algHom_ext fun v => ?_) P
  simp only [AlgHom.comp_apply, subD, aeval_X]
  split_ifs with h
  · set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, scaleVar, aeval_X, Sum.elim_inl, Sum.elim_inr, map_one]
    refine Finset.sum_congr rfl fun β _ => ?_
    ring
  · simp

variable [Fintype ι]

theorem jetLin_right (J : (DVar ι a b →₀ ℕ) → K) (w : ι → K) (c : K)
    (Q : MvPolynomial ((ι × Fin b × Fin b) ⊕ DVar ι a b) K) :
    jetLin (fun m => c * ((m.prod fun v e => w v.1 ^ e) * J m)) Q =
      c • jetLin J (scaleVar (Sum.elim (fun _ => 1) fun k => w k.1) Q) := by
  refine LinearMap.congr_fun (g := c • (jetLin J ∘ₗ (scaleVar (Sum.elim (fun _ => 1) fun k => w k.1)).toLinearMap))
    ((basisMonomials _ K).ext fun m => ?_) Q
  rw [coe_basisMonomials]
  simp only [LinearMap.smul_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply]
  rw [scaleVar_monomial, map_smul, jetLin_monomial, jetLin_monomial, smul_monomial, smul_monomial, smul_eq_mul, smul_eq_mul,
    Finsupp.prod_fintype _ _ (by simp), Finsupp.prod_fintype _ _ (by simp), Fintype.prod_sum_type]
  simp

theorem jetLin_left (J : (DVar ι a b →₀ ℕ) → K) (w : ι → K)
    (Q : MvPolynomial ((ι × Fin b × Fin b) ⊕ DVar ι a b) K) :
    jetLin J (scaleVar (Sum.elim (fun v => w v.1) fun _ => 1) Q) = scaleVar (fun v => w v.1) (jetLin J Q) := by
  induction Q using MvPolynomial.induction_on' with
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | monomial m c =>
    have e : (monomial m c : MvPolynomial _ K) = c • monomial m 1 := by rw [smul_monomial, smul_eq_mul, mul_one]
    rw [e, map_smul, map_smul, map_smul, map_smul, scaleVar_monomial, map_smul, jetLin_monomial, scaleVar_monomial,
      Finsupp.prod_fintype _ _ (by simp), Finsupp.prod_fintype _ _ (by simp), Fintype.prod_sum_type]
    simp

theorem jetMap_scale (J : (DVar ι a b →₀ ℕ) → K) (w : ι → K) (c : K) (n : ι → ℕ) (P : Pol K ι a) :
    jetMap (fun m => c * ((m.prod fun v e => w v.1 ^ e) * J m)) n P = c • scaleVar (fun v => w v.1) (jetMap J n P) := by
  simp only [jetMap, LinearMap.comp_apply, AlgHom.toLinearMap_apply]
  rw [jetLin_right, subD_scale, jetLin_left]

theorem scaleVar_hom [DecidableEq ι] (w : ι → K) (d : ι → ℕ) {Q : Pol K ι b}
    (hQ : ∀ τ, IsWeightedHomogeneous (GlobalTheory.JetDeg.posW b τ) Q (d τ)) :
    scaleVar (fun v => w v.1) Q = (∏ τ, w τ ^ d τ) • Q := by
  conv_lhs => rw [Q.as_sum]
  conv_rhs => rw [Q.as_sum]

  rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [scaleVar_monomial, Finsupp.prod_fintype _ _ (by simp), Fintype.prod_prod_type]
  congr 1
  refine Finset.prod_congr rfl fun τ _ => ?_
  have h := hQ τ (mem_support_iff.mp hm)
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Fintype.sum_prod_type, Finset.sum_eq_single τ] at h
  · rw [← h]
    simp [GlobalTheory.JetDeg.posW, Finset.prod_pow_eq_pow_sum]
  · intro x _ hx
    simp [GlobalTheory.JetDeg.posW, hx]
  · simp

theorem jetOp_scale : ∀ {ι : Type} [Fintype ι] {a b : ℕ} (lam : ι → DomWeight a) (lam' : ι → DomWeight b) (n : ι → ℕ)
    (J : (Formalism.L2.Ker.DVar ι a b →₀ ℕ) → ℂ) (w : ι → ℂ) (c : ℂ), Formalism.L2.Ker.JetInVV ℂ lam lam' n →
    Formalism.L2.Ker.jetOp lam lam' (fun m => c * ((m.prod fun v e => w v.1 ^ e) * J m)) n =
      (c * ∏ τ, w τ ^ (∑ i, (lam' τ).natW i)) • Formalism.L2.Ker.jetOp lam lam' J n := by
  classical
  intro ι _ a b lam lam' n J w c hV
  refine LinearMap.ext fun P => ?_
  simp only [jetOp, LinearMap.smul_apply, LinearMap.comp_apply, Submodule.subtype_apply]
  rw [jetMap_scale, scaleVar_hom w _ fun τ => GlobalTheory.JetDeg.VV_hom lam' τ (hV J P P.2), smul_smul, map_smul]

end GlobalTheory.JetCharScale

end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CechPic

open TopologicalSpace

theorem exists_units_of_gen_restrict {Z : Scheme.{0}} (L : LB Z) (O : Z.Opens) (t : LB.Gen (L.pull O.ι))
    (ht : t.IsGen) : ∃ b : ∀ i, Γ(Z, L.U i ⊓ O)ˣ, ∀ (i j : L.ι) (x : Z), x ∈ L.U i → x ∈ L.U j → x ∈ O →
      gm (𝟙 Z) x (L.U i ⊓ O) (b i) = gm (𝟙 Z) x (L.U i ⊓ L.U j) (L.g i j) * gm (𝟙 Z) x (L.U j ⊓ O) (b j) := by
  choose c hc using fun i : L.ι => exists_ext_unit O.ι ((L.pull O.ι).U (fun _ => i)) (t.s (fun _ => i))
  have le : ∀ i, L.U i ⊓ O ≤ O.ι ''ᵁ ((L.pull O.ι).U (fun _ => i)) := by
    intro i x hx
    have m : (⟨x, hx.2⟩ : O.toScheme) ∈ (L.pull O.ι).U (fun _ => i) := mem_pull.2 hx.1
    exact ⟨⟨x, hx.2⟩, m, rfl⟩
  refine ⟨fun i => res (le i) (c i), fun i j x hi hj hx => ?_⟩
  let z : O.toScheme := ⟨x, hx⟩
  have mi : z ∈ (L.pull O.ι).U (fun _ => i) := mem_pull.2 hi
  have mj : z ∈ (L.pull O.ι).U (fun _ => j) := mem_pull.2 hj
  have hW : O.ι z ∈ L.U i ⊓ L.U j ⊓ O := ⟨⟨hi, hj⟩, hx⟩
  have hWi : O.ι z ∈ L.U i ⊓ O := ⟨hi, hx⟩
  have hWj : O.ι z ∈ L.U j ⊓ O := ⟨hj, hx⟩
  have hWij : O.ι z ∈ L.U i ⊓ L.U j := ⟨hi, hj⟩
  have l₁ : L.U i ⊓ L.U j ⊓ O ≤ L.U i ⊓ L.U j := inf_le_left
  have l₂ : L.U i ⊓ L.U j ⊓ O ≤ L.U j ⊓ O := le_inf (inf_le_left.trans inf_le_right) inf_le_right
  have key := gm_inj O.ι z (U := L.U i ⊓ O) (U' := L.U i ⊓ L.U j ⊓ O) hWi hW
    (a := res (le i) (c i)) (b := res l₁ (L.g i j) * res l₂ (res (le j) (c j))) (by
      rw [map_mul, gm_res O.ι z l₁ hW, gm_res O.ι z l₂ hW, gm_res O.ι z (le j) hWj, gm_res O.ι z (le i) hWi]
      have e₁ := hc i O.toScheme (𝟙 _) z mi
      have e₂ := hc j O.toScheme (𝟙 _) z mj
      rw [Category.id_comp] at e₁ e₂
      rw [e₁, e₂, (isGen_iff_germ t).1 ht z _ _ mi mj, gm_pull_g L O.ι (𝟙 _) z _ _ mi mj, Category.id_comp])
  rw [map_mul, gm_res (𝟙 Z) (O.ι z) l₁ hW, gm_res (𝟙 Z) (O.ι z) l₂ hW] at key
  exact key

theorem eq_zero_of_pull_eq_zero_of_units_split : ∀ (Z : Scheme.{0}) (O O' : Z.Opens), O ⊔ O' = ⊤ →
    (∀ F : Γ(Z, O ⊓ O')ˣ, ∃ (u : Γ(Z, O)ˣ) (u' : Γ(Z, O')ˣ),
      F = res (inf_le_left : O ⊓ O' ≤ O) u * res (inf_le_right : O ⊓ O' ≤ O') u') →
    ∀ c : Pic Z, GlobalTheory.CechPic.pull O.ι c = 0 → GlobalTheory.CechPic.pull O'.ι c = 0 → c = 0 := by
  intro Z O O' hcov hsplit c hc hc'
  obtain ⟨L, hL, rfl⟩ := cls_surj c
  rw [← cls_pull hL O.ι (pull_isLB hL O.ι)] at hc
  rw [← cls_pull hL O'.ι (pull_isLB hL O'.ι)] at hc'
  obtain ⟨t, ht⟩ := (cls_eq_zero_iff _).1 hc
  obtain ⟨t', ht'⟩ := (cls_eq_zero_iff _).1 hc'
  obtain ⟨b, hb⟩ := exists_units_of_gen_restrict L O t ht
  obtain ⟨b', hb'⟩ := exists_units_of_gen_restrict L O' t' ht'
  have key₁ : ∀ {G : Type} [CommGroup G] (a x y : G), a * x * (a * y)⁻¹ = x * y⁻¹ := fun a x y => by
    rw [← div_eq_mul_inv, ← div_eq_mul_inv, mul_div_mul_left_eq_div]
  have key₂ : ∀ {G : Type} [CommGroup G] (a x y : G), a * x * y * x⁻¹ = a * y := fun a x y => by
    rw [mul_right_comm, mul_inv_cancel_right]

  let W : L.ι → Z.Opens := fun i => L.U i ⊓ (O ⊓ O')
  have lw : ∀ i, W i ≤ L.U i ⊓ O := fun i => inf_le_inf_left _ inf_le_left
  have lw' : ∀ i, W i ≤ L.U i ⊓ O' := fun i => inf_le_inf_left _ inf_le_right
  let q : ∀ i, Γ(Z, W i)ˣ := fun i => res (lw i) (b i) * (res (lw' i) (b' i))⁻¹
  have gq : ∀ i x, x ∈ W i → gm (𝟙 Z) x (W i) (q i) =
      gm (𝟙 Z) x (L.U i ⊓ O) (b i) * (gm (𝟙 Z) x (L.U i ⊓ O') (b' i))⁻¹ := fun i x hx => by
    simp only [q, map_mul, map_inv, gm_res (𝟙 Z) x (lw i) hx, gm_res (𝟙 Z) x (lw' i) hx]
  obtain ⟨F, hF⟩ := glue_unit (O ⊓ O') W (fun i => inf_le_right) (fun x hx => by
      obtain ⟨i, hi⟩ := exists_chart hL x
      exact Opens.mem_iSup.2 ⟨i, hi, hx⟩) q (fun i j x hx => by
      rw [gq i x hx.1, gq j x hx.2, hb i j x hx.1.1 hx.2.1 hx.1.2.1, hb' i j x hx.1.1 hx.2.1 hx.1.2.2, key₁])
  obtain ⟨u, u', hu⟩ := hsplit F

  have gF : ∀ i x, x ∈ W i → gm (𝟙 Z) x (L.U i ⊓ O) (b i) =
      gm (𝟙 Z) x (L.U i ⊓ O') (b' i) * gm (𝟙 Z) x O u * gm (𝟙 Z) x O' u' := fun i x hx => by
    have e := congrArg (gm (𝟙 Z) x (W i)) (hF i)
    rw [gm_res (𝟙 Z) x _ hx, gq i x hx, hu, map_mul, gm_res (𝟙 Z) x _ hx.2, gm_res (𝟙 Z) x _ hx.2] at e
    rw [(mul_inv_eq_iff_eq_mul).1 e.symm]
    ac_rfl

  have loc : ∀ i, ∃ s : Γ(Z, L.U i)ˣ,
      (∀ y, y ∈ L.U i → y ∈ O → gm (𝟙 Z) y (L.U i) s = gm (𝟙 Z) y (L.U i ⊓ O) (b i) * (gm (𝟙 Z) y O u)⁻¹) ∧
      (∀ y, y ∈ L.U i → y ∈ O' → gm (𝟙 Z) y (L.U i) s = gm (𝟙 Z) y (L.U i ⊓ O') (b' i) * gm (𝟙 Z) y O' u') := by
    intro i
    let V : Bool → Z.Opens := fun β => Bool.rec (L.U i ⊓ O') (L.U i ⊓ O) β
    let v : ∀ β, Γ(Z, V β)ˣ := fun β => Bool.rec (motive := fun β => Γ(Z, V β)ˣ)
      (b' i * res (inf_le_right : L.U i ⊓ O' ≤ O') u') (b i * (res (inf_le_right : L.U i ⊓ O ≤ O) u)⁻¹) β
    have hV : ∀ β, V β ≤ L.U i := fun β => by cases β <;> exact inf_le_left
    have g₁ : ∀ y, y ∈ L.U i ⊓ O → gm (𝟙 Z) y (V true) (v true) =
        gm (𝟙 Z) y (L.U i ⊓ O) (b i) * (gm (𝟙 Z) y O u)⁻¹ := fun y hy => by
      show gm (𝟙 Z) y (L.U i ⊓ O) (b i * (res (inf_le_right : L.U i ⊓ O ≤ O) u)⁻¹) = _
      rw [map_mul, map_inv, gm_res (𝟙 Z) y _ hy]
    have g₀ : ∀ y, y ∈ L.U i ⊓ O' → gm (𝟙 Z) y (V false) (v false) =
        gm (𝟙 Z) y (L.U i ⊓ O') (b' i) * gm (𝟙 Z) y O' u' := fun y hy => by
      show gm (𝟙 Z) y (L.U i ⊓ O') (b' i * res (inf_le_right : L.U i ⊓ O' ≤ O') u') = _
      rw [map_mul, gm_res (𝟙 Z) y _ hy]
    obtain ⟨s, hs⟩ := glue_unit (L.U i) V hV (fun y hy => by
        have h : y ∈ O ⊔ O' := hcov ▸ (trivial : y ∈ (⊤ : Z.Opens))
        rcases Opens.mem_sup.1 h with h | h
        · exact Opens.mem_iSup.2 ⟨true, hy, h⟩
        · exact Opens.mem_iSup.2 ⟨false, hy, h⟩) v (fun β β₂ y hy => by
        cases β <;> cases β₂
        · rfl
        · rw [g₀ y hy.1, g₁ y hy.2, gF i y ⟨hy.1.1, hy.2.2, hy.1.2⟩, key₂]
        · rw [g₁ y hy.1, g₀ y hy.2, gF i y ⟨hy.1.1, hy.1.2, hy.2.2⟩, key₂]
        · rfl)
    refine ⟨s, fun y hi ho => ?_, fun y hi ho => ?_⟩
    · have e := congrArg (gm (𝟙 Z) y (V true)) (hs true)
      rw [gm_res (𝟙 Z) y (hV true) (show y ∈ L.U i ⊓ O from ⟨hi, ho⟩)] at e
      exact e.trans (g₁ y ⟨hi, ho⟩)
    · have e := congrArg (gm (𝟙 Z) y (V false)) (hs false)
      rw [gm_res (𝟙 Z) y (hV false) (show y ∈ L.U i ⊓ O' from ⟨hi, ho⟩)] at e
      exact e.trans (g₀ y ⟨hi, ho⟩)
  choose s hs using loc
  refine (cls_eq_zero_iff hL).2 ⟨⟨s⟩, (isGen_iff_germ _).2 fun y i j hi hj => ?_⟩
  have h : y ∈ O ⊔ O' := hcov ▸ (trivial : y ∈ (⊤ : Z.Opens))
  rcases Opens.mem_sup.1 h with h | h
  · show gm (𝟙 Z) y (L.U i) (s i) = _ * gm (𝟙 Z) y (L.U j) (s j)
    rw [(hs i).1 y hi h, (hs j).1 y hj h, hb i j y hi hj h, _root_.mul_assoc]
  · show gm (𝟙 Z) y (L.U i) (s i) = _ * gm (𝟙 Z) y (L.U j) (s j)
    rw [(hs i).2 y hi h, (hs j).2 y hj h, hb' i j y hi hj h, _root_.mul_assoc]

end GlobalTheory.CechPic
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions NumberField Classical

namespace GlobalTheory.OtherLoss

theorem inertLoss_primeSum : ∀ {eps : ℝ} (Fm : FamP eps), 0 < eps → eps < 1 / 52 → ∃ C x0 : ℝ, 0 ≤ C ∧ ∀ x, x0 ≤ x → ∀ hx : Fm.x1 < x, ∀ i : Fm.Ix x, ∀ j ∈ SizeData₂.lifts (Fm.D x i), ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime ∧ (G.IsResidueClassZero (Fm.D x i) p ∨ G.IsSg (Fm.D x i) p) ∧ (p : ℝ) ≤ (Fm.L x i).sc.X'' (Fm.D x i).R.n ∧ ¬ (G.IsResidueClassZero (Fm.D x i) p ∧ G.hP (Fm.D x i) p = 0)) → ∑ p ∈ P, 2 * Real.log (p : ℝ) * |EatI (Fm.L x i) Fm.GK Fm.cX.err j p| ≤ C * (Fm.L x i).B0 := by
  intro eps Fm _ _
  refine ⟨848, 0, by norm_num, fun x _ hx i j hj P hP => ?_⟩
  have h := sum_eatI (K := Fm.GK) (c := Fm.cX.err) (Fm.sizes x hx i) Fm.fixed.2.1 Fm.fixed.2.2.1 Fm.fixed.2.2.2.2.1 hj P
    (fun p hp => ⟨(hP p hp).1, (hP p hp).2.2.1⟩)
  calc _ = 2 * ∑ p ∈ P, |EatI (Fm.L x i) Fm.GK Fm.cX.err j p| * Real.log (p : ℝ) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun p _ => by ring
    _ ≤ _ := by linarith

end GlobalTheory.OtherLoss
end
