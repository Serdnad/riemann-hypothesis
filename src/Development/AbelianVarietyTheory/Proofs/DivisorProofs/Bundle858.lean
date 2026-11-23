module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle236
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle239
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqZeroOfCobOneEqZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
public import Development.AbelianVarietyTheory.Definitions.Divisors.GlRes
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousConjFin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle829
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CasKOp

@[expose] public section

section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CechDR KaehlerDifferential
attribute [local instance] GlobalTheory.Cris.opModule GlobalTheory.Cris.isCentralScalar_kaehler GlobalTheory.Cris.isScalarTower_kaehler

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.TanVanish

variable {R : Type} [CommRing R] {X : Scheme.{0}} {s : X ⟶ Sp R}

theorem snd_val_affine {R' : Type} [CommRing R'] [Algebra R R'] (U : X.affineOpens)
    (α : Sec s U.1 →ₐ[R] TrivSqZeroExt R' R') (y : Sp (TrivSqZeroExt R' R') ⟶ X)
    (hy : y ≫ s = spMap (algebraMap R (TrivSqZeroExt R' R')))
    (e : spMap (α : Sec s U.1 →+* TrivSqZeroExt R' R') ≫ affPt s U = y) (f : Form s)
    (h0 : connForm f.1 (affPt s U) (affPt_w s U) = 0) :
    TrivSqZeroExt.snd ((SqExt.ofModule R R' R').val y hy f.1) = 0 := by
  have hx := affPt_w s U
  letI : Algebra (Sec s U.1) R' := ((TrivSqZeroExt.fstHom R R' R').comp α).toRingHom.toAlgebra
  haveI : IsScalarTower R (Sec s U.1) R' := IsScalarTower.of_algebraMap_eq fun r ↦
    (congrArg TrivSqZeroExt.fst (α.commutes r)).symm
  let δ : Derivation R (Sec s U.1) R' :=
    { toFun := fun b ↦ (α b).snd
      map_add' := fun a b ↦ by simp
      map_smul' := fun r b ↦ by
        simp [Algebra.smul_def, TrivSqZeroExt.algebraMap_eq_inl']
      map_one_eq_zero' := by simp
      leibniz' := fun a b ↦ by
        simp only [map_mul, TrivSqZeroExt.snd_mul, smul_eq_mul, Algebra.smul_def,
          RingHom.algebraMap_toAlgebra]
        simp [MulOpposite.smul_eq_mul_unop]
        ring }
  let δ' := δ.liftKaehlerDifferential
  have hop : ∀ (b : Sec s U.1) (ω : Ω[Sec s U.1⁄R]), MulOpposite.op b • ω = b • ω := fun _ _ ↦ rfl
  let Φ : TrivSqZeroExt (Sec s U.1) Ω[Sec s U.1⁄R] →ₐ[R] TrivSqZeroExt R' R' :=
    { toFun := fun c ↦ TrivSqZeroExt.inl (algebraMap (Sec s U.1) R' c.fst) +
        TrivSqZeroExt.inr (δ' c.snd)
      map_one' := by ext <;> simp
      map_zero' := by ext <;> simp
      map_add' := fun a b ↦ by ext <;> simp <;> ring
      map_mul' := fun a b ↦ by
        ext
        · simp
        · simp only [TrivSqZeroExt.snd_mul, hop, map_add (f := _), map_smul, TrivSqZeroExt.snd_add,
            TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, TrivSqZeroExt.fst_add,
            TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, smul_eq_mul, Algebra.smul_def]
          simp [MulOpposite.smul_eq_mul_unop]
          ring
      commutes' := fun r ↦ by
        ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl', ← IsScalarTower.algebraMap_apply] }
  let α₀ : Sec s U.1 →ₐ[R] R' := (TrivSqZeroExt.fstHom R R' R').comp α
  have hπ : ∀ c, α₀ ((diagExt R (Sec s U.1)).π c) = (SqExt.ofModule R R' R').π (Φ c) := fun c ↦ by
    simp [Φ, α₀, RingHom.algebraMap_toAlgebra]
  have e₀ : spMap (α₀ : Sec s U.1 →+* R') ≫ affPt s U =
      spMap ((SqExt.ofModule R R' R').π : TrivSqZeroExt R' R' →+* R') ≫ y := by
    rw [← e, ← Category.assoc, ← Cris.spMap_comp]; rfl
  let Ψ := (diagExt R (Sec s U.1)).thickHom (SqExt.ofModule R R' R') Φ α₀ hπ hx
    ((SqExt.ofModule R R' R').red_w hy) e₀
  let a1 : Thick.triv (Sec s U.1) (affPt s U) hx ⟶
      Thick.triv R' _ ((SqExt.ofModule R R' R').red_w hy) := Thick.trivHom α₀ e₀
  let a2 : Thick.triv (Sec s U.1) (affPt s U) hx ⟶ Thick.triv (TrivSqZeroExt R' R') y hy :=
    Thick.trivHom α e
  have k1 := Form.ev_sq f a1 ((SqExt.ofModule R R' R').secHom ((SqExt.ofModule R R' R').red_w hy)
    (SqExt.ofModule R R' R').i (SqExt.ofModule R R' R').π_i)
    ((diagExt R (Sec s U.1)).secHom hx (diagExt R (Sec s U.1)).i fun _ ↦ rfl) Ψ rfl rfl fun c ↦ by
      change TrivSqZeroExt.inl (α₀ c) = Φ (TrivSqZeroExt.inl c)
      ext <;> simp [Φ, α₀, RingHom.algebraMap_toAlgebra]
  have k2 := Form.ev_sq f a2 ((SqExt.ofModule R R' R').idHom hy)
    ((diagExt R (Sec s U.1)).secHom hx (diagSec R (Sec s U.1)) (fst_derSec _)) Ψ rfl rfl fun c ↦ by
      change α c = Φ (diagSec R (Sec s U.1) c)
      ext
      · simp [Φ, RingHom.algebraMap_toAlgebra]
      · simp only [Φ, AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
          TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add, snd_derSec]
        exact (Derivation.liftKaehlerDifferential_comp_D δ c).symm
  have hΦ : ∀ z, TrivSqZeroExt.snd (Φ z) = δ' z.snd := fun z ↦ by simp [Φ]
  rw [SqExt.val_apply, k1, k2, add_sub_add_right_eq_sub]
  change TrivSqZeroExt.snd (Φ _ - Φ _) = 0
  rw [← map_sub, hΦ]
  have h0' : TrivSqZeroExt.snd (ev f.1 ((diagExt R (Sec s U.1)).secHom hx (diagExt R (Sec s U.1)).i
      fun _ ↦ rfl) - ev f.1 ((diagExt R (Sec s U.1)).secHom hx (diagSec R (Sec s U.1))
      (fst_derSec _))) = 0 := h0
  rw [h0', map_zero]

theorem snd_val_eq_zero (y : Sp (DualNumber R) ⟶ X)
    (hy : y ≫ s = spMap (algebraMap R (DualNumber R))) (f : Form s)
    (h0 : ∀ U : X.affineOpens, connForm f.1 (affPt s U) (affPt_w s U) = 0) :
    TrivSqZeroExt.snd (R := R) ((SqExt.dual R).val y hy f.1) = 0 := by
  have loc : ∀ m : Ideal R, m.IsMaximal →
      ∃ t ∉ m, t * TrivSqZeroExt.snd (R := R) ((SqExt.dual R).val y hy f.1) = 0 := by
    intro m hm
    haveI := hm.isPrime
    let R' := Localization.AtPrime m
    haveI : IsLocalRing (TrivSqZeroExt R' R') :=
      IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun c ↦ by
        simp only [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_one]
        exact IsLocalRing.isUnit_or_isUnit_one_sub_self c.fst
    let φ : DualNumber R →ₐ[R] TrivSqZeroExt R' R' :=
      { toFun := fun c ↦ TrivSqZeroExt.inl (algebraMap R R' c.fst) +
          TrivSqZeroExt.inr (algebraMap R R' c.snd)
        map_one' := by ext <;> simp
        map_zero' := by ext <;> simp
        map_add' := fun a b ↦ by ext <;> simp [Algebra.smul_def] <;> ring
        map_mul' := fun a b ↦ by ext <;> simp [MulOpposite.smul_eq_mul_unop, Algebra.smul_def, TrivSqZeroExt.algebraMap_eq_inl'] <;> ring
        commutes' := fun r ↦ by ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl'] }
    let y' := spMap (φ : DualNumber R →+* TrivSqZeroExt R' R') ≫ y
    have hy' : y' ≫ s = spMap (algebraMap R (TrivSqZeroExt R' R')) := by
      change (spMap (φ : DualNumber R →+* TrivSqZeroExt R' R') ≫ y) ≫ s = _
      rw [Category.assoc, hy, ← Cris.spMap_comp, φ.comp_algebraMap]
    have hv := (SqExt.dual R).val_map (SqExt.ofModule R R' R') φ (Algebra.ofId R R')
      (fun c ↦ by simp [φ]) (fun b ↦ by ext <;> simp [φ, TrivSqZeroExt.algebraMap_eq_inl']) y hy y' hy' rfl f
    obtain ⟨U, hU, hp, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤)
      (x := y' (IsLocalRing.closedPoint (TrivSqZeroExt R' R'))) trivial
    have htop := Scheme.preimage_eq_top_of_closedPoint_mem y' hp
    let α₁ : Sec s U →+* TrivSqZeroExt R' R' := evalAt y' U htop.ge
    have hα : spMap α₁ ≫ affPt s ⟨U, hU⟩ = y' := by
      have k := IsAffineOpen.SpecMap_appLE_fromSpec y' hU (isAffineOpen_top _) htop.ge
      rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at k
      have e1 : spMap α₁ ≫ affPt s ⟨U, hU⟩ =
          Spec.map ((Scheme.ΓSpecIso (CommRingCat.of (TrivSqZeroExt R' R'))).hom) ≫
          Spec.map (y'.appLE U ⊤ htop.ge) ≫ hU.fromSpec := by
        rw [← Category.assoc, ← Spec.map_comp]; rfl
      rw [e1]
      rw [k]
      simp only [← Category.assoc, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id, Category.id_comp]
    have hc : α₁.comp (algebraMap R (Sec s U)) = algebraMap R (TrivSqZeroExt R' R') := by
      have e2 : spMap (α₁.comp (algebraMap R (Sec s U))) = spMap (algebraMap R (TrivSqZeroExt R' R')) := by
        rw [Cris.spMap_comp, ← affPt_w s ⟨U, hU⟩, ← Category.assoc, hα, hy']
      exact congrArg CommRingCat.Hom.hom (Spec.map_injective e2)
    let α : Sec s U →ₐ[R] TrivSqZeroExt R' R' :=
      { α₁ with commutes' := fun r ↦ RingHom.congr_fun hc r }
    have h1 := snd_val_affine ⟨U, hU⟩ α y' hy' hα f (h0 _)
    rw [hv] at h1
    have h2 : algebraMap R R' (TrivSqZeroExt.snd (R := R) ((SqExt.dual R).val y hy f.1)) = 0 := by
      simpa [φ, Algebra.smul_def, TrivSqZeroExt.algebraMap_eq_inl'] using h1
    obtain ⟨⟨t, ht⟩, ht'⟩ := (IsLocalization.map_eq_zero_iff m.primeCompl R' _).1 h2
    exact ⟨t, ht, ht'⟩
  by_contra hx
  let J : Ideal R := LinearMap.ker (LinearMap.toSpanSingleton R R
    (TrivSqZeroExt.snd (R := R) ((SqExt.dual R).val y hy f.1)))
  have hJ : J ≠ ⊤ := fun h ↦ hx (by
    have : (1 : R) ∈ J := h ▸ Submodule.mem_top
    simpa [J] using this)
  obtain ⟨m, hm, hJm⟩ := Ideal.exists_le_maximal J hJ
  obtain ⟨t, ht, ht'⟩ := loc m hm
  exact ht (hJm (by simpa [J] using ht'))

theorem tanVal_eq_zero_of_cmpForm_eq_zero : ∀ (R : Type) [CommRing R] (A : Over (Sp R))
    (v : epsR R ⟶ A) (f : Form (A.hom ≫ 𝟙 (Sp R))),
    GlobalTheory.CechDR.cmpForm (A.hom ≫ 𝟙 (Sp R)) f = 0 → tanVal v f = 0 := by
  intro R _ A v f hf
  rw [tanVal_apply]
  refine snd_val_eq_zero v.left (pt_w v) f fun U ↦ ?_
  have := congrArg (fun g : ClosedForm (A.hom ≫ 𝟙 (Sp R)) ↦ g.1.1 (Opposite.op U)) hf
  exact (cmpForm_apply _ f (Opposite.op U)).symm.trans (this.trans rfl)

end GlobalTheory.TanVanish
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechDR

theorem bijective_liftSemi_secPull : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (X X' : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (φ : X' ⟶ X), IsPullback φ s' s (spMap (algebraMap R R')) → ∀ p : Pair φ, p.1.1.1 = φ ⁻¹ᵁ p.1.2.1 → ∀ f : Sec s p.1.2.1 →ₛₗ[algebraMap R R'] Sec s' p.1.1.1, (∀ b, f b = secPull s s' p b) → Function.Bijective (liftSemi f) := by
  intro R R' _ _ _ X X' s s' φ H p hp f hf
  have hUY : p.1.1.1 = φ ⁻¹ᵁ p.1.2.1 ⊓ s' ⁻¹ᵁ ⊤ := by rw [hp]; simp
  have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := p.1.2.1) (UY := p.1.1.1) le_top le_top hUY).mp
    (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _) (isAffineOpen_top _) p.1.2.2)
  have po' : IsPushout (CommRingCat.ofHom (algebraMap R (Sec s p.1.2.1))) (CommRingCat.ofHom (algebraMap R R'))
      (CommRingCat.ofHom (secPull s s' p)) (CommRingCat.ofHom (algebraMap R' (Sec s' p.1.1.1))) := by
    refine po.of_iso (Scheme.ΓSpecIso (.of R)) (Iso.refl _) (Scheme.ΓSpecIso (.of R')) (Iso.refl _) ?_ ?_ ?_ ?_
    · exact (Category.comp_id _).trans ((Scheme.ΓSpecIso (.of R)).hom_inv_id_assoc _).symm
    · rw [← Scheme.ΓSpecIso_naturality, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
      rfl
    · exact (Category.comp_id _).trans (Category.id_comp _).symm
    · exact (Category.comp_id _).trans ((Scheme.ΓSpecIso (.of R')).hom_inv_id_assoc _).symm
  letI : Algebra (Sec s p.1.2.1) (Sec s' p.1.1.1) := (secPull s s' p).toAlgebra
  letI : Algebra R (Sec s' p.1.1.1) := ((algebraMap R' (Sec s' p.1.1.1)).comp (algebraMap R R')).toAlgebra
  haveI : IsScalarTower R R' (Sec s' p.1.1.1) := .of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower R (Sec s p.1.2.1) (Sec s' p.1.1.1) :=
    .of_algebraMap_eq fun r => (congrArg (fun q => q.hom r) po'.w).symm
  have h : Algebra.IsPushout R R' (Sec s p.1.2.1) (Sec s' p.1.1.1) :=
    (CommRingCat.isPushout_iff_isPushout.mp po').symm
  have e : ⇑(liftSemi f) = ⇑h.out.equiv := by
    funext x
    induction x using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul c v => rw [liftSemi_tmul, h.out.equiv_tmul, hf]; rfl
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  rw [e]
  exact h.out.equiv.bijective

end GlobalTheory.CechDR
end

section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

open GlobalTheory.CechDR KaehlerDifferential
attribute [local instance] GlobalTheory.Cris.opModule GlobalTheory.Cris.isCentralScalar_kaehler GlobalTheory.Cris.isScalarTower_kaehler

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.PtVanish

section Affine

variable {R : Type} [CommRing R] {X : Scheme.{0}} {s : X ⟶ Sp R}
variable {A R' : Type} [CommRing A] [Algebra R A] [CommRing R'] [Algebra R R'] [Algebra A R']
  [IsScalarTower R A R']

def nbdMap (l : Ω[A⁄R] →ₗ[A] R') : TrivSqZeroExt A Ω[A⁄R] →ₐ[R] TrivSqZeroExt R' R' :=
  { toFun := fun c ↦ TrivSqZeroExt.inl (algebraMap A R' c.fst) + TrivSqZeroExt.inr (l c.snd)
    map_one' := by ext <;> simp
    map_zero' := by ext <;> simp
    map_add' := fun a b ↦ by ext <;> simp <;> ring
    map_mul' := fun a b ↦ by
      have hop : ∀ (b : A) (ω : Ω[A⁄R]), MulOpposite.op b • ω = b • ω := fun _ _ ↦ rfl
      ext
      · simp
      · simp only [TrivSqZeroExt.snd_mul, hop, map_add (f := _), map_smul, TrivSqZeroExt.snd_add,
          TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, TrivSqZeroExt.fst_add,
          TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, smul_eq_mul, Algebra.smul_def]
        simp [MulOpposite.smul_eq_mul_unop]
        ring
    commutes' := fun r ↦ by
      ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl', ← IsScalarTower.algebraMap_apply] }

theorem snd_nbdMap (l : Ω[A⁄R] →ₗ[A] R') (c : TrivSqZeroExt A Ω[A⁄R]) :
    (nbdMap l c).snd = l c.snd := by
  simp [nbdMap]

theorem fst_nbdMap (l : Ω[A⁄R] →ₗ[A] R') (c : TrivSqZeroExt A Ω[A⁄R]) :
    (nbdMap l c).fst = algebraMap A R' c.fst := by
  simp [nbdMap]

theorem snd_val_affine_eq (U : X.affineOpens) [Algebra (Sec s U.1) R'] [IsScalarTower R (Sec s U.1) R']
    (l : Ω[Sec s U.1⁄R] →ₗ[Sec s U.1] R') (y : Sp (TrivSqZeroExt R' R') ⟶ X)
    (hy : y ≫ s = spMap (algebraMap R (TrivSqZeroExt R' R')))
    (e : spMap ((nbdMap l).comp (diagSec R (Sec s U.1)) : Sec s U.1 →+* TrivSqZeroExt R' R') ≫
      affPt s U = y) (f : Form s) :
    TrivSqZeroExt.snd ((SqExt.ofModule R R' R').val y hy f.1) =
      l (connForm f.1 (affPt s U) (affPt_w s U)) := by
  have hx := affPt_w s U
  let Φ := nbdMap (R := R) l
  let α : Sec s U.1 →ₐ[R] TrivSqZeroExt R' R' := Φ.comp (diagSec R (Sec s U.1))
  let α₀ : Sec s U.1 →ₐ[R] R' := (TrivSqZeroExt.fstHom R R' R').comp α
  have hπ : ∀ c, α₀ ((diagExt R (Sec s U.1)).π c) = (SqExt.ofModule R R' R').π (Φ c) := fun c ↦ by
    change (Φ (diagSec R (Sec s U.1) c.fst)).fst = (Φ c).fst
    rw [fst_nbdMap, fst_nbdMap, fst_derSec]
  have e₀ : spMap (α₀ : Sec s U.1 →+* R') ≫ affPt s U =
      spMap ((SqExt.ofModule R R' R').π : TrivSqZeroExt R' R' →+* R') ≫ y := by
    rw [← e, ← Category.assoc, ← Cris.spMap_comp]; rfl
  let Ψ := (diagExt R (Sec s U.1)).thickHom (SqExt.ofModule R R' R') Φ α₀ hπ hx
    ((SqExt.ofModule R R' R').red_w hy) e₀
  let a1 : Thick.triv (Sec s U.1) (affPt s U) hx ⟶
      Thick.triv R' _ ((SqExt.ofModule R R' R').red_w hy) := Thick.trivHom α₀ e₀
  let a2 : Thick.triv (Sec s U.1) (affPt s U) hx ⟶ Thick.triv (TrivSqZeroExt R' R') y hy :=
    Thick.trivHom α e
  have k1 := Form.ev_sq f a1 ((SqExt.ofModule R R' R').secHom ((SqExt.ofModule R R' R').red_w hy)
    (SqExt.ofModule R R' R').i (SqExt.ofModule R R' R').π_i)
    ((diagExt R (Sec s U.1)).secHom hx (diagExt R (Sec s U.1)).i fun _ ↦ rfl) Ψ rfl rfl fun c ↦ by
      change TrivSqZeroExt.inl (α₀ c) = Φ (TrivSqZeroExt.inl c)
      ext
      · change (Φ (diagSec R (Sec s U.1) c)).fst = (Φ (TrivSqZeroExt.inl c)).fst
        rw [fst_nbdMap, fst_nbdMap, fst_derSec, TrivSqZeroExt.fst_inl]
      · rw [TrivSqZeroExt.snd_inl, snd_nbdMap, TrivSqZeroExt.snd_inl, map_zero]
  have k2 := Form.ev_sq f a2 ((SqExt.ofModule R R' R').idHom hy)
    ((diagExt R (Sec s U.1)).secHom hx (diagSec R (Sec s U.1)) (fst_derSec _)) Ψ rfl rfl
    fun _ ↦ rfl
  rw [SqExt.val_apply, k1, k2, add_sub_add_right_eq_sub]
  change TrivSqZeroExt.snd (Φ _ - Φ _) = _
  rw [← map_sub, snd_nbdMap]
  rfl

end Affine

theorem tanVal_pull_eq {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {A : Over (Sp R)}
    {B : Over (Sp R')} {φ : B.left ⟶ A.left}
    (m : IsMor (dp0 R) (A.hom ≫ 𝟙 _) (dp0 R') (B.hom ≫ 𝟙 _) (algebraMap R R') φ) (v' : epsR R' ⟶ B)
    (y : Sp (TrivSqZeroExt R' R') ⟶ A.left)
    (hy : y ≫ A.hom ≫ 𝟙 _ = spMap (algebraMap R (TrivSqZeroExt R' R')))
    (e : v'.left ≫ φ = y) (f : Form (A.hom ≫ 𝟙 _)) :
    tanVal v' (m.pullForm f) = TrivSqZeroExt.snd ((SqExt.ofModule R R' R').val y hy f.1) := by
  subst e
  let E := SqExt.ofModule R R' R'
  let E' := SqExt.dual R'
  have hy' := pt_w v'
  have hc : ∀ r : R, algebraMap R E.C r = algebraMap R' E'.C (algebraMap R R' r) := fun r ↦ by
    ext <;> simp [E, E', TrivSqZeroExt.algebraMap_eq_inl']
  have e₀ : spMap (RingHom.id R') ≫ spMap (E.π : E.C →+* E.B) ≫ v'.left ≫ φ =
      (spMap (E'.π : E'.C →+* E'.B) ≫ v'.left) ≫ φ := by
    rw [Cris.spMap_id, Category.id_comp, Category.assoc]; rfl
  let Φ : E.thick _ (E.red_w hy) ⟶ m.obj (E'.thick _ (E'.red_w hy')) :=
    { φ := { RingHom.id E.C with commutes' := hc }
      φ₀ := RingHom.id R'
      comm := fun _ ↦ rfl
      dp := isDPMorphism_sqDP E.sq E'.sq _ fun _ ha ↦ ha
      pt := e₀ }
  let a : Thick.triv E.C _ hy ⟶ m.obj (Thick.triv E'.C _ hy') :=
    Thick.trivHom { RingHom.id E.C with commutes' := hc } (by
      change spMap (RingHom.id E.C) ≫ v'.left ≫ φ = v'.left ≫ φ
      rw [Cris.spMap_id, Category.id_comp])
  let b : Thick.triv E.B _ (E.red_w hy) ⟶ m.obj (Thick.triv E'.B _ (E'.red_w hy')) :=
    Thick.trivHom { RingHom.id R' with commutes' := fun _ ↦ rfl } e₀
  have k1 := Form.ev_sq f a (m.functor.map (E'.idHom hy')) (E.idHom hy) Φ rfl rfl fun _ ↦ rfl
  have k2 := Form.ev_sq f b (m.functor.map (E'.secHom (E'.red_w hy') E'.i E'.π_i))
    (E.secHom (E.red_w hy) E.i E.π_i) Φ rfl rfl fun _ ↦ rfl
  have k : E'.val v'.left hy' (m.pullForm f).1 = E.val (v'.left ≫ φ) hy f.1 :=
    (congrArg₂ (fun u v : E'.C ↦ u - v) k2 k1).trans (add_sub_add_right_eq_sub (G := E'.C) _ _ _)
  rw [tanVal_apply]
  exact congrArg (TrivSqZeroExt.snd (R := R')) k

theorem sec_smooth {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) (hs : Smooth s)
    (U : X.affineOpens) : Algebra.Smooth R (Sec s U.1) := by
  have h1 : RingHom.Smooth (s.appLE ⊤ U.1 le_top).hom :=
    HasRingHomProperty.appLE @Smooth s hs ⟨⊤, isAffineOpen_top _⟩ U le_top
  have h2 : RingHom.Smooth (secMap s U.1).hom :=
    RingHom.Smooth.respectsIso.2 _ (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv h1
  exact h2

end GlobalTheory.PtVanish

namespace GlobalTheory.PtVanish

theorem connForm_eq_zero {K : Type} [Field K] {X : Over (Sp K)} (hX : Smooth X.hom)
    (f : Form (X.hom ≫ 𝟙 (Sp K)))
    (H : ∀ (L : Type) [Field L] (σ : K →+* L), ∃ (X' : Over (Sp L)) (φ : X'.left ⟶ X.left)
      (m : IsMor (dp0 K) (X.hom ≫ 𝟙 (Sp K)) (dp0 L) (X'.hom ≫ 𝟙 (Sp L)) σ φ),
      IsPullback φ X'.hom X.hom (spMap σ) ∧ ∀ u : epsR L ⟶ X', tanVal u (m.pullForm f) = 0)
    (U : X.left.affineOpens) :
    connForm f.1 (affPt (X.hom ≫ 𝟙 (Sp K)) U) (affPt_w (X.hom ≫ 𝟙 (Sp K)) U) = 0 := by
  have hsm : Smooth (X.hom ≫ 𝟙 (Sp K)) := by rw [Category.comp_id]; exact hX
  haveI : Algebra.Smooth K (Sec (X.hom ≫ 𝟙 (Sp K)) U.1) := sec_smooth _ hsm U
  haveI : _root_.IsReduced (Sec (X.hom ≫ 𝟙 (Sp K)) U.1) :=
    GlobalTheory.T.isReduced_of_smooth_over_field' K (Sec (X.hom ≫ 𝟙 (Sp K)) U.1)
  refine GlobalTheory.T.eq_zero_of_forall_residueField_functional' (Sec (X.hom ≫ 𝟙 (Sp K)) U.1) Ω[Sec (X.hom ≫ 𝟙 (Sp K)) U.1⁄K] _ ?_
  intro p _ l
  obtain ⟨X', φ, m, hpb, hv⟩ := H p.ResidueField (algebraMap K p.ResidueField)
  let α : Sec (X.hom ≫ 𝟙 (Sp K)) U.1 →ₐ[K] TrivSqZeroExt p.ResidueField p.ResidueField :=
    (nbdMap l).comp (diagSec K (Sec (X.hom ≫ 𝟙 (Sp K)) U.1))
  let y := spMap (α : Sec (X.hom ≫ 𝟙 (Sp K)) U.1 →+* TrivSqZeroExt p.ResidueField p.ResidueField) ≫
    affPt (X.hom ≫ 𝟙 (Sp K)) U
  have hy : y ≫ X.hom ≫ 𝟙 (Sp K) =
      spMap (algebraMap K (TrivSqZeroExt p.ResidueField p.ResidueField)) := by
    simp only [y, Category.assoc, affPt_w, ← Cris.spMap_comp, α.comp_algebraMap]
  have hcomp : (algebraMap p.ResidueField (DualNumber p.ResidueField)).comp
      (algebraMap K p.ResidueField) =
      algebraMap K (TrivSqZeroExt p.ResidueField p.ResidueField) :=
    RingHom.ext fun r ↦ by ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl']
  have w : y ≫ X.hom = spMap (algebraMap p.ResidueField (DualNumber p.ResidueField)) ≫
      spMap (algebraMap K p.ResidueField) := by
    rw [← Cris.spMap_comp, hcomp, ← hy, Category.comp_id]
  let u : epsR p.ResidueField ⟶ X' :=
    Over.homMk (hpb.lift y (spMap (algebraMap p.ResidueField (DualNumber p.ResidueField))) w)
      (hpb.lift_snd _ _ _)
  have e : u.left ≫ φ = y := hpb.lift_fst _ _ _
  have h := hv u
  rw [tanVal_pull_eq m u y hy e f, snd_val_affine_eq U l y hy rfl f] at h
  exact h

theorem cmpForm_eq_zero_of_tanVal : ∀ (K : Type) [Field K] (X : Over (Sp K)), Smooth X.hom → ∀ f : Form (X.hom ≫ 𝟙 (Sp K)), (∀ (L : Type) [Field L] (σ : K →+* L), ∃ (X' : Over (Sp L)) (φ : X'.left ⟶ X.left) (m : IsMor (dp0 K) (X.hom ≫ 𝟙 (Sp K)) (dp0 L) (X'.hom ≫ 𝟙 (Sp L)) σ φ), IsPullback φ X'.hom X.hom (spMap σ) ∧ ∀ u : epsR L ⟶ X', tanVal u (m.pullForm f) = 0) → GlobalTheory.CechDR.cmpForm (X.hom ≫ 𝟙 (Sp K)) f = 0 := by
  intro K _ X hX f H
  refine Subtype.ext (Subtype.ext (funext fun U ↦ ?_))
  exact (cmpForm_apply _ f U).trans (connForm_eq_zero hX f H U.unop)

end GlobalTheory.PtVanish
end
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem _root_.GlobalTheory.T.exists_coordinates_of_isConnected : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ G : PDivGroup p O, GlobalTheory.PDivLat.IsConn G → ∃ (d : ℕ) (x : ∀ n, Fin d → G.A n) (ev : ∀ n, MvPowerSeries (Fin d) O →ₐ[O] G.A n), (∀ n i, ∃ N : ℕ, (p : G.A n) ∣ x n i ^ N) ∧ (∀ n, IsEval p (x n) (ev n)) ∧ (∀ n i, G.res n (x (n + 1) i) = x n i) ∧ (∀ n i, Coalgebra.counit (R := O) (x n i) = 0) ∧ (∀ n, Function.Surjective (ev n)) ∧ ∀ m N : ℕ, ∃ n, ∀ f, ev n f = 0 → ∀ α : Fin d →₀ ℕ, α.degree < N → (p : O) ^ m ∣ coeff α f := by
  first | exact @GlobalTheory.PDivGroup.exists_coords_of_isConn | exact GlobalTheory.PDivGroup.exists_coords_of_isConn | (intros; apply GlobalTheory.PDivGroup.exists_coords_of_isConn <;> assumption)
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

theorem _root_.GlobalTheory.T.connectedPDivGroup_formalLaw_coordinates : ∀ (p : ℕ) (k : Type) [CommRing k] (d : ℕ) (G : PDivGroup p k) (c : Chart G d), (∃ μ, c.IsLawOf μ) ∧ ∀ (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k), c.IsLawOf μ → (∀ i, constantCoeff (μ i) = 0) ∧ ∀ n f, c.ev₂ n (subst μ f) = Coalgebra.comul (R := k) (c.ev n f) ∧ c.ev₂ n (cob1 μ f) = cobOne k (G.A n) (c.ev n f) := by
  first | exact @GlobalTheory.LawCoord.main | exact GlobalTheory.LawCoord.main | (intros; apply GlobalTheory.LawCoord.main <;> assumption)
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

theorem _root_.GlobalTheory.T.connectedPDivGroupHom_coordinates_existsUnique : ∀ (p : ℕ) (k : Type) [CommRing k] (d e : ℕ) (G H : PDivGroup p k) (c : Chart G d) (c' : Chart H e), ∀ f : G ⟶ H, (∃! φ, c.IsMapOf c' f φ) ∧ ∀ (φ : Fin e → MvPowerSeries (Fin d) k), c.IsMapOf c' f φ → (∀ j, constantCoeff (φ j) = 0) ∧ ∀ n, (∀ g, c.ev n (subst φ g) = f.app n (c'.ev n g)) ∧ ∀ s, c.ev₂ n (pull2 φ s) = pullbackTwo (f.app n) (c'.ev₂ n s) := by
  first | exact @GlobalTheory.Katz.isMapOf_existsUnique_and | exact GlobalTheory.Katz.isMapOf_existsUnique_and | (intros; apply GlobalTheory.Katz.isMapOf_existsUnique_and <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

theorem _root_.GlobalTheory.T.etaleCechAugmentation_equiv_of_section : ∀ (R : Type) [CommRing R] (F : Shv R) (Y X : Scheme.{0}) (f : Y ⟶ X) (s : X ⟶ Y), s ≫ f = 𝟙 X → Eqv R (cechAug f) F := by
  first | exact @GlobalTheory.cechAug_eqv_of_section | exact GlobalTheory.cechAug_eqv_of_section | (intros; apply GlobalTheory.cechAug_eqv_of_section <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.restrictScalars_injective_sheaf_acyclic : ∀ (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S) (I : Shv S) [Injective I] (P : PSh) (n : ℤ), 0 < n → Subsingleton (H R (disc.obj P) ((restr φ).obj I) n) := by
  first
  | exact @GlobalTheory.EtC.restr_injective_acyclic
  | exact GlobalTheory.EtC.restr_injective_acyclic
  | (intros; apply GlobalTheory.EtC.restr_injective_acyclic <;> assumption)
end

section

open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.HCA GroundTheory.Automorphic GlobalTheory.HCAlpha
open scoped ContDiff
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem _root_.GlobalTheory.T.exists_realBasis_glLieAlgebra_sum_sq_elementary : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), ∃ (d : ℕ) (b : Module.Basis (Fin d) ℝ (glL E a)), ∀ (A : Type) [Ring A] [Algebra ℝ A] (ρ : glL E a →ₗ[ℝ] A), ∑ k, ρ (b k) * ρ (b k) = ∑ τ : E →+* ℂ, ∑ i : Fin a, ∑ j : Fin a, (ρ ⟨Matrix.single i j (atEmb τ 1), Submodule.mem_top⟩ ^ 2 + ρ ⟨Matrix.single i j (atEmb τ Complex.I), Submodule.mem_top⟩ ^ 2) := by
  first | exact @GlobalTheory.glBasis_sum_sq | exact GlobalTheory.glBasis_sum_sq | (intros; apply GlobalTheory.glBasis_sum_sq <;> assumption)
end
