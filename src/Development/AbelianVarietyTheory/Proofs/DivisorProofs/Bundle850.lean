module

public import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticChartsRealizationCompPointEq
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle260
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle767
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle768
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle638
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle249
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle004
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle821
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle822
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle824
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle447
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle639
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle828
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle823
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle021
import Development.AbelianVarietyTheory.Definitions.Divisors.CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
import Development.AbelianVarietyTheory.Definitions.Divisors.Pullback1MemHodgeFiltration
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle003

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnPer.Reindex

open GlobalTheory.CatCoh

variable {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] (F : Fam I g Λ) {Λ' : Type} [AddCommGroup Λ'] (A : Λ' →+ Λ)

abbrev fam : Fam I g Λ' := ⟨F.V, F.τ.comp A, fun l ↦ F.hol (A l)⟩

variable {F A} (K' : Charts (fam F A))

@[reducible] def charts : Charts F where
  K := K'.K
  W := K'.W
  base := K'.base
  le m k' k := ∃ l, A l = m ∧ K'.le l k' k
  le_refl k := ⟨0, map_zero A, K'.le_refl k⟩
  le_trans := by
    rintro _ _ k k' k'' ⟨l, rfl, h⟩ ⟨m, rfl, h'⟩
    exact ⟨l + m, map_add A l m, K'.le_trans h h'⟩
  maps := by
    rintro _ k k' ⟨l, rfl, h⟩
    exact K'.maps h

@[reducible] def obj (T : K'.Obj) : (charts K').Obj where
  k := T.k
  C := T.C
  alg := T.alg
  J := T.J
  nil := T.nil
  ρ := T.ρ
  ρ_cst := T.ρ_cst

def hom {T T' : K'.Obj} (f : T ⟶ T') : obj K' T ⟶ obj K' T' where
  φ := f.φ
  deg := A f.deg
  le := ⟨f.deg, rfl, Charts.Hom.le f⟩
  mem := f.mem
  close := f.close

theorem isPeriod_comp : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {B : Type} [CommRing B] {X : Scheme.{0}} {s : X ⟶ Sp B} {σ : B →+* Hol F.V} (u : Unif F s σ) {Λ' : Type} [AddCommGroup Λ'] (A : Λ' →+ Λ) (u' : Unif (⟨F.V, F.τ.comp A, fun l ↦ F.hol (A l)⟩ : Fam I g Λ') s σ), u'.E = u.E → ∀ (c : FirstDeRham s) (per : Λ →+ Hol F.V), IsPeriod u c per → IsPeriod u' c (per.comp A) := by
  intro I _ g Λ _ F B _ X s σ u Λ' _ A u' hE c per h K' r' hr
  let r : Real (charts K') s σ :=
    { x := r'.x
      w := r'.w
      compat := by
        rintro _ k k' ⟨l, rfl, e⟩
        exact r'.compat e }
  have h1 := h (charts K') r (fun k p hp ↦ (hr k p hp).trans (congrFun hE p))
  obtain ⟨f, rfl⟩ := H1.mk_surjective _ c
  obtain ⟨G, hG⟩ := H1.mk_eq_mk.1 h1
  refine H1.mk_eq_mk.2 ⟨fun T ↦ G (obj K' T), ?_⟩
  funext T T' φ
  exact congrFun (congrFun (congrFun hG (obj K' T)) (obj K' T')) (hom K' φ)

end GlobalTheory.AnPer.Reindex
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AnPer

variable {X : Scheme.{0}}

def valHom (x : Sp ℂ ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) : Γ(X, U) →+* ℂ :=
  (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom.comp (x.appLE U ⊤ h).hom

theorem valHom_apply (x : Sp ℂ ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)) :
    valHom x U h f = valAt' x U f := by
  rw [valAt', dite_eq_left h]; rfl

theorem specMap_valHom_fromSpec (x : Sp ℂ ⟶ X) {U : X.Opens} (hU : IsAffineOpen U) (h : ⊤ ≤ x ⁻¹ᵁ U) :
    spMap (valHom x U h) ≫ hU.fromSpec = x := by
  have e := IsAffineOpen.SpecMap_appLE_fromSpec x hU (isAffineOpen_top (Sp ℂ)) h
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at e
  have e2 : CommRingCat.ofHom (valHom x U h) = x.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom := rfl
  rw [spMap, e2, Spec.map_comp, Category.assoc, e, ← Category.assoc, ← Spec.map_comp, Iso.inv_hom_id,
    Spec.map_id, Category.id_comp]

theorem exists_pt_of_affine : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {B : Type} [CommRing B] {X : Scheme.{0}} {s : X ⟶ Sp B} {σ : B →+* Hol F.V} (u : Unif F s σ) (W : Opens (Tot I g)), (∀ p ∈ W, p.1 ∈ F.V) → ∀ U : X.Opens, IsAffineOpen U → (∀ p ∈ W, ⊤ ≤ u.E p ⁻¹ᵁ U) → ∃ x : Sp (Hol W) ⟶ X, ⊤ ≤ x ⁻¹ᵁ U ∧ ∀ (p : Tot I g) (hp : p ∈ W), spMap (Hol.ev p hp).toRingHom ≫ x = u.E p := by
  intro I _ g Λ _ F B _ X s σ u W hW U hU hWU
  have han : ∀ f : Γ(X, U), AnalyticOnNhd ℂ (fun p ↦ valAt' (u.E p) U f) W := fun f p hp ↦
    GlobalTheory.SCV.analyticAt_of_differentiableOn (u.hol U f).2 ((u.hol U f).1.mem_nhds ⟨hW p hp, hWU p hp⟩)
  let φ : Γ(X, U) →+* Hol W :=
    (RingHom.pi fun p : W ↦ valHom (u.E p) U (hWU p p.2)).codRestrict (holSub W) fun f ↦
      ⟨fun p ↦ valAt' (u.E p) U f, han f, fun p ↦ valHom_apply _ _ _ f⟩
  refine ⟨spMap φ ≫ hU.fromSpec, ?_, fun p hp ↦ ?_⟩
  · simp [Scheme.Hom.comp_preimage, hU.fromSpec_preimage_self]
  · have e : (Hol.ev p hp).toRingHom.comp φ = valHom (u.E p) U (hWU p hp) := RingHom.ext fun f ↦ rfl
    rw [← Category.assoc, spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, e]
    exact specMap_valHom_fromSpec _ hU _

end GlobalTheory.AnPer
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.CatCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnPer.ChartMap

variable {I₁ : Type} [Fintype I₁] {g₁ : ℕ} {Λ₁ : Type} [AddCommGroup Λ₁] {F₁ : Fam I₁ g₁ Λ₁}
  {I₂ : Type} [Fintype I₂] {g₂ : ℕ} {Λ₂ : Type} [AddCommGroup Λ₂] {F₂ : Fam I₂ g₂ Λ₂}

def Φc (b : (I₁ → ℂ) → I₂ → ℂ) (M : (Fin g₁ → ℂ) →ₗ[ℂ] (Fin g₂ → ℂ)) {K₁ : Charts F₁} {K₂ : Charts F₂}
    (κ : K₁.K → K₂.K) (hΦ : ∀ k, AnalyticOnNhd ℂ (fun p : Tot I₁ g₁ ↦ ((b p.1, M p.2) : Tot I₂ g₂)) (K₁.W k))
    (hW : ∀ k, ∀ p ∈ K₁.W k, ((b p.1, M p.2) : Tot I₂ g₂) ∈ K₂.W (κ k)) (k : K₁.K) :
    Hol (K₂.W (κ k)) →+* Hol (K₁.W k) :=
  (Hol.comap _ (hΦ k) (hW k)).toRingHom

theorem Φc_cst (b : (I₁ → ℂ) → I₂ → ℂ) (hb : AnalyticOnNhd ℂ b F₁.V) (hbV : ∀ z ∈ F₁.V, b z ∈ F₂.V)
    (M : (Fin g₁ → ℂ) →ₗ[ℂ] (Fin g₂ → ℂ)) {K₁ : Charts F₁} {K₂ : Charts F₂}
    (κ : K₁.K → K₂.K) (hΦ : ∀ k, AnalyticOnNhd ℂ (fun p : Tot I₁ g₁ ↦ ((b p.1, M p.2) : Tot I₂ g₂)) (K₁.W k))
    (hW : ∀ k, ∀ p ∈ K₁.W k, ((b p.1, M p.2) : Tot I₂ g₂) ∈ K₂.W (κ k)) (k : K₁.K) (f : Hol F₂.V) :
    Φc b M κ hΦ hW k (K₂.cst (κ k) f) = K₁.cst k (Hol.comap b hb hbV f) :=
  Hol.ext_fn fun p hp ↦ by
    change (Hol.comap _ (hΦ k) (hW k) (K₂.cst (κ k) f)).fn p = _
    rw [Hol.fn_comap _ _ _ _ hp, Charts.fn_cst _ _ _ (hW k p hp), Charts.fn_cst _ _ _ hp,
      Hol.fn_comap _ _ _ _ (K₁.base k p hp)]

theorem Φc_sh (b : (I₁ → ℂ) → I₂ → ℂ) (M : (Fin g₁ → ℂ) →ₗ[ℂ] (Fin g₂ → ℂ)) (A : Λ₁ →+ Λ₂)
    (hτ : ∀ l, ∀ z ∈ F₁.V, F₂.τ (A l) (b z) = M (F₁.τ l z)) {K₁ : Charts F₁} {K₂ : Charts F₂}
    (κ : K₁.K → K₂.K) (hΦ : ∀ k, AnalyticOnNhd ℂ (fun p : Tot I₁ g₁ ↦ ((b p.1, M p.2) : Tot I₂ g₂)) (K₁.W k))
    (hW : ∀ k, ∀ p ∈ K₁.W k, ((b p.1, M p.2) : Tot I₂ g₂) ∈ K₂.W (κ k)) {l : Λ₁} {k k' : K₁.K}
    (h : K₁.le l k' k) (h₂ : K₂.le (A l) (κ k') (κ k)) (f : Hol (K₂.W (κ k))) :
    Φc b M κ hΦ hW k' (Charts.sh h₂ f) = Charts.sh h (Φc b M κ hΦ hW k f) :=
  Hol.ext_fn fun p hp ↦ by
    change (Hol.comap _ (hΦ k') (hW k') (Charts.sh h₂ f)).fn p =
      (Charts.sh h (Hol.comap _ (hΦ k) (hW k) f)).fn p
    rw [Hol.fn_comap _ _ _ _ hp, Charts.fn_sh _ _ (hW k' p hp), Charts.fn_sh _ _ hp,
      Hol.fn_comap _ _ _ _ (K₁.maps h p hp)]
    congr 1
    simp [Fam.shift, map_add (f := _), hτ l p.1 (K₁.base k' p hp)]

theorem dw_Φc (b : (I₁ → ℂ) → I₂ → ℂ) (hb : AnalyticOnNhd ℂ b F₁.V)
    (M : (Fin g₁ → ℂ) →ₗ[ℂ] (Fin g₂ → ℂ)) {K₁ : Charts F₁} {K₂ : Charts F₂}
    (κ : K₁.K → K₂.K) (hΦ : ∀ k, AnalyticOnNhd ℂ (fun p : Tot I₁ g₁ ↦ ((b p.1, M p.2) : Tot I₂ g₂)) (K₁.W k))
    (hW : ∀ k, ∀ p ∈ K₁.W k, ((b p.1, M p.2) : Tot I₂ g₂) ∈ K₂.W (κ k)) (k : K₁.K) (a : Fin g₁)
    (f : Hol (K₂.W (κ k))) :
    dw a (Φc b M κ hΦ hW k f) = ∑ c, M (Pi.single a 1) c • Φc b M κ hΦ hW k (dw c f) :=
  dw_comap_linear b M (fun p hp ↦ hb _ (K₁.base k p hp)) (hΦ k) (hW k) a f

end GlobalTheory.AnPer.ChartMap

namespace GlobalTheory.AnPer.ChartMap

variable {I₁ : Type} [Fintype I₁] {g₁ : ℕ} {Λ₁ : Type} [AddCommGroup Λ₁] {F₁ : Fam I₁ g₁ Λ₁}
  {I₂ : Type} [Fintype I₂] {g₂ : ℕ} {Λ₂ : Type} [AddCommGroup Λ₂] {F₂ : Fam I₂ g₂ Λ₂}

@[reducible] def objMap (b : (I₁ → ℂ) → I₂ → ℂ) (hb : AnalyticOnNhd ℂ b F₁.V) (hbV : ∀ z ∈ F₁.V, b z ∈ F₂.V)
    (M : (Fin g₁ → ℂ) →ₗ[ℂ] (Fin g₂ → ℂ)) {K₁ : Charts F₁} {K₂ : Charts F₂}
    (κ : K₁.K → K₂.K) (hΦ : ∀ k, AnalyticOnNhd ℂ (fun p : Tot I₁ g₁ ↦ ((b p.1, M p.2) : Tot I₂ g₂)) (K₁.W k))
    (hW : ∀ k, ∀ p ∈ K₁.W k, ((b p.1, M p.2) : Tot I₂ g₂) ∈ K₂.W (κ k)) (T : K₁.Obj) : K₂.Obj where
  k := κ T.k
  C := T.C
  ring := T.ring
  alg := ((algebraMap (Hol F₁.V) T.C).comp (Hol.comap b hb hbV).toRingHom).toAlgebra
  J := T.J
  nil := T.nil
  ρ := T.ρ.comp (Φc b M κ hΦ hW T.k)
  ρ_cst f := by
    change T.ρ (Φc b M κ hΦ hW T.k (K₂.cst (κ T.k) f)) = algebraMap (Hol F₁.V) T.C (Hol.comap b hb hbV f)
    rw [Φc_cst b hb hbV M κ hΦ hW, T.ρ_cst]

def homMap (b : (I₁ → ℂ) → I₂ → ℂ) (hb : AnalyticOnNhd ℂ b F₁.V) (hbV : ∀ z ∈ F₁.V, b z ∈ F₂.V)
    (M : (Fin g₁ → ℂ) →ₗ[ℂ] (Fin g₂ → ℂ)) (A : Λ₁ →+ Λ₂)
    (hτ : ∀ l, ∀ z ∈ F₁.V, F₂.τ (A l) (b z) = M (F₁.τ l z)) {K₁ : Charts F₁} {K₂ : Charts F₂}
    (κ : K₁.K → K₂.K) (hΦ : ∀ k, AnalyticOnNhd ℂ (fun p : Tot I₁ g₁ ↦ ((b p.1, M p.2) : Tot I₂ g₂)) (K₁.W k))
    (hW : ∀ k, ∀ p ∈ K₁.W k, ((b p.1, M p.2) : Tot I₂ g₂) ∈ K₂.W (κ k))
    (hle : ∀ l k' k, K₁.le l k' k → K₂.le (A l) (κ k') (κ k)) {T T' : K₁.Obj} (f : T ⟶ T') :
    Charts.Hom (objMap b hb hbV M κ hΦ hW T) (objMap b hb hbV M κ hΦ hW T') where
  φ := { (f.φ : T.C →+* T'.C) with commutes' := fun r ↦ f.φ.commutes (Hol.comap b hb hbV r) }
  deg := A f.deg
  le := hle _ _ _ (Charts.Hom.le f)
  mem := f.mem
  close := by
    have h := Close.comap_linear T'.J _ _ (Φc b M κ hΦ hW T.k) (fun c a ↦ M (Pi.single a 1) c)
      (dw_Φc b hb M κ hΦ hW T.k) f.close
    convert h using 1
    · exact RingHom.ext fun x ↦ congrArg T'.ρ (Φc_sh b M A hτ κ hΦ hW (Charts.Hom.le f) (hle _ _ _ (Charts.Hom.le f)) x)
    · rfl

def functor (b : (I₁ → ℂ) → I₂ → ℂ) (hb : AnalyticOnNhd ℂ b F₁.V) (hbV : ∀ z ∈ F₁.V, b z ∈ F₂.V)
    (M : (Fin g₁ → ℂ) →ₗ[ℂ] (Fin g₂ → ℂ)) (A : Λ₁ →+ Λ₂)
    (hτ : ∀ l, ∀ z ∈ F₁.V, F₂.τ (A l) (b z) = M (F₁.τ l z)) (K₁ : Charts F₁) (K₂ : Charts F₂)
    (κ : K₁.K → K₂.K) (hΦ : ∀ k, AnalyticOnNhd ℂ (fun p : Tot I₁ g₁ ↦ ((b p.1, M p.2) : Tot I₂ g₂)) (K₁.W k))
    (hW : ∀ k, ∀ p ∈ K₁.W k, ((b p.1, M p.2) : Tot I₂ g₂) ∈ K₂.W (κ k))
    (hle : ∀ l k' k, K₁.le l k' k → K₂.le (A l) (κ k') (κ k)) : K₁.Obj ⥤ K₂.Obj where
  obj := objMap b hb hbV M κ hΦ hW
  map f := homMap b hb hbV M A hτ κ hΦ hW hle f
  map_id _ := Charts.hom_ext (fun _ ↦ rfl) (map_zero A)
  map_comp _ _ := Charts.hom_ext (fun _ ↦ rfl) (map_add A _ _)

def coef (b : (I₁ → ℂ) → I₂ → ℂ) (hb : AnalyticOnNhd ℂ b F₁.V) (hbV : ∀ z ∈ F₁.V, b z ∈ F₂.V)
    (M : (Fin g₁ → ℂ) →ₗ[ℂ] (Fin g₂ → ℂ)) (A : Λ₁ →+ Λ₂)
    (hτ : ∀ l, ∀ z ∈ F₁.V, F₂.τ (A l) (b z) = M (F₁.τ l z)) (K₁ : Charts F₁) (K₂ : Charts F₂)
    (κ : K₁.K → K₂.K) (hΦ : ∀ k, AnalyticOnNhd ℂ (fun p : Tot I₁ g₁ ↦ ((b p.1, M p.2) : Tot I₂ g₂)) (K₁.W k))
    (hW : ∀ k, ∀ p ∈ K₁.W k, ((b p.1, M p.2) : Tot I₂ g₂) ∈ K₂.W (κ k))
    (hle : ∀ l k' k, K₁.le l k' k → K₂.le (A l) (κ k') (κ k)) :
    CoefMap (Hol.comap b hb hbV).toRingHom K₂.Oc K₁.Oc where
  G := functor b hb hbV M A hτ K₁ K₂ κ hΦ hW hle
  α T := RingHom.id T.C
  naturality _ _ := rfl
  smul T r c := (Algebra.smul_def (A := T.C) (Hol.comap b hb hbV r) c).symm

end GlobalTheory.AnPer.ChartMap

namespace GlobalTheory.AnPer

theorem period_pullback_eq_of_chartMap : ∀ {I₁ : Type} [Fintype I₁] {g₁ : ℕ} {Λ₁ : Type} [AddCommGroup Λ₁] {F₁ : Fam I₁ g₁ Λ₁} {B₁ : Type} [CommRing B₁] {X₁ : Scheme.{0}} {s₁ : X₁ ⟶ Sp B₁} {σ₁ : B₁ →+* Hol F₁.V} {I₂ : Type} [Fintype I₂] {g₂ : ℕ} {Λ₂ : Type} [AddCommGroup Λ₂] {F₂ : Fam I₂ g₂ Λ₂} {B₂ : Type} [CommRing B₂] {X₂ : Scheme.{0}} {s₂ : X₂ ⟶ Sp B₂} {σ₂ : B₂ →+* Hol F₂.V} (b : (I₁ → ℂ) → I₂ → ℂ) (hb : AnalyticOnNhd ℂ b F₁.V) (hbV : ∀ z ∈ F₁.V, b z ∈ F₂.V) (M : (Fin g₁ → ℂ) →ₗ[ℂ] (Fin g₂ → ℂ)) (A : Λ₁ →+ Λ₂), (∀ l, ∀ z ∈ F₁.V, F₂.τ (A l) (b z) = M (F₁.τ l z)) → ∀ (K₁ : Charts F₁) (K₂ : Charts F₂) (κ : K₁.K → K₂.K) (hΦ : ∀ k, AnalyticOnNhd ℂ (fun p : Tot I₁ g₁ ↦ ((b p.1, M p.2) : Tot I₂ g₂)) (K₁.W k)) (hW : ∀ k, ∀ p ∈ K₁.W k, ((b p.1, M p.2) : Tot I₂ g₂) ∈ K₂.W (κ k)), (∀ l k' k, K₁.le l k' k → K₂.le (A l) (κ k') (κ k)) → ∀ (r₁ : Real K₁ s₁ σ₁) (r₂ : Real K₂ s₂ σ₂) (β : B₂ →+* B₁) (φ : X₁ ⟶ X₂) (m : IsMor (dp0 B₂) s₂ (dp0 B₁) s₁ β φ), (∀ x, σ₁ (β x) = Hol.comap b hb hbV (σ₂ x)) → (∀ k, spMap (Hol.comap _ (hΦ k) (hW k)).toRingHom ≫ r₂.x (κ k) = r₁.x k ≫ φ) → ∀ (c : FirstDeRham s₂) (per₂ : Λ₂ →+ Hol F₂.V) (per₁ : Λ₁ →+ Hol F₁.V), (∀ l, per₁ l = Hol.comap b hb hbV (per₂ (A l))) → r₂.coef.pull1 c = K₂.perCl per₂ → r₁.coef.pull1 (m.pull1 c) = K₁.perCl per₁ := by
  intro I₁ _ g₁ Λ₁ _ F₁ B₁ _ X₁ s₁ σ₁ I₂ _ g₂ Λ₂ _ F₂ B₂ _ X₂ s₂ σ₂ b hb hbV M A hτ K₁ K₂ κ hΦ hW hle r₁ r₂ β φ m
    hσ hx c per₂ per₁ hper hc
  let n := ChartMap.coef b hb hbV M A hτ K₁ K₂ κ hΦ hW hle
  let θ : (m.coef.comp r₁.coef).G ⟶ (r₂.coef.comp n).G :=
    { app := fun T ↦
        { φ := { RingHom.id T.C with
            commutes' := fun r ↦ congrArg (algebraMap (Hol F₁.V) T.C) (hσ r) }
          φ₀ := RingHom.id (T.C ⧸ T.J)
          comm := fun _ ↦ rfl
          dp := letI := T.ratAlg
            isDPMorphism_of_rat T.δ (ChartMap.objMap b hb hbV M κ hΦ hW T).δ (RingHom.id T.C) fun _ h ↦ h
          pt := by
            change spMap (RingHom.id (T.C ⧸ T.J)) ≫ (spMap ((Ideal.Quotient.mk T.J).comp T.ρ) ≫ r₁.x T.k) ≫ φ =
              spMap (((Ideal.Quotient.mk T.J).comp T.ρ).comp (Hol.comap _ (hΦ T.k) (hW T.k)).toRingHom) ≫
                r₂.x (κ T.k)
            rw [Cris.spMap_id, Category.id_comp, Category.assoc, ← hx T.k,
              Cris.spMap_comp (Hol.comap _ (hΦ T.k) (hW T.k)).toRingHom, Category.assoc] }
      naturality := fun _ _ _ ↦ Thick.Hom.ext' (AlgHom.ext fun _ ↦ rfl) }
  have e₁ : r₁.coef.pull1 (m.pull1 c) = (m.coef.comp r₁.coef).pull1 c := (m.coef.pullCohomologyOne_comp r₁.coef c).symm
  have e₂ : (m.coef.comp r₁.coef).pull1 c = (r₂.coef.comp n).pull1 c :=
    CoefMap.pullCohomologyOne_eq_of_natTrans _ _ θ (fun _ _ ↦ rfl) c
  have e₃ : n.pullbackOneCocycle (K₂.perZ per₂) = K₁.perZ per₁ := by
    refine Subtype.ext ?_
    funext T T' f
    exact (congrArg (algebraMap (Hol F₁.V) T'.C) (hper f.deg)).symm
  rw [e₁, e₂, r₂.coef.pullCohomologyOne_comp n c, hc, Charts.perCl, CoefMap.pullCohomologyOne_class, e₃, Charts.perCl]

end GlobalTheory.AnPer

namespace GlobalTheory.AnPer.CmpCore

theorem period_pullback_eq_of_chartMap_class_alt : ∀ {I₁ : Type} [Fintype I₁] {g₁ : ℕ} {Λ₁ : Type} [AddCommGroup Λ₁] {F₁ : Fam I₁ g₁ Λ₁} {B₁ : Type} [CommRing B₁] {X₁ : Scheme.{0}} {s₁ : X₁ ⟶ Sp B₁} {σ₁ : B₁ →+* Hol F₁.V} {I₂ : Type} [Fintype I₂] {g₂ : ℕ} {Λ₂ : Type} [AddCommGroup Λ₂] {F₂ : Fam I₂ g₂ Λ₂} {B₂ : Type} [CommRing B₂] {X₂ : Scheme.{0}} {s₂ : X₂ ⟶ Sp B₂} {σ₂ : B₂ →+* Hol F₂.V} (b : (I₁ → ℂ) → I₂ → ℂ) (hb : AnalyticOnNhd ℂ b F₁.V) (hbV : ∀ z ∈ F₁.V, b z ∈ F₂.V) (M : (Fin g₁ → ℂ) →ₗ[ℂ] (Fin g₂ → ℂ)) (A : Λ₁ →+ Λ₂), (∀ l, ∀ z ∈ F₁.V, F₂.τ (A l) (b z) = M (F₁.τ l z)) → ∀ (K₁ : Charts F₁) (K₂ : Charts F₂) (κ : K₁.K → K₂.K) (hΦ : ∀ k, AnalyticOnNhd ℂ (fun p : Tot I₁ g₁ ↦ ((b p.1, M p.2) : Tot I₂ g₂)) (K₁.W k)) (hW : ∀ k, ∀ p ∈ K₁.W k, ((b p.1, M p.2) : Tot I₂ g₂) ∈ K₂.W (κ k)), (∀ l k' k, K₁.le l k' k → K₂.le (A l) (κ k') (κ k)) → ∀ (r₁ : Real K₁ s₁ σ₁) (r₂ : Real K₂ s₂ σ₂) (β : B₂ →+* B₁) (φ : X₁ ⟶ X₂) (m : IsMor (dp0 B₂) s₂ (dp0 B₁) s₁ β φ), (∀ x, σ₁ (β x) = Hol.comap b hb hbV (σ₂ x)) → (∀ k, spMap (Hol.comap _ (hΦ k) (hW k)).toRingHom ≫ r₂.x (κ k) = r₁.x k ≫ φ) → ∀ (c : FirstDeRham s₂) (per₂ : Λ₂ →+ Hol F₂.V) (per₁ : Λ₁ →+ Hol F₁.V), (∀ l, per₁ l = Hol.comap b hb hbV (per₂ (A l))) → r₂.coef.pull1 c = K₂.perCl per₂ → r₁.coef.pull1 (m.pull1 c) = K₁.perCl per₁ :=
  @GlobalTheory.AnPer.period_pullback_eq_of_chartMap

end GlobalTheory.AnPer.CmpCore
end
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)
open GlobalTheory.LatVal (Sz)
open GlobalTheory.CMVal (latDisc)

namespace GlobalTheory.QFam

theorem sz_value_of_family (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l])
    (ι : Type) [Fintype ι] (act : ι → SL(2, ℤ) → ι) (w N : ℕ) (f : ι → ℍ → ℂ) (r : ℝ) (τ₀ : ℍ) (Ω : ℂ)
    (hN : 0 < N) (hact : ActBij act) (hf : IsFam act w f) (hq : ∀ i, QAll (Sz l lam r) N (f i))
    (hj : Sz l lam 0 (jT τ₀)) (hΩ : Ω ^ 12 = DD τ₀) (i : ι) :
    Sz l lam r (f i τ₀ / Ω ^ w) := by
  refine GlobalTheory.T.algebraicValuationAtLeast_of_forall_rat_gt l lam r _ fun q hrq => ?_
  obtain ⟨c, hc0, hc, hc'⟩ := GlobalTheory.T.exists_algebraic_of_rational_valuation l lam q
  obtain ⟨R, hR, hcl⟩ := GlobalTheory.T.exists_integrallyClosed_padicIntegralSubring l lam
  obtain ⟨hconst, hmono, -, hmul, -⟩ := GlobalTheory.T.qExpansionValuationBound_ring_closure l lam N hN
  have hfam : IsFam act w fun i τ => c * f i τ := (GlobalTheory.T.isSLTwoPermutedModularFamily_algebra_closure ι act).2.2.1 w c f hf
  have hq' : ∀ i, QAll (· ∈ R) N fun τ => c * f i τ := fun i => by
    obtain ⟨a, ha, ha'⟩ := hmono _ 0 _ (by linarith) (hmul _ _ _ _ (hconst _ c hc) (hq i))
    exact ⟨a, ha, fun n => (hR _).2 (ha' n)⟩
  have hjR : IsIntegral R (jT τ₀) :=
    isIntegral_algebraMap (R := R) (A := ℂ) (x := ⟨jT τ₀, (hR _).2 hj⟩)
  have h0 : Sz l lam 0 (c * f i τ₀ / Ω ^ w) :=
    (hR _).1 (hcl _ (GlobalTheory.T.isIntegral_modularFamily_value_div_period_pow ι act w N _ R τ₀ Ω hN hact hfam hq' hjR hΩ i))
  have h1 := (GlobalTheory.T.algebraicValuationAtLeastAtEmbedding_ring_ops l lam).2.2.1 _ _ _ _ hc' h0
  have e : c⁻¹ * (c * f i τ₀ / Ω ^ w) = f i τ₀ / Ω ^ w := by
    rw [mul_div_assoc, inv_mul_cancel_left₀ hc0]
  rwa [add_zero, e] at h1

end GlobalTheory.QFam
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

theorem _root_.GlobalTheory.T.isInCharacterIsotypicPart_iff_convolution : ∀ (G : Type) [Group G] [Finite G] (φ Y : G → ℂ), IsChar ℂ ℂ Y → (Kills φ Y ↔ ∃ h : G → ℂ, ∀ x, φ x = ∑ᶠ y, Y y * h (y⁻¹ * x)) := by
  first | (exact @GlobalTheory.Shin.kills_iff_conv) | (exact GlobalTheory.Shin.kills_iff_conv) | (intros; apply GlobalTheory.Shin.kills_iff_conv <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh GlobalTheory.AbTan
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.spec_trivSqZeroExt_isPushout : ∀ (R : Type) [CommRing R] (B M : Type) [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M] [Module R M] [IsScalarTower R B M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M] (β : TrivSqZeroExt R M →+* TrivSqZeroExt B M), IsSum β (algebraMap R B) id → ∀ (X : Scheme.{0}) (x : Sp R ⟶ X) (z : Sp (TrivSqZeroExt B M) ⟶ X), spMap (TrivSqZeroExt.fstHom B B M).toRingHom ≫ z = spMap (algebraMap R B) ≫ x → ∃! z₀ : Sp (TrivSqZeroExt R M) ⟶ X, spMap (TrivSqZeroExt.fstHom R R M).toRingHom ≫ z₀ = x ∧ spMap β ≫ z₀ = z := by
  first | exact @GlobalTheory.Pinch.pinch_main | exact GlobalTheory.Pinch.pinch_main | (intros; apply GlobalTheory.Pinch.pinch_main <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem bc_cechAug_eqv : ∀ (R : Type) [CommRing R] (F : Shv R) (S W V : Scheme.{0}) (r : W ⟶ S) (f : V ⟶ W),
    Etale f → Surjective f → ∀ U : Over S, Eqv R ((bcMap (cechAug f) (sch.map r)).app U) F := by
  intro R _ F S W V r f hE hS U
  obtain ⟨e₁, e₂, he⟩ := bc_cechAug_iso S W V r f U
  have hE' : Etale (pullback.snd f (pullback.fst r U.hom)) := inferInstance
  have hS' : Surjective (pullback.snd f (pullback.fst r U.hom)) := inferInstance
  have hA : Eqv R (cechAug (pullback.snd f (pullback.fst r U.hom))) F :=
    smooth_surjective_cech_descent_cohomology R (pullback.snd f (pullback.fst r U.hom)) F
  obtain ⟨hiso, hcomp, -, -⟩ := eqv_basic R F
  have h1 : Eqv R e₁.hom F := hiso _ _ _ inferInstance
  have h2 : Eqv R e₂.hom F := hiso _ _ _ inferInstance
  have h3 : Eqv R (e₁.hom ≫ (bcMap (cechAug f) (sch.map r)).app U) F := by
    rw [he]; exact (hcomp _ _ _ _ _).1 hA h2
  exact (hcomp _ _ _ _ _).2.1 h1 h3

end GlobalTheory.EtC
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

theorem _root_.GlobalTheory.T.cechConerve_chains_quasiIso_of_locallySurjective : ∀ (R : Type) [CommRing R] (T : Type 1) [Category.{0} T] [HasFiniteWidePushouts T] (Ψ : T ⥤ PShᵒᵖ), (∀ n : ℕ, PreservesColimitsOfShape (WidePushoutShape (Fin (n + 1))) Ψ) → ∀ (U V : T) (g : U ⟶ V), Presheaf.IsLocallySurjective Scheme.etaleTopology.{0} (Ψ.map g).unop → QuasiIso ((chains R).map (lev Ψ (coAug g))) := by
  first | (exact @GlobalTheory.EtC.chains_cech_conerve_quasiIso) | (exact GlobalTheory.EtC.chains_cech_conerve_quasiIso) | (intros; apply GlobalTheory.EtC.chains_cech_conerve_quasiIso <;> assumption)
end

section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem _root_.GlobalTheory.T.curvature_lower_bound_on_cover_balls : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (C : Cover A) (H G : La), (∀ i y, y ∈ (A.chart i).source → ∀ ξ : Fin n → ℂ, ξ ≠ 0 → 0 < A.leviAt i (A.ph H i) y ξ) → ∀ t : ℝ, ∃ k0 : ℕ, ∀ k ≥ k0, CurvGe C (G + k • H) t := by
  first | exact @GlobalTheory.OTY.CoverCurv.curv_cover | exact GlobalTheory.OTY.CoverCurv.curv_cover | (intros; apply GlobalTheory.OTY.CoverCurv.curv_cover <;> assumption)
end

section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem _root_.GlobalTheory.T.lintegral_atlasMeasure_etale_pullback_lebesgue : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (U : Set Y) (z : Y → V n), Etale A U z → ∀ φ : Y → ℝ≥0∞, Measurable φ → ∫⁻ y in U, φ y ∂A.mu = ∫⁻ x : U, φ x * ENNReal.ofReal (A.nsq A.kap (jdet A z) x)⁻¹ ∂vol n (fun y : U => z y) := by
  first | exact @GlobalTheory.EtaleMeasure.lintegral_mu_etale | exact GlobalTheory.EtaleMeasure.lintegral_mu_etale | (intros; apply GlobalTheory.EtaleMeasure.lintegral_mu_etale <;> assumption)
end

section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem _root_.GlobalTheory.T.twistedExtension_etaleStein_sqIntegrable : ∀ (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M], ∀ (X : EtaleStein n M) (φ ψ : M → ℝ) (G : M → ℂ) (Ω : Set M) (δ T : ℝ) (θ : ℝ → ℝ), SmoothR n X.z φ → SmoothR n X.z ψ → (∀ x, ψ x ≤ 0) → 0 < δ → 300 ≤ T → IsCut T θ → (∀ α ∈ Set.Icc (1 : ℝ) (1 + δ), LeviNonneg n X.z (fun x => φ x + α * ψ x)) → IsOpen Ω → Measurable G → (∀ e : OpenPartialHomeomorph M (V n), IsChart n X.z e → DifferentiableOn ℂ (G ∘ e.symm) (e.target ∩ e.symm ⁻¹' Ω)) → (∀ x, δ * ψ x ≤ -T + 1 → x ∈ Ω) → wint n X.z (fun x => (θ (δ * ψ x) : ℂ) * G x) (fun x => φ x + ψ x) < ⊤ → ∃ F : M → ℂ, Holo n X.z F ∧ ∫⁻ x, ENNReal.ofReal (‖(θ (δ * ψ x) : ℂ) * G x - F x‖ ^ 2 * (wT T (δ * ψ x) * Real.exp (-(φ x + ψ x)))) ∂vol n X.z ≤ 30 * ∫⁻ x in {x | -T - 1 ≤ δ * ψ x ∧ δ * ψ x ≤ -T + 1}, ENNReal.ofReal (‖G x‖ ^ 2 * Real.exp (-(φ x + ψ x))) ∂vol n X.z := by
  first | exact @GlobalTheory.twistedExtension_sqInt | exact GlobalTheory.twistedExtension_sqInt | (intros; apply GlobalTheory.twistedExtension_sqInt <;> assumption)
end

section

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

theorem _root_.GlobalTheory.T.twistedDual_regularForms_finiteCover : ∀ (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x → ∀ (τ : DR k K →ₗ[K] K), IsTop k K x τ → ∀ I : Finset (Fin (d + 1)), I.Nonempty → ∀ p q : ℕ, p + q = d → ∀ y ∈ ⋀[K]^q Ω[K⁄k], (∀ a ∈ omB k K (rB k K x I) p, Algebra.trace F K (τ (a * y)) ∈ omA k x I) ↔ y ∈ omB k K (rB k K x I) q := by
  first | (exact @GlobalTheory.PD.twistedDual_omB) | (exact GlobalTheory.PD.twistedDual_omB) | (intros; apply GlobalTheory.PD.twistedDual_omB  <;> assumption)
end
