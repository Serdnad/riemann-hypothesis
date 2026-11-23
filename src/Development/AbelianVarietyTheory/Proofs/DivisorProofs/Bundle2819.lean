module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2725
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2726
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2727
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2728
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2729
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2730
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
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

set_option autoImplicit false

namespace GlobalTheory.Desc.GaussPt

section Top

theorem coheight_le_one_of_flat {H S : Scheme.{0}} (p : H ⟶ S) [Flat p] (x : H)
    (hx : Order.coheight x ≤ 1) : Order.coheight (p x) ≤ 1 := by
  have hp := Flat.generalizingMap p
  have hx' := (Order.coheight_le_coe_iff (n := 1)).1 hx
  refine (Order.coheight_le_coe_iff (n := 1)).2 fun y hy ↦ ?_
  obtain ⟨x', h₁, rfl⟩ := hp (show y ⤳ p x from hy.le)
  have hlt : x < x' := ⟨h₁, fun h ↦ hy.not_ge (Specializes.map h p.continuous)⟩
  have hm : IsMax x' := by simpa using hx' x' hlt
  have : IsMax (p x') := fun w hw ↦ by
    obtain ⟨x'', h₂, rfl⟩ := hp (show w ⤳ p x' from hw)
    exact Specializes.map (hm (show x' ≤ x'' from h₂)) p.continuous
  simpa using this

theorem coheight_le_one_iff {X : Scheme.{0}} (x : X) :
    Order.coheight x ≤ 1 ↔ ringKrullDim (X.presheaf.stalk x) ≤ 1 := by
  rw [ringKrullDim_stalk_eq_coheight]
  exact_mod_cast Iff.rfl

theorem height_le_one {R : Type} [CommRing R] (q : Sp R) (h : Order.coheight q ≤ 1) :
    q.asIdeal.height ≤ 1 := by
  rw [coheight_le_one_iff] at h
  have : q.asIdeal.IsPrime := q.2
  letI : Algebra R ((Sp R).presheaf.stalk q) := StructureSheaf.stalkAlgebra R q
  have : IsLocalization.AtPrime ((Sp R).presheaf.stalk q) q.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk R q
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height q.asIdeal] at h
  exact_mod_cast h

variable {R : Type} [CommRing R] [IsDomain R] {X : Scheme.{0}} [IsIntegral X]

theorem asIdeal_genericPoint (p : X ⟶ Sp R) [Flat p] : (p (genericPoint X)).asIdeal = ⊥ := by
  let o : Sp R := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)
  have h : o ⤳ p (genericPoint X) := (PrimeSpectrum.le_iff_specializes _ _).1 bot_le
  obtain ⟨x, h₁, h₂⟩ := Flat.generalizingMap p h
  have : x = genericPoint X := (h₁.antisymm (genericPoint_specializes x)).eq
  rw [← this, h₂]

theorem cst_injective (p : X ⟶ Sp R) [Flat p] : Function.Injective (GlobalTheory.Desc.cst p) := by
  refine (injective_iff_map_eq_zero _).2 fun r hr => ?_
  by_contra h
  refine ((unitAt_cst_iff p (genericPoint X) r).2 ?_).ne_zero hr
  rwa [asIdeal_genericPoint]

theorem ringKrullDim_eq_one (p : X ⟶ Sp R) [Flat p] {x : X} (h : (p x).asIdeal ≠ ⊥)
    (hx : Order.coheight x ≤ 1) : ringKrullDim (X.presheaf.stalk x) = 1 := by
  rw [ringKrullDim_stalk_eq_coheight]
  have h0 : Order.coheight x ≠ 0 := fun h0 => by
    rw [Order.coheight_eq_zero] at h0
    have h₁ : x ⤳ genericPoint X := h0 (show x ≤ genericPoint X from genericPoint_specializes x)
    obtain rfl : x = genericPoint X := (h₁.antisymm (genericPoint_specializes x)).eq
    exact h (asIdeal_genericPoint p)
  have : Order.coheight x = 1 := le_antisymm hx (Order.one_le_iff_ne_zero.2 h0)
  rw [this]; rfl

theorem eq_of_coheight_le_one (p : X ⟶ Sp R) [Smooth p] [GeometricallyConnected p] {x x' : X}
    (e : p x = p x') (h : (p x).asIdeal ≠ ⊥) (hx : Order.coheight x ≤ 1) (hx' : Order.coheight x' ≤ 1) :
    x = x' := by
  have := isIntegral_fiber_of_smooth p (p x)
  let ξ := p.fiberι (p x) (genericPoint _)
  have hξ : p ξ = p x := (p.range_fiberι (p x)).le ⟨_, rfl⟩
  have key : ∀ w : X, p w = p x → Order.coheight w ≤ 1 → w = ξ := by
    intro w hw hc
    obtain ⟨w', rfl⟩ := (p.range_fiberι (p x)).ge hw
    have hs : ξ ⤳ p.fiberι (p x) w' := (genericPoint_specializes w').map (p.fiberι (p x)).continuous
    by_contra hne
    have hlt : p.fiberι (p x) w' < ξ := ⟨hs, fun h' => hne (Specializes.antisymm h' hs).eq⟩
    have hm : IsMax ξ := by simpa using (Order.coheight_le_coe_iff (n := 1)).1 hc ξ hlt
    have h₁ : ξ ⤳ genericPoint X := hm (show ξ ≤ genericPoint X from genericPoint_specializes ξ)
    have h₂ : ξ = genericPoint X := (h₁.antisymm (genericPoint_specializes ξ)).eq
    apply h
    rw [← hξ, h₂]
    exact asIdeal_genericPoint p
  rw [key x rfl hx, key x' e.symm hx']

end Top

section Ring

theorem exists_common_field {R A B : Type} [CommRing R] [CommRing A] [CommRing B] (ρ : R →+* A)
    (ρ' : R →+* B) (q : Sp A) (q' : Sp B) (h : spMap ρ q = spMap ρ' q') :
    ∃ (Ω : Type) (_ : Field Ω) (u : A →+* Ω) (u' : B →+* Ω), RingHom.ker u = q.asIdeal ∧
      RingHom.ker u' = q'.asIdeal ∧ u.comp ρ = u'.comp ρ' := by
  obtain ⟨w, h₁, h₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := spMap ρ) (g := spMap ρ') q q' h
  let k := (pullback (spMap ρ) (spMap ρ')).fromSpecResidueField w
  have hk : ∀ {C : Type} [CommRing C] (g : pullback (spMap ρ) (spMap ρ') ⟶ Sp C),
      RingHom.ker (Spec.preimage (k ≫ g)).hom = (g w).asIdeal := by
    intro C _ g
    let o : Spec ((pullback (spMap ρ) (spMap ρ')).residueField w) := (⊥ : PrimeSpectrum _)
    have e := congrArg (fun m => m o) (Spec.map_preimage (k ≫ g))
    have e' : (k ≫ g) o = g w := by
      rw [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]
    rw [← e', ← e]
    rfl
  refine ⟨_, inferInstance, (Spec.preimage (k ≫ pullback.fst _ _)).hom,
    (Spec.preimage (k ≫ pullback.snd _ _)).hom, (hk _).trans (by rw [h₁]), (hk _).trans (by rw [h₂]), ?_⟩
  have : CommRingCat.ofHom ρ ≫ Spec.preimage (k ≫ pullback.fst _ _) =
      CommRingCat.ofHom ρ' ≫ Spec.preimage (k ≫ pullback.snd _ _) := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp, Spec.map_preimage, Spec.map_preimage, Category.assoc,
      Category.assoc, pullback.condition]
  exact congrArg CommRingCat.Hom.hom this

theorem dvr_of_height {E : Type} [CommRing E] [IsRegularLocalRing E] [IsDomain E]
    (h : (maximalIdeal E).height ≤ 1) (h0 : maximalIdeal E ≠ ⊥) : IsDiscreteValuationRing E := by
  have : IsPrincipalIdealRing E :=
    GroundTheory.Arith.SchemeCoh.IsRegularLocalRing.isPrincipalIdealRing_of_ringKrullDim_le_one (by
      rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim]; exact_mod_cast h)
  exact ⟨h0⟩

theorem height_le_of_map {A E : Type} [CommRing A] [IsNoetherianRing A] [CommRing E] [IsLocalRing E]
    [IsNoetherianRing E] (a : A →+* E) (q : Ideal A) [q.IsPrime] (hq : q.height ≤ 1)
    (h₁ : (maximalIdeal E).comap a = q) (h₂ : q.map a = maximalIdeal E) : (maximalIdeal E).height ≤ 1 := by
  letI := a.toAlgebra
  have : (maximalIdeal E).LiesOver q := ⟨h₁.symm⟩
  refine (Ideal.height_le_height_add_of_liesOver q (maximalIdeal E)).trans ?_
  have h₃ : q.map (algebraMap A E) = maximalIdeal E := h₂
  have h₄ : (maximalIdeal E).map (Ideal.Quotient.mk (q.map (algebraMap A E))) = ⊥ := by
    rw [← h₃, Ideal.map_quotient_self]
  have : Nontrivial (E ⧸ q.map (algebraMap A E)) :=
    Ideal.Quotient.nontrivial_iff.2 (h₃ ▸ (maximalIdeal.isMaximal E).ne_top)
  rw [h₄, Ideal.height_bot, add_zero]
  exact hq

theorem injective_of_flat {A E : Type} [CommRing A] [IsDomain A] [CommRing E] [Nontrivial E]
    {a : A →+* E} (h : a.Flat) : Function.Injective a := by
  letI := a.toAlgebra
  have : Module.Flat A E := h
  exact FaithfulSMul.algebraMap_injective A E

theorem dvd_pow_of_dim {O : Type} [CommRing O] [IsDomain O] [IsLocalRing O] (h : ringKrullDim O ≤ 1)
    {g t : O} (hg : g ≠ 0) (ht : ¬ IsUnit t) : ∃ n : ℕ, g ∣ t ^ n := by
  have : Ring.KrullDimLE 1 O := Ring.krullDimLE_iff.2 h
  have : t ∈ (Ideal.span {g}).radical := by
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
    rintro J ⟨hJ, hp⟩
    have hne : J ≠ ⊥ := fun e => hg (by simpa [e] using hJ)
    rw [eq_maximalIdeal (hp.isMaximal_of_ne_bot hne)]
    exact ht
  obtain ⟨n, hn⟩ := this
  exact ⟨n, Ideal.mem_span_singleton.1 hn⟩

end Ring

section Span

variable {R₁ F₁ : Type} [CommRing R₁] [CommRing F₁] (c : R₁ →+* F₁)

theorem mem_spanBy_iff (T : Set F₁) (v : F₁) :
    v ∈ spanBy c T ↔ letI := c.toAlgebra; v ∈ Submodule.span R₁ T := by
  letI := c.toAlgebra
  rw [Submodule.mem_span_set']
  constructor
  · rintro ⟨n, r, t, ht, rfl⟩
    exact ⟨n, r, fun i => ⟨t i, ht i⟩, rfl⟩
  · rintro ⟨n, r, t, rfl⟩
    exact ⟨n, r, fun i => t i, fun i => (t i).2, rfl⟩

variable {c}

theorem spanBy_zero (T : Set F₁) : (0 : F₁) ∈ spanBy c T :=
  (mem_spanBy_iff c T _).2 (zero_mem _)

theorem spanBy_add {T : Set F₁} {u v : F₁} (hu : u ∈ spanBy c T) (hv : v ∈ spanBy c T) :
    u + v ∈ spanBy c T :=
  (mem_spanBy_iff c T _).2 (add_mem ((mem_spanBy_iff c T _).1 hu) ((mem_spanBy_iff c T _).1 hv))

theorem spanBy_smul {T : Set F₁} (r : R₁) {u : F₁} (hu : u ∈ spanBy c T) : c r * u ∈ spanBy c T :=
  letI := c.toAlgebra
  (mem_spanBy_iff c T _).2 (Submodule.smul_mem _ r ((mem_spanBy_iff c T _).1 hu))

theorem spanBy_induction {T : Set F₁} {P : F₁ → Prop} (h₀ : P 0) (h₁ : ∀ t ∈ T, P t)
    (h₂ : ∀ u v, P u → P v → P (u + v)) (h₃ : ∀ r u, P u → P (c r * u)) {v : F₁}
    (hv : v ∈ spanBy c T) : P v := by
  letI := c.toAlgebra
  rw [mem_spanBy_iff] at hv
  induction hv using Submodule.span_induction with
  | mem x hx => exact h₁ x hx
  | zero => exact h₀
  | add x y _ _ hx hy => exact h₂ x y hx hy
  | smul r x _ hx => exact h₃ r x hx

end Span

end GlobalTheory.Desc.GaussPt
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

theorem _root_.GlobalTheory.T.exists_glue_morphisms_integral_agree_at_genericPoint : ∀ (Y P : Scheme.{0}) [IsIntegral Y] [P.IsSeparated] (U : Y → Y.Opens), (∀ y, y ∈ U y) → ∀ (f : ∀ y, (U y).toScheme ⟶ P) (w : Sp Y.functionField ⟶ P), (∀ y (l : Sp Y.functionField ⟶ (U y).toScheme), l ≫ (U y).ι = gp Y → l ≫ f y = w) → ∃ m : Y ⟶ P, (∀ y, (U y).ι ≫ m = f y) ∧ gp Y ≫ m = w := by
  first | exact @GlobalTheory.Desc.GenGlue.exists_glue | exact GlobalTheory.Desc.GenGlue.exists_glue | (intros; apply GlobalTheory.Desc.GenGlue.exists_glue <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

theorem _root_.GlobalTheory.T.exists_grpPullback_completionChart_to_extension : ∀ (X S : Scheme.{0}) (j : X ⟶ S) [IsOpenImmersion j], IsDominant j → ∀ (A : Over X) [GrpObj A] (G : Over S) [GrpObj G] (e : A.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback A G j e → ∀ (x : S) (C : Chart j A x), ∃ π : C.G.left ⟶ G.left, IsGrpPullback C.G G C.ξ π ∧ C.α ≫ e = pullback.fst C.G.hom (jK C.R) ≫ π := by
  first | exact @GlobalTheory.Desc.exists_grpPullback_chart_to_ext | exact GlobalTheory.Desc.exists_grpPullback_chart_to_ext | (intros; apply GlobalTheory.Desc.exists_grpPullback_chart_to_ext <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

theorem _root_.GlobalTheory.T.squareDecomposition_baseChange_algebraMap : ∀ (k R S : Type) [Field k] [CommRing R] [CommRing S] [Algebra k R] [Algebra k S] (ρ : R →ₐ[k] S) (A₀ : Over (Sp k)) [GrpObj A₀] (L M : LB A₀.left), L.IsLB → M.IsLB → SqDec ((Over.pullback (spMap (algebraMap k R))).obj A₀) (L.pull (pullback.fst A₀.hom (spMap (algebraMap k R)))) (M.pull (pullback.fst A₀.hom (spMap (algebraMap k R)))) → SqDec ((Over.pullback (spMap (algebraMap k S))).obj A₀) (L.pull (pullback.fst A₀.hom (spMap (algebraMap k S)))) (M.pull (pullback.fst A₀.hom (spMap (algebraMap k S)))) := by
  first | exact @GlobalTheory.SqDecBC.sqDec_baseChange | exact GlobalTheory.SqDecBC.sqDec_baseChange | (intros; apply GlobalTheory.SqDecBC.sqDec_baseChange <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

theorem _root_.GlobalTheory.T.squareDecomposition_of_baseChange_along_identity : ∀ (F : Type) [CommRing F] (A : Over (Sp F)) [GrpObj A] (L M : LB A.left), L.IsLB → M.IsLB → SqDec ((Over.pullback (spMap (RingHom.id F))).obj A) (L.pull (pullback.fst A.hom (spMap (RingHom.id F)))) (M.pull (pullback.fst A.hom (spMap (RingHom.id F)))) → SqDec A L M := by
  first | exact @GlobalTheory.SqDecIdBC.sqDec_of_baseChange_id | exact GlobalTheory.SqDecIdBC.sqDec_of_baseChange_id | (intros; apply GlobalTheory.SqDecIdBC.sqDec_of_baseChange_id <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

theorem _root_.GlobalTheory.T.transport_power_decomposition_field_extension : ∀ (k K k₁ K' : Type) [Field k] [Field K] [Field k₁] [Field K'] (a : k →+* K) (b : k →+* k₁) (c : K →+* K') (d : k₁ →+* K'), c.comp a = d.comp b → ∀ (A₀ : Over (Sp k)) [GrpObj A₀] (A : Over (Sp K)) [GrpObj A] (π : A.left ⟶ A₀.left), IsGrpPullback A A₀ (spMap a) π → ∀ (L₀ M₀ : LB A₀.left) (L M : LB A.left), L₀.IsLB → M₀.IsLB → L.IsLB → M.IsLB → LBIso L (L₀.pull π) → LBIso M (M₀.pull π) → SqDec ((Over.pullback (spMap b)).obj A₀) (L₀.pull (pullback.fst A₀.hom (spMap b))) (M₀.pull (pullback.fst A₀.hom (spMap b))) → SqDec ((Over.pullback (spMap c)).obj A) (L.pull (pullback.fst A.hom (spMap c))) (M.pull (pullback.fst A.hom (spMap c))) := by
  first | exact @GlobalTheory.SqDecTransport.transport | exact GlobalTheory.SqDecTransport.transport | (intros; apply GlobalTheory.SqDecTransport.transport <;> assumption)
end

section

open GlobalTheory.Desc

theorem _root_.GlobalTheory.T.span_image_inter_of_flat_linearlyDisjoint : ∀ (R R₁ F F₁ : Type) [CommRing R] [IsDomain R] [CommRing R₁] [Field F] [Field F₁] (ρ : R →+* R₁) (c₀ : R →+* F) (c₁ : R₁ →+* F₁) (θ : F →+* F₁), ρ.Flat → Function.Injective c₀ → θ.comp c₀ = c₁.comp ρ → LinDisj c₀ c₁ θ → ∀ (M N : Set F), (0 : F) ∈ M → (∀ a ∈ M, ∀ b ∈ M, a + b ∈ M) → (∀ r, ∀ a ∈ M, c₀ r * a ∈ M) → (0 : F) ∈ N → (∀ a ∈ N, ∀ b ∈ N, a + b ∈ N) → (∀ r, ∀ a ∈ N, c₀ r * a ∈ N) → spanBy c₁ (θ '' (M ∩ N)) = spanBy c₁ (θ '' M) ∩ spanBy c₁ (θ '' N) := by
  first | exact @GlobalTheory.Desc.spanBy_image_inter | exact GlobalTheory.Desc.spanBy_image_inter | (intros; apply GlobalTheory.Desc.spanBy_image_inter <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

theorem _root_.GlobalTheory.T.locallyOfFiniteType_near_generisation_of_point : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (f : R) (P A : Scheme.{0}) [IsIntegral P] [Nonempty A] (p : P ⟶ Sp R) (ιA : A ⟶ P) (a : A ⟶ Sp (Localization.Away f)), IsPullback ιA a p (awayMap f) → LocallyOfFiniteType a → ∀ (x : Sp R) (V : P.Opens), LocallyOfFiniteType (Limits.pullback.snd (V.ι ≫ p) ((Sp R).fromSpecStalk x)) → ∀ z : P, z ∈ V → (p z).asIdeal ≤ x.asIdeal → ∃ W : P.Opens, z ∈ W ∧ W ≤ V ∧ LocallyOfFiniteType (W.ι ≫ p) := by
  first | exact @GlobalTheory.USpread.locally_finiteType_near | exact GlobalTheory.USpread.locally_finiteType_near | (intros; apply GlobalTheory.USpread.locally_finiteType_near <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

theorem _root_.GlobalTheory.T.semiAbelian_dvr_closedFibre_stalk_uniformiser : ∀ (T : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] (H : Over (Sp T)) [GrpObj H] [IsIntegral H.left], IsSemiAbelian H → ∀ y : H.left, H.hom y = closedPoint T → ringKrullDim (H.left.presheaf.stalk y) = 1 → ∀ ϖ : T, maximalIdeal T = Ideal.span {ϖ} → GlobalTheory.Desc.cst H.hom ϖ ≠ 0 ∧ ∀ u : H.left.functionField, u ≠ 0 → ∃ (k : ℤ) (w : H.left.functionField), GlobalTheory.Cartier.UnitAt y w ∧ u = GlobalTheory.Desc.cst H.hom ϖ ^ k * w := by
  first | exact @GlobalTheory.Desc.GenFibre.unif | exact GlobalTheory.Desc.GenFibre.unif | (intros; apply GlobalTheory.Desc.GenFibre.unif <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

theorem _root_.GlobalTheory.T.squareDecomposition_descends_to_finitelyGenerated : ∀ (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] (A₀ : Over (Sp k)) [GrpObj A₀], IsAbelianScheme A₀ → ∀ (L M : LB A₀.left), L.IsLB → M.IsLB → SqDec ((Over.pullback (spMap (algebraMap k Ω))).obj A₀) (L.pull (pullback.fst A₀.hom (spMap (algebraMap k Ω)))) (M.pull (pullback.fst A₀.hom (spMap (algebraMap k Ω)))) → ∃ R : Subalgebra k Ω, R.FG ∧ SqDec ((Over.pullback (spMap (algebraMap k R))).obj A₀) (L.pull (pullback.fst A₀.hom (spMap (algebraMap k R)))) (M.pull (pullback.fst A₀.hom (spMap (algebraMap k R)))) := by
  first | exact @GlobalTheory.SqDecSpread.sqDec_fg | exact GlobalTheory.SqDecSpread.sqDec_fg | (intros; apply GlobalTheory.SqDecSpread.sqDec_fg <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

theorem _root_.GlobalTheory.T.exists_descent_morphism_to_local_scheme : ∀ (R : Type) [CommRing R] [IsDomain R] (f : R), f ≠ 0 → ∀ (x : Sp R) (S₁ B Z B₀ B₁ : Scheme.{0}) (ξ' : S₁ ⟶ Spec ((Sp R).presheaf.stalk x)), Flat ξ' → Surjective ξ' → QuasiCompact ξ' → ∀ (pB : B ⟶ Sp R) (pZ : Z ⟶ Sp R), Flat pB → IsSeparated pZ → ∀ (φ₀ : B₀ ⟶ B) (q₀ : B₀ ⟶ Sp (Localization.Away f)) (u₀ : B₀ ⟶ Z) (φ₁ : B₁ ⟶ B) (q₁ : B₁ ⟶ S₁) (u₁ : B₁ ⟶ Z), IsPullback φ₀ q₀ pB (awayMap f) → IsPullback φ₁ q₁ pB (ξ' ≫ (Sp R).fromSpecStalk x) → u₁ ≫ pZ = φ₁ ≫ pB → (∀ (T : Scheme.{0}) (t₀ : T ⟶ B₀) (t₁ : T ⟶ B₁), t₀ ≫ φ₀ = t₁ ≫ φ₁ → t₀ ≫ u₀ = t₁ ≫ u₁) → ∃ u : Limits.pullback pB ((Sp R).fromSpecStalk x) ⟶ Z, u ≫ pZ = Limits.pullback.fst _ _ ≫ pB ∧ ∀ (T : Scheme.{0}) (t₀ : T ⟶ B₀) (t : T ⟶ Limits.pullback pB ((Sp R).fromSpecStalk x)), t₀ ≫ φ₀ = t ≫ Limits.pullback.fst _ _ → t₀ ≫ u₀ = t ≫ u := by
  first | exact @GlobalTheory.Desc.exists_desc_specStalk | exact GlobalTheory.Desc.exists_desc_specStalk | (intros; apply GlobalTheory.Desc.exists_desc_specStalk <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

theorem _root_.GlobalTheory.T.grpObj_of_law_unit_inverse_agree_away : ∀ (R : Type) [CommRing R] [IsDomain R] (f g : R), f ≠ 0 → ∀ (X : Scheme.{0}) (q : X ⟶ Sp R), Flat q → IsSeparated q → ∀ (A : Over (Sp (Localization.Away f))) [GrpObj A], IsCommMonObj A → ∀ i : A.left ⟶ X, IsPullback i A.hom q (awayMap f) → ∀ (H : Over (Sp (Localization.Away g))) (h : H.left ⟶ X), IsPullback h H.hom q (awayMap g) → ∀ (m : H ⊗ H ⟶ H) (n : H ⟶ H) (o : 𝟙_ (Over (Sp (Localization.Away g))) ⟶ H), (∀ (T : Scheme.{0}) (t₁ : T ⟶ Sp (Localization.Away g)) (t₀ : T ⟶ Sp (Localization.Away f)) (a b : Over.mk t₁ ⟶ H) (a' b' : Over.mk t₀ ⟶ A), a.left ≫ h = a'.left ≫ i → b.left ≫ h = b'.left ≫ i → (lift a b ≫ m).left ≫ h = (a' * b').left ≫ i) → (∀ (T : Scheme.{0}) (t₁ : T ⟶ Sp (Localization.Away g)) (t₀ : T ⟶ Sp (Localization.Away f)) (a : Over.mk t₁ ⟶ H) (a' : Over.mk t₀ ⟶ A), a.left ≫ h = a'.left ≫ i → (a ≫ n).left ≫ h = (a'⁻¹).left ≫ i) → (∀ (T : Scheme.{0}) (t₁ : T ⟶ Sp (Localization.Away g)) (t₀ : T ⟶ Sp (Localization.Away f)), t₁ ≫ awayMap g = t₀ ≫ awayMap f → t₁ ≫ o.left ≫ h = (1 : Over.mk t₀ ⟶ A).left ≫ i) → ∃ _ : GrpObj H, MulAgree H A h i := by
  first | exact @GlobalTheory.Desc.SpreadGrp.grpObj_of_agree | exact GlobalTheory.Desc.SpreadGrp.grpObj_of_agree | (intros; apply GlobalTheory.Desc.SpreadGrp.grpObj_of_agree <;> assumption)
end
