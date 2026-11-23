module

public import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle005

@[expose] public section

section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {D : Datum H} {l : Level H} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

def WitData {k : Type} [Field k] {b : O →+* k} (a : ArcIn D l β k b)
    (P : Out.DegData (PowerSeries k) (Ideal.span {PowerSeries.X})) [Module (𝓞 E) P.toPre.X]
    (oP : letI := H.starRing; P.toPre.OAct (𝓞 E)) (φ : P.toPre.P.A.left ⟶ a.D₀.P.A.left)
    (he : eSec P.toPre.P.A ≫ φ = spMap (PowerSeries.C (R := k)) ≫ eSec a.D₀.P.A)
    (w : LB.Iso P.toPre.P.L (a.D₀.P.L.pull φ)) (e : a.D₀.X ≃ₗ[𝓞 E] P.toPre.X) : Prop :=
  letI := H.starRing
  IsGrpPullback P.toPre.P.A a.D₀.P.A (spMap (PowerSeries.C (R := k))) φ ∧ w.IsGen ∧
    LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec P.toPre.P.A) (fun _ => 1)) P.toPre.rig
      (rigPullOf φ (spMap (PowerSeries.C (R := k))) he a.D₀.P.L a.D₀.rig) ∧
    (∀ x, (oP.onB.act x).left ≫ φ = φ ≫ (a.oa.onB.act x).left) ∧
    (∀ y, (P.toPre.c (e y)).left ≫ φ = spMap (PowerSeries.C (R := k)) ≫ (a.D₀.c y).left) ∧
    ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing (PowerSeries k)) F] [Algebra (FractionRing k) F]
      (uF : F),
      (∀ x, algebraMap (FractionRing k) F (algebraMap k _ x) =
        algebraMap (FractionRing (PowerSeries k)) F (algebraMap (PowerSeries k) _ (PowerSeries.C x))) →
      uF = algebraMap (FractionRing (PowerSeries k)) F (algebraMap (PowerSeries k) _ PowerSeries.X) →
      ∀ y, GenRel w (LB.pullGen _ _ _ (P.toPre.psi (e y)) (Out.jFK (R := PowerSeries k) F))
        (LB.pullGen _ _ _ (a.D₀.psi y) (Out.jFK (R := k) F)) (uF ^ (a.be y y / 2))

def QkToAkInjSt : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), Out.AdmBase R I →
  ∀ (Dd : Out.DegData R I) (A : Out.PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G],
    IsSemiAbelian G → ∀ (U : Out.Unif I Dd A G) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F]
    (n : ℕ), 1 ≤ n → ∀ (p p' : Out.QkPt Dd.toPre F n) (x : Out.TFK (R := R) F ⟶ A.A),
      Out.QkToAkU U.toUnifPre F n p x → Out.QkToAkU U.toUnifPre F n p' x → Out.QkPt.Equiv Dd.toPre F p p'

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
end
end

section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj

structure UnramExt (V : Type) [CommRing V] where
  W : Type
  [ring : CommRing W]
  [dom : IsDomain W]
  [dvr : IsDiscreteValuationRing W]
  [alg : Algebra V W]
  fin : Module.Finite V W
  inj : Function.Injective (algebraMap V W)
  unram : Algebra.FormallyUnramified V W
  complete : IsAdicComplete (maximalIdeal W) W

attribute [instance] UnramExt.ring UnramExt.dom UnramExt.dvr UnramExt.alg

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}

abbrev ValPt.ξ (P : ValPt Y) (W : UnramExt P.V) : Sp W.W ⟶ Y.X := spMap (algebraMap P.V W.W) ≫ P.yt

def DvrDataOver (P : ValPt Y) (W : UnramExt P.V) (t : SAB H (Sp W.W)) : Prop :=
  ∃ Q : PELUnif (maximalIdeal W.W) t, (∀ y, PsiUnitOn Q.D.toPre y (P.ξ W ⁻¹' abLocus Y.t.G)) ∧ Q.TorsionIso

def SplitOver {V : Type} [CommRing V] (W : UnramExt V) (t : SAB H (Sp W.W)) : Prop :=
  ∃ S : SplitExt (Sp (ResidueField W.W)), S.IsGt ((Over.pullback (spMap (residue W.W))).obj t.G)

def DvrDataAt (P : ValPt Y) : Prop :=
  ∃ (W : UnramExt P.V) (t : SAB H (Sp W.W)) (_ : SABMap t Y.t (P.ξ W)), SplitOver W t ∧ DvrDataOver P W t

def SplitsAt (P : ValPt Y) : Prop :=
  ∃ (W : UnramExt P.V) (t : SAB H (Sp W.W)) (_ : SABMap t Y.t (P.ξ W)), SplitOver W t

private theorem comp_apply_point {A B C : Scheme.{0}} (f : A ⟶ B) (g : B ⟶ C) (x : A) :
    (f ≫ g) x = g (f x) := rfl

private theorem spMap_comp_xi_eq_spMap_lift_comp_y_comp_j (P : ValPt Y) (W : UnramExt P.V) (lift : P.K' →+* FractionRing W.W)
    (hlift : lift.comp (algebraMap P.V P.K') =
      (algebraMap W.W (FractionRing W.W)).comp (algebraMap P.V W.W)) :
    spMap (algebraMap W.W (FractionRing W.W)) ≫ P.ξ W = spMap lift ≫ P.y ≫ Y.j := by
  rw [← P.ext]
  simp only [ValPt.ξ, spMap, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hlift]

private theorem sp_nonempty_of_field (R : Type) [Field R] : Nonempty (Sp R) :=
  ⟨(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)⟩

private theorem jQ_mem_preimage_abLocus (p : Xo.XF c) :
    Y.jQ p ∈ pullback.fst Y.s (spMap β) ⁻¹' abLocus Y.t.G := by
  rw [Y.ab_gen]
  exact Set.mem_range_self _

private theorem exists_lift_fractionRing_comp_algebraMap (P : ValPt Y) (W : UnramExt P.V) :
    ∃ f : P.K' →+* FractionRing W.W, f.comp (algebraMap P.V P.K') =
      (algebraMap W.W (FractionRing W.W)).comp (algebraMap P.V W.W) := by
  haveI := P.frac
  have hinj : Function.Injective
      ((algebraMap W.W (FractionRing W.W)).comp (algebraMap P.V W.W)) := by
    rw [RingHom.coe_comp]
    exact (IsFractionRing.injective W.W (FractionRing W.W)).comp W.inj
  refine ⟨IsFractionRing.lift hinj, RingHom.ext fun x => ?_⟩
  simp only [RingHom.comp_apply, IsFractionRing.lift_algebraMap]

private theorem xi_spMap_eq_pullback_fst_jQ (P : ValPt Y) (W : UnramExt P.V) (lift : P.K' →+* FractionRing W.W)
    (hlift : lift.comp (algebraMap P.V P.K') =
      (algebraMap W.W (FractionRing W.W)).comp (algebraMap P.V W.W))
    (z : Sp (FractionRing W.W)) :
    (P.ξ W) (spMap (algebraMap W.W (FractionRing W.W)) z) =
      pullback.fst Y.s (spMap β) (Y.jQ (P.y (spMap lift z))) := by
  rw [← comp_apply_point, spMap_comp_xi_eq_spMap_lift_comp_y_comp_j P W lift hlift, comp_apply_point, comp_apply_point, Model.j, comp_apply_point]

theorem ValPt.ξ_ab (P : ValPt Y) (W : UnramExt P.V) : (P.ξ W ⁻¹' abLocus Y.t.G).Nonempty := by
  obtain ⟨lift, hlift⟩ := exists_lift_fractionRing_comp_algebraMap P W
  obtain ⟨z⟩ := sp_nonempty_of_field (FractionRing W.W)
  refine ⟨spMap (algebraMap W.W (FractionRing W.W)) z, ?_⟩
  rw [Set.mem_preimage, xi_spMap_eq_pullback_fst_jQ P W lift hlift z]
  exact Set.mem_preimage.mp (jQ_mem_preimage_abLocus (Y := Y) _)

theorem dvrData_of_splitting (h3 : Y.N3) (P : ValPt Y) (hs : SplitsAt P) : DvrDataAt P := by
  obtain ⟨W, t, m, hsp⟩ := hs
  haveI : CharZero P.K' := P.char0
  haveI : CharZero P.V := (algebraMap P.V P.K').charZero
  haveI : CharZero W.W := ⟨fun a b h => by
    apply Nat.cast_injective (R := P.V)
    apply W.inj
    simpa using h⟩
  exact ⟨W, t, m, hsp, h3 W.W inferInstance inferInstance W.complete (P.ξ W) t m (ValPt.ξ_ab P W) hsp⟩

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

namespace ReciprocityTheory.ChartRestriction.G.Chart

attribute [local instance] Over.cartesianMonoidalCategory

variable {S : Type} [CommRing S] {G : Over (Spec (CommRingCat.of S))} [GrpObj G]

def TanS {A : Type} [CommRing A] [Algebra S A] (y : sp (R₀ := S) (DualNumber A) ⟶ G) : Prop :=
  spMap (TrivSqZeroExt.fstHom S A A) ≫ y = 1

theorem tanS_restrict {A A' : Type} [CommRing A] [Algebra S A] [CommRing A'] [Algebra S A'] (j : A →ₐ[S] A')
    {y : sp (R₀ := S) (DualNumber A) ⟶ G} (hy : TanS y) : TanS (spMap (dualMapS j) ≫ y) := by
  unfold TanS at hy ⊢
  rw [← Category.assoc, spMap_comp]
  have e : (TrivSqZeroExt.fstHom S A' A').comp (dualMapS j) = j.comp (TrivSqZeroExt.fstHom S A A) := by
    refine AlgHom.ext fun x => ?_
    simp [dualMapS_fst]
  rw [e, ← spMap_comp, Category.assoc, hy, comp_one'']

theorem tanS_scale {A : Type} [CommRing A] [Algebra S A] (c : A) {y : sp (R₀ := S) (DualNumber A) ⟶ G}
    (hy : TanS y) : TanS (spMap (scaleS c) ≫ y) := by
  unfold TanS at hy ⊢
  rw [← Category.assoc, spMap_comp]
  have e : (TrivSqZeroExt.fstHom S A A).comp (scaleS c) = TrivSqZeroExt.fstHom S A A := by
    refine AlgHom.ext fun x => ?_
    simp [scaleS_fst]
  rw [e, hy]

theorem fst_restrict (s : S) (A : Type) [CommRing A] [Algebra S A] [Algebra (Localization.Away s) A]
    [IsScalarTower S (Localization.Away s) A] :
    (TrivSqZeroExt.fstHom (Localization.Away s) A A).restrictScalars S = TrivSqZeroExt.fstHom S A A := rfl

section Chart

variable {s : S} (C : Chart (Gs G s)) {A : Type} [CommRing A] [Algebra S A] [Algebra (Localization.Away s) A]
  [IsScalarTower S (Localization.Away s) A]

abbrev epsA (A : Type) [CommRing A] [Algebra (Localization.Away s) A] :
    Γ((Gs G s).left, C.U) →ₐ[Localization.Away s] A :=
  (Algebra.ofId (Localization.Away s) A).comp (eps C)

theorem tanS_chart {y : sp (R₀ := S) (DualNumber A) ⟶ G} (hy : TanS y) :
    ∃ h : Γ((Gs G s).left, C.U) →ₐ[Localization.Away s] DualNumber A, IsTanAt (epsA C A) h ∧ y = pushR G (pt C h) := by
  have hy' : pushR G (pullR (G := G) (R' := Localization.Away s) y) = y :=
    pushR_pullR (G := G) (R' := Localization.Away s) y
  have h0 : spMap (TrivSqZeroExt.fstHom (Localization.Away s) A A) ≫
      pullR (G := G) (R' := Localization.Away s) y = pt C (epsA C A) := by
    apply pushR_inj (G := G)
    rw [pushR_spMap, fst_restrict, hy', hy]
    simp only [epsA]
    rw [pt_eps, pushR_one]
  have hnil : ∀ a ∈ RingHom.ker (TrivSqZeroExt.fstHom (Localization.Away s) A A), IsNilpotent a := by
    intro a ha
    have h1 : a.fst = 0 := ha
    refine ⟨2, ?_⟩
    refine TrivSqZeroExt.ext ?_ ?_ <;> simp [pow_two, h1]
  have hcov := le_preimage_of_nil C (TrivSqZeroExt.fstHom (Localization.Away s) A A)
    (fun a => ⟨TrivSqZeroExt.inl a, by simp⟩) hnil _ (epsA C A) h0
  obtain ⟨h, hh⟩ := exists_pt C _ hcov
  refine ⟨h, ?_, ?_⟩
  · have h1 : pt C ((TrivSqZeroExt.fstHom (Localization.Away s) A A).comp h) = pt C (epsA C A) := by
      rw [← spMap_pt, ← hh, h0]
    have h2 := pt_injective C h1
    intro b
    simpa using AlgHom.congr_fun h2 b
  · rw [← hy', hh]

theorem chart_tanS (h : Γ((Gs G s).left, C.U) →ₐ[Localization.Away s] DualNumber A) (hh : IsTanAt (epsA C A) h) :
    TanS (pushR G (pt C h)) := by
  unfold TanS
  rw [← fst_restrict s A, ← pushR_spMap, spMap_pt]
  have e : (TrivSqZeroExt.fstHom (Localization.Away s) A A).comp h = epsA C A := by
    refine AlgHom.ext fun b => ?_
    simpa using hh b
  rw [e]
  simp only [epsA]
  rw [pt_eps, pushR_one]

theorem chart_inj {h₁ h₂ : Γ((Gs G s).left, C.U) →ₐ[Localization.Away s] DualNumber A}
    (e : pushR G (pt C h₁) = pushR G (pt C h₂)) : h₁ = h₂ :=
  pt_injective C (pushR_inj (G := G) e)

theorem chart_map {A' : Type} [CommRing A'] [Algebra S A'] [Algebra (Localization.Away s) A']
    [IsScalarTower S (Localization.Away s) A'] (j : A →ₐ[Localization.Away s] A')
    (h : Γ((Gs G s).left, C.U) →ₐ[Localization.Away s] DualNumber A) :
    spMap (dualMapS (j.restrictScalars S)) ≫ pushR G (pt C h) = pushR G (pt C ((dualMapS j).comp h)) := by
  rw [← spMap_pt, pushR_spMap]
  congr 2

theorem chart_scale (c : A) (h : Γ((Gs G s).left, C.U) →ₐ[Localization.Away s] DualNumber A) :
    spMap (scaleS (S := S) c) ≫ pushR G (pt C h) = pushR G (pt C ((scaleS c).comp h)) := by
  rw [← spMap_pt, pushR_spMap]
  congr 2

def upS {A' : Type} [CommRing A'] [Algebra S A'] [Algebra (Localization.Away s) A']
    [IsScalarTower S (Localization.Away s) A'] (j : A →ₐ[S] A') : A →ₐ[Localization.Away s] A' :=
  { j with
    commutes' := fun r => by
      have : (j : A →+* A').comp (algebraMap (Localization.Away s) A) = algebraMap (Localization.Away s) A' :=
        IsLocalization.ringHom_ext (Submonoid.powers s) (by
          ext a
          simp [← IsScalarTower.algebraMap_apply])
      exact RingHom.congr_fun this r }

end Chart

end ReciprocityTheory.ChartRestriction.G.Chart
end
end

section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj

private theorem res_res_lemma {X : Scheme.{0}} {U V W : X.Opens} (h : W ≤ V) (h' : V ≤ U)
    (x : Γ(X, U)ˣ) : res h (res h' x) = res (h.trans h') x := by
  have e : X.presheaf.map (homOfLE h').op ≫ X.presheaf.map (homOfLE h).op =
      X.presheaf.map (homOfLE (h.trans h')).op := by
    rw [← Functor.map_comp]
    rfl
  apply Units.ext
  exact congrArg (fun φ => φ.hom (x : Γ(X, U))) e

private theorem res_g_mul_res_g_eq_res_g_of_isLB {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (i j k : L.ι) {W : X.Opens}
    (h₁ : W ≤ L.U i ⊓ L.U j) (h₂ : W ≤ L.U j ⊓ L.U k) (h₃ : W ≤ L.U i ⊓ L.U k) :
    res h₁ (L.g i j) * res h₂ (L.g j k) = res h₃ (L.g i k) := by
  have hW : W ≤ L.U i ⊓ L.U j ⊓ L.U k := le_inf h₁ (h₂.trans inf_le_right)
  have key := congrArg (⇑(res hW)) (hL.cocycle i j k)
  simp only [map_mul, res_res_lemma] at key
  exact key

private theorem gm_res_toroidal_compactification {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) {U V : X.Opens} (h : V ≤ U)
    (hy : f y ∈ V) (x : Γ(X, U)ˣ) : gm f y V (res h x) = gm f y U x := by
  have hU : f y ∈ U := h hy
  have e : X.presheaf.map (homOfLE h).op ≫ f.app V ≫ Y.presheaf.germ (f ⁻¹ᵁ V) y hy =
      f.app U ≫ Y.presheaf.germ (f ⁻¹ᵁ U) y hU := by
    rw [← Category.assoc, Scheme.Hom.naturality, Category.assoc]
    congr 1
    exact TopCat.Presheaf.germ_res _ _ _ _
  unfold gm
  rw [dite_eq_left hy, dite_eq_left hU]
  apply Units.ext
  exact congrArg (fun φ => φ.hom (x : Γ(X, U))) e

private theorem isGen_g_iso_self_of_isLB {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) :
    (⟨fun p : L.ι × L.ι => L.g p.1 p.2⟩ : LB.Iso L L).IsGen := by
  rintro ⟨p₁, p₂⟩ ⟨q₁, q₂⟩
  have h₀ : L.U p₁ ⊓ L.U p₂ ⊓ (L.U q₁ ⊓ L.U q₂) ≤ L.U p₁ ⊓ L.U p₂ := inf_le_left
  have h₁ : L.U p₁ ⊓ L.U p₂ ⊓ (L.U q₁ ⊓ L.U q₂) ≤ L.U p₁ ⊓ L.U q₁ :=
    le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)
  have h₂ : L.U p₁ ⊓ L.U p₂ ⊓ (L.U q₁ ⊓ L.U q₂) ≤ L.U q₁ ⊓ L.U q₂ := inf_le_right
  have h₃ : L.U p₁ ⊓ L.U p₂ ⊓ (L.U q₁ ⊓ L.U q₂) ≤ L.U p₁ ⊓ L.U q₂ :=
    le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_right)
  have h₄ : L.U p₁ ⊓ L.U p₂ ⊓ (L.U q₁ ⊓ L.U q₂) ≤ L.U p₂ ⊓ L.U q₂ :=
    le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)
  have c₁ := res_g_mul_res_g_eq_res_g_of_isLB hL p₁ q₁ q₂ h₁ h₂ h₃
  have c₂ := res_g_mul_res_g_eq_res_g_of_isLB hL p₁ p₂ q₂ h₀ h₄ h₃
  have key : res h₀ (L.g p₁ p₂) =
      res h₁ (L.g p₁ q₁) * (res h₄ (L.g p₂ q₂))⁻¹ * res h₂ (L.g q₁ q₂) := by
    rw [mul_right_comm, c₁, ← c₂, mul_inv_cancel_right]
  exact key

private theorem gm_g_mul_gm_g_swap_eq_one_of_isLB {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) (f : Y ⟶ X) (y : Y)
    {i j : L.ι} (hi : f y ∈ L.U i) (hj : f y ∈ L.U j) :
    gm f y (L.U j ⊓ L.U i) (L.g j i) * gm f y (L.U i ⊓ L.U j) (L.g i j) = 1 := by
  have hW : f y ∈ L.U j ⊓ L.U i := ⟨hj, hi⟩
  have h₂ : L.U j ⊓ L.U i ≤ L.U i ⊓ L.U j := le_of_eq (inf_comm _ _)
  have h₃ : L.U j ⊓ L.U i ≤ L.U j ⊓ L.U j := le_inf inf_le_left inf_le_left
  rw [← gm_res_toroidal_compactification f y h₂ hW (L.g i j), ← gm_res_toroidal_compactification f y (le_refl (L.U j ⊓ L.U i)) hW (L.g j i),
    ← map_mul (gm f y (L.U j ⊓ L.U i)), res_g_mul_res_g_eq_res_g_of_isLB hL j i j (le_refl _) h₂ h₃,
    ← res_res_lemma (inf_le_left : L.U j ⊓ L.U i ≤ L.U j) (le_inf le_rfl le_rfl : L.U j ≤ L.U j ⊓ L.U j),
    hL.g_self]
  simp only [map_one]

theorem exists_iso_pair_of_eq {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {L₁ L₂ : RigLB G}
    (h : L₁ = L₂) :
    ∃ (w : LB.Iso L₁.L L₂.L) (w' : LB.Iso L₂.L L₁.L), w.IsGen ∧ w'.IsGen ∧
      LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec G) (fun _ => 1)) L₁.rig L₂.rig ∧
      LB.Gen.Maps (LB.linCombIso w' (K := PUnit) (fun _ => eSec G) (fun _ => 1)) L₂.rig L₁.rig ∧
      ∀ {Y : Scheme.{0}} (f : Y ⟶ G.left) (y : Y) (i : L₁.L.ι) (j : L₂.L.ι), f y ∈ L₁.L.U i → f y ∈ L₂.L.U j →
        gv w f y j i * gv w' f y i j = 1 := by
  cases h
  refine ⟨⟨fun p : L₁.L.ι × L₁.L.ι => L₁.L.g p.1 p.2⟩, ⟨fun p : L₁.L.ι × L₁.L.ι => L₁.L.g p.1 p.2⟩,
    isGen_g_iso_self_of_isLB L₁.isLB, isGen_g_iso_self_of_isLB L₁.isLB, ?_, ?_, ?_⟩
  · intro p
    exact L₁.rigGen p.1 p.2
  · intro p
    exact L₁.rigGen p.1 p.2
  · intro Y f y i j hi hj
    exact gm_g_mul_gm_g_swap_eq_one_of_isLB L₁.isLB f y hi hj

section Lev

open ReciprocityTheory.ChartRestriction.G.Out

end Lev

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
end
end

section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped Pointwise

def QkExtExistsSt : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] (D : Out.DegPre R) (F F' : Type) [Field F] [Algebra (FractionRing R) F]
    [Field F'] [Algebra (FractionRing R) F'] (f : F →+* F'),
    (∀ r : FractionRing R, f (algebraMap _ F r) = algebraMap _ F' r) →
    ∀ (k : ℕ) (p : Out.QkPt D F k), ∃ p' : Out.QkPt D F' k, QkExt f p p'

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
end
end
