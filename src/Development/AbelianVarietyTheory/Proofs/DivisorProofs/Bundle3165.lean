module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle077
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle076
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PrimitiveCocycle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2927
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2958
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2980
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2932
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3104
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1622
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun

@[expose] public section

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
open GlobalTheory.Points


open GlobalTheory.ZH.RatModel in
theorem Tower.valF_app_p {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}
    {X₁ : Setup F W i} {act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)} (𝔗 : Tower X₁ act)
    {U : X₁.M.Z.Opens} (hU : (U : Set X₁.M.Z).Nonempty) (a : Γ(X₁.M.Z, U)) :
    valF 𝔗.X₂.M.pt (𝔗.p ⁻¹ᵁ U) (𝔗.p.app U a) = algebraMap X₁.Ω₁ 𝔗.X₂.Ω₁ (valF X₁.M.pt U a) := by
  refine (valR_comp 𝔗.X₂.M.pt 𝔗.p U a).symm.trans ?_
  rw [𝔗.p_pt]
  exact valR_spMap_comp _ X₁.M.pt U (X₁.M.top_le_preimage_pt hU) a

theorem Tower.stalkHom_stalkMap_p {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}}
    {i : F.X ⟶ Z} {X₁ : Setup F W i} {act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)} (𝔗 : Tower X₁ act)
    (z₂ : 𝔗.X₂.M.Z) (x : X₁.M.Z.presheaf.stalk (𝔗.p z₂)) :
    𝔗.X₂.M.stalkHom z₂ (𝔗.p.stalkMap z₂ x) = algebraMap X₁.Ω₁ 𝔗.X₂.Ω₁ (X₁.M.stalkHom (𝔗.p z₂) x) := by
  obtain ⟨U, hz, f, rfl⟩ := X₁.M.Z.presheaf.germ_exist x
  rw [Scheme.Hom.germ_stalkMap_apply, RatModel.stalkHom_germ hz f]
  exact (RatModel.stalkHom_germ (M := 𝔗.X₂.M) (U := 𝔗.p ⁻¹ᵁ U) hz _).trans (𝔗.valF_app_p ⟨_, hz⟩ f)

theorem Tower.val_comp_p {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}}
    {i : F.X ⟶ Z} {X₁ : Setup F W i} {act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)} (𝔗 : Tower X₁ act)
    {K : Type} [Field K] (y : Sp K ⟶ 𝔗.X₂.M.Z) (w : Sp K) {x : X₁.Ω₁} (hx : x ∈ X₁.M.O (𝔗.p (y w))) :
    X₁.M.val (y ≫ 𝔗.p) x = 𝔗.X₂.M.val y (algebraMap X₁.Ω₁ 𝔗.X₂.Ω₁ x) := by
  obtain ⟨U, a, hz, rfl⟩ := hx
  have h1 : Set.range y ⊆ (𝔗.p ⁻¹ᵁ U : 𝔗.X₂.M.Z.Opens) := by
    rw [RatModel.range_eq_singleton y w, Set.singleton_subset_iff]
    exact hz
  rw [← 𝔗.valF_app_p ⟨_, hz⟩ a, RatModel.val_valF h1,
    RatModel.val_valF (U := U) (by rintro _ ⟨w', rfl⟩; exact h1 ⟨w', rfl⟩)]
  exact valR_comp y 𝔗.p U a

theorem RatModel.val_spMap_comp_field {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M : RatModel o Ω} {K K' : Type} [Field K]
    [Field K'] (σ : K →+* K') (y : Sp K ⟶ M.Z) (w : Sp K) {x : Ω} (hx : x ∈ M.O (y w)) :
    M.val (spMap σ ≫ y) x = σ (M.val y x) := by
  obtain ⟨U, g, hz, rfl⟩ := hx
  have h1 : Set.range y ⊆ U := by
    rw [RatModel.range_eq_singleton y w, Set.singleton_subset_iff]
    exact hz
  rw [RatModel.val_valF h1, RatModel.val_valF (by rintro _ ⟨w', rfl⟩; exact h1 ⟨_, rfl⟩)]
  exact valR_spMap_comp σ y U ((top_le_preimage_iff _ _).2 h1) g

theorem Tower.val_om_ext : ∀ {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z} {X₁ : Setup F W i} {act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)} (𝔗 : Tower X₁ act) {z₁ : X₁.M.Z} {z₂ : 𝔗.X₂.M.Z}, 𝔗.p z₂ = z₁ → ∀ {V V' : Type} [CommRing V] [IsDomain V] [CommRing V'] [IsDomain V'] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (io : V →+* V') (ev₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V') (f : FractionRing V →+* FractionRing V'), (∀ v, f (algebraMap V (FractionRing V) v) = algebraMap V' (FractionRing V') (io v)) → Function.Injective io → 𝔗.Ext ev io ev₂ → RegAt X₁ z₁ ev → ∀ a : X₁.S.R, 𝔗.X₂.M.val (jK V' ≫ spMap ev₂ ≫ 𝔗.X₂.M.Z.fromSpecStalk z₂) (𝔗.om a) = f (X₁.M.val (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) a) := by
  intro g n F W Z i X₁ act 𝔗 z₁ z₂ hz V V' _ _ _ _ ev io ev₂ f hf hio hext hreg a
  subst hz
  have e1 : ev₂.comp (𝔗.p.stalkMap z₂).hom = io.comp ev :=
    RingHom.ext fun x => hext.2 x _ (𝔗.stalkHom_stalkMap_p z₂ x)
  have e2 : jK V' ≫ spMap io = spMap f ≫ jK V := by
    simp only [jK, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext v
    exact (hf v).symm
  have h1 : (jK V' ≫ spMap ev₂ ≫ 𝔗.X₂.M.Z.fromSpecStalk z₂) ≫ 𝔗.p =
      spMap f ≫ (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk (𝔗.p z₂)) := by
    have e3 : spMap ev₂ ≫ Spec.map (𝔗.p.stalkMap z₂) = spMap io ≫ spMap ev := by
      show Spec.map (CommRingCat.ofHom ev₂) ≫ Spec.map (CommRingCat.ofHom (𝔗.p.stalkMap z₂).hom) = _
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, e1, CommRingCat.ofHom_comp, Spec.map_comp]
    rw [Category.assoc, Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk, ← Category.assoc (spMap ev₂), e3,
      Category.assoc, ← Category.assoc (jK V'), e2]
    simp only [Category.assoc]
  have hmem := hreg a a.2
  have hp : 𝔗.p ((jK V' ≫ spMap ev₂ ≫ 𝔗.X₂.M.Z.fromSpecStalk z₂) (closedPoint (FractionRing V'))) =
      (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk (𝔗.p z₂)) (closedPoint (FractionRing V)) := by
    have e := congrArg (fun q : Sp (FractionRing V') ⟶ X₁.M.Z => q (closedPoint (FractionRing V'))) h1
    refine e.trans ?_
    show (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk (𝔗.p z₂)) ((spMap f) (closedPoint (FractionRing V'))) = _
    rw [Subsingleton.elim ((spMap f) (closedPoint (FractionRing V'))) (closedPoint (FractionRing V))]
  rw [𝔗.om_eq, ← 𝔗.val_comp_p (K := FractionRing V') _ (closedPoint (FractionRing V')) (hp ▸ hmem), h1,
    RatModel.val_spMap_comp_field (K := FractionRing V) f _ (closedPoint (FractionRing V)) hmem]

end GlobalTheory.Poinc.Sep
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UCanon

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem toUnit_left_eq' {X : Scheme.{0}} (T : Over X) : (toUnit T).left = T.hom := by
  have := Over.w (toUnit T)
  simpa using this

theorem grpPullback_pow_succ {S S' : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (hφ : IsGrpPullback G' G f φ) {T : Over S'} (x : T ⟶ G')
    (x₀ : Over.mk (T.hom ≫ f) ⟶ G) (hx : x₀.left = x.left ≫ φ) (n : ℕ) :
    (x₀ ^ (n + 1)).left = (x ^ (n + 1)).left ≫ φ := by
  induction n with
  | zero => simpa using hx
  | succ n ih =>
    rw [pow_succ x₀, pow_succ x]
    exact hφ.2 T _ _ _ _ ih hx

theorem eta_eq_etaA_pow {D : Datum H} {l : Geo.Tor.Level H} {B : Type} [CommRing B] {bb : Base (LowDat.lowLevel l) B}
    {S : Scheme.{0}} {s : S ⟶ Sp B} (o : Obj D (LowDat.lowLevel l) bb s) (k : Type) [Field k] [IsAlgClosed k]
    (x : Sp k ⟶ S) (β : B →+* k) (hx : x ≫ s = spMap β) (a : D.La)
    (ha : a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La)) :
    toUnit (Over.mk x) ≫ o.eta a = (toUnit (Over.mk x) ≫ o.etaA a) ^ (l.M' / l.M) := by
  obtain ⟨-, I, -, hA, hM⟩ := o.geom k x β hx
  have hM0 : 0 < l.M := by have := l.three_le; omega
  have hdvd : l.M ∣ l.M' := Nat.dvd_lcm_left l.M l.A
  have hM'0 : 0 < l.M' := Nat.lcm_pos hM0 l.A_pos
  have hq : 0 < l.M' / l.M := Nat.div_pos (Nat.le_of_dvd hM'0 hdvd) hM0
  have hmul : l.M * (l.M' / l.M) = (LowDat.lowLevel l).A := Nat.mul_div_cancel' hdvd
  rw [hM a ha, hA a, ← hmul]
  exact (I.tower l.M (l.M' / l.M) hM0 hq a).symm

end GlobalTheory.UCanon

namespace GlobalTheory.UCanon

theorem sabMap_keeps_eta : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H} (c : Coeff l) (A W : Type) [CommRing A] [IsDomain A] [CommRing W] (bA : c.F →+* A) (b : c.F →+* W) (o' : LowObj D c bA) (o : LowObj D c b) (f : W →+* A), f.comp b = bA → ∀ m : SABMap o'.t o.t (spMap f), (∀ a, (o'.etaA a).left ≫ m.φ = spMap f ≫ (o.etaA a).left) → ∀ a, (o'.eta a).left ≫ m.φ = spMap f ≫ (o.eta a).left := by
  intro E _ _ _ H D l c A W _ _ _ bA b o' o f hf m hA a
  subst hf

  have h1 : (1 : 𝓞 E) ∈ l.Mb ⊔ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by rw [l.coprime]; exact Submodule.mem_top
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.1 h1
  have ha : u • a + v • a = a := by rw [← add_smul, huv, one_smul]
  have hu' : u • a ∈ (LowDat.lowLevel l).Mb • (⊤ : Submodule (𝓞 E) D.La) :=
    Submodule.smul_mem_smul hu Submodule.mem_top
  have hv' : v • a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La) :=
    Submodule.smul_mem_smul hv Submodule.mem_top
  have e1 : o'.eta a = o'.eta (v • a) := by
    conv_lhs => rw [← ha]
    rw [o'.eta_add, o'.eta_ker _ hu', _root_.one_mul]
  have e2 : o.eta a = o.eta (v • a) := by
    conv_lhs => rw [← ha]
    rw [o.eta_add, o.eta_ker _ hu', _root_.one_mul]
  rw [e1, e2]
  generalize v • a = a' at hv' ⊢

  let K := AlgebraicClosure (FractionRing A)
  let κ : A →+* K := (algebraMap (FractionRing A) K).comp (algebraMap A (FractionRing A))
  have hκ : Function.Injective κ :=
    (algebraMap (FractionRing A) K).injective.comp (IsFractionRing.injective A (FractionRing A))
  haveI : IsDominant (spMap κ) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical κ).2 (by
    rw [(RingHom.injective_iff_ker_eq_bot _).1 hκ]; exact bot_le)⟩
  haveI := o.proper
  haveI : IsReduced (𝟙_ (Over (Sp A))).left := (inferInstance : IsReduced (Sp A))
  refine ext_of_isDominant_of_isSeparated o.t.G.hom ?_ (spMap κ) ?_
  · have w1 := Over.w (o'.eta a')
    have w2 := Over.w (o.eta a')
    have w3 := m.cart.1.w
    simp only [Category.assoc]
    rw [w3, ← Category.assoc, w1, w2]
    simp
  · let β : KA (LowDat.lowLevel l) →+* K := κ.comp ((f.comp b).comp (IntermediateField.inclusion (LowDat.ka_le l c)).toRingHom)
    have hx' : spMap κ ≫ lowMap c (f.comp b) = spMap β := by
      unfold lowMap; rw [← Spec.map_comp]; rfl
    have hx : (spMap κ ≫ spMap f) ≫ lowMap c b = spMap β := by
      unfold lowMap; rw [← Spec.map_comp, ← Spec.map_comp]; rfl
    have p' := eta_eq_etaA_pow o' K (spMap κ) β hx' a' hv'
    have p := eta_eq_etaA_pow o K (spMap κ ≫ spMap f) β hx a' hv'
    have hM0 : 0 < l.M := by have := l.three_le; omega
    have hdvd : l.M ∣ l.M' := Nat.dvd_lcm_left l.M l.A
    have hq : 0 < l.M' / l.M := Nat.div_pos (Nat.le_of_dvd (Nat.lcm_pos hM0 l.A_pos) hdvd) hM0
    obtain ⟨n, hn⟩ : ∃ n, l.M' / l.M = n + 1 := ⟨l.M' / l.M - 1, by omega⟩
    rw [hn] at p p'
    have key := grpPullback_pow_succ m.cart (T := Over.mk (spMap κ)) (toUnit _ ≫ o'.etaA a')
      (toUnit (Over.mk (spMap κ ≫ spMap f)) ≫ o.etaA a') (by
        rw [Over.comp_left, Over.comp_left, toUnit_left_eq', toUnit_left_eq']
        simp only [Over.mk_hom, Category.assoc]
        rw [hA a']) n
    have q' := congrArg Over.Hom.left p'
    have q := congrArg Over.Hom.left p
    rw [Over.comp_left, toUnit_left_eq'] at q q'
    simp only [Over.mk_hom] at q q'
    rw [← Category.assoc, q', ← key, ← q, Category.assoc]

end GlobalTheory.UCanon
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon GlobalTheory.PolDeg GlobalTheory.TInj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TInjBase

theorem val_eq_of_injective {X Y Y₀ : Scheme.{0}} {M : LB X} (hM : M.IsLB) {K K' : Type} [Fintype K] [Fintype K']
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ} (hF : FormEq φ ε φ' ε')
    (e : Y₀ ⟶ Y) (he : Function.Injective e.appTop.hom)
    {u : LB.Gen (LB.LinComb M φ ε)} {u' : LB.Gen (LB.LinComb M φ' ε')} (hu : u.IsGen) (hu' : u'.IsGen)
    (h : ∀ y J, Good M y J → val u e y J = val u' e y J) (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J) (hJ : Good M z J) :
    val u r z J = val u' r z J := by
  obtain ⟨t, -, hv⟩ := exists_gen hM (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ h => by
      refine (Fintype.prod_sum_type _).trans (Eq.trans ?_ (Fintype.prod_empty _).symm)
      simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib, hF U h, mul_inv_cancel])
    (LB.mulGen M _ _ _ _ u (LB.invGen M _ _ u')) (DVR.mulGen_isGen _ _ _ _ _ _ _ hu (DVR.invGen_isGen _ _ _ _ hu'))
  have le : (⊤ : Y.Opens) ≤ LB.wchart M (PEmpty.elim : PEmpty → (Y ⟶ X)) PEmpty.elim := fun _ _ =>
    Set.mem_iInter.2 fun k => k.elim
  obtain ⟨a, ha⟩ : ∃ a, a = (res le (t.s PEmpty.elim)).val := ⟨_, rfl⟩
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good M z J →
      (val u r z J * (val u' r z J)⁻¹).val = gs r z ⊤ a := by
    intro Z r z J hJ
    rw [← val_inv, ← val_mul hJ, ← hv Z r z J hJ, val_of t r z J PEmpty.elim (fun k => k.elim)]
    exact (congrArg Units.val (gm_res r z le trivial _)).symm.trans ((gs_unit r z ⊤ trivial _).symm.trans
      (congrArg (gs r z ⊤) ha.symm))
  have a1 : a = 1 := he ((fn_ext (V := ⊤) fun y _ => by
    choose I hI using fun χ : Y₀ ⟶ X => exists_chart hM (χ y)
    have := key _ e y I hI
    rw [h y I hI, mul_inv_cancel] at this
    refine (gs_pull (𝟙 Y₀) e y ⊤ trivial a).trans ?_
    rw [Category.id_comp, ← this, gs_eq _ y ⊤ trivial, map_one, map_one, Units.val_one]).trans (map_one _).symm)
  have := key Z r z J hJ
  rw [a1, gs_eq _ z ⊤ trivial, map_one, map_one] at this
  exact mul_inv_eq_one.1 (Units.ext this)

theorem exists_gens {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (hB : D.TauBimult)
    (hU : ∀ y, PsiUnitOn D y Set.univ) :
    ∃ τ : ∀ a b : D.X, LB.Gen (LB.LinComb D.P.L (lamPts (D.c a) (D.c b)) negε), (∀ a b, (τ a b).IsGen) ∧
      (∀ a b z J, Good D.P.L z J → val (τ a b) (𝟙 _) z J = val (τ b a) (𝟙 _) z J) ∧
      (∀ a a' b z J, Good D.P.L z J → val (τ (a + a') b) (𝟙 _) z J * cubV D.cub z J (D.c a) (D.c a') (D.c b) =
        val (τ a b) (𝟙 _) z J * val (τ a' b) (𝟙 _) z J) ∧
      ∀ a b z J, Good D.P.L z J → val (D.tau a b) (𝟙 _) z J = val (τ a b) (toUnit (TK R)).left z J := by
  obtain ⟨τ₀, h₀⟩ := GlobalTheory.DDataGens.main R D hB hU
  have cadd : ∀ a b, D.c (a + b) = D.c a * D.c b := D.c_add
  have c0 : D.c 0 = 1 := mul_eq_left.1 ((cadd 0 0).symm.trans (by rw [add_zero]))
  have ex : ∀ a b : D.X, ∃ t : LB.Gen (LB.LinComb D.P.L (lamPts (D.c a) (D.c b)) negε), t.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ _) (z : Z) (J), Good D.P.L z J → val t r z J = val (τ₀ a b) r z J := fun a b =>
    exists_gen D.P.isLB (fun U _ h => by
      simp [lamPts, negε, Fin.prod_univ_four, cadd, c0]) (τ₀ a b) (h₀ a b).1
  choose τ hτ hv using ex
  have hK : ∀ a b z J, Good D.P.L z J → val (D.tau a b) (𝟙 _) z J = val (τ a b) (toUnit (TK R)).left z J :=
    fun a b z J hJ => ((h₀ a b).2 z J hJ).trans (hv a b _ _ z J hJ).symm
  have inj : Function.Injective (toUnit (TK R)).left.appTop.hom := by
    rw [GlobalTheory.DDataGens.toUnit_TK_left]
    have nat := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R)))
    intro x y hxy
    refine (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.injective
      (IsFractionRing.injective R (FractionRing R) ?_)
    exact (congrArg (fun g => g.hom x) nat).symm.trans
      ((congrArg (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom hxy).trans (congrArg (fun g => g.hom y) nat))
  refine ⟨τ, hτ, fun a b z J hJ => ?_, fun a a' b z J hJ => ?_, hK⟩
  · refine val_eq_of_injective D.P.isLB (fun U _ h => ?_) _ inj (hτ a b) (hτ b a) (fun y J hJ => ?_) _ _ z J hJ
    · simp only [Fin.prod_univ_four, lamPts, negε, mul_comm (D.c b) (D.c a)]
      simp [mul_right_comm]
    · exact (hK a b y J hJ).symm.trans ((GlobalTheory.TauTwist.val_tau_symm (𝟙 (TK R)) hJ a b).trans (hK b a y J hJ))
  · have key := val_eq_of_injective D.P.isLB (fun U _ h => ?_) _ inj
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (hτ (a + a') b)
        (DVR.pullGen_isGen _ _ _ _ D.cub.isGen (lift (D.c a) (lift (D.c a') (D.c b))).left))
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (hτ a b) (hτ a' b)) (fun y J hJ => ?_) _ (𝟙 _) z J hJ
    · refine Eq.trans ?_ (key.trans (val_mul hJ _ _ _))
      refine Eq.trans ?_ (val_mul hJ _ _ _).symm
      refine congrArg (_ * ·) ?_
      have := val_cub D.cub (𝟙 (𝟙_ (Over (Sp R)))) hJ (D.c a) (D.c a') (D.c b)
      simp only [Category.id_comp] at this
      exact this.symm
    · refine ((Fintype.prod_sum_type _).trans (congrArg₂ (· * ·) rfl (prod_cub (D.c a) (D.c a') (D.c b) h))).trans ?_
      rw [Fintype.prod_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_four, lamPts, negε, cadd]
      apply Additive.ofMul.injective
      simp [ofMul_mul, ofMul_inv]
      abel
    · refine (val_mul hJ _ _ _).trans (Eq.trans ?_ (val_mul hJ _ _ _).symm)
      rw [← hK _ _ y J hJ, ← hK _ _ y J hJ, ← hK _ _ y J hJ]
      exact (congrArg (_ * ·) (val_cub D.cub (toUnit (TK R)) hJ _ _ _)).trans
        (GlobalTheory.TauTwist.val_tau_add (𝟙 (TK R)) hJ hB a a' b)

theorem val_trans {S : Scheme.{0}} {B : Over S} [GrpObj B] [IsCommMonObj B] {L : LB B.left} (hL : L.IsLB) {T T' : Over S}
    (ρ : T' ⟶ T) (x y : T ⟶ B) {t : LB.Gen (LB.LinComb L (lamPts x y) negε)} (ht : t.IsGen) (z : T'.left) {J J'}
    (hJ : Good L z J) (hJ' : Good L z J') :
    val t ρ.left z J' = lamVal (Wit.idPull (abelian₂ B L)) (lift (ρ ≫ x) (ρ ≫ y)).left z J J' * val t ρ.left z J := by
  refine (gen_trans ht ρ.left z (hJ'.mem _ _) (hJ.mem _ _)).trans (congrArg (· * _) ?_)
  have hm : ∀ {J}, Good L z J → (lift (ρ ≫ x) (ρ ≫ y)).left z ∈ (abelian₂ B L).U
    (fun I => J ((lift (ρ ≫ x) (ρ ≫ y)).left ≫ (psum B (x2 B) I.down).left)) := fun hJ => hJ.mem _ _
  refine Eq.trans ?_ (Wit.gw_idPull (abelian₂ B L) _ z _ _ (hm hJ) (hm hJ')).symm
  refine Eq.trans ?_ (gm_linComb L _ _ _ z _ _ (hm hJ) (hm hJ')).symm
  refine Eq.trans ?_ (GlobalTheory.PrimCocycle.prod_lam (ρ ≫ x) (ρ ≫ y) (fun q => gm q z _ (L.g (J q) (J' q)))).symm
  have inv : ∀ q, gm q z _ (L.g (J' q) (J q)) = (gm q z _ (L.g (J q) (J' q)))⁻¹ := fun q =>
    eq_inv_of_mul_eq_one_left ((gm_cocycle hL q z (hJ' q) (hJ q) (hJ' q)).trans (gm_self hL q z (hJ' q)))
  refine (Finset.prod_congr rfl fun k _ => congrArg (· ^ negε k) (inv (_ ≫ _))).trans ?_
  refine Eq.trans (Finset.prod_congr rfl fun k _ => ?_)
    (Wit.prod_neg_lamPts _ _ (fun q => gm q z _ (L.g (J q) (J' q))))
  have : ρ.left ≫ lamPts x y k = 𝟙 _ ≫ lamPts (ρ ≫ x) (ρ ≫ y) k := by
    rw [Category.id_comp]
    fin_cases k
    · exact congrArg (fun q : T' ⟶ B => q.left) (MonObj.comp_mul ρ _ _)
    · rfl
    · rfl
    · exact congrArg (fun q : T' ⟶ B => q.left) (MonObj.comp_one ρ)
  exact congrArg (fun q => (gm q z _ (L.g (J q) (J' q)))⁻¹ ^ negε k) this

theorem main : ∀ {o W : Type} [CommRing o] [CommRing W] [IsDomain W] [IsLocalRing W] (b : o →+* W) (D : DegPre W), D.TauBimult → (∀ y, PsiUnitOn D y Set.univ) → ∀ n : ℕ, ∃ (T : TautBase o W) (ib : D.X ≃+ (Fin T.r → ℤ)) (β : D.P.A.left ⟶ T.B.left) (ββ : (G2 D.P.A).left ⟶ (G2 T.B).left) (w : LB.Iso (abelian₂ D.P.A D.P.L) ((abelian₂ T.B T.M.L).pull ββ)), From T (RingHom.id W) (fun _ : Empty => (1 : W)) (fun _ => 0) n (mulDeg D n) ib β ββ w := by
  intro o W _ _ _ _ b D hB hU n
  obtain ⟨τ, hg, hs, ha, hK⟩ := exists_gens D hB hU
  obtain ⟨ib⟩ : Nonempty (D.X ≃+ (Fin (Module.finrank ℤ D.X) → ℤ)) := ⟨(Module.finBasis ℤ D.X).equivFun.toAddEquiv⟩
  have hid : spMap (RingHom.id W) = 𝟙 (Sp W) := Spec.map_id _
  have hn : ∀ a : D.X, ib.symm ((n : ℤ) • ib a) = n • a := fun a => by
    rw [map_zsmul, ib.symm_apply_apply, natCast_zsmul]
  let T : TautBase o W :=
    { b := b
      B := D.P.A
      comm := D.P.isAb.comm
      isAb := D.P.isAb
      g := D.P.g
      smoothDim := D.P.smoothDim
      M := ⟨D.P.L, D.rig, D.P.isLB, D.rig_gen⟩
      cub := D.cub
      ample := D.P.ample
      ktriv := D.P.ktriv
      r := Module.finrank ℤ D.X
      c₀ := fun a => D.c (ib.symm a)
      c₀_add := fun a a' => by rw [map_add (f := _)]; exact D.c_add _ _
      τ₀ := fun a a' => τ (ib.symm a) (ib.symm a')
      τ₀_gen := fun a a' => hg _ _
      τ₀_symm := fun a a' => hs _ _
      τ₀_add := fun a a' a'' z J hJ => (congrArg (fun x => val (τ x (ib.symm a'')) (𝟙 _) z J * _) (map_add ib.symm a a')).trans
        (ha _ _ _ z J hJ) }
  letI : IsEmpty Empty := Empty.instIsEmpty
  refine ⟨T, ib, 𝟙 _, 𝟙 _, Wit.idPull _, ?_, ⟨(Category.id_comp _).trans (Category.comp_id _).symm,
    (Category.id_comp _).trans (Category.comp_id _).symm⟩, Wit.idPull_isGen (DVR.linComb_isLB _ D.P.isLB _ _), fun a => ?_,
    fun (a b : D.X) => ⟨1, by simp, fun z J J' hJ hJ' => ?_⟩⟩
  · rw [hid]
    exact Wit.grpPullback_id D.P.A
  · rw [hid]
    exact (Category.comp_id _).trans ((congrArg (fun x => (D.c x).left) (hn a).symm).trans (Category.id_comp _).symm)
  · have e₁ : val ((mulDeg D n).tau a b) (𝟙 _) z J' = val (D.tau (n • a) (n • b)) (𝟙 _) z J' := by
      refine (GlobalTheory.TauTwist.val_tau (mulDeg D n) a b _ hJ').trans (Eq.trans ?_ (GlobalTheory.TauTwist.val_tau D _ _ _ hJ').symm)
      rw [← nsmul_add]
      rfl
    have e₂ : val (T.τ₀ ((n : ℤ) • ib a) ((n : ℤ) • ib b)) ((TK W).hom ≫ spMap (RingHom.id W)) z J =
        val (τ (n • a) (n • b)) (toUnit (TK W)).left z J := by
      rw [hid, Category.comp_id, GlobalTheory.DDataGens.toUnit_TK_left]
      exact congrArg₂ (fun x y => val (τ x y) (jK W) z J) (hn a) (hn b)
    have e₃ : gm (𝟙 (TK W).left) z ⊤ (unitOn (1 : (FractionRing W)ˣ)) = 1 := (congrArg (gm (𝟙 (TK W).left) z ⊤) (map_one _)).trans (map_one _)
    refine e₁.trans ((hK _ _ z J' hJ').trans (Eq.trans ?_ (congrArg₂ (· * ·) e₃ (congrArg (_ * ·) e₂)).symm))
    rw [_root_.one_mul]
    exact val_trans D.P.isLB (toUnit (TK W)) _ _ (hg (n • a) (n • b)) z hJ hJ'

end GlobalTheory.TInjBase
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UCanon.DivIso

theorem exists_isPullDeg_id : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] (Q : DegPre V) [Module (𝓞 E) Q.X] (oQ : letI := H.starRing; Q.OAct (𝓞 E)) (Q' : DegPre V) [Module (𝓞 E) Q'.X] (oQ' : letI := H.starRing; Q'.OAct (𝓞 E)) (iw : L.W →+* V) {I : Type} [Fintype I] (s : I → V) (ε : I → LinearMap.BilinForm ℤ L.D.X) (e : Q.X ≃ₗ[𝓞 E] L.D.X) (e' : Q'.X ≃ₗ[𝓞 E] L.D.X), (∀ k, s k ≠ 0) → DivFrom L Q oQ iw s ε e → DivFrom L Q' oQ' iw s ε e' → ∃ hD : IsPullDeg (RingHom.id V) Q Q', (∀ y, e (hD.xe y) = e' y) ∧ (letI := H.starRing; ∀ x, oQ'.onB.act x ≫ hD.e.hom = hD.e.hom ≫ (Over.pullback (specOf (RingHom.id V))).map (oQ.onB.act x)) := by
  intro E _ _ _ H D' l c L V _ _ _ Q _ oQ Q' _ oQ' iw I _ s ε e e' hs ⟨g, p, hg, hx, ha⟩ ⟨g', p', hg', hx', ha'⟩
  letI := H.starRing
  obtain ⟨q, q₁, q₂⟩ := GlobalTheory.PullDegTop.main.2.2.2 (RingHom.id_comp iw) p p' (fun y => L.gen (l.M' • y))
  have he : ∀ y : Q'.X, e (q.xe y) = e' y := fun y => (hx _).symm.trans ((q₂ y).trans (hx' y))
  obtain ⟨r, r₁, r₂⟩ := GlobalTheory.PullDegResc.main.2.1 g g' q s hs (fun y k => (l.M' : ℤ) * ε k (e y) (H.w0 • e y)) hg
    (fun x => (hg' x).trans (Finset.prod_congr rfl fun k _ => by rw [← he x]; rfl))
  refine ⟨r, fun y => (congrArg e (r₂ y)).trans (he y), fun x => (GlobalTheory.PullDegTop.main.2.1 r _ _).2 ?_⟩
  have r' : (r.e.hom.left ≫ pullback.fst Q.P.A.hom (specOf (RingHom.id V))) ≫
      p.e.hom.left ≫ pullback.fst L.D.P.A.hom (specOf iw) = p'.e.hom.left ≫ pullback.fst L.D.P.A.hom (specOf iw) :=
    (congrArg (· ≫ _) r₁).trans q₁
  have pb : IsPullback (p.e.hom.left ≫ pullback.fst L.D.P.A.hom (specOf iw)) Q.P.A.hom L.D.P.A.hom (spMap iw) :=
    (pull_grp p).1
  have w : (r.e.hom.left ≫ pullback.fst Q.P.A.hom (specOf (RingHom.id V))) ≫ Q.P.A.hom =
      Q'.P.A.hom ≫ spMap (RingHom.id V) := (pull_grp r).1.w
  have b : (oQ.onB.act x).left ≫ p.e.hom.left ≫ pullback.fst L.D.P.A.hom (specOf iw) =
      (p.e.hom.left ≫ pullback.fst L.D.P.A.hom (specOf iw)) ≫ (L.oa.onB.act x).left :=
    (ha x).trans (Category.assoc _ _ _).symm
  have b' : (oQ'.onB.act x).left ≫ p'.e.hom.left ≫ pullback.fst L.D.P.A.hom (specOf iw) =
      (p'.e.hom.left ≫ pullback.fst L.D.P.A.hom (specOf iw)) ≫ (L.oa.onB.act x).left :=
    (ha' x).trans (Category.assoc _ _ _).symm
  refine pb.hom_ext ?_ ?_
  · refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) r').trans (b'.trans (Eq.symm ?_)))
    exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) b).trans ((Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ _) r')))
  · refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) w).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ _) (Over.w (oQ'.onB.act x))).trans (Eq.symm ?_))))
    exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (Over.w (oQ.onB.act x))).trans w)

end GlobalTheory.UCanon.DivIso
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

set_option autoImplicit false

namespace GlobalTheory.ChernMassPull

theorem mass : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (σ : k →+* ℂ) (D : ℕ), IsProjOver p → IsProjOver q → SmoothOfRelativeDimension D p → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q), π (genericPoint Y) = genericPoint X → π.residueDegree (genericPoint Y) ≠ 0 → ∀ (B : LB X) (φ : Weight p σ B), φ.IsCInf → ∀ ε : ℤˣ, (φ.pull π hπ).chernPart D ε Set.univ = (π.residueDegree (genericPoint Y) : ENNReal) * φ.chernPart D ε Set.univ := by
  intro k _ X Y _ _ p q σ D hX hY hsm π hπ hη hδ B φ hφ ε
  obtain ⟨U, hUη, hcard, hchart, hlift⟩ := GlobalTheory.T.exists_open_covering_charts_generically_finite_field k X Y p q σ D hX hY hsm π hπ hη hδ
  have hpre : PtsOver.map π hπ (spMap σ) ⁻¹' ptsIn p σ U = ptsIn q σ (π ⁻¹ᵁ U) := by
    ext z
    simp only [Set.mem_preimage, mem_ptsIn]
    rfl
  have h0Y := GlobalTheory.T.chernPart_complement_dense_open_null_field k Y q σ D hY (π ⁻¹ᵁ U) (by simp [hη, hUη]) _ (φ.pull π hπ) ε
  have h0X := GlobalTheory.T.chernPart_complement_dense_open_null_field k X p σ D hX U hUη B φ ε
  have h3 := GlobalTheory.T.chernMeasurePart_preimage_covering_field k X Y p q σ D hX hY π hπ B φ hφ ε (ptsIn p σ U) (isOpen_ptsIn U) _
    hcard hchart hlift
  rw [hpre] at h3
  rw [← measure_add_measure_compl (isOpen_ptsIn (π ⁻¹ᵁ U)).measurableSet, h0Y, add_zero, h3,
    ← measure_add_measure_compl (isOpen_ptsIn (p := p) (σ := σ) U).measurableSet, h0X, add_zero]

end GlobalTheory.ChernMassPull
end
