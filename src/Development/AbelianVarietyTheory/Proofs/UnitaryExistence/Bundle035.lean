module

public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle003
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle011
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsTangentModuleUniversalGroup
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle009
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle013
public import Formalism.LocalToGlobal.ProjectiveLattices.EmbKCoe
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle026
public import Formalism.LocalToGlobal.ProjectiveLattices.IntegrableOnIntegrand
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle028
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
public import Mathlib.RingTheory.LocalProperties.Reduced
public import Mathlib.RingTheory.Localization.InvSubmonoid
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.GroupTheory.MonoidLocalization.Away
import Mathlib.Topology.Sheaves.Presheaf
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001

@[expose] public section

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.DerivEig

open GlobalTheory.HolHom

section General

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {X : Scheme.{0}}

theorem fst_epsMul (s : ℂ) (x : DualNumber ℂ) : TrivSqZeroExt.fst (epsMul s x) = x.fst := by
  simp [epsMul]

theorem snd_epsMul (s : ℂ) (x : DualNumber ℂ) : TrivSqZeroExt.snd (epsMul s x) = s * x.snd := by
  simp [epsMul]

theorem isDerivAt_epsMul {c : V → (Sp ℂ ⟶ X)} {z w : V} {v : Sp (DualNumber ℂ) ⟶ X} (h : HolHom.IsDerivAt c z w v)
    (s : ℂ) : HolHom.IsDerivAt c z (s • w) (spMap (epsMul s) ≫ v) := by
  refine ⟨?_, fun U hU f => ?_⟩
  · rw [← Category.assoc, ← Spec.map_comp, ← h.1]
    congr 2
    ext1
    exact RingHom.ext fun x => fst_epsMul s x
  · rw [valR_spMap _ _ _ ((le_preimage_dual_iff h.1 U).2 hU), snd_epsMul, h.2 U hU, map_smul, smul_eq_mul]

theorem isDerivAt_of_comp_linear {c : V → (Sp ℂ ⟶ X)} (hc : HolAt c 0) (L : V →L[ℂ] V) {w : V}
    {v : Sp (DualNumber ℂ) ⟶ X} (h : HolHom.IsDerivAt (fun t => c (L t)) 0 w v) : HolHom.IsDerivAt c 0 (L w) v := by
  have h0 : c (L 0) = c 0 := by rw [map_zero]
  refine ⟨h.1.trans h0, fun U hU f => ?_⟩
  rw [h.2 U (by beta_reduce; rw [h0]; exact hU) f]
  have h1 : HasFDerivAt (fun t => valAt' (c t) U f) (fderiv ℂ (fun t => valAt' (c t) U f) 0) (L 0) := by
    rw [map_zero]; exact ((hc U hU).2 f).hasFDerivAt
  exact congrArg (· w) (h1.comp 0 L.hasFDerivAt).fderiv

end General

theorem eq_of_relab_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {l : Level H} (c : Coeff l) (σ : c.F →+* ℂ) {τ τ' : E →+* ℂ}
    (h : ∀ a : 𝓞 E, relab c σ τ (a : E) = relab c σ τ' (a : E)) : τ = τ' := by
  refine IsLocalization.ringHom_ext (𝓞 E)⁰ (RingHom.ext fun a => ?_)
  exact congrArg Subtype.val (σ.injective (h a))

end GlobalTheory.DerivEig


open GlobalTheory.HolHom GlobalTheory.DerivEig in
theorem GlobalTheory.isEigAt_iff_of_isDerivAt0 : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (k : Fin F.n) (P : (F.Di k).La →+ (Fin g → ℂ)), IsPeriod (F.Di k) (fun j => relab c σ (e j).1) P → ∀ (w : Fin g → ℂ) (v : (Sp (DualNumber (CAt σ)) ⟶ Xo.univ.t.G.left)) (τ : E →+* ℂ), IsDerivAt0 (fun z => (F.ex k P z).left) w v → (IsEigAt c τ v ↔ ∀ j, w j ≠ 0 → (e j).1 = τ) := by
  intro E _ _ _ H Dw l Xo c σ g e F k P hP w v τ hv
  have hhol : HolAt (fun z => (F.ex k P z).left) 0 := holAt_of_isHolTo (isHolTo_ex F k hP) (Set.mem_univ 0)
  have hv' := (isDerivAt0_iff _ _ _).1 hv
  have hact : ∀ a : 𝓞 E, HolHom.IsDerivAt (fun z => (F.ex k P z).left) 0
      (fun j => relab c σ (e j).1 (a : E) * w j) (v ≫ (Xo.univ.t.act.act a).left) := by
    intro a
    let L : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ) :=
      ContinuousLinearMap.pi fun j => relab c σ (e j).1 (a : E) • ContinuousLinearMap.proj j
    have h1 := hv'.comp (Xo.univ.t.act.act a).left
    have h2 : (fun t => (F.ex k P t).left ≫ (Xo.univ.t.act.act a).left) = fun t => (F.ex k P (L t)).left := by
      funext t
      rw [← Over.comp_left, ← F.ex_lin k P hP a t]
      rfl
    rw [h2] at h1
    exact isDerivAt_of_comp_linear hhol L h1
  have hsc : ∀ a : 𝓞 E, HolHom.IsDerivAt (fun z => (F.ex k P z).left) 0
      (relab c σ τ (a : E) • w) (spMap (epsMul (algebraMap c.F (CAt σ) (embK c τ a))) ≫ v) :=
    fun a => isDerivAt_epsMul hv' _
  constructor
  · intro h j hj
    refine eq_of_relab_eq c σ fun a => ?_
    have h1 := hact a
    have h2 : HolHom.IsDerivAt (fun z => (F.ex k P z).left) 0 (relab c σ τ (a : E) • w)
        (v ≫ (Xo.univ.t.act.act a).left) :=
      Eq.mpr (congrArg (HolHom.IsDerivAt (fun z => (F.ex k P z).left) 0 (relab c σ τ (a : E) • w)) (h a)) (hsc a)
    have h3 := eq_of_forall_fderiv_eq hhol (F.ex_diff k P hP).2 fun U hU f =>
      (h1.2 U hU f).symm.trans (h2.2 U hU f)
    exact mul_right_cancel₀ hj (congrFun h3 j)
  · intro h a
    have h1 := hact a
    have h3 : (fun j => relab c σ (e j).1 (a : E) * w j) = relab c σ τ (a : E) • w := by
      funext j
      by_cases hj : w j = 0
      · simp [hj]
      · rw [h j hj]; rfl
    rw [h3] at h1
    exact h1.unique (hsc a)
end

section

noncomputable section

namespace GlobalTheory.TanDeriv

section SlopeTestRemainingChoices

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames GlobalTheory.TanMod

def evAt {R : Type} [CommRing R] {Y : Scheme.{0}} (W : Sp R ⟶ Y) (U : Y.Opens) (h : ⊤ ≤ W ⁻¹ᵁ U)
    (f : Γ(Y, U)) : R :=
  (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom ((W.appLE U ⊤ h).hom f)

theorem evAt_congr {R : Type} [CommRing R] {Y : Scheme.{0}} {W W' : Sp R ⟶ Y} (e : W = W') (U : Y.Opens)
    (h : ⊤ ≤ W ⁻¹ᵁ U) (h' : ⊤ ≤ W' ⁻¹ᵁ U) (f : Γ(Y, U)) : evAt W U h f = evAt W' U h' f := by
  subst e; rfl

theorem evAt_comp {R A : Type} [CommRing R] [CommRing A] (φ : R →+* A) {Y : Scheme.{0}} (W : Sp R ⟶ Y)
    (U : Y.Opens) (h : ⊤ ≤ W ⁻¹ᵁ U) (h' : ⊤ ≤ (spMap φ ≫ W) ⁻¹ᵁ U) (f : Γ(Y, U)) :
    evAt (spMap φ ≫ W) U h' f = φ (evAt W U h f) := by
  have h1 : (spMap φ ≫ W).appLE U ⊤ h' = W.appLE U ⊤ h ≫ (spMap φ).appTop := by
    have : (spMap φ).appTop = (spMap φ).appLE ⊤ ⊤ le_top := (Scheme.Hom.app_eq_appLE (spMap φ))
    rw [this]
    exact (Scheme.Hom.appLE_comp_appLE (spMap φ) W U ⊤ ⊤ h le_top).symm
  have h2 := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ)
  have h3 := congrArg (fun ψ => ψ.hom ((W.appLE U ⊤ h).hom f)) h2
  unfold evAt
  rw [h1]
  exact h3

theorem top_le_of_comp {R A : Type} [CommRing R] [CommRing A] (p : R →+* A)
    (hs : Function.Surjective p) (hn : ∀ x, p x = 0 → x * x = 0) {Y : Scheme.{0}} (W : Sp R ⟶ Y)
    (U : Y.Opens) (h : ⊤ ≤ (spMap p ≫ W) ⁻¹ᵁ U) : ⊤ ≤ W ⁻¹ᵁ U := by
  intro x _
  have hx : (show PrimeSpectrum R from x) ∈ Set.range (PrimeSpectrum.comap p) := by
    rw [range_comap_of_surjective _ _ hs]
    intro a ha
    have h3 : a * a ∈ (show PrimeSpectrum R from x).asIdeal := by
      rw [hn a ha]; exact Ideal.zero_mem _
    exact ((show PrimeSpectrum R from x).isPrime.mem_or_mem h3).elim id id
  obtain ⟨y, hy⟩ := hx
  have h4 : (show Sp A from y) ∈ (spMap p ≫ W) ⁻¹ᵁ U := h trivial
  have h5 : spMap p (show Sp A from y) = x := hy
  rw [← h5]
  exact h4

theorem comp_top_le {R A : Type} [CommRing R] [CommRing A] (p : R →+* A) {Y : Scheme.{0}} (W : Sp R ⟶ Y)
    (U : Y.Opens) (h : ⊤ ≤ W ⁻¹ᵁ U) : ⊤ ≤ (spMap p ≫ W) ⁻¹ᵁ U :=
  fun y _ => h (show spMap p y ∈ (⊤ : (Sp R).Opens) from trivial)

variable {X0 : Scheme.{0}} {S : Type} [CommRing S] {x0 : Sp S ⟶ X0} {G : Over X0} [GrpObj G]

theorem snd_evAt_mul (u v : overAt x0 (DualNumber S) ⟶ G) (hu0 : smT x0 0 u = 1) (hv0 : smT x0 0 v = 1)
    (U : G.left.Opens) (hu : ⊤ ≤ (show Sp (DualNumber S) ⟶ G.left from u.left) ⁻¹ᵁ U)
    (hv : ⊤ ≤ (show Sp (DualNumber S) ⟶ G.left from v.left) ⁻¹ᵁ U)
    (huv : ⊤ ≤ (show Sp (DualNumber S) ⟶ G.left from (u * v).left) ⁻¹ᵁ U) (f : Γ(G.left, U)) :
    (evAt (R := DualNumber S) (u * v).left U huv f).snd =
      (evAt (R := DualNumber S) u.left U hu f).snd + (evAt (R := DualNumber S) v.left U hv f).snd := by
  have hz : (0 : S →ₗ[S] S) = (0 : S) • (LinearMap.id : S →ₗ[S] S) := by simp
  let P : overAt x0 (TrivSqZeroExt S (S × S)) ⟶ G :=
    (homAt x0 (tm (LinearMap.inl S S S)) ≫ u) * (homAt x0 (tm (LinearMap.inr S S S)) ≫ v)
  have e1 : homAt x0 (tm (LinearMap.fst S S S)) ≫ P = u := by
    rw [MonObj.comp_mul, ← Category.assoc, ← Category.assoc, homAt_comp, homAt_comp,
      ← TrivSqZeroExt.map_comp_map, ← TrivSqZeroExt.map_comp_map,
      LinearMap.fst_comp_inl, LinearMap.fst_comp_inr, hz, TrivSqZeroExt.map_id, homAt_id, Category.id_comp]
    change _ * smT x0 0 v = _
    rw [hv0, _root_.mul_one]
  have e2 : homAt x0 (tm (LinearMap.snd S S S)) ≫ P = v := by
    rw [MonObj.comp_mul, ← Category.assoc, ← Category.assoc, homAt_comp, homAt_comp,
      ← TrivSqZeroExt.map_comp_map, ← TrivSqZeroExt.map_comp_map,
      LinearMap.snd_comp_inl, LinearMap.snd_comp_inr, hz, TrivSqZeroExt.map_id, homAt_id, Category.id_comp]
    change smT x0 0 u * _ = _
    rw [hu0, _root_.one_mul]
  have e3 : homAt x0 (tm (LinearMap.coprod LinearMap.id LinearMap.id : S × S →ₗ[S] S)) ≫ P = u * v := by
    rw [MonObj.comp_mul, ← Category.assoc, ← Category.assoc, homAt_comp, homAt_comp,
      ← TrivSqZeroExt.map_comp_map, ← TrivSqZeroExt.map_comp_map,
      LinearMap.coprod_inl, LinearMap.coprod_inr, TrivSqZeroExt.map_id, homAt_id, Category.id_comp,
      Category.id_comp]
  have f1 : spMap (tm (LinearMap.fst S S S) : TrivSqZeroExt S (S × S) →+* DualNumber S) ≫ P.left = u.left :=
    congrArg (fun φ => φ.left) e1
  have f2 : spMap (tm (LinearMap.snd S S S) : TrivSqZeroExt S (S × S) →+* DualNumber S) ≫ P.left = v.left :=
    congrArg (fun φ => φ.left) e2
  have f3 : spMap (tm (LinearMap.coprod LinearMap.id LinearMap.id : S × S →ₗ[S] S) :
      TrivSqZeroExt S (S × S) →+* DualNumber S) ≫ P.left = (u * v).left :=
    congrArg (fun φ => φ.left) e3
  have hP : ⊤ ≤ (show Sp (TrivSqZeroExt S (S × S)) ⟶ G.left from P.left) ⁻¹ᵁ U := by
    refine top_le_of_comp (tm (LinearMap.fst S S S) : TrivSqZeroExt S (S × S) →+* DualNumber S) ?_ ?_ _ U ?_
    · intro y
      refine ⟨tm (LinearMap.inl S S S) y, ?_⟩
      ext <;> simp
    · intro x hx
      have h1 : x.fst = 0 := by simpa using congrArg TrivSqZeroExt.fst hx
      ext <;> simp [h1]
    · exact f1 ▸ hu
  rw [← evAt_congr f1 U (comp_top_le _ _ U hP) hu, ← evAt_congr f2 U (comp_top_le _ _ U hP) hv,
    ← evAt_congr f3 U (comp_top_le _ _ U hP) huv, evAt_comp _ _ U hP, evAt_comp _ _ U hP, evAt_comp _ _ U hP]
  simp

variable [IsCommMonObj G]

theorem tan_top_le (U : G.left.Opens)
    (h1 : ⊤ ≤ (show Sp S ⟶ G.left from (1 : Over.mk x0 ⟶ G).left) ⁻¹ᵁ U) (m : TanSp x0 G) :
    ⊤ ≤ (show Sp (DualNumber S) ⟶ G.left from m.pt.left) ⁻¹ᵁ U := by
  refine top_le_of_comp (TrivSqZeroExt.fstHom S S S).toRingHom ?_ ?_ _ U ?_
  · intro y
    exact ⟨TrivSqZeroExt.inl y, rfl⟩
  · intro x hx
    have h1 : x.fst = 0 := hx
    ext <;> simp [h1]
  · exact (unit_of_smT_zero x0 _ m.tan).symm ▸ h1

def derivAt (U : G.left.Opens) (h1 : ⊤ ≤ (show Sp S ⟶ G.left from (1 : Over.mk x0 ⟶ G).left) ⁻¹ᵁ U)
    (f : Γ(G.left, U)) : TanSp x0 G →ₗ[S] S where
  toFun m := (evAt (R := DualNumber S) m.pt.left U (tan_top_le U h1 m) f).snd
  map_add' m n := snd_evAt_mul m.pt n.pt m.tan n.tan U _ _ _ f
  map_smul' a m := by
    have := evAt_comp (epsMul a) (show Sp (DualNumber S) ⟶ G.left from m.pt.left) U (tan_top_le U h1 m)
      (tan_top_le U h1 (a • m)) f
    refine (congrArg TrivSqZeroExt.snd this).trans ?_
    simp [epsMul]

theorem derivAt_sum {m : ℕ} (b : Fin m → TanSp x0 G) (a : Fin m → S) (w : Sp (DualNumber S) ⟶ G.left)
    (hw : w = (∑ i, a i • b i).pt.left) (U : G.left.Opens) (h : ⊤ ≤ w ⁻¹ᵁ U)
    (hv : ∀ i, ⊤ ≤ (show Sp (DualNumber S) ⟶ G.left from (b i).pt.left) ⁻¹ᵁ U) (f : Γ(G.left, U)) :
    (evAt w U h f).snd = ∑ i, a i * (evAt (R := DualNumber S) (b i).pt.left U (hv i) f).snd := by
  subst hw
  have h1 : ⊤ ≤ (show Sp S ⟶ G.left from (1 : Over.mk x0 ⟶ G).left) ⁻¹ᵁ U :=
    (unit_of_smT_zero x0 _ (∑ i, a i • b i).tan) ▸ comp_top_le _ _ U h
  have key := map_sum (derivAt U h1 f) (fun i => a i • b i) Finset.univ
  simp only [map_smul, smul_eq_mul] at key
  exact key

theorem derivative_tangent_combination_universal_group_eval {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} (Xo : Moduli Dw l) {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) {m : ℕ}
    (v : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)) (a : Fin m → S)
    (w : Sp (DualNumber S) ⟶ Xo.univ.t.G.left) (hv0 : ∀ i, IsTanAt x (v i)) (hw : IsCombAt x v a w)
    (U : Xo.univ.t.G.left.Opens) (h : ⊤ ≤ w ⁻¹ᵁ U) (hv : ∀ i, ⊤ ≤ v i ⁻¹ᵁ U) (f : Γ(Xo.univ.t.G.left, U)) :
    (evAt w U h f).snd = ∑ i, a i * (evAt (v i) U (hv i) f).snd := by
  let b : Fin m → TanSp x Xo.univ.t.G := fun i =>
    TanSp.mk (Over.homMk (v i) (hv0 i).1) (smT_zero_of x _ (hv0 i).2)
  refine derivAt_sum b a w ?_ U h hv f
  obtain ⟨u, hu, rfl⟩ := hw
  have hub : u = fun i => (a i • b i).pt := funext fun i => Over.OverMorphism.ext (hu i)
  subst hub
  rw [List.prod_ofFn, ← TanSp.pt_sum]

end SlopeTestRemainingChoices

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

theorem deriv_comb : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x : Sp S ⟶ Xo.X) (m : ℕ) (v : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)) (a : Fin m → S) (w : Sp (DualNumber S) ⟶ Xo.univ.t.G.left), (∀ i, IsTanAt x (v i)) → IsCombAt x v a w → ∀ (U : Xo.univ.t.G.left.Opens) (h : ⊤ ≤ w ⁻¹ᵁ U) (hv : ∀ i, ⊤ ≤ v i ⁻¹ᵁ U) (f : Γ(Xo.univ.t.G.left, U)), TrivSqZeroExt.snd (show DualNumber S from (Scheme.ΓSpecIso (CommRingCat.of (DualNumber S))).hom.hom ((w.appLE U ⊤ h).hom f)) = ∑ i, a i * TrivSqZeroExt.snd (show DualNumber S from (Scheme.ΓSpecIso (CommRingCat.of (DualNumber S))).hom.hom (((v i).appLE U ⊤ (hv i)).hom f)) := by
  intro E _ _ _ H Dw l Xo S _ x m v a w hv0 hw U h hv f
  exact derivative_tangent_combination_universal_group_eval Xo x v a w hv0 hw U h hv f

end GlobalTheory.TanDeriv
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory

theorem testRing_localizationAway :
    ∀ (K : Type) [Field K] (p : TRing K) (g : p.R), ∃ (p' : TRing K) (lam : p.R →ₐ[K] p'.R), IsUnit (lam g) ∧ ∀ (T : Type) [CommRing T] [Algebra K T] (ψ : p.R →ₐ[K] T), IsUnit (ψ g) → ∃ k : p'.R →ₐ[K] T, k.comp lam = ψ := by
  intro K _ p g
  obtain ⟨h1, h2⟩ := reduced_finiteType_iff_testRing K
  obtain ⟨hft, hred⟩ := h2 p
  have hft1 : Algebra.FiniteType p.R (Localization.Away g) :=
    IsLocalization.finiteType_of_monoid_fg (Submonoid.powers g) _
  have hft' : Algebra.FiniteType K (Localization.Away g) := Algebra.FiniteType.trans hft hft1
  have hred' : IsReduced (Localization.Away g) :=
    isReduced_localizationPreserves (Submonoid.powers g) _ hred
  obtain ⟨p', ⟨e⟩⟩ := h1 (Localization.Away g) hft' hred'
  refine ⟨p', e.symm.toAlgHom.comp (IsScalarTower.toAlgHom K p.R (Localization.Away g)), ?_, ?_⟩
  · exact (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away g) g).map e.symm
  · intro T _ _ ψ hψ
    have hu : ∀ y : Submonoid.powers g, IsUnit (ψ y) := by
      rintro ⟨_, n, rfl⟩
      simpa using hψ.pow n
    refine ⟨(IsLocalization.liftAlgHom (M := Submonoid.powers g) (S := Localization.Away g)
      (f := ψ) hu).comp e.toAlgHom, ?_⟩
    apply AlgHom.ext
    intro x
    simp [IsLocalization.liftAlgHom]

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

theorem _root_.GlobalTheory.T.existsUnique_glue_dualNumber : ∀ (S : Type) [CommRing S] (Y : Scheme.{0}) (n : ℕ) (h : Fin n → S), Ideal.span (Set.range h) = ⊤ → ∀ w : ∀ i, Sp (DualNumber (Localization.Away (h i))) ⟶ Y, (∀ i j (α : Localization.Away (h i) →+* Localization.Away (h i * h j)) (β : Localization.Away (h j) →+* Localization.Away (h i * h j)), α.comp (algebraMap S (Localization.Away (h i))) = (algebraMap S (Localization.Away (h i * h j))) → β.comp (algebraMap S (Localization.Away (h j))) = (algebraMap S (Localization.Away (h i * h j))) → spMap (dualMap α) ≫ w i = spMap (dualMap β) ≫ w j) → ∃! w₀ : Sp (DualNumber S) ⟶ Y, ∀ i, spMap (dualMap (algebraMap S (Localization.Away (h i)))) ≫ w₀ = w i := by
  first | exact @GlobalTheory.Frames.existsUnique_glue_dual | exact GlobalTheory.Frames.existsUnique_glue_dual | (intros; apply GlobalTheory.Frames.existsUnique_glue_dual <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

theorem _root_.GlobalTheory.T.exists_tangent_module_universal_group : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x : Sp S ⟶ Xo.X), ∃ (N : Type) (_ : AddCommGroup N) (_ : Module S N) (v : N → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)) (ρ : 𝓞 E →+* Module.End S N), Function.Injective v ∧ (∀ w, IsTanAt x w ↔ w ∈ Set.range v) ∧ (∀ (n : ℕ) (b : Fin n → N) (a : Fin n → S) w, IsCombAt x (fun i => v (b i)) a w ↔ w = v (∑ i, a i • b i)) ∧ (∀ a m, v (ρ a m) = v m ≫ (Xo.univ.t.act.act a).left) ∧ ∀ (s : S) m, v (s • m) = spMap (epsMul s) ≫ v m := by
  first | exact @GlobalTheory.TanMod.exists_tangent_module | exact GlobalTheory.TanMod.exists_tangent_module | (intros; apply GlobalTheory.TanMod.exists_tangent_module <;> assumption)
end

section

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory

theorem isDerivAt0_ex_isTanAt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (σ' : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ' ty) (k : Fin F.n) (P : (F.Di k).La →+ (Fin g → ℂ)), IsPeriod (F.Di k) ty P → (∀ w v, IsDerivAt0 (fun z => (F.ex k P z).left) w v → IsTanAt (F.u k P) v) ∧ (∀ w, ∃! v : (Sp (DualNumber ℂ) ⟶ Xo.univ.t.G.left), IsDerivAt0 (fun z => (F.ex k P z).left) w v) ∧ ∀ v : (Sp (DualNumber ℂ) ⟶ Xo.univ.t.G.left), IsTanAt (F.u k P) v → ∃! w, IsDerivAt0 (fun z => (F.ex k P z).left) w v := by
  intro E _ _ _ H Dw l Xo σ' g ty F k P hP
  have h0 := (F.ex_ker k P hP 0).2 (zero_mem _)
  refine ⟨fun w v hv => ⟨((HolHom.isDerivAt0_iff _ _ _).1 hv).over, ?_⟩, fun w => ?_, fun v hv => ?_⟩
  · exact hv.1.trans (congrArg (·.left) h0)
  · obtain ⟨v, hv, -⟩ := (F.ex_diff k P hP).1 w
    exact ⟨v.left, hv, fun v' hv' =>
      ((HolHom.isDerivAt0_iff _ _ _).1 hv').unique ((HolHom.isDerivAt0_iff _ _ _).1 hv)⟩
  · exact (F.ex_diff k P hP).2 (Over.homMk v hv.1) (hv.2.trans (congrArg (·.left) h0).symm)

end GlobalTheory
end
end

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

theorem _root_.GlobalTheory.T.relabelEmbeddings_good_bijective_conj_compat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H) (c : Coeff l) (σ : c.F →+* ℂ), GoodEmb c σ → Function.Bijective (relab c σ) ∧ (∀ τ, relab c σ τ (H.rt : E) = H.rt0 ↔ τ (H.rt : E) = H.rt0) ∧ (∀ τ, relab c σ (conjEmb τ) = conjEmb (relab c σ τ)) ∧ ∀ (Dw : Datum H) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)), IsTypeFn H Dw.p Dw.q (fun j => relab c σ (e j).1) := by
  first | exact @GlobalTheory.Relab.relab_good | exact GlobalTheory.Relab.relab_good | (intros; apply GlobalTheory.Relab.relab_good <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

theorem _root_.GlobalTheory.T.existsUnique_cmEmbedding_eigenvector_sum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] (N : Type) [AddCommGroup N] [Module S N] (ρ : 𝓞 E →+* Module.End S N) (m : N), ∃! f : (E →+* ℂ) → N, (∀ τ a, ρ a (f τ) = algebraMap c.F S (embK c τ a) • f τ) ∧ ∑ τ, f τ = m := by
  first | exact @GlobalTheory.Frames.existsUnique_eigen_sum | exact GlobalTheory.Frames.existsUnique_eigen_sum | (intros; apply GlobalTheory.Frames.existsUnique_eigen_sum <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.CuspCentre

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r ρ : ℕ}

noncomputable def displ (X : Data E r) (cu : FJ.CuspFD X ρ) (s : Finset (Fin r → E)) :
    Matrix (Fin ρ) (Fin ρ) E →+ (s → Fin r → E) where
  toFun β := fun v => FJ.zMatE X cu.e β *ᵥ v.1 - v.1
  map_zero' := by
    funext v
    simp [zMatE_zero]
  map_add' β β' := by
    funext v
    simp only [zMatE_mulVec, Pi.add_apply, Matrix.add_apply, add_mul, Finset.sum_add_distrib,
      add_smul]
    abel

theorem displ_injective (X : Data E r) (cu : FJ.CuspFD X ρ) (s : Finset (Fin r → E))
    (hs : Submodule.span E (s : Set (Fin r → E)) = ⊤) : Function.Injective (displ X cu s) := by
  intro β β' h
  apply zMatE_injective X cu
  apply Matrix.toLin'.injective
  refine LinearMap.ext_on hs fun v hv => ?_
  have h1 : FJ.zMatE X cu.e β *ᵥ v - v = FJ.zMatE X cu.e β' *ᵥ v - v := congrFun h ⟨v, hv⟩
  simpa [Matrix.toLin'_apply] using h1

theorem span_zGam_fg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r ρ : ℕ) (X : Data E r) (cu : FJ.CuspFD X ρ), (Submodule.span ℤ (FJ.zGam X cu)).FG := by
  intro E _ _ _ r ρ X cu
  obtain ⟨s, hs⟩ := X.Λ_fg
  have hsE : Submodule.span E (s : Set (Fin r → E)) = ⊤ := by
    rw [← X.Λ_span, ← hs, Submodule.span_span_of_tower]
  have hΛ : (X.Λ.restrictScalars ℤ).FG := by
    have : Module.Finite (𝓞 E) X.Λ := Module.Finite.iff_fg.2 X.Λ_fg
    have h2 : Module.Finite ℤ X.Λ := Module.Finite.trans (𝓞 E) X.Λ
    exact Module.Finite.iff_fg.1 h2
  have hN : (Submodule.pi Set.univ fun _ : s => X.Λ.restrictScalars ℤ).FG :=
    Submodule.fg_pi fun _ => hΛ
  refine Submodule.fg_of_fg_map_injective (displ X cu s).toIntLinearMap
    (displ_injective X cu s hsE) (hN.of_le ?_)
  rw [Submodule.map_le_iff_le_comap, Submodule.span_le]
  rintro β ⟨-, γ, hγ, e⟩ v -
  have hv : v.1 ∈ X.Λ := hs ▸ Submodule.subset_span v.2
  change FJ.zMatE X cu.e β *ᵥ v.1 - v.1 ∈ X.Λ
  rw [← e]
  exact X.Λ.sub_mem (((X.Γ_stab γ hγ).2 _).1 hv) hv

end GlobalTheory.CuspCentre
end

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

theorem _root_.GlobalTheory.T.finrank_rat_skewHermitian_matrices_cmField : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (ρ : ℕ) (Ψ : Finset (E →+* ℂ)), (∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) → ∀ W : Submodule ℚ (Matrix (Fin ρ) (Fin ρ) E), (∀ β, β ∈ W ↔ FJ.IsSkew β) → Module.finrank ℚ W = Ψ.card * ρ ^ 2 := by
  first | exact @GlobalTheory.finrank_skewHermitian_eq | exact GlobalTheory.finrank_skewHermitian_eq | (intros; apply GlobalTheory.finrank_skewHermitian_eq <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

theorem _root_.GlobalTheory.T.mem_dual_cuspCharacterLattice_iff_adapted_basis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r ρ : ℕ) (X : Data E r) (cu : FJ.CuspFD X ρ) (cc' : Fin ρ → FractionalIdeal (𝓞 E)⁰ E), (∀ a : Fin ρ → E, (∑ b, a b • cu.e b) ∈ X.Λ ↔ ∀ b, a b ∈ cc' b) → ∀ u : Fin ρ → E, u ∈ FJ.dualOE (FJ.XcFD 1 cu) ↔ ∀ a (y : E), (∀ a' ∈ cc' a, ∃ n : ℤ, Algebra.trace ℚ E (y * a') = n) → u a * y ∈ Set.range (algebraMap (𝓞 E) E) := by
  first | exact @GlobalTheory.mem_dualOE_xcFD_one_iff_of_adapted | exact GlobalTheory.mem_dualOE_xcFD_one_iff_of_adapted | (intros; apply GlobalTheory.mem_dualOE_xcFD_one_iff_of_adapted <;> assumption)
end
