module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle011
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle089
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle123
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle157
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieOmegaLatticeVectorBundle
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle015
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle053
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.GermHodgeLatticeExists
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle086
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle174
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle141
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianQuotientLattice
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.Bundle001
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.LocFn

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LocFn.FieldStage

open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar.LieTangent GlobalTheory.CompanionTheory.Ar.LieVB

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

theorem tied_pull (Y : Model Xo c β) {B F : Type} [CommRing B] [CommRing F] (ψ : B →+* F)
    {y : Sp B ⟶ Xo.XF c} {y' : Sp F ⟶ Xo.XF c} (hy : y' = spMap ψ ≫ y)
    {V : Sp (DualNumber B) ⟶ Xo.univ.t.G.left} {V' : Sp (DualNumber B) ⟶ Y.t.G.left} (h : Tied Y y V V') :
    Tied Y y' (spMap (GlobalTheory.CompanionTheory.Ar.dualMap ψ) ≫ V) (spMap (GlobalTheory.CompanionTheory.Ar.dualMap ψ) ≫ V') := by
  subst hy
  obtain ⟨u, h1, h2, h3⟩ := h
  refine ⟨spMap (GlobalTheory.CompanionTheory.Ar.dualMap ψ) ≫ u, ?_, ?_, ?_⟩
  · rw [Category.assoc, h1, ← Category.assoc, ← Category.assoc]
    congr 1
    exact spec_dual_alg ψ
  · rw [Category.assoc, h2]
  · rw [Category.assoc, h3]

theorem tied_over (Y : Model Xo c β) {B : Type} [CommRing B] {y : Sp B ⟶ Xo.XF c}
    {V : Sp (DualNumber B) ⟶ Xo.univ.t.G.left} {V' : Sp (DualNumber B) ⟶ Y.t.G.left} (h : Tied Y y V V') :
    V ≫ Xo.univ.t.G.hom = spMap (algebraMap B (DualNumber B)) ≫ under y := by
  obtain ⟨u, h1, rfl, -⟩ := h
  have hp : IsPullback Y.m0.toSABMap.φ Y.oF.t.G.hom Xo.univ.t.G.hom (pullback.fst _ _) := Y.m0.cart.1
  rw [Category.assoc, hp.w, ← Category.assoc, h1, Category.assoc]

theorem isCombAt_pull {B F : Type} [CommRing B] [CommRing F] (ψ : B →+* F) {x : Sp B ⟶ Xo.X} {x' : Sp F ⟶ Xo.X}
    (hx : spMap ψ ≫ x = x') {m : ℕ} {vs : Fin m → (Sp (DualNumber B) ⟶ Xo.univ.t.G.left)} {cf : Fin m → B}
    {w : Sp (DualNumber B) ⟶ Xo.univ.t.G.left} (h : Formalism.L2.Pj.IsCombAt x vs cf w) :
    Formalism.L2.Pj.IsCombAt x' (fun k => spMap (GlobalTheory.CompanionTheory.Ar.dualMap ψ) ≫ vs k) (fun k => ψ (cf k))
      (spMap (GlobalTheory.CompanionTheory.Ar.dualMap ψ) ≫ w) := by
  obtain ⟨u, hu, rfl⟩ := h
  let P : Formalism.L2.Pj.tEps x' ⟶ Formalism.L2.Pj.tEps x := epsBase ψ hx
  let Q : (Formalism.L2.Pj.tEps x ⟶ Xo.univ.t.G) →* (Formalism.L2.Pj.tEps x' ⟶ Xo.univ.t.G) :=
    { toFun := fun f => P ≫ f, map_one' := comp_one _, map_mul' := fun a b => comp_mul _ _ _ }
  refine ⟨fun i => P ≫ u i, fun i => ?_, ?_⟩
  · change spMap (GlobalTheory.CompanionTheory.Ar.dualMap ψ) ≫ (u i).left = _
    rw [hu i, ← GlobalTheory.CompanionTheory.Ar.FrameEig.epsMul_eq, ← GlobalTheory.CompanionTheory.Ar.FrameEig.epsMul_eq, ← Category.assoc, ← Category.assoc]
    congr 1
    exact spec_dual_eps ψ (cf i)
  · have : (List.ofFn fun i => P ≫ u i).prod = P ≫ (List.ofFn u).prod := by
      change (List.ofFn fun i => Q (u i)).prod = Q (List.ofFn u).prod
      rw [map_list_prod, List.map_ofFn]
      rfl
    rw [this]
    rfl

theorem exists_pulled (Y : Model Xo c β) {B F : Type} [CommRing B] [Field F] (ψ : B →+* F) (yB : Sp B ⟶ Xo.XF c)
    (y : Sp F ⟶ Xo.XF c) (hy : y = spMap ψ ≫ yB) (x₀ : Sp B ⟶ Xo.X) (hx₀ : x₀ = under yB) {n : ℕ} (v : Vecs y n)
    (vs : Fin n → (Sp (DualNumber B) ⟶ Xo.univ.t.G.left))
    (hv : ∀ k, (v k).left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap ψ) ≫ vs k) (C : Matrix (Fin n) (Fin n) B)
    (ee : Fin n → (Sp (DualNumber B) ⟶ Y.t.G.left))
    (hV : ∀ i, ∃ V : Sp (DualNumber B) ⟶ Xo.univ.t.G.left, Tied Y yB V (ee i) ∧
      Formalism.L2.Pj.IsCombAt x₀ vs (C i) V) :
    ∃ v₀ : Vecs y n, (∀ i, IsComb ((ψ.mapMatrix C) i) v (v₀ i)) ∧
      ∀ i, Tied Y y (v₀ i).left (spMap (GlobalTheory.CompanionTheory.Ar.dualMap ψ) ≫ ee i) := by
  choose V hT hC using hV
  have hT' := fun i => tied_pull Y ψ hy (hT i)
  refine ⟨fun i => Over.homMk (spMap (GlobalTheory.CompanionTheory.Ar.dualMap ψ) ≫ V i) (tied_over Y (hT' i)), fun i => ?_, hT'⟩
  rw [GlobalTheory.CompanionTheory.Ar.FrameEig.isComb_iff]
  have hx : spMap ψ ≫ x₀ = under y := by
    rw [hx₀, hy]
    exact (Category.assoc _ _ _).symm
  have := isCombAt_pull ψ hx (hC i)
  simp only [← hv] at this
  exact this

theorem exists_germ (Y : Model Xo c β) {U : Set (Xo.XF c)} (Z : CptOver Y U) {R : Type} [CommRing R]
    (x : Sp R ⟶ Y.X) [IsOpenImmersion x] (φ₂ : R →+* Z.Ω) (hφ : spMap φ₂ ≫ x = Z.ξ₀ ≫ Y.j) {F : Type} [Field F]
    (y : Sp F ⟶ Xo.XF c) (hU : Set.range y ⊆ U) (θF : R →+* F) (hθ : spMap θF ≫ x = y ≫ Y.j) :
    ∃ (h : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (y ≫ Y.j)) (θ' : R →+* Y.X.presheaf.stalk (centre (y ≫ Y.j))),
      spMap θ' ≫ x = Y.X.fromSpecStalk (centre (y ≫ Y.j)) ∧
      (genMap (Z.ξ₀ ≫ Y.j) ⟨centre (y ≫ Y.j), h⟩).comp θ' = φ₂ ∧
      (Scheme.stalkClosedPointTo (y ≫ Y.j)).hom.comp θ' = θF := by
  have h : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (y ≫ Y.j) := by
    have h1 : genPt Z.ξ₀ ⤳ y (IsLocalRing.closedPoint F) := (Z.closure _).1 (hU ⟨_, rfl⟩)
    have h2 := h1.map Y.j.continuous
    simp only [genPt, centre, Scheme.Hom.comp_apply]
    exact h2
  have hqr : centre (y ≫ Y.j) ∈ x.opensRange := by
    rw [← hθ]
    change (spMap θF ≫ x) (IsLocalRing.closedPoint F) ∈ Set.range x
    simp only [Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩
  have hqx : (Y.X.fromSpecStalk (centre (y ≫ Y.j)))
      (IsLocalRing.closedPoint (Y.X.presheaf.stalk (centre (y ≫ Y.j)))) ∈ x.opensRange := by
    rw [Scheme.fromSpecStalk_closedPoint]
    exact hqr
  obtain ⟨θ', hθ'⟩ := exists_lift (A := Y.X.presheaf.stalk (centre (y ≫ Y.j))) x _ hqx
  refine ⟨h, θ', hθ', ?_, ?_⟩
  · have h1 : spMap ((genMap (Z.ξ₀ ≫ Y.j) ⟨centre (y ≫ Y.j), h⟩).comp θ') ≫ x = spMap φ₂ ≫ x := by
      have e1 : spMap ((genMap (Z.ξ₀ ≫ Y.j) ⟨centre (y ≫ Y.j), h⟩).comp θ') =
          spMap (genMap (Z.ξ₀ ≫ Y.j) ⟨centre (y ≫ Y.j), h⟩) ≫ spMap θ' := by
        simp only [spMap, ← Spec.map_comp]; rfl
      rw [e1, Category.assoc, hθ', hφ]
      exact spec_genMap _ _
    exact congrArg (fun g => g.hom) (Spec.map_injective ((cancel_mono x).1 h1))
  · have h1 : spMap ((Scheme.stalkClosedPointTo (y ≫ Y.j)).hom.comp θ') ≫ x = spMap θF ≫ x := by
      have e1 : spMap ((Scheme.stalkClosedPointTo (y ≫ Y.j)).hom.comp θ') =
          spMap (Scheme.stalkClosedPointTo (y ≫ Y.j)).hom ≫ spMap θ' := by
        simp only [spMap, ← Spec.map_comp]; rfl
      rw [e1, Category.assoc, hθ', hθ]
      exact spec_centre _
    exact congrArg (fun g => g.hom) (Spec.map_injective ((cancel_mono x).1 h1))

theorem valAt_of_chart (Y : Model Xo c β) {U : Set (Xo.XF c)} (Z : CptOver Y U) {R : Type} [CommRing R]
    (x : Sp R ⟶ Y.X) (φ₂ : R →+* Z.Ω) {F : Type} [Field F] (y : Sp F ⟶ Xo.XF c) (θF : R →+* F)
    (h : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (y ≫ Y.j)) (θ' : R →+* Y.X.presheaf.stalk (centre (y ≫ Y.j)))
    (h₁ : spMap θ' ≫ x = Y.X.fromSpecStalk (centre (y ≫ Y.j)))
    (h₂ : (genMap (Z.ξ₀ ≫ Y.j) ⟨centre (y ≫ Y.j), h⟩).comp θ' = φ₂)
    (h₃ : (Scheme.stalkClosedPointTo (y ≫ Y.j)).hom.comp θ' = θF) (b : Z.V) (e : epsAt x ⟶ Y.t.G)
    (ht : GlobalTheory.CompanionTheory.Ar.IsTanAt Y.t.G x e) (hb : (Z.M.pt b).left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap φ₂) ≫ e.left)
    (v' : epsAt (y ≫ Y.j) ⟶ Y.t.G) (hv' : v'.left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap θF) ≫ e.left) :
    Z.M.ValAt (y ≫ Y.j) b v' := by
  refine ⟨h, epsBase θ' h₁ ≫ e, ⟨isTanAt_base _ _ ht, ?_⟩, ?_⟩
  · rw [hb, ← h₂, ← spMap_dual_comp]
    simp [epsBase, spMap]
  · rw [hv', ← h₃, ← spMap_dual_comp]
    simp [epsBase, spMap]

theorem sameVec_of_tied (Y : Model Xo c β) {F : Type} [Field F] {y : Sp F ⟶ Xo.XF c}
    {v : epsAt (under y) ⟶ Xo.univ.t.G} {v' : epsAt (y ≫ Y.j) ⟶ Y.t.G} {w : Sp (DualNumber F) ⟶ Y.t.G.left}
    (h : Tied Y y v.left w) (hw : w = v'.left) : SameVec Y y v v' := by
  subst hw
  exact h

end GlobalTheory.CompanionTheory.Ar.LocFn.FieldStage

theorem GlobalTheory.CompanionTheory.Ar.LocFn.function_of_frames_at_field_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (Z : CptOver Y U) (φ : FrameFn Xo c) (a : ⋀[Z.Ω]^D.p Z.V) (b : ⋀[Z.Ω]^D.q Z.V) (S : Type) [CommRing S] [Algebra c.F S] (z : Formalism.L2.Pj.FrPt Xo c S) (hp : D.mult τ = D.p) (hq : D.mult (ComplexEmbedding.conjugate τ) = D.q) (R : Type) [CommRing R] (x : Sp R ⟶ Y.X) [IsOpenImmersion x] (φ₂ : R →+* Z.Ω) (e₁ : Fin D.p → (epsAt x ⟶ Y.t.G)) (e₂ : Fin D.q → (epsAt x ⟶ Y.t.G)) (f : R) (b₁ : Fin D.p → Z.V) (b₂ : Fin D.q → Z.V) (α κ : Z.Ω) (B : Type) [CommRing B] [Algebra S B] (θ : R →+* B) (C₁ : Matrix (Fin D.p) (Fin D.p) B) (C₂ : Matrix (Fin D.q) (Fin D.q) B), IsLineFn U τ φ → Represents Y U τ Z.M a b φ → spMap φ₂ ≫ x = Z.ξ₀ ≫ Y.j → a = α • exteriorPower.ιMulti Z.Ω D.p b₁ → b = κ • exteriorPower.ιMulti Z.Ω D.q b₂ → φ₂ f = α / κ → (∀ i, GlobalTheory.CompanionTheory.Ar.IsTanAt Y.t.G x (e₁ i)) → (∀ i, GlobalTheory.CompanionTheory.Ar.IsTanAt Y.t.G x (e₂ i)) → (∀ i, (Z.M.pt (b₁ i)).left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap φ₂) ≫ (e₁ i).left) → (∀ i, (Z.M.pt (b₂ i)).left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap φ₂) ≫ (e₂ i).left) → spMap θ ≫ x = spMap (algebraMap S B) ≫ zPt z ≫ Y.j → IsUnit C₁.det → IsUnit C₂.det → (∀ i, ∃ V : Sp (DualNumber B) ⟶ Xo.univ.t.G.left, Tied Y (spMap (algebraMap S B) ≫ zPt z) V (spMap (Formalism.L2.Pj.dualMap θ) ≫ (e₁ i).left) ∧ Formalism.L2.Pj.IsCombAt (spMap (algebraMap S B) ≫ z.x) (fun k => spMap (Formalism.L2.Pj.dualMap (algebraMap S B)) ≫ z.u τ (k.cast hp.symm)) (C₁ i) V) → (∀ i, ∃ V : Sp (DualNumber B) ⟶ Xo.univ.t.G.left, Tied Y (spMap (algebraMap S B) ≫ zPt z) V (spMap (Formalism.L2.Pj.dualMap θ) ≫ (e₂ i).left) ∧ Formalism.L2.Pj.IsCombAt (spMap (algebraMap S B) ≫ z.x) (fun k => spMap (Formalism.L2.Pj.dualMap (algebraMap S B)) ≫ z.u (ComplexEmbedding.conjugate τ) (k.cast hq.symm)) (C₂ i) V) → ∀ (F : Type) [Field F] (ψ : B →+* F) (y : Sp F ⟶ Xo.XF c), y = spMap ψ ≫ spMap (algebraMap S B) ≫ zPt z → Set.range y ⊆ U → ∀ (v : Vecs y D.p) (w : Vecs y D.q), (∀ i, (v i).left = spMap (Formalism.L2.Pj.dualMap (ψ.comp (algebraMap S B))) ≫ z.u τ (i.cast hp.symm)) → (∀ j, (w j).left = spMap (Formalism.L2.Pj.dualMap (ψ.comp (algebraMap S B))) ≫ z.u (ComplexEmbedding.conjugate τ) (j.cast hq.symm)) → φ F y v w * ψ C₂.det = ψ (θ f) * ψ C₁.det := by
  intro E _ _ _ H D l Xo c U τ O _ β Y Z φ a b S _ _ z hp hq R _ x _ φ₂ e₁ e₂ f b₁ b₂ α κ B _ _ θ C₁ C₂ hφ hrep hξ ha hb
    hf ht₁ ht₂ hb₁ hb₂ hθ hC₁ hC₂ hV₁ hV₂ F _ ψ y hy hU v w hv hw
  have e0 : ∀ {A : Type} [CommRing A] (g : A →+* B), spMap (ψ.comp g) = spMap ψ ≫ spMap g := fun g => by
    simp only [spMap, ← Spec.map_comp]; rfl
  have hyS : under y = spMap (ψ.comp (algebraMap S B)) ≫ z.x := by
    rw [hy, e0]
    simp only [under, Category.assoc, zPt_fst]
  have hys : y ≫ pullback.snd _ _ = spMap ((ψ.comp (algebraMap S B)).comp (algebraMap c.F S)) := by
    rw [hy]
    simp only [Category.assoc, zPt_snd]
    simp only [spMap, ← Spec.map_comp]
    rfl
  obtain ⟨v', w', hv', hw', hfr⟩ := GlobalTheory.CompanionTheory.Ar.FrameEig.isFramed_frPt E H D l Xo c τ S z F (ψ.comp (algebraMap S B)) y
    hp hq hyS hys
  have ev : v' = v := funext fun i => Over.OverMorphism.ext ((hv' i).trans (hv i).symm)
  have ew : w' = w := funext fun i => Over.OverMorphism.ext ((hw' i).trans (hw i).symm)
  rw [ev, ew] at hfr
  have hF := hfr U hU
  have hzx : spMap (algebraMap S B) ≫ z.x = under (spMap (algebraMap S B) ≫ zPt z) := by
    simp only [under, Category.assoc, zPt_fst]
  have hvv : ∀ k, (v k).left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap ψ) ≫
      (spMap (Formalism.L2.Pj.dualMap (algebraMap S B)) ≫ z.u τ (k.cast hp.symm)) := fun k => by
    rw [hv k, ← Category.assoc]
    exact congrArg (· ≫ _) (GlobalTheory.CompanionTheory.Ar.LieVB.spMap_dual_comp (algebraMap S B) ψ).symm
  have hww : ∀ k, (w k).left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap ψ) ≫
      (spMap (Formalism.L2.Pj.dualMap (algebraMap S B)) ≫ z.u (ComplexEmbedding.conjugate τ) (k.cast hq.symm)) := fun k => by
    rw [hw k, ← Category.assoc]
    exact congrArg (· ≫ _) (GlobalTheory.CompanionTheory.Ar.LieVB.spMap_dual_comp (algebraMap S B) ψ).symm
  obtain ⟨v₀, hc₁, hT₁⟩ := FieldStage.exists_pulled Y ψ _ y hy _ hzx v _ hvv C₁
    (fun i => spMap (Formalism.L2.Pj.dualMap θ) ≫ (e₁ i).left) hV₁
  obtain ⟨w₀, hc₂, hT₂⟩ := FieldStage.exists_pulled Y ψ _ y hy _ hzx w _ hww C₂
    (fun i => spMap (Formalism.L2.Pj.dualMap θ) ≫ (e₂ i).left) hV₂
  have hu₁ : IsUnit (ψ.mapMatrix C₁).det := by
    rw [← RingHom.map_det]; exact hC₁.map ψ
  have hu₂ : IsUnit (ψ.mapMatrix C₂).det := by
    rw [← RingHom.map_det]; exact hC₂.map ψ
  have hF₀ : IsFramed U τ ((ψ.comp (algebraMap S B)).comp (algebraMap c.F S)) y v₀ w₀ :=
    ⟨hF.1, hF.2.1, GlobalTheory.T.eigen_frame_of_unit_det_change Xo.X F Xo.univ.t.G (under y) (𝓞 E) Xo.univ.t.act _ D.p v v₀ (ψ.mapMatrix C₁) hF.2.2.1 hc₁ hu₁,
      GlobalTheory.T.eigen_frame_of_unit_det_change Xo.X F Xo.univ.t.G (under y) (𝓞 E) Xo.univ.t.act _ D.q w w₀ (ψ.mapMatrix C₂) hF.2.2.2 hc₂ hu₂⟩
  have hθF : spMap (ψ.comp θ) ≫ x = y ≫ Y.j := by
    rw [e0, Category.assoc, hθ, hy]
    simp only [Category.assoc]
  obtain ⟨h, θ', g₁, g₂, g₃⟩ := FieldStage.exists_germ Y Z x φ₂ hξ y hU (ψ.comp θ) hθF
  have hval₁ : ∀ i, ∃ v', Z.M.ValAt (y ≫ Y.j) (b₁ i) v' ∧ SameVec Y y (v₀ i) v' := fun i =>
    ⟨GlobalTheory.CompanionTheory.Ar.LieTangent.epsBase (ψ.comp θ) hθF ≫ e₁ i,
      FieldStage.valAt_of_chart Y Z x φ₂ y (ψ.comp θ) h θ' g₁ g₂ g₃ (b₁ i) (e₁ i) (ht₁ i) (hb₁ i) _ rfl,
      FieldStage.sameVec_of_tied Y (hT₁ i) (by
        rw [← Category.assoc]
        exact congrArg (· ≫ _) (GlobalTheory.CompanionTheory.Ar.LieVB.spMap_dual_comp θ ψ))⟩
  have hval₂ : ∀ i, ∃ v', Z.M.ValAt (y ≫ Y.j) (b₂ i) v' ∧ SameVec Y y (w₀ i) v' := fun i =>
    ⟨GlobalTheory.CompanionTheory.Ar.LieTangent.epsBase (ψ.comp θ) hθF ≫ e₂ i,
      FieldStage.valAt_of_chart Y Z x φ₂ y (ψ.comp θ) h θ' g₁ g₂ g₃ (b₂ i) (e₂ i) (ht₂ i) (hb₂ i) _ rfl,
      FieldStage.sameVec_of_tied Y (hT₂ i) (by
        rw [← Category.assoc]
        exact congrArg (· ≫ _) (GlobalTheory.CompanionTheory.Ar.LieVB.spMap_dual_comp θ ψ))⟩
  obtain ⟨h', s, hs₁, hs₂⟩ := hrep F _ y v₀ w₀ b₁ b₂ α κ hF₀ ha hb hval₁ hval₂
  have hs : s = θ' f := Z.gen.inj ⟨_, h'⟩ (hs₁.trans (hf.symm.trans (by rw [← g₂]; rfl)))
  have hvalue : φ F y v₀ w₀ = ψ (θ f) := by
    rw [← hs₂, hs]
    exact RingHom.congr_fun g₃ f
  have hchg := hφ.chg F _ y v w v₀ w₀ (ψ.mapMatrix C₁) (ψ.mapMatrix C₂) hF hF₀ hc₁ hc₂
  rw [hvalue, ← RingHom.map_det, ← RingHom.map_det] at hchg
  exact hchg.symm
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem germ_gives_hodgeLat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X : Scheme.{0}) (t : SAB H X) (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Sp Ω ⟶ X) (d r : ℕ) (M : LieModel t.G ξ (Fin d → Ω)) (S : GermSys t ξ M) (ρ : 𝓞 E →+* Module.End Ω (Fin d → Ω)), IsCptGen ξ → M.IsActOf t.act.act ρ → (∀ q : Cpt ξ, HFree (S.g q).B r) → ∃ 𝓗 : HodgeLat M.lat ρ H.bar r, S.Gives 𝓗 := by
  intro E _ _ _ H _ hstar X t Ω _ _ ξ d r M S ρ _hcg hact hfree
  classical
  have hρeq : ∀ (a : 𝓞 E) (v : Fin d → Ω),
      (GlobalTheory.CompanionTheory.Ar.Conj.rho S.g₀.B a).mulVec v = ρ a v := fun a v =>
    M.inj ((S.act₀ a v).trans (hact a v).symm)
  obtain ⟨⟨ρ0, hρ0⟩, -, -⟩ := GlobalTheory.T.formal_hermitian_action_pairing Ω d (𝓞 E) S.g₀.B
  let dd : ((Fin d → Ω) × (Fin d → Ω)) ≃ₗ[Ω] (Fin d → Ω) × Module.Dual Ω (Fin d → Ω) :=
    PositivityTheory.Xgn.GermHodgeLattice.dd Ω d
  have hdd : ∀ y, dd y = (y.1, dotProductBilin Ω Ω y.2) := fun y =>
    PositivityTheory.Xgn.GermHodgeLattice.dd_apply y
  have hsymm : ∀ y, ((dd.symm y).1, dotProductBilin Ω Ω (dd.symm y).2) = y := fun y => by
    rw [← hdd]; exact dd.apply_symm_apply y
  have hr1 : ∀ (a : 𝓞 E) (z : (Fin d → Ω) × (Fin d → Ω)),
      (GlobalTheory.CompanionTheory.Ar.Conj.rhoH S.g₀.B a z).1 = (GlobalTheory.CompanionTheory.Ar.Conj.rho S.g₀.B a).mulVec z.1 := by
    intro a z; simp [GlobalTheory.CompanionTheory.Ar.Conj.rhoH, Matrix.toLin'_apply]
  have hr2 : ∀ (a : 𝓞 E) (z : (Fin d → Ω) × (Fin d → Ω)),
      (GlobalTheory.CompanionTheory.Ar.Conj.rhoH S.g₀.B a z).2 =
        (GlobalTheory.CompanionTheory.Ar.Conj.rho S.g₀.B (star a)).transpose.mulVec z.2 -
          (GlobalTheory.CompanionTheory.Ar.Conj.bil (S.g₀.B.ad a) 1 1).transpose.mulVec z.1 := by
    intro a z; simp [GlobalTheory.CompanionTheory.Ar.Conj.rhoH, Matrix.toLin'_apply]
  let ρH : 𝓞 E →+* Module.End Ω ((Fin d → Ω) × Module.Dual Ω (Fin d → Ω)) :=
    { toFun := fun a => dd.toLinearMap ∘ₗ ρ0 a ∘ₗ dd.symm.toLinearMap
      map_one' := LinearMap.ext fun y => by simp
      map_mul' := fun a b => LinearMap.ext fun y => by simp [Module.End.mul_apply]
      map_zero' := LinearMap.ext fun y => by simp
      map_add' := fun a b => LinearMap.ext fun y => by simp }
  have hρH : ∀ a y, ρH a y = dd (GlobalTheory.CompanionTheory.Ar.Conj.rhoH S.g₀.B a (dd.symm y)) := by
    intro a y; show dd (ρ0 a (dd.symm y)) = _; rw [hρ0]
  let HL : GlobalTheory.CompanionTheory.Ar.Lat ξ ((Fin d → Ω) × Module.Dual Ω (Fin d → Ω)) := fun p =>
    Submodule.map (dd.toLinearMap.restrictScalars (GlobalTheory.CompanionTheory.Ar.regAt ξ p))
      (GlobalTheory.CompanionTheory.Ar.Flat.stdLat (GlobalTheory.CompanionTheory.Ar.regAt ξ p)
        (GlobalTheory.CompanionTheory.Ar.Conj.transH (S.φ p) (S.ψ p) (S.lam p)))
  have hmem : ∀ p y, dd y ∈ HL p ↔
      y ∈ GlobalTheory.CompanionTheory.Ar.Flat.stdLat (GlobalTheory.CompanionTheory.Ar.regAt ξ p)
        (GlobalTheory.CompanionTheory.Ar.Conj.transH (S.φ p) (S.ψ p) (S.lam p)) := by
    intro p y
    constructor
    · intro h
      obtain ⟨z, hz, hzy⟩ := Submodule.mem_map.mp h
      have : z = y := dd.injective hzy
      exact this ▸ hz
    · intro h
      exact Submodule.mem_map.mpr ⟨y, h, rfl⟩
  have hiso := fun p => GlobalTheory.T.formal_isomorphism_transport Ω d (𝓞 E) S.g₀.B (S.BK p) (S.φ p) (S.ψ p) (S.lam p) (S.iso p)
  have h_fst : ∀ (a : 𝓞 E) (y : (Fin d → Ω) × Module.Dual Ω (Fin d → Ω)),
      ((ρH a) y).1 = (ρ a) y.1 := by
    intro a y
    rw [hρH, hdd]
    dsimp only
    rw [hr1, ← hρeq]
    congr 1
  have h_inr : ∀ (a : 𝓞 E) (f : Module.Dual Ω (Fin d → Ω)),
      (ρH a) (0, f) = (0, f ∘ₗ ρ (H.bar a)) := by
    intro a f
    rw [hρH, hdd]
    have hz := hsymm (0, f)
    generalize dd.symm (0, f) = z at hz ⊢
    obtain ⟨hz1, hz2⟩ : z.1 = 0 ∧ dotProductBilin Ω Ω z.2 = f := Prod.ext_iff.mp hz
    subst hz2
    refine Prod.ext ?_ ?_
    · dsimp only
      rw [hr1, hz1, Matrix.mulVec_zero]
    · dsimp only
      rw [hr2, hz1, Matrix.mulVec_zero, sub_zero]
      refine LinearMap.ext fun u => ?_
      simp only [dotProductBilin_apply_apply, LinearMap.comp_apply, ← hρeq,
        Matrix.mulVec_transpose, hstar]
      exact (Matrix.dotProduct_mulVec _ _ _).symm
  have h_map : GlobalTheory.CompanionTheory.Ar.Lat.map HL
      (LinearMap.fst Ω (Fin d → Ω) (Module.Dual Ω (Fin d → Ω))) = M.lat := by
    funext p
    ext e
    rw [PositivityTheory.Xgn.GermHodgeLattice.lat_eq S p,
      ← PositivityTheory.Xgn.GermHodgeLattice.fst_stdLat (GlobalTheory.CompanionTheory.Ar.regAt ξ p) (S.φ p) (S.ψ p)
        (S.lam p) e]
    show e ∈ Submodule.map _ (HL p) ↔ _
    constructor
    · intro h
      obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp h
      obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hy
      exact ⟨z, hz, by simp [hdd]⟩
    · rintro ⟨z, hz, rfl⟩
      exact Submodule.mem_map.mpr ⟨dd z, (hmem p z).mpr hz, by simp [hdd]⟩
  have h_comap : GlobalTheory.CompanionTheory.Ar.Lat.comap HL
      (LinearMap.inr Ω (Fin d → Ω) (Module.Dual Ω (Fin d → Ω))) = M.lat.dual := by
    funext p
    ext f
    obtain ⟨hl1, hl2, -⟩ := hiso p
    have hz := hsymm (0, f)
    generalize dd.symm (0, f) = z at hz
    obtain ⟨-, hz2⟩ : z.1 = 0 ∧ dotProductBilin Ω Ω z.2 = f := Prod.ext_iff.mp hz
    subst hz2
    show ((0 : Fin d → Ω), dotProductBilin Ω Ω z.2) ∈ HL p ↔
      ∀ e ∈ M.lat p, dotProductBilin Ω Ω z.2 e ∈ GlobalTheory.CompanionTheory.Ar.regAt ξ p
    rw [show ((0 : Fin d → Ω), dotProductBilin Ω Ω z.2) = dd (0, z.2) from (hdd (0, z.2)).symm,
      hmem, PositivityTheory.Xgn.GermHodgeLattice.inr_stdLat _ _ _ _ hl1 hl2,
      PositivityTheory.Xgn.GermHodgeLattice.lat_eq S p]
    simp only [dotProductBilin_apply_apply]
  refine ⟨GlobalTheory.CompanionTheory.Ar.Flat.HodgeLat.mk ρH HL h_fst h_inr h_map h_comap ?_ ?_, ?_⟩
  · intro p
    obtain ⟨x₀, hli, hsp⟩ := hfree p
    obtain ⟨hl1, hl2, hbij, -, hint, -⟩ := hiso p
    obtain ⟨s, hs, hst⟩ :=
      PositivityTheory.Xgn.GermHodgeLattice.exists_finite (GlobalTheory.CompanionTheory.Ar.genMap ξ p) _ hsp
    obtain ⟨U, hpU, hU⟩ := PositivityTheory.Xgn.GermHodgeLattice.exists_open p s hs
    obtain ⟨U', hpU', hU'⟩ := S.loc p
    have hspanT := PositivityTheory.Xgn.GermHodgeLattice.span_stdLat (GlobalTheory.CompanionTheory.Ar.regAt ξ p)
      (GlobalTheory.CompanionTheory.Ar.Conj.transH (S.φ p) (S.ψ p) (S.lam p)) hbij.2
    rw [hst (GlobalTheory.CompanionTheory.Ar.regAt ξ p) (fun r' _ => (GlobalTheory.CompanionTheory.Ar.genMap ξ p).mem_range_self r')
      (GlobalTheory.CompanionTheory.Ar.Conj.transH (S.φ p) (S.ψ p) (S.lam p)), Submodule.span_span_of_tower] at hspanT
    have hcard := PositivityTheory.Xgn.GermHodgeLattice.card_eq _ hli hsp
    have hfin : Module.finrank Ω ((Fin d → Ω) × (Fin d → Ω)) = d + d := by simp
    have hG_li := linearIndependent_of_top_le_span_of_card_eq_finrank hspanT.ge
      (hcard.trans hfin.symm)
    have hF_li := hG_li.map' dd.toLinearMap dd.ker
    have hF_span := congrArg (Submodule.map dd.toLinearMap) hspanT
    rw [Submodule.map_span, ← Set.range_comp, Submodule.map_top, LinearEquiv.range] at hF_span
    simp only [Function.comp_def, LinearEquiv.coe_coe] at hF_span hF_li
    have hfam : ∀ (b : 𝓞 E) (j : Fin r),
        ρH b (dd (GlobalTheory.CompanionTheory.Ar.Conj.transH (S.φ p) (S.ψ p) (S.lam p)
          (PositivityTheory.Xgn.GermHodgeLattice.mp (GlobalTheory.CompanionTheory.Ar.genMap ξ p) (x₀ j)))) =
        dd (GlobalTheory.CompanionTheory.Ar.Conj.transH (S.φ p) (S.ψ p) (S.lam p)
          (PositivityTheory.Xgn.GermHodgeLattice.mp (GlobalTheory.CompanionTheory.Ar.genMap ξ p)
            (GlobalTheory.CompanionTheory.Ar.Conj.rhoH (S.g p).B b (x₀ j)))) := by
      intro b j
      rw [hρH, LinearEquiv.symm_apply_apply]
      exact congrArg dd ((LinearMap.congr_fun (hint b) _).trans
        (congrArg (GlobalTheory.CompanionTheory.Ar.Conj.transH (S.φ p) (S.ψ p) (S.lam p))
          (PositivityTheory.Xgn.GermHodgeLattice.rhoH_mp _ (S.mapK p) b (x₀ j))))
    refine ⟨U ⊓ U', ⟨hpU, hpU'⟩, fun i => dd (GlobalTheory.CompanionTheory.Ar.Conj.transH (S.φ p) (S.ψ p) (S.lam p)
      (PositivityTheory.Xgn.GermHodgeLattice.mp (GlobalTheory.CompanionTheory.Ar.genMap ξ p) (x₀ i))), fun q hq => ?_⟩
    have hHL : HL q = Submodule.map (dd.toLinearMap.restrictScalars (GlobalTheory.CompanionTheory.Ar.regAt ξ q))
        (GlobalTheory.CompanionTheory.Ar.Flat.stdLat (GlobalTheory.CompanionTheory.Ar.regAt ξ q)
          (GlobalTheory.CompanionTheory.Ar.Conj.transH (S.φ p) (S.ψ p) (S.lam p))) := by
      show Submodule.map _ _ = _
      rw [hU' q hq.2]
    rw [hst (GlobalTheory.CompanionTheory.Ar.regAt ξ q) (hU q hq.1), Submodule.map_span, ← Set.range_comp] at hHL
    simp only [Function.comp_def, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe] at hHL
    unfold GlobalTheory.CompanionTheory.Ar.HT.IsFreeOn
    simp only [hfam]
    refine ⟨hF_li, ?_, hHL⟩
    rw [hHL, Submodule.span_span_of_tower]
    exact hF_span
  · intro p _
    obtain ⟨U', hpU', hU'⟩ := S.loc p
    obtain ⟨hl1, hl2, -⟩ := hiso p
    have hfr : Module.finrank Ω (Fin d → Ω) = d := Module.finrank_fin_fun Ω
    have hinjP : Function.Injective (Matrix.toLin' (GlobalTheory.CompanionTheory.Ar.Conj.lin (S.φ p) 1)) := by
      intro u v huv
      have h := congrArg (Matrix.toLin' (GlobalTheory.CompanionTheory.Ar.Conj.lin (S.ψ p) 1)) huv
      simpa [Matrix.toLin'_apply, Matrix.mulVec_mulVec, hl2] using h
    have hsurjP : Function.Surjective (Matrix.toLin' (GlobalTheory.CompanionTheory.Ar.Conj.lin (S.φ p) 1)) := by
      intro v
      refine ⟨(GlobalTheory.CompanionTheory.Ar.Conj.lin (S.ψ p) 1).mulVec v, ?_⟩
      simp [Matrix.toLin'_apply, Matrix.mulVec_mulVec, hl1]
    have hcg : (fun l : Fin d => (GlobalTheory.CompanionTheory.Ar.Conj.lin (S.φ p) 1).mulVec (Pi.single l 1)) =
        (Matrix.toLin' (GlobalTheory.CompanionTheory.Ar.Conj.lin (S.φ p) 1)) ∘ (Pi.basisFun Ω (Fin d)) := by
      funext l; simp [Matrix.toLin'_apply]
    have hc_li : LinearIndependent Ω
        (fun l : Fin d => (GlobalTheory.CompanionTheory.Ar.Conj.lin (S.φ p) 1).mulVec (Pi.single l 1)) := by
      rw [hcg]
      exact (Pi.basisFun Ω (Fin d)).linearIndependent.map' _ (LinearMap.ker_eq_bot.mpr hinjP)
    have hc_span : Submodule.span Ω (Set.range
        (fun l : Fin d => (GlobalTheory.CompanionTheory.Ar.Conj.lin (S.φ p) 1).mulVec (Pi.single l 1))) = ⊤ := by
      rw [hcg, Set.range_comp, ← Submodule.map_span, (Pi.basisFun Ω (Fin d)).span_eq,
        Submodule.map_top, LinearMap.range_eq_top.mpr hsurjP]
    refine ⟨U', hpU',
      (fun l : Fin d => (GlobalTheory.CompanionTheory.Ar.Conj.lin (S.φ p) 1).mulVec (Pi.single l 1)) ∘ (finCongr hfr),
      ?_, ?_⟩
    · rw [(finCongr hfr).surjective.range_comp]; exact hc_span
    · intro q _ hq
      unfold GlobalTheory.CompanionTheory.Ar.Lat.IsFrameAt
      refine ⟨hc_li.comp _ (finCongr hfr).injective, ?_⟩
      rw [(finCongr hfr).surjective.range_comp]
      ext e
      rw [PositivityTheory.Xgn.GermHodgeLattice.lat_eq S q,
        ← PositivityTheory.Xgn.GermHodgeLattice.fst_stdLat (GlobalTheory.CompanionTheory.Ar.regAt ξ q) (S.φ q) (S.ψ q)
          (S.lam q) e,
        ← hU' q hq, PositivityTheory.Xgn.GermHodgeLattice.fst_stdLat]
  · unfold GlobalTheory.CompanionTheory.Ar.Flat.GermSys.Gives
    refine ⟨fun a y => ?_, fun p y => ?_⟩
    · show ρH a (y.1, dotProductBilin Ω Ω y.2) = _
      rw [show (y.1, dotProductBilin Ω Ω y.2) = dd y from (hdd y).symm, hρH,
        LinearEquiv.symm_apply_apply, hdd]
    · show (y.1, dotProductBilin Ω Ω y.2) ∈ HL p ↔ _
      rw [← hdd]
      exact hmem p y

end GlobalTheory.CompanionTheory.Ar.Flat
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights


theorem _root_.GlobalTheory.T.exists_graded_sandwich_coordinates : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (K : Type) [Fintype K] (J : K → Type)
    (y : (Σ k, J k) → Ω) (G : Over X) [GrpObj G]
    (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (V : Lat ξ Li) (r : ℕ) (b₀ : Fin r → Li)
    (m : ℕ) (i : Fin r) (a : K → ℤ) (e₀ : Ω),
    LinearIndependent Ω b₀ → Sandwich M V b₀ m → (V.gr b₀ i).IsDegOn Set.univ y a e₀ →
    ∀ (p : Cpt ξ) (c : (k : K) → J k), InChart ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) c p →
    ∃ (b : Fin r → Li) (π : Fin r → Module.Dual Ω Li) (κ : Ω), (∀ n : ℕ, flagStep Ω b n = flagStep Ω b₀ n) ∧
      V.IsFrameAt b p ∧ (∀ j, (m : Ω) • b j ∈ M.lat p) ∧ (∀ j l, π j (b l) = if j = l then 1 else 0) ∧
      (∀ j, ∀ e ∈ M.lat p, (m : Ω) * π j e ∈ regAt ξ p) ∧ κ ≠ 0 ∧ κ ∈ regAt ξ p ∧ κ⁻¹ ∈ regAt ξ p ∧
      ∀ (e : Li) (t : Ω), e ∈ flagStep Ω b₀ (i + 1) → IsCls b₀ i e t → t / gen y a e₀ c = π i e * κ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.RootHt.cls_frame | exact GlobalTheory.CompanionTheory.Ar.RootHt.cls_frame | (intros; apply GlobalTheory.CompanionTheory.Ar.RootHt.cls_frame <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.abelian_quotient_lattice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X : Scheme.{0}) (t : SAB H X) (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p] (x : Sp k ⟶ X) (Q : AbQuot t x) (d d' : ℕ) (g : GermAt t x d) (gB : GermAt Q.tB (𝟙 (Sp k)) d'), ∃ (Λ : Type) (_ : AddCommGroup Λ) (_ : Module (𝓞 E) Λ) (_ : Module.Free ℤ Λ) (_ : Module.Finite ℤ Λ) (P : Matrix (Fin d') (Fin d) k) (j : TensorProduct ℤ k Λ →ₗ[k] (Fin d → k)), Q.IsDiff g gB P ∧ Function.Surjective P.mulVec ∧ Function.Injective j ∧ (∀ u, P.mulVec u = 0 ↔ u ∈ LinearMap.range j) ∧ (∀ a, P * rho g.B a = rho gB.B a * P) ∧ ∀ a v, j (LinearMap.baseChange k ((LinearMap.lsmul (𝓞 E) Λ a).restrictScalars ℤ) v) = (rho g.B a).mulVec (j v) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LieSeq.lie_seq | exact GlobalTheory.CompanionTheory.Ar.LieSeq.lie_seq | (intros; apply GlobalTheory.CompanionTheory.Ar.LieSeq.lie_seq <;> assumption)
end
