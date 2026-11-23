module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle010
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsOrthFull
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle156
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle096
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle193
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle224
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle220
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle191
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle027
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle186
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle014
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle225
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverOfIsIso
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle155
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.NotIsGlobalPrimePow
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle074
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SlopeNorm

open GroundTheory.Heights₂.Heights

theorem core_left {V : Type} [AddCommGroup V] [Module ℂ V] (c₁ c₂ : InnerProductSpace.Core ℂ V) (W : Set V)
    (hW : Submodule.span ℂ W = ⊤) (a : V) (h : ∀ b ∈ W, c₁.inner b a = c₂.inner b a) (b : V) :
    c₁.inner b a = c₂.inner b a := by
  have hb : b ∈ Submodule.span ℂ W := hW ▸ Submodule.mem_top
  induction hb using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero =>
    have e₁ := c₁.smul_left 0 a 0
    have e₂ := c₂.smul_left 0 a 0
    simp only [smul_zero, map_zero, zero_mul] at e₁ e₂
    rw [e₁, e₂]
  | add x y _ _ hx hy => rw [c₁.add_left, c₂.add_left, hx, hy]
  | smul r x _ hx => rw [c₁.smul_left, c₂.smul_left, hx]

theorem core_eq {V : Type} [AddCommGroup V] [Module ℂ V] (c₁ c₂ : InnerProductSpace.Core ℂ V) (W : Set V)
    (hW : Submodule.span ℂ W = ⊤) (h : ∀ a ∈ W, ∀ b ∈ W, c₁.inner a b = c₂.inner a b) (a b : V) :
    c₁.inner a b = c₂.inner a b := by
  refine core_left c₁ c₂ W hW b (fun x hx => ?_) a
  have e := core_left c₁ c₂ W hW x (fun y hy => h y hy x hx) b
  rw [← c₁.conj_inner_symm, ← c₂.conj_inner_symm, e]

variable {L : Type} [Field L]

theorem span_tmul (σ : L →+* ℂ) (V : Type) [AddCommGroup V] [Module (𝓞 L) V] :
    Submodule.span ℂ (Set.range fun e : V => (1 : ComplexAt σ) ⊗ₜ[𝓞 L] e) = ⊤ := by
  refine (Submodule.eq_top_iff'.2 fun x => ?_)
  induction x using TensorProduct.induction_on with
  | zero => exact Submodule.zero_mem _
  | tmul c e =>
    have hc : c ⊗ₜ[𝓞 L] e = ((ComplexAt.ofComplex σ).symm c : ℂ) • ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] e) := by
      rw [TensorProduct.smul_tmul', ComplexAt.complex_smul_def]
      simp
    rw [hc]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨e, rfl⟩)
  | add a b ha hb => exact Submodule.add_mem _ ha hb

theorem spComp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (d : A →+* B) (c : B →+* C) :
    spMap c ≫ spMap d = spMap (c.comp d) := by
  simp only [spMap, ← Spec.map_comp]
  rfl

def lf {S : Scheme.{0}} {G : Over S} {R : Type} [CommRing R] {x : Sp R ⟶ S} (v : epsAt x ⟶ G) :
    Sp (DualNumber R) ⟶ G.left :=
  v.left

theorem exists_transport {S : Scheme.{0}} {G : Over S} [GrpObj G] {R : Type} [CommRing R] {x x' : Sp R ⟶ S}
    (h : x = x') {V : Type} [AddCommGroup V] [Module R V] (M : LieModel G x V) :
    ∃ M' : LieModel G x' V, ∀ e, lf (M'.pt e) = lf (M.pt e) := by
  subst h
  exact ⟨M, fun _ => rfl⟩

theorem exists_lift {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {R : Type} [CommRing R] (x' : Sp R ⟶ S') {b : Sp R ⟶ S}
    (hb : x' ≫ f = b) {V : Type} [AddCommGroup V] [Module R V] (M : LieModel G b V) :
    ∃ M' : LieModel G' x' V, ∀ e, lf (M'.pt e) ≫ φ = lf (M.pt e) := by
  subst hb
  exact (LiePull.lieModel_pullback S S' G G' f φ h R x' V).1 M

theorem exists_push {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {R : Type} [CommRing R] (x' : Sp R ⟶ S')
    (v : epsAt x' ⟶ G') : ∃ u : epsAt (x' ≫ f) ⟶ G, lf v ≫ φ = lf u :=
  ⟨LiePull.tanPts h x' v, rfl⟩

theorem hodge_congr {S : Scheme.{0}} {G : Over S} [GrpObj G] (Lb : LB G.left) {z z' : Sp ℂ ⟶ S} (h : z = z')
    {v w : epsAt z ⟶ G} {v' w' : epsAt z' ⟶ G} (hv : lf v = lf v') (hw : lf w = lf w') {c : ℂ}
    (hc : HodgeIP G Lb z v w c) : HodgeIP G Lb z' v' w' c := by
  subst h
  obtain rfl : v = v' := Over.OverMorphism.ext hv
  obtain rfl : w = w' := Over.OverMorphism.ext hw
  exact hc

theorem ip_congr {S : Scheme.{0}} {G : Over S}
    (ip : ∀ z : Sp ℂ ⟶ S, (epsAt z ⟶ G) → (epsAt z ⟶ G) → ℂ) {z z' : Sp ℂ ⟶ S} (h : z = z')
    {v w : epsAt z ⟶ G} {v' w' : epsAt z' ⟶ G} (hv : lf v = lf v') (hw : lf w = lf w') :
    ip z v w = ip z' v' w' := by
  subst h
  obtain rfl : v = v' := Over.OverMorphism.ext hv
  obtain rfl : w = w' := Over.OverMorphism.ext hw
  rfl

end GlobalTheory.CompanionTheory.Ar.SlopeNorm


open GroundTheory.Heights₂.Heights GlobalTheory.CompanionTheory.Ar.SlopeNorm GlobalTheory.CompanionTheory.Ar.LiePull in
theorem GlobalTheory.CompanionTheory.Ar.SlopeNorm.sqAt_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (L₁ L : Type) [Field L₁] [Field L] [NumberField L] (e₂ : L₁ →+* L) (z₁ : Sp L₁ ⟶ X) (z : Sp (𝓞 L) ⟶ X) (hz : spMap (algebraMap (𝓞 L) L) ≫ z = spMap e₂ ≫ z₁) (P₁ : AbPart t z₁) (P₂ : AbPart t (spMap e₂ ≫ z₁)) (mK2 : SABMap P₂.tK P₁.tK (spMap e₂)) (mB2 : SABMap P₂.tB P₁.tB (spMap e₂)) (c1 : mK2.φ ≫ P₁.m.φ = P₂.m.φ) (c2 : mK2.φ ≫ (P₁.τ.q ≫ P₁.e.hom).left = (P₂.τ.q ≫ P₂.e.hom).left ≫ mB2.φ) (t' : SAB H (Sp (𝓞 L))) (tK : SAB H (Sp L)) (m' : SABMap tK t' (spMap (algebraMap (𝓞 L) L))) (mP : SABMap tK P₁.tB (spMap e₂)) (w : P₂.tB.G.left ⟶ tK.G.left) (hw : w ≫ mP.φ = mB2.φ) (hw' : w ≫ tK.G.hom = P₂.tB.G.hom) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (Li : Type) [AddCommGroup Li] [Module Ω Li] (M₀ : LieModel t.G ξ Li) (K : Type) (J : K → Type) (y : (Σ k, J k) → Ω) (h : LieMetric M₀ y) (K₀ : ℝ) (hQ : ∀ (zc : Sp ℂ ⟶ X) (P : AbPart t zc) (v : epsAt (𝟙 (Sp ℂ)) ⟶ P.tK.G) (v₀ : epsAt zc ⟶ t.G) (c : ℂ), IsTanAt _ _ v → v.left ≫ P.m.φ = v₀.left → HodgeIP P.tB.G P.tB.PP.L (𝟙 _) (v ≫ P.τ.q ≫ P.e.hom) (v ≫ P.τ.q ≫ P.e.hom) c → c.re ≤ K₀ * (h.ip zc v₀ v₀).re) (B B' : GroundTheory.Heights₂.Heights.HermitianBundle.{0} L) (MB : LieModel t.G z B.carrier) (MB' : LieModel t'.G (𝟙 _) B'.carrier) (hB : IsFibre (fun z v w c => c = h.ip z v w) z B MB) (hB' : IsFibre (HodgeIP t'.G t'.PP.L) (𝟙 _) B' MB') (f : B.carrier →ₗ[𝓞 L] B'.carrier) (hf : ∀ (e : B.carrier) (v : epsAt (𝟙 (Sp L)) ⟶ P₂.tK.G), (v.left ≫ P₂.m.φ = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap (𝓞 L) L)) ≫ (MB.pt e).left) → ((v ≫ P₂.τ.q).left ≫ (P₂.e.hom.left ≫ w ≫ m'.φ) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap (𝓞 L) L)) ≫ (MB'.pt (f e)).left)) (σ : L →+* ℂ) (x : GroundTheory.Heights₂.Heights.Fibre σ B.carrier), sqAt B' σ (f.lTensor (GroundTheory.Heights₂.Heights.ComplexAt σ) x) ≤ K₀ * sqAt B σ x := by
  intro E _ _ _ H X t L₁ L _ _ _ e₂ z₁ z hz P₁ P₂ mK2 mB2 c1 c2 t' tK m' mP w hw hw' Ω _ ξ Li _ _ M₀ K J y h K₀ hQ
    B B' MB MB' hB hB' f hf σ x
  haveI : Smooth t.G.hom := t.semi.smooth
  haveI : Smooth t'.G.hom := t'.semi.smooth
  obtain ⟨Pσ, mKσ, mBσ, d1, d2⟩ := GlobalTheory.T.abelian_part_base_change E H X t L₁ ℂ z₁ P₁ (σ.comp e₂)
  obtain ⟨Mσ, hMσ⟩ := GlobalTheory.T.lie_model_complex_base_change X t.G L z B.carrier MB σ
  obtain ⟨Mσ', hMσ'⟩ := GlobalTheory.T.lie_model_complex_base_change (Sp (𝓞 L)) t'.G L (𝟙 _) B'.carrier MB' σ
  have hb : spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ z = spMap (σ.comp e₂) ≫ z₁ := by
    rw [← spComp (algebraMap (𝓞 L) L) σ, ← spComp e₂ σ, Category.assoc, Category.assoc, hz]
  have hb' : spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ 𝟙 _ = spMap σ ≫ spMap (algebraMap (𝓞 L) L) := by
    rw [Category.comp_id, spComp]
  have hb2 : spMap σ ≫ spMap e₂ = 𝟙 _ ≫ spMap (σ.comp e₂) := by
    rw [Category.id_comp, spComp]

  obtain ⟨core₁, hcore₁⟩ := h.herm _ (Fibre σ B.carrier) Mσ
  have h1 : ∀ a b, (B.metric.form σ).inner a b = h.ip _ (Mσ.pt a) (Mσ.pt b) := by
    intro a b
    rw [← hcore₁]
    refine core_eq _ _ _ (span_tmul σ _) ?_ a b
    rintro _ ⟨e, rfl⟩ _ ⟨e', rfl⟩
    rw [hcore₁]
    exact hB σ e e' _ _ (hMσ e) (hMσ e')

  obtain ⟨Mz, hMz⟩ := exists_transport hb' Mσ'
  have h2 : ∀ a b, HodgeIP t'.G t'.PP.L (spMap σ ≫ spMap (algebraMap (𝓞 L) L)) (Mz.pt a) (Mz.pt b)
      ((B'.metric.form σ).inner a b) := by
    refine GlobalTheory.T.hodge_inner_product_on_span E H (Sp L) (Sp (𝓞 L)) tK t' (spMap (algebraMap (𝓞 L) L)) m' (spMap σ)
      (Fibre σ B'.carrier) Mz (B'.metric.form σ) (Set.range fun e => (1 : ComplexAt σ) ⊗ₜ[𝓞 L] e)
      ⟨0, TensorProduct.tmul_zero _ _⟩ (span_tmul σ _) ?_
    rintro _ ⟨e, rfl⟩ _ ⟨e', rfl⟩
    exact hodge_congr t'.PP.L hb' (hMz _).symm (hMz _).symm (hB' σ e e' _ _ (hMσ' e) (hMσ' e'))

  obtain ⟨Mc, hMc⟩ := exists_transport hb Mσ
  obtain ⟨Mv, hMv⟩ := exists_lift Pσ.m.cart (𝟙 _) (by rw [Category.id_comp]; exact hb.symm) Mσ
  obtain ⟨Mu, hMu⟩ := exists_lift m'.cart (spMap σ) hb'.symm Mσ'
  have hv₀ : lf (Mv.pt x) ≫ Pσ.m.φ = lf (Mc.pt x) := (hMv x).trans (hMc x).symm
  have h3 := GlobalTheory.T.abelian_part_maps_compatible_left E H X t L₁ L e₂ z₁ z hz P₁ P₂ mK2 mB2 c1 c2 t' tK m' mP w hw hw' B.carrier B'.carrier
    MB MB' f hf σ Pσ mKσ mBσ d1 d2 Mσ hMσ Mσ' hMσ' x (Mv.pt x) (Mu.pt (f.lTensor (ComplexAt σ) x)) (hMv x) (hMu _)

  have hUz : lf (Mu.pt (f.lTensor (ComplexAt σ) x)) ≫ m'.φ = lf (Mz.pt (f.lTensor (ComplexAt σ) x)) :=
    (hMu _).trans (hMz _).symm
  have a1 := ((GlobalTheory.T.hodge_inner_product_pullback_unique E H (Sp L) (Sp (𝓞 L)) tK t' (spMap (algebraMap (𝓞 L) L)) m' (spMap σ)
    (Mu.pt (f.lTensor (ComplexAt σ) x)) (Mu.pt (f.lTensor (ComplexAt σ) x))
    (Mz.pt (f.lTensor (ComplexAt σ) x)) (Mz.pt (f.lTensor (ComplexAt σ) x)) hUz hUz).1 _).2
    (h2 (f.lTensor (ComplexAt σ) x) (f.lTensor (ComplexAt σ) x))
  obtain ⟨U, hU⟩ := exists_push mP.cart (spMap σ) (Mu.pt (f.lTensor (ComplexAt σ) x))
  obtain ⟨Vv, hV⟩ := exists_push mBσ.cart (𝟙 _) (Mv.pt x ≫ Pσ.τ.q ≫ Pσ.e.hom)
  have a2 := ((GlobalTheory.T.hodge_inner_product_pullback_unique E H (Sp L) (Sp L₁) tK P₁.tB (spMap e₂) mP (spMap σ)
    (Mu.pt (f.lTensor (ComplexAt σ) x)) (Mu.pt (f.lTensor (ComplexAt σ) x)) U U hU hU).1 _).1 a1
  have hUV : lf U = lf Vv := hU.symm.trans (Eq.trans h3 hV)
  have a3 := ((GlobalTheory.T.hodge_inner_product_pullback_unique E H (Sp ℂ) (Sp L₁) Pσ.tB P₁.tB (spMap (σ.comp e₂)) mBσ (𝟙 _)
    (Mv.pt x ≫ Pσ.τ.q ≫ Pσ.e.hom) (Mv.pt x ≫ Pσ.τ.q ≫ Pσ.e.hom) Vv Vv hV hV).1 _).2
    (hodge_congr P₁.tB.PP.L hb2 hUV hUV a2)
  have h5 := hQ (spMap (σ.comp e₂) ≫ z₁) Pσ (Mv.pt x) (Mc.pt x) _ (Mv.tan x) hv₀ a3
  have h6 : h.ip _ (Mc.pt x) (Mc.pt x) = (B.metric.form σ).inner x x := by
    rw [h1]
    exact ip_congr h.ip hb.symm (hMc x) (hMc x)
  rw [h6] at h5
  exact h5
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HodgeBC


open GroundTheory.Heights₂.Heights in
theorem span_one_tmul {L : Type} [Field L] (e : L →+* ℂ) (V : Type) [AddCommGroup V] [Module (𝓞 L) V] :
    Submodule.span ℂ {w : Fibre e V | ∃ y : V, w = (1 : ComplexAt e) ⊗ₜ[𝓞 L] y} = ⊤ := by
  rw [eq_top_iff]
  rintro w -
  change ComplexAt e ⊗[𝓞 L] V at w
  induction w using TensorProduct.induction_on with
  | zero => exact Submodule.zero_mem _
  | tmul c y =>
    have h : (c ⊗ₜ[𝓞 L] y : ComplexAt e ⊗[𝓞 L] V) = c • ((1 : ComplexAt e) ⊗ₜ[𝓞 L] y) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
    rw [h]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨y, rfl⟩)
  | add a b ha hb => exact Submodule.add_mem _ ha hb

private theorem isGrpPullback_one_left {S : Scheme.{0}} {G : Over S} [GrpObj G] (A : Over S) :
    (1 : A ⟶ G).left = A.hom ≫ (1 : Over.mk (𝟙 S) ⟶ G).left := by
  have h := LieSigma.comp_one_over (M := G) (Over.homMk A.hom (by simp) : A ⟶ Over.mk (𝟙 S))
  calc (1 : A ⟶ G).left
      = ((Over.homMk A.hom (by simp) : A ⟶ Over.mk (𝟙 S)) ≫ (1 : Over.mk (𝟙 S) ⟶ G)).left := by rw [h]
    _ = A.hom ≫ (1 : Over.mk (𝟙 S) ⟶ G).left := by rw [Over.comp_left]; rfl

private theorem one_left_comp_eq_comp_one_of_isGrpPullback {X X' : Scheme.{0}} (G' : Over X') [GrpObj G'] (G : Over X) [GrpObj G]
    (f : X' ⟶ X) (φ : G'.left ⟶ G.left) (hφ : IsGrpPullback G' G f φ) :
    (1 : Over.mk (𝟙 X') ⟶ G').left ≫ φ = f ≫ (1 : Over.mk (𝟙 X) ⟶ G).left := by
  have hε : (1 : Over.mk (𝟙 X') ⟶ G').left ≫ G'.hom = 𝟙 X' := Over.w (1 : Over.mk (𝟙 X') ⟶ G')
  have hw : ((1 : Over.mk (𝟙 X') ⟶ G').left ≫ φ) ≫ G.hom = (Over.mk ((Over.mk (𝟙 X')).hom ≫ f)).hom := by
    rw [Category.assoc, hφ.1.w, ← Category.assoc, hε]
    simp
  let x₀ : Over.mk ((Over.mk (𝟙 X')).hom ≫ f) ⟶ G := Over.homMk ((1 : Over.mk (𝟙 X') ⟶ G').left ≫ φ) hw
  have hmul := hφ.2 (Over.mk (𝟙 X')) 1 1 x₀ x₀ rfl rfl
  have hx : x₀ * x₀ = x₀ * 1 := by
    rw [_root_.mul_one]
    apply Over.OverMorphism.ext
    rw [hmul, _root_.mul_one]
    rfl
  have h1 : x₀ = 1 := _root_.mul_left_cancel hx
  have h2 : x₀.left = (1 : Over.mk ((Over.mk (𝟙 X')).hom ≫ f) ⟶ G).left := by rw [h1]
  rw [isGrpPullback_one_left] at h2
  simpa [x₀] using h2

private theorem exists_tanAt_comp_of_sabMap {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X X' : Scheme.{0}}
    {t : SAB H X} {t' : SAB H X'} {f : X' ⟶ X} (m : SABMap t' t f) (z : Sp ℂ ⟶ X')
    (v : epsAt z ⟶ t'.G) (hv : IsTanAt t'.G z v) :
    ∃ w : epsAt (z ≫ f) ⟶ t.G, w.left = v.left ≫ m.φ ∧ IsTanAt t.G (z ≫ f) w := by
  have hsq : m.φ ≫ t.G.hom = t'.G.hom ≫ f := m.cart.1.w
  refine ⟨Over.homMk (v.left ≫ m.φ) ?_, rfl, ?_⟩
  · rw [Category.assoc, hsq, ← Category.assoc, Over.w v]
    simp [epsAt]
  · have hv' : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) ≫ v.left
        = (1 : Over.mk z ⟶ t'.G).left := hv
    show Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) ≫ (v.left ≫ m.φ)
        = (1 : Over.mk (z ≫ f) ⟶ t.G).left
    have h1 : (1 : Over.mk z ⟶ t'.G).left = (Over.mk z).hom ≫ (1 : Over.mk (𝟙 X') ⟶ t'.G).left :=
      isGrpPullback_one_left _
    have h2 : (1 : Over.mk (z ≫ f) ⟶ t.G).left = (Over.mk (z ≫ f)).hom ≫ (1 : Over.mk (𝟙 X) ⟶ t.G).left :=
      isGrpPullback_one_left _
    rw [h2, ← Category.assoc, hv', h1, Category.assoc, one_left_comp_eq_comp_one_of_isGrpPullback t'.G t.G f m.φ m.cart]
    simp [epsAt]


open LieMove in
theorem hodge_along {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X₀ X₁ X₂ : Scheme.{0}}
    {t₀ : SAB H X₀} {t₁ : SAB H X₁} {t₂ : SAB H X₂} {f₀ : X₀ ⟶ X₁} {f₁ : X₁ ⟶ X₂} (m₀ : SABMap t₀ t₁ f₀)
    (m₁ : SABMap t₁ t₂ f₁) (z : Sp ℂ ⟶ X₀) (p : Sp ℂ ⟶ X₂) (hp : p = (z ≫ f₀) ≫ f₁)
    {V : Type} [AddCommGroup V] [Module ℂ V] (Mp : LieModel t₂.G p V) (core : InnerProductSpace.Core ℂ V) (W : Set V)
    (h0 : (0 : V) ∈ W) (hs : Submodule.span ℂ W = ⊤)
    (hW : ∀ a ∈ W, ∀ b ∈ W, HodgeIP t₂.G t₂.PP.L p (Mp.pt a) (Mp.pt b) (core.inner a b))
    {V' : Type} (Tn : V' → (epsAt z ⟶ t₀.G)) (hT : ∀ x, IsTanAt t₀.G z (Tn x)) :
    ∃ D : V' → V, (∀ x x', HodgeIP t₀.G t₀.PP.L z (Tn x) (Tn x') (core.inner (D x) (D x'))) ∧
      ∀ x a, (Tn x).left ≫ m₀.φ ≫ m₁.φ = (Mp.pt a).left → D x = a := by
  subst hp
  have hall : ∀ a b : V, HodgeIP t₂.G t₂.PP.L ((z ≫ f₀) ≫ f₁) (Mp.pt a) (Mp.pt b) (core.inner a b) :=
    GlobalTheory.T.hodge_inner_product_on_span E H X₁ X₂ t₁ t₂ f₁ m₁ (z ≫ f₀) V Mp core W h0 hs hW
  have key : ∀ x, ∃ w₁ : epsAt (z ≫ f₀) ⟶ t₁.G, w₁.left = (Tn x).left ≫ m₀.φ ∧
      ∃ a : V, (Mp.pt a).left = w₁.left ≫ m₁.φ := by
    intro x
    obtain ⟨w₁, hw₁, ht₁⟩ := exists_tanAt_comp_of_sabMap m₀ z (Tn x) (hT x)
    obtain ⟨w₂, hw₂, ht₂⟩ := exists_tanAt_comp_of_sabMap m₁ (z ≫ f₀) w₁ ht₁
    obtain ⟨a, ha⟩ := Mp.onto w₂ ht₂
    exact ⟨w₁, hw₁, a, by rw [ha, hw₂]⟩
  choose w₁ hw₁ D hD using key
  refine ⟨D, fun x x' => ?_, fun x a h => ?_⟩
  · rw [GlobalTheory.T.hodge_inner_product_map_iff E H X₁ t₁ X₀ t₀ f₀ m₀ z (Tn x) (Tn x') (w₁ x) (w₁ x') _ (hw₁ x) (hw₁ x'),
      GlobalTheory.T.hodge_inner_product_map_iff E H X₂ t₂ X₁ t₁ f₁ m₁ (z ≫ f₀) (w₁ x) (w₁ x') (Mp.pt (D x)) (Mp.pt (D x')) _ (hD x) (hD x')]
    exact hall _ _
  · apply Mp.inj
    apply Over.OverMorphism.ext
    rw [hD x, hw₁ x]
    exact (Category.assoc _ _ _).trans h

theorem lifts_left {S : Scheme.{0}} {R R' : Type} [CommRing R] [CommRing R'] {G : Over S} [GrpObj G]
    {x : Spec (CommRingCat.of R) ⟶ S} {V : Type} [AddCommGroup V] [Module R V] (M : LieModel G x V) (c : R →+* R') (a : V)
    (v : epsAt (spMap c ≫ x) ⟶ G) (h : (v.left ≫ (𝟙 G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap c) ≫ (M.pt a).left)) :
    v.left = spMap (dualMap c) ≫ (M.pt a).left := by
  have h' : v.left ≫ 𝟙 G.left = spMap (dualMap c) ≫ (M.pt a).left := h
  simpa using h'


open GroundTheory.Heights₂.Heights in
theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (t' : SAB H (Sp (𝓞 L))) (tB : SAB H (Sp L)) (tC : SAB H (Sp ℂ)) (e : L →+* ℂ) (m' : SABMap tB t' (spMap (algebraMap (𝓞 L) L))) (mB : SABMap tC tB (spMap e)) (B : GroundTheory.Heights₂.Heights.HermitianBundle.{0} L) (MB : LieModel t'.G (𝟙 _) B.carrier), IsFibre (HodgeIP t'.G t'.PP.L) (𝟙 _) B MB → ∀ (V' : Type) (Tn : V' → (epsAt (𝟙 (Sp ℂ)) ⟶ tC.G)), (∀ x, IsTanAt tC.G (𝟙 _) (Tn x)) → ∃ hb : V' → V' → ℂ, (∀ x x', HodgeIP tC.G tC.PP.L (𝟙 _) (Tn x) (Tn x') (hb x x')) ∧ ∀ (x x' : V') (y y' : B.carrier), (Tn x).left ≫ mB.φ ≫ m'.φ = spMap (dualMap (e.comp (algebraMap (𝓞 L) L))) ≫ (MB.pt y).left → (Tn x').left ≫ mB.φ ≫ m'.φ = spMap (dualMap (e.comp (algebraMap (𝓞 L) L))) ≫ (MB.pt y').left → hb x x' = (B.metric.form e).inner ((1 : GroundTheory.Heights₂.Heights.ComplexAt e) ⊗ₜ[𝓞 L] y) ((1 : GroundTheory.Heights₂.Heights.ComplexAt e) ⊗ₜ[𝓞 L] y') := by
  intro E _ _ _ H L _ _ t' tB tC e m' mB B MB hF V' Tn hT
  haveI : Smooth t'.G.hom := @ReciprocityTheory.ChartRestriction.G.Semi.IsSemiAbelian.smooth _ _ _ t'.semi
  obtain ⟨Mσ, hMσ⟩ := LieSigma.lieModel_fibre (Sp (𝓞 L)) t'.G L (𝟙 _) B.carrier MB e
  have hp : spMap (e.comp (algebraMap (𝓞 L) L)) ≫ 𝟙 (Sp (𝓞 L))
      = (𝟙 (Sp ℂ) ≫ spMap e) ≫ spMap (algebraMap (𝓞 L) L) := by
    simp only [Category.comp_id, Category.id_comp]
    unfold spMap
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  obtain ⟨D, hD1, hD2⟩ := hodge_along mB m' (𝟙 _) _ hp Mσ (B.metric.form e)
    {w | ∃ y : B.carrier, w = (1 : ComplexAt e) ⊗ₜ[𝓞 L] y} ⟨0, by simp⟩ (span_one_tmul e B.carrier)
    (by
      rintro a ⟨y, rfl⟩ b ⟨y', rfl⟩
      exact hF e y y' _ _ (hMσ y) (hMσ y'))
    Tn hT
  refine ⟨fun x x' => (B.metric.form e).inner (D x) (D x'), hD1, ?_⟩
  intro x x' y y' hx hx'
  have e1 : D x = (1 : ComplexAt e) ⊗ₜ[𝓞 L] y :=
    hD2 x _ (hx.trans (lifts_left MB _ _ _ (hMσ y)).symm)
  have e2 : D x' = (1 : ComplexAt e) ⊗ₜ[𝓞 L] y' :=
    hD2 x' _ (hx'.trans (lifts_left MB _ _ _ (hMσ y')).symm)
  simp only [e1, e2]

end GlobalTheory.CompanionTheory.Ar.HodgeBC
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.formal_germs_isomorphic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0), PowFns t → ∀ (S : Type) [CommRing S] [IsLocalRing S] (x : Sp S ⟶ X0) (d : ℕ) (g g₂ : GermAt t x d), ∃ (φ ψ : Germ.Pt S 1 d) (lam : Germ.PS S 2 d), IsIso g.B g₂.B φ ψ lam ∧ ∀ l, IsCombAtG t x g.tg (fun j => lin φ 1 j l) (g₂.tg l) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Conj.germ_iso_main | exact GlobalTheory.CompanionTheory.Ar.Conj.germ_iso_main | (intros; apply GlobalTheory.CompanionTheory.Ar.Conj.germ_iso_main <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.line_bundle_generator_correspondence : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0) (n : ℕ), ∃ κ : LB.Gen (LB.LinComb t.PP.L (Sum.elim (cφG t ![fst t.G t.G ^ n, snd t.G t.G]) (cφG t ![fst t.G t.G, snd t.G t.G])) (Sum.elim (cε 2) fun I => -((n : ℤ) * cε 2 I))), κ.IsGen ∧ LB.Gen.Corr t.PP.L _ _ _ _ (LB.pullGen t.PP.L _ _ κ (lift (1 : t.G ⟶ t.G) (𝟙 t.G)).left) (LB.oneGen t.PP.L) ∧ ∀ (S : Type) [CommRing S] (x : Sp S ⟶ X0) (d : ℕ) (g : GermAt t x d) (m : ℕ), ∃ u : (Jet S (Fin 2 × Fin d) m)ˣ, (u : Jet S (Fin 2 × Fin d) m) = psJet m (pow1 g.B n) ∧ LB.Gen.Corr t.PP.L _ _ _ _ (LB.pullGen t.PP.L _ _ κ (lift (jptG t x d g.x m (0 : Fin 2)) (jptG t x d g.x m (1 : Fin 2))).left) (scaleGenG t _ _ (unitΓ u) (LB.mulGen t.PP.L _ _ _ _ (peG t x d g.x g.e m ![fun j => psIn d m ![0] (g.B.A.act (n : 𝓞 E) j), fun j => MvPolynomial.X ((1 : Fin 2), j)]) (LB.invGen t.PP.L _ _ (genPowG t _ _ (g.e m) n)))) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Nfold.nfold_first_law | exact GlobalTheory.CompanionTheory.Ar.Nfold.nfold_first_law | (intros; apply GlobalTheory.CompanionTheory.Ar.Nfold.nfold_first_law <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Top.LevelZero

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.Models GlobalTheory.Models.RankZero

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}

theorem zeta_mul_pow {a c : ℕ} (ha : 0 < a) (hc : 0 < c) : zeta (a * c) ^ c = zeta a := by
  have ha' : (a : ℂ) ≠ 0 := Nat.cast_ne_zero.2 ha.ne'
  have hc' : (c : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hc.ne'
  rw [zeta, zeta, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  field_simp

theorem KA_le {l l₂ : Level H} (h : l.A ∣ l₂.A) : KA l ≤ KA l₂ := by
  refine IntermediateField.adjoin_le_iff.2 ?_
  rintro x (rfl | rfl)
  · exact IntermediateField.subset_adjoin _ _ (by simp)
  · obtain ⟨c, hc⟩ := h
    have hc0 : 0 < c := Nat.pos_of_ne_zero fun h0 => l₂.A_pos.ne' (by rw [hc, h0, mul_zero])
    rw [← zeta_mul_pow l.A_pos hc0, ← hc]
    exact pow_mem (IntermediateField.subset_adjoin _ _ (by simp)) _

def simOne (hD : D.p + D.q = 0) : Sim D :=
  have := subsingleton_La hD
  { f := fun _ => LinearMap.id
    ν := fun _ => 1
    tower := fun _ _ _ _ _ => ⟨0, Subsingleton.elim _ _⟩
    inv := fun _ _ => ⟨LinearMap.id, fun _ => ⟨⟨0, Subsingleton.elim _ _⟩, ⟨0, Subsingleton.elim _ _⟩⟩⟩
    mult := fun _ _ a b => by
      rw [Subsingleton.elim b 0]
      simp }

theorem simOne_inGam (hD : D.p + D.q = 0) (l l₂ : Level H) : (simOne hD).InGam l l₂ := by
  have := subsingleton_La hD
  refine ⟨by simp [simOne], fun a => ?_, fun a => ⟨0, Subsingleton.elim _ _⟩⟩
  rw [Subsingleton.elim ((simOne hD).f l.M a - a) 0]
  exact zero_mem _

theorem trivAt (hD : D.p + D.q = 0) (g : Sim D) (l₂ : Level H) : g.TrivAt l₂ := by
  have := subsingleton_La hD
  refine ⟨fun a => ?_, fun a => ⟨0, Subsingleton.elim _ _⟩⟩
  rw [Subsingleton.elim (g.f l₂.M a - a) 0]
  exact zero_mem _

theorem isIso_spMap_inclusion {F F' : IntermediateField ℚ ℂ} (h : F = F') :
    IsIso (spMap (IntermediateField.inclusion h.le).toRingHom) := by
  subst h
  have : (IntermediateField.inclusion (le_refl F)).toRingHom = RingHom.id F := RingHom.ext fun _ => rfl
  rw [this]
  have e : spMap (RingHom.id F) = 𝟙 _ := Spec.map_id _
  rw [e]
  infer_instance

def jKA {l l₂ : Level H} (h : l.A ∣ l₂.A) : KA l →+* KA l₂ := (IntermediateField.inclusion (KA_le h)).toRingHom

theorem coe_jKA {l l₂ : Level H} (h : l.A ∣ l₂.A) (x : KA l) : ((jKA h x : KA l₂) : ℂ) = ((x : KA l) : ℂ) :=
  IntermediateField.coe_inclusion (KA_le h) x

theorem spMap_square {l l₂ : Level H} (h : l.A ∣ l₂.A) (c : Coeff l) (c₂ : Coeff l₂) (hc : c.F = c₂.F) :
    spMap (IntermediateField.inclusion c₂.le).toRingHom ≫ spMap (jKA h) =
      spMap (IntermediateField.inclusion hc.le).toRingHom ≫ spMap (IntermediateField.inclusion c.le).toRingHom := by
  rw [RankZero.spMap_comp, RankZero.spMap_comp]
  exact congrArg spMap (RingHom.ext fun x => Subtype.ext rfl)

theorem exists_isIso_rF {l l₂ : Level H} (Xo : Moduli D l) (Xo₂ : Moduli D l₂) (hs : IsIso Xo.s) (hs₂ : IsIso Xo₂.s)
    (h : l.A ∣ l₂.A) (r : Xo₂.X ⟶ Xo.X) (hr : r ≫ Xo.s = Xo₂.s ≫ spMap (jKA h)) (c : Coeff l) (c₂ : Coeff l₂)
    (hc : c.F = c₂.F) : ∃ rF : Xo₂.XF c₂ ⟶ Xo.XF c,
      rF ≫ pullback.fst _ _ = pullback.fst _ _ ≫ r ∧
      rF ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap (IntermediateField.inclusion hc.le).toRingHom ∧ IsIso rF := by
  have hw : (pullback.fst Xo₂.s (spMap (IntermediateField.inclusion c₂.le).toRingHom) ≫ r) ≫ Xo.s =
      (pullback.snd Xo₂.s (spMap (IntermediateField.inclusion c₂.le).toRingHom) ≫
        spMap (IntermediateField.inclusion hc.le).toRingHom) ≫ spMap (IntermediateField.inclusion c.le).toRingHom := by
    rw [Category.assoc, hr, ← Category.assoc, pullback.condition, Category.assoc, spMap_square h c c₂ hc, Category.assoc]
  have h₂ := pullback.lift_snd _ _ hw
  have := isIso_spMap_inclusion hc
  exact ⟨pullback.lift _ _ hw, pullback.lift_fst _ _ hw, h₂, IsIso.of_isIso_fac_right h₂⟩

theorem lev_rank_zero (hD : D.p + D.q = 0) : ToroidalLevelCompatibility (H := H) (D := D) := by
  intro l l₂ Xo Xo₂ hd
  obtain ⟨hs, hG⟩ := isIso_moduli GlobalTheory.card_torsion_abelianVariety hD Xo
  obtain ⟨hs₂, hG₂⟩ := isIso_moduli GlobalTheory.card_torsion_abelianVariety hD Xo₂
  obtain ⟨r, hr⟩ : ∃ r : Xo₂.X ⟶ Xo.X, r ≫ Xo.s = Xo₂.s ≫ spMap (jKA hd.2.2) :=
    ⟨Xo₂.s ≫ spMap (jKA hd.2.2) ≫ inv Xo.s, by simp⟩
  obtain ⟨m⟩ := nonempty_sabMap hG₂ hG r
  obtain ⟨ν⟩ := nonempty_sabMap hG₂ hG₂ (Iso.refl Xo₂.X).hom
  have hlev : ∀ g : Sim D, Xo₂.LevAut g (Iso.refl _) := fun g =>
    ⟨Category.id_comp _, ν, fun a => sec_comm hG₂ ν.cart.1.w _ _, fun a => sec_comm hG₂ ν.cart.1.w _ _⟩
  refine ⟨r, jKA hd.2.2, m, coe_jKA _, hr, fun a => sec_comm hG m.cart.1.w _ _, fun a => sec_comm hG m.cart.1.w _ _,
    fun g _ => ⟨Iso.refl _, hlev g, Category.id_comp _⟩, fun c c₂ hc => ?_⟩
  obtain ⟨rF, h₁, h₂, hF⟩ := exists_isIso_rF Xo Xo₂ hs hs₂ hd.2.2 r hr c c₂ hc
  refine ⟨rF, h₁, h₂, inferInstance, inferInstance, inferInstance, fun k _ _ y y' h => ?_⟩
  obtain rfl : y = y' := (cancel_mono rF).1 h
  exact ⟨⟨simOne hD, Iso.refl _, simOne_inGam hD l l₂, hlev _, Category.id_comp _,
    by simp only [Iso.refl_hom, Category.comp_id]⟩, fun g _ _ _ _ => trivAt hD g l₂⟩

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), D.p + D.q = 0 → ToroidalLevelCompatibility (H := H) (D := D) ∧ ToroidalHeckeCompatibility (H := H) (D := D) :=
  fun _ _ _ _ _ _ hD => ⟨lev_rank_zero hD, GoodModel.hecke_rank_zero hD⟩

end GlobalTheory.CompanionTheory.Ar.Top.LevelZero

end
end
