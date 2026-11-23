module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import Mathlib.Analysis.CStarAlgebra.Classes
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegProd
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.Bundle001
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi

def PullCubCompSt : Prop :=
  ∀ (S S' S'' : Scheme.{0}) (G : Over S) (G' : Over S') (G'' : Over S'') [GrpObj G] [IsCommMonObj G] [GrpObj G']
    [IsCommMonObj G'] [GrpObj G''] [IsCommMonObj G''] (m : CubeMap G' G) (m' : CubeMap G'' G') (n : CubeMap G'' G)
    (L : RigLB G) (L' : RigLB G') (L'' : RigLB G'') (c : CubicalStr G L) (c' : CubicalStr G' L')
    (c'' : CubicalStr G'' L''), n.F = m'.F ≫ m.F → n.F3 = m'.F3 ≫ m.F3 → n.e = m'.e ≫ m.e →
    m.IsPullCubical c' c → m'.IsPullCubical c'' c' → n.IsPullCubical c'' c

def PullCubCancelSt : Prop :=
  ∀ (S S' S'' : Scheme.{0}) (G : Over S) (G' : Over S') (G'' : Over S'') [GrpObj G] [IsCommMonObj G] [GrpObj G']
    [IsCommMonObj G'] [GrpObj G''] [IsCommMonObj G''] (m : CubeMap G' G) (m' : CubeMap G'' G') (n : CubeMap G'' G)
    (L : RigLB G) (L' : RigLB G') (L'' : RigLB G'') (c : CubicalStr G L) (c' : CubicalStr G' L')
    (c'' : CubicalStr G'' L''), n.F = m'.F ≫ m.F → n.F3 = m'.F3 ≫ m.F3 → n.e = m'.e ≫ m.e →
    m.IsPullCubical c' c → n.IsPullCubical c'' c → m'.IsPullCubical c'' c'

def SABCompSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S S' S'' : Scheme.{0}) (t : SAB H S)
    (t' : SAB H S') (t'' : SAB H S'') (f : S' ⟶ S) (g : S'' ⟶ S') (m : SABMap t' t f) (m' : SABMap t'' t' g),
    ∃ n : SABMap t'' t (g ≫ f), n.φ = m'.φ ≫ m.φ

def SABCancelSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S S' S'' : Scheme.{0}) (t : SAB H S)
    (t' : SAB H S') (t'' : SAB H S'') (f : S' ⟶ S) (g : S'' ⟶ S') (m : SABMap t' t f) (n : SABMap t'' t (g ≫ f)),
    ∃ m' : SABMap t'' t' g, n.φ = m'.φ ≫ m.φ

def AbLocusOneSt : Prop :=
  ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], IsSemiAbelian G → ∀ (K : Type) [Field K] (t : Sp K ⟶ S),
    IsProper (pullback.snd G.hom t) → Set.range t ⊆ abLocus G

def ProjProperSt : Prop :=
  ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Sp R), IsProjOver f → IsProper f

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
end
end

section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def zeta (n : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / n)

def KA (l : Level H) : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ {H.rt0, zeta l.A}

def baseKA (l : Level H) : Base l (KA l) where
  unit n hn := IsUnit.mk0 _ (Nat.cast_ne_zero.mpr hn.ne')
  ρ := ⟨H.rt0, IntermediateField.subset_adjoin _ _ (by simp)⟩
  ρ_sq := Subtype.ext (by simpa using H.sqrt_neg_disc_sq)
  ζ := ⟨zeta l.A, IntermediateField.subset_adjoin _ _ (by simp)⟩
  ζ_prim := IsPrimitiveRoot.of_map_of_injective (f := (KA l).val.toRingHom)
    (Complex.isPrimitiveRoot_exp l.A l.A_pos.ne') Subtype.val_injective

def Datum.dim (D : Datum H) : ℕ := Module.finrank ℚ E / 2 * D.p * D.q

def constPt {k : Type} [Field k] {X : Scheme.{0}} (x : Sp (DualNumber k) ⟶ X) : Sp (DualNumber k) ⟶ X :=
  spMap (algebraMap k (DualNumber k)) ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ x

structure Moduli (D : Datum H) (l : Level H) where
  X : Scheme.{0}
  s : X ⟶ Sp (KA l)
  qproj : IsQProjOver s
  smooth : SmoothOfRelativeDimension D.dim s
  univ : Obj D l (baseKA l) s
  rep : ∀ (S : Scheme.{0}) (s' : S ⟶ Sp (KA l)), IsReduced S → ∀ o : Obj D l (baseKA l) s',
    ∃! f : S ⟶ X, f ≫ s = s' ∧ Nonempty (ObjMap o univ f)
  unram : ∀ (k : Type) [Field k] (x : Sp (DualNumber k) ⟶ X) (o : Obj D l (baseKA l) (x ≫ s)),
    Nonempty (ObjMap o univ x) → Nonempty (ObjMap o univ (constPt x)) → x = constPt x

structure Coeff (l : Level H) where
  F : IntermediateField ℚ ℂ
  fin : FiniteDimensional ℚ F
  conj : ∀ (τ : E →+* ℂ) (a : E), τ a ∈ F
  zeta_mem : zeta l.M' ∈ F
  le : KA l ≤ F

variable {D : Datum H} {l : Level H}

abbrev Moduli.XF (Xo : Moduli D l) (c : Coeff l) : Scheme.{0} :=
  pullback Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)

structure Model (Xo : Moduli D l) (c : Coeff l) {O : Type} [CommRing O] (β : O →+* c.F) where
  X : Scheme.{0}
  s : X ⟶ Sp O
  normal : IsNormalScheme X
  proj : IsProjOver s
  flat : Flat s
  jQ : Xo.XF c ⟶ pullback s (spMap β)
  jQ_over : jQ ≫ pullback.snd _ _ = pullback.snd _ _
  jQ_open : IsOpenImmersion jQ
  jQ_dense : Dense (Set.range jQ)
  t : SAB H X
  oF : Obj D l (baseKA l) (pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) ≫ Xo.s)
  m0 : ObjMap oF Xo.univ (pullback.fst _ _)
  m : SABMap oF.t t (jQ ≫ pullback.fst _ _)
  ab_gen : pullback.fst s (spMap β) ⁻¹' abLocus t.G = Set.range jQ

namespace Model

variable {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β)

def j : Xo.XF c ⟶ Y.X := Y.jQ ≫ pullback.fst _ _

def Descends : Prop :=
  ∃ (XK : Scheme.{0}) (sK : XK ⟶ Sp (KA l)) (GK : Over XK) (_ : GrpObj GK) (jK : Xo.X ⟶ XK)
    (φK : Xo.univ.t.G.left ⟶ GK.left) (e : pullback Y.s (spMap β) ⟶ XK)
    (GQ : Over (pullback Y.s (spMap β))) (_ : GrpObj GQ) (φ₁ : GQ.left ⟶ Y.t.G.left) (φ₂ : GQ.left ⟶ GK.left)
    (ψ : Y.oF.t.G.left ⟶ GQ.left),
    IsOpenImmersion jK ∧ jK ≫ sK = Xo.s ∧ IsGrpPullback Xo.univ.t.G GK jK φK ∧
    IsPullback e (pullback.snd _ _) sK (spMap (IntermediateField.inclusion c.le).toRingHom) ∧
    Y.jQ ≫ e = pullback.fst _ _ ≫ jK ∧
    IsGrpPullback GQ Y.t.G (pullback.fst _ _) φ₁ ∧ IsGrpPullback GQ GK e φ₂ ∧
    ψ ≫ φ₁ = Y.m.φ ∧ ψ ≫ GQ.hom = Y.oF.t.G.hom ≫ Y.jQ ∧ ψ ≫ φ₂ = Y.m0.toSABMap.φ ≫ φK

def LevelActs : Prop :=
  ∀ (r : Xo.XF c ≅ Xo.XF c) (ν : SABMap Y.oF.t Y.oF.t r.hom) (gM gA : D.La →ₗ[𝓞 E] D.La),
    r.hom ≫ pullback.snd _ _ = pullback.snd _ _ →
    (∀ a, (Y.oF.eta (gM a)).left ≫ ν.φ = r.hom ≫ (Y.oF.eta a).left) →
    (∀ a, (Y.oF.etaA (gA a)).left ≫ ν.φ = r.hom ≫ (Y.oF.etaA a).left) →
    ∃ (ρ : Y.X ≅ Y.X) (mu : SABMap Y.t Y.t ρ.hom),
      ρ.hom ≫ Y.s = Y.s ∧ Y.j ≫ ρ.hom = r.hom ≫ Y.j ∧ Y.m.φ ≫ mu.φ = ν.φ ≫ Y.m.φ

def Extends (U : Y.X.Opens) (σ : 𝟙_ (Over (Xo.XF c)) ⟶ Y.oF.t.G) : Prop :=
  ∃ σ' : U.toScheme ⟶ Y.t.G.left, σ' ≫ Y.t.G.hom = U.ι ∧
    ∀ j' : Xo.XF c ⟶ U.toScheme, j' ≫ U.ι = Y.j → j' ≫ σ' = σ.left ≫ Y.m.φ

end Model

def PushInvertible {X : Scheme.{0}} (G : Over X) (L : LB G.left) : Prop :=
  ∀ x : X, ∃ V : X.Opens, x ∈ V ∧ ∃ θ ∈ secOn L (G.hom ⁻¹ᵁ V),
    (∀ (W : X.Opens) (hW : W ≤ V), ∀ s ∈ secOn L (G.hom ⁻¹ᵁ W), ∃! a : Γ(X, W), ∀ i,
      s i = (G.hom.appLE W (G.hom ⁻¹ᵁ W ⊓ L.U i) inf_le_left).hom a *
        resG G.left (inf_le_inf_right _ (G.hom.preimage_mono hW)) (θ i)) ∧
    ∀ y ∈ V, ∃ (g : G.left) (i : L.ι), G.hom g = y ∧ g ∈ G.left.basicOpen (θ i)

def IsTransition {l₂ : Level H} {Xo : Moduli D l} {Xo₂ : Moduli D l₂} {c : Coeff l} {c₂ : Coeff l₂}
    {O O₂ : Type} [CommRing O] [CommRing O₂] {β : O →+* c.F} {β₂ : O₂ →+* c₂.F}
    (Y : Model Xo c β) (Y₂ : Model Xo₂ c₂ β₂) (b : O →+* O₂) (π : Y₂.X ⟶ Y.X) : Prop :=
  ∃ (π' : Y₂.X ⟶ pullback Y.s (spMap b)) (mu : SABMap Y₂.t Y.t π) (r : Xo₂.XF c₂ ⟶ Xo.XF c),
    π' ≫ pullback.fst _ _ = π ∧ π' ≫ pullback.snd _ _ = Y₂.s ∧ IsFinite π' ∧ Y₂.j ≫ π = r ≫ Y.j ∧
    (∀ a, (Y₂.oF.eta a ^ (l₂.M / l.M)).left ≫ Y₂.m.φ ≫ mu.φ = r ≫ (Y.oF.eta a).left ≫ Y.m.φ) ∧
    (∀ a, (Y₂.oF.etaA a ^ (l₂.A / l.A)).left ≫ Y₂.m.φ ≫ mu.φ = r ≫ (Y.oF.etaA a).left ≫ Y.m.φ)

def Dominates {Xo : Moduli D l} {c : Coeff l} {O O' : Type} [CommRing O] [CommRing O'] {β : O →+* c.F}
    {β' : O' →+* c.F} (Y : Model Xo c β) (Y' : Model Xo c β') (b : O →+* O') : Prop :=
  ∃ (f : pullback Y.s (spMap b) ⟶ Y'.X) (t : SAB H (pullback Y.s (spMap b)))
    (m₁ : SABMap t Y.t (pullback.fst _ _)) (m₂ : SABMap t Y'.t f),
    f ≫ Y'.s = pullback.snd _ _ ∧
    (∀ a : Xo.XF c ⟶ pullback Y.s (spMap b), a ≫ pullback.fst _ _ = Y.j → a ≫ f = Y'.j) ∧
    ∀ (T : Scheme.{0}) (g : T ⟶ t.G.left) (g₁ : T ⟶ Y.oF.t.G.left) (g₂ : T ⟶ Y'.oF.t.G.left),
      g ≫ m₁.φ = g₁ ≫ Y.m.φ → g₁ ≫ Y.m0.toSABMap.φ = g₂ ≫ Y'.m0.toSABMap.φ → g₁ ≫ Y.oF.t.G.hom = g₂ ≫ Y'.oF.t.G.hom →
      g ≫ m₂.φ = g₂ ≫ Y'.m.φ

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open ReciprocityTheory.ChartRestriction.G.Out NumberField

def GlobalFnsDvrSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V], IsAdicComplete (IsLocalRing.maximalIdeal V) V →
    ∀ t : SAB H (Sp V),
      IsProper ((Over.pullback (spMap (algebraMap V (FractionRing V)))).obj t.G).hom →
      ∀ n : ℕ, Function.Bijective (powObj t.G n).hom.appTop.hom

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

namespace ReciprocityTheory.ChartRestriction.G.Chart

attribute [local instance] Over.cartesianMonoidalCategory

variable {R : Type} [CommRing R] {G : Over (Spec (CommRingCat.of R))} [GrpObj G]

theorem isTan_comp {w : sp (R₀ := R) (DualNumber R) ⟶ G} (hw : IsTan w) (f : G ⟶ G) [IsMonHom f] : IsTan (w ≫ f) := by
  unfold IsTan at hw ⊢
  rw [← Category.assoc, hw]
  first
  | simp only [Hom.one_def, Category.assoc, IsMonHom.one_hom]
  | simp [Hom.one_def]

variable {n : ℕ} {x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin n) m) ⟶ G} (hx : IsUnivChart G n x)

def tvec (c : Fin n → R) : sp (R₀ := R) (DualNumber R) ⟶ G := spMap (dualLift c) ≫ x 1

include hx in
theorem isTan_tvec (c : Fin n → R) : IsTan (tvec (x := x) c) := isTan_dualLift hx c

private lemma sp_tangent_ext {w w' : sp (R₀ := R) (DualNumber R) ⟶ G} (hw : IsTan w) (hw' : IsTan w')
    (h : tcoord hx w hw = tcoord hx w' hw') : w = w' := by
  calc w = spMap (dualLift (tcoord hx w hw)) ≫ x 1 := tcoord_spec hx w hw
    _ = spMap (dualLift (tcoord hx w' hw')) ≫ x 1 := by rw [h]
    _ = w' := (tcoord_spec hx w' hw').symm

theorem tcoord_tvec (c : Fin n → R) : tcoord hx (tvec (x := x) c) (isTan_tvec hx c) = c :=
  (exists_coord hx (tvec (x := x) c) (isTan_tvec hx c)).unique (tcoord_spec hx _ _) rfl

include hx in
theorem tvec_add (c c' : Fin n → R) : tvec (x := x) (c + c') = tvec (x := x) c * tvec (x := x) c' := by
  refine sp_tangent_ext hx (isTan_tvec hx (c + c')) (isTan_mul (isTan_tvec hx c) (isTan_tvec hx c')) ?_
  rw [tcoord_mul hx (isTan_tvec hx c) (isTan_tvec hx c'), tcoord_tvec, tcoord_tvec, tcoord_tvec]

include hx in
theorem tvec_smul (a : R) (c : Fin n → R) : tvec (x := x) (a • c) = spMap (scaleD a) ≫ tvec (x := x) c := by
  refine sp_tangent_ext hx (isTan_tvec hx (a • c)) (isTan_scale a (isTan_tvec hx c)) ?_
  rw [tcoord_scale hx a (isTan_tvec hx c), tcoord_tvec, tcoord_tvec]

theorem tcoord_congr {w w' : sp (R₀ := R) (DualNumber R) ⟶ G} (h : w = w') (hw : IsTan w) (hw' : IsTan w') :
    tcoord hx w hw = tcoord hx w' hw' := by
  subst h
  rfl

def tmap (f : G ⟶ G) [IsMonHom f] : (Fin n → R) →ₗ[R] (Fin n → R) where
  toFun c := tcoord hx (tvec (x := x) c ≫ f) (isTan_comp (isTan_tvec hx c) f)
  map_add' c c' := by
    have e : tvec (x := x) (c + c') ≫ f = (tvec (x := x) c ≫ f) * (tvec (x := x) c' ≫ f) := by
      rw [tvec_add hx, Hom.mul_def, Hom.mul_def, Category.assoc, IsMonHom.mul_hom, ← Category.assoc, lift_map]
    show tcoord hx _ _ = tcoord hx _ _ + tcoord hx _ _
    rw [tcoord_congr hx e _ (isTan_mul (isTan_comp (isTan_tvec hx c) f) (isTan_comp (isTan_tvec hx c') f)),
      tcoord_mul hx]
  map_smul' a c := by
    have e : tvec (x := x) (a • c) ≫ f = spMap (scaleD a) ≫ (tvec (x := x) c ≫ f) := by
      rw [tvec_smul hx, Category.assoc]
    show tcoord hx _ _ = a • tcoord hx _ _
    rw [tcoord_congr hx e _ (isTan_scale a (isTan_comp (isTan_tvec hx c) f)), tcoord_scale hx]

theorem tvec_tmap (f : G ⟶ G) [IsMonHom f] (c : Fin n → R) : tvec (x := x) (tmap hx f c) = tvec (x := x) c ≫ f :=
  (tcoord_spec hx (tvec (x := x) c ≫ f) (isTan_comp (isTan_tvec hx c) f)).symm

end ReciprocityTheory.ChartRestriction.G.Chart
end
end
