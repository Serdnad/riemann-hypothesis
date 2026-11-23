module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle004
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle029
public import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
public import Formalism.LocalToGlobal.Divisibility.NumbersLemmas
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ColHeightSharpWith
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle002
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GalStarComplexMultiplicationPoints
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CmCurveGoodOutsidePrimePremises
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
import Development.AbelianVarietyTheory.Definitions.Divisors.MemSubPtsCutBaseChangeIff
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory.ChowHt GlobalTheory.Adelic
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

namespace GlobalTheory.HSChoice

def join {R : Type} {D N : ℕ} (u : Fin D → Fin N → R) (ξ : Fin N → R) : Fin (D + 1) × Fin N → R :=
  fun p => Fin.lastCases (motive := fun _ => R) (ξ p.2) (fun i => u i p.2) p.1

def spec {F E : Type} [CommRing F] [CommRing E] [Algebra F E] {D N : ℕ} (s : Fin D → Fin N → E)
    (f : MvPolynomial (Fin (D + 1) × Fin N) F) : MvPolynomial (Fin 1 × Fin N) E :=
  aeval (join (fun i j => C (s i j)) fun j => X (0, j)) f

def lin {K : Type} [CommRing K] {N : ℕ} (y : Fin N → K) : MvPolynomial (Fin 1 × Fin N) K := ∑ j, X ((0 : Fin 1), j) * C (y j)

def finPart {K ι : Type} [Field K] [NumberField K] (g : MvPolynomial ι K) : ℝ :=
  (∑ᶠ v : FinitePlace K, Real.log (gaussAbs v g)) / (Module.finrank ℚ K : ℝ)

def mean (K : Type) [Field K] [NumberField K] (a : (K →+* ℂ) → ℝ) : ℝ := (∑ τ, a τ) / (Module.finrank ℚ K : ℝ)

structure ShortLat {F : Type} [Field F] [NumberField F] {N n : ℕ} (w : Matrix (Fin N) (Fin n) F)
    (A : (F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ) (Λ : ℝ) : Prop where
  pos : 0 < N
  spans : Submodule.span F (Set.range w.col) = ⊤
  int : ∀ u ∈ Submodule.span (𝓞 F) (Set.range w.col), u ∈ Submodule.span ℤ (Set.range w.col)
  det : ∀ σ, (A σ).det ≠ 0
  conj : ConjCompat A
  le : ∀ k σ, frameNorm (A σ) (fun j => σ (w j k)) ≤ Λ
  one_le : 1 ≤ Λ

def NoSquare {K : Type} [Field K] {N : ℕ} (g : MvPolynomial (Fin 1 × Fin N) K) : Prop :=
  g ≠ 0 ∧ ∀ y : Fin N → K, y ≠ 0 → ¬ lin y ^ 2 ∣ g

theorem join_last {R : Type} {D N : ℕ} (u : Fin D → Fin N → R) (ξ : Fin N → R) (j : Fin N) : join u ξ (Fin.last D, j) = ξ j := by
  simp [join]

theorem join_castSucc {R : Type} {D N : ℕ} (u : Fin D → Fin N → R) (ξ : Fin N → R) (i : Fin D) (j : Fin N) :
    join u ξ (i.castSucc, j) = u i j := by
  simp [join]

namespace Check

theorem lin_ne {K : Type} [Field K] {N : ℕ} {y : Fin N → K} (hy : y ≠ 0) : lin y ≠ 0 := by
  intro h
  apply hy
  funext j
  have := congrArg (eval (fun p : Fin 1 × Fin N => if p.2 = j then (1:K) else 0)) h
  simpa [lin] using this

end Check

end GlobalTheory.HSChoice
end
end

section

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualCon.Model

variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

theorem fam_ev {U T : Over S} {M : LB (A ⊗ U).left} (h : Fam A M) (u : T ⟶ U) :
    Fam A (ev M (fst A T) (snd A T ≫ u)) := by
  have hM : (ev M (fst A T) (snd A T ≫ u)).IsLB := pull_isLB h.isLB _
  refine ⟨hM, (isAdditive_iff hM).2 fun Y a a' t ↦ ?_⟩
  simp only [evc_ev h.isLB, lift_fst, lift_snd_assoc]
  exact (isAdditive_iff h.isLB).1 h.add Y a a' _

theorem rep_ext {B S' Y : Over S} {b : B ⟶ S'} {P : LB (A ⊗ B).left} (h : Rep A b P) {u u' : Y ⟶ B}
    (hb : u ≫ b = u' ≫ b) (e : Same A P P u u') : u = u' := by
  have hu := fam_ev h.fam u
  exact (h.univ Y (u ≫ b) _ hu).unique ⟨rfl, (cls_eq_iff hu.isLB hu.isLB).1 rfl⟩ ⟨hb.symm, e⟩




end GlobalTheory.DualCon.Model
end
end

section

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.DualCon

variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

theorem Fam.ev {T Y : Over S} {N : LB (A ⊗ T).left} (h : Fam A N) (y : Y ⟶ T) :
    Fam A (ev N (fst A Y) (snd A Y ≫ y)) := by
  have hN' : (GlobalTheory.AbDual.ev N (fst A Y) (snd A Y ≫ y)).IsLB := pull_isLB h.isLB _
  refine ⟨hN', (isAdditive_iff hN').2 fun Z a a' t => ?_⟩
  simp only [evc_ev h.isLB (fst A Y) (snd A Y ≫ y) hN', lift_fst, lift_snd_assoc]
  exact (isAdditive_iff h.isLB).1 h.add Z a a' (t ≫ y)


end GlobalTheory.DualCon
end
end

section

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualOpen

variable {S : Scheme.{0}}

def ptMap {C C' : Type} [CommRing C] [CommRing C'] (s : Sp C ⟶ S) (φ : C →+* C') :
    Over.mk (spMap φ ≫ s) ⟶ Over.mk s := Over.homMk (spMap φ)

@[simp] theorem ptMap_left {C C' : Type} [CommRing C] [CommRing C'] (s : Sp C ⟶ S) (φ : C →+* C') :
    (ptMap s φ).left = spMap φ := rfl

abbrev dnInl (k : Type) [CommRing k] : k →+* DualNumber k := algebraMap k (DualNumber k)

abbrev dnFst (k : Type) [CommRing k] : DualNumber k →+* k := (TrivSqZeroExt.fstHom k k k).toRingHom

structure Milnor {T T₁ T₂ T₀ : Scheme.{0}} (j₁ : T₁ ⟶ T) (j₂ : T₂ ⟶ T) (k₁ : T₀ ⟶ T₁) (k₂ : T₀ ⟶ T₂) : Prop where
  aff : IsAffine T
  aff₁ : IsAffine T₁
  aff₂ : IsAffine T₂
  closed : IsClosedImmersion k₂
  w : k₁ ≫ j₁ = k₂ ≫ j₂
  cart : IsPullback j₁.appTop j₂.appTop k₁.appTop k₂.appTop

variable (A : Over S) [GrpObj A] {U : Over S} (M : LB (A ⊗ U).left)

def FieldChart : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (s : Sp K ⟶ S) (T : Over S) (_ : T ⟶ Over.mk s) (N : LB (A ⊗ T).left),
    Fam A N → ChartAt A M N

def TanLift : Prop :=
  ∀ (k : Type) [Field k] (s : Sp k ⟶ S) (N : LB (A ⊗ Over.mk (spMap (dnInl k) ≫ s)).left), Fam A N →
    ∀ u₀ : Over.mk (spMap (dnFst k) ≫ spMap (dnInl k) ≫ s) ⟶ U, Same A N M (ptMap _ (dnFst k)) u₀ →
      ∃ u : Over.mk (spMap (dnInl k) ≫ s) ⟶ U, Same A N M (𝟙 _) u

def SmallLift : Prop :=
  ∀ (C : Type) [CommRing C] [IsLocalRing C] (e : C), e ∈ IsLocalRing.maximalIdeal C →
    (∀ a ∈ IsLocalRing.maximalIdeal C, a * e = 0) → ∀ (s : Sp C ⟶ S) (N : LB (A ⊗ Over.mk s).left), Fam A N →
    ∀ u₀ : Over.mk (spMap (Ideal.Quotient.mk (Ideal.span {e})) ≫ s) ⟶ U,
      Same A N M (ptMap s (Ideal.Quotient.mk (Ideal.span {e}))) u₀ → ∃ u : Over.mk s ⟶ U, Same A N M (𝟙 _) u

variable {A M}

theorem Milnor.of_isPullback {R R₁ R₂ R₀ : CommRingCat.{0}} {a : R ⟶ R₁} {b : R ⟶ R₂} {c : R₁ ⟶ R₀} {d : R₂ ⟶ R₀}
    (h : IsPullback a b c d) (hd : Function.Surjective d) :
    Milnor (Spec.map a) (Spec.map b) (Spec.map c) (Spec.map d) := by
  refine ⟨inferInstance, inferInstance, inferInstance, IsClosedImmersion.spec_of_surjective d hd, ?_, ?_⟩
  · rw [← Spec.map_comp, ← Spec.map_comp, h.w]
  · exact h.of_iso (Scheme.ΓSpecIso R).symm (Scheme.ΓSpecIso R₁).symm (Scheme.ΓSpecIso R₂).symm
      (Scheme.ΓSpecIso R₀).symm (Scheme.ΓSpecIso_inv_naturality a) (Scheme.ΓSpecIso_inv_naturality b)
      (Scheme.ΓSpecIso_inv_naturality c) (Scheme.ΓSpecIso_inv_naturality d)


end GlobalTheory.DualOpen
end
end

section

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PicGlue

variable {X Y : Scheme.{0}}

structure IsOn (W : X.Opens) (L : LB X) : Prop where
  le : ∀ a, L.U a ≤ W
  cov : ∀ x ∈ W, ∃ a, x ∈ L.U a
  coc : ∀ (x : X) (a b c : L.ι), x ∈ L.U a → x ∈ L.U b → x ∈ L.U c →
    gm (𝟙 X) x _ (L.g a b) * gm (𝟙 X) x _ (L.g b c) = gm (𝟙 X) x _ (L.g a c)

abbrev Cmp (W : X.Opens) (L M : LB X) : Type := ∀ (a : L.ι) (b : M.ι), Γ(X, W ⊓ (L.U a ⊓ M.U b))ˣ

def IsoOn (W : X.Opens) (L M : LB X) (w : Cmp W L M) : Prop :=
  ∀ x ∈ W, ∀ (a a' : L.ι) (b b' : M.ι), x ∈ L.U a → x ∈ L.U a' → x ∈ M.U b → x ∈ M.U b' →
    gm (𝟙 X) x _ (w a b) * gm (𝟙 X) x _ (M.g b b') = gm (𝟙 X) x _ (L.g a a') * gm (𝟙 X) x _ (w a' b')

abbrev RigD (e : Y ⟶ X) (L : LB X) : Type := ∀ a : L.ι, Γ(Y, e ⁻¹ᵁ L.U a)ˣ

def RigOn (e : Y ⟶ X) (L : LB X) (r : RigD e L) : Prop :=
  ∀ (y : Y) (a b : L.ι), e y ∈ L.U a → e y ∈ L.U b →
    gm (𝟙 Y) y _ (r a) = gm e y _ (L.g a b) * gm (𝟙 Y) y _ (r b)

def Norm (e : Y ⟶ X) (W : X.Opens) (L M : LB X) (w : Cmp W L M) (r : RigD e L) (r' : RigD e M) : Prop :=
  ∀ (y : Y) (a : L.ι) (b : M.ι), e y ∈ W → e y ∈ L.U a → e y ∈ M.U b →
    gm e y _ (w a b) * gm (𝟙 Y) y _ (r' b) = gm (𝟙 Y) y _ (r a)

def FnBij (p : X ⟶ Y) : Prop := ∀ V : Y.Opens, Function.Bijective (p.app V).hom

variable {S : Scheme.{0}} (A : Over S) [GrpObj A]

def AddCls {T : Over S} (c : Pic (A ⊗ T).left) : Prop :=
  ∀ (Z : Over S) (a a' : Z ⟶ A) (t : Z ⟶ T),
    CechPic.pull (lift (a * a') t).left c = CechPic.pull (lift a t).left c + CechPic.pull (lift a' t).left c

theorem AddCls.pull {T T' : Over S} {c : Pic (A ⊗ T).left} (h : AddCls A c) (u : T' ⟶ T) :
    AddCls A (CechPic.pull (A ◁ u).left c) := fun Z a a' t ↦ by
  simpa only [← pull_comp, ← Over.comp_left, lift_whiskerLeft] using h Z a a' (t ≫ u)

def addF : (Over S)ᵒᵖ ⥤ Type 1 where
  obj T := {c : Pic (A ⊗ T.unop).left // AddCls A c}
  map u := TypeCat.ofHom fun c ↦ ⟨CechPic.pull (A ◁ u.unop).left c.1, c.2.pull A u.unop⟩
  map_id T := by
    ext c
    change CechPic.pull (A ◁ 𝟙 T.unop).left c.1 = c.1
    rw [MonoidalCategory.whiskerLeft_id, Over.id_left, pull_id]
  map_comp u v := by
    ext c
    change CechPic.pull (A ◁ (v.unop ≫ u.unop)).left c.1 =
      CechPic.pull (A ◁ v.unop).left (CechPic.pull (A ◁ u.unop).left c.1)
    rw [MonoidalCategory.whiskerLeft_comp, Over.comp_left, pull_comp]

theorem addF_map_val {T T' : Over S} (u : T' ⟶ T) (c : (addF A).obj (Opposite.op T)) :
    ((addF A).map u.op c).1 = CechPic.pull (A ◁ u).left c.1 := rfl

variable {A}

def famCls {T : Over S} {N : LB (A ⊗ T).left} (h : Fam A N) : (addF A).obj (Opposite.op T) :=
  ⟨cls N h.isLB, (isAdditive_iff h.isLB).1 h.add⟩

theorem famCls_surj {T : Over S} (c : (addF A).obj (Opposite.op T)) :
    ∃ (N : LB (A ⊗ T).left) (h : Fam A N), famCls h = c := by
  obtain ⟨c, hc⟩ := c
  obtain ⟨N, hN, rfl⟩ := cls_surj c
  exact ⟨N, ⟨hN, (isAdditive_iff hN).2 hc⟩, rfl⟩


omit [GrpObj A] in
theorem whiskerLeft_eq_lift {T T' : Over S} (u : T' ⟶ T) : A ◁ u = lift (fst A T') (snd A T' ≫ u) := by
  ext <;> simp

theorem same_iff_map {T U Z : Over S} {N : LB (A ⊗ T).left} {M : LB (A ⊗ U).left} (hN : Fam A N) (hM : Fam A M)
    (y : Z ⟶ T) (u : Z ⟶ U) : Same A N M y u ↔ (addF A).map y.op (famCls hN) = (addF A).map u.op (famCls hM) := by
  refine (same_iff hN.isLB hM.isLB y u).trans (Iff.trans ?_ Subtype.ext_iff.symm)
  rw [addF_map_val, addF_map_val, whiskerLeft_eq_lift, whiskerLeft_eq_lift]
  rfl

end GlobalTheory.PicGlue
end
end

section

noncomputable section

namespace GlobalTheory.ColRows

open NumberField IsDedekindDomain
open _root_.Formalism.BasicNotions _root_.Formalism.MainNotions _root_.Formalism.L2.DIV
  _root_.Formalism.L2.Col _root_.Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {K : G.Consts} {Y : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl K Y cX}

structure KerTies (t : KerEntTied ex) (W : Wts t.X t.Pr.Word D.R) (Del h0 : ℕ) : Prop where
  host : HostTie (ofRecord D L Del h0) t.seam t.Pr
  wts : ∃ pl : RPl D.R ≃ t.X.Tau, ∀ u, WeightTie (ofRecord D L Del h0) W pl (t.word u) (letterOf D L Del h0 u)
  chr : CharTie (ofRecord D L Del h0) t.seam W t.Ch t.glob t.sel
  an : AnalyticTie D t.δ t.χ t.cD
  mu0 : t.tup D.what₂.mu0 = 1
  sharp : (t.cst D.what₂.mu0).sharp = true
  m2 : t.m2 = D.R.m - 2
  fld : ∀ u, FieldOfDefinition W t.sel (t.tup D.what₂.mu0) (t.cst D.what₂.mu0) (t.word u) t.amb

structure KerSizes (t : KerEntTied ex) (W : Wts t.X t.Pr.Word D.R) (Del h0 : ℕ) (CY CT : ℝ) : Prop where
  sizes : Sizes t.Pr W L.sc.a
  what₂ : ∀ u, GlobalTheory.Core.Ht2.SizeRowsS CY (ofRecord D L Del h0) (letterOf D L Del h0 u)
  logT : ∀ u, Real.log (((D.mem u).A.T : ℕ) : ℝ) ≤ CT * D.R.m * L.sc.L

end GlobalTheory.ColRows

end
end

section

noncomputable section

open WeierstrassCurve
open scoped IntermediateField

namespace GlobalTheory.CMModel

def Stable (L : PeriodPair) (F : IntermediateField ℚ ℂ) {ι : Type} (T : ι → ℂ) : Prop :=
  ∀ σ : ℂ ≃+* ℂ, (∀ x ∈ F, σ x = x) → ∃ e : ι ≃ ι, ∀ i, GlobalTheory.ConjPoint.IsConj L L σ (T i) (T (e i))

def IntV (V : ValuationSubring ℂ) (W : WeierstrassCurve ℂ) : Prop :=
  W.a₁ ∈ V ∧ W.a₂ ∈ V ∧ W.a₃ ∈ V ∧ W.a₄ ∈ V ∧ W.a₆ ∈ V

def ModelAt (V : ValuationSubring ℂ) (F : IntermediateField ℚ ℂ) (W : WeierstrassCurve ℂ) (D : ℂ) : Prop :=
  ∃ C : VariableChange ℂ, (C.u : ℂ) ∈ F ∧ C.r ∈ F ∧ C.s ∈ F ∧ C.t ∈ F ∧ IntV V (C • W) ∧
    V.valuation (C • W).Δ = V.valuation D

abbrev Sq (p : ℕ) : Type := {k : Fin p // ((k : ℕ) : ZMod p) ≠ 0 ∧ IsSquare ((k : ℕ) : ZMod p)}


open Classical in
instance (p : ℕ) : Fintype (Sq p) := Subtype.fintype _

def sqPt (p : ℕ) (t : ℂ) (k : Sq p) : ℂ := ((k.1 : ℕ) : ℂ) * t

def sqProd (p : ℕ) (L : PeriodPair) (t : ℂ) : ℂ := ∏ k : Sq p, L.derivWeierstrassP (sqPt p t k)

def shortTwist {R : Type} [CommRing R] (d a₄ a₆ : R) : WeierstrassCurve R := ⟨0, 0, 0, d ^ 2 * a₄, d ^ 3 * a₆⟩

structure Datum (p : ℕ) (F : IntermediateField ℚ ℂ) (L : PeriodPair) (t : ℂ) : Prop where

  mul : Formalism.L2.Th1.F.MulStable L (GlobalTheory.Published.sqrtNegNat p)

  g₂_mem : L.g₂ ∈ F

  g₃_mem : L.g₃ ∈ F

  notMem : t ∉ L.lattice

  ker : GlobalTheory.Published.sqrtNegNat p * t ∈ L.lattice

end GlobalTheory.CMModel
end
end
