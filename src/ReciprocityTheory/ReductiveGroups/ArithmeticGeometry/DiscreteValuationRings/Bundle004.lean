module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBTransport
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.AppCompatGeneric
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGenFlat
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdIso
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle004
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
import Mathlib.Tactic.TypeStar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR

open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out IsLocalRing

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]

section Scale

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

lemma const_pull' {Y Z : Scheme.{0}} (φ : Y ⟶ Z) (pY : Y ⟶ Spec (CommRingCat.of R)) (pZ : Z ⟶ Spec (CommRingCat.of R))
    (hφ : φ ≫ pZ = pY) (r : R) {U : Z.Opens} {W : Y.Opens} (h : W ≤ φ ⁻¹ᵁ U) :
    (Y.presheaf.map (homOfLE h).op).hom ((φ.app U).hom (resTop U (scal pZ r))) = resTop W (scal pY r) := by
  subst hφ
  simp only [rs, resTop, scal, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
  have key := congrArg (fun f => (CommRingCat.Hom.hom f) ((pZ.appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)))
    (φ.naturality (homOfLE (le_top : U ≤ ⊤)).op)
  simp only [CommRingCat.comp_apply] at key
  rw [key, ← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem expandsAt_scale (U : UnifPre I D A G) (e k : ℕ)
    (σ : LB.Sec (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ))))
    (f : ∀ α : D.toPre.X, D.toPre.SecB k α) (r : R) (h : U.ExpandsAt e k σ f) :
    U.ExpandsAt e k (SecOps.secScale (scal G.hom r) σ)
      (fun α => SecOps.secScale (scal D.toPre.P.A.hom r) (f α)) := by
  obtain ⟨S, hvan, hid⟩ := h
  refine ⟨S, fun α hα j => ?_, fun p j₁ jf jt h1 hcoh => ?_⟩
  · show ((U.gt e).pG.left.app _).hom (resTop _ (scal D.toPre.P.A.hom r) * (f α).f j) = 0
    rw [map_mul, hvan α hα j, mul_zero]
  · have e0 := hid p j₁ jf jt h1 hcoh
    set W := U.expW e p j₁ S jf jt
    have hG : (fstG I e G).left ≫ G.hom = ((Over.map (thick R I e)).obj (thickObj R I e G)).hom := Over.w _
    have hB : (U.gt e).pG.left ≫ D.toPre.P.A.hom = ((Over.map (thick R I e)).obj (thickObj R I e G)).hom :=
      Over.w _
    have e1 := congrArg (fun x => resTop W (scal ((Over.map (thick R I e)).obj (thickObj R I e G)).hom r) * x) e0
    simp only [Finset.mul_sum] at e1
    convert e1 using 1
    · simp only [SecOps.secScale]
      erw [map_mul, map_mul, const_pull' (fstG I e G).left _ G.hom (Over.w _) r (U := U.LG.L.wchart (fun _ => 𝟙 G.left) j₁)]
      exact mul_left_comm _ _ _
    · refine Finset.sum_congr rfl (fun α _ => ?_)
      simp only [SecOps.secScale]
      erw [map_mul, map_mul, const_pull' (U.gt e).pG.left _ D.toPre.P.A.hom (Over.w _) r (U := D.toPre.P.L.wchart (D.toPre.famφB α.1) (jf α.1))]
      exact mul_assoc _ _ _

end Scale


lemma scal_mul {Y : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of V)) (r r' : V) : scal p (r * r') = scal p r * scal p r' := by
  simp only [scal, map_mul]

lemma resTop_mul {Y : Scheme.{0}} (W : Y.Opens) (c c' : Γ(Y, ⊤)) : resTop W (c * c') = resTop W c * resTop W c' :=
  map_mul _ _ _

lemma app_resTop {Y Z : Scheme.{0}} (φ : Y ⟶ Z) (U : Z.Opens) {W : Y.Opens} (h : W ≤ φ ⁻¹ᵁ U) (c : Γ(Z, ⊤)) :
    (Y.presheaf.map (homOfLE h).op).hom ((φ.app U).hom (resTop U c)) = resTop W (φ.appTop.hom c) := by
  simp only [resTop]
  have key := congrArg (fun f => (CommRingCat.Hom.hom f) c) (φ.naturality (homOfLE (le_top : U ≤ ⊤)).op)
  simp only [CommRingCat.comp_apply] at key
  rw [key, ← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

lemma secScal_scale {X Y Y' : Scheme.{0}} {L : LB X} {K₁ K₂ : Type} [Fintype K₁] [Fintype K₂]
    {φ₁ : K₁ → (Y' ⟶ X)} {ε₁ : K₁ → ℤ} {s₁ : LB.Sec (LB.LinComb L φ₁ ε₁)}
    {φ₂ : K₂ → (Y ⟶ X)} {ε₂ : K₂ → ℤ} {s₂ : LB.Sec (LB.LinComb L φ₂ ε₂)} {h : Y' ⟶ Y} {c : Γ(Y', ⊤)}
    (hs : GeneratorPullback.SecScal L φ₁ ε₁ s₁ φ₂ ε₂ s₂ h c) (c' : Γ(Y, ⊤)) :
    GeneratorPullback.SecScal L φ₁ ε₁ s₁ φ₂ ε₂ (SecOps.secScale c' s₂) h (h.appTop.hom c' * c) := by
  intro j₁ j₂ hj
  have e := hs j₁ j₂ hj
  show _ = _ * _
  erw [map_mul, map_mul, e, app_resTop, resTop_mul]
  exact (_root_.mul_assoc _ _ _).symm

section BackK

variable {G : Over (Spec (CommRingCat.of V))}

lemma rs_resTop {Y : Scheme.{0}} {W W' : Y.Opens} (h : W' ≤ W) (c : Γ(Y, ⊤)) : rs h (resTop W c) = resTop W' c :=
  SecOps.resTop_res h c

end BackK

section Integral

variable (D : DegData V (maximalIdeal V)) {O : Type} [CommRing O] [StarRing O] [Module O D.toPre.X]

end Integral

end ReciprocityTheory.ChartRestriction.G.DVR
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR.TG

open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

def pullSec' {X Y Z : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (s : LB.Sec (LB.LinComb L φ ε)) (h : Z ⟶ Y) (φ' : K → (Z ⟶ X)) (hφ : ∀ k, φ' k = h ≫ φ k) :
    LB.Sec (LB.LinComb L φ' ε) := by
  have e : φ' = fun k => h ≫ φ k := funext hφ
  subst e
  exact pullSec L φ ε s h

lemma pullSec'_f {X Y Z : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (s : LB.Sec (LB.LinComb L φ ε)) (h : Z ⟶ Y) (φ' : K → (Z ⟶ X)) (hφ : ∀ k, φ' k = h ≫ φ k)
    (j : K → L.ι) :
    (pullSec' L φ ε s h φ' hφ).f j =
      (Z.presheaf.map (homOfLE (wchart_le_preimage L h φ φ' hφ j)).op).hom ((h.app _).hom (s.f j)) := by
  obtain rfl : φ' = fun k => h ≫ φ k := funext hφ
  rfl

lemma map_inj_of_le_ge {X : Scheme.{0}} {V W : X.Opens} (h1 : W ≤ V) (h2 : V ≤ W) {a b : Γ(X, V)}
    (h : (X.presheaf.map (homOfLE h1).op).hom a = (X.presheaf.map (homOfLE h1).op).hom b) : a = b := by
  obtain rfl : W = V := le_antisymm h1 h2
  have e : homOfLE h1 = 𝟙 W := Subsingleton.elim _ _
  rw [e] at h
  simpa using h

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

def secK (U : UnifPre I D A G) (s : H0 U.LG.L 1) : U.SecK 1 :=
  pullSec' U.LG.L _ _ s (pullback.fst G.hom (jK R)) _ (fun _ => (Category.comp_id _).symm)

lemma secK_rel (U : UnifPre I D A G) (s : H0 U.LG.L 1) :
    GeneratorPullback.SecScal U.LG.L (fun _ : Fin 1 => pullback.fst G.hom (jK R)) (fun _ => ((1 : ℕ) : ℤ)) (secK U s)
      (fun _ : Fin 1 => 𝟙 G.left) (fun _ => ((1 : ℕ) : ℤ)) s (pullback.fst G.hom (jK R)) 1 := by
  intro j₁ j₂ hc
  have hj : j₁ = j₂ := funext fun k => by
    rw [Subsingleton.elim k 0]
    exact hc (Sum.inl 0) (Sum.inr 0) (Category.comp_id _).symm
  subst hj
  rw [secK, pullSec'_f]
  have h1 : resTop (LB.wchart U.LG.L (fun _ : Fin 1 => pullback.fst G.hom (jK R)) j₁ ⊓
      LB.wchart U.LG.L (fun _ : Fin 1 => pullback.fst G.hom (jK R) ≫ 𝟙 G.left) j₁)
      (1 : Γ(pullback G.hom (jK R), ⊤)) = 1 := map_one _
  rw [h1, _root_.one_mul, ← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem sec_eq_of_secScal (U : UnifPre I D A G) [Flat G.hom] (s σ : H0 U.LG.L 1) (sK : U.SecK 1) (r : R)
    (h1 : GeneratorPullback.SecScal U.LG.L (fun _ : Fin 1 => pullback.fst G.hom (jK R)) (fun _ => ((1 : ℕ) : ℤ)) sK
      (fun _ : Fin 1 => 𝟙 G.left) (fun _ => ((1 : ℕ) : ℤ)) s (pullback.fst G.hom (jK R)) 1)
    (h2 : GeneratorPullback.SecScal U.LG.L (fun _ : Fin 1 => pullback.fst G.hom (jK R)) (fun _ => ((1 : ℕ) : ℤ)) sK
      (fun _ : Fin 1 => 𝟙 G.left) (fun _ => ((1 : ℕ) : ℤ)) σ (pullback.fst G.hom (jK R))
      (scal (pullback.snd G.hom (jK R) ≫ jK R) r)) :
    ∀ j, σ.f j = toW G.hom _ r * s.f j := by
  intro (j : Fin 1 → U.LG.L.ι)
  have hc : LB.Coh U.LG.L (Sum.elim (fun _ : Fin 1 => pullback.fst G.hom (jK R))
      (fun k : Fin 1 => pullback.fst G.hom (jK R) ≫ (fun _ : Fin 1 => 𝟙 G.left) k)) (Sum.elim j j) := by
    intro a b _
    rcases a with a | a <;> rcases b with b | b <;> exact congrArg j (Subsingleton.elim _ _)
  have e1 := h1 j j hc
  have e2 := h2 j j hc
  have h1' : resTop (LB.wchart U.LG.L (fun _ : Fin 1 => pullback.fst G.hom (jK R)) j ⊓
      LB.wchart U.LG.L (fun k : Fin 1 => pullback.fst G.hom (jK R) ≫ (fun _ : Fin 1 => 𝟙 G.left) k) j)
      (1 : Γ(pullback G.hom (jK R), ⊤)) = 1 := map_one _
  rw [h1', _root_.one_mul] at e1
  rw [← e1] at e2
  have hle : pullback.fst G.hom (jK R) ⁻¹ᵁ LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) j ≤
      LB.wchart U.LG.L (fun _ : Fin 1 => pullback.fst G.hom (jK R)) j ⊓
        LB.wchart U.LG.L (fun k : Fin 1 => pullback.fst G.hom (jK R) ≫ (fun _ : Fin 1 => 𝟙 G.left) k) j :=
    fun x hx => ⟨Set.mem_iInter.2 fun k => Set.mem_iInter.1 hx k, Set.mem_iInter.2 fun k => Set.mem_iInter.1 hx k⟩
  apply app_fst_jF_injective G.hom
  apply map_inj_of_le_ge (inf_le_right.trans (wchart_comp_le _ _ j)) hle
  refine e2.trans ?_
  have e3 : (((pullback.fst G.hom (jK R)).app (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) j)).hom
      (toW G.hom (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) j) r *
        (show Γ(G.left, LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) j) from s.f j))) =
      toW (pullback.fst G.hom (jK R) ≫ G.hom) _ r *
        ((pullback.fst G.hom (jK R)).app (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) j)).hom
          (show Γ(G.left, LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) j) from s.f j) := by
    rw [map_mul, app_toW]
  erw [e3, map_mul, toW_res, resTop_scal, toW_congr pullback.condition.symm]

end ReciprocityTheory.ChartRestriction.G.DVR.TG
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace ReciprocityTheory.ChartRestriction.G.DVR

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi

def PhiFunStatement : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I)
    (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ), 1 ≤ k →
    ∀ (p : QkPt D.toPre F k)
      (w : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p.g.b) (DegPre.lineε k))),
      w.IsGen →
      ∃ Φ : Fam D.toPre F k →ₗ[F] Fam D.toPre F k,
        ∀ s t : Fam D.toPre F k, PhiRel D.toPre F k p w s t ↔ t = Φ s

end ReciprocityTheory.ChartRestriction.G.DVR
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace ReciprocityTheory.ChartRestriction.G.DVR

open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

section Flat

variable {Y X₁ X₂ : Scheme.{0}} (L₁ : LB X₁) (L₂ : LB X₂) (f₁ : Y ⟶ X₁) (f₂ : Y ⟶ X₂)

private lemma res_res_lemma {X : Scheme.{0}} {U V W : X.Opens} (h1 : W ≤ V) (h2 : V ≤ U) (u : Γ(X, U)ˣ) :
    res h1 (res h2 u) = res (h1.trans h2) u := by
  apply Units.ext
  show (X.presheaf.map (homOfLE h1).op).hom ((X.presheaf.map (homOfLE h2).op).hom (u : Γ(X, U))) =
    (X.presheaf.map ((homOfLE h2).op ≫ (homOfLE h1).op)).hom (u : Γ(X, U))
  rw [Functor.map_comp]
  rfl

lemma flat_le {K : Type} [Fintype K] (p : (K → L₁.ι) × (K → L₂.ι)) (k : K) :
    LB.wchart L₁ (fun _ : K => f₁) p.1 ⊓ LB.wchart L₂ (fun _ : K => f₂) p.2 ≤
      (L₂.pull f₂).U (fun _ => p.2 k) ⊓ (L₁.pull f₁).U (fun _ => p.1 k) := by
  intro x hx
  simp only [LB.pull, LB.LinComb, LB.wchart, TopologicalSpace.Opens.mem_inf, TopologicalSpace.Opens.mem_mk,
    Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe] at hx ⊢
  exact ⟨fun _ => hx.2 k, fun _ => hx.1 k⟩

def flatIso (w : LB.Iso (L₁.pull f₁) (L₂.pull f₂)) {K : Type} [Fintype K] (ε : K → ℤ) :
    LB.Iso (LB.LinComb L₂ (fun _ : K => f₂) ε) (LB.LinComb L₁ (fun _ : K => f₁) ε) :=
  ⟨fun p => ∏ k, res (flat_le L₁ L₂ f₁ f₂ p k) (w.s (fun _ => p.2 k, fun _ => p.1 k)) ^ (-ε k)⟩


lemma comm_alg {M : Type*} [CommGroup M] (a b c : M) (n : ℤ) :
    (a * b⁻¹ * c) ^ (-n) = b ^ n * (a ^ n)⁻¹ * c ^ (-n) := by
  rw [mul_zpow, mul_zpow, zpow_neg a, inv_zpow', neg_neg, mul_comm ((a ^ n)⁻¹) (b ^ n)]

open ReciprocityTheory.ChartRestriction.G.Geo.Tor in
lemma gm_pull_g' {Z : Scheme.{0}} {X : Scheme.{0}} (L : LB X) (f : Y ⟶ X) (r : Z ⟶ Y) (z : Z) (a b : L.ι)
    (ha : f (r z) ∈ L.U a) (hb : f (r z) ∈ L.U b) :
    gm r z ((L.pull f).U (fun _ => a) ⊓ (L.pull f).U (fun _ => b)) ((L.pull f).g (fun _ => a) (fun _ => b)) =
      gm (r ≫ f) z (L.U a ⊓ L.U b) (L.g a b) := by
  exact (gm_linComb L (fun _ : PUnit => f) (fun _ => 1) r z (fun _ => a) (fun _ => b)
    (Set.mem_iInter.2 fun _ => ha) (Set.mem_iInter.2 fun _ => hb)).trans (by simp)

open ReciprocityTheory.ChartRestriction.G.Geo.Tor in

theorem flatIso_isGen (w : LB.Iso (L₁.pull f₁) (L₂.pull f₂)) (hw : w.IsGen) {K : Type} [Fintype K] (ε : K → ℤ) :
    (flatIso L₁ L₂ f₁ f₂ w ε).IsGen := by
  have hP := (isGen_iff w).1 hw
  intro (p : (K → L₁.ι) × (K → L₂.ι)) (q : (K → L₁.ι) × (K → L₂.ι))
  apply unit_ext
  intro y hy
  have hp : y ∈ LB.wchart L₁ (fun _ : K => f₁) p.1 ⊓ LB.wchart L₂ (fun _ : K => f₂) p.2 := hy.1
  have hq : y ∈ LB.wchart L₁ (fun _ : K => f₁) q.1 ⊓ LB.wchart L₂ (fun _ : K => f₂) q.2 := hy.2
  show gm (𝟙 Y) y _ (res _ (∏ k, res (flat_le L₁ L₂ f₁ f₂ p k) (w.s (fun _ => p.2 k, fun _ => p.1 k)) ^ (-ε k))) =
    gm (𝟙 Y) y _ ((res _ ((LB.LinComb L₁ (fun _ : K => f₁) ε).g p.1 q.1) *
      (res _ ((LB.LinComb L₂ (fun _ : K => f₂) ε).g p.2 q.2))⁻¹) *
      res _ (∏ k, res (flat_le L₁ L₂ f₁ f₂ q k) (w.s (fun _ => q.2 k, fun _ => q.1 k)) ^ (-ε k)))
  erw [map_mul, map_mul, map_inv, gm_res _ y _ hy, gm_res _ y _ hy, gm_res _ y _ hy, gm_res _ y _ hy,
    gm_linComb L₁ _ ε (𝟙 Y) y p.1 q.1 hp.1 hq.1, gm_linComb L₂ _ ε (𝟙 Y) y p.2 q.2 hp.2 hq.2]
  erw [map_prod, map_prod]
  rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  have h1 : f₁ y ∈ L₁.U (p.1 k) := Set.mem_iInter.1 hp.1 k
  have h1' : f₁ y ∈ L₁.U (q.1 k) := Set.mem_iInter.1 hq.1 k
  have h2 : f₂ y ∈ L₂.U (p.2 k) := Set.mem_iInter.1 hp.2 k
  have h2' : f₂ y ∈ L₂.U (q.2 k) := Set.mem_iInter.1 hq.2 k
  have e := hP Y (𝟙 Y) y (p.2 k) (q.2 k) (fun _ => p.1 k) (fun _ => q.1 k) (by simpa using h2) (by simpa using h2')
    (Set.mem_iInter.2 fun _ => by simpa using h1) (Set.mem_iInter.2 fun _ => by simpa using h1')
  rw [gm_pull_g' L₁ f₁ (𝟙 Y) y (p.1 k) (q.1 k) (by simpa using h1) (by simpa using h1')] at e
  rw [map_zpow, map_zpow]
  erw [gm_res _ y _ hp, gm_res _ y _ hq]
  change gw w (𝟙 Y) y (p.2 k) (fun _ => p.1 k) ^ (-ε k) = _ * _ * gw w (𝟙 Y) y (q.2 k) (fun _ => q.1 k) ^ (-ε k)
  rw [e]
  simp only [Category.id_comp]
  exact comm_alg _ _ _ _

end Flat

section NZ

variable {Y : Scheme.{0}}

lemma mem_nonzeroLocus {M : LB Y} (s : LB.Sec M) (y : Y) :
    y ∈ nonzeroLocus s ↔ ∃ j, y ∈ Y.basicOpen (s.f j) := by
  rw [nonzeroLocus, TopologicalSpace.Opens.mem_iSup]

theorem nonzeroLocus_secOfIso {A B : LB Y} (u : LB.Iso A B) (t : LB.Sec B) (hu : u.IsGen) (hA : A.IsLB)
    (hB : B.IsLB) : nonzeroLocus t ≤ nonzeroLocus (secOfIso (u := u) t hu hA hB) := by
  intro y hy
  obtain ⟨b, hb⟩ := (mem_nonzeroLocus t y).1 hy
  have hyb : y ∈ B.U b := Y.basicOpen_le _ hb
  obtain ⟨a, ha⟩ : ∃ a, y ∈ A.U a := by
    have : y ∈ (⨆ a, A.U a : Y.Opens) := by rw [hA.cover]; trivial
    simpa [TopologicalSpace.Opens.mem_iSup] using this
  refine (mem_nonzeroLocus _ y).2 ⟨a, ?_⟩
  have e := secOfIso_spec (u := u) t hu hA hB a b
  have e2 := congrArg Y.basicOpen e
  rw [isoCand, Scheme.basicOpen_mul, Scheme.basicOpen_of_isUnit _ (Units.isUnit _), Scheme.basicOpen_res,
    Scheme.basicOpen_res] at e2
  have hmem : y ∈ (A.U a ⊓ B.U b) ⊓ ((A.U a ⊓ B.U b) ⊓ Y.basicOpen (t.f b)) := ⟨⟨ha, hyb⟩, ⟨ha, hyb⟩, hb⟩
  rw [← e2] at hmem
  exact hmem.2

end NZ

section Main

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]

end Main

end ReciprocityTheory.ChartRestriction.G.DVR
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi

def TwistBCSpanStatement : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (D : DegPre R) (k : ℕ), 1 ≤ k → ∀ (α : D.X)
    (R' : Type) [CommRing R'] [IsLocalRing R'] (f : R →+* R'), IsLocalHom f →
    ∀ s' : LB.Sec (LB.LinComb D.P.L
        (fun i => (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A).left ≫ DegPre.famφB D α i)
        (DegPre.famε k)),
      ∃ (n : ℕ) (r : Fin n → Γ(Spec (CommRingCat.of R'), ⊤)) (s : Fin n → D.SecB k α),
        ∀ j, s'.f j = ∑ i,
          ((Over.mk (Spec.map (CommRingCat.ofHom f)) ⊗ D.P.A).left.presheaf.map (homOfLE le_top).op).hom
            ((fst (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A).left.appTop.hom (r i)) *
          ((Over.mk (Spec.map (CommRingCat.ofHom f)) ⊗ D.P.A).left.presheaf.map
            (homOfLE (_root_.ReciprocityTheory.ChartRestriction.G.Out.wchart_comp_le D.P.L (DegPre.famφB D α)
              (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A).left j)).op).hom
            (((snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A).left.app _).hom ((s i).f j))

end ReciprocityTheory.ChartRestriction.G.DVR
end
end
