module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle983
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle885
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle937
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle884
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle015
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle025
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle984
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
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechPer.Nat

theorem isPer_pull : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), ∀ (A' : Over (Sp ℂ)) [GrpObj A'] (g' : ℕ) (L' : LB A'.left) (u' : HolUnif A' L' g') (φ : A' ⟶ A) (M : (Fin g' → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (h : φ.left ≫ str A = str A' ≫ spMap (RingHom.id ℂ)), (∀ w, u.ex (M w) = u'.ex w ≫ φ) → ∀ (hM : ∀ l : u'.Λ, M l ∈ u.Λ) x x' q, IsPull1 h x x' → IsPer u.ex u.Λ x q → IsPer u'.ex u'.Λ x' fun l => q ⟨M l, hM l⟩ := by
  intro A _ g L u A' _ g' L' u' φ M h hex hM x x' q hp hx
  obtain ⟨c, h₀, rfl, ⟨hd, hc, hw⟩, hq⟩ := hx
  obtain ⟨c', rfl⟩ := Hyp1.mk_surjective _ x'
  have hp' : Hyp1.mk _ (pullZZ1 (pairPull h) c) = Hyp1.mk _ (pullZZ1 (pairRes φ.left (str A')) c') := hp
  obtain ⟨b, hb⟩ := Hyp1.mk_eq_mk.1 hp'
  obtain ⟨a1, a2, a3, a4, a5, a6, -, a8, a9, a10, -, a12⟩ := GlobalTheory.T.uniformisation_preimage_value_rules A g L u
  obtain ⟨b1, b2, b3, b4, b5, b6, -, b8, b9, b10, -, b12⟩ := GlobalTheory.T.uniformisation_preimage_value_rules A' g' L' u'
  let Mc : (Fin g' → ℂ) →L[ℂ] (Fin g → ℂ) := LinearMap.toContinuousLinearMap M
  have hP := GlobalTheory.T.uniformisedOneFormEvaluation_linear_pullback A g L u A' g' L' u' φ Mc h hex
  have hpre : ∀ (U : A.left.Opens) z, z ∈ pre u'.ex (φ.left ⁻¹ᵁ U) ↔ M z ∈ pre u.ex U := by
    intro U z
    change ⊤ ≤ (u'.ex z).left ⁻¹ᵁ (φ.left ⁻¹ᵁ U) ↔ ⊤ ≤ (u.ex (M z)).left ⁻¹ᵁ U
    rw [hex]
    rfl
  have hf : ∀ (p l : Pair φ.left) (e : l ≤ p) (a : Opposite.op p.1.1 ⟶ Opposite.op l.1.1)
      (a' : Opposite.op p.1.2 ⟶ Opposite.op l.1.2),
      (show Sec (str A') l.1.1.1 from b (Opposite.op l)) - Sec.res (str A') (Pair.le_fst e) (b (Opposite.op p)) =
        GlobalTheory.CechDR.secPull (str A) (str A') l (c.1.1 _ _ a') - (show Sec (str A') l.1.1.1 from c'.1.1 _ _ a) := by
    intro p l e a a'
    exact congrArg (fun t : Tot1 (OPair φ.left (str A')) => t.1 (Opposite.op p) (Opposite.op l) (homOfLE e).op) hb
  have hω : ∀ (p : Pair φ.left), KaehlerDifferential.D ℂ (Sec (str A') p.1.1.1) (b (Opposite.op p)) =
      (semiHom_secPull h p).m1 (c.1.2 (Opposite.op p.1.2)) -
        (show Ω[Sec (str A') p.1.1.1⁄ℂ] from c'.1.2 (Opposite.op p.1.1)) := by
    intro p
    have e1 := congrArg (fun t : Tot1 (OPair φ.left (str A')) => t.2 (Opposite.op p)) hb
    have e2 : q1 (pairRes φ.left (str A')) (Opposite.op p) (c'.1.2 (Opposite.op p.1.1)) = c'.1.2 (Opposite.op p.1.1) :=
      SemiHom.oneFormMap_eq_self_of_id _ (fun _ => rfl) _
    exact e1.trans (congrArg (fun t => (semiHom_secPull h p).m1 (c.1.2 (Opposite.op p.1.2)) - t) e2)
  have hstep : ∀ (p l : Pair φ.left) (e : l ≤ p), ∀ z ∈ pre u'.ex l.1.1.1, ∀ (a : Opposite.op p.1.1 ⟶ Opposite.op l.1.1),
      h₀ l.1.2 (M z) - val u'.ex l.1.1.1 (b (Opposite.op l)) z =
        h₀ p.1.2 (M z) - val u'.ex p.1.1.1 (b (Opposite.op p)) z + val u'.ex l.1.1.1 (c'.1.1 _ _ a) z := by
    intro p l e z hz a
    obtain ⟨hz', hv, -⟩ := hP l z hz
    let a' : Opposite.op p.1.2 ⟶ Opposite.op l.1.2 := (homOfLE (Pair.le_snd e)).op
    have hs : ∀ x y v w : Sec (str A') l.1.1.1, x - y = v - w →
        val u'.ex l.1.1.1 x z - val u'.ex l.1.1.1 y z = val u'.ex l.1.1.1 v z - val u'.ex l.1.1.1 w z := by
      intro x y v w e
      obtain ⟨ev, hev⟩ := b10 _ z hz
      rw [hev x, hev y, hev v, hev w, ← map_sub, ← map_sub, e]
    have e1 : val u'.ex l.1.1.1 (b (Opposite.op l)) z -
        val u'.ex l.1.1.1 (Sec.res (str A') (Pair.le_fst e) (b (Opposite.op p))) z =
        val u'.ex l.1.1.1 (GlobalTheory.CechDR.secPull (str A) (str A') l (c.1.1 _ _ a')) z - val u'.ex l.1.1.1 (c'.1.1 _ _ a) z :=
      hs _ _ _ _ (hf p l e a a')
    have e3 : val u'.ex l.1.1.1 (Sec.res (str A') (Pair.le_fst e) (b (Opposite.op p))) z =
        val u'.ex p.1.1.1 (b (Opposite.op p)) z := b9 _ _ _ _ z hz
    have e4 : val u'.ex l.1.1.1 (GlobalTheory.CechDR.secPull (str A) (str A') l (c.1.1 _ _ a')) z =
        val u.ex l.1.2.1 (c.1.1 _ _ a') (M z) := hv _
    have e2 := hc p.1.2 l.1.2 a' (M z) hz'
    linear_combination e2 - e1 - e3 - e4
  refine GlobalTheory.T.hasCechDeRhamPeriods_of_affine_basis A' g' L' u' c' (Pair φ.left) (fun p => p.1.1)
    (fun p z => h₀ p.1.2 (M z) - val u'.ex p.1.1.1 (b (Opposite.op p)) z) _ ?_ ?_ ?_ ?_ ?_
  · intro p r z hzp hzr
    have h1 : M z ∈ pre u.ex (p.1.2.1 ⊓ r.1.2.1) := by
      rw [a5]; exact ⟨(hP p z hzp).1, (hP r z hzr).1⟩
    obtain ⟨U, hU, hzU⟩ := a8 _ _ h1
    have h2 : z ∈ pre u'.ex (p.1.1.1 ⊓ r.1.1.1 ⊓ φ.left ⁻¹ᵁ U.1) := by
      rw [b5, b5]; exact ⟨⟨hzp, hzr⟩, (hpre _ _).2 hzU⟩
    obtain ⟨W, hW, hzW⟩ := b8 _ _ h2
    let l : Pair φ.left := ⟨(W, U), hW.trans inf_le_right⟩
    have lp : l ≤ p := Subtype.coe_le_coe.1 (Prod.le_def.2
      ⟨show W.1 ≤ p.1.1.1 from hW.trans (inf_le_left.trans inf_le_left), show U.1 ≤ p.1.2.1 from hU.trans inf_le_left⟩)
    have lr : l ≤ r := Subtype.coe_le_coe.1 (Prod.le_def.2
      ⟨show W.1 ≤ r.1.1.1 from hW.trans (inf_le_left.trans inf_le_right), show U.1 ≤ r.1.2.1 from hU.trans inf_le_right⟩)
    exact ⟨l, Pair.le_fst lp, Pair.le_fst lr, hzW, hstep p l lp z hzW, hstep r l lr z hzW⟩
  · intro U' z hz
    obtain ⟨U, -, hzU⟩ := a8 _ _ (a12 (M z))
    have h2 : z ∈ pre u'.ex (U'.1 ⊓ φ.left ⁻¹ᵁ U.1) := by
      rw [b5]; exact ⟨hz, (hpre _ _).2 hzU⟩
    obtain ⟨W, hW, hzW⟩ := b8 _ _ h2
    exact ⟨⟨(W, U), hW.trans inf_le_right⟩, show W.1 ≤ U'.1 from hW.trans inf_le_left, hzW⟩
  · intro p
    exact ((hd p.1.2).comp Mc.differentiable.differentiableOn fun z hz => (hP p z hz).1).sub (b2 _ _)
  · intro p z hz
    obtain ⟨hz', -, hE⟩ := hP p z hz
    have d1 : DifferentiableAt ℂ (h₀ p.1.2) (Mc z) := (hd p.1.2).differentiableAt ((a1 _).mem_nhds hz')
    have d2 : DifferentiableAt ℂ (val u'.ex p.1.1.1 (b (Opposite.op p))) z :=
      (b2 _ _).differentiableAt ((b1 _).mem_nhds hz)
    have d3 : HasFDerivAt (fun z => h₀ p.1.2 (M z) - val u'.ex p.1.1.1 (b (Opposite.op p)) z)
        ((fderiv ℂ (h₀ p.1.2) (Mc z)).comp Mc - fderiv ℂ (val u'.ex p.1.1.1 (b (Opposite.op p))) z) z :=
      (d1.hasFDerivAt.comp z Mc.hasFDerivAt).sub d2.hasFDerivAt
    have e1 := congrArg (evForm u'.ex p.1.1.1 z) (hω p)
    rw [map_sub, hE] at e1
    have e2 := ((GlobalTheory.T.uniformisedOneFormEvaluation_rules A' g' L' u' _ z hz).2.2 (b (Opposite.op p))).symm.trans e1
    rw [d3.fderiv, hw p.1.2 _ hz']
    exact (congrArg (fun t => _ - t) e2).trans (sub_sub_cancel _ _)
  · intro p l z hz
    have e1 := hq p.1.2 ⟨M l, hM l⟩ (M z) (hP p z hz).1
    change h₀ p.1.2 (M (z + l)) - _ = _
    have e2 : val u'.ex p.1.1.1 (b (Opposite.op p)) (z + l) = val u'.ex p.1.1.1 (b (Opposite.op p)) z := b4 _ _ l z
    rw [map_add (f := _), e2]
    change h₀ p.1.2 (M z + M l) = _ at e1
    rw [e1]
    ring

end GlobalTheory.CechPer.Nat
end
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LBFrameEx

variable {X : Scheme.{0}}

private theorem res_res' {U V W : X.Opens} (h : V ≤ U) (h' : W ≤ V) (x : Γ(X, U)ˣ) :
    res h' (res h x) = res (h'.trans h) x := by
  ext
  simp only [res, Units.coe_map, MonoidHom.coe_coe]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

private theorem coc {L : LB X} (hL : L.IsLB) (i j k : L.ι) {W : X.Opens} (h₁ : W ≤ L.U i ⊓ L.U j)
    (h₂ : W ≤ L.U j ⊓ L.U k) (h₃ : W ≤ L.U i ⊓ L.U k) :
    res h₁ (L.g i j) * res h₂ (L.g j k) = res h₃ (L.g i k) := by
  have hW : W ≤ L.U i ⊓ L.U j ⊓ L.U k := le_inf h₁ (h₂.trans inf_le_right)
  have := congrArg (res hW) (hL.cocycle i j k)
  rwa [map_mul, res_res', res_res', res_res'] at this

structure Ch (L : LB X) where
  U : X.affineOpens
  m : L.ι
  le : (U : X.Opens) ≤ L.U m

instance (L : LB X) : Preorder (Ch L) where
  le a b := (b.U : X.Opens) ≤ a.U
  le_refl _ := le_rfl
  le_trans _ _ _ h h' := h'.trans h

abbrev opF (L : LB X) : Ch L ⥤ AffOp X where
  obj T := Opposite.op T.U
  map a := (homOfLE (leOfHom a)).op

def unit (L : LB X) (T T' : Ch L) (a : T ⟶ T') : Γ(X, opOf (opF L) T')ˣ :=
  res (le_inf T'.le ((show (T'.U : X.Opens) ≤ T.U from leOfHom a).trans T.le) : (T'.U : X.Opens) ≤ L.U T'.m ⊓ L.U T.m) (L.g T'.m T.m)

def gen (L : LB X) (T : Ch L) (m : L.ι) : Γ(X, opOf (opF L) T ⊓ L.U m)ˣ :=
  res (le_inf inf_le_right (inf_le_left.trans T.le) : (T.U : X.Opens) ⊓ L.U m ≤ L.U m ⊓ L.U T.m) (L.g m T.m)

theorem isBas (L : LB X) (hL : L.IsLB) : IsBas (opOf (opF L)) := by
  have hch : ∀ x : X, ∃ m, x ∈ L.U m := fun x => by
    have hx : x ∈ (⊤ : X.Opens) := trivial
    rw [← hL.cover] at hx
    exact TopologicalSpace.Opens.mem_iSup.1 hx
  have hb : ∀ {U : X.Opens} {x : X}, x ∈ U → ∃ U' ∈ X.affineOpens, x ∈ U' ∧ U' ≤ U :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens
  refine ⟨fun x U hx => ?_, fun t₁ t₂ x U hx h₁ h₂ => ?_⟩
  · obtain ⟨m, hm⟩ := hch x
    obtain ⟨V, hV, hxV, hVU⟩ := hb (show x ∈ U ⊓ L.U m from ⟨hx, hm⟩)
    exact ⟨⟨⟨V, hV⟩, m, hVU.trans inf_le_right⟩, hxV, hVU.trans inf_le_left⟩
  · obtain ⟨V, hV, hxV, hVU⟩ := hb (show x ∈ U ⊓ (opOf (opF L) t₁ ⊓ opOf (opF L) t₂) from ⟨hx, h₁, h₂⟩)
    refine ⟨⟨⟨V, hV⟩, t₁.m, (hVU.trans inf_le_right).trans (inf_le_left.trans t₁.le)⟩,
      ⟨homOfLE ?_⟩, ⟨homOfLE ?_⟩, hxV, hVU.trans inf_le_left⟩
    · exact (hVU.trans inf_le_right).trans inf_le_left
    · exact (hVU.trans inf_le_right).trans inf_le_right

theorem isFrame (L : LB X) (hL : L.IsLB) : IsFrame L (opOf (opF L)) (opOf_le (opF L)) (unit L) := by
  refine ⟨gen L, fun T m m' => ?_, fun T T' a m => ?_⟩
  · simp only [gen]
    rw [res_res', res_res']
    exact (coc hL m m' T.m _ _ _).symm
  · simp only [gen, unit]
    rw [res_res', res_res']
    rw [mul_comm]
    exact (coc hL m T'.m T.m _ _ _).symm

theorem exists_frame : ∀ (X : Scheme.{0}) (L : LB X), L.IsLB → ∃ (C : Type) (_ : Category.{0} C) (_ : Quiver.IsThin C)
    (G : C ⥤ AffOp X) (u : ∀ (T T' : C) (_ : T ⟶ T'), Γ(X, opOf G T')ˣ),
    IsBas (opOf G) ∧ IsFrame L (opOf G) (opOf_le G) u :=
  fun X L hL => ⟨Ch L, inferInstance, fun _ _ => inferInstance, opF L, unit L, isBas L hL, isFrame L hL⟩

end GlobalTheory.LBFrameEx
end
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.LBObs

theorem res_res_frameRestrict {X : Scheme.{0}} {U V W : X.Opens} (h : V ≤ U) (h' : W ≤ V) (x : Γ(X, U)ˣ) :
    res h' (res h x) = res (h'.trans h) x := by
  ext
  simp only [res, Units.coe_map, MonoidHom.coe_coe]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem isFrame_restrict : ∀ (X : Scheme.{0}) (C : Type) [Category.{0} C] (V : C → X.Opens) (hV : ∀ ⦃T T' : C⦄, (T ⟶ T') → V T' ≤ V T) (L : LB X) (u : ∀ (T T' : C) (_ : T ⟶ T'), Γ(X, V T')ˣ) (C' : Type) [Category.{0} C'] (V' : C' → X.Opens) (hV' : ∀ ⦃T T' : C'⦄, (T ⟶ T') → V' T' ≤ V' T) (H : C' ⥤ C) (hH : ∀ T, V' T ≤ V (H.obj T)), IsFrame L V hV u → IsFrame L V' hV' fun T T' a ↦ res (hH T') (u _ _ (H.map a)) := by
  intro X C _ V hV L u C' _ V' hV' H hH ⟨τ, hgen, hcomp⟩
  refine ⟨fun T m ↦ res (inf_le_inf_right (L.U m) (hH T)) (τ (H.obj T) m), fun T m m' ↦ ?_, fun T T' a m ↦ ?_⟩
  · have key := congrArg (res (inf_le_inf_right (L.U m') (inf_le_inf_right (L.U m) (hH T)))) (hgen (H.obj T) m m')
    simp only [map_mul, res_res_frameRestrict] at key
    simpa only [map_mul, res_res_frameRestrict] using key
  · have key := congrArg (res (inf_le_inf_right (L.U m) (hH T'))) (hcomp (H.obj T) (H.obj T') (H.map a) m)
    simp only [map_mul, res_res_frameRestrict] at key
    simpa only [map_mul, res_res_frameRestrict] using key

end GlobalTheory.LBObs
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LBObs.FrameCoc

theorem res_res' {X : Scheme.{0}} {U V W : X.Opens} (h : W ≤ V) (h' : V ≤ U) (x : Γ(X, U)ˣ) :
    res h (res h' x) = res (h.trans h') x := by
  ext
  simp only [res, Units.coe_map, MonoidHom.coe_coe]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem isCoc_of_isFrame : ∀ (X : Scheme.{0}) (C : Type) [Category.{0} C] (V : C → X.Opens) (hV : ∀ ⦃T T' : C⦄, (T ⟶ T') → V T' ≤ V T) (L : LB X) (u : ∀ (T T' : C) (_ : T ⟶ T'), Γ(X, V T')ˣ), L.IsLB → IsFrame L V hV u → IsCoc V hV u := by
  intro X C _ V hV L u hL hF T T' T'' a b
  obtain ⟨τ, -, hτ⟩ := hF
  have key : ∀ m : L.ι, res (inf_le_left : V T'' ⊓ L.U m ≤ V T'') (u T T'' (a ≫ b)) =
      res (inf_le_left : V T'' ⊓ L.U m ≤ V T'') (res (hV b) (u T T' a) * u T' T'' b) := by
    intro m
    have h1 := hτ T T'' (a ≫ b) m
    have h2 := congrArg (res (inf_le_inf_right (L.U m) (hV b))) (hτ T T' a m)
    have h3 := hτ T' T'' b m
    rw [res_res', map_mul, res_res', h3] at h2
    rw [h1] at h2
    apply mul_right_cancel (b := τ T'' m)
    rw [h2, map_mul, res_res', ← _root_.mul_assoc]
  apply Units.ext
  refine X.sheaf.eq_of_locally_eq' (fun m => V T'' ⊓ L.U m) (V T'') (fun m => homOfLE inf_le_left) ?_ _ _ ?_
  · rw [← inf_iSup_eq, hL.cover, inf_top_eq]
  · intro m
    exact congrArg Units.val (key m)

end GlobalTheory.LBObs.FrameCoc
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LBObs

structure CommonRef {X : Scheme.{0}} {C C' : Type} [Category.{0} C] [Category.{0} C']
    (G : C ⥤ AffOp X) (G' : C' ⥤ AffOp X) : Type where

  t : C

  t' : C'

  W : X.affineOpens
  le : W.1 ≤ opOf G t
  le' : W.1 ≤ opOf G' t'

namespace CommonRef

variable {X : Scheme.{0}} {C C' : Type} [Category.{0} C] [Category.{0} C'] [Quiver.IsThin C] [Quiver.IsThin C']
  {G : C ⥤ AffOp X} {G' : C' ⥤ AffOp X}

instance : Category.{0} (CommonRef G G') where
  Hom a b := (a.t ⟶ b.t) × (a.t' ⟶ b.t') × PLift (b.W.1 ≤ a.W.1)
  id a := (𝟙 _, 𝟙 _, ⟨le_rfl⟩)
  comp f g := (f.1 ≫ g.1, f.2.1 ≫ g.2.1, ⟨g.2.2.down.trans f.2.2.down⟩)
  id_comp f := by ext <;> simp
  comp_id f := by ext <;> simp
  assoc f g h := by ext <;> simp

instance : Quiver.IsThin (CommonRef G G') := fun a b =>
  ⟨fun f g => Prod.ext (Subsingleton.elim _ _) (Prod.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _))⟩

variable (G G')

def fst : CommonRef G G' ⥤ C where
  obj d := d.t
  map f := f.1

def snd : CommonRef G G' ⥤ C' where
  obj d := d.t'
  map f := f.2.1

def opn : CommonRef G G' ⥤ AffOp X where
  obj d := Opposite.op d.W
  map f := (homOfLE f.2.2.down).op

def toFst : fst G G' ⋙ G ⟶ opn G G' where
  app d := (homOfLE (show d.W ≤ (G.obj d.t).unop from d.le)).op
  naturality _ _ _ := Quiver.Hom.unop_inj (Subsingleton.elim _ _)

def toSnd : snd G G' ⋙ G' ⟶ opn G G' where
  app d := (homOfLE (show d.W ≤ (G'.obj d.t').unop from d.le')).op
  naturality _ _ _ := Quiver.Hom.unop_inj (Subsingleton.elim _ _)

theorem isBas (hG : IsBas (opOf G)) (hG' : IsBas (opOf G')) : IsBas (opOf (opn G G')) := by
  refine ⟨fun x U hx => ?_, fun d₁ d₂ x U hx h₁ h₂ => ?_⟩
  · obtain ⟨t, hxt, htU⟩ := hG.1 x U hx
    obtain ⟨t', hxt', ht'⟩ := hG'.1 x (opOf G t ⊓ U) ⟨hxt, hx⟩
    exact ⟨⟨t, t', (G'.obj t').unop, ht'.trans inf_le_left, le_rfl⟩, hxt', ht'.trans inf_le_right⟩
  · have hx₃ : x ∈ U ⊓ d₁.W.1 ⊓ d₂.W.1 := ⟨⟨hx, h₁⟩, h₂⟩
    obtain ⟨t, a₁, a₂, hxt, htU⟩ := hG.2 d₁.t d₂.t x _ hx₃ (d₁.le h₁) (d₂.le h₂)
    obtain ⟨t', b₁, b₂, hxt', ht'⟩ := hG'.2 d₁.t' d₂.t' x (opOf G t) hxt (d₁.le' h₁) (d₂.le' h₂)
    refine ⟨⟨t, t', (G'.obj t').unop, ht', le_rfl⟩, ⟨(a₁.some, b₁.some, ⟨?_⟩)⟩, ⟨(a₂.some, b₂.some, ⟨?_⟩)⟩, hxt', ?_⟩
    · exact ht'.trans (htU.trans (inf_le_left.trans inf_le_right))
    · exact ht'.trans (htU.trans inf_le_right)
    · exact ht'.trans (htU.trans (inf_le_left.trans inf_le_left))

end CommonRef

theorem common_refinement : ∀ (X : Scheme.{0}) (C C' : Type) [Category.{0} C] [Category.{0} C'] [Quiver.IsThin C] [Quiver.IsThin C'] (G : C ⥤ AffOp X) (G' : C' ⥤ AffOp X), IsBas (opOf G) → IsBas (opOf G') → ∃ (D : Type) (_ : Category.{0} D) (_ : Quiver.IsThin D) (K : D ⥤ AffOp X) (H : D ⥤ C) (H' : D ⥤ C'), Nonempty (H ⋙ G ⟶ K) ∧ Nonempty (H' ⋙ G' ⟶ K) ∧ IsBas (opOf K) :=
  fun X C C' _ _ _ _ G G' hG hG' =>
    ⟨CommonRef G G', inferInstance, inferInstance, CommonRef.opn G G', CommonRef.fst G G', CommonRef.snd G G',
      ⟨CommonRef.toFst G G'⟩, ⟨CommonRef.toSnd G G'⟩, CommonRef.isBas G G' hG hG'⟩

end GlobalTheory.LBObs
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LBObs

variable {X Z : Scheme.{0}} (φ : Z ⟶ X) {C C' : Type} [Category.{0} C] [Category.{0} C']
  (G : C ⥤ AffOp X) (G' : C' ⥤ AffOp Z)

def RefineTriple : Type :=
  {q : Pair φ × C × C' // q.1.1.2.1 ≤ opOf G q.2.1 ∧ q.1.1.1.1 ≤ opOf G' q.2.2}

instance RefineTriple.instPreorder : Preorder (RefineTriple φ G G') where
  le d e := e.1.1 ≤ d.1.1 ∧ Nonempty (d.1.2.1 ⟶ e.1.2.1) ∧ Nonempty (d.1.2.2 ⟶ e.1.2.2)
  le_refl d := ⟨le_rfl, ⟨𝟙 _⟩, ⟨𝟙 _⟩⟩
  le_trans a b c h₁ h₂ := ⟨h₂.1.trans h₁.1, ⟨h₁.2.1.some ≫ h₂.2.1.some⟩, ⟨h₁.2.2.some ≫ h₂.2.2.some⟩⟩

def RefineTriple.pair : RefineTriple φ G G' ⥤ (Pair φ)ᵒᵖ where
  obj d := Opposite.op d.1.1
  map f := (homOfLE (leOfHom f).1).op

def RefineTriple.idx [Quiver.IsThin C] : RefineTriple φ G G' ⥤ C where
  obj d := d.1.2.1
  map f := (leOfHom f).2.1.some
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

def RefineTriple.idx' [Quiver.IsThin C'] : RefineTriple φ G G' ⥤ C' where
  obj d := d.1.2.2
  map f := (leOfHom f).2.2.some
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

end GlobalTheory.LBObs

namespace GlobalTheory.LBObs

theorem exists_pair_refine : ∀ (X Z : Scheme.{0}) (φ : Z ⟶ X) (C C' : Type) [Category.{0} C] [Category.{0} C'] [Quiver.IsThin C] [Quiver.IsThin C'] (G : C ⥤ AffOp X) (G' : C' ⥤ AffOp Z), IsBas (opOf G) → IsBas (opOf G') → ∃ (D : Type) (_ : Category.{0} D) (_ : Quiver.IsThin D) (K : D ⥤ (Pair φ)ᵒᵖ) (H : D ⥤ C) (H' : D ⥤ C'), Nonempty (H ⋙ G ⟶ K ⋙ pairSnd φ) ∧ Nonempty (H' ⋙ G' ⟶ K ⋙ pairFst φ) ∧ IsBas (opOf (K ⋙ pairFst φ)) := by
  intro X Z φ C C' _ _ _ _ G G' hG hG'
  refine ⟨RefineTriple φ G G', inferInstance, inferInstance, RefineTriple.pair φ G G',
    RefineTriple.idx φ G G', RefineTriple.idx' φ G G', ⟨{ app := fun d ↦ (homOfLE d.2.1).op }⟩,
    ⟨{ app := fun d ↦ (homOfLE d.2.2).op }⟩, ?_, ?_⟩
  · intro z U hz
    obtain ⟨t, ht, -⟩ := hG.1 (φ z) ⊤ trivial
    obtain ⟨t', ht', hle⟩ := hG'.1 z (U ⊓ φ ⁻¹ᵁ opOf G t) ⟨hz, ht⟩
    refine ⟨⟨(⟨((G'.obj t').unop, (G.obj t).unop), fun y hy ↦ (hle hy).2⟩, t, t'), le_rfl, le_rfl⟩,
      ht', fun y hy ↦ (hle hy).1⟩
  · intro d₁ d₂ z U hz h₁ h₂
    have k₁ : φ z ∈ d₁.1.1.1.2.1 := d₁.1.1.2 h₁
    have k₂ : φ z ∈ d₂.1.1.1.2.1 := d₂.1.1.2 h₂
    obtain ⟨t, a₁, a₂, ht, hle⟩ := hG.2 d₁.1.2.1 d₂.1.2.1 (φ z) (d₁.1.1.1.2.1 ⊓ d₂.1.1.1.2.1)
      ⟨k₁, k₂⟩ (d₁.2.1 k₁) (d₂.2.1 k₂)
    obtain ⟨t', b₁, b₂, ht', hle'⟩ := hG'.2 d₁.1.2.2 d₂.1.2.2 z
      (U ⊓ d₁.1.1.1.1.1 ⊓ d₂.1.1.1.1.1 ⊓ φ ⁻¹ᵁ opOf G t) ⟨⟨⟨hz, h₁⟩, h₂⟩, ht⟩ (d₁.2.2 h₁) (d₂.2.2 h₂)
    let d : RefineTriple φ G G' :=
      ⟨(⟨((G'.obj t').unop, (G.obj t).unop), fun y hy ↦ (hle' hy).2⟩, t, t'), le_rfl, le_rfl⟩
    refine ⟨d, ⟨homOfLE ⟨?_, a₁, b₁⟩⟩, ⟨homOfLE ⟨?_, a₂, b₂⟩⟩, ht', fun y hy ↦ (hle' hy).1.1.1⟩
    · exact Prod.le_def.2 ⟨fun y hy ↦ (hle' hy).1.1.2, fun y hy ↦ (hle hy).1⟩
    · exact Prod.le_def.2 ⟨fun y hy ↦ (hle' hy).1.2, fun y hy ↦ (hle hy).2⟩

end GlobalTheory.LBObs
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.pChern_neg_one : GlobalTheory.AnPer.PChern (-1) := by
  first | exact @GlobalTheory.AnPer.ChernClause.pchern | exact GlobalTheory.AnPer.ChernClause.pchern | (intros; apply GlobalTheory.AnPer.ChernClause.pchern <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.periodHom_push_end' : PEnd := by
  first | exact @GlobalTheory.AnPer.periodHom_push_end | exact GlobalTheory.AnPer.periodHom_push_end | (intros; apply GlobalTheory.AnPer.periodHom_push_end <;> assumption)
end
