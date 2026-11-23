module

public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ContinuousOnThetaFrameValueHolomorphicFamily
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle046
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle031
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle059
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle029
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle041
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle063
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle040
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle025
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
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle003
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLinearEquivLift

@[expose] public section

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

theorem _root_.GlobalTheory.T.exists_isThetaPt' : Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r) (k : Fin F.n) (T : ThetaData e F M k), ∀ b ∈ T.co ⁻¹' (M.X k).dom, ∀ κ : ℂ, κ ≠ 0 → ∃ y : FrPt Xo c (CAt σ), IsThetaPt T b κ y := by
  first | exact @GlobalTheory.FrameUnif.ThetaPtEx.exists_thetaPt | exact GlobalTheory.FrameUnif.ThetaPtEx.exists_thetaPt | (intros; apply GlobalTheory.FrameUnif.ThetaPtEx.exists_thetaPt <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.conjugation_acts_on_cm_torsion_by_multiplication : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (C : Curve H), ∀ τ : ℂ ≃+* ℂ, τ H.rt0 = H.rt0 → ∀ io : C.P.A.left ⟶ C.P.A.left, IsGrpPullback C.P.A C.P.A (spMap (τ : ℂ →+* ℂ)) io → ∀ n : ℕ, 0 < n → (∃ s, C.ActsBy τ io n s) ∧ ∀ s, C.ActsBy τ io n s → (∃ s' a, wC H s' * wC H s = 1 + n * wC H a) ∧ ∀ m : ℕ, m ∣ n → C.ActsBy τ io m s := by
  first | exact @GlobalTheory.CompRat.Acts.main | exact GlobalTheory.CompRat.Acts.main | (intros; apply GlobalTheory.CompRat.Acts.main <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.exists_splitPureTypePeriod_of_signatureSplit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)), IsTypeFn H D.p D.q ty → SplitLat D → ∃ (P : D.La →+ (Fin g → ℂ)) (hP : IsPeriod D ty P), IsSplit hP := by
  first | exact @GlobalTheory.CompRat.exists_isSplit_of_splitLat | exact GlobalTheory.CompRat.exists_isSplit_of_splitLat | (intros; apply GlobalTheory.CompRat.exists_isSplit_of_splitLat <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.HolGen

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l}

theorem chart_iff {R : Type} [CommRing R] (x : Sp R ⟶ Xo.X) (q : Sp ℂ ⟶ Gx x) (j : Xo.univ.t.PP.L.ι) :
    ⊤ ≤ q ⁻¹ᵁ (PPx x).U (fun _ => j) ↔ ⊤ ≤ (q ≫ gxFst x) ⁻¹ᵁ Xo.univ.t.PP.L.U j := by
  rw [top_le_preimage_iff_mem, top_le_preimage_iff_mem]
  constructor
  · intro hp
    exact Set.mem_iInter.1 hp (0 : Fin 1)
  · intro hp
    exact Set.mem_iInter.2 fun _ => hp

theorem exists_pt {R : Type} [CommRing R] (x : Sp R ⟶ Xo.X) (s : Sp ℂ ⟶ Sp R) (p : Sp ℂ ⟶ Xo.univ.t.G.left)
    (h : s ≫ x = p ≫ Xo.univ.t.G.hom) : ∃ q : Sp ℂ ⟶ Gx x, q ≫ gxFst x = p ∧ q ≫ gxSnd x = s :=
  ⟨pullback.lift (f := x) (g := Xo.univ.t.G.hom) s p h, pullback.lift_snd _ _ _, pullback.lift_fst _ _ _⟩

theorem val_pull {R : Type} [CommRing R] (φ : R →+* ℂ) (x₀ : Sp R ⟶ Xo.X) (x : Sp ℂ ⟶ Xo.X)
    (s₀ : LB.Sec (PPx x₀)) (s : LB.Sec (PPx x)) (pm : Gx x ⟶ Gx x₀) (h₁ : pm ≫ gxFst x₀ = gxFst x)
    (h₂ : pm ≫ gxSnd x₀ = gxSnd x ≫ spMap φ)
    (h₃ : ∀ (i : Fin 1 → Xo.univ.t.PP.L.ι) (h : (PPx x).U i ≤ pm ⁻¹ᵁ (PPx x₀).U i),
      (pm.appLE _ _ h).hom (s₀.f i) = s.f i)
    (i : Fin 1 → Xo.univ.t.PP.L.ι) (pt : Sp ℂ ⟶ Gx x) (q : Sp ℂ ⟶ Gx x₀) (e₁ : q ≫ gxFst x₀ = pt ≫ gxFst x)
    (e₂ : pt ≫ gxSnd x = 𝟙 _) (e₃ : q ≫ gxSnd x₀ = spMap φ) (hp : ⊤ ≤ pt ⁻¹ᵁ (PPx x).U i) :
    valAt' pt ((PPx x).U i) (s.f i) = valAt' q ((PPx x₀).U i) (s₀.f i) := by
  have hq : q = pt ≫ pm := SecCalc.pm_ext _ _
    (e₁.trans (show pt ≫ gxFst x = (pt ≫ pm) ≫ gxFst x₀ by rw [Category.assoc, h₁]))
    (e₃.trans (show spMap φ = (pt ≫ pm) ≫ gxSnd x₀ by
      rw [Category.assoc, h₂, ← Category.assoc, e₂, Category.id_comp]))
  rw [← h₃ i (SecCalc.ppx_le pm h₁ i), hq]
  exact valAt'_appLE pt pm _ _ _ _ hp

theorem val_mul_pull (hT : Out.SecTwistSt) {R : Type} [CommRing R] (φ : R →+* ℂ) (a : ℂ) (x₀ : Sp R ⟶ Xo.X)
    (x y : Sp ℂ ⟶ Xo.X) (hxy : y = x)
    (s₀ : LB.Sec (PPx x₀)) (s : LB.Sec (PPx x)) (t : LB.Sec (PPx y)) (pm : Gx x ⟶ Gx x₀)
    (h₁ : pm ≫ gxFst x₀ = gxFst x) (h₂ : pm ≫ gxSnd x₀ = gxSnd x ≫ spMap φ)
    (h₃ : ∀ (i : Fin 1 → Xo.univ.t.PP.L.ι) (h : (PPx x).U i ≤ pm ⁻¹ᵁ (PPx x₀).U i),
      (pm.appLE _ _ h).hom (s₀.f i) = s.f i) (hst : SecBC (RingHom.id ℂ) a x y s t)
    (i : Fin 1 → Xo.univ.t.PP.L.ι) (pt : Sp ℂ ⟶ Gx y) (q : Sp ℂ ⟶ Gx x₀) (e₁ : q ≫ gxFst x₀ = pt ≫ gxFst y)
    (e₂ : pt ≫ gxSnd y = 𝟙 _) (e₃ : q ≫ gxSnd x₀ = spMap φ) (hp : ⊤ ≤ pt ⁻¹ᵁ (PPx y).U i) :
    valAt' pt ((PPx y).U i) (t.f i) = a * valAt' q ((PPx x₀).U i) (s₀.f i) := by
  subst hxy
  have hy : y = spMap (RingHom.id ℂ) ≫ y := by rw [SecCalc.spMap_id', Category.id_comp]
  have ht := ((SecCalc.sec_calc E H Dw l Xo ℂ ℂ ℂ _ _ y y y hy hy).2.1 a s t).1 hst i
  rw [ht, (sec_values_complex_fibre hT E H Dw l Xo y s).1 a i pt e₂,
    val_pull φ x₀ y s₀ s pm h₁ h₂ h₃ i pt q e₁ e₂ e₃ hp]

theorem exists_val_ne (hT : Out.SecTwistSt) {R : Type} [CommRing R] (φ : R →+* ℂ) (x₀ : Sp R ⟶ Xo.X)
    (x u : Sp ℂ ⟶ Xo.X) (hu : u = x) (s₀ : LB.Sec (PPx x₀)) (s : LB.Sec (PPx x)) (pm : Gx x ⟶ Gx x₀)
    (h₁ : pm ≫ gxFst x₀ = gxFst x) (h₂ : pm ≫ gxSnd x₀ = gxSnd x ≫ spMap φ)
    (h₃ : ∀ (i : Fin 1 → Xo.univ.t.PP.L.ι) (h : (PPx x).U i ≤ pm ⁻¹ᵁ (PPx x₀).U i),
      (pm.appLE _ _ h).hom (s₀.f i) = s.f i) (hs : SecGen x s) :
    ∃ (e : Over.mk u ⟶ Xo.univ.t.G) (j : Xo.univ.t.PP.L.ι), ∀ q : Sp ℂ ⟶ Gx x₀, q ≫ gxFst x₀ = e.left →
      q ≫ gxSnd x₀ = spMap φ → valAt' q ((PPx x₀).U (fun _ => j)) (s₀.f (fun _ => j)) ≠ 0 := by
  subst hu
  obtain ⟨i, pt, hpt, hv⟩ := (sec_values_complex_fibre hT E H Dw l Xo u s).2.1.1 hs
  obtain ⟨j, rfl⟩ : ∃ j, i = fun _ => j := ⟨i (0 : Fin 1), funext fun k : Fin 1 => congrArg i (Subsingleton.elim _ _)⟩
  have hc : gxSnd u ≫ u = gxFst u ≫ Xo.univ.t.G.hom := pullback.condition (f := u) (g := Xo.univ.t.G.hom)
  refine ⟨Over.homMk (pt ≫ gxFst u) ?_, j, fun q e₁ e₃ => ?_⟩
  · show (pt ≫ gxFst u) ≫ Xo.univ.t.G.hom = u
    rw [Category.assoc, ← hc, ← Category.assoc, hpt, Category.id_comp]
  · rw [← val_pull φ x₀ u s₀ s pm h₁ h₂ h₃ _ pt q e₁ hpt e₃ (top_le_preimage_of_valAt'_ne_zero _ hv)]
    exact hv

end

theorem differentiableOn_generator_factor : Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r) (k : Fin F.n) (T : ThetaData e F M k) (R : Type) [CommRing R] [Algebra c.F R] (y₀ : FrPt Xo c R) (B : Set (Fin T.m → ℂ)) (ψ : (Fin T.m → ℂ) → (R →ₐ[c.F] CAt σ)) (κ : (Fin T.m → ℂ) → ℂ) (z y : (Fin T.m → ℂ) → FrPt Xo c (CAt σ)) (G : (Fin T.m → ℂ) → (∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) (CAt σ))) (a : (Fin T.m → ℂ) → CAt σ), IsOpen B → B ⊆ T.co ⁻¹' (M.X k).dom → (∀ t : R, DifferentiableOn ℂ (fun b => toC (ψ b t)) B) → (∀ b ∈ B, FrMap (ψ b) y₀ (z b) ∧ FrChg (G b) (a b) (z b) (y b) ∧ IsThetaPt T b (κ b) (y b)) → DifferentiableOn ℂ κ B → DifferentiableOn ℂ (fun b => toC (a b)) B := by
  intro hT E _ _ _ H Dw l Xo c σ g e F r M k T R _ _ y₀ B ψ κ z y G a hB hBd hψ hb hκ b₀ hb₀
  let φ : (Fin T.m → ℂ) → (R →+* ℂ) := fun b => (ψ b).toRingHom
  have hP : IsHolPeriods (F.Di k) (fun j => relab c σ (e j).1) B (fun b => T.Pf (T.co b)) :=
    ⟨fun b hb => T.holPer.1 b (hBd hb), fun x => (T.holPer.2 x).mono hBd⟩
  have hux : ∀ b ∈ B, F.u k (T.Pf (T.co b)) = (z b).x := fun b h =>
    (hb b h).2.2.1.symm.trans (hb b h).2.1.1
  obtain ⟨pm₀, p₁, p₂, p₃⟩ := (hb b₀ hb₀).1.2.2
  obtain ⟨e₀, j, hne⟩ := exists_val_ne hT (φ b₀) y₀.x (z b₀).x _ (hux b₀ hb₀) y₀.s (z b₀).s pm₀ p₁ p₂ p₃ (z b₀).gen
  obtain ⟨w₀, rfl⟩ := F.ex_onto k _ (hP.1 b₀ hb₀) e₀
  have hq₁ : ∀ b ∈ B, ∃ q : Sp ℂ ⟶ Gx y₀.x, q ≫ gxFst y₀.x = (F.ex k (T.Pf (T.co b)) w₀).left ∧
      q ≫ gxSnd y₀.x = spMap (φ b) := fun b h =>
    exists_pt _ _ _ (((hb b h).1.1.symm.trans (hux b h).symm).trans (Over.w (F.ex k (T.Pf (T.co b)) w₀)).symm)
  have hq₂ : ∀ b, ∃ q : Sp ℂ ⟶ Gx y₀.x, b ∈ B → q ≫ gxFst y₀.x = (F.ex k (T.Pf (T.co b)) w₀).left ∧
      q ≫ gxSnd y₀.x = spMap (φ b) := fun b => by
    by_cases h : b ∈ B
    · exact (hq₁ b h).imp fun _ h' _ => h'
    · exact ⟨(hq₁ b₀ hb₀).choose, fun h' => absurd h' h⟩
  choose q hq using hq₂
  have hι : Differentiable ℂ (fun b : Fin T.m → ℂ => ((b, w₀) : (Fin T.m → ℂ) × (Fin g → ℂ))) := by fun_prop
  have hol : IsHolTo B q := by
    refine HolPullback.isHolTo_of_components _ B _ _ _ _ (gxSnd y₀.x) (gxFst y₀.x) y₀.x Xo.univ.t.G.hom q
      (IsPullback.of_hasPullback y₀.x Xo.univ.t.G.hom) hB ?_ ?_
    · exact LocLift.isHolTo_congr (ThetaValueCont.isHolTo_spMap hB φ hψ) fun b h => (hq b h).2
    · exact LocLift.isHolTo_congr (LocLift.isHolTo_comp (F.hol k _ B _ hB hP).2 hB hι.differentiableOn
        fun b h => ⟨h, trivial⟩) fun b h => (hq b h).1
  have hW := (hol ((Gx y₀.x).basicOpen (y₀.s.f (fun _ => j))) 0).1
  set W := {b ∈ B | ⊤ ≤ q b ⁻¹ᵁ (Gx y₀.x).basicOpen (y₀.s.f (fun _ => j))} with hWd
  have hb₀W : b₀ ∈ W := ⟨hb₀, (top_le_preimage_basicOpen_iff _ _ _).2 (hne _ (hq b₀ hb₀).1 (hq b₀ hb₀).2)⟩
  have vnz : ∀ b ∈ W, valAt' (q b) ((PPx y₀.x).U (fun _ => j)) (y₀.s.f (fun _ => j)) ≠ 0 := fun b h =>
    (top_le_preimage_basicOpen_iff _ _ _).1 h.2
  have m₁ : ∀ b ∈ W, ⊤ ≤ q b ⁻¹ᵁ (PPx y₀.x).U (fun _ => j) := fun b h =>
    top_le_preimage_of_valAt'_ne_zero _ (vnz b h)
  have m₂ : ∀ b ∈ W, ⊤ ≤ (F.ex k (T.Pf (T.co b)) w₀).left ⁻¹ᵁ Xo.univ.t.PP.L.U j := fun b h => by
    rw [← (hq b h.1).1]
    exact (chart_iff _ _ _).1 (m₁ b h)
  have hθ := (ThetaHalf.thetaChar_holomorphic_ne_zero g T.c₁ T.c₂ T.half₁ T.half₂).2 T.m B T.h T.ta hB
    (fun b h => ⟨(T.norm b (hBd h)).2.1, (T.norm b (hBd h)).2.2.1⟩)
    (fun i i' => ⟨(T.hol i i').1.mono hBd, (T.hol i i').2.mono hBd⟩)
  have d₀ : DifferentiableOn ℂ κ W := hκ.mono fun b h => h.1
  have d₁ : DifferentiableOn ℂ (fun b => thetaChar (T.ta b) T.c₁ T.c₂ (T.h b *ᵥ w₀)) W :=
    DifferentiableOn.comp (f := fun b : Fin T.m → ℂ => ((b, w₀) : (Fin T.m → ℂ) × (Fin g → ℂ)))
      (g := fun bz : (Fin T.m → ℂ) × (Fin g → ℂ) => thetaChar (T.ta bz.1) T.c₁ T.c₂ (T.h bz.1 *ᵥ bz.2))
      hθ hι.differentiableOn fun b h => ⟨h.1, trivial⟩
  have d₂ : DifferentiableOn ℂ (fun b => T.fr j (b, w₀)) W :=
    DifferentiableOn.comp (f := fun b : Fin T.m → ℂ => ((b, w₀) : (Fin T.m → ℂ) × (Fin g → ℂ))) (g := T.fr j)
      (T.fr_hol j) hι.differentiableOn fun b h => ⟨hBd h.1, m₂ b h⟩
  have d₃ : DifferentiableOn ℂ (fun b => valAt' (q b) ((PPx y₀.x).U (fun _ => j)) (y₀.s.f (fun _ => j))) W :=
    (hol _ _).2.mono fun b h => ⟨h.1, m₁ b h⟩
  have key : ∀ b ∈ W, κ b * thetaChar (T.ta b) T.c₁ T.c₂ (T.h b *ᵥ w₀) * T.fr j (b, w₀) =
      toC (a b) * valAt' (q b) ((PPx y₀.x).U (fun _ => j)) (y₀.s.f (fun _ => j)) := fun b h => by
    obtain ⟨⟨-, -, pm, p₁, p₂, p₃⟩, ⟨hyz, -, hbc⟩, hyu, -, hth⟩ := hb b h.1
    obtain ⟨pt, e₁, e₂⟩ := exists_pt (R := ℂ) (y b).x (𝟙 _) (F.ex k (T.Pf (T.co b)) w₀).left
      (((Category.id_comp _).trans hyu).trans (Over.w (F.ex k (T.Pf (T.co b)) w₀)).symm)
    refine (hth j w₀ pt e₁ e₂ (m₂ b h)).symm.trans ?_
    refine val_mul_pull hT (φ b) (toC (a b)) y₀.x (z b).x (y b).x hyz y₀.s (z b).s (y b).s pm p₁ p₂ p₃ hbc _ pt (q b)
      ((hq b h.1).1.trans e₁.symm) e₂ (hq b h.1).2 ((chart_iff _ _ _).2 ?_)
    rw [e₁]
    exact m₂ b h
  have d : DifferentiableOn ℂ (fun b => toC (a b)) W := (((d₀.mul d₁).mul d₂).mul (d₃.inv vnz)).congr fun b h =>
    ((mul_inv_eq_iff_eq_mul₀ (vnz b h)).2 (key b h)).symm
  exact (d.differentiableAt (hW.mem_nhds hb₀W)).differentiableWithinAt

end GlobalTheory.HolGen
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory.Frames

theorem secNZ_of_secGen : Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x : Sp S ⟶ Xo.X) (s : LB.Sec (PPx x)), SecGen x s → SecNZ x s := by
  intro hbc E _ _ _ H Dw l Xo S _ x s hs p
  obtain ⟨g, hg, θ, hθ⟩ := GlobalTheory.T.exists_local_generator_stable_baseChange hbc E H Dw l Xo S x p
  have hid : ∀ (R : Type) [CommRing R] (z : Sp R ⟶ Xo.X), z = spMap (RingHom.id R) ≫ z := by
    intro R _ z
    have : spMap (RingHom.id R) = 𝟙 (Sp R) := Spec.map_id _
    rw [this, Category.id_comp]
  obtain ⟨-, hc2, -, hc4⟩ := GlobalTheory.T.scaledBaseChange_fibreSection_calculus E H Dw l Xo (Localization.Away g) (Localization.Away g)
    (Localization.Away g) (RingHom.id _) (RingHom.id _) (spMap (algebraMap S (Localization.Away g)) ≫ x)
    _ _ (hid _ _) (hid _ _)
  have hθθ : SecBC (RingHom.id (Localization.Away g)) 1 _ _ θ θ :=
    (hc2 1 θ θ).2 fun i => by rw [(hc4 1 1 i).2.2, _root_.one_mul]
  have hnz := (hθ _ (RingHom.id _) _ θ (hid _ _) hθθ).2
  obtain ⟨p', hp'⟩ : ∃ p' : PrimeSpectrum (Localization.Away g),
      PrimeSpectrum.comap (algebraMap S (Localization.Away g)) p' = p := by
    have h := PrimeSpectrum.localization_away_comap_range (Localization.Away g) g
    have : (p : PrimeSpectrum S) ∈ Set.range (PrimeSpectrum.comap (algebraMap S (Localization.Away g))) := by
      rw [h]; exact hg
    exact this
  obtain ⟨q, i, hq, hqi⟩ := hnz p'
  obtain ⟨N, s₀, s₁, h01, h1⟩ := GlobalTheory.T.exists_fibreSection_pow_mul_baseChange_away E H Dw l Xo S x g θ
  have hu : IsUnit (scal (spMap (algebraMap S (Localization.Away g)) ≫ x)
      ((algebraMap S (Localization.Away g)) g ^ N) i) := by
    obtain ⟨v, hv⟩ := ((IsLocalization.Away.algebraMap_isUnit (S := Localization.Away g) g).pow N).exists_right_inv
    refine IsUnit.of_mul_eq_one (scal _ v i) ?_
    rw [← (hc4 _ v i).1, hv, (hc4 1 1 i).2.2]
  have hq1 : q ∈ (Gx _).basicOpen (s₁.f i) := by
    rw [h1 i, Scheme.basicOpen_mul, Scheme.basicOpen_of_isUnit _ hu]
    exact ⟨Scheme.basicOpen_le _ _ hqi, hqi⟩
  obtain ⟨q₀, i₀, hq₀, hqi₀⟩ := (GlobalTheory.Frames.secBC_nonvanishing_iff E H Dw l Xo S (Localization.Away g) _ x _ rfl s₀ s₁ h01 p').1
    ⟨q, i, hq, hq1⟩
  obtain ⟨b, hb, -⟩ := hs s₀
  rw [hb i₀, Scheme.basicOpen_mul] at hqi₀
  exact ⟨q₀, i₀, hq₀.trans hp', hqi₀.2⟩

end GlobalTheory.Frames
end
