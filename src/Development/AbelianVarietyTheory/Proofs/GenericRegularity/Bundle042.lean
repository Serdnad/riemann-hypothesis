module

public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle008
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle024
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ContinuousOnThetaFrameValueHolomorphicFamily
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle064
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle054
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle046
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle059
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle105
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle014
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle012
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle039
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle030
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle009
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle032
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle025
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
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLinearEquivLift
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.Bundle001

@[expose] public section

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif GlobalTheory.FrameNorm
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.GenFactor

open GlobalTheory.HolGen

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l}

theorem exists_factor (hT : Out.SecTwistSt) {Z : Type} (x u : Sp ℂ ⟶ Xo.X) (hxu : x = u) (s : LB.Sec (PPx x))
    (hs : SecGen x s) (e : Z → (Over.mk u ⟶ Xo.univ.t.G)) (θ : Z → ℂ) (fr : Xo.univ.t.PP.L.ι → Z → ℂ)
    (hθ : ∃ z, θ z ≠ 0) (hfr : ∀ j z, ⊤ ≤ (e z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr j z ≠ 0)
    (t : (Xo.univ.t.PP.L.pull (pullback.fst Xo.univ.t.G.hom u)).Sec)
    (ht : ∀ j z (p : Sp ℂ ⟶ pullback Xo.univ.t.G.hom u), p ≫ pullback.fst _ _ = (e z).left →
      p ≫ pullback.snd _ _ = 𝟙 _ → ⊤ ≤ (e z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      valAt' p ((Xo.univ.t.PP.L.pull (pullback.fst Xo.univ.t.G.hom u)).U (fun _ => j)) (t.f (fun _ => j)) =
        θ z * fr j z) :
    ∃ κ : ℂ, κ ≠ 0 ∧ ∀ j z (pt : Sp ℂ ⟶ Gx x), pt ≫ Formalism.L2.PjFree.gxFst x = (e z).left → pt ≫ Formalism.L2.PjFree.gxSnd x = 𝟙 (Sp ℂ) →
      ⊤ ≤ (e z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      valAt' pt ((PPx x).U (fun _ => j)) (s.f (fun _ => j)) = κ * θ z * fr j z := by
  subst hxu
  obtain ⟨s', hs'⟩ := GlobalTheory.FibreSection.exists_sec_same_values E H Dw l Xo x t
  obtain ⟨a, ha, -⟩ := hs s'
  have key : ∀ j z (pt : Sp ℂ ⟶ Gx x), pt ≫ Formalism.L2.PjFree.gxFst x = (e z).left → pt ≫ Formalism.L2.PjFree.gxSnd x = 𝟙 (Sp ℂ) →
      ⊤ ≤ (e z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      a * valAt' pt ((PPx x).U (fun _ => j)) (s.f (fun _ => j)) = θ z * fr j z := by
    intro j z pt e₁ e₂ hj
    have hw : (e z).left ≫ Xo.univ.t.G.hom = 𝟙 _ ≫ x := (Over.w (e z)).trans (Category.id_comp _).symm
    have p₁ := pullback.lift_fst (f := Xo.univ.t.G.hom) (g := x) (e z).left (𝟙 _) hw
    have p₂ := pullback.lift_snd (f := Xo.univ.t.G.hom) (g := x) (e z).left (𝟙 _) hw
    refine ((sec_values_complex_fibre hT E H Dw l Xo x s).1 a (fun _ => j) pt e₂).symm.trans ?_
    refine (congrArg (valAt' pt ((PPx x).U (fun _ => j))) (ha (fun _ => j))).symm.trans ?_
    exact (hs' j pt _ (p₁.trans e₁.symm) p₂ e₂).trans (ht j z _ p₁ p₂ hj)
  obtain ⟨z₀, hz₀⟩ := hθ
  obtain ⟨j₀, hj₀⟩ := GlobalTheory.ThetaPtChg.exists_chart_point Xo.univ.t.PP.isLB (e z₀).left
  obtain ⟨pt₀, e₁, e₂⟩ := exists_pt (R := ℂ) x (𝟙 _) (e z₀).left
    ((Category.id_comp _).trans (Over.w (e z₀)).symm)
  have ha0 : a ≠ 0 := by
    rintro rfl
    have := key j₀ z₀ pt₀ e₁ e₂ hj₀
    rw [zero_mul] at this
    exact mul_ne_zero hz₀ (hfr j₀ z₀ hj₀) this.symm
  refine ⟨a⁻¹, inv_ne_zero ha0, fun j z pt e₁ e₂ hj => ?_⟩
  rw [mul_assoc, ← key j z pt e₁ e₂ hj, inv_mul_cancel_left₀ ha0]

end

theorem exists_holomorphic_factor : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (σ' : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ' ty) (k : Fin F.n) (A : Type) [CommRing A] [Algebra c.F A] (yA : FrPt Xo c A) (m : ℕ) (B : Set (Fin m → ℂ)) (φ : (Fin m → ℂ) → (A →ₐ[c.F] CAt σ)) (y : (Fin m → ℂ) → FrPt Xo c (CAt σ)) (P : (Fin m → ℂ) → ((F.Di k).La →+ (Fin g → ℂ))) (θ : (Fin m → ℂ) → (Fin g → ℂ) → ℂ), IsOpen B → (∀ a, DifferentiableOn ℂ (fun b => Formalism.L2.PjFree.toC (φ b a)) B) → (∀ b ∈ B, FrMap (φ b) yA (y b)) → IsHolPeriods (F.Di k) ty B P → (∀ b ∈ B, (y b).x = F.u k (P b)) → (∀ z, DifferentiableOn ℂ (fun b => θ b z) B) → (∀ b ∈ B, ∃ z, θ b z ≠ 0) → IsThetaFrame Xo.univ.t.PP B (fun b => F.u k (P b)) (fun b z => (F.ex k (P b) z).left) θ → ∃ (fr : Xo.univ.t.PP.L.ι → (Fin m → ℂ) × (Fin g → ℂ) → ℂ) (κ : (Fin m → ℂ) → ℂ), RigFrame F k B P fr ∧ DifferentiableOn ℂ κ B ∧ ∀ b ∈ B, κ b ≠ 0 ∧ SecVal F k (P b) (y b).x (y b).s (fun z => κ b * θ b z) (fun j z => fr j (b, z)) := by
  intro E _ _ _ H Dw l Xo c σ σ' g ty F k A _ _ yA m B ψ y P θ hB hψ hb hP hxu hθ hθ0 hfr
  have hT : Out.SecTwistSt := GlobalTheory.abelianSchemeLaws_all.2.secTwist
  obtain ⟨fr, f₁, f₂, f₃, f₄, f₅⟩ := hfr
  have hκ₁ : ∀ b, ∃ κ : ℂ, b ∈ B → κ ≠ 0 ∧
      SecVal F k (P b) (y b).x (y b).s (fun z => κ * θ b z) (fun j z => fr j (b, z)) := fun b => by
    by_cases h : b ∈ B
    · obtain ⟨t, ht⟩ := f₅ b h
      obtain ⟨κ, h₁, h₂⟩ := exists_factor hT (y b).x (F.u k (P b)) (hxu b h) (y b).s (y b).gen (F.ex k (P b)) (θ b)
        (fun j z => fr j (b, z)) (hθ0 b h) (fun j z hz => f₂ j b z h hz) t ht
      exact ⟨κ, fun _ => ⟨h₁, h₂⟩⟩
    · exact ⟨0, fun h' => absurd h' h⟩
  choose κ hκ using hκ₁
  refine ⟨fr, κ, ⟨f₁, f₂, f₃, f₄⟩, fun b₀ hb₀ => ?_, hκ⟩
  let φ : (Fin m → ℂ) → (A →+* ℂ) := fun b => (ψ b).toRingHom
  have hux : ∀ b ∈ B, F.u k (P b) = (y b).x := fun b h => (hxu b h).symm
  obtain ⟨pm₀, p₁, p₂, p₃⟩ := (hb b₀ hb₀).2.2
  obtain ⟨e₀, j, hne⟩ := exists_val_ne hT (φ b₀) yA.x (y b₀).x _ (hux b₀ hb₀) yA.s (y b₀).s pm₀ p₁ p₂ p₃ (y b₀).gen
  obtain ⟨w₀, rfl⟩ := F.ex_onto k _ (hP.1 b₀ hb₀) e₀
  have hq₁ : ∀ b ∈ B, ∃ q : Sp ℂ ⟶ Gx yA.x, q ≫ Formalism.L2.PjFree.gxFst yA.x = (F.ex k (P b) w₀).left ∧
      q ≫ Formalism.L2.PjFree.gxSnd yA.x = spMap (φ b) := fun b h =>
    exists_pt _ _ _ (((hb b h).1.symm.trans (hux b h).symm).trans (Over.w (F.ex k (P b) w₀)).symm)
  have hq₂ : ∀ b, ∃ q : Sp ℂ ⟶ Gx yA.x, b ∈ B → q ≫ Formalism.L2.PjFree.gxFst yA.x = (F.ex k (P b) w₀).left ∧
      q ≫ Formalism.L2.PjFree.gxSnd yA.x = spMap (φ b) := fun b => by
    by_cases h : b ∈ B
    · exact (hq₁ b h).imp fun _ h' _ => h'
    · exact ⟨(hq₁ b₀ hb₀).choose, fun h' => absurd h' h⟩
  choose q hq using hq₂
  have hι : Differentiable ℂ (fun b : Fin m → ℂ => ((b, w₀) : (Fin m → ℂ) × (Fin g → ℂ))) := by fun_prop
  have hol : IsHolTo B q := by
    refine HolPullback.isHolTo_of_components _ B _ _ _ _ (Formalism.L2.PjFree.gxSnd yA.x) (Formalism.L2.PjFree.gxFst yA.x) yA.x Xo.univ.t.G.hom q
      (IsPullback.of_hasPullback yA.x Xo.univ.t.G.hom) hB ?_ ?_
    · exact LocLift.isHolTo_congr (ThetaValueCont.isHolTo_spMap hB φ hψ) fun b h => (hq b h).2
    · exact LocLift.isHolTo_congr (LocLift.isHolTo_comp (F.hol k _ B _ hB hP).2 hB hι.differentiableOn
        fun b h => ⟨h, trivial⟩) fun b h => (hq b h).1
  have hW := (hol ((Gx yA.x).basicOpen (yA.s.f (fun _ => j))) 0).1
  set W := {b ∈ B | ⊤ ≤ q b ⁻¹ᵁ (Gx yA.x).basicOpen (yA.s.f (fun _ => j))} with hWd
  have hb₀W : b₀ ∈ W := ⟨hb₀, (top_le_preimage_basicOpen_iff _ _ _).2 (hne _ (hq b₀ hb₀).1 (hq b₀ hb₀).2)⟩
  have vnz : ∀ b ∈ W, valAt' (q b) ((PPx yA.x).U (fun _ => j)) (yA.s.f (fun _ => j)) ≠ 0 := fun b h =>
    (top_le_preimage_basicOpen_iff _ _ _).1 h.2
  have m₁ : ∀ b ∈ W, ⊤ ≤ q b ⁻¹ᵁ (PPx yA.x).U (fun _ => j) := fun b h =>
    top_le_preimage_of_valAt'_ne_zero _ (vnz b h)
  have m₂ : ∀ b ∈ W, ⊤ ≤ (F.ex k (P b) w₀).left ⁻¹ᵁ Xo.univ.t.PP.L.U j := fun b h => by
    rw [← (hq b h.1).1]
    exact (chart_iff _ _ _).1 (m₁ b h)
  have d₁ : DifferentiableOn ℂ (fun b => θ b w₀) W := (hθ w₀).mono fun b h => h.1
  have d₂ : DifferentiableOn ℂ (fun b => fr j (b, w₀)) W :=
    DifferentiableOn.comp (f := fun b : Fin m → ℂ => ((b, w₀) : (Fin m → ℂ) × (Fin g → ℂ))) (g := fr j)
      (f₁ j) hι.differentiableOn fun b h => ⟨h.1, m₂ b h⟩
  have d₃ : DifferentiableOn ℂ (fun b => valAt' (q b) ((PPx yA.x).U (fun _ => j)) (yA.s.f (fun _ => j))) W :=
    (hol _ _).2.mono fun b h => ⟨h.1, m₁ b h⟩
  have key : ∀ b ∈ W, valAt' (q b) ((PPx yA.x).U (fun _ => j)) (yA.s.f (fun _ => j)) =
      κ b * (θ b w₀ * fr j (b, w₀)) := fun b h => by
    obtain ⟨-, -, pm, p₁, p₂, p₃⟩ := hb b h.1
    obtain ⟨pt, e₁, e₂⟩ := exists_pt (R := ℂ) (y b).x (𝟙 _) (F.ex k (P b) w₀).left
      (((Category.id_comp _).trans (hxu b h.1)).trans (Over.w (F.ex k (P b) w₀)).symm)
    rw [← mul_assoc]
    refine Eq.trans ?_ ((hκ b h.1).2 j w₀ pt e₁ e₂ (m₂ b h))
    refine (val_pull (φ b) yA.x (y b).x yA.s (y b).s pm p₁ p₂ p₃ _ pt (q b)
      ((hq b h.1).1.trans e₁.symm) e₂ (hq b h.1).2 ((chart_iff _ _ _).2 ?_)).symm
    rw [e₁]
    exact m₂ b h
  have nz : ∀ b ∈ W, θ b w₀ * fr j (b, w₀) ≠ 0 := fun b h =>
    right_ne_zero_of_mul (key b h ▸ vnz b h)
  have d : DifferentiableOn ℂ κ W := (d₃.mul ((d₁.mul d₂).inv nz)).congr fun b h =>
    ((mul_inv_eq_iff_eq_mul₀ (nz b h)).2 (key b h)).symm
  exact (d.differentiableAt (hW.mem_nhds hb₀W)).differentiableWithinAt

end GlobalTheory.GenFactor
end

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FrameNorm GlobalTheory.Reg

namespace GlobalTheory.Reg

theorem exists_cusp_restrict_comp_int : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r), (∀ σ, Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf (U σ)) → ∀ (h : GenFrEx Xo c) (Z : Comp Xo c) a n, ∀ g ∈ Formalism.L2.PjFree.cusp Xo c U a n, ∃ g' ∈ Formalism.L2.PjFree.cusp Xo c U a n, evC h Z g' = evC h Z g ∧ (∀ Z', Z' ≠ Z → evC h Z' g' = 0) ∧ ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io), evI y g' = evI y g ∨ evI y g' = 0 := by
  intro E _ _ _ H Dw l Xo c r U hU h Z a n g hg
  obtain ⟨hL, -, -, hA⟩ := GlobalTheory.T.evaluation_laws_generic_frames_atlas_hold E H Dw l Xo c
  obtain ⟨χ, hχ, hidem, h1, h0⟩ := exists_idem_section E H Dw l Xo c hL h (hA h) Z

  have hm : ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (f f' : Rul Xo c),
      evR Xo c (f * f') y = evR Xo c f y * evR Xo c f' y := by
    intro S _ _ y f f'
    unfold evR
    exact evalAt_mul _ _ f f' y
  refine ⟨χ * g, GlobalTheory.Reg.IdemCusp.idem_mul_mem_cusp E H Dw l Xo c r U hU χ hχ hidem a n g hg, ?_, ?_, ?_⟩
  · unfold evC at h1 ⊢
    rw [hm, h1, one_mul]
  · intro Z' hZ'
    have h0' := h0 Z' hZ'
    unfold evC at h0' ⊢
    rw [hm, h0', zero_mul]
  · intro T io y
    letI := io.toAlgebra
    unfold evI

    have hy : IsIdempotentElem (evR Xo c χ y.1) := by
      unfold IsIdempotentElem
      rw [← hm, hidem]
    rcases IsIdempotentElem.iff_eq_zero_or_one.mp hy with h' | h'
    · right
      rw [hm, h', zero_mul]
    · left
      rw [hm, h', one_mul]

end GlobalTheory.Reg
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

namespace GlobalTheory.Reg

theorem exists_cusp_of_integral_all : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ h : GenFrEx Xo c, ∀ (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r), (∀ σ, Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf (U σ)) → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n N : ℕ) (w : Fin N → Rul Xo c), Dom a n → (∀ i, w i ∈ Formalism.L2.PjFree.cusp Xo c U a n) → ∀ (Z : Comp Xo c) (k m : ℕ) (cf : ℕ → MvPolynomial (Fin N) c.F) (b : Om Z), 0 < k → (∀ i < m, (cf i).IsHomogeneous ((m - i) * k)) → b ^ m + ∑ i ∈ Finset.range m, MvPolynomial.aeval (fun s => evC h Z (w s)) (cf i) * b ^ i = 0 → ∃ g ∈ Formalism.L2.PjFree.cusp Xo c U (k • a) (k * n), evC h Z g = b := by
  intro E _ _ _ H Dw l Xo c h r U hU a n N w hDom hw Z k m cf b hk hcf hb
  have hLaws : EvLaws Xo c ∧ IntDiagUnit Xo c ∧ GenFrEx Xo c ∧ ∀ h : GenFrEx Xo c, Atlas h :=
    GlobalTheory.T.evaluation_laws_generic_frames_atlas_hold E H Dw l Xo c
  obtain ⟨hEv, -, -, hAt⟩ := hLaws
  have hws : ∀ i, w i ∈ sec Xo c a n := fun i => (hw i).1
  obtain ⟨g, hg, hgZ, -, hgeq⟩ :=
    GlobalTheory.T.exists_modularSection_of_integral_genericValue E H Dw l Xo c hEv h (hAt h) a n N w hws Z k m cf b hcf hb
  exact ⟨g, GlobalTheory.T.isCuspForm_of_integral_over_dominantWeight E H Dw l Xo c hEv.test r U hU a n N w hDom hw k m cf hk hcf g hg hgeq, hgZ⟩

end GlobalTheory.Reg
end
