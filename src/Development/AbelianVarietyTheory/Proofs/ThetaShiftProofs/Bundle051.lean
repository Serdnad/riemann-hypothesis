module

public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueConstantTangentVectorsAlongArc
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IdealPart
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle031
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle034
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle030
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle048
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.LieImgIffIsLieComb
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle031
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle028
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle032
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.LiePush
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.ArcLineFunctions.Bundle001
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

noncomputable section

namespace GlobalTheory.ArcQ.FrLin

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

section Const

variable {R : Type} [CommRing R] {X Z : Scheme.{0}}

theorem res_const (p : X ⟶ Sp R) {U V : X.Opens} (h : V ≤ U) (a : R) :
    (X.presheaf.map (homOfLE h).op).hom (constFn p U a) = constFn p V a := by
  exact congrArg (fun k => k.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))
    (Scheme.Hom.appLE_map p (U := ⊤) (V := U) le_top (homOfLE h).op)

theorem appLE_const (p : X ⟶ Sp R) (f : Z ⟶ X) {U : X.Opens} {V : Z.Opens} (h : V ≤ f ⁻¹ᵁ U) (a : R) :
    (f.appLE U V h).hom (constFn p U a) = constFn (f ≫ p) V a := by
  exact congrArg (fun k => k.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))
    (Scheme.Hom.appLE_comp_appLE f p ⊤ U V le_top h)

theorem const_spMap {S : Type} [CommRing S] (φ : R →+* S) (q : X ⟶ Sp S) (U : X.Opens) (a : R) :
    constFn (q ≫ spMap φ) U a = constFn q U (φ a) := by
  have N := congrArg (fun f => f.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at N
  unfold constFn
  rw [N, ← Scheme.Hom.appLE_comp_appLE q (spMap φ) ⊤ ⊤ U le_top le_top, CommRingCat.comp_apply]
  congr 2

def smulSec (p : X ⟶ Sp R) (a : R) {L : LB X} (s : LB.Sec L) : LB.Sec L where
  f j := constFn p _ a * s.f j
  compat i j := by
    rw [map_mul, map_mul, s.compat i j, res_const, res_const]
    ring

theorem isoMaps_smul (p : X ⟶ Sp R) (a : R) {L M : LB X} {w : LB.Iso L M} {s : LB.Sec L} {s' : LB.Sec M}
    (h : IsoMaps w s s') : IsoMaps w (smulSec p a s) (smulSec p a s') := by
  intro i k
  have e := h i k
  simp only [smulSec]
  rw [map_mul, map_mul, e, res_const, res_const]
  exact mul_left_comm _ _ _

end Const

theorem dual_alg {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T) :
    spMap (dualMap φ) ≫ spMap (algebraMap S (DualNumber S)) = spMap (algebraMap T (DualNumber T)) ≫ spMap φ := by
  rw [SecCalc.spMap_comp', SecCalc.spMap_comp']
  congr 1
  exact RingHom.ext fun a => by ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l}

theorem comb_transport {R S : Type} [CommRing R] [CommRing S] (io : R →+* S) {x : Sp S ⟶ Xo.X} {G : SAB H (Sp S)}
    {t : SAB H (Sp R)} (m1 : SABMap G Xo.univ.t x) (m2 : SABMap G t (spMap io)) {n : ℕ} (cf : Fin n → R)
    (v : Fin n → (epsR R ⟶ t.G)) (w : epsR R ⟶ t.G) (hw : IsLieComb cf v w) (q : Fin n → (epsR S ⟶ G.G))
    (hq : ∀ i, (q i).left ≫ m2.φ = spMap (dualMap io) ≫ (v i).left)
    (u : Sp (DualNumber S) ⟶ Xo.univ.t.G.left) (hu : IsCombAt x (fun i => (q i).left ≫ m1.φ) (fun i => io (cf i)) u) :
    ∃ u' : Sp (DualNumber S) ⟶ G.G.left, u' ≫ m1.φ = u ∧ u' ≫ m2.φ = spMap (dualMap io) ≫ w.left ∧
      u' ≫ G.G.hom = spMap (algebraMap S (DualNumber S)) := by
  have wb : w.left ≫ t.G.hom = spMap (algebraMap R (DualNumber R)) := Over.w w
  have cond : (spMap (dualMap io) ≫ w.left) ≫ t.G.hom = spMap (algebraMap S (DualNumber S)) ≫ spMap io := by
    rw [Category.assoc, wb, dual_alg]
  let w' : epsR S ⟶ G.G := Over.homMk (m2.cart.1.lift _ _ cond) (m2.cart.1.lift_snd _ _ cond)
  have hw' : w'.left ≫ m2.φ = spMap (dualMap io) ≫ w.left := m2.cart.1.lift_fst _ _ cond
  have hc : IsLieComb (fun i => io (cf i)) q w' := Chart.comb_baseChange io m2.cart hw hq hw'
  obtain ⟨p, hp, hpp⟩ := (Chart.comb_push m1.cart _ _ _).1 hc
  obtain ⟨p', hp', hpp'⟩ := hu
  obtain rfl : p = p' := funext fun i => Over.OverMorphism.ext ((hp i).trans (hp' i).symm)
  exact ⟨w'.left, hpp.symm.trans hpp', hw', Over.w w'⟩

end GlobalTheory.ArcQ.FrLin

namespace GlobalTheory.ArcQ

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open GlobalTheory.ArcQ.FrLin

theorem isArcFr_of_frChg_const : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] (b : O →+* A) (a : ArcIn Dw l β A b) (χ : Sp (PowerSeries A) ⟶ Y.X) (W : Wit Y a χ) (e e' : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR A)) (th th' : a.D₀.P.L.Sec) (g : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) A) (r : A), ThNZ th → (∀ τ k, GtComb (g τ k) (e τ) (e' τ k)) → ThMul r th th' → ∀ (S : Type) [CommRing S] [Algebra c.F S] (ι : PowerSeries A →+* S) (y y' : FrPt Xo c S), Mono Y.j → IsArcFr W e th ι y → FrChg (fun τ => (g τ).map (ι.comp (PowerSeries.C (R := A)))) (ι (PowerSeries.C (R := A) r)) y y' → IsArcFr W e' th' ι y' := by
  intro hL hL2 E _ _ _ H Dw l Xo c O _ β Y A _ _ _ _ b a χ W e e' th th' g r hth hg hr S _ _ io y y' _ hy hchg
  obtain ⟨x', xo', u', t1', t2', t3', s', t4'⟩ := y'
  obtain ⟨hx, hcomb, hs⟩ := hchg
  dsimp only at hx hcomb hs
  subst x'
  obtain ⟨z, G, m1, m2, φ, zj, zx, φb, φ1, φ2, hu, θ, w1, w2, σ, s1, θ2, hθ, r1, r2, i1, i2, ps, hgx⟩ := hy
  have key : ∀ τ k, ∃ (v : epsR (PowerSeries A) ⟶ W.t.G) (q : epsR S ⟶ G.G), LieImg W (e τ k) v ∧
      q.left ≫ m1.φ = y.u τ k ∧ q.left ≫ m2.φ = spMap (dualMap io) ≫ v.left := fun τ k => by
    obtain ⟨v, p, h1, h2, h3, h4⟩ := hu τ k
    exact ⟨v, Over.homMk p h4, h1, h2, h3⟩
  choose v q hv hq1 hq2 using key
  have hθ' : ThetaOf W th' (smulSec W.t.G.hom (PowerSeries.C (R := A) r) θ) :=
    (((GlobalTheory.existsUnique_thetaOf hL hL2 E H Dw l Xo c O β Y A b a χ W th hth).2 θ hθ).2.2 r th' _ hr).2 fun _ => rfl
  have hs' : ∀ i, s'.f i = scal y.x (io (PowerSeries.C (R := A) r)) i * y.s.f i :=
    ((SecCalc.sec_calc E H Dw l Xo S S S (RingHom.id S) (RingHom.id S) y.x y.x y.x
      (by rw [SecCalc.spMap_id', Category.id_comp]) (by rw [SecCalc.spMap_id', Category.id_comp])).2.1 _ _ _).1 hs
  refine ⟨z, G, m1, m2, φ, zj, zx, φb, φ1, φ2, fun τ k => ?_, _, w1, w2,
    smulSec G.G.hom (io (PowerSeries.C (R := A) r)) σ, smulSec G.G.hom (io (PowerSeries.C (R := A) r)) s1,
    smulSec G.G.hom (io (PowerSeries.C (R := A) r)) θ2, hθ', r1, r2, isoMaps_smul _ _ i1, isoMaps_smul _ _ i2,
    fun j h => ?_, fun gx g1 g2 j h => ?_⟩
  · obtain ⟨w, hw, -⟩ := (GlobalTheory.ConstLie.main hL.globalFns E H Dw l Xo c O β Y A b a χ W (e' τ k)).1
    have hc := (GlobalTheory.ConstLin.lieImg_iff_isLieComb hL.globalFns E H Dw l Xo c O β Y A b a χ W _ (g τ k) (e τ) (e' τ k) (v τ) w (hv τ)
      (hg τ k)).1 hw
    have hy : y.u τ = fun i => (q τ i).left ≫ m1.φ := funext fun i => (hq1 τ i).symm
    have hcoeff : (g τ).map (io.comp (PowerSeries.C (R := A))) k =
        fun i => io (PowerSeries.C (R := A) (g τ k i)) :=
      funext fun i => Matrix.map_apply
    obtain ⟨p, p1, p2⟩ := comb_transport io m1 m2 _ (v τ) w hc (q τ) (hq2 τ) (u' τ k) (by
      simpa only [hy, hcoeff] using hcomb τ k)
    exact ⟨w, p, hw, p1, p2⟩
  · show constFn _ _ _ * θ2.f j = (m2.φ.appLE _ _ h).hom (constFn _ _ _ * θ.f _)
    rw [map_mul, ← ps j h, appLE_const, m2.cart.1.w, const_spMap]
  · refine Eq.trans ?_ (congrArg (gx.appLE _ _ h).hom (hs' _)).symm
    refine Eq.trans ?_ (map_mul _ _ _).symm
    refine congrArg₂ (· * ·) ?_ (hgx gx g1 g2 j h)
    exact ((appLE_const _ gx h _).trans (congrArg (fun p => constFn p _ _) g2)).symm

end GlobalTheory.ArcQ
end
end

section

noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.ConstTan

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} [StarRing (𝓞 E)]
variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
variable [Algebra (FractionRing ℂ) ℂ] {Y : Model Xo c β} {b : O →+* ℂ} {a : ArcIn D l β ℂ b} {χ : Sp ℂ⟦X⟧ ⟶ Y.X}
  {W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ} {Λ : _root_.GlobalTheory.ArcPts.GtAn a}

theorem exists_isUnit_tau (Ξ : ConstPts W Λ) (u : Λ.A.V) :
    ∃ k, ⊤ ≤ (Ξ.x u).left ⁻¹ᵁ W.P.U.LG.L.U k ∧ IsUnit (Ξ.τ u k) := by
  obtain ⟨k, hk⟩ := exists_chart W.P.U.LG.isLB ((show Sp ℂ⟦X⟧ ⟶ _ from (Ξ.x u).left) (cpt ℂ⟦X⟧))
  have hk' : ⊤ ≤ (Ξ.x u).left ⁻¹ᵁ W.P.U.LG.L.U k := (top_le_iff_cpt (A := ℂ⟦X⟧) _ _).2 hk
  obtain ⟨jM, hM⟩ := exists_chart W.P.D.toPre.P.isLB ((show Sp ℂ⟦X⟧ ⟶ _ from (Ξ.g u).b.left) (cpt ℂ⟦X⟧))
  have h₀ := FrameValue.le_chartAt a.D₀.P.isLB (Λ.u.ex u.2).left
  have hb : (show Sp ℂ⟦X⟧ ⟶ _ from (Ξ.g u).b.left) ≫ W.φ = spMap (PowerSeries.C (R := ℂ)) ≫ (Λ.u.ex u.2).left :=
    ((Ξ.g_rel u 0).1 2).trans (congrArg (spMap (PowerSeries.C (R := ℂ)) ≫ ·) (Λ.ex0_b u))
  have hj : ⊤ ≤ (show Sp ℂ⟦X⟧ ⟶ _ from (Ξ.g u).b.left) ⁻¹ᵁ (LB.div (a.D₀.P.L.pull W.φ) W.P.D.toPre.P.L).U
      (fun _ => FrameValue.chartAt a.D₀.P.isLB (Λ.u.ex u.2).left, jM) :=
    (top_le_iff_cpt _ _).2 ⟨mem_pull.2 ((congrArg (fun q => q (cpt ℂ⟦X⟧) ∈ a.D₀.P.L.U _) hb).mpr
      (FormalValue.top_le_comp h₀ _ trivial)), hM⟩
  refine ⟨k, hk', isUnit_of_mul_isUnit_right ((congrArg IsUnit (Ξ.τ_eq u k jM _ hk' hj)).mpr ?_)⟩
  exact (Units.isUnit _).mul ((Ne.isUnit (Λ.u.fr_ne _ u.2 h₀)).map _)

end

theorem isTan_of_diffHyp : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (Λ : _root_.GlobalTheory.ArcPts.GtAn a) (Ξ : ConstPts W Λ) (Φ : GenPts Λ.A W.t gen) (g : ℕ) (h : Λ.A.V ≃L[ℂ] (Fin g → ℂ)) (z₀ : Fin g → ℂ) (ν : Out.GtPt a.D₀ (epsR ℂ)) (v : epsR (PowerSeries ℂ) ⟶ W.t.G) (ρ : DualNumber ℂ⟦X⟧ →+* DualNumber ℂ⸨X⸩) (νK : Sp (DualNumber ℂ⸨X⸩) ⟶ pullback W.t.G.hom gen), Ξ.IsGen Φ → DiffHyp W (fun z => Λ.ex0 (h.symm z)) z₀ ν v → (∀ r, ρ (TrivSqZeroExt.inl r) = TrivSqZeroExt.inl (algebraMap ℂ⟦X⟧ ℂ⸨X⸩ r)) → ρ DualNumber.eps = DualNumber.eps → νK ≫ pullback.fst _ _ = spMap ρ ≫ v.left → νK ≫ pullback.snd _ _ = spMap (algebraMap ℂ⸨X⸩ (DualNumber ℂ⸨X⸩)) → Φ.IsTan (h.symm z₀) νK := by
  intro h₁ h₂ E _ _ _ H _ D l Xo c O _ β Y _ _ b a χ W Λ Ξ Φ g h z₀ ν v ρ νK hΦ hd hρ hε hν₁ hν₂
  haveI := isLocalRing_dual ℂ⟦X⟧
  haveI := isLocalRing_dual ℂ
  obtain ⟨g₁, hg₁⟩ := GlobalTheory.T.exists_constantTorusExtension_tangentRel h₁ E H D l Xo c O β Y b a χ W ν
  have hf := GlobalTheory.T.constantTangent_eq_formalPoint_transported E H D l Xo c O β Y b a χ W g _ z₀ ν v g₁ hd hg₁
  have hr := GlobalTheory.T.constantTangent_reduction_eq_origin E H D l Xo c O β Y b a χ W Λ g h z₀ ν Ξ v g₁ hd hg₁ hf
  obtain ⟨jL, hL⟩ := exists_chart W.P.U.LG.isLB
    ((show Sp (DualNumber ℂ⟦X⟧) ⟶ _ from v.left) (cpt (DualNumber ℂ⟦X⟧)))
  replace hL : ⊤ ≤ v.left ⁻¹ᵁ W.P.U.LG.L.U jL := (top_le_iff_cpt (A := DualNumber ℂ⟦X⟧) _ _).2 hL
  obtain ⟨jM, hM⟩ := exists_chart W.P.D.toPre.P.isLB
    ((show Sp (DualNumber ℂ⟦X⟧) ⟶ _ from g₁.b.left) (cpt (DualNumber ℂ⟦X⟧)))
  obtain ⟨j₀, h₀⟩ := exists_chart a.D₀.P.isLB ((show Sp (DualNumber ℂ) ⟶ _ from ν.b.left) (cpt (DualNumber ℂ)))
  have h₀' : ⊤ ≤ (show Sp (DualNumber ℂ) ⟶ _ from ν.b.left) ⁻¹ᵁ a.D₀.P.L.U j₀ := (top_le_iff_cpt _ _).2 h₀
  have hb : (show Sp (DualNumber ℂ⟦X⟧) ⟶ _ from g₁.b.left) ≫ W.φ = spMap constEps ≫ ν.b.left := (hg₁ 0).1 2
  have hj : ⊤ ≤ (show Sp (DualNumber ℂ⟦X⟧) ⟶ _ from g₁.b.left) ⁻¹ᵁ
      (LB.div (a.D₀.P.L.pull W.φ) W.P.D.toPre.P.L).U (fun _ => j₀, jM) :=
    (top_le_iff_cpt _ _).2 ⟨mem_pull.2 ((congrArg (fun q => q (cpt (DualNumber ℂ⟦X⟧)) ∈ a.D₀.P.L.U _) hb).mpr
      (FormalValue.top_le_comp h₀' _ trivial)), hM⟩
  obtain ⟨ω, hω⟩ := FormalValue.isUnit_valR (A := DualNumber ℂ⟦X⟧) g₁.b.left _ hj (W.w.s (fun _ => j₀, jM))
  have hz : ⊤ ≤ (Λ.u.ex 0).left ⁻¹ᵁ a.D₀.P.L.U j₀ := by
    have e := hd.1.1.trans (Λ.ex0_b (h.symm 0))
    rw [map_zero] at e
    exact (congrArg (fun q : Sp ℂ ⟶ _ => ⊤ ≤ q ⁻¹ᵁ a.D₀.P.L.U j₀) e).mp (FormalValue.top_le_comp h₀' _)
  let φ₁ := constEps (jet (fun u : Λ.A.V => Λ.u.fr j₀ u.2) (h.symm z₀))
  have hφ : IsUnit φ₁ := IsUnit.map _ (TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (by
    rw [fst_jet]; exact Ne.isUnit (Λ.u.fr_ne j₀ 0 hz)))
  let τ₁ : DualNumber ℂ⟦X⟧ := ω⁻¹.val * ((FormalValue.tau W.P.U.toUnifPre idealEps v.left jL jM).val * φ₁)
  have hτ : IsUnit τ₁ := (Units.isUnit _).mul ((Units.isUnit _).mul hφ)
  refine GlobalTheory.T.isTangent_genericFibre_of_thetaSections E H Λ.A W.t Φ W.P.U.LG (fun u => (Ξ.x u).left) Ξ.τ (h.symm z₀) v.left jL τ₁ ρ νK W.P.bundle hΦ hr hL
    hτ hρ hε hν₁ hν₂ fun j _ α th hth F hF => ?_
  obtain ⟨m, σ, hσ⟩ := GlobalTheory.T.exists_section_values_formalThetaSum h₁ h₂ E H D l Xo c O β Y b a χ W Λ Ξ j α th hth
  refine ⟨m, σ, fun u k hk => hσ u k hk, ?_⟩
  obtain ⟨N, n, r, s, hs, hsum⟩ := GlobalTheory.T.exists_pow_mul_eq_sum_constantExpansion h₁ E H D l Xo c O β Y b a χ W j σ NeZero.one_le
  choose x y hx hxv hy using fun i => GlobalTheory.T.tangentValue_eq_jet_constantExpansion h₁ h₂ E H D l Xo c O β Y b a χ W Λ Ξ g₁ v.left (h.symm z₀) jL jM ω φ₁ τ₁
    j (s i) hf hL (fun z hz => (hj hz).2) ω.isUnit hτ (Units.mul_inv_cancel_left _ _)
    (fun α s₀ f r jf jt hc hcoh => by
      choose k hk using fun i => exists_chart a.D₀.P.isLB
        ((show Sp (DualNumber ℂ) ⟶ _ from Out.DegPre.gtφT a.D₀ (epsR ℂ) ν.b (Λ.ε α) i) (cpt (DualNumber ℂ)))
      have ht : ⊤ ≤ LB.wchart a.D₀.P.L (Out.DegPre.gtφT a.D₀ (epsR ℂ) ν.b (Λ.ε α)) ![k 0, k 1, j₀, k 3] :=
        (top_le_iff_cpt (𝟙 (Sp (DualNumber ℂ)))
          (LB.wchart a.D₀.P.L (Out.DegPre.gtφT a.D₀ (epsR ℂ) ν.b (Λ.ε α)) ![k 0, k 1, j₀, k 3])).2
          (Set.mem_iInter.2 fun i => by
            fin_cases i
            exacts [hk 0, hk 1, h₀, hk 3])
      have e₁ := GlobalTheory.T.constantSection_mul_coord_dualNumberPoint E H D l Xo c O β Y b a χ W ν g₁ j _ s₀ f r jM jf jt _ hg₁ hc hcoh ht
      have e₂ := GlobalTheory.T.firstOrderJet_constSection_mul_coordinate E H D l c O β b a Λ g h z₀ ν j α s₀ _ hd.1 hd.2.1 ht
      rw [e₂, map_mul, map_pow] at e₁
      rw [hω]
      exact e₁.trans (_root_.mul_assoc _ _ _).symm) (hs i)
  have hJ := IsJet.sum Finset.univ fun i _ => (hx i).const_mul (r i)
  have hX : algebraMap ℂ⟦X⟧ ℂ⸨X⸩ PowerSeries.X ^ N = HahnSeries.single (N : ℤ) (1 : ℂ) := by
    rw [LaurentSeries.coe_algebraMap, PowerSeries.coe_X, HahnSeries.single_pow]; simp
  have e₀ : HahnSeries.single ((N : ℤ) + m) (1 : ℂ) =
      (HahnSeries.single (N : ℤ) (1 : ℂ) * HahnSeries.single (m : ℤ) (1 : ℂ) : ℂ⸨X⸩) := by
    rw [HahnSeries.single_mul_single, _root_.one_mul]
  have key := hJ.dualMapR_eq (N + m) (fun u => Λ.A.FSum j α th u) (fun u => by
    obtain ⟨k, hk, hu⟩ := exists_isUnit_tau Ξ u
    have e := congrArg (algebraMap ℂ⟦X⟧ ℂ⸨X⸩)
      (hsum ℂ⟦X⟧ (algebraMap ℂ⟦X⟧ ℂ⟦X⟧) (Ξ.x u).left k (Over.w (Ξ.x u)) hk)
    simp only [hxv _ u k hk, Algebra.algebraMap_self, RingHom.id_apply, ← _root_.mul_assoc, ← Finset.sum_mul] at e
    rw [map_mul, map_mul, map_pow, map_pow, hσ u k hk, hX] at e
    refine ((hu.map (algebraMap ℂ⟦X⟧ ℂ⸨X⸩)).pow j).mul_right_cancel (e.symm.trans ?_)
    rw [e₀]; ring) F hF
  have e := congrArg ρ (hsum _ (algebraMap ℂ⟦X⟧ (DualNumber ℂ⟦X⟧)) v.left jL (Over.w v) hL)
  simp only [hy, TrivSqZeroExt.algebraMap_eq_inl, ← _root_.mul_assoc, ← Finset.sum_mul] at e
  rw [← eq_dualMapR _ ρ hρ hε] at key
  rw [map_mul, map_mul, map_pow, map_pow, key, hρ, TrivSqZeroExt.inl_pow, hX, e₀, TrivSqZeroExt.inl_mul] at e
  have hu : IsUnit (TrivSqZeroExt.inl (HahnSeries.single (N : ℤ) (1 : ℂ)) : DualNumber ℂ⸨X⸩) :=
    TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (Ne.isUnit (by simp))
  refine hu.mul_left_cancel (e.trans ?_)
  ring

end GlobalTheory.ConstTan
end
end
