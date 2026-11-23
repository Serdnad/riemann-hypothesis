module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle488
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle501
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueFactorCompletedStalkOfMap
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle015
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GermEqZeroOfThickenings
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle091
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle011
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle027
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NVNeZero
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertNeighboursLiftsDoubleCosetTranslates
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.UnipotentAdelicQuotients.Bundle001
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle015
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.KerEntHyp
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle500
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle499
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle005
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle031
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction
import Formalism.LocalToGlobal.IndefiniteReal.RecTie
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Db GlobalTheory.Mem.Top.Bl.WitTr NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.Mem.Top.Bl.WitTr
open Formalism.MainNotions.G Formalism.UG Formalism.L2.Forms Formalism.L2.G
attribute [local instance] Formalism.BasicNotions.factResChar

section Gen

variable {D : D7} (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (h : D.what₂.Word → ℝ) {X : Formalism.L2.Herm.Herm0 D}



def cmpInS (I : Cmp.CmpIn D X) : Cmp.CmpIn (setDiv D N h) (DivTr.herm0S N h X) := { I with }



theorem cmpHyp0P_setDiv {T : ∀ u : D.what₂.Word, Forms0 D u} {Gt : GatTies D} {I : Cmp.CmpIn D X} (H : CmpHyp0P T Gt I) :
    CmpHyp0P (D := setDiv D N h) (fun u => DivTr.forms0S N h (T u)) (gatTr N h Gt) (cmpInS N h I) :=
  ⟨H.ex, H.evInj, H.ptEx, H.ptAll, H.chi, H.latM⟩

theorem stdB_setDiv {B : GL (Fin D.R.k) D.host.E} (hB : Cmp.StdB D B) : Cmp.StdB (setDiv D N h) B := hB



theorem cmpHyp_setDiv {T : ∀ u : D.what₂.Word, Forms0 D u} {Gt : GatTies D} {I : Cmp.CmpIn D X} (H : Cmp.CmpHyp T Gt I) :
    Cmp.CmpHyp (D := setDiv D N h) (fun u => DivTr.forms0S N h (T u)) (gatTr N h Gt) (cmpInS N h I) :=
  ⟨H.ex, H.uniq, H.pos, H.chi, H.li, H.latM⟩



theorem latCmpC_setDiv {T : ∀ u : D.what₂.Word, Forms0 D u} {Gt : GatTies D} {I : Cmp.CmpIn D X} (H : Cmp.CmpHyp T Gt I) :
    cmpTr N h (Cmp.latCmpC T Gt I H) =
      Cmp.latCmpC (D := setDiv D N h) (fun u => DivTr.forms0S N h (T u)) (gatTr N h Gt) (cmpInS N h I) (cmpHyp_setDiv N h H) := rfl



theorem sigma_setDiv {T : ∀ u : D.what₂.Word, Forms0 D u} {Gt : GatTies D} {I : Cmp.CmpIn D X} (H : Cmp.CmpHyp T Gt I)
    (H0 : Formalism.L2.Herm.Herm0 D) :
    (⟨setDiv D N h, gatTr N h Gt, cmpTr N h (Cmp.latCmpC T Gt I H), DivTr.herm0S N h H0, fun u => DivTr.forms0S N h (T u)⟩ :
      Σ D : D7, GatTies D × LatCmp D × Formalism.L2.Herm.Herm0 D × ∀ u, Forms0 D u) =
    ⟨setDiv D N h, gatTr N h Gt,
      Cmp.latCmpC (D := setDiv D N h) (fun u => DivTr.forms0S N h (T u)) (gatTr N h Gt) (cmpInS N h I) (cmpHyp_setDiv N h H),
      DivTr.herm0S N h H0, fun u => DivTr.forms0S N h (T u)⟩ := by
  rw [latCmpC_setDiv]

end Gen

attribute [local instance_reducible] tauRec hP frobSet lamRec packC locPackC recG gatTiesG extRec embRec cmpInC hermitianLevelZeroOfRecursion levTieG gatRecP_lev gatRec_lev gatRec_pos
  DivTr.herm0S DivTr.forms0S DivTr.atTTS cmpInS LocPack.posOK



theorem isRecG_setDiv : ∀ (sc : Scale) (D : D7) (Gt : GatTies D) (c : LatCmp D) (H : Formalism.L2.Herm.Herm0 D)
    (F : ∀ u, Formalism.L2.Forms.Forms0 D u) (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (h : D.what₂.Word → ℝ),
    IsRecG sc D Gt c H F → IsRecG sc (setDiv D N h) (gatTr N h Gt) (cmpTr N h c) (DivTr.herm0S N h H)
      (fun u => DivTr.forms0S N h (F u)) := by
  intro sc D Gt c H F N h hR
  obtain ⟨D0, Lc, I, ψ, hd, H0, hL, T, B, hBs, hB, iK, lam, hK, hPos, CH, eq⟩ := hR
  cases eq
  refine IsRecG.intro (setDiv D0 N h) Lc I ?a1 ?a2 ?a3 ?a4 ?a5 B ?a6 ?a7 ?a8 ?a9 ?a10 ?a11 ?a12 ?a13
  case a1 => with_reducible_and_instances exact ψ
  case a2 => with_reducible_and_instances exact hd
  case a3 => with_reducible_and_instances exact DivTr.herm0S N h H0
  case a4 => with_reducible_and_instances exact hL
  case a5 => with_reducible_and_instances exact fun u => DivTr.forms0S N h (T u)
  case a6 => with_reducible_and_instances exact stdB_setDiv N h hBs
  case a7 => with_reducible_and_instances exact hB
  case a8 => with_reducible_and_instances exact iK
  case a9 => with_reducible_and_instances exact lam
  case a10 => with_reducible_and_instances exact hK
  case a11 => with_reducible_and_instances exact hPos
  case a12 => with_reducible_and_instances exact cmpHyp0P_setDiv N h CH
  case a13 =>
    with_reducible_and_instances refine Eq.trans (sigma_setDiv N h _ H0) ?_
    with_reducible_and_instances exact Eq.refl _

end GlobalTheory.Mem.Top.Bl.WitTr
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR (pGl fGl)
open Formalism.L2.Pj GlobalTheory.RayEv GlobalTheory.FormalPoint GlobalTheory.AdicColimit GlobalTheory.RayEv.Transport
open GlobalTheory.TorusInvariance (wVal)
open GlobalTheory.EndRosati (push)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TransportLimit

theorem val_frame {X Y : Scheme.{0}} {L : LB X} {p : Y ⟶ X} (t : Frame L p) (ht : t.IsGen) {j₀ : L.ι}
    (h₀ : ⊤ ≤ LB.wchart L (K := PUnit) (fun _ => p) (fun _ => j₀)) {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z)
    {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    val t r z J = gm (r ≫ p) z _ (L.g (J (r ≫ p)) j₀) * gm r z ⊤ (res h₀ (t.s (fun _ => j₀))) := by
  refine (gen_trans ht r z (hJ.mem _ r) (h₀ (show r z ∈ (⊤ : Y.Opens) from trivial))).trans
    (congrArg₂ (· * ·) ?_ (gm_res r z h₀ (show r z ∈ (⊤ : Y.Opens) from trivial) _).symm)
  simp only [trF, Fintype.prod_unique, zpow_one]

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]

theorem gw_change (U : UnifPre I D A G) (e : ℕ) {Z : Scheme.{0}} (xe : Z ⟶ (thickObj R I e G).left) (z : Z)
    {p : Z ⟶ G.left} {q : Z ⟶ D.toPre.P.A.left} (hp : xe ≫ (fstG I e G).left = p)
    (hq : xe ≫ (U.gt e).pG.left = q) {j j' : D.toPre.P.L.ι} {k k' : U.LG.L.ι} (hj : q z ∈ D.toPre.P.L.U j)
    (hj' : q z ∈ D.toPre.P.L.U j') (hk : p z ∈ U.LG.L.U k) (hk' : p z ∈ U.LG.L.U k') :
    gw (U.w e) xe z j (fun _ => k) =
      gm q z _ (D.toPre.P.L.g j j') * (gm p z _ (U.LG.L.g k k'))⁻¹ * gw (U.w e) xe z j' (fun _ => k') := by
  subst hp hq
  have w := (isGen_iff _).1 (U.w_gen e) Z xe z j j' (fun _ => k) (fun _ => k') hj hj' (mem_pull.2 hk)
    (mem_pull.2 hk')
  rw [gm_pull_g _ _ xe z _ _ (mem_pull.2 hk) (mem_pull.2 hk')] at w
  exact w

theorem exists_limit_unit (U : UnifPre I D A G) {W : Type} [CommRing W] [IsLocalRing W] (φ : R →+* W)
    [IsAdicComplete (I.map φ) W] (x : Sp W ⟶ G.left) (hx : x ≫ G.hom = spMap φ) (b : Sp W ⟶ D.toPre.P.A.left)
    (hb : Lies U x b) {jL : U.LG.L.ι} {jM : D.toPre.P.L.ι} (hL : ⊤ ≤ x ⁻¹ᵁ U.LG.L.U jL)
    (hM : ⊤ ≤ b ⁻¹ᵁ D.toPre.P.L.U jM) :
    ∃ a : Γ(Sp W, ⊤)ˣ, ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Sp W) (xe : Z ⟶ (thickObj R I e G).left),
      xe ≫ (fstG I e G).left = r ≫ x → ∀ z : Z, gm r z ⊤ a * gw (U.w e) xe z jM (fun _ => jL) = 1 := by
  choose y hy using GlobalTheory.FormalValue.exists_lift_thick I G φ x hx
  have mL : ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Sp W) (xe : Z ⟶ (thickObj R I e G).left),
      xe ≫ (fstG I e G).left = r ≫ x → ∀ z : Z, (fstG I e G).left (xe z) ∈ U.LG.L.U jL := fun e Z r xe h z =>
    (congrArg (fun q => q z ∈ U.LG.L.U jL) h).mpr (hL (show r z ∈ (⊤ : (Sp W).Opens) from trivial))
  have mM : ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Sp W) (xe : Z ⟶ (thickObj R I e G).left),
      xe ≫ (fstG I e G).left = r ≫ x → ∀ z : Z, (U.gt e).pG.left (xe z) ∈ D.toPre.P.L.U jM := fun e Z r xe h z =>
    (congrArg (fun q => q z ∈ D.toPre.P.L.U jM) (hb e Z r xe h)).mpr
      (hM (show r z ∈ (⊤ : (Sp W).Opens) from trivial))
  let O : ∀ e, (thickObj R I e G).left.Opens := fun e =>
    (D.toPre.P.L.pull (U.gt e).pG.left).U (fun _ => jM) ⊓ (U.LG.L.pull (fstG I e G).left).U (fun _ => jL)
  let s : ∀ e, Γ((thickObj R I e G).left, O e)ˣ := fun e => (U.w e).s (fun _ => jM, fun _ => jL)
  have mO : ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Sp W) (xe : Z ⟶ (thickObj R I e G).left),
      xe ≫ (fstG I e G).left = r ≫ x → ∀ z : Z, xe z ∈ O e := fun e Z r xe h z =>
    ⟨mem_pull.2 (mM e Z r xe h z), mem_pull.2 (mL e Z r xe h z)⟩
  have ht : ∀ e, ⊤ ≤ y e ⁻¹ᵁ O e := fun e z _ => mO e _ _ _ (hy e) z
  have hc : ∀ e, Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (e + 1)))
      (valR (y (e + 1)) (O (e + 1)) (s (e + 1)).val) = valR (y e) (O e) (s e).val := fun e => by
    have := isLocalRing_quotient_pow (ne_top_of_isHausdorff (I.map φ)) e
    have := GlobalTheory.FormalValue.fstG_mono (I := I) (G := G) (e + 1)
    have e₁ : thickTrans W (I.map φ) e ≫ y (e + 1) = y e ≫ thickMap R I e G := by
      rw [← cancel_mono (fstG I (e + 1) G).left, Category.assoc, Category.assoc, hy,
        show thickMap R I e G ≫ (fstG I (e + 1) G).left = (fstG I e G).left from GlobalTheory.thickMap_comp_fGl I e G, hy,
        ← Category.assoc, thickTrans_comp]
    apply toStkA_injective
    refine (GlobalTheory.FormalValue.toStkA_map_valR _ _ _ _ (ht _) _).trans
      (Eq.trans ?_ (GlobalTheory.FormalValue.toStkA_valR_eq_gs _ _ _ (ht _) _).symm)
    refine (gs_unit _ _ _ (mO (e + 1) _ (thickTrans W (I.map φ) e ≫ thick W (I.map φ) (e + 1)) _ (by
      rw [Category.assoc, hy, Category.assoc]) _) _).trans (Eq.trans ?_ (gs_unit _ _ _ (mO e _ _ _ (hy e) _) _).symm)
    refine congrArg Units.val ((congrArg (fun q => gm q _ (O (e + 1)) (s (e + 1))) e₁).trans ?_)
    exact GlobalTheory.FormalValue.wv_comp_thickMap e (y e) _ jM jL (mM e _ _ _ (hy e) _) (mL e _ _ _ (hy e) _)
  obtain ⟨a, ha⟩ := GlobalTheory.FormalValue.exists_unit_limit (I.map φ) _ hc fun e =>
    GlobalTheory.FormalValue.isUnit_valR _ _ (ht e) _
  refine ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom.toMonoidHom a, fun e Z r xe h z => ?_⟩
  obtain ⟨ρ, rfl⟩ := GlobalTheory.NormGen.exists_factor I φ e r (xe ≫ (thickObj R I e G).hom) (by
    rw [← hx, ← Category.assoc r, ← h, Category.assoc, Category.assoc]
    exact congrArg (xe ≫ ·) pullback.condition.symm)
  have := GlobalTheory.FormalValue.fstG_mono (I := I) (G := G) e
  obtain rfl : xe = ρ ≫ y e := by
    rw [← cancel_mono (fstG I e G).left, h, Category.assoc, Category.assoc, hy]
  apply Units.ext
  have H := congrArg (fun t => gs ρ z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (W ⧸ I.map φ ^ (e + 1)))).inv.hom t)) (ha e)
  simp only [map_mul, map_one] at H
  rw [gs_mul ρ z ⊤ trivial, GlobalTheory.NormGen.gs_valR _ _ _ (ht e), gs_unit _ _ _ (mO e _ _ _ h z), gs_eq ρ z ⊤ trivial 1,
    map_one, map_one] at H
  refine Eq.trans (congrArg₂ (· * ·) ?_ rfl) H
  rw [← gs_unit _ z ⊤ trivial, ← GlobalTheory.NormGen.gs_valR ρ (thick W (I.map φ) e) ⊤ le_top]
  refine congrArg (fun t => gs ρ z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (W ⧸ I.map φ ^ (e + 1)))).inv.hom t)) ?_
  have k := GlobalTheory.FormalValue.valR_spMap (Ideal.Quotient.mk (I.map φ ^ (e + 1))) (𝟙 (Sp W)) ⊤ le_top
    ((Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom a.val)
  rw [GlobalTheory.NormGen.valR_id, Category.comp_id] at k
  exact k

theorem exists_frRel : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (W : Type) [CommRing W] [IsLocalRing W] (φ : R →+* W) [IsAdicComplete (I.map φ) W] (x' : Sp W ⟶ G.left), x' ≫ G.hom = spMap φ → ∀ b : Sp W ⟶ D.toPre.P.A.left, Lies U x' b → ∃ (g' : Frame U.LG.L x') (g : Frame D.toPre.P.L b), g'.IsGen ∧ g.IsGen ∧ FrRel U x' b g' g := by
  intro R _ _ I D A G _ _ U W _ _ φ _ x' hx b hb
  obtain ⟨jL, hjL⟩ := exists_chart U.LG.isLB (x' (cpt W))
  obtain ⟨jM, hjM⟩ := exists_chart D.toPre.P.isLB (b (cpt W))
  replace hjL := (top_le_iff_cpt (A := W) x' _).2 hjL
  replace hjM := (top_le_iff_cpt (A := W) b _).2 hjM
  obtain ⟨a, ha⟩ := exists_limit_unit U φ x' hx b hb hjL hjM
  obtain ⟨ν', hν'⟩ := ReciprocityTheory.ChartRestriction.G.DVR.exists_gen_of_local (V := W) U.LG.L U.LG.isLB (K := PUnit) (fun _ => x') (fun _ => 1)
  obtain ⟨ν, hν⟩ := ReciprocityTheory.ChartRestriction.G.DVR.exists_gen_of_local (V := W) D.toPre.P.L D.toPre.P.isLB (K := PUnit) (fun _ => b) (fun _ => 1)
  have tL : ⊤ ≤ LB.wchart U.LG.L (K := PUnit) (fun _ => x') (fun _ => jL) := fun y _ =>
    Set.mem_iInter.2 fun _ => hjL (show y ∈ (⊤ : (Sp W).Opens) from trivial)
  have tM : ⊤ ≤ LB.wchart D.toPre.P.L (K := PUnit) (fun _ => b) (fun _ => jM) := fun y _ =>
    Set.mem_iInter.2 fun _ => hjM (show y ∈ (⊤ : (Sp W).Opens) from trivial)
  refine ⟨GlobalTheory.UU.scaleGen (res tL (ν'.s fun _ => jL))⁻¹ ν', GlobalTheory.UU.scaleGen (a⁻¹ * (res tM (ν.s fun _ => jM))⁻¹) ν,
    GlobalTheory.UU.scaleGen_isGen _ hν', GlobalTheory.UU.scaleGen_isGen _ hν, ?_⟩
  intro e Z r y hy z JM JL hJM hJL
  have hyb := hb e Z r y hy
  have m : ∀ {X : Scheme.{0}} {f : Sp W ⟶ X} {O : X.Opens}, ⊤ ≤ f ⁻¹ᵁ O → (r ≫ f) z ∈ O := fun h =>
    h (show r z ∈ (⊤ : (Sp W).Opens) from trivial)
  have v₁ := GlobalTheory.UU.val_scaleGen (res tL (ν'.s fun _ => jL))⁻¹ ν' r hJL
  rw [val_frame ν' hν' tL r z hJL] at v₁
  have v₂ := GlobalTheory.UU.val_scaleGen (a⁻¹ * (res tM (ν.s fun _ => jM))⁻¹) ν r hJM
  rw [val_frame ν hν tM r z hJM] at v₂
  have w₁ : wVal U e z JM JL y = gm (r ≫ b) z _ (D.toPre.P.L.g (JM (r ≫ b)) jM) *
      (gm (r ≫ x') z _ (U.LG.L.g (JL (r ≫ x')) jL))⁻¹ * gw (U.w e) y z jM (fun _ => jL) :=
    (congrArg₂ (fun j k => gw (U.w e) y z (JM j) (fun _ => JL k)) hyb hy).trans
      (gw_change U e y z hy hyb (hJM _) (m hjM) (hJL _) (m hjL))
  rw [eq_inv_of_mul_eq_one_right (ha e Z r y hy z)] at w₁
  rw [v₁, v₂, w₁]
  simp only [map_mul, map_inv]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end GlobalTheory.TransportLimit
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR (pGl fGl)
open Formalism.L2.Pj GlobalTheory.RayEv GlobalTheory.FormalPoint GlobalTheory.AdicColimit GlobalTheory.RayEv.Transport
open GlobalTheory.TorusInvariance (wVal)
open GlobalTheory.EndRosati (push)
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RayEv.Transport

section Helpers

variable {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K]

theorem exists_fn_of_formal (hL : L.IsLB) {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (hF : ∀ (U : Type) [CommGroup U] (h : (Y ⟶ X) → U), ∏ k, h (φ k) ^ ε k = 1)
    (s : LB.Sec (LB.LinComb L φ ε)) :
    ∃ a : Γ(Y, ⊤), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J → sval s r z J = gs r z ⊤ a := by
  obtain ⟨t, hv⟩ := exists_sec hL (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim)
    (fun U _ h => (hF U h).trans (Fintype.prod_empty _).symm) s
  have le : (⊤ : Y.Opens) ≤ LB.wchart L (PEmpty.elim : PEmpty → (Y ⟶ X)) PEmpty.elim := fun _ _ =>
    Set.mem_iInter.2 fun k => k.elim
  refine ⟨(Y.presheaf.map (homOfLE le).op).hom (t.f PEmpty.elim), fun Z r z J hJ => ?_⟩
  rw [← hv Z r z J hJ, sval_of t r z J PEmpty.elim (fun k => k.elim)]
  exact (gs_res r z le trivial _).symm

theorem mem_pow_of_gs {W : Type} [CommRing W] (J : Ideal W) (n : ℕ) (a : W)
    (h : ∀ z, gs (adicLevelι J n) z ⊤ (toΓ W a) = 0) : a ∈ J ^ n := by
  have h1 : (adicLevelι J n).appTop.hom (toΓ W a) = 0 := fn_ext (V := ⊤) fun z _ =>
    (gs_pull (𝟙 _) (adicLevelι J n) z ⊤ trivial _).trans (by
      rw [Category.id_comp, h z]; exact (DVR.gs_zero (𝟙 _) z ⊤ trivial).symm)
  have h2 := congrArg (fun q => q.hom (toΓ W a))
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (Ideal.Quotient.mk (J ^ n))))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h2
  rw [h1, map_zero] at h2
  have h3 : (Scheme.ΓSpecIso (CommRingCat.of W)).hom.hom (toΓ W a) = a := by
    simp only [toΓ]; exact Iso.inv_hom_id_apply _ _
  rw [h3] at h2
  exact Ideal.Quotient.eq_zero_iff_mem.1 h2.symm

theorem toΓ_hom {W : Type} [CommRing W] (a : Γ(Sp W, ⊤)) :
    toΓ W ((Scheme.ΓSpecIso (CommRingCat.of W)).hom.hom a) = a := by
  simp only [toΓ]; exact Iso.hom_inv_id_apply _ _

end Helpers

theorem exists_adic_expansion : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (W : Type) [CommRing W] (φ : R →+* W) (ξ : GtPt D.toPre (Over.mk (spMap φ))) (x' : Over.mk (spMap φ) ⟶ G), IsPointOf U ξ x' → ∀ (b : Sp W ⟶ D.toPre.P.A.left), ξ.b.left = b → ∀ (g' : Frame U.LG.L (Y := Sp W) x'.left) (g : Frame D.toPre.P.L b), g'.IsGen → g.IsGen → FrRel U (T := Sp W) x'.left b g' g → ∀ (k : ℕ) (σ : H0 U.LG.L k) (F : ∀ α, D.toPre.SecB k α), (∀ e, U.ExpandsAt e k σ F) → ∃ (s : W) (t : D.toPre.X → W), (∀ (Z : Scheme.{0}) (r : Z ⟶ Sp W) (z : Z) (JL), Good U.LG.L z JL → sval σ (r ≫ x'.left) z JL = gs r z ⊤ (toΓ W s) * (val g' r z JL ^ k).val) ∧ (∀ (α : D.toPre.X) (Z : Scheme.{0}) (r : Z ⟶ Sp W) (z : Z) (JM), Good D.toPre.P.L z JM → sval (F α) (r ≫ b) z JM * (val (ξ.s α) r z JM).val = gs r z ⊤ (toΓ W (t α)) * (val g r z JM ^ k).val) ∧ ∀ e : ℕ, ∃ S : Finset D.toPre.X, (∀ α ∉ S, t α ∈ I.map φ ^ (e + 1)) ∧ s - ∑ α ∈ S, t α ∈ I.map φ ^ (e + 1) := by
  intro R _ _ I D A G _ _ U W _ φ ξ x' hx b hb g' g hg' hg hfr k σ F hexp
  subst hb
  have hL := U.LG.isLB
  have hM := D.toPre.P.isLB

  obtain ⟨a, ha⟩ := exists_fn_of_formal hL
    (φ := Sum.elim (fun _ : Fin 1 => x'.left ≫ 𝟙 G.left) (fun _ : PUnit.{1} => x'.left))
    (ε := Sum.elim (fun _ => (k : ℤ)) (fun _ => -((k : ℤ) * 1)))
    (fun U _ h => by simp [Fintype.prod_sum_type])
    (pullMulSec σ x'.left (LB.invGen U.LG.L _ _ (GeneratorPullback.powGen U.LG.L _ _ g' k))
      (DVR.invGen_isGen _ _ _ _ (DVR.powGen_isGen _ _ _ _ hg' k)))
  have h1 : ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp W) (z : Z) (JL), Good U.LG.L z JL →
      sval σ (r ≫ x'.left) z JL = gs r z ⊤ a * (val g' r z JL ^ k).val := by
    intro Z r z JL hJL
    have e₁ := (ha Z r z JL hJL).symm.trans (sval_pullMulSec σ x'.left _ _ r z hJL)
    rw [val_inv, show val (GeneratorPullback.powGen U.LG.L _ _ g' k) r z JL = val g' r z JL ^ k from map_pow _ _ _] at e₁
    rw [e₁, _root_.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, _root_.mul_one]

  have ht : ∀ α, ∃ c : Γ(Sp W, ⊤), ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp W) (z : Z) (JM), Good D.toPre.P.L z JM →
      sval (F α) (r ≫ ξ.b.left) z JM * (val (ξ.s α) r z JM).val = gs r z ⊤ c * (val g r z JM ^ k).val := by
    intro α
    obtain ⟨c, hc⟩ := exists_fn_of_formal hM
      (φ := Sum.elim (fun i => ξ.b.left ≫ D.toPre.famφB α i)
        (Sum.elim (DegPre.gtφT D.toPre (Over.mk (spMap φ)) ξ.b α) (fun _ : PUnit.{1} => ξ.b.left)))
      (ε := Sum.elim (DegPre.famε k) (Sum.elim DegPre.gtε (fun _ => -((k : ℤ) * 1))))
      (fun U _ h => by
        have e := GlobalTheory.ConstTerm.prod_factors (fun i => h (ξ.b.left ≫ D.toPre.famφB α i)) k
        have e₀ : ∀ i, h (DegPre.gtφT D.toPre (Over.mk (spMap φ)) ξ.b α i) =
            ![h (ξ.b.left ≫ D.toPre.famφB α 1), h (ξ.b.left ≫ D.toPre.famφB α 2),
              h (ξ.b.left ≫ D.toPre.famφB α 0), h (ξ.b.left ≫ D.toPre.famφB α 3)] i := by
          intro i
          fin_cases i <;> simp [GlobalTheory.ConstTerm.comp_famφB]
        simp only [← e₀] at e
        have e₁ : ξ.b.left ≫ D.toPre.famφB α 0 = ξ.b.left := Category.comp_id _
        rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
        simp only [Sum.elim_inl, Sum.elim_inr]
        rw [← _root_.mul_assoc, e, e₁]
        simp)
      (pullMulSec (F α) ξ.b.left
        (LB.mulGen D.toPre.P.L _ _ _ _ (ξ.s α) (LB.invGen D.toPre.P.L _ _ (GeneratorPullback.powGen D.toPre.P.L _ _ g k)))
        (DVR.mulGen_isGen _ _ _ _ _ _ _ (ξ.isGen α)
          (DVR.invGen_isGen _ _ _ _ (DVR.powGen_isGen _ _ _ _ hg k))))
    refine ⟨c, fun Z r z JM hJM => ?_⟩
    have e₁ := (hc Z r z JM hJM).symm.trans (sval_pullMulSec (F α) ξ.b.left _ _ r z hJM)
    rw [val_mul hJM, val_inv,
      show val (GeneratorPullback.powGen D.toPre.P.L _ _ g k) r z JM = val g r z JM ^ k from map_pow _ _ _] at e₁
    rw [e₁, Units.val_mul, _root_.mul_assoc, _root_.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, _root_.mul_one]
  choose c hc using ht
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of W)).hom.hom a,
    fun α => (Scheme.ΓSpecIso (CommRingCat.of W)).hom.hom (c α), fun Z r z JL hJL => ?_,
    fun α Z r z JM hJM => ?_, fun e => ?_⟩
  · rw [toΓ_hom]; exact h1 Z r z JL hJL
  · rw [toΓ_hom]; exact hc α Z r z JM hJM
  · set J := I.map φ
    obtain ⟨S, hS⟩ := DVR.expandsAt_val U e k σ F (hexp e)
    have hy₁ : reduction I x' e ≫ fGl I G e = adicLevelι J (e + 1) ≫ x'.left := reduction_fstG I x' e
    obtain ⟨hy₂, hy₃⟩ := (hasCoords_iff U e ξ _ _).1 (hx e _ (adicLevelι J (e + 1)) (reduction I x' e) hy₁)
    have gM : ∀ z : Sp (W ⧸ J ^ (e + 1)), ∃ JM, Good D.toPre.P.L z JM := fun z => by
      choose C hC using fun ψ : Sp (W ⧸ J ^ (e + 1)) ⟶ D.toPre.P.A.left => exists_chart hM (ψ z)
      exact ⟨C, hC⟩
    have gL : ∀ z : Sp (W ⧸ J ^ (e + 1)), ∃ JL, Good U.LG.L z JL := fun z => by
      choose C hC using fun ψ : Sp (W ⧸ J ^ (e + 1)) ⟶ G.left => exists_chart hL (ψ z)
      exact ⟨C, hC⟩
    refine ⟨S, fun α hα => mem_pow_of_gs J (e + 1) _ fun z => ?_, mem_pow_of_gs J (e + 1) _ fun z => ?_⟩
    · obtain ⟨JM, hJM⟩ := gM z
      have h0 := (hS _ (reduction I x' e) z JM hJM).1 α hα
      rw [hy₂] at h0
      have h2 := hc α _ (adicLevelι J (e + 1)) z JM hJM
      rw [h0, zero_mul] at h2
      rw [toΓ_hom]
      exact (Units.mul_left_eq_zero _).1 h2.symm
    · obtain ⟨JM, hJM⟩ := gM z
      obtain ⟨JL, hJL⟩ := gL z
      have hE := (hS _ (reduction I x' e) z JM hJM).2 (JL (reduction I x' e ≫ fGl I G e)) (hJL _)
      have hw := hfr e _ (adicLevelι J (e + 1)) (reduction I x' e) hy₁ z JM JL hJM hJL
      have hsv : DVR.sv U k σ (reduction I x' e ≫ fGl I G e) z (JL (reduction I x' e ≫ fGl I G e)) =
          sval σ (adicLevelι J (e + 1) ≫ x'.left) z JL := by
        rw [← hy₁]; exact (sval_of σ _ z JL _ fun _ => by rw [Category.comp_id]).symm
      have hwv : DVR.wv U e (reduction I x' e) z (JM (reduction I x' e ≫ pGl U e))
          (JL (reduction I x' e ≫ fGl I G e)) = wVal U e z JM JL (reduction I x' e) := rfl
      have hterm : ∀ α ∈ S, sval (F α) (reduction I x' e ≫ pGl U e) z JM *
          (val (DVR.tG U e α) (reduction I x' e) z JM).val =
          gs (adicLevelι J (e + 1)) z ⊤ (c α) * (val g (adicLevelι J (e + 1)) z JM ^ k).val := fun α _ => by
        rw [hy₃ α z JM hJM, hy₂]; exact hc α _ _ z JM hJM
      rw [hsv, h1 _ _ z JL hJL, Finset.sum_congr rfl hterm, ← Finset.sum_mul, hwv, hw, mul_pow,
        Units.val_mul] at hE
      have hfin : gs (adicLevelι J (e + 1)) z ⊤ a = ∑ α ∈ S, gs (adicLevelι J (e + 1)) z ⊤ (c α) := by
        refine (Units.mul_left_inj (wVal U e z JM JL (reduction I x' e) ^ k *
          val g' (adicLevelι J (e + 1)) z JL ^ k)).1 ?_
        rw [Units.val_mul]
        linear_combination hE
      have gsub : ∀ x y : Γ(Sp W, ⊤), gs (adicLevelι J (e + 1)) z ⊤ (x - y) =
          gs (adicLevelι J (e + 1)) z ⊤ x - gs (adicLevelι J (e + 1)) z ⊤ y := fun x y => by
        simp only [gs_eq _ z ⊤ trivial, map_sub]

      rw [map_sub, map_sum, toΓ_hom, gsub, DVR.gs_fsum _ z ⊤ trivial, hfin, sub_eq_zero]
      exact Finset.sum_congr rfl fun α _ => by rw [toΓ_hom]

end GlobalTheory.RayEv.Transport
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

theorem _root_.GlobalTheory.T.inertNeighbours_lifts_doubleCoset_translates : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → ∀ (cV : ∀ i, CoefA (Vc X.toD7 i)) (i : Fin X.toD7.R.m) (t : TupU I U) (A k : GL (Fin X.B.R.nV) (LiftBrg.EA X)), LiftBrg.FrameOK X I U i t A k →
    ∀ q : ↑((famR X I hX U Xg tr).okI t) × List ℕ, Formalism.L2.Col.InertTypeOk (Vc X.toD7 i).rank q.2 →
    ∃ (x : Bridge.Gf (Vc X.toD7 i)) (R : Finset (Bridge.Gf (Vc X.toD7 i))),
      IsLabElt (Vc X.toD7 i) (q.1.1 : PlI X.B px).1 (labIn (Vc X.toD7 i).rank q.2) x ∧
      (∀ a ∈ R, IsLocElt (Vc X.toD7 i) (q.1.1 : PlI X.B px).1 a) ∧
      Bridge.IsDC (LiftBrg.envL X I hX U Xg tr L cV i t).lev.J x R ∧
      ∀ (M : Type) [AddCommMonoid M] (ψ : Formalism.L2.Col.DecoSet (E := X.toD7.host.E) (n := X.B.R.nV) (ST := ∅) (SG := LiftBrg.sgL X I U t) → M)
        (g : Bridge.Gf (Vc X.toD7 i)),
        ∑ a ∈ R, ψ (LiftBrg.ptL X I U i t A k (g * a)) =
          ∑ e ∈ (LiftBrg.ptL X I U i t A k g).inertNb ((q.1.1 : PlI X.B px).1).asIdeal q.2, ψ e := by
  first | exact @GlobalTheory.InertNbr.inert_neighbours | exact GlobalTheory.InertNbr.inert_neighbours | (intros; apply GlobalTheory.InertNbr.inert_neighbours <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.schrodingerIntertwiner_injective_schwartzBruhat : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (e : AE D) (f₀ Φ : WO S T → ℂ) (Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)), IsStdChar D ψ (-1) → IsSelfDualC S ΛS → IsSelfDualC T ΛT → e * e = e → e * cA D e = 0 → infPart D e = 0 → IsPlaceModel ψ (symplO S T) (heisO ψ S T) e (latO S T ΛS ΛT fun _ => True) 1 f₀ Tm → f₀ ≠ 0 → IsSBHalf e (latO S T ΛS ΛT fun _ => True) Φ → Φ ≠ 0 → Tm Φ ≠ 0 := by
  first | exact @GlobalTheory.PlaceModelInj.placeModel_ne_zero | exact GlobalTheory.PlaceModelInj.placeModel_ne_zero | (intros; apply GlobalTheory.PlaceModelInj.placeModel_ne_zero <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.lattice_iff_integralWeyl_coordinates : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (Y : DivX (I.rec7 l Z)) (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)) (Pl : Examples₂.EntPl (I.rec7 l Z)) (Bs : PlaceMatrixFamily (I.rec7 l Z)), I.QpIs Y.Qp → I.StdO l Z Y.Qp O → BasOk Pl O Bs → (∀ u a w, LevFree Y u a w → ∀ i, i ≤ B.R.m → ∀ c τ j k, ∃ x : (I.rec7 l Z).what₂.LL, Bs u a w i c τ j k = Pl.iL w x) → ∀ (u : B.Word) (μ : I.ι) (w : (I.rec7 l Z).what₂.places.Pl), LevFree Y u μ w → ∀ (i : ℕ) (hi : i < B.R.m) (eY : (I.chain l u μ).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi.le), I.IdY l Z u μ i hi.le eY → ∀ (c : (I.stp u μ i).Cl) (f : (I.chain l u μ).Y i → ℂ), (∃ P ∈ Formalism.L2.Forms.RatSpan (I.rec7 l Z) ((I.fm l u μ).lam i), ∀ z, f z = fnOf (gramC (gramN (I.rec7 l Z) i hi.le) (embT (I.rec7 l Z))) (shiftOf (lamTG (I.fm l u μ) i)) 1 P (eY z)) → ∀ Bm : GL (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E, Formalism.L2.Forms.IsLocBasis ((I.rec7 l Z).what₂.places.resChar w) (((I.stp u μ i).rep c).1.1.deco.1.N : Set (Sp B.fields.E (B.R.N i))) Bm →  ∀ v : ValQ O u μ i, evC O u μ i v = f → ((∃ P ∈ Formalism.L2.Forms.IntSpan (I.rec7 l Z) w ((I.fm l u μ).lam i), ∀ z, f z = fnOf (gramC (gramN (I.rec7 l Z) i hi.le) (embT (I.rec7 l Z))) (shiftOf (lamTG (I.fm l u μ) i)) (atInf (embT (I.rec7 l Z)) ((Bm⁻¹ : GL (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E) : Matrix (Fin ((I.rec7 l Z).R.N i)) (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E)) P (eY z)) ↔ srcFun Pl Bs u μ w i c (secC O u μ i v) ∈ WeylLatticeDuality.DelW ((I.rec7 l Z).what₂.places.resChar w) (I.rec7 l Z).what₂.Tau ((I.rec7 l Z).R.N i) (nuT (I.rec7 l Z) u i)) := by
  first | exact @GlobalTheory.IntegralityCompare.lattice_iff_weyl | exact GlobalTheory.IntegralityCompare.lattice_iff_weyl | (intros; apply GlobalTheory.IntegralityCompare.lattice_iff_weyl <;> assumption)
end
