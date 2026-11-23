module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle228
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualMapCompDualMap
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2294
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle681
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1439
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1848
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1586
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1438
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1634
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2295
public import Formalism.LocalToGlobal.IndefiniteReal.DatumF
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2296
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle017
public import Development.WeilBound.CoreStatements.PublishedTheorems.NefNumerics.NefRiemannRoch.NefLineBundleNumericalTheoremsProof
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
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2272
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.Heat GlobalTheory.FormalOrigin
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CoordsOrigin

theorem _root_.GlobalTheory.T.originLocalRing_noetherian_free_unitSectionConormal : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (G : Over (Sp R)) [GrpObj G], Smooth G.hom → IsNoetherianRing (G.left.presheaf.stalk (origin G)) ∧ (letI : Algebra R (G.left.presheaf.stalk (origin G)) := (constO G).toAlgebra; Module.Free R (RingHom.ker (evO G)).Cotangent ∧ Module.Finite R (RingHom.ker (evO G)).Cotangent) := by
  first | exact @GlobalTheory.CoordsOrigin.noetherian_free_cotangent | exact GlobalTheory.CoordsOrigin.noetherian_free_cotangent | (intros; apply GlobalTheory.CoordsOrigin.noetherian_free_cotangent <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechKS
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CechKS

section Val

variable {R : Type} [CommRing R] {X : Scheme.{0}} {s : X ⟶ Sp R}

theorem sec_sub_id_eq_val (E : SqExt R) {x : Sp E.B ⟶ X} (hx : x ≫ s = spMap (algebraMap R E.B))
    (y : Sp E.C ⟶ X) (hy : y ≫ s = spMap (algebraMap R E.C))
    (h : spMap ((E.π : E.C →+* E.B).comp (AlgHom.id R E.C : E.C →+* E.C)) ≫ y = x) (f : Z1 (O (dp0 R) s)) :
    ev f (E.secHom hx E.i E.π_i) - ev f (Thick.trivHom (hx := hy) (T := E.thick x hx) (AlgHom.id R E.C) h) =
      E.val y hy f := by
  subst h
  rfl

theorem val_congr (E : SqExt R) {y y' : Sp E.C ⟶ X} (e : y = y') (hy : y ≫ s = spMap (algebraMap R E.C))
    (hy' : y' ≫ s = spMap (algebraMap R E.C)) (f : Z1 (O (dp0 R) s)) : E.val y hy f = E.val y' hy' f := by
  subst e
  rfl

end Val

variable {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A]

theorem ev_sec_sub_ev_tan_eq_val (P : GPt A) {v : epsR K ⟶ A} (hv : IsTangent v)
    (f : Z1 (O (dp0 K) (A.hom ≫ 𝟙 (Sp K)))) :
    ev f P.sec - ev f (P.tan hv) = (SqExt.ofModule K P.B P.B).val (P.trx v) (P.tr v).w f :=
  sec_sub_id_eq_val (SqExt.ofModule K P.B P.B) P.w (P.trx v) (P.tr v).w ((P.isTransl_trx v).red hv) f

theorem dualMap_id (B : Type) [CommRing B] : dualMap (RingHom.id B) = RingHom.id (DualNumber B) :=
  RingHom.ext fun c ↦ by ext <;> simp [dualMap]

@[reducible] def Pt.origin (A : Over (Sp K)) [GrpObj A] : GPt A where
  B := K
  x := η[A].left
  w := by
    rw [Category.comp_id, Over.w η[A]]
    exact (Cris.spMap_id K).symm

theorem isTransl_origin (v : epsR K ⟶ A) : IsTransl (algebraMap K K) η[A].left v v.left := by
  refine ⟨1, Over.homMk (spMap (dualMap (algebraMap K K)) ≫ v.left) (by
      rw [Category.assoc, Over.w v]
      change spMap _ ≫ spMap _ = spMap _
      rw [← Cris.spMap_comp, dualMap_comp_algebraMap]), rfl, rfl, ?_⟩
  rw [_root_.one_mul]
  change spMap (dualMap (RingHom.id K)) ≫ v.left = v.left
  rw [dualMap_id, Cris.spMap_id, Category.id_comp]

theorem origin_trx (v : epsR K ⟶ A) : (Pt.origin A).trx v = v.left :=
  ((Pt.origin A).isTransl_trx v).unique (isTransl_origin v)

end GlobalTheory.CechKS

namespace GlobalTheory.CechKS

variable {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A]

def tanFn (v : epsR K ⟶ A) (f : Z1 (O (dp0 K) (A.hom ≫ 𝟙 (Sp K)))) : PtFn (A.hom ≫ 𝟙 (Sp K)) :=
  fun P ↦ ((SqExt.ofModule K P.B P.B).val (P.trx v) (P.tr v).w f).snd

theorem isNat_tanFn (v : epsR K ⟶ A) (ω : Form (A.hom ≫ 𝟙 (Sp K))) : IsNat ⊤ (tanFn v ω.1) := by
  intro P Q φ _
  have := (SqExt.ofModule K P.B P.B).val_map (SqExt.ofModule K Q.B Q.B) (dualAlg φ.ρ) φ.ρ
    (fun c ↦ (fst_dualAlg φ.ρ c).symm) (fun b ↦ by ext <;> simp) (P.trx v) (P.tr v).w (Q.trx v) (Q.tr v).w
    (φ.tr v).pt ω
  simp only [tanFn]
  rw [this, snd_dualAlg]

theorem tanFn_eq (hA : IsAbelianScheme A) (v : epsR K ⟶ A) (ω : Form (A.hom ≫ 𝟙 (Sp K))) (P : GPt A) :
    tanFn v ω.1 P = algebraMap K P.B (tanVal v ω) := by
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_section_of_natural_on_algebraPoints_of_cover K A.left (A.hom ≫ 𝟙 (Sp K)) Unit (fun _ ↦ ⊤) ⊤ (fun _ ↦ le_rfl)
    (le_iSup_of_le () le_rfl) (tanFn v ω.1) (fun _ ↦ isNat_tanFn v ω)
  obtain ⟨g₀, rfl⟩ := (GlobalTheory.globalFns_holds (Sp K) A hA).2 g
  have key : ∀ Q : GPt A, tanFn v ω.1 Q = algebraMap K Q.B (valR (𝟙 (Sp K)) ⊤ g₀) := by
    intro Q
    rw [hg () Q (fun _ _ ↦ trivial)]
    have e1 : valR Q.x ⊤ (A.hom.appTop.hom g₀) = valR (Q.x ≫ A.hom) ⊤ g₀ := by
      rw [GlobalTheory.Points.valR_comp Q.x A.hom ⊤ g₀]; rfl
    have e2 : Q.x ≫ A.hom = spMap (algebraMap K Q.B) ≫ 𝟙 (Sp K) :=
      (Category.comp_id (Q.x ≫ A.hom)).symm.trans ((Category.assoc _ _ _).trans (Q.w.trans (Category.comp_id _).symm))
    rw [e1, e2, GlobalTheory.Points.valR_spMap_comp _ _ _ (GlobalTheory.Points.le_preimage_top _)]
  have h0 : tanFn v ω.1 (Pt.origin A) = tanVal v ω := by
    simp only [tanFn]
    rw [tanVal_apply]
    exact congrArg TrivSqZeroExt.snd (val_congr (SqExt.dual K) (origin_trx v) _ _ ω.1)
  rw [key, ← h0, key]
  rfl

theorem ev_sec_sub_ev_tan : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A →
    ∀ (v : epsR K ⟶ A) (hv : IsTangent v) (ω : Form (A.hom ≫ 𝟙 (Sp K))) (P : GPt A),
    ev ω.1 P.sec - ev ω.1 (P.tan hv) = (TrivSqZeroExt.inr (algebraMap K P.B (tanVal v ω)) : DualNumber P.B) := by
  intro K _ A _ hA v hv ω P
  rw [ev_sec_sub_ev_tan_eq_val P hv ω.1]
  ext
  · rw [TrivSqZeroExt.fst_inr]; exact SqExt.π_val (SqExt.ofModule K P.B P.B) _ _ ω
  · exact tanFn_eq hA v ω P

end GlobalTheory.CechKS
end
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechKS
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CechKS

theorem Pt.nonempty_affHom_of_in {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) (U : X.affineOpens) (P : Pt s) (h : P.In U.1) :
    Nonempty ((Pt.aff s U).Hom P) := by
  let φ := GlobalTheory.Points.valMap P.x U.1 h
  have hc : ∀ r : R, φ.hom (algebraMap R (CechDR.Sec s U.1) r) = algebraMap R P.B r := by
    intro r
    change φ.hom ((s.appLE ⊤ U.1 le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) = _
    rw [← GlobalTheory.Points.valR_eq P.x U.1 h, GlobalTheory.Points.valR_appLE P.x s le_top h, P.w,
      GlobalTheory.Points.valR_specMap]
    rfl
  refine ⟨⟨{ φ.hom with commutes' := hc }, ?_⟩⟩
  exact GlobalTheory.Points.specMap_valMap_fromSpec U.2 P.x h

theorem Pt.affHom_ρ_eq_valR {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) (U : X.affineOpens) (P : Pt s)
    (a : (Pt.aff s U).Hom P) (b : Γ(X, U.1)) : a.ρ b = valR P.x U.1 b := by
  have hpre : ⊤ ≤ (CechDR.affPt s U) ⁻¹ᵁ U.1 := U.2.fromSpec_preimage_self.ge
  have hid : valR (CechDR.affPt s U) U.1 b = b := by
    rw [GlobalTheory.Points.valR_eq _ _ hpre]
    have h1 : Spec.map (𝟙 Γ(X, U.1)) ≫ U.2.fromSpec = CechDR.affPt s U := by
      rw [Spec.map_id, Category.id_comp]; rfl
    have h2 := GlobalTheory.Points.valMap_specMap_fromSpec U.2 (𝟙 Γ(X, U.1)) (h1 ▸ hpre)
    have h3 : GlobalTheory.Points.valMap (CechDR.affPt s U) U.1 hpre = 𝟙 _ := by
      have key : ∀ (x : Spec Γ(X, U.1) ⟶ X) (hx : x = CechDR.affPt s U) (h : ⊤ ≤ x ⁻¹ᵁ U.1),
          GlobalTheory.Points.valMap x U.1 h = GlobalTheory.Points.valMap (CechDR.affPt s U) U.1 hpre := by
        rintro _ rfl _; rfl
      exact (key _ h1 _).symm.trans h2
    rw [h3]; rfl
  rw [← a.pt, GlobalTheory.Points.valR_spMap_comp _ _ _ hpre, hid]
  rfl

theorem eq_of_valR_eq_on_cover {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) {J : Type} (W : J → X.Opens)
    (hW : ⨆ j, W j = ⊤) (V : X.Opens) (f g : Γ(X, V))
    (h : ∀ (P : Pt s) (j : J), P.In V → P.In (W j) → valR P.x V f = valR P.x V g) : f = g := by
  refine TopCat.Presheaf.section_ext X.sheaf V f g fun x hx ↦ ?_
  have hxW : x ∈ ⨆ j, W j := by rw [hW]; trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hxW
  obtain ⟨U', hU', hxU', hsub⟩ := exists_isAffineOpen_mem_and_subset (U := V ⊓ W j) ⟨hx, hj⟩
  have hle : U' ≤ V ⊓ W j := hsub
  have hleV : U' ≤ V := hle.trans inf_le_left
  let Ua : X.affineOpens := ⟨U', hU'⟩
  have hPU : (Pt.aff s Ua).In U' := hU'.fromSpec_preimage_self.ge
  have hv := h (Pt.aff s Ua) j (hPU.mono hleV) (hPU.mono (hle.trans inf_le_right))
  have key : ∀ b : Γ(X, V), valR (Pt.aff s Ua).x V b = (X.presheaf.map (homOfLE hleV).op).hom b := by
    intro b
    rw [← GlobalTheory.Points.valR_res (Pt.aff s Ua).x hleV hPU b]
    exact (Pt.affHom_ρ_eq_valR s Ua (Pt.aff s Ua) (Pt.Hom.id _) _).symm
  rw [key, key] at hv
  have := congrArg (X.presheaf.germ U' x hxU') hv
  rwa [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply] at this

theorem Pt.affHom_subsingleton {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) (U : X.affineOpens) (P : Pt s)
    (a a' : (Pt.aff s U).Hom P) : a = a' := by
  obtain ⟨ρ, e⟩ := a
  obtain ⟨ρ', e'⟩ := a'
  have : ρ = ρ' := AlgHom.ext fun b ↦ (Pt.affHom_ρ_eq_valR s U P ⟨ρ, e⟩ b).trans (Pt.affHom_ρ_eq_valR s U P ⟨ρ', e'⟩ b).symm
  subst this; rfl

theorem Pt.Hom.comp_triv {R : Type} [CommRing R] {X : Scheme.{0}} {s : X ⟶ Sp R} {P Q T : Pt s}
    (φ : P.Hom Q) (ψ : Q.Hom T) : (φ.comp ψ).triv = φ.triv ≫ ψ.triv :=
  Thick.Hom.ext' (AlgHom.ext fun _ ↦ rfl)

theorem h1_mk_mem_f1_of_isRep_zero : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (J : Type) (W : J → X.Opens), ⨆ j, W j = ⊤ → ∀ c : Z1 (O (dp0 R) s), IsRep W c 0 → H1.mk _ c ∈ F1 s := by
  intro R _ X s J W hW c hc
  obtain ⟨G, hG1, hG2⟩ := hc
  have hG : ∀ j j' (P : Pt s), P.In (W j) → P.In (W j') → G j P = G j' P := fun j j' P h h' ↦
    sub_eq_zero.1 (hG2 j j' P h h')
  change toH1O s (H1.mk _ c) = 0
  refine (injective_iff_map_eq_zero (GlobalTheory.CechDR.cmpO s)).1
    (GlobalTheory.CechDR.cmpO_injective R X s) _ ?_
  rw [← GlobalTheory.CechDR.structureSheaf_comparison_comm, GlobalTheory.CechDR.comparison_mk]
  refine H1.mk_eq_zero.2 ?_
  classical
  let aP : ∀ (U : X.affineOpens) (P : Pt s), P.In U.1 → (Pt.aff s U).Hom P :=
    fun U P h ↦ (Pt.nonempty_affHom_of_in s U P h).some
  let FU : X.affineOpens → PtFn s := fun U P ↦
    if h : P.In U.1 ∧ ∃ j, P.In (W j) then G h.2.choose P - ev c (aP U P h.1).triv else 0
  have FU_eq : ∀ U (P : Pt s) j (hU : P.In U.1), P.In (W j) → FU U P = G j P - ev c (aP U P hU).triv := by
    intro U P j hU hj
    have h : P.In U.1 ∧ ∃ j, P.In (W j) := ⟨hU, j, hj⟩
    simp only [FU, dif_pos h]
    rw [hG _ j P h.2.choose_spec hj]
  have ex : ∀ U : X.affineOpens, ∃ f : Γ(X, U.1), ∀ (j : J) (P : Pt s), P.In (U.1 ⊓ W j) →
      FU U P = valR P.x U.1 f := by
    intro U
    refine GlobalTheory.T.exists_section_of_natural_on_algebraPoints_of_cover R X s J (fun j ↦ U.1 ⊓ W j) U.1 (fun j ↦ inf_le_left) ?_ (FU U) ?_
    · rw [← inf_iSup_eq, hW, inf_top_eq]
    · intro j P Q φ hP
      have hU : P.In U.1 := hP.mono inf_le_left
      have hj : P.In (W j) := hP.mono inf_le_right
      rw [FU_eq U P j hU hj, FU_eq U Q j (hU.map φ) (hj.map φ),
        Pt.affHom_subsingleton s U Q (aP U Q (hU.map φ)) ((aP U P hU).comp φ), Pt.Hom.comp_triv, ev_comp,
        hG1 j P Q φ hj, map_sub]
      have e : φ.triv.φ (ev c (aP U P hU).triv) = φ.ρ (ev c (aP U P hU).triv) := rfl
      rw [e]; ring
  choose f hf using ex
  refine ⟨fun U ↦ f U.unop, ?_⟩
  funext U V a
  have hle : V.unop.1 ≤ U.unop.1 := leOfHom a.unop
  refine eq_of_valR_eq_on_cover s W hW V.unop.1 _ _ fun P j hV hj ↦ ?_
  change valR P.x V.unop.1 (@HSub.hSub Γ(X, V.unop.1) Γ(X, V.unop.1) Γ(X, V.unop.1) _ (f V.unop)
    (GlobalTheory.CechDR.Sec.res s hle (f U.unop))) = valR P.x V.unop.1 (ev c (Pt.affHom s hle).triv)
  have hU : P.In U.unop.1 := hV.mono hle
  set b := aP V.unop P hV
  have e1 : valR P.x V.unop.1 (f V.unop) = FU V.unop P := (hf V.unop j P (hV.inf hj)).symm
  have e2 : valR P.x V.unop.1 (GlobalTheory.CechDR.Sec.res s hle (f U.unop)) = FU U.unop P :=
    (GlobalTheory.Points.valR_res P.x hle hV (f U.unop)).trans (hf U.unop j P (hU.inf hj)).symm
  have e3 : aP U.unop P hU = (Pt.affHom s hle).comp b := Pt.affHom_subsingleton s _ P _ _
  have e4 : ev c (aP U.unop P hU).triv = b.ρ (ev c (Pt.affHom s hle).triv) + ev c b.triv := by
    rw [e3, Pt.Hom.comp_triv, ev_comp]; rfl
  have e5 : valR P.x V.unop.1 (ev c (Pt.affHom s hle).triv) = b.ρ (ev c (Pt.affHom s hle).triv) :=
    (Pt.affHom_ρ_eq_valR s V.unop P b _).symm
  have e6 : b.ρ (@HSub.hSub Γ(X, V.unop.1) Γ(X, V.unop.1) Γ(X, V.unop.1) _ (f V.unop)
      (GlobalTheory.CechDR.Sec.res s hle (f U.unop))) =
      b.ρ (f V.unop) - b.ρ (GlobalTheory.CechDR.Sec.res s hle (f U.unop)) := map_sub b.ρ _ _
  rw [e5, ← Pt.affHom_ρ_eq_valR s V.unop P b, e6, Pt.affHom_ρ_eq_valR s V.unop P b (f V.unop),
    Pt.affHom_ρ_eq_valR s V.unop P b (GlobalTheory.CechDR.Sec.res s hle (f U.unop)), e1, e2,
    FU_eq V.unop P j hV hj, FU_eq U.unop P j hU hj, e4]
  ring

end GlobalTheory.CechKS
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix ENNReal Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WeilAdm


theorem weilAdmissible_of_heisenberg_unitary (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (κ : Type) [Fintype κ]
    (B : ((κ → AF D.host.F) × (κ → AF D.host.F)) ≃ₗ[AF D.host.F] ((κ → AF D.host.F) × (κ → AF D.host.F)))
    (O : Module.End ℂ ((κ → AF D.host.F) → ℂ))
    (hpres : ∀ φ ∈ GlobalTheory.WeilM.schA D.host.F κ, O φ ∈ GlobalTheory.WeilM.schA D.host.F κ)
    (himpl : ∀ w, ∀ φ ∈ GlobalTheory.WeilM.schA D.host.F κ, O (GlobalTheory.WeilM.schr ψ w φ) = GlobalTheory.WeilM.schr ψ (B w) (O φ))
    (hunit : ∀ μ : @Measure (κ → AF D.host.F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∀ φ ∈ GlobalTheory.WeilM.schA D.host.F κ, ∫⁻ x, ‖O φ x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ) :
    ∀ l ∈ (GlobalTheory.WeilM.adeleClass D.host.F).adm κ, l ∘ₗ O ∈ (GlobalTheory.WeilM.adeleClass D.host.F).adm κ := by
  intro l hl g hg
  obtain ⟨M, hMo, hM⟩ := GlobalTheory.T.adelicPureTensor_fixed_by_open_finiteHeisenberg D.host.F ψ hψ.1.1 κ g hg
  obtain ⟨M', hM'o, hM'⟩ := GlobalTheory.T.adeleLinearEquiv_maps_open_finite_subgroup_to_open D.host.F κ B M hMo
  obtain ⟨U, K, hUo, hUc, hK, hfix⟩ := GlobalTheory.T.heisenberg_fixed_invariant_open_compact_compact_support D ψ hψ κ M' hM'o
  obtain ⟨R, hRsb, hdec⟩ := GlobalTheory.T.eq_finset_sum_pureTensor_coset_indicator D.host.F κ U K hUo hUc hK
  obtain ⟨L, hL⟩ := GlobalTheory.T.adeleLinearEquiv_restricts_realLinearEquiv_archimedean D.host.F κ B
  obtain ⟨μ, hμ, C, c, hC, hc0, hcT, hpure, hslice⟩ := GlobalTheory.T.exists_haar_adelicVectors_bounds_pureTensors_slices D.host.F κ g hg U hUo
  have hpA : ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace D.host.F) ℂ,
      GlobalTheory.WeilM.pureA D.host.F f g ∈ GlobalTheory.WeilM.schA D.host.F κ := fun f => Submodule.subset_span ⟨f, g, hg, rfl⟩
  have hfixed : ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace D.host.F) ℂ, ∀ m ∈ M',
      GlobalTheory.WeilM.schr ψ (finE2 D.host.F m) (O (GlobalTheory.WeilM.pureA D.host.F f g)) = O (GlobalTheory.WeilM.pureA D.host.F f g) := by
    intro f m hm
    obtain ⟨m0, hm0, hB⟩ := hM' m hm
    rw [← hB, ← himpl _ _ (hpA f), hM m0 hm0]
  have hs : ∀ (f : SchwartzMap (κ → mixedEmbedding.mixedSpace D.host.F) ℂ) (r : κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F),
      ∃ s : SchwartzMap (κ → mixedEmbedding.mixedSpace D.host.F) ℂ, ∀ z,
        s z = slice D.host.F (O (GlobalTheory.WeilM.pureA D.host.F f g)) r z :=
    fun f r => exists_schwartz_slice _ (hpres _ (hpA f)) r
  choose sl hsl using hs
  let A : (κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F) →
      (SchwartzMap (κ → mixedEmbedding.mixedSpace D.host.F) ℂ →ₗ[ℂ] SchwartzMap (κ → mixedEmbedding.mixedSpace D.host.F) ℂ) :=
    fun r =>
    { toFun := fun f => sl f r
      map_add' := fun f f' => by
        ext z
        rw [SchwartzMap.add_apply, hsl, hsl, hsl, show ⇑(f + f') = ⇑f + ⇑f' from funext fun _ => rfl, pureA_add, map_add (f := _)]
        rfl
      map_smul' := fun a f => by
        ext z
        rw [SchwartzMap.smul_apply, hsl, hsl, show ⇑(a • f) = a • ⇑f from funext fun _ => rfl, pureA_smul, map_smul]
        rfl }
  have hA : ∀ r f, ⇑(A r f) = slice D.host.F (O (GlobalTheory.WeilM.pureA D.host.F f g)) r := fun r f => funext (hsl f r)
  have hcont : ∀ r, Continuous (A r) := by
    intro r
    refine GlobalTheory.T.archSchwartz_L2Bounded_intertwiner_continuous D ψ hψ κ L (A r) (C / c) (ENNReal.div_ne_top hC hc0) (fun f => ?_) (fun v f f' hf => ?_)
    · have h1 := hslice _ (hpres _ (hpA f)) (hfix _ (hfixed f)).1 r
      rw [hunit μ hμ _ (hpA f)] at h1
      have h2 := h1.trans (hpure f)
      rw [hA, ← ENNReal.mul_div_right_comm, ENNReal.le_div_iff_mul_le (Or.inl hc0) (Or.inl hcT), mul_comm]
      exact h2
    · rw [hA, hA, hf, pureA_schrInf, himpl _ _ (hpA f), hL, slice_schr]
  have hT : ∀ r ∈ R, ∃ T : SchwartzMap (κ → mixedEmbedding.mixedSpace D.host.F) ℂ →L[ℂ] ℂ,
      ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace D.host.F) ℂ,
      l (GlobalTheory.WeilM.pureA D.host.F f (Set.indicator {y | y - r ∈ U} fun _ => (1 : ℂ))) = T f :=
    fun r hr => hl _ (hRsb r hr)
  choose T hT using hT
  refine ⟨∑ r ∈ R.attach, (T r.1 r.2).comp ⟨A r.1, hcont r.1⟩, fun f => ?_⟩
  have hΦ := hdec (O (GlobalTheory.WeilM.pureA D.host.F f g)) (hfix _ (hfixed f)).1 (hfix _ (hfixed f)).2

  rw [LinearMap.comp_apply, hΦ, map_sum, ContinuousLinearMap.sum_apply, ← Finset.sum_attach R]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [← hA, hT r.1 r.2]
  rfl

end GlobalTheory.WeilAdm

namespace GlobalTheory.WeilAdm

theorem transport_adm : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle), IsHeckeChar D χS → IsHeckeChar D χT →
      ResEta D χS S.rank → ResEta D χT T.rank →
      ∀ (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
        (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
        ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
        ∀ (κ : Type) [Fintype κ]
          (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
          (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
            co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
          ∀ ω : GA D S × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO S T → ℂ),
            Formalism.IndefR.Datum.IsWeilDatumO ψ S T χS χT ω →
 ∀ om : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA) ×
      GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB) →* Module.End ℂ ((κ → AF D.host.F) → ℂ),
                       GlobalTheory.WeilSchrodinger.IsTransport ψ co ω om →
                       ∀ p, ∀ l ∈ (GlobalTheory.WeilM.adeleClass D.host.F).adm κ, l ∘ₗ om p ∈ (GlobalTheory.WeilM.adeleClass D.host.F).adm κ := by
  intro D ψ hψ S T χS χT hS hT hrS hrT JA JB ξ hJA hJB κ _ co hco ω hω om htr p l hl
  have hP := GlobalTheory.T.transportedWeil_preserves_schwartz_heisenberg_equivariant D ψ hψ S T χS χT hS hT hrS hrT JA JB ξ hJA hJB κ co hco ω hω om htr
  have hU := GlobalTheory.T.transportedWeilDatum_isUnitary_adelicSchwartz D ψ hψ S T χS χT hS hT hrS hrT JA JB ξ hJA hJB κ co hco ω hω om htr
  refine weilAdmissible_of_heisenberg_unitary D ψ hψ κ (co.e.symm.trans ((actLin _ p).trans co.e)) (om p) (hP.1 p)
    (fun w φ hφ => ?_) (fun μ hμ φ hφ => hU μ hμ p φ hφ) l hl
  have h := hP.2 p (co.e.symm w) φ hφ
  simp only [GlobalTheory.WeilM.Darboux.rho, LinearEquiv.apply_symm_apply] at h
  exact h

end GlobalTheory.WeilAdm

end
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

theorem _root_.GlobalTheory.T.thetaTransform_adelicSchwartz_hasFiniteLevel_CM : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
    ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
        ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
        ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
          (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
            co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
          ∀ Φ ∈ schA F κ, ∃ U : AddSubgroup (WOF F E nS nT), IsOpen (U : Set (WOF F E nS nT)) ∧
            ∀ u ∈ U, u.map (infPartF F E) = 0 → heisOF σ JS JT ξ₀ B.ψ u (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Φ) = GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Φ := by
  first | exact @GlobalTheory.ThetaLevelF.thetaTr_levelF | exact GlobalTheory.ThetaLevelF.thetaTr_levelF | (intros; apply GlobalTheory.ThetaLevelF.thetaTr_levelF <;> assumption)
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.ThetaLevelCM

theorem thetaTr_level : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
      ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
        ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
        ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
          (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
            co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
          ∀ φ ∈ schA F κ,
          ∃ U : AddSubgroup (Formalism.IndefR.DatumF.WOF F E nS nT), IsOpen (U : Set (Formalism.IndefR.DatumF.WOF F E nS nT)) ∧
            ∀ u ∈ U, u.map (Formalism.IndefR.DatumF.infPartF F E) = 0 →
              Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ u (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ φ) =
                GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ φ := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ h0 hσ hψ JA JB ξ hA hJB κ _ co hco φ hφ
  exact GlobalTheory.ThetaLevelF.thetaTr_levelF F E σ B hB hψ nS nT JS JT hS hT ξ₀ h0 hσ JA JB ξ hA hJB κ co hco φ hφ

end GlobalTheory.ThetaLevelCM
end

section


theorem _root_.GlobalTheory.T.nefLineBundleNumericalTheorems_proof : GlobalTheory.Published.NefNumerics := by
  first | exact @GlobalTheory.nefNumerics_outright | exact GlobalTheory.nefNumerics_outright | (intros; apply GlobalTheory.nefNumerics_outright <;> assumption)
end
