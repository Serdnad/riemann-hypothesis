module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle132
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle081
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle107
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GenRelNeZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle003
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Mathlib.Tactic.ENatToNat
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle049
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle130
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle068
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle051
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle125
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle009
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle054
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle113
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
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
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.FlatIsoUnitGenerator
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle004
import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZV

noncomputable section
namespace GlobalTheory.ZV.CoordEmbed
open GlobalTheory.ZM.RepBC

theorem appLE_bijective {X Y : Scheme.{0}} (x : Y ⟶ X) [IsOpenImmersion x] {V : X.Opens} {W : Y.Opens}
    (hV : V ≤ x.opensRange) (e : W ≤ x ⁻¹ᵁ V) (e' : x ⁻¹ᵁ V ≤ W) :
    Function.Bijective (x.appLE V W e).hom := by
  obtain rfl : W = x ⁻¹ᵁ V := le_antisymm e e'
  have hiso : IsIso (x.app V) := x.isIso_app V hV
  rw [← x.app_eq_appLE]
  first
    | exact (asIso (x.app V)).commRingCatIsoToRingEquiv.bijective

theorem cover {K σ : Type} [CommRing K] {I : Ideal (MvPolynomial σ K)} {Z : Scheme.{0}} {p : Z ⟶ Sp K} {M : LB Z}
    {th : σ → M.Sec} (h : ProjRep I p M th) : ⨆ i, Out.nonzeroLocus (th i) = ⊤ := by
  obtain ⟨hLB, hpt, -⟩ := h
  rw [eq_top_iff]
  rintro z -
  obtain ⟨R, _, x, v, -, ⟨q, rfl⟩, hv⟩ := (GlobalTheory.T.sectionCoordinateVector_exists_locally Z M σ th hLB).2.2 z
  have hβ : x ≫ p = spMap (Spec.preimage (x ≫ p)).hom := by
    unfold spMap
    simp
  have hspan := (hpt R _ x v hβ hv).1
  obtain ⟨i, hi⟩ : ∃ i, v i ∉ q.asIdeal := by
    by_contra hno
    simp only [not_exists, not_not] at hno
    apply q.isPrime.ne_top
    rw [eq_top_iff, ← hspan, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact hno i
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, ((GlobalTheory.T.sectionCoordinates_pull_iso_nonzeroLocus Z M σ th hLB).2.2 R x v i q hv).2 hi⟩

theorem ratios {K σ S : Type} [CommRing K] [CommRing S] {Z : Scheme.{0}} {p : Z ⟶ Sp K} {M : LB Z}
    {th : σ → M.Sec} (i : σ) (D : Z.Opens) (x : Sp S ⟶ Z) [IsOpenImmersion x] (hD : x.opensRange = D)
    (β : K →+* S) (hx : x ≫ p = spMap β) (v : σ → S) (hv : SecCoord M th x v) (hi : v i = 1)
    (hgen : ∀ a : S, ∃ F : MvPolynomial σ K, a = MvPolynomial.eval₂ β v F) :
    ∃ r : σ → Γ(Z, D),
      (∀ j k, resG Z (inf_le_right : D ⊓ M.U k ≤ M.U k) ((th j).f k) =
        resG Z (inf_le_left : D ⊓ M.U k ≤ D) (r j) * resG Z (inf_le_right : D ⊓ M.U k ≤ M.U k) ((th i).f k)) ∧
      ∀ f : Γ(Z, D), ∃ F : MvPolynomial σ K,
        f = MvPolynomial.eval₂ (RingHom.comp (p.appLE ⊤ _ le_top).hom (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom) r F := by
  obtain ⟨τ, -, hvτ⟩ := hv
  have hU : ∀ k, (M.pull x).U (fun _ => k) = x ⁻¹ᵁ M.U k := fun k => by
    ext1
    simp only [LB.pull, LB.LinComb, LB.wchart, Scheme.Hom.coe_preimage]
    first
      | exact Set.iInter_const _
      | simp
  have hxD : x ⁻¹ᵁ D = ⊤ := by
    rw [← hD]
    exact Scheme.Hom.preimage_opensRange x
  have hDle : D ≤ x.opensRange := hD.ge

  have hres : ∀ (A B : Z.Opens) (hAB : A ≤ B) (W : (Sp S).Opens) (hW : W ≤ x ⁻¹ᵁ A) (a : Γ(Z, B)),
      (x.appLE A W hW).hom (resG Z hAB a) = (x.appLE B W (hW.trans fun _ hz => hAB hz)).hom a := by
    intro A B hAB W hW a
    unfold resG
    rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

  have hres' : ∀ (A : Z.Opens) (W W' : (Sp S).Opens) (hW : W ≤ x ⁻¹ᵁ A) (hW' : W' ≤ W) (a : Γ(Z, A)),
      resG (Sp S) hW' ((x.appLE A W hW).hom a) = (x.appLE A W' (hW'.trans hW)).hom a := by
    intro A W W' hW hW' a
    unfold resG
    rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]
  have hcomp : ∀ (W₁ W₂ W₃ : (Sp S).Opens) (h₁ : W₂ ≤ W₁) (h₂ : W₃ ≤ W₂) (a : Γ(Sp S, W₁)),
      resG (Sp S) h₂ (resG (Sp S) h₁ a) = resG (Sp S) (h₂.trans h₁) a := by
    intro W₁ W₂ W₃ h₁ h₂ a
    unfold resG
    rw [← CommRingCat.comp_apply, ← Functor.map_comp]
    rfl
  have hbij := appLE_bijective x hDle hxD.ge le_top

  obtain ⟨r, hr⟩ : ∃ r : σ → Γ(Z, D),
      ∀ j, (x.appLE D ⊤ hxD.ge).hom (r j) = (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom (v j) :=
    ⟨fun j => (hbij.2 _).choose, fun j => (hbij.2 _).choose_spec⟩
  refine ⟨r, fun j k => ?_, fun f => ?_⟩
  · have hk : x ⁻¹ᵁ (D ⊓ M.U k) ≤ (M.pull x).U (fun _ => k) := by
      rw [hU]
      exact fun _ hz => hz.2
    have key : ∀ (l : σ) (h' : x ⁻¹ᵁ (D ⊓ M.U k) ≤ x ⁻¹ᵁ M.U k),
        (x.appLE (M.U k) (x ⁻¹ᵁ (D ⊓ M.U k)) h').hom ((th l).f k) =
          resG (Sp S) hk (resG (Sp S) (le_top : (M.pull x).U (fun _ => k) ≤ ⊤)
            ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom (v l)) *
            ((τ.s fun _ => k).val : Γ(Sp S, (M.pull x).U fun _ => k))) := by
      intro l h'
      rw [← hvτ l (fun _ => k) (hU k).le, hres']
    have hrj : ∀ (h' : x ⁻¹ᵁ (D ⊓ M.U k) ≤ x ⁻¹ᵁ D),
        (x.appLE D (x ⁻¹ᵁ (D ⊓ M.U k)) h').hom (r j) =
          resG (Sp S) le_top ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom (v j)) := by
      intro h'
      rw [← hr j, hres']
    apply (appLE_bijective x (inf_le_left.trans hDle) le_rfl le_rfl).1
    rw [map_mul, hres, hres, hres, key j, key i, hrj, hi]
    simp only [map_one, _root_.one_mul, map_mul, hcomp]
  · obtain ⟨F, hF⟩ := hgen ((Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom ((x.appLE D ⊤ hxD.ge).hom f))
    refine ⟨F, hbij.1 ?_⟩
    have hbase : ∀ (g : Sp S ⟶ Sp K) (hg : g = spMap β) (e : (⊤ : (Sp S).Opens) ≤ g ⁻¹ᵁ ⊤) (c : K),
        (g.appLE ⊤ ⊤ e).hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom c) =
          (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom (β c) := by
      rintro g rfl e c
      exact GlobalTheory.ZM.Coord.appLE_spec β e c
    have h₁ : (x.appLE D ⊤ hxD.ge).hom.comp
        (RingHom.comp (p.appLE ⊤ _ le_top).hom (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom) =
        (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom.comp β := by
      ext c
      show (x.appLE D ⊤ hxD.ge).hom ((p.appLE ⊤ D le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom c)) =
        (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom (β c)
      have hcc := congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom c))
        (Scheme.Hom.appLE_comp_appLE x p ⊤ D ⊤ le_top hxD.ge)
      exact hcc.trans (hbase _ hx _ c)
    have h₂ : (x.appLE D ⊤ hxD.ge).hom ∘ r = (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom ∘ v := funext hr
    rw [MvPolynomial.eval₂_comp_left, h₁, h₂, ← MvPolynomial.eval₂_comp_left, ← hF,
      ← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply]

theorem vAmp_of_projRep : ∀ (K σ : Type) [Field K] [Finite σ] (I : Ideal (MvPolynomial σ K)) (Z : Scheme.{0}) (p : Z ⟶ Sp K) (M : LB Z) (th : σ → M.Sec), ProjRep I p M th → VAmp p M th := by
  intro K σ _ _ I Z p M th h
  refine ⟨cover h, fun i => ?_⟩
  obtain ⟨x, hx, hrange, hxs, hsc⟩ := GlobalTheory.T.exists_nonzeroCoordinate_affineChart K σ I Z p M th i h
  have hD : x.opensRange = Out.nonzeroLocus (th i) := TopologicalSpace.Opens.ext hrange
  refine ⟨hD ▸ isAffineOpen_opensRange x, ?_⟩
  refine ratios i _ x hD _ hxs _ hsc ?_ ?_
  · rw [← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq]
    exact Ideal.mem_sup_right (Ideal.subset_span rfl)
  · intro a
    obtain ⟨F, rfl⟩ := Ideal.Quotient.mk_surjective a
    refine ⟨F, ?_⟩
    conv_lhs => rw [← MvPolynomial.eval₂_eta F]
    exact MvPolynomial.eval₂_comp_left _ _ _ _

end GlobalTheory.ZV.CoordEmbed
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.FlatTors GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator
open scoped TensorProduct

namespace GlobalTheory.FlatTors

theorem weilIs_of_cubWeil_of_proper {S S' : Scheme.{0}} (f : S' ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G]
    (hG : IsSemiAbelian G) (hpr : IsProper (pullback.snd G.hom f)) {L : RigLB G} (c : CubicalStr G L) (k : ℕ)
    (T : Over S') (x y : Over.mk (T.hom ≫ f) ⟶ G) (z : Γ(T.left, ⊤)ˣ) (h : GlobalTheory.UU.CubWeil c k x y z) :
    WeilIs G L.L (k : ℤ) x y z := by
  let G' : Over S' := (Over.pullback f).obj G
  have hp : IsGrpPullback G' G f (pullback.fst G.hom f) := isGrpPullback_pullback G f
  have hG' : IsSemiAbelian G' := IsSemiAbelian.pullback f G hG
  have := hG'.comm
  have hA : IsAbelianScheme G' := ⟨hG'.comm, hG'.smooth, hpr, hG'.geomConnected⟩
  obtain ⟨hL, hr, ⟨c', hc'⟩, -⟩ := CubePf.cubePull _ _ G G' (cubeMapOf hp) L c
  have hw : pullback.fst G.hom f ≫ G.hom = G'.hom ≫ f := pullback.condition
  let β := GlobalTheory.UU.toBaseHom (GlobalTheory.UU.toBase_mul_pullback G f) T
  have inj : Function.Injective β := fun a b e =>
    Over.OverMorphism.ext (hp.1.hom_ext (congrArg (fun z => z.left) e) ((Over.w a).trans (Over.w b).symm))
  have sur : Function.Surjective β := fun p =>
    ⟨Over.homMk (hp.1.lift p.left T.hom (Over.w p)) (hp.1.lift_snd _ _ _),
      Over.OverMorphism.ext (hp.1.lift_fst _ _ _)⟩
  obtain ⟨u, rfl⟩ := sur x
  obtain ⟨v, rfl⟩ := sur y
  have hu : u ^ k = 1 := inj (by rw [map_pow, map_one]; exact h.1)
  have hv : v ^ k = 1 := inj (by rw [map_pow, map_one]; exact h.2.1)
  obtain ⟨z', hz', -⟩ := GlobalTheory.UU.existsUnique_cubWeil c' hu hv
  have h₁ := GlobalTheory.UU.cubWeil_of_isPullCubical _ _ f G G' (cubeMapOf hp) hw (GlobalTheory.UU.toBase_mul_pullback G f) L _ c c' hc'
    k T u v z' hz'
  obtain rfl : z = z' := h.unique h₁
  have h₂ := (GlobalTheory.UU.cubWeil_iff_weilIs GlobalTheory.SemiRigid.globalFns hA hu hv z).1 hz'
  exact (GlobalTheory.weilIs_iff_of_isGrpPullback_comm _ _ G G' f _ L.L _ L.isLB hL hp
    ⟨GlobalTheory.UU.pullIso _ _, GlobalTheory.UU.pullIso_isGen L.isLB _⟩ T k u v (β u) (β v) z rfl rfl).1 h₂

end GlobalTheory.FlatTors
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

theorem _root_.GlobalTheory.T.lineBundle_generic_fibre_spreads_out : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K] (B : Scheme.{0}) (pB : B ⟶ Sp R) (M : LB (pullback pB (spMap (algebraMap R K)))), QuasiCompact pB → QuasiSeparated pB → M.IsLB → ∃ (f : R) (_ : f ≠ 0) (M' : LB (pullback pB (spMap (algebraMap R (Localization.Away f))))), M'.IsLB ∧ ∀ j : pullback pB (spMap (algebraMap R K)) ⟶ pullback pB (spMap (algebraMap R (Localization.Away f))), j ≫ pullback.fst _ _ = pullback.fst _ _ → LBIso M (M'.pull j) := by
  first | exact @GlobalTheory.lb_generic_spreads_out | exact GlobalTheory.lb_generic_spreads_out | (intros; apply GlobalTheory.lb_generic_spreads_out <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

noncomputable section
namespace GlobalTheory.SerreTwist

theorem iso_eq_of_torsion (hL : Laws) {C : Type} [Field C] [IsAlgClosed C] (Q Q' : PolAV (Sp C))
    (a b : Q.A ≅ Q'.A) (ha : η[Q.A] ≫ a.hom = η[Q'.A]) (hb : η[Q.A] ≫ b.hom = η[Q'.A])
    (la : LBIso Q.L (Q'.L.pull a.hom.left)) (lb : LBIso Q.L (Q'.L.pull b.hom.left))
    {k : ℕ} (hk : 3 ≤ k) (hkC : (k : C) ≠ 0)
    (h : ∀ x : 𝟙_ (Over (Sp C)) ⟶ Q.A, x ^ k = 1 → x ≫ a.hom = x ≫ b.hom) : a.hom = b.hom := by
  have hη : η[Q.A] ≫ (a ≪≫ b.symm).hom = η[Q.A] := by
    rw [Iso.trans_hom, Iso.symm_hom, ← Category.assoc, ha, ← hb, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  have hmon : IsMonHom (a ≪≫ b.symm).hom := hL.rigidity _ Q.A Q.A Q.isAb Q.isAb _ hη
  have hpb : LBIso (Q.L.pull (a ≪≫ b.symm).hom.left) (Q'.L.pull a.hom.left) :=
    GlobalTheory.GenSpread.lbIso_pull_of_lbIso lb _
      (by rw [← Over.comp_left, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id])
  obtain ⟨w, hw⟩ : LBIso Q.L (Q.L.pull (a ≪≫ b.symm).hom.left) :=
    LBIso.trans Q.isLB (LB.isLB_pull Q'.isLB _) (LB.isLB_pull Q.isLB _) la (LBIso.symm hpb)
  have hfix : ∀ x : Over.mk (𝟙 (Sp C)) ⟶ Q.A, x ^ k = 1 → x ≫ (a ≪≫ b.symm).hom = x := by
    intro x hx
    rw [Iso.trans_hom, Iso.symm_hom, ← Category.assoc, h x hx, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have key := GlobalTheory.MatchRigid.aut_eq_id hL Q (𝟙 (Sp C)) hk hkC (a ≪≫ b.symm) w hw hfix
  have := congrArg (· ≫ b.hom) key
  simpa using this

theorem exists_fibre (hB : PolBaseChangeSt) {S S' : Scheme.{0}} (P : PolAV S) (t : S' ⟶ S) :
    ∃ (Q : PolAV S') (e : Q.A.left ≅ (Over.mk t ⊗ P.A).left),
      e.hom ≫ (fst (Over.mk t) P.A).left = Q.A.hom ∧
      LBIso Q.L (P.L.pull (e.hom ≫ (snd (Over.mk t) P.A).left)) ∧
      ∃ F : (𝟙_ (Over S') ⟶ Q.A) →* (Over.mk t ⟶ P.A),
        ∀ x, x.left ≫ e.hom = (lift (𝟙 (Over.mk t)) (F x)).left := by
  obtain ⟨Q, g, hg, -, hmul, w, hw⟩ := hB S S' t P
  have hpb : IsPullback Q.A.hom g t P.A.hom := hg.flip
  let c : Over.mk t ⟶ Over.mk ((𝟙_ (Over S')).hom ≫ t) := Over.homMk (𝟙 S') (by simp)
  have hsnd : hpb.isoPullback.hom ≫ (snd (Over.mk t) P.A).left = g := by
    rw [Over.snd_left]; exact hpb.isoPullback_hom_snd
  refine ⟨Q, hpb.isoPullback, ?_, ?_,
    MonoidHom.mk' (fun x => c ≫ toBase hg.w x) (fun x y => by simp only [hmul, MonObj.comp_mul]), fun x => ?_⟩
  · rw [Over.fst_left]; exact hpb.isoPullback_hom_fst
  · rw [hsnd]; exact LBIso.symm ⟨w, hw⟩
  · apply pullback.hom_ext
    · simp [c]
    · have hs : hpb.isoPullback.hom ≫ pullback.snd (Over.mk t).hom P.A.hom = g := hpb.isoPullback_hom_snd
      rw [Category.assoc, hs, Over.lift_left]
      erw [pullback.lift_snd]
      simp [c, toBase]

theorem prod_iso_eq (hL : Laws) {S : Scheme.{0}} (P P' : PolAV S) {C : Type} [Field C] [IsAlgClosed C]
    (t : Sp C ⟶ S) {k : ℕ} (hk : 3 ≤ k) (hkC : (k : C) ≠ 0) (φ : Fin 2 → (Over.mk t ⊗ P.A ≅ Over.mk t ⊗ P'.A))
    (h1 : ∀ i, (φ i).hom ≫ fst _ _ = fst _ _)
    (h2 : ∀ i, lift (𝟙 (Over.mk t)) (1 : Over.mk t ⟶ P.A) ≫ (φ i).hom ≫ snd _ _ = 1)
    (h3 : ∀ i, LBIso (P.L.pull (snd (Over.mk t) P.A).left) (P'.L.pull ((φ i).hom ≫ snd (Over.mk t) P'.A).left))
    (h4 : ∀ x : Over.mk t ⟶ P.A, x ^ k = 1 →
      lift (𝟙 (Over.mk t)) x ≫ (φ 0).hom ≫ snd _ _ = lift (𝟙 (Over.mk t)) x ≫ (φ 1).hom ≫ snd _ _) :
    (φ 0).hom = (φ 1).hom := by
  obtain ⟨Q, e, he1, he2, F, hF⟩ := exists_fibre hL.polBaseChange P t
  obtain ⟨Q', e', he1', he2', F', hF'⟩ := exists_fibre hL.polBaseChange P' t

  have hlift : ∀ i (z : Over.mk t ⟶ P.A), lift (𝟙 (Over.mk t)) z ≫ (φ i).hom =
      lift (𝟙 (Over.mk t)) (lift (𝟙 (Over.mk t)) z ≫ (φ i).hom ≫ snd _ _) := by
    intro i z
    apply CartesianMonoidalCategory.hom_ext
    · simp [h1 i]
    · simp
  have h1' : ∀ i, (φ i).hom.left ≫ (fst (Over.mk t) P'.A).left = (fst (Over.mk t) P.A).left := by
    intro i
    rw [← Over.comp_left, h1 i]

  let θ : Fin 2 → (Q.A.left ≅ Q'.A.left) := fun i => e ≪≫ (Over.forget S).mapIso (φ i) ≪≫ e'.symm
  have hθ : ∀ i, (θ i).hom = e.hom ≫ (φ i).hom.left ≫ e'.inv := fun i => rfl
  have hw : ∀ i, (θ i).hom ≫ Q'.A.hom = Q.A.hom := by
    intro i
    rw [hθ, ← he1', ← he1, Category.assoc, Category.assoc, Iso.inv_hom_id_assoc, h1']
  let a : Fin 2 → (Q.A ≅ Q'.A) := fun i => Over.isoMk (θ i) (hw i)
  have ha_left : ∀ i, (a i).hom.left = e.hom ≫ (φ i).hom.left ≫ e'.inv := fun i => rfl
  have hcomp : ∀ i (x : 𝟙_ (Over (Sp C)) ⟶ Q.A), x.left ≫ (a i).hom.left =
      (lift (𝟙 (Over.mk t)) (lift (𝟙 (Over.mk t)) (F x) ≫ (φ i).hom ≫ snd _ _)).left ≫ e'.inv := by
    intro i x
    rw [ha_left, ← Category.assoc, hF, ← Category.assoc, ← Over.comp_left, hlift]

  have hone : ∀ (R : PolAV (Sp C)), (1 : 𝟙_ (Over (Sp C)) ⟶ R.A) = η[R.A] := by
    intro R
    rw [Hom.one_def, toUnit_unit, Category.id_comp]
  have ha : ∀ i, η[Q.A] ≫ (a i).hom = η[Q'.A] := by
    intro i
    apply Over.OverMorphism.ext
    rw [Over.comp_left, ← hone Q, hcomp, map_one, h2 i, ← map_one F', ← hF', hone Q', Category.assoc,
      Iso.hom_inv_id, Category.comp_id]

  have la : ∀ i, LBIso Q.L (Q'.L.pull (a i).hom.left) := by
    intro i
    have h3e : LBIso (P.L.pull (e.hom ≫ (snd (Over.mk t) P.A).left))
        (P'.L.pull ((a i).hom.left ≫ e'.hom ≫ (snd (Over.mk t) P'.A).left)) :=
      GlobalTheory.GenSpread.lbIso_pull_comp e.hom rfl
        (by rw [ha_left, Over.comp_left]; simp only [Category.assoc, Iso.inv_hom_id_assoc]) (h3 i)
    have hQ' := GlobalTheory.GenSpread.lbIso_pull_of_lbIso he2' (a i).hom.left rfl
    exact LBIso.trans Q.isLB (LB.isLB_pull P'.isLB _) (LB.isLB_pull Q'.isLB _)
      (LBIso.trans Q.isLB (LB.isLB_pull P.isLB _) (LB.isLB_pull P'.isLB _) he2 h3e) (LBIso.symm hQ')

  have htor : ∀ x : 𝟙_ (Over (Sp C)) ⟶ Q.A, x ^ k = 1 → x ≫ (a 0).hom = x ≫ (a 1).hom := by
    intro x hx
    have hFx : F x ^ k = 1 := by rw [← map_pow, hx, map_one]
    apply Over.OverMorphism.ext
    rw [Over.comp_left, Over.comp_left, hcomp, hcomp, h4 (F x) hFx]
  have key := congrArg Over.Hom.left (iso_eq_of_torsion hL Q Q' (a 0) (a 1) (ha 0) (ha 1) (la 0) (la 1) hk hkC htor)
  rw [ha_left, ha_left] at key
  apply Over.OverMorphism.ext
  simpa using key

end GlobalTheory.SerreTwist

theorem GlobalTheory.SerreTwist.whisker_comp_eq : Laws → ∀ (S : Scheme.{0}) (P P' : PolAV S) (C : Type) [Field C] [IsAlgClosed C] (t : Sp C ⟶ S) (φ : Over.mk t ⊗ P.A ≅ Over.mk t ⊗ P'.A), φ.hom ≫ fst _ _ = fst _ _ → lift (𝟙 (Over.mk t)) (1 : Over.mk t ⟶ P.A) ≫ φ.hom ≫ snd _ _ = 1 → LBIso (P.L.pull (snd (Over.mk t) P.A).left) (P'.L.pull (φ.hom ≫ snd (Over.mk t) P'.A).left) → ∀ k : ℕ, 3 ≤ k → (k : C) ≠ 0 → ∀ s : Over.mk t ≅ Over.mk t, (∀ x : Over.mk t ⟶ P.A, x ^ k = 1 → lift (𝟙 (Over.mk t)) (s.hom ≫ x) ≫ φ.hom ≫ snd _ _ = s.hom ≫ lift (𝟙 (Over.mk t)) x ≫ φ.hom ≫ snd _ _) → s.hom ▷ P.A ≫ φ.hom ≫ snd _ _ = φ.hom ≫ snd _ _ := by
  intro hL S P P' C inst1 inst2 t φ h1 h2 h3 k hk hkC s hs
  let ψ : Over.mk t ⊗ P.A ≅ Over.mk t ⊗ P'.A := whiskerRightIso s P.A ≪≫ φ ≪≫ whiskerRightIso s.symm P'.A
  have hψ : ψ.hom = s.hom ▷ P.A ≫ φ.hom ≫ s.inv ▷ P'.A := rfl
  have hψs : ψ.hom ≫ snd _ _ = s.hom ▷ P.A ≫ φ.hom ≫ snd _ _ := by
    rw [hψ]; simp

  have hsw : ∀ z : Over.mk t ⟶ P.A,
      lift (𝟙 (Over.mk t)) z ≫ s.hom ▷ P.A = s.hom ≫ lift (𝟙 (Over.mk t)) (s.inv ≫ z) := by
    intro z
    apply CartesianMonoidalCategory.hom_ext <;> simp
  have ψ1 : ψ.hom ≫ fst _ _ = fst _ _ := by
    rw [hψ]; simp [reassoc_of% h1]
  have ψ2 : lift (𝟙 (Over.mk t)) (1 : Over.mk t ⟶ P.A) ≫ ψ.hom ≫ snd _ _ = 1 := by
    rw [hψs, ← Category.assoc, hsw, MonObj.comp_one, Category.assoc, h2, MonObj.comp_one]
  have ψ3 : LBIso (P.L.pull (snd (Over.mk t) P.A).left) (P'.L.pull (ψ.hom ≫ snd (Over.mk t) P'.A).left) := by
    rw [hψs]
    exact GlobalTheory.GenSpread.lbIso_pull_comp (s.hom ▷ P.A).left (by rw [← Over.comp_left, whiskerRight_snd])
      (by rw [Over.comp_left]) h3
  have ψ4 : ∀ x : Over.mk t ⟶ P.A, x ^ k = 1 →
      lift (𝟙 (Over.mk t)) x ≫ φ.hom ≫ snd _ _ = lift (𝟙 (Over.mk t)) x ≫ ψ.hom ≫ snd _ _ := by
    intro x hx
    have hx' : (s.inv ≫ x) ^ k = 1 := by rw [← MonObj.comp_pow, hx, MonObj.comp_one]
    conv_rhs => rw [hψs, ← Category.assoc, hsw, Category.assoc]
    rw [← hs _ hx', Iso.hom_inv_id_assoc]
  have key : φ.hom = ψ.hom :=
    GlobalTheory.SerreTwist.prod_iso_eq hL P P' t hk hkC ![φ, ψ] (Fin.forall_fin_two.2 ⟨h1, ψ1⟩)
      (Fin.forall_fin_two.2 ⟨h2, ψ2⟩) (Fin.forall_fin_two.2 ⟨h3, ψ3⟩) ψ4
  rw [← hψs, ← key]

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.LocalModelExists

theorem exists_model_raises : Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (n N : ℕ) (T : Top Xo n N), ToroidalLevelCompatibility (H := H) (D := D) → ∀ (l₀ l : Level H) (B : BaseModel T l₀) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (b : RZ H (n * l₀.M) 1 →+* O), 0 < n → l₀.Dvd l → IsDedFrac β → IsInc (RZ H (n * l₀.M) 1).subtype (c.F.val.toRingHom.comp β) b → ∃ Y : Model (Xo l) c β, Raises B Y := by
  intro L1 L2 L3 E _ _ _ H D Xo n N T hN l₀ l B c O _ β b hn hd hβ hb
  obtain ⟨o, ⟨m0⟩⟩ := GlobalTheory.obj_pull E H D l (KA l) (KA l) (baseKA l) (baseKA l) (RingHom.id _) _ _ (Xo l).s
    (pullback.fst (Xo l).s (spMap (IntermediateField.inclusion c.le).toRingHom) ≫ (Xo l).s)
    (pullback.fst (Xo l).s (spMap (IntermediateField.inclusion c.le).toRingHom)) rfl rfl
    (by simp [spMap]) (Xo l).univ
  obtain ⟨k, r, ν, hr, hk, hlev, hfin, -, -⟩ :=
    GlobalTheory.LevelMapField.exists_levelMap L1 L2 L3 E H D Xo hN l₀ l c o m0 hd
  have hpos : 0 < n * l₀.M := Nat.mul_pos hn (by have := l₀.three_le; omega)
  have hB : IsDedFrac B.β := by
    have aux : ∀ a : ℕ, l₀.A = a → a = 1 → ∀ β₀ : RZ H (n * l₀.M) a →+* KA l₀,
        IsInc (RZ H (n * l₀.M) a).subtype (KA l₀).val.toRingHom β₀ → IsDedFrac β₀ := by
      intro a ha h1
      subst ha
      exact (GlobalTheory.T.cmModelCoefficientSubring_dedekind_compatible_embedding E H l₀ (n * l₀.M) 0 hpos (by simp [h1])).2.2
    exact aux 1 B.A_one rfl B.β B.β_inc
  have hcomp : β.comp b = k.comp B.β := by
    refine RingHom.ext fun x => Subtype.ext ?_
    exact (hb x).trans ((hk (B.β x)).trans (B.β_inc x)).symm
  have hsm : Smooth (pullback.snd (Xo l).s (spMap (IntermediateField.inclusion c.le).toRingHom)) := by
    have := (Xo l).smooth
    have : Smooth (Xo l).s := SmoothOfRelativeDimension.smooth D.dim _
    infer_instance
  have hnorm := (GlobalTheory.isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field _ _ _ hsm).2.1
  obtain ⟨C, hC⟩ := GlobalTheory.T.exists_normal_model_above_finite_cover E H _ _ _ (Xo l₀).s (Xo l₀).univ.t B.β _ _ _
    (pullback.snd (Xo l).s (spMap (IntermediateField.inclusion c.le).toRingHom)) o.t β B.C b k r hr ν hB hβ hcomp
    hnorm hfin
  exact ⟨⟨C.X, C.s, C.normal, C.proj, C.flat, C.jQ, C.jQ_over, C.jQ_open, C.jQ_dense, C.t, o, m0, C.m, C.ab_gen⟩,
    b, r, ν, hb, hlev, hC⟩

end GlobalTheory.LocalModelExists
end
