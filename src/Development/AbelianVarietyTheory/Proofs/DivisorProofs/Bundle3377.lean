module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle001
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3376
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2893
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle002
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle014
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle042
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3373
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3089
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1571
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2912
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3241
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle067
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle071
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3212
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2897
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3374
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3158
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2931
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3032
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3245
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3271
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
import Development.AbelianVarietyTheory.Definitions.Divisors.LogAbsVpOfNormalised
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle044
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle073

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GoodRedProper

theorem isProper_of_proper_fibres :
    ∀ (W L : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field L] [Algebra W L] [IsFractionRing W L] (G : Over (Sp W)) [GrpObj G], GlobalTheory.SS.SmConn G → IsProper ((Over.pullback (spMap (algebraMap W L))).obj G).hom → IsProper (GlobalTheory.SS.spFibre G).hom → IsProper G.hom := by
  intro W L _ _ _ _ _ _ G _ h _ h2
  obtain ⟨a, b, c, d, e⟩ := h
  have := GlobalTheory.grpObj_geometricallyIntegral_of_smooth _ G
  exact GlobalTheory.T.isProper_of_properSpecialFibre_universallyOpen_dvr W G.left G.hom inferInstance inferInstance inferInstance inferInstance inferInstance h2

end GlobalTheory.GoodRedProper
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.exists_finiteType_scheme_representing_polarizedHoms : ∀ (Rg : Type) [CommRing Rg] [IsNoetherianRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left), IsAbelianScheme A → IsAbelianScheme B → L.IsLB → M.IsLB → Out.Rigidified A L → Out.Rigidified B M → Out.RelAmple A L → Out.RelAmple B M → ∃ R : HomFixRep A B L M, QuasiCompact R.π ∧ IsSeparated R.π ∧ LocallyOfFiniteType R.π := by
  first | (exact @GlobalTheory.HomFixAff.exists_homFixRep_finiteType) | (exact GlobalTheory.HomFixAff.exists_homFixRep_finiteType) | (intros; apply GlobalTheory.HomFixAff.exists_homFixRep_finiteType  <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.mumford_formalEndomorphism_algebraic : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ b, FormalEnd U.toUnifPre a h' b → ∃ g : G ⟶ G, IsMonHom g ∧ ∀ e, (Over.pullback (thick R (maximalIdeal R) e)).map g = b e := by
  first | exact @GlobalTheory.Mum.formalEnd_algebraic | exact GlobalTheory.Mum.formalEnd_algebraic | (intros; apply GlobalTheory.Mum.formalEnd_algebraic <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open TopologicalSpace

namespace GlobalTheory.Mum.LBGal
open GlobalTheory.Mum.LBDesc

theorem lemD : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → IsGal ρ → ∀ (G' : Over (Sp R')) [GrpObj G'] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left) (act : Gal ρ → (G'.left ⟶ G'.left)), IsSemiAbelian G → IsGrpPullback G' G (spMap ρ) β → (∀ σ, IsGrpPullback G' G' (spMap (Gal.hom σ)) (act σ)) → (∀ σ, act σ ≫ β = β) → ∀ O : G.left.Opens, Function.Injective (β.app O).hom ∧ ∀ u : Γ(G'.left, β ⁻¹ᵁ O)ˣ, (∀ σ (h : β ⁻¹ᵁ O ≤ act σ ⁻¹ᵁ (β ⁻¹ᵁ O)), ((act σ).appLE _ _ h).hom u.val = u.val) → ∃ g : Γ(G.left, O)ˣ, pullU β O g = u := GlobalTheory.T.galoisBaseChange_semiAbelian_invariant_units_descend

theorem lemF : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → IsGal ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G'), ∀ (a : GalAct ρ hD U') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback G' G (spMap ρ) β → (∀ σ, a.act σ ≫ β = β) → ∃ (V : G.left → G.left.Opens) (T : ∀ (y : G.left) (k : U'.LG.L.ι), Γ(G'.left, β ⁻¹ᵁ V y ⊓ U'.LG.L.U k)ˣ), (∀ y, y ∈ V y) ∧ (∀ y k k', res (inf_le_left : β ⁻¹ᵁ V y ⊓ U'.LG.L.U k ⊓ (β ⁻¹ᵁ V y ⊓ U'.LG.L.U k') ≤ β ⁻¹ᵁ V y ⊓ U'.LG.L.U k) (T y k) = res (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) : β ⁻¹ᵁ V y ⊓ U'.LG.L.U k ⊓ (β ⁻¹ᵁ V y ⊓ U'.LG.L.U k') ≤ U'.LG.L.U k ⊓ U'.LG.L.U k') (U'.LG.L.g k k') * res (inf_le_right : β ⁻¹ᵁ V y ⊓ U'.LG.L.U k ⊓ (β ⁻¹ᵁ V y ⊓ U'.LG.L.U k') ≤ β ⁻¹ᵁ V y ⊓ U'.LG.L.U k') (T y k')) ∧ ∀ (y y' : G.left) (r : Γ(G'.left, β ⁻¹ᵁ (V y ⊓ V y'))ˣ), (∀ (z : G'.left) (k : U'.LG.L.ι), z ∈ β ⁻¹ᵁ (V y ⊓ V y') → z ∈ U'.LG.L.U k → gm (𝟙 G'.left) z _ r = gm (𝟙 G'.left) z _ (T y' k) * (gm (𝟙 G'.left) z _ (T y k))⁻¹) → ∀ σ (h : β ⁻¹ᵁ (V y ⊓ V y') ≤ a.act σ ⁻¹ᵁ (β ⁻¹ᵁ (V y ⊓ V y'))), ((a.act σ).appLE _ _ h).hom r.val = r.val := GlobalTheory.T.exists_galoisInvariant_local_frames_uniformisation

theorem eq_of_gm_inj {Z Y : Scheme.{0}} (p : Z ⟶ Y) (hp : ∀ V : Y.Opens, Function.Injective (p.app V).hom) {O : Y.Opens}
    {a b : Γ(Y, O)ˣ} (h : ∀ z : Z, p z ∈ O → gm (𝟙 Z ≫ p) z O a = gm (𝟙 Z ≫ p) z O b) : a = b := by
  have e : pullU p O a = pullU p O b := unit_ext fun z hz => by
    rw [gm_pull (𝟙 Z) p z O hz a, gm_pull (𝟙 Z) p z O hz b]
    exact h z hz
  exact Units.ext ((hp O) (congrArg Units.val e))

theorem isLB_descLB_inj {Z Y : Scheme.{0}} (p : Z ⟶ Y) (hp : ∀ V : Y.Opens, Function.Injective (p.app V).hom)
    (L' : LB Z) (hL' : L'.IsLB)
    (V : Y → Y.Opens) (hyV : ∀ y, y ∈ V y) (T : ∀ (y : Y) (k : L'.ι), Γ(Z, p ⁻¹ᵁ V y ⊓ L'.U k)ˣ)
    (g : ∀ y y', Γ(Y, V y ⊓ V y')ˣ)
    (key : ∀ {W : Scheme.{0}} (f : W ⟶ Z) (w : W) (y y' : Y) (k : L'.ι), p (f w) ∈ V y → p (f w) ∈ V y' →
      f w ∈ L'.U k → gm (f ≫ p) w ((descLB V g).U y ⊓ (descLB V g).U y') ((descLB V g).g y y') =
        gm f w _ (T y' k) * (gm f w _ (T y k))⁻¹) :
    (descLB V g).IsLB := {
  cover := eq_top_iff.2 fun y _ => Opens.mem_iSup.2 ⟨y, hyV y⟩
  g_self := fun y => eq_of_gm_inj p hp fun z hz => by
    obtain ⟨k, hk⟩ := exists_chart hL' z
    rw [gm_res (𝟙 Z ≫ p) z _ hz, map_one]
    exact (key (𝟙 Z) z y y k hz hz hk).trans (mul_inv_cancel _)
  cocycle := fun a b c => eq_of_gm_inj p hp fun z hz => by
    obtain ⟨k, hk⟩ := exists_chart hL' z
    rw [map_mul, gm_res (𝟙 Z ≫ p) z _ hz, gm_res (𝟙 Z ≫ p) z _ hz, gm_res (𝟙 Z ≫ p) z _ hz,
      key (𝟙 Z) z a b k hz.1.1 hz.1.2 hk, key (𝟙 Z) z b c k hz.1.2 hz.2 hk,
      key (𝟙 Z) z a c k hz.1.1 hz.2 hk]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel }

end GlobalTheory.Mum.LBGal

namespace GlobalTheory.Mum
open GlobalTheory.Mum.LBDesc GlobalTheory.Mum.LBGal

theorem unif_lb_descend_gal : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → IsGal ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G'), ∀ (a : GalAct ρ hD U') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback G' G (spMap ρ) β → (∀ σ, a.act σ ≫ β = β) → ∃ L : LB G.left, L.IsLB ∧ LBIso U'.LG.L (L.pull β) := by
  intro R _ _ _ hR R' _ _ _ ρ hρ hG D D' hD A' G' _ _ hG' U' a G _ _ β hGs hβ hact
  have hDl := lemD R hR R' ρ hρ hG G' G β a.act hGs hβ a.cart hact
  obtain ⟨V, T, hyV, hT, hinv⟩ := lemF R hR R' ρ hρ hG D D' hD A' G' hG' U' a G β hGs hβ hact
  have hL' : U'.LG.L.IsLB := U'.LG.isLB
  have hc : ∀ (y : G.left) {W : Scheme.{0}} (f : W ⟶ G'.left) (w : W) (k k' : U'.LG.L.ι), f w ∈ β ⁻¹ᵁ V y →
      f w ∈ U'.LG.L.U k → f w ∈ U'.LG.L.U k' →
      gm f w _ (T y k) = gm f w (U'.LG.L.U k ⊓ U'.LG.L.U k') (U'.LG.L.g k k') * gm f w _ (T y k') :=
    fun y _ f w k k' h hk hk' => gm_compat U'.LG.L _ (T y) (hT y) f w k k' h hk hk'
  choose r hr using fun y y' => ratio β U'.LG.L hL' (T y) (T y') (hc y) (hc y')
  have hri : ∀ y y' σ (h : β ⁻¹ᵁ (V y ⊓ V y') ≤ a.act σ ⁻¹ᵁ (β ⁻¹ᵁ (V y ⊓ V y'))),
      ((a.act σ).appLE _ _ h).hom (r y y').val = (r y y').val :=
    fun y y' => hinv y y' (r y y') (fun z k hz hk => hr y y' (𝟙 _) z k hz hk)
  choose g hg using fun y y' => (hDl (V y ⊓ V y')).2 (r y y') (hri y y')
  have key : ∀ {W : Scheme.{0}} (f : W ⟶ G'.left) (w : W) (y y' : G.left) (k : U'.LG.L.ι), β (f w) ∈ V y →
      β (f w) ∈ V y' → f w ∈ U'.LG.L.U k →
      gm (f ≫ β) w ((descLB V g).U y ⊓ (descLB V g).U y') ((descLB V g).g y y') =
        gm f w _ (T y' k) * (gm f w _ (T y k))⁻¹ := by
    intro W f w y y' k h1 h2 hk
    exact (gm_pull f β w (V y ⊓ V y') ⟨h1, h2⟩ (g y y')).symm.trans
      ((congrArg _ (hg y y')).trans (hr y y' f w k ⟨h1, h2⟩ hk))
  exact ⟨descLB V g, isLB_descLB_inj β (fun O => (hDl O).1) U'.LG.L hL' V hyV T g key, descIso β U'.LG.L V T g,
    isGen_descIso β U'.LG.L V T g hc key⟩

end GlobalTheory.Mum
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.MixRec

theorem injective_of_finite_int {k : Type} [CommRing k] [IsDomain k] [Module.Finite ℤ k]
    (σ : k →+* ℂ) : Function.Injective σ := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  have hker : RingHom.ker σ = ⊥ := by
    apply Ideal.eq_bot_of_comap_eq_bot (R := ℤ)
    rw [eq_bot_iff]
    intro n hn
    rw [Ideal.mem_comap, RingHom.mem_ker, eq_intCast, map_intCast, Int.cast_eq_zero] at hn
    simp [hn]
  intro a ha
  have : a ∈ RingHom.ker σ := ha
  rwa [hker, Ideal.mem_bot] at this

theorem exists_extension {k : Type} [CommRing k] [IsDomain k] [Module.Finite ℤ k]
    (K : Type) [Field K] [Algebra k K] [IsFractionRing k K] (σ : k →+* ℂ) :
    ∃ τ : K →+* ℂ, σ = τ.comp (algebraMap k K) :=
  ⟨IsFractionRing.lift (A := k) (K := K) (injective_of_finite_int σ),
    RingHom.ext fun x => (IsFractionRing.lift_algebraMap (K := K) (injective_of_finite_int σ) x).symm⟩

theorem side_symm : GlobalTheory.Published.Principalisation → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp k) (e : ℕ), IsArithVar p (e + 1) → ∀ (σ : k →+* ℂ) (L : Fin e → MLine p σ) (M N : MLine p σ) (s : M.B.Sec) (hs : genericPoint X ∈ nonzeroLocus s) (t : N.B.Sec) (ht : genericPoint X ∈ nonzeroLocus t), (∀ z : X, Order.coheight z = 1 → z ∈ nonzeroLocus s ∨ z ∈ nonzeroLocus t) → side N L (M.logSec s) (N.logSec t) (divOfSec M.φ.isLB s hs) = side M L (N.logSec t) (M.logSec s) (divOfSec N.φ.isLB t ht) := by
  intro hP k _ X _ _ p e h σ
  haveI := h.isDomain
  haveI := h.finite
  obtain ⟨K, _, _, _⟩ : ∃ (K : Type) (_ : Field K) (_ : Algebra k K), IsFractionRing k K :=
    ⟨FractionRing k, inferInstance, inferInstance, inferInstance⟩
  obtain ⟨τ, hτ⟩ := exists_extension K σ
  subst hτ
  intro L M N s hs t ht hcod
  obtain ⟨G, j, q, hp⟩ : ∃ (G : Scheme.{0}) (j : G ⟶ X) (q : G ⟶ Sp K),
      IsPullback j q p (spMap (algebraMap k K)) := ⟨_, _, _, IsPullback.of_hasPullback _ _⟩
  obtain ⟨hGi, hGn, hproj, hdim, hgen, -, hstalk, hcoh, -⟩ :=
    GlobalTheory.T.generic_fiber_arithmetic_variety_integral_projective k K X G p q j hp (e + 1) h
  obtain ⟨s', hs', hsl, hsm, hslog⟩ := GlobalTheory.T.exists_section_generic_fiber_pullback_local_iso k K X G p q j hp τ hstalk M s hs hgen
  obtain ⟨t', ht', htl, htm, htlog⟩ := GlobalTheory.T.exists_section_generic_fiber_pullback_local_iso k K X G p q j hp τ hstalk N t ht hgen
  have hcod' : ∀ z : G, Order.coheight z = 1 → z ∈ nonzeroLocus s' ∨ z ∈ nonzeroLocus t' := by
    intro z hz
    rw [hsl, htl]
    exact hcod (j z) ((hcoh z).trans hz)
  have hrec := GlobalTheory.T.arithReciprocity_noCommonDivisor_projective hP K G q τ e hproj hdim (fun i => (L i).bc hp.w τ) (M.bc hp.w τ)
    (N.bc hp.w τ) s' hs' t' ht' hcod'
  have e1 := GlobalTheory.T.reciprocitySide_eq_genericFibre_pullback k K X G p q j hp τ e h _ _ hsm N L (M.logSec s) (N.logSec t)
  have e2 := GlobalTheory.T.reciprocitySide_eq_genericFibre_pullback k K X G p q j hp τ e h _ _ htm M L (N.logSec t) (M.logSec s)
  have hsf : (M.bc hp.w τ).logSec s' = fun y => M.logSec s (bcPt hp.w τ y) := funext hslog
  have htf : (N.bc hp.w τ).logSec t' = fun y => N.logSec t (bcPt hp.w τ y) := funext htlog
  rw [hsf, htf] at hrec
  exact e1.symm.trans (hrec.trans e2)

end GlobalTheory.MixRec
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

theorem _root_.GlobalTheory.T.arith_nef_volume_upper_bound : GlobalTheory.Published.ArCalc → AmpleHS → SemiPull → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (L N : HermLB p) (a : ℝ), L.IsNef D → L.IsSelfInter a → ∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop, Real.log (((L.pow m).tens N).smallSec.ncard : ℝ) ≤ (a / (D + 1).factorial + ε) * (m : ℝ) ^ (D + 1) := by
  first | exact @GlobalTheory.NefUpper.main | exact GlobalTheory.NefUpper.main | (intros; apply GlobalTheory.NefUpper.main <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

theorem _root_.GlobalTheory.T.exists_mixedHeight_of_archimedean_integrals : ArchInteg → ArchRecip → (∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (q : Y ⟶ Sp k), IsAmb q → ∀ m : ℕ, ∃ T, IsMix q m T) := by
  first | exact @GlobalTheory.MixHt.exists_isMix_of_arch | exact GlobalTheory.MixHt.exists_isMix_of_arch | (intros; apply GlobalTheory.MixHt.exists_isMix_of_arch <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum


theorem _root_.GlobalTheory.T.exists_evenCubicalStructure_of_idempotentFactor_biextension : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) (F : Factor D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (inc : G ⟶ G') (pr : G' ⟶ G), IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → pr ≫ inc = oG.act F.e → ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁] (ρ₁ : R →+* R₁) (G₁ : Over (Sp R₁)) [GrpObj G₁] [IsCommMonObj G₁] (β₁ : G₁.left ⟶ G.left) (β₁₂ : (G2 G₁).left ⟶ (G2 G).left) (A₁ : PolAV (Sp (FractionRing R₁))) (gen₁ : (Over.pullback (jK R₁)).obj G₁ ≅ A₁.A), FinExt ρ₁ → IsGrpPullback G₁ G (spMap ρ₁) β₁ → Geo.Tor.IsSquare β₁ β₁₂ → IsMonHom gen₁.hom → ExtLam G₁ (A₁.L.pull gen₁.hom.left) (((abelian₂ G' U'.LG.L).pull (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left).pull β₁₂) → ∃ (R₉ : Type) (_ : CommRing R₉) (_ : IsDomain R₉) (_ : IsLocalRing R₉) (ρ₉ : R →+* R₉) (G₉ : Over (Sp R₉)) (_ : GrpObj G₉) (_ : IsCommMonObj G₉) (β₉ : G₉.left ⟶ G.left) (β₉₂ : (G2 G₉).left ⟶ (G2 G).left) (P₉ : GlobalTheory.UU.CP G₉) (A₉ : PolAV (Sp (FractionRing R₉))) (gen₉ : (Over.pullback (jK R₉)).obj G₉ ≅ A₉.A), FinExt ρ₉ ∧ IsGrpPullback G₉ G (spMap ρ₉) β₉ ∧ Geo.Tor.IsSquare β₉ β₉₂ ∧ IsSemiAbelian G₉ ∧ LBIso (abelian₂ G₉ P₉.L.L) ((abelian₂ G' U'.LG.L).pull (β₉₂ ≫ (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left)) ∧ EvenOn P₉ ∧ IsMonHom gen₉.hom ∧ LBIso (A₉.L.pull gen₉.hom.left) (P₉.L.L.pull (pullback.fst G₉.hom (jK R₉))) := by
  first | exact @GlobalTheory.Mum.exists_finExt_evenCP_of_factor_extLam | exact GlobalTheory.Mum.exists_finExt_evenCP_of_factor_extLam | (intros; apply GlobalTheory.Mum.exists_finExt_evenCP_of_factor_extLam <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

theorem _root_.GlobalTheory.T.idealDescent_thetaModel_to_component_traitOrders : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z), IsThetaCompact F z i → ∀ φ : InvFun ℤ, IsPolFan id g φ → ∀ W : Set Z, IsClopen W → IsIrreducible W → ∀ (W8 : Matrix (Fin 8) (Fin 8) ℤ) (X₁ : Setup F W8 i) (ι : ℕ) (J₁ : X₁.M.Z.IdealSheafData), 1 ≤ ι → Set.range X₁.π = W → (∀ x ∈ J₁.support, X₁.π x ∉ Set.range i) → (∀ (T : Trait F) (ξ₁ : Sp T.V ⟶ X₁.M.Z), jK T.V ≫ ξ₁ ≫ X₁.π = T.y ≫ i → ∃ a : ℕ, (a : ℝ) = ι * φ.evalZ T.β ∧ idlAlong J₁ ξ₁ = Ideal.span {T.ϖ ^ a}) → ∃ (d : ℕ) (J : Z.IdealSheafData), 1 ≤ d ∧ (∀ x ∈ J.support, x ∈ W ∧ x ∉ Set.range i) ∧ ∀ (T : Trait F) (ξ : Sp T.V ⟶ Z), jK T.V ≫ ξ = T.y ≫ i → ξ (closedPoint T.V) ∈ W → ∃ a : ℕ, (a : ℝ) = d * φ.evalZ T.β ∧ idlAlong J ξ = Ideal.span {T.ϖ ^ a} := by
  first | exact @GlobalTheory.PoincDown.idealDescent | exact GlobalTheory.PoincDown.idealDescent | (intros; apply GlobalTheory.PoincDown.idealDescent <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.conjugate_torsion_point_polarised_fibre_image : ∀ (g l : ℕ), l.Prime → Odd l → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → ∀ (V V₁ : Type) [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → IsUnit (l : V₁) → ∀ (Q : Data V), Q.g ≤ g → ∀ (ρ : V →+* V₁), Function.Injective ρ → ∀ (D : DegPre V₁) (e : (Fin 8 → Q.X) ≃+ D.X), SharpRef W Q ρ D e → ∀ (C : Type) (u : (Fin 8 → Q.X) → C → V₁) (mo : (Fin 8 → Q.X) → V₁), (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → IsThetaTerms D ((l ^ j) ^ 2) e (fun mu c => u mu c * mo mu) → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ mu c c', IsUnit (u mu c') → ∃ r ∈ k₀, ev (u mu c) = r * ev (u mu c')) → ∀ (o' : Type) [CommRing o'] (ζ' : o') (g' n' : ℕ) (F' : SFam g' n' ζ') (lam : Sp V ⟶ F'.X) (β : Q.B.left ⟶ F'.univ.A.left) (β₂ : (G2 Q.B).left ⟶ (G2 F'.univ.A).left), 1 ≤ n' → DefOver k₀ (spMap (ev.comp ρ) ≫ lam ≫ F'.s) → IsGrpPullback Q.B F'.univ.A lam β → IsSquare β β₂ → LBIso (abelian₂ Q.B Q.M.L) (F'.univ.P.pull β₂) → ∀ (φ₀₂ : (G2 ((Over.pullback (spMap (ev.comp ρ))).obj Q.B)).left ⟶ (G2 F'.univ.A).left), IsSquare (pullback.fst Q.B.hom (spMap (ev.comp ρ)) ≫ β) φ₀₂ → ∀ (σ : K ≃+* K), (∀ r ∈ k₀, σ r = r) → ∀ (a : Q.X) (p : Sp K ⟶ ((Over.pullback (spMap (ev.comp ρ))).obj Q.B).left), p ≫ pullback.fst Q.B.hom (spMap (ev.comp ρ)) = spMap (ev.comp ρ) ≫ (Q.c a).left → p ≫ pullback.snd Q.B.hom (spMap (ev.comp ρ)) = 𝟙 _ → ∃ (x' : Sp K ⟶ F'.X) (φ : ((Over.pullback (spMap (ev.comp ρ))).obj Q.B).left ⟶ F'.univ.A.left) (φ₂ : (G2 ((Over.pullback (spMap (ev.comp ρ))).obj Q.B)).left ⟶ (G2 F'.univ.A).left), x' ≫ F'.s = spMap (ev.comp ρ) ≫ lam ≫ F'.s ∧ IsGrpPullback ((Over.pullback (spMap (ev.comp ρ))).obj Q.B) F'.univ.A x' φ ∧ IsSquare φ φ₂ ∧ LBIso (F'.univ.P.pull φ₀₂) (F'.univ.P.pull φ₂) ∧ spMap σ.toRingHom ≫ p ≫ pullback.fst Q.B.hom (spMap (ev.comp ρ)) ≫ β = p ≫ φ := by
  first | exact @GlobalTheory.Poinc.Sep.conj_fibre_iso | exact GlobalTheory.Poinc.Sep.conj_fibre_iso | (intros; apply GlobalTheory.Poinc.Sep.conj_fibre_iso <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum.SecsAsm

theorem gs_scal_one {R : Type} [CommRing R] {Y Z : Scheme.{0}} (q : Y ⟶ Sp R) (p : Z ⟶ Y) (z : Z) :
    gs p z ⊤ (scal q 1) = 1 := by
  unfold scal
  rw [map_one, map_one, gs_eq p z ⊤ trivial, map_one, map_one]

theorem closed_pt (R : Type) [CommRing R] [IsLocalRing R] :
    spMap (residue R) (closedPoint (ResidueField R)) = closedPoint R :=
  IsLocalRing.comap_closedPoint (residue R)

theorem secs_exists (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (hB : Base R) (D : DegData R (maximalIdeal R))
    (C : LabCover D) : Nonempty (Secs C.toModif C.G C.P.L.L C.α) := by
  obtain ⟨Y⟩ : Nonempty (Ext D.toPre) := inferInstance
  obtain ⟨hsm, -, -, -, -⟩ := GlobalTheory.Mum.ext_smooth_affine_surj_terms R D.toPre Y
  obtain ⟨S, k₁, himm⟩ := GlobalTheory.T.exists_theta_immersion_torus_extension_projective R hB D Y
  obtain ⟨hth, hth0⟩ := GlobalTheory.T.exists_integralThetaFamily_prescribed_leadingTerm R hB D
  choose k₀ hk₀ using hth
  obtain ⟨⟨j₀, hdesc⟩, hdescθ⟩ := GlobalTheory.Mum.exists_secs_of_intFam R hB D C
  have hk : k₁ + ∑ a ∈ S, k₀ a ≤ C.n ^ (max j₀ (k₁ + ∑ a ∈ S, k₀ a)) :=
    (le_max_right _ _).trans (Nat.lt_pow_self C.n_prime.one_lt).le
  obtain ⟨Φ, hΦ⟩ := hdesc (max j₀ (k₁ + ∑ a ∈ S, k₀ a)) (le_max_left _ _)
  obtain ⟨N, α, b, τ, hτ, hατ, hI⟩ := himm _ ((Nat.le_add_right _ _).trans hk)
  have hF : ∀ i, ∃ F : IntFam (maximalIdeal R) D.toPre (C.n ^ (max j₀ (k₁ + ∑ a ∈ S, k₀ a))), F.Lead (α i) (b i) :=
    fun i => hk₀ (α i) _ (((Finset.single_le_sum (fun _ _ => Nat.zero_le _) (hατ i).1).trans
      (Nat.le_add_left _ _)).trans hk) (b i)
  choose F hFl using hF
  obtain ⟨bθ, τθ, y₀, hθt, hy₀c, hy₀⟩ := GlobalTheory.Mum.exists_term_nonzero_closed R hB D Y
  obtain ⟨F₁, hF₁⟩ := hth0 1 le_rfl bθ
  obtain ⟨θ, hθ⟩ := hdescθ F₁
  have hsm0 : Smooth ((Over.pullback (spMap (residue R))).obj Y.H).hom :=
    inferInstanceAs (Smooth (pullback.snd Y.H.hom (spMap (residue R))))
  have himm0 : IsImmersion (pullback.fst Y.H.hom (spMap (residue R)) ≫ GlobalTheory.ProjSpace.toProj Y.H.hom τ hτ) := by
    have : IsClosedImmersion (spMap (residue R)) := IsClosedImmersion.spec_of_surjective _ residue_surjective
    have : IsClosedImmersion (pullback.fst Y.H.hom (spMap (residue R))) := inferInstance
    infer_instance
  refine ⟨{ N := N, k := _, s := fun i => Φ (F i), θ := θ, Y := (Over.pullback (spMap (residue R))).obj Y.H
            smooth := hsm0
            j := pullback.fst Y.H.hom (spMap (residue R)) ≫ GlobalTheory.ProjSpace.toProj Y.H.hom τ hτ
            j_over := ?_
            imm := himm0
            O := pullback.fst Y.H.hom (spMap (residue R)) ⁻¹ᵁ nonzeroLocus τθ
            O_ne := ?_
            trait := ?_ }⟩
  · rw [Category.assoc, GlobalTheory.ProjSpace.toProj_str, pullback.condition]; rfl
  · obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := Y.H.hom) (g := spMap (residue R)) y₀
      (closedPoint _) (hy₀c.trans (closed_pt R).symm)
    exact ⟨z, show pullback.fst Y.H.hom (spMap (residue R)) z ∈ nonzeroLocus τθ by rw [hz]; exact hy₀⟩
  intro W _ _ _ hW φ ξ hφ hloc hξ
  obtain ⟨W', _, _, _, io, T, hio, hfin, hTφ, hTξ⟩ := C.exists_trait W hW φ ξ hφ hloc hξ
  obtain ⟨u, hu⟩ := hΦ W' T
  obtain ⟨uθ, huθ⟩ := hθ W' T
  choose σ hσE hσA using fun i => hu (F i)
  obtain ⟨θ', hθE, hθA⟩ := huθ
  obtain ⟨κ, e, hκ, he, hred⟩ := GlobalTheory.Mum.trait_lead_value R hB D C Y W' T
  have hκ' : κ.comp (residue R) = (residue W').comp (io.comp φ) := by rw [hκ, hTφ]
  refine ⟨W', _, inferInstance, inferInstance, io, T.G, inferInstance, T.β, σ, θ', κ, e, T.cdvr, hio, hfin,
    by rw [← hTξ]; exact T.cart, hκ', he, fun i Z p p' hpp z J hJ => ?_, fun Z p p' hpp z J hJ => ?_, ?_⟩
  · rw [hσA i Z p p' hpp z J hJ, gs_scal_one, _root_.one_mul]
  · rw [hθA Z p p' hpp z J hJ, gs_scal_one, _root_.one_mul]
  intro Ω _ p p' y hp hy
  have hval := hred (Sp Ω) p p' (y ≫ pullback.fst Y.H.hom (spMap (residue R))) hp
    (by rw [hy]; simp only [Category.assoc])
  have e1 : spMap (residue W') ≫ spMap (io.comp φ) = spMap κ ≫ spMap (residue R) := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hκ']
  have hw := Over.w e.hom
  have hbase : p' ≫ T.G.hom ≫ spMap (io.comp φ) = (y ≫ pullback.fst Y.H.hom (spMap (residue R))) ≫ Y.H.hom := by
    rw [hp]
    simp only [Category.assoc]
    rw [pullback.condition_assoc, e1, pullback.condition]
    rw [hy]
    simp only [Category.assoc]
    erw [pullback.condition_assoc]
    rw [← Category.assoc e.hom.left]
    erw [hw]
    rfl
  refine ⟨?_, fun x hx => ?_⟩
  · obtain ⟨-, hs, hP⟩ := GlobalTheory.Mum.toProj_secPull_of_sval R Ω C.G.left D.toPre.P.A.left T.G.left Y.H.left C.P.L.L D.toPre.P.L
      T.β Y.q.left _ N σ τ Y.H.hom hτ p' (y ≫ pullback.fst Y.H.hom (spMap (residue R))) C.P.L.isLB D.toPre.P.isLB
      (fun z J J' hJ hJ' => by
        obtain ⟨c, hc⟩ := hval _ u z J J' hJ hJ'
        exact ⟨c, fun i => hc (α i) (b i) (τ i) (F i) (σ i) (hατ i).2 (hFl i) (hσE i)⟩)
    rw [hbase]
    exact ⟨hs, hP.trans (by simp only [Category.assoc])⟩
  · choose J hJ using fun χ : Sp Ω ⟶ C.G.left => exists_chart C.P.L.isLB (χ x)
    choose J' hJ' using fun χ : Sp Ω ⟶ D.toPre.P.A.left => exists_chart D.toPre.P.isLB (χ x)
    obtain ⟨c, hc⟩ := hval 1 uθ x J J' hJ hJ'
    have h1 := hc 0 bθ τθ F₁ θ' hθt hF₁ hθE
    have hx' : (y ≫ pullback.fst Y.H.hom (spMap (residue R))) x ∈ nonzeroLocus τθ := hx
    have hu1 := (GlobalTheory.mem_nonzeroLocus_iff_pull τθ _ x (Good.mem hJ' _ _)).1 hx'
    refine (GlobalTheory.mem_nonzeroLocus_iff_pull θ' p' x (Good.mem hJ _ _)).2 ?_
    change IsUnit (sval θ' p' x J)
    rw [h1]
    exact c.isUnit.mul hu1

end GlobalTheory.Mum.SecsAsm

theorem GlobalTheory.Mum.exists_secs_finExt : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D), ∃ (R₁ : Type) (_ : CommRing R₁) (_ : IsDomain R₁) (_ : IsLocalRing R₁) (ρ : R →+* R₁) (D₁ : DegData R₁ (maximalIdeal R₁)) (C₁ : LabCover D₁), FinExt ρ ∧ Nonempty (IsPullDeg ρ D.toPre D₁.toPre) ∧ Nonempty (Secs C₁.toModif C₁.G C₁.P.L.L C₁.α) := by
  intro R _ _ _ hB D C
  obtain ⟨h, -, -⟩ := GlobalTheory.DegPullId.exists_isPullDeg_id_self R (maximalIdeal R) hB.1 D
  exact ⟨R, inferInstance, inferInstance, inferInstance, RingHom.id R, D, C,
    ⟨hB.1, Function.injective_id, RingHom.Finite.id R⟩, ⟨h⟩, GlobalTheory.Mum.SecsAsm.secs_exists R hB D C⟩
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc

theorem exists_isLab : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (c : CTrait X₁ p z₁), ∃ yy : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) (Fin 8 → c.T.D.toPre.X), IsLab X₁ ε₁ c yy := by
  intro g n F W Z i X₁ hg hn hodd himm he8 hth hproj ε₁ hdiag p _ z₁ c
  obtain ⟨c₀, hc, R', fg, frac, hth', hev, ρ', ε', u', hsame, hi₀, hle, hdiag', y₀, hy₀, hpt, hint⟩ :=
    GlobalTheory.T.thetaSystem_rechart_affineOpen_at_classicalTrait g n F W Z i X₁ hg hn hodd himm he8 hth hproj ε₁ hdiag p z₁ c
  obtain ⟨u, l, j, hq, hcong⟩ :=
    GlobalTheory.T.exists_labelled_uniformisedModel_thetaSystem_trait g n F W he8 X₁.o₁ X₁.Ω₁ _ ρ' ε' u' hdiag' p y₀ c.T c.ι c.int hpt hint
  let jm : ModN (X₁.S.r * X₁.S.N) u.D.toPre.X →+ ModN (X₁.S.r * X₁.S.N) (Fin 8 → c.T.D.toPre.X) :=
    QuotientAddGroup.map _ _ j.toAddMonoidHom (by
      rintro _ ⟨x, rfl⟩
      exact ⟨j x, by simp⟩)
  refine ⟨jm.comp l.yy, c₀, hc, R', fg, frac, hth', hev, ρ', ε', hsame, hi₀, hle, y₀, hy₀, u, l, j, hq, ?_, hcong⟩
  intro a χ ha
  simp only [AddMonoidHom.comp_apply, ha, jm]
  rfl

end GlobalTheory.Poinc
end
