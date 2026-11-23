module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1802
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3366
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIvDOfDefinite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3086
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStalkElementsApproxLeadingTermQuotients
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle665
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle006
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle536
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle018
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle019
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3351
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3365
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle029
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2446
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1226
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1378
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3328
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3360
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle014
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle042
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3361
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.QuasiAffine
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3104
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle067
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle074

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

namespace GlobalTheory.FormalAlg

theorem cross_cancel {G : Type} [CommGroup G] (a a' g : G) (p q : ℤ) :
    (a' * g ^ q) ^ p * ((a * g ^ p) ^ q)⁻¹ = a' ^ p * (a ^ q)⁻¹ := by
  rw [mul_zpow, mul_zpow, ← zpow_mul, ← zpow_mul, mul_comm q p]
  group

theorem lbIso_pw_cross : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R → ∀ (X : Over (Spec (CommRingCat.of R))), IsProper X.hom → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (b : ∀ e, (Y e).left ⟶ X.left), (∀ e, IsPullback (b e) (Y e).hom X.hom (thick R I e)) → (∀ e, β e ≫ b (e + 1) = b e) → ∀ (N : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (N e) ((N (e + 1)).pull (β e))), (∀ e, (N e).IsLB) → ∀ (p q : ℤ) (A A' : LB X.left), A.IsLB → A'.IsLB → ∀ (w : ∀ e, LB.Iso (GlobalTheory.AbLaw.pw (N e) p) (A.pull (b e))) (w' : ∀ e, LB.Iso (GlobalTheory.AbLaw.pw (N e) q) (A'.pull (b e))), (∀ e, (w e).IsGen ∧ (w' e).IsGen) → (∀ e z k l' l, b e z ∈ A.U k → β e z ∈ (N (e + 1)).U l' → z ∈ (N e).U l → Geo.Tor.gw (w e) (𝟙 _) z k l = Geo.Tor.gw (w (e + 1)) (β e) z k l' * Geo.Tor.gw (v e) (𝟙 _) z l' l ^ p) → (∀ e z k l' l, b e z ∈ A'.U k → β e z ∈ (N (e + 1)).U l' → z ∈ (N e).U l → Geo.Tor.gw (w' e) (𝟙 _) z k l = Geo.Tor.gw (w' (e + 1)) (β e) z k l' * Geo.Tor.gw (v e) (𝟙 _) z l' l ^ q) → LBIso (GlobalTheory.AbLaw.pw A q) (GlobalTheory.AbLaw.pw A' p) := by
  intro R _ _ I hI X hX Y β b hb hβ N v hN p q A A' hA hA' w w' hg hv hv'
  choose c hc hcg using fun e =>
    GlobalTheory.T.exists_iso_cross_powers_of_pullback_powers X.left (Y e).left (b e) A A' (N e) p q (w e) (w' e) hA hA' (hN e) (hg e).1 (hg e).2
  refine GlobalTheory.T.lineBundleIso_of_compatible_adic_reductions R I hI X hX Y β b hb hβ (pw A q) (pw A' p) (isLB_pw hA q) (isLB_pw hA' p) c hc ?_
  intro e z k k' hk hk'
  obtain ⟨l, hl⟩ := exists_chart (hN e) z
  obtain ⟨l', hl'⟩ := exists_chart (hN (e + 1)) (β e z)
  have hz : b (e + 1) (β e z) = b e z := by
    rw [← Scheme.Hom.comp_apply, hβ e]
  have h1 := hcg (e + 1) (Y e).left (β e) z k k' l' (hz ▸ hk) (hz ▸ hk') hl'
  have h0 := hcg e (Y e).left (𝟙 _) z k k' l hk hk' hl
  rw [h1, h0, hv e z k l' l hk hl' hl, hv' e z k' l' l hk' hl' hl]
  exact (cross_cancel _ _ _ p q).symm

end GlobalTheory.FormalAlg
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep

namespace GlobalTheory.CorrCover

theorem exists_corr : ∀ (Z M S₁ : Scheme.{0}) [IsIntegral M] [IsIntegral S₁] (sM : M ⟶ Sp ℤ) (p₁ : S₁ ⟶ M) (g : M ⟶ Z) (J : Z.IdealSheafData), LocallyOfFiniteType sM → QuasiCompact sM → Flat (p₁ ≫ sM) → Geo.Tor.IsNormalScheme S₁ → IsProper p₁ → IsDominant p₁ → FinalTheorems.EffCartier (J.comap (p₁ ≫ g)) → ∀ (U₁ : S₁.Opens), (U₁ : Set S₁).Nonempty → ∀ (z₁ : M) (R : Type) [CommRing R] [IsLocalRing R] (ev : M.presheaf.stalk z₁ →+* R), IsLocalHom ev → ∀ ξ₁ : Sp R ⟶ S₁, ξ₁ ≫ p₁ = spMap ev ≫ M.fromSpecStalk z₁ → ∃ g₀ : R, idlAlong (J.comap (p₁ ≫ g)) ξ₁ = Ideal.span {g₀} ∧ ∀ D e : ℕ, ∃ e' : ℕ, ∀ f : M.presheaf.stalk z₁, (∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (maximalIdeal V) V → ∀ (ξ' : Sp V ⟶ S₁) (ev' : M.presheaf.stalk z₁ →+* V), IsLocalHom ev' → spMap ev' ≫ M.fromSpecStalk z₁ = ξ' ≫ p₁ → Set.range (jK V ≫ ξ') ⊆ (U₁ : Set S₁) → ev' f ∈ idlAlong (J.comap (p₁ ≫ g)) ξ' ^ D ⊔ ((maximalIdeal (M.presheaf.stalk z₁)).map ev') ^ e') → ∃ h ∈ (Scheme.stalkClosedPointTo ξ₁).hom.range, ev f - h * g₀ ^ D ∈ maximalIdeal R ^ e := by
  intro Z M S₁ _ _ sM p₁ g J h1 h2 h3 hN h5 h6 hEC U₁ hU z₁ R _ _ ev hev ξ₁ hξ
  haveI := h1; haveI := h2; haveI := h3; haveI := h5; haveI := h6; haveI := hev
  set I := J.comap (p₁ ≫ g) with hIdef
  set x₁ := ξ₁ (closedPoint R)
  set ψ := (Scheme.stalkClosedPointTo ξ₁).hom
  obtain ⟨W, f₀, hx, -, hI⟩ := hEC x₁
  have st : ∀ k : ℕ, FinalTheorems.stalkId (I ^ k) x₁ = Ideal.span {(S₁.presheaf.germ _ x₁ hx).hom f₀ ^ k} := fun k => by
    rw [ReciprocityTheory.AnForm.R.ds_stalkId_eq_map _ W x₁ hx, Scheme.IdealSheafData.ideal_pow, Pi.pow_apply, hI,
      Ideal.span_singleton_pow, Ideal.map_span, Set.image_singleton, map_pow]
  refine ⟨ψ ((S₁.presheaf.germ _ x₁ hx).hom f₀), ?_, ?_⟩
  · have := st 1
    rw [pow_one, pow_one] at this
    rw [idlAlong, this, Ideal.map_span, Set.image_singleton]
  intro D e
  obtain ⟨E, hE⟩ := EffCartierData.exists_idealSheaf_eq (CoverElements.effCartier_pow hEC D)
  obtain ⟨e', he'⟩ := GlobalTheory.T.exists_correction_approximate_ideal_sections M S₁ sM p₁ hN U₁ hU E z₁ e
  refine ⟨e', fun f hf => ?_⟩
  have hm := he' f (fun V _ _ _ _ hc ξ' ev' hl hc' hr => by
    rw [hE, TorRef.idlAlong_pow]
    exact hf V hc ξ' ev' hl hc' hr)
  obtain ⟨f₁, hf₁, r, hr, rfl⟩ := Submodule.mem_sup.1 hm
  obtain ⟨u, hu, hψ⟩ := CoverElements.exists_stalk_of_map p₁ E.idealSheaf ξ₁ ev hξ hf₁
  rw [hE, st D] at hu
  obtain ⟨h', rfl⟩ := Ideal.mem_span_singleton'.1 hu
  refine ⟨ψ h', ⟨h', rfl⟩, ?_⟩
  have hmR : (maximalIdeal (M.presheaf.stalk z₁)).map ev ≤ maximalIdeal R :=
    Ideal.map_le_iff_le_comap.2 fun x hx => (IsLocalRing.mem_maximalIdeal _).2 fun hu => hx (isUnit_of_map_unit ev x hu)
  have : ev r ∈ maximalIdeal R ^ e :=
    Ideal.pow_right_mono hmR e (by rw [← Ideal.map_pow]; exact Ideal.mem_map_of_mem ev hr)
  rw [map_add (f := _), ← hψ, map_mul, map_pow]
  convert this using 1
  exact add_sub_cancel_left _ _

end GlobalTheory.CorrCover
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC TensorProduct

theorem _root_.GlobalTheory.T.etaleCohomology_equiv_strictHenselian_line_point : ∀ (q : ℕ) [NeZero q] (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T], AIC T → IsUnit (q : T) → ∀ (O : Type) [CommRing O] [Algebra (Polynomial T) O] [Algebra T O] [IsScalarTower T (Polynomial T) O], SH O → IndEt (Polynomial T) O → ∀ i : ℤ, Eqv _ (spMap (Algebra.TensorProduct.includeRight (R := T) (A := FractionRing T) (B := O)).toRingHom) (tw q i) := by
  first | (exact @GlobalTheory.EtC.LineLocal.eqv_local) | (exact GlobalTheory.EtC.LineLocal.eqv_local) | (intros; apply GlobalTheory.EtC.LineLocal.eqv_local  <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.exists_local_representing_scheme_homFixedPullback : ∀ (Rg : Type) [CommRing Rg] [IsNoetherianRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left), IsAbelianScheme A → IsAbelianScheme B → L.IsLB → M.IsLB → Out.Rigidified A L → Out.Rigidified B M → Out.RelAmple A L → Out.RelAmple B M → ∀ p : Sp Rg, ∃ U : (Sp Rg).Opens, p ∈ U ∧ ∃ (AU : Over (U).toScheme) (_ : GrpObj AU) (BU : Over (U).toScheme) (_ : GrpObj BU) (φA : AU.left ⟶ A.left) (φB : BU.left ⟶ B.left), IsGrpPullback AU A (U).ι φA ∧ IsGrpPullback BU B (U).ι φB ∧ ∃ R : HomFixRep AU BU (L.pull φA) (M.pull φB), QuasiCompact R.π ∧ IsSeparated R.π ∧ LocallyOfFiniteType R.π := by
  first | (exact @GlobalTheory.HomFixLocal.exists_local_homFixRep) | (exact GlobalTheory.HomFixLocal.exists_local_homFixRep) | (intros; apply GlobalTheory.HomFixLocal.exists_local_homFixRep  <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.thickening_eq_of_generic_section_ratios : (∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ b, FormalEnd U.toUnifPre a h' b → ∀ (N : ℕ) (S : ∀ k : ℕ, H0 U.LG.L k → H0 U.LG.L (N * k)), (∀ (k e : ℕ) (s₁ s₂ : H0 U.LG.L k), SecRatioEq U.LG.L ((b e).left ≫ (fstG (maximalIdeal R) e G).left) (fstG (maximalIdeal R) e G).left s₁ s₂ (S k s₁) (S k s₂)) → (∀ k : ℕ, 3 ≤ k → ∃ s₀ : H0 U.LG.L k, SecCoNonzero U.LG.L ((b 0).left ≫ (fstG (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left s₀ (S k s₀)) → ∀ φ : (Over.pullback (jK R)).obj G ⟶ (Over.pullback (jK R)).obj G, (∀ (k : ℕ) (s₁ s₂ : H0 U.LG.L k), SecRatioEq U.LG.L (φ.left ≫ pullback.fst G.hom (jK R)) (pullback.fst G.hom (jK R)) s₁ s₂ (S k s₁) (S k s₂)) → ∀ g : G ⟶ G, IsMonHom g → (Over.pullback (jK R)).map g = φ → ∀ e, (Over.pullback (thick R (maximalIdeal R) e)).map g = b e) := by
  first | exact @GlobalTheory.Mum.thick_eq_of_ratios | exact GlobalTheory.Mum.thick_eq_of_ratios | (intros; apply GlobalTheory.Mum.thick_eq_of_ratios <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke

namespace GlobalTheory.UPel.HT.Hecke

theorem exists_isHeckeMap : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsNoetherianRing R]
    (b : Base D R) (g : D.La →ₗ[D.O] D.La) (c k N : ℕ), c.Coprime p → k.Coprime p → 3 ≤ N → N.Coprime p →
    (∀ x y, D.EF (g x) (g y) = c * D.EF x y) → (∀ x, ∃ y, g y = k • x) → c ∣ k ^ 2 →
    ∀ (M : Model b N) (M' : Model b (N * k)), ∃ π : M'.X ⟶ M.X, IsHeckeMap g c k N M.toRepFam M'.toRepFam π := by
  intro p _ D R _ _ b g c k N hc hk hN hNp hEF hg hck M M'
  obtain ⟨o', ψ, hψ⟩ := GlobalTheory.T.exists_primeToP_hecke_translate_harrisTaylor p D R b g c k N hc hk hN hNp hEF hg hck M'.X M'.s M'.univ
  obtain ⟨π, ⟨hπ, hm⟩, -⟩ := M.toRepFam.rep M'.X M'.s o'
  exact ⟨π, hπ, o', ψ, hψ, hm⟩

end GlobalTheory.UPel.HT.Hecke
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem unif_lb_frames_gal : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → IsGal ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G'), ∀ (a : GalAct ρ hD U') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback G' G (spMap ρ) β → (∀ σ, a.act σ ≫ β = β) → ∃ (V : G.left → G.left.Opens) (T : ∀ (y : G.left) (k : U'.LG.L.ι), Γ(G'.left, β ⁻¹ᵁ V y ⊓ U'.LG.L.U k)ˣ), (∀ y, y ∈ V y) ∧ (∀ y k k', res (inf_le_left : β ⁻¹ᵁ V y ⊓ U'.LG.L.U k ⊓ (β ⁻¹ᵁ V y ⊓ U'.LG.L.U k') ≤ β ⁻¹ᵁ V y ⊓ U'.LG.L.U k) (T y k) = res (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) : β ⁻¹ᵁ V y ⊓ U'.LG.L.U k ⊓ (β ⁻¹ᵁ V y ⊓ U'.LG.L.U k') ≤ U'.LG.L.U k ⊓ U'.LG.L.U k') (U'.LG.L.g k k') * res (inf_le_right : β ⁻¹ᵁ V y ⊓ U'.LG.L.U k ⊓ (β ⁻¹ᵁ V y ⊓ U'.LG.L.U k') ≤ β ⁻¹ᵁ V y ⊓ U'.LG.L.U k') (T y k')) ∧ ∀ (y y' : G.left) (r : Γ(G'.left, β ⁻¹ᵁ (V y ⊓ V y'))ˣ), (∀ (z : G'.left) (k : U'.LG.L.ι), z ∈ β ⁻¹ᵁ (V y ⊓ V y') → z ∈ U'.LG.L.U k → gm (𝟙 G'.left) z _ r = gm (𝟙 G'.left) z _ (T y' k) * (gm (𝟙 G'.left) z _ (T y k))⁻¹) → ∀ σ (h : β ⁻¹ᵁ (V y ⊓ V y') ≤ a.act σ ⁻¹ᵁ (β ⁻¹ᵁ (V y ⊓ V y'))), ((a.act σ).appLE _ _ h).hom r.val = r.val := by
  intro R _ _ _ hB R' _ _ _ ρ hF hG D D' hD A' G' _ _ hS' U' a G _ _ β hS hβ hact
  have key : ∀ y : G.left, ∃ V : G.left.Opens, y ∈ V ∧ ∃ T : ∀ k : U'.LG.L.ι, Γ(G'.left, β ⁻¹ᵁ V ⊓ U'.LG.L.U k)ˣ, IsFrameOver U'.LG.L (β ⁻¹ᵁ V) T ∧ ∀ (σ : Gal ρ) (h : IsPullDeg (Gal.hom σ) D'.toPre D'.toPre) (bc : G' ≅ (Over.pullback (specOf (Gal.hom σ))).obj G'), bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ)) = a.act σ → ∀ hP : IsPullUnif (Gal.hom σ) h bc U' U', PullOver hD h → FrameCarried U'.LG.L (β ⁻¹ᵁ V) T _ (Classical.choose hP.lg) := by
    intro y
    by_cases hy : G.hom y = closedPoint R
    · exact GlobalTheory.T.exists_carried_frame_near_closedFibre R hB R' ρ hF hG D D' hD A' G' hS' U' a G β hS hβ hact y hy
    · exact GlobalTheory.T.exists_carried_frame_off_closedFibre R hB R' ρ hF hG D D' hD A' G' hS' U' a G β hS hβ hact y hy
  choose V hV T hT hI using key
  refine ⟨V, T, hV, hT, ?_⟩
  intro y y' r hr σ h
  obtain ⟨hh, bc, hf, hP, hPO⟩ := a.unif σ
  have i₁ := hI y σ hh bc hf hP hPO
  have i₂ := hI y' σ hh bc hf hP hPO
  revert h
  rw [← hf]
  intro h
  exact FrameCarried.ratio_fixed U'.LG.isLB i₁ i₂ (fun z (hz : z ∈ β ⁻¹ᵁ (V y ⊓ V y')) => hz.1)
    (fun z (hz : z ∈ β ⁻¹ᵁ (V y ⊓ V y')) => hz.2) r hr h

end GlobalTheory.Mum
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.isDualAbelianSchemePoincare_swap : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B] (P : LB (A ⊗ B).left), IsAbelianScheme A → IsAbelianScheme B → DimLe A B → IsDual A B P → IsDual B A (swap P) := by
  first | exact @GlobalTheory.BidualAbelian.isDual_swap | exact GlobalTheory.BidualAbelian.isDual_swap | (intros; apply GlobalTheory.BidualAbelian.isDual_swap <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

set_option autoImplicit false

namespace GlobalTheory.Mix

theorem isNoetherian_of_locallyNoetherian_projOverField {F : Type} [Field F] {X : Scheme.{0}} [IsLocallyNoetherian X] {p : X ⟶ Sp F}
    (hproj : IsProjOver p) : AlgebraicGeometry.IsNoetherian X := by
  obtain ⟨n, i, hi, hpi⟩ := hproj
  have := isProper_str F n
  have : IsProper p := hpi ▸ inferInstance
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  exact {}

theorem infinite_of_ringHom_complex {F : Type} [Field F] (σ : F →+* ℂ) : Infinite F := by
  haveI : CharZero F := σ.charZero
  exact Infinite.of_injective (Nat.cast : ℕ → F) Nat.cast_injective

theorem reciprocity_of_generated_right (hP : GlobalTheory.Published.Principalisation) (F : Type) [Field F] (X : Scheme.{0})
    [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp F) (σ : F →+* ℂ) (e : ℕ) (hproj : IsProjOver p)
    (hdim : topologicalKrullDim X = (e + 1 : ℕ)) (L : Fin e → MLine p σ) (M N : MLine p σ) (s : M.B.Sec)
    (hs : genericPoint X ∈ nonzeroLocus s) (t : N.B.Sec) (ht : genericPoint X ∈ nonzeroLocus t)
    (hcod : ∀ z : X, Order.coheight z = 1 → z ∈ nonzeroLocus s ∨ z ∈ nonzeroLocus t)
    (hN : ∃ (n : ℕ) (u : Fin n → N.B.Sec), ⨆ i, nonzeroLocus (u i) = ⊤) :
    side N L (M.logSec s) (N.logSec t) (divOfSec M.φ.isLB s hs) =
      side M L (N.logSec t) (M.logSec s) (divOfSec N.φ.isLB t ht) := by
  haveI := isNoetherian_of_locallyNoetherian_projOverField hproj
  haveI := infinite_of_ringHom_complex σ
  let S : Set X := {genericPoint X} ∪ {z | Order.coheight z = 1 ∧ z ∉ nonzeroLocus t}
  have hS : S.Finite := (Set.finite_singleton _).union (GlobalTheory.T.finite_coheight_one_notMem_of_genericPoint_mem X (nonzeroLocus t) ht)
  obtain ⟨A, hA, a, hAgen, hMAgen, haS⟩ := GlobalTheory.T.exists_generated_twist_section_nonvanishing_finite_set F X p hproj M.B M.φ.isLB S hS
  obtain ⟨φ, hφ, -⟩ := GlobalTheory.weight_cInf_semiPos_of_generated F X p σ A hA hAgen
  let A' : MLine p σ := ⟨A, φ, hφ⟩
  have ha : genericPoint X ∈ nonzeroLocus a := haS _ (Or.inl rfl)
  have haz : ∀ z : X, Order.coheight z = 1 → z ∉ nonzeroLocus t → z ∈ nonzeroLocus a :=
    fun z hz hzt => haS z (Or.inr ⟨hz, hzt⟩)
  obtain ⟨s₁, h₁, hloc, hadd⟩ := GlobalTheory.T.reciprocityDefect_add_bundleSection hP F X p σ e hproj hdim L M A' N s hs a ha t ht (by
    intro z hz
    by_cases hzt : z ∈ nonzeroLocus t
    · exact Or.inr hzt
    · exact Or.inl ⟨(hcod z hz).resolve_right hzt, haz z hz hzt⟩)
  have h0A := GlobalTheory.T.reciprocity_sections_generatedBundles hP F X p σ e hproj hdim L A' N a ha t ht (by
    intro z hz
    by_cases hzt : z ∈ nonzeroLocus t
    · exact Or.inr hzt
    · exact Or.inl (haz z hz hzt)) hAgen hN
  have h0MA := GlobalTheory.T.reciprocity_sections_generatedBundles hP F X p σ e hproj hdim L (M.tens A') N s₁ h₁ t ht (by
    intro z hz
    by_cases hzt : z ∈ nonzeroLocus t
    · exact Or.inr hzt
    · left
      rw [hloc]
      exact ⟨(hcod z hz).resolve_right hzt, haz z hz hzt⟩) hMAgen hN
  linarith

theorem reciprocity_of_noCommonDivisor : GlobalTheory.Published.Principalisation → ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp F) (σ : F →+* ℂ) (e : ℕ), IsProjOver p → topologicalKrullDim X = (e + 1 : ℕ) → ∀ (L : Fin e → MLine p σ) (M N : MLine p σ) (s : M.B.Sec) (hs : genericPoint X ∈ nonzeroLocus s) (t : N.B.Sec) (ht : genericPoint X ∈ nonzeroLocus t), (∀ z : X, Order.coheight z = 1 → z ∈ nonzeroLocus s ∨ z ∈ nonzeroLocus t) → side N L (M.logSec s) (N.logSec t) (divOfSec M.φ.isLB s hs) = side M L (N.logSec t) (M.logSec s) (divOfSec N.φ.isLB t ht) := by
  intro hP F _ X _ _ p σ e hproj hdim L M N s hs t ht hcod
  haveI := isNoetherian_of_locallyNoetherian_projOverField hproj
  haveI := infinite_of_ringHom_complex σ
  let S : Set X := {genericPoint X} ∪ {z | Order.coheight z = 1 ∧ z ∉ nonzeroLocus s}
  have hS : S.Finite := (Set.finite_singleton _).union (GlobalTheory.T.finite_coheight_one_notMem_of_genericPoint_mem X (nonzeroLocus s) hs)
  obtain ⟨A, hA, a, hAgen, hNAgen, haS⟩ := GlobalTheory.T.exists_generated_twist_section_nonvanishing_finite_set F X p hproj N.B N.φ.isLB S hS
  obtain ⟨φ, hφ, -⟩ := GlobalTheory.weight_cInf_semiPos_of_generated F X p σ A hA hAgen
  let A' : MLine p σ := ⟨A, φ, hφ⟩
  have ha : genericPoint X ∈ nonzeroLocus a := haS _ (Or.inl rfl)
  have haz : ∀ z : X, Order.coheight z = 1 → z ∉ nonzeroLocus s → z ∈ nonzeroLocus a :=
    fun z hz hzs => haS z (Or.inr ⟨hz, hzs⟩)
  obtain ⟨t₁, h₁, hloc, hadd⟩ := GlobalTheory.T.reciprocityDefect_add_bundleSection hP F X p σ e hproj hdim L N A' M t ht a ha s hs (by
    intro z hz
    by_cases hzs : z ∈ nonzeroLocus s
    · exact Or.inr hzs
    · exact Or.inl ⟨(hcod z hz).resolve_left hzs, haz z hz hzs⟩)
  have h0A := reciprocity_of_generated_right hP F X p σ e hproj hdim L M A' s hs a ha (by
    intro z hz
    by_cases hzs : z ∈ nonzeroLocus s
    · exact Or.inl hzs
    · exact Or.inr (haz z hz hzs)) hAgen
  have h0NA := reciprocity_of_generated_right hP F X p σ e hproj hdim L M (N.tens A') s hs t₁ h₁ (by
    intro z hz
    by_cases hzs : z ∈ nonzeroLocus s
    · exact Or.inl hzs
    · right
      rw [hloc]
      exact ⟨(hcod z hz).resolve_left hzs, haz z hz hzs⟩) hNAgen
  linarith

end GlobalTheory.Mix
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

theorem _root_.GlobalTheory.T.arith_log_small_sections_upper_bound : GlobalTheory.Published.ArCalc → AmpleHS → SemiPull → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p) (x : Fin D → X.functionField) (β : ℝ) (q : ℕ), AlgebraicIndependent ℤ x → (∀ S : Finset (Fin D), ∏ i ∈ S, x i ∈ P.Bl 0 1 1) → (P.L.tens P.A).IsNef D → (P.L.tens P.A).IsSelfInter β → 3 ≤ q → P.lc 1 0 1 ≤ bound D q β (gdeg (P.L.tens P.A) D) := by
  first | exact @GlobalTheory.HSNef.lc_le_bound | exact GlobalTheory.HSNef.lc_le_bound | (intros; apply GlobalTheory.HSNef.lc_le_bound <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

theorem _root_.GlobalTheory.T.isMixedHeightByInduction_succ : ArchInteg → ArchRecip → ∀ m : ℕ, (∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (q : Y ⟶ Sp k), IsAmb q → ∃ T, IsMix q m T) → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k), IsAmb p → ∃ T, IsMix p (m + 1) T := by
  first | exact @GlobalTheory.MixHt.Step.isMix_succ | exact GlobalTheory.MixHt.Step.isMix_succ | (intros; apply GlobalTheory.MixHt.Step.isMix_succ <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_siegelModuli_trait_through_compactification_pt : ∀ {g n : ℕ} (F : SFam g n (zetaAway n)) (S : Scheme.{0}) (s : S ⟶ Sp (cycAway n)) [LocallyOfFiniteType s] [IsLocallyNoetherian S] (j : F.X ⟶ S) [IsOpenImmersion j], 3 ≤ n → Dense (Set.range j) → j ≫ s = F.s → ∀ x : S, ∃ (T : GlobalTheory.Poinc.Trait F) (ξT : Sp T.V ⟶ S) (b : cycAway n →+* T.V), ξT (closedPoint T.V) = x ∧ jK T.V ≫ ξT = T.y ≫ j ∧ ξT ≫ s = spMap b := by
  first | exact @GlobalTheory.TChart.exists_trait_at | exact GlobalTheory.TChart.exists_trait_at | (intros; apply GlobalTheory.TChart.exists_trait_at <;> assumption)
end
