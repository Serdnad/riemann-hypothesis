module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle211
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3401
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2672
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3426
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2832
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3115
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2951
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2831
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3226
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle007
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenModelEqGenericFibre
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle019
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3267
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle706
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorTypeTjCorrespondenceTargetFiniteEtal
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3416
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlobalSectionAngehrnSiuInductiveStep
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle064
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2820
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2788
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3424
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1860
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1739
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1617
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1503
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3300
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3301
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2860
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
import Mathlib.Tactic.Basify
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle546
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle041

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

namespace GlobalTheory.ZarhinFam

theorem exists_zarhin_object : ∀ (h M d : ℕ), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → ∃ (jl : (Fin h ⊕ Fin h → ℤ) →+ (Fin (8 * h) ⊕ Fin (8 * h) → ℤ)) (n : ℕ) (o : Fin n → GlobalTheory.ZarhinFam.ord d) (κ : Fin n → (Fin (8 * h) ⊕ Fin (8 * h) → ℤ) →+ (Fin h ⊕ Fin h → ℤ)), ∀ (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t), IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → ∃ (z : SiegPre (8 * h) M (zetaAway M) t) (act : GlobalTheory.ZarhinFam.ord d → (z.A ⟶ z.A)), z.Principal ∧ IsRAct z.A act ∧ Adj z.A z.P (GlobalTheory.ZarhinFam.bar d) act ∧ ZRel (GlobalTheory.ZarhinFam.idem d) jl o κ c z act := by
  intro h M d h1 hM hodd hd hcop
  obtain ⟨κ, hκ⟩ := GlobalTheory.T.exists_zarhinSymplecticTransfer h M d h1 hM hodd hd hcop
  refine ⟨GlobalTheory.ZarhinFam.jlMap h, 8, GlobalTheory.ZarhinFam.oMat d, κ, fun S t c hdu hk => ?_⟩
  obtain ⟨B, _, _, Q, la, mu, hZ⟩ := GlobalTheory.T.exists_zarhin_data h M d S t c h1 hM hodd hd hcop hdu hk
  obtain ⟨r1, r2, sy⟩ := GlobalTheory.T.zarhinBundle_rigidified_symmetric h M d S t c B Q la mu hZ h1 hM hodd hd hcop hdu hk
  obtain ⟨la1, la2⟩ := GlobalTheory.T.zarhinLevel_additive_killed_by_level h M d S t c B Q la mu hZ h1 hM hodd hd hcop hdu hk κ hκ
  have hab : IsAbelianScheme (GlobalTheory.ZarhinFam.Zob c.A B) :=
    AbelianSchemeGerms.isAbelianScheme_tensor _ _ (AbelianSchemeGerms.isAbelianScheme_powObj c.A c.ab 3)
      (AbelianSchemeGerms.isAbelianScheme_powObj B hZ.1 3)
  let z : SiegPre (8 * h) M (zetaAway M) t :=
    { A := GlobalTheory.ZarhinFam.Zob c.A B
      ab := hab
      P := GlobalTheory.ZarhinFam.zP c.A B c.isLB hZ.2.1.isLB d mu
      isLB := GlobalTheory.ZarhinFam.zarhinBundle_isLineBundle c.A B c.isLB hZ.2.1.isLB d mu
      rig₁ := r1
      rig₂ := r2
      symm := sy
      lev := GlobalTheory.ZarhinFam.levZ c.lev (GlobalTheory.ZarhinFam.incZ c.A B) (GlobalTheory.ZarhinFam.actZ c.A B d la mu) (GlobalTheory.ZarhinFam.oMat d) κ
      lev_add := la1
      lev_tors := la2
      geom := GlobalTheory.T.zarhinTrick_level_symplectic_geometricPoints h M d S t c B Q la mu hZ h1 hM hodd hd hcop hdu hk κ hκ }
  obtain ⟨i1, i2, i3, i4, i5⟩ := GlobalTheory.T.zarhinProduct_relation_algebraic_clauses h M d S t c B Q la mu hZ h1 hM hodd hd hcop hdu hk κ hκ
  refine ⟨z, GlobalTheory.ZarhinFam.actZ c.A B d la mu, GlobalTheory.T.zarhinBundle_principal h M d S t c B Q la mu hZ h1 hM hodd hd hcop hdu hk,
    GlobalTheory.T.zarhinOrder_isRingAction_on_product h M d S t c B Q la mu hZ h1 hM hodd hd hcop hdu hk, GlobalTheory.T.zarhinOrderAction_rosati_adjoint h M d S t c B Q la mu hZ h1 hM hodd hd hcop hdu hk,
    GlobalTheory.ZarhinFam.incZ c.A B, GlobalTheory.ZarhinFam.prZ c.A B, i1, i2, i3, i4,
    GlobalTheory.T.zarhin_bundle_isomorphism h M d S t c B Q la mu hZ h1 hM hodd hd hcop hdu hk, i5, fun a => rfl⟩

end GlobalTheory.ZarhinFam
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.adjointActions_order_finite_unramified_scheme : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A : Over S) [GrpObj A] [IsCommMonObj A] (Q : LB (A ⊗ A).left), IsAbelianScheme A → Q.IsLB → (∃ t : (Q.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (Q.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso Q (Q.pull (lift (snd A A) (fst A A)).left) → Out.RelAmple A (Q.pull (lift (𝟙 A) (𝟙 A)).left) → ∀ (O : Type) [Ring O] (bar : O → O) (r : ℕ) (e : Fin r → O) (W : Matrix (Fin r) (Fin r) ℤ) (d : ℕ), (∀ a b, bar (a + b) = bar a + bar b) → Submodule.span ℤ (Set.range e) = ⊤ → ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → 0 < d → ∑ i, ∑ j, W i j • (e j * bar (e i)) = (d : O) → ∃ R : ActRep A Q bar, IsFinite R.π ∧ FormallyUnramified R.π := by
  first | (exact @GlobalTheory.EndLoc.actRep_finite_unramified) | (exact GlobalTheory.EndLoc.actRep_finite_unramified) | (intros; apply GlobalTheory.EndLoc.actRep_finite_unramified  <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

theorem _root_.GlobalTheory.T.harrisTaylor_exists_squareZero_lift_of_filtration : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), N.Coprime p → ∀ (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → ∀ (hsq : RingHom.ker π ^ 2 = 0) (tR : R →+* C) (t : Sp C ⟶ Sp R) (t₀ : Sp C₀ ⟶ Sp R), t = spMap tR → t₀ = spMap π ≫ t → ∀ (o₀ : GlobalTheory.UPel.HT.Obj b N t₀) (E : Submodule C (Crys (divided₂ hsq) (spMap π) o₀.A)), (∃ M : Submodule C (Crys (divided₂ hsq) (spMap π) o₀.A), IsCompl E M) → (∀ y : HdR o₀.A, y ∈ Fil o₀.A ↔ ∃ e ∈ E, (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ hsq) rfl o₀.A).Corr e y) → (∀ (c : D.O), ∀ e ∈ E, (haveI := o₀.act.hom (c); push (divided₂ hsq) (spMap π) (o₀.act.act (c)) (e)) ∈ E) → (∀ Φ : Crys (divided₂ hsq) (spMap π) o₀.A →ₗ[C] Crys (divided₂ hsq) (spMap π) o₀.A →ₗ[C] C, GlobalTheory.AbDual.IsCorrForm (divided₂ hsq) (spMap π) o₀.A o₀.A o₀.P Φ → ∀ x ∈ E, ∀ y ∈ E, Φ x y = 0) → (∀ e : Crys (divided₂ hsq) (spMap π) o₀.A, (haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O D.ω); push (divided₂ hsq) (spMap π) (o₀.act.act (algebraMap (𝓞 D.F) D.O D.ω)) (e)) - tR b.ρ • e ∈ E → ∃ w : Fin D.a → Crys (divided₂ hsq) (spMap π) o₀.A, (∀ i (c : 𝓞 D.F), (haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O c); push (divided₂ hsq) (spMap π) (o₀.act.act (algebraMap (𝓞 D.F) D.O c)) (w i)) - tR (b.t i c) • w i ∈ E) ∧ e - ∑ i, w i ∈ E) → ∃ (o : GlobalTheory.UPel.HT.Obj b N t) (m : GlobalTheory.UPel.HT.ObjMap o₀ o (spMap π)), liftFil (divided₂ hsq) m.cart = E := by
  first | (exact @GlobalTheory.UPel.HT.exists_sqZero_lift_of_fil) | (exact GlobalTheory.UPel.HT.exists_sqZero_lift_of_fil) | (intros; apply GlobalTheory.UPel.HT.exists_sqZero_lift_of_fil <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.Gen

theorem _root_.GlobalTheory.T.exists_open_closed_immersion_genModel_to_fibre : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (R' : Type) [CommRing R'] [Algebra ℚ R'] (φ : R →+* R') (gb : GBase D.toG R'), gb.ρ = φ b.ρ → (∀ i, gb.t i = φ.comp (b.t i)) → ∀ (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (M : Model b N) (X : GenModel gb N), ∃ j : X.X ⟶ pullback M.s (spMap φ), IsOpenImmersion j ∧ IsClosedImmersion j ∧ j ≫ pullback.snd _ _ = X.s ∧ IsGPull X.univ M.univ (j ≫ pullback.fst _ _) := by
  first | (exact @GlobalTheory.UPel.HT.GenCmp.genModel_eq_genericFibre) | (exact GlobalTheory.UPel.HT.GenCmp.genModel_eq_genericFibre) | (intros; apply GlobalTheory.UPel.HT.GenCmp.genModel_eq_genericFibre  <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_smooth_model_near_closedFibre_embedding : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (M : Modif R) (G' : Over M.S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ E : Emb M.π G', ∃ (N : Near M.π G') (fU : N.U.left ⟶ PSpace R E.N) (l : pullback N.U.hom M.π ⟶ E.H.toScheme), l ≫ E.H.ι = N.u ∧ l ≫ E.f = pullback.fst _ _ ≫ fU := by
  first | exact @GlobalTheory.Mum.exists_near | exact GlobalTheory.Mum.exists_near | (intros; apply GlobalTheory.Mum.exists_near <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

theorem GlobalTheory.UPel.HT.ES.finite_dvrPartners_snd : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharZero R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → (p : R) ∈ IsLocalRing.maximalIdeal R → ∀ (r : ℤ) (w : Ideal (𝓞 D.F)) (j c : ℕ), w.IsMaximal → uIdeal D r ≤ w → j ≤ D.n → (∃ e : ℕ, c = p ^ e ∧ (0 < j → 0 < e)) → D.m = 1 → ∀ M : Model b N, ∀ (Y₀ : Scheme.{0}) (s₀ t₀ : Y₀ ⟶ M.X) (gs gt : Y₀ ⟶ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).toScheme) (o₀ o₀' : Obj b N (s₀ ≫ M.s)) (ms₀ : ObjMap o₀ M.univ s₀) (mt₀ : ObjMap o₀' M.univ t₀) (ψ₀ : o₀.A ⟶ o₀'.A), s₀ ≫ M.s = t₀ ≫ M.s → gs ≫ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι = s₀ → gt ≫ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι = t₀ → IsFinite gs → Etale gs → IsFinite gt → Etale gt → IsPIsog c o₀ o₀' ψ₀ → IsTj r w j o₀ o₀' ψ₀ → ∀ z : M.X, {u : M.X | ∃ (V K : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : Field K) (_ : Algebra V K) (_ : IsFractionRing V K) (y' z' : Sp V ⟶ M.X) (x : Sp K ⟶ Y₀), spMap (algebraMap V K) ≫ y' = x ≫ s₀ ∧ spMap (algebraMap V K) ≫ z' = x ≫ t₀ ∧ y' (IsLocalRing.closedPoint V) = u ∧ z' (IsLocalRing.closedPoint V) = z}.Finite := by
  intro p _ D R _ _ _ _ b N hN hNp hpR r w j c hw hu hj hc hm M Y₀ s₀ t₀ gs gt o₀ o₀' ms₀ mt₀ ψ₀ hst hgs hgt _ _ hgtf _ hψ _ z
  by_cases hz : z ∈ M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))
  · exact GlobalTheory.T.finite_dvr_limits_correspondence_finite_snd M.X Y₀ (Sp R) M.s _ s₀ t₀ gt (GlobalTheory.ZM.isSeparated_of_isQProjOver M.qproj) inferInstance hst hgt
      hgtf z hz
  · exact (GlobalTheory.T.finite_pIsogenySources_at_charP_point p D R b N hN hNp hpR c hm M z).subset
      (GlobalTheory.T.exists_pIsogeny_at_closedPoint_of_dvr_limit p D R b N hN hNp hpR c M Y₀ s₀ t₀ o₀ o₀' ms₀ mt₀ ψ₀ hst hψ z hz)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

theorem _root_.GlobalTheory.T.harrisTaylor_typeTj_correspondence_target_finite_etale : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → IsUnit ((p : ℕ) : R) → ∀ (r : ℤ) (w : Ideal (𝓞 D.F)) (j c : ℕ), w.IsMaximal → uIdeal D r ≤ w → j ≤ D.n → (∃ e : ℕ, c = p ^ e ∧ (0 < j → 0 < e)) → D.m = 1 → ∀ (M : Model b N) (Y : Scheme.{0}) (s t : Y ⟶ M.X), s ≫ M.s = t ≫ M.s → ∀ (o o' : Obj b N (s ≫ M.s)) (ms : ObjMap o M.univ s) (mt : ObjMap o' M.univ t) (ψ : o.A ⟶ o'.A), IsPIsog c o o' ψ → IsTj r w j o o' ψ → IsFinite s → Etale s → (∀ (S : Scheme.{0}) (x : S ⟶ M.X) (o₁ o₁' : Obj b N (x ≫ M.s)) (m : ObjMap o₁ M.univ x) (ψ₁ : o₁.A ⟶ o₁'.A), IsPIsog c o₁ o₁' ψ₁ → IsTj r w j o₁ o₁' ψ₁ → ∃! y : S ⟶ Y, y ≫ s = x ∧ ∃ (m₀ : ObjMap o₁ o y) (m₁ : ObjMap o₁' o' y), m₀.φ ≫ ψ.left = ψ₁.left ≫ m₁.φ) → IsFinite t ∧ Etale t := by
  first | exact @GlobalTheory.UPel.HT.ESDual.finite_etale_target | exact GlobalTheory.UPel.HT.ESDual.finite_etale_target | exact @GlobalTheory.UPel.HT.ESDual.square_comp' | exact GlobalTheory.UPel.HT.ESDual.square_comp' | exact @GlobalTheory.UPel.HT.ESDual.square_comp | exact GlobalTheory.UPel.HT.ESDual.square_comp
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.theta_map_pull_O1_power_hodge : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (o : Type) [CommRing o] (m n : ℕ) (f : Xo.XF c ⟶ PSpace o n), Odd m → 3 ≤ m → IsUnit (m : o) → n + 1 = m ^ (4 * (Module.finrank ℚ E / 2 * (Dw.p + Dw.q))) → ThMap Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig m (pullback.fst _ _ : Xo.XF c ⟶ Xo.X) f → ∀ (Y : Model Xo c (RingHom.id c.F)) (g : Y.X ⟶ PSpace o n), Y.j ≫ g = f → ∀ (Ω : Type) [Field Ω] [Algebra c.F Ω] (M : RatModel c.F Ω) (io : M.Z ⟶ Y.X), IsOpenImmersion io → io ≫ Y.s = M.s → LBIso ((lbPow ((ProjSpace.O1 o n).pull g) (8 * (n + 1).factorial)).pull io) ((lbPow (GlobalTheory.SiegelTor.hodge Y.t.G (Module.finrank ℚ E / 2 * (Dw.p + Dw.q))) (4 * (n + 1).factorial * (n + 1).factorial)).pull io) := by
  first | exact @GlobalTheory.UMin.KeyOne.lbIso_pull_O1_hodge | exact GlobalTheory.UMin.KeyOne.lbIso_pull_O1_hodge | (intros; apply GlobalTheory.UMin.KeyOne.lbIso_pull_O1_hodge <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp GlobalTheory.HSNef

namespace GlobalTheory.HSNef

theorem ampleHS_of_principalisation : GlobalTheory.Published.Principalisation → AmpleHS := by
  intro hPr k _ X _ p D hX P a hA hS ha
  have hC := GlobalTheory.MixHt.arCalc_of_principalisation hPr
  obtain ⟨e, x, hx⟩ := GlobalTheory.T.exists_basepointFreeSectionTuple_ample_arith k X p D hX P hA
  obtain ⟨B, hB0, hB⟩ := GlobalTheory.T.exists_fubiniStudyWeights_bounded_difference k X p D hX P e x hx
  have hG := GlobalTheory.T.isGoodSectionGroupFamily_ampleMultiples hC k X p D hX P hA
  obtain ⟨t₀, ht₀⟩ := GlobalTheory.T.arithHilbertSamuel_smallSections_change_of_metric hPr k X p D hX P a hS ha hG
  obtain ⟨C, hCb⟩ := GlobalTheory.T.selfIntersection_canonicalWeights_tendsto_zero hC k X p D hX P hA e x hx
  refine ⟨max (t₀ + B) 1, fun t ht => ?_⟩
  have ht1 : t₀ + B ≤ t := le_trans (le_max_left _ _) ht
  have ht2 : 0 < t := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) ht)
  have hball : ∀ (u : SmFn p) (m : ℕ) (R : ℝ), ballIn (upperParabolic P u) (P.H m 1) m 1 R = (upperParabolic P u).Bl m 1 R :=
    fun _ _ _ => rfl
  have hball' : ∀ (m : ℕ) (R : ℝ), ballIn P (P.H m 1) m 1 R = P.Bl m 1 R := fun _ _ => rfl
  have hF : (0 : ℝ) < D.factorial := by exact_mod_cast Nat.factorial_pos D
  have hF1 : (0 : ℝ) < (D + 1).factorial := by exact_mod_cast Nat.factorial_pos _
  have he : (0 : ℝ) < e := by exact_mod_cast hx.pos
  have hLg : 0 ≤ Real.log ((D : ℝ) + 1) := Real.log_nonneg (by linarith [(Nat.cast_nonneg D : (0 : ℝ) ≤ D)])
  set g := gdeg P.L D with hg
  have hc : (a + ((D : ℝ) + 1) * t * g) / ((D + 1).factorial : ℝ) = g / D.factorial * t + a / (D + 1).factorial := by
    rw [Nat.factorial_succ]; push_cast; field_simp; ring
  have key : ∀ n : ℕ, 1 ≤ n → ∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop,
      |P.lc m 1 (Real.exp (t * m)) / (m : ℝ) ^ (D + 1) - (g / D.factorial * t + a / (D + 1).factorial)|
        ≤ |g| / D.factorial * (Real.log ((D : ℝ) + 1) / (2 * n) / e) + |C| / n / (D + 1).factorial + 2 * ε := by
    intro n hn ε hε
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    obtain ⟨u, hu, huB⟩ := hB n hn
    have hsemi := GlobalTheory.T.fubiniStudyWeightIncrement_semiPositive_curvature k X p D hX P e x hx n u hn hu
    obtain ⟨h, hh⟩ := (hC.arExists k X p D hX).1 (up P.L u)
    have hsi : (up P.L u).IsSelfInter (h (genericPoint X)) := ⟨h, hh, rfl⟩
    have han := hCb n u _ hn hu hsi
    have hdiff := ht₀ u B _ hB0 huB hsemi hsi t ht1
    obtain ⟨hnu1, hnu2, hgu, -, -⟩ := GlobalTheory.T.norm_basepointFree_sections_le_one_fubiniStudy k X p D hX P e x hx n u hn hu
    have hκ1 : Real.exp (-(Real.log ((D : ℝ) + 1) / (2 * n))) ≤ 1 :=
      Real.exp_le_one_iff.2 (neg_nonpos.2 (div_nonneg hLg (by positivity)))
    have hcnt := GlobalTheory.T.sectionCount_growth_metric_near_generatorMax hC k X p D hX (upperParabolic P u) hA e x hgu _ t (Real.exp_pos _) hκ1 ht2 hnu1 hnu2 ε hε
    rw [show (upperParabolic P u).L = up P.L u from rfl, GlobalTheory.T.hermLineBundleGeometricDegree_raiseWeight hC k X p D hX P.L u, Real.log_exp, ← hg] at hcnt
    simp only [hball, hball'] at hdiff
    have hd := hdiff.eventually (Metric.ball_mem_nhds _ hε)
    set an := h (genericPoint X)
    set T := Real.log ((D : ℝ) + 1) / (2 * n) / e with hT
    have hT0 : 0 ≤ T := by positivity
    have hup : g / D.factorial * (t - -(Real.log ((D : ℝ) + 1) / (2 * n)) / e) ≤ g / D.factorial * t + |g| / D.factorial * T := by
      rw [show t - -(Real.log ((D : ℝ) + 1) / (2 * n)) / e = t + T by rw [hT]; ring, mul_add]
      gcongr
      exact le_abs_self g
    have han1 : an / (D + 1).factorial ≤ |C| / n / (D + 1).factorial :=
      div_le_div_of_nonneg_right ((le_abs_self an).trans (han.trans (div_le_div_of_nonneg_right (le_abs_self C) hn0.le))) hF1.le
    have hgT : 0 ≤ |g| / D.factorial * T := by positivity
    have han2 : -(an / (D + 1).factorial) ≤ |C| / n / (D + 1).factorial := by
      rw [← neg_div]; exact div_le_div_of_nonneg_right ((neg_le_abs an).trans (han.trans (div_le_div_of_nonneg_right (le_abs_self C) hn0.le))) hF1.le
    filter_upwards [hd, hcnt] with m hm1 hm2
    rw [Real.dist_eq, abs_sub_lt_iff] at hm1
    have hsplit : P.lc m 1 (Real.exp (t * m)) / (m : ℝ) ^ (D + 1) =
        (upperParabolic P u).lc m 1 (Real.exp (t * m)) / (m : ℝ) ^ (D + 1) -
          (Real.log ((upperParabolic P u).Bl m 1 (Real.exp (t * m))).ncard - Real.log (P.Bl m 1 (Real.exp (t * m))).ncard) /
            (m : ℝ) ^ (D + 1) := by
      simp only [Pair.lc]; ring
    have hq : (an - a) / ((D + 1).factorial : ℝ) = an / (D + 1).factorial - a / (D + 1).factorial := sub_div _ _ _
    rw [hsplit, abs_le]
    constructor <;> linarith [hm2.1, hm2.2]
  rw [hc]
  refine Metric.tendsto_nhds.2 fun δ hδ => ?_
  set K := |g| / D.factorial * (Real.log ((D : ℝ) + 1) / 2 / e) + |C| / (D + 1).factorial with hK
  have hK0 : 0 ≤ K := by positivity
  obtain ⟨n, hn⟩ := exists_nat_gt (2 * K / δ)
  have hn1 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hKn : |g| / D.factorial * (Real.log ((D : ℝ) + 1) / (2 * ((n + 1 : ℕ) : ℝ)) / e) +
      |C| / ((n + 1 : ℕ) : ℝ) / (D + 1).factorial = K / ((n + 1 : ℕ) : ℝ) := by
    rw [hK]; field_simp
  have hKlt : K / ((n + 1 : ℕ) : ℝ) < δ / 2 := by
    have h1 : 2 * K / δ < ((n + 1 : ℕ) : ℝ) := hn.trans (by exact_mod_cast Nat.lt_succ_self n)
    rw [div_lt_iff₀ hδ] at h1
    rw [div_lt_iff₀ hn1]
    linarith
  filter_upwards [key (n + 1) (Nat.le_add_left 1 n) (δ / 8) (by positivity)] with m hm
  rw [hKn] at hm
  rw [Real.dist_eq]
  linarith

end GlobalTheory.HSNef
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep GlobalTheory.FieldPair

theorem _root_.GlobalTheory.T.exists_global_section_angehrnSiu_inductive_step : GlobalTheory.Published.Principalisation → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ),
  IsProjOver p → topologicalKrullDim X = n → letI := algebraΓOfHom p;
  ∀ (Δ : X → ℚ) (m : ℕ) (G A : CartierDiv X) (D : X → ℚ) (P : Finset X) (z : X) (k : ℕ) (h : ℚ),
  IsEffQDiv Δ → (∀ y, KltAt p n Δ y) → 0 < m → IsLogCanonicalMultiple p n Δ m G → IsAmpleLB (toLB A) → IsQCart D →
  (∀ x ∈ P, IsClosed ({x} : Set X) ∧ z ⤳ x) → 1 ≤ k → topologicalKrullDim (closure ({z} : Set X)) = k →
  (z = genericPoint X ∨ IsNkltCentre p n (Δ + D) z) → 0 < h →
  (P.card : ℚ) * (k : ℚ) ^ k < h ^ k * (interNumRed ℂ (Closeds.closure ({z} : Set X)) fun _ : Fin k => toLB A : ℤ) →
  ∀ l₀ : ℕ, ∃ l : ℕ, l₀ ≤ l ∧ h < l ∧ ∃ f₀ ∈ (l • A).sections, (l • A).GeneratesAt z f₀ ∧
    ∃ δ₀ : ℚ, 0 < δ₀ ∧ δ₀ ≤ 1 ∧ ∀ u ∈ (l • A).sections, (l • A).VanishesAt z u →
      ∀ g : X.functionFieldˣ, (g : X.functionField) = f₀ + u → ∀ δ : ℚ, 0 ≤ δ → δ ≤ δ₀ → ∀ x ∈ P,
        ¬ KltAt p n (Δ + (1 - δ) • D + (h / l) • qWeil (CartierDiv.principal g + l • A) 1) x := by
  first | exact @GlobalTheory.PairStep.exists_global_step | exact GlobalTheory.PairStep.exists_global_step | (intros; apply GlobalTheory.PairStep.exists_global_step <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.KeyZh

theorem lft_of_arithBase : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ZH.ArithBase o Ω] (M : ZH.RatModel o Ω), LocallyOfFiniteType (M.s ≫ spMap (algebraMap ℤ o)) := by
  intro o Ω _ _ _ _ M
  have := M.lft
  have hft : Algebra.FiniteType ℤ o := (inferInstance : ZH.ArithBase o Ω).ft
  have : LocallyOfFiniteType (spMap (algebraMap ℤ o)) := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.2 hft
  infer_instance

theorem charZero_of_arithBase : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ZH.ArithBase o Ω] (M : ZH.RatModel o Ω), CharZero Γ(M.Z, ⊤) := by
  intro o Ω _ _ _ _ M
  have hne : ((⊤ : M.Z.Opens) : Set M.Z).Nonempty := ⟨genericPoint M.Z, trivial⟩
  have := (inferInstance : ZH.ArithBase o Ω).char
  exact (M.res ⊤ hne).charZero

theorem unifAlong_of_zhOut : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ZH.ArithBase o Ω] (S : ZH.ThetaSys o Ω) (ρ : S.Real) (M : ZH.RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (Zh : ZH.ZHOut ρ M U₀ EE), UnifAlong Zh.G Zh.L.L := by
  intro o Ω _ _ _ _ S ρ M U₀ EE Zh V _ _ _ _ hc _ ξ hne _
  obtain ⟨D, A, U, hU, -⟩ := Zh.unif V inferInstance inferInstance hc ξ hne
  exact ⟨D, A, U, hU⟩

theorem key_zh : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ZH.ArithBase o Ω] (S : ZH.ThetaSys o Ω) (ρ : S.Real) (M : ZH.RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (Zh : ZH.ZHOut ρ M U₀ EE), 1 ≤ S.g → S.Over₀ M U₀ → IsOpen (abLocus Zh.G) → ∀ (δ : LB M.Z) (t : S.Gam → δ.Sec), δ.IsLB → (⨆ a, nonzeroLocus (t a)) = ⊤ → ZM.SecCoord δ t M.pt S.th → LBIso (lbPow δ 8) (lbPow (GlobalTheory.SiegelTor.hodge Zh.G S.g) 4) := by
  intro o Ω _ _ _ _ S ρ M U₀ EE Zh hg hO hab δ t hδ hcov hsc
  obtain ⟨σ, hσ⟩ := GlobalTheory.T.exists_glued_thetaSection_nonzero_every_fibre o Ω S ρ M U₀ EE Zh hO δ t hδ hcov hsc
    (fun a z hz => GlobalTheory.T.coordinate_divides_on_nonzeroLocus_section o Ω M δ t S.th hδ hsc a z hz)
  exact GlobalTheory.T.keyFormula_evenDegeneration_global M.Z (M.s ≫ spMap (algebraMap ℤ o)) Zh.G S.g Zh.L δ σ hg inferInstance hO.normal
    (lft_of_arithBase o Ω M) (charZero_of_arithBase o Ω M) Zh.semi Zh.dim (GlobalTheory.T.semiAbelianExtension_abelianLocus_nonempty o Ω S ρ M U₀ EE Zh hO) hab
    Zh.sym hδ Zh.pol (unifAlong_of_zhOut o Ω S ρ M U₀ EE Zh) hσ

end GlobalTheory.KeyZh
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.hasSemiAbelianUniformisation_of_finiteExt : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)), HasFin D → Has D := by
  first | exact @GlobalTheory.Mum.has_of_hasFin | exact GlobalTheory.Mum.has_of_hasFin | (intros; apply GlobalTheory.Mum.has_of_hasFin <;> assumption)
end
