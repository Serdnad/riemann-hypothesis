module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle011
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsLatFamilyCongr
public import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.FarguesHodgeTate
public import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.Bundle001
public import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.ZarhinStatement
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle001
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle072
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle055
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HopfOrderLatticeBase
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle043
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.MemFirstLatticeIff
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle064
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ValMulLeOfCyclicKer
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle277
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle148
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle252
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle142
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle130
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle013
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsThetaSectionsBounded
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CInfGood
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle015
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle002
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CuspVolumeLimit
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle032
public import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.ConclusionOfSmooth
public import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.NotSubsetOfDenseCompl
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Development.AbelianVarietyTheory.Definitions.Divisors.SecondCountableTopologyOfIsProjOver
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.FinConstFor
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle280
public import Development.AutomorphicSpectrum.PublishedTheorems.PublishedGlobalResults.PrincipalizationOfPrincipalisation
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.QuasiAffine
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.StepOrderRes
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle002
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp MeasureTheory

attribute [-instance] GlobalTheory.CompHt.fintypePsi in
theorem _root_.GlobalTheory.T.cusp_volume_limit : GlobalTheory.CompanionTheory.Ar.Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (F : UnivFam E (CMType H) Dc.j Dc.j' Dc.n g Λ) (V : Set (Fin Dc.n → ℂ)) (z : (Fin Dc.n → ℂ) → (Sp ℂ ⟶ Or.𝔐.X)) (gm : (Fin Dc.n → ℂ) → (Σ k, J k) → ℂ), IsOpen V → V ⊆ ballDom F.q → DifferentiableOn ℂ gm V → (∀ t ∈ V, CoordsAt Or.𝔐.ξ Dc.y (z t) (gm t) ∧ Or.𝔐.Interior (z t) ∧ Or.𝔐.LabVal (z t) Or.sm F.σ) → (∀ t₀ ∈ V, ∀ (m : ℕ) (s : Fin m → Or.𝔐.Li), (∀ a, ∃ v, Or.𝔐.M.ValAt (z t₀) (s a) v) → ∃ x : Fin m → (Fin Dc.n → ℂ) → Fin g → ℂ, (∀ a, AnalyticAt ℂ (x a) t₀) ∧ ∀ᶠ t in 𝓝 t₀, ∃ v : Fin m → (epsAt (z t) ⟶ Or.𝔐.t.G), (∀ a, Or.𝔐.M.ValAt (z t) (s a) (v a)) ∧ FibreLatVec Or.𝔐.t (z t) (F.R t) (fun a => x a t) v) → ∀ t ∈ V, ∃ G : (Fin Dc.n → ℂ) → ℂ, AnalyticAt ℂ G t ∧ ∀ᶠ t' in 𝓝 t, phMu Hd (gm t') = ballPot F.q t' / 2 + (G t').re := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.phMu_eq_ballPot_half | exact GlobalTheory.CompanionTheory.Ar.Cusp.phMu_eq_ballPot_half | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.phMu_eq_ballPot_half <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt

theorem af_le_stdLat {o C : Type} [CommRing o] [Field C] [Algebra o C] (RC : Subalgebra o C) {F : Type} [Zero F] [One F]
    [DecidableEq F] [Fintype F] (h01 : (0 : F) ≠ 1) {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData C F n Sg r s) (p : ℕ)
    (hM : D.M ≤ stdLat RC _) (χ : F → C) (h0 : χ 0 = 0) (h1 : χ 1 = 1) : D.af RC p χ ≤ stdLat RC _ := by
  intro l hl
  have hl1 : D.l1 RC p ≤ stdLat RC _ := by
    refine sup_le hM ?_
    rintro _ ⟨x, hx, rfl⟩
    intro a _
    have : x a ∈ RC := hx a (Set.mem_univ a)
    have h2 : (p : C) * x a ∈ RC := by
      have := RC.mul_mem (natCast_mem RC p) this
      simpa using this
    simpa using h2
  have h3 := hl1 hl
  intro k _
  have h4 : (linMap n χ l) (Pi.single k 1) ∈ RC := h3 _ (Set.mem_univ _)
  have h5 : (linMap n χ l) (Pi.single k 1) = l k := by
    simp only [linMap, Fintype.linearCombination_apply, LinearMap.coe_mk]
    rw [Finset.sum_apply, Finset.sum_eq_single k]
    · simp [h1]
    · intro j _ hj
      simp [Pi.single_eq_of_ne hj, h0]
    · simp
  rw [h5] at h4
  exact h4


theorem testFacts (hF : GlobalTheory.CompanionTheory.Ar.HT.FarguesHodgeTate) (hQ : GlobalTheory.CompanionTheory.Ar.GR.QuotientByFiniteFlatStatement) (hZ : GlobalTheory.CompanionTheory.Ar.GR.ZarhinStatement) (hH : GlobalTheory.CompanionTheory.Ar.GR.HodgeTateDatumStatement) (hOC : GlobalTheory.CompanionTheory.Ar.GR.OrdinaryCurveStatement) : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), _root_.ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → HT.HTFree 𝔐 p → p ≠ 2 → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (b : ∀ t, Fin (labelRk D t) → 𝔐.Li), (∀ t, LinearIndependent Ω (b t) ∧ Submodule.span Ω (Set.range (b t)) = 𝔐.Vgen t) → ∀ φ : Equiv.Perm (CMType H ⊕ CMType H), IsFrobLabels c p φ → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ (t₀ : CMType H ⊕ CMType H) (Sg : Type) [Fintype Sg] (e : Sg → CMType H ⊕ CMType H) (φ' : Equiv.Perm Sg) (F : Type) [Field F] [Fintype F] [CharP F p] (pq : (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}) →+* F) (sc : F →+ (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)})) (w : O) (σ : Sg → F →+* IsLocalRing.ResidueField O), IsOrbit O 𝔐 p φ t₀ e φ' pq w σ → IsSec pq sc → ∀ (G : GenTors 𝔐 p) (c' : ∀ k, J k), mseg y c' ≠ 0 → ∀ (P : ChartPack G O c') (i : ∀ τ, (Fin (labelRk D (e τ)) → Ω) →ₗ[Ω] (Fin (D.p + D.q) → Ω)), (∀ τ : Sg, SeqHyp (CR O y c') (algebraMap O Ω w) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (dotDual (CR O y c') (coordLat O y (𝔐.HT p (e τ).swap) (b (e τ).swap) c')) (i τ) (qMap P (b (e τ).swap)) ∧ ∀ σE : E →+* Ω, (∀ a : 𝓞 E, σE (a : E) = 𝔐.emb (e τ) a) → DualSeq P σE (𝔐.R p - 2) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (b (e τ)) (i τ)) → (chartD e b pq sc w P i).Base (CR O y c') p (algebraMap O Ω w) → ∀ (C : Type) [Field C] [Algebra O C] [Algebra Ω C] [IsScalarTower O Ω C] (RC : Subalgebra O C), IsTestPt p (CR O y c') RC → ∀ χ : Sg → F →*₀ C, (∀ τ a (o : O), IsLocalRing.residue O o = σ τ a → χ τ a - algebraMap O C o ∈ RC ∧ ∀ u ∈ RC, u * (χ τ a - algebraMap O C o) ≠ 1) →  ((chartD e b pq sc w P i).bc RC).Facts RC p (algebraMap O C w) (fun τ a => χ τ a) φ' := by
  intro E _ _ _ H D l Xo c O₀ _ β Y S Ω _ K _ _ J _ y 𝔐 d hAr hpq p _ hpS hfree hp2 hdisc b hb φ hφ A _ _ _ m _ hpm O _ _ _ _ _ _ _ t₀ Sg _ e φ' F _ _ _ pq sc w σ hOrb hSec G c' hc' P i hseq hBase C _ _ _ _ RC hT χ hχ
  classical
  obtain ⟨hAC, ⟨v, hv, hvp⟩, hcomp, hRC⟩ := id hT
  haveI := hAC
  haveI : CharZero Ω := (RingHom.charZero_iff 𝔐.cst.injective).1 inferInstance
  haveI : CharZero C := (RingHom.charZero_iff (algebraMap Ω C).injective).1 inferInstance
  haveI : Finite (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}) := Ideal.finiteQuotientOfFreeOfNeBot _ (by
    simp [Ideal.span_singleton_eq_bot, (Fact.out : p.Prime).ne_zero])
  letI : Fintype (TestPt.NAdd E (D.p + D.q) p) := Fintype.ofFinite _
  have hInt : v.Integers RC := ⟨Subtype.val_injective, fun x => (hv _).1 x.2, fun {x} h => ⟨⟨x, (hv _).2 h⟩, rfl⟩⟩
  have hw : algebraMap O C w = algebraMap Ω C (algebraMap O Ω w) := IsScalarTower.algebraMap_apply O Ω C w
  obtain ⟨hO1, -⟩ : (∃ u : O, IsUnit u ∧ w ^ (p - 1) = u * (p : O)) ∧ True := ⟨hOrb.2.2.2.2.2.2.1.2.1, trivial⟩
  have hp0 : (p : O) ≠ 0 := hOrb.2.2.2.2.2.2.1.1

  obtain ⟨u, hu, hup⟩ := hO1
  have hp1 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hpΩ : (p : Ω) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have hpC : (p : C) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have h01 : (0 : F) ≠ 1 := zero_ne_one
  have hcd : CharData (CR O y c') p (algebraMap O Ω w)
      (fun (_ : Sg) (a : F) => if a = 0 then (0 : Ω) else 1) := by
    refine ⟨hpΩ, Subalgebra.algebraMap_mem _ w, ?_, h01, fun τ => ⟨by simp, by simp, fun a => ?_⟩⟩
    · obtain ⟨u', hu'⟩ := hu.exists_left_inv
      refine ⟨algebraMap O Ω (u' * w ^ (p - 2)), Subalgebra.algebraMap_mem _ _, ?_⟩
      have e1 : w ^ (p - 1) = w ^ (p - 2) * w := by
        rw [← pow_succ]; congr 1; omega
      have e2 : (p : O) = u' * w ^ (p - 2) * w := by
        rw [_root_.mul_assoc, ← e1, hup, ← _root_.mul_assoc, hu', _root_.one_mul]
      have := congrArg (algebraMap O Ω) e2
      simpa [map_mul] using this
    · show (if a = 0 then (0 : Ω) else 1) ∈ CR O y c'
      by_cases ha : a = 0
      · simp only [ha, if_true]; exact zero_mem _
      · simp only [ha, if_false]; exact one_mem _
  have hBase' : ((chartD e b pq sc w P i).bc RC).Base RC p (algebraMap O C w) := by
    rw [hw]
    exact (GlobalTheory.T.lattice_base_change_larger_ring_holds (chartD e b pq sc w P i) (CR O y c') p (algebraMap O Ω w) _ hcd hBase C RC hRC).2
  have hw0 : algebraMap O C w ≠ 0 := by
    intro h0
    have e1 := congrArg (algebraMap O C) hup
    rw [map_pow, h0, zero_pow (by omega), map_mul, map_natCast] at e1
    exact mul_ne_zero (hu.map (algebraMap O C)).ne_zero hpC e1.symm
  obtain ⟨AA, AW, hAA, hAW, hM, hstab, hFS⟩ := GlobalTheory.T.arith_variety_prime_global_relay E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hAr hpq p hpS hfree hp2 hdisc b hb φ hφ A m hpm O t₀ Sg e φ' F pq sc w σ hOrb hSec G c' hc' P i hseq hBase C RC hT χ hχ
  obtain ⟨hAb, hTi⟩ := GlobalTheory.T.arith_variety_model_hodge_relay hH hOC E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hAr hpq p hpS hfree hp2 hdisc b hb φ hφ A m hpm O t₀ Sg e φ' F pq sc w σ hOrb hSec G c' hc' P i hseq hBase C RC hT χ hχ v hv hvp
  obtain ⟨σ', ee, hfund, hχσ, hσφ⟩ := GlobalTheory.T.arith_variety_prime_hodge_total E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hAr hpq p hpS hfree hp2 hdisc b hb φ hφ A m hpm O t₀ Sg e φ' F pq sc w σ hOrb hSec G c' hc' P i hseq hBase C RC hT χ hχ
  have hptors : ∀ x : TestPt.NAdd E (D.p + D.q) p, p • x = 0 := by
    intro x
    ext k
    have : ((p : ℕ) : 𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk (Ideal.span {(p : 𝓞 E)})), Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_span_singleton_self _
    simp [nsmul_eq_mul, this]
  have hsec : ∀ x : Fin (D.p + D.q) → F, TestPt.fromNAdd pq (TestPt.toNAdd sc x) = x := by
    intro x
    ext k
    exact hSec.1 (x k)
  have hFlag : GlobalTheory.CompanionTheory.Ar.GR.FlagConcl v p AW.carrier (Pi.basisFun F (Fin (D.p + D.q))) σ' := by
    have h1 := GlobalTheory.T.abelian_factor_tight_field_action (GlobalTheory.T.quotient_zarhin_hodge_tate_subquotient hQ hZ hH) p C v RC hInt hvp hcomp (TestPt.NAdd E (D.p + D.q) p) AA hptors
      (by rw [hAA]; exact hAb) (by rw [hAA]; exact hTi) F (Fin (D.p + D.q) → F) (TestPt.toNAdd sc) (TestPt.fromNAdd pq)
      hsec hstab (by rw [hAA]; rw [hAW] at hFS; exact hFS) (D.p + D.q) (Pi.basisFun F (Fin (D.p + D.q))) σ' hfund
    rw [hAW]
    rw [hAA] at h1
    exact h1
  have hTh := GlobalTheory.T.chartD_th_sqIdeal_mem_and_smul_mem_and_eig_mem_sqIdeal E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hAr hpq p hpS hfree hp2 hdisc b hb φ hφ A m hpm O t₀ Sg e φ' F pq sc w σ hOrb hSec G c' hc' P i hseq hBase C RC hT χ hχ σ' ee hχσ
  have hTh' : ∀ τ, (∀ g ∈ ReciprocityTheory.PGsh.Up.sqIdeal (ReciprocityTheory.PGsh.L2.augIdeal AW.carrier), (g, 0) ∈ ((chartD e b pq sc w P i).bc RC).Th τ) ∧ (∀ (a : F) g m, (g, m) ∈ ((chartD e b pq sc w P i).bc RC).Th τ → ((fun x => g (a • x)), (fun (τ : Sg) (a : F) => χ τ a) τ a • m) ∈ ((chartD e b pq sc w P i).bc RC).Th τ) ∧ ∀ g ∈ GlobalTheory.CompanionTheory.Ar.GR.eig AW.carrier (σ' ^ p ^ ee τ), (g, 0) ∈ ((chartD e b pq sc w P i).bc RC).Th τ → g ∈ ReciprocityTheory.PGsh.Up.sqIdeal (ReciprocityTheory.PGsh.L2.augIdeal AW.carrier) := by
    rw [hAW]
    exact hTh
  have hleaf := GlobalTheory.T.arith_variety_model_prime_total hZ hH E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hAr hpq p hpS hfree hp2 hdisc b hb φ hφ A m hpm O t₀ Sg e φ' F pq sc w σ hOrb hSec G c' hc' P i hseq hBase C RC hT χ hχ v hv hvp hAb
  have haf : ∀ τ, ((chartD e b pq sc w P i).bc RC).af RC p (fun a => χ τ a) ≤ stdLat RC _ := fun τ =>
    af_le_stdLat RC h01 _ p hBase'.M_le _ (map_zero (χ τ)) (map_one (χ τ))
  have hseq' : ∀ τ, ((chartD e b pq sc w P i).bc RC).imH RC p τ (fun a => χ τ a) = ((chartD e b pq sc w P i).bc RC).om τ ∧
      ((chartD e b pq sc w P i).bc RC).kerH RC p τ (fun a => χ τ a) = divLat (algebraMap O C w) (((chartD e b pq sc w P i).bc RC).lie τ) := by
    intro τ
    obtain ⟨hbb, h1, h2, h3, h4, h5, h6, h7⟩ := GlobalTheory.T.arith_variety_prime_hodge_estimate E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hAr hpq p hpS hfree hp2 hdisc b hb φ hφ A m hpm O t₀ Sg e φ' F pq sc w σ hOrb hSec G c' hc' P i hseq hBase C RC hT χ hχ τ
    obtain ⟨g1, g2⟩ := GlobalTheory.T.ordinary_curve_model_relay hF hQ hZ hH hOC E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hAr hpq p hpS hfree hp2 hdisc b hb φ hφ A m hpm O t₀ Sg e φ' F pq sc w σ hOrb hSec G c' hc' P i hseq hBase C RC hT χ hχ v hv hvp τ hbb h1 h2 h4 h7
    exact GlobalTheory.T.hodge_kernel_image_lattice RC p ((chartD e b pq sc w P i).bc RC) (algebraMap O C w) (fun (τ : Sg) (a : F) => χ τ a) τ hw0 (hleaf τ) (haf τ)
      _ hbb h1 h2 h3 h4 g1 g2 h5 h6
  exact ⟨hleaf, fun τ => (hseq' τ).1, fun τ => (hseq' τ).2,
    GlobalTheory.CompanionTheory.Ar.Num.PtDx.main RC v hv p hvp ((chartD e b pq sc w P i).bc RC) (algebraMap O C w) (fun (τ : Sg) (a : F) => χ τ a) φ' hBase' AW hM hFS σ' hfund hFlag ee hχσ hσφ hTh',
    GlobalTheory.CompanionTheory.Ar.Num.stepGraph_snd_eq_kk RC v hv p hvp ((chartD e b pq sc w P i).bc RC) (algebraMap O C w) (fun (τ : Sg) (a : F) => χ τ a) φ' hBase' AW hM hFS σ' hfund hFlag ee hχσ hσφ hTh',
    GlobalTheory.CompanionTheory.Ar.Num.PtInj.kernel_stepGraph RC v hv p hvp ((chartD e b pq sc w P i).bc RC) (algebraMap O C w) (fun (τ : Sg) (a : F) => χ τ a) φ' hBase' AW hM hFS σ' hfund hFlag ee hχσ hσφ hTh'⟩

end GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

theorem _root_.GlobalTheory.T.exists_theta_sections_bounded : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (D : PPData H L) (th : Out.H0 D.t.PP.L 1) (Φ : ℝ) (M : (L →+* ℂ) → ℝ) (m : ℕ), 1 ≤ m → D.HasTheta th Φ → D.SupLe th M → ∃ (L' : Type) (_ : Field L') (_ : NumberField L') (_ : Algebra L L') (D' : PPData H L') (_ : D.Ext D') (s : Fin (m ^ (2 * D.g)) → Out.H0 D'.t.PP.L (m ^ 2)), (∀ i, D'.SupLe (s i) fun σ' => M (σ'.comp (algebraMap L L'))) ∧ ∀ (σ' : L' →+* ℂ) (a : D'.Frame σ') (f : Fin (m ^ (2 * D.g)) → (Fin D'.g → ℂ) → ℂ), (∀ i, a.IsFn (s i) (f i)) → ∀ F, a.IsTheta (m ^ 2) F → ∃ c : Fin (m ^ (2 * D.g)) → ℂ, F = ∑ i, c i • f i := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.Basis.main | exact GlobalTheory.CompanionTheory.Ar.Sl.Basis.main | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.Basis.main <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

attribute [-instance] GlobalTheory.CompHt.fintypePsi in
theorem _root_.GlobalTheory.T.component_norm_constant_models : (Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c), CompLaws U h e → ∀ x : ℝ, (∀ σ, GoodEmb c σ → ∀ k (τ : E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = x) → ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (Fr : Small.GenFrame Or) (Z : Comp Xo c) (Rd : Reading Fr h Z), ∃ u : MRing RM.ι, Small.IsFormOff (mCoordIdeal RM.y) u ∧ ∀ (σ : c.F →+* ℂ), ∀ z ∈ mcPts (mCoordIdeal RM.y), (∀ t : c.F, Small.HasVal RM.y 0 (Or.𝔐.cst t) z (σ t)) → MvPolynomial.aeval z u ≠ 0 → ∃ k, Over (U (goodOf c σ)) (e Z) k ∧ ∃ y ∈ ((U (goodOf c σ)).X k).dom, ∀ (a : WZ E) (n' : Option (RootIx Dw) → ℤ), (∀ j, (n' j : ℝ) = RM.coef (towerWt Dw a) 0 j) → ∃ θ : ℂ, ‖θ‖ = (∏ r', (Or.sing r').h z ^ n' (some r')) * lieFacZ Dw x a * ((U (goodOf c σ)).X k).pnorm (laZ (U (goodOf c σ)) a k) (fun _ => 1) y ∧ ∀ f ∈ secZ Xo c a, (GoodEmb c σ → Small.HasVal RM.y (Top.combLine (RM.line 1) n').a (Fr.rd f * (∏ r', Or.e r' ^ (-n' (some r')))) z (θ * rdU (U (goodOf c σ)) f k y)) ∧ (¬ GoodEmb c σ → Small.HasVal RM.y (Top.combLine (RM.line 1) n').a (Fr.rd f * (∏ r', Or.e r' ^ (-n' (some r')))) z (θ * starRingEnd ℂ (rdU (U (goodOf c σ)) f k y)))) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.component_norm_constant_models | exact GlobalTheory.CompanionTheory.Relay.component_norm_constant_models | (intros; apply GlobalTheory.CompanionTheory.Relay.component_norm_constant_models <;> assumption)
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.ResK ReciprocityTheory.AnForm.R

namespace GlobalTheory.CompanionTheory.Hypotheses₂.ResKSide

theorem le_smoothLocus {X Y : Scheme.{0}} (f : X ⟶ Y) [LocallyOfFinitePresentation f] (U : X.Opens)
    [Smooth (U.ι ≫ f)] : U ≤ f.smoothLocus := by
  intro x hx
  have := (U.ι ≫ f).smoothLocus_eq_top.ge (Set.mem_univ (⟨x, hx⟩ : U))
  rw [← Scheme.Hom.preimage_smoothLocus_eq] at this
  exact this

theorem dense_preimage {X Y : Scheme.{0}} (f : X ⟶ Y) {U V : Y.Opens} [IsIso (f ∣_ V)]
    (hV : Dense ((f ⁻¹ᵁ V : X.Opens) : Set X)) (hU : Dense (U : Set Y)) :
    Dense ((f ⁻¹ᵁ U : X.Opens) : Set X) := by
  rw [dense_iff_inter_open]
  intro O hO hne
  obtain ⟨p, hpO, hpV⟩ := hV.inter_open_nonempty O hO hne
  let O' : Set (f ⁻¹ᵁ V) := (f ⁻¹ᵁ V).ι.base ⁻¹' O
  have hO' : IsOpen O' := hO.preimage (f ⁻¹ᵁ V).ι.base.hom.continuous
  have hopen : IsOpen (V.ι.base '' ((f ∣_ V).base '' O')) :=
    V.ι.isOpenEmbedding.isOpenMap _ ((f ∣_ V).isOpenEmbedding.isOpenMap _ hO')
  have hp' : (⟨p, hpV⟩ : f ⁻¹ᵁ V) ∈ O' := hpO
  obtain ⟨y, ⟨q, ⟨p', hp'O, rfl⟩, rfl⟩, hyU⟩ := hU.inter_open_nonempty _ hopen ⟨_, _, ⟨_, hp', rfl⟩, rfl⟩
  refine ⟨(f ⁻¹ᵁ V).ι p', hp'O, ?_⟩
  show f ((f ⁻¹ᵁ V).ι p') ∈ U
  rw [← Scheme.Hom.comp_apply, ← morphismRestrict_ι, Scheme.Hom.comp_apply]
  exact hyU

theorem relDim_preimage {X Y S : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ S) (U : Y.Opens) [IsIso (f ∣_ U)] {D : ℕ}
    (h : SmoothOfRelativeDimension D (U.ι ≫ g)) : SmoothOfRelativeDimension D ((f ⁻¹ᵁ U).ι ≫ f ≫ g) := by
  have : SmoothOfRelativeDimension (0 + D) ((f ∣_ U) ≫ U.ι ≫ g) := inferInstance
  rw [zero_add] at this
  rw [← morphismRestrict_ι_assoc]
  exact this

theorem relDim_of_dense {Y S : Scheme.{0}} (g : Y ⟶ S) [Smooth g] (W : Y.Opens) (hW : Dense (W : Set Y)) {D : ℕ}
    (h : SmoothOfRelativeDimension D (W.ι ≫ g)) : SmoothOfRelativeDimension D g := by
  choose n W' hW' hd using ReciprocityTheory.ChartRestriction.G.H1.exists_dim g
  have key : ∀ x, n x = D := by
    intro x
    obtain ⟨y, hyW', hyW⟩ := hW.inter_open_nonempty (W' x) (W' x).isOpen ⟨x, hW' x⟩
    have := hd x
    have e₁ : SmoothOfRelativeDimension (0 + n x) ((W' x ⊓ W).ι ≫ g) := by
      rw [← Scheme.homOfLE_ι _ (inf_le_left : W' x ⊓ W ≤ W' x), Category.assoc]; infer_instance
    have e₂ : SmoothOfRelativeDimension (0 + D) ((W' x ⊓ W).ι ≫ g) := by
      rw [← Scheme.homOfLE_ι _ (inf_le_right : W' x ⊓ W ≤ W), Category.assoc]; infer_instance
    simpa using ReciprocityTheory.ChartRestriction.G.H1.dim_unique _ e₁ e₂ ⟨y, hyW', hyW⟩
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension D) := HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension D) W'
    (top_le_iff.1 fun x _ => Opens.mem_iSup.2 ⟨x, hW' x⟩) fun x => ?_
  rw [← key x]; exact hd x

theorem isProper_of_isProjOver {K : Type} [Field K] {Y : Scheme.{0}} {h : Y ⟶ Sp K} (hp : IsProjOver h) :
    IsProper h := by
  obtain ⟨N, i, hi, rfl⟩ := hp
  have : IsProper (PSpace.str K N) := isProper_str K N
  infer_instance

end GlobalTheory.CompanionTheory.Hypotheses₂.ResKSide

namespace GlobalTheory.CompanionTheory.Hypotheses₂.ResKSide

theorem resK_of_resolution_principalisation (H₁ : ResolutionCharZero) (H₂ : PrincipalisationCharZero) :
    ResKStatement := by
  intro K _ _ M D X i U ⟨hi, hred, hdense, hU⟩
  have hproj : IsProjOver (i ≫ PSpace.str K M) := ⟨M, i, hi, rfl⟩
  have hP : IsProper (i ≫ PSpace.str K M) := isProper_of_isProjOver hproj
  obtain ⟨X₁, s, hs, hproj₁, hsm₁, hiso₁, hsnc₁⟩ := H₁.projective (i ≫ PSpace.str K M) hproj
  have : Smooth (U.ι ≫ i ≫ PSpace.str K M) := hU.smooth D _
  have hUs : U ≤ (i ≫ PSpace.str K M).smoothLocus := le_smoothLocus _ U
  have : IsIso (s ∣_ U) := isIso_morphismRestrict_of_le s hUs
  have hd₁ : Dense ((s ⁻¹ᵁ U : X₁.Opens) : Set X₁) := by
    refine dense_preimage s (V := (i ≫ PSpace.str K M).smoothLocus) ?_ hdense
    simpa using dense_compl_of_snc _ hsnc₁
  have hP₁ : IsProper (s ≫ i ≫ PSpace.str K M) := isProper_of_isProjOver hproj₁
  have hD₁ : SmoothOfRelativeDimension D (s ≫ i ≫ PSpace.str K M) :=
    relDim_of_dense _ _ hd₁ (relDim_preimage s _ U hU)
  let I : X₁.IdealSheafData := preRed s (U : Set X)ᶜ U.isOpen.isClosed_compl
  have hIs : (I.support : Set X₁) = s.base ⁻¹' (U : Set X)ᶜ := by
    simp [I, preRed]
  have : CompactSpace X₁ := by
    first
    | exact QuasiCompact.compactSpace_of_compactSpace (s ≫ i ≫ PSpace.str K M)
    | exact (quasiCompact_over_affine_iff (s ≫ i ≫ PSpace.str K M)).mp inferInstance
  have : IsLocallyNoetherian X₁ := by
    first
    | exact LocallyOfFiniteType.isLocallyNoetherian (s ≫ i ≫ PSpace.str K M)
    | infer_instance
  have : IsNoetherian X₁ := by first | infer_instance | exact ⟨⟩
  have : NoetherianSpace X₁ := inferInstance
  have hI : ∀ C ∈ irreducibleComponents X₁, ¬ C ⊆ (I.support : Set X₁) := by
    refine SncBlowup.not_subset_of_dense_compl ?_
    rw [hIs]; simpa using hd₁
  obtain ⟨X₂, t, E', hseq, hsm₂, hcart, hsnc₂, hiso₂⟩ :=
    H₂ K D X₁ (s ≫ i ≫ PSpace.str K M) hD₁ inferInstance inferInstance I ⊥ hI (fun x hx => hx.elim)
  have hsupp : ((I.comap t).support : Set X₂) = (t ≫ s).base ⁻¹' (U : Set X)ᶜ := by
    rw [Scheme.IdealSheafData.support_comap]
    simp [hIs] <;> rfl
  have hUc : I.support.compl = s ⁻¹ᵁ U := by
    ext x
    simp [hIs]
  rw [hUc] at hiso₂
  have hiso : IsIso ((t ≫ s) ∣_ U) := by rw [morphismRestrict_comp]; exact @IsIso.comp_isIso _ _ _ _ _ _ _ hiso₂ (isIso_morphismRestrict_of_le s hUs)
  have hT : IsClosed ((t ≫ s).base ⁻¹' (U : Set X)ᶜ) :=
    U.isOpen.isClosed_compl.preimage (t ≫ s).base.hom.continuous
  have hsncT : FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal ⟨_, hT⟩) := by
    have e : (I.comap t).support = ⟨_, hT⟩ := Closeds.ext hsupp
    rwa [e] at hsnc₂
  have hd₂ : Dense (((t ≫ s) ⁻¹ᵁ U : X₂.Opens) : Set X₂) := by
    exact Dense.mono (fun x hx => by simpa using hx) (dense_compl_of_snc _ hsncT)
  have hproj₂ : IsProjOver (t ≫ s ≫ i ≫ PSpace.str K M) :=
    (Resolution.IsBlowupSeq.of_smooth hseq.isSmoothBlowupSeq).isProjOver hproj₁
  have hP₂ := isProper_of_isProjOver hproj₂
  have : CompactSpace X₂ := by
    first
    | exact QuasiCompact.compactSpace_of_compactSpace (t ≫ s ≫ i ≫ PSpace.str K M)
    | exact (quasiCompact_over_affine_iff (t ≫ s ≫ i ≫ PSpace.str K M)).mp inferInstance
  have hsm : Smooth ((t ≫ s) ≫ i ≫ PSpace.str K M) := by simpa using hsm₂
  obtain ⟨hDim, hC⟩ := GlobalTheory.T.coords_statement K D X₂ ((t ≫ s) ≫ i ≫ PSpace.str K M) ((t ≫ s) ⁻¹ᵁ U) _ hT inferInstance hsm hd₂
    (relDim_preimage (t ≫ s) _ U hU) hsncT
  obtain ⟨r, j, hj, e⟩ := exists_closed_in_prod ((t ≫ s) ≫ i) (by simpa using hproj₂)
  exact ⟨r, X₂, j, t ≫ s, hj, e, hDim, hiso, hd₂, hC⟩

end GlobalTheory.CompanionTheory.Hypotheses₂.ResKSide
end
end

section

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem finConst_of_all_hosts : FinConst :=
  FinConstAll.finConst GlobalTheory.T.finite_constant_all_holds

end GlobalTheory.CompanionTheory.Ar.Flat
end
