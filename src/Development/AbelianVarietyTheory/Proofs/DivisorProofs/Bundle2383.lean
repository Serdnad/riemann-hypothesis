module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle011
public import Development.AbelianVarietyTheory.Definitions.CMLattices.Bundle001
public import Formalism.LocalToGlobal.Divisibility.NumbersLemmas
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle025
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2376
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle014
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComponentRanksDegreesAddWithMasses
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAuxiliaryHeckeCharacter
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle546
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle339
import Formalism.LocalToGlobal.UnitaryNorms.CharUniq
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2344
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2183
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2364
public import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.Bundle002
public import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.Bundle003
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.TwistedPlaceChoiceLiesOverPair
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1910
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle059
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.IsStrictDom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle002

@[expose] public section

section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR.Links ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop

theorem _root_.GlobalTheory.T.logPeriod_eq_kroneckerCharacter_logPeriod_of_host : ∀ (D : D7) (L : SizeData₂ D) (Q : Par D), Q.PinHost → ∀ (Del h0 : ℕ), ∃ (_ : NeZero Q.H.d) (χ : DirichletCharacter ℂ Q.H.d), GlobalTheory.IsKroneckerChar χ ∧ (GlobalTheory.CM.logOm D.host.E χ).re = (ofRecord D L Del h0).logOm ∧ (ofRecord D L Del h0).logOm = L.logOm ∧ GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField Q.H := by
  first | exact @GlobalTheory.CovTop.Period.period_eq_kronecker | exact GlobalTheory.CovTop.Period.period_eq_kronecker | (intros; apply GlobalTheory.CovTop.Period.period_eq_kronecker <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum

theorem _root_.GlobalTheory.T.component_ranks_degrees_add_with_masses : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (V : (c.F →+* ℂ) → HSp D) (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r) (G : WTZ D.host.E), Splits U G → Orthogonal U V dict G → Adds U V dict G := by
  first | exact @GlobalTheory.CompAdds.adds | exact GlobalTheory.CompAdds.adds | (intros; apply GlobalTheory.CompAdds.adds <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop NumberField IsDedekindDomain
open GlobalTheory.FunObj.SqNum (nuH halfRank IsTor)
open GlobalTheory.CMVal GlobalTheory.HeckeGal

noncomputable section

namespace GlobalTheory.ThmARatio

open GlobalTheory.ToricDenom GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols Formalism.L2.Host

theorem twisted_value {E : Type} [Field E] [NumberField E] [IsCMField E] {I : Type} [Fintype I] {φ : I → E →+* ℂ}
    (hφ : IsCMType φ) {s : ℕ} {κ : I → ℕ} {𝔣 : Ideal (OF E)} {Q : Finset (HeightOneSpectrum (𝓞 E))} {χ ξ : HChar E}
    {Λ : ℂ → ℂ} {m : ℕ} (hU : UnramFin E) (hs : 1 ≤ s) (hb : IsBaseCond 𝔣) (hQ : IsFinSetSplitPlacesCoprimeConductor 𝔣 (belowSet Q))
    (hχ : IsValChar φ s κ 𝔣 ∅ χ) (hm : m ≠ 0) (hord : ξ.OrderDvd m) (htr : TrivOnF ξ) (htame : ∀ v, ξ.TameAt v)
    (hram : ∀ v, ξ.UnrAt v ↔ v ∉ Q) (hΛ : IsHeckeL (χ * ξ) Λ) :
    ∃ (ψc : PicO (condQ 𝔣 (belowSet Q)) →* ℂˣ) (T : (PicO (condQ 𝔣 (belowSet Q)) →* ℂˣ) → ℂ),
      (∀ y, finPart ξ y = ψc (QuotientGroup.mk y)) ∧
      (∀ ψ, IsTwistedSum φ s κ (condQ 𝔣 (belowSet Q)) χ ψ (T ψ)) ∧ Λ s = T ψc := by
  classical
  have hloc (a b : HChar E) (v : HeightOneSpectrum (𝓞 E)) (x : (v.adicCompletion E)ˣ) :
      (a * b).loc v x = a.loc v x * b.loc v x := rfl
  have hp : ∀ x, ξ.1 x ^ m = 1 := fun x => by
    have := congrArg (fun c : HChar E => c.1 x) hord
    simpa using this
  have hχu : ∀ v ∈ belowSet Q, ∀ P, Over P v → χ.UnrAt P := fun v hv P hP => by
    have e := (hχ.2.2.2 v P hP).2 (Finset.notMem_empty v)
    rwa [expIn, multiplicity_eq_zero_of_not_dvd (hQ v hv).2, expAt_zero_iff] at e
  have hξu : ∀ v ∉ belowSet Q, ∀ P, Over P v → ξ.UnrAt P := fun v hv P hP =>
    (hram P).2 fun h => hv (Finset.mem_image.2 ⟨P, h, HeightOneSpectrum.ext hP⟩)
  have hv : IsValChar φ s κ 𝔣 (belowSet Q) (χ * ξ) := by
    refine ⟨hχ.1.mul (GlobalTheory.ToricDistribution.isUnitary_of_pow hm hp), hχ.2.1.mul htr, fun k => ?_,
      fun v P hP => ⟨fun hv => ?_, fun hv n => ?_⟩⟩
    · rw [HChar.inf_mul, GlobalTheory.ToricDistribution.inf_of_pow hm hp, mul_one]
      exact hχ.2.2.1 k
    · intro x hx hx1
      rw [hloc, hχu v hv P hP x hx, htame P x hx hx1, one_mul]
    · rw [← (hχ.2.2.2 v P hP).2 (Finset.notMem_empty v) n]
      refine forall_congr' fun x => forall_congr' fun hx => ?_
      rw [hloc, hξu v hv P hP x hx, mul_one]
  obtain ⟨P₀⟩ : Nonempty (HeightOneSpectrum (𝓞 E)) := by
    obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 E)
    exact ⟨⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField _)⟩⟩
  have hex : ∀ q : HeightOneSpectrum (OF E), ∃ P, q ∈ belowSet Q → P ∈ Q ∧ Over P q := fun q => by
    by_cases e : q ∈ belowSet Q
    · obtain ⟨P, hP, rfl⟩ := Finset.mem_image.1 e
      exact ⟨P, fun _ => ⟨hP, over_below P⟩⟩
    · exact ⟨P₀, fun h => absurd h e⟩
  choose Pq hPq using hex
  have t := GlobalTheory.ToricDistributionObj.toricSumFormula_holds E I φ hφ s κ 𝔣 (belowSet Q) (χ * ξ) Pq Λ hU hs hb hQ hv
    (fun q hq => (hPq q hq).2) hΛ
  rw [Finset.filter_false_of_mem, Finset.prod_empty, mul_one] at t
  swap
  · intro q hq h
    refine (hram (Pq q)).1 (fun x hx => ?_) (hPq q hq).1
    have := h x hx
    rwa [hloc, hχu q hq _ (hPq q hq).2 x hx, one_mul] at this
  have hker : princ ⊔ hatOUnits (condQ 𝔣 (belowSet Q)) ≤ (finPart ξ).ker := by
    refine sup_le ?_ fun y hy => ?_
    · rintro _ ⟨k, rfl⟩
      have := finPart_mul_inf ξ k
      rwa [GlobalTheory.ToricDistribution.inf_of_pow hm hp, mul_one] at this
    · refine GlobalTheory.CMVal.OrderUnits.finPart_eq_one_of_level htr (fun v => ?_) hy
      by_cases hv : v ∈ belowSet Q
      · refine ⟨1, ?_, fun P _ => htame P⟩
        rw [pow_one]
        exact Dvd.dvd.mul_left (Finset.dvd_prod_of_mem (fun q : HeightOneSpectrum (OF E) => q.asIdeal) hv) _
      · exact ⟨0, by rw [pow_zero]; exact one_dvd _, fun P hP => (ξ.unrAt_iff P).1 (hξu v hv P hP)⟩
  have hψ : ∀ y, finPart ξ y = QuotientGroup.lift _ (finPart ξ) hker (QuotientGroup.mk y) := fun _ => rfl
  obtain ⟨hfin, S, hS, hT⟩ := (isTwistedSum_iff_isToricSum hψ _).2 t
  exact ⟨_, fun ψ => ∑ᶠ q : PicO (condQ 𝔣 (belowSet Q)), ((ψ q : ℂˣ) : ℂ)⁻¹ * (lamF χ s q.out)⁻¹ * S q 0, hψ,
    fun ψ => ⟨hfin, S, hS, rfl⟩, hT⟩

theorem dvd_cond0 {D : D7} {T : Type} {Lc : Formalism.IndefR.Links.LevCh D T} (P : GlobalTheory.ChiGrid.Places Lc) (v : HeightOneSpectrum (OF D.host.E))
    (h : v.asIdeal ∣ GlobalTheory.FunObj.SqNum.condF P) : v.asIdeal ∣ GlobalTheory.LamTie.cond0 D.host (P.w P.v0) := by
  obtain ⟨u, hu, hd⟩ := (v.prime.dvd_finsetProd_iff _).1 h
  have e : v = u := HeightOneSpectrum.ext
    (associated_iff_eq.1 ((v.irreducible.dvd_irreducible_iff_associated u.irreducible).1 (v.prime.dvd_of_dvd_pow hd)))
  subst e
  rcases P.mem_S0_of_sum_eq.1 hu with h0 | h1
  · have e : below (P.w P.v0) = v := (P.under_w (P.mem_S0_of_sum_eq.2 (Or.inl rfl))).trans h0.symm
    unfold GlobalTheory.LamTie.cond0
    rw [e]
    exact dvd_mul_left _ _
  · refine Dvd.dvd.mul_right (Dvd.dvd.pow (Ideal.dvd_span_singleton.2 ?_) two_ne_zero) _
    push_cast
    rcases (GlobalTheory.ChiGrid.S1_mem_OmF D).1 h1 with h | h | h | h
    · exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ h))
    · exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ h))
    · exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ h)
    · exact Ideal.mul_mem_left _ _ h

end GlobalTheory.ThmARatio

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw


theorem _root_.GlobalTheory.T.hasDerivAt_heisenbergTranslate_fockBox : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (M : Vol G)
    (e : Num G i j) (Bs : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E)
    (om : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (h : IsTripleOf W M t i j e Bs Γ X), IsTriple Bs Γ X om om' → ∀ n Φ τ τ', HasFlip B t ρ i j n Φ τ τ' →
    ∀ u, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) u → ∀ P : PolT G (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.routeA t i j), ∃ b : PolT G (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.routeA t i j) →₀ ℂ,
    ∀ d ∈ (τ : TotT G (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.routeA t i j)).support, ∀ v, HasDerivAt (fun s : ℝ =>
      W.ψ (⅟(2 : AF D.host.F) * ((Γ.M.co.e v).1 ⬝ᵥ (Γ.M.co.e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F s • u)).2 -
        (Γ.M.co.e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F s • u)).1 ⬝ᵥ (Γ.M.co.e v).2)) *
      GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.boxA e (Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) d P) (v + GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F s • u))
      (b.sum fun P' c => c * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.boxA e (Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) d P') v) 0 := by
  first | exact @GlobalTheory.RouteBoxDeriv.hasDerivAt_box | exact GlobalTheory.RouteBoxDeriv.hasDerivAt_box | (intros; apply GlobalTheory.RouteBoxDeriv.hasDerivAt_box <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertVacLag

theorem vac_not_mem_augAt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    G.M'.vac v ∉ augAt om' v := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v w hvw hvT hmem
  obtain ⟨C, l, hC, hl, hne⟩ := GlobalTheory.T.exists_lagrangian_invariantForm_inertVacuum F E σ B a a' G X om om' hT v w hvw hvT
  have hle : augAt om' v ≤ LinearMap.ker l := by
    refine Submodule.span_le.2 ?_
    rintro z ⟨g, hg, φ, hφ, φ₁, hφ₁, ha, rfl⟩
    show φ₁ - φ ∈ LinearMap.ker l
    rw [LinearMap.mem_ker, map_sub,
      GlobalTheory.InertVacLag.inv_of_heisInv F E σ B a a' G X om om' hT v w hvw hvT _ C hC l hl g hg φ hφ φ₁ hφ₁ ha, sub_self]
  exact hne (hle hmem)

end GlobalTheory.InertVacLag
end
end

section

open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn

namespace GlobalTheory.SplitLevelsBall

theorem setOf_prime_mem_eq_primesOver (E : Type) [Field E] [NumberField E] (g : ℕ) (hg : g.Prime) :
    {P : Ideal (𝓞 E) | P.IsPrime ∧ (g : 𝓞 E) ∈ P} = (Ideal.span {(g : ℤ)}).primesOver (𝓞 E) := by
  ext P
  simp only [Set.mem_setOf_eq, Ideal.primesOver, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hP, hgP⟩
    refine ⟨hP, ⟨?_⟩⟩
    have hmax : (Ideal.span {(g : ℤ)}).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hg).irreducible
    have hle : Ideal.span {(g : ℤ)} ≤ P.under ℤ := by
      rw [Ideal.span_le, Set.singleton_subset_iff]
      show (g : ℤ) ∈ Ideal.comap (algebraMap ℤ (𝓞 E)) P
      rw [Ideal.mem_comap, map_natCast]
      exact hgP
    have hne : P.under ℤ ≠ ⊤ := (Ideal.IsPrime.comap (f := algebraMap ℤ (𝓞 E)) (hK := hP)).ne_top
    exact hmax.eq_of_le hne hle
  · rintro ⟨hP, hlo⟩
    refine ⟨hP, ?_⟩
    have : (g : ℤ) ∈ P.under ℤ := by
      rw [← hlo.over]; exact Ideal.mem_span_singleton_self _
    simpa [Ideal.under, Ideal.mem_comap] using this

theorem isTotallySplitPrime_of_splitsCompletely :
    ∀ (E : Type) [Field E] [NumberField E] (g : ℕ), SplitsCompletely E g → GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.IsTotallySplitPrime E g := by
  intro E _ _ g ⟨hg, hc⟩
  exact ⟨hg, by rw [← setOf_prime_mem_eq_primesOver E g hg]; exact hc⟩

end GlobalTheory.SplitLevelsBall
end

section

set_option autoImplicit false

open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn

namespace GlobalTheory.UpperArith

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {U C : Type} [Group U] [MulAction U C]

theorem tr_one_mem (M : TwoLevels E r U C) (c : C) : M.tr 1 c ∈ (M.comp c).Γ := by
  have h := M.tr_mul 1 1 c
  simp only [mul_one, one_smul, mul_inv_rev, ← mul_assoc, mul_inv_cancel, one_mul] at h
  simpa using (M.comp c).Γ.inv_mem h

def upperSub (M : TwoLevels E r U C) (c : C) : Subgroup (GL (Fin r) E) where
  carrier := M.upper c
  one_mem' := ⟨1, one_smul U c, (M.tr 1 c)⁻¹, (M.comp c).Γ.inv_mem (tr_one_mem M c), by simp⟩
  mul_mem' := by
    rintro _ _ ⟨u, hu, γ, hγ, rfl⟩ ⟨v, hv, δ, hδ, rfl⟩
    have hc := (M.tr_conj u c δ).1 hδ
    rw [hu] at hc
    have hm := M.tr_mul u v c
    rw [hv, mul_smul, hv, hu] at hm
    refine ⟨u * v, by rw [mul_smul, hv, hu], γ * (M.tr u c * δ * (M.tr u c)⁻¹) *
      (M.tr (u * v) c * (M.tr u c * M.tr v c)⁻¹)⁻¹, ?_, ?_⟩
    · exact (M.comp c).Γ.mul_mem ((M.comp c).Γ.mul_mem hγ hc) ((M.comp c).Γ.inv_mem hm)
    · group
  inv_mem' := by
    rintro _ ⟨u, hu, γ, hγ, rfl⟩
    have hu' : u⁻¹ • c = c := by rw [inv_smul_eq_iff, hu]
    have hm := M.tr_mul u⁻¹ u c
    rw [hu, inv_mul_cancel, one_smul] at hm
    have h1 := tr_one_mem M c
    have hε : M.tr u⁻¹ c * M.tr u c ∈ (M.comp c).Γ := by
      have := (M.comp c).Γ.mul_mem ((M.comp c).Γ.inv_mem hm) h1
      simpa [mul_inv_rev, mul_assoc] using this
    have hc : (M.tr u c)⁻¹ * γ⁻¹ * M.tr u c ∈ (M.comp c).Γ := by
      rw [M.tr_conj u c, hu]
      simpa [mul_assoc] using (M.comp c).Γ.inv_mem hγ
    refine ⟨u⁻¹, hu', (M.tr u c)⁻¹ * γ⁻¹ * M.tr u c * (M.tr u⁻¹ c * M.tr u c)⁻¹,
      (M.comp c).Γ.mul_mem hc ((M.comp c).Γ.inv_mem hε), ?_⟩
    group

theorem prime_and_mem_of_primesOver {g : ℕ} {P : Ideal (𝓞 E)}
    (hP : P ∈ (Ideal.span {(g : ℤ)}).primesOver (𝓞 E)) : P.IsPrime ∧ (g : 𝓞 E) ∈ P := by
  obtain ⟨hp, hl⟩ := hP
  refine ⟨hp, ?_⟩
  have hg : (g : ℤ) ∈ P.under ℤ := by
    rw [← hl.over]
    exact Ideal.mem_span_singleton_self _
  rw [Ideal.mem_comap] at hg
  simpa using hg

theorem upper_subgroup (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U]
    [MulAction U C] (M : TwoLevels E r U C) (c : C) (g : ℕ) (hU : M.UnipotentOver g) :
    ∃ Γo : Subgroup (GL (Fin r) E), (∀ γ ∈ Γo, IsUStab (M.comp c).Gm (M.comp c).L' γ) ∧
      (∀ γ ∈ Γo, GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.IsUnipotentModOver (M.comp c).L' g γ) ∧
      ∀ u : U, u • c = c → M.tr u c ∈ Γo := by
  refine ⟨upperSub M c, ?_, ?_, ?_⟩
  · rintro _ ⟨u, hu, δ, hδ, rfl⟩
    have hs := (M.comp c).Γ_stab δ hδ
    refine ⟨fun v w => ?_, fun v => ?_⟩
    · rw [Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hs.1, M.comp_Gm, M.tr_herm]
    · rw [Units.val_mul, ← Matrix.mulVec_mulVec, M.tr_L' u c v, hu]
      exact M.Γ_L' c δ hδ _
  · intro γ hγ P hP
    obtain ⟨hp, hg⟩ := prime_and_mem_of_primesOver hP
    exact ⟨r, fun v hv => hU c γ hγ P hp hg v hv⟩
  · intro u hu
    exact ⟨u, hu, 1, (M.comp c).Γ.one_mem, (one_mul _).symm⟩

end GlobalTheory.UpperArith
end

section

open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn

namespace GlobalTheory.LevelSplit

theorem primesOver_eq (E : Type) [Field E] [NumberField E] {g : ℕ} (hg : g.Prime) :
    (Ideal.span {(g : ℤ)}).primesOver (𝓞 E) = {P : Ideal (𝓞 E) | P.IsPrime ∧ (g : 𝓞 E) ∈ P} := by
  ext P
  simp only [Ideal.primesOver, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hP, hL⟩
    refine ⟨hP, ?_⟩
    have h1 : (g : ℤ) ∈ Ideal.span {(g : ℤ)} := Ideal.mem_span_singleton_self _
    rw [hL.over] at h1
    simpa using (Ideal.mem_comap.mp h1)
  · rintro ⟨hP, hgP⟩
    refine ⟨hP, ⟨?_⟩⟩
    have hmax : (Ideal.span {(g : ℤ)}).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hg).irreducible
    refine hmax.eq_of_le (Ideal.comap_ne_top _ hP.ne_top) ?_
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap]
    simpa using hgP

end GlobalTheory.LevelSplit

theorem GlobalTheory.levelHyp_totallySplit_unipotent : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [MulAction U C] (M : TwoLevels E r U C), LevelHyp M → ∃ g : ℕ, GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.IsTotallySplitPrime E g ∧ 3 * r < g ∧ ∀ c, ∀ β ∈ M.upper c, GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.IsUnipotentModOver (M.comp c).L' g β := by
  intro E _ _ _ r U C _ _ M hM
  obtain ⟨g, ⟨hg, hcard⟩, hgr, hU⟩ := hM
  have hset := GlobalTheory.LevelSplit.primesOver_eq E hg
  refine ⟨g, ⟨hg, ?_⟩, hgr, ?_⟩
  · rw [hset]; exact hcard
  · intro c β hβ P hP
    rw [hset] at hP
    exact ⟨r, fun v hv => hU c β hβ P hP.1 hP.2 v hv⟩
end

section

open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn

set_option autoImplicit false

namespace GlobalTheory.CompFin

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}


omit [NumberField E] [IsCMField E] in
theorem castFrame_castFrame {Ψ Ψ' : Finset (E →+* ℂ)} (h : Ψ = Ψ') (x : Frame Ψ' r) :
    castFrame h (castFrame h.symm x) = x := rfl

theorem castFrame_mem_GG (X : Data E r) {Ψ : Finset (E →+* ℂ)} (h : X.Ψ = Ψ) (x : Frame X.Ψ r) :
    castFrame h x ∈ GG Ψ X.Gm X.p0 ↔ x ∈ X.dom := by
  subst h
  rfl

variable {U C : Type} [Group U] [MulAction U C] (M : TwoLevels E r U C)

theorem castFrame_mem_dom (c : C) (x : Frame (M.comp c).Ψ r) :
    castFrame (M.comp_Ψ c) x ∈ M.dom ↔ x ∈ (M.comp c).dom := by
  have := castFrame_mem_GG (M.comp c).toData (M.comp_Ψ c) x
  rw [M.comp_Gm c, M.comp_basePoint c] at this
  exact this

def toComp (c : C) : (C → M.dom → ℂ) →ₗ[ℂ] ((M.comp c).dom → ℂ) where
  toFun v x := v c ⟨castFrame (M.comp_Ψ c) x.1, (castFrame_mem_dom M c x.1).2 x.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem cusp_le_comap (ka : Wt M.Ψ r) (c : C) :
    M.cusp ka ≤ (Submodule.span ℂ ((fun f : Frame (M.comp c).Ψ r → ℂ => fun x : (M.comp c).dom => f x) ''
      (M.comp c).SS (castWt (M.comp_Ψ c) ka))).comap (toComp M c) := by
  unfold TwoLevels.cusp
  rw [Submodule.span_le]
  rintro _ ⟨F, hF, rfl⟩
  exact Submodule.subset_span ⟨_, hF c, rfl⟩

theorem toComp_inj (v w : C → M.dom → ℂ) (h : ∀ c, toComp M c v = toComp M c w) : v = w := by
  funext c y
  have hy : castFrame (M.comp_Ψ c).symm y.1 ∈ (M.comp c).dom :=
    (castFrame_mem_dom M c _).1 (by rw [castFrame_castFrame]; exact y.2)
  have := congrFun (h c) ⟨_, hy⟩
  exact this

end

end GlobalTheory.CompFin


open GlobalTheory.CompFin in
theorem GlobalTheory.cusp_finite_of_comp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [Finite C] [MulAction U C] (M : TwoLevels E r U C) (ka : Wt M.Ψ r), (∀ c : C, FiniteDimensional ℂ (Submodule.span ℂ ((fun f : Frame (M.comp c).Ψ r → ℂ => fun x : (M.comp c).dom => f x) '' (M.comp c).SS (castWt (M.comp_Ψ c) ka)))) → Module.Finite ℂ (M.cusp ka) := by
  intro E _ _ _ r U C _ _ _ M ka hfin
  let S : (c : C) → Submodule ℂ ((M.comp c).dom → ℂ) := fun c => Submodule.span ℂ ((fun f : Frame (M.comp c).Ψ r → ℂ =>
    fun x : (M.comp c).dom => f x) '' (M.comp c).SS (castWt (M.comp_Ψ c) ka))
  have : ∀ c, Module.Finite ℂ (S c) := hfin
  let Φ : M.cusp ka →ₗ[ℂ] (∀ c, S c) := LinearMap.pi fun c =>
    ((toComp M c).domRestrict (M.cusp ka)).codRestrict (S c) fun v => cusp_le_comap M ka c v.2
  have hΦ : Function.Injective Φ := by
    intro v w hvw
    apply Subtype.ext
    apply toComp_inj M
    intro c
    have := congrArg Subtype.val (congrFun hvw c)
    exact this
  exact Module.Finite.of_injective Φ hΦ
end

section

open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn

namespace GlobalTheory.UpperStab

theorem upper_isUStab (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [MulAction U C]
    (M : TwoLevels E r U C) (c : C) :
    ∀ β ∈ M.upper c, IsUStab (M.comp c).Gm (M.comp c).L' β ∧ IsUStab (M.comp c).Gm (M.comp c).Λ β := by
  rintro β ⟨u, hu, γ, hγ, rfl⟩
  have hs := (M.comp c).Γ_stab γ hγ
  have hh : ∀ x y, herm (M.comp c).Gm (Matrix.mulVec ((γ * M.tr u c : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) x)
      (Matrix.mulVec ((γ * M.tr u c : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) y) = herm (M.comp c).Gm x y := by
    intro x y
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hs.1, M.comp_Gm c, M.tr_herm]
  refine ⟨⟨hh, fun v => ?_⟩, ⟨hh, fun v => ?_⟩⟩
  · have h1 := M.tr_L' u c v
    rw [hu] at h1
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, h1]
    exact M.Γ_L' c γ hγ _
  · have h1 := M.tr_Λ u c v
    rw [hu] at h1
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, h1]
    exact hs.2 _

end GlobalTheory.UpperStab
end
