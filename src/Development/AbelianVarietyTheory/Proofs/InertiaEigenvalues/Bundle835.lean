module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle800
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle006
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle027
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle831
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle827
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BaseEmbeddingReadingEvalAdelicFunction
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RationalHeckeScalars
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle166
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle156
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeIsogenyThetaGeneratorTransport
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle207
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TransformIntegral
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle008
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.EmbedsLevelZeroDepthZero
public import Formalism.AdmissibleDesigns.RestrictedSevenEightOfFull
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Formalism.SharpRestriction.LevelLetterCocycles.LiftingTheory
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle832
import Formalism.SharpRestriction.LevelLetterCocycles.BaseChangePreservesUnitaryOf
public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.Padics.Complex
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle830
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle462
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
import Mathlib.Algebra.Module.StablyFree.Basic
import Formalism.SharpRestriction.LevelLetterCocycles.EndomorphismIndexBound
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open GlobalTheory.RawLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.siegelEisenstein_doubledTheta_terms_eq_lagrangianIntegrals : ∀ (D : D7) ψ (V W : HSp D) χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr, SWSetup ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr → ∀ f₁ f₂, IsThetaFunO ψ V W f₁ → IsThetaFunO ψ V W f₂ → ∀ (ν : Measure (Mx D V.rank W.rank)) (𝓖' : Set (Mx D V.rank W.rank)), IsCovolOne (ratL V W) ν 𝓖' → ∃ e : GlobalTheory.Eis.Cosets (GlobalTheory.Doubling.siegel W) (GQ (GlobalTheory.Doubling.dblSp W)) ≃ Lag W, ∀ q, ∃ C, IsLagFrame W (e q) C ∧ ∫ y in 𝓖', GlobalTheory.SWPairProof.dbl V W f₁ f₂ (actO (GlobalTheory.Doubling.dblSp W) V ((q.out : GQ (GlobalTheory.Doubling.dblSp W)) : GA D (GlobalTheory.Doubling.dblSp W))⁻¹ 1 (GlobalTheory.SiegelFormula.lagr W V y)) ∂ν = lagTerm μ 𝓕 C f₁ f₂ := by
  first | exact @GlobalTheory.SWLagTerms.lagTerms_eq | exact GlobalTheory.SWLagTerms.lagTerms_eq | (intros; apply GlobalTheory.SWLagTerms.lagTerms_eq <;> assumption)
end

section

open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.DivPtLocal.Count

variable {E : Type} [Field E] [NumberField E] (w : IsDedekindDomain.HeightOneSpectrum (𝓞 E))

def red (N m n : ℕ) : ↥(locDiv w N m n) →+
    (Fin m → Fin n → (w.adicCompletionIntegers E ⧸ Ideal.span {((N : ℕ) : w.adicCompletionIntegers E)})) where
  toFun X i j := Ideal.Quotient.mk _ (⟨(N : w.adicCompletion E) * X.1 i j, X.2 i j⟩ : w.adicCompletionIntegers E)
  map_zero' := by
    funext i j
    rw [Pi.zero_apply, Pi.zero_apply, ← map_zero (Ideal.Quotient.mk _)]
    congr 1
    apply Subtype.ext
    simp
  map_add' X Y := by
    funext i j
    rw [Pi.add_apply, Pi.add_apply, ← map_add (f := _)]
    congr 1
    apply Subtype.ext
    simp [mul_add]

theorem natCast_ne_zero {N : ℕ} (hN : 0 < N) : (N : w.adicCompletion E) ≠ 0 := by
  have h : (N : w.adicCompletion E) = algebraMap E (w.adicCompletion E) (N : E) := by simp
  rw [h]
  exact (map_ne_zero _).mpr (Nat.cast_ne_zero.mpr hN.ne')

theorem red_surjective {N : ℕ} (hN : 0 < N) (m n : ℕ) : Function.Surjective (red w N m n) := by
  intro Y
  have hN' := natCast_ne_zero w hN
  choose Z hZ using fun i j => Ideal.Quotient.mk_surjective (Y i j)
  have key : ∀ i j, (N : w.adicCompletion E) * ((N : w.adicCompletion E)⁻¹ * (Z i j : w.adicCompletion E))
      = Z i j := fun i j => by rw [← mul_assoc, mul_inv_cancel₀ hN', one_mul]
  refine ⟨⟨Matrix.of fun i j => (N : w.adicCompletion E)⁻¹ * (Z i j : w.adicCompletion E), ?_⟩, ?_⟩
  · intro i j
    rw [Matrix.of_apply, key]
    exact (Z i j).2
  · funext i j
    rw [← hZ]
    change Ideal.Quotient.mk _ _ = _
    congr 1
    apply Subtype.ext
    exact key i j

theorem ker_red {N : ℕ} (hN : 0 < N) (m n : ℕ) :
    (red w N m n).ker = (locInt w m n).addSubgroupOf (locDiv w N m n) := by
  have hN' := natCast_ne_zero w hN
  ext X
  rw [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf, mem_locInt]
  simp only [funext_iff, Pi.zero_apply]
  refine forall_congr' fun i => forall_congr' fun j => ?_
  change Ideal.Quotient.mk _ _ = _ ↔ _
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨c, hc⟩
    have h := congrArg (fun z : w.adicCompletionIntegers E => (z : w.adicCompletion E)) hc
    simp only [MulMemClass.coe_mul, SubringClass.coe_natCast] at h
    rw [mul_left_cancel₀ hN' h]
    exact c.2
  · intro h
    refine ⟨⟨X.1 i j, h⟩, ?_⟩
    apply Subtype.ext
    simp

theorem card_locQ (E : Type) [Field E] [NumberField E] (w : IsDedekindDomain.HeightOneSpectrum (𝓞 E))
    (N m n : ℕ) (hN : 0 < N) :
    Nat.card (GlobalTheory.DivPtLocal.LocQ w N m n) =
      Nat.card (w.adicCompletionIntegers E ⧸ Ideal.span {((N : ℕ) : w.adicCompletionIntegers E)}) ^ (m * n) := by
  have e := (QuotientAddGroup.quotientAddEquivOfEq (ker_red w hN m n).symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective (red w N m n) (red_surjective w hN m n))
  rw [Nat.card_congr e.toEquiv, Nat.card_fun, Nat.card_fun, ← pow_mul]
  simp [mul_comm]

end GlobalTheory.DivPtLocal.Count

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2 Formalism.L2.DIV Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT NumberField IsDedekindDomain
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeckeReadRational

section SlopeTestRemainingChoices

open Formalism.IndefR.Arith Formalism.IndefR.Mult Formalism.IndefR.Lev GlobalTheory.IndefiniteRowSideFullHecke.LatticesOverBalls GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

theorem hkC_eq_heckeScalar {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
    (i : Fin D.R.m) (P : Formalism.L2.DIV.Pl D.host.E) (k : ℕ) : hkC R i P k = heckeScalar R i P k := by
  rw [hkC, heckeScalar, zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]

theorem heckeOn_mem_wall_of_hkData {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    {i : Fin D.R.m} (hβ' : IsSDFrame (Wc D i) (R.βW i) (R.ΛW i) 1) (hSb : R.fam_Sb) (hHW : R.models_HW)
    (σ : D.what₂.LL →+* ℂ) {P : Formalism.L2.DIV.Pl D.host.E} {k : ℕ} {α : GA D (Wc D i)} {Rc : Finset (GA D (Wc D i))}
    (hd : IsHkData R i P k α Rc) (z : (R.HW i σ).H) :
    heckeOn (R.MW i σ) Rc ((R.HW i σ).e z) ∈ R.Wall i σ := by
  obtain ⟨hso, -, -, ⟨e, ϖ, he, -, -, hα⟩, hR⟩ := hd
  obtain ⟨c, hβ⟩ := hβ'
  have hN : ((1 ^ c : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
    rw [one_pow, Nat.cast_one]
    exact (Ideal.ne_top_iff_one _).1 P.isPrime.ne_top
  have hoff : ∀ PP, PP ∈ (R.datWp i R.triv).Pg ∨ PP ∈ (R.datWp i R.triv).Q → PP ≠ P ∧ ¬ Lev.IsConjPl PP P := by
    intro PP hPP
    have hPP' : PP ∈ R.Pg := hPP.elim id fun h => absurd h (Finset.notMem_empty _)
    have hS : PP ∈ (R.Sb : Set (Formalism.L2.DIV.Pl D.host.E)) := hSb hPP'
    refine ⟨fun h => hso.2.1 (h ▸ hS), fun h => hso.2.2 PP hS ?_⟩
    rw [Formalism.L2.Col.conjIdeal_asIdeal]
    refine PP.isMaximal.eq_of_le (Formalism.L2.Col.conjPrime₂ P).isPrime.ne_top fun a ha => ?_
    obtain ⟨a', ha', e⟩ := h a ha
    rw [Formalism.L2.Col.mem_conjP]
    have : Formalism.L2.Col.cO D.host.E a = a' := RingOfIntegers.ext e.symm
    rwa [this]
  have hp : IsPrimeIdem P e (e + cA D e) := Or.inl ⟨he, rfl⟩
  have hq := (GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents (Wc D i)).2.2.1 P e _ hp
  obtain ⟨large₂, hLg⟩ := ((GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents (Wc D i)).1 _ hq.1 hq.2.1).1
  have hK : ∀ g, g ∈ levG (Wc D i) (R.βW i) (R.datWp i R.triv) ⊓ large₂ ↔ g ∈ locPart (Wc D i) (KsphC (Wc D i) ∅) e := by
    intro g
    have h1 := ((GlobalTheory.T.level_hyperspecial_trivialCharacter_splits_off_places (Wc D i) (R.βW i) _ _ (R.datWp i R.triv) hβ).2 P e _ hp hN hoff).1 g
    exact ⟨fun h => ⟨(h1 ((hLg g).1 h.2)).1 h.1, (hLg g).1 h.2⟩, fun h => ⟨(h1 h.2).2 h.1, (hLg g).2 h.2⟩⟩
  have hoL := GlobalTheory.HeckeModel.offAt_of_place hβ he hN hoff hLg hK
  have hαL : α ∈ large₂ := (hLg α).2 hα.2.1
  obtain ⟨A₀, hA₀⟩ := GlobalTheory.HeckeSup.exists_local_isDC hoL.splits hαL hR
  have key : heckeOn (R.MW i σ) Rc ((R.HW i σ).e z) = heckeOn (R.MW i σ) A₀ ((R.HW i σ).e z) := by
    ext v : 1
    show heckeLin (Wc D i) Rc ((R.HW i σ).e z v) = heckeLin (Wc D i) A₀ ((R.HW i σ).e z v)
    exact funext fun h => GlobalTheory.HeckeModel.sum_eq_of_isDC hR (hoL.splits.isDC hαL hA₀) ⟨1, 1, by simp⟩
      (GlobalTheory.HeckeSup.model_inv_cl hHW i σ z v) h
  rw [key]
  exact GlobalTheory.HeckeModel.heckeOn_mem_mult hoL (fun g hg => hq.2.2.1 g ((hLg g).1 hg)) hαL hA₀
    (show (R.HW i σ).e z ∈ R.Wall i σ from (hHW i σ).2.1 ▸ LinearMap.mem_range_self _ z)

end SlopeTestRemainingChoices

section Main

open Formalism.IndefR.Mult



theorem rationalHecke_of_readsCusp : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : Formalism.L2.Pj.CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : Formalism.IndefR.FWT.FWTie T R κ v₀) (i : Fin D.R.m), GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection.HeckeTransform → R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels → (∀ hV : T.V ((i : ℕ) + 1) (Formalism.IndefR.FWT.res T (sg0 D A)) = Wc D i, Formalism.IndefR.FWT.JEvAt T R κ v₀ i (sg0 D A) hV) → Function.Injective ((R.FW i).j (sg0 D A)) → (∀ hV : T.V ((i : ℕ) + 1) (Formalism.IndefR.FWT.res T (sg0 D A)) = Wc D i, GlobalTheory.HeckeSup.ReadsCusp T R κ i (Formalism.IndefR.FWT.res T (sg0 D A)) hV) → GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.RationalHecke R i := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ fw i hT hlev hfam hmod hex _ hR P hP k hk
  have hHW : R.models_HW := hmod.HW
  have hV : T.V ((i : ℕ) + 1) (res T (sg0 D A)) = Wc D i :=
    fw.laws.spaceW _ (inR i) _ (base_embedding_good T R fw.alg_eq fw.laws.pins.2.2.1)
  obtain ⟨p, m, hp, hpP, -⟩ := GlobalTheory.HeckeSup.exists_prime_under P
  have hoff := GlobalTheory.HeckeSup.not_dvd_level fw.laws hpP hP.2
  have hsp := GlobalTheory.HeckeSup.split_of_ne (H := T.Q.H) hP.1.1
  have hn : (κ i).n = D.R.nV := (fw.kap i (D.eTau.symm 1)).2.2
  have htr : ∀ f : Cu T κ i, ∃ g ∈ T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n,
      GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.GeoHecke T ((i : ℕ) + 1) P.asIdeal p k
        (hkScal T.Q.c ((Nat.card (kP P) : T.Q.c.F)⁻¹ ^ (k * D.R.nV / 2)) P.asIdeal k D.R.nV) f g := by
    intro f
    obtain ⟨g, hg, hfg⟩ := GlobalTheory.HeckeSup.exists_transform hT GlobalTheory.ThetaTransport.heckePointLaws fw.laws i
      ⟨P.isMaximal, hsp, hp, hpP, hoff⟩ hk ((Nat.card (kP P) : T.Q.c.F)⁻¹ ^ (k * D.R.nV / 2)) (dom_wtA (κ i)) f f.2
    rw [show hkScal T.Q.c ((Nat.card (kP P) : T.Q.c.F)⁻¹ ^ (k * D.R.nV / 2)) P.asIdeal k (κ i).n =
      hkScal T.Q.c ((Nat.card (kP P) : T.Q.c.F)⁻¹ ^ (k * D.R.nV / 2)) P.asIdeal k D.R.nV by rw [hn]] at hfg
    exact ⟨g, hg, hfg⟩
  choose g hg hfg using htr
  have hEI := GlobalTheory.EvalAtUnitVector.evInj T R v₀ hHW fw.hv₀ i _ (base_embedding_good T R fw.alg_eq fw.laws.pins.2.2.1)
  have hread : ∀ f : Cu T κ i, ∀ Rc, GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.IsCosetSys R i P k Rc →
      (R.HW i (sg0 D A)).e ((R.FW i).j (sg0 D A) (fw.e i ⟨g f, hg f⟩ : (R.FW i).WK)) =
        GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.heckeScalar R i P k • heckeOn (R.MW i (sg0 D A)) Rc
          ((R.HW i (sg0 D A)).e ((R.FW i).j (sg0 D A) (fw.e i f : (R.FW i).WK))) := by
    rintro f Rc ⟨α, hα, hRc⟩
    have hd : GlobalTheory.IndefiniteRowSideFullHecke.LatticesOverBalls.IsHkData R i P k α Rc := ⟨hP.1, hP.2, hk, hα, hRc⟩
    have h1 := hR hV P p k α Rc hd ⟨hP.1, hp, hpP, hoff, hk, hα, hRc⟩ f f.2 (g f) (hg f) (hfg f)
    rw [hkC_eq_heckeScalar] at h1
    obtain ⟨z', hz'⟩ : ∃ z', (R.HW i (sg0 D A)).e z' = heckeOn (R.MW i (sg0 D A)) Rc
        ((R.HW i (sg0 D A)).e ((R.FW i).j (sg0 D A) (fw.e i f : (R.FW i).WK))) := by
      rw [← LinearMap.mem_range, (hHW i _).2.1]
      exact heckeOn_mem_wall_of_hkData (hlev.βW i) hfam.Sb hHW _ hd _
    have e1 : (R.FW i).j (sg0 D A) (fw.e i ⟨g f, hg f⟩ : (R.FW i).WK) = GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.heckeScalar R i P k • z' := by
      apply hEI
      refine (GlobalTheory.HeckeSup.baseEmbedding_reading_eval_adelicFunction fw hV (hex hV) ⟨g f, hg f⟩).trans ?_
      funext h
      rw [h1 h, ← GlobalTheory.HeckeSup.baseEmbedding_reading_eval_adelicFunction fw hV (hex hV) f]
      unfold evAt
      rw [map_smul, hz']
      simp [heckeOn, postOn, heckeLin]
      exact Or.inl rfl
    rw [e1, map_smul, hz']
  obtain ⟨n, b, hbK, -, hKspan, hLind, hLspan⟩ := fw.ks i
  let B : Module.Basis (Fin n) D.what₂.LL (Fin (R.nW i) → D.what₂.LL) := Module.Basis.mk hLind hLspan.ge
  have hB : ∀ l, B l = b l := fun l => Module.Basis.mk_apply hLind hLspan.ge l
  let f0 : Fin n → Cu T κ i := fun l => (fw.e i).symm ⟨b l, hbK l⟩
  let yv : Fin n → Fin (R.nW i) → D.what₂.LL := fun l => (fw.e i ⟨g (f0 l), hg (f0 l)⟩ : (R.FW i).WK)
  let hL := B.constr D.what₂.LL yv
  have hLb : ∀ l, hL (b l) = yv l := fun l => by rw [← hB l]; exact B.constr_basis _ _ _
  have hb0 : ∀ l, (fw.e i (f0 l) : Fin (R.nW i) → D.what₂.LL) = b l := fun l => by simp [f0]
  refine ⟨hL, fun Rc hRc => ?_, fun x hx => ?_⟩
  · have hext := B.ext (f₁ := ((R.HW i (sg0 D A)).e.comp ((R.FW i).j (sg0 D A))).comp hL)
      (f₂ := ((GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.heckeScalar R i P k • heckeOn (R.MW i (sg0 D A)) Rc).comp (R.HW i (sg0 D A)).e).comp
        ((R.FW i).j (sg0 D A))) fun l => by
      rw [hB l]
      simp only [LinearMap.comp_apply, LinearMap.smul_apply]
      rw [hLb l, ← hb0 l]
      exact hread (f0 l) Rc hRc
    intro x
    have := LinearMap.congr_fun hext x
    simpa only [LinearMap.comp_apply, LinearMap.smul_apply] using this
  · rw [← hKspan] at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨l, rfl⟩ := hx
      rw [hLb]
      exact (fw.e i _).2
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      rw [← algebraMap_smul D.what₂.LL a x, map_smul, algebraMap_smul]
      exact Submodule.smul_mem _ a hx

end Main

end GlobalTheory.HeckeReadRational
end
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel
open GlobalTheory.Parabolic (mem_fixed)

namespace GlobalTheory.DepthZeroPass

theorem fixed_ne_bot_of_isSubquotient {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {τ : Representation ℂ G W} (hρ : IsSmooth ρ) (h : IsSubquotient τ ρ)
    {H : Subgroup G} (hH : IsCompact (H : Set G)) (hτ : fixed τ H ≠ ⊥) : fixed ρ H ≠ ⊥ := by
  obtain ⟨S, f, hf⟩ := h
  obtain ⟨w, hw, hw0⟩ := (Submodule.ne_bot_iff _).1 hτ
  obtain ⟨u, rfl⟩ := hf w
  have hS : IsSmooth S.toRepresentation := fun v => by
    have : {g : G | S.toRepresentation g v = v} = {g : G | ρ g (v : V) = v} := by
      ext g
      simp only [Set.mem_setOf_eq, Subtype.ext_iff]
      rfl
    rw [this]
    exact hρ v
  obtain ⟨v, hv, hfv⟩ := IwahoriOnto.exists_fixed_map_eq hS hH f.toLinearMap u fun g hg => by
    have h1 := mem_fixed.1 hw g hg
    show f (S.toRepresentation g u) = f u
    exact (f.isIntertwining _ _ g u).trans h1
  refine (Submodule.ne_bot_iff _).2 ⟨(v : V), mem_fixed.2 fun g hg => ?_, ?_⟩
  · have := mem_fixed.1 hv g hg
    exact congrArg Subtype.val this
  · intro h0
    apply hw0
    have hv0 : v = 0 := Subtype.ext h0
    have hfv' : f v = f u := hfv
    rw [← hfv', hv0, map_zero]

theorem fixed_piTensor_ne_bot {α : Type} [Fintype α] [DecidableEq α] {Γ X : α → Type} [∀ a, Group (Γ a)]
    [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (Γ a) (X a))
    (H : ∀ a, Subgroup (Γ a)) (h : ∀ a, fixed (ρ a) (H a) ≠ ⊥) :
    fixed (piTensor ρ) (Subgroup.pi Set.univ H) ≠ ⊥ := by
  choose v hv hv0 using fun a => (Submodule.ne_bot_iff _).1 (h a)
  choose l hl using fun a => Module.Projective.exists_dual_eq_one ℂ (hv0 a)
  refine (Submodule.ne_bot_iff _).2 ⟨PiTensorProduct.tprod ℂ v, mem_fixed.2 fun g hg => ?_, fun h0 => ?_⟩
  · rw [piTensor_tprod]
    congr 1
    funext a
    exact mem_fixed.1 (hv a) (g a) (hg a trivial)
  · have := congrArg (PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ α ℂ).compLinearMap l)) h0
    simp [hl] at this

theorem isCompact_leviKOne {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {α : Type} {m : α → Type} [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] :
    IsCompact (leviKOne k m : Set (Levi k m)) := by
  rw [leviKOne, Subgroup.coe_pi]
  exact isCompact_univ_pi fun a => levelPre_bot (k := k) (n := m a) ▸ isCompact_levelPre ⊥

theorem depthZeroInduction : GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.BernsteinZelevinskyFiniteness →
    GlobalTheory.Published.ZelevinskyPolynomialRing → GlobalTheory.Published.DepthZeroInduction := by
  intro hG hBZ hZ k _ _ _ _ _ x s hs hfix
  obtain ⟨r, u, e, hu, hsq⟩ := GlobalTheory.T.exists_subquotient_jacquetModule_of_supercuspidalSupport hG hBZ hZ k x s hs
  have hxs : IsSmooth x.rep := x.2.rep.smooth
  have h1 : fixed (piTensor fun a => (u a).rep) (leviKOne k fun a => Fin (u a).1) ≠ ⊥ :=
    fixed_piTensor_ne_bot _ _ fun a => hfix _ (hu a)
  have h2 := fixed_ne_bot_of_isSubquotient (isSmooth_jac e hxs) hsq isCompact_leviKOne h1
  obtain ⟨y, hy1, hy0⟩ := (Submodule.ne_bot_iff _).1 h2
  have hy2 : y ∈ fixed (jacU e x.rep) (leviKOne k fun a => Fin (u a).1) := mem_fixed.2 fun g hg => by
    have h3 := mem_fixed.1 hy1 g hg
    have h4 : deltaHalf k (fun a => Fin (u a).1) g = 1 :=
      deltaHalf_of_mem_leviK fun a _ => StepData.KOne_le_KO (hg a trivial)
    simpa [_root_.GlobalTheory.SmGL.jac, _root_.GlobalTheory.SmGL.twist_apply, h4] using h3
  obtain ⟨v, hv, rfl⟩ := GlobalTheory.T.jacquet_proUnipotentRadical_fixed_vectors_lift k e x.rep ((hBZ k).1 _ _ x.rep hxs x.2.rep.irr) y hy2
  refine (Submodule.ne_bot_iff _).2 ⟨v, mem_fixed.2 fun g hg => mem_fixed.1 hv g (KOne_le_proRad e hg), ?_⟩
  rintro rfl
  exact hy0 rfl

end GlobalTheory.DepthZeroPass

end
end

section

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.WeaklyAdmissibleFiltrations

namespace GlobalTheory.InertiaEigenvalues.LengthBoundClosing

theorem stmt_closed : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ D : D7, Formalism.MainNotions.N.K.Rows.AllDesignConditions D → TruncatedSeriesCountingIdentities.Stmt D := by
  intro hA hB hT hE D h51
  exact ⟨GlobalTheory.T.integralityFromMetric_of_designConditionAll hA hB hT hE D h51, Formalism.MainNotions.TruncatedSeriesCountingIdentities.second_statement D⟩

end GlobalTheory.InertiaEigenvalues.LengthBoundClosing
end

section

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory

theorem localConstants_from_admitted_local_Galois_statements_alt : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK →
    ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F),
      LiftingTheory.aux₃ D HW F 10 23 32 32 :=
  fun _ _ _ D HW F Cm => Formalism.MainNotions.LiftingTheory.frobenius_lifting D HW F Cm (GlobalTheory.T.liftingTheorem_wachModuleLemma_hypotheses_admitted D HW F Cm).1

end GlobalTheory
end

section

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

theorem _root_.GlobalTheory.T.theorem_tb_of_local_blochKato_duality_euler : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), LocalSituation.Conclusion4 D HW F := by
  first | exact @GlobalTheory.TheoremTBRecords.aux_of_blochKato_tateDuality_eulerChar | exact GlobalTheory.TheoremTBRecords.aux_of_blochKato_tateDuality_eulerChar | (intros; apply GlobalTheory.TheoremTBRecords.aux_of_blochKato_tateDuality_eulerChar <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.L2.Pj GlobalTheory.GeoTie

theorem _root_.GlobalTheory.T.exists_uniformiser_norm_gap_padic_embedding : ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [NumberField F] (φ : F →+* ℂ_[p]), ∃ ϖ : F, 0 < ‖φ ϖ‖ ∧ ‖φ ϖ‖ < 1 ∧ ∀ c : F, ‖φ c‖ < 1 → ‖φ c‖ ≤ ‖φ ϖ‖ := by
  first | exact @GlobalTheory.UnifGap.exists_unif_norm_gap | exact GlobalTheory.UnifGap.exists_unif_norm_gap | (intros; apply GlobalTheory.UnifGap.exists_unif_norm_gap <;> assumption)
end
