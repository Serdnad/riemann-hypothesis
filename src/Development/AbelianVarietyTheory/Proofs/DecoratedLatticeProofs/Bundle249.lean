module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdempotentMulEntryEqZeroOfCutInverse
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle278
import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.HeckeThetaElements.IsHeckeElt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle162
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle174
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle214
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRingEquivPadicOfResidueCardUniformizerStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle164
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle211
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle216
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsTransportAdelicCorrection
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle099
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MeanPair
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAutomorphicFunctionTranslateAtRealPlace
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle008
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.QuasiOfFam
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle218
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalVolumeLift
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalZero
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle015
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle016
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HeckeFormNSOfHeckeForm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SphericalEisensteinSeriesOnGroup
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RegularisedSiegelWeilFirstTerm

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SplitDecomp

open GlobalTheory.SplitCut GlobalTheory.FinPl

variable {D : D7}

theorem real_idem_mul (y : AE D) (hy : infPart D y = 0) :
    algebraMap (AF D.host.F) (AE D) (pairA D.host.F 1 0) * y = 0 := by
  refine key_gen (Module.finBasis D.host.F D.host.E) _ y fun k => ?_
  have h1 : fstA D.host.F ((Algebra.TensorProduct.basis (AF D.host.F) (Module.finBasis D.host.F D.host.E)).repr y k) = 0 := by
    rw [← GlobalTheory.InfZeroFinSum.repr_map_id (Module.finBasis D.host.F D.host.E) (fstA D.host.F) y k]
    have : Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) y = 0 := hy
    rw [this, map_zero, Finsupp.zero_apply]
  refine baseAdele_ext_infinite_finite ?_ ?_
  · rw [map_mul, h1, mul_zero, map_zero]
  · rw [map_mul, map_zero]
    exact zero_mul _

theorem entry_memAt (V : HSp D) (P : Pl D → Prop) (g : GA D V) (hg : g ∈ grpAt V P) (i j : Fin V.rank) :
    (mt V g - 1) i j ∈ idAt D P := by
  have h := congrArg (fun x : GL (Fin V.rank) (AE D ⧸ idAt D P) => x.1 i j) (show _ = (1 : GL _ _) from hg)
  change Ideal.Quotient.mk (idAt D P) (mt V g i j) = _ at h
  have h2 : Ideal.Quotient.mk (idAt D P) (mt V g i j) =
      Ideal.Quotient.mk (idAt D P) ((1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j) := by
    rw [h, Units.val_one]; by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  rw [Matrix.sub_apply]; exact Ideal.Quotient.eq.mp h2



open GlobalTheory.LocWeil.PlaceIdem in
theorem prod_of_grpAt : ∀ (D : D7) (V : HSp D) (n : ℕ) (k : Fin n → Type) [∀ i, Field (k i)] [∀ i, ValuativeRel (k i)] [∀ i, TopologicalSpace (k i)] [∀ i, IsNonarchimedeanLocalField (k i)] (q : ∀ i, GlobalTheory.FinPl.SplitPt D (k i)), Function.Injective (fun i => (q i).v) → ∀ g ∈ GlobalTheory.FinPl.grpAt V (fun p => ∃ i, p = (q i).v), ∃ h : Fin n → GA D V, (∀ i, SuppAt (q i).e V (h i)) ∧ g = ((List.finRange n).map h).prod := by
  intro D V n k _ _ _ _ q hv g hg
  set E : Fin n → AE D := fun i => algebraMap (AF D.host.F) (AE D) (eFin D.host.F (q i).v) with hEdef
  have hE : ∀ i, (q i).e + cA D (q i).e = E i := fun i => by
    obtain ⟨ε, hε, h⟩ := (q i).above
    rw [h, eFin_of_placeIdem hε]
  have hEE : ∀ i, E i * E i = E i := fun i => by
    simp only [hEdef, ← map_mul, eFin_idem]
  have hEc : ∀ i, cA D (E i) = E i := fun i => cA_algebraMap _
  have hEo : ∀ i i', i ≠ i' → E i * E i' = 0 := fun i i' hii => by
    simp only [hEdef, ← map_mul]
    rw [eFin_mul_eFin _ (fun h => hii (hv h)), map_zero]
  choose h hh using fun i => cut_exists V g (E i) (hEE i) (hEc i)
  set M := mt V g with hM
  refine ⟨h, fun i a b => ?_, ?_⟩
  · rw [hE i, hh i]
    exact idempotent_mul_cut_sub_one_entry _ (hEE i) M a b
  · apply mt_injective
    rw [mt_list_prod V h E M hh hEo _ (List.nodup_finRange n)]
    have hsum : ((List.finRange n).map E).sum = ∑ i, E i := (Fin.sum_univ_def E).symm
    rw [hsum]
    refine exists_widePullback_of_iteratedLine _ M fun a b => ?_
    have hm := entry_memAt V _ g hg a b
    unfold idAt at hm
    obtain ⟨hinf, hoff⟩ := Ideal.mem_inf.mp hm
    rw [Ideal.mem_iInf] at hoff
    have h1 := key (fun i => (q i).v) hv ((M - 1) a b) (fun u hu =>
      (RingHom.mem_ker).mp (hoff ⟨u, fun ⟨i, hi⟩ => hu ⟨i, hi.symm⟩⟩))

    rw [map_sub, map_sub, map_one, map_sum] at h1
    have h2 := real_idem_mul ((M - 1) a b) ((RingHom.mem_ker).mp hinf)
    have h3 : (1 - ∑ i, E i) = (1 - algebraMap (AF D.host.F) (AE D) (pairA D.host.F 1 0) - ∑ i, E i) +
        algebraMap (AF D.host.F) (AE D) (pairA D.host.F 1 0) := by ring
    rw [h3, add_mul, h1, h2, add_zero]

end GlobalTheory.SplitDecomp
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.OtherPlace

theorem pr_placeIdem_other {D : D7} {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k']
    (q : GlobalTheory.FinPl.SplitPt D k) (q' : GlobalTheory.FinPl.SplitPt D k') (hv : q.v ≠ q'.v) :
    q.pr (q'.e + cA D q'.e) = 0 := by
  obtain ⟨ε, hε, hqe⟩ := q.above
  obtain ⟨ε', hε', hqe'⟩ := q'.above
  have hpr : ∀ x, q.pr x = q.pr (q.e * x) := fun x => by rw [← q.sec_pr, q.pr_sec]
  have he : q.e = q.e * algebraMap (AF D.host.F) (AE D) ε := by
    rw [← hqe, mul_add, q.split.1, q.split.2.1, add_zero]
  have hεε : ε * ε' = 0 := by
    rw [GlobalTheory.SplitCut.eFin_of_placeIdem hε, GlobalTheory.SplitCut.eFin_of_placeIdem hε']
    exact GlobalTheory.LocWeil.PlaceIdem.eFin_mul_eFin _ hv
  rw [hqe', hpr, he, mul_assoc, ← map_mul, hεε, map_zero, mul_zero, map_zero]

theorem mt_map_pr_eq_one : ∀ (D : D7) (k k' : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] (q : GlobalTheory.FinPl.SplitPt D k)
    (q' : GlobalTheory.FinPl.SplitPt D k') (V : HSp D) (g : GA D V), q.v ≠ q'.v → SuppAt q'.e V g → (mt V g).map q.pr = 1 := by
  intro D k k' _ _ _ _ _ _ _ _ q q' V g hv hs
  have h0 := pr_placeIdem_other q q' hv
  ext i j
  have h1 := congrArg q.pr (hs i j)
  rw [map_mul, h0, zero_mul, Matrix.sub_apply, map_sub] at h1
  rw [Matrix.map_apply, ← sub_eq_zero, ← h1.symm]
  have : q.pr ((1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j) = (1 : Matrix (Fin V.rank) (Fin V.rank) k) i j := by
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  rw [this]

end GlobalTheory.OtherPlace
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl ValuativeRel NumberField

namespace GlobalTheory.InhPt

open GlobalTheory.MixPer

theorem exists_char : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∃ χ : AddChar k Circle, p.IsChar ψ χ ∧ Continuous χ := by
  intro D k _ _ _ _ p ψ hψ
  have hn : ∀ x : AF D.host.F, ‖ψ x‖ = 1 := hψ.1.2.1
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have htr : Continuous (Algebra.trace (AF D.host.F) (AE D)) :=
    IsModuleTopology.continuous_of_linearMap _
  have hc : Continuous fun a : k => psiE ψ (p.sec a) := hψ.1.1.comp (htr.comp p.cont_sec)
  let χ : AddChar k Circle :=
    { toFun := fun a => ⟨psiE ψ (p.sec a), by simpa [Submonoid.unitSphere, psiE] using hn _⟩
      map_zero_eq_one' := by ext; simp [psiE]
      map_add_eq_mul' := by intro a b; ext; simp [psiE, map_add (f := _), AddChar.map_add_eq_mul]; rfl }
  exact ⟨χ, fun a => rfl, Continuous.subtype_mk hc _⟩

theorem exists_splitPt_frame_char : ∀ (D : D7), (∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [IsTopologicalRing k] [CharZero k] (T : ℕ), T.Prime → Nat.card (IsLocalRing.ResidueField 𝒪[k]) = T → Irreducible (T : 𝒪[k]) → ∀ (w : Formalism.L2.DIV.Pl D.host.E) (e : AE D), Formalism.L2.NTheta.IsIdemAt e w → IsSplitIdem D e → Ideal.absNorm w.asIdeal = T → ¬ (w.asIdeal ^ 2 ∣ Ideal.span {(T : 𝓞 D.host.E)}) → ∃ p : SplitPt D k, p.e = e) ∧ ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k), (∀ (S : HSp D) (n : Type) [Fintype n] [DecidableEq n] (b : Matrix (Fin S.rank) n k) (b' : Matrix n (Fin S.rank) k), b * b' = 1 → b' * b = 1 → ∃ β : Frame p S n, β.b = b) ∧ ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∃ χ : AddChar k Circle, p.IsChar ψ χ ∧ Continuous χ ∧ χ ≠ 1 ∧ (p.UnitAA → GlobalTheory.SplitWeil.HasConductor χ 1) := by
  intro D
  refine ⟨?_, ?_⟩
  · intro k _ _ _ _ _ _ T hT hcard hirr w e hw he hN hsq
    haveI := Fact.mk hT
    obtain ⟨φ, hφ, hφs, hφO⟩ := GlobalTheory.T.exists_ringEquiv_padic_of_residueCard_uniformizer k T hcard hirr
    obtain ⟨v, pr, sec, hab, h1, h2, hpr, hsec, hint⟩ := GlobalTheory.T.exists_padicCoordinates_of_degreeOne_splitPlace D T w e hw he hN hsq
    refine ⟨⟨v, e, he, hab, φ.toRingHom.comp pr, sec.comp φ.symm.toRingHom.toAddMonoidHom, ?_, ?_, ?_, ?_, ?_⟩, rfl⟩
    · intro a; simp [h1]
    · intro x; simp [h2]
    · exact hφ.comp hpr
    · exact hsec.comp hφs
    · intro a
      have := hφO (φ.symm a)
      simp only [RingEquiv.apply_symm_apply] at this
      simp [this, hint]
  · intro k _ _ _ _ p
    refine ⟨?_, ?_⟩
    · intro S n _ _ b b' h1 h2
      obtain ⟨gl, hs, hm⟩ := GlobalTheory.T.exists_GL_embedding_unitaryAdelic_splitPlace_basis D k p S n b b' h1 h2
      exact ⟨⟨b, b', h1, h2, gl, hs, hm⟩, rfl⟩
    · intro ψ hψ
      obtain ⟨χ, hχ, hc⟩ := exists_char D k p ψ hψ
      obtain ⟨a, ha⟩ := GlobalTheory.T.exists_adelicTraceCharacter_splitSection_ne_one D k p ψ hψ
      refine ⟨χ, hχ, hc, ?_, fun hu => GlobalTheory.T.splitPlaceCharacter_conductor_integers D k p ψ χ hψ hχ hu⟩
      intro h1
      apply ha
      rw [← hχ a, h1]
      simp

end GlobalTheory.InhPt

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.thetaFun_eq_zero_of_orth_heisenbergTranslates : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (v : VolM D T.rank S.rank) (f g : WO S T → ℂ), IsThetaFunO ψ S T f → IsThetaFunO ψ S T g → g ≠ 0 → (∀ u : WO S T, thPair v.μ v.𝓕 f (heisO ψ S T u g) = 0) → f = 0 := by
  first | exact @GlobalTheory.ThetaIrred.eq_zero_of_orth_heis | exact GlobalTheory.ThetaIrred.eq_zero_of_orth_heis | (intros; apply GlobalTheory.ThetaIrred.eq_zero_of_orth_heis <;> assumption)
end

section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW

theorem _root_.GlobalTheory.T.definite_unitary_quotient_compact_fundamentalDomain : ∀ (D : D7) (A : HSp D), HSpace.SigOK A → HSpace.IsPosDef A → ∀ m : Measure (GA D A), m.IsHaarMeasure → GlobalTheory.Unf.CoCpt A ∧ ∃ (X K : Set (GA D A)), MeasurableSet X ∧ IsFundamentalDomain (GQ A) X m ∧ IsCompact K ∧ X ⊆ K := by
  first | exact @GlobalTheory.DefFund.coCpt_and_fundamentalDomain_subset_compact | exact GlobalTheory.DefFund.coCpt_and_fundamentalDomain_subset_compact | (intros; apply GlobalTheory.DefFund.coCpt_and_fundamentalDomain_subset_compact <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Mi

theorem typePlaces_noConj : ∀ (D : D7) (Pg : Finset (Pl D.host.E)), GlobalTheory.Core.Mi.IsTypePlaces Pg →
    ∀ PP ∈ Pg, ∀ PP' ∈ Pg, ¬ IsConjPl (D := D) PP PP' := by
  intro D Pg hT PP hP PP' hP' hc
  have hstar : ∀ z : D.host.E, star z = D.host.conj z := Formalism.BasicNotions.bridge_star_holds D.R D.host
  have hFfix : ∀ r : 𝓞 D.host.F,
      D.host.conj ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) r : 𝓞 D.host.E) : D.host.E) =
        ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) r : 𝓞 D.host.E) : D.host.E) :=
    fun r => (D.host.conjE_mem_hostF_iff _).1 (r : D.host.F).2

  have hle : PP.asIdeal.under (𝓞 D.host.F) ≤ PP'.asIdeal.under (𝓞 D.host.F) := by
    intro r hr
    rw [Ideal.under_def, Ideal.mem_comap] at hr ⊢
    obtain ⟨c', hc', he⟩ := hc _ hr
    have : c' = algebraMap (𝓞 D.host.F) (𝓞 D.host.E) r := by
      apply RingOfIntegers.ext
      rw [he, hstar, hFfix]
    rwa [← this]
  have hmax : (PP.asIdeal.under (𝓞 D.host.F)).IsMaximal := by
    rw [← HeightOneSpectrum.under_asIdeal]
    exact (HeightOneSpectrum.under (𝓞 D.host.F) PP).isMaximal
  have hne : PP'.asIdeal.under (𝓞 D.host.F) ≠ ⊤ := by
    rw [← HeightOneSpectrum.under_asIdeal]
    exact (HeightOneSpectrum.under (𝓞 D.host.F) PP').isPrime.ne_top
  have hund : HeightOneSpectrum.under (𝓞 D.host.F) PP' = HeightOneSpectrum.under (𝓞 D.host.F) PP := by
    apply HeightOneSpectrum.ext
    rw [HeightOneSpectrum.under_asIdeal, HeightOneSpectrum.under_asIdeal]
    exact (hmax.eq_of_le hne hle).symm
  have hgP := hT.1 PP hP
  have hgv : ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.F) ∈ (HeightOneSpectrum.under (𝓞 D.host.F) PP).asIdeal := by
    rw [HeightOneSpectrum.under_asIdeal, Ideal.under_def, Ideal.mem_comap, map_natCast]
    exact hgP
  obtain ⟨W, _, hW⟩ := hT.2 _ hgv
  have e1 : PP = W := hW PP ⟨hP, rfl⟩
  have e2 : PP' = W := hW PP' ⟨hP', hund⟩
  have e : PP' = PP := e2.trans e1.symm
  subst e

  obtain ⟨k, hk⟩ : ∃ k : Fin 2, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP'.asIdeal := by
    rw [Nat.cast_mul] at hgP
    rcases PP'.isPrime.mem_or_mem hgP with h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
  obtain ⟨x, hx, hxn⟩ :=
    (GlobalTheory.Mem.Chr.splitsC_main D.R D.host (D.host.g k) (D.host.g_prime k) (D.nd.g_split k) PP' hk).2.2.1
  obtain ⟨c', hc', he⟩ := hc x hx
  exact hxn c' (he.trans (hstar _)) hc'

end GlobalTheory.Core.Mi
end

section

noncomputable section

open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RegSch.GelfCyc

open GlobalTheory.SmoothForms (gelfA gelfA_eq_sum_pow)

section Alg

variable {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ}

theorem gelfA_conj (G : Fin n → Fin n → A) (P Q : Matrix (Fin n) (Fin n) ℂ) (hQP : Q * P = 1) (k : ℕ) :
    gelfA (fun a b => ∑ c, ∑ d, (P a c * Q d b) • G c d) k = gelfA G k := by
  have hPQ : P * Q = 1 := mul_eq_one_comm.1 hQP
  let φ : Matrix (Fin n) (Fin n) ℂ →+* Matrix (Fin n) (Fin n) A := (algebraMap ℂ A).mapMatrix
  have hc : ∀ (M : Matrix (Fin n) (Fin n) A) a b, (φ P * M * φ Q) a b = ∑ c, ∑ d, (P a c * Q d b) • M c d := by
    intro M a b
    simp only [Matrix.mul_apply, φ, RingHom.mapMatrix_apply, Matrix.map_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    rw [← Algebra.smul_def, ← Algebra.commutes, ← Algebra.smul_def, smul_smul, mul_comm]
  have h1 : (Matrix.of fun a b => ∑ c, ∑ d, (P a c * Q d b) • G c d) = φ P * Matrix.of G * φ Q := by
    ext a b
    rw [hc]
    rfl
  have h2 : ∀ m : ℕ, (φ P * Matrix.of G * φ Q) ^ m = φ P * Matrix.of G ^ m * φ Q := by
    intro m
    induction m with
    | zero => rw [pow_zero, pow_zero, mul_one, ← map_mul, hPQ, map_one]
    | succ m ih =>
      have : φ Q * φ P = 1 := by rw [← map_mul, hQP, map_one]
      rw [pow_succ, pow_succ, ih]
      simp only [mul_assoc]
      rw [← mul_assoc (φ Q), this, one_mul]
  rw [gelfA_eq_sum_pow, gelfA_eq_sum_pow, h1, h2]
  simp only [hc]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_comm]
  have : ∀ d, ∑ a, (P a c * Q d a) • (Matrix.of G ^ (k + 1)) c d = (Q * P) d c • (Matrix.of G ^ (k + 1)) c d := by
    intro d
    rw [← Finset.sum_smul, Matrix.mul_apply]
    simp only [mul_comm]
  simp [this, hQP, Matrix.one_apply]

theorem gelfA_swap (E : Fin n → Fin n → A) (k : ℕ) :
    gelfA (fun a b => E b a) k = ∑ idx : Fin (k + 1) → Fin n,
      (List.ofFn fun a : Fin (k + 1) => E (idx a) (idx (a + 1))).reverse.prod := by
  rw [gelfA]
  refine (Fintype.sum_equiv ((Equiv.neg (Fin (k + 1))).arrowCongr (Equiv.refl _)) _ _ fun idx => ?_).symm
  congr 1
  have h : ∀ a : Fin (k + 1), a.rev + 1 = -a := fun a => by
    have : a.rev + a = Fin.last k := Fin.ext (by
      have := a.2
      rw [Fin.val_add, Fin.val_rev, Fin.val_last, Nat.mod_eq_of_lt] <;> omega)
    rw [eq_neg_iff_add_eq_zero, add_right_comm, this, Fin.last_add_one]
  have h' : ∀ a : Fin (k + 1), a.rev = -(a + 1) := fun a => by
    rw [neg_add, ← h, add_neg_cancel_right]
  have e : ∀ g : Fin (k + 1) → A, (List.ofFn g).reverse = List.ofFn fun a => g a.rev := fun g => by
    apply List.ext_getElem
    · simp
    · intro i h1 h2
      simp only [List.getElem_reverse, List.getElem_ofFn, List.length_ofFn]
      congr 1
      ext
      simp
  rw [e]
  congr 1
  funext a
  rw [h, h']
  rfl

theorem prod_ofFn_neg : ∀ (m : ℕ) (g : Fin m → A),
    (List.ofFn fun a => -g a).prod = (-1 : ℂ) ^ m • (List.ofFn g).prod
  | 0, _ => by simp
  | m + 1, g => by
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, prod_ofFn_neg m fun a => g a.succ, pow_succ]
    simp

theorem sum_words (φ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] A) (M : Matrix (Fin n) (Fin n) ℂ) (hM : IsUnit M.det) (k : ℕ) :
    ∑ idx : Fin (k + 1) → Fin n,
      (List.ofFn fun a : Fin (k + 1) => φ (-(M * (Matrix.single (idx a) (idx (a + 1)) 1)ᵀ * M⁻¹))).prod =
    (-1 : ℂ) ^ (k + 1) • ∑ idx : Fin (k + 1) → Fin n,
      (List.ofFn fun a : Fin (k + 1) => φ (Matrix.single (idx a) (idx (a + 1)) 1)).reverse.prod := by
  have e : ∀ a b, φ (M * (Matrix.single a b 1)ᵀ * M⁻¹) = ∑ c, ∑ d, (M⁻¹ a c * M d b) • φ (Matrix.single d c 1) := by
    intro a b

    simp only [← map_smul, ← map_sum]
    congr 1
    rw [Matrix.matrix_eq_sum_single (M * _ * _), Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
    congr 1
    simp [Matrix.mul_apply, Matrix.single, ite_and, mul_comm]
  rw [← gelfA_swap (fun a b => φ (Matrix.single a b 1)),
    ← gelfA_conj _ M⁻¹ M (Matrix.mul_nonsing_inv M hM), gelfA, Finset.smul_sum]
  refine Finset.sum_congr rfl fun idx _ => ?_
  simp only [map_neg, e]
  exact prod_ofFn_neg _ _

end Alg

open GlobalTheory.Mem.RealTranslate (derEnd)

theorem wordDer_eq {D : D7} {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D} (τ : D.what₂.Tau)
    (w : List (Matrix (Fin V.rank) (Fin V.rank) ℂ)) (f : SmFun θ V) :
    wordDer θ V τ w f.1 = ((w.map (derEnd hθ τ)).prod f).1 := by
  induction w with
  | nil => rfl
  | cons Z w ih =>
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply]
    show RderC θ V τ Z (wordDer θ V τ w f.1) = _
    rw [ih]
    rfl

end GlobalTheory.RegSch.GelfCyc

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB

theorem _root_.GlobalTheory.T.mem_besGrp_iff_mt_mul_x0_eq_x0_mul : ∀ (D : D7) (σ : ℕ) (B : BesLev D σ), (∀ g : GA D B.V, g ∈ besGrp B.d B.o ↔ ∃ u ∈ UX D (σ + 1), mt B.V g ⬝ x0 B = x0 B ⬝ u.1) ∧ (∀ a a' : Mx D (σ + 1) (σ + 1), x0 B ⬝ a = x0 B ⬝ a' → a = a') ∧ ∀ g ∈ GQ B.V, ∀ u : UX D (σ + 1), mt B.V g ⬝ x0 B = x0 B ⬝ u.1.1 → u ∈ UXQ D (σ + 1) := by
  first | exact @GlobalTheory.Unf.FB.besselGroup_action_fourierBesselBasePoint | exact GlobalTheory.Unf.FB.besselGroup_action_fourierBesselBasePoint | (intros; apply GlobalTheory.Unf.FB.besselGroup_action_fourierBesselBasePoint <;> assumption)
end
