module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FramePositiveSum
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle010
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle052
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle290
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle097
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle142
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle212
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalVolumeLift
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalZero
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle180
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaSourceAction
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfLintegralEqZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle313
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfPderivStable
public import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle178
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle004
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsBicharPairing
import ReciprocityTheory.Automorphisms.PlaceA
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.VolumeFlatSection
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsLevMeas
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle385
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms
open NumberField IsDedekindDomain Matrix MeasureTheory ValuativeRel GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.AdForm GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw.LevelData

open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge GlobalTheory.LocMod
open _root_.Formalism.L2.Col (IntAt redP qOf)

section Gen

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable {u : D.what₂.Word}

end Gen

section Chain

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem val_lt_one_iff {E : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)} {ι : E →+* k}
    (hi : ∀ x, ι x ∈ 𝒪[k] ↔ IntAt P x) (a : E) : valuation k (ι a) < 1 ↔ P.valuation E a < 1 := by
  by_cases ha : a = 0
  · simp [ha]
  have h := hi a⁻¹
  rw [GlobalTheory.AtTypeExists.intAt_iff, Valuation.mem_integer_iff, map_inv₀, map_inv₀, map_inv₀,
    inv_le_one₀ (zero_lt_iff.2 (by simpa using ha)), inv_le_one₀ (zero_lt_iff.2 (by simpa using ha))] at h
  rw [← not_le, ← not_le, h]

theorem exists_unif {E : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)} {ι : E →+* k}
    (hi : ∀ x, ι x ∈ 𝒪[k] ↔ IntAt P x) (hd : DenseRange ι) (h : ((qOf P : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) :
    ∃ ϖ : kˣ, (ϖ : k) = ι (qOf P : E) ∧ GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ := by
  have hq := GlobalTheory.AtTypeExists.valuation_norm P h
  have h0 : ((qOf P : ℕ) : E) ≠ 0 := fun e => by
    rw [e, map_zero] at hq
    exact WithZero.exp_ne_zero hq.symm
  have h1 : valuation k (ι (qOf P : E)) < 1 := by
    rw [val_lt_one_iff hi, hq, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    omega
  refine ⟨Units.mk0 _ ((map_ne_zero ι).2 h0), rfl, fun x => ⟨fun hx => ?_, fun hx => lt_of_le_of_lt hx h1⟩⟩
  by_cases hx0 : x = 0
  · simp [hx0]
  have h2 : {y : k | valuation k (y - x) < valuation k x} ∈ nhds x := by
    rw [IsValuativeTopology.mem_nhds_iff']
    exact ⟨Units.mk0 (valuation k x) (by simpa using hx0), by simp⟩
  obtain ⟨a, ha⟩ := hd.mem_nhds h2
  have h3 : valuation k (ι a) = valuation k x := by simpa using Valuation.map_add_eq_of_lt_right (valuation k) ha
  have h4 : P.valuation E a < 1 := (val_lt_one_iff hi a).1 (h3 ▸ hx)
  have h5 : IntAt P (a / (qOf P : E)) := by
    rw [GlobalTheory.AtTypeExists.intAt_iff, map_div₀, hq, div_le_one₀ WithZero.exp_pos]
    by_cases ha0 : P.valuation E a = 0
    · simp [ha0]
    · rw [← WithZero.exp_log ha0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at h4
      rw [← WithZero.exp_log ha0, WithZero.exp_le_exp]
      omega
  have h6 := (hi _).2 h5
  rw [Valuation.mem_integer_iff, map_div₀, map_div₀, div_le_one₀ (zero_lt_iff.2 ((map_ne_zero _).2 ((map_ne_zero ι).2 h0))), h3] at h6
  exact h6

theorem mul_sec (q : GlobalTheory.FinPl.SplitPt D k) (x : AE D) (y : k) : x * q.sec y = q.sec (q.pr x * y) := by
  have h := q.sec_pr (x * q.sec y)
  have h' := q.sec_pr (q.sec y)
  rw [map_mul, q.pr_sec] at h
  rw [q.pr_sec] at h'
  rw [h, mul_left_comm, ← h']

end Chain

section Place

end Place

section World

variable {B : Base} {X : PreX B.toPre}

theorem type_prime {P : HeightOneSpectrum (𝓞 B.fields.E)} (hP : P ∈ (B.primes X).vGs) :
    ∃ i, qOf P = B.host.g i ∧ (B.host.g i).Prime ∧ ((B.host.g i : ℕ) : 𝓞 B.fields.E) ∈ P.asIdeal ∧
      ((B.host.g i : ℕ) : 𝓞 B.fields.E) ∉ P.asIdeal ^ 2 ∧ B.host.g i ∉ B.host.small ∧ B.host.g i ≠ B.host.q ∧ B.host.g i ≠ B.host.d ∧
      B.fields.conjO (X.piG i) ∈ P.asIdeal ∧ X.piG i ∉ P.asIdeal ∧ ∀ v, X.piT v - 1 ∈ P.asIdeal := by
  classical
  obtain ⟨hX, hPr, -⟩ := base_fields_primes_ok B X
  obtain ⟨i, hi⟩ : ∃ i, P ∈ (B.primes X).vG i := by
    unfold Formalism.L2.Col.Primes.vGs at hP
    rcases Finset.mem_union.1 hP with h | h
    exacts [⟨0, h⟩, ⟨1, h⟩]
  obtain ⟨h1, h2⟩ := GlobalTheory.TypePrimeUnif.typePrime_mem_and_notMem_sq hX hPr i P hi
  have hp : (B.host.g i).Prime := hPr.g_prime i
  have key : ¬ B.host.g i ∣ B.host.QS * B.host.q * B.host.d := fun h => by
    have h3 : B.host.g i ≡ 1 [MOD B.host.g i] := (hPr.g_cong i).of_dvd h
    exact hp.one_lt.ne' (Nat.dvd_one.1 ((Nat.modEq_zero_iff_dvd).1 (h3.symm.trans (Nat.modEq_zero_iff_dvd.2 dvd_rfl))))
  have hc : B.fields.conjO (X.piG i) ∈ P.asIdeal := by
    unfold Formalism.L2.Col.Primes.vG Formalism.L2.Col.divs at hi
    split_ifs at hi with h
    · exact h.mem_toFinset.1 hi
    · simp at hi
  refine ⟨i, hPr.vG_norm i P hi, hp, h1, h2, B.host.toHostRaw.notMem_small_of_not_dvd key,
    B.host.toHostRaw.ne_q_of_not_dvd key, B.host.toHostRaw.ne_d_of_not_dvd key, hc, fun h => ?_, fun v => ?_⟩
  · obtain ⟨x, y, e⟩ := hPr.piG_cop i
    exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (e ▸ add_mem (Ideal.mul_mem_left _ _ h) (Ideal.mul_mem_left _ _ hc)))
  · refine Ideal.mem_of_dvd _ (dvd_trans ?_ (hPr.piT_cong v)) h1
    refine Nat.cast_dvd_cast (Dvd.dvd.mul_left (Dvd.dvd.pow ?_ two_ne_zero) _)
    fin_cases i
    exacts [dvd_mul_right _ _, dvd_mul_left _ _]

end World

end GlobalTheory.SeeSaw.LevelData

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt

noncomputable section

namespace GlobalTheory.PlaceProjAt

theorem algebraMap_mem_iff {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)} (φ : SplitProj D v)
    (PP : Formalism.L2.DIV.Pl D.host.E) (h : IsProjAt φ PP) (a : 𝓞 D.host.F) :
    algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a ∈ PP.asIdeal ↔ a ∈ v.asIdeal := by
  have h1 : ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a : 𝓞 D.host.E) : D.host.E) =
      algebraMap D.host.F D.host.E (algebraMap (𝓞 D.host.F) D.host.F a) := by
    show algebraMap (𝓞 D.host.E) D.host.E _ = _
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  refine (h _).trans ?_
  rw [h1, GlobalTheory.PlaceRed.rdQ_alg, ReciprocityTheory.Aut.adic_valued_algebraMap, HeightOneSpectrum.valuation_lt_one_iff_mem]

theorem under_resCard : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v) (PP : Pl D.host.E), IsProjAt φ PP → v = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ∧ GlobalTheory.SplitWeil.resCard (Fv D.host.F v) = Ideal.absNorm PP.asIdeal := by
  intro D v φ PP h
  have hmem := algebraMap_mem_iff φ PP h
  have hv : v = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) := by
    refine HeightOneSpectrum.ext (Ideal.ext fun a => ?_)
    rw [← hmem]
    rfl
  refine ⟨hv, ?_⟩
  refine (GlobalTheory.LFun.SatBoundGL.resCard_completion v).trans ?_
  let f : 𝓞 D.host.F →+* 𝓞 D.host.E ⧸ PP.asIdeal :=
    (Ideal.Quotient.mk PP.asIdeal).comp (algebraMap (𝓞 D.host.F) (𝓞 D.host.E))
  have hker : RingHom.ker f = v.asIdeal := by
    ext a
    rw [RingHom.mem_ker, ← hmem]
    exact Ideal.Quotient.eq_zero_iff_mem
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨a, ha⟩ := ReciprocityTheory.Aut.adic_exists_approx v (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdQ φ (x : D.host.E)) (GlobalTheory.PlaceRed.rdQ_int φ x)
    refine ⟨a, ?_⟩
    show Ideal.Quotient.mk PP.asIdeal (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a) = Ideal.Quotient.mk PP.asIdeal x
    rw [Ideal.Quotient.eq, ← neg_mem_iff, neg_sub]
    refine (h _).2 ?_
    have h1 : ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a : 𝓞 D.host.E) : D.host.E) =
        algebraMap D.host.F D.host.E (algebraMap (𝓞 D.host.F) D.host.F a) := by
      show algebraMap (𝓞 D.host.E) D.host.E _ = _
      rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
    rw [show ((x - algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a : 𝓞 D.host.E) : D.host.E) =
        (x : D.host.E) - ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a : 𝓞 D.host.E) : D.host.E) from
        map_sub (algebraMap (𝓞 D.host.E) D.host.E) _ _, ← GlobalTheory.PlaceRed.rdQh_apply, map_sub, GlobalTheory.PlaceRed.rdQh_apply, GlobalTheory.PlaceRed.rdQh_apply, h1,
      GlobalTheory.PlaceRed.rdQ_alg]
    exact ha
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact Nat.card_congr ((Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hsurj)).toEquiv

end GlobalTheory.PlaceProjAt
end
end

section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP


theorem _root_.GlobalTheory.T.doubling_sphericalVacua_to_doubled_lattice_vacuum : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (LA : Lat A) (LB : Lat B), IsStdChar D ψ (-1) → IsSelfDualC A LA → IsSelfDualC (dblSp A) (sumLat finSumFinEquiv LA LA) ∧ ∀ (Sf : Finset (FinPl D)) (Φ₁ Φ₂ : WO A B → ℂ), IsSphOff ψ A B LA LB Sf Φ₁ → IsSphOff ψ A B LA LB Sf Φ₂ → ∀ v ∉ Sf, IsLatVac (heisO ψ (dblSp A) B) (latO (dblSp A) B (sumLat finSumFinEquiv LA LA : Lat (dblSp A)) LB fun u => u = v) (delta A B Φ₁ Φ₂) := by
  first | exact @GlobalTheory.Core.Rk.VacBox.doubling_isLatVac | exact GlobalTheory.Core.Rk.VacBox.doubling_isLatVac | (intros; apply GlobalTheory.Core.Rk.VacBox.doubling_isLatVac <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwoPlaceComm

open GlobalTheory.OrientedHeis (theta_add theta_smul theta_dRho)

section Generic

variable {ι X : Type} {A : ι → (X → ℂ) → (X → ℂ)} {P : (X → ℂ) → Prop}

theorem foldr_comm {B : (X → ℂ) → (X → ℂ)} (hA : ∀ i f, P f → P (A i f))
    (hBA : ∀ i f, P f → B (A i f) = A i (B f)) {f : X → ℂ} (hf : P f) (l : List ι) :
    B (l.foldr (fun i g => A i g) f) = l.foldr (fun i g => A i g) (B f) := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [List.foldr_cons]
    rw [hBA _ _ (GlobalTheory.FockIndep.foldr_mem hA hf l), ih]

theorem pure_comm {B : (X → ℂ) → (X → ℂ)} (hadd : ∀ f f', P f → P f' → P (f + f'))
    (hsm : ∀ (a : ℂ) f, P f → P (a • f)) (hA : ∀ i f, P f → P (A i f))
    (Badd : ∀ f f', P f → P f' → B (f + f') = B f + B f') (Bsm : ∀ (a : ℂ) f, P f → B (a • f) = a • B f)
    (hBA : ∀ i f, P f → B (A i f) = A i (B f)) {f : X → ℂ} (hf : P f) (Q : MvPolynomial ι ℂ) :
    B (pureTensorL A f Q) = pureTensorL A (B f) Q := by
  induction Q using MvPolynomial.induction_on' with
  | monomial k c =>
    rw [GlobalTheory.FockIndep.pure_monomial, GlobalTheory.FockIndep.pure_monomial]
    unfold opPow
    rw [Bsm _ _ (GlobalTheory.FockIndep.foldr_mem hA hf _), foldr_comm hA hBA hf]
  | add p q hp hq =>
    rw [map_add (f := _), map_add (f := _), Badd _ _ (GlobalTheory.FockIndep.pure_mem hadd hsm hA hf _) (GlobalTheory.FockIndep.pure_mem hadd hsm hA hf _),
      hp, hq]

theorem pure_fun_add (hA : ∀ i f, P f → P (A i f)) (hadd : ∀ f f', P f → P f' → P (f + f'))
    (hsm : ∀ (a : ℂ) f, P f → P (a • f))
    (Aadd : ∀ i f f', P f → P f' → A i (f + f') = A i f + A i f') {f f' : X → ℂ} (hf : P f) (hf' : P f')
    (Q : MvPolynomial ι ℂ) : pureTensorL A (f + f') Q = pureTensorL A f Q + pureTensorL A f' Q := by
  have hl : ∀ l : List ι, l.foldr (fun i g => A i g) (f + f') =
      l.foldr (fun i g => A i g) f + l.foldr (fun i g => A i g) f' := fun l => by
    induction l with
    | nil => rfl
    | cons i l ih =>
      simp only [List.foldr_cons]
      rw [ih, Aadd _ _ _ (GlobalTheory.FockIndep.foldr_mem hA hf l) (GlobalTheory.FockIndep.foldr_mem hA hf' l)]
  induction Q using MvPolynomial.induction_on' with
  | monomial k c =>
    rw [GlobalTheory.FockIndep.pure_monomial, GlobalTheory.FockIndep.pure_monomial, GlobalTheory.FockIndep.pure_monomial]
    unfold opPow
    rw [hl, smul_add]
  | add p q hp hq =>
    rw [map_add (f := _), map_add (f := _), map_add (f := _), hp, hq]
    abel

theorem pure_fun_smul (hA : ∀ i f, P f → P (A i f))
    (Asm : ∀ i (a : ℂ) f, P f → A i (a • f) = a • A i f) (a : ℂ) {f : X → ℂ} (hf : P f)
    (Q : MvPolynomial ι ℂ) : pureTensorL A (a • f) Q = a • pureTensorL A f Q := by
  have hl : ∀ l : List ι, l.foldr (fun i g => A i g) (a • f) = a • l.foldr (fun i g => A i g) f := fun l => by
    induction l with
    | nil => rfl
    | cons i l ih =>
      simp only [List.foldr_cons]
      rw [ih, Asm _ _ _ (GlobalTheory.FockIndep.foldr_mem hA hf l)]
  induction Q using MvPolynomial.induction_on' with
  | monomial k c =>
    rw [GlobalTheory.FockIndep.pure_monomial, GlobalTheory.FockIndep.pure_monomial]
    unfold opPow
    rw [hl, smul_comm]
  | add p q hp hq =>
    rw [map_add (f := _), map_add (f := _), hp, hq, smul_add]

end Generic

section Places

variable {D : D7} {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}
  (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) {τ τ' : D.what₂.Tau} (hne : τ ≠ τ')
include hψ hθ hne

theorem dRho_comm_ne (z z' : Matrix (Fin T.rank) (Fin S.rank) ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    Datum.dRho (heisO ψ S T) θ τ z (Datum.dRho (heisO ψ S T) θ τ' z' f) =
      Datum.dRho (heisO ψ S T) θ τ' z' (Datum.dRho (heisO ψ S T) θ τ z f) := by
  rw [GlobalTheory.FockIndep.dRho_comm hψ hθ τ z τ' z' hf]
  simp [GlobalTheory.FockIndep.omDir, hne]

theorem dRho_aPlus_ne (z : Matrix (Fin T.rank) (Fin S.rank) ℂ)
    (J : Matrix (Fin T.rank) (Fin S.rank) ℂ → Matrix (Fin T.rank) (Fin S.rank) ℂ) (u : Matrix (Fin T.rank) (Fin S.rank) ℂ)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    Datum.dRho (heisO ψ S T) θ τ z (aPlus (heisO ψ S T) θ τ' J u f) =
      aPlus (heisO ψ S T) θ τ' J u (Datum.dRho (heisO ψ S T) θ τ z f) := by
  have ht := fun ρ y => theta_dRho hθ hψ ρ y hf
  rw [GlobalTheory.FockIndep.aPlus_eq, GlobalTheory.FockIndep.aPlus_eq,
    GlobalTheory.FockIndep.dRho_smul hψ hθ _ _ _ (theta_add (ht _ _) (theta_smul _ (ht _ _))),
    GlobalTheory.FockIndep.dRho_add hψ hθ _ _ (ht _ _) (theta_smul _ (ht _ _)), GlobalTheory.FockIndep.dRho_smul hψ hθ _ _ _ (ht _ _),
    dRho_comm_ne hψ hθ hne _ _ hf, dRho_comm_ne hψ hθ hne _ _ hf]

theorem aPlus_comm_ne (J J' : Matrix (Fin T.rank) (Fin S.rank) ℂ → Matrix (Fin T.rank) (Fin S.rank) ℂ)
    (z u : Matrix (Fin T.rank) (Fin S.rank) ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    aPlus (heisO ψ S T) θ τ J z (aPlus (heisO ψ S T) θ τ' J' u f) =
      aPlus (heisO ψ S T) θ τ' J' u (aPlus (heisO ψ S T) θ τ J z f) := by
  have ht := fun ρ y => theta_dRho hθ hψ ρ y hf
  rw [GlobalTheory.FockIndep.aPlus_eq τ J z (aPlus (heisO ψ S T) θ τ' J' u f), dRho_aPlus_ne hψ hθ hne _ _ _ hf,
    dRho_aPlus_ne hψ hθ hne _ _ _ hf, ← GlobalTheory.FockIndep.aPlus_smul hψ hθ _ _ _ _ (ht _ _),
    ← GlobalTheory.FockIndep.aPlus_add hψ hθ _ _ _ (ht _ _) (theta_smul _ (ht _ _)),
    ← GlobalTheory.FockIndep.aPlus_smul hψ hθ _ _ _ _ (theta_add (ht _ _) (theta_smul _ (ht _ _))), ← GlobalTheory.FockIndep.aPlus_eq]

theorem annih_aPlus_ne (J J' : Matrix (Fin T.rank) (Fin S.rank) ℂ → Matrix (Fin T.rank) (Fin S.rank) ℂ)
    (z u : Matrix (Fin T.rank) (Fin S.rank) ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    annih (heisO ψ S T) θ τ J z (aPlus (heisO ψ S T) θ τ' J' u f) =
      aPlus (heisO ψ S T) θ τ' J' u (annih (heisO ψ S T) θ τ J z f) := by
  have ht := fun ρ y => theta_dRho hθ hψ ρ y hf
  rw [annih, annih, dRho_aPlus_ne hψ hθ hne _ _ _ hf, dRho_aPlus_ne hψ hθ hne _ _ _ hf,
    ← GlobalTheory.FockIndep.aPlus_smul hψ hθ _ _ _ _ (ht _ _),
    ← GlobalTheory.FockIndep.aPlus_add hψ hθ _ _ _ (ht _ _) (theta_smul _ (ht _ _))]

end Places

section Weil

variable {D : D7} {V W : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {χS χT : (AE D)ˣ →* Circle}
  {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} (hW : IsWeilDatumO ψ V W χS χT ω) (hθ : IsInfFam θ)
  {τ τ' : D.what₂.Tau} (hne : τ ≠ τ') {g : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ'))
include hW hθ hne hg

theorem om_dRho_fix (z : Matrix (Fin W.rank) (Fin V.rank) ℂ) {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f) :
    ω (atTau θ V τ' g, 1) (Datum.dRho (heisO ψ V W) θ τ z f) =
      Datum.dRho (heisO ψ V W) θ τ z (ω (atTau θ V τ' g, 1) f) := by
  rw [GlobalTheory.OrientedHeis.om_dRho hW hθ _ _ τ z hf]
  have h1 : compAt θ τ (Formalism.L2.Theta.mt W 1) = 1 := by
    unfold Formalism.L2.Theta.mt
    rw [map_one, Units.val_one]
    exact Matrix.map_one _ (((θ τ).comp (infPart D)).map_zero) (((θ τ).comp (infPart D)).map_one)
  have h2 : compAt θ τ (Formalism.L2.Theta.mt V (atTau θ V τ' g)) = 1 :=
    (GlobalTheory.PointAtPlaceHom.atTau_spec hθ V τ' hg).2.2 τ hne
  have h3 := GlobalTheory.OrientedHeis.compAt_mt_mul_inv (θ := θ) τ (atTau θ V τ' g)
  rw [h2, Matrix.one_mul] at h3
  rw [h1, h3, Matrix.one_mul, Matrix.mul_one]

theorem om_aPlus_fix (J : Matrix (Fin W.rank) (Fin V.rank) ℂ → Matrix (Fin W.rank) (Fin V.rank) ℂ)
    (u : Matrix (Fin W.rank) (Fin V.rank) ℂ) {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f) :
    ω (atTau θ V τ' g, 1) (aPlus (heisO ψ V W) θ τ J u f) = aPlus (heisO ψ V W) θ τ J u (ω (atTau θ V τ' g, 1) f) := by
  rw [GlobalTheory.FockIndep.aPlus_eq, GlobalTheory.FockIndep.aPlus_eq, map_smul, map_add (f := _), map_smul, om_dRho_fix hW hθ hne hg _ hf,
    om_dRho_fix hW hθ hne hg _ hf]

theorem om_annih_fix (J : Matrix (Fin W.rank) (Fin V.rank) ℂ → Matrix (Fin W.rank) (Fin V.rank) ℂ)
    (u : Matrix (Fin W.rank) (Fin V.rank) ℂ) {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f) :
    ω (atTau θ V τ' g, 1) (annih (heisO ψ V W) θ τ J u f) = annih (heisO ψ V W) θ τ J u (ω (atTau θ V τ' g, 1) f) := by
  rw [annih, annih, map_add (f := _), map_smul, om_dRho_fix hW hθ hne hg _ hf, om_dRho_fix hW hθ hne hg _ hf]

end Weil

theorem twoPlace_comm : ∀ (D : D7) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : (GA D V × GA D W →* Module.End ℂ (WO V W → ℂ))), IsInfFam θ → IsWeilDatumO ψ V W χS χT ω → ∀ (τ τ' : D.what₂.Tau), τ ≠ τ' → ∀ F, IsThetaFunO ψ V W F → let pt := fun ρ => GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ptAt ψ θ V W ρ (cart M ρ) (cart M' ρ) (onb M ρ) (onb M' ρ); let vac := IsFockVacAt (heisO ψ V W) θ τ (cplxO (cart M τ) (cart M' τ)); (∀ P, IsThetaFunO ψ V W (pt τ' F P)) ∧ (∀ P, vac F → vac (pt τ' F P)) ∧ (∀ P Q, pt τ (pt τ' F Q) P = pt τ' (pt τ F P) Q) ∧ ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ'), (vac F → vac (ω (atTau θ V τ' g, 1) F)) ∧ ∀ P, ω (atTau θ V τ' g, 1) (pt τ F P) = pt τ (ω (atTau θ V τ' g, 1) F) P := by
  intro D V W S S' M M' θ ψ χS χT ω hθ hW τ τ' hne F hF
  dsimp only
  have hψ := hW.std
  have hadd : ∀ f f', IsThetaFunO ψ V W f → IsThetaFunO ψ V W f' → IsThetaFunO ψ V W (f + f') :=
    fun _ _ => theta_add
  have hsm : ∀ (a : ℂ) f, IsThetaFunO ψ V W f → IsThetaFunO ψ V W (a • f) := fun a _ => theta_smul a
  have hA : ∀ ρ (k : Fin W.rank × Fin V.rank) g, IsThetaFunO ψ V W g → IsThetaFunO ψ V W
      (aPlus (heisO ψ V W) θ ρ (cplxO (cart M ρ) (cart M' ρ)) (unitMap (onb M ρ) (onb M' ρ) k.1 k.2) g) :=
    fun ρ _ _ h => GlobalTheory.FockIndep.aPlus_theta hψ hθ ρ _ _ h
  have Aadd : ∀ ρ (k : Fin W.rank × Fin V.rank) g g', IsThetaFunO ψ V W g → IsThetaFunO ψ V W g' →
      aPlus (heisO ψ V W) θ ρ (cplxO (cart M ρ) (cart M' ρ)) (unitMap (onb M ρ) (onb M' ρ) k.1 k.2) (g + g') =
      aPlus (heisO ψ V W) θ ρ (cplxO (cart M ρ) (cart M' ρ)) (unitMap (onb M ρ) (onb M' ρ) k.1 k.2) g +
      aPlus (heisO ψ V W) θ ρ (cplxO (cart M ρ) (cart M' ρ)) (unitMap (onb M ρ) (onb M' ρ) k.1 k.2) g' :=
    fun ρ _ _ _ h h' => GlobalTheory.FockIndep.aPlus_add hψ hθ ρ _ _ h h'
  have Asm : ∀ ρ (k : Fin W.rank × Fin V.rank) (a : ℂ) g, IsThetaFunO ψ V W g →
      aPlus (heisO ψ V W) θ ρ (cplxO (cart M ρ) (cart M' ρ)) (unitMap (onb M ρ) (onb M' ρ) k.1 k.2) (a • g) =
      a • aPlus (heisO ψ V W) θ ρ (cplxO (cart M ρ) (cart M' ρ)) (unitMap (onb M ρ) (onb M' ρ) k.1 k.2) g :=
    fun ρ _ a _ h => GlobalTheory.FockIndep.aPlus_smul hψ hθ ρ _ _ a h
  unfold GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ptAt
  refine ⟨fun P => GlobalTheory.FockIndep.pure_mem hadd hsm (hA τ') hF P, fun P hv z => ?_, fun P Q => ?_, fun g hg => ⟨?_, ?_⟩⟩
  · rw [pure_comm hadd hsm (hA τ') (fun _ _ h h' => GlobalTheory.FockIndep.annih_add hψ hθ τ _ z h h')
      (fun a _ h => GlobalTheory.FockIndep.annih_smul hψ hθ τ _ z a h)
      (fun k g hg => annih_aPlus_ne hψ hθ hne _ _ _ _ hg) hF P, hv z]
    have h0 := pure_fun_smul (hA τ') (Asm τ') 0 hF P
    rwa [zero_smul, zero_smul] at h0
  · symm
    refine pure_comm (B := fun g => pureTensorL (fun k : Fin W.rank × Fin V.rank =>
        aPlus (heisO ψ V W) θ τ' (cplxO (cart M τ') (cart M' τ')) (unitMap (onb M τ') (onb M' τ') k.1 k.2)) g Q)
      hadd hsm (hA τ) (fun _ _ h h' => pure_fun_add (hA τ') hadd hsm (Aadd τ') h h' Q)
      (fun a _ h => pure_fun_smul (hA τ') (Asm τ') a h Q) (fun k g hg => ?_) hF P
    exact (pure_comm hadd hsm (hA τ') (Aadd τ k) (Asm τ k)
      (fun j h hh => aPlus_comm_ne hψ hθ hne _ _ _ _ hh) hg Q).symm
  · intro hv z
    rw [← om_annih_fix hW hθ hne hg _ _ hF, hv z, map_zero]
  · intro P
    exact pure_comm hadd hsm (hA τ) (fun f f' _ _ => map_add _ f f') (fun a f _ => map_smul _ a f)
      (fun k h hh => om_aPlus_fix hW hθ hne hg _ _ hh) hF P

end GlobalTheory.TwoPlaceComm

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.integral_quotient_eq_setIntegral_fundamentalDomain : ∀ (D : D7) (V : HSp D) (ν : Measure (GA D V)) (X : Set (GA D V)), ν.IsHaarMeasure → IsFundamentalDomain (GQ V) X ν → ∀ F : GA D V → ℂ, (∀ γ ∈ GQ V, ∀ g, F (γ * g) = F g) → AEStronglyMeasurable F ν → ∫ q, GlobalTheory.AutomorphicL2Unitary.descend (GQ V) F q ∂(GlobalTheory.AutomorphicL2Unitary.autMeasure V ν) = ∫ g in X, F g ∂ν := by
  first | exact @GlobalTheory.ChainOnto.integral_autMeasure_eq_setIntegral | exact GlobalTheory.ChainOnto.integral_autMeasure_eq_setIntegral | (intros; apply GlobalTheory.ChainOnto.integral_autMeasure_eq_setIntegral <;> assumption)
end
