module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralActionUnitCharacterEigen
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1949
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1981
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstStandardPairMemberHasThetaFunction
import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle104
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1641
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1461
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1584
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1342
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1850
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1294
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WittTowerRestrictionIntertwinesWeilUpToCharacter
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle104
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle031
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppellHumbertFactorOfHermitian
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1178
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2254
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1652
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1179
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2128
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1645
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsRapoportOfBasis
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle311
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactSubgroupsActOnFockVectorsAllSignatures
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpDiv
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2253
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle017
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.IntegralLeaf.LeafINTFree

@[expose] public section

section

open NumberField IsDedekindDomain
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 lamOf Th La Iop Qbar lamC)
open Formalism.MainNotions.StandardLatticesGL3 (TT stdL pt oddE0 Wd La0 Crv inc OhE IntU)
open GlobalTheory.NormSum (Pair intG)
open GlobalTheory.FunObj.SqNum (hatId CongOne skewLat unitBlock cosetVec)
open GlobalTheory.NormExact (Reads Setup IsFinIdl HasFinPart finPt)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (InId IsUnitDet unitChar stdFst)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdRead

namespace GlobalTheory.StdRead.CongOneChar

open GlobalTheory.BotClassDict (finQ)
open GlobalTheory.StdRead.CharVal

variable {D : D7}

theorem hat_mono {I J : Ideal (𝓞 D.host.E)} (h : I ≤ J) {x : Formalism.MainNotions.StandardLatticesGL3.AE D} (hx : x ∈ hatId D I) :
    x ∈ hatId D J := by
  refine AddSubgroup.closure_mono ?_ hx
  rintro _ ⟨b, hb, t, ht, rfl⟩
  exact ⟨b, h hb, t, ht, rfl⟩

theorem hat_int {I : Ideal (𝓞 D.host.E)} {x : Formalism.MainNotions.StandardLatticesGL3.AE D} (hx : x ∈ hatId D I) : x ∈ OhE D := by
  induction hx using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨b, -, t, ht, rfl⟩ := hy
    exact mul_mem (inc_int b) ht
  | zero => exact zero_mem _
  | add a b _ _ ha hb => exact add_mem ha hb
  | neg a _ ha => exact neg_mem ha

theorem toE_surj (z : EAf D) : ∃ y, toE D y = z := by
  obtain ⟨w, -, hw⟩ := StandardFirstTheta.GlobalTheory.CompanionTheory.StdFstTheta.toEAf_surj z
  exact ⟨finQ D w, by rw [toE_finQ, hw]⟩

theorem toE_inj : Function.Injective (toE D) := fun _ _ h =>
  (GlobalTheory.BotFormula.toAfE D).injective ((Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).injective h)

theorem rho_one_add (Q : Formalism.L2.DIV.Pl D.host.E) {a b : Formalism.MainNotions.StandardLatticesGL3.AE D} (ha : a ∈ OhE D) (hb : b ∈ OhE D)
    (hu : 1 + a * b ∈ OhE D) (h0 : rho Q ⟨a, ha⟩ * rho Q ⟨b, hb⟩ = 0) : rho Q ⟨_, hu⟩ = 1 := by
  have e : (⟨_, hu⟩ : OhE D) = 1 + ⟨a, ha⟩ * ⟨b, hb⟩ := Subtype.ext rfl
  rw [e, RingHom.map_add (f := _), RingHom.map_mul, h0, RingHom.map_one, add_zero]

theorem exists_inv {u : Formalism.MainNotions.StandardLatticesGL3.AE D} (hu : u ∈ OhE D) (h : ∀ Q : Formalism.L2.DIV.Pl D.host.E, rho Q ⟨u, hu⟩ ≠ 0) :
    ∃ v ∈ OhE D, u * v = 1 := by
  have hU : IsUnit (⟨toE D u, (toE_int_iff u).2 hu⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) :=
    Formalism.L2.DIV.isUnit_of_resS_ne_zero D.sp.cm _ fun Q => h Q
  obtain ⟨w, hw⟩ := hU.exists_right_inv
  obtain ⟨v, hv⟩ := toE_surj (w : EAf D)
  refine ⟨v, (toE_int_iff v).1 (hv ▸ w.2), toE_inj ?_⟩
  rw [RingHom.map_mul, RingHom.map_one, hv]
  exact congrArg Subtype.val hw



theorem unitChar_cong : ∀ {D : D7} (e : AE D) (𝔪 : Ideal (𝓞 D.host.E)), GoodMod e 𝔪 → ∀ ν : (AE D)ˣ →* Circle, KillsCong ν 𝔪 →
  ∀ {k : ℕ} (P : Matrix (Fin k) (Fin k) (Formalism.MainNotions.StandardLatticesGL3.AE D)), (∀ i j, (P - 1) i j ∈ hatId D 𝔪) →
  unitChar ν e (P.map (toE D)) = 1 := by
  intro D e 𝔪 hG ν hK k P hP
  have hm1 := one_sub_eps_mod hG
  obtain ⟨S, c, he, hc, h𝔪, -⟩ := hG
  have hO := eps_int he
  have h2 := eps_conj he
  have hte := toE_finQ e
  have hPO : ∀ i j, P i j ∈ OhE D := fun i j => by
    have h1 : (1 : Matrix (Fin k) (Fin k) (Formalism.MainNotions.StandardLatticesGL3.AE D)) i j ∈ OhE D := by
      rw [Matrix.one_apply]; split_ifs
      · exact one_mem _
      · exact zero_mem _
    have h3 := add_mem (hat_int (hP i j)) h1
    rwa [Matrix.sub_apply, sub_add_cancel] at h3
  have hm := GlobalTheory.FunObj.StdDatum.DetCong.det_sub_one_mem_hatId_of P hPO hP
  have hdet : (P.map (toE D)).det = toE D P.det := (RingHom.map_det (toE D) _).symm
  have hmO := hat_int hm
  have huO : 1 + finQ D e * (P.det - 1) ∈ OhE D := add_mem (one_mem _) (mul_mem hO hmO)
  obtain ⟨v, hvO, huv⟩ := exists_inv huO fun Q => by
    have := Q.isPrime
    have h0 : rho Q ⟨_, hO⟩ * rho Q ⟨_, hmO⟩ = 0 := by
      by_cases hQ : Q ∈ S
      · have hle : 𝔪 ≤ Q.asIdeal := by
          rw [h𝔪]
          exact (Ideal.le_of_dvd (Finset.dvd_prod_of_mem (fun w : Formalism.L2.DIV.Pl D.host.E => w.asIdeal ^ c w) hQ)).trans
            (Ideal.pow_le_self (hc Q hQ).ne')
        obtain ⟨_, h5⟩ := rho_hat Q (hat_mono hle hm)
        rw [h5, mul_zero]
      · have h5 : rho Q ⟨_, hO⟩ = Formalism.L2.DIV.resS D.host.F Q ⟨_, StandardFirstTheta.GlobalTheory.CompanionTheory.StdFstTheta.toEAf_mem he⟩ :=
          congrArg (Formalism.L2.DIV.resS D.host.F Q) (Subtype.ext hte)
        rw [h5, StandardFirstTheta.GlobalTheory.CompanionTheory.StdFstTheta.res_off he _ hQ, zero_mul]
    have h6 : rho Q ⟨_, huO⟩ = 1 := rho_one_add Q hO hmO huO h0
    rw [h6]
    exact one_ne_zero
  have hm' := hat_mul hm (GlobalTheory.FunObj.StdDatum.DetCong.sgA_mem_hatId hm1)
  rw [map_sub, map_one] at hm'
  have hm'' := GlobalTheory.FunObj.StdDatum.mul_mem_hatId hO hm'
  generalize finQ D e = ε at hO h2 hte huO huv hm''
  generalize P.det = d at hdet huO huv hm''
  let y : (Formalism.MainNotions.StandardLatticesGL3.AE D)ˣ := ⟨_, _, huv, by rw [mul_comm, huv]⟩
  have hyv : (y : Formalism.MainNotions.StandardLatticesGL3.AE D) = 1 + ε * (d - 1) := rfl
  have hyi : ((y⁻¹ : (Formalism.MainNotions.StandardLatticesGL3.AE D)ˣ) : Formalism.MainNotions.StandardLatticesGL3.AE D) = v := rfl
  obtain ⟨x, hx, hx1, hx2⟩ := exists_finIdl y
  have hU : IsUnitDet e (P.map (toE D)) x := by
    refine ⟨hx.1, ?_, ?_⟩
    · rw [hx1, show (y : Formalism.MainNotions.StandardLatticesGL3.AE D) = (1 - ε) + ε * d by rw [hyv]; ring, hdet, RingHom.map_add (f := _), RingHom.map_sub,
        RingHom.map_mul, RingHom.map_one, hte]
    · rw [hx2, toE_int_iff, hyi]
      exact hvO
  have hν : ν x = 1 := hK x y hx ⟨huO, hvO⟩ (by
    convert hm'' using 1
    rw [hyv]
    linear_combination (d - 1) * h2)
  rw [unitChar_eq ν e _ hU, hν, inv_one, Circle.coe_one]

end GlobalTheory.StdRead.CongOneChar
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.WeilUnitaryTransport

theorem pair_of_ug : ∀ (D : D7) (S T : HSp D) (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E)
    (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E) (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
    ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
    ∀ (a : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA))
      (b : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB)),
      ∃ (g : GA D S) (h : GA D T), mt T h = a.1.1 ∧ mt S g = (b⁻¹).1.1ᵀ :=
  GlobalTheory.T.unitaryPair_partner_inverse_transpose

theorem theta_quasi : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
      (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
      ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
      ∀ (κ : Type) [Fintype κ]
        (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
        (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
          co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
        ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F κ, ∀ (γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (w : Formalism.IndefR.Datum.WO S T),
          GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ Φ (ratW T S γ + w) = ψ (-(Formalism.IndefR.Datum.symplOH S T (ratW T S γ) w)) * GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ Φ w :=
  GlobalTheory.T.thetaTransform_rational_translate_quasiInvariant

theorem theta_level : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
      (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
      ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
      ∀ (κ : Type) [Fintype κ]
        (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
        (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
          co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
        ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F κ, ∃ U : AddSubgroup (Formalism.IndefR.Datum.WO S T), IsOpen (U : Set (Formalism.IndefR.Datum.WO S T)) ∧
          ∀ u ∈ U, u.map (infPart D) = 0 → Formalism.IndefR.Datum.heisO ψ S T u (GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ Φ) = GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ Φ :=
  GlobalTheory.T.thetaTransform_fixed_by_small_finiteHeisenberg

theorem theta_cont : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
      (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
      ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
      ∀ (κ : Type) [Fintype κ]
        (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
        (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
          co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
        ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F κ, Continuous (GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ Φ) :=
  GlobalTheory.T.continuous_thetaTransform_adelicSchwartz

theorem theta_smooth : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
      (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
      ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
      ∀ (κ : Type) [Fintype κ]
        (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
        (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
          co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
        ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F κ, ∀ (k : ℕ) (L : (Fin k → ℝ) →+ Formalism.IndefR.Datum.WO S T), Continuous L →
          (∀ t, (L t).map (finPart D) = 0) → ∀ w, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t => GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ Φ (w + L t) :=
  GlobalTheory.T.contDiff_thetaTransform_adelicSchwartz_realDirections

theorem isThetaFunO_thetaTr : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
      (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
      ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
      ∀ (κ : Type) [Fintype κ]
        (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
        (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
          co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
        ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F κ, Formalism.IndefR.Datum.IsThetaFunO ψ S T (GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ Φ) := by
  intro D ψ hψ S T JA JB ξ hA hB κ _ co hrat Φ hΦ
  exact ⟨theta_quasi D ψ hψ S T JA JB ξ hA hB κ co hrat Φ hΦ, theta_level D ψ hψ S T JA JB ξ hA hB κ co hrat Φ hΦ,
    theta_cont D ψ hψ S T JA JB ξ hA hB κ co hrat Φ hΦ, theta_smooth D ψ hψ S T JA JB ξ hA hB κ co hrat Φ hΦ⟩

theorem theta_isometry_coord : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ →
    ∀ (κ : Type) [Fintype κ] (μ : @Measure (κ → AF F) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ (ν : @Measure ((κ → AF F) × (κ → AF F)) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) ν →
    ∀ 𝓕 : Set ((κ → AF F) × (κ → AF F)),
      @IsAddFundamentalDomain (GlobalTheory.WeilUnitaryTransport.ratPair F κ) _ _ _ (borel _) 𝓕 ν →
      ∃ c : ENNReal, ∀ Φ ∈ GlobalTheory.WeilM.schA F κ,
        ∫⁻ x, ‖Φ x‖ₑ ^ 2 ∂μ = c * ∫⁻ w in 𝓕, ‖GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ w Φ)‖ₑ ^ 2 ∂ν :=
  GlobalTheory.T.exists_lintegral_sq_eq_mul_setLIntegral_thetaTransform

theorem theta_transfer : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
      (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
      ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
      ∀ (κ : Type) [Fintype κ]
        (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
        (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
          co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
        ∀ (ν : Measure (Formalism.IndefR.Datum.WO S T)) (𝓕 : Set (Formalism.IndefR.Datum.WO S T)), ν.IsAddHaarMeasure →
          IsAddFundamentalDomain (ratL T S) 𝓕 ν →
          ∃ (ν' : @Measure ((κ → AF D.host.F) × (κ → AF D.host.F)) (borel _)) (𝓕' : Set ((κ → AF D.host.F) × (κ → AF D.host.F))),
            @Measure.IsAddHaarMeasure _ _ _ (borel _) ν' ∧
            @IsAddFundamentalDomain (GlobalTheory.WeilUnitaryTransport.ratPair D.host.F κ) _ _ _ (borel _) 𝓕' ν' ∧
            ∀ f : (κ → AF D.host.F) × (κ → AF D.host.F) → ℂ,
              ∫⁻ w in 𝓕, ‖f (co.e w)‖ₑ ^ 2 ∂ν = ∫⁻ w in 𝓕', ‖f w‖ₑ ^ 2 ∂ν' :=
  GlobalTheory.T.rationalDarboux_transfers_haar_fundamentalDomain

theorem theta_isometry : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
      (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
      ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
      ∀ (κ : Type) [Fintype κ]
        (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
        (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
          co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
        ∀ (μ : @Measure (κ → AF D.host.F) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
        ∀ (ν : Measure (Formalism.IndefR.Datum.WO S T)) (𝓕 : Set (Formalism.IndefR.Datum.WO S T)), ν.IsAddHaarMeasure →
          IsAddFundamentalDomain (ratL T S) 𝓕 ν → ∃ c : ENNReal, ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F κ,
            ∫⁻ x, ‖Φ x‖ₑ ^ 2 ∂μ = c * ∫⁻ w in 𝓕, ‖GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ Φ w‖ₑ ^ 2 ∂ν := by
  intro D ψ hψ S T JA JB ξ hA hB κ _ co hrat μ hμ ν 𝓕 hν h𝓕
  obtain ⟨ν', 𝓕', hν', h𝓕', heq⟩ := theta_transfer D ψ hψ S T JA JB ξ hA hB κ co hrat ν 𝓕 hν h𝓕
  obtain ⟨c, hc⟩ := theta_isometry_coord D.host.F ψ hψ.1 κ μ hμ ν' hν' 𝓕' h𝓕'
  refine ⟨c, fun Φ hΦ => ?_⟩
  rw [hc Φ hΦ, ← heq]
  rfl

theorem isUnitaryOn_transport : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
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
                       GlobalTheory.WeilSchrodinger.IsTransport ψ co ω om → GlobalTheory.WeilM.IsUnitaryOn (GlobalTheory.WeilM.adeleClass D.host.F) om := by
  intro D ψ hψ S T χS χT hS hT rS rT JA JB ξ hA hB κ _ co hrat ω hω om hom
  rintro μ hμ ⟨a, b⟩ Φ hΦ
  obtain ⟨g, h, hh, hg⟩ := pair_of_ug D S T JA JB ξ hA hB a b
  obtain ⟨ν, 𝓕, hν, h𝓕⟩ := GlobalTheory.TowerRestrictScalar.exists_fd S T
  obtain ⟨c, hc⟩ := theta_isometry D ψ hψ S T JA JB ξ hA hB κ co hrat μ hμ ν 𝓕 hν h𝓕
  have ht := hom a b g h hh hg Φ hΦ
  rw [hc _ ht.1, hc _ hΦ, ht.2, hω.om_unit ν 𝓕 hν h𝓕 _ _ (isThetaFunO_thetaTr D ψ hψ S T JA JB ξ hA hB κ co hrat Φ hΦ)]

end GlobalTheory.WeilUnitaryTransport

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BiKill

open GlobalTheory.CechPic

theorem lam_lam_diag {S : Scheme.{0}} {A T : Over S} [GrpObj A] [IsCommMonObj A] {M : LB A.left} (hM : M.IsLB)
    (hΘ : ∃ t : LB.Gen (Theta A M), t.IsGen) (a b : T ⟶ A) :
    lam (lam (cls M hM) (𝟙 A) (𝟙 A)) a b = 2 • lam (cls M hM) a b := by
  have e : ∀ h : T ⟶ A, pull h.left (lam (cls M hM) (𝟙 A) (𝟙 A)) = lam (cls M hM) h h := fun h =>
    by rw [pull_lam, Category.comp_id]
  have hr : ∀ x y z : T ⟶ A, lam (cls M hM) x (y * z) = lam (cls M hM) x y + lam (cls M hM) x z := by
    intro x y z
    rw [lam_comm, lam_mul_left hM hΘ, lam_comm _ y, lam_comm _ z]
  change pull (a * b).left _ - pull a.left _ - pull b.left _ + pull (1 : T ⟶ A).left _ = _
  rw [e, e, e, e, lam_mul_left hM hΘ, hr, hr, lam_one_left, lam_comm _ b a, two_smul]
  abel

theorem kernel_pow_eq_one : ∀ (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ P : LB (G2 A).left, P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) → ∀ n : ℕ, (∀ x : 𝟙_ (Over (Sp ℂ)) ⟶ A, (∃ t : (P.pull (lift (snd A (𝟙_ (Over (Sp ℂ))) ≫ x) (fst A (𝟙_ (Over (Sp ℂ))))).left).Gen, t.IsGen) → x ^ n = 1) → ∀ (T : Over (Sp ℂ)) (x : T ⟶ A), (∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) → x ^ n = 1 := by
  intro A _ _ g hA hg P hP h1 h2 hsw hamp n hn T x hx
  obtain ⟨M, hM, hPM⟩ := GlobalTheory.T.exists_mumford_bundle_iso_symmetric_birigidified_complex A g hA hg P hP h1 h2 hsw
  have hΘ := GlobalTheory.exists_gen_theta_of_isAbelianScheme ℂ A hA M hM
  have hcube : (cubeLB A ![fst A A, snd A A] M).IsLB := LB.isLB_linComb hM _ _
  have hcP : cls P hP = lam (cls M hM) (fst A A) (snd A A) :=
    ((cls_eq_iff hP hcube).2 hPM).trans (cls_cube_two hM _ _ hcube)
  have hpullP : ∀ {Y : Over (Sp ℂ)} (a b : Y ⟶ A) (h : (P.pull (lift a b).left).IsLB),
      cls _ h = lam (cls M hM) a b := by
    intro Y a b h
    rw [cls_pull hP, hcP, pull_lam, lift_fst, lift_snd]
  have hL : (P.pull (lift (𝟙 A) (𝟙 A)).left).IsLB := pull_isLB hP _
  have hcL : cls _ hL = lam (cls M hM) (𝟙 A) (𝟙 A) := hpullP _ _ hL
  obtain ⟨L₀, ⟨u₀⟩⟩ := GlobalTheory.HomDescentQb.exists_holUnif A g hA hg
  obtain ⟨u, Hm, χ, -, hF⟩ := GlobalTheory.exists_isFactorAH_frame_of_unif A hA L₀ g u₀ _ hL
  have hpos := GlobalTheory.AmpleHermPos.re_form_pos_of_relAmple A hA _ hL hamp g u Hm χ hF.1 hF.2.1 hF.2.2
  have hAH := GlobalTheory.TorusRM.isAH_of_isFactorAH hF hpos
  obtain ⟨Q, ψ, ρ, N, hN, hψ, hρ, e₁, e₂, e₃⟩ :=
    GlobalTheory.PosAHIsog.exists_isog_principal_lam g A hA _ u Hm χ hL hAH
  have hlamM : (abelian₂ A M).IsLB := LB.isLB_linComb hM _ _
  have hlamL : (abelian₂ A (P.pull (lift (𝟙 A) (𝟙 A)).left)).IsLB := LB.isLB_linComb hL _ _
  have hker : ∀ {Y : Over (Sp ℂ)} (y : Y ⟶ A),
      (∃ t : (P.pull (lift (snd A Y ≫ y) (fst A Y)).left).Gen, t.IsGen) →
      GlobalTheory.RealMult.HasGen ((abelian₂ A M).pull (lift (fst A Y) (snd A Y ≫ y)).left) ∧
      GlobalTheory.RealMult.HasGen ((abelian₂ A (P.pull (lift (𝟙 A) (𝟙 A)).left)).pull (lift (fst A Y) (snd A Y ≫ y)).left) := by
    intro Y y ht
    have h0 : lam (cls M hM) (fst A Y) (snd A Y ≫ y) = 0 := by
      rw [lam_comm, ← hpullP _ _ (pull_isLB hP _)]
      exact (cls_eq_zero_iff _).2 ht
    refine ⟨(cls_eq_zero_iff (pull_isLB hlamM _)).1 ?_, (cls_eq_zero_iff (pull_isLB hlamL _)).1 ?_⟩
    · rw [GlobalTheory.RealMult.Elliptic.cls_pull_lam hM]
      exact h0
    · rw [GlobalTheory.RealMult.Elliptic.cls_pull_lam hL, hcL, lam_lam_diag hM hΘ, h0, smul_zero]
  have hk : x ^ (N * N) = 1 :=
    GlobalTheory.KillSquare.pow_sq_eq_one_of_lam_trivial A hA _ hL Q ψ ρ N hψ hρ e₁ e₂ e₃ T x (hker x hx).2
  have key := GlobalTheory.torsion_point_comp_eq_one A hA M ((𝟙 A) ^ n) (N * N) hM (Nat.mul_pos hN hN) (fun y hy => ?_)
    T x hk (hker x hx).1
  · rwa [MonObj.comp_pow, Category.comp_id] at key
  · rw [MonObj.comp_pow, Category.comp_id]
    refine hn y ((cls_eq_zero_iff (pull_isLB hP _)).1 ?_)
    rw [hpullP, lam_comm, ← GlobalTheory.RealMult.Elliptic.cls_pull_lam hM _ _ (pull_isLB hlamM _)]
    exact (cls_eq_zero_iff _).2 hy

end GlobalTheory.BiKill
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

namespace GlobalTheory.WeightNat

theorem weight_nat : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A A' WW : HSp D) (FA : GlobalTheory.ChainFr.Fr A) (FW : GlobalTheory.ChainFr.Fr WW)
    (a b : D.what₂.Tau → ℚ) (α β : (Formalism.L2.Theta.AE D)ˣ →* Circle) (ωA : GlobalTheory.Grid.WRep A WW), IsInfFam θ →
    (∀ τ, Formalism.UG.HasSignature (gramAt D A τ) A.rank 0) → (∀ τ, Formalism.UG.HasSignature (gramAt D WW τ) WW.rank 0) →
    GlobalTheory.SquareComm.IsTriple A A' WW α β → (∀ τ, HasInfExp D α τ (a τ) ∧ HasInfExp D β τ (b τ)) →
    GlobalTheory.Grid.IsWeil ψ true A WW β (β / α) ωA → (∃ f, GlobalTheory.SquareComm.IsFinF ψ θ true FA FW f ∧ f ≠ 0) →
    ∃ n₀ : D.what₂.Tau → ℕ, ∀ τ, (n₀ τ : ℚ) = b τ - a τ - (WW.rank : ℚ) / 2 := by
  intro D ψ θ A A' WW FA FW a b α β ωA hθ hA hW hT hexp hWeil hf
  obtain ⟨f, hf, hf0⟩ := hf
  have key : ∀ τ, ∃ z : ℤ, (z : ℚ) = b τ - a τ - (WW.rank : ℚ) / 2 ∧ 0 ≤ z := by
    intro τ
    obtain ⟨a', b', ha', hb', hgap⟩ := hT.gap τ
    have e1 := GlobalTheory.Mem.HeckeExp.hasInfExp_unique ha' (hexp τ).1
    have e2 := GlobalTheory.Mem.HeckeExp.hasInfExp_unique hb' (hexp τ).2
    have hdiv := GlobalTheory.RealQuot.hasInfExp_div D α β τ (a τ) (b τ) (hexp τ).1 (hexp τ).2
    obtain ⟨x, y, hx, -, -⟩ := GlobalTheory.CompactFockAction.compactFockAll D _ WW (GlobalTheory.SquareComm.frSgn true FA) FW θ ψ β (β / α)
      (ωA.toSgn true) f τ (b τ) (b τ - a τ) hθ hWeil (hexp τ).2 hdiv hf hf0
    obtain ⟨p, q, -, hr, -⟩ := hT.sig
    have hpos : 0 < A.rank := by omega
    have h1 := hx ⟨0, hpos⟩
    generalize (GlobalTheory.SquareComm.frSgn true FA).ε τ ⟨0, hpos⟩ = e at h1
    have h2 := GlobalTheory.CompactFockAction.card_sign (FW.ε τ) e
    set c := (Finset.univ.filter fun i => FW.ε τ i = e).card
    have hz : ((-(c : ℤ) - x e : ℤ) : ℚ) = b τ - a τ - (WW.rank : ℚ) / 2 := by
      push_cast
      unfold GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.wtS at h1
      cases e <;> simp at h1 h2 <;> linarith
    have hq : (0 : ℚ) < b τ - a τ - (WW.rank : ℚ) / 2 := by
      rw [← e1, ← e2]; linarith
    refine ⟨-(c : ℤ) - x e, hz, ?_⟩
    have : (0 : ℚ) ≤ ((-(c : ℤ) - x e : ℤ) : ℚ) := by rw [hz]; exact hq.le
    exact_mod_cast this
  choose z hz hz0 using key
  refine ⟨fun τ => (z τ).toNat, fun τ => ?_⟩
  rw [← hz τ]
  exact_mod_cast Int.toNat_of_nonneg (hz0 τ)

end GlobalTheory.WeightNat
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.vacuum_character_positive_definite_source : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → IsInfFam θ → S.SigOK → T.SigOK → ∀ (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ), (∀ τ, IsCartanInv (gramAt D S τ) 1) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) → ∀ (a b : D.what₂.Tau → ℚ), (∀ τ, HasInfExp D χS τ (a τ)) → (∀ τ, HasInfExp D χT τ (b τ)) → ∀ (x₁ x₂ x₃ : D.what₂.Tau → ℤ), (∀ τ, (x₁ τ : ℚ) = a τ + (S.rank : ℚ) / 2) → (∀ τ, (x₂ τ : ℚ) = a τ - (S.rank : ℚ) / 2) → (∀ τ, (x₃ τ : ℂ) = -((sT τ).trace / 2 + (b τ : ℂ))) → ∀ f, IsThetaFunO ψ S T f → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO 1 (sT τ)) f) → ∀ g ∈ GinfC S, ∀ h ∈ GinfC T, (∀ τ, sT τ * compAt θ τ (mt T h) = compAt θ τ (mt T h) * sT τ) → om (g, h) f = (∏ τ, ((1 / 2 : ℂ) • (1 + sT τ) * compAt θ τ (mt T h) + (1 / 2 : ℂ) • (1 - sT τ)).det ^ x₁ τ * ((1 / 2 : ℂ) • (1 - sT τ) * compAt θ τ (mt T h) + (1 / 2 : ℂ) • (1 + sT τ)).det ^ x₂ τ * (compAt θ τ (mt S g)).det ^ x₃ τ) • f := by
  first | exact @GlobalTheory.VacuumCharacter.vacuum_character | exact GlobalTheory.VacuumCharacter.vacuum_character | (intros; apply GlobalTheory.VacuumCharacter.vacuum_character <;> assumption)
end
