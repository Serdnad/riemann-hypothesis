module

public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle032
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeEqSmulOfIsot
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1818
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankWeightComponentEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1880
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1785
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle232
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle160
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle066
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1651
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HESmulRight
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1195
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1874
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1347
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitEqNormCompletionTensorOfIsInertAt
import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtA
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1199
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1881
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle013
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1882
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaLatticeImageRationalHomLattice
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.IntegralLeaf.LeafINTFree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.BotFormula

def toFinE (D : D7) : Formalism.MainNotions.StandardLatticesGL3.AE D ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E :=
  (Algebra.TensorProduct.comm ℚ D.host.E (FiniteAdeleRing (𝓞 ℚ) ℚ)).toRingEquiv.trans
    (GlobalTheory.LFun.finAdEquiv ℚ D.host.E)

def IsFinPt {D : D7} (WW : HSp D) (g : Formalism.L2.Theta.GA D WW) {n : ℕ} (h : Formalism.MainNotions.StandardLatticesGL3.GA D n) : Prop :=
  g ∈ GfC WW ∧ ∃ e : WW.rank = n, ∀ i j,
    GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (((finHom WW g : GL (Fin WW.rank) _) : Matrix (Fin WW.rank) (Fin WW.rank) _) i j) =
      toFinE D (((h : GL (Fin n) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin n) (Fin n) (Formalism.MainNotions.StandardLatticesGL3.AE D)) (Fin.cast e i) (Fin.cast e j))

def minorF {D : D7} {a d a₁ d₁ : ℕ} {n : D.what₂.Tau → ℕ} (ha : a = a₁) (hd : d = d₁) (T : Tup D a d n) : PolF D d₁ a₁ :=
  MvPolynomial.rename (fun k : D.what₂.Tau × Fin d × Fin a => (k.1, Fin.cast hd k.2.1, Fin.cast ha k.2.2))
    (GlobalTheory.NormSum.minorPol D T)

theorem IsFinPt.cast {D : D7} {WW : HSp D} {g : Formalism.L2.Theta.GA D WW} {n n' : ℕ} (e : n' = n) {h : Formalism.MainNotions.StandardLatticesGL3.GA D n}
    (hg : IsFinPt WW g h) : IsFinPt WW g (e ▸ h : Formalism.MainNotions.StandardLatticesGL3.GA D n') := by
  subst e; exact hg

theorem lamC_mul {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) {x y : ℂ} (hx : x ∈ Qbar) (hy : y ∈ Qbar) :
    lamC lam (x * y) = lamC lam x * lamC lam y := by
  unfold lamC
  rw [dite_eq_left (Qbar.mul_mem hx hy), dite_eq_left hx, dite_eq_left hy, ← map_mul]
  rfl

end GlobalTheory.BotFormula
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram SphOp hyp)
open GlobalTheory.StdFrame (StdPsi)
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI

namespace GlobalTheory.PartTypeW

theorem part_in_eigenpart : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) {s : ℕ}, A.fam.Ok s → Core R F → ∀ SF, IsSF R SF → ∀ {n : ℕ} (hF : D.host.F = maximalRealSubfield D.host.E) (PY : principalLevelFrame.RowPsi (Yc D 0) n) (PW : ∀ i, principalLevelFrame.RowPsi (Wc D i) n), StdPsi hF PY → (∀ i, StdPsi hF (PW i)) → ∀ π i0 c, principalLevelFrame.IsEigOf (PW i0) (levS _ (R.βW i0) (R.datWp i0 (R.levL F false (sg0 D A)))) (levChi _ (R.βW i0) (R.datWp i0 (R.levL F false (sg0 D A)))) SF π c → ∀ i, ∀ U ∈ principalLevelFrame.isotL R.θ (PW i) (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i (R.levL F false (sg0 D A)))) (levChi _ (R.βW i) (R.datWp i (R.levL F false (sg0 D A)))) (R.eWf i (sg0 D A)) π, ∃ x ∈ Wcc R SF i c, (R.HW i _).e x = U := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F s _hOk hC SF hSF n hF PY PW _hPY hPW π i0 c hEig i U hU
  have hLev := hC.lev

  have hN : ∀ (cc : ℕ) (P : Pl D.host.E), (((1 ^ cc : ℕ) : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
    intro cc P h
    rw [one_pow, Nat.cast_one] at h
    exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)
  have LO := fun (j : Fin D.R.m) (Lv : LevelP R.Pg D.R.r ℂ) (P : Pl D.host.E) (hG : Good R A.μ0 P) =>
    GlobalTheory.LevOp.level_operators (Wc D j) (R.βW j) (R.ΛW j) _ (R.datWp j Lv) (hLev.βW j).choose_spec P
      (hN _ P) (fun PP h => hG PP (h.imp id (fun h' => absurd h' (Finset.notMem_empty _))))
  have hGood := fun P => (GlobalTheory.GoodPrimes.good_primes R F hLev).2.2.1 SF hSF P

  have hU' := hU
  simp only [principalLevelFrame.isotL, Mult.goodPart, Submodule.mem_inf, LinearMap.mem_ker] at hU'
  obtain ⟨⟨hUM, hUe⟩, hUiso⟩ := hU'

  have hle : ∀ k ∈ levS (Wc D i) (R.βW i) (R.datWp i R.triv),
      k ∈ levS (Wc D i) (R.βW i) (R.datWp i (R.levL F false (sg0 D A))) ∧
        levChi (Wc D i) (R.βW i) (R.datWp i (R.levL F false (sg0 D A))) k =
          levChi (Wc D i) (R.βW i) (R.datWp i R.triv) k := by
    intro k hk
    obtain ⟨h1, h2⟩ := GlobalTheory.HeckeParts.triv_le (V := Wc D i) (β := R.βW i) (R.levL F false (sg0 D A)) k hk
    obtain ⟨_, h3⟩ := GlobalTheory.HeckeParts.triv_le (V := Wc D i) (β := R.βW i) R.triv k hk
    exact ⟨h1, h2.trans h3.symm⟩
  have hU0 : U ∈ Mult R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i R.triv)) (levChi _ (R.βW i) (R.datWp i R.triv)) :=
    GlobalTheory.HeckeParts.mult_mono hle hUM

  have hrange := (hC.models.HW i (sg0 D A)).2.1
  obtain ⟨x, hx⟩ : U ∈ LinearMap.range (R.HW i (sg0 D A)).e := by
    rw [hrange]; exact hU0
  refine ⟨x, ?_, hx⟩
  rw [GlobalTheory.Hk3.Wcc, Submodule.mem_comap, hx]
  refine Submodule.mem_inf.2 ⟨Submodule.mem_inf.2 ⟨hU0, LinearMap.mem_ker.2 hUe⟩, Submodule.mem_inf.2 ⟨hU0, ?_⟩⟩
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
  intro P d B hB
  obtain ⟨_, _, _, _, hoff, -⟩ := id hB
  have hG : Good R A.μ0 P := (hGood P).1 hoff
  have hSph : SphOp (Wc D i) P d B := (((LO i R.triv P hG).2.1 SF d B).1 hB).2
  obtain ⟨B0, hB0⟩ : IsLab (Wc D i0) P d :=
    (GlobalTheory.LabEq.isLab_W_iff (s := s) R F hC i0 P d hG).2.2
      ((GlobalTheory.LabEq.isLab_W_iff (s := s) R F hC i P d hG).2.1 ⟨B, hSph⟩)
  obtain ⟨a, ha⟩ := GlobalTheory.T.sphericalHecke_scalar_on_spherical_vectors hF (PW i0) (hPW i0) π P d B0 hB0
  obtain ⟨⟨x0, hx0S, hx0, hx0T⟩, hEigOp, -⟩ := hEig
  have hB0full := ((LO i0 (R.levL F false (sg0 D A)) P hG).2.1 SF d B0).2 ⟨hoff, hB0⟩
  have hfix0 : ∀ κ, (PW i0).ψ κ ∈ hyp (Wc D i0) P → Formalism.L2.NG.rt D.host.E n κ x0 = x0 := by
    intro κ hκ
    obtain ⟨h1, h2⟩ := (LO i0 (R.levL F false (sg0 D A)) P hG).1 _ hκ
    rw [hx0T κ h1]
    simp only [h2, one_smul]
  have hac : a = c P d := by
    have e2 := hEigOp P d B0 hB0full x0 hx0S hx0T
    rw [ha x0 hx0S hfix0] at e2
    exact smul_left_injective ℂ hx0 e2
  obtain ⟨hiff, htr⟩ := GlobalTheory.T.sphericalEigenvalues_independent_of_standardFrame hF (PW i) (PW i0) (hPW i) (hPW i0) P d
  have hvec : ∀ y ∈ π.S, (∀ κ, (PW i).ψ κ ∈ hyp (Wc D i) P → Formalism.L2.NG.rt D.host.E n κ y = y) →
      principalLevelFrame.Hecke₃ (PW i) B y = c P d • y := by
    intro y hy hfy
    rw [htr B B0 hSph hB0 y hfy, ha y hy (fun κ hκ => hfy κ ((hiff κ).2 hκ)), hac]
  have hUfix : ∀ k ∈ hyp (Wc D i) P, postOn (R.MW i (sg0 D A)) (principalLevelFrame.rtA k) U = U := by
    intro k hk
    obtain ⟨h1, h2⟩ := (LO i (R.levL F false (sg0 D A)) P hG).1 k hk
    have hl := principalLevelFrame.mult_lev hUM
    apply MultilinearMap.ext
    intro v
    funext g
    rw [Mult.postOn_apply]
    show U v (g * k) = U v g
    rw [hl v k h1 g, h2, one_mul]
  exact GlobalTheory.IsotSph.hecke_eq_smul_of_isot hF (PW i) (hPW i) R.θ (R.MW i (sg0 D A)) π P d B (c P d) hSph hvec U hUiso hUfix

end GlobalTheory.PartTypeW
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ThetaLawLat

variable {D : D7}

theorem entry_mem_AA {N N' : ℕ} {z : Matrix (Fin N') (Fin N) D.host.E}
    (hz : z ∈ GlobalTheory.InertSign.RL D D.host.ccK (Formalism.MainNotions.StandardLatticesGL3.stdL D N) (Formalism.MainNotions.StandardLatticesGL3.stdL D N'))
    (p : Fin N') (q : Fin N) : z p q ∈ (D.host.AA : Submodule (𝓞 D.host.E) D.host.E) := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨t, ht, A, hA, rfl⟩ := hz
    have hAint : GlobalTheory.InertSign.IntE D (A p q) := by
      have h1 : (Pi.single q 1 : Fin N → D.host.E) ∈ Formalism.MainNotions.StandardLatticesGL3.stdL D N := by
        refine GlobalTheory.ThetaLatImage.mem_stdL.2 fun i => ?_
        by_cases h : i = q
        · subst h; rw [Pi.single_eq_same]; exact one_mem _
        · rw [Pi.single_eq_of_ne h]; exact zero_mem _
      have h2 := GlobalTheory.ThetaLatImage.mem_homL.1 hA _ h1
      rw [Matrix.mulVec_single_one] at h2
      exact GlobalTheory.ThetaLatImage.mem_stdL.1 h2 p
    obtain ⟨o, ho⟩ := hAint
    have ht' : t ∈ (D.host.AA : Submodule (𝓞 D.host.E) D.host.E) := by
      induction ht using Submodule.span_induction with
      | mem t ht =>
        obtain ⟨c, hc, a, ha, rfl⟩ := ht
        have hc' : ((c : D.host.K) : D.host.E) ∈ (D.host.ccE : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) :=
          FractionalIdeal.mem_coeIdeal_of_mem _ (Ideal.mem_map_of_mem (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) hc)
        exact FractionalIdeal.mul_mem_mul hc' ha
      | zero => exact zero_mem _
      | add x y _ _ hx hy => exact add_mem hx hy
      | smul o x _ hx => exact Submodule.smul_mem _ o hx
    rw [Matrix.smul_apply, smul_eq_mul, ← ho, mul_comm, ← Algebra.smul_def]
    exact Submodule.smul_mem _ o ht'
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | smul o x _ hx => exact Submodule.smul_mem _ o hx

end GlobalTheory.ThetaLawLat

namespace GlobalTheory.ThetaLawLat

variable {D : D7}

theorem one_mem_intAf' : (1 : Af D.host.F) ∈ intAf D.host.F := fun v => by
  rw [map_one]; exact one_mem _

theorem inv_frame {S : HSp D} (frS : GL (Fin S.rank) D.host.E)
    (hS : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frS.1 * S.gram * frS.1 = 1) :
    (frS⁻¹).1 = frS.1ᴴ * S.gram := by
  have h1 : (frS.1ᴴ * S.gram) * frS.1 = 1 := hS
  calc (frS⁻¹).1 = ((frS.1ᴴ * S.gram) * frS.1) * (frS⁻¹).1 := by rw [h1, Matrix.one_mul]
    _ = frS.1ᴴ * S.gram := by rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]

theorem finRat_frame_mem_latO {S T : HSp D} (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E)
    (hS : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frS.1 * S.gram * frS.1 = 1)
    (z : Matrix (Fin T.rank) (Fin S.rank) D.host.E)
    (hz : ∀ p q, z p q ∈ (D.host.AA : Submodule (𝓞 D.host.E) D.host.E)) :
    GlobalTheory.VacUnique.finRat S T (frT.1 * z * (frS⁻¹).1) ∈
      latO S T (colLat frS : Set (Fin S.rank → D.host.E)) (colLat frT : Set (Fin T.rank → D.host.E)) (fun _ => True) := by
  have key : GlobalTheory.VacUnique.finRat S T (frT.1 * z * (frS⁻¹).1) =
      ∑ p, ∑ q, Matrix.of fun i j => (pairA D.host.F 0 1) ⊗ₜ[D.host.F]
        (z p q * (fun a => frT.1 a p) i * ∑ k, star ((fun a => frS.1 a q) k) * S.gram k j) := by
    ext i j
    simp only [Matrix.sum_apply, Matrix.of_apply]
    simp only [← TensorProduct.tmul_sum]
    show (pairA D.host.F 0 1) ⊗ₜ[D.host.F] (frT.1 * z * (frS⁻¹).1) i j = _
    congr 1
    rw [inv_frame frS hS]
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by ring
  rw [key]
  refine AddSubgroup.sum_mem _ fun p _ => AddSubgroup.sum_mem _ fun q _ => AddSubgroup.subset_closure ?_
  exact ⟨1, one_mem_intAf', fun v h => (h trivial).elim, z p q, hz p q, _,
    Submodule.subset_span ⟨q, rfl⟩, _, Submodule.subset_span ⟨p, rfl⟩, rfl⟩

theorem mem_La_frame : ∀ {D : D7} (S T : HSp D) (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E), Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frS.1 * S.gram * frS.1 = 1 → Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frT.1 * T.gram * frT.1 = 1 → ∀ δ : ℂ, ∀ x ∈ Formalism.MainNotions.TaylorLogMetric.La D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) (Formalism.MainNotions.StandardLatticesGL3.stdL D S.rank) (Formalism.MainNotions.StandardLatticesGL3.stdL D T.rank), ∃ v : Matrix (Fin T.rank) (Fin S.rank) D.host.E, GlobalTheory.VacUnique.finRat S T v ∈ latO S T (colLat frS : Set (Fin S.rank → D.host.E)) (colLat frT : Set (Fin T.rank → D.host.E)) (fun _ => True) ∧ x = δ • (fun τ a b => ((GlobalTheory.FockPos.frAt frT τ)⁻¹ * Matrix.of (GlobalTheory.VacUnique.infRat S T v τ) * GlobalTheory.FockPos.frAt frS τ) a b) := by
  intro D S T frS frT hS hT δ x hx
  obtain ⟨z, hz, rfl⟩ := GlobalTheory.ThetaLatImage.La_sub hx
  refine ⟨frT.1 * z * (frS⁻¹).1, finRat_frame_mem_latO frS frT hS z (GlobalTheory.ThetaLawLat.entry_mem_AA hz), ?_⟩
  have hmap : ∀ τ, Matrix.of (GlobalTheory.VacUnique.infRat S T (frT.1 * z * (frS⁻¹).1) τ) =
      GlobalTheory.FockPos.frAt frT τ * Matrix.of (fun i j => tauE D τ (z i j)) * (GlobalTheory.FockPos.frAt frS τ)⁻¹ := by
    intro τ
    have hi : (GlobalTheory.FockPos.frAt frS τ)⁻¹ = (frS⁻¹).1.map (tauE D τ) := by
      refine Matrix.inv_eq_right_inv ?_
      rw [GlobalTheory.FockPos.frAt, ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
    rw [hi]
    show (frT.1 * z * (frS⁻¹).1).map (tauE D τ) = _
    rw [Matrix.map_mul, Matrix.map_mul]
    rfl
  funext τ a b
  rw [GlobalTheory.ThetaLatImage.pt_apply]
  show _ = δ * ((GlobalTheory.FockPos.frAt frT τ)⁻¹ * Matrix.of (GlobalTheory.VacUnique.infRat S T (frT.1 * z * (frS⁻¹).1) τ) *
    GlobalTheory.FockPos.frAt frS τ) a b
  rw [hmap τ, GlobalTheory.ThetaLawOF.coord_back frS frT (fun τ i j => tauE D τ (z i j)) τ]
  rfl

end GlobalTheory.ThetaLawLat
end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertSph.Scal

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem disc_sub_sq_notMem (v : Pl (F := F)) (b c t : 𝓞 F) (h2 : (2 : 𝓞 F) ∉ v.asIdeal)
    (hroot : ∀ r : 𝓞 F, r ^ 2 + b * r + c ∉ v.asIdeal) : t ^ 2 - (b ^ 2 - 4 * c) ∉ v.asIdeal := by
  intro h
  obtain ⟨s, a, ha, hs⟩ := v.isMaximal.exists_inv h2
  apply hroot (s * (t - b))
  have h4 : (2 : 𝓞 F) * (2 * ((s * (t - b)) ^ 2 + b * (s * (t - b)) + c)) ∈ v.asIdeal := by
    have e : (2 : 𝓞 F) * (2 * ((s * (t - b)) ^ 2 + b * (s * (t - b)) + c)) =
        (t ^ 2 - (b ^ 2 - 4 * c)) + a * ((t - b) * (a * (t - b) - 2 * t)) := by
      have : a = 1 - s * 2 := by linear_combination hs
      subst this
      ring
    rw [e]
    exact add_mem h (Ideal.mul_mem_right _ _ ha)
  exact ((v.isPrime.mem_or_mem ((v.isPrime.mem_or_mem h4).resolve_left h2)).resolve_left h2)

theorem exists_delta (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E))
    (hin : Formalism.UG.IsInertAt F E v w) (h2 : (2 : 𝓞 F) ∉ v.asIdeal) :
    ∃ (δ : 𝓞 E) (D : 𝓞 F), σ (δ : E) = -(δ : E) ∧ (δ : E) * δ = algebraMap F E (D : F) ∧ D ∉ v.asIdeal ∧
      1 - D ∉ v.asIdeal := by
  have hp : (v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E))).IsPrime := by
    rw [show v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E)) = w.asIdeal from hin]
    exact w.isPrime
  obtain ⟨a, b, c, hq, hc, hroot⟩ := GlobalTheory.InertUnitNorm.exists_integral_gen σ hσ v hp
  have hδ : ((2 * a + algebraMap (𝓞 F) (𝓞 E) b : 𝓞 E) : E) = 2 * (a : E) + algebraMap F E (b : F) := rfl
  have hD : ((b ^ 2 - 4 * c : 𝓞 F) : F) = (b : F) ^ 2 - 4 * (c : F) := rfl
  refine ⟨2 * a + algebraMap (𝓞 F) (𝓞 E) b, b ^ 2 - 4 * c, ?_, ?_, ?_, ?_⟩
  · rw [hδ, map_add (f := _), map_mul, map_ofNat, AlgHom.commutes, hc]
    ring
  · rw [hδ, hD, map_sub, map_mul, map_pow, map_ofNat]
    linear_combination 4 * hq
  · intro h
    apply disc_sub_sq_notMem v b c 0 h2 hroot
    simpa using neg_mem h
  · simpa using disc_sub_sq_notMem v b c 1 h2 hroot

theorem exists_inv (v : Pl (F := F)) (D : 𝓞 F) (hD : D ∉ v.asIdeal) :
    ∃ c : Fv F v, c ∈ v.adicCompletionIntegers F ∧ c * algebraMap F (Fv F v) (D : F) = 1 := by
  have h1 : Valued.v (algebraMap F (Fv F v) (D : F)) = 1 := by
    have h := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (D : F)
    have h' : v.valuation F (D : F) = 1 := (HeightOneSpectrum.valuation_eq_one_iff_notMem v).2 hD
    rw [← h', ← h]
    rfl
  have h0 : algebraMap F (Fv F v) (D : F) ≠ 0 := by
    intro h
    rw [h, map_zero] at h1
    exact zero_ne_one h1
  refine ⟨(algebraMap F (Fv F v) (D : F))⁻¹, ?_, inv_mul_cancel₀ h0⟩
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, h1, inv_one]

theorem smul_eq_of_at {M : Type} [AddCommGroup M] [Module (AF F) M] {v : Pl (F := F)} {z : M} (hz : At (evFin F v) z)
    {a : AF F} (ha : evFin F v a = 1) : a • z = z := by
  have h := hz (a - 1) (by rw [map_sub, map_one, ha, sub_self])
  rwa [sub_smul, one_smul, sub_eq_zero] at h

theorem at_of_mem_latAt {d : ℕ} (W : Spc F E d) (v : Pl (F := F)) {z : Fin d → AE F E} (hz : z ∈ latAt W v) :
    At (evFin F v) z := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, -, y, -, rfl⟩ := hz
    intro u hu
    rw [smul_smul, ← smul_eq_mul u a, ha u hu, zero_smul]
  | zero => intro u _; exact smul_zero u
  | add x y _ _ hx hy => intro u hu; rw [smul_add, hx u hu, hy u hu, add_zero]
  | neg x _ hx => intro u hu; rw [smul_neg, hx u hu, neg_zero]

theorem lift_smul_mem {d : ℕ} (W : Spc F E d) (v : Pl (F := F)) {c : Fv F v} (hc : c ∈ v.adicCompletionIntegers F)
    (o : 𝓞 E) {z : Fin d → AE F E} (hz : z ∈ latAt W v) :
    (GlobalTheory.LatVac.liftV v c • inclR (F := F) (AF F) (o : E)) • z ∈ latAt W v :=
  GlobalTheory.InertLocFrame.Lat.smul_mem_latAt W (AddSubgroup.subset_closure
    ⟨_, GlobalTheory.LatVac.at_liftV v c, by rwa [GlobalTheory.LatVac.evFin_liftV], o, rfl⟩) hz

end GlobalTheory.InertSph.Scal

namespace GlobalTheory.InertSph


open GlobalTheory.InertSph.Scal GlobalTheory.LatVac in
theorem exists_traceZero_unit : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (d : ℕ) (W : Spc F E d) (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w →
    ∃ β b up um : AE F E, At (evFin F v) β ∧ cA σ β = -β ∧ ∀ z ∈ GlobalTheory.InertSph.latAt W v,
      β • z ∈ GlobalTheory.InertSph.latAt W v ∧ b • z ∈ GlobalTheory.InertSph.latAt W v ∧ up • z ∈ GlobalTheory.InertSph.latAt W v ∧
      um • z ∈ GlobalTheory.InertSph.latAt W v ∧ (β * b) • z = z ∧ ((1 + β) * up) • z = z ∧ ((1 - β) * um) • z = z := by
  intro F E _ _ _ _ _ σ B hB d W v w hin
  obtain ⟨δ, D, hσ, hsq, hD, hD1⟩ := exists_delta σ hB.cm v w hin (hB.inert v w hin).1
  obtain ⟨c, hc, hcD⟩ := exists_inv v D hD
  obtain ⟨c', hc', hcD'⟩ := exists_inv v (1 - D) hD1
  have hcD'' : c' * (1 - algebraMap F (Fv F v) (D : F)) = 1 := by
    rwa [show ((1 - D : 𝓞 F) : F) = 1 - (D : F) from rfl, map_sub, map_one] at hcD'
  set x : AE F E := inclR (F := F) (AF F) (δ : E) with hx
  have hxx : x * x = algebraMap (AF F) (AE F E) (algebraMap F (AF F) (D : F)) := by
    rw [hx, ← map_mul, hsq, ← IsScalarTower.algebraMap_apply]
    exact (Algebra.TensorProduct.includeRight : E →ₐ[F] AE F E).commutes _
  have hp : inclR (F := F) (AF F) ((1 + δ : 𝓞 E) : E) = 1 + x := by
    rw [show ((1 + δ : 𝓞 E) : E) = 1 + (δ : E) from rfl, map_add (f := _), map_one]
  have hm : inclR (F := F) (AF F) ((1 - δ : 𝓞 E) : E) = 1 - x := by
    rw [show ((1 - δ : 𝓞 E) : E) = 1 - (δ : E) from rfl, map_sub, map_one]
  have he : liftV v (1 : Fv F v) * liftV v c' = liftV v c' :=
    smul_eq_of_at (at_liftV v c') (evFin_liftV v 1)
  have he' : algebraMap (AF F) (AE F E) (liftV v (1 : Fv F v)) * algebraMap (AF F) (AE F E) (liftV v c') =
      algebraMap (AF F) (AE F E) (liftV v c') := by rw [← map_mul, he]
  have key : ∀ z ∈ latAt W v, ∀ a : AF F, evFin F v a = 1 → algebraMap (AF F) (AE F E) a • z = z := by
    intro z hz a ha
    rw [algebraMap_smul]
    exact smul_eq_of_at (at_of_mem_latAt W v hz) ha
  have hu : evFin F v (liftV v c' * (1 - algebraMap F (AF F) (D : F))) = 1 := by
    rw [map_mul, map_sub, map_one, evFin_liftV, AlgHom.commutes, hcD'']
  refine ⟨liftV v 1 • x, liftV v c • x, liftV v c' • (1 - x), liftV v c' • (1 + x), ?_, ?_, fun z hz =>
    ⟨lift_smul_mem W v (one_mem _) δ hz, lift_smul_mem W v hc δ hz, hm ▸ lift_smul_mem W v hc' (1 - δ) hz,
      hp ▸ lift_smul_mem W v hc' (1 + δ) hz, ?_, ?_, ?_⟩⟩
  · intro u hu
    rw [smul_smul, ← smul_eq_mul, at_liftV v 1 u hu, zero_smul]
  · have h : cA σ x = -x := by
      have h1 : cA σ x = inclR (F := F) (AF F) (σ (δ : E)) := by
        simp [hx, cA, inclR]
      rw [h1, hσ, map_neg]
    rw [map_smul, h, smul_neg]
  · have h := key z hz (liftV v 1 * liftV v c * algebraMap F (AF F) (D : F)) (by
      rw [map_mul, map_mul, evFin_liftV, evFin_liftV, AlgHom.commutes, one_mul, hcD])
    convert h using 2
    simp only [Algebra.smul_def, map_mul, ← hxx]
    ring
  · convert key z hz _ hu using 2
    simp only [Algebra.smul_def, map_mul, map_sub, map_one, ← hxx]
    linear_combination (x * (1 - x)) * he'
  · convert key z hz _ hu using 2
    simp only [Algebra.smul_def, map_mul, map_sub, map_one, ← hxx]
    linear_combination (-x * (1 + x)) * he'

end GlobalTheory.InertSph

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped GlobalTheory.VacAny


theorem _root_.GlobalTheory.T.adelicSchrodinger_tensor_eq_local_of_supportedAt : ∀ {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) {κ : Type} [Fintype κ]
    (w : (κ → AF F) × (κ → AF F)), (∀ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) (w.1 i)) →
    (∀ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) (w.2 i)) → ∀ (φ : (κ → Fv F v) → ℂ) (r : (κ → AF F) → ℂ),
    (∀ x z : κ → AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) z → r (x + z) = r x) →
    GlobalTheory.WeilM.schr ψ w (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.AdelicU.evFin F v) φ r) =
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.AdelicU.evFin F v)
        (GlobalTheory.WeilM.schr (GlobalTheory.VacAny.psiV ψ v) (fun i => GlobalTheory.AdelicU.evFin F v (w.1 i), fun i => GlobalTheory.AdelicU.evFin F v (w.2 i)) φ) r := by
  first | exact @GlobalTheory.SchrLoc.schr_tens_of_at | exact GlobalTheory.SchrLoc.schr_tens_of_at | (intros; apply GlobalTheory.SchrLoc.schr_tens_of_at <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.fockMonomial_at_origin_gaussian_entire_orthonormal : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E), IsStdChar D ψ (-1) → IsInfFam θ → Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frS.1 * S.gram * frS.1 = 1 → Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frT.1 * T.gram * frT.1 = 1 → ∀ (F : WO S T → ℂ) (Φ : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank → ℂ), Differentiable ℂ Φ → (∀ w : WO S T, w.map (finPart D) = 0 → F w = GlobalTheory.FockPos.gaussO θ frS frT w * Φ (GlobalTheory.FockPos.zCo θ frS frT w)) → ∀ k : FVar D T.rank S.rank →₀ ℕ, pureTensorO ψ θ S T (fun _ => 1) (fun _ => 1) (GlobalTheory.FockPos.frAt frS) (GlobalTheory.FockPos.frAt frT) F (MvPolynomial.monomial k 1) 0 = (((Real.sqrt (2 * Real.pi * Formalism.L2.Pj.xiR D) : ℝ) : ℂ)⁻¹) ^ (k.sum fun _ n => n) * Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) Φ := by
  first | exact @GlobalTheory.FockPos.fock_monomial_zero_of_on | exact GlobalTheory.FockPos.fock_monomial_zero_of_on | (intros; apply GlobalTheory.FockPos.fock_monomial_zero_of_on <;> assumption)
end
