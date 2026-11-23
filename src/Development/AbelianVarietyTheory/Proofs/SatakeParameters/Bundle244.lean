module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle185
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IdemOfIsPrimeIdem
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle021
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle015
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NatCastMemOfPlace
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle017
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle224
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EquivFrameBTheta
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle020
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle239
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle238
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle213
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle164
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle297
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle240
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.SharpPoly
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.Bundle001
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle241
public import Formalism.LocalToGlobal.Columns.Bundle023
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv
public import Formalism.LocalToGlobal.Columns.ChainTwTopQ
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainStepHecke

theorem haar_fd {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (hM : R.IsModels) (t : T) (j : ℕ)
    (hj : j < D.R.m) :
    (R.νY t j).IsHaarMeasure ∧ IsFundamentalDomain (GQ (Yc D j)) (R.fdY t j) (R.νY t j) := by
  by_cases h : j + 1 < D.R.m
  · have := hM.νY t j h
    exact ⟨this.1.1, this.2⟩
  · obtain rfl : j = D.R.m - 1 := by omega
    have := hM.νY' t
    exact ⟨this.1.1, this.2⟩

theorem step_hk : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Chain.LiftInteg D → Core R F → SchurAll R → ∀ t P k, Good R t P → k + 1 < D.R.m → VacFix R.ψ (R.ωY t k) P → ∀ cS cT, Match R.ψ (R.ωY t k) P cS (dualC cT) → ∀ U U' : R.CC t (k + 1), (∀ v, U'.1 v = hk _ P cT (U.1 v)) → ∀ v, (R.ioY t k U').1 v = hk _ P cS ((R.ioY t k U).1 v) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hI hC hS t P k hG hkk hF cS cT hM U U' hU v
  classical
  have hθ : IsInfFam R.θ := hC.models.inf
  have hN := ((GlobalTheory.T.theta_lift_levels_good_primes_properties R F hC.lev).2.1 t P hG).1
  have hio := hC.chain.ioY t k (by omega)
  obtain ⟨hνH, hνF⟩ := haar_fd R hC.models t (k + 1) hkk
  obtain ⟨hμH, hμF⟩ := haar_fd R hC.models t k (by omega)
  have lo : ∀ j, j < D.R.m → (∀ κ ∈ hyp (Yc D j) P, κ ∈ levG _ (R.βY j) (R.datYt t j R.triv) ∧
        levChi _ (R.βY j) (R.datYt t j R.triv) κ = 1) ∧
      ∀ c, ∀ U ∈ Mult R.θ (R.MY j) (levS _ (R.βY j) (R.datYt t j R.triv)) (levChi _ (R.βY j) (R.datYt t j R.triv)),
        postOn (R.MY j) (hk _ P c) U ∈ Mult R.θ (R.MY j) (levS _ (R.βY j) (R.datYt t j R.triv)) (levChi _ (R.βY j) (R.datYt t j R.triv)) := by
    intro j hj
    obtain ⟨c, hb⟩ := hC.lev.βY j hj
    have h := GlobalTheory.T.level_operators_at_prime_off_level_datum (Yc D j) (R.βY j) (R.ΛY j) _ (R.datYt t j R.triv) hb P (by
      rw [Nat.cast_pow]
      exact fun h => hN (P.isPrime.mem_of_pow_mem _ h)) hG
    exact ⟨h.1, fun c U hU => h.2.2.2.2 _ R.θ (R.MY j) c hθ U hU⟩

  have hwm := (lo k (by omega)).2 cS _ ((mem_multT R.θ _ _ _ _).1 (R.ioY t k U).2)
  let w : R.CC t k := ⟨PiTensorProduct.lift (postOn (R.MY k) (hk _ P cS) (PiTensorProduct.lift.symm (R.ioY t k U).1)),
    (mem_multT R.θ _ _ _ _).2 (by simpa using hwm)⟩
  have hw : ∀ x, w.1 x = hk _ P cS ((R.ioY t k U).1 x) := by
    intro x
    have : w.1 = (hk _ P cS) ∘ₗ (R.ioY t k U).1 := PiTensorProduct.ext (MultilinearMap.ext fun y => by
      simp [w, postOn_apply])
    rw [this]; rfl
  have hmap := (GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ _).1 ((mem_multT R.θ _ _ _ _).1 U.2)
  have key : ∀ φ x, (R.ioY t k U').1 (R.ItY k φ (PiTensorProduct.tprod ℂ x)) = w.1 (R.ItY k φ (PiTensorProduct.tprod ℂ x)) := by
    intro φ x
    have hvac := (GlobalTheory.T.fockVectors_chain_isVacuum_off_thetaLevels R F hC t P hG).1 k hkk φ
    have e' : (R.ioY t k U').1 (R.ItY k φ (PiTensorProduct.tprod ℂ x)) =
        Lift.liftInt (R.νY t (k + 1)) (R.fdY t (k + 1)) (thetaKO (R.ωY t k)) (R.ptY t k φ) (U'.1 (PiTensorProduct.tprod ℂ x)) :=
      funext fun g => (hio.eq U' φ _ g).symm
    have e : (R.ioY t k U).1 (R.ItY k φ (PiTensorProduct.tprod ℂ x)) =
        Lift.liftInt (R.νY t (k + 1)) (R.fdY t (k + 1)) (thetaKO (R.ωY t k)) (R.ptY t k φ) (U.1 (PiTensorProduct.tprod ℂ x)) :=
      funext fun g => (hio.eq U φ _ g).symm
    have haut : IsAutFunSm R.θ _ (U.1 (PiTensorProduct.tprod ℂ x)) := by simpa using hmap.aut x
    have hcusp : IsCuspFun _ (U.1 (PiTensorProduct.tprod ℂ x)) := by simpa using hmap.cusp x
    have hlev : ∀ κ ∈ levS _ (R.βY (k + 1)) (R.datYt t (k + 1) R.triv), ∀ g, U.1 (PiTensorProduct.tprod ℂ x) (g * κ) =
        levChi _ (R.βY (k + 1)) (R.datYt t (k + 1) R.triv) κ * U.1 (PiTensorProduct.tprod ℂ x) g := by
      simpa using hmap.lev x
    rw [hw, e', e, hU]
    refine GlobalTheory.T.thetaIntegral_vacuum_intertwines_sphericalHecke R.ψ _ _ _ _ (R.ωY t k) P (hC.chain.ωY t k hkk) _ _ hνH hνF hF cS cT hM _ hvac _ haut.left ?_ ?_
    · intro κ hκ h
      obtain ⟨h1, h2⟩ := (lo (k + 1) hkk).1 κ hκ
      rw [hlev κ h1, h2, one_mul]
    · intro g y hy
      refine hI _ _ R.θ R.ψ _ _ (R.ωY t k) hθ (hC.chain.ωY t k hkk) _ _ hνH hνF _ (rTr _ y (U.1 (PiTensorProduct.tprod ℂ x))) hvac.1
        (GlobalTheory.SphericalOps.isAutFunSm_rTr hy haut) ?_ g
      intro r C hC' μ 𝓕 hμ h𝓕 g'
      simp only [rTr, mul_assoc]
      exact hcusp r C hC' μ 𝓕 hμ h𝓕 (g' * y)
  obtain ⟨φ, x, hx⟩ : ∃ φ x, R.ItY k φ (PiTensorProduct.tprod ℂ x) ≠ 0 := by
    by_contra h
    push_neg at h
    refine (hC.chain.ItY t k hkk).ne (LinearMap.ext fun φ => PiTensorProduct.ext (MultilinearMap.ext fun x => ?_))
    simpa using h φ x
  have h0 := GlobalTheory.multT_eq_zero_of_apply_eq_zero R.θ (R.MY k) _ _ _ _ hθ hμH hμF (hS.1 t k (by omega)) (R.ioY t k U' - w).1 (R.ioY t k U' - w).2 _ hx
    (by simp [key φ x])
  have h1 : (R.ioY t k U').1 = w.1 := sub_eq_zero.1 h0
  rw [h1, hw]

end GlobalTheory.ChainStepHecke
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.realising_polynomial_blockwise_homogeneous : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (i : ℕ) {n : ℕ} (h : (X.Pj i).m + 1 = n) (a : D.what₂.Tau → ℤ) (ν : D.what₂.Tau → Fin n → ℕ) (Q : MvPolynomial (GL3Theta.FrV D n) ℂ) (R : XR (X.Pj i) ℂ), Q ∈ WtPol ℂ ν → Realises X D pos i h a Q R → ∀ m ∈ R.support, ∀ τ, (∑ x : Var (X.Pj i), if (⟨x.1, x.2.1⟩ : Σ v : Fin (X.Pj i).nV, Fin ((X.Pj i).n' v)) = (posJ X D pos i).symm τ then (m x : ℤ) else 0) = (if IsOddPos (pos.symm τ).2 then -1 else 1) * ((∑ r, (ν τ r : ℤ)) - n * a τ) - n * eT X D pos i τ := by
  first | exact @GlobalTheory.TwV.DelA.BlockHom.realises_blockHom | exact GlobalTheory.TwV.DelA.BlockHom.realises_blockHom | (intros; apply GlobalTheory.TwV.DelA.BlockHom.realises_blockHom <;> assumption)
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.numerator_div_denominator_at_complex_point : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (ι : ℂ →+* Kc) (j : ℕ) (hN : RankTie X D j) (d : D.what₂.Tau → Matrix (Fin (D.R.N j)) (Fin (D.R.N (j + 1))) ℂ) (f' : D.what₂.Tau → Matrix (Fin (D.R.N (j + 1))) (Fin (D.R.N (j + 1))) ℂ), (∀ τ, (f' τ).det ≠ 0) → (∀ τ, (dfr X D hN d f' τ).det ≠ 0) → evD X D pos ι hN d f' (numD X Kc j) = evD X D pos ι hN d f' (denD X Kc j) * ι (∏ τ, if IsOddPos (pos.symm τ).2 then (zT X D pos f' τ).det ^ (cT1 X D pos j τ - szT X D pos j τ) * ((zT X D pos f' τ).det ^ (D.R.N j) * sgRev (D.R.N j) * (dfr X D hN d f' τ).det) ^ (cT1 X D pos j τ - (D.R.N j : ℤ) * cT1 X D pos j τ + szT X D pos j τ) else (dfr X D hN d f' τ).det ^ (X.nuv (pos.symm τ).1 (j + 1) (pos.symm τ).2 (NN X.G.P.m X.t j)).toNat) := by
  first | exact @GlobalTheory.TwV.DelA.evD_numD_denD | exact GlobalTheory.TwV.DelA.evD_numD_denD | (intros; apply GlobalTheory.TwV.DelA.evD_numD_denD <;> assumption)
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.substituted_value_at_complex_point_oddBlocks : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (ι : ℂ →+* Kc) (j : ℕ) (hN : RankTie X D j) (Gc : XR (X.Pj j) ℂ) (G : (X.Pj j).Xsp), MvPolynomial.map (algebraMap X.G.Kf Kc) G = MvPolynomial.map ι Gc → OddDeg X j G → ∀ (d : D.what₂.Tau → Matrix (Fin (D.R.N j)) (Fin (D.R.N (j + 1))) ℂ) (f' : D.what₂.Tau → Matrix (Fin (D.R.N (j + 1))) (Fin (D.R.N (j + 1))) ℂ), (∀ τ, (f' τ).det ≠ 0) → (∀ τ, (dfr X D hN d f' τ).det ≠ 0) → evD X D pos ι hN d f' (subD X Kc j G) = ι ((∏ τ, if IsOddPos (pos.symm τ).2 then ((zT X D pos f' τ).det ^ ((D.R.N j : ℤ) - 1) * sgRev (D.R.N j) * (dfr X D hN d f' τ).det) ^ ((D.R.N j : ℤ) * cT1 X D pos j τ - szT X D pos j τ) else 1) * valZ X D pos j (rkS X D hN) Gc (dfr X D hN d f')) := by
  first | exact @GlobalTheory.TwV.DelA.evD_subD | exact GlobalTheory.TwV.DelA.evD_subD | (intros; apply GlobalTheory.TwV.DelA.evD_subD <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.trueChain_complexForms_stabiliser_law : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (l0 : I.Law0 l) (Qp : I.ι → Finset ℕ) (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)), I.StdO l Z Qp O → ∀ u a, GlobalTheory.KerJ.FormsAre ((I.tw l l0 Z).fm u a) (O u a) (GlobalTheory.Pdv.stabStd I l Z u a) := by
  first | exact @GlobalTheory.Pdv.FormsStd.formsAre_stabStd | exact GlobalTheory.Pdv.FormsStd.formsAre_stabStd | (intros; apply GlobalTheory.Pdv.FormsStd.formsAre_stabStd <;> assumption)
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.TwU TensorProduct

theorem _root_.GlobalTheory.T.kernelTheta_relation_of_indicator_relation_split : letI := fun D : D7 => D.host.cmStar; ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ), TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → δ ≠ 0 → TaylorLogMetric.IsChi D χ → B.LatAll → B.VecP χ → B.EqP χ → GL3Theta.modelXi D → GL3Theta.movesCompose D → ∀ (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ), 0 < cl → (∀ Q ∈ SS, Formalism.L2.Col.conjPrime₂ Q ∉ SS) → ∀ (a b : ℕ) (P : HeightOneSpectrum (𝓞 D.host.E)), GL3Theta.SplitP D P → P ∉ SS → Formalism.L2.Col.conjPrime₂ P ∉ SS → ((cl : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal → ((cl : ℕ) : 𝓞 D.host.E) ∉ (Formalism.L2.Col.conjPrime₂ P).asIdeal → ∀ (N₀ : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N₀' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (Ξ : Formalism.L2.Col.HomE D.host.E a b → ℂ), TaylorLogMetric.admitted D a b N₀ N₀' → DatLoc D cc SS cl N₀ N₀' Ξ → ∀ (ι : Type) [Fintype ι] (N : ι → Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : ι → Submodule (𝓞 D.host.E) (Fin b → D.host.E)), (∀ i, TaylorLogMetric.admitted D a b (N i) (N' i) ∧ GL3Theta.EqOff D P (N i) N₀ ∧ GL3Theta.EqOff D P (N' i) N₀') → ∀ c : ι → ℂ, (∑ i, c i • Set.indicator (GL3Theta.YP D P (N i) (N' i) : Set (Matrix (Fin b) (Fin a) (GL3Theta.EP D P))) (1 : Matrix (Fin b) (Fin a) (GL3Theta.EP D P) → ℂ)) = 0 → ∀ z, ∑ i, c i * (((Real.sqrt (GL3Theta.volP (GL3Theta.YP D P N₀ N₀') (GL3Theta.YP D P (N i) (N' i))) : ℝ) : ℂ) * (Base.chiFac χ a b (N i) (N' i))⁻¹ * kerTh B χ SS cl (N i) (N' i) Ξ z) = 0 := by
  first | exact @GlobalTheory.KerRel.kerTh_relation_of_indicator | exact GlobalTheory.KerRel.kerTh_relation_of_indicator | (intros; apply GlobalTheory.KerRel.kerTh_relation_of_indicator <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial

theorem _root_.GlobalTheory.T.exists_pos_classSum_eq_mul_invariantForm : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n) (β : a.W →ₗ⋆[ℂ] a.W →ₗ[ℂ] ℂ), GlobalTheory.CoefDuty.IsInvForm a β → ∃ B, GlobalTheory.CoefDuty.IsPetersson a B ∧ ∀ (J : Subgroup (GAf L n)) (χ : J →* ℂˣ) (T : Finset (GAf L n)), GlobalTheory.CoefDuty.IsBounded J → (∃ N : ℕ, 0 < N ∧ ∀ κ, NG.Cong L n N κ → ∃ h : κ ∈ J, χ ⟨κ, h⟩ = 1) → GlobalTheory.CoefDuty.IsClassReps J T → ∃ c : ℝ, 0 < c ∧ ∀ f ∈ NG.TypeSp a.ρ J χ, ∀ f' ∈ NG.TypeSp a.ρ J χ, GlobalTheory.CoefDuty.classSum a β J T f f' = (c : ℂ) * B f f' := by
  first | exact @GlobalTheory.petersson_form_classSum_comparison | exact GlobalTheory.petersson_form_classSum_comparison | (intros; apply GlobalTheory.petersson_form_classSum_comparison <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelA

theorem twPoly_main : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) {n : ℕ} (ν : D.what₂.Tau → Fin n → ℕ) (c : D.what₂.Tau → ℤ), (∀ τ r, (ν τ r : ℤ) ≤ c τ) → ∀ Q : MvPolynomial (GL3Theta.FrV D n) ℂ, Q ∈ WtPol ℂ ν → ∃ R : MvPolynomial (GL3Theta.FrV D n) ℂ, ∀ f : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ, (∀ τ, (f τ).det ≠ 0) → GL3Theta.evFr D R (zT X D pos f) = (∏ τ, if IsOddPos (pos.symm τ).2 then (f τ).det ^ (-(c τ)) else 1) * GL3Theta.evFr D Q f := by
  intro p _ X D pos n ν c hc Q hQ
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨Q, fun f _ => ?_⟩
    have h0 : zT X D pos f = f := funext fun τ => Subsingleton.elim _ _
    rw [h0]
    simp [Matrix.det_fin_zero]
  · obtain ⟨K, P, hP⟩ := GlobalTheory.T.oddTwistedFrameDetFunction_mul_det_pow_polynomial X D pos hn ν c hc Q hQ
    obtain ⟨R, hR⟩ := Formalism.L2.KerInert.SharpPolyP.sp_main
      (fun τ r => if IsOddPos (pos.symm τ).2 then (c τ - (ν τ (Fin.rev r) : ℤ)).toNat else ν τ r)
      (twF X D pos c Q) (fun x β hx hβ => GlobalTheory.T.oddTwistedFrameDetFunction_mul_upper_triangular X D pos ν c hc Q hQ x β hx hβ) _ K P rfl hP
    refine ⟨R, fun f hf => ?_⟩
    have hz : ∀ τ, (zT X D pos f τ).det ≠ 0 := by
      intro τ
      rw [det_zT]
      split_ifs
      · exact mul_ne_zero (sgRev_ne_zero n) (inv_ne_zero (hf τ))
      · exact hf τ
    have h1 := hR (zT X D pos f) hz
    rw [show GL3Theta.evFr D R (zT X D pos f) = MvPolynomial.eval (Formalism.L2.KerInert.SharpPolyP.pt (zT X D pos f)) R from rfl,
      ← h1, twF, zT_zT X D pos f hf]

end GlobalTheory.TwV.DelA
end
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.latticeTupleFrame_scalar_oddPositions_det : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (Kc : Type) [Field Kc] [Algebra (Formalism.MainNotions.FormalGroupSystem.K0 p) Kc] [Algebra X.G.Kf Kc] (ι : ℂ →+* Kc) (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v), PosTie X D pos Kc ι ρ → ∀ (fd : FData X D) (c : Kc), c ≠ 0 → ∀ (j : ℕ) (hN : RankTie X D j) (La' : X.Lt (j + 1)) (M : GL (Fin (D.R.N (j + 1))) D.host.E), StdU D M → FrIs fd ρ (j + 1) La' (rkT X D hN) M → ∀ (ν : D.what₂.Tau → Fin (D.R.N j) → ℕ), NuIs X D pos j ν → GlobalTheory.FrameB.sS X Kc j (GlobalTheory.FrameB.kV Kc fd c j La') * GlobalTheory.FrameB.kN X Kc j (GlobalTheory.FrameB.wV Kc fd c j La') (GlobalTheory.FrameB.kV Kc fd c j La') * (GlobalTheory.FrameB.kD X Kc j (GlobalTheory.FrameB.wV Kc fd c j La') (GlobalTheory.FrameB.kV Kc fd c j La'))⁻¹ = ∏ τ, if IsOddPos (pos.symm τ).2 then c ^ szT X D pos j τ * ι (embT D τ (M : Matrix (Fin (D.R.N (j + 1))) (Fin (D.R.N (j + 1))) D.host.E).det) ^ cT1 X D pos j τ else 1 := by
  first | exact @GlobalTheory.TwV.DelA.scal_tauV | exact GlobalTheory.TwV.DelA.scal_tauV | (intros; apply GlobalTheory.TwV.DelA.scal_tauV <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.sphericalThetaCorrespondence_inertPlace_of_howe : HoweUnram → ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (P : Pl D.host.E), IsWeilDatumO ψ S T χS χT om → _root_.Formalism.DivisionValues.conjPl P = P → VacFix ψ om P → SphCorr ψ om P := by
  first | exact @GlobalTheory.Hk3.CorrInert.sphCorr_of_inert | exact GlobalTheory.Hk3.CorrInert.sphCorr_of_inert | (intros; apply GlobalTheory.Hk3.CorrInert.sphCorr_of_inert <;> assumption)
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.CuspRep GlobalTheory.PRep

theorem _root_.GlobalTheory.T.exists_algebraicForm_weight_level_smooth_at_place : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (lam : (E →+* ℂ) → DomWeight n) (K : Subgroup (UA E n)) (U : Submodule ℂ (UA E n → ℂ)), K ≤ finU (E := E) (n := n) → OfType lam K U → ∀ w₀ : HeightOneSpectrum (𝓞 E), ∃ (W : Wt E n) (f : algForms W), (∀ τ, W.at τ = lam τ) ∧ f ≠ 0 ∧ (∀ v, f.1 v ∈ U) ∧ (∀ k ∈ K, ∀ v g, f.1 v (g * k) = f.1 v g) ∧ ∃ N ∈ nhds (1 : GL (Fin n) (w₀.adicCompletion E)), ∀ x ∈ locU n w₀, cLoc w₀ x ∈ N → ∀ v g, f.1 v (g * x) = f.1 v g := by
  first | (exact @GlobalTheory.Cong.exists_algForm_ofType) | (exact GlobalTheory.Cong.exists_algForm_ofType) | (intros; apply GlobalTheory.Cong.exists_algForm_ofType  <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Col2 GlobalTheory.TopStep

namespace GlobalTheory.TopStep

theorem ext_mem_twisted_k1_level : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E)),
    ((qOf P : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2 → ∀ {N n : ℕ} (hN : N = n + 1) (r b c : ℕ), n = r + b →
    ∀ j : GLint E n P, redGL n P j ∈ HQ (𝓞 E ⧸ P.asIdeal) n r b → extI hN P j ∈ twK1H P N r c := by
  intro E _ _ _ P hq N n hN r b c hn j h
  subst hN
  have hent : ∀ k : GLint E n P, redGL n P k ∈ HQ (𝓞 E ⧸ P.asIdeal) n r b →
      ∀ a l : Fin n, a.1 < r → r ≤ l.1 → IntAt P (k.1 (Pi.single a 1) l / (qOf P : E)) := by
    intro k hk a l ha hl
    have h0 : redP P (k.1 (Pi.single a 1) l) = 0 := by
      have := twTQ_HQ_entry hk ha hl
      rwa [redGL_val] at this
    exact intAt_div_of_redP hq (glint_entry k l a) h0
  refine mem_kOne_of_block P (n := n + 1) (r := r) (c := c) (by omega) (extI rfl P j) (j.1 : Sp E n ≃ₗ[E] Sp E n) ?_ ?_ ?_
  · intro x l
    rw [extI_val]
    by_cases hl : l.1 < n
    · rw [dite_eq_left (show l.1 < n + 1 - 1 by omega)]
      have := congrFun (prH_sumE rfl j.1 1 x) ⟨l.1, hl⟩
      exact this
    · rw [dite_eq_right (show ¬ l.1 < n + 1 - 1 by omega)]
      have e : l = Br.iL (rfl : n + 1 = n + 1) := Fin.ext (by have := l.2; show l.1 = n; omega)
      subst e
      rw [sumE_last, Units.val_one, one_mul]
  · exact fun a l ha hl => hent j h a l ha hl
  · intro a l ha hl
    have := hent j⁻¹ (by rw [map_inv]; exact inv_mem h) a l ha hl
    exact this

end GlobalTheory.TopStep
end
