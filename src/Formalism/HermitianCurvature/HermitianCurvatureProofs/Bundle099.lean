module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle024
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.MulVecBvecApply
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle026
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving
import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle038
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.MatExtMulVec
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SubMulRight
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle070
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerFlagSplitting.MulVecColOfMul
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle027
public import Formalism.HermitianCurvature.Bundle004
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.BesselUnipotentEquivHolds
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.BesselUnitaryEquivHolds
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationInvarianceEverySetting
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LUFactorOrbitBounds
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle029
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle087
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle057
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ActualAdjointnessFromHermitian
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle092
public import Formalism.HermitianCurvature.StatementQr
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.AlgebraicQuantumDeterminant
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle073
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CapelliCoordinates
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.FrameEntries
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LeftDerivativeCurves
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.QuantumMinorCommutation
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.QuantumMinorExpansion
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle061

@[expose] public section

section

open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.LeftFubiniLemmas

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

def CoreLF : Prop :=
  ∀ (k p m n : ℕ) (e : p + m = n), 1 ≤ p → ∀ (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ), (∀ i, d i ≠ 0) →
    ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (Bj : B.RealPlaceData k m Wp Wq) (B0 : B.RealPlaceData k n Wp Wq),
    D.castV e (liftVec k p m Bj.z) = B0.z → D.castV e (liftVec k p m Bj.z') = B0.z' →
    (∀ y : B.Mat k m, Bj.π' y = B0.π' (D.castM e (ιLev k p m y))) →
    Bj.μW' Set.univ = 1 → B0.μW' = Bj.μW'.map (Formalism.FourierDecayAlt.P.PBM.levMt p m e) →
    Bj.μN = D.muN k m → B0.μN = D.muN k n →
    ∃ (X : Type) (_ : MeasurableSpace X) (μ : Measure X)
      (ℓ : X → ((Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp))) (sx : X → B.Mat k n),
      (∀ x, sx x ∈ Sset k n B0.z) ∧
      ∀ g ∈ JF.Om k m Bj.z Bj.z', ∀ H : B.Mat k n → (Wq →L[ℂ] Wp),
        ContinuousOn H {x | x ∈ B.GV k n ∧ Dmin k n B0.z B0.z' x ⟨p, by omega⟩ ≠ 0} →
        (∃ R : ℝ, ∀ x ∈ B.GV k n, H x ≠ 0 → B.gN x ≤ R) →
        Integrable (fun x => ℓ x (PBG.Kr B0 H (sx x * D.castM e (U.mMap k p m (U.hMat σ d) g)))) μ ∧
        B.JF Bj (U.PhiFun (s := 0) k m σ d (D.castV e.symm B0.z) (D.castV e.symm B0.z') (D.castF e H)
            (fun a => a.elim0)) g =
          ∫ x, ℓ x (PBG.Kr B0 H (sx x * D.castM e (U.mMap k p m (U.hMat σ d) g))) ∂μ

end Formalism.FourierDecayAlt.P.LeftFubiniLemmas
end
end

section

namespace Formalism.FourierDecayAlt.P.StabilizerDisintegration.OD

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ComplexConjugate

noncomputable section

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

abbrev RR (k r : ℕ) (w : Equiv.Perm (Fin (r + 1))) : Type :=
  (Mt k r × ((C2.LPidx w → ℂ) × Mt k r)) × (Mt k r × ((G.UT (r + 1) → ℂ) × Mt k r))

section defs

variable (S : B.RealPlaceData k r Wp Wq) (γ : B.Mat k r) (w : Equiv.Perm (Fin (r + 1)))
  (e : ((C2.Lstidx w → ℂ) × (C2.LPidx w → ℂ)) ≃ᵐ (G.UT (r + 1) → ℂ))

def Xi (x : C2.Lstidx w → ℂ) (q : RR k r w) : B.SS k r :=
  ((q.1.1, Matrix.of.symm (C2.tauM k r S.z (G.upper (e (x, q.1.2.1))) * Matrix.of q.1.2.2)),
   (q.2.1, Matrix.of.symm (C2.tauM k r S.z' (G.upper q.2.2.1) * Matrix.of q.2.2.2)))

def Xi0 (q : RR k r w) : B.SS k r :=
  ((q.1.1, Matrix.of.symm (C2.tauM k r S.z (lowP w q.1.2.1)ᴴ * Matrix.of q.1.2.2)),
   (q.2.1, Matrix.of.symm (C2.tauM k r S.z' (G.upper q.2.2.1) * Matrix.of q.2.2.2)))

def rhoX (x : C2.Lstidx w → ℂ) : B.Mat k r := Dx2.Rad.rhoF S γ w x

def rhoP (x : C2.Lstidx w → ℂ) : B.Mat k r := γ⁻¹ * (rhoX S γ w x)⁻¹ * γ

def m0L (x : C2.Lstidx w → ℂ) (y : C2.LPidx w → ℂ) : B.Mat k r :=
  (C2.tauM k r S.z (lowP w y)ᴴ)⁻¹ * (rhoX S γ w x)⁻¹ * C2.tauM k r S.z (G.upper (e (x, y)))

def m0R (x : C2.Lstidx w → ℂ) (u : G.UT (r + 1) → ℂ) : B.Mat k r :=
  (C2.tauM k r S.z' (C2.uMap k r S.z' (rhoP S γ w x) * G.upper u))⁻¹ * rhoP S γ w x * C2.tauM k r S.z' (G.upper u)

def Tx (x : C2.Lstidx w → ℂ) (q : RR k r w) : RR k r w :=
  ((q.1.1, (q.1.2.1, Matrix.of.symm (m0L S γ w e x q.1.2.1 * Matrix.of q.1.2.2))),
   (q.2.1, (utc (C2.uMap k r S.z' (rhoP S γ w x) * G.upper q.2.2.1),
     Matrix.of.symm (m0R S γ w x q.2.2.1 * Matrix.of q.2.2.2))))

def nuR (μ0 μ0' : Measure (Mt k r)) : Measure (RR k r w) :=
  (S.μW.prod ((volume : Measure (C2.LPidx w → ℂ)).prod μ0)).prod
    (S.μW'.prod ((volume : Measure (G.UT (r + 1) → ℂ)).prod μ0'))

def Tt (p : (C2.Lstidx w → ℂ) × RR k r w) : (C2.Lstidx w → ℂ) × RR k r w := (p.1, Tx S γ w e p.1 p.2)

end defs

section alg

variable (S : B.RealPlaceData k r Wp Wq) {γ : B.Mat k r} (hγ : γ ∈ B.GV k r) {w : Equiv.Perm (Fin (r + 1))}
  {d : Fin (r + 1) → ℂ} (hd : ∀ a, d a ≠ 0) (hZw : Zhat k r S.z S.z' γ = C2.monoP w d)
  (hpos : 0 < Gf k r S.z S.z' γ)
  (e : ((C2.Lstidx w → ℂ) × (C2.LPidx w → ℂ)) ≃ᵐ (G.UT (r + 1) → ℂ))
  (he : ∀ p, G.upper (e p) = (lowS w p.1)ᴴ * (lowP w p.2)ᴴ)

include hγ hd hZw hpos in
theorem good : Dx2.Rad.Good S γ w d :=
  ⟨fun x => Dx2.Rad.exists_rho S hγ hpos hd hZw x, Dx2.Rad.u_inj S hγ hpos hd hZw,
    fun _ hρ => Dx2.Rad.u_lstg S hγ hpos hd hZw hρ⟩

include hγ hd hZw hpos in
theorem rhoX_spec (x : C2.Lstidx w → ℂ) :
    rhoX S γ w x ∈ C6.Rset γ ∧ C2.uMap k r S.z (rhoX S γ w x) = (lowS w x)ᴴ := by
  have h := Dx2.Rad.exists_rho S hγ hpos hd hZw x
  have e1 : rhoX S γ w x = h.choose := by
    show Formalism.FourierDecayAlt.D.rhoOfU S γ (Dx2.Rad.low w x)ᴴ = _
    unfold Formalism.FourierDecayAlt.D.rhoOfU
    rw [dite_eq_left h]
  rw [e1, UC.lowS_eq_low]
  exact h.choose_spec

include hγ hd hZw hpos in
theorem rhoP_N (x : C2.Lstidx w → ℂ) : rhoP S γ w x ∈ Nset k r := by
  have h1 := (rhoX_spec S hγ hd hZw hpos x).1
  have hu := PI.StabSplit.GV_unit k r hγ
  have e : rhoP S γ w x = (γ⁻¹ * rhoX S γ w x * γ)⁻¹ := by
    unfold rhoP
    simp only [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hu, mul_assoc]
  rw [e]
  exact Formalism.QuantumDeterminants.WeylGroupFacts.mem_n_inv h1.2

theorem lowPH_UT (y : C2.LPidx w → ℂ) : (lowP w y)ᴴ ∈ C2.UTset (r + 1) :=
  UC.LT_ct (UC.lowerUnipotent_mem w y).1

theorem lowSH_UT (x : C2.Lstidx w → ℂ) : (lowS w x)ᴴ ∈ C2.UTset (r + 1) :=
  UC.LT_ct (UC.lowS_mem w x).1

include he in
theorem upper_e_UT (p : (C2.Lstidx w → ℂ) × (C2.LPidx w → ℂ)) : G.upper (e p) ∈ C2.UTset (r + 1) := by
  rw [he p]
  exact UC.prod_UT w p

include hγ hd hZw hpos he in
theorem left_stabilizer_mem (x : C2.Lstidx w → ℂ) (y : C2.LPidx w → ℂ) : m0L S γ w e x y ∈ C2.N0set k r S.z := by
  have hz : C2.StdZ k r S.z := ⟨S.z_mem, S.T_pos⟩
  have hUF := Formalism.FourierDecayAlt.P.unipotent_map_frame k r S.z hz
  obtain ⟨hρR, hρu⟩ := rhoX_spec S hγ hd hZw hpos x
  have hτv := A.tau_N hz (lowPH_UT y)
  have hτe := A.tau_N hz (upper_e_UT e he (x, y))
  have h1 : (C2.tauM k r S.z (lowP w y)ᴴ)⁻¹ ∈ Nset k r := WeylGroupFacts.mem_n_inv hτv
  have h2 : (rhoX S γ w x)⁻¹ ∈ Nset k r := WeylGroupFacts.mem_n_inv hρR.1
  have hN : m0L S γ w e x y ∈ Nset k r := WeylGroupFacts.mem_n_mul (WeylGroupFacts.mem_n_mul h1 h2) hτe
  refine ⟨hN, ?_⟩
  unfold m0L
  rw [(hUF.1 _ (A.n_in_S (WeylGroupFacts.mem_n_mul h1 h2))).2.2 _ (A.n_in_S hτe),
    (hUF.1 _ (A.n_in_S h1)).2.2 _ (A.n_in_S h2), A.uMap_inv hz hτv, A.uMap_inv hz hρR.1, hρu,
    (Formalism.FourierDecayAlt.P.c2_tau_mem k r S.z hz _ (lowPH_UT y)).2.2,
    (Formalism.FourierDecayAlt.P.c2_tau_mem k r S.z hz _ (upper_e_UT e he (x, y))).2.2, he]
  calc ((lowP w y)ᴴ).adjugate * ((lowS w x)ᴴ).adjugate * ((lowS w x)ᴴ * (lowP w y)ᴴ)
      = ((lowP w y)ᴴ).adjugate * (((lowS w x)ᴴ).adjugate * (lowS w x)ᴴ) * (lowP w y)ᴴ := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by
        rw [Matrix.adjugate_mul, A.det_UT (lowSH_UT x), one_smul, Matrix.mul_one, Matrix.adjugate_mul,
          A.det_UT (lowPH_UT y), one_smul]

include hγ hd hZw hpos in
theorem uP_UT (x : C2.Lstidx w → ℂ) (u : G.UT (r + 1) → ℂ) :
    C2.uMap k r S.z' (rhoP S γ w x) * G.upper u ∈ C2.UTset (r + 1) := by
  have hz' : C2.StdZ k r S.z' := ⟨S.z'_mem, S.T'_pos⟩
  have hUF := Formalism.FourierDecayAlt.P.unipotent_map_frame k r S.z' hz'
  have hρ := rhoP_N S hγ hd hZw hpos x
  have hτ := A.tau_N hz' (UC.upper_mem u)
  rw [← (Formalism.FourierDecayAlt.P.c2_tau_mem k r S.z' hz' _ (UC.upper_mem u)).2.2,
    ← (hUF.1 _ (A.n_in_S hρ)).2.2 _ (A.n_in_S hτ)]
  exact (hUF.1 _ (A.n_in_S (WeylGroupFacts.mem_n_mul hρ hτ))).2.1

include hγ hd hZw hpos in
theorem right_stabilizer_mem (x : C2.Lstidx w → ℂ) (u : G.UT (r + 1) → ℂ) : m0R S γ w x u ∈ C2.N0set k r S.z' := by
  have hz' : C2.StdZ k r S.z' := ⟨S.z'_mem, S.T'_pos⟩
  have hUF := Formalism.FourierDecayAlt.P.unipotent_map_frame k r S.z' hz'
  have hρ := rhoP_N S hγ hd hZw hpos x
  have hτa := A.tau_N hz' (uP_UT S hγ hd hZw hpos x u)
  have hτ := A.tau_N hz' (UC.upper_mem u)
  have h1 := WeylGroupFacts.mem_n_inv hτa
  have hN : m0R S γ w x u ∈ Nset k r := WeylGroupFacts.mem_n_mul (WeylGroupFacts.mem_n_mul h1 hρ) hτ
  refine ⟨hN, ?_⟩
  unfold m0R
  rw [(hUF.1 _ (A.n_in_S (WeylGroupFacts.mem_n_mul h1 hρ))).2.2 _ (A.n_in_S hτ),
    (hUF.1 _ (A.n_in_S h1)).2.2 _ (A.n_in_S hρ), A.uMap_inv hz' hτa,
    (Formalism.FourierDecayAlt.P.c2_tau_mem k r S.z' hz' _ (uP_UT S hγ hd hZw hpos x u)).2.2,
    (Formalism.FourierDecayAlt.P.c2_tau_mem k r S.z' hz' _ (UC.upper_mem u)).2.2, Matrix.mul_assoc,
    Matrix.adjugate_mul, A.det_UT (uP_UT S hγ hd hZw hpos x u), one_smul]


include hγ hd hZw hpos he in
theorem Xi_eq (x : C2.Lstidx w → ℂ) (q : RR k r w) :
    Xi S w e x q = C6.actR γ (rhoX S γ w x) (Xi0 S w (Tx S γ w e x q)) := by
  have hz : C2.StdZ k r S.z := ⟨S.z_mem, S.T_pos⟩
  have hz' : C2.StdZ k r S.z' := ⟨S.z'_mem, S.T'_pos⟩
  have hρ := (rhoX_spec S hγ hd hZw hpos x).1
  have hρu : IsUnit (rhoX S γ w x).det := PI.StabSplit.GV_unit k r hρ.1.1
  have hγu : IsUnit γ.det := PI.StabSplit.GV_unit k r hγ
  have hA : IsUnit (C2.tauM k r S.z (lowP w q.1.2.1)ᴴ).det :=
    PI.StabSplit.GV_unit k r (A.tau_N hz (lowPH_UT q.1.2.1)).1
  have hM := uP_UT S hγ hd hZw hpos x q.2.2.1
  have hB : IsUnit (C2.tauM k r S.z' (C2.uMap k r S.z' (rhoP S γ w x) * G.upper q.2.2.1)).det :=
    PI.StabSplit.GV_unit k r (A.tau_N hz' hM).1
  simp only [Xi, Xi0, Tx, C6.actR, Equiv.apply_symm_apply, UC.upper_utc hM, m0L, m0R, ← mul_assoc,
    Matrix.mul_nonsing_inv_cancel_right _ _ hA, Matrix.mul_nonsing_inv_cancel_right _ _ hB,
    Matrix.mul_nonsing_inv _ hρu]
  simp only [rhoP, ← mul_assoc, Matrix.mul_nonsing_inv_cancel_right _ _ hρu,
    Matrix.mul_nonsing_inv_cancel_right _ _ hγu, Matrix.nonsing_inv_mul _ hγu, one_mul]

end alg

end

end Formalism.FourierDecayAlt.P.StabilizerDisintegration.OD
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

namespace Formalism.FourierDecayAlt.P.CutMP.Gr

open NumberField

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section thr

end thr

section jf

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

theorem jf_mem_FFlM [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (A : ℝ) (m : ℕ)
    (F : B.Mat k r → (Wq →L[ℂ] Wp)) (hT : JF.TransportedAlt k r A m) (hF : B.InCC A m F) :
    B.JF D F ∈ FFlM (m : ℕ∞) k r D.z D.z' D.π D.π' 0 (Q.OmPlus k r D.z D.z') := by
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarW
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarN
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarW'
  have hN := Formalism.QuantumDeterminants.bessel_unipotent_equiv_holds Wp Wq k r D.z D.z' cStd D.π D.π' D.μW D.μN D.μW' F D.z_mem D.z'_mem
    D.haarN.conc (fun n₀ h => D.haarN.left n₀ h)
  have hW := Formalism.FourierDecayAlt.P.bessel_words_of_domain Formalism.FourierDecayAlt.P.bessel_integral_domain
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g₀ hg₀
    obtain ⟨U, F', hU, hgU, hc, he⟩ := (hW k r Wp Wq D A m F hT hF).1 g₀ hg₀
    exact ⟨U, F', hU, hgU, hc, he⟩
  · intro g _ n hn
    have e := hN g n hn.1 1 WeylGroupFacts.mem_n_one
    rw [Matrix.mul_one, Formalism.FourierDecayAlt.P.BesselCapelliCommutation.psi_one D.z'_mem, mul_one] at e
    exact e
  · intro g _ n hn
    have e := hN g 1 WeylGroupFacts.mem_n_one n hn.1
    rw [Matrix.one_mul, Formalism.FourierDecayAlt.P.BesselCapelliCommutation.psi_one D.z_mem, one_mul] at e
    exact e
  · intro g _ h hh h' hh'
    exact Formalism.QuantumDeterminants.bessel_unitary_equiv_holds Wp Wq k r D.z D.z' cStd D.π D.π' D.μW D.μN D.μW' F D.z_mem D.z'_mem
      D.haarN.conc D.haarW.conc D.haarW'.conc (fun h₀ hh₀ => D.haarW.left h₀ hh₀) (fun h₀ hh₀ => D.haarW'.left h₀ hh₀)
      (Formalism.FourierDecayAlt.P.conjugation_invariance_every_setting k r Wp Wq D) D.π_rep D.π'_rep g h hh h' hh'

end jf

end

end Formalism.FourierDecayAlt.P.CutMP.Gr
end

section

open MeasureTheory Filter Topology Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.ParameterFamilyAlgebra

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section Act

variable {k ρ : ℕ} {z z' : Fin (2 * ρ + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] {π : Q.Mx k ρ → (Wp →L[ℂ] Wp)}
  {π' : Q.Mx k ρ → (Wq →L[ℂ] Wq)}

theorem rad_zero (Φ : Q.RadSp k ρ z z' π π') {x : (Fin ρ → ℂ) × Q.Mx k ρ} (hx : x ∉ Q.DomR k ρ z z') :
    (Φ : Q.Fn k ρ (Wq →L[ℂ] Wp)) x.1 x.2 = 0 := Φ.2.1 x hx

theorem one_mem_OmX : (fun _ => (1 : ℂ)) ∈ OmX ρ := fun _ => one_ne_zero

theorem good_fn (hT : 0 ≤ Tz k ρ z * Tz k ρ z') (X : Q.ActualOps k ρ z z' π π') (j : Fin 6) :
    Good z z' π π' (X.fn j) := by
  intro Par _ _ _ _ _ U₀ hU₀ hUpos Ψ Ψf hR hF
  set Φf : Par → Mt k ρ → (Wq →L[ℂ] Wp) := fun Z y =>
    if 0 < Q.GGl k ρ z z' (Matrix.of y) then Q.fnVal k ρ z z' j (Matrix.of y) • Ψf Z y else 0 with hΦf

  have key : ∀ (Φ : Q.RadSp k ρ z z' π π') (c : Fin ρ → ℂ) (y : Mt k ρ),
      Matrix.of y ∈ Q.Glev k ρ (Fin.last ρ) → 0 < Q.GGl k ρ z z' (Matrix.of y) →
      (X.fn j Φ : Q.Fn k ρ (Wq →L[ℂ] Wp)) c (Matrix.of y) =
        Q.fnVal k ρ z z' j (Matrix.of y) • (Φ : Q.Fn k ρ (Wq →L[ℂ] Wp)) c (Matrix.of y) := by
    intro Φ c y hG hpos
    by_cases hD : ((c, Matrix.of y) : (Fin ρ → ℂ) × Q.Mx k ρ) ∈ Q.DomR k ρ z z'
    · exact X.fn_apply j Φ (c, Matrix.of y) hD
    · rw [rad_zero (X.fn j Φ) hD, rad_zero Φ hD, smul_zero]
  have key0 : ∀ (Φ : Q.RadSp k ρ z z' π π') (c : Fin ρ → ℂ) (y : Mt k ρ),
      ¬ 0 < Q.GGl k ρ z z' (Matrix.of y) → (X.fn j Φ : Q.Fn k ρ (Wq →L[ℂ] Wp)) c (Matrix.of y) = 0 := by
    intro Φ c y hpos
    exact rad_zero (X.fn j Φ) (x := (c, Matrix.of y)) (fun hD => hpos hD.2.2)
  refine ⟨Φf, fun Z c y hG => ?_, ?_, fun K hK q hq hG hqK => ?_, ?_⟩
  · by_cases hpos : 0 < Q.GGl k ρ z z' (Matrix.of y)
    · rw [key (Ψ Z) c y hG hpos, hR Z c y hG, hΦf]
      simp only [if_pos hpos]
    · rw [key0 (Ψ Z) c y hpos, hΦf]
      simp only [if_neg hpos]
  · intro q₀ hq hG
    obtain ⟨U, F, hU, hqU, hFs, hfF⟩ := hF q₀ hq hG
    have hfn := Formalism.FourierDecayAlt.P.Qx5.fnVal_contDiffOn (z := z) (z' := z') (k := k) (r := ρ) hT j
    have hm : ContDiff ℝ ∞ fun q : Par × Mt k ρ =>
        (((fun _ => (1 : ℂ)), (Matrix.of q.2 : Q.Mx k ρ)) : (Fin ρ → ℂ) × Q.Mx k ρ) :=
      contDiff_const.prodMk contDiff_snd
    refine ⟨U ∩ U₀, fun q => Q.fnVal k ρ z z' j (Matrix.of q.2) • F q, hU.inter hU₀, ⟨hqU, hq⟩, ?_, ?_⟩
    · refine ContDiffOn.smul (hfn.comp hm.contDiffOn (fun q hq' => ?_)) (hFs.mono Set.inter_subset_left)
      exact ⟨one_mem_OmX, (hUpos hq'.2).2⟩
    · intro q hq' hG'
      have hpos : 0 < Q.GGl k ρ z z' (Matrix.of q.2) := (hUpos hq'.2).2
      show Φf q.1 q.2 = _
      rw [hΦf]
      simp only [if_pos hpos]
      rw [show Ψf q.1 q.2 = F q from hfF q hq'.1 hG']
  · have hpos : 0 < Q.GGl k ρ z z' (Matrix.of q.2) := (hUpos hq).2
    rw [hΦf]
    simp only [if_pos hpos]
    rw [hK q hG (fun h => hqK (subset_closure h)), smul_zero]
  · intro ν _ Kp hKp hν Ψi y V hV hyV hyG hKV hi c
    by_cases hpos : 0 < Q.GGl k ρ z z' (Matrix.of y)
    · rw [key Ψi c y hyG hpos, hi c y hyV hyG, ← integral_smul]
      refine integral_congr_ae (ae_of_all _ fun Z => ?_)
      rw [hΦf]
      simp only [if_pos hpos]
    · rw [key0 Ψi c y hpos]
      have : (fun Z => Φf Z y) = fun _ => 0 := by
        funext Z
        rw [hΦf]
        simp only [if_neg hpos]
      rw [this, integral_zero]

theorem good_alt_bis (hOm : ∀ c : Fin ρ → ℂ, c ∈ OmX ρ) (hS : ∀ c c' : Fin ρ → ℂ, c = c')
    (X : Q.ActualOps k ρ z z' π π') (Y : ℂ) (a b : Fin 2) : Good z z' π π' (X.t Y a b) := by
  intro Par _ _ _ _ _ U₀ hU₀ hUpos Ψ Ψf hR hF
  set c₁ : Fin ρ → ℂ := fun _ => 1 with hc₁
  set f : Par → Q.Mx k ρ → (Wq →L[ℂ] Wp) := fun Z => (Ψ Z : Q.Fn k ρ (Wq →L[ℂ] Wp)) c₁ with hfdef
  have hf : PBI.ParFam k ρ U₀ (fun q => f q.1 (Matrix.of q.2)) :=
    parFam_congr hF (fun q _ hG => (hR q.1 c₁ q.2 hG).symm) hU₀
  obtain ⟨a1, b1, c1⟩ := parOK_tL (E := Wq →L[ℂ] Wp) z z' Y a b Par U₀ hU₀ f hf
  set Φf : Par → Mt k ρ → (Wq →L[ℂ] Wp) := fun Z y =>
    if 0 < Q.GGl k ρ z z' (Matrix.of y) then tL k ρ z z' (Fin.last ρ) Y a b (f Z) (Matrix.of y) else 0 with hΦf
  have key : ∀ (Φ : Q.RadSp k ρ z z' π π') (y : Mt k ρ),
      Matrix.of y ∈ Q.Glev k ρ (Fin.last ρ) → 0 < Q.GGl k ρ z z' (Matrix.of y) →
      (X.t Y a b Φ : Q.Fn k ρ (Wq →L[ℂ] Wp)) c₁ (Matrix.of y) =
        tL k ρ z z' (Fin.last ρ) Y a b ((Φ : Q.Fn k ρ (Wq →L[ℂ] Wp)) c₁) (Matrix.of y) := by
    intro Φ y hG hpos
    exact X.t_apply Y a b Φ (c₁, Matrix.of y) ⟨hOm c₁, hG, hpos⟩
  have key0 : ∀ (Φ : Q.RadSp k ρ z z' π π') (c : Fin ρ → ℂ) (y : Mt k ρ),
      ¬ 0 < Q.GGl k ρ z z' (Matrix.of y) → (X.t Y a b Φ : Q.Fn k ρ (Wq →L[ℂ] Wp)) c (Matrix.of y) = 0 := by
    intro Φ c y hpos
    exact rad_zero (X.t Y a b Φ) (x := (c, Matrix.of y)) (fun hD => hpos hD.2.2)
  refine ⟨Φf, fun Z c y hG => ?_, ?_, fun K hK q hq hG hqK => ?_, ?_⟩
  · rw [hS c c₁]
    by_cases hpos : 0 < Q.GGl k ρ z z' (Matrix.of y)
    · rw [key (Ψ Z) y hG hpos, hΦf]
      simp only [if_pos hpos]
      rfl
    · rw [key0 (Ψ Z) c₁ y hpos, hΦf]
      simp only [if_neg hpos]
  · exact parFam_congr a1 (fun q hq _ => by
      have hpos : 0 < Q.GGl k ρ z z' (Matrix.of q.2) := (hUpos hq).2
      show _ = Φf q.1 q.2
      rw [hΦf]
      simp only [if_pos hpos]) hU₀
  · have hpos : 0 < Q.GGl k ρ z z' (Matrix.of q.2) := (hUpos hq).2
    rw [hΦf]
    simp only [if_pos hpos]
    refine b1 q hq hG (closure K)ᶜ isClosed_closure.isOpen_compl hqK (fun q' hq' hG' => ?_)
    show (Ψ q'.1 : Q.Fn k ρ (Wq →L[ℂ] Wp)) c₁ (Matrix.of q'.2) = 0
    rw [hR q'.1 c₁ q'.2 hG']
    exact hK q' hG' (fun h => hq' (subset_closure h))
  · intro ν _ Kp hKp hν Ψi y V hV hyV hyG hKV hi c
    rw [hS c c₁]
    by_cases hpos : 0 < Q.GGl k ρ z z' (Matrix.of y)
    · rw [key Ψi y hyG hpos]
      rw [c1 ν Kp hKp hν ((Ψi : Q.Fn k ρ (Wq →L[ℂ] Wp)) c₁) y V hV hyV hyG hKV (fun y' hy' hG' => by
        rw [hi c₁ y' hy' hG']
        refine integral_congr_ae (ae_of_all _ fun Z => ?_)
        exact (hR Z c₁ y' hG').symm)]
      refine integral_congr_ae (ae_of_all _ fun Z => ?_)
      show _ = Φf Z y
      rw [hΦf]
      simp only [if_pos hpos]
    · rw [key0 Ψi c₁ y hpos]
      have : (fun Z => Φf Z y) = fun _ => 0 := by
        funext Z
        rw [hΦf]
        simp only [if_neg hpos]
      rw [this, integral_zero]

end Act

end Formalism.FourierDecayAlt.P.ParameterFamilyAlgebra
end
end

section

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

theorem algebraic_quantum_determinant : Qr.AlgDet :=
  qr_algDet_of (qr_algDetBasis_of quantum_jacobi_identity quantum_determinant_vector quantum_minor_covariance)

theorem capelli_hat_frame : Qr.ChatFrame := qr_chatFrame_of frame_minor

theorem determinant_hat : DetHat :=
  qr_detHat_of algebraic_quantum_determinant capelli_hat_frame capelli_right_good left_right_swap

end Formalism.FourierDecayAlt.P
end
