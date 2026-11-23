module

import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1202
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1214
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1234
public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Univ
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1252
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIdeleAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle030
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle042
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.EqNegOfCommute
import Development.WeilBound.ThetaLifts.TowerModels.PlaneReal
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.TotallySplit
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
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle010
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.CmpbHessAtAddConst
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
public import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFrameOfForallExists
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle001
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ThetaQuasiRat

theorem schr_schr {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ : Type} [Fintype κ]
    (w w' : (κ → R) × (κ → R)) (φ : (κ → R) → ℂ) :
    GlobalTheory.WeilM.schr ψ w (GlobalTheory.WeilM.schr ψ w' φ) =
      ψ (⅟(2 : R) * (w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2)) • GlobalTheory.WeilM.schr ψ (w + w') φ := by
  funext x
  simp only [GlobalTheory.WeilM.schr, Pi.smul_apply, smul_eq_mul, Prod.fst_add, Prod.snd_add, add_assoc, ← mul_assoc,
    ← AddChar.map_add_eq_mul, add_dotProduct, dotProduct_add]
  congr 2
  have h : ⅟(2 : R) * 2 = 1 := invOf_mul_self 2
  linear_combination (-(w.1 ⬝ᵥ w'.2)) * h

theorem thetaSum_smul' (F : Type) [Field F] [NumberField F] {κ : Type} (c : ℂ) (φ : (κ → AdeleRing (𝓞 F) F) → ℂ) :
    GlobalTheory.WeilM.thetaSum F (c • φ) = c * GlobalTheory.WeilM.thetaSum F φ := by
  simp only [GlobalTheory.WeilM.thetaSum, Pi.smul_apply, smul_eq_mul, tsum_mul_left]

theorem thetaSum_schr_rat (F : Type) [Field F] [NumberField F] [Invertible (2 : AdeleRing (𝓞 F) F)]
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : ∀ a : F, ψ (algebraMap F (AdeleRing (𝓞 F) F) a) = 1)
    {κ : Type} [Fintype κ] (y z : κ → F) (φ : (κ → AdeleRing (𝓞 F) F) → ℂ) :
    GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ
      (fun i => algebraMap F (AdeleRing (𝓞 F) F) (y i), fun i => algebraMap F (AdeleRing (𝓞 F) F) (z i)) φ) =
      GlobalTheory.WeilM.thetaSum F φ := by
  have h2 : ⅟(2 : AdeleRing (𝓞 F) F) = algebraMap F (AdeleRing (𝓞 F) F) (1 / 2) := by
    apply invOf_eq_right_inv
    rw [← map_ofNat (algebraMap F (AdeleRing (𝓞 F) F)) 2, ← map_mul]
    norm_num
  have key : ∀ ξ : κ → F, ψ ((fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i)) ⬝ᵥ
      (fun i => algebraMap F (AdeleRing (𝓞 F) F) (z i)) + ⅟(2 : AdeleRing (𝓞 F) F) *
      ((fun i => algebraMap F (AdeleRing (𝓞 F) F) (y i)) ⬝ᵥ (fun i => algebraMap F (AdeleRing (𝓞 F) F) (z i)))) = 1 := by
    intro ξ
    have e : (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i)) ⬝ᵥ (fun i => algebraMap F (AdeleRing (𝓞 F) F) (z i)) +
        ⅟(2 : AdeleRing (𝓞 F) F) * ((fun i => algebraMap F (AdeleRing (𝓞 F) F) (y i)) ⬝ᵥ
          (fun i => algebraMap F (AdeleRing (𝓞 F) F) (z i))) =
        algebraMap F (AdeleRing (𝓞 F) F) (ξ ⬝ᵥ z + 1 / 2 * (y ⬝ᵥ z)) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [dotProduct, map_add (f := _), map_mul, map_sum, h2]
    rw [e]
    exact hψ _
  unfold GlobalTheory.WeilM.thetaSum GlobalTheory.WeilM.schr
  simp only [key, one_mul]
  rw [← (Equiv.addRight y).tsum_eq (fun ξ : κ → F => φ (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i)))]
  congr 1
  funext ξ
  congr 1
  funext i
  exact (map_add (algebraMap F (AdeleRing (𝓞 F) F)) (ξ i) (y i)).symm

end GlobalTheory.ThetaQuasiRat

namespace GlobalTheory.ThetaQuasiRat

theorem cA_apply (D : D7) (a : AF D.host.F ⊗[D.host.F] D.host.E) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig a = cA D a := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => rfl
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]

theorem symp_eq_symplO (D : D7) (S T : HSp D) (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E)
    (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E) (ξ : AF D.host.F ⊗[D.host.F] D.host.E) (hA : JA = T.gramᵀ)
    (hB : ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹)) (x y : Formalism.IndefR.Datum.WO S T) :
    GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB) x y =
      Formalism.IndefR.Datum.symplO S T x y := by
  apply GlobalTheory.WeilSchrodinger.symp_eq_symplO <;> assumption

end GlobalTheory.ThetaQuasiRat

namespace GlobalTheory.ThetaQuasiRat

theorem thetaTr_ratW_add : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
      (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
      ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
      ∀ (κ : Type) [Fintype κ]
        (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
        (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
          co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
        ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F κ, ∀ (γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (w : Formalism.IndefR.Datum.WO S T),
          GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ Φ (ratW T S γ + w) = ψ (-(Formalism.IndefR.Datum.symplOH S T (ratW T S γ) w)) * GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ Φ w := by
  intro D ψ hψ S T JA JB ξ hA hB κ _ co hrat Φ _ γ w
  obtain ⟨y, z, hyz⟩ := hrat γ
  have hγ : ratW T S γ = incM D.host.F γ := rfl
  have hform := co.form (incM D.host.F γ) w
  rw [symp_eq_symplO D S T JA JB ξ hA hB, hyz] at hform
  unfold GlobalTheory.WeilSchrodinger.thetaTr GlobalTheory.WeilM.Darboux.rho
  rw [map_add (f := _), hγ, hyz]
  set u : (κ → AF D.host.F) × (κ → AF D.host.F) :=
    (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i)) with hu
  set v := co.e w
  have law := schr_schr ψ u v Φ
  have hinv : ψ (-(⅟(2 : AF D.host.F) * (u.1 ⬝ᵥ v.2 - v.1 ⬝ᵥ u.2))) *
      ψ (⅟(2 : AF D.host.F) * (u.1 ⬝ᵥ v.2 - v.1 ⬝ᵥ u.2)) = 1 := by
    rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
  have hsum : GlobalTheory.WeilM.schr ψ (u + v) Φ =
      ψ (-(⅟(2 : AF D.host.F) * (u.1 ⬝ᵥ v.2 - v.1 ⬝ᵥ u.2))) • GlobalTheory.WeilM.schr ψ u (GlobalTheory.WeilM.schr ψ v Φ) := by
    rw [law, smul_smul, hinv, one_smul]
  have h2 : ⅟(2 : AF D.host.F) = algebraMap D.host.F (AF D.host.F) (1 / 2) := by
    apply invOf_eq_right_inv
    rw [← map_ofNat (algebraMap D.host.F (AF D.host.F)) 2, ← map_mul]
    norm_num
  rw [hsum, thetaSum_smul', hu, thetaSum_schr_rat D.host.F ψ hψ.1.2.2.1 y z, ← hu,
    Formalism.IndefR.Datum.symplOH, hform, h2]

end GlobalTheory.ThetaQuasiRat
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

noncomputable section

namespace GlobalTheory.Mix.PartApply

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}

def colSum (H : Fin D → Matrix (Fin D) (Fin D) ℂ) : ℂ :=
  ∑ τ : Equiv.Perm (Fin D), (Matrix.of fun j l => H (τ l) j l).det

theorem colSum_mul_left (A : Matrix (Fin D) (Fin D) ℂ) (H : Fin D → Matrix (Fin D) (Fin D) ℂ) :
    colSum (fun a => A * H a) = A.det * colSum H := by
  simp only [colSum, Finset.mul_sum, ← Matrix.det_mul]
  refine Finset.sum_congr rfl fun τ _ => congrArg _ ?_
  ext j l
  simp [Matrix.mul_apply]

theorem colSum_transpose (H : Fin D → Matrix (Fin D) (Fin D) ℂ) :
    colSum (fun a => (H a).transpose) = colSum H := by
  simp only [colSum, Matrix.det_apply', Matrix.of_apply, Matrix.transpose_apply]
  rw [Finset.sum_comm, Finset.sum_comm (f := fun (τ ρ : Equiv.Perm (Fin D)) => ((Equiv.Perm.sign ρ : ℤ) : ℂ) * ∏ i, H (τ i) (ρ i) i)]
  refine Fintype.sum_equiv (Equiv.inv _) _ _ fun ρ => ?_
  refine Fintype.sum_equiv (Equiv.mulRight ρ⁻¹) _ _ fun τ => ?_
  simp only [Equiv.inv_apply, Equiv.Perm.sign_inv, Equiv.coe_mulRight]
  congr 1
  refine Fintype.prod_equiv ρ _ _ fun i => ?_
  simp

theorem colSum_mul (A B : Matrix (Fin D) (Fin D) ℂ) (H : Fin D → Matrix (Fin D) (Fin D) ℂ) :
    colSum (fun a => A * H a * B) = A.det * B.det * colSum H := by
  have e : colSum (fun a => H a * B) = B.det * colSum H := by
    rw [← colSum_transpose, ← colSum_transpose H, ← Matrix.det_transpose B, ← colSum_mul_left]
    simp only [Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]
  rw [colSum_mul_left A fun a => H a * B, e, mul_assoc]

theorem dens_eq (L : Fin D → MLine p σ) (c : AlgChart p σ D) (y : CxPts p σ) :
    dens L c y = (Real.pi ^ D)⁻¹ * (colSum fun a => c.hess (L a).φ (pick (L a).φ.isLB y) y).re := rfl

theorem dens_trans (L : Fin D → MLine p σ) (c c' : AlgChart p σ D) {y : CxPts p σ} (hy : y ∈ c.e.source)
    (hy' : y ∈ c'.e.source) : dens L c y = ‖transDet c.e c'.e y‖ ^ 2 * dens L c' y := by
  apply _root_.GlobalTheory.Mix.ChartChange.dens_trans <;> assumption

end GlobalTheory.Mix.PartApply

namespace GlobalTheory.Mix

theorem part_apply : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) [SecondCountableTopology (CxPts p σ)] (D : ℕ) (L : Fin D → MLine p σ) (ε : ℤˣ) (c : AlgChart p σ D) (S : Set (CxPts p σ)), MeasurableSet S → S ⊆ c.e.source → part L ε S = ∫⁻ v in c.e '' S, ENNReal.ofReal ((ε : ℤ) * dens L c (c.e.symm v)) := by
  intro k _ X p σ _ D L ε c S hS hc
  rw [part, glueMeas_apply _ _ (fun c c' => c.holo_trans c') (fun c c' y hy hy' => by
    rw [PartApply.dens_trans L c c' hy hy', mul_left_comm, ENNReal.ofReal_mul (sq_nonneg _)])
    c hS hc, chartMeas_apply_of_subset _ _ hS hc]

end GlobalTheory.Mix
end
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CptBound

variable {E : Type} [Field E] [NumberField E]

theorem isOpen_le_exp (w : Pl E) (m : ℤ) :
    IsOpen {y : w.adicCompletion E | Valued.v y ≤ WithZero.exp m} := by
  apply _root_.GlobalTheory.PowBdd.isOpen_le_exp <;> assumption

theorem exists_bound_of_isCompact (w : Pl E) {S : Set (w.adicCompletion E)} (hS : IsCompact S) :
    ∃ γ : WithZero (Multiplicative ℤ), ∀ x ∈ S, Valued.v x ≤ γ := by
  have hcov : S ⊆ ⋃ m : ℕ, {y : w.adicCompletion E | Valued.v y ≤ WithZero.exp (m : ℤ)} := by
    intro x _
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    rcases eq_or_ne (Valued.v x) 0 with h | h
    · exact ⟨0, by rw [h]; exact zero_le'⟩
    · refine ⟨(WithZero.log (Valued.v x)).toNat, ?_⟩
      conv_lhs => rw [← WithZero.exp_log h]
      rw [WithZero.exp_le_exp]
      exact Int.self_le_toNat _
  have hdir : Directed (· ⊆ ·) (fun m : ℕ => {y : w.adicCompletion E | Valued.v y ≤ WithZero.exp (m : ℤ)}) :=
    Monotone.directed_le fun a b hab y (hy : _ ≤ _) =>
      (show _ ≤ _ from hy.trans (WithZero.exp_le_exp.2 (by exact_mod_cast hab)))
  obtain ⟨m, hm⟩ := hS.elim_directed_cover _ (fun m => isOpen_le_exp w _) hcov hdir
  exact ⟨_, fun x hx => hm hx⟩

theorem charpoly_coeff_eq {R : Type} [CommRing R] (n : ℕ) (M : Matrix (Fin n) (Fin n) R) (k : ℕ) :
    M.charpoly.coeff k = MvPolynomial.eval (fun ij : Fin n × Fin n => M ij.1 ij.2)
      (MvPolynomial.map (Int.castRingHom R) ((Matrix.charpoly.univ ℤ (Fin n)).coeff k)) := by
  rw [MvPolynomial.eval_map]
  have h := Matrix.charpoly.univ_map_eval₂Hom (Fin n) (Int.castRingHom R) (fun ij : Fin n × Fin n => M ij.1 ij.2)
  have hM : Matrix.of (Function.curry fun ij : Fin n × Fin n => M ij.1 ij.2) = M := by
    ext i j; rfl
  rw [hM] at h
  rw [← h, Polynomial.coeff_map]
  rfl

end GlobalTheory.CptBound

namespace GlobalTheory.BCT

open GlobalTheory.CptBound

theorem charpoly_det_bounded_of_isCompact : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E)
    (C : Set (GLw n w)), IsCompact C → ∃ γ : WithZero (Multiplicative ℤ), ∀ y ∈ C,
      (∀ k, Valued.v (y.val.charpoly.coeff k) ≤ γ) ∧ Valued.v (y⁻¹ : GLw n w).val.det ≤ γ := by
  intro E _ _ _ n w C hC
  have hent : Continuous fun y : GLw n w => fun ij : Fin n × Fin n => y.val ij.1 ij.2 :=
    continuous_pi fun ij => Units.continuous_val.matrix_elem ij.1 ij.2
  have hco : ∀ k, Continuous fun y : GLw n w => y.val.charpoly.coeff k := by
    intro k
    have e : (fun y : GLw n w => y.val.charpoly.coeff k) = fun y : GLw n w =>
        MvPolynomial.eval (fun ij : Fin n × Fin n => y.val ij.1 ij.2)
          (MvPolynomial.map (Int.castRingHom (w.adicCompletion E)) ((Matrix.charpoly.univ ℤ (Fin n)).coeff k)) :=
      funext fun y => charpoly_coeff_eq n y.val k
    rw [e]
    exact (MvPolynomial.continuous_eval _).comp hent
  have hdet : Continuous fun y : GLw n w => (y⁻¹ : GLw n w).val.det :=
    Units.continuous_coe_inv.matrix_det
  set S : Set (w.adicCompletion E) :=
    (⋃ k ∈ Finset.range (n + 1), (fun y : GLw n w => y.val.charpoly.coeff k) '' C) ∪
      ((fun y : GLw n w => (y⁻¹ : GLw n w).val.det) '' C) with hS
  have hSc : IsCompact S :=
    ((Finset.range (n + 1)).isCompact_biUnion fun k _ => hC.image (hco k)).union (hC.image hdet)
  obtain ⟨γ, hγ⟩ := exists_bound_of_isCompact w hSc
  refine ⟨γ, fun y hy => ⟨fun k => ?_, hγ _ (Or.inr ⟨y, hy, rfl⟩)⟩⟩
  by_cases hk : k < n + 1
  · exact hγ _ (Or.inl (Set.mem_biUnion (Finset.mem_range.2 hk) ⟨y, hy, rfl⟩))
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by
      rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]; omega), map_zero]
    exact zero_le'

end GlobalTheory.BCT
end
end

section

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.WeilM

namespace GlobalTheory.ThKOp


open scoped Classical in
theorem continuous_of_mem_schA {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    {Φ : (κ → AdeleRing (𝓞 F) F) → ℂ} (hΦ : Φ ∈ schA F κ) : Continuous Φ := by
  apply GlobalTheory.ThetaUnfold.schA_continuous <;> assumption

end GlobalTheory.ThKOp
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct Kronecker ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.VacuumCharacter

theorem exists_factor {m : ℕ} (P : Matrix (Fin m) (Fin m) ℂ) (hP : P * P = P) :
    ∃ (p : ℕ) (U : Matrix (Fin m) (Fin p) ℂ) (V : Matrix (Fin p) (Fin m) ℂ), U * V = P ∧ V * U = 1 := by
  apply GlobalTheory.OneMapRef.RealMove.exists_factor <;> assumption

theorem det_idem_kron {m n : ℕ} (P : Matrix (Fin m) (Fin m) ℂ) (hP : P * P = P) :
    ∃ p : ℕ, P.trace = p ∧ ∀ a : Matrix (Fin n) (Fin n) ℂ,
      (P ⊗ₖ a + (1 - P) ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)).det = a.det ^ p := by
  apply GlobalTheory.OneMapRef.RealMove.det_idem_kron <;> assumption

theorem detPlus_one {m n : ℕ} (s : Matrix (Fin m) (Fin m) ℂ) (hs : s * s = 1) :
    ∃ p : ℕ, s.trace = 2 * p - m ∧ ∀ (a : Matrix (Fin n) (Fin n) ℂ) (b : Matrix (Fin m) (Fin m) ℂ), s * b = b * s →
      GlobalTheory.WeilParts.detPlus 1 s a b = ((1 / 2 : ℂ) • (1 + s) * b + (1 / 2 : ℂ) • (1 - s)).det ^ n * a.det ^ p ∧
      b.det = ((1 / 2 : ℂ) • (1 + s) * b + (1 / 2 : ℂ) • (1 - s)).det *
        ((1 / 2 : ℂ) • (1 - s) * b + (1 / 2 : ℂ) • (1 + s)).det := by
  apply GlobalTheory.OneMapRef.RealMove.detPlus_one <;> assumption

variable {D : D7}

theorem hasInfExp_twist {χ η : (AE D)ˣ →* Circle} {τ : D.what₂.Tau} {a : ℚ} (hχ : HasInfExp D χ τ a)
    (hη : HasInfExp D η τ (1 / 2)) (k : ℕ) : HasInfExp D (χ * (η ^ k)⁻¹) τ (a - k / 2) := by
  apply GlobalTheory.OneMapRef.RealMove.hasInfExp_twist <;> assumption

theorem adele_ext {θ : InfFam D} (hθ : IsInfFam θ) {x y : AE D} (h1 : finPart D x = finPart D y)
    (h2 : ∀ τ, θ τ (infPart D x) = θ τ (infPart D y)) : x = y := by
  apply GlobalTheory.OneMapRef.RealMove.adele_ext <;> assumption


open Classical in
theorem exists_idele_at {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) (w : ℂ) (hw : w ≠ 0) :
    ∃ x : (AE D)ˣ, finPart D (x : AE D) = 1 ∧ ∀ τ', θ τ' (infPart D (x : AE D)) = if τ' = τ then w else 1 := by
  apply GlobalTheory.OneMapRef.RealMove.exists_idele_at <;> assumption

theorem det_compAt (θ : InfFam D) (τ : D.what₂.Tau) {k : ℕ} (M : Matrix (Fin k) (Fin k) (AE D)) :
    (compAt θ τ M).det = θ τ (infPart D M.det) := by
  apply GlobalTheory.OneMapRef.RealMove.det_compAt <;> assumption

theorem finPart_cA (z : AE D) (hz : finPart D z = 1) : finPart D (cA D z) = 1 := by
  apply GlobalTheory.OneMapRef.RealMove.finPart_cA <;> assumption

theorem exists_root {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) (hV : ∀ τ, (gramAt D V τ).det ≠ 0)
    (g : GA D V) (hg : g ∈ GinfC V) :
    ∃ x, IsDetRoot V g x ∧ ∀ (ν : (AE D)ˣ →* Circle) (c : D.what₂.Tau → ℤ), (∀ τ, HasInfExp D ν τ (c τ)) →
      ((ν x : Circle) : ℂ) = ∏ τ, (compAt θ τ (Formalism.L2.Theta.mt V g)).det ^ c τ := by
  apply GlobalTheory.OneMapRef.RealMove.exists_root <;> assumption

end GlobalTheory.VacuumCharacter

end
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.AdelicU

noncomputable section

namespace GlobalTheory.HermSelfDualLoc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem det_ne_zero_of_hasSig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) : M.det ≠ 0 := by
  apply PositivityTheory.ThKG.Tow.Pln.det_ne_zero_of_hasSig <;> assumption

theorem det_ne_zero_of_isHerm (σ : E →ₐ[F] E) (B : Base F E) {n : ℕ} {X : Spc F E n} {r s : ℕ}
    (hX : X.IsHerm σ B r s) : X.J.det ≠ 0 := by
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
  have h := det_ne_zero_of_hasSig (hX.sig w)
  have e : (X.J.map (B.emb w).1).det = (B.emb w).1 X.J.det := (RingHom.map_det _ _).symm
  intro h0
  exact h (by rw [e, h0, map_zero])

theorem hE_transpose (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) :
    hE σ Jᵀ x y = form σ J y x := by
  simp only [hE, Formalism.UG.hform, form, dotProduct, Matrix.mulVec, Matrix.transpose_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  simp only [AlgHom.coe_toRingHom]
  ring

theorem isIntegral_iff_mem_range (e : E) : IsIntegral ℤ e ↔ e ∈ (algebraMap (𝓞 E) E).range :=
  ⟨fun h => ⟨⟨e, h⟩, rfl⟩, fun ⟨r, hr⟩ => hr ▸ r.isIntegral_coe⟩

theorem isSelfDualAt_transpose : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (X : Spc F E n) (r s : ℕ), B.IsGood σ → X.IsHerm σ B r s →
    ∀ v : HeightOneSpectrum (𝓞 F), IsSelfDualAt σ X.Jᵀ X.L v := by
  intro F E _ _ _ _ _ σ B n X r s _ hX v
  have hJ : (X.Jᵀ).det ≠ 0 := by rw [Matrix.det_transpose]; exact det_ne_zero_of_isHerm σ B hX
  refine (GlobalTheory.AdelicU.SelfDual.forall_isSelfDualAt_iff hJ hX.lat).2 (fun y => ?_) v
  rw [hX.dual y]
  simp only [hE_transpose, isIntegral_iff_mem_range]

end GlobalTheory.HermSelfDualLoc

end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo
open GlobalTheory.LB (toMod)
open GlobalTheory.VB (degOfRank)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RatFibreClosure

end GlobalTheory.RatFibreClosure
end
end
