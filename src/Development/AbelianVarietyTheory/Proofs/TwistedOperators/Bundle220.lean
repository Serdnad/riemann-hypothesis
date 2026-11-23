module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.L2UnitaryRepresentationData
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsMatrixCoefficientsEqFockRepresentatio
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ModelsAreCoverSeries
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle025
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle197
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaCorrespondenceModelsOfCoversRealPlace
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle011
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle209
public import Formalism.LocalRingCardinality.DataTheta
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle246
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle002
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle078
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle019
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle143
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle023
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1473
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle210
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle207
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DualLatticeDifferentIndex
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec

theorem _root_.GlobalTheory.T.fockVectors_matrixCoefficients_eq_fockRepresentation : ∀ (p q r s n : ℕ) (T₀ : GrpData (p * r + q * s) (p * s + q * r)) (T₁ : GrpData p q) (T₂ : GrpData r s) (F : FockData T₀ T₁ T₂) (ι Z : Type) (G fr : Mn n) (ε : Fin n → Bool) (br : Bool) (e : Ix p q ≃ Fin n) (A : Mn n → (Z → ℂ) → (Z → ℂ)) (pt : MvPolynomial ι ℂ → (Z → ℂ)) (ip : (Z → ℂ) → (Z → ℂ) → ℂ) (Θ : Submodule ℂ (Z → ℂ)) (κ : MvPolynomial ι ℂ ≃ₗ[ℂ] Pol p q r s) (c : ℚ) (m : ℤ) (N : ℝ), 1 ≤ p + q → IsUnit fr → frᴴ * Formalism.REAL.Jm ε * fr = G → SignCompat ε e → (m : ℚ) = 2 * c → Side A pt κ (phiFr fr br e) c (fockAct1 p q r s) → L2UnitaryRepresentationData G A pt ip Θ → Fischer pt ip κ N → Coef F A pt ip κ (phiFr fr br e) m N := by
  first | exact @GlobalTheory.ArchRec.FockCoef.coef_of_side | exact GlobalTheory.ArchRec.FockCoef.coef_of_side | (intros; apply GlobalTheory.ArchRec.FockCoef.coef_of_side <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec

namespace GlobalTheory.ArchRec.KFiniteTie

open GlobalTheory.CoverModel GlobalTheory.Chain.RealIt.LocalFromCover
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (toFrame)

section Semi

variable {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
  {cj : Bool} {U : H → H'}

theorem cjc_ofReal (cj : Bool) (r : ℝ) : cjc cj (r : ℂ) = r := by
  cases cj <;> simp [cjc]

theorem exists_real (hadd : ∀ x y, U (x + y) = U x + U y) (hs : ∀ (z : ℂ) x, U (z • x) = cjc cj z • U x)
    (hb : Function.Bijective U) (hn : ∀ x, ‖U x‖ = ‖x‖) : ∃ L : H ≃ₗᵢ[ℝ] H', ∀ x, L x = U x := by
  let L₀ : H →ₗᵢ[ℝ] H' :=
    { toFun := U
      map_add' := hadd
      map_smul' := fun r x => by
        rw [← Complex.coe_smul, hs, cjc_ofReal, Complex.coe_smul, RingHom.id_apply]
      norm_map' := hn }
  exact ⟨LinearIsometryEquiv.ofSurjective L₀ hb.2, fun _ => rfl⟩

theorem inner_map (hadd : ∀ x y, U (x + y) = U x + U y) (hs : ∀ (z : ℂ) x, U (z • x) = cjc cj z • U x)
    (hn : ∀ x, ‖U x‖ = ‖x‖) (w x : H) : ⟪U w, U x⟫_ℂ = cjc cj ⟪w, x⟫_ℂ := by
  have hre : ∀ w x : H, (⟪U w, U x⟫_ℂ).re = (⟪w, x⟫_ℂ).re := fun w x => by
    have h1 := re_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two (𝕜 := ℂ) (U w) (U x)
    have h2 := re_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two (𝕜 := ℂ) w x
    rw [← hadd, hn, hn, hn, ← h2] at h1
    exact h1
  have h1 := hre w x
  have h2 := hre w (Complex.I • x)
  rw [hs, inner_smul_right, inner_smul_right] at h2
  cases cj
  · apply Complex.ext <;> simp_all [cjc]
  · apply Complex.ext
    · simp only [cjc, if_true, Complex.conj_re]
      exact h1
    · simp only [cjc, if_true, Complex.conj_im] at h2 ⊢
      simpa using h2

end Semi

theorem isFormIso_phi {p q n : ℕ} {ε : Fin n → Bool} {e : Ix p q ≃ Fin n} (h : SignCompat ε e) (br : Bool) :
    IsFormIso ε (phi br e) := by
  cases br
  · exact isFormIso_plainMat h
  · exact isFormIso_barMat h

theorem exists_kTie : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (τ : D.what₂.Tau) (p q : ℕ) (T : GrpData p q) (R : DSRep T) (lam : Ix p q → ℚ) (c : ℚ) (br cj : Bool) (e : Ix p q ≃ Fin V.rank) (m : ℤ) (U : M.H τ → R.U.H), IsParam lam → IsOrd (M.ε τ) (M.lam τ) lam c (sg br cj) e → (m : ℚ) = 2 * c → Comparison₂ R M τ br cj e m U → (∀ x v, U x = R.ι v → (IsHighestUnit (M.ε τ) (M.lam τ) (M.σ τ) x ↔ UnitHW R (blattner lam) v)) → ∃ u, KTie R M τ lam c br cj e u := by
  intro D V S M τ p q T R lam c br cj e m U hpar hord hm hT hhi
  have hφ := isFormIso_phi hord.1 br
  obtain ⟨L, hL⟩ := exists_real hT.add hT.smul hT.bij hT.norm
  have hr : ∀ v : kfin M τ, ∃ y, R.ι y = U v := by
    rintro ⟨v, hv⟩
    change U v ∈ LinearMap.range R.ι
    induction hv using Submodule.span_induction with
    | mem x hx => exact (hT.kfin x).1 hx
    | zero => rw [← hL, map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [hT.add]; exact add_mem hx hy
    | smul z x _ hx => rw [hT.smul]; exact Submodule.smul_mem _ _ hx
  choose u hu using hr
  have hmC : (m : ℂ) = 2 * (c : ℂ) := by exact_mod_cast hm
  have hgrp : ∀ (g : T.G) (x : M.H τ), U (M.σ τ (phi br e ((T.cov g : GL (Ix p q) ℂ) : Mat p q)) x) =
      ((T.sq g : ℂˣ) : ℂ) ^ m • R.U.π g (U x) := fun g x => by
    rw [hT.grp, smul_smul, ← zpow_add₀ (Units.ne_zero _), add_neg_cancel, zpow_zero, one_smul]
  refine ⟨u, hpar, hord, fun x y => R.ι_inj ?_, fun z x => R.ι_inj ?_, ⟨fun x y h => ?_, fun y => ?_⟩, ?_,
    fun Z hZ v v' => ?_, fun v => hhi _ _ (hu v).symm, fun m' hm' g v w => ?_⟩
  · rw [map_add (f := _), hu, hu, hu, Submodule.coe_add, hT.add]
  · rw [map_smul, hu, hu, Submodule.coe_smul, hT.smul]
  · exact Subtype.ext (hT.bij.1 (by rw [← hu, ← hu, h]))
  · obtain ⟨x, hx⟩ := hT.bij.2 (R.ι y)
    exact ⟨⟨x, Submodule.subset_span ((hT.kfin x).2 ⟨y, hx.symm⟩)⟩, R.ι_inj (by rw [hu]; exact hx)⟩
  · change (fun Z => toFrame M τ (phi br e Z)) '' _ = _
    rw [← toFrame_image M τ, ← Set.image_image (toFrame M τ) (phi br e)]
    congr 1
    ext Y
    obtain ⟨Z, rfl⟩ := hφ.bij.2 Y
    rw [hφ.bij.1.mem_set_image, ← hφ.mem_lie]
    rfl
  · have h1 := (hasDerivAt_sq_zpow T m hZ).fun_smul (R.der Z hZ (u v))
    have h2 : HasDerivAt (fun t : ℝ => L (M.rep τ (NormedSpace.exp (t • phiFr (M.fr τ) br e Z)) (v : M.H τ)))
        (R.ι (R.HK.act Z (u v) + ((c : ℂ) * Z.trace) • u v)) 0 := by
      convert (preTransparency := .reducible) h1 using 1
      · funext t
        have h3 := rep_exp M τ (phi br e Z) t
        rw [hL, show phiFr (M.fr τ) br e Z = toFrame M τ (phi br e Z) from rfl, h3, hφ.exp,
          ← T.expt_cov _ (GlobalTheory.RealPar.KStabLie.smul_mem_upq hZ t), hgrp, hu]
      · rw [hmC, show 2 * (c : ℂ) * (Z.trace / 2) = c * Z.trace by ring]
        simp [T.expt_zero]
    constructor
    · intro h
      have h3 := L.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h
      refine R.ι_inj ?_
      rw [hu, ← hL]
      exact h3.unique h2
    · intro h
      rw [← h, hu, ← hL] at h2
      have h3 := L.symm.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h2
      unfold VecDer
      convert h3 using 1
      · funext t; simp
      · simp
  · obtain rfl : m' = m := by exact_mod_cast hm'.trans hm.symm
    rw [← inner_map hT.add hT.smul hT.norm, hgrp, inner_smul_right, hu, hu]

end GlobalTheory.ArchRec.KFiniteTie

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec

theorem _root_.GlobalTheory.T.thetaCorrespondence_models_of_covers_realPlace : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (W : HSp D) (S' : D.what₂.Tau → SPar) (N : DSModel W S') (τ : D.what₂.Tau) (ι σ Z : Type) (A : Mn V.rank → (Z → ℂ) → (Z → ℂ)) (B : Mn W.rank → (Z → ℂ) → (Z → ℂ)) (pt : MvPolynomial ι ℂ → (Z → ℂ)) (κ : MvPolynomial ι ℂ ≃ₗ[ℂ] MvPolynomial σ ℂ) (p q r s : ℕ) (T₁ : GrpData p q) (T₂ : GrpData r s) (R₁ : DSRep T₁) (R₂ : DSRep T₂) (a₁ : Mat p q →ₗ[ℂ] Module.End ℂ (MvPolynomial σ ℂ)) (a₂ : Mat r s →ₗ[ℂ] Module.End ℂ (MvPolynomial σ ℂ)) (l₁ : Ix p q → ℚ) (l₂ : Ix r s → ℚ) (c₁ c₂ : ℚ) (b₁ b₂ : Bool) (e₁ : Ix p q ≃ Fin V.rank) (e₂ : Ix r s ≃ Fin W.rank) (u₁ : kfin M τ → R₁.HK.V) (u₂ : kfin N τ → R₂.HK.V), KTie R₁ M τ l₁ c₁ b₁ true e₁ u₁ → KTie R₂ N τ l₂ c₂ b₂ false e₂ u₂ → Side A pt κ (phiFr (M.fr τ) b₁ e₁) c₁ a₁ → Side B pt κ (phiFr (N.fr τ) b₂ e₂) c₂ a₂ → (∀ Φ, IsJoint M τ A pt N B Φ ↔ CJoint a₁ a₂ (blattner l₁) (blattner l₂) (κ Φ)) → PairLaw a₁ a₂ R₁ R₂ (blattner l₁) (blattner l₂) → LiftLaw M τ A pt N B := by
  first | exact @GlobalTheory.ArchRec.Lift.liftLaw_of_pairLaw | exact GlobalTheory.ArchRec.Lift.liftLaw_of_pairLaw | (intros; apply GlobalTheory.ArchRec.Lift.liftLaw_of_pairLaw <;> assumption)
end

section

namespace GlobalTheory.CoefficientSpanFiniteDimensional

theorem dual_apply_eq_sum {W ι : Type} [AddCommGroup W] [Module ℂ W] [Fintype ι] (b : Module.Basis ι ℂ W)
    (ℓ : Module.Dual ℂ W) (w : W) (A : W →ₗ[ℂ] W) :
    ℓ (A w) = ∑ j, ∑ i, (b.repr w j * ℓ (b i)) * b.repr (A (b j)) i := by
  conv_lhs => rw [← b.sum_repr w]

  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, map_smul]
  conv_lhs => rw [← b.sum_repr (A (b j))]

  rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, smul_eq_mul, smul_eq_mul]
  ring

theorem finiteDimensional_coeffSpan {K W : Type} [Group K] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ K W) : FiniteDimensional ℂ ↥(GlobalTheory.Published.AutFin.coeffSpan ρ) := by
  classical
  let b := Module.finBasis ℂ W
  let e : Fin (Module.finrank ℂ W) × Fin (Module.finrank ℂ W) → (K → ℂ) :=
    fun p k => b.repr (ρ k (b p.2)) p.1
  haveI : FiniteDimensional ℂ ↥(Submodule.span ℂ (Set.range e)) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range e)
  refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ (Set.range e)) (Submodule.span_le.mpr ?_)
  rintro f ⟨ℓ, w, rfl⟩
  have h : (fun k => ℓ (ρ k w)) = ∑ j, ∑ i, (b.repr w j * ℓ (b i)) • e (i, j) := by
    funext k
    rw [dual_apply_eq_sum b ℓ w (ρ k)]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, e]
  rw [h]
  exact Submodule.sum_mem _ fun j _ => Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨(i, j), rfl⟩)

end GlobalTheory.CoefficientSpanFiniteDimensional
end

section

open GlobalTheory.RealWeil MeasureTheory
open scoped SchwartzMap Matrix

theorem _root_.GlobalTheory.T.exists_scalar_of_commute_schrodingerOperators : ∀ (l : Type) [Fintype l] (S : Sch l →ₗ[ℂ] Sch l), (∀ f, ∫ x, ‖S f x‖ ^ 2 = ∫ x, ‖f x‖ ^ 2) → (∀ w (f f₁ : Sch l), ⇑f₁ = rhoFun w ⇑f → ⇑(S f₁) = rhoFun w ⇑(S f)) → ∃ c : ℂ, ∀ f, S f = c • f := by
  first | exact @GlobalTheory.RealWeil.exists_eq_smul_of_commute_rhoFun | exact GlobalTheory.RealWeil.exists_eq_smul_of_commute_rhoFun | (intros; apply GlobalTheory.RealWeil.exists_eq_smul_of_commute_rhoFun <;> assumption)
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible

namespace GlobalTheory

theorem nonempty_fockData_of_covers :
    ∀ (p q r s : ℕ) (T0 : GrpData (p * r + q * s) (p * s + q * r)) (T1 : GrpData p q)
      (T2 : GrpData r s), Nonempty (FockData T0 T1 T2) :=
  GlobalTheory.T.nonempty_fockModel_unitary_dual_pair

end GlobalTheory
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ScalarAnnih

open IsDedekindDomain GlobalTheory.Idele
open scoped nonZeroDivisors

theorem exists_compact_annihilator_finiteAdeles_traceChar (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ)
    (hc : Continuous ψ)
    (hfin : ∀ x : F, ψ (pairA F 0 (algebraMap F (Af F) x)) =
      Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ F x : ℚ) : ℂ)))
    (O : Set (Af F)) (hO : O ∈ nhds (0 : Af F)) : ∃ K : Set (Af F), IsCompact K ∧
      ∀ x : Af F, (∀ t ∈ O, ψ (pairA F 0 (t * x)) = 1) → x ∈ K := by
  obtain ⟨N, hN, hNO⟩ := GlobalTheory.AdLat.OpenLat.exists_nsmul_adele F O hO
  obtain ⟨t, ht⟩ := exists_idealOf_eq (GlobalTheory.StdDual.codiff_ne_zero (F := F))
  let c : Af F := algebraMap F (Af F) ((N : F)⁻¹) * (t : Af F)
  refine ⟨(fun a => c * a) '' {a : Af F | ∀ v, a v ∈ v.adicCompletionIntegers F},
    (GlobalTheory.AdeleCocompact.isCompact_integral F).image (continuous_const.mul continuous_id), ?_⟩
  intro x hx
  have h1 : (N : Af F) * x ∈ adelicIdeal (GlobalTheory.StdDual.codiff F) := by
    rw [GlobalTheory.SplitUnram.mem_adelicIdeal_codiff_iff hc hfin]
    intro α hα
    have := hx _ (hNO α hα)
    rwa [nsmul_eq_mul, mul_assoc, mul_left_comm] at this
  have h2 : (t : Af F) * (((t⁻¹ : (Af F)ˣ) : Af F) * ((N : Af F) * x)) ∈
      adelicIdeal (t • (1 : FractionalIdeal (𝓞 F)⁰ F)) := by
    rw [Units.mul_inv_cancel_left, smul_one_eq, ht]; exact h1
  rw [mul_mem_adelicIdeal_smul, mem_adelicIdeal] at h2
  refine ⟨_, fun v => (mem_localIdeal_one_iff v _).1 (h2 v), ?_⟩
  have hN0 : (N : F) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have e : algebraMap F (Af F) ((N : F)⁻¹) * (N : Af F) = 1 := by
    rw [← map_natCast (algebraMap F (Af F)) N, ← map_mul, inv_mul_cancel₀ hN0, map_one]
  simp only [c]
  calc algebraMap F (Af F) ((N : F)⁻¹) * (t : Af F) * (((t⁻¹ : (Af F)ˣ) : Af F) * ((N : Af F) * x))
      = algebraMap F (Af F) ((N : F)⁻¹) * (N : Af F) * x := by
        rw [mul_assoc, Units.mul_inv_cancel_left, mul_assoc]
    _ = x := by rw [e, one_mul]

theorem exists_compact_of_annih : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ O ∈ nhds (0 : Af D.host.F), ∃ K : Set (Af D.host.F), IsCompact K ∧
      ∀ x : Af D.host.F, (∀ t ∈ O, ψ (pairA D.host.F 0 (t * x)) = 1) → x ∈ K :=
  fun D ψ hψ O hO =>
    exists_compact_annihilator_finiteAdeles_traceChar D.host.F ψ hψ.1.1 (GlobalTheory.StdRat.stdChar_fin_rat D ψ hψ) O hO

end GlobalTheory.ScalarAnnih

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem definite_unitary_cocompact :
    ∀ {D : D7} (V : HSp D), (∀ τ, (gramAt D V τ).PosDef) →
      ∃ C : Set (GA D V), IsCompact C ∧ ∀ h : GA D V, ∃ γ ∈ GQ V, ∃ c ∈ C, h = γ * c :=
  GlobalTheory.DefiniteQuotient.exists_compact

end GlobalTheory
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped Pointwise TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Grid GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle GlobalTheory.ConstRatio

theorem _root_.GlobalTheory.T.continuous_automorphic_eq_zero_of_vanish_on_finiteAdelic : ∀ (D : D7) (V : HSp D) (φ : GA D V → ℂ), (∀ τ, (gramAt D V τ).PosDef) → Continuous φ → (∀ γ ∈ GQ V, ∀ h, φ (γ * h) = φ h) → (∀ h ∈ GfC V, φ h = 0) → ∀ h, φ h = 0 := by
  first | exact @GlobalTheory.Adopt.continuous_automorphic_eq_zero_of_vanish_on_finiteAdelic | exact GlobalTheory.Adopt.continuous_automorphic_eq_zero_of_vanish_on_finiteAdelic | (intros; apply GlobalTheory.Adopt.continuous_automorphic_eq_zero_of_vanish_on_finiteAdelic <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.EvalAtUnitVectorFinal

theorem evInj_of_isModels_of_tie : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.IsModels → FWTie T R κ v₀ → EvInj T R v₀ := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ hM ht
  have hHW : R.models_HW := by
    cases hM
    assumption
  exact GlobalTheory.EvalAtUnitVector.evInj T R v₀ hHW ht.hv₀

end GlobalTheory.EvalAtUnitVectorFinal
end
