module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAutomorphicFunctionTranslateAtRealPlace
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle014
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle011
public import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.ConjAtFixedIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1806
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle313
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle218
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqUniqueOfClassification
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle448
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle322
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle514
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle409
import Formalism.LocalToGlobal.IndefiniteReal.Bundle022
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DefLift

namespace GlobalTheory.DefLift.LowerKill

open GlobalTheory.PointAtPlaceHom GlobalTheory.Mem.RealTranslate

theorem entry_eq_zero {n : ℕ} {ε : Fin n → Bool} {κ : Matrix (Fin n) (Fin n) ℂ}
    (h : κ * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * κ) {a b : Fin n} (hab : ε a ≠ ε b) : κ a b = 0 := by
  have e := congrFun (congrFun h a) b
  simp only [Formalism.REAL.Jm, mul_diagonal, diagonal_mul] at e
  cases ha : ε a <;> cases hb : ε b <;> simp only [ha, hb, ne_eq, not_true_eq_false] at hab e
  · simp only [Bool.false_eq_true, if_false, if_true] at e
    linear_combination (1 / 2 : ℂ) * e
  · simp only [Bool.false_eq_true, if_false, if_true] at e
    linear_combination (-1 / 2 : ℂ) * e

theorem block_conj {n : ℕ} {ε : Fin n → Bool} {κ κ' Y : Matrix (Fin n) (Fin n) ℂ}
    (h : κ * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * κ) (h' : κ' * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * κ')
    (hY : ∀ a b, ¬ (ε a = false ∧ ε b = true) → Y a b = 0) (a b : Fin n) (hab : ¬ (ε a = false ∧ ε b = true)) :
    (κ' * Y * κ) a b = 0 := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun d _ => ?_
  by_cases hd : ε d = ε b
  · rw [Matrix.mul_apply, Finset.sum_eq_zero fun c _ => ?_, zero_mul]
    by_cases hc : ε a = ε c
    · rw [hY c d (by rw [← hc, hd]; exact hab), mul_zero]
    · rw [entry_eq_zero h' hc, zero_mul]
  · rw [entry_eq_zero h hd, mul_zero]

variable {D : D7} {T : HSp D} {Sp : D.what₂.Tau → SPar}

theorem frame_mem_UH (M : DSModel T Sp) (τ : D.what₂.Tau) {κ : Matrix (Fin T.rank) (Fin T.rank) ℂ}
    (hκ : κ ∈ Formalism.REAL.Kset (M.ε τ)) : (M.fr τ)⁻¹ * κ * M.fr τ ∈ Formalism.QuantumDeterminants.UH (gramAt D T τ) := by
  have hu : IsUnit (M.fr τ).det := (isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have h1 : κᴴ * κ = 1 := hκ.1.1
  have h2 : κᴴ * Formalism.REAL.Jm (M.ε τ) * κ = Formalism.REAL.Jm (M.ε τ) := by
    rw [Matrix.mul_assoc, ← hκ.2, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  have h3 : M.fr τ * ((M.fr τ)⁻¹ * κ * M.fr τ) = κ * M.fr τ := by
    rw [Matrix.mul_assoc, mul_nonsing_inv_cancel_left _ _ hu]
  show ((M.fr τ)⁻¹ * κ * M.fr τ)ᴴ * gramAt D T τ * ((M.fr τ)⁻¹ * κ * M.fr τ) = gramAt D T τ
  rw [← M.fr_gram τ]
  calc _ = (M.fr τ * ((M.fr τ)⁻¹ * κ * M.fr τ))ᴴ * Formalism.REAL.Jm (M.ε τ) * (M.fr τ * ((M.fr τ)⁻¹ * κ * M.fr τ)) := by
        rw [conjTranspose_mul (M.fr τ)]
        simp only [Matrix.mul_assoc]
    _ = (M.fr τ)ᴴ * (κᴴ * Formalism.REAL.Jm (M.ε τ) * κ) * M.fr τ := by
        rw [h3, conjTranspose_mul]
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [h2]

theorem adAt_mem_pMinus {θ : InfFam D} (hθ : IsInfFam θ) (M : DSModel T Sp) (ρ τ : D.what₂.Tau)
    {κ : Matrix (Fin T.rank) (Fin T.rank) ℂ} (hκ : κ ∈ Formalism.REAL.Kset (M.ε ρ))
    {Z : Matrix (Fin T.rank) (Fin T.rank) ℂ} (hZ : Z ∈ GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicParabolicSmoothFunctions.pMinus M τ) :
    adAt θ (atTau θ T ρ ((M.fr ρ)⁻¹ * κ * M.fr ρ)) τ Z ∈ GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicParabolicSmoothFunctions.pMinus M τ := by
  have hs := atTau_spec hθ T ρ (frame_mem_UH M ρ hκ)
  have hi : infMat D.sp.cm.sig T.gram (θ τ) (atTau θ T ρ ((M.fr ρ)⁻¹ * κ * M.fr ρ)) *
      infMat D.sp.cm.sig T.gram (θ τ) (atTau θ T ρ ((M.fr ρ)⁻¹ * κ * M.fr ρ))⁻¹ = 1 := by
    rw [← infMat_mul, mul_inv_cancel, infMat_one]
  unfold adAt
  by_cases c : τ = ρ
  · subst c
    have hu : IsUnit (M.fr τ).det := (isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
    have h1 : κ * κᴴ = 1 := hκ.1.2
    have h1' : κᴴ * κ = 1 := hκ.1.1
    have hJ : κᴴ * Formalism.REAL.Jm (M.ε τ) = Formalism.REAL.Jm (M.ε τ) * κᴴ := by
      have := congrArg conjTranspose hκ.2
      rw [conjTranspose_mul, conjTranspose_mul, Formalism.REAL.Jm_conjTranspose] at this
      exact this.symm
    rw [hs.2.1] at hi ⊢
    have hi2 : (M.fr τ)⁻¹ * κ * M.fr τ * ((M.fr τ)⁻¹ * κᴴ * M.fr τ) = 1 := by
      rw [Matrix.mul_assoc, Matrix.mul_assoc _ κᴴ, mul_nonsing_inv_cancel_left _ _ hu, Matrix.mul_assoc,
        ← Matrix.mul_assoc κ, h1, Matrix.one_mul, nonsing_inv_mul _ hu]
    rw [← inv_eq_right_inv hi, inv_eq_right_inv hi2]
    intro a b hab
    have e : M.fr τ * ((M.fr τ)⁻¹ * κᴴ * M.fr τ * Z * ((M.fr τ)⁻¹ * κ * M.fr τ)) * (M.fr τ)⁻¹ =
        κᴴ * (M.fr τ * Z * (M.fr τ)⁻¹) * κ := by
      simp only [Matrix.mul_assoc, mul_nonsing_inv _ hu, Matrix.mul_one, mul_nonsing_inv_cancel_left _ _ hu]
    rw [e]
    exact block_conj hκ.2 hJ hZ a b hab
  · rw [hs.2.2 τ c] at hi ⊢
    rw [Matrix.one_mul] at hi
    rw [hi, Matrix.one_mul, Matrix.mul_one]
    exact hZ

variable {ψ : AddChar (AF D.host.F) ℂ} {S : HSp D} {χS χT : (AE D)ˣ →* Circle}
  {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} {θ : InfFam D}

theorem exists_op (hom : IsWeilDatumO ψ S T χS χT om) (hθ : IsInfFam θ) (τ : D.what₂.Tau)
    (Z : Matrix (Fin T.rank) (Fin T.rank) ℂ) : ∃ L : Module.End ℂ (WO S T → ℂ), ∀ f, IsThetaFunO ψ S T f → ∀ h,
      RderC θ T τ Z (fun g => thetaKO om h g f) = fun g => thetaKO om h g (L f) := by
  have key : ∀ X ∈ lieAt T τ, ∃ L : Module.End ℂ (WO S T → ℂ), ∀ f, IsThetaFunO ψ S T f → ∀ h,
      Rder θ T τ X (fun g => thetaKO om h g f) = fun g => thetaKO om h g (L f) := by
    intro X hX
    obtain ⟨L, hL⟩ := GlobalTheory.T.exists_weilDatum_generator_realOneParamGroup D ψ S T χS χT om hom θ hθ τ X hX
    refine ⟨L, fun f hf h => funext fun g => ?_⟩
    have := ((hL f hf).2.2.2 (h, g) 0).deriv
    simp only [Prod.mk_mul_mk, mul_one] at this
    exact this
  obtain ⟨h1, h2⟩ := GlobalTheory.SmoothAutCheck.parts_mem T τ Z
  obtain ⟨L₁, e1⟩ := key _ h1
  obtain ⟨L₂, e2⟩ := key _ h2
  refine ⟨L₁ + Complex.I • L₂, fun f hf h => ?_⟩
  unfold RderC
  rw [e1 f hf, e2 f hf]
  funext g
  simp [thetaKO]

def killed (hom : IsWeilDatumO ψ S T χS χT om) (hθ : IsInfFam θ) (M : DSModel T Sp) {Y : Type} [AddCommGroup Y]
    [Module ℂ Y] (pt : Y →ₗ[ℂ] (WO S T → ℂ)) (hpt : ∀ P, IsThetaFunO ψ S T (pt P)) : Submodule ℂ Y where
  carrier := {P | ∀ τ, ∀ Z ∈ GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicParabolicSmoothFunctions.pMinus M τ, ∀ h, RderC θ T τ Z (fun g => thetaKO om h g (pt P)) = 0}
  add_mem' := by
    intro P Q hP hQ τ Z hZ h
    obtain ⟨L, hL⟩ := exists_op hom hθ τ Z
    have a := hP τ Z hZ h
    have b := hQ τ Z hZ h
    rw [hL _ (hpt _)] at a b ⊢
    funext g
    have a' := congrFun a g
    have b' := congrFun b g
    simp only [thetaKO, map_add (f := _), Pi.add_apply, Pi.zero_apply] at a' b' ⊢
    rw [a', b', add_zero]
  zero_mem' := by
    intro τ Z _ h
    obtain ⟨L, hL⟩ := exists_op hom hθ τ Z
    rw [hL _ (hpt _)]
    funext g
    simp [thetaKO]
  smul_mem' := by
    intro r P hP τ Z hZ h
    obtain ⟨L, hL⟩ := exists_op hom hθ τ Z
    have a := hP τ Z hZ h
    rw [hL _ (hpt _)] at a ⊢
    funext g
    have a' := congrFun a g
    simp only [thetaKO, map_smul, Pi.smul_apply, Pi.zero_apply] at a' ⊢
    rw [a', smul_zero]

theorem values_killed : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ θ : InfFam D, IsInfFam θ → ∀ (Sp : D.what₂.Tau → SPar) (M : DSModel T Sp), LowSm M → GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType.LowIrr M → ∀ c : CoefA S, c.Is → ∀ pt : PolF D T.rank S.rank →ₗ[ℂ] (WO S T → ℂ), (∀ P, IsThetaFunO ψ S T (pt P)) → ∀ (Δ : PolF D T.rank S.rank) (io : LowT M →ₗ[ℂ] c.W →ₗ[ℂ] PolF D T.rank S.rank), IsIoW θ M c om (fun P => pt P) Δ io → (∀ τ, ∀ Z ∈ GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicParabolicSmoothFunctions.pMinus M τ, ∀ h, RderC θ T τ Z (fun g => thetaKO om h g (pt Δ)) = 0) → ∀ τ, ∀ Z ∈ GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicParabolicSmoothFunctions.pMinus M τ, ∀ (v : ∀ ρ, lowT M ρ) w h, RderC θ T τ Z (fun g => thetaKO om h g (pt (io (PiTensorProduct.tprod ℂ v) w))) = 0 := by
  intro D ψ S T χS χT om hom θ hθ Sp M h1 h2 c hc pt hpt Δ io hio hΔ τ Z hZ v w h
  classical
  obtain ⟨hS, hK, v₀, w₀, hv₀, hw₀, e₀⟩ := hio
  beta_reduce at hS hK
  let N := killed hom hθ M pt hpt
  have step1 : ∀ w, io (PiTensorProduct.tprod ℂ v₀) w ∈ N := by
    obtain ⟨-, -, -, -, -, -, -, hd, -⟩ := GlobalTheory.RealLift.exists_real_lift D θ S hθ
    suffices hst : ∀ g, (N.comap (io (PiTensorProduct.tprod ℂ v₀))).map (c.ρ g) ≤
        N.comap (io (PiTensorProduct.tprod ℂ v₀)) by
      intro w
      refine (((hc.2.2.2.2 _ hst).resolve_left fun h0 => ?_).ge Submodule.mem_top :
        w ∈ N.comap (io (PiTensorProduct.tprod ℂ v₀)))
      have hm : w₀ ∈ N.comap (io (PiTensorProduct.tprod ℂ v₀)) := by
        show io (PiTensorProduct.tprod ℂ v₀) w₀ ∈ N
        rw [e₀]
        exact hΔ
      rw [h0, Submodule.mem_bot] at hm
      rw [hm, norm_zero] at hw₀
      exact zero_ne_one hw₀
    · rintro g _ ⟨x, hx, rfl⟩
      obtain ⟨a, ha, u, hu, rfl⟩ := hd g
      intro τ Z hZ h
      have e : (fun g => thetaKO om h g (pt (io (PiTensorProduct.tprod ℂ v₀) (c.ρ (a * u) x)))) =
          fun g => thetaKO om (h * u) g (pt (io (PiTensorProduct.tprod ℂ v₀) x)) := by
        funext g
        rw [map_mul, hc.1 a ha, one_mul, ← hS u hu]
        unfold thetaKO
        rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
      rw [e]
      exact hx τ Z hZ (h * u)
  let B : MultilinearMap (RingHom.id ℂ) (fun τ => lowT M τ) (PolF D T.rank S.rank) :=
    (io.flip w).compMultilinearMap (PiTensorProduct.tprod ℂ)
  refine mem_of_translates h1 h2 B N v₀ (fun ρ h0 => ?_) (step1 w) ?_ v τ Z hZ h
  · have := hv₀ ρ
    rw [h0] at this
    simp at this
  · intro ρ k hk v u hu hv τ Z hZ h
    have e : (fun g => thetaKO om h g (pt (B (Function.update v ρ u)))) =
        rTr T (atTau θ T ρ ((M.fr ρ)⁻¹ * k * M.fr ρ)) fun g => thetaKO om h g (pt (B v)) := by
      funext g
      have := hK ρ k hk v u hu w
      show om (h, g) (pt (io (PiTensorProduct.tprod ℂ (Function.update v ρ u)) w)) 0 =
        om (h, g * atTau θ T ρ ((M.fr ρ)⁻¹ * k * M.fr ρ)) (pt (io (PiTensorProduct.tprod ℂ v) w)) 0
      rw [← this, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
    rw [e, RderC_rTr hθ (isRealPt_atTau hθ ρ (frame_mem_UH M ρ hk)), hv τ _ (adAt_mem_pMinus hθ M ρ τ hk hZ) h]
    rfl

end GlobalTheory.DefLift.LowerKill

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.SRe



theorem evalOn_all : GlobalTheory.Dec.DSInfChar → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesUpqUnique → Formalism.L2.SG.RowsDef.RowsFinDim → ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : GA D (D.sp.Y 0)), (∀ x : X.B.I.E, HEq (X.ιE x) x) → GapHyp D → R.toLevCh.Is A.μ0 → R.models_inf → R.models_ν0 → SeeAt R F X h t → ∃ v₀ : (MP R).Vec, (∀ τ, ‖(v₀ τ : (MP R).H τ)‖ = 1) ∧ ∃ c : ℝ, 0 < c ∧ EvalOn R X h t v₀ c (MultR R F) (conjRows X) := by
  intro hDS hCusp hU hFin D G' _ _ Pl0 T A Ks _ _ _ R F X h t hE hGap hl hi hν hsee
  obtain ⟨cc, hcc, hsm⟩ := GlobalTheory.T.contragredientModel_conjDiscreteSeries_of_gap hDS hCusp hU hFin D G' Pl0 T A Ks R F X h t hE hGap hl hi hν hsee
  let v₀ : (MP R).Vec := fun τ => ⟨(cc τ).symm (X.B.w (X.pl.symm τ)), hsm τ⟩
  have hv₀ : ∀ τ, cc τ (v₀ τ : (MP R).H τ) = X.B.w (X.pl.symm τ) := fun τ => by simp [v₀]
  have hnorm : ∀ τ, ‖(v₀ τ : (MP R).H τ)‖ = 1 := fun τ => by
    show ‖(cc τ).symm (X.B.w (X.pl.symm τ))‖ = 1
    rw [LinearIsometryEquiv.norm_map]
    exact (X.low _).1
  obtain ⟨c0, hc0, hN⟩ := GlobalTheory.T.translatedEvaluation_squareIntegrable_norm_all_rows hDS hCusp hU hFin D G' Pl0 T A Ks R F X h t hE hGap hl hi hν hsee
  have hI := GlobalTheory.T.conj_translated_level_row_evaluation_mem_all_rows hDS hCusp hU hFin D G' Pl0 T A Ks R F X h t hE hGap hl hi hν hsee cc v₀ hcc hv₀
  have hO := GlobalTheory.T.exists_rowLevel_translatedEvaluation_of_conj_row hDS hCusp hU hFin D G' Pl0 T A Ks R F X h t hE hGap hl hi hν hsee cc v₀ hcc hv₀
  refine ⟨v₀, hnorm, c0, hc0, ?_⟩
  classical
  have hmem : ∀ S : MultR R F, MemLp (fun x => ev (MP R) v₀ (S : MMap (MP R)) ((iotaX X h).symm x * t)) 2 (muX X) :=
    fun S => (hN v₀ hnorm S S.2).1
  let Φ : MultR R F → conjRows X := fun S =>
    ⟨(hmem S).toLp _, hI S S.2 _ (hmem S).coeFn_toLp⟩
  have hΦ : ∀ S, ((Φ S : conjRows X) : L2X X) =ᵐ[muX X]
      (fun x => ev (MP R) v₀ (S : MMap (MP R)) ((iotaX X h).symm x * t)) := fun S => (hmem S).coeFn_toLp
  have key : ∀ (S : MultR R F) (Fx : conjRows X), ((Fx : L2X X) =ᵐ[muX X]
      fun x => ev (MP R) v₀ (S : MMap (MP R)) ((iotaX X h).symm x * t)) → Φ S = Fx := by
    intro S Fx hF
    apply Subtype.ext
    apply Lp.ext
    exact (hΦ S).trans hF.symm
  let L : MultR R F →ₗ[ℂ] conjRows X :=
    { toFun := Φ
      map_add' := fun S S' => by
        apply key
        have h1 := hΦ S
        have h2 := hΦ S'
        have h3 := Lp.coeFn_add ((Φ S : conjRows X) : L2X X) ((Φ S' : conjRows X) : L2X X)
        refine (Filter.EventuallyEq.trans ?_ (h3.trans (h1.add h2))).trans ?_
        · simp only [Submodule.coe_add]; rfl
        · refine Filter.Eventually.of_forall fun x => ?_
          simp [ev_apply]
      map_smul' := fun a S => by
        rw [RingHom.id_apply]
        apply key
        have h1 := hΦ S
        have h3 := Lp.coeFn_smul a ((Φ S : conjRows X) : L2X X)
        refine (Filter.EventuallyEq.trans ?_ (h3.trans (h1.const_smul a))).trans ?_
        · simp only [Submodule.coe_smul]; rfl
        · refine Filter.Eventually.of_forall fun x => ?_
          simp [ev_apply] }
  have hLn : ∀ S : MultR R F, ‖((L S : conjRows X) : L2X X)‖ ^ 2 =
      c0 * (ipM (MP R) R.ν0 R.fd0 (S : MMap (MP R)) (S : MMap (MP R))).re := by
    intro S
    show ‖((hmem S).toLp _ : L2X X)‖ ^ 2 = _
    rw [Formalism.IndefR.AutomorphicEvaluation.norm_sq_toLp (hmem S)]
    exact (hN v₀ hnorm S S.2).2.1
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro S hS
    have h1 := hLn S
    rw [hS] at h1
    simp only [ZeroMemClass.coe_zero, norm_zero, zero_pow two_ne_zero] at h1
    have h2 := (mul_eq_zero_iff_left hc0.ne').mp h1.symm
    exact Subtype.ext ((hN v₀ hnorm S S.2).2.2 h2)
  have hsurj : Function.Surjective L := by
    intro Fx
    obtain ⟨S, hS, hF⟩ := hO (Fx : L2X X) Fx.2
    exact ⟨⟨S, hS⟩, key ⟨S, hS⟩ Fx hF⟩
  refine ⟨LinearEquiv.ofBijective L ⟨hinj, hsurj⟩, fun S => ⟨hΦ S, hLn S⟩⟩

end GlobalTheory.Mem.SRe
end
end
