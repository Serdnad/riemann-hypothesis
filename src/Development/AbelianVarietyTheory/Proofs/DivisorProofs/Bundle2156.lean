module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2114
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EventuallyAlgebraMapMemIntegers
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2130
public import Development.AbelianVarietyTheory.BlockTheory.AdelicCMFields.UnitaryHeckeCharacterIdele
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle238
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFiniteMeasureQuotMeasure
import Formalism.LocalToGlobal.IndefiniteReal.Bundle014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle243
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1194
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2127
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2129
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle057
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle056
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Definitions.Divisors.MapSmulOfIsHausdorff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff

@[expose] public section

section

noncomputable section

namespace GlobalTheory.ThK.ConeEuler

open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.ConeEuler
open GlobalTheory.Doubling (absE absEv unitFin ideleAt)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem eventually_compFin_mem_intLoc_adele (z : AE F E) :
    ∀ᶠ v : Pl F in cofinite, compFin F E v z ∈ intLoc F E v := by
  induction z using TensorProduct.induction_on with
  | zero => exact Eventually.of_forall fun v => by rw [map_zero]; exact zero_mem _
  | add y z hy hz =>
    filter_upwards [hy, hz] with v h h'
    rw [map_add]
    exact add_mem h h'
  | tmul a e =>
    filter_upwards [a.2.2, eventually_one_tmul_mem_intLoc (F := F) e] with v h h'
    have := mul_mem (tmul_mem_intLoc (a := evFin F v a) h (1 : 𝓞 E)) h'
    change evFin F v a ⊗ₜ[F] e ∈ _
    simpa using this


omit [NumberField E] in
theorem compFin_unitAt_self (v : Pl F) (l : (AE F E)ˣ) :
    compFin F E v (unitAt E v l : AE F E) = compFin F E v l := by
  change compFin F E v (eFin v • (l : AE F E) + (1 - eFin v) • 1) = _
  have h : evFin F v (eFin v) = 1 := GlobalTheory.LatVac.evFin_liftV v 1
  rw [map_add (f := _), compFin_smul, compFin_smul, map_sub, map_one, h, sub_self, zero_smul, one_smul, add_zero]

theorem eventually_unitAt_mem_unitsAt (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (l : (AE F E)ˣ) : ∀ᶠ v in cofinite, unitAt E v l ∈ unitsAt E v := by
  filter_upwards [eventually_compFin_mem_intLoc_adele (l : AE F E),
    eventually_compFin_mem_intLoc_adele ((l⁻¹ : (AE F E)ˣ) : AE F E)] with v h h'
  refine mem_unitsAt.2 ⟨unitAt_mem v l, ?_, ?_⟩
  · rwa [compFin_unitAt_self]
  · rwa [← map_inv, compFin_unitAt_self]

end GlobalTheory.ThK.ConeEuler

end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.InertCoord
open scoped TensorProduct Matrix

namespace GlobalTheory.InertCoordAct

theorem at_mul_left {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {v : Pl (F := F)}
    (a : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) {z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)} (hz : At (evFin F v) z) : At (evFin F v) (a * z) := fun u hu => by
  rw [← mul_smul_comm, hz u hu, mul_zero]

theorem at_mul_right {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {v : Pl (F := F)}
    (a : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) {z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)} (hz : At (evFin F v) z) : At (evFin F v) (z * a) := fun u hu => by
  rw [← smul_mul_assoc, hz u hu, zero_mul]

theorem at_sum {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {v : Pl (F := F)}
    {ι : Type} (s : Finset ι) (f : ι → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (hf : ∀ i, At (evFin F v) (f i)) :
    At (evFin F v) (∑ i ∈ s, f i) := fun u hu => by
  rw [Finset.smul_sum]; exact Finset.sum_eq_zero fun i _ => hf i u hu

theorem act_kap : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (v : Pl (F := F))
    (w : HeightOneSpectrum (𝓞 E)) (hw : Formalism.UG.IsInertAt F E v w) (h : w.under (𝓞 F) = v) {n d : ℕ}
    (X : Spc F E n) (Y : Spc F E d) (A : GL (Fin n) (w.adicCompletion E)) (Bm : GL (Fin d) (w.adicCompletion E))
    (g₁ : UA σ X.J) (g₂ : UA σ Y.J), g₁ ∈ UAt σ X (evFin F v) → g₂ ∈ UAt σ Y (evFin F v) → ∀ x,
      actAB (cA σ) (g₁, g₂) (kap hw h (A : Matrix (Fin n) (Fin n) (w.adicCompletion E)) (Bm : Matrix (Fin d) (Fin d) (w.adicCompletion E)) x) =
        kap hw h (A : Matrix (Fin n) (Fin n) (w.adicCompletion E)) (Bm : Matrix (Fin d) (Fin d) (w.adicCompletion E))
          ((((Bm⁻¹ : GL (Fin d) (w.adicCompletion E)) : Matrix (Fin d) (Fin d) (w.adicCompletion E)) * (mat g₂).map (locW h) *
              (Bm : Matrix (Fin d) (Fin d) (w.adicCompletion E))) * x *
            (((A⁻¹ : GL (Fin n) (w.adicCompletion E)) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) * (mat g₁).map (locW h) *
              (A : Matrix (Fin n) (Fin n) (w.adicCompletion E)))ᵀ) := by
  intro F E _ _ _ _ _ σ v w hw h n d X Y A Bm g₁ g₂ _ _ x
  set P : Matrix (Fin n) (Fin d) (w.adicCompletion E) := (A : Matrix (Fin n) (Fin n) (w.adicCompletion E)) * xᵀ * (Bm : Matrix (Fin d) (Fin d) (w.adicCompletion E))ᵀ with hP
  have hK : kap hw h (A : Matrix (Fin n) (Fin n) (w.adicCompletion E)) (Bm : Matrix (Fin d) (Fin d) (w.adicCompletion E)) x = P.map (ptAt hw h) := kap_apply hw h _ _ x
  have hmm : (P.map (ptAt hw h)).map (locW h) = P := by
    rw [Matrix.map_map]; exact Matrix.ext fun i j => locW_ptAt hw h _
  rw [hK, kap_apply]
  simp only [actAB]
  change mat g₁ * P.map (ptAt hw h) * (mat g₂)ᵀ = _
  have hat : ∀ i j, At (evFin F v) ((mat g₁ * P.map (ptAt hw h) * (mat g₂)ᵀ) i j) := fun i j => by
    simp only [Matrix.mul_apply]
    refine at_sum _ _ fun k => at_mul_right _ (at_sum _ _ fun l => at_mul_left _ (at_ptAt hw h _))
  have e1 : mat g₁ * P.map (ptAt hw h) * (mat g₂)ᵀ =
      ((mat g₁ * P.map (ptAt hw h) * (mat g₂)ᵀ).map (locW h)).map (ptAt hw h) := by
    exact Matrix.ext fun i j => (ptAt_locW hw h (hat i j)).symm
  rw [e1]
  congr 1
  rw [Matrix.map_mul, Matrix.map_mul, hmm, Matrix.transpose_map, hP]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  have hB : (((Bm⁻¹ : GL (Fin d) (w.adicCompletion E)) : Matrix (Fin d) (Fin d) (w.adicCompletion E)))ᵀ *
      ((Bm : Matrix (Fin d) (Fin d) (w.adicCompletion E)))ᵀ = 1 := by
    rw [← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.transpose_one]
  have hA : (A : Matrix (Fin n) (Fin n) (w.adicCompletion E)) * ((A⁻¹ : GL (Fin n) (w.adicCompletion E)) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [hB, Matrix.mul_one, ← Matrix.mul_assoc (A : Matrix (Fin n) (Fin n) (w.adicCompletion E)) ((A⁻¹ : GL (Fin n) (w.adicCompletion E)) : Matrix (Fin n) (Fin n) (w.adicCompletion E)), hA, Matrix.one_mul]

end GlobalTheory.InertCoordAct
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.InertCoord
open scoped TensorProduct Matrix

namespace GlobalTheory.InertCoord

theorem kap_at_and_onto : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : Pl (F := F))
    (w : HeightOneSpectrum (𝓞 E)) (hw : Formalism.UG.IsInertAt F E v w) (h : w.under (𝓞 F) = v) {m n : ℕ}
    (A : GL (Fin m) (w.adicCompletion E)) (Bm : GL (Fin n) (w.adicCompletion E)),
    (∀ x, At (evFin F v) (kap hw h (A : Matrix (Fin m) (Fin m) (w.adicCompletion E)) (Bm : Matrix (Fin n) (Fin n) (w.adicCompletion E)) x)) ∧
    ∀ γ : Matrix (Fin m) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) γ →
      ∃ x, kap hw h (A : Matrix (Fin m) (Fin m) (w.adicCompletion E)) (Bm : Matrix (Fin n) (Fin n) (w.adicCompletion E)) x = γ := by
  intro F E _ _ _ _ _ v w hw h m n A Bm
  refine ⟨fun x u hu => ?_, fun γ hγ => ?_⟩
  · ext i j
    rw [Matrix.smul_apply, kap_apply, Matrix.map_apply, Matrix.zero_apply]
    exact at_ptAt hw h _ u hu
  · refine ⟨(((A⁻¹ : GL (Fin m) (w.adicCompletion E)) : Matrix (Fin m) (Fin m) (w.adicCompletion E)) * γ.map (locW h) *
        ((((Bm⁻¹ : GL (Fin n) (w.adicCompletion E)) : Matrix (Fin n) (Fin n) (w.adicCompletion E)))ᵀ))ᵀ, ?_⟩
    rw [kap_apply, Matrix.transpose_transpose]
    have e : (A : Matrix (Fin m) (Fin m) (w.adicCompletion E)) *
        (((A⁻¹ : GL (Fin m) (w.adicCompletion E)) : Matrix (Fin m) (Fin m) (w.adicCompletion E)) * γ.map (locW h) *
        ((((Bm⁻¹ : GL (Fin n) (w.adicCompletion E)) : Matrix (Fin n) (Fin n) (w.adicCompletion E)))ᵀ)) *
        (Bm : Matrix (Fin n) (Fin n) (w.adicCompletion E))ᵀ = γ.map (locW h) := by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.transpose_one, Matrix.mul_one, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.one_mul]
    rw [e]
    ext i j
    rw [Matrix.map_apply, Matrix.map_apply]
    refine ptAt_locW hw h fun u hu => ?_
    have := congrFun (congrFun (hγ u hu) i) j
    rwa [Matrix.smul_apply, Matrix.zero_apply] at this

end GlobalTheory.InertCoord
end

section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)
open Formalism.UG (cT bc)

noncomputable section

namespace GlobalTheory.GLOneVol

open GroundTheory.Global GroundTheory.Global.AdeleBaseChange GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele GlobalTheory.IdeleCovolume GlobalTheory.OneRep.SplitTwist

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem idl_det_eq (k : ℕ) (g : GL (Fin k) (AF F ⊗[F] E)) :
    GlobalTheory.TateConv.idl F E (Matrix.GeneralLinearGroup.det g) = Matrix.GeneralLinearGroup.det (glTens F E k g) := by
  ext
  change GlobalTheory.TateConv.tens F E (g : Matrix (Fin k) (Fin k) (AF F ⊗[F] E)).det =
    ((GlobalTheory.TateConv.tens F E).toRingEquiv.toRingHom.mapMatrix (g : Matrix (Fin k) (Fin k) (AF F ⊗[F] E))).det
  exact RingHom.map_det (GlobalTheory.TateConv.tens F E).toRingEquiv.toRingHom _

variable [_root_.NumberField.IsTotallyComplex E]

theorem absE_det_cR (k : ℕ) (t : ℝ) :
    ((absE F E (Matrix.GeneralLinearGroup.det (cR F E k t)) : ℝ≥0) : ℝ) =
      ideleNorm (E := E) (Matrix.GeneralLinearGroup.det (GlobalTheory.UnitaryBC.splitCentre E k t)) := by
  rw [GlobalTheory.TateConv.absE_eq, idl_det_eq, glTens_cR]
  rfl

end GlobalTheory.GLOneVol

theorem GlobalTheory.GLOneVol.log_absE_det_cR : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [_root_.NumberField.IsTotallyComplex E] (k : ℕ), 1 ≤ k → ∃ a : ℝ, a ≠ 0 ∧ ∀ t : ℝ,
      Real.log ((absE F E (Matrix.GeneralLinearGroup.det (GlobalTheory.GLOneVol.cR F E k t)) : ℝ≥0) : ℝ) = a * t := by
  intro F E _ _ _ _ _ _ k hk
  let D : ℝ →+ ℝ := AddMonoidHom.mk'
    (fun t => Real.log (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleNorm (E := E)
      (Matrix.GeneralLinearGroup.det (GlobalTheory.UnitaryBC.splitCentre E k t)))) fun x y => by
      rw [GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_add, map_mul, map_mul,
        Real.log_mul (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleNorm_ne_zero _) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleNorm_ne_zero _)]
  have hD : Continuous D :=
    (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.continuous_ideleNorm.comp (Matrix.GeneralLinearGroup.continuous_det.comp
      GlobalTheory.OneRep.SplitTwist.continuous_splitCentre)).log fun _ => GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleNorm_ne_zero _
  have hDt : ∀ t, D t = t * D 1 := fun t => by simpa using map_real_smul D hD t 1
  have hD1 : 0 < D 1 := by
    change 0 < Real.log (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleNorm (E := E)
      (Matrix.GeneralLinearGroup.det (GlobalTheory.UnitaryBC.splitCentre E k 1)))
    rw [GlobalTheory.CuspRep.CuspidalL2GL.det_splitCentre_one, map_pow, Real.log_pow]
    exact mul_pos (by exact_mod_cast hk) (Real.log_pos (GlobalTheory.IdeleCovolume.one_lt_ideleNorm_eIdele E))
  refine ⟨D 1, hD1.ne', fun t => ?_⟩
  rw [GlobalTheory.GLOneVol.absE_det_cR, mul_comm]
  exact hDt t
end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.InertCoord
open scoped TensorProduct Matrix
noncomputable section
namespace GlobalTheory.InertTens

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem quadruple_sum_eq_trace_transpose_mul {L : Type} [CommRing L] {m n : ℕ} (P : Matrix (Fin m) (Fin n) L) (J : Matrix (Fin m) (Fin m) L)
    (K : Matrix (Fin n) (Fin n) L) (Q : Matrix (Fin m) (Fin n) L) :
    ∑ i, ∑ j, ∑ k, ∑ l, P i j * J i k * K j l * Q k l = (Pᵀ * J * Q * Kᵀ).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  refine (Finset.sum_congr rfl fun k _ => Finset.sum_comm).trans ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  ring

theorem trace_orth {L : Type} [Field L] (σL : L →+* L) {m n : ℕ} (J : Matrix (Fin m) (Fin m) L) (K : Matrix (Fin n) (Fin n) L)
    (A : Matrix (Fin m) (Fin m) L) (Bm : Matrix (Fin n) (Fin n) L) (δ : L)
    (hA : Aᵀ * J * A.map σL = 1) (hB : Bmᵀ * K * Bm.map σL = δ • 1) (x y : Matrix (Fin n) (Fin m) L) :
    ((A * xᵀ * Bmᵀ)ᵀ * J * (A * yᵀ * Bmᵀ).map σL * Kᵀ).trace = δ * ((y.map σL)ᵀ * x).trace := by
  have e1 : (A * yᵀ * Bmᵀ).map σL = A.map σL * (y.map σL)ᵀ * (Bm.map σL)ᵀ := by
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, Matrix.transpose_map]
  have e2 : (Bm.map σL)ᵀ * Kᵀ * Bm = δ • 1 := by
    have := congrArg Matrix.transpose hB
    simpa [Matrix.transpose_mul, Matrix.mul_assoc] using this
  rw [e1]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
  have e3 : Bm * (x * Aᵀ) * J * (A.map σL * (y.map σL)ᵀ * (Bm.map σL)ᵀ) * Kᵀ
      = Bm * (x * (Aᵀ * J * A.map σL) * (y.map σL)ᵀ * ((Bm.map σL)ᵀ * Kᵀ)) := by
    simp only [Matrix.mul_assoc]
  rw [e3, hA, Matrix.trace_mul_comm, Matrix.mul_one]
  have e4 : x * (y.map σL)ᵀ * ((Bm.map σL)ᵀ * Kᵀ) * Bm = x * (y.map σL)ᵀ * ((Bm.map σL)ᵀ * Kᵀ * Bm) := by
    simp only [Matrix.mul_assoc]
  rw [e4, e2, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul, smul_eq_mul, Matrix.trace_mul_comm]

theorem hTens_kap (σ : E →ₐ[F] E) {v : Pl (F := F)} {w : HeightOneSpectrum (𝓞 E)} (hw : Formalism.UG.IsInertAt F E v w)
    (h : w.under (𝓞 F) = v) {σL : w.adicCompletion E →+* w.adicCompletion E} (hc : IsConjAt σ h σL)
    {m n : ℕ} (JA : Matrix (Fin m) (Fin m) E) (JB : Matrix (Fin n) (Fin n) E)
    (A : Matrix (Fin m) (Fin m) (w.adicCompletion E)) (Bm : Matrix (Fin n) (Fin n) (w.adicCompletion E))
    (x y : Matrix (Fin n) (Fin m) (w.adicCompletion E)) :
    hTens (cA σ) (incM F JA) (incM F JB) (kap hw h A Bm x) (kap hw h A Bm y) =
      ptAt hw h (∑ i, ∑ j, ∑ k, ∑ l, (A * xᵀ * Bmᵀ) i j * JA.map (algebraMap E (w.adicCompletion E)) i k *
        JB.map (algebraMap E (w.adicCompletion E)) j l * (A * yᵀ * Bmᵀ).map σL k l) := by
  have hr : ∀ (a : E) (z : w.adicCompletion E),
      ptAt hw h z * inclR (F := F) (AF F) a = ptAt hw h (z * algebraMap E (w.adicCompletion E) a) := by
    intro a z
    rw [mul_comm, inclR_mul_ptAt, mul_comm]

  simp only [hTens, incM, kap_apply, Matrix.map_apply, cA_ptAt hw h σ hc, hr, ← map_mul, map_sum]

end GlobalTheory.InertTens

namespace GlobalTheory.InertTens

theorem hTens_kap_eq_locH : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (v : Pl (F := F))
    (w : HeightOneSpectrum (𝓞 E)) (hw : Formalism.UG.IsInertAt F E v w) (h : w.under (𝓞 F) = v)
    (σL : w.adicCompletion E →+* w.adicCompletion E), IsConjAt σ h σL →
    ∀ {m n : ℕ} (JA : Matrix (Fin m) (Fin m) E) (JB : Matrix (Fin n) (Fin n) E) (A : Matrix (Fin m) (Fin m) (w.adicCompletion E))
      (Bm : Matrix (Fin n) (Fin n) (w.adicCompletion E)) (δ : w.adicCompletion E),
      Aᵀ * JA.map (algebraMap E (w.adicCompletion E)) * A.map σL = 1 →
      Bmᵀ * JB.map (algebraMap E (w.adicCompletion E)) * Bm.map σL = δ • 1 →
      ∀ x y, hTens (cA σ) (incM F JA) (incM F JB) (kap hw h A Bm x) (kap hw h A Bm y) =
        ptAt hw h (GlobalTheory.Hk3.locH σL δ (1 : GL (Fin m) (w.adicCompletion E)) (1 : GL (Fin n) (w.adicCompletion E)) x y) := by
  intro F E _ _ _ _ _ σ v w hw h σL hc m n JA JB A Bm δ hA hB x y
  rw [hTens_kap σ hw h hc, quadruple_sum_eq_trace_transpose_mul, trace_orth σL _ _ A Bm δ hA hB x y]
  congr 1
  simp [GlobalTheory.Hk3.locH]

end GlobalTheory.InertTens
end
end

section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)
open Formalism.UG (cT bc)

noncomputable section

namespace GlobalTheory.GLOneVol

open GroundTheory.Global GroundTheory.Global.AdeleBaseChange GlobalTheory.CuspRep.CuspidalL2GL

theorem symm_mem_latR {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [_root_.NumberField.IsTotallyComplex E] {k : ℕ} {g : GlobalTheory.CuspRep.GA E k} (hg : g ∈ GlobalTheory.UnitaryBC.latticeGL E k) :
    (glTens F E k).symm g ∈ latR F E k := by
  obtain ⟨γ, n, rfl⟩ := mem_latticeGL_iff.1 hg
  rw [map_mul, map_zpow]
  refine mul_mem (Subgroup.mem_sup_left ⟨γ, ?_⟩) (zpow_mem (Subgroup.mem_sup_right (Subgroup.mem_zpowers _)) n)
  apply (glTens F E k).injective
  rw [glTens_bc, ContinuousMulEquiv.apply_symm_apply]

def latEquiv (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [_root_.NumberField.IsTotallyComplex E] (k : ℕ) : GlobalTheory.UnitaryBC.latticeGL E k ≃ latR F E k where
  toFun g := ⟨(glTens F E k).symm g, symm_mem_latR g.2⟩
  invFun x := ⟨glTens F E k x, latR_le k x.2⟩
  left_inv g := Subtype.ext ((glTens F E k).apply_symm_apply _)
  right_inv x := Subtype.ext ((glTens F E k).symm_apply_apply _)

theorem finvol_tens : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [_root_.NumberField.IsTotallyComplex E] (k : ℕ) [MeasurableSpace (GL (Fin k) (AF F ⊗[F] E))]
    [BorelSpace (GL (Fin k) (AF F ⊗[F] E))] (ν : Measure (GL (Fin k) (AF F ⊗[F] E)))
    (D : Set (GL (Fin k) (AF F ⊗[F] E))), ν.IsHaarMeasure → IsFundamentalDomain (latR F E k) D ν → ν D ≠ ⊤ := by
  intro F E _ _ _ _ _ _ k _ _ ν D hν hD
  haveI : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  let f := (glTens F E k).toHomeomorph.toMeasurableEquiv
  let μ : Measure (GlobalTheory.CuspRep.GA E k) := ν.map f
  haveI : μ.IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map ν (glTens F E k)
  have hq : Measure.QuasiMeasurePreserving f.symm μ ν :=
    (MeasurePreserving.mk f.symm.measurable (f.map_symm_map)).quasiMeasurePreserving
  have hD' : IsFundamentalDomain (GlobalTheory.UnitaryBC.latticeGL E k) (f '' D) μ :=
    hD.image_of_equiv f.toEquiv hq (latEquiv F E k) fun g x => by
      change glTens F E k ((glTens F E k).symm g * x) = g * glTens F E k x
      rw [map_mul, ContinuousMulEquiv.apply_symm_apply]
  have h1 : ν D = μ (f '' D) := by
    rw [f.map_apply, f.preimage_image]
  rw [h1, ← GlobalTheory.AutomorphicL2Unitary.quotMeasure_univ hD']
  haveI := (GlobalTheory.CovolGL.finvol E k μ).1
  exact measure_ne_top _ _

end GlobalTheory.GLOneVol
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SectionLattice

theorem mem_pull_chart_iff {X Y : Scheme.{0}} (L : LB X) (f : Y ⟶ X) (j : (L.pull f).ι) (y : Y) :
    y ∈ (L.pull f).U j ↔ f.base y ∈ L.U (j PUnit.unit) :=
  ⟨fun h => Set.mem_iInter.1 h PUnit.unit, fun h => Set.mem_iInter.2 fun _ => h⟩

theorem exists_chart_of_isLocalRing {R : Type} [CommRing R] [IsLocalRing R] {X : Scheme.{0}}
    (L : LB X) (hL : L.IsLB) (e : Spec (CommRingCat.of R) ⟶ X) : ∃ m : L.ι, ⊤ ≤ e ⁻¹ᵁ L.U m := by
  have h : e.base (IsLocalRing.closedPoint R) ∈ (⨆ i, L.U i) := by rw [hL.cover]; trivial
  obtain ⟨m, hm⟩ := TopologicalSpace.Opens.mem_iSup.1 h
  refine ⟨m, ?_⟩
  have := (IsLocalRing.closedPoint_mem_iff (R := R) (e ⁻¹ᵁ L.U m)).1 hm
  exact this.ge

theorem integralAtSection_of_conj : ∀ (W K' : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field K'] [Algebra W K'] [IsFractionRing W K'] (G : Over (Sp W)) (σ : K' ≃+* K') (τ : W →+* W), (∀ l : K', l ≠ 0 → ∃ a : W, σ l = algebraMap W K' a * l) → ∀ (φ : G.left ⟶ G.left) (e₀ : Sp W ⟶ G.left), e₀ ≫ G.hom = 𝟙 _ → e₀ ≫ φ = spMap τ ≫ e₀ → ∀ (ρ : pullback G.hom (spMap (algebraMap W K')) ⟶ pullback G.hom (spMap (algebraMap W K'))) (x : Sp K' ⟶ pullback G.hom (spMap (algebraMap W K'))), x ≫ pullback.fst G.hom (spMap (algebraMap W K')) = spMap (algebraMap W K') ≫ e₀ → x ≫ pullback.snd G.hom (spMap (algebraMap W K')) = 𝟙 _ → x ≫ ρ = spMap (σ : K' →+* K') ≫ x → ∀ (M : LB G.left) (N : LB (pullback G.hom (spMap (algebraMap W K')))), M.IsLB → N.IsLB → ∀ (w : LB.Iso (M.pull (pullback.fst G.hom (spMap (algebraMap W K')))) N) (w₁ : LB.Iso ((M.pull φ).pull (pullback.fst G.hom (spMap (algebraMap W K')))) N), (∀ (n : N.ι) (i : ((M.pull φ).pull (pullback.fst G.hom (spMap (algebraMap W K')))).ι) (h : ⊤ ≤ x ⁻¹ᵁ (N.U n ⊓ ((M.pull φ).pull (pullback.fst G.hom (spMap (algebraMap W K')))).U i)) (h' : ⊤ ≤ x ⁻¹ᵁ (N.U n ⊓ (M.pull (pullback.fst G.hom (spMap (algebraMap W K')))).U (fun _ => i PUnit.unit PUnit.unit))), (Scheme.ΓSpecIso (CommRingCat.of K')).hom.hom ((x.appLE _ ⊤ h).hom (w₁.s (n, i)).val) = σ ((Scheme.ΓSpecIso (CommRingCat.of K')).hom.hom ((x.appLE _ ⊤ h').hom (w.s (n, fun _ => i PUnit.unit PUnit.unit)).val))) → GlobalTheory.SectionLattice.IntegralAtSection G.hom w w₁ := by
  intro W K' _ _ _ _ _ _ G σ τ hσ φ e₀ he₀ hφ ρ x hx₁ hx₂ _ M N hM hN w w₁ H
  obtain ⟨m, hm⟩ := exists_chart_of_isLocalRing M hM e₀
  obtain ⟨n, hn⟩ := exists_chart_of_isLocalRing N hN x
  have hi : ⊤ ≤ e₀ ⁻¹ᵁ (M.pull φ).U (fun _ => m) := by
    intro y _
    change e₀.base y ∈ (M.pull φ).U (fun _ => m)
    refine (mem_pull_chart_iff _ _ _ _).2 ?_
    have h1 : φ.base (e₀.base y) = e₀.base ((spMap τ).base y) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hφ]
    rw [h1]
    exact hm (TopologicalSpace.Opens.mem_top _)
  have key : ∀ (P : LB G.left) (i : P.ι), ⊤ ≤ e₀ ⁻¹ᵁ P.U i →
      ⊤ ≤ x ⁻¹ᵁ (N.U n ⊓ (P.pull (pullback.fst G.hom (spMap (algebraMap W K')))).U (fun _ => i)) := by
    intro P i hP y hy
    refine ⟨hn hy, ?_⟩
    change x.base y ∈ (P.pull (pullback.fst G.hom (spMap (algebraMap W K')))).U (fun _ => i)
    refine (mem_pull_chart_iff _ _ _ _).2 ?_
    have h1 : (pullback.fst G.hom (spMap (algebraMap W K'))).base (x.base y) =
        e₀.base ((spMap (algebraMap W K')).base y) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hx₁]
    rw [h1]
    exact hP (TopologicalSpace.Opens.mem_top _)
  have h₁ := key (M.pull φ) (fun _ => m) hi
  have h₂ := key M m hm
  have hw := H n (fun _ _ => m) h₁ h₂
  have hu : IsUnit ((Scheme.ΓSpecIso (CommRingCat.of K')).hom.hom
      ((x.appLE _ ⊤ h₂).hom (w.s (n, fun _ => m)).val)) :=
    ((Units.isUnit _).map _).map _
  obtain ⟨a, ha⟩ := hσ _ hu.ne_zero
  exact ⟨e₀, he₀, x, hx₁, hx₂, fun _ => m, m, n, hi, hm, h₁, h₂, a, hw.trans ha⟩

end GlobalTheory.SectionLattice
end
end

section

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix RealInnerProductSpace
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open scoped Classical

theorem _root_.GlobalTheory.T.exists_archimedean_phaseSpace_coordinates_frames : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : ℕ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (JB : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (a b : ℂ) (A : InfinitePlace F → Matrix α (Ix P Q) ℂ)
    (C : InfinitePlace F → Matrix β (Ix R S) ℂ), IsCMExt F E σ → Framed τ JA JB a b A C →
    ∃ (n : ℕ) (θ : (κ → mixedEmbedding.mixedSpace F) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
      (φ : (InfinitePlace F → Matrix (Ix P Q) (Ix R S) ℂ) ≃ₗ[ℝ] (Fin n ⊕ Fin n → ℝ))
      (φ₀ : ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) ≃ₗ[ℝ] (Fin n ⊕ Fin n → ℝ)),
      (∀ v, GlobalTheory.RealWeil.pPart (φ₀ v) = θ v.1) ∧ (∀ v y, ⟪GlobalTheory.RealWeil.qPart (φ₀ v), θ y⟫ = -GlobalTheory.ArchUniq.trP F κ y v.2) ∧
      (∀ c c', GlobalTheory.RealWeil.sympl (φ c) (φ c') = 2 * (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im) ∧
      ∀ (u : Matrix α β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (c : InfinitePlace F → Matrix (Ix P Q) (Ix R S) ℂ), At (evI F) u →
        (∀ w, u.map (piInf (τ w)) = A w * c w * (C w)ᵀ) →
          φ c = φ₀ (GlobalTheory.ArchUniq.locV (d.e u).1, GlobalTheory.ArchUniq.locV (d.e u).2) := by
  first | exact @GlobalTheory.ArchCoords.exists_coords | exact GlobalTheory.ArchCoords.exists_coords | (intros; apply GlobalTheory.ArchCoords.exists_coords <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.two_smul_picardClass_extends_abelianScheme : ∀ (S : Scheme.{0}) [IsIntegral S] [IsLocallyNoetherian S], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S → ∀ (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (U : S.Opens) (V : A.left.Opens), (U : Set S).Nonempty → (∀ s : S, ∃ x ∈ V, A.hom x = s) → ∀ c : Pic (A.hom ⁻¹ᵁ U ⊔ V).toScheme, GlobalTheory.CechPic.pull (A.left.homOfLE (le_sup_right : V ≤ A.hom ⁻¹ᵁ U ⊔ V)) c = 0 → ∃ c' : Pic A.left, GlobalTheory.CechPic.pull (A.hom ⁻¹ᵁ U ⊔ V).ι c' = 2 • c := by
  first | exact @GlobalTheory.DoubleClassExtension.two_smul_extends | exact GlobalTheory.DoubleClassExtension.two_smul_extends | (intros; apply GlobalTheory.DoubleClassExtension.two_smul_extends <;> assumption)
end
