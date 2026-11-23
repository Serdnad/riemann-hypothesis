module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle024
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle437
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle459
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamComparisonIsFiltered
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfForallMemFilV
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.DRMat

theorem toMatrix_qRep {l : ℕ} [Fact l.Prime] {Γ : Type} [Group Γ] {d : ℕ} (ρ : Γ →* GL (Fin d) ℤ_[l]) (g : Γ) :
    LinearMap.toMatrix (Pi.basisFun ℚ_[l] (Fin d)) (Pi.basisFun ℚ_[l] (Fin d)) (qRep ρ g) =
      (ρ g).val.map (algebraMap ℤ_[l] ℚ_[l]) := by
  rw [LinearMap.toMatrix_eq_toMatrix']
  change LinearMap.toMatrix' (Matrix.toLin' ((ρ g).val.map (algebraMap ℤ_[l] ℚ_[l]))) = _
  rw [LinearMap.toMatrix'_toLin']

theorem invariant_basis_of_isDR : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (d : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]), IsDR (P.PD K) (qRep ρ) → ∃ x : Fin d → Fin d → P.R.BdR, LinearIndependent ↥K.1 x ∧ (∀ j (g : ↥(GK K)), (ρ g).val.map (fun z : ℤ_[l] => algebraMap ℚ_[l] P.R.BdR (z : ℚ_[l])) *ᵥ (fun i => P.actQdR (g : GQ l) (x j i)) = x j) ∧ ∀ c : Fin d → P.R.BdR, (∀ g : ↥(GK K), (ρ g).val.map (fun z : ℤ_[l] => algebraMap ℚ_[l] P.R.BdR (z : ℚ_[l])) *ᵥ (fun i => P.actQdR (g : GQ l) (c i)) = c) → c ∈ Submodule.span ↥K.1 (Set.range x) := by
  intro l _ P AI T K d ρ hDR
  obtain ⟨Q, hQ⟩ := exists_period_matrix_of_isDR l P AI T (Fin d) K (Fin d → ℚ_[l])
    (Pi.basisFun ℚ_[l] (Fin d)) (qRep ρ) hDR
  set M : ↥(GK K) → Matrix (Fin d) (Fin d) P.R.BdR :=
    fun g => (ρ g).val.map (fun z : ℤ_[l] => algebraMap ℚ_[l] P.R.BdR (z : ℚ_[l])) with hM
  have hQ' : ∀ g : ↥(GK K), M g * (Q : Matrix (Fin d) (Fin d) P.R.BdR).map (P.actQdR (g : GQ l)) = Q := by
    intro g
    have h := hQ g
    rw [toMatrix_qRep, Matrix.map_map] at h
    exact h
  letI : Field P.R.BdR := (GlobalTheory.T.deRhamPeriodRing_field_tPow_filtration_units l P AI T).1.toField
  set Qm : Matrix (Fin d) (Fin d) P.R.BdR := (Q : Matrix (Fin d) (Fin d) P.R.BdR) with hQm
  have hQinj : ∀ v w : Fin d → P.R.BdR, Qm *ᵥ v = Qm *ᵥ w → v = w := by
    intro v w h
    have := congrArg (fun u => ((Q⁻¹ : GL (Fin d) P.R.BdR) : Matrix (Fin d) (Fin d) P.R.BdR) *ᵥ u) h
    simp only [Matrix.mulVec_mulVec, hQm] at this
    rwa [← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel, Matrix.GeneralLinearGroup.coe_one,
      Matrix.one_mulVec, Matrix.one_mulVec] at this
  refine ⟨fun j i => Qm i j, ?_, ?_, ?_⟩
  · rw [Fintype.linearIndependent_iff]
    intro c hc
    have hv : Qm *ᵥ (fun j => algebraMap ↥K.1 P.R.BdR (c j)) = Qm *ᵥ 0 := by
      rw [Matrix.mulVec_zero]
      funext i
      have := congrFun hc i
      simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply] at this
      simp only [Algebra.smul_def] at this
      rw [Pi.zero_apply, ← this]
      simp only [Matrix.mulVec, dotProduct]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    have h0 := hQinj _ _ hv
    intro j
    have := congrFun h0 j
    simp only [Pi.zero_apply] at this
    exact (FaithfulSMul.algebraMap_injective ↥K.1 P.R.BdR) (by rw [this, map_zero])
  · intro j g
    funext i
    have h := congrFun (congrFun (hQ' g) i) j
    simpa [hM, Matrix.mul_apply, Matrix.mulVec, dotProduct] using h
  · intro c hc
    obtain ⟨w, hw⟩ : ∃ w, Qm *ᵥ w = c :=
      ⟨((Q⁻¹ : GL (Fin d) P.R.BdR) : Matrix (Fin d) (Fin d) P.R.BdR) *ᵥ c, by
        rw [Matrix.mulVec_mulVec, hQm, ← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel,
          Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec]⟩
    have hfix : ∀ (g : ↥(GK K)) j, P.actQdR (g : GQ l) (w j) = w j := by
      intro g
      have key : Qm *ᵥ (fun j => P.actQdR (g : GQ l) (w j)) = Qm *ᵥ w := by
        have hact : (fun i => P.actQdR (g : GQ l) (c i)) =
            Qm.map (P.actQdR (g : GQ l)) *ᵥ (fun j => P.actQdR (g : GQ l) (w j)) := by
          funext i
          rw [← hw]
          exact RingHom.map_mulVec ((P.actQdR (g : GQ l) : P.R.BdR ≃ₐ[ℚ_[l]] P.R.BdR) : P.R.BdR →+* P.R.BdR) Qm w i
        have := hc g
        rw [hact, Matrix.mulVec_mulVec, hQ' g] at this
        rw [this, hw]
      exact congrFun (hQinj _ _ key)
    have hwK : ∀ j, ∃ k : ↥K.1, algebraMap ↥K.1 P.R.BdR k = w j := fun j =>
      (P.PD K).invdR (w j) fun g => by rw [P.PD_actdR]; exact hfix g j
    choose k hk using hwK
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨k, ?_⟩
    rw [← hw]
    funext i
    simp only [Finset.sum_apply, Pi.smul_apply, Matrix.mulVec, dotProduct]
    simp only [Algebra.smul_def, hk]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _

end GlobalTheory.DRMat
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.DRFilCoord
open Module

theorem deRham_filtered_Ql (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (TT : LocTied l P AI)
    (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V]
    (ρ : Representation ℚ_[l] ↥(GK K) V) (hdR : IsDR (P.PD K) ρ) (a : ℤ) (y : V ⊗[ℚ_[l]] P.R.BdR)
    (hy : y ∈ FilV (P.PD K) (LL := ℚ_[l]) (V := V) a) :
    ∃ (m : ℕ) (k : Fin m → ℤ) (b : Fin m → P.R.BdR) (d : Fin m → V ⊗[ℚ_[l]] P.R.BdR),
      (∀ i, d i ∈ DdR (P.PD K) ρ ∧ d i ∈ FilV (P.PD K) (LL := ℚ_[l]) (V := V) (k i) ∧
        b i ∈ (P.PD K).Fil (a - k i)) ∧
      y = ∑ i, AlgebraTensorModule.map (LinearMap.id : V →ₗ[ℚ_[l]] V) (LinearMap.mulLeft ℚ_[l] (b i)) (d i) := by
  let LL : FinExt l := ⟨⊥, inferInstance⟩
  let e : ↥LL.1 ≃ₐ[ℚ_[l]] ℚ_[l] := IntermediateField.botEquiv ℚ_[l] (Om l)
  letI iM : Module ↥LL.1 V := Module.compHom V (e : ↥LL.1 →+* ℚ_[l])
  haveI : IsScalarTower ℚ_[l] ↥LL.1 V := ⟨fun c x v => by
    show e (c • x) • v = c • (e x • v)
    have h1 := e.toLinearEquiv.map_smul c x
    simp only [AlgEquiv.toLinearEquiv_apply] at h1
    rw [h1, smul_eq_mul, mul_smul]⟩
  haveI : FiniteDimensional ↥LL.1 V := Module.Finite.of_restrictScalars_finite ℚ_[l] _ V
  let ρ' : Representation ↥LL.1 ↥(GK K) V :=
    { toFun := fun g =>
        { toFun := ρ g
          map_add' := fun u w => (ρ g).map_add u w
          map_smul' := fun c v => (ρ g).map_smul (e c) v }
      map_one' := by ext v; simp
      map_mul' := fun g h => by ext v; simp; rfl }
  have hV : finrank ↥LL.1 V = finrank ℚ_[l] V := by
    rw [← Module.finrank_mul_finrank ℚ_[l] ↥LL.1 V, IntermediateField.finrank_bot, one_mul]
  have hR : ∀ g x, actVdR (P.PD K) ρ' g x = actVdR (P.PD K) ρ g x := fun g x => by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v w => simp [actVdR]; rfl
    | add u w hu hw => simp only [map_add (f := _), hu, hw]
  have hD : ∀ x, x ∈ DdR (P.PD K) ρ' ↔ x ∈ DdR (P.PD K) ρ := fun x => by
    simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, hR]
  have hDd : (DdR (P.PD K) ρ').restrictScalars ℚ_[l] = DdR (P.PD K) ρ := by
    ext x
    rw [Submodule.restrictScalars_mem, hD]
  set_option synthInstance.maxHeartbeats 200000 in
  have hDr : finrank ↥LL.1 ↥(DdR (P.PD K) ρ') = finrank ℚ_[l] ↥(DdR (P.PD K) ρ) := by
    rw [← hDd, LinearEquiv.finrank_eq
      ((Submodule.restrictScalarsEquiv ℚ_[l] ↥LL.1 _ (DdR (P.PD K) ρ')).restrictScalars ℚ_[l]),
      ← Module.finrank_mul_finrank ℚ_[l] ↥LL.1 ↥(DdR (P.PD K) ρ'), IntermediateField.finrank_bot, one_mul]
  have hDR' : IsDR (P.PD K) ρ' := by
    unfold IsDR at hdR ⊢
    rw [hDr, hV]; exact hdR
  obtain ⟨m, k, b, d, h, hy'⟩ := GlobalTheory.DRFil.deRham_filtered l P AI TT K LL V ρ' hDR' a y hy
  exact ⟨m, k, b, d, fun i => ⟨(hD _).1 (h i).1, (h i).2.1, (h i).2.2⟩, hy'⟩

theorem filtered_coords : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (d : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]), IsDR (P.PD K) (qRep ρ) → ∀ (a : ℤ) (y : Fin d → P.R.BdR), (∀ i, y i ∈ (P.PD K).Fil a) → ∃ (m : ℕ) (k : Fin m → ℤ) (b : Fin m → P.R.BdR) (z : Fin m → Fin d → P.R.BdR), (∀ r, (∀ g : ↥(GK K), (ρ g).val.map (fun z : ℤ_[l] => algebraMap ℚ_[l] P.R.BdR (z : ℚ_[l])) *ᵥ (fun i => P.actQdR (g : GQ l) (z r i)) = z r) ∧ (∀ i, z r i ∈ (P.PD K).Fil (k r)) ∧ b r ∈ (P.PD K).Fil (a - k r)) ∧ y = ∑ r, b r • z r := by
  intro l _ P AI TT K d ρ hdR a y hy
  let f : (Fin d → ℚ_[l]) ⊗[ℚ_[l]] P.R.BdR →ₗ[ℚ_[l]] (Fin d → P.R.BdR) :=
    (TensorProduct.piScalarRight ℚ_[l] ℚ_[l] P.R.BdR (Fin d)).toLinearMap ∘ₗ
      (TensorProduct.comm ℚ_[l] (Fin d → ℚ_[l]) P.R.BdR).toLinearMap
  have hf : ∀ (v : Fin d → ℚ_[l]) (β : P.R.BdR), f (v ⊗ₜ β) = fun i => v i • β := by
    intro v β; simp [f]
  have hfmul : ∀ (β : P.R.BdR) (x : (Fin d → ℚ_[l]) ⊗[ℚ_[l]] P.R.BdR),
      f (AlgebraTensorModule.map (LinearMap.id : (Fin d → ℚ_[l]) →ₗ[ℚ_[l]] (Fin d → ℚ_[l]))
        (LinearMap.mulLeft ℚ_[l] β) x) = β • f x := by
    intro β x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v w =>
      simp only [AlgebraTensorModule.map_tmul, LinearMap.id_apply, LinearMap.mulLeft_apply, hf]
      funext i
      simp only [Pi.smul_apply, smul_eq_mul, Algebra.smul_def]
      ring
    | add u w hu hw => simp only [map_add (f := _), hu, hw, smul_add]
  have hfil : ∀ (c : ℤ) (x : (Fin d → ℚ_[l]) ⊗[ℚ_[l]] P.R.BdR),
      x ∈ FilV (P.PD K) (LL := ℚ_[l]) (V := Fin d → ℚ_[l]) c → ∀ i, f x i ∈ (P.PD K).Fil c := by
    intro c x hx i
    refine GlobalTheory.DRFil.FilV_induction (P.PD K) (p := fun x => f x i ∈ (P.PD K).Fil c) ?_ ?_ ?_ hx
    · simp
    · intro v β hβ
      rw [hf]
      exact (((P.PD K).Fil c).restrictScalars ℚ_[l]).smul_mem (v i) hβ
    · intro x x' h h'
      rw [map_add (f := _)]
      exact Submodule.add_mem _ h h'
  have hact : ∀ (g : ↥(GK K)) (x : (Fin d → ℚ_[l]) ⊗[ℚ_[l]] P.R.BdR),
      f (actVdR (P.PD K) (qRep ρ) g x) =
        (ρ g).val.map (fun z : ℤ_[l] => algebraMap ℚ_[l] P.R.BdR (z : ℚ_[l])) *ᵥ
          (fun i => P.actQdR (g : GQ l) (f x i)) := by
    intro g x
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero, Pi.zero_apply]; exact (Matrix.mulVec_zero _).symm
    | tmul v β =>
      have h1 : actVdR (P.PD K) (qRep ρ) g (v ⊗ₜ β) = qRep ρ g v ⊗ₜ P.actQdR (g : GQ l) β := by
        simp [actVdR, P.PD_actdR]
      rw [h1, hf, hf]
      funext i
      have hq : qRep ρ g v = ((ρ g).val.map (algebraMap ℤ_[l] ℚ_[l])) *ᵥ v := by
        simp [qRep, Matrix.toLin'_apply]
      rw [hq]
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Finset.sum_smul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, Algebra.smul_def, Algebra.smul_def, ← mul_assoc, ← map_mul]
      rfl
    | add x y hx hy =>
      rw [map_add (f := _), map_add (f := _), hx, hy, ← Matrix.mulVec_add]
      congr 1; funext i; simp
  let x : (Fin d → ℚ_[l]) ⊗[ℚ_[l]] P.R.BdR := ∑ i, Pi.single i (1 : ℚ_[l]) ⊗ₜ y i
  have hx : x ∈ FilV (P.PD K) (LL := ℚ_[l]) (V := Fin d → ℚ_[l]) a :=
    Submodule.sum_mem _ fun i _ => GlobalTheory.DRFil.tmul_mem_FilV (P.PD K) (LL := ℚ_[l]) _ (hy i)
  have hfx : f x = y := by
    funext j

    simp [x, map_sum, hf, Pi.single_apply]
  obtain ⟨m, k, b, dd, h, e⟩ :=
    deRham_filtered_Ql l P AI TT K (Fin d → ℚ_[l]) (qRep ρ) hdR a x hx
  refine ⟨m, k, b, fun r => f (dd r), fun r => ⟨fun g => ?_, hfil _ _ (h r).2.1, (h r).2.2⟩, ?_⟩
  · have hg : actVdR (P.PD K) (qRep ρ) g (dd r) = dd r :=
      (GlobalTheory.DRFil.mem_DdR (P.PD K) (qRep ρ) _).1 (h r).1 g
    rw [← hact, hg]
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [← hfx, e, map_sum]
      exact Finset.sum_congr rfl fun r _ => hfmul _ _

end GlobalTheory.DRFilCoord
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.LevelBasis

variable {A L Q : Type} [CommRing A] [CommRing L] [CommRing Q] (s : A →+* L) (i : L →+* Q) (J : Ideal A)
  {ι : Type} (m : ι → L)

def lsum (c : ι →₀ A) : L := c.sum fun k a => s a * m k

theorem lsum_add (c c' : ι →₀ A) : lsum s m (c + c') = lsum s m c + lsum s m c' :=
  Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by rw [map_add (f := _), add_mul])

theorem lsum_sub (c c' : ι →₀ A) : lsum s m (c - c') = lsum s m c - lsum s m c' :=
  Finsupp.sum_sub_index (fun _ _ _ => by rw [map_sub, sub_mul])

theorem lsum_smul (a : A) (c : ι →₀ A) : lsum s m (a • c) = s a * lsum s m c := by
  unfold lsum
  rw [Finsupp.sum_smul_index (fun _ => by simp), Finsupp.mul_sum]
  refine Finsupp.sum_congr fun k _ => ?_
  rw [map_mul, mul_assoc]

theorem lsum_single (k : ι) : lsum s m (Finsupp.single k 1) = m k := by
  unfold lsum; rw [Finsupp.sum_single_index (by simp), map_one, one_mul]

def IsApprox (n : ℕ) (x : Q) (c : ι →₀ A) : Prop := x - i (lsum s m c) ∈ (J ^ n).map (i.comp s)

theorem map_pow_eq (n : ℕ) : (J ^ n).map (i.comp s) = ((J.map s) ^ n).map i := by
  rw [← Ideal.map_map, Ideal.map_pow]

variable {s i J m}

theorem IsApprox.mono {n n' : ℕ} {x : Q} {c : ι →₀ A} (h : n' ≤ n) (hc : IsApprox s i J m n x c) :
    IsApprox s i J m n' x c :=
  Ideal.map_mono (Ideal.pow_le_pow_right h) hc

theorem exists_approx (hc : IsCompl i (J.map s))
    (H1 : ∀ (n : ℕ) (x : L), ∃ c : ι →₀ A, x - c.sum (fun k a => s a * m k) ∈ (J ^ n).map s)
    (n : ℕ) (x : Q) : ∃ c, IsApprox s i J m n x c := by
  obtain ⟨a, ha⟩ := hc.surj x n
  obtain ⟨c, hc'⟩ := H1 n a
  refine ⟨c, ?_⟩
  unfold IsApprox
  have e : x - i (lsum s m c) = (x - i a) + i (a - lsum s m c) := by rw [map_sub]; ring
  rw [e, map_pow_eq]
  refine add_mem ha (Ideal.mem_map_of_mem i ?_)
  rw [← Ideal.map_pow]; exact hc'

theorem approx_unique (hc : IsCompl i (J.map s))
    (H2 : ∀ (n : ℕ) (c : ι →₀ A), c.sum (fun k a => s a * m k) ∈ (J ^ n).map s → ∀ k, c k ∈ J ^ n)
    {n : ℕ} {x : Q} {c c' : ι →₀ A} (h : IsApprox s i J m n x c) (h' : IsApprox s i J m n x c') (k : ι) :
    c k - c' k ∈ J ^ n := by
  have h3 := sub_mem h' h
  have e : x - i (lsum s m c') - (x - i (lsum s m c)) = i (lsum s m (c - c')) := by
    rw [lsum_sub, map_sub]; ring
  rw [e, map_pow_eq] at h3
  have h4 := hc.ker _ n h3
  rw [← Ideal.map_pow] at h4
  simpa using H2 n (c - c') h4 k

end GlobalTheory.BSP.LevelBasis


open GlobalTheory.BSP.LevelBasis in
theorem GlobalTheory.BSP.exists_topBasis_of_levels (A : Type) [CommRing A] (L : Type) [CommRing L] (Q : Type) [CommRing Q]
    (s : A →+* L) (i : L →+* Q) (J : Ideal A) (ι : Type) (m : ι → L) (k₀ : ι) (h1 : m k₀ = 1)
    (hA : IsAdicComplete J A) (hc : IsCompl i (J.map s))
    (H1 : ∀ (n : ℕ) (x : L), ∃ c : ι →₀ A, x - c.sum (fun k a => s a * m k) ∈ (J ^ n).map s)
    (H2 : ∀ (n : ℕ) (c : ι →₀ A), c.sum (fun k a => s a * m k) ∈ (J ^ n).map s → ∀ k, c k ∈ J ^ n) :
    ∃ tb : TopBasis (i.comp s) J ι, ∀ k, tb.b k = i (m k) := by
  have mt : ∀ n : ℕ, (J ^ n • ⊤ : Submodule A A) = J ^ n := fun n => by
    rw [smul_eq_mul, Ideal.mul_top]
  have exA := exists_approx (m := m) hc H1
  have lim : ∀ (x : Q) (k : ι), ∃ a : A, ∀ n c, IsApprox s i J m n x c → c k - a ∈ J ^ n := by
    intro x k
    choose f hf using exA
    obtain ⟨a, ha⟩ := hA.toIsPrecomplete.prec (f := fun n => f n x k) (fun {p q} hpq => by
      rw [SModEq.sub_mem, mt]
      exact approx_unique hc H2 (hf p x) ((hf q x).mono hpq) k)
    refine ⟨a, fun n c hcn => ?_⟩
    have h2 := ha n
    rw [SModEq.sub_mem, mt] at h2
    have := add_mem (approx_unique hc H2 hcn (hf n x) k) h2
    simpa using this
  choose C hC using lim
  have uniq : ∀ x k a, (∀ n, ∃ c, IsApprox s i J m n x c ∧ c k - a ∈ J ^ n) → C x k = a := by
    intro x k a h
    refine sub_eq_zero.1 (hA.toIsHausdorff.haus _ fun n => ?_)
    rw [SModEq.sub_mem, mt, sub_zero]
    obtain ⟨c, hc1, hc2⟩ := h n
    have := sub_mem hc2 (hC x k n c hc1)
    convert this using 1; ring
  have single_approx : ∀ n k, IsApprox s i J m n (i (m k)) (Finsupp.single k 1) := by
    intro n k; unfold IsApprox; rw [lsum_single, sub_self]; exact zero_mem _
  refine ⟨{
    b := fun k => i (m k)
    c := fun k => AddMonoidHom.mk' (fun x => C x k) (fun x y => uniq (x + y) k _ fun n => by
      obtain ⟨c, hc⟩ := exA n x
      obtain ⟨c', hc'⟩ := exA n y
      refine ⟨c + c', ?_, ?_⟩
      · unfold IsApprox at hc hc' ⊢
        have e : x + y - i (lsum s m (c + c')) = (x - i (lsum s m c)) + (y - i (lsum s m c')) := by
          rw [lsum_add, map_add (f := _)]; ring
        rw [e]; exact add_mem hc hc'
      · have := add_mem (hC x k n c hc) (hC y k n c' hc')
        convert this using 1; simp only [Finsupp.add_apply]; ring)
    c_mul := fun k a x => by
      simp only [AddMonoidHom.mk'_apply]
      refine uniq _ k _ fun n => ?_
      obtain ⟨c, hc⟩ := exA n x
      refine ⟨a • c, ?_, ?_⟩
      · unfold IsApprox at hc ⊢
        have e : (i.comp s) a * x - i (lsum s m (a • c)) = (i.comp s) a * (x - i (lsum s m c)) := by
          rw [lsum_smul, map_mul, RingHom.comp_apply]; ring
        rw [e]; exact Ideal.mul_mem_left _ _ hc
      · have e : (a • c) k - a * C x k = a * (c k - C x k) := by
          rw [Finsupp.smul_apply, smul_eq_mul]; ring
        rw [e]; exact Ideal.mul_mem_left _ _ (hC x k n c hc)
    c_self := fun k => by
      simp only [AddMonoidHom.mk'_apply]
      exact uniq _ k _ fun n => ⟨_, single_approx n k, by simp⟩
    c_ne := fun j k hjk => by
      simp only [AddMonoidHom.mk'_apply]
      exact uniq _ j _ fun n => ⟨_, single_approx n k, by simp [Finsupp.single_apply, Ne.symm hjk]⟩
    fin := fun x n => by
      obtain ⟨c, hc⟩ := exA n x
      refine c.support.finite_toSet.subset fun k hk => ?_
      simp only [Set.mem_setOf_eq, AddMonoidHom.mk'_apply] at hk
      by_contra h
      simp only [Finset.mem_coe, Finsupp.mem_support_iff, not_not] at h
      have := hC x k n c hc
      rw [h, zero_sub, neg_mem_iff] at this
      exact hk this
    approx := fun x n F hF => by
      classical
      simp only [AddMonoidHom.mk'_apply] at hF ⊢
      obtain ⟨c, hc⟩ := exA n x
      have e1 : i (lsum s m c) = ∑ k ∈ F ∪ c.support, (i.comp s) (c k) * i (m k) := by
        unfold lsum

        rw [Finsupp.sum_of_support_subset c (Finset.subset_union_right (s₁ := F)) _ (fun _ _ => by simp), map_sum]
        simp [RingHom.comp_apply, map_mul]
      have e2 : ∑ k ∈ F, (i.comp s) (C x k) * i (m k) =
          ∑ k ∈ F ∪ c.support, (i.comp s) (if k ∈ F then C x k else 0) * i (m k) := by
        rw [← Finset.sum_subset Finset.subset_union_left (fun k _ hk => by rw [if_neg hk, map_zero, zero_mul])]
        exact Finset.sum_congr rfl fun k hk => by rw [if_pos hk]
      have e3 : x - ∑ k ∈ F, (i.comp s) (C x k) * i (m k) = (x - i (lsum s m c)) +
          ∑ k ∈ F ∪ c.support, (i.comp s) (c k - if k ∈ F then C x k else 0) * i (m k) := by
        rw [e2, e1]; simp only [map_sub, sub_mul, Finset.sum_sub_distrib]; ring
      rw [e3]
      refine add_mem hc (Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ?_))
      by_cases hk : k ∈ F
      · rw [if_pos hk]; exact hC x k n c hc
      · rw [if_neg hk, sub_zero]
        have := add_mem (hC x k n c hc) (hF k hk)
        simpa using this
    complete := by rw [← Ideal.map_map]; exact hc.complete
    i₀ := k₀
    b_i₀ := by simp only [h1, map_one] }, fun k => rfl⟩
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem W2.isUnit_of_fst_gh {l : ℕ} [Fact l.Prime] {L : Type} [CommRing L] (x : W2 l L) (h0 : IsUnit x.fst)
    (h1 : IsUnit (W2.gh x)) : IsUnit x := by
  obtain ⟨u, hu⟩ := h0
  obtain ⟨v, hv⟩ := h1
  refine isUnit_iff_exists_inv.2 ⟨⟨(↑u⁻¹ : L), -(↑u⁻¹ : L) ^ l * x.snd * ↑v⁻¹⟩, ?_⟩
  refine W2.ext ?_ ?_
  · change x.fst * (↑u⁻¹ : L) = 1
    rw [← hu]; simp
  · change x.fst ^ l * (-(↑u⁻¹ : L) ^ l * x.snd * ↑v⁻¹) + (↑u⁻¹ : L) ^ l * x.snd +
      (l : L) * x.snd * (-(↑u⁻¹ : L) ^ l * x.snd * ↑v⁻¹) = 0
    have hg : (↑v⁻¹ : L) * (x.fst ^ l + (l : L) * x.snd) = 1 := by
      change (↑v⁻¹ : L) * W2.gh x = 1
      rw [← hv]; simp
    linear_combination (-(↑u⁻¹ : L) ^ l * x.snd) * hg

theorem delta_localization (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (D : Delta l A)
    (M : Submonoid A) (hM : ∀ x ∈ M, D.φ x ∈ M) :
    ∃ D' : Delta l (Localization M), IsδMap D D' (algebraMap A (Localization M)) := by
  let s0 : A →+* W2 l (Localization M) := (W2.map (algebraMap A (Localization M))).comp (deltaSectionToWittLengthTwo D)
  have hs0 : ∀ m : M, IsUnit (s0 m) := fun m => by
    apply W2.isUnit_of_fst_gh
    · exact IsLocalization.map_units (Localization M) m
    · have : W2.gh (s0 m) = algebraMap A (Localization M) (D.φ m) := by
        rw [D.φ_eq]; change (algebraMap A _ m) ^ l + (l : Localization M) * algebraMap A _ (D.δ m) = _
        simp
      rw [this]
      exact IsLocalization.map_units (Localization M) (⟨D.φ m, hM m m.2⟩ : M)
  let s : Localization M →+* W2 l (Localization M) := IsLocalization.lift hs0
  have hsa : ∀ a : A, s (algebraMap A _ a) = s0 a := fun a => IsLocalization.lift_eq hs0 a
  have hsec : ∀ y, (s y).fst = y := fun y => by
    have : (W2.fstHom.comp s : Localization M →+* Localization M) = RingHom.id _ :=
      IsLocalization.ringHom_ext M (RingHom.ext fun a => by
        simp only [RingHom.comp_apply, RingHom.id_apply]
        rw [hsa]; rfl)
    exact RingHom.congr_fun this y
  refine ⟨deltaStructureOfWittLengthTwoSection s hsec, fun a => ?_⟩
  change algebraMap A _ (D.δ a) = (s (algebraMap A _ a)).snd
  rw [hsa]; rfl

end GlobalTheory.BSP
end
