module

public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle025
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle336
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle371
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffSetIntegralNat
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle195
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle150
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle171
public import Formalism.LocalRingCardinality.Bundle009
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle220
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle138
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle294
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle142
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle137
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle204
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped InnerProductSpace

namespace GlobalTheory.Mem.UnitPairing

def IsPolyFn (f : ℝ → ℂ) : Prop := ∃ p : Polynomial ℂ, ∀ s : ℝ, f s = p.eval (s : ℂ)

theorem IsPolyFn.const (c : ℂ) : IsPolyFn fun _ => c := ⟨Polynomial.C c, fun s => by simp⟩

theorem IsPolyFn.coe : IsPolyFn fun s => (s : ℂ) := ⟨Polynomial.X, fun s => by simp⟩

theorem IsPolyFn.add {f g : ℝ → ℂ} (hf : IsPolyFn f) (hg : IsPolyFn g) : IsPolyFn fun s => f s + g s := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  exact ⟨p + q, fun s => by simp [hp, hq]⟩

theorem IsPolyFn.mul {f g : ℝ → ℂ} (hf : IsPolyFn f) (hg : IsPolyFn g) : IsPolyFn fun s => f s * g s := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  exact ⟨p * q, fun s => by simp [hp, hq]⟩

theorem IsPolyFn.sum {ι : Type} (t : Finset ι) {f : ι → ℝ → ℂ} (hf : ∀ i, IsPolyFn (f i)) :
    IsPolyFn fun s => ∑ i ∈ t, f i s := by
  choose p hp using hf
  exact ⟨∑ i ∈ t, p i, fun s => by simp [hp, Polynomial.eval_finsetSum]⟩

theorem IsPolyFn.prod {ι : Type} (t : Finset ι) {f : ι → ℝ → ℂ} (hf : ∀ i, IsPolyFn (f i)) :
    IsPolyFn fun s => ∏ i ∈ t, f i s := by
  choose p hp using hf
  exact ⟨∏ i ∈ t, p i, fun s => by simp [hp, Polynomial.eval_prod]⟩

variable {D : D7} {V V' : HSp D} {S S' : D.what₂.Tau → SPar} (M : DSModel V S) (M' : DSModel V' S')

theorem ellT_pure (w v : ∀ τ, M.H τ) : ellT M w (PiTensorProduct.tprod ℂ v) = ∏ τ, ⟪w τ, v τ⟫_ℂ := by
  simp [ellT]

theorem isPolyFn_ellT (a b : M.Vec) (x : ⨂[ℂ] τ, M.H τ) :
    IsPolyFn fun s => ellT M (fun τ => ((a + (s : ℂ) • b) τ : M.H τ)) x := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r v =>
    simp only [map_smul, ellT_pure, smul_eq_mul, Pi.add_apply, Pi.smul_apply, Submodule.coe_add, Submodule.coe_smul,
      inner_add_left, inner_smul_left, Complex.conj_ofReal]
    exact (IsPolyFn.const _).mul (IsPolyFn.prod _ fun τ => (IsPolyFn.const _).add (IsPolyFn.coe.mul (IsPolyFn.const _)))
  | add x y hx hy =>
    simp only [map_add (f := _)]
    exact hx.add hy

theorem ellT_smul (c : D.what₂.Tau → ℝ) (a : M.Vec) (x : ⨂[ℂ] τ, M.H τ) :
    ellT M (fun τ => (((c τ : ℂ) • a τ : M.sm τ) : M.H τ)) x = (∏ τ, (c τ : ℂ)) * ellT M (fun τ => (a τ : M.H τ)) x := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r v =>
    simp only [map_smul, ellT_pure, smul_eq_mul, Submodule.coe_smul, inner_smul_left, Complex.conj_ofReal,
      Finset.prod_mul_distrib]
    ring
  | add x y hx hy =>
    simp only [map_add (f := _), hx, hy, mul_add]

noncomputable def pairing (L : SmT M' →ₗ[ℂ] SmT M) (w : M.Vec) (v : M'.Vec) : ℂ :=
  ellT M (fun τ => (w τ : M.H τ)) (inclT M (L (PiTensorProduct.tprod ℂ v)))

theorem isPolyFn_pairing (L : SmT M' →ₗ[ℂ] SmT M) (a b : M.Vec) (a' b' : M'.Vec) :
    IsPolyFn fun s => pairing M M' L (a + (s : ℂ) • b) (a' + (s : ℂ) • b') := by
  classical
  have h : ∀ s : ℝ, PiTensorProduct.tprod ℂ (a' + (s : ℂ) • b') = ∑ t : Finset D.what₂.Tau,
      (∏ τ, if τ ∈ t then (1 : ℂ) else (s : ℂ)) • PiTensorProduct.tprod ℂ (t.piecewise a' b') := fun s => by
    rw [MultilinearMap.map_add_univ]
    refine Finset.sum_congr rfl fun t _ => ?_
    have hm := (PiTensorProduct.tprod ℂ).map_smul_univ
      (fun τ => if τ ∈ t then (1 : ℂ) else (s : ℂ)) (t.piecewise a' b')
    simp only [RingHom.id_apply] at hm
    rw [← hm]
    congr 1
    funext τ
    by_cases hτ : τ ∈ t <;> simp [Finset.piecewise, hτ]

  simp only [pairing, h, map_sum, map_smul, smul_eq_mul]
  refine IsPolyFn.sum _ fun t => IsPolyFn.mul (IsPolyFn.prod _ fun τ => ?_) (isPolyFn_ellT M a b _)
  by_cases hτ : τ ∈ t
  · simpa [hτ] using IsPolyFn.const 1
  · simpa [hτ] using IsPolyFn.coe

noncomputable def nrm (a : M.Vec) : M.Vec := fun τ => ((‖(a τ : M.H τ)‖⁻¹ : ℝ) : ℂ) • a τ

theorem smul_nrm (a : M.Vec) : (fun τ => ((‖(a τ : M.H τ)‖ : ℝ) : ℂ) • nrm M a τ) = a := by
  funext τ
  by_cases h : a τ = 0
  · simp [nrm, h]
  · have : ‖(a τ : M.H τ)‖ ≠ 0 := by simpa using h
    rw [nrm, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ this, Complex.ofReal_one, one_smul]

theorem norm_nrm (a : M.Vec) (h : (∏ τ, ((‖(a τ : M.H τ)‖ : ℝ) : ℂ)) ≠ 0) (τ : D.what₂.Tau) : ‖(nrm M a τ : M.H τ)‖ = 1 := by
  have h1 : ‖(a τ : M.H τ)‖ ≠ 0 := Complex.ofReal_ne_zero.1 (Finset.prod_ne_zero_iff.1 h τ (Finset.mem_univ τ))
  rw [nrm, Submodule.coe_smul, norm_smul, Complex.norm_real, norm_inv, norm_norm, inv_mul_cancel₀ h1]

theorem pairing_nrm (L : SmT M' →ₗ[ℂ] SmT M) (w : M.Vec) (v : M'.Vec) :
    pairing M M' L w v = (∏ τ, ((‖(w τ : M.H τ)‖ : ℝ) : ℂ)) * ((∏ τ, ((‖(v τ : M'.H τ)‖ : ℝ) : ℂ)) *
      pairing M M' L (nrm M w) (nrm M' v)) := by
  have h1 : PiTensorProduct.tprod ℂ v = (∏ τ, ((‖(v τ : M'.H τ)‖ : ℝ) : ℂ)) • PiTensorProduct.tprod ℂ (nrm M' v) := by
    have hm := (PiTensorProduct.tprod ℂ).map_smul_univ
      (fun τ => ((‖(v τ : M'.H τ)‖ : ℝ) : ℂ)) (nrm M' v)
    simp only [RingHom.id_apply] at hm
    rw [← hm, smul_nrm]
  have h2 : ∀ x, ellT M (fun τ => (w τ : M.H τ)) x =
      (∏ τ, ((‖(w τ : M.H τ)‖ : ℝ) : ℂ)) * ellT M (fun τ => (nrm M w τ : M.H τ)) x := fun x => by
    rw [← ellT_smul M (fun τ => ‖(w τ : M.H τ)‖)]
    exact congrArg (fun u : M.Vec => ellT M (fun τ => (u τ : M.H τ)) x) (smul_nrm M w).symm
  rw [pairing, pairing, h1, h2, map_smul, map_smul, map_smul, smul_eq_mul]

theorem unit_of_ne {P : Type} [AddCommGroup P] [Module ℂ P] (It : P →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M) (φ : P) (w : M.Vec) (v : M'.Vec)
    (h : pairing M M' (It φ) w v ≠ 0) :
    (∀ τ, ‖(nrm M w τ : M.H τ)‖ = 1) ∧ (∀ τ, ‖(nrm M' v τ : M'.H τ)‖ = 1) ∧
      ∃ φ', pairing M M' (It φ') (nrm M w) (nrm M' v) = 1 := by
  rw [pairing_nrm] at h
  obtain ⟨h1, h⟩ := mul_ne_zero_iff.1 h
  obtain ⟨h2, h3⟩ := mul_ne_zero_iff.1 h
  refine ⟨norm_nrm M w h1, norm_nrm M' v h2, (pairing M M' (It φ) (nrm M w) (nrm M' v))⁻¹ • φ, ?_⟩
  rw [← inv_mul_cancel₀ h3]
  simp only [pairing, map_smul, LinearMap.smul_apply, smul_eq_mul]

theorem exists_pairing_ne {P : Type} [AddCommGroup P] [Module ℂ P] (It : P →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M) (h : It ≠ 0) :
    ∃ φ w v, pairing M M' (It φ) w v ≠ 0 := by
  have : ∃ φ v, It φ (PiTensorProduct.tprod ℂ v) ≠ 0 := by
    by_contra hn
    push Not at hn
    refine h (LinearMap.ext fun φ => ?_)
    exact PiTensorProduct.ext (MultilinearMap.ext fun v => hn φ v)
  obtain ⟨φ, v, hv⟩ := this
  obtain ⟨w, hw⟩ := GlobalTheory.T.smoothPureTensors_separate_tensorProduct D V S M _ hv
  exact ⟨φ, w, v, hw⟩

theorem exists_common (U : Type) [AddCommGroup U] [Module ℂ U] (ι : Type) [Finite ι] (f : ι → U → ℂ)
    (h : ∀ i a b, IsPolyFn fun s => f i (a + (s : ℂ) • b)) (h' : ∀ i, ∃ v, f i v ≠ 0) : ∃ v, ∀ i, f i v ≠ 0 :=
  @GlobalTheory.T.exists_common_nonzero_of_polynomial_on_real_lines U _ (Module.complexToReal U) ι _ f h h'

theorem exists_unit_vectors : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), (∀ k, k + 1 < D.R.m → R.ItY k ≠ 0) → R.ItX ≠ 0 → ∃ (d : ∀ j, (R.MY j).Vec) (dX : R.MX.Vec) (φ : ∀ k, PolF D (Yc D (k + 1)).rank (Yc D k).rank) (φX : PolF D D.sp.X'.rank (Yc D (D.R.m - 1)).rank), (∀ j, j < D.R.m → ∀ τ, ‖(d j τ : (R.MY j).H τ)‖ = 1) ∧ (∀ τ, ‖(dX τ : R.MX.H τ)‖ = 1) ∧ (∀ k, k + 1 < D.R.m → ellT (R.MY k) (fun τ => (d k τ : (R.MY k).H τ)) (inclT (R.MY k) (R.ItY k (φ k) (PiTensorProduct.tprod ℂ (d (k + 1))))) = 1) ∧ ellT (R.MY (D.R.m - 1)) (fun τ => (d (D.R.m - 1) τ : (R.MY (D.R.m - 1)).H τ)) (inclT (R.MY (D.R.m - 1)) (R.ItX φX (PiTensorProduct.tprod ℂ dX))) = 1 := by
  intro D G _ _ Pl0 T A Ks _ _ _ R hY hX
  classical
  have hm := D.R.two_le_m
  have e1 : ∀ k, ∃ φ : PolF D (Yc D (k + 1)).rank (Yc D k).rank, k + 1 < D.R.m →
      ∃ w v, pairing (R.MY k) (R.MY (k + 1)) (R.ItY k φ) w v ≠ 0 := fun k => by
    by_cases hk : k + 1 < D.R.m
    · obtain ⟨φ, h⟩ := exists_pairing_ne _ _ (R.ItY k) (hY k hk)
      exact ⟨φ, fun _ => h⟩
    · exact ⟨0, fun h => absurd h hk⟩
  choose φ hφ using e1
  obtain ⟨φX, wX, vX, hφX⟩ := exists_pairing_ne _ _ R.ItX hX
  let f : Option (Fin (D.R.m - 1)) → (∀ j, (R.MY j).Vec) × R.MX.Vec → ℂ := fun i u =>
    match i with
    | none => pairing (R.MY (D.R.m - 1)) R.MX (R.ItX φX) (u.1 (D.R.m - 1)) u.2
    | some k => pairing (R.MY k) (R.MY (k + 1)) (R.ItY k (φ k)) (u.1 k) (u.1 (k + 1))
  obtain ⟨u, hu⟩ := exists_common _ _ f (fun i a b => by
      cases i with
      | none => exact isPolyFn_pairing _ _ _ _ _ _ _
      | some k => exact isPolyFn_pairing _ _ _ _ _ _ _) (fun i => by
      cases i with
      | none =>
        refine ⟨(Function.update 0 (D.R.m - 1) wX, vX), ?_⟩
        simpa only [f, Function.update_self] using hφX
      | some k =>
        obtain ⟨w, v, h⟩ := hφ k (by omega)
        refine ⟨(Function.update (Function.update 0 (k : ℕ) w) (k + 1) v, 0), ?_⟩
        simpa only [f, Function.update_self, Function.update_of_ne (Nat.succ_ne_self (k : ℕ)).symm] using h)
  obtain ⟨x1, x2, φX', x3⟩ := unit_of_ne _ _ R.ItX φX _ _ (hu none)
  have e2 : ∀ k, ∃ φ' : PolF D (Yc D (k + 1)).rank (Yc D k).rank, k + 1 < D.R.m →
      (∀ τ, ‖(nrm (R.MY k) (u.1 k) τ : (R.MY k).H τ)‖ = 1) ∧
      pairing (R.MY k) (R.MY (k + 1)) (R.ItY k φ') (nrm _ (u.1 k)) (nrm _ (u.1 (k + 1))) = 1 := fun k => by
    by_cases hk : k + 1 < D.R.m
    · obtain ⟨y1, -, φ', y3⟩ := unit_of_ne _ _ (R.ItY k) (φ k) _ _ (hu (some ⟨k, by omega⟩))
      exact ⟨φ', fun _ => ⟨y1, y3⟩⟩
    · exact ⟨0, fun h => absurd h hk⟩
  choose φ' hφ' using e2
  refine ⟨fun j => nrm _ (u.1 j), nrm _ u.2, φ', φX', fun j hj => ?_, x2, fun k hk => (hφ' k hk).2, x3⟩
  by_cases hk : j + 1 < D.R.m
  · exact (hφ' j hk).1
  · obtain rfl : j = D.R.m - 1 := by omega
    exact x1

end GlobalTheory.Mem.UnitPairing
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.EasyInputs

theorem smAll (D : D7) : SmAll D := fun V S M τ => by
  obtain ⟨w, hw, h0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (GlobalTheory.GardingVec.sm_ne_bot D V S M τ)
  exact ⟨⟨w, hw⟩, by simpa using h0⟩

theorem dimOK (D : D7) : DimOK D := fun i σ ρ => GlobalTheory.Mem.WeylDimPos.dimK_kapAt_Wc_pos D i σ ρ

theorem cartanOK (D : D7) : CartanOK D := by
  refine ⟨fun V S M _ τ => GlobalTheory.Chain.VacVec.cart_isCartanInv M τ, fun V hs hp τ => ?_⟩
  have h := GlobalTheory.RepsObj.gramAt_posDef hp hs τ
  exact ⟨by simp, by simp, by simpa using h⟩

theorem spOK (D : D7) : SpOK D := by
  refine ⟨fun τ => Or.inl ?_, fun τ => Or.inl (D.X'_posDef τ)⟩
  have hm : D.R.m - 1 ≤ D.R.m := Nat.sub_le _ _
  show (D.sp.Y (min (D.R.m - 1) D.R.m)).sig τ = ((D.sp.Y (min (D.R.m - 1) D.R.m)).rank, 0)
  rw [min_eq_left hm, D.Y_sigval _ hm τ, D.sp.Y_rank _ hm, sigYD]
  have := D.R.two_le_m
  have h1 : (D.R.m - (D.R.m - 1)) / 2 = 0 := by omega
  rw [h1, Nat.sub_zero]

theorem selfDualOK (D : D7) : SelfDualOK D := by
  rintro V β Λ N ⟨-, hd, hN, h1, h2⟩
  have hM0 : (N : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have hL := (GlobalTheory.PlaceModel.isSelfDualC_latFrame V).1
  rw [← GlobalTheory.PlaceModel.coe_latFrame] at h1 h2
  refine ⟨⟨?_, ?_⟩, fun y => ?_⟩
  · let f : (Fin V.rank → D.host.E) →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E) :=
      (LinearMap.lsmul D.host.E (Fin V.rank → D.host.E) (N : D.host.E)⁻¹).restrictScalars (𝓞 D.host.E)
    refine (hL.fg.map f).of_le fun x hx => ⟨_, h2 x hx, ?_⟩
    change (N : D.host.E)⁻¹ • ((N : D.host.E) • x) = x
    rw [smul_smul, inv_mul_cancel₀ hM0, one_smul]
  · intro s hs hli
    exact (LinearIndependent.iff_fractionRing _ _).mp hli
  · rw [← GlobalTheory.SDFrameLattice.mem_dualL_iff, hd]


open scoped Pointwise in
theorem petAll (D : D7) : PetAll D := by
  intro V μ 𝓕 hμ h𝓕 F hc hl h0 hi
  haveI : BorelSpace (GA D V) := ⟨rfl⟩
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.isTopRing (F := D.host.F) (E := D.host.E)
  haveI : IsTopologicalGroup (GA D V) := inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig V.gram))
  haveI : Countable (GQ V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma _ _
  rw [setIntegral_pos_iff_support_of_nonneg_ae (Filter.Eventually.of_forall fun g => by positivity) hi]
  have hs : Function.support (fun g => ‖F g‖ ^ 2) = Function.support F := by
    ext g
    simp [Function.mem_support]
  rw [hs, pos_iff_ne_zero]
  intro hz
  have hinv : ∀ γ : GQ V, γ • Function.support F = Function.support F := fun γ => by
    ext g
    rw [Set.mem_smul_set_iff_inv_smul_mem, Function.mem_support, Function.mem_support]
    have : F (γ⁻¹ • g) = F g := hl _ (γ⁻¹).2 g
    rw [this]
  have hzero := h𝓕.measure_zero_of_invariant _ hinv hz
  exact (hc.isOpen_support.measure_pos μ (Function.support_nonempty_iff.2 h0)).ne' hzero

theorem easy_inputs : ∀ D : D7, CartanOK D ∧ SelfDualOK D ∧ SpOK D ∧ DimOK D ∧ PetAll D ∧ SmAll D := fun D =>
  ⟨cartanOK D, selfDualOK D, spOK D, dimOK D, petAll D, smAll D⟩

end GlobalTheory.Mem.EasyInputs
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory GlobalTheory.DefLift GlobalTheory.Chain
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DefLiftCont

theorem continuous_integral_of_cocompact {G H : Type*} [TopologicalSpace G] [LocallyCompactSpace G]
    [FirstCountableTopology G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MeasurableSpace H] [BorelSpace H] (Γ : Subgroup H) [Countable Γ] (μ : Measure H)
    [μ.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μ] (𝓕 C : Set H)
    (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (hC : IsCompact C)
    (hcov : ∀ h : H, ∃ γ ∈ Γ, ∃ c ∈ C, h = γ * c) (K : G → H → ℂ)
    (hK : Continuous fun p : G × H => K p.1 p.2)
    (hinv : ∀ γ ∈ Γ, ∀ g h, K g (γ * h) = K g h) :
    Continuous fun g => ∫ h in 𝓕, K g h ∂μ := by
  refine continuous_iff_continuousAt.2 fun g₀ => ?_
  obtain ⟨N, hN, hN₀⟩ := exists_compact_mem_nhds g₀
  obtain ⟨M, hM⟩ := (hN.prod hC).exists_bound_of_continuousOn hK.continuousOn
  have hconst : IntegrableOn (fun _ : H => (M : ℂ)) 𝓕 μ :=
    GlobalTheory.CocompactIntegrable.integrableOn_of_cocompact Γ μ 𝓕 C h𝓕 hC hcov _ continuous_const
      (fun _ _ _ => rfl)
  have hconst' : Integrable (fun _ : H => M) (μ.restrict 𝓕) := by
    exact hconst.re
  refine continuousAt_of_dominated (bound := fun _ => M) ?_ ?_ hconst' ?_
  · refine Filter.Eventually.of_forall fun g => ?_
    exact (hK.comp (Continuous.prodMk_right g)).aestronglyMeasurable
  · filter_upwards [hN₀] with g hg
    refine Filter.Eventually.of_forall fun h => ?_
    obtain ⟨γ, hγ, c, hc, rfl⟩ := hcov h
    rw [hinv γ hγ]
    exact hM (g, c) ⟨hg, hc⟩
  · refine Filter.Eventually.of_forall fun h => ?_
    exact (hK.comp (Continuous.prodMk_left h)).continuousAt

theorem theta_integral_integrable_continuous : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (s : WO V W → ℂ) (F : GA D W → ℂ), IsWeilDatumO ψ V W χS χT ω → (∀ τ, (gramAt D W τ).PosDef) → ν.IsHaarMeasure → IsFundamentalDomain (GQ W) 𝓕 ν → IsThetaFunO ψ V W s → Continuous F → (∀ γ ∈ GQ W, ∀ h, F (γ * h) = F h) → (∀ g, IntegrableOn (fun h => thetaKO ω g h s * F h) 𝓕 ν) ∧ Continuous (Lift.liftInt ν 𝓕 (thetaKO ω) s F) := by
  intro D ψ V W χS χT ω ν 𝓕 s F hω hpos hν h𝓕 hs hF hFinv
  obtain ⟨C, hC, hcov⟩ := GlobalTheory.definite_unitary_cocompact W hpos
  obtain ⟨hcont, hinv⟩ := GlobalTheory.thetaKO_continuous_and_rat_invariant ψ V W χS χT ω hω s hs
  have hK : Continuous fun p : GA D V × GA D W => thetaKO ω p.1 p.2 s * F p.2 :=
    hcont.mul (hF.comp continuous_snd)
  have hKinv : ∀ γ ∈ GQ W, ∀ g h, thetaKO ω g (γ * h) s * F (γ * h) = thetaKO ω g h s * F h := by
    intro γ hγ g h
    have := hinv 1 (one_mem _) γ hγ g h
    rw [one_mul] at this
    rw [this, hFinv γ hγ]
  refine ⟨fun g => ?_, ?_⟩
  · exact GlobalTheory.CocompactIntegrable.integrableOn_fundamentalDomain W ν 𝓕 C hν h𝓕 hC hcov _
      (hK.comp (Continuous.prodMk_right g)) (fun γ hγ h => hKinv γ hγ g h)
  · obtain ⟨-, -, -, _, _, -, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
    obtain ⟨_, _, -, -, -, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
    exact continuous_integral_of_cocompact (GQ W) ν 𝓕 C h𝓕 hC hcov
      (fun g h => thetaKO ω g h s * F h) hK hKinv

end GlobalTheory.DefLiftCont
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory GlobalTheory.DefLift GlobalTheory.Chain
open scoped ComplexOrder NNReal ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LiftShift

theorem map_mul_right_of_cocompact {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (Γ : Subgroup G) [Countable Γ] (μ : Measure G) [μ.IsHaarMeasure] (𝓕 C : Set G)
    (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (hC : IsCompact C)
    (hcov : ∀ h : G, ∃ γ ∈ Γ, ∃ c ∈ C, h = γ * c) (k : G) :
    Measure.map (fun g => g * k) μ = μ := by
  have hle : μ 𝓕 ≤ μ C := by
    rw [h𝓕.measure_eq_tsum C]
    refine le_trans (measure_mono ?_) (measure_iUnion_le _)
    intro h hh
    obtain ⟨γ, hγ, c, hc, rfl⟩ := hcov h
    exact Set.mem_iUnion.2 ⟨⟨γ, hγ⟩, ⟨c, hc, rfl⟩, hh⟩
  have hfin : μ 𝓕 ≠ ⊤ := (hle.trans_lt hC.measure_lt_top).ne
  have hpos : μ 𝓕 ≠ 0 := h𝓕.measure_ne_zero (NeZero.ne μ)
  have h := Measure.isMulLeftInvariant_eq_smul (Measure.map (fun g => g * k) μ) μ
  set c := Measure.haarScalarFactor (Measure.map (fun g => g * k) μ) μ with hc
  have hq : Measure.QuasiMeasurePreserving (fun g : G => g * k) μ μ :=
    ⟨(measurable_mul_const k).aemeasurable, by rw [h]; exact Measure.smul_absolutelyContinuous⟩
  have h2 : IsFundamentalDomain Γ ((fun g : G => g * k) ⁻¹' 𝓕) μ := by
    refine h𝓕.preimage_of_equiv hq (e := id) Function.bijective_id ?_
    intro γ g
    simp only [id, Subgroup.smul_def, smul_eq_mul, mul_assoc]
  have h1 : Measure.map (fun g => g * k) μ 𝓕 = μ 𝓕 := by
    have := (MeasurableEquiv.mulRight k).map_apply (μ := μ) 𝓕
    rw [MeasurableEquiv.coe_mulRight] at this
    rw [this]
    exact h2.measure_eq h𝓕
  have h3 : (c : ℝ≥0∞) * μ 𝓕 = 1 * μ 𝓕 := by
    rw [one_mul]
    conv_rhs => rw [← h1, h]
    simp
  have h4 : (c : ℝ≥0∞) = 1 := (ENNReal.mul_left_inj hpos hfin).1 h3
  have h5 : c = 1 := by exact_mod_cast h4
  rw [h, h5, one_smul]

theorem liftInt_shift : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (s : WO V W → ℂ) (F : GA D W → ℂ), IsWeilDatumO ψ V W χS χT ω → (∀ τ, (gramAt D W τ).PosDef) → ν.IsHaarMeasure → IsFundamentalDomain (GQ W) 𝓕 ν → IsThetaFunO ψ V W s → Continuous F → (∀ γ ∈ GQ W, ∀ h, F (γ * h) = F h) → ∀ k ∈ GinfC W, Lift.liftInt ν 𝓕 (thetaKO ω) (ω (1, k) s) (rTr W k F) = Lift.liftInt ν 𝓕 (thetaKO ω) s F := by
  intro D ψ V W χS χT ω ν 𝓕 s F H hpos hν h𝓕 hs hF hinv k _
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig W.gram
  obtain ⟨_, _, _, _⟩ := GlobalTheory.TwistAdelicTop.locallyCompact_secondCountable_borel_countable W
  obtain ⟨C, hC, hcov⟩ := GlobalTheory.definite_unitary_cocompact W hpos
  obtain ⟨hcont, hθ⟩ := GlobalTheory.thetaKO_continuous_and_rat_invariant ψ V W χS χT ω H s hs
  have hk := map_mul_right_of_cocompact (GQ W) ν 𝓕 C h𝓕 hC hcov k
  funext g
  have hΦ : ∀ γ ∈ GQ W, ∀ h, thetaKO ω g (γ * h) s * F (γ * h) = thetaKO ω g h s * F h := by
    intro γ hγ h
    have := hθ 1 (one_mem _) γ hγ g h
    rw [one_mul] at this
    rw [this, hinv γ hγ]
  have hi : IntegrableOn (fun h => thetaKO ω g h s * F h) 𝓕 ν :=
    GlobalTheory.CocompactIntegrable.integrableOn_fundamentalDomain W ν 𝓕 C hν h𝓕 hC hcov _
      ((hcont.comp (Continuous.prodMk_right g)).mul hF) hΦ
  have key := (GlobalTheory.fundamentalDomain_setIntegral_mul_right (GQ W) ν 𝓕 h𝓕 k hk
    (fun h => thetaKO ω g h s * F h) hΦ hi).2
  have hsh : ∀ h, thetaKO ω g h (ω (1, k) s) = thetaKO ω g (h * k) s := by
    intro h
    have h1 : ω (g, h * k) = ω (g, h) * ω (1, k) := by
      rw [← map_mul, Prod.mk_mul_mk, mul_one]
    unfold thetaKO
    rw [h1]
    rfl
  unfold Lift.liftInt
  simp only [hsh, rTr]
  exact key

end GlobalTheory.LiftShift
end
