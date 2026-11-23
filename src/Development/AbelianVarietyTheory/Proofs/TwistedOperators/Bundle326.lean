module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle309
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle003
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle014
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle197
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.CoassocSimps
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open Matrix MeasureTheory GlobalTheory.Chain GlobalTheory.Chain.RealIt
open GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension (kFin KVec KMap maxCpt rep_mem_kFin)
open scoped TensorProduct InnerProductSpace Classical
open GlobalTheory.Chain.IoLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Chain.IoLift.FinTensor

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S}

theorem inclK_injective (h : KSm M) : Function.Injective (inclK h) := by
  choose r hr using fun τ =>
    LinearMap.exists_leftInverse_of_injective (Submodule.inclusion (h τ))
      (LinearMap.ker_eq_bot.mpr (Submodule.inclusion_injective (h τ)))
  have key : PiTensorProduct.map r ∘ₗ inclK h = LinearMap.id := by
    unfold inclK
    rw [← PiTensorProduct.map_comp]
    simp only [hr, PiTensorProduct.map_id]
  intro x y hxy
  calc x = (PiTensorProduct.map r ∘ₗ inclK h) x := by rw [key, LinearMap.id_apply]
    _ = (PiTensorProduct.map r ∘ₗ inclK h) y := by rw [LinearMap.comp_apply, hxy, ← LinearMap.comp_apply]
    _ = y := by rw [key, LinearMap.id_apply]

theorem incl_tprod (h : KSm M) (v : ∀ ρ, kFin M ρ) :
    inclT M (inclK h (PiTensorProduct.tprod ℂ v)) = PiTensorProduct.tprod ℂ fun ρ => (v ρ : M.H ρ) := by
  simp [inclT, inclK]

theorem incl_tprod_update (h : KSm M) (v : ∀ ρ, kFin M ρ) (τ : D.what₂.Tau) (u : kFin M τ) :
    inclT M (inclK h (PiTensorProduct.tprod ℂ (Function.update v τ u))) =
      PiTensorProduct.tprod ℂ (Function.update (fun ρ => (v ρ : M.H ρ)) τ (u : M.H τ)) := by
  rw [incl_tprod]
  congr 1
  funext ρ
  rcases eq_or_ne ρ τ with rfl | hρ
  · simp
  · simp [Function.update_of_ne hρ]

theorem act_tprod (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) (v : ∀ ρ, M.H ρ) :
    actT M τ g (PiTensorProduct.tprod ℂ v) = PiTensorProduct.tprod ℂ (Function.update v τ (M.rep τ g (v τ))) := by
  simp only [actT, PiTensorProduct.map_tprod]
  congr 1
  funext ρ
  rcases eq_or_ne ρ τ with rfl | hρ
  · simp
  · simp [Function.update_of_ne hρ]

theorem ell_update (w v : ∀ ρ, M.H ρ) (τ : D.what₂.Tau) (u : M.H τ) :
    ellT M w (PiTensorProduct.tprod ℂ (Function.update v τ u)) =
      ⟪w τ, u⟫_ℂ * ∏ ρ ∈ Finset.univ.erase τ, ⟪w ρ, v ρ⟫_ℂ := by
  have hs : ∀ ρ ∈ Finset.univ.erase τ, ⟪w ρ, Function.update v τ u ρ⟫_ℂ = ⟪w ρ, v ρ⟫_ℂ := fun ρ hρ => by
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hρ)]
  simp only [ellT, PiTensorProduct.lift.tprod, MultilinearMap.compLinearMap_apply,
    MultilinearMap.mkPiAlgebra_apply]
  show ∏ ρ, ⟪w ρ, Function.update v τ u ρ⟫_ℂ = _
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ τ), Function.update_self]
  congr 1
  exact Finset.prod_congr rfl hs

private theorem hasDerivAt_ellT_actT_exp_tprod (h : KSm M) (τ : D.what₂.Tau)
    (a : Matrix (Fin V.rank) (Fin V.rank) ℂ → Module.End ℂ (kFin M τ)) (ha : IsKAct M τ a)
    (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) (hX : X ∈ lieAt V τ) (w : ∀ ρ, M.H ρ) (v : ∀ ρ, kFin M ρ) :
    HasDerivAt (fun t : ℝ => ellT M w (actT M τ (NormedSpace.exp (t • X)) (inclT M (inclK h (PiTensorProduct.tprod ℂ v)))))
      (ellT M w (inclT M (inclK h (intersection_update_fsHerm_neg_one τ (a X) (PiTensorProduct.tprod ℂ v))))) 0 := by
  have hd := ha.der X hX (v τ)
  have hi : HasDerivAt (fun t : ℝ => ⟪w τ, M.rep τ (NormedSpace.exp (t • X)) (v τ : M.H τ)⟫_ℂ)
      ⟪w τ, (a X (v τ) : M.H τ)⟫_ℂ 0 := by
    have hc := ((innerSL ℂ (w τ)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd
    simpa [Function.comp_def] using hc
  have e2 : ellT M w (inclT M (inclK h (intersection_update_fsHerm_neg_one τ (a X) (PiTensorProduct.tprod ℂ v)))) =
      ⟪w τ, (a X (v τ) : M.H τ)⟫_ℂ * ∏ ρ ∈ Finset.univ.erase τ, ⟪w ρ, (v ρ : M.H ρ)⟫_ℂ := by
    rw [position_tprod, incl_tprod_update, ell_update]
  have e1 : (fun t : ℝ => ellT M w (actT M τ (NormedSpace.exp (t • X)) (inclT M (inclK h (PiTensorProduct.tprod ℂ v))))) =
      fun t : ℝ => ⟪w τ, M.rep τ (NormedSpace.exp (t • X)) (v τ : M.H τ)⟫_ℂ *
        ∏ ρ ∈ Finset.univ.erase τ, ⟪w ρ, (v ρ : M.H ρ)⟫_ℂ := by
    funext t
    rw [incl_tprod, act_tprod, ell_update]
  rw [e1, e2]
  exact hi.mul_const _

theorem derT_mapFactor (h : KSm M) (τ : D.what₂.Tau) (a : Matrix (Fin V.rank) (Fin V.rank) ℂ → Module.End ℂ (kFin M τ))
    (ha : IsKAct M τ a) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) (hX : X ∈ lieAt V τ) (x : KT M) :
    DerT M τ X (inclK h x) (inclK h (intersection_update_fsHerm_neg_one τ (a X) x)) := by
  delta DerT
  intro w
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r v =>
    simp only [map_smul, smul_eq_mul]
    exact (hasDerivAt_ellT_actT_exp_tprod h τ a ha X hX w v).const_mul r
  | add x y hx hy =>
    simp only [map_add (f := _)]
    exact hx.add hy

theorem incl_mapFactor_kOp (h : KSm M) (τ : D.what₂.Tau) (k : Matrix (Fin V.rank) (Fin V.rank) ℂ) (hk : k ∈ maxCpt M τ)
    (x : KT M) : inclT M (inclK h (intersection_update_fsHerm_neg_one τ (kOp M τ hk) x)) = actT M τ k (inclT M (inclK h x)) := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r v =>
    simp only [map_smul]
    congr 1
    rw [position_tprod, incl_tprod_update, incl_tprod, act_tprod] <;> rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem kFinTensor : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (τ : D.what₂.Tau) (h : KSm M), Function.Injective (inclK h) ∧ (∀ a : Matrix (Fin V.rank) (Fin V.rank) ℂ → Module.End ℂ (kFin M τ), IsKAct M τ a → ∀ X ∈ lieAt V τ, ∀ x : KT M, DerT M τ X (inclK h x) (inclK h (intersection_update_fsHerm_neg_one τ (a X) x))) ∧ ∀ (k : Matrix (Fin V.rank) (Fin V.rank) ℂ) (hk : k ∈ maxCpt M τ) (x : KT M), inclT M (inclK h (intersection_update_fsHerm_neg_one τ (kOp M τ hk) x)) = actT M τ k (inclT M (inclK h x)) := by
  intro D V S M τ h
  refine ⟨inclK_injective h, ?_, ?_⟩
  · intro a ha X hX x
    exact derT_mapFactor h τ a ha X hX x
  · intro k hk x
    exact incl_mapFactor_kOp h τ k hk x

end GlobalTheory.Chain.IoLift.FinTensor

end
end

section

noncomputable section

open scoped TensorProduct Classical
open GlobalTheory.Chain.IoLift

namespace GlobalTheory.TensorContraction

variable {ι : Type} [Fintype ι] {K : ι → Type} [∀ i, AddCommGroup (K i)] [∀ i, Module ℂ (K i)]

theorem prod_update_self [d : DecidableEq ι] (φ : ∀ j, K j →ₗ[ℂ] ℂ) (s : Finset ι) (j : ι) (hj : j ∉ s)
    (v : ∀ k, K k) (x : K j) :
    ∏ k ∈ s, φ k (Function.update v j x k) = ∏ k ∈ s, φ k (v k) := by
  refine Finset.prod_congr rfl fun k hk => ?_
  have hk' : k ≠ j := fun e => hj (e ▸ hk)
  rw [Function.update_of_ne hk']

theorem prod_update_mem [d : DecidableEq ι] (φ : ∀ j, K j →ₗ[ℂ] ℂ) (s : Finset ι) (j : ι) (hj : j ∈ s)
    (v : ∀ k, K k) (x : K j) :
    ∏ k ∈ s, φ k (Function.update v j x k) = φ j x * ∏ k ∈ s.erase j, φ k (v k) := by
  rw [← Finset.mul_prod_erase s _ hj, Function.update_self,
    prod_update_self φ (s.erase j) j (Finset.notMem_erase j s) v x]

def contrM (φ : ∀ j, K j →ₗ[ℂ] ℂ) (s : Finset ι) (i : ι) (hi : i ∉ s) (hs : ∀ j, j ≠ i → j ∈ s) :
    (∀ j, K j) →ₘₗ[ℂ] K i where
  toFun v := (∏ k ∈ s, φ k (v k)) • v i
  map_update_add' v j x y := by
    by_cases h : j = i
    · subst h
      simp only [prod_update_self φ s j hi, Function.update_self, smul_add]
    · simp only [prod_update_mem φ s j (hs j h), Function.update_of_ne (Ne.symm h), map_add (f := _), add_mul, add_smul]
  map_update_smul' v j c x := by
    by_cases h : j = i
    · subst h
      simp only [prod_update_self φ s j hi, Function.update_self, RingHom.id_apply]
      rw [smul_comm]
    · simp only [prod_update_mem φ s j (hs j h), Function.update_of_ne (Ne.symm h), map_smul, smul_eq_mul,
        RingHom.id_apply, mul_assoc, mul_smul]

def contrL (φ : ∀ j, K j →ₗ[ℂ] ℂ) (i : ι) : (⨂[ℂ] j, K j) →ₗ[ℂ] K i :=
  PiTensorProduct.lift (contrM φ (Finset.univ.erase i) i (Finset.notMem_erase _ _)
    fun j h => Finset.mem_erase.2 ⟨h, Finset.mem_univ j⟩)

theorem contrL_tprod (φ : ∀ j, K j →ₗ[ℂ] ℂ) (i : ι) (v : ∀ j, K j) :
    contrL φ i (PiTensorProduct.tprod ℂ v) = (∏ k ∈ Finset.univ.erase i, φ k (v k)) • v i := by
  rw [contrL, PiTensorProduct.lift.tprod]
  rfl

theorem contrL_comp_mapFactor (φ : ∀ j, K j →ₗ[ℂ] ℂ) (i : ι) (f : Module.End ℂ (K i)) :
    contrL φ i ∘ₗ intersection_update_fsHerm_neg_one i f = f ∘ₗ contrL φ i := by
  apply PiTensorProduct.ext
  refine MultilinearMap.ext fun v => ?_
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, position_tprod, contrL_tprod]
  rw [prod_update_self φ _ i (Finset.notMem_erase i _), Function.update_self, map_smul]

private theorem eq_zero_of_contrL_eq_zero (i : ι) (z : ⨂[ℂ] j, K j)
    (h : ∀ φ : ∀ j, K j →ₗ[ℂ] ℂ, contrL φ i z = 0) : z = 0 := by
  let b : ∀ j, Module.Basis (Module.Basis.ofVectorSpaceIndex ℂ (K j)) ℂ (K j) :=
    fun j => Module.Basis.ofVectorSpace ℂ (K j)
  let B := Basis.piTensorProduct b
  refine B.forall_coord_eq_zero_iff.1 fun p => ?_
  let φ : ∀ j, K j →ₗ[ℂ] ℂ := fun j => (b j).coord (p j)
  have key : B.coord p = (b i).coord (p i) ∘ₗ contrL φ i := by
    apply PiTensorProduct.ext
    refine MultilinearMap.ext fun v => ?_
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, contrL_tprod, map_smul, smul_eq_mul, Module.Basis.coord_apply, B,
      Basis.piTensorProduct_repr_tprod_apply, φ]
    rw [Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  rw [key, LinearMap.comp_apply, h φ, map_zero]

theorem eq_of_contrL (i : ι) (x y : ⨂[ℂ] j, K j) (h : ∀ φ : ∀ j, K j →ₗ[ℂ] ℂ, contrL φ i x = contrL φ i y) :
    x = y := by
  rw [← sub_eq_zero]
  exact eq_zero_of_contrL_eq_zero i (x - y) fun φ => by rw [map_sub, h φ, sub_self]

private theorem piTensorProduct_map_ite_eq_self_of_slot_fixed (p : ∀ j, Module.End ℂ (K j)) (x : ⨂[ℂ] j, K j)
    (h : ∀ i, intersection_update_fsHerm_neg_one i (p i) x = x) (s : Finset ι) :
    PiTensorProduct.map (fun j => if j ∈ s then p j else LinearMap.id) x = x := by
  induction s using Finset.induction_on with
  | empty => simp [PiTensorProduct.map_id]
  | insert a s ha ih =>
    have e : (fun j => if j ∈ insert a s then p j else (LinearMap.id : Module.End ℂ (K j))) =
        fun j => Function.update (fun j => (LinearMap.id : K j →ₗ[ℂ] K j)) a (p a) j ∘ₗ
          (if j ∈ s then p j else LinearMap.id) := by
      funext j
      by_cases hj : j = a
      · subst hj
        simp [ha]
      · simp [hj]
    rw [e, PiTensorProduct.map_comp, LinearMap.comp_apply, ih]
    exact h a

theorem map_eq_self (p : ∀ j, Module.End ℂ (K j)) (x : ⨂[ℂ] j, K j) (h : ∀ i, intersection_update_fsHerm_neg_one i (p i) x = x) :
    PiTensorProduct.map p x = x := by
  simpa using piTensorProduct_map_ite_eq_self_of_slot_fixed p x h Finset.univ

theorem mem_range_map (ι : Type) [Fintype ι] (K : ι → Type) [∀ i, AddCommGroup (K i)] [∀ i, Module ℂ (K i)]
    (N : ∀ i, Submodule ℂ (K i)) (x : ⨂[ℂ] i, K i)
    (h : ∀ (i : ι) (L : (⨂[ℂ] j, K j) →ₗ[ℂ] K i), (∀ f : Module.End ℂ (K i), L ∘ₗ intersection_update_fsHerm_neg_one i f = f ∘ₗ L) → L x ∈ N i) :
    x ∈ LinearMap.range (PiTensorProduct.map fun i => (N i).subtype) := by

  have hN : ∀ i, ∀ φ : ∀ j, K j →ₗ[ℂ] ℂ, contrL φ i x ∈ N i :=
    fun i φ => h i (contrL φ i) (contrL_comp_mapFactor φ i)

  choose g hg using fun i => LinearMap.exists_leftInverse_of_injective (N i).subtype (N i).ker_subtype
  let P : ∀ i, Module.End ℂ (K i) := fun i => (N i).subtype ∘ₗ g i
  have hP : ∀ i, ∀ v ∈ N i, P i v = v := fun i v hv => by
    have := congrArg (fun f => (N i).subtype (f ⟨v, hv⟩)) (hg i)
    simpa [P] using this

  have hfix : ∀ i, intersection_update_fsHerm_neg_one i (P i) x = x := fun i =>
    eq_of_contrL i _ _ fun φ => by
      rw [← LinearMap.comp_apply (contrL φ i), contrL_comp_mapFactor, LinearMap.comp_apply, hP i _ (hN i φ)]
  rw [LinearMap.mem_range]
  refine ⟨PiTensorProduct.map g x, ?_⟩
  rw [← LinearMap.comp_apply, ← PiTensorProduct.map_comp]
  exact map_eq_self P x hfix

end GlobalTheory.TensorContraction

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open Matrix MeasureTheory GlobalTheory.Chain GlobalTheory.Chain.RealIt
open GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension (kFin KVec KMap maxCpt rep_mem_kFin)
open scoped TensorProduct InnerProductSpace Classical
open GlobalTheory.Chain.IoLift GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix GlobalTheory.Chain.RealIt.LocalFromCover

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Chain.IoLift.KerTransfer

theorem locKer_of_coverKer (D : D7) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S')
    (τ : D.what₂.Tau) (p q r s : ℕ) (T₁ : GrpData p q) (T₂ : GrpData r s) (R₁ : DSRep T₁) (R₂ : DSRep T₂)
    (e : Ix p q ≃ Fin V.rank) (e' : Ix r s ≃ Fin W.rank) (m m' : ℤ) (aS aT : ℚ) (U : M.H τ → R₁.U.H)
    (U' : M'.H τ ≃ₗᵢ⋆[ℂ] R₂.U.H) (κ : LPol W.rank V.rank ≃ₗ[ℂ] Pol p q r s)
    (a' : Matrix (Fin W.rank) (Fin W.rank) ℂ → Module.End ℂ (kFin M' τ)) (hm' : (m' : ℚ) = 2 * aS)
    (h₁ : Matches R₁ M τ (barMat e) m U) (h₂ : Matches R₂ M' τ (plainMat e') m' U')
    (hκ : IsPolyIso (M.ε τ) (M'.ε τ) e e' κ) (ha : IsKAct M' τ a') (hC : CoverKer p q R₂.HK) :
    LocKer M M' τ aS aT a' := by
  have hmC' : (m' : ℂ) = 2 * (aS : ℂ) := by exact_mod_cast hm'
  have hmem : ∀ v, U'.symm (R₂.ι v) ∈ kFin M' τ := fun v =>
    (h₂.kfin _).2 ⟨v, (U'.apply_symm_apply _).symm⟩
  let j : R₂.HK.V →ₛₗ[starRingEnd ℂ] kFin M' τ :=
    { toFun := fun v => ⟨U'.symm (R₂.ι v), hmem v⟩
      map_add' := fun v w => Subtype.ext (by simp)
      map_smul' := fun c v => Subtype.ext (by simp [LinearIsometryEquiv.map_smulₛₗ]) }
  have hj : ∀ v, U' (j v : M'.H τ) = R₂.ι v := fun v => U'.apply_symm_apply _
  have hsurj : Function.Surjective j := fun y => by
    obtain ⟨v, hv⟩ := (h₂.kfin y).1 y.2
    exact ⟨v, Subtype.ext (U'.injective (by rw [hj, hv]))⟩
  have key : ∀ (Z : Type) [NormedAddCommGroup Z] [InnerProductSpace ℂ Z]
      (B : LPol W.rank V.rank →ₗ[ℂ] kFin M' τ →ₗ[ℂ] Z), IsLocPair M M' τ aS aT a' B →
      ∃ B' : Pol p q r s →ₗ[ℂ] R₂.HK.V →ₛₗ[starRingEnd ℂ] Z, IsCoverPair R₂.HK B' ∧
        ∀ P v, B' (κ P) v = B P (j v) := by
    intro Z _ _ B hB
    let B' : Pol p q r s →ₗ[ℂ] R₂.HK.V →ₛₗ[starRingEnd ℂ] Z :=
      { toFun := fun P => (B (κ.symm P)).comp j
        map_add' := fun P Q => by ext v; simp
        map_smul' := fun c P => by ext v; simp }
    have hB' : ∀ P v, B' (κ P) v = B P (j v) := fun P v => by simp [B']
    refine ⟨B', ⟨fun X hX P P' y y' => ?_, fun Y hY P y => ?_⟩, hB'⟩
    · obtain ⟨P, rfl⟩ := κ.surjective P
      obtain ⟨P', rfl⟩ := κ.surjective P'
      have hX' : toFrame M τ (barMat e X) ∈ lieAt V τ := h₁.lie ▸ ⟨X, hX, rfl⟩
      have h3 : (barMat e X).map (starRingEnd ℂ) = Matrix.reindex e e X := by ext a b; simp [barMat]
      have h4 : (barMat e X).trace = -X.trace := by
        rw [barMat, trace_reindex', ← trace_conj hX]
        simp [Matrix.trace]
      have h := hB.skew _ hX' P P' (j y) (j y')
      simp only [sOp, fr_toFrame, trace_toFrame, h3, h4, LinearMap.add_apply, LinearMap.smul_apply,
        Module.End.one_apply, map_add, map_smul, inner_add_left, inner_add_right, inner_smul_left,
        inner_smul_right, map_neg, map_mul, map_ratCast, trace_conj hX] at h
      rw [← hκ.1, ← hκ.1, hB', hB', hB', hB']
      linear_combination h
    · obtain ⟨P, rfl⟩ := κ.surjective P
      have hY' : toFrame M' τ (plainMat e' Y) ∈ lieAt W τ := h₂.lie ▸ ⟨Y, hY, rfl⟩
      have h4 : (plainMat e' Y).trace = Y.trace := trace_reindex' e' Y
      have h5 : a' (toFrame M' τ (plainMat e' Y)) (j y) = j (R₂.HK.act Y y) - ((aS : ℂ) * Y.trace) • j y := by
        have h6 : a' (toFrame M' τ (plainMat e' Y)) (j y) =
            j (R₂.HK.act Y y + ((m' : ℂ) / 2 * Y.trace) • y) := by
          refine Subtype.ext (U'.injective ?_)
          rw [hj, ← h₂.der Y hY y _ (hj y), dRep, (ha.der _ hY' (j y)).deriv]
        rw [h6, map_add (f := _), LinearMap.map_smulₛₗ, map_mul, map_div₀, map_intCast, map_ofNat, trace_conj hY, hmC',
          sub_eq_add_neg, ← neg_smul]
        congr 2
        ring
      have h := hB.inv _ hY' P (j y)
      rw [h5, tOp, fr_toFrame, trace_toFrame, h4] at h
      rw [← hκ.2, hB', hB', ← h]
      simp [plainMat]
  intro Z₁ Z₂ _ _ _ _ B₁ B₂ hB₁ hB₂ hne n a b hs
  obtain ⟨C₁, hC₁, e₁⟩ := key Z₁ B₁ hB₁
  obtain ⟨C₂, hC₂, e₂⟩ := key Z₂ B₂ hB₂
  choose g hg using hsurj
  have hne' : C₁ ≠ 0 := fun h0 => hne (LinearMap.ext fun P => LinearMap.ext fun y => by
    rw [← hg y, ← e₁, h0]; rfl)
  have h := hC Z₁ Z₂ C₁ C₂ hC₁ hC₂ hne' n (fun i => κ (a i)) (fun i => g (b i)) (by simpa [e₁, hg] using hs)
  simpa [e₂, hg] using h

end GlobalTheory.Chain.IoLift.KerTransfer

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open Matrix MeasureTheory GlobalTheory.Chain GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace Classical
open GlobalTheory.Chain.IoLift

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Chain.CuspGrowSpace

variable {D : D7} {θ : InfFam D} {V : HSp D} {φ ψ : GA D V → ℂ}

theorem isCuspGrow_add (h : IsCuspGrow θ V φ) (h' : IsCuspGrow θ V ψ) : IsCuspGrow θ V (φ + ψ) := by
  obtain ⟨a, s, c, g⟩ := h
  obtain ⟨a', s', c', g'⟩ := h'
  refine ⟨⟨fun γ hγ g => by rw [Pi.add_apply, Pi.add_apply, a.left γ hγ, a'.left γ hγ], ?_, a.cont.add a'.cont⟩,
    add_mem s s', GlobalTheory.MultMem.isCuspFun_add a a' c c', ?_⟩
  · obtain ⟨U, hU, e⟩ := a.level
    obtain ⟨U', hU', e'⟩ := a'.level
    exact ⟨U ⊓ U', hU.inter hU', fun k hk hf g => by
      rw [Pi.add_apply, Pi.add_apply, e k hk.1 hf, e' k hk.2 hf]⟩
  · obtain ⟨N, hN⟩ := GlobalTheory.Size.unifModGrowth_iff.1 g
    obtain ⟨N', hN'⟩ := GlobalTheory.Size.unifModGrowth_iff.1 g'
    refine GlobalTheory.Size.unifModGrowth_iff.2 ⟨max N N', fun l hl => ?_⟩
    rw [(GlobalTheory.Size.linOnSm_rWord hl).add _ s _ s']
    exact ne_top_of_le_ne_top (ENNReal.add_ne_top.2
      ⟨ne_top_of_le_ne_top (hN l hl) (GlobalTheory.Size.growthSize_anti (le_max_left _ _)),
        ne_top_of_le_ne_top (hN' l hl) (GlobalTheory.Size.growthSize_anti (le_max_right _ _))⟩) GlobalTheory.Size.growthSize_add_le

theorem isCuspGrow_smul (z : ℂ) (h : IsCuspGrow θ V φ) : IsCuspGrow θ V (z • φ) := by
  obtain ⟨a, s, c, g⟩ := h
  refine ⟨⟨fun γ hγ g => by rw [Pi.smul_apply, Pi.smul_apply, a.left γ hγ], ?_, a.cont.const_smul z⟩,
    Submodule.smul_mem _ z s, GlobalTheory.MultMem.isCuspFun_smul z c, ?_⟩
  · obtain ⟨U, hU, e⟩ := a.level
    exact ⟨U, hU, fun k hk hf g => by rw [Pi.smul_apply, Pi.smul_apply, e k hk hf]⟩
  · obtain ⟨N, hN⟩ := GlobalTheory.Size.unifModGrowth_iff.1 g
    refine GlobalTheory.Size.unifModGrowth_iff.2 ⟨N, fun l hl => ?_⟩
    rw [(GlobalTheory.Size.linOnSm_rWord hl).smul, GlobalTheory.Size.growthSize_smul]
    exact ENNReal.mul_ne_top enorm_ne_top (hN l hl)

theorem isCuspGrow_zero : IsCuspGrow θ V 0 := by
  refine ⟨(isAutFunSm_const θ V 0).toIsAutFun, zero_mem _, fun _ _ _ _ _ _ _ _ => by simp,
    GlobalTheory.Size.unifModGrowth_iff.2 ⟨0, fun l hl => ?_⟩⟩
  have := (GlobalTheory.Size.linOnSm_rWord (θ := θ) hl).smul 0 0
  rw [zero_smul, zero_smul] at this
  rw [this]
  exact (GlobalTheory.Size.growthSize_const (0 : ℂ)).trans_ne enorm_ne_top

theorem isCuspGrow_of_mem_span : ∀ (D : D7) (θ : InfFam D) (V : HSp D),
    ∀ φ ∈ Submodule.span ℂ {φ | IsCuspGrow θ V φ}, IsCuspGrow θ V φ := by
  intro D θ V φ h
  induction h using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => exact isCuspGrow_zero
  | add x y _ _ hx hy => exact isCuspGrow_add hx hy
  | smul c x _ hx => exact isCuspGrow_smul c hx

end GlobalTheory.Chain.CuspGrowSpace

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open Matrix MeasureTheory GlobalTheory.Chain GlobalTheory.Chain.RealIt
open GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension (kFin KVec KMap maxCpt rep_mem_kFin)
open scoped TensorProduct InnerProductSpace Classical
open GlobalTheory.Chain.IoLift

namespace GlobalTheory.Chain.IoLift

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_isKAct_of_stable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau)
    (hs : ∀ x ∈ kFin M τ, x ∈ GlobalTheory.SmVec.smSub (gramAt D V τ) (M.rep τ))
    (hd : ∀ X ∈ lieAt V τ, ∀ x ∈ kFin M τ, dRep (M.rep τ) X x ∈ kFin M τ) :
    ∃ a : Matrix (Fin V.rank) (Fin V.rank) ℂ → Module.End ℂ (kFin M τ), IsKAct M τ a := by
  have hU : IsUnit (M.fr τ) := M.fr_unit τ
  have hG : IsUnit (gramAt D V τ) := GlobalTheory.SmVec.gram_unit hU (M.fr_gram τ)
  have hπ := GlobalTheory.SmVec.isURepOn_trRep hU (M.fr_gram τ) (M.ds τ).2.2.1
  refine ⟨fun X => if hX : X ∈ lieAt V τ then
    { toFun := fun v => ⟨dRep (M.rep τ) X v, hd X hX v v.2⟩
      map_add' := fun v w => Subtype.ext (GlobalTheory.SmVec.dRep_add (hs v v.2) (hs w w.2) hX)
      map_smul' := fun c v => Subtype.ext (GlobalTheory.SmVec.dRep_smul c (hs v v.2) hX) } else 0, ⟨?_, ?_⟩⟩
  · intro X hX v
    rw [dite_eq_left hX]
    exact GlobalTheory.SmVec.hasDerivAt_dRep (hs v v.2) hX
  · intro X hX v w
    rw [dite_eq_left hX, Submodule.coe_inner, Submodule.coe_inner]
    have key : ⟪(v : M.H τ), dRep (M.rep τ) X w⟫_ℂ = -⟪dRep (M.rep τ) X v, (w : M.H τ)⟫_ℂ :=
      GlobalTheory.SmVec.inner_dRep hG hπ (hs v v.2) (hs w w.2) hX
    change ⟪dRep (M.rep τ) X v, (w : M.H τ)⟫_ℂ + ⟪(v : M.H τ), dRep (M.rep τ) X w⟫_ℂ = 0
    linear_combination key

theorem kFin_smooth_isKAct : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (τ : D.what₂.Tau) (p q : ℕ) (T : GrpData p q) (R : DSRep T) (φ : Mat p q → Matrix (Fin V.rank) (Fin V.rank) ℂ) (m : ℤ) (U : M.H τ → R.U.H), GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.Matches R M τ φ m U → kFin M τ ≤ M.sm τ ∧ ∃ a : Matrix (Fin V.rank) (Fin V.rank) ℂ → Module.End ℂ (kFin M τ), IsKAct M τ a := by
  intro D V S M τ p q T R φ m U hM
  have hk : ∀ y : M.H τ, y ∈ kFin M τ ↔ U y ∈ Set.range R.ι := fun y => hM.kfin y
  have hsm : ∀ y ∈ kFin M τ, y ∈ GlobalTheory.SmVec.smSub (gramAt D V τ) (M.rep τ) := fun y hy =>
    GlobalTheory.SmVec.mem_smSub.2 (hM.smooth y ((hk y).1 hy))
  refine ⟨fun y hy => Submodule.subset_span (hM.smooth y ((hk y).1 hy)), exists_isKAct_of_stable M τ hsm ?_⟩
  intro X hX y hy
  rw [← hM.lie] at hX
  obtain ⟨Z, hZ, rfl⟩ := hX
  obtain ⟨v, hv⟩ := (hk y).1 hy
  exact (hk _).2 ⟨_, (hM.der Z hZ v y hv.symm).symm⟩

end GlobalTheory.Chain.IoLift

end
end
