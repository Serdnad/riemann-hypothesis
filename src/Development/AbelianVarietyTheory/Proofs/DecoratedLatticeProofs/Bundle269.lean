module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle020
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle023
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsDefiniteOfAllPlus
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle396
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle058
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle113
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle206
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle319
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle458
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle244
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle162

@[expose] public section

section

open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn

variable {D : D7}

open Matrix

theorem Tm_row_sub (A : HSp D) (μ : D.host.E) (a : Fin A.rank) :
    (fun k => Tm A μ (finSumFinEquiv (Sum.inl a)) k - Tm A μ (finSumFinEquiv (Sum.inr a)) k) =
      Pi.single (finSumFinEquiv (Sum.inr a)) μ := by
  funext k
  obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective k
  simp only [Pi.single_apply, EmbeddingLike.apply_eq_iff_eq]
  rcases s with j | j
  · simp only [Tm, submatrix_apply, id, Equiv.symm_apply_apply, fromCols_apply_inl, GlobalTheory.Core.Rk.SWLaw.dblDec,
      GlobalTheory.Core.Rk.SWLaw.stackRows, fromRows_apply_inl, fromRows_apply_inr, sub_self, reduceCtorEq, if_false]
  · simp only [Tm, submatrix_apply, id, Equiv.symm_apply_apply, fromCols_apply_inr, GlobalTheory.Core.Rk.SWLaw.dblDec,
      GlobalTheory.Core.Rk.SWLaw.stackRows, Matrix.smul_apply, fromRows_apply_inl, fromRows_apply_inr, Matrix.neg_apply,
      Matrix.one_apply, Sum.inr.injEq, smul_eq_mul]
    by_cases h : j = a
    · subst h
      simp only [if_true]
      have h2 : (2 : D.host.E) ≠ 0 := two_ne_zero
      field_simp
      ring
    · simp [h, Ne.symm h]

end GlobalTheory.StdUnn

namespace GlobalTheory.StdUnn

variable {D : D7}

open Matrix

theorem rat_Tm_mulVec_sub (A : HSp D) (μ : D.host.E) (w : Fin (A.rank + A.rank) → AE D) (a : Fin A.rank) :
    (rat (Tm A μ) *ᵥ w) (finSumFinEquiv (Sum.inl a)) - (rat (Tm A μ) *ᵥ w) (finSumFinEquiv (Sum.inr a)) =
      incA D μ * w (finSumFinEquiv (Sum.inr a)) := by
  have hrow := Tm_row_sub A μ a
  calc _ = ∑ k, incA D ((Pi.single (finSumFinEquiv (Sum.inr a)) μ : Fin (A.rank + A.rank) → D.host.E) k) * w k := by
        rw [mulVec, mulVec, dotProduct, dotProduct, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        have hk : Tm A μ (finSumFinEquiv (Sum.inl a)) k - Tm A μ (finSumFinEquiv (Sum.inr a)) k =
            (Pi.single (finSumFinEquiv (Sum.inr a)) μ : Fin (A.rank + A.rank) → D.host.E) k := congrFun hrow k
        rw [← hk, map_sub, sub_mul]
        rfl
    _ = _ := by
        rw [Finset.sum_eq_single (finSumFinEquiv (Sum.inr a)) (fun k _ hk => by rw [Pi.single_eq_of_ne hk, map_zero, zero_mul])
          (fun h => absurd (Finset.mem_univ _) h), Pi.single_eq_same]

theorem rat_Tm_mulVec_mem_diagSub_iff (A : HSp D) {μ : D.host.E} (hμ : IsSkew μ) (w : Fin (A.rank + A.rank) → AE D) :
    rat (Tm A μ) *ᵥ w ∈ diagSub (AE D) finSumFinEquiv ↔ w ∈ upperHalf D A.rank := by
  have hu : IsUnit (incA D μ) := (isUnit_iff_ne_zero.2 hμ.1).map _
  simp only [diagSub, upperHalf, LinearMap.mem_eqLocus, LinearMap.mem_ker, funext_iff, LinearMap.funLeft_apply,
    Function.comp_apply, Pi.zero_apply]
  exact forall_congr' fun a => by rw [← sub_eq_zero, rat_Tm_mulVec_sub, hu.mul_right_eq_zero]

theorem exists_rat_Tm_mulVec_eq (A : HSp D) {μ : D.host.E} (hμ : IsSkew μ) (v : Fin (A.rank + A.rank) → AE D)
    (hv : v ∈ diagSub (AE D) finSumFinEquiv) : ∃ w ∈ upperHalf D A.rank, rat (Tm A μ) *ᵥ w = v := by
  have hG : IsUnit A.gram.det := (gram_det_ne A).isUnit
  let x : Fin A.rank → AE D := fun a => v (finSumFinEquiv (Sum.inl a))
  let w : Fin (A.rank + A.rank) → AE D := fun k => Sum.elim (rat A.gram *ᵥ x) 0 (finSumFinEquiv.symm k)
  have hw : w ∈ upperHalf D A.rank := by
    simp only [upperHalf, LinearMap.mem_ker, funext_iff, LinearMap.funLeft_apply, Function.comp_apply,
      Pi.zero_apply, w, Equiv.symm_apply_apply, Sum.elim_inr, implies_true]
  have hv' : ∀ a, v (finSumFinEquiv (Sum.inl a)) = v (finSumFinEquiv (Sum.inr a)) := by
    simpa only [diagSub, LinearMap.mem_eqLocus, funext_iff, LinearMap.funLeft_apply, Function.comp_apply] using hv
  have hl : ∀ a, (rat (Tm A μ) *ᵥ w) (finSumFinEquiv (Sum.inl a)) = x a := fun a => by
    have h1 : rat (A.gram⁻¹) * rat A.gram = (1 : Mx D A.rank A.rank) := by
      rw [rat, rat, ← Matrix.map_mul, nonsing_inv_mul _ hG, Matrix.map_one _ (map_zero _) (map_one _)]
    have h2 := congrFun (congrArg (· *ᵥ x) h1) a
    simp only [← mulVec_mulVec, one_mulVec] at h2
    rw [← h2, mulVec, dotProduct, ← finSumFinEquiv.sum_comp, Fintype.sum_sum_type]
    simp only [w, Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, mul_zero,
      Finset.sum_const_zero, add_zero, mulVec, dotProduct, rat, map_apply, Tm, submatrix_apply, id,
      fromCols_apply_inl, GlobalTheory.Core.Rk.SWLaw.dblDec, GlobalTheory.Core.Rk.SWLaw.stackRows, fromRows_apply_inl]
  refine ⟨w, hw, funext fun k => ?_⟩
  obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective k
  rcases s with a | a
  · exact hl a
  · have h3 := (rat_Tm_mulVec_mem_diagSub_iff A hμ w).2 hw
    simp only [diagSub, LinearMap.mem_eqLocus, funext_iff, LinearMap.funLeft_apply, Function.comp_apply] at h3
    rw [← h3 a, hl a, ← hv' a]

theorem mem_siegel_iff_chart_mem_P : ∀ (D : D7) (A : HSp D) (μ : D.host.E), IsSkew μ →
    ∀ κ : GA D (dblSp A) ≃* G D A.rank, IsChart A μ κ → ∀ g, g ∈ siegel A ↔ κ g ∈ P D A.rank := by
  intro D A μ hμ κ hκ g
  have hT : ∀ w, rat (Tm A μ) *ᵥ (mat (κ g) *ᵥ w) = mt (dblSp A) g *ᵥ (rat (Tm A μ) *ᵥ w) := fun w => by
    rw [mulVec_mulVec, mulVec_mulVec, hκ g]
  have hP : κ g ∈ P D A.rank ↔ ∀ w, w ∈ upperHalf D A.rank ↔ mat (κ g) *ᵥ w ∈ upperHalf D A.rank := Iff.rfl
  have hS : g ∈ siegel A ↔ ∀ v, v ∈ diagSub (AE D) finSumFinEquiv ↔
      mt (dblSp A) g *ᵥ v ∈ diagSub (AE D) finSumFinEquiv := Iff.rfl
  rw [hP]
  constructor
  · intro h w
    rw [← rat_Tm_mulVec_mem_diagSub_iff A hμ, ← rat_Tm_mulVec_mem_diagSub_iff A hμ, hT]
    exact hS.1 h _
  · intro h
    refine Subgroup.mem_comap.2 (mem_stabGL_diagSub.2 (keepsDiag_of_mulVec fun v hv => ?_))
    obtain ⟨w, hw, rfl⟩ := exists_rat_Tm_mulVec_eq A hμ v hv
    change mt (dblSp A) g *ᵥ _ ∈ _
    rw [← hT, rat_Tm_mulVec_mem_diagSub_iff A hμ]
    exact (h w).1 hw

end GlobalTheory.StdUnn
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)

noncomputable section

namespace GlobalTheory.ChainTw.IPDictPf

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

theorem isInnerProduct_of_isMet' (t : T) (k : ℕ) {ipD ip} (hm : IsMet (comR R t) (stY R t k) ipD ip) (x y : (stY R t k).CC (comR R t)) :
    GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.IsIP R t k (PiTensorProduct.lift.symm x.1) (PiTensorProduct.lift.symm y.1) (ip y x) := by
  intro v v'
  have h1 := hm.integ y x (PiTensorProduct.tprod ℂ v') (PiTensorProduct.tprod ℂ v)
  have h2 := hm.schur y x (PiTensorProduct.tprod ℂ v') (PiTensorProduct.tprod ℂ v)
  rw [hm.pure v' v] at h2
  have e : (fun g => star ((PiTensorProduct.lift.symm x.1) v g) * (PiTensorProduct.lift.symm y.1) v' g) =
      fun g => PiLocalization₂.val y (PiTensorProduct.tprod ℂ v') g * conj (PiLocalization₂.val x (PiTensorProduct.tprod ℂ v) g) := by
    funext g; rw [mul_comm]; rfl
  refine ⟨?_, ?_⟩
  · exact (congrArg (fun F => IntegrableOn F (stY R t k).fd (stY R t k).ν) e).mpr h1
  · exact (congrArg (fun F : GA D (stY R t k).V → ℂ => ∫ g in (stY R t k).fd, F g ∂(stY R t k).ν) e).trans h2

theorem exists_tprod_ne {k : ℕ} (w : SmT (R.MY k)) (hw : w ≠ 0) : ∃ v : (R.MY k).Vec, PiTensorProduct.tprod ℂ v ≠ 0 := by
  by_contra h
  push_neg at h
  have hid : (LinearMap.id : SmT (R.MY k) →ₗ[ℂ] SmT (R.MY k)) = 0 :=
    PiTensorProduct.ext (MultilinearMap.ext fun v => by simpa using h v)
  exact hw (by simpa using LinearMap.congr_fun hid w)

theorem exists_vec (hC : R.IsChain) (t : T) {k : ℕ} (hk : k < D.R.m) {ipD ip} (hm : IsMet (comR R t) (stY R t k) ipD ip) :
    ∃ v : (R.MY k).Vec, ∏ τ, ⟪(v τ : (R.MY k).H τ), (v τ : (R.MY k).H τ)⟫_ℂ ≠ 0 := by
  have hw : ∃ w : SmT (R.MY k), w ≠ 0 := by
    by_cases hkk : k + 1 < D.R.m
    · by_contra h
      push_neg at h
      exact (hC.ItY t k hkk).ne (LinearMap.ext fun φ => LinearMap.ext fun x => by simpa using h (R.ItY k φ x))
    · obtain rfl : k = D.R.m - 1 := by omega
      by_contra h
      push_neg at h
      exact (hC.ItX t).ne (LinearMap.ext fun φ => LinearMap.ext fun x => by simpa using h (R.ItX φ x))
  obtain ⟨w, hw⟩ := hw
  obtain ⟨v, hv⟩ := exists_tprod_ne R w hw
  refine ⟨v, fun h0 => ?_⟩
  have hp := hm.posD (PiTensorProduct.tprod ℂ v) hv
  rw [hm.pure v v] at hp
  change 0 < (∏ τ, ⟪(v τ : (R.MY k).H τ), (v τ : (R.MY k).H τ)⟫_ℂ).re at hp
  rw [h0] at hp
  simp at hp

theorem ipDict (R : RealDat D A Ks) (F : Face D A) (hG : Given R F) : IPDict R := by
  intro t k hk ipD ip hm x y a
  obtain ⟨v, hv⟩ := exists_vec R hG.core.chain t hk hm
  exact ⟨fun h => hasPeterssonInner_unique _ _ _ _ _ v hv h (isInnerProduct_of_isMet' R t k hm x y), fun h => h ▸ isInnerProduct_of_isMet' R t k hm x y⟩

theorem main : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F → IPDict R := fun R F hG => ipDict R F hG

end GlobalTheory.ChainTw.IPDictPf

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)

noncomputable section

namespace GlobalTheory.ChainTwNorm

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)

theorem orZero_of {X : Type} [Zero X] {p : X → Prop} {x : X} (hx : p x) : OrZero p x :=
  ⟨fun _ => hx, fun hn => absurd ⟨x, hx⟩ hn⟩

theorem baseW_of_given (hG : Given R F) : R.BaseW F := by
  obtain ⟨lev, grp, fam, models, chain, thP⟩ := hG.core
  exact ⟨lev, grp, fam, models,
    ⟨chain.ωY, chain.ωX, chain.vY, chain.vX, chain.ptY, chain.ptX, fun k hk => orZero_of fun t => chain.ItY t k hk,
      orZero_of chain.ItX, fun t k hk => orZero_of (chain.ioY t k (by omega)), fun t => orZero_of (chain.ioX t),
      fun t => orZero_of (chain.Th t)⟩,
    ⟨thP.ωP, thP.vP, thP.pt_theta, fun i => orZero_of (thP.ioP i), fun i t => orZero_of ⟨thP.thF_mem i t, thP.thF i t⟩,
      fun i t => orZero_of (thP.thG i t)⟩⟩

theorem alg_step {d I aa xy ipv P P' na : ℂ} (hna : na ≠ 0) (e1 : aa = na ^ 2) (e2 : P = P') (h1 : d * I = aa * xy)
    (h2 : I = ipv * P) : xy = d * P' / na ^ 2 * ipv := by
  subst e1 e2 h2
  field_simp
  linear_combination -h1

theorem riesz {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
    (ℓ : W →ₗ[ℂ] ℂ) : ∃ a : W, ∀ w, ℓ w = ⟪a, w⟫_ℂ :=
  ⟨(InnerProductSpace.toDual ℂ W).symm (LinearMap.toContinuousLinearMap ℓ), fun w => by
    rw [InnerProductSpace.toDual_symm_apply]; rfl⟩

theorem normX : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks]
    [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F → ∀ h : RangeX R, NormX R h := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG h
  have hB := baseW_of_given R F hG
  have hm := hG.core.models
  obtain ⟨w0, v0, hw0⟩ : ∃ (w : R.cX.W) (v : R.MX.Vec), R.prX w (PiTensorProduct.tprod ℂ v) ≠ 0 := by
    by_contra hc
    push_neg at hc
    apply hm.prX.1
    refine LinearMap.ext fun w => LinearMap.ext fun x => ?_
    induction x using PiTensorProduct.induction_on with
    | smul_tprod r v => simp [hc w v]
    | add x y hx hy => simp [map_add (f := _), hx, hy]
  obtain ⟨a, ha⟩ := riesz (R.prX.flip (PiTensorProduct.tprod ℂ v0))
  have ha' : ∀ w, R.prX w (PiTensorProduct.tprod ℂ v0) = ⟪a, w⟫_ℂ := fun w => ha w
  have hna : a ≠ 0 := by
    rintro rfl
    exact hw0 (by rw [ha']; simp)
  have hv : ∀ τ, (v0 τ : R.MX.H τ) ≠ 0 := by
    intro τ h0
    apply hw0
    have : v0 τ = 0 := Subtype.ext h0
    rw [(PiTensorProduct.tprod ℂ).map_coord_zero τ this, map_zero]
  haveI : Nontrivial R.cX.W := hm.cX.2.2.2.1
  have hd : (0 : ℝ) < Module.finrank ℂ R.cX.W := by exact_mod_cast Module.finrank_pos
  have hP : (0 : ℝ) < ∏ τ, ‖(v0 τ : R.MX.H τ)‖ ^ 2 :=
    Finset.prod_pos fun τ _ => pow_pos (norm_pos_iff.2 (hv τ)) 2
  have hA : (0 : ℝ) < ‖a‖ ^ 2 := pow_pos (norm_pos_iff.2 hna) 2
  refine ⟨(Module.finrank ℂ R.cX.W : ℝ) * (∏ τ, ‖(v0 τ : R.MX.H τ)‖ ^ 2) / ‖a‖ ^ 2, by positivity, fun t => ⟨?_, ?_⟩⟩
  · have hi := GlobalTheory.DefiniteMult.top_injective R hm.inf hm.cX hm.prX hm.HX t
    refine ⟨fun x y e => ?_, fun z => ?_⟩
    · have e2 := (LinearEquiv.ofEq _ _ (h t)).injective e
      exact hi (congrArg Subtype.val e2)
    · obtain ⟨u, hu⟩ := (LinearMap.surjective_rangeRestrict _) ((LinearEquiv.ofEq _ _ (h t)).symm z)
      refine ⟨u, ?_⟩
      simp only [toCC, hu]
      exact (LinearEquiv.ofEq _ _ (h t)).apply_symm_apply z
  · intro ipD ip hM x y
    have hS := hM.schur (toCC R h t y) (toCC R h t x) (PiTensorProduct.tprod ℂ v0) (PiTensorProduct.tprod ℂ v0)
    have hS' := hS.trans (congrArg _ (hM.pure v0 v0))
    have hI := (GlobalTheory.T.unfolding_schur_orthogonality_definite_coefficients D G Pl0 T A Ks R F hB t x y a a).2
    have hJ : (∫ g in R.fdX t, star ⟪a, R.cX.ext ((R.HX t).e x) g⟫_ℂ * ⟪a, R.cX.ext ((R.HX t).e y) g⟫_ℂ ∂(R.νX t)) =
        ip (toCC R h t y) (toCC R h t x) * ∏ τ, ⟪(v0 τ : R.MX.H τ), (v0 τ : R.MX.H τ)⟫_ℂ := by
      refine Eq.trans ?_ hS'
      unfold Lift.pet
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
      have e3 : (((toCC R h t y : (stX R t).CC (comR R t)) : SmT (stX R t).M →ₗ[ℂ] (GA D (stX R t).V → ℂ))
          (PiTensorProduct.tprod ℂ v0)) g = R.prX (R.cX.ext ((R.HX t).e y) g) (PiTensorProduct.tprod ℂ v0) := rfl
      have e4 : (((toCC R h t x : (stX R t).CC (comR R t)) : SmT (stX R t).M →ₗ[ℂ] (GA D (stX R t).V → ℂ))
          (PiTensorProduct.tprod ℂ v0)) g = R.prX (R.cX.ext ((R.HX t).e x) g) (PiTensorProduct.tprod ℂ v0) := rfl
      simp only [e3, e4, ha', starRingEnd_apply]
      exact mul_comm _ _
    have e1 : ⟪a, a⟫_ℂ = ((‖a‖ : ℂ)) ^ 2 := inner_self_eq_norm_sq_to_K a
    have e2 : (∏ τ, ⟪(v0 τ : R.MX.H τ), (v0 τ : R.MX.H τ)⟫_ℂ) = ∏ τ, ((‖(v0 τ : R.MX.H τ)‖ : ℂ)) ^ 2 :=
      Finset.prod_congr rfl fun τ _ => inner_self_eq_norm_sq_to_K _
    have hA' : (‖a‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_pos_iff.2 hna).ne'
    have H := alg_step hA' e1 e2 hI hJ
    rw [H]
    push_cast
    ring
end GlobalTheory.ChainTwNorm
end
end

section

open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem compFin_half (v : HeightOneSpectrum (𝓞 F)) (x c : E) :
    compFin F E v (pairA F 0 1 ⊗ₜ[F] x + pairA F 1 0 ⊗ₜ[F] c) = (1 : Fv F v) ⊗ₜ[F] x := by
  have h1 : evFin F v (pairA F 0 1) = 1 := by
    change evalV F v (1 : Af F) = 1; exact map_one _
  have h0 : evFin F v (pairA F 1 0) = 0 := by
    change evalV F v (0 : Af F) = 0; exact map_zero _
  rw [compFin, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_add (f := _), Algebra.TensorProduct.map_tmul,
    Algebra.TensorProduct.map_tmul, AlgHom.id_apply, AlgHom.id_apply, h1, h0, TensorProduct.zero_tmul, add_zero]

theorem compInf_half (w : InfinitePlace F) (x : E) :
    compInf F E w (2 * (pairA F 0 1 ⊗ₜ[F] x + pairA F 1 0 ⊗ₜ[F] (1 / 2 : E))) = 1 := by
  have h1 : evInf F w (pairA F 0 1) = 0 := by
    change GlobalTheory.AutFunCompare.evW w (0 : Ainf F) = 0; exact map_zero _
  have h0 : evInf F w (pairA F 1 0) = 1 := by
    change GlobalTheory.AutFunCompare.evW w (1 : Ainf F) = 1; exact map_one _
  rw [compInf, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, two_mul, map_add (f := _), map_add (f := _), Algebra.TensorProduct.map_tmul,
    Algebra.TensorProduct.map_tmul, AlgHom.id_apply, AlgHom.id_apply, h1, h0, TensorProduct.zero_tmul, zero_add,
    ← TensorProduct.tmul_add, add_halves, ← Algebra.TensorProduct.one_def]

theorem sigR_half (σ : E →ₐ[F] E) (x : E) :
    sigR (AF F) σ (pairA F 0 1 ⊗ₜ[F] x + pairA F 1 0 ⊗ₜ[F] (1 / 2 : E)) =
      pairA F 0 1 ⊗ₜ[F] σ x + pairA F 1 0 ⊗ₜ[F] (1 / 2 : E) := by
  have h2 : σ (1 / 2 : E) = 1 / 2 := by rw [map_div₀, map_one, map_ofNat]
  rw [sigR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_add (f := _), Algebra.TensorProduct.map_tmul,
    Algebra.TensorProduct.map_tmul, AlgHom.id_apply, AlgHom.id_apply, h2]

theorem half_add (x y : E) (h : x + y = 1) :
    (pairA F 0 1 ⊗ₜ[F] x + pairA F 1 0 ⊗ₜ[F] (1 / 2 : E)) + (pairA F 0 1 ⊗ₜ[F] y + pairA F 1 0 ⊗ₜ[F] (1 / 2 : E)) =
      (1 : AF F ⊗[F] E) := by
  have hae : pairA F 0 1 + pairA F 1 0 = (1 : AF F) := Prod.ext (zero_add 1) (add_zero 1)
  rw [show (pairA F 0 1 ⊗ₜ[F] x + pairA F 1 0 ⊗ₜ[F] (1 / 2 : E)) + (pairA F 0 1 ⊗ₜ[F] y + pairA F 1 0 ⊗ₜ[F] (1 / 2 : E)) =
      pairA F 0 1 ⊗ₜ[F] (x + y) + pairA F 1 0 ⊗ₜ[F] (1 / 2 + 1 / 2 : E) by
    rw [TensorProduct.tmul_add, TensorProduct.tmul_add]; abel,
    h, add_halves, ← TensorProduct.add_tmul, hae, Algebra.TensorProduct.one_def]

end General

theorem exists_halfData : ∀ D : D7, ∃ t : AE D, HalfData t := by
  intro D
  obtain ⟨t₀, ht₀⟩ := GlobalTheory.exists_integer_add_star_eq_one_of_isCMUnram D.host.E D.sp.cm.cmUnram
  refine ⟨pairA D.host.F 0 1 ⊗ₜ[D.host.F] (t₀ : D.host.E) + pairA D.host.F 1 0 ⊗ₜ[D.host.F] (1 / 2 : D.host.E),
    ?_, fun v => ?_, fun w => compInf_half w _⟩
  · exact (congrArg _ (sigR_half D.sp.cm.sig _)).trans (half_add _ _ ht₀)
  · rw [compFin_half]
    exact tmul_mem_intLoc (one_mem _) t₀

end GlobalTheory.StdUnn
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.ChainOnto.parBound_of_rapidDecay : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, LevFacts D → ParBound D := by
  intro hCRD D _hLF c hc j hj s hs u B hB
  obtain ⟨hu0, hpar⟩ := hB
  have hex : ∃ v, PiLocalization₂.val u v ≠ 0 := by
    by_contra h
    push_neg at h
    apply hu0
    apply Subtype.ext
    apply LinearMap.ext
    intro v
    exact h v
  obtain ⟨v, hv⟩ := hex
  set f : GA D s.V → ℂ := fun g => conj (PiLocalization₂.val u v g) with hfdef
  have hPF : ParFun c s (PiLocalization₂.val u v) B := hpar v hv
  have h3 : GlobalTheory.LFun.IsParamFunV s.V c.S f B := ((GlobalTheory.T.thetaChainStage_lattice_stabilizer_params_off_set D c hc j hj s hs).2 f B).1 hPF
  obtain ⟨h4a, _, _⟩ := GlobalTheory.T.thetaChainStage_conjugate_values_hecke_operators hCRD D c hc j hj s hs
  obtain ⟨hcont, ⟨C, hC⟩, hinv, hlev⟩ := h4a u v
  obtain ⟨_, hsph, _⟩ := GlobalTheory.T.thetaChainStage_level_spherical_off_set D c hc j hj s hs
  have hfmem : f ∈ GlobalTheory.FinZeta.bddAut s.V := by
    refine ⟨(Complex.continuous_conj).comp hcont, fun γ hγ g => ?_, C, fun g => ?_⟩
    · simp only [hfdef, hinv γ hγ g]
    · simpa [hfdef] using hC g
  have hf0 : f ≠ 0 := by
    intro h0
    apply hv
    funext g
    have := congrFun h0 g
    simpa [hfdef] using this
  have hlev' : ∀ k ∈ levS s.V s.β s.L, ∀ g, f (g * k) = conj (Lev.levChi s.V s.β s.L k) * f g := by
    intro k hk g
    simp only [hfdef, hlev k hk g, map_mul]
  obtain ⟨a, ha⟩ := GlobalTheory.T.sphericalOperator_eigenvalues_determined_by_params D s.V (levS s.V s.β s.L) (fun k => conj (Lev.levChi s.V s.β s.L k)) c.S hsph B
  obtain ⟨B', hB', hbd⟩ := GlobalTheory.T.exists_satake_parameters_bounded_eigenfunction D s.V _ _ c.S hsph f hfmem hf0 hlev' a (fun P d R hR => ha f h3 P d R hR)
  intro w hw
  rw [GlobalTheory.LFun.IsParamVecOff.unique h3 hB' hw]
  exact hbd w hw
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.pushforward_haar_realPoints_times_level : ∀ D : D7, LevFacts D → ForStage D fun c _ s => MeasurableSet (intOff c s) ∧ MeasurableSet {g : GA D s.V | Lev.finE s.V g ∈ Formalism.L2.DIV.lev D.sp.cm s.V.gram s.β s.L} ∧ {g : GA D s.V | Lev.finE s.V g ∈ Formalism.L2.DIV.lev D.sp.cm s.V.gram s.β s.L} ⊆ intOff c s ∧ (∀ g : GA D s.V, Lev.finE s.V g ∈ Formalism.L2.DIV.lev D.sp.cm s.V.gram s.β s.L → ∃ b : GinfC s.V, ∃ κ ∈ Lev.levG s.V s.β s.L, g = (b : GA D s.V) * κ) ∧ ∃ mR : Measure (GinfC s.V), mR.IsHaarMeasure ∧ ∀ (f : GinfC s.V → ℂ) (F : GA D s.V → ℂ), Integrable f mR → (∀ (b : GinfC s.V), ∀ κ ∈ Lev.levG s.V s.β s.L, F ((b : GA D s.V) * κ) = f b) → IntegrableOn F {g : GA D s.V | Lev.finE s.V g ∈ Formalism.L2.DIV.lev D.sp.cm s.V.gram s.β s.L} s.ν ∧ ∫ g in {g : GA D s.V | Lev.finE s.V g ∈ Formalism.L2.DIV.lev D.sp.cm s.V.gram s.β s.L}, F g ∂s.ν = ∫ b, f b ∂mR := by
  first | exact @GlobalTheory.ChainOnto.HaarInf.pushforward_haar_real | exact GlobalTheory.ChainOnto.HaarInf.pushforward_haar_real | (intros; apply GlobalTheory.ChainOnto.HaarInf.pushforward_haar_real <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.thetaChain_level_properties : ∀ D : D7, LevFacts D := by
  first | exact @GlobalTheory.ChainOnto.LevelFacts.levFacts | exact GlobalTheory.ChainOnto.LevelFacts.levFacts | (intros; apply GlobalTheory.ChainOnto.LevelFacts.levFacts <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.thetaLiftUpwardsAdjoint_of_rapidDecay : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, UpAdj D := by
  first | exact @GlobalTheory.ChainOnto.upAdj_of_cuspRapidDecay | exact GlobalTheory.ChainOnto.upAdj_of_cuspRapidDecay | (intros; apply GlobalTheory.ChainOnto.upAdj_of_cuspRapidDecay <;> assumption)
end
