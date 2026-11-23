module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle309
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle747
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle094
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle004
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle313
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle193
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.KoszulLowersPower
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle310
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
import Mathlib.Tactic.Lemma
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open Matrix MeasureTheory GlobalTheory.Chain GlobalTheory.Chain.RealIt
open GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension (kFin KVec KMap maxCpt rep_mem_kFin)
open scoped TensorProduct InnerProductSpace Classical
open GlobalTheory.Chain.IoLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.KFinIrr

private lemma act_mem_of_forall_upq_act_mem {p q : ℕ} (N : GKMod p q) (W : Submodule ℂ N.V)
    (h : ∀ Z ∈ upq p q, ∀ y ∈ W, N.act Z y ∈ W) : ∀ Z, ∀ y ∈ W, N.act Z y ∈ W := by
  intro Z y hy
  have hre := h _ (GlobalTheory.AdjDescent.re_mem_upq Z) y hy
  have him := h _ (GlobalTheory.AdjDescent.im_mem_upq Z) y hy
  have hZ := GlobalTheory.AdjDescent.decomp Z
  generalize Z + conjR Z = A at hZ hre
  generalize Complex.I • (Z - conjR Z) = B at hZ him
  rw [hZ, map_add (f := _), map_smul, map_smul, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply]
  exact W.add_mem (W.smul_mem _ hre) (W.smul_mem _ him)

private lemma comm_act_of_comm_act_upq {p q : ℕ} (N : GKMod p q) (T : N.V →ₗ[ℂ] N.V)
    (h : ∀ Z ∈ upq p q, T ∘ₗ N.act Z = N.act Z ∘ₗ T) : ∀ Z, T ∘ₗ N.act Z = N.act Z ∘ₗ T := by
  intro Z
  have hre := h _ (GlobalTheory.AdjDescent.re_mem_upq Z)
  have him := h _ (GlobalTheory.AdjDescent.im_mem_upq Z)
  have hZ := GlobalTheory.AdjDescent.decomp Z
  generalize Z + conjR Z = A at hZ hre
  generalize Complex.I • (Z - conjR Z) = B at hZ him
  rw [hZ, map_add (f := _), map_smul, map_smul, LinearMap.comp_add, LinearMap.add_comp,
    LinearMap.comp_smul, LinearMap.smul_comp, LinearMap.comp_smul, LinearMap.smul_comp, hre, him]

theorem absIrr_of_equiv {p q : ℕ} (N : GKMod p q) (hI : Formalism.MainNotions.SchurIrreducible.IrrGK N) (hA : Formalism.MainNotions.SchurIrreducible.AdmGK N)
    {G K : Type} [AddCommGroup K] [Module ℂ K] (a : G → Module.End ℂ K) (e : K ≃ₗ[ℂ] N.V)
    (h : ∀ Z ∈ upq p q, ∃ (g : G) (c : ℂ), ∀ x, e (a g x) = N.act Z (e x) + c • e x) : AbsIrr a := by
  have hy : ∀ Z ∈ upq p q, ∃ (g : G) (c : ℂ), ∀ x, N.act Z (e x) = e (a g x - c • x) := by
    intro Z hZ
    obtain ⟨g, c, hg⟩ := h Z hZ
    refine ⟨g, c, fun x => ?_⟩
    rw [map_sub, map_smul, hg, add_sub_cancel_right]
  refine ⟨fun W hW => ?_, fun T hT => ?_⟩
  · have hst : ∀ Z ∈ upq p q, ∀ y ∈ W.map (e : K →ₗ[ℂ] N.V), N.act Z y ∈ W.map (e : K →ₗ[ℂ] N.V) := by
      rintro Z hZ _ ⟨x, hx, rfl⟩
      obtain ⟨g, c, hg⟩ := hy Z hZ
      have hmem : a g x - c • x ∈ W := W.sub_mem (hW g x hx) (W.smul_mem c hx)
      have hout := Submodule.mem_map_of_mem (f := (e : K →ₗ[ℂ] N.V)) hmem
      simpa [hg] using hout
    rcases hI.2 _ (act_mem_of_forall_upq_act_mem N _ hst) with h0 | h1
    · left
      rw [eq_bot_iff]
      intro x hx
      have hx' : (e : K →ₗ[ℂ] N.V) x ∈ W.map (e : K →ₗ[ℂ] N.V) := Submodule.mem_map_of_mem hx
      rw [h0, Submodule.mem_bot] at hx'
      rw [Submodule.mem_bot]
      simpa using hx'
    · right
      rw [eq_top_iff]
      intro x _
      have hx' : (e : K →ₗ[ℂ] N.V) x ∈ W.map (e : K →ₗ[ℂ] N.V) := by rw [h1]; trivial
      obtain ⟨y, hyW, hyx⟩ := Submodule.mem_map.mp hx'
      have hxy : y = x := e.injective hyx
      exact hxy ▸ hyW
  · have hc : ∀ Z ∈ upq p q, ((e : K →ₗ[ℂ] N.V) ∘ₗ T ∘ₗ (e.symm : N.V →ₗ[ℂ] K)) ∘ₗ N.act Z =
        N.act Z ∘ₗ ((e : K →ₗ[ℂ] N.V) ∘ₗ T ∘ₗ (e.symm : N.V →ₗ[ℂ] K)) := by
      intro Z hZ
      obtain ⟨g, c, hg⟩ := hy Z hZ
      have hTg : ∀ x, T (a g x) = a g (T x) := fun x => LinearMap.congr_fun (hT g) x
      ext y
      obtain ⟨x, rfl⟩ := e.surjective y
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hg, LinearEquiv.symm_apply_apply, map_sub, map_smul, hTg]
    obtain ⟨c, hc'⟩ := GlobalTheory.IrrTensor.schur N hI hA _ (comm_act_of_comm_act_upq N _ hc)
    refine ⟨c, LinearMap.ext fun x => e.injective ?_⟩
    have hx := LinearMap.congr_fun hc' (e x)
    simpa using hx

theorem absIrr_kFin : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (τ : D.what₂.Tau) (p q : ℕ) (T : GrpData p q) (R : DSRep T) (φ : Mat p q → Matrix (Fin V.rank) (Fin V.rank) ℂ) (m : ℤ) (U : M.H τ ≃ₗ[ℂ] R.U.H) (a : Matrix (Fin V.rank) (Fin V.rank) ℂ → Module.End ℂ (kFin M τ)), GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.Matches R M τ φ m U → Formalism.MainNotions.SchurIrreducible.IrrGK R.HK → Formalism.MainNotions.SchurIrreducible.AdmGK R.HK → IsKAct M τ a → AbsIrr fun X : lieAt V τ => a X := by
  intro D V S M τ p q T R φ m U a hM hI hA hK
  have hfin : ∀ x : kFin M τ, U x ∈ LinearMap.range R.ι := fun x =>
    LinearMap.mem_range.mpr ((hM.kfin x.1).mp x.2)
  have hequiv : ∃ e : kFin M τ ≃ₗ[ℂ] R.HK.V, ∀ y, R.ι (e y) = U y := by
    let f : kFin M τ →ₗ[ℂ] LinearMap.range R.ι :=
      LinearMap.codRestrict (LinearMap.range R.ι) ((U : M.H τ →ₗ[ℂ] R.U.H) ∘ₗ (kFin M τ).subtype) hfin
    have hf : ∀ y, (f y : R.U.H) = U y := fun y => rfl
    have hbij : Function.Bijective f := by
      constructor
      · intro x y hxy
        have hv : U x = U y := by rw [← hf, ← hf, hxy]
        exact Subtype.ext (U.injective hv)
      · rintro ⟨y, hy⟩
        have hk : U.symm y ∈ kFin M τ := by
          refine (hM.kfin _).mpr ?_
          rw [U.apply_symm_apply]
          exact LinearMap.mem_range.mp hy
        refine ⟨⟨U.symm y, hk⟩, Subtype.ext ?_⟩
        rw [hf]
        exact U.apply_symm_apply y
    let e2 := LinearEquiv.ofInjective R.ι R.ι_inj
    refine ⟨(LinearEquiv.ofBijective f hbij).trans e2.symm, fun y => ?_⟩
    have h3 := congrArg Subtype.val (e2.apply_symm_apply (f y))
    rw [LinearEquiv.ofInjective_apply, hf] at h3
    exact h3
  obtain ⟨e, hιe⟩ := hequiv
  refine absIrr_of_equiv R.HK hI hA (fun X : lieAt V τ => a X) e ?_
  intro Z hZ
  have hX : IndefiniteRowSideFullHecke.BarMatrix.toFrame M τ (φ Z) ∈ lieAt V τ := by
    rw [← hM.lie]
    exact ⟨Z, hZ, rfl⟩
  have hd : ∀ x : kFin M τ, dRep (M.rep τ) (IndefiniteRowSideFullHecke.BarMatrix.toFrame M τ (φ Z)) (x : M.H τ) =
      (a (IndefiniteRowSideFullHecke.BarMatrix.toFrame M τ (φ Z)) x : M.H τ) := fun x =>
    (hK.der _ hX x).deriv
  refine ⟨⟨_, hX⟩, (m : ℂ) / 2 * Z.trace, fun x => R.ι_inj ?_⟩
  show R.ι (e (a (IndefiniteRowSideFullHecke.BarMatrix.toFrame M τ (φ Z)) x)) = R.ι (R.HK.act Z (e x) + ((m : ℂ) / 2 * Z.trace) • e x)
  rw [hιe, ← hM.der Z hZ (e x) x (hιe x).symm, hd x]

end GlobalTheory.KFinIrr

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open Matrix MeasureTheory GlobalTheory.Chain GlobalTheory.Chain.RealIt
open GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension (kFin KVec KMap maxCpt rep_mem_kFin)
open scoped TensorProduct InnerProductSpace Classical
open GlobalTheory.Chain.IoLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Chain.IoLift.Scal

variable {ι : Type} [Fintype ι] {K : ι → Type} [∀ i, AddCommGroup (K i)] [∀ i, Module ℂ (K i)]

def tform (w : ∀ i, Module.Dual ℂ (K i)) : (⨂[ℂ] i, K i) →ₗ[ℂ] ℂ := GlobalTheory.MultilinearContraction.prodForm w

theorem tform_tprod (w : ∀ i, Module.Dual ℂ (K i)) (v : ∀ i, K i) :
    tform w (PiTensorProduct.tprod ℂ v) = ∏ i, w i (v i) := by
  exact GlobalTheory.MultilinearContraction.prodForm_tprod w v

theorem eq_of_tform {t t' : ⨂[ℂ] i, K i} (h : ∀ w, tform w t = tform w t') : t = t' := by
  let b := fun i => Module.Basis.ofVectorSpace ℂ (K i)
  let B := Basis.piTensorProduct b
  refine B.ext_elem fun p => ?_
  have : B.coord p = tform fun i => (b i).coord (p i) := by
    ext v
    simp [tform_tprod, B, Basis.piTensorProduct_repr_tprod_apply]
  have h2 := h fun i => (b i).coord (p i)
  rw [← this] at h2
  simpa using h2

def ctrM (i : ι) (w : ∀ i, Module.Dual ℂ (K i)) : (Π j, K j) →ₘₗ[ℂ] K i :=
  GlobalTheory.MultilinearContraction.contractMultilinear w i

def ctr (i : ι) (w : ∀ i, Module.Dual ℂ (K i)) : (⨂[ℂ] i, K i) →ₗ[ℂ] K i :=
  PiTensorProduct.lift (ctrM i w)

theorem ctr_tprod (i : ι) (w : ∀ i, Module.Dual ℂ (K i)) (v : ∀ i, K i) :
    ctr i w (PiTensorProduct.tprod ℂ v) = (∏ j ∈ Finset.univ.erase i, w j (v j)) • v i := by
  simp [ctr, ctrM]

theorem ctr_mapFactor (i : ι) (w : ∀ i, Module.Dual ℂ (K i)) (f : Module.End ℂ (K i)) (t : ⨂[ℂ] i, K i) :
    ctr i w (intersection_update_fsHerm_neg_one i f t) = f (ctr i w t) := by
  have : ctr i w ∘ₗ intersection_update_fsHerm_neg_one i f = f ∘ₗ ctr i w := by
    ext v
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, position_tprod, ctr_tprod,
      Function.update_self, map_smul]
    congr 1
    exact Finset.prod_congr rfl fun j hj => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  exact LinearMap.congr_fun this t

theorem tform_eq (i : ι) (w : ∀ i, Module.Dual ℂ (K i)) (t : ⨂[ℂ] i, K i) :
    tform w t = w i (ctr i w t) := by
  have : tform w = w i ∘ₗ ctr i w := by
    ext v
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, tform_tprod, ctr_tprod,
      map_smul, smul_eq_mul]
    rw [Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  exact LinearMap.congr_fun this t

theorem comm_mapFactor_of_absIrr {G : Type} (i : ι) (a : G → Module.End ℂ (K i)) (ha : AbsIrr a)
    (Φ : Module.End ℂ (⨂[ℂ] i, K i)) (h : ∀ g, Φ ∘ₗ intersection_update_fsHerm_neg_one i (a g) = intersection_update_fsHerm_neg_one i (a g) ∘ₗ Φ)
    (f : Module.End ℂ (K i)) (x : ∀ i, K i) :
    Φ (intersection_update_fsHerm_neg_one i f (PiTensorProduct.tprod ℂ x)) = intersection_update_fsHerm_neg_one i f (Φ (PiTensorProduct.tprod ℂ x)) := by
  refine eq_of_tform fun w => ?_
  rw [tform_eq i, tform_eq i, ctr_mapFactor]
  congr 1
  let T : Module.End ℂ (K i) :=
    ctr i w ∘ₗ Φ ∘ₗ (PiTensorProduct.tprod ℂ (s := K)).toLinearMap x i
  have hT : ∀ z, T z = ctr i w (Φ (PiTensorProduct.tprod ℂ (Function.update x i z))) := fun z => rfl
  obtain ⟨c, hc⟩ := ha.2 T (fun g => by
    ext z
    have := LinearMap.congr_fun (h g) (PiTensorProduct.tprod ℂ (Function.update x i z))
    simp only [LinearMap.comp_apply, position_tprod, Function.update_self, Function.update_idem] at this
    simp only [LinearMap.comp_apply, hT, this, ctr_mapFactor])
  have h1 := hT (x i)
  rw [Function.update_eq_self] at h1
  rw [position_tprod, ← hT, ← h1, hc]
  simp

theorem comm_map (Φ : Module.End ℂ (⨂[ℂ] i, K i))
    (h : ∀ i (f : Module.End ℂ (K i)), Φ ∘ₗ intersection_update_fsHerm_neg_one i f = intersection_update_fsHerm_neg_one i f ∘ₗ Φ) (f : ∀ i, Module.End ℂ (K i)) :
    Φ ∘ₗ PiTensorProduct.map f = PiTensorProduct.map f ∘ₗ Φ := by
  have key : ∀ s : Finset ι,
      Φ ∘ₗ PiTensorProduct.map (fun i => if i ∈ s then f i else LinearMap.id) =
        PiTensorProduct.map (fun i => if i ∈ s then f i else LinearMap.id) ∘ₗ Φ := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert i s hi ih =>
      have : PiTensorProduct.map (fun j => if j ∈ insert i s then f j else LinearMap.id) =
          intersection_update_fsHerm_neg_one i (f i) ∘ₗ PiTensorProduct.map (fun i => if i ∈ s then f i else LinearMap.id) := by
        ext v
        simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, PiTensorProduct.map_tprod,
          position_tprod]
        congr 1
        funext j
        by_cases hj : j = i
        · subst hj; simp [hi]
        · simp [hj]
      rw [this, ← LinearMap.comp_assoc, h, LinearMap.comp_assoc, ih, LinearMap.comp_assoc]
  simpa using key Finset.univ

theorem scalar_of_comm (ι : Type) [Fintype ι] (K : ι → Type) [∀ i, AddCommGroup (K i)] [∀ i, Module ℂ (K i)]
    (G : ι → Type) (a : ∀ i, G i → Module.End ℂ (K i)) (ha : ∀ i, AbsIrr (a i))
    (Φ : Module.End ℂ (⨂[ℂ] i, K i)) (h : ∀ i g, Φ ∘ₗ intersection_update_fsHerm_neg_one i (a i g) = intersection_update_fsHerm_neg_one i (a i g) ∘ₗ Φ) :
    ∃ c : ℂ, Φ = c • LinearMap.id := by
  by_cases hn : ∀ i, ∃ e : K i, e ≠ 0
  · choose e he using hn
    have : ∀ i, ∃ w : Module.Dual ℂ (K i), w (e i) = 1 := fun i =>
      Module.Projective.exists_dual_eq_one ℂ (he i)
    choose w hw using this
    refine ⟨tform w (Φ (PiTensorProduct.tprod ℂ e)), ?_⟩
    ext x
    have hc := comm_map Φ (fun i f => by
      ext y
      exact comm_mapFactor_of_absIrr i (a i) (ha i) Φ (h i) f y) (fun i => (w i).smulRight (x i))
    have hm : PiTensorProduct.map (fun i => (w i).smulRight (x i)) =
        (tform w).smulRight (PiTensorProduct.tprod ℂ x) := by
      ext v
      simp [tform_tprod, MultilinearMap.map_smul_univ]
    have := LinearMap.congr_fun hc (PiTensorProduct.tprod ℂ e)
    rw [hm] at this
    simpa [tform_tprod, hw] using this
  · push Not at hn
    obtain ⟨i, hi⟩ := hn
    refine ⟨0, ?_⟩
    ext x
    have : PiTensorProduct.tprod ℂ x = 0 := MultilinearMap.map_coord_zero _ i (hi _)
    simp [this]

end GlobalTheory.Chain.IoLift.Scal

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open Matrix MeasureTheory GlobalTheory.Chain GlobalTheory.Chain.RealIt
open GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension (kFin KVec KMap maxCpt rep_mem_kFin)
open scoped TensorProduct InnerProductSpace Classical
open GlobalTheory.Chain.IoLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Chain.IoLift.FockOrbit

open GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators GlobalTheory.PointAtPlaceHom

section General

variable {G σ : Type} [TopologicalSpace G]

def CoefCont (F : G → MvPolynomial σ ℂ) : Prop := ∀ m, Continuous fun k => AddMonoidAlgebra.coeff (F k) m

theorem CoefCont.const (P : MvPolynomial σ ℂ) : CoefCont fun _ : G => P := fun _ => continuous_const

theorem CoefCont.add {F F' : G → MvPolynomial σ ℂ} (h : CoefCont F) (h' : CoefCont F') :
    CoefCont fun k => F k + F' k := fun m => by
  simp only [MvPolynomial.coeff_add]
  exact (h m).add (h' m)

theorem CoefCont.mul {F F' : G → MvPolynomial σ ℂ} (h : CoefCont F) (h' : CoefCont F') :
    CoefCont fun k => F k * F' k := fun m => by
  simp only [MvPolynomial.coeff_mul]
  exact continuous_finsetSum _ fun p _ => (h _).mul (h' _)

theorem CoefCont.smul {s : G → ℂ} {F : G → MvPolynomial σ ℂ} (hs : Continuous s) (h : CoefCont F) :
    CoefCont fun k => s k • F k := fun m => by
  simp only [MvPolynomial.coeff_smul, smul_eq_mul]
  exact hs.mul (h m)

theorem CoefCont.sum {ι : Type} [Fintype ι] {F : ι → G → MvPolynomial σ ℂ} (h : ∀ i, CoefCont (F i)) :
    CoefCont fun k => ∑ i, F i k := fun m => by
  simp only [MvPolynomial.coeff_sum]
  exact continuous_finsetSum _ fun i _ => h i m

theorem CoefCont.aeval {τ : Type} {g : G → τ → MvPolynomial σ ℂ} (h : ∀ v, CoefCont fun k => g k v)
    (P : MvPolynomial τ ℂ) : CoefCont fun k => MvPolynomial.aeval (g k) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simpa using CoefCont.const _
  | add p q hp hq => simpa using hp.add hq
  | mul_X p v hp => simpa using hp.mul (h v)

theorem exists_monomials [Finite σ] (N : ℕ) : ∃ (n : ℕ) (e : Fin n → σ →₀ ℕ), ∀ P : MvPolynomial σ ℂ,
    P.totalDegree ≤ N → P = ∑ i, AddMonoidAlgebra.coeff P (e i) • MvPolynomial.monomial (e i) (1 : ℂ) := by
  let T := (Finsupp.finite_of_degree_le (σ := σ) N).toFinset
  refine ⟨T.card, fun i => (T.equivFin.symm i : σ →₀ ℕ), fun P hP => ?_⟩
  rw [T.equivFin.symm.sum_comp (fun d : T => AddMonoidAlgebra.coeff P (d : σ →₀ ℕ) •
    MvPolynomial.monomial (d : σ →₀ ℕ) (1 : ℂ)),
    Finset.sum_coe_sort T fun d => AddMonoidAlgebra.coeff P d • MvPolynomial.monomial d (1 : ℂ)]
  simp only [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  conv_lhs => rw [P.as_sum]
  refine Finset.sum_subset (fun d hd => ?_) fun d _ hd => ?_
  · simp only [T, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    exact (MvPolynomial.le_totalDegree hd).trans hP
  · rw [MvPolynomial.notMem_support_iff.1 hd, map_zero]

theorem exists_coefFam [Group G] [Finite σ] (ρ : G → Module.End ℂ (MvPolynomial σ ℂ))
    (hm : ∀ a b P, ρ (a * b) P = ρ a (ρ b P)) (hd : ∀ a P, (ρ a P).totalDegree ≤ P.totalDegree)
    (hc : ∀ P, CoefCont fun k => ρ k P) (φ : MvPolynomial σ ℂ) :
    ∃ (n : ℕ) (φs : Fin n → MvPolynomial σ ℂ) (c : Fin n → G → ℂ), IsCoefFam c ∧ ∀ k, ρ k φ = ∑ i, c i k • φs i := by
  obtain ⟨n, e, he⟩ := exists_monomials (σ := σ) φ.totalDegree
  refine ⟨n, fun i => MvPolynomial.monomial (e i) 1, fun i k => AddMonoidAlgebra.coeff (ρ k φ) (e i),
    ⟨fun i => hc φ _, fun k₀ i => ⟨fun j => AddMonoidAlgebra.coeff (ρ k₀ (MvPolynomial.monomial (e j) 1)) (e i),
      fun k => ?_⟩⟩, fun k => he _ (hd k φ)⟩
  beta_reduce
  rw [hm]
  conv_lhs => rw [he _ (hd k φ)]

  simp only [map_sum, map_smul, MvPolynomial.coeff_sum, MvPolynomial.coeff_smul, smul_eq_mul]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

end General

theorem signBlockDeterminant_ne_zero_of_mem_maxCompact {n : ℕ} {ε : Fin n → Bool} (e : Bool) {k : Matrix (Fin n) (Fin n) ℂ}
    (hk : k ∈ Formalism.REAL.Kset ε) : signBlockDeterminant ε e k ≠ 0 := by
  have hd : k.det ≠ 0 := (Matrix.isUnit_iff_isUnit_det k).1 (Unitary.isUnit_coe (U := ⟨k, hk.1⟩)) |>.ne_zero
  rw [Matrix.twoBlockTriangular_det k (fun i => ε i = e) (fun i hi j hj => by
    have h := congrFun (congrFun hk.2 i) j
    simp only [Formalism.REAL.Jm, Matrix.mul_diagonal, Matrix.diagonal_mul] at h
    cases e <;> simp only [Bool.not_eq_true, Bool.not_eq_false] at hi <;> simp [hi, hj] at h <;>
      first | linear_combination (1 / 2 : ℂ) * h | linear_combination (-1 / 2 : ℂ) * h)] at hd
  have := left_ne_zero_of_mul hd
  unfold signBlockDeterminant
  convert this
  rfl

theorem continuous_signBlockDeterminant {n : ℕ} (ε : Fin n → Bool) (e : Bool) : Continuous (signBlockDeterminant ε e) :=
  (continuous_id.matrix_submatrix _ _).matrix_det

theorem continuous_toMK {n : ℕ} (ε : Fin n → Bool) : Continuous fun k : Formalism.REAL.KG ε => Formalism.REAL.toMK k :=
  ((Formalism.REAL.isClosedEmbeddingMatrix n ε).1.isEmbedding.comp Topology.IsEmbedding.subtypeVal).continuous

variable {D : D7}

theorem unframe_mem {W : HSp D} {S' : D.what₂.Tau → SPar} (M' : DSModel W S') (τ : D.what₂.Tau)
    {k : Matrix (Fin W.rank) (Fin W.rank) ℂ} (hk : k ∈ Formalism.REAL.Kset (M'.ε τ)) :
    (M'.fr τ)⁻¹ * k * M'.fr τ ∈ Formalism.QuantumDeterminants.UH (gramAt D W τ) := by
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 (M'.fr_unit τ)
  have hJ : kᴴ * Formalism.REAL.Jm (M'.ε τ) * k = Formalism.REAL.Jm (M'.ε τ) := (Formalism.REAL.maximal_compact_facts _ _).1 k hk
  have hJ' : ∀ A : Matrix (Fin W.rank) (Fin W.rank) ℂ,
      kᴴ * (Formalism.REAL.Jm (M'.ε τ) * (k * A)) = Formalism.REAL.Jm (M'.ε τ) * A := fun A => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hJ]
  have e1 : ((M'.fr τ)⁻¹)ᴴ * (M'.fr τ)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv _ hd]; simp
  have e2 : ∀ A : Matrix (Fin W.rank) (Fin W.rank) ℂ, ((M'.fr τ)⁻¹)ᴴ * ((M'.fr τ)ᴴ * A) = A := fun A => by
    rw [← Matrix.mul_assoc, e1, Matrix.one_mul]
  change ((M'.fr τ)⁻¹ * k * M'.fr τ)ᴴ * gramAt D W τ * ((M'.fr τ)⁻¹ * k * M'.fr τ) = gramAt D W τ
  rw [← M'.fr_gram τ]
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc, e2, Matrix.mul_nonsing_inv_cancel_left _ _ hd, hJ']

theorem elt_mul {θ : InfFam D} (hθ : IsInfFam θ) {W : HSp D} {S' : D.what₂.Tau → SPar} (M' : DSModel W S')
    (τ : D.what₂.Tau) {a b : Matrix (Fin W.rank) (Fin W.rank) ℂ} (ha : a ∈ Formalism.REAL.Kset (M'.ε τ))
    (hb : b ∈ Formalism.REAL.Kset (M'.ε τ)) : elt θ M' τ (a * b) = elt θ M' τ a * elt θ M' τ b := by
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 (M'.fr_unit τ)
  rw [elt, elt, elt, ← atTau_mul hθ W τ (unframe_mem M' τ ha) (unframe_mem M' τ hb)]
  simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hd]

theorem elt_one' {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S)
    (τ : D.what₂.Tau) : elt θ M τ 1 = 1 := by
  rw [elt, Matrix.mul_one, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)), atTau_one hθ]

theorem coefCont_subst {G : Type} [TopologicalSpace G] {a b : ℕ} (τ : D.what₂.Tau) (ε : Fin a → Bool)
    (ε' : Fin b → Bool) (g : Matrix (Fin a) (Fin a) ℂ) {k : G → Matrix (Fin b) (Fin b) ℂ} (hk : Continuous k)
    (P : PolF D b a) : CoefCont fun x => subst τ ε ε' g (k x) P := by
  unfold subst
  refine CoefCont.aeval (fun v => ?_) P
  split_ifs
  all_goals first
    | exact CoefCont.const _
    | refine CoefCont.sum fun l => CoefCont.sum fun m => CoefCont.smul ?_ (CoefCont.const _)
  · exact (hk.matrix_elem _ _).mul continuous_const
  · exact ((hk.matrix_elem _ _).mul continuous_const).star

theorem fock_orbit_coefFam : ∀ (D : D7) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (f : WO V W → ℂ) (τ : D.what₂.Tau) (aS aT : ℚ), IsInfFam θ → Function.Injective (ptOf ψ θ M M' f) → GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.CompactFock ψ θ M M' ω f τ aS aT → ∀ φ : PolF D W.rank V.rank, ∃ (n : ℕ) (φs : Fin n → PolF D W.rank V.rank) (c : Fin n → Formalism.REAL.KG (M'.ε τ) → ℂ), IsCoefFam c ∧ ∀ k, ω (1, GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.elt θ M' τ (Formalism.REAL.toMK k)) (ptOf ψ θ M M' f φ) = ptOf ψ θ M M' f (∑ i, c i k • φs i) := by
  intro D V W S S' M M' θ ψ ω f τ aS aT hθ hpt hC φ
  obtain ⟨x, y, -, -, hc⟩ := hC
  let pt : PolF D W.rank V.rank →ₗ[ℂ] (WO V W → ℂ) := pureTensorO ψ θ V W (cart M) (cart M') (onb M) (onb M') f
  have hp : ptOf ψ θ M M' f = pt := rfl
  rw [hp] at hpt hc ⊢
  let s : Formalism.REAL.KG (M'.ε τ) → ℂ := fun k => signBlockDeterminant (M.ε τ) true 1 ^ x true * signBlockDeterminant (M.ε τ) false 1 ^ x false *
    (signBlockDeterminant (M'.ε τ) true (Formalism.REAL.toMK k) ^ y true * signBlockDeterminant (M'.ε τ) false (Formalism.REAL.toMK k) ^ y false)
  let ρ : Formalism.REAL.KG (M'.ε τ) → Module.End ℂ (PolF D W.rank V.rank) := fun k =>
    s k • (subst τ (M.ε τ) (M'.ε τ) ((1 : Matrix (Fin V.rank) (Fin V.rank) ℂ).map (starRingEnd ℂ))
      (Formalism.REAL.toMK k)).toLinearMap
  have key : ∀ k P, ω (1, elt θ M' τ (Formalism.REAL.toMK k)) (pt P) = pt (ρ k P) := fun k P => by
    have := hc 1 ⟨one_mem _, by rw [Matrix.one_mul, Matrix.mul_one]⟩ (Formalism.REAL.toMK k) k.2 P
    rw [elt_one' hθ, ← map_smul] at this
    exact this
  have hz : ∀ e, Continuous fun k : Formalism.REAL.KG (M'.ε τ) => signBlockDeterminant (M'.ε τ) e (Formalism.REAL.toMK k) ^ y e := fun e =>
    ((continuous_signBlockDeterminant _ e).comp (continuous_toMK _)).zpow₀ _ fun k => Or.inl (signBlockDeterminant_ne_zero_of_mem_maxCompact e k.2)
  have hs : Continuous s := continuous_const.mul ((hz true).mul (hz false))
  obtain ⟨n, φs, c, h1, h2⟩ := exists_coefFam ρ (fun a b P => hpt (by
      have e : Formalism.REAL.toMK (a * b) = Formalism.REAL.toMK a * Formalism.REAL.toMK b := rfl
      rw [← key, ← key, ← key, e, elt_mul hθ M' τ a.2 b.2, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk,
        mul_one]))
    (fun a P => (MvPolynomial.totalDegree_smul_le _ _).trans
      (GlobalTheory.Chain.RealIt.SubstDeg.totalDegree_subst_le _ _ _ _ _ _ _ _ _))
    (fun P => CoefCont.smul hs (coefCont_subst τ _ _ _ (continuous_toMK _) P)) φ
  exact ⟨n, φs, c, h1, fun k => by rw [key, h2]⟩

end GlobalTheory.Chain.IoLift.FockOrbit

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.weilDatum_transports_heisenbergMatrixCoeffs : ∀ (D : D7) (V W : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χS χT ω → ∀ (g : GA D V) (h : GA D W) (f : WO V W → ℂ), IsThetaFunO ψ V W f → ∀ (μ₀ : Measure (WO V W)) (𝓕₀ : Set (WO V W)), μ₀.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V) 𝓕₀ μ₀ → ∀ w₀ : WO V W, ∫ w in 𝓕₀, heisO ψ V W (actO V W g h w₀) (ω (g, h) f) w * starRingEnd ℂ (ω (g, h) f w) ∂μ₀ = ∫ w in 𝓕₀, heisO ψ V W w₀ f w * starRingEnd ℂ (f w) ∂μ₀ := by
  first | exact @GlobalTheory.WeilCoeff.heis_coeff_eq | exact GlobalTheory.WeilCoeff.heis_coeff_eq | (intros; apply GlobalTheory.WeilCoeff.heis_coeff_eq <;> assumption)
end
