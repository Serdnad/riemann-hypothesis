module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPairingSingleNe
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle067
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle198
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle195
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle216
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle323
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.L2UnitaryRepresentationData
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle328
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle210
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle007
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffSetIntegralNat
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle013
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FinPartDetAtInvInt
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle330
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle013
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle010
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle277
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle287
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle324
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector

@[expose] public section

section

open Matrix Formalism.UG GlobalTheory.Hk3 GlobalTheory.FinWeil GlobalTheory.SphTheta ValuativeRel Classical
open GlobalTheory.LFun (HasSatU IsSatVecU heckeVec)
open GlobalTheory.LGrp (bcParam extProd)
open GlobalTheory.WeilM (UG IsQuad Darboux symp sbClass SB IsWeilB IsWeilPair TestClass schr dbl diagCols)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace (str chi IsUnramAdd)
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.SphTheta.TorusVac

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

def lmulI {n' n : ℕ} (A : Matrix (Fin n') (Fin n') L) : Matrix (Fin n') (Fin n) L →ₗ[intL L] Matrix (Fin n') (Fin n) L where
  toFun x := A * x
  map_add' := Matrix.mul_add A
  map_smul' r x := Matrix.mul_smul A r x

def ex (n' : ℕ) (k : Fin (n' / 2)) (i : Fin n') : ℤ :=
  if i = lo n' k then 1 else if i = (lo n' k).rev then -1 else 0

theorem tMat_single (ϖ : L) (n' : ℕ) (k : Fin (n' / 2)) :
    tMat ϖ n' (n' / 2) (Pi.single k 1) = Matrix.diagonal (fun i => ϖ ^ ex n' k i) := by
  unfold tMat
  congr 1
  funext i
  have hk := k.2
  have hi := i.2
  simp only [ex, Pi.single_apply, lo, Fin.ext_iff, Fin.val_rev]
  split_ifs <;> simp_all <;> omega

variable {σ : L →+* L} {δ : L} {ψ : AddChar L ℂ} {n n' : ℕ}

theorem pairing_unitary (h : GU σ n') (x y : Matrix (Fin n') (Fin n) L) :
    pairing σ δ ψ (h.1.1 * x) (h.1.1 * y) = pairing σ δ ψ x y := by
  have hu : cT σ h.1.1 * antiJ L n' * h.1.1 = antiJ L n' := h.2
  have hl : locH σ δ (antiG L n) (antiG L n') (h.1.1 * x) (h.1.1 * y) = locH σ δ (antiG L n) (antiG L n') x y := by
    unfold locH
    congr 1
    have e1 : ((h.1.1 * y).map σ)ᵀ = (y.map σ)ᵀ * cT σ h.1.1 := by
      rw [Matrix.map_mul, Matrix.transpose_mul]; rfl
    have e2 : ((antiG L n' : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) = antiJ L n' := rfl
    rw [e1, e2]
    congr 1
    calc _ = (((antiG L n)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * (y.map σ)ᵀ * (cT σ h.1.1 * antiJ L n' * h.1.1) * x := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [hu]
  have e3 : ∀ a b : Matrix (Fin n') (Fin n) L, pairing σ δ ψ a b =
      ψ (locH σ δ (antiG L n) (antiG L n') a b + σ (locH σ δ (antiG L n) (antiG L n') a b)) := by
    intro a b; rw [locH_antiG]; rfl
  rw [e3, e3, hl]

theorem mul_inv_val (t : GU σ n') : t.1.1 * (t⁻¹).1.1 = 1 := by
  rw [show t.1.1 * (t⁻¹).1.1 = (t * t⁻¹).1.1 from rfl, mul_inv_cancel]; rfl

theorem selfDual_map (t : GU σ n') {A : Submodule (intL L) (Matrix (Fin n') (Fin n) L)}
    (hA : SelfDual (pairing σ δ ψ) A) : SelfDual (pairing σ δ ψ) (A.map (lmulI t.1.1)) := by
  intro x
  constructor
  · rintro ⟨y, hy, rfl⟩ _ ⟨b, hb, rfl⟩
    show pairing σ δ ψ (t.1.1 * y) (t.1.1 * b) = 1
    rw [pairing_unitary]
    exact (hA y).1 hy b hb
  · intro H
    have hy : (t⁻¹).1.1 * x ∈ A := by
      refine (hA _).2 fun b hb => ?_
      rw [← pairing_unitary t, ← Matrix.mul_assoc, mul_inv_val, Matrix.one_mul]
      exact H _ ⟨b, hb, rfl⟩
    refine ⟨_, hy, ?_⟩
    show t.1.1 * ((t⁻¹).1.1 * x) = x
    rw [← Matrix.mul_assoc, mul_inv_val, Matrix.one_mul]

theorem idx_translate_ne {ϖ : L} {q : ℕ} (hU : IsUnramInv ϖ σ q) (t : GU σ n') (d : Fin n' → ℤ)
    (ht : t.1.1 = Matrix.diagonal fun i => ϖ ^ d i) :
    idx (intMat L (Fin n') (Fin n)) ((intMat L (Fin n') (Fin n)).map (lmulI t.1.1)) ≠ 0 := by
  have h := GlobalTheory.LatIdx.relIndex_intMat_translate ϖ σ q hU n' n d t ht 1 (one_mem _) 1 (one_mem _)
  simp only [one_mul, mul_one] at h
  have e1 : (intMat L (Fin n') (Fin n)).toAddSubgroup = GlobalTheory.InertHomIdx.intMat L n' n :=
    AddSubgroup.ext fun _ => Iff.rfl
  have e2 : ((intMat L (Fin n') (Fin n)).map (lmulI (n := n) t.1.1)).toAddSubgroup =
      AddSubgroup.map (GlobalTheory.InertHomIdx.lmul t.1.1) (GlobalTheory.InertHomIdx.intMat L n' n) :=
    AddSubgroup.ext fun _ => Iff.rfl
  unfold idx
  rw [e1, e2, h]
  exact pow_ne_zero _ (pow_ne_zero _ (by have := hU.2.2.2.2.2.1; omega))

theorem mem_of_mixLat {ϖ : L} (hϖ : Valued.v ϖ ≤ 1) (k : Fin (n' / 2)) (t : GU σ n')
    (hT : t.1.1 = Matrix.diagonal fun i => ϖ ^ ex n' k i) {x a : Matrix (Fin n') (Fin n) L}
    (hx : x ∈ (intMat L (Fin n') (Fin n)).map (lmulI t.1.1)) (ha : a ∈ mixLat L n' n)
    (hxa : x - a ∈ intMat L (Fin n') (Fin n)) : x ∈ intMat L (Fin n') (Fin n) := by
  obtain ⟨y, hy, rfl⟩ := hx
  intro r c
  by_cases hr : r = (lo n' k).rev
  · have hk := k.2
    have h0 : a r c = 0 := (ha r c).1 (Or.inl (by subst hr; simp only [lo, Fin.val_rev]; omega))
    have := hxa r c
    rwa [Matrix.sub_apply, h0, sub_zero] at this
  · show (t.1.1 * y) r c ∈ intL L
    rw [hT, Matrix.diagonal_mul]
    have hp : ϖ ^ ex n' k r ∈ intL L := by
      have he : ex n' k r = 1 ∨ ex n' k r = 0 := by
        unfold ex; split_ifs <;> simp_all
      rcases he with he | he <;> rw [he]
      · simpa using mem_intL.2 hϖ
      · simpa using one_mem (intL L)
    exact mul_mem hp (hy r c)

end GlobalTheory.SphTheta.TorusVac


open GlobalTheory.SphTheta.TorusVac in
theorem GlobalTheory.SphTheta.mixed_torus_value : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L) (ψ : AddChar L ℂ) (n n' : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M) (ω : GU σ n × GU σ n' →* Module.End ℂ M) (s : M), IsStd ϖ σ q δ ψ ρ ω s → CayleyRule q n ρ (ω.comp (MonoidHom.inr _ _)) s → ∀ ℓ : M →ₗ[ℂ] ℂ, ℓ s = 1 → (∀ a ∈ mixLat L n' n, ∀ v, ℓ (ρ a v) = ℓ v) → (∀ x, (¬ ∃ a ∈ mixLat L n' n, x - a ∈ intMat L (Fin n') (Fin n)) → ℓ (ρ x s) = 0) → ∀ (k : Fin (n' / 2)) (t : GU σ n'), t.1.1 = tMat ϖ n' (n' / 2) (Pi.single k 1) → ℓ (ω (1, t) s) = (-1) ^ n * (q : ℂ) ^ (-(n : ℤ)) := by
  intro L _ _ ϖ σ q δ ψ n n' M _ _ ρ ω s hS hC ℓ hℓs hℓmix hℓzero k t ht
  have hU := hS.1.unr
  have hH := hS.isHeis
  have hΛ := hS.selfDual
  have hϖle : Valued.v ϖ ≤ 1 := by
    rw [hU.2.2.2.1]; exact_mod_cast (by decide : (Multiplicative.ofAdd (-1:ℤ)) ≤ 1)
  have hT : t.1.1 = Matrix.diagonal (fun i => ϖ ^ ex n' k i) := ht.trans (tMat_single ϖ n' k)
  have hΛ' := selfDual_map (n := n) (δ := δ) (ψ := ψ) t hΛ
  have hidx := idx_translate_ne (n := n) hU t _ hT
  obtain ⟨e, he1, heinv⟩ := GlobalTheory.T.exists_heisenbergInvariant_linearForm_isotropic_vacuum hH _ hΛ s hS.2.1 hS.fixes hS.2.2.2 _ (fun a ha b hb => hH.iso hΛ ha hb)
  have hv : Fixes ρ ((intMat L (Fin n') (Fin n)).map (lmulI t.1.1)) (ω (1, t) s) := by
    rintro _ ⟨y, hy, rfl⟩
    have h1 := congrArg (fun F : Module.End ℂ M => F s) (hS.1.norm 1 t y)
    simp only [Module.End.mul_apply] at h1
    rw [hS.fixes y hy] at h1
    simp at h1
    exact h1.symm
  have hsum : ℓ (sumOp ρ (intMat L (Fin n') (Fin n)) ((intMat L (Fin n') (Fin n)).map (lmulI t.1.1)) s) = 1 := by
    obtain ⟨N, f, hf, hu⟩ := ((GlobalTheory.T.sumOp_transversal_fixes_linear_and_of_le hH _ _ hΛ').2.1 hidx).1

    rw [((GlobalTheory.T.sumOp_transversal_fixes_linear_and_of_le hH _ _ hΛ').1 s hS.fixes (Fin N) f hf hu).1, map_sum]
    obtain ⟨i0, hi0, huniq⟩ := hu 0 (zero_mem _)
    have key : ∀ i, ℓ (ρ (f i) s) = if i = i0 then 1 else 0 := by
      intro i
      by_cases hfi : f i ∈ intMat L (Fin n') (Fin n)
      · have : i = i0 := huniq i (by show 0 - f i ∈ _; rw [zero_sub]; exact neg_mem hfi)
        rw [if_pos this, hS.fixes _ hfi, hℓs]
      · have hne : i ≠ i0 := by
          rintro rfl
          apply hfi
          have := neg_mem hi0
          rwa [zero_sub, neg_neg] at this
        rw [if_neg hne]
        apply hℓzero
        rintro ⟨a, ha, hxa⟩
        exact hfi (mem_of_mixLat hϖle k t hT (hf i) ha hxa)
    simp only [key, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  obtain ⟨hd, hint, hord⟩ := GlobalTheory.T.cayley_unitaryTorus_inv_det_integral_order L ϖ σ q hU hS.v_two n' k t ht
  have hev := hC e heinv t⁻¹ hd hint
  rw [inv_inv, hord, he1, mul_one] at hev
  have hco := (GlobalTheory.T.heisenbergQuotientOpSum_vacuum_commensurable_selfDualLattice hH _ hΛ s hS.2.1 hS.fixes hS.2.2.2 _ hΛ' hidx).2 e he1 heinv _ hv
  rw [hco, map_smul, hsum, smul_eq_mul, mul_one]
  simp only [MonoidHom.comp_apply, MonoidHom.inr_apply] at hev
  rw [hev, _root_.zpow_neg, zpow_one, mul_inv, _root_.zpow_neg, zpow_natCast, ← inv_pow, inv_neg, inv_one]
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

namespace GlobalTheory.ArchRec.PairVanish

open GlobalTheory.ArchRec.PairTensor (ext_ctr exists_map)
open GlobalTheory.Chain.IoLift.UImg (sumAct sumMod sumAct_single)

variable {p q r s : ℕ} {T : GrpData p q} (R : DSRep T)

theorem ctr_map_right {U U' : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup U'] [Module ℂ U']
    (g : U →ₗ[ℂ] U') (v : R.HK.V) (z : R.HK.V ⊗[ℂ] U) :
    ctr R U' v (TensorProduct.map LinearMap.id g z) = g (ctr R U v z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [ctr_tmul]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem exists_universal (M : GKMod r s) (a : Mat p q →ₗ[ℂ] Module.End ℂ M.V)
    (hc : ∀ Y Z, a Y * M.act Z = M.act Z * a Y) (U : Type) [AddCommGroup U] [Module ℂ U] :
    ∃ (Q : GKMod r s) (B₀ : M.V →ₗ[ℂ] R.HK.V →ₛₗ[starRingEnd ℂ] Q.V), PInv a R B₀ ∧
      (∀ Z P v, B₀ (M.act Z P) v = Q.act Z (B₀ P v)) ∧
      ∀ P v, B₀ P v = 0 → ∀ B : M.V →ₗ[ℂ] R.HK.V →ₛₗ[starRingEnd ℂ] U, PInv a R B → B P v = 0 := by

  obtain ⟨G, hG⟩ : ∃ G : Set (R.HK.V →₀ M.V), G =
      {x | (∃ (P : M.V) (v w : R.HK.V),
          x = Finsupp.single (v + w) P - Finsupp.single v P - Finsupp.single w P) ∨
        (∃ (P : M.V) (v : R.HK.V) (c : ℂ),
          x = Finsupp.single (c • v) P - starRingEnd ℂ c • Finsupp.single v P) ∨
        ∃ (P : M.V) (v : R.HK.V) (Z : Mat p q),
          Z ∈ upq p q ∧ x = Finsupp.single v (a Z P) + Finsupp.single (R.HK.act Z v) P} := ⟨_, rfl⟩
  obtain ⟨N, hNdef⟩ : ∃ N : Submodule ℂ (R.HK.V →₀ M.V), N = Submodule.span ℂ G := ⟨_, rfl⟩
  have hGN : ∀ x ∈ G, x ∈ N := fun x hx => hNdef ▸ Submodule.subset_span hx

  have hN : ∀ Z : Mat r s, N ≤ N.comap (sumAct M R.HK.V Z) := by
    intro Z
    conv_lhs => rw [hNdef]
    rw [Submodule.span_le]
    intro x hx
    rw [hG] at hx
    rw [SetLike.mem_coe, Submodule.mem_comap]
    rcases hx with ⟨P, v, w, rfl⟩ | ⟨P, v, c, rfl⟩ | ⟨P, v, Y, hY, rfl⟩
    · refine hGN _ ?_
      rw [hG]
      exact Or.inl ⟨M.act Z P, v, w, by simp [sumAct_single]⟩
    · refine hGN _ ?_
      rw [hG]
      exact Or.inr (Or.inl ⟨M.act Z P, v, c, by simp [sumAct_single]⟩)
    · refine hGN _ ?_
      rw [hG]
      have hcomm : a Y (M.act Z P) = M.act Z (a Y P) := LinearMap.congr_fun (hc Y Z) P
      exact Or.inr (Or.inr ⟨M.act Z P, v, Y, hY, by simp [sumAct_single, hcomm]⟩)
  let actQ : Mat r s →ₗ[ℂ] Module.End ℂ ((R.HK.V →₀ M.V) ⧸ N) :=
    { toFun := fun Z => N.mapQ N (sumAct M R.HK.V Z) (hN Z)
      map_add' := fun Z Z' => by
        refine Submodule.linearMap_qext _ (LinearMap.ext fun y => ?_)
        simp [Submodule.mapQ_apply]
      map_smul' := fun c Z => by
        refine Submodule.linearMap_qext _ (LinearMap.ext fun y => ?_)
        simp [Submodule.mapQ_apply] }
  have hQ : ∀ Z y, actQ Z (Submodule.Quotient.mk y) = Submodule.Quotient.mk (sumAct M R.HK.V Z y) :=
    fun _ _ => rfl
  let Q : GKMod r s :=
    { V := (R.HK.V →₀ M.V) ⧸ N
      act := actQ
      lie := fun X Y => by
        have h : sumAct M R.HK.V (X * Y - Y * X) =
            sumAct M R.HK.V X * sumAct M R.HK.V Y - sumAct M R.HK.V Y * sumAct M R.HK.V X :=
          (sumMod M R.HK.V).lie X Y
        refine Submodule.linearMap_qext _ (LinearMap.ext fun y => ?_)
        simp only [LinearMap.comp_apply, Submodule.mkQ_apply, LinearMap.sub_apply, Module.End.mul_apply, hQ]
        rw [h]
        simp only [LinearMap.sub_apply, Module.End.mul_apply, Submodule.Quotient.mk_sub]
      kfin := fun x => by
        obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective N x
        obtain ⟨W, hW, hy, hK⟩ : ∃ W : Submodule ℂ (R.HK.V →₀ M.V), FiniteDimensional ℂ W ∧ y ∈ W ∧
            KStable (sumAct M R.HK.V) W := (sumMod M R.HK.V).kfin y
        refine ⟨W.map N.mkQ, Module.Finite.map W N.mkQ, Submodule.mem_map_of_mem hy, ?_⟩
        intro X hX w hw
        obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hw
        exact Submodule.mem_map_of_mem (hK X hX u hu)
      wts := fun x => by
        obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective N x
        have hy : y ∈ ⨆ μ : Ix r s → ℚ, wtSub (sumAct M R.HK.V) μ := (sumMod M R.HK.V).wts y
        have hle : (⨆ μ : Ix r s → ℚ, wtSub (sumAct M R.HK.V) μ).map N.mkQ ≤
            ⨆ μ : Ix r s → ℚ, wtSub actQ μ := by
          rw [Submodule.map_iSup]
          refine iSup_mono fun μ => ?_
          rw [Submodule.map_le_iff_le_comap]
          intro u hu
          rw [Submodule.mem_comap]
          simp only [wtSub, Submodule.mem_iInf, LinearMap.mem_ker] at hu ⊢
          intro i
          have hi := hu i
          simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply] at hi ⊢
          rw [Submodule.mkQ_apply, hQ, ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_sub, hi,
            Submodule.Quotient.mk_zero]
        exact hle (Submodule.mem_map_of_mem hy) }
  let B₀ : M.V →ₗ[ℂ] R.HK.V →ₛₗ[starRingEnd ℂ] ((R.HK.V →₀ M.V) ⧸ N) :=
    LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun P v => N.mkQ (Finsupp.single v P))
      (fun P P' v => by simp [Finsupp.single_add])
      (fun c P v => by
        simp only [RingHom.id_apply]
        rw [← Finsupp.smul_single, map_smul])
      (fun P v w => by
        rw [← map_add (f := _), ← sub_eq_zero, ← map_sub, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        refine hGN _ ?_
        rw [hG]
        exact Or.inl ⟨P, v, w, by abel⟩)
      (fun c P v => by
        rw [← map_smul, ← sub_eq_zero, ← map_sub, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        refine hGN _ ?_
        rw [hG]
        exact Or.inr (Or.inl ⟨P, v, c, rfl⟩))
  refine ⟨Q, B₀, ?_, ?_, ?_⟩
  · intro Z hZ P v
    show N.mkQ (Finsupp.single v (a Z P)) + N.mkQ (Finsupp.single (R.HK.act Z v) P) = 0
    rw [← map_add (f := _), Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    refine hGN _ ?_
    rw [hG]
    exact Or.inr (Or.inr ⟨P, v, Z, hZ, rfl⟩)
  · intro Z P v
    show N.mkQ (Finsupp.single v (M.act Z P)) = actQ Z (N.mkQ (Finsupp.single v P))
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, hQ, sumAct_single]
  · intro P v h B hB
    let L : (R.HK.V →₀ M.V) →ₗ[ℂ] U := Finsupp.lsum ℂ fun w => B.flip w
    have hL : ∀ w (P' : M.V), L (Finsupp.single w P') = B P' w := by
      intro w P'
      simp [L]
    have hNL : N ≤ LinearMap.ker L := by
      rw [hNdef, Submodule.span_le]
      intro x hx
      rw [hG] at hx
      rw [SetLike.mem_coe, LinearMap.mem_ker]
      rcases hx with ⟨P', w, w', rfl⟩ | ⟨P', w, c, rfl⟩ | ⟨P', w, Z, hZ, rfl⟩
      · simp [hL]
      · simp [hL]
      · rw [map_add (f := _), hL, hL]
        exact hB Z hZ P' w
    have h' : N.mkQ (Finsupp.single v P) = 0 := h
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h'
    have := hNL h'
    rw [LinearMap.mem_ker, hL] at this
    exact this

theorem pairNo_of_tensNo : ∀ (p q r s : ℕ) (T₁ : GrpData p q) (σ : Type) (a₁ : Mat p q →ₗ[ℂ] Module.End ℂ (MvPolynomial σ ℂ)) (a₂ : Mat r s →ₗ[ℂ] Module.End ℂ (MvPolynomial σ ℂ)) (R₁ : DSRep T₁), IsGK a₁ → IsGK a₂ → (∀ Y Z, a₁ Y * a₂ Z = a₂ Z * a₁ Y) → AdmGK R₁.HK → TensNo a₁ a₂ R₁ → PairNo a₁ R₁ := by
  intro p q r s T₁ σ a₁ a₂ R₁ h₁ h₂ hc hA hT U _ _ B hB

  let M : GKMod r s :=
    { V := MvPolynomial σ ℂ
      act := a₂
      lie := h₂.1
      kfin := h₂.2.1
      wts := h₂.2.2 }
  obtain ⟨Q, B₀, hB₀, hZ, huniv⟩ := exists_universal R₁ M a₁ hc U
  obtain ⟨f, hf, hfB⟩ := GlobalTheory.ArchRec.PairTensor.exists_map R₁ a₁ h₁ hA B₀ hB₀
  have hT' : TIntw a₁ a₂ R₁.HK Q f := by
    refine ⟨hf, fun Y => LinearMap.ext fun P => ?_⟩
    refine GlobalTheory.ArchRec.PairTensor.ext_ctr R₁ Q.V _ _ fun v => ?_
    simp only [LinearMap.comp_apply]
    rw [← hfB, ctr_map_right, ← hfB]
    exact hZ Y P v
  have hf0 : f = 0 := hT Q f hT'
  refine LinearMap.ext fun P => LinearMap.ext fun v => ?_
  rw [LinearMap.zero_apply, LinearMap.zero_apply]
  refine huniv P v ?_ B hB
  rw [hfB, hf0, LinearMap.zero_apply, map_zero]

end GlobalTheory.ArchRec.PairVanish
end

section

open Classical Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.casselmanWallach_multMap_equivariant_sobolevContinuous : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (E : Type) [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E] [CompleteSpace E] [T2Space E] (p : ℕ → Seminorm ℂ E) (ι : E →ₗ[ℂ] (GA D V → ℂ)) (N : ℕ) (π : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ → (E →L[ℂ] E)), (∀ d x, p d x = (GlobalTheory.Size.growthSob θ V d N (ι x)).toReal) → (∀ x d, GlobalTheory.Size.growthSob θ V d N (ι x) ≠ ⊤) → (∀ τ, ∀ g ∈ Formalism.MainNotions.S.UJset (M.ε τ), ∀ x, ι (π τ g x) = rTr V ((GlobalTheory.ChainFr.Fr.ofModel M).elt θ τ g) (ι x)) → ∀ T : MultilinearMap (RingHom.id ℂ) (fun τ : D.what₂.Tau => M.sm τ) E, (∀ τ, ∀ g ∈ Formalism.MainNotions.S.UJset (M.ε τ), ∀ (v : M.Vec) (w : M.sm τ), (w : M.H τ) = M.σ τ g (v τ) → T (Function.update v τ w) = π τ g (T v)) → (∀ τ (i : ℕ) (v : M.Vec), ∃ (L : List (List (Matrix (Fin V.rank) (Fin V.rank) ℂ))) (C : ℝ), (∀ l ∈ L, ∀ X ∈ l, X ∈ GlobalTheory.SmoothGlob.lieSet (M.ε τ)) ∧ ∀ w : M.sm τ, p i (T (Function.update v τ w)) ≤ C * GlobalTheory.SmoothGlob.sobNorm (M.σ τ) L w) → (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ (v : M.Vec) (w : M.sm τ), (w : M.H τ) = M.rep τ g (v τ) → ι (T (Function.update v τ w)) = rTr V (atTau θ V τ g) (ι (T v))) ∧ ∀ τ (v : M.Vec) (x : GA D V), ∃ ℓ : M.H τ →ₗ[ℂ] ℂ, Sobolev₂ (lieAt V τ) (M.rep τ) ℓ ∧ ∀ w : M.sm τ, ℓ w = ι (T (Function.update v τ w)) x := by
  intro D θ V S M E _ _ _ _ _ _ p ι N π hp hfin hπ T hTe hTc
  refine ⟨fun τ g hg v w hw => ?_, fun τ v x => ?_⟩
  · have hd : IsUnit (M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
    have hg' : M.fr τ * g * (M.fr τ)⁻¹ ∈ Formalism.MainNotions.S.UJset (M.ε τ) :=
      GlobalTheory.GardingVec.conj_mem (M.fr_unit τ) (M.fr_gram τ) hg
    rw [hTe τ _ hg' v w hw, hπ τ _ hg']
    have he : (GlobalTheory.ChainFr.Fr.ofModel M).elt θ τ (M.fr τ * g * (M.fr τ)⁻¹) = atTau θ V τ g := by
      show atTau θ V τ ((M.fr τ)⁻¹ * (M.fr τ * g * (M.fr τ)⁻¹) * M.fr τ) = atTau θ V τ g
      congr 1
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hd, Matrix.one_mul, Matrix.mul_assoc,
        Matrix.nonsing_inv_mul _ hd, Matrix.mul_one]
    rw [he]
  · let f : M.sm τ →ₗ[ℂ] ℂ := (LinearMap.proj x).comp (ι.comp (T.toLinearMap v τ))
    obtain ⟨ℓ, hℓ⟩ := LinearMap.exists_extend f
    have hℓw : ∀ w : M.sm τ, ℓ w = ι (T (Function.update v τ w)) x := fun w => by
      have := LinearMap.congr_fun hℓ w
      simpa [f, MultilinearMap.toLinearMap_apply] using this
    refine ⟨ℓ, ?_, hℓw⟩
    obtain ⟨L, C, hL, hC⟩ := hTc τ 0 v
    refine ⟨L.map (List.map fun X => (M.fr τ)⁻¹ * X * M.fr τ), GlobalTheory.Grow.height V x ^ N * C, ?_, fun w hw => ?_⟩
    · intro l hl X hX
      obtain ⟨l₀, hl₀, rfl⟩ := List.mem_map.1 hl
      obtain ⟨X₀, hX₀, rfl⟩ := List.mem_map.1 hX
      exact GlobalTheory.GKExtFields.conj_mem_lieAt M τ (hL l₀ hl₀ X₀ hX₀)
    · have hmem : w ∈ M.sm τ := Submodule.subset_span hw
      have hw' : ℓ w = ι (T (Function.update v τ ⟨w, hmem⟩)) x := hℓw ⟨w, hmem⟩
      rw [hw']
      set y := T (Function.update v τ ⟨w, hmem⟩)
      have hpos : 0 < GlobalTheory.Grow.height V x ^ N := pow_pos (GlobalTheory.Grow.height_pos V x) N
      have hsz : p 0 y = (GlobalTheory.Size.growthSize V N (ι y)).toReal := by
        rw [hp]; simp [GlobalTheory.Size.growthSob]
      have hne : GlobalTheory.Size.growthSize V N (ι y) ≠ ⊤ := by
        have := hfin y 0; simpa [GlobalTheory.Size.growthSob] using this
      have hb : ‖ι y x‖ ≤ GlobalTheory.Grow.height V x ^ N * p 0 y := by
        have h1 : ENNReal.ofReal (‖ι y x‖ / GlobalTheory.Grow.height V x ^ N) ≤ GlobalTheory.Size.growthSize V N (ι y) :=
          le_iSup (fun g => ENNReal.ofReal (‖ι y g‖ / GlobalTheory.Grow.height V g ^ N)) x
        rw [ENNReal.ofReal_le_iff_le_toReal hne, div_le_iff₀ hpos, ← hsz] at h1
        linarith
      have hs : ((L.map (List.map fun X => (M.fr τ)⁻¹ * X * M.fr τ)).map
          fun l => ‖l.foldr (dRep (M.rep τ)) w‖).sum = GlobalTheory.SmoothGlob.sobNorm (M.σ τ) L (⟨w, hmem⟩ : M.sm τ) := by
        unfold GlobalTheory.SmoothGlob.sobNorm
        rw [List.map_map]
        congr 1
        refine List.map_congr_left fun l _ => ?_
        simp only [Function.comp_apply, GlobalTheory.GKExtFields.foldr_dRep_conj]
      rw [hs, mul_assoc]
      exact hb.trans (mul_le_mul_of_nonneg_left (hC ⟨w, hmem⟩) hpos.le)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv
open Formalism.IndefR.Fin.LevelGroupLemmas (resG detAt)

namespace GlobalTheory.IdemSumF

theorem exists_idem_below : ∀ {D : D7} {P : Finset (Pl D.host.E)} {e : AE D}, IsIdemSum e P →
    ∃ ε : AF D.host.F, IsIdempotentElem ε ∧ algebraMap (AF D.host.F) (AE D) ε = e + cA D e :=
  fun he => Formalism.IndefR.Fin.LevelGroupLemmas.idemSum_eps he

end GlobalTheory.IdemSumF
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.norm_goodRows_finiteGroup_action : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.models_HE → R.models_gE → R.models_ν0 → ∀ g x, ‖R.gE g x‖ = ‖x‖ := by
  first | exact @GlobalTheory.norm_gE_rows | exact GlobalTheory.norm_gE_rows | (intros; apply GlobalTheory.norm_gE_rows <;> assumption)
end
