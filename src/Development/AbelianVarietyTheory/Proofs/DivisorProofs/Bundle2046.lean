module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle259
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle973
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle283
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1997
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankOrth
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsDefiniteOfAllPlus
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSignatureFromBlocks
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle003
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1992
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1733
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1956
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1674
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1673
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RDualC
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1975
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1129
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1163
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsConstAlongSingleton
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1996
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1891
import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactUnipFlag
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EisensteinIsotropicLine

@[expose] public section

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.JHMult

noncomputable section

namespace GlobalTheory.InvTransposeProd

open Matrix GlobalTheory.TypeTame
open scoped TensorProduct

variable {k : Type} [Field k] {h n : ℕ} {d : Fin h → ℕ}

def revPlace (e : (Σ a, Fin (d a)) ≃ Fin n) : (Σ a : Fin h, Fin (d (Fin.rev a))) ≃ Fin n :=
  (Equiv.sigmaCongrLeft (β := fun b => Fin (d b)) Fin.revPerm).trans e

theorem revPlace_apply (e : (Σ a, Fin (d a)) ≃ Fin n) (a : Fin h) (i : Fin (d (Fin.rev a))) :
    revPlace e ⟨a, i⟩ = e ⟨Fin.rev a, i⟩ := rfl

theorem blk_revPlace (e : (Σ a, Fin (d a)) ≃ Fin n) (x : Fin n) :
    blk e x = Fin.rev (blk (revPlace e) x) := by
  obtain ⟨⟨a, i⟩, rfl⟩ := (revPlace e).surjective x
  rw [blk_apply, revPlace_apply, blk_apply]

theorem mem_parab_revPlace (e : (Σ a, Fin (d a)) ≃ Fin n) {q : GL (Fin n) k} (hq : q ∈ parab k e) :
    invTranspose n q ∈ parab k (revPlace e) := by
  refine mem_parab.2 fun i j hij => ?_
  rw [invTranspose_val, Matrix.transpose_apply]
  refine mem_parab.1 (inv_mem hq) j i ?_
  rw [blk_revPlace e i, blk_revPlace e j]
  exact Fin.rev_lt_rev.2 hij

theorem mem_parab_of_revPlace (e : (Σ a, Fin (d a)) ≃ Fin n) {p : GL (Fin n) k}
    (hp : p ∈ parab k (revPlace e)) : invTranspose n p ∈ parab k e := by
  refine mem_parab.2 fun i j hij => ?_
  rw [invTranspose_val, Matrix.transpose_apply]
  refine mem_parab.1 (inv_mem hp) j i ?_
  rw [blk_revPlace e i, blk_revPlace e j] at hij
  exact Fin.rev_lt_rev.1 hij

theorem leviProj_revPlace (e : (Σ a, Fin (d a)) ≃ Fin n) (q : parab k e)
    (hq : invTranspose n (q : GL (Fin n) k) ∈ parab k (revPlace e)) (b : Fin h) :
    leviProj k (revPlace e) ⟨invTranspose n q, hq⟩ b =
      invTranspose (d (Fin.rev b)) (leviProj k e q (Fin.rev b)) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [invTranspose_val, Matrix.transpose_apply, ← Pi.inv_apply, ← map_inv, leviProj_apply, leviProj_apply]
  rfl

theorem det_invTranspose (m : ℕ) (g : GL (Fin m) k) :
    GeneralLinearGroup.det (invTranspose m g) = (GeneralLinearGroup.det g)⁻¹ := by
  ext
  rw [GeneralLinearGroup.val_det_apply, invTranspose_val, Matrix.det_transpose, ← GeneralLinearGroup.val_det_apply,
    map_inv]

omit [Field k] in
theorem modExp_rev (b : Fin h) :
    modExp (fun a => Fin (d (Fin.rev a))) b = -modExp (fun a => Fin (d a)) (Fin.rev b) := by
  unfold modExp
  simp only [Fintype.card_fin, Finset.sum_filter]
  have h1 : (∑ c : Fin h, if b < c then (d (Fin.rev c) : ℤ) else 0) =
      ∑ c : Fin h, if c < Fin.rev b then (d c : ℤ) else 0 :=
    Fintype.sum_equiv Fin.revPerm _ _ fun c => by simp [Fin.rev_lt_rev]
  have h2 : (∑ c : Fin h, if c < b then (d (Fin.rev c) : ℤ) else 0) =
      ∑ c : Fin h, if Fin.rev b < c then (d c : ℤ) else 0 :=
    Fintype.sum_equiv Fin.revPerm _ _ fun c => by simp [Fin.rev_lt_rev]
  rw [h1, h2]
  ring

section Local

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem deltaHalf_revPlace (e : (Σ a, Fin (d a)) ≃ Fin n) (q : parab k e)
    (hq : invTranspose n (q : GL (Fin n) k) ∈ parab k (revPlace e)) :
    deltaHalf k (fun a => Fin (d (Fin.rev a))) (leviProj k (revPlace e) ⟨invTranspose n q, hq⟩) =
      deltaHalf k (fun a => Fin (d a)) (leviProj k e q) := by
  rw [deltaHalf_apply, deltaHalf_apply]
  refine Fintype.prod_equiv Fin.revPerm _ _ fun b => ?_
  rw [leviProj_revPlace e q hq b, det_invTranspose, modExp_rev]
  simp only [Int.cast_neg, neg_div, absPow_neg, MonoidHom.inv_apply, map_inv, inv_inv, Fin.revPerm_apply]
  rfl

variable (X : Fin h → Type) [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]

def revTensor : (⨂[ℂ] a, X a) ≃ₗ[ℂ] ⨂[ℂ] a, X (Fin.rev a) :=
  PiTensorProduct.reindex ℂ X Fin.revPerm

theorem revTensor_tprod (z : ∀ a, X a) :
    revTensor X (PiTensorProduct.tprod ℂ z) = PiTensorProduct.tprod ℂ fun a => z (Fin.rev a) :=
  PiTensorProduct.reindex_tprod _ _

variable {X}

def revRep (π' : ∀ a, Representation ℂ (GL (Fin (d (Fin.rev a))) k) (X (Fin.rev a))) :
    Representation ℂ (Levi k fun a => Fin (d (Fin.rev a))) (⨂[ℂ] a, X a) where
  toFun g := (revTensor X).symm.toLinearMap ∘ₗ piTensor π' g ∘ₗ (revTensor X).toLinearMap
  map_one' := by ext; simp
  map_mul' g g' := by ext; simp

def revRepEquiv (π' : ∀ a, Representation ℂ (GL (Fin (d (Fin.rev a))) k) (X (Fin.rev a))) :
    (revRep π').Equiv (piTensor π') :=
  Representation.Equiv.mk (revTensor X) fun g => LinearMap.ext fun v => by
    simp [revRep]

theorem revRep_leviProj (e : (Σ a, Fin (d a)) ≃ Fin n)
    (π : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a)) (q : parab k e)
    (hq : invTranspose n (q : GL (Fin n) k) ∈ parab k (revPlace e)) :
    revRep (fun a => (π (Fin.rev a)).comp (invTranspose (d (Fin.rev a))))
        (leviProj k (revPlace e) ⟨invTranspose n q, hq⟩) = piTensor π (leviProj k e q) := by
  have key : (piTensor fun a => (π (Fin.rev a)).comp (invTranspose (d (Fin.rev a))))
        (leviProj k (revPlace e) ⟨invTranspose n q, hq⟩) ∘ₗ (revTensor X).toLinearMap =
      (revTensor X).toLinearMap ∘ₗ piTensor π (leviProj k e q) := by
    refine PiTensorProduct.ext (MultilinearMap.ext fun z => ?_)
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      revTensor_tprod, piTensor_tprod]
    congr 1
  refine LinearMap.ext fun v => ?_
  show (revTensor X).symm _ = _
  rw [(revTensor X).symm_apply_eq]
  exact LinearMap.congr_fun key v

end Local

theorem multiProd_comp_invTranspose : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (h n : ℕ) (d : Fin h → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n) (e' : (Σ a, Fin (d (Fin.rev a))) ≃ Fin n) (X : Fin h → Type) [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (π : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a)), (∀ a, IsSmooth (π a)) → Nonempty (Representation.Equiv ((multiProd e π).comp (GlobalTheory.TypeTame.invTranspose n)) (multiProd e' fun a => ((π (Fin.rev a)).comp (GlobalTheory.TypeTame.invTranspose (d (Fin.rev a))) : Representation ℂ (GL (Fin (d (Fin.rev a))) k) (X (Fin.rev a))))) := by
  intro k _ _ _ _ h n d e e' X _ _ π _
  set π' : ∀ a, Representation ℂ (GL (Fin (d (Fin.rev a))) k) (X (Fin.rev a)) :=
    fun a => (π (Fin.rev a)).comp (invTranspose (d (Fin.rev a))) with hπ'
  have key : ∀ (q : parab k e) (hq : invTranspose n (q : GL (Fin n) k) ∈ parab k (revPlace e)),
      ((GlobalTheory.SmGL.twist (revRep π') (deltaHalf k _)).comp (leviProj k (revPlace e))) ⟨invTranspose n q, hq⟩ =
        ((GlobalTheory.SmGL.twist (piTensor π) (deltaHalf k _)).comp (leviProj k e)) q := by
    intro q hq
    refine LinearMap.ext fun v => ?_
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, GlobalTheory.SmGL.twist_apply, GlobalTheory.SmGL.twist_apply, deltaHalf_revPlace e q hq,
      hπ', revRep_leviProj e π q hq]
  obtain ⟨A⟩ : Nonempty ((parInd (revPlace e) (revRep π')).Equiv
      ((multiProd e π).comp (invTranspose n))) := by
    refine Relabel.smInd_equiv_comp (P := parab k (revPlace e)) (Q := parab k e)
      (σ := (GlobalTheory.SmGL.twist (revRep π') (deltaHalf k _)).comp (leviProj k (revPlace e)))
      (τ := (GlobalTheory.SmGL.twist (piTensor π) (deltaHalf k _)).comp (leviProj k e))
      (invTranspose n) (invTranspose n) (continuous_invTranspose n) (continuous_invTranspose n)
      (invTranspose_invTranspose n) (invTranspose_invTranspose n)
      (fun q => ⟨⟨_, mem_parab_revPlace e q.2⟩, rfl, key q _⟩) (fun p => ?_)
    have hp : invTranspose n (invTranspose n (p : GL (Fin n) k)) ∈ parab k (revPlace e) := by
      rw [invTranspose_invTranspose]
      exact p.2
    refine ⟨⟨_, mem_parab_of_revPlace e p.2⟩, rfl, ?_⟩
    refine (key ⟨_, mem_parab_of_revPlace e p.2⟩ hp).symm.trans ?_
    exact congrArg _ (Subtype.ext (invTranspose_invTranspose n (p : GL (Fin n) k)))
  obtain ⟨B⟩ := GlobalTheory.T.product_representation_reorder_equiv k h n (fun a => d (Fin.rev a)) (revPlace e) e' (fun a => X (Fin.rev a)) π'
  exact ⟨A.symm.trans ((parIndEquiv (revPlace e) (revRepEquiv π')).trans B)⟩

end GlobalTheory.InvTransposeProd
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PlaneComplementSig

open Matrix

theorem hasSignature_plane : Formalism.UG.HasSignature (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ) 1 1 := by
  refine GlobalTheory.FrameComplement.hasSignature_of_frame (by simp)
    (Matrix.of fun i k => Sum.elim (fun _ => ![1, 1 / 2] i) (fun _ => ![1, -1 / 2] i) k) ?_
  ext (a | a) (b | b) <;> fin_cases a <;> fin_cases b <;>
    simp [Formalism.UG.Jpq, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, map_ofNat] <;> norm_num

theorem sig : ∀ (D : D7) (S S₁ : HSp D) (ι : S₁.V →ₗ[D.host.E] S.V) (x y : S.V) (q : ℕ), S.rank = S₁.rank + 2 →
    Formalism.BasicNotions.HSpace.IsIsomEmb S₁ S ι → S.hT x x = 0 → S.hT y y = 0 → S.hT x y = 1 →
    (∀ u, S.hT x (ι u) = 0 ∧ S.hT y (ι u) = 0) → NegIdx S (q + 1) →
    ∀ τ : D.host.E →+* ℂ, Formalism.UG.HasSignature (S₁.gram.map τ) (S₁.rank - q) q := by
  intro D S S₁ ι x y q hr hι hxx hyy hxy ho hneg τ
  have hτ : ∀ a, τ (star a) = starRingEnd ℂ (τ a) := D.sp.cm.cmUnram.2.1 τ

  have hS : Formalism.UG.HasSignature (S.gram.map τ) (S.rank - (q + 1)) (q + 1) := by
    obtain ⟨ρ, hσ | hσ⟩ := GlobalTheory.DefiniteMult.exists_tauE_or_conj D τ
    · subst hσ
      simpa [gramAt] using hneg ρ
    · subst hσ
      have h1 := GlobalTheory.BottomIsom.hasSignature_map_star (by simpa [gramAt] using hneg ρ)
      rw [Matrix.map_map] at h1
      exact h1
  obtain ⟨⟨a, b⟩, h₁⟩ := GlobalTheory.WittLow.exists_sig S₁ τ
  have c₁ := (Formalism.UG.P.sig_data _ _ _ h₁).1
  have cS := (Formalism.UG.P.sig_data _ _ _ hS).1
  simp only [Fintype.card_fin] at c₁ cS
  let v : Fin S₁.rank ⊕ Fin 2 → S.V := Sum.elim (fun i => ι (S₁.frame i)) ![x, y]
  have hyx : S.hT y x = 1 := by
    have h := S.herm.eq x y
    rw [hxy, map_one] at h
    exact h.symm
  have hv : (Matrix.of fun k l => S.hT (v k) (v l)) =
      fromBlocks S₁.gram 0 0 (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) D.host.E) := by
    ext (i | i) (j | j)
    · simp only [v, Matrix.of_apply, fromBlocks_apply₁₁, Sum.elim_inl, HSpace.gram]; exact hι _ _
    · fin_cases j
      · have h := S.herm.eq x (ι (S₁.frame i))
        rw [(ho _).1, map_zero] at h
        simp [v, ← h]
      · have h := S.herm.eq y (ι (S₁.frame i))
        rw [(ho _).2, map_zero] at h
        simp [v, ← h]
    · fin_cases i
      · simpa [v] using (ho _).1
      · simpa [v] using (ho _).2
    · fin_cases i <;> fin_cases j <;> simp [v, hxx, hyy, hxy, hyx]
  have hF : Formalism.UG.HasSignature ((Matrix.of fun k l => S.hT (v k) (v l)).map τ) (a + 1) (b + 1) := by
    rw [hv, Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero τ), Matrix.map_zero _ (map_zero τ)]
    have e : (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) D.host.E).map τ = !![0, 1; 1, 0] := by
      ext i j; fin_cases i <;> fin_cases j <;> simp
    rw [e]
    exact GlobalTheory.FrameComplement.hasSignature_fromBlocks h₁ hasSignature_plane
  have key := Formalism.BasicNotions.sig_family S τ hτ v hF hS
  have hb : b = q := by omega
  have ha : a = S₁.rank - q := by omega
  subst hb ha
  exact h₁

end GlobalTheory.PlaneComplementSig
end
end

section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair

noncomputable section

namespace GlobalTheory.GKPair

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem map_inv_map_star {B : Multiset ℂˣ} (h : B.map star = B.map (·⁻¹)) : (B.map (·⁻¹)).map star = B := by
  have e : (B.map (·⁻¹)).map star = (B.map star).map (·⁻¹) := by
    rw [Multiset.map_map, Multiset.map_map]
    refine Multiset.map_congr rfl fun u _ => ?_
    exact Units.ext (by simp)
  rw [e, h, Multiset.map_map]
  conv_rhs => rw [← Multiset.map_id B]
  exact Multiset.map_congr rfl fun u _ => inv_inv u

theorem paired_of_form (π : CuspSub E a) (L : π.V ≃ₗ⋆[ℂ] π.V)
    (hL : ∀ o ψ, L (π.op (invTOp o) ψ) = π.op o (L ψ)) (H : π.V →ₗ⋆[ℂ] π.V →ₗ[ℂ] ℂ)
    (hpos : ∀ φ, φ ≠ 0 → 0 < (H φ φ).re)
    (hfin : ∀ k φ ψ, H (π.op (.fin k) φ) (π.op (.fin k) ψ) = H φ ψ)
    (hcpt : ∀ k φ ψ, H (π.op (.cpt k) φ) (π.op (.cpt k) ψ) = H φ ψ)
    (hlie : ∀ X φ ψ, H (π.op (.lie X) φ) ψ + H φ (π.op (.lie X) ψ) = 0) :
    Paired π π invTOp := by
  let B : π.V →ₗ[ℂ] π.V →ₗ[ℂ] ℂ := (H.comp L.toLinearMap).flip
  have hB : ∀ φ ψ, B φ ψ = H (L ψ) φ := fun _ _ => rfl
  have h0 : ∀ φ, H φ φ = 0 → φ = 0 := fun φ h => by
    by_contra hφ
    have := hpos φ hφ
    rw [h, Complex.zero_re] at this
    exact lt_irrefl _ this
  refine ⟨B, fun φ h => h0 φ ?_, fun ψ h => ?_, fun k φ ψ => ?_, fun k φ ψ => ?_, fun X φ ψ => ?_⟩
  · have := h (L.symm φ)
    rwa [hB, LinearEquiv.apply_symm_apply] at this
  · have := h (L ψ)
    rw [hB] at this
    exact (map_eq_zero_iff L L.injective).1 (h0 _ this)
  · rw [hB, hB, hL, hfin]
  · rw [hB, hB, hL, hcpt]
  · rw [hB, hB, hL, add_comm]
    exact hlie X (L ψ) φ

theorem paired_invTOp (hJS : GlobalTheory.Published.JacquetShalikaRigidity) (hB : GlobalTheory.Published.CuspFormsBoundedGL)
    (hA : GlobalTheory.Published.AutomorphicFormsFiniteGL) (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (ha : 1 ≤ a) (π : CuspSub E a) (hπ : GlobalTheory.DiscSpec.IsNormalised π) : Paired π π invTOp := by
  obtain ⟨H, hH, hpos, hfin, hcpt, hlie⟩ := GlobalTheory.T.exists_invariant_hermitianForm_cuspidalRep hB E a π hπ
  obtain ⟨π₂, J, hJ⟩ := GlobalTheory.T.exists_complex_conjugate_cuspidal_representation E a (UpperTheory.V.TC.dual π)
  have hsat : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∃ B, (CG.mk π₂).HasSat w B ∧ (CG.mk π).HasSat w B := by
    refine (GlobalTheory.T.cuspidal_GL_local_components_eventually_satake hA E a π).mono fun w ⟨B, hBw⟩ => ⟨B, ?_, hBw⟩
    have h1 := UpperTheory.V.TC.hasSatGL_dual hBw
    have h2 := GlobalTheory.T.satake_parameter_GL_of_conj_linear_intertwiner E w a _ _ ((UpperTheory.V.TC.dual π).locRep w) (π₂.locRep w) J
      (fun g x => by rw [CuspSub.locRep_eq, CuspSub.locRep_eq, hJ]) _ h1
    have h3 := GlobalTheory.T.unitary_cuspidal_satake_parameter_star_eq_inv E a π H hH hpos hfin w B hBw
    rw [map_inv_map_star h3] at h2
    exact h2
  have e := hJS.strong_multiplicity_one ha (CG.mk π₂) (CG.mk π) hsat
  obtain ⟨T, hT⟩ : CuspSub.Iso π₂ π := Quotient.exact e
  let L : π.V ≃ₗ⋆[ℂ] π.V := ((UpperTheory.V.TC.toDual π).trans J).trans T
  refine paired_of_form π L (fun o ψ => ?_) H hpos hfin hcpt hlie
  change T (J (UpperTheory.V.TC.toDual π (π.op (invTOp o) ψ))) = π.op o (T (J (UpperTheory.V.TC.toDual π ψ)))
  rw [← UpperTheory.V.TC.op_toDual, hJ, hT]

end GlobalTheory.GKPair
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Nef

theorem semiAbelianLieSeminegative : GlobalTheory.Published.SemiAbelianLieSeminegative := by
  intro k _ _ C _ hs hp hc G _ hG W r hW i hi
  obtain ⟨C', _, π, hC', hdesc⟩ := GlobalTheory.T.semiNegative_descends_fieldExtension_curve k C ⟨hs, hp, hc⟩ (AlgebraicClosure k)
  have : IsIntegral C := GlobalTheory.LieSemineg.isIntegral_curve hs hc
  refine hdesc (Lie G) ?_ W r hW i hi
  exact GlobalTheory.NeronCurve.LieDescent.semiNeg_of_iso (GlobalTheory.NeronCurve.LieDescent.lieBaseIso π G).symm
    (GlobalTheory.T.lieSheaf_semiAbelian_semiNeg_of_isAlgClosed (AlgebraicClosure k) C' hC' _ (IsSemiAbelian.pullback π G hG))

end GlobalTheory.Nef
end
end

section

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability
open Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory.StdPar

section DimensionMonotonicity
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X : Matrix (Fin n) (Fin r) E}

theorem unip_maps_colSpan {T : Finset (Fin r)} {g : GAd σ J} (hg : g ∈ unip σ J X T) {I : Set (Fin r)}
    (hI : ∀ i ∈ I, ∀ l, l < i → l ∈ I) {y : Fin n → AF F ⊗[F] E} (hy : y ∈ colSpan F X I) :
    (matHom _ σ J g).1 *ᵥ y ∈ colSpan F X I := by
  have key : colSpan F X I ≤ (colSpan F X I).comap (matHom _ σ J g).1.mulVecLin := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, hi, rfl⟩
    have h1 := (Subgroup.mem_iInf.1 hg.1 i).2 _ (Submodule.subset_span ⟨i, rfl, rfl⟩)
    have h2 : colSpan F X {l | ∃ k ∈ T, l ≤ k ∧ k < i} ≤ colSpan F X I := by
      refine Submodule.span_mono (Set.image_mono ?_)
      rintro l ⟨k, -, hlk, hki⟩
      exact hI i hi l (lt_of_le_of_lt hlk hki)
    have h3 : (fun i => (adMat F X)ᵀ i) i ∈ colSpan F X I := Submodule.subset_span ⟨i, hi, rfl⟩
    show (matHom _ σ J g).1 *ᵥ _ ∈ colSpan F X I
    have := add_mem (h2 h1) h3
    rwa [sub_add_cancel] at this
  exact key hy

theorem unip_iff_colSpan {T : Finset (Fin r)} {g : GAd σ J} (hg : g ∈ unip σ J X T) {I : Set (Fin r)}
    (hI : ∀ i ∈ I, ∀ l, l < i → l ∈ I) (y : Fin n → AF F ⊗[F] E) :
    y ∈ colSpan F X I ↔ (matHom _ σ J g).1 *ᵥ y ∈ colSpan F X I := by
  refine ⟨unip_maps_colSpan hg hI, fun h => ?_⟩
  have := unip_maps_colSpan (inv_mem hg) hI h
  rwa [mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, one_mulVec] at this

end DimensionMonotonicity

theorem unip_mono_of_subset : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y →
      ∀ (S T : Finset (Fin r)), T ⊆ S → GlobalTheory.StdPar.unip σ J X T ≤ GlobalTheory.StdPar.unip σ J X S := by
  intro F E _ _ _ _ _ σ _ n J _ r X Y _ S T hTS g hg
  refine ⟨Subgroup.mem_iInf.2 fun j => ⟨unip_iff_colSpan hg ?_, fun y hy => ?_⟩,
    ⟨unip_iff_colSpan hg ?_, fun y hy => ?_⟩⟩
  · rintro i ⟨k, hk, hik, hkj⟩ l hl
    exact ⟨k, hk, (le_of_lt (lt_of_lt_of_le hl hik)), hkj⟩
  · refine Submodule.span_mono (Set.image_mono ?_) ((Subgroup.mem_iInf.1 hg.1 j).2 y hy)
    rintro l ⟨k, hk, h1, h2⟩
    exact ⟨k, hTS hk, h1, h2⟩
  · rintro i ⟨k, hk, hik⟩ l hl
    exact ⟨k, hk, le_of_lt (lt_of_lt_of_le hl hik)⟩
  · have hy' : y ∈ colPerp σ J X {i | ∃ k ∈ T, i ≤ k} := by
      simp only [colPerp, Submodule.mem_iInf] at hy ⊢
      rintro i ⟨k, hk, hik⟩
      exact hy i ⟨k, hTS hk, hik⟩
    refine Submodule.span_mono (Set.image_mono ?_) (hg.2.2 y hy')
    rintro l ⟨k, hk, h1⟩
    exact ⟨k, hTS hk, h1⟩

end GlobalTheory.StdPar
end
end

section

open NumberField MeasureTheory Matrix Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine
open GlobalTheory.Doubling (absE)
open scoped TensorProduct NNReal
open Formalism.UG (cT bc)


theorem _root_.GlobalTheory.T.parabolic_archimedean_eigenvector : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (x : Matrix (Fin n) (Fin 1) E) (pL : Matrix (Fin 1) (Fin n) E), pL * x = 1 → ∀ q : GAd σ J, (∀ w : InfinitePlace F, ∃ β : GL (Fin 1) (w.Completion ⊗[F] E), (matHom _ σ J (projArch σ J w q)).1 * x.map (inclR (F := F) w.Completion) = x.map (inclR (F := F) w.Completion) * β.1) → (∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), ∃ β : GL (Fin 1) (Fv F v ⊗[F] E), (matHom _ σ J (proj σ J v q)).1 * x.map (inclR (F := F) (Fv F v)) = x.map (inclR (F := F) (Fv F v)) * β.1) → ∃ l : (AF F ⊗[F] E)ˣ, (matHom _ σ J q).1 * adMat F x = l.1 • adMat F x := by
  first | exact @GlobalTheory.LineGlue.exists_idele_smul_of_local_lines | exact GlobalTheory.LineGlue.exists_idele_smul_of_local_lines | (intros; apply GlobalTheory.LineGlue.exists_idele_smul_of_local_lines <;> assumption)
end
