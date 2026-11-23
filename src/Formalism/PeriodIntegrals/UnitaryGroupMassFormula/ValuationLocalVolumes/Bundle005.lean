module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.LocalGramMatrixFrame
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.Bundle004
public import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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

namespace Formalism.L2.SG.Pf.NcVal.OmVSt.OmW

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  MeasureTheory NumberField IsDedekindDomain Matrix
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def piv (r : ℕ) (a : Fin (r + 1 + r)) : Fin (r + 1 + r) :=
  ⟨if a.val < r then a.val + (r + 1) else if a.val = r then r else a.val - (r + 1), by
    have := a.2; split_ifs <;> omega⟩

theorem piv_e (r : ℕ) (i : Fin r) : piv r (Fin.castAdd r i.castSucc) = Fin.natAdd (r + 1) i := by
  apply Fin.ext; simp [piv]; omega

theorem pivot_castAdd_last (r : ℕ) : piv r (Fin.castAdd r (Fin.last r)) = Fin.castAdd r (Fin.last r) := by
  apply Fin.ext; simp [piv]

theorem piv_f (r : ℕ) (i : Fin r) : piv r (Fin.natAdd (r + 1) i) = Fin.castAdd r i.castSucc := by
  apply Fin.ext
  simp only [piv, Fin.val_natAdd, Fin.val_castAdd, Fin.val_castSucc]
  rw [if_neg (by omega), if_neg (by omega)]
  omega

theorem piv_invol (r : ℕ) : Function.Involutive (piv r) := by
  intro a
  refine Fin.addCases (fun a => ?_) (fun i => by rw [piv_f, piv_e]) a
  exact Fin.lastCases (by rw [pivot_castAdd_last, pivot_castAdd_last]) (fun i => by rw [piv_e, piv_f]) a

variable {D : D7} (X : HidaSetting D) (u' : D.what₂.Word)

theorem hT_hv (a b : Fin (D.R.rS + 1 + D.R.rS)) :
    (VS D).hT (hv X u' a) (hv X u' b) =
      if b = piv D.R.rS a then (if a.val = D.R.rS then -((Tw u' : ℕ) : D.host.E) else 1) else 0 := by
  have hs := (VS D).herm
  refine Fin.addCases (fun a => ?_) (fun a => ?_) a <;> refine Fin.addCases (fun b => ?_) (fun b => ?_) b
  · refine Fin.lastCases ?_ (fun i => ?_) a <;> refine Fin.lastCases ?_ (fun j => ?_) b
    · rw [pivot_castAdd_last, if_pos rfl, if_pos (by simp)]
      simp only [hv, Fin.append_left, Fin.snoc_last]
      rw [X.zu_norm]; rfl
    · rw [pivot_castAdd_last, if_neg (fun h => by have := congrArg Fin.val h; simp at this <;> omega)]
      simp only [hv, Fin.append_left, Fin.snoc_last, Fin.snoc_castSucc]
      exact (hs.eq_iff).1 (X.zu_orth u' j).1
    · rw [piv_e, if_neg (fun h => by have := congrArg Fin.val h; simp at this <;> omega)]
      simp only [hv, Fin.append_left, Fin.snoc_last, Fin.snoc_castSucc]
      exact (X.zu_orth u' i).1
    · rw [piv_e, if_neg (fun h => by have := congrArg Fin.val h; simp at this <;> omega)]
      simp only [hv, Fin.append_left, Fin.snoc_castSucc]
      exact X.ee i j
  · refine Fin.lastCases ?_ (fun i => ?_) a
    · rw [pivot_castAdd_last, if_neg (fun h => by have := congrArg Fin.val h; simp at this <;> omega)]
      simp only [hv, Fin.append_left, Fin.append_right, Fin.snoc_last]
      exact (hs.eq_iff).1 (X.zu_orth u' b).2
    · rw [piv_e]
      simp only [hv, Fin.append_left, Fin.append_right, Fin.snoc_castSucc]
      rw [X.ef]
      by_cases h : i = b
      · subst h; rw [if_pos rfl, if_pos rfl, if_neg (by simp <;> omega)]
      · rw [if_neg h, if_neg (fun e => h ((Fin.natAdd_inj _).1 e).symm)]
  · refine Fin.lastCases ?_ (fun j => ?_) b
    · rw [piv_f, if_neg (fun h => by have := congrArg Fin.val h; simp at this <;> omega)]
      simp only [hv, Fin.append_left, Fin.append_right, Fin.snoc_last]
      exact (X.zu_orth u' a).2
    · rw [piv_f]
      simp only [hv, Fin.append_left, Fin.append_right, Fin.snoc_castSucc]
      rw [← (LinearMap.isSymm_def.1 hs) (X.eX j) (X.fY a), X.ef]
      by_cases h : j = a
      · subst h; rw [if_pos rfl, if_pos rfl, if_neg (by simp <;> omega), map_one]
      · rw [if_neg h, if_neg (fun e => h (Fin.castSucc_inj.1 (Fin.castAdd_inj.1 e))), map_zero]
  · rw [piv_f, if_neg (fun h => by have := congrArg Fin.val h; simp at this <;> omega)]
    simp only [hv, Fin.append_right]
    exact X.ff a b

def cD (a : Fin (D.R.rS + 1 + D.R.rS)) : X.B.I.E := if a.val = D.R.rS then -((Tw u' : ℕ) : X.B.I.E) else 1

theorem gram_eq : gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) =
    diagonal (cD X u') * (Function.Involutive.toPerm _ (piv_invol D.R.rS)).permMatrix X.B.I.E := by
  ext a b
  rw [diagonal_mul]
  show hE _ _ (tupH (frameOf X u') a) (tupH (frameOf X u') b) = _
  rw [tupH_eq, tupH_eq, hE_crdOf, hT_hv]
  simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def,
    Option.some.injEq, Function.Involutive.coe_toPerm, cD]
  by_cases h : b = piv D.R.rS a
  · have h' : piv D.R.rS a = b := h.symm
    rw [if_pos h]
    simp only [h', if_true, mul_one]
    split_ifs <;> simp
  · have h' : ¬ piv D.R.rS a = b := fun e => h e.symm
    simp [h, h']

theorem prod_cD : ∏ a, cD X u' a = -((Tw u' : ℕ) : X.B.I.E) := by
  rw [Finset.prod_eq_single (⟨D.R.rS, by omega⟩ : Fin (D.R.rS + 1 + D.R.rS))]
  · simp [cD]
  · intro b _ hb
    have : b.val ≠ D.R.rS := fun e => hb (Fin.ext e)
    simp [cD, this]
  · simp

theorem det_gram : ∃ s : ℤ, s * s = 1 ∧
    (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).det = (((-(Tw u' : ℤ)) * s : ℤ) : X.B.I.E) := by
  refine ⟨((Equiv.Perm.sign (Function.Involutive.toPerm _ (piv_invol D.R.rS)) : ℤˣ) : ℤ), ?_, ?_⟩
  · rw [← Units.val_mul, Int.units_mul_self, Units.val_one]
  · rw [gram_eq, det_mul, det_diagonal, det_permutation, prod_cD]
    push_cast
    rfl

theorem val_natCast_eq_one {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (t : ℕ)
    (ht : ((t : 𝓞 F)) ∉ v.asIdeal) : Valued.v ((t : ℕ) : Fv F v) = 1 := by
  have h1 : ((t : ℕ) : Fv F v) = algebraMap (𝓞 F) (Fv F v) (t : 𝓞 F) := by simp
  rw [h1]
  refine (HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := F) v (t : 𝓞 F)).trans ?_
  erw [HeightOneSpectrum.valuation_of_algebraMap]
  exact HeightOneSpectrum.intValuation_eq_one_iff.2 ht

theorem inclR_mem_OEv (v : PlX X) (x : 𝓞 X.B.I.E) :
    inclR (Fv X.B.I.F v) (x : X.B.I.E) ∈ OEv (E := X.B.I.E) v :=
  Submodule.subset_span ⟨x, trivial, rfl⟩

theorem omVDet_holds : OmVDet X u' := by
  intro v hT
  obtain ⟨s, hs, hd⟩ := det_gram X u'
  have hdet : (localGramMatrixFrame X u' v).det = inclR (Fv X.B.I.F v) ((((-(Tw u' : ℤ)) * s : ℤ) : 𝓞 X.B.I.E) : X.B.I.E) := by
    rw [localGramMatrixFrame, ← RingHom.mapMatrix_apply, ← RingHom.map_det, hd]
    push_cast; rfl
  set t : Fv X.B.I.F v := ((Tw u' : ℕ) : Fv X.B.I.F v) with ht_def
  have hv1 : Valued.v t = 1 := val_natCast_eq_one v _ hT
  have ht0 : t ≠ 0 := by
    intro h0; rw [h0, map_zero] at hv1; exact zero_ne_one hv1
  have hti : t⁻¹ ∈ v.adicCompletionIntegers X.B.I.F := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hv1, inv_one]
  refine ⟨(⟨t⁻¹, hti⟩ : v.adicCompletionIntegers X.B.I.F) • inclR (Fv X.B.I.F v) (((-s : ℤ) : 𝓞 X.B.I.E) : X.B.I.E),
    Submodule.smul_mem _ _ (inclR_mem_OEv X v _), ?_, ?_⟩
  · rw [hdet]; exact inclR_mem_OEv X v _
  · rw [hdet]
    have e1 : (⟨t⁻¹, hti⟩ : v.adicCompletionIntegers X.B.I.F) • inclR (Fv X.B.I.F v) (((-s : ℤ) : 𝓞 X.B.I.E) : X.B.I.E) =
        algebraMap (Fv X.B.I.F v) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) t⁻¹ *
          inclR (Fv X.B.I.F v) (((-s : ℤ) : 𝓞 X.B.I.E) : X.B.I.E) := by
      rw [← Algebra.smul_def]; rfl
    rw [e1, mul_left_comm, ← map_mul]
    have e2 : ((((-(Tw u' : ℤ)) * s : ℤ) : 𝓞 X.B.I.E) : X.B.I.E) * (((-s : ℤ) : 𝓞 X.B.I.E) : X.B.I.E) =
        ((Tw u' : ℕ) : X.B.I.E) := by
      have : (-(Tw u' : ℤ)) * s * (-s) = (Tw u' : ℤ) := by
        calc (-(Tw u' : ℤ)) * s * (-s) = (Tw u' : ℤ) * (s * s) := by ring
          _ = (Tw u' : ℤ) := by rw [hs, mul_one]
      rw [← map_mul (algebraMap (𝓞 X.B.I.E) X.B.I.E)]
      rw [← Int.cast_mul, this]; simp
    rw [e2, map_natCast, ← map_natCast (algebraMap (Fv X.B.I.F v) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E)), ← map_mul,
      inv_mul_cancel₀ ht0, map_one]

end Formalism.L2.SG.Pf.NcVal.OmVSt.OmW
end
end

section

noncomputable section

namespace Formalism.L2.SG.Pf.NcVal.OmVSt.OmW

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  NumberField IsDedekindDomain
open scoped TensorProduct

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F))

theorem sigR_alg (c : Fv F v) :
    sigR (Fv F v) σ (algebraMap (Fv F v) (Fv F v ⊗[F] E) c) = algebraMap (Fv F v) (Fv F v ⊗[F] E) c := by
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, sigR_tmul_one]

theorem hR_smul_right (c : Fv F v) (x y : Fin n → Fv F v ⊗[F] E) :
    hR (Fv F v) σ J x (c • y) = c • hR (Fv F v) σ J x y := by
  simp only [hR, Formalism.UG.hform, Pi.smul_apply, Algebra.smul_def, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hR_smul_left (c : Fv F v) (x y : Fin n → Fv F v ⊗[F] E) :
    hR (Fv F v) σ J (c • x) y = c • hR (Fv F v) σ J x y := by
  simp only [hR, Formalism.UG.hform, Pi.smul_apply, Algebra.smul_def, Finset.mul_sum, map_mul, sigR_alg]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hR_add_right (x y y' : Fin n → Fv F v ⊗[F] E) :
    hR (Fv F v) σ J x (y + y') = hR (Fv F v) σ J x y + hR (Fv F v) σ J x y' := by
  simp only [hR, Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem hR_add_left (x x' y : Fin n → Fv F v ⊗[F] E) :
    hR (Fv F v) σ J (x + x') y = hR (Fv F v) σ J x y + hR (Fv F v) σ J x' y := by
  simp only [hR, Formalism.UG.hform, Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib]

theorem hR_zero_right (x : Fin n → Fv F v ⊗[F] E) : hR (Fv F v) σ J x 0 = 0 := by
  simp [hR, Formalism.UG.hform]

theorem hR_zero_left (y : Fin n → Fv F v ⊗[F] E) : hR (Fv F v) σ J 0 y = 0 := by
  simp [hR, Formalism.UG.hform]

theorem oev_smul {c : v.adicCompletionIntegers F} {w : Fv F v ⊗[F] E} (hw : w ∈ OEv (E := E) v) :
    (c : Fv F v) • w ∈ OEv (E := E) v :=
  Submodule.smul_mem _ c hw

theorem hR_mem_of (Λ : Set (Fin n → E))
    (hL : ∀ a ∈ Λ, ∀ b ∈ Λ, ∃ o : 𝓞 E, hE σ J a b = (o : E))
    {x y : Fin n → Fv F v ⊗[F] E} (hx : x ∈ latLoc (E := E) v Λ) (hy : y ∈ latLoc (E := E) v Λ) :
    hR (Fv F v) σ J x y ∈ OEv (E := E) v := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨b, hb, rfl⟩ := hy
      obtain ⟨o, ho⟩ := hL a ha b hb
      have h' : hR (Fv F v) σ J (fun i => inclR (Fv F v) (a i)) (fun i => inclR (Fv F v) (b i)) =
          inclR (Fv F v) (hE σ J a b) := hR_ratTup (Fv F v) σ J ![a, b] 0 1
      change hR (Fv F v) σ J (fun i => inclR (Fv F v) (a i)) (fun i => inclR (Fv F v) (b i)) ∈ _
      rw [h', ho]
      exact Submodule.subset_span ⟨o, trivial, rfl⟩
    | zero => rw [hR_zero_right]; exact Submodule.zero_mem _
    | add y y' _ _ h1 h2 => rw [hR_add_right]; exact Submodule.add_mem _ h1 h2
    | smul c y _ h =>
      change hR (Fv F v) σ J _ ((c : Fv F v) • y) ∈ _
      rw [hR_smul_right]; exact oev_smul v h
  | zero => rw [hR_zero_left]; exact Submodule.zero_mem _
  | add x x' _ _ h1 h2 => rw [hR_add_left]; exact Submodule.add_mem _ h1 h2
  | smul c x _ h =>
    change hR (Fv F v) σ J ((c : Fv F v) • x) _ ∈ _
    rw [hR_smul_left]; exact oev_smul v h

end Gen

variable {D : D7} (X : HidaSetting D)

theorem hE_L (a : Fin X.B.I.n → X.B.I.E) (ha : a ∈ abelian₂ X) (b : Fin X.B.I.n → X.B.I.E) (hb : b ∈ abelian₂ X) :
    ∃ o : 𝓞 X.B.I.E, hE X.B.I.cm.sig X.B.I.J a b = (o : X.B.I.E) := by
  obtain ⟨o, ho⟩ := (X.B.I.L_dual b).1 hb a ha
  exact ⟨o, ho.symm⟩

theorem omVSD_fwd (v : PlX X) {x y : Fin X.B.I.n → Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E}
    (hx : x ∈ latLoc (E := X.B.I.E) v (abelian₂ X)) (hy : y ∈ latLoc (E := X.B.I.E) v (abelian₂ X)) :
    hR (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J x y ∈ OEv (E := X.B.I.E) v :=
  hR_mem_of X.B.I.cm.sig X.B.I.J v (abelian₂ X) (hE_L X) hx hy

def OmVSDBwd : Prop :=
  ∀ (v : PlX X) (y : Fin X.B.I.n → Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E),
    (∀ x ∈ latLoc (E := X.B.I.E) v (abelian₂ X), hR (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J x y ∈ OEv (E := X.B.I.E) v) →
      y ∈ latLoc (E := X.B.I.E) v (abelian₂ X)

theorem omVSD_of (h : OmVSDBwd X) : OmVSD X := fun v y =>
  ⟨fun hy x hx => omVSD_fwd X v hx hy, h v y⟩

end Formalism.L2.SG.Pf.NcVal.OmVSt.OmW
end
end
