module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle281
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SurjectiveReductionOntoFiniteLevelGroup
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary
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
import Formalism.LocalToGlobal.IndefiniteReal.Bundle017
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowDict
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

noncomputable section

namespace GlobalTheory.SeeConjChar

open Classical GlobalTheory.SeeConjRead

theorem cast_hA_add {I J : Formalism.MainNotions.S.AutInst} (e : I = J) (y z z' : Formalism.L2.SG.HidaSetting.VA J) :
    cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F)) e)
      (Formalism.L2.SG.HidaSetting.hA I (cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => Formalism.L2.SG.HidaSetting.VA I) e.symm) y)
        (cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => Formalism.L2.SG.HidaSetting.VA I) e.symm) (z + z'))) =
    cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F)) e)
      (Formalism.L2.SG.HidaSetting.hA I (cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => Formalism.L2.SG.HidaSetting.VA I) e.symm) y)
        (cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => Formalism.L2.SG.HidaSetting.VA I) e.symm) z)) +
    cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F)) e)
      (Formalism.L2.SG.HidaSetting.hA I (cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => Formalism.L2.SG.HidaSetting.VA I) e.symm) y)
        (cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => Formalism.L2.SG.HidaSetting.VA I) e.symm) z')) := by
  subst e
  simp only [cast_eq]
  unfold Formalism.L2.SG.HidaSetting.hA Formalism.UG.hform
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem cast_hA_smul {I J : Formalism.MainNotions.S.AutInst} (e : I = J) (c : TensorProduct J.F J.E (Formalism.MainNotions.S.Af J.F))
    (y z : Formalism.L2.SG.HidaSetting.VA J) :
    cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F)) e)
      (Formalism.L2.SG.HidaSetting.hA I (cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => Formalism.L2.SG.HidaSetting.VA I) e.symm) y)
        (cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => Formalism.L2.SG.HidaSetting.VA I) e.symm) (c • z))) =
    c * cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F)) e)
      (Formalism.L2.SG.HidaSetting.hA I (cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => Formalism.L2.SG.HidaSetting.VA I) e.symm) y)
        (cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => Formalism.L2.SG.HidaSetting.VA I) e.symm) z)) := by
  subst e
  simp only [cast_eq]
  unfold Formalism.L2.SG.HidaSetting.hA Formalism.UG.hform
  simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hT_add' {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (y z z' : Fin (Yc D 0).rank → EAf D) : hT X h y (z + z') = hT X h y z + hT X h y z' :=
  cast_hA_add h y z z'

theorem hT_smul' {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (c : EAf D) (y z : Fin (Yc D 0).rank → EAf D) : hT X h y (c • z) = c * hT X h y z :=
  cast_hA_smul h c y z

end GlobalTheory.SeeConjChar

namespace GlobalTheory.SeeConjChar
open Classical
theorem resT_of_mem' {D : D7} (PP : Pl D.host.E) (x : EAf D) (hx : x ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) :
    resT PP x = Formalism.L2.DIV.resS D.host.F PP ⟨x, hx⟩ := dif_pos hx
end GlobalTheory.SeeConjChar

namespace GlobalTheory.SeeConjChar.ResStab

open Classical Matrix

theorem mem_res_eq {R k : Type} [CommRing R] [CommRing k] {S : Subring R} (ρ : S →+* k) {x : R} (s : S)
    (hx : x = s) : ∃ hm : x ∈ S, ρ ⟨x, hm⟩ = ρ s := by
  subst hx
  exact ⟨s.2, rfl⟩

theorem res_conj_mulVec {R k : Type} [CommRing R] [CommRing k] (S : Subring R) (ρ : S →+* k) (r : R → k) (hr : ∀ x (hx : x ∈ S), r x = ρ ⟨x, hx⟩) {n : ℕ}
    (f : (Fin n → R) → R) (hadd : ∀ z z', f (z + z') = f z + f z') (hsmul : ∀ (c : R) z, f (c • z) = c * f z) (β : GL (Fin n) R) (Y : Matrix (Fin n) (Fin n) S) (w : Fin n → Fin n → R)
    (N : Matrix (Fin n) (Fin n) R)
    (hNY : N = (β : Matrix (Fin n) (Fin n) R) * Y.map S.subtype * ((β⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R))
    (hw : ∀ i j, ∃ hm : (((β⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) *ᵥ w j) i ∈ S,
      ρ ⟨_, hm⟩ = if i = j then 1 else 0)
    (hf : ∀ z, (∀ i, (((β⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) *ᵥ z) i ∈ S) → f z ∈ S) (j : Fin n) :
    ∃ hx : f (N *ᵥ w j) ∈ S,
      ρ ⟨_, hx⟩ = ∑ l, r (f (w l)) * ρ (Y l j) := by
  subst hNY
  set B : Matrix (Fin n) (Fin n) R := (β : Matrix (Fin n) (Fin n) R) with hB
  set Bi : Matrix (Fin n) (Fin n) R := ((β⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) with hBi
  have hBiB : Bi * B = 1 := by rw [hBi, hB, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hBBi : B * Bi = 1 := by rw [hBi, hB, ← Units.val_mul, mul_inv_cancel, Units.val_one]

  let b : Fin n → Fin n → R := fun m i => B i m
  have hb : ∀ m, Bi *ᵥ b m = Pi.single m 1 := by
    intro m
    have : b m = B *ᵥ Pi.single m 1 := by
      funext i
      simp [b, Matrix.mulVec_single]
    rw [this, Matrix.mulVec_mulVec, hBiB, Matrix.one_mulVec]
  have ht : ∀ m, f (b m) ∈ S := by
    intro m
    refine hf _ fun i => ?_
    rw [hb m]
    by_cases hi : i = m
    · subst hi; simp only [Pi.single_eq_same]; exact S.one_mem
    · rw [Pi.single_eq_of_ne hi]; exact S.zero_mem
  let t : Fin n → S := fun m => ⟨f (b m), ht m⟩

  have hdec : ∀ z, f z = ∑ m, (Bi *ᵥ z) m * f (b m) := by
    intro z
    have hz : z = ∑ m, (Bi *ᵥ z) m • b m := by
      funext i
      have := congrFun (show B *ᵥ (Bi *ᵥ z) = z by rw [Matrix.mulVec_mulVec, hBBi, Matrix.one_mulVec]) i
      rw [← this, Finset.sum_apply]
      simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, b]
      exact Finset.sum_congr rfl fun m _ => mul_comm _ _
    let fl : (Fin n → R) →ₗ[R] R := ⟨⟨f, hadd⟩, hsmul⟩
    show fl z = _
    conv_lhs => rw [hz]

    rw [map_sum]
    simp only [map_smul, smul_eq_mul]
    rfl
  have hval : ∀ z (v : Fin n → S), (∀ m, (Bi *ᵥ z) m = v m) → f z = ((∑ m, v m * t m : S) : R) := by
    intro z v hv
    rw [hdec z]
    push_cast
    exact Finset.sum_congr rfl fun m _ => by rw [hv m]

  let c : Fin n → Fin n → S := fun l i => ⟨(Bi *ᵥ w l) i, (hw i l).1⟩
  have hc : ∀ l i, ρ (c l i) = if i = l then 1 else 0 := fun l i => (hw i l).2

  have hwl : ∀ l, r (f (w l)) = ρ (t l) := by
    intro l
    obtain ⟨hm, e⟩ := mem_res_eq ρ _ (hval (w l) (c l) fun m => rfl)

    rw [hr _ hm, e, map_sum]
    simp only [map_mul, hc]
    simp

  have hN : ∀ m, (Bi *ᵥ ((B * Y.map S.subtype * Bi) *ᵥ w j)) m = ((∑ i, Y m i * c j i : S) : R) := by
    intro m
    rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hBiB, Matrix.one_mul, ← Matrix.mulVec_mulVec]
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Subring.coe_subtype, c]
    push_cast
    rfl
  obtain ⟨hm, e⟩ := mem_res_eq ρ _ (hval _ (fun m => ∑ i, Y m i * c j i) hN)
  refine ⟨hm, ?_⟩
  rw [e]

  simp only [hwl, map_sum, map_mul, hc]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  exact Finset.sum_congr rfl fun l _ => mul_comm _ _

end GlobalTheory.SeeConjChar.ResStab

namespace GlobalTheory.SeeConjChar

open Classical GlobalTheory.SeeConjRead

theorem resT_hT_mulVec_stab : ∀ {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (β : GL (Fin (Yc D 0).rank) (EAf D)) (PP : Pl D.host.E) (w : Fin (Yc D 0).rank → Fin (Yc D 0).rank → EAf D), RedIs β PP w → ∀ N ∈ St β, ∀ y : Fin (Yc D 0).rank → EAf D, (∀ z : Fin (Yc D 0).rank → EAf D, (∀ i, Matrix.mulVec (β⁻¹).val z i ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) → GlobalTheory.SeeConjChar.hT X h y z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) → ∀ j, GlobalTheory.SeeConjChar.hT X h y (Matrix.mulVec N.val (w j)) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ∧ GlobalTheory.SeeConjChar.resT PP (GlobalTheory.SeeConjChar.hT X h y (Matrix.mulVec N.val (w j))) = ∑ l, GlobalTheory.SeeConjChar.resT PP (GlobalTheory.SeeConjChar.hT X h y (w l)) * (redFn β PP N).val l j := by
  intro D X h β PP w hw N hN y hy j
  obtain ⟨Y, rfl⟩ := hN
  have hval : (Formalism.L2.DIV.frGL β Y).val =
      β.val * Y.val.map (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype * (β⁻¹).val := by
    simp only [Formalism.L2.DIV.frGL, Formalism.L2.DIV.intGL, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Units.val_mul]
    rfl
  have hred : ∀ l, ((Formalism.L2.DIV.redFn β PP (Formalism.L2.DIV.frGL β Y)).val l j) =
      Formalism.L2.DIV.resS D.host.F PP (Y.val l j) := by
    intro l
    rw [Formalism.L2.DIV.redFn_frGL]
    rfl
  obtain ⟨hm, e⟩ := ResStab.res_conj_mulVec (Formalism.L2.Herm.intAf D.host.F D.host.E) (Formalism.L2.DIV.resS D.host.F PP) (resT PP) (resT_of_mem' PP)
    (hT X h y) (hT_add' X h y) (fun c z => hT_smul' X h c y z) β Y.val w _ hval hw hy j
  refine ⟨hm, ?_⟩
  exact (resT_of_mem' PP _ hm).trans (e.trans (Finset.sum_congr rfl fun l _ =>
    congrArg (fun t => resT PP (hT X h y (w l)) * t) (hred l).symm))

end GlobalTheory.SeeConjChar
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

noncomputable section

namespace GlobalTheory.SeeConjComb

open Classical

theorem sum_eq_of_inj {α β M : Type} [Fintype α] [Fintype β] [AddCommMonoid M] (F : α → M) (G : β → M)
    (φ : α → β) (hφ : Function.Injective φ) (hval : ∀ x, F x = G (φ x)) (hs : ∀ b, G b ≠ 0 → ∃ x, φ x = b) :
    ∑ x, F x = ∑ b, G b :=
  Finset.sum_bij_ne_zero (fun x _ _ => φ x) (fun _ _ _ => Finset.mem_univ _) (fun _ _ _ _ _ _ h => hφ h)
    (fun b _ hb => by
      obtain ⟨x, rfl⟩ := hs b hb
      exact ⟨x, Finset.mem_univ _, by rw [hval]; exact hb, rfl⟩)
    (fun x _ _ => hval x)

theorem conj_residue_reindex : ∀ {κ : Type} [CommRing κ] {n r : ℕ} (hr : r ≤ n) (ρ k : ℕ), n = 2 * ρ + k + 1 → r = n → ∀ U : GL (Fin n) κ, upperLeftBlock hr U ∈ unip κ r → ∀ (s : Bool) (fF fN : Fin ρ → Fin n) (gB : Fin k → Fin n), (∀ a, (fF a).1 = 2 * ρ + k - a.1) → (∀ a, (fN a).1 = if a.1 + 1 < ρ then 2 * ρ + k - (a.1 + 1) else ρ + k) → (∀ i, (gB i).1 = ρ + k - 1 - i.1) → (∑ a, (sgnD ρ k (fN a) : κ) * (U⁻¹).val (fN a) (fF a)) + (∑ i : Fin k, if hi : i.1 + 1 < k then (if s then 0 else (sgnD ρ k (gB ⟨i.1 + 1, hi⟩) : κ) * (U⁻¹).val (gB ⟨i.1 + 1, hi⟩) (gB i)) else 0) = ∑ i : Fin r, ∑ j : Fin r, if symEdge ρ k i j then ((GlobalTheory.SeeConjChar.wB ρ k s i j : ℤ) : κ) * (upperLeftBlock hr U).val i j else 0 := by
  intro κ _ n r hr ρ k hn hrn U hU s fF fN gB hfF hfN hgB
  subst hrn
  have hm : U ∈ blockTri (κ := κ) (blk2 r) := fun i j h => absurd h (by simp [blk2, i.2, j.2])
  have hR : upperLeftBlock hr U = U := Units.ext (Matrix.ext fun i j => by rw [upper_block_val_submatrix hr hm]; rfl)
  rw [hR] at hU ⊢
  have hUi : U⁻¹ ∈ unip κ r := inv_mem hU
  have hinv : ∀ p q : Fin r, q.1 = p.1 + 1 → (U⁻¹).val p q = - U.val p q := by
    intro p q hpq
    have hlt : p < q := by rw [Fin.lt_def]; omega
    have h := unip_mul_entry hUi hU hlt (fun l h1 h2 => by
      rw [Fin.lt_def] at h1 h2; omega)
    rw [inv_mul_cancel, Units.val_one, Matrix.one_apply_ne (ne_of_lt hlt)] at h
    exact eq_neg_of_add_eq_zero_left h.symm
  obtain ⟨φ, hφl, hφr⟩ : ∃ φ : Fin ρ ⊕ Fin k → Fin r × Fin r, (∀ a, φ (Sum.inl a) = (fN a, fF a)) ∧
      (∀ i, φ (Sum.inr i) = (⟨ρ + k - 2 - i.1, by omega⟩, gB i)) := ⟨Sum.elim _ _, fun _ => rfl, fun _ => rfl⟩
  refine Eq.trans (Fintype.sum_sum_type (Sum.elim _ _)).symm ?_
  rw [← Fintype.sum_prod_type']
  refine sum_eq_of_inj _ _ φ ?_ ?_ ?_
  · rintro (a|i) (b|j) h
    · rw [hφl, hφl, Prod.mk.injEq] at h
      have h1 := hfF a; have h2 := hfF b; have h3 := congrArg Fin.val h.2
      exact congrArg Sum.inl (Fin.ext (by have := a.2; have := b.2; omega))
    · rw [hφl, hφr, Prod.mk.injEq] at h
      have h1 := hfF a; have h2 := hgB j; have h3 := congrArg Fin.val h.2
      exfalso; have := a.2; have := j.2; omega
    · rw [hφr, hφl, Prod.mk.injEq] at h
      have h1 := hfF b; have h2 := hgB i; have h3 := congrArg Fin.val h.2
      exfalso; have := b.2; have := i.2; omega
    · rw [hφr, hφr, Prod.mk.injEq] at h
      have h1 := hgB i; have h2 := hgB j; have h3 := congrArg Fin.val h.2
      exact congrArg Sum.inr (Fin.ext (by have := i.2; have := j.2; omega))
  · rintro (a|i)
    · rw [hφl]
      simp only [Sum.elim_inl]
      have h1 := hfF a; have h2 := hfN a; have ha := a.2
      by_cases hc : a.1 + 1 < ρ
      · rw [if_pos hc] at h2
        have hq : (fF a).1 = (fN a).1 + 1 := by omega
        have hs : symEdge ρ k (fN a) (fF a) := Or.inl ⟨hq, by omega, by omega⟩
        have hw : GlobalTheory.SeeConjChar.wB ρ k s (fN a) (fF a) = -1 := by
          unfold GlobalTheory.SeeConjChar.wB; split_ifs <;> omega
        have hd : (sgnD ρ k (fN a) : κ) = 1 := by unfold sgnD; rw [if_neg (by omega)]
        rw [if_pos hs, hw, hd, hinv _ _ hq]; push_cast; ring
      · rw [if_neg hc] at h2
        have hq : (fF a).1 = (fN a).1 + 1 := by omega
        have hs : symEdge ρ k (fN a) (fF a) := Or.inl ⟨hq, by omega, by omega⟩
        have hw : GlobalTheory.SeeConjChar.wB ρ k s (fN a) (fF a) = 1 := by
          unfold GlobalTheory.SeeConjChar.wB; split_ifs <;> omega
        have hd : (sgnD ρ k (fN a) : κ) = -1 := by unfold sgnD; rw [if_pos h2]
        rw [if_pos hs, hw, hd, hinv _ _ hq]; push_cast; ring
    · rw [hφr]
      show (if hi : i.1 + 1 < k then (if s then 0 else (sgnD ρ k (gB ⟨i.1 + 1, hi⟩) : κ) * (U⁻¹).val (gB ⟨i.1 + 1, hi⟩) (gB i)) else 0) = _
      have h1 := hgB i; have hi2 := i.2
      by_cases hi : i.1 + 1 < k
      · rw [dite_eq_left hi]
        have h3 := hgB ⟨i.1 + 1, hi⟩
        dsimp only at h3
        have hg : gB ⟨i.1 + 1, hi⟩ = ⟨ρ + k - 2 - i.1, by omega⟩ := Fin.ext (by dsimp only; omega)
        have hq : (gB i).1 = (⟨ρ + k - 2 - i.1, by omega⟩ : Fin r).1 + 1 := by dsimp only; omega
        have hs : symEdge ρ k (⟨ρ + k - 2 - i.1, by omega⟩ : Fin r) (gB i) := Or.inl ⟨hq, by dsimp only; omega, by dsimp only; omega⟩
        have hd : (sgnD ρ k (⟨ρ + k - 2 - i.1, by omega⟩ : Fin r) : κ) = 1 := by
          unfold sgnD; rw [if_neg (by dsimp only; omega)]
        rw [hg, if_pos hs, hd, hinv _ _ hq]
        cases s
        · have hw : GlobalTheory.SeeConjChar.wB ρ k false (⟨ρ + k - 2 - i.1, by omega⟩ : Fin r) (gB i) = -1 := by
            unfold GlobalTheory.SeeConjChar.wB
            rw [if_neg (show ¬ ((⟨ρ + k - 2 - i.1, by omega⟩ : Fin r).1 < ρ) by dsimp only; omega), if_pos (show (⟨ρ + k - 2 - i.1, by omega⟩ : Fin r).1 + 1 < ρ + k by dsimp only; omega)]; rfl
          rw [hw]; simp
        · have hw : GlobalTheory.SeeConjChar.wB ρ k true (⟨ρ + k - 2 - i.1, by omega⟩ : Fin r) (gB i) = 0 := by
            unfold GlobalTheory.SeeConjChar.wB
            rw [if_neg (show ¬ ((⟨ρ + k - 2 - i.1, by omega⟩ : Fin r).1 < ρ) by dsimp only; omega), if_pos (show (⟨ρ + k - 2 - i.1, by omega⟩ : Fin r).1 + 1 < ρ + k by dsimp only; omega)]; rfl
          rw [hw]; simp
      · rw [dite_eq_right hi, if_neg]
        rintro (⟨h4, h5, h6⟩ | ⟨h4, h5⟩) <;> dsimp only at h4 h5 <;> omega
  · rintro ⟨p, q⟩ hne
    dsimp only at hne
    by_cases hs : symEdge ρ k p q
    swap
    · exact absurd (if_neg hs) hne
    rw [if_pos hs] at hne
    have hw : GlobalTheory.SeeConjChar.wB ρ k s p q ≠ 0 := fun h => hne (by rw [h]; simp)
    unfold GlobalTheory.SeeConjChar.wB at hw
    have hp2 := p.2; have hq2 := q.2
    rcases hs with ⟨hq, hp1, hp3⟩ | ⟨hp, hq⟩
    · by_cases h1 : p.1 < ρ
      · simp [h1] at hw
      by_cases h2 : p.1 + 1 < ρ + k
      · refine ⟨Sum.inr ⟨ρ + k - 2 - p.1, by omega⟩, ?_⟩
        rw [hφr, Prod.mk.injEq]
        have h3 := hgB ⟨ρ + k - 2 - p.1, by omega⟩
        dsimp only at h3
        exact ⟨Fin.ext (by dsimp only; omega), Fin.ext (by omega)⟩
      by_cases h3 : p.1 = ρ + k
      · refine ⟨Sum.inl ⟨ρ - 1, by omega⟩, ?_⟩
        rw [hφl, Prod.mk.injEq]
        have h4 := hfN ⟨ρ - 1, by omega⟩; have h5 := hfF ⟨ρ - 1, by omega⟩
        dsimp only at h4 h5
        rw [if_neg (by omega)] at h4
        exact ⟨Fin.ext (by omega), Fin.ext (by omega)⟩
      · refine ⟨Sum.inl ⟨2 * ρ + k - 1 - p.1, by omega⟩, ?_⟩
        rw [hφl, Prod.mk.injEq]
        have h4 := hfN ⟨2 * ρ + k - 1 - p.1, by omega⟩; have h5 := hfF ⟨2 * ρ + k - 1 - p.1, by omega⟩
        dsimp only at h4 h5
        rw [if_pos (by omega)] at h4
        exact ⟨Fin.ext (by omega), Fin.ext (by omega)⟩
    · simp [show p.1 < ρ by omega] at hw

end GlobalTheory.SeeConjComb
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead
open GlobalTheory.SeeConjGroup Formalism.L2.SG.HidaSetting
open scoped Matrix

noncomputable section
namespace GlobalTheory.SeeConjGroup

section RedLemmas
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem redV_eq_of_int (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (PP : Pl E) (v : Fin n → E ⊗[F] Formalism.L2.Herm.Af F)
    (h : ∀ i, ((β⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)).mulVec v i ∈
      Formalism.L2.Herm.intAf F E) (i : Fin n) :
    redV β PP v i = resS F PP ⟨_, h i⟩ := by
  unfold redV
  rw [dite_eq_left (h i)]

end RedLemmas

theorem redV_add_smul_stab : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ} (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (Λ : Submodule (𝓞 E) (Fin n → E)), IsFrame β Λ → ∀ PP : Pl E, (∀ v ∈ Formalism.L2.Herm.hatL (F := F) Λ, ∀ w ∈ Formalism.L2.Herm.hatL (F := F) Λ, redV β PP (v + w) = redV β PP v + redV β PP w) ∧ (∀ (c : Formalism.L2.Herm.intAf F E), ∀ v ∈ Formalism.L2.Herm.hatL (F := F) Λ, redV β PP ((c : E ⊗[F] Formalism.L2.Herm.Af F) • v) = resS F PP c • redV β PP v) ∧ (∀ M ∈ St β, ∀ v ∈ Formalism.L2.Herm.hatL (F := F) Λ, redV β PP ((M : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *ᵥ v) = ((redFn β PP M : GL (Fin n) (kP PP)) : Matrix (Fin n) (Fin n) (kP PP)) *ᵥ redV β PP v) := by
  intro F E _ _ _ _ _ n β Λ hF PP
  have hint : ∀ v ∈ Formalism.L2.Herm.hatL (F := F) Λ, ∀ i,
      ((β⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)).mulVec v i ∈
        Formalism.L2.Herm.intAf F E := fun v hv => (hF v).1 hv
  refine ⟨?_, ?_, ?_⟩
  · intro v hv w hw
    have hs : ∀ i, ((β⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)).mulVec (v + w) i ∈
        Formalism.L2.Herm.intAf F E := by
      intro i
      rw [Matrix.mulVec_add]
      exact Subring.add_mem _ (hint v hv i) (hint w hw i)
    funext i
    rw [Pi.add_apply, redV_eq_of_int β PP _ hs, redV_eq_of_int β PP _ (hint v hv), redV_eq_of_int β PP _ (hint w hw),
      ← map_add]
    congr 1
    apply Subtype.ext
    simp [Matrix.mulVec_add]
  · intro c v hv
    have hs : ∀ i, ((β⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)).mulVec
        ((c : E ⊗[F] Formalism.L2.Herm.Af F) • v) i ∈ Formalism.L2.Herm.intAf F E := by
      intro i
      rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
      exact Subring.mul_mem _ c.2 (hint v hv i)
    funext i
    rw [Pi.smul_apply, smul_eq_mul, redV_eq_of_int β PP _ hs, redV_eq_of_int β PP _ (hint v hv), ← map_mul]
    congr 1
    apply Subtype.ext
    simp [Matrix.mulVec_smul]
  · rintro M ⟨y, rfl⟩ v hv
    set X : Fin n → Formalism.L2.Herm.intAf F E := fun j => ⟨_, hint v hv j⟩ with hX
    have hM : ((frGL β y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) =
        (β : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) * ((intGL F E n y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *
          ((β⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) := by
      simp [frGL, MulAut.conj_apply]
    have hkey : ∀ i, ((β⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)).mulVec
        (((frGL β y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *ᵥ v) i =
        ((((y : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)) *ᵥ X) i : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) := by
      intro i
      rw [hM, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel,
        Units.val_one, Matrix.one_mul, ← Matrix.mulVec_mulVec]
      simp only [Matrix.mulVec, dotProduct, hX]
      rw [AddSubmonoidClass.coe_finsetSum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rfl
    have hs : ∀ i, ((β⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)).mulVec
        (((frGL β y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *ᵥ v) i ∈
          Formalism.L2.Herm.intAf F E := fun i => by rw [hkey i]; exact Subtype.property _
    funext i
    rw [redV_eq_of_int β PP _ hs, redFn_frGL]
    have e1 : (⟨_, hs i⟩ : Formalism.L2.Herm.intAf F E) = ((y : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)) *ᵥ X) i :=
      Subtype.ext (hkey i)
    rw [e1]

    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [redV_eq_of_int β PP _ (hint v hv) j]
    rfl

end GlobalTheory.SeeConjGroup
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

namespace GlobalTheory.SeeConjChar

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.Pf

theorem cpt_cP_eq_zero_of_orth {D : D7} {PP : Pl D.host.E} {e : EAf D} (ho : e * GlobalTheory.StdFrames.sg D e = 0)
    (h1 : GlobalTheory.StdFrames.cpt PP e = 1) : GlobalTheory.StdFrames.cpt (GlobalTheory.IdemSupport.cP PP) e = 0 := by
  have h2 := GlobalTheory.StdFrames.cpt_sg_eq_zero (Q := GlobalTheory.IdemSupport.cP PP) (z := 1 - e)
    (by rw [GlobalTheory.StdFrames.cP_cP, RingHom.map_sub, h1, RingHom.map_one, sub_self])
  rw [RingHom.map_sub, RingHom.map_one, RingHom.map_sub, RingHom.map_one, sub_eq_zero] at h2
  have h3 := congrArg (GlobalTheory.StdFrames.cpt (GlobalTheory.IdemSupport.cP PP)) ho
  rwa [RingHom.map_mul, ← h2, mul_one, RingHom.map_zero] at h3

theorem resT_eq_zero_of_fixed {D : D7} {Q : Pl D.host.E} {e x : EAf D} (hx : x ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    (he : GlobalTheory.StdFrames.cpt Q e = 0) (hf : x = e * x) : resT Q x = 0 := by
  unfold resT
  rw [dite_eq_left hx]
  refine (GlobalTheory.AdIsom.resS_eq_zero_iff_cpt Q ⟨x, hx⟩).2 ?_
  have h0 : GlobalTheory.StdFrames.cpt Q x = 0 := by rw [hf, RingHom.map_mul, he, zero_mul]
  show Valued.v (GlobalTheory.StdFrames.cpt Q x) < 1
  rw [h0, Valuation.map_zero]
  exact zero_lt_one

theorem resT_cP_hT_bwd_eq_zero : ∀ {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (β : GL (Fin (Yc D 0).rank) (EAf D)), IsFrame β (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) → ∀ PP : Pl D.host.E, GlobalTheory.SeeConjChar.sideAt X h PP = true → ∀ M ∈ St β, ∀ i j : Fin D.R.k, GlobalTheory.SeeConjChar.hT X h (bwdT X h i) (Matrix.mulVec M.val (bwT X h j)) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ∧ GlobalTheory.SeeConjChar.resT (GlobalTheory.IdemSupport.cP PP) (GlobalTheory.SeeConjChar.hT X h (bwdT X h i) (Matrix.mulVec M.val (bwT X h j))) = 0 := by
  intro D X h β hF PP hs M hM i j
  have hb := X.vectorsInLattice.2.2
  have ho := X.ew_orth
  have hw := X.bwd_w i
  have h1 : GlobalTheory.StdFrames.cpt PP (ewT X h) = 1 := by
    unfold sideAt at hs
    simpa only [decide_eq_true_eq] using hs
  have hfix : ∀ v, hA X.B.I (X.bwd i) v = X.ew * hA X.B.I (X.bwd i) v := fun v => by
    conv_lhs => rw [hw, unitaryCongruence.hA_smul_left, unitaryCongruence.sigA_sigA]
  obtain ⟨⟨I⟩⟩ := X
  dsimp only at h hb ho hfix
  subst h
  have hv := (hb j).1
  rw [GlobalTheory.SeeMatchOnto.Lf_eq] at hv
  have hv2 := (GlobalTheory.SeeMatchOnto.mem_hatL_iff_of_St hF hM _).1 hv
  have hv3 := (GlobalTheory.SeeMatchOnto.Lf_eq (D := D)).ge hv2
  have hint := unitaryCongruence.hA_int _ (hb i).2 hv3
  exact ⟨hint, resT_eq_zero_of_fixed hint (cpt_cP_eq_zero_of_orth ho h1) (hfix _)⟩

end GlobalTheory.SeeConjChar
end
