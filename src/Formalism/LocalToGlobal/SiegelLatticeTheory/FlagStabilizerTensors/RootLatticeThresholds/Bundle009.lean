module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RescaleCore
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.MassDataInst
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.SharpRestriction.CuspSpanNormBounds.SpanMemOfImage
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle014
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open MeasureTheory NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Matrix

namespace Formalism.L2.SG.Pf.Rescale

section Gram

variable {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

theorem hE_swap (hσ : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J) (x y : Fin n → E) :
    hE σ J y x = σ (hE σ J x y) := by

  simp only [hE, Formalism.UG.hform, AlgHom.coe_toRingHom, map_sum, map_mul, hσ]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [hJ.1]
  ring

theorem standard_gram_nondegenerate : Formalism.L2.SG.Pf.RescaleCore.GramStdND := by
  intro F E _ _ _ σ n J r P T hσ hJ hS
  obtain ⟨hee, hff, hef, hez, hfz, hzz, hT⟩ := hS
  intro hdet
  obtain ⟨v, hv0, hv⟩ := (Matrix.exists_mulVec_eq_zero_iff).2 hdet

  have tE : ∀ a : Fin r, tupH P (Fin.castAdd r (Fin.castSucc a)) = P.e a := by
    intro a; simp [tupH, F0, Fin.append_left, Fin.snoc_castSucc]
  have tZ : tupH P (Fin.castAdd r (Fin.last r)) = P.z := by
    simp [tupH, F0, Fin.append_left, Fin.snoc_last]
  have tF : ∀ a : Fin r, tupH P (Fin.natAdd (r + 1) a) = P.f a := by
    intro a; simp [tupH, Fin.append_right]
  have hsum : ∀ i, (gramE σ J (tupH P) *ᵥ v) i =
      (∑ b : Fin r, hE σ J (tupH P i) (P.e b) * v (Fin.castAdd r (Fin.castSucc b))) +
        hE σ J (tupH P i) P.z * v (Fin.castAdd r (Fin.last r)) +
        ∑ b : Fin r, hE σ J (tupH P i) (P.f b) * v (Fin.natAdd (r + 1) b) := by
    intro i
    simp only [Matrix.mulVec, dotProduct, gramE]
    rw [Fin.sum_univ_add, Fin.sum_univ_castSucc]
    simp only [tE, tZ, tF]
  have hrow : ∀ i, (gramE σ J (tupH P) *ᵥ v) i = 0 := fun i => congrFun hv i
  have vF : ∀ a : Fin r, v (Fin.natAdd (r + 1) a) = 0 := by
    intro a
    have h := hrow (Fin.castAdd r (Fin.castSucc a))
    rw [hsum, tE] at h
    simp only [hee, zero_mul, Finset.sum_const_zero, zero_add, hez, hef, ite_mul, one_mul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true] at h
    exact h
  have hze : ∀ b, hE σ J P.z (P.e b) = 0 := fun b => by rw [hE_swap σ J hσ hJ, hez, map_zero]
  have hzf : ∀ b, hE σ J P.z (P.f b) = 0 := fun b => by rw [hE_swap σ J hσ hJ, hfz, map_zero]
  have hfe : ∀ a b, hE σ J (P.f a) (P.e b) = if b = a then 1 else 0 := fun a b => by
    rw [hE_swap σ J hσ hJ, hef]; split_ifs <;> simp
  have hfz' : ∀ a, hE σ J (P.f a) P.z = 0 := hfz
  have vZ : v (Fin.castAdd r (Fin.last r)) = 0 := by
    have h := hrow (Fin.castAdd r (Fin.last r))
    rw [hsum, tZ] at h
    simp only [hze, hzf, zero_mul, Finset.sum_const_zero, zero_add, add_zero] at h
    have hne : hE σ J P.z P.z ≠ 0 := by
      rw [hzz]
      intro h0
      exact hT (neg_eq_zero.1 ((algebraMap F E).injective (by rw [h0, map_zero])))
    exact (mul_eq_zero.1 h).resolve_left hne
  have vE : ∀ a : Fin r, v (Fin.castAdd r (Fin.castSucc a)) = 0 := by
    intro a
    have h := hrow (Fin.natAdd (r + 1) a)
    rw [hsum, tF] at h
    simp only [hfe, hfz', hff, zero_mul, Finset.sum_const_zero, add_zero, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
    exact h
  apply hv0
  funext i
  refine Fin.addCases (fun j => ?_) (fun a => ?_) i
  · refine Fin.lastCases ?_ (fun a => ?_) j
    · exact vZ
    · exact vE a
  · exact vF a

end Gram

end Formalism.L2.SG.Pf.Rescale

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub

namespace Formalism.L2.SG.Pf.Rescale

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem hform_crdX (X : HidaSetting D) (v w : (VS D).V) :
    X.ιE (Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J (crdOf X.B.I X.ιE X.bas v) (crdOf X.B.I X.ιE X.bas w)) =
      (VS D).hT v w := by
  conv_rhs => rw [← X.bas.sum_repr v, ← X.bas.sum_repr w]

  simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
  Formalism.UG.hform, map_mul, crdOf, starRingEnd_apply, X.ιE_conj, RingEquiv.apply_symm_apply,
  X.J_eq, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [← Formalism.BasicNotions.bridge_star_holds D.R D.host, RingHom.id_apply]
  ring

theorem hE_crdX (X : HidaSetting D) (v w : (VS D).V) :
    hE X.B.I.cm.sig X.B.I.J (crdOf X.B.I X.ιE X.bas v) (crdOf X.B.I X.ιE X.bas w) = X.ιE.symm ((VS D).hT v w) := by
  show Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J _ _ = _
  rw [← hform_crdX X v w, RingEquiv.symm_apply_apply]

theorem frame_stdX (X : HidaSetting D) (u : D.what₂.Word) :
    (Formalism.L2.SG.TypedSets.frameOf X u).IsStd X.B.I.cm.sig X.B.I.J (((D.mem u).A.T : ℕ) : X.B.I.F) := by
  refine ⟨fun a b => ?_, fun a b => ?_, fun a b => ?_, fun a => ?_, fun a => ?_, ?_, ?_⟩
  · show hE _ _ (crdOf X.B.I X.ιE X.bas (X.eX a)) (crdOf X.B.I X.ιE X.bas (X.eX b)) = 0
    rw [hE_crdX, X.ee, map_zero]
  · show hE _ _ (crdOf X.B.I X.ιE X.bas (X.fY a)) (crdOf X.B.I X.ιE X.bas (X.fY b)) = 0
    rw [hE_crdX, X.ff, map_zero]
  · show hE _ _ (crdOf X.B.I X.ιE X.bas (X.eX a)) (crdOf X.B.I X.ιE X.bas (X.fY b)) = _
    rw [hE_crdX, X.ef]
    split_ifs <;> simp
  · show hE _ _ (crdOf X.B.I X.ιE X.bas (X.eX a)) (crdOf X.B.I X.ιE X.bas (X.zu u)) = 0
    rw [hE_crdX, (X.zu_orth u a).1, map_zero]
  · show hE _ _ (crdOf X.B.I X.ιE X.bas (X.fY a)) (crdOf X.B.I X.ιE X.bas (X.zu u)) = 0
    rw [hE_crdX, (X.zu_orth u a).2, map_zero]
  · show hE _ _ (crdOf X.B.I X.ιE X.bas (X.zu u)) (crdOf X.B.I X.ιE X.bas (X.zu u)) = _
    rw [hE_crdX, X.zu_norm]
    simp
  · exact Nat.cast_ne_zero.2 (D.mem u).A.T_prime.ne_zero


end Formalism.L2.SG.Pf.Rescale
end
end

section

noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.MainNotions.FrameBoundFromBesselTorus

namespace Formalism.L2.SG.Pf.Carrier.CarPinTor

variable {k r : ℕ} {κ τ : ℝ}

theorem phiP_stabAct (hκ : 0 < κ) (hτ : 0 < τ) (g a : Mx k r) (x : PairSp k r) :
    phiP k r κ τ (stabAct g a x) = stabAct (cj k r κ τ g) (cj k r κ τ a) (phiP k r κ τ x) := by
  obtain ⟨⟨x1, x2⟩, ⟨x3, x4⟩⟩ := x
  refine Prod.ext (Prod.ext rfl ?_) (Prod.ext rfl ?_)
  · show (fun i j => cj k r κ τ (a * Matrix.of x2) i j) =
      fun i j => (cj k r κ τ a * Matrix.of (cjT k r κ τ x2)) i j
    rw [cj_mul hκ hτ]
    rfl
  · show (fun i j => cj k r κ τ (g⁻¹ * a * g * Matrix.of x4) i j) =
      fun i j => ((cj k r κ τ g)⁻¹ * cj k r κ τ a * cj k r κ τ g * Matrix.of (cjT k r κ τ x4)) i j
    rw [cj_mul hκ hτ, cj_mul hκ hτ, cj_mul hκ hτ, cj_inv hκ hτ]
    rfl

theorem isOrbQuot_trD (hκ : 0 < κ) (hτ : 0 < τ) (L : LocBessel k r)
    (hz : inWb k r ((τ : ℂ) • L.z) ∧ 0 < Tz k r ((τ : ℂ) • L.z))
    (hz' : inWb k r ((τ : ℂ) • L.z') ∧ 0 < Tz k r ((τ : ℂ) • L.z'))
    (hπ : IsHCTypeW k r ((τ : ℂ) • L.z) L.u (fun x => L.π (cjI k r κ τ x)))
    (hπ' : IsHCTypeW k r ((τ : ℂ) • L.z') L.u' (fun x => L.π' (cjI k r κ τ x)))
    (hμW : IsHaarOn (UWset k r ((τ : ℂ) • L.z)) (L.μW.map (cjT k r κ τ)) ∧ L.μW.map (cjT k r κ τ) Set.univ = 1)
    (hμW' : IsHaarOn (UWset k r ((τ : ℂ) • L.z')) (L.μW'.map (cjT k r κ τ)) ∧
      L.μW'.map (cjT k r κ τ) Set.univ = 1)
    {g : Mx k r} {μR : Measure (Mt k r)} {ν : Measure (PairSp k r)} (h : IsOrbQuot L g μR ν) :
    IsOrbQuot (trD L κ τ (L.κN * ENNReal.ofReal (deltaN k r κ τ)) hz hz' hπ hπ' hμW hμW') (cj k r κ τ g)
      (μR.map (cjT k r κ τ)) (ν.map (phiP k r κ τ)) := by
  intro f hf
  rw [pairMeas_trD hκ hτ]
  have exp_product_square_inv : (pairMeas L).map (phiP k r κ τ) = (pairMeas L).map (phiE (k := k) (r := r) hκ hτ) := rfl
  rw [exp_product_square_inv, lintegral_map_equiv]
  rw [h (fun x => f (phiE hκ hτ x)) (hf.comp (phiE hκ hτ).measurable)]
  have eP : ν.map (phiP k r κ τ) = ν.map (phiE (k := k) (r := r) hκ hτ) := rfl
  rw [eP, lintegral_map_equiv]
  refine lintegral_congr (fun x => ?_)
  have eT : μR.map (cjT k r κ τ) = μR.map (cjE (k := k) (r := r) hκ hτ) := rfl
  rw [eT, lintegral_map_equiv]
  refine lintegral_congr (fun a => ?_)
  show f (phiP k r κ τ (stabAct g (Matrix.of a) x)) =
    f (stabAct (cj k r κ τ g) (Matrix.of (cjT k r κ τ a)) (phiP k r κ τ x))
  rw [phiP_stabAct hκ hτ]
  rfl

theorem isRelStab_trD (hκ : 0 < κ) (hτ : 0 < τ) (L : LocBessel k r) (κN₁ : ENNReal)
    (hz : inWb k r ((τ : ℂ) • L.z) ∧ 0 < Tz k r ((τ : ℂ) • L.z))
    (hz' : inWb k r ((τ : ℂ) • L.z') ∧ 0 < Tz k r ((τ : ℂ) • L.z'))
    (hπ : IsHCTypeW k r ((τ : ℂ) • L.z) L.u (fun x => L.π (cjI k r κ τ x)))
    (hπ' : IsHCTypeW k r ((τ : ℂ) • L.z') L.u' (fun x => L.π' (cjI k r κ τ x)))
    (hμW : IsHaarOn (UWset k r ((τ : ℂ) • L.z)) (L.μW.map (cjT k r κ τ)) ∧ L.μW.map (cjT k r κ τ) Set.univ = 1)
    (hμW' : IsHaarOn (UWset k r ((τ : ℂ) • L.z')) (L.μW'.map (cjT k r κ τ)) ∧
      L.μW'.map (cjT k r κ τ) Set.univ = 1)
    {g : Mx k r} (h : IsRelStab L g) :
    IsRelStab (trD L κ τ κN₁ hz hz' hπ hπ' hμW hμW') (cj k r κ τ g) := by
  intro a ha
  obtain ⟨b, rfl⟩ : ∃ b, a = cj k r κ τ b := ⟨cjI k r κ τ a, (cj_cjI hκ hτ a).symm⟩
  have hb : b ∈ RStab k r g := (cj_mem_RStab_iff hκ hτ g b).1 ha
  have e : (cj k r κ τ g)⁻¹ * cj k r κ τ b * cj k r κ τ g = cj k r κ τ (g⁻¹ * b * g) := by
    rw [cj_mul hκ hτ, cj_mul hκ hτ, cj_inv hκ hτ]
  show psi k r ((τ : ℂ) • L.z) ((κ : ℂ) * L.c) (cj k r κ τ b) =
    psi k r ((τ : ℂ) • L.z') ((κ : ℂ) * L.c) ((cj k r κ τ g)⁻¹ * cj k r κ τ b * cj k r κ τ g)
  rw [e, psi_cj hκ hτ L.hz.1, psi_cj hκ hτ L.hz'.1]
  exact h b hb

theorem isOrbQuot_smul {L L' : LocBessel k r} {g : Mx k r} {μR : Measure (Mt k r)} {ν : Measure (PairSp k r)}
    (h : IsOrbQuot L g μR ν) (t : ENNReal) (hP : pairMeas L' = t • pairMeas L) : IsOrbQuot L' g μR (t • ν) := by
  intro f hf
  rw [hP, lintegral_smul_measure, lintegral_smul_measure, h f hf]

theorem pairMeas_scaleN {L L' : LocBessel k r} (hW : L'.μW = L.μW) (hW' : L'.μW' = L.μW') (t : ENNReal)
    (hN : L'.μN = t • L.μN) : pairMeas L' = (t * t) • pairMeas L := by
  haveI : SFinite L.μN := sFinite_haarLie _ _
  haveI : IsFiniteMeasure L.μW' := ⟨by rw [L.hμW'.2]; exact ENNReal.one_lt_top⟩
  unfold pairMeas
  rw [hW, hW', hN, Measure.prod_smul_right, Measure.prod_smul_right, Measure.prod_smul_right,
    Measure.prod_smul_left, smul_smul]

end Formalism.L2.SG.Pf.Carrier.CarPinTor
end
end
