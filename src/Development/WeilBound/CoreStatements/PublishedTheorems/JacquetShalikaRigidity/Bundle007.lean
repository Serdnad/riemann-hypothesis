module

public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.ColumnConjugationMeasure
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle382
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle301
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle352
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle410
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Countable
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace PKY

variable {E : Type} [Field E] [NumberField E] {k : ℕ}

def I (ν : Measure (GA E k)) [IsFiniteMeasure ν] : XB E k →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ g, f g ∂ν
      map_add' := fun f f' => integral_add (f.integrable ν) (f'.integrable ν)
      map_smul' := fun c f => integral_smul c (fun g => f g) }
    (ν.real Set.univ) (fun f => f.norm_integral_le_mul_norm ν)

def L (ν : Measure (GA E k)) [IsFiniteMeasure ν] (φ' : XB E k) (h : GA E k) : XB E k →L[ℂ] ℂ :=
  (I ν).comp (((ContinuousLinearMap.mul ℂ (XB E k)).flip (star φ')).comp (Rt E k h))

theorem L_apply (ν : Measure (GA E k)) [IsFiniteMeasure ν] (φ' x : XB E k) (h : GA E k) :
    L ν φ' h x = ∫ g, x (g * h) * conj (φ' g) ∂ν := by
  first
    | rfl
    | (simp only [L, I, ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.flip_apply,
        ContinuousLinearMap.mul_apply', LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk,
        BoundedContinuousFunction.mul_apply, BoundedContinuousFunction.star_apply]
       rfl)

end PKY

theorem ky_of : W0 → KY := by
  intro hW E _ _ _ k μ _ hk β hβ φ'
  have hfin : (μ.withDensity β) (band E k) < ⊤ := (hW E k μ hk).2 β hβ
  haveI hνf : IsFiniteMeasure ((μ.withDensity β).restrict (band E k)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hfin⟩
  have hLR : ∀ (h a : GlobalTheory.CuspRep.GA E k) (x : PositivityTheory.jumpWindows.XB E k),
      PKY.L ((μ.withDensity β).restrict (band E k)) φ' h (PositivityTheory.jumpWindows.Rt E k a x) =
        PKY.L ((μ.withDensity β).restrict (band E k)) φ' (h * a) x := by
    intro h a x
    show PKY.I _ (((ContinuousLinearMap.mul ℂ (PositivityTheory.jumpWindows.XB E k)).flip (star φ'))
        (PositivityTheory.jumpWindows.Rt E k h (PositivityTheory.jumpWindows.Rt E k a x))) =
      PKY.I _ (((ContinuousLinearMap.mul ℂ (PositivityTheory.jumpWindows.XB E k)).flip (star φ')) (PositivityTheory.jumpWindows.Rt E k (h * a) x))
    rw [map_mul]
    rfl
  let Y : Submodule ℂ (PositivityTheory.jumpWindows.XB E k) :=
    { carrier := {x | (∀ (t : ℝ) (g : GlobalTheory.CuspRep.GA E k), x (GlobalTheory.UnitaryBC.splitCentre E k t * g) = x g) ∧
          ∀ h, PKY.L ((μ.withDensity β).restrict (band E k)) φ' h x = 0}
      add_mem' := by
        rintro x x' ⟨hx1, hx2⟩ ⟨hx1', hx2'⟩
        refine ⟨fun t g => ?_, fun h => ?_⟩
        · show x (GlobalTheory.UnitaryBC.splitCentre E k t * g) + x' (GlobalTheory.UnitaryBC.splitCentre E k t * g) = x g + x' g
          rw [hx1, hx1']
        · rw [map_add (f := _), hx2, hx2', add_zero]
      zero_mem' := ⟨fun t g => rfl, fun h => map_zero _⟩
      smul_mem' := by
        rintro c x ⟨hx1, hx2⟩
        refine ⟨fun t g => ?_, fun h => ?_⟩
        · show c • x (GlobalTheory.UnitaryBC.splitCentre E k t * g) = c • x g
          rw [hx1]
        · rw [map_smul, hx2, smul_zero] }
  have hmemL : ∀ x, x ∈ Y ↔ (∀ (t : ℝ) (g : GlobalTheory.CuspRep.GA E k), x (GlobalTheory.UnitaryBC.splitCentre E k t * g) = x g) ∧
      ∀ h, PKY.L ((μ.withDensity β).restrict (band E k)) φ' h x = 0 := fun x => Iff.rfl
  have hc : IsClosed (Y : Set (PositivityTheory.jumpWindows.XB E k)) := by
    have hset : (Y : Set (PositivityTheory.jumpWindows.XB E k)) =
        (⋂ (t : ℝ), ⋂ (g : GlobalTheory.CuspRep.GA E k),
          {x : PositivityTheory.jumpWindows.XB E k | x (GlobalTheory.UnitaryBC.splitCentre E k t * g) = x g}) ∩
        ⋂ h, {x : PositivityTheory.jumpWindows.XB E k | PKY.L ((μ.withDensity β).restrict (band E k)) φ' h x = 0} := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
      exact hmemL x
    rw [hset]
    exact (isClosed_iInter fun t => isClosed_iInter fun g =>
        isClosed_eq (BoundedContinuousFunction.evalCLM ℂ (GlobalTheory.UnitaryBC.splitCentre E k t * g)).continuous
          (BoundedContinuousFunction.evalCLM ℂ g).continuous).inter
      (isClosed_iInter fun h => isClosed_eq (PKY.L _ φ' h).continuous continuous_const)
  refine ⟨Y, hc, ?_, ?_, ?_⟩
  · intro a x hx
    obtain ⟨hx1, hx2⟩ := (hmemL x).mp hx
    refine (hmemL _).mpr ⟨fun t g => ?_, fun h => ?_⟩
    · show x (GlobalTheory.UnitaryBC.splitCentre E k t * g * a) = x (g * a)
      rw [mul_assoc, hx1]
    · rw [hLR]
      exact hx2 _
  · intro x
    rw [hmemL]
    exact and_congr Iff.rfl (forall_congr' fun h => by rw [PKY.L_apply])
  · intro φ hφ ψ S U η s hcut
    have hφ2 := ((hmemL φ).mp hφ).2
    let F : (Fin k → GlobalTheory.CuspRep.Ad E) → PositivityTheory.jumpWindows.XB E k := fun y => (η y : ℂ) • PositivityTheory.jumpWindows.Rt E k (s y)⁻¹ φ
    have hFc : Continuous F := hcut.contV
    have hFs : HasCompactSupport F := by
      have h1 : HasCompactSupport (fun y => (η y : ℂ)) :=
        hcut.cpt.comp_left (g := ((↑) : ℝ → ℂ)) Complex.ofReal_zero
      exact h1.smul_right (f' := fun y => PositivityTheory.jumpWindows.Rt E k (s y)⁻¹ φ)
    have hFi : Integrable F (GroundTheory.Automorphic.FourierWhittaker.vecMeasure E (Fin k)) :=
      hFc.integrable_of_hasCompactSupport hFs
    have hpt : ∀ g : GlobalTheory.CuspRep.GA E k,
        (∫ y, (η y : ℂ) * φ (g * (s y)⁻¹) ∂GroundTheory.Automorphic.FourierWhittaker.vecMeasure E (Fin k)) =
          (∫ y, F y ∂GroundTheory.Automorphic.FourierWhittaker.vecMeasure E (Fin k)) (g * 1) := by
      intro g
      rw [mul_one]
      exact (BoundedContinuousFunction.evalCLM ℂ g).integral_comp_comm hFi
    simp_rw [hpt]
    rw [← PKY.L_apply, ← ContinuousLinearMap.integral_comp_comm _ hFi]
    have hz : ∀ y, PKY.L ((μ.withDensity β).restrict (band E k)) φ' 1 (F y) = 0 := fun y => by
      show PKY.L _ φ' 1 ((η y : ℂ) • PositivityTheory.jumpWindows.Rt E k (s y)⁻¹ φ) = 0
      rw [map_smul, hLR, one_mul, hφ2, smul_zero]
    simp only [hz, integral_zero]

end PositivityTheory.AdelicQuotientData

end
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace primePairSetFirst

variable {E : Type} [Field E] [NumberField E] {k : ℕ} {ψ : AddChar (Ad E) ℂ}

theorem cont_colT (hψ : StdPsi ψ) (m : ℕ) (f : GA E k → ℂ) (hc : Continuous f)
    (hl : ∀ (c : UnipotentBlockColumnIndex k (m + 1) (m + 1) → E) g, f (ratGL E k (blkU c) * g) = f g) :
    Continuous (colT ψ (m + 1) f) := by
  have key := GlobalTheory.T.continuous_quotientAverage_periodic_family (UnipotentBlockColumnIndex k (m + 1) (m + 1) → Ad E) (ratV E (UnipotentBlockColumnIndex k (m + 1) (m + 1)))
    (isCoLat_ratV E _) (GA E k)
    (fun p => ψ (-dot (eLast k (m + 1)) p.2) * f (blkU p.2 * p.1)) ?_ ?_
  · exact key
  · exact (hψ.cont.comp ((continuous_dot _).neg.comp continuous_snd)).mul
      (hc.comp (((continuous_posU _).comp continuous_snd).mul continuous_fst))
  · intro g γ hγ y
    exact (per_coef hψ (eLast k (m + 1)) hc hl g).2 γ hγ y

theorem colT_blkU (hψ : StdPsi ψ) (m : ℕ) (f : GA E k → ℂ) (hc : Continuous f)
    (hl : ∀ (c : UnipotentBlockColumnIndex k (m + 1) (m + 1) → E) g, f (ratGL E k (blkU c) * g) = f g)
    (y : UnipotentBlockColumnIndex k (m + 1) (m + 1) → Ad E) (g : GA E k) :
    colT ψ (m + 1) f (blkU y * g) = ψ (dot (eLast k (m + 1)) y) * colT ψ (m + 1) f g := by
  have hper := per_coef (a := k) hψ (eLast k (m + 1)) hc hl g
  have hT := GlobalTheory.T.quotientAverage_translate_invariant (UnipotentBlockColumnIndex k (m + 1) (m + 1) → Ad E) (ratV E (UnipotentBlockColumnIndex k (m + 1) (m + 1)))
    (isCoLat_ratV E _) _ hper y
  have hpt : (fun x : UnipotentBlockColumnIndex k (m + 1) (m + 1) → Ad E =>
        ψ (-dot (eLast k (m + 1)) x) * f (blkU x * (blkU y * g))) =
      fun x => ψ (dot (eLast k (m + 1)) y) *
        (ψ (-dot (eLast k (m + 1)) (x + y)) * f (blkU (x + y) * g)) := by
    funext x
    have hd : dot (eLast k (m + 1)) (x + y) = dot (eLast k (m + 1)) x + dot (eLast k (m + 1)) y := by
      simp only [dot, Pi.add_apply, mul_add, Finset.sum_add_distrib]
    have hu : (blkU (x + y) : GA E k) = blkU x * blkU y := posU_add _ x y
    have h1 : ψ (dot (eLast k (m + 1)) y) * ψ (-dot (eLast k (m + 1)) y) = 1 := by
      rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
    rw [hd, hu, neg_add, AddChar.map_add_eq_mul, mul_assoc (blkU x)]
    calc ψ (-dot (eLast k (m + 1)) x) * f (blkU x * (blkU y * g))
        = (ψ (dot (eLast k (m + 1)) y) * ψ (-dot (eLast k (m + 1)) y)) *
            (ψ (-dot (eLast k (m + 1)) x) * f (blkU x * (blkU y * g))) := by rw [h1, one_mul]
      _ = _ := by ring
  change avg _ (fun x => ψ (-dot (eLast k (m + 1)) x) * f (blkU x * (blkU y * g))) =
    _ * avg _ (fun x => ψ (-dot (eLast k (m + 1)) x) * f (blkU x * g))
  rw [hpt, avg_const_mul]
  exact congrArg _ hT

theorem colT_law (m : ℕ) (f : GA E k → ℂ) (j : ℕ) (hj : m + 1 < j)
    (hlaw : ∀ (y : UnipotentBlockColumnIndex k j j → Ad E) (g : GA E k), f (blkU y * g) = ψ (dot (eLast k j) y) * f g)
    (y : UnipotentBlockColumnIndex k j j → Ad E) (g : GA E k) :
    colT ψ (m + 1) f (blkU y * g) = ψ (dot (eLast k j) y) * colT ψ (m + 1) f g := by
  simp only [colT, coefF]
  rw [← avg_const_mul]
  congr 1
  funext x
  have e1 : f (blkU x * (blkU y * g)) = ψ (dot (eLast k j) y) * f (blkU x * g) := by
    rw [← mul_assoc, blkU_mul_blkU hj x y, mul_assoc, hlaw, dot_eLast_shift hj x y]
  rw [e1]
  ring

theorem colT_rat (hψ : StdPsi ψ) (m : ℕ) (hmk : m + 1 < k) (f : GA E k → ℂ) (hc : Continuous f)
    (hl : ∀ γ : GL (Fin k) E, IsMir (m + 1) γ → ∀ g, f (ratGL E k γ * g) = f g)
    (γ : GL (Fin k) E) (hγ : IsMir (m + 1) γ) (g : GA E k) :
    colT ψ (m + 1) f (ratGL E k γ * g) = coefF ψ (m + 1) (fun t => γ.val ⟨m, by omega⟩ t.1.1) f g := by
  unfold colT
  rw [GlobalTheory.T.whittakerCoefficient_rationalMirabolic_mul E k ψ hψ m f hc hl γ hγ (eLast k (m + 1)) g]
  congr 1
  funext t
  let s0 : UnipotentBlockColumnIndex k (m + 1) (m + 1) := ⟨(⟨m, by omega⟩, ⟨m + 1, hmk⟩), Nat.lt_succ_self m, le_refl _, le_refl _⟩
  rw [Finset.sum_eq_single s0]
  · have h1 : eLast (E := E) k (m + 1) s0 = 1 := by simp [eLast, s0]
    rw [h1, one_mul]
  · intro s _ hs
    have h0 : eLast (E := E) k (m + 1) s = 0 := by
      simp only [eLast]
      rw [if_neg]
      intro e
      apply hs
      have h2 := s.2.2
      apply Subtype.ext
      exact Prod.ext (Fin.ext (by simp [s0]; omega)) (Fin.ext (by simp [s0]; omega))
    rw [h0, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem blk_eta {m : ℕ} (hmk : m + 1 < k) (t : UnipotentBlockColumnIndex k (m + 1) (m + 1)) :
    (⟨(t.1.1, ⟨m + 1, hmk⟩), t.2.1, le_rfl, le_rfl⟩ : UnipotentBlockColumnIndex k (m + 1) (m + 1)) = t := by
  have h := t.2.2
  exact Subtype.ext (Prod.ext rfl (Fin.ext (by show m + 1 = (t.1.2 : ℕ); omega)))

def rowEquiv (m : ℕ) (hmk : m + 1 < k) : RowT E k (m + 1) ≃ {ξ : UnipotentBlockColumnIndex k (m + 1) (m + 1) → E // ξ ≠ 0} where
  toFun ξ := ⟨fun t => ξ.1 t.1.1, by
    obtain ⟨i, hi⟩ := Function.ne_iff.1 ξ.2.1
    have him : (i : ℕ) < m + 1 := by
      by_contra h
      exact hi (ξ.2.2 i (by omega))
    intro h0
    exact hi (congrFun h0 ⟨(i, ⟨m + 1, hmk⟩), him, le_rfl, le_rfl⟩)⟩
  invFun η := ⟨fun i => if h : (i : ℕ) < m + 1 then η.1 ⟨(i, ⟨m + 1, hmk⟩), h, le_rfl, le_rfl⟩ else 0, by
    refine ⟨fun h0 => η.2 ?_, fun i hi => dif_neg (by omega)⟩
    funext t
    have h1 := congrFun h0 t.1.1
    simp only [Pi.zero_apply] at h1
    rw [dif_pos t.2.1, blk_eta hmk t] at h1
    exact h1⟩
  left_inv ξ := by
    apply Subtype.ext
    funext i
    by_cases h : (i : ℕ) < m + 1
    · exact dif_pos h
    · exact (dif_neg h).trans (ξ.2.2 i (by omega)).symm
  right_inv η := by
    apply Subtype.ext
    funext t
    show (if h : (t.1.1 : ℕ) < m + 1 then η.1 ⟨(t.1.1, ⟨m + 1, hmk⟩), h, le_rfl, le_rfl⟩ else 0) = η.1 t
    rw [dif_pos t.2.1, blk_eta hmk t]

end primePairSetFirst

theorem p1_holds : N0 → P0 → P1 := by
  intro hN _ E _ _ _ k ψ hψ m hm1 hmk f hf
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hl : ∀ (c : UnipotentBlockColumnIndex k (m + 1) (m + 1) → E) g, f (ratGL E k (blkU c) * g) = f g :=
    fun c g => hf.left _ (isMir_blkU c) g
  simp only [Nat.add_sub_cancel]
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ⟨primePairSetFirst.rowEquiv m hmk, fun ξ t => rfl⟩⟩
  · exact primePairSetFirst.cont_colT hψ m f hf.cont hl
  · intro γ hγ g
    have hγ1 : IsMir (m + 1) γ := fun i c h => hγ i c (by omega)
    rw [primePairSetFirst.colT_rat hψ m hmk f hf.cont hf.left γ hγ1 g]
    unfold colT
    congr 1
    funext t
    rw [hγ ⟨m, by omega⟩ t.1.1 (Or.inl le_rfl)]
    have ht := t.2.1
    simp only [eLast, Matrix.one_apply]
    by_cases h : (t.1.1 : ℕ) = m
    · rw [if_pos (Fin.ext h.symm), if_pos (by omega)]
    · rw [if_neg (fun e => h (congrArg Fin.val e).symm), if_neg (by omega)]
  · intro j hj y g
    rcases Nat.lt_or_ge (m + 1) j with h1 | h1
    · exact primePairSetFirst.colT_law m f j h1 (hf.law j h1) y g
    · obtain rfl : j = m + 1 := by omega
      exact primePairSetFirst.colT_blkU hψ m f hf.cont hl y g
  · intro ξ g
    obtain ⟨hB, hrow⟩ := (hN E k (m + 1) (by omega) (by omega)).1 ξ
    have hγ : IsMir (m + 1) (gam ξ) := fun i c h => hB i c (by omega)
    rw [primePairSetFirst.colT_rat hψ m hmk f hf.cont hf.left _ hγ g]
    congr 1
    funext t
    exact (hrow _ _ rfl).symm
  · intro χ hχ
    funext g
    simp only [colT, coefF]
    rw [← avg_const_mul]
    congr 1
    funext x
    rw [hχ]
    ring

end PositivityTheory.AdelicQuotientData

end
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace PKIR

variable {E : Type} [Field E] [NumberField E] {k : ℕ}

theorem dt_pos (g : GA E k) : 0 < Dt g := (GroundTheory.Global.IdeleGroup.ideleModule E (GeneralLinearGroup.det g)).2

theorem ht_nonneg (g : GA E k) (ξ : Fin k → E) : 0 ≤ ht g ξ :=
  div_nonneg (height_nonneg _ _) (Real.rpow_nonneg (dt_pos g).le _)

theorem dmin_nonneg (g : GA E k) : 0 ≤ dmin g := by
  unfold dmin
  exact Real.iInf_nonneg fun ξ => ht_nonneg g ξ.1

theorem wt_nonneg (M : ℕ) (g : GA E k) : 0 ≤ wt M g := by
  unfold wt
  exact pow_nonneg (le_min zero_le_one (dmin_nonneg g)) M

end PKIR

theorem kir_of : jumpWindows.S2 → jumpWindows.G0 → jumpWindows.G2a → jumpWindows.G2c → jumpWindows.G5 → jumpWindows.G5b → K2 → K3 → K4 → K9 → KIR := by
  intro hS2 hG0 hG2a hG2c _hG5 hG5b hK2 hK3 hK4 hK9 E _ _ _ k hk ψ hψ hcof π hπ
  obtain ⟨S₀, hS₀⟩ := hK9 E k hk ψ hψ hcof π hπ
  refine ⟨S₀, fun S hS α hα M j hj U hU Y hYc hYi hYπ => ?_⟩
  obtain ⟨_hcond, h9⟩ := hS₀ S hS
  obtain ⟨φ, hφ, h, x, hhS, hx, hsat, hlev, hwh⟩ := h9 α hα
  obtain ⟨ρ, J, hW, hsm⟩ := hK2 E k hk M
  obtain ⟨x₀, hx₀, hsm₀⟩ := hK3 E k hk M ρ J hW π hπ φ hφ
  have hJx₀ : J x₀ = x := DFunLike.coe_injective (hx₀.trans hx.symm)

  obtain ⟨_, _, _, hSg, hST, _⟩ := hS2 _ k (XB E k) (ρ.comp (infGL E k)) hW.poly
  obtain ⟨g1, g2, _, _, _, _, g7, _⟩ := hG0 E k
  have hsm1 : SmV (ρ.comp (infGL E k)) (ρ h x₀) := by
    set y := cInf h
    set hf := (infGL E k y)⁻¹ * h
    have hcf : cInf hf = 1 := by simp only [hf, map_mul, map_inv, g1, y, inv_mul_cancel]
    have hc : ∀ (g : GL (Fin k) (Cinf E)) z, ρ hf ((ρ.comp (infGL E k)) g z) = (ρ.comp (infGL E k)) g (ρ hf z) := by
      intro g z
      simp only [MonoidHom.comp_apply]
      rw [← ContinuousLinearMap.mul_apply, ← map_mul, g7 hf hcf g, map_mul, ContinuousLinearMap.mul_apply]
    have := hSg y _ (hST (ρ hf) hc x₀ hsm₀)
    simpa only [MonoidHom.comp_apply, ← ContinuousLinearMap.mul_apply, ← map_mul, hf, mul_inv_cancel_left] using this

  obtain ⟨Yg, hYgc, hYgi, hYgm⟩ := hG2a E k ψ hψ
  have hw := fun w : Off E S => hG2c E k w.1 (Finset.univ.val.map (α w)) (by simp)
  choose Yw hYwc hYwi hYwm using hw
  set Y' : Submodule ℂ (XB E k) := Y ⊓ Yg ⊓ ⨅ w, Yw w with hY'
  have hmem : ∀ z, z ∈ Y' ↔ (z ∈ Y ∧ z ∈ Yg) ∧ ∀ w, z ∈ Yw w := fun z => by
    simp only [Y', Submodule.mem_inf, Submodule.mem_iInf]
  have hYOK : YOK ψ S Y' := by
    refine ⟨?_, ?_, ?_⟩
    · rw [Submodule.coe_inf, Submodule.coe_inf, Submodule.coe_iInf]
      exact (hYc.inter hYgc).inter (isClosed_iInter hYwc)
    · intro g hg z hz
      rw [hmem] at hz ⊢
      exact ⟨⟨hYi g z hz.1.1, hYgi g z hz.1.2⟩, fun w => hYwi w g (hg w.1 w.2) z (hz.2 w)⟩
    · intro z hz
      exact ((hYgm z).1 ((hmem z).1 hz).1.2).1
  have hcusp := π.cusp φ hφ
  have hxY' : Rt E k h x ∈ Y' := by
    have hxg : x ∈ Yg := by
      refine (hYgm x).2 ⟨?_, fun γ g => ?_⟩
      · rw [hx]; exact GlobalTheory.T.isMirabolicWhittakerStage_of_isCuspForm E k ψ φ hcusp
      · rw [congrFun hx, congrFun hx]; exact hcusp.1.left γ g
    rw [hmem]
    exact ⟨⟨hYi h x (hYπ x ⟨φ, hφ, hx⟩), hYgi h x hxg⟩,
      fun w => hYwi w h (hhS w.1 w.2) x ((hYwm w x).2 (hsat w))⟩
  have hJ1 : J (ρ h x₀) = Rt E k h x := by rw [hW.inter, hJx₀]
  obtain ⟨x', C, hCU, hx'Y, hsm', hlev', hBlk, hBump⟩ := hK4 E k (wt M) ρ J hW ψ hψ S Y' hYOK j hj U hU (ρ h x₀)
    (hJ1 ▸ hxY') hsm1 (hJ1 ▸ (hG5b E k S).2.1 h x hlev) (hJ1 ▸ hwh)
  obtain ⟨⟨hx'1, hx'2⟩, hx'3⟩ := (hmem _).1 hx'Y
  obtain ⟨hgood, hinv⟩ := (hYgm _).1 hx'2
  refine ⟨J x', hx'1, ⟨hgood, hinv, fun w => (hYwm w _).1 (hx'3 w), hsm x' hsm', hlev', ?_, ⟨C, hCU, hBlk, hBump⟩⟩⟩
  refine ⟨‖x'‖, fun g => ?_⟩
  have hw0 := PKIR.wt_nonneg M g
  rw [hW.mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hw0, mul_comm ‖x'‖]
  exact mul_le_mul_of_nonneg_left (x'.norm_coe_le_norm g) hw0

end PositivityTheory.AdelicQuotientData

end
end
