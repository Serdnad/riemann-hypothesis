module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle005
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle006
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.GlobCore
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle004
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle007
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

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal

namespace PositivityTheory.Rg.Sw.AbsSt.BasisPf

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt

theorem flatEq_of (hI : Iwa) : FlatEq := by
  intro m n ε c t p q e sL ρ hL Q Q' hQ y
  obtain ⟨pp, k, hp, hk, rfl⟩ := hI n y
  rw [hL.law Q pp k hp, hL.law Q' pp k hp, hQ k hk]

variable {m n : ℕ}

def secK (sL : PX m n →ₗ[ℂ] (GR n → ℂ)) (hc : ∀ Q, Continuous (sL Q)) : PX m n →ₗ[ℂ] C(KR n, ℂ) where
  toFun Q := ⟨fun k => sL Q (k : GR n), (hc Q).comp continuous_subtype_val⟩
  map_add' Q Q' := by ext k; simp
  map_smul' a Q := by ext k; simp

theorem secK_apply (sL : PX m n →ₗ[ℂ] (GR n → ℂ)) (hc : ∀ Q, Continuous (sL Q)) (Q : PX m n) (k : KR n) :
    secK sL hc Q k = sL Q (k : GR n) := rfl

theorem bij_toK : Function.Bijective (toK (n := n)) := by
  constructor
  · intro u v h
    apply Subtype.ext
    have := congrArg (fun k : KR n => ((k : GR n) : GL (Fin n ⊕ Fin n) ℂ).1) h
    exact this
  · intro k
    refine ⟨⟨mR (k : GR n), ⟨k.2.2, k.2.1⟩⟩, ?_⟩
    apply Subtype.ext; apply Subtype.ext; apply Units.ext; rfl

instance t2KR : T2Space (KR n) := inferInstance

def homeoK : uSet n ≃ₜ KR n :=
  haveI : CompactSpace (uSet n) := isCompact_iff_compactSpace.1 (isCompact_uSet n)
  continuous_toK.homeoOfEquivCompactToT2 (f := Equiv.ofBijective _ bij_toK)

instance firstCountableBlockMatrices : FirstCountableTopology (M2 n) := by
  show FirstCountableTopology (Fin n ⊕ Fin n → Fin n ⊕ Fin n → ℂ); infer_instance

instance fcKR : FirstCountableTopology (KR n) :=
  (homeoK (n := n)).symm.isInducing.firstCountableTopology

section Op

variable [MeasurableSpace (KR n)] [BorelSpace (KR n)] (ν : Measure (KR n)) [IsFiniteMeasure ν]

theorem integrable_of_cont {f : KR n → ℂ} (hf : Continuous f) : Integrable f ν :=
  integrableOn_univ.1 (hf.continuousOn.integrableOn_compact isCompact_univ)

def piFun (κ : C(KR n, ℂ)) (h : C(KR n, ℂ)) : C(KR n, ℂ) :=
  ⟨fun k' => ∫ k, κ k * h (k' * k) ∂ν, by
    refine continuous_of_dominated (bound := fun _ => ‖κ‖ * ‖h‖) (fun k' => ?_) (fun k' => ?_)
      (integrable_const _) (Filter.Eventually.of_forall fun k => ?_)
    · exact (κ.continuous.mul (h.continuous.comp (continuous_const.mul continuous_id))).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun k => ?_
      rw [norm_mul]
      exact mul_le_mul (κ.norm_coe_le_norm k) (h.norm_coe_le_norm _) (norm_nonneg _) (norm_nonneg _)
    exact continuous_const.mul (h.continuous.comp (continuous_id.mul continuous_const))⟩

theorem piFun_apply (κ h : C(KR n, ℂ)) (k' : KR n) : piFun ν κ h k' = ∫ k, κ k * h (k' * k) ∂ν := rfl

def piL (κ : C(KR n, ℂ)) : C(KR n, ℂ) →L[ℂ] C(KR n, ℂ) :=
  LinearMap.mkContinuous
    { toFun := piFun ν κ
      map_add' := fun h h' => by
        ext k'
        simp only [piFun_apply, ContinuousMap.add_apply, mul_add]
        exact integral_add (integrable_of_cont ν (κ.continuous.mul (h.continuous.comp (continuous_const.mul continuous_id))))
          (integrable_of_cont ν (κ.continuous.mul (h'.continuous.comp (continuous_const.mul continuous_id))))
      map_smul' := fun a h => by
        ext k'
        simp only [piFun_apply, ContinuousMap.smul_apply, smul_eq_mul, RingHom.id_apply]
        rw [← integral_const_mul]
        congr 1; funext k; ring }
    (‖κ‖ * ν.real univ) fun h => by
      refine (ContinuousMap.norm_le _ (by positivity)).2 fun k' => ?_
      simp only [LinearMap.coe_mk, AddHom.coe_mk, piFun_apply]
      calc ‖∫ k, κ k * h (k' * k) ∂ν‖ ≤ (‖κ‖ * ‖h‖) * ν.real univ := by
            refine norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun k => ?_)
            rw [norm_mul]
            exact mul_le_mul (κ.norm_coe_le_norm k) (h.norm_coe_le_norm _) (norm_nonneg _) (norm_nonneg _)
        _ = ‖κ‖ * ν.real univ * ‖h‖ := by ring

theorem piL_apply (κ h : C(KR n, ℂ)) (k' : KR n) : piL ν κ h k' = ∫ k, κ k * h (k' * k) ∂ν := rfl

end Op

end PositivityTheory.Rg.Sw.AbsSt.BasisPf
end
end

section

noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal

namespace PositivityTheory.Rg.Sw.AbsSt.FarK

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt PositivityTheory.Rg.Sw.AbsSt.Far

variable {m n : ℕ} {ε : Fin m → Bool} {c t : ℝ} {p q : ℕ} {e : ℤ} {sL : PX m n →ₗ[ℂ] (GR n → ℂ)}
  {ρ : GR n → PX m n →ₗ[ℂ] PX m n}

theorem sL_bound (hI : Iwa) (hM : Mult) (hD : CayleyBlocksInvertible) (hL : LocData ε c t p q e sL ρ) (Q : PX m n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : GR n, ‖sL Q y‖ ≤ C * ‖F0 p q e y‖ := by
  have hK : IsCompact (KR n : Set (GR n)) := by
    simpa [Subtype.range_coe] using (isCompact_KR (n := n)).image continuous_subtype_val
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn (hL.cont Q).continuousOn
  have hne : ((KR n : Subgroup (GR n)) : Set (GR n)).Nonempty := ⟨1, (KR n).one_mem⟩
  obtain ⟨k0, -, hmin⟩ := hK.exists_isMinOn hne (continuous_weight_factor (n := n) hD p q e).norm.continuousOn
  have hδ : 0 < ‖F0 p q e k0‖ := norm_pos_iff.mpr (weight_factor_ne_zero hD p q e k0)
  refine ⟨max B 0 / ‖F0 p q e k0‖, div_nonneg (le_max_right _ _) hδ.le, fun y => ?_⟩
  obtain ⟨u, k, hu, hk, rfl⟩ := hI n y
  have hmk : ‖F0 p q e k0‖ ≤ ‖F0 p q e k‖ := hmin hk
  rw [hL.law Q u k hu, ((hM n p q e).1 u k hk).1, norm_mul, norm_mul]
  have h1 : ‖sL Q k‖ ≤ max B 0 := (hB k hk).trans (le_max_left _ _)
  have h2 : max B 0 ≤ max B 0 / ‖F0 p q e k0‖ * ‖F0 p q e k‖ := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hδ]
    exact mul_le_mul_of_nonneg_left hmk (le_max_right _ _)
  calc ‖F0 p q e u‖ * ‖sL Q k‖ ≤ ‖F0 p q e u‖ * (max B 0 / ‖F0 p q e k0‖ * ‖F0 p q e k‖) :=
        mul_le_mul_of_nonneg_left (h1.trans h2) (norm_nonneg _)
    _ = max B 0 / ‖F0 p q e k0‖ * (‖F0 p q e u‖ * ‖F0 p q e k‖) := by ring

theorem rpow_le_add {a x₁ x₂ s : ℝ} (ha : 0 < a) (h₁ : x₁ ≤ s) (h₂ : s ≤ x₂) : a ^ s ≤ a ^ x₁ + a ^ x₂ := by
  rcases le_total 1 a with h | h
  · have := Real.rpow_le_rpow_of_exponent_le h h₂
    have := Real.rpow_nonneg ha.le x₁
    linarith
  · have := Real.rpow_le_rpow_of_exponent_ge ha h h₁
    have := Real.rpow_nonneg ha.le x₂
    linarith

section Glob

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
  [SecondCountableTopology G] {Pp Γ : Subgroup G} {ι : GR n →* G} {s₀ : ℂ} {Ht : G → ℝ≥0}
  {sec I : PX m n →ₗ[ℂ] (G → ℂ)}

theorem Ht_pos (hD : CayleyBlocksInvertible) (hG : GlobCore ε c sL ρ G Pp Γ ι s₀ Ht sec I) (x : G) : 0 < (Ht x : ℝ) := by
  obtain ⟨x₀, y, S, r, hr, rfl, h⟩ := hG.split x
  rw [(h y).1]
  exact mul_pos hr (hLoc_pos hD y)

theorem sec_bound (hI : Iwa) (hM : Mult) (hD : CayleyBlocksInvertible) (hL : LocData ε c t p q e sL ρ)
    (hG : GlobCore ε c sL ρ G Pp Γ ι s₀ Ht sec I) (Q : PX m n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : G, ‖sec Q x‖ ≤ C * ‖sec 1 x‖ := by
  obtain ⟨C, hC0, hC⟩ := PositivityTheory.Rg.Sw.AbsSt.FarK.sL_bound hI hM hD hL Q
  refine ⟨C, hC0, fun x => ?_⟩
  obtain ⟨x0, y, S, r, -, hx, hy⟩ := hG.split x
  subst hx
  rw [(hy y).2 Q, (hy y).2 1, hL.vac y, norm_mul, norm_mul, mul_left_comm]
  exact mul_le_mul_of_nonneg_left (hC y) (norm_nonneg S)

theorem norm_hz (hD : CayleyBlocksInvertible) (hG : GlobCore ε c sL ρ G Pp Γ ι s₀ Ht sec I) (z : ℂ) (Q : PX m n) (x : G) :
    ‖hz Ht sec s₀ z Q x‖ = (Ht x : ℝ) ^ (z.re - s₀.re) * ‖sec Q x‖ := by
  have hpos := PositivityTheory.Rg.Sw.AbsSt.FarK.Ht_pos hD hG x
  simp only [hz, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hpos, Complex.sub_re]

end Glob

end PositivityTheory.Rg.Sw.AbsSt.FarK
end
end

section

noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal

namespace PositivityTheory.Rg.Sw.AbsSt.FarK

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt PositivityTheory.Rg.Sw.AbsSt.Far

variable {m n : ℕ} {ε : Fin m → Bool} {c t : ℝ} {p q : ℕ} {e : ℤ} {sL : PX m n →ₗ[ℂ] (GR n → ℂ)}
  {ρ : GR n → PX m n →ₗ[ℂ] PX m n}
  {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
  [SecondCountableTopology G] {Pp Γ : Subgroup G} {ι : GR n →* G} {s₀ : ℂ} {Ht : G → ℝ≥0}
  {sec I : PX m n →ₗ[ℂ] (G → ℂ)}

theorem split_mul (x₀ : G) (y k : GR n) : x₀ * ι y * ι k = x₀ * ι (y * k) := by
  rw [mul_assoc, ← map_mul]

theorem cont_hz (hD : CayleyBlocksInvertible) (hL : LocData ε c t p q e sL ρ) (hG : GlobCore ε c sL ρ G Pp Γ ι s₀ Ht sec I)
    (z : ℂ) (b : GR n) (x : G) : Continuous fun k : KR n => hz Ht sec s₀ z 1 (x * ι ((k : GR n) * b)) := by
  obtain ⟨x₀, y, S, r, hr, rfl, h⟩ := hG.split x
  have hfun : (fun k : KR n => hz Ht sec s₀ z 1 (x₀ * ι y * ι ((k : GR n) * b))) =
      fun k : KR n => ((r * hLoc (y * (k : GR n) * b) : ℝ) : ℂ) ^ (z - s₀) * (S * F0 p q e (y * (k : GR n) * b)) := by
    funext k
    unfold hz
    rw [split_mul, ← mul_assoc y (k : GR n) b, (h _).1, (h _).2 1, hL.vac]
  rw [hfun]
  have hc : Continuous fun k : KR n => y * (k : GR n) * b :=
    (continuous_const.mul continuous_subtype_val).mul continuous_const
  refine Continuous.mul ?_ (continuous_const.mul ((continuous_weight_factor hD p q e).comp hc))
  refine Continuous.cpow ?_ continuous_const (fun k => ?_)
  · exact Complex.continuous_ofReal.comp (continuous_const.mul ((continuous_hLoc hD).comp hc))
  · exact Complex.ofReal_mem_slitPlane.mpr (mul_pos hr (hLoc_pos hD _))

theorem pointId [MeasurableSpace (KR n)] (hD : CayleyBlocksInvertible) (hL : LocData ε c t p q e sL ρ)
    (hG : GlobCore ε c sL ρ G Pp Γ ι s₀ Ht sec I) {ν : Measure (KR n)} {κ : KR n → ℂ} {N : ℕ}
    {yy : Fin N → GR n} {QQ : Fin N → PX m n} {M : ℂ → Matrix (Fin N) (Fin N) ℂ}
    (hMid : ∀ (w : ℂ) (i : Fin N) (y' : GR n), ∫ k, κ k * ((hLoc (y' * (k : GR n) * yy i) : ℂ) ^ w *
        F0 p q e (y' * (k : GR n) * yy i)) ∂ν = (hLoc y' : ℂ) ^ w * ∑ j, M w i j * sL (QQ j) y')
    (z : ℂ) (i : Fin N) (x : G) :
    ∫ k, κ k * hz Ht sec s₀ z 1 (x * ι ((k : GR n) * yy i)) ∂ν = ∑ j, M (z - s₀) i j * hz Ht sec s₀ z (QQ j) x := by
  obtain ⟨x₀, y, S, r, hr, rfl, h⟩ := hG.split x
  have hfun : (fun k : KR n => κ k * hz Ht sec s₀ z 1 (x₀ * ι y * ι ((k : GR n) * yy i))) =
      fun k : KR n => ((r : ℂ) ^ (z - s₀) * S) *
        (κ k * ((hLoc (y * (k : GR n) * yy i) : ℂ) ^ (z - s₀) * F0 p q e (y * (k : GR n) * yy i))) := by
    funext k
    unfold hz
    rw [split_mul, ← mul_assoc y (k : GR n) (yy i), (h _).1, (h _).2 1, hL.vac, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg hr.le (hLoc_pos hD _).le]
    ring
  rw [hfun, integral_const_mul, hMid (z - s₀) i y, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold hz
  rw [(h y).1, (h y).2 (QQ j), Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hr.le (hLoc_pos hD _).le]
  ring

end PositivityTheory.Rg.Sw.AbsSt.FarK
end
end

section

noncomputable section

open MeasureTheory Matrix Set Filter Topology

namespace PositivityTheory.Rg.Sw.AbsSt.DF

open PositivityTheory.Rg.Sw

variable {m n : ℕ}

theorem cnt_add (ε : Fin m → Bool) : cnt ε true + cnt ε false = m := by
  unfold cnt
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin m))) (fun a => ε a = true)
  simp only [Finset.card_univ, Fintype.card_fin] at h
  have h2 : (Finset.univ.filter fun a => ε a = false) = Finset.univ.filter fun a => ¬ ε a = true := by
    ext a; simp
  rw [h2]
  exact h

theorem bS_herm (X : Fin n → ℝ) (h : ℝ) {b : Matrix (Fin n) (Fin n) ℂ} (hb : b.IsHermitian) : (bS X h b).IsHermitian := by
  have hD : (diagonal (fun j => (Real.exp (-(h * X j)) : ℂ)))ᴴ = diagonal (fun j => (Real.exp (-(h * X j)) : ℂ)) := by
    rw [Matrix.diagonal_conjTranspose]
    congr 1
    funext j
    exact Complex.conj_ofReal _
  unfold bS Matrix.IsHermitian
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hD, hb.eq, Matrix.mul_assoc]

theorem derivative_vacuum_of_parts (hG : GaussPart) (hH : GroupPart) : DerivativeVacuumDilations := by
  intro m n ε c t p q e sL ρ hL X a hA y r
  obtain ⟨hadd, ha0, hup, hcont, hupmul, hdec, hconj, hcellinv, hdense, hF0⟩ := hH n X a hA
  obtain ⟨C, hC0, hcell⟩ := hL.cell
  have hpq : p + q = m := by
    rcases hL.sign with ⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩
    · exact cnt_add ε
    · rw [add_comm]; exact cnt_add ε
  have hneg : ∀ h : ℝ, a (-h) * a h = 1 := by
    intro h; rw [← hadd, neg_add_cancel, ha0]

  have L1 : ∀ (Q : PX m n) (y : GR n), (mR y).toBlocks₂₁.det ≠ 0 →
      HasDerivAt (fun h => sL Q (y * a h)) (sL (dil c X Q) y) 0 := by
    intro Q y hy
    obtain ⟨y₁, g, b, hy₁, hb, hg, rfl⟩ := hdec y hy
    have hfun : (fun h => sL Q (y₁ * g * a h)) = fun h => (F0 p q e y₁ * C) *
        (Complex.exp (-((h * ((m : ℝ) * ∑ j, X j) : ℝ) : ℂ)) * secN ε c t Q (bS X h b)) := by
      funext h
      have e1 : y₁ * g * a h = (y₁ * a (-h)) * (a h * g * a h) := by
        calc y₁ * g * a h = y₁ * (a (-h) * a h) * g * a h := by rw [hneg, mul_one]
          _ = _ := by group
      have e2 : F0 p q e (y₁ * a (-h)) = F0 p q e y₁ * F0 p q e (a (-h)) := by
        rw [← hL.vac, hL.law 1 _ _ hy₁, hL.vac]
      have e3 : F0 p q e (a (-h)) = Complex.exp (-((h * ((m : ℝ) * ∑ j, X j) : ℝ) : ℂ)) := by
        rw [hF0, hpq]
      rw [e1, hL.law Q _ _ (hupmul y₁ hy₁ (-h)), e2, e3, hcell Q _ _ (bS_herm X h hb) (hconj g b hg h)]
      ring
    rw [hfun]
    have hv : sL (dil c X Q) (y₁ * g) = (F0 p q e y₁ * C) * secN ε c t (dil c X Q) b := by
      rw [hL.law _ _ _ hy₁, hcell _ _ _ hb hg]; ring
    rw [hv]
    exact (hG m n ε c t hL.cpos X b hb Q).const_mul _

  have L2 : ∀ (Q : PX m n) (y : GR n), (mR y).toBlocks₂₁.det ≠ 0 → ∀ s,
      HasDerivAt (fun h => sL Q (y * a h)) (sL (dil c X Q) (y * a s)) s := by
    intro Q y hy s
    have h0 := L1 Q (y * a s) (hcellinv y hy s)
    have h0' : HasDerivAt (fun h => sL Q (y * a s * a h)) (sL (dil c X Q) (y * a s)) (s - s) := by
      rw [sub_self]; exact h0
    have h1 := HasDerivAt.comp_sub_const s s h0'
    have hf : (fun x => sL Q (y * a x)) = fun x => sL Q (y * a s * a (x - s)) := by
      funext x
      rw [mul_assoc, ← hadd, add_sub_cancel]
    rw [hf]
    exact h1
  have hjc : ∀ (Q : PX m n), Continuous (fun z : GR n × ℝ => sL Q (z.1 * a z.2)) := fun Q =>
    (hL.cont Q).comp (continuous_fst.mul (hcont.comp continuous_snd))

  have L3 : ∀ (Q : PX m n) (s : ℝ) (y : GR n),
      sL Q (y * a s) - sL Q y = ∫ u in (0 : ℝ)..s, sL (dil c X Q) (y * a u) := by
    intro Q s
    have hc1 : Continuous fun y : GR n => sL Q (y * a s) - sL Q y :=
      ((hL.cont Q).comp (continuous_id.mul continuous_const)).sub (hL.cont Q)
    have hc2 : Continuous fun y : GR n => ∫ u in (0 : ℝ)..s, sL (dil c X Q) (y * a u) :=
      intervalIntegral.continuous_parametric_intervalIntegral_of_continuous (hjc (dil c X Q)) continuous_const
    intro y0
    refine congrFun (Continuous.ext_on hdense hc1 hc2 ?_) y0
    intro y hy
    show sL Q (y * a s) - sL Q y = ∫ u in (0 : ℝ)..s, sL (dil c X Q) (y * a u)
    have hd : ∀ x ∈ Set.uIcc (0 : ℝ) s, HasDerivAt (fun h => sL Q (y * a h)) (sL (dil c X Q) (y * a x)) x :=
      fun x _ => L2 Q y hy x
    have hint : IntervalIntegrable (fun u => sL (dil c X Q) (y * a u)) volume 0 s :=
      ((hL.cont (dil c X Q)).comp (continuous_const.mul hcont)).intervalIntegrable 0 s
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint, ha0, mul_one]
  have L4 : ∀ (Q : PX m n) (y : GR n) (s : ℝ),
      HasDerivAt (fun h => sL Q (y * a h)) (sL (dil c X Q) (y * a s)) s := by
    intro Q y s
    have hgc : Continuous fun u => sL (dil c X Q) (y * a u) := (hL.cont _).comp (continuous_const.mul hcont)
    have h1 := (hgc.integral_hasStrictDerivAt 0 s).hasDerivAt
    have h2 := h1.const_add (sL Q y)
    have hf : (fun h => sL Q (y * a h)) = fun x => sL Q y + ∫ u in (0 : ℝ)..x, sL (dil c X Q) (y * a u) := by
      funext x
      rw [← L3 Q x y]; ring
    rw [hf]
    exact h2
  have L5 : ∀ k : ℕ, iteratedDeriv k (fun s => F0 p q e (y * a s)) = fun s => sL ((dil c X ^ k) 1) (y * a s) := by
    intro k
    induction k with
    | zero => funext s; simp [hL.vac]
    | succ k ih =>
      rw [iteratedDeriv_succ, ih]
      funext s
      rw [(L4 _ y s).deriv, pow_succ', Module.End.mul_apply]
  refine ⟨?_, ?_⟩
  · rw [L5 r]
    have := L4 ((dil c X ^ r) 1) y 0
    rw [ha0, mul_one, ← Module.End.mul_apply, ← pow_succ'] at this
    exact this
  · rw [L5 r]
    show sL ((dil c X ^ r) 1) (y * a 0) = _
    rw [ha0, mul_one]

end PositivityTheory.Rg.Sw.AbsSt.DF
end
end

section

noncomputable section

open MeasureTheory Matrix Set Filter Topology

namespace PositivityTheory.Rg.Sw.AbsSt

open PositivityTheory.Rg.Sw

theorem cont_KR_mul (n : ℕ) (y k1 : GR n) : Continuous (fun k : KR n => y * (k : GR n) * k1) :=
  (continuous_const.mul continuous_subtype_val).mul continuous_const

theorem cont_KR_mul' (n : ℕ) (k1 : GR n) : Continuous (fun k : KR n => (k : GR n) * k1) :=
  continuous_subtype_val.mul continuous_const

theorem spherical_section_eq_extension {n : ℕ} (p q : ℕ) (e : ℤ) (g : GR n) : F0 p q e g = twistedScalarSection p q e (mR g) := by
  simp only [F0, twistedScalarSection]

theorem inK_mul {n : ℕ} (k : KR n) (k1 : GR n) (hk1 : k1 ∈ KR n) : InK (mR ((k : GR n) * k1)) :=
  (KR n).mul_mem k.2 hk1

theorem continuousOn_twisted_section_compact {n : ℕ} (p q : ℕ) (e : ℤ) (X : Fin n → ℝ) (y k1 : GR n) (U : Set ℂ) (κ : KR n → ℂ)
    (hκ : Continuous κ) (C : Set (GR n)) (hC : ∀ k : KR n, y * (k : GR n) * k1 ∈ C)
    (hU2c : ContinuousOn (fun yz : GR n × ℂ => twistedScalarSection p q e (mR yz.1 * aZ X yz.2)) (C ×ˢ U)) :
    ContinuousOn (fun yz : KR n × ℂ => κ yz.1 * twistedScalarSection p q e (mR (y * (yz.1 : GR n) * k1) * aZ X yz.2)) (univ ×ˢ U) := by
  refine (hκ.comp continuous_fst).continuousOn.mul ?_
  have hφ : Continuous (fun yz : KR n × ℂ => (y * (yz.1 : GR n) * k1, yz.2)) :=
    ((cont_KR_mul n y k1).comp continuous_fst).prodMk continuous_snd
  have hcmp : (fun yz : KR n × ℂ => twistedScalarSection p q e (mR (y * (yz.1 : GR n) * k1) * aZ X yz.2)) =
      (fun yz : GR n × ℂ => twistedScalarSection p q e (mR yz.1 * aZ X yz.2)) ∘ (fun yz : KR n × ℂ => (y * (yz.1 : GR n) * k1, yz.2)) :=
    funext fun _ => rfl
  rw [hcmp]
  exact ContinuousOn.comp (g := fun yz : GR n × ℂ => twistedScalarSection p q e (mR yz.1 * aZ X yz.2)) hU2c hφ.continuousOn
    (fun yz hyz => ⟨hC yz.1, hyz.2⟩)

theorem contOn_Fid {n : ℕ} (k1 : GR n) (U U1 : Set ℂ) (hUU : U ⊆ U1) (κ : KR n → ℂ) (hκ : Continuous κ)
    (Fid : GR n → ℂ → ℂ) (hFidc : ContinuousOn (fun y : GR n × ℂ => Fid y.1 y.2) (univ ×ˢ U1)) :
    ContinuousOn (fun yz : KR n × ℂ => κ yz.1 * Fid ((yz.1 : GR n) * k1) yz.2) (univ ×ˢ U) := by
  refine (hκ.comp continuous_fst).continuousOn.mul ?_
  have hφ : Continuous (fun yz : KR n × ℂ => ((yz.1 : GR n) * k1, yz.2)) :=
    ((cont_KR_mul' n k1).comp continuous_fst).prodMk continuous_snd
  have hcmp : (fun yz : KR n × ℂ => Fid ((yz.1 : GR n) * k1) yz.2) =
      (fun y : GR n × ℂ => Fid y.1 y.2) ∘ (fun yz : KR n × ℂ => ((yz.1 : GR n) * k1, yz.2)) :=
    funext fun _ => rfl
  rw [hcmp]
  exact ContinuousOn.comp (g := fun y : GR n × ℂ => Fid y.1 y.2) hFidc hφ.continuousOn
    (fun yz hyz => ⟨mem_univ _, hUU hyz.2⟩)

end PositivityTheory.Rg.Sw.AbsSt
end
end
