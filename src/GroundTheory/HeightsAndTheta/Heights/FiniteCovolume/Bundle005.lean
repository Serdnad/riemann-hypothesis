module

public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle001
public import GroundTheory.HeightsAndTheta.Theta.EisensteinZeta.MirabolicInduction.LinearIndependentRealOfInt
public import GroundTheory.HeightsAndTheta.Heights.Bundle001
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle004
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open Module Submodule Matrix GroundTheory.Heights₂.Theta.FunctionalEquationAlt.ShortGen

noncomputable section

theorem ReducedBasisBound.short_basis {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [FiniteDimensional ℝ W] (m : ℕ) : ∀ lam : ℝ, 0 < lam → ∀ C : ℝ, ∃ R : ℝ,
    ∀ b : Fin m → W, LinearIndependent ℝ b → Sep (span ℤ (Set.range b)) lam →
      (gram ℝ b).det ≤ C → ∃ b' : Fin m → W, span ℤ (Set.range b') = span ℤ (Set.range b) ∧
        ∀ i, ‖b' i‖ ≤ R := by
  induction m with
  | zero => exact fun _ _ _ => ⟨0, fun b _ _ _ => ⟨b, rfl, fun i => i.elim0⟩⟩
  | succ m ih =>
    intro lam hlam C
    obtain ⟨g, hg, hgb⟩ := (bounds (W := W) m).1 (lam / 2) (half_pos hlam)
    obtain ⟨R', hR'⟩ := ih (lam / 2) (half_pos hlam) (C / lam ^ 2)
    refine ⟨|R'| + Real.sqrt (C / g), fun b hb hsep hC => ?_⟩
    obtain ⟨v, c, hvL, hv, hlv, hmin, hc, hmemc, hsepc, hdet⟩ := decompose b hb hlam hsep
    have hgc := hgb c hc hsepc
    have hv2 : ‖v‖ ^ 2 ≤ C / g := by
      rw [le_div_iff₀ hg]
      nlinarith [mul_le_mul_of_nonneg_left hgc (sq_nonneg ‖v‖)]
    have hvR : ‖v‖ ≤ Real.sqrt (C / g) := (le_abs_self _).trans (Real.abs_le_sqrt hv2)
    have hcC : (gram ℝ c).det ≤ C / lam ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      have h2 : lam ^ 2 ≤ ‖v‖ ^ 2 := pow_le_pow_left₀ hlam.le hlv 2
      nlinarith [hg.le.trans hgc]
    obtain ⟨c', hc'span, hc'R⟩ := hR' c hc hsepc hcC
    set L := span ℤ (Set.range b) with hL
    have hlift : ∀ i, ∃ y ∈ L, proj v y = c' i ∧ ‖y‖ ≤ ‖c' i‖ + ‖v‖ / 2 := by
      intro i
      have hci : c' i ∈ span ℤ (Set.range c) := hc'span ▸ subset_span ⟨i, rfl⟩
      obtain ⟨x, hx, hxe⟩ := (hmemc _).1 hci
      obtain ⟨y, hyL, hy, hyn⟩ := exists_lift hvL hv hx
      exact ⟨y, hyL, hy.trans hxe, hxe ▸ hyn⟩
    choose y hyL hy hyn using hlift
    refine ⟨Fin.cons v y, le_antisymm ?_ ?_, fun i => ?_⟩
    · rw [span_le]
      rintro _ ⟨i, rfl⟩
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using hvL
      · simpa using hyL j
    · intro x hx
      obtain ⟨k, hk⟩ := (mem_span_range_iff_exists_fun ℤ).1
        (hc'span ▸ (hmemc (proj v x)).2 ⟨x, hx, rfl⟩)
      have hzL : ∑ j, k j • y j ∈ L := L.sum_mem fun j _ => L.smul_mem _ (hyL j)
      have h0 : proj v (x - ∑ j, k j • y j) = 0 := by

        rw [map_sub, map_sum, ← hk, sub_eq_zero]
        simp [map_zsmul, hy]
      obtain ⟨n, hn⟩ := mem_zsmul_of_proj_eq_zero hvL hv hmin (L.sub_mem hx hzL) h0
      have hxe : x = n • v + ∑ j, k j • y j := by rw [← hn]; abel
      rw [hxe]
      refine add_mem (smul_mem _ _ (subset_span ⟨0, by simp⟩))
        (sum_mem fun j _ => smul_mem _ _ (subset_span ⟨j.succ, by simp⟩))
    · have hs := Real.sqrt_nonneg (C / g)
      refine Fin.cases ?_ (fun j => ?_) i
      · simp only [Fin.cons_zero]
        linarith [abs_nonneg R']
      · simp only [Fin.cons_succ]
        linarith [hyn j, hc'R j, le_abs_self R']

theorem ReducedBasisBound.proof : ReducedBasisBound.Statement := by
  intro d t c ht
  obtain ⟨R, hR⟩ := ReducedBasisBound.short_basis (W := EuclideanSpace ℝ (Fin d)) d t ht (c ^ 2)
  refine ⟨R, fun L _ _ hmin hcov => ?_⟩
  have hrk : finrank ℤ L = d := by rw [ZLattice.rank ℝ L, finrank_euclideanSpace_fin]
  let e : Basis (Fin d) ℤ L := Module.finBasisOfFinrankEq ℤ L hrk
  have hspan : span ℤ (Set.range fun i => (e i : EuclideanSpace ℝ (Fin d))) = L := by
    rw [show (Set.range fun i => (e i : EuclideanSpace ℝ (Fin d))) = L.subtype '' Set.range e by
      rw [← Set.range_comp]; rfl, ← Submodule.map_span, e.span_eq, Submodule.map_top,
      Submodule.range_subtype]
  have hli : LinearIndependent ℝ fun i => (e i : EuclideanSpace ℝ (Fin d)) := by
    have h := (e.ofZLatticeBasis ℝ L).linearIndependent
    rwa [show ⇑(e.ofZLatticeBasis ℝ L) = fun i => (e i : EuclideanSpace ℝ (Fin d)) from
      funext fun i => e.ofZLatticeBasis_apply ℝ L i] at h
  have hdet : (gram ℝ fun i => (e i : EuclideanSpace ℝ (Fin d))).det ≤ c ^ 2 := by
    have h1 := GroundTheory.Heights₂.Heights.covolume_eq_sqrt_det_gram L e
    rcases le_or_gt 0 (gram ℝ fun i => (e i : EuclideanSpace ℝ (Fin d))).det with h | h
    · rw [← Real.sq_sqrt h, ← h1]
      exact pow_le_pow_left₀ (ZLattice.covolume_pos L).le hcov 2
    · nlinarith [sq_nonneg c]
  have hsep : Sep (span ℤ (Set.range fun i => (e i : EuclideanSpace ℝ (Fin d)))) t := by
    rw [hspan]; exact hmin
  obtain ⟨b', hb'span, hb'R⟩ := hR _ hli hsep hdet
  rw [hspan] at hb'span
  have htop : ⊤ ≤ span ℝ (Set.range b') := by
    rw [← IsZLattice.span_top (K := ℝ) (L := L), ← hb'span, Submodule.span_span_of_tower]
  have hliR : LinearIndependent ℝ b' :=
    linearIndependent_of_top_le_span_of_card_eq_finrank htop (by simp)
  refine ⟨(Basis.span (hliR.restrict_scalars' ℤ)).map (LinearEquiv.ofEq _ _ hb'span), fun i => ?_⟩
  simpa using hb'R i

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open GroundTheory.Automorphic Module

noncomputable section

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]

namespace ComplementForm

theorem conj_apply (h : HermitianForm F E W) (x y : W) :
    conjHom F E (h.toSesq x y) = h.toSesq y x :=
  LinearMap.isSymm_def.1 h.isSymm x y

theorem apply_w_v {h : HermitianForm F E W} {v w : W} (hp : IsHyperbolicPair h v w) :
    h.toSesq w v = 1 := by
  rw [← conj_apply h v w, hp.2.2, map_one]

def proj (h : HermitianForm F E W) (v w : W) (hp : IsHyperbolicPair h v w) :
    W →ₗ[E] hypComplement h v w :=
  LinearMap.codRestrict (hypComplement h v w)
    (LinearMap.id - (h.toSesq w).smulRight v - (h.toSesq v).smulRight w) fun x => by
      rw [mem_hypComplement]
      simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smulRight_apply, map_sub,
        map_smul, smul_eq_mul, hp.1, hp.2.1, hp.2.2, apply_w_v hp]
      constructor <;> ring

theorem proj_apply (h : HermitianForm F E W) (v w : W) (hp : IsHyperbolicPair h v w) (x : W) :
    (proj h v w hp x : W) = x - h.toSesq w x • v - h.toSesq v x • w := rfl

theorem eq_add_proj (h : HermitianForm F E W) (v w : W) (hp : IsHyperbolicPair h v w) (x : W) :
    x = h.toSesq w x • v + (proj h v w hp x : W) + h.toSesq v x • w := by
  rw [proj_apply]; abel

theorem proj_of_mem (h : HermitianForm F E W) (v w : W) (hp : IsHyperbolicPair h v w)
    (x : hypComplement h v w) : proj h v w hp x = x := by
  obtain ⟨h1, h2⟩ := mem_hypComplement.1 x.2
  ext
  rw [proj_apply, h1, h2, zero_smul, zero_smul, sub_zero, sub_zero]

def restr (h : HermitianForm F E W) (v w : W) :
    hypComplement h v w →ₛₗ[conjHom F E] hypComplement h v w →ₗ[E] E :=
  LinearMap.mk₂'ₛₗ (conjHom F E) (RingHom.id E) (fun x y => h.toSesq x y)
    (fun _ _ _ => by simp only [Submodule.coe_add, map_add (f := _), LinearMap.add_apply])
    (fun _ _ _ => by simp only [Submodule.coe_smul, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul])
    (fun _ _ _ => by simp only [Submodule.coe_add, map_add (f := _)])
    (fun _ _ _ => by simp only [Submodule.coe_smul, map_smul, smul_eq_mul, RingHom.id_apply])

theorem restr_apply (h : HermitianForm F E W) (v w : W) (x y : hypComplement h v w) :
    restr h v w x y = h.toSesq x y := rfl

def form (h : HermitianForm F E W) (v w : W) (hp : IsHyperbolicPair h v w) :
    HermitianForm F E (hypComplement h v w) where
  toSesq := restr h v w
  isSymm := LinearMap.isSymm_def.2 fun x y => conj_apply h x y
  nonsingular := by
    constructor
    · refine (injective_iff_map_eq_zero _).2 fun a ha => ?_
      obtain ⟨h1, h2⟩ := mem_hypComplement.1 a.2
      have hav : h.toSesq a v = 0 := by rw [← conj_apply, h1, map_zero]
      have haw : h.toSesq a w = 0 := by rw [← conj_apply, h2, map_zero]
      have hall : h.toSesq (a : W) = 0 := by
        ext y
        have hy : h.toSesq (a : W) (proj h v w hp y) = 0 := by
          rw [← restr_apply, ha, LinearMap.zero_apply]
        rw [eq_add_proj h v w hp y, map_add (f := _), map_add (f := _), map_smul, map_smul, hav, haw, hy,
          LinearMap.zero_apply]
        simp
      have : (a : W) = 0 := h.nonsingular.1 (hall.trans (map_zero _).symm)
      exact Subtype.ext this
    · intro φ
      obtain ⟨y, hy⟩ := h.nonsingular.2 (φ ∘ₗ proj h v w hp)
      have hpv : proj h v w hp v = 0 := by
        ext; rw [proj_apply, hp.1, apply_w_v hp, one_smul, zero_smul]; simp
      have hpw : proj h v w hp w = 0 := by
        ext; rw [proj_apply, hp.2.1, hp.2.2, one_smul, zero_smul]; simp
      have hyv : h.toSesq y v = 0 := by
        rw [hy, LinearMap.comp_apply, hpv, map_zero]
      have hyw : h.toSesq y w = 0 := by
        rw [hy, LinearMap.comp_apply, hpw, map_zero]
      have hmem : y ∈ hypComplement h v w := by
        rw [mem_hypComplement, ← conj_apply h y v, ← conj_apply h y w, hyv, hyw, map_zero]
        exact ⟨rfl, rfl⟩
      refine ⟨⟨y, hmem⟩, ?_⟩
      ext z
      rw [restr_apply, hy, LinearMap.comp_apply, proj_of_mem]

end ComplementForm

theorem ComplementForm.proof (h : HermitianForm F E W) : ComplementForm.Statement h :=
  fun v w hp => ⟨ComplementForm.form h v w hp, fun _ _ => rfl⟩

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module

variable {F E : Type*} [Field F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι]


omit [NumberField E] in
theorem HermitianForm.eq_zero_of_toSesq_eq_zero (h : HermitianForm F E W) {x : W}
    (hx : ∀ w, h.toSesq x w = 0) : x = 0 := by
  apply h.nonsingular.1
  rw [map_zero]
  exact LinearMap.ext hx

theorem TraceHermNondegenerate.proof (h : HermitianForm F E W) (v : Basis ι E W) :
    TraceHermNondegenerate.Statement h v := by
  have hT := (traceForm_nondegenerate ℚ E).1
  constructor
  · intro y hy
    have key : ∀ w, h.toSesq (v.equivFun.symm y) w = 0 := by
      intro w
      apply hT
      intro a
      have := hy (v.equivFun (a • w))
      rw [traceHerm_apply, LinearEquiv.symm_apply_apply, LinearMap.map_smul, smul_eq_mul] at this
      rw [Algebra.traceForm_apply, mul_comm]
      exact this
    have h0 := HermitianForm.eq_zero_of_toSesq_eq_zero h key
    exact (map_eq_zero_iff _ v.equivFun.symm.injective).1 h0
  · intro z hz
    have key : ∀ w, h.toSesq w (v.equivFun.symm z) = 0 := by
      intro w
      apply hT
      intro a
      have := hz (v.equivFun (conj F E a • w))
      rw [traceHerm_apply, LinearEquiv.symm_apply_apply, LinearMap.map_smulₛₗ₂, smul_eq_mul] at this
      rw [Algebra.traceForm_apply, mul_comm]
      simpa [conj_conj] using this
    have key' : ∀ w, h.toSesq (v.equivFun.symm z) w = 0 := by
      intro w
      have e := (LinearMap.isSymm_def.1 h.isSymm) (v.equivFun.symm z) w
      rw [key w] at e
      exact (map_eq_zero_iff _ (conjHom F E).injective).1 e
    have h0 := HermitianForm.eq_zero_of_toSesq_eq_zero h key'
    exact (map_eq_zero_iff _ v.equivFun.symm.injective).1 h0

end GroundTheory.Heights₂.Heights.FiniteCovolume
end
