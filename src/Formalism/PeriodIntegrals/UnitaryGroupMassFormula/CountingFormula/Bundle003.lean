module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.DensGSDvr
public import Formalism.SharpRestriction.CuspSpanNormBounds.LinQRawRange
public import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001

@[expose] public section

section

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField Formalism.MainNotions.S
open Classical ValuativeRel

section Coord

variable {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
  [TopologicalSpace E] [MeasurableSpace E] {M : Loc.Model F E}
  {V : Type} [AddCommGroup V] [Module E V]

def InP (ϖ : 𝒪[F]) (u : F) : Prop := ∃ o : 𝒪[F], u = (ϖ : F) * o

theorem e_alg (e : E ≃ₐ[F] F × F) (c : F) : e (algebraMap F E c) = (c, c) := by
  first
  | (rw [e.commutes]; rfl)

theorem pi_smulF (e : E ≃ₐ[F] F × F) {n : ℕ} (π : V ≃+ (Fin n → F) × (Fin n → F))
    (hπ : ∀ (a : E) (x : V), π (a • x) = ((e a).1 • (π x).1, (e a).2 • (π x).2)) (c : F) (x : V) :
    π (algebraMap F E c • x) = (c • (π x).1, c • (π x).2) := by
  rw [hπ, e_alg]

theorem mem_smulLat_iff' (H : Loc.HermSp M V) (Λ : Submodule M.L.O V) (c : E) (x : V) :
    x ∈ H.smulLat c Λ ↔ ∃ y ∈ Λ, x = c • y := by
  unfold Loc.HermSp.smulLat
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨y, hy, rfl⟩ := hz
      exact ⟨y, hy, rfl⟩
    | zero => exact ⟨0, Λ.zero_mem, (smul_zero c).symm⟩
    | add z w _ _ hz hw =>
      obtain ⟨y, hy, rfl⟩ := hz
      obtain ⟨y', hy', rfl⟩ := hw
      exact ⟨y + y', Λ.add_mem hy hy', (smul_add c y y').symm⟩
    | smul a z _ hz =>
      obtain ⟨y, hy, rfl⟩ := hz
      refine ⟨a • y, Λ.smul_mem a hy, ?_⟩
      first
      | exact smul_comm a c y
  · rintro ⟨y, hy, rfl⟩
    exact Submodule.subset_span ⟨y, hy, rfl⟩

theorem mem_smulLat_coord (e : E ≃ₐ[F] F × F) (H : Loc.HermSp M V) (Λ : Submodule M.L.O V) {n : ℕ}
    (π : V ≃+ (Fin n → F) × (Fin n → F))
    (hπa : ∀ (a : E) (x : V), π (a • x) = ((e a).1 • (π x).1, (e a).2 • (π x).2))
    (hπL : ∀ x : V, x ∈ Λ ↔ (∀ k, (π x).1 k ∈ 𝒪[F]) ∧ ∀ k, (π x).2 k ∈ 𝒪[F]) (ϖ : 𝒪[F]) (x : V) :
    x ∈ H.smulLat (algebraMap F E ϖ) Λ ↔ (∀ k, InP ϖ ((π x).1 k)) ∧ ∀ k, InP ϖ ((π x).2 k) := by
  rw [mem_smulLat_iff']
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [pi_smulF e π hπa]
    obtain ⟨h1, h2⟩ := (hπL y).1 hy
    exact ⟨fun k => ⟨⟨_, h1 k⟩, by simp [Pi.smul_apply, smul_eq_mul]⟩,
      fun k => ⟨⟨_, h2 k⟩, by simp [Pi.smul_apply, smul_eq_mul]⟩⟩
  · rintro ⟨h1, h2⟩
    choose o1 ho1 using h1
    choose o2 ho2 using h2
    refine ⟨π.symm ((fun k => (o1 k : F)), (fun k => (o2 k : F))), ?_, ?_⟩
    · rw [hπL, AddEquiv.apply_symm_apply]
      exact ⟨fun k => (o1 k).2, fun k => (o2 k).2⟩
    · apply π.injective
      rw [pi_smulF e π hπa, AddEquiv.apply_symm_apply]
      ext k <;> simp [ho1, ho2, Pi.smul_apply, smul_eq_mul]

theorem inP_sub_iff [IsDiscreteValuationRing 𝒪[F]] {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) {u w : F}
    (hu : u ∈ 𝒪[F]) (hw : w ∈ 𝒪[F]) : InP ϖ (u - w) ↔ resF F u = resF F w := by
  have key : ∀ d : 𝒪[F], InP ϖ (d : F) ↔ ϖ ∣ d := by
    intro d
    constructor
    · rintro ⟨o, ho⟩
      exact ⟨o, Subtype.ext (by simp [ho])⟩
    · rintro ⟨o, rfl⟩
      exact ⟨o, by simp⟩
  have e1 : resF F u = IsLocalRing.residue 𝒪[F] ⟨u, hu⟩ := by
    first
    | simp [resF, hu]
  have e2 : resF F w = IsLocalRing.residue 𝒪[F] ⟨w, hw⟩ := by
    first
    | simp [resF, hw]
  have hs : (u - w : F) = ((⟨u, hu⟩ - ⟨w, hw⟩ : 𝒪[F]) : F) := rfl
  have hm : IsLocalRing.maximalIdeal 𝒪[F] = Ideal.span {ϖ} := by
    first
    | exact hϖ.maximalIdeal_eq
  rw [e1, e2, hs, key, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, hm, Ideal.mem_span_singleton]

theorem mk_eq_iff [IsDiscreteValuationRing 𝒪[F]] (e : E ≃ₐ[F] F × F) (H : Loc.HermSp M V)
    (Λ : Submodule M.L.O V) {n : ℕ} (π : V ≃+ (Fin n → F) × (Fin n → F))
    (hπa : ∀ (a : E) (x : V), π (a • x) = ((e a).1 • (π x).1, (e a).2 • (π x).2))
    (hπL : ∀ x : V, x ∈ Λ ↔ (∀ k, (π x).1 k ∈ 𝒪[F]) ∧ ∀ k, (π x).2 k ∈ 𝒪[F]) {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ)
    {x y : V} (hx : x ∈ Λ) (hy : y ∈ Λ) :
    Submodule.Quotient.mk (p := H.smulLat (algebraMap F E ϖ) Λ) x =
        Submodule.Quotient.mk (p := H.smulLat (algebraMap F E ϖ) Λ) y ↔
      (∀ k, resF F ((π x).1 k) = resF F ((π y).1 k)) ∧ ∀ k, resF F ((π x).2 k) = resF F ((π y).2 k) := by
  rw [Submodule.Quotient.eq, mem_smulLat_coord e H Λ π hπa hπL ϖ]
  obtain ⟨hx1, hx2⟩ := (hπL x).1 hx
  obtain ⟨hy1, hy2⟩ := (hπL y).1 hy
  simp only [map_sub, Prod.fst_sub, Prod.snd_sub, Pi.sub_apply]
  exact and_congr (forall_congr' fun k => inP_sub_iff hϖ (hx1 k) (hy1 k))
    (forall_congr' fun k => inP_sub_iff hϖ (hx2 k) (hy2 k))

theorem mem_span_irr_iff (e : E ≃ₐ[F] F × F)
    (hO : ∀ x : E, x ∈ M.L.O ↔ (e x).1 ∈ 𝒪[F] ∧ (e x).2 ∈ 𝒪[F]) (ϖ : 𝒪[F]) (z : E) :
    z ∈ Submodule.span M.L.O {algebraMap F E (ϖ : F)} ↔ InP ϖ (e z).1 ∧ InP ϖ (e z).2 := by
  rw [Submodule.mem_span_singleton]
  constructor
  · rintro ⟨a, rfl⟩
    have ha := (hO a).1 a.2
    refine ⟨⟨⟨(e a).1, ha.1⟩, ?_⟩, ⟨⟨(e a).2, ha.2⟩, ?_⟩⟩ <;>
      simp [Subring.smul_def, Submonoid.smul_def, Subalgebra.smul_def, map_mul, e_alg, mul_comm]
  · rintro ⟨⟨o1, h1⟩, ⟨o2, h2⟩⟩
    have hmem : e.symm ((o1 : F), (o2 : F)) ∈ M.L.O := by
      rw [hO, AlgEquiv.apply_symm_apply]
      exact ⟨o1.2, o2.2⟩
    refine ⟨⟨_, hmem⟩, ?_⟩
    apply e.injective
    ext <;> simp [Subring.smul_def, Submonoid.smul_def, Subalgebra.smul_def, map_mul, e_alg, h1, h2, mul_comm]

theorem resF_bil {n : ℕ} (x y : Fin n → F) (hx : ∀ k, x k ∈ 𝒪[F]) (hy : ∀ k, y k ∈ 𝒪[F])
    (Ph : Matrix (Fin n) (Fin n) 𝒪[F]) :
    resF F (∑ k, ∑ l, x k * (Ph k l : F) * y l) =
      ∑ k, ∑ l, resF F (x k) * IsLocalRing.residue 𝒪[F] (Ph k l) * resF F (y l) := by
  have hc : ∀ (a : F) (ha : a ∈ 𝒪[F]), resF F a = IsLocalRing.residue 𝒪[F] ⟨a, ha⟩ := by
    intro a ha
    first
    | simp [resF, ha]
  have hsum : (∑ k, ∑ l, x k * (Ph k l : F) * y l) =
      ((∑ k, ∑ l, (⟨x k, hx k⟩ : 𝒪[F]) * Ph k l * (⟨y l, hy l⟩ : 𝒪[F]) : 𝒪[F]) : F) := by
    first
    | (push_cast; rfl)
  have hxk : ∀ k, resF F (x k) = IsLocalRing.residue 𝒪[F] ⟨x k, hx k⟩ := fun k => hc _ (hx k)
  have hyl : ∀ l, resF F (y l) = IsLocalRing.residue 𝒪[F] ⟨y l, hy l⟩ := fun l => hc _ (hy l)
  have hc' : ∀ z : 𝒪[F], resF F (z : F) = IsLocalRing.residue 𝒪[F] z := fun z => hc z z.2
  rw [hsum, hc']

  simp only [map_sum, map_mul, hxk, hyl]

theorem bil_mem {n : ℕ} (x y : Fin n → F) (hx : ∀ k, x k ∈ 𝒪[F]) (hy : ∀ k, y k ∈ 𝒪[F])
    (Ph : Matrix (Fin n) (Fin n) 𝒪[F]) : (∑ k, ∑ l, x k * (Ph k l : F) * y l) ∈ 𝒪[F] := by
  exact sum_mem fun k _ => sum_mem fun l _ => mul_mem (mul_mem (hx k) (Ph k l).2) (hy l)

end Coord

end PI.UnitaryGroupMassFormula.CntFormula
end
end

section

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open Formalism.MainNotions.S Polynomial
open ValuativeRel

theorem fl_hensel {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    (hl : IsNonarchimedeanLocalField F) : HenselianRing 𝒪[F] 𝓂[F] := by
  haveI := hl
  letI : UniformSpace F := IsTopologicalAddGroup.rightUniformSpace F
  haveI : IsUniformAddGroup F := isUniformAddGroup_of_addCommGroup
  exact IsAdicComplete.henselianRing _ _

theorem fl_coe_mul {F : Type} [Field F] [ValuativeRel F] (a b : 𝒪[F]) :
    ((a * b : 𝒪[F]) : F) = (a : F) * b := rfl

theorem fl_sq_div {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : Loc.LocE F E) (hl : IsNonarchimedeanLocalField F)
    (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ) (b n : 𝒪[F]) (hbn : b * b = n) (hn : n ∈ 𝓂[F]) :
    ∃ z ∈ L.O, algebraMap F E b = algebraMap F E ϖ * z := by
  haveI := hl
  have hb : b ∈ 𝓂[F] := by
    have h2 : b * b ∈ 𝓂[F] := hbn ▸ hn
    rcases (IsLocalRing.maximalIdeal.isMaximal 𝒪[F]).isPrime.mem_or_mem h2 with h | h <;> exact h
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ, Ideal.mem_span_singleton] at hb
  obtain ⟨c, rfl⟩ := hb
  exact ⟨algebraMap F E c, fl_int_mem L c, by rw [fl_coe_mul, map_mul]⟩

theorem fl_local {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : Loc.LocE F E) (hl : IsNonarchimedeanLocalField F)
    (hE : ∀ x : E, x ≠ 0 → IsUnit x) (hinj : Function.Injective (algebraMap F E))
    (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ) :
    ∀ x ∈ L.O, (¬ ∃ z ∈ L.O, x = algebraMap F E ϖ * z) → ∃ y ∈ L.O, x * y = 1 := by
  intro x hx hnd
  haveI := hl
  obtain ⟨n, hn⟩ := fl_norm L hinj hx
  obtain ⟨t, ht⟩ := fl_trace L hinj hx
  have hquad : x * x = algebraMap F E t * x - algebraMap F E n := by
    rw [ht, hn]; ring
  by_cases hnu : IsUnit n
  · obtain ⟨u, rfl⟩ := hnu
    refine ⟨L.cj x * algebraMap F E ((↑u⁻¹ : 𝒪[F]) : F), mul_mem (fl_cj_mem L hx) (fl_int_mem L _), ?_⟩
    rw [← mul_assoc, ← hn, ← map_mul, ← fl_coe_mul, Units.mul_inv]
    simp
  · exfalso
    have hnm : n ∈ 𝓂[F] := (IsLocalRing.mem_maximalIdeal n).2 hnu
    have hspan := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ
    by_cases htm : t ∈ 𝓂[F]
    · apply hnd
      rw [hspan, Ideal.mem_span_singleton] at htm hnm
      obtain ⟨t', rfl⟩ := htm
      obtain ⟨n', rfl⟩ := hnm
      have hsp : x * x ∈ Submodule.span L.O {algebraMap F E ϖ} := by
        refine Submodule.mem_span_singleton.2 ⟨⟨algebraMap F E t' * x - algebraMap F E n',
          sub_mem (mul_mem (fl_int_mem L t') hx) (fl_int_mem L n')⟩, ?_⟩
        rw [hquad, fl_coe_mul, fl_coe_mul, map_mul, map_mul]
        show (algebraMap F E t' * x - algebraMap F E n') * algebraMap F E ϖ = _
        ring
      obtain ⟨z, hz⟩ := Submodule.mem_span_singleton.1 (L.unram ϖ hϖ x hx hsp)
      exact ⟨z, z.2, by rw [← hz, Subring.smul_def]; exact mul_comm _ _⟩
    · haveI := fl_hensel hl
      haveI := IsLocalRing.maximalIdeal.isMaximal 𝒪[F]
      let f : Polynomial 𝒪[F] := X ^ 2 + (C n - C t * X)
      have hf : f.Monic := by
        refine (monic_X_pow 2).add_of_left ?_
        rw [degree_X_pow]
        refine lt_of_le_of_lt (degree_sub_le _ _) ?_
        exact max_lt (lt_of_le_of_lt degree_C_le (by norm_num))
          (lt_of_le_of_lt (degree_C_mul_X_le t) (by norm_num))
      have h0 : f.eval 0 ∈ 𝓂[F] := by simpa [f] using hnm
      have h1 : IsUnit (Ideal.Quotient.mk 𝓂[F] (f.derivative.eval 0)) := by
        letI := Ideal.Quotient.field 𝓂[F]
        have hne : Ideal.Quotient.mk 𝓂[F] (f.derivative.eval 0) ≠ 0 := by
          rw [Ne, Ideal.Quotient.eq_zero_iff_mem]
          simpa [f, Polynomial.derivative_sub, Polynomial.derivative_mul] using htm
        exact hne.isUnit
      obtain ⟨a, ha, -⟩ := HenselianRing.is_henselian f hf 0 h0 h1
      have hroot : a ^ 2 + (n - t * a) = 0 := by simpa [f, Polynomial.IsRoot] using ha
      have hrootE : algebraMap F E (a : F) ^ 2 + (algebraMap F E (n : F) -
          algebraMap F E (t : F) * algebraMap F E (a : F)) = 0 := by
        have := congrArg (fun r : 𝒪[F] => algebraMap F E (r : F)) hroot
        simpa [map_sub, map_mul, map_pow, map_add (f := _)] using this
      have hfac : (x - algebraMap F E (a : F)) * (x - (algebraMap F E (t : F) - algebraMap F E (a : F))) = 0 := by
        linear_combination hquad - hrootE
      have hxF : ∃ b : 𝒪[F], x = algebraMap F E (b : F) := by
        by_cases hxa : x - algebraMap F E (a : F) = 0
        · exact ⟨a, sub_eq_zero.1 hxa⟩
        · obtain ⟨u, hu⟩ := hE _ hxa
          have : x - (algebraMap F E (t : F) - algebraMap F E (a : F)) = 0 := by
            have h2 := congrArg (fun y => (↑u⁻¹ : E) * y) hfac
            simp only [mul_zero] at h2
            rw [← mul_assoc, ← hu, Units.inv_mul, one_mul] at h2
            exact h2
          refine ⟨t - a, ?_⟩
          rw [sub_eq_zero.1 this]
          simp
      obtain ⟨b, rfl⟩ := hxF
      have hcj : L.cj (algebraMap F E (b : F)) = algebraMap F E (b : F) := L.cj.commutes _
      rw [hcj, ← map_mul, ← fl_coe_mul] at hn
      have hbn : b * b = n := Subtype.val_injective (hinj hn).symm
      exact hnd (fl_sq_div L hl ϖ hϖ b n hbn hnm)

end PI.UnitaryGroupMassFormula.CntFormula
end
end

section

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open Formalism.MainNotions.S Module
open ValuativeRel

theorem flb_int_mem {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : Loc.LocE F E) (a : 𝒪[F]) : algebraMap F E a ∈ L.O := by
  exact (L.O_def _).2 isIntegral_algebraMap

theorem flb_cj_mem {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : Loc.LocE F E) {x : E} (hx : x ∈ L.O) : L.cj x ∈ L.O := by
  exact (L.O_def _).2 (((L.O_def x).1 hx).map ((L.cj : E →ₐ[F] E).restrictScalars 𝒪[F]))

theorem flb_pid {E : Type} [CommRing E] (S : Subring E) (p : E) (hp : p ∈ S)
    (hfac : ∀ x ∈ S, x ≠ 0 → ∃ k : ℕ, ∃ u ∈ S, (∃ w ∈ S, u * w = 1) ∧ x = p ^ k * u) :
    IsPrincipalIdealRing S := by
  classical
  refine ⟨fun I => ?_⟩
  have hget : ∀ x : S, x ∈ I → ∀ (j : ℕ) (u : E), u ∈ S → (∃ w ∈ S, u * w = 1) →
      (x : E) = p ^ j * u → (⟨p, hp⟩ : S) ^ j ∈ I := by
    rintro x hxI j u hu ⟨w, hw, huw⟩ hxe
    have h : (⟨p, hp⟩ : S) ^ j = x * ⟨w, hw⟩ := by
      apply Subtype.ext
      simp only [SubmonoidClass.coe_pow, Subring.coe_mul, hxe]
      rw [mul_assoc, huw, mul_one]
    rw [h]
    exact I.mul_mem_right _ hxI
  by_cases hI : ∃ x ∈ I, x ≠ 0
  · have hex : ∃ k : ℕ, (⟨p, hp⟩ : S) ^ k ∈ I := by
      obtain ⟨x, hxI, hx0⟩ := hI
      obtain ⟨k, u, hu, huw, hxe⟩ := hfac x x.2 (fun h => hx0 (Subtype.ext h))
      exact ⟨k, hget x hxI k u hu huw hxe⟩
    refine ⟨⟨(⟨p, hp⟩ : S) ^ Nat.find hex, ?_⟩⟩
    apply le_antisymm
    · intro x hxI
      by_cases hx0 : x = 0
      · rw [hx0]
        exact Submodule.zero_mem _
      obtain ⟨j, u, hu, huw, hxe⟩ := hfac x x.2 (fun h => hx0 (Subtype.ext h))
      have hkj : Nat.find hex ≤ j := Nat.find_min' hex (hget x hxI j u hu huw hxe)
      rw [Ideal.submodule_span_eq, Ideal.mem_span_singleton']
      refine ⟨(⟨p, hp⟩ : S) ^ (j - Nat.find hex) * ⟨u, hu⟩, ?_⟩
      apply Subtype.ext
      simp only [SubmonoidClass.coe_pow, Subring.coe_mul, hxe]
      rw [mul_comm, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hkj]
    · rw [Ideal.submodule_span_eq, Ideal.span_le, Set.singleton_subset_iff]
      exact Nat.find_spec hex
  · push Not at hI
    refine ⟨⟨0, ?_⟩⟩
    rw [Submodule.span_singleton_eq_bot.mpr rfl]
    exact (Submodule.eq_bot_iff I).mpr hI

section Herm

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

theorem flb_h_add_right {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V]
    (H : Loc.HermSp M V) (x y y' : V) : H.h x (y + y') = H.h x y + H.h x y' := by
  rw [H.h_herm (y + y') x, H.h_add_left, map_add (f := _), ← H.h_herm, ← H.h_herm]

theorem flb_h_smul_right {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V]
    (H : Loc.HermSp M V) (x : V) (a : E) (y : V) : H.h x (a • y) = M.L.cj a * H.h x y := by
  rw [H.h_herm (a • y) x, H.h_smul_left, map_mul, ← H.h_herm]

theorem flb_h_sum_right {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V]
    (H : Loc.HermSp M V) {ι : Type} [Fintype ι] (x : V) (c : ι → E) (v : ι → V) :
    H.h x (∑ i, c i • v i) = ∑ i, M.L.cj (c i) * H.h x (v i) := by
  have hs := map_sum (AddMonoidHom.mk' (H.h x) (flb_h_add_right H x)) (fun i => c i • v i) Finset.univ
  simp only [AddMonoidHom.mk'_apply] at hs
  rw [hs]
  exact Finset.sum_congr rfl fun i _ => flb_h_smul_right H x (c i) (v i)

theorem flb_h_sum_left {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V]
    (H : Loc.HermSp M V) {ι : Type} [Fintype ι] (y : V) (c : ι → E) (v : ι → V) :
    H.h (∑ i, c i • v i) y = ∑ i, c i * H.h (v i) y := by
  have hs := map_sum (AddMonoidHom.mk' (fun z => H.h z y) (fun a b => H.h_add_left a b y))
    (fun i => c i • v i) Finset.univ
  simp only [AddMonoidHom.mk'_apply] at hs
  rw [hs]
  exact Finset.sum_congr rfl fun i _ => H.h_smul_left (c i) (v i) y

end Herm

end PI.UnitaryGroupMassFormula.CntFormula
end
end
