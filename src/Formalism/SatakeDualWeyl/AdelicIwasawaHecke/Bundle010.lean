module

public import Formalism.SatakeDualWeyl.Bundle001
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.GlintPrincRelIndexNeZero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Lemma
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

@[expose] public section

section

open Formalism.UG

noncomputable section

namespace Formalism.UG.P

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem fSatake_nontriv {ϖ : L} {σ : L →+* L} {q : ℕ} (hU : IsUnramInv ϖ σ q) :
    (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).IsNontrivial := by
  obtain ⟨-, -, -, hv, -⟩ := hU
  refine ⟨ϖ, ?_, ?_⟩
  · rw [hv]; exact WithZero.coe_ne_zero
  · rw [hv]
    intro h1
    have := WithZero.coe_injective (h1.trans WithZero.coe_one.symm)
    exact absurd (Multiplicative.ofAdd.injective (this.trans ofAdd_zero.symm)) (by norm_num)

theorem isCommensurated_integral_unitary_of_unramified {ϖ : L} {σ : L →+* L} {q : ℕ} (hU : IsUnramInv ϖ σ q) (n : ℕ) :
    IsCommensurated (KU σ n) := by
  haveI : (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).IsNontrivial :=
    fSatake_nontriv hU
  obtain ⟨-, -, -, hvϖ, -, hq2, hq⟩ := hU
  set A := (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring with hA
  haveI : IsCyclic (WithZero (Multiplicative ℤ))ˣ :=
    isCyclic_of_surjective (WithZero.unitsWithZeroEquiv (α := Multiplicative ℤ)).symm.toMonoidHom
      (MulEquiv.surjective _)
  haveI hD : IsDiscreteValuationRing ↥A.toSubring := Valuation.valuationSubring_isDiscreteValuationRing _
  have hRes : Finite (IsLocalRing.ResidueField ↥A.toSubring) := by
    apply Nat.finite_of_card_ne_zero
    rw [show Nat.card (IsLocalRing.ResidueField ↥A.toSubring) = q ^ 2 from hq]
    exact pow_ne_zero 2 (by omega)
  intro g
  obtain ⟨c, hc0, hg1, hg2⟩ := Formalism.UG.P.glint_exists_denom A (g : GL (Fin n) L)
  haveI : Finite (↥A.toSubring ⧸ Ideal.span {c * c}) :=
    glint_finite_quotient_of_dvr hRes _ (by
      rw [Ne, Ideal.span_singleton_eq_bot]
      exact mul_ne_zero hc0 hc0)
  have hO : intL L = A.toSubring := rfl
  unfold KU
  rw [hO]
  have hK : intPts A.toSubring.subtype (GU σ n) = GU σ n ⊓ (bc (n := Fin n) A.toSubring.subtype).range := rfl
  rw [hK]
  have hmap : ((GU σ n ⊓ (bc (n := Fin n) A.toSubring.subtype).range).subgroupOf (GU σ n)).map (MulAut.conj g).toMonoidHom =
      ((GU σ n ⊓ (bc (n := Fin n) A.toSubring.subtype).range).map (MulAut.conj (g : GL (Fin n) L)).toMonoidHom).subgroupOf (GU σ n) := by
    ext x
    simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, by simp⟩
    · rintro ⟨y, hy, hyx⟩
      exact ⟨⟨y, hy.1⟩, hy, Subtype.ext (by simpa using hyx)⟩
  rw [hmap, Subgroup.relIndex_subgroupOf inf_le_left]
  have hPB := glint_princ_relIndex_ne_zero (n := Fin n) A.toSubring (Ideal.span {c * c})
  have h1 : (princ (n := Fin n) A.toSubring.subtype (Ideal.span {c * c}) ⊓ GU σ n).relIndex
      (GU σ n ⊓ (bc (n := Fin n) A.toSubring.subtype).range) ≠ 0 := by
    rw [inf_comm (GU σ n) (bc (n := Fin n) A.toSubring.subtype).range]
    exact Subgroup.relIndex_inter_ne_zero hPB (GU σ n)
  have hle : princ (n := Fin n) A.toSubring.subtype (Ideal.span {c * c}) ⊓ GU σ n ≤
      (GU σ n ⊓ (bc (n := Fin n) A.toSubring.subtype).range).map (MulAut.conj (g : GL (Fin n) L)).toMonoidHom := by
    rintro h ⟨hP, hHh⟩
    obtain ⟨b, hb, hbh⟩ := glint_princ_le_map_conj A.toSubring (g : GL (Fin n) L) c hg1 hg2 hP
    refine ⟨b, ⟨?_, hb⟩, hbh⟩
    have hbe : b = (g : GL (Fin n) L)⁻¹ * h * g := by
      rw [← hbh]
      simp [MulAut.conj_apply, mul_assoc]
    rw [hbe]
    exact (GU σ n).mul_mem ((GU σ n).mul_mem ((GU σ n).inv_mem g.2) hHh) g.2
  exact fun hz => h1 (Subgroup.relIndex_eq_zero_of_le_left hle hz)

theorem fSatake_v_eq {x : L} (hx : x ≠ 0) :
    Valued.v x = ((Multiplicative.ofAdd (-ordL x) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
  have h : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  unfold ordL
  rw [dite_eq_right h, neg_neg, ofAdd_toAdd, WithZero.coe_unzero]

private lemma ordL_eq_of_valuation_eq {x : L} (hx : x ≠ 0) {k : ℤ}
    (h : Valued.v x = ((Multiplicative.ofAdd (-k) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) :
    ordL x = k := by
  rw [fSatake_v_eq hx] at h
  have h2 := WithZero.coe_injective h
  have h3 := Multiplicative.ofAdd.injective h2
  linarith

theorem fSatake_ord_mul {x y : L} (hx : x ≠ 0) (hy : y ≠ 0) : ordL (x * y) = ordL x + ordL y := by
  apply ordL_eq_of_valuation_eq (mul_ne_zero hx hy)
  rw [map_mul, fSatake_v_eq hx, fSatake_v_eq hy, ← WithZero.coe_mul, ← ofAdd_add, neg_add]

theorem fSatake_ord_one : ordL (1 : L) = 0 := by
  apply ordL_eq_of_valuation_eq one_ne_zero
  simp

theorem fSatake_ord_of_v {x y : L} (h : Valued.v x = Valued.v y) : ordL x = ordL y := by
  unfold ordL
  simp only [h]

theorem fSatake_ord_zpow {ϖ : L}
    (hϖ : Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))
    (k : ℤ) : ordL (ϖ ^ k) = k := by
  have h0 : ϖ ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hϖ
    exact WithZero.zero_ne_coe hϖ
  apply ordL_eq_of_valuation_eq (zpow_ne_zero k h0)
  rw [map_zpow₀, hϖ, ← WithZero.coe_zpow, ← ofAdd_zsmul]
  congr 2
  simp

theorem fSatake_ord_nonneg {x : L} (hx : x ≠ 0) (hO : x ∈ intL L) : 0 ≤ ordL x := by
  have h1 : Valued.v x ≤ 1 := hO
  rw [fSatake_v_eq hx, ← WithZero.coe_one, WithZero.coe_le_coe, ← ofAdd_zero,
    Multiplicative.ofAdd_le] at h1
  linarith

end Formalism.UG.P
end
end

section

noncomputable section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

namespace Formalism.UG.P

open Formalism.UG

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem satake_unif_ne_zero {ϖ : v.adicCompletion F} (h : IsUnifV F v ϖ) : ϖ ≠ 0 := by
  intro h0
  subst h0
  unfold IsUnifV at h
  first | simp at h | done

theorem satake_lt_one_le {x : WithZero (Multiplicative ℤ)} (hx : x < 1) :
    x ≤ ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
  cases x using WithZero.recZeroCoe with
  | zero => exact WithZero.zero_le _
  | coe a =>
    have h1 : a < 1 := by exact_mod_cast hx
    have h2 : a ≤ Multiplicative.ofAdd (-1 : ℤ) := by
      change Multiplicative.toAdd a ≤ -1
      have h3 : Multiplicative.toAdd a < 0 := h1
      omega
    exact WithZero.coe_le_coe.mpr h2

private theorem mem_Ov_iff' (x : v.adicCompletion F) : x ∈ Ov F v ↔ Valued.v x ≤ 1 := by
  unfold Ov
  first
    | exact Iff.rfl
    | exact mem_adicCompletionIntegers
    | simp [mem_adicCompletionIntegers]

theorem satake_unif_inv_not_mem {ϖ : v.adicCompletion F} (h : IsUnifV F v ϖ) : ϖ⁻¹ ∉ Ov F v := by
  unfold IsUnifV at h
  intro hm
  have hm' : Valued.v ϖ⁻¹ ≤ 1 := (mem_Ov_iff' v _).mp hm
  rw [map_inv₀, h] at hm'
  have h4 : ((Multiplicative.ofAdd (-1 : ℤ))⁻¹ : Multiplicative ℤ) ≤ 1 := by
    rw [← WithZero.coe_le_coe, WithZero.coe_inv]
    first | exact_mod_cast hm' | simpa using hm'
  have h5 : Multiplicative.toAdd ((Multiplicative.ofAdd (-1 : ℤ))⁻¹) ≤ Multiplicative.toAdd (1 : Multiplicative ℤ) := h4
  simp at h5

theorem satake_mem_span_iff {ϖ : v.adicCompletion F} (hϖ : ϖ ∈ Ov F v) (h : IsUnifV F v ϖ)
    (y : Ov F v) : y ∈ Ideal.span {(⟨ϖ, hϖ⟩ : Ov F v)} ↔ Valued.v (y : v.adicCompletion F) < 1 := by
  have h0 := satake_unif_ne_zero v h
  rw [Ideal.mem_span_singleton']
  constructor
  · rintro ⟨z, rfl⟩
    have hz : Valued.v ((z : Ov F v) : v.adicCompletion F) ≤ 1 := z.2
    show Valued.v ((z : v.adicCompletion F) * ϖ) < 1
    rw [Valuation.map_mul, h]
    calc Valued.v (z : v.adicCompletion F) * ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))
        ≤ 1 * ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) :=
          by gcongr
      _ < 1 := by
          rw [one_mul, ← WithZero.coe_one, WithZero.coe_lt_coe]
          show (-1 : ℤ) < 0
          omega
  · intro hy
    have hle := satake_lt_one_le hy
    have hm : (y : v.adicCompletion F) * ϖ⁻¹ ∈ Ov F v := by
      show Valued.v ((y : v.adicCompletion F) * ϖ⁻¹) ≤ 1
      rw [Valuation.map_mul, Valuation.map_inv, h]
      calc Valued.v (y : v.adicCompletion F) * (((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))⁻¹
          ≤ ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) *
              (((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))⁻¹ :=
            by gcongr
        _ = 1 := mul_inv_cancel₀ WithZero.coe_ne_zero
    refine ⟨⟨_, hm⟩, Subtype.ext ?_⟩
    show (y : v.adicCompletion F) * ϖ⁻¹ * ϖ = y
    field_simp

def satakeIota : 𝓞 F →+* Ov F v := algebraMap (𝓞 F) (v.adicCompletionIntegers F)

theorem satakeIota_coe (r : 𝓞 F) :
    ((satakeIota v r : Ov F v) : v.adicCompletion F) = algebraMap (𝓞 F) (v.adicCompletion F) r := by first | rfl | simp [satakeIota] | (unfold satakeIota Ov; done)

theorem satake_card_res {ϖ : v.adicCompletion F} (hϖ : ϖ ∈ Ov F v) (h : IsUnifV F v ϖ) :
    Nat.card (Ov F v ⧸ Ideal.span {(⟨ϖ, hϖ⟩ : Ov F v)}) = qV F v := by
  set I := Ideal.span {(⟨ϖ, hϖ⟩ : Ov F v)}
  let φ : 𝓞 F →+* Ov F v ⧸ I := (Ideal.Quotient.mk I).comp (satakeIota v)
  have hker : ∀ r ∈ v.asIdeal, φ r = 0 := by
    intro r hr
    simp only [φ, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
    rw [satake_mem_span_iff v hϖ h]
    unfold satakeIota
    rw [algebraMap_adicCompletionIntegers_apply, adicCompletion.valued_coe (K := F) (v := v),
      valuation_of_algebraMap]
    exact (intValuation_lt_one_iff_mem v r).2 hr
  have := v.isMaximal
  let _ := Ideal.Quotient.field v.asIdeal
  let ψ := Ideal.Quotient.lift v.asIdeal φ hker
  have hne : I ≠ ⊤ := by
    intro htop
    have h1 : (1 : Ov F v) ∈ I := htop ▸ Submodule.mem_top
    rw [satake_mem_span_iff v hϖ h] at h1
    simp at h1
  have : Nontrivial (Ov F v ⧸ I) := Ideal.Quotient.nontrivial_iff.2 hne
  have hinj : Function.Injective ψ := RingHom.injective ψ
  have hsurj : Function.Surjective ψ := by
    intro y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨r, hr⟩ := glint_exists_approx v x
    refine ⟨Ideal.Quotient.mk _ r, ?_⟩
    show φ r = _
    simp only [φ, RingHom.comp_apply]
    rw [Ideal.Quotient.eq, satake_mem_span_iff v hϖ h]
    have e : ((satakeIota v r - x : Ov F v) : v.adicCompletion F) =
        -((x : v.adicCompletion F) - algebraMap (𝓞 F) (v.adicCompletion F) r) := by
      rw [AddSubgroupClass.coe_sub, satakeIota_coe, neg_sub]
    rw [e, Valuation.map_neg]
    exact hr
  rw [← Nat.card_congr (Equiv.ofBijective ψ ⟨hinj, hsurj⟩)]
  unfold qV
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]

theorem satake_ordV_unif {ϖ : v.adicCompletion F} (h : IsUnifV F v ϖ) : ordV F v ϖ = 1 := by
  unfold ordV IsUnifV at *
  have h0 : Valued.v ϖ ≠ 0 := by rw [h]; exact WithZero.coe_ne_zero
  rw [dite_eq_right h0]
  have e : ((WithZero.unzero h0 : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) =
      ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
    rw [WithZero.coe_unzero, h]
  rw [WithZero.coe_injective e]
  simp

theorem satake_ordV_one : ordV F v 1 = 0 := by
  unfold ordV
  have h0 : Valued.v (1 : v.adicCompletion F) ≠ 0 := by simp
  rw [dite_eq_right h0]
  have e : ((WithZero.unzero h0 : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) =
      ((1 : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
    rw [WithZero.coe_unzero, map_one, WithZero.coe_one]
  rw [WithZero.coe_injective e]
  simp

theorem satake_two_le_qV : 2 ≤ qV F v := by
  unfold qV
  have h1 : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  have h2 : Ideal.absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top
  omega

end Formalism.UG.P
end
end
