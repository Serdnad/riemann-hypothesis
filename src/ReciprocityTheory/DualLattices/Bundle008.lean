module

public import ReciprocityTheory.DualLattices.Bundle002
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Valuation.Integers
public import Mathlib.NumberTheory.ModularForms.Discriminant
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
public import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
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
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.NumberTheory.ModularForms.CuspFormSubmodule
public import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula

@[expose] public section

section

noncomputable section

open Finset

namespace ReciprocityTheory.PGsh.L2

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
  {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]

def HopfOrder.ofSpan (S : Set (N → C)) (hlat : IsLat R (Submodule.span R S))
    (hint : S ⊆ (intFun (C := C) R N : Set (N → C))) (h1 : (1 : N → C) ∈ Submodule.span R S)
    (hmul : ∀ a ∈ S, ∀ b ∈ S, a * b ∈ Submodule.span R S)
    (hcomul : ∀ a ∈ S, addPull R N a ∈ tensorSpan R (Submodule.span R S))
    (hanti : ∀ a ∈ S, (fun x => a (-x)) ∈ Submodule.span R S) : HopfOrder (C := C) R N where
  carrier := Submodule.span R S
  lat := hlat
  le_int := Submodule.span_le.mpr hint
  one_mem := h1
  mul_mem f g hf hg := by
    have h := Submodule.mul_mem_mul hf hg
    rw [Submodule.span_mul_span] at h
    refine (Submodule.span_le.mpr ?_) h
    rintro x ⟨a, ha, b, hb, rfl⟩
    exact hmul a ha b hb
  comul f hf := by
    have : Submodule.span R S ≤
        (tensorSpan R (Submodule.span R S)).comap (addPull R N) :=
      Submodule.span_le.mpr hcomul
    exact this hf
  antipode f hf := by
    have : Submodule.span R S ≤
        (Submodule.span R S).comap (LinearMap.funLeft R C (fun x : N => -x)) :=
      Submodule.span_le.mpr hanti
    exact this hf

def constOrder : HopfOrder (C := C) R N :=
  HopfOrder.ofSpan (Set.range fun a : N => (Pi.single a (1 : C) : N → C))
    ⟨1, by simp, by
      congr 1
      ext f
      simp only [Set.mem_range]
      constructor
      · rintro ⟨a, rfl⟩; exact ⟨a, by ext x; simp [Matrix.one_apply, Pi.single_apply]⟩
      · rintro ⟨a, rfl⟩; exact ⟨a, by ext x; simp [Matrix.one_apply, Pi.single_apply]⟩⟩
    (by
      rintro f ⟨a, rfl⟩ x
      by_cases h : x = a
      · exact ⟨1, by simp [h]⟩
      · exact ⟨0, by simp [h]⟩)
    (by
      have : (1 : N → C) = ∑ a, (Pi.single a (1 : C) : N → C) := by
        ext x; simp [Pi.single_apply]
      rw [this]
      exact Submodule.sum_mem _ fun a _ => Submodule.subset_span ⟨a, rfl⟩)
    (by
      rintro f ⟨a, rfl⟩ g ⟨b, rfl⟩
      have : (Pi.single a (1 : C) : N → C) * Pi.single b 1 =
          (if a = b then (1 : R) else 0) • (Pi.single a (1 : C) : N → C) := by
        ext x; by_cases h : a = b <;> by_cases hx : x = a <;> simp_all [Pi.single_apply]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩))
    (by
      rintro f ⟨c, rfl⟩
      have : addPull R N (Pi.single c (1 : C) : N → C) =
          ∑ a, fun p : N × N => (Pi.single a (1 : C) : N → C) p.1 *
            (Pi.single (c - a) (1 : C) : N → C) p.2 := by
        ext ⟨x, y⟩
        simp only [addPull, LinearMap.funLeft_apply, Finset.sum_apply, Pi.single_apply,
          ite_mul, one_mul, zero_mul]
        by_cases h : x + y = c
        · have : y = c - x := by rw [← h]; abel
          simp [this]
        · have : ¬ y = c - x := by intro hy; apply h; rw [hy]; abel
          simp [h, this]
      rw [this]
      refine Submodule.sum_mem _ fun a _ => Submodule.subset_span ?_
      exact ⟨_, Submodule.subset_span ⟨a, rfl⟩, _, Submodule.subset_span ⟨c - a, rfl⟩, rfl⟩)
    (by
      rintro f ⟨a, rfl⟩
      refine Submodule.subset_span ⟨-a, ?_⟩
      ext x; simp [Pi.single_apply, neg_eq_iff_eq_neg])

def negChar (ψ : AddChar N C) : AddChar N C where
  toFun x := ψ (-x)
  map_zero_eq_one' := by simp
  map_add_eq_mul' a b := by rw [neg_add, AddChar.map_add_eq_mul]

def multOrder (v : Valuation C NNReal) (hv : v.Integers R) (e : N ≃ AddChar N C)
    (hB : IsUnit (Matrix.of fun x j : N => e j x).det) : HopfOrder (C := C) R N :=
  HopfOrder.ofSpan (Set.range fun j : N => ((e j : AddChar N C) : N → C))
    ⟨_, hB, by simp [Matrix.of_apply]⟩
    (by
      rintro f ⟨j, rfl⟩ x
      refine hv.exists_of_le_one ?_
      have hn : (e j x) ^ Fintype.card N = 1 := by
        rw [← AddChar.map_nsmul_eq_pow, card_nsmul_eq_zero, AddChar.map_zero_eq_one]
      have : v (e j x) ^ Fintype.card N ≤ 1 := by rw [← map_pow, hn, map_one]
      exact (pow_le_one_iff_of_nonneg (by positivity) Fintype.card_ne_zero).mp this)
    (Submodule.subset_span ⟨e.symm 1, by simp⟩)
    (by
      rintro f ⟨a, rfl⟩ g ⟨b, rfl⟩
      exact Submodule.subset_span ⟨e.symm (e a * e b), by simp⟩)
    (by
      rintro f ⟨j, rfl⟩
      refine Submodule.subset_span ⟨_, Submodule.subset_span ⟨j, rfl⟩, _,
        Submodule.subset_span ⟨j, rfl⟩, ?_⟩
      ext p; simp [addPull, AddChar.map_add_eq_mul])
    (by
      rintro f ⟨j, rfl⟩
      exact Submodule.subset_span ⟨e.symm (negChar (e j)), by ext x; simp [negChar]⟩)

theorem charTable_isUnit (e : N ≃ AddChar N C) : IsUnit (Matrix.of fun x j : N => e j x).det := by
  rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.linearIndependent_cols_iff_isUnit]
  have hinj : Function.Injective fun j : N => (e j).toMonoidHom := fun a b hab =>
    e.injective (DFunLike.ext _ _ fun x => DFunLike.congr_fun hab (Multiplicative.ofAdd x))
  exact (linearIndependent_monoidHom (Multiplicative N) C).comp _ hinj

def multOrder' (v : Valuation C NNReal) (hv : v.Integers R) (e : N ≃ AddChar N C) :
    HopfOrder (C := C) R N :=
  multOrder v hv e (charTable_isUnit e)

end ReciprocityTheory.PGsh.L2
end
end

section

noncomputable section

namespace ReciprocityTheory.PGsh.L2

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]

def DualHopfOrderStatement : Prop :=
  ∀ (v : Valuation C NNReal), v.Integers R →
  ∀ (N H : Type) [AddCommGroup N] [Fintype N] [DecidableEq N] [AddCommGroup H] [Fintype H]
    [DecidableEq H] (e : H ≃ AddChar N C), (∀ h h', e (h + h') = e h * e h') →
    Fintype.card H = Fintype.card N →
    ∀ AA : HopfOrder (C := C) R N,
      ∃ AD : HopfOrder (C := C) R H,
        AD.carrier = (dualLat AA.carrier).map (fourier (R := R) fun h a => e h a) ∧
        (dualLat AD.carrier).map (fourier (R := R) fun a h => e h a) = AA.carrier ∧
        ∀ c c', HasColen R v AA.carrier c → HasColen R v AD.carrier c' →
          (c * c') ^ 2 = v (Fintype.card N : C) ^ Fintype.card N

end ReciprocityTheory.PGsh.L2
end
end

section

noncomputable section

namespace ReciprocityTheory.PGsh.L2

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]

def SubgroupFreenessStatement : Prop :=
  IsAlgClosed C → CharZero C →
  ∀ (v : Valuation C NNReal), v.Integers R →
  ∀ (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N] (K : AddSubgroup N)
    [DecidablePred (· ∈ K)] [DecidableEq (N ⧸ K)] [Fintype (N ⧸ K)]
    (AA : HopfOrder (C := C) R N),
    let B := AA.carrier.comap (pullQ (R := R) K)
    let AK := AA.carrier.map (resK (R := R) K)
    let IK := (augIdeal B).map (pullQ K)
    (∃ f : K → N → C, (∀ j, f j ∈ AA.carrier) ∧ ∀ g ∈ AA.carrier,
      ∃! b : K → N → C, (∀ j, b j ∈ B.map (pullQ K)) ∧ g = ∑ j, b j * f j) ∧
    (∀ g ∈ AA.carrier, resK (R := R) K g = 0 → g ∈ IK * AA.carrier) ∧
    (∀ c cB cK, HasColen R v AA.carrier c → HasColen R v B cB → HasColen R v AK cK →
      c = cB ^ Fintype.card K * cK ^ Fintype.card (N ⧸ K)) ∧
    (∀ g ∈ augIdeal AA.carrier, resK (R := R) K g ∈ augIdeal AK * augIdeal AK →
      g ∈ IK ⊔ augIdeal AA.carrier * augIdeal AA.carrier)

end ReciprocityTheory.PGsh.L2
end
end

section

namespace ReciprocityTheory.PGsh

open UpperHalfPlane hiding I
open Complex ModularForm ModularFormClass MatrixGroups EisensteinSeries

def monoIdx (w : ℕ) : Finset ℕ :=
  (Finset.range (w + 1)).filter fun a => 4 * a ≤ w ∧ 6 ∣ w - 4 * a

def monoB (w a : ℕ) : ℕ := (w - 4 * a) / 6

theorem monoIdx_wt {w a : ℕ} (h : a ∈ monoIdx w) : 4 * a + 6 * monoB w a = w := by
  simp only [monoIdx, Finset.mem_filter, Finset.mem_range] at h
  obtain ⟨_, h1, h2⟩ := h
  unfold monoB
  omega

noncomputable def monoW (w a : ℕ) : ModularForm 𝒮ℒ (w : ℤ) :=
  if h : 4 * a + 6 * monoB w a = w then
    ModularForm.mcast (by omega) ((E₄.pow a).mul (E₆.pow (monoB w a)))
  else 0

theorem coe_monoW {w a : ℕ} (h : a ∈ monoIdx w) :
    (⇑(monoW w a) : ℍ → ℂ) = (⇑E₄) ^ a * (⇑E₆) ^ monoB w a := by
  simp [monoW, monoIdx_wt h]

theorem qExpansion_monoW {w a : ℕ} (h : a ∈ monoIdx w) :
    qExpansion 1 (monoW w a) =
      PowerSeries.map (Int.castRingHom ℂ) (e4Z ^ a * e6Z ^ monoB w a) := by
  simp only [monoW, monoIdx_wt h, dite_true, ModularForm.qExpansion_mcast]
  rw [ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_SL,
    ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL,
    ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL, qExpansion_E₄_eq,
    qExpansion_E₆_eq, map_mul, map_pow, map_pow]

theorem qExpansion_monoW_coeff_zero {w a : ℕ} (h : a ∈ monoIdx w) :
    (qExpansion 1 (monoW w a)).coeff 0 = 1 := by
  have h4 : PowerSeries.constantCoeff e4Z = 1 := by simp [e4Z]
  have h6 : PowerSeries.constantCoeff e6Z = 1 := by simp [e6Z]
  rw [qExpansion_monoW h, PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff_apply,
    map_mul, map_pow, map_pow, h4, h6]
  simp

theorem monoIdx_nonempty {w : ℕ} (he : Even w) (h2 : w ≠ 2) : ∃ a, a ∈ monoIdx w := by
  obtain ⟨m, rfl⟩ := he
  simp only [monoIdx, Finset.mem_filter, Finset.mem_range]
  by_cases h : m % 2 = 0
  · exact ⟨(m + m) / 4, by omega, by omega, ⟨0, by omega⟩⟩
  · exact ⟨(m + m - 6) / 4, by omega, by omega, ⟨1, by omega⟩⟩

noncomputable def monoSpanF (w : ℕ) : Submodule ℂ (ℍ → ℂ) :=
  Submodule.span ℂ (Set.range fun a : monoIdx w => (⇑(monoW w a) : ℍ → ℂ))

theorem mono_mem_monoSpanF {w a : ℕ} (h : a ∈ monoIdx w) : (⇑(monoW w a) : ℍ → ℂ) ∈ monoSpanF w :=
  Submodule.subset_span ⟨⟨a, h⟩, rfl⟩

theorem mulDisc_mem {w : ℕ} (hw : 12 ≤ w) {φ : ℍ → ℂ} (hφ : φ ∈ monoSpanF (w - 12)) :
    (ModularForm.discriminant : ℍ → ℂ) * φ ∈ monoSpanF w := by
  induction hφ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨a, ha⟩, rfl⟩ := hx
    have hwt := monoIdx_wt ha
    have ha3 : a + 3 ∈ monoIdx w := by
      simp only [monoIdx, Finset.mem_filter, Finset.mem_range]
      refine ⟨by omega, by omega, ⟨monoB (w - 12) a, by omega⟩⟩
    have ha0 : a ∈ monoIdx w := by
      simp only [monoIdx, Finset.mem_filter, Finset.mem_range]
      refine ⟨by omega, by omega, ⟨monoB (w - 12) a + 2, by omega⟩⟩
    have hb3 : monoB w (a + 3) = monoB (w - 12) a := by
      have := monoIdx_wt ha3; omega
    have hb0 : monoB w a = monoB (w - 12) a + 2 := by
      have := monoIdx_wt ha0; omega
    have heq : (ModularForm.discriminant : ℍ → ℂ) * ⇑(monoW (w - 12) a) =
        (1728 : ℂ)⁻¹ • ((⇑(monoW w (a + 3)) : ℍ → ℂ) - ⇑(monoW w a)) := by
      rw [coe_monoW ha, coe_monoW ha3, coe_monoW ha0, hb3, hb0]
      funext z
      simp only [Pi.mul_apply, Pi.pow_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
        ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq]
      ring
    rw [heq]
    exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (mono_mem_monoSpanF ha3)
      (mono_mem_monoSpanF ha0))
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hx

theorem coe_mem_monoSpanF (w : ℕ) (f : ModularForm 𝒮ℒ (w : ℤ)) : (⇑f : ℍ → ℂ) ∈ monoSpanF w := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
  rcases Nat.even_or_odd w with he | ho
  · by_cases h2 : w = 2
    · subst h2
      have : f = 0 := rank_zero_iff_forall_zero.mp ModularForm.levelOne_weight_two_rank_zero f
      subst this
      simp
    obtain ⟨a, ha⟩ := monoIdx_nonempty he h2
    set g := f - (qExpansion 1 f).coeff 0 • monoW w a with hg
    have hgc : (qExpansion 1 g).coeff 0 = 0 :=
      (ModularForm.isCuspForm_iff_coeffZero_eq_zero g).mp
        (ModularForm.sub_smul_isCuspForm f _ (qExpansion_monoW_coeff_zero ha))
    have hfg : (⇑f : ℍ → ℂ) = ⇑g + (qExpansion 1 f).coeff 0 • ⇑(monoW w a) := by
      rw [hg]; simp
    rw [hfg]
    refine Submodule.add_mem _ ?_ (Submodule.smul_mem _ _ (mono_mem_monoSpanF ha))
    by_cases h12 : w < 12
    · have h0 : ModularForm.toCuspForm g hgc = 0 :=
        rank_zero_iff_forall_zero.mp (CuspForm.rank_eq_zero_of_weight_lt_twelve (by omega)) _
      have : (⇑g : ℍ → ℂ) = 0 := by
        funext z
        have := congrArg (fun F : CuspForm 𝒮ℒ (w : ℤ) => F z) h0
        simpa using this
      rw [this]; exact Submodule.zero_mem _
    · replace h12 : 12 ≤ w := by omega
      set h := CuspForm.discriminantEquiv (ModularForm.toCuspForm g hgc) with hh
      have hmem := ih (w - 12) (by omega) (ModularForm.mcast (by omega) h)
      have hgd : (⇑g : ℍ → ℂ) = (ModularForm.discriminant : ℍ → ℂ) * ⇑h := by
        have := ModularForm.discriminant_mul_discriminantEquiv (ModularForm.toCuspForm g hgc)
        rw [hh, this]; rfl
      rw [hgd]
      exact mulDisc_mem h12 hmem
  · have : f = 0 := ModularForm.levelOne_odd_weight_eq_zero (by exact_mod_cast ho.natCast) f
    subst this
    simp

end ReciprocityTheory.PGsh
end

section

noncomputable section

namespace ReciprocityTheory.PGsh.L2

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]

def SubgroupQuotientStatement : Prop :=
  ∀ (v : Valuation C NNReal), v.Integers R →
  ∀ (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N] (K : AddSubgroup N)
    [DecidablePred (· ∈ K)] [DecidableEq (N ⧸ K)] [Fintype (N ⧸ K)]
    (AA : HopfOrder (C := C) R N),
    (∃ AK : HopfOrder (C := C) R K, AK.carrier = AA.carrier.map (resK K)) ∧
    (∃ AQ : HopfOrder (C := C) R (N ⧸ K), AQ.carrier = AA.carrier.comap (pullQ K)) ∧
    dualLat (AA.carrier.map (resK (R := R) K)) = (dualLat AA.carrier).comap (extK K) ∧
    dualLat (AA.carrier.comap (pullQ (R := R) K)) = (dualLat AA.carrier).map (pushQ K)

end ReciprocityTheory.PGsh.L2
end
end
