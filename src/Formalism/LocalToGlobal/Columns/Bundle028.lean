module

public import Formalism.LocalToGlobal.Columns.Bundle018
public import Formalism.LocalToGlobal.Columns.TwQLevU
public import Formalism.LocalToGlobal.Columns.Bundle025
public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Formalism.LocalToGlobal.Columns.ChainInst
public import Formalism.LocalToGlobal.Columns.Bundle027
import Formalism.LocalToGlobal.Columns.Bundle021
import Formalism.LocalToGlobal.Columns.QthExistsBound
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open NumberField IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.UG Formalism.UG.P Formalism.L2.DIV

section Bridge

variable {F E K : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] [Field K]
  (hc : Formalism.BasicNotions.CMData F E) {n : ℕ} [NeZero n] {Q : Finset (Pl E)} (Θ : LevQFam E K n Q)
  (hQ : ∀ P : Q, conjPrime₂ P.1 ≠ P.1) (hΘ : ThetaOpen Θ)

def qbPi (P : Q) : 𝓞 E := Classical.choose (qsp_exists hc P.1 (hQ P))

theorem qbPi_spec (P : Q) : qbPi hc hQ P ∈ P.1.asIdeal ∧ cO E (qbPi hc hQ P) ∉ P.1.asIdeal ∧
    Nonempty (Formalism.MainNotions.Gaps.LG.SplitAt hc.sig (underPl F P.1) ((qbPi hc hQ P : 𝓞 E) : E)) :=
  Classical.choose_spec (qsp_exists hc P.1 (hQ P))

def qbSp (P : Q) : Formalism.MainNotions.Gaps.LG.SplitAt hc.sig (underPl F P.1) ((qbPi hc hQ P : 𝓞 E) : E) :=
  Classical.choice (qbPi_spec hc hQ P).2.2

def qbN (P : Q) : ℕ := Classical.choose (hΘ P)

theorem qbN_spec (P : Q) : 0 < qbN Θ hΘ P ∧ ∀ g : ↥(GLint E n P.1), lqPrinc P.1 (qbN Θ hΘ P) (g : Sp E n ≃ₗ[E] Sp E n) →
    ∃ h : g ∈ (Θ P).H, (Θ P).lam ⟨g, h⟩ = 1 :=
  Classical.choose_spec (hΘ P)

abbrev qbD (P : Q) : E := ((qbPi hc hQ P : 𝓞 E) : E) ^ qbN Θ hΘ P

theorem qbPi_ne (P : Q) : qbPi hc hQ P ≠ 0 := fun h => (qbPi_spec hc hQ P).2.1 (by rw [h, map_zero]; exact zero_mem _)

theorem qbD_ne (P : Q) : qbD hc Θ hQ hΘ P ≠ 0 :=
  pow_ne_zero _ (fun h => qbPi_ne hc hQ P (by exact_mod_cast h))

theorem qbD_val (P : Q) : P.1.valuation E (qbD hc Θ hQ hΘ P) ≤ WithZero.exp (-(qbN Θ hΘ P : ℤ)) := by
  have h1 : qbPi hc hQ P ^ qbN Θ hΘ P ∈ P.1.asIdeal ^ qbN Θ hΘ P := Ideal.pow_mem_pow (qbPi_spec hc hQ P).1 _
  have := (P.1.intValuation_le_pow_iff_mem _ _).2 h1
  rw [← HeightOneSpectrum.valuation_of_algebraMap (K := E)] at this
  simpa using this

abbrev qbF (P : Q) : E →+* (qv F P.1).adicCompletion F := qbPhi hc P.1 (qbPi hc hQ P) (qbSp hc hQ P)

theorem qbF_int (P : Q) (r : 𝓞 E) : Valued.v (qbF hc hQ P (algebraMap (𝓞 E) E r)) ≤ 1 :=
  phi_integral_valuation_le_one hc P.1 _ (qbSp hc hQ P) r

theorem qbF_P (P : Q) (r : 𝓞 E) : Valued.v (qbF hc hQ P (algebraMap (𝓞 E) E r)) < 1 ↔ r ∈ P.1.asIdeal :=
  qsp_sp_P hc P.1 _ (qbPi_spec hc hQ P).1 (qbPi_spec hc hQ P).2.1 (qbSp hc hQ P) r

theorem qbK_mono {v : HeightOneSpectrum (𝓞 F)} {c w : v.adicCompletion F} (hw : w ∈ v.adicCompletionIntegers F)
    {x : GL (Fin n) (v.adicCompletion F)} (hx : x ∈ qbK (c * w)) : x ∈ qbK c := by
  refine ⟨hx.1, hx.2.1, fun i j => ?_⟩
  obtain ⟨z, hz, e⟩ := hx.2.2 i j
  exact ⟨w * z, Subring.mul_mem _ hw hz, by rw [e, mul_assoc]⟩



theorem qbU_dense (P : Q) (k : GL (Fin n) ((qv F P.1).adicCompletion F))
    (hk : qbInt (k : Matrix (Fin n) (Fin n) ((qv F P.1).adicCompletion F)))
    (hk' : qbInt ((k⁻¹ : GL (Fin n) ((qv F P.1).adicCompletion F)) : Matrix (Fin n) (Fin n) ((qv F P.1).adicCompletion F))) :
    ∃ g : ↥(GLint E n P.1), (qbIota P.1 (qbF hc hQ P) g)⁻¹ * k ∈
      qbU P.1 (qbF hc hQ P) (qbF_int hc hQ P) (qbF_P hc hQ P) (Θ P) (qbF hc hQ P (qbD hc Θ hQ hΘ P)) := by
  obtain ⟨b, hb⟩ := qsp_norm_mem hc (qbPi hc hQ P)
  have hbP : b ∈ (underPl F P.1).asIdeal := by
    show algebraMap (𝓞 F) (𝓞 E) b ∈ P.1.asIdeal
    rw [hb]; exact Ideal.mul_mem_right _ _ (qbPi_spec hc hQ P).1
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [map_zero, eq_comm, mul_eq_zero] at hb
    rcases hb with h | h
    · exact qbPi_ne hc hQ P h
    · exact (qbPi_spec hc hQ P).2.1 (by rw [h]; exact zero_mem _)
  have hNpos := (qbN_spec Θ hΘ P).1
  have hD0 : b ^ qbN Θ hΘ P ≠ 0 := pow_ne_zero _ hb0
  have hDv : b ^ qbN Θ hΘ P ∈ (underPl F P.1).asIdeal := Ideal.pow_mem_of_mem _ hbP _ hNpos
  obtain ⟨g, hg⟩ := qsp_dense P.1 (qbF hc hQ P) (qbF_int hc hQ P) (qbF_P hc hQ P) (qsp_sp_F hc P.1 _ (qbSp hc hQ P))
    (qsp_isOver P.1) (b ^ qbN Θ hΘ P) hD0 hDv k hk hk'
  have hbE : algebraMap (𝓞 F) ((qv F P.1).adicCompletion F) b =
      qbF hc hQ P ((qbPi hc hQ P : 𝓞 E) : E) * qbF hc hQ P (algebraMap (𝓞 E) E (cO E (qbPi hc hQ P))) := by
    rw [IsScalarTower.algebraMap_apply (𝓞 F) F ((qv F P.1).adicCompletion F), ← qsp_sp_F hc P.1 _ (qbSp hc hQ P),
      ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 E) E, hb, map_mul, map_mul]
  have hDE : algebraMap (𝓞 F) ((qv F P.1).adicCompletion F) (b ^ qbN Θ hΘ P) =
      qbF hc hQ P (qbD hc Θ hQ hΘ P) * qbF hc hQ P (algebraMap (𝓞 E) E (cO E (qbPi hc hQ P))) ^ qbN Θ hΘ P := by
    rw [map_pow, hbE, mul_pow, map_pow]
  rw [hDE] at hg
  have hw : qbF hc hQ P (algebraMap (𝓞 E) E (cO E (qbPi hc hQ P))) ^ qbN Θ hΘ P ∈ ((qv F P.1).adicCompletionIntegers F) :=
    Subring.pow_mem _ ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (qbF_int hc hQ P _)) _
  have hg2 := qbK_mono hw hg
  refine ⟨g, hg2.1, hg2.2.1, 1, (Θ P).H.one_mem, ?_⟩
  simpa using hg2

def qbLoc : QLoc hc n Q Θ where
  sp P := (qbSp hc hQ P).φ
  sp_sig P := (qbSp hc hQ P).sig
  sp_alg P := (qbSp hc hQ P).alg
  sp_int P := (qbSp hc hQ P).int
  sp_P P r := qbF_P hc hQ P r
  U P := qbU P.1 (qbF hc hQ P) (qbF_int hc hQ P) (qbF_P hc hQ P) (Θ P) (qbF hc hQ P (qbD hc Θ hQ hΘ P))
  U_int _ _ hk := hk.1
  U_rat P g := qbU_rat P.1 (qbF hc hQ P) (qbF_int hc hQ P) (qbF_P hc hQ P) (Θ P) (qbD hc Θ hQ hΘ P) (qbD_ne hc Θ hQ hΘ P)
    (qbD_val hc Θ hQ hΘ P) (qbN_spec Θ hΘ P).2 g
  U_dense P k hk hk' := qbU_dense hc Θ hQ hΘ P k hk hk'
  chr P := qbChr P.1 (qbF hc hQ P) (qbF_int hc hQ P) (qbF_P hc hQ P) (Θ P) (qbD hc Θ hQ hΘ P) (qbD_ne hc Θ hQ hΘ P)
    (qbD_val hc Θ hQ hΘ P) (qbN_spec Θ hΘ P).2
  chr_rat P g hg h := qbChr_rat P.1 (qbF hc hQ P) (qbF_int hc hQ P) (qbF_P hc hQ P) (Θ P) (qbD hc Θ hQ hΘ P) (qbD_ne hc Θ hQ hΘ P)
    (qbD_val hc Θ hQ hΘ P) (qbN_spec Θ hΘ P).2 g hg h

end Bridge

end Formalism.L2.Col
end
end

section

open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Conj

variable {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E)) (q : ℕ) (hq0 : (q : E) ≠ 0)

def QClose {m : ℕ} (W : Sp E m ≃ₗ[E] Sp E m) : Prop :=
  ∀ i j, P.valuation E ((((toGLm E m W : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) - 1) i j) ≤ P.valuation E (q : E)

theorem qth_conj_close {m : ℕ} (h r : Sp E m ≃ₗ[E] Sp E m) (a b N e : ℕ)
    (ha : ∀ i j, P.valuation E (((toGLm E m h : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) i j) ≤ WithZero.exp (a : ℤ))
    (hb : ∀ i j, P.valuation E (((toGLm E m h⁻¹ : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) i j) ≤ WithZero.exp (b : ℤ))
    (hr : ∀ i j, P.valuation E ((((toGLm E m r : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) - 1) i j) ≤ WithZero.exp (-(N : ℤ)))
    (he : WithZero.exp (-(e : ℤ)) ≤ P.valuation E (q : E)) (hN : a + b + e ≤ N) : QClose P q (h⁻¹ * r * h) := by
  intro i j
  set A := ((toGLm E m h⁻¹ : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) with hAdef
  set R := ((toGLm E m r : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) with hRdef
  set B := ((toGLm E m h : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) with hBdef
  have hmul : ((toGLm E m (h⁻¹ * r * h) : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) = A * R * B := by
    rw [map_mul, map_mul, Units.val_mul, Units.val_mul]
  have hAB : A * B = 1 := by
    rw [hAdef, hBdef, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
  have key : A * R * B - 1 = A * (R - 1) * B := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hAB]
  rw [hmul, key]
  have h1 := qth_conj_le P A (R - 1) B (b : ℤ) (a : ℤ) (N : ℤ) hb hr ha i j
  refine h1.trans (le_trans ?_ he)
  exact WithZero.exp_le_exp.mpr (by omega)


include hq0 in
theorem qth_mem_JQ {n c : ℕ} (kj : ℕ) (y : Sp E (n + c) ≃ₗ[E] Sp E (n + c)) (hy : QClose P q y) (hy' : QClose P q y⁻¹) :
    y ∈ LocE.JQ P q kj n c := by
  have hinv : ∀ x : Sp E (n + c), y⁻¹ (y x) = x := fun x => LinearEquiv.symm_apply_apply y x
  have he : ∀ l : ℕ, (fun l : ℕ => if kj ≤ l ∧ l < n then (1 : ℤ) else 0) l = 0 ∨
      (fun l : ℕ => if kj ≤ l ∧ l < n then (1 : ℤ) else 0) l = 1 := by
    intro l
    simp only
    split_ifs <;> simp
  refine Subgroup.mem_inf.2 ⟨fun x => ⟨fun hx => ?_, fun hx => qth_close_std P q hq0 y hy hx⟩,
    fun x => ⟨fun hx => ?_, fun hx => qth_close_scl P q hq0 _ he y hy hx⟩⟩
  · have := qth_close_std P q hq0 y⁻¹ hy' hx
    rwa [hinv] at this
  · have := qth_close_scl P q hq0 _ he y⁻¹ hy' hx
    rwa [hinv] at this


include hq0 in
theorem qth_red_entry (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) {m : ℕ} {y : Sp E m ≃ₗ[E] Sp E m} (hy : QClose P q y) (i j : Fin m) :
    IntAt P (((toGLm E m y : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) i j) ∧
      redP P (((toGLm E m y : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) i j) = redP P ((1 : Matrix (Fin m) (Fin m) E) i j) := by
  set M := ((toGLm E m y : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) with hMdef
  have hyij : P.valuation E ((M - 1) i j) ≤ P.valuation E (q : E) := hy i j
  have hv0 : P.valuation E (q : E) ≠ 0 := by simpa using hq0
  have ha0 : P.valuation E ((1 : Matrix (Fin m) (Fin m) E) i j) ≤ 1 := by
    rw [Matrix.one_apply]
    split_ifs <;> simp
  have hd : IntAt P ((M - 1) i j / (q : E)) := by
    rw [qth_intAt_iff, map_div₀, div_eq_mul_inv]
    calc P.valuation E ((M - 1) i j) * (P.valuation E (q : E))⁻¹
        ≤ P.valuation E (q : E) * (P.valuation E (q : E))⁻¹ := by gcongr
      _ = 1 := mul_inv_cancel₀ hv0
  have hsum : M i j = (1 : Matrix (Fin m) (Fin m) E) i j + (q : E) * ((M - 1) i j / (q : E)) := by
    rw [mul_div_cancel₀ _ hq0, Matrix.sub_apply]
    ring
  refine ⟨?_, ?_⟩
  · rw [qth_intAt_iff, show M i j = (1 : Matrix (Fin m) (Fin m) E) i j + (M - 1) i j by
      rw [Matrix.sub_apply]; ring]
    exact Valuation.map_add_le _ ha0 (hyij.trans (qth_vq_le P q))
  · rw [hsum]
    exact redP_add_natCast_mul hq hd

end Conj

end Formalism.L2.Col
end
end
