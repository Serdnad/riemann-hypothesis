module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle624
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle634
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle635
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle636
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle024
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

namespace GlobalTheory.BSP.PoleBound

variable {l : ℕ} [Fact l.Prime] {K : FinExt l} {bk : BK K} {τ : Ainf l}

theorem frobW_per (hτ : bk.IsPer τ) : frobW l (inclW l τ) = bk.evW bk.E * inclW l τ := by
  rw [frobW_inclW, hτ.1, map_mul]; rfl

theorem exists_basis {d : ℕ} {S : Strat bk d} {ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]}
    {T : Matrix (Fin d) (Fin d) (WCb l)} (hτ : bk.IsPer τ) (h : MReal S ρ T) :
    ∃ t : Matrix (Fin d) (Fin d) (Ainf l), t.map (inclW l) = inclW l τ ^ S.a • T := by
  have key : ∀ r j, inclW l τ ^ S.a * T r j ∈ (inclW l).range := fun r =>
    GlobalTheory.FrobIntTensor.mem_range_inclW l (fun j => inclW l τ ^ S.a * T r j)
      (Matrix.of fun j i => bk.ev (S.A i j)) fun j => by
        have e := congrFun (congrFun h.φ r) j
        simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.mul_apply, smul_eq_mul] at e
        rw [map_mul, map_pow, frobW_per hτ, mul_pow, mul_comm (bk.evW bk.E ^ S.a), mul_assoc, e, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        change _ = bk.evW (S.A i j) * _
        ring
  choose t ht using key
  exact ⟨Matrix.of t, Matrix.ext fun r j => ht r j⟩

theorem exists_inv {d : ℕ} {S : Strat bk d} {ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]}
    {T U : Matrix (Fin d) (Fin d) (WCb l)} (hτ : bk.IsPer τ) (h : MReal S ρ T) (hU : U * T = 1) (hT : T * U = 1) :
    ∃ t : Matrix (Fin d) (Fin d) (Ainf l), t.map (inclW l) = inclW l τ ^ S.b • U := by
  have h1 : U.map (frobW l) * T.map (frobW l) = 1 := by
    rw [← Matrix.map_mul (f := frobW l), hU, Matrix.map_one _ (map_zero _) (map_one _)]
  have h2 : S.A.map bk.evW * S.A'.map bk.evW = bk.evW bk.E ^ S.b • (1 : Matrix (Fin d) (Fin d) (WCb l)) := by
    rw [← Matrix.map_mul (f := bk.evW), S.A_mul]
    ext1 i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_pow, Matrix.one_apply]
    split_ifs <;> simp
  have h3 : bk.evW bk.E ^ S.b • U.map (frobW l) = bk.evW bk.E ^ S.a • (S.A'.map bk.evW * U) := by
    have e := congrArg (fun M => U.map (frobW l) * (M * S.A'.map bk.evW) * U) h.φ
    simp only [Matrix.mul_assoc T, h2, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one] at e
    rw [← Matrix.mul_assoc, h1, Matrix.one_mul, Matrix.mul_assoc, hT, Matrix.mul_one] at e
    exact e.symm
  have key : ∀ r j, inclW l τ ^ S.b * U j r ∈ (inclW l).range := fun r =>
    GlobalTheory.FrobIntTensor.mem_range_inclW l (fun j => inclW l τ ^ S.b * U j r)
      (Matrix.of fun j i => bk.ev (bk.E ^ S.a * S.A' j i)) fun j => by
        have e := congrFun (congrFun h3 j) r
        simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.mul_apply, smul_eq_mul] at e
        rw [map_mul, map_pow, frobW_per hτ, mul_pow, mul_comm (bk.evW bk.E ^ S.b), mul_assoc, e, Finset.mul_sum,
          Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        change _ = bk.evW (bk.E ^ S.a * S.A' j i) * _
        rw [map_mul, map_pow]
        ring
  choose t ht using key
  exact ⟨Matrix.of fun j r => t r j, Matrix.ext fun j r => ht r j⟩

theorem exists_pow_smul : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ →
    ∀ (d d' : ℕ) (S : Strat bk d) (S' : Strat bk d') (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l])
    (ρ' : ↥(GK K) → Matrix (Fin d') (Fin d') ℤ_[l]) (T : Matrix (Fin d) (Fin d) (WCb l))
    (T' : Matrix (Fin d') (Fin d') (WCb l)), MReal S ρ T → MReal S' ρ' T' →
    ∀ (f : Matrix (Fin d') (Fin d) ℤ_[l]) (X : Matrix (Fin d') (Fin d) (WCb l)), T' * X = zW f * T →
    ∃ (M : ℕ) (x : Matrix (Fin d') (Fin d) (Ainf l)), x.map (inclW l) = inclW l τ ^ M • X := by
  intro l _ K bk τ hτ d d' S S' ρ ρ' T T' h h' f X hX
  obtain ⟨V, hV⟩ := h'.unit
  have hU : (V⁻¹ : _ˣ).1 * T' = 1 := hV ▸ V.inv_mul
  have hT : T' * (V⁻¹ : _ˣ).1 = 1 := hV ▸ V.mul_inv
  obtain ⟨t, ht⟩ := exists_basis hτ h
  obtain ⟨u, hu⟩ := exists_inv hτ h' hU hT
  have hf : (f.map (algebraMap ℤ_[l] (Ainf l))).map (inclW l) = zW f :=
    Matrix.ext fun i j => (inclWA l).commutes (f i j)
  refine ⟨S'.b + S.a, u * (f.map (algebraMap ℤ_[l] (Ainf l)) * t), ?_⟩
  rw [Matrix.map_mul, Matrix.map_mul, ht, hu, hf, Matrix.mul_smul, ← hX, Matrix.smul_mul, Matrix.mul_smul,
    ← Matrix.mul_assoc, hU, Matrix.one_mul, smul_smul, pow_add]

end GlobalTheory.BSP.PoleBound
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem bk_ev_injective : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), Function.Injective bk.ev := by
  intro l _ K bk
  obtain ⟨ι, ⟨tb⟩⟩ := GlobalTheory.T.ainf_adicTopologicalBasis_over_breuilKisin l K bk
  intro a a' h
  have h1 : tb.c tb.i₀ 1 = 1 := by simpa [tb.b_i₀] using tb.c_self tb.i₀
  have key : ∀ x, tb.c tb.i₀ (bk.ev x) = x := fun x => by
    have := tb.c_mul tb.i₀ x (tb.b tb.i₀)
    rw [tb.b_i₀, mul_one, h1, mul_one] at this
    exact this
  rw [← key a, ← key a', h]

end GlobalTheory.BSP
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem mem_nonZeroDivisors_of_invertible_span {A : Type} [CommRing A] {I : Ideal A}
    (hI : Module.Invertible A ↥I) {d : A} (hd : I = Ideal.span {d}) : d ∈ nonZeroDivisors A := by
  have hdI : d ∈ I := hd ▸ Ideal.mem_span_singleton_self d
  let φ : A →ₗ[A] ↥I := LinearMap.toSpanSingleton A ↥I ⟨d, hdI⟩
  have hs : Function.Surjective φ := by
    rintro ⟨x, hx⟩
    rw [hd] at hx
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hx
    exact ⟨a, Subtype.ext (by simp [φ])⟩
  have hb := Module.Invertible.bijective_of_surjective hs
  refine mem_nonZeroDivisors_iff.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
  · refine hb.1 (?_ : φ a = φ 0)
    exact Subtype.ext (by simp [φ]; linear_combination ha)
  · refine hb.1 (?_ : φ a = φ 0)
    exact Subtype.ext (by simp [φ]; linear_combination ha)

theorem associated_of_span_eq {A : Type} [CommRing A] {d d' : A} (hd : d ∈ nonZeroDivisors A)
    (h : Ideal.span {d} = Ideal.span {d'}) : Associated d d' := by
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 (h ▸ Ideal.mem_span_singleton_self d)
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 (h.symm ▸ Ideal.mem_span_singleton_self d')
  have hab : a * b = 1 := by
    have : d * (a * b - 1) = 0 := by linear_combination a * hb + ha
    exact sub_eq_zero.1 ((mem_nonZeroDivisors_iff.1 hd).1 _ this)
  exact ⟨⟨b, a, by rw [mul_comm]; exact hab, hab⟩, by rw [Units.val_mk, mul_comm]; exact hb⟩

theorem hf_E_pair : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (B : Obj l ↥(OL K)) (f g : Hom bk.prism B),
    BK.hf f bk.E ∈ nonZeroDivisors B.A ∧ Associated (BK.hf f bk.E) (BK.hf g bk.E) ∧
      BK.hf f bk.E ∣ BK.hf g X - BK.hf f X := by
  intro l _ K bk B f g
  obtain ⟨hfI, hfX⟩ := GlobalTheory.T.isOrientedPrismUniformizerFrame_breuilKisinHom l K bk B f
  obtain ⟨hgI, hgX⟩ := GlobalTheory.T.isOrientedPrismUniformizerFrame_breuilKisinHom l K bk B g
  have hreg := mem_nonZeroDivisors_of_invertible_span B.inv hfI
  refine ⟨hreg, associated_of_span_eq hreg (hfI.symm.trans hgI), ?_⟩
  rw [← Ideal.mem_span_singleton, ← hfI]
  exact Ideal.Quotient.eq.1 (hgX.trans hfX.symm)

end GlobalTheory.BSP
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.disc_bounded_function_isPowerSeries : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (ρ : ℝ≥0), 0 < ρ → ρ < 1 → ∀ y : bk.DS ρ, (∀ ρ₁ : ℝ≥0, ρ₁ < 1 → ∃ (ρ' : ℝ≥0) (R : bk.DS ρ' →+* bk.DS ρ) (y' : bk.DS ρ'), ρ₁ ≤ ρ' ∧ ρ ≤ ρ' ∧ ρ' < 1 ∧ IsDiscMap (l := _) (u := _) (ρ := _) (RingHom.id bk.S) R ∧ R y' = y ∧ ‖y'‖ ≤ 1) → ∃ a, toDisc l (X : bk.S) ρ a = y := by
  first | exact @GlobalTheory.BSP.disc_bdd_isSeries | exact GlobalTheory.BSP.disc_bdd_isSeries | (intros; apply GlobalTheory.BSP.disc_bdd_isSeries <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.ResTilt

variable (l : ℕ) [hl : Fact l.Prime] (a : ℕ) [NeZero a]

abbrev red : (Wq l a)⟦X⟧ →+* (Fq l a)⟦X⟧ := PowerSeries.map (WittVector.constantCoeff (p := l) (R := Fq l a))

def sec (f : (Fq l a)⟦X⟧) : (Wq l a)⟦X⟧ := mk fun n => WittVector.teichmuller l (coeff n f)

theorem red_sec : Function.RightInverse (sec l a) (red l a) := fun f =>
  PowerSeries.ext fun n => by simp [red, sec, coeff_map, WittVector.constantCoeff_apply]

theorem red_l : red l a (l : (Wq l a)⟦X⟧) = 0 := by
  rw [map_natCast]; exact l_eq_zero l a


omit [NeZero a] in
theorem sub_teich_dvd (x : Ainf l) : ∃ z, x = WittVector.teichmuller l (x.coeff 0) + (l : Ainf l) * z := by
  have h : x - WittVector.teichmuller l (x.coeff 0) ∈ Ideal.span {(l : Ainf l)} := by
    rw [← WittVector.ker_constantCoeff, RingHom.mem_ker, map_sub]
    simp [WittVector.constantCoeff_apply]
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 h
  exact ⟨z, by linear_combination -hz⟩

end GlobalTheory.BSP.ResTilt


open GlobalTheory.BSP.ResTilt in
theorem GlobalTheory.BSP.exists_resTilt_retract : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K),
    ∃ (ek : (Fq l bk.a)⟦X⟧ →+* OCb l) (pr : OCb l →+ (Fq l bk.a)⟦X⟧),
      (∀ s : bk.S, ek (PowerSeries.map (WittVector.constantCoeff (p := l) (R := Fq l bk.a)) s) =
        (bk.ev s).coeff 0) ∧ Function.Injective ek ∧ (∀ a y, pr (ek a * y) = a * pr y) ∧ pr 1 = 1 := by
  intro l _ K bk
  obtain ⟨ι, ⟨tb⟩⟩ := GlobalTheory.T.ainf_adicTopologicalBasis_over_breuilKisin l K bk
  let φ : bk.S →+* OCb l := (WittVector.constantCoeff (p := l) (R := OCb l)).comp bk.ev
  have hker : RingHom.ker (red l bk.a) ≤ RingHom.ker φ := fun s hs => by
    obtain ⟨t, rfl⟩ := dvd_of_map_eq_zero l bk.a s hs
    rw [RingHom.mem_ker, map_mul, map_natCast, CharP.cast_eq_zero, zero_mul]
  let ek : (Fq l bk.a)⟦X⟧ →+* OCb l := (red l bk.a).liftOfRightInverse (sec l bk.a) (red_sec l bk.a) ⟨φ, hker⟩
  have hek : ∀ s, ek (red l bk.a s) = φ s := fun s =>
    (red l bk.a).liftOfRightInverse_comp_apply (sec l bk.a) (red_sec l bk.a) ⟨φ, hker⟩ s

  let P : OCb l → (Fq l bk.a)⟦X⟧ := fun y => red l bk.a (tb.c tb.i₀ (WittVector.teichmuller l y))
  have hwd : ∀ x : Ainf l, red l bk.a (tb.c tb.i₀ x) = P (x.coeff 0) := fun x => by
    obtain ⟨z, hz⟩ := sub_teich_dvd l x
    conv_lhs => rw [hz]
    have e : (l : Ainf l) = bk.ev (l : bk.S) := (map_natCast _ _).symm
    rw [map_add (f := _), e, tb.c_mul, map_add (f := _), map_mul, red_l l bk.a, zero_mul, add_zero]
  let pr : OCb l →+ (Fq l bk.a)⟦X⟧ :=
    { toFun := P
      map_zero' := by simp [P]
      map_add' := fun y y' => by
        have h := hwd (WittVector.teichmuller l y + WittVector.teichmuller l y')
        rw [map_add (f := _), map_add (f := _)] at h
        have h0 : (WittVector.teichmuller l y + WittVector.teichmuller l y').coeff 0 = y + y' := by
          rw [← WittVector.constantCoeff_apply, map_add (f := _)]; simp [WittVector.constantCoeff_apply]
        rw [h0] at h
        exact h.symm }
  have hmul : ∀ a y, pr (ek a * y) = a * pr y := fun f y => by
    obtain ⟨s, rfl⟩ : ∃ s, red l bk.a s = f := ⟨sec l bk.a f, red_sec l bk.a f⟩
    have h := hwd (bk.ev s * WittVector.teichmuller l y)
    rw [tb.c_mul, map_mul] at h
    change P (ek (red l bk.a s) * y) = red l bk.a s * P y
    have e : (bk.ev s * WittVector.teichmuller l y).coeff 0 = φ s * y := by
      rw [← WittVector.constantCoeff_apply, map_mul, WittVector.constantCoeff_apply,
        WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]
      rfl
    rw [hek, ← e]
    exact h.symm
  have hone : pr 1 = 1 := by
    change red l bk.a (tb.c tb.i₀ (WittVector.teichmuller l 1)) = 1
    rw [map_one, ← tb.b_i₀, tb.c_self, map_one]
  refine ⟨ek, pr, fun s => hek s, ?_, hmul, hone⟩
  refine Function.LeftInverse.injective (g := pr) fun f => ?_
  have := hmul f 1
  rwa [mul_one, hone, mul_one] at this
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

theorem _root_.GlobalTheory.T.null_powerSeries_of_null_ainf_mul : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (ι : Type) (TB : TopBasis bk.ev bk.J ι) (d : ℕ) (Y : Matrix (Fin d) (Fin d) (Ainf l)), IsUnit (Y.map (inclW l)) → ∀ (σ : ι → Matrix (Fin d) (Fin d) bk.S), (∀ (n : ℕ) (a b : Fin d), {i | (Y * (σ i).map bk.ev) a b ∉ (bk.J ^ n).map bk.ev}.Finite) → ∀ (n : ℕ) (a b : Fin d), {i | σ i a b ∉ bk.J ^ n}.Finite := by
  first | exact @GlobalTheory.NullOverS.null_of_mul_null | exact GlobalTheory.NullOverS.null_of_mul_null | (intros; apply GlobalTheory.NullOverS.null_of_mul_null <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.breuilKisinPrism_homs_agree_witt_and_mod_ideal : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (B : Obj l ↥(OL K)) (f g : Hom bk.prism B), (∀ w, BK.hf f (PowerSeries.C w) = BK.hf g (PowerSeries.C w)) ∧ BK.hf f X - BK.hf g X ∈ B.I ∧ B.I = Ideal.span {BK.hf f bk.E} := by
  first | exact @GlobalTheory.BSP.IdealSubMembership.main | exact GlobalTheory.BSP.IdealSubMembership.main | (intros; apply GlobalTheory.BSP.IdealSubMembership.main <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.exists_closedDisc_extension_breuilKisinHom : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), ∀ (B : Obj l ↥(OL K)) (f g : Hom bk.prism B) (ρ : ℝ≥0), bk.ρ₀ ≤ ρ → ρ ≤ 1 → ∃ F : bk.DS ρ →+* Disc l (BK.hf f X) ρ, IsDiscMap (l := _) (u := _) (ρ := _) (BK.hf g) F := by
  first | exact @GlobalTheory.BSP.DiscPrism.disc_map_exists | exact GlobalTheory.BSP.DiscPrism.disc_map_exists | (intros; apply GlobalTheory.BSP.DiscPrism.disc_map_exists <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.exists_ainf_linear_retraction_breuilKisin : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), ∃ c : Ainf l →+ bk.S, (∀ (s : bk.S) (a : Ainf l), c (bk.ev s * a) = s * c a) ∧ c 1 = 1 := by
  first | exact @GlobalTheory.BKLim.AinfRetraction.main | exact GlobalTheory.BKLim.AinfRetraction.main | (intros; apply GlobalTheory.BKLim.AinfRetraction.main <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.mittagLeffler_image_breuilKisin_modPow : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (d' : ℕ → ℕ) (R : ∀ n, Matrix (Fin d) (Fin (d' n)) (WCb l)) (Y : ∀ n, Matrix (Fin (d' n)) (Fin (d' (n + 1))) (bk.S)), (∀ n i j, (l : WCb l) ^ n ∣ (R n * (Y n).map bk.evW - R (n + 1)) i j) → (∀ n, ∃ c : ℕ, ∀ m, n ≤ m → ∀ s : Fin (d' n) → bk.S, ∃ s' : Fin (d' m) → bk.S, ∀ i, (l : WCb l) ^ n ∣ ((R n *ᵥ fun j => bk.evW (X ^ c * s j)) - R m *ᵥ fun j => bk.evW (s' j)) i) → ∀ n, ∃ m, n ≤ m ∧ ∀ s : Fin (d' m) → bk.S, ∃ v : Fin d → WCb l, (∀ i, (l : WCb l) ^ n ∣ (v - R m *ᵥ fun j => bk.evW (s j)) i) ∧ ∀ k, ∃ s' : Fin (d' k) → bk.S, ∀ i, (l : WCb l) ^ k ∣ (v - R k *ᵥ fun j => bk.evW (s' j)) i := by
  first | exact @GlobalTheory.BKLim.mittagLeffler_image | exact GlobalTheory.BKLim.mittagLeffler_image | (intros; apply GlobalTheory.BKLim.mittagLeffler_image <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.norm_teichmullerTiltMinusOne_le : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (e : OCb l), IsEps e → ‖bk.iA (mu e)‖ ≤ (l : ℝ)⁻¹ ∧ (l = 2 → ‖bk.iA (mu e)‖ ≤ (4 : ℝ)⁻¹) := by
  first | exact @GlobalTheory.BSP.BK.norm_iA_mu_le | exact GlobalTheory.BSP.BK.norm_iA_mu_le | (intros; apply GlobalTheory.BSP.BK.norm_iA_mu_le <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.acris_frobenius_matrix_eq_zero_of_dvd : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d c : ℕ) (D₀ F F' : Matrix (Fin d) (Fin d) (Per.Acris l)), (∀ i j, ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev) X ∣ D₀ i j) → (l : Per.Acris l) ^ c • D₀ = F * D₀.map (phiA l) * F' → D₀ = 0 := by
  first | exact @GlobalTheory.BKLim.acris_frob_eq_zero | exact GlobalTheory.BKLim.acris_frob_eq_zero | (intros; apply GlobalTheory.BKLim.acris_frob_eq_zero <;> assumption)
end
