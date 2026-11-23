module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle573
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle701
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle549
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DetCharacterMemPrincipalCongruenceFixedVectors
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle199
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle704
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsEqAlgebraMapAddPowMul
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InstTameDescentExponentDataPadicThree
public import Mathlib.RingTheory.FiniteLength
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle690
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle708
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAuxiliaryHeckeCharacter
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle707
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle489
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle558
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle556
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle706
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.Kernel
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle009
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InvertibleSpanSingleton
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle015
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle638
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP

theorem BK.X_pow_eq_sub {l : ℕ} [Fact l.Prime] {K : FinExt l} (bk : BK K) :
    ∃ q : bk.S, (X : bk.S) ^ bk.Ep.natDegree = bk.E - (l : bk.S) * q := by
  have h : Polynomial.C (l : Wq l bk.a) ∣ bk.Ep - Polynomial.X ^ bk.Ep.natDegree := by
    rw [Polynomial.C_dvd_iff_dvd_coeff]
    intro i
    rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow]
    rcases lt_trichotomy i bk.Ep.natDegree with hi | rfl | hi
    · rw [if_neg hi.ne, sub_zero]; exact bk.dvd_coeff i hi
    · rw [if_pos rfl, bk.monic.coeff_natDegree, sub_self]; exact dvd_zero _
    · rw [if_neg hi.ne', sub_zero, Polynomial.coeff_eq_zero_of_natDegree_lt hi]; exact dvd_zero _
  obtain ⟨q, hq⟩ := h
  refine ⟨(q : bk.S), ?_⟩
  have := congrArg (Polynomial.coeToPowerSeries.ringHom (R := Wq l bk.a)) hq
  simp only [map_sub, map_pow, map_mul, Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_X,
    Polynomial.coe_C, map_natCast] at this
  linear_combination -this

theorem isHausdorff_quot {l : ℕ} [Fact l.Prime] {R : Type} [CommRing R] (P : Obj l R) (d : P.A)
    (hd : P.I = Ideal.span {d}) : IsHausdorff ((JJ P).map (Ideal.Quotient.mk P.I)) (P.A ⧸ P.I) := by
  have hinv := P.inv
  rw [hd] at hinv
  have hnzd : d ∈ nonZeroDivisors P.A := GlobalTheory.T.mem_nonZeroDivisors_of_invertible_span_singleton' P.A d hinv
  obtain ⟨N, hN⟩ := P.bdd
  have hbdd : ∀ (x : P.A) (m : ℕ), (l : P.A) ^ m * x ∈ Ideal.span {d} →
      (l : P.A) ^ N * x ∈ Ideal.span {d} := by
    intro x m hx
    rw [← hd, ← Ideal.Quotient.eq_zero_iff_mem] at hx ⊢
    rw [map_mul, map_pow, map_natCast] at hx ⊢
    exact hN _ ⟨m, hx⟩
  have hc := P.complete
  rw [hd] at hc
  refine ⟨fun y hy => ?_⟩
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [Ideal.Quotient.eq_zero_iff_mem, hd]
  refine GlobalTheory.T.mem_span_singleton_of_bounded_torsion_of_adic_limit l P.A d N hnzd hbdd hc x fun n => ?_
  have h1 := hy n
  simp only [SModEq.zero, smul_eq_mul, Ideal.mul_top] at h1
  rw [← Ideal.map_pow, Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective] at h1
  obtain ⟨y, hy, hyx⟩ := h1
  rw [Ideal.Quotient.eq, hd, Ideal.mem_span_singleton'] at hyx
  obtain ⟨z, hz⟩ := hyx
  refine ⟨-z, ?_⟩
  have e : x - d * -z = y := by linear_combination hz
  rw [e]
  rw [JJ, hd] at hy
  exact hy

theorem exists_lift_coeff_zero {l : ℕ} [Fact l.Prime] {k B : Type} [CommRing k] [CharP k l] [PerfectRing k l]
    [CommRing B] (f0 : WittVector l k →+* B) (hl : f0 (l : WittVector l k) = 0) :
    ∃ ψ : k →+* B, ∀ w : WittVector l k, ψ (w.coeff 0) = f0 w := by
  have hsurj : Function.Surjective (WittVector.constantCoeff : WittVector l k →+* k) :=
    fun x => ⟨WittVector.teichmuller l x, by simp [WittVector.constantCoeff_apply]⟩
  have hker : ∀ a ∈ RingHom.ker (WittVector.constantCoeff : WittVector l k →+* k), f0 a = 0 := by
    intro a ha
    rw [WittVector.ker_constantCoeff, Ideal.mem_span_singleton'] at ha
    obtain ⟨b, rfl⟩ := ha
    rw [map_mul, hl, mul_zero]
  refine ⟨(Ideal.Quotient.lift _ f0 hker).comp (RingHom.quotientKerEquivOfSurjective hsurj).symm.toRingHom,
    fun w => ?_⟩
  have e : (RingHom.quotientKerEquivOfSurjective hsurj).symm (w.coeff 0) = Ideal.Quotient.mk _ w := by
    rw [RingEquiv.symm_apply_eq]; rfl
  show Ideal.Quotient.lift _ f0 hker ((RingHom.quotientKerEquivOfSurjective hsurj).symm (w.coeff 0)) = _
  rw [e, Ideal.Quotient.lift_mk]

theorem pow_mem_of_eq_sub {A S : Type} [CommRing A] [CommRing S] {I J : Ideal A} (hIJ : I ≤ J) {l : ℕ}
    (hl : (l : A) ∈ J) (τ : S →+* A ⧸ I) {x E q : S} {e : ℕ} {v : A} (hq : x ^ e = E - (l : S) * q)
    (hE : τ E = 0) (hx : τ x = Ideal.Quotient.mk I v) : v ^ e ∈ J := by
  have a2 := congrArg τ hq
  rw [map_pow, map_sub, map_mul, map_natCast, hx, hE] at a2
  obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective (τ q)
  have h1 : Ideal.Quotient.mk I (v ^ e + (l : A) * t) = 0 := by
    rw [map_add (f := _), map_pow, map_mul, map_natCast, ht, a2]
    ring
  have h2 := hIJ (Ideal.Quotient.eq_zero_iff_mem.1 h1)
  have h3 : (l : A) * t ∈ J := Ideal.mul_mem_right _ _ hl
  simpa using J.sub_mem h2 h3

theorem sub_mem_map_of_mk_eq {A : Type} [CommRing A] {I J : Ideal A} (hIJ : I ≤ J) (a : A) (y : A ⧸ I)
    (h : Ideal.Quotient.mk J a = Ideal.Quotient.factor hIJ y) :
    Ideal.Quotient.mk I a - y ∈ J.map (Ideal.Quotient.mk I) := by
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq] at h
  rw [← map_sub]
  exact Ideal.mem_map_of_mem _ h

theorem quot_comp_eq {W A : Type} [CommRing W] [CommRing A] {I J : Ideal A}
    (hH : IsHausdorff (J.map (Ideal.Quotient.mk I)) (A ⧸ I)) (σ : W⟦X⟧ →+* A) (τ : W⟦X⟧ →+* A ⧸ I)
    {v : A} {e : ℕ} (hve : v ^ e ∈ J) (hσX : σ X = v) (hτX : τ X = Ideal.Quotient.mk I v)
    (hC : ∀ w, Ideal.Quotient.mk I (σ (C w)) = τ (C w)) : (Ideal.Quotient.mk I).comp σ = τ := by
  refine ringHom_ext_of_sep _ _ hC ?_ ?_
  · rw [RingHom.comp_apply, hσX, hτX]
  · intro y hy
    refine hH.haus y fun n => ?_
    simp only [SModEq.zero, smul_eq_mul, Ideal.mul_top]
    obtain ⟨c, hc⟩ := hy (e * n)
    rw [hc, RingHom.comp_apply, hσX, pow_mul, ← map_pow]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (Ideal.mem_map_of_mem _ hve) n)

theorem mem_of_comp_eq {S A : Type} [CommRing S] [CommRing A] {I : Ideal A} (σ : S →+* A)
    (τ : S →+* A ⧸ I) (heq : (Ideal.Quotient.mk I).comp σ = τ) {E : S} (hE : τ E = 0) (a : S)
    (ha : a ∈ Ideal.span {E}) : σ a ∈ I := by
  obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.1 ha
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← RingHom.comp_apply, heq, map_mul, hE, mul_zero]

theorem natCast_mem_map_quot {A : Type} [CommRing A] {I J : Ideal A} {l : ℕ} (h : (l : A) ∈ J) :
    (l : A ⧸ I) ∈ J.map (Ideal.Quotient.mk I) := by
  have := Ideal.mem_map_of_mem (Ideal.Quotient.mk I) h
  rwa [map_natCast] at this

theorem exists_hom_of_frame : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (C : Obj l ↥(OL K)) (d v : C.A),
    IsFrame bk C d v → C.D.δ v = 0 → ∃ g : Hom bk.prism C, BK.hf (bk := bk) g X = v := by
  intro l _ K bk P d v hF hδ
  obtain ⟨hd, hv⟩ := hF
  obtain ⟨τ, hτ⟩ : ∃ τ : bk.S →+* P.A ⧸ P.I,
      τ = P.str.comp (bk.str.symm.toRingHom.comp (Ideal.Quotient.mk (Ideal.span {bk.E}))) := ⟨_, rfl⟩
  have hτX : τ X = Ideal.Quotient.mk P.I v := by rw [hτ]; exact hv.symm
  have hτE : τ bk.E = 0 := by
    rw [hτ]
    show P.str (bk.str.symm (Ideal.Quotient.mk (Ideal.span {bk.E}) bk.E)) = 0
    rw [Ideal.Quotient.mk_singleton_self, map_zero, map_zero]
  set J : Ideal P.A := JJ P with hJ
  have hIJ : P.I ≤ J := le_sup_right
  have hlJ : (l : P.A) ∈ J := Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)
  obtain ⟨f0, hf0⟩ : ∃ f0 : Wq l bk.a →+* P.A ⧸ J,
      f0 = ((Ideal.Quotient.factor hIJ).comp τ).comp PowerSeries.C := ⟨_, rfl⟩
  have hl0 : f0 (l : Wq l bk.a) = 0 := by
    rw [map_natCast, ← map_natCast (Ideal.Quotient.mk J) l]
    exact Ideal.Quotient.eq_zero_iff_mem.2 hlJ
  obtain ⟨ψ, hψ⟩ := exists_lift_coeff_zero f0 hl0
  obtain ⟨ω, hω⟩ := GlobalTheory.T.exists_wittVector_lift_of_isAdicComplete' l (Fq l bk.a) P.A J hlJ P.complete ψ
  obtain ⟨q, hq⟩ := bk.X_pow_eq_sub
  generalize bk.Ep.natDegree = e at hq
  have hve : v ^ e ∈ J := pow_mem_of_eq_sub hIJ hlJ τ hq hτE hτX
  obtain ⟨σ, hσC, hσX⟩ := GlobalTheory.T.exists_powerSeries_ringHom_of_isAdicComplete (Wq l bk.a) P.A J P.complete ω v _ hve
  have hσδ := GlobalTheory.T.isDeltaRingHom_powerSeries_of_rank_one_image l bk.a P.A P.D J hlJ P.complete.toIsHausdorff σ _ (by rw [hσX]; exact hve)
    (by rw [hσX]; exact hδ)
  have hH := isHausdorff_quot P d hd
  have hlJ' := natCast_mem_map_quot (I := P.I) hlJ
  have hωC : (Ideal.Quotient.mk P.I).comp ω = τ.comp PowerSeries.C := by
    refine GlobalTheory.T.wittVector_ringHom_eq_of_sub_mem' l (Fq l bk.a) (P.A ⧸ P.I) (J.map (Ideal.Quotient.mk P.I)) hlJ' hH _ _ ?_
    intro w
    refine sub_mem_map_of_mk_eq hIJ (ω w) (τ (PowerSeries.C w)) ((hω w).trans ((hψ w).trans ?_))
    rw [hf0]
    simp only [RingHom.comp_apply]
  have heq : (Ideal.Quotient.mk P.I).comp σ = τ :=
    quot_comp_eq hH σ τ hve hσX hτX fun w =>
      (congrArg (Ideal.Quotient.mk P.I) (hσC w)).trans (RingHom.congr_fun hωC w)
  refine ⟨{ f := σ, f_δ := fun a => hσδ a, f_I := mem_of_comp_eq σ τ heq hτE, f_str := ?_ }, hσX⟩
  intro r a h
  have h' : Ideal.Quotient.mk (Ideal.span {bk.E}) a = bk.str r := h
  have h2 := RingHom.congr_fun heq a
  rw [hτ] at h2
  refine h2.trans ?_
  show P.str (bk.str.symm (Ideal.Quotient.mk (Ideal.span {bk.E}) a)) = P.str r
  exact congrArg P.str ((congrArg bk.str.symm h').trans (bk.str.symm_apply_apply r))

end GlobalTheory.BSP
end
end

section

open Polynomial GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.GLp.Supp GlobalTheory.SerSys GlobalTheory.TypeLeaf Formalism.BasicNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders
open scoped Classical

theorem _root_.GlobalTheory.T.series_eq_prod_of_parabolic_induction_chain : ∀ (g : ℕ) [Fact g.Prime] (S : Sys g) (π : GLRep g) (L : List (GLRep g)), InInd π L → ∀ F, Has S π.2.ρ F → ∃ fs : List (ZMod g)[X], List.Forall₂ (fun (ρ : GLRep g) f => Has S ρ.2.ρ f) L fs ∧ F = fs.prod := by
  first | exact @GlobalTheory.SerSys.has_prod_of_inInd | exact GlobalTheory.SerSys.has_prod_of_inInd | (intros; apply GlobalTheory.SerSys.has_prod_of_inInd <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem GlobalTheory.BK.Hom.finiteLength_coker_of_generic : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (κ : Type) [Fintype κ] [DecidableEq κ] (P : PhiMod O K l e a ι) (Q : PhiMod O K l e a κ) (F : GlobalTheory.BK.Hom P Q), ((∀ τ, ∃ (Y : Matrix ι κ K⟦X⟧) (g : K⟦X⟧), (∀ i j, Y i j ∈ A O K) ∧ (∃ n, ‖coeff n g‖ = 1) ∧ F.mat τ * Y = g • (1 : Matrix κ κ K⟦X⟧)) → IsFiniteLength (A O K) F.coker) ∧ ((∀ τ, ∃ (Y : Matrix ι κ K⟦X⟧) (g : K⟦X⟧), (∀ i j, Y i j ∈ A O K) ∧ (∃ n, ‖coeff n g‖ = 1) ∧ Y * F.mat τ = g • (1 : Matrix ι ι K⟦X⟧)) → ∀ v ∈ Q.M, ∀ f ∈ A O K, f ≠ 0 → f • v ∈ F.imM → v ∈ F.imM) := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ κ _ _ P Q F
  have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
  have h1 : (l : K) = algebraMap ℚ_[l] K (l : ℚ_[l]) := (map_natCast _ _).symm
  have hlK : ‖(l : K)‖ < 1 := by
    rw [h1, norm_algebraMap', Padic.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hl2)
  have hl0 : (l : K) ≠ 0 := by
    rw [h1]
    exact (map_ne_zero _).2 (by exact_mod_cast (Fact.out : l.Prime).ne_zero)
  have he : 0 < e := Nat.pos_of_ne_zero (NeZero.ne e)
  have hone : ∃ c : ℝ, ∀ n, ‖coeff n (1 : K⟦X⟧)‖ ≤ c :=
    ⟨1, fun n => by rw [coeff_one]; split_ifs <;> simp⟩
  refine ⟨fun hyp => GlobalTheory.T.coker_finite_length_of_primitive_divisor O K l e a ι κ P Q F hyp ?_, fun hyp => GlobalTheory.T.cokernel_torsionFree_of_bounded_leftInverse O K l e a ι κ P Q F hyp ?_⟩
  · rcases isEmpty_or_nonempty κ with hκ | ⟨⟨i0⟩⟩
    · intro τ
      exact ⟨hone, 0, ⟨0, fun _ j => isEmptyElim j⟩, Subsingleton.elim _ _⟩
    · obtain ⟨M₁, h₁⟩ := GlobalTheory.T.exists_E_pow_mul_frob_mem_rightDivisorSet O K l e a ι κ P Q F
      obtain ⟨M₂, h₂⟩ := GlobalTheory.T.exists_frobeniusSlice_mem_rightDivisorSet O K l e a ι κ P Q F
      refine GlobalTheory.T.one_mem_of_frobenius_linked_boundedSeries_ideals K l e a M₁ M₂ he hl0 hlK F.rdivSet (fun τ x hx y hy => Hom.rdivSet_add F τ hx hy)
        (fun τ x hx b hb => Hom.rdivSet_mul F τ hx b hb) (fun τ x hx => hx.1) ?_ h₁ h₂
      intro τ
      obtain ⟨Y, g, hY, hg, hFY⟩ := hyp τ
      have hgA : g ∈ A O K := by
        have : (F.mat τ * Y) i0 i0 = g := by rw [hFY]; simp
        rw [← this, Matrix.mul_apply]
        exact Subalgebra.sum_mem _ fun j _ => mul_mem (F.mem τ i0 j) (hY j i0)
      exact ⟨g, ⟨⟨1, mem_A.1 hgA⟩, Y, ⟨1, fun i j => mem_A.1 (hY i j)⟩, hFY⟩, mem_A.1 hgA, hg⟩
  · rcases isEmpty_or_nonempty ι with hι | ⟨⟨i0⟩⟩
    · intro τ
      exact ⟨hone, 0, ⟨0, fun i _ => isEmptyElim i⟩, Subsingleton.elim _ _⟩
    · obtain ⟨M₁, h₁⟩ := GlobalTheory.T.frob_mem_leftDivisorSet_phiModuleHom O K l e a ι κ P Q F
      obtain ⟨M₂, h₂⟩ := GlobalTheory.T.frobeniusResidueSlice_mem_boundedLeftDivisorSet O K l e a ι κ P Q F
      refine GlobalTheory.T.one_mem_of_frobenius_linked_boundedSeries_ideals K l e a M₁ M₂ he hl0 hlK F.ldivSet (fun τ x hx y hy => Hom.ldivSet_add F τ hx hy)
        (fun τ x hx b hb => Hom.ldivSet_mul F τ hx b hb) (fun τ x hx => hx.1) ?_ h₁ h₂
      intro τ
      obtain ⟨Y, g, hY, hg, hFY⟩ := hyp τ
      have hgA : g ∈ A O K := by
        have : (Y * F.mat τ) i0 i0 = g := by rw [hFY]; simp
        rw [← this, Matrix.mul_apply]
        exact Subalgebra.sum_mem _ fun j _ => mul_mem (hY i0 j) (F.mem τ j i0)
      exact ⟨g, ⟨⟨1, mem_A.1 hgA⟩, Y, ⟨1, fun i j => mem_A.1 (hY i j)⟩, hFY⟩, mem_A.1 hgA, hg⟩
end

section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie

namespace GlobalTheory.LamTie

theorem sum_th_empty_ne_zero : ∀ (D : D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (Z : LamDat D), Z.Ok → IsLamTie0 X Z → ∀ i, X.NonzeroIndexPlace i → ∀ lam : X.abelian₂ i, (∑ δ, X.th i ∅ lam δ) ≠ 0 ∧ ∃ s : ℤ, BlochKatoReduction.Gen.SOk X i lam s := by
  intro D N X Z hZ hT i hi lam
  obtain ⟨ι, j, a, s, hs, u, T, hu, hTs, hEq⟩ := hT i hi lam
  refine ⟨?_, s, hs⟩
  have h1 : 1 ≤ s := by
    have := hs.2.1
    exact_mod_cast this
  have h2 : (s : ℤ) ≤ (BlochKatoReduction.Gen.NFun D.R : ℤ) + 1 := hs.2.2
  obtain ⟨Λ, -, hne, hiff⟩ := GlobalTheory.T.exists_heckeL_eq_toricSum_ne_zero D.R D.host _ (phi D.host) s (Z.kap j a s) (cond0 D.host Z.w0)
    (Z.lam0 (X.l i) j a) (GlobalTheory.T.isHostDatum_kap_lam0_of_ok D Z hZ (X.l i) j a s h1 h2)
  have hT0 : T ≠ 0 := by rw [(hiff T).1 hTs]; exact hne
  intro h0
  rw [h0, map_zero] at hEq
  exact mul_ne_zero hu ((map_ne_zero ι).2 hT0) hEq.symm

end GlobalTheory.LamTie
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.EtReal

open Matrix

variable {l : ℕ} [hl : Fact l.Prime]

theorem equivFun_frob {T : Type} [AddCommGroup T] [Module ℤ_[l] T] {ι : Type} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℤ_[l] T) (y : WCb l ⊗[ℤ_[l]] T) :
    (b.baseChange (WCb l)).equivFun (TensorProduct.map (frobW l).toLinearMap LinearMap.id y) =
      fun i => frobW l ((b.baseChange (WCb l)).equivFun y i) := by
  funext i
  simp only [Module.Basis.equivFun_apply]
  induction y with
  | tmul a t =>
    rw [TensorProduct.map_tmul, Module.Basis.baseChange_repr_tmul, Module.Basis.baseChange_repr_tmul,
      map_smul, AlgHom.toLinearMap_apply, LinearMap.id_apply]
  | add y z hy hz => rw [map_add (f := _), map_add (f := _), map_add (f := _), Finsupp.add_apply, Finsupp.add_apply, map_add (f := _), hy, hz]

theorem equivFun_map {T : Type} [AddCommGroup T] [Module ℤ_[l] T] {ι : Type} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℤ_[l] T) (s : WCb l ≃ₐ[ℤ_[l]] WCb l) (r : T →ₗ[ℤ_[l]] T) (y : WCb l ⊗[ℤ_[l]] T) :
    (b.baseChange (WCb l)).equivFun (TensorProduct.map s.toLinearMap r y) =
      (LinearMap.toMatrix b b r).map (algebraMap ℤ_[l] (WCb l)) *ᵥ
        fun k => s ((b.baseChange (WCb l)).equivFun y k) := by
  funext i
  simp only [Module.Basis.equivFun_apply, Matrix.mulVec, dotProduct, Matrix.map_apply]
  induction y with
  | tmul a t =>
    rw [TensorProduct.map_tmul, Module.Basis.baseChange_repr_tmul, AlgEquiv.toLinearMap_apply,
      ← LinearMap.toMatrix_mulVec_repr b b r t]

    simp only [Module.Basis.baseChange_repr_tmul, Matrix.mulVec, dotProduct, map_smul, Algebra.smul_def,
    Finset.sum_mul, map_mul, mul_assoc, map_sum, AlgEquiv.commutes]
  | add y z hy hz =>
    simp only [map_add (f := _), Finsupp.add_apply, hy, hz, mul_add, Finset.sum_add_distrib]

theorem algEquiv_mulVec {R A : Type} [CommSemiring R] [CommRing A] [Algebra R A] {n : Type} [Fintype n]
    (s : A ≃ₐ[R] A) (U : Matrix n n A) (v : n → A) (i : n) :
    s ((U *ᵥ v) i) = (U.map s *ᵥ fun k => s (v k)) i :=
  RingHom.map_mulVec s.toRingEquiv.toRingHom U v i

theorem realises_of_mreal : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (S : Strat bk d) (M : FCrys l ↥(OL K)) (e : Module.Basis (Fin d) bk.prism.A (M.M bk.prism)), Framed S M e → ∀ (T : Type) [AddCommGroup T] [Module ℤ_[l] T] (ρ : ↥(GK K) → (T →ₗ[ℤ_[l]] T)) (b : Module.Basis (Fin d) ℤ_[l] T) (U : Matrix (Fin d) (Fin d) (WCb l)), MReal S (fun g => LinearMap.toMatrix b b (ρ g)) U → ∃ j : M.M (ainfObj K) →ₛₗ[(inclW l).comp (ainfId K).toRingHom] (WCb l ⊗[ℤ_[l]] T), Realises K M (ainfObj K) (ainfId K) T ρ j := by
  intro l _ K bk d S M e hF T _ _ ρ b U hU
  obtain ⟨b₀, hb₀⟩ := GlobalTheory.T.isSemilinearBaseChange_exists_basis_eq_image_of_basis _ _ _ _ _ (M.tr bk.ι) (M.tr_bc bk.ι) _ e
  let σ : (ainfObj K).A →+* WCb l := (inclW l).comp (ainfId K).toRingHom
  let cv : (Fin d → (ainfObj K).A) →ₛₗ[σ] (Fin d → WCb l) :=
    { toFun := fun v k => σ (v k)
      map_add' := fun v w => funext fun k => map_add σ (v k) (w k)
      map_smul' := fun a v => funext fun k => map_mul σ a (v k) }
  let j : M.M (ainfObj K) →ₛₗ[σ] (WCb l ⊗[ℤ_[l]] T) :=
    ((b.baseChange (WCb l)).equivFun.symm.toLinearMap ∘ₗ Matrix.toLin' U) ∘ₛₗ (cv ∘ₛₗ b₀.equivFun.toLinearMap)
  have hj : ∀ x, (b.baseChange (WCb l)).equivFun (j x) = U *ᵥ fun k => σ (b₀.equivFun x k) := fun x =>
    (b.baseChange (WCb l)).equivFun.apply_symm_apply _
  have hjs : ∀ c : Fin d → (ainfObj K).A, (b.baseChange (WCb l)).equivFun (j (b₀.equivFun.symm c)) = U *ᵥ fun k => σ (c k) := fun c => by
    rw [hj, LinearEquiv.apply_symm_apply]

  have hbc : SemiBC j := by
    letI := hU.unit.invertible
    let c := (Pi.basisFun (WCb l) (Fin d)).map ((Matrix.toLinearEquiv' U this).trans (b.baseChange (WCb l)).equivFun.symm)
    refine GlobalTheory.T.isSemilinearBaseChange_of_basis_maps_to_basis _ _ _ _ _ j (Fin d) b₀ c fun i => ?_
    apply (b.baseChange (WCb l)).equivFun.injective
    rw [hj]
    simp only [c, Module.Basis.map_apply, Pi.basisFun_apply, LinearEquiv.trans_apply,
      LinearEquiv.apply_symm_apply, Matrix.toLinearEquiv'_apply, Matrix.toLin'_apply]
    refine congrArg _ (funext fun k => ?_)
    rw [Module.Basis.equivFun_self]
    by_cases h : i = k
    · subst h; simp
    · simp [h, Pi.single_apply, Ne.symm h]
  have hu : IsUnit (inclW l (bk.ev bk.E)) := isUnit_inclW_of_span bk.span_ev
  obtain ⟨d₀, hd₀⟩ : ∃ d₀ : ↥(ainfObj K).I, ((d₀ : (ainfObj K).A) : Ainf l) = bk.ev bk.E :=
    ⟨⟨bk.ι.f bk.E, bk.ι.f_I _ (Ideal.mem_span_singleton_self _)⟩, rfl⟩
  have hne : (d₀ : (ainfObj K).A) ≠ 0 := fun h => hu.ne_zero (by rw [← hd₀, h]; exact map_zero (inclW l))
  refine ⟨j, Realises.of_generator (isAinf_ainfObj K) hbc d₀ (by rw [hd₀]; exact bk.span_ev) ?_ ?_⟩
  · intro x m k hfr
    have hx : x = ∑ i, b₀.equivFun x i • M.tr bk.ι (e i) := by
      simp_rw [← hb₀]; exact (b₀.sum_equivFun x).symm
    rw [hx] at hfr
    obtain ⟨r, hr⟩ := GlobalTheory.T.prismaticFCrystal_frobenius_pullback_basis l K bk d M e S.a S.A hF.Φ (ainfObj K) bk.ι d₀ (b₀.equivFun x) m k hfr
    haveI : IsDomain (ainfObj K).A := (ainfId K).toMulEquiv.isDomain
    haveI := Module.Free.of_basis b₀
    have h1 := sub_eq_zero.1 ((smul_eq_zero.1 hr).resolve_left (pow_ne_zero _ hne))
    simp_rw [← hb₀] at h1
    rw [← b₀.equivFun_symm_apply] at h1
    have h2 : σ (BK.hf bk.ι bk.E) ^ S.a • j m = σ (d₀ : (ainfObj K).A) ^ k •
        j (b₀.equivFun.symm ((S.A.map (BK.hf bk.ι)) *ᵥ fun i => (ainfObj K).D.φ (b₀.equivFun x i))) :=
      calc σ (BK.hf bk.ι bk.E) ^ S.a • j m = σ (BK.hf bk.ι bk.E ^ S.a) • j m := by rw [map_pow]
        _ = j (BK.hf bk.ι bk.E ^ S.a • m) := (j.map_smulₛₗ _ _).symm
        _ = j ((d₀ : (ainfObj K).A) ^ k • b₀.equivFun.symm ((S.A.map (BK.hf bk.ι)) *ᵥ
              fun i => (ainfObj K).D.φ (b₀.equivFun x i))) := congrArg j h1
        _ = σ ((d₀ : (ainfObj K).A) ^ k) • j (b₀.equivFun.symm ((S.A.map (BK.hf bk.ι)) *ᵥ
              fun i => (ainfObj K).D.φ (b₀.equivFun x i))) := j.map_smulₛₗ _ _
        _ = _ := congrArg (· • _) (map_pow σ _ _)
    suffices hs : σ (BK.hf bk.ι bk.E) ^ S.a • (σ (d₀ : (ainfObj K).A) ^ k •
        TensorProduct.map (frobW l).toLinearMap LinearMap.id (j x)) = σ (BK.hf bk.ι bk.E) ^ S.a • j m from
      (hu.pow S.a).smul_left_cancel.1 hs
    rw [h2]
    refine (smul_comm (σ (BK.hf bk.ι bk.E) ^ S.a) (σ (d₀ : (ainfObj K).A) ^ k) _).trans
      (congrArg (σ (d₀ : (ainfObj K).A) ^ k • ·) ?_)
    apply (b.baseChange (WCb l)).equivFun.injective
    have hz : (fun i => frobW l ((b.baseChange (WCb l)).equivFun (j x) i)) =
        U.map (frobW l) *ᵥ fun k => σ ((ainfObj K).D.φ (b₀.equivFun x k)) := by
      rw [hj]
      funext i
      refine (RingHom.map_mulVec (frobW l).toRingHom U _ i).trans ?_
      exact congrArg (fun v => (U.map (frobW l) *ᵥ v) i) (funext fun k => frobW_inclW (b₀.equivFun x k))
    have hc : (fun k => σ (((S.A.map (BK.hf bk.ι)) *ᵥ fun i => (ainfObj K).D.φ (b₀.equivFun x i)) k)) =
        S.A.map bk.evW *ᵥ fun k => σ ((ainfObj K).D.φ (b₀.equivFun x k)) := by
      funext k
      have hA : (S.A.map (BK.hf bk.ι)).map σ = S.A.map bk.evW := Matrix.ext fun _ _ => rfl
      exact (RingHom.map_mulVec σ _ _ k).trans
        (congrArg (fun A => (A *ᵥ fun k => σ ((ainfObj K).D.φ (b₀.equivFun x k))) k) hA)
    have hσE : σ (BK.hf bk.ι bk.E) = bk.evW bk.E := rfl
    refine ((b.baseChange (WCb l)).equivFun.map_smul _ _).trans ?_
    refine Eq.trans ?_ (hjs _).symm
    refine (congrArg (σ (BK.hf bk.ι bk.E) ^ S.a • ·) ((equivFun_frob b (j x)).trans hz)).trans ?_
    refine Eq.trans ?_ (congrArg (U *ᵥ ·) hc).symm
    exact (congrArg (fun t => t ^ S.a • (U.map (frobW l) *ᵥ _)) hσE).trans
      ((Matrix.smul_mulVec _ _ _).symm.trans
        ((congrArg (· *ᵥ _) hU.φ).trans (Matrix.mulVec_mulVec _ _ _).symm))
  · intro g x
    let h := (isAinf_ainfObj K).galHom g
    have hk : ∀ k, M.tr h (b₀ k) = ∑ i, S.ε bk.ι (h.comp bk.ι) i k • b₀ i := fun k =>
      (congrArg (M.tr h) (hb₀ k)).trans ((M.tr_comp h bk.ι (e k)).symm.trans
        ((hF.tr bk.ι (h.comp bk.ι) k).trans (Finset.sum_congr rfl fun i _ => congrArg _ (hb₀ i).symm)))
    have htr : M.tr h x = b₀.equivFun.symm ((S.ε bk.ι (h.comp bk.ι)) *ᵥ fun k => h.f (b₀.equivFun x k)) :=
      calc M.tr h x = M.tr h (∑ k, b₀.equivFun x k • b₀ k) := congrArg (M.tr h) (b₀.sum_equivFun x).symm
        _ = ∑ k, h.f (b₀.equivFun x k) • M.tr h (b₀ k) :=
          (map_sum (M.tr h) _ _).trans (Finset.sum_congr rfl fun k _ => (M.tr h).map_smulₛₗ _ _)
        _ = ∑ k, ∑ i, (h.f (b₀.equivFun x k) * S.ε bk.ι (h.comp bk.ι) i k) • b₀ i :=
          Finset.sum_congr rfl fun k _ => (congrArg _ (hk k)).trans
            (Finset.smul_sum.trans (Finset.sum_congr rfl fun i _ => smul_smul _ _ _))
        _ = ∑ i, (∑ k, S.ε bk.ι (h.comp bk.ι) i k * h.f (b₀.equivFun x k)) • b₀ i :=
          Finset.sum_comm.trans (Finset.sum_congr rfl fun i _ =>
            (Finset.sum_congr rfl fun k _ => congrArg (· • b₀ i) (mul_comm _ _)).trans Finset.sum_smul.symm)
        _ = _ := (b₀.equivFun_symm_apply _).symm
    apply (b.baseChange (WCb l)).equivFun.injective
    have hσ : ∀ a : (ainfObj K).A, σ a = inclW l a := fun a => rfl
    have hh : ∀ a : (ainfObj K).A, h.f a = Per.σA (g : GQ l) a := fun a => rfl
    have hL : (fun k => σ (((S.ε bk.ι (h.comp bk.ι)) *ᵥ fun k => h.f (b₀.equivFun x k)) k)) =
        (S.ε bk.ι (h.comp bk.ι)).map σ *ᵥ fun k => σ (h.f (b₀.equivFun x k)) :=
      funext fun k => RingHom.map_mulVec σ _ _ k
    have hR : (fun k => galW l (g : GQ l) ((b.baseChange (WCb l)).equivFun (j x) k)) =
        U.map (galW l (g : GQ l)) *ᵥ fun k => σ (h.f (b₀.equivFun x k)) :=
      funext fun i => by
        have h1 := congrArg (fun v : Fin d → WCb l => galW l (g : GQ l) (v i)) (hj x)
        have h2 := algEquiv_mulVec (galW l (g : GQ l)) U (fun k => σ (b₀.equivFun x k)) i
        have h3 : (fun k => galW l (g : GQ l) (σ (b₀.equivFun x k))) = fun k => σ (h.f (b₀.equivFun x k)) :=
          funext fun k => (congrArg (galW l (g : GQ l)) (hσ _)).trans ((galW_inclW (g : GQ l) (b₀.equivFun x k)).trans
            ((hσ _).symm.trans (congrArg σ (hh _).symm)))
        beta_reduce at h1 ⊢
        exact h1.trans (h2.trans (congrArg (fun v => (U.map (galW l (g : GQ l)) *ᵥ v) i) h3))
    have hg := hU.gal g
    refine ((congrArg (fun z => (b.baseChange (WCb l)).equivFun (j z)) htr).trans (hjs _)).trans ?_
    refine Eq.trans ?_ (equivFun_map b _ _ _).symm
    refine (congrArg (U *ᵥ ·) hL).trans (Eq.trans ?_ (congrArg (_ *ᵥ ·) hR).symm)
    exact (Matrix.mulVec_mulVec _ _ _).trans ((congrArg (· *ᵥ _) hg.symm).trans (Matrix.mulVec_mulVec _ _ _).symm)

end GlobalTheory.BSP.EtReal
end
end
