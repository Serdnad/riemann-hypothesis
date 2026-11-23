module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InvertibleSpanSingleton
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle557
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle573
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle001
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle558
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodRingsGaloisActionLawsFrobeniusComm
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAdicCompleteOfPowLe
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemBallOfGaugeLt
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle024
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem isUnit_δ_of_I_eq_span : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (B : Obj l R) (d : B.A),
    B.I = Ideal.span {d} → IsUnit (B.D.δ d) := by
  intro l hl R _ B d hI
  by_contra hu
  obtain ⟨m, hm, hdm⟩ := Ideal.exists_le_maximal (Ideal.span {B.D.δ d})
    (by rwa [Ne, Ideal.span_singleton_eq_top])
  have hδd : B.D.δ d ∈ m := hdm (Ideal.mem_span_singleton_self _)
  have hJ : JJ B ≤ m := by
    have h1 : JJ B ≤ (⊥ : Ideal B.A).jacobson := @IsAdicComplete.le_jacobson_bot _ _ _ B.complete
    exact h1.trans (sInf_le ⟨bot_le, hm⟩)
  have hlm : (l : B.A) ∈ m := hJ (Ideal.mem_sup_left (Ideal.mem_span_singleton_self _))
  have hdm' : d ∈ m := hJ (Ideal.mem_sup_right (by rw [hI]; exact Ideal.mem_span_singleton_self _))
  have hmem := B.l_mem
  rw [hI, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton_sup] at hmem
  obtain ⟨a, y, hy, hle⟩ := hmem
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hy
  have hl2 : 2 ≤ l := hl.out.two_le
  have hφ : B.D.φ d ∈ m ^ 2 := by
    rw [B.D.φ_eq]
    refine Ideal.add_mem _ ?_ ?_
    · have : d ^ l = d ^ 2 * d ^ (l - 2) := by rw [← pow_add]; congr 1; omega
      rw [this]; exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hdm' 2)
    · rw [pow_two]; exact Ideal.mul_mem_mul hlm hδd
  have hy2 : c * B.D.φ d ∈ m ^ (1 + 1) := Ideal.mul_mem_left _ _ hφ
  have hδy : B.D.δ (c * B.D.φ d) ∈ m := by
    simpa using GlobalTheory.T.delta_mem_ideal_pow_of_mem_pow_succ l B.A B.D m hlm 1 _ hy2
  have hδad : B.D.δ (a * d) ∈ m := by
    rw [B.D.δ_mul]
    refine Ideal.add_mem _ (Ideal.add_mem _ ?_ ?_) ?_
    · exact Ideal.mul_mem_left _ _ hδd
    · exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ hdm' _ hl.out.pos)
    · exact Ideal.mul_mem_left _ _ hδd
  have hsum : ∑ k ∈ Finset.Ioo 0 l, ((l.choose k / l : ℕ) : B.A) * (a * d) ^ k * (c * B.D.φ d) ^ (l - k) ∈ m :=
    Ideal.sum_mem _ fun k hk =>
      Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _
        (Ideal.pow_mem_of_mem _ (Ideal.mul_mem_left _ _ hdm') _ (Finset.mem_Ioo.1 hk).1))
  have hδl : B.D.δ (l : B.A) ∈ m := by
    rw [← hle, B.D.δ_add]
    exact Ideal.sub_mem _ (Ideal.add_mem _ hδad hδy) hsum
  exact (GlobalTheory.T.prime_not_mem_sq_and_delta_not_mem l B.A B.D m hm.ne_top hlm).2 hδl

end GlobalTheory.BSP
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.Prism.Rigid

theorem φ_mem_of_mem {l : ℕ} (hl : 0 < l) {A : Type} [CommRing A] (D : Delta l A) {m : Ideal A}
    (hlm : (l : A) ∈ m) {x : A} (hx : x ∈ m) : D.φ x ∈ m := by
  rw [D.φ_eq]
  exact Ideal.add_mem _ (Ideal.pow_mem_of_mem _ hx _ hl) (Ideal.mul_mem_right _ _ hlm)

theorem φ_mem_sq {l : ℕ} (hl : 0 < l) {A : Type} [CommRing A] (D : Delta l A) {m : Ideal A}
    (hlm : (l : A) ∈ m) {x : A} (hx : x ∈ m ^ 2) : D.φ x ∈ m ^ 2 := by
  have h : (m ^ 2).map D.φ ≤ m ^ 2 := by
    rw [Ideal.map_pow, sq, sq]
    have hm : m.map D.φ ≤ m := Ideal.map_le_iff_le_comap.2 fun y hy => φ_mem_of_mem hl D hlm hy
    exact Ideal.mul_mono hm hm
  exact h (Ideal.mem_map_of_mem _ hx)

theorem map_I_eq (l : ℕ) [hl : Fact l.Prime] (R : Type) [CommRing R] (B B' : Obj l R) (f : Hom B B') :
    B.I.map f.f = B'.I := by
  have hl0 : 0 < l := hl.out.pos
  have hNI : B.I.map f.f ≤ B'.I := Ideal.map_le_iff_le_comap.2 fun a ha => f.f_I a ha
  refine GlobalTheory.T.eq_of_le_invertible_of_not_le_maximal_mul B'.A B'.I (B.I.map f.f) B'.inv hNI ?_
  intro m hm hN

  have hjac : Ideal.span {(l : B'.A)} ⊔ B'.I ≤ m := by
    haveI := B'.complete
    refine le_trans (IsAdicComplete.le_jacobson_bot (Ideal.span {(l : B'.A)} ⊔ B'.I)) ?_
    exact sInf_le ⟨bot_le, hm⟩
  have hlm : (l : B'.A) ∈ m := hjac (Ideal.mem_sup_left (Ideal.mem_span_singleton_self _))
  have hIm : B'.I ≤ m := le_trans le_sup_right hjac
  have hN2 : B.I.map f.f ≤ m ^ 2 := by
    rw [sq]; exact le_trans hN (Ideal.mul_mono_right hIm)

  have hmap : B.I ⊔ B.I.map B.D.φ ≤ (m ^ 2).comap f.f := by
    refine sup_le (fun a ha => hN2 (Ideal.mem_map_of_mem _ ha)) ?_
    refine Ideal.map_le_iff_le_comap.2 fun a ha => ?_
    show f.f (B.D.φ a) ∈ m ^ 2
    rw [f.f_φ]
    exact φ_mem_sq hl0 B'.D hlm (hN2 (Ideal.mem_map_of_mem _ ha))
  have hl2 : (l : B'.A) ∈ m ^ 2 := by
    have := hmap B.l_mem
    simpa [map_natCast] using this
  exact (GlobalTheory.T.prime_not_mem_sq_and_delta_not_mem l B'.A B'.D m hm.ne_top hlm).1 hl2

end GlobalTheory.Prism.Rigid
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BcrisInv

theorem map_smul_matrix {R S : Type} [CommRing R] [CommRing S] {d : ℕ} (f : R →+* S) (a : R)
    (M : Matrix (Fin d) (Fin d) R) : (a • M).map f = f a • M.map f := by
  ext i j; simp

theorem invariant_unit : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (N d k : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (Y Y' : Matrix (Fin d) (Fin d) (Ainf l)) (ε : ↥(GK K) → Matrix (Fin d) (Fin d) (Ainf l)) (Q Q' : Matrix (Fin d) (Fin d) (_root_.Formalism.Per.Acris l)), Y * Y' = τ ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (Ainf l)) → (∀ g : ↥(GK K), τ ^ N • ((ρ g).val.map (_root_.Formalism.Per.zA l) * Y.map (_root_.Formalism.Per.σA (g : GQ l))) = _root_.Formalism.Per.σA (g : GQ l) τ ^ N • (Y * ε g)) → Q * Q' = (l : _root_.Formalism.Per.Acris l) ^ (2 * k) • (1 : Matrix (Fin d) (Fin d) (_root_.Formalism.Per.Acris l)) → (∀ g : ↥(GK K), (ε g).map (fun a => algebraMap (Ainf l) (_root_.Formalism.Per.Acris l) (WittVector.frobenius a)) * Q.map (sigA (g : GQ l)) = Q) → ∃ U : Matrix (Fin d) (Fin d) (_root_.Formalism.Per.Bcris l), IsUnit U ∧ ∀ g : ↥(GK K), (ρ g).val.map (_root_.Formalism.Per.zB l) * U.map (_root_.Formalism.Per.σB (g : GQ l)) = U := by
  intro l _ K bk τ hτ N d k ρ Y Y' ε Q Q' hYY hgal hQQ hε
  have hFφ : ∀ a : Ainf l, WittVector.frobenius a = _root_.Formalism.Per.φA l a := fun a => (GlobalTheory.RingBasics.φA_apply l a).symm
  set f : Ainf l →+* _root_.Formalism.Per.Bcris l := (_root_.Formalism.Per.aB l).comp (_root_.Formalism.Per.φA l) with hf
  set alg : _root_.Formalism.Per.Acris l →+* _root_.Formalism.Per.Bcris l := algebraMap (_root_.Formalism.Per.Acris l) (_root_.Formalism.Per.Bcris l) with halg
  obtain ⟨-, e, η, ⟨he1, he2⟩, hτe⟩ := hτ
  have hne : e ≠ 1 := by
    rintro rfl; apply he2; simp
  have hmu : IsUnit (_root_.Formalism.Per.aB l (WittVector.teichmuller l e - 1)) :=
    GlobalTheory.CrisLoc.unit_of_root_aB l e he1 hne
  have hw : IsUnit (f τ) := by
    have : f τ = _root_.Formalism.Per.aB l (η : Ainf l) * _root_.Formalism.Per.aB l (WittVector.teichmuller l e - 1) := by
      simp only [hf, RingHom.comp_apply, ← hFφ, hτe, map_mul]
    rw [this]; exact (η.isUnit.map _).mul hmu
  obtain ⟨W, hW⟩ := hw.pow N

  set A := Y.map f with hA
  set B := Q.map alg with hB
  refine ⟨((W⁻¹ : (_root_.Formalism.Per.Bcris l)ˣ) : _root_.Formalism.Per.Bcris l) • (A * B), ?_, ?_⟩
  ·
    have hB' : B * Q'.map alg = alg ((l : _root_.Formalism.Per.Acris l) ^ (2 * k)) • (1 : Matrix (Fin d) (Fin d) (_root_.Formalism.Per.Bcris l)) := by
      rw [hB, ← Matrix.map_mul, hQQ, map_smul_matrix, Matrix.map_one _ (map_zero _) (map_one _)]
    have hA' : A * Y'.map f = f τ ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (_root_.Formalism.Per.Bcris l)) := by
      rw [hA, ← Matrix.map_mul, hYY, map_smul_matrix, Matrix.map_one _ (map_zero _) (map_one _), map_pow]
    have hc : IsUnit (((W⁻¹ : (_root_.Formalism.Per.Bcris l)ˣ) : _root_.Formalism.Per.Bcris l) * alg ((l : _root_.Formalism.Per.Acris l) ^ (2 * k)) * f τ ^ (2 * N)) := by
      refine (W⁻¹.isUnit.mul ?_).mul (hw.pow _)
      have h := (isUnit_l_Bcris l).pow (2 * k)
      simpa [halg, map_pow, map_natCast] using h
    obtain ⟨c, hcv⟩ := hc
    set V := Q'.map alg * Y'.map f
    have hUV : (((W⁻¹ : (_root_.Formalism.Per.Bcris l)ˣ) : _root_.Formalism.Per.Bcris l) • (A * B)) * V = (c : _root_.Formalism.Per.Bcris l) • (1 : Matrix (Fin d) (Fin d) (_root_.Formalism.Per.Bcris l)) := by
      rw [hcv, smul_mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc B, hB', smul_mul_assoc, Matrix.one_mul,
        mul_smul_comm, hA', smul_smul, smul_smul, mul_assoc]
    have h1 : (((W⁻¹ : (_root_.Formalism.Per.Bcris l)ˣ) : _root_.Formalism.Per.Bcris l) • (A * B)) * (((c⁻¹ : (_root_.Formalism.Per.Bcris l)ˣ) : _root_.Formalism.Per.Bcris l) • V) = 1 := by
      rw [Matrix.mul_smul, hUV, smul_smul, Units.inv_mul, one_smul]
    exact ⟨⟨_, _, h1, mul_eq_one_comm.mp h1⟩, rfl⟩
  · intro g
    set σ := _root_.Formalism.Per.σB (g : GQ l) with hσ
    have hσaB : ∀ a : Ainf l, σ (_root_.Formalism.Per.aB l a) = _root_.Formalism.Per.aB l (_root_.Formalism.Per.σA (g : GQ l) a) :=
      (ActLaws.act_laws l).2.2.2.2.2.1 (g : GQ l)
    have hσf : ∀ a : Ainf l, σ (f a) = f (_root_.Formalism.Per.σA (g : GQ l) a) := fun a => by
      simp only [hf, RingHom.comp_apply, hσaB, ActLaws.φA_σA]
    have hfz : ∀ z : ℤ_[l], f (_root_.Formalism.Per.zA l z) = _root_.Formalism.Per.zB l z := fun z => by
      simp only [hf, RingHom.comp_apply, GlobalTheory.RingIface.zB_eq_aB_zA, (ActLaws.act_laws l).2.2.2.2.2.2.2.2.1 z]
    have hσalg : ∀ x : _root_.Formalism.Per.Acris l, σ (alg x) = alg (sigA (g : GQ l) x) :=
      (ActLaws.act_laws l).2.2.2.2.2.2.2.2.2.2.2.1 (g : GQ l)

    have hG := congrArg (fun M => M.map f) (hgal g)
    simp only [map_smul_matrix, Matrix.map_mul, Matrix.map_map, map_pow] at hG
    have e1 : (⇑f ∘ ⇑(_root_.Formalism.Per.zA l)) = ⇑(_root_.Formalism.Per.zB l) := funext hfz
    rw [e1, ← hσf] at hG

    have hE := congrArg (fun M => M.map alg) (hε g)
    simp only [Matrix.map_mul, Matrix.map_map] at hE
    have e2 : (⇑alg ∘ fun a => (algebraMap (Ainf l) (_root_.Formalism.Per.Acris l)) (WittVector.frobenius a)) = ⇑f := by
      funext a; simp only [Function.comp_apply, hFφ, hf, halg, RingHom.comp_apply, GlobalTheory.RingIface.aB_eq_alg]
    rw [e2] at hE

    have eA : A.map σ = Y.map (⇑f ∘ ⇑(_root_.Formalism.Per.σA (g : GQ l))) := by
      rw [hA, Matrix.map_map]; congr 1; funext a; exact hσf a
    have eB : B.map σ = Q.map (⇑alg ∘ ⇑(sigA (g : GQ l))) := by
      rw [hB, Matrix.map_map]; congr 1; funext a; exact hσalg a
    rw [map_smul_matrix, Matrix.map_mul, eA, eB]
    have hsW : σ ((W⁻¹ : (_root_.Formalism.Per.Bcris l)ˣ) : _root_.Formalism.Per.Bcris l) * σ (W : _root_.Formalism.Per.Bcris l) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    have hσW : σ (f τ) ^ N = σ (W : _root_.Formalism.Per.Bcris l) := by rw [hW, map_pow]
    rw [hσW, ← hW] at hG
    have hZ : (ρ g).val.map (_root_.Formalism.Per.zB l) * Y.map (⇑f ∘ ⇑(_root_.Formalism.Per.σA (g : GQ l))) =
        (((W⁻¹ : (_root_.Formalism.Per.Bcris l)ˣ) : _root_.Formalism.Per.Bcris l) * σ (W : _root_.Formalism.Per.Bcris l)) • (A * (ε g).map f) := by
      rw [← smul_smul, ← hG, smul_smul, Units.inv_mul, one_smul]
    rw [mul_smul_comm, ← Matrix.mul_assoc, hZ, smul_mul_assoc, Matrix.mul_assoc, hE, smul_smul, mul_left_comm, hsW,
      mul_one]

end GlobalTheory.BcrisInv
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BKLim.BetaBd

variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l}

theorem θ_σA_ev (bk : BK K) (g : ↥(GK K)) (s : bk.S) :
    Per.θ l (_root_.Formalism.Per.σA (g : GQ l) (bk.ev s)) = Per.θ l (bk.ev s) := by
  obtain ⟨r, hr⟩ := bk.str.surjective (Ideal.Quotient.mk _ s)
  rw [GlobalTheory.RingBasics.θ_σA, bk.θ_ev r s hr.symm]
  apply Subtype.ext
  rw [GlobalTheory.RingIface.sigO_coe]
  change _root_.Formalism.Per.σC (g : GQ l) (((r : ↥K.1) : Om l) : ℂ_[l]) = (((r : ↥K.1) : Om l) : ℂ_[l])
  rw [GlobalTheory.RingBasics.σC_coe, (IntermediateField.mem_fixingSubgroup_iff _ _).1 g.2 _ (r : ↥K.1).2]

theorem dvd_σA_ev_sub (bk : BK K) (g : ↥(GK K)) (s : bk.S) :
    bk.ev bk.E ∣ _root_.Formalism.Per.σA (g : GQ l) (bk.ev s) - bk.ev s := by
  rw [← Ideal.mem_span_singleton, bk.span_ev, RingHom.mem_ker, map_sub, θ_σA_ev, sub_self]

theorem exists_dvd_bound (u : OC l) (hu : u ≠ 0) : ∃ a : ℕ, ∀ (x y : OC l) (n : ℕ),
    x * u = (l : OC l) ^ n * y → a ≤ n → ∃ y' : OC l, x = (l : OC l) ^ (n - a) * y' := by
  have hu' : 0 < ‖(u : ℂ_[l])‖ := norm_pos_iff.2 (fun h => hu (Subtype.ext h))
  obtain ⟨a, ha⟩ : ∃ a : ℕ, ‖(l : ℂ_[l])‖ ^ a < ‖(u : ℂ_[l])‖ :=
    ((tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) GlobalTheory.RingBasics.norm_p_lt).eventually
      (gt_mem_nhds hu')).exists
  refine ⟨a, fun x y n h han => ?_⟩
  have hl0 : 0 < ‖(l : ℂ_[l])‖ := norm_pos_iff.2 GlobalTheory.RingBasics.p_ne_zero
  have hy : ‖(y : ℂ_[l])‖ ≤ 1 := (GlobalTheory.RingBasics.mem_OC _).1 y.2
  have h1 : ‖(x : ℂ_[l])‖ * ‖(u : ℂ_[l])‖ = ‖(l : ℂ_[l])‖ ^ n * ‖(y : ℂ_[l])‖ := by
    have := congrArg (fun t : OC l => ‖(t : ℂ_[l])‖) h
    simpa [norm_mul, norm_pow] using this
  have hn : ‖(l : ℂ_[l])‖ ^ n = ‖(l : ℂ_[l])‖ ^ (n - a) * ‖(l : ℂ_[l])‖ ^ a := by
    rw [← pow_add, Nat.sub_add_cancel han]
  have hx : ‖(x : ℂ_[l])‖ ≤ ‖(l : ℂ_[l])‖ ^ (n - a) := by
    have hpa : 0 < ‖(l : ℂ_[l])‖ ^ a := pow_pos hl0 a
    have hpn : 0 ≤ ‖(l : ℂ_[l])‖ ^ (n - a) := pow_nonneg hl0.le _
    by_contra hc
    push_neg at hc
    have : ‖(l : ℂ_[l])‖ ^ (n - a) * ‖(l : ℂ_[l])‖ ^ a < ‖(x : ℂ_[l])‖ * ‖(u : ℂ_[l])‖ :=
      mul_lt_mul'' hc ha hpn hpa.le
    have h2 : ‖(l : ℂ_[l])‖ ^ n * ‖(y : ℂ_[l])‖ ≤ ‖(l : ℂ_[l])‖ ^ n := mul_le_of_le_one_right (pow_nonneg hl0.le n) hy
    linarith
  have hm := (GlobalTheory.RingBasics.mem_span_pow_OC (n - a) x).2 hx
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hm
  obtain ⟨b, hb⟩ := hm
  exact ⟨b, by rw [← hb, mul_comm]⟩

end GlobalTheory.BKLim.BetaBd

end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
noncomputable section

namespace GlobalTheory.FlatKummer

theorem isPrimitiveRoot_of_seq {Ω : Type*} [Field Ω] (l : ℕ) [Fact l.Prime] (ζ : ℕ → Ω) (h0 : ζ 0 = 1)
    (hs : ∀ m, ζ (m + 1) ^ l = ζ m) (h1 : ζ 1 ≠ 1) (m : ℕ) : IsPrimitiveRoot (ζ m) (l ^ m) := by
  have hp : ∀ k, ζ k ^ l ^ k = 1 := by
    intro k
    induction k with
    | zero => simp [h0]
    | succ k ih => rw [pow_succ', pow_mul, hs, ih]
  have h1' : ∀ k, ζ (k + 1) ^ l ^ k = ζ 1 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', pow_mul, hs, ih]
  cases m with
  | zero => simp [h0]
  | succ m =>
    have h := orderOf_eq_prime_pow (x := ζ (m + 1)) (p := l) (n := m) (by rw [h1']; exact h1) (hp _)
    rw [← h]
    exact IsPrimitiveRoot.orderOf _

theorem exists_exponent_of_seq {Ω : Type*} [Field Ω] (l : ℕ) [Fact l.Prime] (ζ : ℕ → Ω) (h0 : ζ 0 = 1)
    (hs : ∀ m, ζ (m + 1) ^ l = ζ m) (h1 : ζ 1 ≠ 1) (z w : ℕ → Ω) (hz : ∀ m, z (m + 1) ^ l = z m)
    (hw : ∀ m, w (m + 1) ^ l = w m) (hwz : w 0 = z 0) :
    ∃ c : ℤ_[l], ∀ m, w m = ζ m ^ (PadicInt.toZModPow m c).val * z m := by
  have hne : ∀ m, NeZero (l ^ m) := fun m => ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hiter : ∀ (x : ℕ → Ω), (∀ m, x (m + 1) ^ l = x m) → ∀ m, x m ^ l ^ m = x 0 := by
    intro x hx m
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ', pow_mul, hx, ih]
  by_cases hz0 : z 0 = 0
  · refine ⟨0, fun m => ?_⟩
    have a : z m = 0 := pow_eq_zero_iff (pow_ne_zero _ (Fact.out : l.Prime).ne_zero) |>.1 ((hiter z hz m).trans hz0)
    have b : w m = 0 := pow_eq_zero_iff (pow_ne_zero _ (Fact.out : l.Prime).ne_zero) |>.1
      ((hiter w hw m).trans (hwz.trans hz0))
    rw [a, b, mul_zero]
  have hzm : ∀ m, z m ≠ 0 := fun m h => hz0 (by rw [← hiter z hz m, h, zero_pow (hne m).out])
  have hprim := isPrimitiveRoot_of_seq l ζ h0 hs h1
  have hpow : ∀ m a b : ℕ, ζ m ^ a = ζ m ^ b ↔ (a : ZMod (l ^ m)) = (b : ZMod (l ^ m)) := by
    intro m a b
    have hf : IsOfFinOrder (ζ m) := (hprim m).isOfFinOrder (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)
    rw [hf.pow_eq_pow_iff_modEq, ← (hprim m).eq_orderOf, ZMod.natCast_eq_natCast_iff]
  have e1 : ∀ m, ∃ a : ℕ, w m = ζ m ^ a * z m := by
    intro m
    obtain ⟨a, -, ha⟩ := (hprim m).eq_pow_of_pow_eq_one (ξ := w m / z m) (by
      rw [div_pow, hiter w hw, hiter z hz, hwz, div_self hz0])
    exact ⟨a, by rw [ha, div_mul_cancel₀ _ (hzm m)]⟩
  choose a ha using e1
  have hd : ∀ i, (l : ℤ) ^ i ∣ (a (i + 1) : ℤ) - (a i : ℤ) := by
    intro i
    have h2 := congrArg (· ^ l) (ha (i + 1))
    simp only [mul_pow, hw, hz] at h2
    rw [← pow_mul, mul_comm (a (i + 1)), pow_mul, hs, ha i] at h2
    have h3 := (hpow i _ _).mp (mul_right_cancel₀ (hzm i) h2)
    rw [ZMod.natCast_eq_natCast_iff] at h3
    exact_mod_cast h3.dvd
  refine ⟨PadicInt.ofIntSeq (fun i => (a i : ℤ)) (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub _ l hd),
    fun m => ?_⟩
  rw [PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub _ l hd, ha m]
  congr 1
  rw [hpow]
  simp

theorem rootT_succ_pow_l {l : ℕ} [Fact l.Prime] (e : _root_.Formalism.Per.Fl l) (m : ℕ) : rootT e (m + 1) ^ l = rootT e m := by
  rw [rootT, rootT, Function.iterate_succ_apply', ← map_pow, frobeniusEquiv_symm_pow_p]

theorem exists_kummer_flat : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (C : Core l), ∃ c : ↥(GK K) → ℤ_[l],
    (∀ (g : ↥(GK K)) (m : ℕ), rootT (_root_.Formalism.Per.σF (g : GQ l) bk.flat) m =
      rootT C.ε m ^ (PadicInt.toZModPow m (c g)).val * rootT bk.flat m) ∧ ∀ g, bk.FixFlat g → c g = 0 := by
  intro l _ K bk C
  obtain ⟨hz, -⟩ := GlobalTheory.BSP.rootT_flat_alg_and_fix l K bk
  choose z hz using hz
  have hinj : Function.Injective (algebraMap (Om l) ℂ_[l]) := (algebraMap (Om l) ℂ_[l]).injective
  have hz' : ∀ n, ((rootT bk.flat n : _root_.Formalism.Per.OC l) : ℂ_[l]) = algebraMap (Om l) ℂ_[l] (z n) := hz
  have hzs : ∀ m, z (m + 1) ^ l = z m := by
    intro m
    apply hinj
    rw [map_pow, ← hz', ← hz', ← rootT_succ_pow_l bk.flat m]
    push_cast
    rfl
  set r : ↥(OL K) := bk.str.symm (Ideal.Quotient.mk _ X) with hr
  have hθ : rootT bk.flat 0 = intToOC K r := by
    show bk.flat.untilt = _
    rw [← WittVector.fontaineTheta_teichmuller, ← bk.ev_X]
    exact bk.θ_ev r X (by rw [hr, RingEquiv.apply_symm_apply])
  have hz0 : z 0 = (((r : ↥K.1) : Om l)) := by
    apply hinj
    rw [← hz', hθ, coe_intToOC]
    rfl
  have good : ∀ g : ↥(GK K), ∃ c : ℤ_[l], ∀ m, rootT (_root_.Formalism.Per.σF (g : GQ l) bk.flat) m =
      rootT C.ε m ^ (PadicInt.toZModPow m c).val * rootT bk.flat m := by
    intro g
    have hfix : (g : GQ l) (z 0) = z 0 := by
      rw [hz0]
      exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 g.2 _ (r : ↥K.1).2
    obtain ⟨c, hc⟩ := exists_exponent_of_seq l C.ζ C.ζ_zero C.ζ_succ C.ζ_one z (fun m => (g : GQ l) (z m)) hzs
      (fun m => by rw [← map_pow, hzs]) hfix
    refine ⟨c, fun m => ?_⟩
    have hit : ∀ k : ℕ, ((frobeniusEquiv (_root_.Formalism.Per.Fl l) l).symm)^[k] (_root_.Formalism.Per.σF (g : GQ l) bk.flat) =
        _root_.Formalism.Per.σF (g : GQ l) (((frobeniusEquiv (_root_.Formalism.Per.Fl l) l).symm)^[k] bk.flat) := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, RingHom.map_frobeniusEquiv_symm]
    have hsig : rootT (_root_.Formalism.Per.σF (g : GQ l) bk.flat) m = _root_.Formalism.Per.σO (g : GQ l) (rootT bk.flat m) := by
      rw [rootT, hit, GlobalTheory.RingBasics.untilt_σF]; rfl
    rw [hsig]
    apply Subtype.ext
    have h1 : ((_root_.Formalism.Per.σO (g : GQ l) (rootT bk.flat m) : _root_.Formalism.Per.OC l) : ℂ_[l]) = _root_.Formalism.Per.σC (g : GQ l) (rootT bk.flat m : ℂ_[l]) :=
      by apply GlobalTheory.RingIface.sigO_coe
    have h2 : _root_.Formalism.Per.σC (g : GQ l) (algebraMap (Om l) ℂ_[l] (z m)) = algebraMap (Om l) ℂ_[l] ((g : GQ l) (z m)) :=
      GlobalTheory.RingBasics.σC_coe (g : GQ l) _
    push_cast
    rw [h1, hz', h2, hc m, map_mul, map_pow, C.ε_root]
  classical
  refine ⟨fun g => if bk.FixFlat g then 0 else (good g).choose, fun g m => ?_, fun g hg => by simp [hg]⟩
  by_cases hg : bk.FixFlat g
  · simp only [hg, if_true, map_zero, ZMod.val_zero, pow_zero, one_mul]
    rw [show _root_.Formalism.Per.σF (g : GQ l) bk.flat = bk.flat from hg]
  · simp only [hg, if_false]
    exact (good g).choose_spec m

end GlobalTheory.FlatKummer

end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory

theorem use₁₀ : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (n d : ℕ) (X Z : Matrix (Fin d) (Fin d) (_root_.Formalism.Per.BdRp l)), (∃ (k : ℕ) (s : Matrix (Fin d) (Fin d) bk.S), ∀ i j, aDp l (bk.ev (s i j)) - (l : _root_.Formalism.Per.BdRp l) ^ k * X i j ∈ _root_.Formalism.Per.FilP l n) → (∃ (k : ℕ) (s : Matrix (Fin d) (Fin d) bk.S), ∀ i j, aDp l (bk.ev (s i j)) - (l : _root_.Formalism.Per.BdRp l) ^ k * Z i j ∈ _root_.Formalism.Per.FilP l n) → ∃ (k : ℕ) (s : Matrix (Fin d) (Fin d) bk.S), ∀ i j, aDp l (bk.ev (s i j)) - (l : _root_.Formalism.Per.BdRp l) ^ k * (X * Z) i j ∈ _root_.Formalism.Per.FilP l n := by
  intro l _ K bk n d X Z ⟨k₁, s₁, h₁⟩ ⟨k₂, s₂, h₂⟩
  refine ⟨k₁ + k₂, s₁ * s₂, fun i j => ?_⟩
  have e : aDp l (bk.ev ((s₁ * s₂) i j)) - (l : _root_.Formalism.Per.BdRp l) ^ (k₁ + k₂) * (X * Z) i j
      = ∑ m, (aDp l (bk.ev (s₁ i m)) * (aDp l (bk.ev (s₂ m j)) - (l : _root_.Formalism.Per.BdRp l) ^ k₂ * Z m j)
        + (aDp l (bk.ev (s₁ i m)) - (l : _root_.Formalism.Per.BdRp l) ^ k₁ * X i m) * ((l : _root_.Formalism.Per.BdRp l) ^ k₂ * Z m j)) := by

    rw [Matrix.mul_apply, Matrix.mul_apply, map_sum, map_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [map_mul, map_mul, pow_add]
    ring
  rw [e]
  exact Ideal.sum_mem _ fun m _ => Ideal.add_mem _ (Ideal.mul_mem_left _ _ (h₂ m j)) (Ideal.mul_mem_right _ _ (h₁ i m))

end GlobalTheory
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.acris_disc_ringHom_ext_of_ainf : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (γ γ' : Per.Acris l →+* bk.DA bk.ρ₀), (∀ a : Ainf l, γ (algebraMap (Ainf l) (Per.Acris l) a) = γ' (algebraMap (Ainf l) (Per.Acris l) a)) → (∀ x, ‖γ x‖ ≤ 1) → (∀ x, ‖γ' x‖ ≤ 1) → γ = γ' := by
  first | exact @GlobalTheory.AcrisDiscExt.acris_disc_ext | exact GlobalTheory.AcrisDiscExt.acris_disc_ext | (intros; apply GlobalTheory.AcrisDiscExt.acris_disc_ext <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

theorem _root_.GlobalTheory.T.stratPeriodMatrix_exists_fixed_frobenius_solution : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d d' : ℕ) (S : Strat bk d) (S' : Strat bk d') (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (ρ' : ↥(GK K) → Matrix (Fin d') (Fin d') ℤ_[l]) (T : Matrix (Fin d) (Fin d) (WCb l)) (T' : Matrix (Fin d') (Fin d') (WCb l)), MReal S ρ T → MReal S' ρ' T' → ∀ f : Matrix (Fin d') (Fin d) ℤ_[l], (∀ g, f * ρ g = ρ' g * f) → ∃ X : Matrix (Fin d') (Fin d) (WCb l), T' * X = zW f * T ∧ (∀ g : ↥(GK K), bk.FixFlat g → X.map (galW l (g : GQ l)) = X) ∧ bk.evW bk.E ^ S.a • (S'.A.map bk.evW * X.map (frobW l)) = bk.evW bk.E ^ S'.a • (X * S.A.map bk.evW) := by
  first | exact @GlobalTheory.BSP.MReal.exists_fixed_frob | exact GlobalTheory.BSP.MReal.exists_fixed_frob | (intros; apply GlobalTheory.BSP.MReal.exists_fixed_frob <;> assumption)
end
