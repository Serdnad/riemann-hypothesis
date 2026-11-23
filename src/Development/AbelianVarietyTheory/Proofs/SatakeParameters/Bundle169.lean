module

public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConjugateSpaceJointEigenspacesPairCommISup
public import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.IsOrthCo
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HeckeLocalProduct.PvLocalSelf
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle006
public import Formalism.SatakeDualWeyl.Bundle001
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ElementaryDivisorsMulMinusculeTopTerm
public import Formalism.SharpRestriction.GrowthBounds.IsResidueClassZero
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle311
public import Formalism.LocalRingCardinality.SpanPowerMembership.GatTies
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ToLEInvApply
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle017
import Formalism.LocalToGlobal.Columns.CoefficientsModP.WeTransposeWordTransposeWord
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.IsComplRatCompl
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
import Formalism.SharpRestriction.GrowthBounds.FormalGroupSystem

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.conjugateSpace_jointEigenspaces_pairComm_iSup : ∀ (s : Bool) {E I : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (h : I → Module.End ℂ E), (Formalism.L2.Col.PairComm h → Formalism.L2.Col.PairComm (fun i => (Tw.map s (h i) : Module.End ℂ (Tw s E)))) ∧ (∀ Q : (I → ℂ) → Prop, Formalism.L2.Col.eigSum (fun i => (Tw.map s (h i) : Module.End ℂ (Tw s E))) Q = Tw.sub s (Formalism.L2.Col.eigSum h fun x => Q fun i => cj s (x i))) ∧ ∀ {C : Type} (Ec : C → Submodule ℂ E), Tw.sub s (⨆ c, Ec c) = ⨆ c, Tw.sub s (Ec c) := by
  first | exact @GlobalTheory.TwEig.pairComm_eigSum_sub_iSup | exact GlobalTheory.TwEig.pairComm_eigSum_sub_iSup | (intros; apply GlobalTheory.TwEig.pairComm_eigSum_sub_iSup <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat
open Formalism.UG (bc prV)
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.CompanLocP

section General

variable {R : Type*} [CommRing R] {W : Type*} [AddCommGroup W] [Module R W]

theorem mem_locP (p : Ideal R) [p.IsPrime] (M : Submodule R W) (x : W) :
    x ∈ Formalism.HermitianLatticesTheory.localization₂ p M ↔ ∃ s ∈ p.primeCompl, s • x ∈ M := Iff.rfl

theorem le_locP (p : Ideal R) [p.IsPrime] (M : Submodule R W) : M ≤ Formalism.HermitianLatticesTheory.localization₂ p M :=
  fun x hx => (mem_locP p M x).2 ⟨1, p.primeCompl.one_mem, by simpa using hx⟩

theorem localization_mono (p : Ideal R) [p.IsPrime] {M M₁ : Submodule R W} (h : M ≤ M₁) :
    Formalism.HermitianLatticesTheory.localization₂ p M ≤ Formalism.HermitianLatticesTheory.localization₂ p M₁ := by
  intro x hx
  obtain ⟨s, hs, hx⟩ := (mem_locP p M x).1 hx
  exact (mem_locP p M₁ x).2 ⟨s, hs, h hx⟩

theorem localization_le_localization_of_le_localization (p : Ideal R) [p.IsPrime] {M M₁ : Submodule R W}
    (h : M ≤ Formalism.HermitianLatticesTheory.localization₂ p M₁) : Formalism.HermitianLatticesTheory.localization₂ p M ≤ Formalism.HermitianLatticesTheory.localization₂ p M₁ := by
  intro x hx
  obtain ⟨s, hs, hx⟩ := (mem_locP p M x).1 hx
  obtain ⟨t, ht, hx'⟩ := (mem_locP p M₁ _).1 (h hx)
  refine (mem_locP p M₁ x).2 ⟨t * s, p.primeCompl.mul_mem ht hs, ?_⟩
  rw [mul_smul]
  exact hx'

end General

section Form

variable {E : Type} [Field E] [NumberField E] {N : ℕ} (σ : E →+* E) (J : Matrix (Fin N) (Fin N) E)

theorem hform_smul_right (x y : Fin N → E) (c : E) :
    Formalism.UG.hform σ J x (c • y) = c * Formalism.UG.hform σ J x y := by
  simp only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hform_smul_left (x y : Fin N → E) (c : E) :
    Formalism.UG.hform σ J (c • x) y = σ c * Formalism.UG.hform σ J x y := by
  simp only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, map_mul]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hform_add_left (x x' y : Fin N → E) :
    Formalism.UG.hform σ J (x + x') y = Formalism.UG.hform σ J x y + Formalism.UG.hform σ J x' y := by
  simp only [Formalism.UG.hform, Pi.add_apply, map_add (f := _), ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hform_zero_left (y : Fin N → E) : Formalism.UG.hform σ J 0 y = 0 := by
  simp [Formalism.UG.hform]

theorem ointSmul (s : 𝓞 E) (y : Fin N → E) : s • y = (s : E) • y :=
  (algebraMap_smul E s y).symm

theorem span_dualSet_le (q : Ideal (𝓞 E)) [q.IsPrime] (Λ Λ' : Submodule (𝓞 E) (Fin N → E)) (hΛ' : Λ'.FG)
    (h' : Λ' ≤ Formalism.HermitianLatticesTheory.localization₂ (q.comap (RingOfIntegers.mapRingHom σ)) Λ) :
    Submodule.span (𝓞 E) (dualSet σ J Λ) ≤
      Formalism.HermitianLatticesTheory.localization₂ q (Submodule.span (𝓞 E) (dualSet σ J Λ')) := by
  classical
  rw [Submodule.span_le]
  intro y hy
  obtain ⟨S, hS⟩ := hΛ'
  have hgen : ∀ g ∈ S, ∃ s ∈ q.primeCompl,
      ((s : 𝓞 E) : E) * Formalism.UG.hform σ J g y ∈ (algebraMap (𝓞 E) E).range := by
    intro g hg
    obtain ⟨t, ht, htg⟩ := (mem_locP _ _ _).1 (h' (hS ▸ Submodule.subset_span hg))
    refine ⟨RingOfIntegers.mapRingHom σ t, ht, ?_⟩
    have e : Formalism.UG.hform σ J (t • g) y = ((RingOfIntegers.mapRingHom σ t : 𝓞 E) : E) * Formalism.UG.hform σ J g y := by
      rw [ointSmul, hform_smul_left]
      rfl
    rw [← e]
    exact hy _ htg
  choose! f hf hf' using hgen
  refine (mem_locP _ _ _).2 ⟨∏ g ∈ S, f g, q.primeCompl.prod_mem (fun g hg => hf g hg), Submodule.subset_span ?_⟩
  intro x hx
  rw [← hS] at hx
  rw [ointSmul, hform_smul_right]
  induction hx using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem f hg
    rw [hc, mul_comm (f g) c, show ((c * f g : 𝓞 E) : E) = (c : E) * (f g : E) from map_mul (algebraMap (𝓞 E) E) c (f g), mul_assoc]
    exact Subring.mul_mem _ ⟨c, rfl⟩ (hf' g hg)
  | zero =>
    rw [hform_zero_left, mul_zero]
    exact Subring.zero_mem _
  | add x x' _ _ hx hx' =>
    rw [hform_add_left, mul_add]
    exact Subring.add_mem _ hx hx'
  | smul c x _ hx =>
    rw [ointSmul, hform_smul_left, mul_left_comm]
    exact Subring.mul_mem _ ⟨RingOfIntegers.mapRingHom σ c, rfl⟩ hx

end Form

theorem locP_companion_le {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (sp : Spaces R F E) {N : ℕ} (J : Matrix (Fin N) (Fin N) E) (a : 𝓞 E) (q : Ideal (𝓞 E)) [q.IsPrime]
    (Λ Λ' : Submodule (𝓞 E) (Fin N → E)) (hΛ' : Λ'.FG)
    (h : Formalism.HermitianLatticesTheory.localization₂ q Λ = Formalism.HermitianLatticesTheory.localization₂ q Λ')
    (h' : Formalism.HermitianLatticesTheory.localization₂ (q.comap (RingOfIntegers.mapRingHom (sp.cm.sig : E →+* E))) Λ =
      Formalism.HermitianLatticesTheory.localization₂ (q.comap (RingOfIntegers.mapRingHom (sp.cm.sig : E →+* E))) Λ') :
    Formalism.HermitianLatticesTheory.localization₂ q (compan (sp := sp) J a Λ) ≤ Formalism.HermitianLatticesTheory.localization₂ q (compan (sp := sp) J a Λ') := by
  apply localization_le_localization_of_le_localization
  unfold compan
  refine sup_le ((le_locP q Λ).trans (h.le.trans (localization_mono q le_sup_left))) ?_
  refine Submodule.smul_le.2 fun r hr m hm => ?_
  have hd := span_dualSet_le (sp.cm.sig : E →+* E) J q Λ Λ' hΛ' ((le_locP _ Λ').trans h'.symm.le) hm
  obtain ⟨s, hs, hsm⟩ := (mem_locP _ _ _).1 hd
  refine (mem_locP _ _ _).2 ⟨s, hs, ?_⟩
  rw [smul_comm]
  exact Submodule.mem_sup_right (Submodule.smul_mem_smul hr hsm)

theorem locP_companion_eq : ∀ {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (sp : Spaces R F E) {N : ℕ} (J : Matrix (Fin N) (Fin N) E) (a : 𝓞 E) (q : Ideal (𝓞 E)) [q.IsPrime]
    (Λ Λ' : Submodule (𝓞 E) (Fin N → E)), Λ.FG → Λ'.FG →
    Formalism.HermitianLatticesTheory.localization₂ q Λ = Formalism.HermitianLatticesTheory.localization₂ q Λ' →
    Formalism.HermitianLatticesTheory.localization₂ (q.comap (RingOfIntegers.mapRingHom (sp.cm.sig : E →+* E))) Λ =
      Formalism.HermitianLatticesTheory.localization₂ (q.comap (RingOfIntegers.mapRingHom (sp.cm.sig : E →+* E))) Λ' →
    Formalism.HermitianLatticesTheory.localization₂ q (compan (sp := sp) J a Λ) = Formalism.HermitianLatticesTheory.localization₂ q (compan (sp := sp) J a Λ') := by
  intro R F E _ _ _ _ _ _ sp N J a q _ Λ Λ' hΛ hΛ' h h'
  exact le_antisymm (locP_companion_le sp J a q Λ Λ' hΛ' h h') (locP_companion_le sp J a q Λ' Λ hΛ h.symm h'.symm)

end GlobalTheory.CompanLocP

end
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct

noncomputable section

namespace GlobalTheory.HeckeFinVal

open Neutral.B1 Formalism.L2.Host PI.HeckeProdW

theorem idele_ext {L : Type} [Field L] [NumberField L] {a c : Ideles L}
    (h1 : ∀ w, pw w a = pw w c) (h2 : ∀ v, pv v a = pv v c) : a = c :=
  Units.ext (Prod.ext (funext fun w => h1 w) (Subtype.ext (funext fun v => h2 v)))

theorem loc_eq_val_zpow {L : Type} [Field L] [NumberField L] (χ : HChar L) (P : HeightOneSpectrum (𝓞 L))
    (hP : χ.UnrAt P) (x : (P.adicCompletion L)ˣ) : ∃ k : ℤ, χ.loc P x = χ.val P ^ k := by
  have hx0 : Valued.v (x : P.adicCompletion L) ≠ 0 := by simp
  set m : ℤ := WithZero.log (Valued.v (x : P.adicCompletion L)) with hm
  have hxm : Valued.v (x : P.adicCompletion L) = WithZero.exp m := (WithZero.exp_log hx0).symm
  set ϖ : (P.adicCompletion L)ˣ := atFin P (unif P) with hϖ
  have hϖv : Valued.v (ϖ : P.adicCompletion L) = WithZero.exp (-1 : ℤ) := unif_spec P
  refine ⟨-m, ?_⟩
  have hu : IsUnitAt P (x * ϖ ^ m) := by
    unfold IsUnitAt
    rw [Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, hxm, hϖv, ← WithZero.exp_zsmul,
      ← WithZero.exp_add]
    simp
  have h3 := hP _ hu
  rw [map_mul, map_zpow, mul_eq_one_iff_eq_inv, ← zpow_neg] at h3
  exact h3

theorem eq_prod_val_zpow : ∀ {L : Type} [Field L] [NumberField L] (χ : Formalism.L2.Host.HChar L) (T : Finset (HeightOneSpectrum (𝓞 L)))
    (b : Neutral.B1.Ideles L), Formalism.L2.Host.IsFinIdele b → (∀ P, P ∉ T → (b : AdeleRing (𝓞 L) L).2 P = 1) →
    (∀ P ∈ T, χ.UnrAt P) → ∃ n : HeightOneSpectrum (𝓞 L) → ℤ, χ.1 b = ∏ P ∈ T, χ.val P ^ n P := by
  intro L _ _ χ T b hb hout hunr
  classical
  let u : ∀ P : HeightOneSpectrum (𝓞 L), (P.adicCompletion L)ˣ := fun P =>
    ⟨pv P b, pv P b⁻¹, by rw [← map_mul, mul_inv_cancel, map_one], by rw [← map_mul, inv_mul_cancel, map_one]⟩
  have hdec : b = ∏ P ∈ T, localIdele L P (u P) := by
    refine idele_ext (fun w => ?_) (fun v => ?_)
    · rw [map_prod]
      rw [Finset.prod_eq_one fun P _ => pw_local w P (u P)]
      exact hb w
    · rw [map_prod]
      by_cases hv : v ∈ T
      · rw [Finset.prod_eq_single v]
        · rw [pv_local_self]
        · intro P _ hPv
          exact pv_local_ne P v (Ne.symm hPv) _
        · intro h; exact absurd hv h
      · rw [Finset.prod_eq_one fun P hP => pv_local_ne P v (fun e => hv (e ▸ hP)) _]
        exact hout v hv
  have hk : ∀ P ∈ T, ∃ k : ℤ, χ.loc P (u P) = χ.val P ^ k := fun P hP => loc_eq_val_zpow χ P (hunr P hP) (u P)
  choose! n hn using hk
  refine ⟨n, ?_⟩
  rw [hdec, map_prod]
  exact Finset.prod_congr rfl fun P hP => hn P hP

end GlobalTheory.HeckeFinVal
end
end

section

open IsDedekindDomain NumberField Matrix

noncomputable section

namespace GlobalTheory.Hk3.MinuscTopLocal

theorem ov_eq (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    Formalism.UG.Ov F v = Formalism.UG.intL (v.adicCompletion F) := by
  ext x
  exact (HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 F) (K := F) v).trans Iff.rfl

theorem zpow_int {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)}
    {ϖ : v.adicCompletion F} (hϖ : Formalism.UG.IsUnifV F v ϖ) (m : ℤ) :
    ϖ ^ m ∈ Formalism.UG.intL (v.adicCompletion F) ↔ 0 ≤ m := by
  rw [← ov_eq]
  show ϖ ^ m ∈ v.adicCompletionIntegers F ↔ 0 ≤ m
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_zpow₀, hϖ, ← WithZero.coe_zpow,
    ← WithZero.coe_one, WithZero.coe_le_coe, ← ofAdd_zsmul, ← ofAdd_zero, Multiplicative.ofAdd_le,
    smul_eq_mul]
  omega

def dU {L : Type} [Field L] {n : ℕ} {ϖ : L} (h0 : ϖ ≠ 0) (e : Fin n → ℤ) : GL (Fin n) L where
  val := Matrix.diagonal fun i => ϖ ^ e i
  inv := Matrix.diagonal fun i => ϖ ^ (-e i)
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext i; rw [← zpow_add₀ h0]; simp
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext i; rw [← zpow_add₀ h0]; simp

theorem intM_mul {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}
    {A B : Matrix (Fin n) (Fin n) L} (hA : ∀ i j, A i j ∈ Formalism.UG.intL L) (hB : ∀ i j, B i j ∈ Formalism.UG.intL L) :
    ∀ i j, (A * B) i j ∈ Formalism.UG.intL L := fun i j => by
  rw [Matrix.mul_apply]
  exact sum_mem fun l _ => mul_mem (hA _ _) (hB _ _)

theorem intM_diag {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} {n : ℕ}
    {ϖ : v.adicCompletion F} (hϖ : Formalism.UG.IsUnifV F v ϖ) {e : Fin n → ℤ} (he : ∀ i, 0 ≤ e i) :
    ∀ i j, (Matrix.diagonal fun i => ϖ ^ e i) i j ∈ Formalism.UG.intL (v.adicCompletion F) := fun i j => by
  rw [Matrix.diagonal_apply]
  split_ifs with h
  · exact (zpow_int hϖ _).2 (he i)
  · exact zero_mem _

theorem unif_ne_zero {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)}
    {ϖ : v.adicCompletion F} (hϖ : Formalism.UG.IsUnifV F v ϖ) : ϖ ≠ 0 := by
  intro h
  rw [Formalism.UG.IsUnifV, h, map_zero] at hϖ
  exact WithZero.zero_ne_coe hϖ

theorem cartan_top_step : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) (ϖ : v.adicCompletion F), Formalism.UG.IsUnifV F v ϖ → ∀ (d : Fin n → ℤ) (k : ℕ), Antitone d → (∀ i, 0 ≤ d i) → (∀ i : Fin n, 0 < d i ↔ (i : ℕ) < k) → ∀ a₁ ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov F v), ∀ a₂ ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov F v), ∀ a₃ ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov F v), ∀ d' : Fin n → ℤ, Antitone d' → ∀ k₁ ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov F v), ∀ k₂ ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov F v), (a₁ : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * Formalism.UG.diagPow F v ϖ (fun i => if 0 < d i then d i - 1 else d i) * (a₂ : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * Formalism.UG.diagPow F v ϖ (fun i => if (i : ℕ) < k then 1 else 0) * (a₃ : Matrix (Fin n) (Fin n) (v.adicCompletion F)) = (k₁ : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * Formalism.UG.diagPow F v ϖ d' * (k₂ : Matrix (Fin n) (Fin n) (v.adicCompletion F)) → (∀ i, 0 ≤ d' i) ∧ (d' = d ∨ (∑ i, d' i = ∑ i, d i ∧ ∑ i, d' i ^ 2 < ∑ i, d i ^ 2)) := by
  intro F _ _ v n ϖ hϖ d k hd hd0 hk a₁ ha₁ a₂ ha₂ a₃ ha₃ d' hd' k₁ hk₁ k₂ hk₂ e
  have h0 : ϖ ≠ 0 := unif_ne_zero hϖ
  rw [ov_eq] at ha₁ ha₂ ha₃ hk₁ hk₂
  have hm0 : ∀ i, 0 ≤ (fun i => if 0 < d i then d i - 1 else d i) i := fun i => by
    have := hd0 i; dsimp only; split_ifs <;> omega
  have hw0 : ∀ i : Fin n, 0 ≤ (fun i : Fin n => if (i : ℕ) < k then (1 : ℤ) else 0) i := fun i => by
    dsimp only; split_ifs <;> omega
  have hG : a₁ * dU h0 (fun i => if 0 < d i then d i - 1 else d i) * a₂ *
      dU h0 (fun i : Fin n => if (i : ℕ) < k then (1 : ℤ) else 0) * a₃ = k₁ * dU h0 d' * k₂ :=
    Units.ext (by simp only [Units.val_mul]; exact e)
  have hD : k₁⁻¹ * (a₁ * dU h0 (fun i => if 0 < d i then d i - 1 else d i) * a₂ *
      dU h0 (fun i : Fin n => if (i : ℕ) < k then (1 : ℤ) else 0) * a₃) * k₂⁻¹ = dU h0 d' := by
    rw [hG]; group
  have hd'0 : ∀ i, 0 ≤ d' i := by
    intro i
    have hI : ∀ a b, ((k₁⁻¹ * (a₁ * dU h0 (fun i => if 0 < d i then d i - 1 else d i) * a₂ *
        dU h0 (fun i : Fin n => if (i : ℕ) < k then (1 : ℤ) else 0) * a₃) * k₂⁻¹ : GL (Fin n) _) :
          Matrix (Fin n) (Fin n) _) a b ∈ Formalism.UG.intL (v.adicCompletion F) := by
      simp only [Units.val_mul]
      refine intM_mul (intM_mul (GlobalTheory.Hk3.MinuscTop.glint_entry (inv_mem hk₁)) ?_)
        (GlobalTheory.Hk3.MinuscTop.glint_entry (inv_mem hk₂))
      refine intM_mul (intM_mul (intM_mul (intM_mul (GlobalTheory.Hk3.MinuscTop.glint_entry ha₁) ?_)
        (GlobalTheory.Hk3.MinuscTop.glint_entry ha₂)) ?_) (GlobalTheory.Hk3.MinuscTop.glint_entry ha₃)
      · exact intM_diag hϖ hm0
      · exact intM_diag hϖ hw0
    have := hI i i
    rw [hD] at this
    change (Matrix.diagonal fun i => ϖ ^ d' i) i i ∈ _ at this
    rw [Matrix.diagonal_apply_eq] at this
    exact (zpow_int hϖ _).1 this
  obtain ⟨dN, hdN⟩ : ∃ f : Fin n → ℕ, ∀ i, (f i : ℤ) = d i :=
    ⟨fun i => (d i).toNat, fun i => Int.toNat_of_nonneg (hd0 i)⟩
  obtain ⟨d'N, hd'N⟩ : ∃ f : Fin n → ℕ, ∀ i, (f i : ℤ) = d' i :=
    ⟨fun i => (d' i).toNat, fun i => Int.toNat_of_nonneg (hd'0 i)⟩
  have hdA : Antitone dN := fun i j h => by have := hd h; have := hdN i; have := hdN j; omega
  have hd'A : Antitone d'N := fun i j h => by have := hd' h; have := hd'N i; have := hd'N j; omega
  have hkN : ∀ i : Fin n, 0 < dN i ↔ (i : ℕ) < k := fun i => by rw [← hk i, ← hdN i]; omega
  have hg : ∃ l₁ ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL (v.adicCompletion F)),
      ∃ l₂ ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL (v.adicCompletion F)),
      ((l₁ * (a₁ * dU h0 (fun i => if 0 < d i then d i - 1 else d i) * a₂) * l₂ : GL (Fin n) _) :
        Matrix (Fin n) (Fin n) _) = Matrix.diagonal fun i => ϖ ^ (dN i - 1) := by
    refine ⟨a₁⁻¹, inv_mem ha₁, a₂⁻¹, inv_mem ha₂, ?_⟩
    have : a₁⁻¹ * (a₁ * dU h0 (fun i => if 0 < d i then d i - 1 else d i) * a₂) * a₂⁻¹ =
        dU h0 (fun i => if 0 < d i then d i - 1 else d i) := by group
    rw [this]
    change (Matrix.diagonal fun i => ϖ ^ (if 0 < d i then d i - 1 else d i)) = _
    congr 1; funext i
    rw [← zpow_natCast]; congr 1
    have := hdN i
    split_ifs <;> omega
  have ha : ∃ l₁ ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL (v.adicCompletion F)),
      ∃ l₂ ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL (v.adicCompletion F)),
      ((l₁ * (dU h0 (fun i : Fin n => if (i : ℕ) < k then (1 : ℤ) else 0) * a₃) * l₂ : GL (Fin n) _) :
        Matrix (Fin n) (Fin n) _) = Matrix.diagonal fun i : Fin n => if (i : ℕ) < k then ϖ else 1 := by
    refine ⟨1, one_mem _, a₃⁻¹, inv_mem ha₃, ?_⟩
    have : 1 * (dU h0 (fun i : Fin n => if (i : ℕ) < k then (1 : ℤ) else 0) * a₃) * a₃⁻¹ =
        dU h0 (fun i : Fin n => if (i : ℕ) < k then (1 : ℤ) else 0) := by group
    rw [this]
    change (Matrix.diagonal fun i : Fin n => ϖ ^ (if (i : ℕ) < k then (1 : ℤ) else 0)) = _
    congr 1; funext i
    split_ifs <;> simp
  have hga : ∃ l₁ ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL (v.adicCompletion F)),
      ∃ l₂ ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL (v.adicCompletion F)),
      ((l₁ * ((a₁ * dU h0 (fun i => if 0 < d i then d i - 1 else d i) * a₂) *
        (dU h0 (fun i : Fin n => if (i : ℕ) < k then (1 : ℤ) else 0) * a₃)) * l₂ : GL (Fin n) _) :
        Matrix (Fin n) (Fin n) _) = Matrix.diagonal fun i => ϖ ^ d'N i := by
    refine ⟨k₁⁻¹, inv_mem hk₁, k₂⁻¹, inv_mem hk₂, ?_⟩
    rw [← mul_assoc (a₁ * _ * a₂), hD]
    change (Matrix.diagonal fun i => ϖ ^ d' i) = _
    congr 1; funext i
    rw [← hd'N i, zpow_natCast]
  have key := GlobalTheory.Hk3.MinuscTop.elemDiv_mul_minuscule (v.adicCompletion F) ϖ n hϖ dN k hdA hkN _ _ hg ha
    d'N hd'A hga
  refine ⟨hd'0, ?_⟩
  have s1 : ∑ i, d' i = ((∑ i, d'N i : ℕ) : ℤ) := by
    push_cast; exact Finset.sum_congr rfl fun i _ => (hd'N i).symm
  have s2 : ∑ i, d i = ((∑ i, dN i : ℕ) : ℤ) := by
    push_cast; exact Finset.sum_congr rfl fun i _ => (hdN i).symm
  have s3 : ∑ i, d' i ^ 2 = ((∑ i, d'N i ^ 2 : ℕ) : ℤ) := by
    push_cast; exact Finset.sum_congr rfl fun i _ => by rw [hd'N i]
  have s4 : ∑ i, d i ^ 2 = ((∑ i, dN i ^ 2 : ℕ) : ℤ) := by
    push_cast; exact Finset.sum_congr rfl fun i _ => by rw [hdN i]
  rcases key with h | ⟨h1, h2⟩
  · left; funext i; rw [← hd'N i, ← hdN i, h]
  · right
    rw [s1, s2, s3, s4]
    exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩

end GlobalTheory.Hk3.MinuscTopLocal
end
end

section

noncomputable section

namespace GlobalTheory.TwU.Served

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU Classical NumberField

theorem hP_ne_zero (D : D7) (p : ℕ) (hp : p.Prime) (hc : IsResidueClassZero D p) (hn : HNeZero D.host p) : hP D p ≠ 0 := by
  obtain ⟨P, hP', hL, σ, hσ⟩ := Formalism.BasicNotions.Examples₂.LevelValuationRings.exists_frob D.host p hp hc
  have hne : ∃ g, g ∈ frobSet D p := ⟨_, P, hP', hL, σ, hσ, rfl⟩
  obtain ⟨P₂, h1, h2, σ₂, hσ₂, he⟩ := Classical.epsilon_spec hne
  have h3 := @HNeZero.ne_one _ _ _ hn P₂ h1 h2 σ₂ hσ₂
  intro h0
  apply h3
  rw [he]
  have h4 := Formalism.HC.Frame.iota_iotaInv D.R.toFrame (Classical.epsilon (fun g => g ∈ frobSet D p)).2
  unfold hP at h0
  rw [h0, Formalism.HC.Frame.iota_zero] at h4
  exact h4.symm

theorem jacobi_eq_neg_one (D : D7) (p : ℕ) (hp : p.Prime) (hc : IsResidueClassZero D p) :
    jacobiSym (-(D.host.d : ℤ)) p = -1 := by
  obtain ⟨h2, hq, hd, hjd, -⟩ := Formalism.BasicNotions.Examples₂.LevelValuationRings.of_cls D.host p hc
  have : NeZero p := ⟨hp.ne_zero⟩
  have hcop : (-(D.host.d : ℤ)).gcd (p : ℤ) = 1 := by
    rw [Int.neg_gcd, Int.gcd_natCast_natCast]
    exact (Nat.coprime_primes D.host.hyp.2.1 hp).2 (Ne.symm hd)
  rcases jacobiSym.trichotomy (-(D.host.d : ℤ)) p with h | h | h
  · exact absurd hcop (jacobiSym.eq_zero_iff_not_coprime.1 h)
  · exact absurd h hjd
  · exact h

theorem coprime_absNorm_ccK (D : D7) (p : ℕ) (hp : p.Prime) (hc : IsResidueClassZero D p) :
    Nat.Coprime (Ideal.absNorm D.host.ccK) p := by
  obtain ⟨-, -, -, hjd, -⟩ := Formalism.BasicNotions.Examples₂.LevelValuationRings.of_cls D.host p hc
  refine Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2 fun h => ?_)
  obtain ⟨P, hpP, hdvd⟩ := GlobalTheory.HalfCompare.exists_place_of_dvd_absNorm hp D.host.ccK h
  obtain ⟨hNP, hj⟩ := D.host.ccK_split P.asIdeal P.isPrime (Ideal.le_of_dvd hdvd)
  obtain ⟨l, hl, hlP⟩ := GlobalTheory.HalfCompare.exists_prime_under P
  have hlp : l = p := (Nat.prime_dvd_prime_iff_eq hl hp).1 ((hlP p).1 hpP)
  have hlN : l = Ideal.absNorm P.asIdeal :=
    (Nat.prime_dvd_prime_iff_eq hl hNP).1 ((hlP _).1 (Ideal.absNorm_mem P.asIdeal))
  rw [← hlN, hlp] at hj
  exact hjd hj

theorem served_facts : ∀ (D : D7) (p : ℕ), p.Prime → IsResidueClassZero D p → HNeZero D.host p →
    hP D p ≠ 0 ∧ jacobiSym (-(D.host.d : ℤ)) p = -1 ∧ Nat.Coprime (Ideal.absNorm D.host.ccK) p :=
  fun D p hp hc hn => ⟨hP_ne_zero D p hp hc hn, jacobi_eq_neg_one D p hp hc, coprime_absNorm_ccK D p hp hc⟩

end GlobalTheory.TwU.Served
end
end
