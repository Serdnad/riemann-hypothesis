module

public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle003
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle007
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsValCharTwist
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1376
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle230
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalVolumeLift
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1473
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1546
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1182
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1960
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.Radical.NatInt
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
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalZero
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle047
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle002
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IMemSiegel
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SqStep

theorem gbig_three {Q₁ Q₂ Q₃ Q : GP} (h₁ : GBig Q₁) (h₂ : GBig Q₂) (h₃ : GBig Q₃)
    (H : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData Lc sc) (μ₀ : T) (C x b : ℝ),
      Q₁ G μ₀ C x b → Q₂ G μ₀ C x b → Q₃ G μ₀ C x b → Q G μ₀ C x b) : GBig Q := by
  obtain ⟨F₁, h₁⟩ := h₁
  obtain ⟨F₂, h₂⟩ := h₂
  obtain ⟨F₃, h₃⟩ := h₃
  refine ⟨max F₁ (max F₂ F₃), fun ε CF hCF => ?_⟩
  obtain ⟨C₁, x₁, k₁⟩ := h₁ ε CF (le_trans (le_max_left _ _) hCF)
  obtain ⟨C₂, x₂, k₂⟩ := h₂ ε CF (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hCF)
  obtain ⟨C₃, x₃, k₃⟩ := h₃ ε CF (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hCF)
  refine ⟨max C₁ (max C₂ C₃), max x₁ (max x₂ x₃), fun C hC D large₂ he hx hR T Lc μ₀ hL G => H G μ₀ C _ _ ?_ ?_ ?_⟩
  · exact k₁ C (le_trans (le_max_left _ _) hC) D large₂ he (le_trans (le_max_left _ _) hx) hR T Lc μ₀ hL G
  · exact k₂ C (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hC) D large₂ he
      (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx) hR T Lc μ₀ hL G
  · exact k₃ C (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hC) D large₂ he
      (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx) hR T Lc μ₀ hL G

end GlobalTheory.SqStep

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StageConv

theorem m_le_of_size {D : D7} {large₂ : SizeData₂ D} (h : GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows large₂) : D.R.m ≤ D.R.r + 1 := by
  have h4 : D.R.m ^ 4 ≤ D.R.f := h.2.2.1
  have hm : 44 ≤ D.R.m := h.2.2.2.1
  have hfm : D.R.f * D.R.m ≤ (D.R.r + 1) ^ 3 := h.2.2.2.2.2.2.1
  by_contra hc
  push_neg at hc
  have h1 : (D.R.r + 1) ^ 3 < D.R.m ^ 3 := Nat.pow_lt_pow_left hc (by norm_num)
  have h2 : D.R.m ^ 3 ≤ D.R.m ^ 4 * D.R.m := by
    calc D.R.m ^ 3 ≤ D.R.m ^ 5 := Nat.pow_le_pow_right (by omega) (by norm_num)
      _ = D.R.m ^ 4 * D.R.m := by ring
  have h3 : D.R.m ^ 4 * D.R.m ≤ D.R.f * D.R.m := Nat.mul_le_mul_right _ h4
  omega

theorem rank_lt {D : D7} {i j : Fin D.R.m} {p q : ℕ} {A A' WW : HSp D} (hmr : D.R.m ≤ D.R.r + 1)
    (hp : p ≤ pp D j) (hq : q ≤ qq D j) (hA : A.rank + 2 * pp D j = rankV D (i + 1) (j + 1) + 2 * p)
    (hA' : A'.rank + 2 * qq D j = rankV D i j + 2 * q) (hd : A.rank + A'.rank = WW.rank) :
    WW.rank < 2 * (A.rank - p) := by
  have e1 : rankV D ((i : ℕ) + 1) ((j : ℕ) + 1) = rankV D i j + D.R.t + sLen D := by
    simp only [rankV]; ring
  have hpp : 2 * pp D j ≤ D.R.m - 1 := by
    simp only [pp]; have := j.2; omega
  have hs : sLen D = D.R.r + 6 := rfl
  rw [e1] at hA
  omega

end GlobalTheory.StageConv
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (betaBound_vp cE_vp c_vp delta_vp a0 n_vp IsClassZetaVals)
open GlobalTheory.CMVal (OF IsBaseCond expIn)

namespace GlobalTheory.DenExist

section Field

variable {E : Type} [Field E] [NumberField E]

theorem finite_support (d s : ℕ) {I : Type} [Fintype I] (κ : I → ℕ) (𝔣 : Ideal (OF E)) (h𝔣 : 𝔣 ≠ ⊥)
    (z : ClassGroup (OF E) → ℚ) :
    {l : ℕ | l.Prime ∧ (⌈betaBound_vp d s κ 𝔣 z l / 12⌉₊ : ℕ) ≠ 0}.Finite := by
  set A : Set ℕ := {l | l.Prime ∧ ∃ v : HeightOneSpectrum (OF E), v.asIdeal ∣ 𝔣 ∧ (l : OF E) ∈ v.asIdeal} with hAdef
  have hA : A.Finite :=
    GlobalTheory.FunObj.SqNum.finite_primes_under (K := maximalRealSubfield E) (p := fun v => v.asIdeal ∣ 𝔣)
      (Ideal.finite_factors h𝔣)
  let B : Finset ℕ := (Finset.univ.biUnion fun C =>
    (z C / 2 ^ Module.finrank ℚ (maximalRealSubfield E)).den.primeFactors) ∪ (discr E).natAbs.primeFactors
  refine (hA.union B.finite_toSet).subset ?_
  rintro l ⟨hl, hn⟩
  by_contra hc
  simp only [Set.mem_union, not_or, Finset.mem_coe] at hc
  obtain ⟨hlA, hlB⟩ := hc
  apply hn
  have hv : ∀ v : HeightOneSpectrum (OF E), (l : OF E) ∈ v.asIdeal → ¬ v.asIdeal ∣ 𝔣 :=
    fun v h1 h2 => hlA ⟨hl, v, h2, h1⟩
  have ha0 : a0 𝔣 l = 0 := by
    apply Nat.eq_zero_of_le_zero
    apply csSup_le'
    rintro _ ⟨v, h1, rfl⟩
    simp [expIn, multiplicity_eq_zero_of_not_dvd (hv v h1)]
  have hcv : c_vp 𝔣 l = 0 := by
    have hd : ¬ l ∣ (discr E).natAbs := fun h => hlB (Finset.mem_union_right _
      (Nat.mem_primeFactors.2 ⟨hl, h, by simpa using discr_ne_zero E⟩))
    rw [c_vp, if_neg (fun ⟨v, h1, h2⟩ => hv v h1 h2), delta_vp]
    simp [padicValInt, padicValNat.eq_zero_of_not_dvd hd]
  have hcE : cE_vp l z = 0 := by
    rw [cE_vp, ← bot_eq_zero, Finset.sup_eq_bot_iff]
    intro C _
    set q := z C / 2 ^ Module.finrank ℚ (maximalRealSubfield E)
    have hd : ¬ l ∣ q.den := fun h => hlB (Finset.mem_union_left _ (Finset.mem_biUnion.2
      ⟨C, Finset.mem_univ _, Nat.mem_primeFactors.2 ⟨hl, h, q.den_ne_zero⟩⟩))
    show (-padicValRat l q).toNat = 0
    rw [Int.toNat_eq_zero, padicValRat, padicValNat.eq_zero_of_not_dvd hd]
    simp
  simp [betaBound_vp, hcE, hcv, ha0, n_vp]

end Field

variable {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts}

theorem exists_denom (hz : GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals.ZetaDenominators) (G : GridData Lc sc) (hcm : IsCMField D.host.E)
    (hb : IsBaseCond (condF G.pl)) (i j : Fin D.R.m) (s : ℕ) (hs : 1 ≤ s) :
    ∃ n, IsDenom G i j s n ∧ {l | l.Prime ∧ n l ≠ 0}.Finite := by
  obtain ⟨⟨z, hz'⟩, -⟩ := @hz D.host.E _ _ hcm s hs
  refine ⟨fun l => ((⌈betaBound_vp D.host.d s (kap D sc.cGap i j s) (condF G.pl) z l / 12⌉₊ : ℕ) : ℝ),
    ⟨z, hz', fun l _ => rfl⟩, ?_⟩
  refine (finite_support D.host.d s (kap D sc.cGap i j s) (condF G.pl) hb.1 z).subset ?_
  rintro l ⟨hl, h⟩
  exact ⟨hl, fun h' => h (by simp only [h', Nat.cast_zero])⟩

theorem denEx (hz : GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals.ZetaDenominators) (hF : FieldDat) : DenEx := by
  obtain ⟨CF0, h⟩ := hF
  refine ⟨CF0, fun ε CF hCF => ?_⟩
  obtain ⟨C0, x₀, h⟩ := h ε CF hCF
  refine ⟨C0, x₀, fun C hC D large₂ he hx hR T Lc μ₀ hL G => ?_⟩
  obtain ⟨hcm, -, -, hb, -⟩ := h C hC D large₂ he hx hR T Lc μ₀ hL G
  exact fun i j s hs _ => exists_denom hz G hcm hb i j s hs

end GlobalTheory.DenExist

end
end

section

open GlobalTheory.SqTop

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.CMVal
open Formalism.L2.Host (HChar)

namespace GlobalTheory.ToricExist

theorem exists_rat_repr (D : D7) {w : D.host.E} (hw : w ^ 2 = -(D.host.d : D.host.E)) (hd : 0 < D.host.d)
    (σ : D.host.E →+* ℂ) (hσ : σ w = Complex.I * (Real.sqrt D.host.d : ℝ)) :
    w ∈ D.host.K ∧ ∀ y : D.host.K, ∃ a b : ℚ, (y : D.host.E) = (a : D.host.E) + (b : D.host.E) * w := by
  set bb : D.host.E := D.host.sqd with hbb
  have hb : bb ^ 2 = -(D.host.d : D.host.E) := D.host.sqd_sq
  have hbK : bb ∈ D.host.K := IntermediateField.mem_adjoin_simple_self ℚ _
  have hwb : w = bb ∨ w = -bb := by
    have h0 : (w - bb) * (w + bb) = 0 := by
      have : (w - bb) * (w + bb) = w ^ 2 - bb ^ 2 := by ring
      rw [this, hw, hb, sub_self]
    rcases mul_eq_zero.1 h0 with h | h
    · exact Or.inl (sub_eq_zero.1 h)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h)
  have hwK : w ∈ D.host.K := by
    rcases hwb with h | h
    · rw [h]; exact hbK
    · rw [h]; exact neg_mem hbK
  refine ⟨hwK, fun y => ?_⟩
  let wK : D.host.K := ⟨w, hwK⟩
  have hli : LinearIndependent ℚ ![(1 : D.host.K), wK] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h0 : (s : D.host.E) + (t : D.host.E) * w = 0 := by
      have := congrArg Subtype.val hst
      simpa [Rat.smul_def, wK] using this
    have h1 := congrArg σ h0
    simp only [map_add (f := _), map_mul, map_ratCast, map_zero, hσ] at h1
    have hre := congrArg Complex.re h1
    have him := congrArg Complex.im h1
    simp at hre him
    refine ⟨by exact_mod_cast hre, ?_⟩
    rcases him with h | h
    · exact_mod_cast h
    · exact absurd h hd.ne'
  have hcard : Fintype.card (Fin 2) = Module.finrank ℚ D.host.K := by
    rw [GlobalTheory.CurveLattice.finrank_hostK]; rfl
  let B := basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hB : ∀ i, B i = ![(1 : D.host.K), wK] i := fun i => by
    simp [B, coe_basisOfLinearIndependentOfCardEqFinrank]
  refine ⟨B.repr y 0, B.repr y 1, ?_⟩
  have e := B.sum_repr y
  rw [Fin.sum_univ_two, hB, hB] at e
  have e2 := congrArg (fun z : D.host.K => (z : D.host.E)) e
  simp only [IntermediateField.coe_add, IntermediateField.coe_smul, Matrix.cons_val_zero, Matrix.cons_val_one,
    IntermediateField.coe_one, Rat.smul_def, mul_one] at e2
  rw [← e2]
  rfl

theorem exists_phiK (D : D7) (hFD : GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData D.host.d (cmPhi D)) :
    ∃ φK : D.host.K →+* ℂ, (∀ τ, (cmPhi D τ).comp (algebraMap D.host.K D.host.E) = φK) ∧
      ∀ Λ, GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsIntLattice D.host.d Λ → GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.IsLatOf φK 1 Λ := by
  obtain ⟨-, hd4, -, -, -, hcard, -, w, hw, hwφ⟩ := hFD
  have hne : Nonempty D.what₂.Tau := Fintype.card_pos_iff.1 (by omega)
  obtain ⟨τ₀⟩ := hne
  obtain ⟨hwK, hrep⟩ := exists_rat_repr D hw (by omega) (cmPhi D τ₀) (hwφ τ₀)
  let φK : D.host.K →+* ℂ := (cmPhi D τ₀).comp (algebraMap D.host.K D.host.E)
  have hval : ∀ (τ : D.what₂.Tau) (y : D.host.K) (a b : ℚ), (y : D.host.E) = (a : D.host.E) + (b : D.host.E) * w →
      cmPhi D τ (y : D.host.E) = (a : ℂ) + (b : ℂ) * (Complex.I * (Real.sqrt D.host.d : ℝ)) := by
    intro τ y a b h
    rw [h, map_add (f := _), map_mul, map_ratCast, map_ratCast, hwφ τ]
  have hcomp : ∀ τ, (cmPhi D τ).comp (algebraMap D.host.K D.host.E) = φK := fun τ => by
    ext y
    obtain ⟨a, b, h⟩ := hrep y
    show cmPhi D τ (y : D.host.E) = cmPhi D τ₀ (y : D.host.E)
    rw [hval τ y a b h, hval τ₀ y a b h]
  refine ⟨φK, hcomp, fun Λ hΛ => ?_⟩
  have hinj : Function.Injective φK := φK.injective
  ext x
  simp only [Set.mem_image, SetLike.mem_coe]
  constructor
  · intro hx
    obtain ⟨hint, a, b, rfl⟩ := (hΛ x).1 hx
    let y : D.host.K := (a : D.host.K) + (b : D.host.K) * ⟨w, hwK⟩
    have hy : φK y = (a : ℂ) + (b : ℂ) * (Complex.I * (Real.sqrt D.host.d : ℝ)) := by
      show cmPhi D τ₀ (y : D.host.E) = _
      exact hval τ₀ y a b (by simp [y])
    refine ⟨y, ?_, hy⟩
    have hyi : IsIntegral ℤ y := (isIntegral_algHom_iff φK.toIntAlgHom hinj).1 (by rw [← hy] at hint; exact hint)
    exact (FractionalIdeal.mem_one_iff _).2 ⟨⟨y, hyi⟩, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨y', rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hy
    obtain ⟨a, b, h⟩ := hrep (algebraMap (𝓞 D.host.K) D.host.K y')
    refine (hΛ _).2 ⟨?_, a, b, hval τ₀ _ a b h⟩
    exact (RingOfIntegers.isIntegral_coe y').map φK.toIntAlgHom

theorem gBig_of {P R : GP} (hP : GBig P)
    (h : ∀ {D : D7} {T : Type} {Lc : Formalism.IndefR.Links.LevCh D T} {sc : Consts} (G : GridData Lc sc) (μ₀ : T) (C x b : ℝ),
      Lc.Is μ₀ → P G μ₀ C x b → R G μ₀ C x b) : GBig R := by
  obtain ⟨CF0, h1⟩ := hP
  refine ⟨CF0, fun ε CF hCF => ?_⟩
  obtain ⟨C0, x0, h2⟩ := h1 ε CF hCF
  exact ⟨C0, x0, fun C hC D large₂ he hx hr T Lc μ₀ hμ G => h G μ₀ _ _ _ hμ (h2 C hC D large₂ he hx hr T Lc μ₀ hμ G)⟩

theorem gBig_and {P Q : GP} (hP : GBig P) (hQ : GBig Q) :
    GBig fun {_ _ _ _} G μ₀ C x b => P G μ₀ C x b ∧ Q G μ₀ C x b := by
  obtain ⟨CF1, h1⟩ := hP
  obtain ⟨CF2, h2⟩ := hQ
  refine ⟨max CF1 CF2, fun ε CF hCF => ?_⟩
  obtain ⟨C1, x1, k1⟩ := h1 ε CF (le_trans (le_max_left _ _) hCF)
  obtain ⟨C2, x2, k2⟩ := h2 ε CF (le_trans (le_max_right _ _) hCF)
  refine ⟨max C1 C2, max x1 x2, fun C hC D large₂ he hx hr T Lc μ₀ hμ G => ⟨?_, ?_⟩⟩
  · exact k1 C (le_trans (le_max_left _ _) hC) D large₂ he (le_trans (le_max_left _ _) hx) hr T Lc μ₀ hμ G
  · exact k2 C (le_trans (le_max_right _ _) hC) D large₂ he (le_trans (le_max_right _ _) hx) hr T Lc μ₀ hμ G

theorem exists_prime {E : Type} [Field E] [NumberField E] {𝔣 : Ideal (OF E)} (h : IsBaseCond 𝔣) :
    Nonempty (HeightOneSpectrum (𝓞 E)) := by
  obtain ⟨M, hM, hfM⟩ := Ideal.exists_le_maximal 𝔣 h.2.1
  let v : HeightOneSpectrum (OF E) := ⟨M, hM.isPrime, fun e => h.1 (eq_bot_iff.2 (e ▸ hfM))⟩
  obtain ⟨P, -⟩ := (h.2.2 v (Ideal.dvd_iff_le.2 hfM)).1
  exact ⟨P⟩

theorem torEx : GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.Transport → FieldDat → LNe → TorEx := by
  intro hT hF hL
  refine gBig_of (gBig_and hF hL) ?_
  intro D T Lc sc G μ₀ C x b hμ ⟨hf, hl⟩ i j s hs1 hs2 c
  obtain ⟨hCM, hAb, hFD, hBC, -⟩ := hf
  have hFD' := hFD
  obtain ⟨-, hd4, hU, -, -, hcard, hφ, -⟩ := hFD
  have hV : IsValChar (cmPhi D) s (kap D sc.cGap i j s) (condF G.pl) ∅ (fam G μ₀ i j c) := by
    cases c with
    | none => exact (GlobalTheory.FunObj.SqNum.Model.isValChar_nu hμ G i j hs2).1
    | some c => exact (GlobalTheory.FunObj.SqNum.Model.isValChar_nu hμ G i j hs2).2 c
  obtain ⟨P⟩ := exists_prime hBC
  have hAux : IsFinSetSplitPlacesCoprimeConductor (condF G.pl) ∅ := fun q hq => absurd hq (Finset.notMem_empty q)
  have hTS : ∀ Λ, IsHeckeL (fam G μ₀ i j c) Λ →
      IsToricSum (cmPhi D) s (kap D sc.cGap i j s) (condF G.pl) (fam G μ₀ i j c) (Λ s) := fun Λ hΛ => by
    have := GlobalTheory.ToricSumValue.toricSum_eq GlobalTheory.Published.HeckeEntire_holds D.host.E D.what₂.Tau (cmPhi D) hφ s
      (kap D sc.cGap i j s) (condF G.pl) ∅ (fam G μ₀ i j c) (fun _ => P) Λ hU hs1 hBC hAux hV
      (fun q hq => absurd hq (Finset.notMem_empty q)) hΛ
    simpa [condQ] using this
  obtain ⟨Λ, hΛ, hne⟩ := (hl i j).2 c
  refine ⟨Λ s, ⟨hV, hTS Λ hΛ⟩, hne s hs1, fun Λ' h => by rw [hΛ.unique h], fun Λ₁ hΛ₁ => ?_⟩
  obtain ⟨φK, hcomp, hlat⟩ := exists_phiK D hFD'
  haveI := hCM
  haveI := hAb
  obtain ⟨t, 𝔞, Λσ, -, -, hTr⟩ := hT D.host.K D.host.d hd4 (GlobalTheory.CurveLattice.finrank_hostK D)
    (GlobalTheory.CurveLattice.discr_hostK D) φK Λ₁ (hlat Λ₁ hΛ₁)
  have hk := hTr D.host.E hU D.what₂.Tau (cmPhi D) hcard hφ hcomp s (kap D sc.cGap i j s) (condF G.pl) hs1
    (fun τ => (GlobalTheory.FunObj.SqNum.Model.kap_add D sc.cGap i j τ hs2).2) hBC
  exact (hk.1 ∅ _ _ ⟨hAux, hV, by simpa [condQ] using hTS Λ hΛ⟩).1

end GlobalTheory.ToricExist
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SqStep

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Chars Base PsiUnr stepFac)

variable {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts}


open Classical in
def chs (G : GridData Lc sc) (i j : Fin D.R.m) (t : T) : Chars D.host.F D.host.E where
  α := Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2)
  β := G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)
  S₀ := G.pl.S0
  Q := (twPl G t).image fun w => w.under (𝓞 D.host.F)

def BaseFits (G : GridData Lc sc) (W : G.Weil) (i j : Fin D.R.m) (t : T) (B : Base D.host.F D.host.E) : Prop :=
  B.ψ = W.ψ ∧ (chs G i j t).T ⊆ B.P ∧ (∀ v ∈ B.P, PsiUnr B.ψ v) ∧
    ∀ v : B.P, v.1 ∈ (chs G i j t).T → GlobalTheory.AdelicU.splitPrime (B.τ v) ∈ locPl G t

end GlobalTheory.SqStep
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate Matrix NNReal
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (sZero)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP (Pair Unram SphFun openOff integrand wcoef rcoef up)

noncomputable section
namespace GlobalTheory.BottomIPData

variable {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts}

def alphaB (L : LevCh D T) (i j : Fin D.R.m) (t : T) : (AE D)ˣ →* Circle := L.mu t (j + 1) * L.eta ^ (rankV D i j % 2)

def betaB (G : GridData L sc) (i j : Fin D.R.m) : (AE D)ˣ →* Circle := G.ch.chi (D.R.m - i) * L.eta ^ (rankV D i j % 2)


open Classical in
def sfB (G : GridData L sc) (t : T) : Finset (GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.FinPl D) :=
  (locPl G t).image fun w => w.under (𝓞 D.host.F)

theorem isBottomTri_is {G : GridData L sc} {W : G.Weil} {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}
    (h : IsBottomTri W i j X) :
    X.Is W.ψ W.θ (alphaB L i j) (fun _ => betaB G i j) (fun t => SqNum.nuH G t i j) (locPl G) := h.is

theorem gbig_mono {Q Q' : GP} (h : GBig Q) (H : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts}
    (G : GridData Lc sc) (μ₀ : T) (C x b : ℝ), Q G μ₀ C x b → Q' G μ₀ C x b) : GBig Q' := by
  obtain ⟨CF0, h⟩ := h
  refine ⟨CF0, fun ε CF hCF => ?_⟩
  obtain ⟨C0, x₀, h⟩ := h ε CF hCF
  exact ⟨C0, x₀, fun C hC D large₂ he hx hR T Lc μ₀ hL G => H _ _ _ _ _ (h C hC D large₂ he hx hR T Lc μ₀ hL G)⟩

theorem gbig_and {Q Q' : GP} (h : GBig Q) (h' : GBig Q') : GBig fun G μ₀ C x b => Q G μ₀ C x b ∧ Q' G μ₀ C x b := by
  obtain ⟨CF0, h⟩ := h
  obtain ⟨CF0', h'⟩ := h'
  refine ⟨max CF0 CF0', fun ε CF hCF => ?_⟩
  obtain ⟨C0, x₀, h⟩ := h ε CF (le_of_max_le_left hCF)
  obtain ⟨C0', x₀', h'⟩ := h' ε CF (le_of_max_le_right hCF)
  exact ⟨max C0 C0', max x₀ x₀', fun C hC D large₂ he hx hR T Lc μ₀ hL G =>
    ⟨h C (le_of_max_le_left hC) D large₂ he (le_of_max_le_left hx) hR T Lc μ₀ hL G,
      h' C (le_of_max_le_right hC) D large₂ he (le_of_max_le_right hx) hR T Lc μ₀ hL G⟩⟩

end GlobalTheory.BottomIPData
end
end

section

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh

theorem weil_twist_base : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.Char F → ∀ (i : Fin D.R.m) (t : T0) (k : GA D (Wc D i)) (x : (AE D)ˣ), IsDetRoot (Wc D i) k x → ∀ f, IsThetaFunO R.ψ (Vc D i) (Wc D i) f → R.ωP i t (1, k) f = ((R.xi t x : Circle) : ℂ) • R.ωP i A.μ0 (1, k) f := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR i t k x hx f hf
  have h := GlobalTheory.TwistFactorProof.frame_ratio R (GlobalTheory.T.weilDatum_unique_on_thetaFunctions D) (GlobalTheory.T.exists_weilDatum_twist_heckeCharacters D) hR.thP.ωP i A.μ0 t hx hf
  rw [GlobalTheory.TwistFactorCompare.eq_one_of_chrEq_one (hR.lev.xi_base ▸ hR.lev.xi A.μ0) x, Circle.coe_one, one_smul] at h
  exact h

end GlobalTheory.AdTh
end
