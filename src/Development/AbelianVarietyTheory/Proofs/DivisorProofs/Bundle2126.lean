module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1984
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle326
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle320
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle214
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1291
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2092
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2039
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2035
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2084
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2085
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2045
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2086
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2047
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2051
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2087
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1910
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMixModelB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2003
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle337
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle386
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFinsetSelfDualClassesHerm
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1990

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory Matrix
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm GlobalTheory.BigNZ GlobalTheory.FlipMatch GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB incM)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW psiLoc chrW)
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopFlip

namespace GlobalTheory.XiAway

theorem xi_awayIm : ∀ {D : D7} {T : Type} {L : LevCh D T} {μ₀ : T}, L.Is μ₀ → ∀ t : T, LocIn D.what₂.embLL (L.xiH t) →
      ∀ (m : ℕ) (y : (AE D)ˣ), GlobalTheory.KappaArith.AwayIm D m ((L.xi t y : Circle) : ℂ) := by
  intro D T L μ₀ hL t hx m y
  obtain ⟨n, hn, ho⟩ := hL.xi_fin t
  have h := hL.xi t
  have h1 : L.xi t y ^ n = 1 := GlobalTheory.HeckeFinTrivial.eq_one_of_trivial_on_finite D (L.xi t ^ n) ⟨h.1.1.pow n, fun x => by
    rw [MonoidHom.pow_apply, h.1.2, one_pow]⟩ (GlobalTheory.CharOrderFin.char_pow_eq_one_of_orderDvd D _ _ h n ho) y
  obtain ⟨ζ, hζ⟩ := GlobalTheory.TwistValues.char_mem (L.xi t) (L.xiH t) h hn ho D.what₂.embLL.fieldRange
    (fun P k => hx P (Formalism.L2.Host.atFin P k)) y
  have h2 : ζ ^ n = 1 := D.what₂.embLL.injective (by
    rw [map_pow, map_one]
    erw [hζ]
    have := congrArg (fun w : Circle => (w : ℂ)) h1
    simpa using this)
  exact ⟨ζ, GlobalTheory.KappaArith.isAwayUnit_of_pow_eq_one m hn h2, hζ⟩

end GlobalTheory.XiAway
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory Matrix
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm GlobalTheory.BigNZ GlobalTheory.FlipMatch GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB incM)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW psiLoc chrW)
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopFlip

open Formalism.L2.Host (HChar)

namespace GlobalTheory.TopFlipNu

theorem exists_pow_close {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (x c : w.adicCompletion E)
    (hx : Valued.v x = 1) (hc : c ≠ 0) : ∃ k : ℕ, 0 < k ∧ Valued.v (x ^ k - 1) ≤ Valued.v c := by
  haveI : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have e := ValuativeRel.isEquiv (ValuativeRel.valuation (w.adicCompletion E))
    (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)))
  have hK : IsCompact {y : w.adicCompletion E | Valued.v y ≤ 1} := by
    have := IsNonarchimedeanLocalField.isCompact_closedBall (w.adicCompletion E) 1
    convert this using 1
    ext y
    exact e.le_one_iff_le_one.symm
  have hv0 : Valued.v c ≠ 0 := by simpa using hc
  obtain ⟨s, -, hs⟩ := hK.elim_nhds_subcover (fun y => {z | (z - y) * c⁻¹ ∈ w.adicCompletionIntegers E}) fun y _ =>
    ((Valued.isOpen_valuationSubring _).preimage ((continuous_id.sub continuous_const).mul continuous_const)).mem_nhds
      (by simp)
  have h1 : ∀ n : ℕ, ∃ y : s, Valued.v (x ^ n - y) ≤ Valued.v c := fun n => by
    have : x ^ n ∈ {y : w.adicCompletion E | Valued.v y ≤ 1} := by simp [hx]
    obtain ⟨y, hy, h⟩ := Set.mem_iUnion₂.1 (hs this)
    refine ⟨⟨y, hy⟩, ?_⟩
    have h2 : Valued.v ((x ^ n - y) * c⁻¹) ≤ 1 := h
    rwa [map_mul, map_inv₀, mul_inv_le_iff₀ (zero_lt_iff.2 hv0), one_mul] at h2
  choose f hf using h1
  have key : ∀ a b : ℕ, a < b → f a = f b → ∃ k : ℕ, 0 < k ∧ Valued.v (x ^ k - 1) ≤ Valued.v c := fun a b hab h => by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hab
    refine ⟨k + 1, by omega, ?_⟩
    have h3 := Valuation.map_sub_le _ (hf (a + k + 1)) (h ▸ hf a)
    have h4 : x ^ (a + k + 1) - f (a + k + 1) - (x ^ a - f (a + k + 1)) = x ^ a * (x ^ (k + 1) - 1) := by ring
    rwa [h4, map_mul, map_pow, hx, one_pow, one_mul] at h3
  obtain ⟨a, b, hne, h⟩ := Finite.exists_ne_map_eq_of_infinite f
  rcases lt_or_gt_of_ne hne with h' | h'
  exacts [key a b h' h, key b a h' h.symm]

theorem exists_pow_eq_one {E : Type} [Field E] [NumberField E] {χ : HChar E} {w : HeightOneSpectrum (𝓞 E)} {n : ℕ}
    (h : χ.LevelLe w n) (x : (w.adicCompletion E)ˣ) (hx : Valued.v (x : w.adicCompletion E) = 1) :
    ∃ k : ℕ, 0 < k ∧ χ.loc w x ^ k = 1 := by
  have hu := Formalism.L2.Host.unif_spec w
  unfold Formalism.L2.Host.IsUnifAt at hu
  obtain ⟨k, hk, h1⟩ := exists_pow_close w x
    (((Formalism.L2.Host.atFin w (Formalism.L2.Host.unif w) : (w.adicCompletion E)ˣ) : w.adicCompletion E) ^ n) hx
    (pow_ne_zero _ (Units.ne_zero _))
  refine ⟨k, hk, ?_⟩
  rw [← map_pow]
  refine h _ ?_ ?_
  · show Valued.v _ = 1
    rw [Units.val_pow_eq_pow_val, map_pow, hx, one_pow]
  · rw [map_pow, hu, ← WithZero.exp_nsmul] at h1
    rw [Units.val_pow_eq_pow_val]
    simpa using h1

theorem awayIm_unit {D : D7} {χ : HChar D.host.E} (hχ : LocIn D.what₂.embLL χ) {w : HeightOneSpectrum (𝓞 D.host.E)} {n : ℕ}
    (h : χ.LevelLe w n) (x : (w.adicCompletion D.host.E)ˣ) (hx : Valued.v (x : w.adicCompletion D.host.E) = 1) (m : ℕ) :
    GlobalTheory.KappaArith.AwayIm D m (χ.loc w x : ℂ) := by
  obtain ⟨k, hk, h1⟩ := exists_pow_eq_one h x hx
  obtain ⟨ζ, hζ⟩ := hχ w x
  have h2 : ζ ^ k = 1 := D.what₂.embLL.injective (by rw [map_pow, hζ, map_one, ← Units.val_pow_eq_pow_val, h1, Units.val_one])
  exact ⟨ζ, GlobalTheory.KappaArith.isAwayUnit_of_pow_eq_one m hk h2, hζ⟩

theorem chi_levelLe {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData L sc) {i : ℕ} (h1 : 1 ≤ i)
    (h2 : i ≤ D.R.m) (w : HeightOneSpectrum (𝓞 D.host.E)) : (G.ch.chiH i).LevelLe w 2 := by
  by_cases h : w.under (𝓞 D.host.F) ∈ G.pl.S0
  · rcases G.pl.mem_S0_of_sum_eq.1 h with h | h
    · exact fun x hx h3 => (G.ch.lev0 i h1 h2 w h).1 x hx (h3.trans (WithZero.exp_le_exp.2 (by omega)))
    · exact (G.ch.lev1 i h1 h2 w h).1
  · exact fun x hx _ => G.ch.unr i h1 h2 w h x hx

theorem nu_arith : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → CharsIn G D.what₂.embLL → ∀ (i j : Fin D.R.m) (x : ∀ w : Pl D.host.E, (Kw w)ˣ) (t : T),
      (∀ w ∈ locPl G t, ValuativeRel.valuation (Kw w) (x w : Kw w) = 1) →
      ∃ z : ℂ, GlobalTheory.KappaArith.AwayIm D (Qn G t) z ∧ ∏ w ∈ locPl G t, (((locGrid G t w).nu i j (x w) : ℂˣ) : ℂ) =
        z * ∏ w ∈ locPl G μ₀, (((locGrid G μ₀ w).nu i j (x w) : ℂˣ) : ℂ) := by
  classical
  intro D T L sc G μ₀ hL hC i j x t hx
  have hQ : L.Q μ₀ = ∅ := Finset.eq_empty_of_forall_notMem fun w hw =>
    (hL.Q_ram μ₀ w).2 (Or.inl hw) (by rw [hL.xi_base]; intro x _; rfl)
  have h0 : locPl G μ₀ = G.pl.W0 := by rw [locPl, hQ]; simp
  have hsub : G.pl.W0 ⊆ locPl G t := fun w hw => by unfold locPl; simp [hw]
  have hf : ∀ w, (((locGrid G t w).nu i j (x w) : ℂˣ) : ℂ) =
      ((L.xiH t).loc w (x w) : ℂ) * (((locGrid G μ₀ w).nu i j (x w) : ℂˣ) : ℂ) := fun w => by
    have loc_mul (a b : HChar D.host.E) : (a * b).loc w (x w) = a.loc w (x w) * b.loc w (x w) := rfl
    have loc_one : (1 : HChar D.host.E).loc w (x w) = 1 := rfl
    simp only [Grid.nu, locGrid, MonoidHom.div_apply, loc_mul, hL.xi_base, loc_one,
      Units.val_div_eq_div_val, Units.val_mul, Units.val_one]
    ring
  have hb : ∀ w ∈ locPl G t, GlobalTheory.KappaArith.AwayIm D (Qn G t) (((locGrid G μ₀ w).nu i j (x w) : ℂˣ) : ℂ) := fun w hw => by
    haveI : (Valued.v : Valuation (Kw w) (WithZero (Multiplicative ℤ))).Compatible := Valuation.Compatible.ofValuation _
    have e := ValuativeRel.isEquiv (ValuativeRel.valuation (Kw w)) (Valued.v : Valuation (Kw w) (WithZero (Multiplicative ℤ)))
    have hv : Valued.v (x w : Kw w) = 1 := e.eq_one_iff_eq_one.1 (hx w hw)
    have hv' : Valued.v (((x w)⁻¹ : (Kw w)ˣ) : Kw w) = 1 := by rw [Units.val_inv_eq_inv_val, map_inv₀, hv, inv_one]
    have h1 : 1 ≤ D.R.m - (i : ℕ) := by have := i.2; omega
    have h2 : D.R.m - (i : ℕ) ≤ D.R.m := Nat.sub_le _ _
    have a := awayIm_unit (hC.mu0 j) ((L.C.isMu0 j).tame w) (x w) hv (Qn G t)
    have b := awayIm_unit (hC.chi _ h1 h2) (chi_levelLe G h1 h2 w) (x w)⁻¹ hv' (Qn G t)
    have hm : muBase L (j + 1) = L.C.mu0 j := by rw [muBase, dite_eq_left j.2]
    convert a.mul b using 1
    simp only [Grid.nu, locGrid, MonoidHom.div_apply, hL.xi_base, mul_one, hm, map_inv,
      Units.val_div_eq_div_val, Units.val_inv_eq_inv_val]
    exact div_eq_mul_inv _ _
  refine ⟨(∏ w ∈ locPl G t, ((L.xiH t).loc w (x w) : ℂ)) *
    ∏ w ∈ locPl G t \ G.pl.W0, (((locGrid G μ₀ w).nu i j (x w) : ℂˣ) : ℂ), ?_, ?_⟩
  · exact (GlobalTheory.KappaArith.AwayIm.prod _ _ fun w _ => GlobalTheory.KappaArith.awayIm_val hL (hC.xi t) _ w (x w)).mul
      (GlobalTheory.KappaArith.AwayIm.prod _ _ fun w hw => hb w (Finset.mem_sdiff.1 hw).1)
  · rw [h0, mul_assoc, Finset.prod_sdiff hsub, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun w _ => hf w

end GlobalTheory.TopFlipNu
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

namespace GlobalTheory.SqStepK

section Values

open GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem idealVal_mul_chr (χ ψ : Chr F E) (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) :
    idealVal (χ * ψ) 𝔞 = idealVal χ 𝔞 * idealVal ψ 𝔞 := by
  unfold idealVal
  simp_rw [val_mul, mul_zpow]
  exact finprod_mul_distrib (GlobalTheory.SqStepIdeal.mulSupport_finite _ 𝔞) (GlobalTheory.SqStepIdeal.mulSupport_finite _ 𝔞)

theorem idealVal_prime (χ : Chr F E) (w : HeightOneSpectrum (𝓞 E)) :
    idealVal χ (w.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) = val χ w := by
  unfold idealVal
  rw [finprod_eq_single _ w, FractionalIdeal.count_self, zpow_one]
  intro v hv
  rw [FractionalIdeal.count_maximal_coprime E v hv.symm, zpow_zero]

theorem idealVal_one (χ : Chr F E) : idealVal χ (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) = 1 := by
  unfold idealVal
  simp [FractionalIdeal.count_one]

theorem exists_idealVal_eq {ξ : Chr F E} (hξ : IsHecke F E ξ) (hu : ∀ᶠ w in Filter.cofinite, UnrAt ξ w) {n : ℕ} (hn : 0 < n)
    (hv : ∀ w, val ξ w ^ n = 1) (k : (AE F E)ˣ) :
    ∃ 𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E, 𝔞 ≠ 0 ∧ idealVal ξ 𝔞 = Circle.toUnits (ξ k) := by
  let H : Subgroup ℂˣ :=
    { carrier := {z | ∃ 𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E, 𝔞 ≠ 0 ∧ idealVal ξ 𝔞 = z}
      mul_mem' := by
        rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
        exact ⟨a * b, mul_ne_zero ha hb, GlobalTheory.EulerIdeal.idealVal_mul ξ ha hb⟩
      one_mem' := ⟨1, one_ne_zero, idealVal_one ξ⟩
      inv_mem' := by
        rintro _ ⟨a, ha, rfl⟩
        exact ⟨a⁻¹, inv_ne_zero ha, GlobalTheory.EulerIdeal.idealVal_inv ξ a⟩ }
  haveI : NeZero n := ⟨hn.ne'⟩
  have h1 : H ≤ rootsOfUnity n ℂ := by
    rintro _ ⟨a, -, rfl⟩
    unfold idealVal
    rw [finprod_eq_prod_of_mulSupport_subset _ (s := (GlobalTheory.SqStepIdeal.mulSupport_finite (val ξ) a).toFinset) (by simp)]
    exact Subgroup.prod_mem _ fun w _ => Subgroup.zpow_mem _ ((mem_rootsOfUnity _ _).2 (hv w)) _
  haveI : Finite H := Finite.of_injective _ (Subgroup.inclusion_injective h1)
  have hc : 0 < Nat.card H := Nat.card_pos
  haveI : NeZero (Nat.card H) := ⟨hc.ne'⟩
  have h2 : H ≤ rootsOfUnity (Nat.card H) ℂ := fun z hz => by
    rw [mem_rootsOfUnity]
    have := congrArg Subtype.val (pow_card_eq_one' (x := (⟨z, hz⟩ : H)))
    rwa [SubmonoidClass.coe_pow] at this
  have h3 : H = rootsOfUnity (Nat.card H) ℂ := by
    refine Subgroup.eq_of_le_of_card_ge h2 ?_
    exact card_rootsOfUnity ℂ (Nat.card H)
  have h4 : ξ ^ Nat.card H = 1 := by
    refine GlobalTheory.HeckeUnifApprox.eq_one_of_unif_cofinite _ ⟨?_, fun x => ?_⟩ (hu.mono fun w hw ϖ hϖ => ?_)
    · exact hξ.1.pow _
    · rw [MonoidHom.pow_apply, hξ.2 x, one_pow]
    · have e1 : val ξ w ∈ H := ⟨w.asIdeal, FractionalIdeal.coeIdeal_ne_zero.2 w.ne_bot, idealVal_prime ξ w⟩
      have e2 := (mem_rootsOfUnity _ _).1 (h2 e1)
      rw [← hw.locChar_eq_val hϖ] at e2
      have e3 : Circle.toUnits (ξ (locIdele F w ϖ) ^ Nat.card H) = Circle.toUnits 1 := by
        rw [map_pow, map_one]; exact e2
      rw [MonoidHom.pow_apply]
      exact Circle.ext (congrArg Units.val e3)
  have h5 : Circle.toUnits (ξ k) ∈ H := by
    rw [h3, mem_rootsOfUnity, ← map_pow, ← MonoidHom.pow_apply, h4, MonoidHom.one_apply, map_one]
  exact h5

theorem nu_good {B : Base F E} {X : Chars F E} {a a' : ℕ} (h : X.IsGood B a a') :
    IsHecke F E X.ν ∧ ∀ᶠ w in Filter.cofinite, UnrAt X.ν w := by
  refine ⟨⟨h.heckeα.1.div' h.heckeβ.1, fun x => by
    simp only [Chars.ν, MonoidHom.div_apply, h.heckeα.2 x, h.heckeβ.2 x, div_one]⟩, ?_⟩
  have hf : (above E (X.T : Set (Pl F))).Finite :=
    (Set.Finite.biUnion X.T.finite_toSet fun v _ => Formalism.L2.Host.finite_aboveF (L := E) F v).subset fun w hw =>
      Set.mem_biUnion hw rfl
  refine Filter.eventually_cofinite.2 (hf.subset fun w hw => ?_)
  by_contra hn
  refine hw ?_
  rw [Chars.ν, div_eq_mul_inv]
  exact (h.unrα w hn).mul (h.unrβ w hn).inv

theorem exists_stepFac_twist (B : Base F E) {X Y : Chars F E} (hξ : IsHecke F E (X.ν / Y.ν))
    (hu : ∀ᶠ w in Filter.cofinite, UnrAt (X.ν / Y.ν) w) {n : ℕ} (hn : 0 < n) (hv : ∀ w, val (X.ν / Y.ν) w ^ n = 1)
    (e₁ e₂ s : ℤˣ) (𝔟 𝔠 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (z : ℤ) (k : (AE F E)ˣ) :
    ∃ (𝔟' : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (r : ℂ), r ≠ 0 ∧
      stepFac B X e₁ e₂ s 𝔟' 𝔠 z = ((X.ν k / Y.ν k : Circle) : ℂ) * r * stepFac B X e₁ e₂ s 𝔟 𝔠 z ∧
      stepFac B Y e₁ e₂ s 𝔟' 𝔠 z = r * stepFac B Y e₁ e₂ s 𝔟 𝔠 z := by
  obtain ⟨𝔟₀, h0, e0⟩ : ∃ 𝔟₀ : FractionalIdeal (nonZeroDivisors (𝓞 E)) E, 𝔟₀ ≠ 0 ∧
      ∀ χ : Chr F E, idealVal χ 𝔟₀ = idealVal χ 𝔟 := by
    by_cases h : 𝔟 = 0
    · refine ⟨1, one_ne_zero, fun χ => ?_⟩
      rw [idealVal_one, h]
      unfold idealVal
      simp [FractionalIdeal.count_zero]
    · exact ⟨𝔟, h, fun _ => rfl⟩
  obtain ⟨𝔞, ha, e⟩ := exists_idealVal_eq hξ hu hn hv (k ^ (e₁ : ℤ))
  have e1 : idealVal X.ν 𝔞 ^ (e₁ : ℤ) = Circle.toUnits (X.ν k / Y.ν k) * idealVal Y.ν 𝔞 ^ (e₁ : ℤ) := by
    have : idealVal X.ν 𝔞 = idealVal (X.ν / Y.ν) 𝔞 * idealVal Y.ν 𝔞 := by
      rw [← idealVal_mul_chr, div_mul_cancel]
    rw [this, e, mul_zpow, map_zpow, map_zpow, ← zpow_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, zpow_one,
      MonoidHom.div_apply]
  refine ⟨𝔞 * 𝔟₀, (idealVal Y.ν 𝔞 ^ (e₁ : ℤ) : ℂˣ), Units.ne_zero _, ?_, ?_⟩
  · unfold stepFac
    rw [GlobalTheory.EulerIdeal.idealVal_mul _ ha h0, e0, mul_zpow, e1]
    simp only [Units.val_mul, mul_assoc]
    rfl
  · unfold stepFac
    rw [GlobalTheory.EulerIdeal.idealVal_mul _ ha h0, e0, mul_zpow]
    simp only [Units.val_mul, mul_assoc]

end Values

theorem val_quot_pow {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) {μ₀ : T} (hL : Lc.Is μ₀)
    (W : G.Weil) (S : GridChoice W Set.univ) (hN : NumbersIn D.what₂.embLL S μ₀) (i j : Fin D.R.m) (t : T) :
    ∃ n : ℕ, 0 < n ∧ ∀ w, GlobalTheory.LFun.val ((GlobalTheory.SqStep.chs G i j t).ν / (GlobalTheory.SqStep.chs G i j μ₀).ν) w ^ n = 1 := by
  have e : ∀ s, (GlobalTheory.SqStep.chs G i j s).ν = G.nu s i (j + 1) := fun s => by
    show (Lc.mu s (j + 1) * Lc.eta ^ _) / (G.ch.chi _ * Lc.eta ^ _) = _
    rw [mul_div_mul_right_eq_div]
    rfl
  have hν : (GlobalTheory.SqStep.chs G i j t).ν / (GlobalTheory.SqStep.chs G i j μ₀).ν = Lc.xi t * (Lc.xi μ₀)⁻¹ := by
    rw [e, e]
    refine MonoidHom.ext fun x => ?_
    show Lc.mu0 (j + 1) x * Lc.xi t x / G.ch.chi (D.R.m - i) x / (Lc.mu0 (j + 1) x * Lc.xi μ₀ x / G.ch.chi (D.R.m - i) x) =
      Lc.xi t x * (Lc.xi μ₀ x)⁻¹
    rw [div_div_div_cancel_right, mul_div_mul_left_eq_div, div_eq_mul_inv]
  obtain ⟨n, hn, hfin⟩ := hL.xi_fin t
  refine ⟨n, hn, fun w => ?_⟩
  rw [hν, GlobalTheory.LFun.val_mul, GlobalTheory.LFun.val_inv, GlobalTheory.LFun.val_eq_of_chrEq (hL.xi t) w, GlobalTheory.LFun.val_eq_of_chrEq (hL.xi μ₀) w,
    hL.xi_base, show (1 : HChar D.host.E).val w = 1 from rfl, inv_one, mul_one]
  exact (GlobalTheory.SqStepIdeal.val_mem hfin (hN.chars.xi t) w).1

theorem gbig_three_is {Q₁ Q₂ Q₃ Q : GP} (h₁ : GBig Q₁) (h₂ : GBig Q₂) (h₃ : GBig Q₃)
    (H : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData Lc sc) (μ₀ : T) (C x b : ℝ),
      Lc.Is μ₀ → Q₁ G μ₀ C x b → Q₂ G μ₀ C x b → Q₃ G μ₀ C x b → Q G μ₀ C x b) : GBig Q := by
  obtain ⟨F₁, h₁⟩ := h₁
  obtain ⟨F₂, h₂⟩ := h₂
  obtain ⟨F₃, h₃⟩ := h₃
  refine ⟨max F₁ (max F₂ F₃), fun ε CF hCF => ?_⟩
  obtain ⟨C₁, x₁, k₁⟩ := h₁ ε CF (le_trans (le_max_left _ _) hCF)
  obtain ⟨C₂, x₂, k₂⟩ := h₂ ε CF (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hCF)
  obtain ⟨C₃, x₃, k₃⟩ := h₃ ε CF (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hCF)
  refine ⟨max C₁ (max C₂ C₃), max x₁ (max x₂ x₃), fun C hC D large₂ he hx hR T Lc μ₀ hL G => H G μ₀ C _ _ hL ?_ ?_ ?_⟩
  · exact k₁ C (le_trans (le_max_left _ _) hC) D large₂ he (le_trans (le_max_left _ _) hx) hR T Lc μ₀ hL G
  · exact k₂ C (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hC) D large₂ he
      (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx) hR T Lc μ₀ hL G
  · exact k₃ C (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hC) D large₂ he
      (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx) hR T Lc μ₀ hL G

end GlobalTheory.SqStepK

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount
open GlobalTheory.FrameTransport


theorem _root_.GlobalTheory.T.frame_mulVec_completedIdeal_mem_completedIdealLattice : ∀ {D : D7} {n : ℕ} (fr : GL (Fin n) D.host.E) (𝔪 : Ideal (𝓞 D.host.E)) (w : Fin n → Lev.EAf D), (∀ i, w i ∈ Submodule.span (Formalism.L2.Herm.intAf D.host.F D.host.E) ((fun b : 𝓞 D.host.E => GlobalTheory.FrameTransport.inclEAf D (b : D.host.E)) '' (𝔪 : Set (𝓞 D.host.E)))) → (Formalism.UG.bc (GlobalTheory.FrameTransport.inclEAf D) fr).val *ᵥ w ∈ Formalism.L2.Herm.hatL (F := D.host.F) (𝔪 • colLat fr) := by
  first | exact @GlobalTheory.FrameColSmul.mulVec_mem | exact GlobalTheory.FrameColSmul.mulVec_mem | (intros; apply GlobalTheory.FrameColSmul.mulVec_mem <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount
open GlobalTheory.FrameTransport


theorem _root_.GlobalTheory.T.completedColumnLattice_integral_frameCoords : ∀ {D : D7} {n : ℕ} (fr : GL (Fin n) D.host.E) (y : Fin n → Lev.EAf D), y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr) → ∀ i, ((Formalism.UG.bc (GlobalTheory.FrameTransport.inclEAf D) fr)⁻¹.val *ᵥ y) i ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  first | exact @GlobalTheory.FrameTransport.hatL_colLat_coord_int | exact GlobalTheory.FrameTransport.hatL_colLat_coord_int | (intros; apply GlobalTheory.FrameTransport.hatL_colLat_coord_int <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount
open GlobalTheory.FrameTransport

theorem _root_.GlobalTheory.T.exists_standardUnitary_frameConj_eq : ∀ {D : D7} (V : HSp D) (fr : GL (Fin V.rank) D.host.E), Formalism.UG.cT (↑D.sp.cm.sig) (fr : Matrix (Fin V.rank) (Fin V.rank) D.host.E) * V.gram * (fr : Matrix (Fin V.rank) (Fin V.rank) D.host.E) = 1 → ∀ M : GL (Fin V.rank) (Lev.EAf D), M ∈ UA D.sp.cm V.gram → ∃ h : StandardLatticesGL3.GA D V.rank, GlobalTheory.FrameTransport.frConj fr h.1 = M := by
  first | exact @GlobalTheory.FrameTransport.exists_frConj_eq | exact GlobalTheory.FrameTransport.exists_frConj_eq | (intros; apply GlobalTheory.FrameTransport.exists_frConj_eq <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount
open GlobalTheory.FrameTransport

theorem _root_.GlobalTheory.T.frameConj_standardUnitary_mem_unitaryFiniteAdelic : ∀ {D : D7} (V : HSp D) (fr : GL (Fin V.rank) D.host.E), Formalism.UG.cT (↑D.sp.cm.sig) (fr : Matrix (Fin V.rank) (Fin V.rank) D.host.E) * V.gram * (fr : Matrix (Fin V.rank) (Fin V.rank) D.host.E) = 1 → ∀ h : StandardLatticesGL3.GA D V.rank, GlobalTheory.FrameTransport.frConj fr h.1 ∈ UA D.sp.cm V.gram := by
  first | exact @GlobalTheory.FrameTransport.frConj_mem_UA | exact GlobalTheory.FrameTransport.frConj_mem_UA | (intros; apply GlobalTheory.FrameTransport.frConj_mem_UA <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount
open GlobalTheory.FrameTransport


theorem _root_.GlobalTheory.T.finiteAdeleModelsIso_mem_integral_of_OhE : ∀ {D : D7} (x : StandardLatticesGL3.AE D), x ∈ StandardLatticesGL3.OhE D → GlobalTheory.FrameTransport.adSwap D x ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  first | exact @GlobalTheory.FrameTransport.adSwap_mem_intAf_of_OhE | exact GlobalTheory.FrameTransport.adSwap_mem_intAf_of_OhE | (intros; apply GlobalTheory.FrameTransport.adSwap_mem_intAf_of_OhE <;> assumption)
end

section

open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormExact

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.continuous_heckeCharacterFinitePart : ∀ {D : D7} {N : ℕ} (c : HeckeU D N), Continuous (GlobalTheory.HeckeUChar.finChar c) := by
  first | exact @GlobalTheory.HeckeUChar.continuous_finChar | exact GlobalTheory.HeckeUChar.continuous_finChar | (intros; apply GlobalTheory.HeckeUChar.continuous_finChar <;> assumption)
end

section

open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.StdPar GlobalTheory.IdTorus
open Formalism.UG (cT)
open GlobalTheory.Doubling (absE conjUnit)
open scoped TensorProduct


theorem _root_.GlobalTheory.T.idelicFrameTorusElement_matrix_eq : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}, IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y →
    ∀ {l : Fin r → (AF F ⊗[F] E)ˣ} {a : GAd σ J}, IsIdTorusElt σ J X Y l a →
    (matHom _ σ J a).1 = 1 + adMat F X * diagonal (fun k => ((l k : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) - 1) * adMat F (cT (σ : E →+* E) Y * J)
      + adMat F Y * diagonal (fun k => (((conjUnit σ (l k))⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) - 1) * adMat F (cT (σ : E →+* E) X * J) := by
  first | exact @GlobalTheory.IdTorus.mat_eq_of_isIdTorusElt | exact GlobalTheory.IdTorus.mat_eq_of_isIdTorusElt | (intros; apply GlobalTheory.IdTorus.mat_eq_of_isIdTorusElt <;> assumption)
end

section

open GlobalTheory.SumCount GlobalTheory.SumSize

theorem _root_.GlobalTheory.T.datumCountBound_largeData : GlobalTheory.SumCount.DataK := by
  first | exact @GlobalTheory.SumCount.DataCount.dataK | exact GlobalTheory.SumCount.DataCount.dataK | (intros; apply GlobalTheory.SumCount.DataCount.dataK <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.SumSize GlobalTheory.KerConjMean

theorem _root_.GlobalTheory.T.rationalEqualSignKernels_largeConstants : BigC fun _ ch _ _ => RatTopAt ch := by
  first | exact @GlobalTheory.KerConjMean.ratTopAt_big | exact GlobalTheory.KerConjMean.ratTopAt_big | (intros; apply GlobalTheory.KerConjMean.ratTopAt_big <;> assumption)
end
