module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle014
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1139
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle385
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle014
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LevelPlusSubgroup
public import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1967
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2021
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1285
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2020
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1384
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2011
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
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFinsetSelfDualClassesHerm
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactUnipFlag
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2047
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsConstAlongSingleton
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1991
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1910
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1199
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038

@[expose] public section

section

open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.StdPar GlobalTheory.IdTorus
open Formalism.UG (cT)
open GlobalTheory.Doubling (absE conjUnit)
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.IdTorus

end GlobalTheory.IdTorus
end
end

section

noncomputable section

namespace GlobalTheory.CuspSplit

open NumberField IsDedekindDomain MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions
  Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum

set_option synthInstance.maxHeartbeats 200000

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}
  {c : Coeff l} {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r}

theorem idem_mul_mem_cuspOn (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ)) (Z : Comp Xo c) {G : WTZ D.host.E}
    (F : cuspW Xo c U G) : idem Z * (F : Rul Xo c) ∈ cuspOn U Z G := by
  refine ⟨GlobalTheory.CompRestr.idem_mul_mem_cuspW hU Z F.2, ?_⟩
  rw [mul_comm]
  exact mul_mem_suppOn _ (idem_mem_suppOn Z)

theorem idem_mul_of_mem_cuspOn {Z : Comp Xo c} {G : WTZ D.host.E} {f : Rul Xo c} (hf : f ∈ cuspOn U Z G) :
    idem Z * f = f :=
  (mem_suppOn_iff_idem_mul (cuspW_le_secZ G hf.1) Z).1 hf.2

theorem idem_mul_eq_zero {Z Z' : Comp Xo c} (h : Z ≠ Z') {G : WTZ D.host.E} {f : Rul Xo c}
    (hf : f ∈ cuspOn U Z' G) : idem Z * f = 0 := by
  calc idem Z * f = idem Z * (idem Z' * f) := by rw [idem_mul_of_mem_cuspOn hf]
    _ = 0 := by rw [← mul_assoc, idem_mul_idem_of_ne h, zero_mul]

theorem finsum_parts (f : Rul Xo c) : ∑ᶠ Z : Comp Xo c, idem Z * f = f := by
  haveI := CompFin.finite_comp Xo c
  haveI := Fintype.ofFinite (Comp Xo c)
  rw [finsum_eq_sum_of_fintype, sum_idem_mul]

theorem mem_latOn_part (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ)) {G : WTZ D.host.E} (F : cuspW Xo c U G)
    (hF : F ∈ latW U G) (Z : Comp Xo c) :
    (⟨_, idem_mul_mem_cuspOn hU Z F⟩ : cuspOn U Z G) ∈ latOn U Z G := by
  rw [latOn, mem_supLat_iff (idem_mul_mem_cuspOn hU Z F).2]
  intro la v hv
  show 0 ≤ v (idem Z * (F : Rul Xo c))
  rw [(isVal_valOn hv).mul, val_idem hv, zero_add]
  exact (mem_supLat.1 hF) la v (valOn_subset Z la hv)

theorem mem_latW_of_parts (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ)) {G : WTZ D.host.E} (F : cuspW Xo c U G)
    (h : ∀ Z, (⟨_, idem_mul_mem_cuspOn hU Z F⟩ : cuspOn U Z G) ∈ latOn U Z G) : F ∈ latW U G := by
  haveI := CompFin.finite_comp Xo c
  haveI := Fintype.ofFinite (Comp Xo c)
  refine mem_supLat.2 ?_
  intro la v hv
  have hval := isVal_valSet la v hv
  rw [← sum_idem_mul (F : Rul Xo c)]
  refine Finset.sum_induction _ (fun x => 0 ≤ v x) (fun a b ha hb => (le_min ha hb).trans (hval.add a b))
    (by rw [hval.zero]; exact le_top) fun Z _ => ?_
  exact (mem_supLat.1 ((mem_latOn U).1 (h Z))) la v hv

theorem cuspOn_indep (G : WTZ D.host.E) : iSupIndep (fun Z : Comp Xo c => cuspOn U Z G) := fun Z => by
  rw [Submodule.disjoint_def]
  intro x hx hx'
  have hle : (⨆ (j) (_ : j ≠ Z), cuspOn U j G) ≤ LinearMap.ker (LinearMap.mulLeft c.F (idem Z)) :=
    iSup₂_le fun j hj y hy => by
      rw [LinearMap.mem_ker, LinearMap.mulLeft_apply]
      exact idem_mul_eq_zero (Ne.symm hj) hy
  have h0 : idem Z * x = 0 := by
    have := hle hx'
    rwa [LinearMap.mem_ker, LinearMap.mulLeft_apply] at this
  calc x = idem Z * x := (idem_mul_of_mem_cuspOn hx).symm
    _ = 0 := h0

theorem iSup_cuspOn (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ)) (G : WTZ D.host.E) :
    ⨆ Z : Comp Xo c, cuspOn U Z G = cuspW Xo c U G := by
  refine le_antisymm (iSup_le fun Z => cuspOn_le U Z G) fun F hF => ?_
  haveI := CompFin.finite_comp Xo c
  haveI := Fintype.ofFinite (Comp Xo c)
  rw [← sum_idem_mul F]
  exact Submodule.sum_mem _ fun Z _ => Submodule.mem_iSup_of_mem Z (idem_mul_mem_cuspOn hU Z ⟨F, hF⟩)

theorem coe_mem_of_mem_partLat {Z : Comp Xo c} {G : WTZ D.host.E} {g : cuspW Xo c U G}
    (hg : g ∈ partLat U Z G) : (g : Rul Xo c) ∈ cuspOn U Z G := by
  obtain ⟨f, -, rfl⟩ := hg
  exact f.2

theorem partLat_indep (G : WTZ D.host.E) : iSupIndep (fun Z : Comp Xo c => partLat U Z G) := fun Z => by
  rw [Submodule.disjoint_def]
  intro x hx hx'
  have hle : (⨆ (j) (_ : j ≠ Z), partLat U j G) ≤
      (LinearMap.ker ((LinearMap.mulLeft c.F (idem Z)).comp (cuspW Xo c U G).subtype)).restrictScalars (𝓞 c.F) :=
    iSup₂_le fun j hj y hy => by
      rw [Submodule.restrictScalars_mem, LinearMap.mem_ker, LinearMap.comp_apply, Submodule.subtype_apply,
        LinearMap.mulLeft_apply]
      exact idem_mul_eq_zero (Ne.symm hj) (coe_mem_of_mem_partLat hy)
  have h0 : idem Z * (x : Rul Xo c) = 0 := by
    have := hle hx'
    rwa [Submodule.restrictScalars_mem, LinearMap.mem_ker, LinearMap.comp_apply, Submodule.subtype_apply,
      LinearMap.mulLeft_apply] at this
  apply Subtype.ext
  calc (x : Rul Xo c) = idem Z * x := (idem_mul_of_mem_cuspOn (coe_mem_of_mem_partLat hx)).symm
    _ = 0 := h0

theorem iSup_partLat (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ)) (G : WTZ D.host.E) :
    ⨆ Z : Comp Xo c, partLat U Z G = latW U G := by
  refine le_antisymm (iSup_le fun Z => partLat_le U Z G) fun F hF => ?_
  haveI := CompFin.finite_comp Xo c
  haveI := Fintype.ofFinite (Comp Xo c)
  have hF' : F = ∑ Z : Comp Xo c,
      (⟨idem Z * (F : Rul Xo c), GlobalTheory.CompRestr.idem_mul_mem_cuspW hU Z F.2⟩ : cuspW Xo c U G) := by
    apply Subtype.ext
    rw [Submodule.coe_sum]
    exact (sum_idem_mul _).symm
  rw [hF']
  refine Submodule.sum_mem _ fun Z _ => Submodule.mem_iSup_of_mem Z ?_
  exact ⟨⟨_, idem_mul_mem_cuspOn hU Z F⟩, mem_latOn_part hU F hF Z, rfl⟩

theorem splits : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (V : (c.F →+* ℂ) → HSp D)
    (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r),
    (∀ σ, GoodEmb c σ → IsUnf (U σ)) → ∀ G : WTZ D.host.E, Splits U G :=
  fun _ _ _ _ _ _ _ _ _ _ hU G =>
    ⟨fun F => ⟨(finsum_parts _).symm, fun Z => idem_mul_mem_cuspOn hU Z F,
        ⟨fun hF Z => mem_latOn_part hU F hF Z, mem_latW_of_parts hU F⟩⟩,
      ⟨cuspOn_indep G, iSup_cuspOn hU G⟩, partLat_indep G, iSup_partLat hU G⟩

end GlobalTheory.CuspSplit
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.InfSize.WtSize

theorem wtOf_abs_le {n : ℕ} {E : Finset ℚ} {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ x ∈ E, |(x : ℝ)| ≤ B) (i : Fin n) :
    |(((wtOf n E).w i : ℤ) : ℝ)| ≤ B + n + 1 := by
  unfold wtOf
  split_ifs with h
  · show |((⌊GlobalTheory.SignedHC.highestWeight E h.1 i⌋ : ℤ) : ℝ)| ≤ _
    set y := GlobalTheory.SignedHC.highestWeight E h.1 i with hy
    have hy' : (y : ℝ) = (GlobalTheory.SignedHC.descEnum E h.1 i : ℝ) - (((n : ℝ) - 1) / 2 - ((i : ℕ) : ℝ)) := by
      rw [hy]; unfold GlobalTheory.SignedHC.highestWeight; push_cast; ring
    have hd := hB _ (GlobalTheory.SignedHC.descEnum_mem E h.1 i)
    have hi : ((i : ℕ) : ℝ) + 1 ≤ n := by exact_mod_cast i.2
    have hi0 : (0 : ℝ) ≤ ((i : ℕ) : ℝ) := by positivity
    have f1 : ((⌊y⌋ : ℤ) : ℝ) ≤ y := by exact_mod_cast Int.floor_le y
    have f2 : (y : ℝ) < ⌊y⌋ + 1 := by exact_mod_cast Int.lt_floor_add_one y
    rw [abs_le] at hd ⊢
    constructor <;> linarith [hd.1, hd.2]
  · show |((((0 : Fin n → ℤ) i : ℤ)) : ℝ)| ≤ _
    have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    simp only [Pi.zero_apply, Int.cast_zero, abs_zero]
    linarith

end GlobalTheory.InfSize.WtSize

namespace GlobalTheory.InfSize.WtSize

theorem weightX_abs_le {D : D7} {large₂ : SizeData₂ D} (hs : GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows large₂) (τ : D.what₂.Tau) {x : ℚ}
    (hx : x ∈ (num D 1 τ).weightX D.R.m) : |(x : ℝ)| ≤ 5 * large₂.sc.b := by
  obtain ⟨hγb, hb⟩ := GlobalTheory.BigTop.Fun.gap_le_b hs
  have hs' := hs
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hgap, -, -⟩ := hs'
  have hS := large₂.Sc_pos
  have h4 := (isLeast_gap D 1).1.2.1
  have hm := D.R.two_le_m
  have hk := D.R.m_add_three_le_k
  have hNg : bigN D ≤ gap D 1 := by
    have := Nat.le_self_pow (by norm_num : 3 ≠ 0) (bigN D)
    omega
  have htN : D.R.t + 1 ≤ bigN D := by
    unfold bigN
    have := Nat.le_mul_of_pos_left (D.R.t + sLen D + 1) (by omega : 0 < D.R.m)
    omega
  have hsN : sLen D ≤ gap D 1 := by omega
  have hγ0 : (0 : ℝ) ≤ gap D 1 := by positivity
  have hmR : (0 : ℝ) ≤ D.R.m := by positivity
  have htR : (D.R.t : ℝ) + 1 ≤ large₂.sc.b := by
    have h1 : ((D.R.t + 1 : ℕ) : ℝ) ≤ gap D 1 := by exact_mod_cast htN.trans hNg
    push_cast at h1
    linarith
  have hsR : (sLen D : ℝ) ≤ large₂.sc.b := by
    have h1 : (sLen D : ℝ) ≤ gap D 1 := by exact_mod_cast hsN
    linarith
  have hmγ : (0 : ℝ) ≤ ((D.R.m : ℝ) + 1) * gap D 1 := by positivity
  rcases GlobalTheory.SignedHC.GridData.mem_weightX.1 hx with h | h | ⟨i, hi1, hi2, h⟩ | ⟨l, hl1, hl2, h⟩
  · obtain ⟨i, hi, rfl⟩ := GlobalTheory.SignedHC.GridData.mem_tops.1 h
    have ev : (D.hc τ).v ⟨0, by omega⟩ = ((num D 1 τ).v 2 : ℚ) :=
      (GlobalTheory.SignedHC.GridData.ofHCParam_spec (D.hc τ) (sLen D) (gap D 1) (cen D 1 τ)).1 ⟨0, by omega⟩
    obtain ⟨v0, v1⟩ := large₂.cloud_v τ ⟨0, by omega⟩
    rw [ev] at v0 v1
    have ha : (num D 1 τ).a i = ((num D 1 τ).v 2 : ℚ) + 1 / 2 + ((D.R.m : ℚ) + 1 - i) * (gap D 1 : ℚ) := rfl
    have hi' : (i : ℝ) ≤ D.R.m := by exact_mod_cast hi
    have hi0 : (0 : ℝ) ≤ i := by positivity
    have v0' : (0 : ℝ) ≤ ((num D 1 τ).v 2 : ℝ) := by exact_mod_cast v0
    have v1' : ((num D 1 τ).v 2 : ℝ) ≤ large₂.Sc := by exact_mod_cast v1
    rw [ha]
    push_cast
    have p1 : (0 : ℝ) ≤ ((D.R.m : ℝ) + 1 - i) * (gap D 1 : ℝ) := mul_nonneg (by linarith) hγ0
    have p2 : ((D.R.m : ℝ) + 1 - i) * (gap D 1 : ℝ) ≤ ((D.R.m : ℝ) + 1) * gap D 1 := by nlinarith
    rw [abs_le]; constructor <;> linarith
  · obtain ⟨i, hi2, hik, rfl⟩ := GlobalTheory.SignedHC.GridData.mem_cloudHalf.1 h
    have hik' : i ≤ D.R.k := hik
    have ev : (D.hc τ).v ⟨i - 2, by omega⟩ = ((num D 1 τ).v (i - 2 + 2) : ℚ) :=
      (GlobalTheory.SignedHC.GridData.ofHCParam_spec (D.hc τ) (sLen D) (gap D 1) (cen D 1 τ)).1 ⟨i - 2, by omega⟩
    rw [show i - 2 + 2 = i by omega] at ev
    obtain ⟨v0, v1⟩ := large₂.cloud_v τ ⟨i - 2, by omega⟩
    rw [ev] at v0 v1
    have v0' : (0 : ℝ) ≤ ((num D 1 τ).v i : ℝ) := by exact_mod_cast v0
    have v1' : ((num D 1 τ).v i : ℝ) ≤ large₂.Sc := by exact_mod_cast v1
    unfold GlobalTheory.SignedHC.GridData.vHalf
    push_cast
    rw [abs_le]; constructor <;> linarith
  · obtain ⟨a, ha, rfl⟩ := GlobalTheory.SignedHC.mem_block.1 h
    obtain ⟨c0, c1⟩ := GlobalTheory.BigTop.Fun.cen_bounds hs τ hi1 hi2
    have ec : (num D 1 τ).cen i = cen D 1 τ i := rfl
    have es : (num D 1 τ).s = sLen D := rfl
    rw [ec, es]
    have hs1 : (((sLen D - 1 : ℕ)) : ℝ) ≤ large₂.sc.b := by
      have : ((sLen D - 1 : ℕ) : ℝ) ≤ sLen D := by exact_mod_cast Nat.sub_le _ _
      linarith
    have ha' : (a : ℝ) + 1 ≤ ((sLen D - 1 : ℕ) : ℝ) := by exact_mod_cast ha
    have ha0 : (0 : ℝ) ≤ a := by positivity
    have c0' : (0 : ℝ) ≤ (cen D 1 τ i : ℝ) := by exact_mod_cast c0
    push_cast
    rw [abs_le]; constructor <;> linarith
  · obtain ⟨a, ha, rfl⟩ := GlobalTheory.SignedHC.mem_block.1 h
    have hl2' : l ≤ D.R.m := hl2
    obtain ⟨e0, e1⟩ := GlobalTheory.BigTop.Fun.numE_bounds hs τ (j := l - 1) (by omega)
    rw [show l - 1 + 1 = l by omega] at e0 e1
    have et : (num D 1 τ).t = D.R.t := rfl
    rw [et]
    have ha' : (a : ℝ) + 1 ≤ (D.R.t : ℝ) + 1 := by exact_mod_cast ha
    have ha0 : (0 : ℝ) ≤ a := by positivity
    have e0' : (0 : ℝ) ≤ ((num D 1 τ).e l : ℝ) := by exact_mod_cast e0
    push_cast
    rw [abs_le]; constructor <;> linarith

theorem wt_top_abs_le : ∃ K1 : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D), GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows large₂ → ∀ {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc), sc.cGap = 1 → ∀ τ i, |(((wt G (.top D.R.m) τ).w i : ℤ) : ℝ)| ≤ K1 * large₂.sc.b := by
  refine ⟨7, fun D large₂ hs T L sc G hc τ i => ?_⟩
  obtain ⟨hγb, hb⟩ := GlobalTheory.BigTop.Fun.gap_le_b hs
  have h4 := (isLeast_gap D 1).1.2.1
  have hNg : bigN D ≤ gap D 1 := by
    have := Nat.le_self_pow (by norm_num : 3 ≠ 0) (bigN D)
    omega
  have hn := GlobalTheory.DefRank.rank_le_bigN G (.top D.R.m) (show D.R.m ≤ D.R.m from le_rfl)
  have hnb : (((G.V (.top D.R.m)).rank : ℕ) : ℝ) ≤ large₂.sc.b := by
    have : (((G.V (.top D.R.m)).rank : ℕ) : ℝ) ≤ gap D 1 := by exact_mod_cast hn.trans hNg
    linarith
  have e : wt G (.top D.R.m) τ = wtOf (G.V (.top D.R.m)).rank ((num D 1 τ).weightX D.R.m) := by
    show wtOf _ (GlobalTheory.SignedHC.entries (Node.par D sc.cGap (.top D.R.m) τ)) = _
    rw [hc]
    exact congrArg _ (GlobalTheory.SignedHC.entries_plus _)
  rw [e]
  have := wtOf_abs_le (B := 5 * large₂.sc.b) (by linarith) (fun x hx => weightX_abs_le hs τ hx) i
  linarith

end GlobalTheory.InfSize.WtSize

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount

theorem _root_.GlobalTheory.T.parameterSizeConditions_numericBounds : ∀ {D : D7} (large₂ : SizeData₂ D), GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows large₂ → (bigN D : ℝ) ≤ large₂.sc.b ∧ (D.R.f : ℝ) ≤ large₂.sc.b ∧ 1 ≤ bigN D ∧ 1 ≤ D.R.f ∧ 2 ≤ D.R.m ∧ 1 ≤ D.host.rdE ∧ Real.log D.host.rdE ≤ Real.log large₂.sc.b / 100 ∧ 12 ≤ large₂.sc.b := by
  first | exact @GlobalTheory.SizesOfRows.sizes_of_sizeRows | exact GlobalTheory.SizesOfRows.sizes_of_sizeRows | (intros; apply GlobalTheory.SizesOfRows.sizes_of_sizeRows <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv
open GlobalTheory.PureMatch GlobalTheory.SquareFlipReach ValuativeRel


theorem _root_.GlobalTheory.T.thetaTripleSquare_splitPlace_character_eq_localGrid : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil)
    (M : Vol G) (t : T) (i j : Fin D.R.m) (e : Num G i j) (Bs : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j)
    (X : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E), IsTripleOf W M t i j e Bs Γ X →
    ∀ (w : Pl D.host.E) (v : Pl D.host.F) (hv : w.under (𝓞 D.host.F) = v) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v),
    splitPrime τ = w →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.chrW X.ν τ = ((locGrid G t w).nu i j).comp (Units.map (GlobalTheory.LFun.complMap hv).toMonoidHom) ∧
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.chrW X.α τ = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.chrW X.ν τ * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.chrW X.β τ := by
  first | exact @GlobalTheory.PureMatch.chrW_triple_split_nu | exact GlobalTheory.PureMatch.chrW_triple_split_nu | (intros; apply GlobalTheory.PureMatch.chrW_triple_split_nu <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels


theorem _root_.GlobalTheory.T.exists_nonzero_complementary_adelicSchwartz_function : ∀ {F : Type} [Field F] [NumberField F] (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) {κ : Type} [Fintype κ]
    (f : (κ → Fv F v) → ℂ), f ∈ GlobalTheory.WeilM.SB (κ → Fv F v) →
    ∃ r : (κ → AF F) → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (evFin F v) f r ∧ ∃ x₀, r x₀ ≠ 0 := by
  first | exact @GlobalTheory.RestComplement.exists_rest_ne_zero | exact GlobalTheory.RestComplement.exists_rest_ne_zero | (intros; apply GlobalTheory.RestComplement.exists_rest_ne_zero <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels


theorem _root_.GlobalTheory.T.exists_complementary_adelicSchwartz_restFunction : ∀ {F : Type} [Field F] [NumberField F] (κ : Type) [Fintype κ] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)),
    ∃ R : (κ → AF F) → ℂ, R 0 ≠ 0 ∧ ∀ φ ∈ GlobalTheory.WeilM.SB (κ → Fv F v), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (evFin F v) φ R := by
  first | exact @GlobalTheory.RestWitness.exists_rest | exact GlobalTheory.RestWitness.exists_rest | (intros; apply GlobalTheory.RestWitness.exists_rest <;> assumption)
end

section

open scoped TensorProduct NNReal ENNReal Matrix Classical
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.TowU

namespace GlobalTheory.TowU.PointVal

theorem adelicSchwartz_pointValues_admitted_alt : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ], (∀ x : κ → AF F, (LinearMap.proj x : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) ∈ (adeleClass F).adm κ) ∧ (∃ φ ∈ schA F κ, φ 0 = 1) ∧ (∀ w, ∀ φ ∈ schA F κ, schr ψ w φ ∈ schA F κ) ∧ ∀ (w w' : (κ → AF F) × (κ → AF F)) (φ : (κ → AF F) → ℂ), schr ψ w (schr ψ w' φ) = ψ (⅟(2 : AF F) * (w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2)) • schr ψ (w + w') φ := by
  intro F _ _ ψ hψ κ _
  have h3 : ∀ w, ∀ φ ∈ schA F κ, schr ψ w φ ∈ schA F κ := fun w φ hφ => GlobalTheory.ConeMeasV.schr_mem_schA hψ w hφ
  refine ⟨?_, ?_, h3, ?_⟩
  · intro x g _
    refine ⟨g (fun i => (x i).2) • ((BoundedContinuousFunction.evalCLM ℂ
      (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1)).comp
      (SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ ℂ)), fun f => ?_⟩
    simp [pureA, mul_comm]
  · obtain ⟨φ, hφ, hne⟩ := GlobalTheory.ThetaSumNe.exists_mem_schA_thetaSum_ne_zero F κ
    have : ∃ ξ : κ → F, φ (fun i => algebraMap F (AF F) (ξ i)) ≠ 0 := by
      by_contra h
      push_neg at h
      exact hne (by simp [thetaSum, h])
    obtain ⟨ξ, hξ⟩ := this
    refine ⟨(φ (fun i => algebraMap F (AF F) (ξ i)))⁻¹ • schr ψ ((fun i => algebraMap F (AF F) (ξ i)), 0) φ,
      Submodule.smul_mem _ _ (h3 _ φ hφ), ?_⟩
    simp [schr, hξ]
  · intro w w' φ
    funext x
    simp only [schr, Pi.smul_apply, smul_eq_mul, Prod.fst_add, Prod.snd_add]
    rw [← mul_assoc, ← AddChar.map_add_eq_mul, ← mul_assoc, ← AddChar.map_add_eq_mul, add_assoc x w.1 w'.1]
    congr 2
    simp only [add_dotProduct, dotProduct_add]
    have h2 : (2 : AF F) * ⅟(2 : AF F) = 1 := mul_invOf_self 2
    linear_combination (-(w.1 ⬝ᵥ w'.2)) * h2

end GlobalTheory.TowU.PointVal
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct Classical

theorem _root_.GlobalTheory.T.scaled_lattice_fourier_invariant : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ] (a : F), a ≠ 0 →
    ∀ b : κ → F, (∀ ξ : κ → F, (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) ∈ GlobalTheory.EvAdm.scaledInt F κ a →
        ∃ k : ℤ, Algebra.trace ℚ F (∑ i, ξ i * b i) = k) →
    ∀ f f' : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
      (∀ x, f' x = Complex.exp (-(2 * Real.pi * Complex.I) *
          ((Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, x i * mixedEmbedding F (b i)) : ℝ) : ℂ)) * f x) →
      schr ψ (0, fun i => algebraMap F (AF F) (b i))
          (pureA F f ((GlobalTheory.EvAdm.scaledInt F κ a : Set (κ → FiniteAdeleRing (𝓞 F) F)).indicator (fun _ => (1 : ℂ)))) =
        pureA F f' ((GlobalTheory.EvAdm.scaledInt F κ a : Set (κ → FiniteAdeleRing (𝓞 F) F)).indicator (fun _ => (1 : ℂ))) := by
  first | exact @GlobalTheory.SchrCharPure.main | exact GlobalTheory.SchrCharPure.main | (intros; apply GlobalTheory.SchrCharPure.main <;> assumption)
end
