module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwLMulSelf
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.Bundle001
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle001
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Bundle001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle467
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.MapUgAlgebraMap
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.ResCoeff
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SEqOne
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.GlobalDifferentialForms.FormCos
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle468
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DividedPowerReduction.Bundle001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle340
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalSystemQuotients.FlatL
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuotientReductionBijectiveOfFlat
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.GrSplit
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.Bundle005
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle469
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MapHComp
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
import Std.Tactic.BVDecide.Normalize.Bool
import Std.Tactic.BVDecide.Normalize.Prop
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.IsMultZero
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.IsCoreMod
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLoc
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsDPMorphismBot
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusWittActions.TeichmullerCongruence
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.HodgeC
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DpZeroRight
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalSystemQuotients.ModFSW
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

section

open Finset PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.LvChain
open CompanionTheory.D.LK (Pos)
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.LvChainAdj

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

def ip (x z : Cq n V) : ℂ := ∑ A, ⟪x A, z A⟫_ℂ

theorem sgL_conj (i : Lt n) (A : Finset (Lt n)) : (starRingEnd ℂ) (sgL i A) = sgL i A := by
  simp [PositivityTheory.RgBcC.RealD.sgL]

theorem sgL_erase_self (i : Lt n) {A : Finset (Lt n)} (h : i ∈ A) : sgL i (A.erase i) = sgL i A := by
  rw [GlobalTheory.CompanionTheory.LvChain.sgL_erase i h, GlobalTheory.CompanionTheory.LvChain.twL_self, one_mul]

theorem ip_creL (i : Lt n) (x z : Cq n V) : ip (creL i x) z = ip x (annL i z) := by
  classical
  have hL : GlobalTheory.CompanionTheory.LvChainAdj.ip (PositivityTheory.RgBcC.RealD.creL i x) z =
      ∑ A ∈ Finset.univ.filter (fun A => i ∈ A),
        PositivityTheory.RgBcC.RealD.sgL i A * ⟪x (A.erase i), z A⟫_ℂ := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun A _ => ?_
    rw [GlobalTheory.CompanionTheory.LvChain.creL_apply]
    split_ifs <;> simp [inner_smul_left, GlobalTheory.CompanionTheory.LvChainAdj.sgL_conj] <;> ring
  have hR : GlobalTheory.CompanionTheory.LvChainAdj.ip x (PositivityTheory.RgBcC.RealD.annL i z) =
      ∑ B ∈ Finset.univ.filter (fun B => i ∉ B),
        PositivityTheory.RgBcC.RealD.sgL i B * ⟪x B, z (insert i B)⟫_ℂ := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun B _ => ?_
    rw [GlobalTheory.CompanionTheory.LvChain.annL_apply]
    split_ifs <;> simp [inner_smul_right]
  rw [hL, hR]
  refine Finset.sum_nbij' (fun A => A.erase i) (fun B => insert i B) ?_ ?_ ?_ ?_ ?_
  · intro A _
    simp
  · intro B _
    simp
  · intro A hA
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hA
    exact Finset.insert_erase hA
  · intro B hB
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hB
    exact Finset.erase_insert hB
  · intro A hA
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hA
    rw [GlobalTheory.CompanionTheory.LvChainAdj.sgL_erase_self i hA, Finset.insert_erase hA]

theorem ip_conj (x z : Cq n V) : (starRingEnd ℂ) (ip x z) = ip z x := by
  unfold GlobalTheory.CompanionTheory.LvChainAdj.ip

  rw [map_sum]
  exact Finset.sum_congr rfl fun A _ => inner_conj_symm (z A) (x A)

theorem ip_annL (i : Lt n) (x z : Cq n V) : ip (annL i x) z = ip x (creL i z) := by
  rw [← GlobalTheory.CompanionTheory.LvChainAdj.ip_conj z (PositivityTheory.RgBcC.RealD.annL i x), ← GlobalTheory.CompanionTheory.LvChainAdj.ip_creL i z x,
    GlobalTheory.CompanionTheory.LvChainAdj.ip_conj]

theorem ip_creL_annL (i k : Lt n) (x z : Cq n V) :
    ip ((creL k * annL i : Module.End ℂ (Cq n V)) x) z = ip x ((creL i * annL k : Module.End ℂ (Cq n V)) z) := by
  rw [Module.End.mul_apply, Module.End.mul_apply, GlobalTheory.CompanionTheory.LvChainAdj.ip_creL,
    GlobalTheory.CompanionTheory.LvChainAdj.ip_annL]

theorem ip_add_left (x y z : Cq n V) : ip (x + y) z = ip x z + ip y z := by
  unfold GlobalTheory.CompanionTheory.LvChainAdj.ip
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun A _ => by rw [← inner_add_left]; rfl

theorem ip_add_right (x y z : Cq n V) : ip x (y + z) = ip x y + ip x z := by
  unfold GlobalTheory.CompanionTheory.LvChainAdj.ip
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun A _ => by rw [← inner_add_right]; rfl

theorem ip_smul_left (c : ℂ) (x z : Cq n V) : ip (c • x) z = (starRingEnd ℂ) c * ip x z := by
  unfold GlobalTheory.CompanionTheory.LvChainAdj.ip
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun A _ => by rw [← inner_smul_left]; rfl

theorem ip_smul_right (c : ℂ) (x z : Cq n V) : ip x (c • z) = c * ip x z := by
  unfold GlobalTheory.CompanionTheory.LvChainAdj.ip
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun A _ => by rw [← inner_smul_right]; rfl

theorem ip_zero_left (z : Cq n V) : ip (0 : Cq n V) z = 0 := by
  unfold GlobalTheory.CompanionTheory.LvChainAdj.ip
  exact Finset.sum_eq_zero fun A _ => by
    rw [show (0 : PositivityTheory.RgBcC.RealD.Cq n V) A = 0 from rfl, inner_zero_left]

theorem ip_zero_right (x : Cq n V) : ip x (0 : Cq n V) = 0 := by
  unfold GlobalTheory.CompanionTheory.LvChainAdj.ip
  exact Finset.sum_eq_zero fun A _ => by
    rw [show (0 : PositivityTheory.RgBcC.RealD.Cq n V) A = 0 from rfl, inner_zero_right]

theorem ip_sum_left {ι : Type} (s : Finset ι) (f : ι → Cq n V) (z : Cq n V) :
    ip (∑ a ∈ s, f a) z = ∑ a ∈ s, ip (f a) z := by
  classical
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.sum_empty, Finset.sum_empty, GlobalTheory.CompanionTheory.LvChainAdj.ip_zero_left]
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, GlobalTheory.CompanionTheory.LvChainAdj.ip_add_left, ih]

theorem ip_sum_right {ι : Type} (s : Finset ι) (x : Cq n V) (f : ι → Cq n V) :
    ip x (∑ a ∈ s, f a) = ∑ a ∈ s, ip x (f a) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.sum_empty, Finset.sum_empty, GlobalTheory.CompanionTheory.LvChainAdj.ip_zero_right]
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, GlobalTheory.CompanionTheory.LvChainAdj.ip_add_right, ih]

theorem adCL_conj (p q : Fin n) (l k : Lt n) : (starRingEnd ℂ) (adCL false p q l k) = adCL false p q l k := by
  unfold PositivityTheory.RgBcC.RealD.adCL
  split_ifs <;> simp

theorem adCL_swap (p q : Fin n) (l k : Lt n) : adCL false p q l k = adCL false q p k l := by
  unfold PositivityTheory.RgBcC.RealD.adCL
  simp only [Bool.false_xor, Bool.false_bne, Prod.ext_iff]
  congr 1
  · exact if_congr
      ⟨fun ⟨h1, h2, h3, h4⟩ => ⟨h3.symm, h2.symm, h1.symm, h4.symm⟩,
        fun ⟨h1, h2, h3, h4⟩ => ⟨h3.symm, h2.symm, h1.symm, h4.symm⟩⟩ rfl rfl
  · exact if_congr
      ⟨fun ⟨h1, h2, h3, h4⟩ => ⟨h4, h2.symm, h3.symm, h1⟩,
        fun ⟨h1, h2, h3, h4⟩ => ⟨h4, h2.symm, h3.symm, h1⟩⟩ rfl rfl

theorem inUU_iff_of_adCL {lev : Fin n → ℕ} {p q : Fin n} (h : lev p = lev q) {l k : Lt n}
    (hc : adCL false p q l k ≠ 0) : inUU lev l ↔ inUU lev k := by
  unfold PositivityTheory.RgBcC.RealD.adCL at hc
  unfold PositivityTheory.RgBcC.RealD.inUU
  split_ifs at hc with h1 h2 h2
  · exact absurd (sub_self _) hc
  · obtain ⟨hq, -, hk⟩ := h1
    simp [hk, h, hq]
  · obtain ⟨hp, -, hk⟩ := h2
    simp [hk, hp, h]
  · exact absurd (sub_self _) hc

theorem ip_term {lev : Fin n → ℕ} {p q : Fin n} (h : lev p = lev q) (l k : Lt n) (x z : Cq n V) :
    ip ((if inUU lev l then adCL false p q l k • (creL k * annL l) else 0 : Module.End ℂ (Cq n V)) x) z =
      ip x ((if inUU lev k then adCL false q p k l • (creL l * annL k) else 0 : Module.End ℂ (Cq n V)) z) := by
  rw [← GlobalTheory.CompanionTheory.LvChainAdj.adCL_swap p q l k]
  by_cases hc : PositivityTheory.RgBcC.RealD.adCL false p q l k = 0
  · simp only [hc, zero_smul, ite_self, LinearMap.zero_apply, GlobalTheory.CompanionTheory.LvChainAdj.ip_zero_left,
      GlobalTheory.CompanionTheory.LvChainAdj.ip_zero_right]
  · have hiff := GlobalTheory.CompanionTheory.LvChainAdj.inUU_iff_of_adCL h hc
    by_cases hl : PositivityTheory.RgBcC.RealD.inUU lev l
    · rw [if_pos hl, if_pos (hiff.mp hl), LinearMap.smul_apply, LinearMap.smul_apply,
        GlobalTheory.CompanionTheory.LvChainAdj.ip_smul_left, GlobalTheory.CompanionTheory.LvChainAdj.ip_smul_right, GlobalTheory.CompanionTheory.LvChainAdj.adCL_conj,
        GlobalTheory.CompanionTheory.LvChainAdj.ip_creL_annL]
    · rw [if_neg hl, if_neg (mt hiff.mpr hl), LinearMap.zero_apply, LinearMap.zero_apply,
        GlobalTheory.CompanionTheory.LvChainAdj.ip_zero_left, GlobalTheory.CompanionTheory.LvChainAdj.ip_zero_right]

theorem ip_adLL {lev : Fin n → ℕ} {p q : Fin n} (h : lev p = lev q) (x z : Cq n V) :
    ip (adLL lev false p q x) z = ip x (adLL lev false q p z) := by
  unfold PositivityTheory.RgBcC.RealD.adLL
  simp only [LinearMap.sum_apply, GlobalTheory.CompanionTheory.LvChainAdj.ip_sum_left, GlobalTheory.CompanionTheory.LvChainAdj.ip_sum_right]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  exact GlobalTheory.CompanionTheory.LvChainAdj.ip_term h l k x z

theorem ip_liftL {E1 E2 : Fin n → Fin n → Module.End ℂ V}
    (hU : ∀ a b (x y : V), ⟪kA E1 E2 a b x, y⟫_ℂ = ⟪x, kA E1 E2 b a y⟫_ℂ) (p q : Fin n) (x z : Cq n V) :
    ip (liftL n (kA E1 E2 p q) x) z = ip x (liftL n (kA E1 E2 q p) z) := by
  unfold GlobalTheory.CompanionTheory.LvChainAdj.ip
  exact Finset.sum_congr rfl fun A _ => hU p q (x A) (z A)

theorem Lv_adjoint : ∀ (n : ℕ) (lev : Fin n → ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (E1 E2 : Fin n → Fin n → Module.End ℂ V),
    (∀ a b (x y : V), ⟪kA E1 E2 a b x, y⟫_ℂ = ⟪x, kA E1 E2 b a y⟫_ℂ) → ∀ p q : Fin n, lev p = lev q → ∀ x z : Cq n V,
      ∑ A, ⟪Lv lev E1 E2 p q x A, z A⟫_ℂ = ∑ A, ⟪x A, Lv lev E1 E2 q p z A⟫_ℂ := by
  intro n lev V _ _ E1 E2 hU p q h x z
  show GlobalTheory.CompanionTheory.LvChainAdj.ip _ _ = GlobalTheory.CompanionTheory.LvChainAdj.ip _ _
  unfold GlobalTheory.CompanionTheory.LvChain.Lv
  rw [LinearMap.add_apply, LinearMap.add_apply, GlobalTheory.CompanionTheory.LvChainAdj.ip_add_left,
    GlobalTheory.CompanionTheory.LvChainAdj.ip_add_right, GlobalTheory.CompanionTheory.LvChainAdj.ip_liftL hU,
    GlobalTheory.CompanionTheory.LvChainAdj.ip_adLL h]

end GlobalTheory.CompanionTheory.LvChainAdj
end
end

section

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.SWGlue

open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

variable {D : D7} {n : ℕ}

theorem weil_cell_zero {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle} {θ : InfFam D} {V : HSp D}
    {μ : Measure (Mx D V.rank n)} {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)}
    (hω : IsWeilSch ψ χ θ V μ ω) {w u : G D n} (hw : mat w = blk4 0 1 (-1) 0) (b : hermA D n)
    (hu : mat u = blk4 1 b.1 0 1) (Φ : schwartzA θ V.rank n) (g : G D n) :
    (ω (w * u * g) Φ).1 0 = Jt ψ V μ (ω g Φ).1 b := by
  have e : ω (w * u * g) Φ = ω w (ω u (ω g Φ)) := by
    simp only [map_mul, Module.End.mul_apply]
  rw [e, hω.weyl w hw _ 0]
  unfold Jt
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  have h0 : GlobalTheory.StdUnn.inner V (0 : Mx D V.rank n) y = 0 := by
    simp [GlobalTheory.StdUnn.inner, GlobalTheory.MixModel.adj]
  simp only [h0, Matrix.trace_zero, map_zero, AddChar.map_zero_eq_one, mul_one]
  rw [hω.unip u b.1 hu (ω g Φ) y, mul_comm]

theorem ndOfWhit : PositivityTheory.PfSWUS.NDOfWhit := by
  intro hU hT hW D n V ψ χ θ μ ω H l s ν Φ hS hR nb lam 𝓖 hC β hβ g
  obtain ⟨w, hw⟩ := GlobalTheory.StdUnn.Model.exists_weyl (D := D) (n := n)
  have h1 := hW D n V ψ χ θ μ ω H l s ν Φ hS hR lam 𝓖 nb hC w hw β hβ g
  rw [hT D n V ψ χ θ μ ω H l s ν Φ hS hR nb lam 𝓖 hC β hβ g]
  refine h1.congr ⟨(n : ℝ) / 2, fun z hz => ?_⟩
  show _ = fc ψ lam 𝓖 nb (fun x => eis ω H Φ x z) β g
  rw [(hU D n V ψ χ θ μ ω H l s ν Φ hS hR nb lam 𝓖 hC w hw β hβ z hz g).2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
  show _ * _ = sect ω H Φ z (w * nb b * g) * _
  rw [sect, weil_cell_zero hS.hω hw b (hC.1 b) Φ g]

end GlobalTheory.CompanionTheory.SWGlue

end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

theorem _root_.GlobalTheory.T.period_ring_universal_property : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (n : ℕ) (B : Type) [CommRing B] (h : (base l).Acr n →+* B), (∀ g : A.A →+* B ⧸ ((base l).PFil n).map h, (∀ a : Ob l, g (A.s a) = Ideal.Quotient.mk _ (h ((base l).toAcr n (WittVector.teichmuller l a)))) → ∃ f : A.Acr n →+* B, f.comp (mapAcr A.fromBase n) = h ∧ ∀ a, Ideal.Quotient.mk _ (f (A.toAcr n (WittVector.teichmuller l a))) = g a) ∧ ∀ f f' : A.Acr n →+* B, f.comp (mapAcr A.fromBase n) = h → f'.comp (mapAcr A.fromBase n) = h → (∀ a, f (A.toAcr n (WittVector.teichmuller l a)) - f' (A.toAcr n (WittVector.teichmuller l a)) ∈ ((base l).PFil n).map h) → f = f' := by
  first | exact @GlobalTheory.CompanionTheory.AcrUniv.maps_out | exact GlobalTheory.CompanionTheory.AcrUniv.maps_out | (intros; apply GlobalTheory.CompanionTheory.AcrUniv.maps_out <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison.PAlg CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.ACrisAdic

theorem acris_isAdicComplete :
    ∀ {l : ℕ} [Fact l.Prime], IsAdicComplete (Ideal.span {(l : Acris l)}) (Acris l) := by
  intro l _
  exact ACris.isAdicComplete ℂ_[l] l

end GlobalTheory.CompanionTheory.ACrisAdic
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

theorem _root_.GlobalTheory.T.witt_level_one_graded_finite : ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] [PerfectRing k l] {O : Type} [CommRing O] {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) [IsProper q] (ρ : O →+* k) (U : Cov q) (r j : ℕ),
    Module.Finite (Wc.Wm l k 1) (CH.H (sq (sFil (St (γ := Wc.pd l k 1) (p := l) (q := q) (κ := (Wc.res l k 1).comp ρ) ⊤ (Set.range U.U)) r) (sFil (St (γ := Wc.pd l k 1) (p := l) (q := q) (κ := (Wc.res l k 1).comp ρ) ⊤ (Set.range U.U)) ((r : ℤ) + 1))) j) := by
  first | exact @GlobalTheory.CompanionTheory.FibGr.level_one_gr_finite | exact GlobalTheory.CompanionTheory.FibGr.level_one_gr_finite | (intros; apply GlobalTheory.CompanionTheory.FibGr.level_one_gr_finite <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob GlobalTheory.CompanionTheory.CechSerre
universe w

theorem _root_.GlobalTheory.T.cover_intersection_graded_vanish : ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) [Smooth q]
    (U : Cov q) (a n : ℕ) (i : Fin (n + 1) → U.ι) (r : ℕ), r ≠ a → Subsingleton (HU (Fk q U a) (capT (Vk q U a) i) r) := by
  first | exact @GlobalTheory.CompanionTheory.CapVan.van | exact GlobalTheory.CompanionTheory.CapVan.van | (intros; apply GlobalTheory.CompanionTheory.CapVan.van <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.FirstChernPullback

theorem mem_VD_pb {X X' : Scheme.{0}} (D : E.LineData X) (u : X' ⟶ X) {V : X.Opens} (hV : V ∈ 𝒱D D) :
    u ⁻¹ᵁ V ∈ 𝒱D (D.pb u) := by
  obtain ⟨σ, hσ⟩ := hV
  refine ⟨Limits.pullback.lift ((u ∣_ V) ≫ σ) (u ⁻¹ᵁ V).ι ?_, ?_⟩
  · rw [Category.assoc, hσ, morphismRestrict_ι]
  · exact Limits.pullback.lift_snd _ _ _

theorem sSup_preimage {X X' : Scheme.{0}} (𝒲 : Set X.Opens) (u : X' ⟶ X) (h : sSup 𝒲 = ⊤) :
    sSup ((fun V : X.Opens => u ⁻¹ᵁ V) '' 𝒲) = ⊤ := by
  refine top_le_iff.1 fun x _ => ?_
  have hx : u x ∈ sSup 𝒲 := by rw [h]; trivial
  obtain ⟨V, hV, hxV⟩ := TopologicalSpace.Opens.mem_sSup.1 hx
  exact TopologicalSpace.Opens.mem_sSup.2 ⟨_, ⟨V, hV, rfl⟩, hxV⟩

theorem u_congr {X : Scheme.{0}} (D : E.LineData X) {A : CommRingCat.{0}} {a a' b b' : Spec A ⟶ D.Y} (ea : a = a') (eb : b = b')
    (h : a ≫ D.f = b ≫ D.f) (h' : a' ≫ D.f = b' ≫ D.f) :
    (Scheme.ΓSpecIso A).hom.hom (D.u a b h) = (Scheme.ΓSpecIso A).hom.hom (D.u a' b' h') := by
  subst ea eb
  rfl

end GlobalTheory.CompanionTheory.FirstChernPullback


open GlobalTheory.CompanionTheory.FirstChernPullback in
theorem GlobalTheory.CompanionTheory.FirstChernPullback.firstChern_pullback : ∀ {O O' R R' : Type} [CommRing O] [CommRing O'] [CommRing R] [CommRing R'] {I : Ideal R} {I' : Ideal R'}
    {γ : DividedPowers I} {γ' : DividedPowers I'} {X X' : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {q' : X' ⟶ Spec (CommRingCat.of O')}
    {κ : O →+* R ⧸ I} {κ' : O' →+* R' ⧸ I'} {σ : R →+* R'} (m : NMor γ q κ γ' q' κ' σ) {p : ℕ}
    (Q : ObjectProperty (Thick (nlFun γ p X q κ))) (Q₀ : ObjectProperty (Thick (nlFun γ' p X' q' κ'))) (hQ : Used Q₀)
    (h : ∀ T, St Q₀ {⊤} T → Q ((m.mor p).obj T)) (D : E.LineData X) (N : ℕ) (z : HO Q 2) (z' : HO (St Q₀ {⊤}) 2),
    sSup (𝒱D D) = ⊤ → IsFirstChernThickening Q D N z → IsFirstChernThickening (St Q₀ {⊤}) (D.pb m.u) N z' → (m.smor Q (St Q₀ {⊤}) h).o.pull 2 z = z' := by
  intro O O' R R' _ _ _ _ I I' γ γ' X X' q q' κ κ' σ m p Q Q₀ hQ h D N z z' hD hz hz'
  let 𝒱 : Set X'.Opens := (fun V : X.Opens => m.u ⁻¹ᵁ V) '' 𝒱D D
  have h1 : St Q₀ 𝒱 ≤ St Q₀ {⊤} := fun T hT => ⟨hT.1, ⊤, rfl, fun _ _ => trivial⟩
  have hc : ∀ W ∈ ({⊤} : Set X'.Opens), W ≤ sSup 𝒱 := by
    rintro W rfl
    exact (sSup_preimage _ m.u hD).ge
  apply (GlobalTheory.T.cech_refinement_cohomology_bijective Q₀ hQ 𝒱 {⊤} h1 hc 2).2.2.1
  let G' : (St Q₀ 𝒱).FullSubcategory ⥤ (St Q₀ {⊤}).FullSubcategory := ObjectProperty.ιOfLE h1
  let sm := m.smor Q (St Q₀ {⊤}) h
  let G'' : (St Q₀ 𝒱).FullSubcategory ⥤ Q.FullSubcategory := G' ⋙ sm.G
  have hV' : ∀ T, ∃ V ∈ 𝒱D (D.pb m.u), InU V (G'.obj T).obj := by
    rintro ⟨T, -, -, ⟨V, hV, rfl⟩, hT⟩
    exact ⟨_, mem_VD_pb D m.u hV, hT⟩
  have hV : ∀ T, ∃ V ∈ 𝒱D D, InU V (G''.obj T).obj := by
    rintro ⟨T, -, -, ⟨V, hV, rfl⟩, hT⟩
    exact ⟨V, hV, hT⟩
  obtain ⟨Λ'⟩ := GlobalTheory.T.exists_crystalline_lift (q := q') (b := nlBase R' I' γ' p) (ht := rfl) (κ := κ') (G' ⋙ (St Q₀ {⊤}).ι) (D.pb m.u) (fun T => by
    obtain ⟨V, ⟨s, hs⟩, hT⟩ := hV' T
    have hr : Set.range (pt (G'.obj T).obj) ⊆ Set.range V.ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨x, rfl⟩
      exact hT (show x ∈ (⊤ : Scheme.Opens _) from trivial)
    refine ⟨IsOpenImmersion.lift V.ι (pt (G'.obj T).obj) hr ≫ s, ?_⟩
    rw [Category.assoc, hs, IsOpenImmersion.lift_fac]
    rfl)
  let Λ : B.CLift (q := q) (b := nlBase R I γ p) (ht := rfl) (κ := κ) (G'' ⋙ Q.ι) D :=
    { p := fun T => Λ'.p T ≫ Limits.pullback.fst D.f m.u
      hp := fun T => by
        have e := Λ'.hp T
        rw [Category.assoc, Limits.pullback.condition, ← Category.assoc]
        exact congrArg (· ≫ m.u) e
      w := fun φ => Λ'.w φ
      hw := fun {T T'} φ hh => by
        have hh' : (B.thSp ((G' ⋙ (St Q₀ {⊤}).ι).map φ) ≫ Λ'.p T) ≫ (D.pb m.u).f = Λ'.p T' ≫ (D.pb m.u).f := by
          rw [Category.assoc, Λ'.hp T, Λ'.hp T']
          exact congrArg (fun y => y.1.2) ((G' ⋙ (St Q₀ {⊤}).ι).map φ).pt
        refine (Λ'.hw φ hh').trans ?_
        exact u_congr D (Category.assoc _ _ _) rfl _ hh }
  obtain ⟨hz1, hcl1⟩ := hz' _ G' hV' Λ'
  obtain ⟨hz2, hcl2⟩ := hz _ G'' hV Λ
  let ψ : CH.Mor (G' ⋙ CH.modF (sP (St Q₀ {⊤})).A) (CH.modF (sP (St Q₀ 𝒱)).A) (RingHom.id R') :=
    { G := 𝟭 _, τ := fun T => (incl h1).o.τ T, nat := fun φ x => (incl h1).o.nat φ x }
  let μ : CH.Mor (G'' ⋙ CH.modF (sP Q).A) (CH.modF (sP (St Q₀ 𝒱)).A) σ :=
    { G := 𝟭 _, τ := fun T => sm.o.τ (G'.obj T), nat := fun φ x => sm.o.nat (G'.map φ) x }
  have e1 : (incl h1).o.pull 2 z' = ψ.pull 2 ((CH.Mor.restrict (CH.modF (sP (St Q₀ {⊤})).A) G').pull 2 z') := by
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ z'
    rfl
  have e2 : (incl h1).o.pull 2 (sm.o.pull 2 z) = μ.pull 2 ((CH.Mor.restrict (CH.modF (sP Q).A) G'').pull 2 z) := by
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    rfl
  have hE : μ.pullC 2 (Λ.coc (RingHom.id R) N) = ψ.pullC 2 (Λ'.coc (RingHom.id R') N) := by
    funext s
    rfl
  have b1 : CH.d _ 2 (ψ.pullC 2 (Λ'.coc (RingHom.id R') N)) = 0 := by
    rw [ψ.d_pullC, hz1, map_zero]
  have b2 : CH.d _ 2 (μ.pullC 2 (Λ.coc (RingHom.id R) N)) = 0 := by
    rw [μ.d_pullC, hz2, map_zero]
  have k1 : ψ.pull 2 ((CH.cx _).cls _ hz1) = (CH.cx _).cls _ b1 := CrystallineSemistableComparison.P.mapH_cls ψ.hom 2 _ hz1 b1
  have k2 : μ.pull 2 ((CH.cx _).cls _ hz2) = (CH.cx _).cls _ b2 := CrystallineSemistableComparison.P.mapH_cls μ.hom 2 _ hz2 b2
  have key : ∀ (a b : CH.Cn (CH.modF (sP (St Q₀ 𝒱)).A) 2) (ha : CH.d _ 2 a = 0) (hb : CH.d _ 2 b = 0), a = b →
      (CH.cx _).cls a ha = (CH.cx _).cls b hb := by
    rintro a _ ha hb rfl
    rfl
  rw [e1, e2, ← hcl1, ← hcl2, k1, k2]
  exact key _ _ b2 b1 hE
end

section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Ls CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.LsG

theorem _root_.GlobalTheory.T.quotient_reduction_bijective_of_flat : ∀ (W : Type) [CommRing W] (l : ℕ) (K L : Cx.{1} W) (m : ℕ) (f : Cx.Hom K (quo l L m) (RingHom.id W)), FlatL l m K → FlatL l (m + 1) L → (∀ j, Function.Bijective (f.mapH j)) → ∀ b (h : b ≤ m) j, Function.Bijective ((qred l f h).mapH j) := by
  first | exact @GlobalTheory.CompanionTheory.QredFlat.qred_bij | exact GlobalTheory.CompanionTheory.QredFlat.qred_bij | (intros; apply GlobalTheory.CompanionTheory.QredFlat.qred_bij <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.RedPull

theorem incl_redM : ∀ {b : Base} {L : b.Fun} {Q Q' : ObjectProperty (Thick L)} (h : Q' ≤ Q) (r : Option ℤ) (c : b.R) (j : ℕ) (z : HO Q j),
    ((incl h).sq (a := IdF.top _) (a' := IdF.top _) (fun _ _ _ => trivial) (incl_std h r c)).pull j (redM Q r c j z) =
      redM Q' r c j ((incl h).o.pull j z) := by
  intro b L Q Q' h r c j z
  exact sq_toSq (incl h) _ _ (fun _ _ _ => trivial) (incl_std h r c) j z

end GlobalTheory.CompanionTheory.RedPull
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

theorem _root_.GlobalTheory.T.exists_continuous_epsilon_power : ∀ {l : ℕ} [Fact l.Prime] (ε : Eps l), ∃ η : ((base l).cont ℤ_[l]).A,
  (∀ (m : ℕ) (z : ℤ_[l]), Hom.f ((base l).evCont z) η - (base l).s (ε.e 0) ^ (PadicInt.toZModPow m z).val ∈ Ideal.span {(base l).pi ^ (l ^ m)}) ∧
  Hom.f (contShift (base l)) η = ((base l).cont ℤ_[l]).s (ε.e 0) * η := by
  first | exact @GlobalTheory.CompanionTheory.ContUniv.EtaFn.exists_eta | exact GlobalTheory.CompanionTheory.ContUniv.EtaFn.exists_eta | (intros; apply GlobalTheory.CompanionTheory.ContUniv.EtaFn.exists_eta <;> assumption)
end
