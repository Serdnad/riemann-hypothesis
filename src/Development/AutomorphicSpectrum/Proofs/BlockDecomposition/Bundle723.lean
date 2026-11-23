module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle002
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.PropsCos
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle444
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle502
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle705
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle712
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle714
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle718
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle719
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle710
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle711
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle708
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle716
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle720
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
import Mathlib.RingTheory.Radical.NatInt
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

@[expose] public section

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg

theorem _root_.GlobalTheory.T.exists_segment_representation : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ : Segment k), ∃ π : IrrRep (GL (Fin Δ.deg) k), IsLSeg Δ π.ρ := by
  first | exact @GlobalTheory.CompanionTheory.SegExists.exists_isLSeg | exact GlobalTheory.CompanionTheory.SegExists.exists_isLSeg | (intros; apply GlobalTheory.CompanionTheory.SegExists.exists_isLSeg <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M

theorem _root_.GlobalTheory.T.langlands_sum_subquotient_product : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL), LSocleGL k → LSegJacquet k → LOrderFree k → (∀ x : IrrGL (k := k), ∃ 𝔪 : Multiset (Segment k), IsL 𝔪 x.rep) → ∀ (𝔪 𝔫 : Multiset (Segment k)) (x : Fin 2 → IrrGL (k := k)) (y : IrrGL (k := k)) (hd : ∑ a, (x a).1 = y.1), IsL 𝔪 (x 0).rep → IsL 𝔫 (x 1).rep → IsL (𝔪 + 𝔫) y.rep → IsSubquotient y.rep (prodIrr x hd) := by
  first | exact @GlobalTheory.CompanionTheory.LangSumSub.main | exact GlobalTheory.CompanionTheory.LangSumSub.main | (intros; apply GlobalTheory.CompanionTheory.LangSumSub.main <;> assumption)
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.frame_integral_eq_coefficient_nonrepresented : ∀ (D : D7) (r : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (μ : Measure (Mx D V.rank r)) (lam : Measure (hermA D r)) (ν : Measure (GA D V)) (φ : Mx D V.rank r → ℂ), Hyp D r V ψ θ μ lam ν φ → ∀ (t : ℕ) (β : HermE D r), GlobalTheory.CompanionTheory.WeilSiegel.Deg.IsBlockNF t β → (¬ ∃ x : Matrix (Fin V.rank) (Fin r) D.host.E, x.rank = r ∧ gramQ V x = β.1) → IfrB V ν φ β = W ψ V μ lam φ β := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.noFrame | exact GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.noFrame | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.noFrame <;> assumption)
end

section

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.FJE.PcShear

theorem jc_zero {D : D7} {ρ p : ℕ} (y : Mx D ρ p) : GlobalTheory.CompanionTheory.FJE.jc y 0 = 0 := by
  apply Subtype.ext
  have h : adj (0 : Mx D ρ p) = 0 := by
    ext i j
    simp [adj]
  show (HMul.hMul y (adj (0 : Mx D ρ p)) : Mx D ρ ρ) + (HMul.hMul (0 : Mx D ρ p) (adj y) : Mx D ρ ρ) = _
  rw [h]
  simp

theorem chz_neg {D : D7} {ρ : ℕ} (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ) (b₀ : HermE D ρ)
    (z : hermA D ρ) : chz ψ b₀ (-z) = conj (chz ψ b₀ z) := by
  obtain ⟨hadd, hnorm, -, -⟩ := GlobalTheory.T.centre_character_properties ψ hψ b₀
  have h0 : chz ψ b₀ (0 : hermA D ρ) = 1 := by
    have h := hadd 0 0
    rw [add_zero] at h
    have hne : chz ψ b₀ (0 : hermA D ρ) ≠ 0 := by
      intro h'
      have := hnorm 0
      rw [h'] at this
      simp at this
    exact (mul_eq_left₀ hne).1 h.symm
  have h1 : chz ψ b₀ z * chz ψ b₀ (-z) = 1 := by
    rw [← hadd, add_neg_cancel, h0]
  have h2 : chz ψ b₀ z * conj (chz ψ b₀ z) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hnorm]
    simp
  have hne : chz ψ b₀ z ≠ 0 := left_ne_zero_of_mul_eq_one h1
  exact mul_left_cancel₀ hne (h1.trans h2.symm)

theorem zc_sh {D : D7} {n ρ p : ℕ} {hn : ρ + p = n} (M : Maps D hn) (m : Meas D ρ p)
    (ψ : AddChar (AF D.host.F) ℂ) (b₀ : HermE D ρ) (F : G D n → ℂ) (hF : LeftInv (GF D n) F)
    (ξ : Matrix (Fin ρ) (Fin p) D.host.E) (k : G D n) :
    zc M m ψ b₀ F (M.sh (GlobalTheory.CompanionTheory.FJE.rt ξ) * k) = zc M m ψ b₀ F k := by
  unfold zc
  congr 1
  funext z
  have hc : M.sh (GlobalTheory.CompanionTheory.FJE.rt ξ) * M.nzx z 0 = M.nzx z 0 * M.sh (GlobalTheory.CompanionTheory.FJE.rt ξ) := by
    have := GlobalTheory.T.shift_conj_heisenberg M (GlobalTheory.CompanionTheory.FJE.rt ξ) z 0
    rwa [jc_zero, add_zero] at this
  have hr : M.sh (GlobalTheory.CompanionTheory.FJE.rt ξ) ∈ GF D n := (GlobalTheory.T.rational_points_heisenberg_group M).1 ξ
  rw [← mul_assoc, ← hc, mul_assoc, hF _ hr]

theorem zc_at {D : D7} {n ρ p : ℕ} {hn : ρ + p = n} (M : Maps D hn) (m : Meas D ρ p)
    (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ) (b₀ : HermE D ρ) (F : G D n → ℂ)
    (hF : LeftInv (GF D n) F) (ξ : Matrix (Fin ρ) (Fin p) D.host.E) (h : G D n) (x : Mx D ρ p) :
    zc M m ψ b₀ F (M.nzx 0 x * (M.sh (GlobalTheory.CompanionTheory.FJE.rt ξ) * h)) =
      conj (GlobalTheory.CompanionTheory.FJE.chv ψ b₀ x (GlobalTheory.CompanionTheory.FJE.rt ξ)) * zc M m ψ b₀ F (M.nzx 0 x * h) := by
  set c : hermA D ρ := -GlobalTheory.CompanionTheory.FJE.jc (GlobalTheory.CompanionTheory.FJE.rt ξ) x with hc
  have h1 : M.sh (GlobalTheory.CompanionTheory.FJE.rt ξ) * M.nzx c x = M.nzx 0 x * M.sh (GlobalTheory.CompanionTheory.FJE.rt ξ) := by
    have := GlobalTheory.T.shift_conj_heisenberg M (GlobalTheory.CompanionTheory.FJE.rt ξ) c x
    rwa [hc, neg_add_cancel] at this
  have h2 : M.nzx c x = M.nzx c 0 * M.nzx 0 x := by
    rw [GlobalTheory.CompanionTheory.NzxAdd.nzx_add, add_zero, zero_add]
  have h3 : M.nzx 0 x * (M.sh (GlobalTheory.CompanionTheory.FJE.rt ξ) * h) =
      M.sh (GlobalTheory.CompanionTheory.FJE.rt ξ) * (M.nzx c 0 * (M.nzx 0 x * h)) := by
    rw [← mul_assoc, ← h1, h2]
    simp only [mul_assoc]
  rw [h3, zc_sh M m ψ b₀ F hF, GlobalTheory.T.centre_coefficient_equivariance M m ψ hψ b₀ F hF, hc, chz_neg ψ hψ, GlobalTheory.T.centre_character_commutator]

theorem pc_sh : ∀ {D : D7} {n ρ p : ℕ} {hn : ρ + p = n} (M : Maps D hn) (m : Meas D ρ p) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ (b₀ : HermE D ρ) (F : G D n → ℂ), LeftInv (GF D n) F → ∀ (ξ : Matrix (Fin ρ) (Fin p) D.host.E) (h : G D n), pc M m ψ b₀ F (M.sh (GlobalTheory.CompanionTheory.FJE.rt ξ) * h) = ∫ x in m.𝓕, conj (GlobalTheory.CompanionTheory.FJE.chv ψ b₀ x (GlobalTheory.CompanionTheory.FJE.rt ξ)) * zc M m ψ b₀ F (M.nzx 0 x * h) ∂m.μ := by
  intro D n ρ p hn M m ψ hψ b₀ F hF ξ h
  unfold PositivityTheory.Rg.Rsw.pc
  congr 1
  funext x
  exact zc_at M m ψ hψ b₀ F hF ξ h x

end GlobalTheory.CompanionTheory.FJE.PcShear
end
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.Jp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_residue_character_of_conductor : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (v : Pl D), GoodPsi D ψ v → ∀ ϖ : Ov D v, Irreducible ϖ → ∀ w : (Lv D v)ˣ, (w : Lv D v) = algebraMap (Ov D v) (Lv D v) ϖ → ∃ ψ₀ : AddChar (kv D v) ℂ, ψ₀ ≠ 1 ∧ ∀ c : Ov D v, psiV D.host.F ψ v (((w⁻¹ : (Lv D v)ˣ) : Lv D v) * algebraMap (Ov D v) (Lv D v) c) = ψ₀ (IsLocalRing.residue (Ov D v) c) := by
  first | exact @GlobalTheory.CompanionTheory.Jp.ResChar.main | exact GlobalTheory.CompanionTheory.Jp.ResChar.main | (intros; apply GlobalTheory.CompanionTheory.Jp.ResChar.main <;> assumption)
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.Jp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.local_image_of_unipotent_element : ∀ (D : D7) (n : ℕ) (nb : hermA D n → G D n), IsNMap nb → ∀ (v : Pl D) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (x : hermA D n), thU D n v τ (proj D.sp.cm.sig (Jst D n) v (nb x)) = nU (tauC τ x.1) := by
  first | exact @GlobalTheory.CompanionTheory.Jp.thU_proj_nMap | exact GlobalTheory.CompanionTheory.Jp.thU_proj_nMap | (intros; apply GlobalTheory.CompanionTheory.Jp.thU_proj_nMap <;> assumption)
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.Jp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.bijective_local_unitary_to_GL : ∀ (D : D7) (n : ℕ) (v : Pl D) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v), Function.Bijective (thU D n v τ) := by
  first | exact @GlobalTheory.CompanionTheory.Jp.thU_bijective | exact GlobalTheory.CompanionTheory.Jp.thU_bijective | (intros; apply GlobalTheory.CompanionTheory.Jp.thU_bijective <;> assumption)
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.Jp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.character_pairing_local_hermitian : ∀ (D : D7) (n : ℕ) (v : Pl D) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (ψ : AddChar (AF D.host.F) ℂ) (x : hermA D n), (∀ w i j, compInf D.host.F D.host.E w (x.1 i j) = 0) → (∀ v' ≠ v, ∀ i j, cv D v' (x.1 i j) = 0) → ∀ β : HermE D n, pch ψ x.1 (rat β.1) = psiV D.host.F ψ v (Matrix.trace (tauC τ x.1 * β.1.map τ)) := by
  first | exact @GlobalTheory.CompanionTheory.Jp.SplitPair.pch_rat_split | exact GlobalTheory.CompanionTheory.Jp.SplitPair.pch_rat_split | (intros; apply GlobalTheory.CompanionTheory.Jp.SplitPair.pch_rat_split <;> assumption)
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.Jp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.mem_maximal_compact_iff_integral_image : ∀ (D : D7) (n : ℕ) (v : Pl D) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (g : GLoc D.sp.cm.sig (Jst D n) v), g ∈ GlobalTheory.LocIntw.KUpFin D.sp.cm.sig (Jst D n) v ↔ thU D n v τ g ∈ (inL (O := Ov D v) (L := Lv D v) (n := n)).range := by
  first | exact @GlobalTheory.CompanionTheory.Jp.SplitK.mem_KUpFin_iff | exact GlobalTheory.CompanionTheory.Jp.SplitK.mem_KUpFin_iff | (intros; apply GlobalTheory.CompanionTheory.Jp.SplitK.mem_KUpFin_iff <;> assumption)
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.Jp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.normalized_valuation_uniformizer : ∀ (D : D7) (v : Pl D) (ϖ : Ov D v), Irreducible ϖ → ∀ w : (Lv D v)ˣ, (w : Lv D v) = algebraMap (Ov D v) (Lv D v) ϖ → NvOK (O := Ov D v) (nvL D v) w := by
  first | exact @GlobalTheory.CompanionTheory.Jp.nvOK_nvL | exact GlobalTheory.CompanionTheory.Jp.nvOK_nvL | (intros; apply GlobalTheory.CompanionTheory.Jp.nvOK_nvL <;> assumption)
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.Jp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_global_hermitian_local_approximation : ∀ (D : D7) (n : ℕ) (v : Pl D) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (X : Matrix (Fin n) (Fin n) (Fv D.host.F v)), ∃ x : hermA D n, (∀ w i j, compInf D.host.F D.host.E w (x.1 i j) = 0) ∧ (∀ v' ≠ v, ∀ i j, cv D v' (x.1 i j) = 0) ∧ tauC τ x.1 = X ∧ ((∀ i j, X i j ∈ v.adicCompletionIntegers D.host.F) → ∀ i j, cv D v (x.1 i j) ∈ intLoc D.host.F D.host.E v) := by
  first | exact @GlobalTheory.CompanionTheory.Jp.exists_herm_at | exact GlobalTheory.CompanionTheory.Jp.exists_herm_at | (intros; apply GlobalTheory.CompanionTheory.Jp.exists_herm_at <;> assumption)
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.Jp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.modulus_upper_parabolic_local : ∀ (D : D7) (n : ℕ) (v : Pl D) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (y : GLoc D.sp.cm.sig (Jst D n) v) (a d : GL (Fin n) (Fv D.host.F v)) (b : Matrix (Fin n) (Fin n) (Fv D.host.F v)), thU D n v τ y = pM a d b → ∃ hy : y ∈ GlobalTheory.LocIntw.upperParabolic (Fv D.host.F v) D.sp.cm.sig (Jst D n), absEv D.host.F D.host.E v (GlobalTheory.LocIntw.aUp (Fv D.host.F v) D.sp.cm.sig (Jst D n) ⟨y, hy⟩) = nvL D v (Matrix.GeneralLinearGroup.det a) / nvL D v (Matrix.GeneralLinearGroup.det d) := by
  first | exact @GlobalTheory.CompanionTheory.Jp.UpTri.upperParabolic_height | exact GlobalTheory.CompanionTheory.Jp.UpTri.upperParabolic_height | (intros; apply GlobalTheory.CompanionTheory.Jp.UpTri.upperParabolic_height <;> assumption)
end
