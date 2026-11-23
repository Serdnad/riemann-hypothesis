module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.SegmentDerivatives.Bundle001
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle002
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle002
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.Bundle001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LUnlinkedIrr
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.HermitianCellMeasures.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle389
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle001
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsBlockMatrixTwoByTwoFinEq
public import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.MapsExist
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle352
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle712
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierZeroHolds
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle702
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle710
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle555
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialConstantTermBound
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle713
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.LeftInvOfIsSection
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzHeightMajorantIntegrable
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaTwistIdentity
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
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle260

@[expose] public section

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg

theorem _root_.GlobalTheory.T.exists_socle_segment_product : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ : Segment k) {N : ℕ} (hd : ∑ a, (dec Δ a).1 = N), ∃ τ : IrrRep (GL (Fin N) k), IsSocle τ.ρ (prodIrr (dec Δ) hd) := by
  first | exact @GlobalTheory.CompanionTheory.SegSocle.exists_isSocle_prodIrr_dec | exact GlobalTheory.CompanionTheory.SegSocle.exists_isSocle_prodIrr_dec | (intros; apply GlobalTheory.CompanionTheory.SegSocle.exists_isSocle_prodIrr_dec <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

theorem _root_.GlobalTheory.T.lUnlinkedIrr_of_irreducibleAdmissible : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → Zc.LSegJacquet k → GlobalTheory.Published.GeometricLemmaFiltration → GlobalTheory.BZSeg.NuPair k → GlobalTheory.BZSeg.WhitRankStd k → GlobalTheory.BZSeg.ProdIrrFiniteLength k → GlobalTheory.BZSeg.LUnlinkedIrr k := by
  first | exact @GlobalTheory.CompanionTheory.BZSeg.NuPairIrr.lUnlinkedIrr | exact GlobalTheory.CompanionTheory.BZSeg.NuPairIrr.lUnlinkedIrr | (intros; apply GlobalTheory.CompanionTheory.BZSeg.NuPairIrr.lUnlinkedIrr <;> assumption)
end

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L PositivityTheory.Rg.Rsw.Cell

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.SetCell

variable {D : D7} {p : ℕ}

theorem mem_K_of_mem_KOff {S : Finset (Pl D)} {u : G D p} (hu : u ∈ KOff D p S) : u ∈ K D p := by
  obtain ⟨hf, h1, h2⟩ := mem_levelOff.1 hu
  refine mem_levelAll.2 ⟨fun v => ?_, fun w => ?_⟩
  · by_cases hv : v ∈ S
    · rw [h1 v hv]; exact one_mem _
    · exact h2 v hv
  · rw [mem_finPts_iff_forall.1 hf w]; exact one_mem _

theorem height_mul_K {H : G D p → ℝ≥0} (hH : IsHeight H) {k : G D p} (hk : k ∈ K D p) (g : G D p) :
    H (g * k) = H g := by
  obtain ⟨q, hq, k', hk', rfl⟩ := GlobalTheory.StdUnn.Iwasawa.exists_mul D p g
  rw [mul_assoc, GlobalTheory.CompanionTheory.HtEx.height_eq hH ⟨q, hq⟩ (mul_mem hk' hk), GlobalTheory.CompanionTheory.HtEx.height_eq hH ⟨q, hq⟩ hk']

theorem w_mem_GF {w : G D p} (hw : IsW w) : w ∈ GF D p := by
  have hY : mat w⁻¹ = blk4 0 (-1) 1 0 := by
    have e2 : mat w⁻¹ * mat w = 1 :=
      (show mat (w⁻¹ * w) = mat w⁻¹ * mat w from rfl).symm.trans (by rw [inv_mul_cancel]; rfl)
    have e3 : mat w * blk4 0 (-1) 1 0 = 1 := by
      rw [show mat w = _ from hw, GlobalTheory.StdUnn.Model.submatrix_fromBlocks_mul]
      simp [GlobalTheory.StdUnn.Model.block_matrix_one]
    calc mat w⁻¹ = mat w⁻¹ * (mat w * blk4 0 (-1) 1 0) := by rw [e3, mul_one]
      _ = blk4 0 (-1) 1 0 := by rw [← mul_assoc, e2, one_mul]
  refine GlobalTheory.CompanionTheory.PcB.mem_GF w (blk4 0 1 (-1) 0) (blk4 0 (-1) 1 0) ?_ ?_
  · rw [show mat w = _ from hw, GlobalTheory.CompanionTheory.PcB.rational_map_block_matrix, GlobalTheory.CompanionTheory.PcB.rat_zero', GlobalTheory.CompanionTheory.PcB.rat_one', GlobalTheory.CompanionTheory.PcB.rat_neg',
      GlobalTheory.CompanionTheory.PcB.rat_one']
  · rw [hY, GlobalTheory.CompanionTheory.PcB.rational_map_block_matrix, GlobalTheory.CompanionTheory.PcB.rat_zero', GlobalTheory.CompanionTheory.PcB.rat_one', GlobalTheory.CompanionTheory.PcB.rat_neg',
      GlobalTheory.CompanionTheory.PcB.rat_one']

theorem npow_half_add_half (r : ℝ≥0) : npow r ((p : ℂ) / 2 + (p : ℂ) / 2) = (((r : ℝ) ^ p : ℝ) : ℂ) := by
  have e : (p : ℂ) / 2 + (p : ℂ) / 2 = (p : ℂ) := by ring
  rw [e, npow, Complex.cpow_natCast]
  push_cast
  rfl

def hp (H : G D p → ℝ≥0) (g : G D p) : ℝ := (H g : ℝ) ^ p

theorem hp_law {H : G D p → ℝ≥0} (hH : IsHt H) {q : G D p} (hq : q ∈ P D p) {a : GL (Fin p) (AE D)}
    (ha : blkA (mat q) = a.1) (g : G D p) :
    hp H (q * g) = (absA D (Matrix.GeneralLinearGroup.det a) : ℝ) ^ p * hp H g := by
  simp only [hp]
  rw [hH.2.2 q hq a ha g, NNReal.coe_mul, mul_pow]

theorem hp_pos {H : G D p → ℝ≥0} (hH : IsHt H) (g : G D p) : 0 < hp H g :=
  pow_pos (by exact_mod_cast hH.2.1 g) _

theorem exists_block {q : G D p} (hq : q ∈ P D p) : ∃ a : GL (Fin p) (AE D), blkA (mat q) = a.1 :=
  ⟨GlobalTheory.StdUnn.HeightExists.leviBlock (D := D) (n := p) ⟨q, hq⟩, rfl⟩

theorem isRho_iff_sec {H : G D p → ℝ≥0} (hH : IsHt H) (f : G D p → ℂ) : IsRho f ↔ Sec (P D p) (hp H) f := by
  constructor
  · rintro ⟨c, l⟩
    refine ⟨c, fun q hq g => ?_⟩
    obtain ⟨a, ha⟩ := exists_block hq
    rw [l q hq a ha g, hp_law hH hq ha g, npow_half_add_half]
    simp only [MonoidHom.one_apply, Circle.coe_one, one_mul]
    push_cast
    ring
  · rintro ⟨c, l⟩
    refine ⟨c, fun q hq a ha g => ?_⟩
    have h1 := l q hq g
    rw [hp_law hH hq ha g] at h1
    have h0 : ((hp H g : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (hp_pos hH g).ne'
    rw [npow_half_add_half]
    simp only [MonoidHom.one_apply, Circle.coe_one, one_mul]
    apply mul_right_cancel₀ h0
    rw [h1]
    push_cast
    ring

theorem setC : HtExist → PositivityTheory.Rg.Rsw.Cell.SetC := by
  intro hEx D p mu hmu
  obtain ⟨H, hH⟩ := GlobalTheory.StdUnn.exists_height D p
  have hI : IsHt H := GlobalTheory.CompanionTheory.HtEx.isHt_of_isHeight hH
  have hS := isRho_iff_sec hI
  refine ⟨hp H, ?_, hS, ?_, ?_⟩
  · refine ⟨GlobalTheory.StdUnn.HeightExists.isClosed_P, (hEx D p).2, ?_, hp_pos hI, ?_, ?_, ?_, ?_⟩
    · exact (NNReal.continuous_coe.comp hI.1).pow p
    · intro q hq g g'
      obtain ⟨a, ha⟩ := exists_block hq
      rw [hp_law hI hq ha g, hp_law hI hq ha g']
      ring
    · exact fun f f' hf hf' => hmu.add f f' ((hS f).2 hf) ((hS f').2 hf')
    · exact fun c f hf => hmu.smul c f ((hS f).2 hf)
    · exact fun f hf h0 => hmu.pos f ((hS f).2 hf) h0
  · intro S u hu g
    simp only [hp]
    rw [height_mul_K hH (mem_K_of_mem_KOff hu) g]
  · intro nb hnb w hw y
    have hN : ∀ f, IsRho f → mu (fun g => f (g * nb y)) = mu f := fun f hf => hmu.inv_n (nb y) y.1 (hnb y) f hf
    have hW := w_mem_GF hw
    refine ⟨fun f hf => hN f ((hS f).2 hf), fun f hf => ?_⟩
    have hf' := (hS f).2 hf
    have r1 := GlobalTheory.CompanionTheory.MuC.isRho_right hf' w⁻¹
    have r2 := GlobalTheory.CompanionTheory.MuC.isRho_right r1 (nb y)
    have e3 := hmu.inv_rat w hW _ r2
    have e2 := hN _ r1
    have e1 := hmu.inv_rat w⁻¹ ((GF D p).inv_mem hW) f hf'
    calc mu (fun g => f (g * (w * nb y * w⁻¹))) = mu (fun g => f (g * w * nb y * w⁻¹)) := by
          simp only [mul_assoc]
      _ = mu f := by rw [e3, e2, e1]

end GlobalTheory.CompanionTheory.SetCell

end
end

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.Jp

def GoodPsi (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (v : Pl D) : Prop :=
  (∀ a ∈ v.adicCompletionIntegers D.host.F, psiV D.host.F ψ v a = 1) ∧
    ∀ ϖ : v.adicCompletionIntegers D.host.F, Irreducible ϖ →
      ∃ b : v.adicCompletionIntegers D.host.F,
        psiV D.host.F ψ v ((b : Fv D.host.F v) / (ϖ : Fv D.host.F v)) ≠ 1

def GoodChi (D : D7) (χ : (AE D)ˣ →* Circle) (v : Pl D) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) : Prop :=
  ∀ a : (Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ,
    ‖splitProj τ (a : Fv D.host.F v ⊗[D.host.F] D.host.E)‖ =
      ‖splitProj (τ.comp D.sp.cm.sig) (a : Fv D.host.F v ⊗[D.host.F] D.host.E)‖ →
    χ (ideleAt D.host.F D.host.E v a) = 1

abbrev sphV (D : D7) (n : ℕ) (v : Pl D) (z : ℂ) : GLoc D.sp.cm.sig (Jst D n) v → ℂ :=
  GlobalTheory.LocIntw.sphUp (Fv D.host.F v) D.sp.cm.sig (Jst D n) (absEv D.host.F D.host.E v)
    (GlobalTheory.LocIntw.KUpFin D.sp.cm.sig (Jst D n) v) z

def GoodPlacesOutsideFiniteSet : Prop :=
  ∀ (D : D7) (r : ℕ) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ χ : (AE D)ˣ →* Circle, IsHeckeChar D χ →
    ResEta D χ r → ∀ S : Finset (Pl D), ∃ v ∉ S, GoodPsi D ψ v ∧ ∃ τ : D.host.E →ₐ[D.host.F] Fv D.host.F v, GoodChi D χ v τ

def SplitPlaceRankCutEigenvalue : Prop :=
  ∀ (D : D7) (n r t : ℕ), r + t = n → 1 ≤ r → ∀ ψ : AddChar (AF D.host.F) ℂ, IsCharAF D.host.F ψ →
    ∀ nb : hermA D n → G D n, IsNMap nb → ∀ v : Pl D, GoodPsi D ψ v → ∀ _ : D.host.E →ₐ[D.host.F] Fv D.host.F v,
    ∃ (C : Cut D n v) (c : ℂ → ℂ), C.Kills ψ r ∧ Differentiable ℂ c ∧ c ((t : ℂ) / 2) ≠ 0 ∧
      ∀ νv : Measure (KAt D n v), νv.IsHaarMeasure → IsProbabilityMeasure νv → ∀ z : ℂ,
        ∫ k : KAt D n v, ∑ x ∈ C.s, C.co x * sphV D n v z (proj D.sp.cm.sig (Jst D n) v ((k : G D n) * nb x)) ∂νv = c z

def SectionEigenfunctionMaximalCompact : Prop :=
  ∀ (D : D7) (n : ℕ) (χ : (AE D)ˣ →* Circle) (nb : hermA D n → G D n), IsNMap nb → ∀ (v : Pl D)
    (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v), GoodChi D χ v τ → ∀ (C : Cut D n v) (νv : Measure (KAt D n v)),
    νv.IsHaarMeasure → ∀ z c : ℂ,
    (∫ k : KAt D n v, ∑ x ∈ C.s, C.co x * sphV D n v z (proj D.sp.cm.sig (Jst D n) v ((k : G D n) * nb x)) ∂νv = c) →
    ∀ f : G D n → ℂ, IsLaw χ z f → (∀ k ∈ KAt D n v, ∀ g, f (g * k) = f g) → ∀ g : G D n,
      ∫ k : KAt D n v, cutR nb C f (g * k) ∂νv = c * f g

end GlobalTheory.CompanionTheory.Jp

end
end

section

open PositivityTheory.Rg.Rsw

theorem _root_.GlobalTheory.T.residue_measure_identity : MapsExist → HtExist → HeckeEta → FJEis → PcBound → RSec → EisHol → ThTotal → PcFc → SphBound → PositivityTheory.PfSWUS.FourierZero → PositivityTheory.PfSWUS.CoefDataExists → ResMu := by
  first | exact @GlobalTheory.CompanionTheory.ResMu.resMu_main | exact GlobalTheory.CompanionTheory.ResMu.resMu_main | (intros; apply GlobalTheory.CompanionTheory.ResMu.resMu_main <;> assumption)
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.ZcShift




theorem zc_shift : ∀ {D : D7} {n ρ p : ℕ} {hn : ρ + p = n} (M : Maps D hn) (m : Meas D ρ p) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ (b₀ : HermE D ρ) (F : G D n → ℂ), LeftInv (GF D n) F → ∀ (c : hermA D ρ) (h : G D n), zc M m ψ b₀ F (M.nzx c 0 * h) = chz ψ b₀ c * zc M m ψ b₀ F h := by
  intro D n ρ p hn M m ψ hψ b₀ F hF c h
  obtain ⟨hadd, hnorm, hrat, -⟩ := GlobalTheory.T.centre_character_properties ψ hψ b₀
  obtain ⟨hl, hFD, -⟩ := m.hz
  obtain ⟨i1, i2, i3, i4, -, -⟩ := GlobalTheory.TowerResNonzero.lattice_ratMx D ρ ρ
  haveI : BorelSpace (Mx D ρ ρ) := ⟨rfl⟩
  haveI : BorelSpace (hermA D ρ) := Subtype.borelSpace _
  haveI : SecondCountableTopology (hermA D ρ) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : DiscreteTopology (ratHerm D ρ) := GlobalTheory.CompanionTheory.FourierN.discrete_ratHerm
  haveI : Countable (ratHerm D ρ) := countable_of_Lindelof_of_discrete
  have hnz : ∀ z z' : hermA D ρ, M.nzx z 0 * M.nzx z' 0 = M.nzx (z + z') 0 := fun z z' => by
    have := GlobalTheory.T.unipotent_heisenberg_mul M z z' 0 0
    rwa [add_zero] at this
  have hconj : conj (chz ψ b₀ c) * chz ψ b₀ c = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hnorm c]
    simp
  set u : hermA D ρ → ℂ := fun z => F (M.nzx z 0 * h) * conj (chz ψ b₀ z) with hu
  have hper : ∀ γ ∈ ratHerm D ρ, ∀ x, u (γ + x) = u x := by
    intro γ hγ x
    simp only [hu]
    rw [← hnz, mul_assoc, hF _ ((GlobalTheory.T.rational_points_heisenberg_group M).2.2 γ hγ), hadd, hrat γ hγ, one_mul]
  have hpt : ∀ z : hermA D ρ, F (M.nzx z 0 * (M.nzx c 0 * h)) * conj (chz ψ b₀ z) = chz ψ b₀ c * u (z + c) := by
    intro z
    simp only [hu]
    rw [← mul_assoc, hnz, hadd, map_mul]
    linear_combination (-(F (M.nzx (z + c) 0 * h) * conj (chz ψ b₀ z))) * hconj
  unfold zc
  simp only [hpt]
  rw [integral_const_mul]
  congr 1
  exact GlobalTheory.CompanionTheory.ConstN.setIntegral_add_right (ratHerm D ρ) m.lz hFD u hper c

end GlobalTheory.CompanionTheory.ZcShift

end
end

section

open scoped TensorProduct ENNReal Matrix NNReal
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.Eis GlobalTheory GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdelicU GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn
open PositivityTheory.Rg.Rsw

noncomputable section

namespace GlobalTheory.CompanionTheory.EisHolFam

open GlobalTheory.StdUnn.HeightExists GlobalTheory.StdUnn.PolesModel

theorem eisHol_of_htExist : HtExist → EisHol := by
  intro _ D p χ _ c f hc hd hl h
  haveI := t2Space_adeleRing' (F := D.host.F)
  have hsub : rightOf (max c ((p : ℝ) / 2)) ⊆ {z : ℂ | c < z.re} := fun z hz =>
    lt_of_le_of_lt (le_max_left _ _) (mem_rightOf.1 hz)
  have key := analyticOnNhd_cosetSum (P := P D p) (Γ := GF D p) (K := K D p) (δ := modP (D := D) (n := p))
    (χ := χ.comp detP) (ρ := (p : ℝ) / 2) (σ := max c ((p : ℝ) / 2)) (Φ := f) isIwasawa isCompact_K
    (hc.mono (Set.prod_mono hsub (Set.subset_univ _)))
    (fun z hz q g => by
      have := hl z (hsub hz) q q.2 (leviBlock (D := D) (n := p) q) rfl g
      push_cast
      exact this)
    (fun τ hτ => summable_spherical τ (lt_of_le_of_lt (le_max_right _ _) hτ))
    (fun g => (hd g).mono hsub) h
  refine key.differentiableOn.mono fun z hz => ?_
  exact mem_rightOf.2 (max_lt hz.1 hz.2)

end GlobalTheory.CompanionTheory.EisHolFam

end
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.schwartz_height_majorant_integrable : ∀ (D : D7) (n ρ p : ℕ) (hn : ρ + p = n) (M : Maps D hn) (m : Meas D ρ p) (θ : InfFam D), IsInfFam θ →
  ∀ H : G D n → ℝ≥0, IsHt H → (∃ C : Set (G D n), IsCompact C ∧ ∀ g, ∃ q ∈ P D n, ∃ c ∈ C, g = q * c) →
  ∀ Φ ∈ schwartzA θ ρ p, ∀ τ : ℝ, 0 ≤ τ → ∃ W : Mx D ρ p → ℝ, Integrable W m.μ ∧
    ∀ (x : G D n) (y : Mx D ρ p), (H (x * M.sh y) : ℝ) ^ τ * ‖Φ y‖ ≤ W y * (H x : ℝ) ^ τ := by
  first | exact @GlobalTheory.CompanionTheory.ShearGrowth.height_shear_majorant | exact GlobalTheory.CompanionTheory.ShearGrowth.height_shear_majorant | (intros; apply GlobalTheory.CompanionTheory.ShearGrowth.height_shear_majorant <;> assumption)
end

section

open PositivityTheory.Rg.Rsw

theorem _root_.GlobalTheory.T.theta_twist_identity : ThTwist := by
  first | exact @GlobalTheory.CompanionTheory.ThTw.thTwist | exact GlobalTheory.CompanionTheory.ThTw.thTwist | (intros; apply GlobalTheory.CompanionTheory.ThTw.thTwist <;> assumption)
end
