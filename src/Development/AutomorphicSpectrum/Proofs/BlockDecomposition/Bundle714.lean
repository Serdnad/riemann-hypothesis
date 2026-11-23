module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle040
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsBlockMatrixTwoByTwoFinEq
public import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle015
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.GlintPrincRelIndexNeZero
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle502
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierZeroHolds
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle602
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FockTranslateSchwartzMajorant
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle710
import Formalism.LocalRingCardinality.DataHost
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle705
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle712
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle713
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle711
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle543
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle614
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2130
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle002
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivativeCuspidalPairLength
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CanonicalProductEquivMultiplicityOne
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle012
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle001
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.ThetaOrbits
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs

@[expose] public section

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.tamagawa_fourier_integrable : ∀ (F : Type) [Field F] [NumberField F], NumberField.IsTotallyReal F → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ (κ : Type) [Fintype κ] [MeasurableSpace (κ → AF F)] [BorelSpace (κ → AF F)] (μ : Measure (κ → AF F)), GlobalTheory.SWLit.IsTamagawa F κ μ → ∀ (Y : Type) [MeasurableSpace Y] (ν : Measure Y) [SFinite ν] (φ : Y → ℂ) (g : Y → κ → AF F), Integrable φ ν → Measurable g → Integrable (fun v : κ → AF F => ∫ y, φ y * ψ (v ⬝ᵥ g y) ∂ν) μ → ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, (∀ y, Φ (g y) = 0) → ∫ z, (∫ v, (∫ y, φ y * ψ (v ⬝ᵥ g y) ∂ν) * ψ (-(v ⬝ᵥ z)) ∂μ) * Φ z ∂μ = 0 := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.pair_vanish | exact GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.pair_vanish | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.pair_vanish <;> assumption)
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

abbrev Ov (D : D7) (v : Pl D) : Type := v.adicCompletionIntegers D.host.F

abbrev Lv (D : D7) (v : Pl D) : Type := Fv D.host.F v

abbrev kv (D : D7) (v : Pl D) : Type := IsLocalRing.ResidueField (Ov D v)

instance kvFintype (D : D7) (v : Pl D) : Fintype (kv D v) :=
  @Fintype.ofFinite _ (Formalism.UG.P.glint_finite_residueField v)

def blkGL {R : Type} [CommRing R] (n : ℕ) : GL (Fin (n + n)) R →* GL (Ix n) R :=
  Units.map (Matrix.reindexAlgEquiv R R (finSumFinEquiv (m := n) (n := n)).symm).toAlgHom.toMonoidHom

def thU (D : D7) (n : ℕ) (v : Pl D) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) :
    GLoc D.sp.cm.sig (Jst D n) v →* GL (Ix n) (Fv D.host.F v) :=
  (blkGL n).comp (splitHom D.sp.cm.sig (Jst D n) τ)

def tauC {D : D7} {n : ℕ} {v : Pl D} (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (x : Mx D n n) :
    Matrix (Fin n) (Fin n) (Fv D.host.F v) := fun i j => splitProj τ (cv D v (x i j))

def hU (D : D7) (n : ℕ) (v : Pl D) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (g : GL (Ix n) (Fv D.host.F v)) : ℝ≥0 :=
  GlobalTheory.LocIntw.hgtUp _ D.sp.cm.sig (Jst D n) (absEv D.host.F D.host.E v) (GlobalTheory.LocIntw.KUpFin D.sp.cm.sig (Jst D n) v)
    (Function.invFun (thU D n v τ) g)

def nvL (D : D7) (v : Pl D) : (Fv D.host.F v)ˣ →* ℝ≥0 :=
  (nnnormHom : Fv D.host.F v →*₀ ℝ≥0).toMonoidHom.comp (Units.coeHom _)

end GlobalTheory.CompanionTheory.Jp

end
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg

theorem _root_.GlobalTheory.T.derivative_cuspidal_pair_length : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {p q N c : ℕ} (u v : IrrGL (k := k)) (s : Fin p → IrrGL (k := k)) (t : Fin q → IrrGL (k := k)) (hs : ∑ i, (s i).1 = u.1) (ht : ∑ i, (t i).1 = v.1) (d : ℕ) (hsd : ∀ i, (s i).1 = d) (htd : ∀ j, (t j).1 = d) (hsc : ∀ i, (s i).IsCusp) (htc : ∀ i, (t i).IsCusp) (hu : Nonempty ((_root_.GlobalTheory.SmGL.jac (stdBlocks (fun i => (s i).1) hs) u.rep).Equiv (piTensor fun i => (s i).rep))) (hv : Nonempty ((_root_.GlobalTheory.SmGL.jac (stdBlocks (fun i => (t i).1) ht) v.rep).Equiv (piTensor fun i => (t i).rep))) (hd : ∑ i, (![u, v] i).1 = N) (y : Fin c → IrrGL (k := k)) (hy : ∑ i, (y i).1 = N) (hyc : ∀ i, (y i).IsCusp) (h : 1 ≤ jm y hy (prodIrr ![u, v] hd)), ∃ (f : Fin p ↪o Fin c) (g : Fin q ↪o Fin c), Disjoint (Set.range f) (Set.range g) ∧ (∀ i, y (f i) = s i) ∧ ∀ j, y (g j) = t j := by
  first | exact @GlobalTheory.CompanionTheory.Shuffle2.shuffle2 | exact GlobalTheory.CompanionTheory.Shuffle2.shuffle2 | (intros; apply GlobalTheory.CompanionTheory.Shuffle2.shuffle2 <;> assumption)
end

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.FJE

theorem Wz_sh_nzx : ∀ {D : D7} {n ρ p : ℕ} {hn : ρ + p = n} (M : Maps D hn) (m : Meas D ρ p)
    (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ (b₀ : HermE D ρ) (χ : (AE D)ˣ →* Circle) (s : ℂ)
    (f : G D n → ℂ), IsLaw χ s f → ∀ (η : Mx D ρ p) (z : hermA D ρ) (x : Mx D ρ p) (h : G D n),
    Wz M m ψ b₀ f (M.sh η * (M.nzx z x * h)) =
      chz ψ b₀ z * GlobalTheory.CompanionTheory.FJE.chv ψ b₀ x η * Wz M m ψ b₀ f (M.sh η * h) := by
  intro D n ρ p hn M m ψ hψ b₀ χ s f hf η z x h
  obtain ⟨hadd, hnorm, -, -⟩ := GlobalTheory.T.centre_character_properties ψ hψ b₀
  have hjc := GlobalTheory.T.centre_character_commutator ψ b₀ η x
  have hsh := GlobalTheory.T.shift_conj_heisenberg M η z x
  have hmul := GlobalTheory.T.unipotent_heisenberg_mul M
  have hw := GlobalTheory.T.section_invariant_heisenberg_weyl M χ s f hf
  have e1 : M.sh η * (M.nzx z x * h) = M.nzx (z + jc η x) x * (M.sh η * h) := by
    rw [← mul_assoc, hsh, mul_assoc]
  rw [e1]
  generalize M.sh η * h = h'
  have hc : chz ψ b₀ z * chv ψ b₀ x η = chz ψ b₀ (z + jc η x) := by rw [hadd, hjc]
  rw [hc]
  generalize z + jc η x = c
  have hcc : chz ψ b₀ c * conj (chz ψ b₀ c) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hnorm c]
    simp
  have hconj : ∀ t, conj (chz ψ b₀ t) = conj (chz ψ b₀ (t + c)) * chz ψ b₀ c := by
    intro t
    have hh : conj (chz ψ b₀ (t + c)) * chz ψ b₀ c = conj (chz ψ b₀ t) * (chz ψ b₀ c * conj (chz ψ b₀ c)) := by
      rw [hadd, map_mul]; ring
    rw [hh, hcc, mul_one]
  have hpt : ∀ t : hermA D ρ, f (M.w * M.nzx t 0 * (M.nzx c x * h')) =
      f (M.w * M.nzx (t + c) 0 * h') := by
    intro t
    have e2 : M.w * M.nzx t 0 * (M.nzx c x * h') = M.w * M.nzx 0 x * (M.nzx (t + c) 0 * h') := by
      have a1 : M.nzx t 0 * M.nzx c x = M.nzx 0 x * M.nzx (t + c) 0 := by
        rw [hmul, hmul]; simp
      calc M.w * M.nzx t 0 * (M.nzx c x * h') = M.w * (M.nzx t 0 * M.nzx c x) * h' := by
            simp only [mul_assoc]
        _ = M.w * M.nzx 0 x * (M.nzx (t + c) 0 * h') := by
            rw [a1]; simp only [mul_assoc]
    rw [e2, hw, mul_assoc]
  haveI := m.hz.1
  haveI : ContinuousAdd (hermA D ρ) := ⟨Continuous.subtype_mk ((continuous_subtype_val.comp continuous_fst).add
    (continuous_subtype_val.comp continuous_snd)) _⟩
  haveI : BorelSpace (Mx D ρ ρ) := ⟨rfl⟩
  haveI : BorelSpace (hermA D ρ) := Subtype.borelSpace _
  haveI : MeasurableAdd (hermA D ρ) := ContinuousAdd.measurableAdd
  unfold Wz
  calc ∫ t, f (M.w * M.nzx t 0 * (M.nzx c x * h')) * conj (chz ψ b₀ t) ∂m.lz
      = ∫ t, (fun u => f (M.w * M.nzx u 0 * h') * (conj (chz ψ b₀ u) * chz ψ b₀ c)) (t + c) ∂m.lz := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
        show f (M.w * M.nzx t 0 * (M.nzx c x * h')) * conj (chz ψ b₀ t) = f (M.w * M.nzx (t + c) 0 * h') * (conj (chz ψ b₀ (t + c)) * chz ψ b₀ c)
        rw [hpt, ← hconj]
    _ = ∫ u, f (M.w * M.nzx u 0 * h') * (conj (chz ψ b₀ u) * chz ψ b₀ c) ∂m.lz :=
        integral_add_right_eq_self (μ := m.lz)
          (fun u => f (M.w * M.nzx u 0 * h') * (conj (chz ψ b₀ u) * chz ψ b₀ c)) c
    _ = chz ψ b₀ c * ∫ u, f (M.w * M.nzx u 0 * h') * conj (chz ψ b₀ u) ∂m.lz := by
        rw [← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
        show _ = _
        ring

end GlobalTheory.CompanionTheory.FJE
end
end

section

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn GlobalTheory.StdUnn.Model PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.PcFc

variable {D : D7} {n ρ p : ℕ}

theorem conj_psi {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (t : AF D.host.F) : conj (ψ t) = ψ (-t) := by
  rw [AddChar.map_neg_eq_inv, Complex.inv_eq_conj (hψ.2.1 t)]

theorem chn_eq (ψ : AddChar (AF D.host.F) ℂ) (β : HermE D n) (b : hermA D n) :
    chn ψ β b = ψ (-GlobalTheory.CompanionTheory.FourierN.pr β.1 b.1) := rfl

theorem chn_cont {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (β : HermE D n) : Continuous (chn ψ β) :=
  hψ.1.comp ((GlobalTheory.CompanionTheory.FourierN.continuous_pr β.1).neg.comp continuous_subtype_val)

theorem chn_per {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (β : HermE D n) : IsPer (chn ψ β) := fun γ hγ x => by
  rw [chn_eq, chn_eq, show (γ + x).1 = γ.1 + x.1 from rfl, GlobalTheory.CompanionTheory.FourierN.pr_add_right, neg_add, AddChar.map_add_eq_mul,
    GlobalTheory.CompanionTheory.FourierN.ker_of_rat hψ γ hγ, one_mul]

theorem trace_bl_mul {R : Type} [CommRing R] (hn : ρ + p = n) (a z : Matrix (Fin ρ) (Fin ρ) R) (d y : Matrix (Fin p) (Fin p) R)
    (x : Matrix (Fin ρ) (Fin p) R) (c : Matrix (Fin p) (Fin ρ) R) :
    Matrix.trace (bl hn a 0 0 d * bl hn z x c y) = Matrix.trace (a * z) + Matrix.trace (d * y) := by
  unfold bl
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  have h : ∀ M : Matrix (Fin ρ ⊕ Fin p) (Fin ρ ⊕ Fin p) R,
      Matrix.trace (M.submatrix (finSumFinEquiv.trans (finCongr hn)).symm (finSumFinEquiv.trans (finCongr hn)).symm) = Matrix.trace M :=
    fun M => Equiv.sum_comp (finSumFinEquiv.trans (finCongr hn)).symm (fun j => M j j)
  rw [h]
  simp [Matrix.trace, Fintype.sum_sum_type]

theorem map_dsum (hn : ρ + p = n) (b₀ : HermE D ρ) (β' : HermE D p) :
    (dsum hn b₀ β').1.map (incA D) = bl hn (b₀.1.map (incA D)) 0 0 (β'.1.map (incA D)) := by
  refine Matrix.ext fun i j => ?_
  simp only [dsum, bl, Matrix.map_apply, Matrix.submatrix_apply]
  rcases (finSumFinEquiv.trans (finCongr hn)).symm i with i' | i' <;>
    rcases (finSumFinEquiv.trans (finCongr hn)).symm j with j' | j' <;> simp

theorem pr_split (hn : ρ + p = n) (b₀ : HermE D ρ) (β' : HermE D p) (z : hermA D ρ) (x : Mx D ρ p) (y : hermA D p) :
    GlobalTheory.CompanionTheory.FourierN.pr (dsum hn b₀ β').1 (bT hn z x y).1 = GlobalTheory.CompanionTheory.FourierN.pr b₀.1 z.1 + GlobalTheory.CompanionTheory.FourierN.pr β'.1 y.1 := by
  simp only [GlobalTheory.CompanionTheory.FourierN.pr, ← GlobalTheory.CompanionTheory.FourierN.halfTr_add]
  congr 1
  rw [map_dsum]
  exact trace_bl_mul hn _ _ _ _ _ _

theorem chn_split {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (hn : ρ + p = n) (b₀ : HermE D ρ) (β' : HermE D p)
    (z : hermA D ρ) (x : Mx D ρ p) (y : hermA D p) :
    chn ψ (dsum hn b₀ β') (bT hn z x y) = conj (chz ψ b₀ z) * chn ψ β' y := by
  rw [chn_eq, pr_split, neg_add, AddChar.map_add_eq_mul, chn_eq]
  congr 1
  exact (conj_psi hψ _).symm

theorem coef_pm (hn : ρ + p = n) (m : Meas D ρ p) {lam : Measure (hermA D n)} {𝓖 : Set (hermA D n)} (h : IsCovolOneH lam 𝓖)
    {lp : Measure (hermA D p)} {𝓖p : Set (hermA D p)} (hp : IsCovolOneH lp 𝓖p) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ)
    (b₀ : HermE D ρ) (β' : HermE D p) (Φ : hermA D n → ℂ) (hc : Continuous Φ) (hper : IsPer Φ) :
    ∫ b in 𝓖, Φ b * chn ψ (dsum hn b₀ β') b ∂lam = ∫ y in 𝓖p, pm hn m ψ b₀ Φ y * chn ψ β' y ∂lp := by
  have hd := GlobalTheory.T.hermitian_integral_block_fubini hn m h hp (fun b => Φ b * chn ψ (dsum hn b₀ β') b) (hc.mul (chn_cont hψ _))
    (fun γ hγ x => by
      show Φ (γ + x) * chn ψ (dsum hn b₀ β') (γ + x) = _
      rw [hper γ hγ x, chn_per hψ _ γ hγ x])
  rw [hd]
  refine integral_congr_ae (.of_forall fun y => ?_)
  show ∫ x in m.𝓕, ∫ z in m.𝓖, Φ (bT hn z x y) * chn ψ (dsum hn b₀ β') (bT hn z x y) ∂m.lz ∂m.μ = pm hn m ψ b₀ Φ y * chn ψ β' y
  simp only [chn_split hψ, ← mul_assoc]
  simp only [integral_mul_const, pm]

end GlobalTheory.CompanionTheory.PcFc

namespace GlobalTheory.CompanionTheory.PcFc

theorem per_nb {D : D7} {n : ℕ} {F : G D n → ℂ} (hinv : LeftInv (GF D n) F) {nb : hermA D n → G D n} (hnb : IsNMap nb) (g : G D n) :
    IsPer (fun b => F (nb b * g)) := fun γ hγ x => by
  show F (nb (γ + x) * g) = F (nb x * g)
  rw [GlobalTheory.CompanionTheory.FourierN.nb_add hnb, mul_assoc]
  exact hinv _ (GlobalTheory.CompanionTheory.FourierN.nb_rat hnb γ hγ) _

theorem cont_nb {D : D7} {n : ℕ} {F : G D n → ℂ} (hF : Continuous F) {nb : hermA D n → G D n} (hnb : IsNMap nb) (g : G D n) :
    Continuous (fun b => F (nb b * g)) :=
  hF.comp ((GlobalTheory.CompanionTheory.FourierN.continuous_nb hnb).mul continuous_const)

def zH (D : D7) (p : ℕ) : HermE D p := ⟨0, by
  rw [Matrix.map_zero _ (map_zero _), Matrix.transpose_zero]⟩

theorem chn_zero {D : D7} {p : ℕ} (ψ : AddChar (AF D.host.F) ℂ) (y : hermA D p) : chn ψ (zH D p) y = 1 := by
  have h := GlobalTheory.CompanionTheory.FourierN.pr_zero_left (D := D) (n := p) y.1
  simp only [GlobalTheory.CompanionTheory.FourierN.pr] at h
  simp only [chn, zH, h, neg_zero, AddChar.map_zero_eq_one]

theorem pcFc : PcFc := by
  intro D n ρ p hn M m ψ hψ F hF hinv
  obtain ⟨lp, 𝓖p, hp⟩ := GlobalTheory.CompanionTheory.HermVol.exists_isCovolOneH D p
  refine ⟨?_, ?_⟩
  · intro h nb lam 𝓖 hC β hr g
    obtain ⟨a, b₀, β', hd, he⟩ := GlobalTheory.T.hermitian_block_diagonal_normal_form hn β hr
    obtain ⟨q, hq⟩ := GlobalTheory.T.fourier_coefficient_conjugation hψ F hF hinv hC a β
    have h1 := hq (q⁻¹ * g)
    rw [mul_inv_cancel_left] at h1
    rw [h1, he]
    have h2 := coef_pm hn m hC.2 hp hψ b₀ β' _ (cont_nb hF hC.1 (q⁻¹ * g)) (per_nb hinv hC.1 (q⁻¹ * g))
    refine h2.trans ?_
    refine setIntegral_eq_zero_of_forall_eq_zero fun y _ => ?_
    rw [← GlobalTheory.T.partial_coefficient_unipotent_mean M m ψ b₀ F hC.1, h b₀ hd, zero_mul]
  · intro hR b₀ hb β hβ nb lam 𝓖 hC g
    have hc := cont_nb hF hC.1 g
    have hpr := per_nb hinv hC.1 g
    have key := GlobalTheory.T.eq_const_of_fourier_coefficients_zero hp hψ (pm hn m ψ b₀ (fun b => F (nb b * g))) (GlobalTheory.T.continuous_partial_fourier_mean hn m hψ b₀ _ hc hpr)
      (GlobalTheory.T.periodic_partial_fourier_mean hn m ψ b₀ _ hpr)
      (fun a ha => by
        rw [← coef_pm hn m hC.2 hp hψ b₀ a _ hc hpr]
        exact hR nb lam 𝓖 hC _ (GlobalTheory.T.rank_direct_sum_hermitian_lt hn b₀ hb a ha) g)
    have e0 : β = dsum hn b₀ (zH D p) := Subtype.ext hβ
    have e1 : fc ψ lam 𝓖 nb F β g = ∫ y in 𝓖p, pm hn m ψ b₀ (fun b => F (nb b * g)) y * chn ψ (zH D p) y ∂lp := by
      rw [e0]
      exact coef_pm hn m hC.2 hp hψ b₀ _ _ hc hpr
    have e2 : pc M m ψ b₀ F g = pm hn m ψ b₀ (fun b => F (nb b * g)) 0 := by
      have := GlobalTheory.T.partial_coefficient_unipotent_mean M m ψ b₀ F hC.1 g 0
      have hz : bT hn (0 : hermA D ρ) 0 (0 : hermA D p) = 0 := by
        apply Subtype.ext
        show (bl hn (0 : Mx D ρ ρ) 0 (adj (0 : Mx D ρ p)) 0 : Mx D n n) = 0
        rw [adj_zero, bl, Matrix.fromBlocks_zero]
        rfl
      rw [hz, GlobalTheory.CompanionTheory.FourierN.nb_zero hC.1, one_mul] at this
      exact this
    rw [e1, e2]
    simp only [chn_zero, mul_one]
    rw [show (fun y => pm hn m ψ b₀ (fun b => F (nb b * g)) y) = fun _ => pm hn m ψ b₀ (fun b => F (nb b * g)) 0 from funext key]
    rw [setIntegral_const, measureReal_def, hp.2.2]
    simp

theorem target : MapsExist → PositivityTheory.PfSWUS.FourierZero → PcFc := fun _ _ => pcFc

end GlobalTheory.CompanionTheory.PcFc
end
end

section

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
namespace GlobalTheory.CompanionTheory.IwaAd
open GlobalTheory.StdUnn GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.LeftInvSect PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
variable {D : D7} {n : ℕ}
theorem integral_mul_right (m : ℕ) (μ : Measure (Mx D m n)) (hμ : μ.IsAddHaarMeasure) (a : GL (Fin n) (AE D))
    (f : Mx D m n → ℂ) :
    ∫ y, f (HMul.hMul y a.1 : Mx D m n) ∂μ = npow (absA D (Matrix.GeneralLinearGroup.det a)) (-(m : ℂ)) * ∫ y, f y ∂μ := by
  obtain ⟨i1, i2, i3, i4, -, -⟩ := lattice_Mx D m n
  haveI : IsTopologicalAddGroup (Mx D m n) := i1
  haveI : LocallyCompactSpace (Mx D m n) := i2
  haveI : SecondCountableTopology (Mx D m n) := i3
  haveI : T2Space (Mx D m n) := i4
  haveI : BorelSpace (Mx D m n) := ⟨rfl⟩
  haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  let φ := GlobalTheory.ModuLR.lrCE (1 : GL (Fin m) (AE D)) a
  have hc : addEquivAddHaarChar φ = absA D (Matrix.GeneralLinearGroup.det a) ^ m := by
    have := GlobalTheory.ResidueEisenstein.ModMat.addEquivAddHaarChar_lrCE D.host.F D.host.E D.sp.cm.sig (isCMExt_host D) m n
      (1 : GL (Fin m) (AE D)) a
    simpa using this
  have hA : 0 < absA D (Matrix.GeneralLinearGroup.det a) := absA_pos _
  have e : ∀ y : Mx D m n, (HMul.hMul y a.1 : Mx D m n) = φ y := fun y => by
    simp only [φ]
    rw [GlobalTheory.ModuLR.lrCE_apply, Units.val_one, Matrix.one_mul]
  have key : ∫ y, f (φ y) ∂μ = ((((addEquivAddHaarChar φ)⁻¹ : ℝ≥0) : ℝ) : ℂ) * ∫ y, f y ∂μ :=
    integral_comp_char μ φ f
  rw [hc, npow_neg_nat hA] at key
  simp only [e]
  exact key

theorem integral_shift {A : Type} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
    [MeasurableSpace A] [BorelSpace A] (μ : Measure A) [μ.IsAddHaarMeasure] (f : A → ℂ) (g : A) :
    ∫ x, f (x - g) ∂μ = ∫ x, f x ∂μ :=
  integral_sub_right_eq_self f g

theorem integral_shift_herm (lam : Measure (hermA D n)) (hl : lam.IsAddHaarMeasure) (f : hermA D n → ℂ) (g : hermA D n) :
    ∫ x, f (x - g) ∂lam = ∫ x, f x ∂lam := by
  obtain ⟨i1, -, -, -, -, -⟩ := lattice_Mx D n n
  haveI : IsTopologicalAddGroup (Mx D n n) := i1
  haveI : BorelSpace (Mx D n n) := ⟨rfl⟩
  exact integral_shift lam f g

theorem halfTr_add (x y : AE D) : halfTr (x + y) = halfTr x + halfTr y := by
  simp [halfTr, mul_add]

theorem halfTr_neg (x : AE D) : halfTr (-x) = -halfTr x := by
  simp [halfTr]

theorem inner_mul_right (V : HSp D) {r : ℕ} (x : Mx D V.rank r) (s : Mx D r r) :
    StdUnn.inner V (HMul.hMul x s : Mx D V.rank r) (HMul.hMul x s : Mx D V.rank r) =
      adj s * StdUnn.inner V x x * s := by
  unfold StdUnn.inner
  rw [adj_mul]
  simp only [Matrix.mul_assoc]

theorem trace_cg (a : GL (Fin n) (AE D)) (c Q : Mx D n n) :
    Matrix.trace (a.1 * c * adj a.1 * (adj (a⁻¹).1 * Q * (a⁻¹).1)) = Matrix.trace (c * Q) := by
  have h1 : a.1 * c * adj a.1 * (adj (a⁻¹).1 * Q * (a⁻¹).1) = a.1 * (c * Q * (a⁻¹).1) := by
    calc _ = a.1 * c * (adj a.1 * adj (a⁻¹).1) * Q * (a⁻¹).1 := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [adj_mul_adj_inv]; simp only [Matrix.mul_assoc, Matrix.mul_one]
  rw [h1, Matrix.trace_mul_comm, Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]

theorem trace_beta (a : GL (Fin n) (AE D)) (B c : Mx D n n) :
    Matrix.trace (B * (a.1 * c * adj a.1)) = Matrix.trace (adj a.1 * B * a.1 * c) := by
  rw [← Matrix.mul_assoc, Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

theorem weil_pt {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle} {θ : InfFam D} {V : HSp D}
    {μ : Measure (Mx D V.rank n)} {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)} (hω : IsWeilSch ψ χ θ V μ ω)
    (a : GL (Fin n) (AE D)) {m u : G D n} (hm : mat m = blk4 a.1 0 0 (adj (a⁻¹).1)) {b1 : Mx D n n}
    (hu : mat u = blk4 1 b1 0 1) (φ : schwartzA θ V.rank n) (y : Mx D V.rank n) :
    (ω (m * u) φ).1 y = (χ (Matrix.GeneralLinearGroup.det a) : ℂ) *
      npow (absA D (Matrix.GeneralLinearGroup.det a)) ((V.rank : ℂ) / 2) *
      (ψ (halfTr (Matrix.trace (b1 * StdUnn.inner V (HMul.hMul y a.1 : Mx D V.rank n) (HMul.hMul y a.1 : Mx D V.rank n)))) *
        φ.1 (HMul.hMul y a.1 : Mx D V.rank n)) := by
  rw [map_mul, Module.End.mul_apply, hω.levi m a hm, hω.unip u b1 hu]

theorem jt_step {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle} {θ : InfFam D} {V : HSp D}
    {μ : Measure (Mx D V.rank n)} {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)} (hω : IsWeilSch ψ χ θ V μ ω)
    (hμ : μ.IsAddHaarMeasure) (a : GL (Fin n) (AE D)) {m u : G D n} (hm : mat m = blk4 a.1 0 0 (adj (a⁻¹).1))
    {b1 : hermA D n} (hu : mat u = blk4 1 b1.1 0 1) (φ : schwartzA θ V.rank n) (c : hermA D n) :
    Jt ψ V μ (ω (m * u) φ).1 (cg a c) = (χ (Matrix.GeneralLinearGroup.det a) : ℂ) *
      npow (absA D (Matrix.GeneralLinearGroup.det a)) ((V.rank : ℂ) / 2) *
      (npow (absA D (Matrix.GeneralLinearGroup.det a)) (-(V.rank : ℂ)) * Jt ψ V μ φ.1 (c + b1)) := by
  set F : Mx D V.rank n → ℂ := fun y => φ.1 y * ψ (halfTr (Matrix.trace (HMul.hMul (c + b1).1 (StdUnn.inner V y y) : Mx D n n))) with hF
  have hpt : ∀ y : Mx D V.rank n, (ω (m * u) φ).1 y *
      ψ (halfTr (Matrix.trace (HMul.hMul (cg a c).1 (StdUnn.inner V y y) : Mx D n n))) =
      ((χ (Matrix.GeneralLinearGroup.det a) : ℂ) * npow (absA D (Matrix.GeneralLinearGroup.det a)) ((V.rank : ℂ) / 2)) *
        F (HMul.hMul y a.1 : Mx D V.rank n) := by
    intro y
    have hy : y = (HMul.hMul (HMul.hMul y a.1 : Mx D V.rank n) (a⁻¹).1 : Mx D V.rank n) := by
      rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
    set Y : Mx D V.rank n := HMul.hMul y a.1 with hY
    have e1 : Matrix.trace (HMul.hMul (cg a c).1 (StdUnn.inner V y y) : Mx D n n) =
        Matrix.trace (c.1 * StdUnn.inner V Y Y) := by
      rw [hy, inner_mul_right]
      exact trace_cg a c.1 _
    rw [weil_pt hω a hm hu, e1]
    simp only [hF]
    have e2 : Matrix.trace (HMul.hMul (c + b1).1 (StdUnn.inner V Y Y) : Mx D n n) =
        Matrix.trace (c.1 * StdUnn.inner V Y Y) + Matrix.trace (b1.1 * StdUnn.inner V Y Y) := by
      rw [← Matrix.trace_add, ← Matrix.add_mul]
      rfl
    rw [e2, halfTr_add, AddChar.map_add_eq_mul]
    ring
  unfold Jt
  simp only [hpt]
  rw [integral_const_mul, integral_mul_right V.rank μ hμ a F]

end GlobalTheory.CompanionTheory.IwaAd
end
end

section

open GlobalTheory.CompanionTheory.ThTot

theorem _root_.GlobalTheory.T.iwasawa_compactness : IwaCpt := by
  first | exact @GlobalTheory.CompanionTheory.ThTot.iwaCpt | exact GlobalTheory.CompanionTheory.ThTot.iwaCpt | (intros; apply GlobalTheory.CompanionTheory.ThTot.iwaCpt <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos

theorem _root_.GlobalTheory.T.canonical_product_equiv_multiplicity_one : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → LSegJacquet k → LUnlinkedIrr k → ∀ {h N : ℕ} (Γ : Fin h → Segment k) (y : Fin h → IrrGL (k := k)) (hd : ∑ a, (y a).1 = N), IsCanon Γ → (∀ i, IsLSeg (Γ i) (y i).rep) → ∃ (g : ℕ) (z : Fin g → IrrGL (k := k)) (hz : ∑ b, (z b).1 = N), Nonempty ((prodIrr y hd).Equiv (prodIrr z hz)) ∧ jm z hz (prodIrr z hz) ≤ 1 := by
  first | exact @GlobalTheory.CompanionTheory.GroupCount.groupCount | exact GlobalTheory.CompanionTheory.GroupCount.groupCount | (intros; apply GlobalTheory.CompanionTheory.GroupCount.groupCount <;> assumption)
end
