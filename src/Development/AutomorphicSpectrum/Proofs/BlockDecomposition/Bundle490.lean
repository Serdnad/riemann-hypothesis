module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle431
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle459
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle432
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.EisCellsDefs
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.MapsExist
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.HeisSch
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle461
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle449
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.CreationOperators.Bundle001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle465
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MixedPointLengthFormula
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Tactic.Basify
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
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.CoefDataExists
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle001
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle039
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS GlobalTheory.Eis GlobalTheory.CompanionTheory.SwUnf

theorem _root_.GlobalTheory.T.coset_cell_invariant_unipotent : ∀ {D : D7} {n : ℕ} (q : Cosets (P D n) (GF D n)) (γ : GF D n) (b : Matrix (Fin n) (Fin n) D.host.E), mat (γ : G D n) = blk4 1 (b.map (incA D)) 0 1 → cosetCell (rmulEquiv (P D n) (GF D n) γ q) = cosetCell q := by
  first | exact @GlobalTheory.CompanionTheory.SwUnf.cosetCell_rmulEquiv | exact GlobalTheory.CompanionTheory.SwUnf.cosetCell_rmulEquiv | (intros; apply GlobalTheory.CompanionTheory.SwUnf.cosetCell_rmulEquiv <;> assumption)
end
end

section

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS GlobalTheory.Eis GlobalTheory.CompanionTheory.SwUnf
open PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.LeftInvSect GlobalTheory.CompanionTheory.Hypotheses₂.WeilU
open PositivityTheory.Rg.Rsw

namespace GlobalTheory.CompanionTheory.ZUnf

section Rows

variable {K : Type} [Field K] {n ρ p : ℕ}

def zinc (hn : ρ + p = n) : (Fin ρ → K) →ₗ[K] (Fin n → K) where
  toFun u i := Sum.elim u (fun _ : Fin p => (0 : K)) ((finSumFinEquiv.trans (finCongr hn)).symm i)
  map_add' u v := by
    funext i
    simp only [Pi.add_apply]
    generalize (finSumFinEquiv.trans (finCongr hn)).symm i = j
    rcases j with j | j <;> simp
  map_smul' c u := by
    funext i
    simp only [Pi.smul_apply, RingHom.id_apply]
    generalize (finSumFinEquiv.trans (finCongr hn)).symm i = j
    rcases j with j | j <;> simp

def wM (hn : ρ + p = n) : Matrix (Fin (n + n)) (Fin (n + n)) K :=
  blk4 (bl hn 0 0 0 1) (bl hn 1 0 0 0) (bl hn (-1) 0 0 0) (bl hn 0 0 0 1)

def nM (hn : ρ + p = n) (ζ : Matrix (Fin ρ) (Fin ρ) K) : Matrix (Fin (n + n)) (Fin (n + n)) K :=
  blk4 1 (bl hn ζ 0 0 0) 0 1

def sM (hn : ρ + p = n) (σ : K →+* K) (η : Matrix (Fin ρ) (Fin p) K) : Matrix (Fin (n + n)) (Fin (n + n)) K :=
  blk4 (bl hn 1 η 0 1) 0 0 (bl hn 1 0 (-cT σ η) 1)

def eM (hn : ρ + p = n) (a b c d : Matrix (Fin p) (Fin p) K) : Matrix (Fin (n + n)) (Fin (n + n)) K :=
  blk4 (bl hn 1 0 0 a) (bl hn 0 0 0 b) (bl hn 0 0 0 c) (bl hn 1 0 0 d)

def rowC (hn : ρ + p = n) (η : Matrix (Fin ρ) (Fin p) K) (a c : Matrix (Fin p) (Fin p) K) : Matrix (Fin n) (Fin n) K :=
  bl hn (-1) (-(η * a)) 0 c

def rowD (hn : ρ + p = n) (σ : K →+* K) (ζ : Matrix (Fin ρ) (Fin ρ) K) (η : Matrix (Fin ρ) (Fin p) K)
    (b d : Matrix (Fin p) (Fin p) K) : Matrix (Fin n) (Fin n) K :=
  bl hn (-ζ) (-(η * b)) (-cT σ η) d

end Rows

variable {D : D7} {n ρ p : ℕ}

def zKer (hn : ρ + p = n) (x : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E) : Submodule D.host.E (Fin ρ → D.host.E) :=
  (cellKer x).comap (zinc hn)

end GlobalTheory.CompanionTheory.ZUnf
end
end

section

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.CompanionTheory.EisUnfold
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.eisenstein_hermitian_integral_unfolding : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V : HSp D) (r s : ℕ) (μr : Measure (Mx D V.rank r))
    (𝓕r : Set (Mx D V.rank r)), IsCovolOne (ratMx D V.rank r) μr 𝓕r →
    ∀ (c : Matrix (Fin r) (Fin (r + s)) D.host.E) (a : Matrix (Fin (r + s)) (Fin (r + s)) D.host.E), IsCompl c a →
    ∀ (b : HermE D r) (Φ : Mx D V.rank (r + s) → ℂ),
      ∫ t, ψ (halfTr (Matrix.trace (HMul.hMul (rat b.1) (inner V t t) : Mx D r r))) *
          Φ (HMul.hMul (colJoin (-t) (0 : Mx D V.rank s)) (rat a)) ∂μr = J ψ V μr (pull c Φ) b := by
  first | exact @GlobalTheory.CompanionTheory.EisUnfold.NegStep.integral_colJoin_neg_eq_J | exact GlobalTheory.CompanionTheory.EisUnfold.NegStep.integral_colJoin_neg_eq_J | (intros; apply GlobalTheory.CompanionTheory.EisUnfold.NegStep.integral_colJoin_neg_eq_J <;> assumption)
end
end

section

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.CompanionTheory.EisUnfold
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.block_weil_action_theta_unfolding : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ (V : HSp D) (r s : ℕ)
    (b : Matrix (Fin r) (Fin r) D.host.E), (b.map (D.sp.cm.sig : D.host.E → D.host.E)).transpose = b →
    ∀ (a : Matrix (Fin (r + s)) (Fin (r + s)) D.host.E), IsUnit a.det →
    ∀ (Φ : Mx D V.rank (r + s) → ℂ) (y₁ : Mx D V.rank r) (y₂ : Mx D V.rank s) (v : Mx D V.rank ((r + s) + (r + s))),
    xPart v = -HMul.hMul (colJoin y₁ (0 : Mx D V.rank s)) (rat a) →
    yPart v = HMul.hMul (colJoin (-HMul.hMul y₁ (rat b)) y₂) (rat (cT (D.sp.cm.sig : D.host.E →+* D.host.E) a)⁻¹) →
    ∀ (p : Matrix (Fin V.rank) (Fin r) D.host.E) (q : Matrix (Fin V.rank) (Fin s) D.host.E),
      Heisenberg₂ ψ V v Φ (rat (colJoin p q * a)) = cellTerm ψ V b a Φ p q y₁ y₂ := by
  first | exact @GlobalTheory.CompanionTheory.EisUnfold.Summand.summand | exact GlobalTheory.CompanionTheory.EisUnfold.Summand.summand | (intros; apply GlobalTheory.CompanionTheory.EisUnfold.Summand.summand <;> assumption)
end
end

section

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.CompanionTheory.EisUnfold
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.weil_action_block_matrix_components : ∀ (D : D7) (m r s : ℕ) (b : Matrix (Fin r) (Fin r) D.host.E) (a : Matrix (Fin (r + s)) (Fin (r + s)) D.host.E)
    (y₁ : Mx D m r) (y₂ : Mx D m s),
    xPart (HMul.hMul (zy (colJoin y₁ y₂)) ((repMat (D.sp.cm.sig : D.host.E →+* D.host.E) b a).map (incA D))) =
        -HMul.hMul (colJoin y₁ (0 : Mx D m s)) (rat a) ∧
      yPart (HMul.hMul (zy (colJoin y₁ y₂)) ((repMat (D.sp.cm.sig : D.host.E →+* D.host.E) b a).map (incA D))) =
        HMul.hMul (colJoin (-HMul.hMul y₁ (rat b)) y₂) (rat (cT (D.sp.cm.sig : D.host.E →+* D.host.E) a)⁻¹) := by
  first | exact @GlobalTheory.CompanionTheory.EisUnfold.Parts.parts | exact GlobalTheory.CompanionTheory.EisUnfold.Parts.parts | (intros; apply GlobalTheory.CompanionTheory.EisUnfold.Parts.parts <;> assumption)
end
end

section

open GlobalTheory.CompanionTheory.PairMult

noncomputable section

open Finset
open CompanionTheory.D.LK (Pos)

namespace GlobalTheory.CompanionTheory.PairMult.TopCycQ

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

theorem annq_app (l : Lt n) (x : Cq n V) (B : Finset (Lt n)) :
    annq l x B = if l ∈ B then 0 else sgL l B • x (insert l B) := rfl

theorem creq_app (l : Lt n) (x : Cq n V) (B : Finset (Lt n)) :
    creq l x B = if l ∈ B then sgL l B • x (B.erase l) else 0 := rfl

theorem mem_omQ (lev : Fin n → ℕ) (l : Lt n) :
    l ∈ omQ lev ↔ l.1 = true ∧ lev l.2.1.1 < lev l.2.1.2 := by
  simp [omQ]

theorem insert_ne_omQ (lev : Fin n → ℕ) (s t : Bool) (i j k : Pos n)
    (ht : i.1.2 = j.1.1 ∧ k.1.1 = i.1.1 ∧ k.1.2 = j.1.2) (C : Finset (Lt n)) :
    insert (s, i) (insert (t, j) (C.erase ((s == t), k))) ≠ omQ lev := by
  intro e
  have hi := (mem_omQ lev _).1 (e ▸ mem_insert_self _ _)
  have hj := (mem_omQ lev _).1 (e ▸ mem_insert_of_mem (mem_insert_self _ _))
  obtain ⟨t1, t2, t3⟩ := ht
  have hs : s = true := hi.1
  have htt : t = true := hj.1
  subst hs htt
  have ck : ((true == true), k) ∈ omQ lev := (mem_omQ lev _).2
    ⟨rfl, by rw [t2, t3]; exact (hi.2.trans_eq (congrArg lev t1)).trans hj.2⟩
  rw [← e] at ck
  rcases mem_insert.1 ck with h | h
  · have hk : k = i := congrArg Prod.snd h
    subst hk
    have pj := j.2
    rw [← t1, t3] at pj
    exact lt_irrefl _ pj
  · rcases mem_insert.1 h with h | h
    · have hk : k = j := congrArg Prod.snd h
      subst hk
      have pi := i.2
      rw [← t2, t1] at pi
      exact lt_irrefl _ pi
    · exact notMem_erase _ _ h

theorem topCyc : TopCyc := by
  intro n lev V _ _ E1 E2 _ v hv
  funext A
  simp only [bdq, LinearMap.add_apply, LinearMap.sum_apply, Pi.add_apply, Finset.sum_apply, Pi.zero_apply]
  rw [Finset.sum_eq_zero, Finset.sum_eq_zero, add_zero]
  · intro s _
    refine Finset.sum_eq_zero fun t _ => Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ =>
      Finset.sum_eq_zero fun k _ => ?_
    split_ifs with ht
    · rw [Module.End.mul_apply, Module.End.mul_apply, creq_app]
      split_ifs with hk
      · rw [annq_app]
        split_ifs with h1
        · exact smul_zero _
        · rw [annq_app]
          split_ifs with h2
          · simp
          · rw [topq, Pi.single_eq_of_ne (insert_ne_omQ lev s t i j k ht A), smul_zero, smul_zero, smul_zero]
      · rfl
    · rfl
  · intro l _
    show Tl E1 E2 l (annq l (topq lev v) A) = 0
    rw [annq_app]
    split_ifs with hl
    · exact map_zero _
    · by_cases e : insert l A = omQ lev
      · have hlK := (mem_omQ lev l).1 (e ▸ mem_insert_self l A)
        rw [topq, e, Pi.single_eq_same, map_smul, hv l hlK, smul_zero]
      · rw [topq, Pi.single_eq_of_ne e, smul_zero, map_zero]

end GlobalTheory.CompanionTheory.PairMult.TopCycQ
end
end

section

open Finset

noncomputable section

namespace GlobalTheory.CompanionTheory.RealMult.TorC

open CompanionTheory.D.LK (Pos)

section Abstract

variable {R ι : Type*} [Ring R] [Algebra ℂ R] [Fintype ι] [DecidableEq ι]

def br (x y : R) : R := x * y - y * x

theorem br_mul (x y z : R) : br x (y * z) = br x y * z + y * br x z := by
  simp only [GlobalTheory.CompanionTheory.RealMult.TorC.br, mul_sub, sub_mul, mul_assoc]
  abel

theorem br_add_right (x y z : R) : br x (y + z) = br x y + br x z := by
  simp only [GlobalTheory.CompanionTheory.RealMult.TorC.br, mul_add, add_mul]
  abel

theorem br_add_left (x y z : R) : br (x + y) z = br x z + br y z := by
  simp only [GlobalTheory.CompanionTheory.RealMult.TorC.br, mul_add, add_mul]
  abel

theorem br_smul_right (r : ℂ) (x y : R) : br x (r • y) = r • br x y := by
  simp only [GlobalTheory.CompanionTheory.RealMult.TorC.br, mul_smul_comm, smul_mul_assoc, smul_sub]

theorem br_sum_right {κ : Type*} (s : Finset κ) (x : R) (f : κ → R) : br x (∑ i ∈ s, f i) = ∑ i ∈ s, br x (f i) := by
  simp only [GlobalTheory.CompanionTheory.RealMult.TorC.br, Finset.mul_sum, Finset.sum_mul, Finset.sum_sub_distrib]

theorem br_anti (x y : R) : br x y = -br y x := by
  simp only [GlobalTheory.CompanionTheory.RealMult.TorC.br, neg_sub]

theorem swap3 {M : Type*} [AddCommMonoid M] (g : ι → ι → ι → M) :
    ∑ j, ∑ k, ∑ b, g j k b = ∑ b, ∑ k, ∑ j, g j k b := by
  calc ∑ j, ∑ k, ∑ b, g j k b = ∑ j, ∑ b, ∑ k, g j k b :=
        Finset.sum_congr rfl fun j _ => Finset.sum_comm
    _ = ∑ b, ∑ j, ∑ k, g j k b := Finset.sum_comm
    _ = ∑ b, ∑ k, ∑ j, g j k b := Finset.sum_congr rfl fun b _ => Finset.sum_comm

theorem swap4 {M : Type*} [AddCommMonoid M] (f : ι → ι → ι → ι → M) :
    ∑ i, ∑ j, ∑ k, ∑ b, f i j k b = ∑ b, ∑ j, ∑ k, ∑ i, f i j k b := by
  calc ∑ i, ∑ j, ∑ k, ∑ b, f i j k b = ∑ i, ∑ j, ∑ b, ∑ k, f i j k b :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_comm
    _ = ∑ i, ∑ b, ∑ j, ∑ k, f i j k b := Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ b, ∑ i, ∑ j, ∑ k, f i j k b := Finset.sum_comm
    _ = ∑ b, ∑ j, ∑ i, ∑ k, f i j k b := Finset.sum_congr rfl fun b _ => Finset.sum_comm
    _ = ∑ b, ∑ j, ∑ k, ∑ i, f i j k b :=
        Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun j _ => Finset.sum_comm

def Dm (a c : ι → R) (A : ι → ι → ℂ) : R := ∑ i, ∑ k, A i k • (c k * a i)

theorem reindex (W : ι → ι → ι → R) (S : ι → ι → ι → ℂ) (A : ι → ι → ℂ) :
    ∑ i, ∑ j, ∑ k, S i j k • ((∑ l, A k l • W i j l) - (∑ b, A b j • W i b k) - ∑ b, A b i • W b j k) =
      ∑ i, ∑ j, ∑ k, ((∑ m, S i j m * A m k) - (∑ m, S i m k * A j m) - ∑ m, S m j k * A i m) • W i j k := by
  simp only [smul_sub, sub_smul, Finset.smul_sum, Finset.sum_smul, smul_smul, Finset.sum_sub_distrib]
  refine congrArg₂ _ (congrArg₂ _ ?_ ?_) ?_
  · exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_comm
  · exact Finset.sum_congr rfl fun i _ => GlobalTheory.CompanionTheory.RealMult.TorC.swap3 _
  · exact GlobalTheory.CompanionTheory.RealMult.TorC.swap4 _

variable {a c : ι → R}

theorem term_a (haa : ∀ i j, a i * a j + a j * a i = 0)
    (hac : ∀ i j, a i * c j + c j * a i = if i = j then 1 else 0) (i k m : ι) :
    br (c k * a i) (a m) = -(if m = k then a i else 0) := by
  have h₁ : a i * a m = -(a m * a i) := eq_neg_of_add_eq_zero_left (haa i m)
  have h₂ : a m * c k = (if m = k then 1 else 0) - c k * a m := eq_sub_of_add_eq (hac m k)
  unfold GlobalTheory.CompanionTheory.RealMult.TorC.br
  rw [mul_assoc, h₁, ← mul_assoc (a m), h₂]
  split_ifs <;> simp only [sub_mul, mul_neg, mul_assoc, one_mul, zero_mul] <;> abel

theorem term_c (hcc : ∀ i j, c i * c j + c j * c i = 0)
    (hac : ∀ i j, a i * c j + c j * a i = if i = j then 1 else 0) (i k m : ι) :
    br (c k * a i) (c m) = if i = m then c k else 0 := by
  have h₁ : a i * c m = (if i = m then 1 else 0) - c m * a i := eq_sub_of_add_eq (hac i m)
  have h₂ : c m * c k = -(c k * c m) := eq_neg_of_add_eq_zero_left (hcc m k)
  unfold GlobalTheory.CompanionTheory.RealMult.TorC.br
  rw [mul_assoc, h₁, ← mul_assoc (c m), h₂]
  split_ifs <;> simp only [mul_sub, neg_mul, mul_assoc, mul_one, mul_zero] <;> abel

theorem dm_a (haa : ∀ i j, a i * a j + a j * a i = 0)
    (hac : ∀ i j, a i * c j + c j * a i = if i = j then 1 else 0) (A : ι → ι → ℂ) (m : ι) :
    br (Dm a c A) (a m) = -∑ i, A i m • a i := by
  calc GlobalTheory.CompanionTheory.RealMult.TorC.br (GlobalTheory.CompanionTheory.RealMult.TorC.Dm a c A) (a m)
        = ∑ i, ∑ k, A i k • GlobalTheory.CompanionTheory.RealMult.TorC.br (c k * a i) (a m) := by
          simp only [GlobalTheory.CompanionTheory.RealMult.TorC.Dm, GlobalTheory.CompanionTheory.RealMult.TorC.br,
            Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, smul_sub,
            Finset.sum_sub_distrib]
    _ = ∑ i, ∑ k, A i k • -(if m = k then a i else 0) := by
          simp only [GlobalTheory.CompanionTheory.RealMult.TorC.term_a haa hac]
    _ = -∑ i, A i m • a i := by
          simp [smul_ite, Finset.sum_neg_distrib]

theorem dm_c (hcc : ∀ i j, c i * c j + c j * c i = 0)
    (hac : ∀ i j, a i * c j + c j * a i = if i = j then 1 else 0) (A : ι → ι → ℂ) (m : ι) :
    br (Dm a c A) (c m) = ∑ k, A m k • c k := by
  calc GlobalTheory.CompanionTheory.RealMult.TorC.br (GlobalTheory.CompanionTheory.RealMult.TorC.Dm a c A) (c m)
        = ∑ i, ∑ k, A i k • GlobalTheory.CompanionTheory.RealMult.TorC.br (c k * a i) (c m) := by
          simp only [GlobalTheory.CompanionTheory.RealMult.TorC.Dm, GlobalTheory.CompanionTheory.RealMult.TorC.br,
            Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, smul_sub,
            Finset.sum_sub_distrib]
    _ = ∑ i, ∑ k, A i k • (if i = m then c k else 0) := by
          simp only [GlobalTheory.CompanionTheory.RealMult.TorC.term_c hcc hac]
    _ = ∑ k, A m k • c k := by
          rw [Finset.sum_comm]
          simp [smul_ite]

theorem bracket_wedge_formula (haa : ∀ i j, a i * a j + a j * a i = 0) (hcc : ∀ i j, c i * c j + c j * c i = 0)
    (hac : ∀ i j, a i * c j + c j * a i = if i = j then 1 else 0) (A : ι → ι → ℂ) (i j k : ι) :
    br (Dm a c A) (c k * a j * a i) =
      (∑ l, A k l • (c l * a j * a i)) - (∑ b, A b j • (c k * a b * a i)) - ∑ b, A b i • (c k * a j * a b) := by
  rw [GlobalTheory.CompanionTheory.RealMult.TorC.br_mul, GlobalTheory.CompanionTheory.RealMult.TorC.br_mul,
    GlobalTheory.CompanionTheory.RealMult.TorC.dm_c hcc hac,
    GlobalTheory.CompanionTheory.RealMult.TorC.dm_a haa hac,
    GlobalTheory.CompanionTheory.RealMult.TorC.dm_a haa hac]
  simp only [add_mul, mul_neg, neg_mul, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc,
    mul_smul_comm, mul_assoc]
  abel

theorem br_lift_dm {L : R} (hLa : ∀ i, br L (a i) = 0) (hLc : ∀ i, br L (c i) = 0) (A : ι → ι → ℂ) :
    br L (Dm a c A) = 0 := by
  simp only [GlobalTheory.CompanionTheory.RealMult.TorC.Dm, GlobalTheory.CompanionTheory.RealMult.TorC.br_sum_right,
    GlobalTheory.CompanionTheory.RealMult.TorC.br_smul_right, GlobalTheory.CompanionTheory.RealMult.TorC.br_mul, hLa, hLc, zero_mul, mul_zero,
    add_zero, smul_zero, Finset.sum_const_zero]

end Abstract

section Car

variable {n : ℕ}

theorem key_lt (p : Pos n) : CompanionTheory.D.LK.key p < n * n := by
  unfold CompanionTheory.D.LK.key
  have h1 := p.1.1.2
  have h2 := p.1.2.2
  nlinarith

theorem keyR_inj {i j : Ix n} (h : keyR i = keyR j) : i = j := by
  obtain ⟨b, p⟩ := i
  obtain ⟨b', q⟩ := j
  have hp := key_lt p
  have hq := key_lt q
  cases b <;> cases b' <;> simp only [keyR, if_true, Bool.false_eq_true, if_false] at h
  · rw [CompanionTheory.D.LK.Car.key_inj (by omega : CompanionTheory.D.LK.key p = CompanionTheory.D.LK.key q)]
  · omega
  · omega
  · rw [CompanionTheory.D.LK.Car.key_inj (by omega : CompanionTheory.D.LK.key p = CompanionTheory.D.LK.key q)]

def tw (i j : Ix n) : ℂ := if keyR j < keyR i then -1 else 1

theorem tw_self (i : Ix n) : tw i i = 1 := by simp [tw]

theorem tw_mul_self (i j : Ix n) : tw i j * tw i j = 1 := by
  unfold tw; split_ifs <;> simp

theorem tw_swap {i j : Ix n} (h : i ≠ j) : tw j i = -tw i j := by
  have hk : keyR i ≠ keyR j := fun e => h (keyR_inj e)
  unfold tw
  rcases lt_or_gt_of_ne hk with h1 | h1
  · simp [h1, h1.not_gt]
  · simp [h1, h1.not_gt]

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem liftR_apply {V' : Type} [AddCommGroup V'] [Module ℂ V'] (T : V →ₗ[ℂ] V') (x : Cr n V)
    (A : Finset (Ix n)) : liftR n T x A = T (x A) := rfl

theorem br_lift_lift (T S : Module.End ℂ V) :
    br (liftR n T : Module.End ℂ (Cr n V)) (liftR n S) = liftR n (br T S) := by
  refine LinearMap.ext fun x => funext fun A => ?_
  simp [br, liftR_apply]

end Car

section Coefficients

variable {n : ℕ}

end Coefficients

section Units

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

variable {E1 E2 : Fin n → Fin n → Module.End ℂ V}

end Units

end GlobalTheory.CompanionTheory.RealMult.TorC
end
end

section


theorem _root_.GlobalTheory.T.height_eq_of_full_intersection_system : GlobalTheory.CompanionTheory.MixZ.PtDict → GlobalTheory.CompanionTheory.MixZ.CodimOne → GlobalTheory.CompanionTheory.MixZ.ExistsRat → GlobalTheory.CompanionTheory.MixZ.CycleOfRat → GlobalTheory.CompanionTheory.MixZ.ArchIntEq → GlobalTheory.CompanionTheory.MixZ.VertEq → GlobalTheory.CompanionTheory.MixZ.PtLen → GlobalTheory.CompanionTheory.MixZ.CurveInt → ReciprocityTheory.ChartRestriction.G.AI.I2.RatRStatement → ∀ II : ReciprocityTheory.ChartRestriction.G.Geo.IntersectionSystem, ReciprocityTheory.ChartRestriction.G.Geo.IsFullIntersectionSystem II → GlobalTheory.CompanionTheory.MixZ.HeightEq II := by
  first | exact @GlobalTheory.CompanionTheory.MixZ.heightEq_holds | exact GlobalTheory.CompanionTheory.MixZ.heightEq_holds | (intros; apply GlobalTheory.CompanionTheory.MixZ.heightEq_holds <;> assumption)
end

section


theorem _root_.GlobalTheory.T.mixed_point_length_formula : GlobalTheory.CompanionTheory.MixZ.PtLen := by
  first | exact @GlobalTheory.CompanionTheory.MixZ.PtLenProof.ptLen | exact GlobalTheory.CompanionTheory.MixZ.PtLenProof.ptLen | (intros; apply GlobalTheory.CompanionTheory.MixZ.PtLenProof.ptLen <;> assumption)
end
