module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle035
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.Bundle003
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.Bundle002
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.IsExtAtOfDiff
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle037
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.Bundle003
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle039
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle036
import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.G2HaarMeasure.ContinuousInFrame
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.MatrixOfUnipotentFrame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1891
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKwhitIwa
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle026
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.Bundle005
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.AStep
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem T_sub_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (Φ Φ' : d.Fn) : d.T (Φ - Φ') = d.T Φ - d.T Φ' := by
  funext X
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.T, Pi.sub_apply]
  rw [← map_sub]
  congr 1
  funext y
  simp [Darboux.rho, schr, mul_sub]
theorem vac_tens_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (f : Mx F E d.m d.n → ℂ) (hf : f ∈ R.vac) :
    ∃ Ψ ∈ R.away w, f = R.tens w (fP 1) Ψ := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨g, hg, rfl⟩ := hf
    refine ⟨fun X => (∏ w' ∈ Finset.univ.erase w, fP 1 (R.loc w' X)) * g fun k => (d.crd X k).2,
      Submodule.subset_span ⟨fun _ => 1, g, hg, rfl⟩, ?_⟩
    funext X
    simp only [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens]
    rw [← mul_assoc, Finset.mul_prod_erase _ (fun w' => fP 1 (R.loc w' X)) (Finset.mem_univ w)]
  | zero => exact ⟨0, zero_mem _, by funext X; simp [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens]⟩
  | add f f' _ _ h h' =>
    obtain ⟨Ψ, hΨ, rfl⟩ := h
    obtain ⟨Ψ', hΨ', rfl⟩ := h'
    exact ⟨Ψ + Ψ', add_mem hΨ hΨ', by funext X; simp [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, mul_add]⟩
  | smul a f _ h =>
    obtain ⟨Ψ, hΨ, rfl⟩ := h
    exact ⟨a • Ψ, Submodule.smul_mem _ a hΨ, by funext X; simp [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens]; ring⟩
theorem ndA_k (H : _root_.PositivityTheory.SiegelWeilFormula.AStep.Hyps_k) {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (hmn : d.m < d.n) {Φ : d.Fn} (hΦ : Φ ∈ d.sch) (hv : d.T Φ ∈ R.vac)
    {U p Ê t} (hE : _root_.PositivityTheory.SiegelWeilFormula.AStep.EData_k d (d.sec0 Φ) (s0 d.m d.n) (s0 d.m d.n) U p Ê t) (j : ℕ) (hj : j ≤ p.rootMultiplicity (s0 d.m d.n)) :
    ∀ L ∈ d.lamSet, L (fun g => iteratedDeriv j (Ê · g) (s0 d.m d.n)) = 0 := by
  intro L hL
  have hK := H.polyKFin F E σ d R Φ hΦ ((H.vacK F E σ d R).2.1 hv)
  have hsec := H.secK F E σ d Φ hK
  have hEis := H.eisWk F E σ d _ _ hsec
  obtain ⟨hadd, hbd⟩ := H.lamBd F E σ d L hL
  obtain ⟨nb, lam, 𝓖, T, x, hc, hT, rfl⟩ := hL
  obtain ⟨hUo, hR, hs, hp, hd, hcont, hinv, hfar⟩ := hE
  obtain ⟨hDiff, hComm⟩ := lamDeriv (rat2 σ d.Y) _ hadd hbd U Ê hUo hd hcont hinv
  show fc d.B.ψ d.b nb lam 𝓖 (fun g => iteratedDeriv j (Ê · g) (s0 d.m d.n)) T x = 0
  rw [← hComm _ hs j]
  obtain ⟨t', ht'⟩ := H.unfold F E σ d _ _ hsec hEis
  obtain ⟨ε, w, hw, -⟩ := (H.auxEx F E σ d).2.1
  have hWL := H.whitLow F E σ d R hmn Φ hΦ hv nb lam 𝓖 hc ε w hw T hT x
  rw [zero_mul] at hWL
  have := ordVal U p (fun z => fc d.B.ψ d.b nb lam 𝓖 (Ê z) T x)
    (fun z => ∫ β, _root_.GlobalTheory.ThK.Dbl.flat d.a (d.sec0 Φ) (s0 d.m d.n) z (w * nb β * x) * d.B.ψ (-d.tt (T.1.1 * β.1)) ∂lam) (max t t')
    (s0 d.m d.n) 0 hUo hR hs hp hDiff ?_ hWL j hj
  · rw [this, mul_zero]
  · intro z hz
    have h1 := (hfar z (lt_of_le_of_lt (le_max_left _ _) hz)).2
    have h2 := (ht' z (lt_of_le_of_lt (le_max_right _ _) hz) nb lam 𝓖 hc ε w hw x).2 T hT
    rw [← h2]
    simp only [fc, h1, mul_assoc]
    exact integral_const_mul _ _
theorem holA_pf_k (H : _root_.PositivityTheory.SiegelWeilFormula.AStep.Hyps_k) {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (hmn : d.m < d.n) {Φ : d.Fn} (hΦ : Φ ∈ d.sch) (hv : d.T Φ ∈ R.vac)
    {U : Set ℂ} {p : Polynomial ℂ} {Ê : ℂ → d.G → ℂ} {t : ℝ}
    (hE : _root_.PositivityTheory.SiegelWeilFormula.AStep.EData_k d (d.sec0 Φ) (s0 d.m d.n) (s0 d.m d.n) U p Ê t) (w : InfinitePlace F) (j : ℕ)
    (hj : j ≤ p.rootMultiplicity (s0 d.m d.n)) (hlow : ∀ i < j, ∀ g, iteratedDeriv i (Ê · g) (s0 d.m d.n) = 0) :
    ∃ (pp qq : ℕ) (e : ℤ), (pp = d.m ∧ qq = 0 ∨ pp = 0 ∧ qq = d.m) ∧
      ∀ g, IsHolW pp qq e fun y => iteratedDeriv j (Ê · (g * R.ι w y)) (s0 d.m d.n) := by
  obtain ⟨-, -, hTG, hLC, hT2, hSC⟩ := H.auxEx F E σ d
  have hE' := hE
  obtain ⟨hUo, hR, hs, hp, hd, hcont, hinv, hfar⟩ := hE'
  have hAc := famCont U Ê hUo hd hcont _ hs j
  have hAi : ∀ γ ∈ rat2 σ d.Y, ∀ g, iteratedDeriv j (Ê · (γ * g)) (s0 d.m d.n) = iteratedDeriv j (Ê · g) (s0 d.m d.n) :=
    fun γ hγ g => derivInv U Ê hUo _ hs γ g (fun z hz => hinv z hz γ hγ g) j
  obtain ⟨Ψ, hΨ, hTΨ⟩ := _root_.PositivityTheory.SiegelWeilFormula.AStep.vac_tens_k R w _ hv
  obtain ⟨Lop, hLop⟩ := H.locOpEx F E σ d R w
  obtain ⟨φ, hφ⟩ := H.liftEx F E σ d R w Ψ hΨ
  obtain ⟨sL, ρ, pp, qq, e, -, hLD, hsL, -⟩ := H.locInst F E σ d R w Lop hLop
  have hΦφ : φ 1 = Φ := by
    have h0 := (H.tAll.1 F E σ d).2.2 (φ 1 - Φ) (sub_mem (hφ 1).1 hΦ) (by rw [_root_.PositivityTheory.SiegelWeilFormula.AStep.T_sub_k, (hφ 1).2, hTΨ, sub_self])
    exact sub_eq_zero.1 h0
  have hpq : pp = d.m ∧ qq = 0 ∨ pp = 0 ∧ qq = d.m := by
    rcases hLD.sign with ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩
    · left; rw [h1, h2, cnt_true, cnt_false]; exact ⟨rfl, rfl⟩
    · right; rw [h1, h2, cnt_true, cnt_false]; exact ⟨rfl, rfl⟩
  refine ⟨pp, qq, e, hpq, ?_⟩
  haveI := hTG; haveI := hLC; haveI := hT2; haveI := hSC
  refine H.holLead d.m d.n pp qq e d.ok.hm hmn hpq d.G (par2 σ d.Y) (rat2 σ d.Y) (R.ι w) (s0 d.m d.n) d.Ht (d.sec0 Φ)
    (R.cont w) ?_ U p Ê t hUo hR hs hd hcont (fun z hz => ⟨(hfar z hz).1, fun g => (hfar z hz).2 g⟩) j hlow ?_
  · intro g
    obtain ⟨x, y, c, r, hr, hg, hxy⟩ := H.gSplit F E σ d R w Lop hLop Ψ hΨ φ hφ g
    refine ⟨x, y, c, r, hr, hg, fun y' => ⟨(hxy y').1, ?_⟩⟩
    rw [← hΦφ, (hxy y').2 1, ← hsL, hLD.vac]
  · intro ψ hψ nb hnb g a b
    exact H.lamSing F E σ d R w _ hAc hAi (_root_.PositivityTheory.SiegelWeilFormula.AStep.ndA_k H R hmn hΦ hv hE j hj) ψ hψ nb hnb g a b
end PositivityTheory.SiegelWeilFormula.AStep
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.Act.C1
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} {L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d} {uM : (Fin L.n → AE F E) → d.G} {ν : Measure (Fin L.n → AE F E)}
  {𝓤 : Set (Fin L.n → AE F E)} {nb : nA σ d.Y d.b → d.G}
def Ap_k (hU : L.UData uM ν 𝓤) (u : Fin L.n → AE F E) : Matrix (Fin d.n) (Fin d.n) (AE F E) := (hU.1 u).choose
theorem inFrame_uM_k (hU : L.UData uM ν 𝓤) (u : Fin L.n → AE F E) :
    inFrame d.b (uM u) = Matrix.fromBlocks (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_k L u) 0 0 (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.Ap_k hU u) := (hU.1 u).choose_spec
theorem uM_add_k (hU : L.UData uM ν 𝓤) (u v : Fin L.n → AE F E) : uM (u + v) = uM u * uM v := by
  refine _root_.PositivityTheory.SiegelWeilFormula.Act.C1.blk_unique_k d (A₂ := _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Ap_k hU u * _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Ap_k hU v) (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.inFrame_uM_k hU (u + v)) ?_
  rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, _root_.PositivityTheory.SiegelWeilFormula.Act.C1.inFrame_uM_k hU, _root_.PositivityTheory.SiegelWeilFormula.Act.C1.inFrame_uM_k hU, Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_mul_k]
theorem uM_zero_k (hU : L.UData uM ν 𝓤) : uM 0 = 1 := by
  refine _root_.PositivityTheory.SiegelWeilFormula.Act.C1.blk_unique_k d (A₂ := 1) (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.inFrame_uM_k hU 0) ?_
  rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_one, _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_zero_k, Matrix.fromBlocks_one]
theorem uM_neg_k (hU : L.UData uM ν 𝓤) (u : Fin L.n → AE F E) : uM (-u) = (uM u)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← _root_.PositivityTheory.SiegelWeilFormula.Act.C1.uM_add_k hU, neg_add_cancel, _root_.PositivityTheory.SiegelWeilFormula.Act.C1.uM_zero_k hU])
theorem Ap_neg_mul_k (hU : L.UData uM ν 𝓤) (u : Fin L.n → AE F E) : _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Ap_k hU (-u) * _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Ap_k hU u = 1 := by
  have h := congrArg (inFrame d.b) (show uM (-u) * uM u = 1 by rw [← _root_.PositivityTheory.SiegelWeilFormula.Act.C1.uM_add_k hU, neg_add_cancel, _root_.PositivityTheory.SiegelWeilFormula.Act.C1.uM_zero_k hU])
  rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, _root_.PositivityTheory.SiegelWeilFormula.Act.C1.inFrame_uM_k hU, _root_.PositivityTheory.SiegelWeilFormula.Act.C1.inFrame_uM_k hU, Matrix.fromBlocks_multiply,
    GlobalTheory.EisBL.DoubledParabolic.inFrame_one, ← Matrix.fromBlocks_one] at h
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add] at h
  exact (Matrix.fromBlocks_inj.1 h).2.2.2
theorem frame_conj_k (hU : L.UData uM ν 𝓤) (hN : IsNMap d.b nb) (u : Fin L.n → AE F E) (β : nA σ d.Y d.b) :
    inFrame d.b ((uM u)⁻¹ * nb β * uM u) = Matrix.fromBlocks 1 (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_k L (-u) * β.1 * _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Ap_k hU u) 0 1 := by
  rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, ← _root_.PositivityTheory.SiegelWeilFormula.Act.C1.uM_neg_k hU, _root_.PositivityTheory.SiegelWeilFormula.Act.C1.inFrame_uM_k hU, _root_.PositivityTheory.SiegelWeilFormula.Act.C1.inFrame_uM_k hU, hN β,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one, _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_mul_k, neg_add_cancel, _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_zero_k,
    _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Ap_neg_mul_k hU]
theorem cj_mem_k (hU : L.UData uM ν 𝓤) (hN : IsNMap d.b nb) (u : Fin L.n → AE F E) (β : nA σ d.Y d.b) :
    _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_k L (-u) * β.1 * _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Ap_k hU u ∈ nA σ d.Y d.b :=
  AddSubgroup.subset_closure ⟨_, _root_.PositivityTheory.SiegelWeilFormula.Act.C1.frame_conj_k hU hN u β⟩
def cj_k (hU : L.UData uM ν 𝓤) (hN : IsNMap d.b nb) (u : Fin L.n → AE F E) : nA σ d.Y d.b →+ nA σ d.Y d.b where
  toFun β := ⟨_, _root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_mem_k hU hN u β⟩
  map_zero' := Subtype.ext (by simp)
  map_add' β β' := Subtype.ext (by simp [Matrix.mul_add, Matrix.add_mul])
theorem cj_val_k (hU : L.UData uM ν 𝓤) (hN : IsNMap d.b nb) (u : Fin L.n → AE F E) (β : nA σ d.Y d.b) :
    (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_k hU hN u β).1 = _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_k L (-u) * β.1 * _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Ap_k hU u := rfl
theorem nb_cj_k (hU : L.UData uM ν 𝓤) (hN : IsNMap d.b nb) (u : Fin L.n → AE F E) (β : nA σ d.Y d.b) :
    nb (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_k hU hN u β) = (uM u)⁻¹ * nb β * uM u := by
  apply kunf.inFrame_injective d.b
  rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C1.frame_conj_k hU hN, hN]
  rfl
theorem cj_inv_k (hU : L.UData uM ν 𝓤) (hN : IsNMap d.b nb) (u : Fin L.n → AE F E) (β : nA σ d.Y d.b) :
    _root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_k hU hN (-u) (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_k hU hN u β) = β := by
  apply Subtype.ext
  have h1 : _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_k L u * _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_k L (-u) = 1 := by rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_mul_k, add_neg_cancel, _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_zero_k]
  have h2 : _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Ap_k hU u * _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Ap_k hU (-u) = 1 := by simpa using _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Ap_neg_mul_k hU (-u)
  rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_val_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_val_k, neg_neg]
  calc _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_k L u * (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_k L (-u) * β.1 * _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Ap_k hU u) * _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Ap_k hU (-u)
      = (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_k L u * _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_k L (-u)) * β.1 * (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.Ap_k hU u * _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Ap_k hU (-u)) := by simp only [Matrix.mul_assoc]
    _ = β.1 := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]
theorem continuous_cj_k (hU : L.UData uM ν 𝓤) (hN : IsNMap d.b nb) (u : Fin L.n → AE F E) :
    Continuous (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_k hU hN u) :=
  ((continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const).subtype_mk _
def cjE_k (hU : L.UData uM ν 𝓤) (hN : IsNMap d.b nb) (u : Fin L.n → AE F E) : nA σ d.Y d.b ≃ₜ+ nA σ d.Y d.b where
  toFun := _root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_k hU hN u
  invFun := _root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_k hU hN (-u)
  left_inv β := _root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_inv_k hU hN u β
  right_inv β := by simpa using _root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_inv_k hU hN (-u) β
  map_add' := map_add _
  continuous_toFun := _root_.PositivityTheory.SiegelWeilFormula.Act.C1.continuous_cj_k hU hN u
  continuous_invFun := _root_.PositivityTheory.SiegelWeilFormula.Act.C1.continuous_cj_k hU hN (-u)
end PositivityTheory.SiegelWeilFormula.Act.C1
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.KWhit
open PositivityTheory.SiegelWeilFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem asm_gramR_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (η : E) (Y : Fin d.n → Fin d.m → AF F ⊗[F] E) :
    HeckeCharacterZeroLocus.SiegelWeilU.gramR (AF F) σ (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) Y =
      (HeckeCharacterZeroLocus.SiegelWeilU.inclR (F := F) (AF F) η) • (d.gram (toMx Y) (toMx Y))ᵀ := by
  ext c a
  simp only [HeckeCharacterZeroLocus.SiegelWeilU.gramR, HeckeCharacterZeroLocus.SiegelWeilU.hR, HeckeCharacterZeroLocus.SiegelWeilU.hform, HeckeCharacterZeroLocus.SiegelWeilU.JR, _root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k,
    Matrix.map_apply, Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul, _root_.PositivityTheory.SiegelWeilFormula.SD_k.gram, Matrix.mul_apply, toMx,
    Matrix.of_apply, incM, map_mul, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [asm_incl, asm_cA]
  ring
theorem asm_phase_cell_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} {R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d} {x : d.G} {t u : GL (Fin d.n) (AE F E)} {T : nF σ d.Y d.b} {η : E}
    {T₀ : Matrix (Fin d.n) (Fin d.n) E} {hOf : nA σ d.Y d.b → HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF F) σ d.n}
    {θ : InfinitePlace F → (HeckeCharacterZeroLocus.SiegelWeilU.Ainf F ⊗[F] E →+* ℂ)} {fr : InfinitePlace F → GL (Fin d.m) ℂ}
    {g : InfinitePlace F → GL (Fin d.n) ℂ} (hr : _root_.PositivityTheory.SiegelWeilFormula.KWhit.Rel_k d R x t u T η T₀ hOf θ fr g) (β : nA σ d.Y d.b)
    (Y : Fin d.n → Fin d.m → AF F ⊗[F] E) :
    -(⅟(2 : AF F) * d.tt (β.1 * d.gram (toMx Y) (toMx Y))) =
      PositivityTheory.PfSWUS.Loc.trPair (AF F) ((hOf β).1) (HeckeCharacterZeroLocus.SiegelWeilU.gramR (AF F) σ (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) Y) := by
  rw [PositivityTheory.PfSWUS.Loc.trPair, _root_.PositivityTheory.SiegelWeilFormula.KWhit.asm_gramR_k, hr.hof β, _root_.PositivityTheory.SiegelWeilFormula.SD_k.tt, asm_half, Matrix.neg_mul, asm_scalar_mul,
    Matrix.smul_mul, Matrix.trace_neg, Matrix.trace_smul, smul_eq_mul, map_neg, mul_neg, neg_neg]
  congr 1
  congr 1
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
  ring
theorem asm_phase_whit_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} {R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d} {x : d.G} {t u : GL (Fin d.n) (AE F E)} {T : nF σ d.Y d.b} {η : E}
    {T₀ : Matrix (Fin d.n) (Fin d.n) E} {hOf : nA σ d.Y d.b → HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF F) σ d.n}
    {θ : InfinitePlace F → (HeckeCharacterZeroLocus.SiegelWeilU.Ainf F ⊗[F] E →+* ℂ)} {fr : InfinitePlace F → GL (Fin d.m) ℂ}
    {g : InfinitePlace F → GL (Fin d.n) ℂ} (hr : _root_.PositivityTheory.SiegelWeilFormula.KWhit.Rel_k d R x t u T η T₀ hOf θ fr g) (β : nA σ d.Y d.b) :
    -d.tt (T.1.1 * β.1) =
      -PositivityTheory.PfSWUS.Loc.trPair (AF F) ((Td η T₀).map (HeckeCharacterZeroLocus.SiegelWeilU.inclR (AF F))) ((hOf β).1) := by
  rw [neg_inj, PositivityTheory.PfSWUS.Loc.trPair, hr.hof β, hr.rat, _root_.PositivityTheory.SiegelWeilFormula.SD_k.tt, asm_scalar_mul, Matrix.mul_neg, Matrix.mul_smul,
    Matrix.trace_neg, Matrix.trace_smul, smul_eq_mul, map_neg]
  have h2 : ∑ a, ∑ c, ((Td η T₀).map (HeckeCharacterZeroLocus.SiegelWeilU.inclR (F := F) (AF F))) a c * ((hOf β).1 : Mx F E d.n d.n) c a =
      algebraMap (AF F) (AE F E) (-2) * (HeckeCharacterZeroLocus.SiegelWeilU.inclR (F := F) (AF F) η *
        (incM F T₀ * ((hOf β).1 : Mx F E d.n d.n)ᵀ).trace) := by
    simp only [Td, Matrix.map_apply, Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_neg,
      map_ofNat, Matrix.trace, Matrix.diag, Matrix.mul_apply, incM, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
    rw [asm_incl]
    ring
  rw [h2, ← Algebra.smul_def (-2 : AF F) _, LinearMap.map_smul, smul_eq_mul, ← mul_assoc]
  have h5 : algebraMap F (AF F) (1 / 2) * (-2 : AF F) = -1 := by
    rw [show (-2 : AF F) = algebraMap F (AF F) (-2) by rw [map_neg, map_ofNat], ← map_mul]
    norm_num
  rw [h5]
  ring
theorem asm_c_ne_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (t : GL (Fin d.n) (AE F E)) :
    (d.χ (Matrix.GeneralLinearGroup.det t) : ℂ) *
      (((absE F E (Matrix.GeneralLinearGroup.det t) : ℝ) ^ ((d.m : ℝ) / 2) : ℝ) : ℂ) ≠ 0 := by
  have hpos : 0 < (absE F E (Matrix.GeneralLinearGroup.det t) : ℝ) := by
    have h : absE F E (Matrix.GeneralLinearGroup.det t) * absE F E (Matrix.GeneralLinearGroup.det t)⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel, map_one]
    have h0 : absE F E (Matrix.GeneralLinearGroup.det t) ≠ 0 := left_ne_zero_of_mul_eq_one h
    exact_mod_cast pos_iff_ne_zero.2 h0
  exact mul_ne_zero (Circle.coe_ne_zero _) (Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos hpos _).ne')
theorem dictAsmX_k : _root_.PositivityTheory.SiegelWeilFormula.KWhit.DictAsmX_k := by
  intro hCell hRel hH hM hTh hT hA F E _ _ _ _ _ σ d R Φ hΦ P gf hpg x hx nb lam 𝓖 hcd ε w hw T hTnd
  obtain ⟨t, u, hxtu⟩ := hx
  obtain ⟨η, T₀, hOf, θ, fr, g, l, εs, Φg, Φf, Φv, μ, ν, hr, hΦg, hani, hεs, hcm, hherm, hTT, hdet, hchr, hpl, hfr,
    hpure, hprod, hsdW, hsdH⟩ := hRel hT hA F E σ d R Φ hΦ P gf hpg x t u hxtu T hTnd
  obtain ⟨lv, L₁, L₂, C, hC, hlv, hco, hstd, hht⟩ := hH F E σ d R x t u T η T₀ hOf θ fr g hr nb lam 𝓖 hcd ε w hw
  obtain ⟨hMβ, hMZ⟩ := hM F E σ d R x t u T η T₀ hOf θ fr g hr
  obtain ⟨hembβ, hpresβ⟩ := hMβ nb lam 𝓖 hcd ν hsdH
  obtain ⟨νc, hνc⟩ := (hA F E σ d).1
  obtain ⟨hembZ, hpresZ⟩ := hMZ μ νc hsdW hνc
  obtain ⟨μH, 𝓕, hμH, h𝓕, horb⟩ := hTh F E σ d η hr.ne hr.herm
  set c : ℂ := (d.χ (Matrix.GeneralLinearGroup.det t) : ℂ) *
      (((absE F E (Matrix.GeneralLinearGroup.det t) : ℝ) ^ ((d.m : ℝ) / 2) : ℝ) : ℂ) with hc
  have hc0 : c ≠ 0 := _root_.PositivityTheory.SiegelWeilFormula.KWhit.asm_c_ne_k d t
  have hTx : ∀ Y, d.T (d.om x Φ) (toMx Y) = c * Φg Y := by
    intro Y
    rw [hΦg Y]
    exact (hT.2.1 F E σ d Φ hΦ.1).2.1 x t u hxtu (toMx Y)
  have hint : ∀ z : ℂ, ∀ β : nA σ d.Y d.b,
      _root_.GlobalTheory.ThK.Dbl.flat d.a (d.sec0 Φ) (s0 d.m d.n) z (w * nb β * x) * d.B.ψ (-d.tt (T.1.1 * β.1)) =
        c * (C : ℂ) ^ (z - s0 d.m d.n) * Gen.whI (AF F) σ (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) d.B.ψ μ Φg (Gen.nuA θ g lv L₁ L₂)
          ((Td η T₀).map (HeckeCharacterZeroLocus.SiegelWeilU.inclR (AF F))) z (hOf β) := by
    intro z β
    obtain ⟨hνpos, ha⟩ := hht β
    have hcell := hCell hT F E σ d νc hνc ε w hw Φ hΦ.1 (nb β) x β.1 (hcd.1 β)
    have hZ : ∫ Z, d.B.ψ (-(⅟(2 : AF F) * d.tt (β.1 * d.gram Z Z))) * d.T (d.om x Φ) Z ∂νc =
        c * PositivityTheory.PfSWUS.Loc.jtR (AF F) σ (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) d.B.ψ μ Φg (hOf β) := by
      rw [← hpresZ.integral_comp hembZ]
      simp only [PositivityTheory.PfSWUS.Loc.jtR, hTx, _root_.PositivityTheory.SiegelWeilFormula.KWhit.asm_phase_cell_k hr β]
      rw [← integral_const_mul]
      congr 1
      funext Y
      ring
    have hs : s0 d.m d.n = ((d.m : ℂ) - d.n) / 2 := rfl
    simp only [_root_.GlobalTheory.ThK.Dbl.flat]
    rw [hcell, hZ, ha, _root_.PositivityTheory.SiegelWeilFormula.KWhit.asm_phase_whit_k hr β, asm_cpow_split hC hνpos]
    simp only [Gen.whI, hs]
    ring
  refine ⟨2, _root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η, Td η T₀, d.bs, d.B.ψ, θ, l, εs, fr, g, lv, L₁, L₂, Φg, Φf, Φv, μ, ν, c, C,
    ⟨hcm, hherm, hTT, hdet, hchr, hpl, hfr, hlv, hco, hstd, hpure, hprod, hsdW, hsdH⟩, hani, hεs, hC,
    ⟨0, fun z _ => ⟨fun hI => ?_, ?_⟩⟩, μH, 𝓕, hμH, h𝓕, ?_⟩
  · have hk : c * (C : ℂ) ^ (z - s0 d.m d.n) ≠ 0 :=
      mul_ne_zero hc0 (Complex.cpow_ne_zero_iff.2 (Or.inl (Complex.ofReal_ne_zero.2 hC.ne')))
    have h1 : Integrable (fun β => _root_.GlobalTheory.ThK.Dbl.flat d.a (d.sec0 Φ) (s0 d.m d.n) z (w * nb β * x) *
        d.B.ψ (-d.tt (T.1.1 * β.1))) lam :=
      hI.mul_bdd (_root_.PositivityTheory.SiegelWeilFormula.KWhit.lin_psi_meas_k d T.1.1).aestronglyMeasurable
        (Eventually.of_forall fun β => (GlobalTheory.StdCharFromIsStd.norm_psi d.ok.good.std _).le)
    have h2 := h1.const_mul (c * (C : ℂ) ^ (z - s0 d.m d.n))⁻¹
    have hcomp : Integrable (fun β => Gen.whI (AF F) σ (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) d.B.ψ μ Φg (Gen.nuA θ g lv L₁ L₂)
        ((Td η T₀).map (HeckeCharacterZeroLocus.SiegelWeilU.inclR (AF F))) z (hOf β)) lam := by
      refine h2.congr (Eventually.of_forall fun β => ?_)
      simp only [hint z β]
      exact inv_mul_cancel_left₀ hk _
    exact (hpresβ.integrable_comp_emb hembβ).1 hcomp
  · simp_rw [hint z]
    rw [integral_const_mul, hpresβ.integral_comp hembβ]
  · rw [horb T T₀ hr.rat (d.om x Φ) (_root_.PositivityTheory.SiegelWeilFormula.KWhit.om_mem_sch_k d x hΦ.1)]
    have : (fun Y => d.T (d.om x Φ) (toMx Y)) = fun Y => c * Φg Y := funext hTx
    rw [this, asm_meanC_smul]
end PositivityTheory.SiegelWeilFormula.KWhit
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KWhit
open PositivityTheory.SiegelWeilFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
def thM_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {η : E} (hη : η ≠ 0) : UA σ d.A.J ≃ᵐ HeckeCharacterZeroLocus.SiegelWeilU.HA (AF F) σ (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) :=
  (Homeomorph.mk (_root_.PositivityTheory.SiegelWeilFormula.KWhit.thE_k d hη).toEquiv (_root_.PositivityTheory.SiegelWeilFormula.KWhit.thE_cont_k d hη) (_root_.PositivityTheory.SiegelWeilFormula.KWhit.thE_symm_cont_k d hη)).toMeasurableEquiv
def thE'_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {η : E} (hη : η ≠ 0) (g : UA σ d.A.J) : HeckeCharacterZeroLocus.SiegelWeilU.HR (AF F) σ (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) := _root_.PositivityTheory.SiegelWeilFormula.KWhit.thE_k d hη g
theorem th_rat_iff_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {η : E} (hη : η ≠ 0) (g : UA σ d.A.J) :
    g ∈ ratU σ d.A.J ↔ _root_.PositivityTheory.SiegelWeilFormula.KWhit.thE'_k d hη g ∈ HeckeCharacterZeroLocus.SiegelWeilU.HFinIn (AF F) σ (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) := by
  rw [ratU, Subgroup.mem_subgroupOf, MonoidHom.mem_range, HeckeCharacterZeroLocus.SiegelWeilU.HFinIn, Subgroup.mem_subgroupOf,
    HeckeCharacterZeroLocus.SiegelWeilU.HFin, Subgroup.mem_map]
  constructor
  · rintro ⟨γ, hγ⟩
    refine ⟨γ, ?_, hγ⟩
    have hg : (g.1 : GL (Fin d.m) (AE F E)) ∈ HeckeCharacterZeroLocus.SiegelWeilU.HR (AF F) σ (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) := (_root_.PositivityTheory.SiegelWeilFormula.KWhit.th_mem_iff_k d hη g.1).1 g.2
    rw [← hγ] at hg
    change HeckeCharacterZeroLocus.SiegelWeilU.cT (σ : E →+* E) (γ : Matrix (Fin d.m) (Fin d.m) E) * _root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η * (γ : Matrix (Fin d.m) (Fin d.m) E) =
      _root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η
    apply Matrix.map_injective (th_inclR_injective (F := F) (E := E))
    change HeckeCharacterZeroLocus.SiegelWeilU.cT (HeckeCharacterZeroLocus.SiegelWeilU.sigR (AF F) σ) ((γ : Matrix (Fin d.m) (Fin d.m) E).map (inclR (F := F) (E := E) (AF F))) *
      HeckeCharacterZeroLocus.SiegelWeilU.JR (AF F) (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) * (γ : Matrix (Fin d.m) (Fin d.m) E).map (inclR (F := F) (E := E) (AF F)) =
      HeckeCharacterZeroLocus.SiegelWeilU.JR (AF F) (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) at hg
    dsimp only
    rw [Matrix.map_mul, Matrix.map_mul, th_cT_map]
    exact hg
  · rintro ⟨γ, -, hγ⟩
    exact ⟨γ, hγ⟩
def thR_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {η : E} (hη : η ≠ 0) : HeckeCharacterZeroLocus.SiegelWeilU.HFinIn (AF F) σ (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) ≃ ratU σ d.A.J where
  toFun h := ⟨(_root_.PositivityTheory.SiegelWeilFormula.KWhit.thE_k d hη).symm h.1, (_root_.PositivityTheory.SiegelWeilFormula.KWhit.th_rat_iff_k d hη _).2
    (by have e1 : _root_.PositivityTheory.SiegelWeilFormula.KWhit.thE'_k d hη ((_root_.PositivityTheory.SiegelWeilFormula.KWhit.thE_k d hη).symm h.1) = h.1 := (_root_.PositivityTheory.SiegelWeilFormula.KWhit.thE_k d hη).apply_symm_apply h.1
        rw [e1]; exact h.2)⟩
  invFun g := ⟨_root_.PositivityTheory.SiegelWeilFormula.KWhit.thE'_k d hη g.1, (_root_.PositivityTheory.SiegelWeilFormula.KWhit.th_rat_iff_k d hη _).1 g.2⟩
  left_inv h := Subtype.ext ((_root_.PositivityTheory.SiegelWeilFormula.KWhit.thE_k d hη).apply_symm_apply h.1)
  right_inv g := Subtype.ext ((_root_.PositivityTheory.SiegelWeilFormula.KWhit.thE_k d hη).symm_apply_apply g.1)
theorem th_haar_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {η : E} (hη : η ≠ 0) :
    HeckeCharacterZeroLocus.SiegelWeilU.IsHaarH F E σ d.m (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) (d.μ.map (_root_.PositivityTheory.SiegelWeilFormula.KWhit.thM_k d hη)) := by
  have := d.ok.haar
  exact th_haar_map d.μ (_root_.PositivityTheory.SiegelWeilFormula.KWhit.thE_k d hη) (_root_.PositivityTheory.SiegelWeilFormula.KWhit.thE_cont_k d hη) (_root_.PositivityTheory.SiegelWeilFormula.KWhit.thE_symm_cont_k d hη)
theorem th_fd_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {η : E} (hη : η ≠ 0) :
    HeckeCharacterZeroLocus.SiegelWeilU.IsFDH F E σ d.m (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) (d.μ.map (_root_.PositivityTheory.SiegelWeilFormula.KWhit.thM_k d hη)) (_root_.PositivityTheory.SiegelWeilFormula.KWhit.thM_k d hη '' d.D) := by
  refine d.ok.dom.image_of_equiv (_root_.PositivityTheory.SiegelWeilFormula.KWhit.thM_k d hη).toEquiv ⟨(_root_.PositivityTheory.SiegelWeilFormula.KWhit.thM_k d hη).symm.measurable.aemeasurable, ?_⟩ (_root_.PositivityTheory.SiegelWeilFormula.KWhit.thR_k d hη) ?_
  · change Measure.map (_root_.PositivityTheory.SiegelWeilFormula.KWhit.thM_k d hη).symm (Measure.map (_root_.PositivityTheory.SiegelWeilFormula.KWhit.thM_k d hη) d.μ) ≪ d.μ
    rw [MeasurableEquiv.map_symm_map]
  · intro h x
    rfl
end PositivityTheory.SiegelWeilFormula.KWhit
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KWhit
open PositivityTheory.SiegelWeilFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
def vac_gen_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) : Set (Mx F E d.m d.n → ℂ) :=
  {f | ∃ φ, Dense.Good φ ∧ f = _root_.PositivityTheory.SiegelWeilFormula.KWhit.genF_k R (fun _ => 1) (Dense.pf φ)}
theorem vac_gen_sub_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) : _root_.PositivityTheory.SiegelWeilFormula.KWhit.vac_gen_k R ⊆ R.vac := by
  rintro _ ⟨φ, hφ, rfl⟩
  exact Submodule.subset_span ⟨Dense.pf φ, Dense.pf_mem hφ, rfl⟩
theorem vac_le_span_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) : R.vac ≤ Submodule.span ℂ (_root_.PositivityTheory.SiegelWeilFormula.KWhit.vac_gen_k R) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨g, hg, rfl⟩
  have := Dense.mem_span_pf hg
  clear hg
  have key : _root_.PositivityTheory.SiegelWeilFormula.KWhit.genL_k R (fun _ => 1) g ∈ Submodule.span ℂ (_root_.PositivityTheory.SiegelWeilFormula.KWhit.vac_gen_k R) := by
    induction this using Submodule.span_induction with
    | mem x hx => obtain ⟨φ, hφ, rfl⟩ := hx; exact Submodule.subset_span ⟨φ, hφ, rfl⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx
  exact key
theorem vac_isPureBy_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d)
    (φ : ∀ u : HeightOneSpectrum (𝓞 F), (Fin d.m × Fin d.n × Fin 2 → Fv F u) → ℂ) (hφ : Dense.Good φ) (Φ : d.Fn)
    (h : d.T Φ = _root_.PositivityTheory.SiegelWeilFormula.KWhit.genF_k R (fun _ => 1) (Dense.pf φ)) : ∃ gf, _root_.PositivityTheory.SiegelWeilFormula.KWhit.IsPureBy_k R Φ (fun _ => 1) gf := by
  refine ⟨φ, fun v => hφ.1 v, hφ.2.mono fun v hv => hv, ?_⟩
  rw [h]
  rfl
theorem vacSpan_k : _root_.PositivityTheory.SiegelWeilFormula.KWhit.VacSpan_k := by
  intro hT hF hPK hVK F E _ _ _ _ _ σ d R Φ hΦ hTΦ
  have hB := hT.1 F E σ d
  have hvf : R.vac ≤ R.fock := (hVK F E σ d R).2.1
  have h1 : d.T Φ ∈ Submodule.span ℂ (_root_.PositivityTheory.SiegelWeilFormula.KWhit.vac_gen_k R) := _root_.PositivityTheory.SiegelWeilFormula.KWhit.vac_le_span_k R hTΦ
  obtain ⟨k, c, gs, hsum⟩ := Submodule.mem_span_set'.1 h1
  have hpre : ∀ i : Fin k, ∃ Ψ ∈ d.sch, d.T Ψ = (gs i : Mx F E d.m d.n → ℂ) := fun i =>
    hB.2.1 _ ((hF F E σ d R).1 (hvf (_root_.PositivityTheory.SiegelWeilFormula.KWhit.vac_gen_sub_k R (gs i).2)))
  choose Φs hΦs hTs using hpre
  refine ⟨k, c, Φs, fun i => ⟨hPK F E σ d R (Φs i) (hΦs i) (hTs i ▸ hvf (_root_.PositivityTheory.SiegelWeilFormula.KWhit.vac_gen_sub_k R (gs i).2)),
    hTs i ▸ _root_.PositivityTheory.SiegelWeilFormula.KWhit.vac_gen_sub_k R (gs i).2, ?_⟩, ?_⟩
  · obtain ⟨φ, hφ, e⟩ := (gs i).2
    exact _root_.PositivityTheory.SiegelWeilFormula.KWhit.vac_isPureBy_k R φ hφ (Φs i) ((hTs i).trans e)
  · have hmem : Φ - ∑ i, c i • Φs i ∈ d.sch :=
      sub_mem hΦ (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hΦs i))
    have h0 : d.T (Φ - ∑ i, c i • Φs i) = 0 := by
      rw [_root_.PositivityTheory.SiegelWeilFormula.KWhit.T_sub_k, _root_.PositivityTheory.SiegelWeilFormula.KWhit.T_sum_k, ← hsum]
      simp only [hTs, sub_self]
    exact (sub_eq_zero.1 (hB.2.2 _ hmem h0))
end PositivityTheory.SiegelWeilFormula.KWhit
end
end
end
