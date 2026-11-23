module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle028
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle055
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle011
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle049
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle023
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle033
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle045
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle032
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.PsiZeroGram
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle046
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle043
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle025
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle039
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle120
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.StepNC
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle038
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle048
import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.G2HaarMeasure.ContinuousInFrame
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.MemStabiliserIffFrameLowerBlock
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.MatrixOfUnipotentFrame
import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle011
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.Bundle004
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle027
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.Act.C1
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ}
theorem range_or_k (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (u : Fin d.n ⊕ Fin d.n) :
    (∃ u', Sum.map L.em L.em u' = u) ∨ u ∈ ({Sum.inl L.i₀, Sum.inr L.i₀} : Set (Fin d.n ⊕ Fin d.n)) := by
  rcases u with a | a <;>
  · by_cases ha : a = L.i₀
    · right; simp [ha]
    · obtain ⟨a', rfl⟩ := (L.rng a).1 ha
      left; first | exact ⟨Sum.inl a', rfl⟩ | exact ⟨Sum.inr a', rfl⟩
theorem j_par_k (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) {p : G2 σ L.Y} (hp : p ∈ par2 σ L.Y) : L.j p ∈ par2 σ d.Y := by
  rw [ComplexParameterFamilyContinuity.mem_stabiliser_iff_frame_lower_block d.ok.frame]
  rw [ComplexParameterFamilyContinuity.mem_stabiliser_iff_frame_lower_block L.sd.ok.frame] at hp
  ext a c
  simp only [Matrix.toBlocks₂₁, Matrix.of_apply, Matrix.zero_apply]
  rcases _root_.PositivityTheory.SiegelWeilFormula.Act.C1.range_or_k L (Sum.inr a) with ⟨u', hu'⟩ | hu
  · rcases _root_.PositivityTheory.SiegelWeilFormula.Act.C1.range_or_k L (Sum.inl c) with ⟨v', hv'⟩ | hv
    · rcases u' with a' | a'
      · simp at hu'
      rcases v' with c' | c'
      · have h1 := congrFun (congrFun (L.j_in p) (Sum.inr a')) (Sum.inl c')
        simp only [Matrix.submatrix_apply, Sum.map_inr, Sum.map_inl] at h1
        simp only [Sum.map_inr, Sum.inr.injEq] at hu'
        simp only [Sum.map_inl, Sum.inl.injEq] at hv'
        rw [← hu', ← hv', h1]
        exact congrFun (congrFun hp a') c'
      · simp at hv'
    · rw [(L.j_out p _ hv (Sum.inr a)).2]
      simp
  · rw [(L.j_out p _ hu (Sum.inl c)).1]
    simp
theorem j_rat_k (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) {p : G2 σ L.Y} (hp : p ∈ rat2 σ L.Y) : L.j p ∈ rat2 σ d.Y := by
  obtain ⟨g, hg⟩ := hp
  have hm : mat2 p = incM F g.1 := (congrArg Units.val hg).symm
  have hL : inFrame L.b p = incM F ((L.b⁻¹).1 * g.1 * L.b.1) := by
    rw [kunf.incM_mul', kunf.incM_mul', ← hm]; rfl
  let M' := (L.b⁻¹).1 * g.1 * L.b.1
  let M : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E := fun u v =>
    if hu : ∃ u', Sum.map L.em L.em u' = u then
      if hv : ∃ v', Sum.map L.em L.em v' = v then M' hu.choose hv.choose else (1 : Matrix _ _ E) u v
    else (1 : Matrix _ _ E) u v
  refine kunf.rat_of_inFrame (b := d.b) (M := M) ?_
  ext u v
  show inFrame d.b (L.j p) u v = inclR (F := F) (AF F) (M u v)
  dsimp only [M]
  by_cases hu : ∃ u', Sum.map L.em L.em u' = u
  · by_cases hv : ∃ v', Sum.map L.em L.em v' = v
    · rw [dite_eq_left hu, dite_eq_left hv]
      have h1 := congrFun (congrFun (L.j_in p) hu.choose) hv.choose
      simp only [Matrix.submatrix_apply, hu.choose_spec, hv.choose_spec] at h1
      rw [h1, hL]
      rfl
    · rw [dite_eq_left hu, dite_eq_right hv]
      have hv' := (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.range_or_k L v).resolve_left hv
      rw [(L.j_out p _ hv' u).2]
      simp [Matrix.one_apply, apply_ite]
  · rw [dite_eq_right hu]
    have hu' := (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.range_or_k L u).resolve_left hu
    rw [(L.j_out p _ hu' v).1]
    simp [Matrix.one_apply, apply_ite]
theorem phz_j_leftInv_k (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) {s₁ : ℂ} {f : d.G → ℂ} (hf : IsSec d.K d.χ s₁ f) (z : ℂ) (x : d.G) :
    GlobalTheory.AutomorphicL2Unitary.LeftInv (par2 σ L.Y ⊓ rat2 σ L.Y)
      (fun g : G2 σ L.Y => ((d.Ht (L.j g * x) : ℝ) : ℂ) ^ (z - s₁) * f (L.j g * x)) := by
  intro p hp g
  show _root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (L.j (p * g) * x) = _root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (L.j g * x)
  rw [map_mul, mul_assoc]
  exact _root_.PositivityTheory.SiegelWeilFormula.Act.C1.phz_leftInv_k d hf z (L.j p) ⟨_root_.PositivityTheory.SiegelWeilFormula.Act.C1.j_par_k L hp.1, _root_.PositivityTheory.SiegelWeilFormula.Act.C1.j_rat_k L hp.2⟩ _
end PositivityTheory.SiegelWeilFormula.Act.C1
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Atop
open PositivityTheory.SiegelWeilFormula.KMain
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
def _root_.PositivityTheory.SiegelWeilFormula.RD_k.gens {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (s : Finset (InfinitePlace F)) : Set (Mx F E d.m d.n → ℂ) :=
  {f | ∃ (P : InfinitePlace F → PX d.m d.n) (g : (Fin d.m × Fin d.n × Fin 2 → Af F) → ℂ), (∀ w ∉ s, P w = 1) ∧ g ∈ SB _ ∧
    f = fun X => (∏ w, fP (P w) (R.loc w X)) * g fun k => (d.crd X k).2}
def _root_.PositivityTheory.SiegelWeilFormula.RD_k.vacOn {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (s : Finset (InfinitePlace F)) : Submodule ℂ (Mx F E d.m d.n → ℂ) :=
  Submodule.span ℂ (R.gens s)
theorem vacOn_empty_le_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) : R.vacOn ∅ ≤ R.vac := by
  refine Submodule.span_le.2 ?_
  rintro f ⟨P, g, hP, hg, rfl⟩
  refine Submodule.subset_span ⟨g, hg, ?_⟩
  funext X
  simp only [hP _ (Finset.notMem_empty _)]
theorem fock_le_vacOn_univ_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) : R.fock ≤ R.vacOn Finset.univ := by
  refine Submodule.span_le.2 ?_
  rintro f ⟨P, g, hg, rfl⟩
  exact Submodule.subset_span ⟨P, g, fun w hw => absurd (Finset.mem_univ w) hw, hg, rfl⟩
theorem vacOn_step_k (hG : AbsSt.GenCore) (c : ℂ) (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hAux : _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties) (hFM : _root_.PositivityTheory.SiegelWeilFormula.FockMem_k) (hLE : _root_.PositivityTheory.SiegelWeilFormula.LiftEx_k)
    (hLo : _root_.PositivityTheory.SiegelWeilFormula.LocOpEx_k) (hLI : _root_.PositivityTheory.SiegelWeilFormula.LocInst_k) (hGS : _root_.PositivityTheory.SiegelWeilFormula.GSplit_k) (hGI : _root_.PositivityTheory.SiegelWeilFormula.GIinv_k) (hGD : _root_.PositivityTheory.SiegelWeilFormula.GIdil_k) (hPK : _root_.PositivityTheory.SiegelWeilFormula.PolyKFin_k) (hSK : _root_.PositivityTheory.SiegelWeilFormula.SecK_k)
    (hEW : _root_.PositivityTheory.SiegelWeilFormula.EisWk_k) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (s : Finset (InfinitePlace F)) (hw : w ∉ s)
    (ih : ∀ Φ ∈ d.sch, d.T Φ ∈ R.vacOn s → ∀ x,
      HolValueAt (fun z => d.eis (d.sec0 Φ) (s0 d.m d.n) z x) (s0 d.m d.n) (c * d.I Φ x)) :
    ∀ Φ ∈ d.sch, d.T Φ ∈ R.vacOn (insert w s) → ∀ x,
      HolValueAt (fun z => d.eis (d.sec0 Φ) (s0 d.m d.n) z x) (s0 d.m d.n) (c * d.I Φ x) := by
  have hgen : ∀ f ∈ R.gens (insert w s), ∃ Φf : d.Fn, d.KFin Φf ∧ d.T Φf = f ∧ ∀ x,
      HolValueAt (fun z => d.eis (d.sec0 Φf) (s0 d.m d.n) z x) (s0 d.m d.n) (c * d.I Φf x) := by
    rintro f ⟨P, g, hP, hg, rfl⟩
    set Ψ : Mx F E d.m d.n → ℂ := fun X => (∏ w' ∈ Finset.univ.erase w, fP (P w') (R.loc w' X)) *
      g fun k => (d.crd X k).2 with hΨdef
    have hΨ : Ψ ∈ R.away w := Submodule.subset_span ⟨P, g, hg, rfl⟩
    obtain ⟨φ, hφ⟩ := hLE F E σ d R w Ψ hΨ
    have hTP : ∀ Q : PX d.m d.n, d.T (φ Q) = fun X => (∏ w', fP (Function.update P w Q w') (R.loc w' X)) *
        g fun k => (d.crd X k).2 := by
      intro Q
      rw [(hφ Q).2]
      funext X
      simp only [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, hΨdef]
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ w), Function.update_self, mul_assoc]
      congr 2
      refine Finset.prod_congr rfl fun w' hw' => ?_
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hw')]
    have hfock : ∀ Q, d.T (φ Q) ∈ R.fock := fun Q => by
      rw [hTP Q]
      exact Submodule.subset_span ⟨_, g, hg, rfl⟩
    have hKF : ∀ Q, d.KFin (φ Q) := fun Q => hPK F E σ d R (φ Q) (hφ Q).1 (hfock Q)
    have hvac : ∀ x, HolValueAt (fun z => d.eis (d.sec0 (φ 1)) (s0 d.m d.n) z x) (s0 d.m d.n) (c * d.I (φ 1) x) := by
      refine ih (φ 1) (hφ 1).1 ?_
      rw [hTP 1]
      refine Submodule.subset_span ⟨Function.update P w 1, g, fun w' hw' => ?_, hg, rfl⟩
      by_cases e : w' = w
      · subst e; exact Function.update_self _ _ _
      · rw [Function.update_of_ne e]
        exact hP w' (by simp [e, hw'])
    refine ⟨φ (P w), hKF (P w), ?_, _root_.PositivityTheory.SiegelWeilFormula.Atop.genAt_k hG c hT hAux hFM hLo hLI hGS hGI hGD hPK hSK hEW d R w hΨ hφ hvac (P w)⟩
    rw [hTP (P w), Function.update_eq_self]
  intro Φ hΦ hTΦ x
  obtain ⟨k, a, f, hf⟩ := Submodule.mem_span_set'.1 hTΦ
  choose Φf hK hTf hI using fun i => hgen (f i).1 (f i).2
  have hΦeq : Φ = ∑ i, a i • Φf i := by
    have hmem : Φ - ∑ i, a i • Φf i ∈ d.sch :=
      d.sch.sub_mem hΦ (d.sch.sum_mem fun i _ => d.sch.smul_mem _ (hK i).1)
    refine sub_eq_zero.mp ((hT.1 F E σ d).2.2 _ hmem ?_)

    rw [← _root_.PositivityTheory.SiegelWeilFormula.KMain.Tl_apply_k, map_sub, map_sum]
    simp only [map_smul, _root_.PositivityTheory.SiegelWeilFormula.KMain.Tl_apply_k, hTf, hf, sub_self]
  rw [hΦeq]
  exact _root_.PositivityTheory.SiegelWeilFormula.Atop.ident_lincomb_k hT hSK hEW d c a Φf hK hI x
end PositivityTheory.SiegelWeilFormula.Atop
namespace PositivityTheory.SiegelWeilFormula
def VacAllOfC_k : Prop :=
  AbsSt.GenCore → _root_.PositivityTheory.SiegelWeilFormula.TAll_k → _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties → _root_.PositivityTheory.SiegelWeilFormula.FockMem_k → _root_.PositivityTheory.SiegelWeilFormula.LiftEx_k → _root_.PositivityTheory.SiegelWeilFormula.LocOpEx_k → _root_.PositivityTheory.SiegelWeilFormula.LocInst_k → _root_.PositivityTheory.SiegelWeilFormula.GSplit_k → _root_.PositivityTheory.SiegelWeilFormula.GIinv_k → _root_.PositivityTheory.SiegelWeilFormula.GIdil_k → _root_.PositivityTheory.SiegelWeilFormula.KFinPoly_k → _root_.PositivityTheory.SiegelWeilFormula.PolyKFin_k →
    _root_.PositivityTheory.SiegelWeilFormula.SecK_k → _root_.PositivityTheory.SiegelWeilFormula.EisWk_k → _root_.PositivityTheory.SiegelWeilFormula.VacAll_k
theorem Atop.vacAllOfC_k : _root_.PositivityTheory.SiegelWeilFormula.VacAllOfC_k := by
  intro hG hT hAux hFM hLE hLo hLI hGS hGI hGD hKP hPK hSK hEW F E _ _ _ _ _ σ d R c hV Φ hΦ x
  have claim : ∀ s : Finset (InfinitePlace F), ∀ Φ ∈ d.sch, d.T Φ ∈ R.vacOn s → ∀ x,
      HolValueAt (fun z => d.eis (d.sec0 Φ) (s0 d.m d.n) z x) (s0 d.m d.n) (c * d.I Φ x) := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact fun Φ hΦ hT x => hV Φ hΦ (_root_.PositivityTheory.SiegelWeilFormula.Atop.vacOn_empty_le_k R hT) x
    | insert w s hw ih => exact _root_.PositivityTheory.SiegelWeilFormula.Atop.vacOn_step_k hG c hT hAux hFM hLE hLo hLI hGS hGI hGD hPK hSK hEW d R w s hw ih
  exact claim Finset.univ Φ hΦ.1 (_root_.PositivityTheory.SiegelWeilFormula.Atop.fock_le_vacOn_univ_k R (hKP F E σ d R Φ hΦ)) x
end PositivityTheory.SiegelWeilFormula
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
namespace RD
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F)
theorem _root_.PositivityTheory.SiegelWeilFormula.RD_k.stepW_pf (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hA : _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties) : ∀ (ε : ℤˣ) (w₀ : d.G), d.IsW ε w₀ →
    ∃ (C s : ℂ) (B : d.MF → d.MF), s ≠ 0 ∧ R.StepOK w w₀ (fun f u => C * ∫ v : Fin d.m → Fin d.n → ℂ,
      Complex.exp (2 * Real.pi * Complex.I * ((s * Matrix.trace ((Matrix.of u)ᴴ * Matrix.of v)).re : ℂ)) * f v) B := by
  intro ε w₀ hw
  obtain ⟨⟨ν, hν⟩, -, -⟩ := hA F E σ d
  obtain ⟨C, μ', -, -, hfact⟩ := _root_.PositivityTheory.SiegelWeilFormula.KFock.intFact_k F E σ d R w ν hν
  have hs : (-2 * ((ε : ℤ) : ℂ) * ((R.sg w : ℤ) : ℂ) / R.ζ) ≠ 0 := by
    refine div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) ?_) ?_) (_root_.PositivityTheory.SiegelWeilFormula.KW.zeta_ne_k R)
    · exact Int.cast_ne_zero.mpr (Units.ne_zero ε)
    · exact Int.cast_ne_zero.mpr (Units.ne_zero (R.sg w))
  refine ⟨(C : ℂ), _, fun Ψ X => ∫ Z, d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram X Z.1)) * Ψ Z.1 ∂μ', hs,
    fun f hf => KW.locFT_sw _ _ hs f hf, fun Ψ hΨ => ⟨?_, ?_⟩⟩
  · intro X Z hZ1 hZ2
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun Z₀ => ?_)
    simp only
    rw [_root_.PositivityTheory.SiegelWeilFormula.KW.psi_add_left_k, _root_.PositivityTheory.SiegelWeilFormula.KW.gram_supp_cmp_k d w ⟨hZ1, hZ2⟩ Z₀.2, _root_.PositivityTheory.SiegelWeilFormula.KW.psi_zero_gram_k, mul_one]
  · intro f hf Φ hΦ hTΦ
    funext X
    rw [hT.2.2.1 F E σ d ν hν ε w₀ hw Φ hΦ X, hTΦ]
    let Ψ' : Mx F E d.m d.n → ℂ := fun Z =>
      d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram X (Z - _root_.PositivityTheory.SiegelWeilFormula.KW.insL_k R w (R.loc w Z)))) * Ψ Z
    have hΨ' : ∀ X' Z, (∀ w', w' ≠ w → d.cw w' Z = 0) → finOne F • Z = 0 → Ψ' (X' + Z) = Ψ' X' := by
      intro X' Z hZ1 hZ2
      simp only [Ψ']
      rw [_root_.PositivityTheory.SiegelWeilFormula.KW.rest_inv_k R w X' Z ⟨hZ1, hZ2⟩, hΨ X' Z hZ1 hZ2]
    have e : (fun Z => d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram X Z)) * R.tens w f Ψ Z) =
        R.tens w (fun u => d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram X (_root_.PositivityTheory.SiegelWeilFormula.KW.insL_k R w u))) * f u) Ψ' := by
      funext Z
      simp only [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, Ψ']
      have h := _root_.PositivityTheory.SiegelWeilFormula.KW.psi_add_right_k d ε X (_root_.PositivityTheory.SiegelWeilFormula.KW.insL_k R w (R.loc w Z)) (Z - _root_.PositivityTheory.SiegelWeilFormula.KW.insL_k R w (R.loc w Z))
      rw [add_sub_cancel] at h
      rw [h]
      ring
    rw [e]
    erw [hfact _ Ψ' hΨ']
    have e2 : ∫ Z, Ψ' Z.1 ∂μ' = ∫ Z, d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram X Z.1)) * Ψ Z.1 ∂μ' := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun Z => ?_)
      simp only [Ψ']
      rw [_root_.PositivityTheory.SiegelWeilFormula.KFock.loc_of_mem_k d R w Z.2, _root_.PositivityTheory.SiegelWeilFormula.KW.insL_zero_k, sub_zero]
    rw [e2]
    simp only [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, _root_.PositivityTheory.SiegelWeilFormula.KW.kernel_k R w ε X]
end RD
end PositivityTheory.SiegelWeilFormula
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
namespace RD
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F)
theorem _root_.PositivityTheory.SiegelWeilFormula.RD_k.frame_nU (y : GR d.n) (b : Matrix (Fin d.n) (Fin d.n) ℂ) (hy : mR y = nU b) :
    inFrame d.b (R.ι w y) = Matrix.fromBlocks 1 (inFrame d.b (R.ι w y)).toBlocks₁₂ 0 1 ∧
    d.cw w (inFrame d.b (R.ι w y)).toBlocks₁₂ = R.ζ • b ∧
    (∀ w', w' ≠ w → d.cw w' (inFrame d.b (R.ι w y)).toBlocks₁₂ = 0) ∧ finOne F • (inFrame d.b (R.ι w y)).toBlocks₁₂ = 0 := by
  have hζ0 : R.ζ ≠ 0 := Krd.zeta_ne R.hζ
  set M := inFrame d.b (R.ι w y) with hM
  have hw : d.cw w M = nU (R.ζ • b) := by rw [hM, R.cw_iota_pf w y, hy, dZ_conj_nU hζ0]
  have ho : ∀ w', w' ≠ w → d.cw w' M = 1 := fun w' h => R.off_w w w' y h
  have hf : finOne F • M = finOne F • 1 := R.off_f w y
  have o1 := one_blocks (n := d.n) (1 : ℂ)
  have of := one_blocks (n := d.n) (finOne F • (1 : AE F E))
  simp only [one_smul] at o1
  have hf' : finOne F • M = (finOne F • (1 : AE F E)) • (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) := by
    rw [hf, smul_one_smul]
  have e11 : M.toBlocks₁₁ = 1 := by
    apply _root_.PositivityTheory.SiegelWeilFormula.Place.cw_ext_k d
    · intro w'
      rw [_root_.PositivityTheory.SiegelWeilFormula.Krd.cw_one_k d]
      show (d.cw w' M).toBlocks₁₁ = 1
      by_cases h : w' = w
      · rw [h, hw]; simp [nU]
      · rw [ho w' h]; exact o1.1
    · show (finOne F • M).toBlocks₁₁ = _
      rw [hf', of.1, smul_one_smul]
  have e21 : M.toBlocks₂₁ = 0 := by
    apply _root_.PositivityTheory.SiegelWeilFormula.Place.cw_ext_k d
    · intro w'
      rw [show d.cw w' (0 : Matrix (Fin d.n) (Fin d.n) (AE F E)) = 0 from Matrix.map_zero _ (map_zero _)]
      show (d.cw w' M).toBlocks₂₁ = 0
      by_cases h : w' = w
      · rw [h, hw]; simp [nU]
      · rw [ho w' h]; exact o1.2.2.1
    · show (finOne F • M).toBlocks₂₁ = _
      rw [hf', of.2.2.1, smul_zero]
  have e22 : M.toBlocks₂₂ = 1 := by
    apply _root_.PositivityTheory.SiegelWeilFormula.Place.cw_ext_k d
    · intro w'
      rw [_root_.PositivityTheory.SiegelWeilFormula.Krd.cw_one_k d]
      show (d.cw w' M).toBlocks₂₂ = 1
      by_cases h : w' = w
      · rw [h, hw]; simp [nU]
      · rw [ho w' h]; exact o1.2.2.2
    · show (finOne F • M).toBlocks₂₂ = _
      rw [hf', of.2.2.2, smul_one_smul]
  refine ⟨?_, ?_, ?_, ?_⟩
  · conv_lhs => rw [← Matrix.fromBlocks_toBlocks M]
    rw [e11, e21, e22]
  · show (d.cw w M).toBlocks₁₂ = _
    rw [hw]; simp [nU]
  · intro w' h
    show (d.cw w' M).toBlocks₁₂ = _
    rw [ho w' h]; exact o1.2.1
  · show (finOne F • M).toBlocks₁₂ = _
    rw [hf', of.2.1]
theorem _root_.PositivityTheory.SiegelWeilFormula.RD_k.stepN_pf (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) : ∀ (y : GR d.n) (b : Matrix (Fin d.n) (Fin d.n) ℂ), bᴴ = b → mR y = nU b →
    R.StepOK w (R.ι w y) (fun f u => Complex.exp (2 * Real.pi * Complex.I * ((R.sg w : ℤ) : ℂ) *
      Matrix.trace (b * ((Matrix.of u)ᴴ * Matrix.of u))) * f u) id := by
  intro y b hb hy
  obtain ⟨hM, hβw, hβo, hβf⟩ := R.frame_nU w y b hy
  refine ⟨fun f hf => ?_, fun Ψ hΨ => ⟨hΨ, fun f hf Φ hΦ hTΦ => ?_⟩⟩
  · obtain ⟨φ, rfl⟩ := hf
    obtain ⟨ψ, hψ⟩ := GlobalTheory.T.schwartz_quadratic_phase_multiplication d.m d.n (((R.sg w : ℤ) : ℝ)) b hb φ
    refine ⟨ψ, ?_⟩
    rw [hψ]
    funext u
    push_cast
    rfl
  · funext X
    rw [(hT.2.1 F E σ d Φ hΦ).1 (R.ι w y) _ hM X, R.psi_nU w b hb _ hβw hβo hβf X, hTΦ]
    simp only [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, id]
    ring
end RD
end PositivityTheory.SiegelWeilFormula
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
set_option linter.unusedSimpArgs false
namespace PositivityTheory.SiegelWeilFormula.Act.C4
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d)
namespace Bq
theorem inStabilizer_parabolic_mul {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) {p γ : d.G} (hp : p ∈ par2 σ d.Y) (hγ : _root_.PositivityTheory.SiegelWeilFormula.Act.FirstOrbit L γ) : _root_.PositivityTheory.SiegelWeilFormula.Act.FirstOrbit L (p * γ) := by
  intro i
  have hP := (ComplexParameterFamilyContinuity.mem_stabiliser_iff_frame_lower_block d.ok.frame p).1 hp
  have e1 : ∀ j, inFrame d.b p (Sum.inr i) (Sum.inl j) = 0 := fun j => by
    have := congrFun (congrFun hP i) j
    simpa [Matrix.toBlocks₂₁] using this
  rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, Matrix.mul_apply, Fintype.sum_sum_type]
  simp [e1, hγ _]
theorem inStabilizer_smallerGroupEmbed {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (g : G2 σ L.Y) : _root_.PositivityTheory.SiegelWeilFormula.Act.FirstOrbit L (L.j g) := by
  intro i
  exact (L.j_out g (Sum.inl L.i₀) (by simp) (Sum.inr i)).2.trans (by simp [Matrix.one_apply])
theorem par_of_j_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) {g : G2 σ L.Y} (h : L.j g ∈ par2 σ d.Y) : g ∈ par2 σ L.Y := by
  rw [ComplexParameterFamilyContinuity.mem_stabiliser_iff_frame_lower_block L.ok.frame]
  rw [ComplexParameterFamilyContinuity.mem_stabiliser_iff_frame_lower_block d.ok.frame, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.inFrame_j_k] at h
  refine Matrix.ext fun a c => ?_
  have h1 := congrFun (congrFun h (L.em a)) (L.em c)
  have h2 := _root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_emS_k L (inFrame L.b g) (Sum.inr a) (Sum.inl c)
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k, Sum.map_inr, Sum.map_inl] at h2
  simp only [Matrix.toBlocks₂₁, Matrix.of_apply, Matrix.zero_apply] at h1 ⊢
  rw [← h2]
  exact h1
end Bq
end PositivityTheory.SiegelWeilFormula.Act.C4
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Ald
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
def ChartFacts_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (n : ℕ) (h : n + 1 = d.n) (Y : Spc F E n) (b : GL (Fin n ⊕ Fin n) E)
  (j : G2 σ Y →* d.G) (ε : ℤˣ), 1 ≤ n → _root_.PositivityTheory.SiegelWeilFormula.Ald.SignOK_k d Y → IsFrame2 σ Y b →
  d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = jeps d.n ε → b.1ᵀ * dbl Y.J * b.1.map σ = jeps n ε → _root_.PositivityTheory.SiegelWeilFormula.Ald.IsJ_k d h b j →
  ∀ (dd0 : Darboux (symp (R := AF F) (cA σ) (-1) (incM F d.A.J) (dbl (incM F d.Y.J))) (Fin d.m × Fin d.n × Fin 2))
    (dd' : Darboux (symp (R := AF F) (cA σ) (-1) (incM F d.A.J) (dbl (incM F Y.J))) (Fin d.m × Fin n × Fin 2)),
    IsAdapted d.bs d.A d.Y d.b dd0 → IsAdapted d.bs d.A Y b dd' →
    (∀ w', (GlobalTheory.TowU.reindexD dd0 (eK d.m h).symm).e (emb h b d.b w') =
      (Sum.elim (dd'.e w').1 (0 : Fin d.m × Fin 2 → AF F), Sum.elim (dd'.e w').2 (0 : Fin d.m × Fin 2 → AF F))) ∧
    (∀ u v : Fin d.m × Fin 2 → AF F, ∃ w, (GlobalTheory.TowU.reindexD dd0 (eK d.m h).symm).e w =
      (Sum.elim (0 : Fin d.m × Fin n × Fin 2 → AF F) u, Sum.elim (0 : Fin d.m × Fin n × Fin 2 → AF F) v)) ∧
    (∀ g w, ((GlobalTheory.TowU.reindexD dd0 (eK d.m h).symm).e w).1 ∘ Sum.inl = 0 →
      ((GlobalTheory.TowU.reindexD dd0 (eK d.m h).symm).e w).2 ∘ Sum.inl = 0 → actB (cA σ) (j g) w = w) ∧
    (∀ g (w' : Matrix (Fin d.m) (Fin n ⊕ Fin n) (AE F E)), actB (cA σ) (j g) (emb h b d.b w') = emb h b d.b (actB (cA σ) g w')) ∧
    ∀ (u : UA σ d.A.J) (w' : Matrix (Fin d.m) (Fin n ⊕ Fin n) (AE F E)), mat u * emb h b d.b w' = emb h b d.b (mat u * w')
end PositivityTheory.SiegelWeilFormula.Ald
end
end
end
