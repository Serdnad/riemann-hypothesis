module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle177
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle522
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle216
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1230
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle512
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle236
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RealSmulSplit
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.RowHighestLeSpanColWordComplex
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle298
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FockPolynomialVectorTestThetaZeroEqThetaSeries
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaKernelOrthonormalFrameInDomainPeriodLinear
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle318
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle264
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle038
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle358
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle520
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle386
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle411
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle523
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle476
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle525
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.MatchingAdjoints
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle333
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle468
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.VacTransfer

theorem _root_.GlobalTheory.T.archimedeanHeisenbergLine_continuous_finite_zero : ∀ (D : D7) (S X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d) (g : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
    (cS : Matrix (Fin S.rank) (Fin d) (AE D) ≃+ WO S X),
    (∀ u, cS u = (HMul.hMul (uᵀ.submatrix e id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM g) : Matrix (Fin X.rank) (Fin S.rank) (AE D))) →
    ∀ u : Matrix (Fin S.rank) (Fin d) (AE D),
      Continuous (GlobalTheory.VacTransfer.archLine cS u) ∧ ∀ t, (GlobalTheory.VacTransfer.archLine cS u t).map (finPart D) = 0 := by
  first | exact @GlobalTheory.ArchLineCont.archLine_continuous_finPart | exact GlobalTheory.ArchLineCont.archLine_continuous_finPart | (intros; apply GlobalTheory.ArchLineCont.archLine_continuous_finPart <;> assumption)
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open GlobalTheory.ArchUniq MeasureTheory Filter Topology
open scoped SchwartzMap Classical Matrix

noncomputable section

namespace GlobalTheory.ArchLinePair

theorem acts_of_comm {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ)
    (T : Module.End ℂ ((κ → AF F) → ℂ)) (hpres : ∀ Φ ∈ schA F κ, T Φ ∈ schA F κ)
    (hcomm : ∀ u : AF F, evI F u = 0 → ∀ p q : κ → AF F, ∀ Φ ∈ schA F κ,
      T (schr ψ (u • p, u • q) Φ) = schr ψ (u • p, u • q) (T Φ)) (f : SInf F κ) :
    ∃ f₁ : SInf F κ, Acts (evI F) T f f₁ := by
  obtain ⟨r₀, hr₀1, hr₀⟩ := GlobalTheory.ArchLocality.ref_fun (F := F) κ
  have hΦ₀ : tens (evI F) (⇑f) r₀ ∈ schA F κ := (hr₀ f).2
  obtain ⟨f₁, hf₁⟩ := GlobalTheory.ArchLocality.res_arch _ (hpres _ hΦ₀)
  refine ⟨f₁, fun r hr => funext fun y => ?_⟩
  set u : AF F := (0, 1) with hu_def
  have hu : evI F u = 0 := GlobalTheory.ArchLocality.evI_fin
  have hmul : ∀ a : AF F, u * a = (0, a.2) := fun a => Prod.ext (zero_mul _) (one_mul _)
  set ya : κ → AF F := fun i => ((y i).1, 0) with hya
  have hy : ∀ i, y i = ya i + u * y i := fun i => by
    rw [hmul]
    exact Prod.ext (add_zero _).symm (zero_add _).symm

  have hτx : ∀ (Φ : (κ → AF F) → ℂ) x, schr ψ (u • y, u • (0 : κ → AF F)) Φ x = Φ (x + u • y) := fun Φ x => by
    simp only [schr, smul_zero, dotProduct_zero, mul_zero, add_zero, AddChar.map_zero_eq_one, one_mul]
  have step1 : T (tens (evI F) ⇑f r) y = T (schr ψ (u • y, u • (0 : κ → AF F)) (tens (evI F) ⇑f r)) ya := by
    have e : ya + u • y = y := funext fun i => (hy i).symm
    rw [hcomm u hu y 0 _ hr.2, hτx, e]
  have hmemτ : schr ψ (u • y, u • (0 : κ → AF F)) (tens (evI F) ⇑f r) ∈ schA F κ := by
    have e : schr ψ (u • y, u • (0 : κ → AF F)) (tens (evI F) ⇑f r) = fun x => tens (evI F) ⇑f r (x + u • y) :=
      funext fun x => hτx _ x
    rw [e]
    exact GlobalTheory.SchwartzTranslate.schA_translate F (u • y) hr.2
  have hΨ : schr ψ (u • y, u • (0 : κ → AF F)) (tens (evI F) ⇑f r) - r y • tens (evI F) ⇑f r₀ ∈ schA F κ :=
    Submodule.sub_mem _ hmemτ (Submodule.smul_mem _ _ hΦ₀)
  have hvan : ∀ z, At (evI F) z →
      (schr ψ (u • y, u • (0 : κ → AF F)) (tens (evI F) ⇑f r) - r y • tens (evI F) ⇑f r₀) (ya + z) = 0 := by
    intro z hz
    have hz2 : ∀ i, (z i).2 = 0 := GlobalTheory.ArchLocality.snd_eq_zero_of_at hz
    have e1 : ya + z + u • y = y + z := by
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      conv_rhs => rw [hy i]
      abel
    have e2 : (fun i => evI F ((ya + z) i)) = fun i => evI F ((y + z) i) := rfl
    have e3 : r₀ (ya + z) = 1 := hr₀1 _ fun i => by
      show (0 : FiniteAdeleRing (𝓞 F) F) + (z i).2 = 0
      rw [hz2 i, add_zero]
    rw [Pi.sub_apply, Pi.smul_apply, hτx, e1]
    simp only [tens]
    rw [hr.1 y z hz, e2, e3, smul_eq_mul]
    ring
  have hfib := GlobalTheory.ArchLocality.fibre ψ hψ T hcomm _ hΨ ya hvan
  rw [map_sub, map_smul, Pi.sub_apply, Pi.smul_apply, sub_eq_zero, smul_eq_mul] at hfib
  have hya' : ya = fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (evI F (y i)), 0) := by
    funext i
    simp only [hya, evI, RingEquiv.symm_apply_apply]
  have hf₁' := hf₁ (fun i => evI F (y i))
  rw [step1, hfib, hya', hf₁']
  simp only [tens]
  ring

private theorem hTens_eq_trace_twisted_operators {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E) {α β : Type}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] (JA : Matrix α α E) (JB : Matrix β β E) (x y : Matrix α β E) :
    hTens c JA JB x y = Matrix.trace (xᵀ * (JA * y.map c * JBᵀ)) := by
  simp only [hTens, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

private theorem map_mul_lemma_2 {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E) {α β γ : Type}
    [Fintype β] (A : Matrix α β E) (B : Matrix β γ E) : (A * B).map c = A.map c * B.map c :=
  Matrix.map_mul (f := c.toRingHom)

theorem hTens_actAB {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E) {α β : Type} [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] {JA : Matrix α α E} {JB : Matrix β β E} (p : UG c JA × UG c JB)
    (x y : Matrix α β E) : hTens c JA JB (actAB c p x) (actAB c p y) = hTens c JA JB x y := by
  obtain ⟨⟨G, hG⟩, ⟨H, hH⟩⟩ := p
  have hG' : (G : Matrix α α E)ᵀ * JA * (G : Matrix α α E).map c = JA := hG
  have hH' : (H : Matrix β β E)ᵀ * JB * (H : Matrix β β E).map c = JB := hH
  have hG2 : ∀ N : Matrix α β E, (G : Matrix α α E)ᵀ * (JA * ((G : Matrix α α E).map c * N)) = JA * N :=
    fun N => by simpa only [Matrix.mul_assoc] using congrArg (· * N) hG'
  have hH2 : ((H : Matrix β β E).map c)ᵀ * (JBᵀ * (H : Matrix β β E)) = JBᵀ := by
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc] using congrArg Matrix.transpose hH'
  simp only [actAB, hTens_eq_trace_twisted_operators, map_mul_lemma_2, Matrix.transpose_map, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc, hG2, hH2]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

theorem actAB_smul (p : UA σ X.J × UA σ W.J) (u : AF F) (w : Matrix (Fin n) (Fin d) (AE F E)) :
    actAB (cA σ) p (u • w) = u • actAB (cA σ) p w := by
  simp only [actAB, Matrix.mul_smul, Matrix.smul_mul]

theorem actAB_add (p : UA σ X.J × UA σ W.J) (w w' : Matrix (Fin n) (Fin d) (AE F E)) :
    actAB (cA σ) p (w + w') = actAB (cA σ) p w + actAB (cA σ) p w' := by
  simp only [actAB, Matrix.mul_add, Matrix.add_mul]

theorem actAB_mul (p q : UA σ X.J × UA σ W.J) (w : Matrix (Fin n) (Fin d) (AE F E)) :
    actAB (cA σ) (p * q) w = actAB (cA σ) p (actAB (cA σ) q w) := by
  simp only [actAB, Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul, Units.val_mul, Matrix.transpose_mul, Matrix.mul_assoc]

theorem actAB_one (w : Matrix (Fin n) (Fin d) (AE F E)) : actAB (cA σ) (1 : UA σ X.J × UA σ W.J) w = w := by
  simp only [actAB, Prod.fst_one, Prod.snd_one, OneMemClass.coe_one, Units.val_one, Matrix.transpose_one, Matrix.one_mul,
    Matrix.mul_one]

theorem actAB_fin {p : UA σ X.J × UA σ W.J} (h1 : p.1 ∈ UAt σ X (evI F)) (h2 : p.2 ∈ UAt σ W (evI F)) (u : AF F)
    (hu : evI F u = 0) (w : Matrix (Fin n) (Fin d) (AE F E)) : actAB (cA σ) p (u • w) = u • w := by
  have e1 : u • mat p.1 = u • (1 : Matrix (Fin n) (Fin n) (AE F E)) := by
    have h := h1 u hu
    rwa [smul_sub, sub_eq_zero] at h
  have e2 : u • mat p.2 = u • (1 : Matrix (Fin d) (Fin d) (AE F E)) := by
    have h := h2 u hu
    rwa [smul_sub, sub_eq_zero] at h
  simp only [mat] at e1 e2
  simp only [actAB]
  rw [Matrix.mul_smul, ← Matrix.smul_mul, e1, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul, ← Matrix.mul_smul,
    ← Matrix.transpose_smul, e2, Matrix.transpose_smul, Matrix.transpose_one, Matrix.mul_smul, Matrix.mul_one]

def amap (M : Model σ X W) (p : UA σ X.J × UA σ W.J) :
    ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) →ₗ[ℝ]
      ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) where
  toFun v := Coord.coordI M (actAB (cA σ) p (GlobalTheory.ArchFam.wv M v))
  map_add' v v' := by
    simp only [GlobalTheory.ArchFam.wv, Prod.fst_add, Prod.snd_add, Coord.lift_add, ← Prod.mk_add_mk, map_add (f := _), actAB_add,
      Coord.coordI_add]
  map_smul' c v := by
    simp only [GlobalTheory.ArchFam.wv, Prod.smul_fst, Prod.smul_snd, Coord.lift_smul, ← Prod.smul_mk, map_smul, actAB_smul,
      Coord.coordI_smul, RingHom.id_apply]

theorem amap_coordI (M : Model σ X W) (p : UA σ X.J × UA σ W.J) (w : Matrix (Fin n) (Fin d) (AE F E)) :
    amap M p (Coord.coordI M w) = Coord.coordI M (actAB (cA σ) p w) := by
  simp only [amap, LinearMap.coe_mk, AddHom.coe_mk, GlobalTheory.ArchFam.wv]
  rw [Coord.lift_coordI, actAB_smul, Coord.coordI_one]

theorem continuous_amap (M : Model σ X W) (v) : Continuous fun p : UA σ X.J × UA σ W.J => amap M p v := by
  have : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) (AE F E)
  have : IsModuleTopology (AF F) (Matrix (Fin n) (Fin d) (AE F E)) :=
    (inferInstance : IsModuleTopology (AF F) (Fin n → Fin d → AE F E))
  have hev : Continuous (evI F) := by
    show Continuous fun a : AF F => InfiniteAdeleRing.ringEquiv_mixedSpace F a.1
    simp only [InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
    refine Continuous.prodMk (continuous_pi fun w => ?_) (continuous_pi fun w => ?_)
    · exact (NumberField.InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal w.2).continuous.comp
        ((continuous_apply _).comp continuous_fst)
    · exact (NumberField.InfinitePlace.Completion.isometry_extensionEmbedding w.1).continuous.comp
        ((continuous_apply _).comp continuous_fst)
  have hloc : Continuous fun x : Fin n × Fin d → AF F => locV x :=
    continuous_pi fun i => hev.comp (continuous_apply i)
  have he : Continuous fun u : Matrix (Fin n) (Fin d) (AE F E) => M.co.e u :=
    IsModuleTopology.continuous_of_linearMap M.co.e.toLinearMap
  have hg : Continuous fun p : UA σ X.J × UA σ W.J => ((p.1 : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) :=
    Units.continuous_val.comp (continuous_subtype_val.comp continuous_fst)
  have hh : Continuous fun p : UA σ X.J × UA σ W.J => ((p.2 : GL (Fin d) (AE F E)) : Matrix (Fin d) (Fin d) (AE F E)) :=
    Units.continuous_val.comp (continuous_subtype_val.comp continuous_snd)
  have hact : Continuous fun p : UA σ X.J × UA σ W.J => actAB (cA σ) p (GlobalTheory.ArchFam.wv M v) :=
    (hg.matrix_mul continuous_const).matrix_mul hh.matrix_transpose
  simp only [amap, LinearMap.coe_mk, AddHom.coe_mk, Coord.coordI]
  exact (hloc.comp (continuous_fst.comp (he.comp hact))).prodMk (hloc.comp (continuous_snd.comp (he.comp hact)))

end GlobalTheory.ArchLinePair
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdSpan.StableFock

theorem revB_isB : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (B₀ : C.Bas), C.IsB B₀ → C.IsB (revB C.X.p0 B₀) ∧ C.sB (revB C.X.p0 B₀) = C.sB B₀ := by
  intro D S T C B₀ hB₀
  let σ : Equiv.Perm (Fin T.rank) := Function.Involutive.toPerm (revPos C.X.p0) (revPos_revPos C.X.p0)
  have hσ : ∀ τ, revB C.X.p0 B₀ τ = (B₀ τ).submatrix id σ := fun τ => rfl
  have hsg : ∀ a : Fin T.rank, sgn C.X.p0 ((σ a : Fin T.rank) : ℕ) = sgn C.X.p0 (a : ℕ) := by
    intro a
    show sgn C.X.p0 ((revPos C.X.p0 a : Fin T.rank) : ℕ) = _
    unfold revPos
    split_ifs with h
    · simp only [sgn, if_pos h.1, if_pos (show C.X.p0 - 1 - (a : ℕ) < C.X.p0 by omega)]
    · rfl
  have hD : (sgnM C.X).submatrix σ σ = sgnM C.X := by
    unfold sgnM
    rw [Matrix.submatrix_diagonal _ _ σ.injective]
    congr 1
    funext a
    simp only [Function.comp_apply, hsg]
  have hD' : ∀ M : Matrix (Fin T.rank) (Fin T.rank) ℂ, M.submatrix id σ * sgnM C.X = (M * sgnM C.X).submatrix id σ := by
    intro M
    ext i j
    simp only [sgnM, Matrix.mul_diagonal, Matrix.submatrix_apply, id, hsg]
  refine ⟨fun τ => ?_, funext fun τ => ?_⟩
  · rw [hσ, Matrix.conjTranspose_submatrix, ← Matrix.submatrix_id_id (gramAt D T τ),
      ← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, ← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, hB₀ τ, hD]
  · show (revB C.X.p0 B₀ τ) * sgnM C.X * (revB C.X.p0 B₀ τ)⁻¹ = B₀ τ * sgnM C.X * (B₀ τ)⁻¹
    rw [hσ, hD', show (B₀ τ).submatrix id σ = (B₀ τ).submatrix (Equiv.refl _) σ from rfl,
      Matrix.inv_submatrix_equiv, show (B₀ τ * sgnM C.X).submatrix id σ = (B₀ τ * sgnM C.X).submatrix (Equiv.refl _) σ from rfl,
      Matrix.submatrix_mul_equiv]
    rfl

theorem pureTensorO_revB : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (B₀ : C.Bas), C.IsB B₀ → ∀ (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (f : WO S T → ℂ), C.IsTh f → ∀ P : MvPolynomial (FVar D T.rank S.rank) ℂ, pureTensorO C.ψ C.θ S T (fun _ => 1) (C.sB B₀) BS B₀ f P = pureTensorO C.ψ C.θ S T (fun _ => 1) (C.sB B₀) BS (revB C.X.p0 B₀) f (MvPolynomial.rename (fun v : FVar D T.rank S.rank => (v.1, revPos C.X.p0 v.2.1, v.2.2)) P) := by
  intro D S T C B₀ hB₀ BS f hf P
  have hS : ∀ τ, IsCartanInv (gramAt D S τ) 1 := by
    intro τ
    have e : gramAt D S τ = 1 := by simp [gramAt, C.m.gS]
    rw [e]
    refine ⟨by simp, by simp, ?_⟩
    simpa using Matrix.PosDef.one
  have hT := fun τ => (((GlobalTheory.Ker.onBasis_frame_period D S T C).2 B₀ hB₀).2.2.1 τ).1
  have := GlobalTheory.OneMapRef.IoCmp.pureTensorO_rename C.std C.inf hS hT hf BS B₀ (revB C.X.p0 B₀)
    (fun _ => revPos C.X.p0) (fun τ => rfl) (fun v : FVar D T.rank S.rank => v.1)
    (fun v => revPos C.X.p0 v.2.1) (fun v => v.2.2) P
  simp only [revPos_revPos] at this
  rw [← this]
  have e : (MvPolynomial.rename fun k : FVar D T.rank S.rank => (k.1, k.2.1, k.2.2)) P = P := by
    change MvPolynomial.rename id P = P
    exact MvPolynomial.rename_id_apply P
  rw [e]

theorem pureTensorO_source : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ), (∀ τ, (BS τ)ᴴ * BS τ = 1) → ∃ u : C.X.Ψ → GL (Fin S.rank) ℂ, (∀ σ, (u σ : Matrix (Fin S.rank) (Fin S.rank) ℂ) ∈ Matrix.unitaryGroup (Fin S.rank) ℂ) ∧ ∀ Q Q' : MvPolynomial (FVar D T.rank S.rank) ℂ, C.toH Q' = Harm.colActHom u (C.toH Q) → ∀ B, C.IsB B → ∀ f, C.IsTh f → pureTensorO C.ψ C.θ S T (fun _ => 1) (C.sB B) BS B f Q = C.fvec B f Q' := by
  intro D S T C BS hBS
  obtain ⟨h, -, hh⟩ := GlobalTheory.T.exists_realPoint_standardSource_unitaryComponents D S T C BS hBS
  obtain ⟨u, hu, -, hcol⟩ := GlobalTheory.Ker.ColChange.col_change D S T C h
  refine ⟨u, hu, fun Q Q' hQ B hB f hf => ?_⟩
  have := hcol Q Q' hQ B hB f hf
  rwa [show (fun τ => compAt C.θ τ (mt S h)) = BS from funext hh] at this

theorem colU_surjective : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (u : C.X.Ψ → GL (Fin S.rank) ℂ), (∀ σ, (u σ : Matrix (Fin S.rank) (Fin S.rank) ℂ) ∈ Matrix.unitaryGroup (Fin S.rank) ℂ) → ∃ h ∈ GinfC S, GlobalTheory.Ker.ColChange.colU C h = u := by
  intro D S T C u hu
  have hv : ∀ τ, ((u (C.m.e τ) : Matrix (Fin S.rank) (Fin S.rank) ℂ).map conj)ᴴ *
      (u (C.m.e τ) : Matrix (Fin S.rank) (Fin S.rank) ℂ).map conj = 1 := by
    intro τ
    have hA := (Matrix.mem_unitaryGroup_iff').1 (hu (C.m.e τ))
    have e : ((u (C.m.e τ) : Matrix (Fin S.rank) (Fin S.rank) ℂ).map conj)ᴴ *
        (u (C.m.e τ) : Matrix (Fin S.rank) (Fin S.rank) ℂ).map conj =
        (star (u (C.m.e τ) : Matrix (Fin S.rank) (Fin S.rank) ℂ) *
          (u (C.m.e τ) : Matrix (Fin S.rank) (Fin S.rank) ℂ)).map conj := by
      ext i j

      simp [Matrix.mul_apply, Matrix.conjTranspose_apply, map_sum, Matrix.star_eq_conjTranspose]
    rw [e, hA]
    ext i j
    simp [Matrix.one_apply]
  obtain ⟨h, hh, hcomp⟩ := GlobalTheory.T.exists_realPoint_standardSource_unitaryComponents D S T C _ hv
  refine ⟨h, hh, funext fun σ => Units.ext ?_⟩
  show (compAt C.θ (C.m.e.symm σ) (mt S h)).map conj = (u σ : Matrix (Fin S.rank) (Fin S.rank) ℂ)
  rw [hcomp]
  ext i j
  simp

theorem fockSpan_rowHighest : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeak C.ψ S T om → T.rank ≤ S.rank → ∀ B₀, C.IsB B₀ → ∀ BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ, (∀ τ, (BS τ)ᴴ * BS τ = 1) → ∀ f, C.IsTh f → C.IsFock B₀ f → f ≠ 0 → ∀ (p q : D.what₂.Tau → ℕ) (ap am : D.what₂.Tau → ℕ → ℕ), (∀ τ, p τ = C.X.p0) → (∀ τ, q τ = C.q0) → ∀ (pt : MvPolynomial (FVar D T.rank S.rank) ℂ → WO S T → ℂ) (U : Submodule ℂ (MvPolynomial (FVar D T.rank S.rank) ℂ)), (∀ P, pt P = pureTensorO C.ψ C.θ S T (fun _ => 1) (C.sB B₀) BS B₀ f P) → Formalism.IndefR.Datum.delta p q ap am ∈ U → (∀ h ∈ GinfC S, ∀ P ∈ U, ∃ P' ∈ U, om (h, 1) (pt P) = pt P') → C.IsB (revB C.X.p0 B₀) ∧ C.sB (revB C.X.p0 B₀) = C.sB B₀ ∧ ∃ (c : C.X.Ψ → Fin C.q0 → ℕ) (c' : C.X.Ψ → Fin C.X.p0 → ℕ) (Q₀ : MvPolynomial (FVar D T.rank S.rank) ℂ), C.toH Q₀ ∈ Harm.rowHighest ℂ c c' ∧ C.fvec (revB C.X.p0 B₀) f Q₀ = pt (Formalism.IndefR.Datum.delta p q ap am) ∧ pt (Formalism.IndefR.Datum.delta p q ap am) ≠ 0 ∧ ∀ Q, C.toH Q ∈ Harm.rowHighest ℂ c c' → ∃ P ∈ U, C.fvec (revB C.X.p0 B₀) f Q = pt P := by
  intro D S T C om hom hrk B₀ hB₀ BS hBS f hf hF hf0 p q ap am hp hq pt U hpt hΔ hU
  obtain ⟨hB, hsB⟩ := revB_isB D S T C B₀ hB₀
  refine ⟨hB, hsB, ?_⟩
  have hFB : C.IsFock (revB C.X.p0 B₀) f := by
    intro τ
    rw [hsB]
    exact hF τ
  obtain ⟨u₀, -, hcol⟩ := pureTensorO_source D S T C BS hBS
  have hinj := C.toH_bijective.1
  have hsurj := C.toH_bijective.2
  have hpt' : ∀ P, ∃ Q, C.toH Q = Harm.colActHom u₀ (C.toH (MvPolynomial.rename
      (fun v : FVar D T.rank S.rank => (v.1, revPos C.X.p0 v.2.1, v.2.2)) P)) ∧
      C.fvec (revB C.X.p0 B₀) f Q = pt P := by
    intro P
    obtain ⟨Q, hQ⟩ := hsurj (Harm.colActHom u₀ (C.toH (MvPolynomial.rename
      (fun v : FVar D T.rank S.rank => (v.1, revPos C.X.p0 v.2.1, v.2.2)) P)))
    refine ⟨Q, hQ, ?_⟩
    rw [hpt, pureTensorO_revB D S T C B₀ hB₀ BS f hf P]
    have := hcol _ _ hQ (revB C.X.p0 B₀) hB f hf
    rw [hsB] at this
    exact this.symm
  obtain rfl : p = fun _ => C.X.p0 := funext hp
  obtain rfl : q = fun _ => C.q0 := funext hq
  obtain ⟨c, c', hc, hc0⟩ := GlobalTheory.T.reversedMinorProduct_mem_harmonicRowHighest D S T C hrk ap am
  obtain ⟨Q₀, hQ₀, hQ₀pt⟩ := hpt' (Formalism.IndefR.Datum.delta (fun _ => C.X.p0) (fun _ => C.q0) ap am)
  have hQ₀mem : C.toH Q₀ ∈ Harm.rowHighest ℂ c c' := by
    rw [hQ₀]
    exact Harm.colAct_mem_rowHighest u₀ hc
  have hQ₀ne : C.toH Q₀ ≠ 0 := by
    rw [hQ₀]
    intro h
    apply hc0
    apply (Harm.colAct ℂ C.X.Ψ C.q0 C.X.p0 (Fin S.rank) u₀).injective
    rw [map_zero]
    exact h
  have hfv0 : C.fvec (revB C.X.p0 B₀) f 0 = 0 := by
    unfold Ctx.fvec
    exact map_zero _
  have hptne : pt (Formalism.IndefR.Datum.delta (fun _ => C.X.p0) (fun _ => C.q0) ap am) ≠ 0 := by
    rw [← hQ₀pt]
    intro h
    have := GlobalTheory.T.fockPolynomialVector_injective_nonzeroVacuum D S T C _ hB f hf hFB hf0 (h.trans hfv0.symm)
    exact hQ₀ne (by rw [this, map_zero])
  refine ⟨c, c', Q₀, hQ₀mem, hQ₀pt, hptne, ?_⟩

  set L₁ := pureTensorO C.ψ C.θ S T (fun _ => 1) (C.sB (revB C.X.p0 B₀)) (fun _ => 1) (revB C.X.p0 B₀) f
    with hL₁
  set L₂ := pureTensorO C.ψ C.θ S T (fun _ => 1) (C.sB B₀) BS B₀ f with hL₂
  have hfv : ∀ Q, C.fvec (revB C.X.p0 B₀) f Q = L₁ Q := fun Q => rfl
  let V : Submodule ℂ (MvPolynomial (FVar D T.rank S.rank) ℂ) := (U.map L₂).comap L₁
  have hV : ∀ Q, Q ∈ V ↔ ∃ P ∈ U, C.fvec (revB C.X.p0 B₀) f Q = pt P := by
    intro Q
    simp only [V, Submodule.mem_comap, Submodule.mem_map, hfv, hpt]
    exact ⟨fun ⟨P, hP, e⟩ => ⟨P, hP, e.symm⟩, fun ⟨P, hP, e⟩ => ⟨P, hP, e.symm⟩⟩
  let W : Submodule ℂ (Harm.Poly ℂ C.X.Ψ C.q0 C.X.p0 (Fin S.rank)) :=
    V.map C.toH.toLinearMap ⊓ Harm.rowHighest ℂ c c'
  have hW : ∀ w, w ∈ W ↔ (∃ Q ∈ V, C.toH Q = w) ∧ w ∈ Harm.rowHighest ℂ c c' := by
    intro w
    simp [W, Submodule.mem_inf, Submodule.mem_map]
  have hWst : ∀ g : C.X.Ψ → GL (Fin S.rank) ℂ,
      (∀ t, (g t : Matrix (Fin S.rank) (Fin S.rank) ℂ) ∈ Matrix.unitaryGroup (Fin S.rank) ℂ) →
      ∀ w ∈ W, Harm.colActHom g w ∈ W := by
    intro g hg w hw
    obtain ⟨⟨Q, hQV, rfl⟩, hwR⟩ := (hW w).1 hw
    refine (hW _).2 ⟨?_, Harm.colAct_mem_rowHighest g hwR⟩
    obtain ⟨Q', hQ'⟩ := hsurj (Harm.colActHom g (C.toH Q))
    refine ⟨Q', ?_, hQ'⟩
    obtain ⟨h, hh, rfl⟩ := colU_surjective D S T C g hg
    obtain ⟨a, ha, hact⟩ := GlobalTheory.T.weilAction_realPoint_fockVectors_scalar_columnAction D S T C om hom _ hB f hf hFB h hh
    obtain ⟨P, hPU, hP⟩ := (hV Q).1 hQV
    obtain ⟨P', hP'U, hP'⟩ := hU h hh P hPU
    refine (hV Q').2 ⟨a⁻¹ • P', U.smul_mem _ hP'U, ?_⟩
    have e1 := hact Q Q' hQ'
    rw [hP, hP'] at e1
    rw [hpt, map_smul, ← hpt, e1, smul_smul, inv_mul_cancel₀ ha, one_smul]
  have hle : W ≤ Harm.rowHighest ℂ c c' := inf_le_right
  have hLie := GlobalTheory.T.harmonicColumnOperatorEnd_mem_of_unitary_stable W hWst
  have hWne : W ≠ ⊥ := by
    intro h
    have : C.toH Q₀ ∈ W := (hW _).2 ⟨⟨Q₀, (hV Q₀).2 ⟨_, hΔ, hQ₀pt⟩, rfl⟩, hQ₀mem⟩
    rw [h, Submodule.mem_bot] at this
    exact hQ₀ne this
  have hn : C.q0 + C.X.p0 ≤ S.rank := by have := C.hr; omega
  have hbase := Harm.basePoly_mem_of_colLie_stable hn c c' W hle hLie hWne
  have hword : ∀ w, Harm.colWord ℂ hn c c' w ∈ W := by
    intro w
    induction w with
    | nil => exact hbase
    | cons i w ih => exact hLie i.1 i.2.1 i.2.2 _ ih
  have hall : Harm.rowHighest ℂ c c' ≤ W :=
    (Harm.rowHighest_le_span_colWord_complex hn c c').trans
      (Submodule.span_le.2 (by rintro _ ⟨w, rfl⟩; exact hword w))
  intro Q hQ
  obtain ⟨⟨Q₁, hQ₁, e⟩, -⟩ := (hW _).1 (hall hQ)
  obtain rfl := hinj e
  exact (hV Q₁).1 hQ₁

end GlobalTheory.AdSpan.StableFock

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockTransl
open Formalism.L2.Ker (VCx DVar derivAt0)

theorem _root_.GlobalTheory.T.fockGaussianReading_differentiable : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D), IsStdChar D ψ (-1) → GlobalTheory.FockCompare.Chart θ σ → ∀ (S T : HSp D) (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (f : WO S T → ℂ), GlobalTheory.ChainFr.IsVacF ψ θ A B f → ∀ x, Differentiable ℂ (rd ψ σ A B f x) := by
  first | exact @GlobalTheory.FockEntire.rd_differentiable | exact GlobalTheory.FockEntire.rd_differentiable | (intros; apply GlobalTheory.FockEntire.rd_differentiable <;> assumption)
end

section

open NumberField AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.HeckeEx
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix

theorem _root_.GlobalTheory.T.mem_cuspSections_of_dominated_rational_isometries : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (I₀ : Type) [Finite I₀] (X' : I₀ → Data E r) (la : Wt X.Ψ r) (la' : ∀ j, Wt (X' j).Ψ r) (P : Frame X.Ψ r → ℂ) (Q : ∀ j, Frame (X' j).Ψ r → ℂ) (N : ℕ) (M : ℝ), 0 < N → 0 ≤ M → X.IsSec la P → (∀ j, Q j ∈ (X' j).SS (la' j)) → (∀ j a (h : QMatch X (X' j) N a) τ m, la' j τ m = la ⟨τ.1, h.mem τ⟩ m) → (∀ x ∈ X.dom, ∀ B : ℝ, 0 ≤ B → (∀ j a (h : QMatch X (X' j) N a), ‖Q j (lact a (castFr h.psi x))‖ ≤ B) → ‖P x‖ ≤ M * B) → P ∈ X.SS la := by
  first | exact @GlobalTheory.HeckeEx.mem_SS_of_dom | exact GlobalTheory.HeckeEx.mem_SS_of_dom | (intros; apply GlobalTheory.HeckeEx.mem_SS_of_dom <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical

theorem _root_.GlobalTheory.T.inMaxCompactOfModelFrame_inv : ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : Formalism.IndefR.Mult.DSModel V S) (τ : D.what₂.Tau)
    (g : Matrix (Fin V.rank) (Fin V.rank) ℂ), GlobalTheory.CuspGK.InK M τ g → GlobalTheory.CuspGK.InK M τ g⁻¹ ∧ g⁻¹⁻¹ = g := by
  first | exact @GlobalTheory.CuspGK.inK_inv | exact GlobalTheory.CuspGK.inK_inv | (intros; apply GlobalTheory.CuspGK.inK_inv <;> assumption)
end
