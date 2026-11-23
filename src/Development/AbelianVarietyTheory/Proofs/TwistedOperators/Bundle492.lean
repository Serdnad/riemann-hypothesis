module

public import Development.AbelianVarietyTheory.Proofs.HeightProofs.TypeAtOfDiscreteSeries
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DifferentiableOneP
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MeanPair
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.ConjAtFixedIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasTypeAllAddOfEquiv
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle313
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle010
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle249
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsAllTiedNotStable
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle224
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ComplexConjugationMapsMultiplicitySpace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle168
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle163
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqZeroOfFourierEqZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaRestrictIsotropicQuotientWittTowerPropertie
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SphericalEisensteinSeriesOnGroup
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle468
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size

noncomputable section
namespace GlobalTheory.CuspKFinDecomp

theorem avg_lev : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (N : GlobalTheory.Grid.Node D) (ψ : GA D N.V → ℂ) (U : Subgroup (GA D N.V)), (∀ k ∈ U, k ∈ GfC N.V → ∀ g, ψ (g * k) = ψ g) → ∀ (τ : D.what₂.Tau) (e : Formalism.REAL.KG (N.M.ε τ) → ℂ), ∀ k ∈ U, k ∈ GfC N.V → ∀ g, GlobalTheory.SeriesToClosure.avg θ N.V τ (N.M.ε τ) (N.M.fr τ) e ψ (g * k) = GlobalTheory.SeriesToClosure.avg θ N.V τ (N.M.ε τ) (N.M.fr τ) e ψ g := by
  intro D θ hθ N ψ U hψ τ e k hk hkf g
  unfold GlobalTheory.SeriesToClosure.avg
  congr 1
  funext k'
  rw [mul_assoc, ← GlobalTheory.PointAtPlaceHom.comm_of_mem N.V (GlobalTheory.PointAtPlaceHom.atTau_mem N.V τ _) hkf, ← mul_assoc,
    hψ k hk hkf]

end GlobalTheory.CuspKFinDecomp
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section
open GlobalTheory.Grow GlobalTheory.Size
open scoped ENNReal

namespace GlobalTheory.CuspApproxAll

variable {D : D7}

def avgList (θ : InfFam D) (N : GlobalTheory.Grid.Node D) (e : ∀ τ, Formalism.REAL.KG (N.M.ε τ) → ℂ)
    (l : List D.what₂.Tau) (φ : GA D N.V → ℂ) : GA D N.V → ℂ :=
  l.foldr (fun τ f => GlobalTheory.SeriesToClosure.avg θ N.V τ (N.M.ε τ) (N.M.fr τ) (e τ) f) φ

theorem avgList_nil (θ : InfFam D) (N : GlobalTheory.Grid.Node D) (e : ∀ τ, Formalism.REAL.KG (N.M.ε τ) → ℂ) (φ : GA D N.V → ℂ) :
    avgList θ N e [] φ = φ := rfl

theorem avgList_cons (θ : InfFam D) (N : GlobalTheory.Grid.Node D) (e : ∀ τ, Formalism.REAL.KG (N.M.ε τ) → ℂ) (τ : D.what₂.Tau)
    (l : List D.what₂.Tau) (φ : GA D N.V → ℂ) :
    avgList θ N e (τ :: l) φ = GlobalTheory.SeriesToClosure.avg θ N.V τ (N.M.ε τ) (N.M.fr τ) (e τ) (avgList θ N e l φ) := rfl

theorem growthSob_zero_ne_top {θ : InfFam D} {V : HSp D} {φ : GA D V → ℂ} (h : RapidDecSm θ V φ) (d : ℕ) :
    growthSob θ V d 0 φ ≠ ∞ := by
  let M : Submodule ℂ (GA D V → ℂ) :=
    { carrier := {f | growthSize V 0 f ≠ ∞}
      add_mem' := fun a b => ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨a, b⟩) growthSize_add_le
      zero_mem' := (growthSize_const (0 : ℂ)).trans_ne enorm_ne_top
      smul_mem' := fun c _ a => (growthSize_smul c).trans_ne (ENNReal.mul_ne_top enorm_ne_top a) }
  have hM : φ ∈ allDer θ V M := ⟨h.smooth, fun l hl => modGrowthExp_iff.1
    ((h.decay l hl).bounded.imp fun _ hC g => (hC g).trans_eq (by simp))⟩
  refine wordSum_ne_top_iff.2 fun l _ => ?_
  exact (wordAct_rel (A := glDer θ V) (B := glDer θ V) (R := fun f _ => f ∈ allDer θ V M) l
    (fun a _ _ _ hf => RderC_mem_allDer hf a.1 _) (y := φ) hM).2 [] (fun _ h => by simp at h)

def Good (θ : InfFam D) (V : HSp D) (f : GA D V → ℂ) : Prop := RapidDecSm θ V f ∧ IsCuspFun V f

theorem good_add {θ : InfFam D} {V : HSp D} {f f' : GA D V → ℂ} (h : Good θ V f) (h' : Good θ V f') :
    Good θ V (f + f') :=
  ⟨h.1.add h'.1, GlobalTheory.MultMem.isCuspFun_add h.1.toIsAutFun h'.1.toIsAutFun h.2 h'.2⟩

theorem good_smul {θ : InfFam D} {V : HSp D} {f : GA D V → ℂ} (c : ℂ) (h : Good θ V f) : Good θ V (c • f) :=
  ⟨h.1.smul c, GlobalTheory.MultMem.isCuspFun_smul c h.2⟩

theorem good_zero (θ : InfFam D) (V : HSp D) : Good θ V 0 := by
  refine ⟨rapidDecSm_iff.2 ⟨zero_mem _, ⊤, isOpen_univ, fun _ _ _ _ => rfl⟩, ?_⟩
  exact fun _ _ _ _ _ _ _ _ => by simp

theorem good_value (hP : GlobalTheory.Published.CuspRapidDecay) {θ : InfFam D} (hθ : IsInfFam θ) (N : GlobalTheory.Grid.Node D) {Φ : N.Maps}
    (hΦ : Φ ∈ N.Cusp θ) (v : SmT N.M) : Good θ N.V (Φ v) := by
  obtain ⟨U, hU, rfl⟩ := Submodule.mem_map.1 hΦ
  clear hΦ
  have hU' : ∀ w, Good θ N.V (U w) := by
    induction hU using Submodule.span_induction with
    | mem x hx => exact fun w => ⟨rapidDecSm_of_cuspForm hP hθ (hx.aut w) (hx.cusp w), hx.cusp w⟩
    | zero => exact fun w => good_zero θ N.V
    | add x y _ _ hx hy => exact fun w => good_add (hx w) (hy w)
    | smul c x _ hx => exact fun w => good_smul c (hx w)
  induction v using PiTensorProduct.induction_on with
  | smul_tprod r f => simpa using good_smul r (hU' f)
  | add x y hx hy => simpa using good_add hx hy

end GlobalTheory.CuspApproxAll
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical
open scoped Matrix

noncomputable section

namespace GlobalTheory.GelfSymm

open scoped Matrix

open GlobalTheory.Mem.RealTranslate (derEnd)
open GlobalTheory.RegSch (wordDer)

theorem prod_map_neg {R : Type} [Ring R] [Algebra ℂ R] :
    ∀ l : List R, (l.map fun a => -a).prod = (-1 : ℂ) ^ l.length • l.prod
  | [] => by simp
  | a :: l => by
    rw [List.map_cons, List.prod_cons, prod_map_neg l, List.prod_cons, List.length_cons, pow_succ,
      mul_smul_comm, neg_mul, mul_comm, mul_smul, neg_one_smul, smul_neg]

theorem sum_words_rev {R : Type} [Ring R] [Algebra ℂ R] {n : ℕ} (φ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] R)
    (M : Matrix (Fin n) (Fin n) ℂ) (hM : IsUnit M.det) (k : ℕ) :
    ∑ idx : Fin (k + 1) → Fin n,
      (List.ofFn fun a : Fin (k + 1) => φ (-(M * (Matrix.single (idx a) (idx (a + 1)) 1)ᵀ * M⁻¹))).reverse.prod =
    (-1 : ℂ) ^ (k + 1) • ∑ idx : Fin (k + 1) → Fin n,
      (List.ofFn fun a : Fin (k + 1) => φ (Matrix.single (idx a) (idx (a + 1)) 1)).prod := by
  let ψ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Rᵐᵒᵖ := (MulOpposite.opLinearEquiv ℂ).toLinearMap ∘ₗ φ
  have h := congrArg MulOpposite.unop (GlobalTheory.RegSch.GelfCyc.sum_words ψ M hM k)
  have e : ∀ l : List R, (l.map MulOpposite.op).prod = MulOpposite.op l.reverse.prod := fun l => by
    rw [MulOpposite.op_list_prod, List.map_reverse, List.reverse_reverse]
  have e' : ∀ l : List R, (l.map MulOpposite.op).reverse.prod = MulOpposite.op l.prod := fun l =>
    (MulOpposite.op_list_prod l).symm
  have hψ : ∀ g : Fin (k + 1) → Matrix (Fin n) (Fin n) ℂ, (List.ofFn fun a => ψ (g a)) = (List.ofFn fun a => φ (g a)).map MulOpposite.op := by
    intro g; rw [List.map_ofFn]; rfl
  have hs : ∀ f : (Fin (k + 1) → Fin n) → R, ∑ i, MulOpposite.op (f i) = MulOpposite.op (∑ i, f i) :=
    fun f => (map_sum MulOpposite.opAddEquiv f _).symm
  simp only [hψ, e, e', hs, MulOpposite.unop_smul, MulOpposite.unop_op] at h
  exact h

end GlobalTheory.GelfSymm

namespace GlobalTheory.GelfSymm

open scoped Matrix
open GlobalTheory.Mem.RealTranslate (derEnd)
open GlobalTheory.RegSch (wordDer)

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}

theorem wordDer_append (τ : D.what₂.Tau) (l l' : List (Matrix (Fin V.rank) (Fin V.rank) ℂ)) (f : GA D V → ℂ) :
    wordDer θ V τ (l ++ l') f = wordDer θ V τ l (wordDer θ V τ l' f) := by
  simp only [wordDer, List.foldr_append]

theorem wordDer_mem {τ : D.what₂.Tau} {A : Submodule ℂ (GA D V → ℂ)} (hA : ∀ Z, ∀ f ∈ A, RderC θ V τ Z f ∈ A)
    (l : List (Matrix (Fin V.rank) (Fin V.rank) ℂ)) {f : GA D V → ℂ} (hf : f ∈ A) : wordDer θ V τ l f ∈ A := by
  induction l with
  | nil => exact hf
  | cons Z l ih => exact hA Z _ ih

theorem adj_word {τ : D.what₂.Tau} {A : Submodule ℂ (GA D V → ℂ)} (hA : ∀ Z, ∀ f ∈ A, RderC θ V τ Z f ∈ A)
    (b : (GA D V → ℂ) →ₗ⋆[ℂ] (GA D V → ℂ) →ₗ[ℂ] ℂ)
    (hb : ∀ Z, ∀ x ∈ A, ∀ y ∈ A, b x (RderC θ V τ Z y) =
      b (RderC θ V τ ((gramAt D V τ)⁻¹ * Matrix.conjTranspose Z * gramAt D V τ) x) y) :
    ∀ (l : List (Matrix (Fin V.rank) (Fin V.rank) ℂ)), ∀ x ∈ A, ∀ y ∈ A,
      b x (wordDer θ V τ l y) =
        b (wordDer θ V τ (l.reverse.map fun Z => (gramAt D V τ)⁻¹ * Matrix.conjTranspose Z * gramAt D V τ) x) y
  | [], x, _, y, _ => rfl
  | Z :: l, x, hx, y, hy => by
    show b x (RderC θ V τ Z (wordDer θ V τ l y)) = _
    rw [hb Z x hx _ (wordDer_mem hA l hy), adj_word hA b hb l _ (hA _ _ hx) y hy, List.reverse_cons, List.map_append,
      wordDer_append]
    rfl

end GlobalTheory.GelfSymm


open GlobalTheory.Mem.RealTranslate (derEnd) in
open GlobalTheory.RegSch (wordDer) in
open GlobalTheory.GelfSymm in
theorem GlobalTheory.GelfSymm.gelf_symm : ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D), IsInfFam (D := D) θ →
    ∀ (τ : D.what₂.Tau) (A : Submodule ℂ (GA D V → ℂ)), A ≤ GlobalTheory.Mem.AutSpace.SmFun θ V →
    (∀ Z, ∀ f ∈ A, RderC θ V τ Z f ∈ A) → ∀ b : (GA D V → ℂ) →ₗ⋆[ℂ] (GA D V → ℂ) →ₗ[ℂ] ℂ,
    (∀ Z, ∀ x ∈ A, ∀ y ∈ A, b x (RderC θ V τ Z y) = b (RderC θ V τ ((gramAt D V τ)⁻¹ * Matrix.conjTranspose Z * gramAt D V τ) x) y) →
    ∀ k, ∀ x ∈ A, ∀ y ∈ A, b x (gelf θ V τ k y) = b (gelf θ V τ k x) y := by
  intro D θ V hθ τ A hAS hA b hb k x hx y hy
  have hu : IsUnit (gramAt D V τ).det := GlobalTheory.SmoothAutCheck.gramAt_unit V τ
  have hM : IsUnit ((gramAt D V τ)⁻¹).det := Matrix.isUnit_nonsing_inv_det_iff.2 hu
  let E : (Fin (k + 1) → Fin V.rank) → Fin (k + 1) → Matrix (Fin V.rank) (Fin V.rank) ℂ :=
    fun idx a => Matrix.single (idx a) (idx (a + 1)) 1
  have hg : ∀ f, gelf θ V τ k f = ∑ idx, wordDer θ V τ (List.ofFn (E idx)) f := by
    intro f
    refine Finset.sum_congr rfl fun idx _ => ?_
    rw [wordDer, ← List.foldr_map (f := RderC θ V τ) (g := fun A acc => A acc), List.map_ofFn]
    rfl
  have hs : ∀ i j, (gramAt D V τ)⁻¹ * Matrix.conjTranspose (Matrix.single i j (1 : ℂ)) * gramAt D V τ =
      -(-((gramAt D V τ)⁻¹ * (Matrix.single i j (1 : ℂ))ᵀ * (gramAt D V τ)⁻¹⁻¹)) := by
    intro i j
    rw [neg_neg, Matrix.nonsing_inv_nonsing_inv _ hu, Matrix.conjTranspose_single, Matrix.transpose_single, star_one]
  have key : ∑ idx, (((List.ofFn (E idx)).reverse.map
        fun Z => (gramAt D V τ)⁻¹ * Matrix.conjTranspose Z * gramAt D V τ).map (derEnd hθ τ)).prod =
      ∑ idx, ((List.ofFn (E idx)).map (derEnd hθ τ)).prod := by
    have h1 := sum_words_rev (derEnd hθ τ) (gramAt D V τ)⁻¹ hM k
    have e : ∀ idx, ((List.ofFn (E idx)).reverse.map
        fun Z => (gramAt D V τ)⁻¹ * Matrix.conjTranspose Z * gramAt D V τ).map (derEnd hθ τ) =
        (List.ofFn fun a => derEnd hθ τ (-((gramAt D V τ)⁻¹ * (E idx a)ᵀ * (gramAt D V τ)⁻¹⁻¹))).reverse.map
          fun a => -a := by
      intro idx
      rw [List.map_map, List.map_reverse, List.map_reverse, List.map_ofFn, List.map_ofFn]
      congr 1
      congr 1
      funext a
      simp only [Function.comp_apply, ← map_neg, neg_neg]
      simpa only [E, neg_neg] using congrArg (derEnd hθ τ) (hs (idx a) (idx (a + 1)))
    simp only [e, prod_map_neg, List.length_reverse, List.length_ofFn, List.map_ofFn]
    rw [← Finset.smul_sum, h1, smul_smul, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_smul]
    rfl
  have hxS : x ∈ GlobalTheory.Mem.AutSpace.SmFun θ V := hAS hx
  have wx : ∀ w, wordDer θ V τ w x = ((w.map (derEnd hθ τ)).prod ⟨x, hxS⟩).1 :=
    fun w => GlobalTheory.RegSch.GelfCyc.wordDer_eq hθ τ w ⟨x, hxS⟩
  have hgx : ∑ idx, wordDer θ V τ ((List.ofFn (E idx)).reverse.map
      fun Z => (gramAt D V τ)⁻¹ * Matrix.conjTranspose Z * gramAt D V τ) x = gelf θ V τ k x := by
    rw [hg x]
    simp only [wx]
    rw [← Submodule.coe_sum, ← Submodule.coe_sum, ← LinearMap.sum_apply, ← LinearMap.sum_apply, key]

  rw [hg y, map_sum, ← hgx, map_sum, LinearMap.sum_apply]
  exact Finset.sum_congr rfl fun idx _ => adj_word hA b hb _ x hx y hy
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.CuspValueType

section Model

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem dRep_conj (σ : Mx n → (H →L[ℂ] H)) {P : Mx n} (hP : IsUnit P) (X : Mx n) (w : H) :
    dRep (fun g => σ (P * g * P⁻¹)) X w = dRep σ (P * X * P⁻¹) w := by
  unfold dRep
  simp only [GlobalTheory.SmVecModel.exp_smul_conj hP]

theorem foldr_conj (σ : Mx n → (H →L[ℂ] H)) {P : Mx n} (hP : IsUnit P) (l : List (Mx n)) (w : H) :
    l.foldr (dRep fun g => σ (P * g * P⁻¹)) w = (l.map fun X => P * X * P⁻¹).foldr (dRep σ) w := by
  induction l with
  | nil => rfl
  | cons X l ih => rw [List.foldr_cons, List.map_cons, List.foldr_cons, ih, dRep_conj σ hP]

theorem sobNorm_conj (σ : Mx n → (H →L[ℂ] H)) {P : Mx n} (hP : IsUnit P) (S : List (List (Mx n))) (w : H) :
    sobNorm (fun g => σ (P * g * P⁻¹)) S w = sobNorm σ (S.map fun l => l.map fun X => P * X * P⁻¹) w := by
  unfold sobNorm
  rw [List.map_map]
  congr 1
  refine List.map_congr_left fun l _ => ?_
  simp only [Function.comp_apply, foldr_conj σ hP]

theorem sobNorm_conj_back (σ : Mx n → (H →L[ℂ] H)) {P : Mx n} (hP : IsUnit P) (S : List (List (Mx n))) (w : H) :
    sobNorm (fun g => σ (P * g * P⁻¹)) (S.map fun l => l.map fun X => P⁻¹ * X * P) w = sobNorm σ S w := by
  rw [sobNorm_conj σ hP, List.map_map]
  congr 1
  refine (List.map_congr_left fun l _ => ?_).trans (List.map_id S)
  show List.map (fun X => P * X * P⁻¹) (List.map (fun X => P⁻¹ * X * P) l) = l
  rw [List.map_map]
  refine (List.map_congr_left fun X _ => ?_).trans (List.map_id l)
  exact GlobalTheory.SmVecModel.conj_cancel hP X

theorem exists_ctrl_conj [CompleteSpace H] {ε : Fin n → Bool} {σ : Mx n → (H →L[ℂ] H)} (hσ : Std ε σ) {P G : Mx n}
    (hP : IsUnit P) (hG : Pᴴ * Jm ε * P = G) (S₀ : List (List (Mx n))) (hS₀ : Words (lieOf G) S₀) :
    ∃ S, Words (lieOf G) S ∧ Ctrl (lieOf G) (Formalism.QuantumDeterminants.UH G) (fun g => σ (P * g * P⁻¹)) S ∧
      ∃ A : ℝ, 0 ≤ A ∧ ∀ w, SmoothVec (lieOf G) (fun g => σ (P * g * P⁻¹)) w →
        sobNorm (fun g => σ (P * g * P⁻¹)) S₀ w ≤ A * sobNorm (fun g => σ (P * g * P⁻¹)) S w := by
  obtain ⟨S₁, hS₁, -, ⟨B, hB, hc⟩, A, hA, hd⟩ := GlobalTheory.TypeSumCtrl.exists_ctrl n ε H σ hσ
    (S₀.map fun l => l.map fun X => P * X * P⁻¹) (by
      intro l hl X hX
      obtain ⟨l', hl', rfl⟩ := List.mem_map.1 hl
      obtain ⟨Y, hY, rfl⟩ := List.mem_map.1 hX
      exact GlobalTheory.SmVecModel.lie_conj hP hG (hS₀ l' hl' Y hY))
  refine ⟨S₁.map fun l => l.map fun X => P⁻¹ * X * P, ?_,
    ⟨fun g => B (P * g * P⁻¹), hB.comp (by fun_prop), fun g hg w hw => ?_⟩, A, hA, fun w hw => ?_⟩
  · intro l hl X hX
    obtain ⟨l', hl', rfl⟩ := List.mem_map.1 hl
    obtain ⟨Y, hY, rfl⟩ := List.mem_map.1 hX
    exact GlobalTheory.SmVecModel.lie_conj_inv hP hG (hS₁ l' hl' Y hY)
  · rw [sobNorm_conj_back σ hP, sobNorm_conj_back σ hP]
    exact hc _ (GlobalTheory.TypeAtCompare.conj_mem hP hG hg) w (GlobalTheory.SmVecModel.smoothVec_of_conj hP hG hw)
  · rw [sobNorm_conj_back σ hP, sobNorm_conj σ hP]
    exact hd w (GlobalTheory.SmVecModel.smoothVec_of_conj hP hG hw)

theorem smoothVec_zero (Lie : Set (Mx n)) (σ : Mx n → (H →L[ℂ] H)) : SmoothVec Lie σ (0 : H) := by
  intro k Xs _
  simp only [map_zero]
  exact contDiff_const

theorem hasTypeAll_single [CompleteSpace H] {ε : Fin n → Bool} {σ : Mx n → (H →L[ℂ] H)} (hσ : Std ε σ) {P G : Mx n}
    (hP : IsUnit P) (hG : Pᴴ * Jm ε * P = G) {u : H} (hu : SmoothVec (lieOf G) (fun g => σ (P * g * P⁻¹)) u)
    {ℓ : H →ₗ[ℂ] ℂ} (hℓ : Sobolev₂ (lieOf G) (fun g => σ (P * g * P⁻¹)) ℓ) {f : Mx n → ℂ}
    (hf : ∀ g ∈ Formalism.QuantumDeterminants.UH G, ℓ (σ (P * g * P⁻¹) u) = f g) :
    HasTypeAll (lieOf G) (Formalism.QuantumDeterminants.UH G) (fun g => σ (P * g * P⁻¹)) f := by
  obtain ⟨S₀, C₀, hS₀, hb⟩ := hℓ
  obtain ⟨S, hS, hc, A, hA, hd⟩ := exists_ctrl_conj hσ hP hG S₀ hS₀
  have hv : ∀ i, SmoothVec (lieOf G) (fun g => σ (P * g * P⁻¹)) ((Pi.single 0 u : ℕ → H) i) := fun i => by
    by_cases hi : i = 0
    · subst hi; simpa using hu
    · rw [Pi.single_eq_of_ne hi]; exact smoothVec_zero _ _
  refine ⟨S, hS, hc, Pi.single 0 u, fun i => if i = 0 then ℓ else 0, Pi.single 0 (|C₀| * A),
    ⟨⟨hv, fun i => ?_, fun i w hw => ?_, ?_, fun g hg => ?_⟩, fun S' _ => ?_⟩⟩
  · by_cases hi : i = 0
    · subst hi; simp only [Pi.single_eq_same]; positivity
    · rw [Pi.single_eq_of_ne hi]
  · by_cases hi : i = 0
    · subst hi
      simp only [if_true, Pi.single_eq_same]
      have h1 := hb w hw
      have h2 := hd w hw
      have h3 : 0 ≤ sobNorm (fun g => σ (P * g * P⁻¹)) S₀ w := sobNorm_nonneg _ _ _
      have h4 : C₀ * sobNorm (fun g => σ (P * g * P⁻¹)) S₀ w ≤ |C₀| * sobNorm (fun g => σ (P * g * P⁻¹)) S₀ w :=
        mul_le_mul_of_nonneg_right (le_abs_self _) h3
      calc ‖ℓ w‖ ≤ C₀ * sobNorm (fun g => σ (P * g * P⁻¹)) S₀ w := h1
        _ ≤ |C₀| * sobNorm (fun g => σ (P * g * P⁻¹)) S₀ w := h4
        _ ≤ |C₀| * (A * sobNorm (fun g => σ (P * g * P⁻¹)) S w) := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
        _ = |C₀| * A * sobNorm (fun g => σ (P * g * P⁻¹)) S w := by ring
    · simp [hi, Pi.single_eq_of_ne hi]
  · refine (hasSum_single 0 fun i hi => ?_).summable
    simp [Pi.single_eq_of_ne hi]
  · rw [← hf g hg]
    have := hasSum_single (f := fun i : ℕ => (if i = 0 then ℓ else 0) (σ (P * g * P⁻¹) ((Pi.single 0 u : ℕ → H) i))) 0
      fun i hi => by simp [hi]
    simpa using this
  · refine (hasSum_single 0 fun i hi => ?_).summable
    simp [Pi.single_eq_of_ne hi]

end Model

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Matrix
open GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum

theorem isTypeAt_value {D : D7} (θ : InfFam D)
    (hHC : GlobalTheory.Published.HarishChandraModules) {V : HSp D} {Sp : D.what₂.Tau → SPar} (M : DSModel V Sp)
    {J : Set (GA D V)} {χ : GA D V → ℂ} {T : MMap M} (hT : IsMultMap θ M J χ T) (v : M.Vec) (τ : D.what₂.Tau) :
    IsTypeAt θ V τ (Sp τ) (T v) := by
  have hD := M.ds τ
  haveI : CompleteSpace (M.H τ) := hD.1
  have hσ : Std (M.ε τ) (M.σ τ) := std_of_isDS hHC hD
  refine ⟨M.H τ, _, _, M.σ τ, M.lam τ, M.ε τ, M.fr τ, M.enum τ, hD, M.fr_unit τ, M.fr_gram τ, fun x => ?_⟩
  obtain ⟨ℓ, hℓ, hℓv⟩ := hT.cont τ v x
  have hu : SmoothVec (lieAt V τ) (fun g => M.σ τ (M.fr τ * g * (M.fr τ)⁻¹)) (v τ : M.H τ) :=
    GlobalTheory.SmVecModel.smoothVec_to_conj (M.fr_unit τ) (M.fr_gram τ) ((GlobalTheory.SmVecModel.mem_sm_iff M τ _).1 (v τ).2)
  have hall : HasTypeAll (lieOf (gramAt D V τ)) (Formalism.QuantumDeterminants.UH (gramAt D V τ))
      (fun g => M.σ τ (M.fr τ * g * (M.fr τ)⁻¹)) (fun g => T v (x * atTau θ V τ g)) := by
    refine hasTypeAll_single hσ (M.fr_unit τ) (M.fr_gram τ) hu hℓ fun g hg => ?_
    have h1 := hT.equiv τ g hg v ⟨M.rep τ g (v τ), GlobalTheory.ConjMult.rep_mem_sm M τ hg (v τ).2⟩ rfl
    have h2 := hℓv ⟨M.rep τ g (v τ), GlobalTheory.ConjMult.rep_mem_sm M τ hg (v τ).2⟩
    show ℓ (M.rep τ g (v τ)) = _
    rw [h2, h1]
    rfl
  exact hasTypeAll_iff.1 hall

end GlobalTheory.CuspValueType

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LeviNormInj

open GlobalTheory.MixModel

theorem phase_eq (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (W : HSp D) {r : ℕ} (y' : Mx D r W.rank) (u : Mx D W.rank r) :
    GlobalTheory.LeviNorm.phase ψ W (adj (incA D D.host.xi0⁻¹ • (HMul.hMul y' (giA W)))) u =
      ψ (Algebra.trace (AF D.host.F) (AE D) (Matrix.trace (HMul.hMul (y' : Matrix (Fin r) (Fin W.rank) (AE D)) (u : Matrix (Fin W.rank) (Fin r) (AE D))))) := by
  rw [GlobalTheory.LeviNorm.phase_apply, adj_adj]
  congr 2
  rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, ← mul_assoc, ← map_mul,
    mul_inv_cancel₀ (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D), map_one, one_mul, Matrix.mul_assoc]
  have h : giA W * gA W = 1 := by
    change (W.gram⁻¹).map (incA D) * W.gram.map (incA D) = 1
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 (gram_det_ne W)),
      Matrix.map_one _ (map_zero (incA D)) (map_one (incA D))]
  rw [← Matrix.mul_assoc (giA W), h, Matrix.one_mul]

theorem eq_of_phase_integral_eq : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (W : HSp D) (r : ℕ) (μ : Measure (Mx D W.rank r)), μ.IsAddHaarMeasure → ∀ N₁ N₂ : Mx D W.rank r → ℂ, Continuous N₁ → Continuous N₂ → Integrable N₁ μ → Integrable N₂ μ → (∀ y : Mx D W.rank r, ∫ u, GlobalTheory.LeviNorm.phase ψ W y u * N₁ u ∂μ = ∫ u, GlobalTheory.LeviNorm.phase ψ W y u * N₂ u ∂μ) → N₁ = N₂ := by
  intro D ψ hψ W r μ hμ N₁ N₂ hc₁ hc₂ hi₁ hi₂ h
  obtain ⟨i1, i2, i3, i4, -⟩ := GlobalTheory.TowerRestrict.lattice_Mx D W.rank r
  haveI : BorelSpace (Mx D W.rank r) := ⟨rfl⟩
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have ht : Continuous (Algebra.trace (AF D.host.F) (AE D)) := IsModuleTopology.continuous_of_linearMap _
  have hcont : ∀ y : Mx D r W.rank, Continuous fun u : Mx D W.rank r =>
      ψ (Algebra.trace (AF D.host.F) (AE D) (Matrix.trace (HMul.hMul (y : Matrix (Fin r) (Fin W.rank) (AE D)) (u : Matrix (Fin W.rank) (Fin r) (AE D))))) :=
    fun y => hψ.1.1.comp (ht.comp (continuous_finsetSum _ fun i _ =>
      ((continuous_const.matrix_mul continuous_id).matrix_elem i i)))
  have hint : ∀ (y : Mx D r W.rank) (N : Mx D W.rank r → ℂ), Integrable N μ → Integrable (fun u =>
      ψ (Algebra.trace (AF D.host.F) (AE D) (Matrix.trace (HMul.hMul (y : Matrix (Fin r) (Fin W.rank) (AE D)) (u : Matrix (Fin W.rank) (Fin r) (AE D))))) * N u) μ := by
    intro y N hN
    have := hN.mul_bdd (hcont y).aestronglyMeasurable (c := 1) (Filter.Eventually.of_forall fun u => (hψ.1.2.1 _).le)
    simpa only [mul_comm] using this
  rw [← sub_eq_zero]
  refine GlobalTheory.AdelicMatFourier.eq_zero_of_fourier_eq_zero D ψ hψ W.rank r μ hμ (N₁ - N₂) (hc₁.sub hc₂) (hi₁.sub hi₂) fun y' => ?_
  have e := h (adj (incA D D.host.xi0⁻¹ • (HMul.hMul y' (giA W))))
  simp only [phase_eq] at e
  simp only [Pi.sub_apply, mul_sub]
  rw [integral_sub (hint y' N₁ hi₁) (hint y' N₂ hi₂), e, sub_self]

end GlobalTheory.LeviNormInj
end
end
