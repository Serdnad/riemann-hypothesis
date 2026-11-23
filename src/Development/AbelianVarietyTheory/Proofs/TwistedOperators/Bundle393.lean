module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle361
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle350
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle364
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle350
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle362
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesModelOfDualParameter
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpDiv
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle365
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsTensorDecompositionCommutingFamilies
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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LevelPlusSubgroup
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.NatCastSmulMemHatL
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OffQOfSizeRows
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.TripleAssembly.LieInv

theorem exists_factor {U V P : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V] [AddCommGroup P]
    [Module ℂ P] (T : U →ₗ[ℂ] V) (S : Submodule ℂ U) (hT : ∀ x ∈ S, T x = 0 → x = 0) (p : U →ₗ[ℂ] P) :
    ∃ q : V →ₗ[ℂ] P, ∀ x ∈ S, q (T x) = p x := by
  obtain ⟨r, hr⟩ := (T.comp S.subtype).exists_leftInverse_of_injective (by
    rw [LinearMap.ker_eq_bot']
    exact fun x hx => Subtype.ext (hT x.1 x.2 hx))
  refine ⟨p.comp (S.subtype.comp r), fun x hx => ?_⟩
  have := LinearMap.congr_fun hr ⟨x, hx⟩
  change r (T x) = ⟨x, hx⟩ at this
  simp [this]

theorem det_ne_of_hasSig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨hn, A, hA⟩ := h
  subst hn
  intro h0
  have h1 : Aᵀ * M * A.map star = (A.submatrix finSumFinEquiv id)ᵀ * M.submatrix finSumFinEquiv finSumFinEquiv *
      (A.map star).submatrix finSumFinEquiv id := by
    rw [Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id]
  have h2 := congrArg Matrix.det hA
  rw [h1, Matrix.det_mul, Matrix.det_mul, Matrix.det_submatrix_equiv_self, h0, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_neg] at h2
  simp only [mul_zero, zero_mul, Matrix.det_one, one_mul, mul_one] at h2
  exact pow_ne_zero _ (neg_ne_zero.2 one_ne_zero) h2.symm

theorem det_ne_of_hasSig_map {E : Type} [Field E] {n r s : ℕ} {J : Matrix (Fin n) (Fin n) E} (τ : E →+* ℂ) (c : ℂ)
    (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.HasSig (c • J.map τ) r s) : J.det ≠ 0 := by
  intro h0
  refine det_ne_of_hasSig h ?_
  have : (J.map τ).det = τ J.det := (RingHom.map_det τ J).symm
  rw [Matrix.det_smul, this, h0, map_zero, mul_zero]

theorem exists_sum_pure {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Z)
    (ψ : AddChar (AF F) ℂ) (τ : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver (E := E) w)
    {Ψ : (Fin n × Fin d → AF F) → ℂ} (hΨ : Ψ ∈ darbAlg M ψ τ) :
    ∃ (m : ℕ) (f : Fin m → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d))
      (φ : Fin m → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin d → Fv F v) → ℂ),
      (∀ i, f i ∈ M.Pol ψ τ ∧ (∀ v, φ i v ∈ GlobalTheory.WeilM.SB _) ∧ ∀ᶠ v in Filter.cofinite, φ i v = M.vac v) ∧
      Ψ = ∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i) := by
  obtain ⟨m, c, g, hg⟩ := Submodule.mem_span_set'.1 hΨ
  have hg' := fun i => (g i).2
  simp only [Set.mem_setOf_eq] at hg'
  choose f φ hf hφ hφv hfe using hg'
  refine ⟨m, fun i => c i • f i, φ, fun i => ⟨Submodule.smul_mem _ _ (hf i), hφ i, hφv i⟩, ?_⟩
  rw [← hg]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hfe i]
  funext x
  simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, mul_assoc]

variable {D : D7}

theorem toUX_one (X : HSp D) {k : ℕ} (e : Fin k ≃ Fin X.rank) {J : Matrix (Fin k) (Fin k) D.host.E}
    (hJ : J = D.host.xi0 • (X.gramᵀ).submatrix e e) : GlobalTheory.TripleRead.toUX X e hJ 1 = 1 := by
  apply Subtype.ext
  apply Units.ext
  rw [GlobalTheory.TripleRead.toUX_val]
  simp [Formalism.L2.Theta.mt]

end GlobalTheory.TripleAssembly.LieInv

namespace GlobalTheory.TripleAssembly.LieInv

variable {D : D7}

theorem conjU_mul (M : HSp D) {J : Matrix (Fin M.rank) (Fin M.rank) D.host.E} (c : D.host.E) (hc : J = c • M.gram)
    (g h : GA D M) : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU M c hc (g * h) = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU M c hc g * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU M c hc h := by
  apply Subtype.ext
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU, map_mul]
  rfl

theorem conjU_one' (M : HSp D) {J : Matrix (Fin M.rank) (Fin M.rank) D.host.E} (c : D.host.E) (hc : J = c • M.gram) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU M c hc 1 = 1 := by
  apply Subtype.ext
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU, map_one]
  rfl

theorem finTens_cA (z : AE D) : GlobalTheory.LFun.finTens D.host.F D.host.E (Formalism.L2.Theta.cA D z) =
    Algebra.TensorProduct.map (AlgHom.id D.host.F _) D.sp.cm.sig (GlobalTheory.LFun.finTens D.host.F D.host.E z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

end GlobalTheory.TripleAssembly.LieInv

namespace GlobalTheory.TripleAssembly.LieInv

variable {D : D7}

theorem conjU_mem_UAt (M : HSp D) (Yd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E M.rank) (c : D.host.E)
    (hc : Yd.J = c • M.gram) {g : GA D M} (hg : g ∈ GinfC M) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU M c hc g ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt D.sp.cm.sig Yd (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) := by
  intro u hu
  have hf : finHom M g = 1 := hg
  have hent : ∀ a b, GlobalTheory.LFun.finTens D.host.F D.host.E (Formalism.L2.Theta.mt M g a b) =
      (1 : Matrix (Fin M.rank) (Fin M.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) a b := by
    intro a b
    have := congrArg (fun k : GL (Fin M.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) => k.1 a b) hf
    exact this
  ext i j
  have hm : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU M c hc g) i j = Formalism.L2.Theta.cA D (Formalism.L2.Theta.mt M g i j) := rfl
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.zero_apply]
  apply GlobalTheory.KapXLine.smul_eq_zero_of_finTens hu
  rw [hm, map_sub, finTens_cA, hent, Matrix.one_apply, Matrix.one_apply]
  by_cases h : i = j
  · subst h; simp
  · simp [h]

theorem exists_line_conjU (θ : InfFam D) (M : HSp D) (τ : D.what₂.Tau) (Y : Matrix (Fin M.rank) (Fin M.rank) ℂ)
    (hθ : IsInfFam θ) (hY : Y ∈ lieAt M τ) (Yd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E M.rank) (c : D.host.E)
    (hc : Yd.J = c • M.gram) :
    ∃ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines D.sp.cm.sig Yd, ∀ t : ℝ,
      γ (Multiplicative.ofAdd t) = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU M c hc (oneP θ M τ Y t) := by
  let γ : Multiplicative ℝ →* GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig Yd.J :=
    { toFun := fun t => GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU M c hc (oneP θ M τ Y (Multiplicative.toAdd t))
      map_one' := by
        show GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU M c hc (oneP θ M τ Y 0) = 1
        rw [GlobalTheory.Mem.Lift.oneP_zero hθ, conjU_one']
      map_mul' := fun s t => by
        show GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU M c hc (oneP θ M τ Y (Multiplicative.toAdd s + Multiplicative.toAdd t)) = _
        rw [GlobalTheory.Mem.Lift.oneP_add hθ hY, conjU_mul] }
  refine ⟨γ, ⟨?_, fun t => ?_⟩, fun t => rfl⟩
  · exact (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.continuous_conjU M c hc).comp ((GlobalTheory.Mem.Lift.continuous_oneP hθ hY).comp continuous_toAdd)
  · exact conjU_mem_UAt M Yd c hc (GlobalTheory.Mem.Lift.isAtTau_oneP hθ hY _).1

end GlobalTheory.TripleAssembly.LieInv

namespace GlobalTheory.TripleAssembly.LieInv

variable {D : D7}

end GlobalTheory.TripleAssembly.LieInv

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.TripleAssembly.Onto

theorem det_ne_of_hasSig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨hn, A, hA⟩ := h
  subst hn
  intro h0
  have h1 : Aᵀ * M * A.map star = (A.submatrix finSumFinEquiv id)ᵀ * M.submatrix finSumFinEquiv finSumFinEquiv *
      (A.map star).submatrix finSumFinEquiv id := by
    rw [Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id]
  have h2 := congrArg Matrix.det hA
  rw [h1, Matrix.det_mul, Matrix.det_mul, Matrix.det_submatrix_equiv_self, h0, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_neg] at h2
  simp only [mul_zero, zero_mul, Matrix.det_one, one_mul, mul_one] at h2
  exact pow_ne_zero _ (neg_ne_zero.2 one_ne_zero) h2.symm

theorem det_ne_of_hasSig_map {E : Type} [Field E] {n r s : ℕ} {J : Matrix (Fin n) (Fin n) E} (τ : E →+* ℂ) (c : ℂ)
    (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.HasSig (c • J.map τ) r s) : J.det ≠ 0 := by
  intro h0
  refine det_ne_of_hasSig h ?_
  have : (J.map τ).det = τ J.det := (RingHom.map_det τ J).symm
  rw [Matrix.det_smul, this, h0, map_zero, mul_zero]

theorem exists_factor {U V P : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V] [AddCommGroup P]
    [Module ℂ P] (T : U →ₗ[ℂ] V) (S : Submodule ℂ U) (hT : ∀ x ∈ S, T x = 0 → x = 0) (p : U →ₗ[ℂ] P) :
    ∃ q : V →ₗ[ℂ] P, ∀ x ∈ S, q (T x) = p x := by
  obtain ⟨r, hr⟩ := (T.comp S.subtype).exists_leftInverse_of_injective (by
    rw [LinearMap.ker_eq_bot']
    exact fun x hx => Subtype.ext (hT x.1 x.2 hx))
  refine ⟨p.comp (S.subtype.comp r), fun x hx => ?_⟩
  have := LinearMap.congr_fun hr ⟨x, hx⟩
  change r (T x) = ⟨x, hx⟩ at this
  simp [this]

theorem map_darbAlg_eq_top {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Z)
    (ψ : AddChar (AF F) ℂ) (τ : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver (E := E) w) (hM : M.IsGood ψ)
    {P : Type} [AddCommGroup P] [Module ℂ P] (pr : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d) →ₗ[ℂ] P)
    {N : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F) → Type} [∀ v, AddCommGroup (N v)] [∀ v, Module ℂ (N v)]
    (pv : ∀ v, ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] N v) (s : ∀ v, N v)
    (hs : ∀ᶠ v in Filter.cofinite, pv v (M.vac v) = s v) (hpr : (M.Pol ψ τ).map pr = ⊤)
    (hpv : ∀ v, (GlobalTheory.WeilM.SB _).map (pv v) = ⊤) :
    (darbAlg M ψ τ).map (liftPure M pr pv s) = ⊤ := by
  classical
  have H := GlobalTheory.T.weil_model_projection_factorisation σ Y Z M ψ hM P pr N pv s hs
  have hq : ∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin d → Fv F v) → ℂ),
      (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) →
      liftPure M pr pv s (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = pr f ⊗ₜ GlobalTheory.SmallThetaModules.pureT s (fun v => pv v (φ v)) := by
    unfold liftPure
    rw [dite_eq_left H]
    exact H.choose_spec
  have key : ∀ (x : P) (ξ : ∀ v, N v), Formalism.MainNotions.KudlaSiegelWeil.Restr s ξ →
      x ⊗ₜ[ℂ] GlobalTheory.SmallThetaModules.pureT s ξ ∈ (darbAlg M ψ τ).map (liftPure M pr pv s) := by
    intro x ξ hξ
    obtain ⟨f, hf, rfl⟩ : x ∈ (M.Pol ψ τ).map pr := hpr ▸ Submodule.mem_top
    have h1 : ∀ v, ∃ φ ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v), pv v φ = ξ v ∧ (pv v (M.vac v) = ξ v → φ = M.vac v) := by
      intro v
      by_cases hv : pv v (M.vac v) = ξ v
      · exact ⟨M.vac v, (hM.vac v).1, hv, fun _ => rfl⟩
      · obtain ⟨φ, hφ, e⟩ : ξ v ∈ (GlobalTheory.WeilM.SB _).map (pv v) := (hpv v) ▸ Submodule.mem_top
        exact ⟨φ, hφ, e, fun k => absurd k hv⟩
    choose φ hφ hφ1 hφ2 using h1
    have h2 : ∀ᶠ v in Filter.cofinite, φ v = M.vac v := by
      have h3 : ∀ᶠ v in Filter.cofinite, ξ v = s v := hξ
      filter_upwards [hs, h3] with v a b using hφ2 v (a.trans b.symm)
    refine ⟨GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ, Submodule.subset_span ⟨f, φ, hf, hφ, h2, rfl⟩, ?_⟩
    rw [hq f φ hφ h2, funext hφ1]
  rw [eq_top_iff, ← TensorProduct.span_tmul_eq_top, Submodule.span_le]
  rintro _ ⟨x, y, rfl⟩
  have hy : y ∈ Submodule.span ℂ {z | ∃ ξ, Formalism.MainNotions.KudlaSiegelWeil.Restr s ξ ∧ z = GlobalTheory.SmallThetaModules.pureT s ξ} := by
    rw [GlobalTheory.SmallThetaModules.pureT_span]; trivial
  rw [SetLike.mem_coe]
  induction hy using Submodule.span_induction with
  | mem z hz => obtain ⟨ξ, hξ, rfl⟩ := hz; exact key x ξ hξ
  | zero => rw [TensorProduct.tmul_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [TensorProduct.tmul_add]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [TensorProduct.tmul_smul]; exact Submodule.smul_mem _ c ha

theorem map_thetaLift {D : D7} {m k d : ℕ} {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E m}
    {Z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E k}
    (Mo : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Y Z) (ψ : AddChar (AF D.host.F) ℂ) (G : Matrix (Fin m) (Fin m) D.host.E)
    (e : Fin k ≃ Fin d) (S : Submodule ℂ ((Fin m × Fin k → AF D.host.F) → ℂ)) {P : Type} [AddCommGroup P] [Module ℂ P]
    (pD : ((Fin m × Fin k → AF D.host.F) → ℂ) →ₗ[ℂ] P)
    (hS : S ≤ GlobalTheory.WeilM.schA D.host.F (Fin m × Fin k))
    (T : ((Fin m × Fin k → AF D.host.F) → ℂ) →ₗ[ℂ] (Matrix (Fin d) (Fin m) (AE D) → ℂ))
    (hT : ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F (Fin m × Fin k), T Φ = GlobalTheory.TripleRead.thO Mo ψ G e Φ)
    (hinj : ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F (Fin m × Fin k), T Φ = 0 → Φ = 0) :
    (S.map T).map (thetaLift Mo ψ G e S pD) = S.map pD := by
  have H : ∃ q : (Matrix (Fin d) (Fin m) (AE D) → ℂ) →ₗ[ℂ] P, ∀ Ψ ∈ S, q (GlobalTheory.TripleRead.thO Mo ψ G e Ψ) = pD Ψ := by
    obtain ⟨q, hq⟩ := exists_factor T S (fun x hx => hinj x (hS hx)) pD
    exact ⟨q, fun Ψ hΨ => by rw [← hT Ψ (hS hΨ)]; exact hq Ψ hΨ⟩
  have hq : ∀ Ψ ∈ S, thetaLift Mo ψ G e S pD (T Ψ) = pD Ψ := by
    intro Ψ hΨ
    rw [hT Ψ (hS hΨ)]
    unfold thetaLift
    rw [dite_eq_left H]
    exact H.choose_spec Ψ hΨ
  ext x
  constructor
  · rintro ⟨_, ⟨Ψ, hΨ, rfl⟩, rfl⟩
    exact ⟨Ψ, hΨ, (hq Ψ hΨ).symm⟩
  · rintro ⟨Ψ, hΨ, rfl⟩
    exact ⟨T Ψ, ⟨Ψ, hΨ, rfl⟩, hq Ψ hΨ⟩

end GlobalTheory.TripleAssembly.Onto
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped ComplexConjugate
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

noncomputable section

namespace GlobalTheory.RealDict.LineStab
theorem ptF_one' {D : D7} {V W : HSp D} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A : Fr V) (B : Fr W)
    (f : WO V W → ℂ) : ptF ψ θ A B f 1 = f := by
  have h1 : (1 : PolF D W.rank V.rank) = MvPolynomial.basisMonomials _ ℂ 0 := by
    simp [MvPolynomial.coe_basisMonomials]
  rw [h1]
  simp only [ptF, pureTensorO, pureTensorL]
  rw [Module.Basis.constr_basis]
  simp [opPow]

theorem thO_zero' {m k d : ℕ} {D : D7} {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E m}
    {Z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E k} (Mo : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Y Z)
    (ψ : AddChar (AF D.host.F) ℂ) (G : Matrix (Fin m) (Fin m) D.host.E) (e : Fin k ≃ Fin d) :
    GlobalTheory.TripleRead.thO Mo ψ G e 0 = 0 := by
  funext x
  simp only [GlobalTheory.TripleRead.thO, GlobalTheory.WeilM.thetaSum, Pi.zero_apply]
  refine (tsum_congr fun ξ => ?_).trans tsum_zero
  exact mul_zero _

theorem conjU_one' {D : D7} (V : HSp D) {J : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (c : D.host.E)
    (h : J = c • V.gram) : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU V c h 1 = 1 := by
  apply Subtype.ext
  simp [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU]

theorem det_sgn_gram {D : D7} (ε : Bool) (M : HSp D) (h : (GlobalTheory.RealDict.sgE (D := D) ε • M.gram).det ≠ 0) :
    ((sgn ε M).gram).det ≠ 0 := by
  have hg : (sgn ε M).gram = -(GlobalTheory.RealDict.sgE (D := D) ε • M.gram) := by
    cases ε <;> ext i j <;> simp [GlobalTheory.RealDict.sgE, sgn, HSpace.gram]
  rw [hg, Matrix.det_neg]
  exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) h

end GlobalTheory.RealDict.LineStab

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.HaarRev

theorem haar_rev : ∀ (m : ℕ) (ε : Fin m → Bool), ∃ lam : ℝ, 0 < lam ∧
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (F : Matrix (Fin m) (Fin m) ℂ → E),
    (Integrable (fun u : Formalism.REAL.UJ ε => F (GlobalTheory.ConjDS.rv (Formalism.MainNotions.S.umat u))) (Formalism.REAL.muG ε) ↔
      Integrable (fun h : Formalism.REAL.UJ (fun a => ε a.rev) => F (Formalism.MainNotions.S.umat h)) (Formalism.REAL.muG (fun a => ε a.rev))) ∧
    ∫ u, F (GlobalTheory.ConjDS.rv (Formalism.MainNotions.S.umat u)) ∂(Formalism.REAL.muG ε) =
      lam • ∫ h, F (Formalism.MainNotions.S.umat h) ∂(Formalism.REAL.muG (fun a => ε a.rev)) := by
  intro m ε
  set ε' : Fin m → Bool := fun a => ε a.rev with hε'
  have he : ∀ a, ε' a = ε a.rev := fun a => rfl
  let φ : Formalism.REAL.UJ ε ≃* Formalism.REAL.UJ ε' := GlobalTheory.ConjDS.rvU (GlobalTheory.ConjDS.sg_symm he)
  have hφ : Continuous φ := GlobalTheory.ConjDS.rvU_cont _
  have hφs : Continuous φ.symm := GlobalTheory.ConjDS.rvU_cont he
  haveI : ((Formalism.REAL.muG ε).map φ).IsHaarMeasure :=
    MulEquiv.isHaarMeasure_map _ φ hφ hφs
  set c := Measure.haarScalarFactor ((Formalism.REAL.muG ε).map φ) (Formalism.REAL.muG ε') with hc
  have hmap : (Formalism.REAL.muG ε).map φ = c • Formalism.REAL.muG ε' :=
    Measure.isMulLeftInvariant_eq_smul _ _
  have hc0 : c ≠ 0 := by
    intro h0
    have : (Formalism.REAL.muG ε).map φ = 0 := by rw [hmap, h0, zero_smul]
    exact (Measure.IsHaarMeasure.toIsOpenPosMeasure (μ := (Formalism.REAL.muG ε).map φ)).open_pos _ isOpen_univ
      Set.univ_nonempty (by rw [this]; rfl)
  let e : Formalism.REAL.UJ ε ≃ᵐ Formalism.REAL.UJ ε' :=
    { toEquiv := φ.toEquiv, measurable_toFun := hφ.measurable, measurable_invFun := hφs.measurable }
  have he' : ⇑e = ⇑φ := rfl
  refine ⟨(c : ℝ), by positivity, ?_⟩
  intro E _ _ F
  have hcomp : (fun u : Formalism.REAL.UJ ε => F (GlobalTheory.ConjDS.rv (Formalism.MainNotions.S.umat u))) =
      (fun h : Formalism.REAL.UJ ε' => F (Formalism.MainNotions.S.umat h)) ∘ e := rfl
  constructor
  · rw [hcomp, ← integrable_map_equiv e, he', hmap, ENNReal.smul_def]
    exact integrable_smul_measure (by simpa using hc0) ENNReal.coe_ne_top
  · show ∫ u, F (Formalism.MainNotions.S.umat (e u)) ∂(Formalism.REAL.muG ε) = _
    rw [← integral_map_equiv e (fun h : Formalism.REAL.UJ ε' => F (Formalism.MainNotions.S.umat h)), he', hmap, integral_smul_nnreal_measure, NNReal.smul_def]

end GlobalTheory.HaarRev
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm

theorem _root_.GlobalTheory.T.exists_stable_complement_of_irreducible_span_intertwiners : ∀ (ι J Fm Q Pi : Type) [AddCommGroup Q] [Module ℂ Q] [AddCommGroup Pi] [Module ℂ Pi] (ρ : ι → Module.End ℂ Q)
  (C : Submodule ℂ Q) (σ : ι → Module.End ℂ Pi) (τ : J → Module.End ℂ Pi) (β : Fm → Q →ₗ[ℂ] Pi),
  GlobalTheory.RealQuot.HoweCond ρ C → (∀ f i, β f ∘ₗ ρ i = σ i ∘ₗ β f) → (∀ f, C ≤ LinearMap.ker (β f)) →
  (∀ j f, ∃ f', τ j ∘ₗ β f = β f') → (⨆ f, LinearMap.range (β f)) = ⊤ →
  (∀ N : Submodule ℂ Pi, GlobalTheory.RealQuot.IsStab σ N → GlobalTheory.RealQuot.IsStab τ N → N = ⊥ ∨ N = ⊤) →
  ∀ N : Submodule ℂ Pi, GlobalTheory.RealQuot.IsStab σ N → ∃ N' : Submodule ℂ Pi, GlobalTheory.RealQuot.IsStab σ N' ∧ IsCompl N N' := by
  first | exact @GlobalTheory.RealQuot.SemisimpleSpan.exists_stab_compl | exact GlobalTheory.RealQuot.SemisimpleSpan.exists_stab_compl | (intros; apply GlobalTheory.RealQuot.SemisimpleSpan.exists_stab_compl <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm

theorem _root_.GlobalTheory.T.simple_quotients_iso_of_intertwined_semisimple : ∀ (ι Fm Q Q' Pi : Type) [AddCommGroup Q] [Module ℂ Q] [AddCommGroup Q'] [Module ℂ Q'] [AddCommGroup Pi] [Module ℂ Pi]
  (ρ : ι → Module.End ℂ Q) (C : Submodule ℂ Q) (ρ' : ι → Module.End ℂ Q') (C' : Submodule ℂ Q') (σ : ι → Module.End ℂ Pi)
  (β : Fm → Q →ₗ[ℂ] Pi) (β₁ : Q' →ₗ[ℂ] Pi),
  (∀ f i, β f ∘ₗ ρ i = σ i ∘ₗ β f) → (∀ i, β₁ ∘ₗ ρ' i = σ i ∘ₗ β₁) →
  (∀ f, GlobalTheory.RealQuot.rad ρ C ≤ LinearMap.ker (β f)) → GlobalTheory.RealQuot.rad ρ' C' ≤ LinearMap.ker β₁ → β₁ ≠ 0 →
  (⨆ f, LinearMap.range (β f)) = ⊤ →
  (∀ N : Submodule ℂ Q, GlobalTheory.RealQuot.IsStab ρ N → GlobalTheory.RealQuot.rad ρ C ≤ N → N = GlobalTheory.RealQuot.rad ρ C ∨ N = ⊤) →
  (∀ N : Submodule ℂ Q', GlobalTheory.RealQuot.IsStab ρ' N → GlobalTheory.RealQuot.rad ρ' C' ≤ N → N = GlobalTheory.RealQuot.rad ρ' C' ∨ N = ⊤) →
  (∀ N : Submodule ℂ Pi, GlobalTheory.RealQuot.IsStab σ N → ∃ N' : Submodule ℂ Pi, GlobalTheory.RealQuot.IsStab σ N' ∧ IsCompl N N') →
  ∃ e : (Q ⧸ GlobalTheory.RealQuot.rad ρ C) ≃ₗ[ℂ] (Q' ⧸ GlobalTheory.RealQuot.rad ρ' C'),
    ∀ i, e.toLinearMap ∘ₗ GlobalTheory.RealQuot.radAct ρ C i = GlobalTheory.RealQuot.radAct ρ' C' i ∘ₗ e.toLinearMap := by
  first | exact @GlobalTheory.RealQuot.simpleQuot_iso_of_intertwined | exact GlobalTheory.RealQuot.simpleQuot_iso_of_intertwined | (intros; apply GlobalTheory.RealQuot.simpleQuot_iso_of_intertwined <;> assumption)
end

section

open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_tensorDecomposition_commutingFamilies : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] [Nontrivial W] (G : ι → Type) (a : ∀ i, G i → Module.End ℂ W), (∀ i j, i ≠ j → ∀ g h, a i g * a j h = a j h * a i g) → (∀ N : Submodule ℂ W, (∀ i g, ∀ x ∈ N, a i g x ∈ N) → N = ⊥ ∨ N = ⊤) → ∃ (X : ι → Type) (_ : ∀ i, AddCommGroup (X i)) (_ : ∀ i, Module ℂ (X i)) (_ : ∀ i, FiniteDimensional ℂ (X i)) (b : ∀ i, G i → Module.End ℂ (X i)) (m : ∀ i, X i →ₗ[ℂ] W) (e : (⨂[ℂ] i, X i) ≃ₗ[ℂ] W), (∀ i, Function.Injective (m i)) ∧ (∀ i g x, m i (b i g x) = a i g (m i x)) ∧ (∀ i, ∀ N : Submodule ℂ (X i), (∀ g, ∀ x ∈ N, b i g x ∈ N) → N = ⊥ ∨ N = ⊤) ∧ ∀ i g (x : ∀ i, X i), e (PiTensorProduct.tprod ℂ (Function.update x i (b i g (x i)))) = a i g (e (PiTensorProduct.tprod ℂ x)) := by
  first | exact @GlobalTheory.TensorDecomp.tensor_decomp | exact GlobalTheory.TensorDecomp.tensor_decomp | (intros; apply GlobalTheory.TensorDecomp.tensor_decomp <;> assumption)
end
