module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle009
public import Aesop.BuiltinRules
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle129
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle385
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaSourceAction
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle309
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle313
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle236
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactSubgroupsActOnFockVectorsAllSignatures
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle196
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIntegralForm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle342
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle193
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Coalgebra.CoassocSimps
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod

noncomputable section
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SliceModel

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k)

theorem ι_e (x : k) : p.e * p.ι x = p.ι x := by
  rw [← p.ι_π (p.ι x), p.π_ι]

theorem ι_mul (x y : k) : p.ι (x * y) = p.ι x * p.ι y := by
  have h1 : p.ι (x * y) = p.ι (p.π (p.ι x * p.ι y)) := by rw [map_mul p.π, p.π_ι, p.π_ι]
  rw [h1, p.ι_π, ← mul_assoc, ι_e]

theorem ι_mul_right (x : k) (z : AE D) : p.ι x * z = p.ι (x * p.π z) := by
  rw [ι_mul, p.ι_π, ← mul_assoc, mul_comm (p.ι x) p.e, ι_e]

theorem ι_mul_left (x : k) (z : AE D) : z * p.ι x = p.ι (p.π z * x) := by
  rw [mul_comm, ι_mul_right, mul_comm]

def prH : D.host.E →+* k := p.π.comp (incA D)

theorem prH_apply (a : D.host.E) : prH p a = p.pr a := rfl

theorem map_ι_mul_rat {l m o : Type} [Fintype m] (M : Matrix l m k) (N : Matrix m o D.host.E) :
    M.map p.ι * N.map (incA D) = (M * N.map (prH p)).map p.ι := by
  ext i j

  simp only [Matrix.mul_apply, Matrix.map_apply, map_sum, ι_mul_right]
  rfl

section Frames

variable {ρ : ℕ} (B : BesLev D ρ) (S : HSp D) (s : k) {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
  (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit)) (FS : Frame k S.rank n)

theorem qA_iA_k : B.o.qA.map (prH p) * B.o.iA.map (prH p) = 1 := by
  rw [← Matrix.map_mul, B.o.qA_iA, Matrix.map_one _ (map_zero _) (map_one _)]

theorem qA_iB_k : B.o.qA.map (prH p) * B.o.iB.map (prH p) = 0 := by
  rw [← Matrix.map_mul, B.o.qA_iB, Matrix.map_zero _ (map_zero _)]

variable {p B s FA F₀}

theorem β_eq (h : p.IsCoreFrame B s FA F₀) :
    F₀.β = B.o.iA.map (prH p) * fromCols FA.β 0 +
      B.o.iB.map (prH p) * fromCols 0 (Matrix.of fun i (_ : Unit) => s * prH p (B.ζ i)) := by
  ext r j
  rcases j with a | u
  · rw [h.1 r a]
    simp [Matrix.mul_apply, fromCols]
    rfl
  · rw [h.2 r]
    have := RingHom.map_mulVec (prH p) B.o.iB B.ζ r
    simp only [vecB] at *
    rw [prH_apply] at this
    rw [this]
    simp [Matrix.mul_apply, fromCols, Matrix.mulVec, dotProduct, Finset.mul_sum]
    ring_nf

theorem qA_β (h : p.IsCoreFrame B s FA F₀) : B.o.qA.map (prH p) * F₀.β = fromCols FA.β 0 := by
  rw [β_eq h, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, qA_iA_k, qA_iB_k, Matrix.one_mul, Matrix.zero_mul,
    add_zero]

theorem γ_qA (h : p.IsCoreFrame B s FA F₀) : FA.γ * B.o.qA.map (prH p) = F₀.γ.toRows₁ := by
  have e : FA.γ * B.o.qA.map (prH p) = FA.γ * B.o.qA.map (prH p) * (F₀.β * F₀.γ) := by rw [F₀.βγ, Matrix.mul_one]
  rw [e, ← Matrix.mul_assoc, Matrix.mul_assoc FA.γ, qA_β h, Matrix.mul_fromCols, FA.γβ, Matrix.mul_zero,
    ← Matrix.fromRows_toRows F₀.γ, Matrix.fromCols_mul_fromRows, Matrix.one_mul, Matrix.zero_mul, add_zero, Matrix.toRows₁_fromRows]

theorem γ_iA (h : p.IsCoreFrame B s FA F₀) : F₀.γ * B.o.iA.map (prH p) = fromRows FA.γ (0 : Matrix Unit (Fin B.A.rank) k) := by
  have e1 : B.o.iA.map (prH p) * FA.β = F₀.β * (fromRows (1 : Matrix n' n' k) (0 : Matrix Unit n' k) : Matrix (n' ⊕ Unit) n' k) := by
    rw [← Matrix.fromCols_toCols F₀.β, Matrix.fromCols_mul_fromRows, Matrix.mul_one, Matrix.mul_zero, add_zero]
    ext r a
    exact (h.1 r a).symm
  calc F₀.γ * B.o.iA.map (prH p) = F₀.γ * (B.o.iA.map (prH p) * FA.β) * FA.γ := by
        rw [Matrix.mul_assoc, Matrix.mul_assoc, FA.βγ, Matrix.mul_one]
    _ = (F₀.γ * F₀.β) * (fromRows (1 : Matrix n' n' k) (0 : Matrix Unit n' k) : Matrix (n' ⊕ Unit) n' k) * FA.γ := by
        rw [e1]; simp only [Matrix.mul_assoc]
    _ = fromRows FA.γ 0 := by rw [F₀.γβ, Matrix.one_mul, Matrix.fromRows_mul, Matrix.one_mul, Matrix.zero_mul]

theorem up_slice (h : p.IsCoreFrame B s FA F₀) (x : Matrix n n' k) :
    (B.o.resS S).symm (p.up FA FS x, 0) = p.up F₀ FS (fromCols x 0) := by
  have e : fromCols x (0 : Matrix n Unit k) * F₀.γ = x * F₀.γ.toRows₁ := by
    conv_lhs => rw [← Matrix.fromRows_toRows F₀.γ]
    rw [Matrix.fromCols_mul_fromRows, Matrix.zero_mul, add_zero]
  rw [OrthDec.resS_symm_apply, Matrix.zero_mul, add_zero, OrthDec.pA, GlobalTheory.MixModel.rat, Place.up, Place.up, map_ι_mul_rat,
    Matrix.mul_assoc, γ_qA h, Matrix.mul_assoc FS.β (fromCols x 0) F₀.γ, e, Matrix.mul_assoc]

theorem res_up (h : p.IsCoreFrame B s FA F₀) (x : Matrix n (n' ⊕ Unit) k) :
    (B.o.resS S (p.up F₀ FS x)).1 = p.up FA FS x.toCols₁ := by
  have e : x * fromRows FA.γ (0 : Matrix Unit (Fin B.A.rank) k) = x.toCols₁ * FA.γ := by
    conv_lhs => rw [← Matrix.fromCols_toCols x]
    rw [Matrix.fromCols_mul_fromRows, Matrix.mul_zero, add_zero]
  show (p.up F₀ FS x) * B.o.jA = _
  rw [OrthDec.jA, GlobalTheory.MixModel.rat, Place.up, Place.up, map_ι_mul_rat, Matrix.mul_assoc, γ_iA h, Matrix.mul_assoc, e,
    Matrix.mul_assoc]

end Frames

section Tensor

variable (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']

def splitH : Matrix n (n' ⊕ Unit) k ≃ₜ Matrix n n' k × (n → k) where
  toFun x := (x.toCols₁, fun r => x r (Sum.inr ()))
  invFun q := fromCols q.1 (Matrix.of fun r (_ : Unit) => q.2 r)
  left_inv x := by
    ext r j
    rcases j with j | j <;> rfl
  right_inv q := rfl
  continuous_toFun := (continuous_matrix fun i j => continuous_id.matrix_elem i (Sum.inl j)).prodMk
    (continuous_pi fun r => continuous_id.matrix_elem r (Sum.inr ()))
  continuous_invFun := continuous_matrix fun i j => by
    rcases j with j | j
    · exact continuous_fst.matrix_elem i j
    · exact (continuous_apply i).comp continuous_snd

variable {n n'}

def tens (a : (n → k) → ℂ) (ha : a ∈ SB (n → k)) : SB (Matrix n n' k) →ₗ[ℂ] SB (Matrix n (n' ⊕ Unit) k) where
  toFun Ξ := GlobalTheory.LocFlat.CFac.comapH (splitH n n') (GlobalTheory.LocFlat.CFac.prodSB Ξ ⟨a, ha⟩)
  map_add' Ξ Ξ' := by
    ext x
    simp [GlobalTheory.LocFlat.CFac.comapH_apply, GlobalTheory.LocFlat.CFac.prodSB_apply, add_mul]
  map_smul' c Ξ := by
    ext x
    simp [GlobalTheory.LocFlat.CFac.comapH_apply, GlobalTheory.LocFlat.CFac.prodSB_apply, mul_assoc]

theorem tens_apply (a : (n → k) → ℂ) (ha : a ∈ SB (n → k)) (Ξ : SB (Matrix n n' k)) (x : Matrix n (n' ⊕ Unit) k) :
    (tens a ha Ξ).1 x = Ξ.1 x.toCols₁ * a fun r => x r (Sum.inr ()) := rfl

end Tensor

theorem symplO_zero_right'' (S T : HSp D) (x : WO S T) : symplO S T x 0 = 0 := by
  simp [symplO, hO]

theorem exists_isModel_slice : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (ρ : ℕ) (B : BesLev D ρ) (S : HSp D) (s : k) (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit)) (FS : Frame k S.rank n), p.IsCoreFrame B s FA F₀ → ∀ T₀, p.IsModel ψ F₀ FS T₀ → ∀ (a : (n → k) → ℂ), a ∈ SB _ → ∀ v : WO B.L S, ∃ T₁, p.IsModel ψ FA FS T₁ ∧ ∀ (Ξ : SB (Matrix n n' k)) (Ψ : SB (Matrix n (n' ⊕ Unit) k)), (∀ x, Ψ.1 x = Ξ.1 x.toCols₁ * a fun r => x r (Sum.inr ())) → ∀ u, T₀ Ψ ((B.o.resS S).symm (u, v)) = T₁ Ξ u := by
  intro D k _ _ _ _ p ψ n n' _ _ _ _ ρ B S s FA F₀ FS h T₀ hT a ha v
  let T₁ : SB (Matrix n n' k) →ₗ[ℂ] (WO B.A S → ℂ) :=
    (LinearMap.funLeft ℂ ℂ fun u => (B.o.resS S).symm (u, v)) ∘ₗ T₀ ∘ₗ tens a ha
  have hT₁ : ∀ Φ u, T₁ Φ u = T₀ (tens a ha Φ) ((B.o.resS S).symm (u, v)) := fun _ _ => rfl
  refine ⟨T₁, ⟨fun Φ => ?_, fun x Φ Φ' hΦ => ?_, fun y hy Φ Φ' hΦ => ?_⟩, fun Ξ Ψ hΨ u => ?_⟩
  · exact GlobalTheory.BoxSlice.isThetaFunO_slice_left B.o (hT.theta (tens a ha Φ)) v
  · have h1 : ∀ t, (tens a ha Φ').1 t = (tens a ha Φ).1 (t + fromCols x 0) := by
      intro t
      rw [tens_apply, tens_apply, hΦ]
      congr 2
      ext i j; simp [Matrix.toCols₁, fromCols]
    have h2 := hT.trans (fromCols x 0) _ _ h1
    funext u
    rw [hT₁, h2, ← up_slice S FS h x]
    simp only [heisO, hT₁]
    rw [← map_add (B.o.resS S).symm, Prod.mk_add_mk, add_zero, B.o.symplOH_resS, AddEquiv.apply_symm_apply,
      AddEquiv.apply_symm_apply, GlobalTheory.MixModel.symplOH_zero_right, add_zero]
  · have hY : IsHalf (cA D p.e) ((B.o.resS S).symm (y, 0)) := by
      intro i j
      rw [OrthDec.resS_symm_apply, Matrix.zero_mul, add_zero]
      simp only [Matrix.mul_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [← mul_assoc, hy i l]
    have h1 : ∀ t, (tens a ha Φ').1 t =
        ψ (symplO B.V₀ S (p.up F₀ FS t) ((B.o.resS S).symm (y, 0))) * (tens a ha Φ).1 t := by
      intro t
      rw [tens_apply, tens_apply, hΦ, B.o.symplO_resS, AddEquiv.apply_symm_apply, res_up S FS h,
        symplO_zero_right'', add_zero, mul_assoc]
    have h2 := hT.modul _ hY _ _ h1
    funext u
    rw [hT₁, h2]
    simp only [heisO, hT₁]
    rw [← map_add (B.o.resS S).symm, Prod.mk_add_mk, add_zero, B.o.symplOH_resS, AddEquiv.apply_symm_apply,
      AddEquiv.apply_symm_apply, GlobalTheory.MixModel.symplOH_zero_right, add_zero]
  · have e : Ψ = tens a ha Ξ := Subtype.ext (funext fun x => (hΨ x).trans (tens_apply a ha Ξ x).symm)
    rw [e, hT₁]

end GlobalTheory.SliceModel

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ItKFin

theorem inclT_mapFactor {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau)
    (g : Module.End ℂ (M.sm τ)) (A : M.H τ →ₗ[ℂ] M.H τ) (hg : ∀ w, ((g w : M.sm τ) : M.H τ) = A w) (y : SmT M) :
    inclT M (GlobalTheory.Chain.IoLift.intersection_update_fsHerm_neg_one τ g y) =
      PiTensorProduct.map (Function.update (fun ρ => (LinearMap.id : M.H ρ →ₗ[ℂ] M.H ρ)) τ A) (inclT M y) := by
  rw [inclT, GlobalTheory.Chain.IoLift.intersection_update_fsHerm_neg_one, ← LinearMap.comp_apply, ← LinearMap.comp_apply, ← PiTensorProduct.map_comp,
    ← PiTensorProduct.map_comp]
  congr 2
  funext ρ
  by_cases e : ρ = τ
  · subst e
    ext w
    simp [hg]
  · ext w
    simp [e]

theorem itKFin : ∀ (D : D7) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) (aS aT : D.what₂.Tau → ℚ) (ω : (GA D V × GA D W →* Module.End ℂ (WO V W → ℂ))) (f : WO V W → ℂ) (It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M), IsInfFam θ → IsWeilExp ψ V W aS aT ω → IsVacVec ψ θ M M' f → IsItW θ M M' ω (ptOf ψ θ M M' f) It → ∀ P v, It P v ∈ (Submodule.span ℂ {w : SmT M | ∃ v : (M).Vec, (∀ τ, (v τ : (M).H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.kfin M τ) ∧ w = PiTensorProduct.tprod ℂ v}) := by
  intro D V W S S' M M' θ ψ aS aT ω f It hθ hW hf hIt P v
  obtain ⟨χS, χT, hWD, hexp⟩ := hW
  have hp : ptOf ψ θ M M' f = ⇑(pureTensorO ψ θ V W (cart M) (cart M') (onb M) (onb M') f) := rfl
  have hA : ∀ τ, ∀ h ∈ Formalism.REAL.Kset (M.ε τ), ∃ P' : PolF D W.rank V.rank, P'.totalDegree ≤ P.totalDegree ∧
      inclT M (It P' v) = actT M τ ((M.fr τ)⁻¹ * h * M.fr τ) (inclT M (It P v)) := by
    intro τ h hh
    obtain ⟨a, b, -, -, hc⟩ := GlobalTheory.CompactFockAction.compactFockAll D V W (Fr.ofModel M) (Fr.ofModel M') θ ψ χS χT ω f τ
      (aS τ) (aT τ) hθ hWD (hexp τ).1 (hexp τ).2 ⟨hf.theta, hf.vac⟩ hf.ne
    have h1 : (1 : Matrix (Fin W.rank) (Fin W.rank) ℂ) ∈ Formalism.REAL.Kset (M'.ε τ) := ⟨one_mem _, by simp⟩
    have := hc h hh 1 h1 P
    have e1 : (Fr.ofModel M').elt θ τ 1 = 1 := by
      have hd' := (Matrix.isUnit_iff_isUnit_det _).1 (M'.fr_unit τ)
      show atTau θ W τ ((M'.fr τ)⁻¹ * 1 * M'.fr τ) = 1
      rw [Matrix.mul_one, Matrix.nonsing_inv_mul _ hd']
      exact GlobalTheory.PointAtPlaceHom.atTau_one hθ W τ
    rw [e1, ptF_ofModel, hp, ← map_smul, ← hp] at this
    refine ⟨_, ?_, hIt.eqK τ _ (GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.maxCpt_subset M τ (GlobalTheory.Chain.IoLift.frame_mem M τ hh)) P _ this.symm v⟩
    exact (MvPolynomial.totalDegree_smul_le _ _).trans (GlobalTheory.Chain.RealIt.SubstDeg.totalDegree_subst_le _ _ _ _ _ _ _ _ _)
  have hJ := fun τ => (Formalism.REAL.maximal_compact_facts _ (M.ε τ)).1
  have hsm : ∀ τ, ∀ h ∈ Formalism.REAL.Kset (M.ε τ), ∀ w ∈ M.sm τ, (M.σ τ h : M.H τ →ₗ[ℂ] M.H τ) w ∈ M.sm τ :=
    fun τ h hh w hw => (GlobalTheory.MultGelf.mem_sm M τ).2 (GlobalTheory.SmVec.sigma_mem (M.fr_unit τ) (M.fr_gram τ) (M.ds τ).2.2.1
      ((GlobalTheory.MultGelf.mem_sm M τ).1 hw) (hJ τ h hh))
  let fK : ∀ τ, ∀ h ∈ Formalism.REAL.Kset (M.ε τ), Module.End ℂ (M.sm τ) := fun τ h hh =>
    (M.σ τ h : M.H τ →ₗ[ℂ] M.H τ).restrict (hsm τ h hh)
  have hconj : ∀ τ (h : Matrix (Fin V.rank) (Fin V.rank) ℂ), M.fr τ * ((M.fr τ)⁻¹ * h * M.fr τ) * (M.fr τ)⁻¹ = h :=
    fun τ h => by
      have hd := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
      rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_right _ _ hd, Matrix.mul_nonsing_inv_cancel_left _ _ hd]
  have hact : ∀ τ h (hh : h ∈ Formalism.REAL.Kset (M.ε τ)) (y : SmT M),
      inclT M (GlobalTheory.Chain.IoLift.intersection_update_fsHerm_neg_one τ (fK τ h hh) y) = actT M τ ((M.fr τ)⁻¹ * h * M.fr τ) (inclT M y) := by
    intro τ h hh y
    rw [inclT_mapFactor M τ _ (M.σ τ h : M.H τ →ₗ[ℂ] M.H τ) (fun w => rfl)]
    simp only [actT, DSModel.rep, hconj]
  have hx := GlobalTheory.Chain.IoLift.mem_range_map_subtype_of_contr D.what₂.Tau (fun τ => M.sm τ)
    (fun τ => (GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ).comap (M.sm τ).subtype) (It P v) fun τ L hL => by
      show IsKFin (M.ε τ) (M.σ τ) ((L (It P v) : M.sm τ) : M.H τ)
      let E : Submodule ℂ (SmT M) := (MvPolynomial.restrictTotalDegree _ ℂ P.totalDegree).map (It.flip v)
      have hle : Submodule.span ℂ ((fun k => M.σ τ k ((L (It P v) : M.sm τ) : M.H τ)) '' Formalism.REAL.Kset (M.ε τ)) ≤
          (E.map L).map (M.sm τ).subtype := by
        rw [Submodule.span_le]
        rintro _ ⟨k, hk, rfl⟩
        obtain ⟨P', hP', e⟩ := hA τ k hk
        have e2 : It P' v = GlobalTheory.Chain.IoLift.intersection_update_fsHerm_neg_one τ (fK τ k hk) (It P v) :=
          (tensorLaw D V S M).inj (by rw [e, hact τ k hk])
        have e3 := LinearMap.congr_fun (hL (fK τ k hk)) (It P v)
        simp only [LinearMap.comp_apply] at e3
        refine ⟨L (It P' v), ⟨It P' v, ⟨P', (MvPolynomial.mem_restrictTotalDegree _ _ _).2 hP', rfl⟩, rfl⟩, ?_⟩
        rw [e2, e3]
        rfl
      have hσ := (M.ds τ).2.2.1
      refine ⟨_, Submodule.finiteDimensional_of_le hle, Submodule.subset_span ⟨1, ⟨one_mem _, by simp⟩, ?_⟩,
        fun g hg w hw => ?_⟩
      · simp only [hσ.1.1]; rfl
      · refine Submodule.mem_comap.1 ((Submodule.span_le (p := Submodule.comap (M.σ τ g : M.H τ →ₗ[ℂ] M.H τ) _)).2 ?_ hw)
        rintro _ ⟨k, hk', rfl⟩
        refine Submodule.subset_span ⟨g * k, Formalism.REAL.Kset_mul _ hg hk', ?_⟩
        simp only [hσ.1.2 g (hJ τ g hg) k (hJ τ k hk')]; rfl
  obtain ⟨z, hz⟩ := hx
  rw [← hz]
  clear hz
  induction z using PiTensorProduct.induction_on with
  | smul_tprod r n =>
    rw [map_smul, PiTensorProduct.map_tprod]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨fun τ => (n τ : M.sm τ), fun τ => Submodule.subset_span (n τ).2, rfl⟩)
  | add a b ha hb => rw [map_add]; exact add_mem ha hb

end GlobalTheory.ItKFin
end
end
