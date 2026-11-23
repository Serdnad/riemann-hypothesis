module

public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WeilDeligneParamMonodromyEqZeroIff
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneParamMonodromyEqZeroIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DirectSumDeRhamCrystallineJumpsAdd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PolarizedGaloisRep
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle066
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle008
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle007
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle022
import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import ReciprocityTheory.Automorphisms.PlaceA

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.WeilDeligne

namespace TwistAway

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {l : ℕ} [Fact l.Prime] {a : ℕ}

theorem matrix_eq_zero_of_isNilpotent {K : Type*} [Field K] {M : Matrix (Fin 1) (Fin 1) K}
    (hM : IsNilpotent M) : M = 0 := by
  have h1 := Matrix.isNilpotent_trace_of_isNilpotent hM
  rw [Matrix.trace_fin_one] at h1
  ext i j
  fin_cases i; fin_cases j
  simpa using h1.eq_zero

theorem end_eq_zero_of_isNilpotent {f : Module.End ℂ (Fin 1 → ℂ)} (hf : IsNilpotent f) : f = 0 := by
  have h1 := matrix_eq_zero_of_isNilpotent (hf.map
    (LinearMap.toMatrixAlgEquiv' : Module.End ℂ (Fin 1 → ℂ) ≃ₐ[ℂ] Matrix (Fin 1) (Fin 1) ℂ))
  have h2 : (LinearMap.toMatrixAlgEquiv' : Module.End ℂ (Fin 1 → ℂ) ≃ₐ[ℂ] Matrix (Fin 1) (Fin 1) ℂ) f =
      (LinearMap.toMatrixAlgEquiv' : Module.End ℂ (Fin 1 → ℂ) ≃ₐ[ℂ] Matrix (Fin 1) (Fin 1) ℂ) 0 := by
    rw [h1, map_zero]
  exact (LinearMap.toMatrixAlgEquiv' : Module.End ℂ (Fin 1 → ℂ) ≃ₐ[ℂ] Matrix (Fin 1) (Fin 1) ℂ).injective h2

theorem twGL_det_val (ρ : G E Ω →* GL (Fin a) (Qbar l)) (χ : G E Ω →* GL (Fin 1) (Qbar l))
    (g : G E Ω) :
    ((Formalism.MainNotions.SumRepresentations.At.twGL ρ (Matrix.GeneralLinearGroup.det.comp χ) g : GL (Fin a) (Qbar l)) :
        Matrix (Fin a) (Fin a) (Qbar l)) =
      (χ g : Matrix (Fin 1) (Fin 1) (Qbar l)) 0 0 • (ρ g : Matrix (Fin a) (Fin a) (Qbar l)) := by
  simp [Formalism.MainNotions.SumRepresentations.At.twGL, Matrix.det_unique, Algebra.smul_def]

variable {t : Ine (F := E) A →* Multiplicative ℤ_[l]}

theorem isMonodromy_zero_of_line {χ : G E Ω →* GL (Fin 1) (Qbar l)} {N : Matrix (Fin 1) (Fin 1) (Qbar l)}
    (hN : IsMonodromy t χ N) : IsMonodromy t χ 0 := by
  rwa [matrix_eq_zero_of_isNilpotent hN.1] at hN

theorem isMonodromy_twGL {ρ : G E Ω →* GL (Fin a) (Qbar l)} {χ : G E Ω →* GL (Fin 1) (Qbar l)}
    {N : Matrix (Fin a) (Fin a) (Qbar l)} (hN : IsMonodromy t ρ N) (hχ : IsMonodromy t χ 0) :
    IsMonodromy t (Formalism.MainNotions.SumRepresentations.At.twGL ρ (Matrix.GeneralLinearGroup.det.comp χ)) N := by
  obtain ⟨h1, U, hU, H⟩ := hN
  obtain ⟨-, U', hU', H'⟩ := hχ
  refine ⟨h1, U ⊓ U', hU.inter hU', fun σ hσ => ?_⟩
  rw [twGL_det_val, H' σ hσ.2, H σ hσ.1]
  simp

theorem wdMat_twGL {φ : Weil h} (hφ : deg φ = 1) (ρ : G E Ω →* GL (Fin a) (Qbar l))
    (χ : G E Ω →* GL (Fin 1) (Qbar l)) (N : Matrix (Fin a) (Fin a) (Qbar l)) (g : Weil h) :
    wdMat t hφ (Formalism.MainNotions.SumRepresentations.At.twGL ρ (Matrix.GeneralLinearGroup.det.comp χ)) N g =
      (χ g : Matrix (Fin 1) (Fin 1) (Qbar l)) 0 0 • wdMat t hφ ρ N g := by
  rw [wdMat, wdMat, twGL_det_val, smul_mul_assoc]

theorem isFrobSS_tensor_line {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {ρ : Weil h → Module.End ℂ V} {N : Module.End ℂ V} {a₀ : WDRep h V}
    {ψ : Weil h → Module.End ℂ (Fin 1 → ℂ)} {b₀ : WDRep h (Fin 1 → ℂ)}
    (ha : IsFrobSS ρ N a₀) (hb : IsFrobSS ψ 0 b₀) :
    IsFrobSS (fun g => TensorProduct.map (ρ g) (ψ g)) (N.rTensor (Fin 1 → ℂ)) (a₀.tensor b₀) := by
  have hψ : ∀ g, b₀.ρ g = ψ g := fun g =>
    (sub_eq_zero.mp (end_eq_zero_of_isNilpotent (hb.2 g).2)).symm
  refine ⟨by rw [WDRep.tensor_N, ha.1, hb.1, LinearMap.lTensor_zero, add_zero], fun g => ⟨?_, ?_⟩⟩
  · rw [WDRep.tensor_ρ, hψ]
    show TensorProduct.map _ _ * TensorProduct.map _ _ = TensorProduct.map _ _ * TensorProduct.map _ _
    rw [← TensorProduct.map_mul, ← TensorProduct.map_mul, (ha.2 g).1.eq]
  · rw [WDRep.tensor_ρ, hψ]
    have e1 : TensorProduct.map (ρ g) (ψ g) - TensorProduct.map (a₀.ρ g) (ψ g) =
        (ρ g - a₀.ρ g).rTensor (Fin 1 → ℂ) * (ψ g).lTensor V :=
      TensorProduct.ext' fun x y => by simp [TensorProduct.sub_tmul]
    rw [e1]
    have hc : Commute ((ρ g - a₀.ρ g).rTensor (Fin 1 → ℂ)) ((ψ g).lTensor V) := by
      show _ * _ = _ * _
      rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, LinearMap.lTensor_comp_rTensor,
        LinearMap.rTensor_comp_lTensor]
    exact hc.isNilpotent_mul_right ((ha.2 g).2.map (Module.End.rTensorAlgHom ℂ V (Fin 1 → ℂ)))

def lineEquiv (V : Type) [AddCommGroup V] [Module ℂ V] : TensorProduct ℂ V (Fin 1 → ℂ) ≃ₗ[ℂ] V :=
  (TensorProduct.congr (LinearEquiv.refl ℂ V) (LinearEquiv.funUnique (Fin 1) ℂ ℂ)).trans
    (TensorProduct.rid ℂ V)

@[simp] theorem lineEquiv_tmul (V : Type) [AddCommGroup V] [Module ℂ V] (x : V) (y : Fin 1 → ℂ) :
    lineEquiv V (x ⊗ₜ y) = y 0 • x := by
  simp [lineEquiv]

end TwistAway


open TwistAway in
theorem wdOf_twGL_det : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver (F := E) A w) (l : ℕ) [Fact l.Prime] (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (ι : Qbar l ≃+* ℂ) (a : ℕ) (ρ : G E Ω →* GL (Fin a) (Qbar l)) (χ : G E Ω →* GL (Fin 1) (Qbar l)), Continuous (fun g => ((ρ g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l))) → Continuous (fun g => ((χ g : GL (Fin 1) (Qbar l)) : Matrix (Fin 1) (Fin 1) (Qbar l))) → GlobalTheory.WeilDeligne.wdOf h hl ι (Formalism.MainNotions.SumRepresentations.At.twGL ρ (Matrix.GeneralLinearGroup.det.comp χ)) = (GlobalTheory.WeilDeligne.wdOf h hl ι ρ).lpChar (GlobalTheory.WeilDeligne.wdOf h hl ι χ) := by
  intro E Ω _ _ _ _ _ A w h l _ hl ι a ρ χ hρ hχ
  have ht := isTameChar_tameL h hl
  obtain ⟨N, hN⟩ := exists_isMonodromy h hl ht hρ
  obtain ⟨Nχ, hNχ⟩ := exists_isMonodromy h hl ht hχ
  have hχ0 := isMonodromy_zero_of_line hNχ
  have hN' := isMonodromy_twGL hN hχ0
  obtain ⟨a₀, ha, ea⟩ := hN.wdOf_spec hl ht (deg_frob (h := h)) ι
  obtain ⟨b₀, hb, eb⟩ := hχ0.wdOf_spec hl ht (deg_frob (h := h)) ι
  obtain ⟨d, hd, ed⟩ := hN'.wdOf_spec hl ht (deg_frob (h := h)) ι
  rw [ea, eb, ed, WD.lpChar_mk]
  refine WD.sound (WDRep.Iso.symm ?_)
  rw [map_zero] at hb
  refine (isFrobSS_tensor_line ha hb).iso hd (lineEquiv _) (fun g v => ?_) (fun v => ?_)
  · induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
      simp only [TensorProduct.map_tmul, lineEquiv_tmul, IsMonodromy.rep_apply, wdMat_twGL,
        wdMat_zero, toEndC_smul, map_smul, LinearMap.smul_apply]
      rw [smul_smul]
      congr 1
      simp [toEndC_apply, Matrix.mulVec, dotProduct, mul_comm]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  · induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy]

end GlobalTheory.WeilDeligne
end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module IsNilpotent

namespace GlobalTheory.WeilDeligne.SumParam

section Blocks

variable (k : Type) [CommRing k] (a b : ℕ)

def blk : Matrix (Fin a) (Fin a) k × Matrix (Fin b) (Fin b) k →+*
    Matrix (Fin (a + b)) (Fin (a + b)) k :=
  (Matrix.reindexAlgEquiv k k finSumFinEquiv).toRingEquiv.toRingHom.comp
    { toFun := fun p => Matrix.fromBlocks p.1 0 0 p.2
      map_one' := Matrix.fromBlocks_one
      map_mul' := fun p q => by simp [Matrix.fromBlocks_multiply]
      map_zero' := by simp
      map_add' := fun p q => by simp [Matrix.fromBlocks_add] }

variable {k a b}

theorem blk_apply (p : Matrix (Fin a) (Fin a) k × Matrix (Fin b) (Fin b) k) :
    blk k a b p = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks p.1 0 0 p.2) :=
  rfl

theorem blk_smul (c : k) (p : Matrix (Fin a) (Fin a) k × Matrix (Fin b) (Fin b) k) :
    blk k a b (c • p) = c • blk k a b p := by
  rw [blk_apply, blk_apply]
  ext i j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.smul_apply, Prod.smul_fst,
    Prod.smul_snd]
  rcases finSumFinEquiv.symm i with i | i <;> rcases finSumFinEquiv.symm j with j | j <;> simp

theorem coe_sumRep {Γ : Type} [Group Γ] (ρ : Γ →* GL (Fin a) k) (ρ' : Γ →* GL (Fin b) k) (g : Γ) :
    ((Formalism.MainNotions.SumRepresentations.At.sumRep ρ ρ' g : GL (Fin (a + b)) k) : Matrix (Fin (a + b)) (Fin (a + b)) k) =
      blk k a b ((ρ g : Matrix (Fin a) (Fin a) k), (ρ' g : Matrix (Fin b) (Fin b) k)) :=
  rfl

end Blocks

theorem isNilpotent_pair {R S : Type*} [MonoidWithZero R] [MonoidWithZero S] {x : R} {y : S}
    (hx : IsNilpotent x) (hy : IsNilpotent y) : IsNilpotent (x, y) := by
  obtain ⟨m, hm⟩ := hx
  obtain ⟨n, hn⟩ := hy
  exact ⟨m + n, Prod.ext (by simp [pow_add, hm]) (by simp [pow_add, hn])⟩

theorem exp_pair {R S : Type*} [Ring R] [Ring S] [Module ℚ R] [Module ℚ S] {x : R} {y : S}
    (hx : IsNilpotent x) (hy : IsNilpotent y) : exp (x, y) = (exp x, exp y) := by
  have hp := isNilpotent_pair hx hy
  exact Prod.ext (map_exp hp (RingHom.fst R S)) (map_exp hp (RingHom.snd R S))

def eqv (a b : ℕ) : ((Fin a → ℂ) × (Fin b → ℂ)) ≃ₗ[ℂ] (Fin (a + b) → ℂ) :=
  (LinearEquiv.sumArrowLequivProdArrow (Fin a) (Fin b) ℂ ℂ).symm.trans
    (LinearEquiv.funCongrLeft ℂ ℂ finSumFinEquiv.symm)

theorem eqv_toEndC {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a b : ℕ}
    (M : Matrix (Fin a) (Fin a) (Qbar l)) (M' : Matrix (Fin b) (Fin b) (Qbar l))
    (v : (Fin a → ℂ) × (Fin b → ℂ)) :
    eqv a b ((toEndC ι M).prodMap (toEndC ι M') v) = toEndC ι (blk _ a b (M, M')) (eqv a b v) := by
  obtain ⟨v1, v2⟩ := v
  funext i
  obtain ⟨k, rfl⟩ := finSumFinEquiv.surjective i
  simp only [eqv, LinearEquiv.trans_apply, toEndC_apply, blk_apply, Matrix.reindex_apply,
    Matrix.toLin'_apply, LinearMap.prodMap_apply, LinearEquiv.funCongrLeft_apply]
  rw [← Matrix.submatrix_map, Matrix.submatrix_mulVec_equiv]
  rcases k with k | k <;> simp [Matrix.fromBlocks_map, Matrix.fromBlocks_mulVec, Function.comp_def,
    LinearEquiv.sumArrowLequivProdArrow_symm_apply_inl, LinearEquiv.sumArrowLequivProdArrow_symm_apply_inr]

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
variable {l : ℕ} [Fact l.Prime] {a b : ℕ}

theorem isMonodromy_sum {t : Ine (F := E) A →* Multiplicative ℤ_[l]}
    {ρ : G E Ω →* GL (Fin a) (Qbar l)} {ρ' : G E Ω →* GL (Fin b) (Qbar l)}
    {N : Matrix (Fin a) (Fin a) (Qbar l)} {N' : Matrix (Fin b) (Fin b) (Qbar l)}
    (hN : IsMonodromy t ρ N) (hN' : IsMonodromy t ρ' N') :
    IsMonodromy t (Formalism.MainNotions.SumRepresentations.At.sumRep ρ ρ') (blk _ a b (N, N')) := by
  obtain ⟨h1, U, hU, H⟩ := hN
  obtain ⟨h1', U', hU', H'⟩ := hN'
  have hp := isNilpotent_pair h1 h1'
  refine ⟨hp.map _, U ⊓ U', hU.inter hU', fun σ hσ => ?_⟩
  rw [coe_sumRep, H σ hσ.1, H' σ hσ.2, ← blk_smul, ← map_exp (hp.smul _), Prod.smul_mk,
    exp_pair (h1.smul _) (h1'.smul _)]

theorem wdMat_sum {t : Ine (F := E) A →* Multiplicative ℤ_[l]} {φ : Weil h} (hφ : deg φ = 1)
    {ρ : G E Ω →* GL (Fin a) (Qbar l)} {ρ' : G E Ω →* GL (Fin b) (Qbar l)}
    {N : Matrix (Fin a) (Fin a) (Qbar l)} {N' : Matrix (Fin b) (Fin b) (Qbar l)}
    (h1 : IsNilpotent N) (h1' : IsNilpotent N') (g : Weil h) :
    wdMat t hφ (Formalism.MainNotions.SumRepresentations.At.sumRep ρ ρ') (blk _ a b (N, N')) g =
      blk _ a b (wdMat t hφ ρ N g, wdMat t hφ ρ' N' g) := by
  have hp := isNilpotent_pair h1 h1'
  rw [wdMat, wdMat, wdMat, coe_sumRep, ← blk_smul, ← map_exp (hp.smul _), ← map_mul, Prod.smul_mk,
    exp_pair (h1.smul _) (h1'.smul _)]
  rfl

theorem isFrobSS_sum {V V' : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V']
    {ρ₁ : Weil h → Module.End ℂ V} {N₁ : Module.End ℂ V} {x : WDRep h V}
    {ρ₂ : Weil h → Module.End ℂ V'} {N₂ : Module.End ℂ V'} {y : WDRep h V'}
    (hx : IsFrobSS ρ₁ N₁ x) (hy : IsFrobSS ρ₂ N₂ y) :
    IsFrobSS (fun g => (ρ₁ g).prodMap (ρ₂ g)) (N₁.prodMap N₂) (x.sum y) := by
  refine ⟨by rw [WDRep.sum_N, hx.1, hy.1], fun g => ⟨?_, ?_⟩⟩
  · rw [WDRep.sum_ρ]
    have hc : Commute ((x.ρ g, y.ρ g) : Module.End ℂ V × Module.End ℂ V') (ρ₁ g, ρ₂ g) :=
      Prod.ext (hx.2 g).1.eq (hy.2 g).1.eq
    exact hc.map (LinearMap.prodMapRingHom ℂ V V')
  · rw [WDRep.sum_ρ]
    have hn := (isNilpotent_pair (hx.2 g).2 (hy.2 g).2).map (LinearMap.prodMapRingHom ℂ V V')
    have e : (ρ₁ g).prodMap (ρ₂ g) - (x.ρ g).prodMap (y.ρ g) =
        LinearMap.prodMapRingHom ℂ V V' (ρ₁ g - x.ρ g, ρ₂ g - y.ρ g) := by
      rw [← Prod.mk_sub_mk, map_sub]; rfl
    show IsNilpotent ((ρ₁ g).prodMap (ρ₂ g) - (x.ρ g).prodMap (y.ρ g))
    rw [e]; exact hn

theorem wdOf_sumRep (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (ι : Qbar l ≃+* ℂ)
    (ρ : G E Ω →* GL (Fin a) (Qbar l)) (ρ' : G E Ω →* GL (Fin b) (Qbar l))
    (hc : Continuous fun g => ((ρ g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)))
    (hc' : Continuous fun g => ((ρ' g : GL (Fin b) (Qbar l)) : Matrix (Fin b) (Fin b) (Qbar l))) :
    wdOf h hl ι (Formalism.MainNotions.SumRepresentations.At.sumRep ρ ρ') = (wdOf h hl ι ρ).lpSum (wdOf h hl ι ρ') := by
  have ht := isTameChar_tameL h hl
  obtain ⟨N, hN⟩ := exists_isMonodromy h hl ht hc
  obtain ⟨N', hN'⟩ := exists_isMonodromy h hl ht hc'
  have hS := isMonodromy_sum hN hN'
  obtain ⟨x, hx⟩ := hN.exists_isFrobSS hl ht (deg_frob (h := h)) ι
  obtain ⟨y, hy⟩ := hN'.exists_isFrobSS hl ht (deg_frob (h := h)) ι
  obtain ⟨z, hz⟩ := hS.exists_isFrobSS hl ht (deg_frob (h := h)) ι
  rw [IsWDOf.wdOf_eq hl ⟨_, ht, _, deg_frob, N, x, hN, hx, rfl⟩,
    IsWDOf.wdOf_eq hl ⟨_, ht, _, deg_frob, N', y, hN', hy, rfl⟩,
    IsWDOf.wdOf_eq hl ⟨_, ht, _, deg_frob, _, z, hS, hz, rfl⟩, WD.lpSum_mk]
  refine (WD.sound ((isFrobSS_sum hx hy).iso hz (eqv a b) (fun g v => ?_) fun v => ?_)).symm
  · rw [wdMat_sum deg_frob hN.1 hN'.1]
    exact eqv_toEndC ι _ _ v
  · exact eqv_toEndC ι _ _ v

end GlobalTheory.WeilDeligne.SumParam

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
open Formalism.BasicNotions.Loc
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.WeilDeligne.wdOf_sumRep_awayFrom : ∀ (D : D7) (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a b : ℕ) (ρ : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l)) (ρ' : G D.host.E D.nd.Om →* GL (Fin b) (Qbar l)) (w : PlE D.host) (hw : ((l : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal), Continuous (fun g => ((ρ g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l))) → Continuous (fun g => ((ρ' g : GL (Fin b) (Qbar l)) : Matrix (Fin b) (Fin b) (Qbar l))) → GlobalTheory.WeilDeligne.wdOf (D.nd.plOm.2 w) hw ι (Formalism.MainNotions.SumRepresentations.At.sumRep ρ ρ') = (GlobalTheory.WeilDeligne.wdOf (D.nd.plOm.2 w) hw ι ρ).lpSum (GlobalTheory.WeilDeligne.wdOf (D.nd.plOm.2 w) hw ι ρ') :=
  fun D l _ ι a b ρ ρ' w hw hc hc' =>
    GlobalTheory.WeilDeligne.SumParam.wdOf_sumRep (h := D.nd.plOm.2 w) hw ι ρ ρ' hc hc'
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
open Formalism.BasicNotions.Loc
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.DirectSumLocal

open Module

noncomputable def splitEquiv (k : Type) [Field k] (a b : ℕ) : (Fin (a + b) → k) ≃ₗ[k] (Fin a → k) × (Fin b → k) :=
  (LinearEquiv.funCongrLeft k k finSumFinEquiv).trans (LinearEquiv.sumArrowLequivProdArrow (Fin a) (Fin b) k k)

theorem splitEquiv_sumRep {Γ k : Type} [Group Γ] [Field k] {a b : ℕ} (r₁ : Γ →* GL (Fin a) k)
    (r₂ : Γ →* GL (Fin b) k) (g : Γ) (v : Fin (a + b) → k) :
    splitEquiv k a b ((Formalism.MainNotions.SumRepresentations.At.sumRep r₁ r₂ g : Matrix _ _ k).mulVec v) =
      (((r₁ g : Matrix _ _ k)).mulVec (splitEquiv k a b v).1, ((r₂ g : Matrix _ _ k)).mulVec (splitEquiv k a b v).2) := by
  ext i
  · simp [splitEquiv, Formalism.MainNotions.SumRepresentations.At.sumRep, Formalism.MainNotions.SumRepresentations.At.blkHom, Matrix.mulVec, dotProduct, Fin.sum_univ_add, Matrix.fromBlocks]
    rfl
  · simp [splitEquiv, Formalism.MainNotions.SumRepresentations.At.sumRep, Formalism.MainNotions.SumRepresentations.At.blkHom, Matrix.mulVec, dotProduct, Fin.sum_univ_add, Matrix.fromBlocks]
    rfl

end GlobalTheory.DirectSumLocal

namespace GlobalTheory.DirectSumLocal

theorem isdRE_sumRep_and_multE_add : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (E Ω : Type) [Field E] [Field Ω] [Algebra E Ω] (Gw : Subgroup (Ω ≃ₐ[E] Ω)) (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O) (LL' : FinExt l) (a b : ℕ) (r₁ : ↥Gw →* GL (Fin a) ↥LL'.1) (r₂ : ↥Gw →* GL (Fin b) ↥LL'.1), (Bw.IsdRE P LL' (Formalism.MainNotions.SumRepresentations.At.sumRep r₁ r₂) ↔ Bw.IsdRE P LL' r₁ ∧ Bw.IsdRE P LL' r₂) ∧ ∀ (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1) (c : ℤ), Bw.multE P LL' (Formalism.MainNotions.SumRepresentations.At.sumRep r₁ r₂) τ' c = Bw.multE P LL' r₁ τ' c + Bw.multE P LL' r₂ τ' c := by
  intro l _ P AI hT E Ω _ _ _ Gw O _ _ _ Bw LL' a b r₁ r₂
  obtain ⟨T⟩ := hT
  have he : ∀ g v, splitEquiv (↥LL'.1) a b (Bw.repE LL' (Formalism.MainNotions.SumRepresentations.At.sumRep r₁ r₂) g v) =
      (Bw.repE LL' r₁ g (splitEquiv (↥LL'.1) a b v).1, Bw.repE LL' r₂ g (splitEquiv (↥LL'.1) a b v).2) := by
    intro g v
    exact splitEquiv_sumRep r₁ r₂ _ v
  obtain ⟨h1, -, h3⟩ := GlobalTheory.Per.DirectSumHT.directSum_hodgeTate l P AI T Bw.Kw LL' (Fin (a + b) → ↥LL'.1)
    (Bw.repE LL' (Formalism.MainNotions.SumRepresentations.At.sumRep r₁ r₂)) (Fin a → ↥LL'.1) (Bw.repE LL' r₁) (Fin b → ↥LL'.1)
    (Bw.repE LL' r₂) (splitEquiv (↥LL'.1) a b) he
  refine ⟨?_, fun τ' c => h3 τ' c⟩
  unfold Formalism.BasicNotions.LocBridge.IsdRE
  unfold Formalism.MainNotions.N.IsDR at h1
  simpa only [Module.finrank_fin_fun] using h1

end GlobalTheory.DirectSumLocal
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCGal

open Formalism.MainNotions.SumRepresentations.At GlobalTheory.TwistLG

section Rep

variable {Γ : Type} [Group Γ] {k : Type} [Field k] {a b : ℕ}

theorem sumRep_val (ρ : Γ →* GL (Fin a) k) (ρ' : Γ →* GL (Fin b) k) (g : Γ) :
    ((sumRep ρ ρ' g : GL (Fin (a + b)) k) : Matrix (Fin (a + b)) (Fin (a + b)) k) =
      Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (ρ g : Matrix (Fin a) (Fin a) k) 0 0 (ρ' g : Matrix (Fin b) (Fin b) k)) := rfl

theorem cont_sumRep [TopologicalSpace Γ] [TopologicalSpace k] [IsTopologicalRing k]
    (ρ : Γ →* GL (Fin a) k) (ρ' : Γ →* GL (Fin b) k)
    (c : Continuous fun g => ((ρ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k))
    (c' : Continuous fun g => ((ρ' g : GL (Fin b) k) : Matrix (Fin b) (Fin b) k)) :
    Continuous fun g => ((sumRep ρ ρ' g : GL (Fin (a + b)) k) : Matrix (Fin (a + b)) (Fin (a + b)) k) := by
  simp only [sumRep_val]
  exact (c.matrix_fromBlocks continuous_const continuous_const c').matrix_reindex _ _

theorem ss_sumRep (ρ : Γ →* GL (Fin a) k) (ρ' : Γ →* GL (Fin b) k) (h : IsSSRep ρ) (h' : IsSSRep ρ') :
    IsSSRep (sumRep ρ ρ') := by
  refine GlobalTheory.Proof.SemisimpleRepresentationIntegralConjugate.isSSRep_of_prod ((LinearEquiv.funCongrLeft k k finSumFinEquiv).trans
      (LinearEquiv.sumArrowLequivProdArrow _ _ k k)) (fun g v => ?_) h h'
  rw [sumRep_val]
  ext i <;>
    simp [Matrix.submatrix_mulVec_equiv, Matrix.fromBlocks_mulVec, LinearMap.funLeft]
  all_goals rfl

theorem ss_zero (ρ : Γ →* GL (Fin 0) k) : IsSSRep ρ := fun W _ =>
  ⟨⊥, fun g v hv => by simp [Subsingleton.elim v 0], by rw [Subsingleton.elim W ⊤]; exact isCompl_top_bot⟩

end Rep

section Glob

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N) (i : N.Loc)

theorem eq_lpZero {w : PlE H} (x : A.LP w) (hu : A.unr x) (hd : A.lpDim x = 0) : x = A.lpZero w := by
  have h1 : A.frobEig x = 0 := Multiset.card_eq_zero.1 (by rw [A.frobEig_card _ hu, hd])
  have h2 := A.unr_eq_lpUnr _ (A.lpZero_unr w)
  rw [A.frobEig_zero] at h2
  rw [A.unr_eq_lpUnr _ hu, h1, h2]

theorem lpTw_lpZero (w : PlE H) (c : ℝ) : A.lpTw (A.lpZero w) c = A.lpZero w :=
  eq_lpZero N A _ ((A.unr_tw _ _).2 (A.lpZero_unr w)) (by rw [A.lpDim_tw, A.lpDim_zero])

theorem param_int (hLP : TieLP N A) {a : ℕ} (π : A.CG a) (w : PlE H) (u t : ℝ) :
    A.lpChar (A.lpChar (A.lpTw (A.locG π w) u) (A.lpTw (A.locG A.etaT w) (1 / 2)))
      (A.lpTw (A.locG A.etaTinv w) (t - 1 / 2)) = A.lpTw (A.locG π w) (u + t) := by
  have d1 : A.lpDim (A.locG A.etaT w) = 1 := A.locG_dim _ w
  have d2 : A.lpDim (A.locG A.etaTinv w) = 1 := A.locG_dim _ w
  set X := A.lpTw (A.locG π w) u
  have c3a := (hLP w (A.lpChar X (A.lpTw (A.locG A.etaT w) (1 / 2))) (A.lpZero w) (A.locG A.etaTinv w)
    (A.locG A.etaTinv w) (t - 1 / 2) d2 d2).2.2.1
  have c3b := (hLP w X (A.lpZero w) (A.locG A.etaT w) (A.locG A.etaT w) (1 / 2) d1 d1).2.2.1
  have c2 := (hLP w (A.lpChar X (A.locG A.etaT w)) (A.lpZero w) (A.locG A.etaTinv w) (A.locG A.etaTinv w)
    (1 / 2) d2 d2).2.1
  have c4 := (hLP w X (A.lpZero w) (A.locG A.etaT w) (A.locG A.etaTinv w) 0 d1 d2).2.2.2.1
  have c5 := (hLP w X (A.lpZero w) (A.locG A.etaT w) (A.locG A.etaTinv w) 0 d1 d2).2.2.2.2.1
  rw [c3a, c3b, c2, c4, etaT_char_etaTinv N A w, c5, A.lpTw_add, A.lpTw_add]
  congr 1
  ring

end Glob

section Piece

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N) (i : N.Loc)

theorem eta_alg (hAut : TieAut N A) (m : ℤ) (τ : H.E →+* ℂ) :
    (∀ z ∈ A.infG A.etaT τ, ∃ k : ℤ, z + (((m : ℝ) + 1 / 2 : ℝ) : ℂ) = (k : ℂ)) ∧
    (∀ z ∈ A.infG A.etaTinv τ, ∃ k : ℤ, z + (((m : ℝ) + 1 / 2 : ℝ) : ℂ) = (k : ℂ)) := by
  obtain ⟨h1, h2⟩ := hAut.2.1 τ
  rw [h2]
  rcases h1 with h1 | h1 <;> rw [h1] <;> refine ⟨fun z hz => ?_, fun z hz => ?_⟩ <;>
    simp only [Multiset.map_singleton, Multiset.mem_singleton] at hz <;> subst hz
  · exact ⟨m + 1, by push_cast; ring⟩
  · exact ⟨m, by push_cast; ring⟩
  · exact ⟨m, by push_cast; ring⟩
  · exact ⟨m + 1, by push_cast; ring⟩

end Piece

section List

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N) (i : N.Loc)

end List

end GlobalTheory.BCGal

end
end
