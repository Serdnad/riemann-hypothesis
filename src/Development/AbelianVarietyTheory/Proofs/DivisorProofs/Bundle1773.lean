module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle545
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle543
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle715
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle793
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle883
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle021
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1735
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle544
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle641
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle642
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle885
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle029
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle031
public import Development.AbelianVarietyTheory.Definitions.Divisors.LinearIndependentPullChart
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle033
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1738
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1737
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1610
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1739
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.QuasiAffine
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.LocallyConstant.Algebra
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBoundedPolesGlobalData
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle050
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038

@[expose] public section

section

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

noncomputable section

namespace GlobalTheory.KSp.WeylCellRel

variable {F : Type} [Field F] {E : Type} [Field E] [Algebra F E] (c : E →ₐ[F] E)
  {ν : Type} [Fintype ν] [DecidableEq ν]

theorem mat_mul (p q : UG c (stdJ ν E)) : mat c (p * q) = mat c p * mat c q := rfl

theorem mat_weyl_inv : mat c (weyl c ν)⁻¹ = -stdJ ν E := rfl

theorem mat_unip_inv (b : Matrix ν ν E) (hb : (b.map c)ᵀ = b) : mat c (unip c b hb)⁻¹ = fromBlocks 1 (-b) 0 1 := rfl

theorem mat_weyl : mat c (weyl c ν) = fromBlocks 0 1 (-1) 0 := rfl

theorem mat_levi (hc : ∀ z, c (c z) = z) (a : GL ν E) :
    mat c (levi c hc a) = fromBlocks (a : Matrix ν ν E) 0 0 (((a⁻¹ : GL ν E) : Matrix ν ν E).map c)ᵀ := rfl

theorem mat_unip (b : Matrix ν ν E) (hb : (b.map c)ᵀ = b) : mat c (unip c b hb) = fromBlocks 1 b 0 1 := rfl

theorem splitUnitaryElementMatrix_bigCell_product (b : Matrix ν ν E) (hb : (b.map c)ᵀ = b) (hb0 : b.det ≠ 0) (hb' : ((-b⁻¹).map c)ᵀ = -b⁻¹) :
    mat c (weyl c ν * unip c b hb * weyl c ν * (unip c (-b⁻¹) hb')⁻¹ * (weyl c ν)⁻¹) =
      fromBlocks (-b⁻¹) 1 0 (-b) := by
  have h1 : b * b⁻¹ = 1 := mul_nonsing_inv b (isUnit_iff_ne_zero.mpr hb0)
  rw [mat_mul, mat_mul, mat_mul, mat_mul, mat_weyl_inv, mat_unip_inv, mat_unip, mat_weyl]
  simp only [stdJ, fromBlocks_multiply, fromBlocks_neg, h1]
  simp [h1]

theorem conj_levi_mem (hc : ∀ z, c (c z) = z) (a : GL ν E) :
    weyl c ν * levi c hc a * (weyl c ν)⁻¹ ∈ sieg c ν := by
  rw [mem_sieg, mat_mul, mat_mul, mat_weyl_inv, mat_weyl, mat_levi]
  simp [stdJ, fromBlocks_multiply, fromBlocks_neg]

theorem herm_neg_inv (b : Matrix ν ν E) (hb : (b.map c)ᵀ = b) (hb0 : b.det ≠ 0) : ((-b⁻¹).map c)ᵀ = -b⁻¹ := by
  have h1 : ((b⁻¹).map c)ᵀ * b = 1 := by
    have h3 : ((b⁻¹).map c)ᵀ * (b.map c)ᵀ = 1 := by
      rw [← transpose_mul, ← Matrix.map_mul (f := c), mul_nonsing_inv b (isUnit_iff_ne_zero.mpr hb0),
        Matrix.map_one _ (map_zero c) (map_one c), transpose_one]
    rwa [hb] at h3
  have h2 : ((b⁻¹).map c)ᵀ = b⁻¹ := (Matrix.inv_eq_left_inv h1).symm
  rw [Matrix.map_neg _ (map_neg c), transpose_neg, h2]

theorem lower_left (hc : ∀ z, c (c z) = z) (a : GL ν E) (b : Matrix ν ν E) (hb : (b.map c)ᵀ = b) :
    (mat c (weyl c ν * (levi c hc a * unip c b hb) * weyl c ν)).toBlocks₂₁ = (a : Matrix ν ν E) * b := by
  rw [mat_mul, mat_mul, mat_mul, mat_weyl, mat_levi, mat_unip]
  simp [fromBlocks_multiply]

end GlobalTheory.KSp.WeylCellRel

theorem GlobalTheory.KSp.WeylCellRel.gauss_const_ne_zero : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) (χ : Eˣ →* Circle) (_ : Continuous χ) (_ : ResEtaPow (R := F) ⊥ χ (Fintype.card α)) [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)] (μ : Measure (Matrix α ν E)) [μ.IsAddHaarMeasure] (γ₀ : ℂ), (∀ b : Matrix ν ν E, (b.map c)ᵀ = b → b.det ≠ 0 → HasGauss μ (fun x => ψ (2⁻¹ * pr c Q x (x * b))) (γ₀ * sc F χ (Fintype.card α) b.det⁻¹)) → γ₀ ≠ 0 := by
  intro F _ _ _ _ _ E _ _ _ _ c δ hE α _ _ ν _ _ Q hQ ψ hψ hψ1 hψne χ hχ hres _ _ μ _ γ₀ hγ hγ0
  obtain ⟨hfd, -, -, -, -, -, -, hmat⟩ := GlobalTheory.T.quadExt_topological_properties F E c δ hE
  obtain ⟨hmt, hgood⟩ := hmat α ν
  haveI : FiniteDimensional F (Matrix α ν E) := inferInstance
  obtain ⟨β, hβ, hsymm, hnd, -, -⟩ := GlobalTheory.T.hermitianMatrixColumnPairing_algebraic_properties F E c δ hE α ν Q hQ
  have hpair := GlobalTheory.T.isSelfDualBicharacterPairing_of_symmBilinForm F (Matrix α ν E) ψ hψ hψ1 hψne β hsymm hnd
  have hfou : ∀ f, fou c ψ Q μ f = four μ (fun x y => ψ (β x y)) f := by
    intro f
    have hfe : (fun x y => ψ (β x y)) = (fun x y => ψ (pr c Q x y)) := by funext x y; rw [hβ]
    rw [hfe]; rfl
  obtain ⟨C, hC, hinv⟩ := GlobalTheory.T.bicharacterFourierTransform_twice_eq_pos_smul_reflect (Matrix α ν E) hgood μ _ hpair
  have inj : ∀ g ∈ SB (Matrix α ν E), fou c ψ Q μ g = 0 → g = 0 := by
    intro g hg h0
    funext x
    have h1 := hinv g hg (-x)
    rw [← hfou g, h0, neg_neg] at h1
    have h2 : four μ (fun x y => ψ (β x y)) (0 : Matrix α ν E → ℂ) (-x) = 0 := by simp [four]
    rw [h2] at h1
    exact (mul_eq_zero.mp h1.symm).resolve_left (by exact_mod_cast hC.ne')
  haveI := hgood.grp
  haveI := hgood.t2
  obtain ⟨L, hLc, hLo, -⟩ := hgood.small Set.univ Filter.univ_mem
  have hLcl : IsClopen (L : Set (Matrix α ν E)) :=
    ⟨AddSubgroup.isClosed_of_isOpen L hLo, hLo⟩
  set φ : Matrix α ν E → ℂ := (L : Set (Matrix α ν E)).indicator 1 with hφd
  have hφ : φ ∈ SB (Matrix α ν E) := by
    refine ⟨?_, HasCompactSupport.intro hLc fun x hx => Set.indicator_of_notMem hx _⟩
    have := (LocallyConstant.indicator (1 : LocallyConstant (Matrix α ν E) ℂ) hLcl).isLocallyConstant
    convert this using 1
    funext y
    exact (LocallyConstant.indicator_apply (1 : LocallyConstant (Matrix α ν E) ℂ) hLcl y).symm
  have hφ0 : φ 0 = 1 := by simp [hφd, Set.indicator_of_mem (zero_mem L)]
  have hfφ : fou c ψ Q μ φ ∈ SB (Matrix α ν E) := by
    rw [hfou]; exact GlobalTheory.T.bicharacterFourierTransform_mem_schwartzBruhat (Matrix α ν E) hgood μ _ hpair φ hφ
  have h1 : ((1 : Matrix ν ν E).map c)ᵀ = 1 := by
    rw [Matrix.map_one _ (map_zero c) (map_one c), transpose_one]
  have hu : unip c 1 h1 ∈ sieg c ν := by rw [mem_sieg, WeylCellRel.mat_unip]; simp
  have hg := GlobalTheory.T.siegelParabolic_preserves_schwartzBruhat F E c δ hE α ν Q hQ ψ hψ hψ1 hψne χ hχ hres (unip c 1 h1) hu _ hfφ
  obtain ⟨sc1, scmul, -⟩ := GlobalTheory.T.unitaryCharacterAbsScalar_basic_properties F E c δ hE (Fintype.card α) χ hres
  have sc_ne : ∀ z : E, z ≠ 0 → sc F χ (Fintype.card α) z ≠ 0 := fun z hz h => by
    have h' := scmul z z⁻¹
    rw [mul_inv_cancel₀ hz, sc1, h, zero_mul] at h'
    exact one_ne_zero h'
  have br := GlobalTheory.T.fourier_hermitianMultiplier_braid_relation F E c δ hE α ν Q hQ ψ hψ hψ1 hψne χ hχ hres μ 1 _ h1 (by simp)
    (hγ 1 h1 (by simp)) φ hφ
  rw [hγ0, zero_mul, zero_smul] at br
  have hs : sc F χ (Fintype.card α) (-(1 : Matrix ν ν E)⁻¹).det ≠ 0 := sc_ne _ (by simp [det_neg])
  have hX := (smul_eq_zero.mp br).resolve_left hs
  have hpar0 := inj _ hg hX
  apply one_ne_zero (α := ℂ)
  rw [← hφ0]
  have hF0 : fou c ψ Q μ φ = 0 := by
    funext x
    have h2 := congrFun hpar0 x
    have hψ0 : ∀ t, ψ t ≠ 0 := by
      intro t h4; have := hψ1 t; rw [h4, norm_zero] at this; exact zero_ne_one this
    simpa [parFun, WeylCellRel.mat_unip, sc1, hψ0] using h2
  rw [inj φ hφ hF0]; rfl

theorem GlobalTheory.KSp.weyl_cell_relation : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) (χ : Eˣ →* Circle) (_ : Continuous χ) (_ : ResEtaPow (R := F) ⊥ χ (Fintype.card α)) [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)] (μ : Measure (Matrix α ν E)) [μ.IsAddHaarMeasure], ∃ κ : ℂ, κ ≠ 0 ∧ ∀ p ∈ sieg c ν, InCell c (weyl c ν * p * weyl c ν) → ∃ p₁ ∈ sieg c ν, ∃ p₂ ∈ sieg c ν, weyl c ν * p * weyl c ν = p₁ * weyl c ν * p₂ ∧ ∀ φ ∈ SB (Matrix α ν E), κ • fou c ψ Q μ (parFun c ψ χ Q (mat c p) (κ • fou c ψ Q μ φ)) = parFun c ψ χ Q (mat c p₁) (κ • fou c ψ Q μ (parFun c ψ χ Q (mat c p₂) φ)) := by
  intro F _ _ _ _ _ E _ _ _ _ c δ hE α _ _ ν _ _ Q hQ ψ hψ hψ1 hψne χ hχ hres _ _ μ _
  obtain ⟨γ₀, hγ⟩ := GlobalTheory.T.hasGaussIntegral_hermitian_quadratic_character F E c δ hE α ν Q hQ ψ hψ hψ1 hψne χ hχ hres μ
  have hγ0 : γ₀ ≠ 0 :=
    GlobalTheory.KSp.WeylCellRel.gauss_const_ne_zero F E c δ hE α ν Q hQ ψ hψ hψ1 hψne χ hχ hres μ γ₀ hγ
  obtain ⟨sc1, scmul, -⟩ := GlobalTheory.T.unitaryCharacterAbsScalar_basic_properties F E c δ hE (Fintype.card α) χ hres
  have sc_ne : ∀ z : E, z ≠ 0 → sc F χ (Fintype.card α) z ≠ 0 := fun z hz h => by
    have h' := scmul z z⁻¹
    rw [mul_inv_cancel₀ hz, sc1, h, zero_mul] at h'
    exact one_ne_zero h'
  have hs1 : sc F χ (Fintype.card α) (-1 : Matrix ν ν E).det ≠ 0 := sc_ne _ (by simp [det_neg])
  refine ⟨sc F χ (Fintype.card α) (-1 : Matrix ν ν E).det / γ₀, div_ne_zero hs1 hγ0, ?_⟩
  intro p hp hcell
  obtain ⟨-, -, a, b, hb, rfl⟩ := GlobalTheory.T.splitUnitarySiegelParabolic_block_relations F E c δ hE ν p hp
  have hb0 : b.det ≠ 0 := by
    have h := (GlobalTheory.T.inCell_iff_det_lower_left_block_ne_zero F E c δ hE ν _).mp hcell
    rw [WeylCellRel.lower_left, det_mul] at h
    exact right_ne_zero_of_mul h
  have hb' := WeylCellRel.herm_neg_inv c b hb hb0
  have hunip : ∀ (b' : Matrix ν ν E) (h' : (b'.map c)ᵀ = b'), unip c b' h' ∈ sieg c ν := by
    intro b' h'; rw [mem_sieg, WeylCellRel.mat_unip]; simp
  have hlevi : levi c hE.invol a ∈ sieg c ν := by rw [mem_sieg, WeylCellRel.mat_levi]; simp
  obtain ⟨q, hqd⟩ : ∃ q, q = weyl c ν * levi c hE.invol a * (weyl c ν)⁻¹ := ⟨_, rfl⟩
  obtain ⟨p₀, hp0d⟩ : ∃ p₀, p₀ = weyl c ν * unip c b hb * weyl c ν * (unip c (-b⁻¹) hb')⁻¹ * (weyl c ν)⁻¹ :=
    ⟨_, rfl⟩
  have hq : q ∈ sieg c ν := hqd ▸ WeylCellRel.conj_levi_mem c hE.invol a
  have hp0m : mat c p₀ = fromBlocks (-b⁻¹) 1 0 (-b) := hp0d ▸ WeylCellRel.splitUnitaryElementMatrix_bigCell_product c b hb hb0 hb'
  have hp0 : p₀ ∈ sieg c ν := by rw [mem_sieg, hp0m]; simp
  refine ⟨q * p₀, mul_mem hq hp0, unip c (-b⁻¹) hb', hunip _ _, by rw [hqd, hp0d]; group, ?_⟩
  intro φ hφ
  obtain ⟨-, pm⟩ := GlobalTheory.T.parFun_sieg_mul' F E c δ hE α ν Q hQ ψ hψ hψ1 hψne χ hχ hres
  have fl := GlobalTheory.T.fourier_intertwines_siegelLeviOperator F E c δ hE α ν Q hQ ψ hψ hψ1 hψne χ hχ hres μ (levi c hE.invol a) hlevi q hq
    (by rw [hqd]; group)
  have br := GlobalTheory.T.fourier_hermitianMultiplier_braid_relation F E c δ hE α ν Q hQ ψ hψ hψ1 hψne χ hχ hres μ b _ hb hb0 (hγ b hb hb0) φ hφ
  rw [← WeylCellRel.mat_unip c b hb, ← WeylCellRel.mat_unip c (-b⁻¹) hb', ← hp0m] at br
  have pf_smul : ∀ (g : Matrix (ν ⊕ ν) (ν ⊕ ν) E) (k : ℂ) (f : Matrix α ν E → ℂ),
      parFun c ψ χ Q g (k • f) = k • parFun c ψ χ Q g f := by
    intro g k f; funext x; simp only [parFun, Pi.smul_apply, smul_eq_mul]; ring
  have fou_smul : ∀ (k : ℂ) (f : Matrix α ν E → ℂ), fou c ψ Q μ (k • f) = k • fou c ψ Q μ f := by
    intro k f; funext x; simp only [fou, four, Pi.smul_apply, smul_eq_mul]
    rw [← integral_const_mul]; congr 1; funext y; ring
  have e : (-b⁻¹ : Matrix ν ν E).det = (-1 : Matrix ν ν E).det * b.det⁻¹ := by
    rw [← neg_one_mul, det_mul, det_nonsing_inv, Ring.inverse_eq_inv']
  have hκγ : sc F χ (Fintype.card α) (-1 : Matrix ν ν E).det / γ₀ * (γ₀ * sc F χ (Fintype.card α) b.det⁻¹) =
      sc F χ (Fintype.card α) (-b⁻¹).det := by
    rw [e, scmul]; field_simp
  have hs : sc F χ (Fintype.card α) (-b⁻¹).det ≠ 0 := sc_ne _ (by
    rw [e]; exact mul_ne_zero (by simp [det_neg]) (inv_ne_zero hb0))
  have hγne : γ₀ * sc F χ (Fintype.card α) b.det⁻¹ ≠ 0 := by
    intro h; rw [h, mul_zero] at hκγ; exact hs hκγ.symm
  set κ := sc F χ (Fintype.card α) (-1 : Matrix ν ν E).det / γ₀ with hκ
  have key : κ • fou c ψ Q μ (parFun c ψ χ Q (mat c (unip c b hb)) (fou c ψ Q μ φ)) =
      parFun c ψ χ Q (mat c p₀) (fou c ψ Q μ (parFun c ψ χ Q (mat c (unip c (-b⁻¹) hb')) φ)) := by
    apply smul_right_injective _ hγne
    simp only
    rw [smul_smul, mul_comm, hκγ, br]
  rw [pf_smul, fou_smul, pm _ hlevi _ (hunip _ _), fl, ← pf_smul, key, pf_smul, pm _ hq _ hp0]

end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechPer

theorem isReg_of_isReg_sub : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → ∀ (n : ℕ) (W : Fin n → A.left.Opens) (r : ∀ k, Fin n → Γ(A.left, W k)), IsRatioCover u.ex W r → ∀ (h : Fin n → (Fin g → ℂ) → ℂ), (∀ k, DifferentiableOn ℂ (h k) (pre u.ex (W k))) → (∀ k (l : u.Λ), ∀ z ∈ pre u.ex (W k), h k (z + l) = h k z) → (∀ k j, IsReg u.ex (W k ⊓ W j) (h k - h j)) → ∀ k, IsReg u.ex (W k) (h k) := by
  intro A _ g L u hA n W r hr h hd hp hreg l
  obtain ⟨-, hdiff, -, hper, hinf, -, -, -, -, -, hbas, -⟩ := GlobalTheory.T.uniformisation_preimage_value_rules A g L u
  have hr' := hr
  obtain ⟨haff, -, hbo, -, hco⟩ := hr'
  have h1 : ∀ k, ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∃ b : Γ(A.left, W k), ∀ z ∈ pre u.ex (A.left.basicOpen (r k l)),
      val u.ex (W k) b z = val u.ex (W k) (r k l) z ^ N * (h k - h l) z := fun k ↦
    GlobalTheory.T.exists_pow_mul_eq_regularValue_basicOpen A g L u (W k) (haff k) (r k l) (h k - h l) (by rw [hbo]; exact hreg k l)
  choose N₀ hN₀ using h1
  set N : ℕ := Finset.univ.sup N₀ with hN
  have h2 := fun k ↦ hN₀ k N (Finset.le_sup (f := N₀) (Finset.mem_univ k))
  choose b hb using h2
  let σ : Fin n → (Fin g → ℂ) → ℂ := fun k z ↦
    val u.ex (W k) (r k l) z * (val u.ex (W k) (r k l) z ^ N * h k z - val u.ex (W k) (b k) z)
  have hin : ∀ k z, z ∈ pre u.ex (W k) → z ∈ pre u.ex (W l) → σ k z = val u.ex (W k) (r k l) z ^ (N + 1) * h l z := by
    intro k z hk hl
    have hz : z ∈ pre u.ex (A.left.basicOpen (r k l)) := by rw [hbo, hinf]; exact ⟨hk, hl⟩
    simp only [σ]
    rw [hb k z hz, Pi.sub_apply]
    ring
  have hout : ∀ k z, z ∉ pre u.ex (W l) → σ k z = 0 := by
    intro k z hl
    have hz : z ∉ pre u.ex (A.left.basicOpen (r k l)) := by rw [hbo, hinf]; exact fun hz ↦ hl hz.2
    rw [hbas, not_not] at hz
    simp only [σ]
    rw [hz, zero_mul]
  have hσ := GlobalTheory.T.isRegular_periodic_ratioCover_families A g L u hA n W r hr (N + 1) σ
    (fun k ↦ (hdiff _ (r k l)).mul ((((hdiff _ (r k l)).pow N).mul (hd k)).sub (hdiff _ (b k))))
    (fun k m z hz ↦ by simp only [σ]; rw [hper, hper, hp k m z hz])
    (fun k j z hk hj ↦ by
      by_cases hl : z ∈ pre u.ex (W l)
      · rw [hin k z hk hl, hin j z hj hl, hco k j l z hk hj]
        ring
      · rw [hout k z hl, hout j z hl, mul_zero]) l
  obtain ⟨c, hc⟩ := hσ
  refine ⟨c, fun z hz ↦ ?_⟩
  have hne : val u.ex (W l) (r l l) z ≠ 0 := by
    rw [← hbas, hbo, hinf]; exact ⟨hz, hz⟩
  have hone : val u.ex (W l) (r l l) z = 1 :=
    (mul_right_cancel₀ hne ((_root_.one_mul _).trans (hco l l l z hz hz))).symm
  rw [← hc z hz, hin l z hz hz, hone, one_pow, _root_.one_mul]

end GlobalTheory.CechPer
end

section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem flat_cohomology_baseChange {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] [Module.Flat R R']
    {A B C H H' : Type} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
    [AddCommGroup H] [Module R H] [AddCommGroup H'] [Module R' H']
    (f : A →ₗ[R] B) (g : B →ₗ[R] C) (hfg : ∀ a, g (f a) = 0)
    (θ : LinearMap.ker (g.baseChange R) →ₗ[R] H) (θ' : LinearMap.ker (g.baseChange R') →ₗ[R'] H')
    (hs : Function.Surjective θ) (hk : ∀ z, θ z = 0 ↔ z.1 ∈ LinearMap.range (f.baseChange R))
    (hs' : Function.Surjective θ') (hk' : ∀ z, θ' z = 0 ↔ z.1 ∈ LinearMap.range (f.baseChange R'))
    (p : H → H')
    (hp : ∀ z z', z'.1 = (Algebra.ofId R R').toLinearMap.rTensor B z.1 → θ' z' = p (θ z)) :
    ∃ e : R' ⊗[R] H ≃ₗ[R'] H', ∀ c, e (1 ⊗ₜ c) = p c := by
  let Z := LinearMap.ker g
  let f' : A →ₗ[R] Z := f.codRestrict Z hfg
  let i : Z →ₗ[R] LinearMap.ker (g.baseChange R) :=
    ((TensorProduct.mk R R B 1) ∘ₗ Z.subtype).codRestrict _ (fun z ↦ by
      have : g z.1 = 0 := z.2
      simp [this])
  have hi : ∀ z : Z, (i z).1 = (1 : R) ⊗ₜ[R] z.1 := fun z ↦ rfl
  have his : Function.Surjective i := by
    rintro ⟨x, hx⟩
    obtain ⟨b, rfl⟩ := (TensorProduct.lid R B).symm.surjective x
    have hb : g b = 0 := by
      have h1 : (1 : R) ⊗ₜ[R] g b = 0 := by simpa using hx
      have := congrArg (TensorProduct.lid R C) h1
      simpa using this
    exact ⟨⟨b, hb⟩, Subtype.ext (by simp [hi])⟩
  let τ : Z →ₗ[R] H := θ ∘ₗ i
  have hτs : Function.Surjective τ := hs.comp his
  have hex : Function.Exact f' τ := by
    intro z
    change θ (i z) = 0 ↔ _
    rw [hk, hi]
    constructor
    · rintro ⟨x, hx⟩
      obtain ⟨a, rfl⟩ := (TensorProduct.lid R A).symm.surjective x
      refine ⟨a, Subtype.ext ?_⟩
      have := congrArg (TensorProduct.lid R B) hx
      change f a = z.1
      simpa using this
    · rintro ⟨a, rfl⟩
      exact ⟨1 ⊗ₜ a, rfl⟩
  have hexZ : Function.Exact (Z.subtype.baseChange R') (g.baseChange R') :=
    Module.Flat.lTensor_exact R' (LinearMap.exact_subtype_ker_map g)
  have hinj : Function.Injective (Z.subtype.baseChange R') :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := R') Z.subtype Z.subtype_injective
  let j : R' ⊗[R] Z →ₗ[R'] LinearMap.ker (g.baseChange R') :=
    (Z.subtype.baseChange R').codRestrict _ (fun x ↦ hexZ.apply_apply_eq_zero x)
  have hjs : Function.Surjective j := by
    rintro ⟨x, hx⟩
    obtain ⟨y, rfl⟩ := (hexZ x).1 hx
    exact ⟨y, rfl⟩
  let a : R' ⊗[R] Z →ₗ[R'] R' ⊗[R] H := τ.baseChange R'
  let b : R' ⊗[R] Z →ₗ[R'] H' := θ' ∘ₗ j
  have has : Function.Surjective a := LinearMap.lTensor_surjective R' hτs
  have hbs : Function.Surjective b := hs'.comp hjs
  have hexa : Function.Exact (f'.baseChange R') a := lTensor_exact R' hex hτs
  have hcomp : ∀ y, Z.subtype.baseChange R' (f'.baseChange R' y) = f.baseChange R' y := by
    intro y
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp]
    rfl
  have hker : LinearMap.ker a = LinearMap.ker b := by
    ext x
    rw [LinearMap.mem_ker, LinearMap.mem_ker, hexa x]
    change _ ↔ θ' (j x) = 0
    rw [hk']
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y, (hcomp y).symm⟩
    · rintro ⟨y, hy⟩
      exact ⟨y, hinj ((hcomp y).trans hy)⟩
  refine ⟨(a.quotKerEquivOfSurjective has).symm ≪≫ₗ Submodule.quotEquivOfEq _ _ hker ≪≫ₗ
    b.quotKerEquivOfSurjective hbs, fun c ↦ ?_⟩
  obtain ⟨z, rfl⟩ := hτs c
  have h1 : (a.quotKerEquivOfSurjective has).symm ((1 : R') ⊗ₜ[R] τ z) =
      Submodule.Quotient.mk ((1 : R') ⊗ₜ[R] z) := by
    rw [LinearEquiv.symm_apply_eq]
    rfl
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, h1]
  change θ' (j (1 ⊗ₜ z)) = p (θ (i z))
  apply hp
  rw [hi, LinearMap.rTensor_tmul]
  change (1 : R') ⊗ₜ[R] z.1 = (algebraMap R R' 1) ⊗ₜ[R] z.1
  rw [map_one]

theorem exists_fin_affine_cover {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) [QuasiCompact s] :
    ∃ (n : ℕ) (D : Fin n → X.Opens), (∀ i, IsAffineOpen (D i)) ∧ ⨆ i, D i = ⊤ := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace s
  obtain ⟨S, hS, e⟩ := (isCompact_iff_finite_and_eq_biUnion_affineOpens (U := (⊤ : X.Opens))).1 isCompact_univ
  have := hS.fintype
  let q := (Fintype.equivFin S).symm
  refine ⟨_, fun i ↦ (q i).1.1, fun i ↦ (q i).1.2, ?_⟩
  rw [e]
  apply le_antisymm
  · exact iSup_le fun i ↦ le_iSup₂_of_le (q i).1 (q i).2 le_rfl
  · refine iSup₂_le fun U hU ↦ ?_
    obtain ⟨i, hi⟩ := q.surjective ⟨U, hU⟩
    exact le_iSup_of_le i (by simp only [hi]; exact le_rfl)

theorem flat_baseChange_HO : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] [Module.Flat R R'] (X X' : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (φ : X' ⟶ X) (h : IsPullback φ s' s (spMap (algebraMap R R'))), IsSeparated s → QuasiCompact s → (∃ e : R' ⊗[R] HO1 s ≃ₗ[R'] HO1 s', ∀ c, e (1 ⊗ₜ c) = pullHO1 h.w c) ∧ ∃ e : R' ⊗[R] HO2 s ≃ₗ[R'] HO2 s', ∀ c, e (1 ⊗ₜ c) = pullHO2 h.w c := by
  intro R R' _ _ _ _ X X' s s' φ h hsep hqc
  obtain ⟨n, D, hD, hcov⟩ := exists_fin_affine_cover s
  obtain ⟨M⟩ := GlobalTheory.T.orderedCech_finiteAffineCover_models_structureSheafCohomology R X s (Fin n) D hsep hD hcov
  generalize GlobalTheory.AbLaw.cechLB s (LB.triv X) D = K at M
  have h0 : IsPullback (𝟙 X) s s (spMap (algebraMap R R)) := by
    have e : spMap (algebraMap R R) = 𝟙 _ := spMap_id R
    rw [e]
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  have hdd : ∀ i j k a, (K.d j k).hom ((K.d i j).hom a) = 0 := by
    intro i j k a
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, K.d_comp_d]
    rfl
  obtain ⟨a1, a2, a3, a4⟩ := M.exact h0
  obtain ⟨b1, b2, b3, b4⟩ := M.exact h
  obtain ⟨c1, c2⟩ := M.nat h0 h (Algebra.ofId R R') φ h.w (Category.comp_id φ)
  exact ⟨flat_cohomology_baseChange _ _ (hdd 0 1 2) (M.θ1 h0) (M.θ1 h) a1 a2 b1 b2 _ c1,
    flat_cohomology_baseChange _ _ (hdd 1 2 3) (M.θ2 h0) (M.θ2 h) a3 a4 b3 b4 _ c2⟩

end GlobalTheory.AbCoh
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.hasProperSmoothDualRepresentative_of_local : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] (g : ℕ), IsAbelianScheme A → (∀ s : S, ∃ V : S.Opens, s ∈ V ∧ HasRep A g (Over.mk V.ι)) → HasRep A g (𝟙_ _) := by
  first | exact @GlobalTheory.DualCon.hasRep_of_local | exact GlobalTheory.DualCon.hasRep_of_local | (intros; apply GlobalTheory.DualCon.hasRep_of_local <;> assumption)
end

section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

theorem _root_.GlobalTheory.T.finiteHeight_sub_mean_le_degree_fullLattice_detIdeal : ∀ (F V : Type) [Field F] [NumberField F] [AddCommGroup V] [Module F V] [Module (𝓞 F) V] [IsScalarTower (𝓞 F) F V] (nm : HermFam F V) (M : Submodule (𝓞 F) V) (d : ℕ) (b : Module.Basis (Fin d) F V), IsFull M → ∀ (τ : Type) (g : MvPolynomial τ F), g ≠ 0 → (∀ m, AddMonoidAlgebra.coeff g m ∈ Submodule.span (𝓞 F) {y | ∃ v : Fin d → V, (∀ i, v i ∈ M) ∧ y = b.det v}) → finPart g - mean F (fun σ => Real.log (nm.gram σ b).det.re) / 2 ≤ deg nm M := by
  first | exact @GlobalTheory.HSShort.DetIdeal.finPart_sub_mean_le_deg | exact GlobalTheory.HSShort.DetIdeal.finPart_sub_mean_le_deg | (intros; apply GlobalTheory.HSShort.DetIdeal.finPart_sub_mean_le_deg <;> assumption)
end

section

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.DefPt MvPolynomial
open scoped Matrix

theorem _root_.GlobalTheory.T.slope_dualWeylFibreLattice_ge : ∀ (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (T : Type) [Fintype T] [DecidableEq T] (N : T → ℕ) (la : ∀ t, Fin (N t) → ℕ), (∀ t, Antitone (la t)) → ∀ (a : HeightOneSpectrum (𝓞 K) → K) (B : HeightOneSpectrum (𝓞 K) → ∀ t, Matrix (Fin (N t)) (Fin (N t)) K) (s : (K →+* ℂ) → ℝ) (X : (K →+* ℂ) → ∀ t, Matrix (Fin (N t)) (Fin (N t)) ℂ), (∀ w, a w ≠ 0) → (Function.support fun w => vAdd w (a w)).Finite → (∀ t, IsAdelic fun w => B w t) → (∀ σ, 0 < s σ) → (∀ σ t, (X σ t).det ≠ 0) → (∀ σ, s ((starRingEnd ℂ).comp σ) = s σ) → (∀ σ t, ‖(X ((starRingEnd ℂ).comp σ) t).det‖ = ‖(X σ t).det‖) → (∀ σ, (fibY la (s σ) (X σ)).det ≠ 0) ∧ lineDeg s (fun w => (vAdd w (a w) : ℝ)) + ∑ t, ((size (la t) : ℝ) / (N t : ℝ) * detDeg (fun w => B w t) (fun σ => X σ t) - Real.log (dim (la t)) / 2) ≤ slope_sq (matNorm fun σ => fibY la (s σ) (X σ)) (locLat fun w => fibA la (a w) (B w)) / 2 := by
  first | exact @GlobalTheory.FibSlope.slope_fibre_ge | exact GlobalTheory.FibSlope.slope_fibre_ge | (intros; apply GlobalTheory.FibSlope.slope_fibre_ge <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow

theorem _root_.GlobalTheory.T.liftModelParameter_decreasing_halfIntegral_width : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ i σ s, IsEmbOverK D σ s → ∀ ρ, StrictAnti ((R.MW i σ).lam ρ) ∧ (∀ a, ∃ z : ℤ, (R.MW i σ).lam ρ a - (((Wc D i).rank : ℝ) - 1) / 2 = (z : ℝ)) ∧ ∀ a b, |(R.MW i σ).lam ρ a - (R.MW i σ).lam ρ b| ≤ (degAt D i σ ρ : ℝ) + D.R.nV + 3 := by
  first | exact @GlobalTheory.LowRow.lam_par_width | exact GlobalTheory.LowRow.lam_par_width | (intros; apply GlobalTheory.LowRow.lam_par_width <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

theorem _root_.GlobalTheory.T.exists_clear_denominators_ampleHermLineBundle : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.A.B → ∀ (a : ℤ) (J : Type) [Finite J] (f : J → X.functionField), ∃ (c : ℕ) (g : X.functionField), 0 < c ∧ g ≠ 0 ∧ g ∈ P.H a c ∧ ∀ j, g * f j ∈ P.H a c := by
  first | exact @GlobalTheory.HSNef.Den.exists_clear_denominators | exact GlobalTheory.HSNef.Den.exists_clear_denominators | (intros; apply GlobalTheory.HSNef.Den.exists_clear_denominators <;> assumption)
end
