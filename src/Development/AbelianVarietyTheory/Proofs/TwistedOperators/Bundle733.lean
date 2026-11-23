module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemHatMxHomLatIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSelfDualAdelicFrameLevelOne
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ClassConditionsCoreFromMixedCoordinateFunctionStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ClassConditionsIsotropicHomFromFirstMixedCoordinStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousReprSymm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle486
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsThetaFunctionMixedCoordinateBumpMulCoreStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatMapProductDatumEqUnitriangularIntegralBumpStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle454
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelTargetBumpMulCoreThetaExistsStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle455
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldingConditionsFromSecondMixedCoordinateStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle024
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle489
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle169
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle400
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle652
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle729
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle584
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemCompletedGridArrowLatticeIffIntegralFrameMatr
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle636
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PolarisationTwistLatticeSelfDualSameStabilisers
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
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
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinTensMemLatO
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockDetBlockTriangular

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin




namespace GlobalTheory.BigRow

variable {D : D7}

private theorem smul_mem_hatMx_of_fr {m n : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    {Λ' : Submodule (𝓞 D.host.E) (Fin m → D.host.E)} {β : GL (Fin n) (Lev.EAf D)} {β' : GL (Fin m) (Lev.EAf D)}
    (hβ : Formalism.L2.DIV.IsFrame β Λ) (hβ' : Formalism.L2.DIV.IsFrame β' Λ') (𝔪 : Ideal (𝓞 D.host.E)) {a : AE D}
    (ha0 : infPart D a = 0) (ha : toEAf D a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) {z : Mx D m n}
    (hz : ∀ i j, ∃ s ∈ Formalism.L2.DIV.idS D.host.F 𝔪, s.1 = GlobalTheory.FunObj.Comparison₂.fr β' β (z.map (toEAf D)) i j) :
    a • z ∈ hatMx (𝔪 • homLat Λ Λ') := by
  rw [GlobalTheory.FunObj.HatFrame.mem_hatMx_homLat_iff D Λ Λ' β β' hβ hβ' 𝔪]
  refine ⟨fun i j => by rw [Matrix.smul_apply, smul_eq_mul, map_mul, ha0, zero_mul], fun i j => ?_⟩
  obtain ⟨s, hs, hse⟩ := hz i j
  refine ⟨⟨toEAf D a, ha⟩ * s, Ideal.mul_mem_left _ _ hs, ?_⟩
  have e2 : GlobalTheory.FunObj.Comparison₂.fr β' β ((a • z).map (toEAf D)) i j = toEAf D a * GlobalTheory.FunObj.Comparison₂.fr β' β (z.map (toEAf D)) i j := by
    simp only [GlobalTheory.FunObj.Comparison₂.fr, Matrix.mul_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul,
      Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
  exact (congrArg (toEAf D a * ·) hse).trans e2.symm

private theorem exists_frames {m n : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    {Λ' : Submodule (𝓞 D.host.E) (Fin m → D.host.E)} (hΛ : Submodule.IsFullLattice D.host.E Λ)
    (hΛ' : Submodule.IsFullLattice D.host.E Λ') :
    ∃ β : GL (Fin n) (Lev.EAf D), ∃ β' : GL (Fin m) (Lev.EAf D), Formalism.L2.DIV.IsFrame β Λ ∧ Formalism.L2.DIV.IsFrame β' Λ' := by
  obtain ⟨β, hβ⟩ := GlobalTheory.AdelicFrame.exists_isFrame D.host.F Λ hΛ.fg (Submodule.IsFullLattice.span_eq_top (self := hΛ))
  obtain ⟨β', hβ'⟩ := GlobalTheory.AdelicFrame.exists_isFrame D.host.F Λ' hΛ'.fg (Submodule.IsFullLattice.span_eq_top (self := hΛ'))
  exact ⟨β, β', hβ, hβ'⟩

private theorem smul_mem_hatMx {m n : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    {Λ' : Submodule (𝓞 D.host.E) (Fin m → D.host.E)} (hΛ : Submodule.IsFullLattice D.host.E Λ)
    (hΛ' : Submodule.IsFullLattice D.host.E Λ') (𝔪 : Ideal (𝓞 D.host.E)) {a : AE D}
    (ha0 : infPart D a = 0) (ha : toEAf D a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) {z : Mx D m n}
    (hz : z ∈ hatMx (𝔪 • homLat Λ Λ')) : a • z ∈ hatMx (𝔪 • homLat Λ Λ') := by
  obtain ⟨β, β', hβ, hβ'⟩ := exists_frames hΛ hΛ'
  rw [GlobalTheory.FunObj.HatFrame.mem_hatMx_homLat_iff D Λ Λ' β β' hβ hβ' 𝔪] at hz
  exact smul_mem_hatMx_of_fr hβ hβ' 𝔪 ha0 ha hz.2

theorem exists_nsmul_mem {K : Type} [Field K] [NumberField K] (I : FractionalIdeal (𝓞 K)⁰ K) {𝔪 : Ideal (𝓞 K)}
    (h𝔪 : 𝔪 ≠ ⊥) : ∃ N : ℕ, 0 < N ∧ ∀ a ∈ I, ∃ o ∈ 𝔪, (N : K) * a = algebraMap (𝓞 K) K o := by
  obtain ⟨d, hd, hI⟩ := I.isFractional
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  have hJ : Ideal.span {d} * 𝔪 ≠ ⊥ := mul_ne_zero (by simpa using hd0) h𝔪
  refine ⟨Ideal.absNorm (Ideal.span {d} * 𝔪), Nat.pos_of_ne_zero (by rwa [Ne, Ideal.absNorm_eq_zero_iff]), fun a ha => ?_⟩
  obtain ⟨z, hz, hzd⟩ := Ideal.mem_span_singleton_mul.1 (Ideal.absNorm_mem (Ideal.span {d} * 𝔪))
  obtain ⟨b, hb⟩ := hI a ha
  refine ⟨z * b, 𝔪.mul_mem_right _ hz, ?_⟩
  rw [← map_natCast (algebraMap (𝓞 K) K), ← hzd, map_mul, map_mul, hb, Algebra.smul_def]
  ring

private theorem selfDual_full (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (hΛ : IsSelfDualC V Λ) : Submodule.IsFullLattice D.host.E Λ := by
  haveI : Submodule.IsLattice D.host.E Λ := hΛ.1
  refine ⟨?_⟩
  obtain ⟨s, hs⟩ := hΛ.1.fg
  apply eq_top_iff.mpr
  intro y _
  let f : (Fin V.rank → D.host.E) → D.host.E := fun x =>
    ∑ i, ∑ j, star (x i) * V.gram i j * y j
  obtain ⟨a, ha⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 D.host.E)) s f
  have ha0 : (algebraMap (𝓞 D.host.E) D.host.E a) ≠ 0 := by
    exact (FaithfulSMul.algebraMap_injective _ _).ne (mem_nonZeroDivisors_iff_ne_zero.mp a.2)
  let P : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) := {
    carrier := {x | ∃ b : 𝓞 D.host.E, (b : D.host.E) = (algebraMap (𝓞 D.host.E) D.host.E a) * f x}
    zero_mem' := by refine ⟨0, ?_⟩; simp [f]
    add_mem' := by
      rintro x z ⟨b, hb⟩ ⟨c, hc⟩
      refine ⟨b + c, ?_⟩
      change (b : D.host.E) + c = _
      rw [hb, hc]
      simp [f, map_add, add_mul, Finset.sum_add_distrib, mul_add]
    smul_mem' := by
      rintro c x ⟨b, hb⟩
      refine ⟨RingOfIntegers.mapRingHom (starRingEnd D.host.E) c * b, ?_⟩
      simp only [map_mul, hb, f, Pi.smul_apply, Algebra.smul_def, map_mul, RingOfIntegers.mapRingHom_apply, star_mul]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      change star (c : D.host.E) * _ = _
      ring }
  have hsP : (s : Set (Fin V.rank → D.host.E)) ⊆ P := by
    intro x hx
    obtain ⟨b, hb⟩ := ha x hx
    exact ⟨b, by simpa [Algebra.smul_def] using hb⟩
  have hy : (algebraMap (𝓞 D.host.E) D.host.E a) • y ∈ Λ := by
    apply (hΛ.2 _).2
    intro x hx
    have hxP : x ∈ P := (hs ▸ Submodule.span_le.mpr hsP) hx
    obtain ⟨b, hb⟩ := hxP
    refine ⟨b, ?_⟩
    rw [hb]
    dsimp only [f, Pi.smul_apply]
    simp only [smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hy' : (algebraMap (𝓞 D.host.E) D.host.E a) • y ∈ Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E)) :=
    Submodule.subset_span hy
  have := (Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E))).smul_mem
    (algebraMap (𝓞 D.host.E) D.host.E a)⁻¹ hy' 
  change (algebraMap (𝓞 D.host.E) D.host.E a)⁻¹ •
    ((algebraMap (𝓞 D.host.E) D.host.E a) • y) ∈ _ at this
  rw [← smul_assoc, smul_eq_mul, inv_mul_cancel₀ ha0, one_smul] at this
  exact this


theorem nsmul_tmul (N : ℕ) (α : AF D.host.F) (x : D.host.E) :
    (N • (α ⊗ₜ[D.host.F] x) : AE D) = α ⊗ₜ[D.host.F] ((N : D.host.E) * x) := by
  rw [← nsmul_eq_mul]
  exact (map_nsmul (TensorProduct.mk D.host.F (AF D.host.F) D.host.E α) N x).symm

theorem nsmul_mem_latO {S T : HSp D} (LS : Set (Fin S.rank → D.host.E)) (LT LT' : Set (Fin T.rank → D.host.E)) (N : ℕ)
    (h : ∀ t ∈ LT, (N : D.host.E) • t ∈ LT') (x : WO S T) (hx : x ∈ latO S T LS LT fun _ => True) :
    N • x ∈ latO S T LS LT' fun _ => True := by
  induction hx using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, h0, a, ha, s, hs, t, ht, rfl⟩ := hw
    refine AddSubgroup.subset_closure ⟨α, hα, h0, a, ha, s, hs, _, h t ht, ?_⟩
    ext i j
    simp only [Matrix.smul_apply, Matrix.of_apply, Pi.smul_apply, smul_eq_mul]
    rw [nsmul_tmul]
    congr 1
    ring
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem nsmul_mem_hatMx {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} (hS : IsSelfDualC S ΛS) {𝔪 : Ideal (𝓞 D.host.E)} {N : ℕ}
    (h : ∀ a ∈ D.host.AA, ∃ o ∈ 𝔪, (N : D.host.E) * a = algebraMap (𝓞 D.host.E) D.host.E o)
    (x : WO S T) (hx : x ∈ latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True) :
    N • x ∈ hatMx (𝔪 • homLat ΛS ΛT) := by
  induction hx using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, h0, a, ha, s, hs, t, ht, rfl⟩ := hw
    obtain ⟨o, ho, hoa⟩ := h a ha
    refine AddSubgroup.subset_closure ⟨α, hα, _,
      Submodule.smul_mem_smul ho (GlobalTheory.RowLatChi.genMap_one_mem_homLat hS hs ht), ?_⟩
    ext i j
    simp only [Matrix.smul_apply, Matrix.of_apply, GlobalTheory.LatVac.genMap]
    rw [nsmul_tmul, Algebra.smul_def, ← hoa]
    congr 1
    ring
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem smul_mem_of_idLat {n : ℕ} {I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E}
    (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) {N : ℕ}
    (h : ∀ a ∈ I, ∃ o ∈ (⊤ : Ideal (𝓞 D.host.E)), (N : D.host.E) * a = algebraMap (𝓞 D.host.E) D.host.E o) :
    ∀ t ∈ idLat I Λ, (N : D.host.E) • t ∈ Λ := by
  intro t ht
  induction ht using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨s, hs, y, hy, rfl⟩ := hx
    obtain ⟨o, -, ho⟩ := h s hs
    rw [smul_smul, ho, algebraMap_smul]
    exact Λ.smul_mem o hy
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | smul o x _ hx => rw [smul_comm]; exact Λ.smul_mem o hx

theorem exists_nsmul_latBig_mem_latRow : OnStd fun {D} _ _ {sc} {G} _ _ => ∀ i, i < D.R.m → ∃ N : ℕ, 0 < N ∧ ∀ u ∈ latBig G i, N • u ∈ latRow G i := by
  intro D hq T L μ0 hL sc G W M hM F hF i hi
  obtain ⟨N₁, hN₁, h₁⟩ := exists_nsmul_mem (shiftId G) (𝔪 := ⊤) top_ne_bot
  obtain ⟨N₂, hN₂, h₂⟩ := exists_nsmul_mem D.host.AA (𝔪 := G.modul) (G.pl.modul_ne_bot sc)
  have hsd := GlobalTheory.CosetRow.selfDual_chi hL G i hi
  refine ⟨N₂ * N₁, Nat.mul_pos hN₂ hN₁, fun u hu => ?_⟩
  have k1 := nsmul_mem_latO _ _ (G.Λ (.grid i 0) : Set _) N₁ (smul_mem_of_idLat _ h₁) u hu
  have k2 : N₁ • u ∈ latO (negSp (G.V (.grid (i + 1) 0))) (G.V (.grid i 0)) (G.Λ (.grid (i + 1) 0) : Set _)
      (G.Λ (.grid i 0) : Set _) (fun _ => True) := GlobalTheory.RowLoc.mem_latO_negSp.2 k1
  rw [mul_smul]
  refine ⟨nsmul_mem k2 N₂, fun e he => ?_⟩
  have hprops := GlobalTheory.IdemSumIdeal.isIdemSum_props e G.pl.W0 (fun _ => 0) he
  exact smul_mem_hatMx (selfDual_full _ _ hsd.1) (selfDual_full _ _ hsd.2) G.modul hprops.1 hprops.2.1
    (nsmul_mem_hatMx hsd.1 h₂ _ k2)

end GlobalTheory.BigRow
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.AscFinNe

variable {D : D7}

theorem left_inv_of_li {n ρ : ℕ} (x₀ : Matrix (Fin n) (Fin ρ) D.host.E) (h : LinearIndependent D.host.E x₀.transpose) :
    ∃ L : Matrix (Fin ρ) (Fin n) D.host.E, L * x₀ = 1 := by
  have hinj : Function.Injective (Matrix.toLin' x₀) := by
    show Function.Injective x₀.mulVec
    exact mulVec_injective_iff.mpr h
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' x₀) (LinearMap.ker_eq_bot.2 hinj)
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  conv_lhs => rw [← LinearMap.toMatrix'_toLin' x₀]
  rw [← LinearMap.toMatrix'_comp, hg, LinearMap.toMatrix'_id]

theorem flat_ne_zero : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V V₀ W W₀ : HSp D) (ρ σ : ℕ) (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) (s : Step ψ V V₀ W W₀ ρ σ) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E) (y : Mx D V₀.rank σ), LinearIndependent D.host.E x₀.transpose → ∀ p : Pieces V₀ W W₀ ρ σ, p.Is dV dW (rat x₀) ψ → ∃ Φ ∈ cls dV dW p (rat x₀) y ψ, flatS dV dW s (rat x₀) y Φ ≠ 0 := by
  intro D ψ hψ V V₀ W W₀ ρ σ dV dW s x₀ y hx₀ p hp
  obtain ⟨g, hgv, hg0⟩ := hp.vac₀
  obtain ⟨β₂, hβ₂, hβ₂y, hβ₂per, hβ₂supp⟩ := GlobalTheory.T.exists_adelicBump_periodic_under_adjointLattice D V₀ W W₀ σ dW p.B₂ hp.b₂ y
  obtain ⟨L, hL⟩ := left_inv_of_li x₀ hx₀
  obtain ⟨b, hb, hbx, hb01, hbsupp, hbper⟩ := exists_bump_le (rat x₀) p.A₁ hp.a₁ _
    (GlobalTheory.T.positiveRealPart_traceCharacter_mem_nhds D ψ hψ W.rank ρ (rat L) (rat x₀))
  have hpos : ∀ u : UX D ρ, b (rat x₀ ⬝ u.1.1) ≠ 0 → 0 < (star (psiUni ψ u.1)).re := by
    intro u hu
    obtain ⟨r, hr, hrU, hrA⟩ := hbsupp _ hu
    rw [GlobalTheory.T.genericCharacter_eq_realPartChar_on_bumpSupport D ψ V V₀ W W₀ ρ σ dV dW p x₀ L hL hp u r hr hrA]
    simpa only [Set.mem_setOf_eq, add_sub_cancel_left] using hrU
  have hcpt : HasCompactSupport (fun u : UX D ρ => b (rat x₀ ⬝ u.1.1)) := by
    refine HasCompactSupport.intro' (GlobalTheory.T.isCompact_unitriangular_of_rational_mul_mem_compact D W.rank ρ x₀ hx₀ _ (HasCompactSupport.isCompact (f := fun z => (b z : ℂ)) hb.supp))
      ((isClosed_tsupport _).preimage (continuous_const.matrix_mul (Units.continuous_val.comp continuous_subtype_val))) ?_
    intro u hu
    by_contra h
    exact hu (subset_tsupport _ (by simpa using h))
  obtain ⟨g', hg', hg'm⟩ := GlobalTheory.T.mixedModelTarget_bump_mul_coreTheta_exists D ψ hψ V₀ W W₀ σ dW s.vT β₂ g hβ₂ hgv.1
  obtain ⟨Φ, hΦ, hΦm⟩ := GlobalTheory.T.exists_thetaFunction_mixedCoordinate_bump_mul_core D ψ hψ V V₀ W ρ dV s.vS (fun z => (b z : ℂ)) g' hb hg'
  have hbper' : ∀ a ∈ p.A₁, ∀ z, (fun z => (b z : ℂ)) (z + a) = (fun z => (b z : ℂ)) z := fun a ha z => by
    simp only [hbper a ha z]
  have hbsupp' : ∀ z, (fun z => (b z : ℂ)) z ≠ 0 → ∃ r : Mx D W.rank ρ, r.map (finPart D) = 0 ∧ z - (rat x₀ + r) ∈ p.A₁ :=
    fun z hz => by
      obtain ⟨r, hr, -, hrA⟩ := hbsupp z (by simpa using hz)
      exact ⟨r, hr, hrA⟩
  obtain ⟨hB₁, hB₂, hvac⟩ := GlobalTheory.T.unfolding_conditions_from_second_mixedCoordinate D ψ hψ V V₀ W W₀ ρ σ dV dW s.vT p (rat x₀) y hp β₂ g g' hgv hg' hg'm hβ₂per hβ₂supp
  obtain ⟨hA₁, hA₂⟩ := GlobalTheory.T.class_conditions_isotropicHom_from_firstMixedCoordinate D ψ hψ V V₀ W W₀ ρ σ dV dW s.vS p (rat x₀) hp _ g' Φ hΦ hΦm hbper' hbsupp'
  obtain ⟨hC₁, hC₂, hCv⟩ := GlobalTheory.T.class_conditions_core_from_mixedCoordinateFunction D ψ hψ V V₀ W W₀ ρ σ dV dW s.vS p y _ g' Φ hg' hΦ hΦm hB₁ hB₂ hvac
  refine ⟨Φ, ⟨hΦ, hA₁, hA₂, hC₁, hC₂, hCv⟩, ?_⟩
  exact GlobalTheory.T.flatMap_productDatum_eq_unitriangularIntegral_bump D ψ hψ V V₀ W W₀ ρ σ dV dW s (rat x₀) y b β₂ g g' Φ hg0 hβ₂y hΦm hg'm
    (Complex.continuous_re.comp hb.cont |>.congr fun z => by simp) hbx (fun z => (hb01 z).1) hpos hcpt

end GlobalTheory.AscFinNe

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.AscFin.RowAAUnit

variable {D : D7}

theorem idem_smul_latA {S : HSp D} {L : Lat S} {P : GlobalTheory.FinPl.Pl D → Prop} (v : GlobalTheory.FinPl.Pl D)
    {z : Fin S.rank → AE D} (hz : z ∈ latA S L P) : GlobalTheory.FinPlLoc.idem D (· = v) • z ∈ latA S L (· = v) := by
  induction hz using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hαi, hα, a, ha, x, hx, rfl⟩ := hy
    refine AddSubgroup.subset_closure ⟨GlobalTheory.FinPlLoc.ePl D (· = v) * α, fun w => ?_, fun w hw => ?_, a, ha, x, hx, ?_⟩
    · rw [map_mul]; exact mul_mem (GlobalTheory.FinPlLoc.ePl_int _ w) (hαi w)
    · rw [map_mul, GlobalTheory.FinPlLoc.evalV_ePl, if_neg hw, zero_mul]
    · funext i
      rw [Pi.smul_apply, smul_eq_mul]
      unfold GlobalTheory.FinPlLoc.idem
      rw [Algebra.TensorProduct.tmul_mul_tmul, ← GlobalTheory.FinPlLoc.pairA_mul, one_mul]
  | zero => rw [smul_zero]; exact zero_mem _
  | add y y' _ _ h h' => rw [smul_add]; exact add_mem h h'
  | neg y _ h => rw [smul_neg]; exact neg_mem h

theorem smul_mulVec_mem_latV : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m) (M : WO (G.V (.grid (2 * ρ + 2) 0)) (G.V (.grid (2 * ρ + 1) 0))), M ∈ latRow G (2 * ρ + 1) → ∀ v : GlobalTheory.FinPl.Pl D, ∀ y ∈ latV _ (G.Λ (.grid (2 * ρ + 2) 0)) (· = v), ∀ s ∈ GlobalTheory.SeeSaw.idV (D.host.AA⁻¹) v, s • (M *ᵥ y) ∈ latV _ (G.Λ (.grid (2 * ρ + 1) 0)) (· = v) := by
  intro D hOff T L μ0 hL sc G W Mv hM F hF ρ h M hMr v y hy s hs
  have hV : IsSelfDualC (G.V (.grid (2 * ρ + 2) 0)) (G.Λ (.grid (2 * ρ + 2) 0)) :=
    (G.isV (X := .grid (2 * ρ + 2) 0) ⟨h, Nat.zero_le _⟩ (fun j hj => by injection hj with h1 h2; omega)).sd
  have hO : M ∈ latO (G.V (.grid (2 * ρ + 2) 0)) (G.V (.grid (2 * ρ + 1) 0)) (G.Λ (.grid (2 * ρ + 2) 0) : Set _)
      (G.Λ (.grid (2 * ρ + 1) 0) : Set _) (fun _ => True) :=
    GlobalTheory.RowLoc.mem_latO_negSp.1 hMr.1
  have hyT : y ∈ latV _ (G.Λ (.grid (2 * ρ + 2) 0)) (fun _ => True) := GlobalTheory.FinPl.PsiUnit.latV_mono trivial hy
  have hA : M *ᵥ y ∈ latA _ (G.Λ (.grid (2 * ρ + 1) 0)) (fun _ => True) := GlobalTheory.FinPl.LatMem.latO_maps hV hO hyT
  have hy' : GlobalTheory.FinPlLoc.idem D (· = v) • y = y := by
    funext i
    rw [Pi.smul_apply, smul_eq_mul]
    exact (GlobalTheory.FinPlLoc.mem_idAt_iff _ _).1 (GlobalTheory.FinPlLoc.latV_idAt hy i)
  have hAv : M *ᵥ y ∈ latA _ (G.Λ (.grid (2 * ρ + 1) 0)) (· = v) := by
    rw [← hy', Matrix.mulVec_smul]
    exact idem_smul_latA v hA
  exact (((GlobalTheory.SeeSaw.idV_props D W.ψ W.ψ_std v).2.2.2.2.2.2 _ _ _).1 hAv).2 s hs

end GlobalTheory.AscFin.RowAAUnit

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.RowBig

open scoped Pointwise

variable {D : D7}

theorem idLat_one {n : ℕ} (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) :
    idLat (1 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) Λ = Λ := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨s, hs, y, hy, rfl⟩
    obtain ⟨r, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hs
    rw [algebraMap_smul]
    exact Λ.smul_mem r hy
  · intro y hy
    exact Submodule.subset_span ⟨1, FractionalIdeal.one_mem_one _, y, hy, (one_smul _ _).symm⟩

theorem conjFI_coe (I : Ideal (𝓞 D.host.E)) :
    GlobalTheory.SeeSaw.conjFI D (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) =
      ((D.host.conj • I : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) := by
  ext x
  rw [GlobalTheory.SeeSaw.mem_conjFI, FractionalIdeal.mem_coeIdeal, FractionalIdeal.mem_coeIdeal]
  constructor
  · rintro ⟨r, hr, hx⟩
    refine ⟨D.host.conj • r, Ideal.smul_mem_pointwise_smul _ _ _ hr, ?_⟩
    show D.host.conj (r : D.host.E) = x
    rw [show (r : D.host.E) = D.host.conj x from hx, GlobalTheory.SeeSaw.conj_conj_host]
  · rintro ⟨r, hr, rfl⟩
    refine ⟨D.host.conj⁻¹ • r, Ideal.mem_pointwise_smul_iff_inv_smul_mem.1 hr, ?_⟩
    show D.host.conj.symm (r : D.host.E) = D.host.conj (r : D.host.E)
    rw [AlgEquiv.symm_apply_eq, GlobalTheory.SeeSaw.conj_conj_host]

theorem conjFI_conjFI (𝔞 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : GlobalTheory.SeeSaw.conjFI D (GlobalTheory.SeeSaw.conjFI D 𝔞) = 𝔞 := by
  ext x
  rw [GlobalTheory.SeeSaw.mem_conjFI, GlobalTheory.SeeSaw.mem_conjFI, GlobalTheory.SeeSaw.conj_conj_host]

theorem conjFI_shiftId {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) :
    GlobalTheory.SeeSaw.conjFI D (shiftId G) = (shiftId G)⁻¹ := by
  have hb : ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) =
      GlobalTheory.SeeSaw.conjFI D (G.modul : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) := (conjFI_coe _).symm
  unfold shiftId
  rw [hb, map_mul, map_inv₀, conjFI_conjFI, mul_inv, inv_inv, mul_comm]

theorem shiftId_ne_zero {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) : shiftId G ≠ 0 := by
  have hm : (G.modul : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 (G.pl.modul_ne_bot sc)
  have hb : ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0 := by
    rw [show ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) =
      GlobalTheory.SeeSaw.conjFI D (G.modul : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) from (conjFI_coe _).symm]
    exact (RingEquiv.map_ne_zero_iff _).2 hm
  exact mul_ne_zero hm (inv_ne_zero hb)

theorem isSelfDualC_idLat_shiftId {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) {S : HSp D} (Λ : Lat S)
    (hΛ : IsSelfDualC S Λ) : IsSelfDualC S (idLat (shiftId G) Λ) := by
  refine GlobalTheory.ScaleSelfDual.isSelfDualC_scaleLat S Λ hΛ (shiftId_ne_zero G) fun c => ?_
  rw [← conjFI_shiftId, GlobalTheory.SeeSaw.mem_conjFI, Formalism.BasicNotions.bridge_star_holds D.R D.host c]

theorem latRow_le_latBig : All fun {D} _ _ _ {G} _ _ => ∀ i, 1 ≤ i → i < D.R.m → latRow G i ≤ latBig G i := by
  intro D hq T L μ0 hL sc G W M hM i hi1 him u hu
  have hS : IsSelfDualC (G.V (.grid (i + 1) 0)) (G.Λ (.grid (i + 1) 0)) :=
    (G.isV (X := .grid (i + 1) 0) ⟨by omega, by omega⟩ (fun j h => by injection h with h1 h2; omega)).sd
  have hT : IsSelfDualC (G.V (.grid i 0)) (G.Λ (.grid i 0)) :=
    (G.isV (X := .grid i 0) ⟨by omega, by omega⟩ (fun j h => by injection h with h1 h2; omega)).sd
  have h1 := idLat_one (G.Λ (.grid i 0))
  have hsh := isSelfDualC_idLat_shiftId G _ hT
  obtain ⟨e, he, -⟩ := W.cosVec_is
  have hu' : u ∈ latO (negSp (G.V (.grid (i + 1) 0))) (G.V (.grid i 0)) (G.Λ (.grid (i + 1) 0) : Set _)
      (G.Λ (.grid i 0) : Set _) (fun _ => True) ∧
      ∀ e : AE D, IsIdemSum e G.pl.W0 → e • u ∈ hatMx (G.modul • homLat (G.Λ (.grid (i + 1) 0)) (G.Λ (.grid i 0))) := hu
  have key := GlobalTheory.T.completedHomLattice_modulus_depth_mem_shift hq μ0 hL G (G.Λ (.grid (i + 1) 0)) 1 (G.Λ (.grid i 0)) hS (by rw [h1]; exact hT)
    (by rw [one_mul]; exact hsh) u (by rw [h1]; exact GlobalTheory.RowLoc.mem_latO_negSp.1 hu'.1) ⟨e, he, by rw [h1]; exact hu'.2 e he⟩
  rw [one_mul] at key
  exact key

end GlobalTheory.RowBig

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

theorem _root_.GlobalTheory.T.isFiniteAdelicMatrixLattice_depthLatticeOfPair : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (p : Pair T), IsSelfDualC (G.pS p) (G.latS p) → IsSelfDualC (G.pT p) (G.latT p) → FinLat (depLat G p) := by
  first | exact @GlobalTheory.AscFin.DepLat.finLat_depLat | exact GlobalTheory.AscFin.DepLat.finLat_depLat | (intros; apply GlobalTheory.AscFin.DepLat.finLat_depLat <;> assumption)
end
