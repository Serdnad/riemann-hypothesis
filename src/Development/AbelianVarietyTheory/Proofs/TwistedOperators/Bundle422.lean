module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1794
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1922
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle419
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle221
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle186
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle009
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle384
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle236
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle390
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
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.NatCastSmulMemHatL
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OffQOfSizeRows
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TowerEx
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle333

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin



noncomputable section

namespace GlobalTheory.UnitAtPl

open GlobalTheory.FinPlLoc (idem ePl evalV_ePl ePl_int idem_mem_idAt idem_mul_self finPart_pair)

variable {D : D7}

theorem evalV_inv_mem (x : GlobalTheory.FinPl.Pl D) (c : 𝓞 D.host.F) (hc : c ∉ x.asIdeal) :
    evalV D.host.F x (algebraMap D.host.F (Af D.host.F) ((c : D.host.F))⁻¹) ∈ x.adicCompletionIntegers D.host.F := by
  rw [AlgHom.commutes, HeightOneSpectrum.mem_adicCompletionIntegers]
  have h1 : x.intValuation c = 1 := HeightOneSpectrum.intValuation_eq_one_iff.2 hc
  have h2 := HeightOneSpectrum.valuation_of_algebraMap (K := D.host.F) x c
  rw [h1] at h2
  show Valued.v ((((c : D.host.F))⁻¹ : D.host.F) : x.adicCompletion D.host.F) ≤ 1
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', map_inv₀]
  have : HeightOneSpectrum.valuation D.host.F x (c : D.host.F) = 1 := h2
  rw [this, inv_one]

theorem inv_ePl_int (x : GlobalTheory.FinPl.Pl D) (c : 𝓞 D.host.F) (hc : c ∉ x.asIdeal) :
    ((c : D.host.F))⁻¹ • ePl D (· = x) ∈ intAf D.host.F := by
  intro w
  rw [Algebra.smul_def, map_mul, evalV_ePl]
  split_ifs with h
  · subst h; rw [mul_one]; exact evalV_inv_mem w c hc
  · rw [mul_zero]; exact zero_mem _

theorem tmul_one_mul_mem {γ : Af D.host.F} (hγ : γ ∈ intAf D.host.F) {w : Af D.host.F ⊗[D.host.F] D.host.E}
    (hw : w ∈ intAE D) : (γ ⊗ₜ[D.host.F] (1 : D.host.E)) * w ∈ intAE D := by
  induction hw using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, o, rfl⟩ := hw
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    refine AddSubgroup.subset_closure ⟨γ * α, fun v => ?_, o, rfl⟩
    rw [map_mul]
    exact mul_mem (hγ v) (hα v)
  | zero => rw [mul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | neg x _ hx => rw [mul_neg]; exact neg_mem hx

theorem finPart_idem_inv (x : GlobalTheory.FinPl.Pl D) (c : 𝓞 D.host.F) :
    finPart D (idem D (· = x) * incA D ((c : D.host.F) : D.host.E)⁻¹) =
      (((c : D.host.F))⁻¹ • ePl D (· = x)) ⊗ₜ[D.host.F] (1 : D.host.E) := by
  have h0 : idem D (· = x) * incA D ((c : D.host.F) : D.host.E)⁻¹ =
      pairA D.host.F 0 (ePl D (· = x)) ⊗ₜ[D.host.F] ((c : D.host.F) : D.host.E)⁻¹ := by
    change (pairA D.host.F 0 (ePl D (· = x)) ⊗ₜ[D.host.F] (1 : D.host.E)) *
      ((1 : AF D.host.F) ⊗ₜ[D.host.F] ((c : D.host.F) : D.host.E)⁻¹) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  have h1 : ((c : D.host.F) : D.host.E)⁻¹ = ((c : D.host.F))⁻¹ • (1 : D.host.E) := by
    rw [Algebra.smul_def, map_inv₀, mul_one]; rfl
  rw [h0, finPart_pair, h1, TensorProduct.tmul_smul, TensorProduct.smul_tmul']

theorem idem_mul_mem_of_unit : ∀ (D : D7) (v : GlobalTheory.FinPl.Pl D) (u : 𝓞 D.host.F), u ∉ v.asIdeal → ∀ z : AE D, GlobalTheory.FinPlLoc.idem D (· = v) * incA D ((u : D.host.F) : D.host.E) * z ∈ intAt D (· = v) → GlobalTheory.FinPlLoc.idem D (· = v) * z ∈ intAt D (· = v) := by
  intro D v u hu z hz
  have hu0 : ((u : D.host.F) : D.host.E) ≠ 0 := by
    intro h
    apply hu
    have h' : (u : D.host.F) = 0 := by exact_mod_cast h
    have h'' : u = 0 := by exact_mod_cast h'
    rw [h'']; exact zero_mem _
  have hinc : incA D ((u : D.host.F) : D.host.E)⁻¹ * incA D ((u : D.host.F) : D.host.E) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hu0, map_one]
  have key : idem D (· = v) * z = (idem D (· = v) * incA D ((u : D.host.F) : D.host.E)⁻¹) *
      (idem D (· = v) * incA D ((u : D.host.F) : D.host.E) * z) := by
    calc idem D (· = v) * z = (idem D (· = v) * idem D (· = v)) *
        (incA D ((u : D.host.F) : D.host.E)⁻¹ * incA D ((u : D.host.F) : D.host.E)) * z := by
          rw [idem_mul_self, hinc, mul_one]
      _ = _ := by ring
  refine ⟨Ideal.mul_mem_right _ _ (idem_mem_idAt _), ?_⟩
  rw [key, (finPart D).map_mul, finPart_idem_inv]
  exact tmul_one_mul_mem (inv_ePl_int v u hu) hz.2

end GlobalTheory.UnitAtPl

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.WittCoreLat

open GlobalTheory.FinPl.LatMem

variable {D : D7}

theorem rat_mulVec_tmul {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) (c : AF D.host.F) (z : Fin n → D.host.E) :
    rat M *ᵥ (fun i => c ⊗ₜ[D.host.F] z i) = fun k => c ⊗ₜ[D.host.F] (M *ᵥ z) k := by
  funext k
  simp only [Matrix.mulVec, dotProduct, rat, Matrix.map_apply]
  rw [TensorProduct.tmul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  show ((1 : AF D.host.F) ⊗ₜ[D.host.F] M k j) * (c ⊗ₜ[D.host.F] z j) = c ⊗ₜ[D.host.F] (M k j * z j)
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

theorem i₀_mulVec_mem {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {L : Lat S} {L₀ : Lat S₀}
    (hL : ∀ z : Fin S.rank → D.host.E, (∀ v : GlobalTheory.FinPl.Pl D, (fun i => pairA D.host.F 0 (GlobalTheory.FinPl.LatMem.indP D.host.F (· = v)) ⊗ₜ[D.host.F] z i) ∈ latV S L (· = v)) → z ∈ L)
    (hmono : ∀ v, MonoAt d L L₀ v) : ∀ y ∈ L₀, d.i₀ *ᵥ y ∈ L := by
  intro y hy
  have hX : d.qX * d.i₀ = 0 := rat_injective (D := D) (by rw [rat_mul, rat_zero]; exact d.pX_j0)
  have hY : d.qY * d.i₀ = 0 := rat_injective (D := D) (by rw [rat_mul, rat_zero]; exact d.pY_j0)
  have h0 : d.q0 * d.i₀ = 1 := rat_injective (D := D) (by rw [rat_mul, rat_one]; exact d.p0_j0)
  refine hL _ fun v => ?_
  set c : AF D.host.F := pairA D.host.F 0 (indP D.host.F (· = v))
  refine (hmono v _).2 ⟨fun i => ?_, fun i => ?_, ?_⟩
  · have : d.pX *ᵥ (fun i => c ⊗ₜ[D.host.F] (d.i₀ *ᵥ y) i) = 0 := by
      rw [HypDec.pX, rat_mulVec_tmul, Matrix.mulVec_mulVec, hX, Matrix.zero_mulVec]
      funext k; exact TensorProduct.tmul_zero _ _
    rw [this]
    have h' : GlobalTheory.FinPl.colMul d.jX i ((0 : Fin ρ → AE D) i) = 0 := by
      funext k; simp [GlobalTheory.FinPl.colMul]
    rw [h']; exact zero_mem _
  · have : d.pY *ᵥ (fun i => c ⊗ₜ[D.host.F] (d.i₀ *ᵥ y) i) = 0 := by
      rw [HypDec.pY, rat_mulVec_tmul, Matrix.mulVec_mulVec, hY, Matrix.zero_mulVec]
      funext k; exact TensorProduct.tmul_zero _ _
    rw [this]
    have h' : GlobalTheory.FinPl.colMul d.jY i ((0 : Fin ρ → AE D) i) = 0 := by
      funext k; simp [GlobalTheory.FinPl.colMul]
    rw [h']; exact zero_mem _
  · rw [HypDec.p0, rat_mulVec_tmul, Matrix.mulVec_mulVec, h0, Matrix.one_mulVec]
    exact AddSubgroup.subset_closure ⟨indP D.host.F (· = v), indicatorAdele_mem_integralAdeles' _ _, indicatorAdele_supported _ _, 1, rfl, y, hy,
      by funext k; rw [one_mul]⟩

end GlobalTheory.WittCoreLat
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.FinPl.CoreProj

theorem rat_mulVec_gen' {D : D7} {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) (t : AF D.host.F) (x : Fin n → D.host.E) :
    rat M *ᵥ (fun l => t ⊗ₜ[D.host.F] (1 * x l)) = fun k => t ⊗ₜ[D.host.F] (1 * (M *ᵥ x) k) := by
  funext k
  simp only [Matrix.mulVec, dotProduct, rat, Matrix.map_apply, one_mul, TensorProduct.tmul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  change ((1 : AF D.host.F) ⊗ₜ[D.host.F] M k l) * (t ⊗ₜ[D.host.F] x l) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

theorem wittCoreProjection_mem_lattice_of_splits : ∀ {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {L : Lat S} {L₀ : Lat S₀}, (∀ z : Fin S₀.rank → D.host.E, (∀ v : GlobalTheory.FinPl.Pl D, (fun i => pairA D.host.F 0 (GlobalTheory.FinPl.LatMem.indP D.host.F (· = v)) ⊗ₜ[D.host.F] z i) ∈ latV S₀ L₀ (· = v)) → z ∈ L₀) → (∀ v, MonoAt d L L₀ v) → ∀ t ∈ L, d.q0 *ᵥ t ∈ L₀ := by
  intro D S S₀ ρ d L L₀ hlg hmono t ht
  refine hlg _ fun v => ?_
  have hY : (fun i => pairA D.host.F 0 (GlobalTheory.FinPl.LatMem.indP D.host.F (· = v)) ⊗ₜ[D.host.F] (1 * t i)) ∈
      latV S L (· = v) :=
    AddSubgroup.subset_closure ⟨_, GlobalTheory.FinPl.LatMem.indicatorAdele_mem_integralAdeles' _ _, GlobalTheory.FinPl.LatMem.indicatorAdele_supported _ _, 1, rfl, t, ht, rfl⟩
  have h := ((hmono v _).1 hY).2.2
  rw [HypDec.p0, rat_mulVec_gen'] at h
  simpa only [one_mul] using h

end GlobalTheory.FinPl.CoreProj
end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical

noncomputable section

namespace GlobalTheory.ThetaSchrCont

open GlobalTheory.HeisSchA GlobalTheory.Published.Metaplectic
open scoped Matrix

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

def finSlice (Φ : (κ → AdeleRing (𝓞 F) F) → ℂ) (y : κ → mixedEmbedding.mixedSpace F) :
    (κ → FiniteAdeleRing (𝓞 F) F) → ℂ :=
  fun w => Φ fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y i), w i)

theorem finSlice_mem {Φ : (κ → AdeleRing (𝓞 F) F) → ℂ} (hΦ : Φ ∈ schA F κ) (y : κ → mixedEmbedding.mixedSpace F) :
    finSlice Φ y ∈ SB (κ → FiniteAdeleRing (𝓞 F) F) := by
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, g, hg, rfl⟩ := hx
    have : finSlice (pureA F f g) y = f y • g := by
      funext w
      simp only [finSlice, pureA, RingEquiv.apply_symm_apply, Pi.smul_apply, smul_eq_mul]
    rw [this]
    exact Submodule.smul_mem _ _ hg
  | zero => exact (SB _).zero_mem
  | add x x' _ _ hx hx' => exact (SB _).add_mem hx hx'
  | smul a x _ hx => exact (SB _).smul_mem a hx

theorem exists_fin_of_rest {f : SInf F κ} {r : (κ → AF F) → ℂ} (hr : Rest (evI F) (⇑f) r) (hf : f ≠ 0) :
    ∃ G ∈ SB (κ → FiniteAdeleRing (𝓞 F) F), ∀ x : κ → AF F, r x = G fun i => (x i).2 := by
  obtain ⟨y, hy⟩ : ∃ y, f y ≠ 0 := by
    by_contra h
    push_neg at h
    exact hf (SchwartzMap.ext h)
  let e := InfiniteAdeleRing.ringEquiv_mixedSpace F
  refine ⟨(f y)⁻¹ • finSlice (tens (evI F) (⇑f) r) y, Submodule.smul_mem _ _ (finSlice_mem hr.2 y), fun x => ?_⟩
  let z : κ → AF F := fun i => mk (e.symm (y i) - (x i).1) 0
  have hz : At (evI F) z := by
    intro u hu
    funext i
    exact at_mk _ u hu
  have hxz : x + z = fun i => (e.symm (y i), (x i).2) := by
    funext i
    refine Prod.ext ?_ ?_
    · show (x i).1 + (e.symm (y i) - (x i).1) = e.symm (y i)
      abel
    · show (x i).2 + 0 = (x i).2
      exact add_zero _
  have h1 := hr.1 x z hz
  rw [hxz] at h1
  have h2 : (fun i => evI F ((e.symm (y i), (x i).2) : AF F)) = y := by
    funext i
    exact e.apply_symm_apply (y i)
  simp only [Pi.smul_apply, smul_eq_mul, finSlice, tens]
  rw [h2, ← h1]
  field_simp
  rfl

theorem tens_eq_pureA (g : SInf F κ) {r : (κ → AF F) → ℂ} {G : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ}
    (hG : ∀ x : κ → AF F, r x = G fun i => (x i).2) : tens (evI F) (⇑g) r = pureA F g G := by
  funext x
  simp only [tens, pureA, hG]
  rfl

theorem schr_pureA_eq [Invertible (2 : AdeleRing (𝓞 F) F)] (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : IsStd ψ)
    (w : (κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F)) (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ)
    (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) :
    let q : AdeleRing (𝓞 F) F →+* mixedEmbedding.mixedSpace F := (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp p1
    let h : AdeleRing (𝓞 F) F := ⅟(2 : AdeleRing (𝓞 F) F) * (w.1 ⬝ᵥ w.2)
    schr ψ w (pureA F f g) = pureA F (archS f (fun i => q (w.2 i)) (fun i => q (w.1 i))
      (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (q h)))
      (finS ψ g (fun i => p2 (w.2 i)) (fun i => p2 (w.1 i)) (p2 h)) := by
  intro q h
  let c : κ → mixedEmbedding.mixedSpace F := fun i => q (w.2 i)
  let t : κ → mixedEmbedding.mixedSpace F := fun i => q (w.1 i)
  let k : ℝ := Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (q h)
  let d : κ → FiniteAdeleRing (𝓞 F) F := fun i => p2 (w.2 i)
  let s : κ → FiniteAdeleRing (𝓞 F) F := fun i => p2 (w.1 i)
  funext x
  let y : κ → mixedEmbedding.mixedSpace F := fun i => q (x i)
  let z : κ → FiniteAdeleRing (𝓞 F) F := fun i => p2 (x i)
  have h1 : (fun i => q ((x + w.1) i)) = y + t := funext fun i => map_add q (x i) (w.1 i)
  have h2 : (fun i => p2 ((x + w.1) i)) = z + s := funext fun i => map_add p2 (x i) (w.1 i)
  have h3 : ψ (x ⬝ᵥ w.2 + h) = eChar ((-trL c) y + -k) * finChar ψ (z ⬝ᵥ d + p2 h) := by
    rw [map_eq_mul ψ, hψ.2.2 _ (at_mk _)]
    congr 1
    · have e1 : evI F (mk (p1 (x ⬝ᵥ w.2 + h)) 0) = y ⬝ᵥ c + q h := by
        change q (x ⬝ᵥ w.2 + h) = _
        rw [map_add (f := _), RingHom.map_dotProduct]
        rfl
      rw [e1, map_add (f := _), eChar_apply, ContinuousLinearMap.neg_apply, trL_apply]
      congr 1
      push_cast
      ring
    · rw [map_add (f := _), RingHom.map_dotProduct]
      rfl
  change ψ (x ⬝ᵥ w.2 + h) * (f (fun i => q ((x + w.1) i)) * g (fun i => p2 ((x + w.1) i))) =
    archS f c t k y * (finChar ψ (z ⬝ᵥ d + p2 h) * g (z + s))
  rw [h1, h2, h3, archS_apply]
  ring

theorem exists_clm_hasSum : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ), IsStd ψ →
    ∀ (u : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (f : SInf F (Fin n × Fin d)) (r : (Fin n × Fin d → AF F) → ℂ),
    Rest (evI F) (⇑f) r → f ≠ 0 → ∃ T : SInf F (Fin n × Fin d) →L[ℂ] ℂ, ∀ g : SInf F (Fin n × Fin d),
      HasSum (fun ξ : Fin n × Fin d → F => M.co.rho ψ u (tens (evI F) (⇑g) r) (fun i => algebraMap F (AF F) (ξ i))) (T g) := by
  intro F E _ _ _ _ _ σ n d X W M ψ hψ u f r hr hf
  obtain ⟨G, hG, hrG⟩ := exists_fin_of_rest hr hf
  set w := M.co.e u with hw
  let q : AdeleRing (𝓞 F) F →+* mixedEmbedding.mixedSpace F :=
    (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp p1
  let h : AdeleRing (𝓞 F) F := ⅟(2 : AdeleRing (𝓞 F) F) * (w.1 ⬝ᵥ w.2)
  let c : Fin n × Fin d → mixedEmbedding.mixedSpace F := fun i => q (w.2 i)
  let t : Fin n × Fin d → mixedEmbedding.mixedSpace F := fun i => q (w.1 i)
  let k : ℝ := Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (q h)
  let G' := finS ψ G (fun i => p2 (w.2 i)) (fun i => p2 (w.1 i)) (p2 h)
  have hG' : G' ∈ SB (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F) := finS_mem ψ hψ.1 hG _ _ _
  obtain ⟨l, hl, hleq⟩ := GlobalTheory.ThetaAdmitted.exists_admitted_form_eq_adelicThetaDistribution_alt F (Fin n × Fin d)
  obtain ⟨T₀, hT₀⟩ := hl G' hG'
  let A : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d) :=
    (SchwartzMap.smulLeftCLM ℂ (fun y : Fin n × Fin d → mixedEmbedding.mixedSpace F => eChar ((-trL c) y + -k))).comp
      (SchwartzMap.compSubConstCLM ℂ (-t))
  refine ⟨T₀.comp A, fun g => ?_⟩
  have hΦ : M.co.rho ψ u (tens (evI F) (⇑g) r) = pureA F (A g) G' := by
    rw [tens_eq_pureA g hrG]
    exact schr_pureA_eq ψ hψ w g G
  rw [hΦ]
  have hmem : pureA F (A g) G' ∈ schA F (Fin n × Fin d) := Submodule.subset_span ⟨A g, G', hG', rfl⟩
  convert hasSum_thetaSum F hmem using 1
  rw [ContinuousLinearMap.comp_apply, ← hT₀, hleq _ hmem]

end GlobalTheory.ThetaSchrCont
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

namespace GlobalTheory.GoodComm

theorem exists_open_fix_algF {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hθ : IsInfFam θ) {W₁ X : HSp D}
    {A₁ : Fr W₁} {B : Fr X} {χS χT : (AE D)ˣ →* Circle} {ωB : WRep W₁ X} (hW : IsWeilDatumO ψ W₁ X χS χT ωB)
    {Ψ : WO W₁ X → ℂ} (hΨ : Ψ ∈ algF ψ θ false A₁ B) :
    ∃ U : Subgroup (GA D W₁), IsOpen (U : Set (GA D W₁)) ∧ ∀ k ∈ U, k ∈ GfC W₁ → ωB (k, 1) Ψ = Ψ := by
  induction hΨ using Submodule.span_induction with
  | mem Φ hΦ =>
    obtain ⟨f, P, hf, rfl⟩ := hΦ
    obtain ⟨U, U', hU, -, hfix⟩ := GlobalTheory.Mem.ThetaLevel.exists_level D ψ hW.std W₁ X ωB
      (GlobalTheory.Ker.isWeak_of_datum hW) hW.om_cont f hf.1
    refine ⟨U, hU, fun k hk hkf => ?_⟩
    have e := GlobalTheory.OrientedHeis.om_fin_pureTensorO ψ W₁ X χS χT ωB hW θ hθ k hkf 1 (one_mem _)
      (frSgn false A₁).cart B.cart A₁.onb B.onb f P hf.1
    show ωB (k, 1) (fockF ψ θ false A₁ B f P) = fockF ψ θ false A₁ B f P
    unfold fockF
    exact e.trans (by rw [hfix k hk hkf 1 (one_mem _) (one_mem _)]; rfl)
  | zero => exact ⟨⊤, by simp, fun k _ _ => map_zero _⟩
  | add x y _ _ hx hy =>
    obtain ⟨U, hU, h⟩ := hx
    obtain ⟨U', hU', h'⟩ := hy
    refine ⟨U ⊓ U', by rw [Subgroup.coe_inf]; exact hU.inter hU', fun k hk hkf => ?_⟩
    rw [map_add (f := _), h k (Subgroup.mem_inf.1 hk).1 hkf, h' k (Subgroup.mem_inf.1 hk).2 hkf]
  | smul c x _ hx =>
    obtain ⟨U, hU, h⟩ := hx
    exact ⟨U, hU, fun k hk hkf => by rw [map_smul, h k hk hkf]⟩

theorem comm_at_good_place : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ →
    ∀ (W₁ X : HSp D) (A₁ : Fr W₁) (B : Fr X)
    (α β : (AE D)ˣ →* Circle) (ωB : WRep W₁ X), IsWeil ψ false W₁ X α (α / β) ωB →
    ∀ (n : ℕ) (Ψ : Fin n → WO W₁ X → ℂ) (u : Fin n → GA D W₁), (∀ i, Ψ i ∈ algF ψ θ false A₁ B) → (∀ i, u i ∈ GfC W₁) →
    ∃ P : Finset (HeightOneSpectrum (𝓞 D.host.F)), ∀ v ∉ P, ∀ z : GA D W₁ →₀ ℂ,
      (∀ k ∈ z.support, k ∈ Set.range (GlobalTheory.AdelicU.emb D.sp.cm.sig W₁.gram v)) → ∀ i, ∃ u' ∈ GfC W₁,
        (z.sum fun k c => c • ωB (k, 1)) (ωB (u i, 1) (Ψ i)) = ωB (u', 1) ((z.sum fun k c => c • ωB (k, 1)) (Ψ i)) := by
  classical
  intro D ψ θ hθ W₁ X A₁ B α β ωB hB n Ψ u hΨ hu
  have hW : IsWeilDatumO ψ W₁ X α (α / β) ωB := hB
  choose U hU hfix using fun i => exists_open_fix_algF (A₁ := A₁) (B := B) hθ hW (hΨ i)
  have hfin : ∀ i, {v : HeightOneSpectrum (𝓞 D.host.F) | ¬ (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.gAt W₁ (Sum.inl v) (u i) ∈ U i ∧
      GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.gAt W₁ (Sum.inl v) (u i) ∈ GfC W₁)}.Finite := fun i =>
    ((GlobalTheory.PlaceGen.gen_by_local D W₁ (U i) (hU i)).1 (u i)).preimage Sum.inl_injective.injOn
  refine ⟨Finset.univ.biUnion fun i => (hfin i).toFinset, fun v hv z hz i => ?_⟩
  have hvi : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.gAt W₁ (Sum.inl v) (u i) ∈ U i ∧ GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.gAt W₁ (Sum.inl v) (u i) ∈ GfC W₁ := by
    by_contra hc
    exact hv (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, (hfin i).mem_toFinset.2 hc⟩)
  set uv := GlobalTheory.AdelicU.emb D.sp.cm.sig W₁.gram v (GlobalTheory.AdelicU.proj D.sp.cm.sig W₁.gram v (u i)) with huv
  have hfixv : ωB (uv, 1) (Ψ i) = Ψ i := hfix i uv hvi.1 hvi.2
  refine ⟨u i * uv⁻¹, mul_mem (hu i) (inv_mem hvi.2), ?_⟩
  have hp : GlobalTheory.AdelicU.proj D.sp.cm.sig W₁.gram v (u i * uv⁻¹) = 1 := by
    rw [map_mul, map_inv, huv, GlobalTheory.AdelicU.proj_emb_self, mul_inv_cancel]
  have m : ∀ (a b : GA D W₁) (f : WO W₁ X → ℂ), ωB (a * b, 1) f = ωB (a, 1) (ωB (b, 1) f) := fun a b f => by
    rw [show ((a * b, (1 : GA D X)) : GA D W₁ × GA D X) = (a, 1) * (b, 1) by simp, map_mul, Module.End.mul_apply]
  have key : ∀ k ∈ z.support, ωB (k, 1) (ωB (u i, 1) (Ψ i)) = ωB (u i * uv⁻¹, 1) (ωB (k, 1) (Ψ i)) := by
    intro k hk
    obtain ⟨x, rfl⟩ := hz k hk
    have hc := GlobalTheory.AdelicU.commute_emb D.sp.cm.sig W₁.gram x hp
    have e1 : GlobalTheory.AdelicU.emb D.sp.cm.sig W₁.gram v x * u i =
        (u i * uv⁻¹) * (GlobalTheory.AdelicU.emb D.sp.cm.sig W₁.gram v x * uv) := by
      rw [← mul_assoc, ← hc.eq]; group
    rw [← m, e1, m (u i * uv⁻¹), m (GlobalTheory.AdelicU.emb D.sp.cm.sig W₁.gram v x) uv, hfixv]
  simp only [Finsupp.sum]

  rw [LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [LinearMap.smul_apply, LinearMap.smul_apply, map_smul, key k hk]

end GlobalTheory.GoodComm
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix
open scoped Classical


theorem _root_.GlobalTheory.T.polynomial_fock_space_stable_mul_trace_pairing : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
      IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → IsHecke F E χX → IsHecke F E χW →
      M.IsWeil ψ χX χW om →
      ∀ τ : ∀ w : InfinitePlace F, EmbOver E w, (∀ w, IsCartan (X.J.map (τ w).1) (X.θ w)) →
        (∀ w, IsCartan (Complex.I • W.J.map (τ w).1) (W.θ w)) →
        ∀ (q : (Fin n × Fin d → mixedEmbedding.mixedSpace F)), ∀ f ∈ M.Pol ψ τ, ∃ f₁ ∈ M.Pol ψ τ,
          ∀ x, f₁ x = (GlobalTheory.GaussLine.pairInf F (Fin n × Fin d) x q : ℂ) * f x := by
  first | exact @GlobalTheory.PolMul.pol_mul_pairInf_pair | exact GlobalTheory.PolMul.pol_mul_pairInf_pair | (intros; apply GlobalTheory.PolMul.pol_mul_pairInf_pair <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.reframe_vacuum_and_liftVector : ∀ (D : D7) (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V), StdFrame.OrthFrame (reS S b) → ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Lt D.host.E S.rank) (ΛT : Set (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (f₀ f : WO S T → ℂ), (ΛS : Set (Fin S.rank → D.host.E)) = L0c D S → Formalism.L2.DIV.IsFrame βS ΛS → IsThPVecOf ψ θ S T (fun _ => 1) sT (ΛS : Set (Fin S.rank → D.host.E)) ΛT βS βT Pg Q ξ f₀ f → ∃ βS' : GL (Fin (reS S b).rank) (Lev.EAf D), Formalism.L2.DIV.IsFrame βS' (stdL D.host.E (reS S b).rank) ∧ IsThPVecOf ψ θ (reS S b) T (fun _ => 1) sT (stdL D.host.E (reS S b).rank : Set (Fin (reS S b).rank → D.host.E)) ΛT βS' βT Pg Q ξ (reF S T b f₀) (reF S T b f) := by
  first | exact @GlobalTheory.AdSpan.ReVec.reframe_thPVecOf | exact GlobalTheory.AdSpan.ReVec.reframe_thPVecOf | (intros; apply GlobalTheory.AdSpan.ReVec.reframe_thPVecOf <;> assumption)
end
