module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle315
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
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

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

namespace GlobalTheory.ConjFinArch

variable {D : D7}

def eInf (F : Type) [Field F] [NumberField F] : AF F :=
  ((1 : Ainf F), (0 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F))

theorem one_sub_eInf_fst (F : Type) [Field F] [NumberField F] : (1 - eInf F).1 = 0 := by
  show (1 : Ainf F) - 1 = 0
  exact sub_self _

theorem evI_sub_eInf (F : Type) [Field F] [NumberField F] : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F (1 - eInf F) = 0 := by
  rw [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI, one_sub_eInf_fst, map_zero]

theorem eInf_smul_tmul (a : AF D.host.F) (y : D.host.E) :
    eInf D.host.F • (a ⊗ₜ[D.host.F] y) = (eInf D.host.F * a) ⊗ₜ[D.host.F] y := by
  rfl

def incInf (F : Type) [Field F] [NumberField F] : Ainf F →ₗ[F] AF F where
  toFun x := ((x, (0 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F)) : AF F)
  map_add' x y := by
    show ((x + y, (0 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F)) : Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) = (x + y, 0 + 0)
    rw [add_zero]
  map_smul' c x := by
    show ((c • x, (0 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F)) : Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) = (c • x, c • (0 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F))
    rw [smul_zero]

theorem eInf_mul' (a : AF D.host.F) : eInf D.host.F * a = incInf D.host.F (fstA D.host.F a) := by
  show ((1 : Ainf D.host.F) * a.1, (0 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) * a.2) = (a.1, 0)
  rw [one_mul, zero_mul]

theorem cA_tmul (a : AF D.host.F) (y : D.host.E) :
    cA D (a ⊗ₜ[D.host.F] y) = a ⊗ₜ[D.host.F] D.sp.cm.sig y := by
  show Algebra.TensorProduct.map (AlgHom.id D.host.F (AF D.host.F)) D.sp.cm.sig (a ⊗ₜ[D.host.F] y) = _
  rw [Algebra.TensorProduct.map_tmul]
  rfl

theorem smul_tmul_AF (r a : AF D.host.F) (y : D.host.E) :
    r • (a ⊗ₜ[D.host.F] y) = (r * a) ⊗ₜ[D.host.F] y := rfl

theorem cA_smul (r : AF D.host.F) (x : AF D.host.F ⊗[D.host.F] D.host.E) : cA D (r • x) = r • cA D x := by
  induction x using TensorProduct.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | tmul a y => rw [smul_tmul_AF, cA_tmul, cA_tmul, smul_tmul_AF]
  | add x y hx hy => rw [smul_add, map_add (f := _), hx, hy, map_add (f := _), smul_add]



theorem eInf_smul (x : AF D.host.F ⊗[D.host.F] D.host.E) :
    eInf D.host.F • x = TensorProduct.map (incInf D.host.F) LinearMap.id
      (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) x) := by
  have key : DistribSMul.toLinearMap D.host.F (AF D.host.F ⊗[D.host.F] D.host.E) (eInf D.host.F) =
      (TensorProduct.map (incInf D.host.F) (LinearMap.id : D.host.E →ₗ[D.host.F] D.host.E)).comp
        (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)).toLinearMap := by
    refine TensorProduct.ext' fun a y => ?_
    show eInf D.host.F • (a ⊗ₜ[D.host.F] y) = TensorProduct.map (incInf D.host.F) LinearMap.id
      (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) (a ⊗ₜ[D.host.F] y))
    rw [eInf_smul_tmul, eInf_mul', Algebra.TensorProduct.map_tmul]
    rfl
  exact LinearMap.congr_fun key x

theorem eInf_smul_eq_zero {x : AF D.host.F ⊗[D.host.F] D.host.E}
    (hx : Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) x = 0) : eInf D.host.F • x = 0 := by
  rw [eInf_smul, hx, map_zero]

theorem one_apply_map {R S : Type} [Semiring R] [Semiring S] {n : ℕ} (f : R →+* S) (i j : Fin n) :
    f ((1 : Matrix (Fin n) (Fin n) R) i j) = (1 : Matrix (Fin n) (Fin n) S) i j := by
  rw [Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem eInf_smul_conjU_sub_one (V : HSp D) {J : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (c : D.host.E)
    (hJ : J = c • V.gram) {g : GA D V} (hg : g ∈ GfC V) (i j : Fin V.rank) :
    eInf D.host.F • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU V c hJ g) - 1) i j = 0 := by
  have hm : (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU V c hJ g) - 1) i j = cA D (mt V g i j - (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j) := by
    rw [map_sub, Matrix.sub_apply, one_apply_map]
    rfl
  have hinf : infHom V g = 1 := hg
  have he : Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) (mt V g i j) =
      (1 : Matrix (Fin V.rank) (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E)) i j := by
    have := congrArg (fun h : GL (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E) => h.1 i j) hinf
    exact this
  rw [hm, ← cA_smul, eInf_smul_eq_zero, map_zero]
  rw [map_sub, he]
  exact sub_eq_zero.2 (one_apply_map (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom i j).symm

end GlobalTheory.ConjFinArch

theorem GlobalTheory.ConjFinArch.smul_mat_conjU_sub_one : ∀ (D : D7) (V : HSp D) {J : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (c : D.host.E) (hJ : J = c • V.gram)
    (g : GA D V), g ∈ GfC V → ∀ u : AF D.host.F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) u →
      u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU V c hJ g) - 1) = 0 := by
  intro D V J c hJ g hg u hu
  have h1 : (1 - GlobalTheory.ConjFinArch.eInf D.host.F) * u = 0 := hu _ (GlobalTheory.ConjFinArch.evI_sub_eInf _)
  have h2 : u = u * GlobalTheory.ConjFinArch.eInf D.host.F := by
    rw [sub_mul, one_mul, sub_eq_zero] at h1
    rw [mul_comm]; exact h1
  rw [h2, mul_smul]
  have h3 : GlobalTheory.ConjFinArch.eInf D.host.F • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU V c hJ g) - 1) = 0 := by
    ext i j
    rw [Matrix.smul_apply, GlobalTheory.ConjFinArch.eInf_smul_conjU_sub_one V c hJ hg i j, Matrix.zero_apply]
  rw [h3, smul_zero]
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
open scoped ComplexConjugate
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

namespace GlobalTheory.Twist.RestrictionTransfer

theorem rest_transfer : ∀ (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ] (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ) (r : (κ → AF F) → ℂ),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) f r → (∃ x, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) f r x ≠ 0) →
    ∀ f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) f₁ r := by
  intro F _ _ κ _ f r ⟨hinv, hsch⟩ ⟨x₀, hx₀⟩ f₁
  refine ⟨hinv, ?_⟩
  set a₀ : κ → mixedEmbedding.mixedSpace F := fun i => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F (x₀ i) with ha₀
  have hc : f a₀ ≠ 0 := by
    intro h; apply hx₀; simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens]; rw [← ha₀, h, zero_mul]
  let zz : (κ → AF F) → (κ → AF F) := fun x i =>
    (((x₀ i).1 - (x i).1, 0) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)
  have hz1 : ∀ x i, (x i + zz x i).1 = (x₀ i).1 := by
    intro x i; show (x i).1 + ((x₀ i).1 - (x i).1) = _; ring
  have hz2 : ∀ x i, (x i + zz x i).2 = (x i).2 := by
    intro x i; show (x i).2 + 0 = _; simp
  have hev : ∀ x, (fun i => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F ((x + zz x) i)) = a₀ := by
    intro x; funext i; simp only [Pi.add_apply, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI, ha₀]; rw [hz1]
  have hAt : ∀ x, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (zz x) := by
    intro x u hu
    have hu1 : u.1 = 0 := by
      exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).map_eq_zero_iff.mp hu
    funext i
    show ((u.1 * ((x₀ i).1 - (x i).1), u.2 * 0) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F) = (0, 0)
    rw [hu1]; simp
  let L : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ) :=
    { toFun := fun Φ x => f₁ (fun i => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F (x i)) * Φ (x + zz x)
      map_add' := by intro Φ Ψ; funext x; simp [mul_add]
      map_smul' := by intro c Φ; funext x; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
  have key : ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, L Φ ∈ GlobalTheory.WeilM.schA F κ := by
    intro Φ hΦ
    induction hΦ using Submodule.span_induction with
    | mem Φ hΦ =>
      obtain ⟨g, h, hh, rfl⟩ := hΦ
      have : L (GlobalTheory.WeilM.pureA F g h) = g a₀ • GlobalTheory.WeilM.pureA F f₁ h := by
        funext x
        have e := hev x
        simp only [L, LinearMap.coe_mk, AddHom.coe_mk, GlobalTheory.WeilM.pureA, Pi.smul_apply, smul_eq_mul]
        simp only [Pi.add_apply, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI] at e ⊢
        rw [e]
        have : (fun i => (x i + zz x i).2) = fun i => (x i).2 := funext fun i => hz2 x i
        rw [this]; ring
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨f₁, h, hh, rfl⟩)
    | zero => simp
    | add Φ Ψ _ _ h1 h2 => rw [map_add (f := _)]; exact Submodule.add_mem _ h1 h2
    | smul c Φ _ h1 => rw [map_smul]; exact Submodule.smul_mem _ c h1
  have hLt : L (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) f r) =
      f a₀ • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) f₁ r := by
    funext x
    simp only [L, LinearMap.coe_mk, AddHom.coe_mk, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens, Pi.smul_apply, smul_eq_mul]
    rw [hev x, hinv x (zz x) (hAt x)]; ring
  have hm := key _ hsch
  rw [hLt] at hm
  have := Submodule.smul_mem _ (f a₀)⁻¹ hm
  rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this

end GlobalTheory.Twist.RestrictionTransfer
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

namespace GlobalTheory.ArchCancel

theorem eq_of_tens_eq : ∀ (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ] (r : (κ → AF F) → ℂ),
    (∀ x z, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) z → r (x + z) = r x) → (∃ x, r x ≠ 0) →
    ∀ f₁ f₂ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ,
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) f₁ r = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) f₂ r → f₁ = f₂ := by
  intro F _ _ κ _ r hr hne f₁ f₂ h
  obtain ⟨x₀, hx₀⟩ := hne
  refine DFunLike.ext f₁ f₂ fun y => ?_
  let z : κ → AF F := fun i =>
    ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y i - GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F (x₀ i)), 0)
  have hz : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) z := by
    intro u hu
    funext i
    have hu1 : u.1 = 0 := by
      have : InfiniteAdeleRing.ringEquiv_mixedSpace F u.1 = 0 := hu
      exact (map_eq_zero_iff _ (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective).mp this
    show u * z i = 0
    refine Prod.ext ?_ ?_
    · show u.1 * (z i).1 = 0
      rw [hu1, zero_mul]
    · show u.2 * (z i).2 = 0
      show u.2 * 0 = 0
      rw [mul_zero]
  have hev : (fun i => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F ((x₀ + z) i)) = y := by
    funext i
    show InfiniteAdeleRing.ringEquiv_mixedSpace F ((x₀ i).1 +
      (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y i - GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F (x₀ i))) = y i
    rw [map_add (f := _), RingEquiv.apply_symm_apply]
    show GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F (x₀ i) + (y i - GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F (x₀ i)) = y i
    exact add_sub_cancel _ _
  have h2 := congrFun h (x₀ + z)
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens] at h2
  rw [hev, hr x₀ z hz] at h2
  exact mul_right_cancel₀ hx₀ h2

end GlobalTheory.ArchCancel
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

namespace GlobalTheory.TripleAssembly.PureImage

theorem det_ne_of_sig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.HasSig M r s) : M.det ≠ 0 := by
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

theorem det_ne_of_sig_map {E : Type} [Field E] {n r s : ℕ} {J : Matrix (Fin n) (Fin n) E} (τ : E →+* ℂ) (c : ℂ)
    (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.HasSig (c • J.map τ) r s) : J.det ≠ 0 := by
  intro h0
  refine det_ne_of_sig h ?_
  have : (J.map τ).det = τ J.det := (RingHom.map_det τ J).symm
  rw [Matrix.det_smul, this, h0, map_zero, mul_zero]

theorem exists_factor_inj {U V P : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V] [AddCommGroup P]
    [Module ℂ P] (T : U →ₗ[ℂ] V) (S : Submodule ℂ U) (hT : ∀ x ∈ S, T x = 0 → x = 0) (p : U →ₗ[ℂ] P) :
    ∃ q : V →ₗ[ℂ] P, ∀ x ∈ S, q (T x) = p x := by
  obtain ⟨r, hr⟩ := (T.comp S.subtype).exists_leftInverse_of_injective (by
    rw [LinearMap.ker_eq_bot']
    exact fun x hx => Subtype.ext (hT x.1 x.2 hx))
  refine ⟨p.comp (S.subtype.comp r), fun x hx => ?_⟩
  have := LinearMap.congr_fun hr ⟨x, hx⟩
  change r (T x) = ⟨x, hx⟩ at this
  simp [this]

end GlobalTheory.TripleAssembly.PureImage
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

open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.TwistRest

open scoped Classical in
theorem restTr : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (f f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ) (r : (κ → AF F) → ℂ),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) f r → f ≠ 0 → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) f₁ r := by
  intro F _ _ κ _ f f₁ r hr hf
  obtain ⟨hinv, hsch⟩ := hr

  set g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ := fun y => r (fun i => ((0 : InfiniteAdeleRing F), y i)) with hgdef
  have hrg : ∀ x : κ → AF F, r x = g (fun i => (x i).2) := by
    intro x
    let z : κ → AF F := fun i => ((x i).1, (0 : FiniteAdeleRing (𝓞 F) F))
    have hz : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) z := by
      intro u hu
      have hu1 : u.1 = 0 :=
        (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact hu)
      funext i
      change (u * z i : AF F) = 0
      refine Prod.ext ?_ ?_
      · change u.1 * (x i).1 = 0
        rw [hu1, zero_mul]
      · change u.2 * 0 = 0
        exact mul_zero _
    let x' : κ → AF F := fun i => ((0 : InfiniteAdeleRing F), (x i).2)
    have := hinv x' z hz
    have hx : x = x' + z := by
      funext i
      refine Prod.ext ?_ ?_
      · change (x i).1 = (0 : InfiniteAdeleRing F) + (x i).1
        rw [zero_add]
      · change (x i).2 = (x i).2 + (0 : FiniteAdeleRing (𝓞 F) F)
        rw [add_zero]
    exact (congrArg r hx).trans this
  have htens : ∀ f' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ,
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (⇑f') r = GlobalTheory.WeilM.pureA F (⇑f') g := by
    intro f'
    funext x
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens, GlobalTheory.WeilM.pureA, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI]
    rw [hrg x]

  obtain ⟨x₀, hx₀⟩ : ∃ x₀, f x₀ ≠ 0 := by
    by_contra h
    push_neg at h
    exact hf (SchwartzMap.ext h)
  let a : κ → InfiniteAdeleRing F := fun i => (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (x₀ i)
  let Λ : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → FiniteAdeleRing (𝓞 F) F) → ℂ) :=
    { toFun := fun Φ y => Φ (fun i => (a i, y i))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hΛ : ∀ (f' : (κ → mixedEmbedding.mixedSpace F) → ℂ) (g' : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ),
      Λ (GlobalTheory.WeilM.pureA F f' g') = f' x₀ • g' := by
    intro f' g'
    funext y
    change f' (fun i => (InfiniteAdeleRing.ringEquiv_mixedSpace F) (a i)) * g' y = f' x₀ * g' y
    congr 1
    apply congrArg f'
    funext i
    exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply (x₀ i)
  have hle : GlobalTheory.WeilM.schA F κ ≤ (GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F)).comap Λ := by
    refine Submodule.span_le.2 ?_
    rintro Φ ⟨f', g', hg', rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap, hΛ]
    exact Submodule.smul_mem _ _ hg'
  have hg : g ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F) := by
    have h1 := hle (htens f ▸ hsch)
    rw [Submodule.mem_comap, hΛ] at h1
    have := Submodule.smul_mem _ (f x₀)⁻¹ h1
    rwa [smul_smul, inv_mul_cancel₀ hx₀, one_smul] at this
  refine ⟨hinv, ?_⟩
  rw [htens f₁]
  exact Submodule.subset_span ⟨f₁, g, hg, rfl⟩

end GlobalTheory.TwistRest
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm

namespace GlobalTheory.SquareAgree

theorem I_smul {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Y Wd) (s : ℂ) (Φ : (Fin n × Fin d → AF F) → ℂ) (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ Wd.J) :
    M.I om (s • Φ) h = s * M.I om Φ h := by
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model.I, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.theta, map_smul, GlobalTheory.WeilM.thetaSum, Pi.smul_apply, smul_eq_mul,
    tsum_mul_left, integral_const_mul]

end GlobalTheory.SquareAgree

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.continuous_restrictedWeilFirstFactor_apply : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E) (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χS χT ω → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D W.rank r) μ 𝓨 → ∀ (f : WO V W → ℂ), IsThetaFunO ψ V W f → ∀ x, Continuous fun m : GA D V => GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (ω (m, 1) f) x := by
  first | exact @GlobalTheory.ResFirstCont.continuous_res_left | exact GlobalTheory.ResFirstCont.continuous_res_left | (intros; apply GlobalTheory.ResFirstCont.continuous_res_left <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.continuous_restrictedHeisenbergWeilTranslate_at_zero : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χS χT ω → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ f, IsThetaFunO ψ V W f → ∀ u : WO V W, Continuous fun p : GA D V × GA D W => res V V' W C B μ 𝓨 (heisO ψ V W u (ω p f)) 0 := by
  first | exact @GlobalTheory.ResHeisCont.continuous_res_heisO | exact GlobalTheory.ResHeisCont.continuous_res_heisO | (intros; apply GlobalTheory.ResHeisCont.continuous_res_heisO <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.isotropic_part_rational_characters_adelic_matrices : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ C' : Matrix (Fin V.rank) (Fin r) D.host.E, adj D C * V.gram * C' = 1 → adj D C' * V.gram * C' = 0 → adj D C' * V.gram * B = 0 → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → (∀ (a : Matrix (Fin W.rank) (Fin r) D.host.E), Continuous fun t : Mx D W.rank r => ψ (symplO V W (isoPart V W C' t) (isoPart V W C (a.map (incA D))))) ∧ (∀ (a : Matrix (Fin W.rank) (Fin r) D.host.E) t s, ψ (symplO V W (isoPart V W C' (t + s)) (isoPart V W C (a.map (incA D)))) = ψ (symplO V W (isoPart V W C' t) (isoPart V W C (a.map (incA D)))) * ψ (symplO V W (isoPart V W C' s) (isoPart V W C (a.map (incA D))))) ∧ (∀ (a b : Matrix (Fin W.rank) (Fin r) D.host.E) t, ψ (symplO V W (isoPart V W C' t) (isoPart V W C ((a + b).map (incA D)))) = ψ (symplO V W (isoPart V W C' t) (isoPart V W C (a.map (incA D)))) * ψ (symplO V W (isoPart V W C' t) (isoPart V W C (b.map (incA D))))) ∧ (∀ t, (∀ a : Matrix (Fin W.rank) (Fin r) D.host.E, ψ (symplO V W (isoPart V W C' t) (isoPart V W C (a.map (incA D)))) = 1) ↔ t ∈ ratMx D W.rank r) ∧ ∀ a : Matrix (Fin W.rank) (Fin r) D.host.E, (∀ t, ψ (symplO V W (isoPart V W C' t) (isoPart V W C (a.map (incA D)))) = 1) → a = 0 := by
  first | exact @GlobalTheory.IsoDualChars.chars | exact GlobalTheory.IsoDualChars.chars | (intros; apply GlobalTheory.IsoDualChars.chars <;> assumption)
end
