module

import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle324
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.ProdGPn
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubsingletonOfGiso
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle001
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle947
public import Development.WeilBound.CoreStatements.AutomorphicKernels.BernsteinUnitaryProducts.IrreducibleAdmissibleReps.AdmissibleParabolicInduction.AdmProd
public import Development.WeilBound.CoreStatements.AutomorphicKernels.BernsteinUnitaryProducts.IrreducibleAdmissibleReps.AdmissibleParabolicInduction.IrrAdm
public import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
public import Mathlib.Basic.Complex.Basic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle318
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitarisableOfSquareIntegrable
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle309
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.GKLocal
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.ColMatMulGlEmbMat
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle310
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JhMultSubAddQuot
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NontrivialOfIrreducible
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.Sheaves.Presheaf
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle297
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.Bundle001
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm

@[expose] public section

section

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.LeibOrd.PsiIso

private theorem mapQ_eq_id_of_eq_id {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    (p : Submodule R M) {f : M →ₗ[R] M} (hf : f = LinearMap.id) (h : p ≤ p.comap f) :
    p.mapQ p f h = LinearMap.id := by
  subst hf
  exact Submodule.mapQ_id p h

private theorem mapQ_congr {R M M₂ : Type*} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup M₂]
    [Module R M₂] (p : Submodule R M) (q : Submodule R M₂) {f g : M →ₗ[R] M₂} (hfg : f = g)
    (hf : p ≤ q.comap f) (hg : p ≤ q.comap g) : p.mapQ q f hf = p.mapQ q g hg := by
  subst hfg
  rfl

theorem twAct_equiv {G M V W : Type} [Group G] [Group M] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (e : ρ.Equiv σ) (N : Subgroup G) (θ : N →* ℂˣ) (s : M →* G)
    (hs : ∀ (m : M) (n : N), ∃ h : s m * (n : G) * (s m)⁻¹ ∈ N, θ ⟨_, h⟩ = θ n) :
    Nonempty ((twAct ρ N θ s hs).Equiv (twAct σ N θ s hs)) := by
  apply GlobalTheory.CompanionTheory.LeibOrd.nonempty_twAct_equiv <;> assumption

theorem giso_psiN : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ)
    (A B : MRep k n), MIso A B → GIso (psiN A) (psiN B) := by
  intro k _ _ _ _ n A B ⟨e⟩
  exact GlobalTheory.CompanionTheory.LeibOrd.giso_tw _
    (GlobalTheory.CompanionTheory.LeibOrd.PsiIso.twAct_equiv e (GlobalTheory.BZMir.MirUin k n) 1
      (GlobalTheory.BZMir.levi k n) (GlobalTheory.BZMir.levi_normalises n))

end GlobalTheory.CompanionTheory.LeibOrd.PsiIso

end
end

section

namespace GlobalTheory.CompanionTheory.ProdAdm

theorem isAdmissible_multiProd_smIrr (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {c n : ℕ} (N : Fin c → ℕ) (h : ∑ i, N i = n)
    (σ : ∀ i, GlobalTheory.CuspRep.SmIrr (GL (Fin (N i)) k)) :
    GlobalTheory.PRep.IsAdmissible (GlobalTheory.SmGL.multiProd (GlobalTheory.SmGL.stdBlocks N h) fun i => (σ i).ρ) :=
  PositivityTheory.PfBern.Props1.isAdmissible_parInd_of _ _
    (GlobalTheory.ContraProd.isAdmissible_piTensor _ _ fun i =>
      PositivityTheory.PfBern.Props1.irrSmoothAdmissible_holds k (N i) (σ i).V (σ i).ρ (σ i).smooth (σ i).irred)

end GlobalTheory.CompanionTheory.ProdAdm
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib GlobalTheory.CompanionTheory.Rodier
open scoped TensorProduct

theorem _root_.GlobalTheory.T.projection_to_twisted_eigenfunction_support : ∀ {G : Type} {W : Type} [AddCommGroup W] [Module ℂ W] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (P : Subgroup G) (τ : Representation ℂ P W) (L : Subgroup G), IsCompact (L : Set G) → ∀ θ : L →* ℂˣ, IsOpen (θ.ker : Set L) → ∀ f : smoothPart (ind P τ), ∃ f' : smoothPart (ind P τ), f - f' ∈ twKer (smInd P τ) L θ ∧ (∀ g, f'.1.1 g ≠ 0 → ∃ l ∈ L, f.1.1 (g * l) ≠ 0) ∧ ∀ (l : L) (g : G), f'.1.1 (g * l) = (θ l : ℂ) • f'.1.1 g := by
  first | exact @GlobalTheory.CompanionTheory.TwAvgInd.exists_twisted_average_smInd | exact GlobalTheory.CompanionTheory.TwAvgInd.exists_twisted_average_smInd | (intros; apply GlobalTheory.CompanionTheory.TwAvgInd.exists_twisted_average_smInd <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL Filter Topology

namespace GlobalTheory.CompanionTheory.SqIntUnit

theorem isUnitarisable_of_isSqIntCoeff : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (x : IrrGL (k := k)), IsSqIntCoeff x.rep → IsUnitarisable x.rep := by
  intro k _ _ _ _ x h
  exact GlobalTheory.SqIntUnit.main k x.1 _ x.rep x.2.rep.smooth x.2.rep.irr h

end GlobalTheory.CompanionTheory.SqIntUnit
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg

namespace GlobalTheory.CompanionTheory.FrobInv

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]
  [Fintype n] [DecidableEq n] {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem mk_parab (e : (Σ a, m a) ≃ n) (τ : Representation ℂ (GL n k) V) (p : parab k e) (w : V) :
    (Submodule.Quotient.mk (τ (p : GL n k) w) : Jacquet τ (unipRad k e)) =
      Submodule.Quotient.mk (τ (leviEmb k e (leviProj k e p)) w) := by
  obtain ⟨u, hu, hp⟩ := exists_levi_mul_unip k e p
  have key : ∀ y : V, (Submodule.Quotient.mk (τ u y) : Jacquet τ (unipRad k e)) = Submodule.Quotient.mk y := by
    intro y
    rw [Submodule.Quotient.eq]
    apply Submodule.subset_span
    refine Set.mem_ofPred.mpr ⟨⟨u, hu⟩, y, ?_⟩
    simp
  have hL : ∀ y : V, (Submodule.Quotient.mk (τ (leviEmb k e (leviProj k e p)) y) : Jacquet τ (unipRad k e)) =
      ((deltaHalf k m (leviProj k e p) : ℂˣ) : ℂ) • _root_.GlobalTheory.SmGL.jac e τ (leviProj k e p) (Submodule.Quotient.mk y) := by
    intro y
    rw [_root_.GlobalTheory.SmGL.jac_mk, smul_smul, Units.mul_inv, one_smul]
  have e1 : τ (p : GL n k) w = τ (leviEmb k e (leviProj k e p)) (τ u w) := by
    first
    | (rw [hp, map_mul]; rfl)
    | rw [hp, map_mul]
  rw [e1, hL, hL, key]

def frobFun (e : (Σ a, m a) ≃ n) {τ : Representation ℂ (GL n k) V} {ρ : Representation ℂ (Levi k m) W}
    (f : (_root_.GlobalTheory.SmGL.jac e τ).IntertwiningMap ρ) (v : V) : GL n k → W :=
  fun g => f (Submodule.Quotient.mk (τ g v))

theorem frobFun_law (e : (Σ a, m a) ≃ n) {τ : Representation ℂ (GL n k) V} {ρ : Representation ℂ (Levi k m) W}
    (f : (_root_.GlobalTheory.SmGL.jac e τ).IntertwiningMap ρ) (v : V) (p : parab k e) (g : GL n k) :
    frobFun e f v (p * g) = (deltaHalf k m (leviProj k e p) : ℂ) • ρ (leviProj k e p) (frobFun e f v g) := by
  have h1 : frobFun e f v (p * g) =
      f (Submodule.Quotient.mk (τ (leviEmb k e (leviProj k e p)) (τ g v))) := by
    show f (Submodule.Quotient.mk (τ ((p : GL n k) * g) v)) = _
    rw [map_mul]
    exact congrArg f (mk_parab e τ p (τ g v))
  have h2 := LinearMap.congr_fun (f.isIntertwining' (leviProj k e p)) (Submodule.Quotient.mk (τ g v))
  simp only [LinearMap.comp_apply] at h2
  rw [h1]
  show f.toLinearMap (Submodule.Quotient.mk (τ (leviEmb k e (leviProj k e p)) (τ g v))) =
    ((deltaHalf k m (leviProj k e p) : ℂˣ) : ℂ) • ρ (leviProj k e p) (f.toLinearMap (Submodule.Quotient.mk (τ g v)))
  rw [← h2, _root_.GlobalTheory.SmGL.jac_mk, map_smul, smul_smul, Units.mul_inv, one_smul]

theorem frobFun_mem (e : (Σ a, m a) ≃ n) {τ : Representation ℂ (GL n k) V} {ρ : Representation ℂ (Levi k m) W}
    (f : (_root_.GlobalTheory.SmGL.jac e τ).IntertwiningMap ρ) (v : V) :
    frobFun e f v ∈ indSpace (parab k e) ((_root_.GlobalTheory.SmGL.twist ρ (deltaHalf k m)).comp (leviProj k e)) := by
  show ∀ (h : ↥(parab k e)) (g : GL n k),
    frobFun e f v (↑h * g) = ((_root_.GlobalTheory.SmGL.twist ρ (deltaHalf k m)).comp (leviProj k e)) h (frobFun e f v g)
  intro p x
  rw [frobFun_law, MonoidHom.comp_apply, _root_.GlobalTheory.SmGL.twist_apply]

theorem frobFun_translate (e : (Σ a, m a) ≃ n) {τ : Representation ℂ (GL n k) V} {ρ : Representation ℂ (Levi k m) W}
    (f : (_root_.GlobalTheory.SmGL.jac e τ).IntertwiningMap ρ) (v : V) (h x : GL n k) :
    frobFun e f v (x * h) = frobFun e f (τ h v) x := by
  show f (Submodule.Quotient.mk (τ (x * h) v)) = f (Submodule.Quotient.mk (τ x (τ h v)))
  first
  | (rw [map_mul]; rfl)
  | rw [map_mul]

theorem frobFun_smooth (e : (Σ a, m a) ≃ n) {τ : Representation ℂ (GL n k) V} (hτ : IsSmooth τ)
    {ρ : Representation ℂ (Levi k m) W} (f : (_root_.GlobalTheory.SmGL.jac e τ).IntertwiningMap ρ) (v : V) :
    (⟨frobFun e f v, frobFun_mem e f v⟩ : indSpace (parab k e) ((_root_.GlobalTheory.SmGL.twist ρ (deltaHalf k m)).comp (leviProj k e))) ∈
      smoothPart (ind (parab k e) ((_root_.GlobalTheory.SmGL.twist ρ (deltaHalf k m)).comp (leviProj k e))) := by
  show IsOpen {g : GL n k | (ind (parab k e) ((_root_.GlobalTheory.SmGL.twist ρ (deltaHalf k m)).comp (leviProj k e))) g
    ⟨frobFun e f v, frobFun_mem e f v⟩ = ⟨frobFun e f v, frobFun_mem e f v⟩}
  set F : indSpace (parab k e) ((_root_.GlobalTheory.SmGL.twist ρ (deltaHalf k m)).comp (leviProj k e)) :=
    ⟨frobFun e f v, frobFun_mem e f v⟩ with hF
  set R := ind (parab k e) ((_root_.GlobalTheory.SmGL.twist ρ (deltaHalf k m)).comp (leviProj k e)) with hR
  have hstab : ∀ s, τ s v = v → R s F = F := by
    intro s hs
    apply Subtype.ext
    funext x
    show frobFun e f v (x * s) = frobFun e f v x
    rw [frobFun_translate, hs]
  rw [isOpen_iff_forall_mem_open]
  intro g0 hg0
  refine ⟨(fun g => g0⁻¹ * g) ⁻¹' {g | τ g v = v}, ?_, IsOpen.preimage (continuous_const_mul g0⁻¹) (hτ v), ?_⟩
  · intro g hg
    have h1 : R (g0 * (g0⁻¹ * g)) F = R g0 (R (g0⁻¹ * g) F) := by
      first
      | (rw [map_mul]; rfl)
      | rw [map_mul]
    rw [mul_inv_cancel_left] at h1
    show R g F = F
    rw [h1, hstab _ hg]
    exact hg0
  · show τ (g0⁻¹ * g0) v = v
    rw [inv_mul_cancel, map_one]
    rfl

def frobInv (e : (Σ a, m a) ≃ n) {τ : Representation ℂ (GL n k) V} (hτ : IsSmooth τ)
    {ρ : Representation ℂ (Levi k m) W} (f : (_root_.GlobalTheory.SmGL.jac e τ).IntertwiningMap ρ) :
    τ.IntertwiningMap (parInd e ρ) where
  toLinearMap :=
    { toFun := fun v => ⟨⟨frobFun e f v, frobFun_mem e f v⟩, frobFun_smooth e hτ f v⟩
      map_add' := fun v w => by
        refine Subtype.ext (Subtype.ext (funext fun g => ?_))
        show f (Submodule.Quotient.mk (τ g (v + w))) = f (Submodule.Quotient.mk (τ g v)) + f (Submodule.Quotient.mk (τ g w))
        rw [map_add (f := _), Submodule.Quotient.mk_add, map_add (f := _)]
      map_smul' := fun c v => by
        refine Subtype.ext (Subtype.ext (funext fun g => ?_))
        show f (Submodule.Quotient.mk (τ g (c • v))) = c • f (Submodule.Quotient.mk (τ g v))
        rw [map_smul, Submodule.Quotient.mk_smul, map_smul] }
  isIntertwining' g := by
    refine LinearMap.ext fun v => Subtype.ext (Subtype.ext (funext fun x => ?_))
    exact (frobFun_translate e f v g x).symm

theorem frobInv_one (e : (Σ a, m a) ≃ n) {τ : Representation ℂ (GL n k) V} (hτ : IsSmooth τ)
    {ρ : Representation ℂ (Levi k m) W} (f : (_root_.GlobalTheory.SmGL.jac e τ).IntertwiningMap ρ) (v : V) :
    (frobInv e hτ f v).1.1 1 = f (Submodule.Quotient.mk v) := by
  show f (Submodule.Quotient.mk (τ 1 v)) = f (Submodule.Quotient.mk v)
  first
  | (rw [map_one]; rfl)
  | rw [map_one]

theorem exists_frobInv_ne_zero (e : (Σ a, m a) ≃ n) {τ : Representation ℂ (GL n k) V} (hτ : IsSmooth τ)
    {ρ : Representation ℂ (Levi k m) W} (f : (_root_.GlobalTheory.SmGL.jac e τ).IntertwiningMap ρ) (hf : ∃ v, f v ≠ 0) :
    ∃ v, frobInv e hτ f v ≠ 0 := by
  obtain ⟨w, hw⟩ := hf
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  refine ⟨v, fun h => hw ?_⟩
  have h1 := frobInv_one e hτ f v
  rw [h] at h1
  exact h1.symm

theorem exists_map_prodIrr {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {h N : ℕ} (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N) {V : Type} [AddCommGroup V] [Module ℂ V]
    (τ : Representation ℂ (GL (Fin N) k) V) (hτ : IsSmooth τ)
    (f : (_root_.GlobalTheory.SmGL.jac (stdBlocks (fun a => (x a).1) hd) τ).IntertwiningMap (piTensor fun a => (x a).rep))
    (hf : ∃ v, f v ≠ 0) : ∃ g : τ.IntertwiningMap (prodIrr x hd), ∃ v, g v ≠ 0 := by
  exact ⟨frobInv (stdBlocks (fun a => (x a).1) hd) hτ f, exists_frobInv_ne_zero _ hτ f hf⟩

end GlobalTheory.CompanionTheory.FrobInv

end
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct

theorem _root_.GlobalTheory.T.generic_has_generic_irreducible_subquotient : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ∀ (N : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin N) k) V), IsSmooth ρ → GlobalTheory.SmGL.HasFiniteLength ρ → IsGenericFor ψ ρ → ∃ A B : Subrepresentation ρ, B ≤ A ∧ (subQuot A B).IsIrreducible ∧ IsSmooth (subQuot A B) ∧ IsGenericFor ψ (subQuot A B) := by
  first | exact @GlobalTheory.CompanionTheory.GenExists.exists_generic_subQuot | exact GlobalTheory.CompanionTheory.GenExists.exists_generic_subQuot | (intros; apply GlobalTheory.CompanionTheory.GenExists.exists_generic_subQuot <;> assumption)
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos

namespace GlobalTheory.CompanionTheory.StdQuot

section Theta

variable {k : Type} [Field k] {N : ℕ}

theorem thetaW_apply (g : GL (Fin N) k) (i j : Fin N) :
    (thetaW k N g).val i j = (g⁻¹).val (Fin.rev j) (Fin.rev i) := by
  simp [thetaW, invT, Matrix.reindexAlgEquiv_apply]

theorem thetaW_mem_unipB {u : GL (Fin N) k} (hu : u ∈ unipB k (Fin N)) : thetaW k N u ∈ unipB k (Fin N) := by
  have hi := (mem_unipB k).1 (inv_mem hu)
  refine (mem_unipB k).2 ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [thetaW_apply]
    exact hi.1 _ _ (Fin.rev_lt_rev.2 hij)
  · rw [thetaW_apply]
    exact hi.2 _

theorem whitChar_thetaW (ψ : AddChar k Circle) (u : unipB k (Fin N)) :
    whitChar ψ N ⟨thetaW k N u, thetaW_mem_unipB u.2⟩ = whitChar ψ N u⁻¹ := by
  show Circle.toUnits (ψ _) = Circle.toUnits (ψ _)
  refine congrArg (fun s => Circle.toUnits (ψ s)) ?_
  refine Finset.sum_nbij' (fun p => (Fin.rev p.2, Fin.rev p.1)) (fun p => (Fin.rev p.2, Fin.rev p.1)) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    have h := (Finset.mem_filter.1 hp).2
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
    simp only [Fin.val_rev]
    have := p.1.2
    have := p.2.2
    omega
  · intro p hp
    have h := (Finset.mem_filter.1 hp).2
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
    simp only [Fin.val_rev]
    have := p.1.2
    have := p.2.2
    omega
  · intro p _
    simp
  · intro p _
    simp
  · intro p _
    simp only [thetaW_apply]
    rfl

theorem whitChar_inv (ψ : AddChar k Circle) (u : unipB k (Fin N)) :
    whitChar ψ⁻¹ N u = whitChar ψ N u⁻¹ := by
  rw [map_inv]
  show Circle.toUnits (ψ⁻¹ _) = (Circle.toUnits (ψ _))⁻¹
  rw [AddChar.inv_apply', map_inv]

end Theta

section Main

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable {k}

variable (k)

end Main

end GlobalTheory.CompanionTheory.StdQuot

end
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct

theorem _root_.GlobalTheory.T.multiProd_equiv_standard_blocks : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) (e : (Σ a, Fin (d a)) ≃ Fin N) (X : Fin h → Type) [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (π : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a)), Nonempty ((multiProd e π).Equiv (multiProd (stdBlocks d hd) π)) := by
  first | exact @GlobalTheory.CompanionTheory.GenMultiProd.multiProd_equiv_stdBlocks | exact GlobalTheory.CompanionTheory.GenMultiProd.multiProd_equiv_stdBlocks | (intros; apply GlobalTheory.CompanionTheory.GenMultiProd.multiProd_equiv_stdBlocks <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir Zc

theorem _root_.GlobalTheory.T.invariant_pairing_mirabolic_vanishing : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (n s : ℕ) (V V' : Type) [AddCommGroup V] [Module ℂ V]
    [AddCommGroup V'] [Module ℂ V'] (T : Representation ℂ (Mir k (n + 1)) V) (T' : Representation ℂ (Mir k (n + 1)) V'),
    IsSmooth T → IsSmooth T' → ∀ B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ,
    (∀ (p : Mir k (n + 1)) v v', B (T p v) (T' p v') =
      ((detChar (Fin (n + 1 + 1)) (absPow k (s : ℂ)) (p : GL (Fin (n + 1 + 1)) k) : ℂˣ) : ℂ) * B v v') →
    (∀ v, v ≠ 0 → ∃ v', B v v' ≠ 0) →
    Subsingleton (TwJacquet T (MirUin k (n + 1)) (mirChar k ψ n)) →
    ∃ B' : TwJacquet T (MirUin k (n + 1)) 1 →ₗ[ℂ] TwJacquet T' (MirUin k (n + 1)) 1 →ₗ[ℂ] ℂ,
      (∀ (g : GL (Fin (n + 1)) k) w w', B' (psiMinus k T g w) (psiMinus k T' g w') =
        ((detChar (Fin (n + 1)) (absPow k (s : ℂ)) g : ℂˣ) : ℂ) * B' w w') ∧
      (∀ w, w ≠ 0 → ∃ w', B' w w' ≠ 0) := by
  first | exact @GlobalTheory.CompanionTheory.MirPsiPair.pair_psi | exact GlobalTheory.CompanionTheory.MirPsiPair.pair_psi | (intros; apply GlobalTheory.CompanionTheory.MirPsiPair.pair_psi <;> assumption)
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg

namespace GlobalTheory.CompanionTheory.FineStep

theorem isSubquotient_subQuot_self {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    {J : Representation ℂ G V} (S R : Subrepresentation J) : IsSubquotient (subQuot S R) J := by
  refine GlobalTheory.SmGL.IsSubquotient.trans (σ := S.toRepresentation) ?_ ?_
  · refine GlobalTheory.SmGL.IsSubquotient.of_surjective
      ⟨(Submodule.comap S.toSubmodule.subtype R.toSubmodule).mkQ, fun g => ?_⟩ ?_
    · ext v
      rfl
    · exact Submodule.mkQ_surjective _
  · refine GlobalTheory.SmGL.IsSubquotient.of_injective ⟨S.toSubmodule.subtype, fun g => ?_⟩ ?_
    · ext v
      rfl
    · exact Subtype.val_injective

theorem nonempty_equiv_of_jhMult_eq_one :
    ∀ {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
      (T : Representation ℂ G W) (J : Representation ℂ G V), T.IsIrreducible → HasFiniteLength J →
      jhMult T J = 1 →
      (∀ (X : Type) [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ G X), ρ.IsIrreducible →
        IsSubquotient ρ J → Nonempty (ρ.Equiv T)) → Nonempty (J.Equiv T) := by
  intro G V W _ _ _ _ _ T J hT hfin hJ hall
  have hstep : ∀ {P Q : Subrepresentation J}, Q ⋖ P → GlobalTheory.JHMult.Step T P Q := fun {P Q} h =>
    GlobalTheory.JHMult.step_iff.mp
      (hall _ (subQuot P Q) (GlobalTheory.SmGL.isIrreducible_subQuot h) (isSubquotient_subQuot_self P Q))
  have hwf : WellFounded ((· < ·) : Subrepresentation J → Subrepresentation J → Prop) := by
    haveI : IsArtinian (MonoidAlgebra ℂ G) J.asModule :=
      (isFiniteLength_iff_isNoetherian_isArtinian.mp
        (show IsFiniteLength (MonoidAlgebra ℂ G) J.asModule from hfin)).2
    exact (Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := J)).toOrderEmbedding.ltEmbedding.wellFounded
      wellFounded_lt
  have hne : (⊥ : Subrepresentation J) ≠ ⊤ := by
    intro h
    haveI : Subsingleton V := ⟨fun a b => by
      have ha : a ∈ (⊤ : Subrepresentation J).toSubmodule := Submodule.mem_top
      have hb : b ∈ (⊤ : Subrepresentation J).toSubmodule := Submodule.mem_top
      rw [← h] at ha hb
      rw [(Submodule.mem_bot ℂ).mp ha, (Submodule.mem_bot ℂ).mp hb]⟩
    have h0 := GlobalTheory.SmGL.jhMult_of_subsingleton hT J
    rw [hJ] at h0
    exact one_ne_zero h0
  have hirr : J.IsIrreducible := by
    show IsSimpleOrder (Subrepresentation J)
    refine { exists_pair_ne := ⟨⊥, ⊤, hne⟩, eq_bot_or_eq_top := fun S => ?_ }
    by_contra hS
    obtain ⟨hS0, hS1⟩ := not_or.mp hS
    obtain ⟨A, ⟨hA0, hAS⟩, hAmin⟩ := hwf.has_min {A | ⊥ < A ∧ A ≤ S}
      ⟨S, show ⊥ < S ∧ S ≤ S from ⟨bot_lt_iff_ne_bot.mpr hS0, le_rfl⟩⟩
    obtain ⟨B, hB, hBmin⟩ := hwf.has_min {B | S < B}
      ⟨⊤, show S < ⊤ from lt_top_iff_ne_top.mpr hS1⟩
    have hcA : (⊥ : Subrepresentation J) ⋖ A := ⟨hA0, by
      intro c hc hcA
      exact hAmin c (show ⊥ < c ∧ c ≤ S from ⟨hc, hcA.le.trans hAS⟩) hcA⟩
    have hSB : S < B := hB
    have hcB : S ⋖ B := ⟨hSB, by
      intro c hc hcB
      exact hBmin c (show S < c from hc) hcB⟩
    have hocc : GlobalTheory.SmGL.OccursTimes T J 2 := by
      have := GlobalTheory.JHMult.occurs_of_finset (σ := T) (ρ := J) (r := 2) Finset.univ ![A, B] ![⊥, S]
        (by simp [Fin.forall_fin_two, hSB.le]) (by simp [Fin.forall_fin_two, hAS])
        (by simp [Fin.forall_fin_two, hstep hcA, hstep hcB])
      simpa using this
    have h2 : ((2 : ℕ) : ℕ∞) ≤ GlobalTheory.SmGL.jhMult T J := by
      unfold GlobalTheory.SmGL.jhMult
      exact le_iSup₂_of_le 2 hocc le_rfl
    rw [hJ] at h2
    have h21 : ¬ ((2 : ℕ) : ℕ∞) ≤ ((1 : ℕ) : ℕ∞) := by
      rw [ENat.natCast_le_natCast]
      omega
    exact h21 (by simpa using h2)
  exact hall V J hirr (GlobalTheory.SmGL.IsSubquotient.refl J)

end GlobalTheory.CompanionTheory.FineStep
end
end
