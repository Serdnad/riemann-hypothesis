module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle073
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle120
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle124
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsCuspFunIffConstTerm
public import Formalism.LocalToGlobal.KernelLattices.ThDistC
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle123
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle125
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle038
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.AdelicUnitaryGroups

@[expose] public section

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound

theorem _root_.GlobalTheory.T.support_parahoricBiTransforming_doubleCosets : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k →
  ∀ (r l t : ℕ) (ξ : kˣ →* ℂˣ), IsTame ξ → ¬ IsUnram ξ →
  ∀ φ : GL (Fin r ⊕ Blocks l t) k → ℂ, IsBiType ξ φ →
    (∀ x y, φ (emb₂ k (Equiv.refl (Fin r ⊕ Blocks l t)) (x, y)) ≠ 0 → x ∈ KO k (Fin r)) →
    ∀ g, φ g ≠ 0 → ∃ e : Fin (l * t) → ℤ, Antitone e ∧ g ∈ dcell ϖ (e ∘ (blkEquiv l t).symm) := by
  first | exact @GlobalTheory.ChainStepSupp.support_dcell | exact GlobalTheory.ChainStepSupp.support_dcell | (intros; apply GlobalTheory.ChainStepSupp.support_dcell <;> assumption)
end

section

open GlobalTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SmGL.Exponents ValuativeRel
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.SmGL.Exponents

section Bool

variable {X : Bool → Type} [∀ x, AddCommGroup (X x)] [∀ x, Module ℂ (X x)]

def boolPair (v : X false) (w : X true) : ∀ x, X x
  | false => v
  | true => w

def boolMulti : (∀ x, X x) →ₘₗ[ℂ] (X false ⊗[ℂ] X true) :=
  MultilinearMap.mk' (fun x => x false ⊗ₜ[ℂ] x true)
    (fun m i x y => by cases i <;> simp [TensorProduct.add_tmul, TensorProduct.tmul_add])
    (fun m i c x => by cases i <;> simp [TensorProduct.smul_tmul', TensorProduct.tmul_smul])

theorem boolPair_eq_right (v : X false) (w w' : X true) :
    boolPair v w = Function.update (boolPair v w') true w := by
  funext x; cases x <;> simp [boolPair]

theorem boolPair_eq_left (v v' : X false) (w : X true) :
    boolPair v w = Function.update (boolPair v' w) false v := by
  funext x; cases x <;> simp [boolPair]

def boolBilin : X false →ₗ[ℂ] X true →ₗ[ℂ] PiTensorProduct ℂ X :=
  LinearMap.mk₂ ℂ (fun v w => PiTensorProduct.tprod ℂ (boolPair v w))
    (fun v v' w => by
      rw [boolPair_eq_left (v + v') 0, boolPair_eq_left v 0, boolPair_eq_left v' 0,
        MultilinearMap.map_update_add])
    (fun c v w => by
      rw [boolPair_eq_left (c • v) 0, boolPair_eq_left v 0, MultilinearMap.map_update_smul,
        RingHom.id_apply])
    (fun v w w' => by
      rw [boolPair_eq_right v (w + w') 0, boolPair_eq_right v w 0, boolPair_eq_right v w' 0,
        MultilinearMap.map_update_add])
    (fun c v w => by
      rw [boolPair_eq_right v (c • w) 0, boolPair_eq_right v w 0, MultilinearMap.map_update_smul,
        RingHom.id_apply])

def boolTensorEquiv : PiTensorProduct ℂ X ≃ₗ[ℂ] X false ⊗[ℂ] X true :=
  LinearEquiv.ofLinearMap (PiTensorProduct.lift boolMulti) (TensorProduct.lift boolBilin)
    (by
      refine TensorProduct.ext' fun v w => ?_
      simp [boolBilin, boolMulti, boolPair])
    (by
      refine PiTensorProduct.ext (MultilinearMap.ext fun x => ?_)
      simp only [boolBilin, boolMulti, LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
        PiTensorProduct.lift.tprod, MultilinearMap.mk'_apply, TensorProduct.lift.tmul,
        LinearMap.mk₂_apply, LinearMap.id_apply]
      apply (PiTensorProduct.tprod ℂ).congr_arg
      funext i
      cases i <;> rfl)

theorem boolTensorEquiv_tprod (x : ∀ i, X i) :
    boolTensorEquiv (PiTensorProduct.tprod ℂ x) = x false ⊗ₜ[ℂ] x true := by
  simp [boolTensorEquiv, boolMulti]

end Bool

def piTensorTwoEquiv {R a b V W : Type} [CommRing R] [Fintype a] [DecidableEq a] [Fintype b]
    [DecidableEq b] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (π₁ : Representation ℂ (GL a R) V) (π₂ : Representation ℂ (GL b R) W) :
    (piTensor (twoRep π₁ π₂)).Equiv
      ((extTensor π₁ π₂).comp (leviTwo R a b).symm.toMonoidHom) :=
  .mk (boolTensorEquiv (X := Two V W)) fun g => by
    refine PiTensorProduct.ext (MultilinearMap.ext fun x => ?_)
    show boolTensorEquiv (X := Two V W) (piTensor (twoRep π₁ π₂) g (PiTensorProduct.tprod ℂ x)) =
      extTensor π₁ π₂ ((leviTwo R a b).symm g) (boolTensorEquiv (X := Two V W) (PiTensorProduct.tprod ℂ x))
    rw [piTensor_tprod, boolTensorEquiv_tprod, boolTensorEquiv_tprod]
    exact (extTensor_tmul π₁ π₂ ((leviTwo R a b).symm g) (x false) (x true)).symm

theorem prod₂_equiv_multiProd (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (r t : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (W : Type)
    [AddCommGroup W] [Module ℂ W] (π₁ : Representation ℂ (GL (Fin r) k) V)
    (π₂ : Representation ℂ (GL (Fin t) k) W) :
    Nonempty ((prod₂ π₁ π₂).Equiv (multiProd (two (stdSum (rfl : r + t = r + t))) (twoRep π₁ π₂))) :=
  ⟨(LocGL.parIndEquiv (two (stdSum (rfl : r + t = r + t))) (piTensorTwoEquiv π₁ π₂)).symm⟩

end GlobalTheory.SmGL.Exponents
end
end

section

open GlobalTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SmGL.Exponents ValuativeRel

theorem _root_.GlobalTheory.T.jordanHolderMultiplicity_jacquet_eq_borelJacquet_of_small : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (β n : Type) [Fintype β] [LinearOrder β] [Fintype n] [DecidableEq n] [LinearOrder n] (c : β → Type) [∀ j, Fintype (c j)] [∀ j, DecidableEq (c j)] (f : (Σ j, c j) ≃ n), StrictMono (blk f) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL n k) V) (χ : β → kˣ →* ℂˣ), jhMult (ofChar (leviChar c χ)) (jac f π) = jhMult (ofChar (torusChar fun i => χ (blk f i))) (jacB π) := by
  first | exact @GlobalTheory.SmGL.EmptyBlocks.jhMult_jac_eq_jacB | exact GlobalTheory.SmGL.EmptyBlocks.jhMult_jac_eq_jacB | (intros; apply GlobalTheory.SmGL.EmptyBlocks.jhMult_jac_eq_jacB <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta MeasureTheory NumberField
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CuspLocApprox

theorem integral_eq_zero_of_forall_approx {X : Type} [MeasurableSpace X] {μ : Measure X} {v : X → ℂ} {w : X → ℝ}
    (hw : Integrable w μ)
    (h : ∀ ε : ℝ, 0 < ε → ∃ u : X → ℂ, Integrable u μ ∧ ∫ x, u x ∂μ = 0 ∧ ∀ x, ‖u x - v x‖ ≤ ε * w x) :
    ∫ x, v x ∂μ = 0 := by
  by_cases hv : Integrable v μ
  swap
  · exact integral_undef hv
  have key : ∀ ε : ℝ, 0 < ε → ‖∫ x, v x ∂μ‖ ≤ ε * ∫ x, w x ∂μ := fun ε hε => by
    obtain ⟨u, hu, h0, hn⟩ := h ε hε
    have e : ∫ x, (u x - v x) ∂μ = -∫ x, v x ∂μ := by rw [integral_sub hu hv, h0, zero_sub]
    rw [← norm_neg, ← e, ← integral_const_mul]
    exact norm_integral_le_of_norm_le (hw.const_mul ε) (Filter.Eventually.of_forall hn)
  have t : Filter.Tendsto (fun ε : ℝ => ε * ∫ x, w x ∂μ) (nhdsWithin 0 (Set.Ioi 0)) (nhds (0 * ∫ x, w x ∂μ)) :=
    ((continuous_id.mul continuous_const).tendsto 0).mono_left nhdsWithin_le_nhds
  rw [zero_mul] at t
  exact norm_le_zero_iff.1 (ge_of_tendsto t (eventually_nhdsWithin_of_forall key))

variable {D : D7} {V : HSp D}

def LocApprox (V : HSp D) (f : GA D V → ℂ) : Prop :=
  ∀ C : Set (GA D V), IsCompact C → ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (ψ : Fin n → GA D V → ℂ),
    (∀ l, Continuous (ψ l) ∧ (∀ γ ∈ GQ V, ∀ g, ψ l (γ * g) = ψ l g) ∧ IsCuspFun V (ψ l)) ∧
    ∀ x ∈ C, ‖f x - ∑ l, ψ l x‖ < ε

theorem leftInv_of_locApprox {f : GA D V → ℂ} (h : LocApprox V f) : ∀ γ ∈ GQ V, ∀ g, f (γ * g) = f g := by
  intro γ hγ g
  refine eq_of_forall_dist_le fun ε hε => ?_
  obtain ⟨n, ψ, hψ, happ⟩ := h {γ * g, g} (Set.toFinite _).isCompact (ε / 2) (by positivity)
  have e : ∑ l, ψ l (γ * g) = ∑ l, ψ l g := Finset.sum_congr rfl fun l _ => (hψ l).2.1 γ hγ g
  have h1 := happ (γ * g) (by simp)
  have h2 := happ g (by simp)
  rw [dist_eq_norm]
  have e' : f (γ * g) - f g = (f (γ * g) - ∑ l, ψ l (γ * g)) - (f g - ∑ l, ψ l g) := by rw [e]; ring
  rw [e']
  linarith [norm_sub_le (f (γ * g) - ∑ l, ψ l (γ * g)) (f g - ∑ l, ψ l g)]

theorem isCuspFun_of_locApprox {f : GA D V → ℂ} (h : LocApprox V f) : IsCuspFun V f := by
  have hl := leftInv_of_locApprox h
  rw [GlobalTheory.AutFunCompare.GQ_eq] at hl
  rw [GlobalTheory.AutFunCompare.isCuspFun_iff_constTerm]
  intro W hW μ hμ 𝓕 h𝓕 g
  have hint : ∀ φ : GA D V → ℂ, Continuous φ → (∀ γ ∈ GQ V, ∀ x, φ (γ * x) = φ x) →
      IntegrableOn (fun n : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.unipRad D.sp.cm V (AF D.host.F) W => φ (n.1 * g)) 𝓕 μ := by
    intro φ hc hl'
    rw [GlobalTheory.AutFunCompare.GQ_eq] at hl'
    exact GlobalTheory.AutFunCompare.integrableOn_constTerm D.sp.cm V W hW φ hc hl' μ hμ 𝓕 h𝓕 g
  obtain ⟨K, hK, hKs⟩ := GlobalTheory.AutFunCompare.unipRad_cocompact D.sp.cm V W hW
  have : IsModuleTopology (AF D.host.F) (AF D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
  have : IsTopologicalRing (AF D.host.F ⊗[D.host.F] D.host.E) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
  have : IsTopologicalGroup (GA D V) := inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig V.gram))
  have hcont : Continuous fun n : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.unipRad D.sp.cm V (AF D.host.F) W => (n : GA D V) * g :=
    continuous_subtype_val.mul continuous_const
  have hw : Integrable (fun _ : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.unipRad D.sp.cm V (AF D.host.F) W => (1 : ℝ)) (μ.restrict 𝓕) := by
    simpa using (hint (fun _ => (1 : ℂ)) continuous_const fun _ _ _ => rfl).norm
  refine integral_eq_zero_of_forall_approx (μ := μ.restrict 𝓕) (v := fun n => f (n.1 * g)) hw fun ε hε => ?_
  obtain ⟨m, ψ, hψ, happ⟩ := h _ (hK.image hcont) ε hε
  refine ⟨fun n => ∑ l, ψ l (n.1 * g), integrable_finsetSum _ fun l _ => hint _ (hψ l).1 (hψ l).2.1, ?_,
    fun n => ?_⟩
  · rw [integral_finsetSum _ fun l _ => hint _ (hψ l).1 (hψ l).2.1]
    exact Finset.sum_eq_zero fun l _ =>
      (GlobalTheory.AutFunCompare.isCuspFun_iff_constTerm V _).1 (hψ l).2.2 W hW μ hμ 𝓕 h𝓕 g
  · obtain ⟨γ, hγ, hk⟩ := hKs n
    have e1 : f (n.1 * g) = f ((γ * n).1 * g) := by
      rw [Subgroup.coe_mul, mul_assoc]; exact (hl _ hγ _).symm
    have e2 : ∀ l, ψ l (n.1 * g) = ψ l ((γ * n).1 * g) := fun l => by
      have hl' := (hψ l).2.1
      rw [GlobalTheory.AutFunCompare.GQ_eq] at hl'
      rw [Subgroup.coe_mul, mul_assoc]; exact (hl' _ hγ _).symm
    show ‖∑ l, ψ l (n.1 * g) - f (n.1 * g)‖ ≤ ε * 1
    rw [e1, Finset.sum_congr rfl fun l _ => e2 l, mul_one, norm_sub_rev]
    exact (happ _ ⟨_, hk, rfl⟩).le

end GlobalTheory.CuspLocApprox

end
end

section

open Formalism.L2.Ker MvPolynomial

theorem _root_.GlobalTheory.T.thetaJetMap_weighted_table_scale : ∀ {ι : Type} [Fintype ι] {a b : ℕ} (u : ℂ) (c : ι → ℂ) (J : (DVar ι a b →₀ ℕ) → ℂ) (nn : ι → ℕ) (P : Formalism.L2.DIV.Pol ℂ ι a), jetMap (fun m => u * ((m.prod fun k e => c k.1 ^ e) * J m)) nn P = u • Formalism.GradedWeylDivisibility.blockAct ℂ (fun τ => Matrix.diagonal fun _ : Fin b => c τ) (jetMap J nn P) := by
  first | exact @GlobalTheory.JetScale.jetMap_weight_scale | exact GlobalTheory.JetScale.jetMap_weight_scale | (intros; apply GlobalTheory.JetScale.jetMap_weight_scale <;> assumption)
end

section

open Formalism.L2.Ker MvPolynomial

theorem _root_.GlobalTheory.T.jetOperator_bideterminantBasis_repr_isAlgebraic : ∀ {ι : Type} [Fintype ι] {a b : ℕ} (lam : ι → Formalism.BasicNotions.DomWeight a) (lam' : ι → Formalism.BasicNotions.DomWeight b) (J : (DVar ι a b →₀ ℕ) → ℂ) (nn : ι → ℕ), (∀ m, IsAlgebraic ℚ (J m)) → JetInVV ℂ lam lam' nn → ∀ (i : Formalism.L2.DIV.VVIdx lam') (j : Formalism.L2.DIV.VVIdx lam), IsAlgebraic ℚ ((Formalism.L2.DIV.bVV ℂ lam').repr (jetOp lam lam' J nn (Formalism.L2.DIV.bVV ℂ lam j)) i) := by
  first | exact @GlobalTheory.JetAlg.repr_jetOp_isAlgebraic | exact GlobalTheory.JetAlg.repr_jetOp_isAlgebraic | (intros; apply GlobalTheory.JetAlg.repr_jetOp_isAlgebraic <;> assumption)
end
