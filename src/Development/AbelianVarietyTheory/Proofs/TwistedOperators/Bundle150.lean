module

public import Formalism.LocalToGlobal.IndefiniteReal.Bundle013
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle139
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RepresentationTheory.Intertwining
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle030
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.FiniteIntertwining
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle004
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle001
public import Formalism.RealPlaceAnalysis.Bundle002
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StepLaw

variable {D : D7}

def TameOn (χ : (AE D)ˣ →* Circle) (e : AE D) (P : Finset (Pl D.host.E))
    (c : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) : Prop :=
  ∀ x : (AE D)ˣ, infPart D (x : AE D) = 1 → ∀ hx : toEAf D (x : AE D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E,
    toEAf D ((x⁻¹ : (AE D)ˣ) : AE D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E → cA D e * (x : AE D) = cA D e →
    ∀ u : ∀ PP : Pl D.host.E, (kP PP)ˣ, (∀ PP ∈ P, (u PP : kP PP) = resS D.host.F PP ⟨toEAf D (x : AE D), hx⟩) →
      ((χ x : Circle) : ℂ) = ∏ PP ∈ P, ((c PP (u PP) : ℂˣ) : ℂ)

def vacScal {S T : HSp D} (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (P : Finset (Pl D.host.E))
    (cS cT : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (g : GA D S) (h : GA D T) : ℂ :=
  ∏ PP ∈ P, (((cT PP (Matrix.GeneralLinearGroup.det (redFn βS PP (finE S g))) : ℂˣ) : ℂ)⁻¹ *
    ((cS PP (Matrix.GeneralLinearGroup.det (redFn βT PP (finE T h))) : ℂˣ) : ℂ))


open Classical in
def resChr {T0 : Type} (L : LevCh D T0) (t : T0) (n : ℕ) (PP : Pl D.host.E) : (kP PP)ˣ →* ℂˣ :=
  if PP ∈ L.Pg then (L.chi n PP)⁻¹ else L.xiR t PP

end GlobalTheory.StepLaw

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.Cx

namespace GlobalTheory.Proof.RealFockActionTwistedOperators

theorem thetaKO_rat_mul {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hom : IsWeilDatumO ψ S T χS χT om) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) {γ : GA D S} (hγ : γ ∈ GQ S) (h : GA D S) (g : GA D T) :
    thetaKO om (γ * h) g f = thetaKO om h g f := by
  unfold thetaKO
  have hp : ((γ * h, g) : GA D S × GA D T) = (γ, 1) * (h, g) := by simp
  rw [hp, map_mul, mul_apply_eq_comp]
  exact hom.om_aut γ hγ 1 (one_mem _) _ (hom.om_pres _ _ hf)

theorem thetaKO_mul_right {D : D7} {S T : HSp D} (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))
    (f : WO S T → ℂ) (h u : GA D S) (g : GA D T) :
    thetaKO om (h * u) g f = thetaKO om h g (om (u, 1) f) := by
  unfold thetaKO
  have hp : ((h * u, g) : GA D S × GA D T) = (h, g) * (u, 1) := by simp
  rw [hp, map_mul, mul_apply_eq_comp]

theorem adForms_rat {G Γ W : Type} [Group G] [Group Γ] (ι : Γ →* G) [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    {ρ : Γ →* Module.End ℂ W} {J : Subgroup G} {χ : J →* ℂˣ} {f : G → W} (hf : f ∈ Bridge.AdForms ι ρ J χ)
    (γ : Γ) (h : G) : f (ι γ * h) = ρ γ (f h) := by
  have h1 : f (ι γ * h * ((1 : J) : G)) = (χ 1 : ℂ) • ρ γ (f h) := hf γ h 1
  simpa using h1

theorem form_rat {D : D7} {V : HSp D} (c : CoefA V) {J : Subgroup (Bridge.Gf V)} {χ : J →* ℂˣ}
    {f : Bridge.Gf V → c.W} (hf : f ∈ Bridge.AdForms (Bridge.ratF V) c.coef.ρ J χ) {γ : GA D V} (hγ : γ ∈ GQ V)
    (h : GA D V) : c.ext f (γ * h) = c.ρ (γ * h)⁻¹ (c.ρ γ (f ((finHom V).rangeRestrict h))) := by
  show c.ρ (γ * h)⁻¹ (f ((finHom V).rangeRestrict (γ * h))) = _
  congr 1
  have hr : (finHom V).rangeRestrict (γ * h) = Bridge.ratF V ⟨γ, hγ⟩ * (finHom V).rangeRestrict h := by
    apply Subtype.ext
    simp [Bridge.ratF]
  rw [hr, adForms_rat (Bridge.ratF V) hf ⟨γ, hγ⟩]
  rfl

theorem ext_mul_real {D : D7} {V : HSp D} (c : CoefA V) (f : Bridge.Gf V → c.W) {u : GA D V} (hu : u ∈ GinfC V)
    (h : GA D V) : c.ext f (h * u) = c.ρ (h * u)⁻¹ (f ((finHom V).rangeRestrict h)) := by
  have hu' : finHom V u = 1 := hu
  have hr : (finHom V).rangeRestrict (h * u) = (finHom V).rangeRestrict h := by
    apply Subtype.ext
    simp [hu']
  show c.ρ (h * u)⁻¹ (f ((finHom V).rangeRestrict (h * u))) = _
  rw [hr]

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) (t : T)

end GlobalTheory.Proof.RealFockActionTwistedOperators

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField

namespace GlobalTheory.Chain.VacVec

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

private theorem Jm_mul_Jm_eq_oneFormalDegree {n : ℕ} (ε : Fin n → Bool) : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
  unfold Formalism.REAL.Jm
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  by_cases h : ε a <;> simp [h]

private theorem conjTranspose_Jm_eq_Jm {n : ℕ} (ε : Fin n → Bool) :
    Matrix.conjTranspose (Formalism.REAL.Jm ε) = Formalism.REAL.Jm ε := by
  unfold Formalism.REAL.Jm
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext a
  by_cases h : ε a <;> simp [h]

private theorem conj_cartan_involution_props {n : ℕ} (F J : Matrix (Fin n) (Fin n) ℂ) (hF : IsUnit F) (hJ : J * J = 1)
    (hJh : Matrix.conjTranspose J = J) :
    F⁻¹ * J * F * (F⁻¹ * J * F) = 1 ∧
      Matrix.conjTranspose (F⁻¹ * J * F) * (Matrix.conjTranspose F * J * F) * (F⁻¹ * J * F) =
        Matrix.conjTranspose F * J * F ∧
      Matrix.conjTranspose F * J * F * (F⁻¹ * J * F) = Matrix.conjTranspose F * F := by
  have hd : IsUnit F.det := (Matrix.isUnit_iff_isUnit_det F).mp hF
  have hdh : IsUnit (Matrix.conjTranspose F).det := by rw [Matrix.det_conjTranspose]; exact hd.star
  have hJJ : ∀ X : Matrix (Fin n) (Fin n) ℂ, J * (J * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hJ, Matrix.one_mul]
  refine ⟨?_, ?_, ?_⟩
  · simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hd, hJJ]
    exact Matrix.nonsing_inv_mul F hd
  · simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv, hJh, Matrix.mul_assoc,
      Matrix.nonsing_inv_mul_cancel_left _ _ hdh, Matrix.mul_nonsing_inv_cancel_left _ _ hd, hJJ]
  · simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hd, hJJ]


open Matrix in
open scoped ComplexOrder in
theorem cart_isCartanInv {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) :
    IsCartanInv (gramAt D V τ) (cart M τ) := by
  unfold IsCartanInv cart
  rw [← M.fr_gram τ]
  obtain ⟨h1, h2, h3⟩ := conj_cartan_involution_props _ _ (M.fr_unit τ) (Jm_mul_Jm_eq_oneFormalDegree (M.ε τ)) (conjTranspose_Jm_eq_Jm (M.ε τ))
  refine ⟨h1, h2, ?_⟩
  rw [h3]
  have hinj : Function.Injective (M.fr τ).mulVec := Matrix.mulVec_injective_iff_isUnit.mpr (M.fr_unit τ)
  simpa only [Matrix.mul_one] using Matrix.PosDef.one.conjTranspose_mul_mul_same hinj

end GlobalTheory.Chain.VacVec

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FlagAction

theorem act_sum_smul {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank)
    (g : Formalism.L2.DIV.G0 L.Pg L.r) {ι : Type} (s : Finset ι) (c : ι → ℂ) (F : ι → GA D V → ℂ) :
    actG0 V β L g (∑ i ∈ s, c i • F i) = ∑ i ∈ s, c i • actG0 V β L g (F i) := by
  unfold actG0
  split_ifs with hk
  · funext h
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => mul_left_comm _ _ _
  · simp

theorem convIdempotent_act : ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) [Fintype (Formalism.L2.DIV.G0 L.Pg L.r)], LiftsExist V β L → ∀ c : Formalism.L2.DIV.G0 L.Pg L.r → ℂ, (∀ g, ∑ a, c a * c (a⁻¹ * g) = c g) → ∀ F : GA D V → ℂ, HasType V β (flag1L L) F → (∑ g, c g • actG0 V β L g (∑ g', c g' • actG0 V β L g' F)) = ∑ g, c g • actG0 V β L g F := by
  intro D V β L _ hL c hc F hF
  have hA := levelGroupAction_isAction V β L hL F hF
  calc (∑ g, c g • actG0 V β L g (∑ g', c g' • actG0 V β L g' F))
      = ∑ g, ∑ g', (c g * c g') • actG0 V β L (g * g') F := by
        refine Finset.sum_congr rfl fun g _ => ?_
        rw [act_sum_smul, Finset.smul_sum]
        refine Finset.sum_congr rfl fun g' _ => ?_
        rw [hA.2 g g', smul_smul]
    _ = ∑ g, ∑ k, (c g * c (g⁻¹ * k)) • actG0 V β L k F := by
        refine Finset.sum_congr rfl fun g _ => ?_
        exact Fintype.sum_equiv (Equiv.mulLeft g) _ _ fun g' => by
          simp only [Equiv.coe_mulLeft, inv_mul_cancel_left]
    _ = ∑ k, (∑ g, c g * c (g⁻¹ * k)) • actG0 V β L k F := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun k _ => Finset.sum_smul.symm
    _ = ∑ g, c g • actG0 V β L g F := by
        simp only [hc]

end GlobalTheory.FlagAction
end

section

open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility GlobalTheory.Branching GlobalTheory.GLDuality
open Formalism.REAL (fockF)
open scoped DirectSum TensorProduct Kronecker Matrix

namespace GlobalTheory

theorem tensor_eq_zero_of_forall_contract_right {V W : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (z : V ⊗[ℂ] W)
    (h : ∀ l : Module.Dual ℂ W, TensorProduct.rid ℂ V (LinearMap.lTensor V l z) = 0) : z = 0 := by
  classical
  let b := Module.Free.chooseBasis ℂ W
  apply (TensorProduct.equivFinsuppOfBasisRight (M := V) b).injective
  ext i
  simp [TensorProduct.equivFinsuppOfBasisRight_apply, h]

theorem outerTensor_intertwining_eq_zero_of_left :
    ∀ (G H V W V' W' : Type) [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [AddCommGroup V'] [Module ℂ V'] [AddCommGroup W'] [Module ℂ W'] (ρ : Representation ℂ G V) (σ : Representation ℂ H W) (ρ' : Representation ℂ G V') (σ' : Representation ℂ H W'), (∀ ψ : ρ.IntertwiningMap ρ', ψ = 0) → ∀ φ : (Representation.tprod (ρ.comp (MonoidHom.fst G H)) (σ.comp (MonoidHom.snd G H)) : Representation ℂ (G × H) (V ⊗[ℂ] W)).IntertwiningMap (Representation.tprod (ρ'.comp (MonoidHom.fst G H)) (σ'.comp (MonoidHom.snd G H)) : Representation ℂ (G × H) (V' ⊗[ℂ] W')), φ = 0 := by
  intro G H V W V' W' _ _ _ _ _ _ _ _ _ _ ρ σ ρ' σ' h φ

  have hpure : ∀ (v : V) (w : W), φ (v ⊗ₜ[ℂ] w) = 0 := by
    intro v w
    apply tensor_eq_zero_of_forall_contract_right
    intro l
    let f : V →ₗ[ℂ] V' :=
      (TensorProduct.rid ℂ V').toLinearMap ∘ₗ LinearMap.lTensor V' l ∘ₗ φ.toLinearMap ∘ₗ
        (TensorProduct.mk ℂ V W).flip w
    have hf : ∀ (g : G) (x : V), f (ρ g x) = ρ' g (f x) := by
      intro g x
      have key : ∀ y : V' ⊗[ℂ] W', TensorProduct.rid ℂ V'
          (LinearMap.lTensor V' l (TensorProduct.map (ρ' g) (σ' 1) y)) =
          ρ' g (TensorProduct.rid ℂ V' (LinearMap.lTensor V' l y)) := by
        intro y
        induction y using TensorProduct.induction_on with
        | zero => simp
        | tmul a c => simp
        | add a c ha hc => simp only [map_add (f := _), ha, hc]
      have e1 : ρ g x ⊗ₜ[ℂ] w = (Representation.tprod (ρ.comp (MonoidHom.fst G H))
          (σ.comp (MonoidHom.snd G H))) (g, 1) (x ⊗ₜ[ℂ] w) := by
        simp [Representation.tprod_apply]
      have e2 := Representation.IntertwiningMap.isIntertwining _ _ φ (g, 1) (x ⊗ₜ[ℂ] w)
      simp only [f, LinearMap.comp_apply, LinearMap.flip_apply, TensorProduct.mk_apply,
        Representation.IntertwiningMap.toLinearMap_apply, LinearEquiv.coe_coe]
      rw [e1, e2, Representation.tprod_apply]
      exact key _
    have h0 := h (f.intertwiningMap_of_isIntertwiningMap ρ ρ' hf)
    have hv := congrArg (fun ψ : ρ.IntertwiningMap ρ' => ψ v) h0
    simpa [f] using hv
  apply Representation.IntertwiningMap.ext
  apply TensorProduct.ext'
  intro v w
  simp [hpure]

end GlobalTheory
end
