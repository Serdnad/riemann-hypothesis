module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle199
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.EmbedsLevelZeroDepthZero
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle229
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
public import GroundTheory.LocalFields.LocalArtinMap
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle518
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle175
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle371
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IdemOfIsPrimeIdem
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle640
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle011
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle785
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle692
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle710
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle683
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle658
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle679
public import Formalism.LocalRingCardinality.Bundle004
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.Bundle004
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle413
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle786
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
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle017

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG

noncomputable section

namespace GlobalTheory.IndChain.SuppStep

open GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.LocGL
open scoped TensorProduct

variable {g : ℕ} [Fact g.Prime]

theorem isUnram_of_supp {ν : ℚ_[g]ˣ →* ℂˣ} (h : Supp.IsUnram ν) : GlobalTheory.SplitWeil.IsUnram ν := by
  intro x hx
  have a1 := GlobalTheory.SplitWeil.padic_valuation_lt_iff g (x : ℚ_[g]) 1
  have a2 := GlobalTheory.SplitWeil.padic_valuation_lt_iff g 1 (x : ℚ_[g])
  rw [hx, map_one] at a1 a2
  have h1 : ‖(x : ℚ_[g])‖ = 1 := by
    simp only [lt_self_iff_false, norm_one, false_iff, not_lt] at a1 a2
    exact le_antisymm a2 a1
  have := h (PadicInt.mkUnits h1)
  convert this using 2
  exact Units.ext rfl

theorem extTensor_twist_apply {a b : ℕ} {W W' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    (σ : Representation ℂ (GL (Fin a) ℚ_[g]) W) (ρ : Representation ℂ (GL (Fin b) ℚ_[g]) W')
    (χ₁ : GL (Fin a) ℚ_[g] →* ℂˣ) (χ₂ : GL (Fin b) ℚ_[g] →* ℂˣ) (x : GL (Fin a) ℚ_[g]) (y : GL (Fin b) ℚ_[g])
    (w : W ⊗[ℂ] W') :
    extTensor (_root_.GlobalTheory.SmGL.twist σ χ₁) (_root_.GlobalTheory.SmGL.twist ρ χ₂) (x, y) w = ((χ₁ x * χ₂ y : ℂˣ) : ℂ) • TensorProduct.map (σ x) (ρ y) w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add u v hu hv => rw [map_add (f := _), hu, hv, map_add (f := _), smul_add]
  | tmul u v =>
    rw [extTensor_tmul, TensorProduct.map_tmul, twist_apply, twist_apply, TensorProduct.smul_tmul_smul,
      Units.val_mul]

theorem scal_eq (ν₁ ν₂ A B : ℚ_[g]ˣ →* ℂˣ) (u v : ℚ_[g]ˣ) :
    (A u * B v) * ((ν₁ * A⁻¹) u * (ν₂ * B⁻¹) v) = ν₁ u * ν₂ v := by
  simp only [MonoidHom.mul_apply, MonoidHom.inv_apply]
  simp [mul_assoc, mul_comm, mul_left_comm]

theorem law {a b : ℕ} {V W W' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup W'] [Module ℂ W'] (π : Representation ℂ (GL (Fin (a + b)) ℚ_[g]) V)
    (σ : Representation ℂ (GL (Fin a) ℚ_[g]) W) (ρ : Representation ℂ (GL (Fin b) ℚ_[g]) W')
    (ν₁ ν₂ : ℚ_[g]ˣ →* ℂˣ) (Λ : V →ₗ[ℂ] W ⊗[ℂ] W')
    (hΛ : ∀ (p : GL (Fin (a + b)) ℚ_[g]) (x : GL (Fin a) ℚ_[g]) (y : GL (Fin b) ℚ_[g]),
      (∀ i j : Fin (a + b), (j : ℕ) < a → a ≤ (i : ℕ) → (p : Matrix (Fin (a + b)) (Fin (a + b)) ℚ_[g]) i j = 0) →
      (∀ i j : Fin a, (x : Matrix (Fin a) (Fin a) ℚ_[g]) i j =
        Formalism.MainNotions.ArithmeticCylinders.entN (p : Matrix (Fin (a + b)) (Fin (a + b)) ℚ_[g]) i j) →
      (∀ i j : Fin b, (y : Matrix (Fin b) (Fin b) ℚ_[g]) i j =
        Formalism.MainNotions.ArithmeticCylinders.entN (p : Matrix (Fin (a + b)) (Fin (a + b)) ℚ_[g]) (a + i) (a + j)) →
      ∀ v, Λ (π p v) = ((ν₁ (Matrix.GeneralLinearGroup.det x) * ν₂ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ) •
        TensorProduct.map (σ x) (ρ y) (Λ v))
    (q : parab ℚ_[g] (two (stdSum (rfl : a + b = a + b)))) (w : V) :
    Λ (π q w) = (deltaHalf ℚ_[g] (Two (Fin a) (Fin b)) (leviProj ℚ_[g] _ q) : ℂ) •
      extTensor (_root_.GlobalTheory.SmGL.twist σ (detChar (Fin a) (ν₁ * (absPow ℚ_[g] ((b : ℂ) / 2))⁻¹)))
        (_root_.GlobalTheory.SmGL.twist ρ (detChar (Fin b) (ν₂ * (absPow ℚ_[g] (-(a : ℂ) / 2))⁻¹)))
        ((leviTwo ℚ_[g] (Fin a) (Fin b)).symm (leviProj ℚ_[g] _ q)) (Λ w) := by
  set X := ((leviTwo ℚ_[g] (Fin a) (Fin b)).symm (leviProj ℚ_[g] _ q)).1 with hX
  set Y := ((leviTwo ℚ_[g] (Fin a) (Fin b)).symm (leviProj ℚ_[g] _ q)).2 with hY
  have hL : leviProj ℚ_[g] _ q = leviTwo ℚ_[g] _ _ (X, Y) := (MulEquiv.apply_symm_apply _ _).symm
  have hpar := (mem_parab_two ℚ_[g]).1 q.2
  have h0 : ∀ i j : Fin (a + b), (j : ℕ) < a → a ≤ (i : ℕ) →
      ((q : GL (Fin (a + b)) ℚ_[g]) : Matrix (Fin (a + b)) (Fin (a + b)) ℚ_[g]) i j = 0 := by
    intro i j hj hi
    have e1 : stdSum (rfl : a + b = a + b) (.inr ⟨i - a, by omega⟩) = i := Fin.ext (by rw [stdSum_inr]; simp; omega)
    have e2 : stdSum (rfl : a + b = a + b) (.inl ⟨j, hj⟩) = j := Fin.ext (by rw [stdSum_inl])
    have := hpar ⟨i - a, by omega⟩ ⟨j, hj⟩
    rwa [e1, e2] at this
  have hx : ∀ i j : Fin a, (X : Matrix (Fin a) (Fin a) ℚ_[g]) i j =
      Formalism.MainNotions.ArithmeticCylinders.entN ((q : GL (Fin (a + b)) ℚ_[g]) : Matrix (Fin (a + b)) (Fin (a + b)) ℚ_[g]) i j := by
    intro i j
    have hi := i.2
    have hj := j.2
    rw [Formalism.MainNotions.ArithmeticCylinders.entN, dite_eq_left ⟨by omega, by omega⟩]
    show ((q : GL (Fin (a + b)) ℚ_[g]) : Matrix (Fin (a + b)) (Fin (a + b)) ℚ_[g]) (stdSum (rfl : a + b = a + b) (.inl i)) (stdSum (rfl : a + b = a + b) (.inl j)) = _
    congr 1 <;> exact Fin.ext (stdSum_inl _ _)
  have hy : ∀ i j : Fin b, (Y : Matrix (Fin b) (Fin b) ℚ_[g]) i j =
      Formalism.MainNotions.ArithmeticCylinders.entN ((q : GL (Fin (a + b)) ℚ_[g]) : Matrix (Fin (a + b)) (Fin (a + b)) ℚ_[g]) (a + i) (a + j) := by
    intro i j
    have hi := i.2
    have hj := j.2
    rw [Formalism.MainNotions.ArithmeticCylinders.entN, dite_eq_left ⟨by omega, by omega⟩]
    show ((q : GL (Fin (a + b)) ℚ_[g]) : Matrix (Fin (a + b)) (Fin (a + b)) ℚ_[g]) (stdSum (rfl : a + b = a + b) (.inr i)) (stdSum (rfl : a + b = a + b) (.inr j)) = _
    congr 1 <;> exact Fin.ext (stdSum_inr _ _)
  rw [hΛ q X Y h0 hx hy w, hL, MulEquiv.symm_apply_apply, deltaHalf_two, extTensor_twist_apply, smul_smul,
    ← Units.val_mul, detChar_apply, detChar_apply]
  simp only [Fintype.card_fin]
  rw [scal_eq]

theorem supp_of_mapsToProd : GlobalTheory.Published.ZelevinskyPolynomialRing → ∀ (g : ℕ) [Fact g.Prime] (n a b : ℕ) (V W W' : Type)
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    (π : Representation ℂ (GL (Fin n) ℚ_[g]) V) (σ : Representation ℂ (GL (Fin a) ℚ_[g]) W)
    (ρ : Representation ℂ (GL (Fin b) ℚ_[g]) W'),
    GlobalTheory.PRep.IsSmooth π → π.IsIrreducible → Supp.MapsToProd π σ ρ →
    ∀ (ys yr : Multiset (GlobalTheory.LocGL.IrrGL (k := ℚ_[g]))), GlobalTheory.LocGL.HasSupport σ ys → GlobalTheory.LocGL.HasSupport ρ yr →
    ∃ (μ₁ μ₂ : ℚ_[g]ˣ →* ℂˣ) (h₁ : GlobalTheory.SplitWeil.IsUnram μ₁) (h₂ : GlobalTheory.SplitWeil.IsUnram μ₂),
      GlobalTheory.LocGL.HasSupport π (ys.map (fun x => x.tw μ₁ (GlobalTheory.SmGL.isSmoothChar_of_isUnram h₁)) +
        yr.map (fun x => x.tw μ₂ (GlobalTheory.SmGL.isSmoothChar_of_isUnram h₂))) := by
  intro hZ g _ n a b V W W' _ _ _ _ _ _ π σ ρ hs hπ hM ys yr hys hyr
  obtain ⟨Z, Ψ, -, hΨ, -⟩ := hZ ℚ_[g]
  obtain ⟨hn, ν₁, ν₂, Λ, h₁, h₂, hΛ0, hΛ⟩ := hM
  subst hn
  have hμ₁ : GlobalTheory.SplitWeil.IsUnram (ν₁ * (absPow ℚ_[g] ((b : ℂ) / 2))⁻¹) :=
    isUnram_mul (isUnram_of_supp h₁) (isUnram_inv (isUnram_absPow _ _))
  have hμ₂ : GlobalTheory.SplitWeil.IsUnram (ν₂ * (absPow ℚ_[g] (-(a : ℂ) / 2))⁻¹) :=
    isUnram_mul (isUnram_of_supp h₂) (isUnram_inv (isUnram_absPow _ _))
  refine ⟨_, _, hμ₁, hμ₂, ?_⟩
  let T : π.IntertwiningMap (prod₂ (_root_.GlobalTheory.SmGL.twist σ (detChar (Fin a) (ν₁ * (absPow ℚ_[g] ((b : ℂ) / 2))⁻¹)))
      (_root_.GlobalTheory.SmGL.twist ρ (detChar (Fin b) (ν₂ * (absPow ℚ_[g] (-(a : ℂ) / 2))⁻¹)))) :=
    { toFun := fun v => ⟨⟨fun x => Λ (π x v), fun q x => by
          show Λ (π (q * x) v) = _
          rw [map_mul, Module.End.mul_apply]
          exact law π σ ρ ν₁ ν₂ Λ hΛ q (π x v)⟩,
        mem_smoothPart_of_nhds (Filter.mem_of_superset ((hs v).mem_nhds (by simp)) fun h hh => by
          have hh' : π h v = v := hh
          refine Subtype.ext (funext fun x => ?_)
          show Λ (π (x * h) v) = Λ (π x v)
          rw [map_mul, Module.End.mul_apply, hh'])⟩
      map_add' := fun v w => Subtype.ext (Subtype.ext (funext fun x => by
        show Λ (π x (v + w)) = Λ (π x v) + Λ (π x w)
        rw [map_add (f := _), map_add (f := _)]))
      map_smul' := fun c v => Subtype.ext (Subtype.ext (funext fun x => by
        show Λ (π x (c • v)) = c • Λ (π x v)
        rw [map_smul, map_smul]))
      isIntertwining' := fun h => LinearMap.ext fun v => Subtype.ext (Subtype.ext (funext fun x => by
        show Λ (π x (π h v)) = Λ (π (x * h) v)
        rw [map_mul, Module.End.mul_apply])) }
  have hT : Function.Injective T := by
    haveI := hπ
    refine (Representation.IsIrreducible.injective_or_eq_zero T).resolve_right fun h0 => hΛ0 (LinearMap.ext fun v => ?_)
    have h1 : (T v).1.1 1 = 0 := by rw [h0]; rfl
    change Λ (π 1 v) = 0 at h1
    simpa using h1
  have hσ' := hys.tw _ (isSmoothChar_of_isUnram hμ₁)
  have hρ' := hyr.tw _ (isSmoothChar_of_isUnram hμ₂)
  obtain ⟨φ⟩ := nonempty_prod₂_equiv_prodIrr _ hσ'.isSmooth hσ'.isIrreducible _ hρ'.isSmooth hρ'.isIrreducible
    (Fin.sum_univ_two _)
  have hsub := (IsSubquotient.of_injective T hT).trans (.of_injective φ.toIntertwiningMap φ.toLinearEquiv.injective)
  have key := SupportRing.hasSupport_of_isSubquotient_prodIrr hΨ
    (t := ![_, _]) (Fin.forall_fin_two.2 ⟨hσ'.of_equiv (IrrGL.equivOf _ _ _), hρ'.of_equiv (IrrGL.equivOf _ _ _)⟩)
    hπ hsub
  rw [Fin.sum_univ_two] at key
  exact key

end GlobalTheory.IndChain.SuppStep
end
end

section

open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict GroundTheory.LocalField GroundTheory.LocalField.FormalGroup
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ArtinCompareApply

theorem lift_localArtinMap_apply : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w)
    (a : Weil h →* (w.adicCompletion E)ˣ), IsLocalArtin h a → ∀ (ι : Ω →ₐ[E] Kbar w), IsLocEmb A w ι →
    ∀ (σ : Weil h) (τ : GalLoc w), Lifts ι τ (σ : G E Ω) →
    ∀ (z : Kbar w) (hz : z ∈ maximalAbelianExtension (w.adicCompletion E) (Kbar w)),
      τ ((localArtinMap (w.adicCompletion E) (Kbar w) (a σ) ⟨z, hz⟩ : maximalAbelianExtension (w.adicCompletion E) (Kbar w)) : Kbar w) = z := by
  intro E Ω _ _ _ _ _ A w h a ha ι hι σ τ hτ z hz
  have H := GlobalTheory.ArtinCompare.restrict_eq_inv_localArtinMap E Ω A w h ι hι a ha σ τ hτ
  set M := maximalAbelianExtension (w.adicCompletion E) (Kbar w)
  set g := localArtinMap (w.adicCompletion E) (Kbar w) (a σ)
  have e : AlgEquiv.restrictNormalHom M τ (g ⟨z, hz⟩) = ⟨z, hz⟩ := by
    rw [H, ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
  have e2 := congrArg (fun y : M => (y : Kbar w)) e
  simp only [AlgEquiv.restrictNormalHom_apply] at e2
  exact e2

end GlobalTheory.ArtinCompareApply
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.RawLift

theorem schur_trPair_real_fin : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → ∀ i, LevProd R i → ∀ (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (x y : (R.HW i (sg0 D A)).H), ∀ u ∈ GinfC (Wc D i), ∀ γ ∈ GfC (Wc D i), dimProd A i * ∫ z in R.fdW i, star (val R i v x z) * val R i v y (z * (u * γ)) ∂(R.νW i) = trPair R i γ x y * ∏ ρ, ⟪((v ρ : (R.MW i (sg0 D A)).sm ρ) : (R.MW i (sg0 D A)).H ρ), (R.MW i (sg0 D A)).rep ρ (infMat D.sp.cm.sig (Wc D i).gram (R.θ ρ) u) ((v ρ : (R.MW i (sg0 D A)).sm ρ) : (R.MW i (sg0 D A)).H ρ)⟫_ℂ := by
  intro hP D G _ _ Pl0 T A Ks _ _ _ R F hL i hLP v x y u hu γ hγ
  have hθ : IsInfFam R.θ := hL.models.inf
  obtain ⟨-, hr, -⟩ := hL.models.HW i (sg0 D A)
  have hHaar : (R.νW i).IsHaarMeasure := (hL.models.νW i).1.1
  have hfd : IsFundamentalDomain (GQ (Wc D i)) (R.fdW i) (R.νW i) := (hL.models.νW i).2
  have hTm : IsMultMap R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i R.triv))
      (levChi _ (R.βW i) (R.datWp i R.triv)) ((R.HW i (sg0 D A)).e x) :=
    (GlobalTheory.MultMem.mem_mult_iff ..).1 (by
      have : (R.HW i (sg0 D A)).e x ∈ R.Wall i (sg0 D A) := hr ▸ LinearMap.mem_range_self _ x
      exact this)
  have hTm' : IsMultMap R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i R.triv))
      (levChi _ (R.βW i) (R.datWp i R.triv)) ((R.HW i (sg0 D A)).e y) :=
    (GlobalTheory.MultMem.mem_mult_iff ..).1 (by
      have : (R.HW i (sg0 D A)).e y ∈ R.Wall i (sg0 D A) := hr ▸ LinearMap.mem_range_self _ y
      exact this)
  set J' : Set (GA D (Wc D i)) := {k | k ∈ levW R i ∧ γ⁻¹ * k * γ ∈ levW R i} with hJ'
  have hT1 : IsMultMap R.θ (R.MW i (sg0 D A)) J' (fun _ => 1) ((R.HW i (sg0 D A)).e x) :=
    ⟨hTm.aut, hTm.cusp, fun w k hk g => by rw [hTm.lev w k hk.1 g, hLP.2.1 k hk.1], hTm.equiv, hTm.cont⟩
  have hT2 : IsMultMap R.θ (R.MW i (sg0 D A)) J' (fun _ => 1)
      (heckeOn (R.MW i (sg0 D A)) {γ} ((R.HW i (sg0 D A)).e y)) := by
    have hT3 : IsMultMap R.θ (R.MW i (sg0 D A)) J' (fun _ => 1) ((R.HW i (sg0 D A)).e y) :=
      ⟨hTm'.aut, hTm'.cusp, fun w k hk g => by rw [hTm'.lev w k hk.1 g, hLP.2.1 k hk.1], hTm'.equiv, hTm'.cont⟩
    refine GlobalTheory.SphericalOps.isMultMap_heckeOn hT3 (fun k hk => ?_) (fun w k hk g => ?_)
    · rw [Finset.mem_singleton] at hk
      exact hk ▸ hγ
    · simp only [heckeLin_apply, Finset.sum_singleton, one_mul]
      have e : g * k * γ = g * γ * (γ⁻¹ * k * γ) := by group
      rw [e, hTm'.lev w _ hk.2 (g * γ), hLP.2.1 _ hk.2, one_mul]
  obtain ⟨c, hc⟩ := GlobalTheory.MultFinite.schurMult (θ := R.θ) (M := R.MW i (sg0 D A)) (J := J') (χ := fun _ => 1) hP
    (R.νW i) (R.fdW i) hθ hHaar hfd _ ((GlobalTheory.MultMem.mem_mult_iff ..).2 hT1) _ ((GlobalTheory.MultMem.mem_mult_iff ..).2 hT2)
  have hip := ipM_spec _ _ _ _ _ ⟨c, hc⟩
  obtain ⟨v', hv', hmove⟩ := GlobalTheory.RealPointMove.translate_eq_move D R.θ hθ (Wc D i) _ (R.MW i (sg0 D A)) J' (fun _ => 1) _ hT2
    u hu (fun ρ => (v ρ : (R.MW i (sg0 D A)).sm ρ))
  have htr : trPair R i γ x y = dimProd A i * ipM (R.MW i (sg0 D A)) (R.νW i) (R.fdW i) ((R.HW i (sg0 D A)).e x)
      (heckeOn (R.MW i (sg0 D A)) {γ} ((R.HW i (sg0 D A)).e y)) := rfl
  have hint : ∀ z, star (val R i v x z) * val R i v y (z * (u * γ)) =
      star ((R.HW i (sg0 D A)).e x (fun ρ => (v ρ : (R.MW i (sg0 D A)).sm ρ)) z) *
        heckeOn (R.MW i (sg0 D A)) {γ} ((R.HW i (sg0 D A)).e y) v' z := fun z => by
    rw [← hmove z]
    simp [val, heckeOn, postOn_apply, heckeLin_apply, mul_assoc]
  simp_rw [hint]
  rw [(hip (fun ρ => (v ρ : (R.MW i (sg0 D A)).sm ρ)) v').2, htr, mul_assoc]
  congr 2
  refine Finset.prod_congr rfl fun ρ _ => ?_
  rw [hv' ρ]

end GlobalTheory.RawLift

end
end

section

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem GlobalTheory.BKGal.JumpDR.BasisGlue.exists_basis {R W : Type} [CommRing R] [AddCommGroup W] (act : R →+ (W →+ W))
    (hmul : ∀ (r s : R) (w : W), act (r * s) w = act r (act s w)) (hone : ∀ w : W, act 1 w = w) (eD : R)
    (hbij : Function.Bijective (act eD)) (F : ℤ → W → Prop) (hshift : ∀ (y : W) (j : ℤ), F j y ↔ F (j + 1) (act eD y))
    {ι : Type} [Fintype ι] [DecidableEq ι] (β β₀ : ℕ) (g h b : ι → W) (hg : ∀ i, act (eD ^ β₀) (g i) = h i)
    (hspan : ∀ w, F ((β₀ + β : ℕ) : ℤ) w ↔ ∃ d : ι → R, w = ∑ i, act (d i) (h i))
    (hb0 : ∀ v, F 0 v ↔ ∃ d : ι → R, v = ∑ k, act (d k) (b k))
    (hbi : ∀ d : ι → R, ∑ k, act (d k) (b k) = 0 → ∀ k, d k = 0) :
    ∃ f : ι → W, (∀ i, act (eD ^ β) (f i) = g i) ∧ (∀ v, F 0 v ↔ ∃ d : ι → R, v = ∑ i, act (d i) (f i)) ∧
      ∀ d : ι → R, ∑ i, act (d i) (f i) = 0 → ∀ i, d i = 0 := by
  have hcomm : ∀ (d d' : R) (w : W), act d (act d' w) = act d' (act d w) := by
    intro d d' w
    rw [← hmul, ← hmul, mul_comm]
  have hpow : ∀ (n : ℕ) (w : W), act (eD ^ n) w = (act eD)^[n] w := by
    intro n
    induction n with
    | zero => intro w; rw [pow_zero, hone]; rfl
    | succ n ih => intro w; rw [pow_succ', hmul, ih, Function.iterate_succ_apply']
  have hinj : ∀ n : ℕ, Function.Injective (act (eD ^ n)) := by
    intro n x x' hxx
    rw [hpow, hpow] at hxx
    exact (hbij.1.iterate n) hxx
  have hsh : ∀ (n : ℕ) (w : W) (j : ℤ), F j w ↔ F (j + n) (act (eD ^ n) w) := by
    intro n
    induction n with
    | zero => intro w j; rw [pow_zero, hone, Nat.cast_zero, add_zero]
    | succ n ih =>
      intro w j
      rw [ih w j, hshift (act (eD ^ n) w) (j + n), pow_succ', hmul, Nat.cast_succ, ← add_assoc]
  have hsingle : ∀ (v : ι → W) (i : ι), ∑ k, act ((Pi.single i (1 : R) : ι → R) k) (v k) = v i := by
    intro v i
    rw [Finset.sum_eq_single i (fun k _ hk => by rw [Pi.single_eq_of_ne hk, map_zero, AddMonoidHom.zero_apply])
      (fun h => (h (Finset.mem_univ i)).elim), Pi.single_eq_same, hone]
  let ginv : W → W := (Equiv.ofBijective _ hbij).symm
  have hginv : ∀ x, act eD (ginv x) = x := fun x => (Equiv.ofBijective _ hbij).apply_symm_apply x
  have h1 : ∀ i, act (eD ^ β) (ginv^[β] (g i)) = g i := by
    intro i
    rw [hpow]
    exact Function.RightInverse.iterate hginv β _
  have h2 : ∀ v, F 0 v ↔ ∃ d : ι → R, v = ∑ i, act (d i) (ginv^[β] (g i)) := by
    have hf : ∀ i, act (eD ^ (β₀ + β)) (ginv^[β] (g i)) = h i := by
      intro i
      rw [pow_add, hmul, hpow β, Function.RightInverse.iterate hginv β, hg]
    intro v
    rw [hsh (β₀ + β) v 0, zero_add, hspan]
    constructor
    · rintro ⟨d, hd⟩
      refine ⟨d, hinj (β₀ + β) ?_⟩

      rw [hd, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hcomm, hf i]
    · rintro ⟨d, rfl⟩
      refine ⟨d, ?_⟩

      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hcomm, hf i]
  refine ⟨fun i => ginv^[β] (g i), h1, h2, ?_⟩
  refine GlobalTheory.T.linearIndependent_of_mutual_span_of_indep R W act hmul hone ι b _ hbi ?_ ?_
  · intro i
    exact (hb0 _).1 ((h2 _).2 ⟨Pi.single i 1, (hsingle (fun i => ginv^[β] (g i)) i).symm⟩)
  · intro k
    exact (h2 _).1 ((hb0 _).2 ⟨Pi.single k 1, (hsingle b k).symm⟩)


private theorem mulVec_smul_single_one_apply {R ι : Type} [CommSemiring R] [Fintype ι]
    [DecidableEq ι] (M : Matrix ι ι R) (r : R) (i j : ι) :
    (M *ᵥ (r • Pi.single i 1)) j = r * M j i := by
  rw [Matrix.mulVec_smul, Matrix.mulVec_single_one]
  rfl

private theorem map_pow_mul_of_eq {R S : Type} [Semiring R] [Semiring S]
    (f : R →+* S) (z y : R) (w : S) (n m : ℕ) (h : f y = f z ^ m * w) :
    f (z ^ n * y) = f z ^ (n + m) * w := by
  rw [map_mul, map_pow, h, pow_add, mul_assoc]

set_option maxHeartbeats 8000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem GlobalTheory.BKGal.JumpDR.basis_images : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T) (jB : (ι → OB l ↥(OL LL)) ≃ₗ[OB l ↥(OL LL)] TW (OB l ↥(OL LL)) T) (Pl : LocPrime l) (AI : LocAinf l Pl) (Td : LocTied l Pl AI), IsCrisCmp I jB → ∀ (X : TW (OB l ↥(OL LL)) T →+ T.V ⊗[ℚ_[l]] Pl.R.BdR), (∀ (o : ↥(OL LL)) (b : Per.Bcris l) (x : ↥T.L.T), X ((o ⊗ₜ[ℤ_[l]] b) ⊗ₜ[↥(OL LL)] x) = ((o : ↥LL.1) • (x : T.V)) ⊗ₜ[ℚ_[l]] GlobalTheory.BKGal.JumpDR.cB Td b) → ∀ (A : OD l ↥(OL LL) →+ (T.V ⊗[ℚ_[l]] Pl.R.BdR →+ T.V ⊗[ℚ_[l]] Pl.R.BdR)), (∀ (o : ↥(OL LL)) (b : Per.BdRp l) (v : T.V) (c : Pl.R.BdR), A (o ⊗ₜ[ℤ_[l]] b) (v ⊗ₜ[ℚ_[l]] c) = ((o : ↥LL.1) • v) ⊗ₜ[ℚ_[l]] (GlobalTheory.BKGal.JumpDR.cD Td b * c)) → ∀ (β : ℕ) (y : ZMod a → ι → ι → Ahat ↥(OL LL) ↥LL.1 l e), (∀ τ j i, algebraMap (Ahat ↥(OL LL) ↥LL.1 l e) (AhatE ↥(OL LL) ↥LL.1 l e) (y τ j i) = algebraMap (Ahat ↥(OL LL) ↥LL.1 l e) (AhatE ↥(OL LL) ↥LL.1 l e) (Ehat ↥(OL LL) ↥LL.1 l e) ^ β * hat ↥(OL LL) l e (P.mxInv τ j i)) → ∃ f : ι → T.V ⊗[ℚ_[l]] Pl.R.BdR, (∀ i, A ((ϖ.iD (thetaW a LL) ↥LL.1 (fun _ => Ehat ↥(OL LL) ↥LL.1 l e)) ^ β) (f i) = ∑ j, A (ϖ.iD (thetaW a LL) ↥LL.1 (fun τ => y τ j i)) (X (jB (Pi.single j 1)))) ∧ (∀ v, v ∈ FilV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (LL := ↥LL.1) (V := T.V) (0) ↔ ∃ d : ι → OD l ↥(OL LL), v = ∑ i, A (d i) (f i)) ∧ ∀ d : ι → OD l ↥(OL LL), ∑ i, A (d i) (f i) = 0 → ∀ i, d i = 0 := by
  intro hF l _ a e _ _ ϖ LL _ _ hl2 ι _ _ P T I jB Pl AI Td hC X hX act hA β y hy
  have hAct := GlobalTheory.T.coeffDeRhamPlusAction_mul_one l LL T Pl AI Td act hA
  have hE := GlobalTheory.T.eisenstein_mul_bijective_shifts_filtrationV l a e ϖ LL T Pl AI Td act hA
  have hExp := P.exists_exponents
  refine hExp.elim fun α h => h.elim fun β0 hBounds => ?_
  have hLM1 : ∀ v ∈ P.M, E ↥LL.1 l e ^ (β0 + β) • v ∈ P.L := by
    intro v hv
    have := P.L.smul_mem (⟨_, pow_mem (E_mem l e _) β⟩ : A ↥(OL LL) ↥LL.1) (hBounds.2 v hv)
    rw [pow_add, mul_comm, mul_smul]
    exact this
  have hβ1 : ∀ τ j i, E ↥LL.1 l e ^ (β0 + β) * P.mxInv τ j i ∈ A ↥(OL LL) ↥LL.1 := by
    intro τ j i
    let v : ι → (↥LL.1)⟦X⟧ := Pi.single i 1
    have hv : (fun _ : ZMod a => v) ∈ P.M :=
      (mem_tot (P := fun _ => Mc ↥(OL LL) ↥LL.1 ι)).2 fun _ =>
        (mem_vecs (B := A ↥(OL LL) ↥LL.1)).2 fun k => by
          change (Pi.single i (1 : (↥LL.1)⟦X⟧) : ι → (↥LL.1)⟦X⟧) k ∈ A ↥(OL LL) ↥LL.1
          by_cases hk : k = i
          · rw [hk, Pi.single_eq_same]
            exact one_mem _
          · rw [Pi.single_eq_of_ne hk]
            exact zero_mem _
    have hw := (mem_tot (P := P.extc (A ↥(OL LL) ↥LL.1))).1 (hLM1 _ hv) τ
    have hmem := (mem_vecs (B := A ↥(OL LL) ↥LL.1)).1 (P.mem_extc_iff.1 hw) j
    exact (congrArg (fun z : (↥LL.1)⟦X⟧ => z ∈ A ↥(OL LL) ↥LL.1)
      (mulVec_smul_single_one_apply (P.mxInv τ) (E ↥LL.1 l e ^ (β0 + β)) i j)).mp hmem
  let eHat := Ehat ↥(OL LL) ↥LL.1 l e
  let loc := algebraMap (Ahat ↥(OL LL) ↥LL.1 l e) (AhatE ↥(OL LL) ↥LL.1 l e)
  let yScaled (τ : ZMod a) (j i : ι) := eHat ^ β0 * y τ j i
  have hy1 (τ : ZMod a) (j i : ι) :=
    map_pow_mul_of_eq loc eHat (y τ j i) (hat ↥(OL LL) l e (P.mxInv τ j i)) β0 β (hy τ j i)
  have hyA := GlobalTheory.T.coordinates_eq_of_eisensteinPow_mul_inverse_matrix l a e ϖ LL ι P
    (β0 + β) yScaled hy1 hβ1
  let iD := ϖ.iD (thetaW a LL) ↥LL.1
  let constantEhat : ZMod a → Ahat ↥(OL LL) ↥LL.1 l e := fun _ => eHat
  let eD := iD constantEhat
  let x (j : ι) := X (jB (Pi.single j 1))
  let c (j i : ι) (τ : ZMod a) : A ↥(OL LL) ↥LL.1 :=
    ⟨E ↥LL.1 l e ^ (β0 + β) * P.mxInv τ j i, hβ1 τ j i⟩
  let d (j i : ι) := iD (fun τ => y τ j i)
  let d' (j i : ι) := toOD l ↥(OL LL) (ϖ.iTot (thetaW a LL) ↥LL.1 (c j i))
  let g (i : ι) := ∑ j, act (d j i) (x j)
  let h (i : ι) := ∑ j, act (d' j i) (x j)
  have hcoeff (j i : ι) : eD ^ β0 * d j i = d' j i := by
    have hpt : constantEhat ^ β0 * (fun τ => y τ j i) =
        fun τ => ofA ↥(OL LL) ↥LL.1 l e (c j i τ) :=
      funext fun τ => hyA τ j i
    calc
      _ = iD (constantEhat ^ β0) * d j i :=
        congrArg (fun z => z * d j i) (map_pow iD constantEhat β0).symm
      _ = iD (constantEhat ^ β0 * (fun τ => y τ j i)) :=
        (map_mul iD (constantEhat ^ β0) (fun τ => y τ j i)).symm
      _ = iD (fun τ => ofA ↥(OL LL) ↥LL.1 l e (c j i τ)) := congrArg iD hpt
      _ = _ := PiSys.iD_ofA (thetaW a LL) ↥LL.1 ϖ (c j i)
  have hg (i : ι) : act (eD ^ β0) (g i) = h i :=
    (map_sum (act (eD ^ β0)) (fun j => act (d j i) (x j)) (Finset.univ : Finset ι)).trans
      (Finset.sum_congr rfl fun j _ =>
        (hAct.1 (eD ^ β0) (d j i) (x j)).symm.trans (congrArg (fun z => act z (x j)) (hcoeff j i)))
  have hspan := GlobalTheory.T.breuilKisin_filtration_span_deRhamLattice hF l a e ϖ LL hl2 ι P T I
    jB Pl AI Td hC X hX act hA α (β0 + β) hBounds.1 hLM1 hβ1
  have hBasis := GlobalTheory.T.galoisLattice_basis_indexed_by_breuilKisin l a e ϖ LL ι P T I
  refine hBasis.elim fun b => ?_
  have hb := GlobalTheory.T.coeffDeRhamPlus_basis_tensorLattice_free l LL T Pl AI Td act hA ι b
  exact GlobalTheory.BKGal.JumpDR.BasisGlue.exists_basis act hAct.1 hAct.2 eD hE.1
    (fun (j : ℤ) (v : T.V ⊗[ℚ_[l]] Pl.R.BdR) =>
      v ∈ FilV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (LL := ↥LL.1) (V := T.V) j)
    hE.2 β β0 g h
    (fun k => ((b k : ↥T.L.T) : T.V) ⊗ₜ[ℚ_[l]] (1 : Pl.R.BdR)) hg hspan hb.1 hb.2

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

namespace GlobalTheory.ExhaustRows

theorem main : ∀ (D : D7) (M : MtFam D), HeckeTied D M → AVTied D M → ∀ Tn : NormalizedLocalCompatibility D M, HeckeStdTw Tn.B → SumRepresentations.Conclusion42 D → GoodFTAll D → ∀ (i : D.nd.Loc) (σ : D.what₂.FT), D.what₂.isot (D.nd.j i) σ ≠ ⊥ → D.nd.goodRow σ ∧ ∃ i' ∈ D.nd.locs (D.nd.j i) (D.nd.w i), HG D.nd D.naut i' ∧ AtM D.nd D.naut i' σ := by
  intro D M hT hA Tn hS h42 hG i σ hne
  have hg : D.nd.goodRow σ := hG σ
  obtain ⟨P, hP⟩ := ((h42 i) σ hne).1.2
  obtain ⟨i', hi', P', x', hth, hx⟩ := GlobalTheory.T.theta_lift_has_point_at_localisation_same_place D M hT hA Tn hS i σ P hP
  obtain ⟨hxg, hat⟩ := GlobalTheory.T.thetaLift_goodRow_point_good D h42 i' σ P' x' hg hth hx
  exact ⟨hg, i', hi', ⟨x', hxg⟩, hat⟩

end GlobalTheory.ExhaustRows
end
