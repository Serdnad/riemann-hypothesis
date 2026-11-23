module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FlagComponentFramedPointFrame
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle651
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineStableLieEigenspaceFrame
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStalkFactor
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2336
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle167
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle635
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle471
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle625
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle012
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle681
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle631
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle683
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
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
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalBoundaryMetricData
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle682
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle008
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle102

@[expose] public section

section

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.LieBase
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts
open scoped Topology
open ReciprocityTheory.L2DbarEstimates (V)

set_option autoImplicit false

noncomputable section

open CategoryTheory.Limits

namespace GlobalTheory.ShFam.StalkSpread

open GlobalTheory.LieLocFrame (res res_sum res_res)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (spMap_comp_spMap)
open scoped CategoryTheory.MonObj

attribute [local instance] Over.cartesianMonoidalCategory

theorem exists_affine_isMap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (X : Var F) (j : X.X ⟶ gen Z) (z : X.X) (φz : c.F →+* X.X.presheaf.stalk z) (fz : EigFrame Z φz (stalkPt X z ≫ j ≫ genι Z)) (W₀ : X.X.Opens), z ∈ W₀ → stalkPt X z ≫ j ≫ genStr Z = spMap φz → ∃ (W : X.X.Opens) (hW : IsAffineOpen W) (φ : c.F →+* Γ(X.X, W)) (fW : EigFrame Z φ (((show Sp Γ(X.X, W) ⟶ X.X from hW.fromSpec) ≫ j) ≫ genι Z)) (hz : z ∈ W), W ≤ W₀ ∧ ((show Sp Γ(X.X, W) ⟶ X.X from hW.fromSpec) ≫ j) ≫ genStr Z = spMap φ ∧ (fun mapψ dstFrame => ∀ embτ basisIdx, _root_.GlobalTheory.ShFam.EigFrame.v dstFrame embτ basisIdx = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (_root_.Formalism.L2.Pj.dualMap mapψ) ≫ _root_.GlobalTheory.ShFam.EigFrame.v fW embτ basisIdx) (X.X.presheaf.germ W z hz).hom fz := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ X j z φz fz W₀ hz₀ hstr
  obtain ⟨U₀, hU₀, φ₀, f₀, hy₀, hs₀, -⟩ := GlobalTheory.ShFam.EigSpread.exists_stable_eigFrame E H Dw l Xo c O β Z (j z)
  let gm₀ : Γ(gen Z, U₀) →+* X.X.presheaf.stalk z :=
    (X.X.presheaf.germ (j ⁻¹ᵁ U₀) z hy₀).hom.comp (j.app U₀).hom
  have hgm : ∀ (U : X.X.Opens) (hy : z ∈ U) (h : U ≤ j ⁻¹ᵁ U₀),
      (X.X.presheaf.germ U z hy).hom.comp (j.appLE U₀ U h).hom = gm₀ := fun U hy h =>
    RingHom.ext fun a => X.X.presheaf.germ_res_apply (homOfLE h) z hy _
  have hρ : ∀ (U : X.X.Opens) (hU : IsAffineOpen U) (h : U ≤ j ⁻¹ᵁ U₀),
      spMap (j.appLE U₀ U h).hom ≫ (show Sp Γ(gen Z, U₀) ⟶ gen Z from hU₀.fromSpec) =
        (show Sp Γ(X.X, U) ⟶ X.X from hU.fromSpec) ≫ j := fun U hU h =>
    IsAffineOpen.SpecMap_appLE_fromSpec j hU₀ hU h
  have hx₀ : spMap gm₀ ≫ (show Sp Γ(gen Z, U₀) ⟶ gen Z from hU₀.fromSpec) = stalkPt X z ≫ j := by
    obtain ⟨U, hU, hy, h⟩ := exists_isAffineOpen_mem_and_subset (X := X.X) (U := j ⁻¹ᵁ U₀) (x := z) hy₀
    rw [← hgm U hy h, ← spMap_comp_spMap, Category.assoc, hρ U hU h, ← Category.assoc, Spread.spMap_germ]
    rfl
  have hs₀' : (show Sp Γ(gen Z, U₀) ⟶ gen Z from hU₀.fromSpec) ≫ genStr Z = spMap φ₀ := hs₀
  have hφ₀ : gm₀.comp φ₀ = φz := by
    have h1 : spMap (gm₀.comp φ₀) = spMap φz := by
      rw [← spMap_comp_spMap, ← hs₀', ← Category.assoc, hx₀, Category.assoc, hstr]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
  have hx₁ : spMap gm₀ ≫ (show Sp Γ(gen Z, U₀) ⟶ gen Z from hU₀.fromSpec) ≫ genι Z =
      stalkPt X z ≫ j ≫ genι Z := by rw [← Category.assoc, hx₀, Category.assoc]
  obtain ⟨g, hg⟩ := Spread.exists_bc f₀ gm₀ hφ₀ hx₁
  choose A B hAB hA using Spread.exists_coord g fz
  obtain ⟨U, hU, hy, s, hle, hs⟩ := Spread.exists_affine_germs z (W := W₀ ⊓ j ⁻¹ᵁ U₀) ⟨hz₀, hy₀⟩
    (fun p : Bool × (Σ τ : E →+* ℂ, Fin (Dw.mult τ) × Fin (Dw.mult τ)) =>
      (cond p.1 (A p.2.1) (B p.2.1)) p.2.2.1 p.2.2.2)
  have h₀ : U ≤ j ⁻¹ᵁ U₀ := fun w hw => (hle hw).2
  let gm : Γ(X.X, U) →+* X.X.presheaf.stalk z := (X.X.presheaf.germ U z hy).hom
  let ρ : Γ(gen Z, U₀) →+* Γ(X.X, U) := (j.appLE U₀ U h₀).hom
  let A' : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) Γ(X.X, U) :=
    fun τ => Matrix.of fun i k => s (true, ⟨τ, i, k⟩)
  let B' : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) Γ(X.X, U) :=
    fun τ => Matrix.of fun i k => s (false, ⟨τ, i, k⟩)
  have hA' : ∀ τ i k, gm (A' τ i k) = A τ i k := fun τ i k => hs (true, ⟨τ, i, k⟩)
  have hB' : ∀ τ i k, gm (B' τ i k) = B τ i k := fun τ i k => hs (false, ⟨τ, i, k⟩)
  have hAB' : ∀ τ, B' τ * A' τ = 1 := fun τ => Matrix.ext fun i k => germ_injective_of_isIntegral X.X z hy (by
    show gm _ = gm _
    have := congrFun (congrFun (hAB τ) i) k

    simp only [Matrix.mul_apply, map_sum, map_mul, hA', hB', Matrix.one_apply] at this ⊢
    rw [this]
    split_ifs <;> simp)
  have hx₂ : spMap ρ ≫ (show Sp Γ(gen Z, U₀) ⟶ gen Z from hU₀.fromSpec) ≫ genι Z =
      ((show Sp Γ(X.X, U) ⟶ X.X from hU.fromSpec) ≫ j) ≫ genι Z := by rw [← Category.assoc, hρ U hU h₀]
  have hx₃ : spMap gm ≫ ((show Sp Γ(X.X, U) ⟶ X.X from hU.fromSpec) ≫ j) ≫ genι Z =
      stalkPt X z ≫ j ≫ genι Z := by
    rw [Category.assoc, ← Category.assoc, Spread.spMap_germ]
    rfl
  obtain ⟨g', hg'⟩ := Spread.exists_bc f₀ ρ rfl hx₂
  obtain ⟨fr, hfr⟩ := Spread.exists_change g' A' B' hAB'
  refine ⟨U, hU, ρ.comp φ₀, fr, hy, fun w hw => (hle hw).1, ?_, fun τ i => ?_⟩
  · rw [← hρ U hU h₀, Category.assoc, hs₀']
    exact spMap_comp_spMap φ₀ ρ
  · have hv : fz.vec τ i = res gm hx₃ (fr.vec τ i) := by
      rw [hfr, res_sum, hA]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hA', hg, hg', res_res ρ hx₂ gm hx₃ (hgm U hy h₀) hx₁]
    exact congrArg (fun v => (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv v).left) hv

end GlobalTheory.ShFam.StalkSpread
end
end

section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagCptBase

theorem exists_geomPt (S : Scheme.{0}) (s : S) :
    ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (q : Sp K ⟶ S), s ∈ Set.range q := by
  let K := AlgebraicClosure (S.residueField s)
  obtain ⟨t⟩ : Nonempty (Sp K) := inferInstance
  refine ⟨K, inferInstance, inferInstance, spMap (algebraMap (S.residueField s) K) ≫ S.fromSpecResidueField s, t, ?_⟩
  have h : S.fromSpecResidueField s (spMap (algebraMap (S.residueField s) K) t) ∈
      Set.range (S.fromSpecResidueField s) := ⟨_, rfl⟩
  rw [Scheme.range_fromSpecResidueField] at h
  rw [Scheme.Hom.comp_apply]
  exact h

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {F : Type} [Field F] {e : F ≃+* c.F}

theorem isClosed_range_π (C : FlagCpt Z e) : IsClosed (Set.range C.π) := by
  have hZ : IsProper Z.s := projProper O Z.X Z.s Z.proj
  have : IsProper (genStr Z) := inferInstance
  have : IsSeparated (genStr Z ≫ spMap e.toRingHom) := inferInstance
  have : IsProper (C.π ≫ genStr Z ≫ spMap e.toRingHom) := by rw [C.π_str]; infer_instance
  have : IsProper C.π := IsProper.of_comp C.π (genStr Z ≫ spMap e.toRingHom)
  exact C.π.isClosedMap.isClosed_range

end GlobalTheory.FlagCptBase

namespace GlobalTheory.FlagCptBase

open CategoryTheory.Limits

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {F : Type} [Field F] {e : F ≃+* c.F} {σ : c.F →+* ℂ} {N : ℕ} {U : Formalism.L2.PjFree.Unf Xo c σ N}

theorem exists_mem_range (Φ : FlagTor Z e U) (w : gen Z) : ∃ i, w ∈ Set.range (Φ.C i).π := by
  obtain ⟨K, _, _, q, t, hq⟩ := exists_geomPt _ w
  let χ : c.F →+* K := (Spec.preimage (q ≫ genStr Z)).hom
  have hχ : q ≫ genStr Z = spMap χ := (Spec.map_preimage _).symm
  obtain ⟨g⟩ := GlobalTheory.ShFam.EigLoc.exists_eigFrame E H Dw l Xo c O β Z K χ q hχ
  obtain ⟨⟨i, p⟩, ⟨hp, -⟩, -⟩ := Φ.lifts K χ q hχ g
  refine ⟨i, p t, ?_⟩
  rw [← hq, ← Scheme.Hom.comp_apply]
  exact congrArg (fun m : Sp K ⟶ gen Z => m t) hp

theorem eq_of_apply_eq (Φ : FlagTor Z e U)
    (hA : ∀ (i : U.Comp) (K : Type) [Field K] [IsAlgClosed K] (χ : c.F →+* K) (x : Sp K ⟶ gen Z),
      x ≫ genStr Z = spMap χ → ∀ (g g' : EigFrame Z χ (x ≫ genι Z)) (p : Sp K ⟶ (Φ.C i).Y.X), p ≫ (Φ.C i).π = x →
      (Φ.C i).Carries p g → ∃ p' : Sp K ⟶ (Φ.C i).Y.X, p' ≫ (Φ.C i).π = x ∧ (Φ.C i).Carries p' g')
    (hB : ∀ (i : U.Comp) (K : Type) [Field K] (χ : c.F →+* K) (p : Sp K ⟶ (Φ.C i).Y.X),
      p ≫ (Φ.C i).π ≫ genStr Z = spMap χ → ∃ g : EigFrame Z χ (p ≫ (Φ.C i).π ≫ genι Z), (Φ.C i).Carries p g)
    {i i' : U.Comp} (y : (Φ.C i).Y.X) (y' : (Φ.C i').Y.X) (h : (Φ.C i).π y = (Φ.C i').π y') : i = i' := by
  obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := (Φ.C i).π) (g := (Φ.C i').π) y y' h
  obtain ⟨K, _, _, q, -⟩ := exists_geomPt _ z
  let p := q ≫ pullback.fst (Φ.C i).π (Φ.C i').π
  let p' := q ≫ pullback.snd (Φ.C i).π (Φ.C i').π
  let w := p ≫ (Φ.C i).π
  have hw' : p' ≫ (Φ.C i').π = w := by
    simp only [p, p', w, Category.assoc, pullback.condition]
  let χ : c.F →+* K := (Spec.preimage (w ≫ genStr Z)).hom
  have hχ : w ≫ genStr Z = spMap χ := (Spec.map_preimage _).symm
  have hB' : ∀ (i : U.Comp) (p : Sp K ⟶ (Φ.C i).Y.X) (x : Sp K ⟶ gen Z), p ≫ (Φ.C i).π = x →
      x ≫ genStr Z = spMap χ → ∃ g : EigFrame Z χ (x ≫ genι Z), (Φ.C i).Carries p g := by
    intro i p x hx hxχ
    subst hx
    rw [Category.assoc] at hxχ ⊢
    exact hB i K χ p hxχ
  obtain ⟨g, hg⟩ := hB' i p w rfl hχ
  obtain ⟨g', hg'⟩ := hB' i' p' w hw' hχ
  obtain ⟨p'', hp'', hc''⟩ := hA i K χ w hχ g g' p rfl hg
  obtain ⟨_, -, huniq⟩ := Φ.lifts K χ w hχ g'
  have h1 := huniq ⟨i, p''⟩ ⟨hp'', hc''⟩
  have h2 := huniq ⟨i', p'⟩ ⟨hw', hg'⟩
  exact congrArg Sigma.fst (h1.trans h2.symm)

end GlobalTheory.FlagCptBase

theorem GlobalTheory.FlagCptBase.exists_pt_over_base : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (N : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ N) (Φ : FlagTor Z e U) (k : U.Comp) (X : Var F) (j : X.X ⟶ gen Z), IsOpenImmersion j → j ≫ genStr Z ≫ spMap e.toRingHom = X.str → ∀ (f : (Φ.C k).Y.X ⟶ X.X), f ≫ j = (Φ.C k).π → (∀ (i : U.Comp) (K : Type) [Field K] [IsAlgClosed K] (χ : c.F →+* K) (x : Sp K ⟶ gen Z), x ≫ genStr Z = spMap χ → ∀ (g g' : EigFrame Z χ (x ≫ genι Z)) (p : Sp K ⟶ (Φ.C i).Y.X), p ≫ (Φ.C i).π = x → (Φ.C i).Carries p g → ∃ p' : Sp K ⟶ (Φ.C i).Y.X, p' ≫ (Φ.C i).π = x ∧ (Φ.C i).Carries p' g') → (∀ (i : U.Comp) (K : Type) [Field K] (χ : c.F →+* K) (p : Sp K ⟶ (Φ.C i).Y.X), p ≫ (Φ.C i).π ≫ genStr Z = spMap χ → ∃ g : EigFrame Z χ (p ≫ (Φ.C i).π ≫ genι Z), (Φ.C i).Carries p g) → ∀ (K : Type) [Field K] [IsAlgClosed K] (χ : c.F →+* K) (x : Sp K ⟶ X.X), x ≫ j ≫ genStr Z = spMap χ → ∃ p : Sp K ⟶ (Φ.C k).Y.X, p ≫ f = x := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e σ N U Φ k X j hj _ f hf hA hB K _ _ χ x hx
  let W : U.Comp → Set X.X := fun i => j ⁻¹' Set.range (Φ.C i).π
  have hcl : ∀ i, IsClosed (W i) := fun i => (GlobalTheory.FlagCptBase.isClosed_range_π (Φ.C i)).preimage j.continuous
  have hdis : ∀ i i' z, z ∈ W i → z ∈ W i' → i = i' := by
    rintro i i' z ⟨y, hy⟩ ⟨y', hy'⟩
    exact GlobalTheory.FlagCptBase.eq_of_apply_eq Φ hA hB y y' (hy.trans hy'.symm)
  have hcov : ∀ z, ∃ i, z ∈ W i := fun z => GlobalTheory.FlagCptBase.exists_mem_range Φ (j z)
  have hWk : W k = Set.univ := by
    have hc : (W k)ᶜ = ⋃ i ∈ ({k}ᶜ : Set U.Comp), W i := by
      ext z
      simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_singleton_iff, exists_prop]
      constructor
      · intro hz
        obtain ⟨i, hi⟩ := hcov z
        exact ⟨i, fun h => hz (h ▸ hi), hi⟩
      · rintro ⟨i, hik, hi⟩ hz
        exact hik (hdis i k z hi hz)
    have hopen : IsOpen (W k) := by
      rw [← isClosed_compl_iff, hc]
      exact Set.Finite.isClosed_biUnion (Set.toFinite _) (fun i _ => hcl i)
    obtain ⟨y⟩ : Nonempty (Φ.C k).Y.X := inferInstance
    have hne : (W k).Nonempty := ⟨f y, y, by rw [← hf, Scheme.Hom.comp_apply]⟩
    exact IsClopen.eq_univ ⟨hcl k, hopen⟩ hne
  have hx' : (x ≫ j) ≫ genStr Z = spMap χ := by rw [Category.assoc]; exact hx
  obtain ⟨g⟩ := GlobalTheory.ShFam.EigLoc.exists_eigFrame E H Dw l Xo c O β Z K χ (x ≫ j) hx'
  obtain ⟨⟨i, p⟩, ⟨hp, -⟩, -⟩ := Φ.lifts K χ (x ≫ j) hx' g
  obtain ⟨t⟩ : Nonempty (Sp K) := inferInstance
  have hi : i = k := by
    have h1 : x t ∈ W i := ⟨p t, by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply]
      exact congrArg (fun m : Sp K ⟶ gen Z => m t) hp⟩
    have h2 : x t ∈ W k := hWk ▸ Set.mem_univ _
    exact hdis _ _ _ h1 h2
  subst hi
  refine ⟨p, ?_⟩
  rw [← cancel_mono j, Category.assoc, hf]
  exact hp
end
end

section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical

namespace GlobalTheory.CompOfVar

theorem exists_var_comp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F), SmoothOfRelativeDimension Dw.dim (genStr Z) → ∀ (Y : Var F) (π : Y.X ⟶ gen Z), π ≫ genStr Z ≫ spMap e.toRingHom = Y.str → ∃ (X : Var F) (j : X.X ⟶ gen Z), IsOpenImmersion j ∧ j ≫ genStr Z ≫ spMap e.toRingHom = X.str ∧ Set.range π ⊆ Set.range j := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e hsm Y π hπ
  have hS : Smooth (genStr Z) := SmoothOfRelativeDimension.smooth Dw.dim _
  have := isProper_genStr Z
  have : IsLocallyNoetherian (gen Z) := LocallyOfFiniteType.isLocallyNoetherian (genStr Z)
  have : CompactSpace (gen Z) := QuasiCompact.compactSpace_of_compactSpace (genStr Z)
  have : IsNoetherian (gen Z) := {}
  have hcc := fun z : gen Z => PtComp.connectedComponent_mem
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
    (fun W hW W' hW' => PtComp.disjoint_of_smooth (genStr Z) hS W W' hW hW') z
  let z : gen Z := π (genericPoint Y.X)
  let V : (gen Z).Opens := ⟨connectedComponent z, (hcc z).2⟩
  have hred : IsReduced (gen Z) := by
    have := GlobalTheory.isNormalScheme_of_smooth (genStr Z)
    exact GlobalTheory.IsNormalScheme.isReduced
  have : CharZero F := e.toRingHom.charZero
  have : IsIso (spMap e.toRingHom) :=
    inferInstanceAs (IsIso (Spec.map e.toCommRingCatIso.hom))
  have hproj : IsProjOver (genStr Z ≫ spMap e.toRingHom) := GlobalTheory.GenFibreComp.isProjOver_comp_equiv e _
    ((GlobalTheory.ProjSpace.points_and_stability O 0).2.2.1 c.F β Z.X Z.s Z.proj)
  have : IrreducibleSpace V.toScheme := Subtype.irreducibleSpace (hcc z).1.1
  have : IsIntegral V.toScheme := isIntegral_of_irreducibleSpace_of_isReduced _
  have hcl : IsClosedImmersion V.ι := IsClosedImmersion.of_isPreimmersion _ (by
    rw [Scheme.Opens.range_ι]; exact isClosed_connectedComponent)
  have hp : IsProjOver (V.ι ≫ genStr Z ≫ spMap e.toRingHom) :=
    (GlobalTheory.ProjSpace.points_and_stability F 0).2.2.2.1 _ _ _ _ hcl hproj
  have hsd : SmoothOfRelativeDimension Dw.dim (V.ι ≫ genStr Z ≫ spMap e.toRingHom) := by
    have h : SmoothOfRelativeDimension (0 + (Dw.dim + 0)) (V.ι ≫ genStr Z ≫ spMap e.toRingHom) := inferInstance
    simpa using h
  have hr : Set.range π ⊆ Set.range V.ι := by
    rw [Scheme.Opens.range_ι]
    exact (isPreconnected_range π.continuous).subset_connectedComponent ⟨_, rfl⟩
  let g : Y.X ⟶ V.toScheme := IsOpenImmersion.lift V.ι π hr
  have hg : g ≫ V.ι = π := IsOpenImmersion.lift_fac _ _ _
  have : Smooth (V.ι ≫ genStr Z ≫ spMap e.toRingHom) := SmoothOfRelativeDimension.smooth Dw.dim _
  have : GlobalTheory.IsNormalScheme V.toScheme := GlobalTheory.ModifSections.isNormalScheme_of_smooth (V.ι ≫ genStr Z ≫ spMap e.toRingHom)
  have : GeometricallyConnected (V.ι ≫ genStr Z ≫ spMap e.toRingHom) := by
    refine GlobalTheory.GeomConnFn.geometricallyConnected_of_locallyOfFiniteType _ ?_
    exact GlobalTheory.T.algebraicConstants_descend_to_normalIntegralScheme F V.toScheme Y.X _ Y.str g (by rw [reassoc_of% hg, hπ])
      (GlobalTheory.T.geometricallyIntegral_algebraicConstants_mem_range F Y.X Y.str)
  obtain ⟨X, ε, -, hs⟩ := GlobalTheory.ProjVar.Var.exists_iso _ Dw.dim hp
  refine ⟨X, ε.inv ≫ V.ι, inferInstance, ?_, ?_⟩
  · rw [Category.assoc, ← hs, Iso.inv_hom_id_assoc]
  · rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, ε.inv.surjective.range_eq, Set.image_univ]
    exact hr

end GlobalTheory.CompOfVar
end

section

noncomputable section

open Matrix GlobalTheory.RedTh NumberField GlobalTheory.PolFan ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.RedTh

theorem exists_siegel_split {X X₁ : Type} [AddCommGroup X] [AddCommGroup X₁] [Module.Finite ℤ X] [Module.Free ℤ X]
    [Module.Finite ℤ X₁] [Module.Free ℤ X₁] (r : X →ₗ[ℤ] X₁) (σ : X₁ →ₗ[ℤ] X) (hrσ : ∀ y, r (σ y) = y)
    (B₀ : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) (hs₀ : ∀ y z, B₀ y z = B₀ z y) (hp₀ : IsPosDef B₀)
    (B₁ : X₁ →ₗ[ℤ] X₁ →ₗ[ℤ] ℝ) (hs₁ : ∀ y z, B₁ y z = B₁ z y) (hp₁ : IsPosDef B₁)
    (n : ℕ) (hn : Module.finrank ℤ X = n) :
    ∃ (b : Module.Basis (Fin n) ℤ X) (d d' : Fin n → ℝ) (u : Matrix (Fin n) (Fin n) ℝ) (t : ℝ),
      IsSiegel d u ∧ IsSiegel d' u ∧ (∀ i, 0 < d' i) ∧ (∀ i j, B₁ (r (b i)) (r (b j)) = gram d u i j) ∧
      ∀ i j, t * B₀ (b i - σ (r (b i))) (b j - σ (r (b j))) + B₁ (r (b i)) (r (b j)) = gram d' u i j := by
  classical
  have hfree : Module.Free ℤ (LinearMap.ker r) := Module.free_of_finite_type_torsion_free'
  obtain ⟨s, ⟨bK⟩⟩ : ∃ s, Nonempty (Module.Basis (Fin s) ℤ (LinearMap.ker r)) := ⟨_, ⟨Module.finBasis ℤ _⟩⟩
  obtain ⟨m, ⟨bQ⟩⟩ : ∃ m, Nonempty (Module.Basis (Fin m) ℤ X₁) := ⟨_, ⟨Module.finBasis ℤ _⟩⟩
  let BK : LinearMap.ker r →ₗ[ℤ] LinearMap.ker r →ₗ[ℤ] ℝ := B₀.compl₁₂ (LinearMap.ker r).subtype (LinearMap.ker r).subtype
  have hpK : IsPosDef BK := fun k x hx c hc =>
    hp₀ k (fun i => (x i : X)) (hx.map' (LinearMap.ker r).subtype (Submodule.ker_subtype _)) c hc
  obtain ⟨b₁, d₁, u₁, hS₁, hd₁, hg₁⟩ := GlobalTheory.T.exists_siegelReduced_basis_of_posDef_form s _ bK BK (fun y z => hs₀ _ _) hpK
  obtain ⟨b₂, d₂, u₂, hS₂, hd₂, hg₂⟩ := GlobalTheory.T.exists_siegelReduced_basis_of_posDef_form m _ bQ B₁ hs₁ hp₁
  obtain ⟨t, d, d', u, -, hS, hS', hd', g11, g12, g22⟩ := GlobalTheory.T.exists_siegel_reduction_orthogonal s m d₁ u₁ d₂ u₂ hS₁ hS₂ hd₁ hd₂
  let p : X →ₗ[ℤ] LinearMap.ker r := LinearMap.codRestrict _ (LinearMap.id - σ ∘ₗ r) fun x => by
    simp [hrσ]
  let e : X ≃ₗ[ℤ] LinearMap.ker r × X₁ := LinearEquiv.ofLinear (p.prod r) ((LinearMap.ker r).subtype.coprod σ)
    (by
      ext x
      · simp [p, LinearMap.mem_ker.1 x.2]
      · simp [LinearMap.mem_ker.1 x.2]
      · simp [p, hrσ]
      · simp [hrσ])
    (by ext x; simp [p])
  let c : Module.Basis (Fin (s + m)) ℤ X := ((b₁.prod b₂).map e.symm).reindex finSumFinEquiv
  have hc₁ : ∀ i, c (Fin.castAdd m i) = (b₁ i : X) := fun i => by
    have : finSumFinEquiv.symm (Fin.castAdd m i) = Sum.inl i := finSumFinEquiv_symm_apply_castAdd i
    simp [c, this, e]
  have hc₂ : ∀ j, c (Fin.natAdd s j) = σ (b₂ j) := fun j => by
    have : finSumFinEquiv.symm (Fin.natAdd s j) = Sum.inr j := finSumFinEquiv_symm_apply_natAdd j
    simp [c, this, e]
  have hnm : n = s + m := by
    rw [← hn, Module.finrank_eq_card_basis c, Fintype.card_fin]
  subst hnm
  have hr₁ : ∀ i, r (c (Fin.castAdd m i)) = 0 := fun i => by rw [hc₁]; exact (b₁ i).2
  have hr₂ : ∀ j, r (c (Fin.natAdd s j)) = b₂ j := fun j => by rw [hc₂, hrσ]
  have hq₁ : ∀ i, c (Fin.castAdd m i) - σ (r (c (Fin.castAdd m i))) = (b₁ i : X) := fun i => by
    rw [hr₁, map_zero, sub_zero, hc₁]
  have hq₂ : ∀ j, c (Fin.natAdd s j) - σ (r (c (Fin.natAdd s j))) = 0 := fun j => by rw [hr₂, hc₂, sub_self]
  refine ⟨c, d, d', u, t, hS, hS', hd', fun i j => ?_, fun i j => ?_⟩
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simp [hr₁, (g11 _ _).1]
    · simp [hr₁, (g12 _ _).1]
    · simp [hr₁, (g12 _ _).2.1]
    · rw [hr₂, hr₂, hg₂, (g22 _ _).1]
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · rw [hq₁, hq₁, hr₁, hr₁, map_zero, add_zero, (g11 _ _).2, ← hg₁]
      rfl
    · rw [hq₁, hq₂, hr₁]
      simp only [map_zero, LinearMap.zero_apply, mul_zero, add_zero]
      exact (g12 _ _).2.2.1.symm
    · rw [hq₂, hq₁, hr₁]
      simp only [map_zero, LinearMap.zero_apply, mul_zero, add_zero]
      exact (g12 _ _).2.2.2.symm
    · rw [hq₂, hq₂, hr₂, hr₂]
      simp only [map_zero, LinearMap.zero_apply, mul_zero, zero_add]
      rw [hg₂, (g22 _ _).2]

theorem projective_int_of_projective {O M : Type} [CommRing O] [AddCommGroup M] [Module O M] [Module.Free ℤ O]
    [Module.Projective O M] : Module.Projective ℤ M := by
  obtain ⟨s, hs⟩ := Module.projective_def'.1 ‹Module.Projective O M›
  let i : M →ₗ[ℤ] (M →₀ O) := s.toAddMonoidHom.toIntLinearMap
  let p : (M →₀ O) →ₗ[ℤ] M := (Finsupp.linearCombination O id).toAddMonoidHom.toIntLinearMap
  exact Module.Projective.of_split i p (LinearMap.ext fun x => LinearMap.congr_fun hs x)

theorem exists_adapted_siegel_basis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X] (B₀ : X →ₗ[ℤ] X →ₗ[ℤ] ℝ), B₀ ∈ realForms H.bar X → IsPosDef B₀ → ∀ n : ℕ, Module.finrank ℤ X = n → ∀ B ∈ psdCone (bar := H.bar) (X := X), ∃ (b : Module.Basis (Fin n) ℤ X) (d d' : Fin n → ℝ) (u : Matrix (Fin n) (Fin n) ℝ) (B' : X →ₗ[ℤ] X →ₗ[ℤ] ℝ), IsSiegel d u ∧ IsSiegel d' u ∧ (∀ i, 0 < d' i) ∧ B' ∈ realForms H.bar X ∧ (∀ i j, B (b i) (b j) = gram d u i j) ∧ ∀ i j, B' (b i) (b j) = gram d' u i j := by
  intro E _ _ _ H X _ _ _ _ B₀ hB₀ hp₀ n hn B hB
  obtain ⟨X₁, _, _, _, r, B₁, hr, hB₁, hp₁, hBr⟩ := hB
  have : Module.Finite (𝓞 E) X₁ := Module.Finite.of_surjective r hr
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property r LinearMap.id hr
  have hrσ : ∀ y, r (σ y) = y := fun y => LinearMap.congr_fun hσ y
  have : Module.Finite ℤ X := Module.Finite.trans (𝓞 E) X
  have : Module.Finite ℤ X₁ := Module.Finite.trans (𝓞 E) X₁
  have : Module.Projective ℤ X := projective_int_of_projective (O := 𝓞 E)
  have : Module.Projective ℤ X₁ := projective_int_of_projective (O := 𝓞 E)
  have : Module.Free ℤ X := Module.free_of_finite_type_torsion_free'
  have : Module.Free ℤ X₁ := Module.free_of_finite_type_torsion_free'
  let rZ : X →ₗ[ℤ] X₁ := r.toAddMonoidHom.toIntLinearMap
  let σZ : X₁ →ₗ[ℤ] X := σ.toAddMonoidHom.toIntLinearMap
  obtain ⟨b, d, d', u, t, hS, hS', hd', hg, hg'⟩ := exists_siegel_split rZ σZ hrσ B₀ hB₀.1 hp₀ B₁ hB₁.1 hp₁ n hn
  let π : X →ₗ[𝓞 E] X := LinearMap.id - σ ∘ₗ r
  let πZ : X →ₗ[ℤ] X := π.toAddMonoidHom.toIntLinearMap
  refine ⟨b, d, d', u, t • B₀.compl₁₂ πZ πZ + B₁.compl₁₂ rZ rZ, hS, hS', hd', ⟨fun y z => ?_, fun a y z => ?_⟩,
    fun i j => (hBr _ _).trans (hg i j), fun i j => (hg' i j).symm ▸ ?_⟩
  · simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.compl₁₂_apply]
    rw [hB₀.1, hB₁.1]
  · have e₁ : ∀ y, πZ (a • y) = a • πZ y := fun y => π.map_smul a y
    have e₂ : ∀ y, rZ (a • y) = a • rZ y := fun y => r.map_smul a y
    have e₃ : ∀ y, πZ (H.bar a • y) = H.bar a • πZ y := fun y => π.map_smul _ y
    have e₄ : ∀ y, rZ (H.bar a • y) = H.bar a • rZ y := fun y => r.map_smul _ y
    simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.compl₁₂_apply, e₁, e₂, e₃, e₄]
    rw [hB₀.2, hB₁.2]
  · rfl

end GlobalTheory.RedTh
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_snc_coordinates_complexPoint_smoothVariety : ∀ (k : Type) [Field k] [CharZero k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (n : ℕ) (D : TopologicalSpace.Closeds Y) (σ : k →+* ℂ), SmoothOfRelativeDimension n p → ReciprocityTheory.AnForm.R.FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal D) → ∀ x₀ : CxPts p σ, ∃ (a : ℕ) (e : OpenPartialHomeomorph (CxPts p σ) (Fin n → ℂ)), x₀ ∈ e.source ∧ e x₀ = 0 ∧ (∀ j, HolAlong e.source fun x => e x j) ∧ IsHolTo e.target (fun z => (e.symm z).1) ∧ ∀ x ∈ e.source, (x.1 (IsLocalRing.closedPoint ℂ) ∉ D ↔ ∀ j : Fin n, (j : ℕ) < a → e x j ≠ 0) := by
  first | exact @GlobalTheory.SncChart.exists_coords | exact GlobalTheory.SncChart.exists_coords | (intros; apply GlobalTheory.SncChart.exists_coords <;> assumption)
end
