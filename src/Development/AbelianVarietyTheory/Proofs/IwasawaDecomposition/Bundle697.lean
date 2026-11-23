module

public import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle008
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle070
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle428
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle638
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle399
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLinearEquivLift
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle048
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle022
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HolDifferentiableAt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle667
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle683
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqAddOfRedVEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle685
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle007
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle682
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532

@[expose] public section

section

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical

namespace GlobalTheory.GrassTop

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

noncomputable def rootToFlag (H : Host E) (Dw : Datum H) (x : Root Dw.mult) :
    MvPolynomial (GlobalTheory.AllWt.Psi H × Fin (Dw.p + Dw.q)) ℝ :=
  if h : x.1 (H.rt : E) = H.rt0 then
    X (⟨x.1, h⟩, ⟨x.2, by have := x.2.isLt; simp only [Datum.mult, h, if_true] at this; omega⟩)
  else
    -X (⟨conjEmb x.1, GlobalTheory.AllWt.conj_mem h⟩,
      ⟨Dw.p + (Dw.q - 1 - x.2), by have := x.2.isLt; simp only [Datum.mult, h, if_false] at this; omega⟩)

noncomputable def rho (H : Host E) (Dw : Datum H) :
    MvPolynomial (Root Dw.mult) ℝ →ₐ[ℝ] MvPolynomial (GlobalTheory.AllWt.Psi H × Fin (Dw.p + Dw.q)) ℝ :=
  aeval (rootToFlag H Dw)

noncomputable def intGr (H : Host E) (Dw : Datum H) (Q : MvPolynomial ((E →+* ℂ) × ℕ) ℝ) : ℝ :=
  Formalism.DegreeFormula.degFl (GlobalTheory.AllWt.Psi H) (Dw.p + Dw.q)
            (rho H Dw (chernRoots Dw.mult Q * rootDiscr Dw.mult)) /
    ((Dw.p.factorial * Dw.q.factorial : ℝ) ^ Fintype.card (GlobalTheory.AllWt.Psi H))

noncomputable def relIdeal (H : Host E) (Dw : Datum H) : Ideal (MvPolynomial ((E →+* ℂ) × ℕ) ℝ) :=
  Ideal.span ((Set.range fun τ : E →+* ℂ => (X (τ, 0) - 1 : MvPolynomial ((E →+* ℂ) × ℕ) ℝ)) ∪
    {P | ∃ (τ : E →+* ℂ) (k : ℕ), Dw.mult τ < k ∧ P = X (τ, k)} ∪
    {P | ∃ (τ : GlobalTheory.AllWt.Psi H) (k : ℕ), 1 ≤ k ∧
      P = ∑ a ∈ Finset.range (k + 1),
        C ((-1 : ℝ) ^ (k - a)) * X (τ.1, a) * X (conjEmb τ.1, k - a)})

end GlobalTheory.GrassTop
end

section

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.LieBase
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts
open scoped Topology
open ReciprocityTheory.L2DbarEstimates (V)

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Filter Topology

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HolCoordEv

theorem eventually_differentiableAt_of_forms {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {g : ℕ}
    (W : V → Fin g → ℂ) (b₀ : V) (H : ∀ w : Fin g → ℂ, (∀ L : V → ((Fin g → ℂ) →L[ℂ] ℂ),
      (∀ᶠ b in 𝓝 b₀, DifferentiableAt ℂ L b) → (∀ᶠ b in 𝓝 b₀, DifferentiableAt ℂ (fun b => L b (W b)) b) →
        L b₀ w = 0) → w = 0) : ∀ᶠ b in 𝓝 b₀, DifferentiableAt ℂ W b := by
  let M : Submodule ℂ (Module.Dual ℂ (Fin g → ℂ)) :=
    { carrier := {l | ∃ L : V → ((Fin g → ℂ) →L[ℂ] ℂ), (∀ᶠ b in 𝓝 b₀, DifferentiableAt ℂ L b) ∧
        (∀ᶠ b in 𝓝 b₀, DifferentiableAt ℂ (fun b => L b (W b)) b) ∧ ∀ w, L b₀ w = l w}
      add_mem' := by
        rintro l l' ⟨L, h1, h2, h3⟩ ⟨L', h1', h2', h3'⟩
        refine ⟨fun b => L b + L' b, ?_, ?_, fun w => by simp [h3, h3']⟩
        · filter_upwards [h1, h1'] with b hb hb' using hb.add hb'
        · filter_upwards [h2, h2'] with b hb hb' using hb.add hb'
      zero_mem' := ⟨fun _ => 0, Eventually.of_forall fun _ => differentiableAt_const _,
        Eventually.of_forall fun _ => by simp, by simp⟩
      smul_mem' := by
        rintro c l ⟨L, h1, h2, h3⟩
        refine ⟨fun b => c • L b, ?_, ?_, fun w => by simp [h3]⟩
        · filter_upwards [h1] with b hb using hb.const_smul c
        · filter_upwards [h2] with b hb using hb.const_smul c }
  have hM : M = ⊤ := by
    have h0 : M.dualCoannihilator = ⊥ := by
      refine eq_bot_iff.2 fun w hw => H w fun L h1 h2 => ?_
      exact (Submodule.mem_dualCoannihilator w).1 hw (L b₀).toLinearMap ⟨L, h1, h2, fun _ => rfl⟩
    rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := M), h0, Submodule.dualAnnihilator_bot]
  have hj : ∀ j : Fin g, LinearMap.proj j ∈ M := fun j => hM ▸ Submodule.mem_top
  choose L h1 h2 h3 using hj
  let J : V → ((Fin g → ℂ) →L[ℂ] (Fin g → ℂ)) := fun b => ContinuousLinearMap.pi fun j => L j b
  have hJ : ∀ᶠ b in 𝓝 b₀, DifferentiableAt ℂ J b := by
    filter_upwards [eventually_all.2 h1] with b hb
    exact (ContinuousLinearMap.piEquivL ℂ (Fin g → ℂ) (fun _ : Fin g => ℂ)).differentiableAt.comp b
      (differentiableAt_pi.2 hb)
  have hJ0 : IsUnit (J b₀) := by
    have : J b₀ = 1 := by
      ext1 w
      funext j
      exact h3 j w
    rw [this]; exact isUnit_one
  have hU : ∀ᶠ b in 𝓝 b₀, IsUnit (J b) :=
    hJ.self_of_nhds.continuousAt.eventually (Units.isOpen.mem_nhds hJ0)
  filter_upwards [hJ, hU, eventually_all.2 h2] with b hJb hUb hWb
  have hW : DifferentiableAt ℂ (fun b => J b (W b)) b := differentiableAt_pi.2 hWb
  refine ((hJb.inverse hUb).clm_apply hW).congr_of_eventuallyEq ?_
  filter_upwards [hJb.continuousAt.eventually (Units.isOpen.mem_nhds hUb)] with b' hb'
  have := congrArg (fun T : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ) => T (W b')) (Ring.inverse_mul_cancel _ hb')
  exact this.symm


open GlobalTheory.TangentOrigin GlobalTheory.HolLieFrame in
theorem exists_hol_snd_ev {V R : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [CommRing R] {X : Scheme.{0}}
    (ψ : Sp (DualNumber R) ⟶ X) (ev : V → (R →+* ℂ)) (b₀ : V)
    (hev : ∀ c, ∀ᶠ b in 𝓝 b₀, DifferentiableAt ℂ (fun b => ev b c) b)
    (U : X.Opens) (f : Γ(X, U)) (h₀ : ⊤ ≤ (spMap (Chart.dualMapR (ev b₀)) ≫ ψ) ⁻¹ᵁ U) :
    ∃ F : V → ℂ, (∀ᶠ b in 𝓝 b₀, DifferentiableAt ℂ F b) ∧ ∀ᶠ b in 𝓝 b₀,
      ∃ h : ⊤ ≤ (spMap (Chart.dualMapR (ev b)) ≫ ψ) ⁻¹ᵁ U, (evalPt _ U h f).snd = F b := by
  have h₁ : ⊤ ≤ (spMap (fstC.comp (Chart.dualMapR (ev b₀))) ≫ ψ) ⁻¹ᵁ U := by
    have := (top_le_preimage_iff _ U).1 h₀
    rwa [← Category.assoc, ← Spec.map_comp] at this
  obtain ⟨r, a, hr, H⟩ := exists_fraction ψ U f _ h₁
  have hf : ∀ b (x : DualNumber R), (Chart.dualMapR (ev b) x).fst = ev b x.fst := fun b x => by simp [Chart.dualMapR]
  have hs : ∀ b (x : DualNumber R), (Chart.dualMapR (ev b) x).snd = ev b x.snd := fun b x => by simp [Chart.dualMapR]
  have hr' : ev b₀ r.fst ≠ 0 := (hf b₀ r) ▸ hr
  have hne : ∀ᶠ b in 𝓝 b₀, ev b r.fst ≠ 0 := (hev r.fst).self_of_nhds.continuousAt.eventually_ne hr'
  refine ⟨fun b => (ev b a.snd - ev b a.fst * (ev b r.fst)⁻¹ * ev b r.snd) * (ev b r.fst)⁻¹, ?_, ?_⟩
  · filter_upwards [hev a.snd, hev a.fst, hev r.fst, hev r.snd, hne] with b h1 h2 h3 h4 h5
    exact (h1.sub ((h2.mul (h3.inv h5)).mul h4)).mul (h3.inv h5)
  filter_upwards [hne] with b hb
  obtain ⟨h, e⟩ := H _ (Chart.dualMapR (ev b)) (TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (by rw [hf]; exact hb.isUnit))
  refine ⟨h, ?_⟩
  have e1 := congrArg TrivSqZeroExt.fst e
  have e2 := congrArg TrivSqZeroExt.snd e
  rw [TrivSqZeroExt.fst_mul, hf, hf] at e1
  rw [DualNumber.snd_mul, hf, hs, hs] at e2
  rw [← e1, ← e2]
  field_simp
  ring

end GlobalTheory.HolCoordEv

namespace GlobalTheory.HolCoordEv

open GlobalTheory.ShFam.Hor.LogCh
open ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows (isDerivAt0_unique)

theorem eventually_differentiableAt_dir {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Z : Model Xo c β)
    (σ : c.F →+* ℂ) {g : ℕ} {ty : Fin g → (E →+* ℂ)}
    (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (i : Fin Fu.n) {n : ℕ}
    {B : Set (Fin n → ℂ)} (hB : IsOpen B) {P : (Fin n → ℂ) → ((Fu.Di i).La →+ (Fin g → ℂ))}
    {p : (Fin n → ℂ) → (Sp ℂ ⟶ Xo.XF c)}
    (hu : ∀ b, Fu.u i (P b) = p b ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom))
    (hP : ∀ b, IsPeriod (Fu.Di i) ty (P b)) (hPd : ∀ a, DifferentiableOn ℂ (fun b => P b a) B)
    (hs : ∀ b, p b ≫ pullback.snd _ _ = spMap σ) {R : Type} [CommRing R] (v : Sp (DualNumber R) ⟶ Z.t.G.left)
    (ev : (Fin n → ℂ) → (R →+* ℂ)) {b₀ : Fin n → ℂ} (hb₀ : b₀ ∈ B)
    (hev : ∀ t, ∀ᶠ b in 𝓝 b₀, DifferentiableAt ℂ (fun b => ev b t) b) (W : (Fin n → ℂ) → Fin g → ℂ)
    (hW : ∀ᶠ b in 𝓝 b₀, IsDerivAt0 (fun z => liftEx Z Fu (p b) i (P b) (hu b) z ≫ Z.m.φ) (W b)
      (spMap (Formalism.L2.Pj.dualMap (ev b)) ≫ v)) :
    ∀ᶠ b in 𝓝 b₀, DifferentiableAt ℂ W b := by
  classical
  have h1 := Fu.hol i n B P hB ⟨fun b _ => hP b, hPd⟩
  have hp : IsHolTo B p := TrueCx.TorHolo.isHolTo_of_fst _ _ hB (spMap σ) hs
    (LocLift.isHolTo_congr h1.1 fun b _ => (hu b).symm)
  have h2 := TrueCx.TorFrHolo.isHolTo_lift Z.m0.toSABMap.cart.1 hB (fun b z => (Fu.ex i (P b) z).left) p h1.2 hp
    (fun b z => by rw [Over.w (Fu.ex i (P b) z), ← hu b]; rfl)
  have hFt : IsHolTo (B ×ˢ Set.univ) (fun bz : (Fin n → ℂ) × (Fin g → ℂ) =>
      liftEx Z Fu (p bz.1) i (P bz.1) (hu bz.1) bz.2 ≫ Z.m.φ) :=
    ReciprocityTheory.ChartRestriction.G.PullbackSections.isHolTo_comp h2 Z.m.φ
  have hExp : IsExpAt Z.t (p b₀ ≫ Z.jQ ≫ genι Z)
      (pushEx Z Fu (p b₀) i (P b₀) (p b₀ ≫ Z.jQ ≫ genι Z) (hu b₀) rfl) :=
    isExpAt_pushEx E H Dw l Xo c O β Z g ty _ Fu (p b₀) i (P b₀) (p b₀ ≫ Z.jQ ≫ genι Z) (hu b₀) rfl (hP b₀)
  have hW' : ∀ᶠ b in 𝓝 b₀, IsDerivAt0 (fun z => liftEx Z Fu (p b) i (P b) (hu b) z ≫ Z.m.φ) (W b)
      (spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR (ev b)) ≫ v) := by
    filter_upwards [hW] with b hb
    rwa [← HolFrameMatrix.dualMap_eq]
  refine eventually_differentiableAt_of_forms W b₀ fun w hw => ?_
  have hw' : ∀ (O : Z.t.G.left.Opens) (f : Γ(Z.t.G.left, O)),
      ⊤ ≤ (liftEx Z Fu (p b₀) i (P b₀) (hu b₀) 0 ≫ Z.m.φ) ⁻¹ᵁ O →
      fderiv ℂ (fun z => valAt' (liftEx Z Fu (p b₀) i (P b₀) (hu b₀) z ≫ Z.m.φ) O f) 0 w = 0 := by
    intro O f hO
    refine hw (fun b => fderiv ℂ (fun z => valAt' (liftEx Z Fu (p b) i (P b) (hu b) z ≫ Z.m.φ) O f) 0) ?_ ?_
    · have hc : ContinuousAt (fun b : Fin n → ℂ => (b, (0 : Fin g → ℂ))) b₀ :=
        continuousAt_id.prodMk continuousAt_const
      filter_upwards [hc.preimage_mem_nhds ((hFt O f).1.mem_nhds ⟨⟨hb₀, trivial⟩, hO⟩)] with b hb
      exact HolLieFrame.differentiableAt_fderiv
        (e := fun b z => liftEx Z Fu (p b) i (P b) (hu b) z ≫ Z.m.φ) hFt hb.1.1 O f hb.2
    · obtain ⟨Fn, hF, hF'⟩ := exists_hol_snd_ev v ev b₀ hev O f
        ((TangentOrigin.top_le_preimage_iff _ O).2 (by rw [hW'.self_of_nhds.1]; exact hO))
      filter_upwards [hF, (hF'.and hW').eventually_nhds] with b hFb hnear
      refine hFb.congr_of_eventuallyEq ?_
      filter_upwards [hnear] with b' ⟨⟨h, e'⟩, hd⟩
      exact (hd.2 O h f).symm.trans e'
  have d₁ := LocalLift.isDerivAt0_const (fun z => liftEx Z Fu (p b₀) i (P b₀) (hu b₀) z ≫ Z.m.φ) w hw'
  have d₀ := LocalLift.isDerivAt0_const (fun z => liftEx Z Fu (p b₀) i (P b₀) (hu b₀) z ≫ Z.m.φ) 0
    fun _ _ _ => map_zero _
  obtain ⟨u, ⟨hut, hud⟩, -⟩ := hExp.2.1 0
  have hu0 := isDerivAt0_unique hud d₀
  obtain ⟨w', -, hw''⟩ := hExp.2.2 u hut
  have a1 : w = w' := hw'' w (by rw [hu0]; exact d₁)
  have a0 : (0 : Fin g → ℂ) = w' := hw'' 0 hud
  exact a1.trans a0.symm

end GlobalTheory.HolCoordEv
end
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

noncomputable section

namespace GlobalTheory.PolCell

variable {O : Type} [CommRing O] {bar : O → O} {φ : InvFun O} {X X₁ : Type} [AddCommGroup X] [Module O X]
  [Module.Finite O X] [AddCommGroup X₁] [Module O X₁] [Module.Finite O X₁] {m : ℕ}

theorem StrictWith.mul {N t : ℕ} (ht : 0 < t) {ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ}
    {u : Fin m → LinearMap.BilinForm ℤ X} (h : StrictWith bar φ N ℓ u) :
    StrictWith bar φ (t * N) ((t : ℤ) • ℓ) u := by
  obtain ⟨h1, h2, h3⟩ := h
  have ht' : (0 : ℝ) < t := by exact_mod_cast ht
  refine ⟨fun i => ?_, fun β hβ hp => ?_, fun β hβ hp he => h3 β hβ hp ?_⟩
  · simp only [LinearMap.smul_apply, smul_eq_mul, Int.cast_mul, Int.cast_natCast, h1 i, Nat.cast_mul]; ring
  · have := mul_le_mul_of_nonneg_left (h2 β hβ hp) ht'.le
    simp only [LinearMap.smul_apply, smul_eq_mul, Int.cast_mul, Int.cast_natCast, Nat.cast_mul]
    linarith
  · simp only [LinearMap.smul_apply, smul_eq_mul, Int.cast_mul, Int.cast_natCast, Nat.cast_mul] at he
    have : (t : ℝ) * (N * φ.evalZ β) = t * ℓ β := by linarith
    exact mul_left_cancel₀ ht'.ne' this

theorem StrictWith.of_pull {N : ℕ} {r : X →ₗ[O] X₁} (hr : Function.Surjective r) {ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ}
    {u : Fin m → LinearMap.BilinForm ℤ X₁} (h : StrictWith bar φ N ℓ fun i => pull r (u i)) :
    StrictWith bar φ N (ℓ ∘ₗ { toFun := pull r, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }) u := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun i => (h1 i).trans (by rw [evalZ_pull φ hr]), fun β hβ hp => ?_, fun β hβ hp he => ?_⟩
  · rw [← evalZ_pull φ hr]
    exact h2 _ (pull_mem r hβ) fun y => hp _
  · rw [← evalZ_pull φ hr] at he
    obtain ⟨k, c, hk, hc⟩ := h3 _ (pull_mem r hβ) (fun y => hp _) he
    refine ⟨k, c, hk, LinearMap.ext₂ fun a b => ?_⟩
    obtain ⟨a, rfl⟩ := hr a
    obtain ⟨b, rfl⟩ := hr b
    simpa [LinearMap.sum_apply] using LinearMap.congr_fun₂ hc a b

end GlobalTheory.PolCell


open Classical in
theorem GlobalTheory.PolCell.exists_common_den : ∀ (X : Type) [AddCommGroup X] [Module.Finite ℤ X] (φ : InvFun ℤ),
    IsPolFanOn (id : ℤ → ℤ) φ X → ∃ N : ℕ, 0 < N ∧ ∀ B ∈ psdCone (bar := (id : ℤ → ℤ)) (X := X), ∃ (m : ℕ)
      (u : Fin m → LinearMap.BilinForm ℤ X) (w : (X × X) →₀ ℤ), IsCone (id : ℤ → ℤ) φ u ∧
      StrictWith (id : ℤ → ℤ) φ N (linW w) u ∧ B ∈ rcone u := by
  intro X _ _ φ hφ
  obtain ⟨S, hS, hSc⟩ := hφ.finite
  haveI : Finite S := hS.to_subtype
  let K := Σ m : Fin (Nat.card S + 1), (Fin m → S)
  haveI : Fintype K := Fintype.ofFinite K
  let D : K → ℕ := fun k =>
    if h : IsCone (id : ℤ → ℤ) φ (fun i => ((k.2 i : S) : LinearMap.BilinForm ℤ X)) then Classical.choose h.strict else 1
  have hD : ∀ k, 0 < D k := fun k => by
    simp only [D]
    split_ifs with h
    · exact (Classical.choose_spec (Classical.choose_spec h.strict)).1
    · exact one_pos
  refine ⟨∏ k, D k, Finset.prod_pos fun k _ => hD k, fun B hB => ?_⟩
  obtain ⟨m, γ, c, hγ, hc, rfl⟩ := hφ.cover B hB
  obtain ⟨e, he⟩ := hSc m γ hγ
  have hγ' := hγ.pull_equiv e
  have hm : m < Nat.card S + 1 := by
    have := Nat.card_le_card_of_injective (fun i : Fin m => (⟨_, he i⟩ : S))
      (fun i j h => hγ'.injective (congrArg Subtype.val h))
    rw [Nat.card_fin] at this
    exact Nat.lt_succ_of_le this
  let k : K := ⟨⟨m, hm⟩, fun i => ⟨_, he i⟩⟩
  have hk : IsCone (id : ℤ → ℤ) φ (fun i => ((k.2 i : S) : LinearMap.BilinForm ℤ X)) := hγ'
  have hDk : D k = Classical.choose hk.strict := dif_pos hk
  obtain ⟨ℓ, -, hℓ⟩ := Classical.choose_spec hk.strict
  obtain ⟨t, ht⟩ : D k ∣ ∏ k, D k := Finset.dvd_prod_of_mem D (Finset.mem_univ k)
  have ht0 : 0 < t := by
    rcases Nat.eq_zero_or_pos t with h | h
    · have := Finset.prod_pos fun k (_ : k ∈ Finset.univ) => hD k
      rw [ht, h, mul_zero] at this; exact absurd this (lt_irrefl 0)
    · exact h
  have h1 : StrictWith (id : ℤ → ℤ) φ (t * D k) ((t : ℤ) • ℓ) fun i => pull e.toLinearMap (γ i) := by
    rw [hDk]; exact StrictWith.mul ht0 hℓ
  have h2 := StrictWith.of_pull e.surjective h1
  obtain ⟨w, hw⟩ := exists_linW_eq X (((t : ℤ) • ℓ) ∘ₗ
    { toFun := pull e.toLinearMap, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl })
  refine ⟨m, γ, w, hγ, ?_, c, hc, rfl⟩
  rw [hw, ht, mul_comm]
  exact h2
end
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan

theorem cellMult_pos {O : Type} [CommRing O] [Module.Finite ℤ O] (bar : O → O) {X : Type} [AddCommGroup X] [Module O X]
    [Module.Finite O X] {m : ℕ} (δ : Fin m → balForms bar X) : 0 < cellMult bar δ := by
  haveI : Module.Finite ℤ X := Module.Finite.trans O X
  unfold cellMult
  set M := balForms bar X ⧸ Submodule.span ℤ (Set.range δ)
  set T := Submodule.torsion ℤ M
  haveI : IsNoetherian ℤ (LinearMap.BilinForm ℤ X) := inferInstance
  haveI : Module.Finite ℤ M := inferInstance
  haveI : IsNoetherian ℤ M := inferInstance
  haveI : IsNoetherian ℤ T := isNoetherian_of_submodule_of_noetherian ℤ M T inferInstance
  haveI : Module.Finite ℤ T := ⟨IsNoetherian.noetherian ⊤⟩
  haveI : AddGroup.FG T := by
    rw [← Module.Finite.iff_addGroup_fg]; infer_instance
  haveI : Finite T := by
    apply AddCommGroup.finite_of_fg_torsion
    rintro ⟨x, hx⟩
    obtain ⟨⟨a, ha⟩, hax⟩ := hx
    refine (isOfFinAddOrder_iff_zsmul_eq_zero).2 ⟨a, nonZeroDivisors.ne_zero ha, ?_⟩
    ext
    exact hax
  exact Nat.card_pos

end GlobalTheory.PolFan
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan

theorem isPrim_eq_one_of_smul_eq : ∀ {O : Type} [CommRing O] (bar : O → O) {X : Type} [AddCommGroup X] [Module O X] (β : LinearMap.BilinForm ℤ X) (hβ : β ∈ balForms bar X), IsPrim bar (⟨β, hβ⟩ : balForms bar X) →
  ∀ (k : ℕ) (β' : LinearMap.BilinForm ℤ X), (k : ℤ) • β' = β → k = 1 := by
  intro O _ bar X _ _ β hβ hp k β' hk
  rcases Nat.eq_zero_or_pos k with rfl | hpos
  · exfalso
    have h0 : (⟨β, hβ⟩ : balForms bar X) = 0 := Subtype.ext (by simpa using hk.symm)
    rw [h0] at hp
    exact not_isPrim_zero hp
  have hk0 : (k : ℤ) ≠ 0 := by exact_mod_cast hpos.ne'
  have hval : ∀ y z, (k : ℤ) * β' y z = β y z := by
    intro y z
    rw [← hk]
    simp
  have hb : β' ∈ balForms bar X := by
    refine ⟨fun y z => ?_, fun a y z => ?_⟩
    · apply mul_left_cancel₀ hk0
      rw [hval, hval]
      exact hβ.1 y z
    · apply mul_left_cancel₀ hk0
      rw [hval, hval]
      exact hβ.2 a y z
  refine hp k ⟨β', hb⟩ (Subtype.ext ?_)
  simp [← hk]

end GlobalTheory.PolFan
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan

theorem balForms_zsmul_cancel {O : Type} [CommRing O] {bar : O → O} {X : Type} [AddCommGroup X] [Module O X]
    {g : ℤ} (hg : g ≠ 0) {a b : balForms bar X} (h : g • a = g • b) : a = b := by
  apply Subtype.ext
  refine LinearMap.ext₂ fun y z => ?_
  have h2 := LinearMap.congr_fun₂ (congrArg Subtype.val h) y z
  simp only [Submodule.coe_smul, LinearMap.smul_apply, smul_eq_mul] at h2
  exact mul_left_cancel₀ hg h2

theorem isPrim_ray_eq : ∀ {O : Type} [CommRing O] (bar : O → O) {X : Type} [AddCommGroup X] [Module O X]
    (β β' : balForms bar X) (p r : ℕ), IsPrim bar β → IsPrim bar β' → 0 < p → 0 < r → p • β = r • β' → β = β' := by
  intro O _ bar X _ _ β β' p r hβ hβ' hp hr h
  set g := Nat.gcd p r with hgdef
  have hg : 0 < g := Nat.gcd_pos_of_pos_left r hp
  obtain ⟨p₁, hp₁⟩ : g ∣ p := Nat.gcd_dvd_left p r
  obtain ⟨r₁, hr₁⟩ : g ∣ r := Nat.gcd_dvd_right p r
  have hcop : Nat.Coprime p₁ r₁ := by
    have := Nat.coprime_div_gcd_div_gcd (m := p) (n := r) hg
    rw [← hgdef] at this
    have e1 : p / g = p₁ := by rw [hp₁, Nat.mul_div_cancel_left _ hg]
    have e2 : r / g = r₁ := by rw [hr₁, Nat.mul_div_cancel_left _ hg]
    rwa [e1, e2] at this

  have h1 : (p₁ : ℤ) • β = (r₁ : ℤ) • β' := by
    apply balForms_zsmul_cancel (g := (g : ℤ)) (by exact_mod_cast hg.ne')
    rw [smul_smul, smul_smul, ← Nat.cast_mul, ← Nat.cast_mul, ← hp₁, ← hr₁, natCast_zsmul, natCast_zsmul]
    exact h

  have hbez : (p₁ : ℤ) * Nat.gcdA p₁ r₁ + (r₁ : ℤ) * Nat.gcdB p₁ r₁ = 1 := by
    rw [← Nat.gcd_eq_gcd_ab, hcop.gcd_eq_one]; rfl
  set u := Nat.gcdA p₁ r₁
  set v := Nat.gcdB p₁ r₁
  have hr1 : r₁ = 1 := by
    apply hβ r₁ (u • β' + v • β)
    calc β = ((p₁ : ℤ) * u + (r₁ : ℤ) * v) • β := by rw [hbez, one_smul]
      _ = u • ((p₁ : ℤ) • β) + (r₁ : ℤ) • (v • β) := by
          rw [add_smul, smul_smul, smul_smul, mul_comm (p₁ : ℤ) u]
      _ = r₁ • (u • β' + v • β) := by
          rw [h1, smul_smul, mul_comm u, ← smul_smul, ← smul_add, natCast_zsmul]
  have hp1 : p₁ = 1 := by
    apply hβ' p₁ (u • β' + v • β)
    calc β' = ((p₁ : ℤ) * u + (r₁ : ℤ) * v) • β' := by rw [hbez, one_smul]
      _ = (p₁ : ℤ) • (u • β') + v • ((r₁ : ℤ) • β') := by
          rw [add_smul, smul_smul, smul_smul, mul_comm (r₁ : ℤ) v]
      _ = p₁ • (u • β' + v • β) := by
          rw [← h1, smul_smul v, mul_comm v, ← smul_smul, ← smul_add, natCast_zsmul]
  rw [hr1, hp1] at h1
  simpa using h1

end GlobalTheory.PolFan
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

theorem _root_.GlobalTheory.T.cell_generator_mem_cone_of_smul_combination : ∀ {O : Type} [CommRing O] (bar : O → O) (φ : InvFun O) {X : Type} [AddCommGroup X] [Module O X]
    [Module.Finite O X] {m m' : ℕ} (δ : Fin m → LinearMap.BilinForm ℤ X) (γ : Fin m' → LinearMap.BilinForm ℤ X)
    (i : Fin m) (k : ℕ) (a : Fin m' → ℕ), IsCell bar φ δ → IsCell bar φ γ → 0 < k → k • δ i = ∑ j, a j • γ j →
    ∀ j, 0 < a j → ∃ (k' : ℕ) (b : Fin m → ℕ), 0 < k' ∧ k' • γ j = ∑ l, b l • δ l := by
  first | exact @GlobalTheory.PolFan.cell_gen_mem_cone_of_smul | exact GlobalTheory.PolFan.cell_gen_mem_cone_of_smul | (intros; apply GlobalTheory.PolFan.cell_gen_mem_cone_of_smul <;> assumption)
end
