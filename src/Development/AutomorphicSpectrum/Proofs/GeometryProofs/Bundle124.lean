module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle013
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle112
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ReferenceGeometryMultihomogForm
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle001
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle116
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsOrthFull
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle113
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle032
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle115
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle086
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle114
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
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle003
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle098
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle067
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle058
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle076
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle073
import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle033
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle087
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

theorem _root_.GlobalTheory.T.theta_function_unique : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (P : RigLB G) (z : Sp ℂ ⟶ S) (g : ℕ) (a : ArchFrame P z g) (n : ℕ) (s : Out.H0 P.L n), ∃! θ, a.IsFn s θ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.frame_fn_existsUnique | exact GlobalTheory.CompanionTheory.Ar.Sl.frame_fn_existsUnique | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.frame_fn_existsUnique <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.algebraic_constants_in_range : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (Fl : 𝔐.Flag), SplitComps Y → Fl.deg = 1 → ∀ a : Ω, IsAlgebraic ℤ a → a ∈ 𝔐.cst.range := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagConst.isAlgebraic_mem_cst_range | exact GlobalTheory.CompanionTheory.Ar.FlagConst.isAlgebraic_mem_cst_range | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagConst.isAlgebraic_mem_cst_range <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.embeds_generic_of_char_zero : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (κ : Type) (x : κ → Ω), CoordTie ℤ ξ x → EmbedsGeneric ξ x := by
  first | exact @GlobalTheory.CompanionTheory.Ar.EmbedsOfTie.embedsGeneric_of_coordTie | exact GlobalTheory.CompanionTheory.Ar.EmbedsOfTie.embedsGeneric_of_coordTie | (intros; apply GlobalTheory.CompanionTheory.Ar.EmbedsOfTie.embedsGeneric_of_coordTie <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl


theorem _root_.GlobalTheory.T.normalized_degree_gram_det : ∀ (L : Type) [Field L] [NumberField L] (B : HermitianBundle.{0} L) (n : ℕ) (e : Fin n → B.carrier), LinearIndependent (𝓞 L) e → Submodule.span (𝓞 L) (Set.range e) = ⊤ → B.normDegree ⊤ = -(1 / 2) * mean L (fun σ => Real.log ‖B.gramDet σ e‖) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.KeyDegFree.normDegree_top_eq_mean_gramDet | exact GlobalTheory.CompanionTheory.Ar.Sl.KeyDegFree.normDegree_top_eq_mean_gramDet | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.KeyDegFree.normDegree_top_eq_mean_gramDet <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.ExRefEff

theorem _root_.GlobalTheory.T.reference_geometry_multihomog_form : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β₀ : O →+* c.F) (Y : Model Xo c β₀) (G : RefGeo Y), ∃ (β : MRing G.J) (dβ : G.K → ℕ), IsMultiHomog β dβ ∧ β ∉ mCoordIdeal G.y ∧ MvPolynomial.aeval G.y β ≠ 0 ∧ MvPolynomial.aeval G.y β ∈ chartLat G.y (fun κ => (dβ κ : ℤ)) 1 ∧ ∀ p : Cpt G.𝔐.ξ, (∀ r : ℕ, r.Prime → ¬ InFibre G.𝔐.ξ r p) → p.1 ∉ abLocus G.𝔐.t.G → ∀ cc : ∀ k, G.J k, InChart G.𝔐.ξ (fun c' : ∀ k, G.J k => ∏ k, G.y ⟨k, c' k⟩) cc p → ¬ unitAt G.𝔐.ξ p (MvPolynomial.aeval G.y β * ∏ k, G.y ⟨k, cc k⟩ ^ (-((1 : ℕ) * (dβ k : ℤ)))) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.ExRefEff.BdForm.bd_form | exact GlobalTheory.CompanionTheory.Ar.ExRefEff.BdForm.bd_form | (intros; apply GlobalTheory.CompanionTheory.Ar.ExRefEff.BdForm.bd_form <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

theorem _root_.GlobalTheory.T.exists_join_model_dominates : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (Ω' : Type) [Field Ω'] [Algebra o Ω'] (i : Ω →+* Ω') (κ' : Type) [Finite κ'] (w : κ' → Ω'), (∀ a : o, i (algebraMap o Ω a) = algebraMap o Ω' a) → (∃ l, w l ≠ 0) → Subfield.closure (Set.range i ∪ {a | ∃ l l', a = w l / w l'}) = ⊤ → ∃ (M' : PModel o (joinCo i x w)) (f : M'.X ⟶ M.X), Dominates M'.ξ M.ξ f i :=
  @_root_.PositivityTheory.HtPt.Mb.join_exists
end

section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

theorem _root_.GlobalTheory.T.regular_functions_two_components : ∀ {o : Type} [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] {κ : Type} [Finite κ] {x : κ → Ω} (M : PModel o x) {X' : Scheme.{0}} {Ω' : Type} [Field Ω'] (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (i : Ω →+* Ω') (p' : Cpt ξ') (q₁ q₂ : Cpt M.ξ), ((∀ a ∈ regAt M.ξ q₁, i a ∈ regAt ξ' p') ∧ ∀ a ∈ regAt M.ξ q₁, unitAt ξ' p' (i a) → unitAt M.ξ q₁ a) → ((∀ a ∈ regAt M.ξ q₂, i a ∈ regAt ξ' p') ∧ ∀ a ∈ regAt M.ξ q₂, unitAt ξ' p' (i a) → unitAt M.ξ q₂ a) → q₁ = q₂ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Centre.Sep.eq_of_dominated | exact GlobalTheory.CompanionTheory.Ar.Centre.Sep.eq_of_dominated | (intros; apply GlobalTheory.CompanionTheory.Ar.Centre.Sep.eq_of_dominated <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.LogPer

open GroundTheory.Heights₂.Heights.Regular

variable {n a g : ℕ} {Λ : Type} [AddCommGroup Λ]

theorem add_single_mem_logCover (h : a ≤ n) {w : Fin n → ℂ} (hw : w ∈ logCover h) (i : Fin a) :
    w + Pi.single (Fin.castLE h i) (2 * Real.pi * Complex.I) ∈ logCover h := by
  refine ⟨fun j => ?_, fun k hk => ?_⟩
  · by_cases hj : Fin.castLE h j = Fin.castLE h i
    · simpa [hj, Pi.single_apply] using (by simpa [hj] using hw.1 j)
    · simpa [Pi.single_apply, hj] using hw.1 j
  · have hki : k ≠ Fin.castLE h i := by
      rintro rfl
      simp at hk
      omega
    simpa [Pi.single_apply, hki] using hw.2 k hk

theorem expCover_add_single (h : a ≤ n) (w : Fin n → ℂ) (i : Fin a) :
    expCover a (w + Pi.single (Fin.castLE h i) (2 * Real.pi * Complex.I)) = expCover a w := by
  funext k
  by_cases hk : k = Fin.castLE h i
  · subst hk
    have hi : (Fin.castLE h i).val < a := i.2
    simp only [expCover, Pi.add_apply, Pi.single_eq_same, if_pos hi, Complex.exp_add,
      Complex.exp_two_pi_mul_I]
    exact mul_one _
  · simp [expCover, Pi.single_apply, hk]

theorem exists_mem_logCover (h : a ≤ n) : ∃ w : Fin n → ℂ, w ∈ logCover h := by
  refine ⟨fun k => if k.val < a then -1 else 0, fun i => ?_, fun k hk => ?_⟩
  · have hi : (Fin.castLE h i).val < a := i.2
    simp only [if_pos hi]
    simp
  · simp [not_lt.2 hk]

theorem monodromy_preserves_form (L : Flat.LogPeriods n a g Λ) (i : Fin a) (x y : Λ) :
    L.E (L.T i x) (L.T i y) = L.E x y := by
  obtain ⟨w, hw⟩ := exists_mem_logCover L.a_le
  have h1 := L.im _ (add_single_mem_logCover L.a_le hw i) x y
  rw [L.mono i w hw, L.mono i w hw, expCover_add_single, L.im w hw] at h1
  exact_mod_cast h1

theorem T_bijective (L : Flat.LogPeriods n a g Λ) (i : Fin a) : Function.Bijective (L.T i) := by
  haveI := L.fin
  let e : Λ ≃ₗ[ℤ] Module.Dual ℤ Λ := LinearEquiv.ofBijective L.E L.unimod
  let S : Λ →ₗ[ℤ] Λ := e.symm.toLinearMap ∘ₗ (L.T i).dualMap ∘ₗ e.toLinearMap
  have hE : ∀ x y, L.E (S x) y = L.E x (L.T i y) := by
    intro x y
    have h1 : e (S x) = (L.T i).dualMap (e x) := by simp [S]
    exact congrArg (fun f : Module.Dual ℤ Λ => f y) h1
  have hST : ∀ x, S (L.T i x) = x := fun x =>
    L.unimod.1 (LinearMap.ext fun y => by rw [hE, monodromy_preserves_form])
  have hSs : Function.Surjective S := fun x => ⟨_, hST x⟩
  have hSi : Function.Injective S := OrzechProperty.injective_of_surjective_endomorphism S hSs
  exact ⟨fun x y h => by rw [← hST x, ← hST y, h], fun y => ⟨S y, hSi (hST (S y))⟩⟩

theorem exists_conj_logPeriods : ∀ (n a g : ℕ) (Λ : Type) [AddCommGroup Λ] (L' : Flat.LogPeriods n a g Λ),
    ∃ L : Flat.LogPeriods n a g Λ, (∀ w x, L.P w x = star (L'.P (star w) x)) ∧
      ∀ z, L.H z = (L'.H (star z)).map (starRingEnd ℂ) := by
  intro n a g Λ _ L'
  exact ⟨ConjPeriods.conj L' (T_bijective L'), fun _ _ => rfl, fun _ => rfl⟩

end GlobalTheory.CompanionTheory.Ar.Flat.LogPer
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.TorusUnif
open scoped CategoryTheory.Obj


theorem _root_.GlobalTheory.T.hermitian_square_norm_gram : ∀ (L : Type) [Field L] [NumberField L] (B : GroundTheory.Heights₂.Heights.HermitianBundle.{0} L) (σ : L →+* ℂ) (n : ℕ)
    (ε : Fin n → B.carrier) (Γ : Matrix (Fin n) (Fin n) ℂ),
    (∀ a b, Γ a b = (B.metric.form σ).inner ((1 : GroundTheory.Heights₂.Heights.ComplexAt σ) ⊗ₜ[𝓞 L] ε a)
      ((1 : GroundTheory.Heights₂.Heights.ComplexAt σ) ⊗ₜ[𝓞 L] ε b)) → ∀ w : Fin n → ℂ,
    sqAt B σ (∑ a, GroundTheory.Heights₂.Heights.ComplexAt.ofComplex σ (w a) ⊗ₜ[𝓞 L] ε a) = (star w ⬝ᵥ (Γ *ᵥ w)).re := by
  first | exact @GlobalTheory.CompanionTheory.Ar.TorusUnif.sqAt_sum_eq_gram | exact GlobalTheory.CompanionTheory.Ar.TorusUnif.sqAt_sum_eq_gram | (intros; apply GlobalTheory.CompanionTheory.Ar.TorusUnif.sqAt_sum_eq_gram <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun

theorem _root_.GlobalTheory.T.flag_frames_generic_model_right : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (κ : Type) [Finite κ] (x : κ → Ω) (S : Type) [Fintype S] (r : S → ℕ) (V : S → Submodule Ω E) (L : S → Lat ξ E) (m n : S → ℕ) (φ : ∀ s, Fin (n s) → Module.Dual Ω E) (c : ∀ s, Fin (r s) → E) (X' : Scheme.{0}) (ξ' : Spec (CommRingCat.of (GenField Ω r)) ⟶ X') (f : X' ⟶ X), CoordTie ℤ ξ x → (∀ q : X, genPt ξ ⤳ q) → (∀ s, (L s).IsVB (r s) (V s)) → (∀ s, IsTwistGen ξ x (L s) (m s) (φ s)) → (∀ s, LinearIndependent Ω (c s) ∧ Submodule.span Ω (Set.range (c s)) = V s) → CoordTie ℤ ξ' (flagCoord κ x φ c) → (∀ q : X', genPt ξ' ⤳ q) → Dominates ξ' ξ f (algebraMap Ω (GenField Ω r)) → (∀ (p' : Cpt ξ') (c₁ : κ) (h : genPt ξ ⤳ f p'.1), InChart ξ x c₁ ⟨f p'.1, h⟩ ↔ InChart ξ' (fun k => algebraMap Ω (GenField Ω r) (x k)) c₁ p') → Smooth f := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.flag_smooth | exact GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.flag_smooth | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.flag_smooth <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights


theorem _root_.GlobalTheory.T.val_at_gen_independent_choice : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (K : Type) [Fintype K] (J : K → Type)
    (y : (Σ k, J k) → Ω) (z : Sp ℂ ⟶ X) (w : (Σ k, J k) → ℂ) (a : K → ℤ) (e₀ τ : Ω) (c₀ c₁ : (k : K) → J k) (u u' : ℂ),
    IsCptGen ξ → e₀ ≠ 0 → CoordsAt ξ y z w → (∀ k, w ⟨k, c₀ k⟩ ≠ 0) → (∀ k, w ⟨k, c₁ k⟩ ≠ 0) →
    ValAt ξ z (τ / gen y a e₀ c₀) u → ValAt ξ z (τ / gen y a e₀ c₁) u' →
    u * ∏ k, w ⟨k, c₀ k⟩ ^ a k = u' * ∏ k, w ⟨k, c₁ k⟩ ^ a k := by
  first | exact @GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.gen_chart_change | exact GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.gen_chart_change | (intros; apply GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.gen_chart_change <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.Cusp.FamEx

theorem _root_.GlobalTheory.T.constants_value_over_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (z : Sp ℂ ⟶ 𝔐.X) (κ : c.F →+* ℂ) (p : Sp ℂ ⟶ Xo.X), IsOver 𝔐 z κ p → ∀ x : c.F, ValAt 𝔐.ξ z (𝔐.cst x) (κ x) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.val_cst | exact GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.val_cst | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.val_cst <;> assumption)
end
