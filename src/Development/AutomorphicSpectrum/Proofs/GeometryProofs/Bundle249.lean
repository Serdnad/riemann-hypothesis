module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle006
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle007
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateWeilPullback
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsLatFamilyCongr
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle006
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle008
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle067
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle017
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle248
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.hodge_tate_weil_pullback : ∀ (X : Scheme.{0}) [IsLocallyNoetherian X] (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X), IsCptGen ξ → Flat.NormalCpt ξ → ∀ (G : Over X) [GrpObj G], IsSemiAbelian G → ∀ (L : LB G.left) (n : ℕ), 1 ≤ n → FullTorsion G ξ n → ∀ e, GenWeil G L ξ n e → ∀ (E : Type) [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E) (X' : Scheme.{0}) [IsLocallyNoetherian X'] (Ω' : Type) [Field Ω'] (ξ' : Spec (CommRingCat.of Ω') ⟶ X'), IsCptGen ξ' → Flat.NormalCpt ξ' → ∀ (f : X' ⟶ X) (i : Ω →+* Ω'), GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f i → ∀ (G' : Over X') [GrpObj G'] [IsCommMonObj G'] (φ : G'.left ⟶ G.left), IsGrpPullback G' G f φ → ∀ (L' : LB G'.left) (e' : (Over.mk ξ' ⟶ G') → (Over.mk ξ' ⟶ G') → Ω'ˣ), GenWeil G' L' ξ' n e' → ∀ (E' : Type) [AddCommGroup E'] [Module Ω' E'] (M' : LieModel G' ξ' E') (j : E →+ E') (jd : Module.Dual Ω E →+ Module.Dual Ω' E'), (∀ v, (M'.pt (j v)).left ≫ φ = spMap (dualMap i) ≫ (M.pt v).left) → (∀ w v, jd w (j v) = i (w v)) → M'.htOm L' n = (M.htOm L n).pull ξ' f jd ∧ M'.omLat = M.omLat.pull ξ' f jd := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HtPull.main | exact GlobalTheory.CompanionTheory.Ar.HtPull.main | (intros; apply GlobalTheory.CompanionTheory.Ar.HtPull.main <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.hodge_tate_omega_coherent : ∀ (X : Scheme.{0}) [IsLocallyNoetherian X] (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X), IsCptGen ξ → Flat.NormalCpt ξ → ∀ (G : Over X) [GrpObj G], IsSemiAbelian G → ∀ (L : LB G.left) (n : ℕ), 1 ≤ n → FullTorsion G ξ n → ∀ e, GenWeil G L ξ n e → ∀ (E : Type) [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E), (M.htOm L n).IsCohOn Set.univ ∧ ∀ q : Cpt ξ, (∀ u ∈ M.omLat q, n • u ∈ M.htOm L n q) ∧ M.htOm L n q ≤ M.omLat q ∧ ∀ (a : G ⟶ G) [IsMonHom a] (A : E →ₗ[Ω] E), M.IsDiffOf a A → ∀ w ∈ M.htOm L n q, w ∘ₗ A ∈ M.htOm L n q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HTCoh.htOm_coherent | exact GlobalTheory.CompanionTheory.Ar.HTCoh.htOm_coherent | (intros; apply GlobalTheory.CompanionTheory.Ar.HTCoh.htOm_coherent <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT


theorem _root_.GlobalTheory.T.generic_torsion_noetherian_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (p : ℕ) (G : GenTors 𝔐 p) (O : Type) [CommRing O] [Algebra O Ω] (c' : ∀ k, J k) [IsNoetherianRing (CR O y c')] [IsIntegrallyClosed (CR O y c')] [IsFractionRing (CR O y c') Ω] (P : ChartPack G O c') (F : Type) [Field F] (pq : (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}) →+* F) (sc : F →+ (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)})), Function.Surjective pq → IsSec pq sc → ∀ a ∈ P.Γ₁.btOrder ⊤, (fun t => a (toN sc (fromN pq t))) ∈ P.Γ₁.btOrder ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.FamEx.btOrder_stable_of_section | exact GlobalTheory.CompanionTheory.Ar.Num.FamEx.btOrder_stable_of_section | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.FamEx.btOrder_stable_of_section <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Conj.CurveDegreeNonneg

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

theorem subDeg_map {K : Type} [Field K] (C : ACurve K) {V : Type} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {d : ℕ} (L : C.I → AddSubgroup V) (L' : C.I → AddSubgroup (Fin d → K))
    (e : V ≃ₗ[K] (Fin d → K)) (hL' : IsBun C L') (h : ∀ i v, v ∈ L i ↔ e v ∈ L' i)
    (U : Submodule K V) :
    subDeg C L' (U.map (e : V →ₗ[K] (Fin d → K))) = subDeg C L U := by
  have hb := (GlobalTheory.CompanionTheory.Ar.Crv.SubQuot.isBun_sub_quot K C (Fin d → K) L' (U.map (e : V →ₗ[K] (Fin d → K))) hL').1
  refine (GlobalTheory.CompanionTheory.Ar.Crv.DegEquiv.deg_equiv K C _ _ (sub C L' (U.map (e : V →ₗ[K] (Fin d → K)))) (sub C L U)
    (e.submoduleMap U).symm hb ?_).2.symm
  intro i x
  have hx : e ((e.submoduleMap U).symm x : V) = x := by
    have := (e.submoduleMap U).apply_symm_apply x
    exact congrArg Subtype.val this
  simp only [sub, AddSubgroup.mem_comap, LinearMap.toAddMonoidHom_coe, Submodule.subtype_apply]
  rw [h i, hx]

theorem mem_eigSp {K V O : Type} [Field K] [AddCommGroup V] [Module K V] [CommRing O]
    (r : O →+* Module.End K V) (σ : O →+* K) (v : V) :
    v ∈ eigSp r σ ↔ ∀ a, r a v = σ a • v := by
  simp [eigSp, Submodule.mem_iInf, sub_eq_zero]

theorem mem_eig {K V O : Type} [Field K] [AddCommGroup V] [Module K V]
    (ρ : O → V →ₗ[K] V) (χ : O → K) (v : V) :
    v ∈ eig ρ χ ↔ ∀ a, ρ a v = χ a • v := by
  simp [eig, Submodule.mem_iInf, sub_eq_zero]

theorem map_eigSp {K V O : Type} [Field K] [AddCommGroup V] [Module K V] [CommRing O] {d : ℕ}
    (r : O →+* Module.End K V) (ρ : O →+* Matrix (Fin d) (Fin d) K) (σ : O →+* K)
    (e : V ≃ₗ[K] (Fin d → K)) (h : ∀ a v, e (r a v) = (ρ a).mulVec (e v)) :
    (eigSp r σ).map (e : V →ₗ[K] (Fin d → K)) = eig (fun a => Matrix.toLin' (ρ a)) (fun a => σ a) := by
  ext y
  obtain ⟨v, rfl⟩ := e.surjective y
  have h1 : e v ∈ (eigSp r σ).map (e : V →ₗ[K] (Fin d → K)) ↔ v ∈ eigSp r σ := by
    constructor
    · rintro ⟨u, hu, huv⟩
      have : u = v := e.injective huv
      exact this ▸ hu
    · exact fun hv => ⟨v, hv, rfl⟩
  rw [h1, mem_eigSp, mem_eig]
  refine forall_congr' fun a => ?_
  rw [Matrix.toLin'_apply, ← h, ← map_smul]
  exact e.injective.eq_iff.symm

theorem m2Curve_holds : CurveSemiAbelianConjecture := by
  intro E _ _ _ H X0 t hpow k K _ _ _ p _ _ hp C z Y hne hk hfib V _ _ _ M r hact T _ χ hsplit hχ
    j q w W L hj hq hW0 hL0 hWj hLq hgap
  letI := H.starRing
  obtain ⟨d, D, e, hlie, her⟩ := GlobalTheory.T.curve_lie_eigen_degree E H (fun _ => rfl) X0 t hpow K p C z Y hne hfib V M r hact
  let f : V →ₗ[K] (Fin d → K) := e
  have key := GlobalTheory.T.eigen_flag_slope_bound K C p (𝓞 E) k (T ⊕ T) T χ d D Sum.inl Sum.inr j q w
    (fun τ i => (W τ i).map f) (fun τ i => (L τ i).map f) hp hsplit hk
    (by
      have : (Sum.elim Sum.inl Sum.inr : T ⊕ T → T ⊕ T) = id := by ext (x | x) <;> rfl
      rw [this]; exact Function.bijective_id)
    (fun τ a => hχ τ a) hj hq
    (fun τ => by simp [hW0 τ]) (fun τ => by simp [hL0 τ])
    (fun τ => by rw [hWj τ]; exact map_eigSp r D.ρ _ e her)
    (fun τ => by rw [hLq τ]; exact map_eigSp r D.ρ _ e her) hgap
  simpa only [subDeg_map C (Y.lieLat M) D.lie e D.lie_bun hlie, f] using key

end GlobalTheory.CompanionTheory.Ar.Conj.CurveDegreeNonneg
end
end
