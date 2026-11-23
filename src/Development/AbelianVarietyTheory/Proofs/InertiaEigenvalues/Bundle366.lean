module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle014
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.T2SpaceCoefficientRing
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CohDimTwoLocalOfLocalFiniteness
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelmerObstructionLeResidualSelmerSimpleExtension
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle015
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle343
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CocycleFormsSpanOddResidueChar
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidualSelmerBaseChangeCoefficientField
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanTwoOfGaloisHypothesis
public import GroundTheory.GlobalFields.TateThesis.AdeleIdealMeasure
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle345
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle339
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle236
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle344
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle013
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle012
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ResidualConstruction
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle016
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle297
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle355
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle004

@[expose] public section

section

open GlobalTheory.LiftLeaf GlobalTheory.TwSys GlobalTheory.TwAll Formalism.BasicNotions Formalism.MainNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.admALG_of_commG_var : ∀ D : D7, CommG D → IntegralHeckeForms.GroupAlgebraIntegrality D.nexp := by
  first | exact @GlobalTheory.IdemAlg.admALG_of_commG | exact GlobalTheory.IdemAlg.admALG_of_commG | (intros; apply GlobalTheory.IdemAlg.admALG_of_commG <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.PointRepConj

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices

theorem exists_gl_of_equiv {K Γ : Type} [Field K] {n : ℕ} (A B : Γ → Matrix (Fin n) (Fin n) K)
    (e : (Fin n → K) ≃ₗ[K] (Fin n → K))
    (he : ∀ g u, e (Matrix.toLin' (A g) u) = Matrix.toLin' (B g) (e u)) :
    ∃ P : GL (Fin n) K, ∀ g, (P : Matrix (Fin n) (Fin n) K) * A g = B g * (P : Matrix (Fin n) (Fin n) K) := by
  refine ⟨⟨LinearMap.toMatrix' (e : (Fin n → K) →ₗ[K] (Fin n → K)),
      LinearMap.toMatrix' (e.symm : (Fin n → K) →ₗ[K] (Fin n → K)), ?_, ?_⟩, ?_⟩
  · rw [← LinearMap.toMatrix'_comp]
    simp
  · rw [← LinearMap.toMatrix'_comp]
    simp
  · intro g
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun u => ?_
    simpa [Matrix.toLin'_mul] using he g u

theorem main : GlobalTheory.TwSys.Cheb → ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (i : N.Loc) (r r' : (N.X i → (GE N →* GL (Fin R.nV) (N.O i)))), GoodR N i r → GoodR N i r' → ∀ x, (∃ Pm : GL (Fin R.nV) (KK N i), ∀ g, (Pm : Matrix (Fin R.nV) (Fin R.nV) (KK N i)) * (rO N i r x g).map (toK N i) = (rO N i r' x g).map (toK N i) * (Pm : Matrix (Fin R.nV) (Fin R.nV) (KK N i))) := by
  intro hC R H what₂ N i r r' hr hr' x
  have h₁ := (GlobalTheory.ComplementCompare.isHeckeGalois_iff N i x (r x)).1 (hr x)
  have h₂ := (GlobalTheory.ComplementCompare.isHeckeGalois_iff N i x (r' x)).1 (hr' x)
  obtain ⟨e, he⟩ := GlobalTheory.ComplementCompare.isRx_unique N hC i x _ _ h₁ h₂
  exact exists_gl_of_equiv _ _ e he

end GlobalTheory.PointRepConj

end
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published

theorem _root_.GlobalTheory.T.selmerObstruction_le_residualSelmer_simpleExtension : PoitouTateTotallyComplex → CohDimTwo → LocalFiniteness → LocalTateDuality → LocalEulerChar → GlobalFiniteness → GlobalEulerChar → ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i) (Λ : Type) [CommRing Λ] [IsLocalRing Λ] [Algebra (X.O0 i) Λ] (κ : GE N →* Λˣ) (Q : Finset (PlE D.host)), Setup bkP i s κ Q → NoInv i s κ → LocSat bkP i s κ → LocCount bkP i s κ → SelObs bkP i s κ Q := by
  first | exact @GlobalTheory.SelObstruction.selObs | exact GlobalTheory.SelObstruction.selObs | (intros; apply GlobalTheory.SelObstruction.selObs <;> assumption)
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet

namespace GlobalTheory.NewPrime

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}

theorem exists_isDual (i : X.Tw) (s : X.Sig i) : ∃ ρ, IsDual i s ρ := by
  have hu : ∀ g, IsUnit (Tmat i s g).det := fun g => by
    rw [← Tgl_coe]; exact Matrix.isUnits_det_units _
  let τ : GE N →* Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i) :=
    { toFun := Tdual i s
      map_one' := by
        rw [Tdual, ← Tgl_coe, map_one, map_one]; simp
      map_mul' := fun g h => by
        simp only [Tdual, ← Tgl_coe, map_mul, Units.val_mul, Matrix.mul_inv_rev, Matrix.transpose_mul, smul_mul_smul_comm] }
  exact ⟨τ.toHomUnits, fun g => rfl⟩


end GlobalTheory.NewPrime
end
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel

theorem _root_.GlobalTheory.T.exists_unit_coeff_of_not_X_pow_dvd_line : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (i : X.Tw) (M : ℕ) (ι : Type) [Fintype ι] (K : Type) [Field K] [Algebra (X.O0 i) K], IsRes i K → ∀ (b : ι → K) (n : ℕ), n ≤ X.l i ^ M → ∀ F G : MvPolynomial ι (X.O0 i), toLam X i M ι F = toLam X i M ι G → ¬ (Polynomial.X : Polynomial K) ^ n ∣ MvPolynomial.aeval (fun q => Polynomial.C (b q) * Polynomial.X) G → ∃ m : ι →₀ ℕ, m.degree < n ∧ IsUnit (F.coeff m) := by
  first | exact @GlobalTheory.ResSel.exists_unit_coeff_of_not_dvd_line | exact GlobalTheory.ResSel.exists_unit_coeff_of_not_dvd_line | (intros; apply GlobalTheory.ResSel.exists_unit_coeff_of_not_dvd_line <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel

theorem _root_.GlobalTheory.T.exists_open_normal_subgroup_under_inertia : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (T : Set (X.Sig i)), (∀ s ∈ T, GalHyp bkP i s) → ∀ z, IsTameInertiaElementAtTwistPrime X i z → ∀ (M : ℕ) (H : Subgroup (GE N)), IsOpen (H : Set (GE N)) → H.Normal → (∀ v ∈ X.pD i, ∀ A : ValuationSubring N.Om, IsPlaceOver A v → Ine (F := D.host.E) A ≤ H) → ∃ L : Subgroup (GE N), IsOpen (L : Set (GE N)) ∧ L.Normal ∧ L ≤ H ∧ (∀ s ∈ T, Small i s L z) ∧ (∀ g ∈ L, ∀ ζ : N.Om, ζ ^ (2 * X.l i ^ M) = 1 → g ζ = ζ) ∧ ∀ s ∈ T, ∀ g ∈ L, ∀ a b, (Tmat i s g - 1) a b ∈ Ideal.span {(X.l i : X.O0 i) ^ nu X i} * IsLocalRing.maximalIdeal (X.O0 i) := by
  first | exact @GlobalTheory.ResSel.SmallSub.exists_small | exact GlobalTheory.ResSel.SmallSub.exists_small | (intros; apply GlobalTheory.ResSel.SmallSub.exists_small <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel

theorem _root_.GlobalTheory.T.cocycleFormsSpan_oddResidueChar : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), GalHyp bkP i s → SpanOdd i s := by
  first | exact @GlobalTheory.ResSel.SpanOddPf.spanOdd | exact GlobalTheory.ResSel.SpanOddPf.spanOdd | (intros; apply GlobalTheory.ResSel.SpanOddPf.spanOdd <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.ResDual

theorem _root_.GlobalTheory.T.residualSelmer_baseChange_coefficientField : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (ρ : GE N →* GL (Fin D.R.r) (X.O0 i)) (k : Type) [Field k] [Algebra (X.O0 i) k] [TopologicalSpace k] [DiscreteTopology k] (K : Type) [Field K] [Algebra (X.O0 i) K] [TopologicalSpace K] [DiscreteTopology K], IsRes i k → Function.Surjective (algebraMap (X.O0 i) k) → IsRes i K → ∀ Q : Finset (PlE D.host), Module.Finite k (selOn bkP i ρ (1 : GE N →* kˣ) k Q) → Module.Finite K (selOn bkP i ρ (1 : GE N →* Kˣ) K Q) ∧ Module.finrank K (selOn bkP i ρ (1 : GE N →* Kˣ) K Q) = Module.finrank k (selOn bkP i ρ (1 : GE N →* kˣ) k Q) := by
  first | exact @GlobalTheory.ResSel.BaseChange.selOn_baseChange | exact GlobalTheory.ResSel.BaseChange.selOn_baseChange | (intros; apply GlobalTheory.ResSel.BaseChange.selOn_baseChange <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel

theorem _root_.GlobalTheory.T.span_two_of_galois_hypothesis : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), GalHyp bkP i s → SpanTwo i s := by
  first | exact @GlobalTheory.ResSel.AltSpan.spanTwo_of_galHyp | exact GlobalTheory.ResSel.AltSpan.spanTwo_of_galHyp | (intros; apply GlobalTheory.ResSel.AltSpan.spanTwo_of_galHyp <;> assumption)
end

section

open NumberField IsDedekindDomain
open scoped nonZeroDivisors

theorem _root_.GlobalTheory.T.mem_natMultipleIntegralFiniteAdeles_iff_idealFiniteAdeles : ∀ (E : Type) [Field E] [NumberField E] (N : ℕ), 0 < N → ∀ (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ), (J : FractionalIdeal (𝓞 E)⁰ E) = FractionalIdeal.spanSingleton (𝓞 E)⁰ (N : E) → ∀ z : FiniteAdeleRing (𝓞 E) E, z ∈ GlobalTheory.RSJ.natLat E N ↔ z ∈ GroundTheory.Global.idealFiniteAdeles J := by
  first | (exact @GlobalTheory.RSJ.natLat_iff_mem_idealFiniteAdeles) | (exact GlobalTheory.RSJ.natLat_iff_mem_idealFiniteAdeles) | (intros; apply GlobalTheory.RSJ.natLat_iff_mem_idealFiniteAdeles  <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.BK

open PowerSeries

section Helpers

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {a : ℕ} {ι : Type}

theorem Epow_smul_mem_of_hasU (l e : ℕ) {B : Subalgebra O K⟦X⟧} [HasU B]
    (W : Submodule B (Vec K a ι)) (k : ℕ) {x : Vec K a ι} (hx : x ∈ W) : E K l e ^ k • x ∈ W := by
  have := W.smul_mem (EIn l e B ^ k) hx
  rwa [Subalgebra.smul_def, SubmonoidClass.coe_pow, coe_EIn] at this

theorem natPow_smul_mem {R M : Type} [Semiring R] [AddCommMonoid M] [Module R M] [Module K M]
    (W : Submodule R M) (l n : ℕ) {x : M} (hx : x ∈ W) : (l : K) ^ n • x ∈ W := by
  rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
  exact W.nsmul_mem hx _

end Helpers

theorem lpow_Epow_twistedMon_decomp : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H) (c : ℕ), 1 ≤ η → η < H → 14 * H < l → 10 * H + 2 ≤ l → ∀ y' ∈ D.Y', ∀ m ∈ D.Minv, (l : K) ^ c • D.zeta (D.phi m) ∈ D.MM → ∃ p ∈ D.L, ∃ f ∈ D.FilMM (10 * H), Ezpow K l e (-(2 * H : ℤ)) • f ∈ D.Man ∧ (l : K) ^ c • (E K l e ^ (2 * H) • (E K l e • D.zeta (y' + D.phi m) - D.EN (y' + D.phi m))) = p + ((l : K) ^ (3 * H))⁻¹ • f := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ η H D c h1 h2 h3 h4 y' hy' m hm hc
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[l] K).injective
  have hr : ((l : K) ^ (3 * H)) ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  have IC := GlobalTheory.T.breuilKisin_integrality_computation O K l e a ι η H D h2 h4
  obtain ⟨p₁, hp₁, f₁, hf₁, h₁⟩ := GlobalTheory.T.breuilKisin_zeta_fine_bound_second_basis O K l e a ι η H D h1 h2 h3 y' hy'
  obtain ⟨p', hp', f', hf', h'⟩ := IC.1 _ hc
  have hy : y' + D.phi m ∈ D.EM η := by
    refine add_mem ((D.desc.Y'_le_Y η hy').1 : y' ∈ D.EM η) ?_
    rw [mem_divE]
    exact D.upper _ (D.phi_mem_L hm.1)
  obtain ⟨p'', hp'', f'', hf'', h''⟩ := IC.2.2 _ hy
  set r : K := (l : K)
  set u : K⟦X⟧ := E K l e
  have hF : (u ^ (2 * H + 1) • (r ^ c • f₁) + r ^ (3 * H) • (u ^ (2 * H + 1) • f') -
      r ^ (3 * H) • (r ^ c • f'')) ∈ D.FilMM (10 * H) :=
    sub_mem (add_mem (Epow_smul_mem_of_hasU l e _ _ (natPow_smul_mem _ _ _ hf₁))
      (natPow_smul_mem _ _ _ (Epow_smul_mem_of_hasU l e _ _ hf')))
      (natPow_smul_mem _ _ _ (natPow_smul_mem _ _ _ hf''))
  refine ⟨u ^ (2 * H + 1) • (r ^ c • r ^ (l - 14 * H) • p₁) + u ^ (2 * H + 1) • p' - r ^ c • p'',
    sub_mem (add_mem (Epow_smul_mem_of_hasU l e _ _ (natPow_smul_mem _ _ _ (natPow_smul_mem _ _ _ hp₁)))
      (Epow_smul_mem_of_hasU l e _ _ hp')) (natPow_smul_mem _ _ _ hp''), _, hF, IC.2.1 _ hF, ?_⟩
  have hinv : (r ^ (3 * H))⁻¹ • (u ^ (2 * H + 1) • (r ^ c • f₁) + r ^ (3 * H) • (u ^ (2 * H + 1) • f') -
      r ^ (3 * H) • (r ^ c • f'')) =
      u ^ (2 * H + 1) • (r ^ c • ((r ^ (3 * H))⁻¹ • f₁)) + u ^ (2 * H + 1) • f' - r ^ c • f'' := by
    rw [smul_sub, smul_add, inv_smul_smul₀ hr, inv_smul_smul₀ hr, smul_comm (r ^ (3 * H))⁻¹ (u ^ (2 * H + 1)),
      smul_comm (r ^ (3 * H))⁻¹ (r ^ c)]
  rw [hinv, map_add D.zeta, h₁, smul_sub, smul_smul (u ^ (2 * H)) u, ← pow_succ, smul_sub,
    smul_comm (r ^ c) (u ^ (2 * H + 1)), smul_add (r ^ c) _ (D.zeta (D.phi m)), h', h'']
  simp only [smul_add]
  abel

end GlobalTheory.BK
end
end

section

noncomputable section

namespace GlobalTheory.LcImage

open PowerSeries GlobalTheory.BK GlobalTheory.IndefiniteRowSideFullHecke.ImagePolynomialAction

theorem norm_intCast_eq_one {K : Type} [NormedField K] (l : ℕ) [Fact l.Prime]
    [NormedAlgebra ℚ_[l] K] {u : ℤ} (hu : ¬ (l : ℤ) ∣ u) : ‖(u : K)‖ = 1 := by
  rw [← map_intCast (algebraMap ℚ_[l] K), norm_algebraMap']
  exact le_antisymm (Padic.norm_int_le_one u)
    (not_lt.1 fun h => hu (Padic.norm_intCast_lt_one_iff.1 h))

theorem exists_mul_intCast_eq {O K : Type} [CommRing O] [NormedField K] [Algebra O K]
    [IsUnitBall O K] (l : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] {r : ℤ} (hr : r ≠ 0)
    {m : ℕ} (hm : padicValInt l r ≤ m) : ∃ t : O, algebraMap O K t * (r : K) = (l : K) ^ m := by
  obtain ⟨v, hvdef⟩ : ∃ v, padicValInt l r = v := ⟨_, rfl⟩
  have hdv := padicValInt_dvd (p := l) r
  rw [hvdef] at hdv hm
  obtain ⟨u, hu⟩ := hdv
  have hpr : (l : ℕ).Prime := Fact.out
  have hu' : ¬ (l : ℤ) ∣ u := by
    rintro ⟨k, rfl⟩
    have h := (padicValInt_dvd_iff (p := l) (v + 1) r).1
      ⟨k, by rw [hu, pow_succ]; ring⟩
    omega
  have hl0 : (l : K) ≠ 0 := natCast_ne_zero' l hpr.ne_zero
  have hu0 : (u : K) ≠ 0 := by
    intro h
    have := norm_intCast_eq_one (K := K) l hu'
    rw [h, norm_zero] at this
    exact zero_ne_one this
  set t : K := (l : K) ^ (m - v) * (u : K)⁻¹ with ht
  obtain ⟨t', ht'⟩ := (IsUnitBall.mem_range_iff (O := O) t).2 (by
    rw [ht, norm_mul, norm_pow, norm_inv, norm_intCast_eq_one l hu', inv_one, mul_one, norm_l l]
    exact pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ (by exact_mod_cast hpr.one_le)))
  refine ⟨t', ?_⟩
  rw [ht', ht, hu]
  push_cast
  rw [mul_comm ((l : K) ^ v), ← mul_assoc, mul_assoc _ _ (u : K), inv_mul_cancel₀ hu0,
    mul_one, ← pow_add, Nat.sub_add_cancel hm]

theorem exists_mem_Y'_Lc_cls_eq : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H) (U : Finset ℤ) (N : ℕ), D.jumps ⊆ U → U ⊆ Finset.Icc (-(η : ℤ)) H → U.card ≤ N + 1 → η < H → H + η < l → 10 * H + 2 ≤ l → ∀ c : ℕ, ∀ w ∈ D.Zl, (l : K) ^ c • D.Lc w ∈ D.Z → ∃ y ∈ D.Y', D.Lc (D.cls y) = (l : K) ^ (c + η + (N + 1) * η) • D.Lc w := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ η H D U N hJ hU hN hηH hl h10 c w hw hc
  obtain ⟨-, hVal, hInt⟩ := GlobalTheory.T.breuilKisinDescent_monodromy_image_valuation O K l e a ι η H D U N hJ hU hN hηH
  obtain ⟨-, hR0, hv, hcard, hcard'⟩ := hVal hl

  obtain ⟨z, hz, hRz⟩ := hInt h10 (c : ℤ) (D.LcZ ⟨w, hw⟩) ⟨_, rfl⟩ (by
    rw [zpow_natCast, D.coe_LcZ]; exact hc)
  rw [zpow_natCast] at hz
  have hRz' : (((polyR l e U η).eval 0 : ℤ) : K) • D.Lc w = D.Lc z := by
    simpa using congrArg Subtype.val hRz

  obtain ⟨t, ht⟩ := exists_mul_intCast_eq (O := O) (K := K) l hR0 (m := (N + 1) * η)
    (by omega)
  have hx1 : t • ((l : K) ^ c • (z : D.Pol)) ∈ D.Z := D.Z.smul_mem t hz
  have hLx1 : D.Lc (t • ((l : K) ^ c • (z : D.Pol))) = (l : K) ^ (c + (N + 1) * η) • D.Lc w := by
    rw [← algebraMap_smul K t, map_smul, map_smul, ← hRz', smul_smul, smul_smul, pow_add]
    congr 1
    rw [← ht]; ring

  obtain ⟨z'', hz'', hv''⟩ := (GlobalTheory.T.prime_pow_divisibility_of_descentDatum O K l e a ι η H D).1 _ hx1

  have hz3 : z'' ∈ (D.desc.Y η).map (D.cls.restrictScalars O) := by
    rw [Descent.map_Y]; exact hz''
  obtain ⟨y'', hy'', rfl⟩ := hz3
  refine ⟨(X : K⟦X⟧) ^ e • y'', (Descent.mem_Y' _).2 ⟨y'', hy'', rfl⟩, ?_⟩
  have h1 : D.cls ((X : K⟦X⟧) ^ e • y'') = (l : K) ^ η • (t • ((l : K) ^ c • (z : D.Pol))) := by
    rw [hv'']; rfl
  rw [h1, map_smul, hLx1, smul_smul, ← pow_add]
  congr 2
  ring

end GlobalTheory.LcImage
end
end
