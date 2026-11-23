module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.RingHom.Etale
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle006
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Perfection
public import Mathlib.RingTheory.Valuation.ValuationRing
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusIntegralityWittTiltAinf
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Finiteness.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle092
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import ReciprocityTheory.NeutralLocalFields.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle709
public import Mathlib.Analysis.SpecificLimits.Normed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.IsStrictDom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.MeasInvStatementPfA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle001
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle002
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle021
import Development.AbelianVarietyTheory.Definitions.Divisors.CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
import Development.AbelianVarietyTheory.Definitions.Divisors.Pullback1MemHodgeFiltration
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.EntireEqOfHalfPlane
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle637

@[expose] public section

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst GlobalTheory.ScalarPoin MeasureTheory

namespace GlobalTheory

theorem tsum_pow_eventually_ne_zero : ∀ {ι : Type} (a : ι → ℂ) (i0 : ι) (k0 : ℕ), a i0 = 1 → (∀ i, ‖a i‖ ≤ 1) → (∀ i, i ≠ i0 → ‖a i‖ < 1) → Summable (fun i => ‖a i‖ ^ k0) → ∀ N : ℕ, ∃ k : ℕ, N ≤ k ∧ ∑' i, a i ^ k ≠ 0 := by
  intro ι a i0 k0 h0 h1 hlt hs N
  classical
  have hlim : Filter.Tendsto (fun k : ℕ => ∑' i, a i ^ k) Filter.atTop
      (nhds (∑' i, (if i = i0 then (1:ℂ) else 0))) := by
    apply tendsto_tsum_of_dominated_convergence (bound := fun i => ‖a i‖ ^ k0) hs
    · intro i
      by_cases hi : i = i0
      · subst hi; simp [h0]
      · simp only [hi, if_false]
        exact tendsto_pow_atTop_nhds_zero_of_norm_lt_one (hlt i hi)
    · filter_upwards [Filter.eventually_ge_atTop k0] with k hk i
      rw [norm_pow]
      exact pow_le_pow_of_le_one (norm_nonneg _) (h1 i) hk
  rw [tsum_ite_eq] at hlim
  have hev := hlim.eventually_ne one_ne_zero
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.1 hev
  exact ⟨max N M, le_max_left _ _, hM _ (le_max_right _ _)⟩

end GlobalTheory
end

section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Points
open scoped TensorProduct

namespace GlobalTheory.EtaleComplexPoints

theorem encard_complexPoints_eq_rank : ∀ {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (δ : ℕ), f.Etale → f.Finite → (letI := f.toAlgebra; Module.Free A B ∧ Module.finrank A B = δ) → ∀ φ : A →+* ℂ, {ψ : B →+* ℂ | ψ.comp f = φ}.encard = (δ : ℕ∞) := by
  intro A B _ _ f δ hf hfin hfree φ
  letI := f.toAlgebra
  letI := φ.toAlgebra
  obtain ⟨hF, hrk⟩ := hfree
  have hEt : Algebra.Etale A B := RingHom.etale_algebraMap.1 hf
  have hMF : Module.Finite A B := hfin
  have hFE : Algebra.FormallyEtale ℂ (ℂ ⊗[A] B) := inferInstance
  have hcard := GlobalTheory.natCard_algHom_eq_finrank_of_etale_baseChange A B ℂ
  have hto (ψ : {ψ : B →+* ℂ | ψ.comp f = φ}) (a : A) : ψ.1 (algebraMap A B a) = algebraMap A ℂ a := by
    have := congrArg (fun g : A →+* ℂ => g a) ψ.2
    simpa [RingHom.algebraMap_toAlgebra] using this
  have hinv (g : B →ₐ[A] ℂ) : (g : B →+* ℂ).comp f = φ := by
    ext a
    simpa [RingHom.algebraMap_toAlgebra] using g.commutes a
  let e : {ψ : B →+* ℂ | ψ.comp f = φ} ≃ (B →ₐ[A] ℂ) :=
    { toFun := fun ψ => { ψ.1 with commutes' := hto ψ }
      invFun := fun g => ⟨g.toRingHom, hinv g⟩
      left_inv := fun ψ => rfl
      right_inv := fun g => rfl }
  have hfinite : Finite (B →ₐ[A] ℂ) :=
    Finite.of_equiv _ (AlgHom.liftEquiv A ℂ B ℂ).symm
  rw [Set.encard, ENat.card_congr e, ENat.card_eq_coe_natCard, hcard, hrk]

end GlobalTheory.EtaleComplexPoints
end

section

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.TiltValuation

theorem tilt_isDomain_valuationRing : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∃ _ : IsDomain (PreTilt O p), ValuationRing (PreTilt O p) := by
  intro p _ C _ _ _ v O _ _ _ _ hv
  haveI hdom : IsDomain (PreTilt O p) := PreTilt.isDomain C v O hv p
  haveI : IsDomain O := hv.hom_inj.isDomain _
  haveI : ValuationRing O := ValuationRing.iff_dvd_total.2 ⟨fun a b => by
    rcases le_total (v (algebraMap O C a)) (v (algebraMap O C b)) with h | h
    · exact Or.inr (hv.dvd_of_le h)
    · exact Or.inl (hv.dvd_of_le h)⟩
  exact ⟨hdom, ValuationRing.iff_dvd_total.2 ⟨fun a b => GlobalTheory.FrobInt.dvd_total_tilt a b⟩⟩

end GlobalTheory.TiltValuation
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem finrank_range_baseChange_eq_dualMap_and_finrank_dual :
    ∀ (O : Type) [CommRing O] (K : Type) [Field K] [Algebra O K] (M₁ : Type) [AddCommGroup M₁] [Module O M₁] [Module.Free O M₁] [Module.Finite O M₁] (M₂ : Type) [AddCommGroup M₂] [Module O M₂] [Module.Free O M₂] [Module.Finite O M₂] (f : M₁ →ₗ[O] M₂), Module.finrank K (LinearMap.range (f.baseChange K)) = Module.finrank K (LinearMap.range (f.dualMap.baseChange K)) ∧ Module.finrank K (K ⊗[O] M₁) = Module.finrank K (K ⊗[O] Module.Dual O M₁) := by
  intro O _ K _ _ M₁ _ _ _ _ M₂ _ _ _ _ f
  obtain ⟨h1, h2⟩ := GlobalTheory.DualFibreRank.finrank_dual_and_range_dualMap_baseChange O M₁ M₂ K f
  exact ⟨h2.symm, h1.symm⟩

end GlobalTheory.AbCoh
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exteriorSq_of_symm_relations (K : Type) [Field K] (V W : Type) [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [Module.Finite K V] [Module.Finite K W] (β : V →ₗ[K] V →ₗ[K] W)
    (hW : Module.finrank K W ≤ (Module.finrank K V).choose 2)
    (hrel : ∀ t : V ⊗[K] V, TensorProduct.lift β t = 0 → TensorProduct.comm K V V t = t) :
    (∃ e : ⋀[K]^2 V ≃ₗ[K] W, ∀ a b, e (exteriorPower.ιMulti K 2 ![a, b]) = β a b) ∧
      Function.Surjective (TensorProduct.lift β) ∧
      ∀ t : V ⊗[K] V, TensorProduct.comm K V V t = t → TensorProduct.lift β t = 0 := by
  classical
  set n := Module.finrank K V with hn
  have h0 : ∀ a b x : V, Function.update ![a, b] 0 x = ![x, b] := by
    intro a b x; ext i; fin_cases i <;> rfl
  have h1 : ∀ a b x : V, Function.update ![a, b] 1 x = ![a, x] := by
    intro a b x; ext i; fin_cases i <;> rfl
  let wb : V →ₗ[K] V →ₗ[K] ⋀[K]^2 V :=
    LinearMap.mk₂ K (fun a b => exteriorPower.ιMulti K 2 ![a, b])
      (by intro a₁ a₂ b
          rw [← h0 a₁ b (a₁ + a₂), AlternatingMap.map_update_add]; simp only [h0])
      (by intro c a b
          rw [← h0 a b (c • a), AlternatingMap.map_update_smul]; simp only [h0])
      (by intro a b₁ b₂
          rw [← h1 a b₁ (b₁ + b₂), AlternatingMap.map_update_add]; simp only [h1])
      (by intro c a b
          rw [← h1 a b (c • b), AlternatingMap.map_update_smul]; simp only [h1])
  let π : V ⊗[K] V →ₗ[K] ⋀[K]^2 V := TensorProduct.lift wb
  have hπt : ∀ a b, π (a ⊗ₜ b) = exteriorPower.ιMulti K 2 ![a, b] := by
    intro a b; simp [π, wb]
  have hπ : Function.Surjective π := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← exteriorPower.ιMulti_span K 2 V, Submodule.span_le]
    rintro _ ⟨m, rfl⟩
    refine ⟨m 0 ⊗ₜ m 1, ?_⟩
    rw [hπt]; congr 1; ext i; fin_cases i <;> rfl
  have hswap : ∀ x y : V, exteriorPower.ιMulti K 2 ![x, y] = -exteriorPower.ιMulti K 2 ![y, x] := by
    intro x y
    rw [← (exteriorPower.ιMulti K 2).map_swap ![y, x] (show (0 : Fin 2) ≠ 1 by decide)]
    congr 1; ext i; fin_cases i <;> rfl
  have hdiag : ∀ x : V, exteriorPower.ιMulti K 2 ![x, x] = 0 := by
    intro x
    exact (exteriorPower.ιMulti K 2).map_eq_zero_of_eq ![x, x] (i := 0) (j := 1) rfl (by decide)
  let b := Module.finBasis K V
  let bt := b.tensorProduct b
  let r : V ⊗[K] V →ₗ[K] ⋀[K]^2 V :=
    bt.constr K (fun p => if p.1 < p.2 then exteriorPower.ιMulti K 2 ![b p.1, b p.2] else 0)
  have hrb : ∀ i j, r (b i ⊗ₜ b j) = if i < j then exteriorPower.ιMulti K 2 ![b i, b j] else 0 := by
    intro i j
    rw [← Module.Basis.tensorProduct_apply, Module.Basis.constr_basis]
  have hr : r ∘ₗ (LinearMap.id - (TensorProduct.comm K V V).toLinearMap) = π := by
    apply bt.ext; rintro ⟨i, j⟩
    simp only [bt, Module.Basis.tensorProduct_apply, LinearMap.comp_apply, LinearMap.sub_apply,
      LinearMap.id_apply, LinearEquiv.coe_coe, TensorProduct.comm_tmul, map_sub, hrb, hπt]
    rcases lt_trichotomy i j with h | h | h
    · simp [h, lt_asymm h]
    · subst h; simp [hdiag]
    · simp [h, lt_asymm h, hswap (b i) (b j)]
  have hS : ∀ t, TensorProduct.comm K V V t = t → π t = 0 := by
    intro t ht
    rw [← hr, LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply, LinearEquiv.coe_coe, ht,
      sub_self, map_zero]
  set L := TensorProduct.lift β with hLdef
  have hle : LinearMap.ker L ≤ LinearMap.ker π := fun t ht => hS t (hrel t ht)
  have hVV : Module.finrank K (V ⊗[K] V) = n * n := Module.finrank_tensorProduct
  have hext : Module.finrank K (⋀[K]^2 V) = n.choose 2 := by rw [exteriorPower.finrank_eq]
  have hπk := LinearMap.finrank_range_add_finrank_ker π
  rw [LinearMap.range_eq_top.mpr hπ, finrank_top, hext, hVV] at hπk
  have hLk := LinearMap.finrank_range_add_finrank_ker L
  rw [hVV] at hLk
  have hLr : Module.finrank K (LinearMap.range L) ≤ Module.finrank K W := Submodule.finrank_le _
  have hNeq : LinearMap.ker L = LinearMap.ker π :=
    Submodule.eq_of_le_of_finrank_le hle (by
      generalize n * n = m at hπk hLk
      generalize n.choose 2 = k at hπk hW
      omega)
  have hL : Function.Surjective L := by
    rw [← LinearMap.range_eq_top]
    apply Submodule.eq_top_of_finrank_eq
    rw [hNeq] at hLk
    generalize n * n = m at hπk hLk
    generalize n.choose 2 = k at hπk hW
    omega
  refine ⟨?_, hL, fun t ht => ?_⟩
  · refine ⟨(π.quotKerEquivOfSurjective hπ).symm.trans
      ((Submodule.quotEquivOfEq _ _ hNeq.symm).trans (L.quotKerEquivOfSurjective hL)), ?_⟩
    intro a c
    rw [← hπt, ← LinearMap.quotKerEquivOfSurjective_apply_mk π hπ, LinearEquiv.trans_apply,
      LinearEquiv.symm_apply_apply, LinearEquiv.trans_apply, Submodule.quotEquivOfEq_mk,
      LinearMap.quotKerEquivOfSurjective_apply_mk, hLdef, TensorProduct.lift.tmul]
  · have : t ∈ LinearMap.ker L := hNeq ▸ hS t ht
    exact this

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ExtSqKer

variable {R : Type} [CommRing R] {M H Q : Type} [AddCommGroup M] [Module R M]
  [AddCommGroup H] [Module R H] [AddCommGroup Q] [Module R Q]

theorem upd_congr {J : Type} [DecidableEq J] (p : M →ₗ[R] H) (F : M [⋀^J]→ₗ[R] Q)
    (hF : ∀ (u : J → M) (j : J), p (u j) = 0 → F u = 0)
    (u : J → M) (j : J) (a b : M) (hab : p a = p b) :
    F (Function.update u j a) = F (Function.update u j b) := by
  have h1 : a = b + (a - b) := by abel
  rw [h1, F.map_update_add, hF (Function.update u j (a - b)) j (by simp [hab]), add_zero]

noncomputable def descend {J : Type} (p : M →ₗ[R] H) (hp : Function.Surjective p)
    (F : M [⋀^J]→ₗ[R] Q)
    (hF : ∀ (u : J → M) (j : J), p (u j) = 0 → F u = 0) :
    H [⋀^J]→ₗ[R] Q where
  toFun v := F (fun k => Function.surjInv hp (v k))
  map_update_add' := by
    intro _ v j x y
    have e : ∀ z : H, (fun k => Function.surjInv hp (Function.update v j z k)) =
        Function.update (fun k => Function.surjInv hp (v k)) j (Function.surjInv hp z) := by
      intro z; funext k; by_cases h : k = j
      · subst h; simp
      · simp [h]
    simp only [e]
    rw [upd_congr p F hF _ j _ (Function.surjInv hp x + Function.surjInv hp y)
      (by simp [Function.surjInv_eq hp]), F.map_update_add]
  map_update_smul' := by
    intro _ v j c x
    have e : ∀ z : H, (fun k => Function.surjInv hp (Function.update v j z k)) =
        Function.update (fun k => Function.surjInv hp (v k)) j (Function.surjInv hp z) := by
      intro z; funext k; by_cases h : k = j
      · subst h; simp
      · simp [h]
    simp only [e]
    rw [upd_congr p F hF _ j _ (c • Function.surjInv hp x)
      (by simp [Function.surjInv_eq hp]), F.map_update_smul, RingHom.id_apply]
  map_eq_zero_of_eq' := by
    intro v a b hv hab
    exact F.map_eq_zero_of_eq _ (by simp [hv]) hab

end GlobalTheory.ExtSqKer

namespace GlobalTheory.ExtSqKer

variable {R : Type} [CommRing R] {M H Q : Type} [AddCommGroup M] [Module R M]
  [AddCommGroup H] [Module R H] [AddCommGroup Q] [Module R Q]

theorem fin_two_vector_eq_matrixVecCons (u : Fin 2 → M) : u = ![u 0, u 1] := by
  ext k; fin_cases k <;> rfl

theorem congr_two (p : M →ₗ[R] H) (F : M [⋀^Fin 2]→ₗ[R] Q)
    (hF : ∀ (u : Fin 2 → M) (j : Fin 2), p (u j) = 0 → F u = 0)
    (u u' : Fin 2 → M) (h : ∀ k, p (u k) = p (u' k)) : F u = F u' := by
  calc F u = F (Function.update u 0 (u 0)) := by rw [Function.update_eq_self]
    _ = F (Function.update u 0 (u' 0)) := upd_congr p F hF u 0 _ _ (h 0)
    _ = F (Function.update (Function.update u 0 (u' 0)) 1 ((Function.update u 0 (u' 0)) 1)) := by
        rw [Function.update_eq_self]
    _ = F (Function.update (Function.update u 0 (u' 0)) 1 (u' 1)) :=
        upd_congr p F hF _ 1 _ _ (by simpa using h 1)
    _ = F u' := by
        congr 1; ext k; fin_cases k <;> simp

end GlobalTheory.ExtSqKer


open GlobalTheory.ExtSqKer in
theorem GlobalTheory.exteriorSquare_ker_of_surjective (R : Type) [CommRing R] (W M H : Type)
    [AddCommGroup W] [Module R W] [AddCommGroup M] [Module R M] [AddCommGroup H] [Module R H]
    (i : W →ₗ[R] M) (p : M →ₗ[R] H) (hp : Function.Surjective p) (hex : Function.Exact i p)
    (t : ⋀[R]^2 M) (ht : exteriorPower.map 2 p t = 0) :
    ∃ (n : ℕ) (a : Fin n → M) (w : Fin n → W),
      t = ∑ k, exteriorPower.ιMulti R 2 ![a k, i (w k)] := by
  set S : Set (⋀[R]^2 M) := {x | ∃ (a : M) (w : W), x = exteriorPower.ιMulti R 2 ![a, i w]}
  set N : Submodule R (⋀[R]^2 M) := Submodule.span R S
  let F : M [⋀^Fin 2]→ₗ[R] (⋀[R]^2 M ⧸ N) := N.mkQ.compAlternatingMap (exteriorPower.ιMulti R 2)
  have hF : ∀ (u : Fin 2 → M) (j : Fin 2), p (u j) = 0 → F u = 0 := by
    intro u j hj
    obtain ⟨w, hw⟩ := (hex (u j)).1 hj
    simp only [F, LinearMap.compAlternatingMap_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    fin_cases j
    · have e : u = ![u 1, i w] ∘ Equiv.swap 0 1 := by
        ext k; fin_cases k <;> simp [hw]
      rw [e, AlternatingMap.map_swap _ _ (by decide)]
      exact N.neg_mem (Submodule.subset_span ⟨u 1, w, rfl⟩)
    · rw [fin_two_vector_eq_matrixVecCons u]
      exact Submodule.subset_span ⟨u 0, w, by simp [hw]⟩
  let g := exteriorPower.alternatingMapLinearEquiv (descend p hp F hF)
  have hg : g ∘ₗ exteriorPower.map 2 p = N.mkQ := by
    apply exteriorPower.linearMap_ext
    ext m
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.coe_comp, Function.comp_apply,
      exteriorPower.map_apply_ιMulti, g, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
    change F _ = F m
    exact congr_two p F hF _ _ (fun k => by simp [Function.surjInv_eq hp])
  have hN : t ∈ N := by
    have := congrArg (fun f => f t) hg
    simp only [LinearMap.coe_comp, Function.comp_apply, ht, map_zero, Submodule.mkQ_apply] at this
    exact (Submodule.Quotient.mk_eq_zero N).1 this.symm
  obtain ⟨n, c, x, hx⟩ := Submodule.mem_span_set'.1 hN
  choose a w haw using fun k => (x k).2
  refine ⟨n, fun k => c k • a k, w, ?_⟩
  rw [← hx]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [haw k]
  have e : ![c k • a k, i (w k)] = Function.update ![a k, i (w k)] 0 (c k • a k) := by
    ext l; fin_cases l <;> simp
  rw [e, AlternatingMap.map_update_smul]
  congr 2
  ext l; fin_cases l <;> simp
end

section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
open GlobalTheory.ToricTransport (coordIn)
open scoped nonZeroDivisors

namespace GlobalTheory

theorem exists_sq_eq_neg_of_discr_eq_neg : ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (h2 : Module.finrank ℚ K = 2) (hd : discr K = -(d : ℤ)), ∃ δ : K, δ ^ 2 = -(d : K) := by
  classical
  intro K _ _ d h2 hd
  haveI : Algebra.IsQuadraticExtension ℚ K := ⟨h2⟩
  haveI : IsGalois ℚ K := inferInstance
  have hcard : Nat.card (K ≃ₐ[ℚ] K) = 2 := by rw [IsGalois.card_aut_eq_finrank, h2]
  obtain ⟨σ, hσ, huniq⟩ := (Nat.card_eq_two_iff' (1 : K ≃ₐ[ℚ] K)).1 hcard
  have huniv : (Finset.univ : Finset (K ≃ₐ[ℚ] K)) = {1, σ} := by
    ext y
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    by_cases hy : y = 1
    · exact Or.inl hy
    · exact Or.inr (huniq y hy)
  have htr : ∀ x : K, algebraMap ℚ K (Algebra.trace ℚ K x) = x + σ x := by
    intro x
    rw [_root_.trace_eq_sum_automorphisms, huniv, Finset.sum_pair (Ne.symm hσ)]
    rfl
  let e : Module.Free.ChooseBasisIndex ℤ (𝓞 K) ≃ Fin 2 :=
    Fintype.equivFinOfCardEq (by rw [← Module.finrank_eq_card_basis (integralBasis K), h2])
  let b : Fin 2 → K := fun i => integralBasis K (e.symm i)
  have hb : ⇑(integralBasis K) ∘ ⇑e.symm = b := rfl
  have key : algebraMap ℚ K (discr K : ℚ) = (b 0 * σ (b 1) - b 1 * σ (b 0)) ^ 2 := by
    rw [coe_discr, ← Algebra.discr_reindex ℚ (integralBasis K) e, hb, Algebra.discr_def,
      Matrix.det_fin_two]
    simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply, map_sub, map_mul, htr]
    ring
  refine ⟨b 0 * σ (b 1) - b 1 * σ (b 0), ?_⟩
  rw [← key, hd]
  push_cast
  simp

end GlobalTheory
end

section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal Neutral.B1
open scoped nonZeroDivisors

namespace GlobalTheory.Div.SuppIdele

theorem snd_apply_mul {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (a b : AdeleRing (𝓞 K) K) : (a * b).2 v = a.2 v * b.2 v := rfl

theorem supported_eq_localIdele : ∀ {K : Type} [Field K] [NumberField K] {v : HeightOneSpectrum (𝓞 K)} {a : Ideles K},
    IsSupportedAt K a v → ∃ x : (v.adicCompletion K)ˣ, (x : v.adicCompletion K) = (a : AdeleRing (𝓞 K) K).2 v ∧
      localIdele K v x = a := by
  intro K _ _ v a ha
  classical
  let x : (v.adicCompletion K)ˣ :=
    { val := (a : AdeleRing (𝓞 K) K).2 v
      inv := ((a⁻¹ : Ideles K) : AdeleRing (𝓞 K) K).2 v
      val_inv := by
        rw [← snd_apply_mul, Units.mul_inv]; rfl
      inv_val := by
        rw [← snd_apply_mul, Units.inv_mul]; rfl }
  refine ⟨x, rfl, ?_⟩
  apply Units.ext
  apply Prod.ext
  · funext w
    exact (ha.1 w).symm
  · apply RestrictedProduct.ext
    intro w
    by_cases hw : w = v
    · subst hw
      exact (localIdele_snd_self K w x).trans rfl
    · exact ((localIdele_isSupportedAt K v x).2 w hw).trans (ha.2 w hw).symm

end GlobalTheory.Div.SuppIdele
end
