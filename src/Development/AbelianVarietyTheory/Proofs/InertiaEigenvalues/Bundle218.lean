module

public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.NumberTheory.Padics.ValuativeRel
public import GroundTheory.LocalFields.Bundle002
public import GroundTheory.LocalFields.Integers
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TracePairingInjectiveEquivariantLevelMap
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLimitCocycleOfCompatibleModPow
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.NumberTheory.Padics.Complex
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle177
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle203
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle080
public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Valuation.ValuationRing
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle205
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
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.Valuation.Integral
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle007

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

noncomputable section

namespace GlobalTheory.PMon.Ram

theorem padic_mem_integer_iff (l : ℕ) [Fact l.Prime] (a : ℚ_[l]) : a ∈ 𝒪[ℚ_[l]] ↔ ‖a‖ ≤ 1 := by
  change valuation ℚ_[l] a ≤ 1 ↔ _
  rw [← map_one (valuation ℚ_[l]), ← (valuation ℚ_[l]).vle_iff_le,
    Valuation.Compatible.vle_iff_le (v := Padic.mulValuation),
    GroundTheory.LocalField.Padic.mulValuation_le_iff_norm_le, norm_one]

theorem isIntegral_integer_iff_norm_le (l : ℕ) [Fact l.Prime] (y : Om l) :
    IsIntegral 𝒪[ℚ_[l]] y ↔ ‖y‖ ≤ 1 := by
  have hy : IsIntegral ℚ_[l] y := Algebra.IsIntegral.isIntegral y
  rw [← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralValue_le_one_iff (minpoly.monic hy)]
  constructor
  · intro h n
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] h, Polynomial.coeff_map]
    exact (padic_mem_integer_iff l _).1 ((minpoly 𝒪[ℚ_[l]] y).coeff n).2
  · intro h
    have hl : minpoly ℚ_[l] y ∈ Polynomial.lifts (algebraMap 𝒪[ℚ_[l]] ℚ_[l]) := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      exact fun n => ⟨⟨_, (padic_mem_integer_iff l _).2 (h n)⟩, rfl⟩
    obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_degree_eq_and_monic hl (minpoly.monic hy)
    refine ⟨q, hqm, ?_⟩
    rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap ℚ_[l], hq, minpoly.aeval]

end GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem mem_integer_iff_norm_le_and_valuation_lt_one_iff_norm_lt (l : ℕ) [Fact l.Prime] (L : Type) [Field L]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra ℚ_[l] L]
    [ValuativeExtension ℚ_[l] L] [FiniteDimensional ℚ_[l] L] [IsGalois ℚ_[l] L] [Algebra L (Om l)]
    [IsScalarTower ℚ_[l] L (Om l)] (x : L) :
    (x ∈ 𝒪[L] ↔ ‖algebraMap L (Om l) x‖ ≤ 1) ∧ (valuation L x < 1 ↔ ‖algebraMap L (Om l) x‖ < 1) := by
  have key : ∀ z : L, z ∈ 𝒪[L] ↔ ‖algebraMap L (Om l) z‖ ≤ 1 := by
    intro z
    let f : L →ₐ[𝒪[ℚ_[l]]] Om l := (IsScalarTower.toAlgHom ℚ_[l] L (Om l)).restrictScalars 𝒪[ℚ_[l]]
    have hf : Function.Injective f := (algebraMap L (Om l)).injective
    rw [← isIntegral_integer_iff_norm_le]
    change valuation L z ≤ 1 ↔ IsIntegral 𝒪[ℚ_[l]] (f z)
    rw [isIntegral_algHom_iff f hf, GroundTheory.LocalField.isIntegral_iff ℚ_[l] L z]
  refine ⟨key x, ?_⟩
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have hy : algebraMap L (Om l) x ≠ 0 := (map_ne_zero _).2 hx
  have hv : valuation L x ≠ 0 := by simpa using hx
  have h1 := key x⁻¹
  rw [map_inv₀, norm_inv, inv_le_one₀ (norm_pos_iff.2 hy)] at h1
  change valuation L x⁻¹ ≤ 1 ↔ _ at h1
  rw [map_inv₀, inv_le_one₀ (zero_lt_iff.2 hv)] at h1
  rw [← not_le, ← not_le, h1]

end GlobalTheory.PMon.Ram

end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

theorem _root_.GlobalTheory.T.tracePairing_injective_equivariant_levelMap : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL] (A A' : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (LA' : Lattice (O := O) A'.ρ) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDualLat1 (P.PD K) LA LA' m → ∀ (lam : LL →ₗ[ℚ_[l]] ℚ_[l]), (∀ a : LL, (∀ b : O, ∃ u : ℤ_[l], lam (a * algebraMap O LL b) = (u : ℚ_[l])) ↔ ∃ b : O, algebraMap O LL b = a) → ∀ (r : ℕ) (hI : StableSub LA (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T)) (hI' : StableSub LA' (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA'.T)), (∀ g : ↥(GK K), ∃ u : ℤ_[l], (((P.PD K).χ g : ℚ_[l]ˣ) : ℚ_[l]) = (u : ℚ_[l]) ∧ (PadicInt.toZModPow r u : ZMod (l ^ r)) = ((Formalism.GaloisCohomology.cycK l K.1 r (IntermediateField.fixingSubgroupEquiv K.1 g) : (ZMod (l ^ r))ˣ) : ZMod (l ^ r))) → ∀ (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M] (e : (↥LA.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T)) ≃+ M) (rho : Representation (ZMod (l ^ r)) (Formalism.GaloisCohomology.GK l K.1) M), (∀ g x, rho g (e x) = e (actQ LA _ hI ((IntermediateField.fixingSubgroupEquiv K.1).symm g) x)) → ∃ Ψ : (↥LA'.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA'.T)) →+ ReciprocityTheory.Gal.TDual (ZMod (l ^ r)) M, Function.Injective Ψ ∧ ∀ g y, Ψ (actQ LA' _ hI' ((IntermediateField.fixingSubgroupEquiv K.1).symm g) y) = ReciprocityTheory.Gal.twDual (Formalism.GaloisCohomology.cycK l K.1 r) rho g (Ψ y) := by
  first | exact @GlobalTheory.tracePairing_levelMap | exact GlobalTheory.tracePairing_levelMap | (intros; apply GlobalTheory.tracePairing_levelMap <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

theorem _root_.GlobalTheory.T.exists_limit_cocycle_of_compatible_mod_pow : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (ϖ : O), Irreducible ϖ → ∀ (hI : ∀ n : ℕ, StableSub LA (Ideal.span {ϖ ^ n} • ⊤ : Submodule O ↥LA.T)) (w : ℕ → ↥(GK K) → ↥LA.T), (∀ n, (fun g => (Submodule.Quotient.mk (w n g) : ↥LA.T ⧸ (Ideal.span {ϖ ^ n} • ⊤ : Submodule O ↥LA.T))) ∈ quotientCocycles LA _ (hI n)) → (∀ n g, w (n + 1) g - w n g ∈ (Ideal.span {ϖ ^ n} • ⊤ : Submodule O ↥LA.T)) → ∃ d ∈ latticeCocycles LA, ∀ n g, ∃ t ∈ (Ideal.span {ϖ ^ n} • ⊤ : Submodule O ↥LA.T), d g = (w n g : A.V) + (t : A.V) := by
  first | exact @GlobalTheory.LimCocycle.limit_cocycle | exact GlobalTheory.LimCocycle.limit_cocycle | (intros; apply GlobalTheory.LimCocycle.limit_cocycle <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory

theorem _root_.GlobalTheory.isIrrSub_mapRep_of_span_restrict_eq_top {k Γ : Type} [Field k] [Group Γ] {L : Type}
    [Field L] (f : k →+* L) {a : ℕ} (ρ : Γ →* GL (Fin a) k) (W : Submodule k (Fin a → k))
    (hW : _root_.Formalism.MainNotions.N.Stable (_root_.Formalism.MainNotions.N.matRep ((Units.coeHom _).comp ρ)) W) (hne : W ≠ ⊥)
    (hsp : Submodule.span k (Set.range fun g =>
      (_root_.Formalism.MainNotions.N.matRep ((Units.coeHom _).comp ρ) g).restrict (hW g)) = ⊤) :
    _root_.Formalism.MainNotions.N.IsIrrSub (_root_.Formalism.MainNotions.N.mapRep f ρ)
      (Submodule.span L ((fun v => f ∘ v) '' (W : Set (Fin a → k)))) := by
  classical
  have hmul : ∀ (g : Γ) (w : Fin a → k),
      ((_root_.Formalism.MainNotions.N.mapRep f ρ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L).mulVec (f ∘ w) =
        f ∘ ((ρ g : Matrix (Fin a) (Fin a) k).mulVec w) := by
    intro g w
    funext i
    exact (RingHom.map_mulVec f _ w i).symm
  let T : Γ → (Fin a → L) →ₗ[L] (Fin a → L) := fun g =>
    Matrix.toLin' ((_root_.Formalism.MainNotions.N.mapRep f ρ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L)
  let A := Submodule.span L (Set.range T)
  let P : Submodule k (Module.End k W) :=
    { carrier := {E | ∃ M ∈ A, ∀ w : W, M (f ∘ (w : Fin a → k)) = f ∘ ((E w : W) : Fin a → k)}
      add_mem' := by
        rintro E₁ E₂ ⟨M₁, hM₁, h₁⟩ ⟨M₂, hM₂, h₂⟩
        refine ⟨M₁ + M₂, A.add_mem hM₁ hM₂, fun w => ?_⟩
        rw [LinearMap.add_apply, h₁, h₂]
        funext i
        simp
      zero_mem' := ⟨0, A.zero_mem, fun w => by funext i; simp⟩
      smul_mem' := by
        rintro c E ⟨M, hM, h⟩
        refine ⟨f c • M, A.smul_mem _ hM, fun w => ?_⟩
        rw [LinearMap.smul_apply, h]
        funext i
        simp }
  have hP : ∀ E, E ∈ P := by
    have hle : Submodule.span k (Set.range fun g =>
        (_root_.Formalism.MainNotions.N.matRep ((Units.coeHom _).comp ρ) g).restrict (hW g)) ≤ P := by
      rw [Submodule.span_le]
      rintro _ ⟨g, rfl⟩
      refine ⟨T g, Submodule.subset_span ⟨g, rfl⟩, fun w => ?_⟩
      rw [LinearMap.restrict_coe_apply]
      exact hmul g w
    intro E
    apply hle
    rw [hsp]
    exact Submodule.mem_top
  have hA : ∀ W' : Submodule L (Fin a → L), _root_.Formalism.MainNotions.N.IsInv (_root_.Formalism.MainNotions.N.mapRep f ρ) W' →
      ∀ M ∈ A, ∀ v ∈ W', M v ∈ W' := by
    intro W' hW' M hM
    induction hM using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      intro v hv
      exact hW' g v hv
    | zero => intro v _; simpa using W'.zero_mem
    | add x y _ _ hx hy => intro v hv; exact W'.add_mem (hx v hv) (hy v hv)
    | smul c x _ hx => intro v hv; exact W'.smul_mem c (hx v hv)
  unfold _root_.Formalism.MainNotions.N.IsIrrSub
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    intro h
    apply hw0
    have hfw : f ∘ w ∈ Submodule.span L ((fun v => f ∘ v) '' (W : Set (Fin a → k))) :=
      Submodule.subset_span ⟨w, hw, rfl⟩
    rw [h, Submodule.mem_bot] at hfw
    funext i
    simpa using congrFun hfw i
  · intro g v hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨w, hw, rfl⟩ := hx
      rw [hmul]
      exact Submodule.subset_span ⟨_, hW g w hw, rfl⟩
    | zero => rw [Matrix.mulVec_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [Matrix.mulVec_smul]; exact Submodule.smul_mem _ c hx
  · intro W' hle hst
    by_cases h0 : W' = ⊥
    · exact Or.inl h0
    right
    apply le_antisymm hle
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
      by_contra h
      push_neg at h
      exact hx0 (funext h)
    rw [Submodule.span_le]
    rintro _ ⟨w₀, hw₀, rfl⟩
    show f ∘ w₀ ∈ W'
    let φ : W →ₗ[k] k := (LinearMap.proj i : (Fin a → k) →ₗ[k] k).comp W.subtype
    let E : Module.End k W := φ.smulRight ⟨w₀, hw₀⟩
    obtain ⟨M, hMA, hM⟩ := hP E
    have key : ∀ y ∈ Submodule.span L ((fun v => f ∘ v) '' (W : Set (Fin a → k))),
        M y = y i • (f ∘ w₀) := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨w, hw, rfl⟩ := hy
        rw [hM ⟨w, hw⟩]
        funext j
        simp [E, φ]
      | zero => simp
      | add y z _ _ hy hz => rw [map_add (f := _), hy, hz, Pi.add_apply, add_smul]
      | smul c y _ hy => rw [map_smul, hy, Pi.smul_apply, smul_eq_mul, mul_smul]
    have hmem : M x ∈ W' := hA W' hst M hMA x hx
    rw [key x (hle hx)] at hmem
    have hsm := W'.smul_mem (x i)⁻¹ hmem
    rwa [smul_smul, inv_mul_cancel₀ hi, one_smul] at hsm

end GlobalTheory
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory

noncomputable def bnMatRep {k Γ : Type} [Field k] [Group Γ] {W : Type} [AddCommGroup W]
    [Module k W] {a : ℕ} (b : Module.Basis (Fin a) k W) (s : Representation k Γ W) :
    Γ →* GL (Fin a) k :=
  MonoidHom.toHomUnits
    (((LinearMap.toMatrixAlgEquiv b).toAlgHom.toRingHom.toMonoidHom).comp s)

theorem bnMatRep_val {k Γ : Type} [Field k] [Group Γ] {W : Type} [AddCommGroup W]
    [Module k W] {a : ℕ} (b : Module.Basis (Fin a) k W) (s : Representation k Γ W) (g : Γ) :
    ((bnMatRep b s g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k)
      = LinearMap.toMatrix b b (s g) := rfl

theorem bnMatRep_mulVec {k Γ : Type} [Field k] [Group Γ] {W : Type} [AddCommGroup W]
    [Module k W] {a : ℕ} (b : Module.Basis (Fin a) k W) (s : Representation k Γ W) (g : Γ)
    (v : W) :
    ((bnMatRep b s g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k).mulVec (b.equivFun v)
      = b.equivFun (s g v) := by
  rw [bnMatRep_val]
  exact LinearMap.toMatrix_mulVec_repr b b (s g) v

theorem bnMatRep_isSSRep {k Γ : Type} [Field k] [Group Γ] {W : Type} [AddCommGroup W]
    [Module k W] {a : ℕ} (b : Module.Basis (Fin a) k W) (s : Representation k Γ W)
    (hs : IsSS s) : IsSSRep (bnMatRep b s) := by
  intro U hU
  obtain ⟨U', hU', hc⟩ := hs (U.comap (b.equivFun : W →ₗ[k] (Fin a → k))) (by
    intro g v hv
    have := hU g _ hv
    simp only [Submodule.mem_comap, LinearEquiv.coe_coe] at this ⊢
    rw [← bnMatRep_mulVec]
    exact this)
  refine ⟨U'.map (b.equivFun : W →ₗ[k] (Fin a → k)), ?_, ?_⟩
  · rintro g _ ⟨v, hv, rfl⟩
    refine ⟨s g v, hU' g v hv, ?_⟩
    exact (bnMatRep_mulVec b s g v).symm
  · have h := (Submodule.orderIsoMapComap b.equivFun).isCompl hc
    have h1 : (Submodule.orderIsoMapComap b.equivFun)
        (U.comap (b.equivFun : W →ₗ[k] (Fin a → k))) = U :=
      Submodule.map_comap_eq_of_surjective b.equivFun.surjective U
    rw [h1] at h
    exact h

theorem brauerNesbitt_abstract_of_matrix : (∀ (Γ k : Type) [Group Γ] [Field k] (a : ℕ) (ρ ρ' : Γ →* GL (Fin a) k), IsSSRep ρ → IsSSRep ρ' → (∀ g, ((ρ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k).charpoly = ((ρ' g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k).charpoly) → ∃ h : GL (Fin a) k, ∀ g, ρ' g = h * ρ g * h⁻¹) → ∀ {k Γ : Type} [Field k] [Group Γ] {W : Type} [AddCommGroup W] [Module k W] [FiniteDimensional k W] {V : Type} [AddCommGroup V] [Module k V] [FiniteDimensional k V] (s : Representation k Γ W) (s' : Representation k Γ V), IsSS s → IsSS s' → (∀ g, LinearMap.charpoly (s g) = LinearMap.charpoly (s' g)) → ∃ e : W ≃ₗ[k] V, ∀ g v, e (s g v) = s' g (e v) := by
  intro H k Γ _ _ W _ _ _ V _ _ _ s s' hs hs' hc
  have hdim : Module.finrank k V = Module.finrank k W := by
    rw [← LinearMap.charpoly_natDegree (s 1), ← LinearMap.charpoly_natDegree (s' 1), hc]
  let b : Module.Basis (Fin (Module.finrank k W)) k W := Module.finBasis k W
  let b' : Module.Basis (Fin (Module.finrank k W)) k V := Module.finBasisOfFinrankEq k V hdim
  obtain ⟨h, hh⟩ := H Γ k _ (bnMatRep b s) (bnMatRep b' s') (bnMatRep_isSSRep b s hs)
    (bnMatRep_isSSRep b' s' hs') (by
      intro g
      rw [bnMatRep_val, bnMatRep_val, LinearMap.charpoly_toMatrix, LinearMap.charpoly_toMatrix, hc])
  let m : (Fin (Module.finrank k W) → k) ≃ₗ[k] (Fin (Module.finrank k W) → k) :=
    (Matrix.GeneralLinearGroup.toLin h).toLinearEquiv
  have hm : ∀ x, m x = (h : Matrix _ _ k).mulVec x := fun x => rfl
  refine ⟨b.equivFun.trans (m.trans b'.equivFun.symm), fun g v => ?_⟩
  apply b'.equivFun.injective
  rw [← bnMatRep_mulVec]
  simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply, hm]
  rw [← bnMatRep_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul,
    ← Units.val_mul, hh g, inv_mul_cancel_right]

end GlobalTheory
end

section

open Polynomial
open Classical

namespace GlobalTheory

theorem separated_roots_additive_poly : ∀ (l : ℕ) [Fact l.Prime] (E M h : ℕ) (a : ℕ → ℂ_[l]) (ρ : ℝ), M + h ≤ E → (∀ k, k ≤ E → ‖a k‖ ≤ 1) → ‖a (M + h)‖ = 1 → 0 < ρ → ρ < 1 → ‖a M‖ * ρ ^ l ^ M = ‖(l : ℂ_[l])‖ → (∀ k, M < k → k ≤ E → ‖a k‖ * ρ ^ l ^ k < ‖(l : ℂ_[l])‖) → ∃ Z : Finset ℂ_[l], l ^ h ≤ Z.card ∧ (∀ W ∈ Z, ‖W‖ ≤ 1 ∧ ∑ k ∈ Finset.range (E + 1), a k * W ^ l ^ k = 0) ∧ ∀ W ∈ Z, ∀ W' ∈ Z, W ≠ W' → ρ < ‖W - W'‖ := by
  intro l _ E M h a ρ hMh ha1 haMh hρ0 hρ1 haM hak
  have hl : 2 ≤ l := (Fact.out : l.Prime).two_le
  have hinj : Function.Injective (fun k : ℕ => l ^ k) := Nat.pow_right_injective hl
  set G : ℂ_[l][X] := ∑ k ∈ Finset.range (E + 1), Polynomial.monomial (l ^ k) (a k) with hG
  have hcoeff : ∀ j, G.coeff j = ∑ k ∈ Finset.range (E + 1), if l ^ k = j then a k else 0 := by
    intro j
    simp only [hG, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial_apply]
  have hcd : G.coeff (l ^ (M + h)) = a (M + h) := by
    rw [hcoeff, Finset.sum_eq_single (M + h)]
    · simp
    · intro b _ hb
      rw [if_neg]
      intro hh; exact hb (hinj hh)
    · intro hn; exact absurd (Finset.mem_range.2 (by omega)) hn
  have hcd0 : G.coeff (l ^ (M + h)) ≠ 0 := by
    rw [hcd]; intro h0; rw [h0, norm_zero] at haMh; exact zero_ne_one haMh
  have hcle : ∀ j, ‖G.coeff j‖ ≤ 1 := by
    intro j
    rw [hcoeff]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun k hk => ?_
    split_ifs
    · exact ha1 k (by have := Finset.mem_range.1 hk; omega)
    · simp
  have hrc := (GlobalTheory.T.card_roots_closedBall_bounds_ultrametric ℂ_[l] G 1 (l ^ (M + h)) one_pos hcd0).1 (by
    intro j; simp only [one_pow, mul_one]; rw [hcd, haMh]; exact hcle j)
  set s := G.roots.filter fun z => ‖z‖ ≤ 1 with hs
  have hG0 : G ≠ 0 := by
    intro h0; apply hcd0; rw [h0]; simp
  obtain ⟨Z, hZc, hZs, hZsep⟩ := GlobalTheory.T.exists_finset_separated_of_multiset_bounded_cluster ℂ_[l] s ρ (l ^ h) (l ^ M) hρ0.le
    (pow_pos (by omega) _) (by rw [mul_comm, ← pow_add]; exact hrc) (by
      intro W hW
      have hW1 : ‖W‖ ≤ 1 := (Multiset.mem_filter.1 hW).2
      refine le_trans (Multiset.card_le_card ?_) (GlobalTheory.T.card_roots_closedBall_le_prime_pow l E M a ρ W (by omega) ha1 hρ0 hρ1 haM hak hW1)
      exact Multiset.monotone_filter_left _ (Multiset.filter_le _ _))
  refine ⟨Z, hZc, fun W hW => ?_, hZsep⟩
  have hWs := Multiset.mem_filter.1 (hZs W hW)
  refine ⟨hWs.2, ?_⟩
  have hr := (Polynomial.mem_roots hG0).1 hWs.1
  have := hr.eq_zero
  rw [hG, Polynomial.eval_finsetSum] at this
  simpa [Polynomial.eval_monomial] using this

end GlobalTheory
end

section

open scoped NNReal TensorProduct

namespace GlobalTheory

theorem descent_of_points_killed : ∀ (l : ℕ) [Fact l.Prime] (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Module.Flat A B] (u : A) (pr : B →ₗ[A] A), ((l : ℕ) : B) = 0 → algebraMap A B u ∈ nonZeroDivisors B → IsHausdorff (Ideal.span {algebraMap A B u}) B → ∀ (κ : Type) [Fintype κ] (x : κ → B), (∀ (T : Type) [CommRing T] (i₁ i₂ : B →+* T), (∀ a, i₁ (algebraMap A B a) = i₂ (algebraMap A B a)) → IsUnit (i₁ (algebraMap A B u)) → ∃ c : κ → κ → T, ∀ j, i₁ (x j) - i₂ (x j) = ∑ i, (i₁ (x i) - i₂ (x i)) ^ l * c i j) → (∀ (O : Type) [CommRing O] [IsDomain O] [ValuationRing O] [CharP O l] [PerfectRing O l] (ψ ψ' : B →+* O), ψ (algebraMap A B u) ≠ 0 → ¬ IsUnit (ψ (algebraMap A B u)) → IsAdicComplete (Ideal.span {ψ (algebraMap A B u)}) O → (∀ a, ψ (algebraMap A B a) = ψ' (algebraMap A B a)) → ∀ j, ψ (x j) = ψ' (x j)) → pr 1 = 1 → ∀ j, x j = algebraMap A B (pr (x j)) := by
  intro l _ A B _ _ _ _ u pr hl hu hH κ _ x hEq hPt hpr
  let iL : B →ₐ[A] B ⊗[A] B := Algebra.TensorProduct.includeLeft
  let iR : B →ₐ[A] B ⊗[A] B := Algebra.TensorProduct.includeRight
  let U : B ⊗[A] B := algebraMap A (B ⊗[A] B) u
  let D : κ → B ⊗[A] B := fun j => iL (x j) - iR (x j)
  have hiL : ∀ a, iL (algebraMap A B a) = algebraMap A (B ⊗[A] B) a := fun a => iL.commutes a
  have hiR : ∀ a, iR (algebraMap A B a) = algebraMap A (B ⊗[A] B) a := fun a => iR.commutes a

  have hlR : ((l : ℕ) : B ⊗[A] B) = 0 := by
    rw [← map_natCast iL, hl, map_zero]

  have hUreg : U ∈ nonZeroDivisors (B ⊗[A] B) := by
    have hinj : Function.Injective (LinearMap.mulLeft A (algebraMap A B u)) := by
      intro b b' hbb
      have h0 : (b - b') * algebraMap A B u = 0 := by
        simp only [LinearMap.mulLeft_apply] at hbb
        rw [sub_mul, mul_comm b, mul_comm b', hbb, sub_self]
      exact sub_eq_zero.mp ((mul_right_mem_nonZeroDivisors_eq_zero_iff hu).mp h0)
    have hinj' := Module.Flat.rTensor_preserves_injective_linearMap (M := B) _ hinj
    have hmul : ∀ y : B ⊗[A] B, y * U = LinearMap.rTensor B (LinearMap.mulLeft A (algebraMap A B u)) y := by
      intro y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul b b' =>
        simp [U, Algebra.TensorProduct.algebraMap_apply, mul_comm]
      | add y z hy hz => rw [add_mul, hy, hz, map_add (f := _)]
    rw [mem_nonZeroDivisors_iff_right]
    intro y hy
    rw [hmul] at hy
    exact hinj' (by rw [hy, map_zero])

  obtain ⟨h, c', hc'⟩ : ∃ (h : ℕ) (c' : κ → κ → B ⊗[A] B), ∀ j, U ^ h * D j = ∑ i, D i ^ l * c' i j := by
    let T := Localization.Away U
    let i₁ : B →+* T := (algebraMap (B ⊗[A] B) T).comp iL.toRingHom
    let i₂ : B →+* T := (algebraMap (B ⊗[A] B) T).comp iR.toRingHom
    have hA : ∀ a, i₁ (algebraMap A B a) = i₂ (algebraMap A B a) := by
      intro a
      simp only [i₁, i₂, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, hiL, hiR]
    have hunit : IsUnit (i₁ (algebraMap A B u)) := by
      simp only [i₁, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, hiL]
      exact IsLocalization.Away.algebraMap_isUnit U
    obtain ⟨c, hc⟩ := hEq T i₁ i₂ hA hunit
    obtain ⟨⟨b, hb⟩, hb'⟩ := IsLocalization.exist_integer_multiples (Submonoid.powers U) (S := T)
      (Finset.univ : Finset (κ × κ)) (fun p => c p.1 p.2)
    obtain ⟨h, rfl⟩ := hb
    choose c' hc'' using fun (p : κ × κ) => hb' p (Finset.mem_univ p)
    refine ⟨h, fun i j => c' (i, j), fun j => ?_⟩
    have hD : ∀ i, algebraMap (B ⊗[A] B) T (D i) = i₁ (x i) - i₂ (x i) := by
      intro i; simp [D, i₁, i₂]
    apply IsLocalization.injective T (M := Submonoid.powers U) (Submonoid.powers_le.mpr hUreg)

    rw [map_mul, map_sum, hD, hc j, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [map_mul, map_pow, hD]
    rw [hc'' (i, j)]
    change _ = _ * ((U ^ h) • c i j)
    rw [Algebra.smul_def, map_pow]
    ring

  have hkey : ∀ (m : ℕ) j, U ^ m ∣ D j := by
    refine GlobalTheory.T.dvd_all_pow_of_frobenius_eq_killed_by_perfect_points l (B ⊗[A] B) U hlR hUreg κ D c' h hc' ?_
    intro O _ _ _ _ _ f hf0 hfnu hcomp j
    let ψ : B →+* O := f.comp iL.toRingHom
    let ψ' : B →+* O := f.comp iR.toRingHom
    have hψ : ψ (algebraMap A B u) = f U := by
      simp only [ψ, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, hiL, U]
    have hagree : ∀ a, ψ (algebraMap A B a) = ψ' (algebraMap A B a) := by
      intro a
      simp only [ψ, ψ', RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, hiL, hiR]
    have := hPt O ψ ψ' (by rw [hψ]; exact hf0) (by rw [hψ]; exact hfnu) (by rw [hψ]; exact hcomp) hagree j
    simp only [ψ, ψ', RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] at this
    simp only [D, map_sub, this, sub_self]

  let φ : B ⊗[A] B →ₗ[A] B := TensorProduct.lift ((LinearMap.lsmul A B).comp pr)
  have hφ : ∀ b b' : B, φ (b ⊗ₜ b') = pr b • b' := fun b b' => by simp [φ]
  intro j
  have hφD : φ (D j) = algebraMap A B (pr (x j)) - x j := by
    simp only [D, map_sub]
    change φ (x j ⊗ₜ 1) - φ (1 ⊗ₜ x j) = _
    rw [hφ, hφ, hpr, one_smul, Algebra.smul_def, mul_one]
  have hmem : ∀ n : ℕ, algebraMap A B (pr (x j)) - x j ∈ Ideal.span {algebraMap A B u ^ n} := by
    intro n
    obtain ⟨r, hr⟩ := hkey n j
    rw [← hφD, hr]
    have : U ^ n * r = u ^ n • r := by simp [U, Algebra.smul_def, map_pow]
    rw [this, LinearMap.map_smul, Algebra.smul_def, map_pow]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  have hz := hH.haus (algebraMap A B (pr (x j)) - x j) (fun n => by
    rw [SModEq.zero, Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top]
    exact hmem n)
  exact (sub_eq_zero.mp hz).symm

end GlobalTheory
end
