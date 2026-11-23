module

public import Formalism.GaloisCohomology.LocalTateDualityK
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import ReciprocityTheory.BasicDefinitions.AdRep
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle276
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle261
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachWeierstrassTestAndDensity
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle277
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle099
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.Bundle004
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle007
public import Formalism.SharpRestriction.LevelLetterCocycles.SecondPropositionEveryLocalisation
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle279
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
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle010
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle012
public import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle008
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle009
import Formalism.LocalToGlobal.Divisibility.Bundle001
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide

@[expose] public section

section

open GlobalTheory.AdmLoc Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Filter Topology
open scoped TensorProduct

namespace GlobalTheory.EulerFree

theorem card_Z1_of_invariants_eq_bot {O G M : Type} [CommRing O] [Group G] [TopologicalSpace G]
    [AddCommGroup M] [Module O M] (π : Representation O G M)
    (hlc : ∀ m, IsLocallyConstant fun g => π g m) (h0 : π.invariants = ⊥) :
    Nat.card (ReciprocityTheory.Def.Z1 π ⊤) = Nat.card (ReciprocityTheory.Def.H1 π ⊤) * Nat.card M := by
  have hle : ReciprocityTheory.Def.B1 π ⊤ ≤ ReciprocityTheory.Def.Z1 π ⊤ := by
    rintro _ ⟨m, -, rfl⟩
    refine ⟨⟨(hlc m).comp (fun x => x - m), fun _ => Submodule.mem_top⟩, ?_⟩
    funext x
    change π x.1 (π x.2 m - m) - (π (x.1 * x.2) m - m) + (π x.1 m - m) = 0
    simp only [map_mul, Module.End.mul_apply, map_sub]
    abel
  have h1 := Submodule.card_eq_card_quotient_mul_card
    ((ReciprocityTheory.Def.B1 π ⊤).submoduleOf (ReciprocityTheory.Def.Z1 π ⊤))
  have h2 : Nat.card ((ReciprocityTheory.Def.B1 π ⊤).submoduleOf (ReciprocityTheory.Def.Z1 π ⊤)) =
      Nat.card (ReciprocityTheory.Def.B1 π ⊤) := Nat.card_congr (Submodule.comapSubtypeEquivOfLe hle).toEquiv
  have hinj : Function.Injective (ReciprocityTheory.Def.d0 π) := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff, ← h0]
    intro m hm g
    exact sub_eq_zero.1 (congrFun (LinearMap.mem_ker.1 hm) g)
  have h3 : Nat.card (ReciprocityTheory.Def.B1 π ⊤) = Nat.card M :=
    (Nat.card_congr (Submodule.topEquiv.symm.trans
      (Submodule.equivMapOfInjective _ hinj ⊤)).toEquiv).symm
  rw [h1, h2, h3, mul_comm]

theorem card_H1_of_euler (R O G G' : Type) [CommRing R] [CommRing O] [Group G] [TopologicalSpace G]
    [Group G'] [TopologicalSpace G'] (φ : G' ≃* G) (hφ : Continuous φ ∧ Continuous φ.symm)
    (M : Type) [AddCommGroup M] [Module R M] [Module O M] [Finite M] [TopologicalSpace M]
    [DiscreteTopology M] (rho : Representation R G M) (hrho : ReciprocityTheory.Gal.ContAction rho) (d : ℕ)
    (hEu : Nat.card (ReciprocityTheory.Gal.H1 rho) =
      Nat.card (ReciprocityTheory.Gal.H0 rho) * Nat.card (ReciprocityTheory.Gal.H2 rho) * Nat.card M ^ d)
    (π : Representation O G' M) (ha : ∀ g m, rho g m = π (φ.symm g) m)
    (hlc : ∀ m, IsLocallyConstant fun g => π g m) (h0 : π.invariants = ⊥)
    (h2 : Subsingleton (ReciprocityTheory.Def.H2 π ⊤)) :
    Nat.card (ReciprocityTheory.Def.H1 π ⊤) = Nat.card M ^ d := by
  have ha' : ∀ g m, rho (φ g) m = π g m := fun g m => by rw [ha, φ.symm_apply_apply]
  have hH0 : Nat.card (ReciprocityTheory.Gal.H0 rho) = 1 := by
    have : ReciprocityTheory.Gal.H0 rho = ⊥ := by
      rw [eq_bot_iff]
      intro m hm
      have : m ∈ π.invariants := fun g => by rw [← ha']; exact hm (φ g)
      rw [h0] at this
      exact this
    rw [this]
    exact Nat.card_unique
  have hH2 : Nat.card (ReciprocityTheory.Gal.H2 rho) = 1 := by
    have : Subsingleton (ReciprocityTheory.Gal.H2 rho) := by
      refine Submodule.Quotient.subsingleton_iff.2 (eq_top_iff.2 fun z _ => ?_)
      let z' : ReciprocityTheory.Def.Z2 π ⊤ := ⟨fun x => z.1 (φ x.1, φ x.2),
        ⟨(IsLocallyConstant.iff_continuous _).2 (z.2.1.comp
          ((hφ.1.comp continuous_fst).prodMk (hφ.1.comp continuous_snd))), fun _ => Submodule.mem_top⟩, by
        funext x
        have := z.2.2 (φ x.1) (φ x.2.1) (φ x.2.2)
        rw [ha', ← map_mul, ← map_mul] at this
        exact this⟩
      have hz' : z' ∈ (ReciprocityTheory.Def.B2 π ⊤).submoduleOf (ReciprocityTheory.Def.Z2 π ⊤) := by
        rw [Submodule.Quotient.subsingleton_iff.1 h2]
        exact Submodule.mem_top
      obtain ⟨b, hb, hbz⟩ := hz'
      refine ⟨fun g => b (φ.symm g), hb.1.continuous.comp hφ.2, ?_⟩
      funext x
      have h : π (φ.symm x.1) (b (φ.symm x.2)) - b (φ.symm x.1 * φ.symm x.2) + b (φ.symm x.1) =
          z.1 (φ (φ.symm x.1), φ (φ.symm x.2)) := congrFun hbz (φ.symm x.1, φ.symm x.2)
      rw [φ.apply_symm_apply, φ.apply_symm_apply, ← map_mul, ← ha] at h
      exact h
    exact Nat.card_unique
  have hZ := GlobalTheory.CocycleCount.card_cocycles_mul_invariants_discrete _ _ M rho hrho
  let E : ↥(ReciprocityTheory.Def.Z1 π ⊤) ≃ ↥(ReciprocityTheory.Gal.Z1 rho) :=
    { toFun := fun c => ⟨fun g => c.1 (φ.symm g), c.2.1.1.continuous.comp hφ.2, fun g h => by
        beta_reduce
        rw [ha, map_mul, cocycle_mul]⟩
      invFun := fun c => ⟨fun g => c.1 (φ g),
        ⟨(IsLocallyConstant.iff_continuous _).2 (c.2.1.comp hφ.1), fun _ => Submodule.mem_top⟩, by
          funext x
          have := c.2.2 (φ x.1) (φ x.2)
          rw [ha', ← map_mul] at this
          change π x.1 (c.1 (φ x.2)) - c.1 (φ (x.1 * x.2)) + c.1 (φ x.1) = 0
          rw [this]
          abel⟩
      left_inv := fun c => Subtype.ext (funext fun g => congrArg c.1 (φ.symm_apply_apply g))
      right_inv := fun c => Subtype.ext (funext fun g => congrArg c.1 (φ.apply_symm_apply g)) }
  have hM : 0 < Nat.card M := Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_right hM
  rw [← card_Z1_of_invariants_eq_bot π hlc h0, Nat.card_congr E]
  rw [hEu, hH0, hH2] at hZ
  simpa using hZ

theorem card_H1_eq_pow :
    Formalism.GaloisCohomology.LocalEulerCharK → ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (O M : Type) [CommRing O] [AddCommGroup M] [Module O M] [Finite M] (π : Representation O ↥(GK K) M), (∀ m : M, l • m = 0) → (∀ m, IsLocallyConstant fun g => π g m) → π.invariants = ⊥ → Subsingleton (ReciprocityTheory.Def.H2 π ⊤) → Nat.card (ReciprocityTheory.Def.H1 π ⊤) = Nat.card M ^ Module.finrank ℚ_[l] ↥K.1 := by
  intro hE l _ K O M _ _ _ _ π hl hlc h0 h2
  have hK : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  let _ : TopologicalSpace M := ⊥
  have _ : DiscreteTopology M := ⟨rfl⟩
  have hr' : ∀ m : M, l ^ 1 • m = 0 := fun m => by rw [pow_one, hl]
  have _ : NeZero (l ^ 1) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  let _ : Module (ZMod (l ^ 1)) M := AddCommGroup.zmodModule hr'
  let φ : ↥(GK K) ≃* Formalism.GaloisCohomology.GK l K.1 := IntermediateField.fixingSubgroupEquiv K.1
  have hφ : Continuous φ ∧ Continuous φ.symm :=
    GlobalTheory.fixingSubgroupEquiv_bicontinuous ℚ_[l] (Om l) K.1
  let rho : Representation (ZMod (l ^ 1)) (Formalism.GaloisCohomology.GK l K.1) M :=
    GlobalTheory.CocycleCount.repOfAction _ (fun g => (π (φ.symm g)).toAddMonoidHom)
      (fun m => by simp) (fun g h m => by simp)
  have hrho : ReciprocityTheory.Gal.ContAction rho := by
    refine continuous_prod_of_discrete_right.2 fun m => ?_
    exact (hlc m).continuous.comp hφ.2
  exact card_H1_of_euler _ O _ _ φ hφ M rho hrho _ (hE l K.1 hK 1 M rho Nat.one_pos hrho) π
    (fun _ _ => rfl) hlc h0 h2

end GlobalTheory.EulerFree
end

section

open GlobalTheory.GLq GlobalTheory.GLp Formalism.MainNotions.ArithmeticCylinders Polynomial NumberField
open scoped Classical

namespace GlobalTheory.FixedPlaceSplit

theorem host_conj_conj (D : Formalism.BasicNotions.D7) (x : D.host.E) : D.host.conj (D.host.conj x) = x := by
  apply D.host.φ₀.injective
  rw [D.host.toHostAx.conjE_apply, D.host.toHostAx.conjE_apply]
  simp

theorem isSplitPl_of_not_isConjPl (D : Formalism.BasicNotions.D7) (w : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E))
    (h : ¬ Formalism.BasicNotions.IsConjPl D.host w w) : Formalism.BasicNotions.IsSplitPl D.host w := by
  by_contra hs
  apply h
  have key : ∀ x y : 𝓞 D.host.E, (y : D.host.E) = D.host.conj (x : D.host.E) →
      x ∈ w.asIdeal → y ∈ w.asIdeal := by
    intro x y hxy hx
    by_contra hy
    apply hs
    refine ⟨x, hx, fun y' hy' => ?_⟩
    have : y' = y := by
      apply RingOfIntegers.ext
      exact hy'.trans hxy.symm
    rwa [this]
  intro x y hxy
  refine ⟨key x y hxy, key y x ?_⟩
  rw [hxy, host_conj_conj]

theorem isSplitPl_plGw : ∀ (D : Formalism.BasicNotions.D7) (k : Fin 2) (v : D.nd.PlG k),
    Formalism.BasicNotions.IsSplitPl D.host (D.naut.plGw k v) :=
  fun D k v => isSplitPl_of_not_isConjPl D _ (D.naut.plGw_nconj k v v)

end GlobalTheory.FixedPlaceSplit
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys

namespace GlobalTheory.TwSys.ResidualCompare

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}

theorem isConjPl_unique {P v v' : PlE D.host} (h : IsConjPl D.host P v) (h' : IsConjPl D.host P v') : v = v' := by
  apply HeightOneSpectrum.ext
  ext y
  obtain ⟨x, hx⟩ := (RingOfIntegers.mapRingEquiv D.host.conj.toRingEquiv).surjective y
  have hy : (y : D.host.E) = D.host.conj (x : D.host.E) := by
    rw [← hx]; rfl
  rw [← h x y hy, ← h' x y hy]

variable (bkP : BKPh X)

end GlobalTheory.TwSys.ResidualCompare

end
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL

theorem _root_.GlobalTheory.T.wachWeierstrass_test_and_density : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; (∀ (k : ℕ) (a : AA K LL), (∀ (i : Let K) (ζ : ↥LL.1), IsPrimitiveRoot ζ (l ^ s) → a ∈ van W i ζ k) → W.Q ^ k ∣ a) ∧ (∀ (k : ℕ) (a : AA K LL), (∀ (i : Let K) (ζ : ↥LL.1), ζ ^ (l ^ (s - 1)) = 1 → a ∈ van W i ζ k) → W.X ^ k ∣ a) ∧ (∀ (i : Let K) (ζ : ↥LL.1), (∃ j : ℕ, IsPrimitiveRoot ζ (l ^ j)) → ∀ (f : PowerSeries ↥LL.1) (m : ℕ), ∃ (a : AA K LL) (c : ↥LL.1), c ≠ 0 ∧ PowerSeries.X ^ m ∣ c • W.lev i ζ a - f) ∧ ∀ (i : Let K) (ζ : ↥LL.1), IsPrimitiveRoot ζ (l ^ s) → ∀ (f : PowerSeries ↥LL.1) (m : ℕ), ∃ (a : AA K LL) (c : ↥LL.1), c ≠ 0 ∧ PowerSeries.X ^ m ∣ c • W.lev i ζ a - f ∧ ∀ (i' : Let K) (ζ' : ↥LL.1), IsPrimitiveRoot ζ' (l ^ s) → (i', ζ') ≠ (i, ζ) → a ∈ van W i' ζ' m := by
  first | exact @GlobalTheory.NL.WDiv.weierstrass_dense | exact GlobalTheory.NL.WDiv.weierstrass_dense | (intros; apply GlobalTheory.NL.WDiv.weierstrass_dense <;> assumption)
end

section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module TensorProduct GlobalTheory.Pass

namespace GlobalTheory.CycBridge

theorem locChi_epsU_eq_cycLL : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)), Br.locChi D.nbr i w hw (epsU D.nd i) = cycLL (Br.PD D.loc D.nbr i w hw) (Br.LL D.nbr i w hw) :=
  fun D i w hw => MonoidHom.ext (GlobalTheory.CycBridge.locChi_epsU D i w hw)

end GlobalTheory.CycBridge
end

section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass GlobalTheory.Cut

theorem _root_.GlobalTheory.T.cyclotomicChar_unramified_away_from_ell : ∀ (D : D7) (i : D.nd.Loc) (v : HeightOneSpectrum (𝓞 D.host.E)), v ∉ placesOver D.host.E (D.nd.l i) → ∀ γ ∈ Ine (F := D.host.E) (D.nd.plOm.1 v), epsU D.nd i γ = 1 ∧ ∀ c, 1 ≤ c → c ≤ D.R.t → chiU D.nd i c γ = chiU D.nd i 1 γ := by
  first | exact @GlobalTheory.CycUnram.main | exact GlobalTheory.CycUnram.main | (intros; apply GlobalTheory.CycUnram.main <;> assumption)
end

section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module TensorProduct GlobalTheory.Pass
open scoped Pointwise

noncomputable section

namespace GlobalTheory.TypeDegOne

theorem fix_of_stabilizer_trivial {l : ℕ} [Fact l.Prime] {E : Type} [Field E] [NumberField E] [IsGalois ℚ E]
    (c : E →+* PadicAlgCl l) (P : Ideal (𝓞 E)) (hc : ∀ x : 𝓞 E, x ∈ P ↔ ‖c (x : E)‖ < 1)
    (hP : ∀ σ : E ≃ₐ[ℚ] E, σ • P = P → σ = 1) (τ : PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l) (x : E) :
    τ (c x) = c x := by
  letI : Algebra E (PadicAlgCl l) := c.toAlgebra
  haveI : IsScalarTower ℚ E (PadicAlgCl l) :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  let φ : E →ₐ[ℚ] PadicAlgCl l := ((τ : PadicAlgCl l →+* PadicAlgCl l).comp c).toRatAlgHom
  let σ : E ≃ₐ[ℚ] E := φ.restrictNormal' E
  have hσ : ∀ y, c (σ y) = τ (c y) := fun y => φ.restrictNormal_commutes E y
  have h1 : σ⁻¹ • P = P := by
    ext y
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, inv_inv, hc, hc]
    have e : ((σ • y : 𝓞 E) : E) = σ (y : E) := rfl
    have hn : ‖τ (c y)‖ = ‖c y‖ := (spectralNorm_eq_of_equiv τ _).symm
    rw [e, hσ, hn]
  have h2 : σ = 1 := inv_eq_one.1 (hP _ h1)
  rw [← hσ, h2]
  rfl

theorem eq_bot_of_subset_closure {l : ℕ} [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l))
    (S : Set (PadicAlgCl l)) (hK : (K : Set (PadicAlgCl l)) ⊆ closure S)
    (hS : ∀ (τ : PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l), ∀ y ∈ S, τ y = y) : K = ⊥ := by
  haveI : IsGalois ℚ_[l] (PadicAlgCl l) := IsAlgClosure.isGalois _ _
  refine eq_bot_iff.2 fun y hy => (InfiniteGalois.mem_bot_iff_fixed y).2 fun τ => ?_
  have hc : Continuous τ :=
    (AddMonoidHomClass.isometry_of_norm τ fun x => (spectralNorm_eq_of_equiv τ x).symm).continuous
  exact closure_minimal (fun y hy => hS τ y hy) (isClosed_eq hc continuous_id) (hK hy)

theorem mem_place_iff (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) (x : 𝓞 D.host.E) :
    x ∈ w.asIdeal ↔ ‖(D.nbr i w hw).j (algebraMap D.host.E D.nd.Om (x : D.host.E))‖ < 1 := by
  rw [← D.nd.plOm.2 w x]
  set y := algebraMap D.host.E D.nd.Om (x : D.host.E)
  by_cases hy : y = 0
  · simp [hy]
  have hj : 0 < ‖(D.nbr i w hw).j y‖ := norm_pos_iff.2 ((_root_.map_ne_zero _).2 hy)
  have h := D.nbr_ind i w hw y⁻¹
  rw [← ValuationSubring.valuation_le_one_iff, map_inv₀, map_inv₀, norm_inv, inv_le_one₀ hj,
    inv_le_one₀ (zero_lt_iff.2 ((_root_.map_ne_zero _).2 hy))] at h
  rw [← not_le, ← not_le, h]

theorem degree_one : ∀ (D : D7) (i : D.nd.Loc) (k : Fin 2), D.nd.l i = D.host.g k → (placesOver D.host.E (D.nd.l i)).ncard = 2 * D.R.f ∧ ∀ w (hw : w ∈ placesOver D.host.E (D.nd.l i)), finrank ℚ_[D.nd.l i] (Br.Kw D.nbr i w hw) = 1 := by
  intro D i k hk
  have hs : (placesOver D.host.E (D.nd.l i)).ncard = finrank ℚ D.host.E := by
    rw [hk]; exact D.nd.g_split k
  haveI : IsGalois ℚ D.host.E := D.host.hostE_isGalois
  refine ⟨?_, fun w hw => ?_⟩
  · have h1 : finrank ℚ D.host.E = 4 * D.R.ord := D.host.finrank_cmField
    have h5 : D.R.f = 2 * D.R.ord := rfl
    rw [hs, h1, h5]; ring
  · have hP := (GlobalTheory.Mem.Chr.splitsC_place (p := D.nd.l i) Fact.out hs w hw).2.2
    have hb : (D.nbr i w hw).Kw.1 = ⊥ := by
      refine eq_bot_of_subset_closure _ _ (D.nbr i w hw).j_dense ?_
      rintro τ _ ⟨x, rfl⟩
      exact fix_of_stabilizer_trivial ((D.nbr i w hw).j.comp (algebraMap D.host.E D.nd.Om)) w.asIdeal
        (mem_place_iff D i w hw) hP τ x
    exact IntermediateField.finrank_eq_one_iff.2 hb

end GlobalTheory.TypeDegOne

end
end

section

noncomputable section

open Matrix

namespace GlobalTheory.FlatConj

def gaussGL {k : Type} [Field k] [Fintype k] [DecidableEq k] (ψ : AddChar k ℂ) (ξ : kˣ →* ℂˣ) (r : ℕ) : ℂ :=
  ∑ x : GL (Fin r) k, (((ξ (Matrix.GeneralLinearGroup.det x))⁻¹ : ℂˣ) : ℂ) * ψ (Matrix.trace (x : Matrix (Fin r) (Fin r) k))

variable {E : Type} [Field E] [NumberField E]

def resField (PP : Formalism.L2.DIV.Pl E) : Field (Formalism.L2.DIV.kP PP) :=
  haveI := PP.isMaximal
  Ideal.Quotient.field PP.asIdeal

def resFintype (PP : Formalism.L2.DIV.Pl E) : Fintype (Formalism.L2.DIV.kP PP) :=
  haveI : Finite (Formalism.L2.DIV.kP PP) := Ideal.finiteQuotientOfFreeOfNeBot PP.asIdeal PP.ne_bot
  Fintype.ofFinite _

def gaussP (PP : Formalism.L2.DIV.Pl E) (ψ : AddChar (Formalism.L2.DIV.kP PP) ℂ) (ξ : (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (r : ℕ) : ℂ :=
  @gaussGL (Formalism.L2.DIV.kP PP) (resField PP) (resFintype PP) (Classical.decEq _) ψ ξ r

end GlobalTheory.FlatConj
end
end

section

open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef NumberField IsDedekindDomain GlobalTheory.EtaJoin

namespace GlobalTheory.NLocPlace

theorem vAdd_int (D : D7) (w : D.what₂.places.Pl) (a : 𝓞 D.what₂.LL) (ha : (a : D.what₂.LL) ≠ 0) :
    0 ≤ vAdd (D.plEq w) (a : D.what₂.LL) ∧ (a ∈ (D.plEq w).asIdeal ↔ 0 < vAdd (D.plEq w) (a : D.what₂.LL)) := by
  have hv0 : (D.plEq w).valuation D.what₂.LL (a : D.what₂.LL) ≠ 0 := (Valuation.ne_zero_iff _).2 ha
  have hle : (D.plEq w).valuation D.what₂.LL (algebraMap (𝓞 D.what₂.LL) D.what₂.LL a) ≤ 1 :=
    (D.plEq w).valuation_le_one a
  have hmem := (D.plEq w).valuation_lt_one_iff_mem (K := D.what₂.LL) a
  change (D.plEq w).valuation D.what₂.LL (a : D.what₂.LL) ≤ 1 at hle
  change (D.plEq w).valuation D.what₂.LL (a : D.what₂.LL) < 1 ↔ _ at hmem
  unfold vAdd
  rw [← WithZero.exp_log hv0, ← WithZero.exp_zero, WithZero.exp_le_exp] at hle
  rw [← WithZero.exp_log hv0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at hmem
  refine ⟨by omega, ?_⟩
  rw [← hmem]
  omega

end GlobalTheory.NLocPlace

namespace GlobalTheory.NLocPlace

theorem ec_int_resChar_unit : ∀ (D : D7) (M : MtFam D) (B : NLocBase D M) (j : ℕ) (w : D.what₂.places.Pl),
    (∀ a : 𝓞 D.what₂.LL, B.ec j w (a : D.what₂.LL) ∈ (algebraMap (B.Oc j w) (FractionRing (B.Oc j w))).range) ∧
    ((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL) ∈ (D.plEq w).asIdeal ∧
    ∀ (a : 𝓞 D.what₂.LL) (z : B.Oc j w), algebraMap (B.Oc j w) (FractionRing (B.Oc j w)) z = B.ec j w (a : D.what₂.LL) →
      (a ∈ (D.plEq w).asIdeal ↔ ¬ IsUnit z) := by
  intro D M B j w
  have hinj : Function.Injective (algebraMap (B.Oc j w) (FractionRing (B.Oc j w))) :=
    IsFractionRing.injective _ _

  have hval : ∀ x : D.what₂.LL, x ≠ 0 → D.what₂.places.val w x = ((vAdd (D.plEq w) x : ℤ) : WithTop ℤ) :=
    fun x hx => D.val_eq w x hx

  have hsum : ∀ x : D.what₂.LL, x ≠ 0 → vAdd (D.plEq w) x + vAdd (D.plEq w) x⁻¹ = 0 := by
    intro x hx
    have h1 : D.what₂.places.val w (x * x⁻¹) = 0 := by rw [mul_inv_cancel₀ hx, AddValuation.map_one]
    rw [AddValuation.map_mul, hval x hx, hval x⁻¹ (inv_ne_zero hx), ← WithTop.coe_add] at h1
    exact_mod_cast h1
  refine ⟨?_, ?_, ?_⟩
  · intro a
    apply (B.ec_w j w _).1
    by_cases ha : (a : D.what₂.LL) = 0
    · rw [ha, AddValuation.map_zero]; exact le_top
    · rw [hval _ ha]
      exact_mod_cast (vAdd_int D w a ha).1
  · have hp0 : (((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL) : D.what₂.LL) ≠ 0 := by
      push_cast; exact Nat.cast_ne_zero.2 (D.what₂.places.resChar_prime w).ne_zero
    rw [(vAdd_int D w _ hp0).2]
    have h1 := D.what₂.places.val_resChar w
    have hc : (((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL) : D.what₂.LL) = ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) := by
      push_cast; rfl
    rw [← hc, hval _ hp0] at h1
    have h2 : vAdd (D.plEq w) (((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL) : D.what₂.LL) = (D.what₂.places.ramIdx w : ℤ) :=
      WithTop.coe_injective h1
    rw [h2]
    exact_mod_cast D.what₂.places.ramIdx_pos w
  · intro a z hz
    by_cases ha : (a : D.what₂.LL) = 0
    · have ha' : a = 0 := by exact_mod_cast ha
      have hz0 : z = 0 := hinj (by rw [hz, ha, map_zero, map_zero])
      subst ha' hz0
      simp
    · have hec : B.ec j w (a : D.what₂.LL) ≠ 0 := by
        rw [map_ne_zero]; exact ha
      obtain ⟨hnn, hiff⟩ := vAdd_int D w a ha
      have hs := hsum _ ha
      rw [hiff]
      constructor
      · rintro hpos ⟨u, hu⟩
        have h1 : algebraMap (B.Oc j w) (FractionRing (B.Oc j w)) (↑u⁻¹ : B.Oc j w) = B.ec j w (a : D.what₂.LL)⁻¹ := by
          rw [map_inv₀, ← hz, ← hu]
          apply eq_inv_of_mul_eq_one_right
          rw [← map_mul, Units.mul_inv, map_one]
        have h2 := (B.ec_w j w (a : D.what₂.LL)⁻¹).2 ⟨_, h1⟩
        rw [hval _ (inv_ne_zero ha)] at h2
        have h3 : (0 : ℤ) ≤ vAdd (D.plEq w) (a : D.what₂.LL)⁻¹ := by exact_mod_cast h2
        omega
      · intro hnu
        by_contra hle
        have h0 : vAdd (D.plEq w) (a : D.what₂.LL)⁻¹ = 0 := by omega
        have h2 : 0 ≤ D.what₂.places.val w (a : D.what₂.LL)⁻¹ := by
          rw [hval _ (inv_ne_zero ha), h0]; rfl
        obtain ⟨y, hy⟩ := (B.ec_w j w _).1 h2
        apply hnu
        have hzy : z * y = 1 := hinj (by rw [map_mul, map_one, hz, hy, ← map_mul, mul_inv_cancel₀ ha, map_one])
        exact ⟨⟨z, y, hzy, by rw [mul_comm]; exact hzy⟩, rfl⟩

end GlobalTheory.NLocPlace
end

section

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.WeaklyAdmissibleFiltrations

namespace GlobalTheory

theorem charpoly_span_and_hom_relations_of_admissible : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i), TruncatedSeriesCountingIdentities.admG1 i r → LargeLevelLemmas.CharpolyCoeffsLemmaFamily i r ∧ LargeLevelLemmas.SpanQuotientLemma i r ρ π ∧ LargeLevelLemmas.HomRelationsLemmaAllChoices i r ρ π :=
  fun _ i r ρ π h => ⟨LargeLevelLemmas.span_lemma_clause i r h, LargeLevelLemmas.eigenspace_lemma_clause i r ρ π, LargeLevelLemmas.relation_lemma_clause i r ρ π⟩

end GlobalTheory
end

section

open GlobalTheory.TypeLeaf Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.tameGenerator_image_eq_coprime_pow : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (γ γ' : G E Ω), TameGenAt A γ → TameGenAt A γ' → ∀ (M : Type) [Group M] (φ : G E Ω →* M), IsOpen (φ.ker : Set (G E Ω)) → (∀ s : G E Ω, (∀ y : Ω, y ≠ 0 → A.valuation (s y / y - 1) < 1) → φ s = 1) → ∃ n : ℕ, n.Coprime (orderOf (φ γ)) ∧ 0 < orderOf (φ γ) ∧ φ γ' = φ γ ^ n := by
  first | exact @GlobalTheory.TypeLeaf.tameGen_pow | exact GlobalTheory.TypeLeaf.tameGen_pow | (intros; apply GlobalTheory.TypeLeaf.tameGen_pow <;> assumption)
end
