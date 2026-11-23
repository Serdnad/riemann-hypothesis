module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1692
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeasureToRealEqMass
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle035
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.EllipticPartTestData
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EventuallyAlgebraMapMemIntegers
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle261
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FlatSpaceComponents
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle274
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle282
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GluedHermitianLatticeUnique
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle277
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle279
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset
import Aesop.Main
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle314
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RowDictPf
public import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
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
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle245
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle136

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory Formalism.L2.Theta
open Formalism.IndefR
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DefiniteClassSum

theorem invariant_sup {G X : Type} [Group G] {A B : Subgroup G} {Φ : G → X} (hA : ∀ k ∈ A, ∀ h, Φ (h * k) = Φ h)
    (hB : ∀ k ∈ B, ∀ h, Φ (h * k) = Φ h) : ∀ k ∈ A ⊔ B, ∀ h, Φ (h * k) = Φ h := by
  let S : Subgroup G :=
    { carrier := {k | ∀ h, Φ (h * k) = Φ h}
      mul_mem' := fun {a b} ha hb h => by rw [← mul_assoc, hb, ha]
      one_mem' := fun h => by rw [mul_one]
      inv_mem' := fun {a} ha h => by rw [← ha (h * a⁻¹), inv_mul_cancel_right] }
  exact fun k hk => (sup_le (show A ≤ S from hA) (show B ≤ S from hB) : A ⊔ B ≤ S) hk

theorem integral_eq_sum {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
    [BorelSpace G] [Group H] (ν : Measure G) [ν.IsMulLeftInvariant] (π : G →* H) (Γ : Subgroup G) [Countable Γ] {𝓖 : Set G}
    (h𝓖 : IsFundamentalDomain Γ 𝓖 ν) (J : Subgroup H) (ho : IsOpen (J.comap π : Set G)) (h1 : ν (J.comap π) = 1)
    {I : Type} [Fintype I] (y : I → H) (hy : Bridge.IsReps (π.comp Γ.subtype) J y) (a : I → G) (ha : ∀ i, π (a i) = y i)
    (Φ : G → ℂ) (hl : ∀ γ ∈ Γ, ∀ h, Φ (γ * h) = Φ h) (hr : ∀ k ∈ J.comap π, ∀ h, Φ (h * k) = Φ h) :
    (∀ i, Finite (Bridge.stab (π.comp Γ.subtype) J (y i))) ∧ IntegrableOn Φ 𝓖 ν ∧
      ∫ h in 𝓖, Φ h ∂ν = ∑ i, ((Nat.card (Bridge.stab (π.comp Γ.subtype) J (y i)) : ℂ))⁻¹ * Φ (a i) := by
  have hs : ∀ i, (Bridge.stab (π.comp Γ.subtype) J (y i) : Set Γ) = {γ : Γ | (a i)⁻¹ * (γ : G) * a i ∈ J.comap π} := by
    intro i
    ext γ
    rw [SetLike.mem_coe, Bridge.mem_stab, Set.mem_setOf_eq, Subgroup.mem_comap, map_mul, map_mul, map_inv, ha]
    rfl
  have hfin : ∀ i, {γ : Γ | (a i)⁻¹ * (γ : G) * a i ∈ J.comap π}.Finite := fun i =>
    GlobalTheory.InnerClassSum.finite_stab_of_measure ν Γ _ h𝓖 (h1 ▸ one_ne_zero) (h1 ▸ ENNReal.one_ne_top) (a i)
  have him : ∀ i, {γ : G | γ ∈ Γ ∧ (a i)⁻¹ * γ * a i ∈ J.comap π} =
      Subtype.val '' {γ : Γ | (a i)⁻¹ * (γ : G) * a i ∈ J.comap π} := by
    intro i
    ext γ
    simp only [Set.mem_setOf_eq, Set.mem_image, Subtype.exists, exists_and_right, exists_eq_right]
    exact ⟨fun h => ⟨h.1, h.2⟩, fun ⟨h, h'⟩ => ⟨h, h'⟩⟩
  have hu : ∀ x : G, ∃! i, ∃ γ ∈ Γ, ∃ k ∈ J.comap π, x = γ * a i * k := by
    intro x
    refine (existsUnique_congr fun i => ?_).1 (hy (π x))
    constructor
    · rintro ⟨γ, k, e⟩
      refine ⟨γ, γ.2, ((γ : G) * a i)⁻¹ * x, ?_, by group⟩
      rw [Subgroup.mem_comap, map_mul, map_inv, map_mul, ha, e]
      change (π γ * y i)⁻¹ * (π γ * y i * k) ∈ J
      rw [inv_mul_cancel_left]
      exact k.2
    · rintro ⟨γ, hγ, k, hk, rfl⟩
      exact ⟨⟨γ, hγ⟩, ⟨π k, hk⟩, by rw [map_mul, map_mul, ha]; rfl⟩
  obtain ⟨-, hi, he⟩ := GlobalTheory.Ker.integral_fundamentalDomain_eq_sum_doubleCoset G ν Γ (J.comap π) 𝓖 h𝓖 ho
    (h1 ▸ ENNReal.one_ne_top) I a hu (fun i => him i ▸ (hfin i).image _) Φ hl hr
  refine ⟨fun i => ?_, hi, ?_⟩
  · have := hfin i
    rw [← hs] at this
    exact this
  · rw [he, h1]
    simp only [ENNReal.toReal_one, Complex.ofReal_one, one_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [him, Set.ncard_image_of_injective _ Subtype.val_injective, ← hs, ← Nat.card_coe_set_eq]
    rfl

theorem classSumIntegral : GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.ClassSumIntegral := by
  intro D V _ K hK μ 𝓕 hμ I _ y hy z hz Φ hΦ
  have hT := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  have hB := hT.2.2.2.1
  have hG := hT.2.2.2.2.1
  have hC := hT.2.2.2.2.2.2
  have := hμ.1.1
  have hr : ∀ k ∈ K.comap (Lev.finE V), ∀ h, Φ (h * k) = Φ h := by
    rw [GlobalTheory.Mass.Levels.comap_finE]
    exact invariant_sup hΦ.level hΦ.real
  have ho : IsOpen (((GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.levelFin V K).comap (finHom V).rangeRestrict : Subgroup (GA D V)) : Set (GA D V)) := hK.1
  have h1 : μ ((GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.levelFin V K).comap (finHom V).rangeRestrict : Subgroup (GA D V)) = 1 :=
    GlobalTheory.Mass.Levels.measure_comap_finE hμ.1
  exact integral_eq_sum μ (finHom V).rangeRestrict (GQ V) hμ.2 (GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.levelFin V K) ho h1 y hy z hz Φ hΦ.left hr

end GlobalTheory.DefiniteClassSum
end

section

open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

noncomputable section

namespace GlobalTheory.TrUnitLat
theorem alpha_mem_stab : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (r : ℕ) (P : PPol σ r), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, diagH (star' P) (one₁ P) (Fv F v) (alphaRat P) ∈ stabLoc (star' P) (one₁ P) (stdLattice (Fld P) 1) v := by
  intro F E _ _ _ _ _ σ r P
  filter_upwards [eventually_one_tmul_mem_intLoc (F := F) (alpha P),
    eventually_one_tmul_mem_intLoc (F := F) (alpha P)⁻¹] with v h1 h2
  have e0 : ∀ Y : Fin 1 → Fv F v ⊗[F] Fld P,
      (matHom _ (star' P) (one₁ P) (diagH (star' P) (one₁ P) (Fv F v) (alphaRat P))).1 *ᵥ Y ∈
        latLoc F (stdLattice (Fld P) 1) v ↔ (1 : Fv F v) ⊗ₜ[F] alpha P * Y 0 ∈ intLoc F (Fld P) v := fun Y => by
    have e : (matHom _ (star' P) (one₁ P) (diagH (star' P) (one₁ P) (Fv F v) (alphaRat P))).1 0 0 =
        (1 : Fv F v) ⊗ₜ[F] alpha P := rfl
    rw [mem_latLoc_stdLattice, Fin.forall_fin_one, ← e]
    simp [Matrix.mulVec, dotProduct]
  have hinv : (1 : Fv F v) ⊗ₜ[F] (alpha P)⁻¹ * (1 : Fv F v) ⊗ₜ[F] alpha P = 1 := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, inv_mul_cancel₀ (alpha_ne_zero P), Algebra.TensorProduct.one_def]
  refine mem_stabLoc.2 fun Y => ?_
  rw [e0, mem_latLoc_stdLattice, Fin.forall_fin_one]
  refine ⟨mul_mem h1, fun hY => ?_⟩
  have := mul_mem h2 hY
  rwa [← mul_assoc, hinv, one_mul] at this

theorem stab_torEmb_iff : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (r n : ℕ) (P : PPol σ r) (v : HeightOneSpectrum (𝓞 F)) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)) (x : Fv F v ⊗[F] Fld P) (φ : (Fv F v ⊗[F] Fld P) ≃ₗ[Fv F v ⊗[F] E] (Fin n → Fv F v ⊗[F] E)) (h : IsIsom P (Fv F v) J x φ), (∀ y, y ∈ intLoc F (Fld P) v ↔ φ y ∈ latLoc F L v) → ∀ t, torEmb h t ∈ stabLoc σ J L v ↔ t ∈ stabLoc (star' P) (one₁ P) (stdLattice (Fld P) 1) v := by
  intro F E _ _ _ _ σ r n P v J L x φ h hφ t
  have e1 : (matHom _ σ J (torEmb h t)).1 = mulMat φ (torUnit t).1 := rfl
  have e0 : (torUnit t).1 = t.1.1 0 0 := Matrix.det_fin_one _
  have e2 : ∀ Y : Fin 1 → Fv F v ⊗[F] Fld P,
      (matHom _ (star' P) (one₁ P) t).1 *ᵥ Y ∈ latLoc F (stdLattice (Fld P) 1) v ↔
        (torUnit t).1 * Y 0 ∈ intLoc F (Fld P) v := fun Y => by
    rw [mem_latLoc_stdLattice, Fin.forall_fin_one, e0]
    simp [Matrix.mulVec, dotProduct, matHom]
    exact Iff.rfl
  rw [mem_stabLoc, mem_stabLoc]
  constructor
  · intro H Y
    rw [e2, mem_latLoc_stdLattice, Fin.forall_fin_one]
    have := H (φ (Y 0))
    rwa [e1, mulMat_mulVec, ← hφ, ← hφ] at this
  · intro H Y
    obtain ⟨y, rfl⟩ := φ.surjective Y
    rw [e1, mulMat_mulVec, ← hφ, ← hφ]
    have := H (fun _ => y)
    rwa [e2, mem_latLoc_stdLattice, Fin.forall_fin_one] at this

end GlobalTheory.TrUnitLat

namespace GlobalTheory.TrUnitLat

theorem hform_mulVec' {A : Type} [CommRing A] (s : A →+* A) {n : ℕ} (J k : Matrix (Fin n) (Fin n) A) (a b : Fin n → A) :
    Formalism.UG.hform s J (k *ᵥ a) (k *ᵥ b) = Formalism.UG.hform s (Formalism.UG.cT s k * J * k) a b := by
  have e2 : ∀ (J : Matrix (Fin n) (Fin n) A) a b, Formalism.UG.hform s J a b = (s ∘ a) ⬝ᵥ J *ᵥ b := by
    intro J a b
    simp only [Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, Function.comp_apply, mul_assoc]
  have e3 : s ∘ (k *ᵥ a) = (s ∘ a) ᵥ* Formalism.UG.cT s k := by
    funext i
    rw [Formalism.UG.cT, Matrix.vecMul_transpose, Function.comp_apply, RingHom.map_mulVec]
  rw [e2, e2, e3, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

theorem eventually_unitClass_isom : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (r : ℕ) (P : PPol σ r) (J : Matrix (Fin r) (Fin r) E), IsHermND σ J → ∀ (L : Submodule (𝓞 E) (Fin r → E)) [Submodule.IsFullLattice E L], ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, ∃ (φ : (Fv F v ⊗[F] Fld P) ≃ₗ[Fv F v ⊗[F] E] (Fin r → Fv F v ⊗[F] E)) (h : IsIsom P (Fv F v) J (1 : plusUnits P (Fv F v)).1.1 φ), gam h ∈ stabLoc σ J L v ∧ ∀ t, torEmb h t ∈ stabLoc σ J L v ↔ t ∈ stabLoc (star' P) (one₁ P) (stdLattice (Fld P) 1) v := by
  intro F E _ _ _ _ _ σ hcm r P J hJ L _
  have := isLattice_stdLattice (E := E) (n := r)
  filter_upwards [GlobalTheory.T.traceFormGramPowerBasis_hermitian_nondegenerate F E σ hcm r P |> fun hH => GlobalTheory.T.eventually_hermitian_integrally_congruent_cmExt F E σ hcm r J (gramOne P) hJ hH,
    eventually_latLoc_eq F L (stdLattice E r), GlobalTheory.T.eventually_localIntegers_iff_powerBasisCoords_all F E σ r P, GlobalTheory.TrUnitLat.alpha_mem_stab F E σ r P] with v hu hL h3 h4
  obtain ⟨u, hu, hul⟩ := hu
  let φ : (Fv F v ⊗[F] Fld P) ≃ₗ[Fv F v ⊗[F] E] (Fin r → Fv F v ⊗[F] E) :=
    (coordEquiv P (Fv F v)).trans (Matrix.toLinearEquiv' u.1 (Units.invertible u))
  have eφ : ∀ y, φ y = u.1 *ᵥ coordEquiv P (Fv F v) y := fun y => rfl
  have hφ : IsIsom P (Fv F v) J (1 : plusUnits P (Fv F v)).1.1 φ := fun y y' => by
    rw [eφ, eφ, hform_mulVec', hu]
    exact GlobalTheory.T.powerBasisCoords_isTorusHermitianIsometry F E σ r P (Fv F v) y y'
  have h5 : ∀ y, y ∈ intLoc F (Fld P) v ↔ φ y ∈ latLoc F L v := fun y => by
    rw [eφ, hL, hul, h3]
  exact ⟨φ, hφ, (GlobalTheory.TrUnitLat.stab_torEmb_iff F E σ r r P v J L _ φ hφ h5 _).2 h4, GlobalTheory.TrUnitLat.stab_torEmb_iff F E σ r r P v J L _ φ hφ h5⟩

end GlobalTheory.TrUnitLat
end
end

section

open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

theorem _root_.GlobalTheory.T.unitaryTorus_equiv_centralizer_with_measure : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (r n : ℕ) (P : PPol σ r) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (k : Type) [CommRing k] [Algebra F k] [TopologicalSpace k] [IsTopologicalRing k] [T2Space k] (x : plusUnits P k) (φ : (k ⊗[F] Fld P) ≃ₗ[k ⊗[F] E] (Fin n → k ⊗[F] E)) (h : IsIsom P k J x.1.1 φ), ∃ e : Tor P k ≃ₜ* cent (gam h), (∀ t, (e t).1 = torEmb h t) ∧ ∀ dt : Measure (Tor P k), centMeas h dt = dt.map e := by
  first | exact @GlobalTheory.TorCentTop.torEquiv_cent | exact GlobalTheory.TorCentTop.torEquiv_cent | (intros; apply GlobalTheory.TorCentTop.torEquiv_cent <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Matrix
open Formalism.L2.DIV (Pl)
open Formalism.IndefR.Lev (EAf)
open Formalism.IndefR.Datum (IsSelfDualC)
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents GlobalTheory.AdIsom
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.correctionSt_of_transportSt : ∀ D : D7, TransportSt D → CorrectionSt D := by
  first | exact @GlobalTheory.AdIsomCorrection.correction_of_transport | exact GlobalTheory.AdIsomCorrection.correction_of_transport | (intros; apply GlobalTheory.AdIsomCorrection.correction_of_transport <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Matrix
open Formalism.L2.DIV (Pl)
open Formalism.IndefR.Lev (EAf)
open Formalism.IndefR.Datum (IsSelfDualC)
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents GlobalTheory.AdIsom
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.adelicIsometry_transport_unique_mod_stabilizer : ∀ (D : D7) (W Y : HSp D) (L : Lat W) (Λ : Lat Y) (S : Finset (Pl D.host.E)), IsSplitSet S → ∀ (n : ℕ) (be : Pl D.host.E → Matrix (Fin W.rank) (Fin n) (EAf D)) (be' : Pl D.host.E → Matrix (Fin Y.rank) (Fin n) (EAf D)), Submodule.IsFullLattice D.host.E L → (∀ w ∈ S, IsBasisAt W w L (be w)) → ∀ x, IsTransport W Y L Λ S be be' x → ∀ x', IsTransport W Y L Λ S be be' x' ↔ ∃ k, InStabAway W L S k ∧ x' = HMul.hMul x (k.1 : Matrix (Fin W.rank) (Fin W.rank) (EAf D)) := by
  intro D W Y L Λ S hS n be be' hL hbe x hx x'
  first
  | exact GlobalTheory.TransportUnique.transport_unique D W Y L Λ S hS n be be' hL hbe x hx x'
  | exact GlobalTheory.TransportUnique.transport_unique D W Y L Λ S hS n be be' hL.toIsLattice hbe x hx x' 
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Matrix
open Formalism.L2.DIV (Pl)
open Formalism.IndefR.Lev (EAf)
open Formalism.IndefR.Datum (IsSelfDualC)
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents GlobalTheory.AdIsom
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.gluedHermitianLattice_unique : ∀ (D : D7) (u : D.what₂.Word) (π : 𝓞 D.host.E), IsPi u π → ∀ (Y X : HSp D) (ι : X.V →ₗ[D.host.E] Y.V) (z : Y.V) (L₀ : Lat X) (f₀ : Pl D.host.E → Fin X.rank → EAf D) (L L' : Submodule (𝓞 D.host.E) Y.V), IsGlued Y X ι z u π L₀ f₀ L → IsGlued Y X ι z u π L₀ f₀ L' → L = L' := by
  first | exact @GlobalTheory.GlueUnique.glued_unique | exact GlobalTheory.GlueUnique.glued_unique | (intros; apply GlobalTheory.GlueUnique.glued_unique <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.conjPart_mem_completedSelfDualLattice_iff_splitPlace : ∀ (D : D7) (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (β : GL (Fin V.rank) (EAf D)), IsSelfDualC V Λ → Formalism.L2.DIV.IsFrame β Λ → ∀ (v : FinPl D) (φ : SplitProj D v) (e : AE D), IsIdemOf φ e → ∀ y : Fin V.rank → AE D, (fun i => finPart D (cA D e * y i)) ∈ Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (Λ : Set (Fin V.rank → D.host.E)) ↔ ∀ j, Valued.v (((fun i => rdA φ (cA D (y i))) ᵥ* ((V.gram.map (rdQ φ)) * (frCo φ β).1)) j) ≤ 1 := by
  first | exact @GlobalTheory.SplitRowLat.conj_mem_latHat_iff | exact GlobalTheory.SplitRowLat.conj_mem_latHat_iff | (intros; apply GlobalTheory.SplitRowLat.conj_mem_latHat_iff <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.GoodProjEval

open GlobalTheory.Mem.SRe Formalism.L2.SG.Pf.unitaryCongruence

theorem multR_left_inv {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)
    (v₀ : (MP R).Vec) (S : MMap (MP R)) (hS : S ∈ MultR R F) :
    ∀ γ ∈ GQ (D.sp.Y 0), ∀ g, S v₀ (γ * g) = S v₀ g := by
  intro γ hγ g
  induction hS using Submodule.span_induction with
  | mem x hx => exact (hx.aut v₀).left γ hγ g
  | zero => rfl
  | add x y _ _ hx hy =>
    show x v₀ (γ * g) + y v₀ (γ * g) = x v₀ g + y v₀ g
    rw [hx, hy]
  | smul c x _ hx =>
    show c • x v₀ (γ * g) = c • x v₀ g
    rw [hx]

theorem goodOp_star_ev : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → ∀ (Gd : GoodOp X) (t : GA D (Yc D 0)) (v₀ : (MP R).Vec), RowLevelMatchAt R F X h t → ∀ S ∈ Mult R.θ (R.MY 0) (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))), ∀ φ : L2X X, φ =ᵐ[muX X] (fun x => ev (MP R) v₀ S (@HMul.hMul (GA D (Yc D 0)) (GA D (Yc D 0)) (GA D (Yc D 0)) _ ((iotaX X h).symm x) t)) → (star (Gd.Rg (star φ)) : L2X X) =ᵐ[muX X] (fun x => ev (MP R) v₀ (postOn (MP R) R.e0 S) (@HMul.hMul (GA D (Yc D 0)) (GA D (Yc D 0)) (GA D (Yc D 0)) _ ((iotaX X h).symm x) t)) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F X h _ _ _ Gd t v₀ hM S hS φ hφ
  obtain ⟨σ, red, -, hB, hC⟩ := hM
  letI : Fintype (G0g D.nd) := Fintype.ofEquiv G σ.symm.toEquiv
  obtain ⟨hgood, hmul, hsurj, hker⟩ := hB.1
  choose s hsK hsred using hsurj
  have hinv := multR_left_inv R F v₀ S hS
  have hEv := evalAct_intertwines D G Pl0 T A Ks R F X h t v₀ σ red hB S hS φ hφ hinv

  have hF1 : ∀ k ∈ X.B.I.Kset, X.B.R (1, k) (star φ) = X.B.R (1, s (red k)) (star φ) := by
    intro k hk
    classical
    let a : G0g D.nd → ℂ := fun γ => if γ = red k then 1 else 0
    let s' : G0g D.nd → X.B.I.Gf := Function.update s (red k) k
    have hs' : ∀ γ, s' γ ∈ X.B.I.Kset ∧ red (s' γ) = γ := by
      intro γ
      by_cases hγ : γ = red k
      · subst hγ
        simp only [s', Function.update_self]
        exact ⟨hk, trivial⟩
      · simp only [s', Function.update_of_ne hγ]
        exact ⟨hsK γ, hsred γ⟩
    have e1 := hEv a s' hs'
    have e2 := hEv a s (fun γ => ⟨hsK γ, hsred γ⟩)
    have hsum : ∀ u : G0g D.nd → X.B.I.Gf,
        (∑ γ, star (a γ) • star (X.B.R (1, u γ) (star φ)) : L2X X) = star (X.B.R (1, u (red k)) (star φ)) := by
      intro u
      rw [Finset.sum_eq_single (red k)]
      · simp [a]
      · intro γ _ hγ
        simp [a, hγ]
      · intro hn
        exact absurd (Finset.mem_univ _) hn
    rw [hsum] at e1 e2
    have e3 : star (X.B.R (1, k) (star φ)) = (star (X.B.R (1, s (red k)) (star φ)) : L2X X) := by
      apply Lp.ext
      have : s' (red k) = k := by simp [s']
      rw [this] at e1
      exact e1.trans e2.symm
    exact star_injective e3

  have hKgK : X.B.I.Kg X.B.g ⊆ X.B.I.Kset := fun x hx => hx.1
  have hKgO : IsOpen (X.B.I.Kg X.B.g) :=
    X.B.I.topf_open X.B.g (Nat.one_le_iff_ne_zero.2 (Formalism.L2.SG.Pf.RowDictPf.level_ne_zero X))
  have h1Kg : (1 : X.B.I.Gf) ∈ X.B.I.Kg X.B.g := by
    rw [← hker 1 (K_one _)]
    have := hmul 1 (K_one _) 1 (K_one _)
    rw [mul_one] at this
    exact left_eq_mul.mp this
  have hvol_pos : 0 < X.B.μf (X.B.I.Kg X.B.g) := hKgO.measure_pos X.B.μf ⟨1, h1Kg⟩
  have hvol_fin : X.B.μf (X.B.I.Kg X.B.g) < ⊤ :=
    lt_of_le_of_lt (measure_mono hKgK) ((Formalism.L2.SG.Closed.AutKCompact_holds X.B.I).measure_lt_top)
  set C : G0g D.nd → Set X.B.I.Gf := fun γ => (fun y => (s γ)⁻¹ * y) ⁻¹' X.B.I.Kg X.B.g with hCdef
  have hCmem : ∀ γ k, k ∈ C γ ↔ k ∈ X.B.I.Kset ∧ red k = γ := by
    intro γ k
    show (s γ)⁻¹ * k ∈ X.B.I.Kg X.B.g ↔ _
    constructor
    · intro hk'
      have hk2 : k = s γ * ((s γ)⁻¹ * k) := by group
      have hKk : k ∈ X.B.I.Kset := by rw [hk2]; exact K_mul _ (hsK γ) (hKgK hk')
      refine ⟨hKk, ?_⟩
      rw [hk2, hmul _ (hsK γ) _ (hKgK hk'), (hker _ (hKgK hk')).2 hk', mul_one, hsred]
    · rintro ⟨hKk, hrk⟩
      have hK' : (s γ)⁻¹ * k ∈ X.B.I.Kset := K_mul _ (K_inv _ (hsK γ)) hKk
      refine (hker _ hK').1 ?_
      have := hmul (s γ) (hsK γ) _ hK'
      rw [mul_inv_cancel_left, hrk, hsred] at this
      exact (left_eq_mul.mp this)
  have hCmeas : ∀ γ, MeasurableSet (C γ) := fun γ =>
    (hKgO.preimage (continuous_const.mul continuous_id)).measurableSet
  have hCvol : ∀ γ, X.B.μf (C γ) = X.B.μf (X.B.I.Kg X.B.g) := fun γ =>
    measure_preimage_mul X.B.μf _ _

  set vol : ℝ := (X.B.μf (X.B.I.Kg X.B.g)).toReal with hvol
  have hvol0 : (vol : ℂ) ≠ 0 := by
    rw [hvol]
    exact_mod_cast (ENNReal.toReal_pos hvol_pos.ne' hvol_fin.ne).ne'
  have hRg : Gd.Rg (star φ) = ∑ γ, D.ntypes.e0.coeff γ • X.B.R (1, s γ) (star φ) := by
    apply ext_inner_left ℂ
    intro x
    rw [Gd.Rg_spec.2 x (star φ), inner_sum]
    simp_rw [inner_smul_right]
    have hpt : ∀ k, eg X k * ⟪x, X.B.R (1, k) (star φ)⟫_ℂ =
        ∑ γ, (C γ).indicator (fun _ => D.ntypes.e0.coeff γ / (vol : ℂ) * ⟪x, X.B.R (1, s γ) (star φ)⟫_ℂ) k := by
      intro k
      by_cases hk : k ∈ X.B.I.Kset
      · have hgk := hgood k hk
        have heg : eg X k = D.ntypes.e0.coeff (red k) / (vol : ℂ) := by
          unfold eg
          rw [dite_eq_left ⟨hk, ⟨red k, hgk⟩⟩]
          congr 1
          exact Formalism.L2.SG.Pf.rowDictEgWellDef_holds X k _ _ (Classical.choose_spec _) hgk
        rw [Finset.sum_eq_single (red k)]
        · rw [Set.indicator_of_mem ((hCmem _ k).2 ⟨hk, rfl⟩), heg, hF1 k hk]
        · intro γ _ hγ
          exact Set.indicator_of_notMem (fun hm => hγ ((hCmem γ k).1 hm).2.symm) _
        · intro hn
          exact absurd (Finset.mem_univ _) hn
      · have heg : eg X k = 0 := by
          unfold eg
          rw [dite_eq_right (fun h' => hk h'.1)]
        rw [heg, zero_mul]
        symm
        refine Finset.sum_eq_zero fun γ _ => Set.indicator_of_notMem (fun hm => hk ((hCmem γ k).1 hm).1) _
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
    rw [integral_finsetSum _ (fun γ _ => (integrable_indicator_iff (hCmeas γ)).2
      (integrableOn_const (by rw [hCvol]; exact hvol_fin.ne)))]
    refine Finset.sum_congr rfl fun γ _ => ?_
    rw [integral_indicator_const _ (hCmeas γ), Measure.real, hCvol, ← hvol, Complex.real_smul]
    field_simp

  have hstar : (star (Gd.Rg (star φ)) : L2X X) =
      ∑ γ, star (D.ntypes.e0.coeff γ) • star (X.B.R (1, s γ) (star φ)) := by

    rw [← conjL_apply (muX X), hRg, map_sum]
    refine Finset.sum_congr rfl fun γ _ => ?_
    rw [LinearIsometryEquiv.map_smulₛₗ, conjL_apply]
    rfl
  rw [hstar]
  refine (hEv (fun γ => D.ntypes.e0.coeff γ) s (fun γ => ⟨hsK γ, hsred γ⟩)).trans
    (Filter.Eventually.of_forall fun x => ?_)
  have hc : (fun g => star (D.ntypes.e0.coeff (σ.symm g))) = RealDat.eC (A := A) D.what₂.embLL := by
    funext g
    rw [hC (σ.symm g), MulEquiv.apply_symm_apply]
  show gaL (Yc D 0) (R.βY 0) (R.dat0 R.triv) R.eG (fun g => star (D.ntypes.e0.coeff (σ.symm g))) (S v₀) _ =
    R.e0 (S v₀) _
  rw [hc]
  rfl

end GlobalTheory.GoodProjEval
end
end

section

open GlobalTheory.FunObj

namespace GlobalTheory

theorem chainTo_update_of_le {V : ℕ → Type} [∀ j, AddCommGroup (V j)] [∀ j, Module ℂ (V j)]
    (k : ∀ j, V j →ₗ[ℂ] V (j + 1)) (j₀ : ℕ) (A : V j₀ →ₗ[ℂ] V (j₀ + 1)) :
    ∀ n, n ≤ j₀ → chainTo (Function.update k j₀ A) n = chainTo k n
  | 0, _ => rfl
  | n + 1, h => by
    show Function.update k j₀ A n ∘ₗ chainTo (Function.update k j₀ A) n = k n ∘ₗ chainTo k n
    rw [Function.update_of_ne (by omega : n ≠ j₀), chainTo_update_of_le k j₀ A n (by omega)]

theorem chainTo_update_succ {V : ℕ → Type} [∀ j, AddCommGroup (V j)] [∀ j, Module ℂ (V j)]
    (k : ∀ j, V j →ₗ[ℂ] V (j + 1)) (j₀ : ℕ) (A : V j₀ →ₗ[ℂ] V (j₀ + 1)) :
    chainTo (Function.update k j₀ A) (j₀ + 1) = A ∘ₗ chainTo k j₀ := by
  show Function.update k j₀ A j₀ ∘ₗ chainTo (Function.update k j₀ A) j₀ = _
  rw [Function.update_self, chainTo_update_of_le k j₀ A j₀ le_rfl]

theorem chainTo_update_add : ∀ {V : ℕ → Type} [∀ j, AddCommGroup (V j)] [∀ j, Module ℂ (V j)] (k : ∀ j, V j →ₗ[ℂ] V (j + 1)) (j₀ : ℕ)
    (A B : V j₀ →ₗ[ℂ] V (j₀ + 1)) (n : ℕ), j₀ < n →
    chainTo (Function.update k j₀ (A + B)) n = chainTo (Function.update k j₀ A) n + chainTo (Function.update k j₀ B) n := by
  intro V _ _ k j₀ A B n hn
  induction n, hn using Nat.le_induction with
  | base =>
    rw [chainTo_update_succ, chainTo_update_succ, chainTo_update_succ, LinearMap.add_comp]
  | succ n hn ih =>
    show Function.update k j₀ (A + B) n ∘ₗ chainTo (Function.update k j₀ (A + B)) n =
      Function.update k j₀ A n ∘ₗ chainTo (Function.update k j₀ A) n + Function.update k j₀ B n ∘ₗ chainTo (Function.update k j₀ B) n
    have hne : n ≠ j₀ := by omega
    rw [Function.update_of_ne hne, Function.update_of_ne hne, Function.update_of_ne hne, ih, LinearMap.comp_add]

end GlobalTheory
end
