module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle083
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle073
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle100
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle084
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIndexIdeal
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NontrivialOfIrreducible
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Formalism.AlgebraicWeights.InertDatumExists
public import Formalism.LocalRingCardinality.Bundle002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle096
public import Formalism.LocalToGlobal.Columns.GenericUnipotentCharacter
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.Columns.GoodXgFin
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle102
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle047
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.Bundle001
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx.FibProp

section Alg

variable {A : Type} [CommRing A] {n : ℕ} (s : A →+* A) (J : Matrix (Fin n) (Fin n) A)

theorem form_eq (x y : Fin n → A) :
    Formalism.UG.hform s J x y = dotProduct (fun i => s (x i)) (J.mulVec y) := by
  simp only [Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem form_mulVec {g : Matrix (Fin n) (Fin n) A} (hg : Formalism.UG.cT s g * J * g = J) (x y : Fin n → A) :
    Formalism.UG.hform s J (g.mulVec x) (g.mulVec y) = Formalism.UG.hform s J x y := by
  have e : (fun i => s (g.mulVec x i)) = Matrix.vecMul (fun i => s (x i)) (Formalism.UG.cT s g) := by
    funext i

    simp only [Matrix.mulVec, Matrix.vecMul, dotProduct, map_sum, map_mul, Formalism.UG.cT, Matrix.transpose_apply,
    Matrix.map_apply, mul_comm]
  rw [form_eq, form_eq, e, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hg]

theorem form_smul (a : A) (x : Fin n → A) :
    Formalism.UG.hform s J (a • x) (a • x) = s a * a * Formalism.UG.hform s J x x := by
  simp only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem det_norm {g : Matrix (Fin n) (Fin n) A} (hJ : IsUnit J.det) (hg : Formalism.UG.cT s g * J * g = J) :
    g.det * s g.det = 1 := by
  have h := congrArg Matrix.det hg
  rw [Matrix.det_mul, Matrix.det_mul, Formalism.UG.cT, Matrix.det_transpose, ← RingHom.mapMatrix_apply,
    ← RingHom.map_det] at h
  apply hJ.mul_left_cancel
  linear_combination h

theorem lrAct_one (g : Matrix (Fin n) (Fin n) A) {k : ℕ} (X : Fin k → Fin n → A) :
    lrAct g 1 X = fun a => g.mulVec (X a) := by
  funext a
  simp [lrAct, Matrix.one_apply]

end Alg

section Q

variable {F E : Type} [Field F] [Field E] [Algebra F E]
  (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

theorem sig_alg (r : R) : sigR R σ (algebraMap R (R ⊗[F] E) r) = algebraMap R (R ⊗[F] E) r := by
  simp [sigR, Algebra.TensorProduct.algebraMap_apply]

theorem sig_incl (e : E) : sigR R σ (inclR R e) = inclR R (σ e) := by
  simp [sigR, inclR]

theorem q_scale (r : R) (z : Fin M → R ⊗[F] E) :
    qR R σ J (algebraMap R (R ⊗[F] E) r • z) = r * r * qR R σ J z := by
  unfold qR hR
  rw [form_smul, sig_alg, ← map_mul, ← Algebra.smul_def (r * r), map_smul, smul_eq_mul]
  ring

theorem q_rat [CharZero F] (h2 : Module.finrank F E = 2) (x : Fin M → E) (β : F)
    (hx : hE σ J x x = algebraMap F E β) :
    qR R σ J (fun i => inclR R (x i)) = algebraMap F R β := by
  haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ h2
  have e : hR R σ J (fun i => inclR R (x i)) (fun i => inclR R (x i)) = inclR R (hE σ J x x) := by

    simp only [hR, hE, Formalism.UG.hform, JR, Matrix.map_apply, sig_incl, map_sum, map_mul]
    rfl
  have e2 : inclR R (algebraMap F E β) = algebraMap R (R ⊗[F] E) (algebraMap F R β) := by
    rw [← IsScalarTower.algebraMap_apply]
    exact (Algebra.TensorProduct.includeRight : E →ₐ[F] R ⊗[F] E).commutes β
  unfold qR
  rw [e, hx, e2, Algebra.trace_algebraMap_of_basis
    (Algebra.TensorProduct.basis R (Module.finBasisOfFinrankEq F E h2))]
  simp only [Fintype.card_fin, nsmul_eq_mul]
  rw [← mul_assoc, ← map_natCast (algebraMap F R), ← map_mul]
  norm_num

theorem q_cont [TopologicalSpace R] [FiniteDimensional F E] [IsTopologicalRing R] :
    Continuous (qR R σ J) := by
  have hs : Continuous (sigR R σ) :=
    IsModuleTopology.continuous_of_linearMap
      (Algebra.TensorProduct.map (AlgHom.id R R) σ).toLinearMap
  have ht : Continuous (Algebra.trace R (R ⊗[F] E)) := IsModuleTopology.continuous_of_linearMap _
  unfold qR hR Formalism.UG.hform
  fun_prop

end Q

theorem fibre_invariant_orbit_ne_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R], Nice R → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (x : Fin 1 → Fin M → E) (β : F) (lam : Measure (R ⊗[F] E)) (ν : Measure R) (m : Measure (Fin 1 → Fin M → R ⊗[F] E)), IsHermND σ J → β ≠ 0 → hE σ J (x 0) (x 0) = algebraMap F E β → lam.IsAddHaarMeasure → ν.IsAddHaarMeasure → FibAt R σ J (tupMeas lam 1 M) ν (algebraMap F R β) m → IsInvTup R σ J m ∧ OnOrbit R σ J x m ∧ m ≠ 0 := by
  intro F E _ _ _ _ _ σ hCM R _ _ _ _ _ _ _ _ _ hN M J x β lam ν m hJ hβ hx hlam hν hm
  have hu : IsUnit (algebraMap F R β) := (IsUnit.mk0 β hβ).map _
  have hq : qR R σ J (ratTup (F := F) R x 0) = algebraMap F R β := q_rat R σ J hCM.2.2.1 (x 0) β hx
  obtain ⟨hsupp, -, huniq⟩ := GlobalTheory.T.fibreFamily_hermitian_quadratic_form_at_unit_props F E σ R hN M J _ ν _ m hν hu hm
  have h1 : modu R 1 = 1 := (GlobalTheory.GaugeEx.modu_basic R).2.2.1
  refine ⟨fun g => ?_, ?_, ?_⟩
  · set G : Matrix (Fin M) (Fin M) (R ⊗[F] E) := (HA.mat R σ J g).val with hG
    have hg : Formalism.UG.cT (sigR R σ) G * JR R J * G = JR R J := g.2
    have hd : IsUnit G.det := (Matrix.isUnit_iff_isUnit_det _).1 (HA.mat R σ J g).isUnit
    have hJu : IsUnit (JR (F := F) R J).det := by
      unfold JR
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
      exact (IsUnit.mk0 _ hJ.2).map _
    have hm1 : modu (R ⊗[F] E) G.det = 1 := by
      rw [(GlobalTheory.T.haarModulus_tensor_eq_modulus_norm F E σ hCM R G.det 1 hd (by rw [map_one, det_norm _ _ hJu hg])).2, h1]
    have := GlobalTheory.T.fibreMeasures_transport_unitary_similitude F E σ R hN M J J lam ν _ 1 m G hlam hν hd isUnit_one
      (fun z => by rw [one_mul]; unfold qR hR; rw [form_mulVec _ _ hg]) hm
    rw [one_mul, hm1, h1, inv_one, mul_one, one_smul] at this
    have e : lrAct G 1 = fun X : Fin 1 → Fin M → R ⊗[F] E => g • X := by
      funext X; rw [lrAct_one]; rfl
    rw [e] at this
    exact huniq _ this
  · refine measure_mono_null (fun y hy => ?_) hsupp
    exact fun h => hy (GlobalTheory.T.cmExtension_localFieldProductRing_exists_smul_eq F E σ hCM R hN M J hJ _ _ y hu hq h)
  · rintro rfl
    obtain ⟨-, -, hO, U, hU, h1U, s, -, -, hs⟩ := id hN
    obtain ⟨fib, hfib, -⟩ := id hm
    obtain ⟨w, hw⟩ := hu
    let T : Set R := {b | IsUnit b} ∩ (fun b => b * (↑w⁻¹ : R)) ⁻¹' U
    have hT : IsOpen T := by
      refine IsOpen.inter ?_ (hU.preimage (by fun_prop))
      exact hO.isOpenEmbedding_unitsVal.isOpen_range
    have hz : ∀ b ∈ T, fib b = 0 := by
      rintro b ⟨hb, hbU⟩
      set r := s (b * (↑w⁻¹ : R))
      have hr : r * r = b * (↑w⁻¹ : R) := hs _ hbU
      have hrr : IsUnit (r * r) := hr ▸ IsUnit.mul hb (Units.isUnit _)
      have hru : IsUnit r := isUnit_of_mul_isUnit_left hrr
      have := GlobalTheory.T.fibreMeasures_transport_unitary_similitude F E σ R hN M J J lam ν _ (r * r) 0
        (algebraMap R (R ⊗[F] E) r • (1 : Matrix (Fin M) (Fin M) (R ⊗[F] E))) hlam hν
        (by rw [Matrix.det_smul, Matrix.det_one, mul_one]; exact (hru.map _).pow _) hrr
        (fun z => by rw [Matrix.smul_mulVec, Matrix.one_mulVec, q_scale]) hm
      rw [Measure.map_zero, smul_zero, hr, ← hw, Units.inv_mul_cancel_right] at this
      exact (GlobalTheory.T.fibreFamily_hermitian_quadratic_form_at_unit_props F E σ R hN M J _ ν _ 0 hν hb this).2.2 _ ⟨fib, hfib, rfl⟩
    let O : Set (Fin 1 → Fin M → R ⊗[F] E) := (fun X => qR R σ J (X 0)) ⁻¹' T
    have hOo : IsOpen O := hT.preimage ((q_cont R σ J).comp (continuous_apply 0))
    have hne : O.Nonempty := ⟨ratTup (F := F) R x, by
      show qR R σ J (ratTup (F := F) R x 0) ∈ T
      rw [hq, ← hw]
      exact ⟨w.isUnit, by simpa using h1U⟩⟩
    have key := hfib.2.1 (O.indicator 1) (measurable_one.indicator hOo.measurableSet)
    have hz' : ∀ b, fib b O = 0 := by
      intro b
      by_cases hb : b ∈ T
      · rw [hz b hb]; rfl
      · refine measure_mono_null (fun y hy => ?_) (hfib.1 b)
        intro h
        apply hb
        have : qR R σ J (y 0) = b := h.1
        rw [← this]; exact hy
    simp only [Measure.restrict_univ, lintegral_indicator_one hOo.measurableSet, hz',
      lintegral_zero] at key
    haveI : (tupMeas lam 1 M).IsOpenPosMeasure := by
      unfold tupMeas
      haveI : (Measure.pi fun _ : Fin M => lam).IsOpenPosMeasure :=
        Measure.pi.isOpenPosMeasure (fun _ : Fin M => lam)
      exact Measure.pi.isOpenPosMeasure (fun _ : Fin 1 => Measure.pi fun _ : Fin M => lam)
    exact (hOo.measure_pos _ hne).ne' key

end GlobalTheory.GaugeEx.FibProp
end

section

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.BetaEx
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

theorem exists_index_ideal_inf_sup (E : Type) [Field E] [NumberField E] (n : ℕ)
    (M M' : Submodule (𝓞 E) (Fin n → E)) (hb : Bdd (M' ⊔ M))
    (ht : ∀ m ∈ M, ∃ a : 𝓞 E, a ≠ 0 ∧ a • m ∈ M') :
    ∃ 𝔞 : Ideal (𝓞 E), 𝔞 ≠ ⊥ ∧ detSpan (M ⊓ M') = 𝔞 • detSpan M ∧
      detSpan M' = 𝔞 • detSpan (M' ⊔ M) ∧
      Ideal.absNorm 𝔞 = (M ⊓ M').toAddSubgroup.relIndex M.toAddSubgroup := by
  classical
  have hsub : ∀ N : Submodule (𝓞 E) (Fin n → E), N ≤ M' ⊔ M → Bdd N := by
    intro N hN
    obtain ⟨k, hk, h⟩ := hb
    exact ⟨k, hk, fun v hv => h v (hN hv)⟩
  have key : ∀ s : Finset (Fin n → E), (∀ x ∈ s, x ∈ M) →
      ∃ 𝔞 : Ideal (𝓞 E), 𝔞 ≠ ⊥ ∧
        detSpan (M ⊓ M') = 𝔞 • detSpan ((M ⊓ M') ⊔ Submodule.span (𝓞 E) (s : Set (Fin n → E))) ∧
        detSpan M' = 𝔞 • detSpan (M' ⊔ Submodule.span (𝓞 E) (s : Set (Fin n → E))) ∧
        Ideal.absNorm 𝔞 = (M ⊓ M').toAddSubgroup.relIndex
          ((M ⊓ M') ⊔ Submodule.span (𝓞 E) (s : Set (Fin n → E))).toAddSubgroup := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro _; exact ⟨⊤, by simp, by simp, by simp, by simp⟩
    | insert m s _ ih =>
      intro hs
      obtain ⟨𝔞, h0, h1, h1', h2⟩ := ih fun x hx => hs x (Finset.mem_insert_of_mem hx)
      have hsM : Submodule.span (𝓞 E) (s : Set (Fin n → E)) ≤ M :=
        Submodule.span_le.2 fun x hx => hs x (Finset.mem_insert_of_mem hx)
      set N := (M ⊓ M') ⊔ Submodule.span (𝓞 E) (s : Set (Fin n → E)) with hN
      set S := M' ⊔ Submodule.span (𝓞 E) (s : Set (Fin n → E)) with hS
      have hm : m ∈ M := hs m (Finset.mem_insert_self _ _)
      have hmM : Submodule.span (𝓞 E) {m} ≤ M := (Submodule.span_singleton_le_iff_mem _ _).2 hm
      have e : (M ⊓ M') ⊔ Submodule.span (𝓞 E) ((insert m s : Finset (Fin n → E)) : Set (Fin n → E)) =
          N ⊔ Submodule.span (𝓞 E) {m} := by
        rw [Finset.coe_insert, Submodule.span_insert, hN, sup_assoc, sup_comm (Submodule.span _ {m})]
      have e' : M' ⊔ Submodule.span (𝓞 E) ((insert m s : Finset (Fin n → E)) : Set (Fin n → E)) =
          S ⊔ Submodule.span (𝓞 E) {m} := by
        rw [Finset.coe_insert, Submodule.span_insert, hS, sup_assoc, sup_comm (Submodule.span _ {m})]
      have hNS : N = M ⊓ S := by
        rw [hN, hS, inf_sup_assoc_of_le _ hsM]
      have hb1 : Bdd (N ⊔ Submodule.span (𝓞 E) {m}) :=
        hsub _ (le_sup_of_le_right (sup_le (sup_le inf_le_left hsM) hmM))
      have hb2 : Bdd (S ⊔ Submodule.span (𝓞 E) {m}) :=
        hsub _ (sup_le (sup_le_sup_left hsM _) (le_sup_of_le_right hmM))
      have hc : (N.comap (LinearMap.toSpanSingleton (𝓞 E) _ m) : Ideal (𝓞 E)) =
          S.comap (LinearMap.toSpanSingleton (𝓞 E) _ m) := by
        ext a
        rw [hNS]
        exact ⟨fun h => h.2, fun h => ⟨M.smul_mem a hm, h⟩⟩
      rw [e, e']
      refine ⟨𝔞 * (N.comap (LinearMap.toSpanSingleton (𝓞 E) _ m) : Ideal (𝓞 E)), ?_, ?_, ?_, ?_⟩
      · refine mul_ne_zero h0 ?_
        obtain ⟨a, ha, ham⟩ := ht m hm
        exact (Submodule.ne_bot_iff _).2
          ⟨a, (le_sup_left : M ⊓ M' ≤ N) ⟨M.smul_mem a hm, ham⟩, ha⟩
      · rw [h1, Submodule.mul_smul, ← detSpan_cyclic N m hb1]
      · rw [h1', hc, Submodule.mul_smul, ← detSpan_cyclic S m hb2]
      · rw [map_mul, h2, index_cyclic]
        exact AddSubgroup.relIndex_mul_relIndex _ _ _ (Submodule.toAddSubgroup_mono le_sup_left)
          (Submodule.toAddSubgroup_mono le_sup_left)
  have hfg : M.FG := by
    obtain ⟨k, hk, h⟩ := hsub M le_sup_right
    have hs : (stdLat E n).FG := Submodule.fg_pi fun _ => by
      rw [Submodule.one_eq_span]; exact Submodule.fg_span_singleton _
    apply Submodule.fg_of_fg_map_injective (LinearMap.lsmul (𝓞 E) (Fin n → E) k)
      (fun x y hxy => smul_right_injective _ hk hxy)
    exact hs.of_le (by rintro _ ⟨v, hv, rfl⟩; exact h v hv)
  obtain ⟨s, rfl⟩ := hfg
  have := key s fun x hx => Submodule.subset_span hx
  rwa [sup_eq_right.2 inf_le_left] at this

end GlobalTheory.BetaEx
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting
  NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.HeckeFrob

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

def conjSplit (s : SplitPlace L) : SplitPlace L := ⟨s.v, s.i.comp (IsCMField.complexConj L).toAlgHom⟩

section
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

def IsLocMap {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W] (s : SplitPlace L)
    (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L)))
    (i : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L)
    (T : σ.V →ₗ[ℂ] (GAf L n → W)) : Prop :=
  ∀ x : GAf L n, TrivOutside {s.v} x → ∀ a,
    T (σ.ρ (Matrix.GeneralLinearGroup.map i.toRingHom (s.loc n x)) a) = NG.rt L n x (T a)

end

def twEig (w : HeightOneSpectrum (𝓞 L)) {n : ℕ} (α : Fin n → ℂˣ) : Multiset ℂ :=
  (Finset.univ.val.map fun i => ((α i : ℂ))⁻¹).map (· * ((normV w : ℕ) : ℂ) ^ (((1 - (n : ℝ)) / 2 : ℝ) : ℂ))

end GlobalTheory.HeckeFrob

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial Formalism.UG GlobalTheory.SatInd

namespace GlobalTheory.SatInd.CosetFin

theorem finite_cosets {G H : Type} [Group G] [Group H] (φ : G →* H) (H' : Subgroup H) (K : Subgroup H')
    (U : Subgroup G) (p : G → Prop) (F : Set (H' ⧸ K)) (hF : F.Finite)
    (hp : ∀ x, p x → ∃ hx : φ x ∈ H', ((⟨φ x, hx⟩ : H') : H' ⧸ K) ∈ F)
    (hU : ∀ x y, p x → p y → ∀ hz : φ (x⁻¹ * y) ∈ H', (⟨φ (x⁻¹ * y), hz⟩ : H') ∈ K → x⁻¹ * y ∈ U) :
    Set.Finite {c : G ⧸ U | ∃ x : G, (x : G ⧸ U) = c ∧ p x} := by
  have hsub : {c : G ⧸ U | ∃ x : G, (x : G ⧸ U) = c ∧ p x} ⊆
      ⋃ d ∈ F, {c : G ⧸ U | ∃ x : G, (x : G ⧸ U) = c ∧ p x ∧
        ∃ hx : φ x ∈ H', ((⟨φ x, hx⟩ : H') : H' ⧸ K) = d} := by
    rintro c ⟨x, hc, hx⟩
    obtain ⟨h1, h2⟩ := hp x hx
    exact Set.mem_biUnion h2 ⟨x, hc, hx, h1, rfl⟩
  refine (hF.biUnion fun d _ => Set.Subsingleton.finite ?_).subset hsub
  rintro c ⟨x, rfl, hx, hx1, hx2⟩ c' ⟨y, rfl, hy, hy1, hy2⟩
  have hk := QuotientGroup.eq.1 (hx2.trans hy2.symm)
  have hz : φ (x⁻¹ * y) ∈ H' := by
    rw [map_mul, map_inv]; exact H'.mul_mem (H'.inv_mem hx1) hy1
  refine QuotientGroup.eq.2 (hU x y hx hy hz ?_)
  convert hk using 1
  apply Subtype.ext
  simp

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem trivOutside_mul {T : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))} {x y : GA L n}
    (hx : TrivOutside T x) (hy : TrivOutside T y) : TrivOutside T (x * y) := by
  intro w hw
  have : ((x * y).1 : Matrix (Fin n) (Fin n) (AL L)) =
      (x.1 : Matrix (Fin n) (Fin n) (AL L)) * (y.1 : Matrix (Fin n) (Fin n) (AL L)) := rfl
  rw [this, Matrix.map_mul, hx w hw, hy w hw, mul_one]

theorem trivOutside_inv {T : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))} {x : GA L n}
    (hx : TrivOutside T x) : TrivOutside T x⁻¹ := by
  intro w hw
  have h1 : (((x⁻¹ : GA L n).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) *
      (x.1 : Matrix (Fin n) (Fin n) (AL L)) = 1 := by
    rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]
    rfl
  have h2 := congrArg (fun M => M.map (compAt L w)) h1
  simp only [Matrix.map_mul, hx w hw, mul_one] at h2
  rw [h2, Matrix.map_one _ (map_zero _) (map_one _)]

variable {v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))} {w : HeightOneSpectrum (𝓞 L)}

def locHom (D : InertDatum L n v w) : GAf L n →* GL (Fin n) (w.adicCompletion L) :=
  MonoidHom.mk' D.loc fun x y => by
    simp only [InertDatum.loc, Subgroup.coe_mul, map_mul, mul_assoc, mul_inv_cancel_left]

theorem entries_int {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))] {σ : K →+* K}
    {g : GU σ n} (hg : g ∈ KU σ n) (i j : Fin n) :
    ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j ∈ intL K := by
  obtain ⟨-, k, hk⟩ := hg
  have hk' : bc (n := Fin n) (intL K).subtype k = (g : GL (Fin n) K) := hk
  rw [← hk']
  exact ((k : Matrix (Fin n) (Fin n) (intL K)) i j).2

theorem finite_inert_support : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w), (∀ s : GU Dv.σw n, Set.Finite {c : GU Dv.σw n ⧸ KU Dv.σw n | ∃ a ∈ KU Dv.σw n, ((a * s : GU Dv.σw n) : GU Dv.σw n ⧸ KU Dv.σw n) = c}) → (∀ z : GAf L n, TrivOutside {v} z → (∀ i j, ((Dv.loc z : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) (w.adicCompletion L)) i j ∈ intL (w.adicCompletion L)) → z ∈ Umax L n) → ∀ (U : Subgroup (GAf L n)), (∀ κ, TrivOutside {v} κ → (κ ∈ U ↔ κ ∈ Umax L n)) → ∀ h ∈ Hecke ℂ (KU Dv.σw n), Set.Finite {c : GAf L n ⧸ U | ∃ x : GAf L n, (x : GAf L n ⧸ U) = c ∧ TrivOutside {v} x ∧ Dv.hval h (Dv.loc x) ≠ 0} := by
  intro L _ _ _ n v w Dv hfin hint U hU h hh
  obtain ⟨-, S, hS⟩ := hh
  refine finite_cosets (locHom Dv) (GU Dv.σw n) (KU Dv.σw n) U
    (fun x => TrivOutside {v} x ∧ Dv.hval h (Dv.loc x) ≠ 0) _
    (S.finite_toSet.biUnion fun s _ => hfin s) ?_ ?_
  · rintro x ⟨-, hx⟩
    have hm : Dv.loc x ∈ GU Dv.σw n := by
      by_contra hm
      exact hx (dif_neg hm)
    have hne : h ⟨Dv.loc x, hm⟩ ≠ 0 := by
      intro h0
      exact hx ((dif_pos hm).trans h0)
    obtain ⟨s, hs, a, b, e⟩ := hS _ hne
    refine ⟨hm, Set.mem_biUnion hs ⟨a, a.2, ?_⟩⟩
    have e' : (⟨locHom Dv x, hm⟩ : GU Dv.σw n) = (a : GU Dv.σw n) * s * b := e
    rw [e']
    exact (QuotientGroup.mk_mul_of_mem _ b.2).symm
  · rintro x y ⟨hx, -⟩ ⟨hy, -⟩ hz hk
    have ht : TrivOutside {v} (x⁻¹ * y) := trivOutside_mul (trivOutside_inv hx) hy
    exact (hU _ ht).2 (hint _ ht fun i j => entries_int hk i j)

end GlobalTheory.SatInd.CosetFin
end
end

section

open NumberField IsDedekindDomain
open scoped TensorProduct

theorem _root_.GlobalTheory.T.splitting_fst_mem_integers' : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (spl : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F),
    (∀ a : v.adicCompletion F, spl ((1 : E) ⊗ₜ[F] a) = (a, a)) →
    ∀ z ∈ Formalism.BasicNotions.intV E v, (spl z).1 ∈ v.adicCompletionIntegers F := by
  first | exact @GlobalTheory.splitting_fst_mem_integers | exact GlobalTheory.splitting_fst_mem_integers | (intros; apply GlobalTheory.splitting_fst_mem_integers <;> assumption)
end

section

open NumberField IsDedekindDomain

namespace GlobalTheory

theorem blockIndexOf_blockIndexTwo_eq_coarseBlocks_pointwise {n r t : ℕ} (hn : n = r + t) (a : Fin n) :
    Formalism.L2.DIV.blkOf r t a = Formalism.L2.Col.coarse r [t] a.val ∧
      Formalism.L2.DIV.blk2 r a = Formalism.L2.Col.coarse r [t] a.val := by
  have ha := a.isLt
  by_cases h : a.val < r
  · rw [Formalism.L2.Col.coarse_of_lt h]
    simp [Formalism.L2.DIV.blkOf, Formalism.L2.DIV.blk2, h]
  · have h' : r ≤ a.val := Nat.not_lt.mp h
    rw [Formalism.L2.Col.coarse_of_le h']
    have hlt : a.val - r < t := by omega
    have hd : (a.val - r) / t = 0 := Nat.div_eq_of_lt hlt
    simp [Formalism.L2.DIV.blkOf, Formalism.L2.DIV.blk2, h, hd, Formalism.L2.Col.blkIdx, hlt]

theorem blockTriangular_blockIndexOf_iff_colBlockUT_twoBlocks :
    ∀ {κ : Type} [CommRing κ] {n r t : ℕ}, n = r + t → ∀ g : GL (Fin n) κ,
      (g ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf r t) ↔ g ∈ Formalism.L2.Col.blockUT n κ r [t]) ∧
        (g ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 r) ↔ g ∈ Formalism.L2.Col.blockUT n κ r [t]) := by
  intro κ _ n r t hn g
  rw [Formalism.L2.DIV.mem_blockTri, Formalism.L2.DIV.mem_blockTri, Formalism.L2.Col.mem_btG]
  refine ⟨?_, ?_⟩
  · simp only [(blockIndexOf_blockIndexTwo_eq_coarseBlocks_pointwise hn _).1]
  · simp only [(blockIndexOf_blockIndexTwo_eq_coarseBlocks_pointwise hn _).2]

end GlobalTheory
end

section

open Formalism.L2.DIV

theorem _root_.GlobalTheory.T.absIrrChar_realise_of_primitiveRoot_card : ∀ {G : Type} [inst : Group G] [inst_1 : Fintype G] {K : Type} [inst_2 : Field K] (σ : K →+* ℂ) (z : K), IsPrimitiveRoot z (Fintype.card G) → ∀ (ψ : G → ℂ), ψ ∈ Formalism.L2.Col.gxIrrSet (G := G) ℂ → ∃ χ : G → K, IsAbsIrrChar χ ∧ ∀ g, σ (χ g) = ψ g := by
  first | exact @GlobalTheory.BrauerRealise.absIrr_realise_of_isPrimitiveRoot | exact GlobalTheory.BrauerRealise.absIrr_realise_of_isPrimitiveRoot | (intros; apply GlobalTheory.BrauerRealise.absIrr_realise_of_isPrimitiveRoot <;> assumption)
end
