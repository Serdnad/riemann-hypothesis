module

public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle065
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle063
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle064
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ThetaAtEqSumHeisOfFourierSum
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1195
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1347
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1191
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1230
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1588
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle537
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle223
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.TypeAtOfDiscreteSeries
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle503
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle538
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle162
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacewiseToAdelicDecompositionForall
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle305
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle136
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalStabilizerDoubledVacuumEigenvalueEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1449
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle468
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle010
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1610

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HalfWaves

open GlobalTheory.PlaceModel GlobalTheory.PlaceDatum

variable {D : D7} {S T : HSp D}

theorem isSBHalf_trans {a : AE D} {Λ : AddSubgroup (WO S T)} {x : WO S T} (hx : IsHalf a x) {k : ℕ} (hk : 0 < k)
    (hkx : k • x ∈ Λ) : IsSBHalf a Λ fun t => halfInd a Λ (t + x) := by
  have hx' := (isHalf_iff S T).1 hx
  refine ⟨fun t ht => ?_, k, hk, fun u hu hh t => ?_, fun t ht => ?_⟩
  · have h : t + x ∈ Λ ∧ IsHalf a (t + x) := by
      by_contra h
      exact ht (if_neg h)
    refine (isHalf_iff S T).2 ?_
    exact (add_mem_cancel_right hx').1 ((isHalf_iff S T).1 h.2)
  · have hm : k • u ∈ Λ ⊓ half S T a :=
      nsmul_mem (AddSubgroup.mem_inf.2 ⟨hu, (isHalf_iff S T).1 hh⟩) k
    rw [halfInd_eq_ind]
    change ind _ (t + k • u + x) = ind _ (t + x)
    rw [add_right_comm]
    exact ind_add _ _ hm
  · have h : t + x ∈ Λ ∧ IsHalf a (t + x) := by
      by_contra h
      exact ht (if_neg h)
    have e : k • t = k • (t + x) - k • x := by rw [nsmul_add, add_sub_cancel_right]
    rw [e]
    exact sub_mem (nsmul_mem h.1 k) hkx

theorem isSBHalf_modul (ψ : AddChar (AF D.host.F) ℂ) {a : AE D} {Λ : AddSubgroup (WO S T)}
    (hLL' : ∀ u ∈ Λ ⊓ half S T a, ∀ y ∈ Λ ⊓ half S T (cA D a), ψ (symplO S T u y) = 1)
    {y : WO S T} (hy : IsHalf (cA D a) y) {k : ℕ} (hk : 0 < k) (hky : k • y ∈ Λ) {Φ : WO S T → ℂ}
    (hΦ : IsSBHalf a Λ Φ) : IsSBHalf a Λ fun t => ψ (symplO S T t y) * Φ t := by
  have hb : IsBichar (fun x y : WO S T => ψ (symplO S T x y)) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro a b y; rw [symplO_add_left, AddChar.map_add_eq_mul]
    · intro a b y; rw [symplO_add_right, AddChar.map_add_eq_mul]
    · intro y; rw [symplO_zero_left, AddChar.map_zero_eq_one]
    · intro y; rw [symplO_zero_right, AddChar.map_zero_eq_one]
  obtain ⟨a1, k', hk1, a2, a3⟩ := hΦ
  refine ⟨fun t ht => a1 t (right_ne_zero_of_mul ht), k * k', Nat.mul_pos hk hk1, fun u hu hh t => ?_,
    fun t ht => ?_⟩
  · have e1 : Φ (t + (k * k') • u) = Φ t := by
      rw [mul_nsmul]
      exact a2 _ (nsmul_mem hu k) ((isHalf_iff S T).2 (nsmul_mem ((isHalf_iff S T).1 hh) k)) t
    have e2 : ψ (symplO S T ((k * k') • u) y) = 1 := by
      rw [mul_nsmul']
      exact (hb.nsmul k _ y).trans (hLL' _ (nsmul_mem (AddSubgroup.mem_inf.2 ⟨hu, (isHalf_iff S T).1 hh⟩) k') _
        ⟨hky, nsmul_mem ((isHalf_iff S T).1 hy) k⟩)
    simp only [e1, symplO_add_left, AddChar.map_add_eq_mul, e2, mul_one]
  · rw [mul_nsmul']
    exact nsmul_mem (a3 t (right_ne_zero_of_mul ht)) k

end GlobalTheory.HalfWaves

namespace GlobalTheory.PlaceTensor

open GlobalTheory.PlaceModel GlobalTheory.PlaceDatum GlobalTheory.HalfWaves

theorem halfWaves_span : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsStdChar D ψ (-1) → IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ a : AE D, a * a = a → a * cA D a = 0 → infPart D a = 0 → (∀ x y : WO S T, IsHalf a x → IsHalf (cA D a) y → IsSBHalf a (latO S T ΛS ΛT fun _ => True) (fun t => ψ (symplO S T t y) * halfInd a (latO S T ΛS ΛT fun _ => True) (t + x)) ∧ ∀ (f₀ : WO S T → ℂ) (Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)), IsPlaceModel ψ (symplO S T) (heisO ψ S T) a (latO S T ΛS ΛT fun _ => True) 1 f₀ Tm → Tm (fun t => ψ (symplO S T t y) * halfInd a (latO S T ΛS ΛT fun _ => True) (t + x)) = heisO ψ S T y (heisO ψ S T x f₀)) ∧ ∀ Φ, IsSBHalf a (latO S T ΛS ΛT fun _ => True) Φ → Φ ∈ Submodule.span ℂ {Ψ : WO S T → ℂ | ∃ x y : WO S T, IsHalf a x ∧ IsHalf (cA D a) y ∧ Ψ = fun t => ψ (symplO S T t y) * halfInd a (latO S T ΛS ΛT fun _ => True) (t + x)} := by
  intro D ψ S T ΛS ΛT hψ hS hT e he _ hinf
  have hSfull := GlobalTheory.PlaceVec.selfDual_isFullLattice S ΛS hS
  have hTfull := GlobalTheory.PlaceVec.selfDual_isFullLattice T ΛT hT
  have hdual := (GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T _ _ hψ hS hT).1
  have hfin0 := GlobalTheory.LatFinMod.latO_finite_mod D S T _ _ hS.1.fg hT.1.fg fun _ => True
  have he' : cA D e * cA D e = cA D e := by rw [← RingHom.map_mul, he]
  have hsm : ∀ a : AE D, a * a = a → ∀ u ∈ latO S T ΛS ΛT fun _ => True,
      a • u ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T a := fun a ha u hu =>
    AddSubgroup.mem_inf.2 ⟨GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ a
      (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, ha])) u hu, by rw [mem_half, smul_smul, ha]⟩
  have hLL' : ∀ u ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T e,
      ∀ y ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T (cA D e), ψ (symplO S T u y) = 1 := fun u hu y hy =>
    (hdual u (infPart_of_half hinf ((isHalf_iff S T).2 hu.2))).1 hu.1 y hy.1
  have hX : ∀ x ∈ half S T e, (∀ y ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T (cA D e), ψ (symplO S T x y) = 1) →
      x ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T e := fun x hx h => by
    refine ⟨(hdual x (infPart_of_half hinf ((isHalf_iff S T).2 hx))).2 fun u hu => ?_, hx⟩
    have := h _ (hsm _ he' u hu)
    rwa [← symplO_smul, (mem_half S T).1 hx] at this
  have hfin : ∀ k : ℕ, 0 < k → ∃ R : Set (WO S T), R.Finite ∧
      ∀ t ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T e, ∃ r ∈ R,
        ∃ u ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T e, t = r + k • u := fun k hk => by
    obtain ⟨R, hR, h⟩ := hfin0 k hk
    refine ⟨(fun r => e • r) '' R, hR.image _, fun t ht => ?_⟩
    obtain ⟨r, hr, u, hu, htr⟩ := h t ht.1
    refine ⟨_, ⟨r, hr, rfl⟩, e • u, hsm e he u hu, ?_⟩
    have := (mem_half S T).1 ht.2
    rw [← this, htr, smul_add, smul_comm e k u]
  have tf : ∀ k : ℕ, 0 < k → Function.Injective fun t : WO S T => k • t := fun k hk a b hab => by
    rw [← inv_smul_nsmul S T hk a, ← inv_smul_nsmul S T hk b]
    exact congrArg _ hab
  have hb : IsBichar (fun x y : WO S T => ψ (symplO S T x y)) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro a b y; rw [symplO_add_left, AddChar.map_add_eq_mul]
    · intro a b y; rw [symplO_add_right, AddChar.map_add_eq_mul]
    · intro y; rw [symplO_zero_left, AddChar.map_zero_eq_one]
    · intro y; rw [symplO_zero_right, AddChar.map_zero_eq_one]
  have hsb : ∀ x, IsHalf e x → IsSBHalf e (latO S T ΛS ΛT fun _ => True)
      fun t => halfInd e (latO S T ΛS ΛT fun _ => True) (t + x) := fun x hx => by
    obtain ⟨k, hk, hk'⟩ := exists_nsmul_mem_latO' hSfull hTfull x (infPart_of_half hinf hx)
    exact isSBHalf_trans hx hk hk'
  have hmod : ∀ x y, IsHalf e x → IsHalf (cA D e) y → IsSBHalf e (latO S T ΛS ΛT fun _ => True)
      fun t => ψ (symplO S T t y) * halfInd e (latO S T ΛS ΛT fun _ => True) (t + x) := fun x y hx hy => by
    obtain ⟨k, hk, hk'⟩ := exists_nsmul_mem_latO' hSfull hTfull y (infPart_of_half (infPart_cA hinf) hy)
    exact isSBHalf_modul ψ hLL' hy hk hk' (hsb x hx)
  refine ⟨fun x y hx hy => ⟨hmod x y hx hy, fun f₀ Tm hTm => ?_⟩, fun Φ hΦ => ?_⟩
  · have v := hTm.vac
    rw [one_smul] at v
    rw [hTm.modul _ (hsb x hx) y hy, hTm.trans _ (GlobalTheory.isSBHalf_halfInd e _) x hx, v]
  · have hm : Φ ∈ waveSpan (fun x y : WO S T => ψ (symplO S T x y)) (half S T e) (half S T (cA D e))
        ((latO S T ΛS ΛT fun _ => True) ⊓ half S T e) := by
      obtain ⟨h1, k, hk, h2, h3⟩ := hΦ
      exact mem_waveSpan hb inf_le_right inf_le_right hLL' hX (half_div S T e) (half_div S T _) tf hfin Φ
        (fun t ht => (isHalf_iff S T).1 (h1 t ht)) k hk (fun u hu => h2 u hu.1 ((isHalf_iff S T).2 hu.2))
        fun t ht => ⟨h3 t ht, (half S T e).nsmul_mem ((isHalf_iff S T).1 (h1 t ht)) _⟩
    refine (Submodule.span_le.2 ?_) hm
    rintro _ ⟨x, hx, y, hy, rfl⟩
    have e1 : wave (fun x y : WO S T => ψ (symplO S T x y)) ((latO S T ΛS ΛT fun _ => True) ⊓ half S T e) x y =
        ψ (symplO S T x y) • fun t => ψ (symplO S T t y) * halfInd e (latO S T ΛS ΛT fun _ => True) (t + x) := by
      funext t
      simp only [wave, Pi.smul_apply, smul_eq_mul, halfInd_eq_ind, symplO_add_left, AddChar.map_add_eq_mul]
      ring
    rw [e1]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, y, (isHalf_iff S T).2 hx, (isHalf_iff S T).2 hy, rfl⟩)

end GlobalTheory.PlaceTensor

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels


theorem _root_.GlobalTheory.T.latticeStabilizers_fix_vacua_fixes_pureTensor_left : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) {n d : ℕ} (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d)
    (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W) (r s r' s' : ℕ),
    GlobalTheory.ThK.IsPair B M χX χW om r s r' s' → ∀ S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)),
    (∀ v ∉ S, ∀ k ∈ GlobalTheory.InertSph.KAt σ X v, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) (om (k, 1)) (M.vac v) (M.vac v)) →
    ∀ k : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J,
    (∀ u : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) u → u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k - 1) = 0) →
    (∀ w ∈ S, ∀ u : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F w) u → u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k - 1) = 0) →
    (∀ w ∉ S, ∀ z ∈ GlobalTheory.InertSph.latAt X w,
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k *ᵥ z ∈ GlobalTheory.InertSph.latAt X w ∧ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k⁻¹ *ᵥ z ∈ GlobalTheory.InertSph.latAt X w) →
    ∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) (φ : ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin d → Fv F w) → ℂ),
      (∀ w, φ w ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F w)) → (∀ w ∉ S, φ w = M.vac w) →
      om (k, 1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ := by
  first | exact @GlobalTheory.SphGlobX.fixes_pure_left | exact GlobalTheory.SphGlobX.fixes_pure_left | (intros; apply GlobalTheory.SphGlobX.fixes_pure_left <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

theorem _root_.GlobalTheory.T.latticeStabilizers_fix_vacua_fixes_pureTensor : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ)
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d) (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (ψ : AddChar (AF F) ℂ)
    (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W) (S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))),
    0 < n → X.L.IsFullLattice E → W.L.IsLattice E → M.IsGood ψ → M.IsWeil ψ χX χW om →
    (∀ v, v ∉ S → ∀ k ∈ GlobalTheory.InertSph.KAt σ W v,
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) (om (1, k)) (M.vac v) (M.vac v)) →
    ∀ k : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ W.J,
    (∀ u : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) u → u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k - 1) = 0) →
    (∀ w ∈ S, ∀ u : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F w) u → u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k - 1) = 0) →
    (∀ w, w ∉ S → ∀ γ, γ * (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k)ᵀ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X W w ↔ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X W w) →
    ∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) (φ : ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin d → Fv F w) → ℂ),
      (∀ w, φ w ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F w)) → (∀ w, w ∉ S → φ w = M.vac w) →
      om (1, k) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ := by
  intro F E _ _ _ _ _ σ n d X W M ψ χX χW om S hn hXL
  letI := hXL
  exact GlobalTheory.SphGlob.fixes_pure F E σ n d X W M ψ χX χW om S hn inferInstance
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.SplitVacV
open GlobalTheory.DblVacSiegel

theorem siegel_eigen_eq_one_any : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)), v ∉ X.T →
    ∀ (d' : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J)) (Fin a × Fin (a + a'))),
    ∀ (dd : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J))) ((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a'))))
      (omd : GlobalTheory.DblVac.UD σ G.V →* Module.End ℂ (((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')) → AF F) → ℂ)),
    IsDblCoord (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) d' dd →
    IsUWeilSplit (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (adeleClass F) B.ψ (-1 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J)) dd (X.β / X.α) (diagCols (Fin a)) omd →
    ∀ r : (Fin a × Fin (a + a') → AF F) → ℂ, Rest (evFin F v) (G.M.vac v) r → tens (evFin F v) (G.M.vac v) r ≠ 0 →
    ∀ p ∈ GlobalTheory.DblVac.KD σ G.V v, p ∈ GlobalTheory.DblVac.PDiag σ G.V → ∀ μ : ℂ,
      omd p (boxFun (tens (evFin F v) (G.M.vac v) r) (fun x => star (tens (evFin F v) (G.M.vac v) r x))) =
        μ • boxFun (tens (evFin F v) (G.M.vac v) r) (fun x => star (tens (evFin F v) (G.M.vac v) r x)) → μ = 1 := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v hv d' dd omd hdd hW r hr h0 p hp hpd μ hμ
  obtain ⟨t, ht₀⟩ := hpd
  have ht : GlobalTheory.DblVac.matD p * (diagCols (Fin a) : Matrix (Fin a ⊕ Fin a) (Fin a) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) =
      (diagCols (Fin a) : Matrix (Fin a ⊕ Fin a) (Fin a) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) * (t : Matrix (Fin a) (Fin a) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) := ht₀
  have hF := hT.base.cm.1
  set Ψ := tens (evFin F v) (G.M.vac v) r with hΨ
  have hS := GlobalTheory.SchwartzBox.boxFun_mem_schA F _ _ Ψ hr.2 _ (GlobalTheory.SchAConj.star_mem_schA F _ Ψ hr.2)
  have hl := lDiag_box_ne_zero hF hr.2 h0
  have hS0 : (boxFun Ψ fun x => star (Ψ x)) ≠ 0 := fun h => hl (by rw [h, map_zero])
  have hn := norm_eq_one_of_eigen hF hW.2.1.unit hS hS0 hμ
  have hrule := hW.2.2 _ DiagForm.lDiag_adm (fun z φ hφ => by
    have e : z * (diagCols (Fin a) : Matrix _ _ (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))ᵀ = Matrix.fromCols z z := by
      rw [diagCols, Matrix.transpose_fromRows, Matrix.mul_fromCols, Matrix.transpose_one, Matrix.mul_one]
    rw [e, Darboux.rho, hdd]
    exact DiagForm.lDiag_schr B.ψ _ _ hφ) p t ht _ hS
  have hvec : ∀ (g : GlobalTheory.DblVac.UD σ G.V) (s : Matrix (Fin a) (Fin a) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))),
      GlobalTheory.DblVac.matD g * (diagCols (Fin a) : Matrix (Fin a ⊕ Fin a) (Fin a) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) = (diagCols (Fin a) : Matrix (Fin a ⊕ Fin a) (Fin a) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) * s → ∀ z,
      (GlobalTheory.DblVac.matD g *ᵥ Sum.elim z z) ∘ Sum.inl = s *ᵥ z := fun g s hs z => by
    have e : ∀ z : Fin a → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), (diagCols (Fin a) : Matrix (Fin a ⊕ Fin a) (Fin a) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) *ᵥ z = Sum.elim z z := fun z => by
      rw [diagCols, Matrix.fromRows_mulVec, Matrix.one_mulVec]
    rw [← e, Matrix.mulVec_mulVec, hs, ← Matrix.mulVec_mulVec, e]
    rfl
  have ht' : GlobalTheory.DblVac.matD p⁻¹ * (diagCols (Fin a) : Matrix (Fin a ⊕ Fin a) (Fin a) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) =
      (diagCols (Fin a) : Matrix (Fin a ⊕ Fin a) (Fin a) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) * ((t⁻¹ : GL (Fin a) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin a) (Fin a) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) := by
    have e1 : GlobalTheory.DblVac.matD p⁻¹ * GlobalTheory.DblVac.matD p = 1 := p.1.inv_mul
    calc _ = GlobalTheory.DblVac.matD p⁻¹ * ((diagCols (Fin a) : Matrix (Fin a ⊕ Fin a) (Fin a) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) * (t : Matrix (Fin a) (Fin a) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))) *
          ((t⁻¹ : GL (Fin a) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin a) (Fin a) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, t.mul_inv, Matrix.mul_one]
      _ = _ := by rw [← ht, ← Matrix.mul_assoc, e1, Matrix.one_mul]
  have hunr : ∀ P : HeightOneSpectrum (𝓞 E), P.under (𝓞 F) = v → UnrAt (X.β / X.α) P := fun P hP => by
    have hPT : P ∉ above E (X.T : Set (Pl (F := F))) := fun h => hv (hP ▸ (h : P.under (𝓞 F) ∈ (X.T : Set (Pl (F := F)))))
    rw [div_eq_mul_inv]
    exact (hT.chars.unrβ P hPT).mul (hT.chars.unrα P hPT).inv
  have hβ : (X.β / X.α) (Matrix.GeneralLinearGroup.det t) = 1 := by
    refine GlobalTheory.DblVacSiegelAny.chr_det_eq_one_any (v := v) G.V hT.geo.hV.lat hunr t (fun u hu => ?_) fun z hz => ?_
    · have e1 : (GlobalTheory.DblVac.matD p - 1) * (diagCols (Fin a) : Matrix (Fin a ⊕ Fin a) (Fin a) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) =
          (diagCols (Fin a) : Matrix (Fin a ⊕ Fin a) (Fin a) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) * ((t : Matrix (Fin a) (Fin a) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) - 1) := by
        rw [Matrix.sub_mul, Matrix.mul_sub, ht, Matrix.one_mul, Matrix.mul_one]
      have e2 : (diagCols (Fin a) : Matrix (Fin a ⊕ Fin a) (Fin a) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) * (u • ((t : Matrix (Fin a) (Fin a) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) - 1)) = 0 := by
        rw [Matrix.mul_smul, ← e1, ← Matrix.smul_mul, hp.1 u hu, Matrix.zero_mul]
      rw [diagCols, Matrix.fromRows_mul, Matrix.one_mul] at e2
      ext i j
      exact congrFun (congrFun e2 (Sum.inl i)) j
    · have hz' := hp.2 (Sum.elim z z) ⟨hz, hz⟩
      exact ⟨hvec p _ ht z ▸ hz'.1.1, hvec p⁻¹ _ ht' z ▸ hz'.2.1⟩
  have he := congrArg (DiagForm.lDiag F (Fin a × Fin (a + a'))) hμ
  rw [map_smul, smul_eq_mul] at he
  rw [hβ, Circle.coe_one, one_mul] at hrule
  have hμ' := mul_right_cancel₀ hl (he.symm.trans hrule)
  rw [hμ', Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (NNReal.coe_nonneg _) _)] at hn
  rw [hμ', hn, Complex.ofReal_one]

end GlobalTheory.SplitVacV

end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.DblVac

theorem gen_diag_anti_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)), (∀ w : HeightOneSpectrum (𝓞 E), ¬ Formalism.UG.IsInertAt F E v w) → PsiUnr B.ψ v →
    (2 : 𝓞 F) ∉ v.asIdeal → 3 < Ideal.absNorm v.asIdeal → ∀ H : Subgroup (GlobalTheory.DblVac.UD σ G.W),
      (∀ p ∈ GlobalTheory.DblVac.KD σ G.W v, p ∈ GlobalTheory.DblVac.PDiag σ G.W → p ∈ H) →
      (∀ p ∈ GlobalTheory.DblVac.KD σ G.W v, p ∈ GlobalTheory.DblVac.PAnti σ G.W → p ∈ H) → ∀ g ∈ GlobalTheory.DblVac.KD σ G.W v, g ∈ H := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v hv hψ h2 _ H hD hA g hg
  obtain ⟨Y, hYat, hYlat, hYadm, M, hM, hMlat⟩ := GlobalTheory.T.exists_admissible_unipotent_splitPlace σ B G.W _ _ hT.base hT.geo.hW v hv hψ h2 g hg
  obtain ⟨p, hpK, hpD, hp⟩ := GlobalTheory.T.exists_unipotent_doubledStabilizer_adds_diagonalBlock σ G.W v h2 Y hYat hYlat hYadm
  obtain ⟨hpgK, hpg⟩ := hp g hg
  have hbig : GlobalTheory.DblVac.BigCell G.W v (p * g) := ⟨M, by rw [hpg]; exact hM, hMlat⟩
  obtain ⟨q, hqK, hqA, p', hp'K, hp'D, he⟩ := GlobalTheory.T.doubledVacuumStabilizer_gaussDecomposition_bigCell σ G.W v h2 (p * g) hpgK hbig
  have hg' : g = p⁻¹ * (q * p') := by rw [← he]; group
  rw [hg']
  exact H.mul_mem (H.inv_mem (hD p hpK hpD)) (H.mul_mem (hA q hqK hqA) (hD p' hp'K hp'D))

end GlobalTheory.DblVac
end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.doubledVacuum_eigenvalue_eq_one_splitPlace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)), (∀ w : HeightOneSpectrum (𝓞 E), ¬ Formalism.UG.IsInertAt F E v w) → v ∉ X.T → PsiUnr B.ψ v →
    ∀ (dd : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J))) ((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a'))))
      (omd : GlobalTheory.DblVac.UD σ G.W →* Module.End ℂ (((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')) → AF F) → ℂ)),
    IsDblCoord (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) G.M.co dd →
    IsUWeilSplit (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (adeleClass F) B.ψ (-1 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J)) dd X.β (diagCols (Fin (a + a'))) omd →
    ∀ r : (Fin a × Fin (a + a') → AF F) → ℂ, Rest (evFin F v) (G.M.vac v) r → tens (evFin F v) (G.M.vac v) r ≠ 0 →
    ∀ p ∈ GlobalTheory.DblVac.KD σ G.W v, p ∈ GlobalTheory.DblVac.PDiag σ G.W → ∀ μ : ℂ,
      omd p (boxFun (tens (evFin F v) (G.M.vac v) r) (fun x => star (tens (evFin F v) (G.M.vac v) r x))) =
        μ • boxFun (tens (evFin F v) (G.M.vac v) r) (fun x => star (tens (evFin F v) (G.M.vac v) r x)) → μ = 1 := by
  first | exact @GlobalTheory.DblVacSiegelAny.eigen_eq_one_of_diag_split | exact GlobalTheory.DblVacSiegelAny.eigen_eq_one_of_diag_split | (intros; apply GlobalTheory.DblVacSiegelAny.eigen_eq_one_of_diag_split <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size


theorem _root_.GlobalTheory.T.averaged_automorphic_function_K_finite : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (N : GlobalTheory.Grid.Node D) (ψ : GA D N.V → ℂ), IsAutFunSm θ N.V ψ → ∀ (τ : D.what₂.Tau) (e : Formalism.REAL.KG (N.M.ε τ) → ℂ), GlobalTheory.TypeSum.KFinFun (N.M.ε τ) e → GlobalTheory.CuspKFin.KFinAt θ N τ (GlobalTheory.SeriesToClosure.avg θ N.V τ (N.M.ε τ) (N.M.fr τ) e ψ) := by
  first | exact @GlobalTheory.CuspKFin.kFinAt_avg | exact GlobalTheory.CuspKFin.kFinAt_avg | (intros; apply GlobalTheory.CuspKFin.kFinAt_avg <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinZeta

theorem isSBHalf_levDatum : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (LT : LevDat D.host.E ℂ T.rank) (Q : Finset (Pl D.host.E)) (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Z : Finset (Pl D.host.E)) (e : AE D), IsSelfDualC S ΛS → IsSelfDualC T ΛT → IsFrame βS ΛS → IsFrame βT ΛT → IsIdemSum e Z → IsSBHalf (cA D e) (latO S T ΛS ΛT fun _ => True) (levDatum S T βS βT LT Q m e) := by
  intro D S T ΛS ΛT βS βT LT Q m Z e hS hT hfS hfT he
  classical

  have hlin : ∀ (k : ℕ) (u : WO S T), frMapAdj S T βS βT (k • u) = k • frMapAdj S T βS βT u := by
    intro k u
    induction k with
    | zero =>
      have h0 := GlobalTheory.PlaceVec.frMapAdj_add S T βS βT 0 0
      simpa using h0
    | succ n ih =>
      rw [succ_nsmul, GlobalTheory.PlaceVec.frMapAdj_add, ih, succ_nsmul]
  have hadd : ∀ (x u : WO S T) (k : ℕ) i j,
      frMapAdj S T βS βT (x + k • u) i j = frMapAdj S T βS βT x i j + k * frMapAdj S T βS βT u i j := by
    intro x u k i j
    rw [GlobalTheory.PlaceVec.frMapAdj_add, hlin, Matrix.add_apply, Matrix.smul_apply, nsmul_eq_mul]

  have hB : ∃ M : ℕ, 0 < M ∧ ∀ u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E))
      (fun _ => True), ∀ i j, (M : EAf D) * frMapAdj S T βS βT u i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    obtain ⟨M, hM, hMl⟩ := GlobalTheory.PlaceDatum.exists_den_latO (S := S) (T := T) hS.1.fg hT.1.fg
    obtain ⟨k, hk, hup⟩ := GlobalTheory.PlaceVec.frMapAdj_up S T βS βT
    refine ⟨k * M, Nat.mul_pos hk hM, fun u hu i j => ?_⟩
    have hint : IsIntM ((M • u).map (toEAf D)) := by
      intro a b
      rw [Matrix.map_apply, Matrix.smul_apply, map_nsmul, nsmul_eq_mul]
      exact hMl u hu a b
    have h := hup (M • u) hint i j
    rw [hlin, Matrix.smul_apply, Matrix.smul_apply, nsmul_eq_mul, nsmul_eq_mul, ← mul_assoc] at h
    simpa [Nat.cast_mul] using h

  have hC : ∃ K : ℕ, 0 < K ∧ ∀ t, IsHalf (cA D e) t → IsIntM (frMapAdj S T βS βT t) →
      K • t ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) := by
    obtain ⟨k, hk, hdown⟩ := GlobalTheory.PlaceVec.frMapAdj_down S T βS βT
    obtain ⟨K, hK, hKl⟩ := GlobalTheory.PlaceDatum.exists_nsmul_mem_latO (S := S) (T := T)
      (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hS)
      (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hT)
    refine ⟨K * k, Nat.mul_pos hK hk, fun t ht hti => ?_⟩
    have hinf : t.map (infPart D) = 0 :=
      GlobalTheory.PlaceDatum.infPart_of_half (GlobalTheory.PlaceDatum.infPart_cA (GlobalTheory.PlaceDatum.infPart_idemSum he)) ht
    have hinf' : (k • t).map (infPart D) = 0 := by
      ext a b
      have h1 := congrFun (congrFun hinf a) b
      rw [Matrix.map_apply, Matrix.zero_apply] at h1
      rw [Matrix.map_apply, Matrix.smul_apply, map_nsmul, h1, smul_zero, Matrix.zero_apply]
    have hint' : ∀ a b, toEAf D ((k • t) a b) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
      intro a b
      have h2 := hdown t hti a b
      rwa [Matrix.smul_apply, Matrix.map_apply, ← map_nsmul] at h2
    rw [← smul_smul]
    exact hKl (k • t) hinf' hint'

  have hω : ∀ y y' : (∀ PP : Pl D.host.E, Matrix (Fin S.rank) (Fin T.rank) (kP PP)),
      (∀ PP ∈ LT.Pg ∪ Q, y PP = y' PP) →
        omegaG LT m y * omegaQ Q T.rank m (-1) y = omegaG LT m y' * omegaQ Q T.rank m (-1) y' := by
    intro y y' h
    rw [GlobalTheory.PlaceDatum.omegaG_congr LT m y y' (fun PP hP => h PP (Finset.mem_union_left _ hP)),
      GlobalTheory.PlaceDatum.omegaQ_congr Q T.rank m (-1) y y' (fun PP hP => h PP (Finset.mem_union_right _ hP))]
  have key := GlobalTheory.PlaceDatum.isSBHalf_of_red (cA D e)
    (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)
    (frMapAdj S T βS βT) hadd hB hC (LT.Pg ∪ Q) (fun y => omegaG LT m y * omegaQ Q T.rank m (-1) y) hω
  unfold levDatum
  exact key

end GlobalTheory.FinZeta

end
end
