module

import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle033
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.RingTheory.Ideal.Prime
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle012
public import Formalism.SatakeDualWeyl.StatementG
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAHEqOfMemRatPts
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemSiegelOfIffRightAct
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIntegralKeepsDoublingDiagonalAdicCompletio
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle003
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle083
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HoweDualityUnitarySubstitutionSpanUnit
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ColHeightSharpWith
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1019
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle084
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart
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
import Mathlib.RingTheory.PicardGroup
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle010
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle038

@[expose] public section

section

namespace GlobalTheory.ExistsPrimeMem

theorem exists_prime_mem {A : Type} [inst : CommRing A] (P : Ideal A) (hP : Ideal.IsPrime P) :
    ∀ (n : ℕ), n ≠ (0 : ℕ) → (↑n : A) ∈ P → ∃ (ℓ : ℕ), Nat.Prime ℓ ∧ (↑ℓ : A) ∈ P := by
  apply GlobalTheory.PlaceInt.LocBasis.exists_prime_mem <;> assumption

end GlobalTheory.ExistsPrimeMem
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.PRep
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke ordL)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (bcParam)
open GlobalTheory.LFun (toCompl locMat locChar IsSplitChart IsInertChart IsFrameAt KGL IsSatVecGL IsSatVecU eulerFac UnrAt LvTw dv Fam)


theorem _root_.GlobalTheory.T.invariant_sphericalCoefficient_eq_zero_or_zonal : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : Lˣ) (σ : L →+* L) (q n : ℕ), IsUnramInv (ϖ : L) σ q → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GU σ n) V) (x : V) (α : Fin (n / 2) → ℂˣ), IsSatVecU (ϖ : L) q ρ x α → ∀ ℓ : V →ₗ[ℂ] ℂ, (∀ k ∈ KU σ n, ∀ g, ℓ (ρ (k * g) x) = ℓ (ρ g x)) → (ℓ x = 0 → ∀ g, ℓ (ρ g x) = 0) ∧ (ℓ x ≠ 0 → GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.IsZonal (ϖ : L) q α fun g => ℓ (ρ g x) / ℓ x) := by
  first | exact @GlobalTheory.ZonalCoeff.coeff_zero_or_zonal | exact GlobalTheory.ZonalCoeff.coeff_zero_or_zonal | (intros; apply GlobalTheory.ZonalCoeff.coeff_zero_or_zonal <;> assumption)
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.PRep
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke ordL)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (bcParam)
open GlobalTheory.LFun (toCompl locMat IsInertChart IsFrameAt)

noncomputable section

namespace GlobalTheory.DblInert

open Formalism.UG GlobalTheory.LFun.InertChart

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)} {σ : E →ₐ[F] E} {h : w.under (𝓞 F) = v}
  {c : w.adicCompletion E →+* w.adicCompletion E} {m : ℕ}

theorem bc_mem_iff_gram (hw : IsInertAt F E v w) (hc : GlobalTheory.LFun.IsConjAt σ h c) {J : Matrix (Fin m) (Fin m) E}
    {T : Matrix (Fin m) (Fin m) (w.adicCompletion E)} {a : GL (Fin m) (w.adicCompletion E)}
    (ha : cT c a.1 * J.map (algebraMap E _) * a.1 = T) (g : GL (Fin m) (Fv F v ⊗[F] E)) :
    g ∈ HR (Fv F v) σ J ↔ a⁻¹ * bc (toCompl h) g * a ∈ UJ c T := by
  have h1 : cT c (bc (toCompl h) g).1 = (cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ) g.1).map (toCompl h) :=
    Matrix.ext fun i j => hc _
  have h2 : g ∈ HR (Fv F v) σ J ↔ bc (toCompl h) g ∈ UJ c (J.map (algebraMap E _)) := by
    change _ ↔ cT c (bc (toCompl h) g).1 * _ * g.1.map (toCompl h) = _
    rw [h1, ← JR_map h, ← Matrix.map_mul, ← Matrix.map_mul]
    exact (Matrix.map_injective (toCompl_bijective hw h).1).eq_iff.symm
  have h3 : ∀ x : GL (Fin m) (w.adicCompletion E), cT c (a⁻¹ * x * a).1 * T * (a⁻¹ * x * a).1 =
      cT c a.1 * (cT c x.1 * J.map (algebraMap E _) * x.1) * a.1 := fun x => by
    rw [← ha, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← cT_mul, Matrix.mul_assoc, ← Units.val_mul, ← mul_assoc,
      mul_inv_cancel_left, Units.val_mul, cT_mul]
    simp only [Matrix.mul_assoc]
  have h4 : IsUnit (cT c a.1) := IsUnit.of_mul_eq_one (cT c (a⁻¹).1) (by rw [← cT_mul, Units.inv_mul, cT_one])
  rw [h2]
  change _ ↔ _ * _ * _ = _
  rw [h3, ← ha, a.isUnit.mul_left_inj, h4.mul_right_inj]
  rfl

def chartGram (hw : IsInertAt F E v w) (hc : GlobalTheory.LFun.IsConjAt σ h c) {J : Matrix (Fin m) (Fin m) E}
    {T : Matrix (Fin m) (Fin m) (w.adicCompletion E)} {a : GL (Fin m) (w.adicCompletion E)}
    (ha : cT c a.1 * J.map (algebraMap E _) * a.1 = T) : GLoc σ J v ≃* UJ c T :=
  have e1 : ∀ x : GL (Fin m) (w.adicCompletion E), bc (toCompl h) (bc (complEquiv hw h).symm.toRingHom x) = x :=
    fun _ => Units.ext (Matrix.ext fun _ _ => (complEquiv hw h).apply_symm_apply _)
  have e2 : ∀ x : GL (Fin m) (Fv F v ⊗[F] E), bc (complEquiv hw h).symm.toRingHom (bc (toCompl h) x) = x :=
    fun _ => Units.ext (Matrix.ext fun _ _ => (complEquiv hw h).symm_apply_apply _)
  { toFun := fun g => ⟨a⁻¹ * locMat σ J h g * a, (bc_mem_iff_gram hw hc ha _).1 g.2⟩
    invFun := fun u => ⟨bc (complEquiv hw h).symm.toRingHom (a * u * a⁻¹), (bc_mem_iff_gram hw hc ha _).2 (by
      rw [e1, show a⁻¹ * (a * u * a⁻¹) * a = u by group]; exact u.2)⟩
    left_inv := fun g => Subtype.ext ((congrArg (bc (complEquiv hw h).symm.toRingHom)
      (show a * (a⁻¹ * locMat σ J h g * a) * a⁻¹ = locMat σ J h g by group)).trans (e2 g.1))
    right_inv := fun u => Subtype.ext ((congrArg (a⁻¹ * · * a) (e1 _)).trans (by group))
    map_mul' := fun g g' => Subtype.ext (by simp only [map_mul, Subgroup.coe_mul]; group) }

section Conj

variable {A B n ι : Type} [CommRing A] [CommRing B] [Fintype n] [Fintype ι] [DecidableEq n] [DecidableEq ι]
  (e : n ⊕ n ≃ ι)

theorem blkGL_mem_diag (a : GL n A) : blkGL e (a, a) ∈ stabGL (diagSub A e) :=
  mem_stabGL_diagSub.2 ((keepsDiag_blkMat e).2 rfl)

theorem conj_mem_diag (a : GL n A) (x : GL ι A) :
    (blkGL e (a, a))⁻¹ * x * blkGL e (a, a) ∈ stabGL (diagSub A e) ↔ x ∈ stabGL (diagSub A e) := by
  rw [Subgroup.mul_mem_cancel_right _ (blkGL_mem_diag e a),
    Subgroup.mul_mem_cancel_left _ (inv_mem (blkGL_mem_diag e a))]

theorem bc_mem_diag {f : A →+* B} (hf : Function.Injective f) (x : GL ι A) :
    bc f x ∈ stabGL (diagSub B e) ↔ x ∈ stabGL (diagSub A e) := by
  rw [mem_stabGL_diagSub, mem_stabGL_diagSub]
  refine ⟨fun hx => (keepsDiag_iff e).2 fun i j => hf ?_, fun hx => hx.map e f⟩
  rw [map_add (f := _), map_add (f := _)]
  exact (keepsDiag_iff e).1 hx i j

theorem det_leviMat_conj (a : GL n A) {x : GL ι A} (hx : x ∈ stabGL (diagSub A e)) :
    (leviMat e ((blkGL e (a, a))⁻¹ * x * blkGL e (a, a)).1).det = (leviMat e x.1).det := by
  let D : stabGL (diagSub A e) →* Aˣ := Matrix.GeneralLinearGroup.det.comp (leviGL e)
  let b : stabGL (diagSub A e) := ⟨_, blkGL_mem_diag e a⟩
  have h1 : D (b⁻¹ * ⟨x, hx⟩ * b) = D ⟨x, hx⟩ := by
    rw [map_mul, map_mul, map_inv, inv_mul_cancel_comm]
  exact congrArg Units.val h1

end Conj

theorem exists_dblChart : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (Q : Matrix (Fin (n + n)) (Fin (n + n)) E) (hQ : Q = dblGram finSumFinEquiv J) (L : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsLattice E L], ∀ (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)) (h : w.under (𝓞 F) = v), IsInertAt F E v w → ∀ (c : w.adicCompletion E →+* w.adicCompletion E) (e : GLoc σ J v ≃* GU c n), IsInertChart σ J L h c e → ∃ f : GLoc σ Q v ≃* GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.GD c n, (∀ g, g ∈ KFin σ Q L v ↔ f g ∈ GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.KD c n) ∧ (∀ y, f (ioH _ σ hQ (y, 1)) = GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.io1 c n (e y)) ∧ (∀ g, g ∈ siegelH (Fv F v) σ Q ↔ f g ∈ GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.PD c n) ∧ ∀ (p : siegelH (Fv F v) σ Q) (hp : f p ∈ GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.PD c n), GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.aD c n ⟨f p, hp⟩ = Units.map (toCompl h).toMonoidHom (aH _ σ Q p) := by
  intro F E _ _ _ _ _ σ _ n J _ Q hQ L _ v w h hw c e he
  obtain ⟨hc, ⟨a, ha', ha, hea⟩, -⟩ := he
  have hA' : IsFrameAt w (sumLat finSumFinEquiv L L) (blkGL finSumFinEquiv (a, a)) :=
    GlobalTheory.LFun.isFrameAt_sumLat_blkGL E w n L a ha'
  have hT : cT c (blkGL finSumFinEquiv (a, a)).1 * Q.map (algebraMap E _) * (blkGL finSumFinEquiv (a, a)).1 =
      dblGram finSumFinEquiv (antiJ (w.adicCompletion E) n) := by
    rw [hQ, dblGram, blkMat_map _ _ (map_zero _), val_blkGL, cT_blkMat, blkMat_mul, blkMat_mul, ha,
      Matrix.map_neg _ (map_neg _), Matrix.mul_neg, Matrix.neg_mul, ha]
    rfl
  have hinj := (toCompl_bijective hw h).1
  refine ⟨chartGram hw hc hT, fun g => ?_, fun y => Subtype.ext ?_, fun g => ?_, fun p hp => Units.ext ?_⟩
  · refine Iff.trans ?_ (((isFrameAt_mul hA' (one_mem _)).2 (locMat σ Q h g)).trans
      ⟨fun hg => ⟨(chartGram hw hc hT g).2, hg⟩, fun hg => hg.2⟩)
    rw [mem_stabLoc]
    refine ⟨fun hg z => ?_, fun hg y => ?_⟩
    · obtain ⟨y, rfl⟩ := exists_comp h z
      rw [← mem_latLoc_iff hw, hg, mem_latLoc_iff hw h, comp_mulVec]
      rfl
    · rw [mem_latLoc_iff hw h, hg, mem_latLoc_iff hw h, comp_mulVec]
      rfl
  · change (blkGL finSumFinEquiv (a, a))⁻¹ * bc (toCompl h) (blkGL finSumFinEquiv
      (GlobalTheory.AdelicU.matHom _ σ J y, GlobalTheory.AdelicU.matHom _ σ J 1)) * blkGL finSumFinEquiv (a, a) =
        blkGL finSumFinEquiv ((e y : GL (Fin n) (w.adicCompletion E)), 1)
    rw [bc_blkGL, ← map_inv, ← map_mul, ← map_mul, hea, map_one, map_one, Prod.inv_mk, Prod.mk_mul_mk,
      Prod.mk_mul_mk, mul_one, inv_mul_cancel]
    rfl
  · exact ((conj_mem_diag finSumFinEquiv a _).trans (bc_mem_diag finSumFinEquiv hinj _)).symm
  · refine (det_leviMat_conj finSumFinEquiv a ((bc_mem_diag finSumFinEquiv hinj _).2 p.2)).trans ?_
    exact (congrArg Matrix.det (leviMat_map finSumFinEquiv (toCompl h) _)).trans (RingHom.map_det _ _).symm

end GlobalTheory.DblInert

end
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.PRep
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke ordL)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (bcParam)
open GlobalTheory.LFun (toCompl locMat locChar IsSplitChart IsInertChart IsFrameAt KGL IsSatVecGL IsSatVecU eulerFac UnrAt LvTw dv Fam)

namespace GlobalTheory.LFun

theorem LvTw_div_dv_inert_eq_stdL : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (B : Fam E) (m : HeightOneSpectrum (𝓞 E) → ℂˣ) (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)) (r b : ℕ) (α : Fin (r / 2) → ℂˣ) (s : ℂ), Module.finrank F E = 2 → IsInertAt F E v w → Formalism.MainNotions.SchurIrreducible.IsUnram (E := E) v → B w = bcParam r α → LvTw B m v (s + 1 / 2) / dv E r b v s = GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.stdL (qV F v) r α (((m w)⁻¹ : ℂˣ) : ℂ) (s + 1 / 2) / GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.dFac (qV F v) r b s := by
  intro F E _ _ _ _ _ B m v w r b α s h2 hw hU hB
  have hv := InertChart.under_eq_iff hw
  have hq := InertChart.absNorm_eq h2 hw
  have hq0 : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (one_lt_absNorm v).ne_bot
  have hns := not_isSplit_of_isInertAt hw
  rw [LvTw_inert B m hv hq, hB]
  congr 1
  · rw [GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.stdL, Units.val_inv_eq_inv_val]
    congr 2
    rw [npow, show qV F v = Ideal.absNorm v.asIdeal from rfl, pow_two,
      show -(2 * (s + 1 / 2)) = -(s + 1 / 2) + -(s + 1 / 2) by ring, Complex.cpow_add _ _ hq0,
      Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
  · rw [dv, GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.dFac]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [locL, etaFam_of_unram hU, eulerFac_singleton, GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.etaL, Units.val_pow_eq_pow_val, npow,
      show qV F v = Ideal.absNorm v.asIdeal from rfl]
    have he : ((etaU E v : ℂˣ) : ℂ) = -1 := by simp [etaU, hns]
    rw [he]

end GlobalTheory.LFun
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.PRep
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke ordL)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (bcParam)
open GlobalTheory.LFun (toCompl locMat locChar IsSplitChart IsInertChart IsFrameAt KGL IsSatVecGL IsSatVecU eulerFac UnrAt LvTw dv Fam)


theorem _root_.GlobalTheory.T.exists_integral_keepsDoublingDiagonal_adicCompletion : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (ϖ : w.adicCompletion E), IsUnifV E w ϖ → ∀ (d : Fin n → ℤ) (t k₁ k₂ : GL (Fin n) (w.adicCompletion E)), t.1 = Matrix.diagonal (fun i => ϖ ^ d i) → k₁ ∈ KGL w (n := n) → k₂ ∈ KGL w (n := n) → ∃ κ ∈ KGL w (n := (n + n)), KeepsDiag finSumFinEquiv (blkGL finSumFinEquiv (k₁ * t * k₂, 1) * κ).1 ∧ ordL (leviMat finSumFinEquiv (blkGL finSumFinEquiv (k₁ * t * k₂, 1) * κ).1).det = ∑ i, max (d i) 0 ∧ ordL (quotMat finSumFinEquiv (blkGL finSumFinEquiv (k₁ * t * k₂, 1) * κ).1).det = ∑ i, min (d i) 0 := by
  first | exact @GlobalTheory.GraphShear.graph_shear | exact GlobalTheory.GraphShear.graph_shear | (intros; apply GlobalTheory.GraphShear.graph_shear <;> assumption)
end

section

open PowerSeries GlobalTheory.Honda Formalism.L2.Th1.CM

theorem _root_.GlobalTheory.T.cmMultiplierIntegralSeriesAtInertPrime_proof : EndOmega := by
  first | exact @GlobalTheory.Honda.endOmega_holds | exact GlobalTheory.Honda.endOmega_holds | (intros; apply GlobalTheory.Honda.endOmega_holds <;> assumption)
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

theorem _root_.GlobalTheory.T.card_parahoricDoubleCosetReps_inv_eq : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (g : GL (A ⊕ D) k) (R R' : Finset (GL (A ⊕ D) k)) (d d' : GL (A ⊕ D) k → kˣ), IsReps g R d → IsReps g⁻¹ R' d' → R.card = R'.card ∧ R.Nonempty := by
  first | exact @GlobalTheory.ParHeckeCard.card_isReps_inv | exact GlobalTheory.ParHeckeCard.card_isReps_inv | (intros; apply GlobalTheory.ParHeckeCard.card_isReps_inv <;> assumption)
end

section

open MvPolynomial Formalism.BasicNotions Formalism.L2.Forms Formalism.L2.Ker GlobalTheory.KJInf MeasureTheory
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_invertibleFamily_eval_span : ∀ (ι : Type) [Fintype ι] (a : ℕ) (lam : ι → DomWeight a) (n : ι → ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] (T : PY ι a →ₗ[ℂ] W), ∃ (m : ℕ) (y : Fin m → ι → Matrix (Fin a) (Fin a) ℂ) (P : Fin m → W), (∀ j, IsInv (y j)) ∧ ∀ F ∈ Vn lam n, T F = ∑ j, evalAt (y j) F • P j := by
  first | exact @GlobalTheory.KJInf.exists_evalAt_span | exact GlobalTheory.KJInf.exists_evalAt_span | (intros; apply GlobalTheory.KJInf.exists_evalAt_span <;> assumption)
end

section

open MvPolynomial Formalism.BasicNotions Formalism.L2.Forms Formalism.L2.Ker GlobalTheory.KJInf MeasureTheory
open scoped TensorProduct

theorem _root_.GlobalTheory.T.howeDualityUnitarySubstitutionSpan_unit : HoweSpan Unit := by
  first | exact @GlobalTheory.HoweOne.howeSpan_unit | exact GlobalTheory.HoweOne.howeSpan_unit | (intros; apply GlobalTheory.HoweOne.howeSpan_unit <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open GlobalTheory.Core.Ht2
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.firstCoupledKernel_finiteDatum_level_size : ∀ (CY : ℝ) (D : D7) (N : NumDatum) (X : Fields) (s : Seam D X) (Pr : Primes X) (W : Wts X Pr.Word N.R) (Ch : Chars X Pr N.R.m) (G : ChGlob X N.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu)) (I : ChIdx X Pr N.R (QE sel (mu : Chr X.F X.E X.K))) (dl : ℂ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) (δ : Code N), HypS CY N s W Ch G sel mu cst I dl χ cD pl u δ → ∀ (al : I.β (N.R.m - 2)) (p₀ : ChPt (R := N.R) sel mu u (N.R.m - 2)) (p : ChPt (R := N.R) sel mu u (N.R.m - 2 + 1)) (Y : Set (Sp X.E (N.R.N (N.R.m - 2 + 1)))), SmallDatum (Sall sel mu u) p₀.deco.1.N p.deco.1.N (Pr.T u * (Pr.g 0 * Pr.g 1)) (XiCpl1 Ch sel mu cst I (N.R.m - 2) al p₀ p Y) 1 := by
  first | exact @GlobalTheory.Core.Ht2.DatOneS.smallDatum_xiCpl1_sharp | exact GlobalTheory.Core.Ht2.DatOneS.smallDatum_xiCpl1_sharp | (intros; apply GlobalTheory.Core.Ht2.DatOneS.smallDatum_xiCpl1_sharp <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open GlobalTheory.Core.Ht2
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.unfoldedEntry_typePrime_support_period_size : ∃ C : ℕ, ∀ (CY : ℝ) (D : D7) (N : NumDatum) (X : Fields) (s : Seam D X) (Pr : Primes X) (W : Wts X Pr.Word N.R) (Ch : Chars X Pr N.R.m) (G : ChGlob X N.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu)) (I : ChIdx X Pr N.R (QE sel (mu : Chr X.F X.E X.K))) (dl : ℂ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) (δ : Code N), HypS CY N s W Ch G sel mu cst I dl χ cD pl u δ → ∀ i, i + 2 < N.R.m → ∀ (al : I.β i) (be : I.β (i + 1)) (P : rowSG Pr sel mu), LocSmall (Formalism.L2.Col.qOf P.1) (stdAt X.E (N.R.N i) P.1) (stdAt X.E (N.R.N (i + 1)) P.1) (XiAt Ch sel mu cst i P (I.h i al P) (I.h (i + 1) be P)) ((Formalism.L2.Col.qOf P.1 : ℝ) ^ (C * N.R.m ^ 2 * N.Nm ^ 2)) := by
  first | exact @GlobalTheory.Core.Ht2.UnfoldS.locSmall_XiAt_sharp | exact GlobalTheory.Core.Ht2.UnfoldS.locSmall_XiAt_sharp | (intros; apply GlobalTheory.Core.Ht2.UnfoldS.locSmall_XiAt_sharp <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.RatPtsEquiv

theorem rat_equiv : ∀ (D : D7) (V : HSp D) (n : ℕ) (hn : V.rank = n), ∃ r : ↥(GQ V) ≃* ↥(UJ (sigD D : D.host.E →+* D.host.E) (V.gram.reindex (finCongr hn) (finCongr hn))), ∀ γ, finM V hn γ.1 = (bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (r γ).1).1 := by
  intro D V n hn
  subst hn
  have hinj : Function.Injective (incA D) :=
    Algebra.TensorProduct.includeRight_injective (NumberField.AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F)
  have hm : ∀ δ : ↥(UJ (sigD D : D.host.E →+* D.host.E) (V.gram.reindex (finCongr rfl) (finCongr rfl))),
      bc (incA D) δ.1 ∈ HR (AF D.host.F) D.sp.cm.sig V.gram := by
    intro δ
    have hδ' : cT (sigD D : D.host.E →+* D.host.E) δ.1.1 * V.gram * δ.1.1 = V.gram := δ.2
    have h2 := congrArg (fun M => M.map (incA D)) hδ'
    simp only [Matrix.map_mul] at h2
    exact h2
  let φ : ↥(UJ (sigD D : D.host.E →+* D.host.E) (V.gram.reindex (finCongr rfl) (finCongr rfl))) →* ↥(GQ V) :=
    { toFun := fun δ => ⟨⟨bc (incA D) δ.1, hm δ⟩, Subgroup.mem_subgroupOf.2 ⟨δ.1, δ.2, rfl⟩⟩
      map_one' := by
        apply Subtype.ext; apply Subtype.ext
        exact map_one (bc (incA D))
      map_mul' := by
        intro a b
        apply Subtype.ext; apply Subtype.ext
        exact map_mul (bc (incA D)) a.1 b.1 }
  have hφ : Function.Bijective φ := by
    constructor
    · intro a b h
      have h1 : (bc (incA D) a.1 : GL (Fin V.rank) _) = bc (incA D) b.1 := congrArg (fun x => x.1.1) h
      apply Subtype.ext; apply Units.ext
      refine Matrix.ext fun i j => ?_
      have := congrArg (fun x : GL (Fin V.rank) _ => x.1 i j) h1
      exact hinj this
    · intro γ
      obtain ⟨δ, hδ, e⟩ := Subgroup.mem_subgroupOf.1 γ.2
      exact ⟨⟨δ, hδ⟩, Subtype.ext (Subtype.ext e)⟩
  refine ⟨(MulEquiv.ofBijective φ hφ).symm, fun γ => ?_⟩
  set δ := (MulEquiv.ofBijective φ hφ).symm γ with hδ
  have hγ : γ = φ δ := by
    rw [hδ]; exact ((MulEquiv.ofBijective φ hφ).apply_symm_apply γ).symm
  rw [hγ]
  simp only [finM, finCongr_refl, Matrix.reindex_refl_refl]
  rfl

end GlobalTheory.RatPtsEquiv
end
end
