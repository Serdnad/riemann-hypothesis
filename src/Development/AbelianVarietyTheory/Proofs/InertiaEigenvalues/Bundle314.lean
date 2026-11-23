module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
public import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
public import Development.AbelianVarietyTheory.Definitions.Divisors.EntireEqOfHalfPlane
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle298
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle003
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle299
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleOrbitalFourierRankOneTransfer
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWeakTopologyWittTiltTensor
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAlgClosedTiltFieldAndValuationRing
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle006
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle307
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle233
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle008
public import Development.AbelianVarietyTheory.CrystallinePeriods.CrisMapsLoc
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle288
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle226
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle289
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.SimpleRing.Principal
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
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle009
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle012
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAuxiliaryHeckeCharacter
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle193
import Formalism.ConjugateSelfDual.Bundle001
import Formalism.FrobeniusOrbits.Statement
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import ReciprocityTheory.GaloisValuations.GlobalA
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PeriodDiscExtensionTateElement
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

section

noncomputable section

namespace GlobalTheory.TripleLocal

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
open GlobalTheory.Pst GlobalTheory.GalOfCusp GlobalTheory.TripleGal
open GlobalTheory.TypeLeaf (FrobDense)

theorem exists_aut {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [Algebra ℤ_[l] O]
    (φ ψ : O →+* Qbar l) (hφ : Function.Injective φ) (hψ : Function.Injective ψ)
    (hφ' : ∀ z : ℤ_[l], φ (algebraMap ℤ_[l] O z) = algebraMap ℚ_[l] (Qbar l) (z : ℚ_[l]))
    (hψ' : ∀ z : ℤ_[l], ψ (algebraMap ℤ_[l] O z) = algebraMap ℚ_[l] (Qbar l) (z : ℚ_[l])) :
    ∃ γ : Qbar l ≃+* Qbar l, ∀ x, γ (φ x) = ψ x := by
  have halg : Algebra.IsAlgebraic ℤ_[l] (Qbar l) :=
    haveI := IsLocalization.isAlgebraic (R := ℤ_[l]) ℚ_[l] (nonZeroDivisors ℤ_[l])
    Algebra.IsAlgebraic.trans ℤ_[l] ℚ_[l] (Qbar l)
  have key : ∀ (f : O →+* Qbar l) (hf : Function.Injective f),
      (∀ z : ℤ_[l], f (algebraMap ℤ_[l] O z) = algebraMap ℚ_[l] (Qbar l) (z : ℚ_[l])) →
      letI := f.toAlgebra
      haveI : Module.IsTorsionFree O (Qbar l) := Module.isTorsionFree_iff_algebraMap_injective.2 hf
      IsAlgClosure O (Qbar l) := fun f hf hf' => by
    letI := f.toAlgebra
    haveI : Module.IsTorsionFree O (Qbar l) := Module.isTorsionFree_iff_algebraMap_injective.2 hf
    haveI : IsScalarTower ℤ_[l] O (Qbar l) := IsScalarTower.of_algebraMap_eq fun z => (hf' z).symm
    have hi : Function.Injective (algebraMap ℤ_[l] O) := fun x y h => by
      have := (hf' x).symm.trans ((congrArg f h).trans (hf' y))
      exact Subtype.ext ((algebraMap ℚ_[l] (Qbar l)).injective this)
    exact ⟨inferInstance, Algebra.IsAlgebraic.extendScalars hi⟩
  let e := @IsAlgClosure.equiv O _ _ (Qbar l) (Qbar l) _ _ ψ.toAlgebra
    (@Module.isTorsionFree_iff_algebraMap_injective _ _ _ _ ψ.toAlgebra _ _ |>.2 hψ) (key ψ hψ hψ') φ.toAlgebra
    (@Module.isTorsionFree_iff_algebraMap_injective _ _ _ _ φ.toAlgebra _ _ |>.2 hφ) (key φ hφ hφ')
  exact ⟨@AlgEquiv.toRingEquiv O _ _ _ _ _ φ.toAlgebra ψ.toAlgebra e,
    fun x => @AlgEquiv.commutes O _ _ _ _ _ φ.toAlgebra ψ.toAlgebra e x⟩

variable {D : D7} {i : D.ntw.Tw} {j : FractionRing (D.ntw.O0 i) →+* ℂ}
  {ρ : G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.ntw.O0 i)} {π : D.naut.CG D.R.r} {s : ℝ}

def brEmb (i : D.ntw.Tw) (v : PlE D.host) (hv : v ∈ placesOver D.host.E (D.ntw.l i)) : D.ntw.O0 i →+* Qbar (D.ntw.l i) :=
  (algebraMap ↥(D.ntwbr i v hv).LL.1 (Om (D.ntw.l i))).comp (D.ntwbr i v hv).toLL

theorem isModel_brEmb (v : PlE D.host) (hv : v ∈ placesOver D.host.E (D.ntw.l i)) :
    IsModel (D.ntwbr i v hv) (resDec D.nd.plOm.1 (mapRep (brEmb i v hv) ρ) v) (D.ntwbr i v hv).LL
      (mapRep (D.ntwbr i v hv).toLL (ρ.comp (DecV D.nd v).subtype)) :=
  ⟨le_rfl, by ext g a b; rfl⟩

end GlobalTheory.TripleLocal

end
end

section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie

namespace GlobalTheory.LamTie.GridCharacters

theorem levelLe_of_le {E : Type} [Field E] [NumberField E] {χ : Formalism.L2.Host.HChar E} {w : HeightOneSpectrum (𝓞 E)} {m n : ℕ}
    (h : χ.LevelLe w m) (hmn : m ≤ n) : χ.LevelLe w n := fun x hx hx' =>
  h x hx (hx'.trans (WithZero.exp_le_exp.2 (by omega)))

theorem expAt_succ {E : Type} [Field E] [NumberField E] {χ : Formalism.L2.Host.HChar E} {w : HeightOneSpectrum (𝓞 E)} {n : ℕ}
    (h : χ.LevelLe w (n + 1)) (h' : ¬ χ.LevelLe w n) : ExpAt χ w (n + 1) := fun m =>
  ⟨fun hm => by
    by_contra hlt
    exact h' (levelLe_of_le hm (by omega)), fun hm => levelLe_of_le h hm⟩

end GlobalTheory.LamTie.GridCharacters
end

section

open GlobalTheory.UnitLemma Polynomial

theorem _root_.GlobalTheory.T.unitLemma_local_oddResidue_of_lieAlgebra : UnitLemmaLie → ∀ (K : UQ), K.Odd → ∀ B₁ B₂ : InvAlg K, B₁.g * B₁.σ B₁.g = 1 → B₂.g * B₂.σ B₂.g = 1 → (B₁.P * B₂.P).Separable → IsIntegral K.O B₁.g → IsIntegral K.O B₂.g → IsLocalRing (Algebra.adjoin K.O ({(B₁.prod B₂).g} : Set (B₁.prod B₂).A)) → InvAlg.Identity B₁ B₂ := by
  first | exact @GlobalTheory.UnitLemma.Unr.unitLemma_local_of_lie | exact GlobalTheory.UnitLemma.Unr.unitLemma_local_of_lie | (intros; apply GlobalTheory.UnitLemma.Unr.unitLemma_local_of_lie <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.exists_test_orbU_eq_orbL : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (m : A.Meas ψ) (r : ℕ) (M : Meas r F E) (τ : A.K) (p : Fin r → F) (lam : F), A.IsGen τ p → ∀ (x : A.Kˣ) (j : A.L ≃ₗ[E] (Fin r → E)), A.IsIsom x j → ∀ Ax : selfAdjoint (Matrix (Fin r) (Fin r) E), (∀ z, j (algebraMap A.K A.L τ * z) = Ax.1 *ᵥ j z) → ∀ f : Hn r F E → ℂ, IsTest f → ∃ φ : A.L → ℂ, IsTest φ ∧ ∀ y : A.L, IsUnit y → orbU M f (Ax, j y, lam) = A.orbL m.ν φ y ∧ orbU M (fourU M ψ f) (Ax, j y, lam) = A.orbL m.ν (fourB (m.μL x) (A.kerL ψ x) φ) y := by
  first | exact @GlobalTheory.JR.unitary_orbital_descent | exact GlobalTheory.JR.unitary_orbital_descent | (intros; apply GlobalTheory.JR.unitary_orbital_descent <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.weilRepresentationEtale_of_quadraticField : WeilField → WeilEt := by
  first | exact @GlobalTheory.JR.weilEt_of_weilField | exact GlobalTheory.JR.weilEt_of_weilField | (intros; apply GlobalTheory.JR.weilEt_of_weilField <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.etaleOrbitalFourier_rankOne_transfer : RankOne := by
  first | exact @GlobalTheory.JR.RankOneTransfer.rankOne | exact GlobalTheory.JR.RankOneTransfer.rankOne | (intros; apply GlobalTheory.JR.RankOneTransfer.rankOne <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL

namespace GlobalTheory.WeakClosed

set_option synthInstance.maxHeartbeats 400000

instance vrOCb (l : ℕ) [Fact l.Prime] : ValuationRing (OCb l) :=
  (GlobalTheory.TiltAlgClosed.isAlgClosed_tilt_and_valuationRing l).2

@[reducible] def cbValued (l : ℕ) [Fact l.Prime] :
    Valued (Cb l) (ValuationRing.ValueGroup (OCb l) (Cb l)) :=
  Valued.mk' (ValuationRing.valuation (OCb l) (Cb l))

@[reducible] def cbTop (l : ℕ) [Fact l.Prime] : TopologicalSpace (Cb l) :=
  (cbValued l).toUniformSpace.toTopologicalSpace

@[reducible] def wTop (l : ℕ) [Fact l.Prime] : TopologicalSpace (WCb l) :=
  @GlobalTheory.WeakTop.wittTop l (Cb l) (cbTop l)

variable {l : ℕ} [Fact l.Prime]

@[reducible] def zlMod {K LL : FinExt l} (T : Lt K LL) : Module ℤ_[l] ↥T.L.T :=
  Module.compHom ↥T.L.T (algebraMap ℤ_[l] ↥(OL LL))

theorem zlTower_gen {O M : Type} [CommRing O] [Algebra ℤ_[l] O] [AddCommGroup M] [Module O M] :
    letI := Module.compHom M (algebraMap ℤ_[l] O)
    IsScalarTower ℤ_[l] O M :=
  letI := Module.compHom M (algebraMap ℤ_[l] O)
  ⟨fun c a x => by rw [Algebra.smul_def, mul_smul]; rfl⟩

theorem zlTower {K LL : FinExt l} (T : Lt K LL) :
    @IsScalarTower ℤ_[l] ↥(OL LL) ↥T.L.T _ _ (zlMod T).toSMul :=
  zlTower_gen

abbrev LatB {K LL : FinExt l} (T : Lt K LL) (d : ℕ) : Type :=
  @Module.Basis (Fin d) ℤ_[l] ↥T.L.T _ _ (zlMod T)

@[reducible] def twTop {K LL : FinExt l} (T : Lt K LL) {d : ℕ} (b : LatB T d) :
    TopologicalSpace (TW (RW LL) T) :=
  letI := zlMod T
  haveI := zlTower T
  TopologicalSpace.induced (GlobalTheory.WeakTop.coords (WCb l) ↥(OL LL) b)
    (@Pi.topologicalSpace (Fin d) (fun _ => WCb l) (fun _ => wTop l))

@[reducible] def oTop {LL : FinExt l} {e : ℕ} (bO : Module.Basis (Fin e) ℤ_[l] ↥(OL LL)) :
    TopologicalSpace ↥(OL LL) :=
  TopologicalSpace.induced bO.equivFun inferInstance

@[reducible] def aTop {K LL : FinExt l} {e : ℕ} (bO : Module.Basis (Fin e) ℤ_[l] ↥(OL LL)) :
    TopologicalSpace (AA K LL) :=
  letI := oTop bO
  @Pi.topologicalSpace _ _ fun _ => PowerSeries.WithPiTopology.instTopologicalSpace ↥(OL LL)

end GlobalTheory.WeakClosed
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL GlobalTheory.HWL.Cmp

namespace GlobalTheory.HWL.LevExp

theorem eq_exp {F : Type} [Field F] [CharZero F] [Algebra ℚ F] (E : PowerSeries F)
    (h0 : PowerSeries.constantCoeff E = 1) (h1 : PowerSeries.derivative (R := F) E = E) :
    E = PowerSeries.exp F := by
  exact PowerSeries.exp_unique_of_derivative_eq_self h1 h0

theorem map_poly {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {n : ℕ} (f : LetA O n →ₐ[O] A)
    (i : ZMod n) (hf : ∀ a, a i = 0 → f a = 0) (p : ZMod n → Polynomial O) :
    f (fun j => ((p j : Polynomial O) : PowerSeries O)) = Polynomial.aeval (f letπ) (p i) := by
  have hfam : f (fun j => ((p j : Polynomial O) : PowerSeries O)) =
      f (fun _ => ((p i : Polynomial O) : PowerSeries O)) := by
    have h := hf ((fun j => ((p j : Polynomial O) : PowerSeries O)) -
      (fun _ => ((p i : Polynomial O) : PowerSeries O))) (by simp)
    rwa [map_sub, sub_eq_zero] at h
  rw [hfam]
  have hg : f.comp ((Pi.constAlgHom O (ZMod n) (PowerSeries O)).comp
      (Polynomial.coeToPowerSeries.algHom O)) = Polynomial.aeval (f letπ) := by
    apply Polynomial.algHom_ext
    simp only [AlgHom.comp_apply, Polynomial.aeval_X, Polynomial.coeToPowerSeries.algHom_apply,
      Polynomial.coe_X, Algebra.algebraMap_self, PowerSeries.map_id]
    rfl
  have h2 := congrArg (fun φ => φ (p i)) hg
  simp only [AlgHom.comp_apply, Polynomial.coeToPowerSeries.algHom_apply, Algebra.algebraMap_self,
    PowerSeries.map_id] at h2
  exact h2

theorem map_poly_series {O L : Type} [CommRing O] [CommRing L] [Algebra O L] {n : ℕ}
    (f : LetA O n →ₐ[O] PowerSeries L) (i : ZMod n) (hf : ∀ a, a i = 0 → f a = 0) (p : ZMod n → Polynomial O) :
    f (fun j => ((p j : Polynomial O) : PowerSeries O)) =
      Polynomial.aeval (f letπ) ((p i).map (algebraMap O L)) := by
  rw [map_poly f i hf p, Polynomial.aeval_map_algebraMap]

theorem lev_isExp : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (s : ℕ) (LL : FinExt l) (Γ : GamS P K s LL) (R : WSer Γ), ∀ (i : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) (ζ : ↥LL.1), (∃ j : ℕ, IsPrimitiveRoot ζ (l ^ j)) → ∀ a : LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K)), IsExp ζ (toLL a i) (R.lev i ζ a) := by
  intro l _ P K s LL Γ R i ζ hζ a
  have hπ : R.lev i ζ letπ = PowerSeries.C ζ * PowerSeries.exp ↥LL.1 - 1 := by
    obtain ⟨E, hE0, hE1, hE⟩ := R.lev_π i ζ (by rw [P.PD_p K]; exact hζ)
    rw [eq_exp E hE0 hE1] at hE
    rw [← hE]
    ring
  have htr : ∀ m : ℕ, Polynomial.aeval (PowerSeries.C ζ * PowerSeries.exp ↥LL.1 - 1)
      (PowerSeries.trunc m (toLL a i)) =
      R.lev i ζ (fun j => ((PowerSeries.trunc m (a j) : Polynomial ↥(OL LL)) : PowerSeries ↥(OL LL))) := by
    intro m
    rw [map_poly_series (R.lev i ζ) i (R.lev_letter i ζ) (fun j => PowerSeries.trunc m (a j)), hπ]
    simp only [toLL, PowerSeries.trunc_map]
  intro k
  simp only [htr]
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  obtain ⟨r, hr⟩ : ∃ r : ℕ, (l : ℝ) ^ (-(r : ℝ)) < ε := by
    obtain ⟨r, hr⟩ := exists_pow_lt_of_lt_one hε (inv_lt_one_of_one_lt₀ hl)
    refine ⟨r, ?_⟩
    rw [Real.rpow_neg (by positivity), Real.rpow_natCast, ← inv_pow]
    exact hr
  obtain ⟨m₀, hm₀⟩ := R.lev_cont i ζ a k r
  refine ⟨m₀, fun m hm => ?_⟩
  have hv := hm₀ m hm
  rw [← WithTop.coe_natCast] at hv
  have hn := ((NormVal.locPrime_v_normalised l P LL).2.1 _ (r : ℚ)).1 hv
  rw [dist_eq_norm, ← norm_neg, neg_sub]
  calc _ = _ := by push_cast; rfl
    _ ≤ _ := hn
    _ = (l : ℝ) ^ (-(r : ℝ)) := by push_cast; rfl
    _ < ε := hr

end GlobalTheory.HWL.LevExp
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem jumpSum_wild_top_le_of_detects : ∀ (F L : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra F L] [ValuativeExtension F L] [FiniteDimensional F L] [IsGalois F L] (p E r : ℕ) (B : Subgroup (L ≃ₐ[F] L)), p.Prime → 0 < E → OrdIs L p E → AxIn F L p → Detects p r ⊤ B → jumpSum (wild F L) ⊤ B ≤ 6 * E := by
  intro F L _ _ _ _ _ _ _ _ _ _ _ _ p E r B hp hE hord hax hdet
  obtain ⟨hanti, hbot⟩ := GlobalTheory.T.wildLowerRamificationGroup_antitone_eventually_bot F L
  obtain ⟨n, hn⟩ := GlobalTheory.T.exists_initialSegment_not_inf_le_filtration _ (wild F L) ⊤ B hanti hbot
  rcases n with _ | k
  · rw [GlobalTheory.T.ramificationJumpSum_eq_sum_range _ (wild F L) ⊤ B 0 hanti hn]
    simp
  · have hk : ¬ (⊤ : Subgroup (L ≃ₐ[F] L)) ⊓ wild F L k ≤ B := (hn k).1 (Nat.lt_succ_self k)
    obtain ⟨σ₀, hσ₀, hσ₀B⟩ := SetLike.not_le_iff_exists.1 hk
    have hσ₀k : σ₀ ∈ wild F L k := (Subgroup.mem_inf.1 hσ₀).2
    obtain ⟨x, a, hxa, hnd⟩ := hdet σ₀ (Subgroup.mem_top σ₀) hσ₀B
    obtain ⟨J, hJ, hJsum⟩ := GlobalTheory.T.jumpSum_kernel_coboundaryChar_le_six_mul F L p E r x a hp hE hord hax
      (fun σ => hxa σ (Subgroup.mem_top σ)) ⟨σ₀, hnd⟩
    have hσ₀J : σ₀ ∉ J := fun h => hnd ((hJ σ₀).1 h)
    have hmono : ∀ t, (⊤ : Subgroup (L ≃ₐ[F] L)) ⊓ wild F L t ≤ J → (⊤ : Subgroup (L ≃ₐ[F] L)) ⊓ wild F L t ≤ B := by
      intro t ht
      by_contra hB
      have htk : t ≤ k := Nat.lt_succ_iff.1 ((hn t).2 hB)
      have hσ₀t : σ₀ ∈ wild F L t := hanti htk hσ₀k
      exact hσ₀J (ht (Subgroup.mem_inf.2 ⟨Subgroup.mem_top σ₀, hσ₀t⟩))
    exact le_trans (GlobalTheory.T.ramificationJumpSum_mono_of_le _ (wild F L) ⊤ B J hanti hbot hmono) hJsum

end GlobalTheory.PMon.Ram
end

section

open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.norm_tiltUntilt_le_of_frobeniusSeries_size_le : ∀ (l : ℕ) [Fact l.Prime] (h : ℕ) (ρ : ℝ) (x : Fl l), 2 ≤ h → 0 ≤ ρ → ρ < 1 → ‖sh x‖ < 1 → (∀ j : ℕ, j < 2 → ‖lam h j x‖ ≤ gam l h j ρ) → ‖sh x‖ ≤ ρ := by
  first | exact @GlobalTheory.PSer.norm_sh_le_of_lam_le | exact GlobalTheory.PSer.norm_sh_le_of_lam_le | (intros; apply GlobalTheory.PSer.norm_sh_le_of_lam_le <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

theorem _root_.GlobalTheory.T.card_le_wild_jumpSum_totallyRamified : ∀ (F L : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra F L] [ValuativeExtension F L] [FiniteDimensional F L] [IsGalois F L] (p E : ℕ) (B : Subgroup (L ≃ₐ[F] L)), p.Prime → 0 < E → lowerRamificationGroup F L 0 = ⊤ → OrdIs L p E → (∀ σ τ : L ≃ₐ[F] L, σ * τ * σ⁻¹ * τ⁻¹ ∈ B) → (∀ σ : L ≃ₐ[F] L, σ ^ p ∈ B) → B ≠ ⊤ → Nat.card (L ≃ₐ[F] L) ≤ jumpSum (wild F L) ⊤ B := by
  first | exact @GlobalTheory.PMon.Ram.card_le_jumpSum_wild_of_exponent | exact GlobalTheory.PMon.Ram.card_le_jumpSum_wild_of_exponent | (intros; apply GlobalTheory.PMon.Ram.card_le_jumpSum_wild_of_exponent <;> assumption)
end

section

noncomputable section

open scoped Formalism.Per

namespace GlobalTheory.PMon.Gauss

variable {l : ℕ} [Fact l.Prime]

theorem iSup_pow_eq {f : ℕ → ℝ} (h0 : ∀ n, 0 ≤ f n) (hb : BddAbove (Set.range f)) (k : ℕ) :
    (⨆ n, f n ^ k) = (⨆ n, f n) ^ k := by
  have hS : 0 ≤ ⨆ n, f n := le_ciSup_of_le hb 0 (h0 0)
  have hle : ∀ n, f n ^ k ≤ (⨆ n, f n) ^ k := fun n => pow_le_pow_left₀ (h0 n) (le_ciSup hb n) k
  have hb' : BddAbove (Set.range fun n => f n ^ k) := ⟨_, Set.forall_mem_range.2 hle⟩
  refine le_antisymm (ciSup_le hle) ?_
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  by_contra hlt
  push_neg at hlt
  set T := ⨆ n, f n ^ k
  have hT : 0 ≤ T := le_ciSup_of_le hb' 0 (pow_nonneg (h0 0) k)
  have hroot : T ^ ((1 : ℝ) / k) < ⨆ n, f n := by
    have := Real.rpow_lt_rpow hT hlt (by positivity : (0 : ℝ) < 1 / k)
    rwa [← Real.rpow_natCast, ← Real.rpow_mul hS, mul_one_div_cancel (by positivity), Real.rpow_one] at this
  obtain ⟨n, hn⟩ := exists_lt_of_lt_ciSup hroot
  have h1 := pow_lt_pow_left₀ hn (Real.rpow_nonneg hT _) hk.ne'
  rw [← Real.rpow_natCast, ← Real.rpow_mul hT, one_div_mul_cancel (by positivity), Real.rpow_one] at h1
  exact absurd (le_ciSup hb' n) (not_le.2 h1)

theorem gA_phi (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (a : Formalism.Per.Ainf l) :
    gA l ρ (Formalism.Per.φA l a) = gA l (ρ ^ ((1 : ℝ) / l)) a ^ l := by
  have hl : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  set σ := ρ ^ ((1 : ℝ) / l)
  have hσ0 : 0 ≤ σ := Real.rpow_nonneg hρ0 _
  have hσ1 : σ ≤ 1 := Real.rpow_le_one hρ0 hρ1 (by positivity)
  have hσl : σ ^ l = ρ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hρ0, one_div_mul_cancel hl.ne', Real.rpow_one]
  set f : ℕ → ℝ := fun n => ‖(((a.coeff n).untilt : Formalism.Per.OC l) : ℂ_[l])‖ ^ ((1 : ℝ) / (l : ℝ) ^ n) * σ ^ n
  have hf0 : ∀ n, 0 ≤ f n := fun n => by positivity
  have hf1 : ∀ n, f n ≤ 1 := fun n =>
    mul_le_one₀ (Real.rpow_le_one (norm_nonneg _) ((GlobalTheory.RingBasics.mem_OC _).1 (Subtype.prop _)) (by positivity))
      (pow_nonneg hσ0 _) (pow_le_one₀ hσ0 hσ1)
  have hterm : ∀ n, ‖((((Formalism.Per.φA l a).coeff n).untilt : Formalism.Per.OC l) : ℂ_[l])‖ ^ ((1 : ℝ) / (l : ℝ) ^ n) * ρ ^ n
      = f n ^ l := by
    intro n
    have hc : (Formalism.Per.φA l a).coeff n = a.coeff n ^ l := by
      rw [GlobalTheory.RingBasics.φA_apply, WittVector.coeff_frobenius_charP]
    rw [hc, map_pow, SubmonoidClass.coe_pow, norm_pow, ← hσl, mul_pow, ← pow_mul, ← pow_mul, mul_comm n l, pow_mul]
    congr 1
    rw [← Real.rpow_natCast_mul (norm_nonneg _), ← Real.rpow_mul_natCast (norm_nonneg _), mul_comm]
  simp only [gA]
  simp_rw [hterm]
  exact iSup_pow_eq hf0 ⟨1, Set.forall_mem_range.2 hf1⟩ l

theorem isGauss_phi (ρ : ℝ) (h0 : (l : ℝ)⁻¹ ≤ ρ) (h1 : ρ < 1) :
    IsGauss l (ρ ^ ((1 : ℝ) / l)) (fun x => gC l ρ (φc l x) ^ ((1 : ℝ) / l)) := by
  have hl : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  have hρ0 : 0 ≤ ρ := (inv_nonneg.2 hl.le).trans h0
  obtain ⟨e1, e2, e3, e4, e5⟩ := isGauss_gC_of_le l ρ h0 h1
  have hpos : (0 : ℝ) < 1 / l := by positivity
  refine ⟨fun x => ⟨Real.rpow_nonneg (e1 _).1 _, Real.rpow_le_one (e1 _).1 (e1 _).2 hpos.le⟩, fun x y => ?_,
    fun x => ?_, fun x y => ?_, fun a => ?_⟩
  · simp only [map_add (f := _)]
    refine (Real.rpow_le_rpow (e1 _).1 (e2 _ _) hpos.le).trans ?_
    rcases le_total (gC l ρ (φc l x)) (gC l ρ (φc l y)) with h | h
    · rw [max_eq_right h, max_eq_right (Real.rpow_le_rpow (e1 _).1 h hpos.le)]
    · rw [max_eq_left h, max_eq_left (Real.rpow_le_rpow (e1 _).1 h hpos.le)]
  · simp only [map_neg, e3]
  · simp only [map_mul, e4]
    exact Real.mul_rpow (e1 _).1 (e1 _).1
  · simp only
    have ha : φc l (algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l) a) =
        algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l) (Formalism.Per.φA l a) := (GlobalTheory.CrisMaps.phiA_extends l).alg a
    rw [ha, e5, gA_phi ρ hρ0 h1.le, ← Real.rpow_natCast, ← Real.rpow_mul, mul_one_div_cancel hl.ne', Real.rpow_one]
    exact le_ciSup_of_le ⟨1, by
      rintro _ ⟨n, rfl⟩
      exact mul_le_one₀ (Real.rpow_le_one (norm_nonneg _) ((GlobalTheory.RingBasics.mem_OC _).1 (Subtype.prop _)) (by positivity))
        (pow_nonneg (Real.rpow_nonneg hρ0 _) _) (pow_le_one₀ (Real.rpow_nonneg hρ0 _)
          (Real.rpow_le_one hρ0 h1.le (by positivity)))⟩ 0 (by positivity)

theorem gC_phi : ∀ (l : ℕ) [Fact l.Prime] (ρ : ℝ), (l : ℝ)⁻¹ ≤ ρ → ρ < 1 → ∀ x : Formalism.Per.Acris l,
    gC l ρ (φc l x) = gC l (ρ ^ ((1 : ℝ) / l)) x ^ l := by
  intro l _ ρ h0 h1 x
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hl : (0 : ℝ) < l := by linarith
  have hρ0 : 0 ≤ ρ := (inv_nonneg.2 hl.le).trans h0
  have hσ0 : ρ ≤ ρ ^ ((1 : ℝ) / l) := by
    conv_lhs => rw [← Real.rpow_one ρ]
    exact Real.rpow_le_rpow_of_exponent_ge' hρ0 h1.le (by positivity)
      (by rw [div_le_one hl]; exact hl1.le)
  have hσ1 : ρ ^ ((1 : ℝ) / l) < 1 := Real.rpow_lt_one hρ0 h1 (by positivity)
  have e := GlobalTheory.T.gaussNormAcris_unique l (ρ ^ ((1 : ℝ) / l)) _ _ (h0.trans hσ0) hσ1 (isGauss_phi ρ h0 h1)
    (isGauss_gC_of_le l _ (h0.trans hσ0) hσ1)
  have ex : gC l ρ (φc l x) ^ ((1 : ℝ) / l) = gC l (ρ ^ ((1 : ℝ) / l)) x := congrFun e x
  rw [← ex, ← Real.rpow_natCast, ← Real.rpow_mul ((isGauss_gC_of_le l ρ h0 h1).1 _).1,
    one_div_mul_cancel hl.ne', Real.rpow_one]

end GlobalTheory.PMon.Gauss

end
end
