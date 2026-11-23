module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle017
public import Mathlib.Algebra.AffineMonoid.Basic
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle015
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle214
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle334
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocFacts
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocalDenominators
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LatExists
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.Bundle002
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.PoincareConstantEq
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle329
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardRowAutomorphismsEqLatticeStabilizer
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatsDiscStable
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle342
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitLatticeUnimodularAndPrimitive
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowsEqOfStabilizerConjugateLattices
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle007
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle344
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle001
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle002
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle123
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle338
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle296
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle337
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegrablePh
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle147
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle304
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.SameKindIsometric
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicFlagUnfoldingBound
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
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RowsConc
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle009

@[expose] public section

section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold

noncomputable section

namespace GlobalTheory.FixConvRow

theorem loc_gen {E : Type} [Field E] [NumberField E] (P : IsDedekindDomain.HeightOneSpectrum (𝓞 E))
    (J : Ideal (𝓞 E)) (hJ : J ≠ ⊥) :
    ∃ d ∈ J, d ≠ 0 ∧ ∃ s, s ∉ P.asIdeal ∧ ∀ y ∈ J, ∃ o : 𝓞 E, s * y = o * d := by
  first
  | exact @_root_.GlobalTheory.LocalGenerators.main
  | exact _root_.GlobalTheory.LocalGenerators.main
  | (apply _root_.GlobalTheory.LocalGenerators.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.LocalGenerators.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LocalGenerators.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LocalGenerators.main ..)

end GlobalTheory.FixConvRow

namespace GlobalTheory.FixConvRow

open IsDedekindDomain

section Gen

variable {E : Type} [Field E] [NumberField E]

theorem locS_le_of_le {V : Type} [AddCommGroup V] [Module (𝓞 E) V] (M : Submonoid (𝓞 E)) {A B : Submodule (𝓞 E) V}
    (h : A ≤ Formalism.HermitianLatticesTheory.locS M B) : Formalism.HermitianLatticesTheory.locS M A ≤ Formalism.HermitianLatticesTheory.locS M B := by
  rintro x ⟨s, hs, hx⟩
  obtain ⟨t, ht, htx⟩ := h hx
  exact ⟨t * s, M.mul_mem ht hs, by rw [mul_smul]; exact htx⟩

theorem locS_span_eq {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]
    (M : Submonoid (𝓞 E)) {r : ℕ} (e : Fin r → V) (I : Fin r → Set E) (c : Fin r → E)
    (h1 : ∀ a, ∃ s ∈ M, algebraMap (𝓞 E) E s * c a ∈ I a)
    (h2 : ∀ a, ∀ x ∈ I a, ∃ s ∈ M, ∃ o : 𝓞 E, algebraMap (𝓞 E) E s * x = algebraMap (𝓞 E) E o * c a) :
    Formalism.HermitianLatticesTheory.locS M (Submodule.span (𝓞 E) {y | ∃ (a : Fin r) (x : E), x ∈ I a ∧ y = x • e a}) =
      Formalism.HermitianLatticesTheory.locS M (Submodule.span (𝓞 E) (Set.range fun a => c a • e a)) := by
  have key : ∀ (s : 𝓞 E) (x : E) (v : V), s • (x • v) = (algebraMap (𝓞 E) E s * x) • v := by
    intro s x v
    rw [← smul_assoc, Algebra.smul_def]
  apply le_antisymm
  · apply locS_le_of_le
    rw [Submodule.span_le]
    rintro _ ⟨a, x, hx, rfl⟩
    obtain ⟨s, hs, o, ho⟩ := h2 a x hx
    refine ⟨s, hs, ?_⟩
    rw [key, ho, ← key]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  · apply locS_le_of_le
    rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    obtain ⟨s, hs, hsc⟩ := h1 a
    refine ⟨s, hs, ?_⟩
    rw [key]
    exact Submodule.subset_span ⟨a, _, hsc, rfl⟩

theorem inv_gen (P : HeightOneSpectrum (𝓞 E)) (J : Ideal (𝓞 E)) (hJ : J ≠ ⊥) :
    ∃ c : E, c ≠ 0 ∧ (∃ s ∈ P.asIdeal.primeCompl,
      algebraMap (𝓞 E) E s * c ∈ ((J : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)⁻¹)) ∧
      ∀ x ∈ ((J : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)⁻¹), ∃ s ∈ P.asIdeal.primeCompl, ∃ o : 𝓞 E,
        algebraMap (𝓞 E) E s * x = algebraMap (𝓞 E) E o * c := by
  obtain ⟨d, hdJ, hd0, s, hsP, hs⟩ := loc_gen P J hJ
  have hJ0 : (J : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.2 hJ
  have hd0' : algebraMap (𝓞 E) E d ≠ 0 := by
    rwa [Ne, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 E) E)]
  refine ⟨(algebraMap (𝓞 E) E d)⁻¹, inv_ne_zero hd0', ⟨s, hsP, ?_⟩, fun x hx => ⟨1, P.asIdeal.primeCompl.one_mem, ?_⟩⟩
  · rw [FractionalIdeal.mem_inv_iff hJ0]
    intro y hy
    obtain ⟨y', hy', rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hy
    obtain ⟨o, ho⟩ := hs y' hy'
    rw [FractionalIdeal.mem_one_iff _]
    refine ⟨o, ?_⟩
    have e : algebraMap (𝓞 E) E s * algebraMap (𝓞 E) E y' = algebraMap (𝓞 E) E o * algebraMap (𝓞 E) E d := by
      rw [← map_mul, ← map_mul, ho]
    field_simp
    exact e.symm
  · rw [FractionalIdeal.mem_inv_iff hJ0] at hx
    obtain ⟨o, ho⟩ := (FractionalIdeal.mem_one_iff _).1 (hx _ ((FractionalIdeal.mem_coeIdeal _).2 ⟨d, hdJ, rfl⟩))
    refine ⟨o, ?_⟩
    rw [ho, map_one, one_mul]
    field_simp

theorem inv_one (P : HeightOneSpectrum (𝓞 E)) (J : Ideal (𝓞 E)) (hJ : J ≠ ⊥) (t : 𝓞 E) (htJ : t ∈ J)
    (htP : t ∉ P.asIdeal) :
    (∃ s ∈ P.asIdeal.primeCompl,
      algebraMap (𝓞 E) E s * 1 ∈ ((J : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)⁻¹)) ∧
      ∀ x ∈ ((J : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)⁻¹), ∃ s ∈ P.asIdeal.primeCompl, ∃ o : 𝓞 E,
        algebraMap (𝓞 E) E s * x = algebraMap (𝓞 E) E o * 1 := by
  have hJ0 : (J : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.2 hJ
  refine ⟨⟨1, P.asIdeal.primeCompl.one_mem, ?_⟩, fun x hx => ⟨t, htP, ?_⟩⟩
  · rw [FractionalIdeal.mem_inv_iff hJ0]
    intro y hy
    obtain ⟨y', -, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hy
    rw [FractionalIdeal.mem_one_iff _]
    exact ⟨y', by simp⟩
  · rw [FractionalIdeal.mem_inv_iff hJ0] at hx
    obtain ⟨o, ho⟩ := (FractionalIdeal.mem_one_iff _).1 (hx _ ((FractionalIdeal.mem_coeIdeal _).2 ⟨t, htJ, rfl⟩))
    exact ⟨o, by rw [ho, mul_one, mul_comm]⟩

end Gen

end GlobalTheory.FixConvRow

namespace GlobalTheory.FixConvRow

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem ddS_zpow_eq (D : D7) (a : Fin D.R.rS) :
    (ddS D ^ (-((D.R.rS : ℤ) - (a : ℕ))) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) =
      ((↑((Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F))) ^
        (D.R.rS - (a : ℕ))) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E))⁻¹ := by
  rw [FractionalIdeal.coeIdeal_pow, ← Nat.cast_sub a.2.le, zpow_neg, zpow_natCast]
  rfl

theorem absNorm_different_not_mem (D : D7) (P : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E))
    (hg : ((_root_.Formalism.MainNotions.S.Lat.gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) :
    ((Ideal.absNorm (differentIdeal ℤ (𝓞 D.host.F)) : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
  intro hNP
  rw [_root_.Formalism.MainNotions.S.Lat.gS, Nat.cast_mul] at hg
  obtain ⟨i, hi⟩ : ∃ i : Fin 2, ((D.host.g i : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := by
    rcases P.isPrime.mem_or_mem hg with h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
  have hc := Nat.isCoprime_iff_coprime.2 (GlobalTheory.FrameIntegral.coprime_gi (D := D) i)
  obtain ⟨u, v, huv⟩ := hc.map (Int.castRingHom (𝓞 D.host.E))
  apply P.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← huv]
  simp only [eq_intCast, Int.cast_natCast]
  exact P.asIdeal.add_mem (P.asIdeal.mul_mem_left _ hNP) (P.asIdeal.mul_mem_left _ hi)

theorem isFixedConv_of_XLam_eq : ∀ (D : D7) (T : D.host.E) (F : FlagG (VS D) D.R.rS T) (Λ : LV D),
    XLam Λ (lf D F) = XS D F → (∀ c : D.host.E, c • F.z ∈ Lsub Λ (lf D F) → ∃ o : 𝓞 D.host.E, (o : D.host.E) = c) →
    IsFixedConv Λ (_root_.Formalism.MainNotions.S.Lat.gS D) (lf D F) := by
  intro D T F Λ hX hprim
  refine ⟨fun P => ?_, hprim⟩
  have hJd0 : Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F)) ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot (differentIdeal_ne_bot (A := ℤ) (B := 𝓞 D.host.F))
  have hJm : ∀ m : ℕ, Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F)) ^ m ≠ ⊥ :=
    fun m => pow_ne_zero m hJd0
  have goal : ∀ c : Fin D.R.rS → D.host.E,
      (∀ a : Fin D.R.rS, ∃ s ∈ P.asIdeal.primeCompl, algebraMap (𝓞 D.host.E) D.host.E s * c a ∈
        (ddS D ^ (-((D.R.rS : ℤ) - (a : ℕ))) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)) →
      (∀ a : Fin D.R.rS, ∀ x ∈ (ddS D ^ (-((D.R.rS : ℤ) - (a : ℕ))) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E),
        ∃ s ∈ P.asIdeal.primeCompl, ∃ o : 𝓞 D.host.E,
          algebraMap (𝓞 D.host.E) D.host.E s * x = algebraMap (𝓞 D.host.E) D.host.E o * c a) →
      (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (XLam Λ (lf D F)) =
        Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Submodule.span (𝓞 D.host.E) (Set.range fun a => c a • (lf D F).fl.e a))) := by
    intro c h1 h2
    rw [hX]
    exact locS_span_eq _ F.e
      (fun a => ((ddS D ^ (-((D.R.rS : ℤ) - (a : ℕ))) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) :
        Set D.host.E)) c h1 h2
  by_cases hg : ((_root_.Formalism.MainNotions.S.Lat.gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal
  · have hN : ((Ideal.absNorm (differentIdeal ℤ (𝓞 D.host.F)) : ℕ) : 𝓞 D.host.E) ∈
        Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F)) := by
      have h := Ideal.mem_map_of_mem (algebraMap (𝓞 D.host.F) (𝓞 D.host.E))
        (Ideal.absNorm_mem (differentIdeal ℤ (𝓞 D.host.F)))
      simpa using h
    have hNP := absNorm_different_not_mem D P hg
    have hone := fun a : Fin D.R.rS => inv_one P _ (hJm (D.R.rS - (a : ℕ))) _ (Ideal.pow_mem_pow hN _)
      (fun h => hNP (P.isPrime.mem_of_pow_mem _ h))
    refine ⟨fun _ => 1, fun _ => one_ne_zero, fun _ _ => rfl, goal _ ?_ ?_⟩
    · intro a; rw [ddS_zpow_eq]; exact (hone a).1
    · intro a; rw [ddS_zpow_eq]; exact (hone a).2
  · choose c hc0 hc1 hc2 using fun a : Fin D.R.rS => inv_gen P _ (hJm (D.R.rS - (a : ℕ)))
    refine ⟨c, hc0, fun h => absurd h hg, goal c ?_ ?_⟩
    · intro a; rw [ddS_zpow_eq]; exact hc1 a
    · intro a; rw [ddS_zpow_eq]; exact hc2 a

end GlobalTheory.FixConvRow
end
end

section

open scoped Classical ENNReal Pointwise
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FrameFactorG

open IsDedekindDomain ValuativeRel

variable {D : D7}

theorem exists_diff_not_mem (P : HeightOneSpectrum (𝓞 D.host.E))
    (hP : ((_root_.Formalism.MainNotions.S.Lat.gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) :
    ∃ m : 𝓞 D.host.F, m ∈ differentIdeal ℤ (𝓞 D.host.F) ∧ m ∉ (below D P).asIdeal := by
  have h := Formalism.L2.SG.Pf.LatEx.ddG_of D Formalism.L2.SG.Pf.LatEx.splitDiff_holds P hP
  rw [Ideal.map_le_iff_le_comap] at h
  obtain ⟨m, hm, hmP⟩ := Set.not_subset.1 h
  exact ⟨m, hm, hmP⟩

theorem coe_algebraMap_int (m : 𝓞 D.host.F) :
    ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) m : 𝓞 D.host.E) : D.host.E) =
      algebraMap D.host.F D.host.E (m : D.host.F) := by
  first
  | rfl
  | simp
  | exact (IsScalarTower.algebraMap_apply (𝓞 D.host.F) D.host.F D.host.E m).symm

theorem iota_mem_of_inv_pow (P : HeightOneSpectrum (𝓞 D.host.E))
    (hP : ((_root_.Formalism.MainNotions.S.Lat.gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) (k : ℕ) (y : D.host.E) (hy : y ∈ (ddS D)⁻¹ ^ k) :
    (D.s.atP (below D P)).ιE y ∈ (D.s.atP (below D P)).O := by
  obtain ⟨m, hm, hmP⟩ := exists_diff_not_mem P hP
  set c : D.host.E := ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) m : 𝓞 D.host.E) : D.host.E) with hc
  have hmE : c ∈ ddS D := by
    unfold ddS
    rw [FractionalIdeal.mem_coeIdeal]
    exact ⟨_, Ideal.mem_map_of_mem _ hm, rfl⟩
  have hpow : c ^ k ∈ ddS D ^ k := by
    rw [← FractionalIdeal.mem_coe, FractionalIdeal.coe_pow]
    exact Submodule.pow_mem_pow _ (FractionalIdeal.mem_coe.2 hmE) k
  have h1 : y * c ^ k ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
    have := FractionalIdeal.mul_mem_mul hy hpow
    rwa [← mul_pow, inv_mul_cancel₀ GlobalTheory.FrameFactorUnit.ddS_ne_zero, one_pow] at this
  obtain ⟨o, ho⟩ := (FractionalIdeal.mem_one_iff _).1 h1
  have hu := Formalism.L2.SG.Pf.LocalDenominators.iF_unit (D.s.atP (below D P)) hmP
  set t := (D.s.atP (below D P)).ιF (m : D.host.F) with ht
  have ht0 : t ≠ 0 := by
    intro h0; rw [h0, map_zero] at hu; exact zero_ne_one hu
  have htinv : t⁻¹ ∈ 𝒪[(D.s.atP (below D P)).Fp] := by
    rw [Valuation.mem_integer_iff, map_inv₀, hu, inv_one]
  have hcE : (D.s.atP (below D P)).ιE c = algebraMap _ (D.s.atP (below D P)).Ep t := by
    rw [hc, coe_algebraMap_int, (D.s.atP (below D P)).compat]
  have e : (D.s.atP (below D P)).ιE y =
      (D.s.atP (below D P)).ιE (o : D.host.E) *
        (algebraMap _ (D.s.atP (below D P)).Ep t⁻¹) ^ k := by
    have h2 := congrArg (D.s.atP (below D P)).ιE ho
    have h3 : (D.s.atP (below D P)).ιE (algebraMap (𝓞 D.host.E) D.host.E o) =
        (D.s.atP (below D P)).ιE (o : D.host.E) := rfl
    rw [h3, map_mul, map_pow, hcE] at h2
    rw [h2, mul_assoc, ← mul_pow, ← map_mul, mul_inv_cancel₀ ht0, map_one, one_pow, mul_one]
  rw [e]
  exact mul_mem (Formalism.L2.SG.Pf.LocalDenominators.iE_int _ (RingOfIntegers.isIntegral_coe o))
    (pow_mem (Formalism.L2.SG.Pf.LocalDenominators.alg_mem_O _ htinv) _)

end GlobalTheory.FrameFactorG


open GlobalTheory.FrameFactorG in
theorem GlobalTheory.FrameFactorG.frFac_unit_at_g : ∀ (D : D7) (Tn T'n : ℕ) (F0 : FlagG (VS D) D.R.rS (Tn : D.host.E)) (F : LFlag (D.sp.Y 0) D.R.rS (Tn : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (T'n : D.host.E)) (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP Tn T'n F F' → ∀ (Λ : LV D) (y : Dat Z FP), LocOver Λ y → ∀ g : GV D, Adapt g (lf D F0) F → IsRowLat D F0 (Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ) → ∀ P : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E), ((_root_.Formalism.MainNotions.S.Lat.gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal → ∀ a, frFac Z.δ (below D P) a ∈ (Z.M (below D P)).L.O ∧ Ring.inverse (frFac Z.δ (below D P) a) ∈ (Z.M (below D P)).L.O := by
  intro D Tn T'n F0 F F' Z FP _ Λ y _ g _ _ P hP a
  have hO := Formalism.L2.SG.Pf.LocFacts.lf_hO Z (below D P)
  have hD := Formalism.L2.SG.Pf.locDiffC_holds D Z (below D P) a
  have hexp : (-((D.R.rS : ℤ) - ((a : ℕ) : ℤ))) = -((D.R.rS - a.val : ℕ) : ℤ) := by
    rw [Nat.cast_sub (by omega : a.val ≤ D.R.rS)]
  have hpw : (ddS D) ^ (-((D.R.rS - a.val : ℕ) : ℤ)) = (ddS D)⁻¹ ^ (D.R.rS - a.val) := by
    rw [zpow_neg, zpow_natCast, inv_pow]
  rw [hexp, hpw] at hD
  constructor
  · have h : frFac Z.δ (below D P) a ∈ Submodule.span (Z.M (below D P)).L.O
        ((D.s.atP (below D P)).ιE '' ((((ddS D)⁻¹ ^ (D.R.rS - a.val) :
          FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)) : Set D.host.E)) := by
      rw [hD]; exact Submodule.mem_span_singleton_self _
    suffices key : ∀ x ∈ Submodule.span (Z.M (below D P)).L.O
        ((D.s.atP (below D P)).ιE '' ((((ddS D)⁻¹ ^ (D.R.rS - a.val) :
          FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)) : Set D.host.E)), x ∈ (Z.M (below D P)).L.O from
      key _ h
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨w, hw, rfl⟩ := hx
      rw [hO]; exact iota_mem_of_inv_pow P hP _ w hw
    | zero => exact zero_mem _
    | add x w _ _ hx hw => exact add_mem hx hw
    | smul o x _ hx => rw [Subring.smul_def]; exact mul_mem o.2 hx
  · have h1 : (1 : (D.s.atP (below D P)).Ep) ∈ Submodule.span (Z.M (below D P)).L.O {frFac Z.δ (below D P) a} := by
      rw [← hD]
      exact Submodule.subset_span ⟨1, GlobalTheory.FrameFactorUnit.one_mem_inv_pow _, map_one _⟩
    obtain ⟨o1, ho1⟩ := Submodule.mem_span_singleton.1 h1
    have ho1' : (o1 : (D.s.atP (below D P)).Ep) * frFac Z.δ (below D P) a = 1 := by
      simpa [Subring.smul_def, smul_eq_mul] using ho1
    have hu : IsUnit (frFac Z.δ (below D P) a) :=
      ⟨⟨frFac Z.δ (below D P) a, o1, by rw [mul_comm]; exact ho1', ho1'⟩, rfl⟩
    have hinv : Ring.inverse (frFac Z.δ (below D P) a) = o1 := by
      calc Ring.inverse (frFac Z.δ (below D P) a)
          = ((o1 : (D.s.atP (below D P)).Ep) * frFac Z.δ (below D P) a) * Ring.inverse (frFac Z.δ (below D P) a) := by
            rw [ho1', one_mul]
        _ = o1 := by rw [mul_assoc, Ring.mul_inverse_cancel _ hu, mul_one]
    rw [hinv]; exact o1.2

end
end

section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.localScalar_eq_one_at_place_over_typePrimes : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) {T T' : D.host.E} (F00 : LFlag (D.sp.Y 0) D.R.rS T) (F'0 : LFlag (D.sp.Y 0) D.R.rS T') (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS) (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G) (P : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E)), ((_root_.Formalism.MainNotions.S.Lat.gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal → G.c (below D P) = 1 := by
  first | exact @GlobalTheory.HL.GCoord.c_eq_one_of_gS_mem | exact GlobalTheory.HL.GCoord.c_eq_one_of_gS_mem | (intros; apply GlobalTheory.HL.GCoord.c_eq_one_of_gS_mem <;> assumption)
end

section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.theta_smul_completedLattice_iff_typePrimeMul : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) {T T' : D.host.E} (F00 : LFlag (D.sp.Y 0) D.R.rS T) (F'0 : LFlag (D.sp.Y 0) D.R.rS T') (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS) (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G) (P : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E)), ((_root_.Formalism.MainNotions.S.Lat.gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal → ∀ (Λ : G.Lt) (x : (G.S (below D P)).V), (G.S (below D P)).InTh ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).lat (below D P) Λ) x ↔ x ∈ (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).lat (below D P) (Ideal.span {((_root_.Formalism.MainNotions.S.Lat.gS D : ℕ) : 𝓞 D.host.E)} • Λ) := by
  first | exact @GlobalTheory.HL.ThetaG.inTh_lat_iff | exact GlobalTheory.HL.ThetaG.inTh_lat_iff | (intros; apply GlobalTheory.HL.ThetaG.inTh_lat_iff <;> assumption)
end

section

open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.card_row_automorphisms_eq_lattice_stabilizer : ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), GlobalTheory.TypeAsm.Std D large₂ → ∀ Λ ∈ Y.what₂ u, Nat.card (autLz D (X.Fu u) Λ) = Nat.card (MulAction.stabilizer (GlobalTheory.RowsOrb.Gz X u) (GlobalTheory.RowsOrb.Lmap X u Λ)) := by
  first | exact @GlobalTheory.RowsOrb.card_autLz | exact GlobalTheory.RowsOrb.card_autLz | (intros; apply GlobalTheory.RowsOrb.card_autLz <;> assumption)
end

section

open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.definiteQuotientLattice_eq_image_anisotropicPart : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (W : Submodule D.host.E (VS D).V) (e : GlobalTheory.RowsOrb.Ub X u ≃ₗ[D.host.E] W), (∀ x : GlobalTheory.RowsOrb.Ub X u, ((e x : W) : (VS D).V) - ((x : GlobalTheory.RowsOrb.Wb X) : (VS D).V) ∈ (GlobalTheory.TypeAsm.F0 X u).X) → ∀ Λ : Submodule (𝓞 D.host.E) (VS D).V, GlobalTheory.DegAsm.lat0 (GlobalTheory.TypeAsm.F0 X u) W.subtype Λ = GlobalTheory.Mass.Transp.img e (GlobalTheory.Mass.latIn (GlobalTheory.RowsOrb.Ub X u) (GlobalTheory.RowsOrb.Lmap X u Λ)) := by
  first | exact @GlobalTheory.RowsOrb.lat0_eq_img_latIn_Ub | exact GlobalTheory.RowsOrb.lat0_eq_img_latIn_Ub | (intros; apply GlobalTheory.RowsOrb.lat0_eq_img_latIn_Ub <;> assumption)
end

section

open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.orbit_lattice_unimodular_and_primitive : ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), GlobalTheory.TypeAsm.Std D large₂ → ∀ Λ ∈ Y.what₂ u, Submodule.IsLattice D.host.E (GlobalTheory.RowsOrb.Lmap X u Λ) ∧ Formalism.HermitianLatticesTheory.IsUnimodular (GlobalTheory.RowsOrb.hb X) (GlobalTheory.RowsOrb.Lmap X u Λ) ∧ ∀ t : D.host.E, t • GlobalTheory.RowsOrb.zb X u ∈ GlobalTheory.RowsOrb.Lmap X u Λ ↔ t ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := by
  first | exact @GlobalTheory.RowsOrb.Basic.lmap_basic | exact GlobalTheory.RowsOrb.Basic.lmap_basic | (intros; apply GlobalTheory.RowsOrb.Basic.lmap_basic <;> assumption)
end

section

open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.rows_eq_of_stabilizer_conjugate_lattices : ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), GlobalTheory.TypeAsm.Std D large₂ → ∀ Λ₁ ∈ Y.what₂ u, ∀ Λ₂ ∈ Y.what₂ u, ∀ g : GlobalTheory.RowsOrb.Gz X u, g • GlobalTheory.RowsOrb.Lmap X u Λ₁ = GlobalTheory.RowsOrb.Lmap X u Λ₂ → Λ₁ = Λ₂ := by
  first | exact @GlobalTheory.RowsOrb.rows_eq_of_conj | exact GlobalTheory.RowsOrb.rows_eq_of_conj | (intros; apply GlobalTheory.RowsOrb.rows_eq_of_conj <;> assumption)
end

section

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.mean_primitiveSublattices_genus_definiteLattice : GlobalTheory.Mass.MaxMass → Formalism.HermitianLatticesTheory.SiegelMassRatio → ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → HasOrtho K → 1 ≤ Formalism.HermitianLatticesTheory.vInv K → GlobalTheory.Mass.PD H.B.flip → 3 ≤ (Module.finrank K V) → ∀ (T : ℕ) (L₀ : Submodule (𝓞 K) V) (Mb : ℝ), T.Prime → (∀ P : Ideal (𝓞 K), P.IsMaximal → (T : 𝓞 K) ∈ P → Ideal.absNorm P = T ∧ (T : 𝓞 K) ∉ P ^ 2) → GlobalTheory.Mass.IsIntLat H.B.flip L₀ → Nonempty ((↥(Formalism.HermitianLatticesTheory.dual H.B.flip L₀) ⧸ L₀.comap (Formalism.HermitianLatticesTheory.dual H.B.flip L₀).subtype) ≃ₗ[𝓞 K] (𝓞 K ⧸ Ideal.span {(T : 𝓞 K)})) → Mb = (20 * ((Formalism.HermitianLatticesTheory.fDeg K) : ℝ) * (2 * Formalism.HermitianLatticesTheory.vInv K) ^ 2) ^ (2 * ((Formalism.HermitianLatticesTheory.fDeg K) : ℝ) * (6 + cf K)) → ∀ D₀ : ℝ, D₀ = (T : ℝ) ^ (2 * (Formalism.HermitianLatticesTheory.fDeg K)) → ∀ s n : ℕ, 1 ≤ s → s < (Module.finrank K V) → 1 ≤ n → GlobalTheory.Mass.orbSum (Formalism.HermitianLatticesTheory.isom H.B.flip) (Formalism.HermitianLatticesTheory.genus H.B.flip L₀) (fun L => (((GlobalTheory.Mass.primSp H.B.flip L ((Module.finrank K V) - s) n).encard : ℕ∞) : ℝ≥0∞)) ≤ ENNReal.ofReal (Formalism.HermitianLatticesTheory.mass H.B.flip L₀ * (Mb * (2 * Formalism.HermitianLatticesTheory.vInv K) ^ (Formalism.HermitianLatticesTheory.fDeg K) * 16 ^ (s * (Module.finrank K V) * (Formalism.HermitianLatticesTheory.fDeg K))) * ((n : ℝ) / D₀) ^ (((Module.finrank K V) : ℝ) / 2) * ((n : ℝ) * D₀) ^ (5 * (s : ℝ) + 5 + 2 * cf K)) := by
  first | exact @GlobalTheory.DegCnt.PrimGenus.main | exact GlobalTheory.DegCnt.PrimGenus.main | (intros; apply GlobalTheory.DegCnt.PrimGenus.main <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.Deep
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.DeepKernel

theorem deep_kernel_bound_of_ptBound : PtBound →
    (∀ (B : RowsAut) (Cg : ℝ) (n₀ : ℕ) (d : InfinitePlace B.I.F → ℝ) (p q : ℕ) (b : ℝ), 8 ≤ n₀ →
      CountHyp B Cg n₀ d p q b → FiniteDimensional ℂ (B.I.eHom B.σs B.μf B.fund B.R B.Re)) →
    GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.DeepKernelBound := by
  intro hP hF Cg n₀ B d p q b c x _ hn hq hC hc hx
  obtain ⟨-, -, -, -, -, hqn, hrk, hmin, -, -, -, -, h, -, hgap, h40, h32, -, h120, -⟩ :=
    GlobalTheory.Dec.countHyp_numerics B Cg n₀ d p q b hn hC
  have hD : IsDSData B d := hC.1
  have hg : 1 ≤ B.g := hC.2.2.2.2.2.2.2.2.2.1
  have hS := GlobalTheory.T.isKTypeOf_lowK_of_countHyp B Cg n₀ d p q b hn hC
  have hfin := hF B Cg n₀ d p q b hn hC
  have hloc : LocDec B h := (hP B d p q h hD hC.2.1 hgap (by rw [hmin]; exact h120)).2.2.2.2.2.2
  obtain ⟨Rφ, hR, T, -, hT2, hT3, -, -, hT6, hT7, hT8, hT9⟩ :=
    GlobalTheory.T.exists_orthonormal_cuspidal_isometric_intertwiners B d h hD hS hg (fun v => by rw [hrk v]; exact h120) hloc h40 hfin
  choose Fr hFr using fun i => GlobalTheory.T.exists_continuousRowRepresentatives_lowestKType B d hD hS hg (T i) (hT2 i) (hT7 i)
  obtain ⟨y, Fc, hy, hsp, hFc, hk, -⟩ := GlobalTheory.KernelExpansion.kernelB B d h hD (by omega) hloc h32 hfin Rφ hR
  have hw := (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.tens_w_mem B hD 0).1
  have e := GlobalTheory.Dec.kerDiag_basis_indep B B.D y (fun i => T i (B.tens B.w)) Fc (fun i => Fr i (B.tens B.w))
    hy hT8 (hsp.trans hT9.symm) (fun i => ⟨hFc i, (hFr i 0 _ hw).1⟩) x
  have e2 : (kern B.I (phe B d) x x).re = ‖vv B Fr (B.tens B.w) x‖ ^ 2 := by
    rw [hk, EuclideanSpace.norm_sq_eq, Complex.re_sum]
    simp only [vv]
    rw [← e]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.star_def, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  rw [e2]
  exact GlobalTheory.T.deepPoint_bound_cuspidalIsometricIntertwinerFamily B Cg n₀ d p q b c x B.D T Fr hn hq hC hc hx hFr hT3 hT6

end GlobalTheory.DeepKernel
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

theorem _root_.GlobalTheory.T.isotropicFlag_unfolding_bound : UnfoldBound := by
  first | exact @GlobalTheory.FlagUnfold.unfoldBound | exact GlobalTheory.FlagUnfold.unfoldBound | (intros; apply GlobalTheory.FlagUnfold.unfoldBound <;> assumption)
end
