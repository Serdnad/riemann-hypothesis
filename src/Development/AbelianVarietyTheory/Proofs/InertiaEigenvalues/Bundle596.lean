module

public import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle183
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FinPartDetAtInvInt
public import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.NHkRow
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle570
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle010
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle013
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Formalism.SharpRestriction.LevelLetterCocycles.ElementDenominator
public import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle007
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle571
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle503
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle572
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HausdorffOfModuleTopologyFiniteDimensional
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeNhds
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.T2SpaceLocalLatticeRepresentationSpace
public import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle568
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
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle023
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.SharpRestriction.LevelLetterCocycles.IntegralHeckeForms
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InvertibleSpanSingleton
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAdicCompleteOfPowLe
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemBallOfGaugeLt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle024
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity
public import Mathlib.FieldTheory.Galois.Infinite

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

namespace GlobalTheory.ConjLocVal

theorem value_at_conj_place : ∀ (D : D7) (PP : Pl D.host.E) (e : AE D) (ϖ : 𝓞 D.host.E) (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E) (n : ℕ) (y : (AE D)ˣ), Formalism.L2.NTheta.IsIdemAt e PP → ϖ ∈ PP.asIdeal → ϖ ∉ PP.asIdeal ^ 2 → ChrEq c χ → χ.UnrAt (Formalism.L2.DIV.conjPl PP) → (y : AE D) = 1 + cA D e * (incA D (star (ϖ : D.host.E)) ^ n - 1) → ((c y : Circle) : ℂ) = ((χ.val (Formalism.L2.DIV.conjPl PP) : ℂˣ) : ℂ) ^ n := by
  intro D PP e ϖ c χ n y he h1 h2 hc hU hy
  obtain ⟨⟨e1, e2, v, ε, hε, e3⟩, e4⟩ := Formalism.IndefR.Fin.LevelGroupLemmas.isIdemAt_conj he
  have hpl : Formalism.L2.JoinChr.IsPlIdem D (cA D e) (Formalism.L2.DIV.conjPl PP) := ⟨e1, ⟨v, ε, hε, Or.inl ⟨e2, e3⟩⟩, e4⟩
  have hϖ0 : ϖ ≠ 0 := by
    rintro rfl
    exact h2 (zero_mem _)
  have hϖE : (ϖ : D.host.E) ≠ 0 := by exact_mod_cast hϖ0
  have hs0 : star (ϖ : D.host.E) ≠ 0 := star_ne_zero.2 hϖE
  set k : D.host.Eˣ := Units.mk0 (star (ϖ : D.host.E)) hs0 with hk
  have hy' : (y : AE D) = Formalism.L2.JoinChr.locE D (cA D e) ((k ^ n : D.host.Eˣ) : D.host.E) := by
    rw [hy, Formalism.L2.JoinChr.locE, Units.val_pow_eq_pow_val, map_pow]
    rfl
  rw [hc.2 _ _ hpl (k ^ n) y hy', map_pow, Units.val_pow_eq_pow_val]
  congr 1
  have hmem : Formalism.L2.DIV.starO ϖ ∈ (Formalism.L2.DIV.conjPl PP).asIdeal := by
    show Formalism.L2.DIV.starO (Formalism.L2.DIV.starO ϖ) ∈ PP.asIdeal
    rw [Formalism.L2.DIV.starO_starO]; exact h1
  have hnsq : Formalism.L2.DIV.starO ϖ ∉ (Formalism.L2.DIV.conjPl PP).asIdeal ^ 2 := by
    intro hm
    have hm' := Ideal.le_comap_pow (f := Formalism.L2.DIV.starOHom) (K := PP.asIdeal) 2 hm
    rw [Ideal.mem_comap] at hm'
    apply h2
    have : Formalism.L2.DIV.starOHom (Formalism.L2.DIV.starO ϖ) = ϖ := Formalism.L2.DIV.starO_starO ϖ
    rwa [this] at hm'
  have hunif : Formalism.L2.Host.IsUnifAt (Formalism.L2.DIV.conjPl PP) (Formalism.L2.Host.atFin (Formalism.L2.DIV.conjPl PP) k) := by
    show Valued.v (((star (ϖ : D.host.E) : D.host.E)) : (Formalism.L2.DIV.conjPl PP).adicCompletion D.host.E) = _
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', ← Formalism.L2.DIV.starO_coe,
      HeightOneSpectrum.valuation_of_algebraMap]
    exact GlobalTheory.LatIntFacts.intValuation_uniformiser _ hmem hnsq
  have hval : χ.loc (Formalism.L2.DIV.conjPl PP) (Formalism.L2.Host.atFin (Formalism.L2.DIV.conjPl PP) k) = χ.val (Formalism.L2.DIV.conjPl PP) := by
    have hu : Formalism.L2.Host.IsUnitAt (Formalism.L2.DIV.conjPl PP)
        (Formalism.L2.Host.atFin (Formalism.L2.DIV.conjPl PP) k * (Formalism.L2.Host.atFin (Formalism.L2.DIV.conjPl PP) (Formalism.L2.Host.unif (Formalism.L2.DIV.conjPl PP)))⁻¹) := by
      have h2' := Formalism.L2.Host.unif_spec (Formalism.L2.DIV.conjPl PP)
      unfold Formalism.L2.Host.IsUnitAt
      unfold Formalism.L2.Host.IsUnifAt at hunif h2'
      rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, hunif, h2']
      exact mul_inv_cancel₀ (by simp)
    have h3 := hU _ hu
    rw [map_mul, map_inv, mul_inv_eq_one] at h3
    exact h3
  show ((χ.loc (Formalism.L2.DIV.conjPl PP) (Formalism.L2.Host.atFin (Formalism.L2.DIV.conjPl PP) k) : ℂˣ) : ℂ) = _
  rw [hval]

end GlobalTheory.ConjLocVal
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.IntegralHeckeForms NumberField Polynomial Formalism.IndefR.NX
open scoped TensorProduct

theorem _root_.GlobalTheory.T.good_projector_forms_idempotent : ∀ (D : D7) (S : RatDat D.ntw) (j : ℕ), D.ntw.Tw →
    goodProjW S j D.nexp.eLL0 * goodProjW S j D.nexp.eLL0 = goodProjW S j D.nexp.eLL0 := by
  first | exact @GlobalTheory.GoodSS.Idem.goodProjW_idem | exact GlobalTheory.GoodSS.Idem.goodProjW_idem | (intros; apply GlobalTheory.GoodSS.Idem.goodProjW_idem <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

theorem _root_.GlobalTheory.T.theoremB_of_localFilteredHypotheses : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), ∀ (C CR CA CB CK Ckap : ℝ), (320 : ℝ) ≤ C → CrystallineLiftingBounds.adm22 D HW F → CrystallineLiftingBounds.adm23 D HW F → Formalism.MainNotions.N.LetterConditionGlobal D HW F → ArcLiftingSetup.Stmt D HW F Cm C CR CA CB CK Ckap := by
  first | exact @GlobalTheory.theoremB_of_admitted_inputs | exact GlobalTheory.theoremB_of_admitted_inputs | (intros; apply GlobalTheory.theoremB_of_admitted_inputs <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory

theorem rootOfUnity_mem_range_Om : ∀ (l : ℕ) [Fact l.Prime] (x : ℂ_[l]) (m : ℕ), 0 < m → x ^ m = 1 → ∃ z : Om l, (z : ℂ_[l]) = x := by
  intro l _ x m hm hx
  haveI : NeZero m := ⟨hm.ne'⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (Om l) m
  have hζ' : IsPrimitiveRoot (algebraMap (Om l) ℂ_[l] ζ) m :=
    hζ.map_of_injective (algebraMap (Om l) ℂ_[l]).injective
  obtain ⟨i, -, hi⟩ := hζ'.eq_pow_of_pow_eq_one hx
  exact ⟨ζ ^ i, by rw [← hi]; exact map_pow (algebraMap (Om l) ℂ_[l]) ζ i⟩

end GlobalTheory
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory

theorem isClosed_setOf_gal_apply_eq_padic (l : ℕ) [Fact l.Prime] (a b : Om l) :
    IsClosed {g : GQ l | g a = b} := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro g hg
  refine ⟨(fun h => g⁻¹ * h) ⁻¹' (MulAction.stabilizer (GQ l) a : Set (GQ l)), ?_,
    (stabilizer_isOpen_of_isIntegral a).preimage (continuous_const.mul continuous_id), ?_⟩
  · intro h hh
    have hs : (g⁻¹ * h) a = a := hh
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq] at hg ⊢
    intro hb
    apply hg
    rw [AlgEquiv.mul_apply] at hs
    have hga := congrArg g hs
    rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply] at hga
    rw [← hga, hb]
  · show (g⁻¹ * g) a = a
    rw [inv_mul_cancel, AlgEquiv.one_apply]

theorem galois_transitive_on_root_systems_of_prime : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (π : ↥(OL K)), Prime π → ∀ y z : ℕ → Om l, y 0 = ((π : ↥K.1) : Om l) → z 0 = ((π : ↥K.1) : Om l) → (∀ n, y (n + 1) ^ l = y n) → (∀ n, z (n + 1) ^ l = z n) → ∃ g : ↥(GK K), ∀ n, (g : GQ l) (y n) = z n := by
  intro l _ K π hπ y z hy hz hy' hz'
  have hGK : IsClosed ((GK K : Subgroup (GQ l)) : Set (GQ l)) := by
    unfold GK
    exact InfiniteGalois.fixingSubgroup_isClosed _

  have hpow : ∀ w : ℕ → Om l, (∀ n, w (n + 1) ^ l = w n) → ∀ m k, w (m + k) ^ (l ^ k) = w m := by
    intro w hw m k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, pow_mul', ← add_assoc, hw, ih]

  let T : ℕ → Set (GQ l) := fun n =>
    (GK K : Set (GQ l)) ∩ ⋂ m, ⋂ (_ : m ≤ n), {g : GQ l | g (y m) = z m}
  have hcl : ∀ n, IsClosed (T n) := fun n =>
    hGK.inter (isClosed_iInter fun m => isClosed_iInter fun _ =>
      isClosed_setOf_gal_apply_eq_padic l (y m) (z m))
  have hdec : ∀ n, T (n + 1) ⊆ T n := by
    rintro n g ⟨h1, h2⟩
    refine ⟨h1, Set.mem_iInter.2 fun m => Set.mem_iInter.2 fun hm => ?_⟩
    exact Set.mem_iInter.1 (Set.mem_iInter.1 h2 m) (Nat.le_succ_of_le hm)
  have hne : ∀ n, (T n).Nonempty := by
    intro n
    have hyn : y n ^ (l ^ n) = ((π : ↥K.1) : Om l) := by
      have h := hpow y hy' 0 n
      rw [zero_add] at h
      rw [h, hy]
    have hzn : z n ^ (l ^ n) = ((π : ↥K.1) : Om l) := by
      have h := hpow z hz' 0 n
      rw [zero_add] at h
      rw [h, hz]
    obtain ⟨g, hg⟩ := GlobalTheory.T.exists_galois_apply_eq_of_pow_eq_prime l K π hπ (l ^ n) (y n) (z n) hyn hzn
      (pow_pos (Fact.out : l.Prime).pos n)
    refine ⟨(g : GQ l), g.2, Set.mem_iInter.2 fun m => Set.mem_iInter.2 fun hm => ?_⟩
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
    show (g : GQ l) (y m) = z m
    rw [← hpow y hy' m k, ← hpow z hz' m k, map_pow, hg]

  obtain ⟨g, hg⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed T hdec hne
    (hcl 0).isCompact hcl
  refine ⟨⟨g, (Set.mem_iInter.1 hg 0).1⟩, fun n => ?_⟩
  exact Set.mem_iInter.1 (Set.mem_iInter.1 (Set.mem_iInter.1 hg n).2 n) le_rfl

end GlobalTheory
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N

theorem _root_.GlobalTheory.T.crystalline_restrict_finite_extension_jumps : ∀ D : D7, Formalism.MainNotions.ElementDenominator.adm12 D := by
  first | exact @GlobalTheory.Per.ResFinite.adm12_elementDenominator | exact GlobalTheory.Per.ResFinite.adm12_elementDenominator | (intros; apply GlobalTheory.Per.ResFinite.adm12_elementDenominator <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes

namespace GlobalTheory.TypeConjSplit

theorem ambTypeD_of_splitRow : ∀ (D : D7) (i : D.nd.Loc) (ep : Bool),
    GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes.SplitRowPrime D.host (D.nd.l i) → EmbeddingTypes.ambTypeD (D := D) i ep := by
  intro D i ep hi u hu hU w hw hc τ₀ hτ
  obtain ⟨-, h2, h3, -⟩ := (GlobalTheory.SplitRowAll.splitRow_at D).2 i hi
  have hUin : ∀ τ, EmbIn (N := D.nd) D.nbr i ep u hu τ :=
    fun τ => (GlobalTheory.T.embTypeUe_iff_localEmbeddingInCMHalfType D i u hu ep τ).1 (hU τ)
  have hwin : EmbIn (N := D.nd) D.nbr i ep w hw τ₀ := (GlobalTheory.T.embTypeUe_iff_localEmbeddingInCMHalfType D i w hw ep τ₀).1 hτ
  rcases h3 u w hu hw hc with ⟨hpu, hpw⟩ | ⟨hpu, hpw⟩ <;> cases ep
  · obtain ⟨τ⟩ := hpu.1
    exact h2 u hu τ ⟨hpu.2 τ, hUin τ⟩
  · exact h2 w hw τ₀ ⟨hwin, hpw.2 τ₀⟩
  · exact h2 w hw τ₀ ⟨hpw.2 τ₀, hwin⟩
  · obtain ⟨τ⟩ := hpu.1
    exact h2 u hu τ ⟨hUin τ, hpu.2 τ⟩

end GlobalTheory.TypeConjSplit
end

section

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

theorem _root_.GlobalTheory.T.crysOnCond_of_every_datum : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), CrysOnCond D HW F := by
  first | exact @GlobalTheory.crysOnCond_all | exact GlobalTheory.crysOnCond_all | (intros; apply GlobalTheory.crysOnCond_all <;> assumption)
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation TensorProduct

namespace GlobalTheory.HerrFull

theorem fontaine_decompletion (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) :
    adm9 D HW F := fun l _ K s LL h =>
  ⟨GlobalTheory.Cyc.FontW.main D HW F l K s LL h, GlobalTheory.Decompl.decompletion D HW F l K s LL h⟩

theorem herr_a_and_natural :
    ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), ∀ (l : ℕ) [Fact l.Prime]
      (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
      HerrAat (sit D.loc HW l (D.locA l) K s LL h) ∧
        HerrAsat (sit D.loc HW l (D.locA l) K s LL h) ∧ ((HW l).W K s LL h).ClNat := by
  intro D HW F l _ K s LL h
  have h9 := fontaine_decompletion D HW F
  have h1 := GlobalTheory.HerrClass.herr_a D HW F h9 l K s LL h
  exact ⟨h1.1, h1.2, GlobalTheory.HerrNatural.clNat D HW F h9 l K s LL h⟩

end GlobalTheory.HerrFull
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation TensorProduct

namespace GlobalTheory.Decompl

theorem fontaine_and_decompletion :
    ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), adm9 D HW F :=
  fun D HW F l _ K s LL h =>
    ⟨GlobalTheory.Cyc.FontW.main D HW F l K s LL h, GlobalTheory.Decompl.decompletion D HW F l K s LL h⟩

end GlobalTheory.Decompl
end

section


theorem _root_.GlobalTheory.T.natInvIso_of_localTateDuality_cyclotomicTwist : Formalism.GaloisCohomology.LocalTateDualityK → ReciprocityTheory.ChartRestriction.T2.NatInvIso := by
  first | exact @GlobalTheory.natInvIso_of_localTateDuality | exact GlobalTheory.natInvIso_of_localTateDuality | (intros; apply GlobalTheory.natInvIso_of_localTateDuality <;> assumption)
end
