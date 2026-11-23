module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle763
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricLevelLiftsExist
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle155
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle237
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CohDimTwoLocalOfLocalFiniteness
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle014
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle366
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle755
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle386
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle368
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle452
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle420
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle505
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle013
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle015
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle765
public import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypeJumps
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle766
public import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle767
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle015

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl idem SplitProj IsIdemOf IsProjAt adjCo grpCo frCo)
open GlobalTheory.DownLift.GenSplit

noncomputable section

namespace GlobalTheory.DownLift.GenSplit

section Reindex
variable {n K L : Type} [Fintype n] [CommRing K] [CommRing L]

theorem map_symm_mulVec_comp (ρ : K ≃+* L) (M : Matrix n n L) (x : n → L) :
    (M.map ρ.symm) *ᵥ (fun j => ρ.symm (x j)) = fun j => ρ.symm ((M *ᵥ x) j) := by
  funext j
  exact (RingHom.map_mulVec ρ.symm.toRingHom M x j).symm

theorem fix_hyperplane_map_iff (ρ : K ≃+* L) (M : Matrix n n L) (a : n → K) :
    (∀ x, (fun j => ρ (a j)) ⬝ᵥ x = 0 → M *ᵥ x = x) ↔ ∀ w, a ⬝ᵥ w = 0 → (M.map ρ.symm) *ᵥ w = w := by
  constructor
  · intro h w hw
    have hd : (fun j => ρ (a j)) ⬝ᵥ (fun j => ρ (w j)) = 0 := by
      have := (RingHom.map_dotProduct ρ.toRingHom a w).symm
      simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hw, map_zero] at this
      exact this
    have h1 := h _ hd
    have h2 := map_symm_mulVec_comp ρ M (fun j => ρ (w j))
    rw [h1] at h2
    simpa only [RingEquiv.symm_apply_apply] using h2
  · intro h x hx
    have hd : a ⬝ᵥ (fun j => ρ.symm (x j)) = 0 := by
      have := (RingHom.map_dotProduct ρ.symm.toRingHom (fun j => ρ (a j)) x).symm
      simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hx, map_zero] at this
      simpa only [Function.comp_def, RingEquiv.symm_apply_apply] using this
    have h1 := h _ hd
    rw [map_symm_mulVec_comp] at h1
    funext j
    have := congrArg ρ (congrFun h1 j)
    simpa only [RingEquiv.apply_symm_apply] using this

end Reindex

theorem mirC_hyperplane_reindex : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), ∀ (i : Fin D.R.m) (PP : Pl D.host.E) (hPP : PP ∈ R.Pg) (v : FinPl D) (ρk : IsLocalRing.ResidueField (OI v) ≃+* kP PP) (a : Fin D.R.r → IsLocalRing.ResidueField (OI v)) (F : GL (Fin D.R.r) (IsLocalRing.ResidueField (OI v)) → ℂ), (∑ᶠ g ∈ {g : G | mirC R i ⟨PP, hPP⟩ (fun j => ρk (a j)) false 1 g ≠ 0}, F (Matrix.GeneralLinearGroup.map ρk.symm.toRingHom (R.eG g ⟨PP, hPP⟩))) = ∑ᶠ g ∈ {g : GL (Fin D.R.r) (IsLocalRing.ResidueField (OI v)) | ∀ w, a ⬝ᵥ w = 0 → (g : Matrix (Fin D.R.r) (Fin D.R.r) (IsLocalRing.ResidueField (OI v))).mulVec w = w}, F g := by
  classical
  intro D G _ _ Pl0 T A Ks _ _ _ R i PP hPP v ρk a F
  set P : R.Pg := ⟨PP, hPP⟩ with hP
  have key : ∀ g : G, ((∀ x, (fun j => ρk (a j)) ⬝ᵥ x = 0 →
      ((R.eG g P : GL (Fin D.R.r) (kP PP)) : Matrix (Fin D.R.r) (Fin D.R.r) (kP PP)) *ᵥ x = x) ↔
      ∀ w, a ⬝ᵥ w = 0 → ((Matrix.GeneralLinearGroup.map ρk.symm.toRingHom (R.eG g P) : GL (Fin D.R.r) _) :
        Matrix (Fin D.R.r) (Fin D.R.r) _) *ᵥ w = w) :=
    fun g => fix_hyperplane_map_iff ρk _ a
  have hset : {g : G | mirC R i P (fun j => ρk (a j)) false 1 g ≠ 0} =
      {g : G | (∀ PP', PP' ≠ P → R.eG g PP' = 1) ∧ ∀ w, a ⬝ᵥ w = 0 →
        ((Matrix.GeneralLinearGroup.map ρk.symm.toRingHom (R.eG g P) : GL (Fin D.R.r) _) :
          Matrix (Fin D.R.r) (Fin D.R.r) _) *ᵥ w = w} := by
    ext g
    rw [Set.mem_setOf_eq, Set.mem_setOf_eq, ← key g]
    simp only [mirC, Bool.false_eq_true, ↓reduceIte, zpow_one]
    split_ifs with hc
    · simp only [ne_eq, Units.ne_zero, not_false_eq_true, true_iff]
      exact hc
    · simp only [ne_eq, not_true_eq_false, false_iff]
      exact hc
  rw [hset]
  apply finsum_mem_eq_of_bijOn (fun g => Matrix.GeneralLinearGroup.map ρk.symm.toRingHom (R.eG g P))
  · refine ⟨?_, ?_, ?_⟩
    · rintro g ⟨_, hg⟩
      exact hg
    · rintro g₁ ⟨h1, _⟩ g₂ ⟨h2, _⟩ he
      apply R.eG.injective
      funext PP'
      by_cases hq : PP' = P
      · rw [hq]
        have he' : ((R.eG g₁ P : GL (Fin D.R.r) (kP PP)) : Matrix (Fin D.R.r) (Fin D.R.r) (kP PP)).map ρk.symm =
            ((R.eG g₂ P : GL (Fin D.R.r) (kP PP)) : Matrix (Fin D.R.r) (Fin D.R.r) (kP PP)).map ρk.symm :=
          congrArg Units.val he
        exact Units.ext (Matrix.map_injective ρk.symm.injective he')
      · rw [h1 PP' hq, h2 PP' hq]
    · intro g₀ hg₀
      have hcomp : Matrix.GeneralLinearGroup.map ρk.symm.toRingHom (Matrix.GeneralLinearGroup.map ρk.toRingHom g₀) = g₀ := by
        ext j k
        simp
      refine ⟨R.eG.symm (Pi.mulSingle P (Matrix.GeneralLinearGroup.map ρk.toRingHom g₀)), ⟨?_, ?_⟩, ?_⟩
      · intro PP' hq
        rw [MulEquiv.apply_symm_apply, Pi.mulSingle_eq_of_ne hq]
      · rw [MulEquiv.apply_symm_apply, Pi.mulSingle_eq_same, hcomp]
        exact hg₀
      · show Matrix.GeneralLinearGroup.map ρk.symm.toRingHom (R.eG (R.eG.symm _) P) = g₀
        rw [MulEquiv.apply_symm_apply, Pi.mulSingle_eq_same, hcomp]
  · intro g _
    rfl

end GlobalTheory.DownLift.GenSplit

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl idem SplitProj IsIdemOf IsProjAt adjCo grpCo frCo)
open GlobalTheory.DownLift.GenSplit

noncomputable section

namespace GlobalTheory.DownLift.SplitIntLift

theorem exists_lift {R K O : Type} [CommRing R] [CommRing K] [CommRing O] {n : ℕ} (S : Subring R) (π : R →+* K)
    (ι : O →+* K) (p : S) (hinj : ∀ x, π x = 0 → (p : R) * x = 0) (hl : ∀ o, ∃ s : S, π s = ι o)
    (h : GL (Fin n) O) (β g : GL (Fin n) R)
    (hg : (Matrix.GeneralLinearGroup.map π β)⁻¹ * Matrix.GeneralLinearGroup.map π g * Matrix.GeneralLinearGroup.map π β =
      Matrix.GeneralLinearGroup.map ι h) :
    ∃ (Y : Matrix (Fin n) (Fin n) S) (u : S), (∀ i j, π (Y i j) = ι (h.1 i j)) ∧ u * Y.det = p ∧
      (p : R) • g.1 = (p : R) • (β.1 * Y.map S.subtype * (β⁻¹).1) := by
  choose Y hY using fun i j => hl (h.1 i j)
  obtain ⟨u, hu⟩ := hl (h⁻¹).1.det
  have eY : (Matrix.of Y).map (π.comp S.subtype) = h.1.map ι := Matrix.ext hY
  refine ⟨Matrix.of Y, p * u, hY, Subtype.ext ?_, ?_⟩
  · have e1 : π ((Matrix.of Y).det : S) = ι h.1.det := by
      rw [RingHom.map_det ι, RingHom.mapMatrix_apply, ← eY, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
      rfl
    have := hinj (u * ((Matrix.of Y).det : S) - 1) (by
      rw [map_sub, map_mul, hu, e1, ← map_mul, ← Matrix.det_mul, Units.inv_mul, Matrix.det_one, map_one, map_one, sub_self])
    push_cast
    linear_combination this
  · have e2 : Matrix.GeneralLinearGroup.map π g = Matrix.GeneralLinearGroup.map π β * Matrix.GeneralLinearGroup.map ι h *
        Matrix.GeneralLinearGroup.map π β⁻¹ := by
      rw [← hg, map_inv]; group
    have e3 : g.1.map π = (β.1 * (Matrix.of Y).map S.subtype * (β⁻¹).1).map π := by
      rw [Matrix.map_mul, Matrix.map_mul, Matrix.map_map]
      exact (congrArg Units.val e2).trans (congrArg (fun z => β.1.map π * z * (β⁻¹).1.map π) eY.symm)
    ext i j
    have := hinj (g.1 i j - (β.1 * (Matrix.of Y).map S.subtype * (β⁻¹).1) i j) (by
      rw [map_sub, sub_eq_zero]; exact congrFun (congrFun e3 i) j)
    rw [mul_sub, sub_eq_zero] at this
    exact this

open GlobalTheory.LevSplit GlobalTheory.ParahoricLift Formalism.L2.NTheta GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting

variable {D : D7}

theorem rdE_finSw {v : FinPl D} (φ : SplitProj D v) (a : Formalism.L2.Theta.AE D) : rdE φ (finSw D a) = rdA φ a :=
  GlobalTheory.SplitProjChart.rdE_toEAf φ a

theorem finSw_surjective (z : Formalism.IndefR.Lev.EAf D) : ∃ w, finSw D w = z := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, RingHom.map_zero _⟩
  | tmul x a => exact ⟨(show AF D.host.F from (0, a)) ⊗ₜ x, rfl⟩
  | add a b ha hb =>
    obtain ⟨s, rfl⟩ := ha
    obtain ⟨t, rfl⟩ := hb
    exact ⟨s + t, RingHom.map_add _ _ _⟩

theorem cut_inj {v : FinPl D} {φ : SplitProj D v} {e : Formalism.L2.Theta.AE D} (he : IsIdemOf φ e)
    (x : Formalism.IndefR.Lev.EAf D) (hx : rdE φ x = 0) : finSw D e * x = 0 := by
  obtain ⟨w, rfl⟩ := finSw_surjective x
  rw [rdE_finSw] at hx
  rw [← RingHom.map_mul, ((GlobalTheory.SplitProjChart.chart_rdA D v φ e he).1.2.1 w).1 hx, RingHom.map_zero]

theorem int_lift {v : FinPl D} {φ : SplitProj D v} {e : Formalism.L2.Theta.AE D} (he : IsIdemOf φ e) (o : OI v) :
    ∃ s : Formalism.L2.Herm.intAf D.host.F D.host.E, rdE φ s = algebraMap (OI v) (Fv D.host.F v) o := by
  obtain ⟨h1, -, -, h4⟩ := (GlobalTheory.SplitProjChart.chart_rdA D v φ e he).1
  obtain ⟨a, ha⟩ := h1 (algebraMap (OI v) (Fv D.host.F v) o)
  refine ⟨⟨finSw D (e * a), swapAE_int ((h4 a).2 ⟨o, ha.symm⟩)⟩, ?_⟩
  show rdE φ (finSw D (e * a)) = _
  rw [rdE_finSw, RingHom.map_mul, he.2.2, one_mul, ha]



theorem lift_of_integral : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ), IsBaseFrame V β Λ N → ∀ (PP : Pl D.host.E) (v : FinPl D) (φ : SplitProj D v) (e : Formalism.L2.Theta.AE D), IsProjAt φ PP → IsIdemOf φ e → ∀ (red : OI v →+* kP PP), (∀ (a : Formalism.IndefR.Lev.EAf D) (ha : a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E), ∃ h : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdE φ a ∈ v.adicCompletionIntegers D.host.F, red ⟨GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdE φ a, h⟩ = resS D.host.F PP ⟨a, ha⟩) → ∀ (h : GL (Fin V.rank) (OI v)) (κ : GA D V), Formalism.L2.Theta.SuppAt e V κ → grpCo φ V (frCo φ β) κ = Matrix.GeneralLinearGroup.map (algebraMap (OI v) (Fv D.host.F v)) h → κ ∈ GfC V ∧ finE V κ ∈ Formalism.L2.DIV.St β ∧ redFn β PP (finE V κ) = Matrix.GeneralLinearGroup.map red h ∧ ∀ PP', PP' ≠ PP → ¬ Formalism.IndefR.Lev.IsConjPl PP PP' → redFn β PP' (finE V κ) = 1 := by
  intro D V β Λ N hB P v φ e hP0 he0 red hred h κ hs hκ0
  have he : IsIdemAt e P := (((GlobalTheory.SplitIdemDict.idem_dictionary D).2 v φ P hP0).2.2 e he0).1
  obtain ⟨p, hp, hpp, hres⟩ := exists_idem_int he
  have hg : (Matrix.GeneralLinearGroup.map (rdE φ) β)⁻¹ * Matrix.GeneralLinearGroup.map (rdE φ) (finE V κ) *
      Matrix.GeneralLinearGroup.map (rdE φ) β = Matrix.GeneralLinearGroup.map (algebraMap (OI v) (Fv D.host.F v)) h := by
    rw [← hκ0]
    have : Matrix.GeneralLinearGroup.map (rdE φ) (finE V κ) =
        Matrix.GeneralLinearGroup.map (rdA φ) (Formalism.L2.Theta.matHom V κ) :=
      Units.ext (Matrix.ext fun i j => rdE_finSw φ (Formalism.L2.Theta.mt V κ i j))
    rw [this]
    rfl
  obtain ⟨Y, u, hY, hu', hκ⟩ := exists_lift (Formalism.L2.Herm.intAf D.host.F D.host.E) (rdE φ)
    (algebraMap (OI v) (Fv D.host.F v)) p (fun x hx => hp ▸ cut_inj he0 x hx) (int_lift he0) h β (finE V κ) hg
  have hP : IsPrimeIdem P e (e + cA D e) := Or.inl ⟨he, rfl⟩
  obtain ⟨-, -, T3, -⟩ := GlobalTheory.IdemSupport.supported_group_and_prime_idempotents V
  have hsf := supp_fin V (f := e + cA D e) hs
  have hf : finSw D (e + cA D e) = p + Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) p := by
    rw [RingHom.map_add (f := _), finSw_cA, hp]
  have hSt : finE V κ ∈ St β :=
    mem_St_of_part D.sp.cm.sig V.gram Λ β hB.1 (hatL_selfDual hB) p u hpp (sigR_int p.2) Y hu' (finE V κ)
      (finE_mem_UA V κ) _ hf hsf hκ
  refine ⟨(T3 P e _ hP).2.2.1 κ hs, hSt, Units.ext ?_, fun P' h1 h2 => ?_⟩
  · rw [redFn_of_smul_eq β P _ hSt p hres Y hκ]
    refine Matrix.ext fun i j => ?_
    obtain ⟨hi, hr⟩ := hred (Y i j) (Y i j).2
    exact hr.symm.trans (congrArg red (Subtype.ext (hY i j)))
  · obtain ⟨y, y', hy, hyy, a1, a2⟩ := exists_sep h1 fun h => h2 (isConjPl_symm h)
    obtain ⟨w, hw⟩ := idem_div_int hP y y' hyy a1 a2
    refine redFn_eq_one β P' _ hSt (w * oToS D.host.F D.host.E y) ?_ ?_
    · rw [RingHom.map_mul, resS_oToS, Ideal.Quotient.eq_zero_iff_mem.2 hy, mul_zero]
    · have e1 : ((w * oToS D.host.F D.host.E y : Formalism.L2.Herm.intAf D.host.F D.host.E) : Formalism.IndefR.Lev.EAf D) =
          finSw D (e + cA D e) := hw
      rw [e1]
      exact hsf

end GlobalTheory.DownLift.SplitIntLift

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl idem SplitProj IsIdemOf IsProjAt adjCo grpCo frCo)
open GlobalTheory.DownLift.GenSplit

noncomputable section
namespace GlobalTheory.LiftDiag

section Mat
variable {k : Type} [CommRing k] {n r t : ℕ}

theorem rowIx_inl (h : r + t = n) (j : Fin r) : ((rowIx h) (Sum.inl j)).val = j.val := by
  simp [rowIx]

theorem symm_lower (h : r + t = n) {a : Fin n} (ha : r ≤ a.val) : ∃ j, (rowIx h).symm a = Sum.inr j := by
  rcases hx : (rowIx h).symm a with j | j
  · exfalso
    have : a = rowIx h (Sum.inl j) := by rw [← hx, Equiv.apply_symm_apply]
    have h2 := rowIx_inl h j
    rw [← this] at h2
    omega
  · exact ⟨j, rfl⟩

theorem symm_castLE (h : r + t = n) (hr : r ≤ n) (a : Fin r) : (rowIx h).symm (Fin.castLE hr a) = Sum.inl a := by
  rw [Equiv.symm_apply_eq]
  ext
  rw [rowIx_inl]
  rfl

theorem lower_row (h : r + t = n) (A : Matrix (Fin r) (Fin r) k) {a : Fin n} (ha : r ≤ a.val) (b : Fin n) :
    ((Matrix.fromBlocks A 0 0 (1 : Matrix (Fin t) (Fin t) k)).submatrix (rowIx h).symm (rowIx h).symm) a b =
      (1 : Matrix (Fin n) (Fin n) k) a b := by
  obtain ⟨j, hj⟩ := symm_lower h ha
  rw [Matrix.submatrix_apply, hj]
  have e1 : (1 : Matrix (Fin n) (Fin n) k) a b =
      (1 : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) k) ((rowIx h).symm a) ((rowIx h).symm b) := by
    simp only [Matrix.one_apply, (rowIx h).symm.injective.eq_iff]
  rw [e1, hj]
  rcases (rowIx h).symm b with j' | j'
  · simp [Matrix.fromBlocks_apply₂₁, Matrix.one_apply]
  · simp [Matrix.fromBlocks_apply₂₂, Matrix.one_apply]

theorem mem_blockTri_diag (h : r + t = n) (A : Matrix (Fin r) (Fin r) k) {b : Fin n → ℕ}
    (hb : ∀ a : Fin n, a.val < r → b a = 0) (g : GL (Fin n) k)
    (hg : (g : Matrix (Fin n) (Fin n) k) =
      (Matrix.fromBlocks A 0 0 (1 : Matrix (Fin t) (Fin t) k)).submatrix (rowIx h).symm (rowIx h).symm) :
    g ∈ blockTri b := by
  intro i j hij
  have hi : r ≤ i.val := by
    by_contra hc
    rw [hb i (by omega)] at hij
    omega
  show (g : Matrix (Fin n) (Fin n) k) i j = 0
  rw [hg, lower_row h A hi, Matrix.one_apply_ne]
  rintro rfl
  exact lt_irrefl _ hij

theorem blockDiagonalPart_blockDiagOne_reindexed_eq_one (h : r + t = n) (A : Matrix (Fin r) (Fin r) k) {b : Fin n → ℕ}
    (hb : ∀ a : Fin n, a.val < r → b a = 0) (g : GL (Fin n) k)
    (hg : (g : Matrix (Fin n) (Fin n) k) =
      (Matrix.fromBlocks A 0 0 (1 : Matrix (Fin t) (Fin t) k)).submatrix (rowIx h).symm (rowIx h).symm)
    {c : ℕ} (hc : c ≠ 0) : dBlk b c g = 1 := by
  apply Units.ext
  rw [diag_block_det_val c (mem_blockTri_diag h A hb g hg), Units.val_one]
  have : (g : Matrix (Fin n) (Fin n) k).submatrix (Subtype.val : {a : Fin n // b a = c} → Fin n) (Subtype.val : {a : Fin n // b a = c} → Fin n) = 1 := by
    ext x y
    have hx : r ≤ x.1.val := by
      by_contra hh
      exact hc (x.2.symm.trans (hb _ (by omega)))
    rw [Matrix.submatrix_apply, hg, lower_row h A hx]
    simp only [Matrix.one_apply, Subtype.ext_iff]
  rw [this, Matrix.det_one]

theorem topLeftBlock_blockDiagOne_reindexed_eq (h : r + t = n) (hr : r ≤ n) (A : Matrix (Fin r) (Fin r) k) (g : GL (Fin n) k)
    (hg : (g : Matrix (Fin n) (Fin n) k) =
      (Matrix.fromBlocks A 0 0 (1 : Matrix (Fin t) (Fin t) k)).submatrix (rowIx h).symm (rowIx h).symm) :
    ((upperLeftBlock hr g : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) = A := by
  have hb : ∀ a : Fin n, a.val < r → blk2 r a = 0 := fun a ha => by simp [blk2, ha]
  rw [upper_block_val_submatrix hr (mem_blockTri_diag h A hb g hg), hg]
  ext a b
  simp only [Matrix.submatrix_apply, symm_castLE h hr, Matrix.fromBlocks_apply₁₁]

theorem blockIndexSecond_eq_zero_of_lt (r : ℕ) (a : Fin n) (ha : a.val < r) : blk2 r a = 0 := by simp [blk2, ha]

theorem blkOf_low (r t : ℕ) (a : Fin n) (ha : a.val < r) : blkOf r t a = 0 := by simp [blkOf, ha]

end Mat

end GlobalTheory.LiftDiag

namespace GlobalTheory.LiftDiag

theorem lift_diag : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), ∀ (i : Fin D.R.m) (t : T) (PP : Pl D.host.E) (hPP : PP ∈ R.Pg) (g : G), (∀ PP' : R.Pg, PP' ≠ ⟨PP, hPP⟩ → R.eG g PP' = 1) → ∀ κ : GA D (Vc D i), κ ∈ GfC (Vc D i) → finE (Vc D i) κ ∈ Formalism.L2.DIV.St (R.βV i) → ((redFn (R.βV i) PP (finE (Vc D i) κ) : GL (Fin (Vc D i).rank) (kP PP)) : Matrix (Fin (Vc D i).rank) (Fin (Vc D i).rank) (kP PP)) = (Matrix.fromBlocks ((R.eG g ⟨PP, hPP⟩ : GL (Fin D.R.r) (kP PP)) : Matrix (Fin D.R.r) (Fin D.R.r) (kP PP)) 0 0 (1 : Matrix (Fin D.R.t) (Fin D.R.t) (kP PP))).submatrix (rowIx (rank_V i)).symm (rowIx (rank_V i)).symm → (∀ PP', PP' ∈ R.Pg ∨ PP' ∈ R.Q t → PP' ≠ PP → redFn (R.βV i) PP' (finE (Vc D i) κ) = 1) → IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) (R.eG g) κ ∧ levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) κ = 1 := by
  intro D G _ _ Pl0 T A Ks _ _ _ R i t PP hPP g hg κ hκ hSt hN hoth
  have memb : ∀ b : Fin (Vc D i).rank → ℕ, (∀ a : Fin (Vc D i).rank, a.val < D.R.r → b a = 0) →
      ∀ PP', PP' ∈ R.Pg ∨ PP' ∈ R.Q t → redFn (R.βV i) PP' (finE (Vc D i) κ) ∈ blockTri b := by
    intro b hb PP' hP'
    by_cases he : PP' = PP
    · subst he; exact mem_blockTri_diag (rank_V i) _ hb _ hN
    · rw [hoth PP' hP' he]; exact Subgroup.one_mem _
  have dB : ∀ b : Fin (Vc D i).rank → ℕ, (∀ a : Fin (Vc D i).rank, a.val < D.R.r → b a = 0) → ∀ c : ℕ, c ≠ 0 →
      ∀ PP', PP' ∈ R.Pg ∨ PP' ∈ R.Q t → dBlk b c (redFn (R.βV i) PP' (finE (Vc D i) κ)) = 1 := by
    intro b hb c hc PP' hP'
    by_cases he : PP' = PP
    · subst he; exact blockDiagonalPart_blockDiagOne_reindexed_eq_one (rank_V i) _ hb _ hN hc
    · rw [hoth PP' hP' he]; exact blockDiagonalExtendByOnePrimeField_one _ _
  refine ⟨⟨hκ, ?_, ?_⟩, ?_⟩
  · exact mem_parLev.2 ⟨GlobalTheory.LevSplit.finE_mem_UA _ κ, hSt,
      fun PP' hP' => memb _ (blkOf_low _ _) PP' (Or.inl hP'), fun PP' hP' => memb _ (blockIndexSecond_eq_zero_of_lt _) PP' (Or.inr hP')⟩
  · funext PP'
    obtain ⟨PP', hP'⟩ := PP'
    show upperLeftBlock _ (redFn (R.βV i) PP' (finE (Vc D i) κ)) = R.eG g ⟨PP', hP'⟩
    by_cases he : PP' = PP
    · subst he; apply Units.ext; exact topLeftBlock_blockDiagOne_reindexed_eq (rank_V i) _ _ _ hN
    · rw [hoth PP' (Or.inl hP') he]
      have h1 : upperLeftBlock (r_le_V i) (1 : GL (Fin (Vc D i).rank) (kP PP')) = 1 := blockDiagonalExtendByOnePrimeField_one _ _
      have h2 : R.eG g ⟨PP', hP'⟩ = 1 := hg ⟨PP', hP'⟩ (fun h => he (congrArg Subtype.val h))
      rw [h2]
      exact h1
  · have key : levFn (R.βV i) (flagL (R.datVt i t)) (finE (Vc D i) κ) = 1 := by
      unfold levFn
      rw [Finset.prod_eq_one, Finset.prod_eq_one, mul_one, mul_one]
      · exact (extendOne_of_mem _ (Subgroup.mem_top _)).trans rfl
      · intro PP' hP'
        exact (congrArg _ (dB _ (blockIndexSecond_eq_zero_of_lt _) 1 one_ne_zero PP' (Or.inr hP'))).trans (map_one _)
      · intro PP' hP'
        exact Finset.prod_eq_one fun c _ =>
          (congrArg _ (dB _ (blkOf_low _ _) (c + 1) (Nat.succ_ne_zero c) PP' (Or.inl hP'))).trans (map_one _)
    show ((levFn (R.βV i) (flagL (R.datVt i t)) (finE (Vc D i) κ) : ℂˣ) : ℂ) = 1
    rw [key, Units.val_one]

end GlobalTheory.LiftDiag
end
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel

namespace GlobalTheory.ResSel

theorem residual_bound_of_parts : Cheb → PoitouTateTotallyComplex → CohDimTwo → TameLocal → LocalFiniteness → LocalTateDuality → LocalEulerChar → GlobalFiniteness → GlobalEulerChar → UnramifiedOrthogonality → Gen.ArchimedeanSignatureMatching → GreenbergWiles → ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X), ResidualBoundOddPrimes bkP := by
  intro hC hPT hCD hT hLF hLT hLE hGF hGE hU hA _ D N X bkP
  have hgw : ∀ i s, GalHyp bkP i s → EqDim bkP i s := fun i s h =>
    GlobalTheory.T.residual_selmer_finrank_eq_dual hC hPT hCD hT hLF hLT hLE hGF hGE hU hA D N X bkP i s h
  refine GlobalTheory.T.residual_bound_of_components D N X bkP (fun i => GlobalTheory.T.exists_auxiliary_primes_prescribed_frobenius hC D N X i)
    (fun i => GlobalTheory.T.exists_elements_selmerForms_small_corank hGF D N X bkP i fun s h =>
      ⟨GlobalTheory.T.cocycleFormsSpan_oddResidueChar D N X bkP i s h, GlobalTheory.T.span_two_of_galois_hypothesis D N X bkP i s h, hgw i s h⟩)
    (fun i s h => ?_)
  have hk := GlobalTheory.T.firstHalfLocalCohomologyVanishing_of_localDualityTheorems hLF hLT hLE hT D N X bkP i s h
  exact GlobalTheory.T.residual_selmer_determinant_order_bound hT D N X bkP i s h hk
    (GlobalTheory.T.reciprocity_auxiliaryPlaces_secondHalf hC hPT hCD hT hLF hLT hLE hGF hGE hU hA D N X bkP i s h hk) (hgw i s h)

end GlobalTheory.ResSel
end

section

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

theorem _root_.GlobalTheory.T.arcCoordinatesCaseA_of_admArcA_of_P1free_of_adm11 : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), UnusedSlot80.AdmArcA D HW F Cm → DeltaInvariantLattices.WachLatticeFreeGlobal D HW F → RamifiedCoefficientChains.adm11 D → UnusedSlot80.ArcLiftingCoordinates D HW F Cm := by
  first | exact @GlobalTheory.admissibleArcDatum_gives_arcProperty | exact GlobalTheory.admissibleArcDatum_gives_arcProperty | (intros; apply GlobalTheory.admissibleArcDatum_gives_arcProperty <;> assumption)
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

theorem _root_.GlobalTheory.T.letterConditionGlobal_of_N1used : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), Formalism.MainNotions.DeltaInvariantLattices.DeltaInvariantNormBound D HW F Cm → Formalism.MainNotions.N.LetterConditionGlobal D HW F := by
  first | exact @GlobalTheory.PrimeSequence.eigenvalue_product_maps_letter_lattice_of_conclusions | exact GlobalTheory.PrimeSequence.eigenvalue_product_maps_letter_lattice_of_conclusions | (intros; apply GlobalTheory.PrimeSequence.eigenvalue_product_maps_letter_lattice_of_conclusions <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

theorem _root_.GlobalTheory.T.classSplitting_along_arcs_of_admissible : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), UnusedSlot80.AdmSplitA D HW F Cm → UnusedSlot80.AdmArcA D HW F Cm → DeltaInvariantLattices.WachLatticeFreeGlobal D HW F → DeltaInvariantLattices.P6 D HW F → LiftingTheory.WachKillsQuotients D HW F → InvariantsGenerators.LitFont D HW F → LiftingTheory.adm23 D HW F → TruncatedSeriesCountingBounds.adm9 D → RamifiedCoefficientChains.adm11 D → UnusedSlot80.SplittingArcLifting D HW F Cm := by
  first | exact @GlobalTheory.classSplitAlongArcs | exact GlobalTheory.classSplitAlongArcs | (intros; apply GlobalTheory.classSplitAlongArcs <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.theoremB_of_admittedHypotheses : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (r : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (large₂ : SizeData₂ D) (ep : Bool) (CA C : ℝ) (Qp : MvPolynomial (Fin 3) ℕ), 13 * max CA 0 ≤ C → (∀ f r t : ℕ, 260 * f ^ 2 * t ^ 2 * (r + t) ≤ EmbeddingTypeJumps.polyVal Qp f r t) → EmbeddingTypeJumps.admW (D := D) HW F → EmbeddingTypeJumps.admA (D := D) CA → EmbeddingTypeJumps.GlobalIndexAwayFromTypes r ρ → EmbeddingTypeJumps.admG1 r → EmbeddingTypeJumps.admG2 r ρ → EmbeddingTypeJumps.admG3 r ρ → EmbeddingTypeJumps.admG4 r → EmbeddingTypeJumps.admG5 r → EmbeddingTypeJumps.admG6 r → EmbeddingTypeJumps.iwahoriAdmissibleSet r ρ → EmbeddingTypeJumps.admTB (D := D) HW F → EmbeddingTypeJumps.admBK (D := D) → EmbeddingTypeJumps.KillingTwistedPlaces ρ → EmbeddingTypeJumps.HodgeJumpWindowsAtDistinguishedPrimes r ep large₂ → EmbeddingTypeJumps.FontaineSubOfSumsAtDistinguishedPrimes r ρ → EmbeddingTypeJumps.LiteratureHypotheses (D := D) → EmbeddingTypeJumps.ParametersPolynomiallyBounded large₂ → EmbeddingTypeJumps.Conclusion2 ρ large₂ C Qp := by
  first | exact @GlobalTheory.TheoremB.theoremB_of_admitted | exact GlobalTheory.TheoremB.theoremB_of_admitted | (intros; apply GlobalTheory.TheoremB.theoremB_of_admitted <;> assumption)
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

theorem _root_.GlobalTheory.T.gamma_sub_one_div_uniformiser_at_letter_of_conclusions : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), Formalism.MainNotions.DeltaInvariantLattices.DeltaInvariantNormBound D HW F Cm → Formalism.MainNotions.RamifiedCoefficientChains.adm18 D HW F := by
  first | exact @GlobalTheory.adm18_of_N1used | exact GlobalTheory.adm18_of_N1used | (intros; apply GlobalTheory.adm18_of_N1used <;> assumption)
end
