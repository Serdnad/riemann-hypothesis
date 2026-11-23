module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle021
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffHeckePolyOfComplex
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1648
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle257
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle511
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle726
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle547
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle548
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle737
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle738
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle024
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle731
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle586
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.Kernel
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle732
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle733
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle605
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.TransSum

def conjMeet {Γ : Type*} [Group Γ] (K : Subgroup Γ) (γ : Γ) : Subgroup Γ :=
  K ⊓ K.comap (MulAut.conj γ⁻¹).toMonoidHom

theorem mem_conjMeet {Γ : Type*} [Group Γ] {K : Subgroup Γ} {γ x : Γ} :
    x ∈ conjMeet K γ ↔ x ∈ K ∧ γ⁻¹ * x * γ ∈ K := by
  simp [conjMeet, Subgroup.mem_inf, Subgroup.mem_comap, MulAut.conj_apply]

theorem exists_sum_inv {Γ : Type*} [Group Γ] (K : Subgroup Γ) (γ : Γ)
    [hf : ((conjMeet K γ).subgroupOf K).FiniteIndex] :
    ∃ C : Finset Γ, C.Nonempty ∧ (∀ δ ∈ C, ∃ k ∈ K, δ = k * γ) ∧
      ∀ F : Γ → ℂ, (∀ k ∈ K, ∀ g, F (g * k) = F g) → ∀ k ∈ K, ∀ g,
        ∑ δ ∈ C, F (g * k * δ) = ∑ δ ∈ C, F (g * δ) := by
  classical
  set H := (conjMeet K γ).subgroupOf K
  haveI : Fintype (K ⧸ H) := Fintype.ofFinite _
  let r : K ⧸ H → Γ := fun q => ((Quotient.out q : K) : Γ) * γ
  have hr : Function.Injective r := by
    intro q₁ q₂ h
    have h' : (Quotient.out q₁ : K) = Quotient.out q₂ := Subtype.ext (mul_right_cancel h)
    rw [← Quotient.out_eq q₁, ← Quotient.out_eq q₂, h']
  refine ⟨Finset.univ.image r, ?_, ?_, ?_⟩
  · exact Finset.image_nonempty.2 ⟨(QuotientGroup.mk 1 : K ⧸ H), Finset.mem_univ _⟩
  · intro δ hδ
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hδ
    exact ⟨_, (Quotient.out q).2, rfl⟩
  · intro F hF k hk g
    rw [Finset.sum_image (fun a _ b _ h => hr h), Finset.sum_image (fun a _ b _ h => hr h)]
    let kk : K := ⟨k, hk⟩

    have key : ∀ q : K ⧸ H, F (g * k * r q) = F (g * r (kk • q)) := by
      intro q
      have hq : (QuotientGroup.mk (Quotient.out (kk • q)) : K ⧸ H) = QuotientGroup.mk (kk * Quotient.out q) := by
        rw [QuotientGroup.out_eq']
        conv_lhs => rw [← QuotientGroup.out_eq' q]
        rfl
      have hm := QuotientGroup.eq.1 hq
      rw [Subgroup.mem_subgroupOf, mem_conjMeet] at hm
      have e : g * k * r q = g * r (kk • q) * (γ⁻¹ * ((((Quotient.out (kk • q))⁻¹ * (kk * Quotient.out q) : K) : Γ)) * γ) := by
        simp only [r, Subgroup.coe_mul, Subgroup.coe_inv, kk]
        group
      rw [e, hF _ hm.2]

    rw [Finset.sum_congr rfl fun q _ => key q]
    exact Fintype.sum_equiv (MulAction.toPerm kk) _ _ (fun q => rfl)

end GlobalTheory.TransSum

namespace GlobalTheory.TransSum

theorem heckeOn_doubleCoset_mem_wall : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {i : Fin D.R.m}, LevProd R i → ∀ (γ : GA D (Wc D i)), γ ∈ GfC (Wc D i) → ∃ C : Finset (GA D (Wc D i)), C.Nonempty ∧ (∀ δ ∈ C, ∃ k ∈ levW R i, δ = k * γ) ∧ ∀ T ∈ R.Wall i (sg0 D A), heckeOn (R.MW i (sg0 D A)) C T ∈ R.Wall i (sg0 D A) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R i hP γ hγ
  have topgrp := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig (Wc D i).gram
  haveI : CompactSpace (levW R i) :=
    isCompact_iff_compactSpace.mp (GlobalTheory.ParahoricCompact.isCompact_levG _ _ _)
  have hU := GlobalTheory.LevelOpen.isOpen_levG (Wc D i) (R.βW i) (R.datWp i R.triv)
  have hopen : IsOpen (((conjMeet (levW R i) γ).subgroupOf (levW R i) : Subgroup (levW R i)) : Set (levW R i)) := by
    let φ : levW R i → GfC (Wc D i) := fun x =>
      ⟨γ⁻¹ * (x : GA D (Wc D i)) * γ, mul_mem (mul_mem (inv_mem hγ) (hP.1 x.2)) hγ⟩
    have hφ : Continuous φ := by
      refine Continuous.subtype_mk ?_ _
      exact (continuous_const.mul continuous_subtype_val).mul continuous_const
    have e : (((conjMeet (levW R i) γ).subgroupOf (levW R i) : Subgroup (levW R i)) : Set (levW R i)) =
        φ ⁻¹' {g : GfC (Wc D i) | (g : GA D (Wc D i)) ∈ levG _ (R.βW i) (R.datWp i R.triv)} := by
      ext x
      simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf, mem_conjMeet, Set.mem_preimage, Set.mem_setOf_eq, φ]
      exact ⟨fun h => h.2, fun h => ⟨x.2, h⟩⟩
    rw [e]
    exact hU.preimage hφ
  haveI : Finite (levW R i ⧸ (conjMeet (levW R i) γ).subgroupOf (levW R i)) :=
    Subgroup.quotient_finite_of_isOpen _ hopen
  haveI : ((conjMeet (levW R i) γ).subgroupOf (levW R i)).FiniteIndex :=
    Subgroup.finiteIndex_of_finite_quotient
  obtain ⟨C, hne, hC, hsum⟩ := exists_sum_inv (levW R i) γ
  refine ⟨C, hne, hC, fun Tm hT => ?_⟩
  have hCf : ∀ a ∈ C, a ∈ GfC (Wc D i) := by
    intro a ha
    obtain ⟨k, hk, rfl⟩ := hC a ha
    exact mul_mem (hP.1 hk) hγ
  unfold RealDat.Wall at hT ⊢
  rw [GlobalTheory.MultMem.mem_mult_iff] at hT ⊢
  refine GlobalTheory.HeckeParts.isMultMap_heckeOn hT hCf fun v k hk g => ?_
  have h1 : levChi _ (R.βW i) (R.datWp i R.triv) k = 1 := hP.2.1 k hk
  rw [h1, one_mul, heckeLin_apply, heckeLin_apply]
  exact hsum (Tm v) (fun k' hk' g' => by rw [hT.lev v k' hk' g', hP.2.1 k' hk', one_mul]) k hk g

end GlobalTheory.TransSum

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open GlobalTheory.BadPlace
open Classical

noncomputable section

namespace GlobalTheory.BadPlace

theorem datP_ne_zero_unpack {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (ea : AE D)
    (y : WO (Vc D i) (Wc D i)) (h : datP R i t ea y ≠ 0) :
    IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) y) ∧
    (∀ PP ∈ R.Pg, topL (Wc D i).rank (redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) y)) = 1) ∧
    (∀ PP ∈ R.Q t, IsUnit (topL (Wc D i).rank (redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) y))).det) := by
  unfold datP at h
  split_ifs at h with hc
  · refine ⟨hc.2, fun PP hPP => ?_, fun PP hPP => ?_⟩
    · have hK := left_ne_zero_of_mul h
      unfold omegaK at hK
      split_ifs at hK with hh
      · exact (hh PP hPP).2
      · exact absurd rfl hK
    · have hQ := right_ne_zero_of_mul h
      unfold omegaQ at hQ
      split_ifs at hQ with hh
      · exact (hh PP hPP).2
      · exact absurd rfl hQ
  · exact absurd rfl h

theorem disj_supp : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (ea : AE D), IsIdemSum ea (R.Pg ∪ R.Q t) → ∀ (P : Pl D.host.E), P ∈ R.Pg ∨ P ∈ R.Q t → ∀ e f, IsPrimeIdem P e f → ∀ k, SuppF (Wc D i) f k → k ∉ levW R i → ∀ x x' : WO (Vc D i) (Wc D i), (∀ a b, f * x a b = f * x' a b) → datP R i t ea (actO (Vc D i) (Wc D i) 1 k⁻¹ x) ≠ 0 → datP R i t ea x' ≠ 0 → False := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hL hFP i t ea hea P hP e f hpe k hk hkn x x' hxx h1 h2
  apply hkn
  have hPS : P ∈ R.Pg ∪ R.Q t := Finset.mem_union.2 hP
  obtain ⟨heP, hfe, hcf, hinf, hcP⟩ := GlobalTheory.T.primeIdempotent_of_idempotentSum_place_split D P e f ea (R.Pg ∪ R.Q t) hpe hea hPS
  obtain ⟨hI1, hK1, hQ1⟩ := datP_ne_zero_unpack R i t ea _ h1
  obtain ⟨hI2, hK2, hQ2⟩ := datP_ne_zero_unpack R i t ea _ h2
  have hY := GlobalTheory.T.frameMapAdjoint_translate_inv_eq_mul_frameMatrix D (Vc D i) (Wc D i) (R.βV i) (R.βW i) k x
  have hid := GlobalTheory.T.frameMapAdjoint_mul_frameMatrix_eq_idempotent_split D (Vc D i) (Wc D i) (R.βV i) (R.βW i) f hcf k hk x x' hxx
  rw [← hY] at hid

  have he1 := GlobalTheory.StdFrames.cpt_of_isIdemAt heP
  have hcPP : GlobalTheory.IdemSupport.cP P ≠ P := hcP P hPS
  have hfP : GlobalTheory.StdFrames.cpt P (toEAf D f) = 1 := by
    rw [hfe, RingHom.map_add (f := _), GlobalTheory.StdFrames.toEAf_cA, RingHom.map_add (f := _), he1.1,
      GlobalTheory.StdFrames.cpt_sg_eq_zero (he1.2 _ hcPP), add_zero]
  have hfoff : ∀ PP ∈ R.Pg, PP ≠ P → GlobalTheory.StdFrames.cpt PP (toEAf D f) = 0 := by
    intro PP hPP hne
    rw [hfe, RingHom.map_add (f := _), GlobalTheory.StdFrames.toEAf_cA, RingHom.map_add (f := _), he1.2 _ hne,
      GlobalTheory.StdFrames.cpt_sg_eq_zero (he1.2 _ (hcP PP (Finset.mem_union_left _ hPP))), add_zero]
  have hu : ∀ (y : WO (Vc D i) (Wc D i)), (∀ PP ∈ R.Pg, topL (Wc D i).rank (redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) y)) = 1) →
      (∀ PP ∈ R.Q t, IsUnit (topL (Wc D i).rank (redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) y))).det) →
      IsUnit (topL (Wc D i).rank (redM P (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) y))).det := by
    intro y hK hQ
    rcases hP with hP | hP
    · rw [hK P hP, Matrix.det_one]; exact isUnit_one
    · exact hQ P hP
  obtain ⟨hint, hdet, hone⟩ := GlobalTheory.T.localFrameChange_mem_integralGL_at_place D P _ _ _ _ _ _ hfP hid hI2 hI1 (hu _ hK2 hQ2) (hu _ hK1 hQ1)
  have hSt := GlobalTheory.T.finiteAdelic_mem_selfDualFrameStabilizer_of_splitSupport D (Wc D i) (R.βW i) (R.ΛW i) (hL.lev.βW i) e f P heP hfe hcPP k hk hint hdet
  have hred : ∀ PP, PP ∈ (R.datWp i R.triv).Pg ∨ PP ∈ (R.datWp i R.triv).Q → redFn (R.βW i) PP (finE (Wc D i) k) = 1 := by
    rintro PP (hPP | hPP)
    · change PP ∈ R.Pg at hPP
      refine GlobalTheory.T.frameReduction_eq_one_of_frameMatrix_congruent_one D (Wc D i) (R.βW i) k PP hSt ?_
      by_cases hPe : PP = P
      · subst hPe
        exact hone (hK2 PP hPP) (hK1 PP hPP)
      · intro a b
        rw [GlobalTheory.T.frameMatrix_component_sub_one_eq_zero_off_idempotent D (Wc D i) (R.βW i) f k PP hk (hfoff PP hPP hPe) a b, map_zero]
        exact zero_lt_one
    · exact absurd hPP (Finset.notMem_empty _)
  exact ⟨GlobalTheory.IdemSupport.mem_GfC_of_suppF (Wc D i) hinf hk,
    GlobalTheory.LevSplit.mem_lev_of_red D.sp.cm (Wc D i).gram (R.βW i) (R.datWp i R.triv) _ (GlobalTheory.LevSplit.finE_mem_UA _ k) hSt hred⟩

end GlobalTheory.BadPlace

end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BKLim.BetaStep

variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l} (bk : BK K)

theorem evE_ne_zero : bk.ev bk.E ≠ 0 := fun h =>
  bk.E_ne_zero (bk.ev_injective (by rw [h, map_zero]))

theorem theta_eq_zero_iff (a : Ainf l) : Per.θ l a = 0 ↔ bk.ev bk.E ∣ a := by
  rw [← RingHom.mem_ker, ← bk.span_ev, Ideal.mem_span_singleton]

theorem dvd_of_dvd_lpow_mul (n : ℕ) (c : Ainf l) (h : bk.ev bk.E ∣ (l : Ainf l) ^ n * c) :
    bk.ev bk.E ∣ c := by
  rw [← theta_eq_zero_iff] at h ⊢
  rw [map_mul, map_pow, map_natCast] at h
  have hne : ((l : OC l)) ^ n ≠ 0 := pow_ne_zero _ (fun h0 =>
    GlobalTheory.RingBasics.p_ne_zero (p := l) (by simpa using congrArg Subtype.val h0))
  exact (mul_eq_zero.mp h).resolve_left hne

theorem pow_dvd_of_l_mul (m : ℕ) : ∀ a : Ainf l,
    bk.ev bk.E ^ m ∣ (l : Ainf l) * a → bk.ev bk.E ^ m ∣ a := by
  induction m with
  | zero => intro a _; simp
  | succ m ih =>
    intro a h
    have h1 : bk.ev bk.E ∣ (l : Ainf l) ^ 1 * a := by
      rw [pow_one]; exact dvd_trans (dvd_pow_self _ (Nat.succ_ne_zero m)) h
    obtain ⟨a', rfl⟩ := dvd_of_dvd_lpow_mul bk 1 a h1
    rw [pow_succ']
    apply mul_dvd_mul_left
    apply ih
    rw [pow_succ', mul_left_comm] at h
    exact (mul_dvd_mul_iff_left (evE_ne_zero bk)).mp h

theorem pow_dvd_of_lpow (i n : ℕ) (a : Ainf l) (h : bk.ev bk.E ^ i ∣ (l : Ainf l) ^ n * a) :
    bk.ev bk.E ^ i ∣ a := by
  induction n generalizing a with
  | zero => simpa using h
  | succ n ih =>
    apply ih
    apply pow_dvd_of_l_mul bk i
    rw [← mul_assoc, ← pow_succ']
    exact h

end GlobalTheory.BKLim.BetaStep


open GlobalTheory.BKLim.BetaStep in
theorem GlobalTheory.BKLim.beta_step : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (N d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (F : Frame bk N d ρ) (g : ↥(GK K)) (w : Ainf l), Per.σA (g : GQ l) (bk.ev bk.E) = bk.ev bk.E * w → ∀ (m k : ℕ) (β : Matrix (Fin d) (Fin d) bk.S), F.IsBeta m k β → ∀ (i n : ℕ), i + 1 ≤ m → ∀ γ : Matrix (Fin d) (Fin d) bk.S, (∀ p q, bk.E ^ i ∣ (β - (l : bk.S) ^ n • γ) p q) → ∃ δ : Matrix (Fin d) (Fin d) bk.S, (∀ p q, bk.E ^ (i + 1) ∣ (β - (l : bk.S) ^ n • γ - bk.E ^ i • δ) p q) ∧ ∀ p q, ∃ y : OC l, Per.θ l (bk.ev (δ p q)) * (Per.θ l w ^ i - 1) = (l : OC l) ^ n * y := by
  intro l _ K bk N d ρ F g w hw m k β hβ i n him γ hγ
  haveI : IsDomain (Ainf l) := inclW_injective.isDomain (inclW l)
  choose δ hδ using hγ
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at hδ
  refine ⟨Matrix.of δ, fun p q => ?_, fun p q => ?_⟩
  · simp [Matrix.sub_apply, Matrix.smul_apply, hδ]
  set P : Fin d → Fin d → Ainf l := fun a c => WittVector.frobenius (F.ε g a c) with hPdef
  set σ := Per.σA (g : GQ l)
  have hent : ∀ a b, bk.ev bk.E ^ m ∣ ∑ c, P a c * σ (bk.ev (β c b)) - bk.ev (β a b) := by
    intro a b
    have := hβ.2 g a b
    simpa [Matrix.sub_apply, Matrix.mul_apply, Matrix.map_apply, hPdef] using this
  have hm : 0 < m := by omega
  have hθβ : ∀ c b, Per.θ l (bk.ev (β c b)) = (l : OC l) ^ k * (if c = b then 1 else 0) := by
    intro c b
    have h2 : Per.θ l (bk.ev ((β - (l : bk.S) ^ k • (1 : Matrix (Fin d) (Fin d) bk.S)) c b)) = 0 :=
      (theta_eq_zero_iff bk _).2 (map_dvd bk.ev (hβ.1 c b))
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, map_sub, map_mul, map_pow,
      map_natCast] at h2
    rw [sub_eq_zero] at h2
    rw [h2]; split_ifs <;> simp
  have hlOC : ((l : ℕ) : OC l) ≠ 0 := fun h =>
    GlobalTheory.RingBasics.p_ne_zero (p := l) (by simpa using congrArg Subtype.val h)
  have hP : ∀ a c, Per.θ l (P a c) = if a = c then 1 else 0 := by
    intro a b
    have h := (theta_eq_zero_iff bk _).2 ((dvd_pow_self _ hm.ne').trans (hent a b))

    simp only [σ, map_sub, map_sum, map_mul, GlobalTheory.BKLim.BetaBd.θ_σA_ev, hθβ, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
    rw [sub_eq_zero] at h
    have hl := pow_ne_zero k hlOC
    apply mul_right_cancel₀ hl
    rw [h]; split_ifs <;> simp

  have hβe : ∀ c b, β c b = (l : bk.S) ^ n * γ c b + bk.E ^ i * δ c b := fun c b => by
    rw [← hδ c b]; ring
  have hσE : σ (bk.ev bk.E) ^ i = bk.ev bk.E ^ i * w ^ i := by rw [hw, mul_pow]
  have hD : ∀ a b, ∑ c, P a c * σ (bk.ev (β c b)) - bk.ev (β a b) =
      (l : Ainf l) ^ n * (∑ c, P a c * σ (bk.ev (γ c b)) - bk.ev (γ a b)) +
      bk.ev bk.E ^ i * (w ^ i * ∑ c, P a c * σ (bk.ev (δ c b)) - bk.ev (δ a b)) := by
    intro a b
    have e1 : ∀ c, P a c * σ (bk.ev (β c b)) = (l : Ainf l) ^ n * (P a c * σ (bk.ev (γ c b))) +
        bk.ev bk.E ^ i * (w ^ i * (P a c * σ (bk.ev (δ c b)))) := by
      intro c
      rw [hβe]
      simp only [map_add (f := _), map_mul, map_pow, map_natCast, hσE]
      ring
    rw [Finset.sum_congr rfl (fun c _ => e1 c), Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      ← Finset.mul_sum, hβe a b]
    simp only [map_add (f := _), map_mul, map_pow, map_natCast]
    ring
  have hDγ : ∀ a b, bk.ev bk.E ^ i ∣ ∑ c, P a c * σ (bk.ev (γ c b)) - bk.ev (γ a b) := by
    intro a b
    apply pow_dvd_of_lpow bk i n
    have h1 : bk.ev bk.E ^ i ∣ ∑ c, P a c * σ (bk.ev (β c b)) - bk.ev (β a b) :=
      (pow_dvd_pow _ (by omega)).trans (hent a b)
    rw [hD] at h1
    exact (dvd_add_left (dvd_mul_right _ _)).1 h1
  choose η hη using hDγ
  have hX : bk.ev bk.E ∣ (l : Ainf l) ^ n * η p q +
      (w ^ i * ∑ c, P p c * σ (bk.ev (δ c q)) - bk.ev (δ p q)) := by
    have e : bk.ev bk.E ^ i * ((l : Ainf l) ^ n * η p q +
        (w ^ i * ∑ c, P p c * σ (bk.ev (δ c q)) - bk.ev (δ p q))) =
        ∑ c, P p c * σ (bk.ev (β c q)) - bk.ev (β p q) := by
      rw [hD, hη]; ring
    have h1 : bk.ev bk.E ^ i * bk.ev bk.E ∣ bk.ev bk.E ^ i * ((l : Ainf l) ^ n * η p q +
        (w ^ i * ∑ c, P p c * σ (bk.ev (δ c q)) - bk.ev (δ p q))) := by
      rw [e, ← pow_succ]
      exact (pow_dvd_pow _ him).trans (hent p q)
    exact (mul_dvd_mul_iff_left (pow_ne_zero i (evE_ne_zero bk))).1 h1
  rw [← theta_eq_zero_iff] at hX

  simp only [σ, map_add (f := _), map_sub, map_mul, map_pow, map_natCast, map_sum, GlobalTheory.BKLim.BetaBd.θ_σA_ev, hP,
  ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true] at hX
  refine ⟨-Per.θ l (η p q), ?_⟩
  simp only [Matrix.of_apply]
  linear_combination hX
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.semistable_periods_galois_fixing_flat : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : WSeed bk d ρ τ), ∀ g : ↥(GK K), bk.FixFlat g → ∀ G : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) (Per.σA (g : GQ l)) G → (∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) bk.ev j → ∀ x, G (j x) = j x) ∧ bk.iA τ ^ s.N • ((ρ g).map (bk.iA.comp (algebraMap ℤ_[l] (Ainf l))) * s.W.map G) = G (bk.iA τ) ^ s.N • s.W := by
  first | exact @GlobalTheory.BKLim.wseed_gal_periods | exact GlobalTheory.BKLim.wseed_gal_periods | (intros; apply GlobalTheory.BKLim.wseed_gal_periods; all_goals assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem isPushout_of_away {A C A' C' : Type} [CommRing A] [CommRing C] [CommRing A'] [CommRing C']
    (h : A →+* C) (k : A →+* A') (k' : C →+* C') (h' : A' →+* C') (e : k'.comp h = h'.comp k) (x : A)
    (H : letI := h.toAlgebra; IsLocalization.Away x C)
    (H' : letI := h'.toAlgebra; IsLocalization.Away (k x) C') :
    CategoryTheory.IsPushout (CommRingCat.ofHom h) (CommRingCat.ofHom k) (CommRingCat.ofHom k')
      (CommRingCat.ofHom h') := by
  letI : Algebra A C := h.toAlgebra
  letI : Algebra A A' := k.toAlgebra
  letI : Algebra C C' := k'.toAlgebra
  letI : Algebra A' C' := h'.toAlgebra
  letI : Algebra A C' := (h'.comp k).toAlgebra
  haveI : IsScalarTower A A' C' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower A C C' := IsScalarTower.of_algebraMap_eq fun a => (RingHom.congr_fun e a).symm
  haveI : IsLocalization (Submonoid.powers x) C := H
  haveI : IsLocalization (Algebra.algebraMapSubmonoid A' (Submonoid.powers x)) C' := by
    rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers]
    exact H'
  haveI : Algebra.IsPushout A A' C C' :=
    Algebra.isPushout_of_isLocalization (Submonoid.powers x) C A' C'
  exact (CommRingCat.isPushout_iff_isPushout (R := A) (R' := C) (S := A') (S' := C')).2
    (Algebra.IsPushout.symm inferInstance)

theorem IsLoc.isUnit_of_complete {l : ℕ} {R : Type} [CommRing R] {B C : Obj l R} {s : B.A} {h : Hom B C}
    (H : IsLoc s h) : IsUnit (h.f s) := by
  have hu : IsUnit (qmap h 1 (Ideal.Quotient.mk (adI B ^ 1) s)) := by
    letI := (qmap h 1).toAlgebra
    haveI := H.away 1
    exact IsLocalization.Away.algebraMap_isUnit _
  rw [qmap_mk] at hu
  haveI := C.complete
  have hj : adI C ^ 1 ≤ (⊥ : Ideal C.A).jacobson := by
    rw [pow_one]
    exact IsAdicComplete.le_jacobson_bot _
  haveI := isLocalHom_of_le_jacobson_bot _ hj
  exact IsUnit.of_map (Ideal.Quotient.mk _) _ hu

theorem stable_of_isLoc : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (B C : Obj l R) (s : B.A) (h : Hom B C),
    (∃ t ∈ B.I, ∀ x ∈ B.I, ∃ k : ℕ, s ^ k * x ∈ Ideal.span {t}) → IsLoc s h → Stable h := by
  rintro l _ R _ B C s h ⟨t, ht, hst⟩ H
  refine ⟨fun m => ?_, fun B' k => ?_⟩
  · letI := (qmap h m).toAlgebra
    haveI := H.away m
    exact IsLocalization.flat _ (Submonoid.powers (Ideal.Quotient.mk (adI B ^ m) s))
  ·
    have hgen : GenAway B' (k.f s) (k.f t) := by
      refine ⟨k.f_I t ht, fun x hx => ?_⟩
      rw [← GlobalTheory.T.prism_hom_map_ideal_eq l R B B' k] at hx
      have hx' : x ∈ Ideal.span (k.f '' B.I) := hx
      refine Submodule.span_induction
        (p := fun x _ => ∃ n : ℕ, k.f s ^ n * x ∈ Ideal.span {k.f t}) ?_ ?_ ?_ ?_ hx'
      · rintro _ ⟨y, hy, rfl⟩
        obtain ⟨n, hn⟩ := hst y hy
        obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hn
        refine ⟨n, Ideal.mem_span_singleton'.2 ⟨k.f c, ?_⟩⟩
        simpa only [map_mul, map_pow] using congrArg k.f hc
      · exact ⟨0, by simp⟩
      · rintro a b _ _ ⟨n₁, h₁⟩ ⟨n₂, h₂⟩
        refine ⟨n₁ + n₂, ?_⟩
        have hab : k.f s ^ (n₁ + n₂) * (a + b) =
            k.f s ^ n₂ * (k.f s ^ n₁ * a) + k.f s ^ n₁ * (k.f s ^ n₂ * b) := by ring
        rw [hab]
        exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h₁) (Ideal.mul_mem_left _ _ h₂)
      · rintro a b _ ⟨n, hn⟩
        refine ⟨n, ?_⟩
        rw [smul_eq_mul, mul_left_comm]
        exact Ideal.mul_mem_left _ _ hn
    obtain ⟨C', h', hloc', -⟩ := GlobalTheory.T.exists_isPrismLocalizationAway_of_generated l R B' (k.f s) (k.f t) hgen
    obtain ⟨k', hk'⟩ := H.univ C' (h'.comp k)
      (show IsUnit (h'.f (k.f s)) from IsLoc.isUnit_of_complete hloc')
    refine ⟨C', k', h', hk', fun m => ?_⟩
    refine isPushout_of_away (qmap h m) (qmap k m) (qmap k' m) (qmap h' m) ?_
      (Ideal.Quotient.mk _ s) (H.away m) ?_
    · refine Ideal.Quotient.ringHom_ext (RingHom.ext fun a => ?_)
      simp only [RingHom.comp_apply, qmap_mk]
      exact congrArg (fun g : Hom B C' => Ideal.Quotient.mk (adI C' ^ m) (g.f a)) hk'
    · rw [qmap_mk]
      exact hloc'.away m

end GlobalTheory.BSP
end
