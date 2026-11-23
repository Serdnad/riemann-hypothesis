module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle024
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConnPhiExtensionGeneratorEqZeta
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIterateDerivative
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle617
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusStratificationCoeffEqConnectionPow
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CrisToODToOCr
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle621
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle622
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle106
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle623
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrobeniusPeriodRingInjective
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DecompositionInvariantsCondition
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle514
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle646
public import Formalism.SharpRestriction.LevelLetterCocycles.JsetEmb
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle619
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
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Monotonicity.Lemmas
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InvertibleSpanSingleton
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle628
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle015
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.exists_breuilKisinLatticeFrame_of_linked_preframe : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d N : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (tw : Tower ρ) (F : ∀ n, Frame bk N (tw.d' n) fun g => (tw.ρ' n g).val) (P : Pre bk N d fun g => (ρ g).val) (r : ℕ), (∀ n, ∃ m, n ≤ m ∧ Link bk P.T (F m).T (tw.Pi m) n r) → ∃ F₀ : Frame bk N d fun g => (ρ g).val, F₀.toPre = P := by
  first | exact @GlobalTheory.BKLim.frame_of_links | exact GlobalTheory.BKLim.frame_of_links | (intros; apply GlobalTheory.BKLim.frame_of_links <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.breuilKisinFrame_isCr_of_linked_tower : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d N : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (tw : Tower ρ) (F : ∀ n, Frame bk N (tw.d' n) fun g => (tw.ρ' n g).val) (F₀ : Frame bk N d fun g => (ρ g).val) (r : ℕ), (∀ n, ∃ m, n ≤ m ∧ Link bk F₀.T (F m).T (tw.Pi m) n r) → (∀ n, (F n).IsCr) → F₀.IsCr := by
  first | (exact @GlobalTheory.BKLim.CrLimit.isCr_of_link) | (exact GlobalTheory.BKLim.CrLimit.isCr_of_link) | (intros; apply GlobalTheory.BKLim.CrLimit.isCr_of_link  <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix GlobalTheory.BKGal.XiFil
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.XiDecomp

theorem toBcris_xiExt_eq_sum : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (w : Vec K a ι) (hwS : ∀ τ j, w τ j ∈ invL l (S O K e)) (hw : P.xiExt w ∈ P.MMl) (hd : ∀ j, P.xi (fun _ => Pi.single j 1) ∈ P.MMl), toBcris t ϖ P ⟨P.xiExt w, hw⟩ = ∑ j, ϖ.iB t K (fun τ => ⟨w τ j, hwS τ j⟩) • toBcris t ϖ P ⟨P.xi (fun _ => Pi.single j 1), hd j⟩ := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ t ϖ ι _ _ P w hwS hw hd
  have hsum : (⟨P.xiExt w, hw⟩ : P.MMl) = ∑ j, (⟨(fun τ => w τ j) • P.xi (fun _ => Pi.single j 1),
      P.smul_tot_mem_ext (fun τ => hwS τ j) (hd j)⟩ : P.MMl) := by
    apply Subtype.ext
    show P.xiExt w = _
    rw [Submodule.coe_sum]

    conv_lhs => rw [eq_sum_bas w, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    show _ = (fun τ => w τ j) • P.xi (fun _ => Pi.single j 1)
    rw [PhiMod.xiExt_smul_tot, PhiMod.xi_apply, cst_single]

  rw [hsum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ext1 k
  rw [Pi.smul_apply, toBcris_apply, toBcris_apply, smul_eq_mul, ← map_mul]
  congr 1
  funext τ
  apply Subtype.ext
  simp [coordL, Matrix.mulVec_smul]

end GlobalTheory.XiDecomp
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.eq_xi_red_of_conn_eq_zero' : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] (P : PhiMod O K l e a ι) (v : Vec K a ι), P.conn v = 0 → v = P.xi (red v) := by
  first | exact @GlobalTheory.horiz_eq_xi_red | exact GlobalTheory.horiz_eq_xi_red | (intros; apply GlobalTheory.horiz_eq_xi_red <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.frobeniusStratification_coeff_eq_connection_pow : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] (P : PhiMod O K l e a ι) (sh : K⟦X⟧ →+* K⟦X⟧⟦X⟧) (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ (f : K⟦X⟧) (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (sh f) = (PowerSeries.derivative (R := K))^[i] f) → (∀ f : K⟦X⟧, φ₂ (PowerSeries.C f) = PowerSeries.C (frob K l f)) → (∀ f : K⟦X⟧, φ₂ (sh f) = sh (frob K l f)) → ∀ ε : ZMod a → Matrix ι ι K⟦X⟧⟦X⟧, (∀ τ, (ε τ).map PowerSeries.constantCoeff = 1) → (∀ τ, ε τ * ((P.mx (τ - 1)).map (frob K l)).map sh = ((P.mx (τ - 1)).map (frob K l)).map PowerSeries.C * (ε (τ - 1)).map φ₂) → ∀ (τ : ZMod a) (n : ℕ) (i j : ι), (n.factorial : K⟦X⟧) * coeff n (ε τ i j) = (P.mxInv τ *ᵥ (P.nabla ^ n) (P.phi (bas j)) τ) i := by
  first | exact @GlobalTheory.TaylorStrat.stratification_coeff_eq_nabla_pow | exact GlobalTheory.TaylorStrat.stratification_coeff_eq_nabla_pow | (intros; apply GlobalTheory.TaylorStrat.stratification_coeff_eq_nabla_pow <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKReal.IBInj

variable {l : ℕ} [hl : Fact l.Prime] {a e : ℕ} [NeZero a] [NeZero e] {O K : Type} [CommRing O]
  [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K]
  [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [CompleteSpace K]


omit [NeZero a] [NeZero e] [Module.Finite ℤ_[l] O] [CompleteSpace K] in
theorem toOB_injective : Function.Injective (toOB l O) :=
  Module.Flat.lTensor_preserves_injective_linearMap (M := O) (acrisToBcris l).toLinearMap
    (GlobalTheory.MemLoc.PhiInj.algebraMap_acris_bcris_injective l)


omit [NeZero a] in
theorem iSD_eq_of_mem_invL_A (ϖ : PiSys l e) (f : invL l (S O K e)) (hf : (f : K⟦X⟧) ∈ invL l (A O K)) :
    ϖ.iSD O K f = ϖ.iHat O K (toHatS O K l e f) := by
  obtain ⟨n, hn⟩ := hf
  have hlu : IsUnit ((l : OD l O) ^ n) := isUnit_l_OD.pow n
  have hg : ((l : A O K) : K⟦X⟧) ^ n * (f : K⟦X⟧) ∈ S O K e := A_le_S l e hn
  have e1 : (l : invL l (S O K e)) ^ n * f = algebraMap (S O K e) (invL l (S O K e)) ⟨_, hg⟩ :=
    Subtype.ext (by simp)
  have e2 : toHatS O K l e (algebraMap (S O K e) (invL l (S O K e)) ⟨_, hg⟩) =
      ofA O K l e ⟨_, hn⟩ := toHat_eq_ofAl l e rfl
  refine hlu.mul_left_cancel ?_
  have h3 := congrArg (ϖ.iSD O K) e1
  have h4 := congrArg (fun y => ϖ.iHat O K (toHatS O K l e y)) e1
  simp only [map_mul, map_pow, map_natCast] at h3 h4
  rw [h3, h4, e2, ϖ.iHat_ofA O K]
  refine (ϖ.iSD_of_mem O K hg _).trans ?_
  rw [ϖ.iS_of_mem O K hn, crisToOD_toOCr]


omit [NeZero a] in
theorem crisToOD_iS (ϖ : PiSys l e) (s : S O K e) : crisToOD l O (ϖ.iS O K s) =
    ϖ.iHat O K (toHatS O K l e (algebraMap (S O K e) (invL l (S O K e)) s)) := by
  have hlu : IsUnit (l : OD l O) := isUnit_l_OD
  set ξ : OD l O := ϖ.iAl O K (EIn l e _) with hξ
  have hS : ∀ s : S O K e, ϖ.iSD O K (algebraMap (S O K e) (invL l (S O K e)) s) =
      crisToOD l O (ϖ.iS O K s) := fun s => ϖ.iSD_of_mem O K s.2 _
  rw [← sub_eq_zero]
  set D : S O K e → OD l O := fun s => crisToOD l O (ϖ.iS O K s) -
    ϖ.iHat O K (toHatS O K l e (algebraMap (S O K e) (invL l (S O K e)) s)) with hD
  have hDadd : ∀ p q : S O K e, D (p + q) = D p + D q := fun p q => by
    simp only [hD, map_add (f := _)]; ring
  have hDmul : ∀ (k : ℕ) (q : S O K e), D ((l : S O K e) ^ k * q) = (l : OD l O) ^ k * D q := fun k q => by
    simp only [hD, map_mul, map_pow, map_natCast]; ring
  have hdiv : ∀ m : ℕ, ξ ^ m ∣ D s := by
    intro m
    obtain ⟨N, hN⟩ := GlobalTheory.BKReal.CrisBounded.bdd_crisToOD l e O K ϖ m
    have hw : ∀ k : ℕ, ∃ y : OA l O,
        ξ ^ m ∣ (l : OD l O) ^ (N + m) * D s - (l : OD l O) ^ k * toOD l O y := by
      intro k
      obtain ⟨N0, hN0⟩ := exists_sum_monomial_add l e s.2 k
      obtain ⟨h, hh, hs⟩ := hN0 N0 le_rfl
      set hS' : S O K e := ⟨h, hh⟩
      have hP : (s : K⟦X⟧) - (l : K⟦X⟧) ^ k * h ∈ S O K e :=
        sub_mem s.2 (mul_mem (pow_mem (natCast_mem _ l) k) hh)
      set P : S O K e := ⟨_, hP⟩
      have hsP : s = P + (l : S O K e) ^ k * hS' := Subtype.ext (by simp [P, hS'])
      have hPA : (P : K⟦X⟧) ∈ invL l (A O K) := by
        have : (P : K⟦X⟧) = ∑ n ∈ Finset.range N0, monomial n (coeff n (s : K⟦X⟧)) := by
          simp only [P]; linear_combination hs
        rw [this]
        exact sum_mem fun n _ => monomial_mem_invL l n _
      have hDP : D P = 0 := by
        simp only [hD, sub_eq_zero]
        rw [← hS]
        exact iSD_eq_of_mem_invL_A ϖ _ hPA
      obtain ⟨y1, hy1⟩ := hN (ϖ.iS O K hS')
      obtain ⟨y2, hy2⟩ := GlobalTheory.BKReal.exists_l_pow_iHat_toHatS_sub_dvd l e O K ϖ m hS'
      refine ⟨(l : OA l O) ^ m * y1 - (l : OA l O) ^ N * y2, ?_⟩
      have e1 : (l : OD l O) ^ (N + m) * D s - (l : OD l O) ^ k *
            toOD l O ((l : OA l O) ^ m * y1 - (l : OA l O) ^ N * y2) =
          (l : OD l O) ^ k * ((l : OD l O) ^ m * ((l : OD l O) ^ N * crisToOD l O (ϖ.iS O K hS') -
            toOD l O y1) - (l : OD l O) ^ N * ((l : OD l O) ^ m *
              ϖ.iHat O K (toHatS O K l e (algebraMap (S O K e) (invL l (S O K e)) hS')) - toOD l O y2)) := by
        rw [hsP, hDadd, hDP, zero_add, hDmul]
        simp only [hD, map_sub, map_mul, map_pow, map_natCast]
        ring
      rw [e1]
      exact dvd_mul_of_dvd_right (dvd_sub (dvd_mul_of_dvd_right hy1 _) (dvd_mul_of_dvd_right hy2 _)) _
    have h1 := GlobalTheory.BKReal.SepFil.dvd_of_forall_near_OD l e O K ϖ m _ hw
    rw [pow_add, mul_assoc] at h1
    exact (((hlu.pow N).mul (hlu.pow m)).dvd_mul_left).1 (by rwa [← mul_assoc] at h1)
  have hc := ϖ.complete_OD O K
  exact hc.toIsHausdorff.haus' _ fun n => by
    simp only [Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top, SModEq.zero]
    exact Ideal.mem_span_singleton.2 (hdiv n)


omit [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NeZero e] [CompleteSpace K] in
theorem eq_zero_of_forall_dvd (x : Ahat O K l e) (h : ∀ n : ℕ, ∃ y, x = Ehat O K l e ^ n * y) : x = 0 := by
  refine AdicCompletion.ext_evalₐ fun n => ?_
  obtain ⟨y, rfl⟩ := h n
  have hE : AdicCompletion.evalₐ (idE O K l e) n (Ehat O K l e) = Ideal.Quotient.mk _ (EIn l e _) :=
    AlgHom.commutes _ _
  rw [map_mul, map_pow, hE, ← map_pow, Ideal.Quotient.eq_zero_iff_mem.2
    (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) n), zero_mul]
  exact (map_zero _).symm

theorem eq_zero_of_idem_mul_iS (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (τ : ZMod a) (s : S O K e)
    (h : idem (constC t) τ * ϖ.iS O K s = 0) : s = 0 := by
  set x := toHatS O K l e (algebraMap (S O K e) (invL l (S O K e)) s) with hx
  have h1 : idem (constD t) τ * ϖ.iHat O K x = 0 := by
    have h2 := congrArg (crisToOD l O) h
    rw [map_mul, map_zero, crisToOD_iS ϖ s] at h2
    have h3 : crisToOD l O (idem (constC t) τ) = idem (constD t) τ :=
      crisToOD_toOCr (constA t (Pi.single τ 1))
    rwa [h3] at h2
  have h4 : ϖ.iD t K (Pi.single τ x) = 0 := by
    rw [PiSys.iD, glue_apply, Finset.sum_eq_single τ (fun σ _ hσ => by
      rw [Pi.single_eq_of_ne hσ, map_zero, mul_zero]) (by simp), Pi.single_eq_same, h1]
  have h5 : x = 0 := eq_zero_of_forall_dvd x fun n => by
    obtain ⟨y, hy⟩ := GlobalTheory.BKReal.PiSys.eq_Ehat_pow_mul_of_iD_mem l a e O K t ϖ n (Pi.single τ x)
      (by rw [h4]; exact zero_mem _)
    exact ⟨y τ, by simpa using congrFun hy τ⟩
  have h6 : toHat O K l e ⟨(s : K⟦X⟧), invL_S_le_Rpi l e (le_away _ _ s.2)⟩ = 0 := h5
  have h7 := GlobalTheory.BK.toHat_injective O K l e (h6.trans (map_zero _).symm)
  have h8 : (s : K⟦X⟧) = 0 := congrArg (fun z : Rpi O K l e => (z : K⟦X⟧)) h7
  exact Subtype.ext h8

theorem iB_injective (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) : Function.Injective (ϖ.iB t K) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx => funext fun τ => ?_
  obtain ⟨k, hk⟩ := (x τ).2
  set s : S O K e := ⟨_, hk⟩
  have hs : algebraMap (S O K e) (invL l (S O K e)) s = (l : invL l (S O K e)) ^ k * x τ :=
    Subtype.ext (by simp [s])
  have h1 := idem_mul_glue (constB t) (ϖ.iSl O K) x τ
  rw [show glue (constB t) (ϖ.iSl O K) x = 0 from hx, mul_zero] at h1
  have h3 : ϖ.iSl O K (algebraMap (S O K e) (invL l (S O K e)) s) = toOB l O (ϖ.iS O K s) :=
    ϖ.iSl_of_mem O K s.2 _
  have h2 : toOB l O (idem (constC t) τ * ϖ.iS O K s) = 0 := by
    rw [map_mul, ← h3, hs, map_mul, map_pow, map_natCast]
    change idem (constB t) τ * (_ * _) = 0
    rw [mul_left_comm, ← h1, mul_zero]
  have h4 : idem (constC t) τ * ϖ.iS O K s = 0 := toOB_injective (h2.trans (map_zero _).symm)
  have h5 := eq_zero_of_idem_mul_iS t ϖ τ s h4
  have h6 : (l : invL l (S O K e)) ^ k * x τ = 0 := by rw [← hs, h5, map_zero]
  have h7 : (l : K⟦X⟧) ^ k * (x τ : K⟦X⟧) = 0 := by simpa using congrArg Subtype.val h6
  have hl0 : (l : K⟦X⟧) ≠ 0 := fun h0 => BK.l_ne_zero (K := K) l (by
    simpa using congrArg PowerSeries.constantCoeff h0)
  exact Subtype.ext ((mul_eq_zero.1 h7).resolve_left (pow_ne_zero _ hl0))

theorem iB_injective_finExt : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (LL : FinExt l)
    (t : Wq l a →ₐ[ℤ_[l]] ↥(OL LL)) (ϖ : PiSys l e), Function.Injective (ϖ.iB t ↥LL.1) :=
  fun _ _ _ _ _ _ _ t ϖ => iB_injective t ϖ

end GlobalTheory.BKReal.IBInj
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.exists_pow_mul_crisToOD_sub_toOD_dvd : ∀ (l : ℕ) [Fact l.Prime] (e : ℕ) [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (ϖ : PiSys l e) (m : ℕ), ∃ N : ℕ, ∀ z : OCr l O, ∃ y : OA l O, ϖ.iAl O K (EIn l e _) ^ m ∣ (l : OD l O) ^ N * crisToOD l O z - toOD l O y := by
  first | exact @GlobalTheory.BKReal.CrisBounded.bdd_crisToOD | exact GlobalTheory.BKReal.CrisBounded.bdd_crisToOD | (intros; apply GlobalTheory.BKReal.CrisBounded.bdd_crisToOD <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.dvd_of_forall_approx_toOD : ∀ (l : ℕ) [Fact l.Prime] (e : ℕ) [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (ϖ : PiSys l e) (m : ℕ) (w : OD l O), (∀ k : ℕ, ∃ y : OA l O, ϖ.iAl O K (EIn l e _) ^ m ∣ w - (l : OD l O) ^ k * toOD l O y) → ϖ.iAl O K (EIn l e _) ^ m ∣ w := by
  first | exact @GlobalTheory.BKReal.SepFil.dvd_of_forall_near_OD | exact GlobalTheory.BKReal.SepFil.dvd_of_forall_near_OD | (intros; apply GlobalTheory.BKReal.SepFil.dvd_of_forall_near_OD <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.exists_pow_iHat_toHatS_sub_toOD_dvd : ∀ (l : ℕ) [Fact l.Prime] (e : ℕ) [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (ϖ : PiSys l e) [CompleteSpace K] (m : ℕ) (s : S O K e), ∃ y : OA l O, ϖ.iAl O K (EIn l e _) ^ m ∣ (l : OD l O) ^ m * ϖ.iHat O K (toHatS O K l e (algebraMap (S O K e) (invL l (S O K e)) s)) - toOD l O y := by
  first | exact @GlobalTheory.BKReal.exists_l_pow_iHat_toHatS_sub_dvd | exact GlobalTheory.BKReal.exists_l_pow_iHat_toHatS_sub_dvd | (intros; apply GlobalTheory.BKReal.exists_l_pow_iHat_toHatS_sub_dvd <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.ideal_power_membership_divisible : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [CompleteSpace K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (n : ℕ) (x : ZMod a → Ahat O K l e), ϖ.iD t K x ∈ Ideal.span {ϖ.iD t K (fun _ => Ehat O K l e) ^ n} → ∃ y : ZMod a → Ahat O K l e, x = (fun _ => Ehat O K l e) ^ n * y := by
  first | exact @GlobalTheory.BKReal.PiSys.eq_Ehat_pow_mul_of_iD_mem | exact GlobalTheory.BKReal.PiSys.eq_Ehat_pow_mul_of_iD_mem | (intros; apply GlobalTheory.BKReal.PiSys.eq_Ehat_pow_mul_of_iD_mem <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations

namespace GlobalTheory.HubX.InvariantsNoJump

theorem mem_Jset_of_isJumpV (S : LocalSituation.Sit) (Y : LocLat S.G S.Qp S.LL S.O) (τ : S.K →ₐ[S.Qp] S.LL) (a : ℤ)
    (ha : IsJumpV S.PD Y.ρ τ a) : a ∈ LocalSituation.Jset S Y := by
  intro heq
  apply ha
  unfold FildR DdRE
  rw [inf_right_comm, heq, inf_right_comm]

theorem two_add_sum_jumps_le_intervalExponent (S : LocalSituation.Sit) (Y : LocLat S.G S.Qp S.LL S.O) (τ : S.K →ₐ[S.Qp] S.LL) (l m vd : ℕ)
    (hfin : (LocalSituation.Jset S Y).Finite) (h0 : ¬ IsJumpV S.PD Y.ρ τ 0) :
    2 + ∑ᶠ (u : ℤ) (_ : IsJumpV S.PD Y.ρ τ u), (m + LocalSituation.vZ l u) ≤ LocalSituation.cLL l m vd (LocalSituation.Jset S Y) 0 1 := by
  classical
  have hI : Finset.Ico (0 : ℤ) 1 = {0} := by decide
  unfold LocalSituation.cLL LocalSituation.rI
  rw [hI, Finset.sum_singleton]
  simp only [sub_zero]
  have hle : ∑ᶠ (u : ℤ) (_ : IsJumpV S.PD Y.ρ τ u), (m + LocalSituation.vZ l u) ≤
      ∑ᶠ (u : ℤ) (_ : u ∈ LocalSituation.Jset S Y) (_ : u ≠ 0), (m + LocalSituation.vZ l u) := by
    simp only [finsum_eq_if]
    rw [finsum_eq_sum_of_support_subset _ (s := hfin.toFinset) ?_,
      finsum_eq_sum_of_support_subset _ (s := hfin.toFinset) ?_]
    rotate_left
    all_goals try
      intro u hu
      rw [Set.Finite.coe_toFinset]
      by_contra hn
      have hn' : ¬ IsJumpV S.PD Y.ρ τ u := fun hj => hn (mem_Jset_of_isJumpV S Y τ u hj)
      apply hu
      simp [hn, hn']
    apply Finset.sum_le_sum
    · intro u _
      by_cases hj : IsJumpV S.PD Y.ρ τ u
      · have hu0 : u ≠ 0 := by rintro rfl; exact h0 hj
        simp only [if_pos hj, if_pos (mem_Jset_of_isJumpV S Y τ u hj), if_pos hu0, le_refl]
      · simp only [if_neg hj]
        exact Nat.zero_le _
  omega

end GlobalTheory.HubX.InvariantsNoJump

namespace GlobalTheory.HubX.InvariantsNoJump

theorem torsion_exponent_kills_invariants_no_jump_zero : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let S := LocalSituation.sit D.loc HW l (D.locA l) K s LL h; ∀ (M0 h0 : ℕ) (T : LocLat S.G S.Qp S.LL S.O), LocalSituation.HypW S ((F l).E K s LL h).tie T M0 h0 → (∀ τ, ¬ IsJumpV S.PD T.ρ τ 0) → ∀ x : T.V ⧸ T.L.T, (∀ g, actD T.L g x = x) → ((LocalSituation.ell S : S.O) ^ GlobalTheory.HubX.invariantsCountConstant D.loc HW D.locA l K s LL h M0 h0 T) • x = 0 := by
  intro _ _ _ D HW F _ l _ K s LL h S M0 h0 T hW hJ x hx
  have hat := GlobalTheory.T.invariants_vanish_at_prime_of_admissible D HW F (GlobalTheory.Per.FontaineAll.fontaine_bounds D) l K s LL h
  have hp : LocalSituation.ell S = l := (D.loc l).PD_p K
  have hs : S.W.s = s := (HW l).W_s K s LL h
  have hcard := Formalism.MainNotions.N.JsetEmb.card_emb_good h
  have hpos : 0 < Nat.card (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) := by
    haveI : FiniteDimensional ℚ_[l] ↥K.1 := K.2
    rw [hcard]; exact Module.finrank_pos
  obtain ⟨τ⟩ := (Nat.card_pos_iff.1 hpos).1
  have key := hat M0 h0 T τ hW (hJ τ) x hx
  have hfin : (LocalSituation.Jset S T).Finite :=
    (Set.finite_Icc (-(M0 : ℤ)) h0).subset fun a ha => hW.2.1 a ha
  have hle : LocalSituation.c0 S T τ M0 h0 ≤ GlobalTheory.HubX.invariantsCountConstant D.loc HW D.locA l K s LL h M0 h0 T := by
    unfold LocalSituation.c0
    rw [hp, hs]
    exact two_add_sum_jumps_le_intervalExponent S T τ l _ _ hfin (hJ τ)
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
  rw [hk, pow_add, mul_comm, mul_smul, key, smul_zero]

end GlobalTheory.HubX.InvariantsNoJump
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.isDeltaRingHom_of_dense_deltaCommuteLocus : ∀ (l : ℕ) [Fact l.Prime] (Q : Type) [CommRing Q] (C : Type) [CommRing C] (D : Delta l Q) (DC : Delta l C) (J : Ideal Q) (JC : Ideal C) (h : Q →+* C), (l : Q) ∈ J → J.map h ≤ JC → IsHausdorff JC C → (∀ (x : Q) (n : ℕ), ∃ a ∈ δLocus D DC h, x - a ∈ J ^ n) → IsδMap D DC h := by
  first | exact @GlobalTheory.isδMap_of_dense_δLocus | exact GlobalTheory.isδMap_of_dense_δLocus | (intros; apply GlobalTheory.isδMap_of_dense_δLocus <;> assumption)
end
