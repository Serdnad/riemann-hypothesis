module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaussNormCoeffWittDisc
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle555
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle490
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle330
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle336
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle005
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle014
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle113
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle573
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle136
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle157
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeEqFiltrationSumAtLevel
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeEqStdPowerSeriesAtZero
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle569
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle501
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import ReciprocityTheory.GaloisValuations.GlobalA
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHalfOfBasePins
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle181
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.DiscSer

variable (l : ℕ) {W : Type} [CommRing W] (ρ : ℝ≥0)

def shiftX (s : W⟦X⟧) : W⟦X⟧ := PowerSeries.mk fun n => coeff (n + 1) s

theorem coeff_shiftX (s : W⟦X⟧) (n : ℕ) : coeff n (shiftX s) = coeff (n + 1) s := coeff_mk _ _

theorem X_mul_shiftX (s : W⟦X⟧) : X * shiftX s = s - C (coeff 0 s) := by
  ext n
  rcases n with _ | n
  · simp
  · rw [coeff_succ_X_mul, coeff_shiftX, map_sub, coeff_C]; simp

theorem eq_zero_of_X_mul_eq_zero {t : W⟦X⟧} (h : X * t = 0) : t = 0 := by
  ext n
  have := congrArg (coeff (n + 1)) h
  rwa [coeff_succ_X_mul, map_zero] at this

theorem exists_rep (y : PreDisc l (X : W⟦X⟧) ρ) : ∃ (c : ℕ) (s : W⟦X⟧),
    y = algebraMap _ _ s * IsLocalization.Away.invSelf (S := PreDisc l (X : W⟦X⟧) ρ) (l : W⟦X⟧) ^ c := by
  obtain ⟨c, s, hs⟩ := IsLocalization.Away.surj (l : W⟦X⟧) y
  exact ⟨c, s, by rw [← hs, mul_assoc, ← mul_pow, IsLocalization.Away.mul_invSelf, one_pow, mul_one]⟩

theorem aPre_rep (n c : ℕ) (s : W⟦X⟧) :
    aPre l ρ n (algebraMap _ (PreDisc l (X : W⟦X⟧) ρ) s *
      IsLocalization.Away.invSelf (S := PreDisc l (X : W⟦X⟧) ρ) (l : W⟦X⟧) ^ c) =
      algebraMap W (PreDisc l (0 : W) 1) (coeff n s) *
        IsLocalization.Away.invSelf (S := PreDisc l (0 : W) 1) (l : W) ^ c := by
  rw [aPre_apply, map_mul, phi_alg, map_pow, phi_inv, ← map_pow, coeff_mul_C, coeff_map]

theorem eq_zero_of_X_mul (z : PreDisc l (X : W⟦X⟧) ρ)
    (h : algebraMap _ (PreDisc l (X : W⟦X⟧) ρ) (X : W⟦X⟧) * z = 0) : z = 0 := by
  obtain ⟨c, t, rfl⟩ := exists_rep l ρ z
  have hu : IsUnit (IsLocalization.Away.invSelf (S := PreDisc l (X : W⟦X⟧) ρ) (l : W⟦X⟧)) :=
    IsUnit.of_mul_eq_one_right (algebraMap _ _ (l : W⟦X⟧)) (IsLocalization.Away.mul_invSelf _)
  rw [← mul_assoc, ← map_mul] at h
  have h2 : algebraMap _ (PreDisc l (X : W⟦X⟧) ρ) (X * t) = 0 := (hu.pow c).mul_left_eq_zero.1 h
  obtain ⟨⟨m, hm⟩, hm'⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers (l : W⟦X⟧)) _ _).1 h2
  obtain ⟨k, rfl⟩ := hm
  have h3 : (l : W⟦X⟧) ^ k * t = 0 :=
    eq_zero_of_X_mul_eq_zero (by rw [mul_left_comm]; exact hm')
  have h4 : algebraMap _ (PreDisc l (X : W⟦X⟧) ρ) t = 0 := by
    have h5 := congrArg (algebraMap _ (PreDisc l (X : W⟦X⟧) ρ)) h3
    rw [map_mul, map_zero] at h5
    rw [map_pow] at h5
    exact ((IsLocalization.Away.algebraMap_isUnit (S := PreDisc l (X : W⟦X⟧) ρ) (l : W⟦X⟧)).pow k).mul_right_eq_zero.1 h5
  rw [h4, zero_mul]

abbrev c0 (y : PreDisc l (X : W⟦X⟧) ρ) : PreDisc l (X : W⟦X⟧) ρ :=
  preMap l (0 : W) 1 (X : W⟦X⟧) ρ C (aPre l ρ 0 y)

theorem X_mul_rep (c : ℕ) (s : W⟦X⟧) :
    algebraMap _ (PreDisc l (X : W⟦X⟧) ρ) (X : W⟦X⟧) * (algebraMap _ _ (shiftX s) *
      IsLocalization.Away.invSelf (S := PreDisc l (X : W⟦X⟧) ρ) (l : W⟦X⟧) ^ c) =
    algebraMap _ _ s * IsLocalization.Away.invSelf (S := PreDisc l (X : W⟦X⟧) ρ) (l : W⟦X⟧) ^ c -
      c0 l ρ (algebraMap _ _ s * IsLocalization.Away.invSelf (S := PreDisc l (X : W⟦X⟧) ρ) (l : W⟦X⟧) ^ c) := by
  rw [c0, aPre_rep, map_mul, preMap_alg, map_pow, preMap_inv, ← mul_assoc, ← map_mul, X_mul_shiftX, map_sub,
    sub_mul]

def dFun (y : PreDisc l (X : W⟦X⟧) ρ) : PreDisc l (X : W⟦X⟧) ρ :=
  algebraMap _ _ (shiftX (exists_rep l ρ y).choose_spec.choose) *
    IsLocalization.Away.invSelf (S := PreDisc l (X : W⟦X⟧) ρ) (l : W⟦X⟧) ^ (exists_rep l ρ y).choose

theorem X_mul_dFun (y : PreDisc l (X : W⟦X⟧) ρ) :
    algebraMap _ (PreDisc l (X : W⟦X⟧) ρ) (X : W⟦X⟧) * dFun l ρ y = y - c0 l ρ y := by
  have hy := (exists_rep l ρ y).choose_spec.choose_spec
  rw [dFun, X_mul_rep, ← hy]

theorem dFun_eq (y z : PreDisc l (X : W⟦X⟧) ρ)
    (h : algebraMap _ (PreDisc l (X : W⟦X⟧) ρ) (X : W⟦X⟧) * z = y - c0 l ρ y) : dFun l ρ y = z :=
  sub_eq_zero.1 (eq_zero_of_X_mul l ρ _ (by rw [mul_sub, X_mul_dFun, h, sub_self]))

theorem dFun_rep (c : ℕ) (s : W⟦X⟧) :
    dFun l ρ (algebraMap _ _ s * IsLocalization.Away.invSelf (S := PreDisc l (X : W⟦X⟧) ρ) (l : W⟦X⟧) ^ c) =
      algebraMap _ _ (shiftX s) * IsLocalization.Away.invSelf (S := PreDisc l (X : W⟦X⟧) ρ) (l : W⟦X⟧) ^ c :=
  dFun_eq l ρ _ _ (X_mul_rep l ρ c s)

def DPre : PreDisc l (X : W⟦X⟧) ρ →+ PreDisc l (X : W⟦X⟧) ρ :=
  AddMonoidHom.mk' (dFun l ρ) fun y z => dFun_eq l ρ _ _ (by
    rw [mul_add, X_mul_dFun, X_mul_dFun, c0, c0, c0, map_add (f := _), map_add (f := _)]; abel)

theorem DPre_apply (y : PreDisc l (X : W⟦X⟧) ρ) : DPre l ρ y = dFun l ρ y := rfl

theorem aPre_DPre (n : ℕ) (y : PreDisc l (X : W⟦X⟧) ρ) : aPre l ρ n (DPre l ρ y) = aPre l ρ (n + 1) y := by
  obtain ⟨c, s, rfl⟩ := exists_rep l ρ y
  rw [DPre_apply, dFun_rep, aPre_rep, aPre_rep, coeff_shiftX]

theorem norm_DPre_le [Fact l.Prime] (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (y : PreDisc l (X : W⟦X⟧) ρ) :
    ‖DPre l ρ y‖ ≤ (ρ : ℝ)⁻¹ * ‖y‖ := by
  have hl : 0 < l := (Fact.out : l.Prime).pos
  have hρ : (0 : ℝ) < ρ := by exact_mod_cast hρ0
  refine norm_le_of_aPre l ρ hρ0 hρ1 _ _ (by positivity) fun n => ?_
  rw [aPre_DPre, inv_mul_eq_div, le_div_iff₀ hρ, mul_assoc, ← pow_succ]
  exact norm_aPre_le l ρ hl hρ1.le y (n + 1)

theorem continuous_DPre [Fact l.Prime] (hρ0 : 0 < ρ) (hρ1 : ρ < 1) : Continuous (DPre l ρ (W := W)) :=
  AddMonoidHomClass.continuous_of_bound _ _ (norm_DPre_le l ρ hρ0 hρ1)

theorem exists_const_add_X_mul [Fact l.Prime] (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (κ : Disc l (0 : W) 1 →+* Disc l (X : W⟦X⟧) ρ) (hκ : IsDiscMap (l := _) (u := _) (ρ := _) (C : W →+* W⟦X⟧) κ)
    (x : Disc l (X : W⟦X⟧) ρ) :
    ∃ (c : Disc l (0 : W) 1) (x₁ : Disc l (X : W⟦X⟧) ρ), x = κ c + toDisc l (X : W⟦X⟧) ρ X * x₁ := by
  have hl : 0 < l := (Fact.out : l.Prime).pos
  let A0 := (aPre l ρ 0 (W := W)).completion (continuous_aPre l ρ hl hρ0 hρ1.le 0)
  let D := (DPre l ρ (W := W)).completion (continuous_DPre l ρ hρ0 hρ1)
  have hA : ∀ y, A0 (ofPre l (X : W⟦X⟧) ρ y) = ofPre l (0 : W) 1 (aPre l ρ 0 y) := fun y =>
    AddMonoidHom.completion_coe _ _ y
  have hD : ∀ y, D (ofPre l (X : W⟦X⟧) ρ y) = ofPre l (X : W⟦X⟧) ρ (DPre l ρ y) := fun y =>
    AddMonoidHom.completion_coe _ _ y
  have hκc : Continuous κ :=
    AddMonoidHomClass.continuous_of_bound _ 1 fun y => (hκ.norm_le y).trans (one_mul _).ge
  have e : κ.comp (ofPre l (0 : W) 1) = (ofPre l (X : W⟦X⟧) ρ).comp (preMap l (0 : W) 1 (X : W⟦X⟧) ρ C) :=
    IsLocalization.ringHom_ext (Submonoid.powers (l : W)) (RingHom.ext fun a => by
      simp only [RingHom.comp_apply]; rw [preMap_alg]; exact hκ.ext a)
  refine ⟨A0 x, D x, ?_⟩
  refine (denseRange_ofPre l (X : W⟦X⟧) ρ).induction_on x
    (isClosed_eq continuous_id ((hκc.comp (AddMonoidHom.continuous_completion _ _)).add
      (continuous_const.mul (AddMonoidHom.continuous_completion _ _)))) fun y => ?_
  rw [hA, hD, show κ (ofPre l (0 : W) 1 (aPre l ρ 0 y)) = _ from RingHom.congr_fun e _, RingHom.comp_apply,
    show toDisc l (X : W⟦X⟧) ρ X = ofPre l (X : W⟦X⟧) ρ (algebraMap _ _ X) from rfl, ← map_mul, ← map_add,
    DPre_apply, X_mul_dFun]
  congr 1
  abel

end GlobalTheory.BSP.DiscSer

namespace GlobalTheory.BSP

theorem exists_const_add_X_mul_disc : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (ρ : ℝ≥0), 0 < ρ → ρ < 1 →
    ∀ (κ : Disc l (0 : Wq l bk.a) 1 →+* bk.DS ρ), IsDiscMap (l := _) (u := _) (ρ := _) (C : Wq l bk.a →+* bk.S) κ →
    ∀ x : bk.DS ρ, ∃ (c : Disc l (0 : Wq l bk.a) 1) (x₁ : bk.DS ρ), x = κ c + toDisc l (X : bk.S) ρ X * x₁ :=
  fun l _ _ _ ρ hρ0 hρ1 κ hκ x => DiscSer.exists_const_add_X_mul l ρ hρ0 hρ1 κ hκ x

end GlobalTheory.BSP
end
end

section

noncomputable section

open GlobalTheory.GLq GlobalTheory.Published Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

namespace GlobalTheory.GreenRegularCharactersInertiaEigenvalues

variable {g : ℕ} [Fact g.Prime]

theorem isPrimeLab_pos {e : ℕ} {P : (ZMod g)[X]} (h : IsPrimeLab e P) : 0 < e := by
  have := degree_pos_of_irreducible h.2.1
  rw [← h.2.2.2]
  exact natDegree_pos_iff_degree_pos.mpr this

theorem family (g : ℕ) [Fact g.Prime] (e : ℕ) (he : 0 < e) (K : Type) [Field K] [Algebra (ZMod g) K]
    (hK : Module.finrank (ZMod g) K = e) (τ : (Kˣ →* ℂˣ) → Gn g e → ℂ)
    (h1 : ∀ θ, IsRegularChar g e θ → IsCusp (τ θ))
    (h2 : ∀ θ θ', IsRegularChar g e θ → IsRegularChar g e θ' → (τ θ = τ θ' ↔ ∃ i < e, θ' = θ ^ g ^ i)) :
    ∃ L : (ZMod g)[X] → Gn g e → ℂ,
      (∀ P, IsPrimeLab e P → IsCusp (L P) ∧ ∃ θ, IsRegularChar g e θ ∧ L P = τ θ) ∧
      ∀ P P', IsPrimeLab e P → IsPrimeLab e P' → L P = L P' → P = P' := by
  obtain ⟨c, hc1, hc2⟩ := GlobalTheory.T.monicIrreducible_inject_regularCharacterOrbits g e he K hK
  refine ⟨fun P => τ (c P), fun P hP => ⟨h1 _ (hc1 P hP), c P, hc1 P hP, rfl⟩, ?_⟩
  intro P P' hP hP' h
  exact hc2 P P' hP hP' ((h2 _ _ (hc1 P hP) (hc1 P' hP')).mp h)

theorem factor_lab {f : (ZMod g)[X]} (h0 : f.coeff 0 ≠ 0) :
    ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors f, IsPrimeLab P.natDegree P := by
  intro P hP
  have hirr := UniqueFactorizationMonoid.irreducible_of_normalized_factor P hP
  have hmon : P.Monic := by
    rw [← UniqueFactorizationMonoid.normalize_normalized_factor P hP]
    exact monic_normalize hirr.ne_zero
  refine ⟨hmon, hirr, ?_, rfl⟩
  intro hc
  have : (X : (ZMod g)[X]) ∣ f :=
    (X_dvd_iff.mpr hc).trans (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hP)
  exact h0 (X_dvd_iff.mp this)

theorem prod_factors {f : (ZMod g)[X]} (hf : f.Monic) (h0 : f.coeff 0 ≠ 0) :
    (UniqueFactorizationMonoid.normalizedFactors f).prod = f := by
  have hm : ((UniqueFactorizationMonoid.normalizedFactors f).prod).Monic := by
    have := monic_multiset_prod_of_monic (UniqueFactorizationMonoid.normalizedFactors f) id
      (fun P hP => (factor_lab h0 P hP).1)
    simpa using this
  exact eq_of_monic_of_associated hm hf (UniqueFactorizationMonoid.prod_normalizedFactors hf.ne_zero)

theorem count (d : ℕ) (hd : 0 < d) (Lf : ∀ e, (ZMod g)[X] → Gn g e → ℂ)
    (hc : ∀ e P, IsPrimeLab e P → IsCusp (Lf e P))
    (hi : ∀ e P P', IsPrimeLab e P → IsPrimeLab e P' → Lf e P = Lf e P' → P = P')
    (χ : Gn g d → ℂ) (hχ : IsCusp χ) (hne : ∀ P, IsPrimeLab d P → Lf d P ≠ χ) : False := by
  let s : Set (ZMod g)[X] := {P | IsPrimeLab P.natDegree P}
  let φ : (ZMod g)[X] → Pc g := fun P => ⟨P.natDegree, Lf P.natDegree P⟩
  have hinj : Set.InjOn φ s := by
    intro P hP P' hP' h
    have h1 : P.natDegree = P'.natDegree := congrArg Sigma.fst h
    have h2 : (⟨P'.natDegree, Lf P'.natDegree P'⟩ : Pc g) = ⟨P.natDegree, Lf P.natDegree P'⟩ := by rw [h1]
    have h3 : Lf P.natDegree P = Lf P.natDegree P' := sigma_mk_injective (h.trans h2)
    have hP'' : IsPrimeLab P.natDegree P' := by rw [h1]; exact hP'
    exact hi _ P P' hP hP'' h3
  let ψ : Pc g → (ZMod g)[X] := Function.invFunOn φ s
  have hleft : ∀ P ∈ s, ψ (φ P) = P := fun P hP => hinj.leftInvOn_invFunOn hP
  let T : Set (ZMod g)[X] := {f | f.Monic ∧ f.natDegree = d ∧ f.coeff 0 ≠ 0}
  obtain ⟨hcard, hfin⟩ := GlobalTheory.T.ncard_monic_natDegree_coeff_zero_ne_zero g d hd
  let F : (ZMod g)[X] → Multiset (Pc g) := fun f => (UniqueFactorizationMonoid.normalizedFactors f).map φ
  have hback : ∀ f ∈ T, (F f).map ψ = UniqueFactorizationMonoid.normalizedFactors f := by
    intro f hf
    simp only [F, Multiset.map_map]
    conv_rhs => rw [← Multiset.map_id (UniqueFactorizationMonoid.normalizedFactors f)]
    exact Multiset.map_congr rfl (fun P hP => hleft P (factor_lab hf.2.2 P hP))
  have hFinj : Set.InjOn F T := by
    intro f hf f' hf' h
    have := congrArg (fun M => (M.map ψ).prod) h
    simp only [hback f hf, hback f' hf'] at this
    rwa [prod_factors hf.1 hf.2.2, prod_factors hf'.1 hf'.2.2] at this
  have hnot : ({⟨d, χ⟩} : Multiset (Pc g)) ∉ hfin.toFinset.image F := by
    intro hmem
    obtain ⟨f, hf, hfe⟩ := Finset.mem_image.mp hmem
    rw [Set.Finite.mem_toFinset] at hf
    have hnf := hback f hf
    rw [hfe, Multiset.map_singleton] at hnf
    have hPmem : ψ ⟨d, χ⟩ ∈ UniqueFactorizationMonoid.normalizedFactors f := by
      rw [← hnf]; exact Multiset.mem_singleton_self _
    have hPl := factor_lab hf.2.2 _ hPmem
    have hφ : φ (ψ ⟨d, χ⟩) = ⟨d, χ⟩ := by
      have := hfe
      simp only [F] at this
      rw [← hnf, Multiset.map_singleton, Multiset.singleton_inj] at this
      exact this
    set P := ψ ⟨d, χ⟩ with hPdef
    have hdeg : P.natDegree = d := congrArg Sigma.fst hφ
    have h2 : (⟨d, Lf d P⟩ : Pc g) = ⟨P.natDegree, Lf P.natDegree P⟩ := by rw [hdeg]
    have h3 : Lf d P = χ := sigma_mk_injective (h2.trans hφ)
    have hPl' : IsPrimeLab d P := by rw [← hdeg]; exact hPl
    exact hne P hPl' h3
  let S : Finset (Multiset (Pc g)) := insert {⟨d, χ⟩} (hfin.toFinset.image F)
  have hS : ∀ M ∈ S, (M.map fun p => p.1).sum = d ∧ ∀ p ∈ M, IsCusp p.2 := by
    intro M hM
    rcases Finset.mem_insert.mp hM with rfl | hM
    · refine ⟨by simp, ?_⟩
      intro p hp
      rw [Multiset.mem_singleton] at hp
      subst hp
      exact hχ
    · obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hM
      rw [Set.Finite.mem_toFinset] at hf
      refine ⟨?_, ?_⟩
      · simp only [F, Multiset.map_map]
        have hdeg := natDegree_multiset_prod_of_monic (UniqueFactorizationMonoid.normalizedFactors f)
          (fun P hP => (factor_lab hf.2.2 P hP).1)
        rw [prod_factors hf.1 hf.2.2, hf.2.1] at hdeg
        rw [hdeg]
        rfl
      · intro p hp
        obtain ⟨P, hP, rfl⟩ := Multiset.mem_map.mp hp
        exact hc _ P (factor_lab hf.2.2 P hP)
  have hle := GlobalTheory.T.card_cuspidal_multisets_total_degree_le g d hd S hS
  have hcardS : S.card = g ^ d - g ^ (d - 1) + 1 := by
    rw [Finset.card_insert_of_notMem hnot, Finset.card_image_of_injOn, ← hcard,
      Set.ncard_eq_toFinset_card T hfin]
    rw [Set.Finite.coe_toFinset]
    exact hFinj
  omega

end GlobalTheory.GreenRegularCharactersInertiaEigenvalues


open GlobalTheory.GreenRegularCharactersInertiaEigenvalues in
theorem GlobalTheory.greenRegularCharacters_holds : GreenRegularCharacters := by
  intro g _ d hd K _ _ hK
  obtain ⟨τ, hτ1, hτ2⟩ := GlobalTheory.T.exists_cuspidalCharacter_of_regularCharacter_GLn g d hd K hK
  refine ⟨τ, hτ1, hτ2, ?_⟩
  have hex : ∀ e, ∃ L : (ZMod g)[X] → Gn g e → ℂ,
      (∀ P, IsPrimeLab e P → IsCusp (L P)) ∧
      (∀ P P', IsPrimeLab e P → IsPrimeLab e P' → L P = L P' → P = P') ∧
      (∀ _ : e = d, ∀ P, IsPrimeLab e P → ∃ θ, IsRegularChar g d θ ∧ (⟨e, L P⟩ : Pc g) = ⟨d, τ θ⟩) := by
    intro e
    by_cases hed : e = d
    · subst hed
      obtain ⟨L, hL1, hL2⟩ := family g e hd K hK τ (fun θ hθ => (hτ1 θ hθ).1) hτ2
      refine ⟨L, fun P hP => (hL1 P hP).1, hL2, fun _ P hP => ?_⟩
      obtain ⟨θ, hθ, he⟩ := (hL1 P hP).2
      exact ⟨θ, hθ, by rw [he]⟩
    · by_cases he0 : e = 0
      · refine ⟨fun _ _ => 0, fun P hP => absurd (isPrimeLab_pos hP) (by omega),
          fun P _ hP _ _ => absurd (isPrimeLab_pos hP) (by omega), fun h => absurd h hed⟩
      · have hpos : 0 < e := Nat.pos_of_ne_zero he0
        obtain ⟨τ', hτ'1, hτ'2⟩ := GlobalTheory.T.exists_cuspidalCharacter_of_regularCharacter_GLn g e hpos (GaloisField g e) (GaloisField.finrank g he0)
        obtain ⟨L, hL1, hL2⟩ := family g e hpos (GaloisField g e) (GaloisField.finrank g he0) τ'
          (fun θ hθ => (hτ'1 θ hθ).1) hτ'2
        exact ⟨L, fun P hP => (hL1 P hP).1, hL2, fun h => absurd h hed⟩
  choose Lf hc hi hdd using hex
  intro χ hχ
  by_contra hno
  push_neg at hno
  refine count d hd Lf hc hi χ hχ ?_
  intro P hP heq
  obtain ⟨θ, hθ, hs⟩ := hdd d rfl P hP
  have : Lf d P = τ θ := sigma_mk_injective hs
  exact hno θ hθ (heq ▸ this)

end
end

section

noncomputable section

open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.Published

theorem chebotarevDegreeOne' : ChebotarevDegreeOne := by
  intro F Ω _ _ _ _ _ L _ _ g S hS
  have : IsGalois F Ω := {}
  obtain ⟨g', rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := F) (K₁ := L) Ω g
  have : NumberField L := NumberField.of_module_finite F L
  obtain ⟨m, hm, hdvd, hirr⟩ := GlobalTheory.T.exists_prime_dvd_sub_one_cyclotomic_irreducible_over L (Module.finrank F L) Module.finrank_pos.ne'
  obtain ⟨Z, τ, hZ, hZirr, hcross⟩ := GlobalTheory.T.exists_cyclotomic_crossing_field_deciding_frobenius F Ω L g' m hm hdvd hirr
  have : NumberField Z := NumberField.of_module_finite F Z
  have : IsAlgClosure Z Ω := ⟨IsAlgClosure.isAlgClosed F, inferInstance⟩
  have hfin := hS.union (GlobalTheory.T.finite_places_inertia_not_fixing_finiteExtension F Ω L)
  let u : HeightOneSpectrum (𝓞 Z) → HeightOneSpectrum (𝓞 F) := fun w => w.under (𝓞 F)
  have hu : ∀ w : HeightOneSpectrum (𝓞 Z), w.asIdeal.LiesOver (u w).asIdeal := fun w => ⟨rfl⟩
  have hfin' : (u ⁻¹' (S ∪ {v | ∃ B : ValuationSubring Ω, IsPlaceOver B v ∧
      ¬ Ine (F := F) B ≤ L.fixingSubgroup})).Finite := by
    refine hfin.preimage' fun v _ => ?_
    have := v.isMaximal
    refine ((IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 Z)).preimage
      (f := fun w : HeightOneSpectrum (𝓞 Z) => w.asIdeal) (fun a _ b _ h => HeightOneSpectrum.ext h)).subset ?_
    rintro w rfl
    exact ⟨w.isPrime, hu w⟩
  obtain ⟨w, hw, hp, hτ⟩ := GlobalTheory.T.exists_prime_absNorm_eq_of_irreducible_cyclotomic' Z m hm hZirr τ _ hfin'
  obtain ⟨B, hB⟩ := exists_isPlaceOver Ω w
  obtain ⟨σ, hσ⟩ := exists_isFrob hB
  obtain ⟨hN, hBv, hσv⟩ := GlobalTheory.T.isFrob_restrictScalars_of_prime_absNorm' F Ω Z w (u w) (hu w) hp B hB σ hσ
  simp only [Set.mem_preimage, Set.mem_union, not_or, Set.mem_ofPred_eq, not_exists, not_and, not_not] at hw
  refine ⟨u w, hw.1, ((GlobalTheory.absNorm_prime_iff_inertiaDeg_eq_one_and_finite_ramified F).1 _).1 (hN ▸ hp),
    B, hBv, hw.2 B hBv, σ.restrictScalars F, hσv, ?_⟩
  have hmw : ((m : ℕ) : 𝓞 Z) ∉ w.asIdeal := by
    intro h
    have : Fact m.Prime := ⟨hm⟩
    have h1 : Ideal.absNorm w.asIdeal ∣ m ^ Module.finrank ℤ (𝓞 Z) := by
      rw [← Ideal.absNorm_span_natCast]
      exact Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).2 h)
    have h2 := (Nat.prime_dvd_prime_iff_eq hp hm).1 (hp.dvd_of_dvd_pow h1)
    rw [h2, ZMod.natCast_self] at hτ
    exact τ.ne_zero hτ.symm
  have key := hcross (σ.restrictScalars F) (fun x => σ.commutes x) fun ζ hζ => by
    have hq : ζ ^ (τ : ZMod m).val = ζ ^ normV w := by
      rw [← hτ, ZMod.val_natCast]
      simpa only [normV, Ideal.absNorm_eq_natCard] using
        (pow_eq_pow_mod (Ideal.absNorm w.asIdeal) hζ).symm
    rw [hq]
    have h1 := not_valuation_lt_one_of_isPlaceOver hmw hB 1
    rw [pow_one] at h1
    refine eq_of_pow_eq_one B h1 ?_ ?_ (hσ.2 ζ (valuation_eq_one_of_pow_eq_one B hm.ne_zero hζ).le)
    · rw [← map_pow, hζ, map_one]
    · rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow]
  rwa [← IntermediateField.restrictNormalHom_ker, MonoidHom.mem_ker, map_mul, map_inv,
    mul_inv_eq_one] at key

theorem cheb_holds : GlobalTheory.TwSys.Cheb :=
  chebotarevDegreeOne_iff_cheb.1 chebotarevDegreeOne'

end GlobalTheory.Published

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct

namespace GlobalTheory.Per.SESJumps

theorem isJumpV_iff_of_isSESLat : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (T₀ T₁ T₂ : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (ι : LatHom T₀.L T₁.L) (π : LatHom T₁.L T₂.L), IsSESLat (Qp := ℚ_[l]) ι π → IsCrys (P.PD K) T₀.ρ → IsCrys (P.PD K) T₁.ρ → IsCrys (P.PD K) T₂.ρ → ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ), IsJumpV (P.PD K) T₁.ρ τ a ↔ IsJumpV (P.PD K) T₀.ρ τ a ∨ IsJumpV (P.PD K) T₂.ρ τ a := by
  intro l _ P AI hT K LL T₀ T₁ T₂ ι π hS _ h₁ _ τ a
  obtain ⟨hi, hs, -, hex, -⟩ := hS
  have hrk : LinearMap.range ι.f = LinearMap.ker π.f := by
    ext x
    rw [LinearMap.mem_range, LinearMap.mem_ker]
    exact (hex x).symm
  have hDR := (GlobalTheory.Per.CrisDR.isDR_of_isCrys l P AI hT K LL T₁.V T₁.ρ h₁).1
  exact ((GlobalTheory.T.de_rham_representation_tensor_comparison l P AI hT K LL T₀.V T₀.ρ T₁.V T₁.ρ T₂.V T₂.ρ ι.f π.f ι.equiv π.equiv
    hi hs hrk hDR).2.2 τ a).2.2

end GlobalTheory.Per.SESJumps
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL

theorem _root_.GlobalTheory.T.wach_lattice_eq_filtration_sum_at_level : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; let C := Cm l; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ (i : Let K) (ζ : ↥LL.1) τ, Pt (HW l) h i ζ τ → ∀ f : ℤ → T.V ⊗[ℚ_[l]] (D.loc l).R.B, f ∈ Lat C h T i ζ ↔ (∃ m : ℤ, ∀ k < m, f k = 0) ∧ ∀ k : ℤ, f k ∈ Di (HW l) h T i ∧ ιV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V) (f k) ∈ FilAt ((D.loc l).PD K) T τ (-k) := by
  first | exact @GlobalTheory.NL.LatFil.lat_eq_fil | exact GlobalTheory.NL.LatFil.lat_eq_fil | (intros; apply GlobalTheory.NL.LatFil.lat_eq_fil <;> assumption)
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL

theorem _root_.GlobalTheory.T.wach_lattice_eq_std_powerSeries_at_zero : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; let C := Cm l; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ i : Let K, Std (Di (HW l) h T i) (Lat C h T i 1) := by
  first | exact @GlobalTheory.NL.AtZero.lat_one_std | exact GlobalTheory.NL.AtZero.lat_one_std | (intros; apply GlobalTheory.NL.AtZero.lat_one_std <;> assumption)
end

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.Member GlobalTheory.CoverHalf Formalism.IndefR.FWT Formalism.L2.DIV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.UnivCover


theorem _root_.GlobalTheory.T.openKernel_ideleCharacter_trivial_finitePart_one : ∀ (D : D7) {A : Type} [Group A] (χ : (AE D)ˣ →* A), IsOpen (χ.ker : Set (AE D)ˣ) → ∀ x : (AE D)ˣ, finPart D (x : AE D) = 1 → χ x = 1 := by
  first | exact @GlobalTheory.UnivCover.OpenKerChar.map_eq_one_of_finPart_eq_one | exact GlobalTheory.UnivCover.OpenKerChar.map_eq_one_of_finPart_eq_one | (intros; apply GlobalTheory.UnivCover.OpenKerChar.map_eq_one_of_finPart_eq_one <;> assumption)
end
