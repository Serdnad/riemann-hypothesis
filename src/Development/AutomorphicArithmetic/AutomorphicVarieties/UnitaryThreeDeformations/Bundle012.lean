module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IsHostFrame
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle008
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle062
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.IsUnitOrIsUnitOfAddOne
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IsCharZeroPt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.FinCrit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.Bundle007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.DiagEq
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.WPresEx
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.Bundle011
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle004
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.AffineMonoid.Basic
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle003
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CohDimTwoLocalOfLocalFiniteness
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Log.Base
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Mathlib.Tactic.TypeStar
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open IsLocalRing UpperTheory.V.Alg

private theorem norm_le_one_of_int (l : ℕ) [Fact l.Prime] (x : PadicAlgCl l) (hx : IsIntegral ℤ_[l] x) :
    ‖x‖ ≤ 1 :=
  _root_.UpperTheory.Reformulated.B.NormLeOneOfIsIntegral.norm_le_one_of_isIntegral l x hx

set_option linter.overlappingInstances false in
private theorem norm_abs (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [Algebra O (PadicAlgCl l)] [IsScalarTower ℤ_[l] O (PadicAlgCl l)]
    (a : O) (ha : a ≠ 0) :
    ‖algebraMap O (PadicAlgCl l) a‖ ^ (UpperTheory.V.Base.eO l O).toNat =
      ((l : ℝ)⁻¹) ^ (IsDiscreteValuationRing.addVal O a).toNat := by
  have hle : ∀ x : O, ‖algebraMap O (PadicAlgCl l) x‖ ≤ 1 := fun x =>
    norm_le_one_of_int l _ ((Algebra.IsIntegral.isIntegral (R := ℤ_[l]) x).algebraMap)
  have hu : ∀ u : Oˣ, ‖algebraMap O (PadicAlgCl l) (u : O)‖ = 1 := by
    intro u
    have h1 : ‖algebraMap O (PadicAlgCl l) (u : O)‖ * ‖algebraMap O (PadicAlgCl l) ((u⁻¹ : Oˣ) : O)‖ = 1 := by
      rw [← norm_mul, ← map_mul, Units.mul_inv]; simp
    have h2 := hle u
    have h3 := hle (u⁻¹ : Oˣ)
    have h4 := norm_nonneg (algebraMap O (PadicAlgCl l) (u : O))
    nlinarith
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have key : ∀ x : O, x ≠ 0 → ‖algebraMap O (PadicAlgCl l) x‖ =
      ‖algebraMap O (PadicAlgCl l) ϖ‖ ^ (IsDiscreteValuationRing.addVal O x).toNat := by
    intro x hx
    obtain ⟨n, u, h⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hϖ
    rw [IsDiscreteValuationRing.addVal_def x u hϖ n h, h]
    simp [hu]
  have hl0 : (l : O) ≠ 0 := by
    intro h
    have h' : algebraMap O (PadicAlgCl l) (l : O) = 0 := by rw [h, map_zero]
    rw [map_natCast] at h'
    exact (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) h'
  have hl : ‖algebraMap O (PadicAlgCl l) (l : O)‖ = (l : ℝ)⁻¹ := by
    have : algebraMap O (PadicAlgCl l) (l : O) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := by simp
    rw [this, norm_algebraMap', Padic.norm_p]
  have he : UpperTheory.V.Base.eO l O = IsDiscreteValuationRing.addVal O (l : O) :=
    (UpperTheory.V.Base.dvrFacts l O).2.2.2.2.2.2.2.1
  rw [he, ← hl, key a ha, key _ hl0, ← pow_mul, ← pow_mul, mul_comm]

theorem UpperTheory.norm_bound_of_integral_values :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
        [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [Algebra O (PadicAlgCl l)] [IsScalarTower ℤ_[l] O (PadicAlgCl l)] [FaithfulSMul O (PadicAlgCl l)],
        IsNVal O (PadicAlgCl l) (fun x => ((UpperTheory.V.Base.eO l O).toNat : ℝ) * UpperTheory.V.UnitaryThreeInertia.vl1 l x) := by
  intro l _ O _ _ _ _ _ _ _ _
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hv : ∀ x, UpperTheory.V.UnitaryThreeInertia.vl1 l x = -Real.logb l ‖x‖ := fun x => by
    rw [UpperTheory.V.UnitaryThreeInertia.vl1, Real.logb, neg_div]
  simp only [hv]
  refine ⟨fun x y hx hy => ?_, fun x y hx hy hxy => ?_, fun a ha => ?_⟩
  · rw [norm_mul, Real.logb_mul (norm_ne_zero_iff.2 hx) (norm_ne_zero_iff.2 hy)]
    ring
  · have h := IsUltrametricDist.norm_add_le_max x y
    have hp := norm_pos_iff.2 hxy
    rcases le_max_iff.1 h with h | h
    · refine min_le_of_left_le (mul_le_mul_of_nonneg_left (neg_le_neg ?_) (Nat.cast_nonneg _))
      exact Real.logb_le_logb_of_le hl hp h
    · refine min_le_of_right_le (mul_le_mul_of_nonneg_left (neg_le_neg ?_) (Nat.cast_nonneg _))
      exact Real.logb_le_logb_of_le hl hp h
  · have h := congrArg (Real.logb l) (norm_abs l O a ha)
    rw [Real.logb_pow, Real.logb_pow, Real.logb_inv, Real.logb_self_eq_one hl] at h
    linarith
end

section

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia UpperTheory.V.Pr

private theorem rz_off {O A : Type} [CommRing O] [IsLocalRing O] {G Γ ι : Type} [Group G] [Group Γ]
    (F : Frame O G Γ ι) [CommRing A] [Algebra O A] (g : Γ) {a b : Fin 3} (h : wt a b ≠ 0) :
    (F.rz A g).mat a b = 0 := by
  have hab : a ≠ b := by
    rintro rfl
    simp [wt] at h
  simp [Frame.rz, r0, GG.mat, GG.map, tor_val, Matrix.diagonal_apply_ne _ hab]

private theorem eq_of_wt {a b : Fin 3} (h : wt a b = 0) : a = b := by
  simp only [wt, wt1] at h
  apply Fin.ext
  omega

theorem UpperTheory.V.UnitaryThreeInertia.universal_diagonal_of_triangular_points :
    ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O] [Finite (ResidueField O)]
      {G Γ ι : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
      [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ] [Finite ι] (F : Frame O G Γ ι), F.Ok →
    F.Cl1 → ∀ (g₁ : Γ), F.Marked g₁ → ∀ {R : Type} [CommRing R] [Algebra O R] [IsCO O R]
      (u : Γ →* GG (m := 3) (R := R)), F.IsUniv g₁ u →
    (∀ (A : Type) [CommRing A] [Algebra O A] [IsCD O A], (∀ a ∈ maximalIdeal O, algebraMap O A a = 0) →
      ∀ r : Γ →* GG (m := 3) (R := A), F.IsPt g₁ r → Upper F.η r ∨ Lower F.η r) →
      Module.Finite O (wpart O u 0) := by
  intro O _ _ _ _ _ _ G Γ ι _ _ _ _ _ _ _ _ _ _ _ _ _ F hOk hCl g₁ hg₁ R _ _ hCO u hu htri
  letI : IsLocalRing R := hCO.toIsLocalRing
  obtain ⟨W, hW, -⟩ := exists_adapted F hOk g₁ hg₁ u hu
  rw [← hW.part 0]
  have key : ∀ {A : Type} [CommRing A] [Algebra O A] (f : R →ₐ[O] A) (g : Γ) (a b : Fin 3),
      f ((u g).mat a b - ((F.rz R) g).mat a b) = ((push f u) g).mat a b - ((F.rz A) g).mat a b := by
    intro A _ _ f g a b
    simp [push, Frame.rz, GG.mat, GG.map]
  refine finCrit O R W ?_ ?_
  · intro i
    obtain ⟨g, a, b, -, -, hz⟩ := hW.var i
    rw [hz]
    have h1 := hu.pt.red g a b
    have h2 : ((F.rz R) g).mat = ((r0 F.η F.Ψ) g).mat.map ⇑(algebraMap O R) := by
      simp [Frame.rz, GG.mat, GG.map]
    rw [h2]
    simpa using h1
  · intro A _ _ hCD f hf hA
    haveI iDA : IsDomain A := hCD.toIsDomain
    have iDVR : IsDiscreteValuationRing A := hCD.toIsDiscreteValuationRing
    letI iLA : IsLocalRing A := iDVR.toIsLocalRing
    haveI iNA : IsNoetherianRing A := @PrincipalIdealRing.isNoetherianRing A _ iDVR.toIsPrincipalIdealRing
    haveI : IsLocalHom (algebraMap O A) := hCD.isLocalHom
    haveI := hf
    have hpt : F.IsPt g₁ (push f u) := isPt_push F f g₁ u hu.pt
    have htr := htri A hA (push f u) hpt
    have hdiag : ∀ (g : Γ) (a : Fin 3), ((push f u) g).mat a a = ((F.rz A) g).mat a a :=
      @diag_eq_of_tri O _ _ _ _ _ _ G Γ ι _ _ _ _ _ _ _ _ _ _ _ _ _ F hOk hCl g₁ hg₁ A _ iDA iLA iNA _ _
        (push f u) hpt htr
    refine ⟨?_, ?_⟩
    · intro i hi
      obtain ⟨g, a, b, -, hw, hz⟩ := hW.var i
      rw [hi] at hw
      obtain rfl := eq_of_wt hw.symm
      rw [hz, key, hdiag, sub_self]
    · rcases htr with hU | hL
      · left
        intro i hi
        obtain ⟨g, a, b, hg, hw, hz⟩ := hW.var i
        rw [hw] at hi
        rw [hz, key, hU g (MonoidHom.mem_ker.mpr hg) a b hi, rz_off (A := A) F g hi.ne, sub_self]
      · right
        intro i hi
        obtain ⟨g, a, b, hg, hw, hz⟩ := hW.var i
        rw [hw] at hi
        rw [hz, key, hL g (MonoidHom.mem_ker.mpr hg) a b hi, rz_off (A := A) F g hi.ne', sub_self]
end

section

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

private theorem norm_two_eq_one {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [CharZero O]
    [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (h : IsUnit (2 : O)) : ‖(2 : PadicAlgCl l)‖ = 1 := by
  haveI : Nontrivial O := IsDomain.toNontrivial
  have h2 : IsUnit (2 : ℤ_[l]) := by
    by_contra hn
    have hl : (l : ℤ) ∣ 2 := by
      rw [PadicInt.isUnit_iff] at hn
      have hlt : ‖((2 : ℤ) : ℤ_[l])‖ < 1 := lt_of_le_of_ne (PadicInt.norm_le_one _) (by simpa using hn)
      exact PadicInt.norm_int_lt_one_iff_dvd 2 |>.1 hlt
    have hinj : Function.Injective (algebraMap ℤ_[l] O) := by
      set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
      intro x hx
      by_contra hx0
      have e := PadicInt.unitCoeff_spec hx0
      rw [e, map_mul, map_pow, map_natCast] at hx
      rcases mul_eq_zero.1 hx with h1 | h1
      · exact ((Units.isUnit _).map (algebraMap ℤ_[l] O)).ne_zero h1
      · exact pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) h1
    haveI : FaithfulSMul ℤ_[l] O := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
    exact hn (isUnit_of_map_unit (algebraMap ℤ_[l] O) 2 (by rwa [map_ofNat]))
  have h3 : ‖(2 : ℚ_[l])‖ = 1 := by
    have := PadicInt.isUnit_iff.1 h2
    rw [PadicInt.norm_def] at this
    exact_mod_cast this
  rw [← map_ofNat (algebraMap ℚ_[l] (PadicAlgCl l)) 2, norm_algebraMap', h3]

theorem UpperTheory.V.UnitaryThreeInertia.conj_of_matIso :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O] [Finite (ResidueField O)]
      [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [Algebra O (PadicAlgCl l)] [IsScalarTower ℤ_[l] O (PadicAlgCl l)] [FaithfulSMul O (PadicAlgCl l)]
      {G Γ ι : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
      [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ] [Finite ι] (F : Frame O G Γ ι), F.Ok →
    ∀ g₁, F.Marked g₁ → ∀ (r : Γ →* GG (m := 3) (R := PadicAlgCl l)), F.IsCharZeroPt g₁ r →
      ∀ r' : Γ →* GG (m := 3) (R := PadicAlgCl l), F.IsCharZeroPt g₁ r' → TypeI F.η r →
        MatIso F.η.ker (mats r) (mats r') → ∃ t, r' = conjBy (tor (PadicAlgCl l) t) r := by
  intro l _ O _ _ _ _ _ _ _ _ _ _ _ G Γ ι _ _ _ _ _ _ _ _ _ _ _ _ _ F hF g₁ hg r hr r' hr' hI hiso
  obtain ⟨m, n, -, hz, hz1, -⟩ := isCharZeroPt_basic F hF g₁ hg r hr
  obtain ⟨m', n', -, hz', hz1', -⟩ := isCharZeroPt_basic F hF g₁ hg r' hr'
  refine conjBy_tor_of_iso F.η r r' F.c g₁ two_ne_zero m m' hF.ηc hg.1 n n' ?_ ?_ ?_ (Or.inl hI) hiso
  · rw [← norm_ne_zero_iff, hz1]; exact one_ne_zero
  · rw [← norm_ne_zero_iff, hz1']; exact one_ne_zero
  · intro e
    have h2 := norm_two_eq_one (l := l) hF.two
    have hle := IsUltrametricDist.norm_add_le_max
      (zeta F.c g₁ r - zeta F.c g₁ (F.rz (PadicAlgCl l)))
      (-(zeta F.c g₁ r' - zeta F.c g₁ (F.rz (PadicAlgCl l))))
    rw [norm_neg] at hle
    have hlt := lt_of_le_of_lt hle (max_lt hz hz')
    have e2 : zeta F.c g₁ r - zeta F.c g₁ (F.rz (PadicAlgCl l)) +
        -(zeta F.c g₁ r' - zeta F.c g₁ (F.rz (PadicAlgCl l))) = 2 * zeta F.c g₁ r := by
      rw [e]; ring
    rw [e2, norm_mul, h2, hz1, mul_one] at hlt
    exact lt_irrefl _ hlt
end

local instance (priority := 2000) ratFieldIsTorsionFree (Ω : Type) [Field Ω] [CharZero Ω] :
    Module.IsTorsionFree ℚ Ω := DivisionSemiring.to_moduleIsTorsionFree

section

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia Module

private noncomputable def subquotEquiv {R R' X : Type*} [CommRing R] [CommRing R'] [AddCommGroup X]
    [Module R X] [Module R' X] (Z B : Submodule R X) (Z' B' : Submodule R' X)
    (hZ : ∀ x, x ∈ Z ↔ x ∈ Z') (hB : ∀ x, x ∈ B ↔ x ∈ B') :
    (Z ⧸ B.comap Z.subtype) ≃ (Z' ⧸ B'.comap Z'.subtype) :=
  Quotient.congr (Equiv.subtypeEquivRight hZ) fun a b => by
    rw [Submodule.quotientRel_def, Submodule.quotientRel_def]
    exact hB _

private theorem ef_eq_one (v : Pl) : v.asIdeal.ramificationIdx ℤ * v.asIdeal.inertiaDeg ℤ = 1 := by
  classical
  letI : Module.Free ℤ (NumberField.RingOfIntegers ℚ) :=
    NumberField.RingOfIntegers.instFreeInt ℚ
  haveI : Module.Flat ℤ (NumberField.RingOfIntegers ℚ) := Module.Flat.of_free
  haveI : Fintype ((v.asIdeal.under ℤ).primesOver (NumberField.RingOfIntegers ℚ)) := Fintype.ofFinite _
  have hsum := Ideal.sum_ramification_inertia_eq_finrank (v.asIdeal.under ℤ) (NumberField.RingOfIntegers ℚ)
  rw [NumberField.RingOfIntegers.rank, Module.finrank_self] at hsum
  have hmem : v.asIdeal ∈ (v.asIdeal.under ℤ).primesOver (NumberField.RingOfIntegers ℚ) :=
    ⟨inferInstance, ⟨rfl⟩⟩
  have hle := Finset.single_le_sum
    (f := fun q : (v.asIdeal.under ℤ).primesOver (NumberField.RingOfIntegers ℚ) =>
      q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ) (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ (⟨v.asIdeal, hmem⟩ : (v.asIdeal.under ℤ).primesOver _))
  have hDedekind : IsDedekindDomain (NumberField.RingOfIntegers ℚ) := inferInstance
  haveI : IsNoetherianRing (Localization.AtPrime v.asIdeal) :=
    IsLocalization.isNoetherianRing v.asIdeal.primeCompl _ hDedekind.toIsDedekindRing.toIsNoetherian
  haveI : IsNoetherianRing (Localization.AtPrime v.asIdeal ⧸
      (v.asIdeal.under ℤ).map (algebraMap ℤ (Localization.AtPrime v.asIdeal))) :=
    Ideal.Quotient.isNoetherianRing _
  have he := Ideal.ramificationIdx_pos (R := ℤ) v.asIdeal
  have hf := Ideal.inertiaDeg_pos v.asIdeal ℤ
  simp only at hle
  rw [hsum] at hle
  have := Nat.mul_pos he hf
  omega

theorem UpperTheory.local_euler_characteristic_rationals :
    LocalFiniteness → LocalEulerChar → ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (k M : Type) [Field k] [Finite k] [CharP k l] [AddCommGroup M] [Module k M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (A : ValuationSubring Ω) (v : Pl) (ρ : Representation k (Dec (F := ℚ) A) M),
        Formalism.ConjugateSelfDual.IsPlaceOver A v → ContAction ρ →
        Module.Finite k (H1 ρ) ∧ Module.Finite k (H2 ρ) ∧
          (((l : ℕ) : NumberField.RingOfIntegers ℚ) ∈ v.asIdeal → finrank k (H1 ρ) = finrank k (H0 ρ) + finrank k (H2 ρ) + finrank k M) ∧
          (((l : ℕ) : NumberField.RingOfIntegers ℚ) ∉ v.asIdeal → finrank k (H1 ρ) = finrank k (H0 ρ) + finrank k (H2 ρ)) := by
  intro hFin hEC Ω _ _ _ l _ k M _ _ _ _ _ _ _ _ A v ρ hv hc
  classical
  haveI : CharP k (l ^ 1) := by rw [pow_one]; infer_instance
  let φ : ZMod (l ^ 1) →+* k := ZMod.castHom (dvd_refl _) k
  letI : Module (ZMod (l ^ 1)) M := Module.compHom M φ
  haveI : LinearMap.CompatibleSMul M M (ZMod (l ^ 1)) k := ⟨fun f c x => f.map_smul (φ c) x⟩
  let ρ' : Representation (ZMod (l ^ 1)) (Dec (F := ℚ) A) M :=
    { toFun := fun g => (ρ g).restrictScalars (ZMod (l ^ 1))
      map_one' := by ext x; simp
      map_mul' := fun g h => by ext x; simp }
  have hc' : ContAction ρ' := hc
  have hF := hFin ℚ Ω l 1 M A ρ' v one_pos hv hc'
  have hE := hEC ℚ Ω l 1 M A ρ' v one_pos hv hc'
  have e1 : H1 ρ' ≃ H1 ρ := subquotEquiv _ _ _ _ (fun _ => Iff.rfl) (fun _ => Iff.rfl)
  have e2 : H2 ρ' ≃ H2 ρ := subquotEquiv _ _ _ _ (fun _ => Iff.rfl) (fun _ => Iff.rfl)
  have e0 : ↥(H0 ρ') ≃ ↥(H0 ρ) := Equiv.subtypeEquivRight (fun _ => Iff.rfl)
  haveI := hF.2.1
  haveI := hF.2.2.1
  haveI : Finite (H1 ρ) := Finite.of_equiv _ e1
  haveI : Finite (H2 ρ) := Finite.of_equiv _ e2
  haveI : Module.Finite k (H1 ρ) := Module.Finite.of_finite
  haveI : Module.Finite k (H2 ρ) := Module.Finite.of_finite
  haveI : Module.Finite k M := Module.Finite.of_finite
  haveI : Module.Finite k ↥(H0 ρ) := Module.Finite.of_finite
  have hq : 1 < Nat.card k := Finite.one_lt_card
  have inj := Nat.pow_right_injective (show 2 ≤ Nat.card k by omega)
  have c1 : Nat.card (H1 ρ') = Nat.card k ^ finrank k (H1 ρ) := by
    rw [Nat.card_congr e1]; exact Module.natCard_eq_pow_finrank
  have c2 : Nat.card (H2 ρ') = Nat.card k ^ finrank k (H2 ρ) := by
    rw [Nat.card_congr e2]; exact Module.natCard_eq_pow_finrank
  have c0 : Nat.card ↥(H0 ρ') = Nat.card k ^ finrank k ↥(H0 ρ) := by
    rw [Nat.card_congr e0]; exact Module.natCard_eq_pow_finrank
  have cM : Nat.card M = Nat.card k ^ finrank k M := Module.natCard_eq_pow_finrank
  have hd : locDeg v = 1 := ef_eq_one v
  refine ⟨inferInstance, inferInstance, fun hl => ?_, fun hl => ?_⟩
  · have h := hE.1 hl
    rw [c1, c0, c2, cM, hd, pow_one, ← pow_add, ← pow_add] at h
    exact inj h
  · have h := hE.2 hl
    rw [c1, c0, c2, ← pow_add] at h
    exact inj h
end

section

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia Module

theorem UpperTheory.card_global_euler_characteristic_rationals :
    GlobalEulerChar → ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (M : Type) [AddCommGroup M] [Module (ZMod (l ^ 1)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (S : Finset Pl) (ρ : Representation (ZMod (l ^ 1)) (Gam Ω S) M),
            ContainsAbove S l → ContAction ρ → ∀ σ : Formalism.ConjugateSelfDual.G ℚ Ω, IsCC σ →
            Nat.card (H1 ρ) * Nat.card {m : M // ρ (toGS Ω _ σ) m = m} = Nat.card (H0 ρ) * Nat.card (H2 ρ) * Nat.card M := by
  intro hG Ω _ _ _ l _ _ M _ _ _ _ _ S ρ hS hρ σ hσ
  have h := hG ℚ Ω l 1 M S ρ Nat.one_pos hS hρ (fun _ => σ) (by
    intro w _
    obtain ⟨j, hj⟩ := hσ
    exact ⟨j, hj, Subsingleton.elim _ _⟩)
  have hc : NumberField.InfinitePlace.nrComplexPlaces ℚ = 0 :=
    NumberField.InfinitePlace.nrComplexPlaces_eq_zero_of_finrank_eq_one (Module.finrank_self ℚ)
  simp only [archH0Card, hc, pow_zero, mul_one, Module.finrank_self, pow_one] at h
  rw [Finset.prod_eq_single_of_mem Rat.infinitePlace
    (by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact Rat.isReal_infinitePlace)
    (fun b _ hb => absurd (Subsingleton.elim b _) hb)] at h
  exact h.symm
end

section

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia Module

private theorem twDual_inv_eq_zero {Γ k M : Type} [Group Γ] [Field k] [AddCommGroup M] [Module k M]
    (N : ℕ) [Module (ZMod N) M] (μ : Γ →* (ZMod N)ˣ) (ρ : Representation k Γ M)
    (g : Γ) (a : k) (n : ℕ) (hg : ∀ m, ρ g m = a • m) (hn : (n : ZMod N) = μ g) (han : a ≠ (n : k))
    (y : H0 (twDual μ (GlobalTheory.Published.zmodRep N ρ))) : y = 0 := by
  obtain ⟨φ, hφ⟩ := y
  apply Subtype.ext
  have h1 : twDual μ (GlobalTheory.Published.zmodRep N ρ) g φ = φ := hφ _
  show φ = 0
  apply LinearMap.ext
  intro x
  set m : M := (a - (n : k))⁻¹ • x with hm
  have hx : x = a • m - n • m := by
    rw [← Nat.cast_smul_eq_nsmul k, ← sub_smul, hm, smul_smul,
      mul_inv_cancel₀ (sub_ne_zero.2 han), one_smul]
  have h3 := congrArg (fun ψ : TDual (ZMod N) M => ψ (GlobalTheory.Published.zmodRep N ρ g m)) h1
  simp only [twDual_apply] at h3
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply,
    ← hn] at h3
  have h4 : GlobalTheory.Published.zmodRep N ρ g m = a • m := hg m
  rw [h4] at h3
  show φ x = 0
  rw [hx]
  refine (LinearMap.map_sub (φ : Module.Dual (ZMod N) M) _ _).trans (sub_eq_zero.mpr ?_)
  refine h3.symm.trans ?_
  rw [← nsmul_eq_mul]
  exact (map_nsmul (F := Module.Dual (ZMod N) M) φ n m).symm

theorem UpperTheory.global_cohomology_finite_set :
    GlobalTheory.Published.PoitouTateNormalised → ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (k M : Type) [Field k] [Finite k] [CharP k l] [AddCommGroup M] [Module k M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (S : Finset Pl) (A : S → ValuationSubring Ω) (ρ : Representation k (Gam Ω S) M),
                 ContainsAbove S l → (∀ v, Formalism.ConjugateSelfDual.IsPlaceOver (A v) v.1) → ContAction ρ →
                 (∃ (σ : Formalism.ConjugateSelfDual.G ℚ Ω) (a : k) (n : ℕ), (∀ m, ρ (toGS Ω _ σ) m = a • m) ∧ (n : ZMod (l ^ 1)) = (cycMod ℚ Ω l 1 σ : (ZMod (l ^ 1))ˣ) ∧ a ≠ (n : k)) →
                 ∀ κ : ∀ v : S, Z2 (ρ.comp ((toGS Ω _).comp (Dec (F := ℚ) (A v)).subtype) : Representation k (Dec (F := ℚ) (A v)) M), ∃ z : Z2 ρ, ∀ v : S,
                   (fun p : Dec (F := ℚ) (A v) × Dec (F := ℚ) (A v) => z.1 (toGS Ω _ p.1.1, toGS Ω _ p.2.1)) - (κ v).1 ∈
                     B2 (ρ.comp ((toGS Ω _).comp (Dec (F := ℚ) (A v)).subtype) : Representation k (Dec (F := ℚ) (A v)) M) := by
  intro hPT Ω _ _ _ l _ hl k M _ _ _ _ _ _ _ _ S A ρ hS hA hρ hσ κ
  obtain ⟨σ, a, n, hσa, hn, han⟩ := hσ
  have hM : ∀ m : M, (l ^ 1) • m = 0 := fun m => by
    rw [pow_one, ← Nat.cast_smul_eq_nsmul k, CharP.cast_eq_zero, zero_smul]
  letI : Module (ZMod (l ^ 1)) M := AddCommGroup.zmodModule hM
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : NeZero (l ^ 1) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ 1)
  obtain ⟨μ, hμ⟩ := GlobalTheory.Published.PoitouTate.exists_lift_cycMod (F := ℚ) (Ω := Ω) (l := l) (r := 1) hS
  obtain ⟨inv, -, h⟩ := hPT ℚ Ω l 1 (Or.inl hl) Nat.one_pos ζ hζ
  have hex := (h S hS A hA μ hμ M (GlobalTheory.Published.zmodRep (l ^ 1) ρ) hρ).1
  have hμσ : μ (toGS Ω _ σ) = cycMod ℚ Ω l 1 σ := DFunLike.congr_fun hμ σ
  obtain ⟨z, hz⟩ := (hex.mem_range_localization_H2_iff
    (fun v => Submodule.Quotient.mk ⟨(κ v).1, (κ v).2⟩)).2 (fun y => by
      rw [twDual_inv_eq_zero (l ^ 1) μ ρ _ a n hσa (by rw [hμσ]; exact hn) han y]
      simp only [map_zero, Finset.sum_const_zero])
  induction z using Submodule.Quotient.induction_on with
  | H z =>
    refine ⟨⟨z.1, z.2⟩, fun v => ?_⟩
    have e : (Submodule.Quotient.mk (restrictCocycles2 (GlobalTheory.Published.zmodRep (l ^ 1) ρ) (locFam S A v)
        (continuous_locFam S A v) z) : H2 ((GlobalTheory.Published.zmodRep (l ^ 1) ρ).comp (locFam S A v))) =
        Submodule.Quotient.mk ⟨(κ v).1, (κ v).2⟩ := congrFun hz v
    obtain ⟨c, hc, hcf⟩ := (separated_dvr_second_cohomology_mem _ _).1 ((Submodule.Quotient.eq _).1 e)
    exact (separated_dvr_second_cohomology_mem _ _).2 ⟨c, hc, hcf⟩
end
