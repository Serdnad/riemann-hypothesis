module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.FLevel
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.FLimit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.OfDetToDet
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DChKer
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle016
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DPull
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle009
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle012
public import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.IsSaturatedChain
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
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
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle002
public import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.LocDim
public import ReciprocityTheory.CommutativeAlgebra.PolynomialHeights.HeightAddRingKrullDimQuotientMvPolynomialField
import ReciprocityTheory.CommutativeAlgebra.PolynomialHeights.PolyCM
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.RingTheory.MvPolynomial.Localization

@[expose] public section

section

open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

theorem UpperTheory.V.CA.finE :
    ∀ {n h : ℕ} {B G : Type} [CommRing B] [IsLocalRing B] [IsNoetherianRing B] [IsAdicComplete (maximalIdeal B) B] [Finite (ResidueField B)] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] (D : GDet n B G) (χ : Fin n → G →* (ResidueField B)ˣ), D.IsCont (maximalIdeal B) → D.map (residue B) = GDet.ofChars χ → MultFree χ h → ∀ Z : Set (MonoidAlgebra B G), (∃ s : Finset G, s.card ≤ finBound n h ∧ Submodule.span B ((fun g => D.toQuot Z (MonoidAlgebra.single g 1)) '' (s : Set G)) = ⊤) ∧ Module.Finite B (D.CHQuot Z) ∧ ∀ N : ℕ, ∃ U : OpenNormalSubgroup G, ∀ u ∈ U, D.toQuot Z (MonoidAlgebra.single u 1) - 1 ∈ (maximalIdeal B ^ N) • (⊤ : Submodule B (D.CHQuot Z)) := by
  classical
  intro n h B G _ _ _ _ _ _ _ _ _ _ D χ hc hm hmf Z
  obtain ⟨s, hs, hy, hU⟩ := f_limit (D.CH ∪ Z) (finBound n h) (fun U => by
    obtain ⟨s, hs, hy⟩ := f_level D χ hc hm hmf 1 U
    refine ⟨s, hs, fun y => ?_⟩
    obtain ⟨z, hz, hyz⟩ := hy y
    refine ⟨z, hz, ?_⟩
    apply TwoSidedIdeal.span_mono ?_ hyz
    intro x hx
    rcases hx with (hx | hx) | hx
    · exact Or.inl (Or.inl (Or.inl hx))
    · exact Or.inl (Or.inr hx)
    · exact Or.inr hx)
  have key : ∀ a b : MonoidAlgebra B G, a - b ∈ closureIdeal (maximalIdeal B) (D.CH ∪ Z) →
      D.toQuot Z a = D.toQuot Z b := by
    intro a b hab
    show RingCon.mkₐ B (D.chBar Z).ringCon a = RingCon.mkₐ B (D.chBar Z).ringCon b
    exact Quot.sound ((TwoSidedIdeal.rel_iff _ _ _).2 hab)
  have hspan : Submodule.span B ((fun g => D.toQuot Z (MonoidAlgebra.single g 1)) '' (s : Set G)) = ⊤ := by
    rw [eq_top_iff]
    intro q _
    obtain ⟨y, rfl⟩ : ∃ y, D.toQuot Z y = q := ⟨Quot.out q, Quot.out_eq q⟩
    obtain ⟨z, hz, hyz⟩ := hy y
    have himg : (fun g => D.toQuot Z (MonoidAlgebra.single g 1)) '' (s : Set G) =
        (D.toQuot Z).toLinearMap '' ((fun g => MonoidAlgebra.single g 1) '' (s : Set G)) := by
      rw [Set.image_image]
      rfl
    rw [himg, Submodule.span_image]
    exact ⟨z, hz, (key y z hyz).symm⟩
  refine ⟨⟨s, hs, hspan⟩, ⟨⟨s.image (fun g => D.toQuot Z (MonoidAlgebra.single g 1)), by
    rw [Finset.coe_image]
    exact hspan⟩⟩, ?_⟩
  intro N
  obtain ⟨U, hU'⟩ := hU N
  refine ⟨U, fun u hu => ?_⟩
  obtain ⟨z, hz, hz'⟩ := hU' u hu
  have heq : D.toQuot Z (MonoidAlgebra.single u 1) - 1 = D.toQuot Z z := by
    rw [← map_one (D.toQuot Z), ← map_sub]
    exact key _ _ hz'
  rw [heq]
  have hle : (maximalIdeal B ^ N) • (⊤ : Submodule B (MonoidAlgebra B G)) ≤
      ((maximalIdeal B ^ N) • (⊤ : Submodule B (D.CHQuot Z))).comap (D.toQuot Z).toLinearMap := by
    rw [Submodule.smul_le]
    intro r hr m _
    rw [Submodule.mem_comap]
    show D.toQuot Z (r • m) ∈ _
    rw [map_smul]
    exact Submodule.smul_mem_smul hr trivial
  exact hle hz
end

section

open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

theorem UpperTheory.V.CA.d_quotDet :
    ∀ {n : ℕ} {A G : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [Group G] (D : GDet n A G) [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G], D.IsCont (maximalIdeal A) → ∀ Z : Set (MonoidAlgebra A G), (∀ z ∈ Z, D.Kills z) → ∃ DE : Det n A (D.CHQuot Z), DE.IsCH ∧ DE.pull (D.toQuot Z) = D.toDet := by
  intro n A G _ _ _ _ D _ _ _ _ hc Z hZ
  set f := D.toQuot Z
  have hsurj : Function.Surjective f := RingCon.mkₐ_surjective _
  have hmem : ∀ x, x ∈ D.chBar Z → f x = 0 := by
    intro x hx
    have hr : (D.chBar Z).ringCon x 0 := (TwoSidedIdeal.rel_iff _ _ _).2 (by rwa [sub_zero])
    rw [← map_zero f]
    exact (RingCon.eq _).2 hr
  have hker : ∀ x, f x = 0 → x ∈ D.chBar Z := by
    intro x hx
    rw [← map_zero f] at hx
    have hr := (RingCon.eq _).1 hx
    simpa using (TwoSidedIdeal.rel_iff _ _ _).1 hr
  have hle : TwoSidedIdeal.span (D.CH ∪ Z) ≤ D.chBar Z := by
    unfold GDet.chBar closureIdeal
    refine le_iInf fun N => le_iInf fun H => fun y hy => ?_
    exact TwoSidedIdeal.mem_span_iff.1 hy _ fun z hz =>
      TwoSidedIdeal.subset_span (R := MonoidAlgebra A G) (Or.inl (Or.inl hz))
  have hsub : D.CH ∪ Z ⊆ D.chBar Z := fun x hx =>
    hle (TwoSidedIdeal.subset_span (R := MonoidAlgebra A G) hx)
  have hCHk : ∀ z ∈ D.CH, D.Kills z := by
    intro z hz
    have hz' : z ∈ D.toDet.CH := by
      rw [d_toDet_CH]
      exact TwoSidedIdeal.subset_span (R := MonoidAlgebra A G) hz
    exact (d_toDet D z).2.2.2.1 ((d_ker _ z).1.1 (d_ch_ker _ hz'))
  have hK : ∀ x, f x = 0 → x ∈ D.toDet.ker := fun x hx =>
    (d_ker _ x).1.2 ((d_toDet D x).2.2.2.2
      (d_closed D (maximalIdeal A) hc (D.CH ∪ Z)
        (by
          rintro z (hz | hz)
          exacts [hCHk z hz, hZ z hz]) x (hker x hx)))
  obtain ⟨DE, hDE, -⟩ := d_factor D.toDet f hsurj hK
  refine ⟨DE, ?_, hDE⟩
  show DE.CH = ⊥
  ext y
  constructor
  · intro hy
    obtain ⟨x, hx, rfl⟩ := ((d_pull DE f).2.2.2 hsurj).2 y hy
    rw [hDE, d_toDet_CH] at hx
    rw [hmem x ((TwoSidedIdeal.mem_span_iff.1 hx) _ fun z hz => hsub (Or.inl hz))]
    exact TwoSidedIdeal.zero_mem _
  · intro hy
    rw [TwoSidedIdeal.mem_bot] at hy
    rw [hy]
    exact TwoSidedIdeal.zero_mem _
end

section

open IsLocalRing

private theorem height_map_mk_comap {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T)
    (hφ : Function.Surjective φ) (I : Ideal S) (hI : I = RingHom.ker φ) (J : Ideal T) :
    ((J.comap φ).map (Ideal.Quotient.mk I)).height = J.height := by
  subst hI
  have h : (J.comap φ).map (Ideal.Quotient.mk (RingHom.ker φ)) =
      J.comap (RingHom.quotientKerEquivOfSurjective hφ) := by
    rw [← Ideal.map_comap_of_surjective (Ideal.Quotient.mk (RingHom.ker φ)) Ideal.Quotient.mk_surjective
      (J.comap (RingHom.quotientKerEquivOfSurjective hφ))]
    congr 1
  rw [h, RingEquiv.height_comap]

attribute [local instance] MvPolynomial.algebraMvPolynomial in
private theorem height_ker_add {B C : Type} [CommRing B] [IsDomain B] [CommRing C] [IsDomain C] [Algebra B C]
    [FaithfulSMul B C] (t N : ℕ) (ht : Algebra.trdeg B C = t) (g : MvPolynomial (Fin N) B →ₐ[B] C)
    (hg : Function.Surjective g) :
    ((RingHom.ker (g : MvPolynomial (Fin N) B →+* C)).height : WithBot ℕ∞) + t = N := by
  let K := FractionRing B
  let L := FractionRing C
  have hBL : Function.Injective (algebraMap B L) := by
    rw [IsScalarTower.algebraMap_eq B C L]
    exact (IsFractionRing.injective C L).comp (FaithfulSMul.algebraMap_injective B C)
  have : FaithfulSMul B L := (faithfulSMul_iff_algebraMap_injective _ _).mpr hBL
  letI : Algebra K L := FractionRing.liftAlgebra B L
  have : IsScalarTower B K L := FractionRing.isScalarTower_liftAlgebra B L
  let g' : MvPolynomial (Fin N) K →ₐ[K] L :=
    MvPolynomial.aeval fun i => algebraMap C L (g (MvPolynomial.X i))
  have hgg : ∀ x, g' (algebraMap (MvPolynomial (Fin N) B) (MvPolynomial (Fin N) K) x) = algebraMap C L (g x) := by
    intro x
    induction x using MvPolynomial.induction_on with
    | C a =>
      rw [MvPolynomial.algebraMap_def, MvPolynomial.map_C, MvPolynomial.algHom_C, MvPolynomial.algHom_C,
        ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | mul_X a i ha =>
      simp only [map_mul, ha]
      rw [MvPolynomial.algebraMap_def, MvPolynomial.map_X]
      simp [g']
  have hL : IsLocalization ((nonZeroDivisors B).map (MvPolynomial.C (σ := Fin N))) (MvPolynomial (Fin N) K) :=
    MvPolynomial.isLocalization _ _
  have hp : (RingHom.ker g').IsPrime := RingHom.ker_isPrime g'
  have hc : (RingHom.ker g').comap (algebraMap (MvPolynomial (Fin N) B) (MvPolynomial (Fin N) K)) =
      RingHom.ker (g : MvPolynomial (Fin N) B →+* C) := by
    ext x
    rw [Ideal.mem_comap, RingHom.mem_ker, RingHom.mem_ker, hgg]
    exact map_eq_zero_iff _ (IsFractionRing.injective C L)
  have h1 := ReciprocityTheory.CA.height_add_ringKrullDim_quotient_mvPolynomial_field K N (RingHom.ker g')
  have h2 : ringKrullDim (MvPolynomial (Fin N) K ⧸ RingHom.ker g') = ringKrullDim g'.range :=
    ringKrullDim_eq_of_ringEquiv (Ideal.quotientKerEquivRange g').toRingEquiv
  have hft : Algebra.FiniteType K g'.range :=
    Algebra.FiniteType.of_surjective g'.rangeRestrict g'.rangeRestrict_surjective
  have h3 : Algebra.trdeg K g'.range = t := by
    have hmem : ∀ c : C, algebraMap C L c ∈ g'.range := fun c => by
      obtain ⟨x, rfl⟩ := hg c
      exact ⟨_, hgg x⟩
    let j : C →ₐ[B] g'.range.restrictScalars B :=
      (IsScalarTower.toAlgHom B C L).codRestrict (g'.range.restrictScalars B) hmem
    have hj : Function.Injective j := fun a b hab =>
      IsFractionRing.injective C L (congrArg Subtype.val hab)
    have a1 : Algebra.trdeg B C ≤ Algebra.trdeg B g'.range := trdeg_le_of_injective j hj
    have a2 : Algebra.trdeg B g'.range ≤ Algebra.trdeg B L :=
      trdeg_le_of_injective (g'.range.val.restrictScalars B) Subtype.val_injective
    have : Algebra.IsAlgebraic C L := IsLocalization.isAlgebraic L (nonZeroDivisors C)
    have : Algebra.IsAlgebraic B K := IsLocalization.isAlgebraic K (nonZeroDivisors B)
    have a3 : Algebra.trdeg B L = Algebra.trdeg B C := by
      rw [← trdeg_add_eq B C (A := L), trdeg_eq_zero (R := C) (A := L), add_zero]
    have a4 : Algebra.trdeg B g'.range = Algebra.trdeg K g'.range := by
      have : FaithfulSMul K g'.range :=
        (faithfulSMul_iff_algebraMap_injective _ _).mpr (algebraMap K g'.range).injective
      rw [← trdeg_add_eq B K (A := g'.range), trdeg_eq_zero (R := B) (A := K), zero_add]
    rw [← a4, ← ht]
    exact le_antisymm (a2.trans a3.le) a1
  rw [h2, ReciprocityTheory.CA.ringKrullDim_eq_of_trdeg_eq_field t h3,
    ← IsLocalization.height_under ((nonZeroDivisors B).map (MvPolynomial.C (σ := Fin N))) (RingHom.ker g'), Ideal.under_def, hc] at h1
  exact h1

theorem UpperTheory.V.CA.g_dimform :
    ∀ (B C : Type) [CommRing B] [IsDomain B] [IsLocalRing B] [CommRing C] [IsDomain C] [Algebra B C] [FaithfulSMul B C]
      [Algebra.FiniteType B C] (t : ℕ), ReciprocityTheory.CA.IsCMQuot B → Algebra.trdeg B C = t →
        ∀ (𝔪 : Ideal C) [𝔪.IsMaximal], 𝔪.comap (algebraMap B C) = maximalIdeal B →
          (𝔪.height : WithBot ℕ∞) = ringKrullDim B + t := by
  intro B C _ _ _ _ _ _ _ hft t hB ht 𝔪 _ h𝔪
  obtain ⟨P, _, _, f, hP, hf⟩ := hB
  have := hP.1
  obtain ⟨N, g, hg⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp hft
  let F : MvPolynomial (Fin N) P →+* MvPolynomial (Fin N) B := MvPolynomial.map f
  have hF : Function.Surjective F := MvPolynomial.map_surjective f hf
  let G : MvPolynomial (Fin N) P →+* C := (g : MvPolynomial (Fin N) B →+* C).comp F
  have hG : Function.Surjective G := hg.comp hF
  have hGC : ∀ a : P, G (MvPolynomial.C a) = algebraMap B C (f a) := fun a => by
    simp [G, F]
  have : (𝔪.comap G).IsMaximal := Ideal.comap_isMaximal_of_surjective G hG
  have hc : (𝔪.comap G).comap MvPolynomial.C = maximalIdeal P := by
    have : (𝔪.comap G).comap MvPolynomial.C = (maximalIdeal B).comap f := by
      ext a
      rw [← h𝔪]
      simp only [Ideal.mem_comap, hGC]
    rw [this]
    exact IsLocalRing.eq_maximalIdeal (Ideal.comap_isMaximal_of_surjective f hf)
  obtain ⟨hCM, e1⟩ := ReciprocityTheory.CA.isCM_localization_mvPolynomial hP N (𝔪.comap G) hc
  have : (RingHom.ker G).IsPrime := RingHom.ker_isPrime G
  have : (RingHom.ker f).IsPrime := RingHom.ker_isPrime f
  have e2 := ReciprocityTheory.CA.height_eq_add_of_isCM_localization (𝔪.comap G) (RingHom.ker G) hCM
    (Ideal.ker_le_comap G)
  rw [height_map_mk_comap G hG _ rfl] at e2
  have : (RingHom.ker G).LiesOver (RingHom.ker f) := ⟨by
    ext a
    rw [Ideal.under_def, Ideal.mem_comap, RingHom.mem_ker, RingHom.mem_ker, MvPolynomial.algebraMap_eq, hGC]
    exact (map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective B C)).symm⟩
  have e3 := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (RingHom.ker f) (RingHom.ker G)
  have hk : RingHom.ker G = (RingHom.ker (g : MvPolynomial (Fin N) B →+* C)).comap F := rfl
  have e4 := height_map_mk_comap F hF ((RingHom.ker f).map (algebraMap P (MvPolynomial (Fin N) P)))
    (by rw [MvPolynomial.algebraMap_eq]; exact (MvPolynomial.ker_map f).symm)
    (RingHom.ker (g : MvPolynomial (Fin N) B →+* C))
  rw [← hk] at e4
  rw [e4] at e3
  have e5 := height_ker_add t N ht g hg
  have e6 := hP.height_add_ringKrullDim_quotient (RingHom.ker f)
  rw [ringKrullDim_eq_of_ringEquiv (RingHom.quotientKerEquivOfSurjective hf)] at e6
  have f1 : (RingHom.ker G).height ≠ ⊤ := Ideal.height_ne_top (Ideal.IsPrime.ne_top inferInstance)
  have key : (((RingHom.ker G).height : ℕ∞) : WithBot ℕ∞) + 𝔪.height =
      (((RingHom.ker G).height : ℕ∞) : WithBot ℕ∞) + (ringKrullDim B + t) := by
    rw [← WithBot.coe_add, ← e2, e1, ← e6, ← e5, e3, WithBot.coe_add]
    abel
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp f1
  rw [← hn] at key
  exact (ENat.WithBot.natCast_add_cancel).mp key
end
