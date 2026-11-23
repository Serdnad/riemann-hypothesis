module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.Bundle009
public import GroundTheory.GlobalFields.IdeleGroups.LocalNorms
public import GroundTheory.GlobalFields.IdeleGroups.LocalNormsEverywhere
import GroundTheory.GlobalFields.KummerTheory.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr
public import Mathlib.GroupTheory.Nilpotent
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.Bundle006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Bundle011
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle007
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
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.TwSingle
import Mathlib.Tactic.ReduceModChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.StickelbergerTheorem.StickelbergerAt

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Stick UpperTheory.V.FW
open scoped nonZeroDivisors

private theorem ideal_step {R : Type} [CommRing R] [IsDedekindDomain R] (c : R ≃+* R) (P I : Ideal R) (a : R)
    (hP : P ≠ 0) (hI : I ≠ 0) (ha : a ≠ 0) (hc : P.map c = P) (h : I * I.map c = Ideal.span {a}) :
    ∃ b t : R, b * c b = a * t ∧ ∀ w : Ideal R, w.IsPrime → P ≤ w → t ∉ w := by
  obtain ⟨b, hb⟩ := IsDedekindDomain.exists_sup_span_eq (I := I * P) (J := I) Ideal.mul_le_left (mul_ne_zero hI hP)
  obtain ⟨J, hJ⟩ : I ∣ Ideal.span {b} := Ideal.dvd_iff_le.2 (hb ▸ le_sup_right)
  have h1 : P ⊔ J = ⊤ := by
    rw [hJ, ← Ideal.mul_sup] at hb
    have := mul_left_cancel₀ hI (hb.trans (mul_one I).symm)
    rwa [Ideal.one_eq_top] at this
  have h2 : P ⊔ J.map c = ⊤ := by
    have := congrArg (Ideal.map c) h1
    rwa [Ideal.map_sup, hc, Ideal.map_top] at this
  have h3 : Ideal.span {b * c b} = Ideal.span {a} * (J * J.map c) := by
    have := congrArg (Ideal.map c) hJ
    rw [Ideal.map_span, Set.image_singleton, Ideal.map_mul] at this
    rw [← Ideal.span_singleton_mul_span_singleton, hJ, this, ← h]; ring
  have h4 : b * c b ∈ Ideal.span {a} :=
    (Ideal.span_singleton_le_iff_mem _).1 (h3 ▸ Ideal.mul_le_left)
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton.1 h4
  refine ⟨b, t, ht, fun w hw hPw htw => ?_⟩
  rw [ht, ← Ideal.span_singleton_mul_span_singleton] at h3
  have h5 := mul_left_cancel₀ (by simpa using ha) h3
  have h6 : J * J.map c ≤ w := h5 ▸ (Ideal.span_singleton_le_iff_mem _).2 htw
  rcases hw.mul_le.1 h6 with h7 | h7
  · exact hw.ne_top (top_le_iff.1 (h1 ▸ sup_le hPw h7))
  · exact hw.ne_top (top_le_iff.1 (h2 ▸ sup_le hPw h7))

private theorem norm_cm (K : Type) [Field K] [NumberField K] [IsCMField K] (b : K) :
    algebraMap (maximalRealSubfield K) K (Algebra.norm (maximalRealSubfield K) b) = b * IsCMField.complexConj K b := by
  classical
  have hcard : Fintype.card (K ≃ₐ[maximalRealSubfield K] K) = 2 := by
    rw [← Nat.card_eq_fintype_card, ← Subgroup.card_top, ← IsCMField.zpowers_complexConj_eq_top, Nat.card_zpowers,
      IsCMField.orderOf_complexConj]
  have hne := (IsCMField.complexConj_ne_one K).symm
  have huniv : (Finset.univ : Finset (K ≃ₐ[maximalRealSubfield K] K)) = {1, IsCMField.complexConj K} :=
    (Finset.eq_univ_of_card _ (by rw [Finset.card_pair hne, hcard])).symm
  rw [Algebra.norm_eq_prod_automorphisms, huniv, Finset.prod_pair hne]
  rfl

theorem UpperTheory.V.FW.locFin :
    ∀ (K : Type) [Field K] [NumberField K] [IsCMField K] (x : (maximalRealSubfield K)ˣ) (a : 𝓞 K) (I : (Ideal (𝓞 K))⁰), UnrFin K → (a : K) = algebraMap (maximalRealSubfield K) K x → (I * idMap (cE K) I).1 = Ideal.span {a} → ∀ v, GroundTheory.Global.IdeleGroup.finiteProj v (GroundTheory.Global.IdeleGroup.diagonal (maximalRealSubfield K) x) ∈ (GroundTheory.Global.IdeleNorm.finiteLocalNorm K v).range := by
  intro K _ _ _ x a I hunr hax hI v
  have haK : (a : K) ≠ 0 := by rw [hax]; simp
  have ha : a ≠ 0 := fun h => haK (by rw [h]; rfl)
  obtain ⟨w⟩ := GroundTheory.Global.nonempty_placesOver K v
  have hw : w.1.asIdeal.LiesOver v.asIdeal := inferInstance
  have hP : v.asIdeal.map (algebraMap (𝓞 (maximalRealSubfield K)) (𝓞 K)) ≠ 0 :=
    fun h => v.ne_bot ((Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective _ _)).1 h)
  have hc : (v.asIdeal.map (algebraMap (𝓞 (maximalRealSubfield K)) (𝓞 K))).map (RingOfIntegers.mapRingEquiv (cE K)) =
      v.asIdeal.map (algebraMap (𝓞 (maximalRealSubfield K)) (𝓞 K)) := by
    have : ((RingOfIntegers.mapRingEquiv (cE K) : 𝓞 K ≃+* 𝓞 K) : 𝓞 K →+* 𝓞 K).comp (algebraMap (𝓞 (maximalRealSubfield K)) (𝓞 K)) = algebraMap (𝓞 (maximalRealSubfield K)) (𝓞 K) := by
      ext y
      exact (IsCMField.complexConj K).commutes (y : maximalRealSubfield K)
    rw [← Ideal.map_coe, Ideal.map_map, this]
  obtain ⟨b, t, hbt, ht⟩ := ideal_step (RingOfIntegers.mapRingEquiv (cE K)) _ I.1 a hP (nonZeroDivisors.ne_zero I.2) ha hc hI
  have htw : t ∉ w.1.asIdeal := ht _ w.1.isPrime (Ideal.map_le_iff_le_comap.2 hw.over.le)
  have ht0 : t ≠ 0 := fun h => htw (h ▸ zero_mem _)
  have hb0 : (b : K) ≠ 0 := by
    intro h
    have : b = 0 := by simpa using h
    rw [this, zero_mul] at hbt
    exact mul_ne_zero ha ht0 hbt.symm
  set n : (maximalRealSubfield K)ˣ := Units.map (Algebra.norm (maximalRealSubfield K)) (Units.mk0 (b : K) hb0) with hn
  have hy : algebraMap (maximalRealSubfield K) K ((n * x⁻¹ : (maximalRealSubfield K)ˣ) : maximalRealSubfield K) = (t : K) := by
    have h1 : algebraMap (maximalRealSubfield K) K n = (a : K) * t :=
      (norm_cm K b).trans (congrArg (fun z : 𝓞 K => (z : K)) hbt)
    rw [Units.val_mul, map_mul, h1, Units.val_inv_eq_inv_val, map_inv₀, ← hax]
    field_simp
  have hv : v.valuation (maximalRealSubfield K) ((n * x⁻¹ : (maximalRealSubfield K)ˣ) : maximalRealSubfield K) = 1 := by
    have h1 := HeightOneSpectrum.valuation_liesOver K v w.1 ((n * x⁻¹ : (maximalRealSubfield K)ˣ) : maximalRealSubfield K)
    rw [hy, (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := K) w.1).2 htw] at h1
    apply (pow_eq_one_iff.1 h1).resolve_right
    rw [← Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal w.1.asIdeal v.ne_bot]
    exact Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver _ v.ne_bot
  have h1 : GroundTheory.Global.IdeleGroup.finiteProj v (GroundTheory.Global.IdeleGroup.diagonal (maximalRealSubfield K) n) ∈
      (GroundTheory.Global.IdeleNorm.finiteLocalNorm K v).range := by
    rw [hn, ← GroundTheory.Global.ideleNorm_diagonal, GroundTheory.Global.IdeleNorm.finiteProj_ideleNorm]
    exact ⟨_, rfl⟩
  have h2 : GroundTheory.Global.IdeleGroup.finiteProj v (GroundTheory.Global.IdeleGroup.diagonal (maximalRealSubfield K) (n * x⁻¹)) ∈
      (GroundTheory.Global.IdeleNorm.finiteLocalNorm K v).range := by
    refine Subgroup.map_le_range _ (GroundTheory.Global.IdeleNorm.integerUnitsOver K v) ?_
    rw [GroundTheory.Global.IdeleNorm.map_integerUnitsOver_eq_of_ramificationIdx_eq_one v w (hunr w.1)]
    refine HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.2 ?_
    rw [GroundTheory.Global.IdeleGroup.coe_finiteProj_diagonal]
    exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _).trans hv
  have h3 := mul_mem (inv_mem h2) h1
  rwa [← map_inv, ← map_inv, ← map_mul, ← map_mul, mul_inv_rev, inv_inv, inv_mul_cancel_right] at h3
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Stick UpperTheory.V.FW
open scoped nonZeroDivisors

private theorem aH_lc {H M : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [AddCommGroup M]
    (φ : H → M) (h : ∀ a b, φ (a * b) = φ a + φ b) (N : Set H) (hN : IsOpen N) (h1 : (1 : H) ∈ N)
    (h0 : ∀ u ∈ N, φ u = 0) : IsLocallyConstant φ := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have ho : IsOpen ((fun y => x⁻¹ * y) ⁻¹' N) := hN.preimage (by fun_prop)
  filter_upwards [ho.mem_nhds (show x ∈ (fun y => x⁻¹ * y) ⁻¹' N by simpa using h1)] with y hy
  have := h x (x⁻¹ * y)
  rw [h0 _ hy, add_zero, mul_inv_cancel_left] at this
  exact this

private theorem aH_one {H M : Type} [Group H] [AddCommGroup M]
    (φ : H → M) (h : ∀ a b, φ (a * b) = φ a + φ b) : φ 1 = 0 := by
  have := h 1 1
  rw [mul_one] at this
  exact left_eq_add.1 this

private theorem aH_inv {H M : Type} [Group H] [AddCommGroup M]
    (φ : H → M) (h : ∀ a b, φ (a * b) = φ a + φ b) (a : H) : φ a⁻¹ = -φ a := by
  have := h a⁻¹ a
  rw [inv_mul_cancel, aH_one φ h] at this
  exact eq_neg_of_add_eq_zero_left this.symm

private theorem aH_mem {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] (l : ℕ)
    (U : Subgroup (G F Ω)) [hU : U.Normal] (φ : U → ZMod l) :
    φ ∈ EqHom 1 U (Formalism.GaloisCohomology.scalRep (ZMod l) (1 : G F Ω →* (ZMod l)ˣ)) ↔
      IsLocallyConstant φ ∧ (∀ a b, φ (a * b) = φ a + φ b) ∧
        (∀ (A : ValuationSubring Ω) (u : U), u.1 ∈ Ine (F := F) A → φ u = 0) ∧
        ∀ (g : G F Ω) (u : U), φ ⟨g * u * g⁻¹, hU.conj_mem _ u.2 g⟩ = φ u := by
  rw [EqHom, Submodule.mem_inf, Submodule.mem_iInf]
  constructor
  · rintro ⟨⟨h1, h2, h3, -⟩, h4⟩
    refine ⟨h1, h2, h3, fun g u => ?_⟩
    have := h4 g u ⟨g * u * g⁻¹, hU.conj_mem _ u.2 g⟩ (fun x => by
      show g (u.1 (g.symm (g x))) = g (u.1 x)
      rw [AlgEquiv.symm_apply_apply])
    rw [this, scalRep_apply]
    simp
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨⟨h1, h2, h3, fun A hA => ?_⟩, fun g u u' h => ?_⟩
    · simp at hA
    · rw [scalRep_apply, ← h4 g u]
      have : u' = ⟨g * u * g⁻¹, hU.conj_mem _ u.2 g⟩ := Subtype.ext (AlgEquiv.ext fun x => by
        have := h (g.symm x)
        rw [show g.toRingEquiv (g.symm x) = x from g.apply_symm_apply x] at this
        exact this)
      rw [this]
      simp

theorem UpperTheory.V.FW.ambHom :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (K : Type) [Field K] [NumberField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure K Ω] [IsGalois F K] (l : ℕ) [Fact l.Prime] (ζ : F), IsPrimitiveRoot ζ l → IsCyclic Gal(K/F) → (∀ A : ValuationSubring Ω, ¬ A.valuation (l : Ω) < 1 → Ine (F := F) A ≤ galOf F K Ω) → Finite (EqHom 1 (galOf F K Ω) (Formalism.GaloisCohomology.scalRep (ZMod l) (1 : G F Ω →* (ZMod l)ˣ))) → Nat.card (EqHom 1 (galOf F K Ω) (Formalism.GaloisCohomology.scalRep (ZMod l) (1 : G F Ω →* (ZMod l)ˣ))) ≤ Set.ncard {φ : G F Ω → ZMod l | IsLocallyConstant φ ∧ (∀ a b, φ (a * b) = φ a + φ b) ∧ ∀ A : ValuationSubring Ω, ¬ A.valuation (l : Ω) < 1 → ∀ g ∈ Ine (F := F) A, φ g = 0} := by
  intro F Ω _ _ _ _ _ K _ _ _ _ _ _ _ l hl ζ hζ hc hI hfin
  haveI : IsGalois F Ω := {}
  have hUo : IsOpen (galOf F K Ω : Set (G F Ω)) := (galEmbTop F K Ω).2.1
  have hcyc : IsCyclic (G F Ω ⧸ galOf F K Ω) := by
    obtain ⟨q1, q2, -⟩ := galQuot F K Ω
    have e := (QuotientGroup.quotientMulEquivOfEq q2.symm).trans (QuotientGroup.quotientKerEquivOfSurjective _ q1)
    exact isCyclic_of_surjective e.symm e.symm.surjective
  have hn : (galOf F K Ω).Normal := inferInstance
  set U := galOf F K Ω with hUdef
  have hm := aH_mem l U
  set E := EqHom 1 U (Formalism.GaloisCohomology.scalRep (ZMod l) (1 : G F Ω →* (ZMod l)ˣ)) with hE
  let N : Subgroup (G F Ω) :=
    { carrier := {g | ∃ h : g ∈ U, ∀ φ : E, φ.1 ⟨g, h⟩ = 0}
      one_mem' := ⟨U.one_mem, fun φ => aH_one φ.1 ((hm _).1 φ.2).2.1⟩
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨U.mul_mem ha hb, fun φ => ?_⟩
        have := ((hm _).1 φ.2).2.1 ⟨a, ha⟩ ⟨b, hb⟩
        rw [ha', hb', add_zero] at this
        exact this
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨U.inv_mem ha, fun φ => ?_⟩
        have := aH_inv φ.1 ((hm _).1 φ.2).2.1 ⟨a, ha⟩
        rw [ha', neg_zero] at this
        exact this }
  have hN : ∀ g, g ∈ N ↔ ∃ h : g ∈ U, ∀ φ : E, φ.1 ⟨g, h⟩ = 0 := fun _ => Iff.rfl
  haveI : N.Normal := ⟨fun u ⟨hu, hu'⟩ g => ⟨hn.conj_mem u hu g, fun φ =>
    (((hm _).1 φ.2).2.2.2 g ⟨u, hu⟩).trans (hu' φ)⟩⟩
  have hNo : IsOpen (N : Set (G F Ω)) := by
    have : (N : Set (G F Ω)) = Subtype.val '' (⋂ φ : E, φ.1 ⁻¹' {0}) := by
      ext g
      simp only [SetLike.mem_coe, hN, Set.mem_image, Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff]
      exact ⟨fun ⟨h, h'⟩ => ⟨⟨g, h⟩, h', rfl⟩, fun ⟨u, h, e⟩ => e ▸ ⟨u.2, h⟩⟩
    rw [this]
    exact hUo.isOpenMap_subtype_val _ (isOpen_iInter_of_finite fun φ => ((hm _).1 φ.2).1 _)
  haveI : Finite (G F Ω ⧸ N) := N.quotient_finite_of_isOpen hNo
  haveI : N.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hcomm : ∀ g, ∀ u ∈ U, g * u * g⁻¹ * u⁻¹ ∈ N := fun g u hu => by
    refine ⟨U.mul_mem (hn.conj_mem u hu g) (U.inv_mem hu), fun φ => ?_⟩
    obtain ⟨-, h2, -, h4⟩ := (hm _).1 φ.2
    have := h2 ⟨g * u * g⁻¹, hn.conj_mem u hu g⟩ (⟨u, hu⟩ : U)⁻¹
    rw [aH_inv φ.1 h2, h4 g ⟨u, hu⟩, add_neg_cancel] at this
    exact this
  have hIN : ∀ (A : ValuationSubring Ω) (u : U), u.1 ∈ Ine (F := F) A → u.1 ∈ N := fun A u hu =>
    ⟨u.2, fun φ => ((hm _).1 φ.2).2.2.1 A u hu⟩
  have key := homCyc l (G F Ω) U N (fun g h => h.1) hcyc hcomm
  have e1 : Nat.card E = Nat.card {φ : U → ZMod l // (∀ a b, φ (a * b) = φ a + φ b) ∧ ∀ u : U, u.1 ∈ N → φ u = 0} := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun φ => ⟨fun h => ⟨((hm _).1 h).2.1, fun u hu => hu.2 ⟨φ, h⟩⟩, ?_⟩)
    rintro ⟨h2, h0⟩
    refine (hm _).2 ⟨aH_lc φ h2 (Subtype.val ⁻¹' N) (hNo.preimage continuous_subtype_val) N.one_mem h0, h2,
      fun A u hu => h0 u (hIN A u hu), fun g u => ?_⟩
    have := h2 ⟨g * u * g⁻¹, hn.conj_mem u u.2 g⟩ u⁻¹
    rw [aH_inv φ h2, h0 _ (hcomm g u u.2)] at this
    exact add_neg_eq_zero.1 this.symm
  have hf := finChar F Ω l l ζ hl.out.ne_zero hl.out.ne_zero hζ
  rw [e1]
  refine key.trans ?_
  rw [← Nat.card_coe_set_eq]
  haveI := hf.to_subtype
  refine Nat.card_le_card_of_injective (fun φ => ⟨φ.1, aH_lc φ.1 φ.2.1 N hNo N.one_mem φ.2.2, φ.2.1,
    fun A hA g hg => φ.2.2 g (hIN A ⟨g, hI A hA hg⟩ hg)⟩) fun a b h => Subtype.ext (Subtype.mk.inj h)
end
