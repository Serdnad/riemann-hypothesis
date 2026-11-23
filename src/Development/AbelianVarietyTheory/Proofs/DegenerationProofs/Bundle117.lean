module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Mathlib.RingTheory.Invariant.Defs
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle006
import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle024
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle065
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle112
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle005
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.QuotientIsAbelianSchemeOfQuotientScheme
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle051
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsQuotientByFiniteGroupOfPoints
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle003
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProjectiveOverRingByChartsAbelianVariety
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
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
public import Mathlib.RingTheory.Invariant.Galois
import Mathlib.RingTheory.PowerSeries.Ideal
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Lemma
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.FiniteAlgebraLocalCompletion
public import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
public import Mathlib.RingTheory.Invariant.Basic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN

namespace GlobalTheory

namespace ResidueGalois

theorem galois_of_isInvariant (A B G : Type) [CommRing A] [CommRing B] [Algebra A B] [Group G]
    [Finite G] [MulSemiringAction G B] [Algebra.IsInvariant A B G] [SMulCommClass G A B]
    (k K : Type) [Field k] [Field K] [Algebra k K] [CharZero k] (p : A →+* k) (q : B →+* K)
    (hp : Function.Surjective p) (hq : Function.Surjective q)
    (h : ∀ x, algebraMap k K (p x) = q (algebraMap A B x)) :
    FiniteDimensional k K ∧ IsGalois k K ∧
      ∀ τ : K ≃ₐ[k] K, ∃ σ : G, ∀ x, q (σ • x) = τ (q x) := by
  let P : Ideal A := RingHom.ker p
  let Q : Ideal B := RingHom.ker q
  have : P.IsPrime := RingHom.ker_isPrime p
  have : Q.IsPrime := RingHom.ker_isPrime q
  have : Q.LiesOver P := ⟨by
    ext x
    simp only [P, Q, Ideal.under, Ideal.mem_comap, RingHom.mem_ker, ← h, map_eq_zero]⟩
  let _ : Algebra (A ⧸ P) k := (RingHom.kerLift p).toAlgebra
  let _ : Algebra (B ⧸ Q) K := (RingHom.kerLift q).toAlgebra
  let _ : Algebra (A ⧸ P) K := ((algebraMap k K).comp (RingHom.kerLift p)).toAlgebra
  have : IsScalarTower (A ⧸ P) k K := .of_algebraMap_eq fun _ => rfl
  have : IsScalarTower (A ⧸ P) (B ⧸ Q) K := .of_algebraMap_eq fun x => by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact h x
  have : FaithfulSMul (A ⧸ P) k :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (RingHom.kerLift_injective p)
  have : FaithfulSMul (B ⧸ Q) K :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (RingHom.kerLift_injective q)
  have : IsFractionRing (A ⧸ P) k := IsFractionRing.of_field _ _ fun z => by
    obtain ⟨x, rfl⟩ := hp z
    exact ⟨Ideal.Quotient.mk P x, 1, by rw [map_one, div_one]; rfl⟩
  have : IsFractionRing (B ⧸ Q) K := IsFractionRing.of_field _ _ fun z => by
    obtain ⟨x, rfl⟩ := hq z
    exact ⟨Ideal.Quotient.mk Q x, 1, by rw [map_one, div_one]; rfl⟩
  have hn : Normal k K := Ideal.IsFractionRing.normal G P Q k K
  have hs : Algebra.IsSeparable k K := inferInstance
  refine ⟨Ideal.IsFractionRing.finite_of_isInvariant G P Q k K, { }, fun τ => ?_⟩
  obtain ⟨σ, rfl⟩ := IsFractionRing.stabilizerHom_surjective G P Q k K τ
  exact ⟨σ.1, fun x => (IsFractionRing.stabilizerHom_apply_apply_mk G P Q k K σ x).symm⟩

theorem map_maximalIdeal_le {A B : Type} [CommRing A] [CommRing B] [IsLocalRing A]
    [IsLocalRing B] (f : A →+* B) (hf : f.IsIntegral) :
    (IsLocalRing.maximalIdeal A).map f ≤ IsLocalRing.maximalIdeal B := by
  have := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' f hf (IsLocalRing.maximalIdeal B)
  rw [Ideal.map_le_iff_le_comap, IsLocalRing.eq_maximalIdeal this]

end ResidueGalois

theorem exists_cDvr_residue_galois : ∀ (V V' : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [CommRing V'] [IsDomain V'] [IsLocalRing V'], CDvr V → CDvr V' → (∀ n : ℕ, n ≠ 0 → IsUnit (n : V)) → ∀ g : V →+* V', Function.Injective g → g.Finite → ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (j : V' →+* W), CDvr W ∧ Function.Injective j ∧ (IsLocalRing.maximalIdeal V').map j ≤ IsLocalRing.maximalIdeal W ∧ (IsLocalRing.maximalIdeal V).map (j.comp g) ≤ IsLocalRing.maximalIdeal W ∧ ∀ (k K : Type) [Field k] [Field K] [Algebra k K] (p : V →+* k) (q : W →+* K), Function.Surjective p → Function.Surjective q → (∀ x, algebraMap k K (p x) = q (j (g x))) → FiniteDimensional k K ∧ IsGalois k K ∧ ∀ τ : K ≃ₐ[k] K, ∃ σ : W ≃+* W, (∀ x, σ (j (g x)) = j (g x)) ∧ ∀ x, q (σ x) = τ (q x) := by
  intro V V' _ _ _ _ _ _ hV _ hu g hg hfin
  obtain ⟨hd, hc, h0⟩ := (cDvr_iff V).1 hV
  let _ : Algebra V V' := g.toAlgebra
  have : Module.Finite V V' := hfin
  have : FaithfulSMul V V' := (faithfulSMul_iff_algebraMap_injective _ _).2 hg
  let K := FractionRing V
  let K' := FractionRing V'
  let _ : Algebra K K' := FractionRing.liftAlgebra V K'
  have : IsScalarTower V K K' := FractionRing.isScalarTower_liftAlgebra V K'
  have : FiniteDimensional K K' := inferInstance
  have : CharZero K := IsFractionRing.charZero_of_isFractionRing V
  let L := IntermediateField.normalClosure K K' (AlgebraicClosure K')
  have : FiniteDimensional K L := inferInstance
  have : IsGalois K L := inferInstance
  let W := integralClosure V L
  have hB : Module.Finite V W := IsIntegralClosure.finite V K L _
  have hBd : IsDiscreteValuationRing W := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_dvr V K L
  have : IsFractionRing W L := IsIntegralClosure.isFractionRing_of_finite_extension V K L W
  let i : V' →ₐ[V] L :=
    ((IsScalarTower.toAlgHom K K' L).restrictScalars V).comp (IsScalarTower.toAlgHom V V' K')
  have hi : Function.Injective i :=
    (algebraMap K' L).injective.comp (IsFractionRing.injective V' K')
  let j : V' →ₐ[V] W := i.codRestrict W fun x => (Algebra.IsIntegral.isIntegral x).map i
  have hj : Function.Injective j := fun x y h => hi (congrArg Subtype.val h)
  have hjg : ∀ x, j (g x) = algebraMap V W x := fun x => j.commutes x
  have hjg' : (j : V' →+* W).comp g = algebraMap V W := RingHom.ext hjg
  have hint : ((j : V' →+* W).comp g).IsIntegral := by
    rw [hjg']
    exact fun x => Algebra.IsIntegral.isIntegral x
  have : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
  refine ⟨W, inferInstance, inferInstance, inferInstance, (j : V' →+* W),
    (cDvr_iff W).2 ⟨hBd, CompleteFiniteExtension.isAdicComplete_of_finite_local V W,
      inferInstance⟩, hj,
    ResidueGalois.map_maximalIdeal_le _ (RingHom.IsIntegral.tower_top g _ hint),
    ResidueGalois.map_maximalIdeal_le _ hint, ?_⟩
  intro k K₁ _ _ _ p q hp hq h
  have : CharZero k := ⟨fun m n hmn => by
    by_contra hne
    wlog hlt : m < n generalizing m n
    · exact this n m hmn.symm (Ne.symm hne) (lt_of_le_of_ne (not_lt.1 hlt) (Ne.symm hne))
    have := ((hu (n - m) (by omega)).map p).ne_zero
    rw [map_natCast, Nat.cast_sub hlt.le, hmn, sub_self] at this
    exact this rfl⟩
  have : Algebra.IsInvariant V W (W ≃ₐ[V] W) := Algebra.isInvariant_of_isGalois' V K L W
  have : Finite (W ≃ₐ[V] W) := Finite.of_equiv _ (galRestrict V K L W).toEquiv
  obtain ⟨h₁, h₂, h₃⟩ := ResidueGalois.galois_of_isInvariant V W (W ≃ₐ[V] W) k K₁ p q hp hq
    fun x => (h x).trans (congrArg q (hjg x))
  refine ⟨h₁, h₂, fun τ => ?_⟩
  obtain ⟨σ, hσ⟩ := h₃ τ
  refine ⟨σ.toRingEquiv, fun x => ?_, hσ⟩
  change σ (j (g x)) = j (g x)
  rw [hjg, AlgEquiv.commutes]

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN

namespace GlobalTheory
namespace ArcLocus

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

theorem closedPoint_notMem (Y : Model Xo c β) {O' : Type} [CommRing O'] [IsDomain O'] {b : O →+* O'}
    (a : ArcIn D l β O' b) {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (f : O' →+* R) (u : R)
    (χ : Sp R ⟶ Y.X) (h : Y.HasArcData a (IsLocalRing.maximalIdeal R) f u χ) :
    χ (IsLocalRing.closedPoint R) ∉ abLocus Y.t.G := by
  intro h₁
  obtain ⟨W⟩ := (Y.hasArcData_iff a _ f u χ).1 h
  have h₂ := (abLocus_pullback abLocusOne Y.t.semi W.m.cart.1 _).1 h₁
  have hmax : (IsLocalRing.maximalIdeal R ^ (0 + 1)).IsMaximal := by
    rw [zero_add, pow_one]; infer_instance
  have hF : IsField (R ⧸ IsLocalRing.maximalIdeal R ^ (0 + 1)) :=
    (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).1 hmax
  obtain ⟨p, hp⟩ : IsLocalRing.closedPoint R ∈ Set.range (PrimeSpectrum.comap
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (0 + 1)))) := by
    rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker, zero_add, pow_one]
    exact le_refl (IsLocalRing.maximalIdeal R)
  let g := W.P.U.gt 0
  have m : Mono g.i := ⟨fun a b h => g.isKernel.hom_ext h (toUnit_unique _ _)⟩
  have hp' : thick R (IsLocalRing.maximalIdeal R) 0 p ∈ abLocus W.t.G := by
    rw [← hp] at h₂; exact h₂
  have hs := ArcNotAbelian.subsingleton_of_mem_abLocus W.t.G W.t.semi _ hF _ p hp' W.P.D.toPre.X g.i g.i_hom
  have hn : Nontrivial a.D₀.X := a.nontriv
  exact not_subsingleton _ (W.e.toEquiv.subsingleton)

theorem exists_trait (R : Type) [CommRing R] [IsDomain R] [CharZero R] [IsNoetherianRing R] (x : PrimeSpectrum R)
    (hx : x.asIdeal ≠ ⊥) :
    ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (φ : R →+* W)
      (gam : FractionRing R →+* FractionRing W), CDvr W ∧ (∀ r, gam (algebraMap R _ r) = algebraMap W _ (φ r)) ∧
      (IsLocalRing.maximalIdeal W).comap φ = x.asIdeal := by
  obtain ⟨W, _, _, _, _, φ, h1, h2⟩ :=
    exists_complete_discreteValuationRing_of_prime_lt (⊥ : Ideal R) x.asIdeal (bot_lt_iff_ne_bot.2 hx)
  have hφ : Function.Injective φ := (RingHom.injective_iff_ker_eq_bot φ).2 h1
  have hφ' : Function.Injective ((algebraMap W (FractionRing W)).comp φ) :=
    (IsFractionRing.injective W (FractionRing W)).comp hφ
  exact ⟨W, inferInstance, inferInstance, inferInstance, φ, IsFractionRing.lift hφ',
    ⟨inferInstance, inferInstance, charZero_of_injective_ringHom hφ⟩,
    fun r => IsFractionRing.lift_algebraMap hφ' r, h2⟩

theorem j_mem (Y : Model Xo c β) (p : Xo.XF c) : Y.j p ∈ abLocus Y.t.G := by
  have hz : Y.jQ p ∈ pullback.fst Y.s (spMap β) ⁻¹' abLocus Y.t.G := by
    rw [Y.ab_gen]; exact ⟨_, rfl⟩
  exact hz

theorem mem_range_j (Y : Model Xo c β) (z : Y.X) (hz : z ∈ abLocus Y.t.G) (p : Xo.XF c)
    (hp : Y.s z = Y.s (Y.j p)) : z ∈ Set.range Y.j := by
  have h₁ : z ∈ Set.range (pullback.fst Y.s (spMap β)) := by
    rw [Scheme.Pullback.range_fst, Set.mem_preimage, hp]
    have : Y.j p ∈ Set.range (pullback.fst Y.s (spMap β)) := ⟨Y.jQ p, rfl⟩
    rwa [Scheme.Pullback.range_fst] at this
  obtain ⟨w, rfl⟩ := h₁
  have h₂ : w ∈ Set.range Y.jQ := by rw [← Y.ab_gen]; exact hz
  obtain ⟨q, rfl⟩ := h₂
  exact ⟨q, rfl⟩

theorem exists_jK_eq_bot (R : Type) [CommRing R] [IsDomain R] :
    ∃ pt : Sp (FractionRing R), jK R pt = (⊥ : PrimeSpectrum R) := by
  refine ⟨(⊥ : PrimeSpectrum (FractionRing R)), PrimeSpectrum.ext ?_⟩
  exact (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R (FractionRing R))

end ArcLocus


open ArcLocus in
theorem arc_abLocus_of_traitData : Laws → Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (W₀ : ValuationSubring ℂ) (Y : Model Xo c (c.V W₀).subtype) (O' : Type) [CommRing O'] [IsDomain O'] [CharZero O'] (b : c.V W₀ →+* O') (a : ArcIn D l (c.V W₀).subtype O' b) (ϖ : O'), ArcBase O' ϖ → ∀ (y : Sp (FractionRing (PowerSeries O')) ⟶ Xo.XF c) (χ : Sp (PowerSeries O') ⟶ Y.X), jK _ ≫ χ = y ≫ Y.j → TraitData Y a (RingHom.id _) y → χ ≫ Y.s = spMap (PowerSeries.C (R := O')) ≫ spMap b ∧ (∀ x : Sp (PowerSeries O'), χ x ∈ abLocus Y.t.G ↔ PowerSeries.X ∉ x.asIdeal) ∧ ∀ x : Sp (PowerSeries O'), PowerSeries.C ϖ * PowerSeries.X ∉ x.asIdeal → χ x ∈ Set.range Y.j := by
  intro _ _ E _ _ _ H D l Xo c W₀ Y O' _ _ _ b a ϖ hb y χ hχ hT
  have hN : IsNoetherianRing O' := by
    rcases hb with h | h
    · letI := h.1.toField; infer_instance
    · have := h.1; infer_instance
  have hc : CharZero (PowerSeries O') := charZero_of_injective_ringHom (PowerSeries.C_injective (R := O'))
  obtain ⟨pt, hpt⟩ := exists_jK_eq_bot (PowerSeries O')
  have h0 : χ (⊥ : PrimeSpectrum (PowerSeries O')) = Y.j (y pt) := by
    rw [← hpt, ← Scheme.Hom.comp_apply, hχ, Scheme.Hom.comp_apply]
  have h1 : χ ≫ Y.s = spMap (PowerSeries.C (R := O')) ≫ spMap b := by
    have hd : IsDominant (jK (PowerSeries O')) := by
      constructor
      exact (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical (algebraMap (PowerSeries O') (FractionRing (PowerSeries O')))).2
        (by rw [(RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective (PowerSeries O') _)]; exact bot_le)
    refine ext_of_isDominant (jK (PowerSeries O')) ?_
    rw [← Category.assoc, hχ, Category.assoc, hT.1]
    have : spMap (RingHom.id (PowerSeries O')) = 𝟙 _ := Spec.map_id _
    rw [this, Category.id_comp]
  have h2 : ∀ x : Sp (PowerSeries O'), χ x ∈ abLocus Y.t.G ↔ PowerSeries.X ∉ x.asIdeal := by
    intro x
    by_cases hx : x.asIdeal = ⊥
    · have e : x = (⊥ : PrimeSpectrum (PowerSeries O')) := PrimeSpectrum.ext hx
      refine iff_of_true ?_ ?_
      · rw [e, h0]; exact j_mem Y _
      · rw [hx]; exact PowerSeries.X_ne_zero
    obtain ⟨W, _, _, _, φ, gam, hW, hg, hφ⟩ := exists_trait (PowerSeries O') x hx
    have key : spMap gam ≫ jK (PowerSeries O') = jK W ≫ spMap φ := by
      show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
      rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
      congr 2
      exact RingHom.ext hg
    have ht := hT.2 W hW φ gam hg (spMap φ ≫ χ) (by rw [← hχ, ← Category.assoc, key, Category.assoc])
    have hu : PowerSeries.X ∉ x.asIdeal ↔ IsUnit (φ PowerSeries.X) := by
      rw [← hφ, Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]
    have hcl : spMap φ (IsLocalRing.closedPoint W) = x := PrimeSpectrum.ext hφ
    rw [hu]
    refine ⟨fun hab => ?_, fun h => ht.1 h ⟨IsLocalRing.closedPoint W, (Scheme.Hom.comp_apply _ _ _).trans (congrArg χ hcl)⟩⟩
    by_contra h
    obtain ⟨W', _, _, _, io, -, -, hfin, hA⟩ := ht.2 h
    refine closedPoint_notMem Y a _ _ _ hA ?_
    have hcl' : spMap io (IsLocalRing.closedPoint W') = IsLocalRing.closedPoint W := by
      refine PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal ?_)
      exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' io hfin.to_isIntegral (IsLocalRing.maximalIdeal W')
    have e : (spMap io ≫ spMap φ ≫ χ) (IsLocalRing.closedPoint W') = χ x :=
      (Scheme.Hom.comp_apply _ _ _).trans ((congrArg (spMap φ ≫ χ) hcl').trans
        ((Scheme.Hom.comp_apply _ _ _).trans (congrArg χ hcl)))
    rw [e]
    exact hab
  refine ⟨h1, h2, fun x hx => mem_range_j Y _ ((h2 x).2 fun h => hx (Ideal.mul_mem_left _ _ h)) (y pt) ?_⟩
  have hC : ∀ z : Sp (PowerSeries O'), PowerSeries.C ϖ * PowerSeries.X ∉ z.asIdeal →
      spMap (PowerSeries.C (R := O')) z = (⊥ : PrimeSpectrum O') := by
    intro z hz
    refine PrimeSpectrum.ext ?_
    change z.asIdeal.comap (PowerSeries.C (R := O')) = ⊥
    have hzp := z.isPrime
    rcases hb with h | h
    · letI := h.1.toField
      exact Ideal.eq_bot_of_prime _
    · have := h.1
      by_contra hne
      have hm := IsLocalRing.eq_maximalIdeal (Ring.DimensionLEOne.maximalOfPrime hne inferInstance)
      have : ϖ ∈ z.asIdeal.comap (PowerSeries.C (R := O')) := by
        rw [hm]; exact h.2.1.not_isUnit
      exact hz (Ideal.mul_mem_right _ _ this)
  have hb0 : spMap (PowerSeries.C (R := O')) (⊥ : PrimeSpectrum (PowerSeries O')) = (⊥ : PrimeSpectrum O') :=
    PrimeSpectrum.ext ((RingHom.injective_iff_ker_eq_bot _).1 (PowerSeries.C_injective (R := O')))
  have h3 : ∀ z : Sp (PowerSeries O'), Y.s (χ z) = spMap b (spMap (PowerSeries.C (R := O')) z) := fun z => by
    rw [← Scheme.Hom.comp_apply, h1, Scheme.Hom.comp_apply]
  rw [← h0, h3, hC x hx]
  exact ((h3 _).trans (congrArg (spMap b) hb0)).symm

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN

theorem GlobalTheory.LN.exists_polAV_of_polAt : Laws → Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] (t : SAB H (Sp R)), PolAt t (jK R) → letI := H.starRing; ∃ (A : PolAV (Sp (FractionRing R))) (oA : A.OAct (𝓞 E)) (gen : (Over.pullback (jK R)).obj t.G ≅ A.A), IsMonHom gen.hom ∧ LBIso (A.L.pull gen.hom.left) (t.PP.L.pull (pullback.fst t.G.hom (jK R))) ∧ ∀ x, (Over.pullback (jK R)).map (t.act.act x) ≫ gen.hom = gen.hom ≫ oA.act x := by
  intro _ _ E _ _ _ H R _ _ t ⟨hp, hA, hK⟩
  let := H.starRing
  obtain ⟨PP', cub, sym, adj, prim, m₁, hm₁⟩ := sabPull CubePf.cubePull (jK R) t
  let t' : SAB H (Spec (CommRingCat.of (FractionRing R))) :=
    ⟨(Over.pullback (jK R)).obj t.G, IsSemiAbelian.pullback _ t.G t.semi,
      Geo.Tor.OAct.pullback _ t.G t.act, PP', cub, sym, adj, prim⟩
  let m₀ : SABMap t' t (jK R) := m₁
  have hm₀ : m₀.cm.F = pullback.fst t.G.hom (jK R) := hm₁
  obtain ⟨w, hw, -⟩ := m₀.lin
  have hL : LBIso t'.PP.L (t.PP.L.pull (pullback.fst t.G.hom (jK R))) := hm₀ ▸ ⟨w, hw⟩
  have hM := pull_isLB t.PP.isLB (pullback.fst t.G.hom (jK R))
  have hL' : LBIso t'.PP.L ((t.PP.L.pull (pullback.fst t.G.hom (jK R))).pull (𝟙 t'.G.left)) :=
    LBIso.chartPull (Geo.Tor.chartPullId _) (Geo.Tor.chartPullPull _ (𝟙 _) (𝟙 _) rfl) hL
  obtain ⟨v, hv⟩ := hL'
  have : IsMonHom (Iso.refl t'.G).hom := inferInstanceAs (IsMonHom (𝟙 t'.G))
  have hid : IsGrpPullback t'.G t'.G (𝟙 _) (𝟙 t'.G.left) := isGrpPullback_of_iso (Iso.refl t'.G)
  have hA' : RelAmple t'.G t'.PP.L :=
    relAmple_pull hid.1 hM t'.PP.isLB ((isGen_iff v).1 hv) ⊤ (isAffineOpen_top _) (fun _ => trivial) hA
  have hK' : KTriv t'.G t'.PP.L := kTriv_pull hid hM t'.PP.isLB ((isGen_iff v).1 hv) hK
  have := t'.semi.smooth
  have := t'.semi.geomConnected
  have : ConnectedSpace ↥t'.G.left :=
    GeometricallyConnected.geometrically_connectedSpace (f := t'.G.hom) (𝟙 _) (𝟙 _) t'.G.hom
      (IsPullback.of_horiz_isIso ⟨by simp⟩)
  obtain ⟨g, hg⟩ := exists_dim_of_preconnected t'.G.hom (Classical.arbitrary _)
  refine ⟨GenericPol.toPolAV t' g hg hp hA' hK', ⟨t'.act.toRingAct, GenericPol.rosatiAdj t'⟩, Iso.refl _,
    inferInstanceAs (IsMonHom (𝟙 t'.G)), ?_,
    fun a => ?_⟩
  · exact LBIso.chartPull (Geo.Tor.chartPullPull t'.PP.L (𝟙 _) (𝟙 _) rfl) (Geo.Tor.chartPullId _) hL
  · exact (Category.comp_id _).trans (Category.id_comp _).symm
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

theorem _root_.GlobalTheory.T.exists_weakNeronModel_birational_groupLaw : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K], SH R K → ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (n : ℕ) (M : Fin n → Model R A), (∀ i, (M i).Irr) → WeakNeron M → ∃ N : Model R A, BirLaw N ∧ ∃ c : ℕ, 1 ≤ c ∧ ∀ a : (𝟙_ (Over (Sp K)) ⟶ A), GenIso N N (transl (a ^ c)).hom := by
  first | exact @GlobalTheory.SS.NeutralModel.exists_birLaw | exact GlobalTheory.SS.NeutralModel.exists_birLaw | (intros; apply GlobalTheory.SS.NeutralModel.exists_birLaw <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory

namespace FiniteQuot

variable {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] [IsCommMonObj A]

lemma translHom_eq (c : 𝟙_ (Over (Sp K)) ⟶ A) : (transl c).hom = (toUnit A ≫ c) * 𝟙 A := rfl

lemma comp_translHom {Z : Over (Sp K)} (g : Z ⟶ A) (c : 𝟙_ (Over (Sp K)) ⟶ A) :
    g ≫ (transl c).hom = (toUnit Z ≫ c) * g := by
  rw [translHom_eq, MonObj.comp_mul, Category.comp_id, comp_toUnit_assoc]

lemma translHom_one : (transl (1 : 𝟙_ (Over (Sp K)) ⟶ A)).hom = 𝟙 A := by
  rw [translHom_eq, MonObj.comp_one, _root_.one_mul]

lemma translHom_mul (a c : 𝟙_ (Over (Sp K)) ⟶ A) :
    (transl (a * c)).hom = (transl a).hom ≫ (transl c).hom := by
  rw [comp_translHom, translHom_eq, translHom_eq, MonObj.comp_mul, ← _root_.mul_assoc,
    _root_.mul_comm (toUnit A ≫ c)]

end FiniteQuot


open FiniteQuot PointQuot AbelianQuotient in
theorem exists_quotient_abelian_by_finite_points :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (A : Over (Sp k)) [GrpObj A], IsAbelianScheme A → ∀ C : Subgroup (𝟙_ (Over (Sp k)) ⟶ A), Finite C → ∃ (B : Over (Sp k)) (_ : GrpObj B) (ψ : A ⟶ B), IsAbelianScheme B ∧ IsMonHom ψ ∧ IsFinite ψ.left ∧ Etale ψ.left ∧ Surjective ψ.left ∧ ∀ (k' : Type) [Field k'] [IsAlgClosed k'] (t : Sp k' ⟶ Sp k) (x : Over.mk t ⟶ A), x ≫ ψ = 1 ↔ ∃ c ∈ C, x = toUnit _ ≫ c := by
  open FiniteQuot PointQuot in
  intro k _ _ A _ hA C hC
  have := hA.comm
  have hq : IsQProjOver A.hom := by
    obtain ⟨N, i, hi, e⟩ := (ProjSpace.isProjBy_iff_isProjOver A.hom).1
      (AbelianProjective.isProjBy_of_isAbelianScheme k A hA)
    exact ⟨N, i, inferInstance, inferInstance, e⟩
  obtain ⟨Y, π, sY, hw, hG, hsep, hlft, -⟩ :=
    ZM.exists_isGaloisCover_of_isQProjOver k A.left A.hom C (fun c => ((transl c.1).hom).left) hq
      (congrArg CommaMorphism.left (translHom_one (A := A)))
      (fun a c => congrArg CommaMorphism.left (translHom_mul a.1 c.1))
      (fun a => Over.w _) (by
        intro K _ _ y a h
        let y' : Over.mk (y ≫ A.hom) ⟶ A := Over.homMk y rfl
        have h' : y' ≫ (transl a.1).hom = y' := Over.OverMorphism.ext h
        have : Nonempty (Over.mk (y ≫ A.hom)).left := inferInstanceAs (Nonempty (PrimeSpectrum K))
        have := epi_toUnit (Over.mk (y ≫ A.hom))
        rw [comp_translHom, mul_eq_right, ← MonObj.comp_one (toUnit _), cancel_epi] at h'
        exact Subtype.ext h')
  let B : Over (Sp k) := Over.mk sY
  let q : A ⟶ B := Over.homMk π hw
  have hfin : IsFinite q.left := hG.fin
  have het : Etale q.left := hG.etale
  have hsurj : Surjective q.left := hG.onto
  have hinv : ∀ c : C, (transl c.1).hom ≫ q = q := fun c => Over.OverMorphism.ext (hG.inv c)
  let x : C → (𝟙_ (Over (Sp k)) ⟶ A) := Subtype.val
  have hmono := mono_constDesc x Subtype.val_injective
  obtain ⟨_, hi⟩ := exists_grpObj_constObj x C Subtype.range_coe
  obtain ⟨_, hcomm, hhom, -⟩ := grpObj_of_flat_coset_quotient _ A _ B (constDesc x) q hi hmono
    inferInstance hsurj inferInstance (by
      intro Z g g'
      constructor
      · intro h
        obtain ⟨t, ht⟩ := exists_lift x (g' / g) fun z => by
          obtain ⟨V, a, hV, e⟩ :=
            hG.exists_local_geom g.left g'.left (congrArg CommaMorphism.left h) z
          have e' : openι Z V ≫ g ≫ (transl a.1).hom = openι Z V ≫ g' := Over.OverMorphism.ext e
          refine ⟨V, hV, a, ?_⟩
          rw [GrpObj.comp_div, ← e', ← Category.assoc, comp_translHom, mul_div_cancel_right]
        exact ⟨t, by rw [ht, div_mul_cancel]⟩
      · rintro ⟨t, rfl⟩
        refine hom_ext_local _ _ fun z => ?_
        obtain ⟨V, hV, c, hc⟩ := locally_const_desc x t z
        refine ⟨V, hV, ?_⟩
        rw [← Category.assoc _ (_ * _), MonObj.comp_mul, hc, ← comp_translHom, Category.assoc,
          Category.assoc, hinv])
  refine ⟨B, inferInstance, q, ?_, hhom, hfin, het, hsurj, fun K _ _ t y => ⟨fun hy => ?_, ?_⟩⟩
  · have hw' : q.left ≫ B.hom = A.hom := Over.w q
    have := hA.smooth
    have := hA.proper
    have := hA.geomConnected
    have := forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ A.hom hA.smooth
      hA.geomConnected
    have : IsSeparated B.hom := hsep
    have : LocallyOfFiniteType B.hom := hlft
    have : UniversallyClosed (q.left ≫ B.hom) := by rw [hw']; infer_instance
    have : GeometricallyReduced (q.left ≫ B.hom) := by rw [hw']; infer_instance
    have : GeometricallyConnected (q.left ≫ B.hom) := by rw [hw']; infer_instance
    have := UniversallyClosed.of_comp_surjective q.left B.hom
    have := AbelianQuotient.geometricallyReduced_of_comp q.left B.hom
    have : LocallyOfFinitePresentation B.hom := inferInstance
    exact ⟨hcomm, AbelianQuotient.smooth_of_grpObj_of_flat B, ⟨⟩, AbelianQuotient.geometricallyConnected_of_comp q.left B.hom⟩
  · have h1 : (1 : Over.mk t ⟶ A) ≫ q = y ≫ q := by rw [hy, MonObj.one_comp]
    obtain ⟨a, ha, -⟩ := hG.fibre K (1 : Over.mk t ⟶ A).left y.left
      (congrArg CommaMorphism.left h1)
    have ha' : (1 : Over.mk t ⟶ A) ≫ (transl a.1).hom = y := Over.OverMorphism.ext ha
    exact ⟨a.1, a.2, by rw [← ha', comp_translHom, _root_.mul_one]⟩
  · rintro ⟨c, hc, rfl⟩
    rw [← _root_.mul_one (toUnit _ ≫ c), ← comp_translHom, Category.assoc, hinv ⟨c, hc⟩,
      MonObj.one_comp]

end GlobalTheory
end
