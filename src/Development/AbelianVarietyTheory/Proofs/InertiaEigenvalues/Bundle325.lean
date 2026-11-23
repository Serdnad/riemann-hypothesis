module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoboundaryMemBlochKatoCocycles
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle204
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle046
public import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle294
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle296
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormLeOneOfMemOL
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.OffRange
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle308
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistedModelAdmissibleCocycles
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle297
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle032
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle011
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle298
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle098
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle100
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle299
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle009
import ReciprocityTheory.BasicDefinitions.ExistsUnique
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle013
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle014
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle012

@[expose] public section

section

noncomputable section

namespace GlobalTheory.TopSteps.FinSummand

open Module TensorProduct
open GlobalTheory.AdmLoc Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N

theorem exists_isCompl_of_saturated {O M : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O]
    [AddCommGroup M] [Module O M] [Module.Finite O M] (N : Submodule O M)
    (h : ∀ (a : O) (x : M), a ≠ 0 → a • x ∈ N → x ∈ N) : ∃ C : Submodule O M, IsCompl N C := by
  first
  | exact @_root_.GlobalTheory.SaturatedComplement.exists_isCompl_of_saturated
  | exact _root_.GlobalTheory.SaturatedComplement.exists_isCompl_of_saturated
  | (apply _root_.GlobalTheory.SaturatedComplement.exists_isCompl_of_saturated <;> assumption)
  | (intros; apply _root_.GlobalTheory.SaturatedComplement.exists_isCompl_of_saturated <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SaturatedComplement.exists_isCompl_of_saturated <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SaturatedComplement.exists_isCompl_of_saturated ..)

section General

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL]

section Rep

variable {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
  {ρ : Representation LL G V}


variable [Module O V] [IsScalarTower O LL V] [IsDomain O] [IsFractionRing O LL]


omit [TopologicalSpace G] in
theorem invariants_stableLattice_mod_irreducible_eq_bot [IsDiscreteValuationRing O] (L : Lattice (O := O) ρ) {lam : O} (hlam : Irreducible lam)
    (h : (coefRep (latRep L) (O ⧸ Ideal.span {lam})).invariants = ⊥) : H0V ρ = ⊥ := by
  haveI : Module.Finite O ↥L.T := Module.Finite.iff_fg.2 L.fg
  have hsm : ∀ (a : O) (x : V), a ≠ 0 → a • x = 0 → x = 0 := fun a x ha hx => by
    rw [← algebraMap_smul LL] at hx
    exact (smul_eq_zero.1 hx).resolve_left (by simpa using ha)
  have hM : (latRep L).invariants = ⊥ := by
    refine Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (Ideal.span {lam}) _ (IsNoetherian.noetherian _) ?_ ?_
    · intro x hx
      have h1 : x ⊗ₜ[O] (1 : O ⧸ Ideal.span {lam}) ∈
          (coefRep (latRep L) (O ⧸ Ideal.span {lam})).invariants := fun g => by
        rw [coefRep_tmul, hx g]
      rw [h, Submodule.mem_bot] at h1
      have h2 := congrArg (TensorProduct.tensorQuotEquivQuotSMul ↥L.T (Ideal.span {lam})) h1
      rw [map_zero, ← map_one (Ideal.Quotient.mk _), TensorProduct.tensorQuotEquivQuotSMul_tmul_mk, one_smul,
        Submodule.Quotient.mk_eq_zero, Submodule.ideal_span_singleton_smul] at h2
      obtain ⟨y, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists x lam ⊤).1 h2
      refine Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) fun g => Subtype.ext ?_
      have h3 := congrArg Subtype.val (hx g)
      rw [map_smul] at h3
      refine sub_eq_zero.1 (hsm lam _ hlam.ne_zero ?_)
      rw [smul_sub]
      exact sub_eq_zero.2 h3
    · rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top, hlam.maximalIdeal_eq]
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨a, ha, hax⟩ := GlobalTheory.H1fGeneratorBoundAlt.exists_smul_mem L x
  have h1 : (⟨a • x, hax⟩ : ↥L.T) ∈ (latRep L).invariants := fun g => Subtype.ext (by
    have := (Submodule.mem_iInf _).1 hx g
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at this
    change ρ g (a • x) = a • x
    rw [← algebraMap_smul LL, map_smul, this])
  rw [hM, Submodule.mem_bot] at h1
  exact hsm a x ha (congrArg Subtype.val h1)

variable [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V]

theorem h1fT_saturated (L : Lattice (O := O) ρ) (a : O) (x : LatticeCohomology L) (ha : a ≠ 0) (hx : a • x ∈ latticeFiniteCohomology PD L) :
    x ∈ latticeFiniteCohomology PD L := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨c', hc', h⟩ := hx
  rw [← Submodule.Quotient.mk_smul, Submodule.mkQ_apply, Submodule.Quotient.eq] at h
  obtain ⟨b, -, hb⟩ := h
  have h1 : ((c' - a • c : ↥(latticeCocycles L)) : G → V) ∈ finiteCocycles PD ρ := by
    refine ⟨(c' - a • c).2.1, b ⊗ₜ 1, fun g => ?_⟩
    have : ρ g b - b = ((c' - a • c : ↥(latticeCocycles L)) : G → V) g := congrFun hb g
    rw [← this]
    simp [actVB, sub_tmul]
  have h2 : algebraMap O LL a • (c : G → V) ∈ finiteCocycles PD ρ := by
    have := (finiteCocycles PD ρ).sub_mem hc'.2 h1
    rw [algebraMap_smul]
    simpa using this
  have ha' : algebraMap O LL a ≠ 0 := by simpa using ha
  have h3 : (c : G → V) ∈ finiteCocycles PD ρ := (Submodule.smul_mem_iff (finiteCocycles PD ρ) ha').1 h2
  exact ⟨c, ⟨c.2, h3⟩, rfl⟩

theorem finrank_h1fT [CompactSpace G] (L : Lattice (O := O) ρ) (hT : IsOpen (L.T : Set V)) :
    finrank O ↥(latticeFiniteCohomology PD L) = finrank LL (FiniteCohomology PD ρ) := by
  refine congrArg Cardinal.toNat (GlobalTheory.BlochKatoRank.rank_subquotient_eq (K := LL) LinearMap.id (latticeCocycles L) (latticeCoboundaries L)
    (latticeFiniteCocycles PD L) (finiteCocycles PD ρ) (B1 ρ) (fun a ha => ha.2) ?_ ?_ ?_)
  · rintro _ ⟨x, -, rfl⟩
    exact ⟨x, rfl⟩
  · rintro a ⟨x, hx⟩
    obtain ⟨m, hm, h⟩ := GlobalTheory.H1fGeneratorBoundAlt.exists_smul_mem L x
    refine ⟨m, hm, m • x, h, ?_⟩
    rw [map_smul]
    exact congrArg (m • ·) hx
  · intro c hc
    obtain ⟨a, ha, h⟩ := GlobalTheory.H1fGeneratorBoundAlt.exists_smul_fun_mem L hT c hc.1.1
    have h1 : a • c ∈ (finiteCocycles PD ρ).restrictScalars O :=
      Submodule.smul_mem ((finiteCocycles PD ρ).restrictScalars O) a hc
    exact ⟨a, ha, a • c, ⟨h1.1, fun g _ => h g⟩, ⟨⟨h1.1, fun g _ => h g⟩, h1⟩, rfl⟩

end Rep

end General


end GlobalTheory.TopSteps.FinSummand
end
end

section

open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions

open ReciprocityTheory.Def (Z1 B1 H1)
open TensorProduct


theorem _root_.GlobalTheory.T.twistedAction_eq_twistedCoefficients_cocycle_iff : ∀ {G : Type} [Group G] [TopologicalSpace G] {LL : Type} [Field LL] {O : Type} [CommRing O]
    [Algebra O LL] {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
    {ρ : Representation LL G V} (L : Lattice (O := O) ρ) (X : Type) [AddCommGroup X] [Module O X]
    (χ : G →* Oˣ),
    (∀ g m, tableLineDegreeTwo.actTw L X χ g m = twCoef (latRep L) χ X g m) ∧
    ∀ z : G → ↥L.T ⊗[O] X, tableLineDegreeTwo.IsCoc L X χ z ↔ z ∈ Z1 (twCoef (latRep L) χ X) ⊤ := by
  first | exact @GlobalTheory.actTw_eq_twCoef_and_isCoc_iff | exact GlobalTheory.actTw_eq_twCoef_and_isCoc_iff | (intros; apply GlobalTheory.actTw_eq_twCoef_and_isCoc_iff <;> assumption)
end

section

open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions

open ReciprocityTheory.Def (Z1 B1 H1)
open TensorProduct


theorem _root_.GlobalTheory.T.period_data_dual_exact : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀]
    [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL] {O : Type} [CommRing O] [Algebra O LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] [Module O V]
    [IsScalarTower O LL V] {ρ : Representation LL G V} [TopologicalSpace V] [ContinuousAdd V]
    [ContinuousConstSMul LL V] (L : Lattice (O := O) ρ) (ρ' : Representation LL G V) (L' : Lattice (O := O) ρ')
    (X : Type) [AddCommGroup X] [Module O X] (χ : G →* Oˣ),
    (∀ g, ρ' g = ((tableLineDegreeTwo.charL (LL := LL) χ g)⁻¹ : LLˣ).val • ρ g) → L'.T = L.T →
    ∀ (z : G → ↥L.T ⊗[O] X) (hz : z ∈ Z1 (twCoef (latRep L) χ X) ⊤),
      (Submodule.Quotient.mk ⟨z, hz⟩ ∈ finiteSelmer PD L χ X ↔ tableLineDegreeTwo.InHfX PD L L' X χ z) := by
  first | exact @GlobalTheory.AdmLoc.mk_mem_H1fX_iff_inHfX | exact GlobalTheory.AdmLoc.mk_mem_H1fX_iff_inHfX | (intros; apply GlobalTheory.AdmLoc.mk_mem_H1fX_iff_inHfX <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.Prism

namespace GlobalTheory.Prism.LocalValue

theorem exists_basis {A B M N ι : Type} [CommRing A] [CommRing B] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module B N] [Fintype ι] {f : A →+* B} {u : M →ₛₗ[f] N} (h : SemiBC u)
    (b : Module.Basis ι A M) : ∃ c : Module.Basis ι B N, ∀ i, c i = u (b i) := by
  classical
  let v : M →ₛₗ[f] (ι → B) :=
    { toFun := fun x i => f (b.equivFun x i)
      map_add' := fun x y => by ext i; simp
      map_smul' := fun a x => by ext i; simp }
  obtain ⟨S, hS, -⟩ := h _ v
  let Q : (ι → B) →ₗ[B] N := Fintype.linearCombination B fun i => u (b i)
  have hQ : Q.comp S = LinearMap.id := h.hom_ext fun x => by
    rw [LinearMap.comp_apply, hS, LinearMap.id_apply, Fintype.linearCombination_apply]

    conv_rhs => rw [← b.sum_equivFun x, map_sum]
    exact Finset.sum_congr rfl fun i _ => (u.map_smulₛₗ _ _).symm
  have hQ1 : ∀ i, Q (Pi.single i 1) = u (b i) := fun i => by
    simp [Q]
  have hS' : S.comp Q = LinearMap.id := by
    refine (Pi.basisFun B ι).ext fun i => ?_
    rw [LinearMap.comp_apply, Pi.basisFun_apply, hQ1, hS, LinearMap.id_apply]
    ext k
    change f (b.equivFun (b i) k) = _
    rw [b.equivFun_self, Pi.single_apply]
    by_cases hik : i = k
    · simp [hik]
    · simp [hik, Ne.symm hik]
  refine ⟨(Pi.basisFun B ι).map (LinearEquiv.ofLinear Q S hQ hS'), fun i => ?_⟩
  rw [Module.Basis.map_apply, Pi.basisFun_apply]
  exact hQ1 i

theorem exists_pow_smul_eq_sum {A M ι : Type} [CommRing A] [AddCommGroup M] [Module A M] [Fintype ι]
    {d : A} {f : A →+* Localization.Away d} {Φ : M →ₛₗ[f] LocalizedModule (Submonoid.powers d) M}
    (h : SemiBC Φ) (b : Module.Basis ι A M) (m : ι → M) (k : ι → ℕ)
    (hm : ∀ i, IsFrac d (Φ (b i)) (m i) (k i)) (x : M) :
    ∃ (r : ℕ) (s : ι → A), d ^ r • x = ∑ i, s i • m i := by
  obtain ⟨c, hc⟩ := exists_basis h b
  have h1 : (LocalizedModule.mk x 1 : LocalizedModule (Submonoid.powers d) M) ∈
      Submodule.span (Localization.Away d)
        (Set.range fun i => (LocalizedModule.mk (m i) 1 : LocalizedModule (Submonoid.powers d) M)) := by
    refine (?_ : (⊤ : Submodule (Localization.Away d) _) ≤ _) Submodule.mem_top
    rw [← c.span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have h2 : c i = (Localization.mk 1 ⟨d ^ k i, (Submonoid.mem_powers_iff _ _).2 ⟨k i, rfl⟩⟩ :
        Localization.Away d) • (LocalizedModule.mk (m i) 1 : LocalizedModule (Submonoid.powers d) M) := by
      rw [hc, hm i, LocalizedModule.mk_smul_mk, one_smul, mul_one]
    rw [h2]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  obtain ⟨⟨_, t, rfl⟩, ht⟩ := multiple_mem_span_of_mem_localization_span (Submonoid.powers d)
    (Localization.Away d) _ _ h1
  obtain ⟨s, hs⟩ := (Submodule.mem_span_range_iff_exists_fun A).1 ht
  have h3 : LocalizedModule.mkLinearMap (Submonoid.powers d) M (∑ i, s i • m i) =
      LocalizedModule.mkLinearMap (Submonoid.powers d) M (d ^ t • x) := by

    rw [map_sum, map_smul]
    simp only [map_smul]
    exact hs
  rw [LocalizedModule.mkLinearMap_apply, LocalizedModule.mkLinearMap_apply, LocalizedModule.mk_eq] at h3
  obtain ⟨⟨_, a, rfl⟩, ha⟩ := h3
  simp only [one_smul, Submonoid.smul_def] at ha
  refine ⟨a + t, fun i => d ^ a * s i, ?_⟩
  rw [pow_add, mul_smul, ← ha, Finset.smul_sum]
  simp only [mul_smul]

theorem exists_eq_smul {A B M N ι : Type} [CommRing A] [CommRing B] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module B N] [Fintype ι] {f : A →+* B} {u : M →ₛₗ[f] N} (h : SemiBC u)
    (b : Module.Basis ι A M) {π : A} (hπ : RingHom.ker f = Ideal.span {π}) (x : M) (hx : u x = 0) :
    ∃ y, x = π • y := by
  obtain ⟨c, hc⟩ := exists_basis h b
  have h1 : ∑ i, f (b.equivFun x i) • c i = 0 := by
    rw [← hx]

    conv_rhs => rw [← b.sum_equivFun x, map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [hc, u.map_smulₛₗ]
  have h2 := Fintype.linearIndependent_iff.1 c.linearIndependent _ h1
  have h3 : ∀ i, ∃ a, a * π = b.equivFun x i := fun i =>
    Ideal.mem_span_singleton'.1 (hπ ▸ (RingHom.mem_ker).2 (h2 i))
  choose a ha using h3
  refine ⟨∑ i, a i • b i, ?_⟩
  conv_lhs => rw [← b.sum_equivFun x]
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [← ha, smul_smul, mul_comm]

theorem ennreal_volume_ratio_step_cancel {A B M N : Type} [CommRing A] [CommRing B] [IsDomain B] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module B N] [Module.Free B N] {f : A →+* B} (u : M →ₛₗ[f] N) {e : A}
    (he : f e ≠ 0) {m n : M} {k i r : ℕ} (h : (e * e) ^ r • (e ^ i • m - e ^ k • n) = 0) {y : N}
    (hy : f e ^ i • y = u n) : f e ^ k • y = u m := by
  have h2 := congrArg u h
  rw [u.map_smulₛₗ, map_sub, u.map_smulₛₗ, u.map_smulₛₗ, map_zero, map_pow, map_pow, map_pow, map_mul,
    ← hy, smul_comm (f e ^ k), ← smul_sub, smul_eq_zero, smul_eq_zero] at h2
  rcases h2 with h2 | h2 | h2
  · exact absurd h2 (pow_ne_zero _ (mul_ne_zero he he))
  · exact absurd h2 (pow_ne_zero _ he)
  · exact (sub_eq_zero.1 h2).symm

theorem general {l : ℕ} {R : Type} [CommRing R] {PS PA : Obj l R} [IsLocalRing PS.A] (io : Hom PS PA)
    {B N : Type} [CommRing B] [IsDomain B] [AddCommGroup N] [Module B N] {f : PA.A →+* B}
    (E : FCrys l R) {j : E.M PA →ₛₗ[f] N} (hj : SemiBC j) (F : N → N)
    (hF : ∀ (d : ↥PA.I), (d : PA.A) ≠ 0 → ∀ (x m : E.M PA) (k : ℕ), IsFrac (d : PA.A) (E.Φ PA d x) m k →
      f d ^ k • F (j x) = j m)
    {Q : PS.A} (hQ : Q ∈ PS.I) (ψ : PS.A →+* B) (hψ : ∀ x, ψ x = f (io.f x)) (hQ0 : ψ Q ≠ 0) :
    ∃ (q : ℕ) (b : Module.Basis (Fin q) PS.A (E.M PS)) (c : Module.Basis (Fin q) B N),
      (∀ i, c i = j (E.tr io (b i))) ∧
      (∀ x, ∃ (k : ℕ) (m : E.M PS), ψ Q ^ k • F (j (E.tr io x)) = j (E.tr io m)) ∧
      (∀ x, ∃ (k : ℕ) (s : Fin q → PS.A), ψ Q ^ k • j (E.tr io x) = ∑ i, ψ (s i) • F (c i)) := by
  have := E.fin PS
  have := E.proj PS
  have : Module.Free PS.A (E.M PS) := Module.free_of_flat_of_isLocalRing
  let b := Module.finBasis PS.A (E.M PS)
  obtain ⟨c', hc'⟩ := exists_basis (E.tr_bc io) b
  obtain ⟨c, hc⟩ := exists_basis hj c'
  have hcb : ∀ i, c i = j (E.tr io (b i)) := fun i => by rw [hc, hc']
  have : Module.Free B N := Module.Free.of_basis c
  have hsm : ∀ (s : PS.A) (x : E.M PS), j (E.tr io (s • x)) = ψ s • j (E.tr io x) := fun s x => by
    rw [LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ, hψ]
  have key : ∀ (x m : E.M PS) (k : ℕ), IsFrac Q (E.Φ PS ⟨Q, hQ⟩ x) m k →
      ψ Q ^ k • F (j (E.tr io x)) = j (E.tr io m) := by
    intro x m k h
    have h0 : io.f Q ≠ 0 := fun h0 => hQ0 (by rw [hψ, h0, map_zero])
    obtain ⟨n, i, hn⟩ := exists_isFrac (io.f Q) (E.Φ PA ⟨io.f Q, io.f_I Q hQ⟩ (E.tr io x))
    obtain ⟨r, hr⟩ := E.Φ_nat io ⟨Q, hQ⟩ ⟨io.f Q, io.f_I Q hQ⟩ x m k n i h hn
    have h1 := hF ⟨io.f Q, io.f_I Q hQ⟩ h0 _ n i hn
    rw [hψ] at hQ0 ⊢
    exact ennreal_volume_ratio_step_cancel j hQ0 hr h1
  refine ⟨_, b, c, hcb, fun x => ?_, fun x => ?_⟩
  · obtain ⟨m, k, h⟩ := exists_isFrac Q (E.Φ PS ⟨Q, hQ⟩ x)
    exact ⟨k, m, key x m k h⟩
  · choose m k hm using fun i => exists_isFrac Q (E.Φ PS ⟨Q, hQ⟩ (b i))
    obtain ⟨r, s, hs⟩ := exists_pow_smul_eq_sum (E.Φ_bc PS ⟨Q, hQ⟩) b m k hm x
    refine ⟨r, fun i => s i * Q ^ k i, ?_⟩
    have hs' : Q ^ r • x = ∑ i, s i • m i := hs

    rw [← map_pow, ← hsm, hs', map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hsm, ← key _ _ _ (hm i), hcb, smul_smul, map_mul, map_pow]

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (PS PW : Obj l ↥(OL K)) (ev : Hom PS PW) (ioH : Hom PS (ainfObj K)) (gH : ↥(GK K) → Hom PS PS) (π Q : PS.A) (ψ : PS.A →+* WCb l), (∀ x, ψ x = inclW l (ainfId K (ioH.f x))) → (∀ g, ioH.comp (gH g) = (ainfHom K g).comp ioH) → (∀ g, ev.comp (gH g) = ev) → RingHom.ker ev.f = Ideal.span {π} → Q ∈ PS.I → IsLocalRing PS.A → ψ Q ≠ 0 → ∀ (T : Type) [AddCommGroup T] [Module ℤ_[l] T] (ρ : ↥(GK K) → (T →ₗ[ℤ_[l]] T)) (E : FCrys l ↥(OL K)) (j : E.M (ainfObj K) →ₛₗ[(inclW l).comp (ainfId K).toRingHom] (WCb l ⊗[ℤ_[l]] T)), Realises K E (ainfObj K) (ainfId K) T ρ j → ∃ (q : ℕ) (b : Module.Basis (Fin q) PS.A (E.M PS)) (c : Module.Basis (Fin q) (WCb l) (WCb l ⊗[ℤ_[l]] T)), (∀ i, c i = j (E.tr ioH (b i))) ∧ (∀ x, ∃ (k : ℕ) (m : E.M PS), ψ Q ^ k • TensorProduct.map (frobW l).toLinearMap LinearMap.id (j (E.tr ioH x)) = j (E.tr ioH m)) ∧ (∀ x, ∃ (k : ℕ) (s : Fin q → PS.A), ψ Q ^ k • j (E.tr ioH x) = ∑ i, ψ (s i) • TensorProduct.map (frobW l).toLinearMap LinearMap.id (c i)) ∧ (∀ (g : ↥(GK K)) x, TensorProduct.map (galW l (g : GQ l)).toLinearMap (ρ g) (j (E.tr ioH x)) = j (E.tr ioH (E.tr (gH g) x))) ∧ (∀ g x, ∃ y, E.tr (gH g) x - x = π • y) := by
  intro l _ K PS PW ev ioH gH π Q ψ hψ hg hev hker hQ hloc hQ0 T _ _ ρ E j H
  obtain ⟨q, b, c, h1, h2, h3⟩ := general ioH E H.bc
    (fun y => TensorProduct.map (frobW l).toLinearMap LinearMap.id y) H.j_φ hQ ψ hψ hQ0
  refine ⟨q, b, c, h1, h2, h3, fun g x => ?_, fun g x => ?_⟩
  · have h4 : E.tr ioH (E.tr (gH g) x) = E.tr (ainfHom K g) (E.tr ioH x) :=
      ((E.tr_comp ioH (gH g) x).symm.trans (congrArg (fun f => E.tr f x) (hg g))).trans
        (E.tr_comp (ainfHom K g) ioH x)
    exact (H.j_act g (E.tr ioH x)).symm.trans (congrArg j h4.symm)
  · refine exists_eq_smul (E.tr_bc ev) b hker _ ?_
    rw [map_sub, ← E.tr_comp, hev, sub_self]

end GlobalTheory.Prism.LocalValue
end
end

section

open GlobalTheory.LiftLeaf GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw Formalism.BasicNotions Formalism.MainNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

namespace GlobalTheory.EigRed

open Formalism.MainNotions.IntegralHeckeForms

theorem admT3_of_semisimple_good : ∀ (D : D7) (E : IntegralHeckeForms.XD D), IntegralHeckeForms.IsotypicPartsInternalDirectSum D.nexp E → IntegralHeckeForms.GroupAlgebraIntegrality D.nexp → D.nexp.sig_all → HkSS D → IntegralHeckeForms.GoodLatticePoints D.nexp := by
  intro D E hI hA hS hss i hi j hj b x hxB hxm ev hev
  by_contra hno
  apply hxm
  have hcomm := ((hA i hi b).2 j hj).1
  have hM := (hI i hi j hj b).2.2.2.1
  have hx := hss i hi j hj b hxB.2
  obtain ⟨f, hf, hfx⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).1 hx
  refine mem_smul_of_sum_eigenvectors (ι := {p : ℕ × PlE D.host // HkIdx i p.1 p.2}) _ _
    (fun p => hkO D.nexp i j b p.1.1 p.1.2) (fun p z hz => ?_) (fun p => ev p.1.1 p.1.2) f.support
    (fun a => f a) x (fun a _ => ?_) ?_ hxB (fun p => hev _ _ p.2)
  · exact ⟨hM _ _ p.2 ⟨z, hz.1, rfl⟩, idempotentImage_stable_of_equivariant D.nexp i j b _ (fun g => hcomm g _ _ p.2) z hz.2⟩
  · by_cases h0 : f a = 0
    · exact Or.inl h0
    right
    have hex : eG D.nexp i j b (f a) = f a := by
      obtain ⟨y, -, hy⟩ := (hf a).2
      rw [← hy, eG_idem]
    have heig : ∀ k P, HkIdx i k P → D.nexp.hkF i j b k P (f a) = a k P • f a := by
      intro k P hk
      have h1 := (hf a).1
      simp only [Eigsp, SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at h1
      exact h1 k P hk
    obtain ⟨s, hs1, hs2, hs3⟩ := hS i j b _ a h0 hex
      (fun k P h1 h2 h3 h4 => heig k P ⟨h1, h2, h3, h4⟩)
    refine ⟨fun p => D.ntw.hEig i s p.1.1 p.1.2, fun p => ?_, ?_⟩
    · change D.nexp.hkF i j b _ _ _ = _
      rw [heig _ _ p.2, ← hs3 _ _ p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2, algebraMap_smul]
    · by_contra hu
      refine hno ⟨s, hs1, hs2, fun k P hk => ?_⟩
      exact fun h => hu ⟨⟨(k, P), hk⟩, h⟩
  · exact hfx.symm

end GlobalTheory.EigRed
end

section

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries

theorem _root_.GlobalTheory.T.exists_largest_model' : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt) (A : Ob k G) (N₀ : Lats k n A.m), M.Model A N₀ → ∃ N, M.Model A N ∧ ∀ N', M.Model A N' → ∀ i, N' i ≤ N i := by
  first | exact @GlobalTheory.Models.exists_largest_model | exact GlobalTheory.Models.exists_largest_model | (intros; apply GlobalTheory.Models.exists_largest_model <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.extension_block_periodMatrix_semistable : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (a b : Type) [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (K : FinExt l) (ρ : ↥(GK K) →* GL (a ⊕ b) ↥(MaximalUnramifiedExtension l)) (ρ₁ : ↥(GK K) →* GL a ↥(MaximalUnramifiedExtension l)) (ρ₂ : ↥(GK K) →* GL b ↥(MaximalUnramifiedExtension l)) (c : ↥(GK K) → Matrix a b ↥(MaximalUnramifiedExtension l)), (∀ g, (ρ g : Matrix (a ⊕ b) (a ⊕ b) ↥(MaximalUnramifiedExtension l)) = Matrix.fromBlocks (ρ₁ g : Matrix a a ↥(MaximalUnramifiedExtension l)) (c g) 0 (ρ₂ g : Matrix b b ↥(MaximalUnramifiedExtension l))) → ∀ (Q₁ : GL a (Bst P)) (Q₂ : GL b (Bst P)), (∀ g : ↥(GK K), (ρ₁ g : Matrix a a ↥(MaximalUnramifiedExtension l)).map (ks P) * (Q₁ : Matrix a a (Bst P)).map (actSt P (g : GQ l)) = Q₁) → (∀ g : ↥(GK K), (ρ₂ g : Matrix b b ↥(MaximalUnramifiedExtension l)).map (ks P) * (Q₂ : Matrix b b (Bst P)).map (actSt P (g : GQ l)) = Q₂) → ∀ v : a × b → Bst P, (∀ g : ↥(GK K), (fun i => ks P (extCoc ρ₂ c g i)) = ((homRep ρ₁ ρ₂ g : Matrix (a × b) (a × b) ↥(MaximalUnramifiedExtension l)).map (ks P)).mulVec (fun i => actSt P (g : GQ l) (v i)) - v) → ∃ Q : GL (a ⊕ b) (Bst P), ∀ g : ↥(GK K), (ρ g : Matrix (a ⊕ b) (a ⊕ b) ↥(MaximalUnramifiedExtension l)).map (ks P) * (Q : Matrix (a ⊕ b) (a ⊕ b) (Bst P)).map (actSt P (g : GQ l)) = Q := by
  first | exact @GlobalTheory.PMon.extPeriodMatrix | exact GlobalTheory.PMon.extPeriodMatrix | (intros; apply GlobalTheory.PMon.extPeriodMatrix <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.matrixHom_periodMatrix_semistable : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (a b : Type) [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (K : FinExt l) (ρ₁ : ↥(GK K) →* GL a ↥(MaximalUnramifiedExtension l)) (ρ₂ : ↥(GK K) →* GL b ↥(MaximalUnramifiedExtension l)) (Q₁ : GL a (Bst P)) (Q₂ : GL b (Bst P)), (∀ g : ↥(GK K), (ρ₁ g : Matrix a a ↥(MaximalUnramifiedExtension l)).map (ks P) * (Q₁ : Matrix a a (Bst P)).map (actSt P (g : GQ l)) = Q₁) → (∀ g : ↥(GK K), (ρ₂ g : Matrix b b ↥(MaximalUnramifiedExtension l)).map (ks P) * (Q₂ : Matrix b b (Bst P)).map (actSt P (g : GQ l)) = Q₂) → ∀ g : ↥(GK K), (homRep ρ₁ ρ₂ g : Matrix (a × b) (a × b) ↥(MaximalUnramifiedExtension l)).map (ks P) * ((homUnit Q₁ Q₂ : GL (a × b) (Bst P)) : Matrix (a × b) (a × b) (Bst P)).map (actSt P (g : GQ l)) = (homUnit Q₁ Q₂ : GL (a × b) (Bst P)) := by
  first | exact @GlobalTheory.PMon.homUnit_period | exact GlobalTheory.PMon.homUnit_period | (intros; apply GlobalTheory.PMon.homUnit_period <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.matrixHomRepresentationCocycle_rational_continuous : ∀ (l : ℕ) [Fact l.Prime] (a b : Type) [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (K K' : FinExt l) (hK : K.1 ≤ K'.1) (r : ℕ) (ρ : ↥(GK K) →* GL (a ⊕ b) ↥(MaximalUnramifiedExtension l)) (ρ₁ : ↥(GK K) →* GL a ↥(MaximalUnramifiedExtension l)) (ρ₂ : ↥(GK K) →* GL b ↥(MaximalUnramifiedExtension l)) (c : ↥(GK K) → Matrix a b ↥(MaximalUnramifiedExtension l)), IsRat r ρ → (∀ g, (ρ g : Matrix (a ⊕ b) (a ⊕ b) ↥(MaximalUnramifiedExtension l)) = Matrix.fromBlocks (ρ₁ g : Matrix a a ↥(MaximalUnramifiedExtension l)) (c g) 0 (ρ₂ g : Matrix b b ↥(MaximalUnramifiedExtension l))) → (∀ g i, fr l r (extCoc (ρ₂.comp (Subgroup.inclusion (GK_le hK))) (fun g => c (Subgroup.inclusion (GK_le hK) g)) g i) = extCoc (ρ₂.comp (Subgroup.inclusion (GK_le hK))) (fun g => c (Subgroup.inclusion (GK_le hK) g)) g i) ∧ (∀ i, Continuous fun g => ((extCoc (ρ₂.comp (Subgroup.inclusion (GK_le hK))) (fun g => c (Subgroup.inclusion (GK_le hK) g)) g i : ↥(MaximalUnramifiedExtension l)) : Om l)) ∧ (∀ g h, extCoc (ρ₂.comp (Subgroup.inclusion (GK_le hK))) (fun g => c (Subgroup.inclusion (GK_le hK) g)) (g * h) = extCoc (ρ₂.comp (Subgroup.inclusion (GK_le hK))) (fun g => c (Subgroup.inclusion (GK_le hK) g)) g + (homRep (ρ₁.comp (Subgroup.inclusion (GK_le hK))) (ρ₂.comp (Subgroup.inclusion (GK_le hK))) g : Matrix (a × b) (a × b) ↥(MaximalUnramifiedExtension l)).mulVec (extCoc (ρ₂.comp (Subgroup.inclusion (GK_le hK))) (fun g => c (Subgroup.inclusion (GK_le hK) g)) h)) := by
  first | exact @GlobalTheory.PMon.extCoc_rat_cont_cocycle | exact GlobalTheory.PMon.extCoc_rat_cont_cocycle | (intros; apply GlobalTheory.PMon.extCoc_rat_cont_cocycle <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.matrixHomRepresentation_restrict_rational_continuous : ∀ (l : ℕ) [Fact l.Prime] (a b : Type) [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (K K' : FinExt l) (hK : K.1 ≤ K'.1) (r : ℕ) (ρ : ↥(GK K) →* GL (a ⊕ b) ↥(MaximalUnramifiedExtension l)) (ρ₁ : ↥(GK K) →* GL a ↥(MaximalUnramifiedExtension l)) (ρ₂ : ↥(GK K) →* GL b ↥(MaximalUnramifiedExtension l)) (c : ↥(GK K) → Matrix a b ↥(MaximalUnramifiedExtension l)), IsRat r ρ → (∀ g, (ρ g : Matrix (a ⊕ b) (a ⊕ b) ↥(MaximalUnramifiedExtension l)) = Matrix.fromBlocks (ρ₁ g : Matrix a a ↥(MaximalUnramifiedExtension l)) (c g) 0 (ρ₂ g : Matrix b b ↥(MaximalUnramifiedExtension l))) → IsRat r (homRep (ρ₁.comp (Subgroup.inclusion (GK_le hK))) (ρ₂.comp (Subgroup.inclusion (GK_le hK)))) := by
  first | exact @GlobalTheory.PMon.isRat_homRep_restrict | exact GlobalTheory.PMon.isRat_homRep_restrict | (intros; apply GlobalTheory.PMon.isRat_homRep_restrict <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.orbitalIntegral_linearDescent_cutoff : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (τ : A.K) (p : Fin r → F) (hG : A.IsGen τ p) (lam : F), ∀ (M : Meas r F E) (μK : Measure A.K), μK.IsAddHaarMeasure → ∀ (α : GL (Fin r) F → ℝ) (f' : Gl r F → ℂ), IsTest f' → IsLocallyConstant α → HasCompactSupport α → (∀ g, 0 ≤ α g) → (∀ g : GL (Fin r) F, (∃ v w : Fin r → F, f' ((g : Matrix (Fin r) (Fin r) F) * companion p * ((g⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F), v, w, lam) ≠ 0) → ∀ s₀ : A.Kˣ, ∫ s, α (g * LinDesc.tm A hG s₀ * LinDesc.tm A hG s) ∂(LinDesc.unitsMeas A μK) = 1) → ∀ κ₀ : ℂ, (∀ a : A.K, IsUnit a → ∀ g : GL (Fin r) F, omega (act g (LinDesc.pt A hG lam 1 a)) = κ₀ * eta ((g : Matrix (Fin r) (Fin r) F).det) * A.etaK a) → ∀ a : A.K, IsUnit a → orbG M f' (LinDesc.pt A hG lam 1 a) = κ₀ * A.orbK μK (LinDesc.desc A M hG lam α f') a := by
  first | exact @GlobalTheory.JR.LinDesc.orb_descent_unit | exact GlobalTheory.JR.LinDesc.orb_descent_unit | (intros; apply GlobalTheory.JR.LinDesc.orb_descent_unit <;> assumption)
end

section

open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.stableQuadraticGaussIntegral_transform_weil : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ) (μ : Measure A.L) (ω : A.K → ℂ), Hyp A ψ x μ ω → ∀ (u : A.Kˣ) (G G₁ : ℂ), IsStableGauss A ψ x μ u G → IsStableGauss A ψ x μ 1 G₁ → G = G₁ * ω u * ((A.absK u : ℂ))⁻¹ := by
  first | exact @GlobalTheory.JR.WeilQuad.gauss_transform | exact GlobalTheory.JR.WeilQuad.gauss_transform | (intros; apply GlobalTheory.JR.WeilQuad.gauss_transform <;> assumption)
end
