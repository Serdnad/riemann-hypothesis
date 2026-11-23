module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle006
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle039
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JhMultSubAddQuot
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle062
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle071
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AlgebraicValuesFinite.AlgValsFinMain
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AlgebraicValuesFinite.EvFLocalIdeleSelf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AlgebraicValuesFinite.OrdFEqOfClassOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AlgebraicValuesFinite.ValuedAtFin
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL
open scoped TensorProduct

namespace GlobalTheory.SmGL.IndExact

section General

variable {G X U : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup X] [Module ℂ X]
  [AddCommGroup U] [Module ℂ U] {P : Subgroup G} {σ : Representation ℂ P X} {ρ : Representation ℂ P U}

theorem smIndMap_injective (ι : σ.IntertwiningMap ρ) (hι : Function.Injective ι) :
    Function.Injective (smIndMap ι) := fun φ ψ h =>
  Subtype.ext (Subtype.ext (funext fun g =>
    hι (congrFun (congrArg (fun χ : smoothPart (ind P ρ) => χ.1.1) h) g)))

theorem exists_smIndMap_eq (ι : σ.IntertwiningMap ρ) (hι : Function.Injective ι)
    (F : smoothPart (ind P ρ)) (hF : ∀ g, ∃ u, ι u = F.1.1 g) : ∃ F', smIndMap ι F' = F := by
  choose u hu using hF
  refine ⟨⟨⟨u, fun h g => hι ?_⟩, mem_smoothPart_of_nhds (Filter.mem_of_superset
    (IsOpen.mem_nhds F.2 (by simp)) fun g hg => ?_)⟩, Subtype.ext (Subtype.ext (funext hu))⟩
  · rw [ι.isIntertwining, hu, hu, F.1.2 h g]
  · have hg' : ind P ρ g F.1 = F.1 := hg
    refine Subtype.ext (funext fun x => hι ?_)
    show ι (u (x * g)) = ι (u x)
    rw [hu, hu]
    exact congrFun (congrArg Subtype.val hg') x

theorem exists_normalised_pi {α : Type} [Finite α] {Γ : α → Type} [∀ i, Group (Γ i)]
    [∀ i, TopologicalSpace (Γ i)] (K : ∀ i, Subgroup (Γ i))
    (h : ∀ i, ∀ U ∈ nhds (1 : Γ i), ∃ J : Subgroup (Γ i), IsOpen (J : Set (Γ i)) ∧ (J : Set (Γ i)) ⊆ U ∧
      J ≤ K i ∧ ∀ x ∈ K i, ∀ j ∈ J, x * j * x⁻¹ ∈ J) :
    ∀ U ∈ nhds (1 : ∀ i, Γ i), ∃ J : Subgroup (∀ i, Γ i), IsOpen (J : Set (∀ i, Γ i)) ∧
      (J : Set (∀ i, Γ i)) ⊆ U ∧ J ≤ Subgroup.pi Set.univ K ∧
        ∀ x ∈ Subgroup.pi Set.univ K, ∀ j ∈ J, x * j * x⁻¹ ∈ J := by
  intro U hU
  rw [nhds_pi, Filter.mem_pi] at hU
  obtain ⟨I, -, t, ht, hI⟩ := hU
  choose J h1 h2 h3 h4 using fun i => h i (t i) (ht i)
  exact ⟨Subgroup.pi Set.univ J, isOpen_set_pi Set.finite_univ fun i _ => h1 i,
    fun x hx => hI fun i _ => h2 i (hx i trivial), fun x hx i _ => h3 i (hx i trivial),
    fun x hx j hj i _ => h4 i _ (hx i trivial) _ (hj i trivial)⟩

end General

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α β : Type} [Fintype α] [Fintype β] [LinearOrder β]
  {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
  {c : α → β → Type} [∀ i j, Fintype (c i j)] [∀ i j, DecidableEq (c i j)]
  {W W' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']

theorem isSmoothChar_relDeltaHalf : IsSmoothChar (relDeltaHalf k c) := by
  unfold relDeltaHalf
  refine Finset.prod_induction _ IsSmoothChar (fun _ _ => IsSmoothChar.mul) isSmoothChar_one
    fun a _ => ?_
  exact (isSmoothChar_deltaHalf k).comp _ (continuous_apply a)

theorem relInd_surjective (f : ∀ i, (Σ j, c i j) ≃ m i)
    {π : Representation ℂ (∀ i, Levi k (c i)) W} {π' : Representation ℂ (∀ i, Levi k (c i)) W'}
    (p : π.IntertwiningMap π') (hp : Function.Surjective p) (hπ : IsSmooth π) :
    Function.Surjective (smIndMap (compMap (twistMap p (relDeltaHalf k c)) (relProj k f))) := by
  have H := fun i => GlobalTheory.SmGL.LeviInt.levi_integral_facts k β (m i) (c i) (f i)
  obtain ⟨_, _⟩ := SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have hP : IsClosed (relParab k f : Set (Levi k m)) :=
    isClosed_set_pi fun i _ => (H i).2.2.2.2.2.2.1
  have hK : IsCompact (Subgroup.pi Set.univ (fun i => KO k (m i)) : Set (Levi k m)) :=
    isCompact_univ_pi fun i => SplitFlip.isCompact_KO
  have hPK : ∀ g : Levi k m, ∃ q ∈ relParab k f, ∃ x ∈ Subgroup.pi Set.univ (fun i => KO k (m i)),
      g = q * x := fun g => by
    choose q hq x hx e using fun i => (H i).2.2.2.2.2.2.2.2 (g i)
    exact ⟨q, fun i _ => hq i, x, fun i _ => hx i, funext e⟩
  have hcont : Continuous (relProj k f) := continuous_pi fun i =>
    (H i).2.2.2.2.2.1.comp (((continuous_apply i).comp continuous_subtype_val).subtype_mk _)
  let σ₀ : Representation ℂ (relParab k f) W := (twist π (relDeltaHalf k c)).comp (relProj k f)
  let z : Representation.IntertwiningMap σ₀ σ₀ :=
    { toLinearMap := 0, isIntertwining' := fun _ => by ext; simp }
  refine (GlobalTheory.SmGL.IndCoinv.smInd_coinvariants (Levi k m) (relParab k f) _ hP hK hPK
    (exists_normalised_pi _ fun i => GlobalTheory.SmGL.exists_open_normalised_subgroup_subset k (m i)) _ _ _ _
    (isSmooth_comp (isSmooth_twist hπ isSmoothChar_relDeltaHalf) _ hcont)
    (compMap (twistMap p _) _) Unit (fun _ => z) hp ?_).1
  intro x _
  refine Submodule.subset_span ⟨(), -x, ?_⟩
  show x = (0 : _) - -x
  simp

end Local

theorem jhMult_relInd_exact : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (α β : Type) [Fintype α] [Fintype β] [LinearOrder β] (m : α → Type) [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] (c : α → β → Type) [∀ i j, Fintype (c i j)] [∀ i j, DecidableEq (c i j)] (f : ∀ i, (Σ j, c i j) ≃ m i) (W W₁ W₂ : Type) [AddCommGroup W] [Module ℂ W] [AddCommGroup W₁] [Module ℂ W₁] [AddCommGroup W₂] [Module ℂ W₂] (π : Representation ℂ (∀ i, GlobalTheory.SmGL.Levi k (c i)) W) (π₁ : Representation ℂ (∀ i, GlobalTheory.SmGL.Levi k (c i)) W₁) (π₂ : Representation ℂ (∀ i, GlobalTheory.SmGL.Levi k (c i)) W₂) (ι : π₁.IntertwiningMap π) (p : π.IntertwiningMap π₂), Function.Injective ι → Function.Surjective p → (∀ u, p (ι u) = 0) → (∀ v, p v = 0 → ∃ u, ι u = v) → GlobalTheory.PRep.IsSmooth π → ∀ (Y : Type) [AddCommGroup Y] [Module ℂ Y] (τ : Representation ℂ (GlobalTheory.SmGL.Levi k m) Y), τ.IsIrreducible → GlobalTheory.SmGL.jhMult τ (GlobalTheory.SmGL.relInd f π) = GlobalTheory.SmGL.jhMult τ (GlobalTheory.SmGL.relInd f π₁) + GlobalTheory.SmGL.jhMult τ (GlobalTheory.SmGL.relInd f π₂) := by
  intro k _ _ _ _ α β _ _ _ m _ _ c _ _ f W W₁ W₂ _ _ _ _ _ _ π π₁ π₂ ι p hι hp h0 hker hπ Y _ _ τ hτ
  refine GlobalTheory.JHMult.jhMult_exact
    (smIndMap (compMap (twistMap ι (relDeltaHalf k c)) (relProj k f)))
    (smIndMap (compMap (twistMap p (relDeltaHalf k c)) (relProj k f))) hτ
    (smIndMap_injective _ hι) (relInd_surjective f p hp hπ)
    (fun u => Subtype.ext (Subtype.ext (funext fun g => h0 _))) fun F hF => ?_
  exact exists_smIndMap_eq _ hι F fun g =>
    hker _ (congrFun (congrArg (fun χ => χ.1.1) hF) g)

end GlobalTheory.SmGL.IndExact
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions

namespace GlobalTheory.EmbeddingPlace

open NumberField IsDedekindDomain in
theorem _root_.GlobalTheory.EmbeddingPlace.finitePlace_le_one_iff {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (x : K) :
    FinitePlace.mk v x ≤ 1 ↔ v.valuation K x ≤ 1 := by
  rw [FinitePlace.mk_apply, FinitePlace.norm_embedding, NumberField.HeightOneSpectrum.adicAbv_def,
    NNReal.coe_le_one]
  exact WithZeroMulInt.toNNReal_le_one_iff (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v)

open NumberField IsDedekindDomain in
private theorem valuation_le_one_iff_exists_eq_mul_inv_of_notMem {R L : Type} [CommRing R] [IsDedekindDomain R]
    [Field L] [Algebra R L] [IsFractionRing R L] (v : HeightOneSpectrum R) (x : L) :
    v.valuation L x ≤ 1 ↔
      ∃ a, ∃ s ∉ v.asIdeal, x = algebraMap R L a * (algebraMap R L s)⁻¹ := by
  rw [← Valuation.mem_valuationSubring_iff,
    ← HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring,
    ← ValuationSubring.mem_toSubring, HeightOneSpectrum.valuationSubringAtPrime_toSubring,
    Subalgebra.mem_toSubring]
  simp only [Localization.subalgebra.ofField]
  change (∃ a s, ∃ (_ : s ∈ v.asIdeal.primeCompl),
      x = algebraMap R L a * (algebraMap R L s)⁻¹) ↔ _
  exact ⟨fun ⟨a, s, hs, h⟩ => ⟨a, s, hs, h⟩, fun ⟨a, s, hs, h⟩ => ⟨a, s, hs, h⟩⟩

open NumberField IsDedekindDomain in
private theorem exists_heightOneSpectrum_range_iff_finitePlace_le_one {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {K : Type} [Field K] [NumberField K] (p : ℕ) (hp : p ≠ 0)
    (hpO : (p : O) ∈ IsLocalRing.maximalIdeal O) (ι : K →+* FractionRing O) :
    ∃ la : HeightOneSpectrum (𝓞 K), (p : 𝓞 K) ∈ la.asIdeal ∧
      ∀ x : K, ι x ∈ (algebraMap O (FractionRing O)).range ↔ FinitePlace.mk la x ≤ 1 := by
  have hinj := IsFractionRing.injective O (FractionRing O)
  have hint : ∀ y : 𝓞 K, IsIntegral O (ι (algebraMap (𝓞 K) K y)) := fun y =>
    IsIntegral.map_of_comp_eq (algebraMap ℤ O) ι (RingHom.ext_int _ _)
      (RingOfIntegers.isIntegral_coe y)
  let ψ : 𝓞 K →+* O :=
    { toFun := fun y => IsIntegralClosure.mk' O (ι (algebraMap (𝓞 K) K y)) (hint y)
      map_one' := hinj (by simp [IsIntegralClosure.algebraMap_mk'])
      map_mul' := fun a b => hinj (by simp [IsIntegralClosure.algebraMap_mk'])
      map_zero' := hinj (by simp [IsIntegralClosure.algebraMap_mk'])
      map_add' := fun a b => hinj (by simp [IsIntegralClosure.algebraMap_mk']) }
  have hψ : ∀ y : 𝓞 K, algebraMap O (FractionRing O) (ψ y) = ι (algebraMap (𝓞 K) K y) :=
    fun y => IsIntegralClosure.algebraMap_mk' O _ (hint y)
  let P : Ideal (𝓞 K) := (IsLocalRing.maximalIdeal O).comap ψ
  have hpP : (p : 𝓞 K) ∈ P := Ideal.mem_comap.mpr (by rw [map_natCast]; exact hpO)
  have hPne : P ≠ ⊥ := by
    intro h
    have hp0 := hpP
    rw [h, Ideal.mem_bot, Nat.cast_eq_zero] at hp0
    exact hp hp0
  have hunitP : ∀ s : 𝓞 K, s ∉ P → IsUnit (ψ s) := fun s hs =>
    IsLocalRing.notMem_maximalIdeal.mp hs
  let la : HeightOneSpectrum (𝓞 K) :=
    { asIdeal := P, isPrime := Ideal.IsPrime.comap ψ, ne_bot := hPne }
  refine ⟨la, hpP, fun x => ?_⟩
  rw [_root_.GlobalTheory.EmbeddingPlace.finitePlace_le_one_iff]
  constructor
  · rintro ⟨o, ho⟩
    by_contra hx
    push_neg at hx
    have hx0 : x ≠ 0 := by
      rintro rfl
      simp at hx
    have hy : la.valuation K x⁻¹ < 1 := by
      rw [map_inv₀]
      exact inv_lt_one_of_one_lt₀ hx
    obtain ⟨a, s, hs, hxa⟩ := (valuation_le_one_iff_exists_eq_mul_inv_of_notMem la x⁻¹).mp hy.le
    have hs0 : algebraMap (𝓞 K) K s ≠ 0 := by
      have : s ≠ 0 := by
        rintro rfl
        exact hs (zero_mem _)
      exact (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr this
    have hsa : algebraMap (𝓞 K) K a = x⁻¹ * algebraMap (𝓞 K) K s := by
      rw [hxa, inv_mul_cancel_right₀ hs0]
    have hvs : la.valuation K (algebraMap (𝓞 K) K s) = 1 := by
      rw [HeightOneSpectrum.valuation_of_algebraMap]
      exact le_antisymm (la.intValuation_le_one s)
        (not_lt.mp fun h => hs ((la.intValuation_lt_one_iff_mem s).mp h))
    have hva : la.intValuation a < 1 := by
      rw [← HeightOneSpectrum.valuation_of_algebraMap (K := K)]
      change la.valuation K (algebraMap (𝓞 K) K a) < 1
      rw [hsa, map_mul, hvs, mul_one]
      exact hy
    have ha : ψ a ∈ IsLocalRing.maximalIdeal O :=
      Ideal.mem_comap.mp ((la.intValuation_lt_one_iff_mem a).mp hva)
    have heq : o * ψ a = ψ s := hinj (by
      rw [map_mul, ho, hψ, hψ, hsa, map_mul, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hx0,
        map_one, one_mul])
    have hunit : IsUnit (o * ψ a) := by
      rw [heq]
      exact hunitP s hs
    exact (IsLocalRing.mem_maximalIdeal _).mp ha (isUnit_of_mul_isUnit_right hunit)
  · intro h
    obtain ⟨a, s, hs, rfl⟩ := (valuation_le_one_iff_exists_eq_mul_inv_of_notMem la x).mp h
    refine ⟨ψ a * ↑(hunitP s hs).unit⁻¹, ?_⟩
    rw [map_mul, map_units_inv, IsUnit.unit_spec, hψ, hψ, map_mul, map_inv₀]


open NumberField IsDedekindDomain in
theorem _root_.GlobalTheory.EmbeddingPlace.exists_place : ∀ (D : _root_.Formalism.BasicNotions.D7) (Ks : Type) [Field Ks] [NumberField Ks] (i : D.ntw.Tw) (ι : Ks →+* FractionRing (D.ntw.O i)), ∃ la : HeightOneSpectrum (𝓞 Ks), ((D.ntw.l i : ℕ) : 𝓞 Ks) ∈ la.asIdeal ∧ ∀ x : Ks, ι x ∈ (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i))).range ↔ FinitePlace.mk la x ≤ 1 := by
  intro D Ks _ _ i ι
  haveI := D.ntw.domO i
  haveI := D.ntw.dvrO i
  exact exists_heightOneSpectrum_range_iff_finitePlace_le_one (D.ntw.l i) (D.ntw.lPrime i).out.ne_zero (D.ntw.O_l i) ι

end GlobalTheory.EmbeddingPlace
end

section

open NumberField IsDedekindDomain Formalism.L2.Host
noncomputable section

namespace GlobalTheory

open PI.AlgValsFin.W ReciprocityTheory.Neutral.Bridge.HCFR Neutral.B1

theorem isAlgebraic_embedding_apply {L : Type} [Field L] [NumberField L] (φ : L →+* ℂ) (x : L) :
    IsAlgebraic ℚ (φ x) :=
  (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom φ.toRatAlgHom

theorem heckeChar_val_isAlgebraic : ∀ (L : Type) [Field L] [NumberField L] (χ : HChar L) (m : (L →+* ℂ) → ℤ),
    (∀ k : Lˣ, ((χ.inf k : ℂˣ) : ℂ) = ∏ φ : L →+* ℂ, φ (k : L) ^ m φ) →
    ∀ w : HeightOneSpectrum (𝓞 L), IsAlgebraic ℚ ((χ.val w : ℂˣ) : ℂ) := by
  intro L _ _ χ m hm w
  classical

  obtain ⟨h, hpos, hk⟩ := (classPow : ClassPow L)
  obtain ⟨k, hk⟩ := hk w
  have hkw : ordF w k = (h : ℤ) := by rw [hk w, if_pos rfl]
  have hout : ∀ v, v ∉ ({w} : Finset (HeightOneSpectrum (𝓞 L))) → ordF v k = 0 := by
    intro v hv
    rw [hk v, if_neg (by simpa using hv)]
  obtain ⟨r, hr, hdec⟩ := (decomp : Decomp L) k {w} hout
  rw [Finset.prod_singleton] at hdec
  have hrel : χ.inf k * χ.loc w (atFin w k) * χ.1 r = 1 := by
    have e := χ.2.2 k
    rw [hdec, map_mul, map_mul] at e
    exact e
  obtain ⟨N, hN, hNt⟩ := torsUnits L χ

  have hinf : IsAlgebraic ℚ ((χ.inf k : ℂˣ) : ℂ) := by
    rw [hm k, ← mem_algebraicClosure_iff]
    refine prod_mem fun φ _ => zpow_mem ?_ _
    exact mem_algebraicClosure_iff.2 (isAlgebraic_embedding_apply φ _)

  have hloc : IsAlgebraic ℚ ((χ.loc w (atFin w k) : ℂˣ) : ℂ) := by
    have e : χ.loc w (atFin w k) ^ N = (χ.inf k ^ N)⁻¹ := by
      have e1 := congrArg (· ^ N) hrel
      simp only [mul_pow, hNt r hr, mul_one, one_pow] at e1
      exact eq_inv_of_mul_eq_one_right e1
    refine IsAlgebraic.of_pow hN ?_
    rw [← Units.val_pow_eq_pow_val, e, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val,
      ← mem_algebraicClosure_iff]
    exact inv_mem (pow_mem (mem_algebraicClosure_iff.2 hinf) _)

  set y : (w.adicCompletion L)ˣ := atFin w (unif w) ^ h * (atFin w k)⁻¹ with hy
  have hyv : Valued.v ((y : (w.adicCompletion L)ˣ) : w.adicCompletion L) = 1 := by
    have h1 : Valued.v ((atFin w (unif w) : (w.adicCompletion L)ˣ) : w.adicCompletion L) =
        WithZero.exp (-1) := unif_spec w
    rw [hy, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, map_mul, map_inv₀, map_pow, h1,
      valued_atFin, hkw, ← WithZero.exp_nsmul, ← WithZero.exp_neg, ← WithZero.exp_add]
    simp
  have hyU : localIdele L w y ∈ UFin L := by
    refine ⟨rfl, fun v => ?_⟩
    by_cases hv : v = w
    · subst hv
      rw [localIdele_snd_self]
      exact hyv
    · rw [(localIdele_isSupportedAt L w y).2 v hv, map_one]
  have hyN : χ.loc w y ^ N = 1 := hNt _ hyU
  have hyval : χ.loc w y = χ.val w ^ h * (χ.loc w (atFin w k))⁻¹ := by
    rw [hy, map_mul, map_pow, map_inv]
    rfl
  have hpow : χ.val w ^ (h * N) = χ.loc w (atFin w k) ^ N := by
    rw [hyval, mul_pow, ← pow_mul, inv_pow, mul_inv_eq_one] at hyN
    exact hyN
  refine IsAlgebraic.of_pow (Nat.mul_pos hpos hN) ?_
  rw [← Units.val_pow_eq_pow_val, hpow, Units.val_pow_eq_pow_val, ← mem_algebraicClosure_iff]
  exact pow_mem (mem_algebraicClosure_iff.2 hloc) _

end GlobalTheory
end
end
