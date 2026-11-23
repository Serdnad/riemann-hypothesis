module

public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle002
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle003
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle003
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LamIdealOfNotPrimePow
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RayClassIdealCountEqNcardShiftedBinaryForm
public import Mathlib.NumberTheory.LSeries.Basic
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle011
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle015
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
public import Mathlib.MeasureTheory.Function.Floor
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.RamificationInertia.Galois
public import Mathlib.NumberTheory.RamificationInertia.Unramified
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory.SelfDualLatticeCompare

section Field

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E}

theorem conj_conj (h : IsCMExt F E σ) (e : E) : σ (σ e) = e := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem exists_of_conj_eq (h : IsCMExt F E σ) (e : E) (he : σ e = e) :
    ∃ f, algebraMap F E f = e := by
  haveI := Subalgebra.isSimpleOrder_of_finrank h.2.2.1
  rcases eq_bot_or_eq_top (AlgHom.equalizer σ (AlgHom.id F E)) with h0 | h0
  · have : e ∈ AlgHom.equalizer σ (AlgHom.id F E) := he
    rw [h0, Algebra.mem_bot] at this
    exact this
  · exfalso
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    haveI := h.2.1
    refine IsTotallyComplex.complexEmbedding_not_isReal τ ?_
    rw [ComplexEmbedding.isReal_iff]
    ext x
    have hx : x ∈ AlgHom.equalizer σ (AlgHom.id F E) := h0 ▸ Algebra.mem_top
    have hx' : σ x = x := hx
    have := h.2.2.2 τ x
    rw [hx'] at this
    exact this.symm

theorem trace_field (h : IsCMExt F E σ) (e : E) :
    algebraMap F E (Algebra.trace F E e) = e + σ e := by
  have hσ := conj_conj h
  obtain ⟨a, ha⟩ := exists_of_conj_eq h (e + σ e) (by rw [map_add (f := _), hσ, add_comm])
  have h1 : Algebra.trace F E (σ e) = Algebra.trace F E e :=
    Algebra.trace_eq_of_algEquiv (AlgEquiv.ofAlgHom σ σ (AlgHom.ext hσ) (AlgHom.ext hσ)) e
  have h3 := congrArg (Algebra.trace F E) ha
  rw [Algebra.trace_algebraMap, h.2.2.1, map_add (f := _), h1, two_smul, ← two_mul, ← two_mul] at h3
  rw [← ha, mul_left_cancel₀ two_ne_zero h3]

variable (R : Type) [CommRing R] [Algebra F R]

theorem trace_tensor (h : IsCMExt F E σ) (z : R ⊗[F] E) :
    algebraMap R (R ⊗[F] E) (Algebra.trace R (R ⊗[F] E) z) = z + sigR R σ z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb]; ring
  | tmul a e =>
    have h1 : a ⊗ₜ[F] e = a • ((1 : R) ⊗ₜ[F] e) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    have h3 : Algebra.trace R (R ⊗[F] E) (a ⊗ₜ[F] e) =
        a * algebraMap F R (Algebra.trace F E e) := by
      rw [h1, map_smul, Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul,
        LinearMap.trace_baseChange, smul_eq_mul]
    have h4 : sigR R σ (a ⊗ₜ[F] e) = a ⊗ₜ[F] σ e := rfl
    rw [h3, h4, ← TensorProduct.tmul_add, ← trace_field h, Algebra.TensorProduct.algebraMap_apply,
      Algebra.algebraMap_self, RingHom.id_apply, mul_comm, ← Algebra.smul_def,
      TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one]

theorem sigR_sigR (h : IsCMExt F E σ) (z : R ⊗[F] E) : sigR R σ (sigR R σ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb]
  | tmul a e =>
    show a ⊗ₜ[F] σ (σ e) = _
    rw [conj_conj h]

theorem hR_self (h : IsCMExt F E σ) {M : ℕ} {J : Matrix (Fin M) (Fin M) E} (hJ : IsHermND σ J)
    (x : Fin M → R ⊗[F] E) : hR R σ J x x = algebraMap R (R ⊗[F] E) (qR R σ J x) := by
  have hJ' : ∀ i j, sigR R σ (JR R J j i) = JR R J i j := by
    intro i j
    show (1 : R) ⊗ₜ[F] σ (J j i) = (1 : R) ⊗ₜ[F] J i j
    rw [hJ.1]
  have hs : sigR R σ (hR R σ J x x) = hR R σ J x x := by

    simp only [hR, Formalism.UG.hform, map_sum, map_mul, sigR_sigR R h]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hJ']
    ring
  have h2 : algebraMap R (R ⊗[F] E) (algebraMap F R (1 / 2)) * 2 = 1 := by
    rw [← IsScalarTower.algebraMap_apply, ← map_ofNat (algebraMap F (R ⊗[F] E)) 2, ← map_mul,
      show (1 / 2 * 2 : F) = 1 by norm_num, map_one]
  rw [qR, map_mul, trace_tensor R h, hs, ← two_mul, ← mul_assoc, h2, one_mul]

theorem hR_smul_right {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (x y : Fin M → R ⊗[F] E)
    (c : R ⊗[F] E) : hR R σ J x (c • y) = c * hR R σ J x y := by
  simp only [hR, Formalism.UG.hform, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

end Field

section Clauses

open GlobalTheory.IndefiniteRowSideFullHecke

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (v : HeightOneSpectrum (𝓞 F))

theorem unram_iff : UnitaryLatticeOrthogonal.UnramAt F E v ↔ SelfDualLatticeActions.UnramifiedOrSplit E v := by
  refine forall_congr' fun w => forall_congr' fun hw => ?_
  haveI := w.isPrime
  haveI := w.isMaximal
  exact Ideal.ramificationIdx_eq_one_iff

theorem isSDLat_iff (L : Submodule (SelfDualLatticeActions.OEv E v) (SelfDualLatticeActions.Wv E v M)) :
    UnitaryLatticeOrthogonal.IsSDLat σ J v L ↔ SelfDualLatticeActions.IsSelfDualLat v σ J L := Iff.rfl

theorem hasONB_iff (L : Submodule (SelfDualLatticeActions.OEv E v) (SelfDualLatticeActions.Wv E v M)) :
    UnitaryLatticeOrthogonal.HasONB σ J v L ↔ SelfDualLatticeActions.HasOrthonormalBasis v σ J L := by
  refine exists_congr fun b => ?_
  rw [← Matrix.ext_iff]
  refine forall_congr' fun i => forall_congr' fun j => ?_
  rw [Matrix.one_apply]
  exact Iff.rfl

theorem disjoint_span_perpLat (h : IsCMExt F E σ) (hJ : IsHermND σ J)
    (L : Submodule (SelfDualLatticeActions.OEv E v) (SelfDualLatticeActions.Wv E v M)) (x : SelfDualLatticeActions.Wv E v M)
    (hx : IsUnit (qR (Fv F v) σ J x)) :
    Disjoint (Submodule.span (SelfDualLatticeActions.OEv E v) {x}) (SelfDualLatticeActions.perpLat v σ J x L) := by
  rw [Submodule.disjoint_def]
  intro y hy hy'
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
  have h0 : hR (Fv F v) σ J x ((c : SelfDualLatticeActions.Ev E v) • x) = 0 := hy'.1
  rw [hR_smul_right, hR_self _ h hJ, (hx.map _).mul_left_eq_zero] at h0
  show (c : SelfDualLatticeActions.Ev E v) • x = 0
  rw [h0, zero_smul]

theorem unitVectors_iff (h : IsCMExt F E σ) (hJ : IsHermND σ J)
    (L : Submodule (SelfDualLatticeActions.OEv E v) (SelfDualLatticeActions.Wv E v M)) (β : Fv F v) (hβ : IsUnit β) :
    UnitaryLatticeOrthogonal.UnitVectors σ J v L β ↔ SelfDualLatticeActions.UnitVectorClaims v σ J L β := by
  refine and_congr Iff.rfl (and_congr ?_ Iff.rfl)
  refine forall_congr' fun x => forall_congr' fun hx => ?_
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1.symm, disjoint_span_perpLat σ J v h hJ L x (hx.2 ▸ hβ), h2⟩
  · rintro ⟨h1, -, h2⟩
    exact ⟨h1.symm, h2⟩

theorem conclusion_iff (h : IsCMExt F E σ) (hJ : IsHermND σ J)
    (L : Submodule (SelfDualLatticeActions.OEv E v) (SelfDualLatticeActions.Wv E v M)) :
    (UnitaryLatticeOrthogonal.HasONB σ J v L ∧
      (∀ L₁ : Submodule (UnitaryLatticeOrthogonal.OEv F E v) (Fin M → UnitaryLatticeOrthogonal.Ev F E v), UnitaryLatticeOrthogonal.IsSDLat σ J v L₁ →
        ∃ g : HA (Fv F v) σ J, ∀ y, y ∈ L ↔ UnitaryLatticeOrthogonal.act σ J v g y ∈ L₁) ∧
      ∀ β : (v.adicCompletionIntegers F)ˣ,
        UnitaryLatticeOrthogonal.UnitVectors σ J v L ((β : v.adicCompletionIntegers F) : Fv F v)) ↔
    (SelfDualLatticeActions.HasOrthonormalBasis v σ J L ∧
      (∀ L' : Submodule (SelfDualLatticeActions.OEv E v) (SelfDualLatticeActions.Wv E v M), SelfDualLatticeActions.IsSelfDualLat v σ J L' →
        ∃ g : HA (Fv F v) σ J, ∀ y, y ∈ L ↔ SelfDualLatticeActions.act v σ J g y ∈ L') ∧
      ∀ β : (v.adicCompletionIntegers F)ˣ,
        SelfDualLatticeActions.UnitVectorClaims v σ J L ((β : v.adicCompletionIntegers F) : Fv F v)) :=
  and_congr (hasONB_iff σ J v L) (and_congr Iff.rfl (forall_congr' fun β =>
    unitVectors_iff σ J v h hJ L _ (β.isUnit.map (v.adicCompletionIntegers F).subtype)))

end Clauses

theorem selfDualLattices_iff :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal.SelfDualLattices ↔ GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeActions.SelfDualLatticeLemmas := by
  refine forall_congr' fun F => forall_congr' fun E => forall_congr' fun _ =>
    forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun _ =>
    forall_congr' fun σ => forall_congr' fun h => forall_congr' fun M => forall_congr' fun J => ?_
  rw [imp.swap]
  refine forall_congr' fun _ => forall_congr' fun hJ => forall_congr' fun v => ?_
  refine imp_congr (unram_iff v) (forall_congr' fun L => ?_)
  exact imp_congr (isSDLat_iff σ J v L) (conclusion_iff σ J v h hJ L)

end GlobalTheory.SelfDualLatticeCompare
end
end

section

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory.UnramifiedDiscriminant

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E}

open scoped TensorProduct in
open NumberField IsDedekindDomain MeasureTheory Topology in
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} in
private lemma isCMExt_conj_ne_id (h : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ) : σ ≠ AlgHom.id F E := by
  obtain ⟨-, hE, -, hτ⟩ := h
  intro hσ
  let τ : E →+* ℂ := (IsAlgClosed.lift (M := ℂ) (R := ℚ) (S := E)).toRingHom
  have hc := hE.isComplex (InfinitePlace.mk τ)
  rw [InfinitePlace.isComplex_mk_iff] at hc
  apply hc
  rw [ComplexEmbedding.isReal_iff]
  ext x
  rw [ComplexEmbedding.conjugate_coe_eq]
  have hx := hτ τ x
  rw [hσ, AlgHom.id_apply] at hx
  exact hx.symm

open scoped TensorProduct in
open NumberField IsDedekindDomain MeasureTheory Topology in
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} in
private lemma isCMExt_mem_range_of_conj_fixed (h : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ) {x : E} (hx : σ x = x) :
    x ∈ Set.range (algebraMap F E) := by
  have hprime : (Module.finrank F E).Prime := by rw [h.2.2.1]; exact Nat.prime_two
  haveI := Subalgebra.isSimpleOrder_of_finrank_prime F E hprime
  rcases eq_bot_or_eq_top (AlgHom.equalizer σ (AlgHom.id F E)) with h0 | h1
  · have hmem : x ∈ AlgHom.equalizer σ (AlgHom.id F E) := hx
    rw [h0] at hmem
    exact Algebra.mem_bot.mp hmem
  · exfalso
    apply isCMExt_conj_ne_id h
    ext y
    have hmem : y ∈ AlgHom.equalizer σ (AlgHom.id F E) := h1 ▸ Algebra.mem_top
    exact hmem


open scoped TensorProduct in
open NumberField IsDedekindDomain MeasureTheory Topology in
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} in
theorem _root_.GlobalTheory.UnramifiedDiscriminant.exists_int_of_conj_eq (h : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ) (a : 𝓞 E) (ha : σ a = a) :
    ∃ t : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) t = a := by
  obtain ⟨f, hf⟩ := isCMExt_mem_range_of_conj_fixed h ha
  have hint : IsIntegral ℤ f := by
    rw [← isIntegral_algebraMap_iff (B := E), hf]
    exact RingOfIntegers.isIntegral_coe a
  refine ⟨⟨f, hint⟩, ?_⟩
  ext
  exact hf

open scoped TensorProduct in
open NumberField IsDedekindDomain MeasureTheory Topology in
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} in
private lemma isCMExt_conj_conj (h : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨-, -, -, hτ⟩ := h
  let τ : E →+* ℂ := (IsAlgClosed.lift (M := ℂ) (R := ℚ) (S := E)).toRingHom
  apply τ.injective
  rw [hτ, hτ, star_star]

open scoped TensorProduct in
open NumberField IsDedekindDomain MeasureTheory Topology in
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} in
theorem _root_.GlobalTheory.UnramifiedDiscriminant.exists_discr_notMem (F E : Type) [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (h : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ)
    (v : HeightOneSpectrum (𝓞 F)) (hv : _root_.GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.UnramifiedPlace F E v) :
    ∃ (w : E) (t n : 𝓞 F), w + σ w = algebraMap F E (t : F) ∧ w * σ w = algebraMap F E (n : F) ∧
      t ^ 2 - 4 * n ∉ v.asIdeal := by
  have hinj : Function.Injective (algebraMap (𝓞 F) (𝓞 E)) := FaithfulSMul.algebraMap_injective _ _
  obtain ⟨P, -, hPp, hPv⟩ := Ideal.exists_ideal_over_prime_of_isIntegral v.asIdeal (⊥ : Ideal (𝓞 E))
    (by rw [(show Ideal.under _ ⊥ = ⊥ from Ideal.comap_bot_of_injective _ hinj)]; exact bot_le)
  have hPne : P ≠ ⊥ := by
    rintro rfl
    apply v.ne_bot
    rw [← hPv, (show Ideal.under _ ⊥ = ⊥ from Ideal.comap_bot_of_injective _ hinj)]
  haveI : P.LiesOver v.asIdeal := ⟨hPv.symm⟩
  haveI : Algebra.IsUnramifiedAt (𝓞 F) P := hv ⟨P, hPp, hPne⟩ ⟨hPv.symm⟩
  let σ' : E ≃ₐ[F] E := AlgEquiv.ofBijective σ (Function.Involutive.bijective (isCMExt_conj_conj h))
  haveI : IsGalois F E := by
    refine IsGalois.of_fixedField_eq_bot F E (eq_bot_iff.mpr fun x hx => ?_)
    exact IntermediateField.mem_bot.mpr (isCMExt_mem_range_of_conj_fixed h
      ((IntermediateField.mem_fixedField_iff _ _).mp hx σ' (Subgroup.mem_top _)))
  have hcard : Nat.card (P.inertia (E ≃ₐ[F] E)) = 1 := by
    rw [Ideal.card_inertia_eq_ramificationIdxIn v.asIdeal P,
      Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal P (E ≃ₐ[F] E)]
    exact Ideal.ramificationIdx_eq_one_of_isUnramifiedAt
  obtain ⟨x, hx⟩ : ∃ x : 𝓞 E, σ' • x - x ∉ P := by
    by_contra hcon
    push_neg at hcon
    have hmem : σ' ∈ P.inertia (E ≃ₐ[F] E) := hcon
    haveI := (Nat.card_eq_one_iff_unique.mp hcard).1
    have h1 : σ' = 1 := congrArg Subtype.val (Subsingleton.elim (⟨σ', hmem⟩ : P.inertia _) 1)
    apply isCMExt_conj_ne_id h
    ext z
    exact DFunLike.congr_fun h1 z
  set y : 𝓞 E := σ' • x
  have hy : (y : E) = σ x := rfl
  obtain ⟨t, ht⟩ := _root_.GlobalTheory.UnramifiedDiscriminant.exists_int_of_conj_eq h (x + y) (by
    show σ ((x : E) + σ x) = (x : E) + σ x
    rw [map_add (f := _), isCMExt_conj_conj h, add_comm])
  obtain ⟨n, hn⟩ := _root_.GlobalTheory.UnramifiedDiscriminant.exists_int_of_conj_eq h (x * y) (by
    show σ ((x : E) * σ x) = (x : E) * σ x
    rw [map_mul, isCMExt_conj_conj h, mul_comm])
  refine ⟨x, t, n, ?_, ?_, ?_⟩
  · rw [← hy]
    exact (congrArg (fun z : 𝓞 E => (z : E)) ht).symm
  · rw [← hy]
    exact (congrArg (fun z : 𝓞 E => (z : E)) hn).symm
  · intro hmem
    have hP : algebraMap (𝓞 F) (𝓞 E) (t ^ 2 - 4 * n) ∈ P := by
      rw [← hPv] at hmem
      exact Ideal.mem_comap.mp hmem
    have heq : algebraMap (𝓞 F) (𝓞 E) (t ^ 2 - 4 * n) = (y - x) ^ 2 := by
      rw [map_sub, map_pow, map_mul, ht, hn, map_ofNat]
      ring
    rw [heq] at hP
    exact hx (hPp.mem_of_pow_mem 2 hP)

end GlobalTheory.UnramifiedDiscriminant
end

section

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical

namespace GlobalTheory.Lin

open MeasureTheory in
private lemma measurable_norm_sum_primesIoc (a : ℕ → ℂ) (x : ℝ) :
    Measurable (fun t : ℝ => ‖∑ p ∈ _root_.GlobalTheory.Lin.primesIoc x t, a p‖) := by
  have h : (fun t : ℝ => ‖∑ p ∈ _root_.GlobalTheory.Lin.primesIoc x t, a p‖) =
      (fun n : ℕ => ‖∑ p ∈ (Finset.Ioc ⌊x⌋₊ n).filter Nat.Prime, a p‖) ∘ Nat.floor := by
    funext t
    rfl
  rw [h]
  exact measurable_from_nat.comp Nat.measurable_floor

open MeasureTheory in
private lemma norm_sum_primesIoc_le_sum_range (a : ℕ → ℂ) (x y t : ℝ) (hty : t ≤ y) :
    ‖∑ p ∈ _root_.GlobalTheory.Lin.primesIoc x t, a p‖ ≤ ∑ n ∈ Finset.range (⌊y⌋₊ + 1), ‖a n‖ := by
  refine (norm_sum_le _ _).trans
    (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => norm_nonneg _))
  intro n hn
  have hn' := (Finset.mem_filter.1 hn).1
  have h1 := (Finset.mem_Ioc.1 hn').2
  have h2 : ⌊t⌋₊ ≤ ⌊y⌋₊ := Nat.floor_le_floor hty
  exact Finset.mem_range.2 (by omega)

open MeasureTheory in
private lemma integrableOn_norm_sum_primesIoc_pow_div (a : ℕ → ℂ) (x y : ℝ) (hx : 0 < x)
    (k : ℕ) :
    IntegrableOn (fun t : ℝ => ‖∑ p ∈ _root_.GlobalTheory.Lin.primesIoc x t, a p‖ ^ k / t) (Set.Icc x y) := by
  set B := ∑ n ∈ Finset.range (⌊y⌋₊ + 1), ‖a n‖
  refine Measure.integrableOn_of_bounded (M := B ^ k / x) (by simp)
    (((measurable_norm_sum_primesIoc a x).pow_const k).div measurable_id).aestronglyMeasurable ?_
  refine ae_restrict_of_forall_mem measurableSet_Icc (fun t ht => ?_)
  have ht0 : 0 < t := hx.trans_le ht.1
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact div_le_div₀ (by positivity)
    (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_primesIoc_le_sum_range a x y t ht.2) k) hx ht.1


open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology in
open scoped Classical in
theorem _root_.GlobalTheory.Lin.sq_integral_primeSum_div_le (a : ℕ → ℂ) (x y : ℝ) (hx : 1 ≤ x) (hxy : x ≤ y) :
    (∫ t in x..y, ‖∑ p ∈ _root_.GlobalTheory.Lin.primesIoc x t, a p‖ / t) ^ 2 ≤
      Real.log (y / x) * ∫ t in x..y, ‖∑ p ∈ _root_.GlobalTheory.Lin.primesIoc x t, a p‖ ^ 2 / t := by
  have hx0 : 0 < x := by linarith
  have hI : ∀ k : ℕ, IntervalIntegrable
      (fun t : ℝ => ‖∑ p ∈ _root_.GlobalTheory.Lin.primesIoc x t, a p‖ ^ k / t) volume x y := by
    intro k
    refine IntegrableOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hxy]
    exact integrableOn_norm_sum_primesIoc_pow_div a x y hx0 k
  have hI1 : IntervalIntegrable
      (fun t : ℝ => ‖∑ p ∈ _root_.GlobalTheory.Lin.primesIoc x t, a p‖ / t) volume x y := by
    simpa only [pow_one] using hI 1
  have hI0 : IntervalIntegrable (fun t : ℝ => 1 / t) volume x y := by
    refine ContinuousOn.intervalIntegrable ?_
    refine continuousOn_const.div continuousOn_id (fun t ht => ?_)
    rw [Set.uIcc_of_le hxy] at ht
    exact (hx0.trans_le ht.1).ne'
  have hlog : ∫ t in x..y, 1 / t = Real.log (y / x) := integral_one_div_of_pos hx0 (by linarith)
  have hquad : ∀ c : ℝ, 0 ≤ Real.log (y / x) * (c * c) +
      (-2 * ∫ t in x..y, ‖∑ p ∈ _root_.GlobalTheory.Lin.primesIoc x t, a p‖ / t) * c +
      ∫ t in x..y, ‖∑ p ∈ _root_.GlobalTheory.Lin.primesIoc x t, a p‖ ^ 2 / t := by
    intro c
    have h0 : 0 ≤ ∫ t in x..y, (c - ‖∑ p ∈ _root_.GlobalTheory.Lin.primesIoc x t, a p‖) ^ 2 / t :=
      intervalIntegral.integral_nonneg hxy
        (fun t ht => div_nonneg (sq_nonneg _) (hx0.trans_le ht.1).le)
    have heq : ∫ t in x..y, (c - ‖∑ p ∈ _root_.GlobalTheory.Lin.primesIoc x t, a p‖) ^ 2 / t =
        (c * c) * (∫ t in x..y, 1 / t) -
          (2 * c) * (∫ t in x..y, ‖∑ p ∈ _root_.GlobalTheory.Lin.primesIoc x t, a p‖ / t) +
          ∫ t in x..y, ‖∑ p ∈ _root_.GlobalTheory.Lin.primesIoc x t, a p‖ ^ 2 / t := by
      rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
        ← intervalIntegral.integral_sub (hI0.const_mul _) (hI1.const_mul _),
        ← intervalIntegral.integral_add ((hI0.const_mul _).sub (hI1.const_mul _)) (hI 2)]
      congr 1
      funext t
      ring
    rw [heq, hlog] at h0
    linarith
  have hd := discrim_le_zero hquad
  unfold discrim at hd
  nlinarith [hd]

end GlobalTheory.Lin
end

section

open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical

theorem _root_.GlobalTheory.T.rayClassIdealCount_eq_ncard_shiftedBinaryForm : ∀ (K : Type) [Field K] [NumberField K] (d M : ℕ) (x : K), d.Prime → d % 4 = 3 → 100 ≤ d → x ^ 2 = -(d : K) → Module.finrank ℚ K = 2 → 3 ≤ M → ∀ D : RayData K M, ∀ g : D.G, ∃ α γ l θ₁ θ₂ : ℝ, 1 ≤ α ∧ 1 ≤ γ ∧ α * γ = d * (M : ℝ) ^ 4 / 4 ∧ (∀ v : ℤ × ℤ, ∃ n : ℕ, 1 ≤ n ∧ qForm α γ l θ₁ θ₂ v = n) ∧ ∀ n : ℕ, aRay D g n = (({v : ℤ × ℤ | qForm α γ l θ₁ θ₂ v = n}.ncard : ℕ) : ℝ) := by
  first | exact @GlobalTheory.Hk.RayForm.aRay_eq_ncard_qForm | exact GlobalTheory.Hk.RayForm.aRay_eq_ncard_qForm | (intros; apply GlobalTheory.Hk.RayForm.aRay_eq_ncard_qForm <;> assumption)
end

section

open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical

theorem _root_.GlobalTheory.T.rayClassLFunctionFamily_logDeriv_positivity : ∀ (𝓕 : LFam) (χ ψ : AddChar 𝓕.G ℂ) (σ t : ℝ), 1 < σ → 0 ≤ 3 * (LSeries (𝓕.lamChi 1) σ).re + 4 * (LSeries (𝓕.lamChi χ) (σ + t * I)).re + (LSeries (𝓕.lamChi (χ * χ)) (σ + 2 * t * I)).re ∧ 0 ≤ (LSeries (𝓕.lamChi 1) σ).re ∧ (χ * χ = 1 → ψ * ψ = 1 → 0 ≤ (LSeries (𝓕.lamChi 1) σ).re + (LSeries (𝓕.lamChi χ) σ).re ∧ 0 ≤ (LSeries (𝓕.lamChi 1) σ).re + (LSeries (𝓕.lamChi χ) σ).re + (LSeries (𝓕.lamChi ψ) σ).re + (LSeries (𝓕.lamChi (χ * ψ)) σ).re) := by
  first | exact @GlobalTheory.Hk.LFamPos.positivity | exact GlobalTheory.Hk.LFamPos.positivity | (intros; apply GlobalTheory.Hk.LFamPos.positivity <;> assumption)
end

section

open Complex
open scoped Real

theorem _root_.GlobalTheory.T.jacobiTripleFiniteCoeff_tendsto_and_bounded : ∀ t : ℂ, ‖t‖ < 1 → (∀ j : ℤ, Filter.Tendsto (fun n : ℕ => GlobalTheory.JacobiTriple.finCoeff t n j) Filter.atTop (nhds (GlobalTheory.JacobiTriple.qPochInf t)⁻¹)) ∧ ∃ C : ℝ, ∀ (n : ℕ) (j : ℤ), ‖GlobalTheory.JacobiTriple.finCoeff t n j‖ ≤ C := by
  first | exact @GlobalTheory.JacobiTriple.finCoeff_tendsto_and_bounded | exact GlobalTheory.JacobiTriple.finCoeff_tendsto_and_bounded | (intros; apply GlobalTheory.JacobiTriple.finCoeff_tendsto_and_bounded <;> assumption)
end
