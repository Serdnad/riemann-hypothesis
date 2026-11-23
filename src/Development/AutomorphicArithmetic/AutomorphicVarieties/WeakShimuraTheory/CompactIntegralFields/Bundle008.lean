module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.IsClassFieldHilbert
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.KwAbsRam
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.MkTower
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.Bundle007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ContinuousResP
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.CmplEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.ContResQ
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.HomOfDer
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.ImportsAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.Bundle007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ValuationCharacters.ConstOfFinite
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ValuationCharacters.ValLtIff
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.Radical.NatInt
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

@[expose] public section

local instance (priority := 2000) ratFieldIsTorsionFreeForCompactIntegralFieldsBundle008
    (Ω : Type) [Field Ω] [CharZero Ω] : Module.IsTorsionFree ℚ Ω :=
  DivisionSemiring.to_moduleIsTorsionFree

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem dx_conj {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (j : Ω →+* ℂ) :
    ∃ c : G ℚ Ω, ∀ x, j (c x) = starRingEnd ℂ (j x) := by
  haveI : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  letI : Algebra Ω ℂ := j.toAlgebra
  haveI : IsScalarTower ℚ Ω ℂ := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  let s : ℂ ≃ₐ[ℚ] ℂ := AlgEquiv.ofRingEquiv (f := starRingAut (R := ℂ)) fun x => by simp
  exact ⟨s.restrictNormal Ω, fun x => s.restrictNormal_commutes Ω x⟩

private theorem dx_field {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (F : IntermediateField ℚ Ω) [IsTotallyReal F]
    (H : Subgroup (G ℚ Ω)) (hH : IsOpen (H : Set (G ℚ Ω))) (hc : commutator (G ℚ Ω) ≤ H) (m : ℕ) (hm : Odd m)
    (hp : ∀ g ∈ F.fixingSubgroup, g ^ m ∈ H) :
    ∃ L : IntermediateField ℚ Ω, L.fixingSubgroup = H ∧ NumberField L ∧ IsTotallyReal L ∧ IsAbelianGalois ℚ L := by
  have : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  have : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  let N : ClosedSubgroup (Ω ≃ₐ[ℚ] Ω) := ⟨H, Subgroup.isClosed_of_isOpen H hH⟩
  obtain ⟨L, hfix⟩ : ∃ L : IntermediateField ℚ Ω, L.fixingSubgroup = H :=
    ⟨_, InfiniteGalois.fixingSubgroup_fixedField N⟩
  subst hfix
  have : FiniteDimensional ℚ L := (InfiniteGalois.isOpen_iff_finite L).1 hH
  have hG : IsGalois ℚ L := (InfiniteGalois.normal_iff_isGalois _).1 (Subgroup.Normal.of_commutator_le _ hc)
  have : NumberField L := NumberField.of_module_finite ℚ _
  have hker : ∀ g ∈ L.fixingSubgroup, UpperTheory.V.CF.resTo ℚ L Ω g = 1 := fun g hg => by
    refine AlgEquiv.ext fun x => (algebraMap L Ω).injective ?_
    rw [UpperTheory.V.CF.resTo_commutes]
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg _ x.2
  have hab : IsAbelianGalois ℚ L :=
    { is_comm := ⟨fun a b => by
        obtain ⟨a, rfl⟩ := UpperTheory.V.CF.resTo_surjective ℚ L Ω a
        obtain ⟨b, rfl⟩ := UpperTheory.V.CF.resTo_surjective ℚ L Ω b
        rw [← commutatorElement_eq_one_iff_mul_comm, ← map_commutatorElement]
        exact hker _ (hc (Subgroup.commutator_mem_commutator trivial trivial))⟩ }
  refine ⟨L, rfl, this, ⟨fun w => ?_⟩, hab⟩
  letI : Algebra L ℂ := w.embedding.toAlgebra
  haveI : Algebra.IsAlgebraic L Ω := Algebra.IsAlgebraic.tower_top (K := ℚ) L
  let j : Ω →ₐ[L] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  obtain ⟨c, hcj⟩ := dx_conj (j : Ω →+* ℂ)
  have h2 : c ^ 2 = 1 := AlgEquiv.ext fun x => (j : Ω →+* ℂ).injective (by
    rw [pow_two, AlgEquiv.mul_apply, hcj, hcj]; simp)
  have hF : c ∈ F.fixingSubgroup := (F.mem_fixingSubgroup_iff c).2 fun x hx => (j : Ω →+* ℂ).injective (by
    rw [hcj]
    have h := IsTotallyReal.complexEmbedding_isReal (K := F) ((j : Ω →+* ℂ).comp (algebraMap F Ω))
    exact RingHom.congr_fun h ⟨x, hx⟩)
  have hL : c ∈ L.fixingSubgroup := by
    obtain ⟨k, rfl⟩ := hm
    have := hp c hF
    rwa [pow_succ, pow_mul, h2, one_pow, one_mul] at this
  rw [InfinitePlace.isReal_iff]
  refine RingHom.ext fun x => ?_
  have h3 := hcj x
  rw [(L.mem_fixingSubgroup_iff c).1 hL x x.2] at h3
  have h4 : (j : Ω →+* ℂ) x = w.embedding x := j.commutes x
  rw [h4] at h3
  exact h3.symm

private theorem dx_mu {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {w : ℕ} (hw : w ≠ 0) (g : G ℚ Ω)
    (hg : ∀ ζ : Ω, ζ ^ w = 1 → g ζ = ζ) (n : ℕ) : ∀ ζ : Ω, ζ ^ w ^ (n + 1) = 1 → (g ^ w ^ n) ζ = ζ := by
  induction n with
  | zero => simpa using hg
  | succ n ih =>
    intro ζ hζ
    set h := g ^ w ^ n with hh
    have h0 : ζ ≠ 0 := by
      rintro rfl
      rw [zero_pow (pow_ne_zero _ hw)] at hζ
      exact zero_ne_one hζ
    have h1 : h (ζ ^ w) = ζ ^ w := ih _ (by rw [← pow_mul, ← pow_succ']; exact hζ)
    have h2 : (h ζ / ζ) ^ w = 1 := by rw [div_pow, ← map_pow, h1, div_self (pow_ne_zero _ h0)]
    have h3 : h (h ζ / ζ) = h ζ / ζ := ih _ (by rw [pow_succ', pow_mul, h2, one_pow])
    have h4 : ∀ k : ℕ, (h ^ k) ζ = (h ζ / ζ) ^ k * ζ := fun k => by
      induction k with
      | zero => simp
      | succ k ih2 =>
        rw [pow_succ', AlgEquiv.mul_apply, ih2, map_mul, map_pow, h3, pow_succ, mul_assoc, div_mul_cancel₀ _ h0]
    rw [pow_succ, pow_mul, ← hh, h4, h2, one_mul]

private theorem dx_ker {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l w : ℕ} (hl : l.Prime) (hw : w.Prime) (hne : w ≠ l)
    (θ : G ℚ Ω →* Multiplicative (ZMod l)) (ho : IsOpen (θ.ker : Set (G ℚ Ω)))
    (hu : ∀ A, Raw.Away {w} A → Ine (F := ℚ) A ≤ θ.ker) (g : G ℚ Ω) (hg : ∀ ζ : Ω, ζ ^ w = 1 → g ζ = ζ) : g ∈ θ.ker := by
  obtain ⟨n, hn⟩ := UpperTheory.V.CF.kwAbsRam Ω θ.ker ho (Abelianization.commutator_subset_ker θ) w hw.pos
    fun A hA => hu A fun p hp => by rw [Finset.mem_singleton.1 hp]; exact hA
  have h1 := hn (g ^ w ^ n) fun ζ hζ => dx_mu hw.ne_zero g hg n ζ (by rw [pow_succ, pow_mul, hζ, one_pow])
  rw [MonoidHom.mem_ker, map_pow] at h1
  haveI : NeZero l := ⟨hl.ne_zero⟩
  have h2 : θ g ^ l = 1 := by
    have := pow_card_eq_one (x := θ g)
    rwa [Fintype.card_multiplicative, ZMod.card] at this
  have h3 := pow_gcd_eq_one.2 ⟨h1, h2⟩
  rw [Nat.Coprime.gcd_eq_one (((Nat.coprime_primes hw hl).2 hne).pow_left n), pow_one] at h3
  exact h3

private theorem dx_open {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {w : ℕ} (hw : w ≠ 0) (H : Subgroup (G ℚ Ω))
    (h : ∀ g : G ℚ Ω, (∀ ζ : Ω, ζ ^ w = 1 → g ζ = ζ) → g ∈ H) : IsOpen (H : Set (G ℚ Ω)) := by
  have : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  have hf : Set.Finite {ζ : Ω | ζ ^ w = 1} := by
    refine (nthRootsFinset w (1 : Ω)).finite_toSet.subset fun ζ hζ => ?_
    exact (mem_nthRootsFinset (Nat.pos_of_ne_zero hw) _).2 hζ
  haveI := hf.to_subtype
  haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {ζ : Ω | ζ ^ w = 1}) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  refine Subgroup.isOpen_mono (H₁ := (IntermediateField.adjoin ℚ {ζ : Ω | ζ ^ w = 1}).fixingSubgroup) (fun g hg => h g fun ζ hζ => ?_)
    (IntermediateField.fixingSubgroup_isOpen _)
  exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg ζ (IntermediateField.subset_adjoin _ _ hζ)

theorem UpperTheory.V.Ws.diesEx :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ T : Tower D, TameL l T.F → T.Ok → ∀ W : Finset ℕ, (∀ w ∈ W, w.Prime ∧ T.Splits w) → ∃ T' : Tower D, T.Le T' ∧ TameL l T'.F ∧ ∀ w ∈ W, Dies l w T'.F := by
  intro Ω _ _ _ l hl c D hD T ht hO W hW
  have : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  have hne : ∀ w ∈ W, w ≠ l := by
    rintro w hw rfl
    have hT : w ∈ D.T := Finset.mem_insert_self _ _
    have h1 := (hW w hw).2 _ (hD.pl_over w hl.out) (hD.sg_frob w hT).1
    have h2 : D.rbar (D.sg w) = 1 := h1.1.2
    have h3 : D.om (D.sg w) = 1 := h1.2
    have h4 : Raw.bar D.al (D.sg w) = 1 := by
      have := congrFun (congrFun h2 2) 2
      simpa [Raw.rbar, Raw.r0, mapRep, diagRep, Raw.ps] using this
    have h5 := hD.om_bar (D.sg w)
    apply hD.condD w hT 0
    simp only [Raw.bar, Raw.al, MonoidHom.mul_apply, MonoidHom.inv_apply, h3, inv_one, mul_one, Units.val_mul, map_mul,
      Units.val_one, map_one] at h4 h5
    rw [← h5, one_mul] at h4
    simpa using h4
  let U : ℕ → Subgroup (G ℚ Ω) := fun w => ⨅ θ : {θ : G ℚ Ω →* Multiplicative (ZMod l) // IsOpen (θ.ker : Set (G ℚ Ω)) ∧
    ∀ A, Raw.Away {w} A → Ine (F := ℚ) A ≤ θ.ker}, θ.1.ker
  let V : Subgroup (G ℚ Ω) := ⨅ w : W, U w
  have hV : ∀ g, g ∈ V ↔ ∀ w ∈ W, ∀ θ : G ℚ Ω →* Multiplicative (ZMod l), IsOpen (θ.ker : Set (G ℚ Ω)) →
      (∀ A, Raw.Away {w} A → Ine (F := ℚ) A ≤ θ.ker) → g ∈ θ.ker := fun g => by
    simp only [V, U, Subgroup.mem_iInf, Subtype.forall, and_imp]
  have hVo : IsOpen (V : Set (G ℚ Ω)) := by
    rw [Subgroup.coe_iInf]
    exact isOpen_iInter_of_finite fun w => dx_open (hW w w.2).1.ne_zero _ fun g hg =>
      Subgroup.mem_iInf.2 fun θ => dx_ker hl.out (hW w w.2).1 (hne w w.2) θ.1 θ.2.1 θ.2.2 g hg
  have hVl : ∀ g, g ^ l ∈ V := fun g => (hV _).2 fun w _ θ _ _ => by
    have := pow_card_eq_one (x := θ g)
    rwa [Fintype.card_multiplicative, ZMod.card, ← map_pow] at this
  have hFc : commutator (G ℚ Ω) ≤ T.F.fixingSubgroup := by
    have hab := T.abF
    have hn : Normal ℚ T.F := hab.toIsGalois.to_normal
    rw [← @IntermediateField.restrictNormalHom_ker ℚ Ω _ _ _ T.F hn, commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hab.is_comm.comm _ _
  obtain ⟨L, hL, _, _, _⟩ := dx_field T.F (T.F.fixingSubgroup ⊓ V)
    ((IntermediateField.fixingSubgroup_isOpen _).inter hVo)
    (le_inf hFc fun g hg => (hV g).2 fun w _ θ _ _ => Abelianization.commutator_subset_ker θ hg) l
    (hl.out.odd_of_ne_two hD.l_odd) fun g hg => ⟨pow_mem hg _, hVl g⟩
  have hg0 : resQ T.F T.g0 ^ l ∈ L.fixingSubgroup := by
    rw [hL]
    exact ⟨pow_mem ((T.F.mem_fixingSubgroup_iff _).2 fun x hx => T.g0.commutes ⟨x, hx⟩) _, hVl _⟩
  let g1 : G L Ω := AlgEquiv.ofRingEquiv (f := (resQ T.F T.g0 ^ l).toRingEquiv)
    fun x => (L.mem_fixingSubgroup_iff _).1 hg0 x.1 x.2
  obtain ⟨T', h1, h2, h3, h4⟩ := mkTower D hD T.pr T.K L T.degK (hO.split l hD.l_mem) g1
  refine ⟨T', ⟨h1, h2, ?_, ⟨1, fun g hg => ?_⟩, ⟨1, ?_⟩⟩, fun A hA g hg => ?_, fun w hw θ ho hu g hg => ?_⟩
  · rw [h3, ← InfiniteGalois.fixedField_fixingSubgroup L]
    exact (IntermediateField.le_iff_le _ _).2 (hL ▸ inf_le_left)
  · rw [h3, hL, pow_one]
    exact ⟨pow_mem hg _, hVl g⟩
  · rw [h4, pow_one]
    rfl
  · obtain ⟨m, hm, hgm⟩ := ht A hA g hg
    refine ⟨m, hm, ?_⟩
    rw [h3, hL]
    refine ⟨hgm, pow_mem ((hV g).2 fun w hw θ _ hu => hu A (fun p hp hpA => ?_) hg) _⟩
    rw [Finset.mem_singleton.1 hp] at hpA
    obtain ⟨a, b, hab⟩ : IsCoprime (w : ℤ) (l : ℤ) :=
      Nat.Coprime.cast ((Nat.coprime_primes (hW w hw).1 hl.out).2 (hne w hw))
    have e : (a : Ω) * w + b * l = 1 := by exact_mod_cast hab
    have hi : ∀ z : ℤ, A.valuation (z : Ω) ≤ 1 := fun z => (A.valuation_le_one_iff _).2 (intCast_mem A z)
    have := A.valuation.map_add_lt (x := (a : Ω) * w) (y := (b : Ω) * l) (g := 1)
      (by rw [map_mul]; exact mul_lt_one_of_nonneg_of_lt_one_right (hi a) zero_le' hpA)
      (by rw [map_mul]; exact mul_lt_one_of_nonneg_of_lt_one_right (hi b) zero_le' hA)
    rw [e, map_one] at this
    exact lt_irrefl _ this
  · rw [h3, hL] at hg
    exact (hV g).1 hg.2 w hw θ ho hu
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem UpperTheory.V.Ws.ch_num {x y : WithBot ℕ∞} {a b c N : ℕ} (h1 : x ≤ y + (a : ℕ)) (h2 : y + (b : ℕ) ≤ (c : ℕ))
    (h : c + a < N + b) : x < N := by
  refine h1.trans_lt ?_
  induction y using WithBot.recBotCoe with
  | bot => simp
  | coe y =>
    induction y using ENat.recTopCoe with
    | top => exact absurd h2 (by norm_cast)
    | coe y =>
      have h3 : y + b ≤ c := by exact_mod_cast h2
      exact_mod_cast (by omega : y + a < N)

set_option linter.overlappingInstances false in
private theorem UpperTheory.V.Ws.ch_core {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ] {Φ : Fr O Γ} {l : ℕ} [Fact l.Prime] {Λ : Type} [CommRing Λ] [IsDomain Λ]
    [IsDiscreteValuationRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] [Finite (ResidueField Λ)] {a : O →+* Λ} (hS : Φ.Std l a)
    (X : Space Φ a) (J : Ideal X.B) (U : Φ.ι → Set Γ) (hU : ∀ v, ∀ s ∈ U v, s ∈ Φ.Gv v) {d C dv N : ℕ}
    (hB : Φ.Bounds ((residue Λ).comp a) d C) (hN1 : d + 20 * C + 1 < N)
    (hN2 : 2 * d + 1 + (2 + 4 * Nat.card Φ.ι) < N + dv)
    (hnn : ∀ v i j, i ≠ j → ∀ q : Ideal X.B, q.IsPrime → J ≤ q → (maximalIdeal Λ).map (algebraMap Λ X.B) ≤ q →
      (∀ s ∈ U v, X.ψ v i s - X.ψ v j s ∈ q) → ringKrullDim (X.B ⧸ q) + dv ≤ (2 * d + 1 : ℕ))
    (hp1 : ∀ (k : Type) [Field k] [Finite k] [Algebra Λ k] (y : X.A →ₐ[Λ] PowerSeries k),
      (∀ b ∈ @maximalIdeal X.B X.cB.toCommSemiring X.coB.toIsLocalRing, PowerSeries.constantCoeff (y (algebraMap X.B X.A b)) = 0) →
      (∀ b ∈ J, y (algebraMap X.B X.A b) = 0) →
      (∀ v i j, i ≠ j → ∃ s ∈ U v, y (X.P.ψ v i s) ≠ y (X.P.ψ v j s)) →
      Irr (mapRep ((algebraMap (PowerSeries k) (FractionRing (PowerSeries k))).comp (y : X.A →+* PowerSeries k)) X.P.r) →
      X.LocZero J (y : X.A →+* PowerSeries k))
    {c : PD Φ.ι Γ (ResidueField Λ)} (hc : Φ.IsRes ((residue Λ).comp a) c) (hg : Φ.Good ((residue Λ).comp a) c)
    {R : Type} [CommRing R] [Algebra Λ R] [IsCO Λ R] (f : X.A →ₐ[Λ] R) (hdef : Φ.IsDef a c (X.P.map (f : X.A →+* R)))
    {P Q : Ideal R} (hPQ : Ch.Adj R (N + 1) P Q) (hP : J ≤ P.comap ((f : X.A →+* R).comp (algebraMap X.B X.A))) :
    J ≤ Q.comap ((f : X.A →+* R).comp (algebraMap X.B X.A)) := by
  classical
  haveI := hS.char
  haveI : IsLocalRing R := IsCO.toIsLocalRing (O := Λ)
  haveI : IsLocalHom (algebraMap Λ R) := IsCO.isLocalHom
  let φ : X.B →+* R := (f : X.A →+* R).comp (algebraMap X.B X.A)
  have hφ : ∀ t : Λ, φ (algebraMap Λ X.B t) = algebraMap Λ R t := fun t => by
    show f (algebraMap X.B X.A _) = _
    rw [← IsScalarTower.algebraMap_apply, AlgHom.commutes]
  obtain ⟨ϖ, hϖ⟩ := (IsPrincipalIdealRing.principal (maximalIdeal Λ)).1
  have hm : ∀ q : Ideal R, algebraMap Λ R ϖ ∈ q → ∀ t ∈ maximalIdeal Λ, algebraMap Λ R t ∈ q := fun q hq t ht => by
    rw [hϖ] at ht
    obtain ⟨u, rfl⟩ := Ideal.mem_span_singleton'.1 ht
    rw [map_mul]
    exact q.mul_mem_left _ hq
  have hϖm : algebraMap Λ R ϖ ∈ maximalIdeal R :=
    map_nonunit _ _ (show ϖ ∈ maximalIdeal Λ by rw [hϖ]; exact Ideal.mem_span_singleton_self ϖ)
  let A : {S // S ∈ redTypes} → Ideal R := fun S => redIdeal S.1 (X.P.map (f : X.A →+* R)).r
  let B : {t : Φ.ι × Fin 4 × Fin 4 // t.2.1 ≠ t.2.2} → Ideal R := fun t =>
    J.map φ ⊔ Ideal.span {algebraMap Λ R ϖ} ⊔ Ideal.span ((fun s => φ (X.ψ t.1.1 t.1.2.1 s - X.ψ t.1.1 t.1.2.2 s)) '' U t.1.1)
  haveI : Finite {S // S ∈ redTypes} := (List.finite_toSet redTypes).to_subtype
  obtain ⟨p, hp, hIp, hdim, hϖp, hA, hBp⟩ := Ch.nice _ hϖm N (by omega) A B
    (fun S => (red Φ l a hS d C hB c hc hg R _ hdef S.1 S.2).trans_lt (by exact_mod_cast hN1))
    (fun t q hq hle hr => ch_num
      (fib Φ l a hS X c hc R f hdef q (Ch.irr hS.ok hc hdef.1
        ((algebraMap (R ⧸ q) (FractionRing (R ⧸ q))).comp (Ideal.Quotient.mk q)) q
        (fun x hx => Ideal.Quotient.eq_zero_iff_mem.1 ((map_eq_zero_iff _ (IsFractionRing.injective _ _)).1 hx))
        fun S hS => hr ⟨S, hS⟩))
      (hnn t.1.1 _ _ t.2 (q.comap φ) (Ideal.comap_isPrime _ _)
        (Ideal.map_le_iff_le_comap.1 (le_sup_left.trans (le_sup_left.trans hle)))
        (Ideal.map_le_iff_le_comap.2 fun u hu => by
          show φ (algebraMap Λ X.B u) ∈ q
          rw [hφ]
          exact hm q (hle (Ideal.mem_sup_left (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)))) u hu)
        fun s hs => hle (Ideal.mem_sup_right (Ideal.subset_span ⟨s, hs, rfl⟩))) hN2) _ hPQ.2.2
  obtain ⟨K, _, _, _, j, hj, hj0⟩ := Ch.curve l Λ R p hp hdim (hm p hϖp)
  have hJp : ∀ b ∈ J, φ b ∈ p := fun b hb => hIp (Ideal.mem_sup_left (hP hb))
  haveI : Q.IsPrime := hPQ.2.1.1.1
  refine hp1 K (j.comp f) (fun b hb => hj0 _ ?_) (fun b hb => (hj _).2 (hJp b hb)) (fun v i i' hi => ?_)
    (Ch.irr hS.ok hc hdef.1 ((algebraMap (PowerSeries K) (FractionRing (PowerSeries K))).comp (j : R →+* PowerSeries K)) p
      (fun x hx => (hj x).1 ((map_eq_zero_iff _ (IsFractionRing.injective _ _)).1 hx)) fun S hS => hA ⟨S, hS⟩)
    _ (Ideal.comap_isPrime _ _) fun s hs => (hj _).2 (hIp (Ideal.mem_sup_right hs))
  · show (f.comp (IsScalarTower.toAlgHom Λ X.B X.A)) b ∈ maximalIdeal R
    rw [← res_eq_zero_iff Λ, res_map, res_eq_zero_iff]
    exact hb
  · by_contra hn
    push Not at hn
    refine hBp ⟨(v, i, i'), hi⟩ (sup_le (sup_le (Ideal.map_le_iff_le_comap.2 hJp)
      ((Ideal.span_singleton_le_iff_mem _).2 hϖp)) (Ideal.span_le.2 ?_))
    rintro _ ⟨s, hs, rfl⟩
    refine (hj _).1 ?_
    show (j.comp f) (algebraMap X.B X.A (X.ψ v i s - X.ψ v i' s)) = 0
    rw [map_sub, map_sub, X.ψ_map v i s (hU v s hs), X.ψ_map v i' s (hU v s hs), hn s hs, sub_self]

theorem UpperTheory.V.Ws.ch :
    CohomologyHyp → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), T.Fit → T.Deep → ∀ (ι : PadicAlgCl l ≃+* ℂ) (c' : Coef l) (h : c.O ≤ c'.O) (X : Space (T.fr ∅) (inc h)) (J : Ideal X.B), T.PM ι X J → ∀ C : ℕ, (T.fr ∅).Bounds ((residue c'.O).comp (inc h)) T.d C → 30 * (C + 1) * (C + 1) ≤ T.d →
      ∀ x : X.A →ₐ[c'.O] ResidueField c'.O, (T.fr ∅).IsRes ((residue c'.O).comp (inc h)) (X.P.map (x : X.A →+* _)) → (T.fr ∅).Good ((residue c'.O).comp (inc h)) (X.P.map (x : X.A →+* _)) →
      X.SomeIn J (RingHom.ker x) → X.AllIn J (RingHom.ker x) := by
  intro hC Ω _ _ _ l _ c D T hF hD ι c' h X J hPM C hB hd x hx hg ⟨q₀, hq₀, hq₀x, hq₀J⟩ q hq hqx
  haveI : Finite (ResidueField c'.O) := (UpperTheory.V.abelian₂.dvr_finite l c'.O).2.1
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : IsAlgClosure T.F Ω := ⟨inferInstance, inferInstance⟩
  haveI : IsGalois T.F Ω := {}
  haveI : CompactSpace (G T.F Ω) := inferInstanceAs (CompactSpace (Ω ≃ₐ[T.F] Ω))
  haveI : TotallyDisconnectedSpace (G T.F Ω) := inferInstanceAs (TotallyDisconnectedSpace (Ω ≃ₐ[T.F] Ω))
  have hS := (std hC D T hF ∅ c' h).1 (Finset.notMem_empty 0)
  obtain ⟨R, _, _, hco, f, hdef, hfl, hres⟩ := cmplEx (T.fr ∅) l (inc h) hS X x hx
  haveI : IsLocalRing R := hco.toIsLocalRing
  obtain ⟨a, b, π, e, hπ, hk, hab⟩ := x1 hC D T hF hD c' h _ hx R _ hdef
  obtain ⟨dv, hdv⟩ := chDv D T
  have hg' : Nat.card T.ι ≤ C := hB.card
  have hdv' : 30 * (C + 1) ≤ dv := by
    by_contra hn
    have h1 : dv * Nat.card T.ι ≤ 30 * (C + 1) * C := Nat.mul_le_mul (by omega) hg'
    nlinarith
  have hd' : 30 * (C + 1) ≤ T.d := le_trans (Nat.le_mul_of_pos_right _ (by omega)) hd
  obtain ⟨N, hN⟩ : ∃ N, N + 2 * Nat.card T.ι = 2 * T.d + 1 := ⟨2 * T.d + 1 - 2 * Nat.card T.ι, by omega⟩
  have hker : RingHom.ker x = (maximalIdeal R).comap (f : X.A →+* R) := by
    ext z
    rw [RingHom.mem_ker, ← hres]
    exact res_eq_zero_iff c'.O R (f z)
  obtain ⟨P, hP, rfl⟩ := Ch.flat_min _ hfl hq₀ (hker ▸ hq₀x)
  obtain ⟨Q, hQ, rfl⟩ := Ch.flat_min _ hfl hq (hker ▸ hqx)
  rw [Ideal.map_le_iff_le_comap, Ideal.comap_comap] at hq₀J ⊢
  have hch := Ch.chain c'.O (D := N + 1) π e hπ hk (by omega) hP hQ
  clear hq hqx hQ
  induction hch with
  | refl => exact hq₀J
  | tail _ hPQ ih =>
    exact ch_core hS X J T.U1 (fun v s hs => Ine_le_Dec _ hs.1) (dv := dv) hB (by omega)
      (by show _ + (2 + 4 * Nat.card T.ι) < _; omega)
      (fun v i j hij q h1 h2 h3 h4 => nn hC D T hF hD ι c' h X J hPM v i j hij q h1 h2 h3 h4 dv hdv) hPM.p1 hx hg f hdef hPQ ih
end
