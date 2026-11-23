module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle003
public import Formalism.HermitianLattices.Bundle003
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianLatticeDiscriminantOrderNeZeroUnimodula
import Formalism.HermitianLattices.HermitianLatticesProofs.DualBasic
public import Formalism.PeriodIntegrals.HermitianGenusExtension.SemilocalHermitianLattices.FiniteDimensionalOfOrtho
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle004
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle097
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramePairCoordinatesTransportUnitaryMass
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle046
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesStabilizerActsOnTerms
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SpanToZero
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle091
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle005
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Adelstab
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle047
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Afsplit
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlobApprox
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis

@[expose] public section

section

open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

namespace GlobalTheory.Mass.MaxExists

open NumberField Matrix in
open scoped ENNReal Classical in
private lemma isIntLat_of_isUnimodular {K V : Type} [Field K] [NumberField K] [StarRing K]
    [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    {h : V →ₗ⋆[K] V →ₗ[K] K} {M : Submodule (𝓞 K) V} (hL : Submodule.IsFullLattice K M)
    (hU : _root_.Formalism.HermitianLatticesTheory.IsUnimodular h M) : _root_.GlobalTheory.Mass.IsIntLat h M := by
  unfold _root_.GlobalTheory.Mass.IsIntLat
  refine ⟨hL, ?_⟩
  unfold _root_.Formalism.HermitianLatticesTheory.IsIntegralLat
  intro x hx y hy
  unfold _root_.Formalism.HermitianLatticesTheory.IsUnimodular at hU
  have hy' : y ∈ _root_.Formalism.HermitianLatticesTheory.dual h M := by rw [hU]; exact hy
  exact (_root_.Formalism.HermitianLatticesTheory.dualBasic_mem_dual h M y).1 hy' x hx

open NumberField Matrix in
open scoped ENNReal Classical in
theorem _root_.GlobalTheory.Mass.MaxExists.main : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), _root_.Formalism.HermitianLatticesTheory.IsCMUnram K → h.IsSymm → h.Nondegenerate → (∀ M : Submodule (𝓞 K) V, _root_.GlobalTheory.Mass.IsIntLat h M → ∃ M', _root_.GlobalTheory.Mass.IsMaxLat h M' ∧ M ≤ M') ∧ (∀ M : Submodule (𝓞 K) V, Submodule.IsFullLattice K M → _root_.Formalism.HermitianLatticesTheory.IsUnimodular h M → _root_.GlobalTheory.Mass.IsMaxLat h M ∧ _root_.GlobalTheory.Mass.badP h M = ∅ ∧ _root_.GlobalTheory.Mass.lamMax h M = 1) ∧ (∀ (M : Submodule (𝓞 K) V) (n : ℕ), _root_.Formalism.HermitianLatticesTheory.IsOrthoLattice h M n → Submodule.IsLattice K M ∧ _root_.Formalism.HermitianLatticesTheory.IsUnimodular h M ∧ Module.finrank K V = n) := by
  intro K V _ _ _ _ _ _ _ _ h hK hS hN
  have D := fun M hM => _root_.GlobalTheory.Mass.DiscOrder.main K V h hK hS hN M hM
  refine ⟨?_, ?_, ?_⟩
  · have key : ∀ n : ℕ, ∀ M : Submodule (𝓞 K) V, _root_.GlobalTheory.Mass.IsIntLat h M →
        _root_.GlobalTheory.Mass.discN h M = n →
        ∃ M', _root_.GlobalTheory.Mass.IsMaxLat h M' ∧ M ≤ M' := by
      intro n
      induction n using Nat.strong_induction_on with
      | _ n ih =>
        intro M hM hn
        by_cases hmax : ∀ N : Submodule (𝓞 K) V, _root_.GlobalTheory.Mass.IsIntLat h N → M ≤ N → N = M
        · exact ⟨M, by unfold _root_.GlobalTheory.Mass.IsMaxLat; exact ⟨hM, hmax⟩, le_rfl⟩
        · push_neg at hmax
          obtain ⟨N, hNi, hMN, hne⟩ := hmax
          obtain ⟨hidx0, hdisc⟩ := (D M hM).2.2.1 N hNi hMN
          have hidx1 : _root_.GlobalTheory.Mass.idxN N M ≠ 1 := by
            intro h1
            exact hne (le_antisymm (_root_.GlobalTheory.Mass.DiscOrder.idxN_eq_one.1 h1) hMN)
          have hNpos : 0 < _root_.GlobalTheory.Mass.discN h N :=
            Nat.pos_of_ne_zero (D N hNi).1
          have hlt : _root_.GlobalTheory.Mass.discN h N < n := by
            rw [← hn, hdisc]
            have h2 : 2 ≤ _root_.GlobalTheory.Mass.idxN N M := by omega
            have h4 : 1 < _root_.GlobalTheory.Mass.idxN N M ^ 2 :=
              Nat.one_lt_pow (by norm_num) (by omega)
            calc _root_.GlobalTheory.Mass.discN h N
                = _root_.GlobalTheory.Mass.discN h N * 1 := (mul_one _).symm
              _ < _root_.GlobalTheory.Mass.discN h N * _root_.GlobalTheory.Mass.idxN N M ^ 2 :=
                  Nat.mul_lt_mul_of_pos_left h4 hNpos
          obtain ⟨M', hM', hNM'⟩ := ih _ hlt N hNi rfl
          exact ⟨M', hM', hMN.trans hNM'⟩
    exact fun M hM => key _ M hM rfl
  · intro M hL hU
    have hI := isIntLat_of_isUnimodular hL hU
    have hD1 : _root_.GlobalTheory.Mass.discN h M = 1 := ((D M hI).2.1).2 hU
    have hbad : _root_.GlobalTheory.Mass.badP h M = ∅ := by
      unfold _root_.GlobalTheory.Mass.badP
      ext P
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and, not_not]
      intro hP
      refine (D M hI).2.2.2.2.1 P hP ?_
      rw [hD1, Nat.cast_one]
      exact fun h1 => hP.ne_top ((Ideal.eq_top_iff_one P).2 h1)
    refine ⟨?_, hbad, ?_⟩
    · unfold _root_.GlobalTheory.Mass.IsMaxLat
      refine ⟨hI, fun N hNi hMN => ?_⟩
      obtain ⟨_, hdisc⟩ := (D M hI).2.2.1 N hNi hMN
      rw [hD1] at hdisc
      have h1 : _root_.GlobalTheory.Mass.idxN N M ^ 2 = 1 :=
        Nat.eq_one_of_mul_eq_one_left hdisc.symm
      have h1' : _root_.GlobalTheory.Mass.idxN N M = 1 := by
        simpa using h1
      exact le_antisymm (_root_.GlobalTheory.Mass.DiscOrder.idxN_eq_one.1 h1') hMN
    · unfold _root_.GlobalTheory.Mass.lamMax
      rw [hbad]
      exact finprod_mem_empty
  · intro M n hO
    exact ⟨_root_.ReciprocityTheory.ChartRestriction.L3.isLattice_of_ortho hO, _root_.ReciprocityTheory.ChartRestriction.L3.isUnimodular_of_ortho hO, _root_.ReciprocityTheory.ChartRestriction.L3.finrank_of_ortho hO⟩

end GlobalTheory.Mass.MaxExists
end

section

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.CoordAmp

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E]
  [TopologicalSpace E] [MeasurableSpace E] {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]
  {H : HermSp M V} {r k : ℕ} {P : LocNG.FPair H r} {S : Frames M.L r k}

open scoped Pointwise ENNReal Classical in
private lemma tsum_transversal_eq_tsum_orbits_lemma {T X G R : Type*} [Group G] [MulAction G X]
    [AddCommMonoid R] [TopologicalSpace R] (St : Subgroup G)
    (rel : T → T → Prop) (A B : Set T) (hB : _root_.Formalism.MainNotions.S.LocNG.IsTransv rel A B) (ℓ : T → X) (term : X → Prop)
    (p : T → Prop) (Q : X → Prop)
    (hterm : ∀ t ∈ A, term (ℓ t)) (hsurj : ∀ Λ, term Λ → ∃ t ∈ A, ℓ t = Λ)
    (hrel : ∀ t t', rel t t' ↔ ∃ g ∈ St, ℓ t' = g • ℓ t)
    (hinv : ∀ Λ, term Λ → ∀ g ∈ St, term (g • Λ))
    (hpQ : ∀ t ∈ A, (p t ↔ Q (ℓ t))) (hQ : ∀ Λ, term Λ → ∀ g ∈ St, Q Λ → Q (g • Λ))
    (f : X → R) (hf : ∀ Λ, term Λ → ∀ g ∈ St, f (g • Λ) = f Λ)
    (val : T → R) (hval : ∀ t ∈ A, val t = f (ℓ t)) :
    ∑' t : {t // t ∈ B ∧ p t}, val t.1
      = ∑' o : MulAction.orbitRel.Quotient St X,
          if term (Quotient.out o) ∧ Q (Quotient.out o) then f (Quotient.out o) else 0 := by
  obtain ⟨hBA, hcover, huniq⟩ := hB
  have key : ∀ Λ : X, ∃ g ∈ St,
      Quotient.out (Quotient.mk (MulAction.orbitRel St X) Λ) = g • Λ := fun Λ => by
    obtain ⟨⟨g, hg⟩, hgx⟩ := Quotient.mk_out (s := MulAction.orbitRel St X) Λ
    exact ⟨g, hg, hgx.symm⟩
  let toFun : {t // t ∈ B ∧ p t} →
      ↥{o : MulAction.orbitRel.Quotient St X | term (Quotient.out o) ∧ Q (Quotient.out o)} :=
    fun t => ⟨Quotient.mk _ (ℓ t.1), by
      obtain ⟨g, hg, he⟩ := key (ℓ t.1)
      have h1 := hterm _ (hBA t.2.1)
      show term (Quotient.out (Quotient.mk (MulAction.orbitRel St X) (ℓ t.1)))
        ∧ Q (Quotient.out (Quotient.mk (MulAction.orbitRel St X) (ℓ t.1)))
      rw [he]
      exact ⟨hinv _ h1 g hg, hQ _ h1 g hg ((hpQ _ (hBA t.2.1)).1 t.2.2)⟩⟩
  have hbij : Function.Bijective toFun := by
    constructor
    · rintro ⟨t, ht⟩ ⟨t', ht'⟩ heq
      have h2 : Quotient.mk (MulAction.orbitRel St X) (ℓ t) = Quotient.mk _ (ℓ t') :=
        congrArg Subtype.val heq
      obtain ⟨⟨g, hg⟩, hgx⟩ := Quotient.exact h2
      have : rel t' t := (hrel t' t).2 ⟨g, hg, hgx.symm⟩
      exact Subtype.ext (huniq _ ht'.1 _ ht.1 this).symm
    · rintro ⟨o, ho⟩
      obtain ⟨t0, ht0A, ht0⟩ := hsurj _ ho.1
      obtain ⟨y, hyB, hy⟩ := hcover t0 ht0A
      obtain ⟨g, hg, hgy⟩ := (hrel y t0).1 hy
      have hyA := hBA hyB
      have hQy : Q (ℓ y) := by
        have := hQ (ℓ t0) (hterm _ ht0A) g⁻¹ (inv_mem hg) (by rw [ht0]; exact ho.2)
        rwa [hgy, inv_smul_smul] at this
      refine ⟨⟨y, hyB, (hpQ y hyA).2 hQy⟩, Subtype.ext ?_⟩
      show Quotient.mk _ (ℓ y) = o
      rw [← Quotient.out_eq o, ← ht0, hgy]
      exact Quotient.sound ⟨⟨g⁻¹, inv_mem hg⟩, inv_smul_smul g _⟩
  let e := Equiv.ofBijective toFun hbij
  have hR : (∑' o : MulAction.orbitRel.Quotient St X,
      if term (Quotient.out o) ∧ Q (Quotient.out o) then f (Quotient.out o) else 0)
      = ∑' o : ↥{o : MulAction.orbitRel.Quotient St X |
          term (Quotient.out o) ∧ Q (Quotient.out o)}, f (Quotient.out o.1) := by
    refine Eq.trans ?_ (tsum_subtype _ (fun o => f (Quotient.out o))).symm
    refine tsum_congr fun o => ?_
    simp only [Set.indicator_apply, Set.mem_setOf_eq]
  rw [hR, ← e.tsum_eq]
  refine tsum_congr fun t => ?_
  show val t.1 = f (Quotient.out (Quotient.mk _ (ℓ t.1)))
  obtain ⟨g, hg, he⟩ := key (ℓ t.1)
  rw [he, hf _ (hterm _ (hBA t.2.1)) g hg, hval _ (hBA t.2.1)]


open scoped Pointwise ENNReal Classical in
open ValuativeRel in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E]
  [TopologicalSpace E] [MeasurableSpace E] {M : _root_.Formalism.MainNotions.S.Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V]
  {H : _root_.Formalism.MainNotions.S.Loc.HermSp M V} {r k : ℕ} {P : _root_.Formalism.MainNotions.S.LocNG.FPair H r} {S : _root_.GlobalTheory.HL.Frames M.L r k} in
theorem _root_.GlobalTheory.HL.CoordAmp.sums_eq (hM : M.OK) (c : _root_.GlobalTheory.HL.Coord P S)
    (R : _root_.Formalism.MainNotions.S.LocNG.Reps P) (d : _root_.Formalism.MainNotions.S.LocNG.Datum P)
    (p : _root_.Formalism.MainNotions.S.Loc.Term V M r → Prop) (Q : Submodule M.L.O S.V → Prop)
    (hpQ : ∀ t, _root_.Formalism.MainNotions.S.LocNG.IsTermOver P d t → (p t ↔ Q (c.lat t.abelian₂)))
    (hQ : ∀ Λ, S.IsTerm (c.dat d) Λ →
      ∀ h ∈ S.St, Q Λ → Q (h • Λ)) :
    _root_.Formalism.MainNotions.S.LocNG.amp R d p = S.amp (c.dat d) Q ∧
      (∑' t : {t // t ∈ R.RT d ∧ p t}, ENNReal.ofReal (_root_.Formalism.MainNotions.S.LocNG.mu P t.1))
        = S.mass (c.dat d) Q := by
  haveI := hM.loc
  haveI := hM.char0
  obtain ⟨-, -, hbij, hlatg, -, hmu⟩ := _root_.GlobalTheory.HL.CoordMass.transport M hM H r k P S c
  obtain ⟨-, -, -, hSt, -⟩ := _root_.GlobalTheory.HL.CoordUnip.transport M hM H r k P S c
  obtain ⟨hcorr, hex, -⟩ := _root_.GlobalTheory.HL.CoordTermWt.terms_correspond M hM H r k P S c
  have hB := R.hRT d
  have hrel : ∀ t t', _root_.Formalism.MainNotions.S.LocNG.TRel P t t' ↔ ∃ g ∈ S.St,
      c.lat t'.abelian₂ = g • c.lat t.abelian₂ := by
    intro t t'
    unfold _root_.Formalism.MainNotions.S.LocNG.TRel
    constructor
    · rintro ⟨s, hs, he⟩
      exact ⟨c.grp s, (hSt s).1 hs, by rw [he, hlatg]⟩
    · rintro ⟨g, hg, he⟩
      refine ⟨c.grp.symm g, (hSt _).2 (by simpa using hg), hbij.1 ?_⟩
      rw [hlatg, MulEquiv.apply_symm_apply, he]
  have hterm_inv : ∀ Λ, S.IsTerm (c.dat d) Λ →
      ∀ g ∈ S.St, S.IsTerm (c.dat d) (g • Λ) :=
    fun Λ h g hg => (_root_.GlobalTheory.FrameAct.stabiliser_acts_on_terms M.L r k S _ Λ h g hg).1
  have hom_inv : ∀ Λ, S.IsTerm (c.dat d) Λ →
      ∀ g ∈ S.St,
        S.om (c.dat d) (g • Λ) = S.om (c.dat d) Λ :=
    fun Λ h g hg => (_root_.GlobalTheory.FrameAct.stabiliser_acts_on_terms M.L r k S _ Λ h g hg).2.1
  have hmu_inv : ∀ Λ, S.IsTerm (c.dat d) Λ →
      ∀ g ∈ S.St,
        S.mu (g • Λ) = S.mu Λ :=
    fun Λ h g hg => ((_root_.GlobalTheory.HL.volSt M.L r k S).1 Λ
      (_root_.GlobalTheory.HL.TermBasic.term_basic M.L r k S _ Λ h).1.1).2.2 g hg
  constructor
  · unfold _root_.Formalism.MainNotions.S.LocNG.amp _root_.GlobalTheory.HL.Frames.amp
    exact tsum_transversal_eq_tsum_orbits_lemma S.St (_root_.Formalism.MainNotions.S.LocNG.TRel P) _ _ hB
      (fun t => c.lat t.abelian₂) (S.IsTerm (c.dat d)) p Q
      (fun t ht => (hcorr d t ht).1) (fun Λ h => hex d Λ h) hrel hterm_inv hpQ hQ
      (fun Λ => (S.mu Λ : ℂ) * S.om (c.dat d) Λ)
      (fun Λ h g hg => by simp only [hmu_inv Λ h g hg, hom_inv Λ h g hg])
      (fun t => (_root_.Formalism.MainNotions.S.LocNG.mu P t : ℂ) * _root_.Formalism.MainNotions.S.LocNG.om P t)
      (fun t ht => by simp only [hmu t, (hcorr d t ht).2.1])
  · unfold _root_.GlobalTheory.HL.Frames.mass
    exact tsum_transversal_eq_tsum_orbits_lemma S.St (_root_.Formalism.MainNotions.S.LocNG.TRel P) _ _ hB
      (fun t => c.lat t.abelian₂) (S.IsTerm (c.dat d)) p Q
      (fun t ht => (hcorr d t ht).1) (fun Λ h => hex d Λ h) hrel hterm_inv hpQ hQ
      (fun Λ => ENNReal.ofReal (S.mu Λ))
      (fun Λ h g hg => by simp only [hmu_inv Λ h g hg])
      (fun t => ENNReal.ofReal (_root_.Formalism.MainNotions.S.LocNG.mu P t))
      (fun t _ => by simp only [hmu t])


open scoped Pointwise ENNReal Classical in
open ValuativeRel in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E]
  [TopologicalSpace E] [MeasurableSpace E] {M : _root_.Formalism.MainNotions.S.Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V]
  {H : _root_.Formalism.MainNotions.S.Loc.HermSp M V} {r k : ℕ} {P : _root_.Formalism.MainNotions.S.LocNG.FPair H r} {S : _root_.GlobalTheory.HL.Frames M.L r k} in
theorem _root_.GlobalTheory.HL.CoordAmp.amp_mass_eq : ∀ {F : Type} [Field F] [ValuativeRel F]
    [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : _root_.Formalism.MainNotions.S.Loc.Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : _root_.Formalism.MainNotions.S.Loc.HermSp M V) (r k : ℕ)
    (P : _root_.Formalism.MainNotions.S.LocNG.FPair H r), ∀ (S : _root_.GlobalTheory.HL.Frames M.L r k) (c : _root_.GlobalTheory.HL.Coord P S),
    ∀ (R : _root_.Formalism.MainNotions.S.LocNG.Reps P) (d : _root_.Formalism.MainNotions.S.LocNG.Datum P),
    _root_.Formalism.MainNotions.S.LocNG.amp R d (_root_.Formalism.MainNotions.S.LocNG.BBne (H := H)) = S.amp (c.dat d)
        (fun Λ => ¬ S.BBzero (c.dat d) Λ) ∧
      _root_.Formalism.MainNotions.S.LocNG.amp R d (fun t => ¬ _root_.Formalism.MainNotions.S.LocNG.BBne (H := H) t) = S.amp (c.dat d)
        (S.BBzero (c.dat d)) ∧
      _root_.Formalism.MainNotions.S.LocNG.amp R d (fun _ => True) = S.amp (c.dat d) (fun _ => True) ∧
      (∑' t : R.RT d, ENNReal.ofReal (_root_.Formalism.MainNotions.S.LocNG.mu P t.1))
        = S.mass (c.dat d) (fun _ => True) := by
  intro F _ _ _ E _ _ _ _ M hM V _ _ H r k P S c R d
  haveI := hM.loc
  haveI := hM.char0
  obtain ⟨hcorr, -, -⟩ := _root_.GlobalTheory.HL.CoordTermWt.terms_correspond M hM H r k P S c
  have hBB : ∀ Λ, S.IsTerm (c.dat d) Λ →
      ∀ h ∈ S.St,
        (S.BBzero (c.dat d) (h • Λ)
          ↔ S.BBzero (c.dat d) Λ) :=
    fun Λ hΛ h hh => (_root_.GlobalTheory.FrameAct.stabiliser_acts_on_terms M.L r k S _ Λ hΛ h hh).2.2.2.2.2.2.2.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (_root_.GlobalTheory.HL.CoordAmp.sums_eq hM c R d _ _
      (fun t ht => (hcorr d t ht).2.2)
      (fun Λ hΛ h hh hq => by rwa [hBB Λ hΛ h hh])).1
  · exact (_root_.GlobalTheory.HL.CoordAmp.sums_eq hM c R d _ _
      (fun t ht => by rw [(hcorr d t ht).2.2, not_not])
      (fun Λ hΛ h hh hq => (hBB Λ hΛ h hh).2 hq)).1
  · exact (_root_.GlobalTheory.HL.CoordAmp.sums_eq hM c R d (fun _ => True) (fun _ => True)
      (fun _ _ => Iff.rfl) (fun _ _ _ _ _ => trivial)).1
  · rw [← (_root_.GlobalTheory.HL.CoordAmp.sums_eq hM c R d (fun _ => True) (fun _ => True)
      (fun _ _ => Iff.rfl) (fun _ _ _ _ _ => trivial)).2]
    exact ((Equiv.subtypeEquivRight (fun t => by simp)).tsum_eq
      (fun t => ENNReal.ofReal (_root_.Formalism.MainNotions.S.LocNG.mu P t.1))).symm

end GlobalTheory.HL.CoordAmp
end

section

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct
open Formalism.UG.P

namespace GlobalTheory.St.G.IntAd

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem levelafC_natCast (m : ℕ) : levelafC (F := F) E (m : 𝓞 F) = (m : E ⊗[F] Ad F) := by
  induction m with
  | zero => simp only [levelafC, Nat.cast_zero, map_zero, TensorProduct.tmul_zero]
  | succ k ih =>
    simp only [levelafC] at ih ⊢
    rw [Nat.cast_succ, Nat.cast_succ, map_add (f := _), map_one, TensorProduct.tmul_add, ih,
      Algebra.TensorProduct.one_def]

private theorem sum_afsplitI_one_apply_of_mem (S : Finset (HeightOneSpectrum (𝓞 F))) (w : HeightOneSpectrum (𝓞 F))
    (hw : w ∈ S) : (∑ v ∈ S, afsplitI v (1 : v.adicCompletion F)) w = 1 := by

  rw [show (∑ v ∈ S, afsplitI v (1 : v.adicCompletion F)) w =
    ∑ v ∈ S, (afsplitI v (1 : v.adicCompletion F)) w from map_sum (evalV F w) _ S]
  rw [Finset.sum_eq_single_of_mem w hw (fun v _ hv => afsplitI_ne v w (Ne.symm hv) 1),
    afsplitI_self]

private theorem sum_afsplitI_one_apply_of_not_mem (S : Finset (HeightOneSpectrum (𝓞 F))) (w : HeightOneSpectrum (𝓞 F))
    (hw : w ∉ S) : (∑ v ∈ S, afsplitI v (1 : v.adicCompletion F)) w = 0 := by

  rw [show (∑ v ∈ S, afsplitI v (1 : v.adicCompletion F)) w =
    ∑ v ∈ S, (afsplitI v (1 : v.adicCompletion F)) w from map_sum (evalV F w) _ S]
  exact Finset.sum_eq_zero (fun v hv => afsplitI_ne v w (fun h => hw (by rw [h]; exact hv)) 1)

theorem mem_of_local (a : E ⊗[F] Ad F)
    (h : ∀ v : HeightOneSpectrum (𝓞 F), prV (E := E) v a ∈ intV E v) : a ∈ OAd F E := by
  classical
  obtain ⟨d, hd0, hd⟩ := levelaf_denom (E := E) a
  have hfin := levelaf_finite_places (F := F) d hd0
  set S := hfin.toFinset with hS
  set dF : F := algebraMap (𝓞 F) F d with hdF
  have hdF0 : dF ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).mpr hd0
  set s : Ad F := ∑ v ∈ S, afsplitI v (1 : v.adicCompletion F) with hs
  set u : Ad F := (1 - s) * algebraMap F (Ad F) dF⁻¹ with hu
  have hu_int : u ∈ intAd F := by
    show ∀ w : HeightOneSpectrum (𝓞 F), u w ∈ w.adicCompletionIntegers F
    intro w
    have hcomp : u w = (1 - s w) * (dF⁻¹ • (1 : w.adicCompletion F)) := by
      rw [hu, afsplit_mul_apply, afsplit_sub_apply, afsplit_one_apply,
        Algebra.algebraMap_eq_smul_one, afsplit_smul_apply, afsplit_one_apply]
    by_cases hw : w ∈ S
    · rw [hcomp, hs, sum_afsplitI_one_apply_of_mem S w hw, sub_self, zero_mul]
      exact zero_mem _
    · rw [hcomp, hs, sum_afsplitI_one_apply_of_not_mem S w hw, sub_zero, one_mul, Algebra.smul_def, mul_one, map_inv₀,
        HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀]
      have h1 := levelaf_int_mem_v w d
      rw [HeightOneSpectrum.mem_adicCompletionIntegers] at h1
      have h2 : ¬ Valued.v (algebraMap (𝓞 F) (w.adicCompletion F) d) < 1 :=
        fun hlt => hw (hfin.mem_toFinset.mpr hlt)
      have h3 : Valued.v (algebraMap (𝓞 F) (w.adicCompletion F) d) = 1 :=
        le_antisymm h1 (not_lt.mp h2)
      rw [hdF, ← IsScalarTower.algebraMap_apply, h3, inv_one]
  have he : ∑ v ∈ S, afsplitEps E v = (1 : E) ⊗ₜ[F] s := by
    rw [hs, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    rw [afsplitEps, Algebra.TensorProduct.one_def, afsplitIE_tmul]
  have h1 : (1 : E ⊗[F] Ad F) - ∑ v ∈ S, afsplitEps E v = ((1 : E) ⊗ₜ[F] u) * levelafC E d := by
    rw [he, levelafC, Algebra.TensorProduct.tmul_mul_tmul, one_mul, hu, mul_assoc,
      IsScalarTower.algebraMap_apply (𝓞 F) F (Ad F) d, ← hdF, ← map_mul, inv_mul_cancel₀ hdF0,
      map_one, mul_one, TensorProduct.tmul_sub, ← Algebra.TensorProduct.one_def]
  have hsplit : a = (∑ v ∈ S, afsplitEps E v) * a + ((1 : E) ⊗ₜ[F] u) * (levelafC E d * a) := by
    rw [← mul_assoc, ← h1]
    ring
  rw [hsplit]
  refine add_mem ?_ (mul_mem ?_ hd)
  · rw [Finset.sum_mul]
    refine sum_mem (fun v _ => ?_)
    rw [← afsplit_decomp]
    exact afsplit_IE_int v _ (h v)
  · have hmem := levelaf_tmul_mem (E := E) (1 : 𝓞 E) hu_int
    rwa [map_one] at hmem

theorem expand_trace {ι : Type} [Fintype ι] [DecidableEq ι] (β : Module.Basis ι F E)
    (a : E ⊗[F] Ad F) :
    a = ∑ i, ((Algebra.traceForm F E).dualBasis (traceForm_nondegenerate F E) β i) ⊗ₜ[F]
      adelstabT F E (inclE (F := F) (Ad F) (β i) * a) := by
  induction a using TensorProduct.induction_on with
  | zero => simp only [mul_zero, map_zero, TensorProduct.tmul_zero, Finset.sum_const_zero]
  | tmul e y =>
    have hT : ∀ i, adelstabT F E (inclE (F := F) (Ad F) (β i) * (e ⊗ₜ[F] y)) =
        Algebra.trace F E (e * β i) • y := by
      intro i
      rw [inclE, Algebra.TensorProduct.includeLeftRingHom_apply, Algebra.TensorProduct.tmul_mul_tmul,
        one_mul, adelstabT_tmul, Algebra.smul_def, mul_comm (β i) e]
    simp_rw [hT, ← TensorProduct.smul_tmul, ← TensorProduct.sum_tmul]
    congr 1
    conv_lhs => rw [← ((Algebra.traceForm F E).dualBasis (traceForm_nondegenerate F E) β).sum_repr e]
    simp only [LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply]
  | add x y hx hy =>
    conv_lhs => rw [hx, hy]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [mul_add, map_add (f := _), TensorProduct.tmul_add]

private theorem adelstabT_inclE_of_forall_divisible (a : E ⊗[F] Ad F)
    (h : ∀ m : ℕ, 0 < m → ∃ t ∈ OAd F E, a = (m : E ⊗[F] Ad F) * t) (e : E) :
    adelstabT F E (inclE (F := F) (Ad F) e * a) = 0 := by
  obtain ⟨d, hd0, hd⟩ := levelaf_denom (E := E) (inclE (F := F) (Ad F) e)
  have hxS : inclE (F := F) (Ad F) (algebraMap (𝓞 F) E d * e) ∈ OAd F E := by
    rw [map_mul, adelstab_incl_C]
    exact hd
  have hzero : adelstabT F E (inclE (F := F) (Ad F) (algebraMap (𝓞 F) E d * e) * a) = 0 := by
    refine GlobalTheory.IntegralFinAdele.eq_zero_of_forall_mul F _ (fun M hM => ?_)
    obtain ⟨t, ht, hat⟩ := h M hM
    refine ⟨adelstabT F E (inclE (F := F) (Ad F) (algebraMap (𝓞 F) E d * e) * t),
      adelstabT_mem (mul_mem hxS ht), ?_⟩
    rw [hat, mul_left_comm, ← nsmul_eq_mul, map_nsmul, nsmul_eq_mul]
  have hdF0 : algebraMap (𝓞 F) F d ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).mpr hd0
  have hxe : inclE (F := F) (Ad F) (algebraMap (𝓞 F) E d * e) * a =
      algebraMap (𝓞 F) F d • (inclE (F := F) (Ad F) e * a) := by
    rw [IsScalarTower.algebraMap_apply (𝓞 F) F E d, ← Algebra.smul_def, inclE,
      Algebra.TensorProduct.includeLeftRingHom_apply, Algebra.TensorProduct.includeLeftRingHom_apply,
      ← TensorProduct.smul_tmul', smul_mul_assoc]
  rw [hxe, map_smul] at hzero
  calc adelstabT F E (inclE (F := F) (Ad F) e * a)
      = (algebraMap (𝓞 F) F d)⁻¹ • algebraMap (𝓞 F) F d • adelstabT F E (inclE (F := F) (Ad F) e * a) :=
        (inv_smul_smul₀ hdF0 _).symm
    _ = 0 := by rw [hzero, smul_zero]

theorem eq_zero_of_multiples (a : E ⊗[F] Ad F)
    (h : ∀ m : ℕ, 0 < m → ∃ t ∈ OAd F E, a = (m : E ⊗[F] Ad F) * t) : a = 0 := by
  classical
  rw [expand_trace (Module.Free.chooseBasis F E) a]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  rw [adelstabT_inclE_of_forall_divisible a h, TensorProduct.tmul_zero]

theorem exists_nat_denom (a : E ⊗[F] Ad F) :
    ∃ m : ℕ, 0 < m ∧ (m : E ⊗[F] Ad F) * a ∈ OAd F E := by
  obtain ⟨d, hd0, hd⟩ := levelaf_denom (E := E) a
  obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.mp (Ideal.absNorm_mem (Ideal.span {d}))
  refine ⟨Ideal.absNorm (Ideal.span {d}), Nat.pos_of_ne_zero ?_, ?_⟩
  · rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact hd0
  · rw [← levelafC_natCast, hq, levelafC_mul, mul_comm (levelafC E d), mul_assoc]
    exact mul_mem (levelafC_mem q) hd

theorem integral_adeles_properties : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], (∀ a : E ⊗[F] Ad F, a ∈ OAd F E ↔ ∀ v : HeightOneSpectrum (𝓞 F), prV (E := E) v a ∈ intV E v) ∧ (∀ a ∈ OAd F E, ∀ m : ℕ, 0 < m → ∃ x : 𝓞 E, ∃ t ∈ OAd F E, a = inclE (F := F) (Ad F) (x : E) + (m : E ⊗[F] Ad F) * t) ∧ (∀ a : E ⊗[F] Ad F, (∀ m : ℕ, 0 < m → ∃ t ∈ OAd F E, a = (m : E ⊗[F] Ad F) * t) → a = 0) ∧ (∀ a : E ⊗[F] Ad F, ∃ m : ℕ, 0 < m ∧ (m : E ⊗[F] Ad F) * a ∈ OAd F E) ∧ (∀ x : E, inclE (F := F) (Ad F) x ∈ OAd F E ↔ x ∈ intOE E) := by
  intro F E _ _ _ _ _
  refine ⟨fun a => ⟨fun ha v => afsplit_prV_int v a ha, mem_of_local a⟩, ?_,
    fun a => eq_zero_of_multiples a, exists_nat_denom, fun x => ⟨?_, ?_⟩⟩
  · intro a ha m hm
    have hm' : (m : 𝓞 F) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
    obtain ⟨b, t, ht, hab⟩ := csGlob_approx (E := E) csGlob_intAdApprox (m : 𝓞 F) hm' a ha
    refine ⟨b, t, ht, ?_⟩
    rw [hab, levelafC_natCast]
    try rfl
  · intro hx
    exact ⟨⟨x, csGlob_int x hx⟩, rfl⟩
  · rintro ⟨b, rfl⟩
    exact adelstab_incl_int b

end GlobalTheory.St.G.IntAd
end
