module

public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle180
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle335
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle113
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle493
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemOfForallAnnihilatorAnnihilatorFieldModInteger
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle306
public import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle255
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle490
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle257
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle254
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle494
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BijectiveOfRetract

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.KerToDivisible

theorem torsion_finite_and_killed {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (ℓ : O) (hℓ0 : ℓ ≠ 0) (hℓ : ¬ IsUnit ℓ) (hfin : ∀ n : ℕ, Finite (O ⧸ Ideal.span {ℓ ^ n}))
    (M : Type) [AddCommGroup M] [Module O M] [Module.Finite O M] :
    Finite ↥(Submodule.torsion O M) ∧ ∃ k : ℕ, ∀ x ∈ Submodule.torsion O M, ℓ ^ k • x = 0 := by
  have hdvd : ∀ y : O, y ≠ 0 → ∃ n : ℕ, y ∣ ℓ ^ n := by
    intro y hy
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy hϖ
    obtain ⟨e, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hℓ0 hϖ
    have he : e ≠ 0 := by
      rintro rfl; apply hℓ; rw [hv, pow_zero, mul_one]; exact v.isUnit
    refine ⟨n, ?_⟩
    rw [hu, hv, mul_pow, Units.mul_left_dvd]
    apply Dvd.dvd.mul_left
    rw [← pow_mul]
    exact pow_dvd_pow ϖ (Nat.le_mul_of_pos_left n (Nat.pos_of_ne_zero he))
  haveI : Module.Finite O ↥(Submodule.torsion O M) :=
    Module.Finite.iff_fg.2 (IsNoetherian.noetherian _)
  obtain ⟨y, hy, hy0⟩ := Submodule.annihilator_top_inter_nonZeroDivisors
    (Submodule.torsion_isTorsion (R := O) (M := M))
  obtain ⟨k, t, ht⟩ := hdvd y (nonZeroDivisors.ne_zero hy0)
  have hk : ∀ x : ↥(Submodule.torsion O M), ℓ ^ k • x = 0 := by
    intro x
    rw [ht, mul_comm, mul_smul, Submodule.mem_annihilator.1 hy x Submodule.mem_top, smul_zero]
  refine ⟨?_, k, fun x hx => congrArg Subtype.val (hk ⟨x, hx⟩)⟩
  have hT : Module.IsTorsionBy O ↥(Submodule.torsion O M) (ℓ ^ k) := fun x => hk x
  letI := hT.module
  haveI := hfin k
  haveI : IsScalarTower O (O ⧸ Ideal.span {ℓ ^ k}) ↥(Submodule.torsion O M) :=
    Module.IsTorsionBySet.isScalarTower ((Module.isTorsionBySet_span_singleton_iff _).mpr hT)
  haveI : Module.Finite (O ⧸ Ideal.span {ℓ ^ k}) ↥(Submodule.torsion O M) :=
    Module.Finite.of_restrictScalars_finite O _ _
  exact Module.finite_of_finite (O ⧸ Ideal.span {ℓ ^ k})

section Gen
variable {G : Type} [Group G] [TopologicalSpace G] {LL : Type} [Field LL] {O : Type} [CommRing O]
  [Algebra O LL] {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
  [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V]
  {ρ : Representation LL G V}

theorem redT_mem_BQ (L : Lattice (O := O) ρ) (I : Submodule O ↥L.T) (hI : StableSub L I)
    (a : ↥(latticeCocycles L)) (ha : (Submodule.Quotient.mk a : LatticeCohomology L) = 0) : redT L I a ∈ BQ L I hI := by
  rw [Submodule.Quotient.mk_eq_zero] at ha
  obtain ⟨x, hx, hxa⟩ := ha
  refine ⟨I.mkQ ⟨x, hx⟩, ?_⟩
  funext g
  have h1 : evT L g a = actT L g ⟨x, hx⟩ - ⟨x, hx⟩ := Subtype.ext (congrFun hxa g).symm
  show actQ L I hI g (I.mkQ ⟨x, hx⟩) - I.mkQ ⟨x, hx⟩ = I.mkQ (evT L g a)
  rw [h1, map_sub]
  rfl


omit [TopologicalSpace G] [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V] in
theorem exists_smul_mem [IsDomain O] [IsFractionRing O LL] (L : Lattice (O := O) ρ) (w : V) :
    ∃ b : O, b ≠ 0 ∧ b • w ∈ L.T := by
  first
  | exact @_root_.GlobalTheory.NonzeroScalarLattice.exists_ne_zero_smul_mem
  | exact _root_.GlobalTheory.NonzeroScalarLattice.exists_ne_zero_smul_mem
  | (apply _root_.GlobalTheory.NonzeroScalarLattice.exists_ne_zero_smul_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.NonzeroScalarLattice.exists_ne_zero_smul_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NonzeroScalarLattice.exists_ne_zero_smul_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NonzeroScalarLattice.exists_ne_zero_smul_mem ..)

theorem exists_torsion_lift [IsDomain O] [IsFractionRing O LL] (L : Lattice (O := O) ρ)
    (hρ : ∀ m, Continuous fun g => ρ g m) (s : O) (σ : LL) (hs : algebraMap O LL s = σ) (hσ : σ ≠ 0)
    (c : G → ↥L.T ⧸ (Ideal.span {s} • ⊤ : Submodule O ↥L.T))
    (hc : (fun g => (Submodule.Quotient.mk (σ⁻¹ • Formalism.MainNotions.LocalSituation.liftQ L _ (c g)) : V ⧸ L.T)) ∈ BD L) :
    ∃ a : ↥(latticeCocycles L), (Submodule.Quotient.mk a : LatticeCohomology L) ∈ Submodule.torsion O (LatticeCohomology L) ∧
      redT L _ a = c := by
  obtain ⟨vb, hvb⟩ := hc
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ vb
  have h1 : ∀ g, (ρ g v - v) - σ⁻¹ • Formalism.MainNotions.LocalSituation.liftQ L _ (c g) ∈ L.T := by
    intro g
    rw [← Submodule.Quotient.eq, ← congrFun hvb g, Submodule.Quotient.mk_sub]
    rfl
  have hspec : ∀ g, ∃ y : ↥L.T, (y : V) = Formalism.MainNotions.LocalSituation.liftQ L _ (c g) ∧
      Submodule.Quotient.mk y = c g := fun g =>
    ⟨_, rfl, (Submodule.Quotient.mk_surjective _ (c g)).choose_spec⟩
  choose y hy hyc using hspec
  set w : V := σ • v with hw
  have h2 : ∀ g, ρ g w - w = (y g : V) + s • ((⟨_, h1 g⟩ : ↥L.T) : V) := by
    intro g
    rw [← algebraMap_smul LL s, hs, hy, hw, map_smul]
    simp only [smul_sub, smul_smul, mul_inv_cancel₀ hσ, one_smul]
    abel
  have h3 : ∀ g, ρ g w - w ∈ L.T := fun g => by
    rw [h2]; exact L.T.add_mem (y g).2 (L.T.smul_mem _ (h1 g))
  have hZ : (fun g => ρ g w - w) ∈ latticeCocycles L := by
    refine Submodule.mem_inf.2 ⟨⟨?_, fun g h => ?_⟩, Submodule.mem_pi.2 fun g _ => h3 g⟩
    · simp_rw [sub_eq_add_neg]
      exact (hρ w).add continuous_const
    · simp only [map_mul, Module.End.mul_apply, map_sub]
      abel
  refine ⟨⟨_, hZ⟩, ?_, ?_⟩
  · obtain ⟨b, hb, hbw⟩ := exists_smul_mem L w
    refine ⟨⟨b, mem_nonZeroDivisors_of_ne_zero hb⟩, ?_⟩
    show b • (Submodule.Quotient.mk ⟨_, hZ⟩ : LatticeCohomology L) = 0
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    refine ⟨b • w, hbw, ?_⟩
    funext g
    show ρ g (b • w) - b • w = b • (ρ g w - w)
    rw [smul_sub, LinearMap.map_smul_of_tower]
  · funext g
    rw [← hyc g]
    show (Submodule.Quotient.mk (evT L g ⟨_, hZ⟩) : ↥L.T ⧸ _) = _
    rw [Submodule.Quotient.eq, GlobalTheory.TateOrth.mem_span_smul_top]
    refine ⟨⟨_, h1 g⟩, Subtype.ext ?_⟩
    show (ρ g w - w) - y g = _
    rw [h2, add_sub_cancel_left]
    rfl

theorem exists_finset_red (L : Lattice (O := O) ρ) (I : Submodule O ↥L.T) (hI : StableSub L I)
    [Finite ↥(Submodule.torsion O (LatticeCohomology L))] :
    ∃ F : Finset (QuotientCohomology L I hI), F.card ≤ Nat.card ↥(Submodule.torsion O (LatticeCohomology L)) ∧
      ∀ (c : ↥(quotientCocycles L I hI)) (a : ↥(latticeCocycles L)),
        (Submodule.Quotient.mk a : LatticeCohomology L) ∈ Submodule.torsion O (LatticeCohomology L) → redT L I a = c →
        (Submodule.Quotient.mk c : QuotientCohomology L I hI) ∈ F := by
  classical
  letI := Fintype.ofFinite ↥(Submodule.torsion O (LatticeCohomology L))
  have key : ∀ t : ↥(Submodule.torsion O (LatticeCohomology L)), ∃ x : QuotientCohomology L I hI,
      ∀ (c : ↥(quotientCocycles L I hI)) (a : ↥(latticeCocycles L)), (Submodule.Quotient.mk a : LatticeCohomology L) = t →
        redT L I a = c → (Submodule.Quotient.mk c : QuotientCohomology L I hI) = x := by
    intro t
    by_cases h : ∃ (c : ↥(quotientCocycles L I hI)) (a : ↥(latticeCocycles L)), (Submodule.Quotient.mk a : LatticeCohomology L) = t ∧
        redT L I a = c
    · obtain ⟨c0, a0, h0, h0'⟩ := h
      refine ⟨Submodule.Quotient.mk c0, fun c a h1 h1' => ?_⟩
      rw [Submodule.Quotient.eq]
      have := redT_mem_BQ L I hI (a - a0) (by rw [Submodule.Quotient.mk_sub, h0, h1, sub_self])
      rw [map_sub, h0', h1'] at this
      exact this
    · exact ⟨0, fun c a h1 h1' => absurd ⟨c, a, h1, h1'⟩ h⟩
  choose ψ hψ using key
  refine ⟨Finset.univ.image ψ, ?_, fun c a ha hac => ?_⟩
  · refine Finset.card_image_le.trans ?_
    rw [Nat.card_eq_fintype_card, Finset.card_univ]
  · exact Finset.mem_image.2 ⟨⟨_, ha⟩, Finset.mem_univ _, (hψ ⟨_, ha⟩ c a rfl hac).symm⟩

theorem ker_bounded_gen [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O LL]
    (L : Lattice (O := O) ρ) (hρ : ∀ m, Continuous fun g => ρ g m) (hfg : Module.Finite O (LatticeCohomology L))
    (ℓ : O) (σ : LL) (hs : algebraMap O LL ℓ = σ) (hσ : σ ≠ 0) (hℓ : ¬ IsUnit ℓ)
    (hfin : ∀ n : ℕ, Finite (O ⧸ Ideal.span {ℓ ^ n})) :
    ∃ C0 k0 : ℕ, ∀ (r : ℕ) (hI : StableSub L (Ideal.span {ℓ ^ r} • ⊤ : Submodule O ↥L.T)),
      ∃ F : Finset (QuotientCohomology L _ hI), F.card ≤ C0 ∧ ∀ c : ↥(quotientCocycles L _ hI),
        (fun g => (Submodule.Quotient.mk ((σ ^ r)⁻¹ • Formalism.MainNotions.LocalSituation.liftQ L _
          ((c : G → ↥L.T ⧸ (Ideal.span {ℓ ^ r} • ⊤ : Submodule O ↥L.T)) g)) : V ⧸ L.T)) ∈ BD L →
        (Submodule.Quotient.mk c : QuotientCohomology L _ hI) ∈ F ∧
          (ℓ ^ k0) • (Submodule.Quotient.mk c : QuotientCohomology L _ hI) = 0 := by
  have hℓ0 : ℓ ≠ 0 := fun h => hσ (by rw [← hs, h, map_zero])
  obtain ⟨hF, k, hk⟩ := torsion_finite_and_killed ℓ hℓ0 hℓ hfin (LatticeCohomology L)
  refine ⟨Nat.card ↥(Submodule.torsion O (LatticeCohomology L)), k, fun r hI => ?_⟩
  obtain ⟨F, hFc, hFm⟩ := exists_finset_red L _ hI
  refine ⟨F, hFc, fun c hc => ?_⟩
  obtain ⟨a, ha, hac⟩ := exists_torsion_lift L hρ (ℓ ^ r) (σ ^ r)
    (by rw [map_pow, hs]) (pow_ne_zero _ hσ) _ hc
  refine ⟨hFm c a ha hac, ?_⟩
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  have := redT_mem_BQ L _ hI (ℓ ^ k • a)
    (by rw [Submodule.Quotient.mk_smul]; exact hk _ ha)
  rw [map_smul, hac] at this
  exact this

end Gen

theorem ker_bounded : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A' : GRep ↥(GK K) ℚ_[l] LL O) (LA' : Lattice (O := O) A'.ρ), ∃ C0 k0 : ℕ, ∀ (r : ℕ) (hI' : StableSub LA' (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA'.T)), ∃ F : Finset (QuotientCohomology LA' _ hI'), F.card ≤ C0 ∧ ∀ c' : ↥(quotientCocycles LA' _ hI'), (fun g => (Submodule.Quotient.mk ((((l : ℕ) : LL) ^ r)⁻¹ • Formalism.MainNotions.LocalSituation.liftQ LA' _ ((c' : ↥(GK K) → ↥LA'.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA'.T)) g)) : A'.V ⧸ LA'.T)) ∈ BD LA' → (Submodule.Quotient.mk c' : QuotientCohomology LA' _ hI') ∈ F ∧ (((l : ℕ) : O) ^ k0) • (Submodule.Quotient.mk c' : QuotientCohomology LA' _ hI') = 0 := by
  intro hT l _ P K LL _ _ _ O _ _ hO A' LA'
  have hgc := GlobalTheory.GoodCoeff.good_coeff_integers l LL O hO
  have hfg : Module.Finite O (LatticeCohomology LA') := GlobalTheory.TateFiniteH1.tate_finH1 hT l P K LL O hO A' LA'
  letI hD : IsDomain O := hO.1.choose
  haveI : IsDiscreteValuationRing O := hO.1.choose_spec.1
  haveI : IsFractionRing O LL := hO.1.choose_spec.2
  have hlLL : ((l : ℕ) : LL) ≠ 0 := by
    intro h
    have h' : algebraMap ℚ_[l] LL (l : ℚ_[l]) = 0 := by rw [map_natCast]; exact h
    rw [map_eq_zero_iff _ (algebraMap ℚ_[l] LL).injective] at h'
    exact (Fact.out : l.Prime).ne_zero (by exact_mod_cast h')
  have hℓu : ¬ IsUnit ((l : ℕ) : O) :=
    GlobalTheory.DoubleAnnihilator.not_isUnit_of_adicComplete _ hgc.2.2.2
  exact ker_bounded_gen (G := ↥(GK K)) (LL := LL) (O := O) (V := A'.V) (ρ := A'.ρ) LA' A'.cont hfg
    ((l : ℕ) : O) ((l : ℕ) : LL) (map_natCast (algebraMap O LL) l) hlLL hℓu hgc.2.2.1

end GlobalTheory.KerToDivisible
end

section

open NumberField IsDedekindDomain

namespace GlobalTheory.WeakApprox

variable {L : Type} [Field L] [NumberField L]

theorem exists_int_approx (S : Finset (HeightOneSpectrum (𝓞 L))) (t : HeightOneSpectrum (𝓞 L) → 𝓞 L)
    (ht : ∀ v ∈ S, t v ≠ 0) : ∃ y : 𝓞 L, ∀ v ∈ S,
      v.valuation L ((y : L) - (t v : L)) ≤ WithZero.exp (-1 : ℤ) * v.valuation L (t v : L) := by
  classical
  obtain ⟨y, hy⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := S)
    (fun v : HeightOneSpectrum (𝓞 L) => v.asIdeal)
    (fun v => multiplicity v.asIdeal (Ideal.span {t v}) + 1)
    (fun v _ => v.prime) (fun v _ w _ hvw h => hvw (HeightOneSpectrum.ext h)) (fun v => t v)
  refine ⟨y, fun v hv => ?_⟩
  have h1 := (v.intValuation_le_pow_iff_mem _ _).2 (hy v hv)
  have h2 := v.intValuation_eq_exp_neg_multiplicity (ht v hv)
  have e1 : ((y : L) - (t v : L)) = algebraMap (𝓞 L) L (y - t v) := by simp
  have e2 : ((t v : L)) = algebraMap (𝓞 L) L (t v) := rfl
  rw [e1, e2, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
    h2, ← WithZero.exp_add]
  refine h1.trans (le_of_eq ?_)
  congr 1
  push_cast
  ring

private lemma valued_algebraMap_adicCompletion_eq_valuation (K : Type) [Field K] [NumberField K] (P : HeightOneSpectrum (𝓞 K)) (a : K) :
    Valued.v (algebraMap K (P.adicCompletion K) a) = P.valuation K a := by
  rw [HeightOneSpectrum.algebraMap_adicCompletion]
  simp

private lemma exp_neg_one_mul_lt_of_ne_zero {x : WithZero (Multiplicative ℤ)} (hx : x ≠ 0) : WithZero.exp (-1 : ℤ) * x < x := by
  have h : WithZero.exp (-1 : ℤ) < 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  simpa using mul_lt_mul_of_pos_right h (zero_lt_iff.2 hx)

theorem exists_units_approx :
    ∀ (L : Type) [Field L] [NumberField L] (R : Finset (HeightOneSpectrum (𝓞 L)))
      (z : ∀ P : HeightOneSpectrum (𝓞 L), P.adicCompletion L), (∀ P ∈ R, z P ≠ 0) →
      ∃ k : Lˣ, ∀ P ∈ R, Valued.v (z P - algebraMap L (P.adicCompletion L) (k : L)) ≤
        WithZero.exp (-1 : ℤ) * Valued.v (z P) := by
  intro L _ _ R z hz
  classical

  have happ : ∀ P, ∃ a : L, P ∈ R →
      Valued.v (z P - algebraMap L (P.adicCompletion L) a) < WithZero.exp (-1 : ℤ) * Valued.v (z P) := by
    intro P
    by_cases hP : P ∈ R
    · obtain ⟨π, hπ⟩ := P.valuation_exists_uniformizer L
      have hπ0 : π ≠ 0 := by
        intro h
        rw [h, map_zero] at hπ
        exact WithZero.exp_ne_zero hπ.symm
      have hc : algebraMap L (P.adicCompletion L) π * z P ≠ 0 :=
        mul_ne_zero ((map_ne_zero _).2 hπ0) (hz P hP)
      obtain ⟨a, ha⟩ := GlobalTheory.adicCompletion_exists_approx_lt L P (z P) _ hc
      refine ⟨a, fun _ => ?_⟩
      rwa [map_mul, valued_algebraMap_adicCompletion_eq_valuation, hπ] at ha
    · exact ⟨0, fun h => absurd h hP⟩
  choose a ha using happ

  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 L)) R a
  have hint : ∀ P, ∃ r : 𝓞 L, P ∈ R → algebraMap (𝓞 L) L r = (d : 𝓞 L) • a P := by
    intro P
    by_cases hP : P ∈ R
    · obtain ⟨r, hr⟩ := hd P hP
      exact ⟨r, fun _ => hr⟩
    · exact ⟨0, fun h => absurd h hP⟩
  choose t ht using hint
  set D : L := algebraMap (𝓞 L) L d with hDdef
  have hD : D ≠ 0 :=
    (map_ne_zero_iff (algebraMap (𝓞 L) L) (IsFractionRing.injective (𝓞 L) L)).2
      (nonZeroDivisors.coe_ne_zero d)
  have htP : ∀ P ∈ R, algebraMap (𝓞 L) L (t P) = D * a P := fun P hP => by
    rw [ht P hP, Algebra.smul_def]
  have ha0 : ∀ P ∈ R, a P ≠ 0 := by
    intro P hP h
    have h' := ha P hP
    rw [h, map_zero, sub_zero] at h'
    exact lt_irrefl _ (h'.trans (exp_neg_one_mul_lt_of_ne_zero ((Valuation.ne_zero_iff _).2 (hz P hP))))
  have ht0 : ∀ P ∈ R, t P ≠ 0 := by
    intro P hP h
    have h' := htP P hP
    rw [h, map_zero] at h'
    exact mul_ne_zero hD (ha0 P hP) h'.symm

  obtain ⟨y, hy⟩ := exists_int_approx (L := L) R t ht0
  have hy' : ∀ P ∈ R, P.valuation L (algebraMap (𝓞 L) L y - algebraMap (𝓞 L) L (t P)) ≤
      WithZero.exp (-1 : ℤ) * P.valuation L (algebraMap (𝓞 L) L (t P)) := hy
  rcases R.eq_empty_or_nonempty with hR | ⟨P0, hP0⟩
  · exact ⟨1, by simp [hR]⟩
  have hy0 : algebraMap (𝓞 L) L y ≠ 0 := by
    intro h
    have h' := hy' P0 hP0
    rw [h, zero_sub, Valuation.map_neg] at h'
    have hv : P0.valuation L (algebraMap (𝓞 L) L (t P0)) ≠ 0 :=
      (Valuation.ne_zero_iff _).2 ((map_ne_zero_iff _ (IsFractionRing.injective (𝓞 L) L)).2 (ht0 P0 hP0))
    exact lt_irrefl _ (h'.trans_lt (exp_neg_one_mul_lt_of_ne_zero hv))
  refine ⟨Units.mk0 (algebraMap (𝓞 L) L y / D) (div_ne_zero hy0 hD), fun P hP => ?_⟩
  simp only [Units.val_mk0]
  have hA := ha P hP
  have hza : Valued.v (algebraMap L (P.adicCompletion L) (a P)) = Valued.v (z P) := by
    apply Valuation.map_eq_of_sub_lt
    rw [Valuation.map_sub_swap]
    exact hA.trans (exp_neg_one_mul_lt_of_ne_zero ((Valuation.ne_zero_iff _).2 (hz P hP)))
  have hsplit : z P - algebraMap L (P.adicCompletion L) (algebraMap (𝓞 L) L y / D) =
      (z P - algebraMap L _ (a P)) + algebraMap L _ (a P - algebraMap (𝓞 L) L y / D) := by
    rw [map_sub]; ring
  rw [hsplit]
  refine Valuation.map_add_le _ hA.le ?_
  rw [valued_algebraMap_adicCompletion_eq_valuation, ← hza, valued_algebraMap_adicCompletion_eq_valuation]
  have e : a P - algebraMap (𝓞 L) L y / D =
      (algebraMap (𝓞 L) L (t P) - algebraMap (𝓞 L) L y) / D := by
    rw [htP P hP]; field_simp
  have hDv : P.valuation L D ≠ 0 := (Valuation.ne_zero_iff _).2 hD
  rw [e, map_div₀, Valuation.map_sub_swap, div_le_iff₀ (zero_lt_iff.2 hDv)]
  calc _ ≤ WithZero.exp (-1 : ℤ) * P.valuation L (algebraMap (𝓞 L) L (t P)) := hy' P hP
    _ = _ := by rw [htP P hP, map_mul]; ac_rfl

end GlobalTheory.WeakApprox
end

section

open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.FunctorialityH2

namespace GlobalTheory.QuotientH2Count

def zmodScalarRep (n : ℕ) {O Γ M : Type} [CommRing O] [Group Γ] [AddCommGroup M] [Module O M]
    [Module (ZMod n) M] (χ : Γ →* Oˣ) : Representation (ZMod n) Γ M where
  toFun g := (DistribSMul.toAddMonoidHom M ((χ g : Oˣ) : O)).toZModLinearMap n
  map_one' := LinearMap.ext fun x => by
    show ((χ 1 : Oˣ) : O) • x = x
    rw [map_one, Units.val_one, one_smul]
  map_mul' g h := LinearMap.ext fun x => by
    show ((χ (g * h) : Oˣ) : O) • x = ((χ g : Oˣ) : O) • (((χ h : Oˣ) : O) • x)
    rw [map_mul, Units.val_mul, mul_smul]

theorem h2_twist_card_of_zmod {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}
    {O : Type} [CommRing O] {G : Type} [Group G] [TopologicalSpace G]
    (hTD : Formalism.GaloisCohomology.LocalTateDualityK) (hK : FiniteDimensional ℚ_[p] K) (i : G ≃ₜ* GK p K)
    (ε : G →* Oˣ) (M : Type) [AddCommGroup M] [Module O M] [TopologicalSpace M]
    [DiscreteTopology M] [Finite M] [IsTopologicalAddGroup M] [ContinuousConstSMul O M]
    (r : ℕ) [Module (ZMod (p ^ r)) M] (hr : 0 < r)
    (hc : Continuous fun q : G × M => ((ε q.1 : Oˣ) : O) • q.2) :
    Finite (H2 (_root_.Formalism.RepresentationBoundsCohomology.LOC.twist ε M)) ∧ Nat.card (H2 (_root_.Formalism.RepresentationBoundsCohomology.LOC.twist ε M)) ≤ Nat.card M := by
  obtain ⟨rho, hrho⟩ : ∃ rho : Representation (ZMod (p ^ r)) (GK p K) M,
      ∀ (g : GK p K) (x : M), rho g x = ((ε (i.symm g) : Oˣ) : O) • x :=
    ⟨zmodScalarRep (p ^ r) (carry i ε), fun _ _ => rfl⟩
  have hcont : ReciprocityTheory.Gal.ContAction rho := by
    have e : (fun q : GK p K × M => rho q.1 q.2) =
        (fun q : G × M => ((ε q.1 : Oˣ) : O) • q.2) ∘ fun q => (i.symm q.1, q.2) := by
      funext q; exact hrho q.1 q.2
    unfold ReciprocityTheory.Gal.ContAction
    rw [e]
    exact hc.comp ((i.symm.continuous.comp continuous_fst).prodMk continuous_snd)
  obtain ⟨hF, hC⟩ := GlobalTheory.T.card_H2_le_card_local hTD p K hK r M rho hr hcont
  have htr := GlobalTheory.T.natCard_H2_comp_equiv i rho
  have hsc := GlobalTheory.T.card_H2_eq_same_action (rho.comp i.toMulEquiv.toMonoidHom) (_root_.Formalism.RepresentationBoundsCohomology.LOC.twist ε M) (fun g x => by
      show rho (i g) x = ((ε g : Oˣ) : O) • x
      rw [hrho, i.symm_apply_apply])
  have hcard : Nat.card (H2 (_root_.Formalism.RepresentationBoundsCohomology.LOC.twist ε M)) = Nat.card (H2 rho) := by
    rw [← hsc, htr]
  refine ⟨?_, hcard ▸ hC⟩
  apply Nat.finite_of_card_ne_zero
  rw [hcard]
  exact Nat.card_pos.ne'

theorem h2_quot_card : ∀ {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O] [IsTopologicalRing O] {G : Type} [Group G] [TopologicalSpace G], Formalism.GaloisCohomology.LocalTateDualityK → FiniteDimensional ℚ_[p] K → PadicCoeff p O → ∀ (i : G ≃ₜ* GK p K) {ε : G →* Oˣ}, IsCyc p K (carry i ε) → ∀ k : ℕ, Finite (H2 (_root_.Formalism.RepresentationBoundsCohomology.LOC.twist ε (O ⧸ IsLocalRing.maximalIdeal O ^ k))) ∧ Nat.card (H2 (_root_.Formalism.RepresentationBoundsCohomology.LOC.twist ε (O ⧸ IsLocalRing.maximalIdeal O ^ k))) ≤ Nat.card (O ⧸ IsLocalRing.maximalIdeal O ^ k) := by
  intro p _ K O _ _ _ _ _ G _ _ hTD hK hO i ε hε k
  obtain ⟨hdisc, hfin⟩ := GlobalTheory.T.quotient_maximalIdeal_pow_discrete_and_finite hO k
  haveI := hdisc
  haveI := hfin
  have hkill : ∀ x : O ⧸ IsLocalRing.maximalIdeal O ^ k, (p ^ (k + 1)) • x = 0 := by
    intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [← map_nsmul, Ideal.Quotient.eq_zero_iff_mem, nsmul_eq_mul]
    push_cast
    rw [pow_succ, mul_assoc]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hO.p_mem k)
  have hce := GlobalTheory.T.continuous_cyclotomic_character_localGalois hO i hε
  have hc : Continuous fun q : G × (O ⧸ IsLocalRing.maximalIdeal O ^ k) =>
      ((ε q.1 : Oˣ) : O) • q.2 := by
    have hq : Continuous (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O ^ k)) := continuous_quot_mk
    have e : (fun q : G × (O ⧸ IsLocalRing.maximalIdeal O ^ k) => ((ε q.1 : Oˣ) : O) • q.2) =
        fun q => Ideal.Quotient.mk _ ((ε q.1 : Oˣ) : O) * q.2 := by
      funext q; exact Algebra.smul_def _ _
    rw [e]
    exact ((hq.comp hce).comp continuous_fst).mul continuous_snd
  letI : Module (ZMod (p ^ (k + 1))) (O ⧸ IsLocalRing.maximalIdeal O ^ k) :=
    AddCommGroup.zmodModule hkill
  exact h2_twist_card_of_zmod hTD hK i ε _ (k + 1) (Nat.succ_pos k) hc

end GlobalTheory.QuotientH2Count
end

section

open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2

theorem _root_.GlobalTheory.T.exists_generator_H2_twist : ∀ {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O] [IsTopologicalRing O] {G : Type} [Group G] [TopologicalSpace G], Formalism.GaloisCohomology.LocalTateDualityK → FiniteDimensional ℚ_[p] K → PadicCoeff p O → ∀ (i : G ≃ₜ* GK p K) {ε : G →* Oˣ}, IsCyc p K (carry i ε) → ∃ z : H2 (_root_.Formalism.RepresentationBoundsCohomology.LOC.twist ε O), Function.Bijective (fun a : O => a • z) := by
  first | exact @GlobalTheory.FreeTwistH2.exists_free_H2_twist | exact GlobalTheory.FreeTwistH2.exists_free_H2_twist | (intros; apply GlobalTheory.FreeTwistH2.exists_free_H2_twist <;> assumption)
end
