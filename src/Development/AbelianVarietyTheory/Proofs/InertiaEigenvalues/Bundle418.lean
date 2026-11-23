module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle010
public import ReciprocityTheory.GaloisValuations.Global
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle164
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankCyclotomicExtAndCyclotomicCharSurjective
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.T2SpaceLocLatV
import Mathlib.Algebra.Lie.OfAssociative
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle106
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle126
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle143
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle081
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoThreeFamily
import Mathlib.Algebra.AffineMonoid.Basic
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
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

namespace GlobalTheory.Cyc

variable {l : ℕ} [Fact l.Prime]

theorem finrank_maxUnramified_eq_cyclotomicLevel (K E : FinExt l) (s : ℕ) (hs : 1 ≤ s) (hE : E.1 = Ks K s)
    (hle : K.1 ≤ E.1) : Module.finrank ℚ_[l] ↥(K0 E) = Module.finrank ℚ_[l] ↥(K0 K) := by
  have h0 : K0 K ≤ K0 E := inf_le_inf_right _ hle
  have h1 : Ks E s = Ks K s := by
    apply le_antisymm
    · refine sup_le ?_ le_sup_right
      rw [← hE]
      exact inf_le_left
    · exact sup_le_sup_right h0 _
  have h2 := finrank_Ks E s hs
  rw [h1, finrank_Ks K s hs] at h2
  have hlp : l.Prime := Fact.out
  have hpos : 0 < (l - 1) * l ^ (s - 1) :=
    Nat.mul_pos (Nat.sub_pos_of_lt hlp.one_lt) (pow_pos hlp.pos _)
  exact (Nat.eq_of_mul_eq_mul_right hpos h2).symm

theorem mem_GKs_iff_mem_Gj (P : LocPrime l) (K : FinExt l) (LL : FinExt l) (n : ℕ)
    (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) n) (x : ↥(GK K)) :
    x ∈ W.GKs ↔ (x : GQ l) ∈ Gj K W.s := by
  have hχ : IsCyc P.χQ := P.χQ_cyc
  have hcb := (cyc_basic l P.χQ hχ).2.2 K
  have hK0 : (x : GQ l) ∈ (K0 K).fixingSubgroup :=
    IntermediateField.fixingSubgroup_antitone (inf_le_left : K0 K ≤ K.1) x.2
  rw [W.GKs_def, (hcb x hK0).1 W.s, P.PD_χ, ← DictKs.le_v_iff P LL,
    (algebraMap ℚ_[l] ↥LL.1).map_sub, (algebraMap ℚ_[l] ↥LL.1).map_one]

theorem actVB_inclusion (P : LocPrime l) (K E LL : FinExt l) (hle : K.1 ≤ E.1)
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (g : ↥(GK E)) :
    actVB (P.PD E) (T.ρ.comp (Subgroup.inclusion (GK_le hle))) g =
      actVB (P.PD K) T.ρ (Subgroup.inclusion (GK_le hle) g) := by
  unfold actVB
  congr 1
  ext b
  change (P.PD E).actB g b = (P.PD K).actB _ b
  rw [P.PD_actB, P.PD_actB]
  rfl

theorem iInf_ker_eq {R M ι κ : Type} [Ring R] [AddCommGroup M] [Module R M]
    (f : ι → M →ₗ[R] M) (g : κ → M →ₗ[R] M) (h1 : ∀ i, ∃ k, f i = g k) (h2 : ∀ k, ∃ i, f i = g k) :
    ⨅ i, LinearMap.ker (f i) = ⨅ k, LinearMap.ker (g k) := by
  apply le_antisymm
  · refine le_iInf fun k => ?_
    obtain ⟨i, hi⟩ := h2 k
    exact hi ▸ iInf_le _ i
  · refine le_iInf fun i => ?_
    obtain ⟨k, hk⟩ := h1 i
    exact hk ▸ iInf_le _ k

theorem Dcris_eq_iInf (P : LocPrime l) (K E LL : FinExt l) (hle : K.1 ≤ E.1)
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (H : Subgroup ↥(GK K))
    (hH : ∀ x : ↥(GK K), x ∈ H ↔ (x : GQ l) ∈ GK E) :
    Dcris (P.PD E) (T.ρ.comp (Subgroup.inclusion (GK_le hle))) =
      ⨅ g : ↥H, LinearMap.ker (actVB (P.PD K) T.ρ (g : ↥(GK K)) -
        (LinearMap.id : T.V ⊗[ℚ_[l]] P.R.B →ₗ[↥LL.1] T.V ⊗[ℚ_[l]] P.R.B)) := by
  unfold Dcris
  apply iInf_ker_eq
  · intro g
    refine ⟨⟨Subgroup.inclusion (GK_le hle) g, (hH _).2 g.2⟩, ?_⟩
    exact congrArg (fun f => f - LinearMap.id) (actVB_inclusion P K E LL hle T g)
  · intro g
    refine ⟨⟨(g : ↥(GK K)), (hH _).1 g.2⟩, ?_⟩
    exact congrArg (fun f => f - LinearMap.id) (actVB_inclusion P K E LL hle T _)



set_option backward.isDefEq.respectTransparency false in
theorem isCrys_Ks_of_finrank : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (s : ℕ) (LL : FinExt l) (n : ℕ) (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) n), W.s = s → ∀ (E : FinExt l), E.1 = Ks K s → ∀ (hle : K.1 ≤ E.1) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), Module.finrank ↥LL.1 ↥(⨅ g : ↥W.GKs, LinearMap.ker (actVB (P.PD K) T.ρ (g : ↥(GK K)) - (LinearMap.id : T.V ⊗[ℚ_[l]] P.R.B →ₗ[↥LL.1] T.V ⊗[ℚ_[l]] P.R.B))) = Module.finrank ℚ_[l] ↥(K0 K) * Module.finrank ↥LL.1 T.V → IsCrys (P.PD E) (T.ρ.comp (Subgroup.inclusion (GK_le hle))) := by
  intro l _ P K s LL n W hs E hE hle T h
  have hG : Gj K W.s = GK E := by
    rw [Gj, hs, ← hE]
    rfl
  have hD := Dcris_eq_iInf P K E LL hle T W.GKs (fun x => by
    rw [mem_GKs_iff_mem_Gj, hG])
  have h1 := finrank_maxUnramified_eq_cyclotomicLevel K E s (hs ▸ W.s_pos) hE hle
  have h2 := congrArg
    (fun D : Submodule ↥LL.1 (T.V ⊗[ℚ_[l]] P.R.B) => Module.finrank ↥LL.1 ↥D) hD
  rw [← h1] at h
  exact h2.trans h

end GlobalTheory.Cyc
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.PtCore

namespace GlobalTheory.Cyc

theorem isCyc_map_cycZ (l : ℕ) [Fact l.Prime] :
    IsCyc ((Units.map (PadicInt.Coe.ringHom (p := l)).toMonoidHom).comp
      (cycZ (F := ℚ_[l]) (Ω := Om l) l)) := by
  intro g m ζ hζ
  haveI : ∀ i : ℕ, NeZero ((l ^ i : ℕ) : Om l) := fun i =>
    ⟨by exact_mod_cast pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  refine ⟨_, ?_, cyclotomicCharacter.spec l (n := m)
    (MulSemiringAction.toRingAut (GQ l) (Om l) g) ζ hζ⟩
  set z : ℤ_[l] := ((cycZ (F := ℚ_[l]) (Ω := Om l) l g : ℤ_[l]ˣ) : ℤ_[l]) with hz
  change ‖(z : ℚ_[l]) - (((PadicInt.toZModPow m z).val : ℕ) : ℚ_[l])‖ ≤ _
  have h : z - (((PadicInt.toZModPow m z).val : ℕ) : ℤ_[l]) ∈
      Ideal.span {(l : ℤ_[l]) ^ m} := by
    haveI : NeZero (l ^ m) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
    rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val,
      sub_self]
  have := (PadicInt.norm_le_pow_iff_mem_span_pow _ m).2 h
  rwa [PadicInt.norm_def, PadicInt.coe_sub, PadicInt.coe_natCast] at this

theorem exists_inertia_cycZ_eq : ∀ (l : ℕ) [Fact l.Prime] (u : ℤ_[l]ˣ), ∃ σ : GQ l, (∀ x ∈ MaximalUnramifiedExtension l, σ x = x) ∧ cycZ (F := ℚ_[l]) (Ω := Om l) l σ = u := by
  intro l _ u
  have hχ := isCyc_map_cycZ l
  set χ := (Units.map (PadicInt.Coe.ringHom (p := l)).toMonoidHom).comp
      (cycZ (F := ℚ_[l]) (Ω := Om l) l) with hχdef
  have hu1 : ‖((u : ℤ_[l]) : ℚ_[l])‖ = 1 := PadicInt.norm_units u
  have hs : IsClosed {g : GQ l | (χ g : ℚ_[l]) = ((u : ℤ_[l]) : ℚ_[l])} :=
    isClosed_eq hχ.continuous continuous_const
  have key := hs.isCompact.inter_iInter_nonempty
    (fun x : MaximalUnramifiedExtension l => ((IntermediateField.adjoin ℚ_[l] {(x : Om l)}).fixingSubgroup : Set (GQ l)))
    (fun x => by
      haveI := IntermediateField.adjoin.finiteDimensional
        (Algebra.IsIntegral.isIntegral (R := ℚ_[l]) (x : Om l))
      exact IntermediateField.fixingSubgroup_isClosed _)
    (fun t => by
      let S : Set (Om l) := (fun x : MaximalUnramifiedExtension l => (x : Om l)) '' (t : Set (MaximalUnramifiedExtension l))
      haveI : Finite S := (t.finite_toSet.image _).to_subtype
      let K : FinExt l := ⟨IntermediateField.adjoin ℚ_[l] S,
        IntermediateField.finiteDimensional_adjoin
          (fun x _ => Algebra.IsIntegral.isIntegral x)⟩
      obtain ⟨g, hg, hgu⟩ := exists_chi_eq K χ hχ _ hu1
      refine ⟨g, hgu, Set.mem_iInter₂.2 fun x hx => ?_⟩
      refine (mem_fixingSubgroup_adjoin_iff _ g).2 ?_
      rintro y rfl
      exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg _
        ⟨IntermediateField.subset_adjoin _ _ ⟨x, hx, rfl⟩, x.2⟩)
  obtain ⟨g, hgu, hg⟩ := key
  refine ⟨g, fun x hx => ?_, Units.ext (Subtype.ext hgu)⟩
  exact (mem_fixingSubgroup_adjoin_iff _ g).1 (Set.mem_iInter.1 hg ⟨x, hx⟩) x rfl

end GlobalTheory.Cyc
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.BdRDVR

section General

variable {R : Type*} [CommRing R]

theorem irreducible_of_units [IsDomain R] {x : R} (hx0 : x ≠ 0) (hxu : ¬ IsUnit x)
    (hu : ∀ y : R, ¬ x ∣ y → IsUnit y) : Irreducible x := by
  refine ⟨hxu, fun a b hab => ?_⟩
  by_cases ha : x ∣ a
  · right
    obtain ⟨c, rfl⟩ := ha
    have h1 : x * 1 = x * (c * b) := by rw [mul_one, ← mul_assoc]; exact hab
    have h2 := mul_left_cancel₀ hx0 h1
    exact IsUnit.of_mul_eq_one_right c h2.symm
  · exact Or.inl (hu a ha)

theorem associated_pow_of_units {x : R} (hu : ∀ y : R, ¬ x ∣ y → IsUnit y)
    [IsHausdorff (Ideal.span {x}) R] {y : R} (hy : y ≠ 0) : ∃ n : ℕ, Associated (x ^ n) y := by
  classical
  have hex : ∃ n : ℕ, ¬ x ^ n ∣ y := by
    by_contra h
    push_neg at h
    apply hy
    refine IsHausdorff.haus (I := Ideal.span {x}) inferInstance y fun n => ?_
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact h n
  have hN := Nat.find_spec hex
  have hN0 : Nat.find hex ≠ 0 := by
    intro h0
    rw [h0, pow_zero] at hN
    exact hN (one_dvd _)
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hN0
  have hmin : x ^ m ∣ y := by
    have := Nat.find_min hex (m := m) (by omega)
    exact not_not.1 this
  obtain ⟨c, rfl⟩ := hmin
  have hc : IsUnit c := hu c fun hxc => hN (by
    rw [hm, pow_succ]
    exact mul_dvd_mul_left _ hxc)
  exact ⟨m, hc.unit, rfl⟩

end General

theorem core_dvr (l : ℕ) [Fact l.Prime] (C : Core l) : C.DVR := by
  have he := core_isEps l C
  obtain ⟨hdom, hinj, hfield, hden⟩ := BdRField.bdR_isField l
  obtain ⟨hfil, hreg, hcomp, -⟩ := filtration_eq_xi_pow l C.ε he
  obtain ⟨-, hker, hunit, -, -⟩ := thetaD_props l
  obtain ⟨-, ht1, ht2, -⟩ := core_t_unit_fil l C
  have hden' := hden C.ε he
  clear hden
  generalize aDp l (xi C.ε) = x at hfil hreg hcomp hden'
  have hθ : ∀ y : Per.BdRp l, Per.θD l y = 0 ↔ x ∣ y := fun y => by
    rw [hker, hfil, pow_one]
  have hu : ∀ y : Per.BdRp l, ¬ x ∣ y → IsUnit y := fun y hy => hunit y fun h => hy ((hθ y).1 h)
  have hx0 : x ≠ 0 := fun h => one_ne_zero (hreg 1 (by rw [h, zero_mul]))
  have hxu : ¬ IsUnit x := fun h => (h.map (Per.θD l)).ne_zero ((hθ x).2 dvd_rfl)
  have hirr : Irreducible x := irreducible_of_units hx0 hxu hu
  haveI : IsHausdorff (Ideal.span {x}) (Per.BdRp l) := hcomp.toIsHausdorff
  haveI hdvr : IsDiscreteValuationRing (Per.BdRp l) :=
    IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
      ⟨x, hirr, fun hy => associated_pow_of_units hu hy⟩
  have hmax : IsLocalRing.maximalIdeal (Per.BdRp l) = Ideal.span {x} := hirr.maximalIdeal_eq
  have hassoc : Associated x (C.j C.t) := by
    obtain ⟨c, hc⟩ := (hfil 1 _).1 ht1
    rw [pow_one] at hc
    have hcu : IsUnit c := hu c fun hxc => ht2 ((hfil 2 _).2 (by
      rw [hc, pow_two]
      exact mul_dvd_mul_left _ hxc))
    exact ⟨hcu.unit, hc.symm⟩
  refine ⟨hdom, hdvr, ?_, ?_, ?_, fun n => ?_, ?_⟩
  · rw [hmax]
    exact Ideal.span_singleton_eq_span_singleton.2 hassoc
  · rw [hmax]
    ext y
    rw [Ideal.mem_span_singleton, RingHom.mem_ker, hθ]
  · rw [hmax]
    exact hcomp
  · ext y
    rw [hfil, Ideal.mem_span_singleton]
    exact (hassoc.pow_pow (n := n)).dvd_iff_dvd_left
  · refine (isLocalization_iff _ _).2 ⟨fun y => ?_, fun z => ?_, fun {a b} h => ⟨1, by rw [hinj h]⟩⟩
    · have hy : algebraMap (Per.BdRp l) (Per.BdR l) y ≠ 0 := fun h =>
        nonZeroDivisors.ne_zero y.2 (hinj (h.trans (map_zero _).symm))
      obtain ⟨b, hb⟩ := hfield.mul_inv_cancel hy
      exact IsUnit.of_mul_eq_one b hb
    · obtain ⟨n, y, h⟩ := hden' z
      exact ⟨(y, ⟨x ^ n, mem_nonZeroDivisors_of_ne_zero (pow_ne_zero n hx0)⟩), by
        simpa only [map_pow] using h⟩

end GlobalTheory.MemLoc.BdRDVR
end

section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

noncomputable section

namespace GlobalTheory.NLinkAdmF

theorem placesOver_three_nonempty (D : D7) : (placesOver D.host.E 3).Nonempty := by
  have hl : Nat.Prime 3 := Nat.prime_three
  have hne : ((3 : ℕ) : 𝓞 D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hl.ne_zero
  have hnu : ¬ IsUnit ((3 : ℕ) : 𝓞 D.host.E) := by
    intro h
    have h1 := h.map (Algebra.norm ℤ)
    have h2 : Algebra.norm ℤ ((3 : ℕ) : 𝓞 D.host.E) = ((3 : ℕ) : ℤ) ^ Module.finrank ℤ (𝓞 D.host.E) := by
      rw [← Algebra.norm_algebraMap (R := ℤ) (S := 𝓞 D.host.E) ((3 : ℕ) : ℤ)]; simp
    rw [h2, isUnit_pow_iff Module.finrank_pos.ne', Int.isUnit_iff_natAbs_eq, Int.natAbs_natCast] at h1
    exact hl.one_lt.ne' h1
  obtain ⟨M, hM, hlM⟩ := exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.2 hnu)
  exact ⟨⟨M, hM.isPrime, fun h => hne (by simp [h] at hlM)⟩, hlM⟩

theorem sumOver_three_even (D : D7) (c : ℝ) :
    TwistedPlaces.sumOver D 3 (fun _ => c / ((placesOver D.host.E 3).ncard : ℝ)) = c := by
  have hfin : (placesOver D.host.E 3).Finite := FamilyRepresentationConstants.placesOver_finite D.host.E 3 (by norm_num)
  have hpos : 0 < (placesOver D.host.E 3).ncard :=
    (Set.ncard_pos hfin).2 (placesOver_three_nonempty D)
  unfold TwistedPlaces.sumOver
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, Finset.sum_const, nsmul_eq_mul,
    ← Set.ncard_eq_toFinset_card _ hfin]
  have : ((placesOver D.host.E 3).ncard : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
  field_simp

theorem localBoundTableAllPrimes_conditionTwoThree : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (X : KillingConditions.HubData D) (C : ℝ) (tf : TwistedPlaces.Tab L), Concl L P X C → TwistedPlaces.SmallPrimeLengthBound L tf C → TwistedPlaces.SmallPrimeLengthBound L (tab L X tf C) C := by
  intro D L P X C tf _ hF i hi hl
  have hFi := hF i hi hl
  by_cases h2 : D.nd.l i ∈ D.host.small
  · have hlen : (tab L X tf C).len i = fun _ => 0 := by
      funext lam
      simp only [tab, if_pos h2]
    have hBB : (tab L X tf C).BB i = TwistedPlaces.sumOver D (D.nd.l i) (tf.len i) + tf.BB i := by
      simp only [tab, if_pos h2]
    show TwistedPlaces.sumOver D _ ((tab L X tf C).len i) + (tab L X tf C).BB i ≤ _
    rw [hlen, hBB]
    have h0 : TwistedPlaces.sumOver D (D.nd.l i) (fun _ => (0 : ℝ)) = 0 := by simp [TwistedPlaces.sumOver]
    rw [h0, zero_add]
    exact hFi
  · have h3 : D.nd.l i = 3 := hl.resolve_left h2
    have hq : D.host.q ≠ 3 := D.host.q_ne_three
    have hd : D.host.d ≠ 3 := by
      have := D.host.hyp.2.2.2.1
      omega
    have hlen : (tab L X tf C).len i =
        fun _ => (TwistedPlaces.sumOver D 3 (tf.len i) + tf.BB i) / ((placesOver D.host.E 3).ncard : ℝ) := by
      funext lam
      simp only [tab, if_neg h2, if_pos h3]
    have hBB : (tab L X tf C).BB i = 0 := by
      have h1 : ¬ (D.nd.l i = D.host.q ∨ D.nd.l i = D.host.d) := by omega
      have hR : ¬ KillingConditions.RangeAD L X.exc (D.nd.l i) := fun hr => hr.1 (Or.inr h3)
      simp only [tab, if_neg h2, if_neg h1, if_neg hR]
    show TwistedPlaces.sumOver D (D.nd.l i) ((tab L X tf C).len i) + (tab L X tf C).BB i ≤ _
    have hFi' : TwistedPlaces.sumOver D (D.nd.l i) (tf.len i) + tf.BB i ≤ _ := hFi
    rw [h3] at hFi'
    rw [hlen, hBB, h3, sumOver_three_even, add_zero]
    exact hFi'

end GlobalTheory.NLinkAdmF

end
end

section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

open Classical

namespace GlobalTheory.NLink

theorem localBoundTableAllPrimes_rowsAndBand : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (X : KillingConditions.HubData D) (C : ℝ) (tf : TwistedPlaces.Tab L), Concl L P X C → TwistedPlaces.admA L (tab L X tf C) C ∧ TwistedPlaces.admB L (tab L X tf C) C ∧ TwistedPlaces.MediumInertPrimeLengthBound L (tab L X tf C) C ∧ TwistedPlaces.SmallInertPrimeSmallOrderLengthBound L (tab L X tf C) C ∧ TwistedPlaces.BandPlaceWeightApproximation L (tab L X tf C) C := by
  intro D L P X C tf h
  have hC := h.pos
  obtain ⟨nA, nB, nC, nD, nBand⟩ := h.num
  have h3 : ¬ TwistedPlaces.InertK D 3 := h.small.2.2.2.1
  have hR : ∀ i, D.nd.l i ≠ 3 → KillingConditions.RangeAD L X.exc (D.nd.l i) →
      (tab L X tf C).len i = (tabX L X).len i := by
    intro i h3 hr; funext lam
    have hs : D.nd.l i ∉ D.host.small := fun e => hr.1 (Or.inl e)
    show (if D.nd.l i ∈ D.host.small then (0 : ℝ) else if D.nd.l i = 3 then _
      else if KillingConditions.RangeAD L X.exc (D.nd.l i) then _ else 0) = _
    rw [if_neg hs, if_neg h3, if_pos hr]; rfl
  have hN : ∀ i, D.nd.l i ≠ 3 → ¬ KillingConditions.RangeAD L X.exc (D.nd.l i) →
      (tab L X tf C).len i = fun _ => 0 := by
    intro i h3 hr; funext lam
    show (if D.nd.l i ∈ D.host.small then (0 : ℝ) else if D.nd.l i = 3 then _
      else if KillingConditions.RangeAD L X.exc (D.nd.l i) then _ else 0) = _
    rw [if_neg h3, if_neg hr, ite_self]
  have hx : 0 < L.sc.x := lt_trans one_pos L.sc.one_lt_alt
  have hb : 1 ≤ L.sc.b := Real.one_le_exp (Real.rpow_nonneg hx.le _)
  have hSc := L.Sc_pos
  have hEta := L.etaSz_pos
  have ht : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
  have hLg : 0 ≤ TwistedPlaces.large₂ L := Real.rpow_nonneg hx.le _
  have hB1 : 1 ≤ TwistedPlaces.hB L := by unfold TwistedPlaces.hB; linarith
  have hwB : 0 ≤ TwistedPlaces.wB L := by
    have hb' : 0 < L.sc.b' := by
      unfold Scale.b' Scale.a Scale.X'
      positivity
    have h0 : 0 ≤ L.sc.w'' D.R.n := by unfold Scale.w''; positivity
    unfold TwistedPlaces.wB
    exact le_trans (by linarith) (le_max_left _ _)
  have hetaP : 0 ≤ TwistedPlaces.eta₃ L := by unfold TwistedPlaces.eta₃; linarith
  have hwP : 0 ≤ TwistedPlaces.wP L := by unfold TwistedPlaces.wP; linarith
  have hGP : 0 ≤ TwistedPlaces.GP L := by unfold TwistedPlaces.GP; linarith
  have heP : ∀ l : ℕ, l.Prime → 0 ≤ TwistedPlaces.eP L C l := by
    intro l hl
    unfold TwistedPlaces.eP
    have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.one_lt
    have h1 : 0 ≤ Real.logb l (TwistedPlaces.hB L) := Real.logb_nonneg hl1 hB1
    have h2 : 0 ≤ TwistedPlaces.hB L / l := div_nonneg (by linarith) (by linarith)
    exact mul_nonneg hC (by linarith)
  have hflat : ∀ (tb : TwistedPlaces.Tab L) i lam (l : ℕ), 0 ≤ TwistedPlaces.flatCD L tb i lam l := by
    intro tb i lam l
    unfold TwistedPlaces.flatCD
    have h1 : 0 ≤ (TwistedPlaces.wP L + TwistedPlaces.eta₃ L) / l := div_nonneg (by linarith) (Nat.cast_nonneg _)
    have h2 : 0 ≤ TwistedPlaces.eta₃ L * (if tb.band i lam then 1 else 0) :=
      mul_nonneg hetaP (by split_ifs <;> norm_num)
    linarith
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i hi hP
    have h5 := hP.1
    have h3' : D.nd.l i ≠ 3 := by omega
    by_cases hr : KillingConditions.RangeAD L X.exc (D.nd.l i)
    · rw [hR i h3' hr]; exact nA i hi hP
    · rw [hN i h3' hr]
      have hl := (D.nd.lPrime i).out
      have h0 : TwistedPlaces.sumOver D (D.nd.l i) (fun _ => (0 : ℝ)) = 0 := by
        unfold TwistedPlaces.sumOver; simp
      rw [h0, mul_zero]
      unfold TwistedPlaces.sumOver
      apply finsum_nonneg; intro lam; apply finsum_nonneg; intro _
      exact mul_nonneg (by positivity) (heP _ hl)
  · intro i hi hP
    have hI := hP.1
    have h3' : D.nd.l i ≠ 3 := fun e => h3 (by rw [e] at hI; exact hI)
    by_cases hr : KillingConditions.RangeAD L X.exc (D.nd.l i)
    · rw [hR i h3' hr]; exact nB i hi hP
    · rw [hN i h3' hr]
      intro lam _
      have hl1 : (1 : ℝ) ≤ D.nd.l i := by exact_mod_cast (D.nd.lPrime i).out.one_lt.le
      have h1 : 0 ≤ TwistedPlaces.hB L / ((D.nd.l i : ℝ) - 1) ^ (TwistedPlaces.jA L (D.nd.l i) + 1) :=
        div_nonneg (by linarith) (pow_nonneg (by linarith) _)
      have h2 : 0 ≤ (TwistedPlaces.GP L + 1) * ((TwistedPlaces.jA L (D.nd.l i) : ℝ) + 1) :=
        mul_nonneg (by linarith) (by positivity)
      exact mul_nonneg (mul_nonneg (mul_nonneg hC (by positivity)) (Nat.cast_nonneg _)) (by linarith)
  · intro i hi hP
    have hI := hP.1
    have h3' : D.nd.l i ≠ 3 := fun e => h3 (by rw [e] at hI; exact hI)
    by_cases hr : KillingConditions.RangeAD L X.exc (D.nd.l i)
    · rw [hR i h3' hr]; exact nC i hi hP
    · rw [hN i h3' hr]
      intro lam _
      have hl := (D.nd.lPrime i).out
      have h1 : 0 ≤ TwistedPlaces.hB L / (D.nd.l i : ℝ) ^ 2 := div_nonneg (by linarith) (by positivity)
      have h2 := hflat (tab L X tf C) i lam (D.nd.l i)
      have h4 := heP _ hl
      exact add_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC (by positivity)) (Nat.cast_nonneg _)) (by linarith))
        (mul_nonneg (mul_nonneg (mul_nonneg hC (by positivity)) (Nat.cast_nonneg _)) h4)
  · intro i hi hP
    have hI := hP.1
    have h3' : D.nd.l i ≠ 3 := fun e => h3 (by rw [e] at hI; exact hI)
    by_cases hr : KillingConditions.RangeAD L X.exc (D.nd.l i)
    · rw [hR i h3' hr]; exact nD i hi hP
    · rw [hN i h3' hr]
      intro lam _
      have hl := (D.nd.lPrime i).out
      have h1 : 0 ≤ TwistedPlaces.hB L / (D.nd.l i : ℝ) ^ 2 := div_nonneg (by linarith) (by positivity)
      have h2 := hflat (tab L X tf C) i lam (D.nd.l i)
      have h4 := heP _ hl
      exact add_nonneg (add_nonneg
        (mul_nonneg (mul_nonneg (mul_nonneg hC (by positivity)) (Nat.cast_nonneg _)) h1)
        (mul_nonneg (mul_nonneg (mul_nonneg hC (by positivity)) (Nat.cast_nonneg _)) h2))
        (mul_nonneg (mul_nonneg (mul_nonneg hC (by positivity)) (Nat.cast_nonneg _)) h4)
  · exact nBand

end GlobalTheory.NLink
end
