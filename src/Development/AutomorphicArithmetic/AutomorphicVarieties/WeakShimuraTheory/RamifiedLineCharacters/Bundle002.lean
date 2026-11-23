module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import ReciprocityTheory.Hypotheses.GalCoh
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.DecompSigmaOrd
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.Bundle002
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.Bundle001
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedIdeal
public import Mathlib.Data.FunLike.Fintype

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.Gys.gwLower :
    GlobalFiniteness → GreenbergWiles → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M] [Module (ZMod (l ^ 1)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M], l ≠ 2 → ∀ (S : Finset (HeightOneSpectrum (𝓞 F))) (ρ : Representation (ZMod (l ^ 1)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M), ContainsAbove S l → ContAction ρ →
      ∀ Av : S → ValuationSubring Ω, (∀ v, IsPlaceOver (Av v) v.1) → ∀ L : LocCond ρ (locFam S Av),
        ∏ v : S, Nat.card (L v) ≤ Nat.card (Sel ρ (locFam S Av) (continuous_locFam S Av) L) * (Nat.card (TDual (ZMod (l ^ 1)) M) * Nat.card M ^ Module.finrank ℚ F) *
          ∏ v : S, Nat.card (H0 (ρ.comp (locFam S Av v))) := by
  classical
  intro hGF hGW F Ω _ _ _ _ _ l _ M _ _ _ _ _ hl S ρ hS hρ Av hA L
  obtain ⟨μ, hμ⟩ := GlobalTheory.Published.PoitouTate.exists_lift_cycMod (F := F) (Ω := Ω) (l := l) (r := 1) (S := S) hS
  obtain ⟨c, hc⟩ := UpperTheory.V.Ws.Gys.ccEx F Ω
  have e := hGW F Ω l 1 M S ρ one_pos hl hS hρ μ hμ Av hA c hc L
  haveI : NeZero (l ^ 1) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  haveI hfd : Finite (TDual (ZMod (l ^ 1)) M) := DFunLike.finite _
  haveI hf1 : Finite (H1 ρ) := (hGF F Ω l 1 M S ρ one_pos hS hρ).2.1
  have hM : 0 < Nat.card M := Nat.card_pos
  have p1 : 0 < Nat.card (Sel ρ (locFam S Av) (continuous_locFam S Av) L) := Nat.card_pos
  have p2 : 0 < Nat.card (H0 (twDual μ ρ)) := Nat.card_pos
  have p3 : 0 < ∏ v : S, Nat.card (H0 (ρ.comp (locFam S Av v))) :=
    Finset.prod_pos fun v _ => Nat.card_pos
  have p4 : 0 < archH0Card S ρ c := by
    unfold archH0Card
    refine Nat.mul_pos (Finset.prod_pos fun w _ => ?_) (pow_pos hM _)
    haveI : Nonempty {m : M // ρ (toGS Ω _ (c w)) m = m} := ⟨⟨0, map_zero _⟩⟩
    exact Nat.card_pos
  have b2 : Nat.card (H0 (twDual μ ρ)) ≤ Nat.card (TDual (ZMod (l ^ 1)) M) :=
    Nat.card_le_card_of_injective _ Subtype.val_injective
  have b4 : archH0Card S ρ c ≤ Nat.card M ^ Module.finrank ℚ F := by
    unfold archH0Card
    have h1 : (∏ w ∈ Finset.univ.filter (fun w : InfinitePlace F => w.IsReal),
        Nat.card {m : M // ρ (toGS Ω _ (c w)) m = m}) ≤ Nat.card M ^ InfinitePlace.nrRealPlaces F := by
      have h2 := Finset.prod_le_pow_card (Finset.univ.filter (fun w : InfinitePlace F => w.IsReal))
        (fun w => Nat.card {m : M // ρ (toGS Ω _ (c w)) m = m}) (Nat.card M)
        (fun w _ => Nat.card_le_card_of_injective _ Subtype.val_injective)
      have h3 : (Finset.univ.filter (fun w : InfinitePlace F => w.IsReal)).card = InfinitePlace.nrRealPlaces F := by
        rw [InfinitePlace.nrRealPlaces, Fintype.card_subtype]
      rwa [h3] at h2
    refine (Nat.mul_le_mul_right _ h1).trans ?_
    rw [← pow_add]
    refine Nat.pow_le_pow_right hM ?_
    have := InfinitePlace.card_add_two_mul_card_eq_rank F
    omega
  have hpos := Nat.mul_pos (Nat.mul_pos (Nat.mul_pos p1 p2) p3) p4
  refine (Nat.le_of_dvd hpos (Dvd.intro_left _ e.symm)).trans ?_
  calc _ = Nat.card (Sel ρ (locFam S Av) (continuous_locFam S Av) L) * (Nat.card (H0 (twDual μ ρ)) * archH0Card S ρ c) *
          ∏ v : S, Nat.card (H0 (ρ.comp (locFam S Av v))) := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul b2 b4))
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem rescale {l : ℕ} [Fact l.Prime] (a : ZMod (l ^ 1)) (ha : a ≠ 0) : ∃ b : ZMod (l ^ 1), b * a = 1 := by
  haveI : Fact (l ^ 1).Prime := ⟨by rw [pow_one]; exact Fact.out⟩
  exact ⟨a⁻¹, inv_mul_cancel₀ ha⟩

theorem UpperTheory.V.Ws.Gys.locHoms :
    LocalTateDuality → LocalEulerChar → UnramifiedOrthogonality → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v → ((l : ℕ) : 𝓞 F) ∉ v.asIdeal → (∀ g ∈ Dec (F := F) A, cycMod F Ω l 1 g = 1) →
      ∃ φ₁ ∈ Z1 (Representation.trivial (ZMod (l ^ 1)) (Dec (F := F) A) (ZMod (l ^ 1))), ∃ φ₂ ∈ Z1 (Representation.trivial (ZMod (l ^ 1)) (Dec (F := F) A) (ZMod (l ^ 1))),
        (∀ g : Dec (F := F) A, g.1 ∈ Ine (F := F) A → φ₁ g = 0) ∧ (∃ g, φ₁ g = 1) ∧ ∃ g : Dec (F := F) A, g.1 ∈ Ine (F := F) A ∧ φ₂ g = 1 := by
  intro hT hE hU F Ω _ _ _ _ _ l _ A v hA hl hμ
  obtain ⟨f, hf, hf0⟩ := UpperTheory.V.Ws.Gys.locNe hT hE F Ω l A v hA hl hμ
  haveI : NeZero (l ^ 1) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  let ρ : Representation (ZMod (l ^ 1)) (Dec (F := F) A) (ZMod (l ^ 1)) := Representation.trivial _ _ _
  let χ := (cycMod F Ω l 1).comp (Dec (F := F) A).subtype
  have hχ : ∀ g, χ g = 1 := fun g => hμ g.1 g.2
  have hc : ContAction ρ := continuous_snd
  obtain ⟨hU1, hU2⟩ := hU F Ω l 1 (ZMod (l ^ 1)) A ρ v one_pos hA hl (fun _ _ => rfl) hc
  have hinj := (hT F Ω l 1 (ZMod (l ^ 1)) A ρ v one_pos hA hc).2.2.1.1
  let T : ZMod (l ^ 1) → TDual (ZMod (l ^ 1)) (ZMod (l ^ 1)) := fun t => TDual.mk (LinearMap.mul _ _ t)
  have htriv : ∀ g (m : TDual (ZMod (l ^ 1)) (ZMod (l ^ 1))), twDual χ ρ g m = m := fun g m => by
    apply DFunLike.ext
    intro t
    rw [twDual_apply, hχ, Units.val_one, one_mul]
    rfl
  let y : Z1 (twDual χ ρ) := ⟨fun g => T (f g), (continuous_of_discreteTopology (f := T)).comp hf.1, fun g h => by
    rw [htriv]
    apply DFunLike.ext
    intro m
    change f (g * h) * m = f g * m + f h * m
    rw [hf.2, add_mul]
    rfl⟩
  have hy : ∀ g (m : TDual (ZMod (l ^ 1)) (ZMod (l ^ 1))), y.1 g = twDual χ ρ g m - m → f g = 0 := fun g m h => by
    rw [htriv, sub_self] at h
    have h1 := congrArg (fun φ : TDual (ZMod (l ^ 1)) (ZMod (l ^ 1)) => φ 1) h
    change f g * 1 = 0 at h1
    rwa [mul_one] at h1
  have ha : ∃ φ ∈ Z1 ρ, (∀ g : Dec (F := F) A, g.1 ∈ Ine (F := F) A → φ g = 0) ∧ φ ≠ 0 := by
    by_contra H
    push Not at H
    refine hf0 (H f hf fun g hg => ?_)
    have h := (hU2 (Submodule.Quotient.mk y)).2 fun x hx => by
      induction x using Submodule.Quotient.induction_on with | H x =>
      obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 ((Submodule.Quotient.mk_eq_zero _).1 hx)
      have : x = 0 := Subtype.ext (H x.1 x.2 fun g hg => (hm ⟨g, hg⟩).trans (sub_self _))
      rw [this]
      exact map_zero _
    obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 ((Submodule.Quotient.mk_eq_zero _).1 h)
    exact hy g m (hm ⟨g, hg⟩)
  have hb : ∃ φ ∈ Z1 ρ, ∃ g : Dec (F := F) A, g.1 ∈ Ine (F := F) A ∧ φ g ≠ 0 := by
    by_contra H
    push Not at H
    have hyu : (Submodule.Quotient.mk y : H1 (twDual χ ρ)) ∈
        H1ur (twDual χ ρ) ((Ine (F := F) A).subgroupOf (Dec (F := F) A)) := by
      refine (Submodule.Quotient.mk_eq_zero _).2 ((mem_coboundaries1 _ _).2 ⟨0, fun j => ?_⟩)
      rw [map_zero, sub_zero]
      apply DFunLike.ext
      intro m
      change f j.1 * m = 0
      rw [H f hf j.1 j.2, zero_mul]
    have h0 : (Submodule.Quotient.mk y : H1 (twDual χ ρ)) = 0 := by
      refine hinj ?_
      refine Eq.trans ?_ (map_zero _).symm
      refine LinearMap.ext fun x => ?_
      induction x using Submodule.Quotient.induction_on with | H x =>
      exact (hU1 (Submodule.Quotient.mk x)).1
        ((Submodule.Quotient.mk_eq_zero _).2 ((mem_coboundaries1 _ _).2
          ⟨0, fun j => (H x.1 x.2 j.1 j.2).trans (sub_self _).symm⟩)) _ hyu
    obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 ((Submodule.Quotient.mk_eq_zero _).1 h0)
    exact hf0 (funext fun g => hy g m (hm g))
  obtain ⟨φ₁, h₁, hI, hne⟩ := ha
  obtain ⟨φ₂, h₂, g₂, hg₂, hne₂⟩ := hb
  obtain ⟨g₁, hg₁⟩ := Function.ne_iff.1 hne
  obtain ⟨b₁, e₁⟩ := rescale _ hg₁
  obtain ⟨b₂, e₂⟩ := rescale _ hne₂
  refine ⟨b₁ • φ₁, Submodule.smul_mem _ _ h₁, b₂ • φ₂, Submodule.smul_mem _ _ h₂, fun g hg => ?_, ⟨g₁, e₁⟩, g₂, hg₂, e₂⟩
  rw [Pi.smul_apply, hI g hg, smul_zero]
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.Gys.coefFacts :
    ∀ {l : ℕ} [Fact l.Prime] (c : Coef l) (k : Type) [Field k] (a : c.O →+* k), (∀ x ∈ maximalIdeal c.O, a x = 0) → CharP k l ∧ (Set.range a).Finite := by
  intro l _ c k _ a ha
  haveI := c.dvr
  haveI := c.fin
  obtain ⟨_, hfin, hl, -⟩ := UpperTheory.V.abelian₂.dvr_finite l c.O
  refine ⟨?_, ?_⟩
  · have hk : (l : k) = 0 := by
      rw [← map_natCast a l]
      exact ha _ hl
    exact (CharP.charP_iff_prime_eq_zero (Fact.out : l.Prime)).2 hk
  · let f : ResidueField c.O →+* k := Ideal.Quotient.lift (maximalIdeal c.O) a ha
    refine (Set.finite_range f).subset ?_
    rintro _ ⟨x, rfl⟩
    exact ⟨IsLocalRing.residue c.O x, Ideal.Quotient.lift_mk _ _ _⟩
end
