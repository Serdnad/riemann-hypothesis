module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.LeAdicClosure
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle001
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle023
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle025
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Finiteness.Quotient
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Jacobson.Ring

@[expose] public section

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem aux {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} (hF : F.Ok C₀) (B : Type) [CommRing B] [Algebra O B]
    [IsCO O B] (P : Ideal B) (hP : P.IsPrime) (a : F.G0 → B) (hO : ∀ c ∈ maximalIdeal O, algebraMap O B c ∈ P)
    (h1 : a 1 = 1) (hmul : ∀ g h, a (g * h) - a g * a h ∈ P) (hc : AdicCont (maximalIdeal B) a)
    (hres : ∀ g, a g - 1 ∈ maximalIdeal B) (hst : ∀ g, a (F.star g) = a g)
    (hloc : ∀ v g, g ∈ F.Iv v → F.Ψ (F.loc v g) = 1 → a (F.loc0 v g) - 1 ∈ P) (g : F.G0) : a g - 1 ∈ P := by
  haveI : P.IsPrime := hP
  haveI : Nontrivial (B ⧸ P) := inferInstance
  haveI : IsCO O (B ⧸ P) :=
    co_quot O B (B ⧸ P) (Ideal.Quotient.mkₐ O P) (Ideal.Quotient.mkₐ_surjective O P)
  have hm : ∀ x ∈ maximalIdeal B, Ideal.Quotient.mk P x ∈ maximalIdeal (B ⧸ P) := by
    intro x hx
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    rintro ⟨u, hu⟩
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (↑u⁻¹ : B ⧸ P)
    have hxy : x * y - 1 ∈ P := by
      rw [← Ideal.Quotient.eq, map_mul, hy, ← hu]
      simp
    have h2 : x * y - 1 ∈ maximalIdeal B := IsLocalRing.le_maximalIdeal hP.ne_top hxy
    have h3 : x * y ∈ maximalIdeal B := Ideal.mul_mem_right _ _ hx
    apply (IsLocalRing.maximalIdeal.isMaximal B).ne_top
    rw [Ideal.eq_top_iff_one]
    simpa using Ideal.sub_mem _ h3 h2
  let χ : F.G0 →* B ⧸ P :=
    { toFun := fun g => Ideal.Quotient.mk P (a g)
      map_one' := by simp [h1]
      map_mul' := fun g h => by
        rw [← map_mul]
        exact Ideal.Quotient.eq.mpr (hmul g h) }
  have hχ : ∀ g, χ g = Ideal.Quotient.mk P (a g) := fun g => rfl
  have key := frobenius_corner_middle_trivial hF (B ⧸ P)
    (fun c hc' => by
      rw [IsScalarTower.algebraMap_apply O B (B ⧸ P), Ideal.Quotient.algebraMap_eq,
        Ideal.Quotient.eq_zero_iff_mem]
      exact hO c hc')
    χ
    (fun N => by
      have hle : ∀ x ∈ maximalIdeal B ^ N,
          Ideal.Quotient.mk (maximalIdeal (B ⧸ P) ^ N) (Ideal.Quotient.mk P x) = 0 := by
        intro x hx
        rw [Ideal.Quotient.eq_zero_iff_mem]
        have hmap : Ideal.map (Ideal.Quotient.mk P) (maximalIdeal B) ≤ maximalIdeal (B ⧸ P) :=
          Ideal.map_le_iff_le_comap.mpr hm
        have := Ideal.pow_right_mono hmap N
        rw [← Ideal.map_pow] at this
        exact this (Ideal.mem_map_of_mem _ hx)
      let f := Ideal.Quotient.lift (maximalIdeal B ^ N)
        ((Ideal.Quotient.mk (maximalIdeal (B ⧸ P) ^ N)).comp (Ideal.Quotient.mk P)) hle
      convert (hc N).comp f using 1
      funext x
      rfl)
    (fun g => by
      rw [hχ, ← map_one (Ideal.Quotient.mk P), ← map_sub]
      exact hm _ (hres g))
    (fun g => by rw [hχ, hχ, hst g])
    (fun v g hg hΨ => by
      rw [hχ, ← map_one (Ideal.Quotient.mk P)]
      exact Ideal.Quotient.eq.mpr (hloc v g hg hΨ))
    g
  rw [hχ, ← map_one (Ideal.Quotient.mk P)] at key
  exact Ideal.Quotient.eq.mp key

theorem UpperTheory.V.Fr.frobenius_corner_middle_mem :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ}, F.Ok C₀ → ∀ (S : Space O F 3) (P : Ideal S.B), P.IsPrime → S.lamId ≤ P → (∀ g h, S.aB (g * h) 1 - S.aB g 1 * S.aB h 1 ∈ P) → (∀ v g, S.aB (F.loc0 v g) 1 - S.ψB v 1 g ∈ P) → ∀ g, S.aB g 1 - 1 ∈ P := by
  intro l _ O _ _ _ _ F C₀ hF S P hP hlam hmul hloc
  obtain ⟨hB, hm⟩ := UpperTheory.V.Fr.co_B hF (Or.inr rfl) S
  obtain ⟨-, hc, -, -⟩ := UpperTheory.V.Fr.cont_u hF (Or.inr rfl) S
  obtain ⟨-, -, -, -, hst⟩ := UpperTheory.V.Fr.star hF
  have h1 : S.aB 1 1 = 1 := Subtype.ext (by
    show S.ρ.r 1 1 1 = 1
    rw [map_one, Matrix.one_apply_eq])
  refine aux hF S.B P hP (fun g => S.aB g 1)
    (fun c hc => hlam (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hc))) h1 hmul (hm ▸ hc 1) (fun g => ?_)
    (fun g => Subtype.ext (hst S.ρ g 1 1)) (fun v g hg hΨ => ?_)
  · rw [hm]
    show S.ρ.r g 1 1 - 1 ∈ maximalIdeal S.R
    rw [← res_eq_zero_iff O, map_sub, map_one, sub_eq_zero]
    have h := S.lift.2.1.1 g 1
    have hw : w 3 1 = 0 := rfl
    rw [hw, zpow_zero] at h
    exact h
  · have h2 : S.ψB v 1 g - 1 ∈ P :=
      hlam (Ideal.mem_sup_right (Ideal.subset_span ⟨v, 1, g, hg, hΨ, rfl⟩))
    have h3 := P.add_mem (hloc v g) h2
    rwa [sub_add_sub_cancel] at h3
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem mem_of_forall_sup_pow {B : Type} [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
    (P : Ideal B) (b : B) (h : ∀ N : ℕ, ∃ y ∈ P, b - y ∈ maximalIdeal B ^ N) : b ∈ P := by
  by_cases hP : P = ⊤
  · rw [hP]
    exact Submodule.mem_top
  haveI : Nontrivial (B ⧸ P) := Ideal.Quotient.nontrivial_iff.2 hP
  haveI : IsLocalRing (B ⧸ P) := IsLocalRing.of_surjective' (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective
  have hPm : P ≤ maximalIdeal B := IsLocalRing.le_maximalIdeal hP
  have hmap : maximalIdeal B ≤ (maximalIdeal (B ⧸ P)).comap (Ideal.Quotient.mk P) := by
    intro x hx
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    rintro ⟨u, hu⟩
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (↑u⁻¹ : B ⧸ P)
    have h1 : Ideal.Quotient.mk P (x * y - 1) = 0 := by
      rw [map_sub, map_mul, hy, ← hu, Units.mul_inv, map_one, sub_self]
    have h2 := hPm (Ideal.Quotient.eq_zero_iff_mem.1 h1)
    have h3 := (maximalIdeal B).sub_mem ((maximalIdeal B).mul_mem_right y hx) h2
    rw [sub_sub_cancel] at h3
    exact (IsLocalRing.maximalIdeal.isMaximal B).ne_top ((Ideal.eq_top_iff_one _).2 h3)
  have hb : Ideal.Quotient.mk P b ∈ ⨅ N : ℕ, (maximalIdeal (B ⧸ P)) ^ N := by
    rw [Ideal.mem_iInf]
    intro N
    obtain ⟨y, hy, hby⟩ := h N
    have h3 := Ideal.mem_map_of_mem (Ideal.Quotient.mk P) hby
    rw [Ideal.map_pow] at h3
    have h4 := Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.2 hmap) N h3
    rwa [map_sub, Ideal.Quotient.eq_zero_iff_mem.2 hy, sub_zero] at h4
  rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (IsLocalRing.maximalIdeal.isMaximal _).ne_top, Ideal.mem_bot,
    Ideal.Quotient.eq_zero_iff_mem] at hb
  exact hb

theorem UpperTheory.V.Fr.frobenius_corner_maximalIdeal_le :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ (S : Space O F n) (P : Ideal S.B), (maximalIdeal O).map (algebraMap O S.B) ≤ P → (∀ x : S.B, (x : S.R) ∈ S.ρ.mon 0 → ∃ c : O, x - algebraMap O S.B c ∈ P) → (∀ v i g, ∃ c : O, S.ψB v i g - algebraMap O S.B c ∈ P) → S.mB ≤ P := by
  intro l _ O _ _ _ _ F C₀ n hF hn S P hO hmon hψ
  obtain ⟨hco, hmax⟩ := co_B hF hn S
  haveI := hco
  obtain ⟨-, -, h0, -, -, -, -⟩ := gr_A hF hn S
  obtain ⟨-, -, -, hcl⟩ := cont_u hF hn S
  have hinj : Function.Injective (algebraMap S.B S.A) := by
    intro x y hxy
    apply Subtype.ext
    exact congrArg (fun z : S.A => (z : S.R)) hxy
  by_cases hPt : P = ⊤
  · rw [hPt]
    exact le_top
  have hPm : P ≤ S.mB := hmax ▸ IsLocalRing.le_maximalIdeal hPt
  let T : Subalgebra O S.R :=
    { carrier := {r | ∃ hr : r ∈ S.B, ∃ c : O, (⟨r, hr⟩ : S.B) - algebraMap O S.B c ∈ P}
      mul_mem' := by
        rintro a b ⟨ha, c, hc⟩ ⟨hb, d, hd⟩
        refine ⟨S.B.mul_mem ha hb, c * d, ?_⟩
        have e1 : (⟨a * b, S.B.mul_mem ha hb⟩ : S.B) = ⟨a, ha⟩ * ⟨b, hb⟩ := rfl
        have e : (⟨a, ha⟩ * ⟨b, hb⟩ : S.B) - algebraMap O S.B (c * d) =
            (⟨a, ha⟩ - algebraMap O S.B c) * ⟨b, hb⟩ + algebraMap O S.B c * (⟨b, hb⟩ - algebraMap O S.B d) := by
          rw [map_mul]
          ring
        rw [e1, e]
        exact P.add_mem (P.mul_mem_right _ hc) (P.mul_mem_left _ hd)
      add_mem' := by
        rintro a b ⟨ha, c, hc⟩ ⟨hb, d, hd⟩
        refine ⟨S.B.add_mem ha hb, c + d, ?_⟩
        have e1 : (⟨a + b, S.B.add_mem ha hb⟩ : S.B) = ⟨a, ha⟩ + ⟨b, hb⟩ := rfl
        have e : (⟨a, ha⟩ + ⟨b, hb⟩ : S.B) - algebraMap O S.B (c + d) =
            (⟨a, ha⟩ - algebraMap O S.B c) + (⟨b, hb⟩ - algebraMap O S.B d) := by
          rw [map_add (f := _)]
          ring
        rw [e1, e]
        exact P.add_mem hc hd
      algebraMap_mem' := by
        intro c
        refine ⟨S.B.algebraMap_mem c, c, ?_⟩
        have e : (⟨algebraMap O S.R c, S.B.algebraMap_mem c⟩ : S.B) = algebraMap O S.B c := rfl
        rw [e, sub_self]
        exact P.zero_mem }
  have hB0 : Algebra.adjoin O (S.ρ.mon 0 ∪ {x | ∃ v i g, x = ((S.ρ.ψ v i g : S.Rˣ) : S.R)}) ≤ T := by
    rw [Algebra.adjoin_le_iff]
    rintro r (hr | ⟨v, i, g, rfl⟩)
    · exact ⟨S.mon_mem hr, hmon ⟨r, S.mon_mem hr⟩ hr⟩
    · exact ⟨(S.ψB v i g).2, hψ v i g⟩
  intro x hx
  apply mem_of_forall_sup_pow P x
  intro N
  obtain ⟨M, hM⟩ := hcl 0 (N + 1)
  have hxB : ∀ K : ℕ, ∃ y ∈ Algebra.adjoin O (S.ρ.mon 0 ∪ {x | ∃ v i g, x = ((S.ρ.ψ v i g : S.Rˣ) : S.R)}),
      (x : S.R) - y ∈ maximalIdeal S.R ^ K := x.2
  obtain ⟨y0, hy0, hxy⟩ := hxB M
  obtain ⟨hy0B, c, hc⟩ := hB0 hy0
  obtain ⟨z, hzdef⟩ : ∃ z : S.B, z = x - ⟨y0, hy0B⟩ := ⟨_, rfl⟩
  have hz : algebraMap S.B S.A z ∈ S.mB ^ (N + 1) • S.gr 0 := by
    refine hM _ ?_ ?_
    · rw [h0]
      exact Submodule.algebraMap_mem z
    · rw [hzdef]
      exact hxy
  rw [h0] at hz
  have key : ∀ a ∈ S.mB ^ (N + 1) • (1 : Submodule S.B S.A), ∃ w ∈ S.mB ^ (N + 1), a = algebraMap S.B S.A w := by
    intro a ha
    refine Submodule.smul_induction_on (p := fun a => ∃ w ∈ S.mB ^ (N + 1), a = algebraMap S.B S.A w) ha ?_ ?_
    · intro r hr t ht
      obtain ⟨s, rfl⟩ := Submodule.mem_one.1 ht
      exact ⟨r * s, Ideal.mul_mem_right _ _ hr, by rw [Algebra.smul_def, map_mul]⟩
    · rintro a b ⟨w1, h1, rfl⟩ ⟨w2, h2, rfl⟩
      exact ⟨w1 + w2, add_mem h1 h2, (map_add _ _ _).symm⟩
  obtain ⟨w, hw, hzw⟩ := key _ hz
  have hzw' : z = w := hinj hzw
  have hzm : z ∈ S.mB := hzw' ▸ Ideal.pow_le_self (Nat.succ_ne_zero N) hw
  have hzN : z ∈ S.mB ^ N := hzw' ▸ Ideal.pow_le_pow_right (Nat.le_succ N) hw
  have hyB : (⟨y0, hy0B⟩ : S.B) ∈ S.mB := by
    have e : (⟨y0, hy0B⟩ : S.B) = x - z := by rw [hzdef, sub_sub_cancel]
    rw [e]
    exact S.mB.sub_mem hx hzm
  have hcB : algebraMap O S.B c ∈ S.mB := by
    have e : algebraMap O S.B c = ⟨y0, hy0B⟩ - (⟨y0, hy0B⟩ - algebraMap O S.B c) := (sub_sub_cancel _ _).symm
    rw [e]
    exact S.mB.sub_mem hyB (hPm hc)
  have hcO : c ∈ maximalIdeal O := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have h1 : ((algebraMap O S.B c : S.B) : S.R) ∈ maximalIdeal S.R := hcB
    have h2 : IsUnit ((algebraMap O S.B c : S.B) : S.R) := hu.map (algebraMap O S.R)
    exact ((IsLocalRing.mem_maximalIdeal _).1 h1) h2
  have hyP : (⟨y0, hy0B⟩ : S.B) ∈ P := by
    have e : (⟨y0, hy0B⟩ : S.B) = (⟨y0, hy0B⟩ - algebraMap O S.B c) + algebraMap O S.B c := (sub_add_cancel _ _).symm
    rw [e]
    exact P.add_mem hc (hO (Ideal.mem_map_of_mem _ hcO))
  refine ⟨⟨y0, hy0B⟩, hyP, ?_⟩
  rw [hmax, ← hzdef]
  exact hzN
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem fibre_closed {B A : Type} [CommRing B] [CommRing A] [Algebra B A] [Algebra.FiniteType B A]
    (m : Ideal B) [m.IsMaximal] (W : Set (PrimeSpectrum A)) (hW : IsLocallyClosed W) (p : PrimeSpectrum A)
    (hp : p ∈ W) (hm : m ≤ p.asIdeal.comap (algebraMap B A)) :
    ∃ x ∈ W, m ≤ x.asIdeal.comap (algebraMap B A) ∧ x.asIdeal.IsMaximal := by
  obtain ⟨U, Z, hU, hZ, rfl⟩ := hW
  obtain ⟨hpU, hpZ⟩ := hp
  obtain ⟨_, ⟨_, ⟨f, rfl⟩, rfl⟩, hpf, hfU⟩ := PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hpU hU
  have hqmax : (p.asIdeal.comap (algebraMap B A)).IsMaximal := by
    have e := Ideal.IsMaximal.eq_of_le ‹m.IsMaximal› (Ideal.IsPrime.comap (algebraMap B A)).ne_top hm
    rw [← e]
    infer_instance
  letI := Ideal.Quotient.field (p.asIdeal.comap (algebraMap B A))
  haveI : IsJacobsonRing (A ⧸ p.asIdeal) :=
    isJacobsonRing_of_finiteType (A := B ⧸ p.asIdeal.comap (algebraMap B A))
  have hbot : (⊥ : Ideal (A ⧸ p.asIdeal)).jacobson = ⊥ :=
    isJacobsonRing_iff_prime_eq.1 ‹_› ⊥ Ideal.isPrime_bot
  have hf0 : Ideal.Quotient.mk p.asIdeal f ∉ (⊥ : Ideal (A ⧸ p.asIdeal)).jacobson := by
    rw [hbot, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem]
    exact (PrimeSpectrum.mem_basicOpen _ _).1 hpf
  have hf1 : ¬ ∀ J ∈ {J : Ideal (A ⧸ p.asIdeal) | ⊥ ≤ J ∧ J.IsMaximal}, Ideal.Quotient.mk p.asIdeal f ∈ J :=
    fun h => hf0 (Ideal.mem_sInf.2 h)
  push_neg at hf1
  obtain ⟨J, ⟨-, hJ⟩, hfJ⟩ := hf1
  haveI := hJ
  haveI := hJ.isPrime
  have hle : p.asIdeal ≤ J.comap (Ideal.Quotient.mk p.asIdeal) := fun a ha => by
    rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 ha]
    exact J.zero_mem
  refine ⟨⟨J.comap (Ideal.Quotient.mk p.asIdeal), Ideal.IsPrime.comap _⟩, ⟨hfU ?_, ?_⟩, ?_,
    Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective⟩
  · exact hfJ
  · have hpx : p ≤ ⟨J.comap (Ideal.Quotient.mk p.asIdeal), Ideal.IsPrime.comap _⟩ := hle
    exact hZ.closure_subset_iff.2 (Set.singleton_subset_iff.2 hpZ) ((PrimeSpectrum.le_iff_mem_closure _ _).1 hpx)
  · exact hm.trans (Ideal.comap_mono hle)

theorem UpperTheory.V.Fr.jac :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ S : Space O F n, ∀ C : Set (PrimeSpectrum S.A), IsClosed C → ∀ U : Set (PrimeSpectrum S.A), IsOpen U → (C ∩ U ∩ S.BB).Nonempty → ∃ x ∈ C ∩ U ∩ S.BB, x.asIdeal.IsMaximal := by
  intro l _ O _ _ _ _ F C₀ n hF hn S C hC U hU hne
  obtain ⟨-, -, -, -, hft, -, -⟩ := gr_A hF hn S
  obtain ⟨hco, hmax⟩ := co_B hF hn S
  haveI := hco
  haveI : S.mB.IsMaximal := hmax ▸ IsLocalRing.maximalIdeal.isMaximal S.B
  obtain ⟨p, ⟨hpC, hpU⟩, hpm, hpT⟩ := hne
  have hO : IsOpen {x : PrimeSpectrum S.A | ¬ S.u.triP ≤ x.asIdeal} :=
    (PrimeSpectrum.isClosed_zeroLocus (S.u.triP : Set S.A)).isOpen_compl
  have hW : IsLocallyClosed (C ∩ U ∩ {x : PrimeSpectrum S.A | ¬ S.u.triP ≤ x.asIdeal}) :=
    (hC.isLocallyClosed.inter hU.isLocallyClosed).inter hO.isLocallyClosed
  obtain ⟨x, ⟨⟨hxC, hxU⟩, hxT⟩, hxm, hxmax⟩ := fibre_closed S.mB _ hW p ⟨⟨hpC, hpU⟩, hpT⟩ hpm
  exact ⟨x, ⟨⟨hxC, hxU⟩, hxm, hxT⟩, hxmax⟩
end
