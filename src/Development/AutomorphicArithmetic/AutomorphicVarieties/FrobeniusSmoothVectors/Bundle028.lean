module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Integral
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle014
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle022
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle019
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle012
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle013
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.LeAdicClosure
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle023
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle025
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle015
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.AdditiveValuation.UnramExtY
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
public import Mathlib.RingTheory.GradedAlgebra.Radical
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Sheaves.Init
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle007
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.FieldTheory.PrimitiveElement

@[expose] public section

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem alg_vring {C K : Type} [CommRing C] [IsLocalRing C] [CommRing K] [Algebra C K]
    {P : ℤ → Submodule C K} [SetLike.GradedMonoid P] (h : HasVertex P) (hi : Function.Injective (algebraMap C K))
    (hn : IsNoetherianRing (lauSub P)) : IsVertexRing C (vertex h) := by
  have hcoeff : ∀ c : C, ((algebraMap C (lauSub P) c : lauSub P) : AddMonoidAlgebra K ℤ).coeff 0 = algebraMap C K c := by
    intro c
    simp
  refine ⟨hn, ?_, alg_sep h hn, ?_, ?_⟩
  · intro c c' hcc
    apply hi
    rw [← hcoeff c, ← hcoeff c', hcc]
  · ext c
    rw [Ideal.mem_comap, mem_vertex, hcoeff]
    constructor
    · rintro ⟨c', hc', he⟩
      rwa [← hi he]
    · intro hc
      exact ⟨c, hc, rfl⟩
  · intro d
    obtain ⟨c, hc⟩ := h.zero _ (d.2 0)
    refine ⟨c, ?_⟩
    rw [mem_vertex]
    refine ⟨0, (maximalIdeal C).zero_mem, ?_⟩
    simp [hc]

private theorem alg_ev (C K : Type) [CommRing C] [CommRing K] [Algebra C K] :
    ∃ e : AddMonoidAlgebra K ℤ →ₐ[C] K, ∀ j x, e (AddMonoidAlgebra.single j x) = x := by
  refine ⟨AddMonoidAlgebra.liftNCAlgHom (AlgHom.id C K) 1 (fun _ _ => Commute.one_right _), fun j x => ?_⟩
  exact (AddMonoidAlgebra.liftNC_single _ _ _ _).trans (by simp)

theorem UpperTheory.V.Fr.alg :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ S : Space O F n, ∀ (C : Type) [CommRing C] [Algebra O C] [IsCO O C] (K : Type) [CommRing K] [Algebra O K] [Algebra C K] [IsScalarTower O C K], Function.Injective (algebraMap C K) → ∀ ρ : NRep F n K, Cone O C ρ → ∃ (ξ : S.A →ₐ[O] K) (β : S.B →ₐ[O] C), S.u.map (ξ : S.A →+* K) = ρ ∧ ∀ b, ξ (S.inc b) = algebraMap C K (β b) := by
  intro l _ O _ _ _ _ F C₀ n hF hn S C _ _ _ K _ _ _ _ hi ρ hcone
  have hv := alg_vertex C ρ hcone
  haveI := alg_ft C ρ hcone.fg
  have hN : IsNoetherianRing (lauSub (NRep.part C ρ)) := Algebra.FiniteType.isNoetherianRing C _
  have hvr := alg_vring hv hi hN
  obtain ⟨ρD, h1, h2⟩ := alg_lau C ρ hcone
  have hmod := alg_model C ρ hcone hv ρD h1 h2
  letI : Algebra O (lauSub (NRep.part C ρ)) :=
    ((algebraMap C (lauSub (NRep.part C ρ))).comp (algebraMap O C)).toAlgebra
  haveI : IsScalarTower O C (lauSub (NRep.part C ρ)) := IsScalarTower.of_algebraMap_eq' rfl
  obtain ⟨ξ, β, hξ, hβ⟩ := alg_limit S C (vertex hv) ρD hvr hmod
  obtain ⟨e, he⟩ := alg_ev C K
  let ev : lauSub (NRep.part C ρ) →ₐ[O] K := (e.comp (lauSub (NRep.part C ρ)).val).restrictScalars O
  refine ⟨ev.comp ξ, β, ?_, fun b => ?_⟩
  · apply NRep.ext
    · ext g i j
      rw [NRep.map_r]
      have hr := NRep.map_r (ξ : S.A →+* lauSub (NRep.part C ρ)) S.u g i j
      rw [hξ] at hr
      show e ((ξ (S.u.r g i j) : lauSub (NRep.part C ρ)) : AddMonoidAlgebra K ℤ) = _
      have hr' : ξ (S.u.r g i j) = ρD.r g i j := hr.symm
      rw [hr', h1, he]
    · funext v i
      ext g
      rw [NRep.map_ψ]
      have hp := NRep.map_ψ (ξ : S.A →+* lauSub (NRep.part C ρ)) S.u v i g
      rw [hξ] at hp
      show e ((ξ ((S.u.ψ v i g : S.Aˣ) : S.A) : lauSub (NRep.part C ρ)) : AddMonoidAlgebra K ℤ) = _
      have hp' : ξ ((S.u.ψ v i g : S.Aˣ) : S.A) = ((ρD.ψ v i g : (lauSub (NRep.part C ρ))ˣ) : lauSub (NRep.part C ρ)) := hp.symm
      rw [hp', h2, he]
  · show e ((ξ (S.inc b) : lauSub (NRep.part C ρ)) : AddMonoidAlgebra K ℤ) = _
    rw [hβ b]
    exact e.commutes (β b)
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem ex_core {B A : Type} [CommRing B] [CommRing A] [Algebra B A] (𝒜 : ℤ → Submodule B A) [GradedAlgebra 𝒜]
    (h0 : 𝒜 0 = 1) (hinj : Function.Injective (algebraMap B A)) (p : Ideal B) [p.IsPrime] :
    ∃ η : Ideal A, η.IsPrime ∧ η.IsHomogeneous 𝒜 ∧ η.comap (algebraMap B A) = p := by
  classical
  have key : ∀ x ∈ Ideal.map (algebraMap B A) p, ∃ c ∈ p, GradedAlgebra.proj 𝒜 0 x = algebraMap B A c := by
    intro x hx
    have hx' : x ∈ (p • (⊤ : Submodule B A)) := by
      rw [Ideal.smul_top_eq_map]
      exact hx
    refine Submodule.smul_induction_on (p := fun x => ∃ c ∈ p, GradedAlgebra.proj 𝒜 0 x = algebraMap B A c)
      hx' ?_ ?_
    · intro b hb y _
      have hy : GradedAlgebra.proj 𝒜 0 y ∈ 𝒜 0 := by
        rw [GradedAlgebra.proj_apply]
        exact SetLike.coe_mem _
      rw [h0] at hy
      obtain ⟨c, hc⟩ := Submodule.mem_one.mp hy
      refine ⟨b * c, p.mul_mem_right c hb, ?_⟩
      rw [LinearMap.map_smul, ← hc, Algebra.smul_def, map_mul]
    · intro x y hx hy
      obtain ⟨c, hc, hxc⟩ := hx
      obtain ⟨d, hd, hyd⟩ := hy
      exact ⟨c + d, p.add_mem hc hd, by rw [map_add (f := _), hxc, hyd, map_add (f := _)]⟩
  have hdisj : Disjoint ((Ideal.map (algebraMap B A) p : Ideal A) : Set A)
      (Algebra.algebraMapSubmonoid A p.primeCompl : Set A) := by
    rw [Set.disjoint_left]
    rintro x hxJ ⟨s, hs, rfl⟩
    obtain ⟨c, hc, he⟩ := key _ hxJ
    rw [GradedAlgebra.proj_apply, DirectSum.decompose_of_mem_same 𝒜 (SetLike.algebraMap_mem_graded 𝒜 s)] at he
    exact hs (by rw [hinj he]; exact hc)
  obtain ⟨P, hP, hJP, hPd⟩ := Ideal.exists_le_prime_disjoint _ _ hdisj
  refine ⟨(P.homogeneousCore 𝒜).toIdeal, Ideal.IsPrime.homogeneousCore (𝒜 := 𝒜) hP,
    (P.homogeneousCore 𝒜).isHomogeneous, ?_⟩
  apply le_antisymm
  · intro b hb
    rw [Ideal.mem_comap] at hb
    have hbP : algebraMap B A b ∈ P := Ideal.toIdeal_homogeneousCore_le 𝒜 P hb
    by_contra hnb
    exact Set.disjoint_left.mp hPd hbP ⟨b, hnb, rfl⟩
  · intro b hb
    rw [Ideal.mem_comap]
    exact Ideal.mem_homogeneousCore_of_homogeneous_of_mem ⟨0, SetLike.algebraMap_mem_graded 𝒜 b⟩
      (hJP (Ideal.mem_map_of_mem _ hb))

private theorem one_le_td {B A : Type} [CommRing B] [CommRing A] [Algebra B A] (𝒜 : ℤ → Submodule B A)
    [GradedAlgebra 𝒜] (η : Ideal A) (hη : η.IsPrime) (hh : η.IsHomogeneous 𝒜) {a : A} {α : ℤ} (ha : a ∈ 𝒜 α)
    (hα : α ≠ 0) (ha' : a ∉ η) : 1 ≤ Algebra.trdeg (B ⧸ η.comap (algebraMap B A)) (A ⧸ η) := by
  classical
  have key : ∀ Q : Polynomial B, Polynomial.aeval a Q ∈ η → ∀ k, Q.coeff k ∈ η.comap (algebraMap B A) := by
    intro Q hQ k
    have hn : Q.natDegree < Q.natDegree + k + 1 := by omega
    rw [Polynomial.aeval_eq_sum_range' hn] at hQ
    have hmem : ∀ i : ℕ, Q.coeff i • a ^ i ∈ 𝒜 (i • α) := fun i =>
      Submodule.smul_mem _ _ (SetLike.pow_mem_graded i ha)
    have h2 : GradedAlgebra.proj 𝒜 (k • α)
        (∑ i ∈ Finset.range (Q.natDegree + k + 1), Q.coeff i • a ^ i) ∈ η := by
      rw [GradedAlgebra.proj_apply]
      exact (Ideal.IsHomogeneous.mem_iff 𝒜 hh).1 hQ _

    rw [map_sum, Finset.sum_eq_single k] at h2
    · rw [GradedAlgebra.proj_apply, DirectSum.decompose_of_mem_same 𝒜 (hmem k), Algebra.smul_def] at h2
      rcases hη.mem_or_mem h2 with h | h
      · exact h
      · exact absurd (hη.mem_of_pow_mem _ h) ha'
    · intro i _ hik
      rw [GradedAlgebra.proj_apply, DirectSum.decompose_of_mem_ne 𝒜 (hmem i)]
      intro he
      apply hik
      have he' : (i : ℤ) * α = (k : ℤ) * α := by simpa [nsmul_eq_mul] using he
      exact_mod_cast mul_right_cancel₀ hα he'
    · intro hk
      exact absurd (Finset.mem_range.2 (by omega)) hk
  have htr : Transcendental (B ⧸ η.comap (algebraMap B A)) (Ideal.Quotient.mk η a) := by
    rw [transcendental_iff]
    intro P hP
    obtain ⟨Q, rfl⟩ := Polynomial.map_surjective (Ideal.Quotient.mk (η.comap (algebraMap B A)))
      Ideal.Quotient.mk_surjective P
    have e : Polynomial.aeval (Ideal.Quotient.mk η a) (Q.map (Ideal.Quotient.mk (η.comap (algebraMap B A))))
        = Ideal.Quotient.mk η (Polynomial.aeval a Q) := by
      have e1 := Polynomial.aeval_map_algebraMap (B ⧸ η.comap (algebraMap B A)) (Ideal.Quotient.mk η a) Q
      rw [Ideal.Quotient.algebraMap_eq] at e1
      rw [e1, ← Ideal.Quotient.mkₐ_eq_mk B η, Polynomial.aeval_algHom_apply]
    rw [e, Ideal.Quotient.eq_zero_iff_mem] at hP
    ext k
    rw [Polynomial.coeff_map, Polynomial.coeff_zero, Ideal.Quotient.eq_zero_iff_mem]
    exact key Q hP k
  haveI : Algebra.Transcendental (B ⧸ η.comap (algebraMap B A)) (A ⧸ η) := ⟨⟨_, htr⟩⟩
  exact Cardinal.one_le_iff_pos.2 (trdeg_pos _ _)

private theorem pair {B A : Type} [CommRing B] [CommRing A] [Algebra B A] (𝒜 : ℤ → Submodule B A)
    [SetLike.GradedMonoid 𝒜] (h0 : 𝒜 0 = 1) {ξ η : Ideal A} (hξ : ξ.IsPrime)
    (hle : η.comap (algebraMap B A) ≤ ξ.comap (algebraMap B A)) {a b : A} {α β : ℤ} (ha : a ∈ 𝒜 α) (hb : b ∈ 𝒜 β)
    (hα : 0 < α) (hβ : β < 0) (ha' : a ∉ ξ) (hb' : b ∉ ξ) : a ∉ η ∧ b ∉ η := by
  obtain ⟨m, hm⟩ : ∃ m : ℕ, (m : ℤ) = α := ⟨α.toNat, Int.toNat_of_nonneg hα.le⟩
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (k : ℤ) = -β := ⟨(-β).toNat, Int.toNat_of_nonneg (by omega)⟩
  have hm0 : 0 < m := by omega
  have hk0 : 0 < k := by omega
  have hmem : a ^ k * b ^ m ∈ 𝒜 0 := by
    have h1 := SetLike.mul_mem_graded (SetLike.pow_mem_graded k ha) (SetLike.pow_mem_graded m hb)
    have he : k • α + m • β = 0 := by
      rw [nsmul_eq_mul, nsmul_eq_mul, hk, hm]
      ring
    rwa [he] at h1
  rw [h0] at hmem
  obtain ⟨x, hx⟩ := Submodule.mem_one.mp hmem
  have hc : a ^ k * b ^ m ∉ ξ := by
    intro hin
    rcases hξ.mem_or_mem hin with h | h
    · exact ha' (hξ.mem_of_pow_mem _ h)
    · exact hb' (hξ.mem_of_pow_mem _ h)
  have hxξ : x ∉ ξ.comap (algebraMap B A) := by
    rw [Ideal.mem_comap, hx]
    exact hc
  have hxη : x ∉ η.comap (algebraMap B A) := fun hin => hxξ (hle hin)
  rw [Ideal.mem_comap, hx] at hxη
  constructor
  · intro hin
    exact hxη (Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ hin _ hk0))
  · intro hin
    exact hxη (Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ hin _ hm0))

private theorem w_lt {n : ℕ} {i j : Fin n} (h : i < j) : w n j < w n i := by
  have : (i : ℕ) < j := h
  unfold w
  split_ifs <;> omega

theorem UpperTheory.V.Fr.frobenius_corner_lift_two_to_three :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ S : Space O F n, ∀ (p : Ideal S.B) (ξ : Ideal S.A), p.IsPrime → ξ.IsPrime → S.u.TI ξ → p ≤ S.π ξ → ∃ η : Ideal S.A, η.IsPrime ∧ S.IsHom η ∧ S.π η = p ∧ S.u.TI η ∧ S.td η = 1 := by
  intro l _ O _ _ _ _ F C₀ n hF hn S p ξ hp hξ hTI hle
  obtain ⟨hint, hgm, h0, -, -, -, hr⟩ := gr_A hF hn S
  letI : GradedAlgebra S.gr := { hgm, hint.chooseDecomposition with }
  have hinj : Function.Injective (algebraMap S.B S.A) := by
    intro x y hxy
    apply Subtype.ext
    exact congrArg (fun z : S.A => (z : S.R)) hxy
  obtain ⟨η, hηp, hηh, hηc⟩ := ex_core S.gr h0 hinj p
  have hP := hTI.1.1
  have hM := hTI.1.2
  simp only [NRep.triP, NRep.triM, Ideal.span_le, Set.not_subset] at hP hM
  obtain ⟨_, ⟨g, i, j, hji, rfl⟩, hb⟩ := hP
  obtain ⟨_, ⟨g', i', j', hij', rfl⟩, ha⟩ := hM
  have hbd : w n i - w n j < 0 := by have := w_lt hji; omega
  have had : 0 < w n i' - w n j' := by have := w_lt hij'; omega
  have hle' : η.comap (algebraMap S.B S.A) ≤ ξ.comap (algebraMap S.B S.A) := by
    rw [hηc]; exact hle
  have hab := pair S.gr h0 hξ hle' (hr g' i' j') (hr g i j) had hbd ha hb
  refine ⟨η, hηp, ?_, hηc, ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · apply le_antisymm
    · have e := (Ideal.IsHomogeneous.iff_eq S.gr η).mp hηh
      calc η = _ := e.symm
        _ ≤ _ := Ideal.span_mono ?_
      rintro _ ⟨⟨x, hxh⟩, hx, rfl⟩
      exact ⟨hx, hxh⟩
    · exact Ideal.span_le.2 fun x hx => hx.1
  · intro h
    exact hab.2 (h (Ideal.subset_span ⟨g, i, j, hji, rfl⟩))
  · intro h
    exact hab.1 (h (Ideal.subset_span ⟨g', i', j', hij', rfl⟩))
  · intro h3 h
    have hE := hTI.2 h3
    simp only [NRep.ee, Ideal.span_le, Set.not_subset] at hE
    obtain ⟨_, ⟨g'', i'', j'', hodd, rfl⟩, hc⟩ := hE
    have hne : w n i'' - w n j'' ≠ 0 := by
      rintro h0'
      rw [h0'] at hodd
      exact (Int.not_odd_iff_even.2 ⟨0, by norm_num⟩) hodd
    have hcη : S.u.r g'' i'' j'' ∉ η := by
      rcases lt_or_gt_of_ne hne with hneg | hpos
      · exact (pair S.gr h0 hξ hle' (hr g' i' j') (hr g'' i'' j'') had hneg ha hc).2
      · exact (pair S.gr h0 hξ hle' (hr g'' i'' j'') (hr g i j) hpos hbd hc hb).1
    exact hcη (h (Ideal.subset_span ⟨g'', i'', j'', hodd, rfl⟩))
  · exact le_antisymm (fibre hF hn S η hηp ⟨fun h => hab.2 (h (Ideal.subset_span ⟨g, i, j, hji, rfl⟩)),
      fun h => hab.1 (h (Ideal.subset_span ⟨g', i', j', hij', rfl⟩))⟩)
      (one_le_td S.gr η hηp hηh (hr g' i' j') had.ne' hab.1)
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem prim_ex (k K : Type) [Field k] [Field K] [Finite K] [Algebra k K] :
    ∃ g : Polynomial k, g.Monic ∧ Irreducible g ∧ Nonempty (AdjoinRoot g ≃ₐ[k] K) := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element k K
  have hint : IsIntegral k α := Algebra.IsIntegral.isIntegral α
  exact ⟨minpoly k α, minpoly.monic hint, minpoly.irreducible hint,
    ⟨(IntermediateField.adjoinRootEquivAdjoin k hint).trans
      ((IntermediateField.equivOfEq hα).trans IntermediateField.topEquiv)⟩⟩

private theorem unr_ex {l : ℕ} (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O]
    (K : Type) [Field K] [Finite K] [Algebra O K] (hK : ∀ a ∈ maximalIdeal O, algebraMap O K a = 0) :
    ∃ (O' : Type) (_ : CommRing O') (_ : IsDomain O') (_ : IsDiscreteValuationRing O') (_ : IsCoef l O')
      (_ : Algebra O O') (_ : Module.Finite O O'), (maximalIdeal O).map (algebraMap O O') = maximalIdeal O' ∧
      Nonempty (K →ₐ[O] ResidueField O') := by
  letI : Algebra (ResidueField O) K := (Ideal.Quotient.lift (maximalIdeal O) (algebraMap O K) hK).toAlgebra
  haveI : IsScalarTower O (ResidueField O) K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨g, hg, hgi, ⟨e⟩⟩ := prim_ex (ResidueField O) K
  obtain ⟨f, hf1, -, hf⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
    (f := residue O) (p := g) (Polynomial.mem_lifts_of_surjective residue_surjective _) hg
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨hd, hv, hi, hc⟩ := KStar.Binom.adjoinRoot_unramified hϖ hf (hf1 ▸ hgi)
  haveI : Module.Finite O (AdjoinRoot f) := hf.finite_adjoinRoot
  have hm : (maximalIdeal O).map (algebraMap O (AdjoinRoot f)) = maximalIdeal (AdjoinRoot f) := by
    rw [hϖ.maximalIdeal_eq, hi.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]
  haveI hl : IsLocalHom (algebraMap O (AdjoinRoot f)) := ((local_hom_tfae _).out 1 3).2 hm.le
  have hcl : UpperTheory.V.CA.IsCL O (AdjoinRoot f) := UpperTheory.V.CA.cl_fin O O (AdjoinRoot f) (UpperTheory.V.CA.IsCL.of_isCO O O)
  have hfin : Finite (ResidueField (AdjoinRoot f)) := Nat.finite_of_card_ne_zero (by
    rw [hc]; exact pow_ne_zero _ Nat.card_pos.ne')
  have hch : CharP (ResidueField (AdjoinRoot f)) l :=
    charP_of_injective_ringHom (ResidueField.map (algebraMap O (AdjoinRoot f))).injective l
  refine ⟨AdjoinRoot f, inferInstance, hd, hv, ⟨hcl.complete, hfin, hch⟩, inferInstance, inferInstance, hm, ?_⟩
  have h0 : Polynomial.aeval (residue (AdjoinRoot f) (AdjoinRoot.root f)) g = 0 := by
    rw [← hf1]
    have h1 : Polynomial.aeval (residue (AdjoinRoot f) (AdjoinRoot.root f)) f = 0 := by
      have := Polynomial.aeval_algebraMap_apply (ResidueField (AdjoinRoot f)) (AdjoinRoot.root f) f
      rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self, map_zero] at this
      exact this
    exact (Polynomial.aeval_map_algebraMap (ResidueField O) _ f).trans h1
  exact ⟨((AdjoinRoot.liftAlgHom _ (Algebra.ofId _ _) _ h0).comp e.symm.toAlgHom).restrictScalars O⟩

private theorem res_eq_of {O R : Type} [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R] [IsCO O R]
    {x : R} {a : O} (h : x - algebraMap O R a ∈ maximalIdeal R) : res O R x = algebraMap O _ a := by
  have := (res_eq_zero_iff O R _).2 h
  rwa [map_sub, AlgHom.commutes, sub_eq_zero] at this

private theorem cpl_univ (O D R : Type) [CommRing O] [IsLocalRing O] [CommRing D] [Algebra O D] [IsNoetherianRing D]
    (φ : D →ₐ[O] ResidueField O) [CommRing R] [IsLocalRing R] [Algebra D R] [Algebra O R] [IsScalarTower O D R]
    [(RingHom.ker φ.toRingHom).IsMaximal] (hc : UpperTheory.V.CA.IsCplAt (RingHom.ker φ.toRingHom) R) :
    ∃ (_ : IsCO O R), (∀ a, res O R (algebraMap D R a) = φ a) ∧
      ∀ (C : Type) [CommRing C] [Algebra O C] [IsCO O C] (f : D →ₐ[O] C),
        (∀ a, res O C (f a) = φ a) → ∃! g : R →ₐ[O] C, ∀ a, g (algebraMap D R a) = f a := by
  have hy : ∀ d : D, algebraMap D R d ∈ maximalIdeal R ↔ φ d = 0 := fun d => by
    have := hc.comap_pow 1
    rw [pow_one, pow_one] at this
    rw [← Ideal.mem_comap, this]
    rfl
  have hs : ∀ d : D, ∃ a : O, φ d = algebraMap O _ a ∧ algebraMap D R d - algebraMap O R a ∈ maximalIdeal R :=
    fun d => by
      obtain ⟨a, ha⟩ := residue_surjective (φ d)
      refine ⟨a, ha.symm, ?_⟩
      rw [IsScalarTower.algebraMap_apply O D R, ← map_sub, hy, map_sub, AlgHom.commutes, sub_eq_zero]
      exact ha.symm
  haveI := hc.noeth
  have hco : IsCO O R :=
    { complete := hc.complete
      isLocalHom := ⟨fun a ha => by
        by_contra hn
        have h1 : algebraMap D R (algebraMap O D a) ∈ maximalIdeal R := by
          rw [hy, AlgHom.commutes]
          exact (residue_eq_zero_iff a).2 hn
        rw [← IsScalarTower.algebraMap_apply] at h1
        exact h1 ha⟩
      res_surj := fun r => by
        obtain ⟨d, hd⟩ := hc.dense 1 r
        obtain ⟨a, -, ha⟩ := hs d
        rw [pow_one] at hd
        exact ⟨a, by simpa using add_mem hd ha⟩ }
  refine ⟨hco, fun d => ?_, fun C _ _ _ f hf => ?_⟩
  · obtain ⟨a, h1, h2⟩ := hs d
    rw [h1, res_eq_of h2]
  · obtain ⟨G, ⟨h1, h2⟩, hu⟩ := (UpperTheory.V.CA.cpl_uniq _ hc).1 C (maximalIdeal C) f.toRingHom fun d hd => by
      rw [Ideal.mem_comap, ← res_eq_zero_iff O]
      exact (hf d).trans hd
    have h3 : ∀ d, G (algebraMap D R d) = f d := fun d => DFunLike.congr_fun h1 d
    refine ⟨{ G with commutes' := fun a => ?_ }, h3, fun g hg => ?_⟩
    · rw [IsScalarTower.algebraMap_apply O D R]
      exact (h3 _).trans (f.commutes a)
    · have := hu g.toRingHom ⟨RingHom.ext hg, fun z hz => by
        rw [Ideal.mem_comap, ← res_eq_zero_iff O]
        exact (UpperTheory.V.Alg.res_map g z).trans ((res_eq_zero_iff O R z).2 hz)⟩
      exact AlgHom.ext fun z => DFunLike.congr_fun this z

private theorem cpl_ex (O D : Type) [CommRing O] [IsLocalRing O] [CommRing D] [Algebra O D] [IsNoetherianRing D]
    (φ : D →ₐ[O] ResidueField O) :
    ∃ (R : Type) (_ : CommRing R) (_ : Algebra O R) (_ : IsCO O R) (j : D →ₐ[O] R), (∀ a, res O R (j a) = φ a) ∧
      ∀ (C : Type) [CommRing C] [Algebra O C] [IsCO O C] (f : D →ₐ[O] C),
        (∀ a, res O C (f a) = φ a) → ∃! g : R →ₐ[O] C, ∀ a, g (j a) = f a := by
  haveI hm : (RingHom.ker φ.toRingHom).IsMaximal := RingHom.ker_isMaximal_of_surjective _ fun z => by
    obtain ⟨a, rfl⟩ := residue_surjective z
    exact ⟨algebraMap O D a, φ.commutes a⟩
  have key : ∃ (R : Type) (_ : CommRing R) (_ : IsLocalRing R) (_ : Algebra D R),
      UpperTheory.V.CA.IsCplAt (RingHom.ker φ.toRingHom) R := by
    obtain ⟨hloc, hc⟩ := UpperTheory.V.CA.cpl_is D (RingHom.ker φ.toRingHom)
    exact ⟨_, _, hloc, _, hc⟩
  obtain ⟨R, _, _, _, hc⟩ := key
  letI : Algebra O R := ((algebraMap D R).comp (algebraMap O D)).toAlgebra
  haveI : IsScalarTower O D R := IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨hco, h1, h2⟩ := cpl_univ O D R φ hc
  exact ⟨R, _, _, hco, IsScalarTower.toAlgHom O D R, h1, h2⟩

private theorem res_fin (O B A : Type) [CommRing O] [IsLocalRing O] [Finite (ResidueField O)] [CommRing B] [Algebra O B]
    [IsCO O B] [CommRing A] [Algebra B A] [Algebra.FiniteType B A] (x : Ideal A) [x.IsMaximal]
    (hx : maximalIdeal B ≤ x.comap (algebraMap B A)) : Finite (A ⧸ x) := by
  letI := Ideal.Quotient.field x
  haveI : Finite (ResidueField B) := Finite.of_surjective _ (resMap_bijective O B).2
  letI : Algebra (ResidueField B) (A ⧸ x) := (Ideal.Quotient.lift (maximalIdeal B) (algebraMap B (A ⧸ x))
    fun a ha => Ideal.Quotient.eq_zero_iff_mem.2 (hx ha)).toAlgebra
  haveI : IsScalarTower B (ResidueField B) (A ⧸ x) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Algebra.FiniteType (ResidueField B) (A ⧸ x) := Algebra.FiniteType.of_restrictScalars_finiteType B _ _
  haveI : Module.Finite (ResidueField B) (A ⧸ x) := finite_of_finite_type_of_isJacobsonRing _ _
  exact Module.finite_of_finite (ResidueField B)

theorem UpperTheory.V.Fr.loc_ex :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ S : Space O F n, ∀ x : Ideal S.A, x.IsMaximal → S.mB ≤ S.π x → Nonempty (S.Loc x) := by
  intro l _ O _ _ _ _ F C₀ n hF hn S x hx hB
  have hA : IsNoetherianRing S.A := (gr_A hF hn S).2.2.2.2.2.1
  have hT : Algebra.FiniteType S.B S.A := (gr_A hF hn S).2.2.2.2.1
  obtain ⟨hco, hm⟩ := UpperTheory.V.Fr.co_B hF hn S
  rw [← hm] at hB
  haveI : Finite (S.A ⧸ x) := res_fin O S.B S.A x hB
  letI := Ideal.Quotient.field x
  obtain ⟨O', _, _, _, _, _, _, hu, ⟨e⟩⟩ := unr_ex (l := l) O (S.A ⧸ x) fun a ha => by
    have h1 : algebraMap O S.B a ∈ maximalIdeal S.B := fun h => ha (IsLocalHom.map_nonunit a h)
    exact Ideal.Quotient.eq_zero_iff_mem.2 (hB h1)
  have hD : IsNoetherianRing (TensorProduct O O' S.A) := by
    have h1 : IsNoetherianRing (TensorProduct O S.A O') :=
      Algebra.FiniteType.isNoetherianRing S.A _
    exact isNoetherianRing_of_ringEquiv _ (Algebra.TensorProduct.comm O S.A O').toRingEquiv
  let φ : TensorProduct O O' S.A →ₐ[O'] ResidueField O' :=
    Algebra.TensorProduct.lift (Algebra.ofId _ _) (e.comp (Ideal.Quotient.mkₐ O x)) fun _ _ => Commute.all _ _
  obtain ⟨R, _, _, _, j, h1, h2⟩ := cpl_ex O' _ φ
  letI : Algebra O R := ((algebraMap O' R).comp (algebraMap O O')).toAlgebra
  haveI : IsScalarTower O O' R := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hφ : ∀ a : S.A, φ (1 ⊗ₜ a) = e (Ideal.Quotient.mk x a) := fun a => by simp [φ]
  refine ⟨{
    O' := O'
    unr := hu
    R := R
    ι := (j.restrictScalars O).comp Algebra.TensorProduct.includeRight
    lies := ?_
    univ := fun C _ _ _ _ _ f hf => ?_ }⟩
  · ext a
    rw [Ideal.mem_comap, ← res_eq_zero_iff O', ← Ideal.Quotient.eq_zero_iff_mem,
      ← map_eq_zero_iff e e.toRingHom.injective, ← hφ, ← h1]
    rfl
  · let f' : TensorProduct O O' S.A →ₐ[O'] C :=
      Algebra.TensorProduct.lift (Algebra.ofId _ _) f fun _ _ => Commute.all _ _
    have hf' : ∀ a : S.A, f' (1 ⊗ₜ a) = f a := fun a => by simp [f']
    have e1 : (res O' C).comp f' = φ := Algebra.TensorProduct.ext (by ext) (by
      ext a
      show res O' C (f' (1 ⊗ₜ a)) = φ (1 ⊗ₜ a)
      rw [hf', hf, ← h1]; rfl)
    obtain ⟨g, hg, hu⟩ := h2 C f' fun a => DFunLike.congr_fun e1 a
    refine ⟨g, fun a => (hg _).trans (hf' a), fun g' hg' => hu g' fun a => ?_⟩
    have e2 : g'.comp j = f' := Algebra.TensorProduct.ext (by ext) (by
      ext a
      show g' (j (1 ⊗ₜ a)) = f' (1 ⊗ₜ a)
      rw [hf']; exact hg' a)
    exact DFunLike.congr_fun e2 a
end
