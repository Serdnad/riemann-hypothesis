module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle449
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle448
public import Mathlib.RingTheory.Ideal.Height
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle437
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle434
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle435
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle436
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle487
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle011
import Mathlib.Algebra.Module.StablyFree.Basic
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
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
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory.PD

theorem projective_exteriorPower_of_projective (R V : Type) [CommRing R] [AddCommGroup V] [Module R V]
    [Module.Projective R V] (n : ℕ) : Module.Projective R (⋀[R]^n V) := by
  obtain ⟨s, hs⟩ := Module.projective_def'.1 (inferInstance : Module.Projective R V)
  haveI : Module.Free R (⋀[R]^n (V →₀ R)) := exteriorPower.instFree R n
  refine Module.Projective.of_split (exteriorPower.map n s)
    (exteriorPower.map n (Finsupp.linearCombination R id)) ?_
  rw [← exteriorPower.map_comp, hs, exteriorPower.map_id]

theorem span_omB_comap_finite_projective : ∀ (k K : Type) [Field k] [Field K] [Algebra k K] (B : Subalgebra k K) [IsFractionRing B K] [Algebra.Smooth k B] (p : ℕ) (W : Type) [AddCommGroup W] [Module K W] [Module k W] [IsScalarTower k K W] (e : W →ₗ[K] DR k K), Function.Injective e → LinearMap.range e = ⋀[K]^p Ω[K⁄k] → Module.Finite B (Submodule.span B ((omB k K B p).comap (e.restrictScalars k) : Set W)) ∧ Module.Projective B (Submodule.span B ((omB k K B p).comap (e.restrictScalars k) : Set W)) := by
  intro k K _ _ _ B _ _ p W _ _ _ _ e he hr
  obtain ⟨e', he', hre', -⟩ := GlobalTheory.T.kahlerFormsOverSubalgebra_eq_range_exteriorPower k K B p
  have hom := fun a ha => ((GlobalTheory.T.kahlerFormsOverSubalgebra_closure_properties k K B p p).2.1 a ha)
  let S : Submodule k W := (omB k K B p).comap (e.restrictScalars k)
  let T : Submodule B W :=
    { carrier := (S : Set W)
      add_mem' := S.add_mem
      zero_mem' := S.zero_mem
      smul_mem' := fun c w hw => by
        change e ((c : K) • w) ∈ omB k K B p
        rw [map_smul]
        exact (hom _ hw).2.2.2 c c.2 }
  have hST : Submodule.span B (S : Set W) = T := Submodule.span_eq T
  change Module.Finite B (Submodule.span B (S : Set W)) ∧ Module.Projective B (Submodule.span B (S : Set W))
  rw [hST]
  let g : T →ₗ[B] DR k K :=
    { toFun := fun w => e w
      map_add' := fun w w' => by simp
      map_smul' := fun c w => by
        change e ((c : K) • (w : W)) = (c : K) • e w
        exact e.map_smul (c : K) w }
  have hg : Function.Injective g := fun w w' h => Subtype.ext (he h)
  have hrg : LinearMap.range g = LinearMap.range e' := by
    ext y
    constructor
    · rintro ⟨w, rfl⟩
      obtain ⟨z, hz⟩ := (hre' _).1 w.2
      exact ⟨z, hz⟩
    · rintro ⟨z, rfl⟩
      have hy : e' z ∈ omB k K B p := (hre' _).2 ⟨z, rfl⟩
      have hy' : e' z ∈ LinearMap.range e := by rw [hr]; exact (hom _ hy).2.2.1
      obtain ⟨w, hw⟩ := hy'
      have hwT : w ∈ T := by
        change e w ∈ omB k K B p
        rw [hw]; exact hy
      exact ⟨⟨w, hwT⟩, hw⟩
  let E : T ≃ₗ[B] ⋀[B]^p Ω[B⁄k] :=
    (LinearEquiv.ofInjective g hg).trans ((LinearEquiv.ofEq _ _ hrg).trans (LinearEquiv.ofInjective e' he').symm)
  haveI : Module.Projective B (⋀[B]^p Ω[B⁄k]) := projective_exteriorPower_of_projective B _ p
  exact ⟨Module.Finite.equiv E.symm, Module.Projective.of_equiv E.symm⟩

end GlobalTheory.PD
end

section

set_option autoImplicit false

noncomputable section

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory.PD

theorem omB_top_coeff_iff_pole : ∀ (k F K : Type) [Field k] [CharZero k] [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] [FiniteDimensional F K] (d : ℕ) (u : Fin d → F), AlgebraicIndependent k u → ∀ (A : Subalgebra k F) [IsFractionRing A F], A = Algebra.adjoin k (Set.range u) → ∀ (B : Subalgebra k K), B = (integralClosure A K).restrictScalars k → Algebra.Smooth k B → ∀ τ : DR k K →ₗ[K] K, τ (ExteriorAlgebra.ιMulti K d fun j => D k K (algebraMap F K (u j))) = 1 → ∀ (Q : Ideal B), Q.IsPrime → Q.height = 1 → ∀ (t : A) (s : B) (e : ℕ), Irreducible t → 1 ≤ e → s ∈ Q → (∀ y ∈ Q, ∃ c r : B, r ∉ Q ∧ r * y = c * s) → (∃ a r : B, a ∉ Q ∧ r ∉ Q ∧ (r : K) * algebraMap F K t = a * s ^ e) → ∀ z : K, (∃ r : B, r ∉ Q ∧ ∃ y ∈ omB k K B d, τ y = r * z) ↔ ∃ c r : B, r ∉ Q ∧ (r : K) * s ^ (e - 1) * z = c := by
  intro k F K _ _ _ _ _ _ _ _ _ d u hu A _ hA B hB _ τ hτ Q hQ hQh t s e ht he hsQ hQs hts z
  obtain ⟨a₀, r₀, ha₀, hr₀, hrt⟩ := hts
  have htQ : ∀ b : B, (b : K) = algebraMap F K t → b ∈ Q := by
    intro b hb
    have h1 : r₀ * b = a₀ * s ^ e := Subtype.ext (by push_cast; rw [hb]; exact hrt)
    have h2 : r₀ * b ∈ Q := h1 ▸ Q.mul_mem_left _ (Q.pow_mem_of_mem hsQ e (by omega))
    exact (hQ.mem_or_mem h2).resolve_left hr₀
  have hcomap := GlobalTheory.T.mem_heightOne_prime_integralClosure_iff_dvd_irreducible k F K d u hu A hA B hB Q hQ hQh t ht htQ
  obtain ⟨htp, m, rfl, y, hy⟩ := GlobalTheory.T.polynomial_ring_irreducible_prime_reduction k F d u hu A hA t ht
  have hAft : Algebra.FiniteType k A := by
    subst hA
    classical
    exact (Subalgebra.fg_iff_finiteType _).1 ⟨Finset.univ.image u, by simp⟩
  have ht0 : t ≠ 0 := ht.ne_zero
  have hP : (Ideal.span {t}).IsPrime := (Ideal.span_singleton_prime ht0).2 htp
  have genA := GlobalTheory.T.exists_not_mem_smul_D_eq_sum k F K A (Ideal.span {t}) hP t (Ideal.mem_span_singleton_self t) ht0
    (fun y hy => by
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hy
      exact ⟨c, 1, (Ideal.ne_top_iff_one _).1 hP.ne_top, by ring⟩) m y hy

  have memB : ∀ a : A, algebraMap F K (a : F) ∈ B := fun a => by
    rw [hB]; exact (Subalgebra.mem_restrictScalars k).2 ((integralClosure A K).algebraMap_mem a)
  let ιB : A → B := fun a => ⟨algebraMap F K (a : F), memB a⟩
  have hιQ : ∀ a : A, ιB a ∈ Q ↔ a ∈ Ideal.span {t} := fun a => by
    rw [Ideal.mem_span_singleton]; exact hcomap a (ιB a) rfl
  set du : DR k K := ExteriorAlgebra.ιMulti K (m + 1) fun j => D k K (algebraMap F K (u j)) with hdu
  have hdu0 : du ≠ 0 := fun h => by rw [h, map_zero] at hτ; exact zero_ne_one hτ
  set gA : Fin (m + 1) → Ω[K⁄k] := Fin.cons (D k K (algebraMap F K (t : F))) (fun j => D k K (algebraMap F K (y j : F))) with hgA
  obtain ⟨rA, hrA, aA, hA1⟩ := GlobalTheory.T.exterior_wedge_eq_of_localized_span A K Ω[K⁄k] (Ideal.span {t}).primeCompl (m + 1) gA (fun j => D k K (algebraMap F K (u j))) (fun i => by
    obtain ⟨r, hr, c, hc⟩ := genA ⟨u i, hA ▸ Algebra.subset_adjoin (Set.mem_range_self i)⟩
    exact ⟨r, hr, c, hc⟩)
  obtain ⟨r', hr', c', hA2⟩ := GlobalTheory.T.exterior_wedge_eq_of_localized_span A K Ω[K⁄k] (Ideal.span {t}).primeCompl (m + 1) (fun j => D k K (algebraMap F K (u j))) gA (fun i => by
    have key : ∀ v : A, ∃ c : Fin (m + 1) → A, D k K (algebraMap F K (v : F)) = ∑ l, algebraMap A K (c l) • D k K (algebraMap F K (u l)) := by
      intro v
      obtain ⟨c, hc, hc'⟩ := GlobalTheory.T.exists_D_eq_sum_smul_D_of_mem_adjoin k F K (m + 1) u (v : F) (hA ▸ v.2)
      exact ⟨fun j => ⟨c j, hA ▸ hc j⟩, hc'⟩
    refine Fin.cases ?_ (fun j => ?_) i
    · obtain ⟨c, hc⟩ := key t
      exact ⟨1, Submonoid.one_mem _, c, by rw [map_one, one_smul]; exact hc⟩
    · obtain ⟨c, hc⟩ := key (y j)
      exact ⟨1, Submonoid.one_mem _, c, by rw [map_one, one_smul]; exact hc⟩)
  have hAeq : rA * r' = aA * c' := by
    apply FaithfulSMul.algebraMap_injective A K
    have h3 : (algebraMap A K (rA * r')) • du = (algebraMap A K (aA * c')) • du := by
      rw [map_mul, map_mul, mul_comm, mul_smul, hA1, smul_comm, hA2, smul_smul, mul_comm]
    exact smul_left_injective K hdu0 h3
  have haA : aA ∉ Ideal.span {t} := fun h => by
    have : rA * r' ∈ Ideal.span {t} := hAeq ▸ Ideal.mul_mem_right _ _ h
    rcases hP.mem_or_mem this with h4 | h4
    · exact hrA h4
    · exact hr' h4

  let y' : Fin m → B := fun j => ιB (y j)
  have hy' := GlobalTheory.T.isTranscendenceBasis_quotient_integralClosure' k F K A B hB Q hQ t hcomap m y hy y' (fun j => rfl)
  haveI := GlobalTheory.T.integralClosure_finiteType_over_adjoin k F K (m + 1) u hu A hA B hB
  have hs0 : s ≠ 0 := by
    rintro rfl
    have h5 : (r₀ : K) * algebraMap F K t = 0 := by rw [hrt]; simp [zero_pow (by omega : e ≠ 0)]
    rcases mul_eq_zero.1 h5 with h6 | h6
    · exact hr₀ (by rw [show r₀ = 0 from Subtype.ext h6]; exact Q.zero_mem)
    · exact ht0 (by
        have : (t : F) = 0 := (map_eq_zero_iff _ (algebraMap F K).injective).1 h6
        exact Subtype.ext this)
  have genB := GlobalTheory.T.exists_not_mem_smul_D_eq_sum k K K B Q hQ s hsQ hs0 hQs m y' hy'
  simp only [Algebra.algebraMap_self_apply] at genB
  obtain ⟨N, Dn, hN, hDn, hND⟩ := GlobalTheory.T.differential_relation_local_ring_bound k K B Q hQ s m (fun j => (y' j : K)) (algebraMap F K t) e he hsQ genB ⟨a₀, r₀, ha₀, hr₀, hrt⟩
  set ω : DR k K := ExteriorAlgebra.ιMulti K (m + 1) (Fin.cons (D k K (s : K)) (fun j => D k K (y' j : K)) : Fin (m + 1) → Ω[K⁄k]) with hω
  let Dt : B := Dn * ιB rA
  let Nt : B := N * ιB aA
  have hDt : Dt ∉ Q := fun h => (hQ.mem_or_mem h).elim hDn (fun h' => hrA ((hιQ rA).1 h'))
  have hNt : Nt ∉ Q := fun h => (hQ.mem_or_mem h).elim hN (fun h' => haA ((hιQ aA).1 h'))
  have hmain : (Dt : K) • du = ((Nt : K) * (s : K) ^ (e - 1)) • ω := by
    have h7 : (Dn : K) • ExteriorAlgebra.ιMulti K (m + 1) gA = ((N : K) * (s : K) ^ (e - 1)) • ω := hND
    have hA1' : (algebraMap F K (rA : F)) • du = (algebraMap F K (aA : F)) • ExteriorAlgebra.ιMulti K (m + 1) gA := hA1
    show ((Dn : K) * algebraMap F K (rA : F)) • du = ((N : K) * algebraMap F K (aA : F) * (s : K) ^ (e - 1)) • ω
    rw [mul_smul, hA1', smul_comm, h7, smul_smul]
    congr 1
    ring
  have hkey : (Dt : K) = (Nt : K) * (s : K) ^ (e - 1) * τ ω := by
    have := congrArg τ hmain
    rw [map_smul, map_smul, hτ, smul_eq_mul, smul_eq_mul, mul_one] at this
    rw [this]
  have hv0 : (Fin.cons (D k K (s : K)) (fun j => D k K (y' j : K)) : Fin (m + 1) → Ω[K⁄k]) = fun j => D k K ((Fin.cons (s : K) (fun j => (y' j : K)) : Fin (m + 1) → K) j) := by
    funext j; exact Fin.cases rfl (fun j => rfl) j
  have hωmem : ∀ b : B, (b : K) • ω ∈ omB k K B (m + 1) := fun b => by
    refine Submodule.subset_span ⟨b, b.2, Fin.cons (s : K) (fun j => (y' j : K)), fun j => Fin.cases s.2 (fun j => (y' j).2) j, ?_⟩
    rw [hω, hv0]
  have P : ∀ yy ∈ omB k K B (m + 1), ∃ c ρ : B, ρ ∉ Q ∧ (ρ : K) * (s : K) ^ (e - 1) * τ yy = c := by
      intro yy hyy
      unfold omB at hyy
      induction hyy using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨b, hb, v, hv, rfl⟩ := hx
        obtain ⟨ρ, hρ, β, hβ⟩ := GlobalTheory.T.exterior_wedge_eq_of_localized_span B K Ω[K⁄k] Q.primeCompl (m + 1) (Fin.cons (D k K (s : K)) (fun j => D k K (y' j : K))) (fun j => D k K (v j)) (fun i => genB ⟨v i, hv i⟩)
        have hβ' : (ρ : K) • ExteriorAlgebra.ιMulti K (m + 1) (fun j => D k K (v j)) = (β : K) • ω := hβ
        have h8 := congrArg τ hβ'
        rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul] at h8
        refine ⟨⟨b, hb⟩ * β * Dt, ρ * Nt, fun h => (hQ.mem_or_mem h).elim hρ hNt, ?_⟩
        rw [map_smul, smul_eq_mul]
        push_cast
        rw [hkey]
        linear_combination ((b : K) * (Nt : K) * (s : K) ^ (e - 1)) * h8
      | zero => exact ⟨0, 1, (Ideal.ne_top_iff_one _).1 hQ.ne_top, by simp⟩
      | add x w _ _ hx hw =>
        obtain ⟨c1, ρ1, h1, e1⟩ := hx
        obtain ⟨c2, ρ2, h2, e2⟩ := hw
        refine ⟨ρ2 * c1 + ρ1 * c2, ρ1 * ρ2, fun h => (hQ.mem_or_mem h).elim h1 h2, ?_⟩
        rw [map_add (f := _)]; push_cast
        linear_combination (ρ2 : K) * e1 + (ρ1 : K) * e2
      | smul a x _ hx =>
        obtain ⟨c, ρ, h1, e1⟩ := hx
        refine ⟨algebraMap k B a * c, ρ, h1, ?_⟩
        rw [τ.map_smul_of_tower, Algebra.smul_def]
        push_cast
        rw [← e1]
        ring
  constructor
  · rintro ⟨r, hr, yy, hyy, hτy⟩
    obtain ⟨c, ρ, hρ, hc⟩ := P yy hyy
    refine ⟨c, ρ * r, fun h => (hQ.mem_or_mem h).elim hρ hr, ?_⟩
    rw [← hc, hτy]; push_cast; ring
  · rintro ⟨c, r, hr, hc⟩
    refine ⟨Dt * r, fun h => (hQ.mem_or_mem h).elim hDt hr, ((c * Nt : B) : K) • ω, hωmem _, ?_⟩
    rw [map_smul, smul_eq_mul]
    push_cast
    rw [hkey]
    linear_combination (-((Nt : K) * τ ω)) * hc

end GlobalTheory.PD
end
end

section

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

noncomputable section
namespace GlobalTheory.KSp.ScBasic

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {E : Type} [Field E] [Algebra F E]

end GlobalTheory.KSp.ScBasic
end

namespace GlobalTheory.KSp

open MeasureTheory Matrix in
private theorem sc_units_eq_mul_nabs_norm_rpow {E : Type} [Field E] (F : Type) [Field F]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Algebra F E]
    (χ : Eˣ →* Circle) (m : ℕ) (z : Eˣ) :
    _root_.GlobalTheory.KSp.sc F χ m (z : E) = (χ z : ℂ) *
      ((_root_.GlobalTheory.SplitWeil.nabs F (Units.map (Algebra.norm F : E →* F) z) ^
        ((m : ℝ) / 2) : ℝ) : ℂ) := by
  simp [_root_.GlobalTheory.KSp.sc, z.ne_zero]

open MeasureTheory Matrix in
private theorem rpow_natCast_div_two_sq {x : ℝ} (hx : 0 < x) (m : ℕ) :
    (x ^ ((m : ℝ) / 2)) ^ 2 = x ^ m := by
  rw [← Real.rpow_natCast (x ^ ((m : ℝ) / 2)) 2, ← Real.rpow_mul hx.le, ← Real.rpow_natCast x m]
  congr 1
  push_cast
  ring

open MeasureTheory Matrix in
private theorem sc_zero' {E : Type} [Field E] (F : Type) [Field F]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Algebra F E]
    (χ : Eˣ →* Circle) (m : ℕ) : _root_.GlobalTheory.KSp.sc F χ m 0 = 0 := by
  simp [_root_.GlobalTheory.KSp.sc]

open MeasureTheory Matrix in
theorem _root_.GlobalTheory.KSp.sc_basic : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : _root_.GlobalTheory.WeilM.IsQuad c δ) (m : ℕ) (χ : Eˣ →* Circle) (_ : _root_.GlobalTheory.WeilM.ResEtaPow (R := F) ⊥ χ m), _root_.GlobalTheory.KSp.sc F χ m 1 = 1 ∧ (∀ z z' : E, _root_.GlobalTheory.KSp.sc F χ m (z * z') = _root_.GlobalTheory.KSp.sc F χ m z * _root_.GlobalTheory.KSp.sc F χ m z') ∧ (∀ z : Eˣ, _root_.GlobalTheory.KSp.sc F χ m (z : E) = (χ z : ℂ) * ((_root_.GlobalTheory.SplitWeil.nabs F ((Units.map (Algebra.norm F : E →* F)) z) ^ ((m : ℝ) / 2) : ℝ) : ℂ)) ∧ (∀ z : Eˣ, ‖_root_.GlobalTheory.KSp.sc F χ m (z : E)‖ ^ 2 = _root_.GlobalTheory.SplitWeil.nabs F ((Units.map (Algebra.norm F : E →* F)) z) ^ m) ∧ (∀ z : Eˣ, _root_.GlobalTheory.KSp.sc F χ m (c (z : E))⁻¹ * ((_root_.GlobalTheory.SplitWeil.nabs F ((Units.map (Algebra.norm F : E →* F)) z) ^ m : ℝ) : ℂ) = _root_.GlobalTheory.KSp.sc F χ m (z : E)) ∧ (∀ t : Fˣ, _root_.GlobalTheory.KSp.sc F χ m (algebraMap F E t) = (_root_.GlobalTheory.KSp.sgn E t * (_root_.GlobalTheory.SplitWeil.nabs F t : ℝ)) ^ m) ∧ ∀ z : Eˣ, _root_.GlobalTheory.KSp.sc F χ m ((z : E) * c (z : E)) = ((_root_.GlobalTheory.SplitWeil.nabs F ((Units.map (Algebra.norm F : E →* F)) z) ^ m : ℝ) : ℂ) := by
  intro F _ _ _ _ _ E _ _ _ _ c δ hE m χ hχ
  haveI : Invertible (2 : F) := invertibleOfNonzero two_ne_zero
  have hinj := hE.algebraMap_injective
  have hinv := hE.invol
  have hpos : ∀ t : Fˣ, 0 < _root_.GlobalTheory.SplitWeil.nabs F t :=
    _root_.GlobalTheory.SplitWeil.nabs_pos F
  have hmul := _root_.GlobalTheory.SplitWeil.nabs_mul F
  have hunit : ∀ z : Eˣ, _root_.GlobalTheory.KSp.sc F χ m (z : E) = (χ z : ℂ) *
      ((_root_.GlobalTheory.SplitWeil.nabs F (Units.map (Algebra.norm F : E →* F) z) ^
        ((m : ℝ) / 2) : ℝ) : ℂ) := fun z => sc_units_eq_mul_nabs_norm_rpow F χ m z
  have hnorm : ∀ z : Eˣ, algebraMap F E ((Units.map (Algebra.norm F : E →* F) z : Fˣ) : F) =
      (z : E) * c z := fun z => by
    simpa using hE.algebraMap_norm (z : E)
  have hNc : ∀ z : Eˣ, Units.map (Algebra.norm F : E →* F) (Units.map (c : E →* E) z) =
      Units.map (Algebra.norm F : E →* F) z := by
    intro z
    apply Units.ext
    apply hinj
    rw [hnorm, hnorm]
    simp [hinv, mul_comm]
  have hNa : ∀ t : Fˣ, Units.map (Algebra.norm F : E →* F) (Units.map (algebraMap F E : F →* E) t)
      = t * t := by
    intro t
    apply Units.ext
    apply hinj
    rw [hnorm]
    simp
  have hbase : ∀ t : Fˣ, _root_.GlobalTheory.KSp.sc F χ m (algebraMap F E t) =
      (_root_.GlobalTheory.KSp.sgn E t * (_root_.GlobalTheory.SplitWeil.nabs F t : ℝ)) ^ m := by
    intro t
    have h1 := hunit (Units.map (algebraMap F E : F →* E) t)
    simp only [Units.coe_map, MonoidHom.coe_coe] at h1
    rw [h1, hχ t, hNa, hmul, Real.mul_rpow (hpos t).le (hpos t).le, ← sq,
      rpow_natCast_div_two_sq (hpos t) m, mul_pow]
    simp only [_root_.GlobalTheory.KSp.sgn, bot_sup_eq]
    split_ifs with h₁ h₂ h₂ <;>
      first
        | (push_cast; ring1)
        | exact absurd (Subgroup.mem_sup_right h₂) h₁
        | exact absurd (by rwa [bot_sup_eq] at h₁) h₂
  refine ⟨?_, ?_, hunit, ?_, ?_, hbase, ?_⟩
  · simpa [_root_.GlobalTheory.SplitWeil.nabs_one] using hunit 1
  · intro z z'
    rcases eq_or_ne z 0 with rfl | hz
    · simp [sc_zero']
    rcases eq_or_ne z' 0 with rfl | hz'
    · simp [sc_zero']
    obtain ⟨u, rfl⟩ : ∃ u : Eˣ, (u : E) = z := ⟨Units.mk0 z hz, rfl⟩
    obtain ⟨u', rfl⟩ : ∃ u : Eˣ, (u : E) = z' := ⟨Units.mk0 z' hz', rfl⟩
    rw [← Units.val_mul, hunit, hunit, hunit, map_mul, map_mul, hmul,
      Real.mul_rpow (hpos _).le (hpos _).le]
    push_cast [Circle.coe_mul]
    ring
  · intro z
    rw [hunit, norm_mul, Circle.norm_coe, one_mul, Complex.norm_real,
      Real.norm_of_nonneg (Real.rpow_nonneg (hpos _).le _), rpow_natCast_div_two_sq (hpos _) m]
  · intro z
    have h1 := hunit (Units.map (c : E →* E) z)⁻¹
    simp only [Units.val_inv_eq_inv_val, Units.coe_map, MonoidHom.coe_coe, map_inv] at h1
    have hs := hpos (Units.map (Algebra.norm F : E →* F) z)
    have habs_inv : ∀ t : Fˣ, _root_.GlobalTheory.SplitWeil.nabs F t⁻¹ =
        (_root_.GlobalTheory.SplitWeil.nabs F t)⁻¹ := fun t =>
      eq_inv_of_mul_eq_one_left (by rw [← hmul, inv_mul_cancel, _root_.GlobalTheory.SplitWeil.nabs_one])
    rw [h1, hNc, hunit,
      _root_.GlobalTheory.WeilM.ResEtaPow.map_conj (c := c) hE hχ z, inv_inv,
      habs_inv, Real.inv_rpow hs.le, ← rpow_natCast_div_two_sq hs m]
    have ha0 : ((_root_.GlobalTheory.SplitWeil.nabs F (Units.map (Algebra.norm F : E →* F) z) ^
        ((m : ℝ) / 2) : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.rpow_pos_of_pos hs _).ne'
    push_cast at ha0 ⊢
    field_simp
  · intro z
    have hz : Units.map (Algebra.norm F : E →* F) z ∈ (Units.map (Algebra.norm F : E →* F)).range :=
      ⟨z, rfl⟩
    rw [← hnorm, hbase]
    simp [_root_.GlobalTheory.KSp.sgn, hz]

end GlobalTheory.KSp
end

section

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

noncomputable section
namespace GlobalTheory.KSp

section PairAlg

variable {F : Type} [Field F] {E : Type} [Field E] [Algebra F E] (c : E →ₐ[F] E)
  {α ν : Type} [Fintype α] [DecidableEq α] [Fintype ν] [DecidableEq ν]

theorem pr_eq_trace (Q : Matrix α α E) (x y : Matrix α ν E) :
    pr c Q x y = 2⁻¹ * Algebra.trace F E (Matrix.trace (Qᵀ * (x * (y.map c)ᵀ))) := by
  have h : fromCols x (0 : Matrix α ν E) * stdJ ν E * ((fromCols (0 : Matrix α ν E) y).map c)ᵀ = x * (y.map c)ᵀ := by
    ext i k
    simp [stdJ, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]
  rw [pr, form, hTens_eq, h]
  congr 2
  simp only [Matrix.trace, diag, Matrix.mul_apply, transpose_apply]
  rw [Finset.sum_comm]

theorem trace_single_pair (Q : Matrix α α E) (y : Matrix α ν E) (i : α) (j : ν) (z : E) :
    Matrix.trace (Qᵀ * (Matrix.single i j z * (y.map c)ᵀ)) = z * (Q * y.map c) i j := by
  simp [Matrix.trace, Matrix.mul_apply, Matrix.single_apply, Finset.mul_sum, ite_and]
  refine Finset.sum_congr rfl fun _ _ => by ring

def prLin (Q : Matrix α α E) : Matrix α ν E →ₗ[F] Matrix α ν E →ₗ[F] F :=
  LinearMap.mk₂ F (fun x y => 2⁻¹ * Algebra.trace F E (Matrix.trace (Qᵀ * (x * (y.map c)ᵀ))))
    (fun x x' y => by simp [Matrix.add_mul, Matrix.mul_add, mul_add])
    (fun t x y => by simp [Matrix.smul_mul, Matrix.mul_smul, mul_left_comm])
    (fun x y y' => by
      rw [show (y + y').map c = y.map c + y'.map c from Matrix.map_add _ (map_add c) _ _]
      simp [Matrix.add_mul, Matrix.mul_add, mul_add])
    (fun t x y => by
      rw [show (t • y).map c = t • y.map c from by ext i j; simp [map_smul]]
      simp [Matrix.smul_mul, Matrix.mul_smul, mul_left_comm])

end PairAlg

end GlobalTheory.KSp

namespace GlobalTheory.KSp

theorem pr_alg : ∀ (F : Type) [Field F] [CharZero F] (E : Type) [Field E] [Algebra F E] (c : E →ₐ[F] E) (δ : E)
    (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν]
    (Q : Matrix α α E) (_ : IsHerm c Q), ∃ β : Matrix α ν E →ₗ[F] Matrix α ν E →ₗ[F] F,
      (∀ x y, β x y = pr c Q x y) ∧ (∀ x y, β x y = β y x) ∧ (∀ y, (∀ x, β x y = 0) → y = 0) ∧
      (∀ (x y : Matrix α ν E) (a : Matrix ν ν E), β (x * a) y = β x (y * (a.map c)ᵀ)) ∧
      ∀ x y, β x y = 2⁻¹ * Algebra.trace F E (Matrix.trace (Qᵀ * (x * (y.map c)ᵀ))) := by
  intro F _ _ E _ _ c δ hE α _ _ ν _ _ Q hQ
  have hc : ∀ z, c (c z) = z := hE.invol
  have ht : ∀ z, Algebra.trace F E (c z) = Algebra.trace F E z := fun z =>
    Algebra.trace_eq_of_algEquiv (AlgEquiv.ofAlgHom c c (AlgHom.ext hc) (AlgHom.ext hc)) z
  have hap : ∀ x y : Matrix α ν E, prLin c Q x y = 2⁻¹ * Algebra.trace F E (Matrix.trace (Qᵀ * (x * (y.map c)ᵀ))) :=
    fun _ _ => rfl
  refine ⟨prLin c Q, fun x y => by rw [hap, pr_eq_trace], fun x y => ?_, fun y hy => ?_, fun x y a => ?_, hap⟩
  ·
    have h : Matrix.trace (Qᵀ * (y * (x.map c)ᵀ)) = c (Matrix.trace (Qᵀ * (x * (y.map c)ᵀ))) := by

      simp only [Matrix.trace, diag, Matrix.mul_apply, transpose_apply, map_apply, map_sum, map_mul, hc, hQ.1]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
      exact congrArg _ (Finset.sum_congr rfl fun j _ => mul_comm _ _)
    rw [hap, hap, h, ht]
  ·
    obtain ⟨bE, -, -⟩ := hE.basis
    haveI : Module.Finite F E := Module.Finite.of_basis bE
    have htr : Algebra.trace F E 1 ≠ 0 := by
      rw [← map_one (algebraMap F E), Algebra.trace_algebraMap, nsmul_eq_mul, mul_one]
      exact Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
    have hw : Q * y.map c = 0 := by
      ext i j
      by_contra hij
      apply htr
      have := hy (Matrix.single i j ((Q * y.map c) i j)⁻¹)
      rw [hap, trace_single_pair, inv_mul_cancel₀ hij] at this
      simpa using this
    have hy0 : y.map c = 0 := by
      have := congrArg (fun m => Q⁻¹ * m) hw
      simpa [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hQ.2] using this
    ext i j
    exact c.toRingHom.injective (by simpa using congrFun (congrFun hy0 i) j)
  ·
    have h : ((y * (a.map c)ᵀ).map c)ᵀ = a * (y.map c)ᵀ := by
      ext i j

      simp [Matrix.mul_apply, map_sum, hc, mul_comm]
    rw [hap, hap, h, Matrix.mul_assoc]

end GlobalTheory.KSp
end
end
