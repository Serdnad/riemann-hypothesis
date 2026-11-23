module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle854
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle182
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle221
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle595
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle222
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle859
public import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
public import Formalism.GradedWeylDivisibility.FinalC
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle865
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Formalism.LocalToGlobal.Divisibility.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle872
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle004
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct
open IsLocalRing
universe u

namespace GlobalTheory

theorem eqLift_tensorModOf : ∀ {C : Type} [CommRing C] (I : Ideal C) {A : Type} [CommRing A] {H : Type u} [AddCommGroup H] [Module C H]
  (σ : A →+* Module.End C H), (letI := GlobalTheory.HTSummand.tensorModOf σ; Module.Projective (C ⊗[ℤ] A) H) →
  ∀ (χ : A →+* C) (l₀ : H →ₗ[C] C ⧸ I), (∀ a x, l₀ (σ a x) = Ideal.Quotient.mk I (χ a) * l₀ x) →
  ∃ l : H →ₗ[C] C, (∀ a x, l (σ a x) = χ a * l x) ∧ ∀ x, Ideal.Quotient.mk I (l x) = l₀ x := by
  intro C _ I A _ H _ _ σ hproj χ l₀ hl₀
  letI mH : Module (C ⊗[ℤ] A) H := GlobalTheory.HTSummand.tensorModOf σ
  let χt : C ⊗[ℤ] A →ₐ[ℤ] C := Algebra.TensorProduct.productMap (AlgHom.id ℤ C) χ.toIntAlgHom
  have hχt : ∀ (r : C) (a : A), χt (r ⊗ₜ[ℤ] a) = r * χ a := fun r a => by
    simp [χt, Algebra.TensorProduct.productMap_apply_tmul]
  obtain ⟨s, hs⟩ := Module.projective_def'.mp hproj
  have hsx : ∀ x, (s x).sum (fun y c => c • y) = x := by
    intro x
    have := LinearMap.congr_fun hs x
    simpa [Finsupp.linearCombination_apply] using this
  let g : H → C := fun y => Function.surjInv Ideal.Quotient.mk_surjective (l₀ y)
  have hg : ∀ y, Ideal.Quotient.mk I (g y) = l₀ y := fun y =>
    Function.surjInv_eq Ideal.Quotient.mk_surjective (l₀ y)
  let F : H → C := fun x => (s x).sum (fun y c => χt c * g y)
  have hadd : ∀ x x', F (x + x') = F x + F x' := by
    intro x x'
    simp only [F, map_add (f := _)]
    exact Finsupp.sum_add_index' (by simp) (by intros; simp [add_mul])
  have hS : ∀ (t : C ⊗[ℤ] A) x, F (t • x) = χt t * F x := by
    intro t x
    simp only [F, map_smul]
    rw [Finsupp.sum_smul_index (by simp), Finsupp.mul_sum]
    simp [_root_.mul_assoc]
  have hr : ∀ (r : C) (x : H), r • x = ((r ⊗ₜ[ℤ] (1 : A) : C ⊗[ℤ] A) • x) := by
    intro r x
    rw [GlobalTheory.HTSummand.tensorModOf_tmul, map_one]
    rfl
  have ha : ∀ (a : A) (x : H), σ a x = ((1 ⊗ₜ[ℤ] a : C ⊗[ℤ] A) • x) := by
    intro a x
    rw [GlobalTheory.HTSummand.tensorModOf_tmul, one_smul]
  let l : H →ₗ[C] C :=
    { toFun := F
      map_add' := hadd
      map_smul' := by
        intro r x
        show F (r • x) = r * F x
        rw [hr, hS, hχt, map_one, _root_.mul_one] }
  have hl₀t : ∀ (t : C ⊗[ℤ] A) y, l₀ (t • y) = Ideal.Quotient.mk I (χt t) * l₀ y := by
    intro t y
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul r a =>
      rw [GlobalTheory.HTSummand.tensorModOf_tmul, l₀.map_smul, hl₀, hχt, map_mul, Algebra.smul_def,
        Ideal.Quotient.algebraMap_eq, _root_.mul_assoc]
    | add t t' h h' => rw [add_smul, map_add (f := _), h, h', map_add (f := _), map_add (f := _), add_mul]
  refine ⟨l, ?_, ?_⟩
  · intro a x
    show F (σ a x) = χ a * F x
    rw [ha, hS, hχt, _root_.one_mul]
  · intro x
    show Ideal.Quotient.mk I (F x) = l₀ x
    conv_rhs => rw [← hsx x]
    simp only [F, map_finsuppSum, map_mul, hg, hl₀t]

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct

set_option autoImplicit false

namespace GlobalTheory.HTSummand

theorem liftSummand_residueCharZero : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (C : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] (I : Ideal C), I ^ 2 = ⊥ → IsUnit (p : C) → ∀ (tR : R →+* C) (H : Type 1) [AddCommGroup H] [Module C H] [Module.Finite C H] [Module.Projective C H] (ρ : D.O →+* Module.End C H), (letI := GlobalTheory.HTSummand.tensorModOf (ρ.comp (algebraMap (𝓞 D.F) D.O)); Module.Projective (C ⊗[ℤ] 𝓞 D.F) H) → ∀ (e : Module.End C H), e * e = e → (∀ c, ρ c * e = e * ρ c) → (∀ x, ρ (algebraMap (𝓞 D.F) D.O D.ω) (e x) = tR b.ρ • e x) → ∀ (F : Submodule C H), I • ⊤ ≤ F → (∀ (c : D.O), ∀ x ∈ F, ρ c x ∈ F) → (∀ x ∈ F, e x ∈ F) → (∃ E' M : Submodule C H, IsCompl E' M ∧ E' ⊔ I • ⊤ = F) → (∀ d ∈ LinearMap.range e, ∃ w : Fin D.a → H, (∀ i (c : 𝓞 D.F), ρ (algebraMap (𝓞 D.F) D.O c) (w i) - tR (b.t i c) • w i ∈ F) ∧ d - ∑ i, w i ∈ F) → ∃ G M : Submodule C H, G ⊓ M = ⊥ ∧ G ⊔ M = LinearMap.range e ∧ (∀ (c : D.O), ∀ x ∈ G, ρ c x ∈ G) ∧ G ⊔ (I • ⊤ ⊓ LinearMap.range e) = F ⊓ LinearMap.range e ∧ ∀ d ∈ LinearMap.range e, ∃ w : Fin D.a → H, (∀ i (c : 𝓞 D.F), ρ (algebraMap (𝓞 D.F) D.O c) (w i) - tR (b.t i c) • w i ∈ G) ∧ d - ∑ i, w i ∈ G := by

  intro p _ D R _ b C _ _ _ I hI hp tR H _ _ _ _ ρ _ e he heρ hω F hIF hFO heF hE' hLie
  have hunitN : ∀ n : ℕ, n ≠ 0 → IsUnit (n : C) := by
    intro n hn
    obtain ⟨k, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn p (Fact.out : p.Prime).one_lt.ne'
    have hcop : m.Coprime p := Nat.coprime_comm.mp (((Fact.out : p.Prime).coprime_iff_not_dvd).2 hm)
    have h2 : IsUnit (tR (m : R)) := (b.unit m hcop).map tR
    rw [map_natCast] at h2
    push_cast
    exact (hp.pow k).mul h2
  have hunitZ : ∀ N : ℤ, N ≠ 0 → IsUnit (N : C) := by
    intro N hN
    obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg N
    · exact_mod_cast hunitN n (by rintro rfl; simp at hN)
    · push_cast; exact (hunitN n (by rintro rfl; simp at hN)).neg
  obtain ⟨NF, kF, u, v, hNF, huv, hcomF⟩ := GlobalTheory.T.exists_separability_element_of_trace_nondegenerate' (𝓞 D.F) (GlobalTheory.T.ringOfIntegers_eq_zero_of_trace_mulLeft_eq_zero D.F)
  haveI := D.freeO; haveI := D.finO
  obtain ⟨NO, kO, x, y, hNO, hxy, hcomO⟩ := GlobalTheory.T.exists_separability_element_of_trace_nondegenerate' D.O (GlobalTheory.T.harrisTaylorOrder_traceForm_nondegenerate p D)
  obtain ⟨φ, hφc, hφφ, hφcomm, hφF, hφmod⟩ := GlobalTheory.T.exists_orthogonal_eigen_idempotents_of_separability R C (𝓞 D.F) tR D.a b.t b.comax NF kF u v huv hcomF
    (hunitZ NF hNF) H (ρ.comp (algebraMap (𝓞 D.F) D.O))
  have hFO' : ∀ c, ∀ z ∈ F, (ρ.comp (algebraMap (𝓞 D.F) D.O)) c z ∈ F := fun c z hz => hFO _ z hz
  set f : Module.End C H := ∑ i, φ i with hfdef
  have hfapp : ∀ z, f z = ∑ i, φ i z := fun z => by rw [hfdef, LinearMap.sum_apply]
  have hf : f * f = f := by
    rw [hfdef, Finset.sum_mul_sum]
    simp only [hφφ]
    exact Finset.sum_congr rfl fun i _ => by simp
  have hcommF : ∀ g : Module.End C H, (∀ c : 𝓞 D.F, g * ρ (algebraMap _ D.O c) = ρ (algebraMap _ D.O c) * g) → g * f = f * g := by
    intro g hg
    have hg' : ∀ c, g * (ρ.comp (algebraMap (𝓞 D.F) D.O)) c = (ρ.comp (algebraMap (𝓞 D.F) D.O)) c * g :=
      fun c => hg _
    rw [hfdef, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => hφcomm g hg' i
  have hef : e * f = f * e := hcommF e fun c => (heρ _).symm
  have hρf : ∀ c : D.O, ρ c * f = f * ρ c := fun c => hcommF (ρ c) fun c' => by
    rw [← map_mul, ← map_mul, Algebra.commutes]
  have hfF : ∀ z ∈ F, f z ∈ F := fun z hz => by
    rw [hfapp]; exact Submodule.sum_mem F fun i _ => hφF F hFO' i z hz
  set ε : Module.End C H := f * e with hεdef
  have hεapp : ∀ z, ε z = f (e z) := fun z => rfl
  have hε : ε * ε = ε := by
    calc f * e * (f * e) = f * ((e * f) * e) := by simp only [_root_.mul_assoc]
      _ = f * ((f * e) * e) := by rw [hef]
      _ = (f * f) * (e * e) := by simp only [_root_.mul_assoc]
      _ = f * e := by rw [hf, he]
  have hρε : ∀ c, ρ c * ε = ε * ρ c := fun c => by
    calc ρ c * (f * e) = (ρ c * f) * e := by rw [_root_.mul_assoc]
      _ = f * (ρ c * e) := by rw [hρf, _root_.mul_assoc]
      _ = f * e * ρ c := by rw [heρ, _root_.mul_assoc]
  have hFε : ∀ z ∈ F, ε z ∈ F := fun z hz => hfF _ (heF z hz)
  obtain ⟨π, hππ, hπρ, hπε, hεπ, hA, hB⟩ := GlobalTheory.T.exists_idempotent_separability_average C D.O I hI NO kO x y hxy hcomO (hunitZ NO hNO) H ρ ε hε hρε
    F hIF hFO hFε hE'
  have hεε : ∀ z, ε (ε z) = ε z := fun z => LinearMap.congr_fun hε z
  have hπε' : ∀ z, π (ε z) = π z := fun z => LinearMap.congr_fun hπε z
  have hεπ' : ∀ z, ε (π z) = π z := fun z => LinearMap.congr_fun hεπ z
  have hππ' : ∀ z, π (π z) = π z := fun z => LinearMap.congr_fun hππ z
  have hfπ : ∀ z, f (π z) = π z := fun z => by
    rw [← hεπ' z, hεapp, ← hεapp]
    have := LinearMap.congr_fun hf (e (π z))
    simp only [Module.End.mul_apply] at this
    rw [hεapp, this]
  have hπP : ∀ z, π z ∈ LinearMap.range e := fun z => ⟨f (π z), by
    have := LinearMap.congr_fun hef (π z)
    simp only [Module.End.mul_apply] at this
    exact this.trans (hεπ' z)⟩
  have heP : ∀ d ∈ LinearMap.range e, e d = d := by
    rintro d ⟨z, rfl⟩
    exact LinearMap.congr_fun he z
  have hfP : ∀ d ∈ LinearMap.range e, d - f d ∈ F := by
    intro d hd
    obtain ⟨w, hw1, hw2⟩ := hLie d hd
    have hfw : ∀ i, f (w i) - w i ∈ F := by
      intro i
      have hs := Submodule.sum_mem F fun j (_ : j ∈ Finset.univ) => hφmod F hFO' i (w i) (hw1 i) j
      rw [Finset.sum_sub_distrib, Finset.sum_ite_eq'] at hs
      simpa [hfapp] using hs
    have key : d - f d = (d - ∑ i, w i) - f (d - ∑ i, w i) - ∑ i, (f (w i) - w i) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sub, map_sum, Finset.sum_sub_distrib]; abel
    rw [key]
    exact F.sub_mem (F.sub_mem hw2 (hfF _ hw2)) (Submodule.sum_mem F fun i _ => hfw i)
  have hGmem : ∀ d ∈ LinearMap.range e, d - π d ∈ LinearMap.range e ⊓ LinearMap.ker π := fun d hd =>
    ⟨Submodule.sub_mem _ hd (hπP d), by simp [hππ']⟩
  refine ⟨LinearMap.range e ⊓ LinearMap.ker π, LinearMap.range π, ?_, ?_, ?_, ?_, ?_⟩
  · rw [eq_bot_iff]
    intro z hz
    obtain ⟨⟨-, hz1⟩, ⟨w, rfl⟩⟩ := hz
    replace hz1 : π (π w) = 0 := hz1
    rw [Submodule.mem_bot, ← hππ' w]; exact hz1
  · apply le_antisymm
    · exact sup_le inf_le_left (by rintro _ ⟨z, rfl⟩; exact hπP z)
    · intro d hd
      exact Submodule.mem_sup.2 ⟨d - π d, hGmem d hd, π d, ⟨d, rfl⟩, sub_add_cancel d (π d)⟩
  · rintro c z ⟨⟨w, rfl⟩, hz⟩
    refine Submodule.mem_inf.2 ⟨LinearMap.mem_range.2 ⟨ρ c w, ?_⟩, ?_⟩
    · have := LinearMap.congr_fun (heρ c) w
      simp only [Module.End.mul_apply] at this
      exact this.symm
    · replace hz : π (e w) = 0 := hz
      show π (ρ c (e w)) = 0
      have := LinearMap.congr_fun (hπρ c) (e w)
      simp only [Module.End.mul_apply] at this
      rw [← this, hz, map_zero]
  · apply le_antisymm
    · refine sup_le ?_ (inf_le_inf_right _ hIF)
      rintro z ⟨hzP, hz⟩
      replace hz : π z = 0 := hz
      refine Submodule.mem_inf.2 ⟨?_, hzP⟩
      have h1 := hfP z hzP
      have h2 := hA (ε z) (hεε z)
      rw [hπε', hz, sub_zero] at h2
      have : z = (z - f z) + ε z := by rw [hεapp, heP z hzP]; abel
      rw [this]; exact F.add_mem h1 h2
    · rintro z ⟨hzF, hzP⟩
      refine Submodule.mem_sup.2 ⟨z - π z, hGmem z hzP, π z, Submodule.mem_inf.2 ⟨?_, hπP z⟩, sub_add_cancel z (π z)⟩
      rw [← hπε']; exact hB (ε z) (hFε z hzF) (hεε z)
  · intro d hd
    refine ⟨fun i => φ i (π d), fun i c => ?_, ?_⟩
    · have := LinearMap.congr_fun (hφc i c) (π d)
      simp only [Module.End.mul_apply, LinearMap.smul_apply, RingHom.comp_apply] at this
      rw [this, sub_self]; exact Submodule.zero_mem _
    · have : ∑ i, φ i (π d) = π d := by rw [← hfapp]; exact hfπ d
      rw [this]; exact hGmem d hd

end GlobalTheory.HTSummand
end

section

set_option autoImplicit false

noncomputable section

open MvPolynomial
open Formalism.GradedWeylDivisibility

namespace GlobalTheory.HighWt

theorem map_bidet {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {r n K : ℕ} (sz : Fin K → ℕ)
    (hsz : ∀ k, sz k ≤ n) (I : ∀ k, Fin (sz k) → Fin r) :
    MvPolynomial.map φ (bideterminant R sz hsz I) = bideterminant S sz hsz I := by
  unfold bideterminant initMinor
  rw [map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [RingHom.map_det]
  congr 1
  ext p q
  simp [RingHom.mapMatrix_apply]

theorem baseChange_holds : BaseChange := by
  intro O _ _ _ ϖ hϖ N ν _
  have hmax : (Ideal.span {ϖ}).IsMaximal := by
    rw [← (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ]
    exact IsLocalRing.maximalIdeal.isMaximal O
  letI : Field (O ⧸ Ideal.span {ϖ}) := Ideal.Quotient.field _
  have hdom : IsDomain (O ⧸ Ideal.span {ϖ}) := Ideal.Quotient.isDomain _
  constructor
  · intro f hf
    rw [standardMonomialSpanDomain (O ⧸ Ideal.span {ϖ}) N N ν] at hf
    induction hf using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨K, sz, hsz, I, hsh, rfl⟩ := hx
      refine ⟨bideterminant O sz hsz I, ?_, map_bidet _ sz hsz I⟩
      rw [← hsh]
      exact bidetMem O N N K sz hsz I
    | zero => exact ⟨0, Submodule.zero_mem _, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨b, hb, rfl⟩ := hy
      exact ⟨a + b, Submodule.add_mem _ ha hb, by simp⟩
    | smul c x _ hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨c', rfl⟩ := Ideal.Quotient.mk_surjective c
      refine ⟨c' • a, Submodule.smul_mem _ c' ha, ?_⟩
      rw [smul_eq_C_mul, smul_eq_C_mul, map_mul, map_C]
  · intro g hg h0
    have hk : g ∈ RingHom.ker (MvPolynomial.map (Ideal.Quotient.mk (Ideal.span {ϖ}))) := h0
    rw [MvPolynomial.ker_map, Ideal.mk_ker, Ideal.map_span, Set.image_singleton,
      Ideal.mem_span_singleton'] at hk
    obtain ⟨h, hh⟩ := hk
    have hgh : g = ϖ • h := by rw [smul_eq_C_mul, ← hh, mul_comm]
    refine ⟨h, ?_, hgh⟩
    exact dualWeylSat O N N ν ϖ h hϖ.ne_zero (hgh ▸ hg)

end GlobalTheory.HighWt

end
end

section

open Polynomial GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters GlobalTheory.ParamLabel

namespace GlobalTheory.ParamLabel

variable {p : ℕ} [Fact p.Prime]

theorem exists_labelsChar_of_pos (L : GlobalTheory.GLq.LabelDatum p) {d : ℕ} (hd : 0 < d) (θ : Tor p d →* ℂˣ) :
    ∃ x : Fbar p, LabelsChar L θ x := by
  have hp : 0 < p ^ d - 1 := Nat.sub_pos_of_lt (Nat.one_lt_pow hd.ne' (Fact.out : p.Prime).one_lt)
  haveI : NeZero (p ^ d - 1) := ⟨hp.ne'⟩
  have hprim : IsPrimitiveRoot (L.gen d) (p ^ d - 1) := L.gen_order d hd ▸ IsPrimitiveRoot.orderOf _
  have h0 : L.gen d ≠ 0 := hprim.ne_zero hp.ne'
  have hprimC : IsPrimitiveRoot (L.teich (L.gen d)) (p ^ d - 1) := by
    refine ⟨by rw [← map_pow, hprim.pow_eq_one, map_one], fun l hl => hprim.dvd_of_pow_eq_one l ?_⟩
    exact L.teich_inj _ _ (pow_ne_zero _ h0) one_ne_zero (by rw [map_pow, hl, map_one])
  let γ : Tor p d := ⟨Units.mk0 _ h0, by
    rw [mem_rootsOfUnity]
    exact Units.ext (by simpa using hprim.pow_eq_one)⟩
  have hγ : γ ^ (p ^ d - 1) = 1 := Subtype.ext ((mem_rootsOfUnity _ _).1 γ.2)
  obtain ⟨k, -, hk⟩ := hprimC.eq_pow_of_pow_eq_one (ξ := ((θ γ : ℂˣ) : ℂ))
    (by rw [← Units.val_pow_eq_pow_val, ← map_pow, hγ, map_one, Units.val_one])
  refine ⟨L.gen d ^ k, by rw [← pow_mul, mul_comm, pow_mul, hprim.pow_eq_one, one_pow], fun u => ?_⟩
  have hu : ((u : (Fbar p)ˣ) : Fbar p) ^ (p ^ d - 1) = 1 := by
    rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity _ _).1 u.2, Units.val_one]
  obtain ⟨n, -, hn⟩ := hprim.eq_pow_of_pow_eq_one hu
  have hex : ∃ n : ℕ, ((u : (Fbar p)ˣ) : Fbar p) = L.gen d ^ n := ⟨n, hn.symm⟩
  unfold GlobalTheory.GLq.thetaOf
  rw [dite_eq_left hex]
  have e : u = γ ^ hex.choose := Subtype.ext (Units.ext (by simpa [γ] using hex.choose_spec))
  rw [map_pow, hk, ← Units.val_pow_eq_pow_val, ← map_pow, ← e]

theorem prod_frobenius_orbit_mem_lifts {d : ℕ} {x : Fbar p} (hx : x ^ (p ^ d - 1) = 1) :
    (∏ i : Fin d, (X - C (x ^ p ^ (i : ℕ)))) ∈ Polynomial.lifts (algebraMap (ZMod p) (Fbar p)) := by
  have hxd : x ^ p ^ d = x := by
    have h1 : p ^ d = (p ^ d - 1) + 1 := (Nat.sub_add_cancel (Nat.one_le_pow _ _ (Fact.out : p.Prime).pos)).symm
    rw [h1, pow_succ, hx, one_mul]
  rw [Fin.prod_univ_eq_prod_range (fun i => (X - C (x ^ p ^ i) : (Fbar p)[X])) d]
  have hfix : (∏ i ∈ Finset.range d, (X - C (x ^ p ^ i) : (Fbar p)[X])).map (frobenius (Fbar p) p) =
      ∏ i ∈ Finset.range d, (X - C (x ^ p ^ i)) := by
    have h1 := Finset.prod_range_succ (fun i => (X - C (x ^ p ^ i) : (Fbar p)[X])) d
    rw [Finset.prod_range_succ', hxd, pow_zero, pow_one] at h1
    rw [Polynomial.map_prod, ← mul_right_cancel₀ (X_sub_C_ne_zero x) h1]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Polynomial.map_sub, map_X, map_C, frobenius_def, pow_succ, pow_mul]
  rw [Polynomial.lifts_iff_coeff_lifts]
  intro n
  have h2 := congrArg (fun q => q.coeff n) hfix
  simp only [coeff_map, frobenius_def] at h2
  obtain ⟨m, hm⟩ := (mem_bot_iff_intCast p (Fbar p)).1 ((Subfield.mem_bot_iff_pow_eq_self (Fbar p) p).2 h2)
  exact ⟨(m : ZMod p), by rw [map_intCast, hm]⟩

theorem exists_labels (p : ℕ) [Fact p.Prime] (L : GlobalTheory.GLq.LabelDatum p) (r : ℕ) (s : SSParam p ℂ r) :
    ∃ (x : Cyc s.1 → Fbar p) (f : (ZMod p)[X]), Labels L s x f := by
  choose x hx using fun c : Cyc s.1 => exists_labelsChar_of_pos L (cycLen_pos s.1 c) (s.2 c)
  have hl : (∏ y : Σ c : Cyc s.1, Fin (cycLen s.1 c), (X - C (rootElt x y))) ∈
      Polynomial.lifts (algebraMap (ZMod p) (Fbar p)) := by
    rw [Fintype.prod_sigma]
    refine Subsemiring.prod_mem _ fun c _ => ?_
    simp only [rootElt]
    exact prod_frobenius_orbit_mem_lifts (d := cycLen s.1 c) (x := x c) (hx c).1
  obtain ⟨f, hf, -, hm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl
    (monic_prod_of_monic _ _ fun y _ => monic_X_sub_C _)
  refine ⟨x, f, hx, fun c => (hx c).1, hm, ?_⟩
  unfold Formalism.CyclotomicNorms.rootsBar
  rw [hf, ← Polynomial.roots_multiset_prod_X_sub_C (Finset.univ.val.map (rootElt x)), Multiset.map_map]
  rfl

end GlobalTheory.ParamLabel
end

section

open Polynomial GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters GlobalTheory.ParamLabel

namespace GlobalTheory.LabelNorm

variable {p : ℕ} [Fact p.Prime]

theorem sub_pos' {d : ℕ} (hd : 0 < d) : 0 < p ^ d - 1 :=
  Nat.sub_pos_of_lt (Nat.one_lt_pow hd.ne' (Fact.out : p.Prime).one_lt)

theorem theta_gen_pow (L : GlobalTheory.GLq.LabelDatum p) {d : ℕ} (hd : 0 < d) {x : Fbar p} (hx : x ^ (p ^ d - 1) = 1)
    (n : ℕ) : GlobalTheory.GLq.thetaOf L d x (L.gen d ^ n) = L.teich x ^ n := by
  have h : ∃ m : ℕ, L.gen d ^ n = L.gen d ^ m := ⟨n, rfl⟩
  unfold GlobalTheory.GLq.thetaOf
  rw [dite_eq_left h]
  have hp : IsPrimitiveRoot (L.gen d) (p ^ d - 1) := L.gen_order d hd ▸ IsPrimitiveRoot.orderOf _
  have hfin : IsOfFinOrder (L.gen d) := isOfFinOrder_iff_pow_eq_one.2 ⟨_, sub_pos' hd, hp.pow_eq_one⟩
  have hm : n ≡ h.choose [MOD p ^ d - 1] := by
    rw [← L.gen_order d hd]; exact hfin.pow_eq_pow_iff_modEq.1 h.choose_spec
  have h1 : L.teich x ^ (p ^ d - 1) = 1 := by rw [← map_pow, hx, map_one]
  rw [pow_eq_pow_mod h.choose h1, pow_eq_pow_mod n h1, hm]

theorem exists_pow (L : GlobalTheory.GLq.LabelDatum p) {d : ℕ} (hd : 0 < d) {z : Fbar p} (hz : z ^ (p ^ d - 1) = 1) :
    ∃ n : ℕ, z = L.gen d ^ n := by
  haveI : NeZero (p ^ d - 1) := ⟨(sub_pos' hd).ne'⟩
  have hprim : IsPrimitiveRoot (L.gen d) (p ^ d - 1) := L.gen_order d hd ▸ IsPrimitiveRoot.orderOf _
  obtain ⟨n, -, hn⟩ := hprim.eq_pow_of_pow_eq_one hz
  exact ⟨n, hn.symm⟩

theorem tor_pow {d : ℕ} (u : Tor p d) : ((u : (Fbar p)ˣ) : Fbar p) ^ (p ^ d - 1) = 1 := by
  rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity _ _).1 u.2, Units.val_one]

theorem base_pow (c : (ZMod p)ˣ) : algebraMap (ZMod p) (Fbar p) c ^ (p ^ 1 - 1) = 1 :=
  tor_pow (toTorOne p c)

theorem labels_norm_pow (L : GlobalTheory.GLq.LabelDatum p) {N : ℕ} (hN : 0 < N) (d : ℕ) (h : d ∣ N) (θ : Tor p d →* ℂˣ)
    (x : Fbar p) (n : ℕ) (hθ : LabelsChar L θ x) : LabelsChar L ((θ.comp (torNorm p h)) ^ n) (x ^ n) := by
  have hd : 0 < d := Nat.pos_of_dvd_of_pos h hN
  have hx : (x ^ n) ^ (p ^ N - 1) = 1 := by
    obtain ⟨k, hk⟩ := Nat.pow_sub_one_dvd_pow_sub_one p h
    rw [hk, ← pow_mul, mul_comm n, pow_mul, pow_mul, hθ.1, one_pow, one_pow]
  refine ⟨hx, fun u => ?_⟩
  obtain ⟨k, hk⟩ := exists_pow L hN (tor_pow u)
  have hn : (((torNorm p h u : Tor p d) : (Fbar p)ˣ) : Fbar p) = L.gen d ^ k := by
    have e : (((torNorm p h u : Tor p d) : (Fbar p)ˣ) : Fbar p) =
        ((u : (Fbar p)ˣ) : Fbar p) ^ ((p ^ N - 1) / (p ^ d - 1)) := Units.val_pow_eq_pow_val _ _
    obtain ⟨e', rfl⟩ := h
    rw [e, hk, ← pow_mul, mul_comm k, pow_mul, L.gen_norm d e' hd (Nat.pos_of_mul_pos_left hN)]
  rw [hk, theta_gen_pow L hN hx, MonoidHom.pow_apply, MonoidHom.comp_apply, Units.val_pow_eq_pow_val, hθ.2, hn,
    theta_gen_pow L hd hθ.1, map_pow, ← pow_mul, ← pow_mul, mul_comm]

theorem labels_base (L : GlobalTheory.GLq.LabelDatum p) {N : ℕ} (hN : 0 < N) (χ : (ZMod p)ˣ →* ℂˣ) (a : (ZMod p)ˣ)
    (h : LabelsTame L χ a) :
    LabelsChar L (χ.comp (baseNorm p N)) (algebraMap (ZMod p) (Fbar p) (a : ZMod p)) := by
  have h1 : LabelsChar L (χ.comp ((MulEquiv.ofBijective (toTorOne p) (toTorOne_bijective p)).symm :
      Tor p 1 →* (ZMod p)ˣ)) (algebraMap (ZMod p) (Fbar p) (a : ZMod p)) := by
    refine ⟨base_pow a, fun u => ?_⟩
    obtain ⟨v, rfl⟩ := (MulEquiv.ofBijective (toTorOne p) (toTorOne_bijective p)).surjective u
    rw [MonoidHom.comp_apply, MonoidHom.coe_coe, MulEquiv.symm_apply_apply, ← h v]
    rfl
  have h2 := labels_norm_pow L hN 1 (one_dvd N) _ _ 1 h1
  rw [pow_one, pow_one] at h2
  exact h2

theorem labels_inv (L : GlobalTheory.GLq.LabelDatum p) (χ : (ZMod p)ˣ →* ℂˣ) (a : (ZMod p)ˣ)
    (h : LabelsTame L χ a) : LabelsTame L χ⁻¹ a⁻¹ := by
  intro u
  obtain ⟨k, hk⟩ := exists_pow L one_pos (base_pow u)
  have h1 := h u
  rw [hk, theta_gen_pow L one_pos (base_pow a)] at h1
  rw [hk, theta_gen_pow L one_pos (base_pow a⁻¹), MonoidHom.inv_apply, Units.val_inv_eq_inv_val (χ u), ← h1,
    ← inv_pow]
  congr 1
  apply eq_inv_of_mul_eq_one_left
  rw [← map_mul, ← map_mul, Units.inv_mul, map_one, map_one]

theorem main : ∀ (p : ℕ) [Fact p.Prime] (L : GlobalTheory.GLq.LabelDatum p) (N : ℕ), 0 < N → (∀ (d : ℕ) (h : d ∣ N) (θ : Tor p d →* ℂˣ) (x : Fbar p) (n : ℕ), LabelsChar L θ x → LabelsChar L ((θ.comp (torNorm p h)) ^ n) (x ^ n)) ∧ ∀ (χ : (ZMod p)ˣ →* ℂˣ) (a : (ZMod p)ˣ), LabelsTame L χ a → LabelsChar L (χ.comp (baseNorm p N)) (algebraMap (ZMod p) (Fbar p) (a : ZMod p)) ∧ LabelsTame L χ⁻¹ a⁻¹ :=
  fun _ _ L _ hN => ⟨labels_norm_pow L hN, fun χ a h => ⟨labels_base L hN χ a h, labels_inv L χ a h⟩⟩

end GlobalTheory.LabelNorm
end

section

open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Matrix
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.levelIdempotent_mul_levelProj_mul_goodPart_eq : ∀ {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type} (B : BlockDat K G Pl0) (ℓ : Lvl K G) (v0 : InfinitePlace K) (s : ℕ), BlockHyp B ℓ v0 s → B.S.lvlE B.r ℓ.P ℓ.ψ * B.S.lvlPr B.r ℓ.P ℓ.ψ * B.vE ℓ = B.vE ℓ := by
  first | exact @GlobalTheory.GoodPartLevelForms.lvlE_lvlPr_vE | exact GlobalTheory.GoodPartLevelForms.lvlE_lvlPr_vE | (intros; apply GlobalTheory.GoodPartLevelForms.lvlE_lvlPr_vE <;> assumption)
end
