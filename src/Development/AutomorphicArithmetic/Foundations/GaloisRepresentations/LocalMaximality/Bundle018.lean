module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.ResidueOfTraceIsFiberSum
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle043
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle448
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle030
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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

@[expose] public section

section

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

noncomputable section

namespace UpperTheory.Gal.productCup_of_system.PartialTraceValue

private theorem nakGen {A B : Type} [CommRing A] [CommRing B] [Algebra A B] [Module.Finite A B] (I : Ideal A) (𝔟 : Ideal B)
    (hb : 𝔟 ⊔ I.map (algebraMap A B) = ⊤) : ∃ r : A, r - 1 ∈ I ∧ algebraMap A B r ∈ 𝔟 := by
  let N : Submodule A B := 𝔟.restrictScalars A
  have key : ∀ j ∈ I.map (algebraMap A B), ∀ b : B,
      (Submodule.Quotient.mk (j * b) : B ⧸ N) ∈ I • (⊤ : Submodule A (B ⧸ N)) := by
    intro j hj
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hj
    · rintro _ ⟨i, hi, rfl⟩ b
      rw [← Algebra.smul_def, Submodule.Quotient.mk_smul]
      exact Submodule.smul_mem_smul hi Submodule.mem_top
    · intro b
      rw [zero_mul]
      exact Submodule.zero_mem _
    · intro u v _ _ hu hv b
      rw [add_mul, Submodule.Quotient.mk_add]
      exact Submodule.add_mem _ (hu b) (hv b)
    · intro c u _ hu b
      rw [smul_eq_mul, show c * u * b = u * (c * b) by ring]
      exact hu _
  have hin : (⊤ : Submodule A (B ⧸ N)) ≤ I • ⊤ := by
    rintro q -
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    obtain ⟨a, ha, j, hj, haj⟩ := Submodule.mem_sup.1 (hb ▸ Submodule.mem_top : (1 : B) ∈ 𝔟 ⊔ I.map (algebraMap A B))
    have : (Submodule.Quotient.mk b : B ⧸ N) = Submodule.Quotient.mk (j * b) := by
      rw [Submodule.Quotient.eq]
      have : b - j * b = a * b := by
        linear_combination (-b) * haj
      rw [this]
      exact 𝔟.mul_mem_right b ha
    rw [this]
    exact key j hj b
  obtain ⟨r, hr1, hr⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul I
    (⊤ : Submodule A (B ⧸ N)) Module.Finite.fg_top hin
  refine ⟨r, hr1, ?_⟩
  have h0 := hr (Submodule.Quotient.mk 1) Submodule.mem_top
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Algebra.smul_def, mul_one] at h0
  exact h0

private theorem nakHom {A B : Type} [CommRing A] [CommRing B] [Algebra ℂ A] [Algebra ℂ B] [Algebra.FiniteType ℂ B]
    (φ : A →ₐ[ℂ] B) (hint : ∀ b : B, φ.toRingHom.IsIntegralElem b) (I : Ideal A) (𝔟 : Ideal B)
    (hb : 𝔟 ⊔ I.map φ.toRingHom = ⊤) : ∃ r : A, r - 1 ∈ I ∧ φ r ∈ 𝔟 := by
  letI alg : Algebra A B := φ.toRingHom.toAlgebra
  haveI tow : IsScalarTower ℂ A B := IsScalarTower.of_algebraMap_eq fun c => (φ.commutes c).symm
  haveI int : Algebra.IsIntegral A B := ⟨hint⟩
  haveI : Algebra.FiniteType A B := Algebra.FiniteType.of_restrictScalars_finiteType ℂ _ _
  haveI fin : Module.Finite A B := Algebra.IsIntegral.finite
  exact nakGen I 𝔟 hb

variable {F L : Type} [Field F] [Field L] [Algebra ℂ F] [Algebra ℂ L] [Algebra F L] [IsScalarTower ℂ F L]
  {d : ℕ} (x : Fin (d + 1) → F)

private def tA (j : Fin d) : rA ℂ x {0} :=
  ⟨x j.succ / x 0, Algebra.subset_adjoin ⟨0, Finset.mem_singleton_self 0, j.succ, rfl⟩⟩

private def IA : Ideal (rA ℂ x {0}) := Ideal.span (Set.range (tA x))

private theorem val_one (φ : rA ℂ x {0} →ₐ[ℂ] ℂ) (hφ : ∀ j, φ (tA x j) = 0) {r : rA ℂ x {0}}
    (hr : r - 1 ∈ IA x) : φ r = 1 := by
  have hle : IA x ≤ RingHom.ker φ := by
    rw [IA, Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    exact hφ j
  have := hle hr
  rw [RingHom.mem_ker, map_sub, map_one, sub_eq_zero] at this
  exact this

private theorem nak (h : IsFinCover ℂ L x) (𝔟 : Ideal (rB ℂ L x {0}))
    (hb : 𝔟 ⊔ FibFin.coordIdeal ℂ L x = ⊤) :
    ∃ r : rA ℂ x {0}, r - 1 ∈ IA x ∧ FibFin.incl ℂ L x r ∈ 𝔟 := by
  haveI := h.smooth 0
  have hcomp : (rB ℂ L x {0}).val.toRingHom.comp (FibFin.incl ℂ L x).toRingHom =
      algebraMap (rA ℂ x {0}) L := RingHom.ext fun a => rfl
  have hint : ∀ b : rB ℂ L x {0}, (FibFin.incl ℂ L x).toRingHom.IsIntegralElem b := fun b => by
    obtain ⟨p, hpm, hp⟩ : IsIntegral (rA ℂ x {0}) (b : L) := b.2
    refine ⟨p, hpm, ?_⟩
    apply Subtype.ext
    change (rB ℂ L x {0}).val.toRingHom (Polynomial.eval₂ (FibFin.incl ℂ L x).toRingHom b p) = (0 : L)
    rw [Polynomial.hom_eval₂, hcomp]
    exact hp
  have hJ : FibFin.coordIdeal ℂ L x ≤ (IA x).map (FibFin.incl ℂ L x).toRingHom := by
    rw [FibFin.coordIdeal, Ideal.span_le]
    rintro _ ⟨l, rfl⟩
    change (FibFin.incl ℂ L x).toRingHom (tA x l) ∈ _
    exact Ideal.mem_map_of_mem _ (Ideal.subset_span (Set.mem_range_self l))
  exact nakHom (FibFin.incl ℂ L x) hint (IA x) 𝔟 (top_le_iff.1 (hb ▸ sup_le_sup_left hJ 𝔟))

private theorem fib_nonempty (h : IsFinCover ℂ L x)
    (hred : IsReduced (rB ℂ L x {0} ⧸ FibFin.coordIdeal ℂ L x)) : Nonempty (fib ℂ L x) := by
  by_contra hne
  have hall := (FibFin.fib_finite_and_sep ℂ L x h hred).2 1 (fun e => (hne ⟨e⟩).elim)
  have ht : FibFin.coordIdeal ℂ L x = ⊤ := (Ideal.eq_top_iff_one _).2 hall
  obtain ⟨r, hr1, hr⟩ := nak x h ⊥ (by rw [ht]; simp)
  have hr0 : r = 0 := by
    have h0 : algebraMap F L (r : F) = 0 := congrArg Subtype.val ((Ideal.mem_bot).1 hr)
    exact Subtype.ext ((map_eq_zero _).1 h0)
  obtain ⟨e, he⟩ := rA_single_polyEquiv ℂ F d x h.pd 0
  have hε : ((MvPolynomial.aeval (0 : Fin d → ℂ)).comp e.symm.toAlgHom) r = 1 := by
    refine val_one x _ (fun j => ?_) hr1
    have htj : tA x j = e (MvPolynomial.X j) := Subtype.ext (by rw [he j, Fin.succAbove_zero]; rfl)
    rw [htj]
    simp
  rw [hr0, map_zero] at hε
  exact zero_ne_one hε

private theorem comax (h : IsFinCover ℂ L x)
    (hred : IsReduced (rB ℂ L x {0} ⧸ FibFin.coordIdeal ℂ L x))
    (hCRT : ∀ v : fib ℂ L x → ℂ, ∃ b : rB ℂ L x {0}, ∀ e : fib ℂ L x, e.1 b = v e)
    (𝔞 : Ideal (rB ℂ L x {0})) (h𝔞 : ∀ e : fib ℂ L x, ∃ b ∈ 𝔞, e.1 b ≠ 0) :
    𝔞 ⊔ FibFin.coordIdeal ℂ L x = ⊤ := by
  obtain ⟨hfin, hsep⟩ := FibFin.fib_finite_and_sep ℂ L x h hred
  haveI := Fintype.ofFinite (fib ℂ L x)
  classical
  choose b hb hb0 using h𝔞
  choose c hc using fun e0 : fib ℂ L x => hCRT (fun e => if e = e0 then (e0.1 (b e0))⁻¹ else 0)
  have hs : (∑ e0, c e0 * b e0) ∈ 𝔞 := Ideal.sum_mem _ fun e0 _ => 𝔞.mul_mem_left _ (hb e0)
  have hval : ∀ e : fib ℂ L x, e.1 (∑ e0, c e0 * b e0) = 1 := by
    intro e

    rw [map_sum, Finset.sum_eq_single e (fun e0 _ hne => by rw [map_mul, hc, if_neg (Ne.symm hne), zero_mul])
    (fun hn => (hn (Finset.mem_univ e)).elim), map_mul, hc, if_pos rfl]
    exact inv_mul_cancel₀ (hb0 e)
  have h1 := hsep (1 - ∑ e0, c e0 * b e0) (fun e => by rw [map_sub, map_one, hval, sub_self])
  rw [Ideal.eq_top_iff_one]
  exact Submodule.mem_sup.2 ⟨_, hs, _, h1, by ring⟩

private theorem partialTrace_valuation_sum (h : IsFinCover ℂ L x)
    (hred : IsReduced (rB ℂ L x {0} ⧸ FibFin.coordIdeal ℂ L x)) (ρ : F →ₗ[ℂ] ℂ)
    (hRT : ∀ b : rB ℂ L x {0}, ρ (Algebra.trace F L b) = ∑ᶠ e : fib ℂ L x, e.1 b)
    (hRes : ∀ e : fib ℂ L x, ∀ f ∈ rA ℂ x {0}, Val (rB ℂ L x {0}) e.1 (algebraMap F L f) (ρ f))
    (hCRT : ∀ v : fib ℂ L x → ℂ, ∃ b : rB ℂ L x {0}, ∀ e : fib ℂ L x, e.1 b = v e)
    (g : L) (γ : fib ℂ L x → ℂ) (hg : ∀ e : fib ℂ L x, Val (rB ℂ L x {0}) e.1 g (γ e))
    (ht : Algebra.trace F L g ∈ rA ℂ x {0}) :
    ρ (Algebra.trace F L g) = ∑ᶠ e, γ e := by
  let 𝔞 : Ideal (rB ℂ L x {0}) :=
    { carrier := {b | (b : L) * g ∈ rB ℂ L x {0}}
      add_mem' := by
        intro a b ha hb
        have := (rB ℂ L x {0}).add_mem ha hb
        simpa [add_mul] using this
      zero_mem' := by simpa using (rB ℂ L x {0}).zero_mem
      smul_mem' := by
        intro c b hb
        have := (rB ℂ L x {0}).mul_mem c.2 hb
        simpa [mul_assoc] using this }
  have h𝔞 : ∀ e : fib ℂ L x, ∃ b ∈ 𝔞, e.1 b ≠ 0 := fun e => by
    obtain ⟨b, hb, hbv, hne, -⟩ := hg e
    exact ⟨⟨b, hb⟩, hbv, hne⟩
  obtain ⟨s, hs1, hs⟩ := nak x h 𝔞 (comax x h hred hCRT 𝔞 h𝔞)
  have hs' : algebraMap F L (s : F) * g ∈ rB ℂ L x {0} := hs
  have hone : ∀ e : fib ℂ L x, e.1 (FibFin.incl ℂ L x s) = 1 := fun e =>
    val_one x (e.1.comp (FibFin.incl ℂ L x)) (fun j => e.2 j) hs1
  have hval : ∀ e : fib ℂ L x, e.1 ⟨_, hs'⟩ = γ e := by
    intro e
    obtain ⟨b, hb, hbv, hne, heq⟩ := hg e
    have h1 : (⟨b, hb⟩ : rB ℂ L x {0}) * ⟨_, hs'⟩ = FibFin.incl ℂ L x s * ⟨b * g, hbv⟩ := by
      apply Subtype.ext
      change b * (algebraMap F L (s : F) * g) = algebraMap F L (s : F) * (b * g)
      ring
    have h2 := congrArg e.1 h1
    rw [map_mul, map_mul, hone, one_mul, heq] at h2
    exact mul_left_cancel₀ hne h2
  obtain ⟨e0⟩ := fib_nonempty x h hred
  have hev : ∀ f : rA ℂ x {0}, e0.1 (FibFin.incl ℂ L x f) = ρ f := by
    intro f
    obtain ⟨b, hb, hbv, hne, heq⟩ := hRes e0 f f.2
    have h1 : (⟨b * algebraMap F L f, hbv⟩ : rB ℂ L x {0}) = ⟨b, hb⟩ * FibFin.incl ℂ L x f := rfl
    rw [h1, map_mul] at heq
    exact mul_left_cancel₀ hne heq
  have htr : Algebra.trace F L (algebraMap F L (s : F) * g) = (s : F) * Algebra.trace F L g := by
    rw [← Algebra.smul_def, map_smul, smul_eq_mul]
  have h3 : ρ ((s : F) * Algebra.trace F L g) = ρ (Algebra.trace F L g) := by
    have h4 := hev (s * ⟨_, ht⟩)
    rw [map_mul, map_mul, hone e0, one_mul, hev] at h4
    exact h4.symm
  rw [← h3, ← htr]
  exact (hRT ⟨_, hs'⟩).trans (finsum_congr hval)

end UpperTheory.Gal.productCup_of_system.PartialTraceValue

end

theorem UpperTheory.Gal.productCup_of_system.trVal_of :
    ResidueOfTraceIsFiberSum → ResVal → CRT → ValBasic → TrVal := by
  intro hRT hRes hCRT _ F L _ _ _ _ _ _ d x hc hred ρ hρ g γ hg ht
  exact PartialTraceValue.partialTrace_valuation_sum (xv x) hc hred ρ (hRT F L d x hc hred ρ hρ)
    (fun e f hf => hRes F L d x hc ρ hρ e f hf) (hCRT F L d x hc).2 g γ hg ht
end

section

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

section
variable {K L : Type} [Field K] [Field L] [Algebra ℂ K] [Algebra ℂ L] [Algebra K L] [IsScalarTower ℂ K L]

private theorem mapDR_smul' (b : K) (w : DR ℂ K) :
    mapDR ℂ K L (b • w) = algebraMap K L b • mapDR ℂ K L w := by
  rw [map_smul]
  exact (algebraMap_smul L b (mapDR ℂ K L w)).symm

private theorem mapDR_iMulti (q : ℕ) (v : Fin q → K) :
    mapDR ℂ K L (ExteriorAlgebra.ιMulti K q fun j => D ℂ K (v j)) =
      ExteriorAlgebra.ιMulti L q fun j => D ℂ L (algebraMap K L (v j)) := by
  simp only [ExteriorAlgebra.ιMulti_apply]
  rw [map_list_prod, List.map_ofFn]
  congr 2
  funext j
  simp [mapDR, map1, ExteriorAlgebra.lift_ι_apply]

private theorem mapDR_om {B : Subalgebra ℂ K} {B' : Subalgebra ℂ L}
    (h : ∀ b ∈ B, algebraMap K L b ∈ B') (q : ℕ) {w : DR ℂ K} (hw : w ∈ omB ℂ K B q) :
    mapDR ℂ K L w ∈ omB ℂ L B' q := by
  induction hw using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨b, hb, v, hv, rfl⟩ := hy
    rw [mapDR_smul', mapDR_iMulti]
    exact Submodule.subset_span ⟨_, h b hb, _, fun j => h _ (hv j), rfl⟩
  | zero => simp
  | add u v _ _ hu hv => rw [map_add]; exact add_mem hu hv
  | smul c u _ hu =>
    have e := ((mapDR ℂ K L).toLinearMap.restrictScalars ℂ).map_smul c u
    have e' : mapDR ℂ K L (c • u) = c • mapDR ℂ K L u := e
    rw [e']
    exact Submodule.smul_mem _ _ hu
end

section
variable {L : Type} [Field L] [Algebra ℂ L]

private theorem om_mul (B : Subalgebra ℂ L) {p q : ℕ} {u w : DR ℂ L} (hu : u ∈ omB ℂ L B p)
    (hw : w ∈ omB ℂ L B q) : u * w ∈ omB ℂ L B (p + q) :=
  _root_.UpperTheory.Reformulated.B.Qe48.om_mul B hu hw
end

section
variable {K K' : Type} [Field K] [Field K'] [Algebra ℂ K] [Algebra ℂ K'] (j2 : K →ₐ[ℂ] K')

private theorem pullback_kahler_smul_alg (b : K) (w : DR ℂ K) : pr2L j2 (b • w) = j2 b • pr2L j2 w := by
  letI : Algebra K K' := j2.toRingHom.toAlgebra
  haveI : IsScalarTower ℂ K K' := IsScalarTower.of_algebraMap_eq fun c => (j2.commutes c).symm
  exact mapDR_smul' (L := K') b w

private theorem pullback_kahler_omegaBounded {B : Subalgebra ℂ K} {B' : Subalgebra ℂ K'} (h : ∀ b ∈ B, j2 b ∈ B') (q : ℕ)
    {w : DR ℂ K} (hw : w ∈ omB ℂ K B q) : pr2L j2 w ∈ omB ℂ K' B' q := by
  letI : Algebra K K' := j2.toRingHom.toAlgebra
  haveI : IsScalarTower ℂ K K' := IsScalarTower.of_algebraMap_eq fun c => (j2.commutes c).symm
  exact mapDR_om (L := K') h q hw
end

private theorem wd_map {ι E E' : Type} [LinearOrder ι] [AddCommGroup E] [Module ℂ E] [AddCommGroup E'] [Module ℂ E']
    (f : E →ₗ[ℂ] E') (w : ι → Module.End ℂ E) (w' : ι → Module.End ℂ E')
    (h : ∀ i m, f (w i m) = w' i (f m)) (c : Finset ι → E) :
    wd w' (fun s => f (c s)) = fun s => f (wd w c s) := by
  funext t

  simp [wd, h, map_sum]

section
variable {F K K' : Type} [Field F] [Field K] [Field K'] [Algebra ℂ F] [Algebra ℂ K] [Algebra ℂ K'] [Algebra F K]
  [IsScalarTower ℂ F K] [Algebra K K'] [IsScalarTower ℂ K K'] [Algebra F K'] [IsScalarTower F K K'] [IsScalarTower ℂ F K'] {d : ℕ}
  (x : Fin (d + 1) → Fˣ) (j2 : K →ₐ[ℂ] K')

private theorem gS_tmul (p q : K) : gS j2 (p ⊗ₜ q) = algebraMap K K' p * j2 q := by
  simp [gS]

private theorem gY_tmul (w' w : DR ℂ K) : gY j2 (w' ⊗ₜ w) = mapDR ℂ K K' w' * pr2L j2 w := by
  simp [gY]

private theorem gS_X (a : ℕ) (i : Fin (d + 1)) :
    gS j2 (((sysZ K x a).X i : (K ⊗[ℂ] K)ˣ) : K ⊗[ℂ] K) = (((sysY x j2 d).X i : K'ˣ) : K') := by
  simp [sysZ, sysY, gS, IsScalarTower.algebraMap_apply F K K']

private theorem gS_Y (a : ℕ) (i : Fin (d + 1)) :
    gS j2 (((sysZ K x a).Y i : (K ⊗[ℂ] K)ˣ) : K ⊗[ℂ] K) = (((sysY x j2 d).Y i : K'ˣ) : K') := by
  simp [sysZ, sysY, gS]

private theorem gY_act (s : K ⊗[ℂ] K) (m : DR ℂ K ⊗[ℂ] DR ℂ K) :
    gY j2 (actZ K s m) = gS j2 s • gY j2 m := by
  induction s using TensorProduct.induction_on with
  | zero => simp
  | add s t hs ht => simp only [map_add (f := _), LinearMap.add_apply, add_smul, hs, ht]
  | tmul p q =>
    induction m using TensorProduct.induction_on with
    | zero => simp
    | add u v hu hv => simp only [map_add (f := _), smul_add, hu, hv]
    | tmul w' w =>
      have e : actZ K (p ⊗ₜ q) (w' ⊗ₜ w) = (p • w') ⊗ₜ[ℂ] (q • w) := by
        simp [actZ, Module.endTensorEndAlgHom_apply]
      rw [e, gY_tmul, gY_tmul, mapDR_smul', pullback_kahler_smul_alg, gS_tmul, smul_mul_smul_comm]

private theorem gS_prod {κ : Type} [LinearOrder κ] (a : ℕ) (n : κ → ℕ × ℕ) (i j : Fin (d + 1)) (t : Finset κ) :
    gS j2 ((∏ l ∈ t, (sysZ K x a).u n i j l : (K ⊗[ℂ] K)ˣ) : K ⊗[ℂ] K) =
      ((∏ l ∈ t, (sysY x j2 d).u n i j l : K'ˣ) : K') := by
  simp only [Units.coe_prod, map_prod, Sys.u, Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow, gS_X, gS_Y]

variable {x j2}

private theorem gY_M (hb : ∀ I, ∀ b ∈ rB ℂ K (xv x) I, algebraMap K K' b ∈ rB ℂ K' (xv x) I ∧ j2 b ∈ R2 (xv x) j2 I)
    {a : ℕ} (ha : a ≤ d) (I J : Finset (Fin (d + 1))) {m : DR ℂ K ⊗[ℂ] DR ℂ K}
    (hm : m ∈ (sysZ K x a).M I J) : gY j2 m ∈ (sysY x j2 d).M I J := by
  have key : (sysZ K x a).M I J ≤ ((sysY x j2 d).M I J).comap (gY j2) := by
    refine Submodule.map₂_le.2 fun u hu w hw => ?_
    show gY j2 (u ⊗ₜ w) ∈ omB ℂ K' (RY (xv x) j2 I J) d
    rw [gY_tmul]
    have e : d - a + a = d := by omega
    have h := om_mul (RY (xv x) j2 I J)
      (mapDR_om (L := K') (B' := RY (xv x) j2 I J)
        (fun b h => (le_sup_left : rB ℂ K' (xv x) I ≤ RY (xv x) j2 I J) (hb I b h).1) _ hu)
      (pullback_kahler_omegaBounded j2 (B' := RY (xv x) j2 I J)
        (fun b h => (le_sup_right : R2 (xv x) j2 J ≤ RY (xv x) j2 I J) (hb J b h).2) _ hw)
    rwa [e] at h
  exact key hm

private theorem gY_mix (hb : ∀ I, ∀ b ∈ rB ℂ K (xv x) I, algebraMap K K' b ∈ rB ℂ K' (xv x) I ∧ j2 b ∈ R2 (xv x) j2 I)
    {a : ℕ} (ha : a ≤ d) (s : Finset (Two d)) {m : DR ℂ K ⊗[ℂ] DR ℂ K}
    (h : m ∈ mixF (sysZ K x a).M s) : gY j2 m ∈ mixF (sysY x j2 d).M s := by
  unfold mixF at h ⊢
  split_ifs at h ⊢ with hc
  · exact gY_M hb ha _ _ h
  · rw [Submodule.mem_bot] at h ⊢
    simp [h]

private theorem gY_wt {κ : Type} [LinearOrder κ] (a : ℕ) (z : κ → K ⊗[ℂ] K) (t : Two d ⊕ₗ κ)
    (m : DR ℂ K ⊗[ℂ] DR ℂ K) :
    gY j2 ((sysZ K x a).wt z t m) = (sysY x j2 d).wt (fun l => gS j2 (z l)) t (gY j2 m) := by
  unfold Sys.wt
  cases ofLex t with
  | inl i => rfl
  | inr l => exact gY_act j2 (z l) m
end

theorem UpperTheory.Gal.productCup_of_system.gMap_of :
    RYBasic → WdUni → GMap := by
  intro hB _ F K K' _ _ _ _ _ _ _ _ _ _ _ _ _ d x j2 h0 a ha
  have hb := (hB F K K' d x j2 h0).2.2.2.1
  refine ⟨fun l => ?_, fun s m => gY_act j2 s m, fun I J s hs => ?_, fun N t ht => ?_, ?_⟩
  · simp [Sys.mu, gS_X, gS_Y, map_sub, map_mul]
  · obtain ⟨t, rfl⟩ := hs
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add u v hu hv =>
      rw [map_add (f := _), map_add (f := _)]
      exact add_mem hu hv
    | tmul p q =>
      have e : gS j2 (Algebra.TensorProduct.map (rB ℂ K (xv x) I).val (rB ℂ K (xv x) J).val (p ⊗ₜ q)) =
          algebraMap K K' p * j2 q := by
        rw [Algebra.TensorProduct.map_tmul, gS_tmul]
        rfl
      refine e ▸ (RY (xv x) j2 I J).mul_mem ?_ ?_
      · exact (le_sup_left : rB ℂ K' (xv x) I ≤ RY (xv x) j2 I J) (hb I _ p.2).1
      · exact (le_sup_right : R2 (xv x) j2 J ≤ RY (xv x) j2 I J) (hb J _ q.2).2
  · obtain ⟨y, hy, rfl⟩ := ht
    refine ⟨fun s => gY j2 (y s), fun s _ => ?_, wd_map (gY j2) _ _ (fun _ _ => rfl) y⟩
    have h := hy s (Set.mem_univ s)
    change y s ∈ (if (s.card : ℤ) = N - 1 then mixF (sysZ K x a).M s else ⊥) at h
    change gY j2 (y s) ∈ (if (s.card : ℤ) = N - 1 then mixF (sysY x j2 d).M s else ⊥)
    split_ifs at h ⊢ with hc
    · exact gY_mix hb ha s h
    · rw [Submodule.mem_bot] at h ⊢
      simp [h]
  · intro κ _ _ n z N c hc
    obtain ⟨hc1, hc2⟩ := hc
    refine ⟨fun s _ => ?_, ?_⟩
    · have h := hc1 s (Set.mem_univ s)
      change c s ∈ (if (s.card : ℤ) = N then mixF (fun I J => ((sysZ K x a).M I J).map
        ((sysZ K x a).act ((∏ l ∈ rgt s, (sysZ K x a).u n (pk I) (pk J) l : (K ⊗[ℂ] K)ˣ) : K ⊗[ℂ] K))) (lft s) else ⊥) at h
      change gY j2 (c s) ∈ (if (s.card : ℤ) = N then mixF (fun I J => ((sysY x j2 d).M I J).map
        ((sysY x j2 d).act ((∏ l ∈ rgt s, (sysY x j2 d).u n (pk I) (pk J) l : K'ˣ) : K'))) (lft s) else ⊥)
      split_ifs at h ⊢ with hcard
      · unfold mixF at h ⊢
        split_ifs at h ⊢ with hne
        · obtain ⟨m, hm, hmc⟩ := h
          refine ⟨gY j2 m, gY_M hb ha _ _ hm, ?_⟩
          rw [← hmc]
          have e := gY_act j2 ((∏ l ∈ rgt s, (sysZ K x a).u n (pk (lft (lft s))) (pk (rgt (lft s))) l :
            (K ⊗[ℂ] K)ˣ) : K ⊗[ℂ] K) m
          rw [gS_prod x j2 a] at e
          exact e.symm
        · rw [Submodule.mem_bot] at h ⊢
          simp [h]
      · rw [Submodule.mem_bot] at h ⊢
        simp [h]
    · have e := wd_map (gY j2) ((sysZ K x a).wt z) ((sysY x j2 d).wt fun l => gS j2 (z l))
        (fun t m => gY_wt a z t m) c
      have hc2' : wd ((sysZ K x a).wt z) c = 0 := hc2
      change wd ((sysY x j2 d).wt fun l => gS j2 (z l)) (fun s => gY j2 (c s)) = 0
      rw [e, hc2']
      funext s
      simp
end
