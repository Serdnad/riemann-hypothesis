module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle567
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle065
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle063
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle064
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle624
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle626
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle689
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle690
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle664
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle684
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle648
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle024
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle691
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.DiscreteValuationRing
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle022
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle534
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.PartsOrth
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.DownLift.SplitCoef

noncomputable section




namespace GlobalTheory.DownLift.GenQuot

open GlobalTheory.PlaceModel

variable {D : D7} {S T : HSp D}

theorem symplO_nsmul_swap (k : ℕ) (x y : WO S T) : symplO S T (k • x) y = symplO S T x (k • y) := by
  induction k with
  | zero => simp only [zero_smul, symplO_zero_left, symplO_zero_right]
  | succ n ih => rw [succ_nsmul, succ_nsmul, symplO_add_left, symplO_add_right, ih]

theorem reps_orth : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D), IsStdChar D ψ (-1) → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ a : AE D, a * a = a → infPart D a = 0 → ∀ k : ℕ, 0 < k → ∃ Y : Finset (WO S T), Y.Nonempty ∧ (∀ y ∈ Y, IsHalf (cA D a) y ∧ k • y ∈ latH S T ΛS ΛT) ∧ (∀ y', IsHalf (cA D a) y' → k • y' ∈ latH S T ΛS ΛT → ∃! y, y ∈ Y ∧ ∃ u ∈ latH S T ΛS ΛT, IsHalf (cA D a) u ∧ y' - y = k • u) ∧ ∀ x, IsHalf a x → k • x ∈ latH S T ΛS ΛT → ((∃ u ∈ latH S T ΛS ΛT, IsHalf a u ∧ x = k • u) → ∀ y ∈ Y, ψ (symplO S T x y) = 1) ∧ ((¬ ∃ u ∈ latH S T ΛS ΛT, IsHalf a u ∧ x = k • u) → ∑ y ∈ Y, ψ (symplO S T x y) = 0) := by
  intro D ψ S T hψ ΛS ΛT hS hT a ha hinf k hk
  classical
  have hdual : ∀ u : WO S T, u.map (infPart D) = 0 →
      (u ∈ latH S T ΛS ΛT ↔ ∀ u' ∈ latH S T ΛS ΛT, ψ (symplO S T u u') = 1) :=
    (GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T _ _ hψ hS hT).1
  have hfin : ∀ m : ℕ, 0 < m → ∃ R : Set (WO S T), R.Finite ∧
      ∀ t ∈ latH S T ΛS ΛT, ∃ r ∈ R, ∃ u ∈ latH S T ΛS ΛT, t = r + m • u :=
    GlobalTheory.LatFinMod.latO_finite_mod D S T _ _ hS.1.fg hT.1.fg fun _ => True
  have hsm : ∀ {b : AE D}, b * b = b → ∀ u ∈ latH S T ΛS ΛT, b • u ∈ latH S T ΛS ΛT ⊓ half S T b :=
    fun {b} hb u hu =>
    ⟨GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ b
      (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, hb])) u hu,
      (mem_half S T).2 (by rw [smul_smul, hb])⟩
  generalize latH S T ΛS ΛT = Λ at *
  have hc : cA D a * cA D a = cA D a := by rw [← RingHom.map_mul, ha]
  generalize hcdef : cA D a = c at *
  have tf : Function.Injective fun t : WO S T => k • t := fun x y hxy => by
    rw [← inv_smul_nsmul S T hk x, ← inv_smul_nsmul S T hk y]
    exact congrArg _ hxy

  let M : AddSubgroup (WO S T) := half S T c ⊓ Λ.comap (nsmulAddMonoidHom k)
  let N : AddSubgroup (WO S T) := (Λ ⊓ half S T c).map (nsmulAddMonoidHom k)
  have hM : ∀ y, y ∈ M ↔ IsHalf c y ∧ k • y ∈ Λ := fun y => by
    rw [isHalf_iff]; rfl
  have hN : ∀ n, n ∈ N ↔ ∃ u ∈ Λ, IsHalf c u ∧ n = k • u := fun n => by
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u, hu.1, (isHalf_iff S T).2 hu.2, rfl⟩
    · rintro ⟨u, hu, hu', rfl⟩
      exact ⟨u, ⟨hu, (isHalf_iff S T).1 hu'⟩, rfl⟩
  let N' : AddSubgroup M := N.addSubgroupOf M
  have hq : ∀ y₁ y₂ : M, ((y₁ : M ⧸ N') = y₂ ↔ (y₂ : WO S T) - y₁ ∈ N) := fun y₁ y₂ => by
    rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
    simp only [AddSubgroup.coe_add, AddSubgroup.coe_neg]
    rw [neg_add_eq_sub]

  obtain ⟨R2, hR2, hR2'⟩ := hfin (k * k) (Nat.mul_pos hk hk)
  have hP : ((fun t : WO S T => k • t) ⁻¹' ((fun r => c • r) '' R2)).Finite :=
    (hR2.image _).preimage tf.injOn
  have hcover : ∀ y : M, ∃ z : M, (z : WO S T) ∈ (fun t : WO S T => k • t) ⁻¹' ((fun r => c • r) '' R2) ∧
      (z : M ⧸ N') = y := by
    rintro ⟨y, hy⟩
    obtain ⟨hyc, hyk⟩ := (hM y).1 hy
    obtain ⟨r, hr, u, hu, hru⟩ := hR2' _ hyk
    have hcu := hsm hc u hu
    have hky : c • (k • y) = k • y := by
      rw [smul_comm]; exact congrArg (k • ·) ((mem_half S T).1 ((isHalf_iff S T).1 hyc))
    have hz : k • (y - k • (c • u)) = c • r := by
      rw [smul_sub, ← hky, hru, smul_add, mul_smul, smul_comm c k (k • u), smul_comm c k u]
      abel
    have hzM : y - k • (c • u) ∈ M := by
      refine (hM _).2 ⟨(isHalf_iff S T).2 ?_, ?_⟩
      · exact sub_mem ((isHalf_iff S T).1 hyc) (nsmul_mem hcu.2 k)
      · rw [smul_sub]
        exact sub_mem hyk (nsmul_mem (nsmul_mem hcu.1 k) k)
    refine ⟨⟨_, hzM⟩, ⟨r, hr, hz.symm⟩, (hq _ _).2 ?_⟩
    show y - (y - k • (c • u)) ∈ N
    rw [sub_sub_cancel]
    exact ⟨c • u, hcu, rfl⟩
  haveI hfinQ : Finite (M ⧸ N') := by
    let P' : Set M := {z | (z : WO S T) ∈ (fun t : WO S T => k • t) ⁻¹' ((fun r => c • r) '' R2)}
    have hP' : P'.Finite := hP.preimage Subtype.val_injective.injOn
    haveI := hP'.to_subtype
    refine Finite.of_surjective (fun z : P' => ((z : M) : M ⧸ N')) fun q => ?_
    induction q using QuotientAddGroup.induction_on with
    | H y =>
      obtain ⟨z, hz, hzy⟩ := hcover y
      exact ⟨⟨z, hz⟩, hzy⟩
  letI := Fintype.ofFinite (M ⧸ N')
  let rep : M ⧸ N' → WO S T := fun q => ((Quotient.out q : M) : WO S T)
  have hrepM : ∀ q, rep q ∈ M := fun q => (Quotient.out q : M).2
  have hrep : ∀ q, ((⟨rep q, hrepM q⟩ : M) : M ⧸ N') = q := fun q => QuotientAddGroup.out_eq' q
  have hrepinj : Function.Injective rep := fun q₁ q₂ h => by
    rw [← hrep q₁, ← hrep q₂]
    simp only [h]
  refine ⟨Finset.univ.image rep, ⟨rep 0, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩, ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hy
    exact (hM _).1 (hrepM q)
  · intro y' hy'c hy'k
    have hy'M : y' ∈ M := (hM y').2 ⟨hy'c, hy'k⟩
    refine ⟨rep (⟨y', hy'M⟩ : M), ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), (hN _).1 ?_⟩, ?_⟩
    · exact (hq _ _).1 (hrep _)
    · rintro y ⟨hyY, hyN⟩
      obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hyY
      have := (hq ⟨rep q, hrepM q⟩ ⟨y', hy'M⟩).2 ((hN _).2 hyN)
      rw [hrep] at this
      rw [this]
  intro x hx hkx
  have hxfin : ∀ {u : WO S T}, IsHalf a u → u.map (infPart D) = 0 := fun hu =>
    GlobalTheory.PlaceVec.half_infPart hinf ((isHalf_iff S T).1 hu)
  have hkxh : IsHalf a (k • x) := (isHalf_iff S T).2 (nsmul_mem ((isHalf_iff S T).1 hx) k)
  refine ⟨?_, fun hnot => ?_⟩
  · rintro ⟨u, hu, hua, rfl⟩ y hy
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hy
    rw [symplO_nsmul_swap]
    exact (hdual u (hxfin hua)).1 hu _ ((hM _).1 (hrepM q)).2
  ·
    have hconst : ∀ y₁ y₂ : M, (y₁ : M ⧸ N') = y₂ →
        ψ (symplO S T x (y₂ : WO S T)) = ψ (symplO S T x (y₁ : WO S T)) := fun y₁ y₂ h => by
      obtain ⟨u, hu, -, hu'⟩ := (hN _).1 ((hq _ _).1 h)
      have e : (y₂ : WO S T) = y₁ + k • u := by rw [← hu']; abel
      rw [e, symplO_add_right, AddChar.map_add_eq_mul, ← symplO_nsmul_swap,
        (hdual _ (hxfin hkxh)).1 hkx u hu, mul_one]

    obtain ⟨x', hx'h, hx'⟩ := half_div S T a k hk x ((isHalf_iff S T).1 hx)
    have hx'Λ : x' ∉ Λ := fun h => hnot ⟨x', h, (isHalf_iff S T).2 hx'h, hx'.symm⟩
    have hx'fin := hxfin ((isHalf_iff S T).2 hx'h)
    obtain ⟨l, hl, hψl⟩ : ∃ l ∈ Λ, ψ (symplO S T x' l) ≠ 1 := by
      by_contra hcon
      push_neg at hcon
      exact hx'Λ ((hdual x' hx'fin).2 hcon)
    have hl' := hsm hc l hl
    obtain ⟨y₀, hy₀h, hy₀⟩ := half_div S T c k hk _ hl'.2
    have hy₀M : y₀ ∈ M := (hM _).2 ⟨(isHalf_iff S T).2 hy₀h, hy₀ ▸ hl'.1⟩
    have hψ0 : ψ (symplO S T x y₀) ≠ 1 := by
      rw [← hx', symplO_nsmul_swap, hy₀, ← hcdef, ← symplO_smul, (mem_half S T).1 hx'h]
      exact hψl

    have hsum : ∑ y ∈ Finset.univ.image rep, ψ (symplO S T x y) = ∑ q : M ⧸ N', ψ (symplO S T x (rep q)) :=
      Finset.sum_image fun q₁ _ q₂ _ h => hrepinj h
    rw [hsum]
    have hshift : ∑ q : M ⧸ N', ψ (symplO S T x (rep q)) =
        (∑ q : M ⧸ N', ψ (symplO S T x (rep q))) * ψ (symplO S T x y₀) := by
      rw [Finset.sum_mul]
      refine (Fintype.sum_equiv (Equiv.addRight ((⟨y₀, hy₀M⟩ : M) : M ⧸ N')) _ _ fun q => ?_).symm
      rw [← AddChar.map_add_eq_mul, ← symplO_add_right]
      have := hconst (⟨rep q, hrepM q⟩ + ⟨y₀, hy₀M⟩) ⟨rep (q + ((⟨y₀, hy₀M⟩ : M) : M ⧸ N')), hrepM _⟩
        (by rw [hrep, QuotientAddGroup.mk_add, hrep])
      simpa using this.symm
    have h0 : (∑ q : M ⧸ N', ψ (symplO S T x (rep q))) * (ψ (symplO S T x y₀) - 1) = 0 := by
      rw [mul_sub, mul_one, ← hshift, sub_self]
    exact (mul_eq_zero.1 h0).resolve_right (sub_ne_zero.2 hψ0)

end GlobalTheory.DownLift.GenQuot

end
end

section

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

namespace GlobalTheory.CrysPrism

theorem cstS_mem_frob : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ w : Wq l a, cstS t K w ∈ SdSet t K e ∧ frobTot K a l (cstS t K w) = cstS t K (sigma l a w) := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ t w
  constructor
  · refine ⟨fun n => if n = 0 then w else 0, fun r => ?_, fun τ n => ?_⟩
    · refine (Set.finite_singleton 0).subset fun n hn => ?_
      by_contra h0
      exact hn (by simp [show n ≠ 0 from h0])
    · rw [cstS_apply, coeff_C]
      by_cases hn : n = 0
      · subst hn; simp
      · simp [hn]
  · funext τ
    change frob K l (cstS t K w (τ - 1)) = cstS t K (sigma l a w) τ
    rw [cstS_apply, cstS_apply, emb_sigma, ← PowerSeries.algebraMap_eq (R := K)]
    exact (frob K l).commutes _

theorem frob_sd_congr : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ F ∈ SdSet t K e, (frobTot K a l) F ∈ SdSet t K e ∧ ∃ B ∈ SdSet t K e, (frobTot K a l) F = F ^ l + (l : ZMod a → K⟦X⟧) * B := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ t
  have hclosed : ∀ F ∈ Sd t K e, F ∈ SdSet t K e := sdSet_closed l a e O K t
  have memS : ∀ {F}, F ∈ SdSet t K e → F ∈ Sd t K e := fun h => Subring.subset_closure h
  have hl0 : l ≠ 0 := (Fact.out : l.Prime).ne_zero
  let G : (ZMod a → K⟦X⟧) → Prop := fun z => z ∈ Sd t K e ∧
    ∃ B ∈ Sd t K e, frobTot K a l z = z ^ l + (l : ZMod a → K⟦X⟧) * B
  have gadd : ∀ x y, G x → G y → G (x + y) := by
    rintro x y ⟨hx, Bx, hBx, ex⟩ ⟨hy, By, hBy, ey⟩
    obtain ⟨r, hr⟩ := exists_add_pow_prime_eq (Fact.out : l.Prime) (⟨x, hx⟩ : Sd t K e) ⟨y, hy⟩
    have hr' := congrArg Subtype.val hr
    push_cast at hr'
    refine ⟨(Sd t K e).add_mem hx hy, Bx + By - x * y * r, ?_, ?_⟩
    · exact (Sd t K e).sub_mem ((Sd t K e).add_mem hBx hBy) ((Sd t K e).mul_mem ((Sd t K e).mul_mem hx hy) r.2)
    · rw [map_add (f := _), ex, ey, hr']; ring
  have gmul : ∀ x y, G x → G y → G (x * y) := by
    rintro x y ⟨hx, Bx, hBx, ex⟩ ⟨hy, By, hBy, ey⟩
    refine ⟨(Sd t K e).mul_mem hx hy, Bx * y ^ l + x ^ l * By + (l : ZMod a → K⟦X⟧) * Bx * By, ?_, ?_⟩
    · have hlS : (l : ZMod a → K⟦X⟧) ∈ Sd t K e := natCast_mem (Sd t K e) l
      exact (Sd t K e).add_mem ((Sd t K e).add_mem ((Sd t K e).mul_mem hBx ((Sd t K e).pow_mem hy l))
        ((Sd t K e).mul_mem ((Sd t K e).pow_mem hx l) hBy)) ((Sd t K e).mul_mem ((Sd t K e).mul_mem hlS hBx) hBy)
    · rw [map_mul, ex, ey]; ring
  have gcst : ∀ w, G (cstS t K w) := by
    intro w
    obtain ⟨hm, hf⟩ := cstS_mem_frob l a e O K t w
    obtain ⟨x, hx⟩ := GlobalTheory.T.wittTiltFrobenius_eq_pow_add_mul l a w
    refine ⟨memS hm, cstS t K x, memS (cstS_mem_frob l a e O K t x).1, ?_⟩
    rw [hf, hx, map_add (f := _), map_pow, map_mul, map_natCast]
  have gdp : ∀ n, G (dpS a e n) := by
    intro n
    obtain ⟨hm, B, hB, eB⟩ := GlobalTheory.T.dividedPowerMonomial_frobenius_congr_pow l a e O K t n
    exact ⟨memS hm, B, memS hB, eB⟩
  have gsum : ∀ (N : ℕ) (v : ℕ → Wq l a), G (∑ n ∈ Finset.range N, cstS t K (v n) * dpS a e n) := by
    intro N v
    refine Finset.sum_induction _ G gadd ⟨(Sd t K e).zero_mem, 0, (Sd t K e).zero_mem, ?_⟩ fun n _ => gmul _ _ (gcst _) (gdp n)
    rw [map_zero, zero_pow hl0, mul_zero, add_zero]
  intro F hF
  refine ⟨GlobalTheory.T.frobenius_maps_dividedPowerSeriesGeneratorSet l a e O K t F hF, ?_⟩
  obtain ⟨N, v, y, hy, hFe⟩ := GlobalTheory.T.dividedPowerSeriesGeneratorSet_eq_sum_add_mul l a e O K t F hF
  obtain ⟨hg, Bg, hBg, eg⟩ := gsum N v
  set g := ∑ n ∈ Finset.range N, cstS t K (v n) * dpS a e n
  set L : ZMod a → K⟦X⟧ := (l : ZMod a → K⟦X⟧)
  set Q := ∑ i ∈ Finset.range l, (g + L * y) ^ i * g ^ (l - 1 - i)
  have hQ : Q ∈ Sd t K e := (Sd t K e).sum_mem fun i _ => (Sd t K e).mul_mem
    ((Sd t K e).pow_mem ((Sd t K e).add_mem hg ((Sd t K e).mul_mem (natCast_mem (Sd t K e) l) (memS hy))) i)
    ((Sd t K e).pow_mem hg _)
  have geo : (g + L * y) ^ l = g ^ l + L * (y * Q) := by
    have h := geom_sum₂_mul (g + L * y) g l
    linear_combination -h
  refine ⟨Bg + frobTot K a l y - y * Q, hclosed _ ((Sd t K e).sub_mem ((Sd t K e).add_mem hBg
    (memS (GlobalTheory.T.frobenius_maps_dividedPowerSeriesGeneratorSet l a e O K t y hy))) ((Sd t K e).mul_mem (memS hy) hQ)), ?_⟩
  rw [hFe, map_add (f := _), map_mul, map_natCast]
  linear_combination eg - geo

end GlobalTheory.CrysPrism
end
end

section

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter
open scoped Formalism.Per

namespace GlobalTheory.CrysPrism.CompPP

theorem mem_span_pow_smul_top {R : Type} [CommRing R] (c x : R) (k : ℕ) :
    x ∈ (Ideal.span {c} ^ k • ⊤ : Submodule R R) ↔ c ^ k ∣ x := by
  change x ∈ Ideal.span {c} ^ k • (⊤ : Ideal R) ↔ _
  rw [Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {O : Type} [CommRing O] [Algebra ℤ_[l] O]
  [Module.Free ℤ_[l] O] {K : Type} [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]

theorem natCast_l_ne_zero : (l : Wq l a) ≠ 0 := WittVector.p_nonzero l (Fq l a)


variable (K) in
theorem emb_injective (t : Wq l a →ₐ[ℤ_[l]] O) (τ : ZMod a) :
    Function.Injective fun x : Wq l a => algebraMap O K (emb t τ x) := by
  haveI : Nontrivial O :=
    ⟨⟨0, 1, fun h => one_ne_zero (by simpa using congrArg (algebraMap O K) h.symm : (1 : K) = 0)⟩⟩
  have ht : Function.Injective t := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra h0
    obtain ⟨m, b, rfl⟩ := WittVector.exists_eq_pow_p_mul' x h0
    have hu : IsUnit (t (b : Wq l a)) := b.isUnit.map t
    rw [map_mul, map_pow, map_natCast] at hx
    have hlm : (l : O) ^ m = 0 := (hu.mul_left_eq_zero).1 hx
    have h2 : ((l : ℤ_[l]) ^ m) • (1 : O) = 0 := by
      rw [Algebra.smul_def, mul_one, map_pow, map_natCast]; exact hlm
    rcases smul_eq_zero.1 h2 with h3 | h3
    · exact pow_ne_zero m (Nat.cast_ne_zero.2 hl.out.ne_zero) h3
    · exact one_ne_zero h3
  exact IsUnitBall.inj.comp (ht.comp (sigmaNeg l a τ).injective)

variable (t : Wq l a →ₐ[ℤ_[l]] O) (e : ℕ)

def Wit (F : ZMod a → K⟦X⟧⟦X⟧) (w : ℕ × ℕ → Wq l a) : Prop :=
  ∀ τ i n, ((i.factorial * (n / e).factorial : ℕ) : K) * coeff n (coeff i (F τ)) =
      algebraMap O K (emb t τ (w (i, n)))

omit [Module.Free ℤ_[l] O] in
theorem Wit.sub {F G : ZMod a → K⟦X⟧⟦X⟧} {w v : ℕ × ℕ → Wq l a} (hF : Wit t e F w) (hG : Wit t e G v) :
    Wit t e (F - G) (w - v) := by
  intro τ i n
  simp only [Pi.sub_apply, map_sub, mul_sub, hF τ i n, hG τ i n]

omit [Module.Free ℤ_[l] O] in
theorem Wit.zero : Wit t e (0 : ZMod a → K⟦X⟧⟦X⟧) 0 := by
  intro τ i n
  simp

omit [Module.Free ℤ_[l] O] in
theorem Wit.lpow {G : ZMod a → K⟦X⟧⟦X⟧} {v : ℕ × ℕ → Wq l a} (hG : Wit t e G v) (k : ℕ) :
    Wit t e ((l : ZMod a → K⟦X⟧⟦X⟧) ^ k * G) (fun p => (l : Wq l a) ^ k * v p) := by
  intro τ i n
  have h1 : ((l : ZMod a → K⟦X⟧⟦X⟧) ^ k * G) τ = C (C ((l : K) ^ k)) * G τ := by
    simp only [Pi.mul_apply, Pi.pow_apply, Pi.natCast_apply, map_pow, map_natCast]
  rw [h1, coeff_C_mul, coeff_C_mul, map_mul, map_mul, map_pow, map_pow, map_natCast, map_natCast,
    ← hG τ i n]
  ring

theorem Wit.unique {F : ZMod a → K⟦X⟧⟦X⟧} {w v : ℕ × ℕ → Wq l a} (hw : Wit t e F w) (hv : Wit t e F v) :
    w = v :=
  funext fun p => emb_injective K t 0 ((hw 0 p.1 p.2).symm.trans (hv 0 p.1 p.2))

omit [Module.Free ℤ_[l] O] in
theorem Wit.eq [CharZero K] {F G : ZMod a → K⟦X⟧⟦X⟧} {w : ℕ × ℕ → Wq l a} (hF : Wit t e F w)
    (hG : Wit t e G w) : F = G :=
  funext fun τ => PowerSeries.ext fun i => PowerSeries.ext fun n =>
    mul_left_cancel₀ (Nat.cast_ne_zero.2 (by positivity)) ((hF τ i n).trans (hG τ i n).symm)


variable (K) in
def mkF (v : ℕ × ℕ → Wq l a) : ZMod a → K⟦X⟧⟦X⟧ := fun τ =>
  PowerSeries.mk fun i => PowerSeries.mk fun n =>
    algebraMap O K (emb t τ (v (i, n))) / ((i.factorial * (n / e).factorial : ℕ) : K)

omit [Module.Free ℤ_[l] O] in
theorem wit_mk [CharZero K] (v : ℕ × ℕ → Wq l a) : Wit t e (mkF K t e v) v := by
  intro τ i n
  simp only [mkF, coeff_mk]
  exact mul_div_cancel₀ _ (Nat.cast_ne_zero.2 (by positivity))

end GlobalTheory.CrysPrism.CompPP

namespace GlobalTheory.CrysPrism.CompPP

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {O : Type} [CommRing O] [Algebra ℤ_[l] O]
  [Module.Free ℤ_[l] O] {K : Type} [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
  (t : Wq l a →ₐ[ℤ_[l]] O) (e : ℕ)


omit [Module.Free ℤ_[l] O] in
theorem tendsToZeroLAdically_of_eq_prime_pow_mul {u v : ℕ × ℕ → Wq l a} (k : ℕ) (h : ∀ p, u p = (l : Wq l a) ^ k * v p)
    (hu : LTo0 l u) : LTo0 l v := by
  intro r
  filter_upwards [hu (k + r)] with p hp
  rw [h p, pow_add] at hp
  exact (mul_dvd_mul_iff_left (pow_ne_zero k natCast_l_ne_zero)).1 hp

theorem dvd_iff [CharZero K] (hcl : ∀ F ∈ PPd t K e, F ∈ PPSet t K e) (F : ↥(PPd t K e)) (k : ℕ)
    {w : ℕ × ℕ → Wq l a} (hw : Wit t e F.1 w) :
    (l : ↥(PPd t K e)) ^ k ∣ F ↔ ∀ p, (l : Wq l a) ^ k ∣ w p := by
  constructor
  · rintro ⟨G, rfl⟩
    obtain ⟨v, -, hv⟩ := hcl G.1 G.2
    have h1 : Wit t e ((l : ↥(PPd t K e)) ^ k * G).1 (fun p => (l : Wq l a) ^ k * v p) := by
      have := Wit.lpow t e hv k
      simpa using this
    rw [Wit.unique t e hw h1]
    exact fun p => dvd_mul_right _ _
  · intro h
    choose v hv using h
    obtain ⟨w', hw0', hw'⟩ := hcl F.1 F.2
    rw [← Wit.unique t e hw hw'] at hw0'
    have hv0 : LTo0 l v := tendsToZeroLAdically_of_eq_prime_pow_mul k hv hw0'
    refine ⟨⟨mkF K t e v, Subring.subset_closure ⟨v, hv0, wit_mk t e v⟩⟩, Subtype.ext ?_⟩
    have h1 := Wit.lpow t e (wit_mk (K := K) t e v) k
    have h2 : (fun p => (l : Wq l a) ^ k * v p) = w := funext fun p => (hv p).symm
    rw [h2] at h1
    simpa using Wit.eq t e hw h1

theorem complete_of [CharZero K] (hcl : ∀ F ∈ PPd t K e, F ∈ PPSet t K e) :
    IsAdicComplete (Ideal.span {(l : ↥(PPd t K e))}) ↥(PPd t K e) := by
  have hWq : ∀ (x y : Wq l a) (n : ℕ), (x ≡ y [SMOD (Ideal.span {(l : Wq l a)} ^ n • ⊤ : Submodule (Wq l a) (Wq l a))] ↔
      (l : Wq l a) ^ n ∣ x - y) := fun x y n => by
    rw [SModEq.sub_mem, mem_span_pow_smul_top]
  have hPP : ∀ (x y : ↥(PPd t K e)) (n : ℕ), (x ≡ y [SMOD (Ideal.span {(l : ↥(PPd t K e))} ^ n • ⊤ :
      Submodule ↥(PPd t K e) ↥(PPd t K e))] ↔ (l : ↥(PPd t K e)) ^ n ∣ x - y) := fun x y n => by
    rw [SModEq.sub_mem, mem_span_pow_smul_top]
  refine { haus' := fun F hF => ?_, prec' := fun f hf => ?_ }
  · obtain ⟨w, -, hw⟩ := hcl F.1 F.2
    have h0 : w = 0 := funext fun p => IsHausdorff.haus' (I := Ideal.span {(l : Wq l a)}) (w p) fun n =>
      (hWq _ _ n).2 (by
        rw [sub_zero]
        exact (dvd_iff t e hcl F n hw).1 (by simpa using (hPP F 0 n).1 (hF n)) p)
    rw [h0] at hw
    exact Subtype.ext (Wit.eq t e hw (Wit.zero t e))
  · choose W hW0 hW using fun m => hcl (f m).1 (f m).2
    have hd : ∀ {m n : ℕ}, m ≤ n → ∀ p, (l : Wq l a) ^ m ∣ W m p - W n p := fun {m n} hmn p =>
      (dvd_iff t e hcl (f m - f n) m (Wit.sub t e (hW m) (hW n))).1 ((hPP _ _ m).1 (hf hmn)) p
    choose w hw using fun p => IsPrecomplete.prec' (I := Ideal.span {(l : Wq l a)}) (fun m => W m p)
      fun {m n} hmn => (hWq _ _ m).2 (hd hmn p)
    have hw' : ∀ p n, (l : Wq l a) ^ n ∣ W n p - w p := fun p n => (hWq _ _ n).1 (hw p n)
    have hw0 : LTo0 l w := by
      intro r
      filter_upwards [hW0 r r] with p hp
      simpa using dvd_sub hp (hw' p r)
    refine ⟨⟨mkF K t e w, Subring.subset_closure ⟨w, hw0, wit_mk t e w⟩⟩, fun n => (hPP _ _ n).2 ?_⟩
    exact (dvd_iff t e hcl _ n (Wit.sub t e (hW n) (wit_mk t e w))).2 fun p => hw' p n

end GlobalTheory.CrysPrism.CompPP

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism

theorem GlobalTheory.CrysPrism.PPd_isAdicComplete : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), IsAdicComplete (Ideal.span {(l : ↥(PPd t K e))}) ↥(PPd t K e) := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ t
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[l] K).injective
  exact GlobalTheory.CrysPrism.CompPP.complete_of t e (GlobalTheory.T.dividedTwoVariableSubring_subset_generatorSet l a e O K t)
end
end

section

open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GroundTheory.Global GroundTheory.Global.IdeleGroup

theorem _root_.GlobalTheory.T.inverseTranspose_mem_cuspFormRapidKernelSpan_contragredient : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CuspSub E a) (F : GA E a → ℂ), F ∈ GlobalTheory.JSW.mspanR π → (fun g => F (invT a (Ad E) g)) ∈ GlobalTheory.JSW.mspanR π.contra := by
  first | exact @GlobalTheory.JSW.invT_mem_mspanR_contra | exact GlobalTheory.JSW.invT_mem_mspanR_contra | (intros; apply GlobalTheory.JSW.invT_mem_mspanR_contra <;> assumption)
end
