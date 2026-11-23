module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.IndexCocycleOrbits.OrbStabZ
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.StabLoc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle008
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

namespace Formalism.L2.SG.Pf.ProdEP2Core

open Formalism.L2.SG.Pf.IndexCocycleOrbits

section Conj

variable {G : Type} [Group G]

def cj (s : G) (X : Subgroup G) : Subgroup G := X.map (MulAut.conj s⁻¹).toMonoidHom

theorem mem_cj {s : G} {X : Subgroup G} {g : G} : g ∈ cj s X ↔ s * g * s⁻¹ ∈ X := by
  unfold cj
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa [mul_assoc] using hx
  · intro h
    exact ⟨s * g * s⁻¹, h, by simp [mul_assoc]⟩

theorem cj_le {s : G} {X Y : Subgroup G} (h : X ≤ Y) : cj s X ≤ cj s Y := Subgroup.map_mono h

theorem cj_self {s : G} {X : Subgroup G} (hs : s ∈ X) : cj s X = X := by
  ext g
  rw [mem_cj]
  constructor
  · intro h
    have h2 : s⁻¹ * (s * g * s⁻¹) * s ∈ X := X.mul_mem (X.mul_mem (X.inv_mem hs) h) hs
    simpa [mul_assoc] using h2
  · intro h
    exact X.mul_mem (X.mul_mem hs h) (X.inv_mem hs)

theorem relIndex_cj (s : G) (X Y : Subgroup G) : (cj s X).relIndex (cj s Y) = X.relIndex Y := Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj s⁻¹).injective

theorem idxRatio_self (A : Subgroup G) : IdxRatio A A = 1 := by
  simp [IdxRatio, Subgroup.relIndex_self]

end Conj

section Dc

variable {K : Type} [Group K] (A : Subgroup K) (π : K →* A) (H : Subgroup K)

def dcMap (k : K) : A ⧸ H.map π := QuotientGroup.mk (π k)

theorem dcMap_surjective (hπ : ∀ a : A, π a = a) : Function.Surjective (dcMap A π H) := by
  intro q
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
  exact ⟨a, by simp [dcMap, hπ]⟩

theorem dcMap_eq_iff (k k' : K) :
    dcMap A π H k = dcMap A π H k' ↔ ∃ n ∈ π.ker, ∃ h ∈ H, k' = n * k * h := by
  unfold dcMap
  rw [QuotientGroup.eq, Subgroup.mem_map]
  constructor
  · rintro ⟨h, hH, hh⟩
    refine ⟨k' * h⁻¹ * k⁻¹, ?_, h, hH, by group⟩
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv, map_inv, hh]
    group
  · rintro ⟨n, hn, h, hH, rfl⟩
    refine ⟨h, hH, ?_⟩
    rw [MonoidHom.mem_ker] at hn
    rw [map_mul, map_mul, hn, one_mul]
    group

theorem card_dc (hπ : ∀ a : A, π a = a) :
    Nat.card (Quotient (Setoid.ker (dcMap A π H))) = (H.map π).index := by
  rw [Subgroup.index, Nat.card_congr (Setoid.quotientKerEquivOfSurjective _ (dcMap_surjective A π H hπ))]

end Dc

end Formalism.L2.SG.Pf.ProdEP2Core
end
end

section

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.ProdE

section Gen

variable {G : Type} [Group G] {ι : Type} {H : ι → Type} [∀ i, Group (H i)] (π : ∀ i, G →* H i)

def glob (A : ∀ i, Subgroup (H i)) : Subgroup G := ⨅ i, (A i).comap (π i)

theorem mem_glob {A : ∀ i, Subgroup (H i)} {g : G} : g ∈ glob π A ↔ ∀ i, π i g ∈ A i := by
  simp [glob, Subgroup.mem_iInf]

theorem relIndex_glob (A C : ∀ i, Subgroup (H i)) (S : Finset ι) (hS : ∀ i ∉ S, A i = C i)
    (hfin : ∀ i, (C i).relIndex (A i) ≠ 0)
    (happrox : ∀ h : ∀ i, H i, ∃ g : G, (∀ i ∈ S, (h i)⁻¹ * π i g ∈ A i ⊓ C i) ∧ ∀ i ∉ S, π i g ∈ A i) :
    (glob π C).relIndex (glob π A) = ∏ i ∈ S, (C i).relIndex (A i) := by
  classical
  set K := (glob π C).subgroupOf (glob π A) with hK
  let Φ : ↥(glob π A) → ∀ i : S, ↥(A (i : ι)) ⧸ (C (i : ι)).subgroupOf (A (i : ι)) := fun g i =>
    QuotientGroup.mk ⟨π i g, (mem_glob π).1 g.2 i⟩
  have hrel : ∀ a b : ↥(glob π A), Φ a = Φ b ↔ a⁻¹ * b ∈ K := by
    intro a b
    rw [hK, Subgroup.mem_subgroupOf, mem_glob]
    simp only [Φ, funext_iff]
    constructor
    · intro h i
      by_cases hi : i ∈ S
      · have h1 := h ⟨i, hi⟩
        rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h1
        simpa using h1
      · rw [← hS i hi]
        simpa using (A i).mul_mem ((A i).inv_mem ((mem_glob π).1 a.2 i)) ((mem_glob π).1 b.2 i)
    · intro h i
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      simpa using h i
  have hsurj : Function.Surjective Φ := by
    intro q
    choose r hr using fun i : S => QuotientGroup.mk_surjective (q i)
    obtain ⟨g, hg1, hg2⟩ := happrox (fun i => if hi : i ∈ S then ((r ⟨i, hi⟩ : A i) : H i) else 1)
    have hgA : g ∈ glob π A := by
      rw [mem_glob]
      intro i
      by_cases hi : i ∈ S
      · have h1 := hg1 i hi
        simp only [dif_pos hi] at h1
        have h2 := (A i).mul_mem (r ⟨i, hi⟩).2 (Subgroup.mem_inf.1 h1).1
        simpa using h2
      · exact hg2 i hi
    refine ⟨⟨g, hgA⟩, ?_⟩
    funext i
    rw [← hr i]
    simp only [Φ]
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have h1 := hg1 i.1 i.2
    simp only [dif_pos i.2] at h1
    simpa using (C i).inv_mem (Subgroup.mem_inf.1 h1).2
  let Ψ : ↥(glob π A) ⧸ K → ∀ i : S, ↥(A (i : ι)) ⧸ (C (i : ι)).subgroupOf (A (i : ι)) :=
    Quotient.lift Φ (fun a b hab => (hrel a b).2 (QuotientGroup.leftRel_apply.1 hab))
  have hbij : Function.Bijective Ψ := by
    constructor
    · intro x y hxy
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
      obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
      exact QuotientGroup.eq.2 ((hrel a b).1 hxy)
    · intro q
      obtain ⟨a, ha⟩ := hsurj q
      exact ⟨QuotientGroup.mk a, ha⟩
  have hcard := Nat.card_congr (Equiv.ofBijective Ψ hbij)
  rw [Nat.card_pi] at hcard
  rw [← Finset.prod_coe_sort S]
  exact hcard

theorem idxRatio_glob (A C : ∀ i, Subgroup (H i)) (S : Finset ι) (hS : ∀ i ∉ S, A i = C i)
    (hfinA : ∀ i, (C i).relIndex (A i) ≠ 0) (hfinC : ∀ i, (A i).relIndex (C i) ≠ 0)
    (happrox : ∀ h : ∀ i, H i, ∃ g : G, (∀ i ∈ S, (h i)⁻¹ * π i g ∈ A i ⊓ C i) ∧ ∀ i ∉ S, π i g ∈ A i) :
    Formalism.L2.SG.Pf.IndexCocycleOrbits.IdxRatio (glob π A) (glob π C) = ∏ i ∈ S, Formalism.L2.SG.Pf.IndexCocycleOrbits.IdxRatio (A i) (C i) := by
  have happrox' : ∀ h : ∀ i, H i, ∃ g : G, (∀ i ∈ S, (h i)⁻¹ * π i g ∈ C i ⊓ A i) ∧ ∀ i ∉ S, π i g ∈ C i := by
    intro h
    obtain ⟨g, hg1, hg2⟩ := happrox h
    refine ⟨g, fun i hi => ?_, fun i hi => ?_⟩
    · rw [inf_comm]
      exact hg1 i hi
    · rw [← hS i hi]
      exact hg2 i hi
  unfold Formalism.L2.SG.Pf.IndexCocycleOrbits.IdxRatio
  rw [relIndex_glob π A C S hS hfinA happrox,
    relIndex_glob π C A S (fun i hi => (hS i hi).symm) hfinC happrox']
  push_cast
  rw [Finset.prod_div_distrib]

end Gen

end Formalism.L2.SG.Pf.ProdE
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.StabShape

namespace Formalism.L2.SG.Pf.ProdEApprox

section Gen

variable {E K : Type*} [Field E] [CommRing K] {r : ℕ}

theorem zLoc_mono (ι : E →+* K) (cj : K →+* K) (Dd : Fin (r + 1) → K) (σ : Fin (r + 1) → Fin (r + 1))
    (ν : Fin (r + 1) → E) :
    zLoc ι cj Dd (mono σ ν) = mono σ (fun a => Dd (σ a) * cj (Dd a) * ι (ν a)) := by
  ext a b
  simp only [zLoc, mono, Matrix.of_apply]
  split_ifs with h
  · subst h; rfl
  · simp

theorem zhatOM_mono (σ : Fin (r + 1) → Fin (r + 1)) (ν : Fin (r + 1) → E) :
    ZhatOM (mono σ ν) = mono σ (fun a => (-1) ^ (r - (σ a).val) * ν a) := by
  ext a b
  simp only [ZhatOM, mono, Matrix.of_apply]
  split_ifs with h
  · subst h; rfl
  · simp

theorem linG_mono {F : Type*} [Field F] [Algebra F K] (e : K ≃ₐ[F] F × F) (q : F) {σ : Fin (r + 1) → Fin (r + 1)}
    (hσ : ∀ a, σ (σ a) = a) (ν : Fin (r + 1) → K) :
    linG e q (mono σ ν) = mono σ (fun a => e.symm ((e (ν a)).1 / q, -((e (ν (σ a))).2 / q))) := by
  ext a b
  simp only [linG, mono, Matrix.of_apply]
  by_cases h : b = σ a
  · subst h
    rw [if_pos rfl, if_pos (hσ a).symm, if_pos rfl]
  · have h' : ¬ a = σ b := fun h' => h (by rw [h', hσ])
    rw [if_neg h, if_neg h', if_neg h]
    simp

theorem fix_single {K : Type*} [CommRing K] {l ρ : Matrix (Fin (r + 1)) (Fin (r + 1)) K} (hl : IsLoUni l)
    (hρ : IsUpUni ρ) (κ : K) :
    l * Matrix.single (Fin.last r) (Fin.last r) κ * ρ = Matrix.single (Fin.last r) (Fin.last r) κ := by
  ext x y
  rw [mul_single_mul]
  have h1 : l x (Fin.last r) = if x = Fin.last r then 1 else 0 := by
    by_cases hx : x = Fin.last r
    · subst hx; rw [if_pos rfl]; exact (hl _ _).2 rfl
    · rw [if_neg hx]; exact (hl _ _).1 (lt_of_le_of_ne (Fin.le_last x) hx)
  have h2 : ρ (Fin.last r) y = if y = Fin.last r then 1 else 0 := by
    by_cases hy : y = Fin.last r
    · subst hy; rw [if_pos rfl]; exact (hρ _ _).2 rfl
    · rw [if_neg hy]; exact (hρ _ _).1 (lt_of_le_of_ne (Fin.le_last y) hy)
  rw [h1, h2, Matrix.single_apply]
  by_cases hx : x = Fin.last r <;> by_cases hy : y = Fin.last r
  · subst hx; subst hy; simp
  · simp [hy, Ne.symm hy]
  · simp [hx, Ne.symm hx]
  · simp [hx, Ne.symm hx]

theorem fix_of_fix {K : Type*} [CommRing K] {l ρ N : Matrix (Fin (r + 1)) (Fin (r + 1)) K} (hl : IsLoUni l)
    (hρ : IsUpUni ρ) (κ : K) (h : l * (N - Matrix.single (Fin.last r) (Fin.last r) κ) * ρ =
      N - Matrix.single (Fin.last r) (Fin.last r) κ) : l * N * ρ = N := by
  rw [Matrix.mul_sub, Matrix.sub_mul, fix_single hl hρ] at h
  exact sub_left_injective h

end Gen

section Rec

open Formalism.L2.SG.CntLocal

variable {D : D7} (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (u u' : D.what₂.Word)

theorem zzp_mono {p : PlF D} (hA : Agree δ M p) {σ : Fin (D.R.rS + 1) → Fin (D.R.rS + 1)} (hσ : ∀ a, σ (σ a) = a)
    (ν : Fin (D.R.rS + 1) → D.host.E) (hν : ∀ a, ν a ≠ 0) :
    ∃ ν' : Fin (D.R.rS + 1) → (D.s.atP p).Ep, (∀ a, IsUnit (ν' a)) ∧ ∃ κ : (D.s.atP p).Ep,
      ZZP (M := M) δ u u' p (mono σ ν) = mono σ ν' - Matrix.single (Fin.last D.R.rS) (Fin.last D.R.rS) κ := by
  set cj : (D.s.atP p).Ep →+* (D.s.atP p).Ep := ((M p).L.cj : (D.s.atP p).Ep →+* (D.s.atP p).Ep)
  have hu : ∀ a, IsUnit (frFac δ p (σ a) * cj (frFac δ p a) * (D.s.atP p).ιE (ν a)) := fun a =>
    ((frFac_unit δ M hA (σ a)).mul ((frFac_unit δ M hA a).map cj)).mul ((isUnit_iff_ne_zero.2 (hν a)).map _)
  cases h : (M p).split with
  | none =>
    refine ⟨fun a => frFac δ p (σ a) * cj (frFac δ p a) * (D.s.atP p).ιE (ν a), hu, 0, ?_⟩
    rw [zzp_none δ M u u' h, zLoc_mono, Matrix.single_zero, sub_zero]
  | some g =>
    refine ⟨fun a => g.e.symm ((g.e (frFac δ p (σ a) * cj (frFac δ p a) * (D.s.atP p).ιE (ν a))).1 / (g.q : (D.s.atP p).Fp),
      -((g.e (frFac δ p (σ (σ a)) * cj (frFac δ p (σ a)) * (D.s.atP p).ιE (ν (σ a)))).2 / (g.q : (D.s.atP p).Fp))),
      fun a => ?_, g.e.symm (-(((D.mem u).A.T : ℕ) : (D.s.atP p).Fp) / (g.q : (D.s.atP p).Fp),
          (((D.mem u').A.T : ℕ) : (D.s.atP p).Fp) / (g.q : (D.s.atP p).Fp)), ?_⟩
    · have hq := q_ne M g
      have h1 := (Prod.isUnit_iff.1 ((hu a).map g.e)).1
      have h2 := (Prod.isUnit_iff.1 ((hu (σ a)).map g.e)).2
      refine IsUnit.map g.e.symm (Prod.isUnit_iff.2 ⟨?_, ?_⟩)
      · exact isUnit_iff_ne_zero.2 (div_ne_zero h1.ne_zero hq)
      · exact isUnit_iff_ne_zero.2 (neg_ne_zero.2 (div_ne_zero h2.ne_zero hq))
    · rw [zzp_some δ M u u' h, zLoc_mono, linG_mono _ _ hσ]

end Rec

end Formalism.L2.SG.Pf.ProdEApprox
end
end

section

noncomputable section

open IsDedekindDomain NumberField ValuativeRel Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.StabShape

namespace Formalism.L2.SG.Pf.ProdEApprox

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Good

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1))

theorem ring_inverse_eq {K : Type*} [CommRing K] {x y : K} (h : x * y = 1) : Ring.inverse x = y := by
  have hx : IsUnit x := ⟨⟨x, y, h, by rw [mul_comm]; exact h⟩, rfl⟩
  calc Ring.inverse x = Ring.inverse x * (x * y) := by rw [h, mul_one]
    _ = y := by rw [← mul_assoc, Ring.inverse_mul_cancel _ hx, one_mul]

theorem cj_mem_O {p : PlF D} {x : (D.s.atP p).Ep} (hx : x ∈ (D.s.atP p).O) : (D.s.atP p).cj x ∈ (D.s.atP p).O := by
  rw [(D.s.atP p).O_def] at hx ⊢
  exact hx.map (((D.s.atP p).cj.toAlgHom).restrictScalars 𝒪[(D.s.atP p).Fp])

theorem lOf_ρOf_int {p : PlF D} (hA : Agree δ M p) (hs : (M p).split = none)
    (hδ : δ p ∈ 𝒪[(D.s.atP p).Fp] ∧ (δ p)⁻¹ ∈ 𝒪[(D.s.atP p).Fp])
    (huP : (D.s.atP p).ιE (uP p : D.host.E) ∈ (D.s.atP p).O ∧ (D.s.atP p).ιE ((uP p : D.host.E)⁻¹) ∈ (D.s.atP p).O)
    (a b : Formalism.L2.SG.PairVal.MatR D) (ha : ∀ i j, (D.s.atP p).ιE (a i j) ∈ (D.s.atP p).O)
    (hb : ∀ i j, (D.s.atP p).ιE (b i j) ∈ (D.s.atP p).O) :
    (∀ i j, lOf δ M p a b i j ∈ (D.s.atP p).O) ∧ ∀ i j, ρOf δ M p a b i j ∈ (D.s.atP p).O := by
  obtain ⟨-, hδ0, hcj, -, -, -⟩ := hA
  set Op := (D.s.atP p).O
  set c : (D.s.atP p).Ep := algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p) * (D.s.atP p).ιE (uP p : D.host.E)
  set ci : (D.s.atP p).Ep := algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p)⁻¹ * (D.s.atP p).ιE ((uP p : D.host.E)⁻¹)
  have hcO : c ∈ Op := Op.mul_mem (alg_mem_O hδ.1) huP.1
  have hciO : ci ∈ Op := Op.mul_mem (alg_mem_O hδ.2) huP.2
  have hcc : c * ci = 1 := by
    have h1 : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p) * algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p)⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hδ0, map_one]
    have h2 : (D.s.atP p).ιE (uP p : D.host.E) * (D.s.atP p).ιE ((uP p : D.host.E)⁻¹) = 1 := by
      rw [← map_mul, mul_inv_cancel₀ (unitAt_ne p), map_one]
    calc c * ci = (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p) * algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p)⁻¹) *
          ((D.s.atP p).ιE (uP p : D.host.E) * (D.s.atP p).ιE ((uP p : D.host.E)⁻¹)) := by ring
      _ = 1 := by rw [h1, h2, mul_one]
  have hfr : ∀ i, frFac δ p i = ci ^ (D.R.rS - i.val) := fun i => by
    unfold frFac
    exact ring_inverse_eq (by rw [← mul_pow, hcc, one_pow])
  have hfri : ∀ i, Ring.inverse (frFac δ p i) = c ^ (D.R.rS - i.val) := fun i => by
    rw [hfr]; exact ring_inverse_eq (by rw [← mul_pow, mul_comm, hcc, one_pow])
  have hcjfr : ∀ i, ((M p).L.cj : (D.s.atP p).Ep →+* (D.s.atP p).Ep) (frFac δ p i) =
      (D.s.atP p).cj ci ^ (D.R.rS - i.val) := fun i => by
    rw [hfr, hcj]; simp
  have hcjfri : ∀ i, Ring.inverse (((M p).L.cj : (D.s.atP p).Ep →+* (D.s.atP p).Ep) (frFac δ p i)) =
      (D.s.atP p).cj c ^ (D.R.rS - i.val) := fun i => by
    rw [hcjfr]
    refine ring_inverse_eq ?_
    rw [← mul_pow, ← map_mul, mul_comm, hcc, map_one, one_pow]
  have hs1 : ∀ x : D.host.E, (D.s.atP p).ιE x ∈ Op → (D.s.atP p).ιE ((-1) ^ (D.R.rS - 0) * x) ∈ Op := fun x hx => by
    rw [map_mul]; exact Op.mul_mem (by rw [map_pow, map_neg, map_one]; exact Op.pow_mem (Op.neg_mem Op.one_mem) _) hx
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · simp only [lOf, hs, lL, Matrix.of_apply]
    rw [hcjfr, hcjfri]
    exact Op.mul_mem (Op.mul_mem (Op.pow_mem (cj_mem_O hciO) _) (ha i j)) (Op.pow_mem (cj_mem_O hcO) _)
  · simp only [ρOf, hs, ρL, Matrix.of_apply]
    rw [hfri, hfr]
    refine Op.mul_mem (Op.mul_mem (Op.pow_mem hcO _) ?_) (Op.pow_mem hciO _)
    rw [map_mul, map_mul]
    have hpm : ∀ k : ℕ, (D.s.atP p).ιE ((-1 : D.host.E) ^ k) ∈ Op := fun k => by
      rw [map_pow, map_neg, map_one]; exact Op.pow_mem (Op.neg_mem Op.one_mem) _
    exact Op.mul_mem (Op.mul_mem (hpm _) (hb i j)) (hpm _)

end Good

end Formalism.L2.SG.Pf.ProdEApprox
end
end
