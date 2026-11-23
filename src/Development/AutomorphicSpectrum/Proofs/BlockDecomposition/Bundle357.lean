module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle335
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle302
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle339
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCompactCosetSet
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanCriterion.Zj
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanNecTemp
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle342
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.ProdGPn

@[expose] public section

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG GlobalTheory.CompanionTheory.BZPhiPG.OntoO Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPhiPG.OntoO.Avg

variable {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup W] [Module ℂ W]

def evL (H : Subgroup G) (ρ : Representation ℂ H W) (g : G) : cIndSpace H ρ →ₗ[ℂ] W :=
  (LinearMap.proj g) ∘ₗ (indSpace H ρ).subtype ∘ₗ (smoothPart (ind H ρ)).subtype ∘ₗ (cIndSpace H ρ).subtype

theorem bump_right_inv {H : Subgroup G} {ρ : Representation ℂ H W} {K : Subgroup G} {v : W} {b : cIndSpace H ρ}
    (hb : IsBump H ρ K 1 v b) (g z : G) (hz : z ∈ K) : b.1.1.1 (g * z) = b.1.1.1 g := by
  by_cases h : ∃ a : H, ∃ x ∈ K, g = (a : G) * 1 * x
  · obtain ⟨a, x, hx, rfl⟩ := h
    rw [hb.1 a x hx, mul_assoc, hb.1 a (x * z) (mul_mem hx hz)]
  · rw [hb.2 g h, hb.2]
    rintro ⟨a, x, hx, e⟩
    exact h ⟨a, x * z⁻¹, mul_mem hx (inv_mem hz), by rw [← mul_assoc, ← e]; group⟩

theorem sum_translate {M : Type} [AddCommMonoid M] (K₁ K₂ : Subgroup G) (h₂₁ : K₂ ≤ K₁) (φ : G → M)
    (hφ : ∀ g, ∀ z ∈ K₂, φ (g * z) = φ g) [Fintype (K₁ ⧸ K₂.subgroupOf K₁)] (y : K₁) :
    ∑ x : K₁ ⧸ K₂.subgroupOf K₁, φ ((y : G) * ((x.out : K₁) : G)) =
      ∑ x : K₁ ⧸ K₂.subgroupOf K₁, φ ((x.out : K₁) : G) := by
  have key : ∀ k : K₁, φ ((((k : K₁ ⧸ K₂.subgroupOf K₁).out : K₁)) : G) = φ (k : G) := by
    intro k
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (K₂.subgroupOf K₁) k
    rw [hh]
    exact hφ _ _ h.2
  calc ∑ x : K₁ ⧸ K₂.subgroupOf K₁, φ ((y : G) * ((x.out : K₁) : G))
      = ∑ x : K₁ ⧸ K₂.subgroupOf K₁, φ (((MulAction.toPerm y x).out : K₁) : G) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        have e : MulAction.toPerm y x = ((y * x.out : K₁) : K₁ ⧸ K₂.subgroupOf K₁) := by
          conv_lhs => rw [← QuotientGroup.out_eq' x]
          rfl
        rw [e, key]
        rfl
    _ = ∑ x : K₁ ⧸ K₂.subgroupOf K₁, φ ((x.out : K₁) : G) :=
        Equiv.sum_comp (MulAction.toPerm y) (fun x : K₁ ⧸ K₂.subgroupOf K₁ => φ ((x.out : K₁) : G))

theorem bump_mem_of_bump {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup W] [Module ℂ W]
    (H : Subgroup G) (ρ : Representation ℂ H W) (K₁ K₂ : Subgroup G) (h₂₁ : K₂ ≤ K₁)
    (hK₁c : IsCompact (K₁ : Set G)) (hK₂o : IsOpen (K₂ : Set G)) (v : W)
    (hv : ∀ a : H, (a : G) ∈ K₁ → ρ a v = v) (S : Submodule ℂ (cIndSpace H ρ))
    (hS : ∀ g, ∀ b ∈ S, cInd H ρ g b ∈ S) (b : cIndSpace H ρ) (hb : IsBump H ρ K₂ 1 v b) (hbS : b ∈ S)
    (B : cIndSpace H ρ) (hB : IsBump H ρ K₁ 1 v B) : B ∈ S := by
  classical
  haveI : CompactSpace K₁ := isCompact_iff_compactSpace.1 hK₁c
  haveI : Finite (K₁ ⧸ K₂.subgroupOf K₁) :=
    Subgroup.quotient_finite_of_isOpen _ (hK₂o.preimage continuous_subtype_val)
  letI : Fintype (K₁ ⧸ K₂.subgroupOf K₁) := Fintype.ofFinite _
  set T : cIndSpace H ρ := ∑ x : K₁ ⧸ K₂.subgroupOf K₁, cInd H ρ ((x.out : K₁) : G) b with hT
  have hTS : T ∈ S := S.sum_mem fun x _ => hS _ _ hbS
  have hTv : ∀ g, T.1.1.1 g = ∑ x : K₁ ⧸ K₂.subgroupOf K₁, b.1.1.1 (g * ((x.out : K₁) : G)) := by
    intro g
    have e : evL H ρ g T = ∑ x : K₁ ⧸ K₂.subgroupOf K₁, evL H ρ g (cInd H ρ ((x.out : K₁) : G) b) := by

      rw [hT, map_sum]
    exact e
  have hTr : ∀ g, ∀ y ∈ K₁, T.1.1.1 (g * y) = T.1.1.1 g := by
    intro g y hy
    rw [hTv, hTv]
    have := sum_translate K₁ K₂ h₂₁ (fun u => b.1.1.1 (g * u))
      (fun u z hz => by
        show b.1.1.1 (g * (u * z)) = b.1.1.1 (g * u)
        rw [← mul_assoc]; exact bump_right_inv hb _ z hz) ⟨y, hy⟩
    simpa only [mul_assoc] using this
  let P : K₁ ⧸ K₂.subgroupOf K₁ → Prop := fun x => ∃ a : H, ∃ z ∈ K₂, ((x.out : K₁) : G) = (a : G) * 1 * z
  have hval : ∀ x, b.1.1.1 ((x.out : K₁) : G) = if P x then v else 0 := by
    intro x
    by_cases hx : P x
    · rw [if_pos hx]
      obtain ⟨a, z, hz, e⟩ := hx
      have ha : (a : G) ∈ K₁ := by
        have : (a : G) = ((x.out : K₁) : G) * z⁻¹ := by rw [e]; group
        rw [this]
        exact mul_mem (x.out).2 (inv_mem (h₂₁ hz))
      rw [e, hb.1 a z hz, hv a ha]
    · rw [if_neg hx]
      exact hb.2 _ hx
  set N : ℕ := (Finset.univ.filter P).card with hN
  have hT1 : T.1.1.1 1 = (N : ℂ) • v := by
    rw [hTv]
    simp only [one_mul, hval]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, Nat.cast_smul_eq_nsmul]
  have hN0 : (N : ℂ) ≠ 0 := by
    have : N ≠ 0 := by
      rw [hN, Finset.card_ne_zero]
      refine ⟨((1 : K₁) : K₁ ⧸ K₂.subgroupOf K₁), Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩⟩
      obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (K₂.subgroupOf K₁) (1 : K₁)
      refine ⟨1, ((h : K₁) : G), h.2, ?_⟩
      rw [hh]
      simp
    exact_mod_cast this
  have hBT : B = (N : ℂ)⁻¹ • T := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    funext g
    show B.1.1.1 g = (N : ℂ)⁻¹ • T.1.1.1 g
    by_cases hg : ∃ a : H, ∃ x ∈ K₁, g = (a : G) * 1 * x
    · obtain ⟨a, y, hy, rfl⟩ := hg
      have e1 : T.1.1.1 ((a : G) * 1 * y) = ρ a ((N : ℂ) • v) := by
        rw [hTr _ y hy, mul_one, ← hT1]
        have := T.1.1.2 a 1
        rwa [mul_one] at this
      rw [hB.1 a y hy, e1, map_smul, smul_smul, inv_mul_cancel₀ hN0, one_smul]
    · have e1 : T.1.1.1 g = 0 := by
        rw [hTv]
        refine Finset.sum_eq_zero fun x _ => hb.2 _ ?_
        rintro ⟨a, z, hz, e⟩
        refine hg ⟨a, z * ((x.out : K₁) : G)⁻¹, mul_mem (h₂₁ hz) (inv_mem (x.out).2), ?_⟩
        rw [← mul_assoc, ← e]
        group
      rw [hB.2 g hg, e1, smul_zero]
  rw [hBT]
  exact S.smul_mem _ hTS

end GlobalTheory.CompanionTheory.BZPhiPG.OntoO.Avg

end
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG GlobalTheory.CompanionTheory.BZPhiPG.OntoO Topology
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.CompanionTheory.BZPhiPG.OntoO

variable {k : Type} [Field k]

theorem sEmb_mul_row (n : ℕ) (m : Mir k n) (q : Mir k (n + 1)) (j : Fin (n + 1 + 1)) :
    (((sEmb (k := k) n m * q : Mir k (n + 1)) : GL (Fin (n + 1 + 1)) k) : Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) k)
        (Fin.castSucc (Fin.last n)) j =
      ((q : GL (Fin (n + 1 + 1)) k) : Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) k) (Fin.castSucc (Fin.last n)) j := by
  have hm : ((m : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) =
      GlobalTheory.BZMir.eLast k n :=
    (GlobalTheory.BZMir.mem_Mir_iff k (m : GL (Fin (n + 1)) k)).1 m.2
  have hm' : ∀ x, ((m : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) x =
      GlobalTheory.BZMir.eLast k n x := fun x => congrFun hm x
  have he : (((GlobalTheory.CompanionTheory.BZPhiPG.sEmb (k := k) n m : GlobalTheory.BZMir.Mir k (n + 1)) : GL (Fin (n + 1 + 1)) k) :
      Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) k) =
      GlobalTheory.BZMir.glEmbMat k (n + 1) ((m : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) :=
    rfl
  simp only [Subgroup.coe_mul, Units.val_mul]
  rw [he, Matrix.mul_apply, Fin.sum_univ_castSucc]
  simp only [GlobalTheory.BZMir.glEmbMat, Fin.lastCases_castSucc, Fin.lastCases_last, hm', zero_mul,
    add_zero, GlobalTheory.BZMir.eLast]
  simp [Pi.single_apply]

end GlobalTheory.CompanionTheory.BZPhiPG.OntoO
end

theorem GlobalTheory.CompanionTheory.BZPhiPG.OntoO.Cl_mul_sO (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) :
    ∀ p ∈ Cl (k := k) i t, ∀ m, p * sO k i t m ∈ Cl (k := k) i t := by
  intro p hp m
  have key : ∀ j, (((GlobalTheory.CompanionTheory.BZPhiPG.OntoO.sO k i t m⁻¹ * p⁻¹ : GlobalTheory.BZMir.Mir k (i + 1 + t + 1)) :
      GL (Fin (i + 1 + t + 1 + 1)) k) : Matrix (Fin (i + 1 + t + 1 + 1)) (Fin (i + 1 + t + 1 + 1)) k)
        (Fin.castSucc (Fin.last (i + 1 + t))) j =
      (((p⁻¹ : GlobalTheory.BZMir.Mir k (i + 1 + t + 1)) : GL (Fin (i + 1 + t + 1 + 1)) k) :
        Matrix (Fin (i + 1 + t + 1 + 1)) (Fin (i + 1 + t + 1 + 1)) k) (Fin.castSucc (Fin.last (i + 1 + t))) j :=
    fun j => GlobalTheory.CompanionTheory.BZPhiPG.OntoO.sEmb_mul_row (i + 1 + t)
      (GlobalTheory.CompanionTheory.BZPhiPG.castM k (by omega) m⁻¹) p⁻¹ j
  simp only [GlobalTheory.CompanionTheory.BZPhiPG.Cl, Set.mem_setOf_eq] at hp ⊢
  intro c
  rw [_root_.mul_inv_rev, ← map_inv (GlobalTheory.CompanionTheory.BZPhiPG.OntoO.sO k i t) m]
  exact (key _).trans (hp c)
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG GlobalTheory.CompanionTheory.BZPhiPG.OntoO Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPhiPG.OntoO

theorem mem_of_bumps {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup W] [Module ℂ W]
    (H : Subgroup G) (ρ : Representation ℂ H W) (K : Subgroup G) (hKo : IsOpen (K : Set G))
    (hKc : IsCompact (K : Set G)) (y : cIndSpace H ρ) (hy : ∀ g, ∀ x ∈ K, y.1.1.1 (g * x) = y.1.1.1 g)
    (S : Submodule ℂ (cIndSpace H ρ)) (hS : ∀ c B, IsBump H ρ K c (y.1.1.1 c) B → B ∈ S) : y ∈ S := by
  classical
  obtain ⟨C, hC, hsupp⟩ := y.2
  have hyeq : ∀ (a : H) (g : G), y.1.1.1 ((a : G) * g) = ρ a (y.1.1.1 g) := y.1.1.2
  obtain ⟨t, -, ht⟩ := hC.elim_nhds_subcover (fun c => (fun x => c * x) '' (K : Set G)) (fun c _ => by
    have : (fun y => c⁻¹ * y) ⁻¹' (K : Set G) ∈ 𝓝 c :=
      (hKo.preimage (continuous_const.mul continuous_id)).mem_nhds (by simp [one_mem])
    filter_upwards [this] with y hy
    exact ⟨c⁻¹ * y, hy, by group⟩)
  let T : Finset (DoubleCoset.Quotient (H : Set G) (K : Set G)) := t.image (DoubleCoset.mk H K)
  have hres := fun d : DoubleCoset.Quotient (H : Set G) (K : Set G) =>
    GlobalTheory.CompanionTheory.LeibPhi.exists_indicator H ρ (GlobalTheory.CompanionTheory.LeibPhi.isHK_doubleCoset H K hKo (Quotient.out d)) y
  choose f hf1 hf0 using hres
  have hbump : ∀ d, IsBump H ρ K (Quotient.out d) (y.1.1.1 (Quotient.out d)) (f d) := by
    intro d
    refine ⟨fun a x hx => ?_, fun g hg => hf0 d g ?_⟩
    · rw [hf1 d _ ⟨a, a.2, x, hx, rfl⟩, hy _ x hx, hyeq]
    · rintro ⟨a, ha, x, hx, e⟩
      exact hg ⟨⟨a, ha⟩, x, hx, e⟩
  have hoff : ∀ (d : DoubleCoset.Quotient (H : Set G) (K : Set G)) (g : G), DoubleCoset.mk H K g ≠ d →
      (f d).1.1.1 g = 0 := by
    intro d g hne
    apply hf0
    rintro ⟨a, ha, x, hx, e⟩
    apply hne
    rw [← DoubleCoset.out_eq' d]
    exact ((@DoubleCoset.eq _ _ H K _ _).2 ⟨a, ha, x, hx, e⟩).symm
  have hmem : ∑ d ∈ T, f d ∈ S := S.sum_mem fun d _ => hS _ _ (hbump d)
  have hval : ∀ g, y.1.1.1 g = (∑ d ∈ T, f d).1.1.1 g := by
    intro g
    let ev : cIndSpace H ρ →ₗ[ℂ] W :=
      (LinearMap.proj g) ∘ₗ (indSpace H ρ).subtype ∘ₗ (smoothPart (ind H ρ)).subtype ∘ₗ (cIndSpace H ρ).subtype
    have hsum : (∑ d ∈ T, f d).1.1.1 g = ∑ d ∈ T, (f d).1.1.1 g := map_sum ev _ _
    rw [hsum]
    by_cases hg : DoubleCoset.mk H K g ∈ T
    · rw [Finset.sum_eq_single_of_mem _ hg (fun d _ hd => hoff d g (Ne.symm hd))]
      obtain ⟨a, ha, x, hx, e⟩ := (@DoubleCoset.eq _ _ H K _ _).1 (DoubleCoset.out_eq' (DoubleCoset.mk H K g))
      exact (hf1 _ g ⟨a, ha, x, hx, e⟩).symm
    · rw [Finset.sum_eq_zero (fun d hd => hoff d g (fun h => hg (h ▸ hd)))]
      by_contra hne
      obtain ⟨a, ha, c', hc', e⟩ := hsupp g hne
      obtain ⟨c, hc, hcc⟩ := Set.mem_iUnion₂.1 (ht hc')
      obtain ⟨x, hx, rfl⟩ := hcc
      apply hg
      have : DoubleCoset.mk H K c = DoubleCoset.mk H K g :=
        (@DoubleCoset.eq _ _ H K _ _).2 ⟨a, ha, x, hx, by rw [e]; group⟩
      rw [← this]
      exact Finset.mem_image_of_mem _ hc
  have e : y = ∑ d ∈ T, f d := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    funext g
    exact hval g
  rw [e]
  exact hmem

end GlobalTheory.CompanionTheory.BZPhiPG.OntoO

end
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG GlobalTheory.CompanionTheory.BZPhiPG.OntoO Topology
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPhiPG.OntoO

theorem continuous_castM (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {a b : ℕ} (h : a = b) : Continuous (castM k h) := by
  subst h
  exact continuous_id

theorem continuous_sO : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (i t : ℕ), Continuous (sO k i t) := by
  intro k _ _ _ _ i t
  exact (GlobalTheory.CompanionTheory.BZPhiPG.EcSmooth.continuous_sEmb k ((i + 1) + t)).comp (continuous_castM k _)

end GlobalTheory.CompanionTheory.BZPhiPG.OntoO
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG GlobalTheory.CompanionTheory.BZPsiPG.FibKer
open scoped TensorProduct

noncomputable section

open ValuativeRel

namespace GlobalTheory.CompanionTheory.BZPsiPG.FibKer

section Exhaust

variable {k : Type} [Field k] [ValuativeRel k]

theorem Lc_le_Lc_mul (n : ℕ) (c : k) {d : k} (hd : d ∈ 𝒪[k]) : Lc n c ≤ Lc n (c * d) := by
  intro y hy j
  have h : c * d * y.toAdd j = d * (c * y.toAdd j) := by ring
  rw [h]
  exact mul_mem hd (hy j)

theorem exists_integral_mul (y : k) : ∃ c : k, c ∈ 𝒪[k] ∧ c ≠ 0 ∧ c * y ∈ 𝒪[k] := by
  by_cases hy : y ∈ 𝒪[k]
  · exact ⟨1, one_mem _, one_ne_zero, by rwa [one_mul]⟩
  · have hy0 : y ≠ 0 := fun h => hy (h ▸ zero_mem _)
    refine ⟨y⁻¹, ?_, inv_ne_zero hy0, ?_⟩
    · rw [Valuation.mem_integer_iff] at hy ⊢
      rw [map_inv₀]
      exact inv_le_one_of_one_le₀ (le_of_lt (not_le.1 hy))
    · rw [inv_mul_cancel₀ hy0]
      exact one_mem _

theorem exists_mem_Lc (n : ℕ) (y : Multiplicative (Fin n → k)) :
    ∃ c : k, c ∈ 𝒪[k] ∧ c ≠ 0 ∧ y ∈ Lc n c := by
  choose f hf hf0 hfy using fun j => exists_integral_mul (y.toAdd j)
  refine ⟨∏ j, f j, prod_mem fun j _ => hf j, Finset.prod_ne_zero_iff.2 fun j _ => hf0 j, ?_⟩
  intro j
  have h : (∏ i, f i) * y.toAdd j = (∏ i ∈ Finset.univ.erase j, f i) * (f j * y.toAdd j) := by
    rw [← Finset.prod_erase_mul Finset.univ f (Finset.mem_univ j)]
    ring
  rw [h]
  exact mul_mem (prod_mem fun i _ => hf i) (hfy j)

variable {X : Type} [AddCommGroup X] [Module ℂ X]

theorem twKer_Lc_mono {n : ℕ} (ρ : Representation ℂ (Multiplicative (Fin n → k)) X) (c : k) {d : k}
    (hd : d ∈ 𝒪[k]) : twKer ρ (Lc n c) 1 ≤ twKer ρ (Lc n (c * d)) 1 := by
  refine Submodule.span_mono ?_
  rintro w ⟨m, v, rfl⟩
  exact ⟨⟨m.1, Lc_le_Lc_mul n c hd m.2⟩, v, rfl⟩

theorem exists_mem_twKer_Lc {n : ℕ} (ρ : Representation ℂ (Multiplicative (Fin n → k)) X) {x : X}
    (hx : x ∈ twKer ρ ⊤ 1) : ∃ c : k, c ∈ 𝒪[k] ∧ c ≠ 0 ∧ x ∈ twKer ρ (Lc n c) 1 := by
  induction hx using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨m, v, rfl⟩ := hw
    obtain ⟨c, hc, hc0, hm⟩ := exists_mem_Lc n m.1
    exact ⟨c, hc, hc0, Submodule.subset_span ⟨⟨m.1, hm⟩, v, rfl⟩⟩
  | zero => exact ⟨1, one_mem _, one_ne_zero, zero_mem _⟩
  | add a b _ _ ha hb =>
    obtain ⟨c, hc, hc0, hca⟩ := ha
    obtain ⟨d, hd, hd0, hdb⟩ := hb
    refine ⟨c * d, mul_mem hc hd, mul_ne_zero hc0 hd0, add_mem (twKer_Lc_mono ρ c hd hca) ?_⟩
    rw [mul_comm c d]
    exact twKer_Lc_mono ρ d hc hdb
  | smul a b _ hb =>
    obtain ⟨c, hc, hc0, hcb⟩ := hb
    exact ⟨c, hc, hc0, Submodule.smul_mem _ a hcb⟩

theorem exists_integral_finite_twKer_Lc {n : ℕ} (ρ : Representation ℂ (Multiplicative (Fin n → k)) X)
    {S : Set X} (hS : S.Finite) (h : ∀ x ∈ S, x ∈ twKer ρ ⊤ 1) :
    ∃ c : k, c ∈ 𝒪[k] ∧ c ≠ 0 ∧ ∀ x ∈ S, x ∈ twKer ρ (Lc n c) 1 := by
  induction S, hS using Set.Finite.induction_on with
  | empty => exact ⟨1, one_mem _, one_ne_zero, fun x hx => absurd hx (Set.notMem_empty x)⟩
  | @insert a s _ _ ih =>
    obtain ⟨c, hc, hc0, hcs⟩ := ih fun x hx => h x (Set.mem_insert_of_mem a hx)
    obtain ⟨d, hd, hd0, hda⟩ := exists_mem_twKer_Lc ρ (h a (Set.mem_insert a s))
    refine ⟨c * d, mul_mem hc hd, mul_ne_zero hc0 hd0, ?_⟩
    rintro x (rfl | hx)
    · rw [mul_comm c d]
      exact twKer_Lc_mono ρ d hc hda
    · exact twKer_Lc_mono ρ c hd (hcs x hx)

end Exhaust

theorem exists_Lc_finite_twKer :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) {X : Type} [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ (Multiplicative (Fin n → k)) X) (S : Set X), S.Finite → (∀ x ∈ S, x ∈ twKer ρ ⊤ 1) → ∃ c : k, c ≠ 0 ∧ ∀ x ∈ S, x ∈ twKer ρ (Lc n c) 1 := by
  intro k _ _ _ _ n X _ _ ρ S hS h
  obtain ⟨c, -, hc0, hc⟩ := exists_integral_finite_twKer_Lc ρ hS h
  exact ⟨c, hc0, hc⟩

end GlobalTheory.CompanionTheory.BZPsiPG.FibKer
end
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG GlobalTheory.CompanionTheory.BZPsiPG.FibKer
open scoped TensorProduct

noncomputable section

open ValuativeRel Topology Uniformity GlobalTheory.CompanionTheory.BZPsiPG.FibKer

namespace GlobalTheory.CompanionTheory.BZPsiPG.FibKer.LatInv

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_inv_integer_subset {W : Set k} (hW : W ∈ 𝓝 (0 : k)) :
    ∃ c : k, c ≠ 0 ∧ ∀ x, c * x ∈ 𝒪[k] → x ∈ W := by
  obtain ⟨γ, hγ⟩ := (IsValuativeTopology.mem_nhds_zero_iff _).1 hW
  obtain ⟨a, ha⟩ := ValuativeRel.valuation_surjective (γ : ValueGroupWithZero k)
  obtain ⟨w, hw0, hw1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation k)
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp only [map_zero] at ha
    exact γ.ne_zero ha.symm
  have hd : a * w ≠ 0 := mul_ne_zero ha0 hw0
  refine ⟨(a * w)⁻¹, inv_ne_zero hd, fun x hx => hγ ?_⟩
  have h1 : valuation k ((a * w)⁻¹ * x) ≤ 1 := hx
  have h2 : valuation k x = valuation k (a * w) * valuation k ((a * w)⁻¹ * x) := by
    rw [← map_mul, mul_inv_cancel_left₀ hd]
  show valuation k x < γ
  calc valuation k x = valuation k (a * w) * valuation k ((a * w)⁻¹ * x) := h2
    _ ≤ valuation k (a * w) * 1 := mul_le_mul_right h1 _
    _ = γ * valuation k w := by rw [mul_one, map_mul, ha]
    _ < γ * 1 := mul_lt_mul_of_pos_left hw1 (zero_lt_iff.mpr γ.ne_zero)
    _ = γ := mul_one _

theorem exists_Lc_subset (t : ℕ) {W : Set (Fin t → k)} (hW : W ∈ 𝓝 (0 : Fin t → k)) :
    ∃ c : k, c ≠ 0 ∧ ∀ o ∈ Lc t c, o.toAdd ∈ W := by
  rw [nhds_pi, Filter.mem_pi] at hW
  obtain ⟨I, -, s, hs, hsub⟩ := hW
  have hU : (⋂ j, s j) ∈ 𝓝 (0 : k) := Filter.iInter_mem.2 hs
  obtain ⟨c, hc, h⟩ := exists_inv_integer_subset hU
  exact ⟨c, hc, fun o ho => hsub fun j _ => Set.mem_iInter.1 (h _ (ho j)) j⟩

theorem exists_Lc_invariant : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (t : ℕ) {Z : Type} [AddCommGroup Z] [Module ℂ Z] (φ : (Fin t → k) → Z), IsLocallyConstant φ → HasCompactSupport φ → ∃ c : k, c ≠ 0 ∧ ∀ o ∈ Lc t c, ∀ v, φ (v + o.toAdd) = φ v := by
  intro k _ _ _ _ t Z _ _ φ hl hc
  letI uG : UniformSpace (Fin t → k) := IsTopologicalAddGroup.rightUniformSpace _
  haveI : IsUniformAddGroup (Fin t → k) := isUniformAddGroup_of_addCommGroup
  letI uZ : UniformSpace Z := ⊥
  have huc : UniformContinuous φ := hc.uniformContinuous_of_continuous hl.continuous
  have hmem : {p : (Fin t → k) × (Fin t → k) | φ p.1 = φ p.2} ∈ 𝓤 (Fin t → k) := by
    have h0 : {q : Z × Z | q.1 = q.2} ∈ 𝓤 Z := by
      show _ ∈ 𝓤[(⊥ : UniformSpace Z)]
      rw [bot_uniformity]
      exact Filter.mem_principal_self _
    exact huc h0
  rw [uniformity_eq_comap_nhds_zero, Filter.mem_comap] at hmem
  obtain ⟨W, hW, hsub⟩ := hmem
  obtain ⟨c, hc0, h⟩ := exists_Lc_subset t hW
  refine ⟨c, hc0, fun o ho v => ?_⟩
  have hv : (v, v + o.toAdd) ∈ (fun x : (Fin t → k) × (Fin t → k) => x.2 - x.1) ⁻¹' W := by
    show v + o.toAdd - v ∈ W
    rw [add_sub_cancel_left]
    exact h o ho
  exact (hsub hv).symm

end GlobalTheory.CompanionTheory.BZPsiPG.FibKer.LatInv

end
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

theorem _root_.GlobalTheory.T.pi_tensor_central_block_scalar : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ∀ {h : ℕ} (x : Fin h → IrrGL (k := k)) (t : kˣ) (c : Fin h → ℂ), (∀ i, Zl.ScalarBy (x i) t (c i)) → ∀ (j : Fin h) (v : PiTensorProduct ℂ (fun a => (x a).2.rep.V)), piTensor (fun a => (x a).rep) (Zl.JC.zj (fun a => (x a).1) t j) v = (∏ i ∈ Finset.univ.filter (· ≤ j), c i) • v := by
  first | exact @GlobalTheory.CompanionTheory.JCScalar.piTensor_zj | exact GlobalTheory.CompanionTheory.JCScalar.piTensor_zj | (intros; apply GlobalTheory.CompanionTheory.JCScalar.piTensor_zj <;> assumption)
end
