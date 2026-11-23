module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.Bundle009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.MapsBc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ThetaCoefficientMapEq
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.Bundle010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.SinfIso
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.Bundle006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.Bundle002
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

theorem UpperTheory.V.Pa.BC.aut_bc :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (n : ℕ) (O O' : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] [Algebra ℤ_[l] O] [CommRing O'] [IsLocalRing O'] [Algebra ℤ_[l] O'] [Algebra O O'] [IsScalarTower ℤ_[l] O O'] [IsLocalHom (algebraMap O O')] [Module.Finite O O'] [Module.Free O O'] (r : Resid G0.frame O n) (r' : Resid G0.frame O' n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] [IsCO O' (Til O O' B)] (u : Pair r B) (u' : Pair r' (Til O O' B)) (J : Ideal B) (D : ℕ) (T : TWGrp G0) (_A : TWAut u J Empty D T), RBC r r' → u.Maps (Til.ι O O' B) u'.D u'.ψ → ∃ A' : TWAut u' (J.map (Til.ι O O' B)) Unit D T, A'.b.lam (MvPowerSeries.X (.inl ())) = Til.s O O' B := by
  intro l _ L G0 n O O' _ _ _ _ _ _ _ _ _ _ _ _ _ r r' B _ _ _ _ u u' J D T A hr hu
  obtain ⟨τ, hτ, hs⟩ := UpperTheory.V.Pa.BC.til_lam O O' D
  obtain ⟨τS, hS⟩ := UpperTheory.V.Pa.BC.sinf_iso l O O' D T.q n τ hτ
  obtain ⟨b', hb⟩ := UpperTheory.V.Pa.BC.base_bc l L G0 n O O' r r' B u u' J D A.b τ hr hu hτ
  have hA := fun N => UpperTheory.V.Pa.BC.ring_bc l L G0 n O O' r r' B u u' J D A.b b' τ (T.GN N) (T.h N) T.q A.ut N τS
    (A.A N) hr hu hb hS
  choose A' hA' using hA
  have hm := fun N => UpperTheory.V.Pa.BC.maps_bc l L G0 n O O' r r' B u u' J D A.b b' τ (T.GN N) (T.h N) T.q A.ut N τS
    (A.A N) (A' N) (T.Nq N) (T.ph N) (T.ta N) A.ex (A.m N) hr hu hb hS (hA' N)
  refine ⟨⟨b', fun j i => algebraMap O O' (A.ut j i), ?_, A', A.ex, fun N => (hm N).some⟩, ?_⟩
  · intro j i
    rw [hr.1 i, ← ResidueField.map_residue, A.ut_res]
    rfl
  · obtain ⟨hb⟩ := hb
    show b'.lam _ = _
    rw [← hs, hb.lam, Til.map_s]
end

section

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

private theorem mem_closureIdeal_of_mem {A G : Type} [CommRing A] [Group G] [TopologicalSpace G] (I : Ideal A)
    (S : Set (MonoidAlgebra A G)) (x : MonoidAlgebra A G) (hx : x ∈ S) : x ∈ closureIdeal I S := by
  unfold closureIdeal
  simp only [TwoSidedIdeal.mem_iInf]
  intro N H
  exact TwoSidedIdeal.subset_span (Or.inl (Or.inl hx))

theorem UpperTheory.V.Pa.BC.mem_span_map_e0ker_of_pair_maps :
    ∀ (l : ℕ) [Fact l.Prime] (F : GFrame l) (O O' : Type) [CommRing O] [IsLocalRing O] [Finite (ResidueField O)] [CharP (ResidueField O) l] [Algebra ℤ_[l] O] [CommRing O'] [IsLocalRing O'] [Algebra ℤ_[l] O'] (n : ℕ) (r : Resid F O n) (r' : Resid F O' n) (B B' : Type) [CommRing B] [Algebra O B] [IsCO O B] [CommRing B'] [Algebra O' B'] [IsCO O' B'] (u : Pair r B) (u' : Pair r' B') (g : B →+* B') [IsLocalHom g], PhiCond F.G₀ l → (∀ w, r'.Ip w = r.Ip w) → (∀ a : ℤ_[l], g (algebraMap O B (algebraMap ℤ_[l] O a)) = algebraMap O' B' (algebraMap ℤ_[l] O' a)) → u.Maps g u'.D u'.ψ → ∀ z ∈ augmentationIdealKernel u', z ∈ TwoSidedIdeal.span (MonoidAlgebra.mapRingHom F.G₀ g '' augmentationIdealKernel u) := by
  intro l _ F O O' _ _ _ _ _ _ _ _ n r r' B B' _ _ _ _ _ _ u u' g _ hPhi hIp hg hM z hz
  obtain ⟨hD, hψ⟩ := hM
  haveI : CompactSpace F.G₀ :=
    isCompact_iff_compactSpace.mp (Subgroup.isClosed_of_isOpen _ F.η_open).isCompact
  obtain ⟨hfin, ⟨χ, h, hmap, hmf⟩, -⟩ := BC.pair_mf l F O n r B u hPhi
  haveI := hfin
  obtain ⟨-, hstar, hoEl⟩ := BC.star_map l F O O' B B' g hg
  have hz' : z ∈ (u.D.map g).chBar (pairGens u') := by
    rw [hD]
    exact hz
  have hψ' : ∀ v, u'.ψ v = fun i => pushCh g (u.ψ v i) := fun v => funext fun i => (hψ v i).symm
  have hin : ∀ x ∈ pairGens u, MonoidAlgebra.mapRingHom F.G₀ g x ∈
      TwoSidedIdeal.span (MonoidAlgebra.mapRingHom F.G₀ g '' {y | y ∈ u.D.chBar (pairGens u)}) :=
    fun x hx => TwoSidedIdeal.subset_span ⟨x, mem_closureIdeal_of_mem _ _ x (Or.inr hx), rfl⟩
  refine BC.closure_bc n h B B' F.G₀ u.D χ u.cont hmap hmf g (pairGens u) (pairGens u') ?_ z hz'
  intro y hy
  rcases hy with ⟨v, γ, hy | hy⟩ | ⟨w, γ, hγ, hy | hy⟩
  · have e := hin (F.oEl v (u.ψ v) γ) (Or.inl ⟨v, γ, Or.inl rfl⟩)
    rwa [hoEl, ← hψ', ← hy] at e
  · have e := hin (F.star O B n (F.oEl v (u.ψ v) γ)) (Or.inl ⟨v, γ, Or.inr rfl⟩)
    rwa [hstar, hoEl, ← hψ', ← hy] at e
  · rw [hIp] at hγ
    have e := hin (MonoidAlgebra.single γ 1 - 1) (Or.inr ⟨w, γ, hγ, Or.inl rfl⟩)
    rwa [map_sub, map_one, MonoidAlgebra.mapRingHom_single, map_one, ← hy] at e
  · rw [hIp] at hγ
    have e := hin (F.star O B n (MonoidAlgebra.single γ 1) - 1) (Or.inr ⟨w, γ, hγ, Or.inr rfl⟩)
    rwa [map_sub, map_one, hstar, MonoidAlgebra.mapRingHom_single, map_one, ← hy] at e
end
