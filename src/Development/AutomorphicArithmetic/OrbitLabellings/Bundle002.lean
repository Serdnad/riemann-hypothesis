module

public import Development.AutomorphicArithmetic.OrbitLabellings.RowDefs
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle001
public import Formalism.LocalToGlobal.CharacterGerms.RowTieAdm
public import Formalism.LocalToGlobal.CharacterGerms.RowTieJet
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd

@[expose] public section

section

open Formalism.L2.FormalSeriesBounds UpperTheory.G2


open Formalism.IncomingBounds in
private theorem cut (K s B : ℕ) (e : ℕ → ℕ) : ∃ pc : Fin s → ℕ → ℕ,
    (∀ u, ∑ k ∈ Finset.Icc 1 K, pc u k ≤ B) ∧
    (∑ k ∈ Finset.Icc 1 K, e k ≤ s * B → (∀ k, e k ≠ 0 → 1 ≤ k ∧ k ≤ K) → ∀ k, ∑ u, pc u k = e k) := by
  by_cases h : ∑ k ∈ Finset.Icc 1 K, e k ≤ s * B
  · obtain ⟨pc, h1, h2, h3⟩ := GlobalTheory.exists_cut_columns_bounded_width K s B e h
    refine ⟨pc, h2, fun _ hs k => ?_⟩
    by_cases hk : k ∈ Finset.Icc 1 K
    · exact h1 k hk
    · have : e k = 0 := by
        by_contra h0
        exact hk (Finset.mem_Icc.2 (hs k h0))
      rw [this]
      exact Finset.sum_eq_zero fun u _ => h3 u k hk
  · exact ⟨fun _ _ => 0, by simp, fun h' => absurd h' h⟩


open Formalism.IncomingBounds in
private theorem monAl_le_first (K rk : ℕ) (e : ℕ → ℕ) (ρ : ℕ) :
    monAl K rk e ρ ≤ ∑ k ∈ Finset.Icc 1 K, e k := by
  unfold monAl
  apply Finset.sum_le_sum_of_subset
  intro k hk
  rw [Finset.mem_Icc] at hk ⊢
  exact ⟨le_trans (Nat.le_add_left 1 ρ) hk.1, le_trans hk.2 (min_le_left _ _)⟩

theorem UpperTheory.pkgZeroCs_nu_nonpos_of_monSupply :
    RF.MONSupply → ∀ (P : RF.Par) (l : ℕ) (Pk : PkgZeroCs P l), Pk.ν ≤ 0 := by
  intro hM P l Pk
  have hl : Pk.R.V.l = l := Pk.R.hVl
  have hl2 : 2 ≤ l := hl ▸ Pk.R.V.l_prime.two_le
  have hc := fun (o : ↥Pk.Z) (σ : ZMod (2 * P.d)) => cut Pk.K Pk.s (l - 1) (Pk.ga o σ)
  choose pc hpcB hpcE using hc
  have hE : ∀ o σ k, ∑ u, pc o σ u k = Pk.ga o σ k := fun o σ =>
    hpcE o σ (Pk.first o σ) (fun k hk => ⟨(Pk.supp o σ k hk).1, (Pk.supp o σ k hk).2.2⟩)
  let blk : ↥Pk.Z → ZMod (2 * P.d) → Fin Pk.s → RF.GlobalTheory (2 * P.d) := fun o σ u =>
    RF.GlobalTheory.mon 0 (fun a k => if a = σ then pc o σ u k else 0) Pk.K
  let L : ↥Pk.Z → List (RF.GlobalTheory (2 * P.d) × ℝ) := fun o =>
    (Finset.univ : Finset (ZMod (2 * P.d) × Fin Pk.s)).toList.map (fun p => (blk o p.1 p.2, (0 : ℝ)))
  have hmem : ∀ o, ∀ q ∈ L o, ∃ σ u, q = (blk o σ u, (0 : ℝ)) := by
    intro o q hq
    obtain ⟨p, -, rfl⟩ := List.mem_map.1 hq
    exact ⟨p.1, p.2, rfl⟩
  have hzero : ∑ o, (List.map Prod.snd (L o)).sum = 0 := by
    apply Finset.sum_eq_zero
    intro o _
    simp [L]
  rw [← hzero]
  apply Pk.val L
  · intro o q hq
    obtain ⟨σ, u, rfl⟩ := hmem o q hq
    apply (hM _ _ _ _ _ (Pk.R.X o) (Pk.R.F o) 0 _ Pk.K).2
    intro a ρ
    rw [hl]
    calc monAl Pk.K ((Pk.R.X o).rkF 0 a) (fun k => if a = σ then pc o σ u k else 0) ρ
        ≤ ∑ k ∈ Finset.Icc 1 Pk.K, (fun k => if a = σ then pc o σ u k else 0) k := monAl_le_first _ _ _ _
      _ ≤ l - 1 := by
        by_cases ha : a = σ
        · simp only [ha, if_true]
          exact hpcB o σ u
        · simp [ha]
      _ < l := by omega
  · intro o q hq g e N hqe
    obtain ⟨σ, u, rfl⟩ := hmem o q hq
    obtain ⟨-, rfl, -⟩ := RF.GlobalTheory.mon.inj hqe
    exact ⟨σ, fun a k ha => if_neg ha⟩
  · have hrow : ∀ o, (List.map (fun q => RF.GlobalTheory.what₂ (Pk.R.X o).n q.1) (L o)).sum = 2 * P.d * Pk.s * Pk.K := by
      intro o
      simp [L, blk, RF.GlobalTheory.what₂]
    simp only [hrow]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, smul_eq_mul]
    calc 2 * (Pk.Z.card * (2 * P.d * Pk.s * Pk.K)) = 4 * Pk.K * Pk.s * (Pk.Z.card * P.d) := by ring
      _ ≤ Pk.nW := Pk.what₂
  · intro o s k
    simp [L, blk, RF.GlobalTheory.wt]
    split_ifs with hk
    · rw [Fintype.sum_prod_type, Finset.sum_eq_single s]
      · simp [hE]
      · intro b _ hb
        simp [Ne.symm hb]
      · intro hs
        exact absurd (Finset.mem_univ s) hs
    · by_contra hne
      have h3 := Pk.supp o s k (Ne.symm hne)
      exact hk ⟨h3.1, h3.2.2, h3.2.1⟩
end

section

open scoped BigOperators
open Classical
open Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.RF UpperTheory.G2 NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem UpperTheory.valBlocksS_of_blkMemS :
    ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (d : ℕ) [NeZero d] (hd : ZMod d), hd + hd = 0 →
    ∀ (Orb : Type) [Fintype Orb] (I J : Orb → Fin 2 → Type) [∀ o g, Fintype (I o g)] [∀ o g, Fintype (J o g)]
    (X : ∀ o, RowData C V d (I o) (J o)) (n : ℕ) (FFimg : Set (∀ o, MvPolynomial (Fin n × WV (I o)) C)) (ν : ℝ),
    ValO X n FFimg ν → ∀ (F : ∀ o, RF.Flag (X o)) (nW : ℕ), nW ≤ 2 * n + 1 → ∀ ga : Orb → ZMod d → ℕ → ℕ,
    PlaneBlockProductsMemFamily hd X n F FFimg ga → (∀ o, (X o).Alt) → (∀ o, (X o).j' < (X o).n) →
    (∀ o s, (X o).rkF 1 (s + hd) = (X o).rkF 0 s) → (∀ o s k, ga o s k ≠ 0 → k ≤ (X o).rkF 0 s) →
    ValBlocksS hd X F nW ga ν := by
  intro C _ _ V d _ hd hhd Orb _ I J _ _ X n FFimg ν hV F nW hnW ga hMem hAlt hj hrk hga
  intro L hAtt hOne hRows hWt
  have hwt : ∀ o, ∀ q ∈ L o, ∀ (g : Fin 2) (a : ZMod d) (k : ℕ),
      GlobalTheory.wt (X o) q.1 g a k ≠ 0 → k ≤ (X o).rkF g a := by
    intro o q hq g a k hne
    fin_cases g
    · have hle : GlobalTheory.wt (X o) q.1 0 a k + GlobalTheory.wt (X o) q.1 1 (a + hd) k ≤ ga o a k := by
        rw [← hWt o a k]
        exact le_sum_map (L o) (fun q => GlobalTheory.wt (X o) q.1 0 a k + GlobalTheory.wt (X o) q.1 1 (a + hd) k) hq
      apply hga o a k
      have : GlobalTheory.wt (X o) q.1 0 a k ≠ 0 := hne
      omega
    · have hs : a + hd + hd = a := by rw [add_assoc, hhd, add_zero]
      have hle : GlobalTheory.wt (X o) q.1 0 (a + hd) k + GlobalTheory.wt (X o) q.1 1 (a + hd + hd) k ≤ ga o (a + hd) k := by
        rw [← hWt o (a + hd) k]
        exact le_sum_map (L o)
          (fun q => GlobalTheory.wt (X o) q.1 0 (a + hd) k + GlobalTheory.wt (X o) q.1 1 (a + hd + hd) k) hq
      rw [hs] at hle
      have hne' : GlobalTheory.wt (X o) q.1 1 a k ≠ 0 := hne
      have h0 : ga o (a + hd) k ≠ 0 := by omega
      have := hga o (a + hd) k h0
      rw [← hrk o (a + hd), hs] at this
      exact this
  have hOK : ∀ o, ∀ q ∈ L o, GlobalTheory.AttainsOK (X o) (F o) q.1 q.2 := fun o q hq =>
    attainsOK_of (X o) (F o) (Or.inl (hAlt o)) (hj o) q.1 q.2 (hwt o q hq) (hAtt o q hq)
  have hsum : ∑ o, (List.map (fun q => GlobalTheory.what₂ (X o).n q.1) (L o)).sum ≤ n := by omega
  exact val_lists hV jetProd F L hOK hsum (hMem L hOne hWt)
end
