module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle007
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle009
public import Formalism.SharpRestriction.CuspSpanNormBounds.NormalizedLocalScale
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle259
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle219
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle143
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle033
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeOfLatMod
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle204
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle163
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicLeviEmbeddingHomomorphismProperties
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicStabilizerRadicalStructure
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentLeviRadicalCoordsHomeomorph
import Formalism.FormalDegreeBessel.FinalG
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetInFamilyMovedOfNotLeak
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GFrames
public import Mathlib.Algebra.Module.Lattice.Full
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle097
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle112
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianLatticeMassEqFinprodLocal
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle068
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Countable
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.DegCnt.FixIdx

section

variable {R V : Type} [CommRing R] [AddCommGroup V] [Module R V]

theorem idx_inf_le (A B C W : Submodule R V) (hAB : A ≤ B) (hAW : A ≤ W) (h : idx B C ≠ 0) :
    idx A (C ⊓ W) ≠ 0 ∧ idx A (C ⊓ W) ≤ idx B C := by
  have e : idx A (C ⊓ W) = idx A C := by
    unfold idx
    rw [← AddSubgroup.inf_relIndex_right (C ⊓ W).toAddSubgroup, ← AddSubgroup.inf_relIndex_right C.toAddSubgroup]
    congr 1
    ext x
    exact ⟨fun hx => ⟨hx.1.1, hx.2⟩, fun hx => ⟨⟨hx.1, hAW hx.2⟩, hx.2⟩⟩
  rw [e]
  have hle : A.toAddSubgroup ≤ B.toAddSubgroup := hAB
  exact ⟨fun h0 => h (AddSubgroup.relIndex_eq_zero_of_le_right hle h0),
    AddSubgroup.relIndex_le_of_le_right hle h⟩

theorem gens_of_sup (A C D : Submodule R V) (hD : A ⊓ C ≤ D) (hDA : D ≤ A) (e : ℕ) (t : Finset V)
    (ht : t.card ≤ e) (h : A ⊔ C = C ⊔ Submodule.span R (t : Set V)) :
    ∃ t' : Finset V, t'.card ≤ e ∧ A = D ⊔ Submodule.span R (t' : Set V) := by
  have h1 : ∀ x : V, ∃ a : V, x ∈ t → a ∈ A ∧ x - a ∈ C := by
    intro x
    by_cases hx : x ∈ t
    · have : x ∈ A ⊔ C := by rw [h]; exact Submodule.mem_sup_right (Submodule.subset_span hx)
      obtain ⟨a, ha, c, hc, rfl⟩ := Submodule.mem_sup.1 this
      exact ⟨a, fun _ => ⟨ha, by simpa using hc⟩⟩
    · exact ⟨0, fun h => absurd h hx⟩
  choose f hf using h1
  have hsA : Submodule.span R ((t.image f : Finset V) : Set V) ≤ A := by
    rw [Submodule.span_le]
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
    exact (hf x hx).1
  refine ⟨t.image f, Finset.card_image_le.trans ht, le_antisymm ?_ (sup_le hDA hsA)⟩
  have h2 : A ≤ C ⊔ Submodule.span R ((t.image f : Finset V) : Set V) := by
    refine le_trans (le_sup_left (b := C)) ?_
    rw [h]
    refine sup_le le_sup_left (Submodule.span_le.2 fun x hx => ?_)
    have : x = (x - f x) + f x := by abel
    rw [SetLike.mem_coe, this]
    exact Submodule.add_mem_sup (hf x hx).2
      (Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_image_of_mem f hx)))
  intro x hx
  obtain ⟨c, hc, s, hs, rfl⟩ := Submodule.mem_sup.1 (h2 hx)
  refine Submodule.add_mem_sup (hD ⟨?_, hc⟩) hs
  simpa using A.sub_mem hx (hsA hs)

end

section

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]


omit [StarRing K] in
theorem isLatMod_of_idx (A B : Submodule (𝓞 K) V) (S I : Submodule K V) (hA : IsLatMod A S I) (hBA : B ≤ A)
    (hI : rs (𝓞 K) I ≤ B) (h : idx A B ≠ 0) : IsLatMod B S I := by
  obtain ⟨⟨M, hM, hL⟩, hsp⟩ := hA
  refine ⟨⟨B ⊓ M, ?_, ?_⟩, le_antisymm ?_ ?_⟩
  · haveI : IsNoetherian (𝓞 K) M := isNoetherian_of_fg_of_noetherian _ hM
    exact isNoetherian_submodule.1 this _ inf_le_right
  · rw [inf_sup_assoc_of_le _ hI, ← hL]
    exact (inf_eq_left.2 hBA).symm
  · rw [← hsp]; exact Submodule.span_mono hBA
  · rw [← hsp, Submodule.span_le]
    intro x hx
    have h1 : (idx A B) • x ∈ B := AddSubgroup.nsmul_relIndex_mem B.toAddSubgroup (K := A.toAddSubgroup) hx
    have h2 : ((idx A B : K))⁻¹ • ((idx A B) • x) ∈ Submodule.span K (B : Set V) :=
      Submodule.smul_mem _ _ (Submodule.subset_span h1)
    rwa [← Nat.cast_smul_eq_nsmul K, smul_smul, inv_mul_cancel₀ (Nat.cast_ne_zero.2 h), one_smul] at h2

variable [FiniteDimensional K V] {H : HermSpace K V} {r : ℕ}

theorem radical (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (N : NF H r) :
    II N.F N.F' ≤ wSp N.F N.F' ∧
      ∀ x ∈ wSp N.F N.F', (∀ y ∈ wSp N.F N.F', H.B x y = 0) ↔ x ∈ II N.F N.F' := by
  obtain ⟨-, -, -, -, -, -, hw, -, hPD, -⟩ := GlobalTheory.T.hermFramePairNormalForm_geometry_summary K V H hK r N
  have h2 : ∀ x ∈ N.Wt ⊔ II N.F N.F', ∀ y ∈ II N.F N.F', H.B y x = 0 := by
    intro x hx y hy
    rw [← hw] at hx
    rw [← H.herm, (mem_perp_iff H _ x).1 hx y (Submodule.mem_sup_left (Submodule.mem_sup_left hy.1)),
      star_zero]
  rw [hw]
  refine ⟨le_sup_right, fun x hx => ⟨fun hx0 => ?_, fun hxI y hy => h2 y hy x hxI⟩⟩
  obtain ⟨a, ha, i, hi, rfl⟩ := Submodule.mem_sup.1 hx
  have haa := hx0 a (Submodule.mem_sup_left ha)
  rw [map_add (f := _), LinearMap.add_apply, h2 a (Submodule.mem_sup_left ha) i hi, add_zero] at haa
  obtain ⟨τ⟩ : Nonempty (K →+* ℂ) := inferInstance
  have ha0 : a = 0 := by
    by_contra hne
    have := hPD τ ⟨a, ha⟩ (fun h => hne (congrArg Subtype.val h))
    have e : GlobalTheory.Mass.hRes H.B.flip N.Wt ⟨a, ha⟩ ⟨a, ha⟩ = H.B a a := rfl
    rw [e, haa] at this
    simp at this
  rw [ha0, zero_add]; exact hi

end

theorem main : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → latTh N.F N.F' Λ ≤ latLa N.F N.F' Λ (g : 𝓞 K) ∧ 0 < N.gI g Λ ∧ 0 < N.iI g Λ ∧ (N.gI g Λ : ℝ) * (N.iI g Λ : ℝ) ^ 2 * (N.bI Λ : ℝ) ^ 2 ≤ N.Del ∧ ((N.gI g Λ : ℝ) * N.iI g Λ ≤ N.Del) ∧ GenBy (flagPairDefinitePartLattice N.F N.F' Λ) (latLa N.F N.F' Λ (g : 𝓞 K)) N.j ∧ _root_.GlobalTheory.HermLat.del H (latTh N.F N.F' Λ) = (N.gI g Λ : ℝ) * N.iI g Λ * N.NT ∧ IsLatMod (latTh N.F N.F' Λ) (wSp N.F N.F') (II N.F N.F') := by
  intro K V _ _ _ _ _ _ _ _ H hK r N g Λ hg hΛ
  obtain ⟨hb0, -, hDel, hbar⟩ := GlobalTheory.T.normal_form_terminal_determinant K V H hK r N g Λ hg hΛ
  obtain ⟨hnB, -, h1L, hB, t, ht, hgen⟩ := GlobalTheory.T.flagPairInnerLattice_indices_and_generators K V H hK r N g Λ hg hΛ
  obtain ⟨hd0, -, -, hlat0, -⟩ := GlobalTheory.T.flagPairDefinitePartLattice_discriminant_eq_quotient K V H hK r N g Λ hg hΛ
  obtain ⟨hIW, hrad⟩ := radical hK N
  have hww : wSp N.F' N.F = wSp N.F N.F' := by
    unfold wSp V0
    rw [sup_comm N.F'.X, Set.pair_comm]
  have hn0 : idx (latL N.F N.F' Λ) (lamOne N.F N.F' Λ) ≠ 0 := by
    intro h0
    rw [h0] at hnB
    simp only [Nat.cast_zero, zero_mul] at hnB
    linarith
  have hB0 : cardB N.F N.F' Λ ≠ 0 := by
    intro h0
    rw [h0] at hnB
    simp only [Nat.cast_zero, mul_zero] at hnB
    linarith
  have hThLa : latTh N.F N.F' Λ ≤ latLa N.F N.F' Λ (g : 𝓞 K) := by
    intro x hx
    refine ⟨⟨⟨(h1L hx.1).2, by rw [hww]; exact hx.2⟩, ⟨(h1L hx.1).1, hx.2⟩⟩, ?_⟩
    obtain ⟨l, hl, i, hi, rfl⟩ := Submodule.mem_sup.1 hx.1.1
    refine Submodule.mem_sup.2 ⟨(l, l), ⟨⟨hl.1, hl.1⟩, ?_⟩, (i, i), ⟨hi.2, hi.1⟩, rfl⟩
    simp
  have hLa0 : latLa N.F N.F' Λ (g : 𝓞 K) ≤ flagPairDefinitePartLattice N.F N.F' Λ := fun x hx => hx.1.2
  have hLaL : latLa N.F N.F' Λ (g : 𝓞 K) ≤ latL N.F N.F' Λ ⊓ latL N.F' N.F Λ :=
    fun x hx => ⟨hx.1.2.1, hx.1.1.1⟩
  have hmul : N.iI g Λ * N.gI g Λ = idx (flagPairDefinitePartLattice N.F N.F' Λ) (latTh N.F N.F' Λ) :=
    AddSubgroup.relIndex_mul_relIndex _ _ _ hThLa hLa0
  obtain ⟨hp0, hpn⟩ : idx (flagPairDefinitePartLattice N.F N.F' Λ) (latTh N.F N.F' Λ) ≠ 0 ∧
      idx (flagPairDefinitePartLattice N.F N.F' Λ) (latTh N.F N.F' Λ) ≤ idx (latL N.F N.F' Λ) (lamOne N.F N.F' Λ) :=
    idx_inf_le _ _ _ _ inf_le_left inf_le_right hn0
  have hq0 : idx (latL N.F N.F' Λ ⊓ latL N.F' N.F Λ) (lamOne N.F N.F' Λ) ≠ 0 := fun h0 =>
    hn0 (AddSubgroup.relIndex_eq_zero_of_le_right
      (show (latL N.F N.F' Λ ⊓ latL N.F' N.F Λ).toAddSubgroup ≤ (latL N.F N.F' Λ).toAddSubgroup from
        fun x hx => hx.1) h0)
  have hiB : N.iI g Λ ≤ cardB N.F N.F' Λ :=
    (idx_inf_le _ _ _ (rs (𝓞 K) (wSp N.F N.F')) hLaL (hLa0.trans inf_le_right) hq0).2.trans hB
  have hi0 : N.iI g Λ ≠ 0 := fun h0 => hp0 (by rw [← hmul, h0, zero_mul])
  have hg0 : N.gI g Λ ≠ 0 := fun h0 => hp0 (by rw [← hmul, h0, mul_zero])
  have hmulR : (N.gI g Λ : ℝ) * N.iI g Λ = idx (flagPairDefinitePartLattice N.F N.F' Λ) (latTh N.F N.F' Λ) := by
    rw [← hmul]; push_cast; ring
  have hmain : (N.gI g Λ : ℝ) * (N.iI g Λ : ℝ) ^ 2 * (N.bI Λ : ℝ) ^ 2 ≤ N.Del := by
    rw [← hDel, ← hnB, sq (N.iI g Λ : ℝ), ← mul_assoc, hmulR]
    have e1 : (idx (flagPairDefinitePartLattice N.F N.F' Λ) (latTh N.F N.F' Λ) : ℝ) ≤ idx (latL N.F N.F' Λ) (lamOne N.F N.F' Λ) := by
      exact_mod_cast hpn
    have e2 : (N.iI g Λ : ℝ) ≤ cardB N.F N.F' Λ := by exact_mod_cast hiB
    gcongr
  have hITh : rs (𝓞 K) (II N.F N.F') ≤ latTh N.F N.F' Λ := by
    intro x hx
    refine ⟨⟨Submodule.mem_sup_right hx, ?_⟩, hIW hx⟩
    exact (mem_perp_iff H _ x).2 fun y hy => (mem_perp_iff H _ x).1 (hIW hx) y (Submodule.mem_sup_left hy)
  have hlat : IsLatMod (latTh N.F N.F' Λ) (wSp N.F N.F') (II N.F N.F') :=
    isLatMod_of_idx _ _ _ _ hlat0 (hThLa.trans hLa0) hITh hp0
  refine ⟨hThLa, Nat.pos_of_ne_zero hg0, Nat.pos_of_ne_zero hi0, hmain, le_trans ?_ hmain, ?_, ?_, hlat⟩
  · have e1 : (1 : ℝ) ≤ N.iI g Λ := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hi0
    have e2 : (1 : ℝ) ≤ N.bI Λ := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hb0
    calc (N.gI g Λ : ℝ) * N.iI g Λ = (N.gI g Λ : ℝ) * (N.iI g Λ * 1) * 1 ^ 2 := by ring
      _ ≤ (N.gI g Λ : ℝ) * (N.iI g Λ * N.iI g Λ) * (N.bI Λ : ℝ) ^ 2 := by gcongr
      _ = _ := by ring
  · have h1 : lamOne N.F N.F' Λ ≤ latL N.F N.F' Λ := h1L.trans inf_le_left
    obtain ⟨t', ht', h'⟩ := ((GlobalTheory.Mass.LatticeGens.gens_and_count K V _ _ h1 hn0).2 N.j t ht hgen).2
      (flagPairDefinitePartLattice N.F N.F' Λ ⊔ lamOne N.F N.F' Λ) le_sup_right (sup_le inf_le_left h1)
    exact gens_of_sup _ _ _
      (le_trans (show flagPairDefinitePartLattice N.F N.F' Λ ⊓ lamOne N.F N.F' Λ ≤ latTh N.F N.F' Λ from
        fun x hx => ⟨hx.2, hx.1.2⟩) hThLa) hLa0 N.j t' ht' h'
  · rw [(DelScale.main K V H hK _ _ _ _ hIW hrad hlat0 hlat).2.2.1, hd0, hmulR]
    have : idx (latTh N.F N.F' Λ) (flagPairDefinitePartLattice N.F N.F' Λ) = 1 :=
      AddSubgroup.relIndex_eq_one.2 (hThLa.trans hLa0)
    rw [gidx, this]
    simp

end GlobalTheory.DegCnt.FixIdx
end

section

noncomputable section

open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.RootNormal

variable {k r : ℕ}

theorem continuous_conj (a : Mat k r) : Continuous (conjM a : Mt k r → Mt k r) :=
  (continuous_const.matrix_mul (continuous_id (X := Mat k r))).matrix_mul continuous_const

theorem det_Hpk : IsUnit (Hpk k r).det :=
  Matrix.isUnit_det_of_right_inverse (hpkFacts k r).2.1

theorem unit_det {g : Mat k r} (hg : g ∈ GG k r) : IsUnit g.det :=
  ((uHGroup _ _ det_Hpk).2.2 g hg).1

theorem mem_S (z : Fin (2 * r + k + 1) → ℂ) {n : Mat k r} (hn : n ∈ Nset k r) : n ∈ Sset k r z :=
  ⟨1, ⟨(uHGroup _ _ det_Hpk).1, fun a => by simp, by simp⟩, n, hn, by simp⟩

theorem twoFl_of {z z' : Fin (2 * r + k + 1) → ℂ} {n n' g : Mat k r} (hn : n ∈ Nset k r) (hn' : n' ∈ Nset k r)
    (h : TwoFl k r z z' (n * g * n')) : TwoFl k r z z' g := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨h1, h2, h3, h4, ?_, ?_, ?_⟩
  · have G := uHGroup _ _ (det_Hpk (k := k) (r := r))
    have e : g = n⁻¹ * (n * g * n') * n'⁻¹ := by
      rw [Matrix.mul_assoc n, Matrix.nonsing_inv_mul_cancel_left _ _ (unit_det hn.1),
        Matrix.mul_nonsing_inv_cancel_right _ _ (unit_det hn'.1)]
    rw [e]
    exact G.2.1 _ (G.2.1 _ (G.2.2 _ hn.1).2 _ h5) _ (G.2.2 _ hn'.1).2
  · rwa [gInv k r z z' h1 h2 _ (mem_S z hn) _ (mem_S z' hn')] at h6
  · unfold Dr at h7 ⊢
    rwa [dInv k r z z' h1 h2 _ (mem_S z hn) _ (mem_S z' hn')] at h7

def patEquiv (p : Point ℂ (r + 1)) (h : ∀ a : Fin r, blockIdx p.1 a.val ≠ blockIdx p.1 r) :
    UTin (fun a : Fin r => blockIdx p.1 a.val) ≃ rootPat p :=
  Equiv.ofBijective
    (fun q => ⟨(q.1.1.1.castSucc, q.1.1.2.castSucc), by
      simp only [rootPat, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨Fin.castSucc_lt_castSucc_iff.2 q.1.2, q.2⟩⟩)
    (by
      constructor
      · rintro ⟨⟨⟨a, b⟩, h1⟩, h2⟩ ⟨⟨⟨c, d⟩, h3⟩, h4⟩ e
        simp only [Subtype.mk.injEq, Prod.mk.injEq, Fin.castSucc_inj] at e
        obtain ⟨rfl, rfl⟩ := e
        rfl
      · rintro ⟨⟨a, b⟩, hq⟩
        simp only [rootPat, Finset.mem_filter, Finset.mem_univ, true_and] at hq
        obtain ⟨h1, h2⟩ := hq
        have h1' : a.val < b.val := h1
        have ha : a.val < r := by omega
        have hb : b.val < r := by
          by_contra hb
          have : b.val = r := by omega
          exact h ⟨a.val, ha⟩ (h2.trans (congrArg (blockIdx p.1) this))
        exact ⟨⟨⟨(⟨a.val, ha⟩, ⟨b.val, hb⟩), h1'⟩, h2⟩, rfl⟩)

theorem card_le (p : Point ℂ (r + 1)) (h : ∀ a : Fin r, blockIdx p.1 a.val ≠ blockIdx p.1 r) :
    (rootPat p).card ≤ r ^ 2 := by
  rw [← Fintype.card_coe, ← Fintype.card_congr (patEquiv p h)]
  refine (Fintype.card_subtype_le _).trans ((Fintype.card_subtype_le _).trans ?_)
  simp [sq]

theorem measurable_rootCoords (z : Fin (2 * r + k + 1) → ℂ) (p : Point ℂ (r + 1)) :
    Measurable (rootCoords k r z p) := by
  refine Continuous.measurable (continuous_pi fun q => ?_)
  unfold rootCoords flagMat
  split_ifs
  · unfold Matrix.mulVec dotProduct
    simp only [Matrix.of_apply]
    fun_prop
  all_goals exact continuous_const

theorem measurable_in (β : Fin r → ℕ) :
    Measurable fun x : UTin β → ℂ => (Matrix.of.symm (uEmb k r (upperIn β x)) : Mt k r) := by
  have : Continuous fun x : UTin β → ℂ => uEmb k r (upperIn β x) := by
    refine (NCoord.cont_uEmb k r).comp (continuous_pi fun q => ?_)
    split_ifs
    · exact continuous_apply _
    · exact continuous_const
  exact (show Continuous (fun x : UTin β → ℂ => (Matrix.of.symm (uEmb k r (upperIn β x)) : Mt k r)) from this).measurable

theorem pOf_mem (q : PPar k r) : pOf k r q ∈ Nset k r :=
  (((Rad.radical k r).1 _ _).2.2.2 ((Rad.radical k r).2.1 _ _)).1

theorem pOf_e (q : PPar k r) (a : Fin r) : pOf k r q *ᵥ bvec (eI k r a) = bvec (eI k r a) :=
  ((Rad.radical k r).1 _ _).1 a

theorem pOf_inv_e (q : PPar k r) (a : Fin r) : (pOf k r q)⁻¹ *ᵥ bvec (eI k r a) = bvec (eI k r a) := by
  conv_lhs => rw [← pOf_e q a]
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (unit_det (pOf_mem q).1), Matrix.one_mulVec]

theorem conj_entry (q : PPar k r) (u : Matrix (Fin r) (Fin r) ℂ) (a b : Fin r) :
    (((pOf k r q)⁻¹ * uEmb k r u * pOf k r q) *ᵥ bvec (eI k r b)) (eI k r a) = u a b := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, pOf_e, UEmb.uEmb_eI, Matrix.mulVec_sum]
  simp only [Matrix.mulVec_smul, pOf_inv_e]
  simp [bvec, Pi.single_apply, UEmb.eI_inj, Finset.sum_apply]

theorem conj_mem {P Q g x : Mat k r} (hP : P ∈ Nset k r) (hQ : Q ∈ Nset k r) (hg : g ∈ GG k r) (hx : x ∈ Rset k r g) :
    P * x * P⁻¹ ∈ Rset k r (Q * g * P⁻¹) := by
  have N := nSubgroup k r
  refine ⟨N.2.1 _ (N.2.1 _ hP _ hx.1) _ (N.2.2 _ hP), ?_⟩
  have e : Q * g * P⁻¹ * (P * x * P⁻¹) * (Q * g * P⁻¹)⁻¹ = Q * (g * x * g⁻¹) * Q⁻¹ := by
    have hu := unit_det hP.1
    simp only [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hu, Matrix.mul_assoc,
      Matrix.nonsing_inv_mul_cancel_left _ _ hu]
  rw [e]
  exact N.2.1 _ (N.2.1 _ hQ _ hx.2) _ (N.2.2 _ hQ)

theorem eq_map (z' : Fin (2 * r + k + 1) → ℂ) (p : Point ℂ (r + 1))
    (h : ∀ a : Fin r, blockIdx p.1 a.val ≠ blockIdx p.1 r) {g : Mat k r} (hg : g ∈ GG k r) (p₁ p₀ : PPar k r)
    (hN : IsNormal k r (fun a => blockIdx p.1 a.val) (pOf k r p₁ * g * (pOf k r p₀)⁻¹))
    (μ : Measure (Mt k r)) (c : ℝ≥0∞) (h0 : μ {x | Matrix.of x ∉ Rset k r g} = 0)
    (h1 : μ.map (rootCoords k r z' p) = c • volume) :
    μ = (c • lebR k r (fun a => blockIdx p.1 a.val)).map (conjM (pOf k r p₀)⁻¹) := by
  set β : Fin r → ℕ := fun a => blockIdx p.1 a.val with hβ
  have hu := unit_det (pOf_mem p₀).1
  let E : (rootPat p → ℂ) → (UTin β → ℂ) := fun y q => y (patEquiv p h q)
  have hE : MeasurePreserving E volume volume :=
    (volume_measurePreserving_piCongrLeft (fun _ : rootPat p => ℂ) (patEquiv p h)).symm _
  have hF := measurable_in (k := k) β
  have hC := (continuous_conj (pOf k r p₀)⁻¹).measurable
  have hR := measurable_rootCoords z' p
  have key : ∀ x : Mt k r, Matrix.of x ∈ Rset k r g →
      conjM (pOf k r p₀)⁻¹ (Matrix.of.symm (uEmb k r (upperIn β (E (rootCoords k r z' p x))))) = x := by
    intro x hx
    have h2 := conj_mem (pOf_mem p₀) (pOf_mem p₁) hg hx
    rw [(GlobalTheory.T.commonStabilizer_normalForm_blockUnitriangular k r _ _ hN).1] at h2
    obtain ⟨y, hy⟩ := h2
    have hx' : Matrix.of x = (pOf k r p₀)⁻¹ * uEmb k r (upperIn β y) * pOf k r p₀ := by
      simp only at hy
      rw [hy]
      simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hu, Matrix.nonsing_inv_mul _ hu, Matrix.mul_one]
    have hy' : E (rootCoords k r z' p x) = y := by
      funext q
      change flagMat k r z' (Matrix.of x) q.1.1.1.castSucc q.1.1.2.castSucc = _
      unfold flagMat fvec
      rw [dif_pos (show q.1.1.1.castSucc.val < r from q.1.1.1.2), dif_pos (show q.1.1.2.castSucc.val < r from q.1.1.2.2), hx']
      refine (conj_entry p₀ _ q.1.1.1 q.1.1.2).trans ?_
      unfold upperIn upper
      rw [dif_pos q.1.2]
      exact dif_pos q.2
    rw [hy']
    unfold conjM
    rw [Matrix.nonsing_inv_nonsing_inv _ hu]
    exact hx'.symm
  have hae : (conjM (pOf k r p₀)⁻¹ ∘ (fun x : UTin β → ℂ => (Matrix.of.symm (uEmb k r (upperIn β x)) : Mt k r)) ∘ E ∘
      rootCoords k r z' p) =ᵐ[μ] id := by
    apply measure_mono_null _ h0
    intro x hx
    exact fun hx' => hx (key x hx')
  have := Measure.map_congr (mβ := inferInstance) hae
  rw [Measure.map_id, ← Measure.map_map hC (hF.comp (hE.measurable.comp hR)), ← Measure.map_map hF (hE.measurable.comp hR),
    ← Measure.map_map hE.measurable hR, h1] at this
  refine this.symm.trans ?_
  congr 1
  unfold lebR
  rw [Measure.map_smul c hE.measurable.aemeasurable, hE.map_eq, Measure.map_smul c hF.aemeasurable]

theorem rootMeas_normR : ∀ (D : D7) (z z' : (Fin (2 * D.R.rS + D.R.k + 1) → ℂ)) (p : Point ℂ (D.R.rS + 1)) (γ : MatKR D.R.k D.R.rS) (μR : Measure (Mt D.R.k D.R.rS)) (θ' : ℝ), TwoFl D.R.k D.R.rS z z' γ → IsRootMeasR D z z' p γ μR → 0 ≤ θ' → 0 ≤ D.host.ka / gg D → (rootPat p).card ≤ D.R.rS ^ 2 ∧ NormR D.R.k D.R.rS γ (θ' * (2 * D.host.ka / gg D / (2 * Real.pi)) ^ (rootPat p).card) (ENNReal.ofReal θ' • μR) := by
  intro D z z' p γ μR θ' hT hR hθ _
  obtain ⟨n, hn, n', hn', g, rfl, hZ, μ, h0, h1, rfl⟩ := hR
  have hg := twoFl_of hn hn' hT
  obtain ⟨p₁, p₀, -, hN, -, h⟩ := GlobalTheory.T.exists_radical_normalForm_pair_of_flags _ _ z z' g p hg hZ
  have N := nSubgroup D.R.k D.R.rS
  have hu₀ := unit_det (pOf_mem p₀).1
  have hu₁ := unit_det (pOf_mem p₁).1
  refine ⟨card_le p h, n * (pOf _ _ p₁)⁻¹, N.2.1 _ hn _ (N.2.2 _ (pOf_mem p₁)), pOf _ _ p₀ * n',
    N.2.1 _ (pOf_mem p₀) _ hn', _, _, hN, ?_, ?_⟩
  · simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hu₀, Matrix.nonsing_inv_mul_cancel_left _ _ hu₁]
  · have e1 : (fun x : Mt D.R.k D.R.rS => fun i j => (n'⁻¹ * Matrix.of x * n') i j) = conjM n'⁻¹ := by
      funext x
      unfold conjM
      rw [Matrix.nonsing_inv_nonsing_inv _ (unit_det hn'.1)]
    have e2 : (conjM (pOf _ _ p₀ * n')⁻¹ : Mt D.R.k D.R.rS → _) = conjM n'⁻¹ ∘ conjM (pOf _ _ p₀)⁻¹ := by
      funext x
      change (pOf _ _ p₀ * n')⁻¹ * Matrix.of x * (pOf _ _ p₀ * n')⁻¹⁻¹ =
        n'⁻¹ * ((pOf _ _ p₀)⁻¹ * Matrix.of x * (pOf _ _ p₀)⁻¹⁻¹) * n'⁻¹⁻¹
      simp only [Matrix.mul_inv_rev, Matrix.mul_assoc]
    rw [e1, e2, eq_map z' p h hg.2.2.2.2.1 p₁ p₀ hN μ _ h0 h1,
      Measure.map_map (continuous_conj _).measurable (continuous_conj _).measurable,
      ENNReal.ofReal_mul hθ, mul_smul, Measure.map_smul (ENNReal.ofReal θ')
        (((continuous_conj _).measurable.comp (continuous_conj _).measurable).aemeasurable)]

end GlobalTheory.Amp.RootNormal
end
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.hermitianDoubleCoset_inFamily_moved_of_not_leak : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (j : Fin r) (β βJ : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.InFF β (j + 1) βJ d Λ → ∀ x x' u s, S.IsMove (j + 1) d Λ x x' u s → (∃ y ∈ Λ, y ∈ S.W0 ∧ S.h u y = 1) → ∀ Λ₁ : Submodule L.O S.V, (Λ₁ : Set S.V) = S.moved Λ x u s → S.InFF β (j + 1) βJ d Λ₁ := by
  first | exact @GlobalTheory.HL.OffLeak.inFF_moved_of_not_leak | exact GlobalTheory.HL.OffLeak.inFF_moved_of_not_leak | (intros; apply GlobalTheory.HL.OffLeak.inFF_moved_of_not_leak <;> assumption)
end

section

open NumberField GlobalTheory.HL
open scoped Pointwise Classical

namespace GlobalTheory.HL.CommInt

theorem stabL_relIndex_K0_ne_zero_of_four_mul_add_seven_le : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig) (r k : ℕ) (G : GFrames A r k), 4 * r + 7 ≤ k → ∀ Λ : G.Lt, Submodule.IsFullLattice E Λ → (G.stabL Λ).relIndex G.K0 ≠ 0 ∧ G.K0.relIndex (G.stabL Λ) ≠ 0 := by
  intro F E _ _ _ _ _ sig A r k G hk Λ hΛ
  obtain ⟨-, hlat, -⟩ := GlobalTheory.T.numberField_lattice_determined_by_local_lattices A (k + 2 * r + 1) Λ hΛ
  obtain ⟨hfin, -⟩ := GlobalTheory.HL.MassProduct.mass_eq_finprod A r k G hk Λ (by first | exact hΛ | exact hΛ.toIsLattice)
  let U : ∀ p, Subgroup (G.S p).GLV :=
    fun p => (G.S p).St ⊓ MulAction.stabilizer (G.S p).GLV (A.lat p Λ)
  let K : ∀ p, Subgroup (G.S p).GLV := fun p => (G.S p).K0
  have hidx : ∀ p, (K p).relIndex (U p) ≠ 0 ∧ (U p).relIndex (K p) ≠ 0 := by
    intro p
    haveI := (A.loc p).lf
    haveI := (A.loc p).char0
    obtain ⟨a, b, -⟩ := (GlobalTheory.HL.volSt (A.L p) r k (G.S p)).1 (A.lat p Λ) (hlat p)
    exact ⟨a, b⟩
  have hKU : {p | K p ≠ U p}.Finite := hfin.subset fun p hp h => hp h.symm
  obtain ⟨h1, h2, -⟩ := GlobalTheory.T.haarInvVolumeRelIndex_pi_univ_eq_finprod K U hKU hidx
  let φ := GlobalTheory.HL.MassProduct.extHom A (k + 2 * r + 1)
  have e1 : G.K0 = (Subgroup.pi Set.univ K).comap φ := (GlobalTheory.HL.MassProduct.comap_pi A _ K).symm
  have e2 : G.stabL Λ = (Subgroup.pi Set.univ U).comap φ := (GlobalTheory.HL.MassProduct.comap_pi A _ U).symm
  rw [e1, e2, Subgroup.relIndex_comap, Subgroup.relIndex_comap]
  exact ⟨fun h0 => h2 (Subgroup.relIndex_eq_zero_of_le_right (Subgroup.map_comap_le _ _) h0),
    fun h0 => h1 (Subgroup.relIndex_eq_zero_of_le_right (Subgroup.map_comap_le _ _) h0)⟩

end GlobalTheory.HL.CommInt
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.hermitianLattice_mass_eq_finprod_local : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (r k : ℕ) (G : GFrames A r k), 4 * r + 7 ≤ k → ∀ Λ : G.Lt, Submodule.IsFullLattice E Λ → {p | (G.S p).St ⊓ MulAction.stabilizer (G.S p).GLV (A.lat p Λ) ≠ (G.S p).K0}.Finite ∧ G.mu Λ = ∏ᶠ p, (G.S p).mu (A.lat p Λ) := by
  intro F E _ _ _ _ _ sig A r k G hk Λ hΛ
  exact GlobalTheory.HL.MassProduct.mass_eq_finprod A r k G hk Λ
    (by first | exact hΛ | exact hΛ.toIsLattice)
end
