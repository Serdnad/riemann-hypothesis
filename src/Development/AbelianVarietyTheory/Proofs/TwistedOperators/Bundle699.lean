module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle046
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1882
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2512
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOKEx
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle632
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle690
import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.Bundle001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle691
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle692
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle468
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle469

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.LocAsm

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def exInd {G : GlobalTheory.SplitFlip.Grid k} (φ : ∀ b : GlobalTheory.SplitFlip.Edge, Matrix (Fin (G.rank b.tgt)) (Fin (G.rank b.src)) k → ℂ) :
    ∀ b : GlobalTheory.SplitFlip.Edge, Matrix (Fin (G.rank b.tgt)) (Fin (G.rank b.src)) k → ℂ := fun b =>
  match b with
  | .ex i j => (SetLike.coe (GlobalTheory.SplitFlip.matLat (Fin (G.rank (GlobalTheory.SplitFlip.Edge.ex i j).tgt))
      (GlobalTheory.SplitFlip.stdLat k (Fin (G.rank (GlobalTheory.SplitFlip.Edge.ex i j).src))))).indicator 1
  | .theta i j => φ (.theta i j)

theorem isNatDatum_exInd {G : GlobalTheory.SplitFlip.Grid k} {ϖ : kˣ} (hϖ : GlobalTheory.SplitFlip.IsUnif ϖ) {e : ℕ} {γ : List GlobalTheory.SplitFlip.Edge}
    (φ : ∀ b : GlobalTheory.SplitFlip.Edge, Matrix (Fin (G.rank b.tgt)) (Fin (G.rank b.src)) k → ℂ)
    (hφ : ∀ b ∈ γ, GlobalTheory.SplitFlip.IsNatDatum ϖ e (φ b)) : ∀ b ∈ γ, GlobalTheory.SplitFlip.IsNatDatum ϖ e (exInd φ b) := by
  intro b hb
  cases b with
  | ex i j => exact GlobalTheory.SplitFlip.hasDepth_indicator hϖ e _
  | theta i j => exact hφ _ hb

variable [MeasurableSpace k] [BorelSpace k]

theorem flatTensor_exOne_eq_exInd {G : GlobalTheory.SplitFlip.Grid k} (hs : 1 ≤ G.s) (ψ : AddChar k Circle) (ν : Measure k)
    (keep : Bool) (g : G.VertexGroup) (γ : List GlobalTheory.SplitFlip.Edge)
    (φ : ∀ b : GlobalTheory.SplitFlip.Edge, Matrix (Fin (G.rank b.tgt)) (Fin (G.rank b.src)) k → ℂ) (x : ColArgs G) :
    flatTensor hs ψ ν (moved G keep g (G.lines₂ γ (exOne φ))) x 0 =
      flatTensor hs ψ ν (moved G keep g (G.lines₂ γ (exInd φ))) x 0 := by
  unfold flatTensor
  congr 1
  funext v
  unfold flatIntegrand moved GlobalTheory.SplitFlip.Grid.pathAct GlobalTheory.SplitFlip.Grid.lines₂
  have key : (γ.map fun b => exOne φ b (G.moveArgs .one g (fill hs x 0 v) b)).prod =
      (γ.map fun b => exInd φ b (G.moveArgs .one g (fill hs x 0 v) b)).prod := by
    refine congrArg List.prod (List.map_congr_left fun b _ => ?_)
    cases b with
    | theta i j => rfl
    | ex i j =>
      have h0 : G.moveArgs .one g (fill hs x 0 v) (.ex i j) = 0 := by
        have : fill hs x 0 v (.ex i j) = 0 := by
          unfold fill
          dsimp only
          split_ifs <;> ext <;> simp
        simp [GlobalTheory.SplitFlip.Grid.moveArgs, this]
      rw [h0]
      simp [exOne, exInd, Set.indicator_of_mem (Submodule.zero_mem _)]
  rw [key]

end Local

section Abstract

variable {ι : Type} [Fintype ι] [DecidableEq ι] {A : ι → Type} [∀ j, AddCommGroup (A j)]


open Classical in
theorem sum_reps_mul_indicator_eq_self (SA BA : ∀ j, A j → Prop) (hSA : ∀ j a b, SA j a → SA j b → SA j (a - b)) (R : ∀ j, Finset (A j))
    (hR2 : ∀ j x, BA j x → ∃ r ∈ R j, SA j (x - r)) (hR3 : ∀ j, ∀ r ∈ R j, ∀ r' ∈ R j, SA j (r - r') → r = r')
    (F : (∀ j, A j) → ℂ) (hper : ∀ x a, (∀ j, SA j (a j)) → F (x + a) = F x) (x : ∀ j, A j)
    (hsupp : F x ≠ 0 → ∀ j, BA j (x j)) :
    ∑ q : (∀ j, R j), F (fun j => (q j).1) * ∏ j, (if SA j (x j - (q j).1) then (1 : ℂ) else 0) = F x := by
  by_cases hex : ∃ q : (∀ j, R j), ∀ j, SA j (x j - (q j).1)
  · obtain ⟨q₀, hx⟩ := hex
    rw [Finset.sum_eq_single q₀]
    · rw [Finset.prod_eq_one fun j _ => if_pos (hx j), mul_one]
      have h := hper (fun j => (q₀ j).1) (x - fun j => (q₀ j).1) hx
      rw [add_sub_cancel] at h
      exact h.symm
    · intro q _ hne
      by_contra hz
      apply hne
      have h1 : ∀ j, SA j (x j - (q j).1) := fun j => by
        by_contra h0
        apply hz
        rw [Finset.prod_eq_zero (Finset.mem_univ j) (if_neg h0)]; ring
      refine funext fun j => Subtype.ext ?_
      have := hSA j _ _ (hx j) (h1 j)
      rw [sub_sub_sub_cancel_left] at this
      exact hR3 j _ (q j).2 _ (q₀ j).2 this
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [Finset.sum_eq_zero]
    · symm
      by_contra hne
      apply hex
      have sx := hsupp hne
      choose r hr hrs using fun j => hR2 j (x j) (sx j)
      exact ⟨fun j => ⟨r j, hr j⟩, hrs⟩
    · intro q _
      by_contra hz
      apply hex
      refine ⟨q, fun j => ?_⟩
      by_contra h0
      apply hz
      rw [Finset.prod_eq_zero (Finset.mem_univ j) (if_neg h0)]; ring

end Abstract



theorem colFlat_expansion : Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch => ∀ (t : T) (β : CosFam ch.G t) (w : locPl ch.G t) (eL : AE D), IsIdemSum eL {w.1} → ∀ (φ : ∀ b : GlobalTheory.SplitFlip.Edge, Matrix (Fin ((locGrid ch.G t w.1).rank b.tgt)) (Fin ((locGrid ch.G t w.1).rank b.src)) (Kw w.1) → ℂ), (∀ b ∈ GlobalTheory.SplitFlip.oppositePath D.R.m, GlobalTheory.SplitFlip.IsNatDatum (unifAt w.1) (depthAt ch.G w.1) (φ b)) → ∃ (I : Type) (S : Finset I) (x : I → ℂ) (d : I → ∀ j : Fin D.R.m, FinDatum ch.G t (.top t j)) (c : I → Combs ch.G), (∀ i ∈ S, ∀ j : Fin D.R.m, (d i j).e = eL ∧ IsCombOf ch.W (d i j) ((c i).1 j)) ∧ ∀ y : ∀ j : Fin D.R.m, WO (ch.G.V (.top j)) (ch.G.V (.top (j + 1))), (∀ j, IsHalf eL (y j)) → ∑ i ∈ S, x i * ∏ j, (d i j).fn (y j) = flatTensor one_le_sLen (psiAt ch.W w.1) (unitVol w.1) (moved (locGrid ch.G t w.1) (keepAt ch.G w.1) ((repsAt ch.G t w.1).elt (β w)) ((locGrid ch.G t w.1).lines₂ (GlobalTheory.SplitFlip.oppositePath D.R.m) (GlobalTheory.LocAsm.exOne φ))) (ch.S.colAt t w.1 y) 0 := by
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch hch _ => ?_⟩⟩
  intro t β w eL heL φ hφ
  have hL := s.core.lev
  have hde : Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q) := by
    obtain ⟨⟨P, -, -⟩, -⟩ := s.size
    have key : ∀ p ∈ D.host.levelPrimes, p.Prime → Nat.Coprime p (D.host.QS * D.host.q) := fun p hp hpp =>
      UpperTheory.Ram.Fun.coprime_QSq_of_splitK D.host hpp (P.level_split p hp)
    exact ⟨key _ D.host.pde_level.1 D.host.pde_prime, key _ D.host.pde_level.2 D.host.pde'_prime⟩
  have hm : 2 ≤ D.R.m := D.R.two_le_m
  have hg := (Good.locGrid_isGood hL ch.G ch.W t hde (hch.guard t)).1 w.1 w.2
  have h00 := hg.square 0 (by change 0 < D.R.m; omega) 0 (by change 0 < D.R.m; omega)
  haveI := (isUnitVol_unitVol w.1).1
  have hT := (locGrid ch.G t w.1).isTensor_pureTensor (unifAt w.1) (depthAt ch.G w.1)
    (GlobalTheory.SplitFlip.oppositePath D.R.m) (exInd φ) (isNatDatum_exInd (isUnif_unifAt w.1) φ hφ)
  obtain ⟨N, hF⟩ := exists_isSBArgs_flat (locGrid ch.G t w.1) one_le_sLen (psiAt ch.W w.1) (unitVol w.1) (unifAt w.1)
    (depthAt ch.G w.1) _ (keepAt ch.G w.1) ((repsAt ch.G t w.1).elt (β w)) hm h00.unif h00.cond hT
  set Fl := flatTensor one_le_sLen (psiAt ch.W w.1) (unitVol w.1) (moved (locGrid ch.G t w.1) (keepAt ch.G w.1)
    ((repsAt ch.G t w.1).elt (β w)) ((locGrid ch.G t w.1).lines₂ (GlobalTheory.SplitFlip.oppositePath D.R.m) (exInd φ))) with hFl
  choose Rp hR1 hR2 hR3 using fun j : Fin D.R.m => GlobalTheory.T.exists_finset_cosetReps_bounded_half_points (ch.S.βp (j + 1)) (ch.S.βp j) {w.1} eL N heL
  have sdT : ∀ j, j ≤ D.R.m → IsSelfDualC (ch.G.V (.top j)) (ch.G.Λ (.top j)) := fun j hj =>
    (ch.G.isV (X := .top j) hj fun _ h => by cases h).sd
  let d : (∀ j : Fin D.R.m, Rp j) → ∀ j : Fin D.R.m, FinDatum ch.G t (.top t j) := fun κ j =>
    { FinDatum.ind ch.G t (.top t j) {w.1} (fun w' hw' => by
        rw [Finset.mem_singleton] at hw'
        subst hw'
        exact (Good.locPl_cases w.2).elim (fun h => .inl h.1) fun h => .inr ⟨_, h.2.2, rfl⟩) eL heL with
      fn := cosLoc {w.1} eL (ch.S.βp (j + 1)) (ch.S.βp j) (N : ℤ) (κ j).1
      sb := GlobalTheory.T.indicator_smallCoset_half_isSchwartzBruhat (ch.G.V (.top j)) (ch.G.V (.top (j + 1))) (ch.G.Λ (.top j)) (ch.G.Λ (.top (j + 1))) (ch.S.βp j)
        (ch.S.βp (j + 1)) {w.1} eL N (κ j).1 (by first | exact GlobalTheory.ProjXCols.selfDual_isFullLattice _ _ (sdT j j.2.le) | exact (sdT j j.2.le).1)
        (by first | exact GlobalTheory.ProjXCols.selfDual_isFullLattice _ _ (sdT (j + 1) j.2) | exact (sdT (j + 1) j.2).1) (ch.S.βp_is j j.2.le)
        (ch.S.βp_is (j + 1) j.2) heL (hR1 j _ (κ j).2).1 }
  choose c₁ hc₁ using fun (κ : ∀ j : Fin D.R.m, Rp j) (j : Fin D.R.m) =>
    GlobalTheory.CombsExist.exists_isCombOf ch.W (p := .top t j) (sdT j j.2.le) (sdT (j + 1) j.2) (d κ j)
  refine ⟨∀ j : Fin D.R.m, Rp j, Finset.univ, fun κ => Fl (ch.S.colAt t w.1 fun j => (κ j).1) 0, d,
    fun κ => (fun j => if h : j < D.R.m then c₁ κ ⟨j, h⟩ else 0, fun _ => 0), ?_, ?_⟩
  · intro κ _ j
    refine ⟨rfl, ?_⟩
    dsimp only
    rw [dite_eq_left j.2]
    exact hc₁ κ j
  · intro y hy
    refine Eq.trans ?_ (flatTensor_exOne_eq_exInd (G := locGrid ch.G t w.1) one_le_sLen _ _ _ _ _ φ _).symm
    have hper : ∀ (x a : ∀ j : Fin D.R.m, WO (ch.G.V (.top j)) (ch.G.V (.top (j + 1)))),
        (∀ j : Fin D.R.m, IsSmall {w.1} (ch.S.βp ((j : ℕ) + 1)) (ch.S.βp j) (N : ℤ) (a j)) →
        Fl (ch.S.colAt t w.1 (x + a)) 0 = Fl (ch.S.colAt t w.1 x) 0 := fun x a ha => by
      rw [colAt_add]
      have := hF.per (ch.S.colAt t w.1 x) 0 (ch.S.colAt t w.1 a) 0 (fun j hj r s => ?_) (fun i _ r s => by simp)
      · rwa [add_zero] at this
      · rw [colAt_eq _ t w.1 _ hj]
        have := ha ⟨j, hj⟩ w.1 (Finset.mem_singleton_self _) (Fin.cast (topRank_eq ch.G t w.1 hj) r)
          (Fin.cast (topRank_eq ch.G t w.1 hj.le) s)
        rw [zpow_natCast] at this
        exact this
    have hsupp : Fl (ch.S.colAt t w.1 y) 0 ≠ 0 → ∀ j : Fin D.R.m,
        IsHalf eL (y j) ∧ IsSmall {w.1} (ch.S.βp ((j : ℕ) + 1)) (ch.S.βp j) (-(N : ℤ)) (y j) := by
      intro hne j
      refine ⟨hy j, fun w' hw' r s => ?_⟩
      rw [Finset.mem_singleton] at hw'
      subst hw'
      have := (hF.supp _ _ hne).1 j j.2 (Fin.cast (topRank_eq ch.G t w.1 j.2).symm r)
        (Fin.cast (topRank_eq ch.G t w.1 j.2.le).symm s)
      rw [colAt_eq _ t w.1 y j.2] at this
      rw [_root_.zpow_neg, zpow_natCast]
      exact this
    have key := sum_reps_mul_indicator_eq_self (ι := Fin D.R.m) (A := fun j : Fin D.R.m => WO (ch.G.V (.top j)) (ch.G.V (.top (j + 1))))
      (fun j a => IsSmall {w.1} (ch.S.βp ((j : ℕ) + 1)) (ch.S.βp j) (N : ℤ) a)
      (fun j a => IsHalf eL a ∧ IsSmall {w.1} (ch.S.βp ((j : ℕ) + 1)) (ch.S.βp j) (-(N : ℤ)) a)
      (fun _ _ _ h h' => h.sub h') Rp (fun j x h => hR2 j x h.1 h.2) hR3 (fun x => Fl (ch.S.colAt t w.1 x) 0)
      hper y hsupp
    refine (Finset.sum_congr rfl fun κ _ => ?_).trans key
    exact congrArg₂ (· * ·) rfl (Finset.prod_congr rfl fun j _ => cosLoc_eq_ite (hy j))

end GlobalTheory.LocAsm
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.RowSingle

theorem locPl_under {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData L sc) (t : T) :
    ∀ w ∈ locPl G t, w.under (𝓞 D.host.F) ∈ G.pl.S0 ∨ ∃ w' ∈ L.Q t, w.under (𝓞 D.host.F) = w'.under (𝓞 D.host.F) := by
  intro w hw
  unfold locPl at hw
  rcases Finset.mem_union.1 hw with h | h
  · left
    unfold Places.W0 at h
    obtain ⟨v, hv, rfl⟩ := by simpa only [Finset.mem_image] using h
    rw [G.pl.under_w hv]
    exact hv
  · exact Or.inr ⟨w, h, rfl⟩

theorem exists_rowData {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} (W : G.Weil)
    {μ₀ : T} (hL : L.Is μ₀) (ρ : RealMatch W) (t : T) (e : AE D) (he : IsIdemSum e (locPl G t))
    (F : ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) → ℂ) (fr : SchRow G)
    (hfr : ∀ i : Fin D.R.m, IsLocVec W (.chi i D.R.m) e (ρ.vX i D.R.m) (F i) (fr i)) :
    ∃ (dr : ∀ i : Fin D.R.m, FinDatum G t (.chi i D.R.m))
      (cr : ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) →₀ ℂ),
      (∀ i, (dr i).e = e ∧ IsCombOf W (dr i) (cr i)) ∧ (∀ i, comb W.ψ _ _ (cr i) (ρ.vX i D.R.m) = fr i) ∧
        ∀ i, (dr i).fn = F i := by
  let dr : ∀ i : Fin D.R.m, FinDatum G t (.chi i D.R.m) := fun i =>
    { FinDatum.ind G t (.chi i D.R.m) (locPl G t) (locPl_under G t) e he with fn := F i, sb := (hfr i).1 }
  let d : PureDat G t := (fun j => FinDatum.vacuum G t (.top t j), dr)
  obtain ⟨c, hc⟩ := GlobalTheory.CombsExist.exists_isCombs W hL (Finsupp.single d 1)
  have hc' := (hc d (by simp)).2
  refine ⟨dr, fun i => (c d).2 i, fun i => ⟨rfl, hc' i⟩, fun i => ?_, fun i => rfl⟩
  have hv := ρ.vX_is i D.R.m i.2 le_rfl
  obtain ⟨⟨Tm, hTm⟩, h1⟩ := (hc' i).2.2 (ρ.vX i D.R.m) hv.2.theta hv.2.lat
  exact (h1 Tm hTm).trans ((hfr i).2.2 Tm hTm).symm

theorem rowData : Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch => ∀ (t : T) (e : AE D), IsIdemSum e (locPl ch.G t) → ∀ (φ : (∀ w : locPl ch.G t, ∀ b : GlobalTheory.SplitFlip.Edge, Matrix (Fin ((locGrid ch.G t w.1).rank b.tgt)) (Fin ((locGrid ch.G t w.1).rank b.src)) (Kw w.1) → ℂ)) (fr : SchRow ch.G), (∀ i : Fin D.R.m, IsLocVec ch.W (.chi i D.R.m) e (ch.rm.vX i D.R.m) (fun y => if IsHalf e y then ∏ w : locPl ch.G t, φ w (.ex i D.R.m) (ch.S.B.coord t w.1 (X := (i, D.R.m)) (Y := (i + 1, D.R.m)) ⟨i.2.le, le_rfl⟩ ⟨i.2, le_rfl⟩ (y.map fun a => cpt w.1 (toEAf D a))) else 0) (fr i)) → ∃ (dr : ∀ i : Fin D.R.m, FinDatum ch.G t (.chi i D.R.m)) (cr : ∀ i : Fin D.R.m, WO (ch.G.pS (.chi i D.R.m : Pair T)) (ch.G.pT (.chi i D.R.m : Pair T)) →₀ ℂ), (∀ i, (dr i).e = e ∧ IsCombOf ch.W (dr i) (cr i)) ∧ (∀ i, comb ch.W.ψ _ _ (cr i) (ch.rm.vX i D.R.m) = fr i) ∧ ∀ i y, IsHalf e y → (dr i).fn y = ∏ w : locPl ch.G t, φ w (.ex i D.R.m) (ch.S.B.coord t w.1 (X := (i, D.R.m)) (Y := (i + 1, D.R.m)) ⟨i.2.le, le_rfl⟩ ⟨i.2, le_rfl⟩ (y.map fun a => cpt w.1 (toEAf D a))) := by
  refine ⟨0, fun _ _ _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch _ _ => ?_⟩⟩
  intro t e he φ fr hfr
  obtain ⟨dr, cr, h1, h2, h3⟩ := exists_rowData ch.W s.core.lev ch.rm t e he _ fr hfr
  exact ⟨dr, cr, h1, h2, fun i y hy => by simp only [h3 i, hy, ↓reduceIte]⟩

end GlobalTheory.RowSingle
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
open GlobalTheory.FlipRun
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.flippedFiniteTensor_local_identity : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (t : T) (Φ : ch.G.Datum) (e : AE D) (τ : SchRow ch.G × SchDown ch.G t →₀ ℂ) (φ : SchRow ch.G × SchDown ch.G t → SchRow ch.G × SchDown ch.G t), (∀ d ∈ τ.support, (∀ i : Fin D.R.m, IsLocVec ch.W (.chi i D.R.m) e (ch.rm.vX i D.R.m) ((φ d).1 i) (d.1 i)) ∧ ∀ j : Fin D.R.m, IsLocVec ch.W (.mu t D.R.m j) e (ch.rm.vT D.R.m j) ((φ d).2 j) (d.2 j)) → (∀ x y, (∀ i, IsHalf e (x i)) → (∀ j, IsHalf e (y j)) → (τ.sum fun d c => c * (∏ i, (φ d).1 i (x i)) * ∏ j, (φ d).2 j (y j)) = ∏ w ∈ locPl ch.G t, Tflip ch.W ch.S.B t Φ w (oppArgs t ch.S.B w x y)) → ∀ (n : locPl ch.G t → ℕ) (xw : ∀ w : locPl ch.G t, Fin (n w) → ℂ) (φw : ∀ w : locPl ch.G t, Fin (n w) → ∀ b : GlobalTheory.SplitFlip.Edge, Matrix (Fin ((locGrid ch.G t w.1).rank b.tgt)) (Fin ((locGrid ch.G t w.1).rank b.src)) (Kw w.1) → ℂ), (∀ (w : locPl ch.G t) z, Tflip ch.W ch.S.B t Φ w.1 z = ∑ i, xw w i * (locGrid ch.G t w.1).lines₂ (GlobalTheory.SplitFlip.oppositePath D.R.m) (φw w i) z) → ∀ (x : RowPt ch.G) (y : ∀ j : Fin D.R.m, WO (ch.G.pS (.mu t D.R.m j : Pair T)) (ch.G.pT (.mu t D.R.m j : Pair T))), (τ.sum fun d c => c * (∏ i, (φ d).1 i (x i)) * ∏ j, (φ d).2 j (y j)) = ∑ a ∈ Fintype.piFinset (fun w => (Finset.univ : Finset (Fin (n w)))), (∏ w, xw w (a w)) * (∏ i : Fin D.R.m, (fun y => if IsHalf e y then ∏ w : locPl ch.G t, (fun w => φw w (a w)) w (.ex i D.R.m) (ch.S.B.coord t w.1 (X := (i, D.R.m)) (Y := (i + 1, D.R.m)) ⟨i.2.le, le_rfl⟩ ⟨i.2, le_rfl⟩ (y.map fun a => cpt w.1 (toEAf D a))) else 0) (x i)) * ∏ j : Fin D.R.m, (fun y => if IsHalf e y then ∏ w : locPl ch.G t, (fun w => φw w (a w)) w (.theta D.R.m j) (ch.S.B.coord t w.1 (X := (D.R.m, j + 1)) (Y := (D.R.m, j)) ⟨le_rfl, j.2⟩ ⟨le_rfl, j.2.le⟩ (y.map fun a => cpt w.1 (toEAf D a))) else 0) (y j) := by
  first | exact @GlobalTheory.LocAsm.flipFin_local_identity | exact GlobalTheory.LocAsm.flipFin_local_identity | (intros; apply GlobalTheory.LocAsm.flipFin_local_identity <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_columnUnitVacuaFamily_moved : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (large₂ : SizeData₂ D) (F : Face D A), HidaSetting large₂ R F → ∀ (ch : Choice R), ch.Is → ∃ v, IsColVac ch v ∧ ∃ (κ : ℕ → ℂˣ) (z : T → ℕ → ℂˣ), (∀ t j, z t j ∈ xiVals R.toLevCh t) ∧ ∀ (t : T) (j : ℕ), j < D.R.m → ch.W.om (.top t j) (ch.G.toPair (.top t j) (ch.S.N.u (Pair.top t j : Pair T).small).1 (ch.S.N.u (Pair.top t j : Pair T).big).1) (ch.S.Z.vac (.top t j)) = ((κ j * z t j : ℂˣ) : ℂ) • v j := by
  first | exact @GlobalTheory.ColVac.colVac | exact GlobalTheory.ColVac.colVac | (intros; apply GlobalTheory.ColVac.colVac <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

theorem _root_.GlobalTheory.T.mem_finitePoints_of_hasLocalLatticeMatrices : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (t : T) (B : Frames G) {j : ℕ}
    (hj : j ≤ D.R.m) (x : GA D (G.V (.grid D.R.m j)))
    (g : ∀ w : locPl G t, GL (Fin ((locGrid G t w.1).rank (D.R.m, j))) (Kw w.1)), HasLoc t B hj x g → x ∈ GfC _ := by
  first | exact @GlobalTheory.RowCover.mem_GfC_of_hasLoc | exact GlobalTheory.RowCover.mem_GfC_of_hasLoc | (intros; apply GlobalTheory.RowCover.mem_GfC_of_hasLoc <;> assumption)
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.rowPeriodGroups_split_real_finite_large_depth : Big fun ch => GrpAt ch := by
  first | exact @GlobalTheory.RowGrpSplit.grpAt_big | exact GlobalTheory.RowGrpSplit.grpAt_big | (intros; apply GlobalTheory.RowGrpSplit.grpAt_big <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.rowTest_exists_combinations_of_expansion : Big fun ch => ∀ t Φ β τ, ch.S.IsExpansion t Φ β τ → ∃ c, IsCombs ch.W τ c := by
  first | exact @GlobalTheory.CombsExist.combs_exist | exact GlobalTheory.CombsExist.combs_exist | (intros; apply GlobalTheory.CombsExist.combs_exist <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.columnCombinations_compose_largeDepth : Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch => ∀ (c : Combs ch.G) (c' c'' : ∀ j : ℕ, WO (ch.G.V (.top j)) (ch.G.V (.top (j + 1))) →₀ ℂ), (∀ j, j < D.R.m → ∀ f, comb ch.W.ψ _ _ (c'' j) f = comb ch.W.ψ _ _ (c.1 j) (comb ch.W.ψ _ _ (c' j) f)) → ∀ (C : BiFam ch.G) (u : ColPt ch.G), evT (combC ch.W c (combC ch.W (c', 0) C)) 1 u 0 = evT (combC ch.W (c'', 0) C) 1 u 0 := by
  first | exact @GlobalTheory.ColComb.main | exact GlobalTheory.ColComb.main | (intros; apply GlobalTheory.ColComb.main <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.exists_combinationOperator_columnProduct : Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch => ∀ c : Combs ch.G, ∃ Tc : (ColPt ch.G → ℂ) →ₗ[ℂ] (ColPt ch.G → ℂ), ∀ C : BiFam ch.G, (fun u => evT (combC ch.W c C) 1 u 0) = Tc (fun u => evT C 1 u 0) := by
  first | exact @GlobalTheory.LocAsm.exists_comb_op | exact GlobalTheory.LocAsm.exists_comb_op | (intros; apply GlobalTheory.LocAsm.exists_comb_op <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField


theorem _root_.GlobalTheory.T.gridBasePoint_trivial_offTensorPlaces : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (t : T) (B : Frames G) (b : Pts G), IsBase t B b → ∀ v : GlobalTheory.FinPl.Pl D, (∀ w ∈ locPl G t, w.under (𝓞 D.host.F) ≠ v) → ∀ y : Fin (G.V (.grid D.R.m 0)).rank → AE D, (∀ i, y i ∈ idAt D (· = v)) → Formalism.L2.Theta.mt _ (b 0) *ᵥ y = y := by
  first | exact @GlobalTheory.RowVal.base_mt_mulVec_off | exact GlobalTheory.RowVal.base_mt_mulVec_off | (intros; apply GlobalTheory.RowVal.base_mt_mulVec_off <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

theorem _root_.GlobalTheory.T.hasLocalLatticeMatrices_inv : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (t : T) (B : Frames G) {j : ℕ}
    (hj : j ≤ D.R.m) (x : GA D (G.V (.grid D.R.m j)))
    (g : ∀ w : locPl G t, GL (Fin ((locGrid G t w.1).rank (D.R.m, j))) (Kw w.1)), HasLoc t B hj x g → HasLoc t B hj x⁻¹ (fun w => (g w)⁻¹) := by
  first | exact @GlobalTheory.RowVal.hasLoc_inv | exact GlobalTheory.RowVal.hasLoc_inv | (intros; apply GlobalTheory.RowVal.hasLoc_inv <;> assumption)
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.isIteratedInvariantIntegral_linear_and_congr : ∀ (ι : Type) [DecidableEq ι] (H : ι → Type) [∀ i, Group (H i)] [∀ i, MeasurableSpace (H i)] (R : ∀ i, Subgroup (H i)) (ρ : ∀ i, Measure (R i)) (μ : ∀ i, Measure (H i)) (l : List ι) (h : ∀ i, H i), (∀ (I : Type) (S : Finset I) (x z : I → ℂ) (q : I → (∀ i, H i) → ℂ), (∀ n ∈ S, NIter ρ μ (q n) l h (z n)) → NIter ρ μ (fun g => ∑ n ∈ S, x n * q n g) l h (∑ n ∈ S, x n * z n)) ∧ ∀ q q' z, (∀ g : ∀ i, H i, (∀ i, i ∉ l → g i = h i) → q g = q' g) → NIter ρ μ q l h z → NIter ρ μ q' l h z := by
  first | exact @GlobalTheory.RowVal.niter_lin_congr | exact GlobalTheory.RowVal.niter_lin_congr | (intros; apply GlobalTheory.RowVal.niter_lin_congr <;> assumption)
end
