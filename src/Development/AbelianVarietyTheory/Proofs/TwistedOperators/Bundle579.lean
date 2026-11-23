module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PathArgsOfNotMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHasLocalSmall
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle014
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle533
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle563
public import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle284
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle566
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle241
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle296
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle239
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped Pointwise

noncomputable section

namespace GlobalTheory.FlipRun

open GlobalTheory.FunObj.LocTensor
open scoped ValuativeRel

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem locArg_eq_locM (B : Frames G) {t : T} {a : Arrow T} (ha : IsGridArrow D.R.m t a) :
    ∃ (β : GL (Fin (G.pT a.pair).rank) (Lev.EAf D)) (β' : GL (Fin (G.pS a.pair).rank) (Lev.EAf D)), ∀ w,
      ∃ (f : Fin ((locGrid G t w).rank (edgeOf a).tgt) → Fin (G.pS a.pair).rank)
        (g : Fin ((locGrid G t w).rank (edgeOf a).src) → Fin (G.pT a.pair).rank),
        f.Surjective ∧ g.Surjective ∧ ∀ x r c, locArg B t w a x r c = locM β β' w x (g c) (f r) := by
  have sur : ∀ {m n : ℕ} (h : m = n), (Fin.cast h).Surjective := fun h y => ⟨Fin.cast h.symm y, by simp⟩
  rcases ha with ⟨i, j, hi, hj, rfl⟩ | ⟨i, j, hi, hj, rfl⟩
  · refine ⟨B.β i j, B.β (i + 1) j, fun w => ⟨Fin.cast (rank_vertex G t w (X := (i + 1, j)) ⟨hi, hj⟩),
      Fin.cast (rank_vertex G t w (X := (i, j)) ⟨hi.le, hj⟩), sur _, sur _, fun x r c => ?_⟩⟩
    have e : locArg B t w (.right i j) x = B.coord t w (X := (i, j)) (Y := (i + 1, j)) ⟨hi.le, hj⟩ ⟨hi, hj⟩
        (x.map fun c => cpt w (toEAf D c)) := dite_eq_left ⟨hi, hj⟩
    rw [e]
    rfl
  · refine ⟨B.β i (j + 1), B.β i j, fun w => ⟨Fin.cast (rank_vertex G t w (X := (i, j)) ⟨hi, hj.le⟩),
      Fin.cast (rank_vertex G t w (X := (i, j + 1)) ⟨hi, hj⟩), sur _, sur _, fun x r c => ?_⟩⟩
    have e : locArg B t w (.down t i j) x = B.coord t w (X := (i, j + 1)) (Y := (i, j)) ⟨hi, hj⟩ ⟨hi, hj.le⟩
        (x.map fun c => cpt w (toEAf D c)) := dite_eq_left ⟨hi, hj⟩
    rw [e]
    rfl

theorem locArg_add (B : Frames G) {t : T} {a : Arrow T} (ha : IsGridArrow D.R.m t a) (w : Pl D.host.E)
    (x u : WO (G.pS a.pair) (G.pT a.pair)) : locArg B t w a (x + u) = locArg B t w a x + locArg B t w a u := by
  obtain ⟨β, β', h⟩ := locArg_eq_locM B ha
  obtain ⟨f, g, -, -, h⟩ := h w
  ext r c
  rw [Matrix.add_apply, h, h, h, locM_add, Matrix.add_apply]

theorem arrow_sb {W : G.Weil} (B : Frames G) (ρ : RealMatch W) {μ₀ : T} (hL : L.Is μ₀) {t : T} {e : AE D}
    (he : IsIdemSum e (locPl G t)) (n : Pl D.host.E → ℕ) {a : Arrow T} (ha : IsGridArrow D.R.m t a) {Y : Type}
    (F : WO (G.pS a.pair) (G.pT a.pair) → Y → ℂ)
    (h1 : ∀ x u y, (∀ w ∈ locPl G t, GivenAdm.CongM (unifAt w ^ n w) (locArg B t w a u)) → F (x + u) y = F x y)
    (h2 : ∀ x y, F x y ≠ 0 → ∀ w ∈ locPl G t, ∀ r c, locArg B t w a x r c ∈ 𝒪[Kw w]) :
    ∃ (ι : Type) (s : Finset ι) (φ : ι → Sch G a) (r : ι → WO (G.pS a.pair) (G.pT a.pair)),
      (∀ i ∈ s, IsSBHalf e (latA G a) (φ i)) ∧ ∀ x y, IsHalf e x → F x y = ∑ i ∈ s, φ i x * F (r i) y := by
  obtain ⟨hS, hT, -⟩ := arrow_data ρ hL ha
  obtain ⟨β, β', hβ⟩ := locArg_eq_locM B ha
  obtain ⟨k, hk, k1, k2⟩ := exists_mult
    (GlobalTheory.PlaceVec.selfDual_isFullLattice _ _ hS)
    (GlobalTheory.PlaceVec.selfDual_isFullLattice _ _ hT) he β β' n
  exact exists_sb hS.1.fg hT.1.fg (GlobalTheory.PlaceVec.idemSum_mul_self he) F hk
    (fun u hu x y => h1 x (k • u) y fun w hw r c => by
      obtain ⟨f, g, -, -, h⟩ := hβ w
      rw [h]
      exact k1 u hu w hw _ _)
    fun x y hx h0 => k2 x hx fun w hw i j => by
      obtain ⟨f, g, hf, hg, h⟩ := hβ w
      obtain ⟨c, rfl⟩ := hg i
      obtain ⟨r, rfl⟩ := hf j
      rw [← h]
      exact h2 x y h0 w hw r c

theorem exists_classSum_schwartzProducts_pathInduction {μ₀ : T} (hL : L.Is μ₀) {W : G.Weil} (B : Frames G) (ρ : RealMatch W) (t : T) {e : AE D}
    (he : IsIdemSum e (locPl G t)) (n : Pl D.host.E → ℕ) {X : Node} : ∀ {Y : Node} (p : Path T X Y), OnGrid D.R.m t p →
    (edges p).Nodup → ∀ {U : Type} (K : (∀ w, (locGrid G t w).Args) → U → ℂ),
    (∀ (x z : ∀ w, (locGrid G t w).Args) (y : U), (∀ w ∈ locPl G t, ∀ b,
      z w b ∈ GlobalTheory.SplitFlip.matLat _ (unifAt w ^ n w • GlobalTheory.SplitFlip.stdLat (Kw w) _)) → K (x + z) y = K x y) →
    (∀ (x : ∀ w, (locGrid G t w).Args) (y : U), K x y ≠ 0 → ∀ w ∈ locPl G t, ∀ b ∈ edges p,
      x w b ∈ GlobalTheory.SplitFlip.matLat _ (GlobalTheory.SplitFlip.stdLat (Kw w) _)) →
    ∃ (ι : Type) (s : Finset ι) (φ d : ι → PureT G p) (r : ι → ArgT G p), (∀ κ ∈ s, VecAll ρ e p (φ κ) (d κ)) ∧
      ∀ (x : ArgT G p) (y : U), HalfAll e p x →
        K (fun w => pathArgs B t w p x) y = ∑ κ ∈ s, famProd p (φ κ) x * K (fun w => pathArgs B t w p (r κ)) y := by
  intro Y p
  induction p with
  | nil =>
    intro _ _ U K _ _
    refine ⟨Unit, {()}, fun _ => (), fun _ => (), fun _ => (), fun _ _ => trivial, fun x y _ => ?_⟩
    rw [Finset.sum_singleton]
    exact (one_mul _).symm
  | snoc a p ih =>
    intro hg hnd U K hK1 hK2
    have hnd' : (edges p ++ [edgeOf a]).Nodup :=
      edges_snoc a p ▸ (hnd : (edges (.snoc a p)).Nodup)
    have hnd1 : (edges p).Nodup := hnd'.of_append_left
    have hne : edgeOf a ∉ edges p :=
      List.disjoint_right.mp hnd'.disjoint (List.mem_singleton_self _)
    have ha : IsGridArrow D.R.m t a := hg.last
    let F (x : WO (G.pS a.pair) (G.pT a.pair)) (z : ArgT G p × U) : ℂ :=
      K (fun w => Function.update (pathArgs B t w p z.1) (edgeOf a) (locArg B t w a x)) z.2
    have hF1 : ∀ x u z, (∀ w ∈ locPl G t, GivenAdm.CongM (unifAt w ^ n w) (locArg B t w a u)) →
        F (x + u) z = F x z := by
      intro x u z hu
      have e1 : (fun w => Function.update (pathArgs B t w p z.1) (edgeOf a) (locArg B t w a (x + u))) =
          (fun w => Function.update (pathArgs B t w p z.1) (edgeOf a) (locArg B t w a x)) +
            fun w => Function.update (0 : (locGrid G t w).Args) (edgeOf a) (locArg B t w a u) := by
        funext w b
        rcases eq_or_ne b (edgeOf a) with rfl | hb
        · simp only [Pi.add_apply, Function.update_self, locArg_add B ha]
        · simp only [Pi.add_apply, Function.update_of_ne hb, Pi.zero_apply, add_zero]
      dsimp only [F]
      rw [e1]
      refine hK1 _ _ _ fun w hw b => ?_
      rcases eq_or_ne b (edgeOf a) with rfl | hb
      · rw [Function.update_self]
        exact GivenAdm.mem_matLat_smul.2 (hu w hw)
      · rw [Function.update_of_ne hb]
        exact zero_mem _
    have hF2 : ∀ x z, F x z ≠ 0 → ∀ w ∈ locPl G t, ∀ r c, locArg B t w a x r c ∈ 𝒪[Kw w] := by
      intro x z h0 w hw r c
      have hm : edgeOf a ∈ edges (.snoc a p) := by
        rw [edges_snoc]
        exact List.mem_append_right _ (List.mem_singleton_self _)
      have h := hK2 (fun w => Function.update (pathArgs B t w p z.1) (edgeOf a) (locArg B t w a x))
        z.2 h0 w hw (edgeOf a) hm
      rw [Function.update_self] at h
      exact GlobalTheory.SplitFlip.mem_matLat_stdLat.1 h r c
    have hArrowExpansion :
        ∃ (ι : Type) (s : Finset ι) (φ : ι → Sch G a) (r : ι → WO (G.pS a.pair) (G.pT a.pair)),
          (∀ i ∈ s, IsSBHalf e (latA G a) (φ i)) ∧
            ∀ x y, IsHalf e x → F x y = ∑ i ∈ s, φ i x * F (r i) y := by
      exact arrow_sb (W := W) B ρ (μ₀ := μ₀) hL (t := t) (e := e) he n (a := a) ha
        (Y := ArgT G p × U) F hF1 hF2
    obtain ⟨ι₁, s₁, φa, r₁, hφa, hexp⟩ := hArrowExpansion
    let K' (x : ∀ w, (locGrid G t w).Args) (y : ι₁ × U) : ℂ :=
      K (fun w => Function.update (x w) (edgeOf a) (locArg B t w a (r₁ y.1))) y.2
    have hK'1 : ∀ x z y, (∀ w ∈ locPl G t, ∀ b,
        z w b ∈ GlobalTheory.SplitFlip.matLat _ (unifAt w ^ n w • GlobalTheory.SplitFlip.stdLat (Kw w) _)) →
        K' (x + z) y = K' x y := by
      intro x z y hz
      have e1 : (fun w => Function.update ((x + z) w) (edgeOf a) (locArg B t w a (r₁ y.1))) =
          (fun w => Function.update (x w) (edgeOf a) (locArg B t w a (r₁ y.1))) +
            fun w => Function.update (z w) (edgeOf a) 0 := by
        funext w b
        rcases eq_or_ne b (edgeOf a) with rfl | hb
        · simp only [Pi.add_apply, Function.update_self, add_zero]
        · simp only [Pi.add_apply, Function.update_of_ne hb]
      dsimp only [K']
      rw [e1]
      refine hK1 _ _ _ fun w hw b => ?_
      rcases eq_or_ne b (edgeOf a) with rfl | hb
      · rw [Function.update_self]
        exact zero_mem _
      · rw [Function.update_of_ne hb]
        exact hz w hw b
    have hK'2 : ∀ x y, K' x y ≠ 0 → ∀ w ∈ locPl G t, ∀ b ∈ edges p,
        x w b ∈ GlobalTheory.SplitFlip.matLat _ (GlobalTheory.SplitFlip.stdLat (Kw w) _) := by
      intro x y h0 w hw b hb
      have hm : b ∈ edges (.snoc a p) := by
        rw [edges_snoc]
        exact List.mem_append_left _ hb
      have h := hK2 (fun w => Function.update (x w) (edgeOf a) (locArg B t w a (r₁ y.1))) y.2 h0 w hw b hm
      have hba : b ≠ edgeOf a := fun hEq => hne (hEq ▸ hb)
      rwa [Function.update_of_ne hba] at h
    obtain ⟨ι₂, s₂, φ₂, d₂, r₂, hv, hexp₂⟩ := ih hg.init hnd1 (U := ι₁ × U) K' hK'1 hK'2
    obtain ⟨Tm, hTm, -, -⟩ := exists_arrowModel ρ hL he ha
    refine ⟨ι₂ × ι₁, s₂ ×ˢ s₁, fun κ => (φ₂ κ.1, φa κ.2), fun κ => (d₂ κ.1, Tm (φa κ.2)), fun κ => (r₂ κ.1, r₁ κ.2),
      fun κ hκ => ?_, fun x y hx => ?_⟩
    · obtain ⟨h1, h2⟩ := Finset.mem_product.1 hκ
      exact ⟨hv _ h1, (hTm _ _).2 ⟨hφa _ h2, rfl⟩⟩
    · have hx' : HalfAll e p x.1 ∧ IsHalf e x.2 := hx
      have e1 : (fun w => pathArgs B t w (.snoc a p) x) =
          fun w => Function.update (pathArgs B t w p x.1) (edgeOf a) (locArg B t w a x.2) :=
        funext fun w => pathArgs_snoc B t w a p x
      calc K (fun w => pathArgs B t w (.snoc a p) x) y
          = ∑ i ∈ s₁, φa i x.2 * K (fun w => Function.update (pathArgs B t w p x.1) (edgeOf a) (locArg B t w a (r₁ i))) y := by
            rw [e1]
            exact hexp x.2 (x.1, y) hx'.2
        _ = ∑ i ∈ s₁, φa i x.2 * ∑ κ ∈ s₂, famProd p (φ₂ κ) x.1 *
              K (fun w => Function.update (pathArgs B t w p (r₂ κ)) (edgeOf a) (locArg B t w a (r₁ i))) y :=
            Finset.sum_congr rfl fun i _ => congrArg _ (hexp₂ x.1 (i, y) hx'.1)
        _ = _ := by
            rw [Finset.sum_product_right]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun κ _ => ?_
            have e2 : (fun w => pathArgs B t w (.snoc a p) ((r₂ κ, r₁ i) : ArgT G (.snoc a p))) =
                fun w => Function.update (pathArgs B t w p (r₂ κ)) (edgeOf a) (locArg B t w a (r₁ i)) :=
              funext fun w => pathArgs_snoc B t w a p _
            show _ = famProd p (φ₂ κ) x.1 * φa i x.2 * K (fun w => pathArgs B t w (.snoc a p) ((r₂ κ, r₁ i) : ArgT G (.snoc a p))) y
            rw [e2]
            ring

theorem exists_classes_path : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ {W : G.Weil} (B : Frames G) (ρ : RealMatch W) (t : T) {e : AE D}, IsIdemSum e (locPl G t) → ∀ (n : Pl D.host.E → ℕ) {X Y : Node} (p : Path T X Y), GlobalTheory.FlipRun.OnGrid D.R.m t p → (GlobalTheory.FlipRun.edges p).Nodup → ∀ {U : Type} (K : (∀ w, (locGrid G t w).Args) → U → ℂ), (∀ (x z : ∀ w, (locGrid G t w).Args) (y : U), (∀ w ∈ locPl G t, ∀ b, z w b ∈ GlobalTheory.SplitFlip.matLat _ (unifAt w ^ n w • GlobalTheory.SplitFlip.stdLat (Kw w) _)) → K (x + z) y = K x y) → (∀ (x : ∀ w, (locGrid G t w).Args) (y : U), K x y ≠ 0 → ∀ w ∈ locPl G t, ∀ b ∈ GlobalTheory.FlipRun.edges p, x w b ∈ GlobalTheory.SplitFlip.matLat _ (GlobalTheory.SplitFlip.stdLat (Kw w) _)) → ∃ (ι : Type) (s : Finset ι) (φ d : ι → PureT G p) (r : ι → GlobalTheory.FlipRun.ArgT G p), (∀ κ ∈ s, GlobalTheory.FlipRun.VecAll ρ e p (φ κ) (d κ)) ∧ ∀ (x : GlobalTheory.FlipRun.ArgT G p) (y : U), GlobalTheory.FlipRun.HalfAll e p x → K (fun w => GlobalTheory.FlipRun.pathArgs B t w p x) y = ∑ κ ∈ s, GlobalTheory.FlipRun.famProd p (φ κ) x * K (fun w => GlobalTheory.FlipRun.pathArgs B t w p (r κ)) y :=
  by
  intro D T L sc G μ₀ hL W B ρ t e he n X Y p hg hnd U K hK1 hK2
  exact exists_classSum_schwartzProducts_pathInduction hL B ρ t he n p hg hnd K hK1 hK2

end GlobalTheory.FlipRun

end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix

namespace GlobalTheory.HoweRealKer

theorem det_ne_zero_of_hasSig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨hrs, A, hA⟩ := h
  let e : Fin r ⊕ Fin s ≃ Fin n := finSumFinEquiv.trans (finCongr hrs)
  let A' : Matrix (Fin n) (Fin n) ℂ := A.submatrix id e.symm
  have hA' : A'ᵀ * M * A'.map star = (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1)).submatrix e.symm e.symm := by
    rw [← hA]
    ext i j
    simp [A', Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply, Matrix.map_apply]
  have hD : (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1 : Matrix (Fin s) (Fin s) ℂ)).det ≠ 0 := by
    rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul, Matrix.det_neg, Matrix.det_one, mul_one]
    simp
  intro hM
  apply hD
  rw [← Matrix.det_submatrix_equiv_self e.symm, ← hA', Matrix.det_mul, Matrix.det_mul, hM, mul_zero, zero_mul]

theorem det_ne_zero_of_sig {E : Type} [Field E] {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (f : E →+* ℂ) {r s : ℕ} (h : HasSig (J.map f) r s) : J.det ≠ 0 := by
  intro hJ
  apply det_ne_zero_of_hasSig h
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, hJ, map_zero]

theorem det_ne_zero_of_sigI {E : Type} [Field E] {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (f : E →+* ℂ) {r s : ℕ} (h : HasSig (Complex.I • J.map f) r s) : J.det ≠ 0 := by
  intro hJ
  apply det_ne_zero_of_hasSig h
  rw [Matrix.det_smul, ← RingHom.mapMatrix_apply, ← RingHom.map_det, hJ, map_zero, mul_zero]

theorem resEtaPow_div {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {χ χ' : Chr F E} {n m : ℕ}
    (h : ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ n)
    (h' : ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ' m) :
    ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range (χ / χ') (n + m) := by
  intro x
  rw [MonoidHom.div_apply, Circle.coe_div, h x, h' x]
  split_ifs
  · simp
  · rw [pow_add]
    rcases neg_one_pow_eq_or ℂ m with hm | hm <;> rw [hm] <;> ring

theorem isHecke_div {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {χ χ' : Chr F E} (h : IsHecke F E χ) (h' : IsHecke F E χ') : IsHecke F E (χ / χ') :=
  ⟨h.1.div' h'.1, fun x => by simp only [MonoidHom.div_apply, h.2 x, h'.2 x, div_self']⟩

theorem actsD_zero {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (T : ℝ → ((κ → AF F) → ℂ) →ₗ[ℂ] (κ → AF F) → ℂ) :
    ActsD (evI F) (fun t => T t) ((0 : SInf F κ) : (κ → mixedEmbedding.mixedSpace F) → ℂ) ((0 : SInf F κ) : _) := by
  intro r _ x
  have h0 : tens (evI F) ((0 : SInf F κ) : (κ → mixedEmbedding.mixedSpace F) → ℂ) r = 0 := by
    funext y; simp [tens]
  simp only [h0, map_zero, Pi.zero_apply]
  exact hasDerivAt_const 0 0

theorem acts_zero {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (T : ((κ → AF F) → ℂ) →ₗ[ℂ] (κ → AF F) → ℂ) :
    Acts (evI F) T ((0 : SInf F κ) : (κ → mixedEmbedding.mixedSpace F) → ℂ) ((0 : SInf F κ) : _) := by
  intro r _
  have h0 : tens (evI F) ((0 : SInf F κ) : (κ → mixedEmbedding.mixedSpace F) → ℂ) r = 0 := by
    funext y; simp [tens]
  simp only [h0, map_zero]

theorem main : GlobalTheory.Published.HoweDualityReal → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W)
    (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf →
      (∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a × Fin (a + a')))),
        StrictMono N → (∀ i, GlobalTheory.Published.ThetaSubInf G.M Bs.ψ Bs.emb om (N i)) → m ≤ L) ∧
      ∀ N : Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a × Fin (a + a'))), GlobalTheory.Published.ThetaSubInf G.M Bs.ψ Bs.emb om N →
        N ≠ G.M.Pol Bs.ψ Bs.emb → ∀ f ∈ N, R.p f = 0 := by
  intro hHD F E _ _ _ _ _ σ Bs a a' G Xc om om' R Rf hMt
  obtain ⟨ht, hr, -⟩ := hMt
  have w0 : InfinitePlace F := Classical.arbitrary _
  have hVdet : G.V.J.det ≠ 0 := det_ne_zero_of_sig _ _ (ht.geo.hV.sig w0)
  have hV'det : G.V'.J.det ≠ 0 := det_ne_zero_of_sig _ _ (ht.geo.hV'.sig w0)
  have hWdet : G.W.J.det ≠ 0 := det_ne_zero_of_sigI _ _ (ht.geo.hW.sig w0)
  have hresW : ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range (Xc.β / Xc.α) (a + a') :=
    resEtaPow_div ht.chars.resβ ht.chars.resα
  have hresW' : ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range (Xc.α / Xc.β) (a' + a) :=
    resEtaPow_div ht.chars.resα ht.chars.resβ
  rw [Nat.add_comm a' a] at hresW'
  have hHk := isHecke_div ht.chars.heckeβ ht.chars.heckeα
  have hHk' := isHecke_div ht.chars.heckeα ht.chars.heckeβ
  obtain ⟨hchain, hsum⟩ := hHD F E σ ht.base.cm a (a + a') G.V G.W G.M Bs.ψ Xc.β (Xc.β / Xc.α) om ht.base.std
    ht.geo.hV.herm hVdet ht.geo.hW.skew hWdet ht.chars.resβ hresW ht.chars.heckeβ hHk ht.weil Bs.emb
    ht.geo.hV.cartan ht.geo.hW.cartan
  have L := GlobalTheory.T.lieDerivative_polynomialFock_archimedeanUnitary F E σ ht.base.cm a (a + a') G.V G.W G.M Bs.ψ Xc.β (Xc.β / Xc.α) om ht.base.std
    ht.geo.hV.herm hVdet ht.geo.hW.skew hWdet ht.chars.resβ hresW ht.chars.heckeβ hHk ht.weil Bs.emb
    ht.geo.hV.cartan ht.geo.hW.cartan
  have L' := GlobalTheory.T.lieDerivative_polynomialFock_archimedeanUnitary F E σ ht.base.cm a' (a + a') G.V' G.W G.M' Bs.ψ Xc.α (Xc.α / Xc.β) om' ht.base.std
    ht.geo.hV'.herm hV'det ht.geo.hW.skew hWdet ht.chars.resα hresW' ht.chars.heckeα hHk' ht.weil' Bs.emb
    ht.geo.hV'.cartan ht.geo.hW.cartan
  have C := GlobalTheory.T.compactUnitary_preserves_polynomialFock F E σ ht.base.cm a (a + a') G.V G.W G.M Bs.ψ Xc.β (Xc.β / Xc.α) om ht.base.std
    ht.geo.hV.herm hVdet ht.geo.hW.skew hWdet ht.chars.resβ hresW ht.chars.heckeβ hHk ht.weil Bs.emb
    ht.geo.hV.cartan ht.geo.hW.cartan
  have C' := GlobalTheory.T.compactUnitary_preserves_polynomialFock F E σ ht.base.cm a' (a + a') G.V' G.W G.M' Bs.ψ Xc.α (Xc.α / Xc.β) om' ht.base.std
    ht.geo.hV'.herm hV'det ht.geo.hW.skew hWdet ht.chars.resα hresW' ht.chars.heckeα hHk' ht.weil' Bs.emb
    ht.geo.hV'.cartan ht.geo.hW.cartan
  refine ⟨hchain, ?_⟩
  intro N hN hNP

  set P := G.M.Pol Bs.ψ Bs.emb with hPdef
  let K : Submodule ℂ (SInf F (Fin a × Fin (a + a'))) := LinearMap.ker R.p ⊓ P
  have hK : GlobalTheory.Published.ThetaSubInf G.M Bs.ψ Bs.emb om K := by
    refine ⟨inf_le_right, ?_, ?_, ?_, ?_⟩
    · intro γ hγ g hg g₁ hg₁
      exact ⟨LinearMap.mem_ker.mpr (hr.quot.lie γ hγ g hg g₁ hg₁), hN.1 (hN.2.1 γ hγ g hg g₁ hg₁)⟩
    · intro k hk g hg g₁ hg₁
      refine ⟨?_, hN.1 (hN.2.2.1 k hk g hg g₁ hg₁)⟩
      show R.p (g₁ - g) = 0
      rw [map_sub, hr.quot.cpt k hk g hg g₁ hg₁, sub_self]
    · intro γ hγ g hg g₁ hg₁
      refine ⟨?_, (L γ hγ g hg.2).2 g₁ hg₁⟩
      have e := hr.lie γ hγ g hg.2 0 (Submodule.zero_mem _) g₁ 0 hg₁ (actsD_zero _)
        (by rw [LinearMap.mem_ker.mp hg.1, map_zero])
      show R.p g₁ = 0
      rw [e, map_zero]
    · intro k hk g hg g₁ hg₁
      refine ⟨?_, (C k hk g hg.2).2 g₁ hg₁⟩
      have e := hr.cpt k hk g hg.2 0 (Submodule.zero_mem _) g₁ 0 hg₁ (acts_zero _)
        (by rw [LinearMap.mem_ker.mp hg.1, map_zero])
      show R.p g₁ = 0
      rw [e, map_zero]
  have hKP : K ≠ P := by
    intro hKP
    haveI := hr.nontriv
    have hle : P ≤ LinearMap.ker R.p := hKP ▸ inf_le_left
    have hbot : P.map R.p = ⊥ := by
      rw [eq_bot_iff, Submodule.map_le_iff_le_comap]
      intro x hx
      simpa [Submodule.mem_comap] using hle hx
    exact bot_ne_top (hbot.symm.trans hr.quot.onto)

  have hirr := hr.irred (N.map R.p) ?_ ?_
  · rcases hirr with hbot | htop
    · intro f hf
      have : R.p f ∈ N.map R.p := Submodule.mem_map_of_mem hf
      rw [hbot] at this
      exact (Submodule.mem_bot ℂ).mp this
    · exfalso
      apply hsum N K hN hK hNP hKP
      refine le_antisymm (sup_le hN.1 inf_le_right) ?_
      intro g hg
      have hpg : R.p g ∈ N.map R.p := htop ▸ Submodule.mem_top
      obtain ⟨n₀, hn₀, hpn⟩ := hpg
      have hk : g - n₀ ∈ K := ⟨show R.p (g - n₀) = 0 by rw [map_sub, hpn, sub_self], P.sub_mem hg (hN.1 hn₀)⟩
      have := Submodule.add_mem_sup hn₀ hk
      simpa using this
  · intro γ hγ g hg g₁ hg₁ hpg
    obtain ⟨n₀, hn₀, hpn⟩ := hpg
    have hg' : R.p g ∈ (G.M'.Pol Bs.ψ Bs.emb).map R.p' := hr.quot'.onto ▸ Submodule.mem_top
    obtain ⟨g', hg'P, hpg'⟩ := hg'
    obtain ⟨g₁', hg₁'⟩ := (L' γ hγ g' hg'P).1
    obtain ⟨n₁, hn₁⟩ := (L γ hγ n₀ (hN.1 hn₀)).1
    have e1 := hr.lie γ hγ g hg g' hg'P g₁ g₁' hg₁ hg₁' hpg'.symm
    have e2 := hr.lie γ hγ n₀ (hN.1 hn₀) g' hg'P n₁ g₁' hn₁ hg₁' (hpn.trans hpg'.symm)
    exact ⟨n₁, hN.2.2.2.1 γ hγ n₀ hn₀ n₁ hn₁, e2.trans e1.symm⟩
  · intro k hk g hg g₁ hg₁ hpg
    obtain ⟨n₀, hn₀, hpn⟩ := hpg
    have hg' : R.p g ∈ (G.M'.Pol Bs.ψ Bs.emb).map R.p' := hr.quot'.onto ▸ Submodule.mem_top
    obtain ⟨g', hg'P, hpg'⟩ := hg'
    obtain ⟨g₁', hg₁'⟩ := (C' k hk g' hg'P).1
    obtain ⟨n₁, hn₁⟩ := (C k hk n₀ (hN.1 hn₀)).1
    have e1 := hr.cpt k hk g hg g' hg'P g₁ g₁' hg₁ hg₁' hpg'.symm
    have e2 := hr.cpt k hk n₀ (hN.1 hn₀) g' hg'P n₁ g₁' hn₁ hg₁' (hpn.trans hpg'.symm)
    exact ⟨n₁, hN.2.2.2.2 k hk n₀ hn₀ n₁ hn₁, e2.trans e1.symm⟩

end GlobalTheory.HoweRealKer
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.SeeConj.exists_conj_level : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → ∃ t ∈ GfC (Yc D 0), ConjLevel (t)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) ((iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) (fun k => star (X.chi2 ((iotaX X h).toMulEquiv k).2)) ∧ IsFrame (finE (Yc D 0) t * R.βY 0) (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F X h hIs hGrp _hMod
  obtain ⟨ψ0, hψ0, _hψ, π, _hπ, hmem, hchi⟩ := hGrp.levels
  obtain ⟨β₃, hfr₃, hD1⟩ := GlobalTheory.T.exists_frame_conjugate_level_symmetricLevel R F X h hIs hGrp ψ0 hψ0
  obtain ⟨β₂, hfr₂, hD2⟩ := GlobalTheory.T.exists_frame_reordering_levelData R.toLevCh (R.levR F true) (PsharpSym R.Pg D.R.r D.R.rS D.R.k ψ0) π hmem hchi β₃ hfr₃
  obtain ⟨t₀, ht₀, hfr₀⟩ := GlobalTheory.T.exists_finiteUnitary_selfDualFrame_to_baseLatticeFrame (Yc D 0) (R.βY 0) (R.ΛY 0) _ (hIs.βY 0 (by have := D.R.two_le_m; omega))
  obtain ⟨u, hu, hfru, hred⟩ := GlobalTheory.T.exists_unitary_matching_frames_at_nonconjugate_places (Yc D 0) R.Pg (GlobalTheory.T.levelPlaces_not_isConjPlace_realDat R F hIs hGrp) _ β₂ hfr₀ hfr₂
  have hfe : finE (Yc D 0) (u * t₀) * R.βY 0 = finE (Yc D 0) u * (finE (Yc D 0) t₀ * R.βY 0) := by
    rw [map_mul, mul_assoc]
  refine ⟨u * t₀, mul_mem hu ht₀, ?_, by rw [hfe]; exact hfru⟩
  intro (k : GA D (Yc D 0))
  have hA := GlobalTheory.T.levelSubgroup_conj_finite_moves_frame (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true)) (u * t₀) (mul_mem hu ht₀) k
  rw [hfe] at hA
  have hC := GlobalTheory.T.levS_iff_and_levChi_eq_of_redFn_eq (Yc D 0) (finE (Yc D 0) u * (finE (Yc D 0) t₀ * R.βY 0)) β₂ _ (R.dat0 (R.levR F true)) hfru hfr₂
    (fun PP hPP x => hred PP hPP x) (fun PP hPP => absurd hPP (Finset.notMem_empty _)) ((u * t₀) * k * (u * t₀)⁻¹)
  have h2 := hD2 ((u * t₀) * k * (u * t₀)⁻¹)
  have h1 := hD1 ((u * t₀) * k * (u * t₀)⁻¹)
  have hm : ∀ hk : k ∈ levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true)), (u * t₀) * k * (u * t₀)⁻¹ ∈ levS (Yc D 0) β₃ (R.dat0 (PsharpSym R.Pg D.R.r D.R.rS D.R.k ψ0)) :=
    fun hk => h2.1.1 (hC.1.1 (hA.1.1 hk))
  have key : (k ∈ levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true)) ↔ (u * t₀) * k * (u * t₀)⁻¹ ∈ (iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) ∧
      (k ∈ levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true)) → star (X.chi2 ((iotaX X h).toMulEquiv ((u * t₀) * k * (u * t₀)⁻¹)).2) = levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true)) k) :=
    ⟨hA.1.trans (hC.1.trans (h2.1.trans h1.1.symm)), fun hk => by rw [h1.2 (hm hk), ← h2.2, ← hC.2, hA.2]⟩
  have e : ((u * t₀)⁻¹⁻¹ : GA D (D.sp.Y 0)) = u * t₀ := inv_inv (G := GA D (D.sp.Y 0)) _
  rw [e]
  exact key
end
