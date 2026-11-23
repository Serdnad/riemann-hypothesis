module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle303
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle294
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle547
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HermitianAdjointSymplecticActionThetaHeisenberg
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle244
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle307
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle549
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle425
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle712
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle726
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle469
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle687
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle727
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OffQOfSizeRows
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittCoreInclusionMemCompletedHomLattice
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle063
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilRepresentationVacuumCosetVectorsGrid
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralNormSqEqToL2
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle644
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceInvariantFormsSeparateThetaFunctions
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle634
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle632
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle013
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.TypeStar
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle005

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
open scoped TensorProduct
namespace GlobalTheory.VacRealPf

variable {D : D7}

theorem mem_GfC_of_idemSum {e : AE D} {Q : Finset (Formalism.L2.DIV.Pl D.host.E)} (he : IsIdemSum e Q) {V : HSp D} {g : GA D V}
    (hs : SuppAt e V g) : g ∈ GfC V := by
  have h0 : infPart D (e + cA D e) = 0 := by
    have h1 := GlobalTheory.FinRestComm.infPart_of_idemSum he
    rw [RingHom.map_add (f := _), h1, GlobalTheory.AdjointPair.infPart_zero e h1, add_zero]
  show g ∈ (infHom V).ker
  rw [MonoidHom.mem_ker]
  apply Units.ext
  ext i j
  have h1 := congrArg (infPart D) (hs i j)
  rw [map_mul, h0, zero_mul] at h1
  have e : (infHom V g).1 i j = infPart D (mt V g i j) := rfl
  change (infHom V g).1 i j = (1 : GL (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E)).1 i j
  rw [e, Units.val_one]
  have h2 : infPart D ((mt V g - 1) i j) = infPart D (mt V g i j) - (1 : Matrix (Fin V.rank) (Fin V.rank) _) i j := by
    rw [Matrix.sub_apply, RingHom.map_sub]
    by_cases hij : i = j
    · subst hij; rw [Matrix.one_apply_eq, Matrix.one_apply_eq, RingHom.map_one]
    · rw [Matrix.one_apply_ne hij, Matrix.one_apply_ne hij, RingHom.map_zero]
  rw [h2] at h1
  exact sub_eq_zero.1 h1.symm

theorem moves_one (S : HSp D) (L : GlobalTheory.FinPl.Lat S) (P : GlobalTheory.FinPl.Pl D → Prop) : GlobalTheory.FinPl.Moves S 1 L L P := by
  intro y _
  rw [show mt S 1 = 1 from rfl, Matrix.one_mulVec]

theorem mem_idx {j : ℕ} : j ∈ idx D ↔ 1 ≤ j ∧ j + 2 ≤ D.R.m := by
  have := D.R.two_le_m
  simp only [idx, List.mem_range'_1]
  omega

section
variable {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R)

theorem base_fin {t : T} {b : Pts ch.G} (hb : IsBase t ch.S.B b) (j : ℕ) : b j ∈ GfC _ := by
  by_cases h0 : j = 0
  · subst h0
    obtain ⟨e, he, hs, -⟩ := hb.1
    exact mem_GfC_of_idemSum he hs
  · by_cases hj : j ∈ idx D
    · obtain ⟨δ, -, hδ⟩ := hb.2.1 j hj
      exact hδ.1
    · rw [hb.2.2 j h0 hj]; exact one_mem _

theorem sd_grid (j : ℕ) (hj : j ≤ D.R.m) : IsSelfDualC _ (ch.G.Λ (.grid D.R.m j)) :=
  (ch.G.isV (X := .grid D.R.m j) ⟨le_rfl, hj⟩ fun i e => by
    have := D.R.two_le_m
    injection e with e1
    omega).sd

theorem sd_top (j : ℕ) (hj : j ≤ D.R.m) : IsSelfDualC _ (ch.G.Λ (.top j)) :=
  (ch.G.isV (X := .top j) hj fun i e => by cases e).sd

theorem fock_vac (t : T) (j : ℕ) (hj : j < D.R.m) (P : PolDown ch.G) {M : GlobalTheory.FinPl.Lat (ch.G.V (.grid D.R.m j))}
    {M' : GlobalTheory.FinPl.Lat (ch.G.V (.grid D.R.m (j + 1)))} (hM : IsSelfDualC _ M) (hM' : IsSelfDualC _ M')
    {g : GA D (ch.G.V (.grid D.R.m j))} {h : GA D (ch.G.V (.grid D.R.m (j + 1)))} (hg : g ∈ GfC _) (hh : h ∈ GfC _)
    (mg : GlobalTheory.FinPl.Moves _ g (ch.G.Λ (.grid D.R.m j)) M fun _ => True)
    (mh : GlobalTheory.FinPl.Moves _ h (ch.G.Λ (.grid D.R.m (j + 1))) M' fun _ => True)
    {x : GA D (ch.G.V (.grid D.R.m j))} {y : GA D (ch.G.V (.grid D.R.m (j + 1)))} (hx : x ∈ GinfC _) (hy : y ∈ GinfC _) :
    GlobalTheory.FinPl.Vac ch.W.ψ (ch.G.V (.grid D.R.m j)) (ch.G.V (.grid D.R.m (j + 1))) M M' (fun _ => True)
      (ch.W.om (.mu t D.R.m j) (x * g, y * h) (fockD ch.W t (fun j => ch.rm.vT D.R.m j) P ⟨j, hj⟩)) :=
  (GlobalTheory.StepMove.gen (ch.W.om_is (.mu t D.R.m j) ⟨le_rfl, hj⟩) (sd_grid ch j hj.le) hM (sd_grid ch (j + 1) hj) hM' hg hh mg mh _ _
    (ch.rm.vT_is t D.R.m j le_rfl hj)).1 _ x hx y hy

theorem real_of {ψ : AddChar (AF D.host.F) ℂ} {X S X' : HSp D} {LA : GlobalTheory.FinPl.Lat X} {LS : GlobalTheory.FinPl.Lat S}
    {LA' : GlobalTheory.FinPl.Lat X'} {C : WO X S → WO S X' → ℂ} (h : IsBiTheta ψ X S X' C)
    (h' : GlobalTheory.FinPl.BiVacAt ψ LA LS LA' (fun _ => True) C) :
    IsBiVac ψ X S X' (LA : Set _) (LS : Set _) (LA' : Set _) C ∧ IsBiSmooth C :=
  ⟨⟨h.cont, h'.1, h'.2⟩, h.smooth⟩

theorem vac_cast {V : HSp D} {LV : GlobalTheory.FinPl.Lat V} {n n' : ℕ} (h : n = n') {f : WO V (ch.G.V (.grid D.R.m n)) → ℂ}
    (hf : GlobalTheory.FinPl.Vac ch.W.ψ V _ LV (ch.G.Λ (.grid D.R.m n)) (fun _ => True) f) :
    GlobalTheory.FinPl.Vac ch.W.ψ V _ LV (ch.G.Λ (.grid D.R.m n')) (fun _ => True) (castSch ch.G h f) := by
  subst h
  exact hf

theorem orth_cast {LZ : GlobalTheory.FinPl.Lat (pLine D)} {v : GlobalTheory.FinPl.Pl D}
    (hor : GlobalTheory.FinPl.OrthAt (topOrth ch.G) (ch.G.Λ (.top D.R.m)) (ch.G.Λ (.grid D.R.m D.R.m)) LZ v) {n : ℕ} (h : D.R.m = n) :
    GlobalTheory.FinPl.OrthAt (topOrthAt ch.G h) (ch.G.Λ (.top n)) (ch.G.Λ (.grid D.R.m D.R.m)) LZ v := by
  subst h
  exact hor

theorem vacReal_of_shape (hsh : ShapeAt ch) : VacReal ch := by
  obtain ⟨N, N₀, LL, LZ, hmv, hLZ, hor, hall⟩ := hsh
  intro t M hM b hb P p hp j hje hjm
  have hm2 := D.R.two_le_m
  obtain ⟨a, ha⟩ := D.R.m_even
  obtain ⟨c, hc⟩ := hje
  have hψ : IsStdChar D ch.W.ψ (-1) := ch.W.ψ_std
  obtain ⟨x₀⟩ := GlobalTheory.SeeSaw.VacShape.nonempty_pl D
  have hFV := GlobalTheory.T.flatMapPreservesVacuum_proof D ch.W.ψ (fun _ => True)
  have hbf := base_fin ch hb
  have hpi : ∀ k, p k ∈ GinfC _ := hp.1
  unfold conAt
  by_cases h0 : j + 2 * 0 + 2 = D.R.m
  · rw [dite_eq_left h0]
    have hb1 : b (j + 1) = 1 := hb.2.2 (j + 1) (by omega) fun h => by
      have := (mem_idx.1 h).2
      omega
    have hs := hall t M hM j 0 h0 (GlobalTheory.Unf.Inhab.nonempty_volN _).some
    have hg0 := (hs x₀).2.2.1
    have hmv1 := hmv t b hb (j + 1) (by omega)
    rw [hb1] at hmv1
    have v₁ := fock_vac ch t j (by omega) P (M := N j) (M' := N (j + 1)) hg0.sdV hg0.sdW (hbf j) (one_mem _)
      (hmv t b hb j (by omega)) hmv1 (hpi j) (one_mem _)
    rw [one_mul] at v₁
    have v₂ := fock_vac ch t (j + 1) (by omega) P (M := N (j + 1)) (M' := ch.G.Λ (.grid D.R.m (j + 1 + 1))) hg0.sdW
      (sd_grid ch _ (by omega)) (one_mem _) (one_mem _) hmv1 (moves_one _ _ _) (one_mem _) (one_mem _)
    rw [one_mul, one_mul, Prod.mk_one_one, map_one, Module.End.one_apply] at v₂
    have v₃ := vac_cast ch (show j + 1 + 1 = D.R.m by omega) v₂
    have f₁ := hFV.1 0 _ _ (lastAt ch.G ch.W t hM j h0 (GlobalTheory.Unf.Inhab.nonempty_volN _).some).s (N j) (N₀ j) (N (j + 1))
      (ch.G.Λ (.top (j + 1))) (fun x _ => (hs x).2.2.1) _ v₁
    have f₂ := hFV.2.2 _ _ _ (rowJac ch.G (j + 1) (by omega) 0 (by omega)) (N (j + 1)) (ch.G.Λ (.top (j + 1)))
      (ch.G.Λ (.grid D.R.m D.R.m)) hg0.sdW hg0.sdW₀ (sd_grid ch _ le_rfl) (fun x _ => (hs x).2.2.1.monoW) _ v₃
    refine real_of ?_ ?_
    · exact GlobalTheory.LastBiTheta.isBiTheta_lastBi D _ hψ _ _ _ _ _ _ _ _ _ _ GlobalTheory.RowChain.LastSeeSawStep.lastTau_gram _ _ f₁.1 f₂.1
    · exact GlobalTheory.T.lastSeeSawDatum_of_vacua_is_vacuum_both D _ hψ _ _ _ _ _ _ _ _ _ _ rfl rfl GlobalTheory.RowChain.LastSeeSawStep.lastTau_gram (fun _ => True) (N₀ j)
        (ch.G.Λ (.top j)) (ch.G.Λ (.top (j + 1))) (ch.G.Λ (.top (j + 1 + 1))) (ch.G.Λ (.grid D.R.m D.R.m)) hg0.sdV₀
        (sd_top ch _ (by omega)) hg0.sdW₀ (sd_top ch _ (by omega)) (sd_grid ch _ le_rfl)
        (fun x _ => ⟨(hs x).2.2.1.tame, LL j, LZ, (hs x).1, hLZ, (hs x).2.1, orth_cast ch (hor x) _, (hs x).2.2.2.2.1 rfl⟩)
        _ _ f₁ f₂
  · have h1 : j + 2 * ((D.R.m - 4 - j) / 2 + 1) + 2 = D.R.m := by omega
    rw [dite_eq_right h0]
    erw [dite_eq_left h1]
    have hs := hall t M hM j _ h1 (GlobalTheory.Unf.Inhab.nonempty_volN _).some
    have hs' := hall t M hM (j + 1 + 1) ((D.R.m - 4 - j) / 2) (by omega) (GlobalTheory.Unf.Inhab.nonempty_volN _).some
    have had := fun x => (hs' x).2.2.2.1 (j + 1) rfl (by omega)
    have hg0 := (hs x₀).2.2.1
    have hg1 := had x₀
    have v₁ := fock_vac ch t j (by omega) P (M := N j) (M' := N (j + 1)) hg0.sdV hg0.sdW (hbf j) (hbf (j + 1))
      (hmv t b hb j (by omega)) (hmv t b hb (j + 1) (by omega)) (hpi j) (hpi (j + 1))
    have v₂ := fock_vac ch t (j + 1) (by omega) P (M := N (j + 1)) (M' := N (j + 1 + 1)) hg0.sdW hg1.sdW (hbf (j + 1))
      (hbf (j + 1 + 1)) (hmv t b hb (j + 1) (by omega)) (hmv t b hb (j + 1 + 1) (by omega)) (hpi (j + 1)) (hpi (j + 1 + 1))
    have f₁ := hFV.1 _ (besAt ch.G hM j _ h1 (GlobalTheory.Unf.Inhab.nonempty_volN _).some)
      (jacAt ch.G hM (j + 1) ((D.R.m - 4 - j) / 2 + 1) (by omega)) (stepAt ch.G ch.W t hM j (by omega) (besDecAt ch.G j _ h1)
      (rowJac ch.G (j + 1) (by omega) ((D.R.m - 4 - j) / 2 + 1) (by omega))) (N j) (N₀ j) (N (j + 1))
      (ch.G.Λ (.top (j + 1))) (fun x _ => (hs x).2.2.1) _ v₁
    have f₂ := hFV.2.1 _ (jacAt ch.G hM (j + 1) ((D.R.m - 4 - j) / 2 + 1) (by omega))
      (besAt ch.G hM (j + 1 + 1) ((D.R.m - 4 - j) / 2) (by omega) (GlobalTheory.Unf.Inhab.nonempty_volN _).some) (stepAt ch.G ch.W t hM (j + 1) (by omega)
      (rowJac ch.G (j + 1) (by omega) ((D.R.m - 4 - j) / 2 + 1) (by omega))
      (besDecAt ch.G (j + 1 + 1) ((D.R.m - 4 - j) / 2) (by omega))) (N (j + 1)) (ch.G.Λ (.top (j + 1))) (N (j + 1 + 1))
      (N₀ (j + 1 + 1)) (fun x _ => had x) _ v₂
    have hCC := GlobalTheory.T.besselThetaContraction_extendByZero_vacuum_smooth D _ hψ _ _ _ _
      (linkAt hM j _ h1 (GlobalTheory.Unf.Inhab.nonempty_volN _).some (by omega) (GlobalTheory.Unf.Inhab.nonempty_volN _).some)
      (ch.G.V (.top (j + 1))) ((GlobalTheory.Unf.Inhab.nonempty_volM D _ _).some) _ _ f₁.1 f₂.1
    exact real_of hCC.1 (hCC.2.2 (fun _ => True) (ch.G.Λ (.top j)) (ch.G.Λ (.top (j + 1))) (ch.G.Λ (.top (j + 1 + 1)))
      (N₀ j) (N₀ (j + 1 + 1)) (sd_top ch _ (by omega)) hg0.sdW₀ (sd_top ch _ (by omega)) hg0.sdV₀ hg1.sdW₀
      (fun x _ => ⟨⟨_, (hs x).2.1⟩, ⟨_, (hs' x).2.1⟩⟩) f₁ f₂)

end

theorem vacReal : Big fun ch => VacReal ch := by
  refine GlobalTheory.RowReal.big_mono ?_ GlobalTheory.T.lastRowLatticesGoodPosition_large_depth
  intro D Γ _ _ Pl0 T A Ks _ _ _ R ch hsh
  exact vacReal_of_shape ch hsh

end GlobalTheory.VacRealPf
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowKFix

theorem key {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks]
    [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (large₂ : SizeData₂ D) (F : Face D A)
    (hS : HidaSetting large₂ R F) (hch : ch.Is) (hsh : ShapeAt ch) : KFix ch := by
  intro t Φ τ hτ J hJ k hk y v
  have hJ' : 1 ≤ J ∧ J + 1 < D.R.m := by
    simp only [idx, List.mem_range'_1] at hJ
    omega
  obtain ⟨j, rfl⟩ : ∃ j, J = j + 1 := ⟨J - 1, by omega⟩
  have hj : j + 1 + 1 < D.R.m := hJ'.2
  obtain ⟨c₁, c₂, h1, h2, h3⟩ := GlobalTheory.T.lastRowInnerVertex_vacua_scaled_localProduct ch large₂ F hS hch hsh t Φ j hj k hk
  exact GlobalTheory.T.weilRep_pair_fixes_flippedTensorSum ch large₂ F hS hch t Φ τ hτ j hj k hk c₁ c₂ h1 h2 h3 y v

theorem kfix : Big fun ch => KFix ch := by
  obtain ⟨CF0, h⟩ := GlobalTheory.T.lastRowLatticesGoodPosition_large_depth
  refine ⟨CF0, fun ε CF hCF => ?_⟩
  obtain ⟨x₀, hx⟩ := h ε CF hCF
  exact ⟨x₀, fun D large₂ he hx' Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hch hsc =>
    key ch large₂ F hS hch (hx D large₂ he hx' Γ Pl0 T A Ks R F hS ch hch hsc)⟩

end GlobalTheory.RowKFix
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.unfoldedVacua_differ_by_twist_values_largeDepth : Big fun ch => VacTw ch := by
  first | exact @GlobalTheory.RowVacTw.vacTw | exact GlobalTheory.RowVacTw.vacTw | (intros; apply GlobalTheory.RowVacTw.vacTw <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.CoreOnto.Reps

private theorem selfDual_core {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (i : ℕ) (hi : i < D.R.m) :
    IsSelfDualC (G.pS (.core i)) (G.latS (.core i)) ∧ IsSelfDualC (G.pT (.core i)) (G.latT (.core i)) := by
  have hV : ∀ k, k ≤ D.R.m → IsSelfDualC (G.V (.core k)) (G.Λ (.core k)) := fun k hk =>
    (G.isV (X := .core k) hk (fun j h => Node.noConfusion h)).sd
  exact ⟨isSelfDualC_neg (hV (i + 1) hi), hV i hi.le⟩

private theorem nsmul_inj {D : D7} {m n : ℕ} {K : ℕ} (hK : 0 < K) {x y : Mx D m n} (h : K • x = K • y) : x = y := by
  have inv : (K : AE D) * incA D (K : D.host.E)⁻¹ = 1 := by
    rw [← map_natCast (incA D), ← map_mul, mul_inv_cancel₀ (Nat.cast_ne_zero.2 hK.ne'), map_one]
  have h' := congrArg (fun z : Mx D m n => incA D (K : D.host.E)⁻¹ • z) h
  rwa [← Nat.cast_smul_eq_nsmul (AE D), ← Nat.cast_smul_eq_nsmul (AE D), smul_smul, smul_smul, mul_comm, inv,
    one_smul, one_smul] at h'

private theorem isHalf_add {D : D7} {m n : ℕ} {c : AE D} {x y : Mx D m n} (hx : IsHalf c x) (hy : IsHalf c y) :
    IsHalf c (x + y) := fun a b => by simp only [Matrix.add_apply, mul_add, hx a b, hy a b]

private theorem isHalf_neg {D : D7} {m n : ℕ} {c : AE D} {x : Mx D m n} (hx : IsHalf c x) : IsHalf c (-x) := fun a b => by
  simp only [Matrix.neg_apply, mul_neg, hx a b]

private theorem isHalf_zero {D : D7} {m n : ℕ} (c : AE D) : IsHalf c (0 : Mx D m n) := fun a b => by simp

private theorem symplO_zero_right {D : D7} (S T : HSp D) (x : WO S T) : symplO S T x 0 = 0 := by
  have := GlobalTheory.ConjHalfDual.symplO_add_right' S T x 0 0
  simp only [add_zero] at this
  exact (add_eq_left.1 this.symm)

private theorem symplO_neg_right {D : D7} (S T : HSp D) (x y : WO S T) : symplO S T x (-y) = -symplO S T x y := by
  have := GlobalTheory.ConjHalfDual.symplO_add_right' S T x y (-y)
  rw [add_neg_cancel, symplO_zero_right] at this
  exact (neg_eq_of_add_eq_zero_right this.symm).symm

private theorem psi_ne_zero {F : Type*} [AddGroup F] (ψ : AddChar F ℂ) (a : F) : ψ a ≠ 0 := by
  intro h
  have := AddChar.map_add_eq_mul ψ a (-a)
  rw [add_neg_cancel, AddChar.map_zero_eq_one, h, zero_mul] at this
  exact one_ne_zero this

private theorem finLat_of_nsmul {D : D7} {m n : ℕ} {Λ A : AddSubgroup (Mx D m n)} (h : GlobalTheory.AscFin.FinLat Λ)
    (hle : A ≤ Λ) {K : ℕ} (hK : 0 < K) (hA : ∀ u ∈ Λ, K • u ∈ A) : GlobalTheory.AscFin.FinLat A := by
  obtain ⟨U, h1, h2, h3⟩ := h.opn
  have inv : (K : AE D) * incA D (K : D.host.E)⁻¹ = 1 := by
    rw [← map_natCast (incA D), ← map_mul, mul_inv_cancel₀ (Nat.cast_ne_zero.2 hK.ne'), map_one]
  have hc : Continuous fun a : Mx D m n => incA D (K : D.host.E)⁻¹ • a :=
    continuous_id.const_smul (incA D (K : D.host.E)⁻¹)
  refine GlobalTheory.AscFinWit.finLat_of (fun a ha => h.fin a (hle ha))
    ⟨_, h1.preimage hc, by rwa [Set.mem_preimage, smul_zero], fun a ha hb => ?_⟩ h.cpt fun a ha => hle ha
  have := hA _ (h3 _ ha fun i j => Ideal.mul_mem_left _ _ (hb i j))
  rwa [← Nat.cast_smul_eq_nsmul (AE D), smul_smul, inv, one_smul] at this

end GlobalTheory.CoreOnto.Reps

open GlobalTheory.CoreOnto.Reps in
theorem _root_.GlobalTheory.T.exists_representatives_half_quotient_pairing_trivial_depthLattice : All fun {D} _ _ _ {G} W _ => ∀ i, i < D.R.m → ∀ e : AE D, IsIdemSum e G.pl.W0 → ∃ R : Finset (WO (G.pS (.core i)) (G.pT (.core i))), (∀ y ∈ R, IsHalf (cA D e) y ∧ ∀ u ∈ depLat G (.core i), W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) u y) = 1) ∧ (∀ y, IsHalf (cA D e) y → (∀ u ∈ depLat G (.core i), W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) u y) = 1) → ∃ y' ∈ R, y - y' ∈ latO (G.pS (.core i)) (G.pT (.core i)) (G.latS (.core i) : Set _) (G.latT (.core i) : Set _) fun _ => True) ∧ (∀ y ∈ R, ∀ y' ∈ R, y - y' ∈ latO (G.pS (.core i)) (G.pT (.core i)) (G.latS (.core i) : Set _) (G.latT (.core i) : Set _) (fun _ => True) → y = y') ∧ (∀ y ∈ R, ∀ y' ∈ R, y ≠ y' → ∃ u ∈ latO (G.pS (.core i)) (G.pT (.core i)) (G.latS (.core i) : Set _) (G.latT (.core i) : Set _) (fun _ => True), IsHalf e u ∧ W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) u y) ≠ W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) u y')) := by
  intro D hQ T L μ₀ hL sc G W M hM i hi e he
  classical
  obtain ⟨hS, hT⟩ := selfDual_core G i hi
  set Λ : AddSubgroup (WO (G.pS (.core i)) (G.pT (.core i))) := latO (G.pS (.core i)) (G.pT (.core i))
    (G.latS (.core i) : Set _) (G.latT (.core i) : Set _) (fun _ => True) with hΛ
  have hee : e * e = e := GlobalTheory.PlaceVec.idemSum_mul_self he
  have hec : e * cA D e = 0 := he.2
  have hinf : infPart D e = 0 := Formalism.IndefR.Fin.infPart_idemSum he
  have hfin : finPart D e ∈ intAE D := GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, hee])
  have hdual : ∀ u, IsHalf (cA D e) u → (u ∈ Λ ↔ ∀ l ∈ Λ, IsHalf e l →
      W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) l u) = 1) :=
    GlobalTheory.ConjHalfDual.mem_latO_iff_of_conjHalf D W.ψ _ _ _ _ W.ψ_std hS hT e hee hec hinf hfin
  obtain ⟨K, hK, hKΛ⟩ : ∃ K : ℕ, 0 < K ∧ ∀ u ∈ Λ, K • u ∈ depLat G (.core i) := by
    obtain ⟨K, hK, h⟩ := GlobalTheory.GridWeil.exists_nsmul_latO (T := G.pT (.core i)) (ΛT := G.latT (.core i)) hS
      (G.pl.modul_ne_bot sc)
    refine ⟨K, hK, fun u hu => ⟨nsmul_mem hu K, fun e' he' => ?_⟩⟩
    rw [smul_comm]
    exact h _ (GlobalTheory.LatticeStable.smul_mem_latO D _ _ _ _ _ e'
      (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, GlobalTheory.PlaceVec.idemSum_mul_self he'])) _ hu)

  have hKy : ∀ y, IsHalf (cA D e) y → (∀ u ∈ depLat G (.core i),
      W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) u y) = 1) → K • y ∈ Λ := by
    intro y hy hyt
    refine (hdual _ (GlobalTheory.StdHalfLat.half_nsmul hy K)).2 fun l hl _ => ?_
    rw [← GlobalTheory.DownLift.SplitSep.symplO_nsmul_swap]
    exact hyt _ (hKΛ l hl)
  let A : AddSubgroup (WO (G.pS (.core i)) (G.pT (.core i))) :=
    { carrier := {y | IsHalf (cA D e) y ∧ ∀ u ∈ depLat G (.core i),
        W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) u y) = 1}
      add_mem' := fun {a b} ha hb => ⟨isHalf_add ha.1 hb.1, fun u hu => by
        rw [GlobalTheory.ConjHalfDual.symplO_add_right', AddChar.map_add_eq_mul, ha.2 u hu, hb.2 u hu, one_mul]⟩
      zero_mem' := ⟨isHalf_zero _, fun u _ => by rw [symplO_zero_right, AddChar.map_zero_eq_one]⟩
      neg_mem' := fun {a} ha => ⟨isHalf_neg ha.1, fun u hu => by
        rw [symplO_neg_right, AddChar.map_neg_eq_inv, ha.2 u hu, inv_one]⟩ }
  let KΛ : AddSubgroup (WO (G.pS (.core i)) (G.pT (.core i))) := Λ.map (nsmulAddMonoidHom K)
  have hKΛle : KΛ ≤ Λ := by
    rintro _ ⟨w, hw, rfl⟩
    exact nsmul_mem hw K
  have finΛ : GlobalTheory.AscFin.FinLat Λ := GlobalTheory.AscFinWit.finLat_latO (GlobalTheory.ProjXCols.selfDual_isFullLattice _ _ hS) (GlobalTheory.ProjXCols.selfDual_isFullLattice _ _ hT)
  have finKΛ : GlobalTheory.AscFin.FinLat KΛ :=
    finLat_of_nsmul finΛ hKΛle hK (fun u hu => ⟨u, hu, rfl⟩)
  let N : AddSubgroup ↥Λ := KΛ.addSubgroupOf Λ
  haveI : CompactSpace ↥Λ := isCompact_iff_compactSpace.mp finΛ.cpt
  have hNopen : IsOpen (N : Set ↥Λ) := by
    obtain ⟨U, hU, h0, hUK⟩ := finKΛ.opn
    refine AddSubgroup.isOpen_of_mem_nhds N (g := 0) ?_
    refine Filter.mem_of_superset ((hU.preimage continuous_subtype_val).mem_nhds (by simpa using h0)) ?_
    intro a ha
    exact AddSubgroup.mem_addSubgroupOf.2 (hUK _ ha (finΛ.fin _ a.2))
  haveI : Finite (↥Λ ⧸ N) := AddSubgroup.quotient_finite_of_isOpen N hNopen
  let f : ↥A →+ ↥Λ :=
    { toFun := fun y => ⟨K • (y : WO (G.pS (.core i)) (G.pT (.core i))), hKy _ y.2.1 y.2.2⟩
      map_zero' := by ext1; simp
      map_add' := fun a b => by ext1; simp [nsmul_add] }
  let g : ↥A →+ ↥Λ ⧸ N := (QuotientAddGroup.mk' N).comp f
  have hker : ∀ y : ↥A, y ∈ g.ker ↔ (y : WO (G.pS (.core i)) (G.pT (.core i))) ∈ Λ := by
    intro y
    rw [AddMonoidHom.mem_ker]
    change (QuotientAddGroup.mk (f y) : ↥Λ ⧸ N) = 0 ↔ _
    rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
    change K • (y : WO (G.pS (.core i)) (G.pT (.core i))) ∈ KΛ ↔ _
    constructor
    · rintro ⟨w, hw, hwe⟩
      have : w = (y : WO (G.pS (.core i)) (G.pT (.core i))) := nsmul_inj hK (by simpa using hwe)
      exact this ▸ hw
    · intro hy
      exact ⟨_, hy, by simp⟩
  haveI : Finite (↥A ⧸ g.ker) := Finite.of_injective _ (QuotientAddGroup.kerLift_injective g)
  haveI : Fintype (↥A ⧸ g.ker) := Fintype.ofFinite _
  let sec : ↥A ⧸ g.ker → ↥A := Function.surjInv QuotientAddGroup.mk_surjective
  have hsec : ∀ q, (QuotientAddGroup.mk (sec q) : ↥A ⧸ g.ker) = q := Function.surjInv_eq _
  have hsame : ∀ a b : ↥A, ((a : WO (G.pS (.core i)) (G.pT (.core i))) - b ∈ Λ) ↔
      (QuotientAddGroup.mk a : ↥A ⧸ g.ker) = QuotientAddGroup.mk b := by
    intro a b
    rw [QuotientAddGroup.eq, hker]
    push_cast
    rw [show -(a : WO (G.pS (.core i)) (G.pT (.core i))) + (b : WO (G.pS (.core i)) (G.pT (.core i))) =
      -((a : WO (G.pS (.core i)) (G.pT (.core i))) - (b : WO (G.pS (.core i)) (G.pT (.core i)))) by abel, neg_mem_iff]
  let R : Finset (WO (G.pS (.core i)) (G.pT (.core i))) :=
    Finset.univ.image (fun q => (sec q : WO (G.pS (.core i)) (G.pT (.core i))))
  have hR : ∀ y ∈ R, y ∈ A := by
    intro y hy
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hy
    exact (sec q).2
  have hsep : ∀ y ∈ R, ∀ y' ∈ R, y - y' ∈ Λ → y = y' := by
    intro y hy y' hy' hyy
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hy
    obtain ⟨q', -, rfl⟩ := Finset.mem_image.1 hy'
    have := (hsame _ _).1 hyy
    rw [hsec, hsec] at this
    rw [this]
  refine ⟨R, fun y hy => hR y hy, ?_, hsep, ?_⟩
  · intro y hy hyt
    let a : ↥A := ⟨y, hy, hyt⟩
    refine ⟨sec (QuotientAddGroup.mk a), Finset.mem_image.2 ⟨_, Finset.mem_univ _, rfl⟩, ?_⟩
    exact (hsame a _).2 (hsec _).symm
  · intro y hy y' hy' hne
    have hnot : y - y' ∉ Λ := fun h => hne (hsep y hy y' hy' h)
    have hhalf : IsHalf (cA D e) (y - y') := by
      rw [sub_eq_add_neg]
      exact isHalf_add (hR y hy).1 (isHalf_neg (hR y' hy').1)
    obtain ⟨l, hl, hle, hne1⟩ : ∃ l ∈ Λ, IsHalf e l ∧
        W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) l (y - y')) ≠ 1 := by
      by_contra hc
      push_neg at hc
      exact hnot ((hdual _ hhalf).2 hc)
    refine ⟨l, hl, hle, fun h => hne1 ?_⟩
    have hsplit : symplO (G.pS (.core i)) (G.pT (.core i)) l y =
        symplO (G.pS (.core i)) (G.pT (.core i)) l (y - y') + symplO (G.pS (.core i)) (G.pT (.core i)) l y' := by
      rw [← GlobalTheory.ConjHalfDual.symplO_add_right', sub_add_cancel]
    rw [hsplit, AddChar.map_add_eq_mul] at h
    exact (mul_eq_right₀ (psi_ne_zero _ _)).1 h

end
end
