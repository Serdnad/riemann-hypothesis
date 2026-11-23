module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CentredSegments.IrreducibleUnif
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle667
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.LInjective
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle001
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle009
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle549
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalAlgebraHolds
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SphericalOneOfLocalAlgebra
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle612
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.SegmentDerivatives.Bundle001
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle002
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.StandardFunctorsFiniteLength
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle381
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle546
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle662
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle374
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityConcat
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.PropsCos
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle668
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivativeJacquetHolds
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.MapsExist
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle669
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.IwasawaUnipotent.IwaU
public import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle658
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle670
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LeviMatchingWords.MatchLM
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle631

@[expose] public section

section

open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

namespace GlobalTheory.CompanionTheory.HeckeBound

theorem norm_lt_of_norm_mul_cpow_lt (q e : ℕ) (hq : 0 < q) (μ : ℂ)
    (h : ‖μ * (q : ℂ) ^ ((e : ℂ) / 2)‖ < 1) : ‖μ‖ < (q : ℝ) ^ (-((e : ℝ) / 2)) := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hre : (((e : ℂ) / 2)).re = (e : ℝ) / 2 := by
    have : ((e : ℂ) / 2) = (((e : ℝ) / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.ofReal_re]
  rw [norm_mul, Complex.norm_natCast_cpow_of_pos hq, hre] at h
  have hp : 0 < (q : ℝ) ^ ((e : ℝ) / 2) := Real.rpow_pos_of_pos hq' _
  rw [Real.rpow_neg hq'.le, ← one_div, lt_div_iff₀ hp]
  exact h

theorem heckeSpectral_of_maxExpStrict (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) (hs : IsSmooth π) (hi : π.IsIrreducible)
    (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hF : GlobalTheory.Published.StandardFunctorsFiniteLength)
    (hM : Zls.MaxExpStrict π) : Zls.HeckeSpectral π := by
  intro m hm j hj hjN T hT μ hμ
  have hq : 0 < Nat.card 𝓀[k] := Nat.card_pos
  by_cases hμ0 : μ = 0
  · subst hμ0
    simpa using Real.rpow_pos_of_pos (by exact_mod_cast hq : (0 : ℝ) < (Nat.card 𝓀[k] : ℝ)) _
  obtain ⟨w, hw⟩ := hμ.exists_hasEigenvector
  let d : Fin 2 → ℕ := ![j, N - j]
  have hd : ∑ a, d a = N := by
    simp only [d, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    omega
  have d0 : d 0 = j := rfl
  have d1 : d 1 = N - j := rfl
  have hd0 : 0 < d 0 := hj
  have hd1 : 0 < d 1 := by rw [d1]; omega
  have hT' : Zls.IsHeckeOp π m (Zls.diagPow k N (Zls.omegaVec N (d 0))) T := hT
  have hTw : T w = μ • w := hw.apply_eq_smul
  have hmk : (Submodule.Quotient.mk (w : V) : Jacquet π (unipRad k (stdBlocks d hd))) ≠ 0 := by
    intro h0
    obtain ⟨r, hr⟩ := GlobalTheory.T.hecke_operator_jacquet_eigen_left k N V π hs m hm d hd hd0 hd1 T hT' w h0
    rw [hw.pow_apply r] at hr
    exact (smul_ne_zero (pow_ne_zero r hμ0) hw.2) hr
  have hjac := GlobalTheory.T.hecke_operator_jacquet_eigen_right k N V π hs m hm d hd hd0 hd1 T hT' w
  have heig : (Submodule.Quotient.mk (π (Zls.diagPow k N (Zls.omegaVec N (d 0))) (w : V)) :
      Jacquet π (unipRad k (stdBlocks d hd))) =
      μ • (Submodule.Quotient.mk (w : V) : Jacquet π (unipRad k (stdBlocks d hd))) := by
    rw [← hjac, hTw]
    rfl
  obtain ⟨x, hx, hxd, hjm, hs0, c1, hs1⟩ :=
    GlobalTheory.T.jacquet_quotient_eigenvector k N V π hs hi hA hF d hd hd0 hd1 μ w hmk heig
  have hpos : ∀ a, 0 < (x a).1 := by
    intro a
    rw [hxd a]
    fin_cases a
    · exact hd0
    · exact hd1
  have hE := hM x hx hpos hjm
  have hc := (hE (Zls.unifU k) (GlobalTheory.T.uniformizer_pow_tendsto_zero k)
    ![μ * (Nat.card 𝓀[k] : ℂ) ^ (((d 0 * d 1 : ℕ) : ℂ) / 2), c1]
    (by
      intro i
      fin_cases i
      · exact hs0
      · exact hs1)).1 0 (by simp)
  have hfil : Finset.univ.filter (· ≤ (0 : Fin 2)) = {0} := by decide
  rw [hfil, Finset.prod_singleton] at hc
  have := norm_lt_of_norm_mul_cpow_lt (Nat.card 𝓀[k]) (d 0 * d 1) hq μ hc
  simpa [d0, d1] using this

end GlobalTheory.CompanionTheory.HeckeBound
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg

theorem _root_.GlobalTheory.T.jacquet_multiplicity_concat : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {s N : ℕ} (y : Fin s → IrrGL (k := k)) (hy : ∑ a, (y a).1 = N) (c : Fin s → ℕ) (x : ∀ a, Fin (c a) → IrrGL (k := k)) (hx : ∀ a, ∑ i, (x a i).1 = (y a).1) (hcat : ∑ i, (concat c x i).1 = N) (hpos : ∀ a, 1 ≤ jm (x a) (hx a) (y a).rep) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) (hs : IsSmooth π) (hfl : HasFiniteLength π), jm y hy π ≤ jm (concat c x) hcat π := by
  first | exact @GlobalTheory.CompanionTheory.JmTrans.jm_le_jm_concat | exact GlobalTheory.CompanionTheory.JmTrans.jm_le_jm_concat | (intros; apply GlobalTheory.CompanionTheory.JmTrans.jm_le_jm_concat <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL Filter Topology

theorem _root_.GlobalTheory.T.jacquet_multiplicity_pos_of_socle : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (h N : ℕ) (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → (∀ a, 0 < (x a).1) → IsSocle π (prodIrr x hd) → Zc.jm x hd π ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.SocleFrob.jm_ne_zero_of_isSocle | exact GlobalTheory.CompanionTheory.SocleFrob.jm_ne_zero_of_isSocle | (intros; apply GlobalTheory.CompanionTheory.SocleFrob.jm_ne_zero_of_isSocle <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M

theorem _root_.GlobalTheory.T.langlands_rep_ordered_word_occurs : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL), LSocleGL k → LSegJacquet k → ∀ (𝔪 : Multiset (Segment k)) {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsL 𝔪 π → ∀ (h : ℕ) (Δ : Fin h → Segment k), IsOrderedForm Δ 𝔪 → Wd π (wtW Δ) := by
  first | exact @GlobalTheory.CompanionTheory.ZWordL.wd_wtW_of_isL | exact GlobalTheory.CompanionTheory.ZWordL.wd_wtW_of_isL | (intros; apply GlobalTheory.CompanionTheory.ZWordL.wd_wtW_of_isL <;> assumption)
end

section

open PositivityTheory.Rg.BcB.F.Eig

theorem _root_.GlobalTheory.T.spherical_one_of_local_algebra : LocAlg → SphOne := by
  first | exact @GlobalTheory.CompanionTheory.SphLine.locAlg_sphOne | exact GlobalTheory.CompanionTheory.SphLine.locAlg_sphOne | (intros; apply GlobalTheory.CompanionTheory.SphLine.locAlg_sphOne <;> assumption)
end

section

noncomputable section

open NumberField IsDedekindDomain
open GlobalTheory.BCT GlobalTheory.UnitaryBC PositivityTheory.Rg.Bc.ArchbcB.B PositivityTheory.Rg.BcB.F.MT
open PositivityTheory.Rg.BcB.F.Eig (lconv)
open PositivityTheory.Rg.BcB.F.U (lpow lone)
open PositivityTheory.Rg.BcN.F2 (mconv)
open scoped Classical

namespace GlobalTheory.CompanionTheory.MatchPowers

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem isLevel_KL (n : ℕ) (w : Pl E) : IsLevel (MonoidHom.id _) (KL n w) (KL n w) :=
  ⟨GlobalTheory.CompanionTheory.SphLine.isOpen_KL n w, le_rfl, fun _ h => h⟩

theorem isHecke_lpow_KL {n : ℕ} {w : Pl E} {f : UL n w → ℂ} (hf : IsHecke (KL n w) f) (j : ℕ) :
    IsHecke (KL n w) (lpow (KL n w) f j) :=
  GlobalTheory.CompanionTheory.UnitaryWord.isHecke_lpow GlobalTheory.CompanionTheory.LocHecke.locAlg (isLevel_KL n w) hf j

theorem matchSplitOf : MatchSplitOf := by
  intro hM3 hCt E _ _ _ n a ha w hw μ hμ f hf k hk
  have hc : ∀ j : ℕ, ctMu (Nat.add_sub_cancel' ha) w μ (lpow (KL n w) f j) =
      Nat.rec (ctMu (Nat.add_sub_cancel' ha) w μ (lone (KL n w)))
        (fun _ g => mconv (ctMu (Nat.add_sub_cancel' ha) w μ f) g) j := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih =>
      have h := hCt E n a ha w hw μ hμ f _ hf (isHecke_lpow_KL hf j)
      rw [ih] at h
      exact h
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have h := hM3 E n a ha w hw μ (KL n w) (isLevel_KL n w) _ (isHecke_lpow_KL hf (j + 1))
  rw [hc (j + 1)] at h
  exact h

end GlobalTheory.CompanionTheory.MatchPowers

end
end

section

noncomputable section

open NumberField IsDedekindDomain
open GlobalTheory.BCT GlobalTheory.UnitaryBC PositivityTheory.Rg.Bc.ArchbcB.B
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.MatchLMPlaces

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.MLM PositivityTheory.Rg.BcB.G8
open PositivityTheory.Rg.BcN.F2 (mconv phi3 gconv leviOf IsHk)
open PositivityTheory.Rg.BcB.F.Eig (lconv)
open PositivityTheory.Rg.BcB.F.U (lpow lone)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem mconv_mul_mul {a b : ℕ} {w : Pl E} (r s : ℂ) (u v : GLw a w × GLw b w → ℂ) :
    mconv (fun y => r * u y) (fun y => s * v y) = fun y => (r * s) * mconv u v y := by
  funext y
  unfold mconv
  rw [← GlobalTheory.CompanionTheory.TailLocPow.hint_smul]
  congr 1
  funext z
  ring

theorem lconv_mul_mul {w : Pl E} (r s : ℂ) (u v : UL n w → ℂ) :
    lconv (fun y => r * u y) (fun y => s * v y) = fun y => (r * s) * lconv u v y := by
  funext y
  unfold lconv
  rw [← GlobalTheory.CompanionTheory.TailLocPow.hint_smul]
  congr 1
  funext z
  ring

section S0

variable (d : LocData E n) {a : ℕ} (ha : a ≤ n) {w : Pl E}

end S0

section T

variable (d : LocData E n) {a : ℕ} (ha : a ≤ n) {w : Pl E}

abbrev cc (d : LocData E n) (w : Pl E) : ↥(d.c w).support → ℂ := fun j => d.c w j.1

abbrev xx (d : LocData E n) (w : Pl E) : ↥(d.c w).support → Fin n → ℤ := fun j => j.1

theorem qT_eq (s : Finset (Fin (n / 2))) :
    d.qT a w s = fun y => (((Tail.I2 a (n - a) w).relIndex (K2 a (n - a) w) : ℕ) : ℂ) *
      MT.entT n w (d.ϖ w) a (cc d w) (xx d w) s y := by
  funext y
  unfold LocData.qT MT.entT
  by_cases h : LocData.admitted n a s
  · have h' : MT.admitted n a s := ⟨h.1.1, h.1.2.1, h.1.2.2, h.2.1, h.2.2⟩
    rw [dite_eq_left h, dite_eq_left h', Finsupp.sum, Finset.mul_sum, ← Finset.sum_coe_sort (d.c w).support]
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold Tail.dc2
    ring
  · have h' : ¬ MT.admitted n a s := fun h' => h ⟨⟨h'.1, h'.2.1, h'.2.2.1⟩, h'.2.2.2.1, h'.2.2.2.2⟩
    rw [dite_eq_right h, dite_eq_right h', mul_zero]

theorem mpow_scale {b : ℕ} (r : ℂ) (u : GLw a w × GLw b w → ℂ) (k : ℕ) :
    MT.mpow w (fun y => r * u y) k = fun y => r ^ k * MT.mpow w u k y := by
  induction k with
  | zero =>
    funext y
    simp [MT.mpow]
  | succ k ih =>
    show mconv _ (MT.mpow w _ k) = _
    rw [ih, mconv_mul_mul]
    funext y
    show _ = r ^ (k + 1) * mconv u (MT.mpow w u k) y
    ring

theorem lpow_scale (K : Subgroup (UL n w)) (r : ℂ) (g : UL n w → ℂ) (k : ℕ) :
    lpow K (fun y => r * g y) k = fun y => r ^ k * lpow K g k y := by
  induction k with
  | zero =>
    funext y
    simp [U.lpow]
  | succ k ih =>
    show lconv _ (lpow K _ k) = _
    rw [ih, lconv_mul_mul]
    funext y
    show _ = r ^ (k + 1) * lconv g (lpow K g k) y
    ring

theorem unitary_function_at_T (hT : w ∈ d.T) : d.g₀ w = fun y => (((iwU n w (d.b w)).relIndex (KL n w) : ℕ) : ℂ) *
    ∑ j, cc d w j * fU n w (d.b w) (d.ϖ w) (lOf (xx d w j)) y := by
  have h : d.g₀ w = fun y => (d.c w).sum fun x t =>
      t * (((iwU n w (d.b w)).relIndex (KL n w) : ℕ) : ℂ) * fU n w (d.b w) (d.ϖ w) (lOf x) y := by
    unfold LocData.g₀
    rw [if_pos hT]
  rw [h]
  funext y
  rw [Finsupp.sum, Finset.mul_sum, ← Finset.sum_coe_sort (d.c w).support]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

end T

end GlobalTheory.CompanionTheory.MatchLMPlaces

end
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

theorem _root_.GlobalTheory.T.jm_theta_holds : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → GlobalTheory.BZSeg.JmTheta k := by
  first | exact @GlobalTheory.CompanionTheory.JmThetaInv.jmTheta | exact GlobalTheory.CompanionTheory.JmThetaInv.jmTheta | (intros; apply GlobalTheory.CompanionTheory.JmThetaInv.jmTheta <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

theorem _root_.GlobalTheory.T.derivative_jacquet_holds : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → GlobalTheory.BZSeg.DerivJac k := by
  first | exact @GlobalTheory.CompanionTheory.BZDerivJac.derivJac_main | exact GlobalTheory.CompanionTheory.BZDerivJac.derivJac_main | (intros; apply GlobalTheory.CompanionTheory.BZDerivJac.derivJac_main <;> assumption)
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.height_right_translate_compact_bound : ∀ (D : D7) (n : ℕ) (H : G D n → ℝ≥0), IsHt H → (∃ C : Set (G D n), IsCompact C ∧ ∀ g, ∃ q ∈ P D n, ∃ c ∈ C, g = q * c) →
  ∀ C : Set (G D n), IsCompact C → ∃ κ : ℝ, 1 ≤ κ ∧ ∀ c ∈ C, ∀ x : G D n, (H (x * c) : ℝ) ≤ κ * (H x : ℝ) := by
  first | exact @GlobalTheory.CompanionTheory.HtRightTranslate.height_mul_le | exact GlobalTheory.CompanionTheory.HtRightTranslate.height_mul_le | (intros; apply GlobalTheory.CompanionTheory.HtRightTranslate.height_mul_le <;> assumption)
end

section

open PositivityTheory.Rg.SwEis

theorem _root_.GlobalTheory.T.eisenstein_far_estimate : EFar := by
  first | exact @GlobalTheory.CompanionTheory.FarSeries.eFar | exact GlobalTheory.CompanionTheory.FarSeries.eFar | (intros; apply GlobalTheory.CompanionTheory.FarSeries.eFar <;> assumption)
end

section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RapidDecay
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal

theorem _root_.GlobalTheory.T.minimal_parabolic_frame_block_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ g ∈ minPar σ J X, ∀ (w : InfinitePlace F) (τ : EmbOver E w) (s : Fin r) (α β : FrameIx r), frameLev s α < 2 → frameLev s β = 2 → (frameIdem (σ : E →+* E) J X Y α).map τ.1 * archMat σ J τ (projArch σ J w g) * (frameIdem (σ : E →+* E) J X Y β).map τ.1 = 0 := by
  first | exact @GlobalTheory.CompanionTheory.RapidDecay.minPar_frame_block_eq_zero | exact GlobalTheory.CompanionTheory.RapidDecay.minPar_frame_block_eq_zero | (intros; apply GlobalTheory.CompanionTheory.RapidDecay.minPar_frame_block_eq_zero <;> assumption)
end
