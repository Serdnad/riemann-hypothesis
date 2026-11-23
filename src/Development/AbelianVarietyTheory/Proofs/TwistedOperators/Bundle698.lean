module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TowerEx
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle308
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentBesselCharacterLaws
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JacobiToBesselFlatMapEquivariant
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LintegralLeOfTsum
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryAdelicHeightOrthogonalEmbeddingLePow
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle384
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle388
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle046
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle310
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle689
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle303
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairVEqOfProdFunEq
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle611
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle468
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle274
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle162
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle423
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle688
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle372
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle318
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle469
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle574

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.lastRowChars_unramified_off_tensorPlaces : Big fun {D} {Γ} _ _ {Pl0 T} {A} {Ks} _ _ _ {R} ch => ∀ (t : T) (v : GlobalTheory.FinPl.Pl D), (∀ w ∈ locPl ch.G t, w.under (𝓞 D.host.F) ≠ v) → ∀ i, i < D.R.m →
    GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D (ch.G.chrS (.mu t D.R.m i)) v ∧ GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D (ch.G.chrT (.mu t D.R.m i)) v := by
  first | exact @GlobalTheory.LastRowUnram.chars_unram | exact GlobalTheory.LastRowUnram.chars_unram | (intros; apply GlobalTheory.LastRowUnram.chars_unram <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

noncomputable section
namespace GlobalTheory.PairKerBound

theorem kernel_bound : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacL D (σ + 1)) (B : BesL D σ) (s : StFB ψ J B) (vL : VolM D B.L.rank J.W₀.rank) (χ χz : (AE D)ˣ →* Circle) (omz : Om J.W₀ B.L), IsWeilDatumO ψ J.W₀ B.L χ χz omz → ∀ (Φ₀ : WO J.W₀ B.L → ℂ) (Φ : WO J.W B.V → ℂ), IsThetaFunO ψ J.W₀ B.L Φ₀ → IsThetaFunO ψ J.W B.V Φ → ∃ (C : ℝ) (a : ℕ), ∀ h h₀ h₁, ‖contractT B.o J.W₀ vL.μ vL.𝓕 (s.om₀ (h₀, B.o.emb (h₁, 1)) (flFB s (s.om (1, h) Φ))) (omz (h₀, 1) Φ₀) 0‖ ≤ C * (height J.W₀ h₀ * height B.A h₁ * height B.V h) ^ a := by
  intro D ψ σ J B s vL χ χz omz homz Φ₀ Φ hΦ₀ hΦ
  obtain ⟨x, hx, hxe⟩ := GlobalTheory.JacMean.xLast_lin B.d B.o B.line
  obtain ⟨C₁, A₁, hC₁⟩ := GlobalTheory.FlatSup.flat_sup_growth D ψ J.W J.W₀ B.V B.V₀ (σ + 1) σ J.d B.d s x hx Φ hΦ
  obtain ⟨C₂, A₂, hC₂⟩ := GlobalTheory.SupThetaGrowth.om_sup_growth D ψ J.W₀ B.L χ χz omz homz Φ₀ hΦ₀
  obtain ⟨C₃, hC₃⟩ := GlobalTheory.EmbHeight.unitaryAdelicHeight_wittEmbedding_le D J.W J.W₀ (σ + 1) J.d
  obtain ⟨C₄, hC₄⟩ := GlobalTheory.EmbHeight.unitaryAdelicHeight_wittEmbedding_le D B.V B.V₀ σ B.d
  obtain ⟨C₅, a₅, hC₅⟩ := GlobalTheory.EmbHeight.height_emb_le D B.V₀ B.A B.L B.o
  have key : ∀ h h₀ h₁ w, s.om₀ (h₀, B.o.emb (h₁, 1)) (flFB s (s.om (1, h) Φ)) w =
      flatS J.d B.d s (rat x) 0 (s.om (J.d.emb0 h₀, embA B.d B.o h₁ * h) Φ) w := by
    intro h h₀ h₁ w
    have e := GlobalTheory.AscFlatEquiFB.flFB_equivariant D ψ σ J B s (s.om (1, h) Φ) (s.weil.om_pres _ _ hΦ) h₀ 1 (one_mem _) h₁
    have hp : psiBes ψ B.d 1 (vecB B.o B.ζ) 1 = 1 :=
      (GlobalTheory.MixPer.charLaws D ψ s.weil.std.1 B.V B.V₀ B.A B.L σ B.d B.o B.ζ 1).2.1 _ 1 (one_mem _)
    rw [hp, star_one, one_smul, one_mul, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one] at e
    rw [← e]
    show flatS J.d B.d s (xLast B.d (vecB B.o B.ζ)) 0 _ w = _
    rw [hxe]
  have hC₃1 : 1 ≤ C₃ := by simpa using (GlobalTheory.Grow.one_le_height J.W (J.d.emb0 1)).trans (hC₃ 1)
  have hC₄1 : 1 ≤ C₄ := by simpa using (GlobalTheory.Grow.one_le_height B.V (B.d.emb0 1)).trans (hC₄ 1)
  have hC₅1 : 1 ≤ C₅ := by simpa using (GlobalTheory.Grow.one_le_height B.V₀ (B.o.emb (1, 1))).trans (hC₅ 1)
  have hM₁ : 0 ≤ max C₁ 0 := le_max_right _ _
  have hM₂ : 0 ≤ max C₂ 0 := le_max_right _ _
  have hK : 0 ≤ C₃ * C₄ * C₅ := by positivity
  refine ⟨max C₁ 0 * (C₃ * C₄ * C₅) ^ A₁ * max C₂ 0, (a₅ + 2) * A₁ + A₂, fun h h₀ h₁ => ?_⟩
  have p0 : 1 ≤ height J.W₀ h₀ := GlobalTheory.Grow.one_le_height _ _
  have p1 : 1 ≤ height B.A h₁ := GlobalTheory.Grow.one_le_height _ _
  have p2 : 1 ≤ height B.V h := GlobalTheory.Grow.one_le_height _ _
  generalize hX : height J.W₀ h₀ * height B.A h₁ * height B.V h = X
  have n01 : 0 ≤ height J.W₀ h₀ * height B.A h₁ := mul_nonneg (by linarith) (by linarith)
  have q0 : height J.W₀ h₀ ≤ X := by
    rw [← hX]; exact (le_mul_of_one_le_right (by linarith) p1).trans (le_mul_of_one_le_right n01 p2)
  have q1 : height B.A h₁ ≤ X := by
    rw [← hX]; exact (le_mul_of_one_le_left (by linarith) p0).trans (le_mul_of_one_le_right n01 p2)
  have q2 : height B.V h ≤ X := by
    rw [← hX]; exact le_mul_of_one_le_left (by linarith) (one_le_mul_of_one_le_of_one_le p0 p1)
  have hX1 : 1 ≤ X := p2.trans q2
  have hX0 : 0 ≤ X := by linarith
  have e1 : height J.W (J.d.emb0 h₀) ≤ C₃ * X := (hC₃ h₀).trans (mul_le_mul_of_nonneg_left q0 (by linarith))
  have e2 : height B.V (embA B.d B.o h₁ * h) ≤ C₄ * C₅ * X ^ (a₅ + 1) := by
    have f1 : height B.V (embA B.d B.o h₁) ≤ C₄ * (C₅ * X ^ a₅) := by
      rw [embA_apply]
      refine (hC₄ _).trans (mul_le_mul_of_nonneg_left ((hC₅ h₁).trans ?_) (by linarith))
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) q1 _) (by linarith)
    calc _ ≤ height B.V (embA B.d B.o h₁) * height B.V h := GlobalTheory.Grow.height_mul_le _ _ _
      _ ≤ (C₄ * (C₅ * X ^ a₅)) * X := mul_le_mul f1 q2 (by linarith) (by positivity)
      _ = C₄ * C₅ * X ^ (a₅ + 1) := by ring
  have hP : height J.W (J.d.emb0 h₀) * height B.V (embA B.d B.o h₁ * h) ≤ C₃ * C₄ * C₅ * X ^ (a₅ + 2) := by
    calc _ ≤ (C₃ * X) * (C₄ * C₅ * X ^ (a₅ + 1)) :=
          mul_le_mul e1 e2 (zero_le_one.trans (GlobalTheory.Grow.one_le_height _ _)) (by positivity)
      _ = _ := by ring
  have hf : ∀ w, ‖flatS J.d B.d s (rat x) 0 (s.om (J.d.emb0 h₀, embA B.d B.o h₁ * h) Φ) w‖ ≤
      max C₁ 0 * (C₃ * C₄ * C₅) ^ A₁ * X ^ ((a₅ + 2) * A₁) := by
    intro w
    have hP0 : 0 ≤ height J.W (J.d.emb0 h₀) * height B.V (embA B.d B.o h₁ * h) :=
      mul_nonneg (zero_le_one.trans (GlobalTheory.Grow.one_le_height _ _)) (zero_le_one.trans (GlobalTheory.Grow.one_le_height _ _))
    calc _ ≤ C₁ * (height J.W (J.d.emb0 h₀) * height B.V (embA B.d B.o h₁ * h)) ^ A₁ := hC₁ _ _ 0 w
      _ ≤ max C₁ 0 * (height J.W (J.d.emb0 h₀) * height B.V (embA B.d B.o h₁ * h)) ^ A₁ :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hP0 _)
      _ ≤ max C₁ 0 * (C₃ * C₄ * C₅ * X ^ (a₅ + 2)) ^ A₁ :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hP0 hP _) hM₁
      _ = _ := by rw [mul_pow, ← pow_mul]; ring
  have hg : ∀ v, ‖omz (h₀, 1) Φ₀ v‖ ≤ max C₂ 0 * X ^ A₂ := by
    intro v
    have := hC₂ h₀ 1 v
    rw [GlobalTheory.Grow.height_one, mul_one] at this
    refine this.trans ?_
    calc C₂ * height J.W₀ h₀ ^ A₂ ≤ max C₂ 0 * height J.W₀ h₀ ^ A₂ :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (by linarith) _)
      _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) q0 _) hM₂
  unfold contractT thPair
  have hvol := vL.covol.2.2
  refine (norm_setIntegral_le_of_norm_le_const (C := max C₁ 0 * (C₃ * C₄ * C₅) ^ A₁ * X ^ ((a₅ + 2) * A₁) *
    (max C₂ 0 * X ^ A₂)) (by rw [hvol]; exact ENNReal.one_lt_top) fun v _ => ?_).trans ?_
  · beta_reduce
    rw [norm_mul, norm_star, key]
    exact mul_le_mul (hf _) (hg _) (norm_nonneg _) (by positivity)
  · rw [measureReal_def, hvol, ENNReal.toReal_one, mul_one, pow_add]
    exact le_of_eq (by ring)

end GlobalTheory.PairKerBound
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.flatTensor_rowFactor_largeDepth : Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch => ∀ (t : T) (β : CosFam ch.G t) (w : locPl ch.G t) (φ : ∀ b : GlobalTheory.SplitFlip.Edge, Matrix (Fin ((locGrid ch.G t w.1).rank b.tgt)) (Fin ((locGrid ch.G t w.1).rank b.src)) (Kw w.1) → ℂ), (∀ b ∈ GlobalTheory.SplitFlip.oppositePath D.R.m, GlobalTheory.SplitFlip.IsNatDatum (unifAt w.1) (depthAt ch.G w.1) (φ b)) → ∀ (u : ∀ j : Fin D.R.m, WO (ch.G.V (.top j)) (ch.G.V (.top (j + 1)))) (y : ∀ i : Fin D.R.m, WO (ch.G.pS (.chi i D.R.m : Pair T)) (ch.G.pT (.chi i D.R.m : Pair T))), flatTensor one_le_sLen (psiAt ch.W w.1) (unitVol w.1) (moved (locGrid ch.G t w.1) (keepAt ch.G w.1) ((repsAt ch.G t w.1).elt (β w)) ((locGrid ch.G t w.1).lines₂ (GlobalTheory.SplitFlip.oppositePath D.R.m) φ)) (ch.S.colAt t w.1 u) (ch.S.rowAt t w.1 y) = flatTensor one_le_sLen (psiAt ch.W w.1) (unitVol w.1) (moved (locGrid ch.G t w.1) (keepAt ch.G w.1) ((repsAt ch.G t w.1).elt (β w)) ((locGrid ch.G t w.1).lines₂ (GlobalTheory.SplitFlip.oppositePath D.R.m) (GlobalTheory.LocAsm.exOne φ))) (ch.S.colAt t w.1 u) 0 * ∏ i : Fin D.R.m, φ (.ex i D.R.m) (ch.S.B.coord t w.1 (X := (i, D.R.m)) (Y := (i + 1, D.R.m)) ⟨i.2.le, le_rfl⟩ ⟨i.2, le_rfl⟩ ((y i).map fun a => cpt w.1 (toEAf D a))) := by
  first | exact @GlobalTheory.LocAsm.flatTensor_rowFactor | exact GlobalTheory.LocAsm.flatTensor_rowFactor | (intros; apply GlobalTheory.LocAsm.flatTensor_rowFactor <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.ExpansionInvariance


variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} in
theorem colMapV_congr (S : GridChoice W U) (t : T)
    (v v' : ∀ j : Fin D.R.m, WO (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T)) → ℂ) (x x' : ∀ j, FinPt G (.top j))
    (h : ∀ j (hj : j < D.R.m), fockComp W S.N.frC (.top t j) (v ⟨j, hj⟩) (x j * S.N.u _) (x (j + 1) * S.N.u _) =
      fockComp W S.N.frC (.top t j) (v' ⟨j, hj⟩) (x' j * S.N.u _) (x' (j + 1) * S.N.u _)) :
    colMapV S t v x = colMapV S t v' x' := by
  have e : (fun j => if hj : j < D.R.m then S.Z.scal 1 (.top t j) •
      fockComp W S.N.frC (.top t j) (v ⟨j, hj⟩) (x j * S.N.u _) (x (j + 1) * S.N.u _) else 0) =
      (fun j => if hj : j < D.R.m then S.Z.scal 1 (.top t j) •
      fockComp W S.N.frC (.top t j) (v' ⟨j, hj⟩) (x' j * S.N.u _) (x' (j + 1) * S.N.u _) else 0) := by
    funext j
    by_cases hj : j < D.R.m
    · rw [dite_eq_left hj, dite_eq_left hj, h j hj]
    · rw [dite_eq_right hj, dite_eq_right hj]
  unfold colMapV
  rw [e]

theorem pairPts_update_top : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} {Φ : G.Datum} {β : CosFam G t} {τ : PureDat G t →₀ ℂ} {μ₀ : T},
    L.Is μ₀ → (Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q)) → (∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) → t ∈ U → β ∈ S.supp t Φ → S.IsExpansion t Φ β τ →
    (∀ d ∈ τ.support, (∀ j, S.Z.HasVec (d.1 j)) ∧ ∀ i, S.Z.HasVec (d.2 i)) →
    ∀ (Ψ : FinPt G (.top 0) → VV ℂ (wt G (.top 0))) (F : FinPt G (.grid 0 D.R.m) → VV ℂ (listedWt G (.grid 0 D.R.m))),
    ∀ (x : ∀ j, FinPt G (.top j)) (y : ∀ i, FinPt G (.grid i D.R.m)) (j : ℕ) (hj : 0 < j) (hjm : j < D.R.m) (k : FinPt G (.top j)),
      finG (G.V (.top j)) k ∈ S.levTop t Φ β j hjm →
      pairPts S τ (Function.update x j (x j * k)) y (Ψ (Function.update x j (x j * k) 0)) (F (y 0)) = pairPts S τ x y (Ψ (x 0)) (F (y 0)) := by
  intro D T L sc G W U S t Φ β τ μ₀ hL hde hc ht hβ hτ hv Ψ F x y j hj hjm k hk
  obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  have hx0 : Function.update x (j + 1) (x (j + 1) * k) 0 = x 0 := Function.update_of_ne (by omega) _ _
  rw [hx0, pairPts_eq_pairV, pairPts_eq_pairV]
  set u := S.N.u (.top (j + 1)) with hu
  set g : FinPt G (.top (j + 1)) := u⁻¹ * k * u with hg
  have thv : ∀ d ∈ τ.support, ∀ j' : Fin D.R.m, IsThetaFunO W.ψ (G.pS (.top t j' : Pair T)) (G.pT (.top t j' : Pair T)) (S.Z.vec (d.1 j')) :=
    fun d hd j' => GlobalTheory.VecThetaDef.vec_isThetaFunO S.Z (d.1 j') (show j'.1 + 1 ≤ D.R.m by omega) (by simp [Pair.InRange, Node.InRange]; try omega) ((hv d hd).1 j')
  have hcol : ∀ d ∈ τ.support, colMapV S t (fun j' => S.Z.vec (d.1 j')) (Function.update x (j + 1) (x (j + 1) * k)) =
      colMapV S t (movedCol S d j hjm g) x := by
    intro d hd
    refine colMapV_congr S t _ _ _ _ fun j' hj' => ?_
    by_cases h1 : j = j'
    · subst h1
      have hA := GlobalTheory.FockTranslate.fockComp_translate W S.N.frC t j (by omega) _ (thv d hd ⟨j, hj'⟩) (x j * S.N.u _) 1 (x (j + 1) * u) g
      rw [mul_one] at hA
      have e1 : x (j + 1) * k * u = x (j + 1) * u * g := by rw [hg]; group
      have m1 : (⟨j, hj'⟩ : Fin D.R.m) ≠ ⟨j + 1, hjm⟩ := by intro h; simp [Fin.ext_iff] at h
      rw [Function.update_of_ne (by omega : j ≠ j + 1), Function.update_self, e1, hA, movedCol,
        Function.update_of_ne m1, Function.update_self]
      try simp only [OneMemClass.coe_one]
      all_goals rfl
    · by_cases h2 : j + 1 = j'
      · subst h2
        have hA := GlobalTheory.FockTranslate.fockComp_translate W S.N.frC t (j + 1) (by omega) _ (thv d hd ⟨j + 1, hj'⟩) (x (j + 1) * u) g (x (j + 1 + 1) * S.N.u _) 1
        rw [mul_one] at hA
        have e1 : x (j + 1) * k * u = x (j + 1) * u * g := by rw [hg]; group
        rw [Function.update_self, Function.update_of_ne (by omega : j + 1 + 1 ≠ j + 1), e1, hA, movedCol, Function.update_self]
        try simp only [OneMemClass.coe_one]
        all_goals rfl
      · have m1 : (⟨j', hj'⟩ : Fin D.R.m) ≠ ⟨j + 1, hjm⟩ := by intro h; simp [Fin.ext_iff] at h; omega
        have m2 : (⟨j', hj'⟩ : Fin D.R.m) ≠ ⟨j, by omega⟩ := by intro h; simp [Fin.ext_iff] at h; omega
        rw [Function.update_of_ne (by omega : j' ≠ j + 1), Function.update_of_ne (by omega : j' + 1 ≠ j + 1), movedCol,
          Function.update_of_ne m1, Function.update_of_ne m2]
  have key : pairV S t τ (fun d j' => S.Z.vec (d.1 j')) (fun d i => S.Z.vec (d.2 i)) (Function.update x (j + 1) (x (j + 1) * k)) y =
      pairV S t τ (fun d => movedCol S d j hjm g) (fun d i => S.Z.vec (d.2 i)) x y := by
    unfold pairV
    refine Finsupp.sum_congr fun d hd => ?_
    rw [hcol d hd]
  rw [key]
  refine congrArg (fun φ => φ (Ψ (x 0)) (F (y 0))) (GlobalTheory.ExpansionInvariance.pairV_eq_of_prodFun_eq S t τ _ _ _ _ ?_ ?_ (GlobalTheory.T.expansion_product_invariant_inner_vertex_level S hL hde hc ht hβ hτ hv j hjm k hk) x y)
  · intro d hd j'
    refine ⟨?_, thv d hd j'⟩
    by_cases h2 : j' = ⟨j + 1, hjm⟩
    · subst h2
      rw [movedCol, Function.update_self]
      exact (W.om_is _ (by simp [Pair.InRange, Node.InRange]; try omega)).om_pres _ _ (thv d hd _)
    · by_cases h1 : j' = ⟨j, by omega⟩
      · subst h1
        rw [movedCol, Function.update_of_ne h2, Function.update_self]
        exact (W.om_is _ (by simp [Pair.InRange, Node.InRange]; try omega)).om_pres _ _ (thv d hd _)
      · rw [movedCol, Function.update_of_ne h2, Function.update_of_ne h1]
        exact thv d hd j'
  · intro d hd i
    have h := GlobalTheory.VecThetaDef.vec_isThetaFunO S.Z (d.2 i) (show i.1 + 1 ≤ D.R.m ∧ D.R.m = D.R.m by omega) (show i.1 + 1 ≤ D.R.m ∧ D.R.m ≤ D.R.m by omega) ((hv d hd).2 i)
    exact ⟨h, h⟩

end GlobalTheory.ExpansionInvariance

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowVal

section Lin

variable {T : Type} {D : D7} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {M : Vol G}
  {ρ : RealMatch W} {t : T}

theorem rowFam_cusp (hS : GlobalTheory.FlipRun.CuspStep W M ρ t) {e : AE D} (he : IsIdemSum e (locPl G t))
    {F : Fn G (.grid 0 D.R.m)} (hF : GlobalTheory.FlipRun.IsCuspListed W.θ (.grid 0 D.R.m) F) :
    ∀ n, n ≤ D.R.m → ∀ (f : ∀ i : Fin n, Sch G (.right i D.R.m)),
      (∀ i : Fin n, ∃ φ g Q, IsLocVec W (.chi i D.R.m) e (ρ.vX i D.R.m) φ g ∧ f i = W.fock (.chi i D.R.m) g Q) →
      GlobalTheory.FlipRun.IsCuspListed W.θ (.grid n D.R.m) (liftP W M (rowPath T D.R.m n) (rowFam D.R.m n f) F) := by
  intro n
  induction n with
  | zero =>
    intro _ _ _
    exact hF
  | succ n ih =>
    intro hn f hf
    obtain ⟨φ, g, Q, hl, e1⟩ := hf (Fin.last n)
    have hprev := ih (by omega) (fun i => f i.castSucc) (fun i => hf i.castSucc)
    have h1 := (hS (.right n D.R.m) (Or.inl ⟨n, D.R.m, by omega, le_rfl, rfl⟩) e he φ g hl Q _ hprev).2
    show GlobalTheory.FlipRun.IsCuspListed W.θ (.grid (n + 1) D.R.m)
      (liftA W M (.right n D.R.m) (f (Fin.last n)) (liftP W M (rowPath T D.R.m n) (rowFam D.R.m n fun i => f i.castSucc) F))
    rw [e1]
    exact h1

theorem downFam_cusp (hS : GlobalTheory.FlipRun.CuspStep W M ρ t) {e : AE D} (he : IsIdemSum e (locPl G t)) :
    ∀ n, n ≤ D.R.m → ∀ (f : ∀ j : Fin n, Sch G (.down t D.R.m j)),
      (∀ j : Fin n, ∃ φ g Q, IsLocVec W (.mu t D.R.m j) e (ρ.vT D.R.m j) φ g ∧ f j = W.fock (.mu t D.R.m j) g Q) →
      ∀ F : Fn G (.grid D.R.m n), GlobalTheory.FlipRun.IsCuspListed W.θ (.grid D.R.m n) F →
      GlobalTheory.FlipRun.IsCuspListed W.θ (.grid D.R.m 0) (liftP W M (downPath t D.R.m n) (downFam t D.R.m n f) F) := by
  intro n
  induction n with
  | zero =>
    intro _ _ _ _ hF
    exact hF
  | succ n ih =>
    intro hn f hf F hF
    obtain ⟨φ, g, Q, hl, e1⟩ := hf (Fin.last n)
    have h1 := (hS (.down t D.R.m n) (Or.inr ⟨D.R.m, n, le_rfl, by omega, rfl⟩) e he φ g hl Q F hF).2
    have h1' : GlobalTheory.FlipRun.IsCuspListed W.θ (.grid D.R.m n) (liftA W M (.down t D.R.m n) (f (Fin.last n)) F) := by
      rw [e1]; exact h1
    have key : liftP W M (downPath t D.R.m (n + 1)) (downFam t D.R.m (n + 1) f) F =
        liftP W M (downPath t D.R.m n) (downFam t D.R.m n fun j => f j.castSucc)
          (liftA W M (.down t D.R.m n) (f (Fin.last n)) F) :=
      pathLift_comp W M (Path.one (.down t D.R.m n)) ((), f (Fin.last n)) F (downPath t D.R.m n)
        (downFam t D.R.m n fun j => f j.castSucc)
    rw [key]
    exact ih (by omega) (fun j => f j.castSucc) (fun j => hf j.castSucc) _ h1'

theorem opp_contAut (hP : GlobalTheory.Published.CuspRapidDecay) (hθ : IsInfFam W.θ) (hS : GlobalTheory.FlipRun.CuspStep W M ρ t) {e : AE D}
    (he : IsIdemSum e (locPl G t)) {F : Fn G (.grid 0 D.R.m)} (hF : GlobalTheory.FlipRun.IsCuspListed W.θ (.grid 0 D.R.m) F)
    (P : PolRow G × PolDown G) (d φ : SchRow G × SchDown G t)
    (hd : (∀ i : Fin D.R.m, IsLocVec W (.chi i D.R.m) e (ρ.vX i D.R.m) (φ.1 i) (d.1 i)) ∧
      ∀ j : Fin D.R.m, IsLocVec W (.mu t D.R.m j) e (ρ.vT D.R.m j) (φ.2 j) (d.2 j)) :
    GlobalTheory.Unf.IsContAut (G.V (.grid D.R.m 0)) (liftP W M (oppPath t D.R.m) (oppPure W t P d) F) := by
  have hr := rowFam_cusp (M := M) hS he hF D.R.m le_rfl _ fun i => ⟨φ.1 i, d.1 i, P.1 i, hd.1 i, rfl⟩
  have hdn := downFam_cusp hS he D.R.m le_rfl _ (fun j => ⟨φ.2 j, d.2 j, P.2 j, hd.2 j, rfl⟩) _ hr
  have key : liftP W M (oppPath t D.R.m) (oppPure W t P d) F =
      liftP W M (downPath t D.R.m D.R.m) (downFam t D.R.m D.R.m fun j => W.fock (.mu t D.R.m j) (d.2 j) (P.2 j))
        (liftP W M (rowPath T D.R.m D.R.m) (rowFam D.R.m D.R.m fun i => W.fock (.chi i D.R.m) (d.1 i) (P.1 i)) F) :=
    pathLift_comp W M _ _ F _ _
  rw [key]
  have hrd := rapidDec_of_cuspForm hP hθ hdn.1 hdn.2.1
  exact ⟨hrd.1, hrd.2.1⟩

theorem bplus_fsum {M₀ : Vol G} (h₀ : M₀.IsRow) (hM : M.Is t) {φ : Fn G (.top 0)} (hφ : GlobalTheory.Unf.IsContAut _ φ) {I : Type}
    (s : Finset I) (a : I → ℂ) (f : I → Fn G (.grid D.R.m 0)) (hf : ∀ i ∈ s, GlobalTheory.Unf.IsContAut _ (f i)) :
    Bplus W M₀ φ (∑ i ∈ s, a i • f i) = ∑ i ∈ s, a i * Bplus W M₀ φ (f i) := by
  suffices hs : Bplus W M φ (∑ i ∈ s, a i • f i) = ∑ i ∈ s, a i * Bplus W M φ (f i) by
    rw [bplus_indep G W M₀ M h₀ hM.isRow φ _ hφ (GlobalTheory.SeeSaw.TrcProof.contAut_sum s a f hf), hs]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [bplus_indep G W M₀ M h₀ hM.isRow φ _ hφ (hf i hi)]
  have hconv (F : Fn G (.grid D.R.m 0)) (hF : GlobalTheory.Unf.IsContAut _ F) : BplusConv W M φ F := by
    let d := G.rowDec 0 (by have := D.R.two_le_m; omega)
    have hV := G.isV (X := .top 0) (Nat.zero_le _) (fun j e => by cases e)
    have hA : IsAniso (G.V (.top 0)) := GlobalTheory.Per.isAniso_of_posDef hV.sigOK fun τ => by
      rw [hV.sig τ, hV.rank]
      simp [Node.neg]
    obtain ⟨emb, hc, hrel, hrat⟩ := GlobalTheory.Mem.UnitaryEmb.exists_embHom D _ _ _ d.isom
    have hemb : embTop G = emb := funext fun h => (hrel h _).1 ((embRel_iff d h _).2 rfl)
    have hQ : GlobalTheory.Per.Inhab.IsRatInv d.ι G.besTop.e
        (fun h n => φ h * F (n * embTop G h) * star (besChar W.ψ G.besTop n)) := by
      refine ⟨fun δ γ h n hn => (GlobalTheory.BesselChar.besChar_conj W.ψ G.besTop δ γ h n hn).1, ?_, ?_⟩
      · intro g n hn γ hγ hq
        rw [GlobalTheory.BesselChar.besChar_mul W.ψ G.besTop γ n hγ hn,
          GlobalTheory.BesselChar.besChar_rat W.ψ W.ψ_std.1 G.besTop γ hγ hq, one_mul,
          mul_assoc γ, hF.1 γ hq]
      · intro g n hn γ hγ δ hδ
        have e : (δ * n * δ⁻¹) * embTop G (γ * g) = emb γ * (n * embTop G g) := by
          rw [hemb, (hrel _ _).1 hδ]
          simp only [map_mul, mul_assoc, inv_mul_cancel_left]
        rw [(GlobalTheory.BesselChar.besChar_conj W.ψ G.besTop δ γ hδ n hn).2, e,
          hF.1 _ (hrat γ hγ), hφ.1 γ hγ]
    obtain ⟨hμ, hfd⟩ := hM.isRow.top.haar_fund
    obtain ⟨-, -, -, -, _, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (G.V (.grid D.R.m 0))
    have hemb_cont : Continuous (embTop G) := hemb.symm ▸ hc
    exact GlobalTheory.RowBplus.integrable_of_haar hQ G.besTop.e_iso d.isom hA
      (((hφ.2.comp continuous_fst).mul
        (hF.2.comp ((continuous_subtype_val.comp continuous_snd).mul (hemb_cont.comp continuous_fst)))).mul
        ((GlobalTheory.BesselChar.besChar_continuous W.ψ W.ψ_std.1 G.besTop).comp continuous_snd).star)
      hμ hfd hM.isRow.unip
  have hterms := fun i (hi : i ∈ s) => hconv (f i) (hf i hi)
  have hsum (h : GA D (G.V (.top 0))) (n : NFlag (G.V (.grid D.R.m 0)) G.besTop.e) :
      besInt W φ (∑ i ∈ s, a i • f i) h n = ∑ i ∈ s, a i * besInt W φ (f i) h n := by
    simp only [besInt, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp only [Bplus]
  simp_rw [hsum]
  have hinner (h : GA D (G.V (.top 0))) :
      (∫ n in M.fdN, ∑ i ∈ s, a i * besInt W φ (f i) h n ∂M.νN) =
        ∑ i ∈ s, a i * ∫ n in M.fdN, besInt W φ (f i) h n ∂M.νN := by
    rw [integral_finsetSum s fun i hi => ((hterms i hi).1 h).const_mul (a i)]
    exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _
  simp_rw [hinner]
  rw [integral_finsetSum s fun i hi => (hterms i hi).2.const_mul (a i)]
  exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _

theorem liftT_oppTens (τi : PolRow G × PolDown G →₀ ℂ) (τ : SchRow G × SchDown G t →₀ ℂ) (F : Fn G (.grid 0 D.R.m)) :
    liftT W M (oppPath t D.R.m) (oppTens W t τi τ) F =
      ∑ P ∈ τi.support, τi P • ∑ d ∈ τ.support, τ d • liftP W M (oppPath t D.R.m) (oppPure W t P d) F := by
  have e : liftT W M (oppPath t D.R.m) (oppTens W t τi τ) F =
      AddMonoidHom.mk' (fun x => liftT W M (oppPath t D.R.m) x F) (fun x y => liftT_add W M _ x y F) (oppTens W t τi τ) := rfl
  rw [e]

  simp only [oppTens, Finsupp.sum, map_sum, AddMonoidHom.mk'_apply, liftT_single, Finset.smul_sum, smul_smul]

end Lin

end GlobalTheory.RowVal
end
end
