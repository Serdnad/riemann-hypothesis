module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle872
public import Formalism.LocalToGlobal.HeckeThetaElements.IsHeckeElt
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle013
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1728
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle588
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle877
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle878
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralFlipScalarMemCoefficientField
import Formalism.LocalRingCardinality.DataHost
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle047
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle021
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle002
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IMemSiegel
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle068
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle843
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle854
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle001
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

section

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.LevelSeries

noncomputable section

namespace GlobalTheory.LevelSeries.FlipScalStep

def flipInv {D : D7} (e : AE D) (m : ℕ) : AE D :=
  e * incA D ((m : D.host.E)⁻¹) + cA D e * (m : AE D) + (1 - e - cA D e)

theorem flipElt_mul_flipInv {D : D7} {e : AE D} (he : IsSplitIdem D e) {m : ℕ} (hm : m ≠ 0) :
    flipElt e m * flipInv e m = 1 := by
  obtain ⟨hee, hec, -⟩ := he
  have hcc : cA D e * cA D e = cA D e := by rw [← map_mul, hee]
  have hmE : ((m : D.host.E)) ≠ 0 := Nat.cast_ne_zero.2 hm
  have hinc : (m : AE D) * incA D ((m : D.host.E)⁻¹) = 1 := by
    rw [← map_natCast (incA D) m, ← map_mul, mul_inv_cancel₀ hmE, map_one]
  unfold flipElt flipInv
  linear_combination (e + cA D e) * hinc
    + ((m : AE D) * incA D ((m : D.host.E)⁻¹) - m - incA D ((m : D.host.E)⁻¹) + 1) * (hee + hcc)
    + ((m : AE D) ^ 2 - 2 * m + incA D ((m : D.host.E)⁻¹) ^ 2 - 2 * incA D ((m : D.host.E)⁻¹) + 2) * hec

theorem mt_inv_eq {D : D7} (V : HSp D) (g : GA D V) (e : AE D) {m : ℕ} (he : IsSplitIdem D e) (hm : m ≠ 0)
    (hg : Formalism.L2.Theta.mt V g = flipElt e m • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D))) :
    Formalism.L2.Theta.mt V g⁻¹ = flipInv e m • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) := by
  have hmul : Formalism.L2.Theta.mt V g⁻¹ * Formalism.L2.Theta.mt V g = 1 := by
    unfold Formalism.L2.Theta.mt
    rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
  have hfb : (flipElt e m • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D))) *
      (flipInv e m • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D))) = 1 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul, flipElt_mul_flipInv he hm, one_smul]
  calc Formalism.L2.Theta.mt V g⁻¹ = Formalism.L2.Theta.mt V g⁻¹ * (Formalism.L2.Theta.mt V g *
        (flipInv e m • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)))) := by rw [hg, hfb, Matrix.mul_one]
    _ = _ := by rw [← Matrix.mul_assoc, hmul, Matrix.one_mul]

theorem mul_flipInv_sub {D : D7} {e : AE D} (he : IsSplitIdem D e) (m : ℕ) :
    (e + cA D e) * (flipInv e m - 1) = flipInv e m - 1 := by
  obtain ⟨hee, hec, -⟩ := he
  have hcc : cA D e * cA D e = cA D e := by rw [← map_mul, hee]
  unfold flipInv
  linear_combination (incA D ((m : D.host.E)⁻¹) - 1) * hee + ((m : AE D) - 1) * hcc
    + ((m : AE D) + incA D ((m : D.host.E)⁻¹) - 2) * hec

theorem idem_mul_flipInv_pow {D : D7} {e : AE D} (he : IsSplitIdem D e) (m n : ℕ) :
    e * flipInv e m ^ n = e * incA D ((m : D.host.E)⁻¹) ^ n := by
  obtain ⟨hee, hec, -⟩ := he
  have heb : e * flipInv e m = e * incA D ((m : D.host.E)⁻¹) := by
    unfold flipInv
    linear_combination (incA D ((m : D.host.E)⁻¹) - 1) * hee + ((m : AE D) - 1) * hec
  induction n with
  | zero => rfl
  | succ n ih =>
    linear_combination flipInv e m * ih + incA D ((m : D.host.E)⁻¹) ^ n * heb

theorem suppAt_inv {D : D7} (V : HSp D) (g : GA D V) (e : AE D) {m : ℕ} (he : IsSplitIdem D e) (hm : m ≠ 0)
    (hg : Formalism.L2.Theta.mt V g = flipElt e m • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D))) :
    Formalism.L2.Theta.SuppAt e V g⁻¹ := by
  intro i j
  rw [mt_inv_eq V g e he hm hg, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  calc (e + cA D e) * (flipInv e m * (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j -
        (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j)
      = ((e + cA D e) * (flipInv e m - 1)) * (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j := by ring
    _ = _ := by rw [mul_flipInv_sub he m]; ring

theorem isDetAt_inv {D : D7} (V : HSp D) (g : GA D V) (e : AE D) {m : ℕ} (he : IsSplitIdem D e) (hm : m ≠ 0)
    (hg : Formalism.L2.Theta.mt V g = flipElt e m • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)))
    {x : (AE D)ˣ} (hx : IsFlipDet V e m x) : Formalism.L2.Theta.IsDetAt e V g⁻¹ x := by
  unfold Formalism.L2.Theta.IsDetAt
  rw [mt_inv_eq V g e he hm hg, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin,
    idem_mul_flipInv_pow he m]
  unfold IsFlipDet at hx
  have hee := he.1
  have hmE : ((m : D.host.E)) ≠ 0 := Nat.cast_ne_zero.2 hm
  have hinc : incA D ((m : D.host.E)⁻¹) * (m : AE D) = 1 := by
    rw [← map_natCast (incA D) m, ← map_mul, inv_mul_cancel₀ hmE, map_one]
  have hpow : incA D ((m : D.host.E)⁻¹) ^ V.rank * (m : AE D) ^ V.rank = 1 := by
    rw [← mul_pow, hinc, one_pow]
  have hy : (e * incA D ((m : D.host.E)⁻¹) ^ V.rank + (1 - e)) * (e * (m : AE D) ^ V.rank + (1 - e)) = 1 := by
    linear_combination (2 - incA D ((m : D.host.E)⁻¹) ^ V.rank - (m : AE D) ^ V.rank) * hee + e ^ 2 * hpow
  linear_combination (e * incA D ((m : D.host.E)⁻¹) ^ V.rank + (1 - e)) * hx - (x : AE D) * hy

theorem om_inv_flip_eq : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χV χW om → ∀ (P : Formalism.L2.DIV.Pl D.host.E) (e : AE D) (m : ℕ) (g : GA D V) (x : (AE D)ˣ) (ℓ : (WO V W → ℂ) →ₗ[ℂ] ℂ), Formalism.L2.NTheta.IsIdemAt e P → m ≠ 0 → Formalism.L2.Theta.mt V g = flipElt e m • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) → IsFlipDet V e m x → (∀ y : WO V W, IsHalf (cA D e) y → ∀ φ : WO V W → ℂ, IsThetaFunO ψ V W φ → ℓ (heisO ψ V W y φ) = ℓ φ) → ∃ r : ℝ, 0 < r ∧ ∀ f : WO V W → ℂ, IsThetaFunO ψ V W f → ℓ (om (g⁻¹, 1) f) = (r : ℂ) * ((χW x : Circle) : ℂ)⁻¹ * ℓ f := by
  intro D ψ V W χV χW om hW P e m g x ℓ hP hm hg hx hℓ
  have he : IsSplitIdem D e := hP.1
  have hm1 : Formalism.L2.Theta.mt W (1 : GA D W) = 1 := by
    unfold Formalism.L2.Theta.mt
    rw [map_one, Units.val_one]
  have h1 : Formalism.L2.Theta.SuppAt e W 1 := fun i j => by rw [hm1, sub_self, Matrix.zero_apply, mul_zero]
  have h1' : Formalism.L2.Theta.IsDetAt e W 1 1 := by
    unfold Formalism.L2.Theta.IsDetAt
    rw [hm1, Matrix.det_one, mul_one, add_sub_cancel, Units.val_one]
  obtain ⟨r, hr, H⟩ := hW.om_split e he g⁻¹ 1 (suppAt_inv V g e he hm hg) h1 x 1 (isDetAt_inv V g e he hm hg hx) h1'
  refine ⟨r, hr, fun f hf => ?_⟩
  rw [H ℓ (fun u hu f hf => hℓ u hu f hf) f hf, splitFacO, map_one, mul_one, Circle.coe_inv]

end GlobalTheory.LevelSeries.FlipScalStep
end
end

section

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.LevelSeries


theorem _root_.GlobalTheory.T.absNorm_maxPowDividing_conjugatePlace : ∀ (D : D7) (P : Formalism.L2.DIV.Pl D.host.E) (N : ℕ), Ideal.absNorm ((Formalism.L2.DIV.conjPl P).maxPowDividing (Ideal.span {((N : ℕ) : 𝓞 D.host.E)})) = Ideal.absNorm (P.maxPowDividing (Ideal.span {((N : ℕ) : 𝓞 D.host.E)})) := by
  first | exact @GlobalTheory.ConjNormPow.absNorm_maxPowDividing_conjPl | exact GlobalTheory.ConjNormPow.absNorm_maxPowDividing_conjPl | (intros; apply GlobalTheory.ConjNormPow.absNorm_maxPowDividing_conjPl <;> assumption)
end

section

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.LevelSeries

namespace GlobalTheory.FlipIdemSum

open Formalism.L2.NTheta (IsIdemAt)

theorem idemSum_flip_subset : ∀ (D : D7) (e eT e' : AE D) (P T : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e P → IsIdemSum eT T → T ⊆ P → IsIdemSum e' ((P \ T) ∪ T.image Formalism.L2.DIV.conjPl) → e' = e - eT + cA D eT := by
  intro D e eT e' P T he hT hTP he'
  obtain ⟨⟨es, hes, hsum⟩, hc⟩ := he
  obtain ⟨⟨ts, hts, htsum⟩, -⟩ := hT
  obtain ⟨⟨gs, hgs, hgsum⟩, -⟩ := he'
  have hmul : ∀ Q ∈ P, e * es Q = es Q := fun Q hQ => by
    rw [hsum, Finset.sum_mul, Finset.sum_eq_single_of_mem Q hQ]
    · exact (hes Q hQ).1.1
    · intro R hR hne
      exact GlobalTheory.Tow.idemAt_orth (hes R hR) (hes Q hQ) hne
  have hconj : ∀ PP ∈ P, IsIdemAt (cA D (es PP)) (Formalism.L2.DIV.conjPl PP) := fun PP hPP =>
    GlobalTheory.MovedIdem.isIdemAt_conj (hes PP hPP) fun _ => Iff.rfl
  have hne : ∀ (a : AE D) (Q : HeightOneSpectrum (𝓞 D.host.E)), IsIdemAt a Q → a ≠ 0 := by
    rintro a Q h rfl
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot Q.ne_bot
    have := (h.2 x hx0).1 hx
    rw [zero_mul, RingHom.map_zero] at this
    exact this (zero_mem _)
  have hdisj : Disjoint (P \ T) (T.image Formalism.L2.DIV.conjPl) := by
    rw [Finset.disjoint_left]
    intro Q hQ hQ'
    obtain ⟨PP, hPP, rfl⟩ := Finset.mem_image.1 hQ'
    have hPPP := hTP hPP
    have h1 := hmul _ (Finset.mem_sdiff.1 hQ).1
    rw [GlobalTheory.Tow.idemAt_unique (hes _ (Finset.mem_sdiff.1 hQ).1) (hconj PP hPPP)] at h1
    have hea' : cA D e * cA D (es PP) = cA D (es PP) := by rw [← map_mul, hmul PP hPPP]
    exact hne _ _ (hconj PP hPPP)
      (by linear_combination (-1 : AE D) * h1 - e * hea' + cA D (es PP) * hc)
  have hinj : ∀ a ∈ T, ∀ b ∈ T, Formalism.L2.DIV.conjPl a = Formalism.L2.DIV.conjPl b → a = b := fun a _ b _ hab => by
    rw [← Formalism.L2.DIV.conjPl_conjPl a, hab, Formalism.L2.DIV.conjPl_conjPl b]
  have hA : ∑ Q ∈ P \ T, gs Q = ∑ Q ∈ P \ T, es Q := Finset.sum_congr rfl fun Q hQ =>
    GlobalTheory.Tow.idemAt_unique (hgs Q (Finset.mem_union_left _ hQ)) (hes Q (Finset.mem_sdiff.1 hQ).1)
  have hB : ∑ Q ∈ T.image Formalism.L2.DIV.conjPl, gs Q = cA D eT := by

    rw [Finset.sum_image hinj, htsum, map_sum]
    refine Finset.sum_congr rfl fun PP hPP => ?_
    rw [GlobalTheory.Tow.idemAt_unique (hts PP hPP) (hes PP (hTP hPP))]
    exact GlobalTheory.Tow.idemAt_unique (hgs _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hPP))) (hconj PP (hTP hPP))
  have hTs : eT = ∑ Q ∈ T, es Q := by
    rw [htsum]
    exact Finset.sum_congr rfl fun PP hPP => GlobalTheory.Tow.idemAt_unique (hts PP hPP) (hes PP (hTP hPP))
  rw [hgsum, Finset.sum_union hdisj, hA, hB, hTs, hsum, ← Finset.sum_sdiff hTP]
  ring

end GlobalTheory.FlipIdemSum
end

section

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.LevelSeries


theorem _root_.GlobalTheory.T.exists_idempotentSum_subset_and_conjugate_flip : ∀ (D : D7) (e : AE D) (P T : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e P → T ⊆ P → (∃ eT : AE D, IsIdemSum eT T) ∧ ∃ e' : AE D, IsIdemSum e' ((P \ T) ∪ T.image Formalism.L2.DIV.conjPl) := by
  first | exact @GlobalTheory.IdemFlip.idemSum_sub_and_flip | exact GlobalTheory.IdemFlip.idemSum_sub_and_flip | (intros; apply GlobalTheory.IdemFlip.idemSum_sub_and_flip <;> assumption)
end

section

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.LevelSeries


theorem _root_.GlobalTheory.T.levelHalf_le_conj_place_of_not_le : ∀ (D : D7) (H : Geo.Tor.Host D.host.E) (l₂ : Geo.Tor.Level H) (Q : Formalism.L2.DIV.Pl D.host.E), ((l₂.M : ℕ) : 𝓞 D.host.E) ∈ Q.asIdeal → ¬ l₂.Mb ≤ Q.asIdeal → l₂.Mb ≤ (Formalism.L2.DIV.conjPl Q).asIdeal := by
  first | exact @GlobalTheory.LevelSeries.mb_le_conjPl_of_not_le | exact GlobalTheory.LevelSeries.mb_le_conjPl_of_not_le | (intros; apply GlobalTheory.LevelSeries.mb_le_conjPl_of_not_le <;> assumption)
end

section

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.LevelSeries


theorem _root_.GlobalTheory.T.weil_representation_preserves_norm : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ (μ : MeasureTheory.Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ (p : GA D S × GA D T) (f : WO S T → ℂ), IsThetaFunO ψ S T f → nrm2 μ 𝓕 f = 1 → nrm2 μ 𝓕 (om p f) = 1 := by
  first | exact @GlobalTheory.WeilUnitNorm.weil_norm_one_of_unit_norm | exact GlobalTheory.WeilUnitNorm.weil_norm_one_of_unit_norm | (intros; apply GlobalTheory.WeilUnitNorm.weil_norm_one_of_unit_norm <;> assumption)
end

section

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.LevelSeries


theorem _root_.GlobalTheory.T.exists_field_element_local_components_level_number : ∀ (E : Type) [Field E] [NumberField E] (χ : Formalism.L2.Host.HChar E) (M₀ : ℕ) (u : Eˣ), (u : E) = ((M₀ : ℕ) : E) → ∀ (T : Finset (HeightOneSpectrum (𝓞 E))), ∃ a : Eˣ, IsIntegral ℤ (a : E) ∧ (∀ v ∈ T, χ.locK v a = χ.locK v u ∧ v.valuation E (a : E) = v.valuation E ((M₀ : ℕ) : E)) ∧ ∀ v : HeightOneSpectrum (𝓞 E), ((M₀ : ℕ) : 𝓞 E) ∈ v.asIdeal → v ∉ T → χ.locK v a = 1 ∧ v.valuation E (a : E) = 1 := by
  first | exact @GlobalTheory.LevelFieldApprox.exists_approx | exact GlobalTheory.LevelFieldApprox.exists_approx | (intros; apply GlobalTheory.LevelFieldApprox.exists_approx <;> assumption)
end

section

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.LevelSeries


theorem _root_.GlobalTheory.T.centralFlipScalar_mem_coefficientField : ∀ (E : Type) [Field E] [NumberField E] (χ : Formalism.L2.Host.HChar E) (M₀ r w : ℕ) (u a : Eˣ) (T : Finset (HeightOneSpectrum (𝓞 E))) (k : Type) [Field k] (σ : k →+* ℂ), Odd w → (u : E) = ((M₀ : ℕ) : E) → IsIntegral ℤ (a : E) → (∀ v ∈ T, ((M₀ : ℕ) : 𝓞 E) ∈ v.asIdeal) → (∀ v : HeightOneSpectrum (𝓞 E), ((M₀ : ℕ) : 𝓞 E) ∉ v.asIdeal → χ.UnrAt v) → χ.ValuesIn (-1 / 2) σ → (∃ y : k, ((χ.inf a : ℂˣ) : ℂ) = σ y * ((|((Algebra.norm ℚ (a : E) : ℚ) : ℝ)| ^ (-(w : ℝ) / 2) : ℝ) : ℂ)) → (∀ v ∈ T, χ.locK v a = χ.locK v u ∧ v.valuation E (a : E) = v.valuation E ((M₀ : ℕ) : E)) → (∀ v : HeightOneSpectrum (𝓞 E), ((M₀ : ℕ) : 𝓞 E) ∈ v.asIdeal → v ∉ T → χ.locK v a = 1 ∧ v.valuation E (a : E) = 1) → (∏ PP ∈ T, ((χ.locK PP u : ℂˣ) : ℂ) ^ r) * ((Real.sqrt ((∏ PP ∈ T, Ideal.absNorm (PP.maxPowDividing (Ideal.span {((M₀ : ℕ) : 𝓞 E)})) ^ (r * w) : ℕ) : ℝ) : ℝ) : ℂ)⁻¹ ∈ σ.fieldRange := by
  first | exact @GlobalTheory.FlipScalField.mem_fieldRange | exact GlobalTheory.FlipScalField.mem_fieldRange | (intros; apply GlobalTheory.FlipScalField.mem_fieldRange <;> assumption)
end

end

section

@[expose] public section

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.LevelSeries


theorem _root_.GlobalTheory.T.isIdemSum_conjugatePlaces_subset_eq_flip : ∀ (D : D7) (e eT e' : AE D) (P T : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e P → IsIdemSum eT T → T ⊆ P → IsIdemSum e' ((P \ T) ∪ T.image Formalism.L2.DIV.conjPl) → e' = e - eT + cA D eT := by
  first | exact @GlobalTheory.FlipIdemSum.idemSum_flip_subset | exact GlobalTheory.FlipIdemSum.idemSum_flip_subset | (intros; apply GlobalTheory.FlipIdemSum.idemSum_flip_subset <;> assumption)

end
end
