module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFixedIff
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSteinberg
public import Formalism.LocalToGlobal.Columns.Bundle023
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CongruenceLevelEqDepthSucc
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle129
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle247
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle131
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle147
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle136
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle236
public import Formalism.LocalToGlobal.Columns.Bundle032
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
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
import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import ReciprocityTheory.Automorphisms.PlaceA
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle022
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle016

@[expose] public section

section

noncomputable section

namespace GlobalTheory.RankOneComp

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP _root_.Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField
  IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil ValuativeRel

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section Char

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] [_root_.NumberField.IsTotallyComplex E]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}

theorem locPar_ofChar_unr_iff (hL : GlobalTheory.Published.LocalLanglandsGL) (χ : HChar E) (h : IsPlaceOver A w) :
    (ParLaws.locPar hL (CG.ofChar χ) h).unr ↔ χ.UnrAt w := by
  obtain ⟨a, ha, ε, -, H⟩ := ParLaws.isRec_locRec hL h
  rw [ParLaws.locPar_ofChar, H.one, Test.unr_lpOfChar_iff ha (ParLaws.isSmoothChar_loc χ w)]
  refine forall_congr' fun x => imp_congr_left ?_
  have h0 : Valued.v (x : w.adicCompletion E) ≠ 0 := by simp
  rw [← ord_eq_zero_iff, SphCompletion.ord_completion, neg_eq_zero, IsUnitAt]
  constructor
  · intro hl
    rw [← WithZero.exp_log h0, hl, WithZero.exp_zero]
  · intro hv
    rw [hv, WithZero.log_one]

theorem locPar_ofChar_frob (hL : GlobalTheory.Published.LocalLanglandsGL) (χ : HChar E) (h : IsPlaceOver A w) (hu : χ.UnrAt w) :
    (ParLaws.locPar hL (CG.ofChar χ) h).frobEig = {(((χ.val w)⁻¹ : ℂˣ) : ℂ)} := by
  have e : χ.loc w = SmGL.unrChar (w.adicCompletion E) (χ.val w) := by
    refine MonoidHom.ext fun x => ?_
    have h2 := unif_spec w
    have h0 : Valued.v (x : w.adicCompletion E) ≠ 0 := by simp
    have h1 : IsUnitAt w (x * (atFin w (unif w) ^ ord (w.adicCompletion E) x)⁻¹) := by
      unfold IsUnitAt IsUnifAt at *
      rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val, map_mul,
        map_inv₀, map_zpow₀, h2, ← WithZero.exp_zsmul, SphCompletion.ord_completion]
      simp only [smul_eq_mul, mul_neg, mul_one, neg_neg]
      rw [WithZero.exp_log h0, mul_inv_cancel₀ h0]
    have h3 := hu _ h1
    rw [map_mul, map_inv, map_zpow, mul_inv_eq_one] at h3
    exact h3
  obtain ⟨a, ha, ε, -, H⟩ := ParLaws.isRec_locRec hL h
  have e2 : ParLaws.locPar hL (CG.ofChar χ) h = WD.mk (WDRep.diag h fun _ : Fin 1 => (χ.val w)⁻¹) := by
    rw [ParLaws.locPar_ofChar, H.one]
    have : ∀ (ξ : (w.adicCompletion E)ˣ →* ℂˣ) (hξ : WeilDeligne.IsSmooth (ξ.comp a)),
        ξ = SmGL.unrChar (w.adicCompletion E) (χ.val w) →
        WD.lpOfChar h (ξ.comp a) hξ = WD.mk (WDRep.diag h fun _ : Fin 1 => (χ.val w)⁻¹) := by
      rintro ξ hξ rfl
      exact Test.lpOfChar_unrChar ha _ _
    exact this _ _ e
  rw [e2, WD.frobEig_diag]
  simp

end Char

end GlobalTheory.RankOneComp

end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Col2 GlobalTheory.TopStep

namespace GlobalTheory.TopLevQ

section Gen

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K]

theorem lamQB_prinCong (P : HeightOneSpectrum (𝓞 E)) (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {N : ℕ} (r c : ℕ) (hc : 0 < c)
    (k : GLint E N P) (hk : k ∈ prinCong N P c) : LocE.lamQB ξ r N k.1.toLinearMap = 1 := by
  have h1 := redGL_of_prinCong hc hk
  refine twLamQB_red_one P ξ le_rfl k.1 fun s t _ _ _ _ => ⟨glint_entry k s t, ?_⟩
  have h2 := congrArg (fun M : GL (Fin N) (𝓞 E ⧸ P.asIdeal) => (M : Matrix (Fin N) (Fin N) (𝓞 E ⧸ P.asIdeal)) s t) h1
  simp only [redGL_val, Units.val_one, Matrix.one_apply] at h2
  exact h2

theorem levI_ext {N : ℕ} {P : HeightOneSpectrum (𝓞 E)} {A B : LevI E K N P} (e : A.H = B.H)
    (e' : ∀ k (h1 : k ∈ A.H) (h2 : k ∈ B.H), A.lam ⟨k, h1⟩ = B.lam ⟨k, h2⟩) : A = B := by
  obtain ⟨H, lam⟩ := A
  obtain ⟨H', lam'⟩ := B
  obtain rfl : H = H' := e
  obtain rfl : lam = lam' := MonoidHom.ext fun a => e' a.1 a.2 a.2
  rfl

theorem level_congruence_eq_twisted_k1 (P : HeightOneSpectrum (𝓞 E)) (hu : ((qOf P : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ)
    {N n : ℕ} (hN : N = n + 1) (r b c : ℕ) (hn : n = r + b) :
    levCong hN P c ⟨HQ (𝓞 E ⧸ P.asIdeal) n r b, (lamQ ξ n r b)⁻¹⟩ = kOneLevel P N r (c + 1) ξ := by
  set l : Lev (𝓞 E ⧸ P.asIdeal) K n := ⟨HQ (𝓞 E ⧸ P.asIdeal) n r b, (lamQ ξ n r b)⁻¹⟩
  have hH : (levCong hN P c l).H = twK1H P N r (c + 1) := by
    refine le_antisymm (sup_le ?_ (GlobalTheory.T.principal_congruence_le_twisted_k1 P r (c + 1) c.succ_pos)) fun g hg => ?_
    · rintro _ ⟨j, hj, rfl⟩
      exact GlobalTheory.T.block_ext_mem_twisted_k1 P hu hN r b (c + 1) hn j hj
    · obtain ⟨j, hj, hb⟩ := GlobalTheory.T.twisted_k1_block_decomposition P hN r b c hn g hg
      exact (mem_levCong hN c l g).2 ⟨j, hj, hb⟩
  refine levI_ext hH fun k h1 h2 => ?_
  obtain ⟨j, hj, hb⟩ := (mem_levCong hN c l k).1 h1
  rw [levCong_lam hN c l h1 hj hb]
  apply Units.ext
  have hjK : extI hN P j ∈ twK1H P N r (c + 1) := GlobalTheory.T.block_ext_mem_twisted_k1 P hu hN r b (c + 1) hn j hj
  have hbK : (extI hN P j)⁻¹ * k ∈ twK1H P N r (c + 1) := GlobalTheory.T.principal_congruence_le_twisted_k1 P r (c + 1) c.succ_pos hb
  have hk : (⟨k, h2⟩ : twK1H P N r (c + 1)) = ⟨_, hjK⟩ * ⟨_, hbK⟩ := Subtype.ext (mul_inv_cancel_left _ _).symm
  show _ = ((kOneCharacter P N r (c + 1) ξ).toHomUnits ⟨k, h2⟩ : K)
  rw [MonoidHom.coe_toHomUnits, hk, map_mul]
  show _ = LocE.lamQB ξ r N (extI hN P j).1.toLinearMap * LocE.lamQB ξ r N ((extI hN P j)⁻¹ * k).1.toLinearMap
  rw [lamQB_prinCong P ξ r (c + 1) c.succ_pos _ hb, mul_one, extI_val, GlobalTheory.T.rowTypeCharacter_blockSumOne_eq P ξ hN r (by omega) j.1,
    GlobalTheory.TopLaw.lamQB_eq_red ξ hn j hj]
  rfl

end Gen

section Top

theorem levQTop_eq_twTt : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S), X.Ok → Pr.Ok → IsSel X sel → (∀ i, Pr.g i ∈ S) → (∀ v, Pr.T v ∈ S) → levQTop R sel mu (4 * R.m) = twTt (R := R) sel mu R.m := by
  intro X Pr R _ sel S mu hX hPr hsel _ _
  funext Q
  have hu : ((qOf Q.1 : ℕ) : 𝓞 X.E) ∉ Q.1.asIdeal ^ 2 :=
    (GlobalTheory.ColPeriod.levelPrimes X Pr sel S mu hX hPr hsel ⟨Q.1, by classical exact Finset.mem_union_right _ Q.2⟩).1.2
  exact level_congruence_eq_twisted_k1 Q.1 hu _ (N_m_succ R) R.r (R.m * R.t) (4 * R.m) (rank_X'_eq R)

end Top
end GlobalTheory.TopLevQ
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.L2.Host

namespace GlobalTheory.LocCompTy

open GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf

theorem rt_mem_isoTyp {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (a : NG.AlgWt L n)
    (S : Submodule ℂ (GAf L n → a.W)) (h : GAf L n) {f : GAf L n → a.W}
    (hf : f ∈ NG.isoTyp a.ρ S) : NG.rt L n h f ∈ NG.isoTyp a.ρ S := by
  have : NG.isoTyp a.ρ S ≤ (NG.isoTyp a.ρ S).comap (NG.rt L n h) := by
    refine sSup_le fun S' hS' => ?_
    intro y hy
    exact le_sSup hS' (hS'.1.1.stable h y hy)
  exact this hf



end GlobalTheory.LocCompTy
end
