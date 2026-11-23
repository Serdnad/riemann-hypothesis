module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle043
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle010
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelValuesThird
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle763
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle072
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.NotMemSpanOfCommute
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.OmVacuumEqSplitFacSmulSum
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1067
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1151
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle568
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle349
import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtA
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle237
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle846
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitAtOfIsSplitPl
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle839
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle703
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle047
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmissibleEmptyOfGood
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivOfNotLinearIndependent
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle002
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IMemSiegel
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle843
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle648
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle712
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle465

@[expose] public section

section

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum


namespace GlobalTheory.StdAtPrime

theorem bnd_inv_of_hLat_std (D : D7) (ι : (Af D.host.F ⊗[D.host.F] D.host.E) ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E)
    (h1 : ∀ x : D.host.E, ι ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) = algebraMap D.host.E _ x)
    (h2 : ∀ y, y ∈ intAE D ↔ ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (ι y P) ≤ 1)
    (V : HSp D) (hL : Bridge.hLat V 1 = Formalism.L2.Pj.stdLat D.host.E V.rank) (p : ℕ) (k : Bridge.Gf V)
    (hk : Bridge.hLat V k = Formalism.L2.Pj.stdLat D.host.E V.rank) :
    Bnd p (Matrix.GeneralLinearGroup.map ι.toRingHom k.1)⁻¹.1 := by
  refine ⟨1, Nat.coprime_one_left p, fun i j Q => ?_⟩
  have hx : (Pi.single j (1 : D.host.E) : Fin V.rank → D.host.E) ∈ Bridge.hLat V k := by
    rw [hk]
    refine Submodule.mem_pi.2 fun i' _ => ?_
    by_cases h : i' = j
    · subst h; rw [Pi.single_eq_same]; exact Submodule.mem_one.2 ⟨1, map_one _⟩
    · rw [Pi.single_eq_of_ne h]; exact zero_mem _
  have := (GlobalTheory.ClassScalarValue.mem_hLat ι h1 h2 V hL k _).1 hx i Q
  have e : (fun j' => algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E)
      ((Pi.single j (1 : D.host.E) : Fin V.rank → D.host.E) j')) = Pi.single j 1 := by
    funext j'
    by_cases h : j' = j
    · subst h; simp
    · simp [Pi.single_eq_of_ne h]
  rw [e, Matrix.mulVec_single_one] at this
  rw [Nat.cast_one, one_mul]
  exact this


end GlobalTheory.StdAtPrime
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl idem SplitProj IsIdemOf IsProjAt adjCo grpCo frCo)
open GlobalTheory.DownLift.GenSplit

noncomputable section

namespace GlobalTheory.DownLift.GenSplit.SupportBound

open GlobalTheory.SplitScalar

variable {D : D7}

theorem exists_pow_le {v : FinPl D} {ϖ : OI v} (hϖ : Irreducible ϖ) {c d : Fv D.host.F v} (hc : c ≠ 0) (hd : d ≠ 0) :
    ∃ N : ℕ, Valued.v (algebraMap (OI v) (Fv D.host.F v) (ϖ ^ N)) ≤ Valued.v c ∧
      Valued.v (algebraMap (OI v) (Fv D.host.F v) (ϖ ^ N)) ≤ Valued.v d := by
  have h1 : Valued.v (algebraMap (OI v) (Fv D.host.F v) ϖ) < 1 := by
    refine lt_of_le_of_ne ϖ.2 fun h => hϖ.not_isUnit ?_
    exact HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.2 h
  have h2 : min (Valued.v c) (Valued.v d) ≠ 0 := by
    rcases min_choice (Valued.v c) (Valued.v d) with h | h <;> rw [h]
    · exact (Valuation.ne_zero_iff _).2 hc
    · exact (Valuation.ne_zero_iff _).2 hd
  obtain ⟨N, hN⟩ := exists_pow_lt₀ h1 (Units.mk0 _ h2)
  refine ⟨N, ?_, ?_⟩ <;> rw [map_pow, map_pow]
  · exact hN.le.trans (min_le_left _ _)
  · exact hN.le.trans (min_le_right _ _)

theorem rdQ_ne_zero {v : FinPl D} (φ : SplitProj D v) {x : D.host.E} (hx : x ≠ 0) : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdQ φ x ≠ 0 := by
  have h : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdQ φ x * GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdQ φ x⁻¹ = 1 := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdQ
    rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_inv_cancel₀ hx]
    exact map_one φ
  exact left_ne_zero_of_mul_eq_one h

theorem map_nsmul_of_add {A B : Type} [AddGroup A] [AddGroup B] {κ : A → B} (h : ∀ x y, κ (x + y) = κ x + κ y) (k : ℕ)
    (x : A) : κ (k • x) = k • κ x :=
  map_nsmul (AddMonoidHom.mk' κ h) k x

theorem symplO_nsmul (S T : HSp D) (k : ℕ) (x y : WO S T) : symplO S T (k • x) y = symplO S T x (k • y) := by
  rw [← Nat.cast_smul_eq_nsmul (AE D), symplO_smul, map_natCast, Nat.cast_smul_eq_nsmul]

theorem level_and_support : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (Formalism.IndefR.Lev.EAf D)) (βT : GL (Fin T.rank) (Formalism.IndefR.Lev.EAf D)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (v : FinPl D) (φ : SplitProj D v) (e : Formalism.L2.Theta.AE D), IsIdemOf φ e → ∀ (ϖ : OI v), Irreducible ϖ → ∀ f, IsThetaFunO ψ S T f → ∃ N : ℕ, (∀ z ∈ halfPow φ S T (frCo φ βS) (frCo φ βT) e ϖ N, heisO ψ S T z f = f) ∧ ∀ ℓ, InvForm ψ S T e ℓ → ∀ x, IsHalf (cA D e) x → ℓ (heisO ψ S T x f) ≠ 0 → Bdd ϖ N (adjCo φ S T (frCo φ βS) (frCo φ βT) x) := by
  intro D ψ hψ S T ΛS ΛT βS βT hS hT hfS hfT v φ e he ϖ hϖ f hf
  obtain ⟨U, hU, hUf⟩ := hf.level
  obtain ⟨k, hk, hkU⟩ := (GlobalTheory.LatLevel.level_of_generators D S T _ _ hS hT
    (GlobalTheory.LatFinGen.latO_finitely_generated D S T _ _ hS hT)).1 U hU
  obtain ⟨hd, -, -⟩ := GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T ΛS ΛT hψ hS hT
  obtain ⟨-, a, -, ha0, -, himg⟩ := GlobalTheory.SplitLatticeHalves.splitLattice D S T ΛS ΛT βS βT hS hT hfS hfT v φ e he
  obtain ⟨⟨hadd, hbij, -⟩, -⟩ := GlobalTheory.PlaceTensor.adjCo_isCoord D S T ΛS ΛT hS hT v φ e he (frCo φ βS) (frCo φ βT)
  have hst := @idem_smul_mem D S T ΛS ΛT _ he.1.1
  have he' := isSplitIdem_conj he.1
  have hb := rdQ_ne_zero φ (star_ne_zero.2 ha0)
  generalize GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdQ φ (star a) = b at hb himg
  generalize (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) = Λ at *
  haveI : CharZero (Fv D.host.F v) := algebraRat.charZero _
  have hk0 : (k : Fv D.host.F v) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  have hkv : Valued.v (k : Fv D.host.F v) ≠ 0 := (Valuation.ne_zero_iff _).2 hk0
  obtain ⟨N, hN1, hN2⟩ := exists_pow_le hϖ (mul_ne_zero hk0 hb) (mul_ne_zero hk0 (inv_ne_zero hb))
  refine ⟨N, fun z hz => ?_, fun ℓ hℓ x hx hne i j => ?_⟩
  · have hy : (k : Fv D.host.F v)⁻¹ • adjCo φ S T (frCo φ βS) (frCo φ βT) z ∈
        {y : Matrix (Fin S.rank) (Fin T.rank) (Fv D.host.F v) | ∀ i j, Valued.v (y i j) ≤ Valued.v b} := by
      intro i j
      obtain ⟨o, ho⟩ := hz.2 i j
      rw [Matrix.smul_apply, ho, smul_eq_mul, map_mul, map_mul, map_mul, map_inv₀, inv_mul_le_iff₀ (zero_lt_iff.2 hkv),
        ← Valuation.map_mul _ (k : Fv D.host.F v)]
      exact (mul_le_of_le_one_right' o.2).trans hN1
    rw [← himg] at hy
    obtain ⟨t, ⟨ht, hth⟩, hty⟩ := hy
    have : z = k • t := by
      refine hbij.injOn hz.1 (isHalf_nsmul hth k) ?_
      rw [map_nsmul_of_add hadd, hty, ← Nat.cast_smul_eq_nsmul (Fv D.host.F v), smul_smul, mul_inv_cancel₀ hk0, one_smul]
    exact hUf z (this ▸ hkU t ht) (half_fin he' hz.1)
  · have hkx : k • x ∈ Λ := by
      by_contra hn
      obtain ⟨l, hl, hlh, hl1⟩ := exists_dual_half he' hd (by rw [GlobalTheory.DualPairCheck.cA_cA]; exact hst)
        (isHalf_nsmul hx k) hn
      rw [GlobalTheory.DualPairCheck.cA_cA] at hlh
      have hlk := isHalf_nsmul hlh k
      have h2 := hℓ _ hlk _ (GlobalTheory.FinTranslate.isTheta_heisO_fin hψ.1 (half_fin he' hx) hf)
      rw [heisO_comm, hUf _ (hkU l hl) (half_fin he.1 hlk), map_smul, smul_eq_mul, symplO_nsmul] at h2
      exact hl1 (mul_right_cancel₀ hne (h2.trans (one_mul _).symm))
    have hy : adjCo φ S T (frCo φ βS) (frCo φ βT) (k • x) ∈
        {y : Matrix (Fin S.rank) (Fin T.rank) (Fv D.host.F v) | ∀ i j, Valued.v (y i j) ≤ Valued.v b} := by
      rw [← himg]
      exact ⟨_, ⟨hkx, isHalf_nsmul hx k⟩, rfl⟩
    have h3 := hy i j
    rw [map_nsmul_of_add hadd, Matrix.smul_apply, nsmul_eq_mul] at h3
    refine ⟨⟨algebraMap (OI v) (Fv D.host.F v) (ϖ ^ N) * adjCo φ S T (frCo φ βS) (frCo φ βT) x i j, ?_⟩, rfl⟩
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, Valuation.map_mul]
    refine (mul_le_mul_left hN2 _).trans ?_
    rw [← Valuation.map_mul, mul_right_comm, Valuation.map_mul, map_inv₀]
    exact mul_inv_le_one_of_le₀ h3 zero_le'

end GlobalTheory.DownLift.GenSplit.SupportBound

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl idem SplitProj IsIdemOf IsProjAt adjCo grpCo frCo)
open GlobalTheory.DownLift.GenSplit

noncomputable section

namespace GlobalTheory.DownLift.GenSplit.DualSep

variable {D : D7}

theorem algebraMap_OI {v : FinPl D} (o : OI v) : algebraMap (OI v) (Fv D.host.F v) o = (o : Fv D.host.F v) := rfl

theorem mem_pow_iff {v : FinPl D} (ϖ : OI v) (hϖ : (ϖ : Fv D.host.F v) ≠ 0) (N : ℕ) (x : Fv D.host.F v) :
    (∃ o : OI v, x = algebraMap (OI v) (Fv D.host.F v) (ϖ ^ N * o)) ↔
      Valued.v x ≤ Valued.v (ϖ : Fv D.host.F v) ^ N := by
  constructor
  · rintro ⟨o, rfl⟩
    rw [algebraMap_OI, Subring.coe_mul, SubmonoidClass.coe_pow, map_mul, map_pow]
    have ho : Valued.v (o : Fv D.host.F v) ≤ 1 :=
      (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 o.2
    calc Valued.v (ϖ : Fv D.host.F v) ^ N * Valued.v (o : Fv D.host.F v)
        ≤ Valued.v (ϖ : Fv D.host.F v) ^ N * 1 := by gcongr
      _ = _ := mul_one _
  · intro h
    have hp : (ϖ : Fv D.host.F v) ^ N ≠ 0 := pow_ne_zero _ hϖ
    have hv : 0 < Valued.v ((ϖ : Fv D.host.F v) ^ N) := by
      rw [zero_lt_iff]; exact (map_ne_zero _).2 hp
    have hmem : x / (ϖ : Fv D.host.F v) ^ N ∈ v.adicCompletionIntegers D.host.F := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_div₀, div_le_one₀ hv, map_pow]
      exact h
    refine ⟨⟨_, hmem⟩, ?_⟩
    rw [algebraMap_OI, Subring.coe_mul, SubmonoidClass.coe_pow]
    show x = (ϖ : Fv D.host.F v) ^ N * (x / (ϖ : Fv D.host.F v) ^ N)
    rw [mul_div_cancel₀ _ hp]

theorem adjCo_smul {v : FinPl D} (φ : SplitProj D v) (S T : HSp D) (BS : GL (Fin S.rank) (Fv D.host.F v))
    (BT : GL (Fin T.rank) (Fv D.host.F v)) (s : AE D) (z : WO S T) :
    adjCo φ S T BS BT (cA D s • z) = GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdA φ s • adjCo φ S T BS BT z := by
  have h1 : ((cA D s • z : WO S T) : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (cA D) =
      s • (z : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (cA D) := by
    ext i j
    simp [GlobalTheory.DualPairCheck.cA_cA]
  have h2 : ∀ (M : Matrix (Fin S.rank) (Fin T.rank) (AE D)),
      (s • M).map (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdA φ) = GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdA φ s • M.map (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdA φ) := by
    intro M; ext i j; simp
  unfold adjCo
  rw [h1, Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul, h2, Matrix.mul_smul, Matrix.smul_mul]

end GlobalTheory.DownLift.GenSplit.DualSep

namespace GlobalTheory.DownLift.GenSplit


open DualSep in
theorem exists_sep_char : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (Formalism.IndefR.Lev.EAf D)) (βT : GL (Fin T.rank) (Formalism.IndefR.Lev.EAf D)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (v : FinPl D) (φ : SplitProj D v) (e : Formalism.L2.Theta.AE D), IsIdemOf φ e → ∀ (ϖ : OI v), Irreducible ϖ → ∀ (N : ℕ) (x : WO S T), IsHalf (cA D e) x → ¬ InPow ϖ N (adjCo φ S T (frCo φ βS) (frCo φ βT) x) → ∃ y, IsHalf e y ∧ (∀ z ∈ halfPow φ S T (frCo φ βS) (frCo φ βT) e ϖ N, ψ (symplO S T z y) = 1) ∧ ψ (symplO S T x y) ≠ 1 := by
  intro D ψ hψ S T ΛS ΛT βS βT hS hT hfS hfT v φ e he ϖ hϖ N x hx hxN
  obtain ⟨a, -, ha0, -, himg⟩ := (GlobalTheory.SplitLatticeHalves.splitLattice D S T ΛS ΛT βS βT hS hT hfS hfT v φ e he).2
  have hα : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdQ φ (star a) ≠ 0 := by
    rw [← GlobalTheory.SplitProjChart.emb_apply]
    exact (map_ne_zero _).2 (star_ne_zero.2 ha0)
  have hϖ0 : (ϖ : Fv D.host.F v) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  have hp : (ϖ : Fv D.host.F v) ^ N ≠ 0 := pow_ne_zero _ hϖ0
  set c : Fv D.host.F v := GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdQ φ (star a) / (ϖ : Fv D.host.F v) ^ N with hcdef
  have hc : c ≠ 0 := div_ne_zero hα hp
  obtain ⟨s, hs⟩ := (GlobalTheory.SplitProjChart.chart_rdA D v φ e he).1.1 c
  have hcoef : ∀ z : WO S T, adjCo φ S T (frCo φ βS) (frCo φ βT) (cA D s • z) =
      c • adjCo φ S T (frCo φ βS) (frCo φ βT) z := fun z => by rw [adjCo_smul, hs]
  have hval : ∀ m : Fv D.host.F v, Valued.v (c * m) ≤ Valued.v (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdQ φ (star a)) ↔
      Valued.v m ≤ Valued.v (ϖ : Fv D.host.F v) ^ N := by
    intro m
    have e1 : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdQ φ (star a) = c * (ϖ : Fv D.host.F v) ^ N := by
      rw [hcdef, div_mul_cancel₀ _ hp]
    rw [e1, map_mul, map_mul, map_pow, mul_le_mul_iff_right₀ (zero_lt_iff.2 ((map_ne_zero _).2 hc))]
  have hinPow : ∀ z : WO S T, InPow ϖ N (adjCo φ S T (frCo φ βS) (frCo φ βT) z) ↔
      ∀ i j, Valued.v ((c • adjCo φ S T (frCo φ βS) (frCo φ βT) z) i j) ≤
        Valued.v (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdQ φ (star a)) := by
    intro z
    unfold InPow
    simp only [Matrix.smul_apply, smul_eq_mul, hval, mem_pow_iff ϖ hϖ0 N]
  have hhalf : ∀ z : WO S T, IsHalf (cA D e) z → IsHalf (cA D e) (cA D s • z) := by
    intro z hz
    rw [GlobalTheory.SplitScalar.isHalf_iff] at *
    rw [smul_comm, hz]
  have hcoord := (GlobalTheory.PlaceTensor.adjCo_isCoord D S T ΛS ΛT hS hT v φ e he (frCo φ βS) (frCo φ βT)).1
  have hmem : ∀ z : WO S T, IsHalf (cA D e) z → InPow ϖ N (adjCo φ S T (frCo φ βS) (frCo φ βT) z) →
      cA D s • z ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) := by
    intro z hz hzN
    have h1 : adjCo φ S T (frCo φ βS) (frCo φ βT) (cA D s • z) ∈ adjCo φ S T (frCo φ βS) (frCo φ βT) ''
        {t | t ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) ∧
          IsHalf (cA D e) t} := by
      rw [himg, hcoef]
      exact (hinPow z).1 hzN
    obtain ⟨t, ⟨htΛ, htH⟩, hteq⟩ := h1
    have h2 : t = cA D s • z := hcoord.2.1.injOn htH (hhalf z hz) hteq
    rw [← h2]
    exact htΛ
  have hnot : cA D s • x ∉
      latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) := by
    intro hmx
    apply hxN
    rw [hinPow]
    have h1 : adjCo φ S T (frCo φ βS) (frCo φ βT) (cA D s • x) ∈
        {y : Matrix (Fin S.rank) (Fin T.rank) (Fv D.host.F v) | ∀ i j, Valued.v (y i j) ≤
          Valued.v (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdQ φ (star a))} := by
      rw [← himg]
      exact ⟨_, ⟨hmx, hhalf x hx⟩, rfl⟩
    rw [hcoef] at h1
    exact h1
  have hsd := (GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T ΛS ΛT hψ hS hT).1
  have hse := GlobalTheory.SplitScalar.isSplitIdem_conj he.1
  obtain ⟨l, hlΛ, hlH, hne⟩ := GlobalTheory.SplitScalar.exists_dual_half hse hsd
    (fun u hu => by rw [GlobalTheory.DualPairCheck.cA_cA]; exact GlobalTheory.SplitScalar.idem_smul_mem he.1.1 u hu) (hhalf x hx) hnot
  rw [GlobalTheory.DualPairCheck.cA_cA] at hlH
  refine ⟨s • l, ?_, fun z hz => ?_, ?_⟩
  · rw [GlobalTheory.SplitScalar.isHalf_iff] at *
    rw [smul_comm, hlH]
  · obtain ⟨hz1, hz2⟩ := hz
    have h1 := (hsd _ (GlobalTheory.SplitScalar.half_fin hse (hhalf z hz1))).1 (hmem z hz1 hz2) l hlΛ
    rwa [GlobalTheory.SplitScalar.symplO_smul, GlobalTheory.DualPairCheck.cA_cA] at h1
  · have h1 := GlobalTheory.SplitScalar.psi_skew_ne hne
    rwa [GlobalTheory.SplitScalar.symplO_smul, GlobalTheory.DualPairCheck.cA_cA] at h1

end GlobalTheory.DownLift.GenSplit

end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.BasicNotions Formalism.MainNotions.N GlobalTheory.DefiniteBC GlobalTheory.RecT

namespace GlobalTheory.DefiniteBCGood

section Local

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.SmGL GlobalTheory.LocGL

variable {E : Type} [Field E] [NumberField E]

theorem good_of_isSpehQuot {a d N : ℕ} (h : ∑ _ : Fin d, a = N) {w : HeightOneSpectrum (𝓞 E)} (σ : LocIrr w a)
    (σ' : LocIrr w N) (hd : 1 ≤ d) (hq : IsSpehQuot h σ σ') (hG : Good (GlobalTheory.BCSupport.clsOf σ')) :
    Good (GlobalTheory.BCSupport.clsOf σ) := by
  obtain ⟨q, hq⟩ := hq
  let x := IrrGL.of σ.ρ σ.smooth σ.irred
  let T : ∀ i : Fin d, (_root_.GlobalTheory.SmGL.twist σ.ρ (detChar (Fin a) (absPow (w.adicCompletion E) (((d : ℂ) - 1) / 2 - (i : ℕ))))).Equiv
      (spehFactor x d i).rep := fun i =>
    (twistEquiv (IrrGL.equivOf σ.ρ σ.smooth σ.irred) _).trans (x.twEquiv _ (isSmoothChar_absPow _))
  let M := multiProdEquiv (stdBlocks (fun _ : Fin d => a) h) T
  have hA : IsSubquotient (GlobalTheory.BCSupport.clsOf σ').rep σ'.ρ :=
    IsSubquotient.of_surjective (IrrGL.equivOf σ'.ρ σ'.smooth σ'.irred).toIntertwiningMap
      (IrrGL.equivOf σ'.ρ σ'.smooth σ'.irred).toLinearEquiv.surjective
  have hB : IsSubquotient σ'.ρ (spehInd h σ) := IsSubquotient.of_surjective q hq
  have hC : IsSubquotient (spehInd h σ) (prodIrr (spehFactor x d) h) :=
    IsSubquotient.of_surjective M.symm.toIntertwiningMap M.symm.toLinearEquiv.surjective
  have hs : IsSubquotient (GlobalTheory.BCSupport.clsOf σ').rep (prodIrr (spehFactor x d) h) := hA.trans (hB.trans hC)
  have h0 := (good_toral_of_isSubquotient_prodIrr _ d (spehFactor x d) (GlobalTheory.BCSupport.clsOf σ') h hs).1 hG ⟨0, hd⟩
  exact (good_nu_iff x _).1 h0

end Local

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂}

attribute [local instance] host_isCMField

section Statements

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {A : NAut N}

def GoodSplitU {n : ℕ} (U : Submodule ℂ (UA H.E n → ℂ)) : Prop :=
  ∀ w : PlE H, IsSplitPl H w → ∀ σ : LocIrr w n,
    IsCompAlong U (locU n w) ((cLoc w).comp (locU n w).subtype) σ.ρ → Good (GlobalTheory.BCSupport.clsOf σ)

end Statements

section Proof

variable {A : NAut N}

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

end Proof

section Frozen

open Formalism.MainNotions

end Frozen

section LawsCore

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands Formalism.ConjugateSelfDual ReciprocityTheory.Gal

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {ar : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h ar} {rc : IrrGL (k := w.adicCompletion E) → WD h}

end LawsCore

section LawsSpeh

open GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.NuShift

end LawsSpeh

section SatCore

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands Formalism.ConjugateSelfDual ReciprocityTheory.Gal

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {ar : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h ar} {rc : IrrGL (k := w.adicCompletion E) → WD h}

end SatCore

section RecordLaws

open GlobalTheory.LocGL GlobalTheory.WeilDeligne Formalism.ConjugateSelfDual ReciprocityTheory.Gal

variable {A : NAut N} (T : GlobalTheory.RowTie.WDTie N A)
  {rec : ∀ w : PlE H, IrrGL (k := w.adicCompletion H.E) → WD (E := H.E) (A := N.plOm.1 w) (w := w) (N.plOm.2 w)}

open GlobalTheory.RecLaws GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands Formalism.ConjugateSelfDual ReciprocityTheory.Gal

end RecordLaws

section Top

open GlobalTheory.LocGL GlobalTheory.WeilDeligne Formalism.ConjugateSelfDual ReciprocityTheory.Gal

end Top

section RecordLawsFam

open GlobalTheory.LocGL GlobalTheory.WeilDeligne Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.SmGL GlobalTheory.LocLanglands GlobalTheory.RecLaws

variable {A : NAut N} (T : GlobalTheory.RowTie.WDTie N A) {rc : GlobalTheory.RecT.RecFam}

end RecordLawsFam

end GlobalTheory.DefiniteBCGood

end
end
