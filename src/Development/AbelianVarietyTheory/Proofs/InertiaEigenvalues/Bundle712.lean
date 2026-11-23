module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RingHomExtDense
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle626
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle680
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFixedIff
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle162
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle021
public import Development.AbelianVarietyTheory.Definitions.Foundations.EqPlaceIdemOfIsPrimeIdem
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtA
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle010
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle695
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle499
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle521
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle498
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle607
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle687
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle696
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitAtOfIsSplitPl
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle020
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle511

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism GlobalTheory.CrysEval
open scoped Formalism.Per


theorem _root_.GlobalTheory.T.exists_polynomial_approx_dividedTwoVariableSet : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ F ∈ PPSet t K e, ∀ r : ℕ, ∃ (n : ℕ) (b : Bp l a) (p h : ZMod a → K⟦X⟧⟦X⟧), n ≠ 0 ∧ p ∈ PPSet t K e ∧ h ∈ PPSet t K e ∧ (n : ZMod a → K⟦X⟧⟦X⟧) * p = iotaP K t b ∧ F = p + (l : ZMod a → K⟦X⟧⟦X⟧) ^ r * h := by
  first | exact @GlobalTheory.CrysEval.exists_poly_approx_PPSet | exact GlobalTheory.CrysEval.exists_poly_approx_PPSet | (intros; apply GlobalTheory.CrysEval.exists_poly_approx_PPSet <;> assumption)
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.CuspRep GlobalTheory.DefiniteBC

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RecLaws

section Core

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {rc : IrrGL (k := w.adicCompletion E) → WD h}

abbrev clsOf {n : ℕ} (σ : SmIrr (GL (Fin n) (w.adicCompletion E))) : IrrGL (k := w.adicCompletion E) :=
  cls (ParLaws.toRep σ)

end Core

end GlobalTheory.RecLaws

namespace GlobalTheory.RecLaws

section Core2

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {rc : IrrGL (k := w.adicCompletion E) → WD h}

theorem rec_hasSatGL (H : IsRec h rc) {n : ℕ} (σ : SmIrr (GL (Fin n) (w.adicCompletion E))) (S : Multiset ℂˣ)
    (hS : GlobalTheory.LFun.HasSatGL w σ.ρ S) :
    (rc (clsOf σ)).unr ∧ (rc (clsOf σ)).frobEig = S.map fun z => ((z⁻¹ : ℂˣ) : ℂ) := by
  have hsph : IsSpherical (ParLaws.toRep σ).ρ := by
    have := hS.1
    unfold IsSpherical IsSphericalFor
    rw [GlobalTheory.SmGL.SphCompletion.KO_completion w n]
    exact this
  have hu : (rc (clsOf σ)).unr := (ParLaws.unr_iff H _).2 hsph
  obtain ⟨α, hα⟩ := ParLaws.exists_hasSatake_of_unr H hu
  have e : S = Finset.univ.val.map α := hS.unique (GlobalTheory.T.hasSatakeGL_of_hasSatakeParameters_principalSeries E w n _ σ.ρ α hα)
  refine ⟨hu, ?_⟩
  rw [clsOf, ParLaws.rec_eq_diag H hα, WD.frobEig_diag, e, Multiset.map_map]
  rfl

end Core2

end GlobalTheory.RecLaws
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.RawLift

theorem suppF_finIdem_mem_range : ∀ (D : D7) (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (f : AE D), IsFinIdem D v f → ∀ k : GA D V, SuppF V f k → ∃ a : GlobalTheory.FinZeta.Gv V v, GlobalTheory.FinZeta.embV V v a = k := by
  intro D V v f hf k hk
  obtain ⟨ε, hε, rfl⟩ := hf
  obtain ⟨a, ha⟩ := (GlobalTheory.AdelicU.Supp.suppF_iff_mem_range V hε k).1 hk
  exact ⟨a, ha⟩

end GlobalTheory.RawLift

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open GlobalTheory.BadPlace
open Classical

noncomputable section

namespace GlobalTheory.SplitStabFrame

open GlobalTheory.StdFrames GlobalTheory.IdemSupport GlobalTheory.IndefiniteRowSideFullHecke.ChainMatrices

variable {D : D7}



theorem cpt_sg_mem {Q : Pl D.host.E} {z : Ef D}
    (hz : cpt Q z ∈ HeightOneSpectrum.adicCompletionIntegers D.host.E Q) :
    cpt (cP Q) (sg D z) ∈ HeightOneSpectrum.adicCompletionIntegers D.host.E (cP Q) := by
  obtain ⟨e, -, -, h1, h0⟩ := exists_idem (D := D) {Q}
  have hQ1 : cpt Q e = 1 := h1 Q (Set.mem_singleton Q)
  have hez : e * z ∈ OA D := by
    refine (mem_OA_iff _).2 fun R => ?_
    rw [map_mul]
    by_cases hR : R = Q
    · rw [hR, hQ1, one_mul]; exact hz
    · rw [h0 R (Set.notMem_singleton_iff.2 hR), zero_mul]; exact zero_mem _
  have h2 : cpt (cP Q) (sg D (e * z)) ∈ HeightOneSpectrum.adicCompletionIntegers D.host.E (cP Q) :=
    (mem_OA_iff (sg D (e * z))).1 (GlobalTheory.LevSplit.sigR_int hez) (cP Q)
  have h3 : cpt (cP Q) (sg D (1 - e)) = 0 :=
    cpt_sg_eq_zero (by rw [cP_cP, map_sub, map_one, hQ1, sub_self])
  have h4 : cpt (cP Q) (sg D e) = 1 := by
    rw [map_sub, map_one, map_sub, map_one, sub_eq_zero] at h3
    exact h3.symm
  rw [map_mul, map_mul, h4, one_mul] at h2
  exact h2

theorem int_mul {Q : Pl D.host.E} {n : ℕ} {A B : Matrix (Fin n) (Fin n) (Ef D)}
    (hA : ∀ i j, cpt Q (A i j) ∈ HeightOneSpectrum.adicCompletionIntegers D.host.E Q)
    (hB : ∀ i j, cpt Q (B i j) ∈ HeightOneSpectrum.adicCompletionIntegers D.host.E Q) :
    ∀ i j, cpt Q ((A * B) i j) ∈ HeightOneSpectrum.adicCompletionIntegers D.host.E Q := by
  intro i j

  rw [Matrix.mul_apply, map_sum]
  exact sum_mem fun l _ => by rw [map_mul]; exact mul_mem (hA i l) (hB l j)

theorem int_of_OA {Q : Pl D.host.E} {n : ℕ} {A : Matrix (Fin n) (Fin n) (Ef D)} (h : ∀ i j, A i j ∈ OA D) :
    ∀ i j, cpt Q (A i j) ∈ HeightOneSpectrum.adicCompletionIntegers D.host.E Q :=
  fun i j => (mem_OA_iff _).1 (h i j) Q

theorem int_cT {Q : Pl D.host.E} {n : ℕ} {A : Matrix (Fin n) (Fin n) (Ef D)}
    (h : ∀ i j, cpt Q (A i j) ∈ HeightOneSpectrum.adicCompletionIntegers D.host.E Q) :
    ∀ i j, cpt (cP Q) (Formalism.UG.cT (sg D) A i j) ∈ HeightOneSpectrum.adicCompletionIntegers D.host.E (cP Q) :=
  fun i j => cpt_sg_mem (h j i)

theorem inv_eq_of_unitary {n : ℕ} {J U' : Matrix (Fin n) (Fin n) (Ef D)} (hU : U' * J = 1) (Y : GL (Fin n) (Ef D))
    (hY : Formalism.UG.cT (sg D) Y.val * J * Y.val = J) : (Y⁻¹).val = U' * Formalism.UG.cT (sg D) Y.val * J := by
  have h1 : U' * (Formalism.UG.cT (sg D) Y.val * J * Y.val) = 1 := by rw [hY, hU]
  calc (Y⁻¹).val = (U' * (Formalism.UG.cT (sg D) Y.val * J * Y.val)) * (Y⁻¹).val := by rw [h1, Matrix.one_mul]
    _ = U' * Formalism.UG.cT (sg D) Y.val * J * (Y.val * (Y⁻¹).val) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [Units.mul_inv, Matrix.mul_one]

theorem unitary_inv {n : ℕ} {J : Matrix (Fin n) (Fin n) (Ef D)} (Y : GL (Fin n) (Ef D))
    (hY : Formalism.UG.cT (sg D) Y.val * J * Y.val = J) :
    Formalism.UG.cT (sg D) (Y⁻¹).val * J * (Y⁻¹).val = J := by
  calc Formalism.UG.cT (sg D) (Y⁻¹).val * J * (Y⁻¹).val
        = Formalism.UG.cT (sg D) (Y⁻¹).val * (Formalism.UG.cT (sg D) Y.val * J * Y.val) * (Y⁻¹).val := by rw [hY]
    _ = Formalism.UG.cT (sg D) (Y.val * (Y⁻¹).val) * J * (Y.val * (Y⁻¹).val) := by
        rw [cT_mul']; simp only [Matrix.mul_assoc]
    _ = J := by rw [Units.mul_inv, cT_one', Matrix.one_mul, Matrix.mul_one]

theorem inv_int_at {Q : Pl D.host.E} {n : ℕ} (X : GL (Fin n) (Ef D))
    (hint : ∀ i j, cpt Q (X.val i j) ∈ HeightOneSpectrum.adicCompletionIntegers D.host.E Q)
    (hdet : Valued.v (cpt Q X.val.det) = 1) :
    ∀ i j, cpt Q ((X⁻¹).val i j) ∈ HeightOneSpectrum.adicCompletionIntegers D.host.E Q := by
  set A := (cpt Q).mapMatrix X.val with hAdef
  have hBA : (cpt Q).mapMatrix (X⁻¹).val * A = 1 := by rw [hAdef, ← map_mul, Units.inv_mul, map_one]
  have hB : (cpt Q).mapMatrix (X⁻¹).val = A⁻¹ := (Matrix.inv_eq_left_inv hBA).symm
  let A' : Matrix (Fin n) (Fin n) (HeightOneSpectrum.adicCompletionIntegers D.host.E Q) :=
    fun i j => ⟨A i j, hint i j⟩
  have hA' : (HeightOneSpectrum.adicCompletionIntegers D.host.E Q).subtype.mapMatrix A' = A := rfl
  have hdetA : A.det = cpt Q X.val.det := (RingHom.map_det _ _).symm
  intro i j
  have e : cpt Q ((X⁻¹).val i j) = ((cpt Q).mapMatrix (X⁻¹).val) i j := rfl
  rw [e, hB, Matrix.inv_def, Matrix.smul_apply, smul_eq_mul]
  refine mul_mem ?_ ?_
  · rw [hdetA, Ring.inverse_eq_inv', HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hdet, inv_one]
  · rw [← hA', ← RingHom.map_adjugate]
    exact (A'.adjugate i j).2

theorem int_of_split {n : ℕ} (J U' : Matrix (Fin n) (Fin n) (Ef D)) (hJ : ∀ i j, J i j ∈ OA D)
    (hU' : ∀ i j, U' i j ∈ OA D) (hUJ : U' * J = 1) (X : GL (Fin n) (Ef D))
    (hX : Formalism.UG.cT (sg D) X.val * J * X.val = J) (P : Pl D.host.E)
    (hint : ∀ i j, cpt P (X.val i j) ∈ HeightOneSpectrum.adicCompletionIntegers D.host.E P)
    (hdet : Valued.v (cpt P X.val.det) = 1)
    (hoff : ∀ Q, Q ≠ P → Q ≠ cP P → (cpt Q).mapMatrix X.val = 1) :
    (∀ i j, X.val i j ∈ OA D) ∧ ∀ i j, (X⁻¹).val i j ∈ OA D := by
  have hXi := unitary_inv X hX
  have intPi := inv_int_at X hint hdet
  have key : ∀ Y : GL (Fin n) (Ef D), Formalism.UG.cT (sg D) Y.val * J * Y.val = J →
      (∀ i j, cpt P (Y.val i j) ∈ HeightOneSpectrum.adicCompletionIntegers D.host.E P) →
      ∀ i j, cpt (cP P) ((Y⁻¹).val i j) ∈ HeightOneSpectrum.adicCompletionIntegers D.host.E (cP P) := by
    intro Y hY hYP
    rw [inv_eq_of_unitary hUJ Y hY]
    exact int_mul (int_mul (int_of_OA hU') (int_cT hYP)) (int_of_OA hJ)
  have hall : ∀ Q : Pl D.host.E,
      (∀ i j, cpt Q (X.val i j) ∈ HeightOneSpectrum.adicCompletionIntegers D.host.E Q) ∧
        ∀ i j, cpt Q ((X⁻¹).val i j) ∈ HeightOneSpectrum.adicCompletionIntegers D.host.E Q := by
    intro Q
    by_cases h1 : Q = P
    · rw [h1]; exact ⟨hint, intPi⟩
    by_cases h2 : Q = cP P
    · rw [h2]
      refine ⟨?_, key X hX hint⟩
      have := key X⁻¹ hXi intPi
      rwa [inv_inv] at this
    · have h3 := hoff Q h1 h2
      have h4 : (cpt Q).mapMatrix (X⁻¹).val = 1 :=
        calc (cpt Q).mapMatrix (X⁻¹).val = (cpt Q).mapMatrix (X⁻¹).val * (cpt Q).mapMatrix X.val := by
              rw [h3, Matrix.mul_one]
          _ = 1 := by rw [← map_mul, Units.inv_mul, map_one]
      have one_int : ∀ i j, (1 : Matrix (Fin n) (Fin n) (Q.adicCompletion D.host.E)) i j ∈
          HeightOneSpectrum.adicCompletionIntegers D.host.E Q := by
        intro i j
        rw [Matrix.one_apply]
        split_ifs
        · exact one_mem _
        · exact zero_mem _
      refine ⟨fun i j => ?_, fun i j => ?_⟩
      · have : cpt Q (X.val i j) = (1 : Matrix (Fin n) (Fin n) _) i j := congrFun (congrFun h3 i) j
        rw [this]; exact one_int i j
      · have : cpt Q ((X⁻¹).val i j) = (1 : Matrix (Fin n) (Fin n) _) i j := congrFun (congrFun h4 i) j
        rw [this]; exact one_int i j
  exact ⟨fun i j => (mem_OA_iff _).2 fun Q => (hall Q).1 i j,
    fun i j => (mem_OA_iff _).2 fun Q => (hall Q).2 i j⟩



theorem finE_mem_St_of_split : ∀ (D : D7) (W : HSp D) (β : GL (Fin W.rank) (Formalism.IndefR.Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)), IsSDFrame W β Λ 1 → ∀ (e f : AE D) (P : Pl D.host.E), Formalism.L2.NTheta.IsIdemAt e P → f = e + cA D e → GlobalTheory.IdemSupport.cP P ≠ P → ∀ k : GA D W, SuppF W f k → (∀ a b, GlobalTheory.StdFrames.cpt P ((HMul.hMul (HMul.hMul ((β)⁻¹).val ((Formalism.L2.Theta.mt W k).map (toEAf D))) (β).val : Matrix (Fin (W).rank) (Fin (W).rank) (Formalism.IndefR.Datum.EAf D)) a b) ∈ P.adicCompletionIntegers D.host.E) → Valued.v (GlobalTheory.StdFrames.cpt P ((HMul.hMul (HMul.hMul ((β)⁻¹).val ((Formalism.L2.Theta.mt W k).map (toEAf D))) (β).val : Matrix (Fin (W).rank) (Fin (W).rank) (Formalism.IndefR.Datum.EAf D))).det) = 1 → finE W k ∈ St β := by
  intro D W β Λ hSD e f P hP hf _ k hS hint hdet
  obtain ⟨hJ, U', hU', hUJ⟩ := unimod_of_isSD hSD
  have hg : Formalism.UG.cT (sg D) (finE W k).val * ratM W.gram * (finE W k).val = ratM W.gram :=
    GlobalTheory.LevSplit.finE_mem_UA W k
  set g := finE W k with hgdef
  let X : GL (Fin W.rank) (Ef D) := β⁻¹ * g * β
  have hXv : X.val = (β⁻¹).val * g.val * β.val := rfl
  have hX : Formalism.UG.cT (sg D) X.val * gramOf W β * X.val = gramOf W β := by
    have e2 : Formalism.UG.cT (sg D) (β⁻¹).val * Formalism.UG.cT (sg D) β.val = 1 := by
      rw [← cT_mul', Units.mul_inv, cT_one']
    have e3 : β.val * (β⁻¹).val = 1 := Units.mul_inv β
    show Formalism.UG.cT (sg D) X.val * (Formalism.UG.cT (sg D) β.val * ratM W.gram * β.val) * X.val =
      Formalism.UG.cT (sg D) β.val * ratM W.gram * β.val
    rw [hXv, cT_mul', cT_mul']
    calc Formalism.UG.cT (sg D) β.val * (Formalism.UG.cT (sg D) g.val * Formalism.UG.cT (sg D) (β⁻¹).val) *
          (Formalism.UG.cT (sg D) β.val * ratM W.gram * β.val) * ((β⁻¹).val * g.val * β.val)
        = Formalism.UG.cT (sg D) β.val * Formalism.UG.cT (sg D) g.val *
          (Formalism.UG.cT (sg D) (β⁻¹).val * Formalism.UG.cT (sg D) β.val) * ratM W.gram * (β.val * (β⁻¹).val) *
          g.val * β.val := by simp only [Matrix.mul_assoc]
      _ = Formalism.UG.cT (sg D) β.val * (Formalism.UG.cT (sg D) g.val * ratM W.gram * g.val) * β.val := by
          rw [e2, e3]; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = _ := by rw [hg]
  have hf0 : ∀ Q, Q ≠ P → Q ≠ cP P → cpt Q (toEAf D f) = 0 := by
    intro Q h1 h2
    have h3 : cP Q ≠ P := fun h => h2 (by rw [← h, cP_cP])
    rw [hf, RingHom.map_add (toEAf D), toEAf_cA, RingHom.map_add (cpt Q), (cpt_of_isIdemAt hP).2 Q h1,
      cpt_sg_eq_zero ((cpt_of_isIdemAt hP).2 _ h3), add_zero]
  have hM : ∀ Q, Q ≠ P → Q ≠ cP P → (cpt Q).mapMatrix g.val = 1 := by
    intro Q h1 h2
    refine Matrix.ext fun i j => ?_
    have h3 := congrArg (fun z => cpt Q (toEAf D z)) (hS i j)
    rw [RingHom.map_mul (toEAf D), RingHom.map_mul (cpt Q), hf0 Q h1 h2, zero_mul, Matrix.sub_apply,
      RingHom.map_sub (toEAf D), RingHom.map_sub (cpt Q)] at h3
    rw [eq_comm, sub_eq_zero] at h3
    change cpt Q (toEAf D (Formalism.L2.Theta.mt W k i j)) = (1 : Matrix (Fin W.rank) (Fin W.rank) _) i j
    rw [h3, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have hoff : ∀ Q, Q ≠ P → Q ≠ cP P → (cpt Q).mapMatrix X.val = 1 := by
    intro Q h1 h2
    rw [hXv, map_mul, map_mul, hM Q h1 h2, Matrix.mul_one, ← map_mul, Units.inv_mul, map_one]
  obtain ⟨h1, h2⟩ := int_of_split (gramOf W β) U' hJ hU' hUJ X hX P hint hdet hoff
  let Mi : Matrix (Fin W.rank) (Fin W.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E) := fun i j => ⟨_, h1 i j⟩
  let Mi' : Matrix (Fin W.rank) (Fin W.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E) := fun i j => ⟨_, h2 i j⟩
  have inj : Function.Injective ((Formalism.L2.Herm.intAf D.host.F D.host.E).subtype.mapMatrix (m := Fin W.rank)) := by
    intro A B h
    ext i j
    exact congrFun (congrFun h i) j
  have p1 : Mi * Mi' = 1 := inj (by rw [map_mul, map_one]; exact Units.mul_inv X)
  have p2 : Mi' * Mi = 1 := inj (by rw [map_mul, map_one]; exact Units.inv_mul X)
  refine ⟨⟨Mi, Mi', p1, p2⟩, ?_⟩
  have hX' : intGL D.host.F D.host.E W.rank ⟨Mi, Mi', p1, p2⟩ = X := Units.ext rfl
  show β * intGL D.host.F D.host.E W.rank ⟨Mi, Mi', p1, p2⟩ * β⁻¹ = g
  rw [hX']
  show β * (β⁻¹ * g * β) * β⁻¹ = g
  rw [mul_assoc, mul_assoc, mul_inv_cancel, mul_one, ← mul_assoc, mul_inv_cancel, one_mul]

end GlobalTheory.SplitStabFrame
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open GlobalTheory.BadPlace
open Classical

namespace GlobalTheory.IdemSumBranch

open GlobalTheory.StdFrames GlobalTheory.IdemSupport

variable {D : D7}

theorem cpt_idemSum {ea : AE D} {S : Finset (Pl D.host.E)} (h : IsIdemSum ea S) {Q : Pl D.host.E} (hQ : Q ∈ S) :
    cpt Q (toEAf D ea) = 1 := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := h
  have hs := map_sum ((cpt Q).comp (toEAf D)).toAddMonoidHom es S
  refine hs.trans ?_
  rw [Finset.sum_eq_single_of_mem Q hQ]
  · exact (cpt_of_isIdemAt (hes Q hQ)).1
  · intro R hR hne
    exact (cpt_of_isIdemAt (hes R hR)).2 Q hne.symm

theorem conjPrime_ne {ea : AE D} {S : Finset (Pl D.host.E)} (h : IsIdemSum ea S) {P Q : Pl D.host.E} (hP : P ∈ S)
    (hQ : Q ∈ S) : cP Q ≠ P := by
  intro hc
  have h1 := congrArg (fun t => cpt P (toEAf D t)) h.2
  simp only [RingHom.map_mul, RingHom.map_zero, cpt_idemSum h hP, one_mul] at h1
  rw [toEAf_cA, ← hc] at h1
  have h2 := cpt_sg_eq_zero h1
  rw [sg_sg, cpt_idemSum h hQ] at h2
  exact one_ne_zero h2

theorem branch : ∀ (D : D7) (P : Pl D.host.E) (e f ea : AE D) (S : Finset (Pl D.host.E)),
    IsPrimeIdem P e f → IsIdemSum ea S → P ∈ S → Formalism.L2.NTheta.IsIdemAt e P ∧ f = e + cA D e ∧ cA D f = f ∧
      infPart D f = 0 ∧ ∀ PP ∈ S, GlobalTheory.IdemSupport.cP PP ≠ P := by
  intro D P e f ea S h1 hS hP
  obtain ⟨hd, ε, hε, hf⟩ := of_isPrimeIdem (comp_toAd D) h1
  have hinf : infPart D f = 0 := hf ▸ (place_comp (comp_toAd D) hε).1
  rcases h1 with ⟨h1, h2⟩ | ⟨rfl, -⟩
  · refine ⟨h1, h2, ?_, hinf, fun Q hQ => conjPrime_ne hS hP hQ⟩
    rw [h2, RingHom.map_add (f := _), Formalism.L2.Theta.cA_cA, add_comm]
  · exfalso
    have h2 := (place_comp (comp_toAd D) hε).2.1 (cP P) (under_cP P)
    rw [← hf, hd.2.2 _ (conjPrime_ne hS hP hP)] at h2
    exact zero_ne_one h2

end GlobalTheory.IdemSumBranch
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open GlobalTheory.BadPlace
open Classical

namespace GlobalTheory.FrameOff

theorem cpt_frame_sub_one_eq_zero_of_suppF : ∀ (D : D7) (W : HSp D) (β : GL (Fin W.rank) (Formalism.IndefR.Lev.EAf D)) (f : AE D) (k : GA D W) (PP : Pl D.host.E), SuppF W f k → GlobalTheory.StdFrames.cpt PP (toEAf D f) = 0 → ∀ a b, GlobalTheory.StdFrames.cpt PP (((HMul.hMul (HMul.hMul ((β)⁻¹).val ((Formalism.L2.Theta.mt W k).map (toEAf D))) (β).val : Matrix (Fin (W).rank) (Fin (W).rank) (Formalism.IndefR.Datum.EAf D)) - 1) a b) = 0 := by
  intro D W β f k PP hS hf a b
  set M := Formalism.L2.Theta.mt W k with hMdef
  have hmap : M.map (toEAf D) - 1 = (M - 1).map (toEAf D) := by
    rw [Matrix.map_sub (toEAf D) (fun x y => (toEAf D).map_sub x y),
      Matrix.map_one _ (toEAf D).map_zero (toEAf D).map_one]
  have hM : ((M - 1).map (toEAf D)).map (GlobalTheory.StdFrames.cpt PP) = 0 := by
    refine Matrix.ext fun i j => ?_
    change GlobalTheory.StdFrames.cpt PP (toEAf D ((M - 1) i j)) = 0
    rw [← hS i j, RingHom.map_mul, RingHom.map_mul, hf, zero_mul]
  have hk : (HMul.hMul (HMul.hMul ((β)⁻¹).val (M.map (toEAf D))) (β).val :
        Matrix (Fin (W).rank) (Fin (W).rank) (Formalism.IndefR.Datum.EAf D)) - 1
      = ((β)⁻¹).val * (M.map (toEAf D) - 1) * (β).val := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Units.inv_mul]
  rw [hk]
  change ((((β)⁻¹).val * (M.map (toEAf D) - 1) * (β).val).map (GlobalTheory.StdFrames.cpt PP)) a b = 0
  rw [Matrix.map_mul, Matrix.map_mul, hmap, hM, Matrix.mul_zero, Matrix.zero_mul]
  rfl

end GlobalTheory.FrameOff
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

theorem _root_.GlobalTheory.T.standard_module_properties : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k], GlobalTheory.Published.LanglandsMultisegments →
    ∀ (P : Segment k → Prop), (∀ 𝔫 : Multiset (Segment k), (∀ Δ ∈ 𝔫, P Δ) → ∃ y : IrrGL (k := k), IsL 𝔫 y.rep) →
    ∀ (h N : ℕ) (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N) (𝔪 : Fin h → Multiset (Segment k)),
      (∀ j, IsL (𝔪 j) (x j).rep) → (∀ j, ∀ Δ ∈ 𝔪 j, P Δ) →
      ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), π.IsIrreducible →
        Nonempty (π.Equiv (prodIrr x hd)) → IsL (∑ j, 𝔪 j) π := by
  first | exact @GlobalTheory.LocGL.IrrProdL.isL_sum_of_isIrreducible | exact GlobalTheory.LocGL.IrrProdL.isL_sum_of_isIrreducible | (intros; apply GlobalTheory.LocGL.IrrProdL.isL_sum_of_isIrreducible <;> assumption)
end

section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocLanglands

theorem isRec_of_isRecLit : DepthZeroCuspidalLL → DepthZeroInduction → LanglandsExhaustionGL → LanglandsMultisegments → StandardCosocleGL → ZelevinskyPolynomialRing → GeometricLemma → BernsteinZelevinskyFiniteness → ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (rc : IrrGL (k := w.adicCompletion E) → WD h), IsRecLit h rc → IsRec h rc := by
  intro hDZ hDI hEx hLM hSC hZP hGL hBZ E Ω _ _ _ _ _ A w h rc H
  obtain ⟨a, ha, ε, hε, L⟩ := H
  refine ⟨a, ha, ε, hε, ?_⟩
  exact
    { bij := L.bij, dim := L.dim, one := L.one, eps := L.eps, cusp := L.cusp, langlands := L.langlands,
      twist := L.twist, central := L.central, dual := L.dual,
      det := GlobalTheory.T.determinant_rec_compatible hSC E Ω A w h a ha _ rc L
      prod := GlobalTheory.T.twist_rec_compatible hEx hLM hSC E Ω A w h a ha _ rc L
      supp := GlobalTheory.T.central_character_rec_compatible hEx hZP hGL hBZ E Ω A w h a ha _ rc L
      sph := GlobalTheory.T.l_factor_rec_compatible hEx hLM hSC hZP hGL hBZ E Ω A w h a ha _ rc L
      sat := GlobalTheory.T.epsilon_factor_rec_compatible hEx hLM hSC hZP hGL hBZ E Ω A w h a ha _ rc L
      depth := GlobalTheory.T.conductor_rec_compatible hDZ hDI hEx hZP hGL hBZ E Ω A w h rc ⟨a, ha, ε, hε, L⟩ }

end GlobalTheory.LocLanglands
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

theorem _root_.GlobalTheory.T.crystalline_twist_crystallineCharacter_jumps_shift : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V) (V' : Type) [AddCommGroup V'] [Module ↥LL.1 V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] ↥LL.1 V'] [FiniteDimensional ↥LL.1 V'] (ρ' : Representation ↥LL.1 ↥(GK K) V') (χ : ↥(GK K) →* (↥LL.1)ˣ), IsTwistRep χ ρ ρ' → IsCrys (P.PD K) (charRep χ) → IsCrys (P.PD K) ρ → IsCrys (P.PD K) ρ' ∧ ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (a b : ℤ), IsJumpV (P.PD K) (charRep χ) τ b → multV (P.PD K) ρ' τ (a + b) = multV (P.PD K) ρ τ a := by
  first | exact @GlobalTheory.TwistRepCrys.isCrys_and_multV_twist | exact GlobalTheory.TwistRepCrys.isCrys_and_multV_twist | (intros; apply GlobalTheory.TwistRepCrys.isCrys_and_multV_twist <;> assumption)
end
