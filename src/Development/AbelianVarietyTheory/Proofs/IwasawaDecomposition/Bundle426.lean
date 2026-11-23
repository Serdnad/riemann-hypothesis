module

public import Formalism.LocalToGlobal.Columns.Bundle014
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ReferenceCharactersFactorTame
public import Formalism.LocalToGlobal.Columns.RecLevelLoc
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle406
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.LatticeBasisExistsHolds
public import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
public import Formalism.LocalToGlobal.Divisibility.QLocTied
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle411
public import Formalism.LocalToGlobal.GaloisLevelStructure.Bundle002
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.ExpDefs
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle183
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle065
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle018
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle023
public import Formalism.LocalToGlobal.IndefiniteReal.RecTie
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle412
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Henselian
import Mathlib.Order.Interval.Finset.Box
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentAndTwistData
import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.ConjugateSelfDual.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.Bundle001
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Mathlib.Algebra.MvPolynomial.Funext
import ReciprocityTheory.Automorphisms.PlaceA
import ReciprocityTheory.GaloisValuations.GlobalA
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle018
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.UG.P Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
open scoped TensorProduct

namespace GlobalTheory.Mem.Col2.Splice

theorem isPtOf_splice : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] (ST SG Q Q0 Q1 : Finset (HeightOneSpectrum (𝓞 E))) (v : HeightOneSpectrum (𝓞 F)) (g0 h : GL (Fin n) (TensorProduct F E (FiniteAdeleRing (𝓞 F) F))) (p0 : DecoF E n ST SG Q0) (p1 : DecoF E n ST SG Q1) (q : DecoF E n ST SG Q), GlobalTheory.Mem.Col2.IsPtOf hc g0 p0 → GlobalTheory.Mem.Col2.IsPtOf hc h p1 → (∀ P ∈ Q, ¬ IsOver v P) → (∀ w ∈ SG, ¬ IsOver v w) → Deco.SameOff ST SG v q.deco.1 p1.deco.1 → (∀ P : HeightOneSpectrum (𝓞 E), IsOver v P → localization₂ P.asIdeal q.deco.1.N = localization₂ P.asIdeal p0.deco.1.N) → (∀ P : ST, IsOver v P.1 → q.deco.1.f P = p0.deco.1.f P) → (∀ P : Q, ∃ P' : Q1, P'.1 = P.1 ∧ p1.fr P' = q.fr P) → GlobalTheory.Mem.Col2.IsPtOf hc (h * rll_put n v (bc (prV (E := E) v) (h⁻¹ * g0))) q := by
  intro F E _ _ _ _ _ _ hc n _ ST SG Q Q0 Q1 v g0 h p0 p1 q h0 h1 hQ hSG hoff hN hf hfr
  obtain ⟨⟨hg0, hd0⟩, -⟩ := (ChTwRead.isPtOf_iff hc g0 p0).1 h0
  obtain ⟨⟨hh, hd1⟩, hfr1⟩ := (ChTwRead.isPtOf_iff hc h p1).1 h1
  set m := h * rll_put n v (bc (prV (E := E) v) (h⁻¹ * g0)) with hm
  have hv : bc (prV (E := E) v) m = bc (prV (E := E) v) g0 := by
    rw [hm, map_mul, rll_put_self, ← map_mul, mul_inv_cancel_left]
  have hne : ∀ P : HeightOneSpectrum (𝓞 E), ¬ IsOver v P → P.under (𝓞 F) ≠ v := by
    rintro P hP rfl
    exact hP rfl
  have hw : ∀ P : HeightOneSpectrum (𝓞 E), ¬ IsOver v P →
      bc (prV (E := E) (P.under (𝓞 F))) m = bc (prV (E := E) (P.under (𝓞 F))) h := by
    intro P hP
    rw [hm, map_mul, rll_put_ne n v _ (hne P hP), mul_one]
  have hmU : m ∈ UAd hc n :=
    mul_mem hh (rll_put_mem_UAd hc n v (afsplit_bc_mem hc.sig 1 v _ (mul_mem (inv_mem hh) hg0)))
  refine (ChTwRead.isPtOf_iff hc m q).2 ⟨⟨hmU, ?_⟩, fun P i j => ?_⟩
  · ext1
    · refine Formalism.L2.DIV.eq_of_forall_localized_eq fun P => ?_
      by_cases hP : IsOver v P
      · rw [hN P hP, hd0]
        exact (updn_mem_loc hP hv).symm
      · rw [hoff.N P hP, hd1]
        exact (updn_mem_loc (v := P.under (𝓞 F)) rfl (hw P hP)).symm
    · funext P
      by_cases hP : IsOver v P.1
      · rw [hf P hP, hd0]
        exact (updn_f_loc ST SG P hP hv).symm
      · rw [hoff.f P hP, hd1]
        exact (updn_f_loc ST SG (v := P.1.under (𝓞 F)) P rfl (hw P.1 hP)).symm
    · funext w
      have hP := hSG w.1 w.2
      rw [hoff.be w hP, hd1]
      exact (updn_be_loc ST SG (v := w.1.under (𝓞 F)) w rfl (hw w.1 hP)).symm
  · obtain ⟨⟨P1, hP1⟩, hP', e⟩ := hfr P
    have hPv := hQ P.1 P.2
    simp only at hP'
    subst hP'
    rw [← e, ← hfr1 ⟨_, hP1⟩ i j]
    refine ChTwRead.adAt_congr_prV P.1 ?_
    have := congrArg (fun g : GL (Fin n) (E ⊗[F] (P.1.under (𝓞 F)).adicCompletion F) =>
      g.val i j) (hw P.1 hPv)
    exact this

end GlobalTheory.Mem.Col2.Splice
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CoeffSpace

theorem nontrivial_VV : ∀ (K : Type) [Field K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n), Nontrivial (Formalism.L2.DIV.VV K lam) := by
  intro K _ ι _ n lam
  have hanti : ∀ τ, Antitone (lam τ).natW := fun τ i j hij =>
    Int.toNat_le_toNat (by have := (lam τ).anti hij; omega)
  have hmem : (∏ τ, Formalism.GradedWeylDivisibility.blockEmb K τ (Formalism.BasicNotions.extremal K n (lam τ))) ∈ Formalism.L2.DIV.VV K lam :=
    Submodule.subset_span ⟨fun τ => Formalism.BasicNotions.extremal K n (lam τ),
      fun τ => Formalism.GradedWeylDivisibility.hwMem K n n le_rfl _ (hanti τ), rfl⟩
  refine ⟨⟨⟨_, hmem⟩, 0, fun h => ?_⟩⟩
  have h0 : (∏ τ, Formalism.GradedWeylDivisibility.blockEmb K τ (Formalism.BasicNotions.extremal K n (lam τ))) = 0 := congrArg Subtype.val h
  rw [Finset.prod_eq_zero_iff] at h0
  obtain ⟨τ, _, h⟩ := h0
  have hinj : Function.Injective (fun v : Fin n × Fin n => (τ, v)) := fun a b hab => (Prod.mk.inj hab).2
  exact Formalism.GradedWeylDivisibility.hwNe K n n le_rfl _ (MvPolynomial.rename_injective _ hinj (h.trans (map_zero _).symm))

end GlobalTheory.CoeffSpace
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.ActPolyCoeff

variable {K : Type} [Field K] {ι : Type} [Fintype ι] {n : ℕ}

def evPt (g : ι → GL (Fin n) K) : (ι ⊕ ι) × Fin n × Fin n → K := fun v =>
  Sum.elim (fun τ => ((g τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) v.2.1 v.2.2)
    (fun τ => (((g τ)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) v.2.2 v.2.1) v.1

def genSub (F : Formalism.L2.DIV.Pol K ι n) :
    MvPolynomial (ι × Fin n × Fin n) (MvPolynomial ((ι ⊕ ι) × Fin n × Fin n) K) :=
  MvPolynomial.eval₂ ((MvPolynomial.C).comp MvPolynomial.C)
    (fun v => ∑ b : Fin n, MvPolynomial.C (MvPolynomial.X (Sum.inl v.1, b, v.2.1)) * MvPolynomial.X (v.1, b, v.2.2)) F

theorem map_genSub (g : ι → GL (Fin n) K) (F : Formalism.L2.DIV.Pol K ι n) :
    MvPolynomial.map (MvPolynomial.eval (evPt g)) (genSub F) = Formalism.L2.DIV.trAct g F := by
  unfold genSub
  rw [MvPolynomial.eval₂_comp_left]
  simp only [Formalism.L2.DIV.trAct, Formalism.GradedWeylDivisibility.blockAct, MvPolynomial.aeval_def, MvPolynomial.algebraMap_eq]
  congr 1
  · ext k; simp
  · funext v; simp [evPt, Matrix.transpose_apply]

end GlobalTheory.ActPolyCoeff

noncomputable section
namespace GlobalTheory.ActPolyCoeff

variable {K : Type} [Field K] {ι : Type} [Fintype ι] {n : ℕ}

theorem lin_map_eval {σ V : Type} (x : V → K) (ψ : MvPolynomial σ K →ₗ[K] K) (p : MvPolynomial σ (MvPolynomial V K)) :
    ψ (MvPolynomial.map (MvPolynomial.eval x) p) =
      MvPolynomial.eval x (∑ m ∈ p.support, p.coeff m * MvPolynomial.C (ψ (MvPolynomial.monomial m 1))) := by
  conv_lhs => rw [p.as_sum]

  simp only [map_sum, MvPolynomial.map_monomial, MvPolynomial.eval_mul, MvPolynomial.eval_C]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← mul_one (MvPolynomial.eval x (p.coeff m)), ← smul_eq_mul, ← MvPolynomial.smul_monomial, map_smul, smul_eq_mul]
  simp

def detL (τ : ι) : MvPolynomial ((ι ⊕ ι) × Fin n × Fin n) K :=
  (Matrix.of fun a b : Fin n => MvPolynomial.X (Sum.inl τ, a, b)).det

def detR (τ : ι) : MvPolynomial ((ι ⊕ ι) × Fin n × Fin n) K :=
  (Matrix.of fun a b : Fin n => MvPolynomial.X (Sum.inr τ, b, a)).det

theorem eval_detL (g : ι → GL (Fin n) K) (τ : ι) :
    MvPolynomial.eval (evPt g) (detL τ) = ((g τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det := by
  unfold detL
  rw [RingHom.map_det]
  congr 1
  ext a b; simp [evPt]

theorem eval_detR (g : ι → GL (Fin n) K) (τ : ι) :
    MvPolynomial.eval (evPt g) (detR τ) = (((g τ)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det := by
  unfold detR
  rw [RingHom.map_det]
  congr 1
  ext a b; simp [evPt]

theorem detPow_eq (g : GL (Fin n) K) (e : ℤ) :
    Formalism.BasicNotions.detPow K n g e = if 0 ≤ e then ((g : Matrix (Fin n) (Fin n) K).det) ^ e.toNat
      else ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det ^ (-e).toNat := by
  unfold Formalism.BasicNotions.detPow
  split_ifs with h
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le h
    simp [zpow_natCast, Matrix.GeneralLinearGroup.val_det_apply]
  · have : e = -(((-e).toNat : ℕ) : ℤ) := by omega
    rw [this, zpow_neg, zpow_natCast, ← inv_pow, ← map_inv]
    simp only [Int.toNat_natCast, neg_neg, Units.val_pow_eq_pow_val, Matrix.GeneralLinearGroup.val_det_apply]

end GlobalTheory.ActPolyCoeff

noncomputable section
namespace GlobalTheory.ActPolyCoeff

def detTwPoly {K : Type} [Field K] {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) :
    MvPolynomial ((ι ⊕ ι) × Fin n × Fin n) K :=
  ∏ τ, if 0 ≤ (lam τ).detShift then detL τ ^ (lam τ).detShift.toNat else detR τ ^ (-(lam τ).detShift).toNat

theorem eval_detTwPoly {K : Type} [Field K] {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n)
    (g : ι → GL (Fin n) K) : MvPolynomial.eval (evPt g) (detTwPoly lam) = Formalism.L2.DIV.detTwK lam g := by
  unfold detTwPoly Formalism.L2.DIV.detTwK
  rw [map_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [detPow_eq]
  split_ifs <;> simp [eval_detL, eval_detR]

theorem polyAction_coeff_poly : ∀ (K : Type) [Field K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n) (F : Formalism.L2.DIV.Pol K ι n)
    (ψ : Formalism.L2.DIV.Pol K ι n →ₗ[K] K), ∃ P : MvPolynomial ((ι ⊕ ι) × Fin n × Fin n) K, ∀ g : ι → GL (Fin n) K,
    ψ (Formalism.L2.DIV.actP lam g F) = MvPolynomial.eval (fun v : (ι ⊕ ι) × Fin n × Fin n =>
      Sum.elim (fun τ => ((g τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) v.2.1 v.2.2)
        (fun τ => (((g τ)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) v.2.2 v.2.1) v.1) P := by
  intro K _ ι _ n lam F ψ
  refine ⟨detTwPoly lam * ∑ m ∈ (genSub F).support, (genSub F).coeff m * MvPolynomial.C (ψ (MvPolynomial.monomial m 1)), ?_⟩
  intro g
  rw [MvPolynomial.eval_mul, ← lin_map_eval]
  change ψ _ = MvPolynomial.eval (evPt g) (detTwPoly lam) * ψ (MvPolynomial.map (MvPolynomial.eval (evPt g)) (genSub F))
  rw [eval_detTwPoly, map_genSub]
  show ψ (Formalism.L2.DIV.detTwK lam g • Formalism.L2.DIV.trAct g F) = _
  rw [map_smul, smul_eq_mul]

end GlobalTheory.ActPolyCoeff
end
end
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

namespace GlobalTheory.SpecFactor

open MvPolynomial

variable {K : Type} [Field K] {ι : Type} [DecidableEq ι] {n : ℕ}

noncomputable def specAt (τ₀ : ι) (y : ι × Fin n × Fin n → K) :
    Formalism.L2.DIV.Pol K ι n →ₐ[K] MvPolynomial (Fin n × Fin n) K :=
  MvPolynomial.aeval fun v => if v.1 = τ₀ then MvPolynomial.X v.2 else MvPolynomial.C (y v)

theorem eval_specAt (τ₀ : ι) (y : ι × Fin n × Fin n → K) (z : Fin n × Fin n → K) (w : Formalism.L2.DIV.Pol K ι n) :
    MvPolynomial.eval z (specAt τ₀ y w) =
      MvPolynomial.eval (fun v => if v.1 = τ₀ then z v.2 else y v) w := by
  have h : (MvPolynomial.eval z).comp (specAt τ₀ y).toRingHom =
      MvPolynomial.eval (fun v : ι × Fin n × Fin n => if v.1 = τ₀ then z v.2 else y v) := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp [specAt]
    · intro v
      by_cases hv : v.1 = τ₀ <;> simp [specAt, hv]
  exact congrArg (fun f : Formalism.L2.DIV.Pol K ι n →+* K => f w) h

theorem exists_specAt_ne [Infinite K] (τ₀ : ι) (w : Formalism.L2.DIV.Pol K ι n) (hw : w ≠ 0) :
    ∃ y, specAt τ₀ y w ≠ 0 := by
  by_contra h
  push_neg at h
  apply hw
  apply MvPolynomial.funext
  intro z
  have := congrArg (MvPolynomial.eval (fun v : Fin n × Fin n => z (τ₀, v))) (h z)
  rw [eval_specAt, map_zero] at this
  rw [map_zero, ← this]
  congr 2
  funext v
  split_ifs with hv
  · obtain ⟨a, b⟩ := v; simp only at hv; subst hv; rfl
  · rfl

theorem specAt_blockEmb (τ₀ : ι) (y : ι × Fin n × Fin n → K) (τ : ι) (F : MvPolynomial (Fin n × Fin n) K) :
    specAt τ₀ y (Formalism.GradedWeylDivisibility.blockEmb K τ F) =
      if τ = τ₀ then F else MvPolynomial.C (MvPolynomial.eval (fun v => y (τ, v)) F) := by
  unfold specAt Formalism.GradedWeylDivisibility.blockEmb
  rw [MvPolynomial.aeval_rename]
  split_ifs with h
  · subst h
    simp only [Function.comp_def, if_true]
    exact MvPolynomial.aeval_X_left_apply F
  · simp only [Function.comp_def, h, if_false]
    have hh : (MvPolynomial.aeval (R := K) fun x : Fin n × Fin n => (MvPolynomial.C (y (τ, x)) : MvPolynomial (Fin n × Fin n) K)).toRingHom =
        MvPolynomial.C.comp (MvPolynomial.eval fun v => y (τ, v)) := by
      apply MvPolynomial.ringHom_ext
      · intro r; simp
      · intro v; simp
    exact congrArg (fun f : MvPolynomial (Fin n × Fin n) K →+* MvPolynomial (Fin n × Fin n) K => f F) hh

end GlobalTheory.SpecFactor

namespace GlobalTheory.SpecFactor

open MvPolynomial

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ}

theorem specAt_mem (lam : ι → DomWeight n) (τ₀ : ι) (y : ι × Fin n × Fin n → K) (P : Formalism.L2.DIV.Pol K ι n)
    (hP : P ∈ Formalism.L2.DIV.VV K lam) : specAt τ₀ y P ∈ nablaSq K n (lam τ₀) := by
  unfold Formalism.L2.DIV.VV Formalism.GradedWeylDivisibility.tensorLat at hP
  induction hP using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨F, hF, rfl⟩ := hx
    rw [map_prod]
    simp only [specAt_blockEmb]
    rw [Fintype.prod_eq_mul_prod_compl τ₀, if_pos rfl, mul_comm]
    have : ∏ i ∈ ({τ₀}ᶜ : Finset ι), (if i = τ₀ then F i else
        MvPolynomial.C (MvPolynomial.eval (fun v => y (i, v)) (F i))) =
        MvPolynomial.C (∏ i ∈ ({τ₀}ᶜ : Finset ι), MvPolynomial.eval (fun v => y (i, v)) (F i)) := by
      rw [map_prod]
      refine Finset.prod_congr rfl fun i hi => ?_
      rw [if_neg (by simpa using hi)]
    rw [this, ← MvPolynomial.smul_eq_C_mul]
    exact Submodule.smul_mem _ _ (hF τ₀)
  | zero => simp
  | add x z _ _ hx hz => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hz
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

theorem specAt_blockAct (τ₀ : ι) (y : ι × Fin n × Fin n → K) (M : Matrix (Fin n) (Fin n) K)
    (P : Formalism.L2.DIV.Pol K ι n) :
    specAt τ₀ y (Formalism.GradedWeylDivisibility.blockAct K (fun τ => if τ = τ₀ then M else 1) P) =
      Formalism.GradedWeylDivisibility.rowAct K M (specAt τ₀ y P) := by
  have h : (specAt τ₀ y).comp (Formalism.GradedWeylDivisibility.blockAct K (n := n) (fun τ => if τ = τ₀ then M else 1)) =
      (Formalism.GradedWeylDivisibility.rowAct K M).comp (specAt τ₀ y) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨τ, a, b⟩
    by_cases hτ : τ = τ₀
    · subst hτ
      simp [specAt, Formalism.GradedWeylDivisibility.blockAct, Formalism.GradedWeylDivisibility.rowAct]
    · set_option synthInstance.maxHeartbeats 100000 in
      simp only [AlgHom.comp_apply, Formalism.GradedWeylDivisibility.blockAct, specAt, MvPolynomial.aeval_X, hτ, if_false, map_sum, map_mul,
        MvPolynomial.aeval_C, Matrix.one_apply]
      rw [Finset.sum_eq_single a]
      · simp [hτ]
      · intro c _ hc; simp [Ne.symm hc]
      · simp
  exact congrArg (fun f : Formalism.L2.DIV.Pol K ι n →ₐ[K] MvPolynomial (Fin n × Fin n) K => f P) h

end GlobalTheory.SpecFactor

theorem GlobalTheory.specialise_factor : ∀ (K : Type) [Field K] [Infinite K] (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
    (lam : ι → DomWeight n) (τ₀ : ι) (w : Formalism.L2.DIV.Pol K ι n), w ∈ Formalism.L2.DIV.VV K lam → w ≠ 0 →
    ∃ φ : Formalism.L2.DIV.Pol K ι n →ₗ[K] MvPolynomial (Fin n × Fin n) K, φ w ≠ 0 ∧
      (∀ P ∈ Formalism.L2.DIV.VV K lam, φ P ∈ nablaSq K n (lam τ₀)) ∧
      ∀ (M : Matrix (Fin n) (Fin n) K) (P : Formalism.L2.DIV.Pol K ι n),
        φ (Formalism.GradedWeylDivisibility.blockAct K (fun τ => if τ = τ₀ then M else 1) P) = Formalism.GradedWeylDivisibility.rowAct K M (φ P) := by
  intro K _ _ n ι _ _ lam τ₀ w _ hw
  obtain ⟨y, hy⟩ := GlobalTheory.SpecFactor.exists_specAt_ne τ₀ w hw
  exact ⟨(GlobalTheory.SpecFactor.specAt τ₀ y).toLinearMap, hy,
    fun P hP => GlobalTheory.SpecFactor.specAt_mem lam τ₀ y P hP,
    fun M P => GlobalTheory.SpecFactor.specAt_blockAct τ₀ y M P⟩
end

section

open MeasureTheory Matrix NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DoubleCosetMeasures Formalism.L2.Host Formalism.L2.DIV Formalism.L2.DIV.QLoc GlobalTheory.Mem.HD

theorem _root_.GlobalTheory.T.blockUpperTriangular_GL_mul_det_inv : ∀ (F : Type) [Field F] (r c : ℕ) (p q : GL (Fin (r + c)) F), bDA (p : Matrix (Fin (r + c)) (Fin (r + c)) F) = 0 → bDA (q : Matrix (Fin (r + c)) (Fin (r + c)) F) = 0 → bDA ((p * q : GL (Fin (r + c)) F) : Matrix (Fin (r + c)) (Fin (r + c)) F) = 0 ∧ bAA ((p * q : GL (Fin (r + c)) F) : Matrix (Fin (r + c)) (Fin (r + c)) F) = bAA (p : Matrix (Fin (r + c)) (Fin (r + c)) F) * bAA (q : Matrix (Fin (r + c)) (Fin (r + c)) F) ∧ bDD ((p * q : GL (Fin (r + c)) F) : Matrix (Fin (r + c)) (Fin (r + c)) F) = bDD (p : Matrix (Fin (r + c)) (Fin (r + c)) F) * bDD (q : Matrix (Fin (r + c)) (Fin (r + c)) F) ∧ (p : Matrix (Fin (r + c)) (Fin (r + c)) F).det = (bAA (p : Matrix (Fin (r + c)) (Fin (r + c)) F)).det * (bDD (p : Matrix (Fin (r + c)) (Fin (r + c)) F)).det ∧ bDA ((p⁻¹ : GL (Fin (r + c)) F) : Matrix (Fin (r + c)) (Fin (r + c)) F) = 0 := by
  first | exact @GlobalTheory.HQStepBlocks.main | exact GlobalTheory.HQStepBlocks.main | (intros; apply GlobalTheory.HQStepBlocks.main <;> assumption)
end

section

open MeasureTheory Matrix NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DoubleCosetMeasures Formalism.L2.Host Formalism.L2.DIV Formalism.L2.DIV.QLoc GlobalTheory.Mem.HD

theorem _root_.GlobalTheory.T.isLocalAt_completionIntegers_chosenUniformiser : ∀ (L : Type) [Field L] [NumberField L] (P : HeightOneSpectrum (𝓞 L)), IsLocalAt (OP P) ((piP P : (P.adicCompletion L)ˣ) : P.adicCompletion L) := by
  first | exact @GlobalTheory.Mem.HD.isLocalAt_adicCompletionIntegers_uniformizer | exact GlobalTheory.Mem.HD.isLocalAt_adicCompletionIntegers_uniformizer | (intros; apply GlobalTheory.Mem.HD.isLocalAt_adicCompletionIntegers_uniformizer <;> assumption)
end

section

open MeasureTheory Matrix NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DoubleCosetMeasures Formalism.L2.Host Formalism.L2.DIV Formalism.L2.DIV.QLoc GlobalTheory.Mem.HD

theorem _root_.GlobalTheory.T.isOpen_isCompact_parahoric_GL_completion : ∀ (L : Type) [Field L] [NumberField L] (P : HeightOneSpectrum (𝓞 L)) (r c : ℕ), IsOpen (parJ (OP P) (piP P : P.adicCompletion L) r c) ∧ IsCompact (parJ (OP P) (piP P : P.adicCompletion L) r c) := by
  first | exact @GlobalTheory.ParahoricTopo.isOpen_isCompact_parJ | exact GlobalTheory.ParahoricTopo.isOpen_isCompact_parJ | (intros; apply GlobalTheory.ParahoricTopo.isOpen_isCompact_parJ <;> assumption)
end

section

open MeasureTheory Matrix NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DoubleCosetMeasures Formalism.L2.Host Formalism.L2.DIV Formalism.L2.DIV.QLoc GlobalTheory.Mem.HD

theorem _root_.GlobalTheory.T.parahoricCharacter_mul_of_tame : ∀ (L : Type) [Field L] [NumberField L] (P : HeightOneSpectrum (𝓞 L)) (δ : (P.adicCompletion L)ˣ →* ℂˣ), IsDel P δ → ∀ (r c : ℕ) (k k' : GL (Fin (r + c)) (P.adicCompletion L)), k ∈ parJ (OP P) (piP P : P.adicCompletion L) r c → k' ∈ parJ (OP P) (piP P : P.adicCompletion L) r c → lamJ δ (k * k') = lamJ δ k * lamJ δ k' := by
  first | exact @GlobalTheory.Mem.LamMul.lamJ_mul | exact GlobalTheory.Mem.LamMul.lamJ_mul | (intros; apply GlobalTheory.Mem.LamMul.lamJ_mul <;> assumption)
end

section

open MeasureTheory Matrix NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DoubleCosetMeasures Formalism.L2.Host Formalism.L2.DIV Formalism.L2.DIV.QLoc GlobalTheory.Mem.HD

theorem _root_.GlobalTheory.T.exists_haar_GL_completion_integers_vol_one : ∀ (L : Type) [Field L] [NumberField L] (P : HeightOneSpectrum (𝓞 L)) (r : ℕ), ∃ μ : Measure (GL (Fin r) (P.adicCompletion L)), μ.IsMulLeftInvariant ∧ μ ((GLint (OP P) r : Subgroup (GL (Fin r) (P.adicCompletion L))) : Set (GL (Fin r) (P.adicCompletion L))) = 1 := by
  first | exact @GlobalTheory.haar_glInt_one | exact GlobalTheory.haar_glInt_one | (intros; apply GlobalTheory.haar_glInt_one <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

theorem _root_.GlobalTheory.T.algebraicModularForms_irreducible_decomposition : ∀ (D : D7) (μ : D.what₂.Tup) (j : ℕ) (Mr : MtReal D μ j), ∃ (ι : Type) (_ : Finite ι) (F : ι → Submodule ℂ (GAf D.host.E D.R.nV → Mr.wt.W)), (∀ P, NG.IsIrrRep Mr.wt.ρ (F P)) ∧ (∀ P P', NG.IsoRep (F P) (F P') → P = P') ∧ (∀ S', NG.IsIrrRep Mr.wt.ρ S' → (NG.isoTyp Mr.wt.ρ S').comap Mr.real ≠ ⊥ → ∃ P, NG.IsoRep (F P) S') ∧ (∀ P, (NG.isoTyp Mr.wt.ρ (F P)).comap Mr.real ≠ ⊥) ∧ iSupIndep (fun P => (NG.isoTyp Mr.wt.ρ (F P)).comap Mr.real) ∧ ⨆ P, (NG.isoTyp Mr.wt.ρ (F P)).comap Mr.real = ⊤ := by
  first | exact @GlobalTheory.AutReps.mtReal_decomp | exact GlobalTheory.AutReps.mtReal_decomp | (intros; apply GlobalTheory.AutReps.mtReal_decomp <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.LevForms

theorem typeSpF_finiteDimensional : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (K : Type) [Field K] {W : Type} [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] (ρ : Representation K (GQ L n) W) (J : Subgroup (GAf L n)) (χ : J →* Kˣ),
    (∃ N : ℕ, 0 < N ∧ ∀ κ, NG.Cong L n N κ → ∃ h : κ ∈ J, χ ⟨κ, h⟩ = 1) →
    FiniteDimensional K ↥(NX.TypeSpF L n K ρ J χ) := by
  intro L _ _ _ n K _ W _ _ _ ρ J χ hJ
  classical
  obtain ⟨N, hN, hNJ⟩ := hJ
  obtain ⟨T, hT⟩ := GlobalTheory.T.finite_doubleCosets_definiteUnitary_maximalLevel L n
  obtain ⟨Jc, hJc⟩ := GlobalTheory.AlgFormsFin.exists_cover L n hN
  let Φ : ↥(NX.TypeSpF L n K ρ J χ) →ₗ[K] (↥(T ×ˢ Jc) → W) :=
    { toFun := fun f p => (f : GAf L n → W) (p.1.1 * p.1.2)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine Module.Finite.of_injective Φ ((injective_iff_map_eq_zero Φ).2 fun f hf => ?_)
  refine Subtype.ext (funext fun g => ?_)
  obtain ⟨γ, t, u, ht, hu, rfl⟩ := hT g
  obtain ⟨j, hj, κ, hκ, rfl⟩ := hJc u hu
  have h0 : (f : GAf L n → W) (t * j) = 0 :=
    congrFun hf ⟨(t, j), Finset.mem_product.2 ⟨ht, hj⟩⟩
  obtain ⟨hκJ, hκ1⟩ := hNJ κ hκ
  have e : (γ : GAf L n) * t * (j * κ) = ((γ : GAf L n) * (t * j)) * κ := by simp only [mul_assoc]
  show (f : GAf L n → W) _ = 0
  rw [e, f.2.2 ⟨κ, hκJ⟩, hκ1, f.2.1 γ, h0, map_zero, Units.val_one, one_smul]

end GlobalTheory.LevForms
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

theorem _root_.GlobalTheory.T.schur_orthogonality_dim_pairing_eq_inner : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.BaseW F → Seed.PrIso R.MX R.cX R.prX → ∀ (t : T) (h h' : (R.HX t).H), (((∏ τ, (Module.finrank ℂ (R.MX.H τ) : ℝ)) : ℝ) : ℂ) * ipMT R.MX (R.νX t) (R.fdX t) (R.cX.toMap R.prX ((R.HX t).e h)) (R.cX.toMap R.prX ((R.HX t).e h')) = ⟪h, h'⟫_ℂ := by
  first | exact @GlobalTheory.Mem.TopSchur.topSchur | exact GlobalTheory.Mem.TopSchur.topSchur | (intros; apply GlobalTheory.Mem.TopSchur.topSchur <;> assumption)
end
