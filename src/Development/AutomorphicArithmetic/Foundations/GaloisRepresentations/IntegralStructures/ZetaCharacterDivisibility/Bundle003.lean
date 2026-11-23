module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.CharOfZeta
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PhiOfDivOf
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceUnitaryLocalPointsEquivGL
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.Bundle022
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle546
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle256
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle320
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.Bundle004
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle012

@[expose] public section

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.Int.Div

namespace UpperTheory.Gal.Int.Div

theorem algGen_of : AlgGen := by
  intro a q B hq hB
  have hz : ((((q : ℝ) ^ (((a : ℝ) - 1) / 2) : ℝ) : ℂ)) ≠ 0 := by
    have : (0 : ℝ) < (q : ℝ) ^ (((a : ℝ) - 1) / 2) := Real.rpow_pos_of_pos (by positivity) _
    exact_mod_cast this.ne'
  have := UpperTheory.Gal.crystallineComparison.genScale_of B _ hz hB
  convert this using 1
  simp [algSat, Multiset.bind_def, Multiset.pure_def]

theorem detFrob_of : DetFrob := by
  intro E Ω _ _ _ _ _ _ l _ ι a U ψ hψ w hw hl B hB A hA
  obtain ⟨J, hJ, -⟩ := hψ.2 w hw B hB
  obtain ⟨h1, h2⟩ := hJ hl A hA
  refine ⟨fun s hs => ?_, fun σ hσ => ?_⟩
  · have := congrArg (fun g : GL (Fin 1) (Qbar l) => g.val 0 0) (h1 s hs)
    exact Units.ext (by simpa [rk1] using this)
  · have := congrArg (fun p : ℂ[X] => p.coeff 0) (h2 σ hσ)
    simpa [rk1, Matrix.charpoly, Matrix.det_fin_one] using this

theorem frobSeed_of (h1 : InFacts) (h2 : GenPin) (h3 : AlgGen) (h4 : DetFrob) : FrobeniusCondition := by
  intro E Ω _ _ _ _ _ _ l _ ι a dd U ψ hψ r ρ hin hdet w hw hl B hB hg he A hA
  obtain ⟨-, i1, i2⟩ := h1 _ _ a dd r ρ hin
  obtain ⟨e1, e2⟩ := he A hA
  refine ⟨fun s hs => i1 s (e1 s hs), fun σ hσ => ?_⟩
  have hc : B.card = a := hB.choose_spec.2.card
  have hn : normV w ≠ 0 := by
    have h := NumberField.HeightOneSpectrum.one_lt_absNorm w
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at h
    exact h.ne_bot
  refine h2 l ι a _ _ (by simp [algSat, hc]) (h3 a _ B hn hg) (i2 σ⁻¹ _ (e2 σ hσ)) ?_
  rw [hdet]
  exact (h4 E Ω l ι a U ψ hψ w hw hl B hB A hA).2 σ hσ

theorem centU_of (h1 : ZetaEx) (h2 : ZetaLoc) (h3 : SchurU) (h4 : CharOfZeta) (h5 : AlgOfFix) (h6 : SatCent) : CentU := by
  intro E _ _ _ a ha U hU
  obtain ⟨ζ, z1, z2, z3, z4, z5⟩ := h1 E a
  obtain ⟨χ, hχ⟩ := h4 E a U hU ζ z2 z3 z4 fun z => h3 E a U hU _ (z3 z)
  obtain ⟨φ, hφ, hφ0⟩ := (Submodule.ne_bot_iff _).1 hU.ne_bot
  obtain ⟨n, hn⟩ := h5 E χ fun z hz => by
    have := hχ z φ hφ
    rw [z5 z hz, map_one] at this
    refine Units.ext (smul_left_injective ℂ hφ0 ?_)
    simpa using this.symm
  refine ⟨χ, n, hn, fun w hw B hB => ?_⟩
  obtain ⟨σ, ⟨hirr, f, hf0, hfU, hfe⟩, hS⟩ := hB
  obtain ⟨x, hx0, hx1, hx2⟩ := h6 E a w σ B hS
  obtain ⟨e, he⟩ := GlobalTheory.locU_equiv_GL E a w hw
  have hker : LinearMap.ker f = ⊥ := ((GlobalTheory.CuspRep.isIrreducible_iff σ.ρ).1 hirr).2 _ (fun g v hv => by
      rw [LinearMap.mem_ker] at hv ⊢
      have h1 := hfe (e.symm g) v
      rw [MonoidHom.comp_apply, Subgroup.subtype_apply, ← he, e.apply_symm_apply] at h1
      rw [h1, hv, map_zero]) |>.resolve_right fun h => hf0 (LinearMap.ker_eq_top.1 h)
  have hfx : f x ≠ 0 := (map_ne_zero_iff f (LinearMap.ker_eq_bot.1 hker)).2 hx0
  have key : ∀ u : (w.adicCompletion E)ˣ, f (σ.ρ (Matrix.GeneralLinearGroup.scalar (Fin a) u) x) =
      ((χ.loc w u : ℂˣ) : ℂ) • f x := fun u => by
    obtain ⟨m1, m2⟩ := h2 E a ζ z1 w hw u
    have := hfe ⟨_, m1⟩ x
    rw [MonoidHom.comp_apply, Subgroup.subtype_apply, m2] at this
    exact this.trans (hχ _ _ (hfU x))
  refine ⟨fun u hu => ?_, ?_⟩
  · have := key u
    rw [hx1 u hu] at this
    refine Units.ext (smul_left_injective ℂ hfx ?_)
    simpa using this.symm
  · have := key (atFin w (unif w))
    rw [hx2 _ (unif_spec w), map_smul] at this
    exact Units.ext (smul_left_injective ℂ hfx this.symm)

end UpperTheory.Gal.Int.Div
end

section

open NumberField IsDedekindDomain
open Neutral.B1 hiding G
open Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.BlockSum (blockRep)
open PositivityTheory.AutomorphicGaloisHodgeTate.Div (DivWCoreLac SenWLac HTLac IsSSMat)
open UpperTheory.Gal.Int.Div

theorem UpperTheory.Gal.Int.Div.divSet_of :
    DivWCoreLac → SenWLac → LacBridge → InFacts → DivSet := by
  intro hcore hsen hlac _ E Ω _ _ _ _ _ l _ a dd ρ hρ hss hHT ψ hψ hD
  classical
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  have : IsGalois E Ω := {}
  have : CompactSpace (G E Ω) := inferInstanceAs (CompactSpace (Ω ≃ₐ[E] Ω))
  obtain ⟨K', _, _, _, X, hX, hroots⟩ := hsen E Ω l dd a ρ hρ (hlac E Ω l a dd ρ hHT)
  let T : G E Ω → (Qbar l)[X] → Prop := fun g Q => Q.Monic ∧ Q.natDegree = a ∧
    aeval (ρ g : Matrix (Fin dd) (Fin dd) (Qbar l)) Q = 0 ∧
      ((ψ g : (Qbar l)ˣ) : Qbar l) = (-1) ^ a * Q.coeff 0
  let P : G E Ω → (Qbar l)[X] := fun g => if h : ∃ Q, T g Q then h.choose else 1
  have hP : ∀ s ∈ {g : G E Ω | ∃ Q, T g Q}, T s (P s) := by
    intro s hs
    have e : P s = (show ∃ Q, T s Q from hs).choose := dif_pos hs
    rw [e]
    exact (show ∃ Q, T s Q from hs).choose_spec
  have hss' : IsSSMat ρ := by
    intro W hW
    obtain ⟨W', h1, h2⟩ := hss W hW
    exact ⟨W', h2, h1⟩
  obtain ⟨r, hrc, hrss, hin, hco, -, -, -, hopen, hdense, -, -⟩ :=
    hcore (G E Ω) (Qbar l) K' dd a ρ (Units.continuous_val.comp hρ) hss'
      {g : G E Ω | ∃ Q, T g Q} hD P
      (fun s hs => ⟨(hP s hs).1, (hP s hs).2.1⟩) (fun s hs => (hP s hs).2.2.1)
      X hX hroots ψ (Units.continuous_val.comp hψ) (fun s hs => (hP s hs).2.2.2)
  refine ⟨r, ?_, ?_, hin, hco, hopen, hdense⟩
  · refine Units.continuous_iff.mpr ⟨hrc, ?_⟩
    simp only [← map_inv]
    exact hrc.comp continuous_inv
  · intro W hW
    obtain ⟨W', h1, h2⟩ := hrss W hW
    exact ⟨W', h2, h1⟩
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.BlockSum (blockRep)
open PositivityTheory.AutomorphicGaloisHodgeTate.Div (DivWCoreLac SenWLac HTLac IsSSMat)
open UpperTheory.Gal.Int.Div

private theorem pow_intertwine {k : Type} [Field k] {a d : ℕ} {P : Matrix (Fin d) (Fin d) k}
    {R : Matrix (Fin a) (Fin a) k} {A : Matrix (Fin d) (Fin a) k} (h : P * A = A * R) (n : ℕ) :
    P ^ n * A = A * R ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, Matrix.mul_assoc, h, ← Matrix.mul_assoc, ih, Matrix.mul_assoc, pow_succ]

private theorem aeval_intertwine {k : Type} [Field k] {a d : ℕ} {P : Matrix (Fin d) (Fin d) k}
    {R : Matrix (Fin a) (Fin a) k} {A : Matrix (Fin d) (Fin a) k} (h : P * A = A * R) (Q : k[X]) :
    aeval P Q * A = A * aeval R Q := by
  induction Q using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), Matrix.add_mul, Matrix.mul_add, hp, hq]
  | monomial n c =>
    rw [aeval_monomial, aeval_monomial, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
    simp only [smul_mul_assoc, one_mul, Matrix.smul_mul, Matrix.mul_smul, pow_intertwine h n]

private theorem left_cancel {k : Type} [Field k] {a d : ℕ} {A : Matrix (Fin d) (Fin a) k} (hA : A.rank = a)
    {M N : Matrix (Fin a) (Fin a) k} (h : A * M = A * N) : M = N := by
  have hker : LinearMap.ker A.mulVecLin = ⊥ := by
    have h1 := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
    have h2 : Module.finrank k (LinearMap.range A.mulVecLin) = a := by
      rw [Matrix.finrank_range_mulVecLin]; exact hA
    rw [h2, Module.finrank_fin_fun] at h1
    exact Submodule.finrank_eq_zero.mp (by omega)
  have hinj := LinearMap.ker_eq_bot.mp hker
  ext i j
  have hv : M.mulVec (Pi.single j 1) = N.mulVec (Pi.single j 1) := by
    apply hinj
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, h]
  simpa using congrFun hv i

theorem UpperTheory.Gal.Int.Div.inFacts_of :
    InFacts := by
  intro Γ k _ _ a d r ρ ⟨A, hA, hc⟩
  refine ⟨hA ▸ A.rank_le_height, fun g hg => ?_, fun g Q hQ => ?_⟩
  · have h := hc g
    rw [hg] at h
    apply Units.ext
    apply left_cancel hA
    simpa using h.symm
  · apply left_cancel hA
    rw [← aeval_intertwine (hc g) Q, hQ]
    simp
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.BlockSum (blockRep)
open PositivityTheory.AutomorphicGaloisHodgeTate.Div (DivWCoreLac SenWLac HTLac IsSSMat)
open UpperTheory.Gal.Int.Div

noncomputable section

namespace UpperTheory.Gal.Int.Div

section SubSplitAux

variable {Γ k : Type} [Group Γ] [Field k] {n a b : ℕ}

private lemma sumRep_val (r : Γ →* GL (Fin a) k) (s : Γ →* GL (Fin b) k) (g : Γ) :
    ((sumRep r s g : GL (Fin (a + b)) k) : Matrix (Fin (a + b)) (Fin (a + b)) k) =
      (Matrix.fromBlocks (r g : Matrix (Fin a) (Fin a) k) 0 0
        (s g : Matrix (Fin b) (Fin b) k)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm := rfl

private def resHom (ρ : Γ →* GL (Fin n) k) {W' : Submodule k (Fin n → k)}
    (hinv : IsInv ρ W') : Γ →* Module.End k W' where
  toFun g := (Matrix.mulVecLin (ρ g : Matrix (Fin n) (Fin n) k)).restrict (hinv g)
  map_one' := by ext x; simp
  map_mul' g h := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    change (ρ (g * h) : Matrix (Fin n) (Fin n) k).mulVec (x : Fin n → k) =
      (ρ g : Matrix (Fin n) (Fin n) k).mulVec
        ((ρ h : Matrix (Fin n) (Fin n) k).mulVec (x : Fin n → k))
    simp [Matrix.mulVec_mulVec]

private def subRep (ρ : Γ →* GL (Fin n) k) {W' : Submodule k (Fin n → k)}
    (hinv : IsInv ρ W') (c : Module.Basis (Fin b) k W') : Γ →* GL (Fin b) k :=
  MonoidHom.toHomUnits
    { toFun := fun g => LinearMap.toMatrix c c (resHom ρ hinv g)
      map_one' := by simp [LinearMap.toMatrix_one]
      map_mul' := fun g h => by
        rw [map_mul, Module.End.mul_eq_comp, LinearMap.toMatrix_comp c c c] }

private lemma subRep_val (ρ : Γ →* GL (Fin n) k) {W' : Submodule k (Fin n → k)}
    (hinv : IsInv ρ W') (c : Module.Basis (Fin b) k W') (g : Γ) :
    ((subRep ρ hinv c g : GL (Fin b) k) : Matrix (Fin b) (Fin b) k) =
      LinearMap.toMatrix c c (resHom ρ hinv g) := rfl

private def colM (A : Matrix (Fin n) (Fin a) k) {W' : Submodule k (Fin n → k)}
    (c : Module.Basis (Fin b) k W') : Matrix (Fin n) (Fin a ⊕ Fin b) k :=
  Matrix.of fun i => Sum.elim (fun j => A i j) (fun j => (c j : Fin n → k) i)

private lemma intertw (ρ : Γ →* GL (Fin n) k) {W' : Submodule k (Fin n → k)}
    (hinv : IsInv ρ W') (c : Module.Basis (Fin b) k W') (A : Matrix (Fin n) (Fin a) k)
    (R : Matrix (Fin a) (Fin a) k) (g : Γ)
    (hA : (ρ g : Matrix (Fin n) (Fin n) k) * A = A * R) :
    (ρ g : Matrix (Fin n) (Fin n) k) * colM A c =
      colM A c * Matrix.fromBlocks R 0 0 (subRep ρ hinv c g : Matrix (Fin b) (Fin b) k) := by
  ext i (j | j)
  · have h := congrFun (congrFun hA i) j
    simpa [colM, Matrix.mul_apply, Fintype.sum_sum_type] using h
  · have hs := congrArg (fun v : W' => (v : Fin n → k) i) (c.sum_repr (resHom ρ hinv g (c j)))
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul] at hs
    simp only [colM, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.of_apply, Sum.elim_inl,
      Sum.elim_inr, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply,
      mul_zero, Finset.sum_const_zero, zero_add, subRep_val, LinearMap.toMatrix_apply]
    refine Eq.trans ?_ (hs.symm.trans ?_)
    · rfl
    · exact Finset.sum_congr rfl fun x _ => mul_comm _ _

private lemma col_indep (A : Matrix (Fin n) (Fin a) k) (hA : A.rank = a)
    {W' : Submodule k (Fin n → k)} (c : Module.Basis (Fin b) k W')
    (hc : IsCompl (LinearMap.range A.mulVecLin) W') :
    LinearIndependent k (Sum.elim A.col (fun j => (c j : Fin n → k))) := by
  apply LinearIndependent.sum_type
  · rw [linearIndependent_iff_card_eq_finrank_span, Fintype.card_fin]
    calc a = Module.finrank k (LinearMap.range A.mulVecLin) := by
          rw [Matrix.finrank_range_mulVecLin]; exact hA.symm
      _ = _ := by
        rw [Matrix.range_mulVecLin]
        rfl
  · exact c.linearIndependent.map' W'.subtype (Submodule.ker_subtype W')
  · refine hc.disjoint.mono ?_ ?_
    · rw [Matrix.range_mulVecLin]
    · rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      exact (c j).2

end SubSplitAux

theorem subSplit_of : SubSplit := by
  intro Γ k _ _ a b r ρ hss ⟨A, hA, hAg⟩
  have hinvW : IsInv ρ (LinearMap.range A.mulVecLin) := by
    rintro g _ ⟨u, rfl⟩
    refine ⟨(r g : Matrix (Fin a) (Fin a) k).mulVec u, ?_⟩
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hAg g]
  obtain ⟨W', hinv, hc⟩ := hss _ hinvW
  have hdim : Module.finrank k W' = b := by
    have h1 := Submodule.finrank_add_eq_of_isCompl hc
    have h2 : Module.finrank k (LinearMap.range A.mulVecLin) = a := by
      rw [Matrix.finrank_range_mulVecLin]; exact hA
    rw [Module.finrank_fin_fun] at h1
    omega
  let c : Module.Basis (Fin b) k W' := Module.finBasisOfFinrankEq k W' hdim
  let e : Fin a ⊕ Fin b ≃ Fin (a + b) := finSumFinEquiv
  let P : Matrix (Fin (a + b)) (Fin (a + b)) k := (colM A c).submatrix id e.symm
  have hP : IsUnit P := by
    rw [← Matrix.linearIndependent_cols_iff_isUnit]
    have h := (col_indep A hA c hc).comp e.symm e.symm.injective
    convert h using 1
    ext j i
    rcases h' : e.symm j with j' | j' <;> simp [P, colM, Matrix.col, h'] <;> rfl
  have hinvP : ((hP.unit⁻¹ : GL (Fin (a + b)) k) : Matrix _ _ k) * P = 1 := by
    have h := hP.unit.inv_mul
    rwa [hP.unit_spec] at h
  refine ⟨subRep ρ hinv c, hP.unit⁻¹, fun x => ?_⟩
  have hx : (ρ x : Matrix _ _ k) * P = P * (Matrix.fromBlocks (r x : Matrix (Fin a) (Fin a) k) 0 0
      (subRep ρ hinv c x : Matrix (Fin b) (Fin b) k)).submatrix e.symm e.symm := by
    rw [Matrix.submatrix_mul_equiv, ← intertw ρ hinv c A (r x) x (hAg x)]
    ext i j
    simp [P, Matrix.mul_apply]
  rw [inv_inv]
  apply Units.ext
  rw [sumRep_val, Units.val_mul, Units.val_mul, hP.unit_spec, mul_assoc, hx, ← mul_assoc, hinvP,
    one_mul]

end UpperTheory.Gal.Int.Div

end
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.BlockSum (blockRep)
open PositivityTheory.AutomorphicGaloisHodgeTate.Div (DivWCoreLac SenWLac HTLac IsSSMat)
open UpperTheory.Gal.Int.Div

theorem UpperTheory.Gal.Int.Div.jumpCard_of :
    JumpCard := by
  intro l _ P AI tied E Ω _ _ _ _ _ A O _ _ _ Bw a r hdR τ LL' τ' hτ
  obtain ⟨T⟩ := id tied
  obtain ⟨L₀, r₀, hm, hd⟩ := hdR
  have l₁ : L₀.1 ≤ (supExt L₀ LL').1 := le_sup_left
  have l₂ : LL'.1 ≤ (supExt L₀ LL').1 := le_sup_right
  have hm' := hm.enlarge l₁
  have hd' := (local_ext P Bw l₁ r₀).2.1.2 hd
  have hτ' : IsInduced Bw τ ((IntermediateField.inclusion l₂).comp τ') := fun x => hτ x
  have hdr' : IsDR (P.PD Bw.Kw) (Bw.repE (supExt L₀ LL') (mapRep (IntermediateField.inclusion l₁).toRingHom r₀)) := by
    rw [IsDR, Module.finrank_fin_fun]
    exact hd'
  obtain ⟨hfin, -, hrk⟩ := (GlobalTheory.Per.Components.components_finrank l P AI T _ (supExt L₀ LL') _
    (Bw.repE (supExt L₀ LL') (mapRep (IntermediateField.inclusion l₁).toRingHom r₀))).1
      ((IntermediateField.inclusion l₂).comp τ')
  obtain ⟨J', h1, h2⟩ := @GlobalTheory.HtCardProof.exists_count _ _ _ _ _ T _ _
    ((mapRep (IntermediateField.inclusion l₁).toRingHom r₀).comp Bw.e.symm.toMonoidHom)
    ((IntermediateField.inclusion l₂).comp τ') hfin
  exact ⟨J', ⟨_, _, hm', hd', _, hτ', h2⟩, h1.trans ((hrk hdr').trans (Module.finrank_fin_fun _))⟩
end

section

open NumberField IsDedekindDomain
open Neutral.B1 hiding Dec
open Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.BlockSum (blockRep)
open PositivityTheory.AutomorphicGaloisHodgeTate.Div (DivWCoreLac SenWLac HTLac IsSSMat)
open UpperTheory.Gal.Int.Div

theorem UpperTheory.Gal.Int.Div.subLoc_of :
    SubSplit → InFacts → LocConj → LocSum → JumpCard → SubLoc := by
  intro hS hI hC hL _ E Ω _ _ _ _ _ l _ a d r ρ hss hin ι w P AI hT A h O _ _ _ Bw hj
  obtain ⟨had, -, -⟩ := hI _ _ a d r ρ hin
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le had
  obtain ⟨s, g, hg⟩ := hS _ _ a b r ρ hss hin
  have e : (sumRep r s).comp (Dec (F := E) A).subtype =
      sumRep (r.comp (Dec (F := E) A).subtype) (s.comp (Dec (F := E) A).subtype) := by
    ext; rfl
  have hiso : RepIso (ρ.comp (Dec (F := E) A).subtype)
      (sumRep (r.comp (Dec (F := E) A).subtype) (s.comp (Dec (F := E) A).subtype)) := by
    refine ⟨g, fun x => ?_⟩
    rw [← e]
    exact hg x
  have hconj := (hC l P AI hT E Ω A O Bw (a + b) (ρ.comp (Dec (F := E) A).subtype) _).2 hiso
  have hsum := hL l P AI hT E Ω A O Bw a b (r.comp (Dec (F := E) A).subtype) (s.comp (Dec (F := E) A).subtype)
  refine ⟨fun hc => ?_, fun τ J J' h1 h2 => hsum.2 τ J J' (hconj.2.2.1 τ J h1) h2⟩
  have hcS := hconj.1 hc
  obtain ⟨cr, cs⟩ := hsum.1 hcS
  refine ⟨cr, fun x => ?_⟩
  have pr := ((hC l P AI hT E Ω A O Bw a _ (r.comp (Dec (F := E) A).subtype)).1 cr).2
  have ps := ((hC l P AI hT E Ω A O Bw b _ (s.comp (Dec (F := E) A).subtype)).1 cs).2
  have pT := ((hC l P AI hT E Ω A O Bw (a + b) _ (ρ.comp (Dec (F := E) A).subtype)).1 hcS).2
  have hw := GlobalTheory.T.weilDeligneParamAboveL_directSum_potSemistable l P AI hT ι E Ω A w O Bw h hj a b _ _ pr ps pT
  rw [← hconj.2.2.2 ι w h hj hc, hw, (UpperTheory.Gal.TP.Sub.wDFacts_holds E Ω A w h _ _).2.1 x]
  exact Dvd.intro _ rfl
end
