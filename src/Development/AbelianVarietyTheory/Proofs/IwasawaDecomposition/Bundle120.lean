module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle049
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle090
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle107
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle062
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle082
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle070
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle091
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle097
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle108
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle063
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle072
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIndexIdeal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle109
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.AbsPowOneNotIsAlgRat
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle014
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle092
public import Formalism.AlgebraicWeights.InertDatumExists
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle110
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle102
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle047
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.Bundle001
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

section

noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.AlgWtHW
open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField Finset

section
variable {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]

theorem sle_mulVec {Φ : GL (Fin n) ℂ → Matrix ι ι ℂ} {M : Matrix ι ι ℂ} (hM : ∀ A, M * Φ A = Φ A * M)
    (lam : Fin n → ℤ) {x : ι → ℂ} (hx : x ∈ Sle Φ lam) : M *ᵥ x ∈ Sle Φ lam := by
  have h : Sle Φ lam ≤ (Sle Φ lam).comap (Matrix.mulVecLin M) := by
    refine Submodule.span_le.2 ?_
    rintro w ⟨ν, hν, hw⟩
    refine Submodule.subset_span ⟨ν, hν, fun D hD => ?_⟩
    show Φ D *ᵥ (M *ᵥ w) = _
    rw [Matrix.mulVec_mulVec, ← hM, ← Matrix.mulVec_mulVec, hw D hD, Matrix.mulVec_smul]
    rfl
  exact h hx

theorem filter_succ (i : Fin n) : univ.filter (fun j : Fin n => (j : ℕ) < (i : ℕ) + 1) =
    insert i (univ.filter (fun j : Fin n => (j : ℕ) < i)) := by
  ext j
  simp only [mem_filter, mem_univ, true_and, mem_insert, Fin.ext_iff]
  omega

theorem not_mem_filter_self (i : Fin n) : i ∉ univ.filter (fun j : Fin n => (j : ℕ) < i) := by
  simp

theorem domLE_antisymm {μ lam : Fin n → ℤ} (h1 : DomLE μ lam) (h2 : DomLE lam μ) : μ = lam := by
  have hs : ∀ k : ℕ, ∑ i ∈ univ.filter (fun i : Fin n => (i : ℕ) < k), μ i =
      ∑ i ∈ univ.filter (fun i : Fin n => (i : ℕ) < k), lam i := fun k => le_antisymm (h1.2 k) (h2.2 k)
  funext i
  have h := hs ((i : ℕ) + 1)
  rw [filter_succ, sum_insert (not_mem_filter_self i), sum_insert (not_mem_filter_self i), hs i] at h
  linarith

theorem le_of_domLE_swap {lam : Fin n → ℤ} {i j : Fin n} (hij : i < j)
    (h : DomLE (lam ∘ Equiv.swap i j) lam) : lam j ≤ lam i := by
  have h1 := h.2 ((i : ℕ) + 1)
  rw [filter_succ, sum_insert (not_mem_filter_self i), sum_insert (not_mem_filter_self i)] at h1
  have h2 : ∑ l ∈ univ.filter (fun l : Fin n => (l : ℕ) < i), (lam ∘ Equiv.swap i j) l =
      ∑ l ∈ univ.filter (fun l : Fin n => (l : ℕ) < i), lam l := by
    refine sum_congr rfl fun l hl => ?_
    simp only [mem_filter, mem_univ, true_and] at hl
    have hli : l ≠ i := fun e => by rw [e] at hl; omega
    have hlj : l ≠ j := fun e => by rw [e] at hl; rw [Fin.lt_def] at hij; omega
    simp [Function.comp, Equiv.swap_apply_of_ne_of_ne hli hlj]
  rw [h2] at h1
  simp only [Function.comp, Equiv.swap_apply_left] at h1
  linarith

end

section
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem algWeight_space_nontrivial (a : AlgWt L n) : Nontrivial a.W := by
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  have := a.irr
  exact bot_ne_top (α := Subrepresentation a.ρ)
    (Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _))

theorem beig_of_hwAt {a : AlgWt L n} {τ : L →+* ℂ} {lam : Fin n → ℤ} (h : a.HWAt τ lam) :
    ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (b : Module.Basis ι ℂ a.W)
      (P : ι → ι → MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ) (v : ι → ℂ),
      Agrees a b P ∧ IsBEig (fun B => evM P (evPt τ B)) v lam := by
  obtain ⟨ι, i1, i2, b, P, hP, v, hv, hB⟩ := h
  exact ⟨ι, i1, i2, b, P, v, hP, hv, hB⟩

theorem domLE_of_agrees {a : AlgWt L n} {τ : L →+* ℂ} {ι : Type} [Fintype ι] [DecidableEq ι]
    {b : Module.Basis ι ℂ a.W} {P : ι → ι → MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ}
    (hP : Agrees a b P) {v : ι → ℂ} {lam μ : Fin n → ℤ}
    (hv : IsBEig (fun B => evM P (evPt τ B)) v lam) (hμ : IsWt (fun B => evM P (evPt τ B)) μ) :
    DomLE μ lam := by
  obtain ⟨w, hw0, hw⟩ := hμ
  have hR := GlobalTheory.T.isPolynomialRepGLComplex_algebraicWeight_evalPoint L n a ι b P hP τ
  refine GlobalTheory.T.dominanceOrderLE_of_mem_spanWeightVectorsDominatedBy n ι _ hR μ lam w hw hw0 ?_
  have hspan := GlobalTheory.T.algebraicWeight_span_translates_factor_commutant L n a ι b P hP τ v hv.1 w
  refine (Submodule.span_le.2 ?_) hspan
  rintro x ⟨B, M, hM, rfl⟩
  have e : evM P (evPt τ B) *ᵥ (M *ᵥ v) = M *ᵥ (evM P (evPt τ B) *ᵥ v) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hM]
  rw [e]
  exact sle_mulVec hM lam (GlobalTheory.T.mulVec_mem_span_lower_weights_of_borelEigenvector n ι _ hR v lam hv B)

theorem isWt_of_beig {ι : Type} [Fintype ι] {Φ : GL (Fin n) ℂ → Matrix ι ι ℂ} {v : ι → ℂ} {lam : Fin n → ℤ}
    (h : IsBEig Φ v lam) : IsWt Φ lam :=
  ⟨v, h.1, fun D hD => h.2 D (fun i j hij => hD (ne_of_gt hij))⟩

theorem beig_transport {a : AlgWt L n} {τ : L →+* ℂ} {ι : Type} [Fintype ι] [DecidableEq ι]
    {b : Module.Basis ι ℂ a.W} {P : ι → ι → MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ}
    {ι' : Type} [Fintype ι'] [DecidableEq ι']
    {b' : Module.Basis ι' ℂ a.W} {P' : ι' → ι' → MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ}
    (hP : Agrees a b P) (hP' : Agrees a b' P') {v' : ι' → ℂ} {lam : Fin n → ℤ}
    (hv : IsBEig (fun B => evM P' (evPt τ B)) v' lam) :
    IsBEig (fun B => evM P (evPt τ B)) (b.toMatrix b' *ᵥ v') lam := by
  have hC : b'.toMatrix b * b.toMatrix b' = 1 := Module.Basis.toMatrix_mul_toMatrix_flip b' b
  refine ⟨fun h0 => hv.1 ?_, fun B hB => ?_⟩
  · have := congrArg (fun x => b'.toMatrix b *ᵥ x) h0
    simpa [Matrix.mulVec_mulVec, hC] using this
  · show evM P (evPt τ B) *ᵥ (b.toMatrix b' *ᵥ v') = _
    rw [GlobalTheory.T.algebraicWeight_polyMatrix_change_of_basis L n a ι' b' P' ι b P hP' hP τ B, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc, hC,
      Matrix.mul_one, ← Matrix.mulVec_mulVec]
    have := hv.2 B hB
    simp only at this
    rw [this, Matrix.mulVec_smul]

theorem hw_exists_unique_antitone : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n)
    (τ : L →+* ℂ), (∃! lam, a.HWAt τ lam) ∧ ∀ lam, a.HWAt τ lam → Antitone lam := by
  intro L _ _ _ n a τ
  have hanti : ∀ lam, a.HWAt τ lam → Antitone lam := by
    intro lam h
    obtain ⟨ι, _, _, b, P, v, hP, hv⟩ := beig_of_hwAt h
    intro i j hij
    rcases eq_or_lt_of_le hij with e | hlt
    · rw [e]
    · exact le_of_domLE_swap hlt (domLE_of_agrees hP hv
        (GlobalTheory.T.isTorusWeightOfPolyRep_comp_swap n ι _ (GlobalTheory.T.isPolynomialRepGLComplex_algebraicWeight_evalPoint L n a ι b P hP τ) lam (isWt_of_beig hv) i j))
  refine ⟨?_, hanti⟩
  obtain ⟨_, ι, _, _, b, P, hP⟩ := a.alg
  haveI := algWeight_space_nontrivial a
  haveI := b.index_nonempty
  obtain ⟨v, lam, hv⟩ := GlobalTheory.T.exists_borelEigenvector_of_polynomialRepGLComplex n ι _ (GlobalTheory.T.isPolynomialRepGLComplex_algebraicWeight_evalPoint L n a ι b P hP τ)
  refine ⟨lam, ⟨ι, inferInstance, inferInstance, b, P, hP, v, hv.1, hv.2⟩, fun lam' h' => ?_⟩
  obtain ⟨ι', _, _, b', P', v', hP', hv'⟩ := beig_of_hwAt h'
  have hv'' := beig_transport hP hP' hv'
  exact domLE_antisymm (domLE_of_agrees hP hv (isWt_of_beig hv'')) (domLE_of_agrees hP hv'' (isWt_of_beig hv))

end

end GlobalTheory.AlgWtHW
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.expModelFiber_eq_one_iff_mem_periodLattice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (σ₀ : KA l →+* ℂ) (Fu : FamilyUnif Xo σ₀ ty) (y : Sp ℂ ⟶ Xo.XF c) (i : Fin Fu.n) (P : (Fu.Di i).La →+ (Fin g → ℂ)) (p : Sp ℂ ⟶ Z.X) (hu : Fu.u i P = y ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) (hp : y ≫ Z.jQ ≫ pullback.fst Z.s (spMap β) = p), IsPeriod (Fu.Di i) ty P → ∀ z, pushEx Z Fu y i P p hu hp z = 1 ↔ z ∈ P.range := by
  first | exact @GlobalTheory.ShFam.Hor.LogCh.pushEx_eq_one_iff | exact GlobalTheory.ShFam.Hor.LogCh.pushEx_eq_one_iff | (intros; apply GlobalTheory.ShFam.Hor.LogCh.pushEx_eq_one_iff <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R

theorem _root_.GlobalTheory.T.exists_lineBundle_sections_generate_idealSheaf : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (J : X.IdealSheafData),
    IsProjOver s → ∃ (L₀ : LB X) (m : ℕ) (σ : Fin (m + 1) → L₀.Sec), L₀.IsLB ∧ GlobalTheory.ProjBlowup.Generates J σ := by
  first | exact @GlobalTheory.ProjBlowup.exists_generates_isLB | exact GlobalTheory.ProjBlowup.exists_generates_isLB | (intros; apply GlobalTheory.ProjBlowup.exists_generates_isLB <;> assumption)
end

section

open CategoryTheory Polynomial

theorem _root_.GlobalTheory.T.classFunctionLabel_of_labelMap_label : ∀ (g : ℕ) [Fact g.Prime] (L : GlobalTheory.GLq.LabelDatum g) {C : Formalism.IrreducibleCountingLemmas.TYPES.LabelConv (ZMod g)} (O : Formalism.IrreducibleCountingLemmas.TYPES.LabelMap (ZMod g) C), (∀ (d : ℕ) (V : FDRep ℂ (GL (Fin d) (ZMod g))), 1 ≤ d → CategoryTheory.Simple V → Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal (ZMod g) V → GlobalTheory.GLq.IsCuspOf L (O.lab d V) (fun x => V.character x)) → (∀ (r s : ℕ) (b : Fin r → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} (ZMod g))), Function.Surjective b → ∀ x : GL (Fin r) (ZMod g), LinearMap.trace ℂ (Formalism.IrreducibleCountingLemmas.TYPES.hcSpace (ZMod g) b lam) (Formalism.IrreducibleCountingLemmas.TYPES.hcRep (ZMod g) b lam x) = GlobalTheory.GLq.hcL (GlobalTheory.SerCmp.canonList b lam) r x) → (∀ (r s : ℕ) (b : Fin r → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} (ZMod g))) (τ : FDRep ℂ (GL (Fin r) (ZMod g))), CategoryTheory.Simple τ → (Formalism.IrreducibleCountingLemmas.TYPES.IsConstituent τ (Formalism.IrreducibleCountingLemmas.TYPES.hcRep (ZMod g) b lam) ↔ GlobalTheory.GLq.ip (fun x => τ.character x) (fun x => LinearMap.trace ℂ (Formalism.IrreducibleCountingLemmas.TYPES.hcSpace (ZMod g) b lam) (Formalism.IrreducibleCountingLemmas.TYPES.hcRep (ZMod g) b lam x)) ≠ 0)) → ∀ (r : ℕ) (τ : FDRep ℂ (GL (Fin r) (ZMod g))) (f : (ZMod g)[X]), CategoryTheory.Simple τ → Formalism.IrreducibleCountingLemmas.TYPES.HasLabelO O τ f → GlobalTheory.GLq.HasLabel L (fun x => τ.character x) f := by
  first | exact @GlobalTheory.SerCmp.hasLabel_of_hasLabelO | exact GlobalTheory.SerCmp.hasLabel_of_hasLabelO | (intros; apply GlobalTheory.SerCmp.hasLabel_of_hasLabelO <;> assumption)
end

section

open CategoryTheory Polynomial

theorem _root_.GlobalTheory.T.exists_blocks_of_cuspidal_character_list : ∀ (g : ℕ) [Fact g.Prime] (Q : List (GlobalTheory.GLq.Pc g)), (∀ p ∈ Q, 1 ≤ p.1 ∧ ∃ V : FDRep ℂ (GL (Fin p.1) (ZMod g)), CategoryTheory.Simple V ∧ Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal (ZMod g) V ∧ ∀ x, V.character x = p.2 x) → ∃ (b : Fin (GlobalTheory.GLq.degL Q) → Fin Q.length) (lam : ∀ c : Fin Q.length, FDRep ℂ (GL {i // b i = c} (ZMod g))), Function.Surjective b ∧ (∀ c, CategoryTheory.Simple (lam c) ∧ Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal (ZMod g) (lam c)) ∧ GlobalTheory.SerCmp.canonList b lam = Q := by
  first | exact @GlobalTheory.SerCmp.canonList_of_cuspidal_list | exact GlobalTheory.SerCmp.canonList_of_cuspidal_list | (intros; apply GlobalTheory.SerCmp.canonList_of_cuspidal_list <;> assumption)
end

section

open CategoryTheory Polynomial

theorem _root_.GlobalTheory.T.labelMap_label_of_classFunctionLabel : ∀ (g : ℕ) [Fact g.Prime] (L : GlobalTheory.GLq.LabelDatum g) {C : Formalism.IrreducibleCountingLemmas.TYPES.LabelConv (ZMod g)} (O : Formalism.IrreducibleCountingLemmas.TYPES.LabelMap (ZMod g) C), (∀ (d : ℕ) (V : FDRep ℂ (GL (Fin d) (ZMod g))) (P : (ZMod g)[X]), 1 ≤ d → CategoryTheory.Simple V → Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal (ZMod g) V → GlobalTheory.GLq.IsCuspOf L P (fun x => V.character x) → P = O.lab d V) → (∀ (d : ℕ) (χ : GlobalTheory.GLq.Gn g d → ℂ), GlobalTheory.GLq.IsCusp χ → ∃ V : FDRep ℂ (GL (Fin d) (ZMod g)), CategoryTheory.Simple V ∧ Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal (ZMod g) V ∧ ∀ x, V.character x = χ x) → (∀ (r s : ℕ) (b : Fin r → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} (ZMod g))), Function.Surjective b → ∀ x : GL (Fin r) (ZMod g), LinearMap.trace ℂ (Formalism.IrreducibleCountingLemmas.TYPES.hcSpace (ZMod g) b lam) (Formalism.IrreducibleCountingLemmas.TYPES.hcRep (ZMod g) b lam x) = GlobalTheory.GLq.hcL (GlobalTheory.SerCmp.canonList b lam) r x) → (∀ (r s : ℕ) (b : Fin r → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} (ZMod g))) (τ : FDRep ℂ (GL (Fin r) (ZMod g))), CategoryTheory.Simple τ → (Formalism.IrreducibleCountingLemmas.TYPES.IsConstituent τ (Formalism.IrreducibleCountingLemmas.TYPES.hcRep (ZMod g) b lam) ↔ GlobalTheory.GLq.ip (fun x => τ.character x) (fun x => LinearMap.trace ℂ (Formalism.IrreducibleCountingLemmas.TYPES.hcSpace (ZMod g) b lam) (Formalism.IrreducibleCountingLemmas.TYPES.hcRep (ZMod g) b lam x)) ≠ 0)) → (∀ (Q : List (GlobalTheory.GLq.Pc g)), (∀ p ∈ Q, 1 ≤ p.1 ∧ ∃ V : FDRep ℂ (GL (Fin p.1) (ZMod g)), CategoryTheory.Simple V ∧ Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal (ZMod g) V ∧ ∀ x, V.character x = p.2 x) → ∃ (b : Fin (GlobalTheory.GLq.degL Q) → Fin Q.length) (lam : ∀ c : Fin Q.length, FDRep ℂ (GL {i // b i = c} (ZMod g))), Function.Surjective b ∧ (∀ c, CategoryTheory.Simple (lam c) ∧ Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal (ZMod g) (lam c)) ∧ GlobalTheory.SerCmp.canonList b lam = Q) → ∀ (r : ℕ) (τ : FDRep ℂ (GL (Fin r) (ZMod g))) (f : (ZMod g)[X]), CategoryTheory.Simple τ → GlobalTheory.GLq.HasLabel L (fun x => τ.character x) f → Formalism.IrreducibleCountingLemmas.TYPES.HasLabelO O τ f := by
  first | exact @GlobalTheory.SerCmp.hasLabelO_of_hasLabel | exact GlobalTheory.SerCmp.hasLabelO_of_hasLabel | (intros; apply GlobalTheory.SerCmp.hasLabelO_of_hasLabel <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

theorem _root_.GlobalTheory.T.restrictedProductMeasure_basic_properties : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ) (ν : Measure (Fin n → Fin M → AF F ⊗[F] E)) (mi : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (mv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)), IsProd b ν mi mv → IsFiniteMeasureOnCompacts ν ∧ (mi ≠ 0 → (∀ v, mv v ≠ 0) → ν ≠ 0) ∧ (∀ ν', IsProd b ν' mi mv → ν' = ν) ∧ ∀ (Ai : Set (Fin n → Fin M → Ainf F ⊗[F] E)) (Av : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E)), MeasurableSet Ai → (∀ v, MeasurableSet (Av v)) → mi Aiᶜ = 0 → (∀ v, mv v (Av v)ᶜ = 0) → ν {X | ¬ (projInf X ∈ Ai ∧ ∀ v, projV v (projFin X) ∈ Av v)} = 0 := by
  first | exact @GlobalTheory.GaugeEx.isProd_basic | exact GlobalTheory.GaugeEx.isProd_basic | (intros; apply GlobalTheory.GaugeEx.isProd_basic <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

theorem _root_.GlobalTheory.T.stdHermitianFibreProduct_change_of_basis : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (s : StdMeas b) (M : ℕ) (J J' : Matrix (Fin M) (Fin M) E) (P : GL (Fin M) E) (β : F) (ν' : Measure (Fin 1 → Fin M → AF F ⊗[F] E)), J' = Formalism.UG.cT (σ : E →+* E) (P : Matrix (Fin M) (Fin M) E) * J * (P : Matrix (Fin M) (Fin M) E) → IsStdX s σ J' β ν' → IsStdX s σ J β (ν'.map (lrAct ((P : Matrix (Fin M) (Fin M) E).map (inclR (AF F))) 1)) := by
  first | exact @GlobalTheory.GaugeEx.BasisX.isStdX_basis | exact GlobalTheory.GaugeEx.BasisX.isStdX_basis | (intros; apply GlobalTheory.GaugeEx.BasisX.isStdX_basis <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.L2.Pj

theorem _root_.GlobalTheory.T.detSpan_conj_mul_integral_of_integral_pairing : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (M M' : Submodule (𝓞 E) (Fin n → E)), (∀ v ∈ M, ∀ w ∈ M', ∑ j, IsCMField.complexConj E (v j) * w j ∈ (algebraMap (𝓞 E) E).range) → ∀ x ∈ GlobalTheory.BetaEx.detSpan M, ∀ y ∈ GlobalTheory.BetaEx.detSpan M', IsCMField.complexConj E x * y ∈ (algebraMap (𝓞 E) E).range := by
  first | exact @GlobalTheory.detSpan_conj_mul_mem_range | exact GlobalTheory.detSpan_conj_mul_mem_range | (intros; apply GlobalTheory.detSpan_conj_mul_mem_range <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.L2.Pj

theorem _root_.GlobalTheory.T.exists_common_indexIdeal_inf_sup_lattices : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (M M' : Submodule (𝓞 E) (Fin n → E)), GlobalTheory.BetaEx.Bdd (M' ⊔ M) → (∀ m ∈ M, ∃ a : 𝓞 E, a ≠ 0 ∧ a • m ∈ M') → ∃ 𝔞 : Ideal (𝓞 E), 𝔞 ≠ ⊥ ∧ GlobalTheory.BetaEx.detSpan (M ⊓ M') = 𝔞 • GlobalTheory.BetaEx.detSpan M ∧ GlobalTheory.BetaEx.detSpan M' = 𝔞 • GlobalTheory.BetaEx.detSpan (M' ⊔ M) ∧ Ideal.absNorm 𝔞 = (M ⊓ M').toAddSubgroup.relIndex M.toAddSubgroup := by
  first | exact @GlobalTheory.BetaEx.exists_index_ideal_inf_sup | exact GlobalTheory.BetaEx.exists_index_ideal_inf_sup | (intros; apply GlobalTheory.BetaEx.exists_index_ideal_inf_sup <;> assumption)
end

section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.FrobeniusOrbits GlobalTheory.HeckeGal

namespace GlobalTheory.GalChar

theorem isTorsionFree_field (E Ω : Type) [Field E] [Field Ω] [Algebra E Ω] : Module.IsTorsionFree E Ω := inferInstance

attribute [local instance 10000] isTorsionFree_field

section Avatar

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {l : ℕ} [Fact l.Prime]
  {O : Type} [CommRing O] [IsDomain O]

def toQ (κ : FractionRing O →+* Qbar l) : O →+* Qbar l := κ.comp (algebraMap O (FractionRing O))

def inQ (κ : FractionRing O →+* Qbar l) (r : G E Ω →* Oˣ) : G E Ω →* (Qbar l)ˣ :=
  (Units.map (toQ κ).toMonoidHom).comp r

def IsGal [TopologicalSpace O] (art : Ideles E →* Gab E Ω) (κ : FractionRing O →+* Qbar l) (ι : Qbar l ≃+* ℂ)
    (χ : HChar E) (n : (E →+* ℂ) → ℤ) (r : G E Ω →* Oˣ) : Prop :=
  IsAlgPos χ n ∧ Continuous (fun g => ((r g : Oˣ) : O)) ∧ IsLAdicOf art ι χ n (inQ κ r)

def sideIso (ι : Qbar l ≃+* ℂ) (b : Bool) : Qbar l ≃+* ℂ :=
  if b then ι else ι.trans (starRingAut : ℂ ≃+* ℂ)

def block (μ η : HChar E) (r : ℕ) : HChar E := μ * (η⁻¹ * Model.absPow E (-(r : ℝ) / 2))

end Avatar

section Universal

variable {R : Ranks} (H : Formalism.BasicNotions.Host R) {Ω : Type} [Field Ω] [Algebra H.E Ω]

def delAt {e : Fin R.m → R.Psi → ℚ} (C : GlobalTheory.Mem.Chr.HFrame H e) (l : ℕ) : HChar H.E :=
  if l = H.pde then C.del' else C.del

theorem conj_conj (x : H.E) : H.conj (H.conj x) = x := by
  let φ : H.E →+* ℂ := Classical.choice inferInstance
  apply φ.injective
  have h := fun y => H.conjE_apply φ y
  exact (h _).trans ((congrArg (starRingEnd ℂ) (h x)).trans (Complex.conj_conj _))

def pair (P : PlE H) : Set (PlE H) := {v | v = P ∨ IsConjPl H P v}

variable {H}

theorem isConjPl_symm {P P' : PlE H} (h : IsConjPl H P P') : IsConjPl H P' P := fun x y e =>
  (h y x (by rw [e, conj_conj])).symm

theorem isConjPl_unique {P P' P'' : PlE H} (h : IsConjPl H P P') (h' : IsConjPl H P P'') : P' = P'' :=
  (GlobalTheory.Mem.Chr.existsUnique_conjPl H.conj.toRingEquiv P).unique
    ((GlobalTheory.Mem.Chr.conjPl_main.2.1 R H P P').1 h) ((GlobalTheory.Mem.Chr.conjPl_main.2.1 R H P P'').1 h')

theorem pair_eq {P P' : PlE H} (h : IsConjPl H P P') : pair H P' = pair H P := by
  ext v
  constructor
  · rintro (rfl | hv)
    · exact Or.inr h
    · exact Or.inl (isConjPl_unique hv (isConjPl_symm h))
  · rintro (rfl | hv)
    · exact Or.inr (isConjPl_symm h)
    · exact Or.inl (isConjPl_unique hv h)

variable (H) (cc : Ω ≃+* Ω) (l : ℕ)

def IsDel (M : ℕ) (T : Set (PlE H)) (d : G H.E Ω →* Multiplicative (ZMod (l ^ M))) : Prop :=
  IsOpen (d.ker : Set (G H.E Ω)) ∧ AntiHom cc d ∧
    (∀ v ∈ placesOver H.E l, ∀ A : ValuationSubring Ω, IsPlaceOver A v → ∀ σ ∈ Dec (F := H.E) A, d σ = 1) ∧
    (∀ v, v ∉ T → ∀ A : ValuationSubring Ω, IsPlaceOver A v → ∀ σ ∈ Ine (F := H.E) A, d σ = 1) ∧
    (∀ v, v ∈ T → ∀ A : ValuationSubring Ω, IsPlaceOver A v → ∀ c, ∃ σ ∈ Ine (F := H.E) A, d σ = c)


open Classical in
def delOf (M : ℕ) (T : Set (PlE H)) : G H.E Ω →* Multiplicative (ZMod (l ^ M)) :=
  if h : ∃ d, IsDel H cc l M T d then h.choose else 1

theorem isDel_delOf {M : ℕ} {T : Set (PlE H)} (h : ∃ d, IsDel H cc l M T d) : IsDel H cc l M T (delOf H cc l M T) := by
  rw [delOf, dite_eq_left h]
  exact h.choose_spec

theorem delOf_laws (M : ℕ) (T : Set (PlE H)) :
    IsOpen ((delOf H cc l M T).ker : Set (G H.E Ω)) ∧ AntiHom cc (delOf H cc l M T) ∧
    (∀ v ∈ placesOver H.E l, ∀ A : ValuationSubring Ω, IsPlaceOver A v → ∀ σ ∈ Dec (F := H.E) A,
      delOf H cc l M T σ = 1) ∧
    (∀ v, v ∉ T → ∀ A : ValuationSubring Ω, IsPlaceOver A v → ∀ σ ∈ Ine (F := H.E) A, delOf H cc l M T σ = 1) := by
  by_cases h : ∃ d, IsDel H cc l M T d
  · obtain ⟨h1, h2, h3, h4, -⟩ := isDel_delOf H cc l h
    exact ⟨h1, h2, h3, h4⟩
  · rw [delOf, dite_eq_right h]
    refine ⟨by simp, fun _ _ _ => by simp, fun _ _ _ _ _ _ => rfl, fun _ _ _ _ _ _ => rfl⟩


open Classical in
def delCoord (Q : Finset (PlE H)) (M : ℕ) (P : PlE H) : G H.E Ω →* Multiplicative (ZMod (l ^ M)) :=
  if pair H P ⊆ ↑Q then delOf H cc l M (pair H P) else 1

def delU (Q : Finset (PlE H)) (M : ℕ) : G H.E Ω →* Multiplicative (DelQM H l Q M) where
  toFun σ := Multiplicative.ofAdd fun P => Multiplicative.toAdd (delCoord H cc l Q M P.1 σ)
  map_one' := by simp only [map_one, toAdd_one]; rfl
  map_mul' g h := by simp only [map_mul, toAdd_mul]; rfl

theorem delU_apply (Q : Finset (PlE H)) (M : ℕ) (σ : G H.E Ω) (P : ↥Q) :
    Multiplicative.toAdd (delU H cc l Q M σ) P = Multiplicative.toAdd (delCoord H cc l Q M P.1 σ) := rfl

theorem delU_eq_one_iff (Q : Finset (PlE H)) (M : ℕ) (σ : G H.E Ω) :
    delU H cc l Q M σ = 1 ↔ ∀ P ∈ Q, delCoord H cc l Q M P σ = 1 :=
  ⟨fun h P hP => Multiplicative.toAdd.injective (congrFun (congrArg Multiplicative.toAdd h) ⟨P, hP⟩),
    fun h => Multiplicative.toAdd.injective (funext fun P => congrArg Multiplicative.toAdd (h P.1 P.2))⟩

theorem delCoord_laws (Q : Finset (PlE H)) (M : ℕ) (P : PlE H) :
    IsOpen ((delCoord H cc l Q M P).ker : Set (G H.E Ω)) ∧ AntiHom cc (delCoord H cc l Q M P) ∧
    (∀ v ∈ placesOver H.E l, ∀ A : ValuationSubring Ω, IsPlaceOver A v → ∀ σ ∈ Dec (F := H.E) A,
      delCoord H cc l Q M P σ = 1) ∧
    (∀ v, v ∉ Q → ∀ A : ValuationSubring Ω, IsPlaceOver A v → ∀ σ ∈ Ine (F := H.E) A,
      delCoord H cc l Q M P σ = 1) := by
  unfold delCoord
  split_ifs with h
  · obtain ⟨h1, h2, h3, h4⟩ := delOf_laws H cc l M (pair H P)
    exact ⟨h1, h2, h3, fun v hv => h4 v fun hm => hv (h hm)⟩
  · refine ⟨by simp, fun _ _ _ => by simp, fun _ _ _ _ _ _ => rfl, fun _ _ _ _ _ _ => rfl⟩

theorem delCoord_of_closed {Q : Finset (PlE H)} (hQ : ∀ P ∈ Q, ∀ P', IsConjPl H P P' → P' ∈ Q) (M : ℕ) {P : PlE H}
    (hP : P ∈ Q) : delCoord H cc l Q M P = delOf H cc l M (pair H P) := by
  refine if_pos ?_
  rintro v (rfl | hv)
  · exact hP
  · exact hQ P hP v hv

def UniversalAnticyclotomicCharLaws : Prop :=
  (∀ Q M v, v ∉ Q → ∀ A : ValuationSubring Ω, IsPlaceOver A v → ∀ σ ∈ Ine (F := H.E) A, delU H cc l Q M σ = 1) ∧
  (∀ Q M v, v ∈ placesOver H.E l → ∀ A : ValuationSubring Ω, IsPlaceOver A v →
    ∀ σ ∈ Dec (F := H.E) A, delU H cc l Q M σ = 1) ∧
  (∀ Q M, AntiHom cc (delU H cc l Q M)) ∧
  (∀ (Q : Finset (PlE H)) (M : ℕ), IsOpen ((delU H cc l Q M).ker : Set (G H.E Ω))) ∧
  (∀ (M : ℕ) (Q' Q : Finset (PlE H)) (h : Q' ⊆ Q),
    (∀ P ∈ Q', ∀ P', IsConjPl H P P' → P' ∈ Q') → (∀ P ∈ Q, ∀ P', IsConjPl H P P' → P' ∈ Q) →
    ∀ (σ : G H.E Ω) (P : PlE H) (hP : P ∈ Q'),
      Multiplicative.toAdd (delU H cc l Q' M σ) ⟨P, hP⟩ = Multiplicative.toAdd (delU H cc l Q M σ) ⟨P, h hP⟩) ∧
  (∀ (Q : Finset (PlE H)) (M : ℕ) (P : PlE H) (hP : P ∈ Q) (P' : PlE H) (hP' : P' ∈ Q),
    IsConjPl H P P' → ∃ s : ℤˣ, ∀ σ : G H.E Ω,
      Multiplicative.toAdd (delU H cc l Q M σ) ⟨P', hP'⟩ =
        ((s : ℤ) : ZMod (l ^ M)) * Multiplicative.toAdd (delU H cc l Q M σ) ⟨P, hP⟩) ∧
  (∀ (Q : Finset (PlE H)) (M : ℕ), (∀ P ∈ Q, ∀ P', IsConjPl H P P' → P' ∈ Q) → ∀ (P : PlE H) (hP : P ∈ Q) (σ : G H.E Ω),
    Multiplicative.toAdd (delU H cc l Q M σ) ⟨P, hP⟩ = Multiplicative.toAdd (delOf H cc l M (pair H P) σ)) ∧
  ∀ (M : ℕ) (P : PlE H), (∃ d, IsDel H cc l M (pair H P) d) → IsDel H cc l M (pair H P) (delOf H cc l M (pair H P))

theorem universal_anticyclotomic_character_laws : UniversalAnticyclotomicCharLaws H cc l := by
  refine ⟨fun Q M v hv A hA σ hσ => ?_, fun Q M v hv A hA σ hσ => ?_, fun Q M g g' h => ?_, fun Q M => ?_,
    fun M Q' Q h h1 h2 σ P hP => ?_, fun Q M P hP P' hP' h => ⟨1, fun σ => ?_⟩, fun Q M hQ P hP σ => ?_,
    fun M P h => isDel_delOf H cc l h⟩
  · exact (delU_eq_one_iff H cc l Q M σ).2 fun P _ => (delCoord_laws H cc l Q M P).2.2.2 v hv A hA σ hσ
  · exact (delU_eq_one_iff H cc l Q M σ).2 fun P _ => (delCoord_laws H cc l Q M P).2.2.1 v hv A hA σ hσ
  · exact Multiplicative.toAdd.injective (funext fun P =>
      congrArg Multiplicative.toAdd ((delCoord_laws H cc l Q M P.1).2.1 g g' h))
  · have e : ((delU H cc l Q M).ker : Set (G H.E Ω)) = ⋂ P ∈ Q, ((delCoord H cc l Q M P).ker : Set (G H.E Ω)) := by
      ext σ
      simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_iInter, delU_eq_one_iff]
    rw [e]
    exact isOpen_biInter_finset fun P _ => (delCoord_laws H cc l Q M P).1
  · rw [delU_apply, delU_apply, delCoord_of_closed H cc l h1 M hP, delCoord_of_closed H cc l h2 M (h hP)]
  · rw [delU_apply, delU_apply]
    have e : delCoord H cc l Q M P' = delCoord H cc l Q M P := by
      unfold delCoord
      rw [pair_eq h]
    simp only [e, Units.val_one, Int.cast_one, one_mul]
  · rw [delU_apply, delCoord_of_closed H cc l hQ M hP]

end Universal

theorem delUTie_of_exists {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}
    (Y : NExp D.R D.host D.what₂ D.LL0 N X) (hY : ∀ i Q M, Y.delU i Q M = delU D.host X.cc (X.l i) Q M)
    (h : GlobalTheory.TwSys.K1 X) : GlobalTheory.TwSys.DelUTie Y := by
  intro i M _ hM
  obtain ⟨H', S, d, h1, h2, h3, h4⟩ := h i M hM
  refine ⟨H', S, fun P => delOf D.host X.cc (X.l i) M (pair D.host P), ⟨h1, h2, h3, fun P a b c => ?_⟩,
    fun Q hQ P hP σ => ?_⟩
  · exact isDel_delOf D.host X.cc (X.l i) ⟨d P, h4 P a b c⟩
  · rw [hY]
    exact (universal_anticyclotomic_character_laws D.host X.cc (X.l i)).2.2.2.2.2.2.1 Q M hQ P hP σ

end GlobalTheory.GalChar

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial Formalism.UG GlobalTheory.SatInd

theorem _root_.GlobalTheory.T.finite_inertHecke_support_cosets : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w), (∀ s : GU Dv.σw n, Set.Finite {c : GU Dv.σw n ⧸ KU Dv.σw n | ∃ a ∈ KU Dv.σw n, ((a * s : GU Dv.σw n) : GU Dv.σw n ⧸ KU Dv.σw n) = c}) → (∀ z : GAf L n, TrivOutside {v} z → (∀ i j, ((Dv.loc z : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) (w.adicCompletion L)) i j ∈ intL (w.adicCompletion L)) → z ∈ Umax L n) → ∀ (U : Subgroup (GAf L n)), (∀ κ, TrivOutside {v} κ → (κ ∈ U ↔ κ ∈ Umax L n)) → ∀ h ∈ Hecke ℂ (KU Dv.σw n), Set.Finite {c : GAf L n ⧸ U | ∃ x : GAf L n, (x : GAf L n ⧸ U) = c ∧ TrivOutside {v} x ∧ Dv.hval h (Dv.loc x) ≠ 0} := by
  first | exact @GlobalTheory.SatInd.CosetFin.finite_inert_support | exact GlobalTheory.SatInd.CosetFin.finite_inert_support | (intros; apply GlobalTheory.SatInd.CosetFin.finite_inert_support <;> assumption)
end
