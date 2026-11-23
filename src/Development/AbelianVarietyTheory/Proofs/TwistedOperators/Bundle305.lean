module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittHyperbolicAnisotropicCommuteLevi
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.GinfCSecondCountable
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle331
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle277
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle290
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle136
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle010
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1610
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle162
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.MixModel GlobalTheory.MixPer
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section




namespace GlobalTheory.HaarCoords

theorem transl_nC : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (μ : Measure (UX D ρ)) (lB : Measure (Mx D ρ S₀.rank)) (lC : Measure (skewA D ρ)), μ.IsHaarMeasure → lB.IsAddHaarMeasure → lC.IsAddHaarMeasure → SFinite μ → SFinite lB → SFinite lC → ∀ c' : skewA D ρ, ∃ T : UX D ρ × (Mx D ρ S₀.rank × skewA D ρ) → UX D ρ × (Mx D ρ S₀.rank × skewA D ρ), MeasurePreserving T (μ.prod (lB.prod lC)) (μ.prod (lB.prod lC)) ∧ ∀ p, d.levi (T p).1.1 * (d.nB (T p).2.1 * d.nC (T p).2.2) = d.nC c' * (d.levi p.1.1 * (d.nB p.2.1 * d.nC p.2.2)) := by
  intro D S S₀ ρ d μ lB lC _ _ hC _ _ _ c'
  haveI : BorelSpace (Mx D ρ ρ) := ⟨rfl⟩
  haveI : BorelSpace (Mx D ρ S₀.rank) := ⟨rfl⟩
  haveI : BorelSpace (UX D ρ) := ⟨rfl⟩
  obtain ⟨i1, -, i3, -⟩ := lattice_Mx D ρ ρ
  haveI : SecondCountableTopology (Mx D ρ ρ) := i3
  haveI : BorelSpace (skewA D ρ) := Subtype.borelSpace _
  haveI : SecondCountableTopology (skewA D ρ) := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  haveI : MeasurableAdd₂ (skewA D ρ) := inferInstance
  haveI : MeasurableAdd (skewA D ρ) := inferInstance
  let s : UX D ρ → skewA D ρ := fun u => skewConj (u⁻¹).1.1 c'
  have hinv : Continuous fun u : UX D ρ => (u⁻¹).1.1 := Units.continuous_coe_inv.comp continuous_subtype_val
  have hs : Continuous s := by
    refine Continuous.subtype_mk ?_ _
    exact (hinv.matrix_mul continuous_const).matrix_mul (continuous_adj.comp hinv)
  refine ⟨fun p => (p.1, (p.2.1, s p.1 + p.2.2)), ?_, ?_⟩
  · have hg : Measurable (Function.uncurry fun (u : UX D ρ) (q : Mx D ρ S₀.rank × skewA D ρ) => (q.1, s u + q.2)) :=
      measurable_snd.fst.prodMk ((hs.measurable.comp measurable_fst).add measurable_snd.snd)
    exact (MeasurePreserving.id μ).skew_product hg
      (Filter.Eventually.of_forall fun u => ((MeasurePreserving.id lB).prod (measurePreserving_add_left lC (s u))).map_eq)
  · rintro ⟨u, b, c⟩
    have h := d.levi_mul_nC c' (u⁻¹).1
    have hL : d.levi (u⁻¹).1 = (d.levi u.1)⁻¹ := by rw [Subgroup.coe_inv, map_inv]
    rw [hL] at h
    have h2 : d.nC c' * d.levi u.1 = d.levi u.1 * d.nC (s u) := by
      calc d.nC c' * d.levi u.1 = d.levi u.1 * ((d.levi u.1)⁻¹ * d.nC c') * d.levi u.1 := by rw [mul_inv_cancel_left]
        _ = d.levi u.1 * (d.nC (s u) * (d.levi u.1)⁻¹) * d.levi u.1 := by rw [h]
        _ = d.levi u.1 * d.nC (s u) := by rw [← mul_assoc (d.levi u.1), inv_mul_cancel_right]
    show d.levi u.1 * (d.nB b * d.nC (s u + c)) = d.nC c' * (d.levi u.1 * (d.nB b * d.nC c))
    rw [d.nC_add, ← mul_assoc (d.nC c'), h2, mul_assoc, ← mul_assoc (d.nC (s u)), d.nC_mul_nB, mul_assoc]

end GlobalTheory.HaarCoords
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.MixModel GlobalTheory.MixPer
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section




namespace GlobalTheory.HaarCoords

theorem transl_nB_preserves : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (μ : Measure (UX D ρ)) (lB : Measure (Mx D ρ S₀.rank)) (lC : Measure (skewA D ρ)), μ.IsHaarMeasure → lB.IsAddHaarMeasure → lC.IsAddHaarMeasure → SFinite μ → SFinite lB → SFinite lC → ∀ b' : Mx D ρ S₀.rank, ∃ T : UX D ρ × (Mx D ρ S₀.rank × skewA D ρ) → UX D ρ × (Mx D ρ S₀.rank × skewA D ρ), MeasurePreserving T (μ.prod (lB.prod lC)) (μ.prod (lB.prod lC)) ∧ ∀ p, d.levi (T p).1.1 * (d.nB (T p).2.1 * d.nC (T p).2.2) = d.nB b' * (d.levi p.1.1 * (d.nB p.2.1 * d.nC p.2.2)) := by
  intro D S S₀ ρ d μ lB lC hμ hB hC _ _ _ b'
  obtain ⟨hTR, _, _, hSC, hBor⟩ := Formalism.IndefR.Eqv.ae_facts D
  haveI := hμ; haveI := hB; haveI := hC; haveI := hTR; haveI := hSC; haveI := hBor
  haveI hMxB : ∀ m n : ℕ, BorelSpace (Mx D m n) := fun _ _ => ⟨rfl⟩
  haveI hMxS : ∀ m n : ℕ, SecondCountableTopology (Mx D m n) := fun m n =>
    inferInstanceAs (SecondCountableTopology (Fin m → Fin n → AE D))
  haveI : BorelSpace (UX D ρ) := ⟨rfl⟩

  let v : UX D ρ → Mx D ρ S₀.rank := fun u => ((u.1)⁻¹ : GL (Fin ρ) (AE D)).1 ⬝ b'
  refine ⟨fun p => (p.1, (v p.1 + p.2.1, cComm S₀ (v p.1) p.2.1 + p.2.2)), ?_, ?_⟩
  · have hvm : Measurable v := by
      have hinv : Continuous fun u : UX D ρ => (((u.1)⁻¹ : GL (Fin ρ) (AE D)) : Matrix (Fin ρ) (Fin ρ) (AE D)) :=
        Units.continuous_coe_inv.comp continuous_subtype_val
      exact (hinv.matrix_mul continuous_const).measurable

    have hplus : Continuous fun b : Mx D ρ S₀.rank => plus S₀ b := by
      show Continuous fun b : Mx D ρ S₀.rank => giA S₀ ⬝ adj b
      exact continuous_const.matrix_mul continuous_adj
    have hΦ : Measurable fun q : Mx D ρ S₀.rank × Mx D ρ S₀.rank => ((cComm S₀ q.1 q.2 : skewA D ρ) : Mx D ρ ρ) := by
      have h1 : Continuous fun q : Mx D ρ S₀.rank × Mx D ρ S₀.rank => q.2 ⬝ plus S₀ q.1 :=
        continuous_snd.matrix_mul (hplus.comp continuous_fst)
      have h2 : Continuous fun q : Mx D ρ S₀.rank × Mx D ρ S₀.rank => q.1 ⬝ plus S₀ q.2 :=
        continuous_fst.matrix_mul (hplus.comp continuous_snd)
      have hc : Continuous fun q : Mx D ρ S₀.rank × Mx D ρ S₀.rank =>
          half D • (q.2 ⬝ plus S₀ q.1 - q.1 ⬝ plus S₀ q.2) :=
        (continuous_const_smul (half D)).comp (h1.sub h2)
      exact hc.measurable
    have hg : Measurable fun p : UX D ρ × (Mx D ρ S₀.rank × skewA D ρ) =>
        ((v p.1 + p.2.1, cComm S₀ (v p.1) p.2.1 + p.2.2) : Mx D ρ S₀.rank × skewA D ρ) := by
      refine ((hvm.comp measurable_fst).add (measurable_fst.comp measurable_snd)).prodMk ?_
      exact Measurable.subtype_mk (f := fun p : UX D ρ × (Mx D ρ S₀.rank × skewA D ρ) =>
          ((cComm S₀ (v p.1) p.2.1 : skewA D ρ) : Mx D ρ ρ) + (p.2.2 : Mx D ρ ρ))
        (h := fun p => (cComm S₀ (v p.1) p.2.1 + p.2.2).2)
        ((hΦ.comp ((hvm.comp measurable_fst).prodMk (measurable_fst.comp measurable_snd))).add
          (measurable_subtype_coe.comp (measurable_snd.comp measurable_snd)))
    have hfib : ∀ u : UX D ρ, Measure.map (fun q : Mx D ρ S₀.rank × skewA D ρ =>
        ((v u + q.1, cComm S₀ (v u) q.1 + q.2) : Mx D ρ S₀.rank × skewA D ρ)) (lB.prod lC) = lB.prod lC := by
      intro u
      have hk : Measurable fun q : Mx D ρ S₀.rank × skewA D ρ => (cComm S₀ (v u) q.1 + q.2 : skewA D ρ) :=
        Measurable.subtype_mk (f := fun q : Mx D ρ S₀.rank × skewA D ρ =>
            ((cComm S₀ (v u) q.1 : skewA D ρ) : Mx D ρ ρ) + (q.2 : Mx D ρ ρ))
          (h := fun q => (cComm S₀ (v u) q.1 + q.2).2)
          ((hΦ.comp (measurable_const.prodMk measurable_fst)).add (measurable_subtype_coe.comp measurable_snd))
      exact ((measurePreserving_add_left lB (v u)).skew_product (g := fun b (c : skewA D ρ) => cComm S₀ (v u) b + c) hk
        (Filter.Eventually.of_forall fun b => map_add_left_eq_self lC _)).map_eq
    exact (MeasurePreserving.id μ).skew_product
      (g := fun (u : UX D ρ) (q : Mx D ρ S₀.rank × skewA D ρ) => ((v u + q.1, cComm S₀ (v u) q.1 + q.2) : Mx D ρ S₀.rank × skewA D ρ))
      hg (Filter.Eventually.of_forall hfib)
  · rintro ⟨u, b, c⟩
    show d.levi u.1 * (d.nB (v u + b) * d.nC (cComm S₀ (v u) b + c)) = d.nB b' * (d.levi u.1 * (d.nB b * d.nC c))
    have hv : u.1.1 ⬝ v u = b' := by
      show u.1.1 ⬝ (((u.1)⁻¹ : GL (Fin ρ) (AE D)).1 ⬝ b') = b'
      rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
    rw [d.nC_add, ← mul_assoc (d.nB _), ← d.nB_mul_nB, ← mul_assoc, ← mul_assoc, d.levi_mul_nB, hv, mul_assoc, mul_assoc]

end GlobalTheory.HaarCoords
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.MixModel GlobalTheory.MixPer
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BesProj

variable {D : D7} {S S₀ A L : HSp D} {ρ : ℕ}

theorem mt_emb_one (o : OrthDec S₀ A L) : mt S₀ (o.emb (1, 1)) = 1 := by
  rw [show ((1 : GA D A), (1 : GA D L)) = 1 from rfl, map_one, mt_one]

theorem mt_emb_mul (o : OrthDec S₀ A L) (h h' : GA D A) :
    mt S₀ (o.emb (h * h', 1)) = mt S₀ (o.emb (h, 1)) * mt S₀ (o.emb (h', 1)) := by
  rw [← mt_mul, ← map_mul, Prod.mk_mul_mk, mul_one]

def Good (d : HypDec S S₀ ρ) (o : OrthDec S₀ A L) (T : Subgroup (GA D A)) (g : GA D S) : Prop :=
  (∃ M : GL (Fin ρ) (AE D), mt S g * d.jX = d.jX * M.1) ∧
    ∃ h ∈ T, ∃ B : Mx D ρ S₀.rank, mt S g * d.j0 = d.j0 * mt S₀ (o.emb (h, 1)) + d.jX * B

section Good

variable (d : HypDec S S₀ ρ) (o : OrthDec S₀ A L) (T : Subgroup (GA D A))

theorem good_one : Good d o T 1 :=
  ⟨⟨1, by rw [mt_one, Matrix.one_mul, Units.val_one, Matrix.mul_one]⟩,
    1, T.one_mem, 0, by rw [mt_one, Matrix.one_mul, mt_emb_one, Matrix.mul_one, Matrix.mul_zero, add_zero]⟩

theorem good_mul {g g' : GA D S} (hg : Good d o T g) (hg' : Good d o T g') : Good d o T (g * g') := by
  obtain ⟨⟨M, hM⟩, h, hT, B, hB⟩ := hg
  obtain ⟨⟨M', hM'⟩, h', hT', B', hB'⟩ := hg'
  refine ⟨⟨M * M', ?_⟩, h * h', T.mul_mem hT hT', B * mt S₀ (o.emb (h', 1)) + M.1 * B', ?_⟩
  · rw [mt_mul, Matrix.mul_assoc, hM', ← Matrix.mul_assoc, hM, Matrix.mul_assoc, Units.val_mul]
  · rw [mt_mul, Matrix.mul_assoc, hB', Matrix.mul_add, ← Matrix.mul_assoc, hB, ← Matrix.mul_assoc, hM, mt_emb_mul]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, add_assoc]

theorem good_inv {g : GA D S} (hg : Good d o T g) : Good d o T g⁻¹ := by
  obtain ⟨⟨M, hM⟩, h, hT, B, hB⟩ := hg
  have hI : mt S g⁻¹ * mt S g = 1 := mt_inv_mul S g
  have hMM : (M.1 : Mx D ρ ρ) * (M⁻¹).1 = 1 := M.mul_inv
  have hX : mt S g⁻¹ * d.jX = d.jX * (M⁻¹).1 := by
    calc mt S g⁻¹ * d.jX = mt S g⁻¹ * (d.jX * M.1) * (M⁻¹).1 := by
          rw [Matrix.mul_assoc (mt S g⁻¹), Matrix.mul_assoc d.jX, hMM, Matrix.mul_one]
      _ = d.jX * (M⁻¹).1 := by rw [← hM, ← Matrix.mul_assoc, hI, Matrix.one_mul]
  refine ⟨⟨M⁻¹, hX⟩, h⁻¹, T.inv_mem hT, -((M⁻¹).1 * B * mt S₀ (o.emb (h⁻¹, 1))), ?_⟩
  have hH : mt S₀ (o.emb (h, 1)) * mt S₀ (o.emb (h⁻¹, 1)) = 1 := by
    rw [← mt_emb_mul, mul_inv_cancel, mt_emb_one]
  have h1 : mt S g⁻¹ * d.j0 * mt S₀ (o.emb (h, 1)) + d.jX * (M⁻¹).1 * B = d.j0 := by
    have h2 : mt S g⁻¹ * (mt S g * d.j0) = d.j0 := by rw [← Matrix.mul_assoc, hI, Matrix.one_mul]
    rw [hB, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hX] at h2
    exact h2
  calc mt S g⁻¹ * d.j0 = mt S g⁻¹ * d.j0 * mt S₀ (o.emb (h, 1)) * mt S₀ (o.emb (h⁻¹, 1)) := by
        rw [Matrix.mul_assoc _ (mt S₀ _), hH, Matrix.mul_one]
    _ = (d.j0 - d.jX * (M⁻¹).1 * B) * mt S₀ (o.emb (h⁻¹, 1)) := by rw [eq_sub_of_add_eq h1]
    _ = _ := by simp only [Matrix.sub_mul, Matrix.add_mul, Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc, sub_eq_add_neg]

def goodSub : Subgroup (GA D S) where
  carrier := {g | Good d o T g}
  one_mem' := good_one d o T
  mul_mem' := fun {g g'} hg hg' => good_mul d o T (g := g) (g' := g') hg hg'
  inv_mem' := fun {g} hg => good_inv d o T (g := g) hg

end Good

end GlobalTheory.BesProj

namespace GlobalTheory.BesProj

variable {D : D7} {S S₀ A L : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (o : OrthDec S₀ A L)

theorem eH_gram_i₀ : d.eᴴ * S.gram * d.i₀ = 0 := by
  have := congrArg Matrix.conjTranspose d.i₀e
  rwa [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, gram_conjTranspose, conjTranspose_zero,
    ← Matrix.mul_assoc] at this

theorem flagN_le_goodSub (T : Subgroup (GA D A)) : flagN d ≤ goodSub d o T := by
  show Subgroup.closure _ ≤ _
  refine (Subgroup.closure_le _).2 ?_
  rintro g ⟨h1, h2⟩
  choose a ha1 ha2 using h1
  have hz : ∀ k : Fin S₀.rank, (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) d.e * S.gram).mulVec
      (fun l => d.i₀ l k) = 0 := by
    intro k; funext j
    exact congrFun (congrFun (eH_gram_i₀ d) j) k
  choose b hb using fun k => h2 _ (hz k)
  let U : Mx D ρ ρ := Matrix.of fun j i => a i j
  let B : Mx D ρ S₀.rank := Matrix.of fun i k => b k i
  have hU : (mt S g - 1) * d.jX = d.jX * U := by
    ext k i
    exact congrFun (ha2 i) k
  have hB : (mt S g - 1) * d.j0 = d.jX * B := by
    ext k i
    exact congrFun (hb i) k
  have hdet : (1 + U).det = 1 := by
    rw [Matrix.det_of_upperTriangular]
    · refine Finset.prod_eq_one fun i _ => ?_
      simp [U, ha1 i i le_rfl]
    · intro i j hji
      have hij : i ≠ j := ne_of_gt hji
      simp [U, ha1 j i hji.le, Matrix.one_apply_ne hij]
  have hdu : IsUnit (1 + U).det := by rw [hdet]; exact isUnit_one
  let M : GL (Fin ρ) (AE D) := ⟨1 + U, (1 + U)⁻¹, Matrix.mul_nonsing_inv _ hdu, Matrix.nonsing_inv_mul _ hdu⟩
  refine ⟨⟨M, ?_⟩, 1, T.one_mem, B, ?_⟩
  · show mt S g * d.jX = d.jX * (1 + U)
    rw [Matrix.mul_add, Matrix.mul_one, ← hU, Matrix.sub_mul, Matrix.one_mul, add_sub_cancel]
  · rw [mt_emb_one, Matrix.mul_one, ← hB, Matrix.sub_mul, Matrix.one_mul, add_sub_cancel]

theorem embA_mem_goodSub (h : GA D A) : embA d o h ∈ goodSub d o ⊤ :=
  ⟨⟨1, by rw [embA_apply, d.wittDecomp_anisotropicEmbedding_inclX, Units.val_one, Matrix.mul_one]⟩, h, Subgroup.mem_top h, 0,
    by rw [embA_apply, d.wittDecomp_anisotropicEmbedding_inclAnisotropic, Matrix.mul_zero, add_zero]⟩

theorem besGrp_le_goodSub : (flagN d ⊔ (embA d o).range : Subgroup (GA D S)) ≤ goodSub d o ⊤ :=
  sup_le (flagN_le_goodSub d o ⊤) (by rintro _ ⟨h, rfl⟩; exact embA_mem_goodSub d o h)

def matP (g : GA D S) : Mx D A.rank A.rank := o.pA * (d.p0 * mt S g * d.j0) * o.jA

theorem bessel_flag_stabilizer_anisotropic_block_exists {T : Subgroup (GA D A)} {g : GA D S} (hg : g ∈ goodSub d o T) :
    ∃ h ∈ T, d.p0 * mt S g * d.j0 = mt S₀ (o.emb (h, 1)) := by
  obtain ⟨-, h, hT, B, hB⟩ := hg
  refine ⟨h, hT, ?_⟩
  rw [Matrix.mul_assoc, hB, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, d.p0_j0, d.p0_jX, Matrix.one_mul,
    Matrix.zero_mul, add_zero]

theorem pA_emb_jA (h : GA D A) : o.pA * mt S₀ (o.emb (h, 1)) * o.jA = mt A h := by
  rw [Matrix.mul_assoc, o.emb_jA, ← Matrix.mul_assoc, o.pA_jA, Matrix.one_mul]

theorem anisotropicBlock_unitary {g : GA D S} (hg : g ∈ (flagN d ⊔ (embA d o).range : Subgroup (GA D S))) :
    adj (matP d o g) * (gA A * matP d o g) = gA A := by
  obtain ⟨h, -, hh⟩ := bessel_flag_stabilizer_anisotropic_block_exists d o (besGrp_le_goodSub d o hg)
  rw [matP, hh, pA_emb_jA]
  exact mt_unitary A h

theorem anisotropicBlock_mul_embA (n : flagN d) (h : GA D A) : matP d o (n.1 * embA d o h) = mt A h := by
  obtain ⟨h', hh', hn⟩ := bessel_flag_stabilizer_anisotropic_block_exists d o (flagN_le_goodSub d o ⊥ n.2)
  rw [Subgroup.mem_bot] at hh'
  rw [hh', mt_emb_one] at hn
  have : d.p0 * mt S (n.1 * embA d o h) * d.j0 = mt S₀ (o.emb (h, 1)) := by
    rw [mt_mul, Matrix.mul_assoc, Matrix.mul_assoc, embA_apply, d.wittDecomp_anisotropicEmbedding_inclAnisotropic, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hn,
      Matrix.one_mul]
  rw [matP, this, pA_emb_jA]

theorem exists_continuous_proj : ∀ (D : D7) (S S₀ A L : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (o : OrthDec S₀ A L),
    ∃ p : (flagN d ⊔ (embA d o).range : Subgroup (GA D S)) → GA D A, Continuous p ∧
      ∀ (h : GA D A) (n : flagN d), p ⟨n.1 * embA d o h, mul_mem (Subgroup.mem_sup_left n.2)
        (Subgroup.mem_sup_right ⟨h, rfl⟩)⟩ = h := by
  intro D S S₀ A L ρ d o
  refine ⟨fun g => ofMat A (matP d o g.1) (anisotropicBlock_unitary d o g.2), ?_, fun h n => ?_⟩
  · refine continuous_of_mt A ?_
    show Continuous fun g : (flagN d ⊔ (embA d o).range : Subgroup (GA D S)) => matP d o g.1
    exact (continuous_const.matrix_mul ((continuous_const.matrix_mul ((continuous_mt S).comp continuous_subtype_val)).matrix_mul
      continuous_const)).matrix_mul continuous_const
  · exact mt_injective A (by rw [mt_ofMat]; exact anisotropicBlock_mul_embA d o n h)

end GlobalTheory.BesProj
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.MixModel GlobalTheory.MixPer
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MixPer

theorem exists_mul_of_mem_sup_range {G H : Type} [Group G] [Group H] (N : Subgroup G) (s : H →* G)
    (hnorm : ∀ n ∈ N, ∀ h, s h * n * (s h)⁻¹ ∈ N) {g : G} (hg : g ∈ N ⊔ s.range) :
    ∃ n ∈ N, ∃ h, g = n * s h := by
  let K : Subgroup G :=
    { carrier := {x | ∃ n ∈ N, ∃ h, x = n * s h}
      one_mem' := ⟨1, N.one_mem, 1, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨n₁, hn₁, h₁, rfl⟩ ⟨n₂, hn₂, h₂, rfl⟩
        refine ⟨n₁ * (s h₁ * n₂ * (s h₁)⁻¹), N.mul_mem hn₁ (hnorm n₂ hn₂ h₁), h₁ * h₂, ?_⟩
        rw [map_mul]
        group
      inv_mem' := by
        rintro _ ⟨n, hn, h, rfl⟩
        refine ⟨s h⁻¹ * n⁻¹ * (s h⁻¹)⁻¹, hnorm n⁻¹ (N.inv_mem hn) h⁻¹, h⁻¹, ?_⟩
        rw [map_inv]
        group }
  have hle : N ⊔ s.range ≤ K := by
    refine sup_le (fun n hn => ⟨n, hn, 1, by simp⟩) ?_
    rintro _ ⟨h, rfl⟩
    exact ⟨1, N.one_mem, h, by simp⟩
  exact hle hg

theorem semiMeas_finite_on_compacts_and_open_pos : ∀ {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [T2Space H] [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H] (N : Subgroup G) (s : H →* G), IsClosed (N : Set G) → Continuous s → (∀ n ∈ N, ∀ h, s h * n * (s h)⁻¹ ∈ N) → (∃ p : (N ⊔ s.range : Subgroup G) → H, Continuous p ∧ ∀ (h : H) (n : N), p ⟨n.1 * s h, mul_mem (Subgroup.mem_sup_left n.2) (Subgroup.mem_sup_right ⟨h, rfl⟩)⟩ = h) → ∀ (μ : Measure H) (ν : Measure N), μ.IsHaarMeasure → ν.IsHaarMeasure → (∀ h, ν.map (fun n : N => s h * n.1 * (s h)⁻¹) = ν.map Subtype.val) → IsFiniteMeasureOnCompacts (semiMeas N s μ ν) ∧ (semiMeas N s μ ν).IsOpenPosMeasure := by
  intro G H _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ N s hN hs hnorm hp μ ν hμ hν _
  obtain ⟨p, hpc, hps⟩ := hp
  haveI : LocallyCompactSpace N := hN.locallyCompactSpace
  haveI : SecondCountableTopology N := inferInstanceAs (SecondCountableTopology (N : Set G))
  haveI : IsFiniteMeasureOnCompacts ν := inferInstance
  haveI : IsLocallyFiniteMeasure ν := isLocallyFiniteMeasure_of_isFiniteMeasureOnCompacts
  haveI : SigmaFinite ν := sigmaFinite_of_locallyFinite
  haveI : μ.IsOpenPosMeasure := inferInstance
  haveI : ν.IsOpenPosMeasure := inferInstance
  haveI : (μ.prod ν).IsOpenPosMeasure := inferInstance

  let φ : H × N → (N ⊔ s.range : Subgroup G) := fun q =>
    ⟨q.2.1 * s q.1, mul_mem (Subgroup.mem_sup_left q.2.2) (Subgroup.mem_sup_right ⟨q.1, rfl⟩)⟩
  have hφc : Continuous φ :=
    ((continuous_subtype_val.comp continuous_snd).mul (hs.comp continuous_fst)).subtype_mk _
  have hmemN : ∀ k : (N ⊔ s.range : Subgroup G), (k : G) * (s (p k))⁻¹ ∈ N := by
    intro k
    obtain ⟨n, hn, h, hk⟩ := exists_mul_of_mem_sup_range N s hnorm k.2
    have hpk : p k = h := by
      have hk' : k = ⟨n * s h, mul_mem (Subgroup.mem_sup_left hn) (Subgroup.mem_sup_right ⟨h, rfl⟩)⟩ :=
        Subtype.ext hk
      rw [hk']
      exact hps h ⟨n, hn⟩
    rw [hpk, hk, mul_inv_cancel_right]
    exact hn
  let ψ : (N ⊔ s.range : Subgroup G) → H × N := fun k => (p k, ⟨(k : G) * (s (p k))⁻¹, hmemN k⟩)
  have hψc : Continuous ψ :=
    hpc.prodMk ((continuous_subtype_val.mul (hs.comp hpc).inv).subtype_mk _)
  have hψφ : ∀ q, ψ (φ q) = q := by
    rintro ⟨h, n⟩
    have h1 : p (φ (h, n)) = h := hps h n
    refine Prod.ext h1 (Subtype.ext ?_)
    show (n : G) * s h * (s (p (φ (h, n))))⁻¹ = n
    rw [h1, mul_inv_cancel_right]
  have hφψ : ∀ k, φ (ψ k) = k := by
    intro k
    apply Subtype.ext
    show (k : G) * (s (p k))⁻¹ * s (p k) = k
    rw [inv_mul_cancel_right]
  have hsurj : Function.Surjective φ := fun k => ⟨ψ k, hφψ k⟩
  show IsFiniteMeasureOnCompacts ((μ.prod ν).map φ) ∧ ((μ.prod ν).map φ).IsOpenPosMeasure
  refine ⟨⟨fun C hC => ?_⟩, hφc.isOpenPosMeasure_map hsurj⟩
  rw [Measure.map_apply hφc.measurable hC.measurableSet]
  refine lt_of_le_of_lt (measure_mono ?_) (hC.image hψc).measure_lt_top
  intro q hq
  exact ⟨φ q, hq, hψφ q⟩

end GlobalTheory.MixPer
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlaceTensor

theorem idem_eq_locIdem (D : D7) (p : Place D) : idem D p = GlobalTheory.LocWeil.idem D p := by
  rcases p with v | τ
  · rw [GlobalTheory.LocWeil.PlaceIdem.idem_inl]
    rfl
  · rw [GlobalTheory.LocWeil.PlaceIdem.idem_inr]
    simp only [idem, GlobalTheory.LocWeil.PlaceIdem.eInf]
    congr 2

theorem idem_spec : ∀ D : D7, (∀ p, idem D p * idem D p = idem D p) ∧ (∀ p q, p ≠ q → idem D p * idem D q = 0) ∧ (∀ p, cA D (idem D p) = idem D p) ∧ (∀ v : FinPl D, infPart D (idem D (.inl v)) = 0 ∧ finPart D (idem D (.inl v)) ∈ intAE D ∧ IsPlaceIdem D v (pairA D.host.F 0 (singleV D.host.F v 1))) ∧ (∀ τ : D.what₂.Tau, finPart D (idem D (.inr τ)) = 0) ∧ infPart D (∑ τ : D.what₂.Tau, idem D (.inr τ)) = 1 ∧ ∀ θ : InfFam D, IsInfFam θ → ∀ τ : D.what₂.Tau, θ τ (infPart D (idem D (.inr τ))) = 1 ∧ ∀ τ' : D.what₂.Tau, τ' ≠ τ → θ τ (infPart D (idem D (.inr τ'))) = 0 := by
  intro D
  have hE : ∀ p, idem D p = GlobalTheory.LocWeil.idem D p := idem_eq_locIdem D
  obtain ⟨hOrth, hTheta, hFinInf, hSum, -, -⟩ := GlobalTheory.LocWeil.PlaceIdem.idem_props D
  simp only [hE]
  refine ⟨fun p => GlobalTheory.LocWeil.idem_mul_self p, fun p q hpq => hOrth p q hpq, fun p => GlobalTheory.LocWeil.cA_idem p,
    ?_, hFinInf, hSum, ?_⟩
  · intro v
    rw [GlobalTheory.LocWeil.PlaceIdem.idem_inl, GlobalTheory.LocWeil.PlaceIdem.infPart_algebraMap,
      GlobalTheory.LocWeil.PlaceIdem.finPart_algebraMap]
    refine ⟨?_, ?_, ⟨singleV D.host.F v 1, rfl, GlobalTheory.LocWeil.PlaceIdem.evalV_single_same _ v,
      fun v' h => GlobalTheory.LocWeil.PlaceIdem.evalV_single_ne _ h⟩⟩
    · exact TensorProduct.zero_tmul _ _
    · apply AddSubgroup.subset_closure
      refine ⟨singleV D.host.F v 1, ?_, 1, ?_⟩
      · simp only [intAf, Set.mem_setOf_eq]
        intro u
        rcases eq_or_ne u v with rfl | h
        · rw [GlobalTheory.LocWeil.PlaceIdem.evalV_single_same]
          exact one_mem _
        · rw [GlobalTheory.LocWeil.PlaceIdem.evalV_single_ne _ h]
          exact zero_mem _
      · rfl
  · intro θ hθ τ
    refine ⟨?_, fun τ' h => ?_⟩
    · rw [hTheta θ hθ τ τ, if_pos rfl]
    · rw [hTheta θ hθ τ' τ, if_neg (Ne.symm h)]

end GlobalTheory.PlaceTensor
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.relIndex_integralMatrices_diagonal_uniformizer_pow : ∀ {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (Q : ℕ), ϖ ≠ 0 → Valued.v ϖ ≤ 1 → (∀ e : ℕ, ((Formalism.UG.intL L).toAddSubgroup.map (AddMonoidHom.mulLeft (ϖ ^ e))).relIndex (Formalism.UG.intL L).toAddSubgroup = Q ^ e) → ∀ (r n : ℕ) (d : Fin r → ℤ), (GlobalTheory.InertHomIdx.intMat L r n).relIndex ((GlobalTheory.InertHomIdx.intMat L r n).map (GlobalTheory.InertHomIdx.lmul (Matrix.diagonal (fun i => ϖ ^ d i)))) = Q ^ (n * (∑ i, max (-d i) 0).toNat) := by
  first | exact @GlobalTheory.DiagIdx.relIndex_intMat_diag | exact GlobalTheory.DiagIdx.relIndex_intMat_diag | (intros; apply GlobalTheory.DiagIdx.relIndex_intMat_diag <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.relIndex_integralMatrices_leftMul_unitary_KU_invariant : ∀ {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (c : L →+* L) (r n : ℕ) (t k₁ k₂ : GU c r), k₁ ∈ KU c r → k₂ ∈ KU c r → (GlobalTheory.InertHomIdx.intMat L r n).relIndex ((GlobalTheory.InertHomIdx.intMat L r n).map (GlobalTheory.InertHomIdx.lmul (k₁ * t * k₂).1.1)) = (GlobalTheory.InertHomIdx.intMat L r n).relIndex ((GlobalTheory.InertHomIdx.intMat L r n).map (GlobalTheory.InertHomIdx.lmul t.1.1)) := by
  first | exact @GlobalTheory.InertHomIdx.relIndex_intMat_lmul_KU | exact GlobalTheory.InertHomIdx.relIndex_intMat_lmul_KU | (intros; apply GlobalTheory.InertHomIdx.relIndex_intMat_lmul_KU <;> assumption)
end
