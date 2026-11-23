module

public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle003
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle293
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EventuallyAlgebraMapMemIntegers
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle290
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle385
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle340
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle289
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle341
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle473
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle269
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle005
public import Formalism.LocalToGlobal.HermitianForms.Bundle001
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianLocalLevelUnitriangularIff
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle008
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlNormOneAdelicQuotientVolumeSiegelStep
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle009
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle270
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FibreGramNumberNullAndCutoffIntegralBound
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.Valuation.Integral
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle007
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis

@[expose] public section

section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

namespace GlobalTheory.CompletedSelfDual

open GlobalTheory.AdelicU GlobalTheory.AdelicU.SelfDual GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces

theorem mem_maxOrder_iff_mem_intLoc {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) (z : Fv F v ⊗[F] E) :
    z ∈ maxOrder F E v ↔ z ∈ intLoc F E v := by
  constructor
  · intro hz
    rw [mem_intLoc_iff_absFin_le_one, absFin_le_iff]
    intro τ
    obtain ⟨p, hp, hpz⟩ := (mem_maxOrder F E v z).1 hz
    let f : v.adicCompletionIntegers F →+* (valBar F v).integer :=
      ((algebraMap (Fv F v) (FvBar F v)).comp (v.adicCompletionIntegers F).subtype).codRestrict _ fun a => by
        change absBar F v (algebraMap (Fv F v) (FvBar F v) a) ≤ 1
        rw [absBar_algebraMap]
        exact_mod_cast Valued.toNormedField.norm_le_one_iff.2 a.2
    refine (Valuation.integer.integers (valBar F v)).mem_of_integral (x := finEmb F v τ z)
      ⟨p.map f, hp.map _, ?_⟩
    have := congrArg (finEmb F v τ : Fv F v ⊗[F] E →+* FvBar F v) hpz
    rw [Polynomial.hom_eval₂, map_zero] at this
    rw [Polynomial.eval₂_map, ← this]
    congr 1
    ext a
    exact ((finEmb F v τ).commutes (a : Fv F v)).symm
  · refine intLoc_induction (p := fun z => z ∈ maxOrder F E v) (fun a ha x => ?_) (zero_mem _)
      (fun _ _ => add_mem) (fun _ => neg_mem)
    have h1 : (1 : Fv F v) ⊗ₜ[F] (x : E) ∈ maxOrder F E v := by
      letI := (intToEv F E v).toAlgebra
      exact (RingOfIntegers.isIntegral_coe x).map_of_comp_eq (algebraMap ℤ _) (inclR (F := F) (E := E) (Fv F v))
        (RingHom.ext_int _ _)
    have h2 : a ⊗ₜ[F] (1 : E) ∈ maxOrder F E v :=
      RingHom.isIntegralElem_map (intToEv F E v) (x := ⟨a, ha⟩)
    simpa using mul_mem h2 h1

theorem exists_isSelfDualLattice : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)), IsHermND σ J → Submodule.IsLattice E L → (∀ y : Fin n → E, y ∈ L ↔ ∀ x ∈ L, hE σ J x y ∈ (algebraMap (𝓞 E) E).range) → ∀ v : HeightOneSpectrum (𝓞 F), ∃ Lv : Submodule (GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.maxOrder F E v) (Fin n → Fv F v ⊗[F] E), GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.IsSelfDualLattice σ J v Lv ∧ ∀ y, y ∈ Lv ↔ y ∈ GlobalTheory.AdelicU.latLoc F L v := by
  intro F E _ _ _ _ _ σ n J L hJ hL hsd v
  classical
  let Lv : Submodule (maxOrder F E v) (Fin n → Fv F v ⊗[F] E) :=
    { carrier := latLoc F L v
      zero_mem' := zero_mem _
      add_mem' := fun h h' => add_mem h h'
      smul_mem' := fun c _ hy =>
        (latLoc F L v).smul_mem ⟨c.1, (mem_maxOrder_iff_mem_intLoc v _).1 c.2⟩ hy }
  have hmem : ∀ y, y ∈ Lv ↔ y ∈ latLoc F L v := fun _ => Iff.rfl
  have hfull : Submodule.IsFullLattice E L := by
    refine { toIsLattice := hL, span_eq_top := eq_top_iff.mpr fun y _ => ?_ }
    obtain ⟨s, hs⟩ := hL.fg
    obtain ⟨d, hd, hden⟩ := exists_integral_multiples ℤ ℚ
      (s.image fun x => hE σ J x y)
    have hdE : (d : E) ≠ 0 := by exact_mod_cast hd
    have hy : (d : E) • y ∈ L := by
      apply (hsd _).2
      intro x hx
      rw [← hs] at hx
      have hint : IsIntegral ℤ (hE σ J x ((d : E) • y)) := by
        induction hx using Submodule.span_induction with
        | mem x hx =>
          have hh := hden (hE σ J x y) (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
          convert hh using 1 <;> simp [hE, Formalism.UG.hform, Pi.smul_apply,
            smul_eq_mul, Finset.mul_sum, Finset.sum_mul, zsmul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
        | zero => simpa [hE, Formalism.UG.hform] using (isIntegral_zero : IsIntegral ℤ (0 : E))
        | add x z _ _ hx hz =>
          convert hx.add hz using 1 <;>
            simp [hE, Formalism.UG.hform, add_mul, Finset.sum_add_distrib]
        | smul a x _ hx =>
          have ha : IsIntegral ℤ (σ (a : E)) := (RingOfIntegers.isIntegral_coe a).map σ.toRingHom.toIntAlgHom
          convert ha.mul hx using 1 <;>
            simp [hE, Formalism.UG.hform, Pi.smul_apply, ← algebraMap_smul E, smul_eq_mul, map_mul,
              Finset.mul_sum, mul_assoc]
      exact ⟨⟨_, hint⟩, rfl⟩
    have hyspan : (d : E) • y ∈ Submodule.span E (L : Set (Fin n → E)) := Submodule.subset_span hy
    have := Submodule.smul_mem (Submodule.span E (L : Set (Fin n → E))) (d : E)⁻¹ hyspan
    simpa [← smul_smul, hdE] using this
  obtain ⟨k, S, Φ, h1, hS, hΦ⟩ := exists_frame L hfull
  have h2 := map_mul_eq_one (F := F) (Fv F v) h1
  have hcol : ∀ j, (fun i => S.map (inclR (F := F) (Fv F v)) i j) ∈ Lv := fun j =>
    tmul_mem_latLoc (one_mem _) (hS j)
  refine ⟨Lv, ⟨?_, ?_, fun y => ?_⟩, hmem⟩
  · refine ⟨Finset.univ.image fun j i => S.map (inclR (F := F) (Fv F v)) i j, le_antisymm ?_ fun y hy => ?_⟩
    · rw [Submodule.span_le]
      intro y hy
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hy
      exact hcol j
    · rw [eq_sum_col h2 y]
      refine sum_mem fun j _ => ?_
      exact Submodule.smul_mem _ (⟨_, (mem_maxOrder_iff_mem_intLoc v _).2
        ((mem_latLoc_iff_of_frame h1 hS hΦ v y).1 hy j)⟩ : maxOrder F E v)
        (Submodule.subset_span (Finset.mem_image.2 ⟨j, Finset.mem_univ j, rfl⟩))
  · refine eq_top_iff.2 fun y _ => ?_
    rw [eq_sum_col h2 y]
    exact sum_mem fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span (hcol j))
  · have h3 : latLoc F L v = dualLoc σ J L v := (forall_isSelfDualAt_iff hJ.2 hfull).2 hsd v
    simp only [mem_maxOrder_iff_mem_intLoc]
    rw [hmem, h3]
    exact Iff.rfl

end GlobalTheory.CompletedSelfDual
end

section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

namespace GlobalTheory.AdelicU.Cofinite

open Filter

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem eventually_mem_intLoc_iff_repr {d : ℕ} (b : Module.Basis (Fin d) F E) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, ∀ y : Fv F v ⊗[F] E, y ∈ intLoc F E v ↔
      ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr y k ∈ v.adicCompletionIntegers F := by
  classical
  set ω := Module.Free.chooseBasis ℤ (𝓞 E) with hω
  have hI : ∀ (v : HeightOneSpectrum (𝓞 F)) (z : Fv F v ⊗[F] E), z ∈ intLoc F E v ↔
      z ∈ AddSubgroup.closure {z : Fv F v ⊗[F] E | ∃ a ∈ v.adicCompletionIntegers F, ∃ x : 𝓞 E,
        z = a ⊗ₜ[F] (x : E)} := fun _ _ => Iff.rfl
  have h1 : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, ∀ j k,
      algebraMap F (Fv F v) (b.repr ((ω j : 𝓞 E) : E) k) ∈ v.adicCompletionIntegers F := by
    simp only [Filter.eventually_all]
    intro j k
    exact eventually_algebraMap_mem_integers _
  have h2 : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, ∀ k,
      (1 : Fv F v) ⊗ₜ[F] b k ∈ intLoc F E v := by
    rw [Filter.eventually_all]
    intro k
    exact eventually_one_tmul_mem_intLoc _
  filter_upwards [h1, h2] with v h1 h2 y
  have key : ∀ (x : 𝓞 E) (k : Fin d),
      algebraMap F (Fv F v) (b.repr (x : E) k) ∈ v.adicCompletionIntegers F := by
    intro x k
    have hx : (x : E) = ∑ j, (ω.repr x j) • ((ω j : 𝓞 E) : E) := by
      have := congrArg (algebraMap (𝓞 E) E) (ω.sum_repr x)

      rw [map_sum] at this
      simp only [map_zsmul] at this
      exact this.symm

    rw [hx, map_sum, Finsupp.coe_finsetSum, Finset.sum_apply, map_sum]
    refine sum_mem fun j _ => ?_
    rw [map_zsmul, Finsupp.smul_apply, map_zsmul]
    exact zsmul_mem (h1 j k) _
  constructor
  · intro hy
    rw [hI] at hy
    induction hy using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, x, rfl⟩ := hz
      intro k
      rw [Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.mapRange_apply,
        smul_eq_mul]
      exact mul_mem ha (key x k)
    | zero => intro k; simp
    | add z w _ _ hz hw =>
      intro k
      rw [map_add (f := _), Finsupp.add_apply]
      exact add_mem (hz k) (hw k)
    | neg z _ hz =>
      intro k
      rw [map_neg, Finsupp.neg_apply]
      exact neg_mem (hz k)
  · intro hy
    rw [← (Algebra.TensorProduct.basis (Fv F v) b).sum_repr y]
    refine sum_mem fun k _ => ?_
    rw [Algebra.TensorProduct.basis_apply, Algebra.smul_def]
    refine mul_mem ?_ (h2 k)
    rw [hI]
    refine AddSubgroup.subset_closure ⟨_, hy k, 1, ?_⟩
    simp [Algebra.TensorProduct.algebraMap_apply]

theorem eventually_latLoc_eq_latV :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n d : ℕ)
      (b : Module.Basis (Fin d) F E) (L : Submodule (𝓞 E) (Fin n → E)), Submodule.IsFullLattice E L →
      ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
        {X : Fin 1 → Fin n → Fv F v ⊗[F] E | X 0 ∈ GlobalTheory.AdelicU.latLoc F L v} = latV b v := by
  intro F E _ _ _ _ _ n d b L hL
  have : Submodule.IsFullLattice E L := hL
  have : Submodule.IsFullLattice E (stdLattice E n) := isLattice_stdLattice
  filter_upwards [eventually_latLoc_eq F L (stdLattice E n), eventually_mem_intLoc_iff_repr b]
    with v hv h1
  have hI : ∀ z : Fv F v ⊗[F] E, z ∈ intLoc F E v ↔
      z ∈ AddSubgroup.closure {z : Fv F v ⊗[F] E | ∃ a ∈ v.adicCompletionIntegers F, ∃ x : 𝓞 E,
        z = a ⊗ₜ[F] (x : E)} := fun _ => Iff.rfl
  have hS : ∀ y : Fin n → Fv F v ⊗[F] E, y ∈ latLoc F (stdLattice E n) v ↔
      y ∈ AddSubgroup.closure {y : Fin n → Fv F v ⊗[F] E | ∃ a ∈ v.adicCompletionIntegers F,
        ∃ x ∈ stdLattice E n, y = fun i => a ⊗ₜ[F] x i} := fun _ => Iff.rfl
  have hstd : ∀ x : Fin n → E, x ∈ stdLattice E n ↔ ∀ i, ∃ z : 𝓞 E, (z : E) = x i := by
    intro x
    unfold stdLattice Formalism.UG.stdLat
    simp only [Submodule.mem_pi, Set.mem_univ, true_implies, LinearMap.mem_range,
      Algebra.linearMap_apply]
  have hloc : ∀ y, y ∈ latLoc F (stdLattice E n) v ↔ ∀ i, y i ∈ intLoc F E v := by
    intro y
    constructor
    · intro hy i
      rw [hS] at hy
      induction hy using AddSubgroup.closure_induction with
      | mem z hz =>
        obtain ⟨a, ha, x, hx, rfl⟩ := hz
        obtain ⟨w, hw⟩ := (hstd x).1 hx i
        rw [hI]
        exact AddSubgroup.subset_closure ⟨a, ha, w, by rw [hw]⟩
      | zero => exact zero_mem _
      | add z w _ _ hz hw => exact add_mem hz hw
      | neg z _ hz => exact neg_mem hz
    · intro hy
      rw [← Finset.univ_sum_single y, hS]
      refine sum_mem fun i _ => ?_
      have hyi := hy i
      rw [hI] at hyi
      revert hyi
      generalize y i = z0
      intro hyi
      induction hyi using AddSubgroup.closure_induction with
      | mem z hz =>
        obtain ⟨a, ha, x, rfl⟩ := hz
        refine AddSubgroup.subset_closure ⟨a, ha, Pi.single i (x : E), (hstd _).2 fun j => ?_, ?_⟩
        · by_cases h : j = i
          · subst h
            exact ⟨x, by simp⟩
          · exact ⟨0, by simp [h]⟩
        · funext j
          by_cases h : j = i
          · subst h
            simp
          · simp [h]
      | zero => simp
      | add z w _ _ hz hw =>
        rw [Pi.single_add]
        exact add_mem hz hw
      | neg z _ hz =>
        rw [Pi.single_neg]
        exact neg_mem hz
  ext X
  unfold latV
  simp only [Set.mem_ofPred_eq, hv, hloc, h1, Fin.forall_fin_one]

end GlobalTheory.AdelicU.Cofinite
end

section

open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

namespace GlobalTheory.GLm

theorem ip_symm_of_inv {G : Type} [Group G] [Fintype G] (α β : G → ℂ) : ip α β = ip β α := by
  unfold ip
  congr 1
  refine Fintype.sum_equiv (Equiv.inv G) _ _ fun x => ?_
  simp [mul_comm]

theorem exists_cusp_list (g : ℕ) [Fact g.Prime] (L : LabelDatum g) (hG : Green) :
    ∀ (n : ℕ) (f : (ZMod g)[X]), f.Monic → f.natDegree = n → f.coeff 0 ≠ 0 →
      ∃ Q : List ((ZMod g)[X] × Pc g), (∀ p ∈ Q, IsCuspOf L p.1 p.2.2) ∧ degL (Q.map Prod.snd) = n ∧
        f = (Q.map Prod.fst).prod := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro f hf hn h0
    by_cases hu : IsUnit f
    · have h1 : f = 1 := hf.isUnit_iff.mp hu
      refine ⟨[], by simp, ?_, by simpa using h1⟩
      rw [← hn, h1]; simp [degL]
    · obtain ⟨P, hPm, hPi, q, hq⟩ := Polynomial.exists_monic_irreducible_factor f hu
      have hqm : q.Monic := hPm.of_mul_monic_left (hq ▸ hf)
      have hdeg : n = P.natDegree + q.natDegree := by
        rw [← hn, hq, hPm.natDegree_mul hqm]
      have hpos : 0 < P.natDegree := hPi.natDegree_pos
      have hc : P.coeff 0 * q.coeff 0 ≠ 0 := by
        rwa [hq, Polynomial.mul_coeff_zero] at h0
      obtain ⟨Q, hQ1, hQ2, hQ3⟩ := ih q.natDegree (by omega) q hqm rfl (right_ne_zero_of_mul hc)
      obtain ⟨τ, hτ, -⟩ := hG g L P.natDegree hpos
      have hP : IsPrimeLab P.natDegree P := ⟨hPm, hPi, left_ne_zero_of_mul hc, rfl⟩
      refine ⟨(P, ⟨P.natDegree, τ P⟩) :: Q, ?_, ?_, ?_⟩
      · intro p hp
        rcases List.mem_cons.mp hp with rfl | hp
        · exact (hτ P hP).1
        · exact hQ1 p hp
      · rw [hdeg, ← hQ2]; simp [degL]
      · rw [List.map_cons, List.prod_cons, ← hQ3]; exact hq

theorem exists_irr_hasLabel (g : ℕ) [Fact g.Prime] (L : LabelDatum g) (hG : Green) (n : ℕ) (f : (ZMod g)[X])
    (hf : f.Monic) (hn : f.natDegree = n) (h0 : f.coeff 0 ≠ 0) :
    ∃ ρ : Gn g n → ℂ, IsIrr ρ ∧ HasLabel L ρ f := by
  obtain ⟨Q, hQ1, hQ2, hQ3⟩ := exists_cusp_list g L hG n f hf hn h0
  have hirr : ∀ p ∈ Q.map Prod.snd, IsIrr p.2 := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    exact (hQ1 q hq).2.1.2.1
  have hch : IsChar (hcL (Q.map Prod.snd) n) :=
    (GlobalTheory.T.harishChandraProductList_isCharacter_and_perm_invariant g _ (Q.map Prod.snd) n hQ2.symm fun p hp => by
      obtain ⟨V, -, hV⟩ := hirr p hp
      exact ⟨V, hV⟩).1
  have hne : hcL (Q.map Prod.snd) n 1 ≠ 0 := by
    intro h
    have hd := GlobalTheory.T.harishChandraProductList_degree g (Q.map Prod.snd) n hQ2.symm
    rw [h, zero_mul] at hd
    refine mul_ne_zero ?_ ?_ hd.symm
    · refine Finset.prod_ne_zero_iff.mpr fun i hi => ?_
      have hi1 : i ≠ 0 := by have := (Finset.mem_Icc.mp hi).1; omega
      have h1 : 1 < g ^ i := Nat.one_lt_pow hi1 (Fact.out : g.Prime).one_lt
      rw [sub_ne_zero]
      exact_mod_cast h1.ne'
    · refine List.prod_ne_zero fun hz => ?_
      obtain ⟨p, hp, hp0⟩ := List.mem_map.mp hz
      obtain ⟨d, hd0, hd1⟩ := (GlobalTheory.T.groupAlgebraTrace_idempotent_and_irreducible_degree (Gn g p.1) 1 p.2).2.1 (hirr p hp)
      rw [hp0] at hd1
      have : d = 0 := by exact_mod_cast hd1.symm
      omega
  have hdec := GlobalTheory.T.character_decomposition_and_classFunction_expansion (Gn g n) (hcL (Q.map Prod.snd) n)
  have hsum := hdec.2.1 (hdec.2.2.1 hch)
  by_contra hcon
  push Not at hcon
  apply hne
  rw [hsum, finsum_mem_of_eqOn_zero]
  · rfl
  · intro ρ hρ
    have : ip (hcL (Q.map Prod.snd) n) ρ = 0 := by
      by_contra hip
      exact hcon ρ hρ ⟨Q, hQ1, hQ2, hQ3, by rwa [ip_symm_of_inv]⟩
    simp [this]

theorem zOf_ne_zero_of_isIrr {G : Type} [Group G] [Fintype G] {ρ : G → ℂ} (hρ : IsIrr ρ) : zOf ρ ≠ 0 := by
  intro h
  obtain ⟨-, h1, h2⟩ := GlobalTheory.T.groupAlgebraTrace_idempotent_and_irreducible_degree G 1 ρ
  obtain ⟨d, hd0, hd1⟩ := h1 hρ
  have htr : tr (1 : MonoidAlgebra ℂ G) ρ = ρ 1 := by
    unfold tr
    rw [Finset.sum_eq_single 1]
    · simp [MonoidAlgebra.one_def]
    · intro b _ hb
      simp [MonoidAlgebra.one_def, Finsupp.single_apply, hb, hb.symm]
    · simp
  have hd : ρ 1 ≠ 0 := by rw [hd1]; exact_mod_cast hd0.ne'
  have hc : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [h, mul_zero, htr] at h2
  exact mul_ne_zero (div_ne_zero hd hc) hd (h2.symm.trans (by simp))

theorem eSerC_ne_zero : ∀ (g : ℕ) [Fact g.Prime] (L : LabelDatum g), Green → ∀ (n : ℕ) (f : (ZMod g)[X]),
    f.Monic → f.natDegree = n → f.coeff 0 ≠ 0 → eSerC L n f ≠ 0 := by
  intro g _ L hG n f hf hn h0 he
  obtain ⟨ρ, hρ, hl⟩ := exists_irr_hasLabel g L hG n f hf hn h0
  have hfin : {χ : Gn g n → ℂ | IsIrr χ ∧ HasLabel L χ f}.Finite :=
    (GlobalTheory.T.finite_irrCharacters_and_finsum_centralIdempotents_eq_one (Gn g n)).1.subset fun χ hχ => hχ.1
  apply zOf_ne_zero_of_isIrr hρ
  have h : zOf ρ * eSerC L n f = zOf ρ := by
    unfold eSerC
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin, Finset.mul_sum, Finset.sum_eq_single ρ]
    · rw [(GlobalTheory.T.centralIdempotentOfIrrCharacter_orthogonal_central _ ρ ρ hρ hρ).1, if_pos rfl]
    · intro b hb hne
      rw [(GlobalTheory.T.centralIdempotentOfIrrCharacter_orthogonal_central _ ρ b hρ (hfin.mem_toFinset.mp hb).1).1, if_neg hne.symm]
    · intro hb
      exact absurd (hfin.mem_toFinset.mpr ⟨hρ, hl⟩) hb
  rw [← h, he, mul_zero]

end GlobalTheory.GLm
end

section

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG GlobalTheory.LocOver
open scoped Classical

theorem _root_.GlobalTheory.T.exists_datum_of_two_congruent_frames : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r : ℕ), ∀ (P : FPair H r) (t : Term V M r), H.IsTerm t → t.T = P.A.T → t.T' = P.B.T → Tri E P.A.f t.f → Tri E P.B.f t.f' → ∃ d : Datum P, IsTermOver P d t := by
  first | exact @GlobalTheory.LocOver.TermOver.exists_datum | exact GlobalTheory.LocOver.TermOver.exists_datum | (intros; apply GlobalTheory.LocOver.TermOver.exists_datum <;> assumption)
end

section

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

theorem _root_.GlobalTheory.T.prime_sq_le_local_hermitian_dual_index : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm (cm.sig : E →+* E) J → J.det ≠ 0 → ∀ (T f : ℕ) (L : Submodule (𝓞 E) (Fin n → E)), T.Prime → SplitsIn E T → Module.finrank ℚ E = 2 * f → TLat cm.sig J T f L → ∀ (v : HeightOneSpectrum (𝓞 F)), (T : 𝓞 F) ∈ v.asIdeal → ∀ (sp : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F), (∀ x, sp (sigR cm.sig (v.adicCompletion F) x) = swapR _ (sp x)) → (∀ a : v.adicCompletion F, sp ((1 : E) ⊗ₜ[F] a) = (a, a)) → ((∀ y ∈ loc v (_root_.GlobalTheory.St.G.dualL cm.sig J L), ∃ z ∈ loc v L, ∀ b, (sp (z b)).1 = (sp (y b)).1) ↔ (∀ y ∈ loc v (_root_.GlobalTheory.St.G.dualL cm.sig J L), ∃ z ∈ loc v L, ∀ b, (sp (z b)).2 = (sp (y b)).2)) → (loc v L).toAddSubgroup.relIndex (loc v (_root_.GlobalTheory.St.G.dualL cm.sig J L)).toAddSubgroup ≠ 0 → T ^ 2 ≤ (loc v L).toAddSubgroup.relIndex (loc v (_root_.GlobalTheory.St.G.dualL cm.sig J L)).toAddSubgroup :=
  @_root_.GlobalTheory.St.G.IdxLower.sq_le_local_index
end

section

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

theorem _root_.GlobalTheory.T.hermitian_local_level_unitriangular_iff : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm (cm.sig : E →+* E) J → J.det ≠ 0 → ∀ (v : HeightOneSpectrum (𝓞 F)) (sp : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F), (∀ x, sp (sigR cm.sig (v.adicCompletion F) x) = swapR _ (sp x)) → (∀ a : v.adicCompletion F, sp ((1 : E) ⊗ₜ[F] a) = (a, a)) → (∀ x, x ∈ intV E v ↔ (sp x).1 ∈ v.adicCompletionIntegers F ∧ (sp x).2 ∈ v.adicCompletionIntegers F) → ∀ (g : ℕ), IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) = Ideal.span {((g : ℕ) : v.adicCompletionIntegers F)} → ∀ (L : Submodule (𝓞 E) (Fin n → E)), IsLat L → ∀ (c : Fin n → Fin n → E ⊗[F] v.adicCompletion F) (fr : GL (Fin n) (v.adicCompletion F)), (∀ j, c j ∈ loc v L) → (∀ j a, (sp (c j a)).2 = 0) → (fr : Matrix (Fin n) (Fin n) (v.adicCompletion F)) = Matrix.of (fun a j => (sp (c j a)).1) → (∀ x : Fin n → v.adicCompletion F, (∃ y ∈ loc v L, ∀ a, (sp (y a)).1 = x a) ↔ ∀ a, ((fr⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)).mulVec x a ∈ v.adicCompletionIntegers F) → ∀ (t : ℕ), ∀ y ∈ levelVL cm.sig J v L, (∀ a b, ((fr⁻¹ * bc ((RingHom.fst _ _).comp sp.toRingHom) y * fr : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) a b ∈ v.adicCompletionIntegers F) ∧ ((∀ i : Fin n, InModL (loc v L) g (c '' {j | j.1 < i.1}) ((y.1 - 1) *ᵥ c i)) ↔ InJ n t n false (redM F v ((fr⁻¹ * bc ((RingHom.fst _ _).comp sp.toRingHom) y * fr : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)))) := by
  first | exact @GlobalTheory.St.G.FirstColumn.unitriangular_iff | exact GlobalTheory.St.G.FirstColumn.unitriangular_iff | (intros; apply GlobalTheory.St.G.FirstColumn.unitriangular_iff <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

theorem _root_.GlobalTheory.T.glNormOneAdelicQuotientVolume_siegel_step : ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E → ∀ j : ℕ, 2 ≤ j → glVol E (j - 1) < ⊤ → glVol E j = glVol E (j - 1) * ENNReal.ofReal (Formalism.HermitianLatticesTheory.vInv E ^ (Formalism.HermitianLatticesTheory.fDeg E * (2 * j - 1)) * zetaE E j) := by
  first | exact @GlobalTheory.FlagBase.SiegelStep.glVol_step | exact GlobalTheory.FlagBase.SiegelStep.glVol_step | (intros; apply GlobalTheory.FlagBase.SiegelStep.glVol_step <;> assumption)
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.normalFormRootMeasure_haar_unimodular : ∀ (k r : ℕ) (γ : Mat k r) (s : ℝ) (μR : Measure (Mt k r)), 0 < s → NormR k r γ s μR → IsClosedSub k r (Rset k r γ) ∧ IsHaarOn (Rset k r γ) μR ∧ IsUnimod (Rset k r γ) μR ∧ NormR k r γ⁻¹ s (μR.map (conjM γ)) := by
  first | exact @GlobalTheory.Amp.RootMeas.normR_facts | exact GlobalTheory.Amp.RootMeas.normR_facts | (intros; apply GlobalTheory.Amp.RootMeas.normR_facts <;> assumption)
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.fibre_gramNumber_null_and_cutoff_integral_bound : ∀ (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ)) (g₀ : Mat k r) (β : Fin r → ℕ) (De : ℝ), 1 ≤ r → 2 * r + 6 ≤ k → TwoFl k r z z' g₀ → IsNormal k r β g₀ → DeOK k r z z' g₀ De → ∀ m ∈ UH (Hb k), ∀ a : Fin r → ℝ, (∀ b, 0 < a b) → lebN k r {n | Yv k r z z' g₀ (Matrix.of n * (uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m)) = 0} = 0 ∧ ∀ φ, SubCut (Nset k r) (lebR k r β) φ → ∀ R₀ y : ℝ, 1 ≤ R₀ → 0 < y → ∫⁻ n, φ n * (Eset k r z z' g₀ R₀ y).indicator 1 (rmulM (uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m) n) ∂(lebN k r) ≤ ENNReal.ofReal (fibVol k r R₀ De y) := by
  first | exact @GlobalTheory.Amp.FibNf.fibre_bound | exact GlobalTheory.Amp.FibNf.fibre_bound | (intros; apply GlobalTheory.Amp.FibNf.fibre_bound <;> assumption)
end
