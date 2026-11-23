module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle001
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle409
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.PoincareConstantEq
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocalAdditiveCharContinuous
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle017
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.FullExistsTiedHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle018
public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicTransportMeasureThird
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle147
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle125
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GramMapFibreMeasureUnitriangularInvariant
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import ReciprocityTheory.Automorphisms.SplitCoeAlgebraMap
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle014
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle326
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
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle005
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Measures
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Topology.Algebra.Group.OpenMapping
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.UniformSpace.Uniformizable

@[expose] public section

section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.transport_represents_classes_weight_one : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (F : Formalism.L2.Forms.Forms0 D u) (Tr : Transport X u F) (hK : X.LevelSubgroupCharacter), (∀ a, Tr.ιA (sigA X.B.I a) = Formalism.UG.sigR (Formalism.L2.Forms.sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (Tr.ιA a)) → LevelMatch X Tr hK → ClsMatch X Tr hK ∧ (Formalism.L2.SG.ColsDim.StabTriv (iotaF X u) (Ku X u hK) → ∀ c, (D.mem u).C.wt 0 c = 1) := by
  first | exact @GlobalTheory.ColClass.classes_and_weight | exact GlobalTheory.ColClass.classes_and_weight | (intros; apply GlobalTheory.ColClass.classes_and_weight <;> assumption)
end

section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting

namespace GlobalTheory

theorem fullExists_of_locTied : ∀ (D : D7) (X : HidaSetting D), Formalism.L2.SG.Pf.LocCP.LocTied D → Nonempty (Formalism.L2.SG.Full.Full X) := by

  intro D X hT
  exact Formalism.L2.SG.Pf.fullExists_tied Formalism.L2.SG.Pf.trExistsC_holds Formalism.L2.SG.Pf.lattice_steps_hold
    Formalism.L2.SG.Closed.LocCTied_holds D X (Formalism.L2.SG.Closed.level_subgroup_is_group X) hT

end GlobalTheory
end

section

open MeasureTheory Formalism.MainNotions.S Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.RowLev NumberField Matrix
open scoped InnerProductSpace TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IntertwMult

theorem contRep_facts (I : AutInst) (μf : Measure I.Gf) [μf.IsHaarMeasure] [SigmaFinite μf] (fund : Set I.GA)
    (R : I.GA → (I.L2 μf fund →L[ℂ] I.L2 μf fund)) (hF : I.IsFundDom (I.muA μf) fund)
    (hR : I.IsRightReg μf fund R) (y : I.L2 μf fund) (f : I.GA → ℂ) (hc : Continuous f)
    (hi : ∀ γ ∈ I.GFset, ∀ x, f (γ * x) = f x) (he : ∀ᵐ x ∂(I.muA μf), f x = I.ext y x) :
    (∀ f' : I.GA → ℂ, Continuous f' → (∀ᵐ x ∂(I.muA μf), f' x = I.ext y x) → f' = f) ∧
    (I.IsCuspFn (I.muA μf) (I.ext y) → I.IsCuspFn (I.muA μf) f) ∧
    ∀ (k : I.GA) (c : ℂ), R k y = c • y → ∀ x, f (x * k) = c * f x := by
  classical
  have hH : I.IsHilbTensor (H := fun _ => ℂ) (fun _ _ => ContinuousLinearMap.id ℂ ℂ)
      (fun _ => ContinuousLinearMap.id ℂ ℂ) (fun x => ∏ v, x v) := by
    refine ⟨fun x y => ?_, fun _ _ => rfl, ?_⟩
    · simp only [RCLike.inner_apply, map_prod, ← Finset.prod_mul_distrib]
    · have hspan : Submodule.span ℂ (Set.range fun x : (∀ _ : InfinitePlace I.F, ℂ) => ∏ v, x v) = ⊤ := by
        refine eq_top_iff.2 fun z _ => ?_
        have h1 : (1 : ℂ) ∈ Set.range fun x : (∀ _ : InfinitePlace I.F, ℂ) => ∏ v, x v :=
          ⟨fun _ => 1, by simp⟩
        simpa using Submodule.smul_mem _ z (Submodule.subset_span h1)
      rw [hspan, Submodule.top_coe]
      exact dense_univ
  let B : RowsAut := GlobalTheory.RepSmooth.bundle I μf fund R (fun _ => ℂ) (fun _ => inferInstance)
    (fun _ _ => ContinuousLinearMap.id ℂ ℂ) ℂ (fun _ => ContinuousLinearMap.id ℂ ℂ) (fun x => ∏ v, x v) hF hR hH 1
  have hy : GlobalTheory.Dec.IsContRep B y f := GlobalTheory.RepSmooth.isContRep_of_ae B hc hi he
  obtain ⟨-, -, htr, hfin⟩ := GlobalTheory.ExtContRep.ext_ae_eq_contRep B y f hy
  obtain ⟨huniq, hlin, -, -⟩ := GlobalTheory.ContRepUniq.contRep_unique_linear B
  refine ⟨fun f' hc' he' => ?_, fun hcu W hW ν hν => ?_, fun k c hk x => ?_⟩
  · have hae : ∀ᵐ x ∂(I.muA μf), f' x = f x := by
      filter_upwards [he', he] with x h1 h2
      rw [h1, h2]
    exact GlobalTheory.RepSmooth.eq_of_ae B hc' hc hae
  · haveI : IsFiniteMeasure ν := hν.1
    filter_upwards [hcu W hW ν hν, hfin ν inferInstance] with x h1 h2
    have h2' : ∀ᵐ m ∂ν, I.ext y (m * x) = f (m * x) := h2
    rw [← h1]
    exact integral_congr_ae (h2'.mono fun m hm => hm.symm)
  · have h3 : GlobalTheory.Dec.IsContRep B (R k y) (fun x => f (x * k)) := htr k
    rw [hk] at h3
    have h4 := hlin y y f f (c - 1) hy hy
    have e1 : y + (c - 1) • y = c • y := by
      rw [sub_smul, one_smul, add_sub_cancel]
    rw [e1] at h4
    have h5 : f (x * k) = f x + (c - 1) * f x := congrFun (huniq _ _ _ h3 h4) x
    rw [h5]
    ring

end GlobalTheory.IntertwMult
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal

theorem _root_.GlobalTheory.T.gramMap_fibreMeasure_unitriangular_invariant : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ a : ℕ, ∀ (μ : Measure (Fin a → Fin n → Fv F v ⊗[F] E)) (ν : Measure (HermR (Fv F v) σ a)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → ∀ fib : HermR (Fv F v) σ a → Measure (Fin a → Fin n → Fv F v ⊗[F] E), IsFibreFamily μ (gramR (Fv F v) σ J) Subtype.val {X | LinearIndependent (Fv F v ⊗[F] E) X} ν Set.univ fib → ∀ (S : HermR (Fv F v) σ a) (u : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)), (∀ i, u i i = 1) → (∀ i j, j < i → u i j = 0) → (u.map (sigR (Fv F v) σ)).transpose * (S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) * u = (S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) → (fib S).map (fun X b => ∑ c, u c b • X c) = fib S := by
  first | exact @GlobalTheory.FibreUnitri.fibre_unitri_invariant | exact GlobalTheory.FibreUnitri.fibre_unitri_invariant | (intros; apply GlobalTheory.FibreUnitri.fibre_unitri_invariant <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys Formalism.MainNotions.ArithmeticCylinders
attribute [local instance] GlobalTheory.TypeRec.factG GlobalTheory.LabPin.instCM
open GlobalTheory.LabPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

theorem indep_subfamily_of_disjoint_or_le : ∀ (ι M : Type) [AddCommGroup M] [Module ℂ M] (N : ι → Submodule ℂ M), (∀ i (J : Finset ι), Disjoint (N i) (⨆ j ∈ J, N j) ∨ N i ≤ ⨆ j ∈ J, N j) → ∀ F : Finset ι, ∃ J ⊆ F, (⨆ j ∈ J, N j) = (⨆ j ∈ F, N j) ∧ ∀ f f' : ι → M, (∀ j ∈ J, f j ∈ N j) → (∀ j ∈ J, f' j ∈ N j) → ∑ j ∈ J, f j = ∑ j ∈ J, f' j → ∀ j ∈ J, f j = f' j := by
  intro ι M _ _ N h F
  classical
  refine Finset.induction_on F ?_ ?_
  · exact ⟨∅, Finset.Subset.refl _, rfl, by simp⟩
  · intro i F hi ih
    obtain ⟨J, hJF, hJsup, huniq⟩ := ih
    have hiJ : i ∉ J := fun hh => hi (hJF hh)
    rcases h i J with hd | hle
    · refine ⟨insert i J, Finset.insert_subset_insert _ hJF, ?_, ?_⟩
      · rw [Finset.iSup_insert, Finset.iSup_insert, hJsup]
      · intro f f' hf hf' hsum
        rw [Finset.sum_insert hiJ, Finset.sum_insert hiJ] at hsum
        have hdiff : f i - f' i = ∑ j ∈ J, f' j - ∑ j ∈ J, f j := by
          rw [sub_eq_sub_iff_add_eq_add, hsum, add_comm]
        have hmem : f i - f' i ∈ N i ⊓ ⨆ j ∈ J, N j := by
          refine ⟨Submodule.sub_mem _ (hf i (Finset.mem_insert_self _ _))
            (hf' i (Finset.mem_insert_self _ _)), ?_⟩
          rw [hdiff]
          exact Submodule.sub_mem _
            (Submodule.sum_mem_biSup fun j hj => hf' j (Finset.mem_insert_of_mem hj))
            (Submodule.sum_mem_biSup fun j hj => hf j (Finset.mem_insert_of_mem hj))
        rw [hd.eq_bot, Submodule.mem_bot, sub_eq_zero] at hmem
        rw [hmem] at hsum
        have hJs : ∑ j ∈ J, f j = ∑ j ∈ J, f' j := add_left_cancel hsum
        intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact hmem
        · exact huniq f f' (fun k hk => hf k (Finset.mem_insert_of_mem hk))
            (fun k hk => hf' k (Finset.mem_insert_of_mem hk)) hJs j hj
    · refine ⟨J, hJF.trans (Finset.subset_insert _ _), ?_, huniq⟩
      rw [Finset.iSup_insert, ← hJsup]
      exact (sup_eq_right.mpr hle).symm

end GlobalTheory
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys Formalism.MainNotions.ArithmeticCylinders
attribute [local instance] GlobalTheory.TypeRec.factG GlobalTheory.LabPin.instCM
open GlobalTheory.LabPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open Filter Topology

namespace GlobalTheory.SlocVal

theorem tendsto_pow_map {A B : Type} [Ring A] [TopologicalSpace A] [Ring B] [TopologicalSpace B]
    (f : A →+* B) (hf : Continuous f) {x : A} (hx : Tendsto (fun n : ℕ => x ^ n) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => f x ^ n) atTop (𝓝 0) := by
  have h := (hf.tendsto 0).comp hx
  rw [map_zero] at h
  simpa [Function.comp_def, map_pow] using h

theorem continuous_symm {A B : Type} [Field A] [TopologicalSpace A] [IsTopologicalRing A]
    [SigmaCompactSpace A] [Field B] [TopologicalSpace B] [IsTopologicalRing B] [BaireSpace B]
    [T2Space B] (e : A ≃+* B) (he : Continuous e) : Continuous e.symm := by
  have ho : IsOpenMap e :=
    AddMonoidHom.isOpenMap_of_sigmaCompact e.toAddEquiv.toAddMonoidHom e.surjective he
  exact e.toEquiv.continuous_symm_iff.2 ho

end GlobalTheory.SlocVal


open GlobalTheory.SlocVal in
theorem GlobalTheory.valuation_lt_one_iff_norm_lt_one_of_continuous : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L) (g : ℕ) [Fact g.Prime] (i : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L) (j : ℚ_[g] ≃+* s.w.adicCompletion L), Continuous i → Continuous j → ∀ z : s.v.adicCompletion (maximalRealSubfield L), Valued.v z < 1 ↔ ‖j.symm (i z)‖ < 1 := by
  intro L _ _ _ s g _ i j hi hj z
  have := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion (maximalRealSubfield L) s.v
  have hj' : Continuous j.symm := continuous_symm j hj
  have hi' : Continuous i.symm := continuous_symm i hi
  have hφ : Continuous (i.trans j.symm) := hj'.comp hi
  have hψ : Continuous (i.trans j.symm).symm := hi'.comp hj
  have hz : Valued.v z < 1 ↔ ‖z‖ < 1 := (Valued.toNormedField.norm_lt_one_iff).symm
  rw [hz, ← tendsto_pow_atTop_nhds_zero_iff_norm_lt_one, ← tendsto_pow_atTop_nhds_zero_iff_norm_lt_one]
  constructor
  · intro h
    exact tendsto_pow_map (i.trans j.symm).toRingHom hφ h
  · intro h
    have := tendsto_pow_map (i.trans j.symm).symm.toRingHom hψ h
    simpa using this
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys Formalism.MainNotions.ArithmeticCylinders
attribute [local instance] GlobalTheory.TypeRec.factG GlobalTheory.LabPin.instCM
open GlobalTheory.LabPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SplitUniqSer

theorem splitPlace_unique : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (s s' : SplitPlace L),
    s.w = s'.w → s = s' :=
  GlobalTheory.SplitUniq.splitPlace_eq_of_w_eq

end GlobalTheory.SplitUniqSer
end
