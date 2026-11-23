module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AuxiliaryPrimeFunction
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.CompFinFinOne
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockSpaces.VolumeIsAddHaar
public import GroundTheory.GlobalFields.TateThesis.AdeleMeasurable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicFourierRealisesWeylElement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
public import Development.WeilBound.ThetaLifts.SmallCones.Bundle001
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

@[expose] public section

section

noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KFock

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def cmpW (d : SD σ) (w : InfinitePlace F) : AddSubgroup (Mx F E d.m d.n) where
  carrier := {X | d.cw w X = 0}
  zero_mem' := by
    show d.cw w 0 = 0
    exact Matrix.map_zero _ (map_zero _)
  add_mem' := by
    intro X Z hX hZ
    show d.cw w (X + Z) = 0
    have e : d.cw w (X + Z) = d.cw w X + d.cw w Z := Matrix.map_add _ (map_add _) X Z
    rw [e, show d.cw w X = 0 from hX, show d.cw w Z = 0 from hZ, add_zero]
  neg_mem' := by
    intro X hX
    show d.cw w (-X) = 0
    have e : d.cw w (-X) = -d.cw w X := Matrix.map_neg _ (map_neg _) X
    rw [e, show d.cw w X = 0 from hX, neg_zero]

def IntFact : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
  (d : SD σ) (R : RD d) (w : InfinitePlace F) (ν : Measure (Mx F E d.m d.n)), d.IsCov ν →
  ∃ (C : ℝ) (μ' : Measure (cmpW d w)), 0 < C ∧ μ'.IsAddHaarMeasure ∧
    ∀ (f : (Fin d.m → Fin d.n → ℂ) → ℂ) (Ψ : Mx F E d.m d.n → ℂ),
      (∀ X Z, (∀ w', w' ≠ w → d.cw w' Z = 0) → finOne F • Z = 0 → Ψ (X + Z) = Ψ X) →
      ∫ X, R.tens w f Ψ X ∂ν = C * (∫ u, f u) * ∫ Z, Ψ Z.1 ∂μ'

section Split

variable (d : SD σ) (R : RD d) (w : InfinitePlace F)

theorem cw_add' (X Z : Mx F E d.m d.n) : d.cw w (X + Z) = d.cw w X + d.cw w Z := Matrix.map_add _ (map_add _) X Z

theorem cw_sub' (X Z : Mx F E d.m d.n) : d.cw w (X - Z) = d.cw w X - d.cw w Z := Matrix.map_sub _ (map_sub _) X Z

theorem loc_add' (X Z : Mx F E d.m d.n) : R.loc w (X + Z) = R.loc w X + R.loc w Z := by
  unfold RD.loc
  rw [cw_add', Matrix.mul_add]
  exact Matrix.map_add _ (fun a b => star_add a b) _ _

theorem loc_of_mem {b : Mx F E d.m d.n} (hb : b ∈ cmpW d w) : R.loc w b = 0 := by
  have h : d.cw w b = 0 := hb
  unfold RD.loc
  rw [h, Matrix.mul_zero]
  exact Matrix.map_zero _ (star_zero _)

theorem continuous_loc : Continuous (R.loc w) := by
  unfold RD.loc
  exact (continuous_const.matrix_mul (Place.continuous_cw d w)).matrix_map continuous_star

end Split

theorem intFact : IntFact := by
  intro F E _ _ _ _ _ σ d R w ν hν
  haveI := hν.1
  obtain ⟨i1, i2, i3, i4⟩ := (PositivityTheory.ThKCT.ideleTop F E).1
  haveI : BorelSpace (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalAddGroup (Mx F E d.m d.n) := inferInstanceAs (IsTopologicalAddGroup (Fin d.m → Fin d.n → AE F E))
  haveI : LocallyCompactSpace (Mx F E d.m d.n) := inferInstanceAs (LocallyCompactSpace (Fin d.m → Fin d.n → AE F E))
  haveI : SecondCountableTopology (Mx F E d.m d.n) :=
    inferInstanceAs (SecondCountableTopology (Fin d.m → Fin d.n → AE F E))
  haveI : BorelSpace (Mx F E d.m d.n) := inferInstanceAs (BorelSpace (Fin d.m → Fin d.n → AE F E))
  have hcl : IsClosed ((cmpW d w : AddSubgroup (Mx F E d.m d.n)) : Set (Mx F E d.m d.n)) :=
    isClosed_eq (Place.continuous_cw d w) continuous_const
  haveI : LocallyCompactSpace (cmpW d w) := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology (cmpW d w) :=
    TopologicalSpace.Subtype.secondCountableTopology ((cmpW d w : AddSubgroup (Mx F E d.m d.n)) : Set (Mx F E d.m d.n))
  haveI : BorelSpace (cmpW d w) := Subtype.borelSpace (fun x' => x' ∈ ((cmpW d w : AddSubgroup (Mx F E d.m d.n)) : Set (Mx F E d.m d.n)))
  haveI := volume_isAddHaar d.m d.n
  obtain ⟨s, hsc, hs1, hs2, hsa, -⟩ := Place.exists_sec d.cm d.B.emb
  set fr : Matrix (Fin d.m) (Fin d.m) ℂ := (R.fr w).1 with hfr
  let U : (Fin d.m → Fin d.n → ℂ) → Matrix (Fin d.m) (Fin d.n) ℂ := fun u => fr * Matrix.of fun b j => star (u b j)
  let sW : (Fin d.m → Fin d.n → ℂ) → Mx F E d.m d.n := fun u i j => s fun w' => if w' = w then U u i j else 0
  have cw_sW : ∀ u, d.cw w (sW u) = U u := fun u => by
    ext i j
    show piInf (d.B.emb w) (s _) = U u i j
    rw [hs1, if_pos rfl]
  have cw_sW' : ∀ u w', w' ≠ w → d.cw w' (sW u) = 0 := fun u w' h => by
    ext i j
    show piInf (d.B.emb w') (s _) = 0
    rw [hs1, if_neg h]
  have fin_sW : ∀ u, finOne F • sW u = 0 := fun u => by
    ext i j
    show finOne F • s _ = 0
    exact hs2 _
  have inv_fr : ((R.fr w)⁻¹).1 * fr = 1 := Units.inv_mul (R.fr w)
  have fr_inv : fr * ((R.fr w)⁻¹).1 = 1 := Units.mul_inv (R.fr w)
  have loc_sW : ∀ u, R.loc w (sW u) = u := fun u => by
    unfold RD.loc
    rw [cw_sW, ← Matrix.mul_assoc, inv_fr, Matrix.one_mul]
    ext a j
    simp
  have U_loc : ∀ X, U (R.loc w X) = d.cw w X := fun X => by
    simp only [U, RD.loc]
    have : (Matrix.of fun b j => star ((((R.fr w)⁻¹).1 * d.cw w X).map star b j)) = ((R.fr w)⁻¹).1 * d.cw w X := by
      ext b j; simp
    rw [this, ← Matrix.mul_assoc, fr_inv, Matrix.one_mul]
  have U_add : ∀ u v, U (u + v) = U u + U v := fun u v => by
    simp only [U]
    rw [← Matrix.mul_add]
    congr 1
    ext b j
    simp [star_add]
  have sW_add : ∀ u v, sW (u + v) = sW u + sW v := fun u v => by
    ext i j
    show s _ = s _ + s _
    rw [← hsa]
    congr 1
    funext w'
    show _ = (if w' = w then U u i j else 0) + (if w' = w then U v i j else 0)
    by_cases h : w' = w
    · rw [if_pos h, if_pos h, if_pos h, U_add]; rfl
    · rw [if_neg h, if_neg h, if_neg h, add_zero]
  have hU : Continuous U := by
    simp only [U]
    exact continuous_const.matrix_mul (continuous_pi fun b => continuous_pi fun j =>
      continuous_star.comp ((continuous_apply j).comp (continuous_apply b)))
  have hsW : Continuous sW := by
    refine continuous_pi fun i => continuous_pi fun j => hsc.comp (continuous_pi fun w' => ?_)
    split_ifs
    · exact (continuous_apply j).comp ((continuous_apply i).comp hU)
    · exact continuous_const
  have mem : ∀ X, X - sW (R.loc w X) ∈ cmpW d w := fun X => by
    show d.cw w (X - sW (R.loc w X)) = 0
    rw [cw_sub', cw_sW, U_loc, sub_self]
  let Φ : (Fin d.m → Fin d.n → ℂ) × cmpW d w ≃ₜ+ Mx F E d.m d.n :=
    { toFun := fun p => sW p.1 + p.2.1
      invFun := fun X => (R.loc w X, ⟨X - sW (R.loc w X), mem X⟩)
      left_inv := fun p => by
        obtain ⟨u, b, hb⟩ := p
        have e1 : R.loc w (sW u + b) = u := by rw [loc_add', loc_sW, loc_of_mem d R w hb, add_zero]
        refine Prod.ext e1 (Subtype.ext ?_)
        show sW u + b - sW (R.loc w (sW u + b)) = b
        rw [e1, add_sub_cancel_left]
      right_inv := fun X => by
        show sW (R.loc w X) + (X - sW (R.loc w X)) = X
        rw [add_sub_cancel]
      map_add' := fun p q => by
        show sW (p.1 + q.1) + (p.2.1 + q.2.1) = sW p.1 + p.2.1 + (sW q.1 + q.2.1)
        rw [sW_add]; abel
      continuous_toFun := (hsW.comp continuous_fst).add (continuous_subtype_val.comp continuous_snd)
      continuous_invFun := (continuous_loc d R w).prodMk
        ((continuous_id.sub (hsW.comp (continuous_loc d R w))).subtype_mk _) }
  obtain ⟨C, hC, hg⟩ := integral_split ν (volume : Measure (Fin d.m → Fin d.n → ℂ)) (Measure.addHaar : Measure (cmpW d w)) Φ
  refine ⟨C, Measure.addHaar, hC, inferInstance, fun f Ψ hΨ => ?_⟩
  rw [hg]
  have e : ∀ p : (Fin d.m → Fin d.n → ℂ) × cmpW d w, R.tens w f Ψ (Φ p) = f p.1 * Ψ p.2.1 := fun p => by
    obtain ⟨u, b, hb⟩ := p
    show f (R.loc w (sW u + b)) * Ψ (sW u + b) = f u * Ψ b
    rw [loc_add', loc_sW, loc_of_mem d R w hb, add_zero, add_comm, hΨ b (sW u) (cw_sW' u) (fin_sW u)]
  simp_rw [e]
  have hp := integral_prod_mul (μ := (volume : Measure (Fin d.m → Fin d.n → ℂ))) (ν := (Measure.addHaar : Measure (cmpW d w)))
    f (fun Z : cmpW d w => Ψ Z.1)
  rw [hp, mul_assoc]

end PositivityTheory.SiegelWeilFormula.KFock

end
end

section

noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KFock

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem intSchA {κ : Type} [Fintype κ] (m : MeasurableSpace (κ → AF F))
    (hm : m = @MeasurableSpace.pi κ _ fun _ => GroundTheory.Global.measurableSpace_adeleRing F)
    (μ : @Measure (κ → AF F) m) (hμ : @Measure.IsAddHaarMeasure _ _ _ m μ) {φ : (κ → AF F) → ℂ} (hφ : φ ∈ schA F κ) :
    Integrable φ μ := by
  subst hm
  letI : MeasurableSpace (AdeleRing (𝓞 F) F) := GroundTheory.Global.measurableSpace_adeleRing F
  haveI : BorelSpace (AdeleRing (𝓞 F) F) := GroundTheory.Global.borelSpace_adeleRing F
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI : BorelSpace (κ → AdeleRing (𝓞 F) F) := Pi.borelSpace
  have h := Measure.isAddLeftInvariant_eq_smul μ (GroundTheory.Automorphic.GJMatrix.adeleMeasurePi F (ι := κ))
  rw [h]
  exact (GlobalTheory.TowU.FourWeyl.integrable_schA hφ).smul_measure (by simp)

theorem measAF_eq : (measAF : MeasurableSpace (AF F)) = GroundTheory.Global.measurableSpace_adeleRing F :=
  (GroundTheory.Global.borelSpace_adeleRing F).measurable_eq.symm

section Cmb

variable (d : SD σ)

theorem cmb_add (c c' : Fin d.m × Fin d.n × Fin 2 → AF F) : d.cmb (c + c') = d.cmb c + d.cmb c' := by
  ext i j
  simp only [SD.cmb, Pi.add_apply, Matrix.add_apply, TensorProduct.add_tmul, Finset.sum_add_distrib]

theorem cmb_eq (c : Fin d.m × Fin d.n × Fin 2 → AF F) (i : Fin d.m) (j : Fin d.n) :
    d.cmb c i j = ∑ k, c (i, j, k) • Algebra.TensorProduct.basis (AF F) d.bs k := by
  simp only [SD.cmb, Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

theorem crd_cmb' (c : Fin d.m × Fin d.n × Fin 2 → AF F) : d.crd (d.cmb c) = c := by
  funext k
  obtain ⟨i, j, l⟩ := k
  simp only [SD.crd, cmb_eq]
  exact congrFun ((Algebra.TensorProduct.basis (AF F) d.bs).repr_sum_self fun k => c (i, j, k)) l

theorem cmb_crd (X : Mx F E d.m d.n) : d.cmb (d.crd X) = X := by
  ext i j
  rw [cmb_eq]
  exact (Algebra.TensorProduct.basis (AF F) d.bs).sum_repr (X i j)

theorem continuous_cmb : Continuous d.cmb := by
  obtain ⟨i1, -, -, -⟩ := (PositivityTheory.ThKCT.ideleTop F E).1
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [cmb_eq]
  exact continuous_finsetSum _ fun k _ => ((continuous_apply (i, j, k)).smul continuous_const)

theorem continuous_crd : Continuous d.crd := by
  obtain ⟨i1, -, -, -⟩ := (PositivityTheory.ThKCT.ideleTop F E).1
  refine continuous_pi fun k => ?_
  have hl : Continuous (((Finsupp.lapply k.2.2).comp (Algebra.TensorProduct.basis (AF F) d.bs).repr.toLinearMap :
      AE F E →ₗ[AF F] AF F)) := IsModuleTopology.continuous_of_linearMap _
  exact hl.comp ((continuous_apply k.2.1).comp (continuous_apply k.1))

def cmbE : (Fin d.m × Fin d.n × Fin 2 → AF F) ≃ₜ+ Mx F E d.m d.n where
  toFun := d.cmb
  invFun := d.crd
  left_inv := crd_cmb' d
  right_inv := cmb_crd d
  map_add' := cmb_add d
  continuous_toFun := continuous_cmb d
  continuous_invFun := continuous_crd d

end Cmb

theorem int_schM (d : SD σ) (ν : Measure (Mx F E d.m d.n)) (hν : ν.IsAddHaarMeasure) {f : Mx F E d.m d.n → ℂ}
    (hf : f ∈ d.schM) : Integrable f ν := by
  obtain ⟨i1, i2, i3, i4⟩ := (PositivityTheory.ThKCT.ideleTop F E).1
  haveI : BorelSpace (AE F E) := ⟨rfl⟩
  haveI : BorelSpace (Mx F E d.m d.n) := inferInstanceAs (BorelSpace (Fin d.m → Fin d.n → AE F E))
  haveI : IsTopologicalAddGroup (Mx F E d.m d.n) := inferInstanceAs (IsTopologicalAddGroup (Fin d.m → Fin d.n → AE F E))
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI : BorelSpace (AF F) := ⟨rfl⟩
  haveI : BorelSpace (Fin d.m × Fin d.n × Fin 2 → AF F) := Pi.borelSpace
  let e : (Fin d.m × Fin d.n × Fin 2 → AF F) ≃ᵐ Mx F E d.m d.n := (cmbE d).toHomeomorph.toMeasurableEquiv
  haveI : (Measure.map e.symm ν).IsAddHaarMeasure := ContinuousAddEquiv.isAddHaarMeasure_map ν (cmbE d).symm
  have h1 : Integrable (f ∘ e) (Measure.map e.symm ν) := by
    have hf' : f ∘ d.cmb ∈ schA F (Fin d.m × Fin d.n × Fin 2) := Submodule.mem_comap.mp hf
    refine intSchA _ ?_ _ inferInstance hf'
    exact congrArg (fun m => @MeasurableSpace.pi (Fin d.m × Fin d.n × Fin 2) (fun _ => AF F) fun _ => m) measAF_eq
  have h2 := (integrable_map_equiv e f).2 h1
  rwa [MeasurableEquiv.map_map_symm] at h2

end PositivityTheory.SiegelWeilFormula.KFock

end
end
