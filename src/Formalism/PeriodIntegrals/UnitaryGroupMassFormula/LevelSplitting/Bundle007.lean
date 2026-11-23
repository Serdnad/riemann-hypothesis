module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.Bundle006
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.LeviInfUnipotentEqOne
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.NCDefs
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.CoordinateHomeomorphism
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.HeisenbergCocycleMemCentre
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.Bundle003
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.Bundle004
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.NCAsmV
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.UnitaryGroupSecondCountableT2
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TensTop
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.Bundle004
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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

@[expose] public section

section

noncomputable section

namespace PI.LevelKSplit.W.NC

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.LevelKSplit
open scoped TensorProduct

section Ext

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} [FiniteDimensional F E]

theorem isClosed_FixXp {r : ℕ} (P : Frame E M r) :
    IsClosed (FixXp (Af F) σ J P : Set (HA (Af F) σ J)) := by
  have h : (FixXp (Af F) σ J P : Set (HA (Af F) σ J)) =
      ⋂ v, ⋂ (_ : InXperp (Af F) σ J P v), {g | lin (Af F) σ J g v = v} := by
    ext g
    simp only [Set.mem_iInter, Set.mem_ofPred_eq, SetLike.mem_coe]
    exact Iff.rfl
  rw [h]
  exact isClosed_iInter fun v => isClosed_iInter fun _ =>
    isClosed_eq (ExC.continuous_lin _) continuous_const

theorem ncoord_of_parts (hH : HeisP F E σ M J) (hL : LevP F E σ M J) : NCoord F E σ M J := by
  intro hJ hinv r P T hP
  obtain ⟨sH, csH, cyH, hs1, hdec, hyH, hZN1, hcent, hmul, hZnorm, hconj, hZconj⟩ :=
    hH hJ hinv r P T hP
  obtain ⟨A, Lev, hAN, hAcl, cLev, hLev, hAN1, hN1norm, hAcomm⟩ := hL hJ hinv r P T hP
  have hmemW : ∀ m : LevelUnipotentSubgroup (Af F) σ J P, ∀ a, yH (Af F) σ J P m a ∈ Wp (Af F) σ J P := by
    intro m a
    obtain ⟨y, hy, -⟩ := hdec m m.2
    rw [← hy a]; exact (y a).2
  let yQ : LevelUnipotentSubgroup (Af F) σ J P → (Fin r → Wp (Af F) σ J P) := fun m a =>
    ⟨yH (Af F) σ J P m a, hmemW m a⟩
  have H : CoordHyp (Nsub (Af F) σ J P) A (LevelUnipotentSubgroup (Af F) σ J P) (Zsub (Af F) σ J P) Lev sH yQ :=
    { hAN := hAN
      coordinate_level_le := inf_le_left
      hZN1 := hZN1
      cLev := cLev
      csH := csH
      cyQ := continuous_pi fun a => Continuous.subtype_mk
        ((continuous_apply a).comp (cyH.comp continuous_subtype_val)) _
      lev_mem := fun n hn => (hLev n hn).1
      lev_rest := fun n hn => (hLev n hn).2
      triv := hAN1
      norm1 := hN1norm
      sH_mem := hs1
      dec := fun m => by
        obtain ⟨y, hy, hz⟩ := hdec m m.2
        have : yQ m = y := funext fun a => Subtype.ext (hy a).symm
        rw [this]; exact hz
      yQ_sH := fun y z hz => funext fun a => Subtype.ext (hyH y z hz a)
      cent := hcent
      mul := hmul }
  refine ⟨A, Zsub (Af F) σ J P, cHomeo H, hAcl, ?_, fun n0 => coord_skew H n0, ?_⟩
  · show IsClosed ((Nsub (Af F) σ J P ⊓ FixXp (Af F) σ J P : Subgroup (HA (Af F) σ J)) :
      Set (HA (Af F) σ J))
    rw [Subgroup.coe_inf]
    exact (ExC.isClosed_Nsub hJ hinv P T hP).inter (isClosed_FixXp P)
  · intro h hh u y z
    obtain ⟨y', hy', hc⟩ := hconj h hh y
    refine ⟨y', hy', ?_⟩
    rw [cHomeo_apply, cHomeo_apply]
    have hu : h * (u : HA (Af F) σ J) * h⁻¹ = u := by rw [hAcomm h hh u u.2]; group
    have hz : h * (z : HA (Af F) σ J) * h⁻¹ = z := hZconj h hh z z.2
    calc h * ((u : HA (Af F) σ J) * sH y * (z : HA (Af F) σ J)) * h⁻¹
        = (h * u * h⁻¹) * (h * sH y * h⁻¹) * (h * z * h⁻¹) := by group
      _ = u * sH y' * z := by rw [hu, hc, hz]

end Ext

theorem ncoordAll_of (hH : HeisPAll) (hL : LevPAll) : NCoordAll := by
  intro F E _ _ _ _ _ σ hσ M J hJ
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hσ.2.2.1]; norm_num)
  exact ncoord_of_parts (hH F E σ hσ M J hJ) (hL F E σ hσ M J hJ)

theorem levelSAll_of_semiNHS_heis_lev (hS : PI.LevelKSplit.W.ExS.SemiNHSAll) (hH : HeisPAll) (hL : LevPAll)
    (hV : PI.LevelKSplit.W.CD.ModVAll) (hA : NCAsmAll) : PI.LevelKSplit.LevelSAll :=
  levelSAll_of_parts hS (ncoordAll_of hH hL) hV hA

end PI.LevelKSplit.W.NC
end
end

section

noncomputable section

namespace PI.LevelKSplit.W.NCH

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub PI.VolSemiDirect.W NumberField IsDedekindDomain
open scoped TensorProduct

theorem heisenberg_parabolic (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E]
    [FiniteDimensional F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) :
    PI.LevelKSplit.W.NC.HeisP F E σ M J := by
  intro hJ hσσ r P T hP
  have H : (datR (Af F) σ J P T).Hyp := datR_hyp (R := Af F) hσσ hJ hP
  have hh : Half (datR (Af F) σ J P T) (algebraMap F (Af F ⊗[F] E) (1 / 2)) := by
    refine ⟨?_, ?_⟩
    · rw [← map_add (f := _), add_halves, map_one]
    · show (Algebra.TensorProduct.map (AlgHom.id F (Af F)) σ) (algebraMap F (Af F ⊗[F] E) (1 / 2)) =
        algebraMap F (Af F ⊗[F] E) (1 / 2)
      exact AlgHom.commutes _ _
  have hcy : Continuous fun y : Fin r → PI.LevelKSplit.W.NC.Wp (Af F) σ J P =>
      fun a => (y a : Fin M → Af F ⊗[F] E) :=
    continuous_pi fun a => continuous_subtype_val.comp (continuous_apply a)
  refine ⟨fun y => sHG hJ H hh (y := fun a => (y a : Fin M → Af F ⊗[F] E)) (fun a => (y a).2),
    ?_, continuous_yH P, fun y => sHG_mem hJ H hh _, fun g hg => ?_, fun y z hz a => ?_,
    centre_le_unipotent_radical hJ H hh, fun z hz g hg => Z_comm hJ H hh hz hg, fun y y' => ?_,
    fun g hg z hz => N_norm_Z hJ H hh hg hz, fun g hg y => ?_, fun g hg z hz => H_comm_Z hJ H hh hg hz⟩
  · exact Md.continuous_into_HA hJ (continuous_sLmat P T _ hcy)
  · exact ⟨fun a => ⟨_, isWp_yH hJ H hh g a⟩, fun a => rfl, inv_mul_mem_Z hJ H hh hg⟩
  · exact (yH_mul_Z hJ H hh (sHG_mem hJ H hh _) hz a).trans (yH_sHG hJ H hh _ a)
  · exact heisenberg_cocycle_mem_centre hJ H hh (y := fun a => (y a : Fin M → Af F ⊗[F] E))
      (y' := fun a => (y' a : Fin M → Af F ⊗[F] E)) (fun a => (y a).2) (fun a => (y' a).2)
      (fun a => ((y + y') a).2)
  · exact ⟨fun a => ⟨lin (Af F) σ J g (y a), H_isWp hJ H hh hg (y a).2⟩, fun a => rfl,
      H_conj_sHG hJ H hh hg _ _⟩

theorem heisenberg_parabolic_all : PI.LevelKSplit.W.NC.HeisPAll := by
  intro F E _ _ _ _ _ σ hσ M J _
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hσ.2.2.1]; norm_num)
  exact heisenberg_parabolic F E σ M J

end PI.LevelKSplit.W.NCH
end
end

section

noncomputable section

namespace PI.LevelKSplit.W.NCL

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField PI.LevelKSplit.W.NC PI.VolSemiDirect.W
open scoped TensorProduct

section Af

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} {r : ℕ}



theorem continuous_uT (P : Frame E M r) (a b : Fin r) :
    Continuous fun g : HA (Af F) σ J => uT (Af F) σ J P g a b := by
  have h1 : Continuous fun g : HA (Af F) σ J => lin (Af F) σ J g (ratV (F := F) (Af F) (P.e b)) :=
    PI.LevelKSplit.W.ExC.continuous_lin _
  have h0 : Continuous fun g : HA (Af F) σ J =>
      ((ratV (F := F) (Af F) (P.f a), lin (Af F) σ J g (ratV (F := F) (Af F) (P.e b))) :
        (Fin M → Af F ⊗[F] E) × (Fin M → Af F ⊗[F] E)) :=
    continuous_const.prodMk h1
  have h3 := PI.VolStabSW.continuous_hR (R := Af F) σ J
  have h2 := h3.comp h0
  unfold uT
  simp only [Matrix.of_apply]
  split_ifs
  · exact h2
  · exact continuous_const
  · exact continuous_const

theorem continuous_levL_mat (T : F) (P : Frame E M r) {X : Type} [TopologicalSpace X]
    {U W : X → Matrix (Fin r) (Fin r) (Af F ⊗[F] E)}
    (hU : ∀ a b, Continuous fun x => U x a b) (hW : ∀ a b, Continuous fun x => W x a b) :
    Continuous fun x => LinearMap.toMatrix' (levL (datR (Af F) σ J P T) (U x) (W x)) := by

  simp only [levL, map_add (f := _), map_sum, map_smul]
  refine (continuous_const.add (continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ =>
    (hU a b).smul continuous_const)).add
    (continuous_finsetSum _ fun d _ => continuous_finsetSum _ fun b _ => (hW d b).smul continuous_const)

theorem continuous_levG (hσσ : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J) (P : Frame E M r) (T : F)
    (hP : P.IsStd σ J T) : Continuous (levG (R := Af F) hσσ hJ hP) := by
  have hU : ∀ a b, Continuous fun g : HA (Af F) σ J => uT (Af F) σ J P g a b := continuous_uT P
  have hUm : Continuous fun g : HA (Af F) σ J => uT (Af F) σ J P g :=
    continuous_pi fun a => continuous_pi fun b => hU a b
  have hIm : Continuous fun g : HA (Af F) σ J => uI (Af F) σ J P g := by
    unfold uI
    exact hUm.matrix_adjugate
  have hI : ∀ a b, Continuous fun g : HA (Af F) σ J => uI (Af F) σ J P g a b := fun a b =>
    (continuous_apply b).comp ((continuous_apply a).comp hIm)
  have hcI : ∀ a b, Continuous fun g : HA (Af F) σ J => cj (Af F) σ (uI (Af F) σ J P g) a b := by
    intro a b
    unfold cj
    simp only [Matrix.of_apply]
    exact (PI.AdicCompletionValuation.continuous_sigR (R := Af F) σ).comp (hI b a)
  have hcT : ∀ a b, Continuous fun g : HA (Af F) σ J => cj (Af F) σ (uT (Af F) σ J P g) a b := by
    intro a b
    unfold cj
    simp only [Matrix.of_apply]
    exact (PI.AdicCompletionValuation.continuous_sigR (R := Af F) σ).comp (hU b a)
  have hM : Continuous fun g : HA (Af F) σ J =>
      LinearMap.toMatrix' (lin (Af F) σ J (levG hσσ hJ hP g)) := by
    simp only [lin_levG]
    exact continuous_levL_mat T P hU hcI
  have hMi : Continuous fun g : HA (Af F) σ J =>
      LinearMap.toMatrix' (lin (Af F) σ J (levG hσσ hJ hP g)⁻¹) := by
    have e : ∀ g : HA (Af F) σ J, lin (Af F) σ J (levG hσσ hJ hP g)⁻¹ =
        levL (datR (Af F) σ J P T) (uI (Af F) σ J P g) (cj (Af F) σ (uT (Af F) σ J P g)) :=
      fun g => LinearMap.ext fun x => by rw [lin_levG_inv]
    simp only [e]
    exact continuous_levL_mat T P hI hcT
  unfold levG
  apply Continuous.subtype_mk
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact hM.congr fun g => LinearMap.toMatrix'_toLin' _
  · exact hMi.congr fun g => LinearMap.toMatrix'_toLin' _

end Af

end PI.LevelKSplit.W.NCL
end
end

section

noncomputable section

namespace PI.LevelKSplit.W.NCA

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory Topology
open PI.LevelKSplit PI.LevelKSplit.W.NC PI.LevelKSplit.W.SemiA PI.VolSemiDirect.W
open scoped TensorProduct

theorem conjInv_of_one {X : Type} [Group X] [TopologicalSpace X] [MeasurableSpace X]
    [BorelSpace X] (N H : Subgroup X) (hN : LCSC N)
    (hex : ∀ h ∈ H, ∃ μ0 : Measure N, μ0.IsHaarMeasure ∧ ∀ f : X → ENNReal, Measurable f →
      ∫⁻ n, f (h * (n : X) * h⁻¹) ∂μ0 = ∫⁻ n, f (n : X) ∂μ0) : ConjInv N H := by
  obtain ⟨hlc, hsc, ht2, htg⟩ := hN
  intro μN hμN h hh f hf
  obtain ⟨μ0, hμ0, hinv⟩ := hex h hh
  rw [Measure.isMulLeftInvariant_eq_smul μN μ0, lintegral_smul_measure, lintegral_smul_measure,
    hinv f hf]

section Af

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [FiniteDimensional F E] {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E}

theorem conjNH_of (hC : NCoord F E σ M J) (hV : PI.LevelKSplit.W.CD.ModV F E σ M J) :
    PI.LevelKSplit.W.ExS.ConjNH F E σ M J := by
  intro hJ hσσ r P T hP
  have hsc : SecondCountableTopology (Af F) := PI.LevelKSplit.W.SC.finite_adeles_secondCountable F
  have hL : LCSC (HA (Af F) σ J) := PI.LevelKSplit.W.ExS.lcsc_HAf hsc
  have : BorelSpace (HA (Af F) σ J) := ⟨rfl⟩
  have : SecondCountableTopology (HA (Af F) σ J) := hL.2.1
  obtain ⟨-, cN, -⟩ := PI.LevelKSplit.W.ExC.closed_SNH hJ hσσ P T hP
  obtain ⟨lN, -⟩ := subgroup_locally_compact_holds (HA (Af F) σ J) ⊥ _ hL cN inferInstance inferInstance
  refine conjInv_of_one _ _ lN ?_
  intro h hh
  obtain ⟨A, Z, Ψ, cA, cZ, hleft, hconj⟩ := hC hJ hσσ r P T hP
  obtain ⟨⟨lcA, scA, t2A, tgA⟩, -⟩ :=
    subgroup_locally_compact_holds (HA (Af F) σ J) ⊥ A hL cA inferInstance inferInstance
  obtain ⟨⟨lcZ, scZ, t2Z, tgZ⟩, -⟩ :=
    subgroup_locally_compact_holds (HA (Af F) σ J) ⊥ Z hL cZ inferInstance inferInstance
  obtain ⟨lcN, scN, t2N, tgN⟩ := lN
  have : BorelSpace A := Subtype.borelSpace _
  have : BorelSpace Z := Subtype.borelSpace _
  have : BorelSpace (Nsub (Af F) σ J P) := Subtype.borelSpace _
  have : SecondCountableTopology (Af F ⊗[F] E) := sc_tens
  have : BorelSpace (Af F ⊗[F] E) := ⟨rfl⟩
  have : BorelSpace (Fin M → Af F ⊗[F] E) := Pi.borelSpace
  have H := SemiA.datR_hyp (R := Af F) hσσ hJ hP
  have cW : IsClosed ((Wp (Af F) σ J P : AddSubgroup (Fin M → Af F ⊗[F] E)) :
      Set (Fin M → Af F ⊗[F] E)) := by
    have e1 : ((Wp (Af F) σ J P : AddSubgroup (Fin M → Af F ⊗[F] E)) : Set (Fin M → Af F ⊗[F] E)) =
        {v | PI.LevelKSplit.W.NCA.DatL.pL (SemiA.datR (Af F) σ J P T) v = v} := by
      ext v
      exact mem_Wp_iff H v
    rw [e1]
    exact isClosed_eq (LinearMap.continuous_on_pi _) continuous_id
  have : LocallyCompactSpace (Wp (Af F) σ J P) := cW.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : SecondCountableTopology (Wp (Af F) σ J P) :=
    TopologicalSpace.secondCountableTopology_induced _ _ Subtype.val
  have : BorelSpace (Wp (Af F) σ J P) := Subtype.borelSpace _
  have : BorelSpace (Fin r → Wp (Af F) σ J P) := Pi.borelSpace
  have : BorelSpace ((Fin r → Wp (Af F) σ J P) × Z) := Prod.borelSpace
  have : BorelSpace (A × ((Fin r → Wp (Af F) σ J P) × Z)) := Prod.borelSpace
  let μA : Measure A := Measure.haar
  let μZ : Measure Z := Measure.haar
  let μW : Measure (Wp (Af F) σ J P) := Measure.addHaar
  let μQ : Measure (Fin r → Wp (Af F) σ J P) := Measure.pi fun _ => μW
  let ρ : Measure (A × ((Fin r → Wp (Af F) σ J P) × Z)) := μA.prod (μQ.prod μZ)
  have hΨm : Measurable Ψ := Ψ.continuous.measurable
  refine ⟨ρ.map Ψ, ?_, ?_⟩
  · have hli : (ρ.map Ψ).IsMulLeftInvariant := by
      refine ⟨fun n0 => ?_⟩
      obtain ⟨a0, t, c, ht, hc, hform⟩ := hleft n0
      have hcomm : (fun n => n0 * n) ∘ Ψ = Ψ ∘ (fun p : A × ((Fin r → Wp (Af F) σ J P) × Z) =>
          (a0 * p.1, (p.2.1 + t p.1, c (p.1, p.2.1) * p.2.2))) := by
        funext ⟨u, y, z⟩
        exact hform u y z
      have hinner : ∀ u : A, MeasurePreserving
          (fun q : (Fin r → Wp (Af F) σ J P) × Z => (q.1 + t u, c (u, q.1) * q.2))
          (μQ.prod μZ) (μQ.prod μZ) := by
        intro u
        refine (measurePreserving_add_right μQ (t u)).skew_product (g := fun y z => c (u, y) * z)
          ?_ (Filter.Eventually.of_forall fun y => map_mul_left_eq_self μZ (c (u, y)))
        exact (show Continuous fun q : (Fin r → Wp (Af F) σ J P) × Z => c (u, q.1) * q.2 from
          (hc.comp (continuous_const.prodMk continuous_fst)).mul continuous_snd).measurable
      have hgm : Continuous fun p : A × ((Fin r → Wp (Af F) σ J P) × Z) =>
          (p.2.1 + t p.1, c (p.1, p.2.1) * p.2.2) :=
        (continuous_snd.fst.add (ht.comp continuous_fst)).prodMk
          ((hc.comp (continuous_fst.prodMk continuous_snd.fst)).mul continuous_snd.snd)
      have hT : MeasurePreserving (fun p : A × ((Fin r → Wp (Af F) σ J P) × Z) =>
          (a0 * p.1, (p.2.1 + t p.1, c (p.1, p.2.1) * p.2.2))) ρ ρ :=
        (measurePreserving_mul_left μA a0).skew_product
          (g := fun (u : A) (q : (Fin r → Wp (Af F) σ J P) × Z) => (q.1 + t u, c (u, q.1) * q.2)) hgm.measurable
          (Filter.Eventually.of_forall fun u => (hinner u).map_eq)
      rw [Measure.map_map (measurable_const_mul n0) hΨm, hcomm, ← Measure.map_map hΨm hT.measurable,
        hT.map_eq]
    have hfc : IsFiniteMeasureOnCompacts (ρ.map Ψ) := Measure.IsFiniteMeasureOnCompacts.map ρ Ψ
    have hop : (ρ.map Ψ).IsOpenPosMeasure := Ψ.continuous.isOpenPosMeasure_map Ψ.surjective
    have := hfc
    have := hli
    have := hop
    exact Measure.IsHaarMeasure.mk
  · intro f hf
    have hF : Measurable fun n : Nsub (Af F) σ J P => f (h * (n : HA (Af F) σ J) * h⁻¹) :=
      hf.comp ((continuous_const.mul continuous_subtype_val).mul continuous_const).measurable
    have hF0 : Measurable fun n : Nsub (Af F) σ J P => f (n : HA (Af F) σ J) :=
      hf.comp continuous_subtype_val.measurable
    have hlinm : Measurable (linWp hh) :=
      (((LinearMap.continuous_on_pi (lin (Af F) σ J h)).comp continuous_subtype_val).subtype_mk
        _).measurable
    let Lq : (Fin r → Wp (Af F) σ J P) → (Fin r → Wp (Af F) σ J P) := fun y a => linWp hh (y a)
    have hLq : MeasurePreserving Lq μQ μQ :=
      measurePreserving_pi (fun _ => μW) (fun _ => μW)
        (fun _ => ⟨hlinm, wp_map hσσ hJ hP hV hh μW inferInstance⟩)
    have hT : MeasurePreserving (Prod.map id (Prod.map Lq id)) ρ ρ :=
      (MeasurePreserving.id μA).prod (hLq.prod (MeasurePreserving.id μZ))
    rw [lintegral_map hF hΨm, lintegral_map hF0 hΨm]
    calc ∫⁻ p, f (h * (Ψ p : HA (Af F) σ J) * h⁻¹) ∂ρ
        = ∫⁻ p, f (Ψ (Prod.map id (Prod.map Lq id) p) : HA (Af F) σ J) ∂ρ := by
          congr 1
          funext ⟨u, y, z⟩
          obtain ⟨y', hy', he⟩ := hconj h hh u y z
          have e2 : y' = Lq y := funext fun a => Subtype.ext (hy' a)
          show f (h * (Ψ (u, y, z) : HA (Af F) σ J) * h⁻¹) = f (Ψ (u, Lq y, z) : HA (Af F) σ J)
          rw [he, e2]
      _ = ∫⁻ p, f (Ψ p : HA (Af F) σ J) ∂ρ :=
          hT.lintegral_comp (show Measurable fun p => f (Ψ p : HA (Af F) σ J) from
            hf.comp (continuous_subtype_val.comp Ψ.continuous).measurable)

theorem normal_conjugation_hypothesis : NCAsm F E σ M J := fun hC hV => conjNH_of hC hV

end Af

theorem normal_conjugation_all : NCAsmAll := by
  intro F E _ _ _ _ _ σ hσ M J hJ
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hσ.2.2.1]; norm_num)
  exact normal_conjugation_hypothesis

end PI.LevelKSplit.W.NCA
end
end
