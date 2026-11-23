module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle055
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle060
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CmTypeRestrictRealSubfieldInfinitePlaceBijective
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsIsArchimedeanAdeleChartOfRealChart
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle033
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle211
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle079
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeckeCharacterOfUnitaryTensorIdeles
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle305
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle306
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle326
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle317
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle306
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle309
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle307
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle302
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RefilledStagesRecord
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle001
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
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TwDefs
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PointAtPlaceHom

open GlobalTheory.PointAtPlace

variable {D : D7} {θ : InfF D}

theorem infMat_mul (V : HSp D) (φ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (a b : GA D V) :
    infMat D.sp.cm.sig V.gram φ (a * b) = infMat D.sp.cm.sig V.gram φ a * infMat D.sp.cm.sig V.gram φ b :=
  archM_mul V φ a b

theorem infMat_one (V : HSp D) (φ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) :
    infMat D.sp.cm.sig V.gram φ 1 = 1 := archM_one V φ

theorem atTau_spec (hθ : IsInfFam θ) (V : HSp D) (τ : D.what₂.Tau) {g : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) : IsAtTau θ V τ g (atTau θ V τ g) := by
  have hu := existsUnique_isAtTau V τ θ hθ g hg
  unfold atTau
  rw [dite_eq_left hu.exists]
  exact hu.exists.choose_spec

theorem atTau_mem (V : HSp D) (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    atTau θ V τ g ∈ GinfC V := by
  unfold atTau
  split_ifs with h
  · exact h.choose_spec.1
  · exact one_mem _

theorem one_mem_UH {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ Formalism.QuantumDeterminants.UH H := by
  show (1 : Matrix (Fin n) (Fin n) ℂ)ᴴ * H * 1 = H
  simp

theorem mul_mem_UH {n : ℕ} {H g g' : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.QuantumDeterminants.UH H)
    (hg' : g' ∈ Formalism.QuantumDeterminants.UH H) : g * g' ∈ Formalism.QuantumDeterminants.UH H := by
  have h1 : gᴴ * H * g = H := hg
  have h2 : g'ᴴ * H * g' = H := hg'
  show (g * g')ᴴ * H * (g * g') = H
  calc (g * g')ᴴ * H * (g * g') = g'ᴴ * (gᴴ * H * g) * g' := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = H := by rw [h1, h2]

theorem atTau_one (hθ : IsInfFam θ) (V : HSp D) (τ : D.what₂.Tau) : atTau θ V τ 1 = 1 :=
  (existsUnique_isAtTau V τ θ hθ 1 (one_mem_UH _)).unique (atTau_spec hθ V τ (one_mem_UH _))
    ⟨one_mem _, infMat_one V _, fun _ _ => infMat_one V _⟩

theorem atTau_mul (hθ : IsInfFam θ) (V : HSp D) (τ : D.what₂.Tau) {g g' : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (hg' : g' ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) :
    atTau θ V τ (g * g') = atTau θ V τ g * atTau θ V τ g' := by
  have a := atTau_spec hθ V τ hg
  have b := atTau_spec hθ V τ hg'
  refine (existsUnique_isAtTau V τ θ hθ _ (mul_mem_UH hg hg')).unique (atTau_spec hθ V τ (mul_mem_UH hg hg'))
    ⟨mul_mem a.1 b.1, ?_, fun τ' h => ?_⟩
  · rw [infMat_mul, a.2.1, b.2.1]
  · rw [infMat_mul, a.2.2 τ' h, b.2.2 τ' h, Matrix.one_mul]

theorem comm_of_mem (V : HSp D) {a k : GA D V} (ha : a ∈ GinfC V) (hk : k ∈ GfC V) : a * k = k * a := by
  have a2 : finHom V a = 1 := ha
  have k1 : infHom V k = 1 := hk
  refine mul_inv_eq_one.1 (eq_one_of_mem V _ ?_ ?_)
  · show infHom V _ = 1
    simp only [map_mul, map_inv, k1, mul_one, one_mul, mul_inv_cancel]
  · show finHom V _ = 1
    simp only [map_mul, map_inv, a2, mul_one, one_mul, mul_inv_cancel]


open Classical in
theorem entry_eq {σ : (D.what₂.Tau → ℂ) →+ AE D} (hσ : GlobalTheory.FockCompare.Chart θ σ) (V : HSp D) (τ : D.what₂.Tau)
    {g : Matrix (Fin V.rank) (Fin V.rank) ℂ} {h : GA D V} (hh : IsAtTau θ V τ g h) (i j : Fin V.rank) :
    (matHom V h).1 i j = (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j +
      σ (Pi.single τ (g i j - (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ) i j)) := by
  refine sub_eq_zero.1 (hσ.ext _ ?_ fun τ' => ?_)
  · have a2 : (finHom V h).1 = (finHom V 1).1 := by rw [map_one]; exact congrArg Units.val hh.1
    have e : finPart D ((matHom V h).1 i j) = finPart D ((1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j) :=
      congrFun (congrFun a2 i) j
    rw [RingHom.map_sub, RingHom.map_add (f := _), hσ.fin, e, add_zero, sub_self]
  · have e1 : θ τ' (infPart D ((1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j)) =
        (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ) i j := congrFun (congrFun (infMat_one V (θ τ')) i) j
    have e2 : θ τ' (infPart D ((matHom V h).1 i j)) = infMat D.sp.cm.sig V.gram (θ τ') h i j := rfl
    rw [RingHom.map_sub, RingHom.map_add (f := _), RingHom.map_sub, RingHom.map_add (f := _), hσ.comp, e1, e2]
    by_cases c : τ' = τ
    · subst c
      rw [hh.2.1, Pi.single_eq_same]; ring
    · rw [hh.2.2 τ' c, Pi.single_eq_of_ne c]; ring

theorem isAtTau_inv (V : HSp D) (τ : D.what₂.Tau) {g : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) {h : GA D V} (hh : IsAtTau θ V τ g h) :
    IsAtTau θ V τ ((gramAt D V τ)⁻¹ * gᴴ * gramAt D V τ) h⁻¹ := by
  have hu : IsUnit (gramAt D V τ).det := by
    have : (gramAt D V τ).det = tauE D τ V.gram.det := (RingHom.map_det (tauE D τ) V.gram).symm
    rw [this]
    exact ((_root_.map_ne_zero _).2 (Formalism.L2.Theta.gram_det_ne V)).isUnit
  have h1 : gᴴ * gramAt D V τ * g = gramAt D V τ := hg
  have h2 : (gramAt D V τ)⁻¹ * gᴴ * gramAt D V τ * g = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, h1, Matrix.nonsing_inv_mul _ hu]
  have k : ∀ φ, infMat D.sp.cm.sig V.gram φ h * infMat D.sp.cm.sig V.gram φ h⁻¹ = 1 := fun φ => by
    rw [← infMat_mul, mul_inv_cancel, infMat_one]
  refine ⟨inv_mem hh.1, ?_, fun τ' c => ?_⟩
  · have := k (θ τ)
    rw [hh.2.1] at this
    rw [← Matrix.one_mul (infMat _ _ _ h⁻¹), ← h2, Matrix.mul_assoc _ g, this, Matrix.mul_one]
  · have := k (θ τ')
    rwa [hh.2.2 τ' c, Matrix.one_mul] at this

theorem continuousOn_atTau (hθ : IsInfFam θ) (V : HSp D) (τ : D.what₂.Tau) :
    ContinuousOn (atTau θ V τ) (Formalism.QuantumDeterminants.UH (gramAt D V τ)) := by
  classical
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  haveI : ContinuousAdd (AE D) := IsModuleTopology.toContinuousAdd (AF D.host.F) _
  have key : ∀ (i j : Fin V.rank), Continuous fun g : Matrix (Fin V.rank) (Fin V.rank) ℂ =>
      (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j +
        σ (Pi.single τ (g i j - (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ) i j)) := fun i j =>
    continuous_const.add (hσ.cont.comp ((continuous_single (A := fun _ : D.what₂.Tau => ℂ) τ).comp
      ((continuous_id.matrix_elem i j).sub continuous_const)))
  rw [continuousOn_iff_continuous_restrict]
  refine continuous_induced_rng.2 (Units.continuous_iff.2 ⟨?_, ?_⟩)
  · refine continuous_pi fun i => continuous_pi fun j => ?_
    refine ((key i j).comp continuous_subtype_val).congr fun g => ?_
    exact (entry_eq hσ V τ (atTau_spec hθ V τ g.2) i j).symm
  · refine continuous_pi fun i => continuous_pi fun j => ?_
    have c : Continuous fun g : Formalism.QuantumDeterminants.UH (gramAt D V τ) => (gramAt D V τ)⁻¹ * g.1ᴴ * gramAt D V τ :=
      (continuous_const.matrix_mul continuous_subtype_val.matrix_conjTranspose).matrix_mul continuous_const
    refine ((key i j).comp c).congr fun g => ?_
    exact (entry_eq hσ V τ (isAtTau_inv V τ g.2 (atTau_spec hθ V τ g.2)) i j).symm

theorem atTau_laws : ∀ (D : D7) (θ : InfF D), IsInfFam θ → ∀ (V : HSp D) (τ : D.what₂.Tau), (∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∃! h, IsAtTau θ V τ g h) ∧ atTau θ V τ 1 = 1 ∧ (∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ g' ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), atTau θ V τ (g * g') = atTau θ V τ g * atTau θ V τ g') ∧ (∀ g, ∀ k ∈ GfC V, atTau θ V τ g * k = k * atTau θ V τ g) ∧ ContinuousOn (atTau θ V τ) (Formalism.QuantumDeterminants.UH (gramAt D V τ)) :=
  fun _ θ hθ V τ => ⟨fun g hg => existsUnique_isAtTau V τ θ hθ g hg, atTau_one hθ V τ,
    fun _ hg _ hg' => atTau_mul hθ V τ hg hg', fun g _ hk => comm_of_mem V (atTau_mem V τ g) hk,
    continuousOn_atTau hθ V τ⟩

end GlobalTheory.PointAtPlaceHom

end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeckeInfExp



open GlobalTheory.FockCompare GlobalTheory.HeckeFinTrivial in
theorem hasInfQ_of_hasInfExp (D : D7) (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E) (e : D.what₂.Tau → ℚ)
    (hc : ChrEq c χ) (h : ∀ τ, HasInfExp D c τ (e τ)) : χ.HasInfQ (tauE D) e := by
  classical
  choose n hn hx using h
  refine ⟨n, hn, fun k => ?_⟩
  obtain ⟨⟨θ', hθ'⟩, -⟩ := GlobalTheory.Member.infiniteAdele_bijective D
  obtain ⟨θ, hθ⟩ : ∃ θ : GlobalTheory.Mem.Th.InfF D, IsInfFam θ := ⟨fun τ => θ' (tauE D τ), fun τ => hθ' _⟩
  obtain ⟨ρ, hρ, r1, r0⟩ := exists_real_chart D θ hθ (GlobalTheory.CMTypePlaces.places_bijective D)
  obtain ⟨s, hs⟩ := RealChart.exists_chart D θ hθ ρ hρ r1 r0
  obtain ⟨-, a, b, -, -, hab, ha, hb⟩ := GlobalTheory.IdeleParts.congr_open_and_parts D
  have ext : ∀ a b : AE D, finPart D a = finPart D b → (∀ τ, θ τ (infPart D a) = θ τ (infPart D b)) → a = b := by
    intro a b h1 h2
    rw [← sub_eq_zero]
    exact hs.ext _ (by rw [RingHom.map_sub, h1, sub_self]) fun τ => by
      rw [RingHom.map_sub, RingHom.map_sub, h2, sub_self]
  let t : (D.what₂.Tau → ℂˣ) → AE D := fun z => s (fun τ => (z τ : ℂ)) + (1 - s 1)
  have tf : ∀ z, finPart D (t z) = 1 := fun z => by
    simp only [t, RingHom.map_add (f := _), RingHom.map_sub, RingHom.map_one, hs.fin, zero_add, sub_zero]
  have ti : ∀ z τ, θ τ (infPart D (t z)) = z τ := fun z τ => by
    simp only [t, RingHom.map_add (f := _), RingHom.map_sub, RingHom.map_one, hs.comp, Pi.one_apply, sub_self, add_zero]
  let T : (D.what₂.Tau → ℂˣ) →* AE D :=
    { toFun := t
      map_one' := ext _ _ (by rw [tf, RingHom.map_one]) fun τ => by
        rw [ti, RingHom.map_one, RingHom.map_one]; rfl
      map_mul' := fun x y => ext _ _ (by rw [RingHom.map_mul, tf, tf, tf, mul_one]) fun τ => by
        rw [RingHom.map_mul, RingHom.map_mul, ti, ti, ti]; rfl }
  have hT : ∀ x : (AE D)ˣ, finPart D (x : AE D) = 1 →
      x = T.toHomUnits fun τ => Units.map ((θ τ).comp (infPart D)).toMonoidHom x := fun x hx =>
    Units.ext (ext _ _ (hx.trans (tf _).symm) fun τ =>
      (ti (fun τ => Units.map ((θ τ).comp (infPart D)).toMonoidHom x) τ).symm)
  have key : ∀ z : D.what₂.Tau → ℂˣ,
      ((c (T.toHomUnits z) : Circle) : ℂ) = ∏ τ, ((z τ : ℂ) / ((‖(z τ : ℂ)‖ : ℝ) : ℂ)) ^ n τ := by
    intro z
    have h1 : c (T.toHomUnits z) = ∏ τ, c (T.toHomUnits (Pi.mulSingle τ (z τ))) := by
      conv_lhs => rw [← Finset.univ_prod_mulSingle z]
      rw [map_prod, map_prod]
    have h2 := congrArg Circle.coeHom h1
    rw [map_prod] at h2
    refine h2.trans (Finset.prod_congr rfl fun τ _ => ?_)
    have h3 := (hx τ).2 θ hθ (T.toHomUnits (Pi.mulSingle τ (z τ))) (tf _) fun τ' hτ' =>
      (ti _ τ').trans (by rw [Pi.mulSingle_eq_of_ne hτ', Units.val_one])
    have h4 : θ τ (infPart D ((T.toHomUnits (Pi.mulSingle τ (z τ)) : (AE D)ˣ) : AE D)) = z τ :=
      (ti _ τ).trans (by rw [Pi.mulSingle_eq_same])
    rw [h4] at h3
    exact h3
  rw [← eq_inf D c χ hc k _ _ (hab _) (hb _).1 (hb _).2, hT _ (ha (Units.map (incA D).toMonoidHom k)).2, key]
  refine Finset.prod_congr rfl fun τ _ => ?_
  have h5 : ((Units.map ((θ τ).comp (infPart D)).toMonoidHom (a (Units.map (incA D).toMonoidHom k)) : ℂˣ) : ℂ) =
      tauE D τ (k : D.host.E) :=
    (congrArg (θ τ) (ha (Units.map (incA D).toMonoidHom k)).1).trans ((hθ τ).1 k)
  rw [h5]

theorem hasInfExp_iff_hasInfQ : ∀ (D : D7) (c : GlobalTheory.Mem.Th.IdC D) (χ : Formalism.L2.Host.HChar D.host.E) (a : D.what₂.Tau → ℚ),
    Formalism.IndefR.Links.ChrEq c χ → ((∀ τ, HasInfExp D c τ (a τ)) ↔ χ.HasInfQ (Formalism.L2.Host.embTau D) a) :=
  fun D c χ a hc => ⟨hasInfQ_of_hasInfExp D c χ a hc, hasInfExp_of_chrEq D c χ a hc⟩

end GlobalTheory.HeckeInfExp
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChrEqUnique

theorem eq_one_of_chrEq {D : D7} {c : (AE D)ˣ →* Circle} (h : ChrEq c 1) (x : (AE D)ˣ) : c x = 1 := by
  refine HeckeFinTrivial.eq_one_of_trivial_on_finite D c h.1 (fun y hy => ?_) x
  obtain ⟨j, h1, h2, h3⟩ := HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨N, hN, hprod⟩ := CharLocProd.char_eq_prod_locK D j h1 h2 (PlaceIdem.exists_isPlIdem D j h1 h2 h3) c 1 h
  obtain ⟨S, k, hS, hS'⟩ := finiteIdele_exists_local_approx D.host.E N hN
    (Units.map ((j : _ →+* _).comp (finPart D)).toMonoidHom y)
  exact Subtype.ext ((hprod y hy S k (fun P hP => ⟨(hS P hP).1, (hS P hP).2.1⟩) hS').trans
    (Finset.prod_eq_one fun P _ => rfl))

noncomputable def phase : ℂˣ →* Circle where
  toFun z := ⟨(z : ℂ) / ((‖(z : ℂ)‖ : ℝ) : ℂ), mem_sphere_zero_iff_norm.2 (by
    rw [norm_div, Complex.norm_real, norm_norm, div_self (norm_ne_zero_iff.2 z.ne_zero)])⟩
  map_one' := Circle.ext (by
    change ((1 : ℂˣ) : ℂ) / ((‖((1 : ℂˣ) : ℂ)‖ : ℝ) : ℂ) = 1
    simp)
  map_mul' x y := Circle.ext (by
    change ((x * y : ℂˣ) : ℂ) / ((‖((x * y : ℂˣ) : ℂ)‖ : ℝ) : ℂ) =
      (x : ℂ) / ((‖(x : ℂ)‖ : ℝ) : ℂ) * ((y : ℂ) / ((‖(y : ℂ)‖ : ℝ) : ℂ))
    rw [Units.val_mul, norm_mul, Complex.ofReal_mul, div_mul_div_comm])

theorem continuous_phase : Continuous phase :=
  Continuous.subtype_mk (Units.continuous_val.div (Complex.continuous_ofReal.comp Units.continuous_val.norm)
    fun z => Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 z.ne_zero)) _

noncomputable def normPow (t : ℝ) : ℂˣ →* Circle where
  toFun z := Circle.exp (t * Real.log ‖(z : ℂ)‖)
  map_one' := by simp
  map_mul' x y := by
    rw [Units.val_mul, norm_mul, Real.log_mul (norm_ne_zero_iff.2 x.ne_zero) (norm_ne_zero_iff.2 y.ne_zero), mul_add,
      Circle.exp_add]

theorem continuous_normPow (t : ℝ) : Continuous (normPow t) :=
  Circle.exp.continuous.comp (continuous_const.mul
    (Units.continuous_val.norm.log fun z => norm_ne_zero_iff.2 z.ne_zero))

theorem eq_one_of_forall {z : ℂˣ} (h : ∀ φ : ℂˣ →* Circle, Continuous φ → φ z = 1) : z = 1 := by
  have hn : ‖(z : ℂ)‖ = 1 := by
    by_contra hne
    have hl : Real.log ‖(z : ℂ)‖ ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one (norm_pos_iff.2 z.ne_zero) hne
    have h1 := h _ (continuous_normPow (Real.pi / Real.log ‖(z : ℂ)‖))
    change Circle.exp (_ * _) = 1 at h1
    rw [div_mul_cancel₀ _ hl] at h1
    have h2 := congrArg (fun w : Circle => (w : ℂ)) h1
    simp only [Circle.coe_exp, Complex.exp_pi_mul_I, Circle.coe_one] at h2
    norm_num at h2
  have h2 := congrArg (fun w : Circle => (w : ℂ)) (h _ continuous_phase)
  change (z : ℂ) / ((‖(z : ℂ)‖ : ℝ) : ℂ) = 1 at h2
  rw [hn, Complex.ofReal_one, div_one] at h2
  exact Units.ext h2

theorem hchar_eq_one (D : D7) (ξ : HChar D.host.E) (h : ∀ P k, ξ.locK P k = 1) : ξ = 1 := by
  obtain ⟨Φ, hΦ, -, h1, h2⟩ := GlobalTheory.HeckeTensorRead.exists_adele_tensor_equiv D
  let u : (AE D)ˣ →* Ideles D.host.E := Units.map Φ.toRingHom.toMonoidHom
  have hu : Continuous u := Continuous.units_map _ hΦ
  refine Subtype.ext (MonoidHom.ext fun y => eq_one_of_forall fun φ hφ => ?_)
  have hc : ChrEq (φ.comp (ξ.1.comp u)) (1 : HChar D.host.E) := by
    refine ⟨⟨hφ.comp (ξ.2.1.comp hu), fun k => ?_⟩, fun P e he k x hx => ?_⟩
    · have : u (Units.map (incA D).toMonoidHom k) = diagUnits D.host.E k := Units.ext (h1 k)
      change φ (ξ.1 (u _)) = 1
      rw [this, ξ.2.2, map_one]
    · have : u x = localIdele D.host.E P (atFin P k) := by
        refine Units.ext ?_
        change Φ (x : AE D) = _
        rw [hx, h2 P e he]
      have h3 : ξ.1 (localIdele D.host.E P (atFin P k)) = 1 := h P k
      change ((φ (ξ.1 (u x)) : Circle) : ℂ) = ((1 : ℂˣ) : ℂ)
      rw [this, h3, map_one]
      rfl
  have hy : u (Units.map Φ.symm.toRingHom.toMonoidHom y) = y := Units.ext (Φ.apply_symm_apply _)
  have := eq_one_of_chrEq hc (Units.map Φ.symm.toRingHom.toMonoidHom y)
  change φ (ξ.1 (u _)) = 1 at this
  rwa [hy] at this

theorem hchar_unique (D : D7) (c : IdC D) (χ χ' : HChar D.host.E) (h : ChrEq c χ) (h' : ChrEq c χ') : χ = χ' := by
  rw [← mul_inv_eq_one]
  refine hchar_eq_one D _ fun P k => ?_
  obtain ⟨Φ, -, -, -, h2⟩ := GlobalTheory.HeckeTensorRead.exists_adele_tensor_equiv D
  obtain ⟨j, j1, j2, j3⟩ := HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨e, he, -⟩ := PlaceIdem.exists_isPlIdem D j j1 j2 j3 P
  let x : (AE D)ˣ := Units.map Φ.symm.toRingHom.toMonoidHom (localIdele D.host.E P (atFin P k))
  have hx : (x : AE D) = locE D e (k : D.host.E) := Φ.symm_apply_eq.2 (h2 P e he k).symm
  change χ.locK P k * (χ'.locK P k)⁻¹ = 1
  rw [mul_inv_eq_one]
  exact Units.ext ((h.2 P e he k x hx).symm.trans (h'.2 P e he k x hx))

theorem idc_unique (D : D7) (c c' : IdC D) (χ : HChar D.host.E) (h : ChrEq c χ) (h' : ChrEq c' χ) : c = c' := by
  have hc : ChrEq (c * c'⁻¹ : (AE D)ˣ →* Circle) (1 : HChar D.host.E) := by
    refine ⟨⟨h.1.1.mul h'.1.1.inv, fun x => ?_⟩, fun P e he k x hx => ?_⟩
    · rw [MonoidHom.mul_apply, MonoidHom.inv_apply, h.1.2, h'.1.2, inv_one, one_mul]
    · change ((c x * (c' x)⁻¹ : Circle) : ℂ) = ((1 : ℂˣ) : ℂ)
      rw [Circle.coe_mul, Circle.coe_inv, h.2 P e he k x hx, h'.2 P e he k x hx, mul_inv_cancel₀ (Units.ne_zero _)]
      rfl
  exact MonoidHom.ext fun x => mul_inv_eq_one.1 (eq_one_of_chrEq hc x)

theorem isUnitary_of_chrEq (D : D7) (c : IdC D) (χ : HChar D.host.E) (h : ChrEq c χ) : χ.IsUnitary := by
  have hc := h.1
  obtain ⟨Φ, -, hΦ, h1, h2⟩ := GlobalTheory.HeckeTensorRead.exists_adele_tensor_equiv D
  let u : Ideles D.host.E →* (AE D)ˣ := Units.map Φ.symm.toRingHom.toMonoidHom
  have hu : Continuous u := Continuous.units_map _ hΦ
  have ht : Continuous (Circle.toUnits : Circle →* ℂˣ) :=
    Units.continuous_iff.2 ⟨continuous_subtype_val, by
      have h : Continuous fun z : Circle => ((z⁻¹ : Circle) : ℂ) := continuous_subtype_val.comp continuous_inv
      refine h.congr fun z => ?_
      simp⟩
  let χ' : HChar D.host.E := ⟨Circle.toUnits.comp (MonoidHom.comp c u), ht.comp (hc.1.comp hu), fun k => by
    have : u (diagUnits D.host.E k) = Units.map (incA D).toMonoidHom k :=
      Units.ext (Φ.symm_apply_eq.2 (h1 k).symm)
    change Circle.toUnits (c (u _)) = 1
    rw [this, hc.2, map_one]⟩
  have h' : ChrEq c χ' := ⟨hc, fun P e he k x hx => by
    have : x = u (localIdele D.host.E P (atFin P k)) :=
      Units.ext (Φ.eq_symm_apply.2 (by rw [hx, h2 P e he k]))
    rw [this]
    rfl⟩
  rw [hchar_unique D c χ χ' h h']
  exact fun x => Circle.norm_coe (c (u x))

theorem chrEq_unique : ∀ (D : D7), (∀ (c : IdC D) (χ χ' : Formalism.L2.Host.HChar D.host.E), Formalism.IndefR.Links.ChrEq c χ → Formalism.IndefR.Links.ChrEq c χ' → χ = χ') ∧ (∀ (c c' : IdC D) (χ : Formalism.L2.Host.HChar D.host.E), Formalism.IndefR.Links.ChrEq c χ → Formalism.IndefR.Links.ChrEq c' χ → c = c') ∧ ∀ (c : IdC D) (χ : Formalism.L2.Host.HChar D.host.E), Formalism.IndefR.Links.ChrEq c χ → χ.IsUnitary :=
  fun D => ⟨hchar_unique D, idc_unique D, isUnitary_of_chrEq D⟩

end GlobalTheory.ChrEqUnique
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

namespace GlobalTheory.DefU.AU

theorem isLoc_unique_of_isSplitAt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : AU E n)
    (w : HeightOneSpectrum (𝓞 E)) (σ σ' : Irr (GL (Fin n) (w.adicCompletion E))),
    IsSplitAt w → π.IsLoc w σ → π.IsLoc w σ' → σ = σ' := by
  intro E _ _ _ n π w σ σ' hw h h'
  obtain ⟨U, rfl⟩ := AU.mk_surjective π
  obtain ⟨σ, rfl⟩ := Quotient.exists_rep (s := SmIrr.setoid _) σ
  obtain ⟨σ', rfl⟩ := Quotient.exists_rep (s := SmIrr.setoid _) σ'
  obtain ⟨e, he⟩ := GlobalTheory.T.splitPlace_unitaryLocalPoints_equiv_GL E n w hw
  obtain ⟨r, -, -, hc⟩ := GlobalTheory.T.exists_continuous_retraction_onto_unitaryLocalPoints E n w
  let s : GL (Fin n) (w.adicCompletion E) →* UA E n :=
    (locU n w).subtype.comp e.symm.toMulEquiv.toMonoidHom
  have hs : ∀ y, cLoc w (s y) = y := fun y => by
    have := he (e.symm y)
    rw [e.apply_symm_apply] at this
    exact this.symm
  have key : ∀ τ : SmIrr (GL (Fin n) (w.adicCompletion E)), U.IsLocComp w τ →
      ∃ f : τ.ρ.IntertwiningMap (U.rep.comp s), f ≠ 0 := by
    rintro τ ⟨-, f, h0, hf, h2⟩
    refine ⟨⟨f.codRestrict U.V hf, fun y => LinearMap.ext fun v => Subtype.ext ?_⟩, fun e0 => h0 ?_⟩
    · have h3 := h2 (e.symm y) v
      have hy : ((cLoc w).comp (locU n w).subtype) (e.symm y) = y := hs y
      rw [hy] at h3
      exact h3
    · exact LinearMap.ext fun v => congrArg Subtype.val (DFunLike.congr_fun e0 v)
  obtain ⟨f, hf⟩ := key σ h
  obtain ⟨f', hf'⟩ := key σ' h'
  have hcomm : ∀ g : UA E n, ∃ u, ∀ y, Commute ((s u)⁻¹ * g) (s y) := fun g =>
    ⟨e (r g), fun y => by
      have : s (e (r g)) = (r g : UA E n) := congrArg Subtype.val (e.symm_apply_apply (r g))
      rw [this]
      exact hc g (e.symm y)⟩
  exact Quotient.sound ((GlobalTheory.T.irreducibleRep_isotypic_of_centraliser_factor _ _ _ _ _ U.rep s σ.ρ σ'.ρ U.isIrreducible_rep σ.irred σ'.irred hcomm f hf).2 f' hf')

end GlobalTheory.DefU.AU
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial


theorem _root_.GlobalTheory.T.exists_span_eq_one_mod_of_splits_in_rayClassField : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (𝔮 : Ideal (𝓞 K)),
    GlobalTheory.Mem.Fld.IsRayField K L 𝔮 → ∀ 𝔭 : HeightOneSpectrum (𝓞 K), ¬ 𝔭.asIdeal ∣ 𝔮 →
      (𝔭.asIdeal.primesOver (𝓞 L)).ncard = Module.finrank K L →
        ∃ π : 𝓞 K, 𝔭.asIdeal = Ideal.span {π} ∧ π - 1 ∈ 𝔮 := by
  first | exact @GlobalTheory.Mem.RaySplit.exists_span_eq_of_splits | exact GlobalTheory.Mem.RaySplit.exists_span_eq_of_splits | (intros; apply GlobalTheory.Mem.RaySplit.exists_span_eq_of_splits <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.Mem GlobalTheory.Mem.SRe

namespace GlobalTheory.Mem.SRe

theorem real_reS : ∀ (D : D7) (Z : SNew D), (Formalism.L2.Theta.RealTied D → Formalism.L2.Theta.RealTied (reS D Z)) ∧ StandardLattice.DstarD (reS D Z) = StandardLattice.DstarD D ∧ (StandardLattice.VolumeEqMass₂ D → StandardLattice.VolumeEqMass₂ (reS D Z)) :=
  fun _ _ => ⟨fun h => ⟨h.cdScale, h.dsig, h.dsig_all, h.vol⟩, rfl, fun h => h⟩

end GlobalTheory.Mem.SRe
end
