module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SelfReciprocalLocalField
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.QuadraticClassFieldTheory
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetGramRatOneNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedGLMassFormula
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1784
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle047
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle547
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle576
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle005
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle009
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankPosOfLeaves
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle578
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle003
import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1778
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLemmas.ToComplBijective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle403

@[expose] public section

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField PositivityTheory.BCUSide.HermitianLocalForms

noncomputable section

namespace GlobalTheory.CompanionTheory.NormClassNorm

theorem norm_mem_normGroup : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (k : Type) [Field k]
    [Algebra (maximalRealSubfield E) k] (r : ℕ) (Q : SelfRecip E r)
    (x : (k ⊗[(maximalRealSubfield E)] plus Q)ˣ), x ∈ norms Q k →
    Units.map (Algebra.norm k : k ⊗[(maximalRealSubfield E)] plus Q →* k) x ∈
      GlobalTheory.QuadSymbol.normGroup (maximalRealSubfield E) E k := by
  intro E _ _ _ k _ _ r Q x hx
  obtain ⟨z, hz⟩ : ∃ z : E, IsCMField.complexConj E z ≠ z := by
    by_contra h
    push Not at h
    exact IsCMField.complexConj_ne_one E (AlgEquiv.ext h)
  have hθ : IsCMField.complexConj E (z - IsCMField.complexConj E z) =
      -(z - IsCMField.complexConj E z) := by
    rw [map_sub, IsCMField.complexConj_apply_apply]; ring
  obtain ⟨b, B, hB⟩ := GlobalTheory.TraceClasses.exists_bases Q (sub_ne_zero.2 hz.symm) hθ
  have h1 : Isometric Q k (GlobalTheory.TraceClasses.gramRat Q B 1)
      ((1 : (k ⊗[(maximalRealSubfield E)] plus Q)ˣ) : k ⊗[(maximalRealSubfield E)] plus Q) := by
    have := (GlobalTheory.TraceClasses.isometric_tmul_iff Q B k (GlobalTheory.TraceClasses.gramRat Q B 1) 1).2
      (GlobalTheory.HermLocal.CongrOver.of_congr ⟨1, by simp, by simp⟩)
    simpa [Algebra.TensorProduct.one_def] using this
  have h2 := Isometric.of_norm Q k hx h1
  rw [one_mul] at h2
  have h3 := GlobalTheory.TraceClasses.norm_div_mem Q hB k (δ := 1) (by simp) h2
  have h4 : GlobalTheory.QuadSymbol.toUnits (maximalRealSubfield E) k 1 = 1 := map_one _
  rwa [h4, div_one] at h3

end GlobalTheory.CompanionTheory.NormClassNorm

end
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.TwCentNorm

open GlobalTheory.ClassParam (krylov)
open GlobalTheory.MassNorm

section Core

variable {R : Type} [CommRing R] {m : ℕ}

def PhiU (m : ℕ) (R : Type) [CommRing R] : GL (Fin m) R :=
  ⟨GlobalTheory.Tw.Phi m R, (GlobalTheory.Tw.Phi m R)ᵀ, Phi_mul_transpose m R, PhiT_mul_Phi⟩

def DJ (J : GL (Fin m) R) : GL (Fin m) R := J⁻¹ * (PhiU m R)⁻¹

theorem psi_DJ (c : R →+* R) (J : GL (Fin m) R) (x : Matrix (Fin m) (Fin m) R) :
    psi c (DJ J) x = (J⁻¹).val * cT c x * J.val := by
  have h1 : ((PhiU m R)⁻¹).val = (GlobalTheory.Tw.Phi m R)ᵀ := rfl
  have h2 : (DJ J).val = (J⁻¹).val * (GlobalTheory.Tw.Phi m R)ᵀ := by
    rw [DJ, Units.val_mul, h1]
  have h3 : ((DJ J)⁻¹).val = GlobalTheory.Tw.Phi m R * J.val := by
    rw [DJ, _root_.mul_inv_rev, inv_inv, inv_inv, Units.val_mul]; rfl
  rw [psi, h2, h3]
  have hP := PhiT_mul_Phi (m := m) (R := R)
  calc _ = (J⁻¹).val * ((GlobalTheory.Tw.Phi m R)ᵀ * GlobalTheory.Tw.Phi m R) * (c.mapMatrix x)ᵀ *
        ((GlobalTheory.Tw.Phi m R)ᵀ * GlobalTheory.Tw.Phi m R) * J.val := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hP, Matrix.mul_one, Matrix.mul_one]; rfl

theorem mem_UJ_iff (c : R →+* R) (J g : GL (Fin m) R) :
    g ∈ UJ c J.val ↔ psi c (DJ J) g.val = (g⁻¹).val := by
  rw [psi_DJ]
  have hJ : J.val * (J⁻¹).val = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hJ' : (J⁻¹).val * J.val = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hg : g.val * (g⁻¹).val = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hg' : (g⁻¹).val * g.val = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  change cT c g.val * J.val * g.val = J.val ↔ _
  constructor
  · intro h
    calc (J⁻¹).val * cT c g.val * J.val
        = (J⁻¹).val * (cT c g.val * J.val * g.val) * (g⁻¹).val := by
          simp only [Matrix.mul_assoc]; rw [hg, Matrix.mul_one]
      _ = _ := by rw [h, hJ', Matrix.one_mul]
  · intro h
    calc cT c g.val * J.val * g.val
        = J.val * ((J⁻¹).val * cT c g.val * J.val) * g.val := by
          simp only [← Matrix.mul_assoc]; rw [hJ, Matrix.one_mul]
      _ = _ := by rw [h, Matrix.mul_assoc, hg', Matrix.mul_one]

theorem psi_norm (c : R →+* R) (hc : ∀ x, c (c x) = x) (D : GL (Fin m) R) :
    psi c D (D * thetaGL m c D).val = ((D * thetaGL m c D)⁻¹).val := by
  have hθ : ∀ g, thetaGL m c (thetaGL m c g) = g := GlobalTheory.LocTwist.thetaGL_thetaGL m c hc
  rw [psi_units]
  congr 1
  simp only [_root_.mul_inv_rev, map_mul, map_inv, hθ]
  group

theorem mem_twCent_iff (c : R →+* R) (D g : GL (Fin m) R) :
    g ∈ twCent (thetaGL m c) D ↔ psi c D g.val = (g⁻¹).val := by
  rw [psi_units]
  constructor
  · intro h
    have h' : g⁻¹ * D = D * thetaGL m c g⁻¹ := (twCent (thetaGL m c) D).inv_mem h
    congr 1
    rw [← h']; group
  · intro h
    have h' : D * thetaGL m c g⁻¹ * D⁻¹ = g⁻¹ := Units.ext h
    have : g⁻¹ ∈ twCent (thetaGL m c) D := by
      change g⁻¹ * D = D * thetaGL m c g⁻¹
      calc g⁻¹ * D = (D * thetaGL m c g⁻¹ * D⁻¹) * D := by rw [h']
        _ = _ := by group
    simpa using (twCent (thetaGL m c) D).inv_mem this

theorem commute_of_mem_twCent (c : R →+* R) (hc : ∀ x, c (c x) = x) (D g : GL (Fin m) R)
    (hg : g ∈ twCent (thetaGL m c) D) : g * (D * thetaGL m c D) = (D * thetaGL m c D) * g := by
  have hθ : ∀ g, thetaGL m c (thetaGL m c g) = g := GlobalTheory.LocTwist.thetaGL_thetaGL m c hc
  have h1 : g * D = D * thetaGL m c g := hg
  have h2 : thetaGL m c g = D⁻¹ * g * D := by rw [mul_assoc, h1]; group
  have h3 := congrArg (thetaGL m c) h2
  rw [hθ, map_mul, map_mul, map_inv, h2] at h3
  calc g * (D * thetaGL m c D)
      = (D * thetaGL m c D) * ((thetaGL m c D)⁻¹ * (D⁻¹ * g * D) * thetaGL m c D) := by group
    _ = _ := by rw [← h3]

theorem mem_twCent_iff_mem_UJ (c : R →+* R) (hc : ∀ x, c (c x) = x) (D J : GL (Fin m) R)
    (hN : D * thetaGL m c D ∈ UJ c J.val) (v : Fin m → R)
    (hv : IsUnit (krylov (D * thetaGL m c D).val v).det) (g : GL (Fin m) R) :
    g ∈ twCent (thetaGL m c) D ↔
      g ∈ UJ c J.val ∧ g * (D * thetaGL m c D) = (D * thetaGL m c D) * g := by
  have key : g * (D * thetaGL m c D) = (D * thetaGL m c D) * g →
      psi c D g.val = psi c (DJ J) g.val := by
    intro hcomm
    obtain ⟨p, hp⟩ := aeval_of_commute_cyclic v hv (N := g.val) (by
      change g.val * (D * thetaGL m c D).val = (D * thetaGL m c D).val * g.val
      rw [← Units.val_mul, ← Units.val_mul, hcomm])
    rw [hp, psi_aeval, psi_aeval, psi_norm c hc, (mem_UJ_iff c J _).1 hN]
  constructor
  · intro hg
    have hcomm := commute_of_mem_twCent c hc D g hg
    refine ⟨?_, hcomm⟩
    rw [mem_UJ_iff, ← key hcomm]
    exact (mem_twCent_iff c D g).1 hg
  · rintro ⟨hg, hcomm⟩
    rw [mem_twCent_iff, key hcomm]
    exact (mem_UJ_iff c J g).1 hg

end Core

section Global

variable (E : Type) [Field E] [NumberField E] [IsCMField E]

theorem cT_map_algebraMap {m : ℕ} (M : Matrix (Fin m) (Fin m) E) :
    cT (conjFin (IsCMField.complexConj E).toRingEquiv) (M.map (algebraMap E (Af E))) =
      (cT (IsCMField.complexConj E).toRingEquiv.toRingHom M).map (algebraMap E (Af E)) := by
  ext i j
  simp [cT, conjFin_algebraMap]

theorem mem_twCent_ratF_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (δ : GL (Fin n) E) (H : Matrix (Fin n) (Fin n) E),
  (δ * thE E n δ).val.charpoly.Separable → IsUnit H.det →
  δ * thE E n δ ∈ UJ (IsCMField.complexConj E).toRingEquiv.toRingHom H →
  ∀ g : GL (Fin n) (Af E), g ∈ twCent (thF E n) (ratF E n δ) ↔
    g ∈ UJ (conjFin (IsCMField.complexConj E).toRingEquiv) (H.map (algebraMap E (Af E))) ∧
      g * ratF E n (δ * thE E n δ) = ratF E n (δ * thE E n δ) * g := by
  intro E _ _ _ n δ H hs hH hU g
  have hc : ∀ y, conjFin (IsCMField.complexConj E).toRingEquiv (conjFin (IsCMField.complexConj E).toRingEquiv y) = y :=
    fun y => GlobalTheory.ThetaPull.cFin_cFin y
  have hNorm : ratF E n δ * thetaGL n (conjFin (IsCMField.complexConj E).toRingEquiv) (ratF E n δ) =
      ratF E n (δ * thE E n δ) := by
    change ratF E n δ * thF E n (ratF E n δ) = _
    rw [GlobalTheory.MassNorm.thF_ratF, map_mul]
  have hdet : IsUnit (H.map (algebraMap E (Af E))).det := by
    have h1 := hH.map (algebraMap E (Af E))
    rwa [RingHom.map_det, RingHom.mapMatrix_apply] at h1
  let J : GL (Fin n) (Af E) := Matrix.nonsingInvUnit _ hdet
  have hJ : J.val = H.map (algebraMap E (Af E)) := rfl
  have hU' : ratF E n (δ * thE E n δ) ∈
      UJ (conjFin (IsCMField.complexConj E).toRingEquiv) (H.map (algebraMap E (Af E))) := by
    have h0 : cT (IsCMField.complexConj E).toRingEquiv.toRingHom (δ * thE E n δ).val * H * (δ * thE E n δ).val = H := hU
    change cT _ (ratF E n (δ * thE E n δ)).val * _ * (ratF E n (δ * thE E n δ)).val = _
    have hv : (ratF E n (δ * thE E n δ)).val = (δ * thE E n δ).val.map (algebraMap E (Af E)) := rfl
    rw [hv, cT_map_algebraMap]
    conv_rhs => rw [← h0]
    simp only [Matrix.map_mul]
  obtain ⟨v, hv⟩ := GlobalTheory.ClassParam.exists_cyclic_field _ hs
  have hv' : IsUnit (krylov (ratF E n δ * thetaGL n (conjFin (IsCMField.complexConj E).toRingEquiv) (ratF E n δ)).val
      (algebraMap E (Af E) ∘ v)).det := by
    have h1 := (IsUnit.mk0 _ hv).map (algebraMap E (Af E))
    rw [RingHom.map_det, RingHom.mapMatrix_apply, GlobalTheory.ClassParam.krylov_map] at h1
    rw [hNorm]
    exact h1
  have := mem_twCent_iff_mem_UJ _ hc (ratF E n δ) J (by rw [hNorm, hJ]; exact hU') _ hv' g
  rw [hNorm, hJ] at this
  exact this

end Global

end GlobalTheory.CompanionTheory.TwCentNorm
end
end

section

noncomputable section

open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CompanionTheory.SmoothRep
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.TypeSpace

section Abstract

variable {K X : Type*} [Group K] [NormedAddCommGroup X] [InnerProductSpace ℂ X]

def restrictRep (π : K →* (X →L[ℂ] X)) (Y : Submodule ℂ X) (hY : ∀ g, ∀ v ∈ Y, π g v ∈ Y) :
    Representation ℂ K Y where
  toFun g := ((π g : X →L[ℂ] X) : X →ₗ[ℂ] X).restrict (hY g)
  map_one' := by ext v; simp
  map_mul' g h := by ext v; simp

theorem span_orbit_stable' (π : K →* (X →L[ℂ] X)) (F : X) (g : K) :
    ∀ v ∈ Submodule.span ℂ (Set.range fun k : K => π k F),
      π g v ∈ Submodule.span ℂ (Set.range fun k : K => π k F) := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    refine Submodule.subset_span ⟨g * k, ?_⟩
    simp [map_mul]
  | zero => simp
  | add x y _ _ hx hy => simpa using add_mem hx hy
  | smul c x _ hx => simpa using Submodule.smul_mem _ c hx

end Abstract

theorem exists_typeSpace : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (H : Submodule ℂ (L2 (latticeGL E a) μ)), H ≤ L2cusp μ → IsIrredSubrep (R (latticeGL E a) μ) H → ∀ F ∈ H, IsKFinL2 μ F → ∃ U : Subgroup (GL (Fin a) (Af E)), IsOpen (U : Set (GL (Fin a) (Af E))) ∧ IsCompact (U : Set (GL (Fin a) (Af E))) ∧ ∃ X : Submodule ℂ (L2 (latticeGL E a) μ), FiniteDimensional ℂ X ∧ F ∈ X ∧ X ≤ H ∧ (∀ (k : Kinf E a), ∀ v ∈ X, R (latticeGL E a) μ (infGL E a (Unitary.toUnits k)) v ∈ X) ∧ (∀ u ∈ U, ∀ v ∈ X, R (latticeGL E a) μ (finGL E a u) v = v) ∧ ∀ B : L2 (latticeGL E a) μ →ₗ[ℂ] L2 (latticeGL E a) μ, (∀ (k : Kinf E a) v, B (R (latticeGL E a) μ (infGL E a (Unitary.toUnits k)) v) = R (latticeGL E a) μ (infGL E a (Unitary.toUnits k)) (B v)) → (∀ v ∈ H, (∀ u ∈ U, R (latticeGL E a) μ (finGL E a u) v = v) → B v ∈ H ∧ ∀ u ∈ U, R (latticeGL E a) μ (finGL E a u) (B v) = B v) → ∀ v ∈ X, B v ∈ X := by
  intro E _ _ _ a μ _ _ H hH hI F hFH hK
  obtain ⟨hSo, hfd⟩ := hK
  obtain ⟨K0, hK0o, hK0c⟩ := GlobalTheory.GLIntegral.exists_isOpen_isCompact E a

  let S : Subgroup (GL (Fin a) (Af E)) :=
    { carrier := {k | R (latticeGL E a) μ (finGL E a k) F = F}
      mul_mem' := fun {x y} hx hy => by
        have hx' : R (latticeGL E a) μ (finGL E a x) F = F := hx
        have hy' : R (latticeGL E a) μ (finGL E a y) F = F := hy
        change R (latticeGL E a) μ (finGL E a (x * y)) F = F
        rw [map_mul, map_mul, ContinuousLinearMap.mul_apply, hy', hx']
      one_mem' := by
        change R (latticeGL E a) μ (finGL E a 1) F = F
        simp
      inv_mem' := fun {x} hx => by
        have hx' : R (latticeGL E a) μ (finGL E a x) F = F := hx
        change R (latticeGL E a) μ (finGL E a x⁻¹) F = F
        conv_lhs => rw [← hx']
        rw [← ContinuousLinearMap.mul_apply, ← map_mul, ← map_mul, inv_mul_cancel]
        simp }
  have hSo' : IsOpen (S : Set (GL (Fin a) (Af E))) := hSo
  let U : Subgroup (GL (Fin a) (Af E)) := K0 ⊓ S
  have hUo : IsOpen (U : Set (GL (Fin a) (Af E))) := hK0o.inter hSo'
  have hUc : IsCompact (U : Set (GL (Fin a) (Af E))) := hK0c.inter_right (S.isClosed_of_isOpen hSo')

  let π : Kinf E a →* (L2 (latticeGL E a) μ →L[ℂ] L2 (latticeGL E a) μ) :=
    (R (latticeGL E a) μ).comp ((infGL E a).comp Unitary.toUnits)
  have hcomm : ∀ (u : GL (Fin a) (Af E)) (k : Kinf E a) (v : L2 (latticeGL E a) μ),
      R (latticeGL E a) μ (finGL E a u) (π k v) = π k (R (latticeGL E a) μ (finGL E a u) v) := by
    intro u k v
    have e := congrArg (fun g => R (latticeGL E a) μ g v) (infGL_comm (E := E) (a := a) (Unitary.toUnits k) u)
    simp only [map_mul, ContinuousLinearMap.mul_apply] at e
    exact e.symm
  let Y : Submodule ℂ (L2 (latticeGL E a) μ) := Submodule.span ℂ (Set.range fun k : Kinf E a => π k F)
  haveI : FiniteDimensional ℂ Y := hfd
  have hYs : ∀ g, ∀ v ∈ Y, π g v ∈ Y := span_orbit_stable' π F
  have hFY : F ∈ Y := Submodule.subset_span ⟨1, by simp⟩
  have hYP : ∀ v ∈ Y, v ∈ H ∧ ∀ u ∈ U, R (latticeGL E a) μ (finGL E a u) v = v := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      refine ⟨hI.1.2 _ _ hFH, fun u hu => ?_⟩
      exact (hcomm u k F).trans (congrArg (π k) hu.2)
    | zero => exact ⟨H.zero_mem, fun _ _ => map_zero _⟩
    | add x y _ _ hx hy =>
      exact ⟨H.add_mem hx.1 hy.1, fun u hu => by rw [map_add (f := _), hx.2 u hu, hy.2 u hu]⟩
    | smul c x _ hx =>
      exact ⟨H.smul_mem c hx.1, fun u hu => by rw [map_smul, hx.2 u hu]⟩
  let ρ : Representation ℂ (Kinf E a) Y := restrictRep π Y hYs
  let C : (Y →ₗ[ℂ] L2 (latticeGL E a) μ) → Prop := fun T =>
    (∀ k w, T (ρ k w) = R (latticeGL E a) μ (infGL E a (Unitary.toUnits k)) (T w)) ∧
      ∀ w, T w ∈ H ∧ ∀ u ∈ U, R (latticeGL E a) μ (finGL E a u) (T w) = T w
  let X : Submodule ℂ (L2 (latticeGL E a) μ) := ⨆ (T : Y →ₗ[ℂ] L2 (latticeGL E a) μ) (_ : C T), LinearMap.range T
  have hXf : FiniteDimensional ℂ X := GlobalTheory.T.cuspidal_K_type_finite E a μ H hH hI U hUo Y ρ
  have hmem : ∀ T, C T → ∀ w, T w ∈ X := fun T hT w =>
    (le_iSup₂_of_le (f := fun (T : Y →ₗ[ℂ] L2 (latticeGL E a) μ) (_ : C T) => LinearMap.range T) T hT le_rfl)
      ⟨w, rfl⟩
  have hXP : ∀ v ∈ X, v ∈ H ∧ ∀ u ∈ U, R (latticeGL E a) μ (finGL E a u) v = v := by
    intro v hv
    let P : Submodule ℂ (L2 (latticeGL E a) μ) :=
      { carrier := {v | v ∈ H ∧ ∀ u ∈ U, R (latticeGL E a) μ (finGL E a u) v = v}
        zero_mem' := ⟨H.zero_mem, fun _ _ => map_zero _⟩
        add_mem' := fun {x y} hx hy =>
          ⟨H.add_mem hx.1 hy.1, fun u hu => by rw [map_add (f := _), hx.2 u hu, hy.2 u hu]⟩
        smul_mem' := fun c x hx => ⟨H.smul_mem c hx.1, fun u hu => by rw [map_smul, hx.2 u hu]⟩ }
    have hle : X ≤ P := iSup₂_le fun T hT => by
      rintro _ ⟨w, rfl⟩
      exact hT.2 w
    exact hle hv
  refine ⟨U, hUo, hUc, X, hXf, ?_, fun v hv => (hXP v hv).1, ?_, fun u hu v hv => (hXP v hv).2 u hu, ?_⟩
  · exact hmem Y.subtype ⟨fun k w => rfl, fun w => hYP _ w.2⟩ ⟨F, hFY⟩
  · intro k v hv
    have hle : X ≤ X.comap ((R (latticeGL E a) μ (infGL E a (Unitary.toUnits k)) :
        L2 (latticeGL E a) μ →L[ℂ] L2 (latticeGL E a) μ) : L2 (latticeGL E a) μ →ₗ[ℂ] L2 (latticeGL E a) μ) :=
      iSup₂_le fun T hT => by
        rintro _ ⟨w, rfl⟩
        change R (latticeGL E a) μ (infGL E a (Unitary.toUnits k)) (T w) ∈ X
        rw [← hT.1 k w]
        exact hmem T hT _
    exact hle hv
  · intro B hB1 hB2 v hv
    have hle : X ≤ X.comap B := iSup₂_le fun T hT => by
      rintro _ ⟨w, rfl⟩
      refine hmem (B ∘ₗ T) ⟨fun k w => ?_, fun w => hB2 _ (hT.2 w).1 (hT.2 w).2⟩ w
      change B (T (ρ k w)) = _
      rw [hT.1 k w, hB1]
      rfl
    exact hle hv

end GlobalTheory.CompanionTheory.TypeSpace

end
end

section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.LimV.NodeApply

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {r s : ℕ}

theorem levi_eq_mul_cf (u u' : BlockIx (r + s) r → Ad E) (m m' : GA E r × GA E s) (k k' : Kinf E (r + s))
    (c c' : GL (Fin (r + s)) (Af E)) (hc : c ∈ KO E (r + s)) (hc' : c' ∈ KO E (r + s))
    (h : unip u * lev (Ad E) r s m * cf (r + s) k c = unip u' * lev (Ad E) r s m' * cf (r + s) k' c') :
    ∃ (k₁ : Kinf E r) (c₁ : GL (Fin r) (Af E)) (k₂ : Kinf E s) (c₂ : GL (Fin s) (Af E)),
      c₁ ∈ KO E r ∧ c₂ ∈ KO E s ∧ m' = (m.1 * cf r k₁ c₁, m.2 * cf s k₂ c₂) := by
  obtain ⟨v, hv⟩ := lev_mul_unip (m⁻¹) (-u + u')
  have hu : (unip u : GA E (r + s))⁻¹ = unip (-u) := by
    rw [inv_eq_iff_mul_eq_one, ← D.unip_add', add_neg_cancel, unip_zero]
  have key : unip v * lev (Ad E) r s (m⁻¹ * m') = cf (r + s) (k * k'⁻¹) (c * c'⁻¹) := by
    rw [← cf_mul, ← cf_inv, map_mul, ← mul_assoc, ← hv, D.unip_add', map_inv, ← hu]
    have h2 : unip u' * lev (Ad E) r s m' =
        unip u * lev (Ad E) r s m * cf (r + s) k c * (cf (r + s) k' c')⁻¹ := by
      rw [h]; group
    rw [mul_assoc (lev (Ad E) r s m)⁻¹, mul_assoc (unip u)⁻¹, h2]
    group
  obtain ⟨k₁, c₁, k₂, c₂, h₁, h₂, hm⟩ := GlobalTheory.T.levi_factor_of_unipotent_decomp v (m⁻¹ * m') _ _
    (mul_mem hc (inv_mem hc')) key
  refine ⟨k₁, c₁, k₂, c₂, h₁, h₂, ?_⟩
  calc m' = m * (m⁻¹ * m') := (mul_inv_cancel_left m m').symm
    _ = _ := by rw [hm]; rfl

theorem nodeFn_apply : ∀ {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {r s : ℕ} (e₁ : GA E r → ℂ) (e₂ : GA E s → ℂ), FlatFn e₁ → FlatFn e₂ → ∀ (u : BlockIx (r + s) r → Ad E) (m : GA E r × GA E s) (k : Kinf E (r + s)) (c : GL (Fin (r + s)) (Af E)), c ∈ KO E (r + s) → nodeFn e₁ e₂ (unip u * lev (Ad E) r s m * cf (r + s) k c) = e₁ m.1 * e₂ m.2 := by
  intro E _ _ _ r s e₁ e₂ f₁ f₂ u m k c hc
  obtain ⟨k', c', hc', hx'⟩ :=
    (exists_iw (unip u * lev (Ad E) r s m * cf (r + s) k c)).choose_spec.choose_spec
  obtain ⟨k₁, c₁, k₂, c₂, h₁, h₂, hm⟩ := levi_eq_mul_cf u _ m _ k k' c c' hc hc' hx'
  have hl : leviOf (unip u * lev (Ad E) r s m * cf (r + s) k c) =
      (m.1 * cf r k₁ c₁, m.2 * cf s k₂ c₂) := hm
  rw [nodeFn, hl, f₁.rinv _ _ _ h₁, f₂.rinv _ _ _ h₂]

end GlobalTheory.CompanionTheory.LimV.NodeApply

end
end

section

open GlobalTheory.CompanionTheory.EGlue

theorem _root_.GlobalTheory.T.convergence_composition : GlobalTheory.CompanionTheory.EGlue.ConvComp := by
  first | exact @GlobalTheory.CompanionTheory.EGlue.convComp_proved | exact GlobalTheory.CompanionTheory.EGlue.convComp_proved | (intros; apply GlobalTheory.CompanionTheory.EGlue.convComp_proved <;> assumption)
end

section

open GlobalTheory.CompanionTheory.EGlue

theorem _root_.GlobalTheory.T.convergence_infimum : GlobalTheory.CompanionTheory.EGlue.DiscInf → GlobalTheory.CompanionTheory.EGlue.TopInf → GlobalTheory.CompanionTheory.EGlue.ConvInf := by
  first | exact @GlobalTheory.CompanionTheory.EGlue.ConvInfProof.convInf_of_discInf_topInf | exact GlobalTheory.CompanionTheory.EGlue.ConvInfProof.convInf_of_discInf_topInf | (intros; apply GlobalTheory.CompanionTheory.EGlue.ConvInfProof.convInf_of_discInf_topInf <;> assumption)
end

section

open GlobalTheory.CompanionTheory.EGlue

theorem _root_.GlobalTheory.T.convergence_shift : GlobalTheory.CompanionTheory.EGlue.ConvShift := by
  first | exact @GlobalTheory.CompanionTheory.EGlue.convShift_holds | exact GlobalTheory.CompanionTheory.EGlue.convShift_holds | (intros; apply GlobalTheory.CompanionTheory.EGlue.convShift_holds <;> assumption)
end

section

open GlobalTheory.CompanionTheory.EGlue

theorem _root_.GlobalTheory.T.infimum_of_equality : GlobalTheory.CompanionTheory.EGlue.InfOfEq := by
  first | exact @GlobalTheory.CompanionTheory.EGlue.infOfEq_holds | exact GlobalTheory.CompanionTheory.EGlue.infOfEq_holds | (intros; apply GlobalTheory.CompanionTheory.EGlue.infOfEq_holds <;> assumption)
end

section

open GlobalTheory.CompanionTheory.EGlue

theorem _root_.GlobalTheory.T.limit_trees : GlobalTheory.CompanionTheory.EGlue.ConvComp → GlobalTheory.CompanionTheory.EGlue.LimTrees := by
  first | exact @GlobalTheory.CompanionTheory.EGlue.LimT.limTrees | exact GlobalTheory.CompanionTheory.EGlue.LimT.limTrees | (intros; apply GlobalTheory.CompanionTheory.EGlue.LimT.limTrees <;> assumption)
end
