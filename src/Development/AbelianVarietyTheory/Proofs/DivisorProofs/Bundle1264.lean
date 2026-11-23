module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle010
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle041
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IteratedLineDerivMemWeylAlg
import Formalism.LocalRingCardinality.DataHost
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1181
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle029
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFrameOfForallExists
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Definitions.Divisors.KerIdealCompOfSurjective
public import Development.AbelianVarietyTheory.Definitions.Divisors.Pullback1MemHodgeFiltration
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1172
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1100
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle987
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1136
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqZeroOfCobOneEqZero
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle034
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRootOfKeyFormula
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle710
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle012
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.Bundle001

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry GlobalTheory.TwoSeq GlobalTheory.DeRham GlobalTheory.AbDual GlobalTheory.ConjSeq GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.BadPt
open GlobalTheory.Cris (dp0)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HodgeWeil

theorem triv_theta (hC : GlobalTheory.Published.CubeTheorem) {S : Scheme.{0}} {A : Over S} [GrpObj A] (hA : IsAbelianScheme A)
    {L : LB A.left} (hL : L.IsLB) : AbLaw.Triv (Theta A L) := by
  have := hA.comm
  have h := hC S A hA L hL (G3 A) (x3 A 0) (x3 A 1) (x3 A 2)
  have e := (CechPic.cls_eq_zero_iff (LB.isLB_linComb hL _ _)).2 h
  rw [CechPic.cls_linComb hL _ _ _, Fin.sum_univ_eight] at e
  refine (CechPic.cls_eq_zero_iff (LB.isLB_linComb hL _ _)).1 ?_
  rw [CechPic.cls_linComb hL _ _ _, ← e, ← Equiv.ulift.symm.sum_comp]
  have u : (Finset.univ : Finset (Finset (Fin 3))) = {{0, 1, 2}, {0, 1}, {0, 2}, {1, 2}, {0}, {1}, {2}, ∅} := by
    decide
  rw [u]
  iterate 7 rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  have k0 : psum A (x3 A) {0, 1, 2} = x3 A 0 * x3 A 1 * x3 A 2 :=
    (show _ = x3 A 0 * (x3 A 1 * (x3 A 2 * 1)) from rfl).trans (by rw [_root_.mul_one, _root_.mul_assoc])
  have k1 : psum A (x3 A) {0, 1} = x3 A 0 * x3 A 1 :=
    (show _ = x3 A 0 * (x3 A 1 * 1) from rfl).trans (by rw [_root_.mul_one])
  have k2 : psum A (x3 A) {0, 2} = x3 A 0 * x3 A 2 :=
    (show _ = x3 A 0 * (x3 A 2 * 1) from rfl).trans (by rw [_root_.mul_one])
  have k3 : psum A (x3 A) {1, 2} = x3 A 1 * x3 A 2 :=
    (show _ = x3 A 1 * (x3 A 2 * 1) from rfl).trans (by rw [_root_.mul_one])
  have k4 : psum A (x3 A) {0} = x3 A 0 := _root_.mul_one (x3 A 0)
  have k5 : psum A (x3 A) {1} = x3 A 1 := _root_.mul_one (x3 A 1)
  have k6 : psum A (x3 A) {2} = x3 A 2 := _root_.mul_one (x3 A 2)
  have k7 : psum A (x3 A) ∅ = 1 := rfl
  simp only [Equiv.ulift_symm_down, k0, k1, k2, k3, k4, k5, k6, k7, ← add_assoc]
  rfl

section Point

variable {R D : Type} [CommRing R] [CommRing D] [Bialgebra R D] [Module.Finite R D] [Module.Projective R D]
  [Coalgebra.IsCocomm R D]

end Point

section Tower

variable {p : ℕ} {R : Type} [CommRing R] {A B : Over (Sp R)} [GrpObj A] [GrpObj B] {𝒜 ℬ : PDivGroup p R}

end Tower

section Linear

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] {V : Type*} [AddCommGroup V] [Module K V] {𝒜 : PDivGroup p K}
  {w : 𝒜 ⟶ 𝒜.dual} {E : V ≃ₗ[K] 𝒜.RigExt} {β : V →ₗ[K] V →ₗ[K] K} {ε : ℤˣ}


end Linear

end GlobalTheory.HodgeWeil
end
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.TwistDisc

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem pow_val_apply (χ : HChar E) (k : ℕ) (x : _) : (χ ^ k).1 x = χ.1 x ^ k := rfl

theorem chiInf_pow (χ : HChar E) (k : ℕ) (z : (Cinf E)ˣ) : chiInf (χ ^ k) z = chiInf χ z ^ k := rfl

theorem dchi_pow (χ : HChar E) (k : ℕ) : dchi (χ ^ k) = (k : ℝ) • dchi χ := by
  obtain ⟨L, hL⟩ := exists_lin _ (continuous_chiInf χ)
  have h1 : dchi χ = L := fderiv_extZero (continuous_chiInf χ) hL
  have h2 : dchi (χ ^ k) = (k : ℝ) • L := fderiv_extZero (continuous_chiInf (χ ^ k)) fun z => by
    rw [chiInf_pow, Units.val_pow_eq_pow_val, hL, ← Complex.exp_nat_mul]
    simp
  rw [h1, h2]

theorem expo_pow (χ : HChar E) (k : ℕ) (τ : E →+* ℂ) : expo (χ ^ k) τ = k * expo χ τ := by
  simp only [expo, dchi_pow, ContinuousLinearMap.smul_apply, Complex.real_smul, Complex.ofReal_natCast]
  ring

theorem chiDet_splitCentre {μ : HChar E} {e : InfinitePlace E → ℤ}
    (h : ∀ z : (Cinf E)ˣ, (chiInf μ z : ℂ) = ∏ v, (z.1 v / (‖z.1 v‖ : ℂ)) ^ e v) (t : ℝ) :
    chiDet a μ (splitCentre E a t) = 1 := by
  unfold splitCentre
  rw [chiDet, MonoidHom.comp_apply, det_infGL]
  change chiInf μ _ = 1
  apply Units.ext
  rw [h, Units.val_one]
  refine Finset.prod_eq_one fun v _ => ?_
  have hz : ((GeneralLinearGroup.det (Units.map (Matrix.scalar (Fin a)).toMonoidHom
      (expU fun _ : InfinitePlace E => (t : ℂ))) : (Cinf E)ˣ) : Cinf E) v = ((Real.exp t ^ a : ℝ) : ℂ) := by
    simp [Matrix.scalar_apply, Matrix.det_diagonal, expU, Complex.ofReal_exp]
  rw [hz, Complex.norm_real, Real.norm_of_nonneg (by positivity), div_self (by exact_mod_cast (by positivity : Real.exp t ^ a ≠ 0)), _root_.one_zpow]

theorem isSqInt_mulChi {χ : HChar E} (hu : χ.IsUnitary) (hs : ∀ t, chiDet a χ (splitCentre E a t) = 1) {φ : Sm E a}
    (h : IsSqInt φ.1) : IsSqInt (mulChi a χ φ).1 := by
  obtain ⟨h1, μ, 𝓕, hμ, hF, hI⟩ := h
  refine ⟨fun t g => ?_, μ, 𝓕, hμ, hF, ?_⟩
  · simp only [mulChi_apply, map_mul, hs, one_mul, h1]
  · have e : ∀ g, ‖(mulChi a χ φ).1 g‖ₑ = ‖φ.1 g‖ₑ := fun g => by
      have h2 : ‖((chiDet a χ g : ℂˣ) : ℂ)‖ₑ = 1 := by
        rw [← ofReal_norm_eq_enorm, show ‖((chiDet a χ g : ℂˣ) : ℂ)‖ = 1 from hu _, ENNReal.ofReal_one]
      rw [mulChi_apply, enorm_mul, h2, mul_one]
    simp only [e]
    exact hI

theorem isDiscrete_map {χ : HChar E} (hu : χ.IsUnitary) (hs : ∀ t, chiDet a χ (splitCentre E a t) = 1)
    {V : Submodule ℂ (Sm E a)} (hV : IsDiscrete V) : IsDiscrete (V.map (mulChi a χ).toLinearMap) := by
  refine { aut := ?_, sqInt := ?_, stable := ?_, ne_bot := ?_, irred := ?_ }
  · rintro _ ⟨φ, hφ, rfl⟩
    have h := hV.aut φ hφ
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro γ g
      simp [h.left, chiDet_ratGL]
    · exact isOpen_stab_of_mem_nhds _ _ <| Filter.mem_of_superset
        ((h.level.inter (isOpen_ker_chiDet χ)).mem_nhds ⟨by simp, by simp⟩) fun k hk => by
          have h1 : rt E a (finGL E a k) φ = φ := hk.1
          have h2 : chiDet a χ (finGL E a k) = 1 := hk.2
          change rt E a (finGL E a k) (CuspRep.mulChi a χ φ) = CuspRep.mulChi a χ φ
          rw [rt_mulChi, h1, h2, Units.val_one, one_smul]
    · have := h.kfin
      refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ (Set.range fun k => cptRep E a k φ)).map
        (CuspRep.mulChi a χ).toLinearMap) (Submodule.span_le.2 ?_)
      rintro _ ⟨k, rfl⟩
      exact ⟨_, Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩), (rt_mulChi χ _ φ).symm⟩
    · have := h.zfin
      refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) ''
        Zalg E a)).map (CuspRep.mulChi a χ).toLinearMap) (Submodule.span_le.2 ?_)
      rintro _ ⟨z, hz, rfl⟩
      obtain ⟨z', h1, h2⟩ := Zalg_mulChi χ hz
      exact ⟨_, Submodule.subset_span ⟨z', h1, rfl⟩, (h2 φ).symm⟩
    · intro g
      obtain ⟨C, N, h1⟩ := h.growth g
      obtain ⟨C', N', h2⟩ := chiDet_growth (a := a) χ
      refine ⟨C * (‖((chiDet a χ g : ℂˣ) : ℂ)‖ * C'), N + N', fun y => ?_⟩
      change ‖(CuspRep.mulChi a χ φ).1 (g * infGL E a y)‖ ≤ _
      rw [mulChi_apply, map_mul, Units.val_mul, norm_mul, norm_mul]
      refine (mul_le_mul (h1 y) (mul_le_mul_of_nonneg_left (h2 y) (norm_nonneg _)) (by positivity)
        ((norm_nonneg _).trans (h1 y))).trans_eq ?_
      ring
  · rintro _ ⟨φ, hφ, rfl⟩
    exact isSqInt_mulChi hu hs (hV.sqInt φ hφ)
  · rintro o _ ⟨φ, hφ, rfl⟩
    exact ⟨_, add_mem (V.smul_mem _ (hV.stable o φ hφ)) (V.smul_mem _ hφ), (act_mulChi χ o φ).symm⟩
  · intro h
    exact hV.ne_bot ((Submodule.map_eq_bot_iff (e := mulChi a χ)).1 h)
  · intro W hW hW'
    have h := hV.irred (W.comap (mulChi a χ).toLinearMap) (fun φ hφ => by
      obtain ⟨ψ, h1, h2⟩ := hW hφ
      rwa [← (mulChi a χ).injective h2]) fun o φ hφ => by
      have h1 : _ ∈ W.comap (mulChi a χ).toLinearMap := (act_mulChi χ o φ) ▸ hW' o _ hφ
      exact (Submodule.smul_mem_iff _ (Units.ne_zero (opMul χ o))).1
        ((Submodule.add_mem_iff_left _ (Submodule.smul_mem _ _ hφ)).1 h1)
    have e := Submodule.map_comap_eq_of_surjective (f := (mulChi a χ).toLinearMap) (mulChi a χ).surjective W
    exact h.imp (fun h => by rw [← e, h, Submodule.map_bot]) fun h => by rw [← e, h]

theorem isLocCompGL_map (χ : HChar E) {V : Submodule ℂ (Sm E a)} {w : HeightOneSpectrum (𝓞 E)}
    {σ : SmIrr (GL (Fin a) (w.adicCompletion E))} (h : IsLocCompGL V w σ) :
    IsLocCompGL (V.map (mulChi a χ).toLinearMap) w
      (σ.twist (CuspSub.locDet a χ w) (CuspSub.isOpen_ker_locDet χ w)) := by
  obtain ⟨f, h0, hV, hf⟩ := h
  refine ⟨(mulChi a χ).toLinearMap ∘ₗ f, fun h => h0 (LinearMap.ext fun v => (mulChi a χ).injective ?_),
    fun v => ⟨f v, hV v, rfl⟩, fun g v => ?_⟩
  · rw [LinearMap.zero_apply, map_zero]; exact LinearMap.congr_fun h v
  · change mulChi a χ (f (((CuspSub.locDet a χ w g : ℂˣ) : ℂ) • σ.ρ g v)) =
      rt E a (finGL E a (locGL E a w g)) (mulChi a χ (f v))
    rw [map_smul f, hf g v, rt_mulChi, CuspSub.chiDet_locGL]
    simp only [map_smul]
    rfl

theorem hasInfCharGL_map {V : Submodule ℂ (Sm E a)} {τ : E →+* ℂ} {m : Multiset ℂ} (h : HasInfCharGL V τ m)
    (χ : HChar E) : HasInfCharGL (V.map (mulChi a χ).toLinearMap) τ (m.map (· + expo χ τ)) := by
  refine ⟨by rw [Multiset.card_map, h.1], ?_⟩
  rintro u _ ⟨φ, hφ, rfl⟩
  change cap τ u (mulChi a χ φ) = _ • mulChi a χ φ
  rw [cap_mulChi, h.2 _ φ hφ, map_smul, Multiset.map_map]
  congr 3
  ext x
  simp [add_assoc, add_comm, add_left_comm]

end GlobalTheory.BCT.TwistDisc
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix ENNReal Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open Complex SchwartzMap
open scoped Real RealInnerProductSpace Topology

namespace GlobalTheory.RealWeil.DRhoTransfer

variable {l : Type} [Fintype l]

theorem exists_decay (h : Sch l) (N : ℕ) : ∃ M : ℝ, 0 ≤ M ∧ ∀ y, (1 + ‖y‖) ^ N * ‖h y‖ ≤ M := by
  refine ⟨2 ^ N * (Finset.Iic (N, 0)).sup (fun m => SchwartzMap.seminorm ℂ m.1 m.2) h, by positivity, fun y => ?_⟩
  have := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (N, 0)) (le_refl N) (le_refl 0) h y
  simpa [norm_iteratedFDeriv_zero] using this

theorem translate_bound (h : Sch l) (N : ℕ) (p : EuclideanSpace ℝ l) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ s : ℝ, |s| ≤ 1 → ∀ x, ‖h (x + s • p)‖ ≤ M * ((1 + ‖x‖) ^ N)⁻¹ := by
  obtain ⟨M, hM, hb⟩ := exists_decay h N
  refine ⟨M * (1 + ‖p‖) ^ N, by positivity, fun s hs x => ?_⟩
  have h1 : 1 + ‖x‖ ≤ (1 + ‖x + s • p‖) * (1 + ‖p‖) := by
    have h0 : ‖x‖ ≤ ‖x + s • p‖ + ‖s • p‖ := by
      have := norm_sub_le (x + s • p) (s • p)
      simpa using this
    have h2 : ‖s • p‖ ≤ ‖p‖ := by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_of_le_one_left (norm_nonneg _) hs
    nlinarith [norm_nonneg (x + s • p), norm_nonneg p]
  have h3 : (1 + ‖x‖) ^ N ≤ (1 + ‖x + s • p‖) ^ N * (1 + ‖p‖) ^ N := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) h1 N
  have hpos : 0 < (1 + ‖x‖) ^ N := by positivity
  rw [← div_eq_mul_inv, le_div_iff₀ hpos]
  calc ‖h (x + s • p)‖ * (1 + ‖x‖) ^ N ≤ ‖h (x + s • p)‖ * ((1 + ‖x + s • p‖) ^ N * (1 + ‖p‖) ^ N) := by
        gcongr
    _ = ((1 + ‖x + s • p‖) ^ N * ‖h (x + s • p)‖) * (1 + ‖p‖) ^ N := by ring
    _ ≤ M * (1 + ‖p‖) ^ N := by gcongr; exact hb _

theorem lintegral_inv_pow_lt_top (K : ℝ) :
    ∫⁻ x : EuclideanSpace ℝ l, ‖K * ((1 + ‖x‖) ^ (Module.finrank ℝ (EuclideanSpace ℝ l) + 1))⁻¹‖ₑ ^ 2 < ⊤ := by
  set N := Module.finrank ℝ (EuclideanSpace ℝ l) + 1 with hN
  have hi := integrable_one_add_norm (E := EuclideanSpace ℝ l) (μ := volume) (r := 2 * N)
    (by rw [hN]; push_cast; have := Nat.cast_nonneg (α := ℝ) (Module.finrank ℝ (EuclideanSpace ℝ l)); linarith)
  have hi2 := hi.const_mul (K ^ 2)
  have e : ∀ x : EuclideanSpace ℝ l, ‖K * ((1 + ‖x‖) ^ N)⁻¹‖ₑ ^ 2 = ‖K ^ 2 * (1 + ‖x‖) ^ (-(2 * N : ℝ))‖ₑ := by
    intro x
    rw [← enorm_pow, mul_pow, inv_pow, ← pow_mul, Real.rpow_neg (by positivity),
      show (2 * (N : ℝ)) = ((N * 2 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
  simp_rw [e]
  exact hi2.hasFiniteIntegral

theorem taylor_bound (w : l ⊕ l → ℝ) (f : Sch l) :
    ∃ B : EuclideanSpace ℝ l → ℝ, (∀ x, 0 ≤ B x) ∧ (∫⁻ x, ‖B x‖ₑ ^ 2 < ⊤) ∧
      ∀ t : ℝ, |t| ≤ 1 → ∀ x, ‖rhoFun (t • w) f x - f x - t * dRho w f x‖ ≤ t ^ 2 * B x := by
  set N := Module.finrank ℝ (EuclideanSpace ℝ l) + 1
  obtain ⟨M, hM, hb⟩ := translate_bound (dRho w (dRho w f)) N (pPart w)
  refine ⟨fun x => M * ((1 + ‖x‖) ^ N)⁻¹, fun x => by positivity, lintegral_inv_pow_lt_top M, fun t ht x => ?_⟩
  set h := dRho w f with hh
  have hB : ∀ s : ℝ, |s| ≤ 1 → ‖rhoFun (s • w) (dRho w h) x‖ ≤ M * ((1 + ‖x‖) ^ N)⁻¹ := fun s hs => by
    rw [rhoFun, norm_mul, norm_phase, one_mul, pPart_smul]
    exact hb s hs x
  have habs : ∀ s σ : ℝ, σ ∈ Set.uIcc 0 s → |σ| ≤ |s| := fun s σ hσ => by
    simpa using Set.abs_sub_left_of_mem_uIcc hσ
  have step1 : ∀ s : ℝ, |s| ≤ 1 → ‖rhoFun (s • w) h x - h x‖ ≤ M * ((1 + ‖x‖) ^ N)⁻¹ * |s| := by
    intro s hs
    have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := fun σ : ℝ => rhoFun (σ • w) h x)
      (f' := fun σ => rhoFun (σ • w) (dRho w h) x) (s := Set.uIcc 0 s) (C := M * ((1 + ‖x‖) ^ N)⁻¹)
      (fun σ _ => (hasDerivAt_rhoFun_at w h x σ).hasDerivWithinAt)
      (fun σ hσ => hB σ ((habs s σ hσ).trans hs)) (convex_uIcc 0 s) Set.left_mem_uIcc Set.right_mem_uIcc
    simpa [rhoFun_zero, Real.norm_eq_abs] using this
  have hd : ∀ σ : ℝ, HasDerivAt (fun σ : ℝ => rhoFun (σ • w) f x - f x - σ * h x)
      (rhoFun (σ • w) h x - h x) σ := fun σ => by
    have e1 : HasDerivAt (fun σ : ℝ => (σ : ℂ) * h x) (h x) σ := by
      simpa using (hasDerivAt_id σ).ofReal_comp.mul_const (h x)
    exact ((hasDerivAt_rhoFun_at w f x σ).sub_const (f x)).sub e1
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun σ : ℝ => rhoFun (σ • w) f x - f x - σ * h x)
    (f' := fun σ => rhoFun (σ • w) h x - h x) (s := Set.uIcc 0 t) (C := M * ((1 + ‖x‖) ^ N)⁻¹ * |t|)
    (fun σ _ => (hd σ).hasDerivWithinAt)
    (fun σ hσ => (step1 σ ((habs t σ hσ).trans ht)).trans (mul_le_mul_of_nonneg_left (habs t σ hσ) (by positivity)))
    (convex_uIcc 0 t) Set.left_mem_uIcc Set.right_mem_uIcc
  simp only [zero_smul, rhoFun_zero, sub_self, ofReal_zero, zero_mul, sub_zero, Real.norm_eq_abs] at this
  refine this.trans (le_of_eq ?_)
  rw [← sq_abs t]
  ring

theorem enorm_sub_sq_le (a b : ℂ) : ‖a - b‖ₑ ^ 2 ≤ 2 * ‖a‖ₑ ^ 2 + 2 * ‖b‖ₑ ^ 2 := by
  simp only [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _)]
  rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  nlinarith [norm_sub_le a b, norm_nonneg a, norm_nonneg b, norm_nonneg (a - b), sq_nonneg (‖a‖ - ‖b‖)]

theorem lintegral_le_of_bound (φ : EuclideanSpace ℝ l → ℂ) (B : EuclideanSpace ℝ l → ℝ) {c : ℝ} (hc : 0 ≤ c)
    (hB : ∀ x, 0 ≤ B x) (h : ∀ x, ‖φ x‖ ≤ c * B x) :
    ∫⁻ x, ‖φ x‖ₑ ^ 2 ≤ ENNReal.ofReal c ^ 2 * ∫⁻ x, ‖B x‖ₑ ^ 2 := by
  rw [← lintegral_const_mul' _ _ (by simp)]
  refine lintegral_mono fun x => ?_
  rw [← mul_pow]
  gcongr
  calc ‖φ x‖ₑ = ENNReal.ofReal ‖φ x‖ := (ofReal_norm_eq_enorm _).symm
    _ ≤ ENNReal.ofReal (c * B x) := ENNReal.ofReal_le_ofReal (h x)
    _ = ENNReal.ofReal c * ‖B x‖ₑ := by rw [ENNReal.ofReal_mul hc, Real.enorm_eq_ofReal (hB x)]

theorem dRho_intertwine : ∀ (l : Type) [Fintype l] (L' : (l ⊕ l → ℝ) →ₗ[ℝ] (l ⊕ l → ℝ))
    (A' : GlobalTheory.RealWeil.Sch l →ₗ[ℂ] GlobalTheory.RealWeil.Sch l) (C : ℝ≥0∞), C ≠ ⊤ →
    (∀ f, ∫⁻ x, ‖A' f x‖ₑ ^ 2 ≤ C * ∫⁻ x, ‖f x‖ₑ ^ 2) →
    (∀ w (f f' : GlobalTheory.RealWeil.Sch l), ⇑f' = GlobalTheory.RealWeil.rhoFun w ⇑f →
      ⇑(A' f') = GlobalTheory.RealWeil.rhoFun (L' w) ⇑(A' f)) →
    ∀ w f, A' (GlobalTheory.RealWeil.dRho w f) = GlobalTheory.RealWeil.dRho (L' w) (A' f) := by
  intro l _ L' A' C hC hA hI w f
  obtain ⟨B₁, hB₁0, hB₁i, hB₁⟩ := taylor_bound w f
  obtain ⟨B₂, hB₂0, hB₂i, hB₂⟩ := taylor_bound (L' w) (A' f)
  set u := A' (dRho w f) - dRho (L' w) (A' f) with hu
  have t1 : ∫⁻ x, ‖B₁ x‖ₑ ^ 2 ≠ ⊤ := hB₁i.ne
  have t2 : (2 : ℝ≥0∞) * C ≠ ⊤ := ENNReal.mul_ne_top (by norm_num) hC
  have t4 : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
  obtain ⟨K, hK⟩ : ∃ K : ℝ≥0∞, K = 2 * C * (∫⁻ x, ‖B₁ x‖ₑ ^ 2) + 2 * ∫⁻ x, ‖B₂ x‖ₑ ^ 2 := ⟨_, rfl⟩
  have hKt : K ≠ ⊤ := by
    rw [hK]
    exact ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top t2 t1, ENNReal.mul_ne_top t4 hB₂i.ne⟩
  have hmeas : ∀ g : Sch l, AEMeasurable (fun x => ‖g x‖ₑ ^ 2) volume := fun g =>
    ((ENNReal.continuous_pow 2).comp g.continuous.enorm).aemeasurable
  have key : ∀ t : ℝ, 0 < t → t ≤ 1 → ∫⁻ x, ‖u x‖ₑ ^ 2 ≤ ENNReal.ofReal (t ^ 2) * K := by
    intro t ht0 ht1
    have hta : |t| ≤ 1 := by rw [abs_of_pos ht0]; exact ht1
    obtain ⟨g, hg⟩ := exists_schwartz_rhoFun l (t • w) f
    have hAg : ⇑(A' g) = rhoFun (t • L' w) ⇑(A' f) := by rw [hI (t • w) f g hg, map_smul]
    set k := g - f - (t : ℂ) • dRho w f with hk
    set m := A' g - A' f - (t : ℂ) • dRho (L' w) (A' f) with hm
    have hkb : ∀ x, ‖k x‖ ≤ t ^ 2 * B₁ x := fun x => by
      have e : k x = rhoFun (t • w) f x - f x - t * dRho w f x := by
        simp only [hk, SchwartzMap.sub_apply, SchwartzMap.smul_apply, smul_eq_mul, hg]
      rw [e]; exact hB₁ t hta x
    have hmb : ∀ x, ‖m x‖ ≤ t ^ 2 * B₂ x := fun x => by
      have e : m x = rhoFun (t • L' w) (A' f) x - A' f x - t * dRho (L' w) (A' f) x := by
        simp only [hm, SchwartzMap.sub_apply, SchwartzMap.smul_apply, smul_eq_mul, hAg]
      rw [e]; exact hB₂ t hta x
    have hum : (t : ℂ) • u = m - A' k := by
      simp only [hu, hk, hm, map_sub, map_smul, smul_sub]
      abel
    obtain ⟨a, ha⟩ : ∃ a : ℝ≥0∞, a = ENNReal.ofReal (t ^ 2) := ⟨_, rfl⟩
    have ha0 : a ≠ 0 := ha ▸ (ENNReal.ofReal_pos.2 (by positivity)).ne'
    have hat : a ≠ ⊤ := ha ▸ ENNReal.ofReal_ne_top
    have hIk := lintegral_le_of_bound k B₁ (by positivity) hB₁0 hkb
    have hIm := lintegral_le_of_bound m B₂ (by positivity) hB₂0 hmb
    have hsc : ∀ x, ‖((t : ℂ) • u) x‖ₑ ^ 2 = a * ‖u x‖ₑ ^ 2 := fun x => by
      rw [SchwartzMap.smul_apply, enorm_smul, mul_pow, ha, ← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _),
        Complex.norm_real, Real.norm_eq_abs, sq_abs]
    have main : a * ∫⁻ x, ‖u x‖ₑ ^ 2 ≤ a * (a * K) := by
      calc a * ∫⁻ x, ‖u x‖ₑ ^ 2 = ∫⁻ x, ‖((t : ℂ) • u) x‖ₑ ^ 2 := by
            rw [← lintegral_const_mul' _ _ hat]; simp only [hsc]
        _ = ∫⁻ x, ‖m x - A' k x‖ₑ ^ 2 := by rw [hum]; simp only [SchwartzMap.sub_apply]
        _ ≤ ∫⁻ x, (2 * ‖m x‖ₑ ^ 2 + 2 * ‖A' k x‖ₑ ^ 2) := lintegral_mono fun x => enorm_sub_sq_le _ _
        _ = 2 * (∫⁻ x, ‖m x‖ₑ ^ 2) + 2 * ∫⁻ x, ‖A' k x‖ₑ ^ 2 := by
            rw [lintegral_add_left' ((hmeas m).const_mul 2), lintegral_const_mul' _ _ t4, lintegral_const_mul' _ _ t4]
        _ ≤ 2 * (ENNReal.ofReal (t ^ 2) ^ 2 * ∫⁻ x, ‖B₂ x‖ₑ ^ 2) +
              2 * (C * (ENNReal.ofReal (t ^ 2) ^ 2 * ∫⁻ x, ‖B₁ x‖ₑ ^ 2)) := by
            have hAk : ∫⁻ x, ‖A' k x‖ₑ ^ 2 ≤ C * (ENNReal.ofReal (t ^ 2) ^ 2 * ∫⁻ x, ‖B₁ x‖ₑ ^ 2) :=
              (hA k).trans (by gcongr)
            gcongr
        _ = a * (a * K) := by rw [hK, ha]; ring
    rw [← ha]
    exact (ENNReal.mul_le_mul_iff_right ha0 hat).mp main
  have hz : ∫⁻ x, ‖u x‖ₑ ^ 2 = 0 := by
    refine le_antisymm ?_ bot_le
    have ht : Filter.Tendsto (fun t : ℝ => ENNReal.ofReal (t ^ 2) * K) (𝓝[>] 0) (𝓝 0) := by
      have := ENNReal.Tendsto.mul_const (ENNReal.tendsto_ofReal ((continuous_pow 2).tendsto (0 : ℝ)))
        (Or.inr hKt)
      simpa using this.mono_left nhdsWithin_le_nhds
    refine ge_of_tendsto ht ?_
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
    exact key t ht.1 ht.2.le
  have hae := (lintegral_eq_zero_iff' (hmeas u)).1 hz
  have hu0 : ⇑u = fun _ => (0 : ℂ) := by
    refine (Continuous.ae_eq_iff_eq volume u.continuous (continuous_const (y := (0 : ℂ)))).1 ?_
    filter_upwards [hae] with x hx
    have hx' : ‖u x‖ₑ ^ 2 = 0 := hx
    simpa using hx'
  have : u = 0 := by ext x; simpa using congrFun hu0 x
  exact sub_eq_zero.1 this

end GlobalTheory.RealWeil.DRhoTransfer
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.levelStructure_baseChange_labels_torsion : ∀ (K C : Type) [Field K] [Field C] [IsAlgClosed C] (f : K →+* C) (P : PolAV (Sp K))
    (P' : PolAV (Sp C)) (io : (Over.mk (spMap f) ⟶ P.A) ≃* (baseOver (Sp C) ⟶ P'.A)),
    (∀ (k : ℕ) a b (z : Γ(Sp C, ⊤)ˣ), WeilIs P'.A P'.L k (io a) (io b) z → WeilIs P.A P.L k a b z) →
    ∀ (g k : ℕ) (hg : P'.g = g) (ζ : Cˣ) (lev : Out.Level P' k (unitOn ζ)), 2 ≤ k →
      IsPrimitiveRoot ζ k ∧
      (∀ a b, io.symm (levelPoint lev hg (a + b)) = io.symm (levelPoint lev hg a) * io.symm (levelPoint lev hg b)) ∧
      Function.Injective (fun a => io.symm (levelPoint lev hg a)) ∧
      (∀ z : Over.mk (spMap f) ⟶ P.A, z ^ k = 1 → ∃ a, io.symm (levelPoint lev hg a) = z) ∧
      ∀ i j, WeilIs P.A P.L k (io.symm (levelPoint lev hg (Pi.single i 1))) (io.symm (levelPoint lev hg (Pi.single j 1)))
        (unitOn (ζ ^ stdSymp g i j)) := by
  first | exact @GlobalTheory.levelPoint_baseChange_label | exact GlobalTheory.levelPoint_baseChange_label | (intros; apply GlobalTheory.levelPoint_baseChange_label <;> assumption)
end
