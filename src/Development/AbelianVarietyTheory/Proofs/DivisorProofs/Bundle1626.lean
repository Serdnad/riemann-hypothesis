module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
public import GroundTheory.ProfiniteCohomology.CohomologicalDimension.PrimaryComponentCohomologyEqBotOfScdpLt
public import GroundTheory.ProfiniteCohomology.DiscreteModules.IsDiscreteRepIffForallExistsOpenNormalSubgroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle930
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1571
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1066
import GroundTheory.ProfiniteCohomology.CohomologicalDimension.SubsingletonCohomologyOfPrimaryOfFinite
import GroundTheory.ProfiniteCohomology.LocalClassFormation.FiniteVanishing.Vanishing
import GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.Bundle002
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1574
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1575
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1576
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.Deriv.Star
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
import Development.AbelianVarietyTheory.Definitions.Foundations.StrictInterlaceIffDescEnum
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Mathlib.Tactic.Polynomial.Basic
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle041
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle042
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle045

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.VacConj
variable {D : D7}
theorem inv_neg' {n : ℕ} (A : Matrix (Fin n) (Fin n) D.host.E) : (-A)⁻¹ = -A⁻¹ := by
  by_cases h : IsUnit A.det
  · exact Matrix.inv_eq_left_inv (by rw [neg_mul_neg, Matrix.nonsing_inv_mul A h])
  · have h' : ¬ IsUnit (-A).det := by
      rw [Matrix.det_neg]
      intro hu
      exact h (isUnit_of_mul_isUnit_right hu)
    rw [Matrix.nonsing_inv_apply_not_isUnit _ h, Matrix.nonsing_inv_apply_not_isUnit _ h', neg_zero]

theorem star_char' {R : Type} [CommRing R] (ψ : AddChar R ℂ) (h : ∀ x, ‖ψ x‖ = 1) (x : R) :
    star (ψ (-x)) = ψ x := by
  have h1 : ψ (-x) * ψ x = 1 := by rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
  have h2 : star (ψ (-x)) * ψ (-x) = 1 := by
    rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, h]; simp
  calc star (ψ (-x)) = star (ψ (-x)) * (ψ (-x) * ψ x) := by rw [h1, mul_one]
    _ = ψ x := by rw [← mul_assoc, h2, one_mul]

theorem hO_neg (S T : HSp D) (x y : WO S T) : hO (negSp S) T x y = -hO S T x y := by
  unfold hO
  rw [negSp_gram, inv_neg']
  simp only [Matrix.neg_apply, map_neg, neg_mul, Finset.sum_neg_distrib]

theorem symplOH_neg (S T : HSp D) (x y : WO S T) : symplOH (negSp S) T x y = -symplOH S T x y := by
  unfold symplOH symplO
  rw [hO_neg, mul_neg, map_neg, mul_neg]

theorem heisO_conj (ψ : AddChar (AF D.host.F) ℂ) (hψ : ∀ x, ‖ψ x‖ = 1) (S T : HSp D) (u : WO S T) (f : WO S T → ℂ) :
    heisO ψ S T u (fun w => starRingEnd ℂ (f w)) = fun w => starRingEnd ℂ (heisO ψ (negSp S) T u f w) := by
  funext w
  simp only [heisO, symplOH_neg, map_mul]
  rw [← Complex.star_def, star_char' ψ hψ]

theorem lineAt_neg {θ : InfFam D} (hθ : IsInfFam θ) {m n : ℕ} (τ : D.what₂.Tau) (z : Matrix (Fin m) (Fin n) ℂ) (t : ℝ) :
    lineAt θ τ (-z) t = lineAt θ τ z (-t) := by
  have hL : IsLineAt θ τ z (lineAt θ τ z) := Classical.epsilon_spec (GlobalTheory.RealLineAt.lineAt_exists D θ hθ m n τ z)
  have hL0 : IsLineAt θ τ (-z) (lineAt θ τ (-z)) :=
    Classical.epsilon_spec (GlobalTheory.RealLineAt.lineAt_exists D θ hθ m n τ (-z))
  have hN : IsLineAt θ τ (-z) (-lineAt θ τ z) := by
    refine ⟨continuous_neg.comp hL.1, fun t => ?_, fun t τ' => ?_⟩
    · rw [AddMonoidHom.neg_apply, Matrix.map_neg _ (fun a => RingHom.map_neg (finPart D) a), hL.2.1 t, neg_zero]
    · have := hL.2.2 t τ'
      have e : compAt θ τ' ((-lineAt θ τ z) t) = -compAt θ τ' (lineAt θ τ z t) := by
        unfold compAt
        rw [AddMonoidHom.neg_apply, Matrix.map_neg _ (fun a => by rw [RingHom.map_neg, RingHom.map_neg])]
      rw [e, this]
      split_ifs <;> simp
  rw [GlobalTheory.RealLineAt.lineAt_unique D θ hθ m n τ (-z) _ _ hL0 hN]
  simp

theorem dRho_neg {θ : InfFam D} (hθ : IsInfFam θ) {m n : ℕ} (hs : Mx D m n → (Mx D m n → ℂ) → (Mx D m n → ℂ))
    (τ : D.what₂.Tau) (z : Matrix (Fin m) (Fin n) ℂ) (f : Mx D m n → ℂ) (x : Mx D m n) :
    Formalism.IndefR.Datum.dRho hs θ τ (-z) f x = -Formalism.IndefR.Datum.dRho hs θ τ z f x := by
  unfold Formalism.IndefR.Datum.dRho
  simp_rw [lineAt_neg hθ]
  rw [deriv_comp_neg (f := fun t => hs (lineAt θ τ z t) f x), neg_zero]

theorem dRho_conj (ψ : AddChar (AF D.host.F) ℂ) (hψ : ∀ x, ‖ψ x‖ = 1) (θ : InfFam D) (S T : HSp D) (τ : D.what₂.Tau)
    (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (f : WO S T → ℂ) (x : WO S T) :
    Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z (fun w => starRingEnd ℂ (f w)) x =
      starRingEnd ℂ (Formalism.IndefR.Datum.dRho (heisO ψ (negSp S) T) θ τ z f x) := by
  unfold Formalism.IndefR.Datum.dRho
  simp_rw [heisO_conj ψ hψ]
  exact deriv.star

theorem cplxO_neg {m n : ℕ} (sS : Matrix (Fin n) (Fin n) ℂ) (sT : Matrix (Fin m) (Fin m) ℂ) (z : Matrix (Fin m) (Fin n) ℂ) :
    cplxO (-sS) sT z = -cplxO sS sT z := by
  unfold cplxO
  rw [Matrix.mul_neg, smul_neg]

theorem latO_le (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    (P : HeightOneSpectrum (𝓞 D.host.F) → Prop) : latO S T LS LT P ≤ latO (negSp S) T LS LT P := by
  unfold latO
  rw [AddSubgroup.closure_le]
  rintro w ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩
  rw [← neg_neg (Matrix.of _)]
  refine neg_mem (AddSubgroup.subset_closure ⟨α, hα, hP, a, ha, s, hs, t, ht, ?_⟩)
  funext i j
  simp [negSp_gram, Finset.sum_neg_distrib, TensorProduct.tmul_neg]

end GlobalTheory.VacConj

namespace GlobalTheory.VacConj

theorem isVacO_conj_negSp {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D)
    (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (f : WO (negSp S) T → ℂ) :
    IsVacO ψ θ (negSp S) T (fun τ => -sS τ) sT LS LT f → IsVacO ψ θ S T sS sT LS LT (fun w => starRingEnd ℂ (f w)) := by
  rintro ⟨hψ, hv⟩
  have hn : ∀ x, ‖ψ x‖ = 1 := hψ.1.2.1
  have hθ : IsInfFam θ := hv.inf
  refine ⟨hψ, ⟨hθ, ⟨fun γ w => ?_, ?_, ?_, ?_⟩, ⟨fun u hu => ?_, fun e he u hu hh => ?_⟩, fun τ z => ?_, ?_⟩⟩
  · have h := hv.theta.quasi γ w
    show starRingEnd ℂ (f (ratW T S γ + w)) = _
    rw [show f (ratW T S γ + w) = _ from h, map_mul, symplOH_neg, ← Complex.star_def, star_char' ψ hn]
    rfl
  · obtain ⟨U, hU, hUf⟩ := hv.theta.level
    exact ⟨U, hU, fun u hu hu' => by rw [heisO_conj ψ hn, hUf u hu hu']⟩
  · exact Complex.continuous_conj.comp hv.theta.cont
  · intro k L hL hL' w
    exact (Complex.conjCLE.contDiff.comp (hv.theta.smooth k L hL hL' w) :)
  · rw [heisO_conj ψ hn, hv.lat.1 u (latO_le S T LS LT _ hu)]
  · rw [heisO_conj ψ hn, hv.lat.2 e he u (latO_le S T LS LT _ hu) hh]
  · funext x
    have h := congrFun (hv.fock τ z) x
    simp only [annih, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h ⊢
    rw [cplxO_neg, dRho_neg hθ] at h
    rw [dRho_conj ψ hn, dRho_conj ψ hn]
    have h' := congrArg (starRingEnd ℂ) h
    simp only [map_add (f := _), map_mul, map_neg, Complex.conj_I, map_zero] at h'
    linear_combination h'
  · obtain ⟨h1, h2⟩ := hv.norm
    refine ⟨h1, fun p hp => ?_⟩
    have := h2 p hp
    unfold nrm2 at this ⊢
    simp only [Complex.norm_conj]
    exact this

end GlobalTheory.VacConj
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.EtC.CdOne

open GroundTheory.ProfCoh

theorem subsingleton_cohomology_trivial_zmod (G : Type) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (q : ℕ) [NeZero q]
    (h : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ q → cdp ℓ G ≤ 1) (n : ℕ) (hn : 2 ≤ n) :
    Subsingleton (cohomology (Rep.trivial (ZMod q) G (ZMod q)) n) := by
  let A : Rep.{0} (ULift.{0} ℤ) G := Rep.trivial (ULift.{0} ℤ) G (ULift.{0} (ZMod q))
  have hq0 : q ≠ 0 := NeZero.ne q
  have hA : ∀ a : A, q • a = 0 := fun a => by
    change (q • a : ULift.{0} (ZMod q)) = 0
    ext
    simp
  have htors : IsAddTorsion A := fun a =>
    isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨q, Nat.pos_of_ne_zero hq0, hA a⟩
  have hsub : Subsingleton (cohomology A n) := by
    suffices h' : ∀ x : cohomology A n, x = 0 from ⟨fun x y => (h' x).trans (h' y).symm⟩
    intro x
    refine eq_zero_of_primaryComponent_eq_bot q hq0 (fun ℓ hℓ hℓq => ?_) x
      (nsmul_cohomology_eq_zero A hA n x)
    refine primaryComponent_cohomology_eq_bot_of_cdp_lt (p := ℓ) A htors ?_
    calc cdp ℓ G ≤ 1 := h ℓ hℓ hℓq
      _ < n := by exact_mod_cast (show 1 < n by omega)
  let e : A ≃+ (Rep.trivial (ZMod q) G (ZMod q) : Rep (ZMod q) G) := AddEquiv.ulift
  exact (cohomologyAddEquivOfEquiv (A := A) (A' := Rep.trivial (ZMod q) G (ZMod q)) e
    (fun _ _ => rfl) n).symm.injective.subsingleton

end GlobalTheory.EtC.CdOne

namespace GlobalTheory.EtC

theorem gaugeSplitting_holds : C1 := by
  intro q _ k K _ _ _ _ _ hq n i hn
  let f : k →+* K := (algebraMap (RatFunc k) K).comp (algebraMap k (RatFunc k))
  have hq0 : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hqk : (q : k) ≠ 0 := by
    intro h0
    have : (q : K) = 0 := by rw [← map_natCast f q, h0, map_zero]
    exact hq.ne_zero this
  haveI : NeZero (q : k) := ⟨hqk⟩
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic q k)
    (Polynomial.degree_cyclotomic_pos q k hq0).ne'
  have hζk : IsPrimitiveRoot ζ q := (Polynomial.isRoot_cyclotomic_iff).1 hζ
  have hζK : IsPrimitiveRoot (f ζ) q := hζk.map_of_injective f.injective
  have hroot : ∃ z : K, Polynomial.aeval z (Polynomial.cyclotomic q ℤ) = 0 := by
    refine ⟨f ζ, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
    exact hζK.isRoot_cyclotomic hq0
  obtain ⟨u⟩ := GlobalTheory.T.tateTwistCohomology_spec_twist_independent q K hq hroot n i 0
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le (show (0 : ℤ) ≤ n by omega)
  have hm : 2 ≤ m := by omega
  let Ω := SeparableClosure K
  have hζΩ : IsPrimitiveRoot (algebraMap K Ω (f ζ)) q :=
    hζK.map_of_injective (algebraMap K Ω).injective
  obtain ⟨e⟩ := GlobalTheory.T.etaleCohomology_field_eq_galoisCohomology q K Ω hq 0 (Rep.trivial (ZMod q) (Ω ≃ₐ[K] Ω) (ZMod q)) _ hζΩ
    (Module.Basis.singleton Unit (ZMod q)) (fun σ a _ => by simp) m
  have hsub := GlobalTheory.EtC.CdOne.subsingleton_cohomology_trivial_zmod (Ω ≃ₐ[K] Ω) q
    (fun ℓ hℓ _ => GlobalTheory.T.cdp_galois_le_one_of_isAlgebraic_ratFunc k K Ω ℓ hℓ) m hm
  exact (u.trans e).injective.subsingleton

end GlobalTheory.EtC
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.exists_hodgeFiltration_to_pDivOmega_linearMap
    (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (N : ℕ) (hN : (p : R) ^ N = 0)
    (A : Over (Sp R)) [GrpObj A] (hA : IsAbelianScheme A) (G : PDivGroup p R)
    (t : G.TorsionTower A) :
    ∃ ψ : PrimitiveSubmodule A →ₗ[R] G.omega,
      ∀ c : PrimitiveSubmodule A, GlobalTheory.PtExt.IsCan t c.1 (G.rigOfOmega (ψ c)) :=
  GlobalTheory.PtExt.exists_hodge_to_omega p R N hN A hA G t
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

theorem _root_.GlobalTheory.T.exists_ample_power_lift_of_nonvanishing_on_closed : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (L : LB X), IsAmpleLB L → ∀ (T : Scheme.{0}) (i : T ⟶ X) [IsClosedImmersion i] (n : ℕ) (s : (lbPow (L.pull i) n).Sec), 1 ≤ n → ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s = ⊤ → ∃ (N : ℕ) (u : (lbPow L N).Sec), 1 ≤ N ∧ Set.range i ⊆ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus u := by
  first | exact @GlobalTheory.LiftAmple.exists_sec_nonzero_on_closed | exact GlobalTheory.LiftAmple.exists_sec_nonzero_on_closed | (intros; apply GlobalTheory.LiftAmple.exists_sec_nonzero_on_closed <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

theorem _root_.GlobalTheory.T.isTranscendenceBasis_functionField_arithmeticVariety : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → (∃ x : Fin D → X.functionField, IsTranscendenceBasis ℤ x) ∧ ∀ x : Fin D → X.functionField, AlgebraicIndependent ℤ x → IsTranscendenceBasis ℤ x := by
  first | exact @GlobalTheory.ArithTrdeg.isTranscendenceBasis_functionField | exact GlobalTheory.ArithTrdeg.isTranscendenceBasis_functionField | (intros; apply GlobalTheory.ArithTrdeg.isTranscendenceBasis_functionField <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.ArithFnField

theorem charZero_and_trdeg_functionField : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X]
    (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D →
    CharZero X.functionField ∧ Algebra.trdeg ℤ X.functionField = D := by
  intro k _ X _ p D h
  refine ⟨?_, ArithTrdeg.trdeg_functionField_eq h⟩
  have hc0 : CharZero Γ(X, ⊤) := (flat_int_iff_charZero _).1 h.flat
  exact ((X.germToFunctionField ⊤).hom.charZero_iff (X.germToFunctionField_injective ⊤)).1 hc0

end GlobalTheory.ArithFnField
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AffCurveSum

variable {k : Type} [CommRing k] {Y : Scheme.{0}} [IsIntegral Y] [IsAffine Y] {q : Y ⟶ Sp k}

def evTop (y : Σ σ : k →+* ℂ, CxPts q σ) : Γ(Y, ⊤) →+* ℂ := evHom (y := y.2) mem_ptsIn_top

theorem evTop_apply (y : Σ σ : k →+* ℂ, CxPts q σ) (b : Γ(Y, ⊤)) :
    evTop y b = ev q y.1 ⊤ b y.2 := (ev_eq mem_ptsIn_top b).symm

theorem evTop_bijective : Function.Bijective (evTop (q := q)) := by
  constructor
  · rintro ⟨σ, y⟩ ⟨σ', y'⟩ h
    have hσ : σ = σ' := RingHom.ext fun a => by
      have := congrArg (fun φ : Γ(Y, ⊤) →+* ℂ => φ (algX q ⊤ a)) h
      simp only [evTop_apply, ev_algX mem_ptsIn_top] at this
      exact this
    subst hσ
    have hy : y = y' := Subtype.ext (Points.ext_of_valR (isAffineOpen_top Y)
      (mem_ptsIn_top : y ∈ ptsIn q σ ⊤) (mem_ptsIn_top : y' ∈ ptsIn q σ ⊤) fun f => by
        have := congrArg (fun φ : Γ(Y, ⊤) →+* ℂ => φ f) h
        simp only [evTop_apply] at this
        exact this)
    rw [hy]
  · intro τ
    refine ⟨⟨τ.comp (algX q ⊤), ofHom (p := q) (σ := τ.comp (algX q ⊤)) (isAffineOpen_top Y) τ
      (fun _ => rfl)⟩, ?_⟩
    ext f
    rw [evTop_apply]
    exact ev_ofHom (p := q) (σ := τ.comp (algX q ⊤)) (isAffineOpen_top Y) τ (fun _ => rfl) f

theorem main : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] [IsAffine Y] (q : Y ⟶ Sp k),
    IsArithVar q 0 → ∀ b : Γ(Y, ⊤), ∑ᶠ σ : k →+* ℂ, ∑ᶠ y : CxPts q σ,
      Real.log ‖ratVal (algebraMap Γ(Y, ⊤) Y.functionField b) y‖ =
        ∑ᶠ τ : Γ(Y, ⊤) →+* ℂ, Real.log ‖τ b‖ := by
  intro k _ Y _ _ q hq b
  have := hq.finite_emb
  have (σ : k →+* ℂ) := ArchDimZero.finite_cxPts hq σ
  let := Fintype.ofFinite (k →+* ℂ)
  let (σ : k →+* ℂ) := Fintype.ofFinite (CxPts q σ)
  let e := Equiv.ofBijective _ (evTop_bijective (q := q))
  have : Finite (Γ(Y, ⊤) →+* ℂ) := .of_equiv _ e
  let := Fintype.ofFinite (Γ(Y, ⊤) →+* ℂ)
  have hv (σ : k →+* ℂ) (y : CxPts q σ) :
      ratVal (algebraMap Γ(Y, ⊤) Y.functionField b) y = evTop ⟨σ, y⟩ b := by
    exact (ratVal_fnOf mem_ptsIn_top _ b).trans (evTop_apply ⟨σ, y⟩ b).symm
  simp only [hv, finsum_eq_sum_of_fintype]
  rw [← Fintype.sum_sigma (fun x : (Σ σ : k →+* ℂ, CxPts q σ) => Real.log ‖evTop x b‖)]
  exact Fintype.sum_equiv e _ _ fun _ => rfl

end GlobalTheory.AffCurveSum
end
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

theorem GlobalTheory.LKMid.Pair.mk_eq_iff_rel_and_out_rel :
    ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P Q : Pair G),
      (Quot.mk Pair.Rel P = Quot.mk Pair.Rel Q ↔ P.Rel Q) ∧
        (Quot.out (Quot.mk Pair.Rel P : Cls G)).Rel P := by
  intro p _ G P Q
  have e : Equivalence (Pair.Rel (G := G)) := GlobalTheory.T.kottwitzPairScalarIsomorphic_equivalence p G
  have key : ∀ A B : Pair G, (Quot.mk Pair.Rel A = Quot.mk Pair.Rel B ↔ A.Rel B) := by
    intro A B
    rw [Quot.eq, e.eqvGen_iff]
  refine ⟨key P Q, ?_⟩
  exact (key _ _).1 (Quot.out_eq _)
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.exists_conj_of_rel_similitude_pairs_same_form : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P P' : Pair G) (B y y' : G.Cˣ) (s s' : ℚ), 0 < s → 0 < s' → (P.β : G.C) = algebraMap ℚ G.C s * (y * B * sh G y) → (P'.β : G.C) = algebraMap ℚ G.C s' * (y' * B * sh G y') → P.Rel P' → ∃ (g : G.Cˣ) (sg : ℚ), 0 < sg ∧ (g : G.C) * B * sh G g = algebraMap ℚ G.C sg * B ∧ g * (y⁻¹ * P.γ * y) * g⁻¹ = y'⁻¹ * P'.γ * y' := by
  first | (exact @GlobalTheory.LKCx.ConjR.conj_of_rel) | (exact GlobalTheory.LKCx.ConjR.conj_of_rel) | (intros; apply GlobalTheory.LKCx.ConjR.conj_of_rel  <;> assumption)
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.rel_of_conj_in_group_of_common_form : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P P' : Pair G) (B y y' g : G.Cˣ) (s s' sg : ℚ), 0 < s → 0 < s' → 0 < sg → (P.β : G.C) = algebraMap ℚ G.C s * (y * B * sh G y) → (P'.β : G.C) = algebraMap ℚ G.C s' * (y' * B * sh G y') → (g : G.C) * B * sh G g = algebraMap ℚ G.C sg * B → g * (y⁻¹ * P.γ * y) * g⁻¹ = y'⁻¹ * P'.γ * y' → P.Rel P' := by
  first | (exact @GlobalTheory.RelConj.rel_of_conj_in_form) | (exact GlobalTheory.RelConj.rel_of_conj_in_form) | (intros; apply GlobalTheory.RelConj.rel_of_conj_in_form  <;> assumption)
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.StabFin
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.centralizer_scalar_padic_bounded : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (r : ℕ) (z : Gr G r) (K : Subgroup (Gr G r)) (g : Gr G r), 0 < r → Subgroup.Commensurable K (KHT p G.m G.n r G.Fw) → ∀ w : P.cent, P.toQr r z w ∈ K.map (MulAut.conj g).toMonoidHom → ‖(((w : G.Cˣ × ℚˣ).2 : ℚ) : ℚ_[p])‖ ≤ 1 := by
  first | (exact @GlobalTheory.StabFin.sim_norm_le_one) | (exact GlobalTheory.StabFin.sim_norm_le_one) | (intros; apply GlobalTheory.StabFin.sim_norm_le_one  <;> assumption)
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.exists_eigenbasis_psi_infinitePlace_distinct_roots : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (v : InfinitePlace G.F), ∃ (Z : GL (Fin G.n) ℂ) (lam : Fin G.n → ℂ), Function.Injective lam ∧ (∀ z : ℂ, P.pol.eval₂ v.embedding z = 0 ↔ ∃ i, lam i = z) ∧ G.psi v (P.γ : G.C) * (Z : Matrix (Fin G.n) (Fin G.n) ℂ) = (Z : Matrix (Fin G.n) (Fin G.n) ℂ) * Matrix.diagonal lam := by
  first | (exact @GlobalTheory.LKMid.psi_eigenbasis) | (exact GlobalTheory.LKMid.psi_eigenbasis) | (intros; apply GlobalTheory.LKMid.psi_eigenbasis  <;> assumption)
end
