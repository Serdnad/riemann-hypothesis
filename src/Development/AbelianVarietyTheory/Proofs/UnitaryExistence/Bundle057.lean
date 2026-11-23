module

public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NormalisedPointsSatisfySingleFrame
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle008
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle014
public import Formalism.LocalToGlobal.ProjectiveLattices.LatPAddRight
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLocalDataPrescribedPointsFlag
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle009
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle047
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle055
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HolDifferentiableAt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsDerivAt0OfIsPullback
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle038
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle026
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsObjOfUniformisedTripleComplex
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle003
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SiegelSpaceAlgebraHolds
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.SpGenStatement
import ReciprocityTheory.ThetaQuasiPeriods.PeriodLattice

@[expose] public section

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

theorem _root_.GlobalTheory.T.normalised_points_satisfy_single_frame : Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r) (k : Fin F.n) (T : ThetaData e F M k) (un : (M.X k).dom → FrPt Xo c (CAt σ)), GoodEmb c σ → ModelBase M → NegXi M → IsNormUn T un → ∀ x, FrameOK e F M k x (un x) := by
  first | exact @GlobalTheory.NormFrame.frameOK_of_isNormUn | exact GlobalTheory.NormFrame.frameOK_of_isNormUn | (intros; apply GlobalTheory.NormFrame.frameOK_of_isNormUn <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

namespace GlobalTheory.CurveHomLift

open UniformLift

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}

theorem exists_linear_lift_of_isHolTo (F : FamilyUnif Xo σ ty) (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ))
    (hP : IsPeriod (F.Di i) ty P) {m : ℕ} (e : (Fin m → ℂ) → (Over.mk (F.u i P) ⟶ Xo.univ.t.G))
    (he : ∀ z w, e (z + w) = e z * e w) (hol : IsHolTo Set.univ fun z => (e z).left) :
    ∃ L : (Fin m → ℂ) →ₗ[ℂ] (Fin g → ℂ), ∀ z, F.ex i P (L z) = e z := by
  have hsm : Smooth Xo.univ.t.G.hom := Xo.univ.t.semi.smooth
  have hsm' : Smooth (pullback.snd Xo.univ.t.G.hom (F.u i P)) := inferInstance
  have hol' := ExpUniqFamily.isHolTo_ex F i P hP
  have he' := F.ex_add i P hP
  have hd := isDerivAt0_fibre _ Xo.univ.t.G (F.u i P) g (F.ex i P) _ _ _ (fun z => fibPt _ (F.ex i P z))
    (IsPullback.of_hasPullback Xo.univ.t.G.hom (F.u i P))
    (fun z => ⟨fibPt_fst _ _, fibPt_snd _ _⟩) hol' (F.ex_diff i P hP)
  obtain ⟨k, k0, hka, hk⟩ := LocalLift.exists_local_lift _ (pullback.snd Xo.univ.t.G.hom (F.u i P)) m g
    (fun z => fibPt _ (e z)) (fun z => fibPt _ (F.ex i P z)) hsm'
    (fun z => fibPt_snd _ _) (fun z => fibPt_snd _ _)
    (HolFibre.isHolTo_fibPt isOpen_univ _ _ e hol) (HolFibre.isHolTo_fibPt isOpen_univ _ _ _ hol') hd
    (by simp only [map_zero_eq_one e he, map_zero_eq_one _ he'])
  have hker : ((toAddHom (F.ex i P) he').ker : Set (Fin g → ℂ)) = P.range := Set.ext fun z => F.ex_ker i P hP z
  exact (existsUnique_linearMap_lift_of_germ (ex := toAddHom e he) (ex' := toAddHom (F.ex i P) he')
    (hker ▸ isDiscrete_iff_discreteTopology.2 hP.2.2.1) hka.differentiableAt k0
    (hk.mono fun z hz => fibPt_injective _ hz)).exists

theorem isHolTo_pt (C : Curve H) : IsHolTo Set.univ fun z : Fin 1 → ℂ => C.pt (z 0) := by
  intro U f
  obtain ⟨h1, h2⟩ := C.u.hol U f
  have hd : Differentiable ℂ (fun (z : Fin 1 → ℂ) (_ : Fin C.P.g) => C.c * z 0) := by fun_prop
  refine ⟨?_, h2.comp hd.differentiableOn fun z hz => hz.2⟩
  exact isOpen_univ.inter (h1.preimage hd.continuous)

theorem pt_one (C : Curve H) : C.pt 1 = C.pt 0 := by
  have h1 := (C.u.ker _).2 ((C.lat fun _ => C.c * 1).2 ⟨1, 0, by simp⟩)
  have h0 := (C.u.ker _).2 ((C.lat fun _ => C.c * 0).2 ⟨0, 0, by simp⟩)
  rw [Curve.pt, Curve.pt, h1, h0]

theorem exists_pure_vector : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → l.A = 1 → ∀ C : Curve H, ∀ (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (F.Di i) ty P), ∀ (φ : C.P.A.left ⟶ Xo.univ.t.G.left) (x : ℂ → (Over.mk (F.u i P) ⟶ Xo.univ.t.G)) (ε : ℤˣ), (∀ z, (x z).left = C.pt z ≫ φ) → (∀ z w, x (z + w) = x z * x w) → (∀ z, x ((1 + ((ε : ℤ) : ℂ) * H.rt0) / 2 * z) = x z ≫ Xo.univ.t.act.act H.w0) → ∃ a ∈ lat hP (((ε : ℤ) : ℂ) * H.rt0), ∀ z : ℂ, x z = F.ex i P (z • P a) := by
  intro E _ _ _ H D l Xo σ g ty F _ _ _ _ C i P hP φ x ε hx hadd hw
  obtain ⟨L, hL⟩ := exists_linear_lift_of_isHolTo F i P hP (m := 1) (fun z => x (z 0)) (fun z w => hadd _ _) (by
    simp only [hx]
    exact HolFibre.isHolTo_comp (isHolTo_pt C) φ)
  have hv : ∀ z : ℂ, x z = F.ex i P (z • L fun _ => 1) := fun z => by
    rw [← map_smul, hL]
    simp
  have h1 : x 1 = 1 := by
    rw [← map_zero_eq_one x hadd]
    exact Over.OverMorphism.ext (by rw [hx, hx, pt_one])
  rw [hv, one_smul, F.ex_ker i P hP] at h1
  obtain ⟨a, ha⟩ := h1
  rw [← ha] at hv
  refine ⟨a, fun j hj => ?_, hv⟩
  set w : ℂ := (1 + ((ε : ℤ) : ℂ) * H.rt0) / 2 with hwdef
  have key : ∀ z : ℂ, z • (w • P a - P (H.w0 • a)) ∈ P.range := fun z => by
    have e1 := hw z
    rw [hv, hv, ← F.ex_lin i P hP] at e1
    have e2 : (fun k => ty k (H.w0 : E) * (z • P a) k) = z • P (H.w0 • a) := by
      funext k
      simp only [Pi.smul_apply, smul_eq_mul, hP.1]
      ring
    have e3 := F.ex_add i P hP (z • (w • P a - P (H.w0 • a))) (z • P (H.w0 • a))
    rw [← smul_add, sub_add_cancel, smul_smul, mul_comm z w, e1, e2] at e3
    exact (F.ex_ker i P hP _).1 (mul_eq_right.1 e3.symm)
  obtain ⟨b, hb⟩ := key 1
  rw [one_smul] at hb
  have hb0 : b = 0 := eq_zero_of_line hP (hb ▸ key)
  rw [hb0, map_zero] at hb
  have e4 := congrFun hb j
  simp only [Pi.zero_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hP.1] at e4
  have e5 : 2 * ty j (H.w0 : E) = 1 + ty j (H.rt : E) := by
    have := congrArg (fun s : 𝓞 E => ty j (s : E)) H.two_weight_eq_one_add_root
    simpa [map_ofNat] using this
  by_contra hne
  apply hj
  have e6 : w = ty j (H.w0 : E) := mul_right_cancel₀ hne (sub_eq_zero.1 e4.symm)
  rw [hwdef] at e6
  linear_combination -e5 - 2 * e6

end GlobalTheory.CurveHomLift
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.PjFree

namespace GlobalTheory.CuspSecFin

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem mem_SS_of_mem_holSub {Comp : Type} (X : Comp → Data E r) (la : ∀ k, Wt (X k).Ψ r)
    {P : FDSec X} (hP : P ∈ holSub X la) (k : Comp) : P k ∈ (X k).SS (la k) := by
  obtain ⟨⟨h0, hadd, hsmul⟩, -⟩ := siegelSpaceAlgebra_holds (E := E) r (X k) (la k) (la k) 0
  induction hP using Submodule.span_induction with
  | mem P hP => exact hP k
  | zero => exact h0
  | add P Q _ _ h1 h2 => exact hadd _ h1 _ h2
  | smul a P _ h1 => exact hsmul a _ h1

end GlobalTheory.CuspSecFin
end

section

noncomputable section

namespace GlobalTheory.CuspProduct

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

theorem mem_holSub_iff {Comp : Type} (X : Comp → Data E r) (la : ∀ k, Wt (X k).Ψ r)
    (P : FDSec X) : P ∈ holSub X la ↔ ∀ k, P k ∈ (X k).SS (la k) := by
  refine ⟨fun h => ?_, holCusp_mem_holSub X la⟩
  induction h using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => exact fun k => (siegelSpaceAlgebra_holds (E := E) r (X k) (la k) (la k) 0).1.1
  | add x y _ _ hx hy => exact fun k => (siegelSpaceAlgebra_holds (E := E) r (X k) (la k) (la k) 0).1.2.1 _ (hx k) _ (hy k)
  | smul a x _ hx => exact fun k => (siegelSpaceAlgebra_holds (E := E) r (X k) (la k) (la k) 0).1.2.2 a _ (hx k)


open Classical in
theorem rdU_mul {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (f g : Rul Xo c) : rdU U (f * g) = rdU U f * rdU U g := by
  funext k x
  show (if h : x ∈ (U.X k).dom then toC (evR Xo c (f * g) (U.un k ⟨x, h⟩)) else 0) =
    (if h : x ∈ (U.X k).dom then toC (evR Xo c f (U.un k ⟨x, h⟩)) else 0) *
      (if h : x ∈ (U.X k).dom then toC (evR Xo c g (U.un k ⟨x, h⟩)) else 0)
  split_ifs with h
  · exact evalAt_mul (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f g (U.un k ⟨x, h⟩)
  · simp

theorem laU_add {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (a a' : (E →+* ℂ) × ℕ → ℕ) (n n' : ℕ) (hn : Even n)
    (hn' : Even n') (k : U.Comp) : laU U (a + a') (n + n') k = laU U a n k + laU U a' n' k := by
  obtain ⟨m, rfl⟩ := hn
  obtain ⟨m', rfl⟩ := hn'
  have h1 : (m + m) / 2 = m := by omega
  have h2 : (m' + m') / 2 = m' := by omega
  have h3 : (m + m + (m' + m')) / 2 = m + m' := by omega
  funext τ j
  simp only [laU, Pi.add_apply, h1, h2, h3]
  split_ifs <;> push_cast <;> ring

theorem cuspMul_holds : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (r : ℕ)
    (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.CuspMul Xo c U := by
  intro E _ _ _ H Dw l Xo c r U a a' n n' f g hd hd' hf hg
  rw [mem_cusp] at hf hg ⊢
  refine ⟨mulC_mem_sec Xo c a a' n n' hf.1 hg.1, fun σ hσ => ?_⟩
  show rdU (U σ) (f * g) ∈ holSub (U σ).X (laU (U σ) (a + a') (n + n'))
  rw [rdU_mul, mem_holSub_iff]
  intro k
  rw [laU_add (U σ) a a' n n' hd.2 hd'.2 k]
  exact (siegelSpaceAlgebra_holds (E := E) r _ _ _ 0).2.1 _ ((mem_holSub_iff _ _ _).1 (hf.2 σ hσ) k) _
    ((mem_holSub_iff _ _ _).1 (hg.2 σ hσ) k).1

end GlobalTheory.CuspProduct
end
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain IsLocalRing ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.MainNotions.DIV.Cons
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_localData_prescribed_points_flag : ∀ (D : D7) (Pt : ℕ → ℕ → Type) (fld : ∀ j p, Pt j p → ModuliIntegralCharts.CF p) (L : ∀ j p, Pt j p → LatB D.host.E), (∀ j p y, (∀ a b, (L j p y).beta a b = (L j p y).beta b a) ∧ (∀ a a' b, (L j p y).beta (a + a') b = (L j p y).beta a b + (L j p y).beta a' b) ∧ (∀ (x x' : 𝓞 D.host.E), (x' : D.host.E) = D.host.conj (x : D.host.E) → ∀ a b, (L j p y).beta (x • a) b = (L j p y).beta a (x' • b)) ∧ (∃ (ι : Type) (_ : Fintype ι) (b : Module.Basis ι ℤ (L j p y).Y), ∀ x : ι → ℝ, x ≠ 0 → 0 < ∑ i, ∑ k, x i * x k * (L j p y).beta (b i) (b k)) ∧ ∃ ρ : ℕ, Module.finrank ℤ (L j p y).Y = 2 * D.R.f * ρ ∧ ρ ≤ (D.R.sigW j).1 ∧ ρ + (D.R.sigW j).1 ≤ D.R.r) → ∃ (P : ModuliIntegralCharts.Prov D) (dat : ℕ → P.Dat), ∀ j, 1 ≤ j → j < D.R.m → (P.rk (dat j) = D.R.r ∧ P.jj (dat j) = (D.R.sigW j).1) ∧ ∀ p y, ∃ η : (P.loc (dat j) p).Pt (P.loc (dat j) p).YY, (P.loc (dat j) p).fld η = fld j p y ∧ ∃ e : (P.loc (dat j) p).Ylat η ≃ₗ[𝓞 D.host.E] (L j p y).Y, ∀ a b, (L j p y).beta (e a) (e b) = (P.loc (dat j) p).be η a b := by
  first | exact @GlobalTheory.exists_prov_prescribed_points | exact GlobalTheory.exists_prov_prescribed_points | (intros; apply GlobalTheory.exists_prov_prescribed_points <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Matrix nonZeroDivisors
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi

namespace GlobalTheory

namespace FibreMatch

theorem surjective_of_countable {V W L : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [Countable L] (f : V →ₗ[ℂ] W) (P : L → W) (h : ∀ w, ∃ z a, w = f z + P a) : Function.Surjective f := by
  have hc : Countable (W ⧸ LinearMap.range f) :=
    Function.Surjective.countable (f := fun a => (LinearMap.range f).mkQ (P a)) fun q => by
      obtain ⟨w, rfl⟩ := (LinearMap.range f).mkQ_surjective q
      obtain ⟨z, a, rfl⟩ := h w
      refine ⟨a, ?_⟩
      have : (LinearMap.range f).mkQ (f z) = 0 := (Submodule.Quotient.mk_eq_zero _).2 ⟨z, rfl⟩
      simp only [map_add (f := _), this, zero_add]
  intro w
  by_contra hw
  have hq : (LinearMap.range f).mkQ w ≠ 0 := fun h0 => hw ((Submodule.Quotient.mk_eq_zero _).1 h0)
  have : Countable ℂ := (smul_left_injective ℂ hq).countable
  exact not_countable (α := ℝ) (Complex.ofReal_injective.countable)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem countable_La (D : Datum H) : Countable D.La := by
  have := D.fin
  have : Countable (𝓞 E) := Finsupp.Countable.of_moduleFinite (R := ℤ)
  exact Finsupp.Countable.of_moduleFinite (R := 𝓞 E)

theorem fibrewise {X : Scheme.{0}} (t : SAB H (Sp ℂ)) (t' : SAB H X) (D₁ D₂ : Datum H) {g : ℕ}
    (ty : Fin g → (E →+* ℂ))
    (P : D₁.La →+ (Fin g → ℂ)) (P' : D₂.La →+ (Fin g → ℂ)) (hP : IsPeriod D₁ ty P) (hP' : IsPeriod D₂ ty P')
    (y y' : Sp ℂ ⟶ X) (n : SABMap t t' y) (hy : (𝟙_ (Over (Sp ℂ))).hom ≫ y = y')
    (e : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ t.G)) (e' : (Fin g → ℂ) → (Over.mk y' ⟶ t'.G))
    (ha : ∀ z w, e (z + w) = e z * e w) (ha' : ∀ z w, e' (z + w) = e' z * e' w)
    (hs : Function.Surjective e)
    (hk : ∀ z, e z = 1 ↔ z ∈ P.range) (hk' : ∀ z, e' z = 1 ↔ z ∈ P'.range)
    (hl : ∀ (a : 𝓞 E) z, e (fun k => ty k (a : E) * z k) = e z ≫ t.act.act a)
    (hl' : ∀ (a : 𝓞 E) z, e' (fun k => ty k (a : E) * z k) = e' z ≫ t'.act.act a)
    (hw : ∀ (k : ℕ) (a b : D₁.La) (c : ℂˣ), 0 < k →
      (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D₁.EF a b : ℂ) / k) →
      Out.WeilIs t.G t.PP.L k (e ((k : ℂ)⁻¹ • P a)) (e ((k : ℂ)⁻¹ • P b)) (unitOn c))
    (hw' : ∀ (k : ℕ) (a b : D₂.La) (c : ℂˣ), 0 < k →
      (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D₂.EF a b : ℂ) / k) →
      Out.WeilIs t'.G t'.PP.L k (e' ((k : ℂ)⁻¹ • P' a)) (e' ((k : ℂ)⁻¹ • P' b)) (unitOn c))
    (hh : IsHolTo Set.univ (fun z => (e z).left)) (hh' : IsHolTo Set.univ (fun z => (e' z).left))
    (hd' : (∀ w, ∃! v : epsPt y' ⟶ t'.G, IsDerivAt0 (fun z => (e' z).left) w v.left) ∧
      ∀ v : epsPt y' ⟶ t'.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e' 0).left →
        ∃! w, IsDerivAt0 (fun z => (e' z).left) w v.left) :
    ∃ (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (gam : D₁.La ≃ₗ[𝓞 E] D₂.La), (∀ z, (e z).left ≫ n.φ = (e' (h z)).left) ∧
      (∀ a, P' (gam a) = h (P a)) ∧ (∀ a a', D₂.EF (gam a) (gam a') = D₁.EF a a') := by
  subst hy
  have dk' : DiscreteTopology {z // e' z = 1} := by
    have h0 : (fun z => e' z = 1) = fun z => z ∈ P'.range := funext fun z => propext (hk' z)
    show DiscreteTopology (Subtype fun z => e' z = 1)
    rw [h0]
    exact hP'.2.2.1
  let ρ := pushHom n.cart (𝟙_ (Over (Sp ℂ)))
  have hρ : ∀ x, (ρ x).left = x.left ≫ n.cm.F := fun _ => rfl
  have ρi : Function.Injective ρ := fun x x' hx => Over.OverMorphism.ext <| n.cart.1.hom_ext
    (by rw [← hρ, ← hρ, hx]) (by rw [Over.w, Over.w])
  have ρs : Function.Surjective ρ := fun x =>
    ⟨Over.homMk (n.cart.1.lift x.left (𝟙_ (Over (Sp ℂ))).hom (Over.w x)) (n.cart.1.lift_snd _ _ _),
      Over.OverMorphism.ext (n.cart.1.lift_fst _ _ _)⟩
  let ψ : pullback t.G.hom (𝟙 (Sp ℂ)) ⟶ pullback t'.G.hom ((𝟙_ (Over (Sp ℂ))).hom ≫ y) :=
    pullback.lift (pullback.fst _ _ ≫ n.cm.F) (pullback.snd _ _) (by
      rw [Category.assoc, n.cart.1.w, ← Category.assoc, pullback.condition, Category.assoc]
      rfl)
  have ψ₁ : ψ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ n.cm.F := pullback.lift_fst _ _ _
  have ψ₂ : ψ ≫ pullback.snd _ _ = pullback.snd _ _ := pullback.lift_snd _ _ _
  obtain ⟨f, hf, -⟩ := existsUnique_linear_lift_fibre (Sp ℂ) X t.G t'.G (𝟙 _) _ g g e e' ψ ρ t'.semi.smooth ha ha'
    hh hh' hd' dk' ψ₂ (fun x => pullback.hom_ext
      (by rw [Category.assoc, ψ₁, ← Category.assoc, UniformLift.fibPt_fst, UniformLift.fibPt_fst]; rfl)
      (by rw [Category.assoc, ψ₂, UniformLift.fibPt_snd, UniformLift.fibPt_snd]))
  have hf : ∀ z, e' (f z) = ρ (e z) := hf
  have := countable_La D₂
  have fs : Function.Surjective f := surjective_of_countable f P' fun w => by
    obtain ⟨x, hx⟩ := ρs (e' w)
    obtain ⟨z, rfl⟩ := hs x
    obtain ⟨a, ha⟩ := (hk' _).1 ((ExpUniqFamily.eq_iff_sub e' ha' w (f z)).1 (hx.symm.trans (hf z).symm))
    exact ⟨z, a, by rw [ha]; abel⟩
  let fe := LinearEquiv.ofBijective f ⟨LinearMap.injective_iff_surjective.2 fs, fs⟩
  obtain ⟨h, gam, h1, h2, -⟩ := ExpUniqFamily.algebraic (fun k (a : 𝓞 E) => ty k (a : E)) P P' hP.1 hP'.1
    hP.2.1 hP'.2.1 hP.2.2.1 hP'.2.2.1 (fun z => ρ (e z)) e' (fun z w => by rw [ha, map_mul]) ha'
    (fun z => by rw [← hk, map_eq_one_iff ρ ρi]) hk' (fun a x => x ≫ t'.act.act a)
    (fun a z => by
      rw [hl]
      apply Over.OverMorphism.ext
      rw [hρ, Over.comp_left, Over.comp_left, hρ, Category.assoc, n.act, Category.assoc])
    hl' f fe.symm hf (fun z => by
      rw [← hf]
      exact congrArg e' (fe.apply_symm_apply z))
  refine ⟨h, gam, fun z => by rw [h1, hρ], h2, fun a a' => ?_⟩
  refine ExpUniqFamily.int_eq_of_exp _ _ fun k hk0 => ?_
  have hL : LBIso t.PP.L (t'.PP.L.pull n.cm.F) := by
    obtain ⟨w, hw, -⟩ := n.lin
    exact ⟨w, hw⟩
  have w1 := (weilIs_grpPullback_of_comm X (Sp ℂ) t'.G t.G y n.cm.F t'.PP.L t.PP.L t'.PP.isLB t.PP.isLB n.cart hL
    _ k _ _ (ρ _) (ρ _) _ (hρ _) (hρ _)).1 (hw k a a' (Units.mk0 _ (Complex.exp_ne_zero _)) hk0 rfl)
  have w2 := hw' k (gam a) (gam a') (Units.mk0 _ (Complex.exp_ne_zero _)) hk0 rfl
  rw [h2, h2, ← map_smul h, ← map_smul h, h1, h1] at w2
  exact congrArg Units.val (weilIs_unique_fieldPoint X t'.G t'.PP.L t'.PP.isLB ℂ _ k _ _ _ _ w2 w1)

end FibreMatch

theorem familyUnif_fibre_lattice_match : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (U : FamilyUnif Xo σ ty) (i : Fin U.n) (P : (U.Di i).La →+ (Fin g → ℂ)) (D' : Datum H) (P' : D'.La →+ (Fin g → ℂ)) (t : SAB H (Sp ℂ)) (e : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ t.G)) (n : SABMap t Xo.univ.t (U.u i P)), IsPeriod (U.Di i) ty P → IsPeriod D' ty P' → (IsProper t.G.hom ∧ SmoothOfRelativeDimension g t.G.hom ∧ Out.RelAmple t.G t.PP.L ∧ Out.KTriv t.G t.PP.L ∧ DetCond D' t.act (𝟙 (Sp ℂ)) H.rt0 ∧ (∀ z w, e (z + w) = e z * e w) ∧ Function.Surjective e ∧ (∀ z, e z = 1 ↔ z ∈ P'.range) ∧ (∀ (a : 𝓞 E) z, e (fun k => ty k (a : E) * z k) = e z ≫ t.act.act a) ∧ IsHolTo Set.univ (fun z => (e z).left) ∧ ∀ (k : ℕ) (a b : D'.La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a b : ℂ) / k) → Out.WeilIs t.G t.PP.L k (e ((k : ℂ)⁻¹ • P' a)) (e ((k : ℂ)⁻¹ • P' b)) (unitOn c)) → ∃ (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (gam : D'.La ≃ₗ[𝓞 E] (U.Di i).La), (∀ z, (e z).left ≫ n.φ = (U.ex i P (h z)).left) ∧ (∀ a, P (gam a) = h (P' a)) ∧ ∀ a a', (U.Di i).EF (gam a) (gam a') = D'.EF a a' := by
  intro E _ _ _ H D l Xo σ g ty U i P D' P' t e n hP hP' ⟨_, _, _, _, _, ha, hs, hk, hl, hh, hw⟩
  exact FibreMatch.fibrewise t Xo.univ.t D' (U.Di i) ty P' P hP' hP _ _ n (Category.id_comp _) e (U.ex i P) ha
    (U.ex_add i P hP) hs hk (U.ex_ker i P hP) hl (U.ex_lin i P hP) hw (U.ex_weil i P hP) hh
    (ExpUniqFamily.isHolTo_ex U i P hP) (U.ex_diff i P hP)

end GlobalTheory
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.GlobalTheory.T.familyUnif_exp_unique_alt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (U : FamilyUnif Xo σ ty) (i j : Fin U.n) (P : (U.Di i).La →+ (Fin g → ℂ)) (P' : (U.Di j).La →+ (Fin g → ℂ)), IsPeriod (U.Di i) ty P → IsPeriod (U.Di j) ty P' → U.u i P = U.u j P' → ∃ (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (gam : (U.Di i).La ≃ₗ[𝓞 E] (U.Di j).La), (∀ z, (U.ex j P' (h z)).left = (U.ex i P z).left) ∧ (∀ a, P' (gam a) = h (P a)) ∧ (∀ a a', (U.Di j).EF (gam a) (gam a') = (U.Di i).EF a a') ∧ (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), ∃ e, gam (U.t i a) = U.t j a + l.M • e) ∧ ∀ a, ∃ e, gam (U.t i a) = U.t j a + l.A • e := by
  first | exact @GlobalTheory.familyUnif_exp_unique | exact GlobalTheory.familyUnif_exp_unique | (intros; apply GlobalTheory.familyUnif_exp_unique <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Matrix nonZeroDivisors
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi
theorem _root_.GlobalTheory.T.exists_universal_fibre_uniformised_triple : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (U : FamilyUnif Xo σ ty) (i : Fin U.n) (P : (U.Di i).La →+ (Fin g → ℂ)), σ (baseKA l).ρ = H.rt0 → g = Module.finrank ℚ E / 2 * (D.p + D.q) → IsPeriod (U.Di i) ty P → ∃ (t : SAB H (Sp ℂ)) (e : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ t.G)) (m : SABMap t Xo.univ.t (U.u i P)), (∀ z, (e z).left ≫ m.φ = (U.ex i P z).left) ∧ (IsProper t.G.hom ∧ SmoothOfRelativeDimension g t.G.hom ∧ Out.RelAmple t.G t.PP.L ∧ Out.KTriv t.G t.PP.L ∧ DetCond (U.Di i) t.act (𝟙 (Sp ℂ)) H.rt0 ∧ (∀ z w, e (z + w) = e z * e w) ∧ Function.Surjective e ∧ (∀ z, e z = 1 ↔ z ∈ P.range) ∧ (∀ (a : 𝓞 E) z, e (fun k => ty k (a : E) * z k) = e z ≫ t.act.act a) ∧ IsHolTo Set.univ (fun z => (e z).left) ∧ ∀ (k : ℕ) (a b : (U.Di i).La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * ((U.Di i).EF a b : ℂ) / k) → Out.WeilIs t.G t.PP.L k (e ((k : ℂ)⁻¹ • P a)) (e ((k : ℂ)⁻¹ • P b)) (unitOn c)) := by
  first | exact @GlobalTheory.UnivFibre.exists_fibre_uniformised | exact GlobalTheory.UnivFibre.exists_fibre_uniformised | (intros; apply GlobalTheory.UnivFibre.exists_fibre_uniformised <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Matrix nonZeroDivisors
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi
theorem _root_.GlobalTheory.T.exists_obj_of_uniformised_triple_complex : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D D' : Datum H) (l : Level H) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (P' : D'.La →+ (Fin g → ℂ)) (t : SAB H (Sp ℂ)) (e : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ t.G)) (f : ℕ → D.La →ₗ[𝓞 E] D'.La), l.A = 1 → σ (baseKA l).ρ = H.rt0 → D'.p = D.p → D'.q = D.q → IsPeriod D' ty P' → (IsProper t.G.hom ∧ SmoothOfRelativeDimension g t.G.hom ∧ Out.RelAmple t.G t.PP.L ∧ Out.KTriv t.G t.PP.L ∧ DetCond D' t.act (𝟙 (Sp ℂ)) H.rt0 ∧ (∀ z w, e (z + w) = e z * e w) ∧ Function.Surjective e ∧ (∀ z, e z = 1 ↔ z ∈ P'.range) ∧ (∀ (a : 𝓞 E) z, e (fun k => ty k (a : E) * z k) = e z ≫ t.act.act a) ∧ IsHolTo Set.univ (fun z => (e z).left) ∧ ∀ (k : ℕ) (a b : D'.La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a b : ℂ) / k) → Out.WeilIs t.G t.PP.L k (e ((k : ℂ)⁻¹ • P' a)) (e ((k : ℂ)⁻¹ • P' b)) (unitOn c)) → (∀ n m : ℕ, 0 < n → 0 < m → ∀ a, ∃ e, f (n * m) a = f n a + n • e) ∧ (∀ n : ℕ, 0 < n → (∀ a, (∃ e, f n a = n • e) ↔ ∃ e, a = n • e) ∧ ∀ a', ∃ a e, a' = f n a + n • e) → (∀ n : ℕ, 0 < n → ∀ a a', (n : ℤ) ∣ D'.EF (f n a) (f n a') - D.EF a a') → ∃ (o : Obj D l (baseKA l) (spMap σ)) (m : SABMap t o.t (𝟙 _)), ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), (e ((l.M : ℂ)⁻¹ • P' (f l.M a))).left ≫ m.φ = (o.eta a).left := by
  first | exact @GlobalTheory.UnifObj.exists_obj_of_uniformised | exact GlobalTheory.UnifObj.exists_obj_of_uniformised | (intros; apply GlobalTheory.UnifObj.exists_obj_of_uniformised <;> assumption)
end
