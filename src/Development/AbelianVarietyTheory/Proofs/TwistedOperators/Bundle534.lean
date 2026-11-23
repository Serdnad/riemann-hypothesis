module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle018
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle512
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle020
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle009
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.Bundle004
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle531
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HostGeneratorPowFourTraceNormModEight
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.KTypeExtension
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle007
public import Development.AbelianVarietyTheory.Definitions.Divisors.BplusOfEquivariant
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle515
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle054
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EventuallyAlgebraMapMemIntegers
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle406
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle514
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle301
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle401
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle197
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle085
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryTorusCompactQuotientFiniteVolume
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle517
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle005
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle516
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
import Mathlib.GroupTheory.IndexNSmul
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
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
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LevelPlusSubgroup
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OffQOfSizeRows
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselPeriodRightTranslateSobolevSepContinuous
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.FibrePushforward
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsPointedOfIsHkIsog
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle411
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Mult Formalism.MainNotions.S
open MeasureTheory IsDedekindDomain NumberField GlobalTheory.AdelicU GlobalTheory.Cusp GlobalTheory.Orb
open GlobalTheory.AutomorphicL2Unitary (starFn)
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors (HypH)
open GlobalTheory.IndefiniteRowSideFullHecke.ConstantTermVanishing

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.isParabolic_isotropicFlag_stabilizer_split_place : ∀ (D : D7) (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (s : SplitAt D.sp.cm.sig V.gram (frameLat V) v)
    (𝔉 : IsoFlag V), GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic.IsParabRad (parAt 𝔉 s)
      ((NLoc 𝔉 v).map (s.equiv : GLoc D.sp.cm.sig V.gram v →* GL (Fin V.rank) (Fv D.host.F v))) := by
  first | exact @GlobalTheory.SplitFlag.isParabRad_parAt | exact GlobalTheory.SplitFlag.isParabRad_parAt | (intros; apply GlobalTheory.SplitFlag.isParabRad_parAt <;> assumption)
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)

theorem _root_.GlobalTheory.T.heckeKernel_value_sum_weight_triangular_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (P : Ideal (𝓞 E)) (p i : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), admitted l P p → GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.TotalAt Xo c P p i → GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.FunAt Xo c P p i → ∀ f ∈ sec Xo c a n, ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra c.F Ω] (t : Ix Dw → Ωˣ) (y y' : FrPt Xo c Ω), FrBor t y y' → hkVal (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (fun Ω _ _ _ y => hkKer (Xo := Xo) P p i Ω y) (fun Ω _ _ _ y C z => hkRelFr P p i (hkTr Xo c p) Ω y C z) f y' = wchar (ex Dw a n) t * hkVal (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (fun Ω _ _ _ y => hkKer (Xo := Xo) P p i Ω y) (fun Ω _ _ _ y C z => hkRelFr P p i (hkTr Xo c p) Ω y C z) f y := by
  first | exact @GlobalTheory.HeckeWeight.hkVal_frBor | exact GlobalTheory.HeckeWeight.hkVal_frBor | (intros; apply GlobalTheory.HeckeWeight.hkVal_frBor <;> assumption)
end

section

open NumberField AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section

set_option autoImplicit false

namespace GlobalTheory.HeckeKerIdx

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}

theorem ex_smul_act (F : FamilyUnif Xo σ ty) (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ))
    (hP : IsPeriod (F.Di i) ty P) (c : ℂ) (r : 𝓞 E) (v : (F.Di i).La) :
    F.ex i P (c • P (r • v)) = F.ex i P (c • P v) ≫ Xo.univ.t.act.act r := by
  rw [← F.ex_lin i P hP]
  congr 1
  ext k
  rw [Pi.smul_apply, hP.1, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_left_comm]

theorem inv_smul_natCast {La : Type} [AddCommGroup La] [Module (𝓞 E) La] (P : La →+ (Fin g → ℂ)) {n : ℕ}
    (hn : n ≠ 0) (w : La) : ((n : ℂ))⁻¹ • P ((n : 𝓞 E) • w) = P w := by
  rw [Nat.cast_smul_eq_nsmul, map_nsmul, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
    inv_mul_cancel₀ (Nat.cast_ne_zero.2 hn), one_smul]

theorem sq_inv_smul_natCast {La : Type} [AddCommGroup La] [Module (𝓞 E) La] (P : La →+ (Fin g → ℂ)) {n : ℕ}
    (hn : n ≠ 0) (w : La) : ((n : ℂ) ^ 2)⁻¹ • P ((n : 𝓞 E) • w) = (n : ℂ)⁻¹ • P w := by
  rw [pow_two, mul_inv, mul_smul, inv_smul_natCast P hn]

theorem mem_span_smul_top {La : Type} [AddCommGroup La] [Module (𝓞 E) La] (n : ℕ) (x : La) :
    x ∈ Ideal.span {(n : 𝓞 E)} • (⊤ : Submodule (𝓞 E) La) ↔ ∃ b, (n : 𝓞 E) • b = x := by
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  simp

end GlobalTheory.HeckeKerIdx


open GlobalTheory.HeckeKerIdx in
theorem GlobalTheory.heckeKer_lattice_bounds : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty) (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ)) (𝔓 : Ideal (𝓞 E)) (p k : ℕ) (C : Subgroup (Over.mk (F.u i P) ⟶ Xo.univ.t.G)) (M : Submodule (𝓞 E) (F.Di i).La), IsPeriod (F.Di i) ty P → GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.IsHeckePrime l 𝔓 p → Xo.univ.t.HeckeKer (Over.mk (F.u i P)) Dw 𝔓 p k C → (∀ a, F.ex i P (((p : ℂ) ^ 2)⁻¹ • P a) ∈ C ↔ a ∈ M) → (Ideal.span {(p : 𝓞 E)} * 𝔓) • (⊤ : Submodule (𝓞 E) (F.Di i).La) ≤ M ∧ 𝔓.map (H.bar : 𝓞 E →+* 𝓞 E) • M ≤ Ideal.span {(p : 𝓞 E)} • (⊤ : Submodule (𝓞 E) (F.Di i).La) ∧ Nat.card (↥(Ideal.span {(p : 𝓞 E)} • (⊤ : Submodule (𝓞 E) (F.Di i).La)) ⧸ M.comap (Ideal.span {(p : 𝓞 E)} • (⊤ : Submodule (𝓞 E) (F.Di i).La)).subtype) = Ideal.absNorm 𝔓 ^ k := by
  intro E _ _ _ H Dw l Xo σ g ty F i P 𝔓 p k C M hP hH hK hM
  obtain ⟨-, -, -, hp, hp𝔓⟩ := hH
  have hp0 : p ≠ 0 := hp.ne_zero
  have hpC : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hp0
  refine ⟨?_, ?_, ?_⟩
  · rw [Submodule.smul_le]
    intro x hx a _
    obtain ⟨π, hπ, rfl⟩ := Ideal.mem_span_singleton_mul.1 hx
    obtain ⟨J, hJ⟩ : 𝔓 ∣ Ideal.span {(p : 𝓞 E)} :=
      Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hp𝔓)
    rw [← hM, mul_smul, sq_inv_smul_natCast P hp0]
    refine hK.2.1 J (by rw [hJ, mul_comm]) fun j hj => ?_
    rw [← ex_smul_act F i P hP, smul_smul]
    have hjπ : j * π ∈ Ideal.span {(p : 𝓞 E)} := by
      rw [hJ, mul_comm j]
      exact Ideal.mul_mem_mul hπ hj
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.1 hjπ
    rw [hc, mul_smul, inv_smul_natCast P hp0]
    exact (F.ex_ker i P hP _).2 ⟨_, rfl⟩
  · rw [Submodule.smul_le]
    intro r hr a ha
    have h1 := hK.2.2.1 ((hM a).2 ha) ((p : 𝓞 E) * r)
      (Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) hr)
    rw [← ex_smul_act F i P hP, mul_smul, sq_inv_smul_natCast P hp0, F.ex_ker i P hP] at h1
    obtain ⟨b, hb⟩ := h1
    rw [mem_span_smul_top]
    refine ⟨b, hP.2.1 ?_⟩
    rw [Nat.cast_smul_eq_nsmul, map_nsmul, hb, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ hpC, one_smul]
  · set N : Submodule (𝓞 E) (F.Di i).La := Ideal.span {(p : 𝓞 E)} • (⊤ : Submodule (𝓞 E) (F.Di i).La) with hN
    set Tp := GlobalTheory.HeckeKerModel.torsSub Xo.univ.t (Over.mk (F.u i P)) p with hTp
    have hmemTp : ∀ y, y ∈ Tp ↔ y ^ p = 1 := fun y => GlobalTheory.HeckeKerModel.mem_tors_span Xo.univ.t y p
    have hpow : ∀ w, F.ex i P w ^ p = F.ex i P (p • w) := fun w => (GlobalTheory.HeckeKerLat.ex_nsmul F i P hP p w).symm
    have hinvmem : ∀ b, F.ex i P ((p : ℂ)⁻¹ • P b) ∈ Tp := fun b => by
      rw [hmemTp, hpow, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ hpC, one_smul]
      exact (F.ex_ker i P hP _).2 ⟨b, rfl⟩
    have hmemN : ∀ x ∈ N, F.ex i P (((p : ℂ) ^ 2)⁻¹ • P x) ∈ Tp := fun x hx => by
      obtain ⟨b, rfl⟩ := (mem_span_smul_top p x).1 hx
      rw [sq_inv_smul_natCast P hp0]
      exact hinvmem b
    let fA : ↥N →+ Additive ↥Tp :=
      { toFun := fun x => Additive.ofMul ⟨F.ex i P (((p : ℂ) ^ 2)⁻¹ • P x), hmemN x.1 x.2⟩
        map_zero' := by
          apply Additive.toMul.injective
          apply Subtype.ext
          show F.ex i P (((p : ℂ) ^ 2)⁻¹ • P 0) = 1
          rw [map_zero, smul_zero]
          exact (F.ex_ker i P hP 0).2 (zero_mem _)
        map_add' := fun x y => by
          apply Additive.toMul.injective
          apply Subtype.ext
          show F.ex i P (((p : ℂ) ^ 2)⁻¹ • P (x.1 + y.1)) = F.ex i P (((p : ℂ) ^ 2)⁻¹ • P x.1) * F.ex i P (((p : ℂ) ^ 2)⁻¹ • P y.1)
          rw [map_add (f := _), smul_add, F.ex_add i P hP] }
    let h0 : (F.Di i).La →+ ↥N :=
      { toFun := fun a => ⟨(p : 𝓞 E) • a, (mem_span_smul_top p _).2 ⟨a, rfl⟩⟩
        map_zero' := by ext; simp
        map_add' := fun a b => by ext; simp [smul_add] }
    have hgsurj : Function.Surjective (fA.comp h0) := by
      intro y
      obtain ⟨w, hw⟩ := F.ex_onto i P hP (Additive.toMul y).1
      have h1 : F.ex i P (p • w) = 1 := by rw [← hpow, hw]; exact (hmemTp _).1 (Additive.toMul y).2
      obtain ⟨a, ha⟩ := (F.ex_ker i P hP _).1 h1
      refine ⟨a, ?_⟩
      apply Additive.toMul.injective
      apply Subtype.ext
      show F.ex i P (((p : ℂ) ^ 2)⁻¹ • P ((p : 𝓞 E) • a)) = (Additive.toMul y).1
      rw [sq_inv_smul_natCast P hp0, ha, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hpC, one_smul, hw]
    have hsurj : Function.Surjective fA := fun y => by
      obtain ⟨a, ha⟩ := hgsurj y
      exact ⟨h0 a, ha⟩
    set H' : AddSubgroup (Additive ↥Tp) := Subgroup.toAddSubgroup (C.subgroupOf Tp) with hH'
    have hker : (M.comap N.subtype).toAddSubgroup = H'.comap fA := by
      ext x
      rw [AddSubgroup.mem_comap]
      show x.1 ∈ M ↔ _
      rw [← hM]
      rfl
    have hidx : Nat.card (↥N ⧸ M.comap N.subtype) = H'.index := by
      rw [← AddSubgroup.index_comap_of_surjective H' hsurj, ← hker]
      rfl
    have hcardTp : Nat.card (Additive ↥Tp) = Nat.card (Xo.univ.t.tors (Over.mk (F.u i P)) (Ideal.span {(p : 𝓞 E)})) := rfl
    have hcardH : Nat.card H' = Nat.card ((C : Set (Over.mk (F.u i P) ⟶ Xo.univ.t.G)) ∩ Xo.univ.t.tors (Over.mk (F.u i P)) (Ideal.span {(p : 𝓞 E)}) : Set (Over.mk (F.u i P) ⟶ Xo.univ.t.G)) :=
      Nat.card_congr
        { toFun := fun z => ⟨(Additive.toMul z.1).1, z.2, (Additive.toMul z.1).2⟩
          invFun := fun z => ⟨Additive.ofMul ⟨z.1, z.2.2⟩, z.2.1⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
    have hfin : Nat.card (Additive ↥Tp) ≠ 0 := by
      have := (F.Di i).fin
      have := GlobalTheory.datum_free_int (F.Di i)
      have : Module.Finite ℤ (F.Di i).La := Module.Finite.trans (𝓞 E) (F.Di i).La
      have hle : (nsmulAddMonoidHom (α := (F.Di i).La) p).range ≤ (fA.comp h0).ker := by
        rintro _ ⟨b, rfl⟩
        rw [AddMonoidHom.mem_ker]
        apply Additive.toMul.injective
        apply Subtype.ext
        show F.ex i P (((p : ℂ) ^ 2)⁻¹ • P ((p : 𝓞 E) • (p • b))) = 1
        rw [sq_inv_smul_natCast P hp0, ← Nat.cast_smul_eq_nsmul (𝓞 E), inv_smul_natCast P hp0]
        exact (F.ex_ker i P hP _).2 ⟨b, rfl⟩
      have hd := AddSubgroup.index_dvd_of_le hle
      rw [AddSubgroup.index_range_nsmul, AddSubgroup.index_ker, AddMonoidHom.range_eq_top.2 hgsurj,
        AddSubgroup.card_top] at hd
      intro h0'
      rw [h0', zero_dvd_iff] at hd
      exact pow_ne_zero _ hp0 hd
    have key := H'.index_mul_card
    rw [hcardTp, hK.2.2.2.2.2, hcardH] at key
    rw [hidx]
    have hc : Nat.card ((C : Set (Over.mk (F.u i P) ⟶ Xo.univ.t.G)) ∩ Xo.univ.t.tors (Over.mk (F.u i P)) (Ideal.span {(p : 𝓞 E)}) : Set (Over.mk (F.u i P) ⟶ Xo.univ.t.G)) ≠ 0 := by
      intro hc0
      apply hfin
      rw [hcardTp, hK.2.2.2.2.2, hc0, zero_mul]
    rw [mul_comm (Nat.card _) (Ideal.absNorm 𝔓 ^ k)] at key
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hc) key
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.pureTensor_update_factor_from_base_vector : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f₀ : WO S T → ℂ) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsBase ψ θ S T sS sT ΛS ΛT f₀ → IsCovolOne (ratL T S) μ 𝓕 → ∀ (x x' : Place D → WO S T → ℂ) (f : WO S T → ℂ) (q : Place D), IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x f → x q = f₀ → (∀ p, p ≠ q → x' p = x p) → IsLocal ψ θ S T sS sT ΛS ΛT q (x' q) → ∃ f', IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x' f' ∧ ∀ (g g' : WO S T → ℂ) (c : ℂ), IsThetaFunO ψ S T g → IsThetaFunO ψ S T g' → (∀ w : WO S T, ipO μ 𝓕 (heisO ψ S T (wAt q w) f) g = c * ipO μ 𝓕 (heisO ψ S T (wAt q w) f₀) g') → ipO μ 𝓕 f' g = c * ipO μ 𝓕 (x' q) g' := by
  first | exact @GlobalTheory.PlaceTensorStep.change_factor | exact GlobalTheory.PlaceTensorStep.change_factor | (intros; apply GlobalTheory.PlaceTensorStep.change_factor <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
  MeasureTheory NumberField Matrix

namespace GlobalTheory.GKExtensionToSmoothVectors

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem gkExtension :
    GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.GKExtension D :=
  fun h₁ h₂ D => ⟨GlobalTheory.T.gKModuleMapCuspForms_extends_multiplicitySpace h₁ h₂ D, GlobalTheory.KFiniteDetermined.restrInj D⟩

end GlobalTheory.GKExtensionToSmoothVectors
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Mi.SepPer (contLeft)

theorem _root_.GlobalTheory.T.exists_compact_meets_besselTopRationalOrbits : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (M : Vol G), M.IsRow →
    ∃ Ω : Set (GA D (G.V (.grid D.R.m 0))), IsCompact Ω ∧ ∀ (h : GA D (G.V (.top 0))) (n : NFlag (G.V (.grid D.R.m 0)) G.besTop.e),
      ∃ γ ∈ GQ (G.V (.grid D.R.m 0)), γ * ((n : GA D (G.V (.grid D.R.m 0))) * embTop G h) ∈ Ω := by
  first | exact @GlobalTheory.BesCover.bplus_cover | exact GlobalTheory.BesCover.bplus_cover | (intros; apply GlobalTheory.BesCover.bplus_cover <;> assumption)
end

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

noncomputable section

namespace GlobalTheory.TestFamTr

section Local

variable {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] {μ : Measure G} [μ.IsMulLeftInvariant]

theorem conv_translate_left (f f' : G → ℂ) (c y : G) :
    GlobalTheory.AutomorphicL2Unitary.conv μ (fun x => f (c * x)) f' y = GlobalTheory.AutomorphicL2Unitary.conv μ f f' (c * y) := by
  simp only [GlobalTheory.AutomorphicL2Unitary.conv]
  rw [← integral_mul_left_eq_self _ c⁻¹]
  congr 1
  funext x
  simp [mul_assoc]

theorem conv_mul_left {f f' : G → ℂ} {k : G} (hf : ∀ y, f (k * y) = f y) (x : G) :
    GlobalTheory.AutomorphicL2Unitary.conv μ f f' (k * x) = GlobalTheory.AutomorphicL2Unitary.conv μ f f' x := by
  have := conv_translate_left (μ := μ) f f' k x
  rw [← this]
  simp only [hf]


omit [MeasurableMul G] [μ.IsMulLeftInvariant] in
theorem conv_mul_right {f f' : G → ℂ} {k : G} (hf' : ∀ y, f' (y * k) = f' y) (x : G) :
    GlobalTheory.AutomorphicL2Unitary.conv μ f f' (x * k) = GlobalTheory.AutomorphicL2Unitary.conv μ f f' x := by
  simp only [GlobalTheory.AutomorphicL2Unitary.conv, ← mul_assoc, hf']

end Local

theorem test_families : ∀ (D : D7) (V : HSp D) (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V), U.u ∉ T.S → ∀ (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)), (∀ v, (μf v).IsHaarMeasure) → (∀ᶠ v in cofinite, μf v (Kv V v) = 1) → ∀ ν, IsFinMeas V μf ν → ∃ e, IsFinFamily D.sp.cm.sig V.gram (frameLat V) e ∧ (∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W), GlobalTheory.PRep.IsSmooth σ → ∀ P, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp ν σ (finFn V e) P → P ∘ₗ P = P ∧ (HasTypeVec T σ → P ≠ 0)) ∧ ∀ g : GfC V, ∃ ff, IsFinFamily D.sp.cm.sig V.gram (frameLat V) ff ∧ (∀ k ∈ U.frame.iwahori, ∀ x, ff U.u (k * x) = ff U.u x) ∧ (∀ t ∈ strictTorus V.rank U.ϖ, IsTestFin T U μf (Function.update ff U.u (U.frame.cosetFn t)) ∧ SphRest T U (Function.update ff U.u (U.frame.cosetFn t))) ∧ ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W), GlobalTheory.PRep.IsSmooth σ → ∀ P, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp ν σ (finFn V e) P → GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp ν σ (finFn V ff) (P ∘ₗ σ g ∘ₗ P) := by
  intro D V T U hu μf hμf h1 ν hν
  obtain ⟨e, heF, heS, hee, heI, heSph, heNZ⟩ := GlobalTheory.T.exists_typeIwahoriMaximalCompact_idempotentFamily D V T U hu μf hμf h1 ν hν
  obtain ⟨-, hconv, hSB⟩ := GlobalTheory.T.convolution_finiteAdelicPureTensor_eq_localConvolutions D V μf hμf h1 ν hν e e heF heF
  have hfe : GlobalTheory.AutomorphicL2Unitary.conv ν (finFn V e) (finFn V e) = finFn V e := by
    rw [← hconv]
    congr 1
    funext v
    exact hee v
  refine ⟨e, heF, ?_, ?_⟩
  · intro W _ _ σ hσ P hP
    haveI := hν.1
    have h := (GlobalTheory.T.heckeOperator_convolution_and_leftTranslate (GfC V) ν W σ hσ (finFn V e) hSB (finFn V e) hSB P P hP hP).1
    rw [hfe] at h
    exact ⟨h.unique hP, fun ht => heNZ W σ hσ ht P hP⟩
  · intro g
    haveI := hν.1
    set c : ∀ v, GLoc D.sp.cm.sig V.gram v := fun v => (proj D.sp.cm.sig V.gram v (g : GA D V))⁻¹ with hc
    set b : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ := fun v x => e v (c v * x) with hb
    have hbF : IsFinFamily D.sp.cm.sig V.gram (frameLat V) b := by
      refine ⟨fun v => comp_mem_SB (heF.1 v) (Homeomorph.mulLeft (c v)), ?_⟩
      filter_upwards [heF.2, eventually_proj_mem_stabLoc D.sp.cm.sig V.gram (frameLat V) (g : GA D V)] with v he hg
      funext x
      have hcv : c v ∈ stabLoc D.sp.cm.sig V.gram (frameLat V) v := inv_mem hg
      simp only [hb, he, unitLoc, Set.indicator, SetLike.mem_coe, Subgroup.mul_mem_cancel_left _ hcv, Pi.one_apply]
    have hbfin : finFn V b = fun x => finFn V e (g⁻¹ * x) := by
      funext x
      simp [finFn, hb, hc, map_mul, map_inv]
    obtain ⟨hffF, hffeq, -⟩ := GlobalTheory.T.convolution_finiteAdelicPureTensor_eq_localConvolutions D V μf hμf h1 ν hν e b heF hbF
    obtain ⟨-, -, hbSB⟩ := GlobalTheory.T.convolution_finiteAdelicPureTensor_eq_localConvolutions D V μf hμf h1 ν hν b b hbF hbF
    have hcb : ∀ v, GlobalTheory.AutomorphicL2Unitary.conv (μf v) (b v) (e v) = b v := fun v => by
      haveI := hμf v
      funext y
      rw [hb]
      simp only
      rw [conv_translate_left, hee v]
    refine ⟨fun v => GlobalTheory.AutomorphicL2Unitary.conv (μf v) (e v) (b v), hffF, ?_, ?_, ?_⟩
    · intro k hk x
      haveI := hμf U.u
      exact conv_mul_left (heI k hk) x
    · intro t ht
      have hne : ∀ v ∈ T.S, v ≠ U.u := fun v hv h => hu (h ▸ hv)
      refine ⟨⟨hu, fun v => ⟨b v, hbF.1 v, ?_⟩, ⟨t, ht, Function.update_self ..⟩, fun v _ hv' => ?_, ?_⟩, ?_⟩
      · haveI := hμf v
        have hcont : ∀ f ∈ GlobalTheory.SplitWeil.SB (GLoc D.sp.cm.sig V.gram v), Continuous f ∧ HasCompactSupport f :=
          fun f hf => ⟨hf.1.continuous, hf.2⟩
        rw [Function.update_of_ne (hne v v.2), ← heS v,
          GlobalTheory.Orb.conv_assoc (hcont _ (heF.1 v)).1 (hcont _ (heF.1 v)).2 (hcont _ (hbF.1 v)).1 (hcont _ (hbF.1 v)).2
            (hcont _ (heF.1 v)).1, hcb]
      · rw [Function.update_of_ne hv']
        exact hffF.1 v
      · filter_upwards [hffF.2, eventually_cofinite_ne U.u] with v hv hv'
        rw [Function.update_of_ne hv']
        exact hv
      · intro v hv hvu k hk k' hk' x
        haveI := hμf v
        simp only [Function.update_of_ne hvu]
        rw [conv_mul_right, conv_mul_left]
        · intro y
          simpa using heSph v hv hvu k hk 1 (one_mem _) y
        · intro y
          simp only [hb]
          simpa [mul_assoc] using heSph v hv hvu 1 (one_mem _) k' hk' (c v * y)
    · intro W _ _ σ hσ P hP
      have h2 := (GlobalTheory.T.heckeOperator_convolution_and_leftTranslate (GfC V) ν W σ hσ (finFn V e) hSB (finFn V e) hSB P P hP hP).2 g
      rw [← hbfin] at h2
      have h3 := (GlobalTheory.T.heckeOperator_convolution_and_leftTranslate (GfC V) ν W σ hσ (finFn V e) hSB (finFn V b) hbSB P _ hP h2).1
      rwa [← hffeq] at h3
end TestFamTr
end GlobalTheory
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)

namespace GlobalTheory.HeckeEx

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {P : Ideal (𝓞 E)} {p i : ℕ}

theorem exists_carried (Z : KerScheme Xo P p i) {k : Type} [Field k] [IsAlgClosed k] (w : Sp k ⟶ Z.Hk)
    (y : Sp k ⟶ Xo.X) (hw : w ≫ Z.π₁ = y) :
    ∃ C : Subgroup (Over.mk y ⟶ Xo.univ.t.G), Xo.univ.t.HeckeKer (Over.mk y) Dw P p i C ∧
      ∀ C', Z.Carries w y C' ↔ C' = C := by
  subst hw
  obtain ⟨C₀, hC₀, hk⟩ := Z.hecke k w
  obtain ⟨ρ, e₀⟩ := GlobalTheory.HkSetPull.exists_equiv Z.m₁.cart (Over.mk w)
  have hh : ∀ (u : Over.mk w ⟶ Z.o₁.t.G) (v : Over.mk (w ≫ Z.π₁) ⟶ Xo.univ.t.G),
      v.left = u.left ≫ Z.m₁.toSABMap.φ → (u ∈ C₀ ↔ v ∈ Subgroup.comap ρ.symm.toMonoidHom C₀) := fun u v e => by
    rw [show v = ρ u from Over.OverMorphism.ext (e.trans (e₀ u).symm)]
    show _ ↔ ρ.symm (ρ u) ∈ C₀
    rw [ρ.symm_apply_apply]
  refine ⟨Subgroup.comap ρ.symm.toMonoidHom C₀,
    (GlobalTheory.HkSetPull.heckeKer_iff Dw P p i Z.m₁.toSABMap (Over.mk w) C₀ _ hh).1 hk, fun C' => ⟨fun h => ?_, ?_⟩⟩
  · ext v
    obtain ⟨u, rfl⟩ := ρ.surjective v
    exact (h.2 u _ (e₀ u)).symm.trans ((hC₀ u).symm.trans (hh u _ (e₀ u)))
  · rintro rfl
    exact ⟨rfl, fun u v e => (hC₀ u).symm.trans (hh u v e)⟩

theorem exists_equiv_carries : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (P : Ideal (𝓞 E)) (p i : ℕ) (Z : KerScheme Xo P p i), admitted l P p → ∀ (k : Type) [Field k] [IsAlgClosed k] (y : Sp k ⟶ Xo.X), ∃ e : {w : Sp k ⟶ Z.Hk // w ≫ Z.π₁ = y} ≃ {C : Subgroup (Over.mk y ⟶ Xo.univ.t.G) // Xo.univ.t.HeckeKer (Over.mk y) Dw P p i C}, ∀ w C, Z.Carries w.1 y C ↔ C = (e w).1 := by
  intro E _ _ _ H Dw l Xo P p i Z hA k _ _ y
  choose c hc hcc using fun w : {w : Sp k ⟶ Z.Hk // w ≫ Z.π₁ = y} => exists_carried Z w.1 y w.2
  refine ⟨Equiv.ofBijective (fun w => ⟨c w, hc w⟩) ⟨fun w w' e => ?_, fun C => ?_⟩, hcc⟩
  · exact Subtype.ext (((GlobalTheory.kerScheme_points E H Dw l Xo P p i Z hA).1 k y (c w) (hc w)).unique
      ((hcc w _).2 rfl) ((hcc w' _).2 (congrArg Subtype.val e)))
  · obtain ⟨z, hz, -⟩ := (GlobalTheory.kerScheme_points E H Dw l Xo P p i Z hA).1 k y C.1 C.2
    exact ⟨⟨z, hz.1⟩, Subtype.ext ((hcc ⟨z, hz.1⟩ _).1 hz).symm⟩

end GlobalTheory.HeckeEx
end

section

open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

theorem _root_.GlobalTheory.T.integral_charpolyKernel_eq_stableOrbitalIntegrals : ∀ (E : Type) [Field E] [NumberField E] (F : Subfield E) [NumberField F] (σ : E →ₐ[F] E), IsCMExt F E σ → Algebra.Unramified (𝓞 F) (𝓞 E) → ∀ (r : ℕ) (P : PPol σ r) (J : Matrix (Fin r) (Fin r) E), IsHermND σ J → ∀ (L : Submodule (𝓞 E) (Fin r → E)) [Submodule.IsFullLattice E L], ∀ μa μf μ, IsRestrictedProd σ J L μa μf μ → ∀ fa ff, (∀ w, Continuous (fa w) ∧ HasCompactSupport (fa w)) → IsFinFamily σ J L ff → ∀ dta dtf dt, IsTorusMeas P dta dtf dt → Integrable (descend (ratPts σ J) (polKernel P J (tensor σ J fa ff))) (quotMeasure (ratPts σ J) μ) ∧ ∫ q, descend (ratPts σ J) (polKernel P J (tensor σ J fa ff)) q ∂quotMeasure (ratPts σ J) μ = ((torVol P dt).toReal : ℂ) * (∏ᶠ v, Phi (J := J) (μf v) (dtf v) (ff v)) * ∏ w, Phi (J := J) (μa w) (dta w) (fa w) := by
  first | exact @GlobalTheory.TrEll.integral_polKernel | exact GlobalTheory.TrEll.integral_polKernel | (intros; apply GlobalTheory.TrEll.integral_polKernel <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.coreChain_lifts_surjective_of_evenRank : (∀ D : D7, GlobalTheory.EvenOnto.OntoAll D) → ComOK → StageOK → ChainEx → TopCols → CoreOnto := by
  first | exact @GlobalTheory.CoreOnto.coreOnto_of_chain | exact GlobalTheory.CoreOnto.coreOnto_of_chain | (intros; apply GlobalTheory.CoreOnto.coreOnto_of_chain <;> assumption)
end
