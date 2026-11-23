module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle018
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle011
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.Bundle020
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.Bundle008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.Bundle004
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle030
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsTypeAndIsLocallyCrystallineRz
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle015
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle019
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.DualNumber
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

namespace GlobalTheory.OrdLoc.RootConjugation

private theorem map_conj {A B G : Type} [CommRing A] [CommRing B] [Group G] (f : A →+* B) (h : GL (Fin 3) A)
    (r : G →* GG (m := 3) (R := A)) (g : G) :
    GG.map f (conjBy h r g) = GG.ofGL (Matrix.GeneralLinearGroup.map f h) * GG.map f (r g) *
      (GG.ofGL (Matrix.GeneralLinearGroup.map f h))⁻¹ := by
  have e : GG.map f (GG.ofGL h) = GG.ofGL (Matrix.GeneralLinearGroup.map f h) := by
    unfold GG.map
    rw [SemidirectProduct.map_inl]
  have e2 : conjBy h r g = GG.ofGL h * r g * (GG.ofGL h)⁻¹ := rfl
  rw [e2, map_mul, map_mul, map_inv, e]

private theorem push_conj {O A B G : Type} [CommRing O] [CommRing A] [CommRing B] [Algebra O A] [Algebra O B]
    [Group G] (f : A →ₐ[O] B) (h : GL (Fin 3) A) (r : G →* GG (m := 3) (R := A)) :
    push f (conjBy h r) = conjBy (Matrix.GeneralLinearGroup.map (f : A →+* B) h) (push f r) :=
  MonoidHom.ext fun g => map_conj _ h r g

private theorem conjBy_one {A G : Type} [CommRing A] [Group G] (r : G →* GG (m := 3) (R := A)) :
    conjBy 1 r = r := by
  refine MonoidHom.ext fun g => ?_
  have e2 : conjBy 1 r g = GG.ofGL 1 * r g * (GG.ofGL 1)⁻¹ := rfl
  rw [e2, map_one, one_mul, inv_one, mul_one]

private theorem exists_conjLift {O : Type} [CommRing O] [IsLocalRing O] {Γ : Type} [Group Γ] [TopologicalSpace Γ]
    {η : Γ →* ℤˣ} {Ψ : Γ →* Oˣ} (hη : IsLocallyConstant η) {R : Type} [CommRing R] [Algebra O R] [IsCO O R]
    (r : GLift O η Ψ R) (h : GL (Fin 3) R) (hh : CongOne (maximalIdeal R) h) :
    ∃ r' : GLift O η Ψ R, r'.hom = conjBy h r.hom := by
  refine ⟨⟨conjBy h r.hom, fun a b N => ?_, fun g => ?_⟩, rfl⟩
  · have h1 : IsLocallyConstant fun g => GG.map (Ideal.Quotient.mk (maximalIdeal R ^ N)) (r.hom g) := by
      rw [IsLocallyConstant.iff_eventually_eq]
      intro x
      have h2 : ∀ᶠ y in nhds x, ∀ a b, Ideal.Quotient.mk (maximalIdeal R ^ N) ((r.hom y).mat a b) =
          Ideal.Quotient.mk (maximalIdeal R ^ N) ((r.hom x).mat a b) :=
        Filter.eventually_all.2 fun a => Filter.eventually_all.2 fun b => (r.cont a b N).eventually_eq x
      filter_upwards [h2, hη.eventually_eq x] with y h3 h4
      refine SemidirectProduct.ext (Units.ext (Matrix.ext h3)) ?_
      rw [GG.map_right, GG.map_right, r.hasMult y, r.hasMult x, h4]
    have h5 := h1.comp fun z => GG.mat (GG.ofGL (Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk _) h) * z *
      (GG.ofGL (Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk _) h))⁻¹) a b
    convert h5 using 2 with g
    rw [Function.comp_apply, ← map_conj]
    rfl
  · have e : Matrix.GeneralLinearGroup.map (res O R : R →+* ResidueField O) h = 1 := by
      refine Units.ext (Matrix.ext fun a b => ?_)
      have h1 := (res_eq_zero_iff O R _).2 (hh a b)
      rw [Matrix.sub_apply, map_sub, sub_eq_zero] at h1
      refine h1.trans ?_
      simp only [Matrix.one_apply, Units.val_one]
      split_ifs <;> simp
    rw [map_conj, e, map_one, one_mul, inv_one, mul_one, r.red]

private theorem eta_lc {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O]
    (D : Dat3 l O) : IsLocallyConstant D.η := by
  haveI := D.Kv.2
  have ho : IsOpen (GK D.Kv : Set (GQ l)) := IntermediateField.fixingSubgroup_isOpen D.Kv.1
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  refine ⟨(fun y => x⁻¹ * y) ⁻¹' (GK D.Kv : Set (GQ l)), ho.preimage (by fun_prop), by simp, fun y hy => ?_⟩
  have h1 := (D.η_ker _).2 hy
  rw [map_mul, map_inv, inv_mul_eq_one] at h1
  exact h1.symm

private theorem exists_univMat (R : Type) [CommRing R] :
    ∃ h : GL (Fin 3) (MvPowerSeries (Fin 3 × Fin 3) R), ∀ a b,
      h.val a b = (1 : Matrix (Fin 3) (Fin 3) (MvPowerSeries (Fin 3 × Fin 3) R)) a b + MvPowerSeries.X (a, b) := by
  let M : Matrix (Fin 3) (Fin 3) (MvPowerSeries (Fin 3 × Fin 3) R) := 1 + Matrix.of fun a b => MvPowerSeries.X (a, b)
  have hM : IsUnit M := by
    rw [Matrix.isUnit_iff_isUnit_det, MvPowerSeries.isUnit_iff_constantCoeff, RingHom.map_det]
    have : (MvPowerSeries.constantCoeff (σ := Fin 3 × Fin 3) (R := R)).mapMatrix M = 1 := by
      rw [map_add (f := _), map_one]
      ext a b
      simp
    rw [this, Matrix.det_one]
    exact isUnit_one
  exact ⟨hM.unit, fun a b => rfl⟩

private theorem gl_ext {S C : Type} [CommRing S] [CommRing C] (F : S →+* C) (u : GL (Fin 3) S) (h : GL (Fin 3) C)
    (x : Fin 3 × Fin 3 → S) (hu : ∀ a b, (u : Matrix (Fin 3) (Fin 3) S) a b = (1 : Matrix (Fin 3) (Fin 3) S) a b + x (a, b))
    (hx : ∀ a b, F (x (a, b)) = ((h : Matrix (Fin 3) (Fin 3) C) - 1) a b) :
    Matrix.GeneralLinearGroup.map F u = h := by
  refine Units.ext (Matrix.ext fun a b => ?_)
  show F ((u : Matrix (Fin 3) (Fin 3) S) a b) = _
  rw [hu, map_add (f := _), hx, Matrix.sub_apply]
  simp only [Matrix.one_apply]
  split_ifs <;> simp

end GlobalTheory.OrdLoc.RootConjugation


open GlobalTheory.OrdLoc.RootConjugation in
theorem GlobalTheory.OrdLoc.rtConj :
    LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O]
    [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O)
    (U : _root_.UpperTheory.V.U3.Univ (_root_.UpperTheory.V.U3.GCond.noCondition O D.η D.Ψ))
    (C : Type) [CommRing C] [Algebra O C] [IsCO O C] (r : GQ l →* GG (m := 3) (R := C))
    (h : GL (Fin 3) C), UpperTheory.V.UnitaryThreeInertia.InHat h → Dat3.On D U r →
      Dat3.On D U (conjBy h r) := by
  intro hP l _ O _ _ _ _ _ _ _ D U C _ _ _ r h hh hr
  obtain ⟨f, rfl, hf⟩ := hr
  obtain ⟨hpr, hprime, hl, hIt, -, -, -⟩ := GlobalTheory.T.ordinaryComponent_unique_prime_dim_thirteen_near_base hP D U
  have hmin : GlobalTheory.OrdLoc.It D U ∈ (GlobalTheory.OrdLoc.Icr D U).minimalPrimes := by
    have : GlobalTheory.OrdLoc.It D U ∈ GlobalTheory.OrdLoc.primesAt0 D U := by rw [hpr]; rfl
    exact this.1
  haveI := hprime
  let q : U.R →ₐ[O] GlobalTheory.OrdLoc.Rt D U := Ideal.Quotient.mkₐ O (GlobalTheory.OrdLoc.It D U)
  haveI : IsCO O (GlobalTheory.OrdLoc.Rt D U) := co_quot O U.R _ q (Ideal.Quotient.mkₐ_surjective O _)
  let S := MvPowerSeries (Fin 3 × Fin 3) (GlobalTheory.OrdLoc.Rt D U)
  haveI : IsCO O S := co_mvps O _ _
  haveI : IsDomain S := NoZeroDivisors.to_isDomain S
  let i : U.R →ₐ[O] S := (IsScalarTower.toAlgHom O (GlobalTheory.OrdLoc.Rt D U) S).comp q
  have hi : ∀ a, i a = MvPowerSeries.C (q a) := fun a => rfl
  have hiI : ∀ a ∈ GlobalTheory.OrdLoc.It D U, i a = 0 := fun a ha => by
    rw [hi, show q a = 0 from Ideal.Quotient.eq_zero_iff_mem.2 ha, map_zero]
  obtain ⟨u, hu⟩ := exists_univMat (GlobalTheory.OrdLoc.Rt D U)
  have hu1 : CongOne (maximalIdeal S) u := fun a b => by
    rw [Matrix.sub_apply, hu, add_sub_cancel_left]
    intro hx
    have := MvPowerSeries.isUnit_constantCoeff _ hx
    simp at this
  obtain ⟨r', hr'⟩ := exists_conjLift (eta_lc D) (U.r.map i) u hu1
  obtain ⟨α, hα, -⟩ := (U.rep S).2 r' trivial
  have hα' : push α U.r.hom = conjBy u (push i U.r.hom) := (congrArg GLift.hom hα).trans hr'
  have hcomp : ∀ {T : Type} [CommRing T] [Algebra O T] (y : S →ₐ[O] T), push (y.comp α) U.r.hom =
      conjBy (Matrix.GeneralLinearGroup.map (y : S →+* T) u) (push (y.comp i) U.r.hom) := fun y => by
    show push y (push α U.r.hom) = _
    rw [hα', push_conj]
    rfl
  have hIY : GlobalTheory.OrdLoc.IY D U ≤ RingHom.ker i := fun a ha =>
    hiI a (hIt (Ideal.le_radical ha))
  have hdel : i (GlobalTheory.OrdLoc.del D U.r.hom) ≠ 0 := by
    rw [hi]
    intro h0
    have h1 : q (GlobalTheory.OrdLoc.del D U.r.hom) = 0 := by
      have := congrArg MvPowerSeries.constantCoeff h0
      simpa using this
    exact GlobalTheory.T.saturatingElement_notMem_minimalPrimes_reducedOrdinaryIdeal D U _ hmin (Ideal.Quotient.eq_zero_iff_mem.1 h1)
  have h1 : GlobalTheory.OrdLoc.Icr D U ≤ RingHom.ker α := GlobalTheory.T.reducedOrdinaryIdeal_le_ker_of_conj_of_saturating_ne_zero D U S i α u hα' hIY hdel
  obtain ⟨c, ⟨hc1, hc2⟩, -⟩ := co_ev O (GlobalTheory.OrdLoc.Rt D U) (GlobalTheory.OrdLoc.Rt D U) (Fin 3 × Fin 3) (AlgHom.id O _) 0 fun _ => zero_mem _
  have h2 : c.comp α = q := by
    have e1 : c.comp i = q := AlgHom.ext fun a => hc1 _
    refine ((U.rep (GlobalTheory.OrdLoc.Rt D U)).2 (U.r.map q) trivial).unique (GLift.ext ?_) rfl
    show push (c.comp α) U.r.hom = push q U.r.hom
    rw [hcomp, e1, gl_ext (c : S →+* GlobalTheory.OrdLoc.Rt D U) u 1 _ hu fun a b => (hc2 _).trans (by simp), conjBy_one]
  have h3 : RingHom.ker α ≤ GlobalTheory.OrdLoc.It D U := fun a ha => by
    have : q a = 0 := by
      rw [← h2, AlgHom.comp_apply, show α a = 0 from ha, map_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.1 this
  have h4 : GlobalTheory.OrdLoc.It D U ≤ RingHom.ker α := hmin.2 ⟨RingHom.ker_isPrime α, h1⟩ h3
  obtain ⟨F, ⟨hF1, hF2⟩, -⟩ := co_ev O (GlobalTheory.OrdLoc.Rt D U) C (Fin 3 × Fin 3) (Ideal.Quotient.liftₐ (GlobalTheory.OrdLoc.It D U) f fun a ha => hf ha)
    (fun s => ((h : Matrix (Fin 3) (Fin 3) C) - 1) s.1 s.2) fun s => hh s.1 s.2
  refine ⟨F.comp α, ?_, fun a ha => ?_⟩
  · have e1 : F.comp i = f := AlgHom.ext fun a => hF1 _
    rw [hcomp, e1, gl_ext (F : S →+* C) u h _ hu fun a b => hF2 _]
  · show F (α a) = 0
    rw [show α a = 0 from h4 ha, map_zero]
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

namespace GlobalTheory.OrdLoc.TangentDual

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O]
  [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (U : _root_.UpperTheory.V.U3.Univ (_root_.UpperTheory.V.U3.GCond.noCondition O D.η D.Ψ))

omit [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] [CharZero O] in
theorem push_base (E : Type) [Field E] [Algebra O E] {x : U.R →ₐ[O] O} (hx : IsBase D.η D.Ψ U.r.hom x) :
    push ((Algebra.ofId O E).comp x) U.r.hom = D.rz E := by
  unfold Dat3.rz
  rw [← show push x U.r.hom = r0 D.η D.Ψ from hx]
  rfl

theorem cont_push (B : Type) [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra O B]
    [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] O B] [IsScalarTower ℤ_[l] ℚ_[l] B] (f : U.R →ₐ[O] B) (a b : Fin 3) :
    QCont l fun g => (push f U.r.hom g).mat a b :=
  (ptCont (l := l) U.R B f).1 (GQ l) (fun g => (U.r.hom g).mat a b) (U.r.cont a b)

omit [IsDomain O] in
theorem qcont_dual {X E : Type} [TopologicalSpace X] [Field E] [Algebra ℚ_[l] E]
    [TopologicalSpace E] [IsModuleTopology ℚ_[l] E] (f : X → DualNumber E) (h1 : Continuous fun x => (f x).fst)
    (h2 : Continuous fun x => (f x).snd) : QCont l f := by
  have e : f = fun x => ((TrivSqZeroExt.inlAlgHom ℚ_[l] E E).toLinearMap (f x).fst) +
      (((TrivSqZeroExt.inrHom E E).restrictScalars ℚ_[l]) (f x).snd) :=
    funext fun x => (TrivSqZeroExt.inl_fst_add_inr_snd_eq _).symm
  unfold QCont
  letI : TopologicalSpace (DualNumber E) := moduleTopology ℚ_[l] _
  haveI : IsModuleTopology ℚ_[l] (DualNumber E) := ⟨rfl⟩
  haveI := IsModuleTopology.toContinuousAdd ℚ_[l] (DualNumber E)
  rw [e]
  exact ((IsModuleTopology.continuous_of_linearMap _).comp h1).add
    ((IsModuleTopology.continuous_of_linearMap _).comp h2)

end GlobalTheory.OrdLoc.TangentDual


open GlobalTheory.OrdLoc.TangentDual in
theorem GlobalTheory.OrdLoc.rtTangent :
    LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (U : _root_.UpperTheory.V.U3.Univ (_root_.UpperTheory.V.U3.GCond.noCondition O D.η D.Ψ)) (E : Type) [Field E] [Algebra ℚ_[l] E] [Module.Finite ℚ_[l] E] [Algebra O E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] O E] [IsScalarTower ℤ_[l] ℚ_[l] E] [TopologicalSpace E] [IsModuleTopology ℚ_[l] E] [IsTopologicalRing E], ∀ γ ∈ Z1 (adRep (D.rz E)), ∀ r' : GQ l →* GG (m := 3) (R := DualNumber E), DualDef (D.rz E) γ r' → (D.On U r' ↔ γ ∈ finiteCocycles (MonoidHom.id _) (adRep (D.rz E))) := by
  intro hP l _ O _ _ _ _ _ _ _ D U E _ _ _ _ _ _ _ _ _ _ γ hγ r' hr'
  obtain ⟨x, hx, -⟩ := univEx D U
  have hc : Continuous fun g => (D.rz E g).mat := by
    refine continuous_matrix fun a b => ?_
    have h := cont_push D U E ((Algebra.ofId O E).comp x) a b
    rw [push_base D U E hx] at h
    unfold QCont at h
    rwa [← eq_moduleTopology ℚ_[l] E] at h
  have hm : HasMult D.η (D.rz E) := fun g => rfl
  have hdc := dualCr D E (D.rz E) hm hc γ hγ r' hr'
  haveI : Module.Finite E (DualNumber E) := inferInstanceAs (Module.Finite E (E × E))
  haveI : Module.Finite ℚ_[l] (DualNumber E) := inferInstanceAs (Module.Finite ℚ_[l] (E × E))
  have hred : (GG.map (TrivSqZeroExt.fstHom E E E : DualNumber E →+* E)).comp r' = D.rz E := by
    refine MonoidHom.ext fun g => SemidirectProduct.ext (Units.ext (Matrix.ext fun a b => ?_)) (hr' g).1
    exact congrArg TrivSqZeroExt.fst ((hr' g).2 a b)
  rw [GlobalTheory.T.onOrdinaryComponent_iff_continuous_crystalline_lift hP D U E (DualNumber E) (TrivSqZeroExt.fstHom E E E)
    (fun a ha => TrivSqZeroExt.isNilpotent_iff_isNilpotent_fst.2 (by rw [show a.fst = 0 from ha]; exact IsNilpotent.zero))
    r' hred]
  refine ⟨fun h => (hdc.1 h.cr).2, fun h => ⟨fun g => (hr' g).1, hred, fun a b => ?_, hdc.2 ⟨(isType_and_isLocallyCrystalline_rz D E).2, h⟩⟩⟩
  refine qcont_dual _ ?_ ?_
  · simp only [(hr' _).2]
    exact hc.matrix_elem a b
  · simp only [(hr' _).2]
    exact (hγ.1.matrix_mul hc).matrix_elem a b
end
