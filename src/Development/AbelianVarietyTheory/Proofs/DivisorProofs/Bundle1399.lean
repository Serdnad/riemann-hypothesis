module

public import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1297
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1204
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle547
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1127
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1299
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1094
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle965
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle849
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermAutomorphicFormIntegral
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle032
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle033
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1300
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1301
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
import Mathlib.RingTheory.Radical.NatInt
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
import ReciprocityTheory.AnalyticForms.PotentialTheory.LocDens
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1298
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle004

@[expose] public section

section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

namespace GlobalTheory.ChernMass

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {L : LB X}

theorem sub_pick_eq (φ ψ : Weight p σ L) {y : CxPts p σ} {i : L.ι} (hi : y ∈ ptsIn p σ (L.U i)) :
    ψ.φ (pick φ.isLB y) y - φ.φ (pick φ.isLB y) y = ψ.φ i y - φ.φ i y := by
  rw [ψ.trans _ i y (mem_pick φ.isLB y) hi, φ.trans _ i y (mem_pick φ.isLB y) hi]
  ring

theorem cInfAt_half_sub {φ ψ : Weight p σ L} (hφ : φ.IsCInf) (hψ : ψ.IsCInf) (x : CxPts p σ) :
    CInfAt (fun y => (ψ.φ (pick φ.isLB y) y - φ.φ (pick φ.isLB y) y) / 2) x := by
  have hx := mem_pick φ.isLB x
  refine (((hψ _ x hx).add (hφ _ x hx).neg).const_mul 2⁻¹).congr ?_
  filter_upwards [(isOpen_ptsIn _).mem_nhds hx] with z hz
  rw [sub_pick_eq φ ψ hz]
  ring

theorem mInt_one_eq {D : ℕ} [CompactSpace (CxPts p σ)] [T2Space (CxPts p σ)]
    {A : FinHolAtlas D (CxPts p σ)} (hA : IsAlgAtlas A) {φ ψ : Weight p σ L} (hφ : φ.IsCInf)
    (hψ : ψ.IsCInf) :
    mInt A (fun _ => φ.locPot) (fun _ => 1) = mInt A (fun _ => ψ.locPot) (fun _ => 1) := by
  have hP : IsPotential A φ.locPot :=
    ((Weight.isCInf_iff_isSmooth hA.anRead).1 hφ).isPotential hA
  have hu : A.Smooth fun y => (ψ.φ (pick φ.isLB y) y - φ.φ (pick φ.isLB y) y) / 2 :=
    (hA.smooth_iff hA.anRead).2 ((cInfAt_iff_smoothOn hA.anRead isOpen_univ).1
      fun y _ => cInfAt_half_sub hφ hψ y)
  rw [← massIndep A (fun _ => φ.locPot) (fun _ => _) (fun _ => hP) fun _ => hu]
  refine SameForm.mInt_eq (fun _ j y hy => hessCGerm _ _ _ ?_) _
  refine eventually_of_mem (((A.chart j).isOpen_inter_preimage_symm (isOpen_ptsIn _)).mem_nhds
    ⟨hy, mem_pick φ.isLB ((A.chart j).symm y)⟩) fun w hw => ?_
  change φ.φ _ _ / 2 + (_ - _) / 2 = ψ.φ (pick φ.isLB _) _ / 2
  rw [sub_pick_eq φ ψ hw.2]
  ring

theorem chernInt_one_eq : ∀ (Y : Var ℂ) (L : LB Y.X) (φ ψ : Weight Y.str (RingHom.id ℂ) L), φ.IsCInf → ψ.IsCInf → Weight.chernInt φ Y.dim Set.univ (fun _ => 1) = Weight.chernInt ψ Y.dim Set.univ (fun _ => 1) := fun Y L φ ψ hφ hψ => by
  obtain ⟨h₁, h₂, -, A, hA⟩ := GlobalTheory.T.complexPoints_smoothProjVariety_compact_manifold Y
  rw [(GlobalTheory.T.chernIntegral_one_eq_mongeAmpereIntegral Y L φ hφ).2 A hA, (GlobalTheory.T.chernIntegral_one_eq_mongeAmpereIntegral Y L ψ hψ).2 A hA]
  exact mInt_one_eq hA hφ hψ

end GlobalTheory.ChernMass
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct

namespace GlobalTheory.QuatTop

variable {R : Type} [CommRing R] [TopologicalSpace R] {a b : R}

theorem continuous_coord_re : Continuous (fun x : ℍ[R, a, b] => x.re) :=
  (continuous_apply (0 : Fin 4)).comp (continuous_induced_dom (f := (coords : ℍ[R, a, b] → Fin 4 → R)))

theorem continuous_coord_imI : Continuous (fun x : ℍ[R, a, b] => x.imI) :=
  (continuous_apply (1 : Fin 4)).comp (continuous_induced_dom (f := (coords : ℍ[R, a, b] → Fin 4 → R)))

theorem continuous_coord_imJ : Continuous (fun x : ℍ[R, a, b] => x.imJ) :=
  (continuous_apply (2 : Fin 4)).comp (continuous_induced_dom (f := (coords : ℍ[R, a, b] → Fin 4 → R)))

theorem continuous_coord_imK : Continuous (fun x : ℍ[R, a, b] => x.imK) :=
  (continuous_apply (3 : Fin 4)).comp (continuous_induced_dom (f := (coords : ℍ[R, a, b] → Fin 4 → R)))

theorem continuous_of_coords {X : Type*} [TopologicalSpace X] {g : X → ℍ[R, a, b]}
    (h0 : Continuous fun x => (g x).re) (h1 : Continuous fun x => (g x).imI)
    (h2 : Continuous fun x => (g x).imJ) (h3 : Continuous fun x => (g x).imK) : Continuous g := by
  refine continuous_induced_rng.2 (continuous_pi fun i => ?_)
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3

theorem isTopologicalRing [IsTopologicalRing R] : IsTopologicalRing ℍ[R, a, b] := by
  have c0 := (continuous_coord_re (R := R) (a := a) (b := b))
  have c1 := (continuous_coord_imI (R := R) (a := a) (b := b))
  have c2 := (continuous_coord_imJ (R := R) (a := a) (b := b))
  have c3 := (continuous_coord_imK (R := R) (a := a) (b := b))
  have p0 := c0.comp (continuous_fst (X := ℍ[R, a, b]) (Y := ℍ[R, a, b]))
  have p1 := c1.comp (continuous_fst (X := ℍ[R, a, b]) (Y := ℍ[R, a, b]))
  have p2 := c2.comp (continuous_fst (X := ℍ[R, a, b]) (Y := ℍ[R, a, b]))
  have p3 := c3.comp (continuous_fst (X := ℍ[R, a, b]) (Y := ℍ[R, a, b]))
  have q0 := c0.comp (continuous_snd (X := ℍ[R, a, b]) (Y := ℍ[R, a, b]))
  have q1 := c1.comp (continuous_snd (X := ℍ[R, a, b]) (Y := ℍ[R, a, b]))
  have q2 := c2.comp (continuous_snd (X := ℍ[R, a, b]) (Y := ℍ[R, a, b]))
  have q3 := c3.comp (continuous_snd (X := ℍ[R, a, b]) (Y := ℍ[R, a, b]))
  have hadd : ContinuousAdd ℍ[R, a, b] := ⟨continuous_of_coords
    (by simp only [QuaternionAlgebra.re_add]; exact p0.add q0) (by simp only [QuaternionAlgebra.imI_add]; exact p1.add q1) (by simp only [QuaternionAlgebra.imJ_add]; exact p2.add q2) (by simp only [QuaternionAlgebra.imK_add]; exact p3.add q3)⟩
  have hmul : ContinuousMul ℍ[R, a, b] := ⟨continuous_of_coords
    (by simp only [QuaternionAlgebra.re_mul]; fun_prop)
    (by simp only [QuaternionAlgebra.imI_mul]; fun_prop)
    (by simp only [QuaternionAlgebra.imJ_mul]; fun_prop)
    (by simp only [QuaternionAlgebra.imK_mul]; fun_prop)⟩
  have hneg : ContinuousNeg ℍ[R, a, b] := ⟨continuous_of_coords
    (by simp only [QuaternionAlgebra.re_neg]; exact c0.neg) (by simp only [QuaternionAlgebra.imI_neg]; exact c1.neg) (by simp only [QuaternionAlgebra.imJ_neg]; exact c2.neg) (by simp only [QuaternionAlgebra.imK_neg]; exact c3.neg)⟩
  exact {}

end GlobalTheory.QuatTop

open GlobalTheory.QuatTop in
theorem GlobalTheory.quaternion_isTopologicalRing_nrm_re_t2 : ∀ (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] (a b : R), IsTopologicalRing ℍ[R, a, b] ∧ Continuous (nrm : ℍ[R, a, b] → R) ∧ Continuous (fun x : ℍ[R, a, b] => x.re) ∧ (T2Space R → T2Space ℍ[R, a, b]) := by
  intro R _ _ _ a b
  have c0 := (continuous_coord_re (R := R) (a := a) (b := b))
  have c1 := (continuous_coord_imI (R := R) (a := a) (b := b))
  have c2 := (continuous_coord_imJ (R := R) (a := a) (b := b))
  have c3 := (continuous_coord_imK (R := R) (a := a) (b := b))
  refine ⟨isTopologicalRing, ?_, c0, fun _ => ?_⟩
  · unfold nrm; fun_prop
  · have hinj : Function.Injective (coords : ℍ[R, a, b] → Fin 4 → R) := by
      intro x y h
      have e0 := congrFun h 0
      have e1 := congrFun h 1
      have e2 := congrFun h 2
      have e3 := congrFun h 3
      simp [coords] at e0 e1 e2 e3
      ext <;> assumption
    exact (Topology.IsEmbedding.mk ⟨rfl⟩ hinj).t2Space
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke

namespace GlobalTheory.UPel.HT.Hecke

theorem harrisTaylor_heckeMap_comp_forgetLevel_general {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R}
    (g g' : D.La →ₗ[D.O] D.La) (c c' k N : ℕ) (hk : k.Coprime p) (hN3 : 3 ≤ N) (hNp : N.Coprime p)
    (hgg' : ∀ x, g (g' x) = k • x) (hg'g : ∀ x, g' (g x) = k • x) (hcc : c * c' = k ^ 2)
    (hc : (N * k * k).Coprime p)
    {S S₁ S₂ : Scheme.{0}} (s : S ⟶ Sp R) (s₁ : S₁ ⟶ Sp R) (s₂ : S₂ ⟶ Sp R)
    (u : Obj b N s) (u₁ : Obj b (N * k) s₁) (u₂ : Obj b (N * k * k) s₂) (π : S₁ ⟶ S) (π₁ : S₂ ⟶ S₁)
    (h₁ : π₁ ≫ s₁ = s₂)
    (o₂ : Obj b N s₁) (ψ₂ : u₁.A ⟶ o₂.A) (hH₂ : IsHecke g c k N u₁ o₂ ψ₂) (m₂ : ObjMap o₂ u π)
    (o₁ : Obj b (N * k) s₂) (ψ₁ : u₂.A ⟶ o₁.A) (hH₁ : IsHecke g' c' k (N * k) u₂ o₁ ψ₁)
    (m₁ : ObjMap o₁ u₁ π₁) :
    Nonempty (ObjMap (u₂.forget N ⟨k * k, by ring⟩ hc) u (π₁ ≫ π)) := by
  subst h₁
  obtain ⟨o₂', ⟨m⟩⟩ := GlobalTheory.HTPull.exists_objMap_pull p D R b N S₁ S₂ s₁ π₁ o₂
  obtain ⟨ψ', hψ'⟩ := GlobalTheory.T.isHeckeTranslate_harrisTaylor_pullback_base p D R b g c k N hk hN3 hNp S₁ S₂ s₁ π₁ u₁ o₂ ψ₂ o₁ o₂' hH₂ m₁ m
  obtain ⟨n⟩ := GlobalTheory.T.harrisTaylor_inverse_heckeTranslates_forget_level p D R b g g' c c' k N hk hN3 hNp hgg' hg'g hcc hc S₂ (π₁ ≫ s₁) u₂ o₁ o₂'
    ψ₁ ψ' hH₁ hψ'
  obtain ⟨n₁⟩ := GlobalTheory.UPel.HT.objMap_comp p D R b N _ _ _ _ _ _ _ _ _ _ _ n m
  obtain ⟨n₂⟩ := GlobalTheory.UPel.HT.objMap_comp p D R b N _ _ _ _ _ _ _ _ _ _ _ n₁ m₂
  rw [Category.id_comp] at n₂
  exact ⟨n₂⟩

theorem heckeMap_comp_forget : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (g g' : D.La →ₗ[D.O] D.La) (c c' k N : ℕ), k.Coprime p → 3 ≤ N → N.Coprime p → (∀ x, g (g' x) = k • x) → (∀ x, g' (g x) = k • x) → c * c' = k ^ 2 → ∀ (hc : (N * k * k).Coprime p) (F : RepFam b N) (F₁ : RepFam b (N * k)) (F₂ : RepFam b (N * k * k)) (π : F₁.X ⟶ F.X) (π₁ : F₂.X ⟶ F₁.X), IsHeckeMap g c k N F F₁ π → IsHeckeMap g' c' k (N * k) F₁ F₂ π₁ → Nonempty (ObjMap (F₂.univ.forget N ⟨k * k, by ring⟩ hc) F.univ (π₁ ≫ π)) := by
  intro p _ D R _ b g g' c c' k N hk hN3 hNp hgg' hg'g hcc hc F F₁ F₂ π π₁ hπ hπ₁
  obtain ⟨-, o₂, ψ₂, hH₂, ⟨m₂⟩⟩ := hπ
  obtain ⟨h₁, o₁, ψ₁, hH₁, ⟨m₁⟩⟩ := hπ₁
  exact harrisTaylor_heckeMap_comp_forgetLevel_general g g' c c' k N hk hN3 hNp hgg' hg'g hcc hc F.s F₁.s F₂.s F.univ F₁.univ F₂.univ π π₁ h₁
    o₂ ψ₂ hH₂ m₂ o₁ ψ₁ hH₁ m₁

end GlobalTheory.UPel.HT.Hecke
end

section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

theorem _root_.GlobalTheory.T.dieudonneTheory_V_eq_verschiebung_injective :
    ∀ (p : ℕ) [Fact p.Prime] (T : GlobalTheory.Dieu.Theory p)
      (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k),
      Function.Injective (T.F G) ∧ Function.Injective (T.V G) ∧
      (∀ m, T.smap (frobProj (p_eq_zero p k) G) (T.V G m) =
        T.map (verschiebung (p_eq_zero p k) G) m) ∧
      (∀ (H : PDivGroup p k) (φ : T.M H →ₗ[WittVector p k] T.M G),
        (∀ m, φ (T.F H m) = T.F G (φ m)) → ∀ m, φ (T.V H m) = T.V G (φ m)) ∧
      ∀ (H : PDivGroup p k) (f : G ⟶ H) (m : T.M H),
        T.map f (T.V H m) = T.V G (T.map f m) :=
  @GlobalTheory.Dieu.theory_V_verschiebung
end

section

open NumberField GlobalTheory.CuspRep GlobalTheory.HCF GlobalTheory.CuspQuot MeasureTheory

noncomputable section

namespace GlobalTheory.HCF.FormsSub

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem isAutForm_zero : IsAutForm (0 : Sm E a) := by
  constructor
  · intro γ g
    rfl
  · have : {k | finRep E a k (0 : Sm E a) = 0} = Set.univ := Set.eq_univ_of_forall fun k => map_zero _
    rw [this]; exact isOpen_univ
  · refine Submodule.finiteDimensional_of_le (S₂ := ⊥) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    simp
  · refine Submodule.finiteDimensional_of_le (S₂ := ⊥) (Submodule.span_le.2 ?_)
    rintro _ ⟨z, hz, rfl⟩
    simp
  · intro g
    exact ⟨0, 0, fun y => by simp⟩

theorem isAutForm_add {φ ψ : Sm E a} (hφ : IsAutForm φ) (hψ : IsAutForm ψ) : IsAutForm (φ + ψ) := by
  constructor
  · intro γ g
    change φ.1 _ + ψ.1 _ = φ.1 _ + ψ.1 _
    rw [hφ.left, hψ.left]
  · exact isOpen_stab_of_mem_nhds _ _ <| Filter.mem_of_superset
      ((hφ.level.inter hψ.level).mem_nhds ⟨by simp, by simp⟩) fun k hk => by
        have h1 : finRep E a k φ = φ := hk.1
        have h2 : finRep E a k ψ = ψ := hk.2
        change finRep E a k (φ + ψ) = φ + ψ
        rw [map_add (f := _), h1, h2]
  · have := hφ.kfin
    have := hψ.kfin
    refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ (Set.range fun k => cptRep E a k φ) ⊔
      Submodule.span ℂ (Set.range fun k => cptRep E a k ψ)) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    simp only [SetLike.mem_coe, map_add (f := _)]
    exact Submodule.add_mem_sup (Submodule.subset_span ⟨k, rfl⟩) (Submodule.subset_span ⟨k, rfl⟩)
  · have := hφ.zfin
    have := hψ.zfin
    refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) '' Zalg E a) ⊔
      Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z ψ) '' Zalg E a)) (Submodule.span_le.2 ?_)
    rintro _ ⟨z, hz, rfl⟩
    simp only [SetLike.mem_coe, map_add (f := _)]
    exact Submodule.add_mem_sup (Submodule.subset_span ⟨z, hz, rfl⟩) (Submodule.subset_span ⟨z, hz, rfl⟩)
  · intro g
    obtain ⟨C1, N1, h1⟩ := hφ.growth g
    obtain ⟨C2, N2, h2⟩ := hψ.growth g
    refine ⟨|C1| + |C2|, N1 + N2, fun y => ?_⟩
    have hy := one_le_height y
    have e1 : height y ^ N1 ≤ height y ^ (N1 + N2) := pow_le_pow_right₀ hy (by omega)
    have e2 : height y ^ N2 ≤ height y ^ (N1 + N2) := pow_le_pow_right₀ hy (by omega)
    have p1 : 0 ≤ height y ^ N1 := by positivity
    have p2 : 0 ≤ height y ^ N2 := by positivity
    change ‖φ.1 _ + ψ.1 _‖ ≤ _
    calc ‖φ.1 (g * infGL E a y) + ψ.1 (g * infGL E a y)‖
        ≤ ‖φ.1 (g * infGL E a y)‖ + ‖ψ.1 (g * infGL E a y)‖ := norm_add_le _ _
      _ ≤ C1 * height y ^ N1 + C2 * height y ^ N2 := add_le_add (h1 y) (h2 y)
      _ ≤ |C1| * height y ^ (N1 + N2) + |C2| * height y ^ (N1 + N2) := by
          exact add_le_add ((mul_le_mul_of_nonneg_right (le_abs_self C1) p1).trans
              (mul_le_mul_of_nonneg_left e1 (abs_nonneg _)))
            ((mul_le_mul_of_nonneg_right (le_abs_self C2) p2).trans
              (mul_le_mul_of_nonneg_left e2 (abs_nonneg _)))
      _ = _ := by ring

theorem isAutForm_smul (c : ℂ) {φ : Sm E a} (hφ : IsAutForm φ) : IsAutForm (c • φ) := by
  constructor
  · intro γ g
    change c • φ.1 _ = c • φ.1 _
    rw [hφ.left]
  · exact isOpen_stab_of_mem_nhds _ _ <| Filter.mem_of_superset
      (hφ.level.mem_nhds (by simp)) fun k hk => by
        have h1 : finRep E a k φ = φ := hk
        change finRep E a k (c • φ) = c • φ
        rw [map_smul, h1]
  · have := hφ.kfin
    refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ (Set.range fun k => cptRep E a k φ))
      (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    simp only [SetLike.mem_coe, map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  · have := hφ.zfin
    refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) '' Zalg E a))
      (Submodule.span_le.2 ?_)
    rintro _ ⟨z, hz, rfl⟩
    simp only [SetLike.mem_coe, map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨z, hz, rfl⟩)
  · intro g
    obtain ⟨C, N, h1⟩ := hφ.growth g
    refine ⟨‖c‖ * C, N, fun y => ?_⟩
    change ‖c • φ.1 _‖ ≤ _
    rw [norm_smul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (h1 y) (norm_nonneg _)

theorem foldr_lin (χ : Module.End ℂ (Sm E a) → ℂ) (c : ℂ) (φ ψ : Sm E a) (zs : List (Module.End ℂ (Sm E a))) :
    zs.foldr (fun z f => z f - χ z • f) (c • φ + ψ) =
      c • zs.foldr (fun z f => z f - χ z • f) φ + zs.foldr (fun z f => z f - χ z • f) ψ := by
  induction zs with
  | nil => rfl
  | cons z zs ih =>
    simp only [List.foldr_cons]
    rw [ih, map_add (f := _), map_smul]
    module

theorem foldr_zero (χ : Module.End ℂ (Sm E a) → ℂ) (zs : List (Module.End ℂ (Sm E a))) :
    zs.foldr (fun z f => z f - χ z • f) (0 : Sm E a) = 0 := by
  induction zs with
  | nil => rfl
  | cons z zs ih => simp only [List.foldr_cons, ih, map_zero, smul_zero, sub_zero]

end GlobalTheory.HCF.FormsSub


open GlobalTheory.HCF.FormsSub in
theorem GlobalTheory.HCF.formsGL_single_span : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (L : Subgroup (GL (Fin a) (Af E))) (W : Submodule ℂ (Kinf E a → ℂ)) (χ : Module.End ℂ (Sm E a) → ℂ) (N : ℕ),
    ∀ φ ∈ Submodule.span ℂ (formsGL E a L W {χ} N), φ ∈ formsGL E a L W {χ} N := by
  intro E _ _ _ a L W χ N
  let S : Submodule ℂ (Sm E a) :=
    { carrier := formsGL E a L W {χ} N
      zero_mem' := by
        refine ⟨isAutForm_zero, fun k _ => map_zero _, fun g => ?_, χ, rfl, fun zs _ _ => foldr_zero χ zs⟩
        have : (fun k : Kinf E a => (cptRep E a k (0 : Sm E a)).1 g) = 0 := by
          funext k; simp
        rw [this]; exact W.zero_mem
      add_mem' := by
        rintro φ ψ ⟨a1, b1, c1, χ1, e1, d1⟩ ⟨a2, b2, c2, χ2, e2, d2⟩
        rw [Set.mem_singleton_iff] at e1 e2
        rw [e1] at d1
        rw [e2] at d2
        refine ⟨isAutForm_add a1 a2, fun k hk => by rw [map_add (f := _), b1 k hk, b2 k hk], fun g => ?_, χ, rfl,
          fun zs hl hz => ?_⟩
        · have : (fun k : Kinf E a => (cptRep E a k (φ + ψ)).1 g) =
              (fun k : Kinf E a => (cptRep E a k φ).1 g) + (fun k : Kinf E a => (cptRep E a k ψ).1 g) := by
            funext k; simp
          rw [this]; exact W.add_mem (c1 g) (c2 g)
        · have := foldr_lin χ 1 φ ψ zs
          rw [one_smul, one_smul] at this
          rw [this, d1 zs hl hz, d2 zs hl hz, add_zero]
      smul_mem' := by
        rintro c φ ⟨a1, b1, c1, χ1, e1, d1⟩
        rw [Set.mem_singleton_iff] at e1
        rw [e1] at d1
        refine ⟨isAutForm_smul c a1, fun k hk => by rw [map_smul, b1 k hk], fun g => ?_, χ, rfl,
          fun zs hl hz => ?_⟩
        · have : (fun k : Kinf E a => (cptRep E a k (c • φ)).1 g) = c • (fun k : Kinf E a => (cptRep E a k φ).1 g) := by
            funext k; simp
          rw [this]; exact W.smul_mem c (c1 g)
        · have := foldr_lin χ c φ 0 zs
          rw [add_zero, foldr_zero, add_zero] at this
          rw [this, d1 zs hl hz, smul_zero] }
  intro φ hφ
  exact (Submodule.span_le (p := S)).2 le_rfl hφ
end
end

section

open NumberField IsDedekindDomain GlobalTheory.CuspRep Matrix

namespace GlobalTheory.JSW

theorem continuous_whit_infGL : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (φ : Sm E a),
    IsAutForm φ → ∀ g h : GA E a,
      Continuous (fun y : GL (Fin a) (Cinf E) => GlobalTheory.JSW.whit φ.1 (g * infGL E a y * h)) := by
  intro E _ _ _ a φ hφ g h
  have hc : Continuous φ.1 := hφ.continuous
  have hW : Continuous (GlobalTheory.JSW.whit φ.1) := by
    have : GlobalTheory.JSW.whit φ.1 = GroundTheory.Automorphic.FourierWhittaker.partialCoeff φ.1 0 := by
      funext x
      exact GroundTheory.Automorphic.FourierWhittaker.whittaker_eq_partialCoeff_zero hc x
    rw [this]
    exact GroundTheory.Automorphic.FourierWhittaker.continuous_partialCoeff hc 0
  exact hW.comp ((continuous_const.mul GlobalTheory.ConstTermSmooth.continuous_infGL).mul continuous_const)

end GlobalTheory.JSW
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc


theorem _root_.GlobalTheory.T.exists_lineBundle_pow_section_vanishing_degree_pos : ∀ (k : Type) [Field k] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)], IsCurve k C → ∀ L : LB C, L.IsLB → 0 < interNum k (GlobalTheory.structureModule C) ![L] → ∃ (m : ℕ) (σ : (lbPow L m).Sec) (c : C), 0 < m ∧ σ ≠ 0 ∧ c ∉ Out.nonzeroLocus σ := by
  first | exact @GlobalTheory.Nef.exists_sec_lbPow_vanishing_of_degree_pos | exact GlobalTheory.Nef.exists_sec_lbPow_vanishing_of_degree_pos | (intros; apply GlobalTheory.Nef.exists_sec_lbPow_vanishing_of_degree_pos <;> assumption)
end

section

theorem GlobalTheory.T.baseChangePull_sum_mul_pointValue_eq :
    type_of% (@GlobalTheory.PtExt.bcPull_sumMul_fv) :=
  @GlobalTheory.PtExt.bcPull_sumMul_fv
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.cechLineBundle_pull_trivial_of_pointwiseGenerator : ∀ (R : Type) [CommRing R] (X Y : Over (Sp R)) (L : LB X.left), L.IsLB → ∀ (q : Y ⟶ X) (t : ∀ (E : Type) [CommRing E] [Algebra R E], Pt Y E → L.ι → E), IsPtGen L q t → GlobalTheory.AbLaw.Triv (L.pull q.left) := by
  first | exact @GlobalTheory.PtExt.triv_pull_of_isPtGen | exact GlobalTheory.PtExt.triv_pull_of_isPtGen | (intros; apply GlobalTheory.PtExt.triv_pull_of_isPtGen <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc


theorem _root_.GlobalTheory.T.exists_bounded_denominator_along_valuationPath : ∀ (k E : Type) [Field k] [Field E] [Algebra k E] (p : Place k E) (u : E) (Y : Scheme.{0}) (ζ : Sp (PowerSeries p.O) ⟶ Y) (U : Y.Opens) (h : ⊤ ≤ (spMap (sc p u) ≫ ζ) ⁻¹ᵁ U) (f : Γ(Y, U)), ∃ e ψ : PowerSeries p.O, PowerSeries.constantCoeff e ≠ 0 ∧ (⊤ ≤ ζ ⁻¹ᵁ U → e = 1) ∧ sc p u e * evAt (spMap (sc p u) ≫ ζ) h f = sc p u ψ := by
  first | exact @GlobalTheory.Nef.den_along_path | exact GlobalTheory.Nef.den_along_path | (intros; apply GlobalTheory.Nef.den_along_path <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc


theorem _root_.GlobalTheory.T.finite_places_centre_outside_open : ∀ (k K E : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k K] [Field E] [Algebra k E] [Algebra K E] [IsScalarTower k K E] [FiniteDimensional K E] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] (x : Sp K ⟶ C), IsGenOver k x →
  ∀ V : C.Opens, (V : Set C).Nonempty → {p : Place k E | ∃ b : Sp p.O ⟶ C, spMap p.O.subtype ≫ b = spMap (algebraMap K E) ≫ x ∧ ¬ ⊤ ≤ b ⁻¹ᵁ V}.Finite := by
  first | exact @GlobalTheory.Nef.finite_centre_not_mem | exact GlobalTheory.Nef.finite_centre_not_mem | (intros; apply GlobalTheory.Nef.finite_centre_not_mem <;> assumption)
end
