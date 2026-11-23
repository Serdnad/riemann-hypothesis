module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ValAtLem
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle710
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle012
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
import ReciprocityTheory.L2DbarEstimates.LeviForms.Bundle005
import ReciprocityTheory.L2DbarEstimates.LeviForms.OfRealNormSqSumMul
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle008
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

noncomputable section

namespace GlobalTheory.MBLow.Cl.SymFrame
open ReciprocityTheory.ChartRestriction.G.TB.ValAt ReciprocityTheory.ChartRestriction.G.PullbackSections

theorem const_of_periodic {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ} (hp : (τ.map Complex.im).PosDef)
    {f : (Fin g → ℂ) → ℂ} (hf : Differentiable ℂ f) (hper : ∀ z M N, f (z + perV τ M N) = f z) (z w : Fin g → ℂ) :
    f z = f w := by
  let P : (Fin g → ℤ) × (Fin g → ℤ) →+ (Fin g → ℂ) := AddMonoidHom.mk' (fun a => perV τ a.1 a.2) fun a b => by
    have e : ∀ M N : Fin g → ℤ, cv (M + N) = cv M + cv N := fun M N => by ext i; simp [cv]
    simp only [perV, Prod.fst_add, Prod.snd_add, e, Matrix.mulVec_add]
    abel
  refine periodic_const_range P (eq_top_iff.2 fun v _ => ?_) f hf (fun z a => hper z a.1 a.2) z w
  obtain ⟨y, hy⟩ := Matrix.mulVec_surjective_iff_isUnit.2 hp.isUnit fun i => (v i).im
  let x : Fin g → ℝ := fun i => (v i).re - (τ.map Complex.re *ᵥ y) i
  have e : v = ∑ i, x i • P (Pi.single i 1, 0) + ∑ i, y i • P (0, Pi.single i 1) := by
    have c0 : cv (0 : Fin g → ℤ) = 0 := by ext i; simp [cv]
    have c1 : ∀ i : Fin g, cv (Pi.single i 1 : Fin g → ℤ) = Pi.single i 1 := fun i => by
      ext k; by_cases h : k = i <;> simp [cv, h, Pi.single_apply]
    ext k
    have hk := congrFun hy k
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply] at hk
    simp only [P, AddMonoidHom.mk'_apply, perV, c0, c1, Matrix.mulVec_zero, add_zero, zero_add, Matrix.mulVec_single_one,
      Pi.add_apply, Finset.sum_apply, Pi.smul_apply, Pi.single_apply]
    apply Complex.ext
    · simp [x, Matrix.mulVec, dotProduct, mul_comm]
    · simp [← hk, mul_comm]
  rw [e]
  exact Submodule.add_mem _ (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩))
    (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩))

theorem autV_mul_autV {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) {a b : Fin g → ℂ} (ha : Half a) (hb : Half b)
    (M N : Fin g → ℤ) (z : Fin g → ℂ) : autV τ a b M N z * autV τ a b M N (-(z + perV τ M N)) = 1 := by
  have h : ∀ {c : Fin g → ℂ}, Half c → ∀ M : Fin g → ℤ, ∃ n : ℤ, 2 * (c ⬝ᵥ cv M) = n := fun {c} hc M => by
    classical
    refine ⟨∑ i, if c i = 0 then 0 else M i, ?_⟩
    rw [dotProduct, Finset.mul_sum, Int.cast_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rcases hc i with e | e <;> simp [e, cv]
  obtain ⟨m, hm⟩ := h ha M
  obtain ⟨n, hn⟩ := h hb N
  have hk : cv N ⬝ᵥ cv M = ((N ⬝ᵥ M : ℤ) : ℂ) := by simp [dotProduct, cv]
  rw [autV, autV, ← Complex.exp_add, Complex.exp_eq_one_iff]
  refine ⟨m - n + N ⬝ᵥ M, ?_⟩
  rw [dotProduct_neg, dotProduct_add, perV, dotProduct_add, hk]
  push_cast
  rw [← hm, ← hn]
  ring

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} [Algebra (FractionRing R) ℂ] {N : NumD ℂ} {g : ℕ}
  {ν : NumOf D ℂ N} {d : AB N.toNumB g}

theorem hol_base (G : Geo ν d) (U : D.P.A.left.Opens) (f : Γ(D.P.A.left, U)ˣ) :
    IsOpen {z | ⊤ ≤ (ν.eA (d.ex z)).left ⁻¹ᵁ U} ∧
      DifferentiableOn ℂ (fun z => valF (ν.eA (d.ex z)).left U f.val) {z | ⊤ ≤ (ν.eA (d.ex z)).left ⁻¹ᵁ U} := by
  have e : ∀ z, ptB ν d z ≫ (snd (TF (R := R) ℂ) D.P.A).left = (ν.eA (d.ex z)).left := fun z => by
    rw [ptB, ← Over.comp_left, lift_snd]
  have h := G.hol ((snd (TF (R := R) ℂ) D.P.A).left ⁻¹ᵁ U) (pullU _ U f).val
  simp only [← e]
  refine ⟨h.1, h.2.congr fun z _ => ?_⟩
  exact (vtf_val_pullU (ptB ν d z) _ U f).symm

theorem differentiable_gen (G : Geo ν d) (hr : ν.rg ≠ 0) {K : Type} [Fintype K] {φ : K → (D.P.A.left ⟶ D.P.A.left)}
    {ε : K → ℤ} (t : LB.Gen (LB.LinComb D.P.L φ ε)) (ht : t.IsGen) (w : K → (Fin g → ℂ) → (Fin g → ℂ))
    (hw : ∀ k, Differentiable ℂ (w k)) (hφ : ∀ k z, (ν.eA (d.ex z)).left ≫ φ k = (ν.eA (d.ex (w k z))).left) :
    Differentiable ℂ fun z => vF t (ν.eA (d.ex z)).left ν.J / ∏ k, ((d.fr (w k z) : ℂ) * ν.rg) ^ ε k := by
  intro z₀
  let j : K → D.P.L.ι := fun k => ν.J ((ν.eA (d.ex z₀)).left ≫ φ k)
  obtain ⟨hS, hv⟩ := hol_base G (LB.wchart D.P.L φ j) (t.s j)
  have hJ : ∀ z, ⊤ ≤ (ν.eA (d.ex z)).left ⁻¹ᵁ LB.wchart D.P.L φ fun k => ν.J ((ν.eA (d.ex z)).left ≫ φ k) :=
    fun z q _ => Set.mem_iInter.2 fun k => ν.good ((ν.eA (d.ex z)).left ≫ φ k) (x := q) trivial
  have hk : ∀ z, ⊤ ≤ (ν.eA (d.ex z)).left ⁻¹ᵁ LB.wchart D.P.L φ j → ∀ k,
      ⊤ ≤ (ν.eA (d.ex (w k z))).left ⁻¹ᵁ D.P.L.U (j k) := fun z hz k q _ => by
    rw [← hφ]
    exact Set.mem_iInter.1 (hz (x := q) trivial) k
  have hfr : ∀ z, ⊤ ≤ (ν.eA (d.ex z)).left ⁻¹ᵁ LB.wchart D.P.L φ j → ∀ k, (d.fr (w k z) : ℂ) * ν.rg =
      valF ((ν.eA (d.ex z)).left ≫ φ k) _ (D.P.L.g (ν.J ((ν.eA (d.ex z)).left ≫ φ k)) (j k)).val * G.frG (j k) (w k z) :=
    fun z hz k => by
      rw [hφ, G.fr_eq]
      exact G.fr_compat _ _ _ fun q _ => ⟨ν.good _ (x := q) trivial, hk z hz k (x := q) trivial⟩
  have hne : ∀ k z, (d.fr (w k z) : ℂ) * ν.rg ≠ 0 := fun k z => mul_ne_zero (Units.ne_zero _) hr
  have hev : (fun z => vF t (ν.eA (d.ex z)).left ν.J / ∏ k, ((d.fr (w k z) : ℂ) * ν.rg) ^ ε k) =ᶠ[nhds z₀]
      fun z => valF (ν.eA (d.ex z)).left (LB.wchart D.P.L φ j) (t.s j).val / ∏ k, G.frG (j k) (w k z) ^ ε k := by
    filter_upwards [hS.mem_nhds (hJ z₀)] with z hz
    have e : vF t (ν.eA (d.ex z)).left ν.J = (∏ k, valF ((ν.eA (d.ex z)).left ≫ φ k) _
        (D.P.L.g (ν.J ((ν.eA (d.ex z)).left ≫ φ k)) (j k)).val ^ ε k) *
        valF (ν.eA (d.ex z)).left (LB.wchart D.P.L φ j) (t.s j).val :=
      vtf_isGen_val D.P.L φ ε t ht _ _ j fun q _ => ⟨hJ z (x := q) trivial, hz (x := q) trivial⟩
    rw [e]
    simp only [hfr z hz, mul_zpow, Finset.prod_mul_distrib]
    refine mul_div_mul_left _ _ (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ ?_)
    exact left_ne_zero_of_mul (hfr z hz k ▸ hne k z)
  refine DifferentiableAt.congr_of_eventuallyEq ?_ hev
  have h0 : ∀ k, G.frG (j k) (w k z₀) ≠ 0 := fun k => right_ne_zero_of_mul (hfr z₀ (hJ z₀) k ▸ hne k z₀)
  have h1 : ∀ k, DifferentiableAt ℂ (fun z => G.frG (j k) (w k z)) z₀ := fun k =>
    ((G.fr_hol (j k)).differentiableAt ((hol_base G _ 1).1.mem_nhds (hk z₀ (hJ z₀) k))).comp z₀ (hw k z₀)
  have h2 : DifferentiableAt ℂ (fun z => ∏ k, G.frG (j k) (w k z) ^ ε k) z₀ :=
    by
      have hp : ∀ s : Finset K, DifferentiableAt ℂ (fun z => ∏ k ∈ s, G.frG (j k) (w k z) ^ ε k) z₀ := fun s => by
        classical
        induction s using Finset.induction_on with
        | empty => simp
        | insert a s ha ih =>
          simp only [Finset.prod_insert ha]
          exact ((h1 a).zpow (Or.inl (h0 a))).mul ih
      exact hp _
  simp only [div_eq_mul_inv]
  exact (hv.differentiableAt (hS.mem_nhds (hJ z₀))).mul
    (h2.inv (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (h0 k)))

theorem rg_ne (ν : NumOf D ℂ N) : ν.rg ≠ 0 := by
  unfold NumOf.rg vF valF
  split_ifs with h
  · exact (((Units.isUnit _).map _).map _).ne_zero
  · exact (h fun q _ => Set.mem_iInter.2 fun _ => ν.good ((TF (R := R) ℂ).hom ≫ eSec D.P.A) (x := q) trivial).elim

end GlobalTheory.MBLow.Cl.SymFrame

namespace GlobalTheory.MBLow.Cl
open SymFrame

theorem sym_of_geo : AllC fun {R} _ _ {D} _ {N} ν => ∀ (g : ℕ) (d : AB N.toNumB g), Nonempty (Geo ν d) → d.Sym := by
  rintro R _ _ _ _ D - - _ N ν g d ⟨G⟩
  have hr := rg_ne ν
  have h0 : d.ex 0 = 1 := by simpa using d.ex_add 0 0
  have hneg : ∀ z, d.ex (-z) = (d.ex z)⁻¹ := fun z =>
    eq_inv_of_mul_eq_one_left (by rw [← d.ex_add, neg_add_cancel, h0])
  have hd := differentiable_gen G hr D.sym D.sym_gen ![fun z => -z, fun z => z]
    (fun k => by fin_cases k <;> simp <;> fun_prop) (fun k z => by
      fin_cases k
      · change _ ≫ (ι[D.P.A]).left = (ν.eA (d.ex (-z))).left
        rw [hneg, map_inv, Hom.inv_def, Over.comp_left]
      · exact Category.comp_id _)
  have hF : Differentiable ℂ fun z => (N.σ (d.ex z) : ℂ) * d.fr z / d.fr (-z) := by
    convert hd using 2 with z
    rw [ν.σ_eq, Fin.prod_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, zpow_one, _root_.zpow_neg]
    have := (d.fr z).ne_zero
    have := (d.fr (-z)).ne_zero
    field_simp
  intro x
  have hc := const_of_periodic d.pos hF (fun z M M' => by
    have h1 := d.fr_per M M' z
    have h2 := d.fr_per M M' (-(z + perV d.τ M M'))
    have h3 := autV_mul_autV d.τ d.ha d.hb M M' z
    rw [show -(z + perV d.τ M M') + perV d.τ M M' = -z by abel] at h2
    rw [d.ex_add, (d.ker _).2 ⟨M, M', rfl⟩, _root_.mul_one, div_eq_div_iff (Units.ne_zero _) (Units.ne_zero _), h1, h2]
    linear_combination (-(N.σ (d.ex z) : ℂ) * d.fr (z + perV d.τ M M') * d.fr (-z)) * h3) x 0
  rw [h0, N.σ_one, neg_zero, d.fr_zero, div_eq_iff (Units.ne_zero _)] at hc
  ext
  simpa using hc

end GlobalTheory.MBLow.Cl

end
end

section

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier

namespace GlobalTheory.HtSelfInter

variable {k : Type} [CommRing k] {X Z : Scheme.{0}} {p : X ⟶ Sp k} {D : ℕ}

theorem isClosed_of_ne_genericPoint [IsIntegral Z] (hd : topologicalKrullDim Z = 1) {z : Z}
    (hz : z ≠ genericPoint Z) : IsClosed ({z} : Set Z) := by
  rcases Order.krullDim_le_one_iff.1 (show Order.krullDim (IrreducibleCloseds Z) ≤ 1 from hd.le)
    ⟨closure {z}, isIrreducible_singleton.closure, isClosed_closure⟩ with h | h
  · refine isClosed_of_closure_subset fun w hw => ?_
    have h₁ : (⟨closure {w}, isIrreducible_singleton.closure, isClosed_closure⟩ : IrreducibleCloseds Z) ≤
        ⟨closure {z}, isIrreducible_singleton.closure, isClosed_closure⟩ :=
      closure_minimal (Set.singleton_subset_iff.2 hw) isClosed_closure
    have h₂ : z ∈ closure {w} := h h₁ (subset_closure rfl)
    exact ((specializes_iff_mem_closure.2 h₂).antisymm (specializes_iff_mem_closure.2 hw)).eq
  · exact absurd (IsGenericPoint.eq (Set.eq_univ_of_univ_subset (@h
      ⟨Set.univ, IrreducibleSpace.isIrreducible_univ Z, isClosed_univ⟩ (Set.subset_univ _)))
      (genericPoint_spec Z)) hz

theorem charZero_residueField_genericPoint [IsIntegral Z] (hc : CharZero Γ(Z, ⊤)) :
    CharZero (Z.residueField (genericPoint Z)) := by
  have h₁ : CharZero Z.functionField :=
    charZero_of_injective_ringHom (fnOf_injective (⊤ : Z.Opens) (Opens.mem_top _))
  let f : Z.functionField →+* Z.residueField (genericPoint Z) := (Z.residue _).hom
  exact charZero_of_injective_ringHom f.injective

theorem eq_genericPoint [IsIntegral Z] {q : Z ⟶ Sp k} (hZ : IsArithVar q 0) {z : Z}
    (hz : CharZero (Z.residueField z)) : z = genericPoint Z := by
  by_contra h
  have := hZ.finite_residueField (isClosed_of_ne_genericPoint hZ.dim_eq h)
  exact not_finite (Z.residueField z)

theorem finite_ringHom [IsIntegral Z] {q : Z ⟶ Sp k} (hZ : IsArithVar q 0) :
    Finite (Z.residueField (genericPoint Z) →+* ℂ) := by
  have hc := charZero_residueField_genericPoint hZ.charZero
  obtain ⟨N, j, _, hj⟩ := hZ.isProjOver
  have := isProper_str k N
  have : IsProper q := hj ▸ inferInstance
  have : IsFinite (spMap (Int.castRingHom k)) :=
    (IsFinite.SpecMap_iff _).2 (RingHom.finite_algebraMap.2 hZ.finite)
  let t := q ≫ spMap (Int.castRingHom k)
  have h₁ : t.QuasiFiniteAt (genericPoint Z) := by
    rw [Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber]
    have h0 : CharZero ((Sp ℤ).residueField (t (genericPoint Z))) :=
      (t.residueFieldMap (genericPoint Z)).hom.charZero
    have hs (w : t.fiber (t (genericPoint Z))) : t.fiberι _ w = genericPoint Z := by
      have e : t (t.fiberι _ w) = t (genericPoint Z) :=
        (t.range_fiberι (t (genericPoint Z))).le ⟨w, rfl⟩
      rw [← e] at h0
      exact eq_genericPoint hZ (charZero_of_injective_ringHom (t.residueFieldMap _).hom.injective)
    have : Subsingleton (t.fiber (t (genericPoint Z))) := ⟨fun a b =>
      (t.fiberι _).isEmbedding.injective ((hs a).trans (hs b).symm)⟩
    exact isOpen_discrete _
  have h₂ := Scheme.Hom.quasiFiniteAt_iff.1 h₁
  have h₃ : LocallyQuasiFinite (Z.fromSpecResidueField (genericPoint Z) ≫ t) := by
    rw [Scheme.fromSpecResidueField, Category.assoc]
    infer_instance
  rw [← Spec.map_preimage (Z.fromSpecResidueField (genericPoint Z) ≫ t),
    HasRingHomProperty.Spec_iff (P := @LocallyQuasiFinite),
    RingHom.ext_int (Spec.preimage (Z.fromSpecResidueField (genericPoint Z) ≫ t)).hom
      ((algebraMap ℚ (Z.residueField (genericPoint Z))).comp (Int.castRingHom ℚ))] at h₃
  have h₄ := RingHom.quasiFinite_algebraMap.1 (RingHom.QuasiFinite.of_comp h₃)
  have : Module.Finite ℚ (Z.residueField (genericPoint Z)) := .of_quasiFinite
  exact .of_equiv _ (RingHom.equivRatAlgHom _ ℂ).symm

theorem nonempty_equiv [IsIntegral Z] {q : Z ⟶ Sp k} (hZ : IsArithVar q 0) :
    Nonempty ((Σ σ : k →+* ℂ, CxPts q σ) ≃ (Z.residueField (genericPoint Z) →+* ℂ)) := by
  have h₁ : Function.Bijective fun y : (Σ σ : k →+* ℂ, CxPts q σ) => y.2.1 := by
    refine ⟨?_, fun y => ⟨⟨(Spec.preimage (y ≫ q)).hom, y, (Spec.map_preimage _).symm⟩, rfl⟩⟩
    rintro ⟨σ, y, hy⟩ ⟨σ', y', hy'⟩ (rfl : y = y')
    obtain rfl : σ = σ' := congrArg CommRingCat.Hom.hom (Spec.map_injective (hy.symm.trans hy'))
    rfl
  have h₂ : Function.Bijective fun φ : Z.residueField (genericPoint Z) →+* ℂ =>
      (Spec.map (CommRingCat.ofHom φ) ≫ Z.fromSpecResidueField (genericPoint Z) : Sp ℂ ⟶ Z) := by
    refine ⟨fun φ ψ h => congrArg CommRingCat.Hom.hom (Spec.map_injective ((cancel_mono _).1 h)),
      fun y => ?_⟩
    obtain ⟨⟨z, φ⟩, rfl⟩ := (Scheme.SpecToEquivOfField ℂ Z).symm.surjective y
    obtain rfl := eq_genericPoint hZ (z := z) φ.hom.charZero
    exact ⟨φ.hom, rfl⟩
  exact ⟨(Equiv.ofBijective _ h₁).trans (Equiv.ofBijective _ h₂).symm⟩

theorem finsum_add_const [IsIntegral Z] {q : Z ⟶ Sp k} (hZ : IsArithVar q 0)
    (f : ∀ σ : k →+* ℂ, CxPts q σ → ℝ) (c : ℝ) :
    ∑ᶠ σ, ∑ᶠ y, (f σ y + c) =
      (∑ᶠ σ, ∑ᶠ y, f σ y) + c * Nat.card (Z.residueField (genericPoint Z) →+* ℂ) := by
  have := finite_ringHom hZ
  have := hZ.finite_emb
  obtain ⟨e⟩ := nonempty_equiv hZ
  have : Finite (Σ σ : k →+* ℂ, CxPts q σ) := .of_equiv _ e.symm
  have (σ : k →+* ℂ) : Finite (CxPts q σ) := .of_injective _ (sigma_mk_injective (i := σ))
  let := Fintype.ofFinite (k →+* ℂ)
  let (σ : k →+* ℂ) := Fintype.ofFinite (CxPts q σ)
  rw [← Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_sigma]
  simp only [finsum_eq_sum_of_fintype, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, Nat.cast_sum, Finset.mul_sum, mul_comm]

theorem card_ringHom_eq (i : Z ⟶ X) [IsClosedImmersion i] (z : Z) :
    Nat.card (X.residueField (i z) →+* ℂ) = Nat.card (Z.residueField z →+* ℂ) := by
  have hs : Function.Surjective (i.residueFieldMap z).hom := fun a => by
    obtain ⟨b, rfl⟩ := Z.residue_surjective z a
    obtain ⟨c, rfl⟩ := i.stalkMap_surjective z b
    exact ⟨X.residue _ c, congrArg (fun f => f.hom c) (Scheme.residue_residueFieldMap i z)⟩
  let e := RingEquiv.ofBijective _ ⟨(i.residueFieldMap z).hom.injective, hs⟩
  exact Nat.card_congr ⟨fun φ => φ.comp e.symm.toRingHom, fun φ => φ.comp e.toRingHom,
    fun φ => by ext; simp, fun φ => by ext; simp⟩

theorem curveDeg_shift (hX : IsArithVar p D) (L : HermLB p) (t : ℝ) (i : Z ⟶ X) [IsClosedImmersion i]
    [IsIntegral Z] [IsLocallyNoetherian Z] (hc : CharZero Γ(Z, ⊤)) (hd : topologicalKrullDim Z = 1)
    {r : (L.restr i).B.ι → Z.functionFieldˣ} (hr : IsRatSec (L.restr i).B r) :
    ((L.shift (fun _ => t) fun _ => rfl).restr i).curveDeg (r := r) hr =
      (L.restr i).curveDeg hr + t * Nat.card (X.residueField (i (genericPoint Z)) →+* ℂ) := by
  have hZ : IsArithVar (i ≫ p) 0 := hX.of_isClosedImmersion i hc hd
  have e (σ : k →+* ℂ) (y : CxPts (i ≫ p) σ) :
      logNorm (((L.shift (fun _ => t) fun _ => rfl).restr i).φ σ) r y =
        logNorm ((L.restr i).φ σ) r y + -t := by
    have e₁ := ((L.shift (fun _ => t) fun _ => rfl).φ σ).pull_φ i rfl
      (CxPts.pick ((L.restr i).φ σ).isLB y) y
    have e₂ := (L.φ σ).pull_φ i rfl (CxPts.pick ((L.restr i).φ σ).isLB y) y
    have e₃ := e₁.trans (congrArg (· + 2 * t) e₂.symm)
    refine (congrArg (_ - · / 2) e₃).trans ?_
    unfold logNorm
    exact (fun a b : ℝ => (by ring : a - (b + 2 * t) / 2 = a - b / 2 + -t)) _ _
  unfold HermLB.curveDeg
  simp only [e]
  rw [finsum_add_const hZ, card_ringHom_eq]
  exact (fun a b c : ℝ => (by ring : a - (b + -t * c) = a - b + t * c)) _ _ _

theorem isAlgPt_genericPoint (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z] (hc : CharZero Γ(Z, ⊤))
    (hd : topologicalKrullDim Z = 1) : IsAlgPt (i (genericPoint Z)) := by
  have := charZero_residueField_genericPoint hc
  refine ⟨(i.residueFieldMap _).hom.charZero, ?_⟩
  have h₁ := (genericPoint_spec Z).image i.continuous
  rw [Set.image_univ, i.isClosedEmbedding.isClosed_range.closure_eq] at h₁
  rw [h₁.def, ← hd]
  exact (IsHomeomorph.topologicalKrullDim_eq _
    i.isClosedEmbedding.isEmbedding.toHomeomorph.isHomeomorph).symm

theorem isNef_shift (hX : IsArithVar p D) {L : HermLB p} {e : ℝ} (hs : L.SemiPos D) (hf : NefFib L)
    (hh : ∀ x, IsAlgPt x → ∃ b, IsPtHt L x b ∧ e ≤ b) :
    (L.shift (fun _ => -e) fun _ => rfl).IsNef D := by
  refine ⟨hs.shift _ _, fun Z i _ _ κ _ _ _ hd => hf Z i κ hd, ?_⟩
  intro Z i _ _ _ hc hd
  obtain ⟨r, hr⟩ := exists_isRatSec (L.restr i).isLB
  obtain ⟨b, ⟨h, H, hb⟩, hle⟩ := hh _ (isAlgPt_genericPoint i hc hd)
  refine ⟨r, hr, ?_⟩
  rw [curveDeg_shift hX L (-e) i hc hd hr, ← H.point Z i hc hd r hr, hb, ← add_mul]
  exact mul_nonneg (by linarith) (Nat.cast_nonneg _)

end GlobalTheory.HtSelfInter
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Mix.RegLog

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}

theorem cInfAt_comp {f : CxPts p σ → ℝ} {y : CxPts p σ} (h : CInfAt f y) {G : ℝ → ℝ} {T : Set ℝ}
    (hT : IsOpen T) (hG : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G T) (hf : ∀ z, f z ∈ T) :
    CInfAt (fun z => G (f z)) y := by
  obtain ⟨W, ι, _, g, F, O, h₁, h₂, h₃, h₄, h₅⟩ := h
  have e : f y = F (fun a => ev p σ W (g a) y) := h₅.eq_of_nhds
  refine ⟨W, ι, inferInstance, g, G ∘ F, O ∩ F ⁻¹' T, h₁, h₄.continuousOn.isOpen_inter_preimage h₂ hT,
    ⟨h₃, show F _ ∈ T from e ▸ hf y⟩, hG.comp (h₄.mono inter_subset_left) fun v hv => hv.2, ?_⟩
  filter_upwards [h₅] with z hz
  simp only [Function.comp_apply, hz]

theorem cInfAt_normSq_ev {W : X.Opens} (g : Γ(X, W)) {y : CxPts p σ} (hy : y ∈ ptsIn p σ W) :
    CInfAt (fun z => ‖ev p σ W g z‖ ^ 2) y :=
  ⟨W, Unit, inferInstance, fun _ => g, fun v => ‖v ()‖ ^ 2, univ, hy, isOpen_univ, trivial,
    ((contDiff_norm_sq ℝ).comp (contDiff_apply ℝ (fun _ => ℂ) ())).contDiffOn, EventuallyEq.rfl⟩

theorem cInfAt_nsq {B : LB X} (φ : Weight p σ B) (hφ : φ.IsCInf) (s : B.Sec) (y : CxPts p σ) :
    CInfAt (φ.nsq (secVal p σ s)) y := by
  have hi := mem_pick φ.isLB y
  have h := (cInfAt_normSq_ev (s.f (pick φ.isLB y)) hi).comp₂ (hφ _ y hi)
    (G := fun x => x.1 * Real.exp (-x.2)) (contDiff_fst.mul (Real.contDiff_exp.comp contDiff_snd.neg))
  refine h.congr ?_
  filter_upwards [(isOpen_ptsIn (p := p) (σ := σ) _).mem_nhds hi] with z hz
  exact φ.nsq_eq (secVal_mem s) hz

end GlobalTheory.Mix.RegLog


open GlobalTheory.Mix.RegLog in
theorem GlobalTheory.Mix.semiPosReg_addFn_log_nsq : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (D : ℕ) (N : MLine p σ), N.φ.SemiPosReg D → ∀ (t : N.B.Sec) (δ : ℝ), 0 < δ → (∀ y, CInfAt (fun y => Real.log (N.φ.nsq (secVal p σ t) y + δ)) y) ∧ (N.φ.addFn fun y => Real.log (N.φ.nsq (secVal p σ t) y + δ)).SemiPosReg D := by
  intro k _ X p σ D N hN t δ hδ
  have hC : ∀ y, CInfAt (fun y => Real.log (N.φ.nsq (secVal p σ t) y + δ)) y := fun y =>
    cInfAt_comp ((cInfAt_nsq N.φ N.cInf t y).add (cInfAt_const δ y)) isOpen_compl_singleton
      Real.contDiffOn_log fun z => (add_pos_of_nonneg_of_pos (N.φ.nsq_nonneg _ z) hδ).ne'
  refine ⟨hC, ?_⟩
  intro i c y hy ξ
  have ho := isOpen_over c.e (isOpen_ptsIn (p := p) (σ := σ) (N.B.U i))
  have hm := mem_over c.e hy.1 hy.2
  have hf : ContDiffAt ℂ 2 (ev p σ (N.B.U i) (t.f i) ∘ c.e.symm) (c.e y) :=
    ReciprocityTheory.L2DbarEstimates.Y.contDiffAt_two_of_holo ho (c.holo _ (t.f i)) hm
  have hψ : ContDiffAt ℝ 2 (fun v => N.φ.φ i (c.e.symm v)) (c.e y) := N.cInf.contDiffAt c hy.1 hy.2
  have hψ' : ContDiffAt ℝ 2 (fun v => 1 * N.φ.φ i (c.e.symm v) + Real.log δ) (c.e y) :=
    (contDiffAt_const.mul hψ).add contDiffAt_const
  let w : Fin 2 → ReciprocityTheory.L2DbarEstimates.V D → ℝ := ![fun v => Complex.normSq ((ev p σ (N.B.U i) (t.f i) ∘ c.e.symm) v),
    fun v => Real.exp (1 * N.φ.φ i (c.e.symm v) + Real.log δ)]
  have hu : ∀ j, ContDiffAt ℝ 2 (w j) (c.e y) := by
    intro j; fin_cases j
    · exact ReciprocityTheory.L2DbarEstimates.contDiffAt_normSq_comp hf
    · exact Real.contDiff_exp.contDiffAt.comp _ hψ'
  have hl : ∀ j, ReciprocityTheory.L2DbarEstimates.LogPshAt D (w j) (c.e y) := by
    intro j; fin_cases j
    · exact ReciprocityTheory.L2DbarEstimates.logPshAt_normSq hf
    · refine ReciprocityTheory.L2DbarEstimates.logPshAt_exp hψ' fun ζ => ?_
      rw [ReciprocityTheory.L2DbarEstimates.Y.leviV_const_mul hψ 1 (Real.log δ) ζ, Complex.ofReal_one, one_mul]
      exact hN i c y hy ζ
  have hpos : 0 < ∑ j, w j (c.e y) := by
    simp only [Fin.sum_univ_two, w, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    exact add_pos_of_nonneg_of_pos (Complex.normSq_nonneg _) (Real.exp_pos _)
  have key := ReciprocityTheory.L2DbarEstimates.leviV_log_sum_nonneg hu hl hpos ξ
  have e : (fun v => (((N.φ.addFn fun y => Real.log (N.φ.nsq (secVal p σ t) y + δ)).φ i (c.e.symm v) : ℝ) : ℂ))
      =ᶠ[𝓝 (c.e y)] fun v => ((Real.log (∑ j, w j v) : ℝ) : ℂ) := by
    filter_upwards [ho.mem_nhds hm] with v hv
    have hz : c.e.symm v ∈ ptsIn p σ (N.B.U i) := hv.2
    congr 1
    simp only [Weight.addFn, N.φ.nsq_eq (secVal_mem t) hz, Fin.sum_univ_two, w, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Function.comp_apply, secVal_apply]
    set a := N.φ.φ i (c.e.symm v)
    set b := ev p σ (N.B.U i) (t.f i) (c.e.symm v)
    have h1 : ‖b‖ ^ 2 * Real.exp (-a) + δ = Real.exp (-a) * (Complex.normSq b + Real.exp (1 * a + Real.log δ)) := by
      rw [Complex.normSq_eq_norm_sq, Real.exp_add, Real.exp_log hδ, one_mul, Real.exp_neg]
      field_simp
    rw [h1, Real.log_mul (Real.exp_pos _).ne' (add_pos_of_nonneg_of_pos (Complex.normSq_nonneg _)
      (Real.exp_pos _)).ne', Real.log_exp]
    ring
  rw [ReciprocityTheory.L2DbarEstimates.leviV_congr e]
  exact key
end
end

section

open GlobalTheory.Ex

noncomputable section

namespace GlobalTheory.MBLow.Cl

def cubF {B : NumB ℂ} {g : ℕ} (d : AB B g) (x y z : Fin g → ℂ) : ℂ :=
  (B.θ (d.ex x) (d.ex y) (d.ex z) : ℂ) * d.fr (x + y) * d.fr (x + z) * d.fr (y + z) /
    (d.fr (x + y + z) * d.fr x * d.fr y * d.fr z)

end GlobalTheory.MBLow.Cl

end
end
