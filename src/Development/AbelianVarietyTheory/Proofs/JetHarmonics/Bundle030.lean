module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.LocalRing.Defs
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.EqZeroOrSingleOfDegreeLtTwo
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ConstantCoeffEv
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.FormalGroupLawCompMulNZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GaugeTrans
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.AxisPderivComp
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FormalSecondPointDerivativeSecondCoordinate
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
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.WittVector.IsPoly
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdIso
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CMField
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle025
public import Mathlib.RingTheory.LocalRing.Module
import Mathlib.Topology.Sheaves.Presheaf
import Std.Tactic.BVDecide.Normalize.Prop
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle002

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open GlobalTheory.AdicColimit

namespace GlobalTheory.FlatComplete

theorem mem_smul_top_iff_repr {O M ι : Type} [CommRing O] [AddCommGroup M] [Module O M] [Fintype ι]
    (b : Module.Basis ι O M) (J : Ideal O) (x : M) :
    x ∈ J • (⊤ : Submodule O M) ↔ ∀ i, b.repr x i ∈ J := by
  constructor
  · intro hx
    refine Submodule.smul_induction_on (p := fun y => ∀ i, b.repr y i ∈ J) hx ?_ ?_
    · intro r hr y _ i
      rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
      exact J.mul_mem_right _ hr
    · intro y z hy hz i
      rw [map_add (f := _), Finsupp.add_apply]
      exact J.add_mem (hy i) (hz i)
  · intro h
    rw [← b.sum_repr x]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (h i) Submodule.mem_top

theorem isAdicComplete_of_finite_basis {O M ι : Type} [CommRing O] [AddCommGroup M] [Module O M]
    [Fintype ι] (b : Module.Basis ι O M) (J : Ideal O) [hO : IsAdicComplete J O] :
    IsAdicComplete J M := by
  have hR : ∀ (n : ℕ) (r : O), r ∈ (J ^ n • ⊤ : Submodule O O) ↔ r ∈ J ^ n := fun n r => by
    rw [smul_eq_mul, Ideal.mul_top]
  have key : ∀ (n : ℕ) (x y : M), x ≡ y [SMOD (J ^ n • ⊤ : Submodule O M)] ↔
      ∀ i, b.repr x i ≡ b.repr y i [SMOD (J ^ n • ⊤ : Submodule O O)] := fun n x y => by
    simp only [SModEq.sub_mem, hR, mem_smul_top_iff_repr b (J ^ n), map_sub, Finsupp.sub_apply]
  rw [isAdicComplete_iff]
  refine ⟨isHausdorff_iff.2 fun x hx => ?_, isPrecomplete_iff.2 fun f hf => ?_⟩
  · apply b.repr.injective
    ext i
    rw [map_zero, Finsupp.zero_apply]
    refine IsHausdorff.haus (inferInstance : IsHausdorff J O) _ fun n => ?_
    have := (key n x 0).1 (hx n) i
    rwa [map_zero, Finsupp.zero_apply] at this
  · have hc : ∀ i, ∃ L : O, ∀ n, b.repr (f n) i ≡ L [SMOD (J ^ n • ⊤ : Submodule O O)] := fun i =>
      IsPrecomplete.prec (inferInstance : IsPrecomplete J O) fun hmn => (key _ _ _).1 (hf hmn) i
    choose L hL using hc
    refine ⟨b.equivFun.symm L, fun n => (key n _ _).2 fun i => ?_⟩
    rw [← b.equivFun_apply (b.equivFun.symm L), LinearEquiv.apply_symm_apply]
    exact hL i n

theorem isAdicComplete_of_finite_flat (O : Type) [CommRing O] [IsLocalRing O] (J : Ideal O)
    (hO : IsAdicComplete J O) (A : Type) [CommRing A] [Algebra O A] [Module.Finite O A]
    [Module.Flat O A] : IsAdicComplete (J.map (algebraMap O A)) A := by
  have : Module.Free O A := Module.free_of_flat_of_isLocalRing
  have := hO
  exact (IsAdicComplete.map_algebraMap_iff (I := J) (M := A)).2
    (isAdicComplete_of_finite_basis (Module.Free.chooseBasis O A) J)

end GlobalTheory.FlatComplete
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.SabPullCompare

variable {S S' : Scheme.{0}}

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem lbIso_cubeLB {G T : Over S} [GrpObj G] [IsCommMonObj G] {n : ℕ} (x : Fin n → (T ⟶ G))
    {L M : LB G.left} (h : LBIso L M) : LBIso (cubeLB G x L) (cubeLB G x M) := by
  obtain ⟨w, hw⟩ := h
  exact ⟨_, DVR.linCombIso_isGen w hw _ _⟩

theorem cubeLB_isLB {G T : Over S} [GrpObj G] [IsCommMonObj G] {n : ℕ} (x : Fin n → (T ⟶ G))
    {L : LB G.left} (h : L.IsLB) : (cubeLB G x L).IsLB := DVR.linComb_isLB _ h _ _

end GlobalTheory.SabPullCompare
end
end

section

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory.FourierChainCompare

section Duality

variable {A B K : Type} [AddCommGroup A] [AddCommGroup B] [Field K]

variable [Fintype A] [Fintype B]


end Duality

section Fourier

variable {A B K : Type} [AddCommGroup A] [AddCommGroup B] [Field K] [Fintype A] [Fintype B]

end Fourier

section Chain

variable {R : Type} [CommRing R] {d : ℕ}

theorem act_zero {O : Type} [CommRing O] {G : FGLaw R d} (A : OAct O G) : A.act 0 = 0 := by
  have hc := A.const 0
  have h1 : A.act 0 = G.add (A.act 0) (A.act 0) := by rw [← A.add_act, add_zero]
  have h2 : A.act 0 = comp1 (A.act 0) (A.act 0) := by rw [← A.mul_act, mul_zero]
  have h3 : dLin (A.act 0) = 0 := by
    have := GlobalTheory.FormalMulN.dLin_add G hc hc
    rw [← h1] at this
    exact left_eq_add.mp this
  have h4 : ∀ i, 2 ≤ (A.act 0 i).order := fun i =>
    GlobalTheory.FormalSeries.two_le_order_iff.mpr ⟨hc i, fun j => by
      obtain ⟨j0, j⟩ := j
      obtain rfl : j0 = 0 := Subsingleton.elim _ _
      exact congrFun (congrFun h3 i) j⟩
  have h5 : ∀ (k : ℕ) i, (k : ℕ∞) ≤ (A.act 0 i).order := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      intro i
      have := GlobalTheory.FormalSeries.le_order_subst_sub_subst
        (a := fun p : Fin 1 × Fin d => (![A.act 0] : Fin 1 → Pt R 1 d) p.1 p.2) (b := 0) (k := k)
        (fun p => GlobalTheory.GaugeAdjoint.const_one hc p.1 p.2) (by simp)
        (fun p => by simpa using ih p.2) (h4 i)
      rw [subst_zero_of_constantCoeff_zero (hc i), sub_zero] at this
      rw [congrFun h2 i]
      exact this
  funext i
  exact GlobalTheory.FormalSeries.eq_of_forall_le_order_sub fun k => by simpa using h5 k i

end Chain

end GlobalTheory.FourierChainCompare
end
end

section

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing

namespace GlobalTheory.DerivEndo

open GlobalTheory.ChartTrans

variable {k : Type} [CommRing k] {d : ℕ}

theorem dof_endo (F : Fin d → PS k 2 d) (hF : ∀ i, constantCoeff (F i) = 0)
    (hu : ∀ i, ev (n := 1) ![pt k (n := 1) d 0, 0] (F i) = (X ((0 : Fin 1), i) : PS k 1 d))
    (φ : Pt k 1 d) (hφ : GP φ)
    (hom : comp1 φ F = addOf F (comp1 φ (pt k (n := 2) d 0)) (comp1 φ (pt k (n := 2) d 1)))
    (u : Fin d → k) (g : PS k 1 d) :
    Dof F u (ev (n := 1) ![φ] g) = ev (n := 1) ![φ] (Dof F ((dLin φ).mulVec u) g) := by
  have h0 : GP (comp1 φ (pt k (n := 2) d 0)) := gp_comp1 φ _ hφ (gp_pt 0)
  have h1 : GP (comp1 φ (pt k (n := 2) d 1)) := gp_comp1 φ _ hφ (gp_pt 1)
  have hΦ := pair_points_zero_constant h0 h1
  have key : ev (n := 2) ![F] (ev (n := 1) ![φ] g) =
      ev ![comp1 φ (pt k (n := 2) d 0), comp1 φ (pt k (n := 2) d 1)] (ev (n := 2) ![F] g) := by
    rw [gt_ev_ev' _ _ (single_point_zero_constant hF) (single_point_zero_constant hφ), vec1, gt_ev_ev' _ _ hΦ (single_point_zero_constant hF), vec1]
    have : evP ![F] φ = evP ![comp1 φ (pt k (n := 2) d 0), comp1 φ (pt k (n := 2) d 1)] F := hom
    rw [this]
  rw [dof_eq _ hF hu, dof_eq F hF hu, key, ChartTrans.ev_sum _ (single_point_zero_constant hφ)]
  simp only [axis_pderiv_comp φ hφ, ChartTrans.ev_C_mul _ (single_point_zero_constant hφ)]

  simp only [Matrix.mulVec, dotProduct, map_sum,
  map_mul, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem dof_smul_dir (F : Fin d → PS k 2 d) (c : k) (u : Fin d → k) (g : PS k 1 d) :
    Dof F (c • u) g = C c * Dof F u g := by
  unfold Dof
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, Finset.sum_mul, mul_assoc]

theorem iterate_dof_C_mul (F : Fin d → PS k 2 d) (u : Fin d → k) (n : ℕ) (c : k) (g : PS k 1 d) :
    (Dof F u)^[n] (C c * g) = C c * (Dof F u)^[n] g := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, GE.dof_C_mul]

theorem dmonOf_endo (F : Fin d → PS k 2 d) (φ : Pt k 1 d) (hφ : GP φ) {ι : Type} [Fintype ι]
    (u : ι → Fin d → k) (α : ι → k)
    (h : ∀ l g, Dof F (u l) (ev (n := 1) ![φ] g) = C (α l) * ev (n := 1) ![φ] (Dof F (u l) g))
    (m : ι →₀ ℕ) (g : PS k 1 d) :
    DmonOf F u m (ev (n := 1) ![φ] g) = C (∏ l, α l ^ m l) * ev (n := 1) ![φ] (DmonOf F u m g) := by
  have hit : ∀ (l : ι) (n : ℕ) (g : PS k 1 d), (Dof F (u l))^[n] (ev (n := 1) ![φ] g) =
      C (α l ^ n) * ev (n := 1) ![φ] ((Dof F (u l))^[n] g) := by
    intro l n g
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, GE.dof_C_mul, h, pow_succ,
        map_mul, mul_assoc]
  rw [← Finset.prod_map_toList]
  unfold DmonOf
  induction (Finset.univ : Finset ι).toList with
  | nil => simp
  | cons a L ih =>
    rw [List.foldr_cons, List.foldr_cons, ih, iterate_dof_C_mul, hit, List.map_cons, List.prod_cons,
      map_mul]
    ring

end GlobalTheory.DerivEndo

namespace GlobalTheory

open DerivEndo QuadDeriv

theorem invariantDeriv_along_endo : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (B : FB R d O) (a : O), (∀ (u : Fin d → k) (g : PS k 1 d), Dof (B.FK k) u (ev (n := 1) ![B.actK k a] g) = ev (n := 1) ![B.actK k a] (Dof (B.FK k) ((dAct k B a).mulVec u) g)) ∧ ∀ (ι : Type) [Fintype ι] (u : ι → Fin d → k) (α : ι → k), (∀ l, (dAct k B a).mulVec (u l) = α l • u l) → ∀ (m : ι →₀ ℕ) (g : PS k 1 d), constantCoeff (DmonOf (B.FK k) u m (ev (n := 1) ![B.actK k a] g)) = (∏ l, α l ^ m l) * constantCoeff (DmonOf (B.FK k) u m g) := by
  intro R _ d O _ _ k _ _ _ B a
  have hF : GP (B.FK k) := constantCoeff_mapP_eq_zero _ _ B.G.const
  have hw : GP (B.actK k a) := constantCoeff_mapP_eq_zero _ _ (B.A.const a)
  have hU : evP (n := 1) ![pt k d 0, 0] (B.FK k) = pt k d 0 := by
    have := congrArg (mapP (algebraMap R k)) (unit_right B.G)
    rw [baseChange_addOf _ _ _ _ (gp_pt 0) gp_zero₂, baseChange_pt,
      show mapP (algebraMap R k) (0 : Pt R 1 d) = 0 from funext fun i => map_zero _] at this
    exact this
  have hom : comp1 (B.actK k a) (B.FK k) = addOf (B.FK k) (comp1 (B.actK k a) (pt k (n := 2) d 0))
      (comp1 (B.actK k a) (pt k (n := 2) d 1)) := by
    have := congrArg (mapP (algebraMap R k)) (B.A.hom a)
    rw [FGLaw.add, FGLaw.add, addOf_pt, baseChange_comp1 _ _ _ B.G.const,
      baseChange_addOf _ _ _ _ (gp_comp1 _ _ (B.A.const a) (gp_pt 0))
        (gp_comp1 _ _ (B.A.const a) (gp_pt 1)),
      baseChange_comp1 _ _ _ (gp_pt 0), baseChange_comp1 _ _ _ (gp_pt 1), baseChange_pt, baseChange_pt] at this
    exact this
  have h1 : ∀ (u : Fin d → k) (g : PS k 1 d), Dof (B.FK k) u (ev (n := 1) ![B.actK k a] g) =
      ev (n := 1) ![B.actK k a] (Dof (B.FK k) ((dAct k B a).mulVec u) g) :=
    dof_endo (B.FK k) hF (congrFun hU) (B.actK k a) hw hom
  refine ⟨h1, fun ι _ u α hα m g => ?_⟩
  rw [dmonOf_endo (B.FK k) (B.actK k a) hw u α (fun l g => by
    rw [h1, hα, dof_smul_dir, ChartTrans.ev_C_mul _ (single_point_zero_constant hw)]), map_mul, constantCoeff_C,
    constSt k d (B.actK k a) hw]

end GlobalTheory
end
end
