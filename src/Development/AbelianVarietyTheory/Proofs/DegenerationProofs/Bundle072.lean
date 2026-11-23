module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle004
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle015
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle067
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GenericInvariantsGeneratedByRatios
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle066
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsBasisLatticeNear
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle002
public import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle068
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle015
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical

namespace GlobalTheory.ThetaInvPart

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω}

theorem diag_eq [IsDomain o] {Q : Type} [AddCommGroup Q] [Fintype Q] (π : S.Gam →+ Q) (i₀ : S.J)
    (hc : Fintype.card S.J = Fintype.card Q)
    (hfix : ∀ a, π a = 0 → ∀ l, S.ρ a l i₀ = if l = i₀ then 1 else 0)
    (horb : ∀ i, ∃ a, ∃ e : ℕ, ∀ l, S.ρ a l i₀ = if l = i then S.ζ ^ e else 0) (a : S.Gam) :
    S.ρ a i₀ i₀ = if π a = 0 then 1 else 0 := by
  have hζ : S.ζ ≠ 0 := S.prim.ne_zero (pow_ne_zero _ (Nat.mul_ne_zero (by have := S.r_pos; omega)
    (by have := S.N_ge; omega)))
  choose c e hce using horb
  have key : ∀ a b, π a = π b → ∃ k : ℕ, ∀ l, S.ρ b l i₀ = S.ζ ^ k * S.ρ a l i₀ := fun a b h => by
    obtain ⟨k, hk⟩ := S.ρ_mul b (a - b)
    refine ⟨k, fun l => ?_⟩
    have := congrFun (congrFun hk l) i₀
    rw [Matrix.mul_apply, add_sub_cancel, Matrix.smul_apply, smul_eq_mul] at this
    simpa [hfix (a - b) (by rw [map_sub, h, sub_self])] using this
  have inj : Function.Injective fun i => π (c i) := fun i j h => by
    obtain ⟨k, hk⟩ := key _ _ h
    by_contra hij
    have := hk j
    rw [hce, hce, if_pos rfl, if_neg (Ne.symm hij), mul_zero] at this
    exact pow_ne_zero _ hζ this
  have surj := ((Fintype.bijective_iff_injective_and_card _).2 ⟨inj, hc⟩).2
  have zero : ∀ a i, π (c i) = π a → i ≠ i₀ → S.ρ a i₀ i₀ = 0 := fun a i h hi => by
    obtain ⟨k, hk⟩ := key _ _ h
    rw [hk, hce, if_neg (Ne.symm hi), mul_zero]
  split_ifs with ha
  · rw [hfix a ha, if_pos rfl]
  · obtain ⟨i, hi⟩ := surj (π a)
    refine zero a i hi fun h => ?_
    obtain ⟨j, hj⟩ := surj (π 0)
    by_cases h' : j = i₀
    · exact ha (by rw [← hi, h, ← h', hj, map_zero])
    · have := zero 0 j hj h'
      rw [hfix 0 (map_zero π), if_pos rfl] at this
      exact one_ne_zero this

theorem rho_fix (hG : GlobalFnsSt) (hi : Function.Injective (algebraMap o Ω)) (ρ : S.Real) (a : S.Gam)
    (ha : (ρ.n ^ ρ.k) • S.r • a = 0) (l : S.J) : S.ρ a l ρ.i₀ = if l = ρ.i₀ then 1 else 0 := by
  have := ρ.P.isAb.comm
  have h0 : ρ.pt 0 = 1 := by
    have := ρ.pt_add 0 0
    rw [add_zero] at this
    exact left_eq_mul.1 this
  have hp : ∀ (n : ℕ) b, ρ.pt (n • b) = ρ.pt b ^ n := fun n b => by
    induction n with
    | zero => rw [zero_smul, pow_zero, h0]
    | succ n ih => rw [succ_nsmul, ρ.pt_add, ih, pow_succ]
  have hm : ρ.pt (S.r • a) ^ (ρ.n ^ ρ.k) = 1 := by rw [← hp, ha, h0]
  have hN : ρ.pt (S.r • a) ^ S.N = 1 :=
    (congrArg _ (ρ.N_eq.trans (sq _))).trans (by rw [pow_mul, hm, one_pow])
  obtain ⟨ν, hν⟩ := exists_gen_negLB hG _ ρ.P 1 (baseOver (Sp S.R))
  have hact := ThetaCoord.isActOf_self hG ρ.P.isAb ρ.P.isLB (q := S.N) (b := 1)
    (by rw [ρ.N_eq]; exact ρ.n_odd.pow.pow) hν ρ.α_gen ρ.s_zero hm hN (ρ.U_sym a)
  have h₁ := ρ.U_act a ρ.i₀ _ hact
  have h₂ : ∀ j, (ρ.s ρ.i₀).f j = ∑ l, liftFun ρ.P.A _ (fn (algebraMap o S.R (if l = ρ.i₀ then 1 else 0))) *
      (ρ.s l).f j := fun j => by
    rw [Finset.sum_eq_single ρ.i₀ (fun b _ hb => by simp [hb, liftFun]) (by simp)]
    simp [liftFun]
  have h₃ := congrFun ((ρ.s_basis (ρ.s ρ.i₀)).unique h₁ h₂) l
  have h₄ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of S.R)).inv).1 h₃
  exact hi (congrArg Subtype.val h₄)

end GlobalTheory.ThetaInvPart

namespace GlobalTheory

open ThetaInvPart

theorem proj_zero_pullback_ne_zero : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω]
    (S : ThetaSys o Ω) (ρ : S.Real) (k : Type) [Field k] (y : o →+* k) (T : AddSubgroup S.Gam), S.IsoFree T →
    ∃ j, y (S.proj T 0 j ρ.i₀) ≠ 0 := by
  intro hL o Ω _ _ _ hA S ρ k _ y T _
  have hN := S.N_ge
  have hr := S.r_pos
  have : NeZero (S.r * S.N) := ⟨Nat.mul_ne_zero (by omega) (by omega)⟩
  have : NeZero (ρ.n ^ ρ.k) := ⟨pow_ne_zero _ ρ.n_prime.ne_zero⟩
  have : IsDomain o := hA.inj.isDomain _
  have hd : ρ.n ^ ρ.k ∣ S.r * S.N := by
    rw [ρ.N_eq]; exact Dvd.dvd.mul_left (dvd_pow_self _ two_ne_zero) _
  let π : S.Gam →+ (Fin S.g ⊕ Fin S.g → ZMod (ρ.n ^ ρ.k)) :=
    (ZMod.castHom hd (ZMod (ρ.n ^ ρ.k))).toAddMonoidHom.compLeft _
  have hdiag := diag_eq π ρ.i₀ (by
      rw [ρ.card, ρ.N_eq, ← pow_mul]
      simp [two_mul])
    (fun a ha => rho_fix hL.1.globalFns hA.inj ρ a (funext fun i => by
      have h : ZMod.castHom hd (ZMod (ρ.n ^ ρ.k)) (a i) = 0 := congrFun ha i
      rw [← ZMod.natCast_zmod_val (a i), map_natCast, ZMod.natCast_eq_zero_iff] at h
      obtain ⟨c, hc⟩ := h
      rw [Pi.smul_apply, Pi.smul_apply, ← ZMod.natCast_zmod_val (a i), hc, nsmul_eq_mul, nsmul_eq_mul,
        ← Nat.cast_mul, ← Nat.cast_mul, Pi.zero_apply, ZMod.natCast_eq_zero_iff]
      exact ⟨c, by rw [ρ.N_eq]; ring⟩)) ρ.orbit
  have hu : ∀ n : ℕ, n ∣ Nat.card S.Gam → IsUnit (n : o) := fun n hn => by
    refine isUnit_of_dvd_unit (Nat.cast_dvd_cast hn) ?_
    rw [Nat.card_fun, Nat.card_zmod, Nat.cast_pow]
    exact S.unit.pow _
  refine ⟨ρ.i₀, (IsUnit.map y ?_).ne_zero⟩
  have := Fintype.ofFinite T
  have hT := AddSubgroup.card_addSubgroup_dvd_card T
  have hK := (AddSubgroup.card_addSubgroup_dvd_card (π.comp T.subtype).ker).trans hT
  have hs : ∑ t : T, S.ρ t ρ.i₀ ρ.i₀ = (Nat.card (π.comp T.subtype).ker : o) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter, Nat.cast_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [hdiag]
    by_cases h : π t = 0 <;> simp [AddMonoidHom.mem_ker, h]
  rw [ThetaSys.proj, finsum_eq_sum_of_fintype, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
  simp only [AddMonoidHom.zero_apply, neg_zero, ZMod.val_zero, pow_zero, one_smul]
  rw [hs]
  exact (hu _ hT).ringInverse.mul (hu _ hK)

end GlobalTheory
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.lineBundleSymmetry_hypothesis_base_change : ∀ (B B' : Scheme.{0}) (G : Over B) (G' : Over B') [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] (f : B' ⟶ B) (φ : G'.left ⟶ G.left) (L : LB G.left) (L' : LB G'.left), L.IsLB → L'.IsLB → IsGrpPullback G' G f φ → LBIso L' (L.pull φ) → HypS G L → HypS G' L' := by
  first | exact @GlobalTheory.SymBaseChange.hypS_baseChange | exact GlobalTheory.SymBaseChange.hypS_baseChange | (intros; apply GlobalTheory.SymBaseChange.hypS_baseChange <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

theorem _root_.GlobalTheory.T.generic_invariants_generated_by_ratios : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] [IsSeparated G.hom] [QuasiCompact G.hom] (C : Charts G.left) (d : ℕ) (c : Fin d → C.Cl) (Sg : Set (Sp R)) [IsAffineHom (pullback.fst G.hom (Out.jK R))], Dense Sg → C.SplitOn c Sg → ∀ (a) (j : Fin d → C.I), C.Based c a j → ∀ i : splitTorus (Sp (FractionRing R)) (Fin d → ℤ) ⟶ ((Over.pullback (Out.jK R)).obj G), Charts.KerIs (H := ((Over.pullback (Out.jK R)).obj G)) (C.pull (pullback.fst G.hom (Out.jK R))) a j i → (∀ a', Stable i ((C.pull (pullback.fst G.hom (Out.jK R))).W a')) → ∀ a' (u : Γ(((Over.pullback (Out.jK R)).obj G).left, (C.pull (pullback.fst G.hom (Out.jK R))).W a')), HasWt i _ u 0 → u ∈ Subring.closure (Set.range (((Over.pullback (Out.jK R)).obj G).hom.appLE ⊤ ((C.pull (pullback.fst G.hom (Out.jK R))).W a') le_top).hom ∪ {v | ∃ j', C.wt j' = C.c₀ ∧ v = (C.pull (pullback.fst G.hom (Out.jK R))).r a' j'}) := by
  first | exact @GlobalTheory.ZJ.GenericInv.generic_invariants | exact GlobalTheory.ZJ.GenericInv.generic_invariants | (intros; apply GlobalTheory.ZJ.GenericInv.generic_invariants <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH.WeightZero

theorem eq_zero_of_q_nonpos {X : Type} [AddCommGroup X] [Module.Free ℤ X] (q : QuadraticMap ℤ X ℝ)
    (hq : Filter.Tendsto q Filter.cofinite Filter.atTop) {α : X} (h : q α ≤ 0) : α = 0 := by
  by_contra h0
  have h1 : {x | ¬ 0 < q x}.Finite := Filter.eventually_cofinite.1 (hq.eventually_gt_atTop 0)
  refine Set.infinite_of_injective_forall_mem (f := fun n : ℤ => n • α) (smul_left_injective ℤ h0)
    (fun n => ?_) h1
  rw [Set.mem_setOf_eq, q.map_smul, not_lt]
  exact smul_nonpos_of_nonneg_of_nonpos (mul_self_nonneg n) h

theorem proj_congr {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω)
    {T T' : AddSubgroup S.Gam} (h : T = T') (c : T →+ ZMod S.N) (c' : T' →+ ZMod S.N)
    (hc : ∀ t ht ht', c ⟨t, ht⟩ = c' ⟨t, ht'⟩) : S.proj T c = S.proj T' c' := by
  subst h
  rw [show c = c' from AddMonoidHom.ext fun t => hc t.1 t.2 t.2]

theorem nsmul_char {T : Type} [AddCommGroup T] (N : ℕ) (c : T →+ ZMod N) : N • c = 0 := by
  ext x
  rw [AddMonoidHom.nsmul_apply]
  simp

theorem map_add_nsmul {X T : Type} [AddCommGroup X] [AddCommGroup T] (N : ℕ) (w : X →+ (T →+ ZMod N)) (β m : X) :
    w (β + N • m) = w β := by
  rw [map_add (f := _), map_nsmul, nsmul_char, add_zero]

theorem span_eq_of_test {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] [hA : ArithBase o Ω] {S : ThetaSys o Ω}
    {p : ℕ} [Fact p.Prime] {y₀ : S.R →+* PadicAlgCl p} (τ : S.Test p y₀) (b : S.J → S.J → PadicAlgCl p)
    (a : S.J → τ.X) (ha : ∀ i v, τ.q (a i) ≤ τ.q (a i + S.N • v))
    (hE : τ.E = Submodule.span (OO p) (Set.range b))
    (hb : ∀ i, ((S.proj _ (τ.wt (a i))).map fun x => y₀ (algebraMap o S.R x)).mulVec (b i) = b i) :
    Submodule.span (OO p) (b '' {i | a i = 0}) =
      Submodule.span (OO p) (Set.range fun i j => y₀ (algebraMap o S.R (S.proj (S.perp τ.yy.ker) 0 j i))) := by
  have : IsDomain o := hA.inj.isDomain
  have := FreeNear.finite_char S (S.perp τ.yy.ker)
  have := Fintype.ofFinite (S.perp τ.yy.ker →+ ZMod S.N)
  obtain ⟨hmul, -⟩ := FreeNear.proj_orthogonal S _ τ.isoFree
  have hz : ∀ α, (∀ v, τ.q α ≤ τ.q (α + S.N • v)) → 0 = τ.wt α → α = 0 := fun α hα h => by
    have h3 := TestBasis.q_le_of_wt_eq τ hα (β := 0) (by rw [map_zero, h])
    rw [map_zero] at h3
    exact eq_zero_of_q_nonpos _ τ.pos h3
  let φ : o →+* PadicAlgCl p := y₀.comp (algebraMap o S.R)
  obtain ⟨Q, hQd⟩ : ∃ Q : (S.perp τ.yy.ker →+ ZMod S.N) → Matrix S.J S.J (PadicAlgCl p),
    ∀ c j i, y₀ (algebraMap o S.R (S.proj _ c j i)) = Q c j i := ⟨fun c => (S.proj _ c).map φ, fun _ _ _ => rfl⟩
  have hQe : ∀ c, Q c = φ.mapMatrix (S.proj _ c) := fun c => Matrix.ext fun j i => (hQd c j i).symm
  have hQ : ∀ c, Q 0 * Q c = if 0 = c then Q 0 else 0 := fun c => by
    rw [hQe, hQe, ← map_mul, hmul]
    split_ifs
    · rfl
    · exact map_zero _
  obtain ⟨L, hL⟩ : ∃ L : (S.J → PadicAlgCl p) →ₗ[OO p] (S.J → PadicAlgCl p), ∀ v, L v = (Q 0).mulVec v :=
    ⟨(Q 0).mulVecLin.restrictScalars (OO p), fun _ => rfl⟩
  have hcol : ∀ c i, L (fun j => Q c j i) = fun j => (Q 0 * Q c) j i := fun c i => hL _
  have hb' : ∀ i, (Q (τ.wt (a i))).mulVec (b i) = b i := fun i => by
    rw [hQe]
    exact hb i
  simp only [hQd]
  have h1 : τ.E.map L ≤ Submodule.span (OO p) (Set.range fun i j => Q 0 j i) := by
    rw [ThetaSys.Test.E, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨α, l, i, hα, hl, rfl⟩, rfl⟩
    simp only [hQd]
    have h2 : L (fun j => l * Q (τ.wt α) j i) = l • fun j => (Q 0 * Q (τ.wt α)) j i := by
      rw [← hcol, hL, hL, ← Matrix.mulVec_smul]
      rfl
    rw [h2, hQ]
    split_ifs with h
    · rw [hz α hα h, map_zero, zero_div, Real.exp_zero] at hl
      exact Submodule.smul_mem _ (⟨l, (mem_OO_iff _).2 hl⟩ : OO p) (Submodule.subset_span ⟨i, rfl⟩)
    · rw [show (fun j => (0 : Matrix S.J S.J (PadicAlgCl p)) j i) = 0 from rfl, smul_zero]
      exact Submodule.zero_mem _
  have h2 : τ.E.map L ≤ Submodule.span (OO p) (b '' {i | a i = 0}) := by
    rw [hE, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    by_cases h : 0 = τ.wt (a i)
    · rw [hL, h, hb']
      exact Submodule.subset_span ⟨i, hz _ (ha i) h, rfl⟩
    · rw [hL, ← hb', Matrix.mulVec_mulVec, hQ, if_neg h, Matrix.zero_mulVec]
      exact Submodule.zero_mem _
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
  · rintro _ ⟨i, hi, rfl⟩
    refine h1 ⟨b i, hE ▸ Submodule.subset_span ⟨i, rfl⟩, ?_⟩
    have := hb' i
    rw [show a i = 0 from hi, map_zero] at this
    rw [hL, this]
  · rintro _ ⟨i, rfl⟩
    refine h2 ⟨fun j => Q 0 j i, Submodule.subset_span ⟨0, 1, i, fun v => ?_, ?_, ?_⟩, ?_⟩
    · rw [map_zero]
      by_contra! h
      rw [eq_zero_of_q_nonpos _ τ.pos h.le, map_zero] at h
      exact lt_irrefl _ h
    · simp
    · funext j
      rw [map_zero, _root_.one_mul, hQd]
    · rw [hcol, hQ, if_pos rfl]

theorem short_transfer {X Y Z : Type} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z] (e : X ≃+ Y) (f : Z ≃+ Y)
    (q : QuadraticMap ℤ X ℝ) (q' : QuadraticMap ℤ Y ℝ) (hq : ∀ α, q α = q' (e α)) {N : ℕ} {y : Y}
    (h : Short (q'.comp f.toIntLinearEquiv.toLinearMap) N (f.symm y)) (v : X) :
    q (e.symm y) ≤ q (e.symm y + N • v) := by
  have h3 : q' (f (f.symm y)) ≤ q' (f (f.symm y + N • f.symm (e v))) := h (f.symm (e v))
  simpa [hq] using h3

end GlobalTheory.ZH.WeightZero

namespace GlobalTheory.ZH


open WeightZero in
theorem span_rows_class_zero : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (t : ρ.GeoTest p y₀), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → t.τ.yy.ker = t.l.yy.ker ∧ (∀ α β, t.l.wt α = t.l.wt β ↔ ∃ m, α = β + S.N • m) ∧ Submodule.span (OO p) ((t.b.map (algebraMap _ (PadicAlgCl p))) '' {i | t.cls i = 0}) = Submodule.span (OO p) (Set.range fun i j => y₀ (algebraMap o S.R (S.proj (S.perp t.l.yy.ker) 0 j i))) := by
  intro o Ω _ _ _ hA S ρ p _ y₀ t _
  obtain ⟨e, hq, hy⟩ := t.mt
  have hker : t.τ.yy.ker = t.l.yy.ker := by
    ext a
    have := hy a 0
    rw [map_zero] at this
    exact this
  have hwt : ∀ α x h h', t.τ.wt α ⟨x, h⟩ = t.l.wt (e α) ⟨x, h'⟩ := fun α x h h' => by
    obtain ⟨a, ha⟩ := t.τ.yy_onto (QuotientAddGroup.mk α)
    rw [t.τ.wt_eq a α ha, t.l.wt_eq a _ ((hy a α).1 ha)]
  have hz : ∀ α, t.l.wt (e α) = 0 → ∃ v, α = S.N • v := fun α h =>
    TestBasis.exists_nsmul_of_wt_eq_zero t.τ α (AddMonoidHom.ext fun x => by
      rw [hwt α x.1 x.2 (hker ▸ x.2), h]
      rfl)
  have hcl : ∀ α β, t.l.wt α = t.l.wt β ↔ ∃ m, α = β + S.N • m := fun α β => by
    constructor
    · intro h
      obtain ⟨v, hv⟩ := hz (e.symm (α - β)) (by rw [e.apply_symm_apply, map_sub, h, sub_self])
      refine ⟨e v, ?_⟩
      rw [← map_nsmul, ← hv, e.apply_symm_apply, add_sub_cancel]
    · rintro ⟨m, rfl⟩
      exact map_add_nsmul _ _ _ _
  refine ⟨hker, hcl, ?_⟩
  have h1 := span_eq_of_test t.τ (t.b.map (algebraMap _ (PadicAlgCl p))) (fun i => e.symm (t.cls i))
    (fun i => short_transfer e t.mod.xe _ _ hq (t.mod.good.short i)) t.span
    (fun i => by
      have h3 : S.proj _ (t.τ.wt (e.symm (t.cls i))) = S.proj _ (t.l.wt (t.cls i)) :=
        proj_congr S (congrArg S.perp hker) _ _ fun x h h' =>
          (hwt _ x h h').trans (by rw [e.apply_symm_apply])
      rw [h3]
      exact t.wt i)
  have h2 : {i | e.symm (t.cls i) = 0} = {i | t.cls i = 0} := Set.ext fun i => e.symm.map_eq_zero_iff
  have h3 : S.proj (S.perp t.τ.yy.ker) 0 = S.proj (S.perp t.l.yy.ker) 0 :=
    proj_congr S (congrArg S.perp hker) _ _ fun _ _ _ => rfl
  rw [h2, h3] at h1
  exact h1

end GlobalTheory.ZH
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ZH.ZHPre
variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]
variable {S : ThetaSys o Ω} {ρ : S.Real} {M : RatModel o Ω} {U₀ : M.Z.Opens} (Q : ZHPre ρ M U₀)

abbrev LOne : LB Q.G.left := LB.LinComb Q.L.L (K := Fin 1) (fun _ => 𝟙 Q.G.left) (fun _ => 1)

abbrev SecFam (N : M.Z.Opens) : Type := ∀ j, Γ(Q.G.left, Q.G.hom ⁻¹ᵁ N ⊓ Q.LOne.U j)

abbrev ThMul (c : Ω) (N : M.Z.Opens) (σ : Q.SecFam N) : Prop :=
  GenVal ρ M U₀ Q.u₀ Q.G Q.φ Q.L.L Q.w 1 (fun _ : Unit => ρ.th₁) (fun _ => c) _ σ

abbrev FibNe (N : M.Z.Opens) (σ : Q.SecFam N) : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ M.Z), Set.range x ⊆ N →
    ∃ (g : Sp K ⟶ Q.G.left) (j : _), g ≫ Q.G.hom = x ∧ valF g _ (σ j) ≠ 0

abbrev ExtPt (a : S.Gam) (W : M.Z.Opens) (h : W.toScheme ⟶ Q.G.left) : Prop :=
  h ≫ Q.G.hom = W.ι ∧
  ∀ (x : Sp Ω ⟶ W.toScheme) (x' : Sp Ω ⟶ pullback ρ.P.A.hom Q.u₀), x ≫ W.ι = M.pt → x' ≫ Q.φ ≫ Q.G.hom = M.pt →
    x' ≫ pullback.fst _ _ = spMap S.R.val.toRingHom ≫ (ρ.pt a).left → x ≫ h = x' ≫ Q.φ

def MulRel (n : ℕ)
    (α : LB.Gen (LB.LinComb ρ.P.L (K := Fin 2) ![𝟙 ρ.P.A.left, (mulA ρ.P.A n).left] ![(n : ℤ) ^ 2, -1]))
    (κ : LB.Gen (LB.LinComb Q.L.L (K := Fin 2) ![𝟙 Q.G.left, (mulA Q.G n).left] ![(n : ℤ) ^ 2, -1])) : Prop :=
  ∀ (K : Type) [Field K] (g g' : Sp K ⟶ pullback ρ.P.A.hom Q.u₀) (jP jP' : ρ.P.L.ι) (jL jL' : Q.L.L.ι),
    g' ≫ pullback.fst _ _ = g ≫ pullback.fst _ _ ≫ (mulA ρ.P.A n).left →
    g' ≫ pullback.snd _ _ = g ≫ pullback.snd _ _ →
    Set.range (g ≫ pullback.fst ρ.P.A.hom Q.u₀) ⊆ ρ.P.L.U jP → Set.range (g ≫ Q.φ) ⊆ Q.L.L.U jL →
    Set.range (g' ≫ pullback.fst ρ.P.A.hom Q.u₀) ⊆ ρ.P.L.U jP' → Set.range (g' ≫ Q.φ) ⊆ Q.L.L.U jL' →
    valF (g ≫ pullback.fst ρ.P.A.hom Q.u₀) _ (α.s ![jP, jP']).val *
        valF g' _ (Q.w.s (fun _ => jP', fun _ => jL')).val =
      valF g _ (Q.w.s (fun _ => jP, fun _ => jL)).val ^ (n ^ 2) * valF (g ≫ Q.φ) _ (κ.s ![jL, jL']).val

def FrameUnit (a : S.Gam) (W : M.Z.Opens) (h : W.toScheme ⟶ Q.G.left) (w : W.toScheme) : Prop :=
  ∀ (jP : ρ.P.L.ι) (jL : Q.L.L.ι) (x' : Sp Ω ⟶ pullback ρ.P.A.hom Q.u₀) (e : Ω), h w ∈ Q.L.L.U jL →
    x' ≫ Q.φ ≫ Q.G.hom = M.pt → x' ≫ pullback.fst _ _ = spMap S.R.val.toRingHom ≫ (ρ.pt a).left →
    Set.range (x' ≫ pullback.fst ρ.P.A.hom Q.u₀) ⊆ ρ.P.L.U jP →
    e = valF (X := (baseOver (Sp S.R)).left) (spMap S.R.val.toRingHom) _ ((ρ.fr a).s fun _ => jP).val /
      valF x' _ (Q.w.s (fun _ => jP, fun _ => jL)).val →
    e ≠ 0 ∧ e ∈ M.O (W.ι w) ∧ e⁻¹ ∈ M.O (W.ι w)

def TestFac {p : ℕ} [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) {y₀ : S.R →+* PadicAlgCl p} (u : ρ.UTest p y₀)
    (jV : u.V →+* OO p) (yV : Sp u.V ⟶ M.Z) (yK : Sp (FractionRing u.V) ⟶ U₀.toScheme) : Prop :=
  (∀ x, (jV x : PadicAlgCl p) = algebraMap (FractionRing u.V) _ (algebraMap u.V (FractionRing u.V) x)) ∧
    spMap jV ≫ yV = y ∧ yK ≫ U₀.ι = jK u.V ≫ yV ∧ yK ≫ Q.u₀ = spMap u.yK

def TestMap {p : ℕ} [Fact p.Prime] {y₀ : S.R →+* PadicAlgCl p} (u : ρ.UTest p y₀)
    (yV : Sp u.V ⟶ M.Z) (yK : Sp (FractionRing u.V) ⟶ U₀.toScheme) (F : u.G.left ⟶ Q.G.left)
    (ψ : pullback u.G.hom (jK u.V) ⟶ pullback ρ.P.A.hom Q.u₀) : Prop :=
  IsGrpPullback u.G Q.G yV F ∧ ψ ≫ pullback.fst _ _ = u.U.gen.hom.left ≫ u.φ ∧
    ψ ≫ pullback.snd _ _ = pullback.snd _ _ ≫ yK ∧ ψ ≫ Q.φ = pullback.fst _ _ ≫ F

end GlobalTheory.ZH.ZHPre
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH.PsiForm

theorem q_eq_val_mul : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab), ∃ (ϖ : u.V) (Q : u.D.toPre.X → ℤ), Irreducible ϖ ∧ DVR.QForm.IsQ u.D.toPre ϖ Q ∧ ‖(u.j ϖ : PadicAlgCl p)‖ < 1 ∧ ∀ χ, l.q χ = Q χ * (-Real.log ‖(u.j ϖ : PadicAlgCl p)‖) := by
  intro o Ω _ _ _ _ S ρ p _ y₀ u l
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible u.V
  choose Q hQ using DVR.QForm.exists_QVal hϖ u.D
  have hj : (u.j ϖ : PadicAlgCl p) =
      algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V (FractionRing u.V) ϖ) := rfl
  refine ⟨ϖ, Q, hϖ, hQ, ?_, fun χ => ?_⟩
  · rw [hj]
    exact norm_lt_one_of_irreducible u.norm_le hϖ
  · have hc := u.D.toPre.P.isLB.cover
    let x : Sp u.V := IsLocalRing.closedPoint u.V
    have hx : (u.D.toPre.c χ).left x ∈ ⨆ i, u.D.toPre.P.L.U i := by rw [hc]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
    have htop : ⊤ ≤ (u.D.toPre.c χ).left ⁻¹ᵁ u.D.toPre.P.L.U i :=
      ((IsLocalRing.closedPoint_mem_iff (R := u.V) _).1 hi).ge
    have h1 := l.q_eq χ (fun _ => i) htop
    have h2 := norm_of_hasVal u.norm_le hϖ
      (hasVal_valF u.D.toPre.P.L _ _ (DVR.QForm.ptK_eq u.D.toPre χ) (-1) _ (hQ χ) (fun _ => i) htop)
    have h3 := neg_injective (Real.exp_injective (h1.symm.trans h2))
    rw [hj, h3, mul_comm]

end GlobalTheory.ZH.PsiForm
end

section

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators

theorem _root_.GlobalTheory.T.degenerationSeriesTerms_nest : ∀ (O : Type) [CommRing O] (N : NumD O), ∀ (n m : ℕ), Odd n → Odd m → ∀ (p'' : N.QT ((n * m) ^ 2)) (p : N.QT (m ^ 2)), p''.1.1 = p.1.1 ^ n → p.1.2 = p''.1.2 ^ n → ∀ χ, N.txT (n * m) p'' χ = N.txT m p χ := by
  first | exact @GlobalTheory.Ex.Nest.txT_nest | exact GlobalTheory.Ex.Nest.txT_nest | (intros; apply GlobalTheory.Ex.Nest.txT_nest <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.ZH

namespace GlobalTheory.ZH

theorem exists_equiv_y_eq_zero : LL → AllD fun {R} _ _ {I} D F _ _ => ∀ (k : ℕ) (pk : QkPt D.toPre F k) (z : D.toPre.X), pk.y = k • z → ∃ p' : QkPt D.toPre F k, p'.y = 0 ∧ QkPt.Equiv D.toPre F pk p' := by
  intro _ R _ _ _ I _ D F _ _ _ k pk z hz
  refine ⟨GlobalTheory.TorusExt.qkShift D.tau_bimult pk (-z), ?_, GlobalTheory.TorusExt.equiv_qkShift D.tau_bimult pk (-z)⟩
  show pk.y + k • (-z) = 0
  rw [hz, smul_neg, add_neg_cancel]

end GlobalTheory.ZH
end
