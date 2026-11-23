module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle538
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle542
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle089
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle041
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NVNeZero
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.HeckeIntertwinersInert
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle007
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle397
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle155
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle160
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle257
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle002
import Development.AbelianVarietyTheory.Definitions.Degenerations.MorAlgSt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle003
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SvalEqZeroOfExpandsAt
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle782
import Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction
import Formalism.LocalToGlobal.IndefiniteReal.RecTie

@[expose] public section

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef
open scoped CategoryTheory.Obj

namespace GlobalTheory.PolExt

section Det

open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.FlagMod GlobalTheory.Reg GlobalTheory.PolFin
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv mkT tanM_ext tv_mem)

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l l' : Level H}
  {Xo : Moduli D l} {Xo' : Moduli D l'} {c : Coeff l} {c' : Coeff l'} {O O' : Type} [CommRing O] [CommRing O']
  {β : O →+* c.F} {β' : O' →+* c'.F} {Z : Model Xo c β} {Z' : Model Xo' c' β'} {N : Scheme.{0}} {p' : N ⟶ Z'.X}
  {p : N ⟶ Z.X} {G : Over N} [GrpObj G] [IsCommMonObj G] {ψ' : G.left ⟶ Z'.t.G.left} {ψ : G.left ⟶ Z.t.G.left}
  (h' : IsGrpPullback G Z'.t.G p' ψ') (h : IsGrpPullback G Z.t.G p ψ) {S S' : Type} [CommRing S] [CommRing S']

def pullBasis (M : MChart Z) (x : Sp S ⟶ N) (hx : ⊤ ≤ (x ≫ p) ⁻¹ᵁ M.U) : Module.Basis (Fin M.n) S (TanM x G) :=
  (lieBasis M (x ≫ p) hx).map (tanEquiv h x).symm

theorem tanPull_pullBasis (M : MChart Z) (φ : S →+* S') {x : Sp S ⟶ N} {x' : Sp S' ⟶ N} (e : spMap φ ≫ x = x')
    (hx : ⊤ ≤ (x ≫ p) ⁻¹ᵁ M.U) (hx' : ⊤ ≤ (x' ≫ p) ⁻¹ᵁ M.U) (j : Fin M.n) :
    tanPull φ e (pullBasis h M x hx j) = pullBasis h M x' hx' j := by
  have e' : spMap φ ≫ x ≫ p = x' ≫ p := by rw [← Category.assoc, e]
  apply (tanEquiv h x').injective
  rw [← tanPull_tanEquiv h φ e e']
  simp only [pullBasis, Module.Basis.map_apply, LinearEquiv.apply_symm_apply]
  exact tanPull_lieBasis M φ e' hx hx' j

theorem pullBasis_toMatrix (M M₁ : MChart Z) (x : Sp S ⟶ N) (hx : ⊤ ≤ (x ≫ p) ⁻¹ᵁ M.U)
    (hx₁ : ⊤ ≤ (x ≫ p) ⁻¹ᵁ M₁.U) : (pullBasis h M x hx).toMatrix (pullBasis h M₁ x hx₁) =
      (lieBasis M (x ≫ p) hx).toMatrix (lieBasis M₁ (x ≫ p) hx₁) := by
  ext i j
  simp [pullBasis, Module.Basis.toMatrix_apply]

def twoDet (M : MChart Z) (M' : MChart Z') (ha : IsAffineOpen (p ⁻¹ᵁ M.U ⊓ p' ⁻¹ᵁ M'.U)) :
    Γ(N, p ⁻¹ᵁ M.U ⊓ p' ⁻¹ᵁ M'.U)ˣ :=
  (isUnit_rdet_toMatrix (pullBasis h M (tau ha) (le_preimage_map p inf_le_left (tau_le _ le_rfl)))
    (pullBasis h' M' (tau ha) (le_preimage_map p' inf_le_right (tau_le _ le_rfl)))).unit

theorem ev_twoDet (M : MChart Z) (M' : MChart Z') (ha : IsAffineOpen (p ⁻¹ᵁ M.U ⊓ p' ⁻¹ᵁ M'.U)) (x : Sp S ⟶ N)
    (h₀ : ⊤ ≤ (x ≫ p) ⁻¹ᵁ M.U) (h₁ : ⊤ ≤ (x ≫ p') ⁻¹ᵁ M'.U) (hh : ⊤ ≤ x ⁻¹ᵁ (p ⁻¹ᵁ M.U ⊓ p' ⁻¹ᵁ M'.U)) :
    ev x _ hh (twoDet h' h M M' ha).val = rdet ((pullBasis h M x h₀).toMatrix (pullBasis h' M' x h₁)) := by
  have e : spMap (ev x _ hh) ≫ tau ha = x := spMap_ev x _ hh
  refine (map_rdet _ _).trans (congrArg rdet ?_)
  ext i j
  have h1 := (pullBasis h M (tau ha) (le_preimage_map p inf_le_left (tau_le _ le_rfl))).sum_toMatrix_smul_self
    (pullBasis h' M' (tau ha) (le_preimage_map p' inf_le_right (tau_le _ le_rfl))) j
  have h2 := congrArg (tanPull (G := G) _ e) h1

  rw [map_sum, tanPull_pullBasis h' M' _ e _ h₁] at h2
  simp only [map_smulₛₗ, tanPull_pullBasis h M _ e _ h₀] at h2
  rw [Module.Basis.toMatrix_apply, ← h2, Module.Basis.repr_sum_self]
  rfl


include h' h in
theorem lbIso_detLie_pull (ha : ∀ (U : Z.X.Opens) (U' : Z'.X.Opens), IsAffineOpen U → IsAffineOpen U' →
    IsAffineOpen (p ⁻¹ᵁ U ⊓ p' ⁻¹ᵁ U')) : LBIso ((detLie Z').pull p') ((detLie Z).pull p) := by
  have le : ∀ J : ((detLie Z).pull p).ι, ((detLie Z).pull p).U J ≤ p ⁻¹ᵁ (J PUnit.unit).U := fun J =>
    LB.wchart_le (detLie Z) (fun _ : PUnit => p) J PUnit.unit
  have le' : ∀ J : ((detLie Z').pull p').ι, ((detLie Z').pull p').U J ≤ p' ⁻¹ᵁ (J PUnit.unit).U := fun J =>
    LB.wchart_le (detLie Z') (fun _ : PUnit => p') J PUnit.unit
  refine ⟨⟨fun a => res (inf_le_inf (le a.1) (le' a.2))
    (twoDet h' h (a.1 PUnit.unit) (a.2 PUnit.unit) (ha _ _ (MChart.hU _) (MChart.hU _)))⟩, fun a b => ?_⟩
  refine Eq.trans ?_ (mul_right_comm _ _ _)
  refine eq_mul_inv_of_mul_eq (Units.ext (ext_ev fun S _ z hz => ?_))
  have hp := le_preimage_mono inf_le_left hz
  have hq := le_preimage_mono inf_le_right hz
  have hp1 : ⊤ ≤ z ⁻¹ᵁ ((detLie Z).pull p).U a.1 := le_preimage_mono inf_le_left hp
  have hq1 : ⊤ ≤ z ⁻¹ᵁ ((detLie Z).pull p).U b.1 := le_preimage_mono inf_le_left hq
  have hp2 : ⊤ ≤ z ⁻¹ᵁ ((detLie Z').pull p').U a.2 := le_preimage_mono inf_le_right hp
  have hq2 : ⊤ ≤ z ⁻¹ᵁ ((detLie Z').pull p').U b.2 := le_preimage_mono inf_le_right hq
  have hp0 := le_preimage_map p (le a.1) hp1
  have hq0 := le_preimage_map p (le b.1) hq1
  have hp3 := le_preimage_map p' (le' a.2) hp2
  have hq3 := le_preimage_map p' (le' b.2) hq2
  have hp4 := le_preimage_mono (inf_le_inf (le a.1) (le' a.2)) hp
  have hq4 := le_preimage_mono (inf_le_inf (le b.1) (le' b.2)) hq
  have g := ev_pull_g (detLie Z) p z a.1 b.1 (le_preimage_inf hp1 hq1) (le_preimage_inf hp0 hq0)
  have g' := ev_pull_g (detLie Z') p' z a.2 b.2 (le_preimage_inf hp2 hq2) (le_preimage_inf hp3 hq3)
  refine (map_mul (ev z _ hz) _ _).trans (Eq.trans ?_ (map_mul (ev z _ hz) _ _).symm)
  refine (congrArg₂ (· * ·) ((ev_res z _ hz hp _).trans ((ev_res z _ hp hp4 _).trans
    (ev_twoDet h' h _ _ _ z hp0 hp3 hp4)))
    ((ev_res z _ hz _ _).trans (g'.trans (ev_detChg _ _ _ hp3 hq3 _)))).trans (Eq.trans ?_
    (congrArg₂ (· * ·) ((ev_res z _ hz _ _).trans (g.trans (ev_detChg _ _ _ hp0 hq0 _)))
      ((ev_res z _ hz hq _).trans ((ev_res z _ hq hq4 _).trans (ev_twoDet h' h _ _ _ z hq0 hq3 hq4)))).symm)
  exact (congrArg (_ * rdet ·) (pullBasis_toMatrix h' _ _ z hp3 hq3).symm).trans ((rdet_toMatrix_mul _ _ _).trans
    ((congrArg (rdet · * _) (pullBasis_toMatrix h _ _ z hp0 hq0).symm).trans (rdet_toMatrix_mul _ _ _)).symm)

end Det

theorem isAffineOpen_snd_inf_fst {X Y T : Scheme.{0}} [IsAffine T] (f : X ⟶ T) (g : Y ⟶ T) {U : X.Opens} {V : Y.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) : IsAffineOpen (pullback.snd f g ⁻¹ᵁ V ⊓ pullback.fst f g ⁻¹ᵁ U) := by
  let m : pullback (hU.fromSpec ≫ f) (hV.fromSpec ≫ g) ⟶ pullback f g :=
    pullback.map _ _ _ _ hU.fromSpec hV.fromSpec (𝟙 _) (by simp) (by simp)
  have e : m.opensRange = pullback.snd f g ⁻¹ᵁ V ⊓ pullback.fst f g ⁻¹ᵁ U := by
    apply Opens.ext
    rw [Scheme.Hom.coe_opensRange, Scheme.Pullback.range_map, hU.range_fromSpec, hV.range_fromSpec, Set.inter_comm]
    rfl
  exact e ▸ isAffineOpen_opensRange m

end GlobalTheory.PolExt
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.LN GlobalTheory.TorRef GlobalTheory.IntegralCombination GlobalTheory.UU Formalism.L2.Pj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.IntFam

noncomputable section

namespace GlobalTheory.IntFam.CoordPow

theorem pow_law {X Q : Type} [AddCommGroup X] [CommGroup Q] (p : X → Q) (t : X → X → Q)
    (ht : ∀ a b, t a b = p (a + b) * (p a)⁻¹ * (p b)⁻¹) (hadd : ∀ a a' b, t (a + a') b = t a b * t a' b)
    (hev : ∀ χ, p (-χ) = p χ) (k : ℕ) (α μ : X) : p (α + k • μ) = p α * (p μ ^ k * t μ α) ^ k := by
  have hsym : ∀ a b, t a b = t b a := fun a b => by rw [ht, ht, add_comm, mul_right_comm]
  have h0 : ∀ b, t 0 b = 1 := fun b => by
    have := hadd 0 0 b
    rw [add_zero] at this
    exact left_eq_mul.1 this
  have hp0 : p 0 = 1 := by
    have := ht 0 0
    rw [h0, add_zero, mul_inv_cancel, one_mul] at this
    exact inv_eq_one.1 this.symm
  have hneg : ∀ a b, t (-a) b = (t a b)⁻¹ := fun a b => by
    have := hadd a (-a) b
    rw [add_neg_cancel, h0] at this
    exact eq_inv_of_mul_eq_one_right this.symm
  have hmm : t μ μ = p μ ^ 2 := by
    have e1 := hneg μ μ
    rw [hsym, ht, add_neg_cancel, hp0, hev, one_mul] at e1
    rw [← inv_inv (t μ μ), ← e1, ← mul_inv, inv_inv, sq]
  have hn : ∀ (n : ℕ) b, t (n • μ) b = t μ b ^ n := fun n b => by
    induction n with
    | zero => rw [zero_nsmul, pow_zero, h0]
    | succ n ih => rw [succ_nsmul, hadd, ih, pow_succ]
  have key : ∀ n : ℕ, p (α + n • μ) = p α * t μ α ^ n * p μ ^ (n * n) := fun n => by
    induction n with
    | zero => rw [zero_nsmul, add_zero, pow_zero, mul_zero, pow_zero, mul_one, mul_one]
    | succ n ih =>
      have e := ht (α + n • μ) μ
      have e2 : t (α + n • μ) μ = t μ α * (p μ ^ 2) ^ n := by
        rw [hadd, hsym α μ, hn, hmm]
      have e3 : p (α + n • μ + μ) = t (α + n • μ) μ * p (α + n • μ) * p μ := by
        rw [e]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv]
        abel
      rw [succ_nsmul, ← add_assoc, e3, e2, ih, ← pow_mul,
        show (n + 1) * (n + 1) = n * n + 2 * n + 1 by ring]
      simp only [pow_add, pow_one]
      ac_rfl
  rw [key, mul_assoc, mul_pow, ← pow_mul, mul_comm (t μ α ^ k)]

end GlobalTheory.IntFam.CoordPow

namespace GlobalTheory.IntFam.CoordPow

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]

theorem val_unit (D : DegPre R) (ξ : Spec (CommRingCat.of (FractionRing R))) {J} (hJc : IntegralCharts D J)
    {Y : Scheme.{0}} {K : Type} [Fintype K] {φ : K → (Y ⟶ D.P.A.left)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb D.P.L φ ε)) (q : Spec (CommRingCat.of R) ⟶ Y)
    (hq : ∀ k, (q ≫ φ k) ≫ D.P.A.hom = 𝟙 _) :
    ∃ u : Rˣ, (val t (jK R ≫ q) ξ J).val = GlobalTheory.PeriodBalance.cst ξ u := by
  refine GlobalTheory.PeriodBalance.unit_gm' ξ q _ (Set.mem_iInter.2 fun k => ?_) _
  have := hJc (q ≫ φ k) (hq k)
  simp only [Category.assoc]
  exact this

end GlobalTheory.IntFam.CoordPow

namespace GlobalTheory.IntFam.CoordPow

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]

theorem pull_unit (D : DegPre R) (ξ : Spec (CommRingCat.of (FractionRing R))) {J} (hJ : Good D.P.L ξ J)
    (hJc : IntegralCharts D J) {Y : Scheme.{0}} {K : Type} [Fintype K] {φ : K → (Y ⟶ D.P.A.left)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb D.P.L φ ε)) (q : Spec (CommRingCat.of R) ⟶ Y)
    (hq : ∀ k, (q ≫ φ k) ≫ D.P.A.hom = 𝟙 _) (h : (TK R).left ⟶ Y) (hh : h = jK R ≫ q) :
    ∃ u : Rˣ, (val (LB.pullGen D.P.L φ ε t h) (𝟙 _) ξ J).val = GlobalTheory.PeriodBalance.cst ξ u := by
  rw [val_pull hJ]
  have e : 𝟙 (TK R).left ≫ h = jK R ≫ q := by rw [hh]; exact Category.id_comp _
  rw [e]
  exact val_unit D ξ hJc t q hq

theorem rig_unit (D : DegPre R) (ξ : Spec (CommRingCat.of (FractionRing R))) {J} (hJ : Good D.P.L ξ J)
    (hJc : IntegralCharts D J) : ∃ u : Rˣ, (val D.rigK (𝟙 _) ξ J).val = GlobalTheory.PeriodBalance.cst ξ u := by
  refine pull_unit D ξ hJ hJc D.rig (𝟙 _) (fun _ => ?_) _ ?_
  · rw [Category.id_comp]
    unfold eSec
    exact Over.w _
  · rw [Over.toUnit_left, Category.comp_id]; rfl

omit [IsLocalRing R] in
theorem cub_hq (D : DegPre R) (a a' b : D.X) (I : thK) :
    ((lift (D.c a) (lift (D.c a') (D.c b))).left ≫ thφ D.P.A (x3 D.P.A) I) ≫ D.P.A.hom = 𝟙 _ := by
  show ((lift (D.c a) (lift (D.c a') (D.c b))).left ≫ (psum D.P.A (x3 D.P.A) I.down).left) ≫ D.P.A.hom = _
  rw [← Over.comp_left, Over.w]; rfl

omit [IsLocalRing R] in
theorem degenerationTriplePoint_eq_lift (D : DegPre R) (a a' b : D.X) :
    D.pt3 a a' b = jK R ≫ (lift (D.c a) (lift (D.c a') (D.c b))).left := by
  simp [DegPre.pt3, ← CartesianMonoidalCategory.comp_lift]

omit [IsLocalRing R] in
open MonObj in
theorem sym_hq (D : DegPre R) (χ : D.X) (k : Fin 2) :
    ((D.c χ).left ≫ (![(ι[D.P.A]).left, 𝟙 D.P.A.left] : Fin 2 → (D.P.A.left ⟶ D.P.A.left)) k) ≫ D.P.A.hom = 𝟙 _ := by
  fin_cases k
  · show ((D.c χ).left ≫ (ι[D.P.A]).left) ≫ D.P.A.hom = _
    rw [← Over.comp_left, Over.w]; rfl
  · show ((D.c χ).left ≫ 𝟙 _) ≫ D.P.A.hom = _
    rw [Category.comp_id, Over.w]; rfl

end GlobalTheory.IntFam.CoordPow

namespace GlobalTheory.IntFam.CoordPow

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R) (D : DegData R I) (k : ℕ)
    (α mu : D.toPre.X) (r s : R), PsiCoord D.toPre α r → PsiCoord D.toPre (α + k • mu) (r * s) →
    ∀ (ξ : Spec (CommRingCat.of (FractionRing R))) (J), Good D.toPre.P.L ξ J → GlobalTheory.IntFam.IntegralCharts D.toPre J →
      ∃ u : Rˣ, (val (GlobalTheory.UU.IntGen.multK D.toPre k mu α) (𝟙 _) ξ J).val ^ k = GlobalTheory.PeriodBalance.cst ξ (u * s) := by
  intro R _ _ _ I D k α mu r s hα hαk ξ J hJ hJc
  let H : Subgroup ((Spec (CommRingCat.of (FractionRing R))).presheaf.stalk ξ)ˣ :=
    (Units.map (GlobalTheory.PeriodBalance.cst ξ).toMonoidHom).range
  have mem : ∀ {g}, (∃ u : Rˣ, g.val = GlobalTheory.PeriodBalance.cst ξ u) → g ∈ H := fun ⟨u, hu⟩ =>
    ⟨u, Units.ext (by rw [Units.coe_map, hu]; rfl)⟩
  let π := QuotientGroup.mk' H
  have π1 : ∀ {g}, (∃ u : Rˣ, g.val = GlobalTheory.PeriodBalance.cst ξ u) → π g = 1 := fun h =>
    (QuotientGroup.eq_one_iff _).2 (mem h)
  let P : D.toPre.X → ((Spec (CommRingCat.of (FractionRing R))).presheaf.stalk ξ)ˣ :=
    fun χ => val (D.toPre.psi χ) (𝟙 _) ξ J
  let T : D.toPre.X → D.toPre.X → ((Spec (CommRingCat.of (FractionRing R))).presheaf.stalk ξ)ˣ :=
    fun a b => val (D.toPre.tau a b) (𝟙 _) ξ J
  let Z : ((Spec (CommRingCat.of (FractionRing R))).presheaf.stalk ξ)ˣ := val D.toPre.rigK (𝟙 _) ξ J
  have hZ : π Z = 1 := π1 (rig_unit D.toPre ξ hJ hJc)
  have law := pow_law (fun χ => π (P χ)) (fun a b => π (T a b))
    (fun a b => by
      show π (T a b) = π (P (a + b)) * (π (P a))⁻¹ * (π (P b))⁻¹
      rw [show T a b = P (a + b) * (P a)⁻¹ * (P b)⁻¹ * Z⁻¹ from GlobalTheory.PeriodBalance.val_tau D.toPre ξ hJ a b,
        map_mul, map_mul, map_mul, map_inv, map_inv, map_inv, hZ, inv_one, mul_one])
    (fun a a' b => by
      have e := (val_mul hJ _ _ _).symm.trans ((val_corr hJ (D.tau_bimult a a' b) (𝟙 _)).trans (val_mul hJ _ _ _))
      have hc := π1 (pull_unit D.toPre ξ hJ hJc D.toPre.cub.t _ (cub_hq D.toPre a a' b) _ (degenerationTriplePoint_eq_lift D.toPre a a' b))
      have e' := congrArg π e
      rw [map_mul, map_mul] at e'
      refine (mul_one _).symm.trans (Eq.trans ?_ e')
      congr 1
      exact hc.symm)
    (fun χ => by
      have e := (val_mul hJ _ _ _).symm.trans (val_corr hJ (D.psi_even χ) (𝟙 _))
      have hc := π1 (pull_unit D.toPre ξ hJ hJc D.toPre.sym _ (sym_hq D.toPre χ) _ (DVR.QForm.ptK_eq D.toPre χ))
      have e' := congrArg π e
      rw [map_mul] at e'
      refine (mul_one _).symm.trans (Eq.trans ?_ e')
      congr 1
      exact hc.symm) k α mu
  set v : ((Spec (CommRingCat.of (FractionRing R))).presheaf.stalk ξ)ˣ :=
    val (GlobalTheory.UU.IntGen.multK D.toPre k mu α) (𝟙 _) ξ J
  have hv : v = P mu ^ k * T mu α * Z ^ k :=
    (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (map_pow _ _ _) rfl))
      (map_pow _ _ _))
  have hq : π (v ^ k * P α * (P (α + k • mu))⁻¹) = 1 := by
    simp only [map_mul, map_inv, map_pow, hv, hZ, one_pow, mul_one]
    rw [law]
    exact mul_inv_eq_one.2 (mul_comm _ _)
  obtain ⟨w, hw⟩ := (QuotientGroup.eq_one_iff _).1 hq
  obtain ⟨u₁, h₁⟩ := GlobalTheory.PeriodBalance.val_psi D.toPre ξ hJ hJc α r hα
  obtain ⟨u₂, h₂⟩ := GlobalTheory.PeriodBalance.val_psi D.toPre ξ hJ hJc (α + k • mu) (r * s) hαk
  have e : v ^ k = Units.map (GlobalTheory.PeriodBalance.cst ξ).toMonoidHom w * P (α + k • mu) * (P α)⁻¹ := by
    rw [hw]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  have hA : ((P α)⁻¹).val * (GlobalTheory.PeriodBalance.cst ξ u₁ * GlobalTheory.PeriodBalance.cst ξ r) = 1 := by
    rw [← map_mul, ← h₁]; exact Units.inv_mul _
  have hu : GlobalTheory.PeriodBalance.cst ξ (u₁⁻¹ : Rˣ) * GlobalTheory.PeriodBalance.cst ξ u₁ = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  refine ⟨w * u₂ * u₁⁻¹, ?_⟩
  rw [← Units.val_pow_eq_pow_val, e, Units.val_mul, Units.val_mul, Units.coe_map, h₂]
  simp only [Units.val_mul, map_mul]
  linear_combination (-(GlobalTheory.PeriodBalance.cst ξ w * GlobalTheory.PeriodBalance.cst ξ u₂ * GlobalTheory.PeriodBalance.cst ξ s *
    GlobalTheory.PeriodBalance.cst ξ r * ((P α)⁻¹).val)) * hu + (GlobalTheory.PeriodBalance.cst ξ w * GlobalTheory.PeriodBalance.cst ξ u₂ *
    GlobalTheory.PeriodBalance.cst ξ s * GlobalTheory.PeriodBalance.cst ξ (u₁⁻¹ : Rˣ)) * hA

end GlobalTheory.IntFam.CoordPow
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2



namespace GlobalTheory.Mem.R3.LiftInertChi


open GlobalTheory.FinZeta.LevelOff in
theorem redFn_eq_one_of_locAt {D : D7} {V : HSp D} (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (x : Bridge.Gf V)
    (hS : Formalism.UG.bc (swapAE D) (x : GL (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) ∈ Formalism.L2.DIV.St β)
    (v : HeightOneSpectrum (𝓞 D.host.F)) (hx : GlobalTheory.IndefiniteRowSideFullHecke.HeckeIntertwinersInert.LocAt V v x) (PP : Formalism.L2.DIV.Pl D.host.E)
    (hPP : (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ≠ v) :
    Formalism.L2.DIV.redFn β PP (Formalism.UG.bc (swapAE D) (x : GL (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E))) = 1 := by
  classical
  set M : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) :=
    (x : GL (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)).val with hM
  set Sb : Finset (HeightOneSpectrum (𝓞 D.host.F)) := {(_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)} with hSb
  set b : FiniteAdeleRing (𝓞 D.host.F) D.host.F := 1 - GlobalTheory.AdeleIdem.ind Sb with hbdef
  have hb : b ∈ Formalism.UG.intAd D.host.F := sub_mem (one_mem _) (GlobalTheory.AdeleIdem.ind_mem Sb)
  have hz : ∀ (i j : Fin V.rank), ∀ w ∈ Sb, Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F w)
      (AlgHom.id D.host.F D.host.E) ((M - 1) i j) = 0 := by
    intro i j w hw
    rw [Finset.mem_singleton] at hw
    subst hw
    have h1 := congrFun (congrFun (hx ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) hPP) i) j
    rw [Matrix.map_apply] at h1
    rw [Matrix.sub_apply, map_sub, h1, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  refine GlobalTheory.LevSplit.redFn_eq_one β PP _ hS ⟨_, GlobalTheory.AdeleIdem.one_tmul_mem hb⟩ ?_ ?_
  · refine GlobalTheory.AdeleIdem.resS_eq_zero PP ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) rfl hb ?_
    simp [hbdef, GlobalTheory.AdeleIdem.ind_apply, hSb]
  · ext i j
    have h2 := one_sub_ind_tmul_mul Sb _ (hz i j)
    have e1 : ((Formalism.UG.bc (swapAE D) (x : GL (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E))).val - 1) i j =
        swapAE D ((M - 1) i j) := by
      rw [Matrix.sub_apply, Matrix.sub_apply, RingHom.map_sub]
      congr 1
      rw [Matrix.one_apply, Matrix.one_apply]
      split_ifs
      · exact (RingHom.map_one _).symm
      · exact (RingHom.map_zero _).symm
    rw [Matrix.smul_apply, smul_eq_mul, e1]
    show swapAE D (b ⊗ₜ[D.host.F] (1 : D.host.E)) * _ = _
    rw [← RingHom.map_mul, h2]

theorem locAt_of_isLocElt {D : D7} (V : HSp D) (P : Formalism.L2.DIV.Pl D.host.E) (x : Bridge.Gf V)
    (h : Formalism.IndefR.Links.IsLocElt V P x) : GlobalTheory.IndefiniteRowSideFullHecke.HeckeIntertwinersInert.LocAt V (P.under (𝓞 D.host.F)) x := by
  obtain ⟨e, f, g, hpi, hg, hx, hs⟩ := h
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  obtain ⟨-, ε, hε, rfl⟩ := GlobalTheory.IdemSupport.of_isPrimeIdem hΦ hpi
  have h1 := (GlobalTheory.HeckeRowsCompare.suppF_iff V hε hg).1 hs
  rw [GlobalTheory.HeckeRowsCompare.mem_locGrp] at h1
  have h2 : GlobalTheory.HeckeRowsCompare.fin V g = x := Subtype.ext hx.symm
  rw [h2] at h1
  exact (GlobalTheory.HeckeRowsCompare.locAt_iff V _ x).2 h1

theorem levChi_eq_one_of_isLocElt : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → ∀ (cV : ∀ i, CoefA (Vc X.toD7 i)) (i : Fin X.toD7.R.m) (t : TupU I U) (q : ↑((famR X I hX U Xg tr).okI t) × List ℕ) (j : (LiftBrg.envL X I hX U Xg tr L cV i t).lev.J),
    IsLocElt (Vc X.toD7 i) (q.1.1 : PlI X.B px).1 (j : Bridge.Gf (Vc X.toD7 i)) → (LiftBrg.envL X I hX U Xg tr L cV i t).lev.χ j = 1 := by
  intro X px I hX U Xg tr L eG hI hV hL hG cV i t q j hj
  set Q0 : Formalism.L2.DIV.Pl X.toD7.host.E := (q.1.1 : PlI X.B px).1 with hQ0
  have e : (LiftBrg.envL X I hX U Xg tr L cV i t).lev.χ j = Formalism.L2.DIV.levFn (L.βV i) (flag1L (L.datVt i t))
      (Formalism.UG.bc (swapAE X.toD7) (j : Bridge.Gf (Vc X.toD7 i)).1) := rfl
  have hm : Formalism.UG.bc (swapAE X.toD7) (j : Bridge.Gf (Vc X.toD7 i)).1 ∈
      Formalism.L2.DIV.lev X.toD7.sp.cm (Vc X.toD7 i).gram (L.βV i) (flag1L (L.datVt i t)) := j.2
  have hSt := Formalism.L2.DIV.parLev_St (Formalism.L2.DIV.lev_le_parLev hm)
  have hloc := locAt_of_isLocElt (Vc X.toD7 i) _ _ hj

  have hoff : Q0 ∉ Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1 := by
    have h := q.1.2
    exact fun hm => h (Or.inr hm)
  have hconj : Formalism.DivisionValues.conjPl Q0 = Q0 := by
    rw [← GlobalTheory.PlaceDict.conjP_eq_conjPl X.toD7]
    exact (q.1.1 : PlI X.B px).2.1
  have hunder : ∀ PP : Formalism.L2.DIV.Pl X.toD7.host.E, PP ∈ Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1 →
      PP.under (𝓞 X.toD7.host.F) ≠ Q0.under (𝓞 X.toD7.host.F) := by
    intro PP hPP hu
    rcases GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq hu with h | h
    · exact hoff (h ▸ hPP)
    · exact hoff ((h.trans hconj) ▸ hPP)
  have hred : ∀ PP ∈ Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1,
      Formalism.L2.DIV.redFn (L.βV i) PP (Formalism.UG.bc (swapAE X.toD7) (j : Bridge.Gf (Vc X.toD7 i)).1) = 1 :=
    fun PP hPP => redFn_eq_one_of_locAt _ _ hSt _ hloc PP (hunder PP hPP)
  have hPg : ∀ PP ∈ (flag1L (L.datVt i t)).Pg, PP ∈ Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1 := by
    intro PP hPP
    rw [show (flag1L (L.datVt i t)).Pg = L.Pg from rfl, hL.Pg] at hPP
    classical
    exact Finset.mem_union.2 (Or.inl hPP)
  have hQ : ∀ PP ∈ (flag1L (L.datVt i t)).Q, PP ∈ Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1 := by
    intro PP hPP
    rw [show (flag1L (L.datVt i t)).Q = L.Q t from rfl, hL.Q t] at hPP
    have e4 : I.Q (ixOf I U t) = Formalism.L2.Col.QE I.sel t.1 := by
      simp only [ColIn.Q, tup_ixOf]
    rw [e4] at hPP
    classical
    exact Finset.mem_union.2 (Or.inr hPP)
  have hr1 : Formalism.L2.DIV.rTup (L.βV i) (flag1L (L.datVt i t)) (Formalism.UG.bc (swapAE X.toD7) (j : Bridge.Gf (Vc X.toD7 i)).1) = 1 := by
    funext PP
    show Formalism.L2.DIV.upperLeftBlock _ (Formalism.L2.DIV.redFn _ PP.1 _) = 1
    rw [hred PP.1 (hPg PP.1 PP.2)]
    exact Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one _ _
  rw [e]
  unfold Formalism.L2.DIV.levFn
  rw [hr1, Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one, one_mul, Finset.prod_eq_one, Finset.prod_eq_one, one_mul]
  · intro PP hPP
    rw [hred PP (hQ PP hPP), Formalism.L2.DIV.dBlk, Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one, map_one]
  · intro PP hPP
    refine Finset.prod_eq_one fun c _ => ?_
    rw [hred PP (hPg PP hPP), Formalism.L2.DIV.dBlk, Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one, map_one]

end GlobalTheory.Mem.R3.LiftInertChi
end
