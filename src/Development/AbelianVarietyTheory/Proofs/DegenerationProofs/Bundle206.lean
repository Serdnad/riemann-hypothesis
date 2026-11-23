module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle098
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle118
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniformisedTableLatticeIntegralFamilies
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle121
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle133
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsAffineHomFromSpecResidueField
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle192
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle204
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle048
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle133
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle120
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle122
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullback
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle025
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.ExtremalEpi
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
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle039
import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
open GlobalTheory.ModelData

theorem _root_.GlobalTheory.T.exists_torsion_isometry_uniformised_model : GlobalTheory.UT.LL → BrGtSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (C : Type) [NormedField C] (o : Full D C) (M : Mdl o) (N' : NumD C) (_ : NumOf M.P.D.toPre C N'), ∃ I : TateIsoQ D M.P.D.toPre M.P.oD C, I.ζ = o.I.ζ ∧ ∀ k, 0 < k → ∀ x p' (z : TFK (R := M.W) C ⟶ M.P.A.A), QkPt.Equiv _ C (I.ev k x) p' → z.left = (o.I.ev k x).left ≫ M.φ → M.P.ToA C k p' z := by
  first | exact @GlobalTheory.ModelData.ModelTate.exists_tateIsoQ_of_model | exact GlobalTheory.ModelData.ModelTate.exists_tateIsoQ_of_model | (intros; apply GlobalTheory.ModelData.ModelTate.exists_tateIsoQ_of_model <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN

namespace GlobalTheory.LN

theorem uniformisation_dvr : Laws → Laws2 → Laws3 → Laws4 → Laws5 → USt := by
  intro h1 h2 h3 h4 h5 V _ _ _ A G _ _ s
  obtain ⟨D, U, hL, hg, -⟩ := GlobalTheory.T.exists_degenerationData_uniformisation_of_torsionCount (GlobalTheory.T.card_torsion_points_abelianVariety h1.globalFns h1.rigidity) h1 h2 V A G s
  refine ⟨D, U, hL, hg, ?_⟩
  obtain ⟨hdvr, hcomp, hchar⟩ := s.cdvr
  have hadm : AdmBase V (IsLocalRing.maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hcomp⟩
  intro F _ _ _ k hk p
  obtain ⟨f, hf, -⟩ := GlobalTheory.TorsionIso.torsion_eq ⟨h1, h2, h3, h4, h5⟩ V _ hadm D A G s.semi U F k hk
  exact ⟨f p, (hf p _).2 rfl⟩

end GlobalTheory.LN
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis

theorem _root_.GlobalTheory.T.uniformised_table_lattice_integral_families : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllUV fun {V} _ _ _ {ϖ} hϖ {D} Q {F} _ _ {v} hv {A} {G} _ _ U => ∀ w₀ ρ, NormW U.toUnifPre w₀ ρ → ∀ (th : SecA A F 1) (ϑ : Fam D.toPre F 1), U.ExpandsF F 1 w₀ th ϑ → Prim D Q v ϑ → ∀ m n : ℕ, Odd m → IsUnit (m : V) → 3 ≤ m → n.Prime → Odd n → IsUnit (n : V) → ∀ O : ValuationSubring F, (∀ x, x ∈ O ↔ 0 ≤ v x) → ∀ (r : ℕ) (cls : Fin r → D.toPre.X) (b τ : Fin r → SecA A F (m ^ 2)) (s : Fin r → Fam D.toPre F (m ^ 2)) (B : Matrix (Fin r) (Fin r) F), Norms D Q v (m ^ 2) cls s → (∀ i, U.ExpandsF F (m ^ 2) w₀ (b i) (s i)) → (∀ t, ∃! a, Cmb τ a t) → (∀ i, Cmb τ (B i) (b i)) → ∀ (d : ℕ) (κ : F), v κ = (((d : ℚ) * (∑ i, (Q (cls i) : ℚ)) / (m ^ 2 : ℕ) : ℚ) : WithTop ℚ) → (tab ρ m th τ).Loc O B n d κ := by
  first | exact @GlobalTheory.OneBasis.UnifLoc.main | exact GlobalTheory.OneBasis.UnifLoc.main | (intros; apply GlobalTheory.OneBasis.UnifLoc.main <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Relabel

namespace GlobalTheory.Relabel

theorem weilIs_push {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] [IsCommMonObj G']
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} {L : LB G.left} {L' : LB G'.left} (hL : L.IsLB) (hL' : L'.IsLB)
    (hp : IsGrpPullback G' G f φ) (hw : LBIso L' (L.pull φ)) (T : Over S') (g : T.left ⟶ S) (hg : g = T.hom ≫ f)
    (k : ℤ) (x y : T ⟶ G') (x₀ y₀ : Over.mk g ⟶ G) (c : Γ(T.left, ⊤)ˣ) (ex : x₀.left = x.left ≫ φ)
    (ey : y₀.left = y.left ≫ φ) (h : WeilIs G L k x₀ y₀ c) : WeilIs G' L' k x y c := by
  subst hg
  exact (GlobalTheory.weilIs_grpPullback_of_comm' S S' G G' f φ L L' hL hL' hp hw T k x y x₀ y₀ c ex ey).2 h

theorem exists_fullI_of_tateIsoQ : GlobalTheory.UT.LL → AllD fun {E} _ _ _ {H} D => ∀ (C : Type) [NormedField C] (o : Full D C) (M : Mdl o) (I' : TateIsoQ D M.P.D.toPre M.P.oD C), ∃ I : FullI o, I.ζ = I'.ζ ∧ ∀ j, 0 < j → ∀ x, ∃ z : TFK (R := M.W) C ⟶ M.P.A.A, z.left = (I.ev j x).left ≫ M.φ ∧ M.P.ToA C j (I'.ev j x) z := by
  intro hLL E _ _ _ H D C _ o M I'
  let := H.starRing
  have : IsAlgClosed C := o.closed
  obtain ⟨hadm, hcz⟩ := M.admissible_base_of_complete_dvr
  have : CharZero M.W := hcz
  have hall := GlobalTheory.TestFibre.laws_all hLL.1 hLL.2.1
  have hT : M.P.TorsionIso := GlobalTheory.T.torsionIso_of_linear_uniformisation_triple hLL hall.2.1 hall.2.2.1 hall.2.2.2.1 hall.2.2.2.2 E H M.W
    (IsLocalRing.maximalIdeal M.W) hadm M.t M.P
  have hTw := GlobalTheory.T.uniformisation_torsion_maps_compatible_in_level hLL M.W (IsLocalRing.maximalIdeal M.W) hadm M.P.D M.P.A M.t.G M.t.semi M.P.U C
  have hT' := fun (k : ℕ) (hk : 1 ≤ k) => hT C k hk
  choose f hfA hfB hfC hfD hfE hfF using hT'
  obtain ⟨e, he⟩ := GlobalTheory.LiePull.exists_pushEquiv M.cart (baseOver (Sp C)) (jFK (R := M.W) C)
    (by simp)

  have gA : ∀ (n : ℕ) (hn : 0 < n) a, M.P.ToA C n (I'.ev n a) (f n hn (I'.ev n a)) := fun n hn a => (hfA n hn _ _).2 rfl
  have gAdd : ∀ (n : ℕ) (hn : 0 < n) a b, f n hn (I'.ev n (a + b)) = f n hn (I'.ev n a) * f n hn (I'.ev n b) :=
    fun n hn a b => hfD n hn _ _ _ (I'.add n hn a b)
  have gLin : ∀ (n : ℕ) (hn : 0 < n) (c : 𝓞 E) a, f n hn (I'.ev n (c • a)) = f n hn (I'.ev n a) ≫ M.P.oA.act c :=
    fun n hn c a => hfE n hn c _ _ (I'.lin n hn c a)
  have gEq : ∀ (n : ℕ) (hn : 0 < n) a b, f n hn (I'.ev n a) = f n hn (I'.ev n b) ↔ ∃ e, a = b + n • e :=
    fun n hn a b => (hfC n hn _ _).trans (I'.ker n hn a b)
  have gZero : ∀ (n : ℕ) (hn : 0 < n), f n hn (I'.ev n 0) = 1 := by
    intro n hn
    have h0 := gAdd n hn 0 0
    rw [add_zero] at h0
    exact mul_left_cancel (h0.symm.trans (_root_.mul_one _).symm)
  have gNsmul : ∀ (n : ℕ) (hn : 0 < n) a (m : ℕ), f n hn (I'.ev n (m • a)) = f n hn (I'.ev n a) ^ m := by
    intro n hn a m
    induction m with
    | zero => rw [zero_smul, gZero, pow_zero]
    | succ m ih => rw [succ_nsmul, gAdd, ih, pow_succ]
  have gPow : ∀ (n : ℕ) (hn : 0 < n) a, f n hn (I'.ev n a) ^ n = 1 := by
    intro n hn a
    rw [← gNsmul, ← gZero n hn]
    exact (gEq n hn _ _).2 ⟨a, by rw [zero_add]⟩
  have gOnto : ∀ (n : ℕ) (hn : 0 < n) x, x ^ n = 1 → ∃ a, f n hn (I'.ev n a) = x := by
    intro n hn x hx
    obtain ⟨p, rfl⟩ := hfB n hn x hx
    obtain ⟨a, ha⟩ := I'.onto n hn p
    exact ⟨a, (hfC n hn _ _).2 ha⟩
  have gTower : ∀ (n m : ℕ) (hn : 0 < n) (hm : 0 < m) a,
      f (n * m) (Nat.mul_pos hn hm) (I'.ev (n * m) a) ^ m = f n hn (I'.ev n a) := by
    intro n m hn hm a
    obtain ⟨q, hqy, hqg, hqe⟩ := I'.tower n m hn hm a
    have h1 := (hTw n m (n * m) hn hm rfl q (I'.ev (n * m) a) (f (n * m) (Nat.mul_pos hn hm) (I'.ev (n * m) a))).2
      hqy hqg (gA (n * m) (Nat.mul_pos hn hm) a)
    rw [(hfA n hn q _).1 h1]
    exact (hfC n hn _ _).2 hqe
  have gWeil : ∀ (n : ℕ) (hn : 0 < n) a b, WeilIs M.P.A.A M.P.A.L n (f n hn (I'.ev n a)) (f n hn (I'.ev n b))
      (unitOn (I'.ζ n ^ D.EF a b)) := fun n hn a b => (hfF n hn _ _ _).1 (I'.isom n hn a b)

  have hL : ∀ y, (e.symm y).left ≫ M.φ = y.left := fun y => by rw [← he, e.apply_symm_apply]
  have hComm : ∀ y (c : 𝓞 E), e.symm (y ≫ M.P.oA.act c) = e.symm y ≫ o.oa.act c := by
    intro y c
    apply e.injective
    rw [e.apply_symm_apply]
    apply Over.OverMorphism.ext
    rw [he, Over.comp_left, Over.comp_left, Category.assoc, M.act c, ← Category.assoc, hL]
  obtain ⟨ev, hev⟩ : ∃ ev : ℕ → D.La → (baseOver (Sp C) ⟶ o.P.A),
      ∀ n a, ev n a = if hn : 0 < n then e.symm (f n hn (I'.ev n a)) else o.I.ev n a := ⟨_, fun _ _ => rfl⟩
  refine ⟨{ ζ := I'.ζ, ζ_prim := I'.ζ_prim, ζ_pow := I'.ζ_pow, ev := ev, add := ?_, lin := ?_, ker := ?_, onto := ?_, tower := ?_, isom := ?_ }, rfl, ?_⟩
  · intro n a b
    by_cases hn : 0 < n
    · rw [hev, hev, hev, dite_eq_left hn, dite_eq_left hn, dite_eq_left hn, gAdd, map_mul]
    · rw [hev, hev, hev, dite_eq_right hn, dite_eq_right hn, dite_eq_right hn]
      exact o.I.add n a b
  · intro n c a
    by_cases hn : 0 < n
    · rw [hev, hev, dite_eq_left hn, dite_eq_left hn, gLin, hComm]
    · rw [hev, hev, dite_eq_right hn, dite_eq_right hn]
      exact o.I.lin n c a
  · intro n hn a
    rw [hev, dite_eq_left hn, map_eq_one_iff _ e.symm.injective, ← gZero n hn, gEq]
    simp only [zero_add]
  · intro n hn x
    constructor
    · intro hx
      obtain ⟨a, ha⟩ := gOnto n hn (e x) (by rw [← map_pow, hx, map_one])
      exact ⟨a, by rw [hev, dite_eq_left hn, ha, e.symm_apply_apply]⟩
    · rintro ⟨a, rfl⟩
      rw [hev, dite_eq_left hn, ← map_pow, gPow, map_one]
  · intro n m hn hm a
    rw [hev, hev, dite_eq_left (Nat.mul_pos hn hm), dite_eq_left hn, ← map_pow, gTower n m hn hm]
  · intro n hn a b
    rw [hev, hev, dite_eq_left hn, dite_eq_left hn]
    exact weilIs_push M.P.A.isLB o.P.isLB M.cart M.lb (baseOver (Sp C)) (jFK (R := M.W) C)
      (by simp) n _ _ _ _ _ (hL _).symm (hL _).symm (gWeil n hn a b)
  · intro j hj x
    refine ⟨f j hj (I'.ev j x), ?_, gA j hj x⟩
    change _ = (ev j x).left ≫ M.φ
    rw [hev, dite_eq_left hj, hL]

end GlobalTheory.Relabel
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.ThetaPtMove GlobalTheory.ConstFam
open GlobalTheory.Ex.OneGen GlobalTheory.UT

noncomputable section
namespace GlobalTheory.Ex.OneGen

section Rig
variable {S S' : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {A : Over S'} [GrpObj A] [IsCommMonObj A]

theorem rigidification_map_on_values (m : CubeMap A G) {L₀ : LB G.left} {L₁ : LB A.left} (w : LB.Iso L₁ (L₀.pull m.F))
    {ρ₀ : LB.Gen (L₀.pull (eSec G))} {ρ₁ : LB.Gen (L₁.pull (eSec A))}
    (h : LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec A) (fun _ => 1)) ρ₁ (m.rigPull L₀ ρ₀)) :
    IsRigidificationPullbackCompatibleIso w m.e ρ₁ ρ₀ := by
  have H := (maps_iff w _ (fun _ => eSec G) _ ρ₁ ρ₀ m.e _ (rigPull_le m.F m.e m.e_comm L₀) (fun _ => rfl)).1 h
  intro Z r z J J' hJ hJ'
  have e : (r ≫ m.e) ≫ eSec G = (r ≫ eSec A) ≫ m.F := by rw [Category.assoc, Category.assoc, m.e_comm]
  refine (val_of (L := L₀) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) ρ₀ (r ≫ m.e) z J
    (fun _ => J ((r ≫ eSec A) ≫ m.F)) (fun _ => congrArg J e)).trans ?_
  refine (H Z r z (fun _ => J ((r ≫ eSec A) ≫ m.F)) (fun _ => J' (r ≫ eSec A)) (fun _ => hJ _) (fun _ => hJ' _)).trans ?_
  rw [Fintype.prod_unique, zpow_one]
  rfl

end Rig

section Move
variable {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {A : Over S'} [GrpObj A]
  {f : S' ⟶ S} {φ : A.left ⟶ G.left} (hp : IsGrpPullback A G f φ)
  {T : Over S'} {T₀ : Over S} (τ : T.left ⟶ T₀.left) (hτ : τ ≫ T₀.hom = T.hom ≫ f)
  {L₀ : LB G.left} {L₁ : LB A.left} {w : LB.Iso L₁ (L₀.pull φ)}

theorem mem_nonzeroLocus_iff_sv {a : ℤ} (s : LB.Sec (LPow A L₁ a T)) {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z)
    {J} (hJ : Good L₁ z J) : r z ∈ nonzeroLocus s ↔ IsUnit (VVRank.sv A s r z J) := by
  have hz := hJ.mem (fun _ : Fin 1 => (snd T A).left) r
  constructor
  · intro h
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 h
    have hz' : r z ∈ (LPow A L₁ a T).U k := (T ⊗ A).left.basicOpen_le _ hk
    have hu := (MulFinite.isUnit_gs r z _ hz' _).2 hk
    have e := sec_trans (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) s r z hz' hz
    exact isUnit_of_mul_isUnit_right (e ▸ hu :)
  · intro h
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨_, (MulFinite.isUnit_gs r z _ hz _).1 h⟩

theorem SecRel.mem_nonzeroLocus (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) {a : ℤ} {s : LB.Sec (LPow A L₁ a T)}
    {s₀ : LB.Sec (LPow G L₀ a T₀)} (h : SecRel hp τ hτ w s s₀) (y : (T ⊗ A).left)
    (hy : psi hp τ hτ y ∈ nonzeroLocus s₀) : y ∈ nonzeroLocus s := by
  obtain ⟨J, hJ⟩ := exists_good' hL₀ y
  obtain ⟨J', hJ'⟩ := exists_good' hL₁ y
  have q := (mem_nonzeroLocus_iff_sv s₀ (𝟙 _ ≫ psi hp τ hτ) y hJ).1 hy
  rw [h _ _ _ _ _ hJ hJ'] at q
  exact (mem_nonzeroLocus_iff_sv s (𝟙 _) y hJ').2 (isUnit_of_mul_isUnit_right q)

theorem SecRel.pullS {a : ℤ} {s : LB.Sec (LPow A L₁ a T)} {s₀ : LB.Sec (LPow G L₀ a T₀)} (h : SecRel hp τ hτ w s s₀)
    {T' : Over S'} {T₀' : Over S} (τ' : T'.left ⟶ T₀'.left) (hτ' : τ' ≫ T₀'.hom = T'.hom ≫ f) (ξ : T' ⟶ T)
    (ξ₀ : T₀' ⟶ T₀) (e : τ' ≫ ξ₀.left = ξ.left ≫ τ) :
    SecRel hp τ' hτ' w (VVRank.pullS A a ξ s) (VVRank.pullS G a ξ₀ s₀) := by
  intro Z r z J J' hJ hJ'
  have e' : psi hp τ' hτ' ≫ (ξ₀ ▷ G).left = (ξ ▷ A).left ≫ psi hp τ hτ := by
    refine psi_ext ?_ ?_
    · rw [Category.assoc, ← Over.comp_left, whiskerRight_fst, Over.comp_left, ← Category.assoc, psi_fst',
        Category.assoc, Category.assoc, psi_fst', e, ← Category.assoc, ← Category.assoc, ← Over.comp_left,
        ← Over.comp_left, whiskerRight_fst]
    · rw [Category.assoc, VVRank.whisker_snd_left, psi_snd', Category.assoc, psi_snd', ← Category.assoc,
        VVRank.whisker_snd_left]
  rw [VVRank.sv_pullS _ _ _ _ _ _ hJ, VVRank.sv_pullS _ _ _ _ _ _ hJ', Category.assoc, e', ← Category.assoc,
    h _ _ _ _ _ hJ hJ', Category.assoc, VVRank.whisker_snd_left]


include hp hτ in
theorem exists_pt_down (x₀ : T₀ ⟶ G) {n : ℕ} (hn : x₀ ^ n = 1) :
    ∃ x : T ⟶ A, τ ≫ x₀.left = x.left ≫ φ ∧ x ^ n = 1 := by
  have hc : (τ ≫ x₀.left) ≫ G.hom = T.hom ≫ f := by rw [Category.assoc, Over.w, hτ]
  let x : T ⟶ A := Over.homMk (hp.1.lift _ _ hc) (hp.1.lift_snd _ _ hc)
  have hx : τ ≫ x₀.left = x.left ≫ φ := (hp.1.lift_fst _ _ hc).symm
  refine ⟨x, hx, Over.OverMorphism.ext (hp.1.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))⟩
  rw [← over_pow hp τ hτ hx n, hn, over_one hp τ hτ]


include hp hτ in
theorem exists_pt_up [IsIso τ] (x : T ⟶ A) {n : ℕ} (hn : x ^ n = 1) :
    ∃ x₀ : T₀ ⟶ G, τ ≫ x₀.left = x.left ≫ φ ∧ x₀ ^ n = 1 := by
  let x₀ : T₀ ⟶ G := Over.homMk (inv τ ≫ x.left ≫ φ) (by
    rw [Category.assoc, Category.assoc, hp.1.w, Over.w_assoc, ← hτ, IsIso.inv_hom_id_assoc])
  have hx : τ ≫ x₀.left = x.left ≫ φ := IsIso.hom_inv_id_assoc _ _
  refine ⟨x₀, hx, Over.OverMorphism.ext ((cancel_epi τ).1 ?_)⟩
  rw [over_pow hp τ hτ hx n, hn, over_one hp τ hτ]

end Move

theorem theta_at_trait : HV → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ (χ : Sp V ⟶ S) (t' : SAB H (Sp V)) (_ : SABMap t' t χ) (_ : PELUnif (maximalIdeal V) t') (σ : LB.Sec (LPow t.G t.PP.L ((1 : ℕ) : ℤ) (Over.mk χ))), NZ t.G t.PP.L χ σ → IsGenSec t.G t.PP.L ((1 : ℕ) : ℤ) σ ∧ ∀ (ϖ : V), Irreducible ϖ → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → ∀ m : ℕ, Odd m → IsUnit (m : V) → 3 ≤ m → ∀ (x' : Sp F ⟶ S) (ξ : Over.mk x' ⟶ Over.mk χ), ξ.left = jFK (R := V) F ≫ jK V → (∀ x (c : F), ThG t.G t.PP.L t.PP.rig m (VVRank.pullS t.G _ ξ σ) x (fnOf c) → 0 ≤ v c) ∧ ∃ x, ∃ c : F, ThG t.G t.PP.L t.PP.rig m (VVRank.pullS t.G _ ξ σ) x (fnOf c) ∧ v c = 0 := by
  intro hV E _ _ _ H S t V _ _ _ hC χ t' m P σ hσ
  obtain ⟨hD, hA, hZ⟩ := hC
  obtain ⟨w, hw, hr, -⟩ := m.lin
  have hR : IsRigidificationPullbackCompatibleIso w χ t'.PP.rig t.PP.rig := by
    have q := rigidification_map_on_values m.cm w hr
    rw [m.base] at q
    exact q
  have hp := m.cart
  have hL₀ := t.PP.isLB
  have hL₁ := t'.PP.isLB
  let τ : (Over.mk (𝟙 (Sp V))).left ⟶ (Over.mk χ).left := 𝟙 (Sp V)
  haveI : IsIso τ := inferInstanceAs (IsIso (𝟙 (Sp V)))
  have hτ : τ ≫ (Over.mk χ).hom = (Over.mk (𝟙 (Sp V))).hom ≫ χ := rfl
  obtain ⟨σ', hs⟩ := exists_secRel hp τ hτ hw hL₀ hL₁ σ
  have hσ' : NZ t'.G t'.PP.L (𝟙 (Sp V)) σ' := by
    obtain ⟨g, hg, hg'⟩ := hσ
    obtain ⟨κ, -, h₂⟩ := ThetaPtUp.exists_psi_inv' hp τ hτ
    have e : psi hp τ hτ (κ g) = g := congrArg (fun q => q g) h₂
    refine ⟨κ g, ?_, SecRel.mem_nonzeroLocus hp τ hτ hL₀ hL₁ hs _ (e.symm ▸ hg')⟩
    have e' := congrArg (fun q => q (κ g)) (psi_fst' hp τ hτ)
    exact e'.symm.trans ((congrArg (fst (Over.mk χ) t.G).left e).trans hg)
  have key : ∀ (ϖ : V), Irreducible ϖ → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F]
      (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → IsGenSec t'.G t'.PP.L ((1 : ℕ) : ℤ) σ' ∧ ∀ n : ℕ, Odd n →
      IsUnit (n : V) → 3 ≤ n → ∀ (ξ : Over.mk (jFK (R := V) F ≫ jK V) ⟶ Over.mk (𝟙 (Sp V))),
      (∀ x (c : F), ThG t'.G t'.PP.L t'.PP.rig n (VVRank.pullS t'.G _ ξ σ') x (fnOf c) → 0 ≤ v c) ∧
      ∃ x, ∃ c : F, ThG t'.G t'.PP.L t'.PP.rig n (VVRank.pullS t'.G _ ξ σ') x (fnOf c) ∧ v c = 0 := by
    intro ϖ hϖ F _ _ _ v hv
    choose Q hQ using QForm.exists_QVal hϖ P.D
    have q := GlobalTheory.T.thetaConstants_integral_unit_of_closedFibre_nonvanishing hV V hA ϖ hϖ P.D Q hQ F v hv P.A t'.G t'.semi P.U
    dsimp only at q
    rw [P.bundle] at q
    exact q σ' hσ'
  refine ⟨?_, fun ϖ hϖ F _ _ _ v hv n h₁ h₂ h₃ x' ξ hξ => ?_⟩
  · obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
    obtain ⟨v, hv⟩ := GlobalTheory.adic_base_embeds_valuation_algebraic_closure.2 V ϖ hϖ
    exact ThetaPtUp.isGenSec_up hp τ hτ hw hL₀ hL₁ hs (key ϖ hϖ _ v hv).1
  · let ξ' : Over.mk (jFK (R := V) F ≫ jK V) ⟶ Over.mk (𝟙 (Sp V)) :=
      Over.homMk (jFK (R := V) F ≫ jK V) (Category.comp_id _)
    obtain ⟨k₁, x, c, k₂, k₃⟩ := (key ϖ hϖ F v hv).2 n h₁ h₂ h₃ ξ'
    let τ' : (Over.mk (jFK (R := V) F ≫ jK V)).left ⟶ (Over.mk x').left := 𝟙 (Sp F)
    haveI : IsIso τ' := inferInstanceAs (IsIso (𝟙 (Sp F)))
    have hτ' : τ' ≫ (Over.mk x').hom = (Over.mk (jFK (R := V) F ≫ jK V)).hom ≫ χ :=
      (Category.id_comp _).trans ((Over.w ξ).symm.trans (congrArg (· ≫ χ) hξ))
    have hs' := SecRel.pullS hp τ hτ hs τ' hτ' ξ' ξ
      ((Category.id_comp _).trans (hξ.trans (Category.comp_id _).symm))
    have hi : inv τ' = 𝟙 (Sp F) := IsIso.inv_eq_of_hom_inv_id (Category.id_comp _)
    refine ⟨fun y₀ d hd => ?_, ?_⟩
    · obtain ⟨y, hy, hn⟩ := exists_pt_down hp τ' hτ' y₀ hd.1
      exact k₁ y d (ThG.move hp τ' hτ' hw hL₀ hL₁ hR hy hn hs' hd)
    · obtain ⟨x₀, hx, hn⟩ := exists_pt_up hp τ' hτ' x k₂.1
      have q := ThG.up hp τ' hτ' hw hL₀ hL₁ hR hx hn hs' k₂
      rw [hi] at q
      exact ⟨x₀, c, q, k₃⟩

end GlobalTheory.Ex.OneGen
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TestFibre

theorem _root_.GlobalTheory.T.exists_integral_basis_combination_of_integral_family : Laws → Laws2 → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → ∀ (x : S.Gam → (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A)) (rig : LB.Gen (u.A.L.pull (eSec u.A.A))) (e : ∀ a, FrameAt u.A (x a)) (th : SecA u.A (PadicAlgCl p) 1) (s : S.J → SecA u.A (PadicAlgCl p) S.N), PtsOver u x → SecsOver u x rig e th s → ∀ (ϖ : u.V) (Q : u.D.toPre.X → ℤ) (v : AddValuation (PadicAlgCl p) (WithTop ℚ)) (lam : ℝ), Irreducible ϖ → ValOver ϖ (PadicAlgCl p) v → NormIs u l ϖ Q v lam → ∀ (w₀ : W0 u.U.toUnifPre) (th' : SecA u.A (PadicAlgCl p) 1) (ϑ : Fam u.D.toPre (PadicAlgCl p) 1) (c : PadicAlgCl p), NormW u.U.toUnifPre w₀ rig → u.U.ExpandsF (PadicAlgCl p) 1 w₀ th' ϑ → Prim u.D Q v ϑ → (∀ j, th.f j = liftFun u.A.A _ (cF u.V c) * th'.f j) → c ≠ 0 → ∀ Φ : Fam u.D.toPre (PadicAlgCl p) S.N, NuGe u.D Q (PadicAlgCl p) v S.N Φ 0 → ∃ (b : S.J → PadicAlgCl p) (σ : SecA u.A (PadicAlgCl p) S.N), (∀ j, ‖c * b j‖ ≤ 1) ∧ IsComb u.A s b σ ∧ u.U.ExpandsF (PadicAlgCl p) S.N w₀ σ Φ := by
  first | exact @GlobalTheory.TestFibre.exists_isComb_expands_of_nuGe_zero | exact GlobalTheory.TestFibre.exists_isComb_expands_of_nuGe_zero | (intros; apply GlobalTheory.TestFibre.exists_isComb_expands_of_nuGe_zero <;> assumption)
end
