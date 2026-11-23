module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.AlternatingMapSumSmulEqDetSmul
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfIsBaseChange
public import Mathlib.Algebra.Module.LocalizedModule.Away
public import Mathlib.Algebra.DualNumber
public import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle006
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Countable
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
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.CechDR

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CechDR

theorem mOm_two_eq_exteriorPowerMapOver {R A B : Type} [CommRing R] [CommRing A] [CommRing B] [Algebra R A]
    [Algebra R B] [Algebra A B] [IsScalarTower R A B] (x : Om R A 2) :
    (SemiHom.of_algHom (IsScalarTower.toAlgHom R A B)).mOm 2 x =
      GlobalTheory.exteriorPowerMapOver B 2 (KaehlerDifferential.map R R A B) x := by
  set h := SemiHom.of_algHom (IsScalarTower.toAlgHom R A B)
  let L : Om R A 2 →ₗ[A] Om R B 2 :=
    { toFun := h.mOm 2
      map_add' := map_add _
      map_smul' := fun a y ↦ by
        rw [h.mOm_smul, RingHom.id_apply]; exact algebraMap_smul B a _ }
  have e : L = GlobalTheory.exteriorPowerMapOver B 2 (KaehlerDifferential.map R R A B) := by
    apply exteriorPower.linearMap_ext
    ext1 v
    have hv : v = ![v 0, v 1] := by ext i; fin_cases i <;> rfl
    rw [LinearMap.compAlternatingMap_apply, LinearMap.compAlternatingMap_apply,
      GlobalTheory.exteriorPowerMapOver_ιMulti, hv, ← wedge_eq_ιMulti]
    change h.mOm 2 _ = _
    rw [h.mOm_wedge, h.oneFormMap_eq_kaehlerDifferential_map (fun _ ↦ rfl), h.oneFormMap_eq_kaehlerDifferential_map (fun _ ↦ rfl), wedge_eq_ιMulti]
    congr 1
    ext i; fin_cases i <;> rfl
  exact LinearMap.congr_fun e x

theorem twoForm_exists_pow_smul_eq_zero_of_isLocalization {R A B : Type} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B] (c : A)
    [IsLocalization.Away c B] (x : Om R A 2)
    (hx : (SemiHom.of_algHom (IsScalarTower.toAlgHom R A B)).mOm 2 x = 0) :
    ∃ n : ℕ, c ^ n • x = 0 := by
  haveI : Algebra.FormallyEtale A B := Algebra.FormallyEtale.of_isLocalization (Submonoid.powers c)
  have hb := GlobalTheory.TopForm.isBaseChange_exteriorPower
    (KaehlerDifferential.isBaseChange_of_formallyEtale R A B) 2
  haveI := (isLocalizedModule_iff_isBaseChange (Submonoid.powers c) B _).2 hb
  rw [mOm_two_eq_exteriorPowerMapOver, ← map_zero (GlobalTheory.exteriorPowerMapOver B 2 (KaehlerDifferential.map R R A B))] at hx
  obtain ⟨n, hn⟩ := IsLocalizedModule.Away.exists_of_eq (r := c) hx
  exact ⟨n, hn.trans (smul_zero _)⟩

theorem twoForm_exists_pow_smul_eq_zero_of_algHom {R A B : Type} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (f : A →ₐ[R] B) (c : A)
    (hc : @IsLocalization.Away A _ c B _ f.toRingHom.toAlgebra) (x : Om R A 2)
    (hx : (SemiHom.of_algHom f).mOm 2 x = 0) : ∃ n : ℕ, c ^ n • x = 0 := by
  letI : Algebra A B := f.toRingHom.toAlgebra
  haveI : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  exact twoForm_exists_pow_smul_eq_zero_of_isLocalization c x hx

theorem twoForm_sep_of_basis : ∀ {R' : Type} [CommRing R'] {X' : Scheme.{0}} (s' : X' ⟶ Sp R') {C' : Type} [Category.{0} C'], ∀ (G : C' ⥤ AffOp X'), (∀ T : AffOp X', ∃ (n : ℕ) (b : Fin n → (OAff s').obj T), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S : AffOp X') (u : T ⟶ S), IsUnit (mp (OAff s') u (b i)) → ∃ (t : C') (v : T ⟶ G.obj t) (w : G.obj t ⟶ S), v ≫ w = u) → (∀ (T : AffOp X') (η : Om R' ((OAff s').obj T) 2), (∀ t (u : T ⟶ G.obj t), pOm (OAff s') 2 u η = 0) → η = 0) := by
  intro R' _ X' s' C' _ G hcov T η hη
  obtain ⟨n, b, hb, hf⟩ := hcov T
  have key : ∀ i, ∃ m : ℕ, b i ^ m • η = 0 := by
    intro i
    let U : X'.affineOpens := T.unop
    let c : Γ(X', U.1) := b i
    let V : X'.affineOpens := ⟨X'.basicOpen c, U.2.basicOpen c⟩
    have hle : V ≤ U := X'.basicOpen_le c
    let u : T ⟶ Opposite.op V := (homOfLE hle).op
    have hu : IsUnit (mp (OAff s') u (b i)) := X'.toRingedSpace.isUnit_res_basicOpen c
    obtain ⟨t, v, w, hvw⟩ := hf i (Opposite.op V) u hu
    have h0 : pOm (OAff s') 2 u η = 0 := by rw [← hvw, pOm_comp, hη t v, map_zero]
    exact twoForm_exists_pow_smul_eq_zero_of_algHom (mp (OAff s') u) (b i)
      (U.2.isLocalization_basicOpen c) η h0
  choose m hm using key
  have hN : ∀ i, b i ^ (∑ j, m j) • η = 0 := fun i ↦ by
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (Finset.single_le_sum (fun j _ ↦ Nat.zero_le (m j))
      (Finset.mem_univ i))
    rw [hk, pow_add, mul_comm, mul_smul, hm i, smul_zero]
  have := Ideal.span_pow_eq_top _ hb (∑ j, m j)
  rw [← Set.range_comp, Ideal.eq_top_iff_one, Ideal.mem_span_range_iff_exists_fun] at this
  obtain ⟨r, hr⟩ := this
  rw [← one_smul ((OAff s').obj T) η, ← hr, Finset.sum_smul]
  exact Finset.sum_eq_zero fun i _ ↦ by
    rw [Function.comp_apply, mul_smul, hN i, smul_zero]

end GlobalTheory.CechDR
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential Opposite MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CechDR

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.InvForm

variable {R : Type} [CommRing R]

section Val

variable {B D : Type} [CommRing B] [Algebra R B] [CommRing D] [Algebra R D]

abbrev redHom (φ : B →ₐ[R] DualNumber D) : B →+* D :=
  (TrivSqZeroExt.fstHom R D D).toRingHom.comp φ.toRingHom

theorem redHom_algebraMap (φ : B →ₐ[R] DualNumber D) (r : R) :
    redHom φ (algebraMap R B r) = algebraMap R D r := by
  simp [redHom, TrivSqZeroExt.algebraMap_eq_inl']

def dVal (φ : B →ₐ[R] DualNumber D) : Ω[B⁄R] →ₗ[R] D :=
  letI : Algebra B D := (redHom φ).toAlgebra
  haveI : IsScalarTower R B D := IsScalarTower.of_algebraMap_eq fun r ↦ (redHom_algebraMap φ r).symm
  let d : Derivation R B D :=
    { toFun := fun b ↦ (φ b).snd
      map_add' := fun a b ↦ by simp
      map_smul' := fun r b ↦ by
        rw [map_smul, TrivSqZeroExt.snd_smul]
        rfl
      map_one_eq_zero' := by simp
      leibniz' := fun a b ↦ by
        change (φ (a * b)).snd = (φ a).fst * (φ b).snd + (φ b).fst * (φ a).snd
        rw [map_mul, TrivSqZeroExt.snd_mul]
        simp [MulOpposite.smul_eq_mul_unop]
        ring }
  d.liftKaehlerDifferential.restrictScalars R

theorem dVal_D (φ : B →ₐ[R] DualNumber D) (b : B) : dVal φ (KaehlerDifferential.D R B b) = (φ b).snd := by
  letI : Algebra B D := (redHom φ).toAlgebra
  haveI : IsScalarTower R B D := IsScalarTower.of_algebraMap_eq fun r ↦ (redHom_algebraMap φ r).symm
  exact Derivation.liftKaehlerDifferential_comp_D _ b

end Val

variable (A : Over (Sp R)) [GrpObj A]

def IsInv (w : GlobForm A.hom) : Prop :=
  ∀ (D : Type) [CommRing D] [Algebra R D] (U V : A.left.affineOpens)
    (φ : Sec A.hom U.1 →ₐ[R] DualNumber D) (ψ : Sec A.hom V.1 →ₐ[R] DualNumber D)
    (p q : Over.mk (spMap (algebraMap R (DualNumber D))) ⟶ A) (q₀ : Sp D ⟶ A.left),
    p.left = spMap (φ : Sec A.hom U.1 →+* DualNumber D) ≫ affPt A.hom U →
    q.left = spMap (algebraMap D (DualNumber D)) ≫ q₀ →
    (p * q).left = spMap (ψ : Sec A.hom V.1 →+* DualNumber D) ≫ affPt A.hom V →
    dVal φ (w.1 (op U)) = dVal ψ (w.1 (op V))

def InvForm : Submodule R (GlobForm A.hom) where
  carrier := {w | IsInv A w}
  add_mem' {w w'} hw hw' D _ _ U V φ ψ p q q₀ hp hq hpq := by
    change dVal φ (w.1 (op U) + w'.1 (op U)) = dVal ψ (w.1 (op V) + w'.1 (op V))
    rw [map_add (f := _), map_add (f := _), hw D U V φ ψ p q q₀ hp hq hpq, hw' D U V φ ψ p q q₀ hp hq hpq]
  zero_mem' D _ _ U V φ ψ p q q₀ _ _ _ := by
    change dVal φ 0 = dVal ψ 0
    rw [map_zero, map_zero]
  smul_mem' r w hw D _ _ U V φ ψ p q q₀ hp hq hpq := by
    change dVal φ (r • w.1 (op U)) = dVal ψ (r • w.1 (op V))
    rw [map_smul, map_smul, hw D U V φ ψ p q q₀ hp hq hpq]

end GlobalTheory.InvForm
end
end

section

open MeasureTheory ValuativeRel Matrix

noncomputable section
namespace GlobalTheory.FunObj
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {G : Grid (k := k)}

theorem isLocallyConstant_of_isTensor {ϖ : kˣ} {e : ℕ} {γ : List Edge} {T : G.Args → ℂ} (hT : G.IsTensor ϖ e γ T) :
    IsLocallyConstant T := by
  classical
  refine (IsLocallyConstant.iff_eventually_eq T).2 fun x => ?_
  have h : ∀ᶠ y in nhds x, ∀ b ∈ γ.toFinset, ∀ i j, (((ϖ ^ e)⁻¹ : kˣ) : k) * (y b i j - x b i j) ∈ 𝒪[k] := by
    refine (Filter.eventually_all_finset _).2 fun b _ => Filter.eventually_all.2 fun i =>
      Filter.eventually_all.2 fun j => ?_
    have hc : Continuous fun y : G.Args => (((ϖ ^ e)⁻¹ : kˣ) : k) * (y b i j - x b i j) :=
      continuous_const.mul (((continuous_apply b).matrix_elem i j).sub continuous_const)
    exact (Model.isOpen_int.preimage hc).mem_nhds (by simp)
  filter_upwards [h] with y hy
  rw [← hT.2.2 x (fun b => if b ∈ γ then y b - x b else 0) fun b => ?_]
  · exact hT.1 fun b hb => by simp [show b ∈ γ from hb]
  · split_ifs with hb
    · exact fun i => (mem_smul_lat _ _ _).2 (mem_stdLat.2 fun j => hy b (List.mem_toFinset.2 hb) i j)
    · exact zero_mem _

theorem continuous_stepPt {n n' : Type*} {c : ℕ} (x₀ : Matrix n n' k) :
    Continuous fun e : StepVar n c n' → k => stepPt x₀ e := by
  refine continuous_const.add (continuous_matrix fun r s => ?_)
  simp only [of_apply]
  split_ifs
  · exact continuous_apply _
  · exact continuous_const

theorem continuous_fill (hs : 1 ≤ G.s) (x : ColArgs G) (y : RowArgs G) : Continuous (fill hs x y) := by
  refine continuous_pi ?_
  rintro (⟨i, j⟩ | ⟨i, j⟩) <;> simp only [fill] <;> split_ifs
  · refine Continuous.matrix_transpose (Continuous.matrix_submatrix ?_ _ _)
    unfold downMap
    split_ifs with h
    · exact ((continuous_stepPt _).comp (continuous_apply (⟨j, h⟩ : Fin (G.m - 1)))).matrix_reindex _ _
    · exact continuous_const
    · exact continuous_const
  all_goals exact continuous_const

theorem continuous_phase (x : ColArgs G) : Continuous (phase x) := by
  have hp : ∀ (j : Fin (G.m - 1)) r s, Continuous fun e : Vars G => stepPt (x j) (e j) r s := fun j r s =>
    ((continuous_stepPt _).comp (continuous_apply j)).matrix_elem r s
  refine continuous_finsetSum _ fun j _ => (continuous_finsetSum _ fun i _ => hp j _ _).add ?_
  split_ifs
  · refine continuous_finsetSum _ fun r _ => Continuous.mul ?_ (hp j _ _)
    unfold rowVar
    split_ifs with h
    · refine continuous_finsetSum _ fun l _ => ?_
      split_ifs
      · exact hp ⟨_, h⟩ _ _
      · exact continuous_const
    · exact continuous_const
  · exact continuous_const


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem exists_fill_entry (hs : 1 ≤ G.s) (x : ColArgs G) (y : RowArgs G) (j : Fin (G.m - 1))
    (rs : StepVar (Fin (topRank G (j + 1))) (G.m - 2 - j) (Fin (topRank G j))) :
    ∃ a b c, ∀ e : Vars G, e j rs = fill hs x y e (.theta G.m j) a b - c := by
  refine ⟨frame (b := G.rank (G.m, j)) (by have := topRank_add hs j; have := j.2; omega) rs.1.2,
    frame (b := G.rank (G.m, j + 1)) (by have := topRank_add hs (j + 1); have := j.2; omega) rs.1.1,
    basePt _ (x j) rs.1.1 rs.1.2, fun e => ?_⟩
  rw [fill_theta, transpose_apply, downMap, dite_eq_left j.2]
  simp only [reindex_apply, submatrix_apply, Equiv.symm_apply_apply, stepPt, Matrix.add_apply, of_apply]
  rw [dite_eq_left rs.2, add_sub_cancel_left]

theorem exists_isCompact_of_mul_mem {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (A : GL m k) (B : GL n k) :
    ∃ K : Set (Matrix m n k), IsCompact K ∧ ∀ X, A.val * X * B.val ∈ matLat m (stdLat k n) → X ∈ K := by
  have hO : IsCompact (𝒪[k] : Set k) := isCompact_iff_compactSpace.2 (inferInstanceAs (CompactSpace 𝒪[k]))
  have hC : IsCompact (Set.univ.pi fun _ : m => Set.univ.pi fun _ : n => (𝒪[k] : Set k)) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hO
  have hc : Continuous fun M : Matrix m n k => (A⁻¹).val * M * (B⁻¹).val :=
    (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  refine ⟨_, hC.image hc, fun X hX => ⟨A.val * X * B.val, fun i _ j _ => mem_matLat_stdLat.1 hX i j, ?_⟩⟩
  show (A⁻¹).val * (A.val * X * B.val) * (B⁻¹).val = X
  rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one, ← Matrix.mul_assoc,
    Units.inv_mul, Matrix.one_mul]

theorem continuous_flatIntegrand (hs : 1 ≤ G.s) {ψ : AddChar k Circle} (hψ : Continuous ψ) {ϖ : kˣ} {e : ℕ}
    {γ : List Edge} {T : G.Args → ℂ} (hT : G.IsTensor ϖ e γ T) (keep : Bool) (g : G.VertexGroup)
    (x : ColArgs G) (y : RowArgs G) : Continuous (flatIntegrand hs ψ (moved G keep g T) x y) := by
  have hm : Continuous (G.moveArgs .one g) := continuous_pi fun b =>
    (continuous_const.matrix_mul (continuous_apply b)).matrix_mul continuous_const
  exact (continuous_const.mul (continuous_const.mul
    ((isLocallyConstant_of_isTensor hT).continuous.comp (hm.comp (continuous_fill hs x y))))).mul
    (continuous_subtype_val.comp (hψ.comp (continuous_phase x).neg))

theorem hasCompactSupport_flatIntegrand (hs : 1 ≤ G.s) (ψ : AddChar k Circle) {ϖ : kˣ} {e : ℕ}
    {T : G.Args → ℂ} (hT : G.IsTensor ϖ e (oppositePath G.m) T) (keep : Bool) (g : G.VertexGroup)
    (x : ColArgs G) (y : RowArgs G) : HasCompactSupport (flatIntegrand hs ψ (moved G keep g T) x y) := by
  obtain ⟨_, _⟩ := Model.secondCountable_and_t2_local_field (k := k)
  choose a b c h using exists_fill_entry hs x y
  choose K hK hK' using fun j : Fin (G.m - 1) => exists_isCompact_of_mul_mem
    (Assignment.one.read (g (Edge.theta G.m j).tgt))⁻¹ (Assignment.one.read (g (Edge.theta G.m j).src))
  refine HasCompactSupport.intro (K := Set.univ.pi fun j => Set.univ.pi fun rs =>
    (fun M => M (a j rs) (b j rs) - c j rs) '' K j) (isCompact_univ_pi fun j => isCompact_univ_pi fun rs =>
      (hK j).image ((continuous_id.matrix_elem _ _).sub continuous_const)) fun v hv => ?_
  have h0 : T (G.moveArgs .one g (fill hs x y v)) = 0 := by
    by_contra hne
    refine hv fun j _ rs _ => ⟨_, hK' j _ ?_, (h j rs v).symm⟩
    by_contra hn
    exact hne (hT.2.1 _ (.theta G.m j) (by have := j.2; simp [oppositePath]; omega) hn)
  simp [flatIntegrand, moved, Grid.pathAct, h0]

theorem flatIntegrable_of_isTensor [MeasurableSpace k] [BorelSpace k] (hs : 1 ≤ G.s) (ψ : AddChar k Circle)
    (ν : Measure k) [ν.IsAddHaarMeasure] {ϖ : kˣ} {e : ℕ} {T : G.Args → ℂ} (hψ : Continuous ψ)
    (hT : G.IsTensor ϖ e (oppositePath G.m) T) : FlatIntegrable hs ψ ν T := by
  classical
  obtain ⟨_, _⟩ := Model.secondCountable_and_t2_local_field (k := k)
  intro g x y
  unfold varsVol
  exact (continuous_flatIntegrand hs hψ hT true g x y).integrable_of_hasCompactSupport
    (hasCompactSupport_flatIntegrand hs ψ hT true g x y)

theorem flatIntegrable [MeasurableSpace k] [BorelSpace k] (hs : 1 ≤ G.s) (ψ : AddChar k Circle)
    (ν : Measure k) [ν.IsAddHaarMeasure] {ϖ : kˣ} {e : ℕ} {T : G.Args → ℂ} :
    IsUnif ϖ → Continuous ψ → G.IsTensor ϖ e (oppositePath G.m) T → FlatIntegrable hs ψ ν T :=
  fun _ hψ hT => flatIntegrable_of_isTensor hs ψ ν hψ hT

end GlobalTheory.FunObj
end
end

section

open ValuativeRel

noncomputable section

namespace GlobalTheory.UnfoldLoss

open GlobalTheory.SplitFlip GlobalTheory.FunObj

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def varLat (G : Grid k) (ϖ : kˣ) (n : ℕ) : AddSubgroup (Vars G) where
  carrier := {e | ∀ j r, valuation k (e j r) ≤ valuation k ((ϖ ^ n : kˣ) : k)}
  zero_mem' := fun j r => by
    show valuation k 0 ≤ _
    simp
  add_mem' := fun {a b} ha hb j r => (Valuation.map_add _ _ _).trans (max_le (ha j r) (hb j r))
  neg_mem' := fun {a} ha j r => by
    show valuation k (-(a j r)) ≤ _
    rw [Valuation.map_neg]
    exact ha j r

def varCount (G : Grid k) : ℕ :=
  ∑ j : Fin (G.m - 1), Nat.card (StepVar (Fin (topRank G (j + 1))) (G.m - 2 - j) (Fin (topRank G j)))

end GlobalTheory.UnfoldLoss
end
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.Katz

private theorem homog_one {R τ : Type} [CommRing R] : (1 : MvPowerSeries τ R).IsHomogeneous 0 := by
  classical
  intro γ h
  rw [coeff_one] at h
  by_cases h0 : γ = 0
  · simp [h0]
  · simp [h0] at h

private theorem homog_X {R τ : Type} [CommRing R] (t : τ) :
    (X t : MvPowerSeries τ R).IsHomogeneous 1 := by
  classical
  intro γ h
  rw [coeff_X] at h
  by_cases h0 : γ = Finsupp.single t 1
  · simp [h0, Finsupp.weight_single]
  · simp [h0] at h

private theorem homog_pow {R τ : Type} [CommRing R] {f : MvPowerSeries τ R}
    (hf : f.IsHomogeneous 1) (n : ℕ) : (f ^ n).IsHomogeneous n := by
  induction n with
  | zero => rw [pow_zero]; exact homog_one
  | succ n ih => rw [pow_succ]; exact IsHomogeneous.mul (f := f ^ n) (g := f) ih hf

private theorem homog_prod {R σ τ : Type} [CommRing R] {a : σ → MvPowerSeries τ R}
    (ha : ∀ i, (a i).IsHomogeneous 1) (n : σ → ℕ) (s : Finset σ) :
    (∏ i ∈ s, a i ^ n i).IsHomogeneous (∑ i ∈ s, n i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.sum_empty]; exact homog_one
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]; exact IsHomogeneous.mul (f := a i ^ n i) (p := n i) (homog_pow (ha i) (n i)) ih

theorem coeff_subst_linear_eq_zero_of_degree {R σ τ : Type} [CommRing R] [Finite σ]
    {a : σ → MvPowerSeries τ R} (ha : ∀ i, (a i).IsHomogeneous 1) {N : ℕ}
    {b : MvPowerSeries σ R} (hb : ∀ α : σ →₀ ℕ, α.degree = N → coeff α b = 0)
    {γ : τ →₀ ℕ} (hγ : γ.degree = N) : coeff γ (subst a b) = 0 := by
  have hs : HasSubst a := hasSubst_of_constantCoeff_zero fun i => by
    rw [← coeff_zero_eq_constantCoeff_apply]
    exact IsHomogeneous.coeff_eq_zero (f := a i) (p := 1) (ha i) (by simp)
  rw [coeff_subst hs]
  refine finsum_eq_zero_of_forall_eq_zero fun α => ?_
  by_cases h : α.degree = N
  · rw [hb α h, zero_smul]
  · have := IsHomogeneous.coeff_eq_zero (f := ∏ i ∈ α.support, a i ^ α i)
      (p := ∑ i ∈ α.support, α i) (homog_prod ha α α.support) (d := γ) (by
      rw [hγ]; exact fun h' => h h'.symm)
    rw [Finsupp.prod, this, smul_zero]

theorem coeff_cob1_addLaw_eq_zero_of_degree_eq : ∀ (R : Type) [CommRing R] (d N : ℕ)
    (b : MvPowerSeries (Fin d) R), (∀ α : Fin d →₀ ℕ, α.degree = N → coeff α b = 0) →
    ∀ γ : Fin d ⊕ Fin d →₀ ℕ, γ.degree = N → coeff γ (cob1 (addLaw R d) b) = 0 := by
  intro R _ d N b hb γ hγ
  unfold cob1 inL inR
  rw [map_sub, map_sub,
    coeff_subst_linear_eq_zero_of_degree (a := addLaw R d)
      (fun i => IsHomogeneous.add (p := 1) (homog_X (Sum.inl i)) (homog_X (Sum.inr i))) hb hγ,
    coeff_subst_linear_eq_zero_of_degree (fun i => homog_X _) hb hγ,
    coeff_subst_linear_eq_zero_of_degree (fun i => homog_X _) hb hγ]
  simp

end GlobalTheory.Katz
end

section

open MvPowerSeries

set_option autoImplicit false

namespace GlobalTheory.Katz

theorem coeff_at2_x2_x3_eq_zero_of_first_ne_zero {R : Type} [CommRing R] {d : ℕ} (c : MvPowerSeries (Fin d ⊕ Fin d) R)
    (a b e : Fin d →₀ ℕ) (ha : a ≠ 0) :
    coeff (Finsupp.sumElim a (Finsupp.sumElim b e)) (at2 c x2 x3) = 0 := by
  classical
  have hX : ∀ s, Sum.elim (x2 (R := R) (d := d)) x3 s
      = X (Sum.elim (fun i => Sum.inr (Sum.inl i)) (fun i => Sum.inr (Sum.inr i)) s) := by
    intro s; cases s <;> rfl
  have hs : HasSubst (Sum.elim (x2 (R := R) (d := d)) x3) :=
    hasSubst_of_constantCoeff_zero fun s => by rw [hX]; exact constantCoeff_X _
  obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
    by_contra h; push_neg at h; exact ha (Finsupp.ext h)
  unfold at2
  rw [coeff_subst hs]
  apply finsum_eq_zero_of_forall_eq_zero
  intro α
  have key : ∃ β : Fin d ⊕ (Fin d ⊕ Fin d) →₀ ℕ, β (Sum.inl i) = 0 ∧
      (α.prod fun s k => (Sum.elim (x2 (R := R) (d := d)) x3 s) ^ k) = monomial β 1 := by
    unfold Finsupp.prod
    refine Finset.prod_induction _ (fun f => ∃ β : Fin d ⊕ (Fin d ⊕ Fin d) →₀ ℕ,
      β (Sum.inl i) = 0 ∧ f = monomial β 1) ?_ ?_ ?_
    · rintro f g ⟨β, hβ, rfl⟩ ⟨γ, hγ, rfl⟩
      exact ⟨β + γ, by simp [hβ, hγ], by rw [monomial_mul_monomial, one_mul]⟩
    · exact ⟨0, rfl, (monomial_zero_one).symm⟩
    · intro s _
      refine ⟨Finsupp.single (Sum.elim (fun i => Sum.inr (Sum.inl i)) (fun i => Sum.inr (Sum.inr i)) s) (α s), ?_, ?_⟩
      · cases s <;> simp
      · dsimp only
        rw [hX, X_pow_eq]
  obtain ⟨β, hβ, hp⟩ := key
  rw [hp, coeff_monomial_ne, smul_zero]
  intro h
  apply hi
  have := congrArg (fun w => w (Sum.inl i)) h
  simpa [hβ] using this

end GlobalTheory.Katz
end
