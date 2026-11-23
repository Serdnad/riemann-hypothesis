module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle371
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle008
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.Definitions.Divisors.CechDeRhamCoefMapOneFormsRestrictAlongFunctor
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle341
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.WExactColim

abbrev altC {T : Type 1} [Category.{0} T] (X : CosimplicialObject T) (F : T ⥤ AddCommGrpCat.{1}) :
    CochainComplex AddCommGrpCat.{1} ℕ :=
  (AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{1}).obj (X ⋙ F)

abbrev altM {T : Type 1} [Category.{0} T] {X Y : CosimplicialObject T} (g : X ⟶ Y) (F : T ⥤ AddCommGrpCat.{1}) :
    altC X F ⟶ altC Y F :=
  (AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{1}).map (Functor.whiskerRight g F)

theorem altM_d {T : Type 1} [Category.{0} T] {X Y : CosimplicialObject T} (g : X ⟶ Y) (F : T ⥤ AddCommGrpCat.{1})
    (n m : ℕ) (w : (altC X F).X n) :
    (altC Y F).d n m ((altM g F).f n w) = (altM g F).f m ((altC X F).d n m w) := by
  have h := ConcreteCategory.congr_hom ((altM g F).comm n m) w
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h
  exact h

theorem altM_comp {T : Type 1} [Category.{0} T] {X Y Z : CosimplicialObject T} (g : X ⟶ Y) (h : Y ⟶ Z)
    (F : T ⥤ AddCommGrpCat.{1}) (n : ℕ) (w : (altC X F).X n) :
    (altM h F).f n ((altM g F).f n w) = (altM (g ≫ h) F).f n w := by
  show F.map (h.app _) (F.map (g.app _) w) = F.map (g.app _ ≫ h.app _) w
  rw [F.map_comp]
  rfl

theorem altM_comp' {T : Type 1} [Category.{0} T] {X Y Z : CosimplicialObject T} (g : X ⟶ Y) (h : Y ⟶ Z)
    (g' : X ⟶ Z) (e : g ≫ h = g') (F : T ⥤ AddCommGrpCat.{1}) (n : ℕ) (w : (altC X F).X n) :
    (altM h F).f n ((altM g F).f n w) = (altM g' F).f n w := by
  subst e
  exact altM_comp g h F n w

theorem exact_elt {T : Type 1} [Category.{0} T] (X : CosimplicialObject T) (F : T ⥤ AddCommGrpCat.{1}) (n : ℕ)
    (h : (altC X F).ExactAt (n + 1)) (w : (altC X F).X (n + 1)) (hw : (altC X F).d (n + 1) (n + 2) w = 0) :
    ∃ v : (altC X F).X n, (altC X F).d n (n + 1) v = w := by
  rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp), ShortComplex.ab_exact_iff] at h
  exact h w hw

theorem wExact_colimit : ∀ (T : Type 1) [Category.{0} T] (N : T ⥤ AddCommGrpCat.{1}), PreservesFilteredColimitsOfSize.{0, 0} N → ∀ (J : Type) [SmallCategory J] [IsFiltered J] (U : J ⥤ T) (X : J ⥤ CosimplicialObject T) (a : U ⋙ CosimplicialObject.const T ⟶ X) (cU : Cocone U) (cX : Cocone X) (b : (CosimplicialObject.const T).obj cU.pt ⟶ cX.pt), IsColimit cU → (∀ k : SimplexCategory, Nonempty (IsColimit (((evaluation SimplexCategory T).obj k).mapCocone cX))) → (∀ j, a.app j ≫ cX.ι.app j = (CosimplicialObject.const T).map (cU.ι.app j) ≫ b) → (∀ j, WExact N (a.app j)) → WExact N b := by
  intro T _ N hN J _ _ U X a cU cX b hU hX hab hW
  have fe := (GlobalTheory.T.preservesFilteredColimits_addCommGrp_iff_elements T N).1 hN
  have hNc : ∀ {A B C : T} (f : A ⟶ B) (g : B ⟶ C) (x : N.obj A), N.map (f ≫ g) x = N.map g (N.map f x) := by
    intros; simp
  have hab' : ∀ j (k : SimplexCategory), (a.app j).app k ≫ (cX.ι.app j).app k = cU.ι.app j ≫ b.app k := by
    intro j k
    exact NatTrans.congr_app (hab j) k
  have hnat : ∀ {j j' : J} (f : j ⟶ j') (k : SimplexCategory), (a.app j).app k ≫ (X.map f).app k = U.map f ≫ (a.app j').app k := by
    intro j j' f k
    exact (NatTrans.congr_app (a.naturality f) k).symm
  have hXι : ∀ {j j' : J} (f : j ⟶ j') (k : SimplexCategory), (X.map f).app k ≫ (cX.ι.app j').app k = (cX.ι.app j).app k := by
    intro j j' f k
    exact NatTrans.congr_app (cX.w f) k
  have feX : ∀ k : SimplexCategory, (∀ x : N.obj (cX.pt.obj k), ∃ j y, N.map ((cX.ι.app j).app k) y = x) ∧
      ∀ j (y : N.obj ((X.obj j).obj k)), N.map ((cX.ι.app j).app k) y = 0 → ∃ (j' : J) (f : j ⟶ j'), N.map ((X.map f).app k) y = 0 := by
    intro k
    exact fe J (X ⋙ (evaluation SimplexCategory T).obj k) _ (hX k).some
  have feU := fe J U cU hU
  refine ⟨?_, ?_, ?_⟩
  ·
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨j, y, rfl⟩ := feU.1 x
    have h0 : N.map ((cX.ι.app j).app (SimplexCategory.mk 0)) (N.map ((a.app j).app (SimplexCategory.mk 0)) y) = 0 := by
      rw [← hNc, hab', hNc]; simpa using hx
    obtain ⟨k, f, hf⟩ := (feX _).2 j _ h0
    rw [← hNc, hnat, hNc] at hf
    have hk := (hW k).1 (hf.trans (map_zero _).symm)
    rw [← cU.w f, hNc]
    simp only [Functor.comp_obj] at hk
    rw [hk, map_zero]
  ·
    intro y hy
    obtain ⟨j, y', rfl⟩ := (feX _).1 y
    have hδ : ∀ {Y Z : CosimplicialObject T} (g : Y ⟶ Z) (i : Fin 2),
        Y.δ (n := 0) i ≫ g.app (SimplexCategory.mk 1) = g.app (SimplexCategory.mk 0) ≫ Z.δ (n := 0) i :=
      fun g i => g.naturality _
    set d' := N.map ((X.obj j).δ (n := 0) 0) y' - N.map ((X.obj j).δ (n := 0) 1) y' with hd'
    have h1 : N.map ((cX.ι.app j).app (SimplexCategory.mk 1)) d' = 0 := by
      rw [hd', map_sub, ← hNc, ← hNc, hδ, hδ, hNc, hNc]
      exact sub_eq_zero.mpr hy
    obtain ⟨k, f, hf⟩ := (feX _).2 j _ h1
    have h2 : N.map ((X.obj k).δ (n := 0) 0) (N.map ((X.map f).app (SimplexCategory.mk 0)) y') =
        N.map ((X.obj k).δ (n := 0) 1) (N.map ((X.map f).app (SimplexCategory.mk 0)) y') := by
      rw [← sub_eq_zero, ← hNc, ← hNc, ← hδ, ← hδ, hNc, hNc, ← map_sub]
      exact hf
    obtain ⟨x, hx⟩ := (hW k).2.1 _ h2
    refine ⟨N.map (cU.ι.app k) x, ?_⟩
    rw [← hNc, ← hab', hNc]
    simp only [Functor.comp_obj] at hx
    rw [hx, ← hNc, hXι]
  · intro n
    rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp), ShortComplex.ab_exact_iff]
    intro z hz
    obtain ⟨j, z', rfl⟩ := (feX _).1 z
    have h1 : (altM (cX.ι.app j) N).f (n + 2) ((altC (X.obj j) N).d (n + 1) (n + 2) z') = 0 := by
      exact (altM_d (cX.ι.app j) N (n + 1) (n + 2) z').symm.trans hz
    obtain ⟨k, f, hf⟩ := (feX _).2 j _ h1
    have h2 : (altC (X.obj k) N).d (n + 1) (n + 2) ((altM (X.map f) N).f (n + 1) z') = 0 := by
      exact (altM_d (X.map f) N (n + 1) (n + 2) z').trans hf
    obtain ⟨v, hv⟩ := exact_elt _ N n ((hW k).2.2 n) _ h2
    refine ⟨(altM (cX.ι.app k) N).f n v, ?_⟩
    show (altC cX.pt N).d n (n + 1) ((altM (cX.ι.app k) N).f n v) = (altM (cX.ι.app j) N).f (n + 1) z'
    rw [altM_d, hv]
    exact altM_comp' (X.map f) (cX.ι.app k) (cX.ι.app j) (cX.w f) N (n + 1) z'

end GlobalTheory.EtC.WExactColim
end

section

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory

open KaehlerDifferential in
private theorem linearIndependent_laurentMonomials {k F ι : Type} [Field k] [Field F] [Algebra k F]
    [Fintype ι] (y : ι → F) (hy : AlgebraicIndependent k y) (hy0 : ∀ i, y i ≠ 0) :
    LinearIndependent k (fun n : ι → ℤ => ∏ i, y i ^ n i) := by
  classical
  rw [linearIndependent_iff']
  intro s g hg n hn
  set B : ℤ := ∑ m ∈ s, ∑ i, |m i| with hBdef
  have hB : ∀ m ∈ s, ∀ i, 0 ≤ m i + B := by
    intro m hm i
    have h1 : |m i| ≤ ∑ i, |m i| :=
      Finset.single_le_sum (f := fun i => |m i|) (fun i _ => abs_nonneg _) (Finset.mem_univ i)
    have h2 : ∑ i, |m i| ≤ B :=
      Finset.single_le_sum (f := fun m : ι → ℤ => ∑ i, |m i|)
        (fun m _ => Finset.sum_nonneg fun i _ => abs_nonneg _) hm
    linarith [neg_abs_le (m i)]
  let e : (ι → ℤ) → (ι →₀ ℕ) := fun m => Finsupp.equivFunOnFinite.symm (fun i => (m i + B).toNat)
  have he : Set.InjOn e s := by
    intro m hm m' hm' h
    funext i
    have h' := congrArg (fun f : ι →₀ ℕ => f i) h
    simp only [e, Finsupp.coe_equivFunOnFinite_symm] at h'
    have := Int.toNat_of_nonneg (hB m hm i)
    have := Int.toNat_of_nonneg (hB m' hm' i)
    omega
  set P : F := ∏ i, y i ^ B with hPdef
  have hkey : ∀ m ∈ s, MvPolynomial.aeval y (MvPolynomial.monomial (e m) (1 : k)) =
      P * ∏ i, y i ^ m i := by
    intro m hm
    rw [MvPolynomial.aeval_monomial, map_one, one_mul,
      Finsupp.prod_fintype _ _ (fun i => pow_zero _), hPdef, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← zpow_add₀ (hy0 i), ← zpow_natCast]
    congr 1
    simp only [e, Finsupp.coe_equivFunOnFinite_symm]
    rw [Int.toNat_of_nonneg (hB m hm i)]
    ring
  have hw : LinearIndependent k (fun a : ι →₀ ℕ => MvPolynomial.aeval y (MvPolynomial.monomial a (1 : k))) := by
    have := (MvPolynomial.basisMonomials ι k).linearIndependent.map'
      (MvPolynomial.aeval y).toLinearMap (LinearMap.ker_eq_bot.mpr hy)
    simpa only [MvPolynomial.coe_basisMonomials, Function.comp_def, AlgHom.toLinearMap_apply] using this
  have hws : LinearIndependent k
      (fun m : s => MvPolynomial.aeval y (MvPolynomial.monomial (e m) (1 : k))) :=
    hw.comp (fun m : s => e m) (fun a b h => Subtype.ext (he a.2 b.2 h))
  rw [Fintype.linearIndependent_iff] at hws
  refine hws (fun m => g m) ?_ ⟨n, hn⟩
  calc ∑ m : s, g m • MvPolynomial.aeval y (MvPolynomial.monomial (e m) (1 : k))
      = ∑ m : s, P * (g m • ∏ i, y i ^ (m : ι → ℤ) i) := by
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [hkey m m.2, mul_smul_comm]
    _ = P * ∑ m ∈ s, g m • ∏ i, y i ^ m i := by
        rw [← Finset.mul_sum, Finset.sum_coe_sort s (fun m => g m • ∏ i, y i ^ m i)]
    _ = 0 := by rw [hg, mul_zero]

open KaehlerDifferential in
private theorem prod_zpow_eq_prod_div_zpow_of_sum_eq_zero {F : Type} [Field F] {d : ℕ} (x : Fin (d + 1) → F)
    (hx : ∀ i, x i ≠ 0) (m : Fin (d + 1) → ℤ) (hm : ∑ j, m j = 0) :
    ∏ j, x j ^ m j = ∏ i : Fin d, (x i.succ / x 0) ^ m i.succ := by
  have h0 : m 0 = -∑ i : Fin d, m i.succ := by
    rw [Fin.sum_univ_succ] at hm
    linarith
  have hpow : ∀ s : Finset (Fin d), ∏ i ∈ s, x 0 ^ m i.succ = x 0 ^ ∑ i ∈ s, m i.succ := by
    classical
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add₀ (hx 0)]
  rw [Fin.prod_univ_succ, h0]
  simp_rw [div_zpow]
  rw [Finset.prod_div_distrib, hpow, zpow_neg, div_eq_mul_inv, mul_comm]


open KaehlerDifferential in
theorem _root_.GlobalTheory.exists_isRes : ∀ (k : Type) [Field k] (F : Type) [Field F]
    [Algebra k F] (d : ℕ) (x : Fin (d + 1) → F),
    _root_.GlobalTheory.PD.IsPd k x → ∃ ρ : F →ₗ[k] k, _root_.GlobalTheory.PD.IsRes k x ρ := by
  intro k _ F _ _ d x hx
  classical
  let v : {m : Fin (d + 1) → ℤ // ∑ j, m j = 0} → F := fun m => ∏ j, x j ^ m.1 j
  have hv : LinearIndependent k v := by
    have hL := linearIndependent_laurentMonomials (k := k) (fun i : Fin d => x i.succ / x 0)
      hx.indep
      (fun i => div_ne_zero (hx.ne _) (hx.ne 0))
    have hinj : Function.Injective
        (fun m : {m : Fin (d + 1) → ℤ // ∑ j, m j = 0} => fun i : Fin d => m.1 i.succ) := by
      intro a b h
      apply Subtype.ext
      have hs : ∀ i : Fin d, a.1 i.succ = b.1 i.succ := fun i => congrFun h i
      have ha := a.2
      have hb := b.2
      rw [Fin.sum_univ_succ] at ha hb
      have hsum : ∑ i : Fin d, a.1 i.succ = ∑ i : Fin d, b.1 i.succ :=
        Finset.sum_congr rfl fun i _ => hs i
      funext j
      refine Fin.cases ?_ (fun i => hs i) j
      linarith
    have := hL.comp _ hinj
    convert this using 1
    funext m
    exact prod_zpow_eq_prod_div_zpow_of_sum_eq_zero x hx.ne m.1 m.2
  let z₀ : {m : Fin (d + 1) → ℤ // ∑ j, m j = 0} := ⟨0, by simp⟩
  have h1 : v z₀ = 1 := by simp [v, z₀]
  have hnot := hv.notMem_span_image (s := {z | z ≠ z₀}) (x := z₀) (by simp)
  rw [h1] at hnot
  obtain ⟨f, hf1, hf⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hnot inferInstance
  refine ⟨(f 1)⁻¹ • f, ?_⟩
  delta _root_.GlobalTheory.PD.IsRes
  refine ⟨?_, ?_⟩
  · rw [LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hf1]
  · intro m hm hm0
    have hmem : ∏ j, x j ^ m j ∈ Submodule.span k (v '' {z | z ≠ z₀}) :=
      Submodule.subset_span ⟨⟨m, hm⟩, fun h => hm0 (congrArg Subtype.val h), rfl⟩
    have hzero : f (∏ j, x j ^ m j) = 0 := by
      exact LinearMap.mem_ker.mp ((LinearMap.le_ker_iff_map.mpr hf) hmem)
    rw [LinearMap.smul_apply, hzero, smul_zero]

end GlobalTheory
end

section

set_option autoImplicit false

noncomputable section

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory.PD

theorem isTop_exists_and_eq (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F]
    [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F) :
    IsFinCover k K x → (∃ τ : DR k K →ₗ[K] K, IsTop k K x τ) ∧
      ∀ τ : DR k K →ₗ[K] K, IsTop k K x τ → ∀ y ∈ ⋀[K]^d Ω[K⁄k], y = τ y • vol0 k K x := by
  intro h
  refine ⟨h.exists_isTop, fun τ hτ y hy => ?_⟩
  obtain ⟨b, hb⟩ := h.exists_basis
  set u : Fin d → K := fun j => (algebraMap F K (x j.succ / x 0))⁻¹
  have hu : ∀ j, u j ≠ 0 := fun j =>
    inv_ne_zero ((map_ne_zero _).2 (div_ne_zero (h.pd.ne _) (h.pd.ne 0)))
  have hp : (∏ j, u j) ≠ 0 := Finset.prod_ne_zero_iff.2 fun j _ => hu j
  have hv : vol0 k K x = (∏ j, u j) • ExteriorAlgebra.ιMulti K d b := by
    rw [← AlternatingMap.map_smul_univ]
    simp only [vol0, hb, u]

  have key : ∀ c : K, c • vol0 k K x = τ (c • vol0 k K x) • vol0 k K x := by
    intro c
    rw [map_smul, hτ.1, smul_eq_mul, mul_one]
  rw [← ExteriorAlgebra.ιMulti_span_fixedDegree] at hy
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨m, rfl⟩ := hz
    have e : ExteriorAlgebra.ιMulti K d m = (b.det m * (∏ j, u j)⁻¹) • vol0 k K x := by
      rw [hv, smul_smul, mul_assoc, inv_mul_cancel₀ hp, mul_one]
      rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff K]
      intro φ
      have h2 := congrArg (fun g => g m)
        (AlternatingMap.eq_smul_basis_det b (φ.compAlternatingMap (ExteriorAlgebra.ιMulti K d)))
      simp only [LinearMap.compAlternatingMap_apply, AlternatingMap.smul_apply, smul_eq_mul] at h2
      rw [map_sub, map_smul, h2, smul_eq_mul, mul_comm, sub_self]
    rw [e]
    exact key _
  | zero => simp
  | add a c _ _ ha hc => rw [map_add (f := _), add_smul, ← ha, ← hc]
  | smul r a _ ha => rw [map_smul, smul_eq_mul, mul_smul, ← ha]

end GlobalTheory.PD
end
end

section

set_option autoImplicit false

noncomputable section

open KaehlerDifferential GlobalTheory.CechDR

namespace GlobalTheory.PD

section Alt

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

theorem altMap_add_smul_self {n : ℕ} (f : M [⋀^Fin n]→ₗ[R] N) (v : Fin n → M) (k : Fin n) (c : Fin n → R)
    (hc : c k = 0) : f (fun j => v j + c j • v k) = f v := by
  classical
  have key : ∀ s : Finset (Fin n), f (fun j => v j + if j ∈ s then c j • v k else 0) = f v := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      by_cases hak : a = k
      · subst hak
        have e : (fun j => v j + if j ∈ insert a s then c j • v a else 0) =
            (fun j => v j + if j ∈ s then c j • v a else 0) := by
          funext j
          by_cases hj : j = a
          · subst hj; simp [hc]
          · simp [Finset.mem_insert, hj]
        rw [e, ih]
      · set g : Fin n → M := fun j => v j + if j ∈ s then c j • v k else 0 with hg
        have e1 : (fun j => v j + if j ∈ insert a s then c j • v k else 0) = Function.update g a (v a + c a • v k) := by
          funext j
          by_cases hj : j = a
          · subst hj; simp
          · simp [hg, Function.update_of_ne hj, Finset.mem_insert, hj]
        have e2 : Function.update g a (v a) = g := by
          funext j
          by_cases hj : j = a
          · subst hj; simp [hg, ha]
          · simp [Function.update_of_ne hj]
        have e3 : f (Function.update g a (v k)) = 0 := by
          refine f.map_eq_zero_of_eq _ (i := a) (j := k) ?_ hak
          simp [Function.update_of_ne (Ne.symm hak), hg, hc]
        rw [e1, f.map_update_add, f.map_update_smul, e2, ih, e3, smul_zero, add_zero]
  simpa using key Finset.univ

theorem exists_perm_succ {d : ℕ} (τ : Fin d → Fin (d + 1)) (hinj : Function.Injective τ) (hne : ∀ j, τ j ≠ 0) :
    ∃ π : Equiv.Perm (Fin d), τ = Fin.succ ∘ π := by
  let p : Fin d → Fin d := fun j => (τ j).pred (hne j)
  have hp : Function.Injective p := by
    intro a b hab
    apply hinj
    simpa [p] using congrArg Fin.succ hab
  refine ⟨Equiv.ofBijective p (Finite.injective_iff_bijective.1 hp), ?_⟩
  funext j
  simp [p]

theorem altMap_sub_succAbove {d : ℕ} (f : M [⋀^Fin d]→ₗ[R] N) (θ : Fin (d + 1) → M) (h0 : θ 0 = 0)
    (i : Fin (d + 1)) : ∃ ε : ℤˣ, f (fun j => θ (i.succAbove j) - θ i) = ε • f (fun j => θ j.succ) := by
  classical
  cases i using Fin.cases with
  | zero => exact ⟨1, by simp [h0]⟩
  | succ i' =>
    have hd : 0 < d := Nat.lt_of_le_of_lt (Nat.zero_le _) i'.isLt
    set i : Fin (d + 1) := i'.succ with hi
    set j0 : Fin d := ⟨0, hd⟩ with hj0
    have hσ0 : i.succAbove j0 = 0 := by
      rw [Fin.succAbove_of_castSucc_lt]
      · rfl
      · rw [Fin.lt_def]; simp [hi, hj0]
    set w : Fin d → M := fun j => θ (i.succAbove j) - θ i with hw
    set c : Fin d → R := fun j => if j = j0 then 0 else -1 with hc
    have k1 := altMap_add_smul_self f w j0 c (by simp [hc])
    have e1 : (fun j => w j + c j • w j0) = Function.update (θ ∘ i.succAbove) j0 ((-1 : R) • θ i) := by
      funext j
      by_cases hj : j = j0
      · subst hj; simp [hw, hc, hσ0, h0]
      · simp [hw, hc, hj, hσ0, h0, Function.update_of_ne hj]
    set τ : Fin d → Fin (d + 1) := Function.update i.succAbove j0 i with hτ
    have e2 : Function.update (θ ∘ i.succAbove) j0 (θ i) = θ ∘ τ := by
      funext j
      by_cases hj : j = j0
      · subst hj; simp [hτ]
      · simp [hτ, Function.update_of_ne hj]
    have hτinj : Function.Injective τ := by
      intro a b hab
      by_cases ha : a = j0 <;> by_cases hb : b = j0
      · rw [ha, hb]
      · simp [hτ, ha, Function.update_of_ne hb] at hab
      · simp [hτ, hb, Function.update_of_ne ha] at hab
      · simp only [hτ, Function.update_of_ne ha, Function.update_of_ne hb] at hab
        exact Fin.succAbove_right_injective hab
    have hτne : ∀ j, τ j ≠ 0 := by
      intro j
      by_cases hj : j = j0
      · subst hj; simp [hτ, hi]
      · rw [hτ, Function.update_of_ne hj, ← hσ0]
        exact fun h => hj (Fin.succAbove_right_injective h)
    obtain ⟨π, hπ⟩ := exists_perm_succ τ hτinj hτne
    refine ⟨-Equiv.Perm.sign π, ?_⟩
    rw [← k1, e1, f.map_update_smul, e2, hπ]
    have e3 : θ ∘ (Fin.succ ∘ ⇑π) = (fun j => θ j.succ) ∘ ⇑π := rfl
    rw [e3, f.map_perm, Units.neg_smul, neg_one_smul]

end Alt

theorem volume_chart_change (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F]
    [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F) (h : IsFinCover k K x)
    (i : Fin (d + 1)) : ∃ ε : ℤˣ, (ExteriorAlgebra.ιMulti K d fun j => D k K (algebraMap F K (x (i.succAbove j) / x i))) =
      ε • algebraMap F K (∏ j, x j / x i) • vol0 k K x := by
  have hx := h.pd.ne
  set y : Fin (d + 1) → K := fun a => algebraMap F K (x a / x 0) with hy
  have hy0 : ∀ a, y a ≠ 0 := fun a => (map_ne_zero _).2 (div_ne_zero (hx a) (hx 0))
  set θ : Fin (d + 1) → Ω[K⁄k] := fun a => (y a)⁻¹ • D k K (y a) with hθ
  have hθ0 : θ 0 = 0 := by
    show (algebraMap F K (x 0 / x 0))⁻¹ • D k K (algebraMap F K (x 0 / x 0)) = 0
    rw [div_self (hx 0), map_one, Derivation.map_one_eq_zero, smul_zero]
  have hD : ∀ a, D k K (algebraMap F K (x a / x i)) = algebraMap F K (x a / x i) • (θ a - θ i) := by
    intro a
    have e : algebraMap F K (x a / x i) = y a / y i := by
      simp only [hy, ← map_div₀]
      congr 1
      field_simp [hx 0, hx i]
    have ha := hy0 a
    have hi := hy0 i
    rw [e, Derivation.leibniz_div, hθ]
    simp only [smul_sub, smul_smul]
    congr 2 <;> field_simp
  obtain ⟨ε, hε⟩ := altMap_sub_succAbove (ExteriorAlgebra.ιMulti K d) θ hθ0 i
  refine ⟨ε, ?_⟩
  have hprod : algebraMap F K (∏ j, x j / x i) = ∏ j, algebraMap F K (x (i.succAbove j) / x i) := by
    rw [Fin.prod_univ_succAbove _ i, div_self (hx i), one_mul, map_prod]
  simp only [hD]
  rw [AlternatingMap.map_smul_univ, hε, hprod]
  rw [smul_comm]
  rfl

end GlobalTheory.PD
end
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR

theorem _root_.GlobalTheory.T.comma_second_order_cocycle_lift : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), Function.Surjective (CoefMap.restrict F G).pull2 → (∀ κ : A2 F, (∀ ⦃T T' T'' T''' : C⦄ (φ : T ⟶ T') (ψ : T' ⟶ T'') (χ : T'' ⟶ T'''), p1 F χ (κ T T' T'' φ ψ) + κ T T'' T''' (φ ≫ ψ) χ = κ T T' T''' φ (ψ ≫ χ) + κ T' T'' T''' ψ χ) → ∀ β' : ∀ t t', (t ⟶ t') → Ω[F.obj (G.obj t')⁄R], (∀ ⦃t t' t'' : C'⦄ (a : t ⟶ t') (b : t' ⟶ t''), κ _ _ _ (G.map a) (G.map b) = p1 F (G.map b) (β' t t' a) - β' t t'' (a ≫ b) + β' t' t'' b) → ∃ β : A1 F, ∀ ⦃T T' T'' : C⦄ (φ : T ⟶ T') (ψ : T' ⟶ T''), κ T T' T'' φ ψ = p1 F ψ (β T T' φ) - β T T'' (φ ≫ ψ) + β T' T'' ψ) → (∀ β' : ∀ t t', (t ⟶ t') → Ω[F.obj (G.obj t')⁄R], (∀ ⦃t t' t'' : C'⦄ (a : t ⟶ t') (b : t' ⟶ t''), β' t t'' (a ≫ b) = p1 F (G.map b) (β' t t' a) + β' t' t'' b) → ∃ β : A1 F, (∀ ⦃T T' T'' : C⦄ (φ : T ⟶ T') (ψ : T' ⟶ T''), β T T'' (φ ≫ ψ) = p1 F ψ (β T T' φ) + β T' T'' ψ) ∧ ∃ θ' : ∀ t, Ω[F.obj (G.obj t)⁄R], ∀ ⦃t t' : C'⦄ (a : t ⟶ t'), β _ _ (G.map a) - β' t t' a = θ' t' - p1 F (G.map a) (θ' t)) → (∀ κ : W1 F 2, (∀ ⦃T T' T'' : C⦄ (φ : T ⟶ T') (ψ : T' ⟶ T''), κ T T'' (φ ≫ ψ) = pOm F 2 ψ (κ T T' φ) + κ T' T'' ψ) → ∀ θ' : ∀ t, Om R (F.obj (G.obj t)) 2, (∀ ⦃t t' : C'⦄ (a : t ⟶ t'), κ _ _ (G.map a) = θ' t' - pOm F 2 (G.map a) (θ' t)) → ∃ θ : W0 F 2, ∀ ⦃T T' : C⦄ (φ : T ⟶ T'), κ T T' φ = θ T' - pOm F 2 φ (θ T)) → (∀ η' : ∀ t, Om R (F.obj (G.obj t)) 2, (∀ ⦃t t' : C'⦄ (a : t ⟶ t'), η' t' = pOm F 2 (G.map a) (η' t)) → ∃ η : W0 F 2, (∀ ⦃T T' : C⦄ (φ : T ⟶ T'), η T' = pOm F 2 φ (η T)) ∧ ∀ t, η (G.obj t) = η' t) → (∀ (T : C) (x : Om R (F.obj T) 3), (∀ t (u : T ⟶ G.obj t), pOm F 3 u x = 0) → x = 0) → Function.Surjective (pullHyp2 (CoefMap.restrict F G)) := by
  first | exact @GlobalTheory.CechDR.pullHyp2_restrict_surjective | exact GlobalTheory.CechDR.pullHyp2_restrict_surjective | (intros; apply GlobalTheory.CechDR.pullHyp2_restrict_surjective <;> assumption)
end
