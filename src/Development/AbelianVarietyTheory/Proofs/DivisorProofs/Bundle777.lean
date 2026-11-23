module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleCocycleFirstChernClassTateTwist
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChosenInjectiveResolutionEtaleSheafSectionsExactStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle463
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle462
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenOfIso
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle102
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
public import CompanionTheory.ThickeningEstimates.LieGroupReduction.MetaplecticRepresentation.RealMetaplecticRepresentationHolds
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle711
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC
namespace KumNat
open ClsSpec

theorem sec_subsingleton {R : Type} [CommRing R] (F : Shv R) (U : Scheme.{0}) {s : ℤ} (hs : s < 0) :
    Subsingleton (Sec ((res R F).X s) U) := (GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness R F U).2.2.2 s hs

theorem ev_sub' {R : Type} [CommRing R] {E : Spc} {I : Cx R} {n : ℤ} (α β : Cochain ((chains R).obj E) I n) (p s h U x) :
    ev (α - β) p s h U x = ev α p s h U x - ev β p s h U x := ((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R).1 α β p s h U x).2.1

variable {q : ℕ}

theorem kum_unique [NeZero q] {X : Scheme.{0}} (hX : IsUnit (q : Γ(X, ⊤))) (u : (Γ(X, ⊤))ˣ)
    {γ γ' : Cochain ((chains (ZMod q)).obj (sch.obj X)) (res _ (tw q 1)) 1}
    (h₁ : ∀ (U : Scheme.{0}) (x : U ⟶ X), ev γ 1 0 (by simp) U x = 0)
    (h₂ : ∀ (U : Scheme.{0}) (x : U ⟶ X) (v : (Γ(U, ⊤))ˣ), v ^ q = umap x u →
      ev γ 0 1 (by simp) U x = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q U v))
    (h₁' : ∀ (U : Scheme.{0}) (x : U ⟶ X), ev γ' 1 0 (by simp) U x = 0)
    (h₂' : ∀ (U : Scheme.{0}) (x : U ⟶ X) (v : (Γ(U, ⊤))ˣ), v ^ q = umap x u →
      ev γ' 0 1 (by simp) U x = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q U v)) : γ = γ' := by
  refine (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.2.1 _ _ fun p s h U x => ?_
  match p with
  | 0 =>
    obtain rfl : s = 1 := by omega
    change U ⟶ X at x
    refine sep (ClsSpec.loc_mono (root_loc (unit_res x hX) (umap x u)) fun V g ⟨v, hv⟩ => ?_)
    rw [(GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.1 γ 0 1 _ V U g x, (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.1 γ' 0 1 _ V U g x]
    have hv' : v ^ q = umap (g ≫ x) u := by rw [hv, umap_comp]
    exact (h₂ V (g ≫ x) v hv').trans (h₂' V (g ≫ x) v hv').symm
  | 1 =>
    obtain rfl : s = 0 := by omega
    exact (h₁ U x).trans (h₁' U x).symm
  | p + 2 =>
    haveI := sec_subsingleton (tw q 1) U (s := s) (by omega)
    exact Subsingleton.elim _ _

theorem eq_zero_of_kumT [NeZero q] (ht : kumT q = 0) {X : Scheme.{0}} (hX : IsUnit (q : Γ(X, ⊤))) (u : (Γ(X, ⊤))ˣ)
    {γ : Cochain ((chains (ZMod q)).obj (sch.obj X)) (res _ (tw q 1)) 1}
    (h₁ : ∀ (U : Scheme.{0}) (x : U ⟶ X), ev γ 1 0 (by simp) U x = 0)
    (h₂ : ∀ (U : Scheme.{0}) (x : U ⟶ X) (v : (Γ(U, ⊤))ˣ), v ^ q = umap x u →
      ev γ 0 1 (by simp) U x = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q U v)) : γ = 0 :=
  kum_unique hX u h₁ h₂ (fun U x => ev_zero (E := sch.obj X) _ _ _ _ _)
    (fun U x v _ => (ev_zero (E := sch.obj X) _ _ _ _ _).trans (by rw [ht]; exact (smap_zero _).symm))

theorem kum_pull [NeZero q] {Y X : Scheme.{0}} (f : Y ⟶ X) (u : (Γ(X, ⊤))ˣ) (hX : IsUnit (q : Γ(X, ⊤))) :
    pull _ (sch.map f) _ _ (kum q u) = kum q (Units.map f.appTop.hom.toMonoidHom u) := by
  obtain ⟨γ, hγ, h₁, h₂⟩ := kum_spec q hX u
  obtain ⟨γ', hγ', h₁', h₂'⟩ := kum_spec q (unit_res f hX) (umap f u)
  rw [← hγ, ← hγ']
  change CohomologyClass.mk (zcomp (Cocycle.ofHom ((chains (ZMod q)).map (sch.map f))) γ (zero_add 1)) = _
  congr 1
  refine Cocycle.ext (kum_unique (unit_res f hX) (umap f u) (fun U y => ?_) (fun U y v hv => ?_) h₁' h₂')
  · change ev ((Cochain.ofHom ((chains (ZMod q)).map (sch.map f))).comp γ.1 (zero_add 1)) 1 0 _ U y = 0
    rw [(GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.2.2.1 (sch.map f) γ.1 1 0 _ U y]
    exact h₁ U (y ≫ f)
  · change ev ((Cochain.ofHom ((chains (ZMod q)).map (sch.map f))).comp γ.1 (zero_add 1)) 0 1 _ U y = _
    rw [(GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.2.2.1 (sch.map f) γ.1 0 1 _ U y]
    exact h₂ U (y ≫ f) v (by rw [hv, umap_comp])

theorem kum_mul [NeZero q] {X : Scheme.{0}} (hX : IsUnit (q : Γ(X, ⊤))) (u₁ u₂ : (Γ(X, ⊤))ˣ) :
    kum q (u₁ * u₂) = kum q u₁ + kum q u₂ := by
  obtain ⟨γ₁, e₁, a₁, b₁⟩ := kum_spec q hX u₁
  obtain ⟨γ₂, e₂, a₂, b₂⟩ := kum_spec q hX u₂
  obtain ⟨γ₃, e₃, a₃, b₃⟩ := kum_spec q hX (u₁ * u₂)
  rw [← e₁, ← e₂, ← e₃, eq_comm, ← CohomologyClass.mk_add, ← sub_eq_zero, ← CohomologyClass.mk_sub,
    CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ 0 (zero_add 1)]
  rcases kumT_cases q with ht | ht
  · obtain ⟨e, he, hw⟩ := exists_two_family ht (E := sch.obj X) (p := 0) (fun U (x : U ⟶ X) => unit_res x hX)
      (fun U (x : U ⟶ X) => umap x u₁) (fun U (x : U ⟶ X) => umap x u₂)
      (fun V U g (x : U ⟶ X) => umap_comp g x u₁) (fun V U g (x : U ⟶ X) => umap_comp g x u₂)
    obtain ⟨β, c₁, c₂⟩ := exists_single (I := res _ (tw q 1)) (n := 0) 0 0 (by simp) e he
    refine ⟨β, (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.2.1 _ _ fun p s h U x => ?_⟩
    rw [Cocycle.coe_sub, Cocycle.coe_add, ev_sub', ev_add]
    match p with
    | 0 =>
      obtain rfl : s = 1 := by omega
      rw [(GlobalTheory.T.etaleCochainEvalOnSimplex_differential_values (ZMod q) (zero_add 1) β U).1 x, c₁]
      have hxU := unit_res (show U ⟶ X from x) hX
      refine sep (ClsSpec.loc_mono (ClsSpec.loc_and (root_loc hxU (umap (show U ⟶ X from x) u₁))
        (root_loc hxU (umap (show U ⟶ X from x) u₂))) ?_)
      rintro V g ⟨⟨v, hv⟩, w, hw'⟩
      have hv' : v ^ q = umap (show V ⟶ X from x.res g) u₁ := by rw [hv]; exact (umap_comp g _ u₁).symm
      have hw'' : w ^ q = umap (show V ⟶ X from x.res g) u₂ := by rw [hw']; exact (umap_comp g _ u₂).symm
      have hvw : (v * w) ^ q = umap (show V ⟶ X from x.res g) (u₁ * u₂) := by rw [mul_pow, hv', hw'', map_mul]
      rw [res_map, he V U g x, res_sub, res_add, (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.1 γ₁.1 0 1 _ V U g x,
        (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.1 γ₂.1 0 1 _ V U g x, (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.1 γ₃.1 0 1 _ V U g x]
      rw [hw V (x.res g) v w hv' hw'', b₁ V (x.res g) v hv', b₂ V (x.res g) w hw'', b₃ V (x.res g) _ hvw, smap_sub,
        smap_add]
    | 1 =>
      obtain rfl : s = 0 := by omega
      have key := (GlobalTheory.T.etaleCochainEvalOnSimplex_differential_values (ZMod q) (zero_add 1) β U).2 0 (-1) 0 (by simp) h x
      have hf : x.face 0 = x.face 1 := rfl
      rw [key, c₂ (0 + 1) _ _ _ _ one_ne_zero, smap_zero, zero_add, Fin.sum_univ_two, hf, a₁ U x, a₂ U x, a₃ U x]
      simp
    | p + 2 =>
      haveI := sec_subsingleton (tw q 1) U (s := s) (by omega)
      exact Subsingleton.elim _ _
  · refine ⟨0, ?_⟩
    rw [δ_zero, Cocycle.coe_sub, Cocycle.coe_add, eq_zero_of_kumT ht hX u₁ a₁ b₁, eq_zero_of_kumT ht hX u₂ a₂ b₂,
      eq_zero_of_kumT ht hX _ a₃ b₃]
    simp

theorem kum_pow_self [NeZero q] {X : Scheme.{0}} (hX : IsUnit (q : Γ(X, ⊤))) (u : (Γ(X, ⊤))ˣ) : kum q (u ^ q) = 0 := by
  obtain ⟨γ, e, a, b⟩ := kum_spec q hX (u ^ q)
  rw [← e, CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ 0 (zero_add 1)]
  rcases kumT_cases q with ht | ht
  · obtain ⟨β, c₁, c₂⟩ := exists_single (E := sch.obj X) (I := res _ (tw q 1)) (n := 0) 0 0 (by simp)
      (fun U (x : U ⟶ X) => kumT q U (umap x u))
      (fun V U g (x : U ⟶ X) => (ht.1 V U g _ (unit_res x hX)).trans (congrArg (kumT q V) (umap_comp g x u).symm))
    refine ⟨β, (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.2.1 _ _ fun p s h U x => ?_⟩
    match p with
    | 0 =>
      obtain rfl : s = 1 := by omega
      rw [(GlobalTheory.T.etaleCochainEvalOnSimplex_differential_values (ZMod q) (zero_add 1) β U).1 x, c₁]
      change U ⟶ X at x
      exact (b U x _ (by rw [← map_pow])).symm
    | 1 =>
      obtain rfl : s = 0 := by omega
      have key := (GlobalTheory.T.etaleCochainEvalOnSimplex_differential_values (ZMod q) (zero_add 1) β U).2 0 (-1) 0 (by simp) h x
      have hf : x.face 0 = x.face 1 := rfl
      rw [key, c₂ (0 + 1) _ _ _ _ one_ne_zero, smap_zero, zero_add, Fin.sum_univ_two, hf, a U x]
      simp
    | p + 2 =>
      haveI := sec_subsingleton (tw q 1) U (s := s) (by omega)
      exact Subsingleton.elim _ _
  · exact ⟨0, by rw [δ_zero, eq_zero_of_kumT ht hX _ a b]⟩

end KumNat


open KumNat in
theorem kum_cocycle_natural_additive : ∀ (q : ℕ) [NeZero q], (∀ (X : Scheme.{0}) (u : (Γ(X, ⊤))ˣ), IsUnit (q : Γ(X, ⊤)) → ∃ γ : Cocycle ((chains (ZMod q)).obj (sch.obj X)) (res _ (tw q 1)) 1, CohomologyClass.mk γ = kum q u ∧ (∀ (U : Scheme.{0}) (x : U ⟶ X), ev γ.1 1 0 (by simp) U x = 0) ∧ ∀ (U : Scheme.{0}) (x : U ⟶ X) (v : (Γ(U, ⊤))ˣ), v ^ q = Units.map x.appTop.hom.toMonoidHom u → ev γ.1 0 1 (by simp) U x = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q U v)) ∧ (∀ {Y X : Scheme.{0}} (f : Y ⟶ X) (u : (Γ(X, ⊤))ˣ), IsUnit (q : Γ(X, ⊤)) → pull _ (sch.map f) _ _ (kum q u) = kum q (Units.map f.appTop.hom.toMonoidHom u)) ∧ ∀ {X : Scheme.{0}} (u v : (Γ(X, ⊤))ˣ), IsUnit (q : Γ(X, ⊤)) → kum q (u * v) = kum q u + kum q v ∧ kum q (u ^ q) = 0 := by
  intro q _
  exact ⟨fun X u hX => kum_spec q hX u, fun f u hX => kum_pull f u hX, fun u v hX => ⟨kum_mul hX u v, kum_pow_self hX u⟩⟩

end GlobalTheory.EtC

end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum.Two

namespace GlobalTheory.Mum.PowData

section ProdPow

variable {X Y Z : Scheme.{0}} (L : LB X) {I K : Type} [Fintype I] [Fintype K]

def prodZGen (φ : I → K → (Y ⟶ X)) (ε : I → K → ℤ) (n : I → ℤ) (t : ∀ i, LB.Gen (LB.LinComb L (φ i) (ε i))) :
    LB.Gen (LB.LinComb L (K := I × K) (fun p => φ p.1 p.2) (fun p => n p.1 * ε p.1 p.2)) where
  s := fun j => ∏ i, res ((fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (i, k)) :
      LB.wchart L (fun p : I × K => φ p.1 p.2) j ≤ LB.wchart L (φ i) (fun k => j (i, k)))
    ((t i).s fun k => j (i, k)) ^ n i

variable {L}

theorem val_prodZGen (φ : I → K → (Y ⟶ X)) (ε : I → K → ℤ) (n : I → ℤ) (t : ∀ i, LB.Gen (LB.LinComb L (φ i) (ε i)))
    (r : Z ⟶ Y) {z : Z} {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    val (prodZGen L φ ε n t) r z J = ∏ i, val (t i) r z J ^ n i := by
  refine (map_prod _ _ _).trans (Finset.prod_congr rfl fun i _ => (map_zpow _ _ _).trans ?_)
  exact congrArg (· ^ n i) (gm_res r z _ (hJ.mem (fun p : I × K => φ p.1 p.2) r) _)

theorem prodZGen_isGen (hL : L.IsLB) {φ : I → K → (Y ⟶ X)} {ε : I → K → ℤ} (n : I → ℤ)
    {t : ∀ i, LB.Gen (LB.LinComb L (φ i) (ε i))} (ht : ∀ i, (t i).IsGen) : (prodZGen L φ ε n t).IsGen := by
  intro j j'
  refine unit_ext fun y hy => ?_
  have m : ∀ (j : I × K → L.ι) (i : I), y ∈ LB.wchart L (fun p : I × K => φ p.1 p.2) j →
      (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart L (φ i) (fun k => j (i, k)) :=
    fun _ i hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (i, k)
  have v : ∀ j : I × K → L.ι, y ∈ LB.wchart L (fun p : I × K => φ p.1 p.2) j →
      gm (𝟙 Y) y _ ((prodZGen L φ ε n t).s j) = ∏ i, gm (𝟙 Y) y _ ((t i).s fun k => j (i, k)) ^ n i := fun j hj =>
    (map_prod _ _ _).trans (Finset.prod_congr rfl fun i _ => (map_zpow _ _ _).trans
      (congrArg (· ^ n i) (gm_res _ y _ hj _)))
  rw [gm_res _ y _ hy, map_mul, gm_res _ y _ hy, v j hy.1, v j' hy.2]
  erw [gm_linComb L (fun p : I × K => φ p.1 p.2) (fun p => n p.1 * ε p.1 p.2) (𝟙 Y) y j j' hy.1 hy.2]
  rw [Fintype.prod_prod_type, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  erw [gen_trans (ht i) (𝟙 Y) y (m j i hy.1) (m j' i hy.2)]
  rw [mul_zpow, trF, ← Finset.prod_zpow]
  congr 1
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← zpow_mul, mul_comm]

end ProdPow

end GlobalTheory.Mum.PowData

namespace GlobalTheory.Mum.PowData

section JoinIso

variable {X X₁ X₂ Z : Scheme.{0}}

theorem part_gm_g_eq_one {N : LB X} {M : LB X₁} {e : X₁ ⟶ X} {π : N.ι → M.ι} (h : IsPart N M e π) (hM : M.IsLB)
    {ψ : Z ⟶ X₁} {f : Z ⟶ X} (hf : f = ψ ≫ e) {z : Z} {i j : N.ι} (e₀ : π i = π j) (hi : ψ z ∈ M.U (π i)) :
    gm f z (N.U i ⊓ N.U j) (N.g i j) = 1 := by
  subst hf
  rw [h.g _ ψ z i j hi (e₀ ▸ hi)]
  have : ∀ b, π i = b → gm ψ z (M.U (π i) ⊓ M.U b) (M.g (π i) b) = 1 := by
    rintro _ rfl; exact gm_self hM _ z hi
  exact this _ e₀

theorem part_gm_g_sec {N : LB X} {M : LB X₁} {e : X₁ ⟶ X} {π : N.ι → M.ι} (h : IsPart N M e π) {σ : M.ι → N.ι}
    (hσ : ∀ i, π (σ i) = i) {ψ : Z ⟶ X₁} {f : Z ⟶ X} (hf : f = ψ ≫ e) {z : Z} {a b : M.ι} (ha : ψ z ∈ M.U a)
    (hb : ψ z ∈ M.U b) : gm f z (N.U (σ a) ⊓ N.U (σ b)) (N.g (σ a) (σ b)) = gm ψ z (M.U a ⊓ M.U b) (M.g a b) := by
  subst hf
  rw [h.g _ ψ z _ _ (by rw [hσ]; exact ha) (by rw [hσ]; exact hb)]
  have : ∀ a b a' b', a = a' → b = b' → gm ψ z (M.U a ⊓ M.U b) (M.g a b) = gm ψ z (M.U a' ⊓ M.U b') (M.g a' b') := by
    rintro _ _ _ _ rfl rfl; rfl
  exact this _ _ _ _ (hσ a) (hσ b)

variable {M₁ : LB X₁} {M₂ : LB X₂} {K : Type} [Fintype K]

theorem exists_iso_of_joinGen (h₁ : M₁.IsLB) (h₂ : M₂.IsLB) [Nonempty X₁] [Nonempty X₂] {φ : K → (X₁ ⟶ X₂)}
    {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb (join M₁ M₂) (Sum.elim (fun k => φ k ≫ coprod.inr) (fun _ : PUnit => 𝟙 X₁ ≫ coprod.inl))
      (Sum.elim ε (fun _ => -1)))) (ht : t.IsGen) :
    ∃ w : LB.Iso M₁ (LB.LinComb M₂ φ ε), w.IsGen ∧ ∀ (Z : Scheme.{0}) (p : Z ⟶ X₁) (z : Z) (J),
      Good (join M₁ M₂) z J → gm p z _ (w.s (fun k => rr J (p ≫ φ k), rl J p)) = val t p z J := by
  have hp₁ := isPart_inl M₁ M₂
  have hp₂ := isPart_inr M₁ M₂
  choose σ₂ hσ₂ using snd_surjective (M₂ := M₂) h₁
  choose σ₁ hσ₁ using fst_surjective (M₁ := M₁) h₂
  let ix : (K → M₂.ι) × M₁.ι → K ⊕ PUnit → (join M₁ M₂).ι := fun a =>
    Sum.elim (fun k => σ₂ (a.1 k)) (fun _ => σ₁ a.2)
  have le : ∀ a, (LB.div (LB.LinComb M₂ φ ε) M₁).U a ≤
      LB.wchart (join M₁ M₂) (Sum.elim (fun k => φ k ≫ coprod.inr) (fun _ : PUnit => 𝟙 X₁ ≫ coprod.inl)) (ix a) :=
    fun a y hy => Set.mem_iInter.2 fun k => by
      rcases k with k | u
      · exact (hp₂.mem _ _).2 ((hσ₂ _).symm ▸ Set.mem_iInter.1 hy.1 k)
      · exact (hp₁.mem _ _).2 ((hσ₁ _).symm ▸ hy.2)
  let c : ChartPull (LB.div (LB.LinComb M₂ φ ε) M₁)
      (LB.LinComb (join M₁ M₂) (Sum.elim (fun k => φ k ≫ coprod.inr) (fun _ : PUnit => 𝟙 X₁ ≫ coprod.inl))
        (Sum.elim ε (fun _ => -1))) (𝟙 X₁) :=
    { idx := ix
      le := le
      g := fun y a b ha hb => by
        erw [gm_div M₁ (LB.LinComb M₂ φ ε) (𝟙 X₁) y a b ⟨ha, hb⟩, gm_linComb M₂ φ ε (𝟙 X₁) y a.1 b.1 ha.1 hb.1,
          gm_linComb (join M₁ M₂) _ _ (𝟙 X₁) y (ix a) (ix b) (le a ha) (le b hb)]
        rw [Fintype.prod_sum_type]
        simp only [Finset.univ_unique, Finset.prod_singleton]
        refine congrArg₂ (· * ·) (Finset.prod_congr rfl fun k _ => ?_) ?_
        · exact congrArg (· ^ ε k) (part_gm_g_sec hp₂ hσ₂ (ψ := 𝟙 X₁ ≫ φ k) (f := 𝟙 X₁ ≫ φ k ≫ coprod.inr)
            (Category.assoc _ _ _).symm (a := a.1 k) (b := b.1 k) (Set.mem_iInter.1 ha.1 k)
            (Set.mem_iInter.1 hb.1 k)).symm
        · refine (congrArg (·⁻¹) ?_).trans (zpow_neg_one _).symm
          refine Eq.trans ?_ (part_gm_g_sec hp₁ hσ₁ (ψ := 𝟙 X₁) (f := 𝟙 X₁ ≫ 𝟙 X₁ ≫ coprod.inl)
            (by rw [Category.id_comp]) (a := a.2) (b := b.2) ha.2 hb.2).symm
          rfl }
  refine ⟨cGen c t, cGen_isGen c ht, fun Z p z J hJ => ?_⟩
  have m : p z ∈ (LB.div (LB.LinComb M₂ φ ε) M₁).U (fun k => rr J (p ≫ φ k), rl J p) :=
    ⟨(hp₂.good hJ).mem φ p, hp₁.good hJ p⟩
  have n := hJ.mem (Sum.elim (fun k => φ k ≫ coprod.inr) (fun _ : PUnit => 𝟙 X₁ ≫ coprod.inl)) p
  refine (gm_res p z _ m _).trans ((gen_trans ht p z (le _ m) n).trans ?_)
  refine (congrArg (· * val t p z J) ?_).trans (one_mul _)
  rw [trF, Fintype.prod_sum_type]
  simp only [Finset.univ_unique, Finset.prod_singleton]
  refine (congrArg₂ (· * ·) (Finset.prod_eq_one fun k _ => ?_) ?_).trans (one_mul 1)
  · refine (congrArg (· ^ ε k) (part_gm_g_eq_one hp₂ h₂ (ψ := p ≫ φ k) (f := p ≫ φ k ≫ coprod.inr)
      (Category.assoc _ _ _).symm (i := σ₂ (rr J (p ≫ φ k))) (j := J (p ≫ φ k ≫ coprod.inr))
      ((hσ₂ _).trans (show (J ((p ≫ φ k) ≫ coprod.inr)).2 = _ by rw [Category.assoc])) ?_)).trans (one_zpow _)
    rw [hσ₂]; exact (hp₂.good hJ) (p ≫ φ k)
  · refine (congrArg (· ^ (-1 : ℤ)) (part_gm_g_eq_one hp₁ h₁ (ψ := p) (f := p ≫ 𝟙 X₁ ≫ coprod.inl)
      (by rw [Category.id_comp]) (i := σ₁ (rl J p)) (j := J (p ≫ 𝟙 X₁ ≫ coprod.inl))
      ((hσ₁ _).trans (show (J (p ≫ coprod.inl)).1 = _ by rw [Category.id_comp])) ?_)).trans (one_zpow _)
    rw [hσ₁]; exact hp₁.good hJ p

end JoinIso

end GlobalTheory.Mum.PowData
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

namespace GlobalTheory.Mum.Two

def TorusHomOf {S : Scheme.{0}} {X X' : Type} [AddCommGroup X] [AddCommGroup X'] (h : X' → X)
    (t : splitTorus S X ⟶ splitTorus S X') : Prop :=
  ∀ χ : X', res (fun x _ => show t.left.base x ∈ (⊤ : TopologicalSpace.Opens _) from trivial)
    (pullU t.left ⊤ (charUnit S X' χ)) = charUnit S X (h χ)

variable {R : Type} [CommRing R] [IsDomain R]

instance nonempty_av {S : Type} [CommRing S] [IsDomain S] (P : PolAV (Sp S)) : Nonempty P.A.left :=
  ⟨eSec P.A (⊥ : PrimeSpectrum S)⟩

abbrev JN (D₁ D₂ : DegPre R) : LB (D₁.P.A.left ⨿ D₂.P.A.left) := join D₁.P.L D₂.P.L

theorem jn_isLB (D₁ D₂ : DegPre R) : (JN D₁ D₂).IsLB := join_isLB D₁.P.isLB D₂.P.isLB

abbrev CmpLB (D₁ D₂ : DegPre R) (a : D₁.P.A ⟶ D₂.P.A) (χ₁ : D₁.X) (χ₂ : D₂.X) : LB D₁.P.A.left :=
  LB.LinComb (JN D₁ D₂) (Sum.elim (fun k => D₁.Oφ (𝟙 _) χ₁ k ≫ coprod.inl) (fun k => D₂.Oφ a χ₂ k ≫ coprod.inr))
    (Sum.elim Oε Oinvε)

def Nrm {D₁ D₂ : DegPre R} {a : D₁.P.A ⟶ D₂.P.A} {χ₁ : D₁.X} {χ₂ : D₂.X} (u : LB.Gen (CmpLB D₁ D₂ a χ₁ χ₂)) : Prop :=
  u.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp R) (z : Z) (J), Good (JN D₁ D₂) z J → val u (r ≫ eSec D₁.P.A) z J = 1

def Act (D₁ D₂ : DegPre R) (a : D₁.P.A ⟶ D₂.P.A) (h : D₂.X →+ D₁.X) {F : Type} [Field F] [Algebra (FractionRing R) F]
    (g : GtPtF D₁ F) (g' : GtPtF D₂ F) : Prop :=
  g'.b = g.b ≫ a ∧ ∀ (χ : D₂.X) (u : LB.Gen (CmpLB D₁ D₂ a (h χ) χ)), Nrm u → ∀ z J, Good (JN D₁ D₂) z J →
    val (g'.s χ) (𝟙 _) z (rr J) = val (g.s (h χ)) (𝟙 _) z (rl J) * val u g.b.left z J

variable {I : Ideal R} {D₁ D₂ : DegData R I} {A₁ A₂ : PolAV (Sp (FractionRing R))}
  {G₁ G₂ : Over (Sp R)} [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂]

def Over₀ (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂) (a : G₁ ⟶ G₂) (b : D₁.toPre.P.A ⟶ D₂.toPre.P.A) : Prop :=
  ∀ e, (Over.pullback (thick R I e)).map a ≫ (U₂.gt e).q = (U₁.gt e).q ≫ (Over.pullback (thick R I e)).map b

def OnTorus (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂) (a : G₁ ⟶ G₂) (h : D₂.toPre.X → D₁.toPre.X) : Prop :=
  ∀ e, ∃ t : splitTorus (Sp (R ⧸ I ^ (e + 1))) D₁.toPre.X ⟶ splitTorus (Sp (R ⧸ I ^ (e + 1))) D₂.toPre.X,
    TorusHomOf h t ∧ (U₁.gt e).i ≫ (Over.pullback (thick R I e)).map a = t ≫ (U₂.gt e).i

def Lin (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂) (a : G₁ ⟶ G₂) (b : D₁.toPre.P.A ⟶ D₂.toPre.P.A)
    (h : D₂.toPre.X →+ D₁.toPre.X) : Prop :=
  IsMonHom a ∧ IsMonHom b ∧ Over₀ U₁ U₂ a b ∧ OnTorus U₁ U₂ a h

def Coord (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂) (a : G₁ ⟶ G₂) (b : D₁.toPre.P.A ⟶ D₂.toPre.P.A)
    (h : D₂.toPre.X →+ D₁.toPre.X) : Prop :=
  ∀ χ, ∃ u : LB.Gen (CmpLB D₁.toPre D₂.toPre b (h χ) χ), Nrm u ∧
    ∀ (e : ℕ) (Z : Scheme.{0}) (x : Z ⟶ (thickObj R I e G₁).left) (z : Z) (J), Good (JN D₁.toPre D₂.toPre) z J →
      val ((U₂.gt e).t χ) (x ≫ ((Over.pullback (thick R I e)).map a).left) z (rr J) =
        val ((U₁.gt e).t (h χ)) x z (rl J) * val u (x ≫ (U₁.gt e).pG.left) z J

def Gen₀ (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂) (a : G₁ ⟶ G₂) (c : A₁.A ⟶ A₂.A) : Prop :=
  (Over.pullback (jK R)).map a ≫ U₂.gen.hom = U₁.gen.hom ≫ c

def CrossH {F : Type} [Field F] [Algebra (FractionRing R) F] (c : A₁.A ⟶ A₂.A) {j j' : ℕ} (t₁ t₂ : SecA A₂ F j)
    (t₁' t₂' : SecA A₁ F j') : Prop :=
  ∀ z J₁ J₂, Good A₁.L z J₁ → Good A₂.L z J₂ →
    sA t₁ (TFK (R := R) F ◁ c).left z J₂ * sA t₂' (𝟙 _) z J₁ = sA t₂ (TFK (R := R) F ◁ c).left z J₂ * sA t₁' (𝟙 _) z J₁

def Key (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂) (c : A₁.A ⟶ A₂.A) (b : D₁.toPre.P.A ⟶ D₂.toPre.P.A)
    (h : D₂.toPre.X →+ D₁.toPre.X) (F : Type) [Field F] [Algebra (FractionRing R) F] : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ (p : QkPt D₁.toPre F k) (x : TFK (R := R) F ⟶ A₁.A), QkToAkU U₁ F k p x →
    ∀ g', Act D₁.toPre D₂.toPre b h p.g g' → ∃ p' : QkPt D₂.toPre F k, p'.g = g' ∧ QkToAkU U₂ F k p' (x ≫ c)

theorem lin_of_endU {U : UnifPre I D₁ A₁ G₁} (E : EndU U) : Lin U U E.aG E.aB E.h ∧ Gen₀ U U E.aG E.aA :=
  ⟨⟨E.homG, E.homB, E.q_lin, E.i_lin⟩, E.ext⟩

end GlobalTheory.Mum.Two
end
end

section

open GlobalTheory.ShFam.Hor.LogCh

set_option autoImplicit false

open Topology

namespace GlobalTheory.LatReal

theorem isRealBasis_of_isLatFam : ∀ (n g r : ℕ) (B : Set (Fin n → ℂ)) (K : (Fin n → ℂ) → Set (Fin g → ℂ))
    (b₀ : Fin n → ℂ) (lam : Fin r → Fin g → ℂ), IsLatFam B K → b₀ ∈ B → Submodule.span ℝ (K b₀) = ⊤ →
    LinearIndependent ℤ lam → (∀ w, w ∈ K b₀ ↔ ∃ k : Fin r → ℤ, w = ∑ j, k j • lam j) →
    LinearIndependent ℝ lam ∧ Submodule.span ℝ (Set.range lam) = ⊤ := by
  intro n g r B K b₀ lam hF hb hspan hli hK
  have hmemL : ∀ w, w ∈ Submodule.span ℤ (Set.range lam) ↔ w ∈ K b₀ := by
    intro w
    rw [Submodule.mem_span_range_iff_exists_fun, hK]
    constructor <;> rintro ⟨k, hk⟩ <;> exact ⟨k, hk.symm⟩
  have hsub : K b₀ ⊆ Submodule.span ℝ (Set.range lam) := by
    intro w hw
    obtain ⟨k, rfl⟩ := (hK w).1 hw
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [← Int.cast_smul_eq_zsmul ℝ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have htop : Submodule.span ℝ (Set.range lam) = ⊤ := by
    rw [eq_top_iff, ← hspan]
    exact Submodule.span_le.2 hsub
  refine ⟨?_, htop⟩
  have h0 : (0 : Fin g → ℂ) ∈ K b₀ := (hK 0).2 ⟨0, by simp⟩
  obtain ⟨ζ, hζ0, -, hev⟩ := hF.2.2.2 b₀ hb 0 h0
  have ht : Filter.Tendsto (fun w : Fin g → ℂ => (b₀, w)) (𝓝 0) (𝓝 (b₀, 0)) :=
    (continuous_const.prodMk continuous_id).tendsto' 0 (b₀, 0) rfl
  have hev' : ∀ᶠ w in 𝓝 (0 : Fin g → ℂ), (w ∈ K b₀ ↔ w = 0) := by
    filter_upwards [ht.eventually hev] with w hw
    simpa [hζ0] using hw
  obtain ⟨U, hU, hUo, hU0⟩ := mem_nhds_iff.1 hev'
  set L := Submodule.span ℤ (Set.range lam) with hLdef
  haveI : DiscreteTopology L := by
    apply discreteTopology_of_isOpen_singleton_zero
    rw [isOpen_induced_iff]
    refine ⟨U, hUo, ?_⟩
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hx
      exact Subtype.ext ((hU hx).1 ((hmemL x).1 x.2))
    · rintro rfl
      exact hU0
  have hLset : (L : Set (Fin g → ℂ)) = K b₀ := by
    ext w
    exact hmemL w
  haveI : IsZLattice ℝ L := ⟨by rw [hLset, hspan]⟩
  have hrank := ZLattice.rank ℝ L
  have hcard : Module.finrank ℤ L = r := by
    rw [Module.finrank_eq_card_basis (Module.Basis.span hli)]
    simp
  apply linearIndependent_of_top_le_span_of_card_eq_finrank htop.ge
  rw [Fintype.card_fin]
  omega

end GlobalTheory.LatReal
end

section

theorem GlobalTheory.Published.realMetaplecticRepresentation_holds : GlobalTheory.Published.RealMetaplecticRepresentation :=
  CompanionTheory.ThKR.realMetaplecticRepresentation_holds
end

section

open MeasureTheory Matrix Complex GlobalTheory.RealWeil
open scoped Real SchwartzMap ComplexConjugate

theorem _root_.GlobalTheory.T.metaplecticGaussianNormalisedAlt : ∀ (l : Type) [Fintype l] [DecidableEq l], ∃ (G : Type) (_ : Group G) (_ : TopologicalSpace G) (_ : IsTopologicalGroup G) (pr : G →* Matrix.symplecticGroup l ℝ) (om : G →* (L2 l ≃ₗᵢ[ℂ] L2 l)) (omS : G →* (Sch l →L[ℂ] Sch l)) (φ : Sch l), IsCoveringMap pr ∧ Function.Surjective pr ∧ (∃ ε : G, ε ≠ 1 ∧ (∀ g, pr g = 1 ↔ g = 1 ∨ g = ε) ∧ ∀ f, om ε f = -f) ∧ (∀ f : L2 l, Continuous fun g => om g f) ∧ (∀ (g : G) (w : l ⊕ l → ℝ) (f : L2 l), om g (rho w f) = rho ((pr g : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ w) (om g f)) ∧ (∀ (g : G) (f : Sch l), om g (f.toLp 2) = (omS g f).toLp 2) ∧ (∀ x : EuclideanSpace ℝ l, φ x = cexp (-π * ((x.ofLp ⬝ᵥ x.ofLp : ℝ) : ℂ))) ∧ (∀ j : l, dRho (Pi.single (.inl j) 1) φ = I • dRho (Pi.single (.inr j) 1) φ) ∧ ∀ (g : G) (P : Matrix l l ℂ), (∀ a b, P a b = ((pr g).1 (.inl a) (.inl b) : ℂ) - I * ((pr g).1 (.inl a) (.inr b) : ℂ)) → omS g φ 0 ^ 2 * P.det = 1 := by
  first | exact @GlobalTheory.metaplecticGaussianNormalised | exact GlobalTheory.metaplecticGaussianNormalised | (intros; apply GlobalTheory.metaplecticGaussianNormalised <;> assumption)
end
