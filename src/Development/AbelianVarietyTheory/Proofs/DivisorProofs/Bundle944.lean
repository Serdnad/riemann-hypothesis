module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChosenInjectiveResolutionEtaleSheafSectionsExactStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle609
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle800
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle463
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle563
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle491
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleCocycleFirstChernClassTateTwist
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle408
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle462
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle766
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle730
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle922
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle801
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle690
public import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoAppTopOfIsPullbackOfSurjective
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle026

@[expose] public section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.CupGen
open ClsSpec

theorem sub_zero_full {E : Spc} {N : ℕ} {U : Scheme.{0}} (x : Sx E N U) (h : 0 + N ≤ N) : x.sub 0 N h = x := by
  have : SimplexCategory.subinterval 0 N h = 𝟙 _ := by
    ext i; simp [SimplexCategory.subinterval]
  simp [Sx.sub, this]

theorem aw_zero_left {R : Type} [CommRing R] {I J K : Cx R} (μ : Pair I J K) {E : Spc} {m : ℤ} (hm : 0 + m = m)
    (hI : ∀ (s : ℤ) (U : Scheme.{0}), s < 0 → Subsingleton (Sec (I.X s) U))
    (α : Cochain ((chains R).obj E) I 0) (β : Cochain ((chains R).obj E) J m) (γ : Cochain ((chains R).obj E) K m)
    (h : μ.IsAW hm α β γ) (N : ℕ) (w : ℤ) (hw : -(N : ℤ) + m = w) (U : Scheme.{0}) (x : Sx E N U) :
    ev γ N w hw U x = μ.mul U 0 w w (zero_add w) (ev α 0 0 (by simp) U (x.sub 0 0 (by omega))) (ev β N w hw U x) := by
  rw [h N w hw U x, Finset.sum_eq_single 0]
  · subst hw
    have e1 : ((m * (((0 : Fin (N + 1)) : ℕ) : ℤ)).negOnePow) = 1 := by simp
    rw [e1, one_smul]
    have e2 : x.sub ((0 : Fin (N + 1)) : ℕ) (N - ((0 : Fin (N + 1)) : ℕ)) (by simp) = x := sub_zero_full x (by omega)
    rw [e2]
    rfl
  · intro p _ hp
    have hp' : 0 < (p : ℕ) := Fin.pos_iff_ne_zero.2 hp
    haveI := hI (-((p : ℕ) : ℤ) + 0) U (by omega)
    rw [Subsingleton.elim (ev α p _ rfl U _) 0, map_zero, LinearMap.zero_apply, smul_zero]
  · intro h0; exact absurd (Finset.mem_univ _) h0

theorem factor_cochain {R : Type} [CommRing R] {E : Spc} {D C : Cx R} (ι : D ⟶ C)
    (hinj : ∀ n U, Function.Injective (Sec.map (ι.f n) (U := U))) {n : ℤ} (β : Cochain ((chains R).obj E) C n)
    (hβ : ∀ p s h U x, ∃ b, Sec.map (ι.f s) b = ev β p s h U x) :
    ∃ β' : Cochain ((chains R).obj E) D n, β'.comp (Cochain.ofHom ι) (add_zero n) = β := by
  choose b hb using hβ
  obtain ⟨β', hβ'⟩ := GlobalTheory.T.exists_cochain_ev_eq_of_natural' R (E := E) (I := D) (n := n) b (fun p s h V U g x => by
    apply hinj
    rw [← res_map, hb, hb, (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R).2.1])
  refine ⟨β', (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R).2.2.1 _ _ fun p s h U x => ?_⟩
  rw [(GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R).2.2.2.2, hβ', hb]

theorem supp_twres (q : ℕ) [NeZero q] (i : ℤ) (D : Cx (ZMod q)) (ι : D ⟶ res _ (tw q i))
    (hinj : ∀ n U, Function.Injective (Sec.map (ι.f n) (U := U)))
    (hD : ∀ n U (a : Sec ((res _ (tw q i)).X n) U), (∃ b, Sec.map (ι.f n) b = a) ↔
      Loc U fun V g => IsUnit (q : Γ(V, ⊤)) ∨ Sec.res g a = 0) :
    ∃ e : ∀ U : Scheme.{0}, Prim q Γ(U, ⊤) → Sec (D.X 0) U, IsTwRes q i D e ∧
      ∀ U ζ, Sec.map (ι.f 0) (e U ζ) = resGen i ζ := GlobalTheory.T.supportedSections_tateTwist_resolution q i D ι hinj hD

theorem exists_unit_map (q : ℕ) [NeZero q] (i k : ℤ) (μ : Pair (res _ (tw q 0)) (res _ (tw q i)) (res _ (tw q k)))
    (D : Cx (ZMod q)) (ι : D ⟶ res _ (tw q i))
    (hD : ∀ n U (a : Sec ((res _ (tw q i)).X n) U), (∃ b, Sec.map (ι.f n) b = a) ↔
      Loc U fun V g => IsUnit (q : Γ(V, ⊤)) ∨ Sec.res g a = 0) :
    ∃ u : D ⟶ res _ (tw q k), ∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (s : ℤ) (b : Sec (D.X s) U),
      Sec.map (u.f s) b = μ.mul U 0 s s (zero_add s) (resGen 0 ζ) (Sec.map (ι.f s) b) := GlobalTheory.T.unitSection_multiplication_chainMap q i k μ D ι hD

theorem loc_all {U : Scheme.{0}} {P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : ∀ V g, P V g) : Loc U P :=
  ⟨⊤, Scheme.etaleTopology.top_mem U, fun V g _ => h V g⟩

theorem root_mul (q : ℕ) [NeZero q] (X : Scheme.{0}) (ζ : Prim q Γ(X, ⊤)) (i j : ℤ) :
    cup q (rootClass i ζ) (rootClass j ζ) = (rootClass (i + j) ζ).cast (by ring) rfl ∧
      rootClass 0 ζ = one q (sch.obj X) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨α, hα, hαv⟩ := rootClass_spec i ζ
    obtain ⟨β, hβ, hβv⟩ := rootClass_spec j ζ
    obtain ⟨γ, hγ⟩ := (GlobalTheory.T.cup_eq_class_of_isAW (ZMod q) (twPair q i j) (E := sch.obj X) (rfl : (0 : ℤ) + 0 = 0 + 0)).1 α β
    have hc := (GlobalTheory.T.cup_eq_class_of_isAW (ZMod q) (twPair q i j) (E := sch.obj X) (rfl : (0 : ℤ) + 0 = 0 + 0)).2 α β γ hγ
    change (twPair q i j).cup (sch.obj X) rfl (rootClass i ζ) (rootClass j ζ) = rootClass (i + j) ζ
    rw [← hα, ← hβ, hc, (GlobalTheory.T.tateTwistUnitClass_rootClass_spec q).2.2.2]
    refine ((GlobalTheory.T.degreeZeroSectionClass_properties (ZMod q) (tw q (i + j)) X).1 _ γ).1 ?_
    have e := hγ 0 0 (by simp) X (𝟙 X)
    rw [Finset.sum_eq_single 0 (fun p _ hp => absurd (Subsingleton.elim (α := Fin 1) p 0) hp) (fun h0 => absurd (Finset.mem_univ _) h0)] at e
    have e1 : (((0 : ℤ) * (((0 : Fin 1) : ℕ) : ℤ)).negOnePow) = 1 := by simp
    rw [e1, one_smul] at e
    refine e.trans ?_
    have a1 := hαv X (𝟙 X)
    have b1 := hβv X (𝟙 X)
    rw [res_id] at a1 b1
    change (twPair q i j).mul X 0 0 0 (add_zero 0) (ev α.1 0 0 (by simp) X (𝟙 X)) (ev β.1 0 0 (by simp) X (𝟙 X)) = _
    rw [a1, b1]
    exact (GlobalTheory.T.tateTwistResolutionPairing_spec_and_cup_unique q i j).1 X ζ
  · obtain ⟨α, hα, hαv⟩ := rootClass_spec 0 ζ
    have hE : Inv q (sch.obj X) := fun U ⟨x⟩ => unit_res (x : U ⟶ X) ζ.2.1
    rw [← hα]
    refine (GlobalTheory.T.tateTwistUnitClass_rootClass_spec q).2.1 _ hE α fun U x ξ => ?_
    refine (hαv U x).trans ?_
    exact (res_resGen (q := q) 0 (show U ⟶ X from x) ζ).trans (resGen_zero_eq _ _)

theorem one_mul_of_pair (q : ℕ) [NeZero q] (E : Spc) (hE : Inv q E) (n i : ℤ) (hn : 0 + n = n)
    (μ : Pair (res _ (tw q 0)) (res _ (tw q i)) (res _ (tw q i))) (hμ : IsTwPair μ) (a : Ht q E n i) :
    μ.cup E hn (one q E) a = a := by
  obtain ⟨α, hα1, hαv⟩ := (GlobalTheory.T.tateTwistUnitClass_rootClass_spec q).1 E hE
  obtain ⟨β, rfl⟩ := a.mk_surjective
  obtain ⟨γ, hγ⟩ := (GlobalTheory.T.cup_eq_class_of_isAW (ZMod q) μ hn).1 α β
  rw [← hα1, (GlobalTheory.T.cup_eq_class_of_isAW (ZMod q) μ hn).2 α β γ hγ]
  obtain ⟨D, ι, hinj, hD⟩ := GlobalTheory.EtC.SuppSub.exists_supp_sub (ZMod q) (res _ (tw q i))
    (fun U => IsUnit (q : Γ(U, ⊤))) (fun V U g h => unit_res g h)
  obtain ⟨e, he, heι⟩ := supp_twres q i D ι hinj hD
  obtain ⟨u, hu⟩ := exists_unit_map q i i μ D ι hD
  have hom : Nonempty (Homotopy u ι) := ((GlobalTheory.T.tateTwistResolution_map_exists_unique_homotopy q i).2.2 e he).2 u ι fun U ζ => by
    rw [hu U ζ 0 (e U ζ), heι]
    exact hμ U ζ

  have hunit : ∀ (p : ℕ) (U : Scheme.{0}) (x : Sx E p U), IsUnit (q : Γ(U, ⊤)) :=
    fun p U x => hE U ⟨x.sub 0 0 (by omega)⟩
  obtain ⟨β', hβ'⟩ := factor_cochain ι hinj β.1 fun p s h U x =>
    (hD s U _).2 (loc_all fun V g => Or.inl (unit_res g (hunit p U x)))
  have hδ : δ n (n + 1) β' = 0 := by
    refine (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.2.1 _ _ fun p s h U x => hinj s U ?_
    rw [← (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.2.2.2, ← δ_comp_ofHom, hβ', Cocycle.δ_eq_zero, ev_zero, ev_zero, smap_zero]
  set β'' : Cocycle ((chains (ZMod q)).obj E) D n := Cocycle.mk β' (n + 1) rfl hδ
  have hb : CohomologyClass.mk β = cpush _ ι n (CohomologyClass.mk β'') := by
    change _ = CohomologyClass.mk _
    congr 1
    exact Cocycle.ext hβ'.symm
  have hg : CohomologyClass.mk γ = cpush _ u n (CohomologyClass.mk β'') := by
    change _ = CohomologyClass.mk _
    congr 1
    refine Cocycle.ext ((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.2.1 _ _ fun N w hw U x => ?_)
    change ev γ.1 N w hw U x = ev (β'.comp (Cochain.ofHom u) (add_zero n)) N w hw U x
    rw [(GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.2.2.2, aw_zero_left μ hn (fun s U hs => (GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness (ZMod q) (tw q 0) U).2.2.2 s hs)
      α.1 β.1 γ.1 hγ N w hw U x]
    refine ClsSpec.sep (ClsSpec.loc_mono ((GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity q U).1 (hunit N U x)) fun V g hz => ?_)
    obtain ⟨ζ⟩ := hz
    rw [res_map, (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.1 β', hu V ζ w, ← hβ', (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.2.2.2,
      μ.nat g, (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.1 α.1, res_map, (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.1 β', hαv V _ ζ]
  rw [hb, hg, ((GlobalTheory.EtC.ZcFun.main (ZMod q)).2.2.2.2 u ι hom _ n).2]

theorem main : ∀ (q : ℕ) [NeZero q], (∀ E : Spc, Inv q E → ∀ {n i : ℤ} (a : Ht q E n i), cup q (one q E) a = a.cast (by ring) (by ring)) ∧ (∀ (X : Scheme.{0}) (ζ : Prim q Γ(X, ⊤)) (i j : ℤ), cup q (rootClass i ζ) (rootClass j ζ) = (rootClass (i + j) ζ).cast (by ring) rfl ∧ rootClass 0 ζ = one q (sch.obj X)) := by
  intro q _
  refine ⟨fun E hE => ?_, fun X ζ i j => root_mul q X ζ i j⟩
  intro n i a
  have key : ∀ (k : ℤ) (hk : i = k) (m : ℤ) (hm : 0 + n = m) (μ : Pair (res _ (tw q 0)) (res _ (tw q i)) (res _ (tw q k))),
      IsTwPair μ → μ.cup E hm (one q E) a = a.cast (by omega) hk := by
    intro k hk m hm μ hμ
    subst hk
    obtain rfl : m = n := by omega
    exact one_mul_of_pair q E hE _ i hm μ hμ a
  exact key (0 + i) (by ring) (0 + n) rfl (twPair q 0 i) ((GlobalTheory.T.tateTwistResolutionPairing_spec_and_cup_unique q 0 i).1)

end GlobalTheory.EtC.CupGen
end
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LiftSys.LocalIsomorphism

theorem fix_of_mem {R B B₀ : Type} [CommRing R] [CommRing B] [Algebra R B] [CommRing B₀]
    (I : Ideal R) (hJ : I.map (algebraMap R B) ^ 2 = 0) (p : B →+* B₀)
    (hker : ∀ b, p b = 0 ↔ b ∈ I.map (algebraMap R B)) (e : B →ₐ[R] B) (he : ∀ b, p (e b) = p b)
    (x : B) (hx : x ∈ I.map (algebraMap R B)) : e x = x := by
  set J := I.map (algebraMap R B) with hJdef
  have hδ : ∀ y, e y - y ∈ J := fun y ↦ (hker _).1 (by rw [map_sub, he, sub_self])
  have hsq : ∀ a ∈ J, ∀ b ∈ J, a * b = 0 := fun a ha b hb ↦ by
    have : a * b ∈ J ^ 2 := by rw [pow_two]; exact Ideal.mul_mem_mul ha hb
    rw [hJ] at this
    simpa using this
  let T : Ideal B :=
    { carrier := {x | ∀ y, e (x * y) = x * y}
      add_mem' := fun {a b} ha hb y ↦ by simp only [Set.mem_setOf_eq] at *; rw [add_mul, map_add (f := _), ha, hb]
      zero_mem' := fun y ↦ by simp
      smul_mem' := fun c {a} ha y ↦ by
        simp only [Set.mem_setOf_eq, smul_eq_mul] at *
        rw [mul_assoc, mul_left_comm, ha, mul_left_comm] }
  have hIT : J ≤ T := by
    rw [hJdef, Ideal.map_le_iff_le_comap]
    intro r hr y
    show e (algebraMap R B r * y) = algebraMap R B r * y
    have hr' : algebraMap R B r ∈ J := Ideal.mem_map_of_mem _ hr
    rw [map_mul, AlgHom.commutes]
    have h0 := hsq _ hr' _ (hδ y)
    rw [mul_sub] at h0
    exact sub_eq_zero.1 h0
  have := hIT hx 1
  simpa using this

theorem bij {R B B₀ : Type} [CommRing R] [CommRing B] [Algebra R B] [CommRing B₀]
    (I : Ideal R) (hJ : I.map (algebraMap R B) ^ 2 = 0) (p : B →+* B₀)
    (hker : ∀ b, p b = 0 ↔ b ∈ I.map (algebraMap R B)) (e : B →ₐ[R] B) (he : ∀ b, p (e b) = p b) :
    Function.Bijective e := by
  have hδ : ∀ y, e y - y ∈ I.map (algebraMap R B) := fun y ↦ (hker _).1 (by rw [map_sub, he, sub_self])
  refine ⟨(injective_iff_map_eq_zero e).2 fun b hb ↦ ?_, fun c ↦ ?_⟩
  · have hb' : b ∈ I.map (algebraMap R B) := (hker b).1 (by rw [← he, hb, map_zero])
    rw [← fix_of_mem I hJ p hker e he b hb', hb]
  · refine ⟨c - (e c - c), ?_⟩
    rw [map_sub, fix_of_mem I hJ p hker e he _ (hδ c)]
    ring

theorem nil {R C D : Type} [CommRing R] [CommRing C] [Algebra R C] [CommRing D] [Algebra R D] (I : Ideal R)
    (q : C →ₐ[R] D) (h : ∀ b, q b = 0 ↔ b ∈ I.map (algebraMap R C)) (h2 : I.map (algebraMap R C) ^ 2 = 0) :
    IsNilpotent (RingHom.ker (q : C →+* D)) := ⟨2, by
  have : RingHom.ker (q : C →+* D) = I.map (algebraMap R C) := Ideal.ext fun b ↦ by
    rw [RingHom.mem_ker]; exact h b
  rw [this, h2]⟩

theorem exists_iso {R R₀ B B' B₀ : Type} [CommRing R] [CommRing R₀] [CommRing B] [Algebra R B] [CommRing B']
    [Algebra R B'] [CommRing B₀] [Algebra R₀ B₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀)
    (p : B →+* B₀) (p' : B' →+* B₀) (hp : SemiHom π p) (hp' : SemiHom π p')
    (hs : Function.Surjective p) (hs' : Function.Surjective p')
    (hk : ∀ b, p b = 0 ↔ b ∈ I.map (algebraMap R B)) (hk' : ∀ b, p' b = 0 ↔ b ∈ I.map (algebraMap R B'))
    [Algebra.FormallySmooth R B] [Algebra.FormallySmooth R B'] :
    ∃ φ : B ≃ₐ[R] B', ∀ b, p' (φ b) = p b := by
  letI : Algebra R B₀ := ((algebraMap R₀ B₀).comp π).toAlgebra
  let P : B →ₐ[R] B₀ := { p with commutes' := fun r ↦ hp.map_algebraMap r }
  let P' : B' →ₐ[R] B₀ := { p' with commutes' := fun r ↦ hp'.map_algebraMap r }
  have hJ := map_sq hI B
  have hJ' := map_sq hI B'
  let φ : B →ₐ[R] B' := Algebra.FormallySmooth.liftOfSurjective P P' hs' (nil I P' hk' hJ')
  let ψ : B' →ₐ[R] B := Algebra.FormallySmooth.liftOfSurjective P' P hs (nil I P hk hJ)
  have hφ : ∀ b, p' (φ b) = p b := fun b ↦
    Algebra.FormallySmooth.liftOfSurjective_apply P P' hs' (nil I P' hk' hJ') b
  have hψ : ∀ b, p (ψ b) = p' b := fun b ↦
    Algebra.FormallySmooth.liftOfSurjective_apply P' P hs (nil I P hk hJ) b
  have b1 := bij I hJ p hk (ψ.comp φ) fun b ↦ by simp [hψ, hφ]
  have b2 := bij I hJ' p' hk' (φ.comp ψ) fun b ↦ by simp [hψ, hφ]
  refine ⟨AlgEquiv.ofBijective φ ⟨fun x y h ↦ b1.1 (by simp [h]), fun c ↦ ?_⟩, hφ⟩
  obtain ⟨d, hd⟩ := b2.2 c
  exact ⟨ψ d, hd⟩

end GlobalTheory.LiftSys.LocalIsomorphism

namespace GlobalTheory.LiftSys

theorem locIso_nonempty : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀)
    (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀),
    ∀ S S' : Sys I π s₀, Nonempty (S.LocIso S') := by
  intro R R₀ _ _ I hI π _ _ X₀ s₀ S S'
  have h : ∀ U, ∃ φ : S.F.obj U ≃ₐ[R] S'.F.obj U, ∀ b, S'.p U (φ b) = S.p U b := fun U ↦ by
    haveI := (S.smooth U).formallySmooth
    haveI := (S'.smooth U).formallySmooth
    exact LocalIsomorphism.exists_iso I hI π (S.p U) (S'.p U) (S.semi U) (S'.semi U) (S.surj U) (S'.surj U)
      (S.ker U) (S'.ker U)
  exact ⟨⟨fun U ↦ (h U).choose, fun U ↦ (h U).choose_spec⟩⟩

end GlobalTheory.LiftSys
end
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LiftSys.Sys

variable {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} {π : R →+* R₀} {X₀ : Scheme.{0}}
  {s₀ : X₀ ⟶ Sp R₀}

theorem isPushout_chart (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (S : Sys I π s₀) (U : AffOp X₀) :
    IsPushout (CommRingCat.ofHom (algebraMap R (S.F.obj U))) (CommRingCat.ofHom π)
      (CommRingCat.ofHom (S.p U)) (CommRingCat.ofHom (algebraMap R₀ (Sec s₀ U.unop.1))) := by
  have hc : ∀ r : R, S.p U (algebraMap R (S.F.obj U) r) = algebraMap R₀ (Sec s₀ U.unop.1) (π r) :=
    fun r ↦ (S.semi U).map_algebraMap r
  have hz : ∀ a ∈ I, π a = 0 := fun a ha ↦ RingHom.mem_ker.1 (hk ▸ ha)
  have key : ∀ (t : Limits.PushoutCocone (CommRingCat.ofHom (algebraMap R (S.F.obj U))) (CommRingCat.ofHom π))
      (b : S.F.obj U), S.p U b = 0 → t.inl.hom b = 0 := by
    intro t b hb
    have hle : I.map (algebraMap R (S.F.obj U)) ≤ RingHom.ker t.inl.hom := by
      rw [Ideal.map_le_iff_le_comap]
      intro a ha
      have e : t.inl.hom (algebraMap R (S.F.obj U) a) = t.inr.hom (π a) := congr($(t.condition) a)
      rw [Ideal.mem_comap, RingHom.mem_ker, e, hz a ha, map_zero]
    exact hle ((S.ker U b).1 hb)
  let desc : ∀ t : Limits.PushoutCocone (CommRingCat.ofHom (algebraMap R (S.F.obj U))) (CommRingCat.ofHom π),
      Sec s₀ U.unop.1 →+* t.pt := fun t ↦
    (Ideal.Quotient.lift (RingHom.ker (S.p U)) t.inl.hom fun b hb ↦ key t b (RingHom.mem_ker.1 hb)).comp
      (RingHom.quotientKerEquivOfSurjective (S.surj U)).symm.toRingHom
  have hdesc : ∀ t b, desc t (S.p U b) = t.inl.hom b := by
    intro t b
    change Ideal.Quotient.lift _ t.inl.hom (fun b hb ↦ key t b (RingHom.mem_ker.1 hb)) ((RingHom.quotientKerEquivOfSurjective (S.surj U)).symm (S.p U b)) = _
    rw [show (RingHom.quotientKerEquivOfSurjective (S.surj U)).symm (S.p U b) = Ideal.Quotient.mk _ b by
      rw [RingEquiv.symm_apply_eq]; rfl]
    rfl
  refine ⟨⟨by ext r; exact hc r⟩, ⟨Limits.PushoutCocone.IsColimit.mk _
    (fun t ↦ CommRingCat.ofHom (desc t)) ?_ ?_ ?_⟩⟩
  · intro t
    ext b
    exact hdesc t b
  · intro t
    ext r
    obtain ⟨a, rfl⟩ := hπ r
    change desc t (algebraMap R₀ (Sec s₀ U.unop.1) (π a)) = t.inr.hom (π a)
    rw [← hc, hdesc]
    exact congr($(t.condition) a)
  · intro t m h₁ _
    ext c
    obtain ⟨b, rfl⟩ := S.surj U c
    change m.hom (S.p U b) = desc t (S.p U b)
    rw [hdesc]
    exact congr($h₁ b)

theorem spMap_p_surjective (hI : I ^ 2 = 0) (S : Sys I π s₀) (U : AffOp X₀) :
    Function.Surjective (spMap (S.p U)) := by
  intro x
  have hx : x ∈ Set.range (PrimeSpectrum.comap (S.p U)) := by
    rw [range_comap_of_surjective (f := S.p U) (hf := S.surj U)]
    intro b hb
    have hb' : b ∈ I.map (algebraMap R (S.F.obj U)) := (S.ker U b).1 hb
    have h2 : b * b ∈ I.map (algebraMap R (S.F.obj U)) ^ 2 := by
      rw [pow_two]; exact Ideal.mul_mem_mul hb' hb'
    rw [map_sq hI] at h2
    have h0 : b * b ∈ (x : PrimeSpectrum (S.F.obj U)).asIdeal := by
      rw [show b * b = 0 from h2]; exact zero_mem _
    exact (Ideal.IsPrime.mem_or_mem (PrimeSpectrum.isPrime (x : PrimeSpectrum (S.F.obj U))) h0).elim id id
  obtain ⟨z, hz⟩ := hx
  exact ⟨z, hz⟩

end GlobalTheory.LiftSys.Sys

namespace GlobalTheory.LiftSys.Sys

variable {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} {π : R →+* R₀} {X₀ : Scheme.{0}}
  {s₀ : X₀ ⟶ Sp R₀}

theorem Presents.apply_red {S : Sys I π s₀} {X : Scheme.{0}} {s : X ⟶ Sp R} {i : X₀ ⟶ X} (P : S.Presents s i)
    (U : AffOp X₀) (z : Sp (Sec s₀ U.unop.1)) : P.y U (spMap (S.p U) z) = i (affPt s₀ U.unop z) := by
  have e := congrArg (fun f : Sp (Sec s₀ U.unop.1) ⟶ X ↦ f z) (P.red U)
  simpa only [Scheme.Hom.comp_apply] using e

instance isOpenImmersion_affPt (U : X₀.affineOpens) : IsOpenImmersion (affPt s₀ U) :=
  IsAffineOpen.isOpenImmersion_fromSpec U.2

theorem Presents.preimage_eq (hI : I ^ 2 = 0) {S : Sys I π s₀} {X : Scheme.{0}} {s : X ⟶ Sp R} {i : X₀ ⟶ X}
    (hc : IsClosedImmersion i) (P : S.Presents s i) [∀ U, IsOpenImmersion (P.y U)] (U : AffOp X₀) :
    i ⁻¹ᵁ (P.y U).opensRange = (affPt s₀ U.unop).opensRange := by
  ext x
  simp only [Scheme.Hom.mem_preimage, Scheme.Hom.coe_opensRange, Set.mem_range]
  constructor
  · rintro ⟨w, hw⟩
    obtain ⟨z, rfl⟩ := spMap_p_surjective hI S U w
    refine ⟨z, i.isClosedEmbedding.injective ?_⟩
    rw [← P.apply_red, hw]
  · rintro ⟨z, rfl⟩
    exact ⟨_, P.apply_red U z⟩

end GlobalTheory.LiftSys.Sys


open GlobalTheory.LiftSys.Sys in
theorem GlobalTheory.LiftSys.presents_isLift : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), ∀ (S : Sys I π s₀) (X : Scheme.{0}) (s : X ⟶ Sp R) (i : X₀ ⟶ X), IsClosedImmersion i → Surjective i → S.Presents s i → IsPullback i s₀ s (spMap π) ∧ Smooth s := by
  intro R R₀ _ _ I hI π hπ hk X₀ s₀ S X s i hc hsurj P
  haveI : ∀ U, IsOpenImmersion (P.y U) := P.isOpen
  have hv : ∀ y : X, ∃ (U : AffOp X₀) (z : Sp (S.F.obj U)), P.y U z = y := by
    intro y
    obtain ⟨x, rfl⟩ := i.surjective y
    obtain ⟨_, ⟨V, hV, rfl⟩, hx, -⟩ := X₀.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    have hx' : x ∈ Set.range (affPt s₀ ⟨V, hV⟩) := by
      have e : Set.range (affPt s₀ ⟨V, hV⟩) = V := (show IsAffineOpen V from hV).range_fromSpec
      rw [e]; exact hx
    obtain ⟨z, rfl⟩ := hx'
    exact ⟨Opposite.op ⟨V, hV⟩, spMap (S.p _) z, P.apply_red _ z⟩
  constructor
  · refine Scheme.isPullback_of_openCover _ _ _ _ (Scheme.Cover.mkOfCovers (AffOp X₀) _ P.y hv) fun (U : AffOp X₀) ↦ ?_
    change IsPullback (Limits.pullback.snd i (P.y U)) (Limits.pullback.fst i (P.y U) ≫ s₀) (P.y U ≫ s) (spMap π)
    have h := IsOpenImmersion.isPullback (spMap (S.p U)) (affPt s₀ U.unop) (P.y U) i (P.red U).symm
      (P.preimage_eq hI hc U)
    have h' : IsPullback (spMap (S.p U)) (affPt s₀ U.unop ≫ s₀) (P.y U ≫ s) (spMap π) := by
      rw [affPt_w, P.base]
      exact isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_chart hπ hk S U)
    refine h'.of_iso h.flip.isoPullback (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_ <;> simp
  · have : IsZariskiLocalAtSource @Smooth := HasRingHomProperty.instIsZariskiLocalAtSource
    refine IsZariskiLocalAtSource.of_openCover (P := @Smooth) (Scheme.Cover.mkOfCovers (AffOp X₀) _ P.y hv) fun (U : AffOp X₀) ↦ ?_
    change Smooth (P.y U ≫ s)
    rw [P.base, HasRingHomProperty.Spec_iff (P := @Smooth)]
    haveI := S.smooth U
    exact RingHom.smooth_algebraMap.2 inferInstance
end
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LiftSys

open Opposite TopologicalSpace

theorem const_of_isAbelianScheme : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A],
    IsAbelianScheme A → Const A.hom := by
  intro R _ _ A _ hA
  have := hA.smooth
  have := hA.proper
  have := hA.geomConnected
  haveI : GeometricallyIntegral A.hom := GlobalTheory.geometricallyIntegral_of_smooth A.hom
  have hbij := ((GlobalTheory.ProperFunctions.functions_of_isProper).2.2 R A.left A.hom).1
  intro g hg
  have hc : ∀ (U V : A.left.affineOpens) (h : V.1 ≤ U.1),
      A.left.presheaf.map (homOfLE h).op (g (op U)) = g (op V) := by
    intro U V h
    have e := congrFun (congrFun (congrFun hg (op U)) (op V)) (homOfLE h).op
    exact (sub_eq_zero.1 e).symm
  obtain ⟨t, ht, -⟩ := A.left.sheaf.existsUnique_gluing' (fun U : A.left.affineOpens ↦ U.1) ⊤
    (fun _ ↦ homOfLE le_top) (iSup_affineOpens_eq_top A.left).ge (fun U ↦ g (op U)) (by
      intro U V
      refine A.left.sheaf.eq_of_locally_eq' (fun W : {W : A.left.affineOpens // W.1 ≤ U.1 ⊓ V.1} ↦ W.1.1)
        (U.1 ⊓ V.1) (fun W ↦ homOfLE W.2) ?_ _ _ fun W ↦ ?_
      · intro x hx
        obtain ⟨W, hW, hxW, hWUV⟩ := Opens.isBasis_iff_nbhd.mp A.left.isBasis_affineOpens hx
        exact Opens.mem_iSup.mpr ⟨⟨⟨W, hW⟩, hWUV⟩, hxW⟩
      · dsimp only
        have e : ∀ {a b c : Opens A.left} (f : b ⟶ a) (f' : c ⟶ b) (x : Γ(A.left, a)),
            A.left.presheaf.map f'.op (A.left.presheaf.map f.op x) = A.left.presheaf.map (f' ≫ f).op x := by
          intros; simp
        refine (e _ _ _).trans ((hc U W.1 (W.2.trans inf_le_left)).trans
          ((hc V W.1 (W.2.trans inf_le_right)).symm.trans (e _ _ _).symm)))
  obtain ⟨r, hr⟩ := hbij.2 t
  refine ⟨r, fun U ↦ ?_⟩
  rw [← ht U.unop, ← hr]
  rfl

end GlobalTheory.LiftSys
end
