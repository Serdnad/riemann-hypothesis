module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.FirstChernCompatibleSystem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle406
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Bundle001
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.Bundle001
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SEqOne
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalisationLadders.CriterionTruncation
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle127
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.SubThickRees
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle128
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
public import Mathlib.RingTheory.RootsOfUnity.Lemmas
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.CompanionTheory.PrimAlgProof

open Polynomial

theorem exists_universal (q : ℕ) [NeZero q] :
    ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (ξ : R), IsPrimitiveRoot ξ q ∧
      ∀ (A : Type) [CommRing A] (z : A), aeval z (cyclotomic q ℤ) = 0 →
        ∃ φ : R →+* A, φ ξ = z := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hlift : ∀ (A : Type) [CommRing A] (z : A), aeval z (cyclotomic q ℤ) = 0 →
      ∃ φ : AdjoinRoot (cyclotomic q ℤ) →+* A, φ (AdjoinRoot.root _) = z := by
    intro A _ z hz
    have h : (cyclotomic q ℤ).eval₂ (Int.castRingHom A) z = 0 := by
      rw [aeval_def] at hz
      simpa [eq_intCast] using hz
    exact ⟨AdjoinRoot.lift _ z h, AdjoinRoot.lift_root h⟩
  haveI hdom : IsDomain (AdjoinRoot (cyclotomic q ℤ)) :=
    AdjoinRoot.isDomain_of_prime (cyclotomic.irreducible hq).prime
  refine ⟨AdjoinRoot (cyclotomic q ℤ), inferInstance, hdom, AdjoinRoot.root _, ?_, hlift⟩
  obtain ⟨ψ, hψ⟩ := hlift ℂ (Complex.exp (2 * Real.pi * Complex.I / q)) (by
    have hp := Complex.isPrimitiveRoot_exp q (NeZero.ne q)
    have : IsRoot (cyclotomic q ℂ) (Complex.exp (2 * Real.pi * Complex.I / q)) :=
      (isRoot_cyclotomic_iff).2 hp
    rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic]
    exact this)
  haveI : NeZero ((q : ℕ) : AdjoinRoot (cyclotomic q ℤ)) := ⟨fun h0 => by
    have := congrArg ψ h0
    rw [map_natCast, map_zero] at this
    exact NeZero.ne q (by exact_mod_cast this)⟩
  refine (isRoot_cyclotomic_iff).1 ?_
  have h := AdjoinRoot.eval₂_root (cyclotomic q ℤ)
  rw [eval₂_eq_eval_map, map_cyclotomic] at h
  exact h

theorem X_pow_sub_one_eq {R : Type} [CommRing R] [IsDomain R] (q : ℕ) [NeZero q] {ξ : R}
    (hξ : IsPrimitiveRoot ξ q) :
    (X ^ q - 1 : R[X]) = ∏ a : ZMod q, (X - C (ξ ^ a.val)) := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  rw [X_pow_sub_one_eq_prod hq hξ]
  symm
  refine Finset.prod_bij (fun a _ => ξ ^ a.val) ?_ ?_ ?_ ?_
  · intro a _
    rw [mem_nthRootsFinset hq]
    rw [← pow_mul, mul_comm, pow_mul, hξ.pow_eq_one, one_pow]
  · intro a _ b _ h
    exact ZMod.val_injective q (hξ.pow_inj (ZMod.val_lt a) (ZMod.val_lt b) h)
  · intro μ hμ
    rw [mem_nthRootsFinset hq] at hμ
    obtain ⟨i, hi, rfl⟩ := hξ.eq_pow_of_pow_eq_one hμ
    exact ⟨(i : ZMod q), Finset.mem_univ _, by rw [ZMod.val_cast_of_lt hi]⟩
  · intro a _
    rfl

theorem cyclotomic_eq {R : Type} [CommRing R] [IsDomain R] (q : ℕ) [NeZero q] {ξ : R}
    (hξ : IsPrimitiveRoot ξ q) :
    cyclotomic q R = ∏ a : (ZMod q)ˣ, (X - C (ξ ^ (a : ZMod q).val)) := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  rw [cyclotomic_eq_prod_X_sub_primitiveRoots hξ]
  symm
  refine Finset.prod_bij (fun a _ => ξ ^ (a : ZMod q).val) ?_ ?_ ?_ ?_
  · intro a _
    rw [mem_primitiveRoots hq]
    exact hξ.pow_of_coprime _ (ZMod.val_coe_unit_coprime a)
  · intro a _ b _ h
    exact Units.ext (ZMod.val_injective q (hξ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h))
  · intro μ hμ
    rw [mem_primitiveRoots hq] at hμ
    obtain ⟨i, hi, rfl⟩ := hξ.eq_pow_of_pow_eq_one hμ.pow_eq_one
    have hc : Nat.Coprime i q := (hξ.pow_iff_coprime hq i).1 hμ
    refine ⟨ZMod.unitOfCoprime i hc, Finset.mem_univ _, ?_⟩
    simp only [ZMod.coe_unitOfCoprime]
    rw [ZMod.val_cast_of_lt hi]
  · intro a _
    rfl

theorem isUnit_one_sub_pow {R A : Type} [CommRing R] [IsDomain R] [CommRing A] (n : ℕ) {ξ : R}
    (hξ : IsPrimitiveRoot ξ (n + 1)) (φ : R →+* A) (hu : IsUnit ((n + 1 : ℕ) : A))
    (k : ℕ) (hk : k < n) : IsUnit (1 - φ ξ ^ (k + 1)) := by
  have h := congrArg φ hξ.prod_one_sub_pow_eq_order
  rw [map_prod] at h
  have hn : φ ((n : R) + 1) = ((n + 1 : ℕ) : A) := by simp
  have hd : φ (1 - ξ ^ (k + 1)) ∣ ∏ i ∈ Finset.range n, φ (1 - ξ ^ (i + 1)) :=
    Finset.dvd_prod_of_mem _ (Finset.mem_range.2 hk)
  rw [h, hn] at hd
  have := isUnit_of_dvd_unit hd hu
  simpa using this

theorem primAlg : CrystallineSemistableComparison.E.PrimAlg := by
  intro q _ A _ ζ
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  obtain ⟨R, _, _, ξ, hξ, hl⟩ := exists_universal q
  obtain ⟨φ, hφ⟩ := hl A ζ.1 ζ.2.2
  have hpow : ζ.1 ^ q = 1 := by rw [← hφ, ← map_pow, hξ.pow_eq_one, map_one]
  have hζu : IsUnit ζ.1 := by
    refine IsUnit.of_mul_eq_one (ζ.1 ^ (q - 1)) ?_
    rw [← pow_succ', Nat.sub_add_cancel hq, hpow]
  have h1 : ∀ k, 0 < k → k < q → IsUnit (1 - ζ.1 ^ k) := by
    intro k hk0 hkq
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne q)
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0.ne'
    subst hn
    have := isUnit_one_sub_pow n hξ φ ζ.2.1 m (by omega)
    rwa [hφ] at this
  have hlt : ∀ a b : ℕ, a < b → b < q → IsUnit (ζ.1 ^ a - ζ.1 ^ b) := by
    intro a b hab hb
    have : ζ.1 ^ a - ζ.1 ^ b = ζ.1 ^ a * (1 - ζ.1 ^ (b - a)) := by
      rw [mul_sub, mul_one, ← pow_add, Nat.add_sub_cancel' hab.le]
    rw [this]
    exact (hζu.pow a).mul (h1 _ (by omega) (by omega))
  refine ⟨hpow, ?_, ?_, ?_⟩
  · intro a b hab
    have hv : a.val ≠ b.val := fun h => hab (ZMod.val_injective q h)
    rcases lt_or_gt_of_ne hv with h | h
    · exact hlt _ _ h (ZMod.val_lt b)
    · have := (hlt _ _ h (ZMod.val_lt a)).neg
      rwa [neg_sub] at this
  · intro r
    have h := congrArg (fun p => eval r (p.map φ)) (X_pow_sub_one_eq q hξ)
    simpa [Polynomial.map_prod, eval_prod, hφ] using h
  · intro r
    have h := congrArg (fun p => eval r (p.map φ)) (cyclotomic_eq q hξ)
    simp only [map_cyclotomic, Polynomial.map_prod, eval_prod] at h
    rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic, h]
    simp [hφ]

end GlobalTheory.CompanionTheory.PrimAlgProof
end
end

section

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.KapBij

section Res

variable {R : Type} [CommRing R] {F : Shv R}

theorem res_smul {V U : Scheme.{0}} (g : V ⟶ U) (c : ULift.{1} R) (a : Sec F U) :
    Sec.res g (c • a) = c • Sec.res g a :=
  map_smul _ _ _

theorem res_res {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (a : Sec F U) :
    Sec.res k (Sec.res g a) = Sec.res (k ≫ g) a := by
  show (F.obj.map k.op).hom ((F.obj.map g.op).hom a) = (F.obj.map (k ≫ g).op).hom a
  rw [op_comp, F.obj.map_comp]
  rfl

end Res

theorem nsmul_eq_up {q : ℕ} {M : Type*} [AddCommGroup M] [Module (ULift.{1} (ZMod q)) M] (c : ℕ) (t : M) :
    c • t = (ULift.up (c : ZMod q) : ULift.{1} (ZMod q)) • t := by
  rw [← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q))]
  congr 1

theorem coef_eq_zero (hg : InGen) {q : ℕ} [NeZero q] (i : ℤ) {V : Scheme.{0}} [Nonempty V]
    (ζ : Prim q Γ(V, ⊤)) (a : ZMod q)
    (h : (ULift.up a : ULift.{1} (ZMod q)) • twGen i ζ = 0) : a = 0 := by
  have hq : q ∣ a.val := (hg q i).2.1 V ζ a.val (by
    rw [nsmul_eq_up (q := q), ZMod.natCast_zmod_val]
    exact h)
  rw [← ZMod.natCast_zmod_val a]
  exact (ZMod.natCast_eq_zero_iff _ _).2 hq

theorem coef_unique (hg : InGen) {q : ℕ} [NeZero q] (i : ℤ) {V : Scheme.{0}} [Nonempty V]
    (ζ : Prim q Γ(V, ⊤)) (a b : ZMod q)
    (h : (ULift.up a : ULift.{1} (ZMod q)) • twGen i ζ = (ULift.up b : ULift.{1} (ZMod q)) • twGen i ζ) :
    a = b := by
  refine sub_eq_zero.1 (coef_eq_zero hg i ζ _ ?_)
  have e : (ULift.up (a - b) : ULift.{1} (ZMod q)) = ULift.up a - ULift.up b := rfl
  rw [e, sub_smul, h, sub_self]

theorem coef_agree (hR : RepRoot) (hg : InGen) {q : ℕ} [NeZero q] (i : ℤ) {U : Scheme.{0}}
    (ζ : Prim q Γ(U, ⊤)) (x : Sec (tw q i) U) {V V' : Scheme.{0}} (g : V ⟶ U) (g' : V' ⟶ U)
    (c c' : ZMod q)
    (h : Sec.res g x = (ULift.up c : ULift.{1} (ZMod q)) • Sec.res g (twGen i ζ))
    (h' : Sec.res g' x = (ULift.up c' : ULift.{1} (ZMod q)) • Sec.res g' (twGen i ζ))
    (v : V) (v' : V') (hv : g v = g' v') : c = c' := by
  obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback v v' hv
  have : Nonempty ↑(pullback g g') := ⟨z⟩
  have e1 : Sec.res (pullback.fst g g' ≫ g) x =
      (ULift.up c : ULift.{1} (ZMod q)) • Sec.res (pullback.fst g g' ≫ g) (twGen i ζ) := by
    rw [← res_res, h, res_smul, res_res]
  have e2 : Sec.res (pullback.fst g g' ≫ g) x =
      (ULift.up c' : ULift.{1} (ZMod q)) • Sec.res (pullback.fst g g' ≫ g) (twGen i ζ) := by
    rw [pullback.condition, ← res_res, h', res_smul, res_res]
  rw [((hR q i U ζ).1 _ (pullback.fst g g' ≫ g)).1] at e1 e2
  exact coef_unique hg i _ c c' (e1.symm.trans e2)

theorem exists_chart (hR : RepRoot) (hg : InGen) {q : ℕ} [NeZero q] (i : ℤ) {U : Scheme.{0}}
    (ζ : Prim q Γ(U, ⊤)) (x : Sec (tw q i) U) (u : U) :
    ∃ (V : Scheme.{0}) (g : V ⟶ U), IsAffine V ∧ Etale g ∧ u ∈ Set.range g ∧
      ∃ c : ZMod q, Sec.res g x = (ULift.up c : ULift.{1} (ZMod q)) • Sec.res g (twGen i ζ) := by
  refine (loc_iff_etale_affine_points U
    (fun V g => ∃ c : ZMod q, Sec.res g x = (ULift.up c : ULift.{1} (ZMod q)) • Sec.res g (twGen i ζ))
    ?_).1 ?_ u
  · rintro V W g k ⟨c, hc⟩
    exact ⟨c, by rw [← res_res, hc, res_smul, res_res]⟩
  · obtain ⟨S, hS, hc⟩ := (hg q i).1 U ζ x
    refine ⟨S, hS, fun V g hgS => ?_⟩
    obtain ⟨c, hc⟩ := hc V g hgS
    refine ⟨(c : ZMod q), ?_⟩
    rw [hc, nsmul_eq_up (q := q), ((hR q i U ζ).1 V g).1]
    rfl

theorem kap_injective (hK : KapSpec) (hg : InGen) {q : ℕ} [NeZero q] (i : ℤ) {U : Scheme.{0}}
    (ζ : Prim q Γ(U, ⊤)) : Function.Injective (kap i ζ) := by
  refine (injective_iff_map_eq_zero (kap i ζ)).2 fun f hf => LocallyConstant.ext fun u => ?_
  let O : U.Opens := ⟨f ⁻¹' {f u}, f.isLocallyConstant.isOpen_fiber _⟩
  have : Nonempty O.toScheme := ⟨⟨u, rfl⟩⟩
  have hO : ∀ v : O.toScheme, f (O.ι v) = f u := fun v => by
    have : O.ι v ∈ Set.range O.ι := ⟨v, rfl⟩
    rw [Scheme.Opens.range_ι] at this
    exact this
  have h := (hK q i U ζ f).1 O.toScheme O.ι (f u) hO
  rw [hf] at h
  have h0 : Sec.res O.ι (0 : Sec (tw q i) U) = 0 := map_zero _
  rw [h0] at h
  exact coef_eq_zero hg i _ _ h.symm

theorem kap_surjective (hR : RepRoot) (hK : KapSpec) (hg : InGen) {q : ℕ} [NeZero q] (i : ℤ)
    {U : Scheme.{0}} (ζ : Prim q Γ(U, ⊤)) : Function.Surjective (kap i ζ) := by
  intro x
  choose V g hA hE hu c hc using exists_chart hR hg i ζ x
  choose y hy using hu
  have hagree : ∀ (u : U) (v : V u), c (g u v) = c u := fun u v =>
    coef_agree hR hg i ζ x (g (g u v)) (g u) _ _ (hc _) (hc u) (y _) v (hy _)
  have hop : ∀ u, IsOpen (Set.range (g u)) := fun u => by
    have := hE u
    exact (g u).isOpenMap.isOpen_range
  let f : LocallyConstant U (ZMod q) := ⟨c, (IsLocallyConstant.iff_exists_open c).2 fun u =>
    ⟨Set.range (g u), hop u, ⟨y u, hy u⟩, by
      rintro _ ⟨v, rfl⟩
      exact hagree u v⟩⟩
  refine ⟨f, ((sec_ext_glue _ _ U).1 _ _ ?_)⟩
  refine (loc_iff_etale_affine_points U (fun V g => Sec.res g (kap i ζ f) = Sec.res g x) ?_).2 fun u => ?_
  · intro V W g k h
    rw [← res_res, h, res_res]
  · refine ⟨V u, g u, hA u, hE u, ⟨y u, hy u⟩, ?_⟩
    have h := (hK q i U ζ f).1 (V u) (g u) (c u) (hagree u)
    rw [h, hc u, ((hR q i U ζ).1 _ (g u)).1]

theorem kapBij : LcCover → RepRoot → KapSpec → KapBij := fun _ hR hK hg q _ i _ ζ =>
  ⟨kap_injective hK hg i ζ, kap_surjective hR hK hg i ζ⟩

end GlobalTheory.CompanionTheory.KapBij
end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.Cone

universe w v u

theorem HU_subsingleton_of_obj {R : Type} [CommRing R] {C : Type u} [Category.{v} C]
    (F : C ⥤ ModuleCat.{w} R) (U : ObjectProperty C) (j : ℕ)
    (h : ∀ T : C, Subsingleton (F.obj T)) : Subsingleton (HU F U j) := by
  have hC : Subsingleton (CH.Cn (U.ι ⋙ F) j) :=
    ⟨fun f g => funext fun s => (h _).elim _ _⟩
  have hZ : Subsingleton ((CH.cx (U.ι ⋙ F)).Z j) :=
    ⟨fun x y => Subtype.ext (hC.elim _ _)⟩
  refine ⟨fun x y => ?_⟩
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  exact congrArg _ (hZ.elim x y)

theorem sq_obj_subsingleton {R : Type} [CommRing R] {C : Type u} [Category.{v} C]
    {A : C ⥤ CommAlgCat.{0} R} (a b : IdF A) (T : C) (h : a.S T = b.S T) :
    Subsingleton ((sq a b).obj T) := by
  have h0 : ∀ x : sqM a b T, x = 0 := by
    rintro ⟨x, hx⟩
    obtain ⟨y, hy, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hx
    refine Subtype.ext ?_
    exact Ideal.Quotient.eq_zero_iff_mem.2 (h ▸ hy)
  exact ⟨fun x y => (h0 x).trans (h0 y).symm⟩

theorem HU_gr_neg {b : Base} (L : b.Fun) (Q : ObjectProperty (Thick L)) (r : ℤ) (hr : r < 0) (j : ℕ) :
    Subsingleton (HU (gr (Φ := thP L) (thFil L) r) Q j) := by
  refine HU_subsingleton_of_obj _ Q j fun T => sq_obj_subsingleton _ _ T ?_
  have e : r.toNat = (r + 1).toNat := by omega
  change T.pdPow r.toNat = T.pdPow (r + 1).toNat
  rw [e]

end GlobalTheory.CompanionTheory.Cone
end

section

open DividedPowers CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.DPFiltration

theorem dpow_mem_span_pow {B : Type} [CommRing B] [Algebra ℚ B] {x : B}
    (δ : DividedPowers (Ideal.span {x})) (k : ℕ) {y : B} (hy : y ∈ Ideal.span {x}) :
    δ.dpow k y ∈ Ideal.span {x ^ k} := by
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hy
  rw [DividedPowers.RatAlgebra.dpow_eq_inv_fact_smul _ δ hy, Algebra.smul_def, mul_pow]
  exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _))

theorem list_prod_dpow_mem {B : Type} [CommRing B] [Algebra ℚ B] {x : B}
    (δ : DividedPowers (Ideal.span {x})) (l : List (ℕ × B))
    (hl : ∀ q ∈ l, q.2 ∈ Ideal.span {x}) :
    (l.map fun q => δ.dpow q.1 q.2).prod ∈ Ideal.span {x ^ (l.map Prod.fst).sum} := by
  induction l with
  | nil => simp
  | cons q l ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons, pow_add]
    have h1 := dpow_mem_span_pow δ q.1 (hl q (by simp))
    have h2 := ih (fun q' hq' => hl q' (by simp [hq']))
    rw [Ideal.mem_span_singleton] at h1 h2 ⊢
    exact mul_dvd_mul h1 h2

theorem dividedPowerFiltration_span_singleton {B : Type} [CommRing B] [Algebra ℚ B] (x : B)
    (δ : DividedPowers (Ideal.span {x})) (r : ℕ) :
    CrystallineSemistableComparison.Pb.pdP δ r = Ideal.span {x ^ r} := by
  apply le_antisymm
  · unfold CrystallineSemistableComparison.Pb.pdP
    rw [Ideal.span_le]
    rintro z ⟨l, hl, hr, rfl⟩
    have h := list_prod_dpow_mem δ l hl
    rw [Ideal.mem_span_singleton] at h
    rw [SetLike.mem_coe, Ideal.mem_span_singleton]
    exact (pow_dvd_pow x hr).trans h
  · rw [Ideal.span_singleton_le_iff_mem]
    unfold CrystallineSemistableComparison.Pb.pdP
    apply Ideal.subset_span
    refine ⟨List.replicate r (1, x), ?_, ?_, ?_⟩
    · intro q hq
      rw [List.eq_of_mem_replicate hq]
      exact Ideal.mem_span_singleton_self x
    · simp
    · simp [δ.dpow_one (Ideal.mem_span_singleton_self x)]

theorem pdP_γB {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W) (r : ℕ) :
    pdP (Lat.γB f ξ) r = Ideal.span {f ξ ^ r} :=
  dividedPowerFiltration_span_singleton (f ξ) (Lat.γB f ξ) r

end GlobalTheory.CompanionTheory.DPFiltration
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.Pb

theorem _root_.GlobalTheory.T.frame_form_restriction_cocycle : ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} (Q : Poly Φ) {Fil : ℤ → IdF Φ.A}
    (hF : IsFil Φ Fil) {d : ℕ} (E : Frame Φ (d + 1)) (σ : ∀ T : C, E.D ⟶ T) (hc : E.GrConst Fil) (j q : ℕ) (r : ℤ) (hr : r = j + q)
    (I : Fin j → Fin d) (x : Φ.A.obj E.D) (hx : x ∈ (Fil q).S E.D)
    (f : CH.Cn (Cut.U E ⋙ gr Fil r) j) (g : CH.Cn (gr Fil r) j),
    (∀ s, (show sqM _ _ _ from f s).1 = Ideal.Quotient.mk _ ((Cut.E1 E).form Cut.can I x s)) →
    (∀ s, (show sqM _ _ _ from g s).1 = Ideal.Quotient.mk _ (E.form σ (Fin.succ ∘ I) x s)) →
    (CH.Mor.restrict (Cut.U E ⋙ gr Fil r) (Cut.Pσ Q σ)).pullC j f =
      (CH.Mor.ofNatTrans (Functor.whiskerRight (Cut.jσ Q σ) (gr Fil r))).pullC j g := by
  first | exact @GlobalTheory.CompanionTheory.GrPull.gr_pull | exact GlobalTheory.CompanionTheory.GrPull.gr_pull | (intros; apply GlobalTheory.CompanionTheory.GrPull.gr_pull <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.Pb

theorem _root_.GlobalTheory.T.frame_form_coboundary_relation : ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} (Q : Poly Φ) {Fil : ℤ → IdF Φ.A}
    (hF : IsFil Φ Fil) {d : ℕ} (E : Frame Φ (d + 1)) (σ : ∀ T : C, E.D ⟶ T) (hc : E.GrConst Fil) (j q : ℕ) (r : ℤ)
    (hr : r = j + 1 + q) (I : Fin j → Fin d) (x : Φ.A.obj E.D) (hx : x ∈ (Fil q).S E.D)
    (y : CH.Cn (Cut.Pσ Q σ ⋙ Cut.U E ⋙ gr Fil r) j) (w : CH.Cn (gr Fil r) (j + 1)),
    (∀ s, (show sqM _ _ _ from y s).1 = Ideal.Quotient.mk _
      ((Q.X (s.obj (Fin.last j)) + (Φ.A.map (Q.j _)).hom (E.a σ 0 (s.map (homOfLE (Fin.zero_le (Fin.last j)))))) *
        (Φ.A.map (Q.j _)).hom (E.form σ (Fin.succ ∘ I) x s))) →
    (∀ s, (show sqM _ _ _ from w s).1 = Ideal.Quotient.mk _ (E.form σ (Fin.cons 0 (Fin.succ ∘ I)) x s)) →
    CH.d _ j y = -(CH.Mor.ofNatTrans (Functor.whiskerRight (Cut.jσ Q σ) (gr Fil r))).pullC (j + 1) w := by
  first | exact @GlobalTheory.CompanionTheory.GrDelta.gr_delta | exact GlobalTheory.CompanionTheory.GrDelta.gr_delta | (intros; apply GlobalTheory.CompanionTheory.GrDelta.gr_delta <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb
attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.CompanionTheory.GeoFT

theorem finiteType_affine {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))
    [LocallyOfFiniteType q] {W : X.Opens} (hW : IsAffineOpen W) :
    letI := (strV q W).toAlgebra; Algebra.FiniteType K Γ(X, W) := by
  have h1 : (q.appLE ⊤ W le_top).hom.FiniteType :=
    HasRingHomProperty.appLE (P := @LocallyOfFiniteType) q inferInstance
      ⟨⊤, isAffineOpen_top _⟩ ⟨W, hW⟩ le_top
  have h2 : (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom.FiniteType :=
    RingHom.FiniteType.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv).2
  have h3 : (strV q W).FiniteType := by
    have : strV q W = (q.appLE ⊤ W le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom := rfl
    rw [this]
    exact h1.comp h2
  letI := (strV q W).toAlgebra
  exact RingHom.finiteType_algebraMap.1 h3

end GlobalTheory.CompanionTheory.GeoFT
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Polynomial DividedPowers GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B

theorem _root_.GlobalTheory.T.exists_lift_to_thickening : ∀ {O : Type} [CommRing O] {F : Fn O} {d : ℕ} (s : F.Small d) {b : Base} (ht : b.t = 1) {κ : O →+* b.R ⧸ b.I} (𝓛 : Lift s.a (fun k => (s.T k : s.R)) b.R b.I κ) (δ : DividedPowers (b.I.map 𝓛.i)) (hδ : IsDPMorphism b.γ δ 𝓛.i) (hp : b.p ≠ 0) (hn : IsNilpotent (b.p : b.R)) (T : Thick (F.cr b ht κ)), ∃ g : s.R →+* T.B ⧸ T.J, (∀ (c : liftObj s ht 𝓛 δ hδ hp hn ⟶ T) (r : s.R) (z : 𝓛.D), Ideal.Quotient.mk _ z = 𝓛.j r → Ideal.Quotient.mk T.J (c.φ z) = g r) ∧ F.Pt.map (CommRingCat.ofHom g) s.y₀ = T.y.1.2 ∧ ∀ u : Fin d → T.B, (∀ k, Ideal.Quotient.mk T.J (u k) = g (s.T k)) → ∃! c : liftObj s ht 𝓛 δ hδ hp hn ⟶ T, ∀ k, c.φ (𝓛.t k) = u k := by
  first | exact @GlobalTheory.CompanionTheory.ThickHom.main | exact GlobalTheory.CompanionTheory.ThickHom.main | (intros; apply GlobalTheory.CompanionTheory.ThickHom.main <;> assumption)
end
