module

public import Development.EtaleCohomology.EtaleSheaves.Bundle026
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.EtaleCohomology.EtaleSheaves.Bundle027
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteMaximalSpectrumOfFiniteOfIsLocalRing
public import Development.EtaleCohomology.EtaleSheaves.Bundle028
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.Lemma
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
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.ResBijPf

def TwSec : Prop :=
  ∀ (q : ℕ) [NeZero q] (i : ℤ), (∀ (U : Scheme.{0}) (y : Sec (tw q i) U), Loc U fun V g => Sec.res g y = 0 ∨ ∃ (ζ : Prim q Γ(V, ⊤)) (c : ℕ), Sec.res g y = c • twGen i ζ) ∧ (∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (y : Sec (tw q i) U), Loc U fun V g => ∃ c : ℕ, Sec.res g y = c • twGen i (ζ.map g.appTop.hom)) ∧ (∀ (U : Scheme.{0}) [Nonempty U] (ζ : Prim q Γ(U, ⊤)) (c : ℕ), c • twGen i ζ = 0 → q ∣ c) ∧ (∀ (V U : Scheme.{0}) (g : V ⟶ U) (ζ : Prim q Γ(U, ⊤)), Sec.res g (twGen i ζ) = twGen i (ζ.map g.appTop.hom)) ∧ (∀ (U : Scheme.{0}) (ζ ξ : Prim q Γ(U, ⊤)) (a : (ZMod q)ˣ), ξ.1 = ζ.1 ^ (a : ZMod q).val → twGen i ξ = ((a ^ i : (ZMod q)ˣ) : ZMod q).val • twGen i ζ) ∧ ∀ (M : Shv (ZMod q)) (e : ∀ U : Scheme.{0}, Prim q Γ(U, ⊤) → Sec M U), (∀ (V U : Scheme.{0}) (g : V ⟶ U) ζ, Sec.res g (e U ζ) = e V (ζ.map g.appTop.hom)) → (∀ (U : Scheme.{0}) (ζ ξ : Prim q Γ(U, ⊤)) (a : (ZMod q)ˣ), ξ.1 = ζ.1 ^ (a : ZMod q).val → e U ξ = ((a ^ i : (ZMod q)ˣ) : ZMod q).val • e U ζ) → ∃! φ : tw q i ⟶ M, ∀ U ζ, Sec.map φ (twGen i ζ) = e U ζ

theorem res_comp' {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (g : W ⟶ V) (h : V ⟶ U) (x : Sec F U) :
    Sec.res (g ≫ h) x = Sec.res g (Sec.res h x) := by
  simp [Sec.res]

theorem res_nsmul' {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (n : ℕ) (x : Sec F U) :
    Sec.res g (n • x) = n • Sec.res g x := map_nsmul _ n x

theorem sep' {R : Type} [CommRing R] {F : Shv R} {U : Scheme.{0}} (S : Sieve U) (hS : S ∈ Scheme.etaleTopology U)
    (y z : Sec F U) (h : ∀ (V : Scheme.{0}) (g : V ⟶ U), S.arrows g → Sec.res g y = Sec.res g z) : y = z := by
  have h1 := (isSheaf_iff_isSheaf_of_type _ _).1
    ((Presheaf.isSheaf_iff_isSheaf_forget _ F.obj (forget (ModuleCat.{1} (ULift.{1} R)))).1 F.property)
  exact (h1 S hS).isSeparatedFor.ext (fun V g hg => h V g hg)

theorem sec_empty {R : Type} [CommRing R] {F : Shv R} {U : Scheme.{0}} [IsEmpty U] (y z : Sec F U) : y = z :=
  sep' ⊥ (Scheme.bot_mem_grothendieckTopology U) y z (fun _ _ h => h.elim)

variable {q : ℕ} {i : ℤ}

theorem smul_mod {U : Scheme.{0}} (G : Sec (tw q i) U) (a : ℕ) : a • G = (a % q) • G := by
  have hq : q • G = 0 := by
    rw [← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q))]
    have : ((q : ℕ) : ULift.{1} (ZMod q)) = 0 := by
      ext; simp
    rw [this, zero_smul]
  conv_lhs => rw [← Nat.mod_add_div a q]
  rw [add_smul, mul_comm, mul_smul, hq, smul_zero, add_zero]

theorem smul_eq_of_cast {U : Scheme.{0}} (G : Sec (tw q i) U) {a b : ℕ} (h : (a : ZMod q) = b) : a • G = b • G := by
  rw [smul_mod G a, smul_mod G b, (ZMod.natCast_eq_natCast_iff' a b q).1 h]

theorem cast_of_smul_eq (hT : TwSec) [NeZero q] {U : Scheme.{0}} [Nonempty U] (ζ : Prim q Γ(U, ⊤)) {a b : ℕ}
    (h : a • twGen i ζ = b • twGen i ζ) : (a : ZMod q) = b := by
  rw [ZMod.natCast_eq_natCast_iff']
  rw [smul_mod _ a, smul_mod _ b] at h
  have ha := Nat.mod_lt a (NeZero.pos q)
  have hb := Nat.mod_lt b (NeZero.pos q)
  have key : ∀ x y : ℕ, x < q → y < q → x ≤ y → x • twGen i ζ = y • twGen i ζ → x = y := by
    intro x y hx hy hxy he
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hxy
    rw [add_smul] at he
    have hd : d • twGen i ζ = 0 := by
      have := congrArg (fun t => t - x • twGen i ζ) he
      simpa using this.symm
    have := (hT q i).2.2.1 U ζ d hd
    have : d = 0 := Nat.eq_zero_of_dvd_of_lt this (by omega)
    omega
  rcases le_total (a % q) (b % q) with hab | hab
  · exact key _ _ ha hb hab h
  · exact (key _ _ hb ha hab h.symm).symm

end LateralTheory.E.ResBijPf

namespace LateralTheory.E.ResBijPf
variable {q : ℕ} {i : ℤ}

theorem surj (hT : TwSec) [NeZero q] {U : Scheme.{0}} [ConnectedSpace U] (ζ : Prim q Γ(U, ⊤))
    (s : Sec (tw q i) U) : ∃ k : ℕ, s = k • twGen i ζ := by
  obtain ⟨S, hS, hSP⟩ := (hT q i).2.1 U ζ s
  obtain ⟨𝒰, hle⟩ := Scheme.exists_cover_of_mem_grothendieckTopology hS
  have hcov := (Scheme.presieve₀_mem_precoverage_iff 𝒰.toPreZeroHypercover).1 𝒰.mem₀
  have hgen : ∀ {V : Scheme.{0}} (g : V ⟶ U) (n : ℕ),
      n • twGen i (ζ.map g.appTop.hom) = Sec.res g (n • twGen i ζ) := by
    intro V g n
    rw [res_nsmul', (hT q i).2.2.2.1]
  have hc : ∀ j, ∃ c : ℕ, Sec.res (𝒰.f j) s = Sec.res (𝒰.f j) (c • twGen i ζ) := by
    intro j
    obtain ⟨c, hc⟩ := hSP _ _ (hle _ (𝒰.f j) (Presieve.ofArrows.mk j))
    exact ⟨c, hc.trans (hgen _ _)⟩
  choose c hc using hc
  have compat : ∀ j j' (x : 𝒰.X j) (x' : 𝒰.X j'), 𝒰.f j x = 𝒰.f j' x' → (c j : ZMod q) = c j' := by
    intro j j' x x' hx
    obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback x x' hx
    have : Nonempty ↑(pullback (𝒰.f j) (𝒰.f j') : Scheme.{0}) := ⟨z⟩
    have e1 : Sec.res (pullback.fst (𝒰.f j) (𝒰.f j') ≫ 𝒰.f j) s =
        Sec.res (pullback.fst (𝒰.f j) (𝒰.f j') ≫ 𝒰.f j) (c j • twGen i ζ) := by
      rw [res_comp', hc j, ← res_comp']
    have e2 : Sec.res (pullback.fst (𝒰.f j) (𝒰.f j') ≫ 𝒰.f j) s =
        Sec.res (pullback.fst (𝒰.f j) (𝒰.f j') ≫ 𝒰.f j) (c j' • twGen i ζ) := by
      rw [pullback.condition, res_comp', hc j', ← res_comp']
    rw [← hgen] at e1 e2
    exact cast_of_smul_eq hT _ (e1.symm.trans e2)
  have hopen : ∀ j, IsOpen (Set.range (𝒰.f j)) := by
    intro j
    have := hcov.2 j
    exact (𝒰.f j).isOpenMap.isOpen_range
  obtain ⟨x0⟩ := (inferInstance : Nonempty U)
  obtain ⟨j0, y0, hy0⟩ := hcov.1 x0
  have claim : ∀ j (y : 𝒰.X j), (c j : ZMod q) = c j0 := by
    intro j y
    by_contra hne
    have hpc := (isPreconnected_univ (α := U))
      (⋃ (j : 𝒰.I₀) (_ : (c j : ZMod q) = c j0), Set.range (𝒰.f j))
      (⋃ (j : 𝒰.I₀) (_ : (c j : ZMod q) ≠ c j0), Set.range (𝒰.f j))
      (isOpen_iUnion fun j => isOpen_iUnion fun _ => hopen j)
      (isOpen_iUnion fun j => isOpen_iUnion fun _ => hopen j)
      (by
        intro x _
        obtain ⟨j', y', hy'⟩ := hcov.1 x
        by_cases h : (c j' : ZMod q) = c j0
        · exact Or.inl (Set.mem_iUnion₂.2 ⟨j', h, y', hy'⟩)
        · exact Or.inr (Set.mem_iUnion₂.2 ⟨j', h, y', hy'⟩))
      ⟨x0, trivial, Set.mem_iUnion₂.2 ⟨j0, rfl, y0, hy0⟩⟩
      ⟨𝒰.f j y, trivial, Set.mem_iUnion₂.2 ⟨j, hne, y, rfl⟩⟩
    obtain ⟨x, -, hA, hB⟩ := hpc
    obtain ⟨j1, h1, y1, hy1⟩ := Set.mem_iUnion₂.1 hA
    obtain ⟨j2, h2, y2, hy2⟩ := Set.mem_iUnion₂.1 hB
    exact h2 ((compat j2 j1 y2 y1 (hy2.trans hy1.symm)).trans h1)
  refine ⟨c j0, sep' _ (Scheme.Cover.mem_grothendieckTopology 𝒰) _ _ ?_⟩
  rintro V g ⟨W, h, g', hg', rfl⟩
  cases hg' with
  | mk j =>
    rw [res_comp', res_comp', hc j]
    congr 1
    rcases isEmpty_or_nonempty (𝒰.X j) with he | ⟨⟨y⟩⟩
    · exact sec_empty _ _
    · rw [smul_eq_of_cast _ (claim j y)]

theorem gen_bij (hT : TwSec) [NeZero q] {U : Scheme.{0}} [ConnectedSpace U] (ζ : Prim q Γ(U, ⊤)) :
    Function.Bijective (fun k : ZMod q => k.val • twGen i ζ) := by
  refine ⟨fun k k' h => ?_, fun s => ?_⟩
  · have := cast_of_smul_eq hT ζ h
    simpa using this
  · obtain ⟨n, rfl⟩ := surj (i := i) hT ζ s
    refine ⟨(n : ZMod q), smul_eq_of_cast _ ?_⟩
    simp

theorem ResBij_of (hT : TwSec) : LateralTheory.E.HZeroPf.ResBij := by
  intro q i Y X f hY hX ⟨ζ⟩
  have : NeZero q := ⟨fun h0 => by
    subst h0
    obtain ⟨x⟩ := (inferInstance : Nonempty X)
    have : Nonempty (⊤ : X.Opens) := ⟨⟨x, trivial⟩⟩
    have h := ζ.2.1
    simp only [Nat.cast_zero, isUnit_zero_iff] at h
    exact zero_ne_one h⟩
  have h1 := gen_bij (i := i) hT ζ
  have h2 := gen_bij (i := i) hT (ζ.map f.appTop.hom)
  have e : (Sec.res (F := tw q i) f) ∘ (fun k : ZMod q => k.val • twGen i ζ) =
      fun k : ZMod q => k.val • twGen i (ζ.map f.appTop.hom) := by
    funext k
    simp only [Function.comp]
    rw [res_nsmul', (hT q i).2.2.2.1]
  exact (Function.Bijective.of_comp_iff _ h1).1 (by rw [e]; exact h2)

end LateralTheory.E.ResBijPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Polynomial

namespace LateralTheory.E.RootAICPf

open LateralTheory.E.t_E2Cut

theorem evalMap {R K : Type} [CommRing R] [CommRing K] (φ : R →+* K) (q : ℕ) (a : R) :
    φ ((cyclotomic q R).eval a) = (cyclotomic q K).eval (φ a) := by
  rw [← map_cyclotomic q φ, Polynomial.eval_map, Polynomial.eval₂_hom]

theorem aeval_eq {R : Type} [CommRing R] (q : ℕ) (a : R) :
    aeval a (cyclotomic q ℤ) = (cyclotomic q R).eval a := by
  rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic]

theorem localRoot {q : ℕ} {X : Scheme.{0}} [IsIntegral X] (hX : AICSch X) (hq : q ≠ 0)
    (hK : ((q : ℕ) : X.functionField) ≠ 0) (V : X.Opens) (hV : IsAffineOpen V) [hne : Nonempty V] :
    ∃ ζ : Γ(X, V), IsPrimitiveRoot (X.germToFunctionField V ζ) q := by
  have hA := hX.2 V hV (by obtain ⟨x⟩ := hne; exact ⟨x.1, x.2⟩)
  obtain ⟨a, ha⟩ := hA (cyclotomic q Γ(X, V)) (cyclotomic.monic q _)
    (by rw [natDegree_cyclotomic]; exact Nat.totient_pos.mpr (Nat.pos_of_ne_zero hq))
  refine ⟨a, ?_⟩
  have : NeZero ((q : ℕ) : X.functionField) := ⟨hK⟩
  rw [← isRoot_cyclotomic_iff]
  show (cyclotomic q _).eval _ = 0
  rw [← evalMap, ha, map_zero]

theorem RootAIC_of : LateralTheory.E.HZeroPf.RootAIC := by
  intro q X hX hq
  haveI := hX.1
  obtain ⟨x0⟩ : Nonempty X := inferInstance
  haveI : Nonempty (⊤ : X.Opens) := ⟨⟨x0, trivial⟩⟩
  have hK : ((q : ℕ) : X.functionField) ≠ 0 := by
    intro h
    have := hq.map (X.germToFunctionField ⊤).hom
    rw [map_natCast] at this
    rw [h] at this
    exact not_isUnit_zero this
  have hq0 : q ≠ 0 := by rintro rfl; exact hK (by simp)
  haveI : NeZero q := ⟨hq0⟩
  have hnb : ∀ x : X, ∃ V : X.Opens, IsAffineOpen V ∧ x ∈ V := fun x => by
    obtain ⟨V, hV, hx, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens (show x ∈ (⊤ : X.Opens) from trivial)
    exact ⟨V, hV, hx⟩
  obtain ⟨V0, hV0, hx0⟩ := hnb x0
  haveI : Nonempty V0 := ⟨⟨x0, hx0⟩⟩
  obtain ⟨ζ0, hζ0⟩ := localRoot hX hq0 hK V0 hV0
  obtain ⟨s, hs⟩ := GlobalTheory.IsNormalScheme.exists_germToFunctionField_eq_of_locally (⊤ : X.Opens)
    (X.germToFunctionField V0 ζ0) (fun x _ => by
      obtain ⟨V, hV, hx⟩ := hnb x
      haveI hne : Nonempty V := ⟨⟨x, hx⟩⟩
      obtain ⟨ζ, hζ⟩ := localRoot hX hq0 hK V hV
      obtain ⟨k, -, hk⟩ := hζ.eq_pow_of_pow_eq_one hζ0.pow_eq_one
      exact ⟨V, hne, ζ ^ k, hx, le_top, by rw [map_pow]; exact hk⟩)
  refine ⟨⟨s, hq, ?_⟩⟩
  apply Scheme.germToFunctionField_injective X ⊤
  have : NeZero ((q : ℕ) : X.functionField) := ⟨hK⟩
  rw [aeval_eq, map_zero]
  show (X.germToFunctionField ⊤).hom _ = 0
  rw [evalMap]
  show (cyclotomic q _).eval ((X.germToFunctionField ⊤) s) = 0
  rw [hs]
  exact (isRoot_cyclotomic_iff.mpr hζ0)

end LateralTheory.E.RootAICPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.E.IntFibPf

lemma eqv_comp {R : Type} [CommRing R] {E E' E'' : Spc} (f : E ⟶ E') (g : E' ⟶ E'') (F : Shv R)
    (hf : Eqv R f F) (hg : Eqv R g F) : Eqv R (f ≫ g) F := by
  intro n
  have : (pull R (f ≫ g) F n : H R E'' F n → H R E F n) = pull R f F n ∘ pull R g F n := by
    funext x; exact pull_comp R f g F n x
  rw [this]; exact (hf n).comp (hg n)

lemma eqv_iso {R : Type} [CommRing R] {E E' : Spc} (e : E ≅ E') (F : Shv R) : Eqv R e.hom F := by
  intro n
  refine Function.bijective_iff_has_inverse.mpr ⟨pull R e.inv F n, fun x => ?_, fun x => ?_⟩
  · rw [← pull_comp, e.inv_hom_id, pull_id]
  · rw [← pull_comp, e.hom_inv_id, pull_id]

lemma isPushout_quot (A : Type) [CommRing A] [IsLocalRing A] {B : CommRingCat.{0}} (ψ : CommRingCat.of A ⟶ B) :
    IsPushout ψ (CommRingCat.ofHom (IsLocalRing.residue A))
      (CommRingCat.ofHom (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A).map ψ.hom)))
      (CommRingCat.ofHom (Ideal.quotientMap ((IsLocalRing.maximalIdeal A).map ψ.hom) ψ.hom Ideal.le_comap_map
        : IsLocalRing.ResidueField A →+* _)) := by
  have w : CommSq ψ (CommRingCat.ofHom (IsLocalRing.residue A)) (CommRingCat.ofHom (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A).map ψ.hom)))
      (CommRingCat.ofHom (Ideal.quotientMap ((IsLocalRing.maximalIdeal A).map ψ.hom) ψ.hom Ideal.le_comap_map : IsLocalRing.ResidueField A →+* _)) := by
    constructor; ext a; rfl
  refine IsPushout.of_isColimit' w (PushoutCocone.IsColimit.mk _ (fun s => CommRingCat.ofHom
      (Ideal.Quotient.lift ((IsLocalRing.maximalIdeal A).map ψ.hom) s.inl.hom ?_)) ?_ ?_ ?_)
  · rename_i s; intro a ha
    have hle : ((IsLocalRing.maximalIdeal A).map ψ.hom) ≤ RingHom.ker s.inl.hom := by
      refine Ideal.map_le_iff_le_comap.mpr fun x hx => ?_
      have h1 := congrArg (fun f => f.hom x) s.condition
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h1
      simp only [Ideal.mem_comap, RingHom.mem_ker, h1,
        (IsLocalRing.residue_eq_zero_iff x).mpr hx, map_zero]
    exact hle ha
  · intro s; ext b; rfl
  · intro s; ext x
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
    have h1 := congrArg (fun f => f.hom a) s.condition
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h1
    exact h1
  · intro s m h1 h2
    ext b
    have := congrArg (fun f => f.hom b) h1
    exact this

theorem IntFib_of : LateralTheory.E.IntPBPf.IntFib := by
  intro A _ _ X p hp
  have : IsAffine X := isAffine_of_isAffineHom p
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (X.isoSpec.inv ≫ p)
  refine ⟨Γ(X, ⊤), inferInstance, ψ.hom, ?_, ?_⟩
  · rw [← IsIntegralHom.SpecMap_iff, hψ]; infer_instance
  · intro q i h
    have hP := isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_quot A ψ)
    have hP' : IsPullback (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A).map ψ.hom))) ≫ X.isoSpec.inv) _ p
        (LateralTheory.E.t_E2Cut.cpt A) :=
      hP.of_iso (Iso.refl _) X.isoSpec.symm (Iso.refl _) (Iso.refl _) (by simp)
        ((Category.comp_id _).trans (Category.id_comp _).symm)
        (by simp [hψ]) (by simp)
    rw [← hP'.isoPullback_inv_fst, Functor.map_comp, Functor.map_comp]
    exact eqv_comp _ _ _ (eqv_iso (sch.mapIso hP'.isoPullback.symm) _)
      (eqv_comp _ _ _ h (eqv_iso (sch.mapIso X.isoSpec.symm) _))

end LateralTheory.E.IntFibPf
end
end

section

noncomputable section
open IsLocalRing Polynomial

namespace LateralTheory.E.IntHensPf

theorem mem_sub (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (m : Ideal A) (S : Subalgebra A B)
    {n : ℕ} (c : Fin n → B) (g : Fin n → (algebraMap A B '' (m : Set A))) (hc : ∀ i, c i ∈ S) :
    ∃ y ∈ m.map (algebraMap A S), (y : B) = ∑ i, c i • (g i : B) := by
  choose a ha hag using fun i => (g i).2
  refine ⟨∑ i, ⟨c i, hc i⟩ * algebraMap A S (a i), Ideal.sum_mem _ fun i _ =>
    Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (ha i)), ?_⟩
  change S.val _ = _

  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, smul_eq_mul, ← hag]; rfl

theorem jac (A B : Type) [CommRing A] [CommRing B] [IsLocalRing A] [Algebra A B] [Algebra.IsIntegral A B] :
    (maximalIdeal A).map (algebraMap A B) ≤ (⊥ : Ideal B).jacobson := by
  rw [Ideal.jacobson, le_sInf_iff]
  rintro n ⟨-, hn⟩
  rw [Ideal.map_le_iff_le_comap]
  have : (n.comap (algebraMap A B)).IsMaximal := Ideal.isMaximal_under_of_isIntegral_of_isMaximal n
  exact le_of_eq (IsLocalRing.eq_maximalIdeal this).symm

theorem evalS (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (S : Subalgebra A B) (p : S[X]) (y : S) :
    ((p.eval y : S) : B) = (p.map S.val.toRingHom).eval (y : B) := by
  rw [eval_map]; exact (eval₂_hom S.val.toRingHom y).symm

theorem hens (A B : Type) [CommRing A] [CommRing B] [HenselianLocalRing A] [Algebra A B]
    [Algebra.IsIntegral A B] : HenselianRing B ((maximalIdeal A).map (algebraMap A B)) := by
  classical
  refine ⟨by simpa only [Ideal.jacobson_bot] using jac A B, fun f hf a0 h0 h1 => ?_⟩
  set J := (maximalIdeal A).map (algebraMap A B) with hJ
  obtain ⟨n1, c1, g1, hs1⟩ := Submodule.mem_span_set'.1 h0
  obtain ⟨v, hv⟩ := h1.exists_left_inv
  obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective v
  have hu : u * f.derivative.eval a0 - 1 ∈ J := by
    rw [← Ideal.Quotient.eq, map_mul, hv, map_one]
  obtain ⟨n2, c2, g2, hs2⟩ := Submodule.mem_span_set'.1 hu
  set s : Finset B := insert a0 (insert u (f.coeffs ∪ (Finset.univ.image c1 ∪ Finset.univ.image c2)))
  let S := Algebra.adjoin A (s : Set B)
  have hsS : ∀ x ∈ s, x ∈ S := fun x hx => Algebra.subset_adjoin hx
  haveI : Module.Finite A S :=
    Algebra.finite_adjoin_of_finite_of_isIntegral s.finite_toSet (fun x _ => Algebra.IsIntegral.isIntegral (R := A) x)
  let JS := (maximalIdeal A).map (algebraMap A S)
  haveI : HenselianRing S JS := GlobalTheory.henselianRing_of_finite A JS (GlobalTheory.map_maximalIdeal_le_jacobson_of_finite A S)
  have hc : (↑f.coeffs : Set B) ⊆ S.toSubring := fun c hc => hsS c (by simp [s, Finset.mem_coe.1 hc])
  let g : S[X] := f.toSubring S.toSubring hc
  have hgf : g.map S.val.toRingHom = f := f.map_toSubring S.toSubring hc
  let b0 : S := ⟨a0, hsS a0 (by simp [s])⟩
  let uS : S := ⟨u, hsS u (by simp [s])⟩
  have hgm : g.Monic := by
    rw [← hgf] at hf; exact Polynomial.monic_of_injective Subtype.val_injective hf
  have h0S : g.eval b0 ∈ JS := by
    obtain ⟨y, hy, hyv⟩ := mem_sub A B _ S c1 g1 (fun i => hsS _ (by simp [s]))
    convert hy using 1
    apply Subtype.ext
    rw [hyv, hs1, evalS, hgf]
  have h1S : IsUnit (Ideal.Quotient.mk JS (g.derivative.eval b0)) := by
    obtain ⟨y, hy, hyv⟩ := mem_sub A B _ S c2 g2 (fun i => hsS _ (by simp [s]))
    have : uS * g.derivative.eval b0 - 1 ∈ JS := by
      convert hy using 1
      apply Subtype.ext
      rw [hyv, hs2]
      simp only [Subalgebra.coe_sub, Subalgebra.coe_mul, Subalgebra.coe_one, evalS]
      rw [← derivative_map, hgf]
    rw [← Ideal.Quotient.eq, map_mul, map_one] at this
    exact ⟨⟨_, _, (mul_comm _ _).trans this, this⟩, rfl⟩
  obtain ⟨a, ha, ha'⟩ := HenselianRing.is_henselian g hgm b0 h0S h1S
  refine ⟨(a : B), ?_, ?_⟩
  · rw [IsRoot.def, ← hgf, ← evalS, ha.eq_zero]; rfl
  · have := Ideal.mem_map_of_mem S.val.toRingHom ha'
    rw [Ideal.map_map] at this
    simpa using this

theorem IntHens_of : LateralTheory.E.IntPBPf.IntHens := by
  intro A B _ _ _ φ hφ
  letI : Algebra A B := φ.toAlgebra
  haveI : Algebra.IsIntegral A B := ⟨hφ⟩
  exact hens A B

end LateralTheory.E.IntHensPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut

namespace LateralTheory.E.FiberCover
open LateralTheory.E.LineOneCut

lemma fibMap_eq {A : Type} [CommRing A] [IsLocalRing A] {U Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)) (ι : U ⟶ Z) :
    fibMap p ι = (pullbackRightPullbackFstIso p (cpt A) ι).inv ≫ pullback.snd ι (pullback.fst p (cpt A)) := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullbackRightPullbackFstIso_inv_snd_fst]; exact pullback.lift_fst _ _ _
  · rw [Category.assoc, pullbackRightPullbackFstIso_inv_snd_snd]
    simp [fibMap]

lemma fibMap_open {A : Type} [CommRing A] [IsLocalRing A] {U Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)) (ι : U ⟶ Z)
    [IsOpenImmersion ι] : IsOpenImmersion (fibMap p ι) := by
  rw [fibMap_eq]; infer_instance

lemma fibMap_range {A : Type} [CommRing A] [IsLocalRing A] {U Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)) (ι : U ⟶ Z) :
    Set.range (fibMap p ι) = (pullback.fst p (cpt A)) ⁻¹' Set.range ι := by
  rw [fibMap_eq, ← Scheme.Pullback.range_snd]
  ext x; constructor
  · rintro ⟨y, rfl⟩
    exact ⟨_, (Scheme.Hom.comp_apply _ _ y).symm⟩
  · rintro ⟨y, rfl⟩
    refine ⟨(pullbackRightPullbackFstIso p (cpt A) ι).hom y, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

theorem FibCover_of : FibCover := by
  intro A _ _ Z U V p ι₁ ι₂ h1 h2 hcov
  refine ⟨fibMap_open p ι₁, fibMap_open p ι₂, ?_⟩
  rw [fibMap_range, fibMap_range, ← Set.preimage_union, hcov, Set.preimage_univ]

end LateralTheory.E.FiberCover
end
end
