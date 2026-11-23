module

public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle457
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FaceSubMid
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZeroChains
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchClsCocycleSec
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle458
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexConjIntegralGLRowCongruence
public import Development.AbelianVarietyTheory.Definitions.Divisors.RatBasisLinearIndependentInt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle459
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToBaseChangePtsBijective
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle449
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle463
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
import Mathlib.RingTheory.Noetherian.Nilpotent
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle405
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle070

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.KummerSplit

theorem _root_.GlobalTheory.T.primitiveRoot_free_action_finsupp_sum : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A] [Nontrivial A] (ζ : Prim q A) (ι : Type) (s : Finset ι) (c : ι → ULift.{1} (ZMod q)) (a : ι → ℕ) (v w : ι → Aˣ), (∀ i ∈ s, (w i : A) = ζ.1 ^ a i * v i) → (∑ i ∈ s, (Finsupp.single (w i) (c i) - Finsupp.single (v i) (c i))) = 0 → ∑ i ∈ s, (c i).down * (a i : ZMod q) = 0 := by
  first | (exact @GlobalTheory.EtC.FreeActSum.free_act_sum) | (exact GlobalTheory.EtC.FreeActSum.free_act_sum) | (intros; apply GlobalTheory.EtC.FreeActSum.free_act_sum  <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem aw_leibniz_rule : ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) {E : Spc} {n m k : ℤ} (hk : n + m = k) (α : Cochain ((chains R).obj E) I n) (β : Cochain ((chains R).obj E) J m) (γ : Cochain ((chains R).obj E) K k) (γ₁ γ₂ : Cochain ((chains R).obj E) K (k + 1)), μ.IsAW hk α β γ → μ.IsAW (by omega) (δ n (n + 1) α) β γ₁ → μ.IsAW (by omega) α (δ m (m + 1) β) γ₂ → δ k (k + 1) γ = γ₁ + n.negOnePow • γ₂ := by
  intro R _ I J K μ E n m k hk α β γ γ₁ γ₂ hc h₁ h₂
  exact CupSpec.aw_leibniz μ rfl rfl rfl hc h₁ h₂

end GlobalTheory.EtC
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.cocycle_ev_d_eq_zero_and_mk_eq_zero_iff :
    ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (I : Cx R) (m n k : ℤ),
      m + 1 = n → n + 1 = k →
        (∀ z : Sec (I.X n) X, Sec.map (I.d n k) z = 0 →
          ∃ α : Cocycle ((chains R).obj (sch.obj X)) I n,
            (∀ (U : Scheme.{0}) (x : U ⟶ X), ev (R := R) α.1 0 n (by simp) U x = Sec.res x z) ∧
              ∀ (p : ℕ) s h U x, ev (R := R) α.1 (p + 1) s h U x = 0) ∧
        ∀ α : Cocycle ((chains R).obj (sch.obj X)) I n,
          Sec.map (I.d n k) (ev (R := R) α.1 0 n (by simp) X (𝟙 X)) = 0 ∧
            (CohomologyClass.mk α = 0 ↔
              ∃ y : Sec (I.X m) X, Sec.map (I.d m n) y = ev (R := R) α.1 0 n (by simp) X (𝟙 X)) := by
  intro R _ X I m n k hmn hnk
  have ev_def {q : ℤ} (α : Cochain ((chains R).obj (sch.obj X)) I q)
      (p : ℕ) (s : ℤ) (h : -(p : ℤ) + q = s) (U : Scheme.{0}) (x : Sx (sch.obj X) p U) :
      ev (R := R) α p s h U x =
        Sec.map ((chainsXIso R (sch.obj X) p).inv ≫ α.v _ _ h) (freeGen R _ U x) := rfl
  have ev_ext {q : ℤ} (α β : Cochain ((chains R).obj (sch.obj X)) I q)
      (h : ∀ p s hs U x, ev (R := R) α p s hs U x = ev (R := R) β p s hs U x) : α = β := by
    ext i s hs : 1
    by_cases hi : i ≤ 0
    · obtain ⟨p, rfl⟩ : ∃ p : ℕ, i = -(p : ℤ) := ⟨(-i).toNat, by omega⟩
      rw [← cancel_epi (chainsXIso R (sch.obj X) p).inv]
      exact CupSpec.free_ext _ _ (fun U x => h p s hs U x)
    · exact (CupSpec.isZero_chains (sch.obj X) i (by omega)).eq_of_src _ _
  have ev_exists {q : ℤ}
      (a : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + q = s → ∀ U : Scheme.{0},
        Sx (sch.obj X) p U → Sec (I.X s) U)
      (ha : ∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx (sch.obj X) p U),
        Sec.res g (a p s h U x) = a p s h V (x.res g)) :
      ∃ α : Cochain ((chains R).obj (sch.obj X)) I q,
        ∀ p s h U x, ev (R := R) α p s h U x = a p s h U x := by
    have key : ∀ (i j : ℤ) (hij : i + q = j),
        ∃ φ : ((chains R).obj (sch.obj X)).X i ⟶ I.X j,
          ∀ (p : ℕ) (hp : i = -(p : ℤ)) U x,
            Sec.map ((chainsXIso R (sch.obj X) p).inv ≫
              eqToHom (congrArg ((chains R).obj (sch.obj X)).X hp.symm) ≫ φ) (freeGen R _ U x) =
              a p j (hp ▸ hij) U x := by
      intro i j hij
      by_cases hi : i ≤ 0
      · obtain ⟨p, rfl⟩ : ∃ p : ℕ, i = -(p : ℤ) := ⟨(-i).toNat, by omega⟩
        obtain ⟨φ, hφ⟩ := CupSpec.free_exists (R := R) _ _ (a p j hij) (ha p j hij)
        refine ⟨(chainsXIso R (sch.obj X) p).hom ≫ φ, fun p' hp U x => ?_⟩
        obtain rfl : p = p' := by omega
        rw [eqToHom_refl, Category.id_comp, Iso.inv_hom_id_assoc]
        exact hφ U x
      · exact ⟨0, fun p hp => by omega⟩
    choose φ hφ using key
    refine ⟨Cochain.mk φ, fun p s h U x => ?_⟩
    have he := hφ _ _ h p rfl U x
    rw [eqToHom_refl, Category.id_comp] at he
    exact he
  have ev_res {q : ℤ} (α : Cochain ((chains R).obj (sch.obj X)) I q)
      (p : ℕ) (s : ℤ) (h : -(p : ℤ) + q = s) {V U : Scheme.{0}} (g : V ⟶ U)
      (x : Sx (sch.obj X) p U) :
      Sec.res g (ev (R := R) α p s h U x) = ev (R := R) α p s h V (x.res g) := by
    rw [ev_def, CupSpec.map_res, CupSpec.freeGen_res]
    rfl
  have ev_zero {q : ℤ} (p : ℕ) (s : ℤ) (h : -(p : ℤ) + q = s)
      (U : Scheme.{0}) (x : Sx (sch.obj X) p U) :
      ev (R := R) (0 : Cochain ((chains R).obj (sch.obj X)) I q) p s h U x = 0 := by
    rw [ev_def, Cochain.zero_v, comp_zero]
    exact (CupSpec.mapHom _ _ _).map_zero
  have ev_δ_zero {a b : ℤ} (hab : a + 1 = b)
      (α : Cochain ((chains R).obj (sch.obj X)) I a) (U : Scheme.{0}) (s t : ℤ)
      (hs : -((0 : ℕ) : ℤ) + a = s) (ht : -((0 : ℕ) : ℤ) + b = t) (x : Sx (sch.obj X) 0 U) :
      ev (R := R) (δ a b α) 0 t ht U x = Sec.map (I.d s t) (ev (R := R) α 0 s hs U x) := by
    rw [ev_def, δ_v a b hab α _ t ht s 1 (by omega) (by simp),
      (CupSpec.isZero_chains (sch.obj X) 1 one_pos).eq_of_tgt (((chains R).obj (sch.obj X)).d _ 1) 0,
      zero_comp, smul_zero, add_zero]
    rfl
  have ev_δ_sch {a b : ℤ} (hab : a + 1 = b)
      (α : Cochain ((chains R).obj (sch.obj X)) I a) (U : Scheme.{0}) (p : ℕ) (s t : ℤ)
      (hs : -((p + 1 : ℕ) : ℤ) + a = s) (ht : -((p + 1 : ℕ) : ℤ) + b = t)
      (x : Sx (sch.obj X) (p + 1) U) :
      ev (R := R) (δ a b α) (p + 1) t ht U x = Sec.map (I.d s t) (ev (R := R) α (p + 1) s hs U x) +
        (if Even p then 0 else b.negOnePow • ev (R := R) α p t (by omega) U x) := by
    have hsum : ev (R := R) (δ a b α) (p + 1) t ht U x =
        Sec.map (I.d s t) (ev (R := R) α (p + 1) s hs U x) +
          b.negOnePow • ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) •
            ev (R := R) α p t (by omega) U (x.face i) := by
      rw [ev_def, δ_v a b hab α _ t ht s (-(p : ℤ)) (by omega) (by omega),
        Preadditive.comp_add, Units.smul_def, Preadditive.comp_zsmul,
        ← Category.assoc _ (((chains R).obj (sch.obj X)).d _ _), CupSpec.chains_d, Category.assoc,
        Preadditive.sum_comp]
      refine (map_add (CupSpec.mapHom _ _ (freeGen R _ U x)) _ _).trans ?_

      rw [map_zsmul, map_sum, Units.smul_def]
      refine congrArg₂ (· + ·) rfl (congrArg _ (Finset.sum_congr rfl fun i _ => ?_))
      rw [Preadditive.zsmul_comp, map_zsmul]
      congr 1
      change Sec.map ((chainsXIso R (sch.obj X) p).inv ≫ α.v _ _ _)
        (Sec.map ((free R).map _) (freeGen R _ U x)) = _
      rw [CupSpec.freeGen_map]
      rfl
    rw [hsum]
    simp only [SchCls.face_sch]
    rw [← Finset.sum_smul, SchCls.sum_neg_one_pow]
    split_ifs <;> simp
  refine ⟨fun z hz => ?_, fun α => ?_⟩
  · obtain ⟨a, ha⟩ := ev_exists (q := n)
      (fun p s h U x => if hp : p = 0 then
        Sec.map (I.XIsoOfEq (show n = s by omega)).hom (Sec.res (x : U ⟶ X) z) else 0)
      (by
        intro p s h V U g x
        by_cases hp : p = 0
        · subst hp
          simp only [dite_eq_left]
          erw [CupSpec.map_res, SchCls.res_comp]
          rfl
        · simp only [dite_eq_right hp]
          exact map_zero _)
    have hc : δ n k a = 0 := by
      refine ev_ext _ _ fun p t ht U x => ?_
      erw [ev_zero]
      cases p with
      | zero =>
        have hkt : k = t := by omega
        subst hkt
        erw [ev_δ_zero hnk a U n k (by simp) ht x, ha]
        simp only [dite_eq_left, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, SchCls.map_id']
        erw [← CupSpec.map_res, hz]
        exact map_zero _
      | succ p =>
        erw [ev_δ_sch hnk a U p (-((p + 1 : ℕ) : ℤ) + n) t (by omega) ht x, ha, ha]
        simp only [Nat.add_one_ne_zero, dite_eq_right, not_false_eq_true, map_zero, zero_add]
        split_ifs with he hp0
        · rfl
        · exact absurd (hp0 ▸ (⟨0, rfl⟩ : Even 0)) he
        · exact smul_zero _
    refine ⟨Cocycle.mk a k hnk hc, fun U x => ?_, fun p s h U x => ?_⟩
    · change ev (R := R) a 0 n _ U x = _
      erw [ha]
      simp only [dite_eq_left, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, SchCls.map_id']
    · change ev (R := R) a (p + 1) s h U x = 0
      erw [ha]
      simp
  · have hδ := Cocycle.δ_eq_zero α k
    refine ⟨?_, ?_⟩
    · have h0 := ev_δ_zero hnk α.1 X n k (by simp) (by simp) (𝟙 X)
      erw [hδ, ev_zero] at h0
      exact h0.symm
    erw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff α m hmn]
    constructor
    · rintro ⟨β, hβ⟩
      refine ⟨ev (R := R) β 0 m (by simp) X (𝟙 X), ?_⟩
      erw [← hβ, ev_δ_zero hmn β X m n (by simp) (by simp)]
    · rintro ⟨y, hy⟩
      obtain ⟨b, hb⟩ := ev_exists (q := m)
        (fun p s h U x => if hp : p = 0 then
          Sec.map (I.XIsoOfEq (show m = s by omega)).hom (Sec.res (x : U ⟶ X) y)
          else if Even p then 0 else (-k.negOnePow) • ev (R := R) α.1 (p + 1) s (by omega) U x)
        (by
          intro p s h V U g x
          by_cases hp : p = 0
          · subst hp
            simp only [dite_eq_left]
            erw [CupSpec.map_res, SchCls.res_comp]
            rfl
          · simp only [dite_eq_right hp]
            split_ifs
            · exact map_zero _
            · erw [SchCls.res_units_smul, ev_res]
              rfl)
      refine ⟨b, ev_ext _ _ fun p t ht U x => ?_⟩
      cases p with
      | zero =>
        have hnt : n = t := by omega
        subst hnt
        erw [ev_δ_zero hmn b U m n (by simp) ht x, hb]
        simp only [dite_eq_left, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, SchCls.map_id']
        erw [← CupSpec.map_res, hy, ev_res]
        congr 1
      | succ p =>
        erw [ev_δ_sch hmn b U p (-((p + 1 : ℕ) : ℤ) + m) t (by omega) ht x, hb, hb]
        have hc := ev_δ_sch hnk α.1 U (p + 1) (-((p + 1 : ℕ) : ℤ) + m) t (by omega) (by omega) x
        erw [hδ, ev_zero] at hc
        rcases Nat.even_or_odd p with he | ho
        · have hne : ¬ Even (p + 1) := Nat.not_even_iff_odd.mpr he.add_one
          simp only [Nat.add_one_ne_zero, dite_eq_right, not_false_eq_true, hne, ite_false, ite_eq_left he,
            add_zero] at hc ⊢
          erw [SchCls.map_units_smul, eq_neg_of_add_eq_zero_left hc.symm, smul_neg, smul_smul]
          simp [Int.units_mul_self]
        · have hne : ¬ Even p := Nat.not_even_iff_odd.mpr ho
          have hp0 : p ≠ 0 := fun h => hne (h ▸ (⟨0, rfl⟩ : Even 0))
          have hev : Even (p + 1) := ho.add_one
          simp only [Nat.add_one_ne_zero, dite_eq_right, not_false_eq_true, hev, ite_true, hne, ite_false,
            dite_eq_right hp0, map_zero, zero_add]
          have hkn : k.negOnePow = -n.negOnePow := by rw [← hnk, Int.negOnePow_succ]
          erw [hkn, neg_neg, smul_smul, Int.units_mul_self, one_smul]
end

section

open MeasureTheory Matrix ValuativeRel


theorem _root_.GlobalTheory.T.norm_mul_normalisedAbsPow_half_eq_one : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (d : ℕ) (χ : kˣ →* ℂˣ), (∀ u : kˣ, valuation k (u : k) = 1 → ‖(χ u : ℂ)‖ = 1) →
    ∀ ϖ : kˣ, GlobalTheory.SplitFlip.IsUnif ϖ → ‖(χ ϖ : ℂ)‖ ^ 2 * (GlobalTheory.SplitWeil.resCard k : ℝ) ^ d = 1 →
    ∀ x : kˣ, ‖(χ x : ℂ) * GlobalTheory.SplitFlip.apow x (-((d : ℂ) / 2))‖ = 1 := by
  first | exact @GlobalTheory.CharNormHalf.norm_mul_apow_eq_one | exact GlobalTheory.CharNormHalf.norm_mul_apow_eq_one | (intros; apply GlobalTheory.CharNormHalf.norm_mul_apow_eq_one <;> assumption)
end

section

open GlobalTheory.FunObj GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.DiagVol ValuativeRel Matrix

theorem _root_.GlobalTheory.T.relIndex_conj_integralGL_column_congruence : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type} [Fintype ι] [DecidableEq ι] (ϖ : kˣ), IsUnif ϖ → ∀ (t : ι) (S : Finset ι), t ∉ S → ∀ (H : Subgroup (GL ι k)), H ≤ KO k ι → (∀ x ∈ H, ∀ r, r ∉ S → x.val r t = (1 : Matrix ι ι k) r t) → (∀ y : ι → k, (∀ r, y r ∈ 𝒪[k]) → (∀ r, r ∉ S → y r = 0) → ∃ x ∈ H, x.val = 1 + Matrix.of (fun r s => if s = t then y r else 0)) → ((KO k ι).map (MulAut.conj ((diagGL (Pi.mulSingle t ϖ))⁻¹)).toMonoidHom).relIndex H = resCard k ^ S.card := by
  first | exact @GlobalTheory.IndexCol.relIndex_conj_col | exact GlobalTheory.IndexCol.relIndex_conj_col | (intros; apply GlobalTheory.IndexCol.relIndex_conj_col <;> assumption)
end

section

open GlobalTheory.FunObj GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.DiagVol ValuativeRel Matrix

theorem _root_.GlobalTheory.T.relIndex_conj_integralGL_row_congruence : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type} [Fintype ι] [DecidableEq ι] (ϖ : kˣ), IsUnif ϖ → ∀ (t : ι) (S : Finset ι), t ∉ S → ∀ (H : Subgroup (GL ι k)), H ≤ KO k ι → (∀ x ∈ H, ∀ s, s ∉ S → x.val t s = (1 : Matrix ι ι k) t s) → (∀ y : ι → k, (∀ s, y s ∈ 𝒪[k]) → (∀ s, s ∉ S → y s = 0) → ∃ x ∈ H, x.val = 1 + Matrix.of (fun r s => if r = t then y s else 0)) → ((KO k ι).map (MulAut.conj (diagGL (Pi.mulSingle t ϖ))).toMonoidHom).relIndex H = resCard k ^ S.card := by
  first | exact @GlobalTheory.DiagVol.RowIdx.relIndex_rowCong | exact GlobalTheory.DiagVol.RowIdx.relIndex_rowCong | (intros; apply GlobalTheory.DiagVol.RowIdx.relIndex_rowCong <;> assumption)
end

section

open DividedPowers GlobalTheory.Cris GlobalTheory.PDA

theorem _root_.GlobalTheory.T.exists_dividedPowers_dividedPowerPolyAlgebra_augIdeal : ∀ (B : Type) [CommRing B] (Q : PDPoly B), ∃ η : DividedPowers Q.aug, ∀ n : ℕ, η.dpow n (Q.e 1) = Q.e n := by
  first | exact @GlobalTheory.PDA.exists_dividedPowers_aug | exact GlobalTheory.PDA.exists_dividedPowers_aug | (intros; apply GlobalTheory.PDA.exists_dividedPowers_aug <;> assumption)
end

section

open CategoryTheory GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

open TensorProduct Coalgebra Bialgebra WithConv

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PDivGroup

theorem app_app_eq_algebraMap_counit_of_isConn_of_isEt {p : ℕ} [Fact p.Prime] {k k' : Type}
    [Field k] [CharP k p] [PerfectRing k p] [Field k'] {σ : k →+* k'} {G' G'₀ : PDivGroup p k'}
    {C : PDivGroup p k} (i₀ : G'₀ ⟶ G') (hG : G'₀.IsConn) (hC : C.IsEt) (x : SemiHom σ G' C)
    (n : ℕ) (a : C.A n) :
    i₀.app n (x.app n a) = algebraMap k' (G'₀.A n) (σ (counit (R := k) a)) := by
  have hmem : a - algebraMap k (C.A n) (counit (R := k) a) ∈ augIdeal k (C.A n) := by
    rw [mem_augIdeal_iff', map_sub, ← Bialgebra.counitAlgHom_apply (R := k),
      ← Bialgebra.counitAlgHom_apply (R := k), AlgHom.commutes, Algebra.algebraMap_self,
      RingHom.id_apply, sub_self]
  suffices h : i₀.app n ((x.app n).toRingHom (a - algebraMap k (C.A n) (counit (R := k) a))) = 0 by
    rw [map_sub, map_sub, sub_eq_zero] at h
    refine h.trans ?_
    change i₀.app n ((x.app n) (algebraMap k (C.A n) (counit (R := k) a))) = _
    rw [(x.app n).map_algebraMap, AlgHomClass.commutes]
  haveI := hC n
  haveI : IsNoetherianRing (G'₀.A n) := isNoetherian_of_tower k' inferInstance
  obtain ⟨N, hN⟩ := (Ideal.FG.isNilpotent_iff_le_nilradical
    (IsNoetherian.noetherian (augIdeal k' (G'₀.A n)))).2 fun y hy => mem_nilradical.2 (hG n y hy)
  obtain ⟨b, hb, hab⟩ := exists_augIdeal_pow_eq (A := C.A n) N _ hmem
  have hfb : i₀.app n ((x.app n).toRingHom b) ∈ augIdeal k' (G'₀.A n) := by
    rw [mem_augIdeal_iff', CoalgHomClass.counit_comp_apply]
    change counit (R := k') ((x.app n) b) = 0
    rw [(x.app n).counit_map, (mem_augIdeal_iff' b).1 hb, map_zero]
  have hle : N ≤ p ^ N := (Nat.lt_pow_self (Fact.out : p.Prime).one_lt).le
  have h1 := Ideal.pow_le_pow_right hle (Ideal.pow_mem_pow hfb (p ^ N))
  rw [hN] at h1
  rw [hab, map_pow, map_pow]
  exact (Submodule.mem_bot _).1 h1

theorem add_app_eq_lift_comul {p : ℕ} {k : Type} [CommRing k] {G H : PDivGroup p k}
    (f g : G ⟶ H) (n : ℕ) (c : H.A n) :
    Hom.app (f + g) n c = Algebra.TensorProduct.lift (f.app n : H.A n →ₐ[k] G.A n)
      (g.app n : H.A n →ₐ[k] G.A n) (fun _ _ => .all _ _) (comul c) := by
  have h := DFunLike.congr_fun (congrArg ofConv (map_mul toPts (f.conv n) (g.conv n))) c
  rw [AlgHom.convMul_apply] at h
  exact h

end GlobalTheory.PDivGroup

theorem GlobalTheory.PDivGroup.semiHom_factor_of_isConn_of_isEt :
    ∀ (p : ℕ) [Fact p.Prime] (k k' : Type) [Field k] [CharP k p] [PerfectRing k p]
    [Field k'] [CharP k' p] [PerfectRing k' p] (σ : k →+* k') (G' G'₀ G'₁ : PDivGroup p k') (C : PDivGroup p k)
    (i₀ : G'₀ ⟶ G') (q₀ : G' ⟶ G'₀) (i₁ : G'₁ ⟶ G') (q₁ : G' ⟶ G'₁), G'₀.IsConn → C.IsEt →
    q₀ ≫ i₀ + q₁ ≫ i₁ = 𝟙 G' → ∀ (x : SemiHom σ G' C) (n : ℕ) (a : C.A n),
      q₁.app n (i₁.app n (x.app n a)) = x.app n a := by
  intro p _ k k' _ _ _ _ _ _ σ G' G'₀ G'₁ C i₀ q₀ i₁ q₁ hG hC hs x n a
  have key : ∀ t : C.A n ⊗[k] C.A n,
      Algebra.TensorProduct.lift ((q₀ ≫ i₀).app n : G'.A n →ₐ[k'] G'.A n)
        ((q₁ ≫ i₁).app n : G'.A n →ₐ[k'] G'.A n) (fun _ _ => .all _ _) ((x.app n).two t) =
      (q₁ ≫ i₁).app n (x.app n (TensorProduct.lid k _ (LinearMap.rTensor _ counit t))) := by
    intro t
    induction t with
    | add u v hu hv =>
      rw [map_add (f := _), map_add (f := _), hu, hv, map_add (f := _), map_add (f := _), ← map_add (f := _), ← map_add (f := _)]
    | tmul a₁ a₂ =>
      rw [TensorProduct.map_tmul, SemiBialgHom.lin_apply, SemiBialgHom.lin_apply,
        Algebra.TensorProduct.lift_tmul, LinearMap.rTensor_tmul, TensorProduct.lid_tmul]
      change q₀.app n (i₀.app n (x.app n a₁)) * _ = _
      rw [app_app_eq_algebraMap_counit_of_isConn_of_isEt i₀ hG hC x n a₁, AlgHomClass.commutes,
        ← Algebra.smul_def, (x.app n).smul_map]
      change _ = ((q₁ ≫ i₁).app n : G'.A n →ₐ[k'] G'.A n) (σ (counit a₁) • x.app n a₂)
      rw [map_smul]
  have h1 : x.app n a = Hom.app (q₀ ≫ i₀ + q₁ ≫ i₁) n (x.app n a) := by rw [hs]; rfl
  rw [add_app_eq_lift_comul, ← SemiBialgHom.two_comul, key, Coalgebra.rTensor_counit_comul,
    TensorProduct.lid_tmul, one_smul] at h1
  exact h1.symm
end
end

section

open CategoryTheory GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

open TensorProduct Coalgebra Bialgebra WithConv

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

theorem PDivGroup.semiHom_app_eq_conn_part :
    ∀ (p : ℕ) [Fact p.Prime] (k k' : Type) [Field k] [CharP k p] [PerfectRing k p]
    [Field k'] [CharP k' p] [PerfectRing k' p] (σ : k →+* k') (G' G'₀ G'₁ : PDivGroup p k') (C : PDivGroup p k)
    (i₀ : G'₀ ⟶ G') (q₀ : G' ⟶ G'₀) (i₁ : G'₁ ⟶ G') (q₁ : G' ⟶ G'₁), G'₁.IsEt → C.IsConn →
    q₀ ≫ i₀ + q₁ ≫ i₁ = 𝟙 G' → ∀ (x : SemiHom σ G' C) (n : ℕ) (a : C.A n),
      q₀.app n (i₀.app n (x.app n a)) = x.app n a := by
  intro p _ k k' _ _ _ _ _ _ σ G' G'₀ G'₁ C i₀ q₀ i₁ q₁ hEt hConn hsplit x n a
  have h1 : ∀ c : C.A n,
      i₁.app n (x.app n c) = algebraMap k' (G'₁.A n) (σ (counit (R := k) c)) := by
    intro c
    haveI := hEt n
    have hmem : c - algebraMap k (C.A n) (counit (R := k) c) ∈ augIdeal k (C.A n) := by
      rw [mem_augIdeal_iff', map_sub, ← Bialgebra.counitAlgHom_apply (R := k),
        ← Bialgebra.counitAlgHom_apply (R := k), AlgHom.commutes, Algebra.algebraMap_self,
        RingHom.id_apply, sub_self]
    have h := (((hConn n _ hmem).map (x.app n).toRingHom).map (i₁.app n)).eq_zero
    change i₁.app n (x.app n (c - _)) = 0 at h
    rw [map_sub, SemiBialgHom.map_algebraMap, map_sub, AlgHomClass.commutes, sub_eq_zero] at h
    exact h
  have hP₁ : ∀ c : C.A n, (q₁ ≫ i₁).app n (x.app n c) =
      algebraMap k' (G'.A n) (σ (counit (R := k) c)) := by
    intro c
    rw [comp_app, BialgHom.comp_apply, h1, AlgHomClass.commutes]
  have hid : ∀ b : G'.A n, ((q₀ ≫ i₀).conv n * (q₁ ≫ i₁).conv n).ofConv b = b := by
    intro b
    have h := congrArg (fun f : G' ⟶ G' => f.app n b) hsplit
    exact h
  have key : ∀ c : C.A n ⊗[k] C.A n,
      Algebra.TensorProduct.lift ((q₀ ≫ i₀).app n : G'.A n →ₐ[k'] G'.A n)
        ((q₁ ≫ i₁).app n : G'.A n →ₐ[k'] G'.A n) (fun _ _ => .all _ _) ((x.app n).two c) =
      (q₀ ≫ i₀).app n (x.app n (TensorProduct.rid k (C.A n)
        (LinearMap.lTensor (C.A n) (counit (R := k)) c))) := by
    intro c
    induction c with
    | add c d hc hd => simp only [map_add (f := _), hc, hd]
    | tmul b c =>
      rw [TensorProduct.map_tmul, Algebra.TensorProduct.lift_tmul, LinearMap.lTensor_tmul,
        TensorProduct.rid_tmul, SemiBialgHom.lin_apply, SemiBialgHom.lin_apply]
      change _ * (q₁ ≫ i₁).app n (x.app n c) = _
      rw [hP₁, (x.app n).smul_map, map_smul, Algebra.smul_def, mul_comm]
      rfl
  have e : (toPts ((q₀ ≫ i₀).conv n * (q₁ ≫ i₁).conv n)).ofConv (x.app n a) = x.app n a :=
    hid (x.app n a)
  rw [map_mul, AlgHom.convMul_apply, toPts_ofConv, toPts_ofConv, ← (x.app n).two_comul] at e
  have e2 := key (comul (R := k) a)
  rw [Coalgebra.lTensor_counit_comul, TensorProduct.rid_tmul, one_smul] at e2
  exact e2.symm.trans e

end GlobalTheory
end
end

section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory.PDivGroup

theorem finrank_quot_kerIdeal_mul_of_idem (p : ℕ) [Fact p.Prime] (k : Type) [Field k]
    (G : PDivGroup p k) (u v : G ⟶ G) (huv : u + v = 𝟙 G) (h1 : u ≫ v = 0) (h2 : v ≫ u = 0)
    (n : ℕ) :
    Module.finrank k (G.A n ⧸ kerIdeal (u.app n)) * Module.finrank k (G.A n ⧸ kerIdeal (v.app n)) =
      p ^ (n * G.height) := by
  have hdim : Module.finrank k (G.A n) = p ^ (n * G.height) := by
    obtain ⟨q⟩ : Nonempty (PrimeSpectrum k) := inferInstance
    have h := G.rank_eq n q
    rw [Module.rankAtStalk_eq_finrank_of_free] at h
    simpa using h
  have hker := GlobalTheory.T.ker_app_eq_bialgHomKernelIdeal_of_idempotents p k G u v huv h1 h2 n
  have hord := finrank_eq_ker_mul_range k (G.A n) (G.A n) (u.app n)
  have hr : Module.finrank k (LinearMap.range ((u.app n : G.A n →ₐ[k] G.A n).toLinearMap)) =
      Module.finrank k (G.A n ⧸ kerIdeal (v.app n)) := by
    rw [← hker]
    exact (((u.app n : G.A n →ₐ[k] G.A n).toLinearMap.quotKerEquivRange).symm.finrank_eq).trans rfl
  rw [← hdim, hord, hr]

end GlobalTheory.PDivGroup
end
