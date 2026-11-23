module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FinitePointsOfIsOpenImmersion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
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
import Mathlib.Tactic.TypeStar
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PowerDiagonal

section General

variable {C : Type*} [Category C] [CartesianMonoidalCategory C]

theorem isMonHom_of_points {X Y : C} [MonObj X] [MonObj Y] (f : X ⟶ Y)
    (h1 : ∀ T : C, (1 : T ⟶ X) ≫ f = 1)
    (hm : ∀ (T : C) (x y : T ⟶ X), (x * y) ≫ f = (x ≫ f) * (y ≫ f)) : IsMonHom f := by
  refine ⟨?_, ?_⟩
  · simpa only [MonObj.one_eq_one] using h1 (𝟙_ C)
  · simpa only [MonObj.mul_eq_mul, MonObj.comp_mul, tensorHom_fst, tensorHom_snd] using
      hm (X ⊗ X) (fst X X) (snd X X)

theorem exists_sections {G H : C} [MonObj G] [MonObj H] {n : Type} [DecidableEq n]
    (p : n → (G ⟶ H)) (hp : ∀ a, IsMonHom (p a))
    (hu : ∀ (T : C) (y : n → (T ⟶ H)), ∃! x : T ⟶ G, ∀ a, x ≫ p a = y a) :
    ∃ j : n → (H ⟶ G), (∀ b, IsMonHom (j b)) ∧ (∀ b, j b ≫ p b = 𝟙 H) ∧
      ∀ b c, c ≠ b → j b ≫ p c = 1 := by
  classical
  have hex := fun b => (hu H (fun c => if c = b then 𝟙 H else 1)).exists
  choose j hj using hex
  have key : ∀ {T : C} (x : T ⟶ H) (b c : n), x ≫ j b ≫ p c = if c = b then x else 1 := by
    intro T x b c
    rw [hj b c]
    split_ifs <;> simp
  have ext : ∀ {T : C} (x y : T ⟶ G), (∀ a, x ≫ p a = y ≫ p a) → x = y := fun {T} x y h =>
    (hu T fun a => y ≫ p a).unique h (fun _ => rfl)
  refine ⟨j, fun b => ?_, fun b => by simpa using key (𝟙 H) b b,
    fun b c hcb => by simpa [hcb] using key (𝟙 H) b c⟩
  apply isMonHom_of_points
  · intro T
    apply ext
    intro a
    haveI := hp a
    rw [Category.assoc, key, MonObj.one_comp]
    split_ifs <;> rfl
  · intro T x y
    apply ext
    intro a
    haveI := hp a
    simp only [Category.assoc, key, MonObj.mul_comp]
    split_ifs <;> simp

theorem hom_ext_sections {G H H' : C} [MonObj G] [MonObj H] [MonObj H']
    {n : Type} [Finite n] [DecidableEq n]
    (p : n → (G ⟶ H)) (hp : ∀ a, IsMonHom (p a))
    (hu : ∀ (T : C) (y : n → (T ⟶ H)), ∃! x : T ⟶ G, ∀ a, x ≫ p a = y a)
    (j : n → (H ⟶ G)) (h1 : ∀ b, j b ≫ p b = 𝟙 H) (h2 : ∀ b c, c ≠ b → j b ≫ p c = 1)
    (f g : G ⟶ H') [IsMonHom f] [IsMonHom g] (h : ∀ b, j b ≫ f = j b ≫ g) : f = g := by
  classical
  haveI := Fintype.ofFinite n
  have ext : ∀ {T : C} (x y : T ⟶ G), (∀ a, x ≫ p a = y ≫ p a) → x = y := fun {T} x y h =>
    (hu T fun a => y ≫ p a).unique h (fun _ => rfl)
  have hcomp : ∀ {K : C} [MonObj K] (k : G ⟶ K) [IsMonHom k] (l : List n),
      (l.map fun b => p b ≫ j b).prod ≫ k = (l.map fun b => p b ≫ j b ≫ k).prod := by
    intro K _ k _ l
    induction l with
    | nil => simp
    | cons b l ih => simp [MonObj.mul_comp, ih]
  have hlist : ∀ (c : n) (l : List n), l.Nodup →
      (l.map fun b => p b ≫ j b ≫ p c).prod = if c ∈ l then p c else 1 := by
    intro c l hl
    induction l with
    | nil => simp
    | cons b l ih =>
      rw [List.map_cons, List.prod_cons, ih (List.nodup_cons.mp hl).2]
      by_cases hbc : b = c
      · subst hbc
        have hnot : b ∉ l := (List.nodup_cons.mp hl).1
        simp [h1, hnot]
      · simp [h2 b c (Ne.symm hbc), Ne.symm hbc]
  have hs : (Finset.univ.toList.map fun b => p b ≫ j b).prod = 𝟙 G := by
    apply ext
    intro c
    haveI := hp c
    rw [hcomp (p c), hlist c _ (Finset.nodup_toList _)]
    simp
  calc f = (Finset.univ.toList.map fun b => p b ≫ j b).prod ≫ f := by rw [hs, Category.id_comp]
    _ = (Finset.univ.toList.map fun b => p b ≫ j b ≫ f).prod := hcomp f _
    _ = (Finset.univ.toList.map fun b => p b ≫ j b ≫ g).prod := by simp only [h]
    _ = (Finset.univ.toList.map fun b => p b ≫ j b).prod ≫ g := (hcomp g _).symm
    _ = g := by rw [hs, Category.id_comp]

end General

theorem exists_diagonal : ∀ (K : Type) [Field K] [IsAlgClosed K] (G₀ G₁ H₀ H₁ : Over (Sp K)) [GrpObj G₀] [GrpObj G₁] [GrpObj H₀] [GrpObj H₁] [IsCommMonObj H₀] [IsCommMonObj H₁], IsSemiAbelian H₀ → IsSemiAbelian H₁ → ∀ (l : ℕ), l.Prime → (l : K) ≠ 0 → ∀ (p₀ : Fin 8 → (G₀ ⟶ H₀)) (p₁ : Fin 8 → (G₁ ⟶ H₁)), (∀ a, IsMonHom (p₀ a)) → (∀ a, IsMonHom (p₁ a)) → (∀ (T : Over (Sp K)) (y : Fin 8 → (T ⟶ H₀)), ∃! x : T ⟶ G₀, ∀ a, x ≫ p₀ a = y a) → (∀ (T : Over (Sp K)) (y : Fin 8 → (T ⟶ H₁)), ∃! x : T ⟶ G₁, ∀ a, x ≫ p₁ a = y a) → ∀ (F : G₀ ⟶ G₁), IsMonHom F → IsIso F → (∀ (z z' : 𝟙_ (Over (Sp K)) ⟶ G₀), (∃ k : ℕ, z ^ (l ^ k) = 1) → (∃ k : ℕ, z' ^ (l ^ k) = 1) → ∀ a a', z ≫ p₀ a = z' ≫ p₀ a' → z ≫ F ≫ p₁ a = z' ≫ F ≫ p₁ a') → ∃ f₁ : H₀ ⟶ H₁, IsMonHom f₁ ∧ IsIso f₁ ∧ ∀ a, F ≫ p₁ a = p₀ a ≫ f₁ := by
  intro K _ _ G₀ G₁ H₀ H₁ _ _ _ _ _ _ hH₀ hH₁ l hl hlK p₀ p₁ hp₀ hp₁ hu₀ hu₁ F hF hFi htor
  classical
  obtain ⟨j₀, hj₀m, hj₀1, hj₀2⟩ := exists_sections p₀ hp₀ hu₀
  obtain ⟨j₁, hj₁m, hj₁1, hj₁2⟩ := exists_sections p₁ hp₁ hu₁
  haveI := hF
  haveI := hFi
  haveI := fun a => hp₀ a
  haveI := fun a => hp₁ a
  haveI := fun b => hj₀m b
  have hpj : ∀ b a : Fin 8, j₀ b ≫ p₀ a = if a = b then 𝟙 H₀ else 1 := by
    intro b a
    split_ifs with h
    · subst h; exact hj₀1 a
    · exact hj₀2 b a h
  have hpj₁ : ∀ b a : Fin 8, j₁ b ≫ p₁ a = if a = b then 𝟙 H₁ else 1 := by
    intro b a
    split_ifs with h
    · subst h; exact hj₁1 a
    · exact hj₁2 b a h

  have htors : ∀ (b : Fin 8) (y : 𝟙_ (Over (Sp K)) ⟶ H₀) (k : ℕ), y ^ (l ^ k) = 1 →
      ∃ k : ℕ, (y ≫ j₀ b) ^ (l ^ k) = 1 := by
    intro b y k hy
    haveI := hj₀m b
    exact ⟨k, by rw [← MonObj.pow_comp, hy, MonObj.one_comp]⟩

  have hoff : ∀ b a : Fin 8, a ≠ b → j₀ b ≫ F ≫ p₁ a = 1 := by
    intro b a hab
    haveI := hj₀m b
    haveI := hp₁ a
    refine GlobalTheory.TorsionDense.eq_one_of_torsion_comp_eq_one K H₀ H₁ hH₀ hH₁ l hl hlK _ inferInstance
      (fun _ _ y k hy => ?_)
    have := htor (y ≫ j₀ b) 1 (htors b y k hy) ⟨0, _root_.one_pow _⟩ a a
      (by rw [Category.assoc, hpj, if_neg hab, MonObj.comp_one, MonObj.one_comp])
    rw [MonObj.one_comp (F ≫ p₁ a)] at this
    simpa [Category.assoc] using this

  have hdiag : ∀ a : Fin 8, j₀ a ≫ F ≫ p₁ a = j₀ 0 ≫ F ≫ p₁ 0 := by
    intro a
    haveI := hj₀m a
    haveI := hj₀m 0
    haveI := hp₁ a
    haveI := hp₁ 0
    have hpt : ∀ (T : Over (Sp K)) (x : T ⟶ H₀),
        x ≫ ((j₀ a ≫ F ≫ p₁ a) * (j₀ 0 ≫ F ≫ p₁ 0)⁻¹) =
          (x ≫ j₀ a ≫ F ≫ p₁ a) * (x ≫ j₀ 0 ≫ F ≫ p₁ 0)⁻¹ := by
      intro T x
      rw [MonObj.comp_mul, GrpObj.comp_inv]
    have hmon : IsMonHom ((j₀ a ≫ F ≫ p₁ a) * (j₀ 0 ≫ F ≫ p₁ 0)⁻¹) := by
      apply isMonHom_of_points
      · intro T
        rw [hpt, MonObj.one_comp, MonObj.one_comp, _root_.inv_one, _root_.mul_one]
      · intro T x y
        rw [hpt, hpt, hpt, MonObj.mul_comp, MonObj.mul_comp, _root_.mul_inv, _root_.mul_mul_mul_comm]
    have h1 := GlobalTheory.TorsionDense.eq_one_of_torsion_comp_eq_one K H₀ H₁ hH₀ hH₁ l hl hlK _ hmon
      (fun _ _ y k hy => by
        have := htor (y ≫ j₀ a) (y ≫ j₀ 0) (htors a y k hy) (htors 0 y k hy) a 0
          (by rw [Category.assoc, Category.assoc, hpj, hpj, if_pos rfl, if_pos rfl])
        rw [hpt, _root_.mul_inv_eq_one]
        simpa [Category.assoc] using this)
    exact _root_.mul_inv_eq_one.mp h1
  let f₁ : H₀ ⟶ H₁ := j₀ 0 ≫ F ≫ p₁ 0
  haveI : IsMonHom f₁ := by
    haveI := hj₀m 0
    haveI := hp₁ 0
    dsimp [f₁]
    infer_instance
  have hcomm : ∀ a, F ≫ p₁ a = p₀ a ≫ f₁ := by
    intro a
    haveI := hp₁ a
    haveI := hp₀ a
    refine hom_ext_sections p₀ hp₀ hu₀ j₀ hj₀1 hj₀2 _ _ (fun b => ?_)
    rw [← Category.assoc (j₀ b) (p₀ a), hpj]
    split_ifs with hab
    · subst hab
      rw [Category.id_comp, hdiag]
    · rw [hoff b a hab, MonObj.one_comp]
  have hsec : j₀ 0 ≫ F = f₁ ≫ j₁ 0 := by
    refine (hu₁ H₀ fun a => (f₁ ≫ j₁ 0) ≫ p₁ a).unique (fun a => ?_) (fun _ => rfl)
    rw [Category.assoc, hcomm, ← Category.assoc, hpj, Category.assoc, hpj₁]
    split_ifs
    · simp
    · rw [MonObj.one_comp, MonObj.comp_one]
  refine ⟨f₁, inferInstance, ⟨⟨j₁ 0 ≫ inv F ≫ p₀ 0, ?_, ?_⟩⟩, hcomm⟩
  · rw [← Category.assoc, ← hsec, Category.assoc, IsIso.hom_inv_id_assoc, hj₀1]
  · rw [Category.assoc, Category.assoc, ← hcomm, IsIso.inv_hom_id_assoc, hj₁1]

end GlobalTheory.PowerDiagonal
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open TopologicalSpace

namespace GlobalTheory.Mum.LBDesc

open ReciprocityTheory.ChartRestriction.G.Geo.Tor (gm gm_res gm_pull unit_ext glue_unit exists_chart gw PGen)

variable {Z Y : Scheme.{0}}

def toZ (V : Z.Opens) {O : V.toScheme.Opens} (a : Γ(V.toScheme, O)ˣ) : Γ(Z, V.ι ''ᵁ O)ˣ := a

theorem toZ_res (V : Z.Opens) {O O' : V.toScheme.Opens} (h : O' ≤ O) (a : Γ(V.toScheme, O)ˣ) :
    toZ V (res h a) = res (V.ι.image_mono h) (toZ V a) := rfl

theorem toZ_mul (V : Z.Opens) {O : V.toScheme.Opens} (a b : Γ(V.toScheme, O)ˣ) :
    toZ V (a * b) = toZ V a * toZ V b := rfl

theorem image_preimage_le' (V : Z.Opens) (O : Z.Opens) : V.ι ''ᵁ V.ι ⁻¹ᵁ O ≤ O :=
  Set.image_preimage_subset _ _

theorem toZ_pullU (V : Z.Opens) (O : Z.Opens) (a : Γ(Z, O)ˣ) :
    toZ V (pullU V.ι O a) = res (image_preimage_le' V O) a := rfl

theorem res_toZ_pullU (V : Z.Opens) (O : Z.Opens) {W : Z.Opens} (hW : W ≤ V.ι ''ᵁ V.ι ⁻¹ᵁ O) (a : Γ(Z, O)ˣ) :
    res hW (toZ V (pullU V.ι O a)) = res (hW.trans (image_preimage_le' V O)) a := by
  rw [toZ_pullU, LB.res_res]

theorem transport (L' : LB Z) (V : Z.Opens) (t : LB.Gen (L'.pull V.ι)) (ht : t.IsGen) :
    ∃ T : ∀ k : L'.ι, Γ(Z, V ⊓ L'.U k)ˣ, ∀ k k',
      res (inf_le_left : V ⊓ L'.U k ⊓ (V ⊓ L'.U k') ≤ V ⊓ L'.U k) (T k) =
        res (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) :
          V ⊓ L'.U k ⊓ (V ⊓ L'.U k') ≤ L'.U k ⊓ L'.U k') (L'.g k k') *
        res (inf_le_right : V ⊓ L'.U k ⊓ (V ⊓ L'.U k') ≤ V ⊓ L'.U k') (T k') := by
  have hle : ∀ k, V ⊓ L'.U k ≤ V.ι ''ᵁ LB.wchart L' (fun _ : PUnit => V.ι) (fun _ => k) := by
    intro k z hz
    exact ⟨⟨z, hz.1⟩, Set.mem_iInter.2 fun _ => hz.2, rfl⟩
  refine ⟨fun k => res (hle k) (toZ V (LB.ts t (fun _ => k))), fun k k' => ?_⟩
  have hle2 : V ⊓ L'.U k ⊓ (V ⊓ L'.U k') ≤ V.ι ''ᵁ (LB.wchart L' (fun _ : PUnit => V.ι) (fun _ => k) ⊓
      LB.wchart L' (fun _ : PUnit => V.ι) (fun _ => k')) := fun z hz =>
    ⟨⟨z, hz.1.1⟩, ⟨Set.mem_iInter.2 fun _ => hz.1.2, Set.mem_iInter.2 fun _ => hz.2.2⟩, rfl⟩
  have e := congrArg (fun x => res hle2 (toZ V x)) ((LB.isGen_iff L' t).1 ht (fun _ => k) (fun _ => k'))
  simp only [toZ_mul, toZ_res, map_mul, LB.res_res, LB.lcg, Fintype.prod_unique, zpow_one, res_toZ_pullU] at e
  simp only [LB.res_res]
  exact e

theorem gm_compat (L' : LB Z) (V : Z.Opens) (T : ∀ k : L'.ι, Γ(Z, V ⊓ L'.U k)ˣ)
    (hT : ∀ k k', res (inf_le_left : V ⊓ L'.U k ⊓ (V ⊓ L'.U k') ≤ V ⊓ L'.U k) (T k) =
        res (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) :
          V ⊓ L'.U k ⊓ (V ⊓ L'.U k') ≤ L'.U k ⊓ L'.U k') (L'.g k k') *
        res (inf_le_right : V ⊓ L'.U k ⊓ (V ⊓ L'.U k') ≤ V ⊓ L'.U k') (T k'))
    {W : Scheme.{0}} (f : W ⟶ Z) (w : W) (k k' : L'.ι) (hV : f w ∈ V) (hk : f w ∈ L'.U k)
    (hk' : f w ∈ L'.U k') :
    gm f w (V ⊓ L'.U k) (T k) = gm f w (L'.U k ⊓ L'.U k') (L'.g k k') * gm f w (V ⊓ L'.U k') (T k') := by
  have hm : f w ∈ V ⊓ L'.U k ⊓ (V ⊓ L'.U k') := ⟨⟨hV, hk⟩, hV, hk'⟩
  have e := congrArg (gm f w (V ⊓ L'.U k ⊓ (V ⊓ L'.U k'))) (hT k k')
  rwa [map_mul, gm_res f w _ hm, gm_res f w _ hm, gm_res f w _ hm] at e

theorem ratio (p : Z ⟶ Y) (L' : LB Z) (hL' : L'.IsLB) {V₁ V₂ : Y.Opens}
    (T₁ : ∀ k : L'.ι, Γ(Z, p ⁻¹ᵁ V₁ ⊓ L'.U k)ˣ) (T₂ : ∀ k : L'.ι, Γ(Z, p ⁻¹ᵁ V₂ ⊓ L'.U k)ˣ)
    (h₁ : ∀ {W : Scheme.{0}} (f : W ⟶ Z) (w : W) (k k' : L'.ι), f w ∈ p ⁻¹ᵁ V₁ → f w ∈ L'.U k → f w ∈ L'.U k' →
      gm f w _ (T₁ k) = gm f w (L'.U k ⊓ L'.U k') (L'.g k k') * gm f w _ (T₁ k'))
    (h₂ : ∀ {W : Scheme.{0}} (f : W ⟶ Z) (w : W) (k k' : L'.ι), f w ∈ p ⁻¹ᵁ V₂ → f w ∈ L'.U k → f w ∈ L'.U k' →
      gm f w _ (T₂ k) = gm f w (L'.U k ⊓ L'.U k') (L'.g k k') * gm f w _ (T₂ k')) :
    ∃ r : Γ(Z, p ⁻¹ᵁ (V₁ ⊓ V₂))ˣ, ∀ {W : Scheme.{0}} (f : W ⟶ Z) (w : W) (k : L'.ι),
      f w ∈ p ⁻¹ᵁ (V₁ ⊓ V₂) → f w ∈ L'.U k → gm f w _ r = gm f w _ (T₂ k) * (gm f w _ (T₁ k))⁻¹ := by
  have l₁ : ∀ k, p ⁻¹ᵁ (V₁ ⊓ V₂) ⊓ L'.U k ≤ p ⁻¹ᵁ V₁ ⊓ L'.U k := fun _ x hx => ⟨hx.1.1, hx.2⟩
  have l₂ : ∀ k, p ⁻¹ᵁ (V₁ ⊓ V₂) ⊓ L'.U k ≤ p ⁻¹ᵁ V₂ ⊓ L'.U k := fun _ x hx => ⟨hx.1.2, hx.2⟩
  have hu : ∀ {W : Scheme.{0}} (f : W ⟶ Z) (w : W) (k : L'.ι) (hw : f w ∈ p ⁻¹ᵁ (V₁ ⊓ V₂) ⊓ L'.U k),
      gm f w _ (res (l₂ k) (T₂ k) * (res (l₁ k) (T₁ k))⁻¹) = gm f w _ (T₂ k) * (gm f w _ (T₁ k))⁻¹ := by
    intro W f w k hw
    rw [map_mul, map_inv, gm_res f w _ hw, gm_res f w _ hw]
  obtain ⟨s, hs⟩ := glue_unit (p ⁻¹ᵁ (V₁ ⊓ V₂)) (fun k => p ⁻¹ᵁ (V₁ ⊓ V₂) ⊓ L'.U k) (fun _ => inf_le_left)
    (fun x hx => by
      obtain ⟨k, hk⟩ := exists_chart hL' x
      exact Opens.mem_iSup.2 ⟨k, hx, hk⟩)
    (fun k => res (l₂ k) (T₂ k) * (res (l₁ k) (T₁ k))⁻¹)
    (fun i j x hx => by
      rw [hu (𝟙 Z) x i hx.1, hu (𝟙 Z) x j hx.2, h₁ (𝟙 Z) x i j hx.1.1.1 hx.1.2 hx.2.2,
        h₂ (𝟙 Z) x i j hx.1.1.2 hx.1.2 hx.2.2, mul_inv, _root_.mul_mul_mul_comm, _root_.mul_inv_cancel, _root_.one_mul])
  refine ⟨s, fun f w k hw hk => ?_⟩
  have hm : f w ∈ p ⁻¹ᵁ (V₁ ⊓ V₂) ⊓ L'.U k := ⟨hw, hk⟩
  rw [← gm_res f w inf_le_left hm s, hs k, hu f w k hm]

theorem descend (p : Z ⟶ Y) (hp : ∀ V : Y.Opens, Function.Bijective (p.app V).hom) (O : Y.Opens)
    (r : Γ(Z, p ⁻¹ᵁ O)ˣ) : ∃ g : Γ(Y, O)ˣ, pullU p O g = r := by
  let e := RingEquiv.ofBijective (p.app O).hom (hp O)
  refine ⟨Units.map e.symm.toRingHom.toMonoidHom r, Units.ext ?_⟩
  exact e.apply_symm_apply r.val

theorem eq_of_gm (p : Z ⟶ Y) (hp : ∀ V : Y.Opens, Function.Bijective (p.app V).hom) {O : Y.Opens}
    {a b : Γ(Y, O)ˣ} (h : ∀ z : Z, p z ∈ O → gm (𝟙 Z ≫ p) z O a = gm (𝟙 Z ≫ p) z O b) : a = b := by
  have e : pullU p O a = pullU p O b := unit_ext fun z hz => by
    rw [gm_pull (𝟙 Z) p z O hz a, gm_pull (𝟙 Z) p z O hz b]
    exact h z hz
  exact Units.ext ((hp O).1 (congrArg Units.val e))

def descLB (V : Y → Y.Opens) (g : ∀ y y', Γ(Y, V y ⊓ V y')ˣ) : LB Y := ⟨Y, V, g⟩

theorem isLB_descLB (p : Z ⟶ Y) (hp : ∀ V : Y.Opens, Function.Bijective (p.app V).hom) (L' : LB Z) (hL' : L'.IsLB)
    (V : Y → Y.Opens) (hyV : ∀ y, y ∈ V y) (T : ∀ (y : Y) (k : L'.ι), Γ(Z, p ⁻¹ᵁ V y ⊓ L'.U k)ˣ)
    (g : ∀ y y', Γ(Y, V y ⊓ V y')ˣ)
    (key : ∀ {W : Scheme.{0}} (f : W ⟶ Z) (w : W) (y y' : Y) (k : L'.ι), p (f w) ∈ V y → p (f w) ∈ V y' →
      f w ∈ L'.U k → gm (f ≫ p) w ((descLB V g).U y ⊓ (descLB V g).U y') ((descLB V g).g y y') =
        gm f w _ (T y' k) * (gm f w _ (T y k))⁻¹) :
    (descLB V g).IsLB := {
  cover := eq_top_iff.2 fun y _ => Opens.mem_iSup.2 ⟨y, hyV y⟩
  g_self := fun y => eq_of_gm p hp fun z hz => by
    obtain ⟨k, hk⟩ := exists_chart hL' z
    rw [gm_res (𝟙 Z ≫ p) z _ hz, map_one]
    exact (key (𝟙 Z) z y y k hz hz hk).trans (mul_inv_cancel _)
  cocycle := fun a b c => eq_of_gm p hp fun z hz => by
    obtain ⟨k, hk⟩ := exists_chart hL' z
    rw [map_mul, gm_res (𝟙 Z ≫ p) z _ hz, gm_res (𝟙 Z ≫ p) z _ hz, gm_res (𝟙 Z ≫ p) z _ hz,
      key (𝟙 Z) z a b k hz.1.1 hz.1.2 hk, key (𝟙 Z) z b c k hz.1.2 hz.2 hk,
      key (𝟙 Z) z a c k hz.1.1 hz.2 hk]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel }

theorem chart_le (p : Z ⟶ Y) (L' : LB Z) (V : Y → Y.Opens) (g : ∀ y y', Γ(Y, V y ⊓ V y')ˣ)
    (q : (LB.div ((descLB V g).pull p) L').ι) :
    (LB.div ((descLB V g).pull p) L').U q ≤ p ⁻¹ᵁ V (q.1 PUnit.unit) ⊓ L'.U q.2 :=
  fun _ hx => ⟨Set.mem_iInter.1 hx.1 PUnit.unit, hx.2⟩

def descIso (p : Z ⟶ Y) (L' : LB Z) (V : Y → Y.Opens) (T : ∀ (y : Y) (k : L'.ι), Γ(Z, p ⁻¹ᵁ V y ⊓ L'.U k)ˣ)
    (g : ∀ y y', Γ(Y, V y ⊓ V y')ˣ) : LB.Iso L' ((descLB V g).pull p) :=
  ⟨fun q => (res (chart_le p L' V g q) (T (q.1 PUnit.unit) q.2))⁻¹⟩

theorem gw_descIso (p : Z ⟶ Y) (L' : LB Z) (V : Y → Y.Opens) (T : ∀ (y : Y) (k : L'.ι), Γ(Z, p ⁻¹ᵁ V y ⊓ L'.U k)ˣ)
    (g : ∀ y y', Γ(Y, V y ⊓ V y')ˣ) {W : Scheme.{0}} (f : W ⟶ Z) (x : W) (j : Y) (k : L'.ι)
    (hj : p (f x) ∈ V j) (hk : f x ∈ L'.U k) :
    gw (descIso p L' V T g) f x j k = (gm f x _ (T j k))⁻¹ := by
  unfold gw descIso
  exact (map_inv (gm f x _) _).trans (congrArg (·⁻¹) (gm_res f x (chart_le p L' V g (fun _ => j, k))
    ⟨Set.mem_iInter.2 fun _ => hj, hk⟩ (T j k)))

theorem isGen_descIso (p : Z ⟶ Y) (L' : LB Z) (V : Y → Y.Opens) (T : ∀ (y : Y) (k : L'.ι), Γ(Z, p ⁻¹ᵁ V y ⊓ L'.U k)ˣ)
    (g : ∀ y y', Γ(Y, V y ⊓ V y')ˣ)
    (hc : ∀ (y : Y) {W : Scheme.{0}} (f : W ⟶ Z) (w : W) (k k' : L'.ι), f w ∈ p ⁻¹ᵁ V y → f w ∈ L'.U k →
      f w ∈ L'.U k' → gm f w _ (T y k) = gm f w (L'.U k ⊓ L'.U k') (L'.g k k') * gm f w _ (T y k'))
    (key : ∀ {W : Scheme.{0}} (f : W ⟶ Z) (w : W) (y y' : Y) (k : L'.ι), p (f w) ∈ V y → p (f w) ∈ V y' →
      f w ∈ L'.U k → gm (f ≫ p) w ((descLB V g).U y ⊓ (descLB V g).U y') ((descLB V g).g y y') =
        gm f w _ (T y' k) * (gm f w _ (T y k))⁻¹) :
    (descIso p L' V T g).IsGen := by
  rw [ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGen_iff]
  intro W f x j j' k k' hj hj' hk hk'
  rw [gw_descIso p L' V T g f x j k hj hk, gw_descIso p L' V T g f x j' k' hj' hk',
    key f x j j' k hj hj' hk, hc j' f x k k' hj' hk hk']
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end GlobalTheory.Mum.LBDesc

namespace GlobalTheory.Mum

open ReciprocityTheory.ChartRestriction.G.Geo.Tor (gm gm_pull)
open GlobalTheory.Mum.LBDesc

theorem lb_descend : ∀ (Z Y : Scheme.{0}) (p : Z ⟶ Y), (∀ V : Y.Opens, Function.Bijective (p.app V).hom) →
    ∀ L' : LB Z, L'.IsLB → (∀ y : Y, ∃ V : Y.Opens, y ∈ V ∧ ∃ t : LB.Gen (L'.pull (p ⁻¹ᵁ V).ι), t.IsGen) →
    ∃ L : LB Y, L.IsLB ∧ LBIso L' (L.pull p) := by
  intro Z Y p hp L' hL' hloc
  choose V hyV t ht using hloc
  choose T hT using fun y => transport L' (p ⁻¹ᵁ V y) (t y) (ht y)
  have hc : ∀ (y : Y) {W : Scheme.{0}} (f : W ⟶ Z) (w : W) (k k' : L'.ι), f w ∈ p ⁻¹ᵁ V y → f w ∈ L'.U k →
      f w ∈ L'.U k' → gm f w _ (T y k) = gm f w (L'.U k ⊓ L'.U k') (L'.g k k') * gm f w _ (T y k') :=
    fun y _ f w k k' h hk hk' => gm_compat L' _ (T y) (hT y) f w k k' h hk hk'
  choose r hr using fun y y' => ratio p L' hL' (T y) (T y') (hc y) (hc y')
  choose g hg using fun y y' => descend p hp _ (r y y')
  have key : ∀ {W : Scheme.{0}} (f : W ⟶ Z) (w : W) (y y' : Y) (k : L'.ι), p (f w) ∈ V y → p (f w) ∈ V y' →
      f w ∈ L'.U k → gm (f ≫ p) w ((descLB V g).U y ⊓ (descLB V g).U y') ((descLB V g).g y y') =
        gm f w _ (T y' k) * (gm f w _ (T y k))⁻¹ := by
    intro W f w y y' k h1 h2 hk
    exact (gm_pull f p w (V y ⊓ V y') ⟨h1, h2⟩ (g y y')).symm.trans
      ((congrArg _ (hg y y')).trans (hr y y' f w k ⟨h1, h2⟩ hk))
  exact ⟨descLB V g, isLB_descLB p hp L' hL' V hyV T g key, descIso p L' V T g,
    isGen_descIso p L' V T g hc key⟩

end GlobalTheory.Mum
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum.FibBC

theorem pullCompIso_hom_eq {T S' S : Scheme.{0}} (p : T ⟶ S') (f : S' ⟶ S) (G : Over S) [GrpObj G] :
    (pullCompIso p f G).hom = (Over.pullbackComp p f).hom.app G := Category.comp_id _

theorem pullCompIso_fst {T S' S : Scheme.{0}} (p : T ⟶ S') (f : S' ⟶ S) (G : Over S) [GrpObj G] :
    (pullCompIso p f G).hom.left ≫ pullback.fst _ p ≫ pullback.fst G.hom f = pullback.fst G.hom (p ≫ f) := by
  rw [pullCompIso_hom_eq]
  simp [Over.pullbackComp, Over.mapComp, pullback.lift_fst_assoc, pullback.lift_fst]

theorem pullCompIso_inv_fst {T S' S : Scheme.{0}} (p : T ⟶ S') (f : S' ⟶ S) (G : Over S) [GrpObj G] :
    (pullCompIso p f G).inv.left ≫ pullback.fst G.hom (p ≫ f) = pullback.fst _ p ≫ pullback.fst G.hom f := by
  rw [← pullCompIso_fst, ← Category.assoc, ← Over.comp_left, Iso.inv_hom_id, Over.id_left, Category.id_comp]

theorem pullback_map_fst {S S' : Scheme.{0}} (g : S' ⟶ S) {A B : Over S} (u : A ⟶ B) :
    ((Over.pullback g).map u).left ≫ pullback.fst B.hom g = pullback.fst A.hom g ≫ u.left :=
  pullback.lift_fst _ _ _

theorem fibre_baseChange : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (W' : Type) [CommRing W'] [IsLocalRing W'] (G' : Over (Sp W')) [GrpObj G'] (ξ' : Sp W' ⟶ S) (β : G'.left ⟶ G.left), IsGrpPullback G' G ξ' β → ∀ (k : Type) [Field k] (Y : Over (Sp k)) [GrpObj Y] (κ' : k →+* ResidueField W') (e' : (Over.pullback (spMap (residue W'))).obj G' ≅ (Over.pullback (spMap κ')).obj Y), IsMonHom e'.hom → ∀ (Ω : Type) [Field Ω] (x : Sp Ω ⟶ S) (κ : k →+* Ω) (Ω' : Type) [Field Ω'] (io : Ω →+* Ω') (i₂ : ResidueField W' →+* Ω'), spMap io ≫ x = spMap i₂ ≫ spMap (residue W') ≫ ξ' → io.comp κ = i₂.comp κ' → ∃ (e : (Over.pullback (spMap io ≫ x)).obj G ≅ (Over.pullback (spMap (io.comp κ))).obj Y) (τ : ((Over.pullback (spMap io ≫ x)).obj G).left ⟶ ((Over.pullback (spMap (residue W'))).obj G').left), IsMonHom e.hom ∧ τ ≫ pullback.fst G'.hom (spMap (residue W')) ≫ β = pullback.fst G.hom (spMap io ≫ x) ∧ e.hom.left ≫ pullback.fst Y.hom (spMap (io.comp κ)) = τ ≫ e'.hom.left ≫ pullback.fst Y.hom (spMap κ') := by
  intro S G _ W' _ _ G' _ ξ' β hβ k _ Y _ κ' e' he' Ω _ x κ Ω' _ io i₂ hc hκ
  have hm : spMap i₂ ≫ spMap κ' = spMap (io.comp κ) := by
    rw [hκ, ← Spec.map_comp]; rfl
  rw [← hm]

  have h₁ : IsGrpPullback ((Over.pullback (spMap i₂ ≫ spMap (residue W'))).obj G') G (spMap io ≫ x)
      (pullback.fst G'.hom (spMap i₂ ≫ spMap (residue W')) ≫ β) :=
    ((isGrpPullback_pullback G' (spMap i₂ ≫ spMap (residue W'))).comp hβ).congr
      (by rw [hc, Category.assoc]) rfl
  obtain ⟨e₁, he₁, he₁f⟩ := grpPullback_iso (isGrpPullback_pullback G (spMap io ≫ x)) h₁
  let e₂ := pullCompIso (spMap i₂) (spMap (residue W')) G'
  let e₃ := (Over.pullback (spMap i₂)).mapIso e'
  let e₄ := (pullCompIso (spMap i₂) (spMap κ') Y).symm
  have i₃ : IsMonHom e₃.hom := by show IsMonHom ((Over.pullback (spMap i₂)).map e'.hom); infer_instance
  have i₄ : IsMonHom e₄.hom := by show IsMonHom (pullCompIso (spMap i₂) (spMap κ') Y).inv; infer_instance
  have f₂ : e₂.hom.left ≫ pullback.fst _ (spMap i₂) ≫ pullback.fst G'.hom (spMap (residue W')) =
      pullback.fst G'.hom (spMap i₂ ≫ spMap (residue W')) := pullCompIso_fst _ _ _
  have f₃ : e₃.hom.left ≫ pullback.fst _ (spMap i₂) = pullback.fst _ (spMap i₂) ≫ e'.hom.left :=
    pullback_map_fst _ _
  have f₄ : e₄.hom.left ≫ pullback.fst Y.hom (spMap i₂ ≫ spMap κ') =
      pullback.fst _ (spMap i₂) ≫ pullback.fst Y.hom (spMap κ') := pullCompIso_inv_fst _ _ _
  refine ⟨e₁ ≪≫ e₂ ≪≫ e₃ ≪≫ e₄, e₁.hom.left ≫ e₂.hom.left ≫ pullback.fst _ (spMap i₂), ?_, ?_, ?_⟩
  · show IsMonHom (e₁.hom ≫ e₂.hom ≫ e₃.hom ≫ e₄.hom); infer_instance
  · rw [Category.assoc, Category.assoc, reassoc_of% f₂, he₁f]
  · show (e₁.hom ≫ e₂.hom ≫ e₃.hom ≫ e₄.hom).left ≫ _ = _
    simp only [Over.comp_left, Category.assoc]
    rw [f₄, reassoc_of% f₃]

end GlobalTheory.Mum.FibBC
end
end

end

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.groupFibre_baseChange_common_field_iso : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (W' : Type) [CommRing W'] [IsLocalRing W'] (G' : Over (Sp W')) [GrpObj G'] (ξ' : Sp W' ⟶ S) (β : G'.left ⟶ G.left), IsGrpPullback G' G ξ' β → ∀ (k : Type) [Field k] (Y : Over (Sp k)) [GrpObj Y] (κ' : k →+* ResidueField W') (e' : (Over.pullback (spMap (residue W'))).obj G' ≅ (Over.pullback (spMap κ')).obj Y), IsMonHom e'.hom → ∀ (Ω : Type) [Field Ω] (x : Sp Ω ⟶ S) (κ : k →+* Ω) (Ω' : Type) [Field Ω'] (io : Ω →+* Ω') (i₂ : ResidueField W' →+* Ω'), spMap io ≫ x = spMap i₂ ≫ spMap (residue W') ≫ ξ' → io.comp κ = i₂.comp κ' → ∃ (e : (Over.pullback (spMap io ≫ x)).obj G ≅ (Over.pullback (spMap (io.comp κ))).obj Y) (τ : ((Over.pullback (spMap io ≫ x)).obj G).left ⟶ ((Over.pullback (spMap (residue W'))).obj G').left), IsMonHom e.hom ∧ τ ≫ pullback.fst G'.hom (spMap (residue W')) ≫ β = pullback.fst G.hom (spMap io ≫ x) ∧ e.hom.left ≫ pullback.fst Y.hom (spMap (io.comp κ)) = τ ≫ e'.hom.left ≫ pullback.fst Y.hom (spMap κ') := by
  first | exact @GlobalTheory.Mum.FibBC.fibre_baseChange | exact GlobalTheory.Mum.FibBC.fibre_baseChange | (intros; apply GlobalTheory.Mum.FibBC.fibre_baseChange <;> assumption)

end
end

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_lineBundle_descent_bijective_app : ∀ (Z Y : Scheme.{0}) (p : Z ⟶ Y), (∀ V : Y.Opens, Function.Bijective (p.app V).hom) → ∀ L' : LB Z, L'.IsLB → (∀ y : Y, ∃ V : Y.Opens, y ∈ V ∧ ∃ t : LB.Gen (L'.pull (p ⁻¹ᵁ V).ι), t.IsGen) → ∃ L : LB Y, L.IsLB ∧ LBIso L' (L.pull p) := by
  first | exact @GlobalTheory.Mum.lb_descend | exact GlobalTheory.Mum.lb_descend | (intros; apply GlobalTheory.Mum.lb_descend <;> assumption)

end
end
