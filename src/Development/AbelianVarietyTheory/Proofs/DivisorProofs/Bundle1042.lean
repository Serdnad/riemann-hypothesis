module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle535
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle590
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle620
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle667
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle854
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle884
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle926
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle904
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle862
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle940
public import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle947
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle949
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle091
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle987
public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1015
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle029
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLineBundleDescentToSubfield
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.PullGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle004

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LBDescent

set_option autoImplicit false

namespace GlobalTheory.LBDescent

private theorem ratio_eq {G : Type} [CommGroup G] (A B C D g : G) (h1 : A = g * B) (h2 : C = g * D) :
    C * A⁻¹ = D * B⁻¹ := by
  subst h1 h2; rw [mul_inv_rev, mul_comm g D, _root_.mul_assoc, mul_inv_cancel_comm_assoc]

private theorem ratio_mul {G : Type} [CommGroup G] (A B C : G) : (B * A⁻¹) * (C * B⁻¹) = C * A⁻¹ := by
  rw [mul_comm (B * A⁻¹), _root_.mul_assoc, inv_mul_cancel_left]

private theorem ratio_inv {G : Type} [CommGroup G] (A S g T : G) (h : S = g * T) :
    A⁻¹ = S * A⁻¹ * g⁻¹ * T⁻¹ := by
  rw [_root_.mul_assoc _ g⁻¹, ← mul_inv, ← h, mul_inv_cancel_comm]

theorem exists_lb_of_invariant_frames : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) [QuasiCompact f] [Flat f] [Surjective f] (L : LB X), L.IsLB →
    ∀ (φ : ∀ i j, Γ(pullback f f, chart f L i j)ˣ),
    (∀ y : Y, ∃ V : Y.Opens, y ∈ V ∧ ∃ s : ∀ i, Γ(X, f ⁻¹ᵁ V ⊓ L.U i)ˣ,
      (∀ (i j : L.ι) (x : X), f x ∈ V → x ∈ L.U i → x ∈ L.U j →
        gm (𝟙 X) x _ (s i) = gm (𝟙 X) x _ (L.g i j) * gm (𝟙 X) x _ (s j)) ∧
      ∀ (z : ↥(pullback f f)) (i j : L.ι), f (pullback.fst f f z) ∈ V → pullback.fst f f z ∈ L.U i →
        pullback.snd f f z ∈ L.U j →
        gm (pullback.fst f f) z _ (s i) * gm (𝟙 _) z _ (φ i j) = gm (pullback.snd f f) z _ (s j)) →
    ∃ L' : LB Y, L'.IsLB ∧ LBIso L (L'.pull f) := by
  intro X Y f _ _ _ L hL φ H
  choose V hV s hs1 hs2 using H
  have hW : ∀ a b i, f ⁻¹ᵁ (V a ⊓ V b) ⊓ L.U i ≤ f ⁻¹ᵁ (V a ⊓ V b) := fun a b i => inf_le_left
  have lb : ∀ a b i, f ⁻¹ᵁ (V a ⊓ V b) ⊓ L.U i ≤ f ⁻¹ᵁ V b ⊓ L.U i := fun a b i x hx => ⟨hx.1.2, hx.2⟩
  have la : ∀ a b i, f ⁻¹ᵁ (V a ⊓ V b) ⊓ L.U i ≤ f ⁻¹ᵁ V a ⊓ L.U i := fun a b i x hx => ⟨hx.1.1, hx.2⟩
  have hex : ∀ a b, ∃ t : Γ(X, f ⁻¹ᵁ (V a ⊓ V b))ˣ, ∀ i,
      res (hW a b i) t = res (lb a b i) (s b i) * (res (la a b i) (s a i))⁻¹ := by
    intro a b
    refine glue_unit _ _ (hW a b) ?_ _ ?_
    · intro x hx
      obtain ⟨i, hi⟩ := exists_chart hL x
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, hx, hi⟩
    · intro i j x hx
      simp only [map_mul, map_inv]
      rw [gm_res _ x (lb a b i) hx.1, gm_res _ x (la a b i) hx.1, gm_res _ x (lb a b j) hx.2,
        gm_res _ x (la a b j) hx.2]
      exact ratio_eq _ _ _ _ _ (hs1 a i j x hx.1.1.1 hx.1.2 hx.2.2) (hs1 b i j x hx.1.1.2 hx.1.2 hx.2.2)
  choose t ht using hex
  have tform : ∀ a b {Z : Scheme.{0}} (g : Z ⟶ X) (z : Z) (i : L.ι), f (g z) ∈ V a → f (g z) ∈ V b →
      g z ∈ L.U i → gm g z _ (t a b) = gm g z _ (s b i) * (gm g z _ (s a i))⁻¹ := by
    intro a b Z g z i ha hb hi
    have hm : g z ∈ f ⁻¹ᵁ (V a ⊓ V b) ⊓ L.U i := ⟨⟨ha, hb⟩, hi⟩
    rw [← gm_res g z (hW a b i) hm, ht a b i, map_mul, map_inv, gm_res g z (lb a b i) hm,
      gm_res g z (la a b i) hm]
  have hk : ∀ a b, ∃ k : Γ(Y, V a ⊓ V b)ˣ, pullU f _ k = t a b := by
    intro a b
    refine GlobalTheory.FlatDescent.exists_unit_of_gm_eq f (IsPullback.of_hasPullback f f) _ _ fun z hz => ?_
    obtain ⟨i, hi⟩ := exists_chart hL (pullback.fst f f z)
    obtain ⟨j, hj⟩ := exists_chart hL (pullback.snd f f z)
    have e : f (pullback.snd f f z) = f (pullback.fst f f z) :=
      congrArg (fun q : pullback f f ⟶ Y => q z) pullback.condition.symm
    rw [tform a b _ z i hz.1 hz.2 hi, tform a b _ z j (e ▸ hz.1) (e ▸ hz.2) hj,
      ← hs2 a z i j hz.1 hi hj, ← hs2 b z i j hz.2 hi hj]
    group
  choose k hk using hk
  have kform : ∀ a b (x : X) (i : L.ι), f x ∈ V a → f x ∈ V b → x ∈ L.U i →
      gm f x (V a ⊓ V b) (k a b) = gm (𝟙 X) x _ (s b i) * (gm (𝟙 X) x _ (s a i))⁻¹ := by
    intro a b x i ha hb hi
    have := gm_pull (𝟙 X) f x (V a ⊓ V b) ⟨ha, hb⟩ (k a b)
    rw [Category.id_comp, hk] at this
    rw [← this]
    exact tform a b (𝟙 X) x i ha hb hi
  have hL' : LB.IsLB (⟨Y, V, k⟩ : LB Y) := by
    refine ⟨?_, fun a => ?_, fun a b c => ?_⟩
    · exact eq_top_iff.2 fun y _ => TopologicalSpace.Opens.mem_iSup.2 ⟨y, hV y⟩
    · refine GlobalTheory.FlatDescent.unit_ext_of_flat f fun x hx => ?_
      obtain ⟨i, hi⟩ := exists_chart hL x
      rw [gm_res f x _ hx, map_one]
      exact (kform a a x i hx hx hi).trans (mul_inv_cancel _)
    · refine GlobalTheory.FlatDescent.unit_ext_of_flat f fun x hx => ?_
      obtain ⟨i, hi⟩ := exists_chart hL x
      rw [map_mul, gm_res f x _ hx, gm_res f x _ hx, gm_res f x _ hx]
      exact ((congrArg₂ (· * ·) (kform a b x i hx.1.1 hx.1.2 hi) (kform b c x i hx.1.2 hx.2 hi)).trans
        (ratio_mul _ _ _)).trans (kform a c x i hx.1.1 hx.2 hi).symm
  have le1 : ∀ (J : PUnit → Y) (i : L.ι), ((⟨Y, V, k⟩ : LB Y).pull f).U J ⊓ L.U i ≤ f ⁻¹ᵁ V (J PUnit.unit) ⊓ L.U i :=
    fun J i x hx => ⟨mem_pull.1 hx.1, hx.2⟩
  refine ⟨⟨Y, V, k⟩, hL', ⟨fun p => (res (le1 p.1 p.2) (s (p.1 PUnit.unit) p.2))⁻¹⟩, ?_⟩
  rintro ⟨J, i⟩ ⟨J', i'⟩
  apply unit_ext
  intro x hx
  have hj := mem_pull.1 hx.1.1
  have hj' := mem_pull.1 hx.2.1
  have d := gm_div_g (L := (⟨Y, V, k⟩ : LB Y)) (L' := L) (F := f) (𝟙 X) x (J PUnit.unit) (J' PUnit.unit) i i'
    hj hj' hx.1.2 hx.2.2
  rw [map_mul, gm_res _ x _ hx, gm_res _ x _ hx]
  erw [d]
  erw [map_inv, map_inv, gm_res (𝟙 X) x (le1 J i) (show x ∈ ((⟨Y, V, k⟩ : LB Y).pull f).U J ⊓ L.U i from hx.1),
    gm_res (𝟙 X) x (le1 J' i') (show x ∈ ((⟨Y, V, k⟩ : LB Y).pull f).U J' ⊓ L.U i' from hx.2)]
  rw [Category.id_comp]
  erw [kform (J PUnit.unit) (J' PUnit.unit) x i hj hj' hx.1.2]
  exact ratio_inv _ _ _ _ (hs1 (J' PUnit.unit) i i' x hj' hx.1.2 hx.2.2)
end GlobalTheory.LBDescent
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

noncomputable section
namespace GlobalTheory.HomFixUniv

variable {A₀ B₀ X Z T : Scheme.{0}} {N : LB A₀} {H : LB B₀} {mA mB : ℕ}

theorem comb_pull (a : Fin mA → LB.Sec N) (φ : X ⟶ A₀) (p : X ⟶ T) (c : Fin mA → Fin mB → Γ(T, ⊤))
    (r : Z ⟶ X) (z : Z) (q : N.ι) (h : φ (r z) ∈ N.U q) (j : Fin mB) :
    comb a (r ≫ φ) (r ≫ p) c z q j = (r.stalkMap z).hom (comb a φ p c (r z) q j) := by

  simp only [comb, map_sum, map_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [gs_comp r p z ⊤ trivial, gs_comp r φ z _ h]

theorem Generates.pull {a : Fin mA → LB.Sec N} {φ : X ⟶ A₀} {p : X ⟶ T} {c : Fin mA → Fin mB → Γ(T, ⊤)}
    (hg : Generates a φ p c) (r : Z ⟶ X) : Generates a (r ≫ φ) (r ≫ p) c := by
  intro z q hz
  obtain ⟨j, hj⟩ := hg (r z) q hz
  exact ⟨j, by rw [comb_pull a φ p c r z q hz]; exact hj.map _⟩

theorem Proport.pull {a : Fin mA → LB.Sec N} {b : Fin mB → LB.Sec H} {φ : X ⟶ A₀} {p : X ⟶ T} {Ψ : X ⟶ B₀}
    {c : Fin mA → Fin mB → Γ(T, ⊤)} (hp : Proport a b φ p Ψ c) (r : Z ⟶ X) :
    Proport a b (r ≫ φ) (r ≫ p) (r ≫ Ψ) c := by
  intro z q k hq hk j j'
  rw [comb_pull a φ p c r z q hq, comb_pull a φ p c r z q hq, gs_comp r Ψ z _ hk, gs_comp r Ψ z _ hk,
    ← map_mul, ← map_mul, hp (r z) q k hq hk j j']

theorem gs_top_comp {S : Scheme.{0}} (t : T ⟶ S) (z : T) (x : Γ(S, ⊤)) :
    (t.stalkMap z).hom (gs (𝟙 S) (t z) ⊤ x) = gs (𝟙 T) z ⊤ (t.appTop x) := by
  rw [← gs_comp t (𝟙 S) z ⊤ trivial, Category.comp_id]
  have e := gs_pull (𝟙 T) t z ⊤ trivial x
  rw [Category.id_comp] at e
  exact e.symm

theorem proport_zero {S : Scheme.{0}} {a : Fin mA → LB.Sec N} {b : Fin mB → LB.Sec H} {eA : S ⟶ A₀} {eB : S ⟶ B₀}
    {uA : ∀ z : S, N.ι → (S.presheaf.stalk z)ˣ} {uB : ∀ z : S, H.ι → (S.presheaf.stalk z)ˣ}
    {α : Fin mA → Γ(S, ⊤)} {β : Fin mB → Γ(S, ⊤)} (t : T ⟶ S) (c : Fin mA → Fin mB → Γ(T, ⊤))
    (ha : ∀ i, IsVal eA uA (a i) (α i)) (hb : ∀ j, IsVal eB uB (b j) (β j)) (hn : Normal t c α β) :
    Proport a b (t ≫ eA) (𝟙 T) (t ≫ eB) c := by
  intro z q k hq hk j j'
  have hc : ∀ j, comb a (t ≫ eA) (𝟙 T) c z q j =
      gs (𝟙 T) z ⊤ (t.appTop (β j)) * (t.stalkMap z).hom (uA (t z) q).val := by
    intro j
    simp only [comb]
    have e : ∀ i, gs (t ≫ eA) z (N.U q) ((a i).f q) =
        gs (𝟙 T) z ⊤ (t.appTop (α i)) * (t.stalkMap z).hom (uA (t z) q).val := by
      intro i
      rw [gs_comp t eA z _ hq, ha i (t z) q hq, map_mul, gs_top_comp]

    simp only [e, hn j, gs_eq (𝟙 T) z ⊤ trivial, map_sum, map_mul, Finset.sum_mul, _root_.mul_assoc]
  have hbj : ∀ j, gs (t ≫ eB) z (H.U k) ((b j).f k) =
      gs (𝟙 T) z ⊤ (t.appTop (β j)) * (t.stalkMap z).hom (uB (t z) k).val := by
    intro j
    rw [gs_comp t eB z _ hk, hb j (t z) k hk, map_mul, gs_top_comp]
  rw [hc, hc, hbj, hbj]
  ring

end GlobalTheory.HomFixUniv

namespace GlobalTheory.HomFixUniv

theorem snd_θ {Rg : Type} [CommRing Rg] (B : Over (Sp Rg)) : (snd (topS Rg) B).left ≫ θ B = 𝟙 _ := by
  have key : ∀ h : B ⟶ topS Rg, snd (topS Rg) B ≫ lift h (𝟙 B) = 𝟙 _ := by
    intro h
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, lift_fst, Category.id_comp]
      apply Over.OverMorphism.ext
      have : Mono (topS Rg).hom := by
        show Mono ((⊤ : (Sp Rg).Opens).ι ≫ 𝟙 _); infer_instance
      apply (cancel_mono (topS Rg).hom).1
      exact (Over.w _).trans (Over.w _).symm
    · rw [Category.assoc, lift_snd, Category.comp_id, Category.id_comp]
  rw [θ, ← Over.comp_left, key]
  rfl

theorem θ_comp_structure {Rg : Type} [CommRing Rg] (B : Over (Sp Rg)) : θ B ≫ fA B = B.hom := by
  rw [θ]; exact Over.w _

end GlobalTheory.HomFixUniv

theorem GlobalTheory.HomFixUniv.hom_of_proport : ∀ (Rg : Type) [CommRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left) (k mA mB : ℕ) (bA : Fin mA → LB.Sec (LPow A L (k : ℤ) (topS Rg))) (bB : Fin mB → LB.Sec (LPow B M (k : ℤ) (topS Rg))) (eA : LB.Gen (L.pull (eSec A))) (eB : LB.Gen (M.pull (eSec B))) (αA : Fin mA → Γ(Sp Rg, ⊤)) (βB : Fin mB → Γ(Sp Rg, ⊤)) (T : Scheme.{0}) (t : T ⟶ Sp Rg) (A' B' : Over T) [GrpObj A'] [GrpObj B'] (φA' : A'.left ⟶ A.left) (φB' : B'.left ⟶ B.left) (Ψ : A'.left ⟶ (topS Rg ⊗ B).left) (c : Fin mA → Fin mB → Γ(T, ⊤)), Hyps L M k bA bB eA eB → (∀ i, GlobalTheory.HomFixUniv.IsVal (eSec A ≫ GlobalTheory.HomFixUniv.θ A) (GlobalTheory.HomFixUniv.uFr A L k eA) (bA i) (αA i)) → (∀ j, GlobalTheory.HomFixUniv.IsVal (eSec B ≫ GlobalTheory.HomFixUniv.θ B) (GlobalTheory.HomFixUniv.uFr B M k eB) (bB j) (βB j)) → IsGrpPullback A' A t φA' → IsGrpPullback B' B t φB' → Ψ ≫ GlobalTheory.HomFixUniv.fA B = A'.hom ≫ t → GlobalTheory.HomFixUniv.Generates bA (φA' ≫ GlobalTheory.HomFixUniv.θ A) A'.hom c → GlobalTheory.HomFixUniv.Proport bA bB (φA' ≫ GlobalTheory.HomFixUniv.θ A) A'.hom Ψ c → GlobalTheory.HomFixUniv.Normal t c αA βB → ∃ Φ : A' ⟶ B', IsMonHom Φ ∧ Φ.left ≫ φB' ≫ GlobalTheory.HomFixUniv.θ B = Ψ := by
  intro Rg _ A B _ _ L M k mA mB bA bB eA eB αA βB T t A' B' _ _ φA' φB' Ψ c hH hvA hvB hA' hB' hΨ hgen hprop hnorm
  obtain ⟨hA, hB, hL, hM, -, -, -, hk, hva, -, hbB⟩ := hH
  have hA'ab : IsAbelianScheme A' := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA hA'
  have hB'ab : IsAbelianScheme B' := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hB hB'
  have hsnd : (snd (topS Rg) B).left ≫ B.hom = fA B := Over.w (snd (topS Rg) B)
  let Φl : A'.left ⟶ B'.left :=
    hB'.1.lift (Ψ ≫ (snd (topS Rg) B).left) A'.hom (by rw [Category.assoc, hsnd, hΨ])
  have hΦ1 : Φl ≫ φB' = Ψ ≫ (snd (topS Rg) B).left := hB'.1.lift_fst _ _ _
  have hΦ2 : Φl ≫ B'.hom = A'.hom := hB'.1.lift_snd _ _ _
  let Φ : A' ⟶ B' := Over.homMk Φl hΦ2
  have hΨΦ : Φ.left ≫ φB' ≫ θ B = Ψ := by
    show Φl ≫ φB' ≫ θ B = Ψ
    rw [← Category.assoc, hΦ1, Category.assoc, snd_θ, Category.comp_id]
  let e' : T ⟶ A'.left := η[A'].left
  have hEA : e' ≫ φA' = t ≫ eSec A := ReciprocityTheory.ChartRestriction.G.Out.PullGtPf.IsGrpPullback.one_left hA'
  have hEB : (η[B'].left : T ⟶ B'.left) ≫ φB' = t ≫ eSec B := ReciprocityTheory.ChartRestriction.G.Out.PullGtPf.IsGrpPullback.one_left hB'
  have hηA : e' ≫ A'.hom = 𝟙 T := Over.w η[A']
  have heB : eSec B ≫ B.hom = 𝟙 _ := Over.w η[B]
  have hzero : e' ≫ Ψ = t ≫ eSec B ≫ θ B := by
    have hgen' := hgen.pull e'
    have hprop' := hprop.pull e'
    rw [← Category.assoc, hEA, hηA, Category.assoc] at hgen' hprop'
    refine GlobalTheory.T.eq_of_pullbackSectionsProportionalToCombinations Rg _ _ T T (fA B) (LPow A L k (topS Rg)) (LPow B M k (topS Rg)) mA mB bA bB _ (𝟙 T) c _ _
      (GlobalTheory.T.sectionsEmbed_of_baseChangeStableBasis Rg B M k mB bB hB hM hk hva hbB) (LB.isLB_linComb hM _ _) (LB.isLB_linComb hL _ _) hgen' hprop'
      (proport_zero t c hvA hvB hnorm) ?_
    rw [Category.assoc, hΨ, ← Category.assoc, hηA, Category.id_comp, Category.assoc, Category.assoc, θ_comp_structure,
      heB]
    exact (Category.comp_id _).symm
  have hz : η[A'] ≫ Φ = η[B'] := by
    apply Over.OverMorphism.ext
    apply hB'.1.hom_ext
    · show e' ≫ Φl ≫ φB' = _
      rw [hΦ1, ← Category.assoc, hzero, hEB, Category.assoc, Category.assoc, θ_snd, Category.comp_id]
    · exact (Over.w _).trans (Over.w _).symm
  exact ⟨Φ, GlobalTheory.rigidity_holds T A' B' hA'ab hB'ab Φ hz, hΨΦ⟩
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

noncomputable section

namespace GlobalTheory.FormsLocus

theorem eval₂_expand {Rg S : Type} [CommRing Rg] [CommRing S] (mA mB : ℕ)
    (ψ : MvPolynomial (Fin (mA * mB)) Rg →+* S) (β : Fin mA → S) (F : MvPolynomial (Fin mB) Rg) :
    MvPolynomial.eval₂Hom (ψ.comp MvPolynomial.C)
        (fun j => ∑ i, ψ (MvPolynomial.X (finProdFinEquiv (i, j))) * β i) F =
      MvPolynomial.eval₂Hom ψ β (expand mA mB F) := by
  rw [expand, ← MvPolynomial.coe_eval₂Hom (MvPolynomial.C.comp MvPolynomial.C), ← RingHom.comp_apply,
    MvPolynomial.comp_eval₂Hom]
  congr 1
  ext r <;> simp

theorem expand_isHomogeneous {Rg : Type} [CommRing Rg] (mA mB : ℕ) {F : MvPolynomial (Fin mB) Rg} {d : ℕ}
    (hF : F.IsHomogeneous d) : (expand mA mB F).IsHomogeneous d := by
  have h := hF.eval₂ (τ := Fin mA)
    (MvPolynomial.C.comp MvPolynomial.C : Rg →+* MvPolynomial (Fin mA) (MvPolynomial (Fin (mA * mB)) Rg))
    (fun j => ∑ i : Fin mA, MvPolynomial.C (MvPolynomial.X (finProdFinEquiv (i, j))) * MvPolynomial.X i)
    (fun r => MvPolynomial.isHomogeneous_C _ _)
    (fun j => MvPolynomial.IsHomogeneous.sum _ _ _ fun i _ => MvPolynomial.isHomogeneous_C_mul_X _ _)
  simpa [expand] using h

theorem germ_eval_comb : ∀ (Rg : Type) [CommRing Rg] (A₀ T X : Scheme.{0}) (f : A₀ ⟶ Sp Rg) (N : LB A₀) (mA mB : ℕ) (a : Fin mA → LB.Sec N) (g : T ⟶ Sp (MvPolynomial (Fin (mA * mB)) Rg)) (φ : X ⟶ A₀) (p : X ⟶ T), φ ≫ f = p ≫ g ≫ affπ Rg (mA * mB) → ∀ (d : ℕ) (F : MvPolynomial (Fin mB) Rg), F.IsHomogeneous d → ∀ (z : X) (q : N.ι), φ z ∈ N.U q → MvPolynomial.eval₂Hom (gc (p ≫ g ≫ affπ Rg (mA * mB)) z) (comb a φ p (matOf g) z q) F = ∑ ν ∈ (GlobalTheory.FormsLocus.expand mA mB F).support, gs p z ⊤ (GlobalTheory.FormsLocus.ringOf g ((GlobalTheory.FormsLocus.expand mA mB F).coeff ν)) * gs φ z (N.U q) ((GlobalTheory.FormsLocus.monSec a d ν).f q) := by
  intro Rg _ A₀ T X f N mA mB a g φ p _ d F hF z q hq
  have hT : p z ∈ (⊤ : T.Opens) := trivial
  let ψ : MvPolynomial (Fin (mA * mB)) Rg →+* X.presheaf.stalk z :=
    (MapIff.gsH p z ⊤ hT).comp (ringOf g)
  have hC : ψ.comp MvPolynomial.C = gc (p ≫ g ≫ affπ Rg (mA * mB)) z := by
    ext r
    have n2 : (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin (mA * mB)) Rg))).inv (MvPolynomial.C r) =
        (affπ Rg (mA * mB)).appTop ((Scheme.ΓSpecIso (CommRingCat.of Rg)).inv r) := by
      rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality]; rfl
    simp only [ψ, RingHom.comp_apply, ringOf, gc, MapIff.gsH, RingHom.coe_comp, Function.comp_apply]
    rw [n2, Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop]
    rfl
  have hcomb : comb a φ p (matOf g) z q =
      fun j => ∑ i, ψ (MvPolynomial.X (finProdFinEquiv (i, j))) * gs φ z (N.U q) ((a i).f q) := by
    funext j
    simp only [comb, ψ, RingHom.comp_apply, ringOf_X, matOf]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [MapIff.gsH_apply]
  rw [← hC, hcomb, eval₂_expand, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_eq']
  refine Finset.sum_congr rfl fun ν hν => ?_
  have hd : ∑ i, ν i = d := by
    have := expand_isHomogeneous mA mB hF (MvPolynomial.mem_support_iff.1 hν)
    rw [← this, Finsupp.weight_apply]
    simp [Finsupp.sum_fintype]
  have hp : gs φ z (N.U q) (∏ i, (a i).f q ^ ν i) = ∏ i, gs φ z (N.U q) ((a i).f q) ^ ν i := by
    rw [← MapIff.gsH_apply φ z _ hq, map_prod]
    simp only [map_pow, MapIff.gsH_apply]
  simp only [ψ, RingHom.comp_apply, monSec, if_pos hd]
  rw [MapIff.gsH_apply]
  exact congrArg (fun x => gs p z ⊤ (ringOf g (AddMonoidAlgebra.coeff (expand mA mB F) ν)) * x) hp.symm

end GlobalTheory.FormsLocus
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct

namespace GlobalTheory.HTSummand

theorem exists_lagrangian_lift_lie : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (C : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] (I : Ideal C), I ^ 2 = ⊥ → ∀ (tR : R →+* C) (H : Type 1) [AddCommGroup H] [Module C H] [Module.Finite C H] [Module.Projective C H] (ρ : D.O →+* Module.End C H), (letI := GlobalTheory.HTSummand.tensorModOf (ρ.comp (algebraMap (𝓞 D.F) D.O)); Module.Projective (C ⊗[ℤ] 𝓞 D.F) H) → ∀ (φ : LinearMap.BilinForm C H), (∀ x y, φ x y = -φ y x) → Function.Bijective φ → (∀ (c : D.O) x y, φ (ρ c x) y = φ x (ρ (D.star c).unop y)) → ∀ (F : Submodule C H), I • ⊤ ≤ F → (∀ (c : D.O), ∀ x ∈ F, ρ c x ∈ F) → (∀ x ∈ F, ∀ y ∈ F, φ x y ∈ I) → (∀ x, (∀ y ∈ F, φ x y ∈ I) → x ∈ F) → (∃ E' M : Submodule C H, IsCompl E' M ∧ E' ⊔ I • ⊤ = F) → (∀ d, ρ (algebraMap (𝓞 D.F) D.O D.ω) d - tR b.ρ • d ∈ F → ∃ w : Fin D.a → H, (∀ i (c : 𝓞 D.F), ρ (algebraMap (𝓞 D.F) D.O c) (w i) - tR (b.t i c) • w i ∈ F) ∧ d - ∑ i, w i ∈ F) → ∃ E : Submodule C H, (∃ M : Submodule C H, IsCompl E M) ∧ E ⊔ I • ⊤ = F ∧ (∀ (c : D.O), ∀ x ∈ E, ρ c x ∈ E) ∧ (∀ x ∈ E, ∀ y ∈ E, φ x y = 0) ∧ ∀ d, ρ (algebraMap (𝓞 D.F) D.O D.ω) d - tR b.ρ • d ∈ E → ∃ w : Fin D.a → H, (∀ i (c : 𝓞 D.F), ρ (algebraMap (𝓞 D.F) D.O c) (w i) - tR (b.t i c) • w i ∈ E) ∧ d - ∑ i, w i ∈ E := by
  intro p _ D R _ b C _ _ _ I hI tR H _ _ _ _ ρ hproj φ hskew hbij hadj F hIF hFO hFiso hFlag hE' hLie
  obtain ⟨e, he, hρe, hφe, hωe, ⟨v, hv, hωk⟩, hestab⟩ := GlobalTheory.T.exists_idempotent_imaginaryQuadratic_eigen_crystal p D R b C tR H ρ φ hadj
  have hFe := hestab F hFO
  have hLie' : ∀ d ∈ LinearMap.range e, ∃ w : Fin D.a → H, (∀ i (c : 𝓞 D.F), ρ (algebraMap (𝓞 D.F) D.O c) (w i) - tR (b.t i c) • w i ∈ F) ∧ d - ∑ i, w i ∈ F := by
    rintro d ⟨y, rfl⟩
    exact hLie _ (by rw [hωe, sub_self]; exact F.zero_mem)
  have hcore : ∃ G M : Submodule C H, G ⊓ M = ⊥ ∧ G ⊔ M = LinearMap.range e ∧ (∀ (c : D.O), ∀ x ∈ G, ρ c x ∈ G) ∧ G ⊔ (I • ⊤ ⊓ LinearMap.range e) = F ⊓ LinearMap.range e ∧ ∀ d ∈ LinearMap.range e, ∃ w : Fin D.a → H, (∀ i (c : 𝓞 D.F), ρ (algebraMap (𝓞 D.F) D.O c) (w i) - tR (b.t i c) • w i ∈ G) ∧ d - ∑ i, w i ∈ G := by
    by_cases hp : IsUnit (p : C)
    · exact GlobalTheory.T.exists_liftSummand_lie_residueCharZero p D R b C I hI hp tR H ρ hproj e he hρe hωe F hIF hFO hFe hE' hLie'
    · exact GlobalTheory.T.exists_lieCondition_summand_residueCharP p D R b C I hI ((IsLocalRing.mem_maximalIdeal _).2 hp) tR H ρ hproj e he hρe hωe F hIF hFO hFe hE' hLie'
  obtain ⟨G, M, hGM, hGMr, hGO, hGF, hGLie⟩ := hcore
  obtain ⟨E, hEc, hEe, hEF, hEiso, hEO, hEst⟩ := GlobalTheory.T.lagrangianCompletion_sup_ideal_smul_eq C I H D.O ρ (fun a => (D.star a).unop) φ e he hρe hskew (fun a => D.star_star a) hadj hφe hbij F hIF hFiso hFlag hFe G M hGM hGMr hGO hGF
  refine ⟨E, hEc, hEF, hEO, hEiso, ?_⟩
  intro d hd
  have hGE : G ≤ E := hEe ▸ inf_le_left
  set k := d - e d with hkdef
  have hek : e k = 0 := by
    have := LinearMap.congr_fun he d
    simp only [Module.End.mul_apply] at this
    simp [hkdef, this]
  have hkE : k ∈ E := by
    set x := ρ (algebraMap (𝓞 D.F) D.O D.ω) d - tR b.ρ • d with hx
    have h1 : x - e x ∈ E := E.sub_mem hd (hEst _ hd)
    have h2 : x - e x = ρ (algebraMap (𝓞 D.F) D.O D.ω) k - tR b.ρ • k := by
      have hc := LinearMap.congr_fun (hρe (algebraMap (𝓞 D.F) D.O D.ω)) d
      simp only [Module.End.mul_apply] at hc
      simp only [hx, hkdef, map_sub, LinearMap.map_smul, smul_sub, hc]
      abel
    rw [h2, hωk k hek] at h1
    obtain ⟨u, rfl⟩ := hv
    have := E.smul_mem (↑u⁻¹ : C) h1
    rwa [smul_smul, Units.inv_mul, one_smul] at this
  obtain ⟨w, hw, hdw⟩ := hGLie (e d) ⟨d, rfl⟩
  refine ⟨w, fun i c => hGE (hw i c), ?_⟩
  have : d - ∑ i, w i = (e d - ∑ i, w i) + k := by rw [hkdef]; abel
  rw [this]
  exact E.add_mem (hGE hdw) hkE

end GlobalTheory.HTSummand
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PureLift
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.inertia_fixes_complex_fibre_pure_endomorphism_torsion : GlobalTheory.Published.FormalAlgebraisation → GlobalTheory.Published.GrothendieckMessing → ∀ (N : IntermediateField ℚ ℂ) [NumberField N] (P : Out.PolAV (Sp (𝓞 N))) (W : P.A ⟶ P.A) [IsMonHom W] (r s : 𝓞 N), IsPureBC P.A W r s → ∀ q : ℕ, q.Prime → ∀ 𝔮 : Ideal (𝓞 N), 𝔮.IsMaximal → (q : 𝓞 N) ∈ 𝔮 → r - s ∉ 𝔮 → ∀ τ : ℂ ≃+* ℂ, (∀ x : 𝓞 N, ∃ y : 𝓞 N, ((y : N) : ℂ) = τ ((x : N) : ℂ) ∧ y - x ∈ 𝔮) → ∀ (A : Over (Sp ℂ)) [GrpObj A] (ψ : A.left ⟶ P.A.left), IsGrpPullback A P.A (spMap ((algebraMap N ℂ).comp (algebraMap (𝓞 N) N))) ψ → ∃ io : A.left ⟶ A.left, IsGrpPullback A A (spMap (τ : ℂ →+* ℂ)) io ∧ ∀ n : ℕ, ¬ q ∣ n → ∀ y : Over.mk (𝟙 (Sp (𝓞 N))) ⟶ P.A, y ^ n = 1 → ∀ x : Sp ℂ ⟶ A.left, x ≫ A.hom = 𝟙 _ → x ≫ ψ = spMap ((algebraMap N ℂ).comp (algebraMap (𝓞 N) N)) ≫ y.left → x ≫ io = spMap (τ : ℂ →+* ℂ) ≫ x := by
  first | exact @GlobalTheory.InertiaTransfer.exists_isGrpPullback_of_inertia | exact GlobalTheory.InertiaTransfer.exists_isGrpPullback_of_inertia | (intros; apply GlobalTheory.InertiaTransfer.exists_isGrpPullback_of_inertia <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.Obs GlobalTheory.LBLift
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.additiveClassDegreeTwo_vanish_affineBases_alt : PrimitiveExtendedDegTwoVanish → ∀ (R R₁ : Type) [CommRing R] [CommRing R₁] [Algebra R R₁] (q : R₁ →ₐ[R] R), (∀ y y', q y = 0 → q y' = 0 → y * y' = 0) → ∀ (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (D T : Type) [Category.{0} D] [Category.{0} T] [Quiver.IsThin D] [Quiver.IsThin T] (G : D ⥤ AffOp A.left) (H : T ⥤ AffOp (A ⊗ A).left) (K₀ K₁ K₂ : T ⥤ D) (le₀ : ∀ t, (H.obj t).unop.1 ≤ (μ[A]).left ⁻¹ᵁ (G.obj (K₀.obj t)).unop.1) (le₁ : ∀ t, (H.obj t).unop.1 ≤ (fst A A).left ⁻¹ᵁ (G.obj (K₁.obj t)).unop.1) (le₂ : ∀ t, (H.obj t).unop.1 ≤ (snd A A).left ⁻¹ᵁ (G.obj (K₂.obj t)).unop.1), IsBasis G → IsBasis H → ∀ c : GlobalTheory.CatCoh.H2 (GlobalTheory.Obs.ext R₁ (G ⋙ OAff A.hom)), (extMap R₁ (pullMap (overW μ[A]) G H K₀ le₀)).pull2 c = (extMap R₁ (pullMap (overW (fst A A)) G H K₁ le₁)).pull2 c + (extMap R₁ (pullMap (overW (snd A A)) G H K₂ le₂)).pull2 c → c = 0 := by
  first | exact @GlobalTheory.Obs.additiveClassDegreeTwo_vanish_affineBases | exact GlobalTheory.Obs.additiveClassDegreeTwo_vanish_affineBases | (intros; apply GlobalTheory.Obs.additiveClassDegreeTwo_vanish_affineBases <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.Obs GlobalTheory.LBLift
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.flat_coefficient_extension_H2_class : ∀ (R : Type) [CommRing R] (I : Ideal R), ∃ (R₁ : Type) (_ : CommRing R₁) (_ : Algebra R R₁) (q : R₁ →ₐ[R] R), (∀ y y', q y = 0 → q y' = 0 → y * y' = 0) ∧ ∀ (D T : Type) [Category.{0} D] [Category.{0} T] (F : D ⥤ CommAlgCat.{0} R) (F' : T ⥤ CommAlgCat.{0} R) (n₀ n₁ n₂ : CoefMap (RingHom.id R) F F'), (∀ t, Module.Flat R (F.obj t)) → (∀ t, Module.Flat R (F'.obj t)) → (∀ c : GlobalTheory.CatCoh.H2 (GlobalTheory.Obs.ext R₁ F), (extMap R₁ n₀).pull2 c = (extMap R₁ n₁).pull2 c + (extMap R₁ n₂).pull2 c → c = 0) → PrimI I n₀ n₁ n₂ := by
  first | exact @GlobalTheory.PrimIdeal.primI_of_ext | exact GlobalTheory.PrimIdeal.primI_of_ext | (intros; apply GlobalTheory.PrimIdeal.primI_of_ext <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.GenericMember
open GlobalTheory.ThickeningDetermines (secIdeal)
open scoped TensorProduct

theorem _root_.GlobalTheory.T.genericMemberSection_ne_zero_isPrime_affineChart : ∀ (k : Type) [Field k] (N : ℕ) (X X' : Scheme.{0}) [IsIntegral X] (f : X ⟶ Sp k) (f' : X' ⟶ Sp (FractionRing (MvPolynomial (Fin N) k))) (π : X' ⟶ X) (L : LB X) (hL : L.IsLB) (b : Fin N → L.Sec) (V : X.Opens) (hne : (V : Set X).Nonempty) (hW : IsAffineOpen (π ⁻¹ᵁ V)) (c : L.ι) (hVc : V ≤ L.U c) (j : Fin N), IsUnit (resG X hVc ((b j).f c)) → letI : Algebra k Γ(X, V) := ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appLE ⊤ V le_top).hom.toAlgebra; ∀ e : FractionRing (MvPolynomial (Fin N) k) ⊗[k] Γ(X, V) ≃+* Γ(X', π ⁻¹ᵁ V), (∀ a, e (1 ⊗ₜ a) = (π.app V).hom a) → (∀ q, e (q ⊗ₜ 1) = ((Scheme.ΓSpecIso _).inv ≫ f'.appLE ⊤ (π ⁻¹ᵁ V) le_top).hom q) → (genSec k N f' π L b).f (fun _ => c) ≠ 0 ∧ ((secIdeal (LB.isLB_pull hL π) (genSec k N f' π L b)).ideal ⟨π ⁻¹ᵁ V, hW⟩ = ⊤ ∨ ((secIdeal (LB.isLB_pull hL π) (genSec k N f' π L b)).ideal ⟨π ⁻¹ᵁ V, hW⟩).IsPrime ∧ ((secIdeal (LB.isLB_pull hL π) (genSec k N f' π L b)).ideal ⟨π ⁻¹ᵁ V, hW⟩).comap (π.app V).hom = ⊥) := by
  first | exact @GlobalTheory.GenericMember.genSec_chart_ne_zero_and_isPrime | exact GlobalTheory.GenericMember.genSec_chart_ne_zero_and_isPrime | (intros; apply GlobalTheory.GenericMember.genSec_chart_ne_zero_and_isPrime <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.AbDual
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_closed_pow_transition_of_frobenius_kills_class : ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (hR : (p : R) = 0) (X : Scheme.{0}) (s : X ⟶ Sp R) (hX : (p : Γ(X, ⊤)) = 0) (h : IsMor (dp0 R) s (dp0 R) s (frobR p R hR) (GlobalTheory.VB.frob X p hX)) (f : Z1 (O (dp0 R) s)), h.pull1 (GlobalTheory.CatCoh.H1.mk _ f) = 0 → ∃ u : ∀ U : GlobalTheory.CechDR.AffOp X, GlobalTheory.CechDR.Sec s U.unop.1, (∀ U, KaehlerDifferential.D R (GlobalTheory.CechDR.Sec s U.unop.1) (u U) = 0) ∧ ∀ (U V : GlobalTheory.CechDR.AffOp X) (a : U ⟶ V), (show GlobalTheory.CechDR.Sec s V.unop.1 from (GlobalTheory.CechDR.cmpZZ s f).1.1 U V a) ^ p = u V - GlobalTheory.CechDR.Sec.res s (leOfHom a.unop) (u U) := by
  first | exact @GlobalTheory.CechDR.FrobKill.exists_closed_pow | exact GlobalTheory.CechDR.FrobKill.exists_closed_pow | (intros; apply GlobalTheory.CechDR.FrobKill.exists_closed_pow <;> assumption)
end
