module

public import Development.EtaleCohomology.TateTwists.Bundle007
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Development.EtaleCohomology.TateTwists.Bundle008
public import Development.EtaleCohomology.TateTwists.Bundle004
public import Development.EtaleCohomology.TateTwists.Bundle006
public import Development.EtaleCohomology.TateTwists.Bundle005
public import Development.EtaleCohomology.TateTwists.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.CategoryTheory.Abelian.Injective.Ext
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
import Mathlib.Tactic.TypeStar

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def L_kumT_ex : Prop := ∀ (q : ℕ) [NeZero q], IsKum q (kumT q)

def L_prim_loc : Prop := ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}), (IsUnit (q : Γ(U, ⊤)) → Loc U fun V _ => Nonempty (Prim q Γ(V, ⊤))) ∧ (∀ ζ ξ : Prim q Γ(U, ⊤), Loc U fun _ g => ∃ a : (ZMod q)ˣ, g.appTop.hom ξ.1 = g.appTop.hom ζ.1 ^ (a : ZMod q).val) ∧ (∀ (ζ : Prim q Γ(U, ⊤)) (x : Γ(U, ⊤)), x ^ q = 1 → Loc U fun _ g => ∃ a : ℕ, g.appTop.hom x = g.appTop.hom ζ.1 ^ a) ∧ (IsUnit (q : Γ(U, ⊤)) → ∀ u : (Γ(U, ⊤))ˣ, Loc U fun V g => ∃ v : (Γ(V, ⊤))ˣ, v ^ q = Units.map g.appTop.hom.toMonoidHom u)

def L_sec_glue : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) (U : Scheme.{0}), (∀ a b : Sec F U, (Loc U fun _ g => Sec.res g a = Sec.res g b) → a = b) ∧ ∀ (S : Sieve U), S ∈ Scheme.etaleTopology U → ∀ s : ∀ (V : Scheme.{0}) (g : V ⟶ U), S.arrows g → Sec F V, (∀ (V W : Scheme.{0}) (g : V ⟶ U) (k : W ⟶ V) (hg : S.arrows g), Sec.res k (s V g hg) = s W (k ≫ g) (S.downward_closed hg k)) → ∃ a : Sec F U, ∀ V g hg, Sec.res g a = s V g hg

def L_sch_cls : Prop := ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (I : Cx R) (m n k : ℤ), m + 1 = n → n + 1 = k → (∀ z : Sec (I.X n) X, Sec.map (I.d n k) z = 0 → ∃ α : Cocycle ((chains R).obj (sch.obj X)) I n, (∀ (U : Scheme.{0}) (x : U ⟶ X), ev α.1 0 n (by simp) U x = Sec.res x z) ∧ ∀ (p : ℕ) s h U x, ev α.1 (p + 1) s h U x = 0) ∧ ∀ α : Cocycle ((chains R).obj (sch.obj X)) I n, Sec.map (I.d n k) (ev α.1 0 n (by simp) X (𝟙 X)) = 0 ∧ (CohomologyClass.mk α = 0 ↔ ∃ y : Sec (I.X m) X, Sec.map (I.d m n) y = ev α.1 0 n (by simp) X (𝟙 X))

def L_res_sec : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) (U : Scheme.{0}), (∀ z : Sec ((res R F).X 0) U, Sec.map ((res R F).d 0 1) z = 0 ↔ ∃ a : Sec F U, Sec.map (resι R F) a = z) ∧ Function.Injective (Sec.map (resι R F) (U := U)) ∧ (∀ (m n k : ℤ), 0 < n → m + 1 = n → ∀ z : Sec ((res R F).X n) U, n + 1 = k → Sec.map ((res R F).d n k) z = 0 → Loc U fun V g => ∃ y : Sec ((res R F).X m) V, Sec.map ((res R F).d m n) y = Sec.res g z) ∧ ∀ n : ℤ, n < 0 → Subsingleton (Sec ((res R F).X n) U)

section Basic
variable {R : Type} [CommRing R]

theorem sec_res_map {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.map φ x) = Sec.map φ (Sec.res g x) :=
  (ConcreteCategory.congr_hom (φ.hom.naturality g.op) x).symm

theorem sec_res_comp {F : Shv R} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (x : Sec F U) :
    Sec.res (k ≫ g) x = Sec.res k (Sec.res g x) := by
  show (F.obj.map (k ≫ g).op).hom x = (F.obj.map k.op).hom ((F.obj.map g.op).hom x)
  rw [op_comp, Functor.map_comp]
  rfl

theorem sec_res_zero {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) : Sec.res g (0 : Sec F U) = 0 := map_zero _

theorem sec_map_comp {F G H : Shv R} (φ : F ⟶ G) (ψ : G ⟶ H) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (φ ≫ ψ) x = Sec.map ψ (Sec.map φ x) := rfl

theorem sec_map_add {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (x y : Sec F U) :
    Sec.map φ (x + y) = Sec.map φ x + Sec.map φ y := LinearMap.map_add _ _ _

theorem sec_map_zero {F G : Shv R} {U : Scheme.{0}} (x : Sec F U) : Sec.map (0 : F ⟶ G) x = 0 := by
  simp [Sec.map]

end Basic

theorem prim_pow {q : ℕ} {A : Type} [CommRing A] (ζ : Prim q A) : ζ.1 ^ q = 1 := by
  obtain ⟨p, hp⟩ := Polynomial.cyclotomic.dvd_X_pow_sub_one q ℤ
  have h := congrArg (Polynomial.aeval ζ.1) hp
  simp only [map_sub, map_pow, Polynomial.aeval_X, map_one, map_mul, ζ.2.2, zero_mul] at h
  exact sub_eq_zero.mp h

theorem prim_isUnit {q : ℕ} [NeZero q] {A : Type} [CommRing A] (ζ : Prim q A) : IsUnit ζ.1 :=
  IsUnit.of_pow_eq_one (prim_pow ζ) (NeZero.ne q)

theorem units_root {q : ℕ} {X U V : Scheme.{0}} (u : (Γ(X, ⊤))ˣ) (x : U ⟶ X) (g : V ⟶ U) (w : (Γ(U, ⊤))ˣ)
    (h : w ^ q = Units.map x.appTop.hom.toMonoidHom u) :
    (Units.map g.appTop.hom.toMonoidHom w) ^ q = Units.map (g ≫ x).appTop.hom.toMonoidHom u := by
  rw [← map_pow, h]
  ext
  simp
  rfl

section Kum
variable (q : ℕ) [NeZero q]

theorem d_resGen (hR : L_res_sec) {U : Scheme.{0}} (ζ : Prim q Γ(U, ⊤)) :
    Sec.map ((res (ZMod q) (tw q 1)).d 0 1) (resGen 1 ζ) = 0 :=
  ((hR (ZMod q) (tw q 1) U).1 _).2 ⟨twGen 1 ζ, rfl⟩

theorem dt_pow (hK : L_kumT_ex) (hR : L_res_sec) {U : Scheme.{0}} (ζ : Prim q Γ(U, ⊤)) (a : ℕ) :
    ∀ v w : (Γ(U, ⊤))ˣ, (w : Γ(U, ⊤)) = ζ.1 ^ a * v →
      Sec.map ((res (ZMod q) (tw q 1)).d 0 1) (kumT q U w) = Sec.map ((res (ZMod q) (tw q 1)).d 0 1) (kumT q U v) := by
  induction a with
  | zero =>
    intro v w h
    have : w = v := Units.ext (by simpa using h)
    subst this; rfl
  | succ a ih =>
    intro v w h
    let m : (Γ(U, ⊤))ˣ := (prim_isUnit ζ).unit ^ a * v
    have hm : (m : Γ(U, ⊤)) = ζ.1 ^ a * v := by simp [m]
    have hw : (w : Γ(U, ⊤)) = ζ.1 * m := by rw [h, hm, pow_succ]; ring
    rw [(hK q).2 U ζ m w hw, sec_map_add, d_resGen q hR, add_zero]
    exact ih v m hm

theorem dt_root (hK : L_kumT_ex) (hP : L_prim_loc) (hG : L_sec_glue) (hR : L_res_sec) {W : Scheme.{0}}
    (hqW : IsUnit (q : Γ(W, ⊤))) (w1 w2 : (Γ(W, ⊤))ˣ) (h : w1 ^ q = w2 ^ q) :
    Sec.map ((res (ZMod q) (tw q 1)).d 0 1) (kumT q W w1) = Sec.map ((res (ZMod q) (tw q 1)).d 0 1) (kumT q W w2) := by
  let ρ : (Γ(W, ⊤))ˣ := w2 * w1⁻¹
  have hρ : ρ ^ q = 1 := by
    simp only [ρ]; rw [mul_pow, inv_pow, ← h, mul_inv_cancel]
  apply (hG (ZMod q) _ W).1
  obtain ⟨S, hS, hPS⟩ := (hP q W).1 hqW
  refine ⟨S, hS, fun V g hg => ?_⟩
  obtain ⟨ζ⟩ := hPS V g hg
  have hqV : IsUnit (q : Γ(V, ⊤)) := by simpa using hqW.map g.appTop.hom
  have hr : (g.appTop.hom (ρ : Γ(W, ⊤))) ^ q = 1 := by
    rw [← map_pow, ← Units.val_pow_eq_pow_val, hρ, Units.val_one, map_one]
  rw [sec_res_map, sec_res_map, (hK q).1 V W g w1 hqW, (hK q).1 V W g w2 hqW]
  apply (hG (ZMod q) _ V).1
  obtain ⟨T, hT, hPT⟩ := (hP q V).2.2.1 ζ _ hr
  refine ⟨T, hT, fun V' k hk => ?_⟩
  dsimp only
  obtain ⟨a, ha⟩ := hPT V' k hk
  rw [sec_res_map, sec_res_map, (hK q).1 V' V k _ hqV, (hK q).1 V' V k _ hqV]
  symm
  apply dt_pow q hK hR (Prim.map k.appTop.hom ζ) a
  have e : (w2 : Γ(W, ⊤)) = (ρ : Γ(W, ⊤)) * w1 := by simp [ρ]
  change k.appTop.hom (g.appTop.hom (w2 : Γ(W, ⊤))) = (k.appTop.hom ζ.1) ^ a * k.appTop.hom (g.appTop.hom (w1 : Γ(W, ⊤)))
  rw [e, map_mul, map_mul, ha]

end Kum

theorem kum_exists_of (hK : L_kumT_ex) (hP : L_prim_loc) (hG : L_sec_glue) (hC : L_sch_cls) (hR : L_res_sec) :
    kum_exists := by
  intro q _ X u hq
  have hqU : ∀ {U : Scheme.{0}} (x : U ⟶ X), IsUnit (q : Γ(U, ⊤)) := fun x => by simpa using hq.map x.appTop.hom
  have key : ∀ {U : Scheme.{0}} (x : U ⟶ X) (w1 w2 : (Γ(U, ⊤))ˣ), w1 ^ q = Units.map x.appTop.hom.toMonoidHom u →
      w2 ^ q = Units.map x.appTop.hom.toMonoidHom u →
      Sec.map ((res (ZMod q) (tw q 1)).d 0 1) (kumT q U w1) = Sec.map ((res (ZMod q) (tw q 1)).d 0 1) (kumT q U w2) :=
    fun x w1 w2 h1 h2 => dt_root q hK hP hG hR (hqU x) w1 w2 (h1.trans h2.symm)
  obtain ⟨S, hS, hroot⟩ := (hP q X).2.2.2 hq u
  choose v hv using hroot
  obtain ⟨z, hz⟩ := (hG (ZMod q) ((res (ZMod q) (tw q 1)).X 1) X).2 S hS
    (fun V g hg => Sec.map ((res (ZMod q) (tw q 1)).d 0 1) (kumT q V (v V g hg))) (by
      intro V W g k hg
      rw [sec_res_map, (hK q).1 W V k _ (hqU g)]
      exact key (k ≫ g) _ _ (units_root u g k _ (hv V g hg)) (hv W (k ≫ g) _))
  have hdz : Sec.map ((res (ZMod q) (tw q 1)).d 1 2) z = 0 := by
    apply (hG (ZMod q) _ X).1
    refine ⟨S, hS, fun V g hg => ?_⟩
    dsimp only
    rw [sec_res_map, hz V g hg, sec_res_zero, ← sec_map_comp, HomologicalComplex.d_comp_d, sec_map_zero]
  obtain ⟨α, hα0, hα1⟩ := (hC (ZMod q) X (res (ZMod q) (tw q 1)) 0 1 2 (by norm_num) (by norm_num)).1 z hdz
  refine ⟨α, fun U x => hα1 0 0 _ U x, fun U x w hw => ?_⟩
  rw [hα0 U x]
  apply (hG (ZMod q) _ U).1
  refine ⟨S.pullback x, (Scheme.etaleTopology).pullback_stable x hS, fun V g hg => ?_⟩
  dsimp only
  rw [← sec_res_comp, hz V (g ≫ x) hg, sec_res_map, (hK q).1 V U g w (hqU x)]
  exact key (g ≫ x) _ _ (hv V (g ≫ x) hg) (units_root u x g w hw)

end LateralTheory.EtaleFoundations
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

lemma aw_diag {M : Type*} [AddCommMonoid M] (N : ℕ) (Φ : ℕ → ℕ → M) :
    ∑ q ∈ Finset.range (N + 1), ∑ p ∈ Finset.range (q + 1), Φ p (q - p) =
      ∑ p ∈ Finset.range (N + 1), ∑ r ∈ Finset.range (N - p + 1), Φ p r := by
  rw [Finset.sum_range_diag_flip]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.mem_range] at hp
  rw [show N + 1 - p = N - p + 1 by omega]

lemma bil_zsmul_left {S A B C : Type*} [CommRing S] [AddCommGroup A] [Module S A] [AddCommGroup B] [Module S B]
    [AddCommGroup C] [Module S C] (f : A →ₗ[S] B →ₗ[S] C) (c : ℤ) (a : A) (b : B) :
    f (c • a) b = c • f a b := by
  have := map_zsmul (f.flip b) c a
  simpa using this

lemma bil_sum_left {S A B C ι : Type*} [CommRing S] [AddCommGroup A] [Module S A] [AddCommGroup B] [Module S B]
    [AddCommGroup C] [Module S C] (f : A →ₗ[S] B →ₗ[S] C) (s : Finset ι) (a : ι → A) (b : B) :
    f (∑ i ∈ s, a i) b = ∑ i ∈ s, f (a i) b := by
  have := map_sum (f.flip b) a s
  simpa using this

variable {R : Type} [CommRing R]

lemma mul_ev_right {A B C : Cx R} (P : Pair A B C) {E : Spc} {N : ℕ} {U : Scheme.{0}} (x : Sx E N U) {s k w : ℤ}
    (a : Sec (A.X s) U) (γ : Cochain ((chains R).obj E) B k) (t t' j j' : ℕ) (ht : t = t') (hj : j = j')
    (h : s + (-(t : ℤ) + k) = w) (h' : s + (-(t' : ℤ) + k) = w) (hl : j + t ≤ N) (hl' : j' + t' ≤ N) :
    P.mul U s (-(t : ℤ) + k) w h a (ev γ t _ rfl U (x.sub j t hl)) =
      P.mul U s (-(t' : ℤ) + k) w h' a (ev γ t' _ rfl U (x.sub j' t' hl')) := by
  subst ht hj; rfl

theorem t_aw_assoc0_of (hev : EtaleCochainEvaluationLinear) (hsub : EtaleSimplexSubfaceComposition) : t_aw_assoc0 := by
  intro R _ I J K M M' L μ ν μ' ν' hass E n m k nm mk w h1 h2 h3 h4 α β γ ab bc x y hab hx hbc hy
  refine (hev R).2.2.1 x y fun N s hs U z => ?_
  rw [hx N s hs U z, hy N s hs U z]
  let Φ : ℕ → ℕ → Sec (L.X s) U := fun p r => if h : p + r ≤ N then
    (((m * (p : ℤ) + k * ((p : ℤ) + r)).negOnePow : ℤˣ) : ℤ) •
      ν'.mul U (-(p : ℤ) + n) (-((N - p : ℕ) : ℤ) + mk) s (by omega) (ev α p _ rfl U (z.sub 0 p (by omega)))
        (μ'.mul U (-(r : ℤ) + m) (-((N - p - r : ℕ) : ℤ) + k) (-((N - p : ℕ) : ℤ) + mk) (by omega)
          (ev β r _ rfl U (z.sub p r (by omega))) (ev γ (N - p - r) _ rfl U (z.sub (p + r) (N - p - r) (by omega))))
    else 0
  have hsg : ∀ a b c : ℤ, a + b = c → ((a.negOnePow : ℤˣ) : ℤ) * ((b.negOnePow : ℤˣ) : ℤ) = ((c.negOnePow : ℤˣ) : ℤ) := by
    intro a b c h; rw [← Units.val_mul, ← Int.negOnePow_add, h]
  calc _ = ∑ q : Fin (N + 1), ∑ p : Fin ((q : ℕ) + 1), Φ p ((q : ℕ) - p) := by
          refine Finset.sum_congr rfl fun q _ => ?_
          rw [hab, bil_sum_left, Finset.smul_sum]
          refine Finset.sum_congr rfl fun p _ => ?_
          have hp := p.is_lt
          have hq := q.is_lt
          simp only [Φ]
          rw [dite_eq_left (by omega), Units.smul_def, Units.smul_def, bil_zsmul_left, smul_smul,
            hsg _ _ (m * ((p : ℕ) : ℤ) + k * (((p : ℕ) : ℤ) + (((q : ℕ) - (p : ℕ) : ℕ) : ℤ)))
              (by push_cast [Nat.cast_sub (show (p : ℕ) ≤ q by omega)]; ring)]
          congr 1
          rw [hass U _ _ _ _ (-((N - p : ℕ) : ℤ) + mk) s _ _ (by omega) (by omega)]
          rw [(hsub z).1 0 q 0 p, (hsub z).1 0 q p (q - p)]
          simp only [Nat.zero_add]
          congr 1
          exact mul_ev_right _ z _ γ (N - q) (N - p - (q - p)) q (p + (q - p)) (by omega) (by omega) _ _ _ _
    _ = ∑ q ∈ Finset.range (N + 1), ∑ p ∈ Finset.range (q + 1), Φ p (q - p) := by
          rw [← Fin.sum_univ_eq_sum_range (fun q => ∑ p ∈ Finset.range (q + 1), Φ p (q - p))]
          exact Finset.sum_congr rfl fun q _ => Fin.sum_univ_eq_sum_range (fun p => Φ p (q - p)) _
    _ = ∑ p ∈ Finset.range (N + 1), ∑ r ∈ Finset.range (N - p + 1), Φ p r := aw_diag N Φ
    _ = ∑ p : Fin (N + 1), ∑ r : Fin (N - (p : ℕ) + 1), Φ p r := by
          rw [← Fin.sum_univ_eq_sum_range (fun p => ∑ r ∈ Finset.range (N - p + 1), Φ p r)]
          exact Finset.sum_congr rfl fun p _ => (Fin.sum_univ_eq_sum_range (fun r => Φ p r) _).symm
    _ = _ := by
          refine Finset.sum_congr rfl fun p _ => ?_

          rw [hbc, map_sum, Finset.smul_sum]
          refine Finset.sum_congr rfl fun r _ => ?_
          have hp := p.is_lt
          have hr := r.is_lt
          simp only [Φ]
          rw [dite_eq_left (by omega), Units.smul_def, Units.smul_def, map_zsmul, smul_smul,
            hsg _ _ (m * ((p : ℕ) : ℤ) + k * (((p : ℕ) : ℤ) + ((r : ℕ) : ℤ))) (by subst h3; ring)]
          rw [(hsub z).1 p (N - p) 0 r, (hsub z).1 p (N - p) r (N - p - r)]
          simp only [Nat.add_zero]

end LateralTheory.EtaleFoundations
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

lemma restr_ex_hom_ext_of_qis {C : Type*} [Category C] [Abelian C] {K K' L : CochainComplex C ℤ}
    [L.IsKInjective] (s : K ⟶ K') [QuasiIso s] (f : K ⟶ L) :
    ∃ g : K' ⟶ L, Nonempty (Homotopy (s ≫ g) f) := by
  have hL := CochainComplex.IsKInjective.rightOrthogonal L
  rw [← ObjectProperty.isLocal_trW] at hL
  have hs : (HomotopyCategory.subcategoryAcyclic C).trW ((HomotopyCategory.quotient C _).map s) := by
    rw [← HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic, HomotopyCategory.quotient_map_mem_quasiIso_iff]
    exact (HomologicalComplex.mem_quasiIso_iff _).2 inferInstance
  obtain ⟨g', hg'⟩ := (hL _ hs).2 ((HomotopyCategory.quotient C _).map f)
  obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient C _).map_surjective g'
  refine ⟨g, ⟨HomotopyCategory.homotopyOfEq _ _ ?_⟩⟩
  simpa using hg'

def EtaleSheafRestrictScalarsFunctorExact : Prop :=
  ∀ (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S),
    PreservesFiniteLimits (restr φ) ∧ PreservesFiniteColimits (restr φ)

theorem etaleSheaf_restrictScalars_resolution_hom_exists_of_exact (hE : EtaleSheafRestrictScalarsFunctorExact) : EtaleSheafRestrictScalarsInjectiveResolutionHomExists := by
  intro R S _ _ φ F
  obtain ⟨h1, h2⟩ := hE R S φ
  let G := restr φ
  have : G.Additive := G.additive_of_preserves_binary_products
  let IS := injectiveResolution F
  let IR := injectiveResolution (G.obj F)
  have : (res R (G.obj F)).IsKInjective := inferInstanceAs IR.cochainComplex.IsKInjective
  have : (res R (G.obj F)).IsStrictlyGE 0 := inferInstanceAs (IR.cochainComplex.IsStrictlyGE 0)
  let s := (G.mapHomologicalComplex (ComplexShape.up ℤ)).map IS.ι'
  have : QuasiIso s := inferInstance
  let f0 := (HomologicalComplex.singleMapHomologicalComplex G (ComplexShape.up ℤ) 0).hom.app F ≫ IR.ι'
  obtain ⟨g, ⟨h⟩⟩ := restr_ex_hom_ext_of_qis (L := res R (G.obj F)) s f0
  refine ⟨fun n => g.f n, fun i j => (g.comm i j).symm, ?_⟩
  have hz1 : IsZero (((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj F)).X 1) :=
    G.map_isZero (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 F 1 (by decide))
  have key : (s ≫ g).f 0 = f0.f 0 := by
    rw [h.comm 0]
    have e1 : dNext 0 h.hom = 0 := by
      have e : h.hom 1 0 = 0 := hz1.eq_of_src _ _
      rw [dNext_eq h.hom (show (ComplexShape.up ℤ).Rel 0 1 from rfl), e, comp_zero]
    have e2 : prevD 0 h.hom = 0 := by
      rw [prevD_eq h.hom (show (ComplexShape.up ℤ).Rel (-1) 0 from rfl),
        ((res R (G.obj F)).isZero_of_isStrictlyGE 0 (-1) (by decide)).eq_of_tgt (h.hom 0 (-1)) 0, zero_comp]
    rw [e1, e2, zero_add, zero_add]
  have key2 := congrArg (fun x => G.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).inv ≫ x) key
  simp only [s, f0, HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    HomologicalComplex.singleMapHomologicalComplex_hom_app_self, ← Category.assoc, ← Functor.map_comp,
    Iso.inv_hom_id, Functor.map_id, Category.id_comp] at key2
  have key3 : G.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).inv ≫ G.map (IS.ι'.f 0) ≫ g.f 0 =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (G.obj F)).inv ≫ IR.ι'.f 0 := by
    refine key2.trans ?_
    have c2 : ((HomologicalComplex.singleMapHomologicalComplex G (ComplexShape.up ℤ) 0).hom.app F).f 0 =
        G.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).hom ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (G.obj F)).inv :=
      HomologicalComplex.singleMapHomologicalComplex_hom_app_self _ _ _ _
    calc _ = G.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).inv ≫ ((G.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).hom ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (G.obj F)).inv) ≫ IR.ι'.f 0) := by
          exact congrArg (fun x => G.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).inv ≫ x) (congrArg (fun y => y ≫ IR.ι'.f 0) c2)
      _ = _ := by
          have aux : ∀ {A B : Shv S} {Y Z : Shv R} (e : A ≅ B) (u : G.obj B ⟶ Y) (v : Y ⟶ Z),
              G.map e.inv ≫ (G.map e.hom ≫ u) ≫ v = u ≫ v := by
            intro A B Y Z e u v
            rw [← Category.assoc, ← Category.assoc, ← G.map_comp, Iso.inv_hom_id, G.map_id, Category.id_comp]
          exact aux _ _ _
  simp only [resι]
  erw [Functor.map_comp, Category.assoc]
  exact key3

end LateralTheory.EtaleFoundations
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def EvDelta : Prop := ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n m : ℤ}
  (hm : n + 1 = m) (α : Cochain ((chains R).obj E) I n) (U : Scheme.{0}),
  (∀ (x : Sx E 0 U), ev (R := R) (δ n m α) 0 m (by simp) U x =
    Sec.map (I.d n m) (ev (R := R) α 0 n (by simp) U x)) ∧
  ∀ (p : ℕ) (s t : ℤ) (hs : -((p + 1 : ℕ) : ℤ) + n = s)
    (ht : -((p + 1 : ℕ) : ℤ) + m = t) (x : Sx E (p + 1) U),
    ev (R := R) (δ n m α) (p + 1) t ht U x =
      Sec.map (I.d s t) (ev (R := R) α (p + 1) s hs U x) +
        m.negOnePow • ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) •
          ev (R := R) α p t (by omega) U (x.face i)

def cx_ext : Prop := ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ} (α : Cochain ((chains R).obj E) I n),
  (∀ p s h U x, ev (R := R) α p s h U x = 0) → α = 0

def res_neg : Prop := ∀ (q : ℕ) (s : ℤ), s < 0 → ∀ (U : Scheme.{0}) (a : Sec ((res _ (tw q 1)).X s) U), a = 0

def EtaleFirstChernCochainCoboundaryVanishesSimplexDegreeOne : Prop := ∀ (q : ℕ) [NeZero q] {E : Spc} (L : E ⟶ ofCat (glCat 1)), Inv q E →
  ∀ α : Cochain ((chains (ZMod q)).obj E) (res _ (tw q 1)) 2, IsEtaleKummerChernClassCochainOfLineBundle q L α →
  ∀ (U : Scheme.{0}) (x : Sx E 1 U), ev (R := ZMod q) (δ 2 3 α) 1 2 (by simp) U x = 0

def EtaleFirstChernCochainCoboundaryVanishesSimplexDegreeTwo : Prop := ∀ (q : ℕ) [NeZero q] {E : Spc} (L : E ⟶ ofCat (glCat 1)), Inv q E →
  ∀ α : Cochain ((chains (ZMod q)).obj E) (res _ (tw q 1)) 2, IsEtaleKummerChernClassCochainOfLineBundle q L α →
  ∀ (U : Scheme.{0}) (x : Sx E 2 U), ev (R := ZMod q) (δ 2 3 α) 2 1 (by simp) U x = 0

def EtaleFirstChernCochainCoboundaryVanishesSimplexDegreeThree : Prop := ∀ (q : ℕ) [NeZero q] {E : Spc} (L : E ⟶ ofCat (glCat 1)), Inv q E →
  ∀ α : Cochain ((chains (ZMod q)).obj E) (res _ (tw q 1)) 2, IsEtaleKummerChernClassCochainOfLineBundle q L α →
  ∀ (U : Scheme.{0}) (x : Sx E 3 U), ev (R := ZMod q) (δ 2 3 α) 3 0 (by simp) U x = 0

theorem etale_first_chern_cochain_closed_of_degree_parts (hd : EvDelta) (hx : cx_ext) (hr : res_neg) (h1 : EtaleFirstChernCochainCoboundaryVanishesSimplexDegreeOne) (h2 : EtaleFirstChernCochainCoboundaryVanishesSimplexDegreeTwo) (h3 : EtaleFirstChernCochainCoboundaryVanishesSimplexDegreeThree) :
    EtaleKummerChernClassCochainIsCocycle := by
  intro q _ E L hi α hα
  apply hx
  intro p s h U x
  match p, x with
  | 0, x =>
    obtain rfl : s = 3 := by omega
    rw [(hd (ZMod q) (show (2:ℤ) + 1 = 3 by norm_num) α U).1 x, hα.1 U x]
    exact map_zero ((((res (ZMod q) (tw q 1)).d 2 3).hom.app (op U)).hom)
  | 1, x =>
    obtain rfl : s = 2 := by omega
    exact h1 q L hi α hα U x
  | 2, x =>
    obtain rfl : s = 1 := by omega
    exact h2 q L hi α hα U x
  | 3, x =>
    obtain rfl : s = 0 := by omega
    exact h3 q L hi α hα U x
  | k + 4, x =>
    exact hr q s (by push_cast at h; omega) U _

end LateralTheory.EtaleFoundations

open LateralTheory.EtaleFoundations in
theorem LateralTheory.EtaleFoundations.etale_first_chern_cochain_closed_of_components (hd : EvDelta) (hx : cx_ext) (hr : res_neg) (h1 : EtaleFirstChernCochainCoboundaryVanishesSimplexDegreeOne) (h2 : EtaleFirstChernCochainCoboundaryVanishesSimplexDegreeTwo) (h3 : EtaleFirstChernCochainCoboundaryVanishesSimplexDegreeThree) :
    LateralTheory.EtaleFoundations.EtaleKummerChernClassCochainIsCocycle := etale_first_chern_cochain_closed_of_degree_parts hd hx hr h1 h2 h3
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def t_pa_tens_ex : Prop :=
  ∀ (R : Type) [CommRing R] (I J : Cx R), ∃ (T : Cx R) (τ : Pair I J T), τ.IsTensor

def t_pa_tens_univ : Prop :=
  ∀ (R : Type) [CommRing R] {I J T K : Cx R} (τ : Pair I J T), τ.IsTensor →
    ∀ μ : Pair I J K, ∃ u : T ⟶ K, τ.Compat μ (𝟙 I) (𝟙 J) u

def t_pa_precomp : Prop :=
  ∀ (R : Type) [CommRing R] {I I' J K : Cx R} (u : I ⟶ I') (μ : Pair I' J K),
    ∃ ρ : Pair I J K, ρ.Compat μ u (𝟙 J) (𝟙 K)

def t_pa_cpush_id : Prop :=
  ∀ (R : Type) [CommRing R] (E : Spc) (I : Cx R) (n : ℤ) (x : CohomologyClass ((chains R).obj E) I n),
    cpush _ (𝟙 I) n x = x

def t_pa_cpush_htpy : Prop :=
  ∀ (R : Type) [CommRing R] (E : Spc) {I J : Cx R} (u u' : I ⟶ J), Homotopy u u' →
    ∀ (n : ℤ) (x : CohomologyClass ((chains R).obj E) I n), cpush _ u n x = cpush _ u' n x

theorem pa_sec_map_id {R : Type} [CommRing R] {F : Shv R} {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (𝟙 F) x = x := rfl

theorem t_pair_assoc_of (htw : EtaleTensorPairTwistResolutionMul) (htri : EtaleTensorPairProductAssociative) (hext : EtaleTwistResolutionUniversalExtension)
    (hcc : EtaleCupProductNaturalInCoefficients) (ha0 : EtaleCochainCupAssociativeOfPairing) (hex : t_pa_tens_ex) (huniv : t_pa_tens_univ)
    (hpre : t_pa_precomp) (hid : t_pa_cpush_id) (hhtpy : t_pa_cpush_htpy) : t_pair_assoc := by
  intro q _ E i j l k₁ k₂ k e1 e2 e3 μ₁ μ₂ ν₁ ν₂ p1 p2 p3 p4 n m p s₁ s₂ s h₁ h₂ h₃ h₄ a b c
  obtain ⟨T, τ, hτ⟩ := hex (ZMod q) (res _ (tw q i)) (res _ (tw q j))
  obtain ⟨T3, τ', hτ'⟩ := hex (ZMod q) T (res _ (tw q l))
  obtain ⟨u, hu⟩ := huniv (ZMod q) τ hτ μ₁
  obtain ⟨ρ, hρ⟩ := hpre (ZMod q) u μ₂
  obtain ⟨ν, hν⟩ := htri (ZMod q) τ τ' hτ hτ' ν₁ ν₂
  obtain ⟨w₁, hw₁⟩ := huniv (ZMod q) τ' hτ' ρ
  obtain ⟨w₂, hw₂⟩ := huniv (ZMod q) τ' hτ' ν
  obtain ⟨ri, -, -⟩ := hext q i
  obtain ⟨rj, fj, -⟩ := hext q j
  obtain ⟨rl, fl, -⟩ := hext q l
  have hT := htw q i j k₁ e1 _ _ ri rj fj τ hτ
  have ek : k₁ + l = k := by omega
  have hT3 := htw q k₁ l k ek _ _ hT rl fl τ' hτ'
  obtain ⟨-, -, huniq⟩ := hext q k
  obtain ⟨H⟩ := (huniq _ hT3).2 w₁ w₂ (by
    intro U ζ
    rw [hw₁, hw₂]
    simp only [HomologicalComplex.id_f, pa_sec_map_id]
    rw [hν U 0 0 0 0 0 0 (add_zero 0) (add_zero 0) (add_zero 0) (add_zero 0)]
    have r1 := hρ U 0 0 0 (add_zero 0) (τ.mul U 0 0 0 (add_zero 0) (resGen i ζ) (resGen j ζ)) (resGen l ζ)
    simp only [HomologicalComplex.id_f, pa_sec_map_id] at r1
    have r2 := hu U 0 0 0 (add_zero 0) (resGen i ζ) (resGen j ζ)
    simp only [HomologicalComplex.id_f, pa_sec_map_id] at r2
    erw [r1, r2, p1, p2, p3, p4])
  have L1 : μ₁.cup E h₁ a b = cpush _ u s₁ (τ.cup E h₁ a b) := by
    rw [hcc _ τ μ₁ (𝟙 _) (𝟙 _) u hu E h₁ a b, hid, hid]
  have L2 : ∀ y, μ₂.cup E h₂ (cpush _ u s₁ y) c = ρ.cup E h₂ y c := by
    intro y
    have := hcc _ ρ μ₂ u (𝟙 _) (𝟙 _) hρ E h₂ y c
    rw [hid, hid] at this
    exact this.symm
  have L3 : ∀ y, ρ.cup E h₂ y c = cpush _ w₁ s (τ'.cup E h₂ y c) := by
    intro y
    rw [hcc _ τ' ρ (𝟙 _) (𝟙 _) w₁ hw₁ E h₂ y c, hid, hid]
  have L4 : ∀ y, ν.cup E h₂ y c = cpush _ w₂ s (τ'.cup E h₂ y c) := by
    intro y
    rw [hcc _ τ' ν (𝟙 _) (𝟙 _) w₂ hw₂ E h₂ y c, hid, hid]
  rw [← ha0 _ τ ν ν₁ ν₂ hν E h₁ h₂ h₃ h₄ a b c, L1, L2, L3, L4, hhtpy _ E w₁ w₂ H]

end LateralTheory.EtaleFoundations
end
