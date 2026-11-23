module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.FirstChernCompatibleSystem
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.RootPowLC

theorem mem_basicOpen_prod {U : Scheme.{0}} {ι : Type} (t : Finset ι) (s : ι → Γ(U, ⊤)) (u : U)
    (h : ∀ a ∈ t, u ∈ U.basicOpen (s a)) : u ∈ U.basicOpen (∏ a ∈ t, s a) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, U.basicOpen_of_isUnit isUnit_one]
    trivial
  | insert a t ha ih =>
    rw [Finset.prod_insert ha, Scheme.basicOpen_mul]
    exact ⟨h a (Finset.mem_insert_self a t), ih fun b hb => h b (Finset.mem_insert_of_mem hb)⟩

theorem exists_notMem_basicOpen {U : Scheme.{0}} {ι : Type} (t : Finset ι) (s : ι → Γ(U, ⊤))
    (h : ∏ a ∈ t, s a = 0) (u : U) : ∃ a ∈ t, u ∉ U.basicOpen (s a) := by
  by_contra hc
  push_neg at hc
  have hm := mem_basicOpen_prod t s u hc
  rw [h, Scheme.basicOpen_zero] at hm
  exact hm

theorem mem_basicOpen_of_isUnit_sub {U : Scheme.{0}} (x y : Γ(U, ⊤)) (h : IsUnit (x - y)) (u : U)
    (hx : u ∉ U.basicOpen x) : u ∈ U.basicOpen y := by
  rw [Scheme.mem_basicOpen_top] at hx ⊢
  have h1 : IsUnit (U.presheaf.germ ⊤ u trivial (x - y)) := h.map _
  rw [map_sub, sub_eq_add_neg] at h1
  rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add h1 with h2 | h2
  · exact absurd h2 hx
  · simpa using h2.neg

theorem isUnit_appTop_of_mem {V U : Scheme.{0}} (g : V ⟶ U) (x : Γ(U, ⊤))
    (h : ∀ v : V, g v ∈ U.basicOpen x) : IsUnit (g.appTop.hom x) := by
  refine RingedSpace.isUnit_of_isUnit_germ V.toRingedSpace ⊤ _ fun v _ => ?_
  have e : V.basicOpen (g.appTop.hom x) = g ⁻¹ᵁ U.basicOpen x := (Scheme.preimage_basicOpen g x).symm
  have hv : v ∈ V.basicOpen (g.appTop.hom x) := by
    rw [e]
    exact h v
  exact (Scheme.mem_basicOpen_top V (g.appTop.hom x) v).1 hv

theorem exists_isPow (hP : PrimAlg) (q : ℕ) [NeZero q] (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤))
    (r : Γ(U, ⊤)) (hr : r ^ q = 1) :
    ∃ f : LocallyConstant U (ZMod q), IsPow ζ f r ∧
      ∀ (u : U) (a : ZMod q), u ∉ U.basicOpen (r - ζ.1 ^ a.val) → f u = a := by
  classical
  have hprod : ∏ a : ZMod q, (r - ζ.1 ^ a.val) = 0 := by
    rw [← (hP q _ ζ).2.2.1 r, hr, sub_self]
  have hex : ∀ u : U, ∃ a : ZMod q, u ∉ U.basicOpen (r - ζ.1 ^ a.val) := by
    intro u
    obtain ⟨a, -, ha⟩ := exists_notMem_basicOpen Finset.univ (fun a : ZMod q => r - ζ.1 ^ a.val) hprod u
    exact ⟨a, ha⟩
  have huniq : ∀ (u : U) (a b : ZMod q), a ≠ b → u ∉ U.basicOpen (r - ζ.1 ^ a.val) →
      u ∈ U.basicOpen (r - ζ.1 ^ b.val) := by
    intro u a b hab ha
    apply mem_basicOpen_of_isUnit_sub _ _ _ u ha
    have hd : (r - ζ.1 ^ a.val) - (r - ζ.1 ^ b.val) = ζ.1 ^ b.val - ζ.1 ^ a.val := by ring
    rw [hd]
    exact (hP q _ ζ).2.1 b a (Ne.symm hab)
  obtain ⟨f0, hf0def⟩ : ∃ f0 : U → ZMod q, f0 = fun u => Classical.choose (hex u) := ⟨_, rfl⟩
  have hf0 : ∀ u, u ∉ U.basicOpen (r - ζ.1 ^ (f0 u).val) := by
    intro u
    rw [hf0def]
    exact Classical.choose_spec (hex u)
  have hf0_iff : ∀ u a, f0 u = a ↔ u ∉ U.basicOpen (r - ζ.1 ^ a.val) := by
    intro u a
    constructor
    · rintro rfl
      exact hf0 u
    · intro ha
      by_contra hne
      exact (hf0 u) (huniq u a (f0 u) (Ne.symm hne) ha)
  have hloc : IsLocallyConstant f0 := by
    rw [IsLocallyConstant.iff_isOpen_fiber]
    intro a
    have hfib : f0 ⁻¹' {a} = ⋂ b ∈ (Finset.univ.erase a : Finset (ZMod q)), (U.basicOpen (r - ζ.1 ^ b.val) : Set U) := by
      ext u
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iInter, Finset.mem_erase, Finset.mem_univ,
        and_true, SetLike.mem_coe]
      rw [hf0_iff]
      constructor
      · intro ha b hb
        exact huniq u a b (Ne.symm hb) ha
      · intro h ha
        obtain ⟨a', ha'⟩ := hex u
        by_cases heq : a' = a
        · exact ha' (heq ▸ ha)
        · exact ha' (h a' heq)
    rw [hfib]
    exact isOpen_biInter_finset fun b _ => (U.basicOpen (r - ζ.1 ^ b.val)).isOpen
  refine ⟨⟨f0, hloc⟩, ?_, fun u a ha => (hf0_iff u a).mpr ha⟩
  delta CrystallineSemistableComparison.E.IsPow
  intro V g a hga
  have hunitb : ∀ b : ZMod q, b ≠ a → IsUnit (g.appTop.hom (r - ζ.1 ^ b.val)) := fun b hb =>
    isUnit_appTop_of_mem g _ (fun v => huniq (g v) a b (Ne.symm hb) ((hf0_iff (g v) a).mp (hga v)))
  have hprodV : ∏ b : ZMod q, (g.appTop.hom r - g.appTop.hom ζ.1 ^ b.val) = 0 := by
    have h0 := congrArg g.appTop.hom hprod
    rw [map_prod, map_zero] at h0
    simpa only [map_sub, map_pow] using h0
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ a)] at hprodV
  have hu : IsUnit (∏ b ∈ Finset.univ.erase a, (g.appTop.hom r - g.appTop.hom ζ.1 ^ b.val)) := by
    refine Finset.prod_induction _ IsUnit (fun x y hx hy => hx.mul hy) isUnit_one (fun b hb => ?_)
    have h1 := hunitb b (Finset.ne_of_mem_erase hb)
    simpa only [map_sub, map_pow] using h1
  have h0 : g.appTop.hom r - g.appTop.hom ζ.1 ^ a.val = 0 := hu.mul_left_eq_zero.mp hprodV
  show g.appTop.hom r = (g.appTop.hom ζ.1) ^ a.val
  exact sub_eq_zero.mp h0

theorem rootPow : CrystallineSemistableComparison.E.PrimAlg → CrystallineSemistableComparison.E.RootPow := by
  intro hP q _ U ζ
  refine ⟨fun r hr => ?_, fun ξ => ?_⟩
  · obtain ⟨f, hf, -⟩ := exists_isPow hP q U ζ r hr
    exact ⟨f, hf⟩
  · have hξq : ξ.1 ^ q = 1 := (hP q _ ξ).1
    obtain ⟨f, hf, hloc⟩ := exists_isPow hP q U ζ ξ.1 hξq
    refine ⟨f, hf, fun u => ?_⟩
    have hprod : ∏ a : ZMod q, (ξ.1 - ζ.1 ^ a.val) = 0 := by
      rw [← (hP q _ ζ).2.2.1 ξ.1, hξq, sub_self]
    obtain ⟨a, -, ha⟩ := exists_notMem_basicOpen Finset.univ
      (fun a : ZMod q => ξ.1 - ζ.1 ^ a.val) hprod u
    rw [hloc u a ha]
    by_contra hna
    set m := a.val with hm
    have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
    have ha' : a = (m : ZMod q) := (ZMod.natCast_zmod_val a).symm
    have hcop : ¬ m.Coprime q := by
      intro hc
      exact hna (ha' ▸ (ZMod.isUnit_iff_coprime m q).2 hc)
    set g := Nat.gcd m q with hgdef
    have hg1 : g ≠ 1 := hcop
    have hgpos : 0 < g := Nat.gcd_pos_of_pos_right m hq
    have hgq : g ∣ q := Nat.gcd_dvd_right m q
    have hgm : g ∣ m := Nat.gcd_dvd_left m q
    set k := q / g with hkdef
    have hkpos : 0 < k := Nat.div_pos (Nat.le_of_dvd hq hgq) hgpos
    have hklt : k < q := Nat.div_lt_self hq (by omega)
    have hζq : ζ.1 ^ q = 1 := (hP q _ ζ).1
    have hζmk : (ζ.1 ^ m) ^ k = 1 := by
      obtain ⟨m', hm'⟩ := hgm
      have e1 : m * k = q * m' := by
        rw [hm', hkdef, mul_comm g m', mul_assoc, Nat.mul_div_cancel' hgq, mul_comm]
      rw [← pow_mul, e1, pow_mul, hζq, one_pow]
    have hunit : IsUnit (ξ.1 ^ k - 1) := by
      have hne : ((k : ℕ) : ZMod q) ≠ 0 := by
        rw [Ne, ZMod.natCast_eq_zero_iff]
        intro hd
        exact absurd (Nat.le_of_dvd hkpos hd) (by omega)
      have hu := (hP q _ ξ).2.1 (k : ZMod q) 0 hne
      rwa [ZMod.val_natCast_of_lt hklt, ZMod.val_zero, pow_zero] at hu
    have hdvd : ξ.1 - ζ.1 ^ m ∣ ξ.1 ^ k - 1 := by
      have hs := sub_dvd_pow_sub_pow ξ.1 (ζ.1 ^ m) k
      rwa [hζmk] at hs
    apply ha
    rw [Scheme.mem_basicOpen_top]
    exact isUnit_of_dvd_unit (map_dvd _ hdvd) (hunit.map _)

end GlobalTheory.CompanionTheory.RootPowLC
end

section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.KapSpecProof

variable {R : Type} [CommRing R]

theorem res_comp {G : Shv R} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (x : Sec G U) :
    Sec.res (k ≫ g) x = Sec.res k (Sec.res g x) := by
  delta GlobalTheory.EtC.Sec.res
  rw [op_comp, Functor.map_comp]
  rfl

theorem primRes_comp {q : ℕ} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (ζ : Prim q Γ(U, ⊤)) :
    primRes (k ≫ g) ζ = primRes k (primRes g ζ) := by
  apply Subtype.ext
  delta CrystallineSemistableComparison.E.primRes
  rfl

theorem sec_subsingleton (hL : LcCover) {U : Scheme.{0}} [IsEmpty U] (G : Shv R) :
    Subsingleton (Sec G U) := by
  let f0 : LocallyConstant U Empty :=
    ⟨fun u => isEmptyElim u, fun s => by
      convert isOpen_empty
      ext u
      exact isEmptyElim u⟩
  obtain ⟨W, j, -, -, -, hglue⟩ := hL U Empty f0
  obtain ⟨z, -, hz⟩ := hglue R G (fun a => a.elim)
  exact ⟨fun x x' => (hz x (fun a => a.elim)).trans (hz x' (fun a => a.elim)).symm⟩

theorem sec_ext (hL : LcCover) {ι : Type} {U : Scheme.{0}} (f : LocallyConstant U ι) (G : Shv R)
    (x y : Sec G U)
    (h : ∀ (V : Scheme.{0}) (g : V ⟶ U) (a : ι), (∀ v : V, f (g v) = a) → Sec.res g x = Sec.res g y) :
    x = y := by
  obtain ⟨W, j, hWf, -, -, hglue⟩ := hL U ι f
  obtain ⟨z, -, hz⟩ := hglue R G (fun a => Sec.res (j a) x)
  exact (hz x (fun a => rfl)).trans (hz y (fun a => (h (W a) (j a) a (hWf a)).symm)).symm

variable {q : ℕ} {i : ℤ}

theorem isLC_unique (hL : LcCover) {U : Scheme.{0}} {ζ : Prim q Γ(U, ⊤)}
    {f : LocallyConstant U (ZMod q)} {x y : Sec (tw q i) U} (hx : IsLC i ζ f x) (hy : IsLC i ζ f y) :
    x = y := by
  refine sec_ext hL f _ x y fun V g a hga => ?_
  delta CrystallineSemistableComparison.E.IsLC at hx hy
  rw [hx V g a hga, hy V g a hga]

theorem isLC_exists (hL : LcCover) (hR : RepRoot) {U : Scheme.{0}} (ζ : Prim q Γ(U, ⊤))
    (f : LocallyConstant U (ZMod q)) : ∃ x : Sec (tw q i) U, IsLC i ζ f x := by
  delta CrystallineSemistableComparison.E.IsLC
  have hres_smul : ∀ {V W : Scheme.{0}} (g : V ⟶ W) (c : ULift (ZMod q)) (y : Sec (tw q i) W),
      Sec.res g (c • y) = c • Sec.res g y := fun g c y => by
    delta GlobalTheory.EtC.Sec.res
    exact map_smul _ c y
  obtain ⟨W, j, -, hfac, -, hglue⟩ := hL U (ZMod q) f
  obtain ⟨x, hx, -⟩ := hglue (ZMod q) (tw q i)
    (fun a => (⟨a⟩ : ULift (ZMod q)) • twGen i (primRes (j a) ζ))
  refine ⟨x, fun V g a ha => ?_⟩
  obtain ⟨k, rfl⟩ := hfac V g a ha
  rw [res_comp, hx a, hres_smul, ((hR q i (W a) (primRes (j a) ζ)).1 V k).1, ← primRes_comp]

theorem isLC_add (hL : LcCover) (hR : RepRoot) {U : Scheme.{0}} {ζ : Prim q Γ(U, ⊤)}
    {f f' : LocallyConstant U (ZMod q)} {x x' : Sec (tw q i) U} (hx : IsLC i ζ f x)
    (hx' : IsLC i ζ f' x') : IsLC i ζ (f + f') (x + x') := by
  delta CrystallineSemistableComparison.E.IsLC at hx hx' ⊢
  intro V g a ha
  have hres_smul : ∀ {V W : Scheme.{0}} (g : V ⟶ W) (c : ULift (ZMod q)) (y : Sec (tw q i) W),
      Sec.res g (c • y) = c • Sec.res g y := fun g c y => by
    delta GlobalTheory.EtC.Sec.res
    exact map_smul _ c y
  have hcont : Continuous (fun v : V => g v) := g.continuous
  let F2 : LocallyConstant V (ZMod q × ZMod q) :=
    ⟨fun v => (f (g v), f' (g v)), IsLocallyConstant.comp₂ (f.isLocallyConstant.comp_continuous hcont)
      (f'.isLocallyConstant.comp_continuous hcont) Prod.mk⟩
  refine sec_ext hL F2 _ _ _ fun V' g' b hb => ?_
  rcases isEmpty_or_nonempty V' with hV | ⟨⟨v⟩⟩
  · haveI := sec_subsingleton hL (U := V') (tw q i)
    exact Subsingleton.elim _ _
  have hb1 : ∀ v, f ((g' ≫ g) v) = b.1 := fun v => congrArg Prod.fst (hb v)
  have hb2 : ∀ v, f' ((g' ≫ g) v) = b.2 := fun v => congrArg Prod.snd (hb v)
  have hres_add : ∀ (y y' : Sec (tw q i) U),
      Sec.res (g' ≫ g) (y + y') = Sec.res (g' ≫ g) y + Sec.res (g' ≫ g) y' := fun y y' => by
    delta GlobalTheory.EtC.Sec.res
    exact map_add _ y y'
  have hab : a = b.1 + b.2 := by
    rw [← ha (g' v), ← hb1 v, ← hb2 v]
    rfl
  rw [← res_comp, hres_add, hx V' (g' ≫ g) b.1 hb1, hx' V' (g' ≫ g) b.2 hb2, ← add_smul, hres_smul,
    ((hR q i V (primRes g ζ)).1 V' g').1, ← primRes_comp, hab]
  rfl

theorem isLC_res {U V : Scheme.{0}} {ζ : Prim q Γ(U, ⊤)}
    {f : LocallyConstant U (ZMod q)} {x : Sec (tw q i) U} (hx : IsLC i ζ f x) (g : V ⟶ U) :
    IsLC i (primRes g ζ) (lcRes q g f) (Sec.res g x) := by
  delta CrystallineSemistableComparison.E.IsLC at hx ⊢
  intro W h a ha
  rw [← res_comp, hx W (h ≫ g) a ?_, primRes_comp]
  intro w
  exact ha w

theorem kapSpec : LcCover → RepRoot → KapSpec := by
  intro hL hR q i U ζ f
  have hk : ∀ {U' : Scheme.{0}} (ζ' : Prim q Γ(U', ⊤)) (f' : LocallyConstant U' (ZMod q)),
      IsLC i ζ' f' (kap i ζ' f') := by
    intro U' ζ' f'
    have hex : ∃ κ : LocallyConstant U' (ZMod q) →+ Sec (tw q i) U', ∀ f'', IsLC i ζ' f'' (κ f'') := by
      choose c hc using fun f'' : LocallyConstant U' (ZMod q) => isLC_exists hL hR (i := i) ζ' f''
      refine ⟨{ toFun := c, map_zero' := ?_, map_add' := fun a b => ?_ }, hc⟩
      · have h := isLC_unique hL (hc (0 + 0)) (isLC_add hL hR (hc 0) (hc 0))
        simpa using h
      · exact isLC_unique hL (hc (a + b)) (isLC_add hL hR (hc a) (hc b))
    delta CrystallineSemistableComparison.E.kap
    exact GlobalTheory.EtC.pick_spec hex f'
  refine ⟨hk ζ f, fun x hx => isLC_unique hL hx (hk ζ f), fun V g => ?_⟩
  exact isLC_unique hL (isLC_res (hk ζ f) g) (hk _ _)

end GlobalTheory.CompanionTheory.KapSpecProof
end

section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.ChernSys

theorem inv_cech (hpt : CrystallineSemistableComparison.E.CechPt) (l : ℕ) {Y X : Scheme.{0}} (f : Y ⟶ X)
    (hl : IsUnit (l : Γ(X, ⊤))) (n : ℕ) : GlobalTheory.EtC.Inv (l ^ n) (cech f) := by
  rintro U ⟨z⟩
  obtain ⟨x, y, h, -⟩ := (hpt Y X f 0 U).1 z
  have h1 : IsUnit (l : Γ(U, ⊤)) := by
    have := hl.map x.appTop.hom
    rwa [map_natCast] at this
  rw [Nat.cast_pow]
  exact h1.pow n

theorem chern_class_compatible_system (hpt : CrystallineSemistableComparison.E.CechPt) : CrystallineSemistableComparison.E.FirstChernCompatibleSystem := by
  intro a2 a11 l _ Y X f _ _ hl L
  have hinv := inv_cech hpt l f hl
  have hne : ∀ n, NeZero (l ^ n) := fun n => ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  refine ⟨hinv, ?_⟩
  have hb : ∀ n, Function.Bijective (pull (ZMod (l ^ n)) (_root_.GlobalTheory.EtC.cechAug f) (tw (l ^ n) 1) 2) :=
    fun n => a2 (ZMod (l ^ n)) f (tw (l ^ n) 1) 2
  choose x hx using fun n => (hb n).2 (c1 (l ^ n) L)
  refine ⟨⟨x, fun k => ?_⟩, hx⟩
  apply (hb k).1
  have e := ((a11 (l ^ (k + 1)) (l ^ k) (pow_dvd_pow l (Nat.le_succ k)) (cech f)).2.1 (hinv (k + 1))).2 L
  have e2 := pull_red (l ^ (k + 1)) (l ^ k) (_root_.GlobalTheory.EtC.cechAug f) 2 1 (x (k + 1))
  exact e2.trans ((congrArg _ (hx (k + 1))).trans (e.trans (hx k).symm))

end GlobalTheory.CompanionTheory.ChernSys
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.EdgeRoot

theorem kap_one_eq_twGen (hRep : CrystallineSemistableComparison.E.RepRoot) (hKap : CrystallineSemistableComparison.E.KapSpec) {q : ℕ} (i : ℤ) {U : Scheme.{0}}
    (ζ : Prim q Γ(U, ⊤)) : kap i ζ 1 = twGen i ζ := by
  refine ((hKap q i U ζ 1).2.1 (twGen i ζ) ?_).symm
  intro V g a h
  rw [((hRep q i U ζ).1 V g).1]
  by_cases hV : Nonempty V
  · obtain ⟨v⟩ := hV
    have ha : (1 : ZMod q) = a := h v
    subst ha
    exact (one_smul _ _).symm
  · have hV' : IsEmpty V := not_nonempty_iff.1 hV
    have h0 := (hKap q i U ζ 1).1 V g 0 (fun v => hV'.elim v)
    have h1 := (hKap q i U ζ 1).1 V g 1 (fun v => hV'.elim v)
    have hz : twGen i (primRes g ζ) = 0 := by
      have e : (ULift.up (1 : ZMod q) : ULift.{1} (ZMod q)) • twGen i (primRes g ζ) =
          (ULift.up (0 : ZMod q) : ULift.{1} (ZMod q)) • twGen i (primRes g ζ) := h1.symm.trans h0
      have e1 : (ULift.up (1 : ZMod q) : ULift.{1} (ZMod q)) • twGen i (primRes g ζ) = twGen i (primRes g ζ) :=
        one_smul _ _
      have e0 : (ULift.up (0 : ZMod q) : ULift.{1} (ZMod q)) • twGen i (primRes g ζ) = 0 := zero_smul _ _
      rw [e1, e0] at e
      exact e
    rw [hz, smul_zero]

theorem d_one_eq_zero {C : Type 1} [Category.{0} C] {R : Type} [CommRing R] (A : C ⥤ CommAlgCat.{0} R) :
    d (modF A) 0 (fun s => (1 : A.obj (s.obj (Fin.last 0)))) = 0 := by
  funext s
  change ∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) • (A.map (GlobalTheory.CatH.toLast i s)).hom 1 = (0 : A.obj _)
  rw [Fin.sum_univ_two, map_one, map_one]
  simp

theorem etRoot_of_spec : CrystallineSemistableComparison.E.EtSpec → CrystallineSemistableComparison.E.RepRoot → CrystallineSemistableComparison.E.KapSpec → CrystallineSemistableComparison.E.EtRoot := by
  intro hEt hRep hKap hGen q _ C _ P X Y ζ hζ i
  refine ((hEt hGen q C P X Y i 0 (rootClass i ζ)).2 _ ?_).symm
  refine ⟨resGen i ζ, (hRep q i X ζ).2, ?_⟩
  refine ⟨fun s => (1 : (lcF P.S q).obj (s.obj (Fin.last 0))), d_one_eq_zero (lcF P.S q), ?_, rfl⟩
  refine ⟨rfl, ?_⟩
  funext s
  change Sec.map (resι _ (tw q i)) (kap i (P.ζ (s.obj (Fin.last 0))) 1) = Sec.res (Y.y (s.obj (Fin.last 0))) (resGen i ζ)
  rw [kap_one_eq_twGen hRep hKap, ((hRep q i X ζ).1 _ _).2, hζ]
  rfl

end GlobalTheory.CompanionTheory.EdgeRoot
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.CompanionTheory.EtNatProof

def resHom {R : Type} [CommRing R] (G : Shv R) {V U : Scheme.{0}} (g : V ⟶ U) : Sec G U →+ Sec G V :=
  (G.obj.map g.op).hom.toAddMonoidHom

theorem res_res {R : Type} [CommRing R] (G : Shv R) {W V U : Scheme.{0}} (f : W ⟶ V) (g : V ⟶ U) (a : Sec G U) :
    Sec.res f (Sec.res g a) = Sec.res (f ≫ g) a := by
  simp [Sec.res]

theorem res_map {R : Type} [CommRing R] {G G' : Shv R} (φ : G ⟶ G') {V U : Scheme.{0}} (g : V ⟶ U) (a : Sec G U) :
    Sec.res g (Sec.map φ a) = Sec.map φ (Sec.res g a) := by
  have h := φ.hom.naturality g.op
  exact (congrArg (fun t => t.hom a) h).symm

theorem kap_zero (hKap : KapSpec) (hTw : TwZero) (hGen : InGen) (q : ℕ) [NeZero q] {U : Scheme.{0}}
    (ζ ξ : Prim q Γ(U, ⊤)) (f : LocallyConstant U (ZMod q)) : kap 0 ζ f = kap 0 ξ f := by
  refine ((hKap q 0 U ζ f).2.1 _ ?_).symm
  intro V g a hv
  rw [(hKap q 0 U ξ f).1 V g a hv, hTw hGen q V (primRes g ξ) (primRes g ζ)]

def resMor {q : ℕ} {C C' : Type 1} [Category.{0} C] [Category.{0} C'] (P : Probe C q) (P' : Probe C' q)
    (m : Mor P.L P'.L (RingHom.id ℤ)) (g : ∀ c : C', P'.U c ⟶ P.U (m.G.obj c))
    (hg : ∀ {c c' : C'} (φ : c ⟶ c'), g c' ≫ (P.S.map (m.G.map φ)).unop = (P'.S.map φ).unop ≫ g c)
    (i : ℤ)
    (hι : ∀ (c : C') (f : LocallyConstant (P.U (m.G.obj c)) (ZMod q)),
      Sec.res (g c) (kap i (P.ζ (m.G.obj c)) f) = kap i (P'.ζ c) (m.τ c f)) :
    ResMor (P.res i) (P'.res i) m where
  τ s c := resHom _ (g c)
  nat s {c c'} φ x := by
    change Sec.res (g c') (Sec.res (P.S.map (m.G.map φ)).unop x) = Sec.res (P'.S.map φ).unop (Sec.res (g c) x)
    rw [res_res, res_res, hg φ]
  ι c x := by
    change Sec.res (g c) (Sec.map (resι _ (tw q i)) (kap i (P.ζ (m.G.obj c)) x)) =
      Sec.map (resι _ (tw q i)) (kap i (P'.ζ c) (m.τ c x))
    rw [res_map, hι]
  dv s c x := by
    change Sec.res (g c) (Sec.map ((GlobalTheory.EtC.res _ (tw q i)).d (s : ℤ) ((s + 1 : ℕ) : ℤ)) x) =
      Sec.map ((GlobalTheory.EtC.res _ (tw q i)).d (s : ℤ) ((s + 1 : ℕ) : ℤ)) (Sec.res (g c) x)
    exact res_map _ _ _

theorem etNat : CrystallineSemistableComparison.E.EtSpec → CrystallineSemistableComparison.E.EdgeMap → CrystallineSemistableComparison.E.RepBasic → CrystallineSemistableComparison.E.KapSpec → CrystallineSemistableComparison.E.TwZero → CrystallineSemistableComparison.E.EtNat := by
  intro hEt hEM hRep hKap hTw hGen q _ C C' _ _ P P' X X' Y Y' u m g hg hτ hy i hi j x
  obtain ⟨a, ha⟩ := (hRep (ZMod q) (GlobalTheory.EtC.res _ (tw q i)) X (j : ℤ)).1 x
  have hE := (hEt hGen q C P X Y i j x).1 a ha
  have hι : ∀ (c : C') (f : LocallyConstant (P.U (m.G.obj c)) (ZMod q)),
      Sec.res (g c) (kap i (P.ζ (m.G.obj c)) f) = kap i (P'.ζ c) (m.τ c f) := by
    intro c f
    rw [(hKap q i _ (P.ζ (m.G.obj c)) f).2.2 _ (g c), hτ c f]
    rcases hi with rfl | hi
    · exact kap_zero hKap hTw hGen q _ _ _
    · rw [hi c]
  let n := resMor P P' m g hg i hι
  have hE' := hEM ℤ ℤ (RingHom.id ℤ) C C' P.L P'.L (P.res i) (P'.res i) m n j _ _ hE
  have hglob : n.pullC j 0 (Y.glob i j a) = Y'.glob i j (Sec.res u a) := by
    funext t
    change Sec.res (g (t.obj (Fin.last 0))) (Sec.res (Y.y (m.G.obj (t.obj (Fin.last 0)))) a) =
      Sec.res (Y'.y (t.obj (Fin.last 0))) (Sec.res u a)
    rw [res_res, res_res, hy]
  rw [hglob] at hE'
  have hR : Rep (pull _ (sch.map u) _ j x) (Sec.res u a) :=
    (hRep (ZMod q) (GlobalTheory.EtC.res _ (tw q i)) X (j : ℤ)).2.2.2.2 X' u x a ha
  exact (hEt hGen q C' P' X' Y' i j _).2 _ ⟨_, hR, hE'⟩

end GlobalTheory.CompanionTheory.EtNatProof

end
end
