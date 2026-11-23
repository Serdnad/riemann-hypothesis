module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.EtSide
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AdicTorsionCup.PowNsmulEqZero
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007

@[expose] public section

section

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace CrystallineSemistableComparison.AdicGeo

theorem lift_facts {X S Z Y : Scheme.{0}} (u : Y ⟶ X) (f : X ⟶ S) (g : Z ⟶ S) (fY : Y ⟶ S) (hf : u ≫ f = fY) :
    (IsOpenImmersion u → IsOpenImmersion (pullback.lift (pullback.fst fY g ≫ u) (pullback.snd fY g)
      (by rw [Category.assoc, hf, pullback.condition]) : pullback fY g ⟶ pullback f g)) ∧
    Set.range (pullback.lift (pullback.fst fY g ≫ u) (pullback.snd fY g)
      (by rw [Category.assoc, hf, pullback.condition]) : pullback fY g ⟶ pullback f g) =
      pullback.fst f g ⁻¹' Set.range u := by
  subst hf
  have key : (pullback.lift (pullback.fst (u ≫ f) g ≫ u) (pullback.snd (u ≫ f) g)
      (by rw [Category.assoc, pullback.condition]) : pullback (u ≫ f) g ⟶ pullback f g) =
      pullback.map (u ≫ f) g f g u (𝟙 Z) (𝟙 S) (by simp) (by simp) := by
    apply pullback.hom_ext <;> simp
  refine ⟨fun hu => ?_, ?_⟩
  · have hsq : IsPullback (pullback.lift (pullback.fst (u ≫ f) g ≫ u) (pullback.snd (u ≫ f) g)
        (by rw [Category.assoc, pullback.condition]) : pullback (u ≫ f) g ⟶ pullback f g)
        (pullback.fst (u ≫ f) g) (pullback.fst f g) u := by
      refine IsPullback.of_right (h₁₂ := pullback.snd f g) (h₂₂ := f) (v₁₃ := g) ?_ (by simp)
        (IsPullback.of_hasPullback f g).flip
      rw [pullback.lift_snd]
      exact (IsPullback.of_hasPullback (u ≫ f) g).flip
    exact MorphismProperty.of_isPullback hsq.flip hu
  · rw [key, Scheme.Pullback.range_map]
    simp

theorem isSum_lift {X S Z : Scheme.{0}} {r : ℕ} {Y : Fin r → Scheme.{0}} (u : ∀ s, Y s ⟶ X) (f : X ⟶ S) (g : Z ⟶ S)
    (fY : ∀ s, Y s ⟶ S) (hf : ∀ s, u s ≫ f = fY s) (h : IsSum u) :
    IsSum (fun s => (pullback.lift (pullback.fst (fY s) g ≫ u s) (pullback.snd (fY s) g)
      (by rw [Category.assoc, hf, pullback.condition]) : pullback (fY s) g ⟶ pullback f g)) := by
  obtain ⟨ho, hc, hd⟩ := h
  refine ⟨fun s => (lift_facts (u s) f g (fY s) (hf s)).1 (ho s), fun x => ?_, fun s s' hss' => ?_⟩
  · obtain ⟨s, hs⟩ := hc (pullback.fst f g x)
    refine ⟨s, ?_⟩
    rw [(lift_facts (u s) f g (fY s) (hf s)).2]
    exact hs
  · rw [(lift_facts (u s) f g (fY s) (hf s)).2, (lift_facts (u s') f g (fY s') (hf s')).2]
    exact (hd s s' hss').preimage _

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

abbrev str (M : Model l K) : GlobalTheory.Et.geom (PadicAlgCl l) M.q ⟶ Spec (CommRingCat.of (PadicAlgCl l)) :=
  pullback.snd M.q (Spec.map (CommRingCat.ofHom (algebraMap K (PadicAlgCl l))))

theorem isSum_geom {M : Model l K} {r : ℕ} {P : Fin r → Model l K} (u : ∀ a, (P a).X ⟶ M.X)
    (hu : ∀ a, u a ≫ M.p = (P a).p) (h : IsSum u) :
    IsSum (fun a => GlobalTheory.Et.geomMap (PadicAlgCl l) (P a).q (Model.genMap (u a) (hu a)) (Model.genMap_q (u a) (hu a))) :=
  isSum_lift (fun a => Model.genMap (u a) (hu a)) M.q _ (fun a => (P a).q) (fun a => Model.genMap_q (u a) (hu a))
    (isSum_lift u M.p _ (fun a => (P a).p) hu h)

theorem proper_p {M : Model l K} (h : M.Good) : IsProper M.p := by
  obtain ⟨N, i, hi, e⟩ := h.1
  have := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str (OK l K) N
  rw [← e]
  infer_instance

theorem proper_str {M : Model l K} (h : M.Good) : IsProper (str M) := by
  have := proper_p h
  infer_instance

theorem comp_str {M : Model l K} (h : M.Good) {d : ℕ} (hc : M.Conn d) {r : ℕ} {Y : Fin r → Scheme.{0}}
    (j : ∀ s, Y s ⟶ GlobalTheory.Et.geom (PadicAlgCl l) M.q) (hj : IsSum j) (s : Fin r) :
    IsProper (j s ≫ str M) ∧ SmoothOfRelativeDimension d (j s ≫ str M) := by
  obtain ⟨ho, hcov, hd⟩ := hj
  have := ho s
  have := proper_str h
  constructor
  · have hcl : IsClosed (Set.range (j s)) := by
      have : Set.range (j s) = (⋃ t ∈ ({s}ᶜ : Set (Fin r)), Set.range (j t))ᶜ := by
        ext x
        simp only [Set.mem_compl_iff, Set.mem_iUnion, not_exists]
        constructor
        · intro hx t hts hxt
          exact Set.disjoint_left.1 (hd s t (Ne.symm hts)) hx hxt
        · intro hx
          obtain ⟨t, ht⟩ := hcov x
          by_cases hts : t = s
          · exact hts ▸ ht
          · exact absurd ht (hx t hts)
      rw [this, isClosed_compl_iff]
      exact isOpen_biUnion fun t _ => (ho t).base_open.isOpen_range
    have : IsClosedImmersion (j s) := .of_isPreimmersion _ hcl
    infer_instance
  · have h1 : SmoothOfRelativeDimension d M.q := hc.2
    have := smoothOfRelativeDimension_isStableUnderBaseChange d
    have h2 : SmoothOfRelativeDimension d (str M) :=
      MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension d) _ _ h1
    have h3 := smoothOfRelativeDimension_comp (n := 0) (m := d) (j s) (str M)
    rwa [zero_add] at h3

theorem unit_of_over {Ω : Type} [Field Ω] [CharZero Ω] {Y : Scheme.{0}} (f : Y ⟶ Spec (CommRingCat.of Ω)) (q : ℕ)
    [NeZero q] : IsUnit (q : Γ(Y, ⊤)) := by
  have h : IsUnit (q : Ω) := (Nat.cast_ne_zero.2 (NeZero.ne q)).isUnit
  simpa using h.map ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv ≫ f.appTop).hom

theorem prim_of_over {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharZero Ω] {Y : Scheme.{0}} (f : Y ⟶ Spec (CommRingCat.of Ω))
    (q : ℕ) [NeZero q] : Nonempty (GlobalTheory.EtC.Prim q Γ(Y, ⊤)) := by
  have hdeg : (Polynomial.cyclotomic q Ω).degree ≠ 0 := (Polynomial.degree_cyclotomic_pos q Ω (NeZero.pos q)).ne'
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root _ hdeg
  have h0 : Polynomial.aeval ζ (Polynomial.cyclotomic q ℤ) = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
    exact hζ
  exact ⟨GlobalTheory.EtC.Prim.map ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv ≫ f.appTop).hom
    ⟨ζ, (Nat.cast_ne_zero.2 (NeZero.ne q)).isUnit, h0⟩⟩

theorem inv_sch (q : ℕ) {Y : Scheme.{0}} (h : IsUnit (q : Γ(Y, ⊤))) : GlobalTheory.EtC.Inv q (GlobalTheory.EtC.sch.obj Y) := by
  intro U ⟨x⟩
  change U ⟶ Y at x
  simpa using h.map x.appTop.hom

end CrystallineSemistableComparison.AdicGeo
end
end

section

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace CrystallineSemistableComparison.AdicCoh

section Cast
variable {q : ℕ} {E : Spc}

theorem cast_cast {n i n' i' n'' i'' : ℤ} (h1 : n = n') (h2 : i = i') (h3 : n' = n'') (h4 : i' = i'') (x : Ht q E n i) :
    (x.cast h1 h2).cast h3 h4 = x.cast (h1.trans h3) (h2.trans h4) := by
  subst h1 h2 h3 h4; rfl

theorem cast_zero {n i n' i' : ℤ} (h1 : n = n') (h2 : i = i') : (0 : Ht q E n i).cast h1 h2 = 0 := by
  subst h1 h2; rfl

theorem cast_add {n i n' i' : ℤ} (h1 : n = n') (h2 : i = i') (x y : Ht q E n i) :
    (x + y).cast h1 h2 = x.cast h1 h2 + y.cast h1 h2 := by
  subst h1 h2; rfl

theorem cast_smul {n i n' i' : ℤ} (h1 : n = n') (h2 : i = i') (c : ℤ) (x : Ht q E n i) :
    (c • x).cast h1 h2 = c • x.cast h1 h2 := by
  subst h1 h2; rfl

theorem cast_nsmul {n i n' i' : ℤ} (h1 : n = n') (h2 : i = i') (c : ℕ) (x : Ht q E n i) :
    (c • x).cast h1 h2 = c • x.cast h1 h2 := by
  subst h1 h2; rfl

theorem cast_eq_zero {n i n' i' : ℤ} (h1 : n = n') (h2 : i = i') (x : Ht q E n i) : x.cast h1 h2 = 0 ↔ x = 0 := by
  subst h1 h2; rfl

def castH {n i n' i' : ℤ} (h1 : n = n') (h2 : i = i') : Ht q E n i →+ Ht q E n' i' where
  toFun x := x.cast h1 h2
  map_zero' := cast_zero h1 h2
  map_add' := cast_add h1 h2

theorem red_cast (Q q' : ℕ) {n i n' i' : ℤ} (h1 : n = n') (h2 : i = i') (x : Ht Q E n i) :
    red Q q' E n' i' (x.cast h1 h2) = (red Q q' E n i x).cast h1 h2 := by
  subst h1 h2; rfl

theorem pull_cast {E' : Spc} (f : E ⟶ E') {n i n' i' : ℤ} (h1 : n = n') (h2 : i = i') (x : Ht q E' n i) :
    pull _ f (tw q i') n' (x.cast h1 h2) = Ht.cast h1 h2 (pull _ f (tw q i) n x) := by
  subst h1 h2; rfl

theorem cup_cast_right {n m i j m' j' : ℤ} (h1 : m = m') (h2 : j = j') (x : Ht q E n i) (y : Ht q E m j) :
    cup q x (y.cast h1 h2) = (cup q x y).cast (by rw [h1]) (by rw [h2]) := by
  subst h1 h2; rfl

theorem cast_heq {n i n' i' : ℤ} (h1 : n = n') (h2 : i = i') (x : Ht q E n i) : HEq (x.cast h1 h2) x := by
  subst h1 h2; rfl

end Cast

variable (l : ℕ) [Fact l.Prime]

theorem neZero_pow (k : ℕ) : NeZero (l ^ k) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩

theorem isSys (hI : ZIn) (X : Scheme.{0}) (hX : IsUnit (l : Γ(X, ⊤))) (n i : ℤ)
    (hfin : ∀ k, Finite (Ht (l ^ k) (sch.obj X) n i)) :
    Adic.IsSys l (fun k => HtL l k (sch.obj X) n i) (fun m m' => red (l ^ m) (l ^ m') (sch.obj X) n i) := by
  refine ⟨fun k r x => HtL.smul_eq l k k le_rfl _ n i r x, ?_, ?_, ?_, hfin⟩
  · intro m x
    have := neZero_pow l m
    exact (hI.a11 (l ^ m) (l ^ m) dvd_rfl (sch.obj X)).2.2.1 n i x
  · intro m m' p x h1 h2
    have := neZero_pow l m
    exact (hI.a11 (l ^ m) (l ^ m') (pow_dvd_pow l h2) (sch.obj X)).2.2.2 (l ^ p) (pow_dvd_pow l h1) n i x
  · exact fun a b z h => hI.bock l a b X hX n i z h

theorem cup_mem (hI : ZIn) (E : Spc) {n m i j n' i' : ℤ} (h1 : n + m = n') (h2 : i + j = i') (x : Hl l E n i) (y : Hl l E m j) :
    (fun k => ((cup (l ^ k) (x.1 k) (y.1 k)).cast h1 h2 : HtL l k E n' i')) ∈ HlSub l E n' i' := by
  intro k
  have := neZero_pow l (k + 1)
  have h := (hI.a11 (l ^ (k + 1)) (l ^ k) (pow_dvd_pow l (Nat.le_succ k)) E).1 (x.1 (k + 1)) (y.1 (k + 1))
  change red _ _ _ _ _ ((cup _ _ _).cast _ _) = (cup _ _ _).cast _ _
  rw [red_cast, h, x.2 k, y.2 k]

variable {l} {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem cup_ex (hI : ZIn) (M : Model l K) {i j : ℕ} (x : M.T i) (y : M.T j) : ∃ z, M.CupT x y z :=
  ⟨⟨_, cup_mem l hI M.spc (by push_cast; rfl) (add_zero 0) x y⟩, fun _ => rfl⟩

variable (l)

theorem sum_inj (hI : ZIn) {X : Scheme.{0}} {r : ℕ} {Y : Fin r → Scheme.{0}} (j : ∀ s, Y s ⟶ X) (hj : IsSum j) (n i : ℤ)
    (x : Hl l (sch.obj X) n i) (h : ∀ s, pullHl l (sch.map (j s)) n i x = 0) : x = 0 := by
  apply Subtype.ext
  funext k
  refine (hI.sum (ZMod (l ^ k)) (tw (l ^ k) i) j hj n).1 (funext fun s => ?_)
  change pull _ _ _ n (x.1 k) = pull _ _ _ n 0
  rw [map_zero]
  exact congrArg (fun z : Hl l (sch.obj (Y s)) n i => z.1 k) (h s)

theorem sum_ext (hI : ZIn) {X : Scheme.{0}} {r : ℕ} {Y : Fin r → Scheme.{0}} (j : ∀ s, Y s ⟶ X) (hj : IsSum j) (n i : ℤ)
    (y : ∀ s, Hl l (sch.obj (Y s)) n i) : ∃ x : Hl l (sch.obj X) n i, ∀ s, pullHl l (sch.map (j s)) n i x = y s := by
  have hb := fun k : ℕ => hI.sum (ZMod (l ^ k)) (tw (l ^ k) i) j hj n
  let xk : ∀ k, HtL l k (sch.obj X) n i := fun k => ((hb k).2 (fun s => (y s).1 k)).choose
  have hxk : ∀ k s, pull _ (sch.map (j s)) _ n (xk k) = (y s).1 k := fun k s =>
    congrFun ((hb k).2 (fun s => (y s).1 k)).choose_spec s
  refine ⟨⟨xk, fun k => ?_⟩, fun s => Subtype.ext (funext fun k => hxk k s)⟩
  refine (hb k).1 (funext fun s => ?_)
  change pull _ _ _ n (red _ _ _ n i (xk (k + 1))) = pull _ _ _ n (xk k)
  rw [pull_red, hxk, hxk]
  exact (y s).2 k

end CrystallineSemistableComparison.AdicCoh
end
end
