module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle001
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle021
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle029
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle007
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle007
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle035
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle090
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle012
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace PositivityTheory.UnitarySelfGeneration

theorem der_coords {B A R : Type} [CommRing B] [CommRing A] [CommRing R] [Nontrivial R] (c : B →+* A) (g : ℕ)
    (hc : c.IsStandardSmoothOfRelativeDimension g) (u : A →+* R) :
    ∃ d : Fin g → A → R, (∀ i a b, d i (a + b) = d i a + d i b) ∧
      (∀ i a b, d i (a * b) = u a * d i b + u b * d i a) ∧ (∀ i b, d i (c b) = 0) ∧
      (∀ e e' : Fin g → R, (∀ a, ∑ i, e i * d i a = ∑ i, e' i * d i a) → e = e') ∧
      ∀ δ : A → R, (∀ a b, δ (a + b) = δ a + δ b) → (∀ a b, δ (a * b) = u a * δ b + u b * δ a) →
        (∀ b, δ (c b) = 0) → ∃ e : Fin g → R, ∀ a, ∑ i, e i * d i a = δ a := by
  classical
  let _ := c.toAlgebra
  let _ := u.toAlgebra
  let _ := (u.comp c).toAlgebra
  have : IsScalarTower B A R := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Algebra.IsStandardSmoothOfRelativeDimension g B A := hc
  have : Algebra.IsStandardSmooth B A := Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth g
  have : Nontrivial A := u.domain_nontrivial
  have hr := Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential (R := B) (S := A) g
  have : Module.Finite A (KaehlerDifferential B A) := inferInstance
  let β : Module.Basis (Fin g) A (KaehlerDifferential B A) :=
    Module.finBasisOfFinrankEq A _ (Module.finrank_eq_of_rank_eq hr)
  have hsm : ∀ (a : A) (r : R), a • r = u a * r := fun a r => Algebra.smul_def a r
  have key : ∀ (e : Fin g → R) (w : KaehlerDifferential B A), ∑ i, e i * u (β.repr w i) = β.constr A e w := by
    intro e w
    rw [Module.Basis.constr_apply_fintype]
    exact Finset.sum_congr rfl fun i _ => by rw [hsm, mul_comm]; rfl
  refine ⟨fun i a => u (β.repr (KaehlerDifferential.D B A a) i), fun i a b => by simp, fun i a b => by simp,
    fun i b => ?_, fun e e' h => ?_, fun δ h1 h2 h3 => ?_⟩
  · have : KaehlerDifferential.D B A (c b) = 0 := Derivation.map_algebraMap _ b
    simp [this]
  · have h' : β.constr A e = β.constr A e' := by
      refine Derivation.liftKaehlerDifferential_unique _ _ (Derivation.ext fun a => ?_)
      simpa [key] using h a
    exact (β.constr A).injective h'
  · let D : Derivation B A R := Derivation.mk'
      { toFun := δ
        map_add' := h1
        map_smul' := fun b a => by
          rw [Algebra.smul_def, h2, RingHom.id_apply, Algebra.smul_def]
          have : δ (algebraMap B A b) = 0 := h3 b
          rw [this, mul_zero, add_zero]; rfl }
      (fun a b => by simpa [hsm] using h2 a b)
    refine ⟨fun i => D.liftKaehlerDifferential (β i), fun a => ?_⟩
    rw [key]
    have : β.constr A (fun i => D.liftKaehlerDifferential (β i)) = D.liftKaehlerDifferential :=
      β.ext fun i => by simp
    rw [this, Derivation.liftKaehlerDifferential_comp_D]
    rfl

theorem lie_free : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (g : ℕ), SmoothOfRelativeDimension g G.hom → ∀ (R : Type) [CommRing R] [IsLocalRing R] (x : Spec (CommRingCat.of R) ⟶ S) (E : Type) [AddCommGroup E] [Module R E] (M : LieModel G x E), Nonempty (Module.Basis (Fin g) R E) := by
  intro S G _ g hG R _ _ x E _ _ M
  let t : Spec (CommRingCat.of R) ⟶ G.left := (1 : Over.mk x ⟶ G).left
  obtain ⟨V, hV, U, hU, hq, hUV, hs⟩ :=
    hG.exists_isStandardSmoothOfRelativeDimension (t (IsLocalRing.closedPoint R))
  have hrange : Set.range t ⊆ Set.range hU.fromSpec := by
    rw [hU.range_fromSpec]
    rintro _ ⟨y, rfl⟩
    exact (IsLocalRing.specializes_closedPoint y).mem_open (t ⁻¹ᵁ U).isOpen hq
  let l := IsOpenImmersion.lift hU.fromSpec t hrange
  have hl : spMap (Spec.preimage l).hom = l := by simp [spMap]
  have h1 : (1 : Over.mk x ⟶ G).left = spMap (Spec.preimage l).hom ≫ hU.fromSpec := by
    rw [hl]; exact (IsOpenImmersion.lift_fac _ _ _).symm
  obtain ⟨d, d1, d2, d3, d4, d5⟩ := der_coords (G.hom.appLE V U hUV).hom g hs (Spec.preimage l).hom
  obtain ⟨M', -⟩ := PositivityTheory.HtPt.Htat.Lie.exists_lieModel (E := Fin g → R) G U V hU hV hUV R x _ h1
    (fun e a => ∑ i, e i * d i a)
    (fun e a b => by simp only [d1, mul_add, Finset.sum_add_distrib])
    (fun e a b => by
      simp only [d2, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring)
    (fun e b => by simp only [d3, mul_zero, Finset.sum_const_zero])
    (fun e e' a => by simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib])
    (fun c e a => by
      simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => mul_assoc _ _ _) d4 d5
  obtain ⟨f, -, -⟩ := GlobalTheory.T.lie_model_existsUnique_equiv S G R x E (Fin g → R) M M'
  exact ⟨Module.Basis.ofEquivFun f⟩

end PositivityTheory.UnitarySelfGeneration
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace PositivityTheory.UnitarySelfGeneration

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {B : Type} [CommRing B] {b : Base l B} {S : Scheme.{0}} {s : S ⟶ Sp B}

theorem tb_eta (o : Obj D l b s) (x e : D.La) : o.eta (x + l.M • e) = o.eta x := by
  have hM : (l.M : 𝓞 E) ∈ l.Mb := by
    have h := Ideal.mem_span_singleton_self (l.M : 𝓞 E)
    rw [← l.prod] at h
    exact Ideal.mul_le_left h
  rw [o.eta_add, o.eta_ker (l.M • e), _root_.mul_one]
  rw [← Nat.cast_smul_eq_nsmul (𝓞 E)]
  exact Submodule.smul_mem_smul hM trivial

theorem tb_etaA (o : Obj D l b s) (x e : D.La) : o.etaA (x + l.A • e) = o.etaA x := by
  rw [o.etaA_add, o.etaA_ker, _root_.mul_one]

theorem tb_map (t : SAB H S) (g g' : HostAut H) (h : ∀ a, g.s (g'.s a) = a) :
    ∃ m : SABMap (twistSAB (twistSAB t g) g') t (𝟙 S), m.φ = 𝟙 t.G.left := by
  obtain ⟨m, hm⟩ := GlobalTheory.T.sab_map_id E H S t
  refine ⟨⟨m.cm, m.cart, m.base, fun a => ?_, m.lin⟩, hm⟩
  have := m.act a
  show (t.act.act (g.s (g'.s a))).left ≫ m.cm.F = _
  rw [h]
  exact this
end

theorem tw_back : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : HostAut H) (a : TwIso D g), ∃ a' : TwIso D g.symm, ∀ (l : Level H) (B : Type) [CommRing B] (b : Base l B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o : Obj D l b s), (∀ (h : TwOK o g a) (h' : TwOK (twistObj o g a h) g.symm a'), Nonempty (ObjMap (twistObj (twistObj o g a h) g.symm a' h') o (𝟙 S))) ∧ ∀ (h : TwOK o g.symm a') (h' : TwOK (twistObj o g.symm a' h) g a), Nonempty (ObjMap (twistObj (twistObj o g.symm a' h) g a h') o (𝟙 S)) := by
  intro E _ _ _ H D g a
  have := D.fin
  have := D.proj
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.T.twisted_module_finite_projective_rank (𝓞 E) g.s D.La
  obtain ⟨f, hf1, hf2⟩ := ProIso.exists_isInv (𝓞 E) D.La (TwMod g.s D.La) D.EF (twForm D g) a
  have k1 : ∀ c, g.s (g.symm.s c) = c := fun c => RingOfIntegers.ext (g.σ.apply_symm_apply c)
  have k2 : ∀ c, g.symm.s (g.s c) = c := fun c => RingOfIntegers.ext (g.σ.symm_apply_apply c)
  let a' : TwIso D g.symm :=
    { a := fun n =>
        { toFun := fun x => f.a n x
          map_add' := fun x y => (f.a n).map_add x y
          map_smul' := fun c x => by
            have e := (f.a n).map_smul (g.symm.s c) x
            refine Eq.trans (congrArg (f.a n) ?_) e
            show c • x = g.s (g.symm.s c) • x
            rw [k1] }
      inj := f.inj
      surj := f.surj
      isom := f.isom
      compat := f.compat }
  refine ⟨a', fun l B _ b S s o => ⟨fun h h' => ?_, fun h h' => ?_⟩⟩
  · have hM : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
    obtain ⟨m, hm⟩ := tb_map o.t g g.symm k1
    refine ⟨⟨m, fun x => ?_, fun x => ?_⟩⟩
    · obtain ⟨e, he⟩ := hf2 l.M hM x
      have : o.eta (a.a l.M (f.a l.M x)) = o.eta x := (congrArg o.eta he).trans (tb_eta o x e)
      exact (congrArg₂ (fun u v => u.left ≫ v) this hm).trans ((Category.comp_id _).trans (Category.id_comp _).symm)
    · obtain ⟨e, he⟩ := hf2 l.A l.A_pos x
      have : o.etaA (a.a l.A (f.a l.A x)) = o.etaA x := (congrArg o.etaA he).trans (tb_etaA o x e)
      exact (congrArg₂ (fun u v => u.left ≫ v) this hm).trans ((Category.comp_id _).trans (Category.id_comp _).symm)
  · have hM : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
    obtain ⟨m, hm⟩ := tb_map o.t g.symm g k2
    refine ⟨⟨m, fun x => ?_, fun x => ?_⟩⟩
    · obtain ⟨e, he⟩ := hf1 l.M hM x
      have : o.eta (f.a l.M (a.a l.M x)) = o.eta x := (congrArg o.eta he).trans (tb_eta o x e)
      exact (congrArg₂ (fun u v => u.left ≫ v) this hm).trans ((Category.comp_id _).trans (Category.id_comp _).symm)
    · obtain ⟨e, he⟩ := hf1 l.A l.A_pos x
      have : o.etaA (f.a l.A (a.a l.A x)) = o.etaA x := (congrArg o.etaA he).trans (tb_etaA o x e)
      exact (congrArg₂ (fun u v => u.left ≫ v) this hm).trans ((Category.comp_id _).trans (Category.id_comp _).symm)

end PositivityTheory.UnitarySelfGeneration
end

section

open MvPolynomial AlgebraicGeometry CategoryTheory NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (IsPullHerm imageZ blockFnField)

namespace PositivityTheory.UnitarySelfGeneration

private theorem sum_shift_mul_neg_indicator_eq_ite (N : ℕ) (m n : Fin N) :
    ∑ k : Fin N, (((if (k:ℕ) + 1 = (m:ℕ) then (1:ℤ) else 0) - if k = m then 1 else 0) * (if n ≤ k then -1 else 0))
      = if n = m then 1 else 0 := by
  have e1 : ∀ k : Fin N, (((if (k:ℕ) + 1 = (m:ℕ) then (1:ℤ) else 0) - if k = m then 1 else 0) * (if n ≤ k then -1 else 0))
      = (if k = m then (if n ≤ k then (1:ℤ) else 0) else 0) - (if (k:ℕ) + 1 = m then (if n ≤ k then (1:ℤ) else 0) else 0) := by
    intro k
    by_cases h1 : (k:ℕ) + 1 = m
    · have : k ≠ m := by intro h; subst h; omega
      split_ifs <;> simp_all
    · split_ifs <;> simp_all
  simp only [e1, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rcases m with ⟨m, hm⟩
  rcases n with ⟨n, hn⟩
  cases m with
  | zero =>
    have : ∀ k : Fin N, ¬ ((k:ℕ) + 1 = 0) := fun k => by omega
    simp only [this, if_false, Finset.sum_const_zero, sub_zero, Fin.le_def, Fin.mk.injEq]
    split_ifs <;> omega
  | succ m =>
    rw [Finset.sum_eq_single ⟨m, by omega⟩]
    · simp only [Fin.le_def, Fin.mk.injEq]
      split_ifs <;> omega
    · intro b _ hb
      have hb' : (b:ℕ) ≠ m := fun h => hb (Fin.ext h)
      have : ¬ ((b:ℕ) + 1 = ((⟨m + 1, hm⟩ : Fin N) : ℕ)) := by simp only [Fin.val_mk]; omega
      rw [if_neg this]
    · simp

theorem h_fundinv : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (r r' : Ψ × Fin N), (∑ a, rootOnFund r a * fundOnRoot a r' = if r = r' then 1 else 0) ∧ (∀ π : Ψ ≃ Ψ, rootOnFund (π r.1, r.2) (π r'.1, r'.2) = rootOnFund r r' ∧ fundOnRoot (π r.1, r.2) (π r'.1, r'.2) = fundOnRoot r r') := by
  intro Ψ _ _ N r r'
  refine ⟨?_, fun π => ?_⟩
  · obtain ⟨p, m⟩ := r
    obtain ⟨q, n⟩ := r'
    rw [Fintype.sum_prod_type]
    simp only [rootOnFund, fundOnRoot]
    rw [Finset.sum_eq_single p (fun b _ hb => by simp [hb]) (by simp)]
    by_cases hq : q = p
    · subst hq
      simp only [if_true, true_and, Prod.mk.injEq]
      rw [sum_shift_mul_neg_indicator_eq_ite N m n]
      by_cases h : n = m
      · simp [h]
      · simp [h, Ne.symm h]
    · have : ¬ (p = q) := fun h => hq h.symm
      simp [hq, this]
  · simp [rootOnFund, fundOnRoot, π.injective.eq_iff]

end PositivityTheory.UnitarySelfGeneration
end
