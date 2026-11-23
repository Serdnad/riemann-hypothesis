module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle015
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsValLineLogNormAtIffEmbedding
public import Development.WeilBound.CoreStatements.VolumeEquality.CoverRootsSch
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle010
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle032
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptFiniteExtension
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
public import Development.WeilBound.CoreStatements.VolumeEquality.Pieces
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
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

namespace RootFieldNumerics.Rig

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.HodgeExt

theorem exists_rel {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} {t : SAB H X}
    {z : Sp ℂ ⟶ X} {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ] {R : RiemLat E g Λ} {A₀ : Type}
    {x : A₀ → Fin g → ℂ} {v : A₀ → (epsAt z ⟶ t.G)} (h : FibreLatVec t z R x v) {V : Type} [AddCommGroup V] [Module ℂ V]
    (Mz : LieModel t.G z V) : ∃ Rel : Submodule ℂ ((Fin g → ℂ) × V), (∀ a s, v a = Mz.pt s → (x a, s) ∈ Rel) ∧
      (∀ d, (d, 0) ∈ Rel → d = 0) ∧ ∀ s, (0, s) ∈ Rel → s = 0 := by
  obtain ⟨A, _, φ, u, χ, hp, -, -, -, -, hv⟩ := h
  have h1 : lft hp (1 : epsAt z ⟶ t.G) = 1 := by
    have := lft_mul hp (1 : epsAt z ⟶ t.G) 1
    rw [_root_.mul_one] at this
    exact left_eq_mul.1 this
  have h0 : u.IsDiff 0 (lft hp (Mz.pt 0)) := by
    rw [Mz.pt_zero, h1, Hom.one_def]
    exact GlobalTheory.ArchMetricCompare.isDiff_zero u
  have hc : ∀ (c c' : ℂ) (p q : (Fin g → ℂ) × V), u.IsDiff p.1 (lft hp (Mz.pt p.2)) → u.IsDiff q.1 (lft hp (Mz.pt q.2)) →
      u.IsDiff (c • p.1 + c' • q.1) (lft hp (Mz.pt (c • p.2 + c' • q.2))) := fun c c' p q a b => by
    have := HodgePull.isDiff_comb Mz hp u ![p.2, q.2] ![p.1, q.1] (fun l => by fin_cases l; exacts [a, b]) 0 ![c, c']
    simpa [Fin.sum_univ_two] using this
  have ht : ∀ s, IsTangent (lft hp (Mz.pt s)) := fun s => isTangent_lft hp (Mz.tan s)
  refine ⟨{ carrier := {p | u.IsDiff p.1 (lft hp (Mz.pt p.2))}
            add_mem' := fun {p q} a b => by simpa using hc 1 1 p q a b
            zero_mem' := h0
            smul_mem' := fun c p a => by simpa using hc c 0 p p a a }, fun a s e => ?_, fun d hd => ?_, fun s hs => ?_⟩
  · obtain ⟨v', e', hd⟩ := hv a
    show u.IsDiff (x a) (lft hp (Mz.pt s))
    rw [← e, ← lft_unique hp e']
    exact hd
  · exact eq_of_isDiff u (ht 0) hd h0
  · have e := GlobalTheory.ArchMetricCompare.eq_of_isDiff u (ht s) (ht 0) hs h0
    apply Mz.inj
    apply Over.OverMorphism.ext
    rw [← lft_left hp (Mz.pt s), e, lft_left]

section Lin

variable {W V : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup V] [Module ℂ V] {Rel : Submodule ℂ (W × V)} {m : ℕ}

theorem indep_of_rel (h1 : ∀ d, (d, 0) ∈ Rel → d = 0) {x : Fin m → W} {ω : Fin m → V} (h : ∀ i, (x i, ω i) ∈ Rel)
    (hx : LinearIndependent ℂ x) : LinearIndependent ℂ ω := by
  rw [Fintype.linearIndependent_iff] at hx ⊢
  intro c hc
  refine hx c (h1 _ ?_)
  have := Rel.sum_mem (t := Finset.univ) fun i _ => Rel.smul_mem (c i) (h i)
  convert this using 1
  ext
  · simp [Prod.fst_sum]
  · simp [Prod.snd_sum, hc]

theorem mem_flag_of_rel (h2 : ∀ s, (0, s) ∈ Rel → s = 0) {x : Fin m → W} {ω : Fin m → V} (h : ∀ i, (x i, ω i) ∈ Rel)
    {k : ℕ} {d : W} {s : V} (hd : (d, s) ∈ Rel) (hm : d ∈ flagStep ℂ x k) : s ∈ flagStep ℂ ω k := by
  have key : ∀ d ∈ flagStep ℂ x k, ∃ s ∈ flagStep ℂ ω k, (d, s) ∈ Rel := by
    intro d hd
    induction hd using Submodule.span_induction with
    | mem _ hy =>
      obtain ⟨i, hi, rfl⟩ := hy
      exact ⟨ω i, Submodule.subset_span ⟨i, hi, rfl⟩, h i⟩
    | zero => exact ⟨0, Submodule.zero_mem _, Rel.zero_mem⟩
    | add a b _ _ ha hb =>
      obtain ⟨s, hs, ha⟩ := ha
      obtain ⟨s', hs', hb⟩ := hb
      exact ⟨s + s', Submodule.add_mem _ hs hs', Rel.add_mem ha hb⟩
    | smul c a _ ha =>
      obtain ⟨s, hs, ha⟩ := ha
      exact ⟨c • s, Submodule.smul_mem _ c hs, Rel.smul_mem c ha⟩
  obtain ⟨s', hs', hr⟩ := key d hm
  have e : s - s' = 0 := h2 _ (by simpa using Rel.sub_mem hd hr)
  rwa [sub_eq_zero.1 e]

theorem flag_le_of_rel (h2 : ∀ s, (0, s) ∈ Rel → s = 0) {x x' : Fin m → W} {ω ω' : Fin m → V} (h : ∀ i, (x i, ω i) ∈ Rel)
    (h' : ∀ i, (x' i, ω' i) ∈ Rel) {k : ℕ} (e : flagStep ℂ x k = flagStep ℂ x' k) : flagStep ℂ ω' k ≤ flagStep ℂ ω k := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨i, hi, rfl⟩
  exact mem_flag_of_rel h2 h (h' i) (e ▸ Submodule.subset_span ⟨i, hi, rfl⟩)

theorem tri_unique {α ω : Fin m → V} (hα : LinearIndependent ℂ α) {u u' : Fin m → Fin m → ℂ} (h1 : ∀ k, u k k = 1)
    (h0 : ∀ l k, l < k → u l k = 0) (h1' : ∀ k, u' k k = 1) (h0' : ∀ l k, l < k → u' l k = 0)
    (hu : ∀ k : Fin m, ∑ l, u l k • α l ∈ flagStep ℂ ω (k + 1)) (hu' : ∀ k : Fin m, ∑ l, u' l k • α l ∈ flagStep ℂ ω (k + 1)) :
    u = u' := by
  classical
  let ε : Fin m → V := fun k => ∑ l, u l k • α l
  have hco : ∀ (t : Fin m → ℂ) (c : Fin m → ℂ), ∑ i, t i • ε i = ∑ l, c l • α l → ∀ l, ∑ i, t i * u l i = c l := by
    intro t c e
    have e2 : ∑ l, ((∑ i, t i * u l i) - c l) • α l = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib, ← e, ε, Finset.smul_sum, Finset.sum_smul, smul_smul]
      rw [Finset.sum_comm, sub_self]
    exact fun l => sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hα _ e2 l)
  have hlow : ∀ (t : Fin m → ℂ) (l : Fin m), (∀ i, i < l → t i = 0) → ∑ i, t i * u l i = t l := by
    intro t l ht
    rw [Finset.sum_eq_single l, h1, _root_.mul_one]
    · intro i _ hi
      rcases lt_or_gt_of_ne hi with h | h
      · rw [ht i h, zero_mul]
      · rw [h0 l i h, mul_zero]
    · simp
  have hvan : ∀ (t c : Fin m → ℂ) (k : ℕ), (∀ l, ∑ i, t i * u l i = c l) → (∀ l : Fin m, (l : ℕ) < k → c l = 0) →
      ∀ l : Fin m, (l : ℕ) < k → t l = 0 := by
    intro t c k e hc l
    induction l using WellFoundedLT.induction with
    | ind l ih =>
      intro hl
      rw [← hlow t l fun i hi => ih i hi (lt_trans hi hl), e, hc l hl]
  have hε : LinearIndependent ℂ ε := by
    rw [Fintype.linearIndependent_iff]
    intro t ht l
    exact hvan t 0 m (hco t 0 (by simpa using ht)) (fun _ _ => rfl) l l.2
  have hfl : ∀ k : ℕ, flagStep ℂ ε k = flagStep ℂ ω k := fun k => by
    have hle : flagStep ℂ ε k ≤ flagStep ℂ ω k := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨i, hi, rfl⟩
      refine Submodule.span_mono (Set.image_mono fun j hj => ?_) (hu i)
      exact lt_of_lt_of_le (show (j : ℕ) < i + 1 from hj) hi
    haveI : FiniteDimensional ℂ (flagStep ℂ ω k) := FiniteDimensional.span_of_finite ℂ (Set.toFinite _)
    refine Submodule.eq_of_le_of_finrank_le hle ?_
    unfold flagStep
    rw [Set.image_eq_range, Set.image_eq_range]
    exact (finrank_range_le_card _).trans (finrank_span_eq_card (hε.comp _ Subtype.val_injective)).ge
  funext l k
  have hm := hu' k
  rw [← hfl] at hm
  obtain ⟨t, ht, e⟩ := (Finsupp.mem_span_image_iff_linearCombination ℂ).1 hm
  rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp)] at e
  have e1 := hco t _ e
  have e2 := hvan t _ k e1 fun l hl => h0' l k hl
  have e3 : t k = 1 := by rw [← hlow t k fun i hi => e2 i hi, e1, h1']
  rw [← e1 l, Finset.sum_eq_single k, e3, _root_.one_mul]
  · intro i _ hi
    rcases lt_or_gt_of_ne hi with h | h
    · rw [e2 i h, zero_mul]
    · have : t i = 0 := by
        by_contra hne
        have h6 : (i : ℕ) < k + 1 := ht (Finsupp.mem_support_iff.2 hne)
        have h7 : (k : ℕ) < i := h
        omega
      rw [this, zero_mul]
  · simp

end Lin

end RootFieldNumerics.Rig
end
end

section

noncomputable section

namespace RootFieldNumerics.Rig

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.CompanionTheory.Ar SheetDecomposition.CovSch

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X}

def Ev (ξ : Sp Ω ⟶ X) (P : X.Opens → Prop) : Prop := ∃ U : X.Opens, genPt ξ ∈ U ∧ ∀ U' ≤ U, P U'

theorem Ev.mono {P Q : X.Opens → Prop} (h : Ev ξ P) (hPQ : ∀ U, P U → Q U) : Ev ξ Q :=
  let ⟨U, hU, h⟩ := h; ⟨U, hU, fun U' hU' => hPQ _ (h U' hU')⟩

theorem Ev.and {P Q : X.Opens → Prop} (h : Ev ξ P) (h' : Ev ξ Q) : Ev ξ fun U => P U ∧ Q U :=
  let ⟨U, hU, h⟩ := h; let ⟨V, hV, h'⟩ := h'
  ⟨U ⊓ V, ⟨hU, hV⟩, fun W hW => ⟨h W (hW.trans inf_le_left), h' W (hW.trans inf_le_right)⟩⟩

theorem Ev.of_forall {P : X.Opens → Prop} (h : ∀ U, P U) : Ev ξ P := ⟨⊤, trivial, fun U _ => h U⟩

theorem Ev.all {I : Type} [Finite I] {P : I → X.Opens → Prop} (h : ∀ i, Ev ξ (P i)) : Ev ξ fun U => ∀ i, P i U := by
  choose U hU h using h
  refine ⟨⟨⋂ i, (U i : Set X), isOpen_iInter_of_finite fun i => (U i).isOpen⟩, Set.mem_iInter.2 hU, fun W hW i => h i W ?_⟩
  exact fun q hq => Set.mem_iInter.1 (hW hq) i

theorem ev_sec (hξ : IsCptGen ξ) (a : Ω) : ∃ (U : X.Opens) (h : centre ξ ∈ U) (s : Γ(X, U)), val ξ U h s = a := by
  obtain ⟨U, h, -, hT⟩ := exists_open hξ {a} (Set.finite_singleton a) ⊤ trivial
  exact ⟨U, h, hT rfl⟩

theorem ev_reg (hξ : IsCptGen ξ) (a : Ω) : Ev ξ fun U => ∀ q : Cpt ξ, q.1 ∈ U → a ∈ regAt ξ q := by
  obtain ⟨U, h, s, rfl⟩ := ev_sec hξ a
  exact ⟨U, h, fun U' hU' q hq => ⟨_, genMap_germ' q U (hU' hq) h s⟩⟩

variable {L : Type} [AddCommGroup L] [Module Ω L]

theorem ev_span (hξ : IsCptGen ξ) {r : ℕ} (b : Fin r → L) {e : L} (he : e ∈ Submodule.span Ω (Set.range b)) :
    Ev ξ fun U => ∀ q : Cpt ξ, q.1 ∈ U → e ∈ Submodule.span (regAt ξ q) (Set.range b) := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun Ω).1 he
  refine (Ev.all fun i => ev_reg hξ (c i)).mono fun U h q hq => Submodule.sum_mem _ fun i _ => ?_
  exact Submodule.smul_mem (Submodule.span (regAt ξ q) (Set.range b)) (⟨c i, h i q hq⟩ : regAt ξ q)
    (Submodule.subset_span ⟨i, rfl⟩)

theorem ev_frame₀ {Λ : Lat ξ L} {r : ℕ} {V : Submodule Ω L} (h : Λ.IsVB r V) :
    ∃ b : Fin r → L, Submodule.span Ω (Set.range b) = V ∧ LinearIndependent Ω b ∧
      Ev ξ fun U => ∀ q : Cpt ξ, q.1 ∈ U → Λ q = Submodule.span (regAt ξ q) (Set.range b) := by
  obtain ⟨U, hU, b, hb, hf⟩ := h ⟨genPt ξ, specializes_rfl⟩ trivial
  exact ⟨b, hb, (hf _ trivial hU).1, U, hU, fun U' hU' q hq => (hf q trivial (hU' hq)).2⟩

theorem ev_mem (hξ : IsCptGen ξ) {Λ : Lat ξ L} {r : ℕ} {V : Submodule Ω L} (h : Λ.IsVB r V) {e : L} (he : e ∈ V) :
    Ev ξ fun U => ∀ q : Cpt ξ, q.1 ∈ U → e ∈ Λ q := by
  obtain ⟨b, hb, -, hf⟩ := ev_frame₀ h
  exact (hf.and (ev_span hξ b (hb ▸ he))).mono fun U hU q hq => by rw [hU.1 q hq]; exact hU.2 q hq

theorem ev_frame (hξ : IsCptGen ξ) {Λ : Lat ξ L} {r : ℕ} {V : Submodule Ω L} (h : Λ.IsVB r V) {a : Fin r → L}
    (ha : LinearIndependent Ω a) (haV : ∀ i, a i ∈ V) : Ev ξ fun U => ∀ q : Cpt ξ, q.1 ∈ U → Λ.IsFrameAt a q := by
  obtain ⟨b, hb, hbi, hf⟩ := ev_frame₀ h
  have e : Submodule.span Ω (Set.range a) = Submodule.span Ω (Set.range b) := by
    haveI : FiniteDimensional Ω (Submodule.span Ω (Set.range b)) := FiniteDimensional.span_of_finite Ω (Set.finite_range b)
    refine Submodule.eq_of_le_of_finrank_eq (Submodule.span_le.2 ?_) ?_
    · rintro _ ⟨i, rfl⟩
      rw [hb]
      exact haV i
    · rw [finrank_span_eq_card ha, finrank_span_eq_card hbi]
  have h1 := Ev.all fun i => ev_span hξ b (e := a i) (e ▸ Submodule.subset_span ⟨i, rfl⟩)
  have h2 := Ev.all fun i => ev_span hξ a (e := b i) (e.symm ▸ Submodule.subset_span ⟨i, rfl⟩)
  refine (hf.and (h1.and h2)).mono fun U hU q hq => ⟨ha, ?_⟩
  rw [hU.1 q hq]
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
  · rintro _ ⟨i, rfl⟩
    exact hU.2.2 i q hq
  · rintro _ ⟨i, rfl⟩
    exact hU.2.1 i q hq

theorem v_add {z : Sp ℂ ⟶ X} {a b : Ω} {r t : ℂ} (ha : ValAt ξ z a r) (hb : ValAt ξ z b t) : ValAt ξ z (a + b) (r + t) := by
  obtain ⟨h, s, rfl, rfl⟩ := ha
  obtain ⟨_, s', rfl, rfl⟩ := hb
  exact ⟨h, s + s', map_add _ _ _, map_add _ _ _⟩

theorem v_of_reg {z : Sp ℂ ⟶ X} {a : Ω} (h : genPt ξ ⤳ centre z) (ha : a ∈ regAt ξ ⟨centre z, h⟩) : ∃ r, ValAt ξ z a r :=
  let ⟨s, hs⟩ := ha; ⟨_, h, s, hs, rfl⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H} {Xo : Moduli D l}
  {c : Coeff l} {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {S : Finset ℕ} {K : Type} [Fintype K] {J : K → Type}
  [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω} (𝔐 : HodgeCpt Y S y)

theorem f_genPt : 𝔐.f (genPt 𝔐.ξ) = genPt 𝔐.ξ₀ := RegAtDom.map_genPt 𝔐.fn_over

theorem spec_f (z : Sp ℂ ⟶ 𝔐.X) : genPt 𝔐.ξ₀ ⤳ centre (z ≫ 𝔐.f) := by
  have := (𝔐.all (centre z)).map 𝔐.f.continuous
  rw [f_genPt] at this
  exact this

theorem Ev.pull {P : Y.X.Opens → Prop} (h : Ev 𝔐.ξ₀ P) :
    Ev 𝔐.ξ fun U => ∃ U₀, P U₀ ∧ ∀ q ∈ U, 𝔐.f q ∈ U₀ :=
  let ⟨U, hU, h⟩ := h
  ⟨𝔐.f ⁻¹ᵁ U, by show 𝔐.f (genPt 𝔐.ξ) ∈ U; rw [f_genPt]; exact hU, fun U' hU' => ⟨U, h U le_rfl, fun q hq => hU' hq⟩⟩

theorem ev_point (T : Set Ω)
    (hT : letI := 𝔐.fn.toAlgebra; IntermediateField.adjoin 𝔐.Ω₀ T = ⊤) :
    Ev 𝔐.ξ fun U => ∀ z z' : Sp ℂ ⟶ 𝔐.X, centre z ∈ U → centre z' ∈ U → z ≫ 𝔐.f = z' ≫ 𝔐.f →
      (∀ a ∈ T, ∃ r, ValAt 𝔐.ξ z a r ∧ ValAt 𝔐.ξ z' a r) → z = z' := by
  letI := 𝔐.fn.toAlgebra
  have hξ := 𝔐.tie.gen
  let Good : Ω → Prop := fun a => Ev 𝔐.ξ fun U => ∀ z z' : Sp ℂ ⟶ 𝔐.X, centre z ∈ U → centre z' ∈ U → z ≫ 𝔐.f = z' ≫ 𝔐.f →
      (∀ a ∈ T, ∃ r, ValAt 𝔐.ξ z a r ∧ ValAt 𝔐.ξ z' a r) → ∃ r, ValAt 𝔐.ξ z a r ∧ ValAt 𝔐.ξ z' a r
  have hall : ∀ a, Good a := fun a => by
    have ha : a ∈ IntermediateField.adjoin 𝔐.Ω₀ T := by rw [hT]; trivial
    induction ha using IntermediateField.adjoin_induction with
    | mem a ha => exact Ev.of_forall fun U z z' _ _ _ h => h a ha
    | algebraMap a =>
      refine (Ev.pull 𝔐 (ev_reg 𝔐.gen₀ a)).mono ?_
      rintro U ⟨U₀, h, hU⟩ z z' hz hz' e -
      obtain ⟨r, hr⟩ := v_of_reg (spec_f 𝔐 z) (h ⟨_, spec_f 𝔐 z⟩ (hU _ hz))
      exact ⟨r, HodgePull.valAt_pull 𝔐.fn_over (𝔐.all _) hr, HodgePull.valAt_pull 𝔐.fn_over (𝔐.all _) (e ▸ hr)⟩
    | add a b _ _ ha hb =>
      refine (ha.and hb).mono fun U h z z' hz hz' e hv => ?_
      obtain ⟨r, h1, h2⟩ := h.1 z z' hz hz' e hv
      obtain ⟨t, h3, h4⟩ := h.2 z z' hz hz' e hv
      exact ⟨r + t, v_add h1 h3, v_add h2 h4⟩
    | inv a _ ha =>
      by_cases h0 : a = 0
      · subst h0
        rwa [inv_zero]
      refine (ha.and (ev_reg hξ a⁻¹)).mono fun U h z z' hz hz' e hv => ?_
      obtain ⟨r, h1, h2⟩ := h.1 z z' hz hz' e hv
      obtain ⟨t, h3⟩ := v_of_reg (𝔐.all _) (h.2 ⟨_, 𝔐.all _⟩ hz)
      have h4 := CxVal.mul h1 h3
      rw [mul_inv_cancel₀ h0] at h4
      have hr : r ≠ 0 := left_ne_zero_of_mul_eq_one (CxVal.unique h4 (CxVal.one (𝔐.all _)))
      exact ⟨r⁻¹, CxVal.inv h1 hr, CxVal.inv h2 hr⟩
    | mul a b _ _ ha hb =>
      refine (ha.and hb).mono fun U h z z' hz hz' e hv => ?_
      obtain ⟨r, h1, h2⟩ := h.1 z z' hz hz' e hv
      obtain ⟨t, h3, h4⟩ := h.2 z z' hz hz' e hv
      exact ⟨r * t, CxVal.mul h1 h3, CxVal.mul h2 h4⟩
  obtain ⟨c₀, hc⟩ := 𝔐.tie.cover ⟨genPt 𝔐.ξ, specializes_rfl⟩
  have hy : ∀ k, y ⟨k, c₀ k⟩ ≠ 0 := fun k => Finset.prod_ne_zero_iff.1 hc.1 k (Finset.mem_univ k)
  refine (Ev.all fun s : Σ k, J k => hall (y s / y ⟨s.1, c₀ s.1⟩)).mono fun U h z z' hz hz' e hv => ?_
  choose w h1 h2 using fun s => h s z z' hz hz' e hv
  have hw1 : ∀ k, w ⟨k, c₀ k⟩ = 1 := fun k => by
    have := h1 ⟨k, c₀ k⟩
    rw [div_self (hy k)] at this
    exact CxVal.unique this (CxVal.one (𝔐.all _))
  exact SheetDecomposition.pt_unique 𝔐 (coordsAt_of_val c₀ hy h1 hw1) (coordsAt_of_val c₀ hy h2 hw1)

end RootFieldNumerics.Rig
end
end
