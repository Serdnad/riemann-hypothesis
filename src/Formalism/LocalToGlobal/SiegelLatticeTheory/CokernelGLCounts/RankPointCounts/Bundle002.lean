module

public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Tactic.Linter.HaveILetI
public import Mathlib.Tactic.Linter.Style
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open scoped ENNReal Classical

namespace Formalism.L2.SG.Pf.StabilizerMassQuotient

variable (Γ : Type*) [Group Γ]

variable {Γ}

theorem card_stab_smul {A : Type*} [MulAction Γ A] (g : Γ) (a : A) :
    Nat.card (MulAction.stabilizer Γ (g • a)) = Nat.card (MulAction.stabilizer Γ a) := by
  refine Nat.card_congr
    { toFun := fun s => ⟨g⁻¹ * (s : Γ) * g, by
        rw [MulAction.mem_stabilizer_iff, mul_smul, mul_smul, MulAction.mem_stabilizer_iff.1 s.2,
          inv_smul_smul]⟩
      invFun := fun t => ⟨g * (t : Γ) * g⁻¹, by
        rw [MulAction.mem_stabilizer_iff, mul_smul, mul_smul, inv_smul_smul,
          MulAction.mem_stabilizer_iff.1 t.2]⟩
      left_inv := fun s => Subtype.ext (by first | simp [mul_assoc] | group)
      right_inv := fun t => Subtype.ext (by first | simp [mul_assoc] | group) }

theorem card_stab_of_orbitRel {A : Type*} [MulAction Γ A] {a a' : A} (h : MulAction.orbitRel Γ A a' a) :
    Nat.card (MulAction.stabilizer Γ a') = Nat.card (MulAction.stabilizer Γ a) := by
  first
  | (obtain ⟨g, rfl⟩ := h; exact card_stab_smul g a)
  | (obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.1 (MulAction.orbitRel_apply.1 h);
      exact card_stab_smul g a)

section Fibre

variable {A B : Type*} [MulAction Γ A] [MulAction Γ B] (f : A → B)
  (hf : ∀ (g : Γ) (a : A), f (g • a) = g • f a)


include hf in
@[reducible] def fibAct (b : B) : MulAction (MulAction.stabilizer Γ b) {a : A // f a = b} where
  smul s a := ⟨(s : Γ) • a.1, by rw [hf, a.2]; exact s.2⟩
  one_smul a := Subtype.ext (one_smul Γ a.1)
  mul_smul s t a := Subtype.ext (mul_smul (s : Γ) (t : Γ) a.1)


include hf in
def qmap : Quotient (MulAction.orbitRel Γ A) → Quotient (MulAction.orbitRel Γ B) :=
  Quotient.map' f fun a a' ⟨g, hg⟩ => ⟨g, by
    have hg' : g • a' = a := hg
    show g • f a' = f a
    rw [← hf, hg']⟩

theorem qmap_mk (a : A) : qmap f hf (Quotient.mk _ a) = Quotient.mk (MulAction.orbitRel Γ B) (f a) := rfl


include hf in
def stabEquiv (b : B) (x : {a : A // f a = b}) :
    (letI := fibAct f hf b; MulAction.stabilizer (MulAction.stabilizer Γ b) x) ≃ MulAction.stabilizer Γ x.1 := by
  letI := fibAct f hf b
  exact
    { toFun := fun s => ⟨(s.1 : Γ), by
        have h := s.2
        rw [MulAction.mem_stabilizer_iff] at h ⊢
        exact congrArg Subtype.val h⟩
      invFun := fun g => ⟨⟨g.1, by
        rw [MulAction.mem_stabilizer_iff]
        have h := MulAction.mem_stabilizer_iff.1 g.2
        have h2 := congrArg f h
        rw [hf, x.2] at h2
        exact h2⟩, by
          rw [MulAction.mem_stabilizer_iff]
          apply Subtype.ext
          exact (MulAction.mem_stabilizer_iff.1 g.2)⟩
      left_inv := fun s => rfl
      right_inv := fun g => rfl }


include hf in
def orbEquiv (oB : Quotient (MulAction.orbitRel Γ B)) :
    (letI := fibAct f hf oB.out; Quotient (MulAction.orbitRel (MulAction.stabilizer Γ oB.out) {a : A // f a = oB.out})) ≃
      ↥(qmap f hf ⁻¹' {oB}) := by
  letI := fibAct f hf oB.out
  refine Equiv.ofBijective (Quotient.lift (fun x => ⟨Quotient.mk _ x.1, ?_⟩) ?_) ⟨?_, ?_⟩
  · show Quotient.mk _ (f x.1) = oB
    rw [x.2]; exact Quotient.out_eq oB
  · rintro x y ⟨s, hs⟩
    apply Subtype.ext
    exact Quotient.sound ⟨(s : Γ), congrArg Subtype.val hs⟩
  · intro X Y hXY
    induction X using Quotient.inductionOn with | h x => ?_
    induction Y using Quotient.inductionOn with | h y => ?_
    have h := congrArg Subtype.val hXY
    obtain ⟨g, hg⟩ := Quotient.exact h
    have hg' : g • y.1 = x.1 := hg
    have hgb : g • oB.out = oB.out := by
      have h2 := congrArg f hg'
      rw [hf, y.2, x.2] at h2
      exact h2
    exact Quotient.sound ⟨⟨g, hgb⟩, Subtype.ext hg'⟩
  · rintro ⟨oA, hoA⟩
    have hoA' : qmap f hf oA = oB := hoA
    have h1 : Quotient.mk (MulAction.orbitRel Γ B) (f oA.out) = Quotient.mk _ oB.out := by
      rw [← qmap_mk f hf, Quotient.out_eq, hoA', Quotient.out_eq]
    obtain ⟨g, hg⟩ := Quotient.exact h1
    have hg' : g • oB.out = f oA.out := hg
    refine ⟨Quotient.mk _ ⟨g⁻¹ • oA.out, by rw [hf, ← hg', inv_smul_smul]⟩, ?_⟩
    apply Subtype.ext
    show Quotient.mk _ (g⁻¹ • oA.out) = oA
    exact (Quotient.sound ⟨g⁻¹, rfl⟩ : Quotient.mk (MulAction.orbitRel Γ A) (g⁻¹ • oA.out) =
      Quotient.mk _ oA.out).trans (Quotient.out_eq oA)

end Fibre

section Sub

variable {Y : Type*} [MulAction Γ Y]

end Sub

section Pair

variable {Y : Type*} [MulAction Γ Y]

end Pair

section Local

variable {T : Type*} [MulAction Γ T]

end Local

end Formalism.L2.SG.Pf.StabilizerMassQuotient
end
end

section

noncomputable section

open MeasureTheory

namespace Formalism.L2.SG.NGCut.SplitEmbedding

private theorem measurePreserving_pi_shear_of_indep {P : Type} [Fintype P]
    {α : P → Type} [∀ p, AddGroup (α p)] [∀ p, MeasurableSpace (α p)] [∀ p, MeasurableAdd₂ (α p)]
    (μ : ∀ p, Measure (α p)) [∀ p, SigmaFinite (μ p)] [∀ p, (μ p).IsAddRightInvariant]
    (S : P → Prop) [DecidablePred S] (d : ∀ p, (∀ q, α q) → α p) (hd : ∀ p, Measurable (d p))
    (hind : ∀ p, S p → ∀ x x' : ∀ q, α q, (∀ q, ¬ S q → x q = x' q) → d p x = d p x') :
    MeasurePreserving (fun g q => if S q then g q + d q g else g q)
      (Measure.pi μ) (Measure.pi μ) := by
  have h1 := measurePreserving_piEquivPiSubtypeProd μ (fun q => ¬ S q)
  set e := MeasurableEquiv.piEquivPiSubtypeProd α (fun q => ¬ S q) with he
  have hfwd : ∀ g : ∀ q, α q, e g = (fun i : {q // ¬ S q} => g i.1, fun i : {q // ¬ ¬ S q} => g i.1) :=
    fun _ => rfl
  have hsymm : ∀ (x : ∀ i : {q // ¬ S q}, α i) (y : ∀ i : {q // ¬ ¬ S q}, α i) (q : P),
      e.symm (x, y) q = if h : ¬ S q then x ⟨q, h⟩ else y ⟨q, h⟩ := fun _ _ _ => rfl
  let v : (∀ i : {q // ¬ S q}, α i) → ∀ i : {q // ¬ ¬ S q}, α i :=
    fun x i => d i.1 (e.symm (x, 0))
  have hvdef : ∀ x i, v x i = d i.1 (e.symm (x, 0)) := fun _ _ => rfl
  have hv : Measurable v := by
    refine Measurable.of_eval (fun i => ?_)
    exact (hd i.1).comp (e.symm.measurable.comp (measurable_id.prodMk measurable_const))
  have hgm : Measurable (Function.uncurry fun (x : ∀ i : {q // ¬ S q}, α i)
      (y : ∀ i : {q // ¬ ¬ S q}, α i) => fun i => y i + v x i) := by
    refine Measurable.of_eval (fun i => ?_)
    exact Measurable.add ((measurable_pi_apply i).comp measurable_snd)
      ((measurable_pi_apply i).comp (hv.comp measurable_fst))
  have hgae : ∀ᵐ x ∂(Measure.pi fun i : {q // ¬ S q} => μ i),
      Measure.map (fun y : ∀ i : {q // ¬ ¬ S q}, α i => fun i => y i + v x i)
        (Measure.pi fun i : {q // ¬ ¬ S q} => μ i) = Measure.pi fun i : {q // ¬ ¬ S q} => μ i :=
    ae_of_all _ fun x =>
      (measurePreserving_pi (hf := fun i => measurePreserving_add_right (μ i.1) (v x i))).map_eq
  have h2 := MeasurePreserving.skew_product (MeasurePreserving.id _) hgm hgae
  have h3 := MeasurePreserving.symm _ h1
  have key : (fun g q => if S q then g q + d q g else g q) =
      (⇑e.symm ∘ (fun z : (∀ i : {q // ¬ S q}, α i) × (∀ i : {q // ¬ ¬ S q}, α i) =>
        (id z.1, fun i => z.2 i + v z.1 i))) ∘ ⇑e := by
    funext g q
    by_cases hq : S q
    · have hd' : d q (e.symm ((fun i : {q // ¬ S q} => g i.1), 0)) = d q g :=
        hind q hq _ _ (fun q' hq' => by simp [hsymm, hq'])
      simp [hfwd, hsymm, hq, hvdef, hd']
    · simp [hfwd, hsymm, hq]
  rw [key]
  exact (h3.comp h2).comp h1

theorem shear_mp : ∀ (n : ℕ) (P : Type) [Fintype P] [DecidableEq P], Fintype.card P = n →
    ∀ (α : P → Type) [∀ p, AddGroup (α p)] [∀ p, MeasurableSpace (α p)] [∀ p, MeasurableAdd₂ (α p)]
      (μ : ∀ p, Measure (α p)) [∀ p, SigmaFinite (μ p)] [∀ p, (μ p).IsAddRightInvariant]
      (h : P → ℕ) (c : ∀ p, (∀ q, α q) → α p), (∀ p, Measurable (c p)) →
      (∀ p (x x' : ∀ q, α q), (∀ q, h q < h p → x q = x' q) → c p x = c p x') →
      MeasurePreserving (fun g p => g p + c p g) (Measure.pi μ) (Measure.pi μ) := by
  intro n P _ _ _ α _ _ _ μ _ _ h c hc hdep
  have hstep : ∀ k : ℕ, MeasurePreserving (fun (g : ∀ q, α q) p => if h p < k then g p + c p g else g p)
      (Measure.pi μ) (Measure.pi μ) := by
    intro k
    induction k with
    | zero =>
      have h0 : (fun (g : ∀ q, α q) p => if h p < 0 then g p + c p g else g p) = id := by
        funext g p
        simp
      rw [h0]
      exact MeasurePreserving.id _
    | succ k ih =>
      have hL := measurePreserving_pi_shear_of_indep μ (fun q => h q = k) c hc
        (fun p hp x x' hx => hdep p x x' (fun q hq => hx q (by omega)))
      have heq : (fun (g : ∀ q, α q) p => if h p < k + 1 then g p + c p g else g p) =
          (fun (g : ∀ q, α q) p => if h p < k then g p + c p g else g p) ∘
            (fun (g : ∀ q, α q) q => if h q = k then g q + c q g else g q) := by
        funext g p
        simp only [Function.comp_apply]
        rcases lt_trichotomy (h p) k with hp | hp | hp
        · have hc' : c p (fun q => if h q = k then g q + c q g else g q) = c p g :=
            hdep p _ _ (fun q hq => by simp [show h q ≠ k by omega])
          simp [hp, show h p < k + 1 by omega, show h p ≠ k by omega, hc']
        · simp [hp]
        · simp [show ¬ h p < k + 1 by omega, show ¬ h p < k by omega, show h p ≠ k by omega]
      rw [heq]
      exact ih.comp hL
  have hfull : (fun (g : ∀ q, α q) p => g p + c p g) =
      (fun (g : ∀ q, α q) p => if h p < Finset.univ.sup h + 1 then g p + c p g else g p) := by
    funext g p
    have hle : h p ≤ Finset.univ.sup h := Finset.le_sup (Finset.mem_univ p)
    simp [show h p < Finset.univ.sup h + 1 by omega]
  rw [hfull]
  exact hstep _

end Formalism.L2.SG.NGCut.SplitEmbedding
end
end

section

noncomputable section

open NumberField

namespace Formalism.L2.SG.NGCut.TorsionTotientBound

variable {E : Type} [Field E] [NumberField E]

theorem two_le_absNorm_prime {P : Ideal (𝓞 E)} (hP : P.IsPrime) (h0 : P ≠ ⊥) : 2 ≤ Ideal.absNorm P := by
  have h1 : Ideal.absNorm P ≠ 1 := by rw [Ne, Ideal.absNorm_eq_one_iff]; exact hP.ne_top
  have h2 : Ideal.absNorm P ≠ 0 := by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact h0
  omega

theorem card_dvd_le_absNorm (M : Ideal (𝓞 E)) (hM : M ≠ ⊥) (D : Finset (Ideal (𝓞 E)))
    (hD : ∀ I ∈ D, I ∣ M) : D.card ≤ Ideal.absNorm M := by
  classical
  have hI0 : ∀ I ∈ D, I ≠ ⊥ := fun I hI h => hM (by obtain ⟨c, hc⟩ := hD I hI; rw [hc, h, Ideal.bot_mul])
  have hinj : Set.InjOn (fun I => UniqueFactorizationMonoid.normalizedFactors I) (D : Set (Ideal (𝓞 E))) := by
    intro I hI J hJ h
    rw [← Ideal.prod_normalizedFactors_eq_self (hI0 I hI), ← Ideal.prod_normalizedFactors_eq_self (hI0 J hJ)]
    exact congrArg Multiset.prod h
  have hsub : D.image (fun I => UniqueFactorizationMonoid.normalizedFactors I) ⊆
      (UniqueFactorizationMonoid.normalizedFactors M).powerset.toFinset := by
    intro s hs
    obtain ⟨I, hI, rfl⟩ := Finset.mem_image.1 hs
    rw [Multiset.mem_toFinset, Multiset.mem_powerset]
    exact (UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors (hI0 I hI) hM).1 (hD I hI)
  have h1 : D.card ≤ 2 ^ Multiset.card (UniqueFactorizationMonoid.normalizedFactors M) := by
    calc D.card = (D.image fun I => UniqueFactorizationMonoid.normalizedFactors I).card :=
          (Finset.card_image_of_injOn hinj).symm
      _ ≤ (UniqueFactorizationMonoid.normalizedFactors M).powerset.toFinset.card := Finset.card_le_card hsub
      _ ≤ Multiset.card (UniqueFactorizationMonoid.normalizedFactors M).powerset := Multiset.toFinset_card_le _
      _ = 2 ^ Multiset.card (UniqueFactorizationMonoid.normalizedFactors M) := Multiset.card_powerset _
  have h2 : 2 ^ Multiset.card (UniqueFactorizationMonoid.normalizedFactors M) ≤ Ideal.absNorm M := by
    have hprod : Ideal.absNorm M =
        ((UniqueFactorizationMonoid.normalizedFactors M).map Ideal.absNorm).prod := by
      conv_lhs => rw [← Ideal.prod_normalizedFactors_eq_self hM]
      exact map_multiset_prod Ideal.absNorm _
    rw [hprod, ← Multiset.card_map Ideal.absNorm]
    refine Multiset.pow_card_le_prod fun n hn => ?_
    obtain ⟨P, hP, rfl⟩ := Multiset.mem_map.1 hn
    have hpr := UniqueFactorizationMonoid.prime_of_normalized_factor P hP
    exact two_le_absNorm_prime (Ideal.isPrime_of_prime hpr) hpr.ne_zero
  exact h1.trans h2

theorem absNorm_map_equiv (σ : 𝓞 E ≃+* 𝓞 E) (I : Ideal (𝓞 E)) :
    Ideal.absNorm (I.map σ) = Ideal.absNorm I := by
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact Nat.card_congr (Ideal.quotientEquiv I (I.map σ) σ rfl).toEquiv.symm

end Formalism.L2.SG.NGCut.TorsionTotientBound
end
end
