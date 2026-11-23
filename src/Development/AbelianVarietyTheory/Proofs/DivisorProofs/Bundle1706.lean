module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle047
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1687
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1689
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle216
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle215
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle183
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1681
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle048
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle043
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DictionaryComponentFrameMarkingUniformisation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1262
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1688
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1662
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1665
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1666
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle002

@[expose] public section

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.centralizer_regular_rationalPoint_finiteAdelic_comm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (γ : UE E n), γ.1.val.charpoly.Separable → ∀ a ∈ twCent (MonoidHom.id (finU (E := E) (n := n))) (finPt γ), ∀ b ∈ twCent (MonoidHom.id (finU (E := E) (n := n))) (finPt γ), a * b = b * a := by
  first | exact @GlobalTheory.BCT.finCent_comm | exact GlobalTheory.BCT.finCent_comm | (intros; apply GlobalTheory.BCT.finCent_comm <;> assumption)
end

section

open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology

namespace GlobalTheory.CxForm.HolAtlas

theorem del_dbar_even_mul (M : Type) [TopologicalSpace M] (n : ℕ) (A : HolAtlas M n) (w : A.Pt → Ev n) (β : A.Fld)
    (hw : A.IsForm (GlobalTheory.LineForm.fld A w)) (hβ : A.IsForm β) :
    A.del (GlobalTheory.LineForm.fld A w * β) = A.del (GlobalTheory.LineForm.fld A w) * β + GlobalTheory.LineForm.fld A w * A.del β ∧
    A.dbar (GlobalTheory.LineForm.fld A w * β) = A.dbar (GlobalTheory.LineForm.fld A w) * β + GlobalTheory.LineForm.fld A w * A.dbar β := by
  have hloc : ∀ i, A.loc (GlobalTheory.LineForm.fld A w * β) i =
      fun v => A.loc (GlobalTheory.LineForm.fld A w) i v * A.loc β i v := by
    intro i
    funext v
    unfold HolAtlas.loc
    split_ifs
    · rfl
    · simp
  have hd : ∀ α : A.Fld, A.IsForm α → ∀ (x : A.Pt) (S),
      DifferentiableAt ℝ (fun v => (bas n).repr (A.loc α x.1.1 v) S) x.crd := fun α hα x S =>
    ((hα.smooth x.1.1 S).contDiffAt ((A.e x.1.1).open_target.mem_nhds (x.ch.map_source x.2))).differentiableAt (by simp)
  have key := fun x : A.Pt => GlobalTheory.T.delOperatorAt_dbarOperatorAt_leibniz_of_commute n (A.loc (GlobalTheory.LineForm.fld A w) x.1.1) (A.loc β x.1.1) x.crd
    (GlobalTheory.LineForm.fld A w x) (hd _ hw x) (hd _ hβ x)
  have hc : ∀ (x : A.Pt) (b : Alt n), b * A.loc (GlobalTheory.LineForm.fld A w) x.1.1 x.crd = GlobalTheory.LineForm.fld A w x * b := by
    intro x b
    rw [A.loc_crd]
    exact Subalgebra.mem_center_iff.1 (w x).2 b
  constructor
  · funext x
    have := (key x).1 fun a => hc x _
    rw [A.loc_crd β x] at this
    simp only [HolAtlas.del, Pi.add_apply, Pi.mul_apply, hloc]
    exact this
  · funext x
    have := (key x).2 fun a => hc x _
    rw [A.loc_crd β x] at this
    simp only [HolAtlas.dbar, Pi.add_apply, Pi.mul_apply, hloc]
    exact this

end GlobalTheory.CxForm.HolAtlas
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.Unfold

theorem lhs_eq {P : Type} [Group P] [TopologicalSpace P] (KP : Subgroup P) (δ : P) (F : P → ℂ)
    (hF : ∀ k ∈ KP, ∀ x, F (k⁻¹ * x * k) = F x) :
    twOrb (MonoidHom.id P) KP δ F = ∑ᶠ d : DoubleCoset.Quotient (twCent (MonoidHom.id P) δ : Set P) (KP : Set P),
      (((twCent (MonoidHom.id P) δ ⊓ KP.map (MulAut.conj (Quotient.out d)).toMonoidHom).relIndex
        (cptPart (twCent (MonoidHom.id P) δ)) : ℕ) : ℂ) * F ((Quotient.out d)⁻¹ * δ * Quotient.out d) := by
  unfold twOrb
  refine finsum_congr fun d => ?_
  congr 1
  have h : (fun k : KP => F ((Quotient.out d * k)⁻¹ * δ * (MonoidHom.id P) (Quotient.out d * k))) =
      fun _ => F ((Quotient.out d)⁻¹ * δ * Quotient.out d) := by
    funext k
    rw [MonoidHom.id_apply, ← hF k k.2 ((Quotient.out d)⁻¹ * δ * Quotient.out d)]
    congr 1
    group
  rw [h, GlobalTheory.IwRed.avg_const]

theorem hint_eq {P N : Type} [Group P] [Group N] (u : N →* P) (KP : Subgroup P) (L : Subgroup N)
    (huK : ∀ X, u X ∈ KP ↔ X ∈ L) (F : P → ℂ) (hF : ∀ k ∈ KP, ∀ x, F (k⁻¹ * x * k) = F x) (y : P) :
    hint L (fun X => F ((u X)⁻¹ * y * u X)) = ∑ᶠ x : N ⧸ L, F ((u (Quotient.out x))⁻¹ * y * u (Quotient.out x)) := by
  have hL : L ≤ rStab (fun X => F ((u X)⁻¹ * y * u X)) := by
    intro l hl x
    show F ((u (x * l))⁻¹ * y * u (x * l)) = F ((u x)⁻¹ * y * u x)
    rw [← hF (u l) ((huK l).2 hl) ((u x)⁻¹ * y * u x)]
    congr 1
    simp only [map_mul]
    group
  have he : rStab (fun X => F ((u X)⁻¹ * y * u X)) ⊓ L = L := inf_eq_right.2 hL
  unfold hint
  rw [he, Subgroup.relIndex_self]
  simp

end GlobalTheory.Unfold

noncomputable section
namespace GlobalTheory.Unfold

theorem rhs_eq (P M N : Type) [Group P] [Group M] [Group N] [TopologicalSpace M] (s : M →* P) (π : P →* M)
    (u : N →* P) (hs : ∀ m, π (s m) = m) (hinj : Function.Injective u) (hker : ∀ p, π p = 1 ↔ ∃ X, u X = p)
    (KP : Subgroup P) (KM : Subgroup M) (L : Subgroup N) (hsK : ∀ k ∈ KM, s k ∈ KP) (hπK : ∀ k ∈ KP, π k ∈ KM)
    (huK : ∀ X, u X ∈ KP ↔ X ∈ L) (γ : M) (F : P → ℂ) (hF : ∀ k ∈ KP, ∀ x, F (k⁻¹ * x * k) = F x) :
    twOrb (MonoidHom.id M) KM γ (fun m' => hint L (fun X => F ((u X)⁻¹ * s m' * u X))) =
      ∑ᶠ q : DoubleCoset.Quotient (twCent (MonoidHom.id M) γ : Set M) (KM : Set M),
        (((twCent (MonoidHom.id M) γ ⊓ KM.map (MulAut.conj (Quotient.out q)).toMonoidHom).relIndex
          (cptPart (twCent (MonoidHom.id M) γ)) : ℕ) : ℂ) *
        ∑ᶠ x : N ⧸ L, F ((s (Quotient.out q) * u (Quotient.out x))⁻¹ * s γ * (s (Quotient.out q) * u (Quotient.out x))) := by
  unfold twOrb
  refine finsum_congr fun q => ?_
  congr 1
  have h : (fun k : KM => hint L (fun X => F ((u X)⁻¹ * s ((Quotient.out q * k)⁻¹ * γ *
      (MonoidHom.id M) (Quotient.out q * k)) * u X))) = fun _ =>
      ∑ᶠ x : N ⧸ L, F ((s (Quotient.out q) * u (Quotient.out x))⁻¹ * s γ * (s (Quotient.out q) * u (Quotient.out x))) := by
    funext k
    rw [hint_eq u KP L huK F hF]
    have e : s ((Quotient.out q * k)⁻¹ * γ * (MonoidHom.id M) (Quotient.out q * k)) =
        (s k)⁻¹ * s ((Quotient.out q)⁻¹ * γ * Quotient.out q) * s k := by
      simp only [MonoidHom.id_apply, map_mul, map_inv]
      group
    rw [e, GlobalTheory.T.unfold_sum_invariant_levi_conj P M N s π u hs hinj hker KP KM L hsK hπK huK F hF k k.2]
    refine finsum_congr fun x => ?_
    congr 1
    simp only [map_mul, map_inv]
    group
  rw [h, GlobalTheory.IwRed.avg_const]

theorem core : ∀ (P M N : Type) [Group P] [Group M] [Group N] (s : M →* P) (π : P →* M) (u : N →* P), (∀ m, π (s m) = m) → Function.Injective u → (∀ p, π p = 1 ↔ ∃ X, u X = p) → ∀ (KP : Subgroup P) (KM : Subgroup M) (L : Subgroup N), (∀ k ∈ KM, s k ∈ KP) → (∀ k ∈ KP, π k ∈ KM) → (∀ X, u X ∈ KP ↔ X ∈ L) → ∀ (TM CM : Subgroup M) (TP CP : Subgroup P), CM ≤ TM → (∀ p, p ∈ TP ↔ ∃ t ∈ TM, s t = p) → (∀ p, p ∈ CP ↔ ∃ t ∈ CM, s t = p) → (∀ q : M, TM ⊓ KM.map (MulAut.conj q).toMonoidHom ≤ CM) → ∀ G : P → ℂ, (∀ t ∈ TP, ∀ p, G (t * p) = G p) → (∀ k ∈ KP, ∀ p, G (p * k) = G p) →
    (∀ X : N, ∃ U : Subgroup M, U ≤ KM ∧ U.relIndex KM ≠ 0 ∧ ∀ k ∈ U, (u X)⁻¹ * s k * u X ∈ KP) →
    {d : DoubleCoset.Quotient (TP : Set P) (KP : Set P) | G (Quotient.out d) ≠ 0}.Finite →
    ∑ᶠ d : DoubleCoset.Quotient (TP : Set P) (KP : Set P),
      (((TP ⊓ KP.map (MulAut.conj (Quotient.out d)).toMonoidHom).relIndex CP : ℕ) : ℂ) * G (Quotient.out d) =
    ∑ᶠ q : DoubleCoset.Quotient (TM : Set M) (KM : Set M),
      (((TM ⊓ KM.map (MulAut.conj (Quotient.out q)).toMonoidHom).relIndex CM : ℕ) : ℂ) *
        ∑ᶠ x : N ⧸ L, G (s (Quotient.out q) * u (Quotient.out x)) := by
  intro P M N _ _ _ s π u hs hinj hker KP KM L hsK hπK huK TM CM TP CP hCT hTP hCP hTC G hGT hGK hU hfin
  have hGout : ∀ p, G (Quotient.out (DoubleCoset.mk TP KP p)) = G p := by
    intro p
    obtain ⟨t, ht, k, hk, he⟩ := (@DoubleCoset.eq _ _ _ _ _ _).1 (DoubleCoset.out_eq' (DoubleCoset.mk TP KP p)).symm
    rw [he, hGK k hk, hGT t ht]
  have hTCP : ∀ p : P, TP ⊓ KP.map (MulAut.conj p).toMonoidHom ≤ CP := by
    intro p x hx
    obtain ⟨hxT, hxK⟩ := Subgroup.mem_inf.1 hx
    obtain ⟨t, ht, rfl⟩ := (hTP x).1 hxT
    refine (hCP _).2 ⟨t, hTC (π p) (Subgroup.mem_inf.2 ⟨ht, ?_⟩), rfl⟩
    obtain ⟨k, hk, hke⟩ := Subgroup.mem_map.1 hxK
    refine Subgroup.mem_map.2 ⟨π k, hπK k hk, ?_⟩
    have := congrArg π hke
    simpa [MulAut.conj_apply, hs] using this
  let ρ : DoubleCoset.Quotient (TP : Set P) (KP : Set P) → DoubleCoset.Quotient (TM : Set M) (KM : Set M) :=
    fun d => DoubleCoset.mk TM KM (π (Quotient.out d))
  have hρmk : ∀ p, ρ (DoubleCoset.mk TP KP p) = DoubleCoset.mk TM KM (π p) := by
    intro p
    obtain ⟨t, ht, k, hk, he⟩ := (@DoubleCoset.eq _ _ _ _ _ _).1 (DoubleCoset.out_eq' (DoubleCoset.mk TP KP p)).symm
    show DoubleCoset.mk TM KM (π (Quotient.out (DoubleCoset.mk TP KP p))) = _
    rw [he, DoubleCoset.eq]
    obtain ⟨t', ht', rfl⟩ := (hTP t).1 ht
    refine ⟨t'⁻¹, TM.inv_mem ht', (π k)⁻¹, KM.inv_mem (hπK k hk), ?_⟩
    simp only [map_mul, hs]
    group
  have hsupp : (Function.support fun d : DoubleCoset.Quotient (TP : Set P) (KP : Set P) =>
      (((TP ⊓ KP.map (MulAut.conj (Quotient.out d)).toMonoidHom).relIndex CP : ℕ) : ℂ) * G (Quotient.out d)).Finite :=
    hfin.subset fun d hd => right_ne_zero_of_mul hd
  rw [GlobalTheory.T.finsum_fiberwise_of_finite_support_complex ρ _ hsupp]
  refine finsum_congr fun q => ?_
  set q0 := Quotient.out q with hq0def
  have hq0 : DoubleCoset.mk TM KM q0 = q := DoubleCoset.out_eq' q
  have hψ : ∀ x : N ⧸ L, ρ (DoubleCoset.mk TP KP (s q0 * u (Quotient.out x))) = q := fun x => by
    rw [hρmk, map_mul, hs, (hker _).2 ⟨_, rfl⟩, mul_one]
    exact hq0
  let ψ : N ⧸ L → {d // ρ d = q} := fun x => ⟨DoubleCoset.mk TP KP (s q0 * u (Quotient.out x)), hψ x⟩
  have hfib : ∀ d : {d // ρ d = q}, ∃ X : N, DoubleCoset.mk TP KP (s q0 * u X) = d.1 ∧
      Nat.card (ψ ⁻¹' {d}) = (TM.map (MulAut.conj q0⁻¹).toMonoidHom ⊓ KM ⊓ KP.comap ((MulAut.conj (u X)⁻¹).toMonoidHom.comp s)).relIndex (TM.map (MulAut.conj q0⁻¹).toMonoidHom ⊓ KM) := by
    intro d
    obtain ⟨X, hX⟩ := GlobalTheory.T.doubleCoset_semidirect_rep_surjective P M N s π u hs hinj hker KP KM L hsK hπK huK TM CM TP CP hCT hTP hCP hTC d.1
    have e : Quotient.out (DoubleCoset.mk TM KM (π (Quotient.out d.1))) = q0 := by
      rw [show DoubleCoset.mk TM KM (π (Quotient.out d.1)) = q from d.2]
    rw [e] at hX
    refine ⟨X, hX, ?_⟩
    rw [← GlobalTheory.T.orbit_count_parabolic_unfold_levi P M N s π u hs hinj hker KP KM L hsK hπK huK TM CM TP CP hCT hTP hCP hTC q0 X]
    apply Nat.card_congr
    refine Equiv.subtypeEquivRight fun x => ?_
    rw [Set.mem_preimage, Set.mem_singleton_iff, Subtype.ext_iff, hX]
  have hwt : ∀ d : {d // ρ d = q},
      (((TP ⊓ KP.map (MulAut.conj (Quotient.out d.1)).toMonoidHom).relIndex CP : ℕ) : ℂ) =
      (((TM ⊓ KM.map (MulAut.conj q0).toMonoidHom).relIndex CM : ℕ) : ℂ) * (Nat.card (ψ ⁻¹' {d}) : ℂ) := by
    intro d
    obtain ⟨X, hX, hc⟩ := hfib d
    obtain ⟨t, ht, k, hk, he⟩ := (@DoubleCoset.eq _ _ _ _ _ _).1 (hX.trans (DoubleCoset.out_eq' d.1).symm)
    rw [he, GlobalTheory.T.doubleCoset_relIndex_inf_conj_const P TP CP KP hTCP t ht k hk,
      GlobalTheory.T.relIndex_unfold_semidirect_product P M N s π u hs hinj hker KP KM L hsK hπK huK TM CM TP CP hCT hTP hCP hTC q0 X, hc]
    push_cast
    rfl
  have hR : ∑ᶠ x : N ⧸ L, G (s q0 * u (Quotient.out x)) =
      ∑ᶠ d : {d // ρ d = q}, (Nat.card (ψ ⁻¹' {d}) : ℂ) * G (Quotient.out d.1) := by
    rw [← GlobalTheory.finsum_comp_eq_finsum_natCard_fiber_mul ψ (fun d => G (Quotient.out d.1)) (Or.inl ?_)]
    · exact finsum_congr fun x => (hGout _).symm
    · intro d _
      obtain ⟨X, -, hc⟩ := hfib d
      have h0 := GlobalTheory.T.stabilizer_relIndex_ne_zero_parabolic P M N s π u hs hinj hker KP KM L hsK hπK huK TM hU q0 X
      rw [← hc] at h0
      haveI := Nat.finite_of_card_ne_zero h0
      exact Set.toFinite _
  rw [hR, mul_finsum]
  refine finsum_congr fun d => ?_
  rw [hwt d, mul_assoc]

theorem twOrb_unfold : ∀ (P M N : Type) [Group P] [Group M] [Group N] [TopologicalSpace P] [TopologicalSpace M] (s : M →* P) (π : P →* M) (u : N →* P), (∀ m, π (s m) = m) → Function.Injective u → (∀ p, π p = 1 ↔ ∃ X, u X = p) → ∀ (KP : Subgroup P) (KM : Subgroup M) (L : Subgroup N), (∀ k ∈ KM, s k ∈ KP) → (∀ k ∈ KP, π k ∈ KM) → (∀ X, u X ∈ KP ↔ X ∈ L) → ∀ γ : M, (∀ p, p ∈ twCent (MonoidHom.id P) (s γ) ↔ ∃ t ∈ twCent (MonoidHom.id M) γ, s t = p) → (∀ p, p ∈ cptPart (twCent (MonoidHom.id P) (s γ)) ↔ ∃ t ∈ cptPart (twCent (MonoidHom.id M) γ), s t = p) → (∀ q : M, twCent (MonoidHom.id M) γ ⊓ KM.map (MulAut.conj q).toMonoidHom ≤ cptPart (twCent (MonoidHom.id M) γ)) → (∀ X : N, ∃ U : Subgroup M, U ≤ KM ∧ U.relIndex KM ≠ 0 ∧ ∀ k ∈ U, (u X)⁻¹ * s k * u X ∈ KP) → ∀ F : P → ℂ, (∀ k ∈ KP, ∀ x, F (k⁻¹ * x * k) = F x) → {d : DoubleCoset.Quotient (twCent (MonoidHom.id P) (s γ) : Set P) (KP : Set P) | F ((Quotient.out d)⁻¹ * s γ * Quotient.out d) ≠ 0}.Finite → twOrb (MonoidHom.id P) KP (s γ) F = twOrb (MonoidHom.id M) KM γ (fun m' => hint L (fun X => F ((u X)⁻¹ * s m' * u X))) := by
  intro P M N _ _ _ _ _ s π u hs hinj hker KP KM L hsK hπK huK γ hTP hCP hTC hU F hF hfin
  rw [lhs_eq KP (s γ) F hF, rhs_eq P M N s π u hs hinj hker KP KM L hsK hπK huK γ F hF]
  refine core P M N s π u hs hinj hker KP KM L hsK hπK huK (twCent (MonoidHom.id M) γ)
    (cptPart (twCent (MonoidHom.id M) γ)) (twCent (MonoidHom.id P) (s γ)) (cptPart (twCent (MonoidHom.id P) (s γ)))
    ((Subgroup.closure_le _).2 fun t ht => ht.1) hTP hCP hTC (fun p => F (p⁻¹ * s γ * p)) ?_ ?_ hU hfin
  · intro t ht p
    have ht' : t * s γ = s γ * t := ht
    show F ((t * p)⁻¹ * s γ * (t * p)) = F (p⁻¹ * s γ * p)
    rw [show (t * p)⁻¹ * s γ * (t * p) = p⁻¹ * (t⁻¹ * (s γ * t)) * p by group, ← ht', inv_mul_cancel_left]
  · intro k hk p
    show F ((p * k)⁻¹ * s γ * (p * k)) = F (p⁻¹ * s γ * p)
    rw [← hF k hk (p⁻¹ * s γ * p)]
    congr 1
    group

end GlobalTheory.Unfold
end
end
end

section

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.dictionary_component_frame_marking_uniformisation : ∀ (D : D7) (H : Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → 1 ≤ r → l.A = 1 → ∀ (θ : InfFam D) (W : HSp D) (hr : W.rank = r) (dict : GA D W → Σ k, Frame (U.X k).Ψ r) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E)) (g : ℕ) (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ) (th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ), IsInfFam θ → (∀ k, IsMod W hr (U.X k)) → (∀ k, IsOrthogonalFrame (U.X k) x₀) → (∀ k τ, IsInfEmb τ.1 (th k τ)) → DictLat U W hr dict ι e F ik φ th x₀ → ∀ (Wt : UW (Formalism.L2.PjFree.Unf.ofPj U)) (h : GA D W), IsONFr (U.X (dict h).1) (dict h).2 ∧ ∃ γ, AtComp θ W hr U.X dict x₀ h γ ∧ MarkAd l W hr ι (γ * h) (Wt.mark (dict h).1) ∧ ∀ γ', AtComp θ W hr U.X dict x₀ h γ' → γ' = γ := by
  first | exact @GlobalTheory.AdTh.dict_atComp_markAd | exact GlobalTheory.AdTh.dict_atComp_markAd | (intros; apply GlobalTheory.AdTh.dict_atComp_markAd <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

set_option autoImplicit false

namespace GlobalTheory.ChernCalc.HoloPull

noncomputable def subst {n n' : ℕ} (L : V n' →L[ℂ] V n) :
    MvPolynomial (Fin n × Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin n' × Fin n') ℂ :=
  aeval fun x : Fin n × Fin n => ∑ c, ∑ d, C (L (coordVec c) x.1 * (starRingEnd ℂ) (L (coordVec d) x.2)) *
    (X (c, d) : MvPolynomial (Fin n' × Fin n') ℂ)

variable {n n' : ℕ} {r : Type} [Fintype r] [DecidableEq r] {G : V n → Matrix r r ℂ} {φ : V n' → V n} {w : V n'}

theorem curvPoly_comp (hφ : ContDiffAt ℂ 2 φ w) (hG : MContDiffAt ∞ G (φ w)) (hu : IsUnit (G (φ w)).det) :
    curvPoly (fun x => G (φ x)) w = (subst (fderiv ℂ φ w)).mapMatrix (curvPoly G (φ w)) := by
  first
  | exact @_root_.GlobalTheory.CurvatureSesquilinearExpansion.curvPoly_pullback
  | exact _root_.GlobalTheory.CurvatureSesquilinearExpansion.curvPoly_pullback
  | (apply _root_.GlobalTheory.CurvatureSesquilinearExpansion.curvPoly_pullback <;> assumption)
  | (intros; apply _root_.GlobalTheory.CurvatureSesquilinearExpansion.curvPoly_pullback <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CurvatureSesquilinearExpansion.curvPoly_pullback <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CurvatureSesquilinearExpansion.curvPoly_pullback ..)

theorem curvEv_eq (G : V n → Matrix r r ℂ) (v : V n) :
    curvEv G v = (aeval sym : MvPolynomial (Fin n × Fin n) ℂ →ₐ[ℂ] Ev n).mapMatrix (curvPoly G v) := rfl

theorem charpolyRev_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (M : Matrix r r R) :
    Matrix.charpolyRev (M.map f) = (Matrix.charpolyRev M).map f := by
  rw [Matrix.charpolyRev, Matrix.charpolyRev, ← Polynomial.coe_mapRingHom, RingHom.map_det]
  congr 1
  ext1 i j
  by_cases h : i = j <;> simp [h, Matrix.one_apply]

end GlobalTheory.ChernCalc.HoloPull

namespace GlobalTheory.ChernCalc


open HoloPull in
theorem curv_pow_chern_comp_holo : ∀ (n n' : ℕ) (r : Type) [Fintype r] [DecidableEq r] (G : V n → Matrix r r ℂ) (φ : V n' → V n) (w : V n'), ContDiffAt ℂ 2 φ w → MContDiffAt ∞ G (φ w) → IsUnit (G (φ w)).det → (∀ k l i j, ∀ G' : V n → Matrix r r ℂ, MContDiffAt ∞ G' (φ w) → IsUnit (G' (φ w)).det → ((curvEv (fun x => G (φ x)) w ^ k * curvEv (fun x => G' (φ x)) w ^ l) i j : Alt n') = pull (fderiv ℂ φ w) ((curvEv G (φ w) ^ k * curvEv G' (φ w) ^ l) i j : Alt n)) ∧ ∀ k, (powAt (fun x => G (φ x)) w k : Alt n') = pull (fderiv ℂ φ w) (powAt G (φ w) k) ∧ (chernAt (fun x => G (φ x)) w k : Alt n') = pull (fderiv ℂ φ w) (chernAt G (φ w) k) := by
  intro n n' r _ _ G φ w hφ hG hu
  have key : ∀ k l i j, ∀ G' : V n → Matrix r r ℂ, MContDiffAt ∞ G' (φ w) → IsUnit (G' (φ w)).det →
      ((curvEv (fun x => G (φ x)) w ^ k * curvEv (fun x => G' (φ x)) w ^ l) i j : Alt n') =
        pull (fderiv ℂ φ w) ((curvEv G (φ w) ^ k * curvEv G' (φ w) ^ l) i j : Alt n) := by
    intro k l i j G' hG' hu'
    simp only [curvEv_eq, curvPoly_comp hφ hG hu, curvPoly_comp hφ hG' hu', ← map_pow, ← map_mul]
    simp only [AlgHom.mapMatrix_apply, Matrix.map_apply]
    exact (pull_aeval_sym _ _ _ _).symm
  refine ⟨key, fun k => ⟨?_, ?_⟩⟩
  · have := fun i => key k 0 i i G hG hu
    simp only [pow_zero, mul_one] at this

    simp only [powAt, Matrix.trace, Matrix.diag_apply, AddSubmonoidClass.coe_finsetSum, map_sum, this]
  · have e : chernPoly (fun x => G (φ x)) w k = subst (fderiv ℂ φ w) (chernPoly G (φ w) k) := by
      rw [chernPoly, chernPoly, curvPoly_comp hφ hG hu, ← map_neg]
      exact (congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p k)
        (charpolyRev_map (subst (fderiv ℂ φ w)).toRingHom _)).trans (Polynomial.coeff_map _ _)
    rw [chernAt, chernAt, e, Subalgebra.coe_smul, Subalgebra.coe_smul, map_smul, pull_aeval_sym]
    rfl

end GlobalTheory.ChernCalc
end

section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

theorem _root_.GlobalTheory.T.varietyComplexPointsMap_isHolomorphic : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X Y : Var F) (f : Y.X ⟶ X.X) (hf : f ≫ X.str = Y.str), (atlas X σ).IsHolo (atlas Y σ) (ptMap σ f hf) := by
  first | exact @GlobalTheory.ChernCalc.ptMap_isHolo | exact GlobalTheory.ChernCalc.ptMap_isHolo | (intros; apply GlobalTheory.ChernCalc.ptMap_isHolo <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory

theorem _root_.GlobalTheory.T.kawamataViehweg_vanishing_numberField_twist : Quoted → ∀ (K : Type) [Field K] [NumberField K] (G : Geo K), IsNef K G.LA → IsBig K G.LA → VanishFrom G.L (GlobalTheory.LB.toMod (tens G.K.bundle G.LA)) 0 := by
  first | exact @GlobalTheory.HSCore.VanishNumberField.vanishFrom_adj | exact GlobalTheory.HSCore.VanishNumberField.vanishFrom_adj | (intros; apply GlobalTheory.HSCore.VanishNumberField.vanishFrom_adj <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory

theorem _root_.GlobalTheory.T.exists_basis_regular_sequence_of_common_zeros : ∀ (K : Type) [Field K] [NumberField K] (G : Geo K) (s : Fin G.D → Fin G.N → K), G.IsGood s → ∀ B : LB G.Y, B.IsLB → ∃ g : Matrix (Fin G.D) (Fin G.D) K, IsUnit g.det ∧ RegSeq G.isLB (GlobalTheory.LB.toMod B) (List.ofFn fun i => G.comb (∑ j, g i j • s j)) := by
  first | exact @GlobalTheory.RegBasis.exists_regular_basis | exact GlobalTheory.RegBasis.exists_regular_basis | (intros; apply GlobalTheory.RegBasis.exists_regular_basis <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory

theorem _root_.GlobalTheory.T.exists_global_combination_of_local_regular_ideal : ∀ (k : Type) [Field k] (Y : Scheme.{0}) [Algebra k Γ(Y, ⊤)], IsProjOver (GlobalTheory.strHom k (X := Y)) → ∀ (L : LB Y) (hL : L.IsLB) (n : ℕ) (t : Fin n → L.Sec) (F : Y.Modules) [IsFiniteQC F] (j₀ l : ℤ), RegSeq hL F (List.ofFn t) → VanishFrom L F j₀ → j₀ + n ≤ l + 1 → ∀ f : Γ(GlobalTheory.twistZ F L (l + 1), ⊤), (∀ y : Y, ∃ (W : Y.Opens) (_ : y ∈ W) (m : Fin n → Γ(GlobalTheory.twistZ F L l, W)), (GlobalTheory.twistZ F L (l + 1)).presheaf.map (homOfLE le_top).op f = ∑ i, (GlobalTheory.Twist.mulSecOfEq F (GlobalTheory.Twist.zofSec (t i)) rfl).app W (m i)) → ∃ m : Fin n → Γ(GlobalTheory.twistZ F L l, ⊤), f = ∑ i, (GlobalTheory.Twist.mulSecOfEq F (GlobalTheory.Twist.zofSec (t i)) rfl).app ⊤ (m i) := by
  first | exact @GlobalTheory.HSCore.exists_global_of_regSeq | exact GlobalTheory.HSCore.exists_global_of_regSeq | (intros; apply GlobalTheory.HSCore.exists_global_of_regSeq <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory

theorem _root_.GlobalTheory.T.hyperplane_section_vanishing_shift : ∀ (k : Type) [Field k] (Y : Scheme.{0}) [Algebra k Γ(Y, ⊤)], IsProjOver (GlobalTheory.strHom k (X := Y)) → ∀ (L : LB Y) (hL : L.IsLB) (F : Y.Modules) [IsFiniteQC F] (t : L.Sec) [Mono (GlobalTheory.cutHom F hL t)] (j₀ : ℤ), VanishFrom L F j₀ → VanishFrom L (GlobalTheory.cut F hL t) (j₀ + 1) ∧ ∀ j : ℤ, j₀ + 1 ≤ j → GlobalTheory.hdim k (GlobalTheory.twistZ F L j) 0 = GlobalTheory.hdim k (GlobalTheory.twistZ F L (j - 1)) 0 + GlobalTheory.hdim k (GlobalTheory.twistZ (GlobalTheory.cut F hL t) L j) 0 := by
  first | exact @GlobalTheory.HSCore.vanishFrom_cut_and_hdim | exact GlobalTheory.HSCore.vanishFrom_cut_and_hdim | (intros; apply GlobalTheory.HSCore.vanishFrom_cut_and_hdim <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

theorem _root_.GlobalTheory.T.dbar_chernConnection_entry_eq_curvature : ∀ (n : ℕ) (r : Type) [Fintype r] [DecidableEq r] (G : V n → Matrix r r ℂ) (v : V n), MContDiffAt ∞ G v → IsUnit (G v).det → ∀ i j, dbarAt (fun x => ∑ a, conn G x (coordVec a) i j • dz a) v = (curvEv G v i j : Alt n) := by
  first | exact @GlobalTheory.ChernCalc.dbarAt_conn | exact GlobalTheory.ChernCalc.dbarAt_conn | (intros; apply GlobalTheory.ChernCalc.dbarAt_conn <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

theorem _root_.GlobalTheory.T.gramLowerTriangularFactor_posDef_properties : ∀ (s : ℕ) (G : Matrix (Fin s) (Fin s) ℂ), G.PosDef → (∀ j, 0 < (leadMinor G j).re ∧ (leadMinor G j).im = 0) ∧ (∀ i, 0 < grD G i ∧ ldPart G i i = grD G i) ∧ (∀ i j, i < j → ldPart G i j = 0) ∧ IsUnit (ldPart G).det := by
  first | exact @GlobalTheory.ChernCalc.ldPart_posDef_spec | exact GlobalTheory.ChernCalc.ldPart_posDef_spec | (intros; apply GlobalTheory.ChernCalc.ldPart_posDef_spec <;> assumption)
end
