module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle034
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle071
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.IsAlgClosureField
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle035
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle074
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle042
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ChainBetweenPairs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.AffSmulOne
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.ContResQ
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.Bundle007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.Bundle008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.GlobalTheory
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.Bundle009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.LayerEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.OverFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.PowOneInj
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.SmallCo
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.SpaceEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.Bundle002
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.RestrT
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.FieldTheory.Galois.Profinite
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Connected.Separation

@[expose] public section

section




section
open Formalism.ConjugateSelfDual IsLocalRing ReciprocityTheory.Gal UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Sd.S2
section
variable {R R' : Type} [CommRing R] [CommRing R'] (j : R →+* R')
private theorem fin_adj (X : M4 R) : adj (X.map j) = (adj X).map j := by
  ext a b
  simp only [adj_apply, Matrix.map_apply, map_zsmul]
private theorem fin_conj (X Y : M4 R) : adj (X.map j) * Y.map j * X.map j = (adj X * Y * X).map j := by
  rw [fin_adj, Matrix.map_mul, Matrix.map_mul]
private theorem fin_gsp (hj : Function.Injective j) (ν : R) (X : M4 R) (h : IsGSp (j ν) (X.map j)) : IsGSp ν X := by
  unfold IsGSp at h ⊢
  rw [fin_adj, ← Matrix.map_mul] at h
  ext a b
  apply hj
  have h1 := congrFun (congrFun h a) b
  rw [Matrix.map_apply] at h1
  rw [h1]
  simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, map_mul]
  split_ifs <;> simp
private theorem fin_psi {ι Γ : Type} [Group Γ] (P : PD ι Γ R) (v : ι) (i : Fin 4) (s : Γ) :
    (P.map j).ψ v i s = j (P.ψ v i s) :=
  congrFun (congrFun (fin_conj j (P.n v) (P.r s)) i) i
end
private theorem fin_q (i j : Fin 4) (h : i ≠ j) (h' : wt i j ∉ qQ) : i < j ∨ (i = 2 ∧ j = 1) := by
  revert i j; decide
private theorem fin_v (w : ℤ × ℤ) (h : w ∉ nP) : w ∉ vV := by
  simp only [nP, vV, Finset.mem_insert, Finset.mem_singleton] at h ⊢
  tauto
theorem UpperTheory.induced_final_statement_alt :
    _root_.UpperTheory.V.Sd.S2.Final_s := by
  intro Ω _ _ _ l _ c D T ι P hG hL hS
  haveI : IsGalois T.F Ω := IsAlgClosure.isGalois T.F Ω
  obtain ⟨c₁, h, Q, hQ, hc⟩ := (UpperTheory.automorphic_forms_descent_to_smaller_level l c).2 T.ι (G T.F Ω) P hG.cont hG.int fun v => (hL.low v).2.1
  subst hQ
  have hinj : Function.Injective (algebraMap c₁.O (Qbar l)) := Subtype.val_injective
  have hz : ∀ x : c₁.O, residue c₁.O x = 0 ↔ ‖algebraMap c₁.O (Qbar l) x‖ < 1 := fun x =>
    (residue_eq_zero_iff x).trans ((UpperTheory.automorphic_forms_descent_to_smaller_level l c₁).1 x).2
  have hne : ∀ x : c₁.O, ‖algebraMap c₁.O (Qbar l) x‖ = 1 → residue c₁.O x ≠ 0 := fun x hx h0 =>
    absurd ((hz x).1 h0) (by rw [hx]; exact lt_irrefl _)
  have heq : ∀ x y : c₁.O, ‖algebraMap c₁.O (Qbar l) x - algebraMap c₁.O (Qbar l) y‖ < 1 →
      residue c₁.O x = residue c₁.O y := fun x y hxy => by
    rw [← sub_eq_zero, ← map_sub, hz, map_sub]
    exact hxy
  have h0 : ∀ x : c₁.O, algebraMap c₁.O (Qbar l) x = 0 → x = 0 := fun x hx => hinj (by rw [hx, map_zero])
  have hV : Supp vV (Q.map (residue c₁.O)).r := fun g i j hij hw => (hz _).2 (hG.supp g i j hij hw)
  have hq : ∀ v, SuppM qQ ((Q.map (residue c₁.O)).n v) := fun v i j hij hw => by
    rcases fin_q i j hij hw with hlt | ⟨rfl, rfl⟩
    · refine (hz _).2 ?_
      have h1 : algebraMap c₁.O (Qbar l) (Q.n v i j) = 0 := (hL.low v).1.2.2 i j hlt
      rw [h1, norm_zero]
      exact one_pos
    · exact (hz _).2 (hL.low v).2.2.1
  refine ⟨c₁, h, Q, ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, hc, ⟨?_, ?_, Or.inl ⟨?_, hq⟩⟩, hS⟩,
    ⟨hV, fun v => ⟨hq v, hne _ (hL.low v).2.2.2⟩⟩, ?_⟩
  · exact fun g => fin_gsp _ hinj _ _ (hG.mult g)
  · intro g hg
    ext i j
    have h1 := congrFun (congrFun (hG.kill g hg) i) j
    have h2 : algebraMap c₁.O (Qbar l) ((1 : M4 c₁.O) i j) = (1 : M4 (Qbar l)) i j := by
      simp only [Matrix.one_apply]
      split_ifs <;> simp
    exact h1.trans h2.symm
  · exact fun i j hij => h0 _ (hG.nrm hij)
  · intro v
    obtain ⟨a1, a2, a3⟩ := (hL.low v).1
    refine ⟨fin_gsp _ hinj _ _ (by rw [map_one]; exact a1), fun i => hinj (by rw [map_one]; exact a2 i),
      fun i j hij => h0 _ (a3 i j hij)⟩
  · intro v s hs i j hij
    refine h0 _ ?_
    have h1 := hL.flag v s hs i j hij
    exact (congrFun (congrFun (fin_conj (algebraMap c₁.O (Qbar l)) (Q.n v) (Q.r s)) i) j).symm.trans h1
  · intro v s hs i
    refine hinj ?_
    exact ((fin_psi (algebraMap c₁.O (Qbar l)) Q v i s).symm.trans (hL.mu v s hs i)).trans (map_one _).symm
  · exact fun g i => heq _ _ (hG.diag g i)
  · intro v s hs i
    refine (fin_psi (residue c₁.O) Q v i s).trans (heq _ _ ?_)
    have h1 := hL.char v s hs i
    rw [fin_psi (algebraMap c₁.O (Qbar l)) Q v i s] at h1
    exact h1
  · exact fun g i j hij hw => hV g i j hij (fin_v _ hw)
  · rcases hG.ent with ⟨g, hg⟩ | ⟨⟨g, hg⟩, g', hg'⟩
    · exact Or.inl ⟨g, 1, 0, by decide, hne _ hg⟩
    · exact Or.inr ⟨⟨g, 1, 2, by decide, hne _ hg⟩, g', 3, 0, by decide, hne _ hg'⟩
end
end

section




section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Cu
private theorem chain_rank_four_good {O Γ R : Type} [CommRing O] [Group Γ] [CommRing R] {Φ : Fr O Γ} {a : O →+* R} {P : PD Φ.ι Γ R}
    [TopologicalSpace Γ] {P' : PD Φ.ι Γ R} (hP : Φ.IsRes a P) (h : Chain4 Φ a P P') :
    Φ.IsRes a P' ∧ Good4 Φ a P' := by
  obtain ⟨hg, hc⟩ := h
  induction hc with
  | refl => exact ⟨hP, hg⟩
  | tail _ hl _ => exact ⟨Asm.linked_isRes hl.2, hl.1⟩
attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete in
private theorem allIn_of_chain4 {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
    [TotallyDisconnectedSpace Γ] {Φ : Fr O Γ} {l : ℕ} [Fact l.Prime] {Λ : Type} [CommRing Λ] [IsDomain Λ]
    [IsDiscreteValuationRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] [Finite (ResidueField Λ)] {a : O →+* Λ} (hΦ : Φ.Std l a)
    (X : Space Φ a) (J : Ideal X.B)
    (hch : ∀ x : X.A →ₐ[Λ] ResidueField Λ, Φ.IsRes ((residue Λ).comp a) (X.P.map (x : X.A →+* ResidueField Λ)) →
      Good4 Φ ((residue Λ).comp a) (X.P.map (x : X.A →+* ResidueField Λ)) → X.SomeIn J (RingHom.ker x) → X.AllIn J (RingHom.ker x))
    (x₀ x₁ : X.A →ₐ[Λ] ResidueField Λ) (hs : Φ.IsRes ((residue Λ).comp a) (X.P.map (x₀ : X.A →+* ResidueField Λ)))
    (hc : Chain4 Φ ((residue Λ).comp a) (X.P.map (x₀ : X.A →+* ResidueField Λ)) (X.P.map (x₁ : X.A →+* ResidueField Λ)))
    (h₁ : X.SomeIn J (RingHom.ker x₁)) : X.AllIn J (RingHom.ker x₀) := by
  have key : ∀ s, Relation.ReflTransGen (fun x y => Good4 Φ ((residue Λ).comp a) y ∧ Φ.Linked ((residue Λ).comp a) x y) s
      (X.P.map (x₁ : X.A →+* ResidueField Λ)) → Φ.IsRes ((residue Λ).comp a) s → Good4 Φ ((residue Λ).comp a) s →
      ∀ x : X.A →ₐ[Λ] ResidueField Λ, X.P.map (x : X.A →+* ResidueField Λ) = s → X.AllIn J (RingHom.ker x) := by
    intro s h
    induction h using Relation.ReflTransGen.head_induction_on with
    | refl =>
      intro k1 k2 x e
      refine hch x (e ▸ k1) (e ▸ k2) ((conn Φ l a hΦ X J x x₁ ?_).2 (hch x₁ k1 k2 h₁))
      rw [e]
      exact Asm.linked_self k1
    | head hl _ ih =>
      rintro k1 k2 x rfl
      obtain ⟨x', rfl⟩ := Asm.end_pt X hl.2
      exact hch x k1 k2 ((conn Φ l a hΦ X J x x' hl.2).2 (ih (Asm.linked_isRes hl.2) hl.1 x' rfl))
  exact key _ hc.2 hs hc.1 x₀ rfl
private theorem conj_trans {H R : Type} [Group H] [CommRing R] {r r' r'' : H →* M4 R} (h : IsConj4 r r') (h' : IsConj4 r' r'') :
    IsConj4 r r'' := by
  obtain ⟨u, hu⟩ := h
  obtain ⟨v, hv⟩ := h'
  exact ⟨v * u, fun g => by rw [hv, hu, mul_inv_rev, Units.val_mul, Units.val_mul]; simp only [mul_assoc]⟩
private theorem res_self (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] :
    (res O O : O →+* ResidueField O) = residue O := RingHom.ext fun x => (res O O).commutes x
private theorem last_step (hCh : _root_.UpperTheory.V.Cu.ChainRankFour) (hCD : ChainDesc4) (hC : CohomologyHyp) (hPM : _root_.UpperTheory.V.Ws.PMExAlt) {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime]
    {c : Coef l} {D : Raw Ω c} (T : Tower D) (hF : T.Fit) (hD : T.Deep) (ι : PadicAlgCl l ≃+* ℂ) (𝔞 : Amb l) (C : ℕ)
    (hB : ∀ (k : Type) [Field k] (a : c.O →+* k), (∀ x ∈ maximalIdeal c.O, a x = 0) → (T.fr ∅).Bounds a T.d C)
    (hd : 30 * (C + 1) * (C + 1) ≤ T.d) {c₁ : Coef l} {h₁ : c.O ≤ c₁.O} {Q : PD T.ι (G T.F Ω) c₁.O} (hQ : T.SeedPairAlt ι h₁ Q)
    {P : PD T.ι (G T.F Ω) 𝔞.V} (hs : 𝔞.Small P) (hp : (T.fr ∅).IsPair (𝔞.a c) P)
    (hr : (T.fr ∅).IsRes (𝔞.red c) (P.map (residue 𝔞.V)))
    (hch : Chain4 (T.fr ∅) (𝔞.red c) (P.map (residue 𝔞.V)) (Q.map (𝔞.red c₁))) :
    ∃ (c' : Coef l) (h : c.O ≤ c'.O) (X : Space (T.fr ∅) (inc h)) (J : Ideal X.B) (y : X.A →+* 𝔞.V), T.PotentialModularityTower ι X J ∧
      y.comp (algebraMap c'.O X.A) = 𝔞.a c' ∧ (∀ b ∈ maximalIdeal X.B, y (algebraMap X.B X.A b) ∈ maximalIdeal 𝔞.V) ∧
      (∀ b ∈ J, y (algebraMap X.B X.A b) = 0) ∧ X.P.map y = P := by
  obtain ⟨c₂, k₂⟩ := hCD 𝔞 c (T.fr ∅) _ _ hr hch
  obtain ⟨c₃, k₃⟩ := smallCo 𝔞 P hs
  obtain ⟨c₄, k₄⟩ := hPM Ω l c D T hF hD ι
  obtain ⟨d₁, a₁, a₂⟩ := (coefSup l).1 c₁ c₂
  obtain ⟨d₂, a₃, a₄⟩ := (coefSup l).1 c₃ c₄
  obtain ⟨c', b₁, b₂⟩ := (coefSup l).1 d₁ d₂
  have e₁ : c₁.O ≤ c'.O := a₁.trans b₁
  have h : c.O ≤ c'.O := h₁.trans e₁
  haveI : Finite (ResidueField c'.O) := by
    haveI : IsLocalHom (algebraMap ℤ_[l] c'.O) := (dvrFacts l c'.O).2.2.1
    haveI : Finite (ResidueField ℤ_[l]) := Finite.of_equiv _ (PadicInt.residueField (p := l)).symm.toEquiv
    exact Module.finite_of_finite (ResidueField ℤ_[l])
  have hS := (std hC D T hF ∅ c' h).1 (Finset.notMem_empty 0)
  obtain ⟨X⟩ := spaceEx (T.fr ∅) l (inc h) hS
  obtain ⟨J, hJ⟩ := k₄ c' h (a₄.trans b₂) X
  obtain ⟨s, t, es, et, rs, cst⟩ := k₂ c' h (a₂.trans b₁)
  obtain ⟨R, _, _, _, f, QR, fi, fa, fr, qc, rfl⟩ := k₃ c' (a₃.trans b₂)
  have inj := (chainMap (T.fr ∅) ((residue c'.O).comp (inc h)) (𝔞.j c') s).2.2
  have loc : ∀ {d : Coef l} (e : d.O ≤ c'.O), maximalIdeal d.O ≤ (maximalIdeal c'.O).comap (inc e) := fun {d} e x hx hu => by
    have h2 : IsUnit (𝔞.a d x) := 𝔞.compat d c' e x ▸ hu.map (𝔞.a c')
    exact hx (IsLocalHom.map_nonunit x h2)
  have jc : (𝔞.j c').comp ((residue c'.O).comp (inc e₁)) = 𝔞.red c₁ :=
    RingHom.ext fun x => congrArg (residue 𝔞.V) (𝔞.compat c₁ c' e₁ x)
  have lQ : (T.fr ∅).Lifts (inc h) t (Q.map (inc e₁)) := by
    refine ⟨hQ.pair.map (inc e₁), hQ.cont.map _ (loc e₁), inj ?_⟩
    show ((Q.map _).map _).map _ = t.map _
    rw [et, res_self, PD.map_map, PD.map_map, ← jc]
    rfl
  obtain ⟨f₁, hf₁⟩ := X.univ c'.O t _ (chain_rank_four_good rs cst).1 lQ
  have sd := hJ.seed ((Algebra.ofId c'.O (PadicAlgCl l)).comp f₁) (by
    have e : X.P.map (((Algebra.ofId c'.O (PadicAlgCl l)).comp f₁ : X.A →ₐ[c'.O] PadicAlgCl l) : X.A →+* PadicAlgCl l) =
        Q.map (algebraMap c₁.O (PadicAlgCl l)) := by
      show (X.P.map (f₁ : X.A →+* c'.O)).map (algebraMap c'.O (PadicAlgCl l)) = _
      rw [hf₁]
      rfl
    rw [e]
    exact hQ.seed)
  have s₁ : X.SomeIn J (RingHom.ker ((res c'.O c'.O).comp f₁)) := Asm.someIn_of_locZero X J _ sd fun z hz => by
    have h0 : f₁ z = 0 := Subtype.ext hz
    show res c'.O c'.O (f₁ z) = 0
    rw [h0, map_zero]
  have e₁' : X.P.map (((res c'.O c'.O).comp f₁ : X.A →ₐ[c'.O] ResidueField c'.O) : X.A →+* ResidueField c'.O) = t := by
    show (X.P.map (f₁ : X.A →+* c'.O)).map (res c'.O c'.O : c'.O →+* ResidueField c'.O) = t
    rw [hf₁]
    exact lQ.red
  have lR : (T.fr ∅).Lifts (inc h) s QR := by
    refine ⟨Asm.pair_of f fi ?_, qc, inj ?_⟩
    · rw [← RingHom.comp_assoc, fa]
      have : (𝔞.a c').comp (inc h) = 𝔞.a c := RingHom.ext fun x => 𝔞.compat c c' h x
      rw [this]
      exact hp
    · show (QR.map _).map _ = s.map _
      rw [es, PD.map_map, PD.map_map, fr]
  obtain ⟨f₀, hf₀⟩ := X.univ R s _ rs lR
  have e₀ : X.P.map (((res c'.O R).comp f₀ : X.A →ₐ[c'.O] ResidueField c'.O) : X.A →+* ResidueField c'.O) = s := by
    show (X.P.map (f₀ : X.A →+* R)).map (res c'.O R : R →+* ResidueField c'.O) = s
    rw [hf₀]
    exact lR.red
  have all := allIn_of_chain4 hS X J
    (hCh hC D T hF hD ι c' h X J hJ C (hB _ _ fun x hx => (residue_eq_zero_iff _).2 (loc h hx)) hd)
    ((res c'.O R).comp f₀) ((res c'.O c'.O).comp f₁) (e₀ ▸ rs) (e₀ ▸ e₁' ▸ cst) s₁
  refine ⟨c', h, X, J, f.comp (f₀ : X.A →+* R), hJ, ?_, fun b hb => ?_, Asm.zero_of_allIn X J _ all fun z hz => ?_, ?_⟩
  · rw [RingHom.comp_assoc, AlgHom.comp_algebraMap, fa]
  · have h0 : res c'.O R ((f₀.comp (IsScalarTower.toAlgHom c'.O X.B X.A)) b) = 0 := by
      rw [res_map, res_eq_zero_iff]
      exact hb
    refine (residue_eq_zero_iff _).1 ((RingHom.congr_fun fr (f₀ (algebraMap X.B X.A b))).trans ?_)
    exact (congrArg (𝔞.j c') h0).trans (map_zero _)
  · have h0 : f₀ z = 0 := (map_eq_zero_iff f fi).1 hz
    show res c'.O R (f₀ z) = 0
    rw [h0, map_zero]
  · exact congrArg (fun Z => PD.map Z f) hf₀
theorem UpperTheory.V.Cu.promodularity_case_three_of_chain_reduction : ExistsTensorFactorTower → _root_.UpperTheory.V.Cu.ChainRankFour → ChainDesc4 → _root_.UpperTheory.V.Cu.RankFourChainReductionDense → _root_.UpperTheory.V.Cu.PromodularityCaseThreeDense := by
  intro hLem hCh hCD hCIV hC hFW hH h4 hPM Ω _ _ _ l _ c D hD ι 𝔞 r u hK hS
  have hG : D.Good := hD.1
  obtain ⟨pr, hl, hP⟩ := labels D hG 𝔞 r u hK
  obtain ⟨T₀, rfl, ok, four, tame₀⟩ := hLem D hD pr hl
  have hF₀ : T₀.Fit := hH D T₀ hD ok four
  have hc := hCIV hC hH h4 D T₀ hD ok four tame₀ ι 𝔞
  obtain ⟨P, qP, nP, cP, sP⟩ := hP _ hF₀.1.dist
  obtain ⟨P', qP', cP', lP'⟩ := lat hC D hG 𝔞 _ _ hl hF₀.1.dist P qP nP (sP hS)
  obtain ⟨T₁, le₁, tame, hT⟩ := hc _ lP'
  have f₁ := leFit D hG T₀ T₁ le₁
  have hF₁ := f₁.2.2.2.2.1 hF₀
  obtain ⟨C, hB⟩ := x2 hC hFW D T₁ hF₁ tame
  obtain ⟨T, m, le, lay, deep, hd⟩ := layerEx D hG T₁ hF₁ tame (30 * (C + 1) * (C + 1))
  have hF := (leFit D hG T₁ T le).2.2.2.2.1 hF₁
  obtain ⟨c₁, h₁, Q, hQ, hch⟩ := hT T le deep
  obtain ⟨P'', sm, pr'', er, ov, rs, ine⟩ := restrQ D hG T₀ T hF₀ (f₁.2.2.2.2.2.2 T le) 𝔞 P' qP' lP'
  obtain ⟨c', h, X, J, y, k1, k2, k3, k4, k5⟩ :=
    last_step hCh hCD hC hPM T hF deep ι 𝔞 C (hB T m le lay) hd hQ sm pr'' rs (hch _ ov rs)
  refine ⟨T, c', h, X, J, y, P'.r, hF, deep, k1, k2, k3, k4, conj_trans cP cP', qP'.pair.mult, by rw [k5, er],
    fun v i s hs => ?_⟩
  subst k5
  exact (PD.map_ψ X.P y v i s).symm.trans (ine v i s hs)
end
end

section




section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws
namespace UpperTheory.V.Cu.RankFourChainReduction
open UpperTheory.V.Ws.Chn
end UpperTheory.V.Cu.RankFourChainReduction
open UpperTheory.V.Cu UpperTheory.V.Ws.Chn UpperTheory.V.Cu.RankFourChainReduction in
theorem UpperTheory.V.Cu.chainIV_alt : _root_.UpperTheory.V.Cu.RankFourChainReductionDense := by
  intro hC hH hS Ω _ _ _ l _ c D T₀ h3 hok h4 htame ι 𝔞 c₀ hc₀
  have hG : D.Good := h3.1
  have hF : T₀.Fit := hH D T₀ h3 hok h4
  have ha := red_zero 𝔞 c
  have ok0 : (T₀.fr ∅).Ok (𝔞.red c) := (std hC D T₀ hF ∅ c le_rfl).2 _ _ ha
  obtain ⟨w, s, hw, hsp, hs, hsM, hseed⟩ := hS Ω l c D T₀ h3 hok h4 ι 𝔞
  obtain ⟨p0, hp0, hov0⟩ := UpperTheory.exists_residualRep_restriction_of_latticeShape D hG T₀ hF _ _ ha ok0 c₀ hc₀
  obtain ⟨-, hp0P, -⟩ := goodQ D hG T₀ hF _ _ ha _ c₀ p0 hc₀ (fun w hw => rt_ne (Φ := T₀.fr ∅) ok0 w hw) hov0 hp0 ∅
  obtain ⟨W1, p2, hW1, hW1s, hp2, hp2Q, hp2A, hp2E⟩ :=
    gysinPs hC D T₀ hF _ _ ha {w} (by simpa using ⟨hw, hsp⟩) s hs hsM
  obtain ⟨W2, p3, p4, hW2, hW2s, hp3, hp4, hp3Q, hp4Q, h30, h42, h34, h3E⟩ :=
    gysinAl hC D T₀ hF _ _ ha W1 hW1s p0 p2 (res_mono T₀ (Finset.empty_subset _) hp0) hp2 hp0P (qP hp2Q)
  obtain ⟨T₁, hL1, ht1, hd1⟩ := diesEx D hG T₀ htame hok W2 hW2s
  refine ⟨T₁, hL1, ht1, fun T hL _ => ?_⟩
  have hT : T₀.Le T := (leFit D hG T₀ T₁ hL1).2.2.2.2.2.2 T hL
  obtain ⟨lo, -, -, -, lf, -, -⟩ := leFit D hG T₀ T hT
  have hd : ∀ w ∈ W2, Dies l w T.F := fun w hw => dies_mono hL.le (hd1 w hw)
  obtain ⟨c₁, h, Q, hQ, hovs, hQA, hQB, hQT⟩ := hseed T hT (lo hok) (hd w (hW2 (hW1 (Finset.mem_singleton_self w))))
  refine ⟨c₁, h, Q, hQ, fun u hu hur => ?_⟩
  have okT : (T.fr ∅).Ok (𝔞.red c) := (std hC D T (lf hF) ∅ c le_rfl).2 _ _ ha
  have hq := _root_.UpperTheory.V.Ws.Chn.seed_res_alt T 𝔞 hQ
  replace hs := res_mono T₀ (hW1.trans hW2) hs
  replace hp0 := res_mono T₀ (Finset.empty_subset W2) hp0
  replace hp2 := res_mono T₀ hW2 hp2
  have R := fun x hx => restrT D hG T₀ T hT hF _ _ ha W2 hW2s hd x hx (Or.inl h4.five)
  obtain ⟨q0, hq0, o0⟩ := R p0 hp0
  obtain ⟨q2, hq2, o2⟩ := R p2 hp2
  obtain ⟨q3, hq3, o3⟩ := R p3 hp3
  obtain ⟨q4, hq4, o4⟩ := R p4 hp4
  have O := overFacts D hG T₀ T hT hF _ _ ha W2 ∅
  obtain ⟨-, -, -, a1, -, -, -, a2⟩ := O p0 p3 q0 q3 hp0 hp3 hq0 hq3 o0 o3
  obtain rfl : u = q0 := a2 c₀ _ hc₀.res.pair hov0 u hur hu
  obtain ⟨-, b0, b1, -, b2, -, b4, -⟩ := O p3 p4 q3 q4 hp3 hp4 hq3 hq4 o3 o4
  obtain ⟨-, c0, c1, c2, -, -, -, -⟩ := O p4 p2 q4 q2 hp4 hp2 hq4 hq2 o4 o2
  obtain ⟨-, d0, d1, -, d2, d3, -, -⟩ := O p2 s q2 _ hp2 hs hq2 hq o2 hovs
  obtain ⟨-, e0, -, -, -, -, -, -⟩ := O s s _ _ hs hs hq hq hovs hovs
  have hlat : LatShape D T.pr (resQ T₀.F T₀.g0) (𝔞.red c) c₀ := hT.pr ▸ hc₀
  have hrt : ∀ w ∈ roots, 𝔞.red c ((frQ D T.pr (resQ T₀.F T₀.g0)).rt w (resQ T₀.F T₀.g0)) ≠ 1 := by
    rw [hT.pr]; exact fun w hw => rt_ne (Φ := T₀.fr ∅) ok0 w hw
  obtain ⟨-, uP, ug⟩ := goodQ D hG T (lf hF) _ _ ha _ c₀ u hlat hrt hu hur ∅
  have P3 := b1 (qP hp3Q)
  have P4 := c1 (qP hp4Q)
  have P2 := d1 (qP hp2Q)
  have M3 := b0 _ (qM hp3Q.1)
  have M4 := c0 _ (qM hp4Q.1)
  have M2 := d0 _ (qM hp2Q.1)
  have Ms := e0 _ hsM
  have s03 := a1 hp0P (qP hp3Q) (samePs_symm h30)
  have s34 := b2 (qM hp3Q.1) (qM hp4Q.1) h34
  have s42 := c2 (qP hp4Q) (qP hp2Q) h42
  have s2s := d2 (qM hp2Q.1) hsM hp2A
  have A3 := (b4 (qM hp3Q.1)).1 h3E
  have E2 := d3 (qP hp2Q).1 hp2E
  have g0 : Good4 (T.fr ∅) (𝔞.red c) u :=
    Or.inl (ug.elim (fun x => Or.inl ⟨x.1, Or.inl x.2⟩) fun x => Or.inr (Or.inr (Or.inl x)))
  have g3 : Good4 (T.fr ∅) (𝔞.red c) q3 :=
    Or.inl (ug.elim (fun x => Or.inl ⟨(samePs_ent hur hq3 uP.1 P3.1 s03).1 x.1, Or.inr A3⟩)
      fun x => Or.inr (Or.inr (Or.inl ⟨samePs_inV hq3 P3 s03 x.1, A3⟩)))
  have g4 : Good4 (T.fr ∅) (𝔞.red c) q4 :=
    Or.inl (Or.inl ⟨(samePs_ent hq4 hq2 P4.1 P2.1 s42).2 E2, Or.inr ((sameAl_ent hq3 hq4 M3 M4 s34).1 A3)⟩)
  have g2 : Good4 (T.fr ∅) (𝔞.red c) q2 :=
    Or.inr (Or.inl ⟨inA_of hq2 (d0 _ hp2Q.1) s2s hQA, E2⟩)
  have gs : Good4 (T.fr ∅) (𝔞.red c) (Q.map (𝔞.red c₁)) := Or.inr (Or.inr ⟨hQA, hQB, hQT⟩)
  exact ⟨g0, (((Relation.ReflTransGen.single ⟨g3, lineP _ _ okT _ _ hur hq3 uP P3 s03⟩).tail
    ⟨g4, lineM _ _ okT _ _ hq3 hq4 M3 M4 s34⟩).tail ⟨g2, lineP _ _ okT _ _ hq4 hq2 P4 P2 s42⟩).tail
    ⟨gs, lineM _ _ okT _ _ hq2 hq M2 Ms s2s⟩⟩
end
end
