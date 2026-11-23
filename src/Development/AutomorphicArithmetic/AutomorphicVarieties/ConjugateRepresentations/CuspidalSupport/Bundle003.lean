module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.HeckeLocalBlock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1124
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle118
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle027
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle022
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

private theorem sum_three {A B C P R : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype P] [Fintype R]
    [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq P]
    (f : A → P) (f' : B → P) (f'' : C → P) (h : Function.Bijective (Sum.elim (Sum.elim f f') f''))
    (g : (A → R) → (B → R) → ℂ) :
    ∑ c : P → R, g (c ∘ f) (c ∘ f') = (Fintype.card R : ℂ) ^ Fintype.card C * ∑ c₁, ∑ c₂, g c₁ c₂ := by
  let e : (P → R) ≃ ((A → R) × (B → R)) × (C → R) :=
    ((Equiv.ofBijective _ h).symm.arrowCongr (Equiv.refl R)).trans
      ((Equiv.sumArrowEquivProdArrow _ _ _).trans
        ((Equiv.sumArrowEquivProdArrow _ _ _).prodCongr (Equiv.refl _)))
  have h1 : ∑ c : P → R, g (c ∘ f) (c ∘ f') = ∑ x : ((A → R) × (B → R)) × (C → R), g x.1.1 x.1.2 :=
    Fintype.sum_equiv e _ _ (fun c => rfl)
  rw [h1, Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, nsmul_eq_mul]
  rw [← Finset.mul_sum, Fintype.sum_prod_type]
  push_cast
  rfl

private def pair3 {r s : ℕ} (S : Finset (Fin (r + s))) (p : sub1 S × ((sub2 S)ᶜ : Finset (Fin s))) : satakePairs S :=
  ⟨(Fin.castAdd s p.1.1, Fin.natAdd r p.2.1), (Finset.mem_filter.1 p.1.2).2, by simpa [sub2] using p.2.2, by
    have := p.1.1.2
    simp only [Fin.lt_def, Fin.val_castAdd, Fin.val_natAdd]
    omega⟩

private theorem bij3 {r s : ℕ} (S : Finset (Fin (r + s))) :
    Function.Bijective (Sum.elim (Sum.elim (pair1 S) (pair2 S)) (pair3 S)) := by
  constructor
  · rintro ((⟨⟨a, b⟩, h⟩ | ⟨⟨a, b⟩, h⟩) | ⟨⟨a, h⟩, ⟨b, h'⟩⟩) ((⟨⟨c, d⟩, k⟩ | ⟨⟨c, d⟩, k⟩) | ⟨⟨c, k⟩, ⟨d, k'⟩⟩) H <;>
      simp only [Sum.elim_inl, Sum.elim_inr, pair1, pair2, pair3, Subtype.mk.injEq, Prod.mk.injEq, Fin.ext_iff,
        Fin.val_castAdd, Fin.val_natAdd, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq] at H ⊢ <;>
      omega
  · rintro ⟨⟨a, b⟩, h1, h2, h3⟩
    induction a using Fin.addCases with
    | left a =>
      induction b using Fin.addCases with
      | left b =>
        exact ⟨.inl (.inl ⟨(a, b), by simpa [sub1] using h1, by simpa [sub1] using h2, h3⟩), rfl⟩
      | right b =>
        exact ⟨.inr (⟨a, by simpa [sub1] using h1⟩, ⟨b, by simpa [sub2] using h2⟩), rfl⟩
    | right a =>
      induction b using Fin.addCases with
      | left b =>
        exfalso
        simp only [Fin.lt_def, Fin.val_castAdd, Fin.val_natAdd] at h3
        omega
      | right b =>
        refine ⟨.inl (.inr ⟨(a, b), by simpa [sub2] using h1, by simpa [sub2] using h2, ?_⟩), rfl⟩
        simp only [Fin.lt_def, Fin.val_natAdd] at h3 ⊢
        omega

theorem UpperTheory.V.Cj.S.sumInner :
    UpperTheory.V.Cj.S.SumInner := by
  intro r s R _ S g
  rw [sum_three (pair1 S) (pair2 S) (pair3 S) (bij3 S) g]
  simp only [Fintype.card_prod, Fintype.card_coe, Finset.card_compl, Fintype.card_fin]
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

private theorem mem_fixed' {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
    {H : Subgroup G} {v : V} : v ∈ fixed ρ H ↔ ∀ k ∈ H, ρ k v = v := by
  change (∀ h : H, ρ (h : G) v = (((1 : H →* ℂˣ) h : ℂˣ) : ℂ) • v) ↔ _
  simp

private theorem blk_mul {r s : ℕ} {R : Type} [CommRing R] (a a' : GL (Fin r) R) (b b' : GL (Fin s) R) :
    blk (a * a') (b * b') = blk a b * blk a' b' := by
  simp only [blk, map_mul, mul_assoc]
  rw [← mul_assoc (emb (e2 r s) b), ← UpperTheory.V.Af.Fin.emb_comm, mul_assoc]

private theorem fL_apply {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {n : ℕ} (w : Pl E)
    (b : GL (Fin n) (w.adicCompletion E)) (φ : Sm E n) (x : GA E n) :
    (fL n w b φ).1 x = φ.1 (x * finGL E n (locGL E n w b)) := rfl

private theorem tOp_apply (hS : HkSum) {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {n : ℕ} (w : Pl E)
    {ϖ : w.adicCompletion E} (hϖ : ϖ ∈ Ov E w) (hu : IsUnifV E w ϖ) [Fintype (satakeRes (Ov E w) ⟨ϖ, hϖ⟩)] (j : ℕ)
    (hj : j ≤ n) (φ : Sm E n) (hφ : φ ∈ fixed (fL n w) (KGL w (n := n))) (x : GA E n) :
    (tOp n w hu j φ).1 x =
      ∑ i : SatakeIdx w hϖ (n := n) j, φ.1 (x * finGL E n (locGL E n w (satakeB w hϖ hu i))) := by
  have h := hS E w n (Sm E n) (fL n w) ϖ hϖ hu j hj φ hφ
  have h' : tOp n w hu j φ = ∑ i : SatakeIdx w hϖ (n := n) j, fL n w (satakeB w hϖ hu i) φ := h
  rw [h', Submodule.coe_sum, Finset.sum_apply]
  rfl

theorem UpperTheory.V.Cj.S.hkRel :
    UpperTheory.V.Cj.S.Slice → UpperTheory.V.Cj.S.HkSum → UpperTheory.V.Cj.S.HkLocal → UpperTheory.V.Cj.S.HeckeLocalBlock → UpperTheory.V.Cj.S.HkRel := by
  intro hSl hS hL hB E _ _ _ r s ψ hN w hψ ϖ hu j hj
  have hϖ : ϖ ∈ Ov E w := mem_Ov_of_isUnifV hu
  have := satake_res_finite w hϖ hu
  letI : Fintype (satakeRes (Ov E w) ⟨ϖ, hϖ⟩) := Fintype.ofFinite _
  obtain ⟨b1, b2, b3, b4⟩ := hB E w r s
  have hfix : ∀ k ∈ KGL w (n := (r + s)), ∀ g, ψ.1 (g * finGL E _ (locGL E _ w k)) = ψ.1 g := fun k hk g =>
    congrFun (congrArg Subtype.val (mem_fixed'.1 hψ k hk)) g
  have hs1 : ∀ y : GA E s, ∃ f : Sm E r, (∀ x, f.1 x = ψ.1 (blk x y)) ∧ f ∈ fixed (fL r w) (KGL w (n := r)) := fun y => by
    obtain ⟨f, hf, -⟩ := hSl E r (r + s) (e1 r s) (emb (e2 r s) y)
    have hf' : ∀ x, (f ψ).1 x = ψ.1 (blk x y) := fun x => by rw [hf, blk, UpperTheory.V.Af.Fin.emb_comm]
    refine ⟨f ψ, hf', mem_fixed'.2 fun k hk => Subtype.ext (funext fun x => ?_)⟩
    rw [fL_apply, hf', hf', ← hfix _ (b4 k hk 1 (one_mem _)) (blk x y), b1, ← blk_mul, map_one, map_one, mul_one]
  have hs2 : ∀ x : GA E r, ∃ f : Sm E s, (∀ y, f.1 y = ψ.1 (blk x y)) ∧ f ∈ fixed (fL s w) (KGL w (n := s)) := fun x => by
    obtain ⟨f, hf, -⟩ := hSl E s (r + s) (e2 r s) (emb (e1 r s) x)
    have hf' : ∀ y, (f ψ).1 y = ψ.1 (blk x y) := fun y => by rw [hf, blk]
    refine ⟨f ψ, hf', mem_fixed'.2 fun k hk => Subtype.ext (funext fun y => ?_)⟩
    rw [fL_apply, hf', hf', ← hfix _ (b4 1 (one_mem _) k hk) (blk x y), b1, ← blk_mul, map_one, map_one, mul_one]
  choose f2 hf2 hf2' using hs2
  refine ⟨fun p x y => ∑ i₁ : SatakeIdx w hϖ (n := r) p.1, ∑ i₂ : SatakeIdx w hϖ (n := s) p.2,
    ψ.1 (blk (x * finGL E r (locGL E r w (satakeB w hϖ hu i₁))) (y * finGL E s (locGL E s w (satakeB w hϖ hu i₂)))),
    fun p => ⟨fun x y => ∑ i₁ : SatakeIdx w hϖ (n := r) p.1,
      ψ.1 (blk (x * finGL E r (locGL E r w (satakeB w hϖ hu i₁))) y), fun y => ?_, fun x => ?_⟩, fun x y => ?_⟩
  · obtain ⟨f, hf, hf'⟩ := hs1 y
    refine ⟨f, funext hf, funext fun x => ?_⟩
    rw [tOp_apply hS w hϖ hu _ (Nat.lt_succ_iff.mp p.1.2) f hf']
    simp only [hf]
  · have hv : ∀ y, (∑ i₁ : SatakeIdx w hϖ (n := r) p.1,
        f2 (x * finGL E r (locGL E r w (satakeB w hϖ hu i₁)))).1 y = ∑ i₁ : SatakeIdx w hϖ (n := r) p.1,
        ψ.1 (blk (x * finGL E r (locGL E r w (satakeB w hϖ hu i₁))) y) := fun y => by
      rw [Submodule.coe_sum, Finset.sum_apply]
      simp only [hf2]
    refine ⟨_, funext hv, funext fun y => ?_⟩
    rw [tOp_apply hS w hϖ hu _ (Nat.lt_succ_iff.mp p.2.2) _ (Submodule.sum_mem _ fun i _ => hf2' _)]
    simp only [hv]
    exact Finset.sum_comm
  · rw [res, tOp_apply hS w hϖ hu j hj ψ hψ,
      hL E w r s ϖ hϖ hu j (fun g => ψ.1 (blk x y * finGL E _ (locGL E _ w g))) (fun X g => by
        obtain ⟨Y, hY⟩ := b2 X
        obtain ⟨Y', hY'⟩ := b3 x y Y
        simp only [map_mul]
        rw [hY, ← mul_assoc, hY', mul_assoc, hN])]
    simp only [b1, blk_mul]
end

section

open Polynomial

namespace UpperTheory.V.Cj.S

private theorem eq_of_prod_eq (m n : Multiset ℂ) (h : ∀ u : ℂ, (m.map (u + ·)).prod = (n.map (u + ·)).prod) : m = n := by
  have key : ∀ (k : Multiset ℂ) (u : ℂ),
      (((k.map fun x => -x).map fun x => X - C x).prod).eval u = (k.map (u + ·)).prod := by
    intro k u
    rw [eval_multiset_prod, Multiset.map_map, Multiset.map_map]
    congr 1
    refine Multiset.map_congr rfl fun x _ => ?_
    simp
  have hp : ((m.map fun x => -x).map fun x => X - C x).prod = ((n.map fun x => -x).map fun x => X - C x).prod :=
    Polynomial.funext fun u => by rw [key, key, h]
  have hr := congrArg Polynomial.roots hp
  rw [roots_multiset_prod_X_sub_C, roots_multiset_prod_X_sub_C] at hr
  exact Multiset.map_injective neg_injective hr

theorem capArith : CapArith := by
  intro m m₁ m₂ α β h
  refine eq_of_prod_eq _ _ fun u => ?_
  rw [← h u, Multiset.map_add (f := _), Multiset.prod_add, Multiset.map_map, Multiset.map_map]
  congr 2
  · exact Multiset.map_congr rfl fun x _ => by simp only [Function.comp]; ring
  · exact Multiset.map_congr rfl fun x _ => by simp only [Function.comp]; ring

end UpperTheory.V.Cj.S
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

attribute [local instance 100] LieRing.ofAssociativeRing in
private theorem one_mem_centerU (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) :
    UniversalEnvelopingAlgebra.ι ℝ (UpperTheory.V.Cm.lieEq E a (oneL E a)) ∈ (isExpLieAlgebra E a).centerU := by
  refine Subalgebra.mem_center_iff.2 fun u => ?_
  induction u using GroundTheory.Automorphic.AutomorphicForm.UEnv.induction with
  | halg r => exact Algebra.commutes r _
  | hι Y =>
    have h : ⁅Y, UpperTheory.V.Cm.lieEq E a (oneL E a)⁆ = 0 := by
      refine Subtype.ext ?_
      rw [LieSubalgebra.coe_bracket, UpperTheory.V.Cm.lieEq_oneL, Ring.lie_def, mul_one, one_mul, sub_self]
      rfl
    rw [← sub_eq_zero, ← Ring.lie_def, ← LieHom.map_lie, h, map_zero]
  | hmul x y hx hy => rw [mul_assoc, hy, ← mul_assoc, hx, mul_assoc]
  | hadd x y hx hy => rw [add_mul, mul_add, hx, hy]

private theorem scalar_of_mem_Zalg {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}
    (m : (E →+* ℂ) → Multiset ℂ) {z : Module.End ℂ (Sm E a)} (hz : z ∈ Zalg E a) :
    ∃ c : ℂ, ∀ φ ∈ CI a m, z φ = c • φ := by
  induction hz using Algebra.adjoin_induction with
  | mem z hz =>
    obtain ⟨t, u, rfl⟩ := hz
    exact ⟨_, fun φ hφ => (mem_CI.1 hφ).2 t u⟩
  | algebraMap r => exact ⟨r, fun φ _ => rfl⟩
  | add x y _ _ hx hy =>
    obtain ⟨c, hc⟩ := hx
    obtain ⟨d, hd⟩ := hy
    exact ⟨c + d, fun φ hφ => by rw [LinearMap.add_apply, hc φ hφ, hd φ hφ, add_smul]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨c, hc⟩ := hx
    obtain ⟨d, hd⟩ := hy
    exact ⟨d * c, fun φ hφ => by rw [Module.End.mul_apply, hd φ hφ, map_smul, hc φ hφ, mul_smul]⟩

theorem UpperTheory.V.Cj.S.ciBasic :
    UpperTheory.V.Cj.S.CapAct → UpperTheory.V.Cj.S.CiBasic := by
  intro hc E _ _ _ a m
  refine ⟨fun o φ hφ => mem_CI.2 ⟨UpperTheory.V.Cm.isCuspForm_act o (mem_CI.1 hφ).1, fun t u => ?_⟩, ?_⟩
  · have h := LinearMap.congr_fun ((hc E a t u).2.1 o).eq φ
    rw [Module.End.mul_apply, Module.End.mul_apply, (mem_CI.1 hφ).2 t u, map_smul] at h
    exact h
  · rw [← UpperTheory.V.Cm.uTC_ι]
    exact scalar_of_mem_Zalg m (UpperTheory.V.Cm.uTC_mem_Zalg (one_mem_centerU E a))
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

theorem UpperTheory.V.Cj.S.ctSat :
    UpperTheory.V.Cj.S.CtSat := by
  intro E _ _ _ n r φ ψ hφ hψ h0 w B hB
  let C : Submodule ℂ (Sm E n) :=
    { carrier := {f | Continuous f.1}
      add_mem' := fun h h' => Continuous.add h h'
      zero_mem' := continuous_const
      smul_mem' := fun c _ h => Continuous.const_smul h c }
  have hC : ∀ g, ∀ f ∈ C, fL n w g f ∈ C := fun g f hf =>
    show Continuous fun x => f.1 (x * finGL E n (locGL E n w g)) from
      Continuous.comp (show Continuous f.1 from hf) (continuous_id.mul continuous_const)
  have hc : φ ∈ C := ((UpperTheory.V.Cm.isAutForm_iff φ).1 hφ).continuous
  let F : C →ₗ[ℂ] (GA E n → ℂ) :=
    { toFun := fun f => constantTerm r f.1.1
      map_add' := fun f f' => funext fun g => GroundTheory.Automorphic.AutomorphicForm.constantTerm_add f.2 f'.2 g
      map_smul' := fun c f => funext fun g => GroundTheory.Automorphic.AutomorphicForm.constantTerm_smul c f.1.1 g }
  have h1 : IsSatVecGL w (GlobalTheory.PRep.sub (fL n w) C hC) ⟨φ, hc⟩ B :=
    IsSatVecGL.of_map C.subtype (fun _ _ => rfl) Subtype.val_injective hB
  have hF : F ⟨φ, hc⟩ = ψ.1 := hψ.symm
  have h2 := h1.map (ρ' := (GlobalTheory.PRep.rightReg ℂ (GA E n) ℂ).comp ((finGL E n).comp (locGL E n w))) F
    (fun g f => funext fun x =>
      GroundTheory.Automorphic.AutomorphicForm.constantTerm_rightTranslate f.1.1 (finGL E n (locGL E n w g)) x)
    (by rw [hF]; exact fun h => h0 (Subtype.ext h))
  rw [hF] at h2
  exact IsSatVecGL.of_map (Sm E n).subtype (fun _ _ => rfl) Subtype.val_injective h2
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host
open GlobalTheory.PRep (fixed)

namespace UpperTheory.V.Cj.S

theorem hkSum : HkSum := by
  intro E _ _ w n V _ _ ρ ϖ hϖ hu _ j hj x hx
  classical
  have hr := satake_range_eq (n := n) w hϖ hu Final.TjCosets hj
  unfold heckeVec
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.univ.image (fun i : SatakeIdx w hϖ (n := n) j =>
      ((satakeB w hϖ hu i : GL (Fin n) (w.adicCompletion E)) :
        GL (Fin n) (w.adicCompletion E) ⧸ KGL w (n := n)))) ?_]
  · rw [Finset.sum_image (fun i _ i' _ h => satakeB_inj w hϖ hu h)]
    refine Finset.sum_congr rfl fun i _ => ?_
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (KGL w (n := n)) (satakeB w hϖ hu i)
    have hfix : ρ (k : GL (Fin n) (w.adicCompletion E)) x = x := GlobalTheory.LGrp.mem_fixed.1 hx _ k.2
    rw [hk, satake_Tj_eq, Set.indicator_of_mem (satake_Tset_right w (satakeB_mem w hϖ hu i) k.2),
      Pi.one_apply, one_smul, map_mul, Module.End.mul_apply, hfix]
  · intro y hy
    have hT : Tj ℂ n (Ov E w) ϖ j y.out ≠ 0 := fun h0 => hy (by simp only [h0, zero_smul])
    have hy' : y ∈ Set.range _ := hr.ge ((satake_Tj_ne_zero_iff w ℂ ϖ j _).1 hT)
    obtain ⟨i, rfl⟩ := hy'
    exact Finset.mem_coe.2 (Finset.mem_image_of_mem _ (Finset.mem_univ i))

end UpperTheory.V.Cj.S
end
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

section

open UpperTheory.V

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

private theorem hull_stable {T : Module.End ℂ (Sm E a)} (hT : T ∈ Comm E a) (S : Submodule ℂ (Sm E a)) :
    ∀ φ ∈ hull S, T φ ∈ hull S := by
  have : hull S ≤ (hull S).comap T := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨T', hT', φ, hφ, rfl⟩
    exact Submodule.subset_span ⟨T * T', ⟨fun k => (hT.1 k).mul_left (hT'.1 k),
      fun z hz => (hT.2.1 z hz).mul_left (hT'.2.1 z hz), fun ψ h => hT.2.2 _ (hT'.2.2 ψ h)⟩, φ, hφ, rfl⟩
  exact fun φ hφ => this hφ

private theorem aut_cap (t : E →+* ℂ) (u : ℂ) (φ : Sm E a) (h : IsAutForm φ) : IsAutForm (cap t u φ) := by
  obtain ⟨p, -, q, -, e⟩ := Cm.mem_Zalg_iff.1 (Cm.cap_mem_Zalg (a := a) t u)
  obtain ⟨ψ, rfl⟩ := Cm.mem_range_ofAut.2 h
  refine Cm.mem_range_ofAut.1 ⟨GroundTheory.Automorphic.AutomorphicForm.uActionAF E a p ψ +
    Complex.I • GroundTheory.Automorphic.AutomorphicForm.uActionAF E a q ψ, ?_⟩
  rw [e, map_add (f := _), map_smul]
  rfl

private theorem smEq_fin (g : GL (Fin a) (Af E)) (φ : Sm E a) :
    Cm.smEq E a (finRep E a g φ) = GroundTheory.Automorphic.AutomorphicForm.rtFin g (Cm.smEq E a φ) :=
  Subtype.ext (funext fun x => (congrArg (fun f : GL (Fin a) (Af E) →* GA E a => φ.1 (x * f g)) Fb.finEmb_eq).symm)

private theorem fin_mem (g : GL (Fin a) (Af E)) : finRep E a g ∈ Comm E a := by
  refine ⟨fun k => ?_, fun z _ => ?_, fun φ h => ?_⟩
  · exact Commute.map (show Commute (finGL E a g) (infGL E a (Unitary.toUnits k)) from (infGL_comm _ _).symm) (rt E a)
  · refine LinearMap.ext fun φ => (Cm.smEq E a).injective ?_
    rw [Module.End.mul_apply, Module.End.mul_apply, smEq_fin, Cm.smEq_uTC, Cm.smEq_uTC, smEq_fin,
      GroundTheory.Automorphic.AutomorphicForm.uAction_rtFin]
  · refine (Cm.isAutForm_iff _).2 ?_
    rw [← Cm.coe_smEq, smEq_fin]
    exact ((Cm.isAutForm_iff _).1 h).rightTranslate_finEmb g

end

theorem UpperTheory.V.Cj.S.hullOps :
    UpperTheory.V.Cj.S.CapAct → UpperTheory.V.Cj.S.HullOps := by
  intro hc E _ _ _ a S
  refine ⟨fun φ hφ => Submodule.subset_span ⟨1, ⟨fun _ => Commute.one_left _, fun _ _ => Commute.one_left _,
    fun _ h => h⟩, φ, hφ, rfl⟩, fun t u => hull_stable ⟨fun k => (hc E a t u).2.1 (.cpt k),
      fun z _ => (hc E a t u).2.2.1 z, aut_cap t u⟩ S, fun g => hull_stable (fin_mem g) S⟩
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

theorem UpperTheory.V.Cj.S.step :
    UpperTheory.V.Cj.S.PairEig → UpperTheory.V.Cj.S.SliceBdd → UpperTheory.V.Cj.S.Iwa → UpperTheory.V.Cj.S.CtCap → UpperTheory.V.Cj.S.CtSat → UpperTheory.V.Cj.S.CapRel → UpperTheory.V.Cj.S.HkRel → UpperTheory.V.Cj.S.CapArith → UpperTheory.V.Cj.S.SatArith → UpperTheory.V.Cj.S.Step := by
  intro hPair hSlice hIwa hCtCap hCtSat hCapRel hHkRel hCapA hSatA E _ _ _ r s φ₀ m B h₀ hne₀
  obtain ⟨φ, hφ, hne⟩ := hIwa E r s φ₀ m B h₀ hne₀
  obtain ⟨S₁, S₂, hS₁, hS₂, hs₁, hs₂⟩ := hSlice E r s φ hφ.aut
  obtain ⟨ψ, hψ, hNI, hcap⟩ := hCtCap E (r + s) r φ hφ.aut
  rw [← hψ] at hne hs₁ hs₂
  have hψ0 : ψ ≠ 0 := by
    rintro rfl
    obtain ⟨x, y, h⟩ := hne
    exact h rfl
  obtain ⟨φ₁, φ₂, m₁, m₂, B₁, B₂, h₁, h₂, hc, hs⟩ := hPair E r s (res ψ.1) S₁ S₂ hS₁ hS₂ hne hs₁ hs₂
  refine ⟨φ₁, φ₂, m₁, m₂, B₁, B₂, h₁, h₂, fun t => ?_, fun ν ν' hν hν' => ?_⟩
  · refine hCapA (m t) (m₁ t) (m₂ t) _ _ fun u => ?_
    have e1 : u + ((-((s : ℝ) / 2) : ℝ) : ℂ) = u - (s : ℂ) / 2 := by push_cast; ring
    have e2 : u + (((r : ℝ) / 2 : ℝ) : ℂ) = u + (r : ℂ) / 2 := by push_cast; ring
    rw [e1, e2]
    refine hc t _ _ _ _ (hCapRel E r s ψ hNI t u) fun x y => ?_
    rw [hcap t u, (hφ.cap t).2 u, hψ]
    simp only [res, constantTerm, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
    exact MeasureTheory.integral_const_mul _ _
  · filter_upwards [hφ.sat, h₁.sat, h₂.sat, hs] with w hw hw₁ hw₂ hw₃
    have hv := hCtSat E (r + s) r φ ψ hφ.aut hψ hψ0 w (B w) hw
    obtain ⟨ϖ, hu⟩ := exists_isUnifV w
    refine hSatA (qV E w) r s (qV_ne_zero w) (B w) (B₁ w) (B₂ w) hw.2.2.1 hw₁.2.2.1 hw₂.2.2.1 (fun j hj => ?_) _ _ ?_ ?_
    · obtain ⟨G, hG, hsum⟩ := hHkRel E r s ψ hNI w hv.2.1 ϖ hu j hj
      refine hw₃ ϖ hu _ G _ hG fun x y => ?_
      rw [hsum x y]
      have : tOp (r + s) w hu j ψ = satEig (qV E w) (r + s) (B w) j • ψ := hv.2.2.2 ϖ hu j hj
      rw [this]
      rfl
    · rw [hν.2.1 w]
      congr 1
      push_cast; ring
    · rw [hν'.2.1 w]
      congr 1
      push_cast; ring
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

private theorem sum_map {ι α : Type} [Fintype ι] (f : α → α) (C : ι → Multiset α) :
    ∑ i, (C i).map f = (∑ i, C i).map f := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← Multiset.coe_mapAddMonoidHom, map_sum]

private theorem sat_twist {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} (π : CG E a) {w : Pl E}
    {B : Multiset ℂˣ} (h : π.HasSat w B) {χ : HChar E} (hχ : χ.UnrAt w) :
    (π.twist χ).HasSat w (B.map (· * χ.val w)) := by
  induction π using Quotient.inductionOn
  exact GlobalTheory.SphGal.hasSatGL_twist _ _ _ χ w B hχ h

theorem UpperTheory.V.Cj.S.suppTwist :
    UpperTheory.V.Cj.S.SuppTwist := by
  rintro E _ _ _ a k m B ⟨ι, _, n, π, μ, hk, hn, ha, hμ, hm, hB⟩ x ν hν
  refine ⟨ι, inferInstance, n, fun i => (π i).twist ν, fun i t => (μ i t).map (· + (x : ℂ)), hk, hn, ha,
    fun i t => ?_, fun t => ?_, hB.mono ?_⟩
  · have h := (hμ i t).twist ν
    rwa [(InfType.expo_of_infType E ν).2.1 x hν t] at h
  · rw [sum_map, hm]
  · rintro w ⟨C, hC, hs⟩
    exact ⟨fun i => (C i).map (· * ν.val w), fun i => sat_twist _ (hC i) (hν.1 w), by rw [sum_map, hs]⟩
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

theorem UpperTheory.V.Cj.S.iwa :
    UpperTheory.V.Cj.S.RtK → UpperTheory.V.Cj.S.Iwa := by
  intro hK E _ _ _ r s φ m B hφ ⟨g, hg⟩
  obtain ⟨b, hb, k, hk, rfl⟩ := GroundTheory.Automorphic.Reduction.exists_adelicBorel_mul_maxCompact (K := E) (n := r + s) g
  obtain ⟨X, m₁, m₂, rfl⟩ := UpperTheory.upperTriangular_eq_unipotent_mul_levi _ r s b (GroundTheory.Automorphic.Reduction.mem_adelicBorel.1 hb)
  refine ⟨_, hK E (r + s) φ m B hφ k hk, m₁, m₂, ?_⟩
  have hl : GroundTheory.Automorphic.AutomorphicForm.IsLeftInvariant φ.1 := hφ.aut.left
  rw [mul_assoc, UpperTheory.constantTerm_unipotent_left_invariant E (r + s) r φ.1 hl] at hg
  rw [← GroundTheory.Automorphic.AutomorphicForm.constantTerm_rightTranslate] at hg
  exact hg
end
