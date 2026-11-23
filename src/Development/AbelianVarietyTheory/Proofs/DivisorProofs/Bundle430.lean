module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.TensorProduct.Maps
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle298
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsZmodActionModelOfIsColimitFiltered
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle299
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle372
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle187
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle306
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormIteratedFDerivRemCompLe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle198
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.RingHom.Etale
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsRegularRingOfSmooth
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsWeaklyRegularMapCAppendMapLinForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle373
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Filtered.Final
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Polynomial
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
import Development.AbelianVarietyTheory.Definitions.Divisors.KerIdealCompOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle005
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.RingTheory.Artinian.Defs
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.Artinian.Ring
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003

@[expose] public section

section

open CategoryTheory Limits TensorProduct

namespace GlobalTheory.BijDescent

theorem exists_stage_isIso {K : Type} [SmallCategory K] [IsFiltered K]
    {R₀ A B : CommRingCat.{0}} (P EA EB : K ⥤ CommRingCat.{0}) (β : ∀ k, R₀ ⟶ P.obj k)
    (fA : R₀ ⟶ A) (fB : R₀ ⟶ B) (hA : fA.hom.FinitePresentation)
    (hB : fB.hom.FinitePresentation) (g : A ⟶ B) (hg : fA ≫ g = fB)
    (uA : P ⟶ EA) (vA : (Functor.const K).obj A ⟶ EA) (uB : P ⟶ EB)
    (vB : (Functor.const K).obj B ⟶ EB)
    (hpoA : ∀ k, IsPushout fA (β k) (vA.app k) (uA.app k))
    (hpoB : ∀ k, IsPushout fB (β k) (vB.app k) (uB.app k))
    (cA : Cocone EA) (hcA : IsColimit cA) (cB : Cocone EB) (hcB : IsColimit cB)
    (iA : A ⟶ cA.pt) (iB : B ⟶ cB.pt) (hiA : ∀ k, vA.app k ≫ cA.ι.app k = iA)
    (hiB : ∀ k, vB.app k ≫ cB.ι.app k = iB) (G : cA.pt ⟶ cB.pt) [IsIso G]
    (hG : ∀ k, (hpoA k).desc (g ≫ vB.app k) (uB.app k)
      (by rw [reassoc_of% hg, (hpoB k).w]) ≫ cB.ι.app k = cA.ι.app k ≫ G) :
    ∃ m : K, ∀ (l : K) (_ : m ⟶ l), IsIso ((hpoA l).desc (g ≫ vB.app l) (uB.app l)
      (by rw [reassoc_of% hg, (hpoB l).w])) := by
  let gs : ∀ k, EA.obj k ⟶ EB.obj k := fun k =>
    (hpoA k).desc (g ≫ vB.app k) (uB.app k) (by rw [reassoc_of% hg, (hpoB k).w])
  have gv : ∀ k, vA.app k ≫ gs k = g ≫ vB.app k := fun k => (hpoA k).inl_desc _ _ _
  have gu : ∀ k, uA.app k ≫ gs k = uB.app k := fun k => (hpoA k).inr_desc _ _ _
  have vAn : ∀ {k l} (f : k ⟶ l), vA.app k ≫ EA.map f = vA.app l := fun f =>
    (vA.naturality f).symm.trans (Category.id_comp _)
  have vBn : ∀ {k l} (f : k ⟶ l), vB.app k ≫ EB.map f = vB.app l := fun f =>
    (vB.naturality f).symm.trans (Category.id_comp _)
  have gnat : ∀ {k l} (f : k ⟶ l), EA.map f ≫ gs l = gs k ≫ EB.map f := by
    intro k l f
    apply (hpoA k).hom_ext
    · rw [reassoc_of% (vAn f), gv, reassoc_of% (gv k), vBn]
    · rw [← uA.naturality_assoc, gu, reassoc_of% (gu k), uB.naturality]
  obtain ⟨k₀⟩ := IsFiltered.nonempty (C := K)
  have hAG : iA ≫ G = g ≫ iB := by
    rw [← hiA k₀, Category.assoc, ← hG, reassoc_of% (gv k₀), hiB]
  let αA : (Functor.const K).obj R₀ ⟶ EA := (Functor.const K).map fA ≫ vA
  let αB : (Functor.const K).obj R₀ ⟶ EB := (Functor.const K).map fB ≫ vB
  obtain ⟨m, s, hs⟩ := GlobalTheory.TorsorColim.exists_stage_factor (I := Unit) EA αA fB cA hcA hB
    (fun _ => iB ≫ inv G) (fun _ k => by
      change fB ≫ iB ≫ inv G = (fA ≫ vA.app k) ≫ cA.ι.app k
      rw [Category.assoc, hiA, ← hg, Category.assoc, ← reassoc_of% hAG, IsIso.hom_inv_id,
        Category.comp_id])
  have hs1 : fB ≫ s () = fA ≫ vA.app m := (hs ()).1
  have hs2 : s () ≫ cA.ι.app m = iB ≫ inv G := (hs ()).2
  obtain ⟨m₁, p₁, hp₁⟩ := GlobalTheory.TorsorColim.exists_stage_eq (I := Unit) EA αA fA cA hcA
    (RingHom.FiniteType.essFiniteType (RingHom.FiniteType.of_finitePresentation hA)) (k := m)
    (fun _ => g ≫ s ()) (fun _ => vA.app m) (fun _ => by rw [reassoc_of% hg, hs1]; rfl)
    (fun _ => rfl) (fun _ => by
      rw [Category.assoc, hs2, hiA, ← reassoc_of% hAG, IsIso.hom_inv_id, Category.comp_id])
  obtain ⟨m₂, p₂, hp₂⟩ := GlobalTheory.TorsorColim.exists_stage_eq (I := Unit) EB αB fB cB hcB
    (RingHom.FiniteType.essFiniteType (RingHom.FiniteType.of_finitePresentation hB)) (k := m)
    (fun _ => s () ≫ gs m) (fun _ => vB.app m)
    (fun _ => by
      change fB ≫ s () ≫ gs m = fB ≫ vB.app m
      rw [reassoc_of% hs1, gv, reassoc_of% hg])
    (fun _ => rfl) (fun _ => by
      rw [Category.assoc, hG, reassoc_of% hs2, IsIso.inv_hom_id, Category.comp_id, hiB])
  let a := IsFiltered.leftToMax m₁ m₂
  let b := IsFiltered.rightToMax m₁ m₂
  let e := IsFiltered.coeqHom (p₁ ≫ a) (p₂ ≫ b)
  have he : (p₁ ≫ a) ≫ e = (p₂ ≫ b) ≫ e := IsFiltered.coeq_condition _ _
  refine ⟨IsFiltered.coeq (p₁ ≫ a) (p₂ ≫ b), fun l f => ?_⟩
  obtain ⟨F', hF'⟩ : ∃ F' : m ⟶ l, F' = (p₁ ≫ a) ≫ e ≫ f := ⟨_, rfl⟩
  have h₁ : g ≫ s () ≫ EA.map F' = vA.app l := by
    subst hF'
    have := hp₁ ()
    simp only [Category.assoc] at this
    rw [← vAn ((p₁ ≫ a) ≫ e ≫ f)]
    simp only [EA.map_comp, Category.assoc]
    rw [reassoc_of% this]
  have h₂ : s () ≫ gs m ≫ EB.map F' = vB.app l := by
    subst hF'
    have := hp₂ ()
    simp only [Category.assoc] at this
    rw [← Category.assoc (p₁ ≫ a), he, ← vBn ((p₂ ≫ b) ≫ e ≫ f)]
    simp only [EB.map_comp, Category.assoc]
    rw [reassoc_of% this]
  let σ : EB.obj l ⟶ EA.obj l := (hpoB l).desc (s () ≫ EA.map F') (uA.app l)
    (by rw [reassoc_of% hs1, vAn, (hpoA l).w])
  have σv : vB.app l ≫ σ = s () ≫ EA.map F' := (hpoB l).inl_desc _ _ _
  have σu : uB.app l ≫ σ = uA.app l := (hpoB l).inr_desc _ _ _
  refine ⟨σ, ?_, ?_⟩
  · apply (hpoA l).hom_ext
    · change vA.app l ≫ gs l ≫ σ = _
      rw [reassoc_of% (gv l), σv, h₁, Category.comp_id]
    · change uA.app l ≫ gs l ≫ σ = _
      rw [reassoc_of% (gu l), σu, Category.comp_id]
  · apply (hpoB l).hom_ext
    · change vB.app l ≫ σ ≫ gs l = _
      rw [reassoc_of% σv, gnat, h₂, Category.comp_id]
    · change uB.app l ≫ σ ≫ gs l = _
      rw [reassoc_of% σu, gu, Category.comp_id]

end GlobalTheory.BijDescent

namespace GlobalTheory.BijDescent

theorem bijective_of_isColimit : ∀ (J : Type) [SmallCategory J] [IsFiltered J] (F : J ⥤ CommRingCat.{0}) (c : Cocone F),
    IsColimit c → ∀ (j : J) (R S : Type) [CommRing R] [CommRing S]
    [Algebra (F.obj j) R] [Algebra (F.obj j) S] [Algebra.FinitePresentation (F.obj j) R]
    [Algebra.FinitePresentation (F.obj j) S] (φ : R →ₐ[F.obj j] S), φ.toRingHom.Finite →
    (letI : Algebra (F.obj j) c.pt := (c.ι.app j).hom.toAlgebra;
      Function.Bijective (Algebra.TensorProduct.map (AlgHom.id c.pt c.pt) φ)) →
    ∃ (k₀ : J) (f₀ : j ⟶ k₀), ∀ (k : J) (f : k₀ ⟶ k),
      letI : Algebra (F.obj j) (F.obj k) := (F.map (f₀ ≫ f)).hom.toAlgebra;
      Function.Bijective (Algebra.TensorProduct.map (AlgHom.id (F.obj k) (F.obj k)) φ) := by
  intro J _ _ F c hc j R S _ _ _ _ _ _ φ _ hbij
  letI : Algebra (F.obj j) c.pt := (c.ι.app j).hom.toAlgebra
  let fR : F.obj j ⟶ CommRingCat.of R := CommRingCat.ofHom (algebraMap (F.obj j) R)
  let fS : F.obj j ⟶ CommRingCat.of S := CommRingCat.ofHom (algebraMap (F.obj j) S)
  have hfR : fR.hom.FinitePresentation := RingHom.finitePresentation_algebraMap.2 inferInstance
  have hfS : fS.hom.FinitePresentation := RingHom.finitePresentation_algebraMap.2 inferInstance
  let g : CommRingCat.of R ⟶ CommRingCat.of S := CommRingCat.ofHom φ.toRingHom
  have hg : fR ≫ g = fS := by ext x; exact φ.commutes x
  have sqR := (CommRingCat.isPushout_tensorProduct (F.obj j) c.pt R).flip
  have sqS := (CommRingCat.isPushout_tensorProduct (F.obj j) c.pt S).flip
  obtain ⟨ER, ιR, uR, vR, ⟨hER⟩, hkR⟩ :=
    GlobalTheory.BaseChangeColim.exists_isColimit_pushout_under J F c hc j _ _ fR _ _ sqR
  obtain ⟨ES, ιS, uS, vS, ⟨hES⟩, hkS⟩ :=
    GlobalTheory.BaseChangeColim.exists_isColimit_pushout_under J F c hc j _ _ fS _ _ sqS
  let G : CommRingCat.of (c.pt ⊗[F.obj j] R) ⟶ CommRingCat.of (c.pt ⊗[F.obj j] S) :=
    CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id c.pt c.pt) φ).toRingHom
  haveI : IsIso G := (ConcreteCategory.isIso_iff_bijective G).2 hbij
  have hGr : g ≫ CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := F.obj j) (A := c.pt) (B := S)).toRingHom =
      CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := F.obj j) (A := c.pt) (B := R)).toRingHom ≫ G := by
    ext x; simp [g, G]
  obtain ⟨m, hm⟩ := exists_stage_isIso (K := Under j) (Under.forget j ⋙ F) ER ES
    (fun k => F.map k.hom) fR fS hfR hfS g hg uR vR uS vS (fun k => (hkR k).1) (fun k => (hkS k).1)
    (Cocone.mk _ ιR) hER (Cocone.mk _ ιS) hES _ _ (fun k => (hkR k).2.1) (fun k => (hkS k).2.1) G
    (fun k => by
      have key : ∀ d : ER.obj k ⟶ ES.obj k, vR.app k ≫ d = g ≫ vS.app k →
          uR.app k ≫ d = uS.app k → d ≫ ιS.app k = ιR.app k ≫ G := by
        intro d hd1 hd2
        apply (hkR k).1.hom_ext
        · rw [reassoc_of% hd1, (hkS k).2.1, reassoc_of% (hkR k).2.1, hGr]
        · change uR.app k ≫ d ≫ ιS.app k = uR.app k ≫ ιR.app k ≫ G
          erw [reassoc_of% hd2, (hkS k).2.2, reassoc_of% (hkR k).2.2]
          ext x
          simp [G]
      exact key _ ((hkR k).1.inl_desc _ _ _) ((hkR k).1.inr_desc _ _ _))
  refine ⟨m.right, m.hom, fun k f => ?_⟩
  let l : Under j := Under.mk (m.hom ≫ f)
  obtain ⟨d, hd1, hd2, hdiso⟩ : ∃ d : ER.obj l ⟶ ES.obj l, vR.app l ≫ d = g ≫ vS.app l ∧
      uR.app l ≫ d = uS.app l ∧ IsIso d :=
    ⟨_, (hkR l).1.inl_desc _ _ _, (hkR l).1.inr_desc _ _ _, hm l (Under.homMk f rfl)⟩
  letI : Algebra (F.obj j) (F.obj k) := (F.map (m.hom ≫ f)).hom.toAlgebra
  have tR := (CommRingCat.isPushout_tensorProduct (F.obj j) (F.obj k) R).flip
  have tS := (CommRingCat.isPushout_tensorProduct (F.obj j) (F.obj k) S).flip
  let M : CommRingCat.of (F.obj k ⊗[F.obj j] R) ⟶ CommRingCat.of (F.obj k ⊗[F.obj j] S) :=
    CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id (F.obj k) (F.obj k)) φ).toRingHom
  have hM : M = ((hkR l).1.isoIsPushout _ _ tR).inv ≫ d ≫ ((hkS l).1.isoIsPushout _ _ tS).hom := by
    apply tR.hom_ext
    · erw [IsPushout.inl_isoIsPushout_inv_assoc _ _ (hkR l).1 tR, reassoc_of% hd1,
        IsPushout.inl_isoIsPushout_hom _ _ (hkS l).1 tS]
      ext x
      simp [M, g]
    · erw [IsPushout.inr_isoIsPushout_inv_assoc _ _ (hkR l).1 tR, reassoc_of% hd2,
        IsPushout.inr_isoIsPushout_hom _ _ (hkS l).1 tS]
      ext x
      simp [M]
  haveI : IsIso M := by rw [hM]; infer_instance
  exact (ConcreteCategory.isIso_iff_bijective M).1 this

end GlobalTheory.BijDescent
end

section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory.PerfectProj

theorem exists_pow_prime_pow_kill (p : ℕ) (hp : 1 < p) (k B : Type) [Field k] [CommRing B]
    [Algebra k B] [Module.Finite k B] :
    ∃ r : ℕ, ∀ x : B, IsNilpotent x → x ^ (p ^ r) = 0 := by
  haveI : IsArtinianRing B := IsArtinianRing.of_finite k B
  obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_nilradical (R := B)
  refine ⟨n, fun x hx => ?_⟩
  have hmem : x ^ n ∈ (nilradical B) ^ n := Ideal.pow_mem_pow (mem_nilradical.mpr hx) n
  rw [hn, Ideal.zero_eq_bot, Ideal.mem_bot] at hmem
  exact pow_eq_zero_of_le (Nat.lt_pow_self hp).le hmem

theorem exists_eq_pow_prime_pow (p : ℕ) {A : Type} [CommRing A] (π : A → A)
    (h : ∀ a, ∃ b, π a = π b ^ p) : ∀ (m : ℕ) (a : A), ∃ b, π a = π b ^ (p ^ m) := by
  intro m
  induction m with
  | zero => intro a; exact ⟨a, by simp⟩
  | succ m ih =>
    intro a
    obtain ⟨b, hb⟩ := ih a
    obtain ⟨c, hc⟩ := h b
    exact ⟨c, by rw [hb, hc, ← pow_mul, pow_succ']⟩

theorem natural_idempotent_reduced : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] (A B : Type) [CommRing A] [Algebra k A] [CommRing B] [Algebra k B] [Module.Finite k B] (π : A →ₐ[k] A) (π' : B →ₐ[k] B), ((∀ a : A, IsNilpotent (a - π a)) ∧ ∀ a : A, ∃ b : A, π a = π b ^ p) → ((∀ a : B, IsNilpotent (a - π' a)) ∧ ∀ a : B, ∃ b : B, π' a = π' b ^ p) → (∀ (f : A →ₐ[k] B) (a : A), f (π a) = π' (f a)) ∧ (∀ b, π' (π' b) = π' b) ∧ ∀ b, IsNilpotent (π' b) → π' b = 0 := by
  intro p _ k _ _ A B _ _ _ _ _ π π' hA hB
  rcases subsingleton_or_nontrivial B with hs | hs
  · exact ⟨fun _ _ => Subsingleton.elim _ _, fun _ => Subsingleton.elim _ _,
      fun _ _ => Subsingleton.elim _ _⟩
  haveI : CharP B p := charP_of_injective_algebraMap (algebraMap k B).injective p
  obtain ⟨r, hr⟩ := exists_pow_prime_pow_kill p (Fact.out : p.Prime).one_lt k B
  have iA := exists_eq_pow_prime_pow p π hA.2 r
  have iB := exists_eq_pow_prime_pow p π' hB.2 r
  have h3 : ∀ b, IsNilpotent (π' b) → π' b = 0 := by
    intro b hb
    obtain ⟨c, hc⟩ := iB b
    rw [hc] at hb ⊢
    exact hr _ hb.of_pow
  refine ⟨fun f a => ?_, fun y => ?_, h3⟩
  · obtain ⟨b, hb⟩ := iA a
    obtain ⟨c, hc⟩ := iB (f a)
    have hd : IsNilpotent (f (π a) - π' (f a)) := by
      have h1 : IsNilpotent (f (a - π a)) := (hA.1 a).map f
      have h2 := hB.1 (f a)
      have e : f (π a) - π' (f a) = (f a - π' (f a)) - f (a - π a) := by rw [map_sub]; ring
      rw [e]
      exact (Commute.all _ _).isNilpotent_sub h2 h1
    have he : f (π a) - π' (f a) = (f (π b) - π' c) ^ (p ^ r) := by
      rw [sub_pow_char_pow, hb, hc, map_pow]
    rw [he] at hd
    exact sub_eq_zero.mp (he.trans (hr _ hd.of_pow))
  · obtain ⟨c, hc⟩ := iB y
    have he : π' (π' y) - π' y = (π' (π' c) - π' c) ^ (p ^ r) := by
      rw [sub_pow_char_pow, hc, map_pow]
    have hn : IsNilpotent (π' (π' c) - π' c) := by
      rw [← neg_sub]; exact (hB.1 (π' c)).neg
    exact sub_eq_zero.mp (he.trans (hr _ hn))

end GlobalTheory.PerfectProj
end

section

open MvPolynomial TensorProduct

namespace GlobalTheory

theorem isRegularRing_quotient_etaleCoordinate : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A]
    [Algebra (ZMod p) A] {n : ℕ} (t : Fin n → A), (MvPolynomial.aeval (R := ZMod p) t).toRingHom.Etale →
    ∀ j : Fin n, IsRegularRing (A ⧸ Ideal.span {t j}) := by
  intro p _ A _ _ n t het j
  let B := MvPolynomial (Fin n) (ZMod p)
  letI : Algebra B A := (MvPolynomial.aeval (R := ZMod p) t).toRingHom.toAlgebra
  have : Algebra.Etale B A := het
  let I : Ideal B := Ideal.span (X '' ({j} : Set (Fin n)))
  have hQ : IsRegularRing (B ⧸ I) :=
    IsRegularRing.of_ringEquiv (quotientSpanXEquiv (ZMod p) ({j} : Set (Fin n))).symm.toRingEquiv
  have : IsRegularRing (TensorProduct B (B ⧸ I) A) := isRegularRing_of_etale (B ⧸ I) _
  have hI : I.map (algebraMap B A) = Ideal.span {t j} := by
    simp only [I, Set.image_singleton, Ideal.map_span, Set.image_singleton]
    congr 2
    show MvPolynomial.aeval t (X j) = t j
    simp
  have e := (Algebra.TensorProduct.quotIdealMapEquivTensorQuot A I).toRingEquiv.trans
    (Algebra.TensorProduct.comm B A (B ⧸ I)).toRingEquiv
  rw [hI] at e
  exact IsRegularRing.of_ringEquiv e.symm

end GlobalTheory
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.PowCancel

def linMapPiEquiv (R : Type) [Ring R] (X M : Type) [AddCommGroup X] [Module R X]
    [AddCommGroup M] [Module R M] (l : ℕ) :
    (X →ₗ[R] (Fin l → M)) ≃ (Fin l → (X →ₗ[R] M)) where
  toFun f i := (LinearMap.proj i).comp f
  invFun g := LinearMap.pi g
  left_inv f := by ext x i; rfl
  right_inv g := by funext i; ext x; rfl

theorem card_linMap_pow (R : Type) [Ring R] (X M : Type) [AddCommGroup X] [Module R X]
    [AddCommGroup M] [Module R M] (l : ℕ) :
    Nat.card (X →ₗ[R] (Fin l → M)) = Nat.card (X →ₗ[R] M) ^ l := by
  rw [Nat.card_congr (linMapPiEquiv R X M l), Nat.card_fun, Nat.card_fin]

theorem cancel_pow : ∀ (R : Type) [Ring R] (M N : Type) [AddCommGroup M] [Module R M] [Finite M]
    [AddCommGroup N] [Module R N] [Finite N] (l : ℕ), 0 < l →
    Nonempty ((Fin l → M) ≃ₗ[R] (Fin l → N)) → Nonempty (M ≃ₗ[R] N) := by
  intro R _ M N _ _ _ _ _ _ l hl ⟨e⟩
  refine GlobalTheory.T.nonempty_linearEquiv_of_card_hom_eq R M N ?_
  intro X _ _ _
  have h1 : Nat.card (X →ₗ[R] (Fin l → M)) = Nat.card (X →ₗ[R] (Fin l → N)) :=
    Nat.card_congr
      { toFun := fun f => e.toLinearMap.comp f
        invFun := fun g => e.symm.toLinearMap.comp g
        left_inv := fun f => by ext x; simp
        right_inv := fun g => by ext x; simp }
  rw [card_linMap_pow, card_linMap_pow] at h1
  exact Nat.pow_left_injective hl.ne' h1

end GlobalTheory.PowCancel
end

section

namespace GlobalTheory.LatticeComb
open scoped SchwartzMap

theorem comb_unique : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (P : LinearMap.BilinForm ℝ V), P.Nondegenerate →
    ∀ (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ] (a : V) (T : SchwartzMap V ℂ →L[ℂ] ℂ),
    (∀ l ∈ Λ, ∀ f f' : SchwartzMap V ℂ, (∀ x, f' x = f (x + l)) → T f' = T f) →
    (∀ μ : V, (∀ l ∈ Λ, ∃ k : ℤ, P l μ = k) → ∀ f f' : SchwartzMap V ℂ,
      (∀ x, f' x = Complex.exp (2 * Real.pi * Complex.I * (P x μ : ℂ)) * f x) →
      T f' = Complex.exp (2 * Real.pi * Complex.I * (P a μ : ℂ)) * T f) →
    ∃ c : ℂ, ∀ f : SchwartzMap V ℂ, T f = c * ∑' l : Λ, f (a + l) := by
  intro V _ _ _ P hP Λ _ _ a T htr hmod
  obtain ⟨h, hhc, hh1⟩ := GlobalTheory.T.exists_schwartz_partition_of_unity_lattice Λ
  refine ⟨T h, fun f => ?_⟩
  have hth : ∀ l : Λ, (fun x => h (x + (l : V))).HasTemperateGrowth := fun l =>
    HasCompactSupport.hasTemperateGrowth (hhc.comp_homeomorph (Homeomorph.addRight (l : V)))
      ((h.smooth ⊤).comp (contDiff_id.add contDiff_const))
  have hh : (⇑h).HasTemperateGrowth := HasCompactSupport.hasTemperateGrowth hhc (h.smooth ⊤)
  let u : Λ → 𝓢(V, ℂ) := fun l => SchwartzMap.smulLeftCLM ℂ (fun x => h (x + (l : V))) f
  have hu : ∀ (l : Λ) (x : V), u l x = h (x + l) * f x := fun l x => by
    simp [u, SchwartzMap.smulLeftCLM_apply_apply (hth l)]
  obtain ⟨F1, hF1p, hF1T⟩ := GlobalTheory.T.summable_schwartz_series u (GlobalTheory.T.lattice_translates_cutoff_summable Λ h f hhc u hu)
  have hF1 : F1 = f := by
    ext x
    refine (hF1p x).unique ?_
    simpa [hu] using (hh1 x).mul_right (f x)
  let w : Λ → 𝓢(V, ℂ) := fun l => SchwartzMap.smulLeftCLM ℂ (⇑h) (SchwartzMap.compSubConstCLM ℂ (l : V) f)
  have hw : ∀ (l : Λ) (x : V), w l x = h x * f (x - l) := fun l x => by
    simp [w, SchwartzMap.smulLeftCLM_apply_apply hh]
  have huw : ∀ l, T (u l) = T (w l) := fun l =>
    htr l l.2 (w l) (u l) (fun x => by rw [hu, hw]; simp)
  obtain ⟨G, hGp, hGT⟩ := GlobalTheory.T.summable_schwartz_series w (GlobalTheory.T.lattice_shifted_cutoff_summable Λ h f hhc w hw)
  have h1 : T f = T G := by
    have := hF1T T
    rw [hF1] at this
    simp_rw [huw] at this
    exact this.unique (hGT T)
  obtain ⟨c, hcs, hcP⟩ := GlobalTheory.T.lattice_dual_fourier_expansion_schwartz P hP Λ f
  have hch : ∀ μ : V, (fun x : V => Complex.exp (2 * Real.pi * Complex.I * (P x μ : ℂ))).HasTemperateGrowth := by
    intro μ
    have e : (fun x : V => Complex.exp (2 * Real.pi * Complex.I * (P x μ : ℂ))) =
        fun x : V => Complex.exp ((Complex.I * ((2 * Real.pi : ℝ) : ℂ)) *
          ((LinearMap.toContinuousLinearMap (P.flip μ) x : ℝ) : ℂ)) := by
      funext x
      simp only [LinearMap.coe_toContinuousLinearMap']
      show _ = Complex.exp (Complex.I * ((2 * Real.pi : ℝ) : ℂ) * ((P x μ : ℝ) : ℂ))
      push_cast; ring_nf
    rw [e]
    exact GlobalTheory.CharFormDeriv.hasTemperateGrowth_char (LinearMap.toContinuousLinearMap (P.flip μ)) (2 * Real.pi)
  let v0 : V → 𝓢(V, ℂ) := fun μ => SchwartzMap.smulLeftCLM ℂ (fun x : V => Complex.exp (2 * Real.pi * Complex.I * (P x μ : ℂ))) h
  have hv0 : ∀ μ x, v0 μ x = Complex.exp (2 * Real.pi * Complex.I * (P x μ : ℂ)) * h x := fun μ x => by
    simp [v0, SchwartzMap.smulLeftCLM_apply_apply (hch μ)]
  let v : {μ : V // ∀ l ∈ Λ, ∃ k : ℤ, P l μ = k} → 𝓢(V, ℂ) := fun μ => c μ • v0 μ
  have hvs : ∀ k n : ℕ, Summable (fun μ => SchwartzMap.seminorm ℂ k n (v μ)) := by
    intro k n
    obtain ⟨C, hC⟩ := GlobalTheory.T.modulated_schwartz_seminorm_polynomial P h v0 hv0 k n
    refine Summable.of_nonneg_of_le (fun μ => apply_nonneg _ _) (fun μ => ?_) ((hcs n).mul_left C)
    simp only [v, map_smul_eq_mul]
    calc ‖c μ‖ * SchwartzMap.seminorm ℂ k n (v0 μ) ≤ ‖c μ‖ * (C * (1 + ‖(μ : V)‖) ^ n) :=
          mul_le_mul_of_nonneg_left (hC μ) (norm_nonneg _)
      _ = C * (‖c μ‖ * (1 + ‖(μ : V)‖) ^ n) := by ring
  obtain ⟨G', hG'p, hG'T⟩ := GlobalTheory.T.summable_schwartz_series v hvs
  have hGG : G = G' := by
    ext x
    refine (hGp x).unique ?_
    have e1 : HasSum (fun μ : {μ : V // ∀ l ∈ Λ, ∃ k : ℤ, P l μ = k} => v μ x)
        (h x * ∑' l : Λ, f (x + l)) := by
      have := (hcP x).mul_left (h x)
      have hfun : (fun μ : {μ : V // ∀ l ∈ Λ, ∃ k : ℤ, P l μ = k} => v μ x) =
          fun μ : {μ : V // ∀ l ∈ Λ, ∃ k : ℤ, P l μ = k} => h x * (c μ * Complex.exp (2 * Real.pi * Complex.I * (P x μ : ℂ))) := by
        funext μ
        simp only [v, SchwartzMap.smul_apply, hv0, smul_eq_mul]
        ring
      rw [hfun]; exact this
    have e2 : h x * ∑' l : Λ, f (x + l) = G' x := e1.unique (hG'p x)
    rw [← e2]
    have hsum : Summable (fun l : Λ => h x * f (x - l)) := by simpa [hw] using (hGp x).summable
    have e3 : ∑' l : Λ, f (x + l) = ∑' l : Λ, f (x - l) := by
      rw [← (Equiv.neg Λ).tsum_eq]
      simp [sub_eq_add_neg]
    rw [e3, ← tsum_mul_left]
    simpa [hw] using hsum.hasSum
  have hTv : ∀ μ, T (v μ) = c μ * Complex.exp (2 * Real.pi * Complex.I * (P a μ : ℂ)) * T h := by
    intro μ
    simp only [v, map_smul, smul_eq_mul]
    rw [hmod μ μ.2 h (v0 μ) (hv0 μ)]
    ring
  have h2 := hG'T T
  simp_rw [hTv] at h2
  rw [h1, hGG, ← h2.tsum_eq, tsum_mul_right, (hcP a).tsum_eq, mul_comm]

end GlobalTheory.LatticeComb
end

section

open IsLocalRing TensorProduct

theorem _root_.GlobalTheory.T.exists_local_generators_jacobian_det_not_mem : ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsRegularRing Λ] [PerfectField (FractionRing Λ)] (σ : Type) [Finite σ] (Q : Ideal (MvPolynomial σ Λ)) [Q.IsPrime], (∀ a : Λ, MvPolynomial.C a ∈ Q → a = 0) → ∃ (h : ℕ) (f : Fin h → MvPolynomial σ Λ) (s : Fin h → σ) (g : MvPolynomial σ Λ), g ∉ Q ∧ (∀ j, f j ∈ Q) ∧ (∀ x ∈ Q, g * x ∈ Ideal.span (Set.range f)) ∧ (Matrix.of fun i j => MvPolynomial.pderiv (s i) (f j)).det ∉ Q := by
  first | exact @GlobalTheory.exists_generic_jacobian_data_of_prime | exact GlobalTheory.exists_generic_jacobian_data_of_prime | (intros; apply GlobalTheory.exists_generic_jacobian_data_of_prime <;> assumption)
end
