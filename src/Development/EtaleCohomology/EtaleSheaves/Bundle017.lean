module

public import Development.EtaleCohomology.EtaleSheaves.Bundle009
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.TypeStar

@[expose] public section

section

noncomputable section
open LateralTheory.E.t_E1Cut LateralTheory.E.LCSplitPf

namespace LateralTheory.E.TorEtPf

def LocalGlue : Prop := ∀ (S C ι : Type) [CommRing S] [CommRing C] [Algebra S C] [Fintype ι] [Nonempty ι] (f g : S),
  Ideal.span {f, g} = ⊤ →
  Nonempty (Localization.Away (algebraMap S C f) ≃ₐ[S] (ι → Localization.Away f)) →
  Nonempty (Localization.Away (algebraMap S C g) ≃ₐ[S] (ι → Localization.Away g)) →
  Algebra.Etale S C ∧ Module.Finite S C ∧ Function.Surjective (PrimeSpectrum.comap (algebraMap S C))

def LocF : Prop := ∀ (q : ℕ) [NeZero q] (S : Type) [CommRing S] (f g : S), Ideal.span {f, g} = ⊤ →
  ∀ (ε : ZMod q → Localization.Away (f * g)) (hε : CompleteOrthogonalIdempotents ε),
  letI := (torMap f g hε).toAlgebra
  Nonempty (Localization.Away (algebraMap S (Tor f g hε) f) ≃ₐ[S] (ZMod q → Localization.Away f))

def LocG : Prop := ∀ (q : ℕ) [NeZero q] (S : Type) [CommRing S] (f g : S), Ideal.span {f, g} = ⊤ →
  ∀ (ε : ZMod q → Localization.Away (f * g)) (hε : CompleteOrthogonalIdempotents ε),
  letI := (torMap f g hε).toAlgebra
  Nonempty (Localization.Away (algebraMap S (Tor f g hε) g) ≃ₐ[S] (ZMod q → Localization.Away g))

theorem surj_local (S C ι : Type) [CommRing S] [CommRing C] [Algebra S C] [Nonempty ι] (f : S)
    (e : Localization.Away (algebraMap S C f) ≃ₐ[S] (ι → Localization.Away f)) (p : PrimeSpectrum S) (hp : f ∉ p.asIdeal) :
    ∃ Q : PrimeSpectrum C, PrimeSpectrum.comap (algebraMap S C) Q = p := by
  have hr : p ∈ Set.range (PrimeSpectrum.comap (algebraMap S (Localization.Away f))) := by
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away f) f]; exact hp
  obtain ⟨P, hP⟩ := hr
  obtain ⟨i⟩ := ‹Nonempty ι›
  refine ⟨PrimeSpectrum.comap (algebraMap C (Localization.Away (algebraMap S C f)))
    (PrimeSpectrum.comap (e : Localization.Away (algebraMap S C f) →+* (ι → Localization.Away f))
      (PrimeSpectrum.comap (Pi.evalRingHom _ i) P)), ?_⟩
  rw [← hP]
  ext x
  simp only [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
  have : (e (algebraMap C (Localization.Away (algebraMap S C f)) (algebraMap S C x))) i = algebraMap S (Localization.Away f) x := by
    rw [← IsScalarTower.algebraMap_apply, AlgEquiv.commutes]; rfl
  simp only [RingHom.coe_coe, Pi.evalRingHom_apply, this]

theorem TorEt_of (hL : LocalGlue) (hF : LocF) (hG : LocG) : TorEt := by
  intro q _ S _ f g hfg ε hε
  letI := (torMap f g hε).toAlgebra
  exact hL S (Tor f g hε) (ZMod q) f g hfg (hF q S f g hfg ε hε) (hG q S f g hfg ε hε)

theorem surj_glue (S C ι : Type) [CommRing S] [CommRing C] [Algebra S C] [Nonempty ι] (f g : S) (hfg : Ideal.span {f, g} = ⊤)
    (ef : Localization.Away (algebraMap S C f) ≃ₐ[S] (ι → Localization.Away f))
    (eg : Localization.Away (algebraMap S C g) ≃ₐ[S] (ι → Localization.Away g)) :
    Function.Surjective (PrimeSpectrum.comap (algebraMap S C)) := by
  intro p
  by_cases hf : f ∈ p.asIdeal
  · have hg : g ∉ p.asIdeal := by
      intro hg
      apply p.isPrime.ne_top
      rw [eq_top_iff, ← hfg, Ideal.span_le]
      rintro x (rfl | rfl) <;> assumption
    exact surj_local S C ι g eg p hg
  · exact surj_local S C ι f ef p hf

def LocalEF : Prop := ∀ (S C ι : Type) [CommRing S] [CommRing C] [Algebra S C] [Fintype ι] [Nonempty ι] (f g : S),
  Ideal.span {f, g} = ⊤ →
  Nonempty (Localization.Away (algebraMap S C f) ≃ₐ[S] (ι → Localization.Away f)) →
  Nonempty (Localization.Away (algebraMap S C g) ≃ₐ[S] (ι → Localization.Away g)) →
  Algebra.Etale S C ∧ Module.Finite S C

theorem localGlue_of (h : LocalEF) : LocalGlue := by
  intro S C ι _ _ _ _ _ f g hfg ⟨ef⟩ ⟨eg⟩
  obtain ⟨h1, h2⟩ := h S C ι f g hfg ⟨ef⟩ ⟨eg⟩
  exact ⟨h1, h2, surj_glue S C ι f g hfg ef eg⟩

theorem TorEt_of' (hE : LocalEF) (hF : LocF) (hG : LocG) : TorEt := TorEt_of (localGlue_of hE) hF hG

theorem awayMap_eq (S C ι : Type) [CommRing S] [CommRing C] [Algebra S C] (f : S)
    (e : Localization.Away (algebraMap S C f) ≃ₐ[S] (ι → Localization.Away f)) :
    Localization.awayMap (algebraMap S C) f =
      (e.symm : (ι → Localization.Away f) →+* Localization.Away (algebraMap S C f)).comp
        (algebraMap (Localization.Away f) (ι → Localization.Away f)) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers f)
  ext s
  simp only [RingHom.comp_apply]
  rw [Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_eq]
  have h1 : algebraMap (Localization.Away f) (ι → Localization.Away f) (algebraMap S (Localization.Away f) s)
      = algebraMap S (ι → Localization.Away f) s := rfl
  rw [h1, RingHom.coe_coe, AlgEquiv.commutes]
  exact (IsScalarTower.algebraMap_apply S C (Localization.Away (algebraMap S C f)) s)

theorem away_prop (P : ∀ {R S : Type} [CommRing R] [CommRing S], (R →+* S) → Prop) (hP : RingHom.RespectsIso @P)
    (S C ι : Type) [CommRing S] [CommRing C] [Algebra S C] (f : S)
    (e : Localization.Away (algebraMap S C f) ≃ₐ[S] (ι → Localization.Away f))
    (hb : P (algebraMap (Localization.Away f) (ι → Localization.Away f))) :
    P (Localization.awayMap (algebraMap S C) f) := by
  rw [awayMap_eq S C ι f e]
  exact hP.1 _ e.symm.toRingEquiv hb

theorem localEF_of : LocalEF := by
  intro S C ι _ _ _ _ _ f g hfg ⟨ef⟩ ⟨eg⟩
  have key : ∀ (P : ∀ {R S : Type} [CommRing R] [CommRing S], (R →+* S) → Prop), RingHom.RespectsIso @P →
      RingHom.OfLocalizationSpan @P →
      (∀ h : S, P (algebraMap (Localization.Away h) (ι → Localization.Away h))) → P (algebraMap S C) := by
    intro P hP hL hb
    apply hL (algebraMap S C) {f, g} hfg
    rintro ⟨r, hr⟩
    rcases hr with rfl | rfl
    · exact away_prop P hP S C ι _ ef (hb _)
    · exact away_prop P hP S C ι _ eg (hb _)
  refine ⟨?_, ?_⟩
  · rw [← RingHom.etale_algebraMap]
    exact key _ RingHom.Etale.respectsIso RingHom.Etale.ofLocalizationSpan
      (fun h => RingHom.etale_algebraMap.mpr inferInstance)
  · rw [← RingHom.finite_algebraMap]
    exact key _ RingHom.finite_respectsIso RingHom.finite_ofLocalizationSpan
      (fun h => RingHom.finite_algebraMap.mpr inferInstance)

theorem TorEt_of'' (hF : LocF) (hG : LocG) : TorEt := TorEt_of' localEF_of hF hG

def pr1 {q : ℕ} [NeZero q] {S : Type} [CommRing S] (f g : S) {ε : ZMod q → Localization.Away (f * g)}
    (hε : CompleteOrthogonalIdempotents ε) : Tor f g hε →+* (ZMod q → Localization.Away f) :=
  (RingHom.fst _ _).comp (Tor f g hε).subtype

def ProjF : Prop := ∀ (q : ℕ) [NeZero q] (S : Type) [CommRing S] (f g : S), Ideal.span {f, g} = ⊤ →
  ∀ (ε : ZMod q → Localization.Away (f * g)) (hε : CompleteOrthogonalIdempotents ε),
  letI := (torMap f g hε).toAlgebra
  letI := (pr1 f g hε).toAlgebra
  IsLocalization.Away (algebraMap S (Tor f g hε) f) (ZMod q → Localization.Away f)

theorem locF_of (h : ProjF) : LocF := by
  intro q _ S _ f g hfg ε hε
  letI := (torMap f g hε).toAlgebra
  letI := (pr1 f g hε).toAlgebra
  haveI := h q S f g hfg ε hε
  let e := IsLocalization.algEquiv (Submonoid.powers (algebraMap S (Tor f g hε) f))
    (Localization.Away (algebraMap S (Tor f g hε) f)) (ZMod q → Localization.Away f)
  refine ⟨AlgEquiv.ofRingEquiv (f := e.toRingEquiv) (fun s => ?_)⟩
  have h1 : algebraMap S (Localization.Away (algebraMap S (Tor f g hε) f)) s =
      algebraMap (Tor f g hε) (Localization.Away (algebraMap S (Tor f g hε) f)) (torMap f g hε s) := rfl
  rw [AlgEquiv.coe_ringEquiv, h1, AlgEquiv.commutes]
  rfl

def pr2 {q : ℕ} [NeZero q] {S : Type} [CommRing S] (f g : S) {ε : ZMod q → Localization.Away (f * g)}
    (hε : CompleteOrthogonalIdempotents ε) : Tor f g hε →+* (ZMod q → Localization.Away g) :=
  (RingHom.snd _ _).comp (Tor f g hε).subtype

def ProjG : Prop := ∀ (q : ℕ) [NeZero q] (S : Type) [CommRing S] (f g : S), Ideal.span {f, g} = ⊤ →
  ∀ (ε : ZMod q → Localization.Away (f * g)) (hε : CompleteOrthogonalIdempotents ε),
  letI := (torMap f g hε).toAlgebra
  letI := (pr2 f g hε).toAlgebra
  IsLocalization.Away (algebraMap S (Tor f g hε) g) (ZMod q → Localization.Away g)

theorem locG_of (h : ProjG) : LocG := by
  intro q _ S _ f g hfg ε hε
  letI := (torMap f g hε).toAlgebra
  letI := (pr2 f g hε).toAlgebra
  haveI := h q S f g hfg ε hε
  let e := IsLocalization.algEquiv (Submonoid.powers (algebraMap S (Tor f g hε) g))
    (Localization.Away (algebraMap S (Tor f g hε) g)) (ZMod q → Localization.Away g)
  refine ⟨AlgEquiv.ofRingEquiv (f := e.toRingEquiv) (fun s => ?_)⟩
  have h1 : algebraMap S (Localization.Away (algebraMap S (Tor f g hε) g)) s =
      algebraMap (Tor f g hε) (Localization.Away (algebraMap S (Tor f g hε) g)) (torMap f g hε s) := rfl
  rw [AlgEquiv.coe_ringEquiv, h1, AlgEquiv.commutes]
  rfl

theorem TorEt_of_proj (hF : ProjF) (hG : ProjG) : TorEt := TorEt_of'' (locF_of hF) (locG_of hG)

end LateralTheory.E.TorEtPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4

namespace LateralTheory.E.LeafKumCut

def LeafTwist : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (B : Type) [CommRing B], Nonempty (Prim q B) →
  ∀ n i j : ℤ, Nonempty (Ht q (sp B) n i ≃+ Ht q (sp B) n j)

def EtaleFirstCohomologyMultiplicativeGroupPicard : Prop := Hyps → DivisorPicardCompatibility

def LeafKumSeq : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (B : Type) [CommRing B], IsUnit (q : B) →
  ∃ (a : Additive (Bˣ ⧸ (powMonoidHom q : Bˣ →* Bˣ).range) →+ Ht q (sp B) 1 1)
    (b : Ht q (sp B) 1 1 →+ H ℤ (sp B) Gm 1), Function.Exact a b

theorem prim_of_isAlgClosed (q : ℕ) [NeZero q] (k : Type) [Field k] [IsAlgClosed k] (hq : IsUnit (q : k)) :
    Nonempty (Prim q k) := by
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic q k)
    (ne_of_gt (Polynomial.degree_cyclotomic_pos q k (NeZero.pos q)))
  refine ⟨⟨ζ, hq, ?_⟩⟩
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
  exact hζ

theorem finite_of_exact {A M N : Type*} [AddCommGroup A] [AddCommGroup M] [AddCommGroup N] [Finite A]
    (a : A →+ M) (b : M →+ N) (h : Function.Exact a b) (hb : Finite b.range) : Finite M := by
  have hK : Finite b.ker := by
    have : (b.ker : Set M) = Set.range a := by ext x; exact h x
    have hf : (Set.range a).Finite := Set.finite_range a
    rw [← this] at hf
    exact hf.to_subtype
  have hQ : Finite (M ⧸ b.ker) := Finite.of_equiv _ (QuotientAddGroup.quotientKerEquivRange b).symm.toEquiv
  have hc := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup b.ker
  apply Nat.finite_of_card_ne_zero
  rw [hc]
  have : Nonempty (M ⧸ b.ker) := ⟨0⟩
  exact Nat.mul_ne_zero (Nat.card_pos).ne' (Nat.card_pos).ne'

theorem goal_of (hT : LeafTwist) (hG : EtaleFirstCohomologyMultiplicativeGroupPicard) (hS : LeafKumSeq) : LeafKum := by
  intro hy q _ k B _ _ _ _ hq hU hP i
  have hqB : IsUnit (q : B) := by simpa using hq.map (algebraMap k B)
  obtain ⟨ζ⟩ := prim_of_isAlgClosed q k hq
  obtain ⟨e⟩ := hT hy q B ⟨ζ.map (algebraMap k B)⟩ 1 i 1
  obtain ⟨a, b, hab⟩ := hS hy q B hqB
  obtain ⟨E⟩ := hG hy B
  have hr : Finite b.range := by
    refine Finite.of_injective (β := {c : CommRing.Pic B // c ^ q = 1})
      (fun y => ⟨Additive.toMul (E y.1), ?_⟩) ?_
    · obtain ⟨x, hx⟩ := y.2
      have h0 : q • x = 0 := by
        rw [← Nat.cast_smul_eq_nsmul (ZMod q), ZMod.natCast_self, zero_smul]
      have : q • E y.1 = 0 := by rw [← hx, ← map_nsmul, ← map_nsmul, h0, map_zero, map_zero]
      rw [← toMul_nsmul, this, toMul_zero]
    · intro y z h
      apply Subtype.ext
      apply E.injective
      apply Additive.toMul.injective
      exact congrArg Subtype.val h
  have : Finite (Ht q (sp B) 1 1) := finite_of_exact a b hab hr
  exact Finite.of_equiv _ e.symm.toEquiv

end LateralTheory.E.LeafKumCut
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.E4

def LeafCoprod : Prop := Hyps → ∀ (q : ℕ) (n i : ℤ) (m : ℕ) (Z : Fin m → Scheme.{0}),
  (∀ j, Finite (Ht q (sch.obj (Z j)) n i)) → Finite (Ht q (sch.obj (∐ Z)) n i)

def LeafCompGeom : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} (p : X ⟶ Sp k) [IsProper p],
  ∃ (m : ℕ) (Z : Fin m → Scheme.{0}) (ι : ∀ j, Z j ⟶ X), (∀ j, IsClosedImmersion (ι j) ∧ IsIntegral (Z j)) ∧
    IsProper (Sigma.desc ι) ∧ Surjective (Sigma.desc ι)

theorem LeafComp_of (hC : LeafCoprod) (hG : LeafCompGeom) : LeafComp := by
  intro hH q k _ X p _ n i hZ
  obtain ⟨m, Z, ι, hι, hP, hS⟩ := hG k p
  exact ⟨∐ Z, Sigma.desc ι, hP, hS, hC hH q n i m Z (fun j => hZ (Z j) (ι j) (hι j).1 (hι j).2)⟩

end LateralTheory.E.E4
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.E4.CurveCut

open LateralTheory.E.E4

def LeafMV : Prop := Hyps → ∀ (R : Type) [CommRing R] (F : Shv R) (X : Scheme.{0}) (U V : X.Opens), U ⊔ V = ⊤ →
  ∀ n : ℤ, ∃ δ : H R (sch.obj (U ⊓ V).toScheme) F n →+ H R (sch.obj X) F (n + 1),
    ∀ x : H R (sch.obj X) F (n + 1),
      (pull R (sch.map U.ι) F (n + 1) x = 0 ∧ pull R (sch.map V.ι) F (n + 1) x = 0) ↔ x ∈ δ.range

def isoH (R : Type) [CommRing R] (F : Shv R) {X Y : Scheme.{0}} (e : X ≅ Y) (n : ℤ) :
    H R (sch.obj Y) F n ≃ H R (sch.obj X) F n where
  toFun := pull R (sch.map e.hom) F n
  invFun := pull R (sch.map e.inv) F n
  left_inv x := by
    rw [← pull_comp, ← Functor.map_comp, e.inv_hom_id, CategoryTheory.Functor.map_id, pull_id]
  right_inv x := by
    rw [← pull_comp, ← Functor.map_comp, e.hom_inv_id, CategoryTheory.Functor.map_id, pull_id]

theorem finite_of_mv (hMV : LeafMV) (hH : Hyps) (R : Type) [CommRing R] (F : Shv R) (X : Scheme.{0}) (U V : X.Opens)
    (hUV : U ⊔ V = ⊤) (n : ℤ) (h0 : Finite (H R (sch.obj (U ⊓ V).toScheme) F n))
    (h1 : Finite (H R (sch.obj U.toScheme) F (n + 1))) (h2 : Finite (H R (sch.obj V.toScheme) F (n + 1))) :
    Finite (H R (sch.obj X) F (n + 1)) := by
  obtain ⟨δ, hδ⟩ := hMV hH R F X U V hUV n
  let φ := (pull R (sch.map U.ι) F (n + 1)).prod (pull R (sch.map V.ι) F (n + 1))
  have hker : φ.ker = δ.range := by
    ext x
    rw [← hδ x, AddMonoidHom.mem_ker]
    simp [φ, Prod.ext_iff]
  have : Finite φ.ker := by
    rw [hker]
    exact Set.finite_range δ |>.to_subtype
  have : Finite (H R (sch.obj X) F (n + 1) ⧸ φ.ker) :=
    Finite.of_equiv _ (QuotientAddGroup.quotientKerEquivRange φ).toEquiv.symm
  exact Finite.of_addSubgroup_quotient φ.ker

theorem subsingleton_of_mv (hMV : LeafMV) (hH : Hyps) (R : Type) [CommRing R] (F : Shv R) (X : Scheme.{0})
    (U V : X.Opens) (hUV : U ⊔ V = ⊤) (n : ℤ) (h0 : Subsingleton (H R (sch.obj (U ⊓ V).toScheme) F n))
    (h1 : Subsingleton (H R (sch.obj U.toScheme) F (n + 1))) (h2 : Subsingleton (H R (sch.obj V.toScheme) F (n + 1))) :
    Subsingleton (H R (sch.obj X) F (n + 1)) := by
  obtain ⟨δ, hδ⟩ := hMV hH R F X U V hUV n
  refine ⟨fun x y => ?_⟩
  have hx : ∀ z : H R (sch.obj X) F (n + 1), z = 0 := by
    intro z
    obtain ⟨w, hw⟩ := (hδ z).1 ⟨Subsingleton.elim _ _, Subsingleton.elim _ _⟩
    rw [← hw, Subsingleton.elim w 0, map_zero]
  rw [hx x, hx y]

end LateralTheory.E.E4.CurveCut
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4

namespace LateralTheory.E.LeafGeoCut

def FamilyV {k Ω : Type} [Field k] [Field Ω] (X : Scheme.{0}) {C0 C1 C2 : Scheme.{0}} (c0 : C0 ⟶ Sp Ω) (γ1 : C1 ⟶ C0)
    (γ2 : C2 ⟶ C1) : Prop :=
  ∃ (B Y0 Y1 Y2 : Scheme.{0}) (b : B ⟶ Sp k) (V : B.Opens) (p : Y0 ⟶ B) (g1 : Y1 ⟶ Y0) (g2 : Y2 ⟶ Y1)
    (h : Y0 ⟶ X) (s : Sp Ω ⟶ B) (u0 : C0 ⟶ Y0) (u1 : C1 ⟶ Y1) (u2 : C2 ⟶ Y2),
    IsIntegral B ∧ IsProper b ∧ Set.range s ⊆ V ∧
    SmP p V ∧ SmP (g1 ≫ p) V ∧ SmP (g2 ≫ g1 ≫ p) V ∧ IsProper (g2 ≫ g1 ≫ h) ∧ Surjective (g2 ≫ g1 ≫ h) ∧
    topologicalKrullDim B < topologicalKrullDim X ∧
    IrreducibleSpace Y0 ∧ topologicalKrullDim Y0 ≤ topologicalKrullDim X ∧ topologicalKrullDim Y0 < ⊤ ∧
    (p ⁻¹' (V : Set B)).Nonempty ∧
    IsPullback u0 c0 p s ∧ IsPullback u1 (γ1 ≫ c0) (g1 ≫ p) s ∧ IsPullback u2 (γ2 ≫ γ1 ≫ c0) (g2 ≫ g1 ≫ p) s ∧
    γ1 ≫ u0 = u1 ≫ g1 ∧ γ2 ≫ u1 = u2 ≫ g2

def LeafGeoV : Prop := ∀ (k : Type) [Field k] [IsAlgClosed k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Sp k) [IsProper p],
  0 < topologicalKrullDim X → ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω) (_ : Algebra k Ω) (C0 : Scheme.{0})
    (c0 : C0 ⟶ Sp Ω), IsCurve c0 ∧ ∀ (C1 C2 : Scheme.{0}) (γ1 : C1 ⟶ C0) (γ2 : C2 ⟶ C1), IsCurve (γ1 ≫ c0) →
      IsCurve (γ2 ≫ γ1 ≫ c0) → Surjective γ1 → Surjective γ2 → FamilyV (k := k) X c0 γ1 γ2

def LeafClosed : Prop := ∀ (B : Scheme.{0}) (V : B.Opens),
  ∃ (W : Scheme.{0}) (ι : W ⟶ B), IsClosedImmersion ι ∧ (V : Set B) = (Set.range ι)ᶜ

def LeafBdry : Prop := ∀ {Y B W : Scheme.{0}} (p : Y ⟶ B) (ι : W ⟶ B), IsClosedImmersion ι → IrreducibleSpace Y →
  topologicalKrullDim Y < ⊤ → (p ⁻¹' (Set.range ι)ᶜ).Nonempty →
  topologicalKrullDim (pullback p ι : Scheme.{0}) < topologicalKrullDim Y

theorem goal_of (hV : LeafGeoV) (hC : LeafClosed) (hB : LeafBdry) : LateralTheory.E.E4.LeafGeo := by
  intro k _ _ X _ p _ hd
  obtain ⟨Ω, iF, iA, iK, C0, c0, hc0, hall⟩ := hV k p hd
  refine ⟨Ω, iF, iA, iK, C0, c0, hc0, fun C1 C2 γ1 γ2 h1 h2 s1 s2 => ?_⟩
  obtain ⟨B, Y0, Y1, Y2, b, V, π, g1, g2, h, s, u0, u1, u2, iB, pb, hs, m0, m1, m2, f1, f2, dB, irr, dY, fin, ne,
    P0, P1, P2, w1, w2⟩ := hall C1 C2 γ1 γ2 h1 h2 s1 s2
  obtain ⟨W, ι, hι, hWV⟩ := hC B V
  exact ⟨B, W, Y0, Y1, Y2, b, ι, V, π, g1, g2, h, s, u0, u1, u2, iB, pb, hι, hWV, hs, m0, m1, m2, f1, f2, dB,
    lt_of_lt_of_le (hB π ι hι irr fin (hWV ▸ ne)) dY, P0, P1, P2, w1, w2⟩

end LateralTheory.E.LeafGeoCut

end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4

namespace LateralTheory.E.LeafGeoVCut

def FamilyVe {k Ω : Type} [Field k] [Field Ω] (X : Scheme.{0}) {C0 C1 C2 : Scheme.{0}} (c0 : C0 ⟶ Sp Ω) (e : C0 ⟶ X)
    (γ1 : C1 ⟶ C0) (γ2 : C2 ⟶ C1) : Prop :=
  ∃ (B Y0 Y1 Y2 : Scheme.{0}) (b : B ⟶ Sp k) (V : B.Opens) (p : Y0 ⟶ B) (g1 : Y1 ⟶ Y0) (g2 : Y2 ⟶ Y1)
    (h : Y0 ⟶ X) (s : Sp Ω ⟶ B) (u0 : C0 ⟶ Y0) (u1 : C1 ⟶ Y1) (u2 : C2 ⟶ Y2),
    IsIntegral B ∧ IsProper b ∧ Set.range s ⊆ V ∧
    SmP p V ∧ SmP (g1 ≫ p) V ∧ SmP (g2 ≫ g1 ≫ p) V ∧ IsProper (g2 ≫ g1 ≫ h) ∧
    topologicalKrullDim B < topologicalKrullDim X ∧
    IrreducibleSpace Y0 ∧ topologicalKrullDim Y0 ≤ topologicalKrullDim X ∧ topologicalKrullDim Y0 < ⊤ ∧
    (p ⁻¹' (V : Set B)).Nonempty ∧
    IsPullback u0 c0 p s ∧ IsPullback u1 (γ1 ≫ c0) (g1 ≫ p) s ∧ IsPullback u2 (γ2 ≫ γ1 ≫ c0) (g2 ≫ g1 ≫ p) s ∧
    γ1 ≫ u0 = u1 ≫ g1 ∧ γ2 ≫ u1 = u2 ≫ g2 ∧ u0 ≫ h = e

def LeafCurveV : Prop := ∀ (k : Type) [Field k] [IsAlgClosed k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Sp k) [IsProper p],
  0 < topologicalKrullDim X → ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω) (_ : Algebra k Ω) (C0 : Scheme.{0})
    (c0 : C0 ⟶ Sp Ω) (e : C0 ⟶ X), IsCurve c0 ∧ e ≫ p = c0 ≫ Spec.map (CommRingCat.ofHom (algebraMap k Ω)) ∧
    genericPoint X ∈ Set.range e ∧ ∀ R : Subalgebra k Ω, R.FG → ringKrullDim R < topologicalKrullDim X

theorem surj_of_generic {Y X : Scheme.{0}} [IrreducibleSpace X] (f : Y ⟶ X) [IsProper f]
    (hη : genericPoint X ∈ Set.range f) : Surjective f := by
  have hc : IsClosed (Set.range f) := f.isClosedMap.isClosed_range
  have h1 : closure ({genericPoint X} : Set X) ⊆ Set.range f :=
    closure_minimal (Set.singleton_subset_iff.mpr hη) hc
  rw [(genericPoint_spec X).def] at h1
  exact ⟨fun x => h1 (Set.mem_univ x)⟩

end LateralTheory.E.LeafGeoVCut

end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafSSCut

def incl0 {R : Type} [CommRing R] (K : Cx R) [K.IsStrictlyLE 0] :
    (HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).obj (K.X 0) ⟶ K :=
  HomologicalComplex.mkHomFromSingle (𝟙 _) (fun k _ =>
    (CochainComplex.isZero_of_isStrictlyLE K 0 k (by
      have : (0 : ℤ) + 1 = k := by assumption
      omega)).eq_of_tgt _ _)

instance chains_isStrictlyLE {R : Type} [CommRing R] (E : Spc) : CochainComplex.IsStrictlyLE ((chains R).obj E) 0 :=
  inferInstanceAs (CochainComplex.IsStrictlyLE (((chainsN R).obj E).extend ComplexShape.embeddingDownNat) 0)

def LeafFilt : Prop := E4.Hyps → ∀ (R : Type) [CommRing R] (K : Cx R) [K.IsStrictlyLE 0] (F : Shv R) (n : ℤ),
  (∀ r : ℕ, 0 < r → (r : ℤ) ≤ n →
    Finite (HK R ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).obj (K.X (-(r : ℤ)))) F (n - r))) →
  Finite (HK.pull R (incl0 K) F n).ker

def LeafCompare : Prop := E4.Hyps → ∀ (R : Type) [CommRing R] (F : Shv R) {Y X : Scheme.{0}} (f : Y ⟶ X) (n : ℤ),
  Eqv R (cechAug f) F → Finite (HK.pull R (incl0 ((chains R).obj (cech f))) F n).ker →
  Finite (pull R (sch.map f) F n).ker

def LeafTerms : Prop := E4.Hyps → ∀ (R : Type) [CommRing R] (F : Shv R) {Y X : Scheme.{0}} (f : Y ⟶ X) [IsProper f]
  (r : ℕ) (m : ℤ), (∀ (Z : Scheme.{0}) (g : Z ⟶ X), IsProper g → Finite (H R (sch.obj Z) F m)) →
  Finite (HK R ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).obj (((chains R).obj (cech f)).X (-(r : ℤ)))) F m)

theorem goal_of (h1 : LeafFilt) (h2 : LeafCompare) (h3 : LeafTerms) : E4.LeafSS := by
  intro hy R _ F Y X f _ n hE hfin
  refine h2 hy R F f n hE ?_
  refine h1 hy R ((chains R).obj (cech f)) F n ?_
  intro r hr hrn
  exact h3 hy R F f r (n - r) (fun Z g hg => hfin Z g hg (n - r) (by omega))

end LateralTheory.E.LeafSSCut
end
end
