module

public import Development.EtaleCohomology.EtaleSheaves.Bundle041
public import Development.EtaleCohomology.EtaleSheaves.Bundle043
public import Development.EtaleCohomology.EtaleSheaves.LZProperCut
public import Development.EtaleCohomology.EtaleSheaves.Bundle044
public import Development.EtaleCohomology.EtaleSheaves.TwistGenerators.LeafTwGenIndepOf
public import Development.EtaleCohomology.EtaleSheaves.Bundle005
public import Development.EtaleCohomology.EtaleSheaves.Bundle014
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

@[expose] public section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.CoverCut

namespace LateralTheory.E.LimIntPf

theorem key {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (hw : f ≫ g = h) (U : Z.Opens) (V₁ : Y.Opens)
    (W₁ W : X.Opens) (e1 : V₁ ≤ g ⁻¹ᵁ U) (e2 : W₁ ≤ f ⁻¹ᵁ V₁) (e3 : W ≤ W₁) (e : W ≤ h ⁻¹ᵁ U) (x : Γ(Z, U)) :
    X.presheaf.map (homOfLE e3).op (f.appLE V₁ W₁ e2 (g.appLE U V₁ e1 x)) = h.appLE U W e x := by
  subst hw
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, Scheme.Hom.appLE_comp_appLE_assoc,
    Scheme.Hom.appLE_map]

theorem app_surj {J : Type} [SmallCategory J] [IsCofiltered J] (D : J ⥤ Scheme.{0}) (c : Cone D) (hc : IsLimit c)
    [∀ {i k : J} (f : i ⟶ k), IsAffineHom (D.map f)] (hC : ∀ {i k : J} (f : i ⟶ k), IsClosedImmersion (D.map f))
    (j : J) (U : (D.obj j).Opens) (hU : IsAffineOpen U) :
    Function.Surjective ((c.π.app j).app U) := by
  intro s
  have (k : Over j) : IsAffine ((opensDiagram D j U).obj k) := hU.preimage (D.map _)
  obtain ⟨k, t, hk⟩ := exists_appTop_π_eq_of_isAffine_of_isLimit _ _ (isLimitOpensCone D c hc j U)
    (c.pt.presheaf.map (homOfLE (show (c.π.app j ⁻¹ᵁ U).ι ''ᵁ ⊤ ≤ c.π.app j ⁻¹ᵁ U by simp)).op s)
  have := hC k.hom
  obtain ⟨u, hu⟩ := (D.map k.hom).app_surjective U hU
    ((D.obj k.left).presheaf.map (homOfLE (show D.map k.hom ⁻¹ᵁ U ≤ (D.map k.hom ⁻¹ᵁ U).ι ''ᵁ ⊤ by simp)).op t)
  refine ⟨u, ?_⟩
  simp only [opensCone_π_app, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE] at hk hu ⊢
  have e1 : ∀ {X : Scheme.{0}} {V W : X.Opens} (h1 : V ≤ W) (h2 : W ≤ V) (x : Γ(X, W)),
      X.presheaf.map (homOfLE h2).op (X.presheaf.map (homOfLE h1).op x) = x := by
    intro X V W h1 h2 x
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    have : (homOfLE h1).op ≫ (homOfLE h2).op = 𝟙 (Opposite.op W) := Subsingleton.elim _ _
    rw [this, CategoryTheory.Functor.map_id]; rfl
  have hs := e1 (X := c.pt) (show (c.π.app j ⁻¹ᵁ U).ι ''ᵁ ⊤ ≤ c.π.app j ⁻¹ᵁ U by simp)
    (show c.π.app j ⁻¹ᵁ U ≤ (c.π.app j ⁻¹ᵁ U).ι ''ᵁ ⊤ by simp) s
  rw [← hk] at hs
  have ht := e1 (X := D.obj k.left) (show D.map k.hom ⁻¹ᵁ U ≤ (D.map k.hom ⁻¹ᵁ U).ι ''ᵁ ⊤ by simp)
    (show (D.map k.hom ⁻¹ᵁ U).ι ''ᵁ ⊤ ≤ D.map k.hom ⁻¹ᵁ U by simp) t
  rw [← hu] at ht
  rw [← hs, ← ht]
  have cg : ∀ {X Y : Scheme.{0}} (f g : X ⟶ Y) (h : f = g) (U : Y.Opens) (V : X.Opens) e e',
      f.appLE U V e = g.appLE U V e' := by
    intro X Y f g h U V e e'; subst h; rfl
  erw [Scheme.Hom.resLE_appLE]
  simp only [← ConcreteCategory.comp_apply, Scheme.Hom.appLE_map]
  exact (key _ _ _ (c.w k.hom) _ _ _ _ _ _ _ _ u).symm

theorem LimInt_of : LateralTheory.E.BuildCut.LimInt := by
  intro Y y J _ _ D c ι hsys j
  obtain ⟨⟨hl⟩, h2, h3⟩ := hsys
  have hA : ∀ {i k : J} (f : i ⟶ k), IsAffineHom (D.map f) := fun f => (h3 f).2
  have hC : ∀ {i k : J} (f : i ⟶ k), IsClosedImmersion (D.map f) := by
    intro i k f
    have : IsClosedImmersion (ι k) := (h2 k).2.1
    have : IsClosedImmersion (D.map f ≫ ι k) := by rw [(h3 f).1]; exact (h2 i).2.1
    exact IsClosedImmersion.of_comp (D.map f) (ι k)
  have : IsClosedImmersion (ι j) := (h2 j).2.1
  have : IsIntegralHom (c.π.app j) :=
    { toIsAffineHom := isAffineHom_π_app D c hl j
      isIntegral_app := fun U hU =>
        (RingHom.Finite.of_surjective _ (app_surj D c hl hC j U hU)).to_isIntegral }
  infer_instance

end LateralTheory.E.LimIntPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.BinPf

universe v u
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]

theorem cls_biprod_eq_zero {K₁ K₂ L : CochainComplex C ℤ} {n : ℤ} (x : CohomologyClass (K₁ ⊞ K₂) L n)
    (h₁ : cpre (Cocycle.ofHom (biprod.inl : K₁ ⟶ K₁ ⊞ K₂)) L n n (zero_add n) x = 0)
    (h₂ : cpre (Cocycle.ofHom (biprod.inr : K₂ ⟶ K₁ ⊞ K₂)) L n n (zero_add n) x = 0) : x = 0 := by
  obtain ⟨α, rfl⟩ := x.mk_surjective
  rw [cpre_mk, CohomologyClass.mk_eq_zero_iff] at h₁ h₂
  obtain ⟨m, hm, β₁, hβ₁⟩ := h₁
  obtain ⟨m', hm', β₂, hβ₂⟩ := h₂
  have hmm : m' = m := by omega
  subst hmm
  rw [CohomologyClass.mk_eq_zero_iff]
  refine ⟨m', hm', (Cochain.ofHom (biprod.fst : K₁ ⊞ K₂ ⟶ K₁)).comp β₁ (zero_add m') +
    (Cochain.ofHom (biprod.snd : K₁ ⊞ K₂ ⟶ K₂)).comp β₂ (zero_add m'), ?_⟩
  rw [δ_add, δ_ofHom_comp, δ_ofHom_comp, hβ₁, hβ₂]
  change (Cochain.ofHom (biprod.fst : K₁ ⊞ K₂ ⟶ K₁)).comp ((Cochain.ofHom biprod.inl).comp α.1 (zero_add n)) (zero_add n) +
    (Cochain.ofHom (biprod.snd : K₁ ⊞ K₂ ⟶ K₂)).comp ((Cochain.ofHom biprod.inr).comp α.1 (zero_add n)) (zero_add n) = α.1
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.comp_assoc_of_first_is_zero_cochain,
    ← Cochain.add_comp, ← Cochain.ofHom_comp, ← Cochain.ofHom_comp, ← Cochain.ofHom_add, biprod.total,
    Cochain.id_comp]

theorem hkpull_comp {R : Type} [CommRing R] {K L M : Cx R} (f : K ⟶ L) (g : L ⟶ M) (F : Shv R) (n : ℤ)
    (x : HK R M F n) : HK.pull R (f ≫ g) F n x = HK.pull R f F n (HK.pull R g F n x) := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [HK.pull, HK.pre, cpre_mk, zcomp, Cochain.ofHom_comp]

theorem hkpull_id {R : Type} [CommRing R] {K : Cx R} (F : Shv R) (n : ℤ)
    (x : HK R K F n) : HK.pull R (𝟙 K) F n x = x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [HK.pull, HK.pre, cpre_mk, zcomp]

def ChainsCoprod : Prop := ∀ (R : Type) [CommRing R] (U V : Spc),
  IsIso (biprod.desc ((chains R).map (coprod.inl : U ⟶ U ⨿ V)) ((chains R).map (coprod.inr : V ⟶ U ⨿ V)))

def CoprodAcyc : Prop := ∀ (q : ℕ) (U V : Spc), Acyc q U → Acyc q V → Acyc q (U ⨿ V)

theorem coprodAcyc_of (hC : ChainsCoprod) : CoprodAcyc := by
  intro q U V hU hV n i hn
  have hI := hC (ZMod q) U V
  set φ := biprod.desc ((chains (ZMod q)).map (coprod.inl : U ⟶ U ⨿ V)) ((chains (ZMod q)).map (coprod.inr : V ⟶ U ⨿ V))
  have h0 : ∀ x : Ht q (U ⨿ V) n i, x = 0 := by
    intro x
    have hy : HK.pull _ φ _ n x = 0 := by
      apply cls_biprod_eq_zero
      · have e := hkpull_comp (biprod.inl) φ (tw q i) n x
        rw [biprod.inl_desc] at e
        have : HK.pull _ ((chains (ZMod q)).map (coprod.inl : U ⟶ U ⨿ V)) (tw q i) n x = 0 :=
          (hU n i hn).elim _ _
        rw [this] at e
        exact e.symm
      · have e := hkpull_comp (biprod.inr) φ (tw q i) n x
        rw [biprod.inr_desc] at e
        have : HK.pull _ ((chains (ZMod q)).map (coprod.inr : V ⟶ U ⨿ V)) (tw q i) n x = 0 :=
          (hV n i hn).elim _ _
        rw [this] at e
        exact e.symm
    have e := hkpull_comp (inv φ) φ (tw q i) n x
    rw [IsIso.inv_hom_id, hkpull_id, hy, map_zero] at e
    exact e
  exact ⟨fun x y => by rw [h0 x, h0 y]⟩

def DescEqv : Prop := LateralTheory.E.t_E2Cut.Hyp → ∀ (q : ℕ) (A R0 R1 : Type) [CommRing A] [CommRing R0] [CommRing R1]
  (e : A ≃+* R0 × R1) (i : ℤ),
  Eqv _ (coprod.desc (spMap ((RingHom.fst R0 R1).comp e.toRingHom)) (spMap ((RingHom.snd R0 R1).comp e.toRingHom))) (tw q i)

end LateralTheory.E.BinPf

theorem LateralTheory.E.ProdAcycPf.Bin_of (hD : LateralTheory.E.BinPf.DescEqv) (hC : LateralTheory.E.BinPf.ChainsCoprod) :
    LateralTheory.E.ProdAcycPf.Bin := by
  intro H q A R0 R1 _ _ _ ⟨e⟩ h0 h1 n i hn
  have hb := (hD H q A R0 R1 e i n).1
  have hs := LateralTheory.E.BinPf.coprodAcyc_of hC q _ _ h0 h1 n i hn
  exact ⟨fun x y => hb (Subsingleton.elim _ _)⟩
end
end

section

noncomputable section
open LateralTheory.E.StandardEtaleChartsIdempotentGluing

namespace LateralTheory.E.IdempotentLiftingAlt

def LZIdemSumNoeth : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (K : Type) [Field K]
  [Algebra A K] (B C : Subalgebra A K) (t : K), Charts B C t → B.FG → C.FG → ∀ e f : K, IdemPair B C t e f →
  e - f ∈ mS B ⊔ mS C

def LZIdemSumApprox : Prop := LZIdemSumNoeth → ∀ (A : Type) [CommRing A] [IsLocalRing A] (K : Type) [Field K]
  [Algebra A K] (B C : Subalgebra A K) (t : K), Charts B C t → ∀ e f : K, IdemPair B C t e f →
  e - f ∈ mS B ⊔ mS C

variable {A K : Type} [CommRing A] [IsLocalRing A] [Field K] [Algebra A K]

theorem mS_le (S : Subalgebra A K) : mS S ≤ Subalgebra.toSubmodule S := by
  unfold mS
  exact Submodule.smul_le_right

theorem lift_of_sum (B C : Subalgebra A K) (e f : K) (he : e ∈ B) (hf : f ∈ C) (h : e - f ∈ mS B ⊔ mS C) :
    ∃ g ∈ B, g ∈ C ∧ g - e ∈ mS B ∧ g - f ∈ mS C := by
  obtain ⟨β, hβ, γ, hγ, hsum⟩ := Submodule.mem_sup.mp h
  have hβB : β ∈ B := mS_le B hβ
  have hγC : γ ∈ C := mS_le C hγ
  refine ⟨e - β, B.sub_mem he hβB, ?_, ?_, ?_⟩
  · have : e - β = f + γ := by linear_combination -hsum
    rw [this]; exact C.add_mem hf hγC
  · have : e - β - e = -β := by ring
    rw [this]; exact (mS B).neg_mem hβ
  · have : e - β - f = γ := by linear_combination -hsum
    rw [this]; exact hγ

theorem IdemLift_of (hN : LZIdemSumNoeth) (hA : LZIdemSumApprox) : LateralTheory.E.StandardEtaleChartsIdempotentGluing.IdemLift := by
  intro A _ _ _ K _ _ B C t hc e f hp
  exact lift_of_sum B C e f hp.1 hp.2.1 (hA hN A K B C t hc e f hp)

end LateralTheory.E.IdempotentLiftingAlt
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.StandardEtaleChartsIdempotentGluing

namespace LateralTheory.E.AlgGlue₂

variable {A K : Type} [CommRing A] [IsLocalRing A] [Field K] [Algebra A K]

theorem mS_mul (S : Subalgebra A K) {x b : K} (hx : x ∈ mS S) (hb : b ∈ S) : x * b ∈ mS S := by
  unfold mS at hx ⊢
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro a ha s hs
    rw [smul_mul_assoc]
    exact Submodule.smul_mem_smul ha (S.mul_mem hs hb)
  · intro x y hx hy
    rw [add_mul]
    exact Submodule.add_mem _ hx hy

theorem unit_case (S : Subalgebra A K) {u h e : K} (hu : u ∈ S) (hh : h ∈ S) (huh : u * h = 1)
    (he : e ∈ S) (hue : u - e ∈ mS S) (hee : e * e - e ∈ mS S) : e - 1 ∈ mS S := by
  have key : e - 1 = (e * e - e) * h + (u - e) * ((e - 1) * h) := by
    linear_combination (1 - e) * huh
  rw [key]
  exact Submodule.add_mem _ (mS_mul S hee hh)
    (mS_mul S hue (S.mul_mem (S.sub_mem he (S.one_mem)) hh))

theorem nonunit_case (S : Subalgebra A K) {u h e : K} (hu : u ∈ S) (hh : h ∈ S) (huh : (1 - u) * h = 1)
    (he : e ∈ S) (hue : u - e ∈ mS S) (hee : e * e - e ∈ mS S) : e ∈ mS S := by
  have h1 := unit_case S (u := 1 - u) (e := 1 - e) (S.sub_mem S.one_mem hu) hh huh
    (S.sub_mem S.one_mem he)
    (by
      have : (1 - u) - (1 - e) = (u - e) * (-1) := by ring
      rw [this]; exact mS_mul S hue (S.neg_mem S.one_mem))
    (by
      have : (1 - e) * (1 - e) - (1 - e) = e * e - e := by ring
      rw [this]; exact hee)
  have : e = (1 - e - 1) * (-1) := by ring
  rw [this]; exact mS_mul S h1 (S.neg_mem S.one_mem)

theorem AlgGlue_of (hL : IdemLift) (hF : LateralTheory.E.LZProperCut.LZHensFinite) : AlgGlue := by
  intro A _ _ _ K _ _ B C t hc hint e f hef
  obtain ⟨heB, hfC, hee, hff, hd⟩ := hef
  obtain ⟨g, hgB, hgC, hge, hgf⟩ := hL A K B C t hc e f ⟨heB, hfC, hee, hff, hd⟩
  set R : Subalgebra A K := Algebra.adjoin A {g} with hR
  have hRB : R ≤ B := Algebra.adjoin_le (Set.singleton_subset_iff.mpr hgB)
  have hRC : R ≤ C := Algebra.adjoin_le (Set.singleton_subset_iff.mpr hgC)
  have hgi : IsIntegral A g := hint g hgB hgC
  have : Module.Finite A R := Algebra.finite_adjoin_simple_of_isIntegral hgi
  have : IsDomain R := inferInstance
  have : ConnectedSpace ↑(Spec (CommRingCat.of R)) := by
    change ConnectedSpace (PrimeSpectrum R)
    infer_instance
  have : IsLocalRing R := hF A R this
  have hgR : g ∈ R := Algebra.self_mem_adjoin_singleton A g
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (⟨g, hgR⟩ : R) with hu | hu
  · obtain ⟨v, hv⟩ := hu.exists_right_inv
    have hv' : g * (v : K) = 1 := by
      have := congrArg Subtype.val hv; simpa using this
    right
    exact ⟨unit_case B hgB (hRB v.2) hv' heB hge hee, unit_case C hgC (hRC v.2) hv' hfC hgf hff⟩
  · obtain ⟨v, hv⟩ := hu.exists_right_inv
    have hv' : (1 - g) * (v : K) = 1 := by
      have := congrArg Subtype.val hv; simpa using this
    left
    exact ⟨nonunit_case B hgB (hRB v.2) hv' heB hge hee, nonunit_case C hgC (hRC v.2) hv' hfC hgf hff⟩

end LateralTheory.E.AlgGlue₂
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E2Cut

namespace LateralTheory.E.RootPf

lemma unit_sec {Z : Scheme.{0}} (q : ℕ) (A : Type) [CommRing A] (p : Z ⟶ Spec (CommRingCat.of A))
    (hq : IsUnit (q : A)) (U : Z.Opens) : IsUnit (q : Γ(Z, U)) := by
  let f : CommRingCat.of A ⟶ Γ(Z, U) :=
    (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ p.appTop ≫ Z.presheaf.map (homOfLE le_top).op
  have := hq.map f.hom
  simpa using this

lemma prim_of_aic (q : ℕ) [NeZero q] (T : Type) [CommRing T] [IsDomain T] (hT : AIC T)
    (hq : IsUnit (q : T)) : ∃ a : T, IsPrimitiveRoot a q := by
  have : NeZero (q : T) := ⟨hq.ne_zero⟩
  obtain ⟨a, ha⟩ := hT (Polynomial.cyclotomic q T) (Polynomial.cyclotomic.monic q T)
    (by rw [Polynomial.natDegree_cyclotomic]; exact Nat.totient_pos.2 (Nat.pos_of_ne_zero (NeZero.ne q)))
  exact ⟨a, (Polynomial.isRoot_cyclotomic_iff (n := q) (μ := a)).1 ha⟩

lemma local_root {Z : Scheme.{0}} [IsIntegral Z]
    (hZ : ∀ U : Z.Opens, IsAffineOpen U → (U : Set Z).Nonempty → AIC Γ(Z, U))
    (q : ℕ) [NeZero q] (hqU : ∀ U : Z.Opens, IsUnit (q : Γ(Z, U))) (ζ : Z.functionField)
    (hζ : IsPrimitiveRoot ζ q) (V : Z.Opens) (hV : IsAffineOpen V) [hne : Nonempty V] :
    ∃ s : Γ(Z, V), (Z.germToFunctionField V).hom s = ζ := by
  obtain ⟨a, ha⟩ := prim_of_aic q Γ(Z, V)
    (hZ V hV (by obtain ⟨x⟩ := hne; exact ⟨x.1, x.2⟩)) (hqU V)
  have hb := ha.map_of_injective (f := (Z.germToFunctionField V).hom) (Z.germToFunctionField_injective V)
  obtain ⟨i, -, hi⟩ := hb.eq_pow_of_pow_eq_one hζ.pow_eq_one
  exact ⟨a ^ i, by rw [map_pow]; exact hi⟩

theorem Root_of : LateralTheory.E.ChartSurjCut.Root := by
  intro q A _ Z p hZ hq
  obtain ⟨hI, hA⟩ := hZ
  have hqU : ∀ U : Z.Opens, IsUnit (q : Γ(Z, U)) := fun U => unit_sec q A p hq U
  obtain ⟨x⟩ := (inferInstance : Nonempty Z)
  have : Nonempty (⊤ : Z.Opens) := ⟨⟨x, trivial⟩⟩
  have hq0 : NeZero q := ⟨by rintro rfl; exact not_isUnit_zero (M₀ := Γ(Z, ⊤)) (by simpa using hqU ⊤)⟩
  have hbasis : ∀ {U : Z.Opens} {y : Z}, y ∈ U → ∃ U' ∈ Z.affineOpens, y ∈ U' ∧ U' ≤ U :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp Z.isBasis_affineOpens
  have haff : ∀ y : Z, ∃ U : Z.Opens, IsAffineOpen U ∧ y ∈ U := by
    intro y
    obtain ⟨U, hU, hy, -⟩ := hbasis (show y ∈ (⊤ : Z.Opens) from trivial)
    exact ⟨U, hU, hy⟩
  obtain ⟨U₀, hU₀, hx⟩ := haff x
  have : Nonempty U₀ := ⟨⟨x, hx⟩⟩
  obtain ⟨a₀, ha₀⟩ := prim_of_aic q Γ(Z, U₀) (hA U₀ hU₀ ⟨x, hx⟩) (hqU U₀)
  set ζ : Z.functionField := (Z.germToFunctionField U₀).hom a₀ with hζdef
  have hζ : IsPrimitiveRoot ζ q :=
    ha₀.map_of_injective (f := (Z.germToFunctionField U₀).hom) (Z.germToFunctionField_injective U₀)
  let ι := {V : Z.Opens // IsAffineOpen V ∧ Nonempty V}
  let U : ι → Z.Opens := fun i => i.1
  have instU : ∀ i : ι, Nonempty (U i) := fun i => i.2.2
  have hex : ∀ i : ι, ∃ s : Γ(Z, U i), (Z.germToFunctionField (U i)).hom s = ζ := fun i =>
    @local_root Z hI hA q hq0 hqU ζ hζ i.1 i.2.1 i.2.2
  let sf : ∀ i : ι, Γ(Z, U i) := fun i => Classical.choose (hex i)
  have hsf : ∀ i : ι, (Z.germToFunctionField (U i)).hom (sf i) = ζ := fun i => Classical.choose_spec (hex i)
  have hcov : (⊤ : Z.Opens) ≤ iSup U := by
    intro y _
    obtain ⟨V, hV, hy⟩ := haff y
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨V, hV, ⟨⟨y, hy⟩⟩⟩, hy⟩
  have hcomp : TopCat.Presheaf.IsCompatible Z.sheaf.1 U sf := by
    intro i j
    have : Nonempty (U i ⊓ U j : Z.Opens) := by
      obtain ⟨y, hy⟩ := nonempty_preirreducible_inter (U i).isOpen (U j).isOpen
        (by obtain ⟨⟨y, hy⟩⟩ := i.2.2; exact ⟨y, hy⟩) (by obtain ⟨⟨y, hy⟩⟩ := j.2.2; exact ⟨y, hy⟩)
      exact ⟨⟨y, hy⟩⟩
    apply Z.germToFunctionField_injective (U i ⊓ U j)
    change Z.presheaf.germ _ _ _ (Z.presheaf.map _ (sf i)) = Z.presheaf.germ _ _ _ (Z.presheaf.map _ (sf j))
    rw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply]
    exact (hsf i).trans (hsf j).symm
  obtain ⟨s0, hs, -⟩ := Z.sheaf.existsUnique_gluing' U ⊤ (fun i => homOfLE le_top) hcov sf hcomp
  let s : Γ(Z, ⊤) := s0
  change ∀ i : ι, Z.presheaf.map (homOfLE le_top).op s = sf i at hs
  have hgs : (Z.germToFunctionField ⊤).hom s = ζ := by
    have h1 := hs ⟨U₀, hU₀, inferInstance⟩
    have h2 := hsf ⟨U₀, hU₀, inferInstance⟩
    rw [← h1] at h2
    change Z.presheaf.germ _ _ _ (Z.presheaf.map _ s) = ζ at h2
    rw [TopCat.Presheaf.germ_res_apply] at h2
    exact h2
  have hps : IsPrimitiveRoot s q := by
    have h' : IsPrimitiveRoot ((Z.germToFunctionField ⊤).hom s) q := by rw [hgs]; exact hζ
    exact IsPrimitiveRoot.of_map_of_injective h' (Z.germToFunctionField_injective ⊤)
  have : NeZero (q : Γ(Z, ⊤)) := ⟨(hqU ⊤).ne_zero⟩
  refine ⟨⟨s, hqU ⊤, ?_⟩⟩
  have hr := (Polynomial.isRoot_cyclotomic_iff (n := q) (μ := s)).2 hps
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
  exact hr

end LateralTheory.E.RootPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.ChartSurjCut

namespace LateralTheory.E.LCIsoPf

def TwTriv : Prop := ∀ (q : ℕ) (i : ℤ) (S : Scheme.{0}) (ζ : Prim q Γ(S, ⊤)),
  ∃ e : ∀ (X : Scheme.{0}) (_s : X ⟶ S), Sec (tw q 0) X ≃+ Sec (tw q i) X,
    ∀ {X Y : Scheme.{0}} (s : X ⟶ S) (t : Y ⟶ S) (f : Y ⟶ X), f ≫ s = t → ∀ x : Sec (tw q 0) X,
      Sec.res f (e X s x) = e Y t (Sec.res f x)

def Tw0 : Prop := ∀ (q : ℕ),
  ∃ c : ∀ T : Scheme.{0}, IsUnit (q : Γ(T, ⊤)) → (LocallyConstant T (ZMod q) ≃+ Sec (tw q 0) T),
    ∀ {V U : Scheme.{0}} (g : V ⟶ U) (hV : IsUnit (q : Γ(V, ⊤))) (hU : IsUnit (q : Γ(U, ⊤))) (a : LocallyConstant U (ZMod q)),
      Sec.res g (c U hU a) = c V hV (a.comap g.base.hom)

def SecIso : Prop := ∀ (q : ℕ) (i : ℤ) (S : Scheme.{0}) (ζ : Prim q Γ(S, ⊤)),
  ∃ e : ∀ (X : Scheme.{0}) (_s : X ⟶ S), LocallyConstant X (ZMod q) ≃+ Sec (tw q i) X,
    ∀ {X Y : Scheme.{0}} (s : X ⟶ S) (t : Y ⟶ S) (f : Y ⟶ X), f ≫ s = t → ∀ g : LocallyConstant X (ZMod q),
      Sec.res f (e X s g) = e Y t (g.comap f.base.hom)

theorem unit_of {q : ℕ} {S X : Scheme.{0}} (ζ : Prim q Γ(S, ⊤)) (s : X ⟶ S) : IsUnit (q : Γ(X, ⊤)) :=
  (ζ.map s.appTop.hom).2.1

theorem SecIso_of (hT : TwTriv) (h0 : Tw0) : SecIso := by
  intro q i S ζ
  obtain ⟨eT, heT⟩ := hT q i S ζ
  obtain ⟨c, hc⟩ := h0 q
  refine ⟨fun X s => (c X (unit_of ζ s)).trans (eT X s), ?_⟩
  intro X Y s t f hf g
  simp only [AddEquiv.trans_apply]
  rw [heT s t f hf, hc f (unit_of ζ t) (unit_of ζ s)]

theorem SecIso_LCIso (hS : SecIso) : LCIso := by
  intro H q i S ζ
  obtain ⟨eS, heS⟩ := hS q i S ζ
  obtain ⟨-, eA, heA, -⟩ := H.a9 (ZMod q) (tw q i)
  refine ⟨fun X s => (eS X s).trans (eA X), ?_⟩
  intro X Y s t f hf g
  simp only [AddEquiv.trans_apply]
  rw [heA, heS s t f hf g]

end LateralTheory.E.LCIsoPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.UnitSections

theorem powLocal : LateralTheory.E.LeafUnitSecPf.Indep.LeafPowLocal := by
  intro q _ U ζ ξ
  obtain ⟨s, hs, hf⟩ := LateralTheory.E.L_prim_locPf.algPow q Γ(U, ⊤) ζ ξ
  obtain ⟨S, hS, hP⟩ := LateralTheory.E.L_prim_locPf.loc_of_span s hs
    (P := fun V g => ∃ a : (ZMod q)ˣ,
      (ξ.map (Scheme.Γ.map g.op).hom).1 = (ζ.map (Scheme.Γ.map g.op).hom).1 ^ (a : ZMod q).val) (by
      intro f hfs V g hu
      obtain ⟨a, n, hn⟩ := hf f hfs
      refine ⟨a, ?_⟩
      have h := LateralTheory.E.L_prim_locPf.eq_of_unit_kill g.appTop.hom hn hu
      rw [map_pow] at h
      exact h)
  exact ⟨S, hS, hP⟩

theorem LeafUnitSec_of : LateralTheory.E.LeafOneExistsPf.LeafUnitSec :=
  LateralTheory.E.LeafUnitSecPf.Indep.LeafUnitSec_of LateralTheory.E.LeafPrimCoverPf.LeafPrimCover_of powLocal

end LateralTheory.E.UnitSections
end
end
