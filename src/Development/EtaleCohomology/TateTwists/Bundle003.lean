module

public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.EtaleCohomology.TateTwists.Bundle001
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Pullbacks
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Limits.Types.Pushouts
import Mathlib.CategoryTheory.Presentable.Type
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

def LateralTheory.EtaleFoundations.EtaleTwistedCupProductAssociative : Prop :=
  ∀ (q : ℕ) [NeZero q] (E : Spc) {n m k i j l : ℤ} (a : Ht q E n i) (b : Ht q E m j) (c : Ht q E k l), cup q (cup q a b) c = (cup q a (cup q b c)).cast (by ring) (by ring)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

def LateralTheory.EtaleFoundations.EtaleTwistedCupProductGradedCommutative : Prop :=
  ∀ (q : ℕ) [NeZero q] (E : Spc) {n m i j : ℤ} (a : Ht q E n i) (b : Ht q E m j), cup q a b = (n * m).negOnePow • (cup q b a).cast (by ring) (by ring)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.AwExPf

variable {R : Type} [CommRing R]

theorem free_ext (P : PSh) (F : Shv R) (φ ψ : (free R).obj P ⟶ F)
    (h : ∀ U x, Sec.map φ (freeGen R P U x) = Sec.map ψ (freeGen R P U x)) : φ = ψ := by
  let φ' : (presheafToSheaf Scheme.etaleTopology _).obj ((freeP R).obj P) ⟶ F := φ
  let ψ' : (presheafToSheaf Scheme.etaleTopology _).obj ((freeP R).obj P) ⟶ F := ψ
  change φ' = ψ'
  apply ((sheafificationAdjunction Scheme.etaleTopology _).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  refine NatTrans.ext (funext fun U => ModuleCat.free_hom_ext fun x => ?_)
  exact h U.unop x.down

theorem ev_ext {E : Spc} {I : Cx R} {n : ℤ} (α β : Cochain ((chains R).obj E) I n)
    (h : ∀ p s h U x, ev α p s h U x = ev β p s h U x) : α = β := by
  refine Cochain.ext _ _ (fun i j hij => ?_)
  by_cases hi : 0 ≤ -i
  · obtain ⟨p, rfl⟩ : ∃ p : ℕ, i = -(p : ℤ) := ⟨(-i).toNat, by omega⟩
    rw [← cancel_epi (chainsXIso R E p).inv]
    exact free_ext _ _ _ _ fun U x => h p j hij U x
  · apply IsZero.eq_of_src
    apply HomologicalComplex.isZero_extend_X
    intro i' hi'
    change -(i' : ℤ) = i at hi'
    omega

end LateralTheory.EtaleFoundations.AwExPf
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

def LateralTheory.EtaleFoundations.PrimitiveRootsOfUnityBasicIdentities : Prop :=
  ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], (∀ ζ : Prim q A, ζ.1 ^ q = 1) ∧ (∀ (ζ : Prim q A) (a : ℕ), Nat.Coprime a q → ∃ ξ : Prim q A, ξ.1 = ζ.1 ^ a) ∧ (∀ (ζ : Prim q A) (a b : ℕ), ¬ a ≡ b [MOD q] → IsUnit (ζ.1 ^ a - ζ.1 ^ b)) ∧ (∀ (ζ : Prim q A) (x : A), x ^ q = 1 → ∏ a ∈ Finset.range q, (x - ζ.1 ^ a) = 0) ∧ (∀ (ζ ξ : Prim q A), ∏ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), (ξ.1 - ζ.1 ^ a) = 0) ∧ ∀ (r : ℕ), r ∣ q → ∀ ζ : Prim q A, ∃ ξ : Prim r A, ξ.1 = ζ.1 ^ (q / r)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

def LateralTheory.EtaleFoundations.twF_gen_inj : Prop :=
  ∀ (q : ℕ) [NeZero q] (B : Type) [CommRing B], Nontrivial B → ∀ (i : ℤ) (ζ : Prim q B),
    Function.Injective (fun c : ZMod q =>
      (c.val • (Submodule.Quotient.mk (Finsupp.single ζ 1) : (twF q i).obj (CommRingCat.of B)) :
        (twF q i).obj (CommRingCat.of B)))

namespace LateralTheory.EtaleFoundations.GenConn

theorem twF_map_mk {q : ℕ} (i : ℤ) {B C : CommRingCat.{0}} (f : B ⟶ C) (ζ : Prim q B) :
    ((twF q i).map f).hom (Submodule.Quotient.mk (Finsupp.single ζ 1)) =
      Submodule.Quotient.mk (Finsupp.single (ζ.map f.hom) 1) := by
  show Submodule.Quotient.mk (Finsupp.mapDomain _ (Finsupp.single ζ 1)) = _
  erw [Finsupp.mapDomain_single]

theorem inj_of (h : LateralTheory.EtaleFoundations.twF_gen_inj) (q : ℕ) [NeZero q] (U : Scheme.{0}) [Nonempty U] (i : ℤ)
    (ζ : Prim q Γ(U, ⊤)) : Function.Injective (fun c : ZMod q => c.val • twGen i ζ) := by
  intro c1 c2 hc
  simp only at hc
  let φ := ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)).app (op U)).hom
  let m : (Scheme.Γ ⋙ twF q i).obj (op U) := Submodule.Quotient.mk (Finsupp.single ζ 1)
  have hsec : φ (c1.val • m - c2.val • m) = 0 := by
    rw [map_sub, map_nsmul, map_nsmul]; exact sub_eq_zero.2 hc
  obtain ⟨u⟩ := (inferInstance : Nonempty U)
  have hloc : ∃ (V : Scheme.{0}) (j : V ⟶ U) (v : V),
      IsAffine V ∧ Etale j ∧ j v = u ∧
        ((twF q i).map j.appTop).hom (c1.val • m - c2.val • m) = 0 := by
    have h0 : φ (c1.val • m - c2.val • m) = φ 0 := by
      rw [map_zero]; exact hsec
    obtain ⟨V, j, v, hV, hj, hv, hS⟩ := LateralTheory.EtaleFoundations.OfRingsLoc.cov_pt _
      (Presheaf.equalizerSieve_mem Scheme.etaleTopology
        (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)) _ 0 h0) u
    refine ⟨V, j, v, hV, hj, hv, ?_⟩
    have h1 : ConcreteCategory.hom ((Scheme.Γ ⋙ twF q i).map j.op) (c1.val • m - c2.val • m) =
        ConcreteCategory.hom ((Scheme.Γ ⋙ twF q i).map j.op) 0 := hS
    rw [map_zero] at h1
    exact h1
  obtain ⟨V, j, v, -, -, -, hV⟩ := hloc
  let ψ := ((twF q i).map j.appTop).hom
  have hV2 : ψ (c1.val • m) = ψ (c2.val • m) := sub_eq_zero.1 ((ψ.map_sub _ _).symm.trans hV)
  erw [map_nsmul, map_nsmul] at hV2
  have hm : ψ m = Submodule.Quotient.mk (Finsupp.single (ζ.map j.appTop.hom) 1) := twF_map_mk i j.appTop ζ
  rw [hm] at hV2
  haveI : Nonempty (⊤ : V.Opens) := ⟨⟨v, trivial⟩⟩
  haveI : Nontrivial Γ(V, ⊤) := AlgebraicGeometry.Scheme.component_nontrivial V ⊤
  exact h q Γ(V, ⊤) inferInstance i (ζ.map j.appTop.hom) hV2

end LateralTheory.EtaleFoundations.GenConn
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.ChainsBasicPf

variable (R : Type) [CommRing R]

lemma chainsN_d (E : Spc) (p : ℕ) :
    ((chainsN R).obj E).d (p + 1) p = ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • (free R).map (E.δ i) :=
  AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq _ p

lemma chains_map_f {E E' : Spc} (f : E ⟶ E') (p : ℕ) :
    ((chains R).map f).f (-(p : ℤ)) =
      (chainsXIso R E p).hom ≫ (free R).map (f.app (op (SimplexCategory.mk p))) ≫ (chainsXIso R E' p).inv :=
  HomologicalComplex.extendMap_f _ _ rfl

lemma chains_d (E : Spc) (p : ℕ) :
    ((chains R).obj E).d (-((p + 1 : ℕ) : ℤ)) (-(p : ℤ)) =
      (chainsXIso R E (p + 1)).hom ≫ ((chainsN R).obj E).d (p + 1) p ≫ (chainsXIso R E p).inv :=
  HomologicalComplex.extend_d_eq _ _ rfl rfl

lemma chains_d' (E : Spc) (p : ℕ) :
    (chainsXIso R E (p + 1)).inv ≫ ((chains R).obj E).d (-((p + 1 : ℕ) : ℤ)) (-(p : ℤ)) ≫ (chainsXIso R E p).hom =
      ((chainsN R).obj E).d (p + 1) p := by
  rw [chains_d R E p]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  erw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

lemma chains_le (E : Spc) : ((chains R).obj E).IsStrictlyLE 0 :=
  inferInstanceAs (CochainComplex.IsStrictlyLE (((chainsN R).obj E).extend ComplexShape.embeddingDownNat) 0)

end LateralTheory.EtaleFoundations.ChainsBasicPf

open LateralTheory.EtaleFoundations.ChainsBasicPf in
theorem LateralTheory.EtaleFoundations.etale_simplicial_chains_basic_properties_hold : LateralTheory.EtaleFoundations.EtaleSimplicialChainsFreeDescription := by
  intro R _
  refine ⟨fun E => chains_le R E, fun {E E'} f p => ?_, fun E p => ?_⟩
  · rw [chains_map_f R f p]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  · rw [chains_d' R E p]
    exact chainsN_d R E p
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem LateralTheory.EtaleFoundations.etale_simplicial_cochain_short_exact_sequence_holds : LateralTheory.EtaleFoundations.EtaleCochainsInjectiveShortExact := by
  intro R _ I hI S hS n
  have hd := (HomologicalComplex.shortExact_iff_degreewise_shortExact S).1 hS
  have hv : ∀ {Y : Cx R} (φ : S.X₁ ⟶ Y) (z : Cochain Y I n) (p q : ℤ) (hpq : p + n = q),
      ((Cochain.ofHom φ).comp z (zero_add n)).v p q hpq = φ.f p ≫ z.v p q hpq := by
    intro Y φ z p q hpq
    rw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v]
  have hv2 : ∀ {Y : Cx R} (φ : S.X₂ ⟶ Y) (z : Cochain Y I n) (p q : ℤ) (hpq : p + n = q),
      ((Cochain.ofHom φ).comp z (zero_add n)).v p q hpq = φ.f p ≫ z.v p q hpq := by
    intro Y φ z p q hpq
    rw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v]
  have hm : ∀ p, Mono (S.f.f p) := fun p => (hd p).mono_f
  have he : ∀ p, Epi (S.g.f p) := fun p => (hd p).epi_g
  refine ⟨?_, ?_, ?_⟩
  · intro a
    refine ⟨Cochain.mk (fun p q h => haveI := hm p; haveI := hI q
      Injective.factorThru (a.v p q h) (S.f.f p)), ?_⟩
    apply Cochain.ext
    intro p q hpq
    rw [hv, Cochain.mk_v]
    have := hm p; have := hI q
    exact Injective.comp_factorThru _ _
  · intro b hb
    refine ⟨Cochain.mk (fun p q h => haveI := (hd p).epi_g
      (hd p).exact.desc (b.v p q h) (by
        have := congrArg (fun z => z.v p q h) hb
        simp only [hv] at this; exact this)), ?_⟩
    apply Cochain.ext
    intro p q hpq
    rw [hv2]
    haveI := (hd p).epi_g
    exact (hd p).exact.g_desc _ _
  · intro c hc
    apply Cochain.ext
    intro p q hpq
    have := congrArg (fun z => z.v p q hpq) hc
    simp only [hv2, Cochain.zero_v] at this
    have hep := he p
    rw [Cochain.zero_v]
    exact (cancel_epi (S.g.f p)).1 (by simpa using this)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def EtaleFreePresheafMayerVietorisShortExact : Prop :=
  ∀ (R : Type) [CommRing R] {P Q E : PSh} (f : P ⟶ E) (g : Q ⟶ E) [Mono f] [Mono g],
    Mono (biprod.lift ((free R).map (pullback.fst f g)) (-(free R).map (pullback.snd f g))) ∧
    ∃ w, (ShortComplex.mk (biprod.lift ((free R).map (pullback.fst f g)) (-(free R).map (pullback.snd f g)))
      (biprod.desc ((free R).map f) ((free R).map g)) w).Exact

theorem chainsXIso_nat (R : Type) [CommRing R] {E E' : Spc} (φ : E ⟶ E') (p : ℕ) :
    ((chains R).map φ).f (-(p : ℤ)) ≫ (chainsXIso R E' p).hom =
      (chainsXIso R E p).hom ≫ (free R).map (φ.app (op (SimplexCategory.mk p))) := by
  have h := HomologicalComplex.extendMap_f ((chainsN R).map φ) ComplexShape.embeddingDownNat (i := p) (i' := -(p:ℤ)) rfl
  have h2 : ((chains R).map φ).f (-(p:ℤ)) = (HomologicalComplex.extendMap ((chainsN R).map φ) ComplexShape.embeddingDownNat).f (-(p:ℤ)) := rfl
  rw [h2, h]
  simp only [chainsXIso]
  erw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

theorem chains_isZero (R : Type) [CommRing R] (E : Spc) (n : ℤ) (hn : 0 < n) :
    IsZero (((chains R).obj E).X n) := by
  apply HomologicalComplex.isZero_extend_X
  intro i h
  change -(i:ℤ) = n at h
  omega

theorem chainsXIso_nat' (R : Type) [CommRing R] {E E' : Spc} (φ : E ⟶ E') (p : ℕ) :
    (chainsXIso R E p).inv ≫ ((chains R).map φ).f (-(p : ℤ)) =
      (free R).map (φ.app (op (SimplexCategory.mk p))) ≫ (chainsXIso R E' p).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, ← chainsXIso_nat, Category.assoc, Iso.hom_inv_id, Category.comp_id]

theorem sq1 (R : Type) [CommRing R] {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E) (p : ℕ) :
    ((free R).map (pullbackObjIso f g (op (SimplexCategory.mk p))).inv ≫ (chainsXIso R (pullback f g) p).inv) ≫
      (biprod.lift ((chains R).map (pullback.fst f g)) (-(chains R).map (pullback.snd f g))).f (-(p:ℤ)) =
    biprod.lift ((free R).map (pullback.fst (f.app (op (SimplexCategory.mk p))) (g.app (op (SimplexCategory.mk p)))))
        (-(free R).map (pullback.snd (f.app (op (SimplexCategory.mk p))) (g.app (op (SimplexCategory.mk p))))) ≫
      (biprod.map (chainsXIso R U p).inv (chainsXIso R V p).inv ≫
        (HomologicalComplex.biprodXIso ((chains R).obj U) ((chains R).obj V) (-(p:ℤ))).inv) := by
  rw [← cancel_mono (HomologicalComplex.biprodXIso ((chains R).obj U) ((chains R).obj V) (-(p:ℤ))).hom]
  apply biprod.hom_ext
  · simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, HomologicalComplex.biprodXIso_hom_fst,
      biprod.map_fst, biprod.lift_fst_assoc]
    rw [← HomologicalComplex.comp_f, biprod.lift_fst, chainsXIso_nat', ← Category.assoc, ← Functor.map_comp,
      pullbackObjIso_inv_comp_fst]
  · simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, HomologicalComplex.biprodXIso_hom_snd,
      biprod.map_snd, biprod.lift_snd_assoc]
    rw [← HomologicalComplex.comp_f, biprod.lift_snd, HomologicalComplex.neg_f_apply, Preadditive.comp_neg,
      chainsXIso_nat']
    simp only [Preadditive.neg_comp, Preadditive.comp_neg]
    rw [← Category.assoc, ← Functor.map_comp, pullbackObjIso_inv_comp_snd]

theorem sq2 (R : Type) [CommRing R] {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E) (p : ℕ) :
    (biprod.map (chainsXIso R U p).inv (chainsXIso R V p).inv ≫
        (HomologicalComplex.biprodXIso ((chains R).obj U) ((chains R).obj V) (-(p:ℤ))).inv) ≫
      (biprod.desc ((chains R).map f) ((chains R).map g)).f (-(p:ℤ)) =
    biprod.desc ((free R).map (f.app (op (SimplexCategory.mk p)))) ((free R).map (g.app (op (SimplexCategory.mk p)))) ≫
      (chainsXIso R E p).inv := by
  apply biprod.hom_ext'
  · have h1 : biprod.inl ≫ (HomologicalComplex.biprodXIso ((chains R).obj U) ((chains R).obj V) (-(p:ℤ))).inv =
        (biprod.inl : (chains R).obj U ⟶ _).f (-(p:ℤ)) := by
      rw [Iso.comp_inv_eq]; apply biprod.hom_ext <;> simp [HomologicalComplex.biprodXIso_hom_fst,
        HomologicalComplex.biprodXIso_hom_snd, ← HomologicalComplex.comp_f]
    simp only [Category.assoc]
    rw [biprod.inl_map_assoc, reassoc_of% h1, ← HomologicalComplex.comp_f, biprod.inl_desc,
      chainsXIso_nat', biprod.inl_desc_assoc]
  · have h1 : biprod.inr ≫ (HomologicalComplex.biprodXIso ((chains R).obj U) ((chains R).obj V) (-(p:ℤ))).inv =
        (biprod.inr : (chains R).obj V ⟶ _).f (-(p:ℤ)) := by
      rw [Iso.comp_inv_eq]; apply biprod.hom_ext <;> simp [HomologicalComplex.biprodXIso_hom_fst,
        HomologicalComplex.biprodXIso_hom_snd, ← HomologicalComplex.comp_f]
    simp only [Category.assoc]
    rw [biprod.inr_map_assoc, reassoc_of% h1, ← HomologicalComplex.comp_f, biprod.inr_desc,
      chainsXIso_nat', biprod.inr_desc_assoc]

theorem etale_chains_mayer_vietoris_short_exact_of_free (hfree : EtaleFreePresheafMayerVietorisShortExact) : EtaleMayerVietorisChainsShortExact := by
  intro R _ U V E f g hc
  obtain ⟨hf, hg, hep⟩ := hc
  have w : biprod.lift ((chains R).map (pullback.fst f g)) (-(chains R).map (pullback.snd f g)) ≫
      biprod.desc ((chains R).map f) ((chains R).map g) = 0 := by
    rw [biprod.lift_desc, ← Functor.map_comp, Preadditive.neg_comp, ← Functor.map_comp, pullback.condition]
    simp
  refine ⟨w, ?_⟩
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  by_cases hn : 0 < n
  · have h1 := chains_isZero R (pullback f g) n hn
    have h3 := chains_isZero R E n hn
    have h2 : IsZero ((HomologicalComplex.eval (Shv R) (ComplexShape.up ℤ) n).obj
        ((chains R).obj U ⊞ (chains R).obj V)) := by
      have hU := chains_isZero R U n hn
      have hV := chains_isZero R V n hn
      refine IsZero.of_iso ?_ (HomologicalComplex.biprodXIso _ _ n)
      rw [IsZero.iff_id_eq_zero, ← biprod.total, hU.eq_of_tgt biprod.fst 0, hV.eq_of_tgt biprod.snd 0]
      simp
    refine ShortComplex.ShortExact.mk' (ShortComplex.exact_of_isZero_X₂ _ h2) ?_ ?_
    · exact ⟨fun a b _ => h1.eq_of_tgt a b⟩
    · exact ⟨fun a b _ => h3.eq_of_src a b⟩
  obtain ⟨p, rfl⟩ : ∃ p : ℕ, n = -(p : ℤ) := ⟨(-n).toNat, by omega⟩
  obtain ⟨hmono, w', hex⟩ := hfree R (f.app (op (SimplexCategory.mk p))) (g.app (op (SimplexCategory.mk p)))
  have hT := ShortComplex.ShortExact.mk' hex hmono (hep _)
  refine ShortComplex.shortExact_of_iso ?_ hT
  refine ShortComplex.isoMk ?e1 ?e2 ?e3 ?c1 ?c2
  case e1 =>
    refine ?_ ≪≫ (chainsXIso R _ p).symm
    exact (free R).mapIso (pullbackObjIso f g _).symm
  case e2 => exact biprod.mapIso (chainsXIso R U p).symm (chainsXIso R V p).symm ≪≫
      (HomologicalComplex.biprodXIso _ _ _).symm
  case e3 => exact (chainsXIso R E p).symm
  case c1 => exact sq1 R f g p
  case c2 => exact sq2 R f g p

end LateralTheory.EtaleFoundations
end
