module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.Bundle001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.SameNormBasic
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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

@[expose] public section

section

open TensorProduct Module
open UpperTheory.Gal.crystallineComparison

private lemma UpperTheory.Gal.crystallineComparison.map_id_eq_rTensor {F B L U V : Type} [Field F] [AddCommGroup B] [Module F B]
    [Field L] [Algebra F L] [AddCommGroup U] [Module L U] [Module F U] [IsScalarTower F L U]
    [AddCommGroup V] [Module L V] [Module F V] [IsScalarTower F L V] (f : U →ₗ[L] V) (x : U ⊗[F] B) :
    AlgebraTensorModule.map f (LinearMap.id : B →ₗ[F] B) x = LinearMap.rTensor B (f.restrictScalars F) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul u b => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

private lemma UpperTheory.Gal.crystallineComparison.inter_map {F G B L U V : Type} [Field F] [Group G] [AddCommGroup B] [Module F B]
    (σ : G → End F B) [Field L] [Algebra F L] [AddCommGroup U] [Module L U] [Module F U] [IsScalarTower F L U]
    [AddCommGroup V] [Module L V] [Module F V] [IsScalarTower F L V]
    {ρ : Representation L G U} {ρ' : Representation L G V} {f : U →ₗ[L] V} (hf : Inter ρ ρ' f) (g : G) (x : U ⊗[F] B) :
    AlgebraTensorModule.map f (LinearMap.id : B →ₗ[F] B) (AlgebraTensorModule.map (ρ g) (σ g) x) =
      AlgebraTensorModule.map (ρ' g) (σ g) (AlgebraTensorModule.map f (LinearMap.id : B →ₗ[F] B) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul u b => simp [hf g u]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem UpperTheory.Gal.crystallineComparison.dinvExact_of :
    DinvExact := by
  intro F G B _ _ _ _ σ L _ _ U V W _ _ _ _ _ _ _ _ _ _ _ _ ρU ρV ρW i p hi hp hinj hex hfin
  have hI : Function.Injective (AlgebraTensorModule.map i (LinearMap.id : B →ₗ[F] B)) := by
    have h := Module.Flat.rTensor_preserves_injective_linearMap (M := B) (i.restrictScalars F) hinj
    intro x y hxy
    apply h
    rw [← map_id_eq_rTensor, ← map_id_eq_rTensor]
    exact hxy
  have hE : Function.Exact (AlgebraTensorModule.map i (LinearMap.id : B →ₗ[F] B))
      (AlgebraTensorModule.map p (LinearMap.id : B →ₗ[F] B)) := by
    have h := Module.Flat.rTensor_exact (f := i.restrictScalars F) (g := p.restrictScalars F) B hex
    have e1 : (AlgebraTensorModule.map i (LinearMap.id : B →ₗ[F] B) : U ⊗[F] B → V ⊗[F] B) =
        LinearMap.rTensor B (i.restrictScalars F) := funext (map_id_eq_rTensor i)
    have e2 : (AlgebraTensorModule.map p (LinearMap.id : B →ₗ[F] B) : V ⊗[F] B → W ⊗[F] B) =
        LinearMap.rTensor B (p.restrictScalars F) := funext (map_id_eq_rTensor p)
    rw [e1, e2]
    exact h
  have key : (Dinv σ ρU).map (AlgebraTensorModule.map i (LinearMap.id : B →ₗ[F] B)) =
      Dinv σ ρV ⊓ LinearMap.ker (AlgebraTensorModule.map p (LinearMap.id : B →ₗ[F] B)) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨?_, ?_⟩
      · refine (mem_Dinv σ).2 fun g => ?_
        rw [← inter_map σ hi, (mem_Dinv σ).1 hx g]
      · exact (hE _).2 ⟨x, rfl⟩
    · rintro ⟨hy, hk⟩
      obtain ⟨x, rfl⟩ := (hE y).1 hk
      refine ⟨x, (mem_Dinv σ).2 fun g => hI ?_, rfl⟩
      rw [inter_map σ hi, (mem_Dinv σ).1 hy g]
  refine ⟨?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    refine (mem_Dinv σ).2 fun g => ?_
    rw [← inter_map σ hp, (mem_Dinv σ).1 hx g]
  · have h1 := LinearMap.finrank_range_add_finrank_ker
      ((AlgebraTensorModule.map p (LinearMap.id : B →ₗ[F] B)).domRestrict (Dinv σ ρV))
    rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict] at h1
    have h2 : finrank L (Submodule.comap (Dinv σ ρV).subtype
        (LinearMap.ker (AlgebraTensorModule.map p (LinearMap.id : B →ₗ[F] B)))) =
        finrank L (Dinv σ ρU) := by
      rw [← Submodule.finrank_map_subtype_eq, Submodule.map_comap_subtype, ← key]
      exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hI _)).symm
    rw [h2] at h1
    omega
end

section

open TensorProduct Module
open UpperTheory.Gal.crystallineComparison

private theorem admissible_exact_sequence (hD : DinvExact) {F G B : Type} [Field F] [Group G] [AddCommGroup B] [Module F B]
    (σ : G → End F B) {L : Type} [Field L] [Algebra F L] {e : ℕ} (hB : Bound σ L e)
    {U V W : Type} [AddCommGroup U] [Module L U] [Module F U] [IsScalarTower F L U] [Module.Finite L U]
    [AddCommGroup V] [Module L V] [Module F V] [IsScalarTower F L V] [Module.Finite L V]
    [AddCommGroup W] [Module L W] [Module F W] [IsScalarTower F L W] [Module.Finite L W]
    (ρU : Representation L G U) (ρV : Representation L G V) (ρW : Representation L G W)
    (i : U →ₗ[L] V) (p : V →ₗ[L] W) (hi : Inter ρU ρV i) (hp : Inter ρV ρW p)
    (inj : Function.Injective i) (ex : Function.Exact i p) (surj : Function.Surjective p)
    (hA : admitted σ e ρV) :
    admitted σ e ρU ∧ admitted σ e ρW ∧
      (Dinv σ ρV).map (AlgebraTensorModule.map p (LinearMap.id : B →ₗ[F] B)) = Dinv σ ρW := by
  obtain ⟨fU, bU⟩ := hB U ρU
  obtain ⟨fV, -⟩ := hB V ρV
  obtain ⟨fW, bW⟩ := hB W ρW
  obtain ⟨hle, hdim⟩ := hD F G B σ L U V W ρU ρV ρW i p hi hp inj ex fV
  have hmono := Submodule.finrank_mono hle
  have hrank : finrank L V = finrank L U + finrank L W := by
    have h1 := LinearMap.finrank_range_add_finrank_ker p
    rw [LinearMap.range_eq_top.mpr surj, finrank_top, LinearMap.exact_iff.mp ex,
      LinearMap.finrank_range_of_inj inj] at h1
    omega
  unfold admitted at hA ⊢
  rw [hrank, mul_add] at hA
  have h2 : finrank L (Dinv σ ρU) = e * finrank L U := by omega
  have h3 : finrank L (Dinv σ ρW) = e * finrank L W := by omega
  refine ⟨h2, h3, Submodule.eq_of_le_of_finrank_eq hle ?_⟩
  omega

theorem UpperTheory.Gal.crystallineComparison.admissibleExact_of_dualInvariantExact :
    DinvExact → AdmExact := by
  intro hD
  unfold AdmExact
  intro F G B _ _ _ _ σ L _ _ e hB V W _ _ _ _ _ _ _ _ _ _ ρ ρ' f hf
  refine ⟨fun inj hA => ?_, fun surj hA => ?_⟩
  · let ρQ : Representation L G (W ⧸ LinearMap.range f) :=
      { toFun := fun g => (LinearMap.range f).mapQ (LinearMap.range f) (ρ' g) (by
          rintro _ ⟨v, rfl⟩
          exact ⟨ρ g v, hf g v⟩)
        map_one' := by
          ext w
          simp
        map_mul' := by
          intro g h
          ext w
          simp [map_mul] }
    have hQ : UpperTheory.Gal.crystallineComparison.Inter ρ' ρQ (LinearMap.range f).mkQ := fun g w => rfl
    exact (admissible_exact_sequence hD σ hB ρ ρ' ρQ f (LinearMap.range f).mkQ hf hQ inj
      (LinearMap.exact_map_mkQ_range f) (Submodule.mkQ_surjective _) hA).1
  · have hK : ∀ (g : G) (x : LinearMap.ker f), ρ g x ∈ LinearMap.ker f := by
      intro g x
      rw [LinearMap.mem_ker, hf g x, LinearMap.mem_ker.mp x.2, map_zero]
    let ρK : Representation L G (LinearMap.ker f) :=
      { toFun := fun g => LinearMap.codRestrict (LinearMap.ker f)
          ((ρ g).comp (LinearMap.ker f).subtype) (hK g)
        map_one' := by
          ext x
          simp
        map_mul' := by
          intro g h
          ext x
          simp only [map_mul, Module.End.mul_apply]
          rfl }
    have hKi : UpperTheory.Gal.crystallineComparison.Inter ρK ρ (LinearMap.ker f).subtype := fun g x => rfl
    obtain ⟨-, hW, hmap⟩ := admissible_exact_sequence hD σ hB ρK ρ ρ' (LinearMap.ker f).subtype f hKi hf
      (LinearMap.ker f).injective_subtype (LinearMap.exact_subtype_ker_map f) surj hA
    exact ⟨hW, hmap⟩
end

section

noncomputable section

namespace UpperTheory.Gal.crystallineComparison

theorem countOut_of : CountOut := by
  intro k H _ _ _ _ _ C hC E
  obtain ⟨s0, hs0⟩ := Module.projective_lifting_property C.mkQ E.subtype (Submodule.mkQ_surjective C)
  have hsec : ∀ (s : E →ₗ[k] H), C.mkQ ∘ₗ s = E.subtype → ∀ e : E, C.mkQ (s e) = e := by
    intro s hs e
    exact LinearMap.congr_fun hs e
  let S := {s : E →ₗ[k] H // C.mkQ ∘ₗ s = E.subtype}
  have hF : ∀ s : S, ¬C ≤ LinearMap.range s.1 ∧ Submodule.map C.mkQ (LinearMap.range s.1) = E := by
    intro s
    constructor
    · intro hle
      haveI : Nontrivial C := Module.nontrivial_of_finrank_eq_succ hC
      obtain ⟨c, hc⟩ := exists_ne (0 : C)
      obtain ⟨e, he⟩ := LinearMap.mem_range.1 (hle c.2)
      have h1 : C.mkQ (s.1 e) = e := hsec s.1 s.2 e
      have h2 : C.mkQ (c : H) = 0 := (Submodule.Quotient.mk_eq_zero C).2 c.2
      rw [he, h2] at h1
      have e0 : e = 0 := Subtype.ext h1.symm
      apply hc
      apply Subtype.ext
      rw [← he, e0, map_zero]
      rfl
    · rw [← LinearMap.range_comp, s.2, Submodule.range_subtype]
  let F : S → {D : Submodule k H // ¬C ≤ D ∧ Submodule.map C.mkQ D = E} :=
    fun s => ⟨LinearMap.range s.1, hF s⟩
  have hFb : Function.Bijective F := by
    constructor
    · intro s t h
      have h' : LinearMap.range s.1 = LinearMap.range t.1 := congrArg Subtype.val h
      apply Subtype.ext
      apply LinearMap.ext
      intro e
      have hm : s.1 e ∈ LinearMap.range t.1 := h' ▸ LinearMap.mem_range_self s.1 e
      obtain ⟨e', he'⟩ := LinearMap.mem_range.1 hm
      have h1 := hsec t.1 t.2 e'
      rw [he', hsec s.1 s.2 e] at h1
      have : e' = e := Subtype.ext h1.symm
      rw [← he', this]
    · rintro ⟨D, hnot, hmap⟩
      have hdisj : ∀ x ∈ D, x ∈ C → x = 0 := by
        intro x hxD hxC
        by_contra hx
        apply hnot
        intro y hy
        have hx' : (⟨x, hxC⟩ : C) ≠ 0 := fun h => hx (congrArg Subtype.val h)
        obtain ⟨a, ha⟩ := (finrank_eq_one_iff_of_nonzero' _ hx').1 hC ⟨y, hy⟩
        have : a • x = y := congrArg Subtype.val ha
        rw [← this]
        exact D.smul_mem a hxD
      let f : D →ₗ[k] H ⧸ C := C.mkQ ∘ₗ D.subtype
      have hf : Function.Injective f := by
        rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
        intro d hd
        apply Subtype.ext
        exact hdisj d.1 d.2 ((Submodule.Quotient.mk_eq_zero C).1 hd)
      have hr : LinearMap.range f = E := by
        rw [LinearMap.range_comp, Submodule.range_subtype, hmap]
      let φ : D ≃ₗ[k] E := (LinearEquiv.ofInjective f hf).trans (LinearEquiv.ofEq _ _ hr)
      have hφ : ∀ d : D, ((φ d : E) : H ⧸ C) = C.mkQ d := fun d => rfl
      let s : E →ₗ[k] H := D.subtype ∘ₗ (φ.symm : E →ₗ[k] D)
      have hs : C.mkQ ∘ₗ s = E.subtype := by
        apply LinearMap.ext
        intro e
        have h1 := hφ (φ.symm e)
        rw [LinearEquiv.apply_symm_apply] at h1
        exact h1.symm
      refine ⟨⟨s, hs⟩, Subtype.ext ?_⟩
      show LinearMap.range s = D
      rw [LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range φ.symm), Submodule.range_subtype]
  let G : (E →ₗ[k] C) → S := fun g =>
    ⟨s0 + C.subtype ∘ₗ g, by
      apply LinearMap.ext
      intro e
      have h1 := LinearMap.congr_fun hs0 e
      have h2 : C.mkQ (g e : H) = 0 := (Submodule.Quotient.mk_eq_zero C).2 (g e).2
      simp only [LinearMap.comp_apply, LinearMap.add_apply, map_add (f := _), Submodule.subtype_apply] at h1 ⊢
      rw [h2, add_zero, h1]⟩
  have hGb : Function.Bijective G := by
    constructor
    · intro g g' h
      apply LinearMap.ext
      intro e
      apply Subtype.ext
      have := LinearMap.congr_fun (congrArg Subtype.val h) e
      simpa [G] using this
    · rintro ⟨s, hs⟩
      have hmem : ∀ e, s e - s0 e ∈ C := by
        intro e
        apply (Submodule.Quotient.mk_eq_zero C).1
        have h1 := hsec s hs e
        have h2 := hsec s0 hs0 e
        simp only [Submodule.mkQ_apply] at h1 h2
        rw [Submodule.Quotient.mk_sub, h1, h2, sub_self]
      refine ⟨LinearMap.codRestrict C (s - s0) hmem, Subtype.ext ?_⟩
      apply LinearMap.ext
      intro e
      simp [G]
  have hcard : Nat.card (E →ₗ[k] C) = Nat.card k ^ Module.finrank k E := by
    haveI : Fintype k := Fintype.ofFinite k
    haveI : Finite (E →ₗ[k] C) := Module.finite_of_finite k
    haveI : Fintype (E →ₗ[k] C) := Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card (α := E →ₗ[k] C), Nat.card_eq_fintype_card (α := k), Module.card_eq_pow_finrank (K := k) (V := E →ₗ[k] C),
      Module.finrank_linearMap k k E C, hC, mul_one]
  rw [← Nat.card_eq_of_bijective F hFb, ← Nat.card_eq_of_bijective G hGb, hcard]

end UpperTheory.Gal.crystallineComparison
end
end

section

open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.normPt_of :
    SameNormRing → BaseOfChart → SecChart → EtAwayChart → GenChart → PtChart → NormOfPt := by
  intro hSN hBOC hSec hEA hGen hPtC l f n hl O _ _ _ ϖ hϖ hl0 hlu Y g hg T hPt U V hU hV h
  intro B _ _ hlB I _ z hs B' _ ρ hρπ ι _ x
  set q := l ^ f with hq
  set πU := Y.presheaf.map (homOfLE le_top).op (fn g ϖ) with hπU
  letI : ∀ j, Algebra Γ(Y, U) Γ((T j).Z, (T j).p ⁻¹ᵁ U) := fun j => (T j).alg U
  obtain ⟨hBase, m, hm⟩ := hBOC l O ϖ hϖ hl0 hlu Y g hg U hU
  let s : (j : Fin (n + 1)) → ι → Γ((T j).Z, (T j).p ⁻¹ᵁ U) := fun j k =>
    ((T j).r.appLE V ((T j).p ⁻¹ᵁ U) (h j)).hom (x k) ^ (q ^ (n - (j : ℕ)))
  have hρ : ∀ a ∈ Ideal.span {πU}, ρ (algebraMap Γ(Y, U) B a) = 0 := by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [map_mul, map_mul, hρπ, mul_zero]
  have key := hSN l Γ(Y, U) (Ideal.span {πU}) hBase (Fin (n + 1))
    (fun j => Γ((T j).Z, (T j).p ⁻¹ᵁ U)) (fun j => (T j).d) (fun j => hEA l Y (T j) U hU)
    (wEv q) (wOd q) ι s ?_ B hlB I z hs B' ρ hρ
  · simpa only [s, map_pow] using key
  intro W _ _ _ _ _ hlW hmin J _ zz hbij
  have hgen := hGen Y (fn g ϖ) U hU W (algebraMap Γ(Y, U) W) hmin
  have hlm : (l : W) ∈ IsLocalRing.maximalIdeal W := by
    have h1 : ((l : Γ(Y, U)) ^ m) ∈ Ideal.comap (algebraMap Γ(Y, U) W) (IsLocalRing.maximalIdeal W) :=
      hmin.1.2 hm
    rw [Ideal.mem_comap, map_pow, map_natCast] at h1
    exact (IsLocalRing.maximalIdeal.isMaximal W).isPrime.mem_of_pow_mem m h1
  have hlκ : ((l : IsLocalRing.ResidueField W)) = 0 := by
    rw [← map_natCast (IsLocalRing.residue W), IsLocalRing.residue_eq_zero_iff]
    exact hlm
  haveI : Fact l.Prime := ⟨hl⟩
  haveI : CharP (IsLocalRing.ResidueField W) l := (CharP.charP_iff_prime_eq_zero hl).mpr hlκ
  let φ := iterateFrobenius (IsLocalRing.ResidueField W) l f
  have hφ : ∀ a, φ a = a ^ q := fun a => rfl
  have hφm : ∀ (k : ℕ) a, (φ ^ k) a = a ^ (q ^ k) := by
    intro k
    induction k with
    | zero => intro a; simp
    | succ k ih =>
      intro a
      rw [pow_succ, RingHom.mul_def, RingHom.comp_apply, ih, hφ, ← pow_mul, pow_succ']
  choose hZ hE using fun j => hSec l Y (T j) U hU
  choose e he using fun j => hE j W
  have hbij' : ∀ j, Function.Bijective (fun i => e j (zz j i)) :=
    fun j => (e j).bijective.comp (hbij j)
  have alt := hPt W hlW (ptOf hU W (algebraMap Γ(Y, U) W)) hgen φ hφ J (fun j i => e j (zz j i)) hbij'
  unfold AltId at alt
  have hterm : ∀ (j : Fin (n + 1)) (i : J j),
      (twist φ Y)^[n - (j : ℕ)] (resPt W ≫ (e j (zz j i)).1 ≫ (T j).r) =
        ptOf hV (IsLocalRing.ResidueField W) ((φ ^ (n - (j : ℕ))).comp ((IsLocalRing.residue W).comp
          ((zz j i).toRingHom.comp ((T j).r.appLE V ((T j).p ⁻¹ᵁ U) (h j)).hom))) := by
    intro j i
    rw [he j (zz j i)]
    unfold resPt
    rw [(hPtC Y V hV (IsLocalRing.ResidueField W)).2.2 (T j).Z (T j).r ((T j).p ⁻¹ᵁ U) (hZ j) (h j) W
      (IsLocalRing.residue W) (zz j i).toRingHom]
    rw [(hPtC Y V hV (IsLocalRing.ResidueField W)).2.1]
  simp only [hterm] at alt
  classical
  let G : (Spec (CommRingCat.of (IsLocalRing.ResidueField W)) ⟶ Y) → ι → IsLocalRing.ResidueField W :=
    fun P k => if hP : ∃ F, ptOf hV (IsLocalRing.ResidueField W) F = P then (Classical.choose hP) (x k) else 0
  have hG : ∀ F, G (ptOf hV (IsLocalRing.ResidueField W) F) = fun k => F (x k) := by
    intro F
    funext k
    have hP : ∃ F', ptOf hV (IsLocalRing.ResidueField W) F' = ptOf hV (IsLocalRing.ResidueField W) F := ⟨F, rfl⟩
    simp only [G, dif_pos hP]
    rw [(hPtC Y V hV (IsLocalRing.ResidueField W)).1 (Classical.choose_spec hP)]
  have alt2 := congrArg (Multiset.map G) alt
  rw [pts_map, pts_map] at alt2
  simp only [hG, RingHom.comp_apply, hφm, AlgHom.coe_toRingHom] at alt2
  simp only [s, map_pow]
  exact alt2
end

section

open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.secChart_of :
    SecChart := by
  intro l Y T U hU
  haveI := T.fin
  letI := T.alg U
  have hZ : IsAffineOpen (T.p ⁻¹ᵁ U) := hU.preimage T.p
  have hsq : Spec.map (T.p.app U) ≫ hU.fromSpec = hZ.fromSpec ≫ T.p := by
    rw [Scheme.Hom.app_eq_appLE]
    exact IsAffineOpen.SpecMap_appLE_fromSpec T.p hU hZ le_rfl
  refine ⟨hZ, fun B _ _ => ?_⟩
  have hrange : ∀ z : T.Sec (ptOf hU B (algebraMap Γ(Y, U) B)),
      Set.range z.1 ⊆ Set.range hZ.fromSpec := by
    rintro z _ ⟨x, rfl⟩
    rw [hZ.range_fromSpec]
    have hx : (z.1 ≫ T.p) x ∈ Set.range hU.fromSpec := by
      rw [z.2]
      unfold ptOf
      rw [Scheme.Hom.comp_apply]
      exact ⟨_, rfl⟩
    rw [hU.range_fromSpec] at hx
    simpa using hx
  have hlift : ∀ z : T.Sec (ptOf hU B (algebraMap Γ(Y, U) B)),
      Spec.map (T.p.app U ≫ Spec.preimage (IsOpenImmersion.lift hZ.fromSpec z.1 (hrange z)))
        = Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, U) B)) := by
    intro z
    rw [← cancel_mono hU.fromSpec, Spec.map_comp, Category.assoc, hsq, Spec.map_preimage,
      IsOpenImmersion.lift_fac_assoc]
    exact z.2
  refine ⟨{ toFun := fun g => ⟨Spec.map (CommRingCat.ofHom g.toRingHom) ≫ hZ.fromSpec, ?_⟩,
            invFun := fun z =>
              { toRingHom := (Spec.preimage (IsOpenImmersion.lift hZ.fromSpec z.1 (hrange z))).hom
                commutes' := fun r => by
                  have h := congrArg (fun φ => φ.hom r) (Spec.map_injective (hlift z))
                  exact h }
            left_inv := fun g => ?_
            right_inv := fun z => ?_ }, fun z => rfl⟩
  · show _ = Spec.map _ ≫ hU.fromSpec
    rw [Category.assoc, ← hsq, ← Spec.map_comp_assoc]
    congr 2
    ext r
    exact g.commutes r
  · apply AlgHom.coe_ringHom_injective
    show (Spec.preimage _).hom = (CommRingCat.ofHom g.toRingHom).hom
    congr 1
    apply Spec.map_injective
    rw [Spec.map_preimage]
    exact (IsOpenImmersion.lift_uniq _ _ _ _ rfl).symm
  · apply Subtype.ext
    show Spec.map (Spec.preimage _) ≫ _ = _
    rw [Spec.map_preimage, IsOpenImmersion.lift_fac]
end

section

open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.etAway_of :
    SecChart → EtChart → EtAwayChart := by
  intro hsec het l Y T U hU
  obtain ⟨hZ, hpts⟩ := hsec l Y T U hU
  have hfin := @IsFinite.finite_app _ _ _ T.fin U hU
  letI : Algebra Γ(Y, U) Γ(T.Z, T.p ⁻¹ᵁ U) := (T.p.app U).hom.toAlgebra
  refine EtAway.mk hfin (het l Y T U hU) ?_
  intro K _ _ _ hl
  obtain ⟨e, -⟩ := hpts K
  rw [Nat.card_congr e]
  exact T.deg K hl _
end

section

open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.rankDeg_of :
    SplitsField → RankOfDeg := by
  intro hSF A S _ _ _ _ _ d hd
  funext p
  letI : Algebra A (AlgebraicClosure p.asIdeal.ResidueField) :=
    ((algebraMap p.asIdeal.ResidueField (AlgebraicClosure p.asIdeal.ResidueField)).comp
      (algebraMap A p.asIdeal.ResidueField)).toAlgebra
  let q : PrimeSpectrum (AlgebraicClosure p.asIdeal.ResidueField) := ⟨⊥, Ideal.isPrime_bot⟩
  have hq : PrimeSpectrum.comap (algebraMap A (AlgebraicClosure p.asIdeal.ResidueField)) q = p := by
    ext x
    change algebraMap A (AlgebraicClosure p.asIdeal.ResidueField) x ∈ (⊥ : Ideal _) ↔ x ∈ p.asIdeal
    rw [Ideal.mem_bot]
    change algebraMap p.asIdeal.ResidueField (AlgebraicClosure p.asIdeal.ResidueField)
      (algebraMap A p.asIdeal.ResidueField x) = 0 ↔ x ∈ p.asIdeal
    rw [map_eq_zero_iff _ (algebraMap p.asIdeal.ResidueField _).injective,
      Ideal.algebraMap_residueField_eq_zero]
  rw [← hq, ← Module.rankAtStalk_baseChange q, Module.rankAtStalk_eq_finrank_of_free]
  obtain ⟨hfin, hsp⟩ := hSF A S (AlgebraicClosure p.asIdeal.ResidueField) inferInstance
  haveI := Fintype.ofFinite (S →ₐ[A] AlgebraicClosure p.asIdeal.ResidueField)
  have e := AlgEquiv.ofBijective (splitMap fun z => z) hsp
  have h1 := e.toLinearEquiv.finrank_eq
  rw [Module.finrank_fintype_fun_eq_card, ← Nat.card_eq_fintype_card,
    hd (AlgebraicClosure p.asIdeal.ResidueField)] at h1
  simp [h1]
end
