module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.Bundle001
public import Mathlib.RingTheory.RingHom.Etale
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle127
public import Mathlib.Algebra.Algebra.Epi
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.CosieveRes
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.DcColSurj
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.DoubleComplexMapMemTotal
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MapHComp
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.CubeTheorem.LBSpreads
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.ExPhiPlusOnto
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle131
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle132
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
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Polynomial DividedPowers GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B
open TensorProduct

namespace GlobalTheory.CompanionTheory.EtalePerfect

theorem surjective_of_unramified {R S : Type} [CommRing R] [CommRing S] (p : ℕ) (hp : p.Prime)
    (hS : (p : S) = 0) (f : R →+* S) (hu : f.FormallyUnramified) (hft : f.FiniteType)
    (hpow : ∀ x : S, ∃ r, f r = x ^ p) : Function.Surjective f := by
  algebraize [f]
  have hint : Algebra.IsIntegral R S := ⟨fun x => by
    obtain ⟨r, hr⟩ := hpow x
    refine IsIntegral.of_pow hp.pos ?_
    rw [← hr]
    exact isIntegral_algebraMap⟩
  have hfin : Module.Finite R S := Algebra.IsIntegral.finite
  obtain ⟨t, ht2, ht1⟩ := Algebra.FormallyUnramified.iff_exists_tensorProduct.1
    (inferInstance : Algebra.FormallyUnramified R S)
  have hT : (p : S ⊗[R] S) = 0 := by
    rw [← map_natCast (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[R] S), hS, map_zero]
  have hadd : ∀ x y : S ⊗[R] S, (x + y) ^ p = x ^ p + y ^ p := by
    intro x y
    obtain ⟨c, hc⟩ := exists_add_pow_prime_eq hp x y
    rw [hc, hT]
    simp
  have haddS : ∀ x y : S, (x + y) ^ p = x ^ p + y ^ p := by
    intro x y
    obtain ⟨c, hc⟩ := exists_add_pow_prime_eq hp x y
    rw [hc, hS]
    simp
  have hfrob : ∀ u : S ⊗[R] S,
      u ^ p = ((Algebra.TensorProduct.lmul' R (S := S) u) ^ p) ⊗ₜ[R] (1 : S) := by
    intro u
    induction u using TensorProduct.induction_on with
    | zero => simp [zero_pow hp.ne_zero]
    | tmul a b =>
      obtain ⟨s, hs⟩ := hpow b
      have hs' : b ^ p = s • (1 : S) := by
        rw [← hs, Algebra.smul_def, mul_one]; rfl
      rw [Algebra.TensorProduct.tmul_pow, Algebra.TensorProduct.lmul'_apply_tmul, mul_pow, hs',
        TensorProduct.tmul_smul, mul_smul_comm, mul_one, TensorProduct.smul_tmul']
    | add x y hx hy =>
      rw [hadd, hx, hy, map_add (f := _), haddS, TensorProduct.add_tmul]
  have hmul : ∀ u : S ⊗[R] S,
      u * t = (Algebra.TensorProduct.lmul' R (S := S) u ⊗ₜ[R] (1 : S)) * t := by
    intro u
    induction u using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      have hb := ht2 b
      rw [sub_mul, sub_eq_zero] at hb
      have : a ⊗ₜ[R] b = (a ⊗ₜ[R] (1 : S)) * ((1 : S) ⊗ₜ[R] b) := by simp
      rw [this, mul_assoc, hb, ← mul_assoc]
      simp
    | add x y hx hy =>
      rw [add_mul, hx, hy, map_add (f := _), TensorProduct.add_tmul, add_mul]
  have hidem : t * t = t := by
    rw [hmul t, ht1]
    exact one_mul t
  have htp : t ^ p = t := (show IsIdempotentElem t from hidem).pow_eq hp.ne_zero
  have ht : t = 1 := by
    rw [← htp, hfrob t, ht1, one_pow]
    rfl
  have hepi : Algebra.IsEpi R S := by
    rw [Algebra.isEpi_iff_forall_one_tmul_eq]
    intro s
    have := ht2 s
    rw [ht, mul_one, sub_eq_zero] at this
    exact this
  exact Algebra.isEpi_iff_surjective_algebraMap_of_finite.1 hepi

theorem pf_of_etale : ∀ (p : ℕ), p.Prime → ∀ {P E : Type} [CommRing P] [CommRing E] (ψ : P →+* E),
    ψ.Etale → D.Pf p P → D.Pf p E := by
  intro p hp P E _ _ ψ hψ hP
  have hEc : (p : E) = 0 := by rw [← map_natCast ψ, hP.char, map_zero]
  have hadd : ∀ {A : Type} [CommRing A], (p : A) = 0 → ∀ x y : A, (x + y) ^ p = x ^ p + y ^ p := by
    intro A _ h x y
    obtain ⟨c, hc⟩ := exists_add_pow_prime_eq hp x y
    rw [hc, h]
    simp
  let φ : E →+* E :=
    { toFun := fun x => x ^ p
      map_one' := one_pow p
      map_mul' := fun x y => mul_pow x y p
      map_zero' := zero_pow hp.ne_zero
      map_add' := hadd hEc }
  let Fp : P →+* P :=
    { toFun := fun x => x ^ p
      map_one' := one_pow p
      map_mul' := fun x y => mul_pow x y p
      map_zero' := zero_pow hp.ne_zero
      map_add' := hadd hP.char }
  let e : P ≃+* P := RingEquiv.ofBijective Fp hP.bij
  let G : P →+* P := e.symm.toRingHom
  have hFG : ∀ x, (G x) ^ p = x := fun x => e.apply_symm_apply x
  have hGF : ∀ x, G (x ^ p) = x := fun x => e.symm_apply_apply x
  have hcomp : φ.comp (ψ.comp G) = ψ := by
    ext x
    change (ψ (G x)) ^ p = ψ x
    rw [← map_pow, hFG]
  have hUψ : ψ.FormallyUnramified := hψ.formallyUnramified
  have hFTψ : ψ.FiniteType := by
    algebraize [ψ]
    have : Algebra.Etale P E := hψ.toAlgebra
    exact (inferInstance : Algebra.FiniteType P E)
  have hu : φ.FormallyUnramified := by
    rw [← hcomp] at hUψ
    exact RingHom.FormallyUnramified.of_comp hUψ
  have hft : φ.FiniteType := by
    rw [← hcomp] at hFTψ
    exact RingHom.FiniteType.of_comp_finiteType hFTψ
  have hsurj : Function.Surjective φ :=
    surjective_of_unramified p hp hEc φ hu hft (fun x => ⟨x, rfl⟩)
  let N : Ideal E := RingHom.ker φ
  have hN : ∀ x ∈ N, IsNilpotent x := fun x hx => ⟨p, hx⟩
  have hL : EtLift N := GlobalTheory.T.etale_lifting_of_nil_ideal N hN
  let eb : (E ⧸ N) ≃+* E := RingHom.quotientKerEquivOfSurjective hsurj
  have heb : ∀ x, eb (Ideal.Quotient.mk N x) = x ^ p := fun x => rfl
  let g : E →+* E ⧸ N := eb.symm.toRingHom
  have hg : ∀ x, g (x ^ p) = Ideal.Quotient.mk N x := by
    intro x
    apply eb.injective
    rw [heb]
    exact eb.apply_symm_apply _
  have hgψ : g.comp ψ = (Ideal.Quotient.mk N).comp (ψ.comp G) := by
    ext x
    apply eb.injective
    change eb (eb.symm (ψ x)) = eb (Ideal.Quotient.mk N (ψ (G x)))
    rw [eb.apply_symm_apply, heb, ← map_pow, hFG]
  obtain ⟨h, ⟨hh1, hh2⟩, -⟩ := hL P E ψ hψ (ψ.comp G) g hgψ
  have hid : h.comp φ = RingHom.id E := by
    refine (hL P E ψ hψ ψ (Ideal.Quotient.mk N) rfl).unique ⟨?_, ?_⟩ ⟨?_, ?_⟩
    · ext x
      change h ((ψ x) ^ p) = ψ x
      rw [← map_pow]
      have := RingHom.congr_fun hh1 (x ^ p)
      simp only [RingHom.comp_apply] at this
      rw [this, hGF]
    · ext x
      have := RingHom.congr_fun hh2 (x ^ p)
      simp only [RingHom.comp_apply] at this
      change Ideal.Quotient.mk N (h (x ^ p)) = _
      rw [this, hg]
    · rfl
    · rfl
  refine ⟨hEc, ?_, ?_⟩
  · intro x y hxy
    have hx := RingHom.congr_fun hid x
    have hy := RingHom.congr_fun hid y
    simp only [RingHom.comp_apply, RingHom.id_apply] at hx hy
    rw [← hx, ← hy]
    exact congrArg h hxy
  · exact hsurj

end GlobalTheory.CompanionTheory.EtalePerfect
end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CrystallineSemistableComparison CrystallineSemistableComparison.Onto

universe w w'

namespace GlobalTheory.CompanionTheory.Onto

variable {R : Type} [CommRing R]

abbrev prodCx {I : Type} (K : I → Cx.{w} R) : Cx.{w} R where
  X n := ∀ i, (K i).X n
  d n := LinearMap.pi fun i => ((K i).d n).comp (LinearMap.proj i)
  dd n x := funext fun i => (K i).dd n (x i)

def prodHom {I : Type} {K : I → Cx.{w} R} {L : I → Cx.{w'} R}
    (φ : ∀ i, Cx.Hom (K i) (L i) (RingHom.id R)) : Cx.Hom (prodCx K) (prodCx L) (RingHom.id R) where
  f n := LinearMap.pi fun i => ((φ i).f n).comp (LinearMap.proj i)
  comm n x := funext fun i => (φ i).comm n (x i)

theorem mem_B_prod {I : Type} (K : I → Cx.{w} R) (n : ℕ) (a : (prodCx K).X n) :
    a ∈ (prodCx K).B n ↔ ∀ i, a i ∈ (K i).B n := by
  cases n with
  | zero =>
    constructor
    · intro h i
      have h0 : a = 0 := h
      rw [h0]
      exact Submodule.zero_mem _
    · intro h
      exact funext fun i => h i
  | succ n =>
    constructor
    · rintro ⟨b, rfl⟩ i
      exact ⟨b i, rfl⟩
    · intro h
      choose b hb using h
      exact ⟨b, funext hb⟩

theorem prod_bij {I : Type} {K : I → Cx.{w} R} {L : I → Cx.{w'} R}
    (φ : ∀ i, Cx.Hom (K i) (L i) (RingHom.id R))
    (h : ∀ i n, Function.Bijective ((φ i).mapH n)) (n : ℕ) :
    Function.Bijective ((prodHom φ).mapH n) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨a, ha, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (prodCx K) n).1 x
    have hb : (prodCx L).d n ((prodHom φ).f n a) = 0 := by rw [(prodHom φ).comm, ha, map_zero]
    rw [CrystallineSemistableComparison.P.mapH_cls _ n a ha hb, (CrystallineSemistableComparison.P.cls_surj _ n).2.1 _ hb, mem_B_prod] at hx
    rw [(CrystallineSemistableComparison.P.cls_surj _ n).2.1, mem_B_prod]
    intro i
    have hai : (K i).d n (a i) = 0 := congrFun ha i
    have hbi : (L i).d n ((φ i).f n (a i)) = 0 := by rw [(φ i).comm, hai, map_zero]
    rw [← (CrystallineSemistableComparison.P.cls_surj _ n).2.1 _ hai]
    apply (injective_iff_map_eq_zero _).1 (h i n).1
    rw [CrystallineSemistableComparison.P.mapH_cls _ n _ hai hbi, (CrystallineSemistableComparison.P.cls_surj _ n).2.1]
    exact hx i
  · intro y
    obtain ⟨b, hb, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (prodCx L) n).1 y
    have hbi : ∀ i, (L i).d n (b i) = 0 := fun i => congrFun hb i
    have key : ∀ i, ∃ a, ∃ ha : (K i).d n a = 0, (φ i).f n a - b i ∈ (L i).B n := by
      intro i
      obtain ⟨x, hx⟩ := (h i n).2 ((L i).cls (b i) (hbi i))
      obtain ⟨a, ha, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (K i) n).1 x
      have hc : (L i).d n ((φ i).f n a) = 0 := by rw [(φ i).comm, ha, map_zero]
      rw [CrystallineSemistableComparison.P.mapH_cls _ n a ha hc] at hx
      exact ⟨a, ha, ((CrystallineSemistableComparison.P.cls_surj _ n).2.2.1 _ _ hc (hbi i)).1 hx⟩
    choose a ha hab using key
    have ha' : (prodCx K).d n a = 0 := funext ha
    have hc : (prodCx L).d n ((prodHom φ).f n a) = 0 := by rw [(prodHom φ).comm, ha', map_zero]
    refine ⟨(prodCx K).cls a ha', ?_⟩
    rw [CrystallineSemistableComparison.P.mapH_cls (prodHom φ) n a ha' hc, (CrystallineSemistableComparison.P.cls_surj _ n).2.2.1 _ _ hc hb, mem_B_prod]
    exact hab

variable {ι : Type} [DecidableEq ι]

abbrev cechCos (A : Sy.{w} R ι) : CosCx.{w} R where
  K p := prodCx fun i : Fin (p + 1) → ι => A.K (ent i)
  δ p k :=
    { f := fun q => (A.term q).cech.δ p k
      comm := fun q x => funext fun t => (A.res (ent_comp t k.succAbove)).comm q (x (t ∘ k.succAbove)) }
  rel p j i q x := (A.term q).cech.rel p j i x

def cechAug (A : Sy.{w} R ι) (hA : A.Desc) : DCx.AugRow (A.K ∅) (cechCos A).dcx where
  ε q := (A.term q).aug
  hε q x := (hA q).1 x
  comm q x := funext fun t => (A.res (Finset.empty_subset (ent t))).comm q x

theorem cechAug_row (A : Sy.{w} R ι) (hA : A.Desc) (q : ℕ) :
    ((cechCos A).dcx.row q).ResUpTo 1 ((cechAug A hA).ε q) := hA q

def cechHom {A B : Sy.{w} R ι} (m : A.Hom B) :
    DCx.Hom (cechCos A).dcx (cechCos B).dcx (RingHom.id R) where
  f p q := (prodHom fun i : Fin (p + 1) → ι => m.φ (ent i)).f q
  ch p q x := by

    rw [Cos.d_apply, Cos.d_apply, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_zsmul]
    refine congrArg _ (funext fun t => ?_)
    exact (m.nat (ent_comp t k.succAbove) q (x (t ∘ k.succAbove))).symm
  cv p q x := (prodHom fun i : Fin (p + 1) → ι => m.φ (ent i)).comm q x

theorem cechHom_col {A B : Sy.{w} R ι} (m : A.Hom B)
    (h : ∀ S : Finset ι, S.Nonempty → ∀ n, Function.Bijective ((m.φ S).mapH n)) (p q : ℕ) :
    Function.Bijective (((cechHom m).col p).mapH q) :=
  prod_bij (fun i : Fin (p + 1) → ι => m.φ (ent i))
    (fun i n => h _ ⟨i 0, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩ n) q

theorem upTo_one {M : Type w} {N : Type w'} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    (f : M →ₗ[R] N) : UpTo (1 : R) f ↔ Function.Bijective f := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨(injective_iff_map_eq_zero f).2 fun x hx => ?_, fun y => ?_⟩
    · simpa using h1 x hx
    · simpa using h2 y
  · intro h
    refine ⟨fun x hx => ?_, fun y => ?_⟩
    · rw [one_smul]
      exact (injective_iff_map_eq_zero f).1 h.1 x hx
    · simpa using h.2 y

theorem cls_congr {K : Cx.{w} R} {n : ℕ} {a b : K.X n} (h : a = b) (ha : K.d n a = 0) (hb : K.d n b = 0) :
    K.cls a ha = K.cls b hb := by
  subst h; rfl

theorem edge_square {A B : Sy.{w} R ι} (m : A.Hom B) (hA : A.Desc) (hB : B.Desc) (n : ℕ) (a : (A.K ∅).X n) :
    (cechHom m).tot.f n ((cechAug A hA).edge.f n a) = (cechAug B hB).edge.f n ((m.φ ∅).f n a) := by
  apply Subtype.ext
  funext p q
  by_cases h : p = 0 ∧ q = n
  · obtain ⟨rfl, rfl⟩ := h
    change (cechHom m).f 0 q ((cechCos A).dcx.sgl 0 q ((cechAug A hA).ε q a) 0 q) =
      (cechCos B).dcx.sgl 0 q ((cechAug B hB).ε q ((m.φ ∅).f q a)) 0 q
    rw [DCx.sgl_self, DCx.sgl_self]
    funext t
    exact m.nat (Finset.empty_subset (ent t)) q a
  · have h' : p ≠ 0 ∨ q ≠ n := by omega
    change (cechHom m).f p q ((cechCos A).dcx.sgl 0 n ((cechAug A hA).ε n a) p q) =
      (cechCos B).dcx.sgl 0 n ((cechAug B hB).ε n ((m.φ ∅).f n a)) p q
    rw [DCx.sgl_ne _ _ h', DCx.sgl_ne _ _ h', map_zero]

theorem mapH_empty_bij {A B : Sy.{w} R ι} (m : A.Hom B) (hA : A.Desc) (hB : B.Desc)
    (h : ∀ S : Finset ι, S.Nonempty → ∀ n, Function.Bijective ((m.φ S).mapH n)) (n : ℕ) :
    Function.Bijective ((m.φ ∅).mapH n) := by
  have eA : Function.Bijective ((cechAug A hA).edge.mapH n) := by
    have := CrystallineSemistableComparison.P.dc_row (cechAug A hA) 1 (cechAug_row A hA) n
    rw [one_pow] at this
    exact (upTo_one _).1 this
  have eB : Function.Bijective ((cechAug B hB).edge.mapH n) := by
    have := CrystallineSemistableComparison.P.dc_row (cechAug B hB) 1 (cechAug_row B hB) n
    rw [one_pow] at this
    exact (upTo_one _).1 this
  have eT : Function.Bijective ((cechHom m).tot.mapH n) := by
    have := CrystallineSemistableComparison.P.dc_map_col (cechHom m) 1 n fun p q _ => (upTo_one _).2 (cechHom_col m h p q)
    rw [one_pow] at this
    exact (upTo_one _).1 this
  have sq : ∀ x, (cechAug B hB).edge.mapH n ((m.φ ∅).mapH n x) =
      (cechHom m).tot.mapH n ((cechAug A hA).edge.mapH n x) := by
    intro x
    obtain ⟨a, ha, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (A.K ∅) n).1 x
    have c1 : (B.K ∅).d n ((m.φ ∅).f n a) = 0 := by rw [(m.φ ∅).comm, ha, map_zero]
    have c2 : (cechCos B).dcx.tot.d n ((cechAug B hB).edge.f n ((m.φ ∅).f n a)) = 0 := by
      rw [(cechAug B hB).edge.comm, c1, map_zero]
    have c3 : (cechCos A).dcx.tot.d n ((cechAug A hA).edge.f n a) = 0 := by
      rw [(cechAug A hA).edge.comm, ha, map_zero]
    have c4 : (cechCos B).dcx.tot.d n ((cechHom m).tot.f n ((cechAug A hA).edge.f n a)) = 0 := by
      rw [(cechHom m).tot.comm, c3, map_zero]
    rw [CrystallineSemistableComparison.P.mapH_cls (m.φ ∅) n a ha c1, CrystallineSemistableComparison.P.mapH_cls (cechAug B hB).edge n _ c1 c2,
      CrystallineSemistableComparison.P.mapH_cls (cechAug A hA).edge n a ha c3, CrystallineSemistableComparison.P.mapH_cls (cechHom m).tot n _ c3 c4]
    exact cls_congr (edge_square m hA hB n a).symm c2 c4
  constructor
  · intro x y hxy
    apply eA.1
    apply eT.1
    rw [← sq, ← sq, hxy]
  · intro y
    obtain ⟨u, hu⟩ := eT.2 ((cechAug B hB).edge.mapH n y)
    obtain ⟨x, rfl⟩ := eA.2 u
    refine ⟨x, eB.1 ?_⟩
    rw [sq, hu]

theorem mvBij : CrystallineSemistableComparison.Onto.MVBij := fun _ _ _ _ _ _ m hA hB h n => mapH_empty_bij m hA hB h n

end GlobalTheory.CompanionTheory.Onto
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.SpreadingModels

namespace GlobalTheory.CompanionTheory.CubeModels

theorem model_refine {R R₀ R₁ : Type} [CommRing R] [CommRing R₀] [CommRing R₁] {φ : R₀ →+* R}
    {ψ : R₀ →+* R₁} {φ₁ : R₁ →+* R} (e : φ₁.comp ψ = φ) (ft : Algebra.FiniteType ℤ R₁)
    {Y Y₀ : Scheme.{0}} {f : Y ⟶ Spec (CommRingCat.of R)} {f₀ : Y₀ ⟶ Spec (CommRingCat.of R₀)}
    {π : Y ⟶ Y₀} (hm : IsModel φ f f₀ π)
    (ρ : Y ⟶ pullback f₀ (Spec.map (CommRingCat.ofHom ψ)))
    (h₁ : ρ ≫ pullback.fst _ _ = π)
    (h₂ : ρ ≫ pullback.snd _ _ = f ≫ Spec.map (CommRingCat.ofHom φ₁)) :
    IsModel φ₁ f (pullback.snd f₀ (Spec.map (CommRingCat.ofHom ψ))) ρ := by
  obtain ⟨-, l, q, s, sq⟩ := hm
  have hc : Spec.map (CommRingCat.ofHom φ) =
      Spec.map (CommRingCat.ofHom φ₁) ≫ Spec.map (CommRingCat.ofHom ψ) := by
    subst e
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
  refine ⟨ft, inferInstance, inferInstance, inferInstance, ?_⟩
  refine IsPullback.of_right (h₁₂ := pullback.fst f₀ (Spec.map (CommRingCat.ofHom ψ)))
    (v₁₃ := f₀) (h₂₂ := Spec.map (CommRingCat.ofHom ψ)) ?_ h₂ (IsPullback.of_hasPullback _ _)
  rw [h₁, ← hc]
  exact sq

def refineMap {R R₀ R₁ : Type} [CommRing R] [CommRing R₀] [CommRing R₁] {φ : R₀ →+* R}
    {ψ : R₀ →+* R₁} {φ₁ : R₁ →+* R} (e : φ₁.comp ψ = φ)
    {Y Y₀ : Scheme.{0}} {f : Y ⟶ Spec (CommRingCat.of R)} {f₀ : Y₀ ⟶ Spec (CommRingCat.of R₀)}
    {π : Y ⟶ Y₀} (hm : IsModel φ f f₀ π) :
    Y ⟶ pullback f₀ (Spec.map (CommRingCat.ofHom ψ)) :=
  pullback.lift π (f ≫ Spec.map (CommRingCat.ofHom φ₁)) (by
    have hc : Spec.map (CommRingCat.ofHom φ) =
        Spec.map (CommRingCat.ofHom φ₁) ≫ Spec.map (CommRingCat.ofHom ψ) := by
      subst e
      rw [CommRingCat.ofHom_comp, Spec.map_comp]
    rw [Category.assoc, ← hc]
    exact hm.2.2.2.2.w)

theorem model_refine' {R R₀ R₁ : Type} [CommRing R] [CommRing R₀] [CommRing R₁] {φ : R₀ →+* R}
    {ψ : R₀ →+* R₁} {φ₁ : R₁ →+* R} (e : φ₁.comp ψ = φ) (ft : Algebra.FiniteType ℤ R₁)
    {Y Y₀ : Scheme.{0}} {f : Y ⟶ Spec (CommRingCat.of R)} {f₀ : Y₀ ⟶ Spec (CommRingCat.of R₀)}
    {π : Y ⟶ Y₀} (hm : IsModel φ f f₀ π) :
    IsModel φ₁ f (pullback.snd f₀ (Spec.map (CommRingCat.ofHom ψ))) (refineMap e hm) :=
  model_refine e ft hm _ (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)

theorem hasModel_of_spreads : GlobalTheory.SpreadingModels.SchemeModels → GlobalTheory.SpreadingModels.Spreads (fun _ _ f => Smooth f) →
    GlobalTheory.SpreadingModels.Spreads (fun _ _ f => IsProper f) → GlobalTheory.SpreadingModels.LBSpreads →
    ∀ (R : Type) [CommRing R] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of R)), Smooth f → IsProper f →
      ∀ M : LB Y, M.IsLB → GlobalTheory.SpreadingModels.HasModel f M := by
  intro hS hSm hPr hLB R _ Y f hsm hpr M hM
  obtain ⟨R₀, _, φ, Y₀, f₀, π, hm⟩ := hS R Y f inferInstance inferInstance inferInstance
  obtain ⟨R₁, _, ψ₁, φ₁, e₁, ft₁, sm₁⟩ := hSm R R₀ φ Y Y₀ f f₀ π hm hsm
  have m₁ := model_refine' e₁ ft₁ hm
  obtain ⟨R₂, _, ψ₂, φ₂, e₂, ft₂, pr₂⟩ := hPr R R₁ φ₁ Y _ f _ _ m₁ hpr
  have m₂ := model_refine' e₂ ft₂ m₁
  obtain ⟨R₃, _, ψ₃, φ₃, ρ, e₃, ft₃, r₁, r₂, M₃, hM₃, w, hw⟩ := hLB R R₂ φ₂ Y _ f _ _ m₂ M hM
  have m₃ := model_refine e₃ ft₃ m₂ ρ r₁ r₂
  have sm₁' : Smooth (pullback.snd f₀ (Spec.map (CommRingCat.ofHom ψ₁))) := sm₁
  have pr₂' : IsProper (pullback.snd (pullback.snd f₀ (Spec.map (CommRingCat.ofHom ψ₁)))
      (Spec.map (CommRingCat.ofHom ψ₂))) := pr₂
  refine ⟨R₃, inferInstance, Algebra.FiniteType.isNoetherianRing ℤ R₃, φ₃, _,
    pullback.snd (pullback.snd (pullback.snd f₀ (Spec.map (CommRingCat.ofHom ψ₁)))
      (Spec.map (CommRingCat.ofHom ψ₂))) (Spec.map (CommRingCat.ofHom ψ₃)), ρ,
    inferInstance, inferInstance, m₃.2.2.2.2, M₃, hM₃, w, hw⟩

end GlobalTheory.CompanionTheory.CubeModels
end
end

section

open GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.BZMir.Fun

theorem _root_.GlobalTheory.T.smooth_psi_minus : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.BZMir.Fun.SmPsiMinus k := by
  first | exact @GlobalTheory.CompanionTheory.BZMirFun.smPsiMinus | exact GlobalTheory.CompanionTheory.BZMirFun.smPsiMinus | (intros; apply GlobalTheory.CompanionTheory.BZMirFun.smPsiMinus <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.BZMir.Fun

theorem _root_.GlobalTheory.T.theta_open_mirabolic : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.BZMir.Fun.ThetaOpen k := by
  first | exact @GlobalTheory.CompanionTheory.BZFun.thetaOpen | exact GlobalTheory.CompanionTheory.BZFun.thetaOpen | (intros; apply GlobalTheory.CompanionTheory.BZFun.thetaOpen <;> assumption)
end
