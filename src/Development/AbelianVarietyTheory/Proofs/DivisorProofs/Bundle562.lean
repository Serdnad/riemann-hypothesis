module

public import Development.AbelianVarietyTheory.Definitions.Divisors.KerIdealCompOfSurjective
public import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImageCochainExists
public import Development.AbelianVarietyTheory.Definitions.Divisors.RatBasisLinearIndependentInt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle508
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle533
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle404
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle509
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle510
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle511
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
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle005
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
import Mathlib.RingTheory.MvPowerSeries.Basic

@[expose] public section

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open TensorProduct

namespace GlobalTheory.CotDualLin

theorem dvd_counit (O A : Type) [CommRing O] [CommRing A] [HopfAlgebra O A] [Module.Finite O A]
    [Module.Projective O A] (a : A) (q : O) (t : A ⊗[O] A)
    (h : Coalgebra.comul (R := O) a = a ⊗ₜ[O] (1 : A) + (1 : A) ⊗ₜ[O] a + q • t) :
    q ∣ Coalgebra.counit (R := O) a := by
  have h1 := CartierDual.mul_apply (R := O) (C := A) 1 1 a
  rw [one_mul, h] at h1
  simp only [map_add (f := _), map_smul, CartierDual.pair_tmul_tmul, CartierDual.one_apply, Bialgebra.counit_one] at h1
  exact ⟨-(CartierDual.pair O A A (1 ⊗ₜ 1) t), by rw [smul_eq_mul] at h1; linear_combination -h1⟩

theorem dvd_of_mem_sq (O A : Type) [CommRing O] [CommRing A] [HopfAlgebra O A] [Coalgebra.IsCocomm O A] [Module.Finite O A]
    [Module.Projective O A] (a : A) (q : O) (t : A ⊗[O] A)
    (h : Coalgebra.comul (R := O) a = a ⊗ₜ[O] (1 : A) + (1 : A) ⊗ₜ[O] a + q • t)
    (χ : CartierDual O A) (hχ : χ ∈ RingHom.ker (Bialgebra.counitAlgHom O (CartierDual O A)) ^ 2) :
    q ∣ χ a := by
  rw [pow_two] at hχ
  refine Submodule.mul_induction_on hχ (fun x hx y hy => ?_) (fun x y hx hy => ?_)
  · have hx1 : x 1 = 0 := hx
    have hy1 : y 1 = 0 := hy
    rw [CartierDual.mul_apply, h]
    simp only [map_add (f := _), map_smul, CartierDual.pair_tmul_tmul, hx1, hy1, mul_zero, zero_mul, zero_add, smul_eq_mul]
    exact dvd_mul_right _ _
  · have e : (x + y) a = x a + y a := rfl
    rw [e]; exact dvd_add hx hy

theorem dvd_sub_of_dUnit_eq : ∀ (O A : Type) [CommRing O] [CommRing A] [HopfAlgebra O A] [Coalgebra.IsCocomm O A]
    [Module.Finite O A] [Module.Projective O A] (a : A) (q : O) (t : A ⊗[O] A),
    Coalgebra.comul (R := O) a = a ⊗ₜ[O] (1 : A) + (1 : A) ⊗ₜ[O] a + q • t →
    ∀ φ ψ : CartierDual O A, PDiv.dUnit (R := O) φ = PDiv.dUnit (R := O) ψ → q ∣ φ a - ψ a := by
  intro O A _ _ _ _ _ _ a q t h φ ψ hd
  have h0 : PDiv.dUnit (R := O) (φ - ψ) = 0 := by rw [PDiv.dUnit, map_sub]; exact sub_eq_zero.2 hd
  rw [PDiv.dUnit, AugCot.d_eq_zero_iff] at h0
  have h2 := dvd_of_mem_sq O A a q t h _ h0
  set c := Bialgebra.counitAlgHom O (CartierDual O A) (φ - ψ)
  have h3 : (algebraMap O (CartierDual O A) c) a = c * Coalgebra.counit (R := O) a := by
    rw [Algebra.algebraMap_eq_smul_one]; rfl
  have e : (φ - ψ - algebraMap O (CartierDual O A) c) a = φ a - ψ a - (algebraMap O (CartierDual O A) c) a := rfl
  rw [e, h3] at h2
  have h4 := dvd_mul_of_dvd_right (dvd_counit O A a q t h) c
  have := dvd_add h2 h4
  rwa [sub_add_cancel] at this

end GlobalTheory.CotDualLin
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Obs

theorem smul_mem_map_eq_zero {R B : Type} [CommRing R] [CommRing B] [Algebra R B] {I : Ideal R} (hI : I ^ 2 = 0)
    {i : R} (hi : i ∈ I) {x : B} (hx : x ∈ I.map (algebraMap R B)) : i • x = 0 := by
  rw [Algebra.smul_def]
  have h : algebraMap R B i * x ∈ I.map (algebraMap R B) * I.map (algebraMap R B) :=
    Ideal.mul_mem_mul (Ideal.mem_map_of_mem _ hi) hx
  rw [← Ideal.map_mul, ← pow_two, hI, Ideal.zero_eq_bot, Ideal.map_bot] at h
  simpa using h

theorem exists_isSig : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (B B₀ : Type) [CommRing B] [Algebra R B] [CommRing B₀] [Algebra R₀ B₀] (p : B →+* B₀) (hs : SemiHom π p) (hp : Function.Surjective p) (hker : ∀ b, p b = 0 ↔ b ∈ I.map (algebraMap R B)), ∃ σ : R₁ ⊗[R₀] B₀ →+ B, α.IsSig p σ := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α B B₀ _ _ _ _ p hs hp hker
  have key : ∀ (y : R₁) (b b' : B), p b = p b' → α.k y • b = α.k y • b' := by
    intro y b b' h
    have hm : b - b' ∈ I.map (algebraMap R B) := (hker _).1 (by rw [map_sub, h, sub_self])
    have := smul_mem_map_eq_zero hI (α.mem y) hm
    rwa [smul_sub, sub_eq_zero] at this
  let s : B₀ → B := Function.surjInv hp
  have hs' : ∀ b₀, p (s b₀) = b₀ := Function.surjInv_eq hp
  let f : R₁ →+ B₀ →+ B := AddMonoidHom.mk' (fun y ↦ AddMonoidHom.mk' (fun b₀ ↦ α.k y • s b₀) (by
      intro b₀ b₀'
      rw [← smul_add]
      exact key y _ _ (by rw [map_add (f := _), hs', hs', hs'])))
    (by
      intro y y'
      ext b₀
      simp [add_smul])
  refine ⟨TensorProduct.liftAddHom f ?_, ?_⟩
  · intro r₀ y b₀
    obtain ⟨r, rfl⟩ := hπ r₀
    change α.k (π r • y) • s b₀ = α.k y • s (π r • b₀)
    rw [α.smul, mul_comm, mul_smul]
    exact key y _ _ (by rw [hs, hs', hs'])
  · intro y b
    change α.k y • s (p b) = α.k y • b
    exact key y _ _ (hs' _)

end GlobalTheory.Obs
end
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Obs

section Chart

variable {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} {π : R →+* R₀}

theorem chart_spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (a : A →+* B) (b : B →+* C) :
    spMap (b.comp a) = spMap b ≫ spMap a := by
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem chart_spMap_inj {A B : Type} [CommRing A] [CommRing B] {a b : A →+* B} (e : spMap a = spMap b) : a = b := by
  have := Spec.map_injective e
  exact congrArg CommRingCat.Hom.hom this

variable (hI : I ^ 2 = 0) {X₀ Z₀ X Z : Scheme.{0}} {s₀ : X₀ ⟶ Sp R₀} {t₀ : Z₀ ⟶ Sp R₀} {s : X ⟶ Sp R}
  {t : Z ⟶ Sp R} {i : X₀ ⟶ X} {k : Z₀ ⟶ Z} {S : Sys I π s₀} {S' : Sys I π t₀} (P : S.Presents s i)
  (P' : S'.Presents t k) {f₀ : Z₀ ⟶ X₀} {f : Z ⟶ X} (hkf : k ≫ f = f₀ ≫ i)


include hkf in
theorem chart_red (p : Pair f₀) :
    spMap (S'.p (Opposite.op p.1.1)) ≫ P'.y (Opposite.op p.1.1) ≫ f =
      spMap (GlobalTheory.CechDR.secPull s₀ t₀ p) ≫ spMap (S.p (Opposite.op p.1.2)) ≫ P.y (Opposite.op p.1.2) := by
  rw [← Category.assoc, P'.red, P.red, Category.assoc, hkf, ← Category.assoc, ← Category.assoc,
    ← GlobalTheory.CechDR.secPull_affPt s₀ t₀ p, Category.assoc]


include hI hkf in
theorem chart_range (p : Pair f₀) :
    Set.range ⇑(P'.y (Opposite.op p.1.1) ≫ f) ⊆ Set.range ⇑(P.y (Opposite.op p.1.2)) := by
  rintro _ ⟨q, rfl⟩
  obtain ⟨q₀, rfl⟩ := (S'.surjective_spMap_p hI (Opposite.op p.1.1)).surj q
  have e := congrArg (fun g ↦ g q₀) (chart_red P P' hkf p)
  simp only [Scheme.Hom.comp_apply] at e
  rw [Scheme.Hom.comp_apply, e]
  exact ⟨_, rfl⟩

def chartMor (p : Pair f₀) : Sp (S'.F.obj (Opposite.op p.1.1)) ⟶ Sp (S.F.obj (Opposite.op p.1.2)) :=
  haveI := P.isOpen (Opposite.op p.1.2)
  IsOpenImmersion.lift _ _ (chart_range hI P P' hkf p)

theorem chartMor_fac (p : Pair f₀) :
    chartMor hI P P' hkf p ≫ P.y (Opposite.op p.1.2) = P'.y (Opposite.op p.1.1) ≫ f :=
  haveI := P.isOpen (Opposite.op p.1.2)
  IsOpenImmersion.lift_fac _ _ _

def chartRing (p : Pair f₀) : S.F.obj (Opposite.op p.1.2) →+* S'.F.obj (Opposite.op p.1.1) :=
  (Spec.preimage (chartMor hI P P' hkf p)).hom

theorem spMap_chartRing (p : Pair f₀) : spMap (chartRing hI P P' hkf p) = chartMor hI P P' hkf p := by
  simp only [spMap, chartRing, CommRingCat.ofHom_hom]
  exact Spec.map_preimage _

theorem chart_ext {A : Type} [CommRing A] (U : AffOp X₀) {a b : S.F.obj U →+* A}
    (e : spMap a ≫ P.y U = spMap b ≫ P.y U) : a = b :=
  haveI := P.isOpen U
  chart_spMap_inj ((cancel_mono (P.y U)).1 e)

include hkf in
theorem chartRing_fac (p : Pair f₀) :
    spMap (chartRing hI P P' hkf p) ≫ P.y (Opposite.op p.1.2) = P'.y (Opposite.op p.1.1) ≫ f := by
  rw [spMap_chartRing, chartMor_fac]


include hkf in
theorem chartRing_comp_algebraMap (hf : f ≫ s = t) (p : Pair f₀) :
    (chartRing hI P P' hkf p).comp (algebraMap R (S.F.obj (Opposite.op p.1.2))) =
      algebraMap R (S'.F.obj (Opposite.op p.1.1)) := by
  refine chart_spMap_inj ?_
  rw [chart_spMap_comp, ← P.base, ← Category.assoc, chartRing_fac, Category.assoc, hf, P'.base]

def chartAlg (hf : f ≫ s = t) (p : Pair f₀) : S.F.obj (Opposite.op p.1.2) →ₐ[R] S'.F.obj (Opposite.op p.1.1) :=
  { chartRing hI P P' hkf p with
    commutes' := fun r ↦ congrArg (fun g ↦ g r) (chartRing_comp_algebraMap hI P P' hkf hf p) }


include hkf in
theorem chartRing_red (p : Pair f₀) :
    (S'.p (Opposite.op p.1.1)).comp (chartRing hI P P' hkf p) =
      (GlobalTheory.CechDR.secPull s₀ t₀ p).comp (S.p (Opposite.op p.1.2)) := by
  refine chart_ext P _ ?_
  rw [chart_spMap_comp, chart_spMap_comp, Category.assoc, Category.assoc, chartRing_fac, chart_red P P' hkf p]


include hkf in
theorem chartRing_nat {p q : Pair f₀} (a : q ≤ p) (b : S.F.obj (Opposite.op p.1.2)) :
    mp S'.F (homOfLE (Pair.le_fst a)).op (chartRing hI P P' hkf p b) =
      chartRing hI P P' hkf q (mp S.F (homOfLE (Pair.le_snd a)).op b) := by
  have e : ((mp S'.F (homOfLE (Pair.le_fst a)).op : _ →+* _)).comp (chartRing hI P P' hkf p) =
      (chartRing hI P P' hkf q).comp (mp S.F (homOfLE (Pair.le_snd a)).op : _ →+* _) := by
    refine chart_ext P _ ?_
    rw [chart_spMap_comp, chart_spMap_comp, Category.assoc, Category.assoc, chartRing_fac, P.nat,
      chartRing_fac, ← Category.assoc, P'.nat]
  exact congrArg (fun g ↦ g b) e

end Chart

end GlobalTheory.Obs

namespace GlobalTheory.Obs

theorem exists_chart_lifts : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ Z₀ X Z : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (t₀ : Z₀ ⟶ Sp R₀) (s : X ⟶ Sp R) (t : Z ⟶ Sp R) (i : X₀ ⟶ X) (k : Z₀ ⟶ Z) (hi : IsPullback i s₀ s (spMap π)) (hkk : IsPullback k t₀ t (spMap π)) (S : Sys I π s₀) (S' : Sys I π t₀) (P : S.Presents s i) (P' : S'.Presents t k) (f₀ : Z₀ ⟶ X₀) (h : f₀ ≫ s₀ = t₀ ≫ spMap (RingHom.id R₀)) (f : Z ⟶ X), f ≫ s = t → k ≫ f = f₀ ≫ i → ∃ (l : ∀ T : (Pair f₀)ᵒᵖ, (ofSys S).B ((pairPull h).G.obj T) →ₐ[R] (pairPre S' f₀).B T), (ofSys S).IsLift (pairPre S' f₀) (pairPull h) l ∧ (ofSys S).IsNat (pairPre S' f₀) (pairPull h) l := by
  intro R R₀ _ _ I hI π _ _ X₀ Z₀ X Z s₀ t₀ s t i k _ _ S S' P P' f₀ h f hf hkf
  refine ⟨fun T ↦ chartAlg hI P P' hkf hf T.unop, fun T b ↦ ?_, fun T T' a b ↦ ?_⟩
  · exact congrArg (fun g ↦ g b) (chartRing_red hI P P' hkf T.unop)
  · exact chartRing_nat hI P P' hkf (leOfHom a.unop) b

end GlobalTheory.Obs
end
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Obs

theorem isTheta_eq {R R₀ B B₀ B' : Type} [CommRing R] [CommRing R₀] [CommRing B] [Algebra R B] [CommRing B₀]
    [Algebra R₀ B₀] [CommRing B'] [Algebra R B'] {I : Ideal R} {p : B →+* B₀} (hp : Function.Surjective p)
    {α β : B →ₐ[R] B'} {θ₁ θ₂ : Ω[B₀⁄R₀] →+ B'} (h₁ : IsTheta I p α β θ₁) (h₂ : IsTheta I p α β θ₂) :
    θ₁ = θ₂ := by
  ext w
  have hw : w ∈ Submodule.span B₀ (Set.range (D R₀ B₀)) := by
    rw [span_range_derivation]; trivial
  refine Submodule.span_induction (p := fun z _ ↦ θ₁ z = θ₂ z) ?_ ?_ ?_ ?_ hw
  · rintro z ⟨y, rfl⟩
    obtain ⟨b, rfl⟩ := hp y
    rw [h₁.der, h₂.der]
  · rw [map_zero, map_zero]
  · intro y z _ _ hy hz; rw [map_add (f := _), map_add (f := _), hy, hz]
  · intro c z _ hz
    obtain ⟨b, rfl⟩ := hp c
    rw [h₁.smul, h₂.smul, hz]

theorem isSig_eq {R R₀ R₁ : Type} [CommRing R] [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁] {I : Ideal R}
    {π : R →+* R₀} (α : Aug I π R₁) {B B₀ : Type} [CommRing B] [Algebra R B] [CommRing B₀] [Algebra R₀ B₀]
    {p : B →+* B₀} (hp : Function.Surjective p) {σ σ' : R₁ ⊗[R₀] B₀ →+ B} (h : α.IsSig p σ) (h' : α.IsSig p σ') :
    σ = σ' := by
  ext x
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul y x =>
    obtain ⟨b, rfl⟩ := hp x
    rw [h, h']
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

theorem isOb2_add : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R₀) (L : Pre I π F) (w w' : Glob1 F) (c c' : GlobalTheory.CatCoh.H2 (ext R₁ F)), L.IsOb2 α w c → L.IsOb2 α w' c' → L.IsOb2 α (w + w') (c + c') := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α C _ F L w w' c c' h h'
  obtain ⟨θ, σ, z, hθ, hσ, rfl, hz⟩ := h
  obtain ⟨θ', σ', z', hθ', hσ', rfl, hz'⟩ := h'
  refine ⟨θ, σ, z + z', hθ, hσ, (map_add _ _ _).symm, fun T T' T'' a b ↦ ?_⟩
  have eθ : θ T T' T'' a b = θ' T T' T'' a b := isTheta_eq (L.surj T) (hθ T T' T'' a b) (hθ' T T' T'' a b)
  have eσ : σ T'' = σ' T'' := isSig_eq α (L.surj T'') (hσ T'') (hσ' T'')
  obtain ⟨k₁, s₁⟩ := hz T T' T'' a b
  obtain ⟨k₂, s₂⟩ := hz' T T' T'' a b
  have ez : (z + z').1 T T' T'' a b = z.1 T T' T'' a b + z'.1 T T' T'' a b := rfl
  refine ⟨?_, ?_⟩
  · unfold Aug.KerQ at k₁ k₂ ⊢
    rw [ez, map_add (f := _), k₁, k₂, add_zero]
  · rw [ez, map_add (f := _), s₁, eσ, s₂, ← eθ]
    exact (map_add (θ T T' T'' a b) (w.1 T) (w'.1 T)).symm

end GlobalTheory.Obs
end
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Obs

theorem rho_id_eq {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} (hI : I ^ 2 = 0) {π : R →+* R₀}
    {C : Type} [Category.{0} C] {F : C ⥤ CommAlgCat.{0} R₀} (L : Pre I π F) (hL : L.IsFun) (T : C) (y : L.B T) :
    L.ρ (𝟙 T) y = y := by
  set e := L.ρ (𝟙 T) with he
  have idem : ∀ x, e (e x) = e x := fun x ↦ by
    have := hL (𝟙 T) (𝟙 T) x
    rw [Category.comp_id] at this
    exact this.symm
  have hJ := LiftSys.map_sq hI (L.B T)
  have memJ : ∀ x, x - e x ∈ I.map (algebraMap R (L.B T)) := fun x ↦ by
    rw [← L.ker]
    rw [map_sub, L.nat, mp_id, sub_self]
  have sq0 : ∀ u v, u ∈ I.map (algebraMap R (L.B T)) → v ∈ I.map (algebraMap R (L.B T)) → u * v = 0 := by
    intro u v hu hv
    have : u * v ∈ I.map (algebraMap R (L.B T)) ^ 2 := by
      rw [pow_two]; exact Ideal.mul_mem_mul hu hv
    rw [hJ] at this
    simpa using this
  have fix : ∀ z ∈ I.map (algebraMap R (L.B T)), e z = z := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, -, rfl⟩ := hx
      exact e.commutes i
    | zero => exact map_zero e
    | add x w _ _ hx hw => rw [map_add (f := _), hx, hw]
    | smul b x hxm hx =>
      rw [smul_eq_mul, map_mul, hx]
      have := sq0 _ _ (memJ b) hxm
      rw [sub_mul] at this
      exact (sub_eq_zero.1 this).symm
  have h1 := fix _ (memJ y)
  rw [map_sub, idem, sub_self] at h1
  exact (sub_eq_zero.1 h1.symm).symm

theorem nonempty_sys_of_isFun : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (L : Pre I π (OAff s₀)), L.IsFun → Nonempty (Sys I π s₀) := by
  intro R R₀ _ _ I hI π _ _ X₀ s₀ L hL
  exact ⟨{
    F := {
      obj := L.B
      map := fun a ↦ CommAlgCat.ofHom (L.ρ a)
      map_id := fun T ↦ CommAlgCat.hom_ext (AlgHom.ext fun y ↦ rho_id_eq hI L hL T y)
      map_comp := fun a b ↦ CommAlgCat.hom_ext (AlgHom.ext fun x ↦ hL a b x) }
    p := L.p
    semi := L.semi
    nat := fun a b ↦ L.nat a b
    surj := L.surj
    ker := L.ker
    smooth := L.smooth }⟩

end GlobalTheory.Obs
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem isAW_existsUnique_biadditive (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) {E : Spc}
    {n m k : ℤ} (hk : n + m = k) :
    (∀ (α : Cochain ((chains R).obj E) I n) (β : Cochain ((chains R).obj E) J m), ∃! γ, μ.IsAW hk α β γ) ∧
    (∀ α α' β γ γ', μ.IsAW (E := E) hk α β γ → μ.IsAW hk α' β γ' → μ.IsAW hk (α + α') β (γ + γ')) ∧
    (∀ α β β' γ γ', μ.IsAW (E := E) hk α β γ → μ.IsAW hk α β' γ' → μ.IsAW hk α (β + β') (γ + γ')) := by
  refine ⟨fun α β => ?_, fun α α' β γ γ' h h' => CupSpec.isAW_add_left μ hk h h',
    fun α β β' γ γ' h h' => CupSpec.isAW_add_right μ hk h h'⟩
  obtain ⟨γ, hγ⟩ := CupSpec.isAW_exists μ hk α β
  exact ⟨γ, hγ, fun γ' h' => CupSpec.isAW_unique μ hk h' hγ⟩

end GlobalTheory.EtC
end

section

set_option autoImplicit false

open DividedPowers GlobalTheory.Cris GlobalTheory.PDA

namespace GlobalTheory.PDA

theorem PDPoly.exists_isStd : ∀ (B : Type) [CommRing B] (J : Ideal B) (δ : DividedPowers J) (Q : PDPoly B),
    ∃ η : DividedPowers (Q.ext J), Q.IsStd δ η := by
  intro B _ J δ Q
  obtain ⟨η, hη⟩ := GlobalTheory.T.exists_dividedPowers_dividedPowerPolyAlgebra_augIdeal B Q
  obtain ⟨ε, hε⟩ := (GlobalTheory.T.exists_lift_and_augmentation_map B Q).2
  obtain ⟨θ, hθ, hθη⟩ := GlobalTheory.T.exists_dividedPowers_split_augmentation_extension B J δ Q.P ε Q.aug η hε
  refine ⟨θ, ⟨hθ, fun n ↦ ?_⟩⟩
  rw [hθη n _ (Q.e_succ_mem_aug 0), hη]

end GlobalTheory.PDA
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.freeEtaleSheaf_section_locally_finite_combination : ∀ (R : Type) [CommRing R] (P : PSh) (U : Scheme.{0}), (∀ y : Sec ((free R).obj P) U, Loc U fun V g => ∃ c : P.obj (op V) →₀ ULift.{1} R, Sec.res g y = c.sum fun x r => r • freeGen R P V x) ∧ ∀ c : P.obj (op U) →₀ ULift.{1} R, (c.sum fun x r => r • freeGen R P U x) = 0 → Loc U fun _ g => Finsupp.mapDomain (P.map g.op) c = 0 := by
  first | (exact @GlobalTheory.EtC.free_sec_loc) | (exact GlobalTheory.EtC.free_sec_loc) | (intros; apply GlobalTheory.EtC.free_sec_loc  <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.sectionwiseTensor_presheaf_locallyBijective : ∀ (R : Type) [CommRing R] (C P Q : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) (φ : P ⟶ Q), (∀ (U : Scheme.{0}) (y : Q.obj (op U)), Loc U fun V g => ∃ x, (φ.app (op V)).hom x = (Q.map g.op).hom y) → (∀ (U : Scheme.{0}) (x : P.obj (op U)), (φ.app (op U)).hom x = 0 → Loc U fun _ g => (P.map g.op).hom x = 0) → ∀ U : Scheme.{0}, (∀ y : TensorProduct (ULift.{1} R) (C.obj (op U)) (Q.obj (op U)), Loc U fun V g => ∃ x, LinearMap.lTensor _ (φ.app (op V)).hom x = TensorProduct.map (C.map g.op).hom (Q.map g.op).hom y) ∧ ∀ x : TensorProduct (ULift.{1} R) (C.obj (op U)) (P.obj (op U)), LinearMap.lTensor _ (φ.app (op U)).hom x = 0 → Loc U fun _ g => TensorProduct.map (C.map g.op).hom (P.map g.op).hom x = 0 := by
  first | (exact @GlobalTheory.EtC.tensor_loc_bij) | (exact GlobalTheory.EtC.tensor_loc_bij) | (intros; apply GlobalTheory.EtC.tensor_loc_bij  <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.tateTwistSheaf_isLocallyFlat : ∀ (q : ℕ) [NeZero q] (i : ℤ), FlatS (tw q i) := by
  first | (exact @GlobalTheory.EtC.flatS_tw) | (exact GlobalTheory.EtC.flatS_tw) | (intros; apply GlobalTheory.EtC.flatS_tw  <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.alexanderWhitneyDiagonal_and_swap_chain_maps : ∀ N, Pr.d (N + 1) (Pr.aw (N + 1)) = Pr.bd (Pr.aw N) ∧ Pr.d (N + 1) (Pr.wa (N + 1)) = Pr.bd (Pr.wa N) := by
  first | exact @GlobalTheory.EtC.AWChain.aw_wa_chain | exact GlobalTheory.EtC.AWChain.aw_wa_chain | (intros; apply GlobalTheory.EtC.AWChain.aw_wa_chain <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.exists_natural_homotopyEquiv_chains_constant_presheaf : ∀ (R : Type) [CommRing R] , ∃ e : ∀ P : PSh, HomotopyEquiv (sgl ((free R).obj P)) ((chains R).obj (disc.obj P)), (∀ P, sglι _ ≫ (e P).hom.f 0 = (chainsXIso R (disc.obj P) 0).inv) ∧ ∀ {P Q : PSh} (f : P ⟶ Q), (e P).hom ≫ (chains R).map (disc.map f) = (CochainComplex.singleFunctor (Shv R) 0).map ((free R).map f) ≫ (e Q).hom := by
  first | (exact @GlobalTheory.EtC.chains_disc_homotopyEquiv) | (exact GlobalTheory.EtC.chains_disc_homotopyEquiv) | (intros; apply GlobalTheory.EtC.chains_disc_homotopyEquiv  <;> assumption)
end
