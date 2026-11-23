module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle444
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CrystallineSiteZariskiCoveredByAtlas
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.MapAcrFromBase
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle213
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle421
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle434
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.Bundle005
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
public import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle008
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulEqOfRangeLe
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.QuotVanish

@[expose] public section

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.Deg

theorem gramQ_mul_right (D : D7) (V : HSp D) {r : ℕ} (x : Matrix (Fin V.rank) (Fin r) D.host.E)
    (a : Matrix (Fin r) (Fin r) D.host.E) :
    gramQ V (x * a) = (a.map (D.sp.cm.sig : D.host.E → D.host.E))ᵀ * gramQ V x * a := by
  have hm : (x * a).map (D.sp.cm.sig : D.host.E → D.host.E) =
      x.map (D.sp.cm.sig : D.host.E → D.host.E) * a.map (D.sp.cm.sig : D.host.E → D.host.E) :=
    Matrix.map_mul (f := (D.sp.cm.sig : D.host.E →+* D.host.E))
  unfold gramQ
  rw [hm, Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]

def congrEquiv (D : D7) (V : HSp D) {r : ℕ} (β : HermE D r) (a : Matrix (Fin r) (Fin r) D.host.E)
    (ha : a.det ≠ 0) :
    {x : Matrix (Fin V.rank) (Fin r) D.host.E // x.rank = r ∧ gramQ V x = β.1} ≃
      {x : Matrix (Fin V.rank) (Fin r) D.host.E // x.rank = r ∧ gramQ V x = (congrH a β).1} :=
  have hu : IsUnit a.det := isUnit_iff_ne_zero.mpr ha
  have hi : a * a⁻¹ = 1 := Matrix.mul_nonsing_inv a hu
  have hi' : a⁻¹ * a = 1 := Matrix.nonsing_inv_mul a hu
  have hu' : IsUnit (a⁻¹).det := by
    have := congrArg Matrix.det hi
    rw [Matrix.det_mul, Matrix.det_one] at this
    exact IsUnit.of_mul_eq_one _ (by rwa [mul_comm] at this)
  have hc : ((a⁻¹).map (D.sp.cm.sig : D.host.E → D.host.E))ᵀ *
      (a.map (D.sp.cm.sig : D.host.E → D.host.E))ᵀ = 1 := by
    rw [← Matrix.transpose_mul]
    have hm : (a * a⁻¹).map (D.sp.cm.sig : D.host.E → D.host.E) =
        a.map (D.sp.cm.sig : D.host.E → D.host.E) * (a⁻¹).map (D.sp.cm.sig : D.host.E → D.host.E) :=
      Matrix.map_mul (f := (D.sp.cm.sig : D.host.E →+* D.host.E))
    rw [← hm, hi, Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]
  { toFun := fun x => ⟨x.1 * a, by
      rw [Matrix.rank_mul_eq_left_of_isUnit_det a x.1 hu]
      exact x.2.1, by
      rw [gramQ_mul_right, x.2.2]; rfl⟩
    invFun := fun x => ⟨x.1 * a⁻¹, by
      rw [Matrix.rank_mul_eq_left_of_isUnit_det a⁻¹ x.1 hu']
      exact x.2.1, by
      rw [gramQ_mul_right, x.2.2]
      change ((a⁻¹).map (D.sp.cm.sig : D.host.E → D.host.E))ᵀ *
        ((a.map (D.sp.cm.sig : D.host.E → D.host.E))ᵀ * β.1 * a) * a⁻¹ = β.1
      calc _ = (((a⁻¹).map (D.sp.cm.sig : D.host.E → D.host.E))ᵀ *
              (a.map (D.sp.cm.sig : D.host.E → D.host.E))ᵀ) * β.1 * (a * a⁻¹) := by
            simp only [Matrix.mul_assoc]
        _ = β.1 := by rw [hc, hi, Matrix.one_mul, Matrix.mul_one]⟩
    left_inv := fun x => Subtype.ext (by
      change x.1 * a * a⁻¹ = x.1
      rw [Matrix.mul_assoc, hi, Matrix.mul_one])
    right_inv := fun x => Subtype.ext (by
      change x.1 * a⁻¹ * a = x.1
      rw [Matrix.mul_assoc, hi', Matrix.mul_one]) }

theorem ifrB_congrH : ∀ (D : D7) (V : HSp D) (ν : Measure (GA D V)) (r : ℕ) (φ : Mx D V.rank r → ℂ) (β : HermE D r)
    (a : Matrix (Fin r) (Fin r) D.host.E), a.det ≠ 0 →
    IfrB V ν φ (GlobalTheory.CompanionTheory.WeilSiegel.Deg.congrH a β) = IfrB V ν (pull a φ) β := by
  intro D V ν r φ β a ha
  have key : (fun h : GA D V => ∑' x : {x : Matrix (Fin V.rank) (Fin r) D.host.E //
        x.rank = r ∧ gramQ V x = (congrH a β).1},
        φ (HMul.hMul (Formalism.L2.Theta.mt V h⁻¹) (x.1.map (incA D)))) =
      (fun h : GA D V => ∑' x : {x : Matrix (Fin V.rank) (Fin r) D.host.E //
        x.rank = r ∧ gramQ V x = β.1},
        pull a φ (HMul.hMul (Formalism.L2.Theta.mt V h⁻¹) (x.1.map (incA D)))) := by
    funext h
    rw [← (congrEquiv D V β a ha).tsum_eq]
    refine tsum_congr fun x => ?_
    have hm : (x.1 * a).map (incA D) = HMul.hMul (x.1.map (incA D)) (a.map (incA D)) :=
      Matrix.map_mul (f := incA D)
    change φ (HMul.hMul (Formalism.L2.Theta.mt V h⁻¹) ((x.1 * a).map (incA D))) =
      φ (HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt V h⁻¹) (x.1.map (incA D))) (a.map (incA D)))
    rw [hm, Matrix.mul_assoc]
  unfold IfrB
  rw [key]

end GlobalTheory.CompanionTheory.WeilSiegel.Deg
end
end

section

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.TestZar

theorem idem_unit {R : Type} [CommRing R] {u : R} (hu : IsIdempotentElem u) (h : IsUnit u) : u = 1 :=
  h.mul_left_cancel (by rw [mul_one]; exact hu)

theorem factor_one {R R' ι : Type} [CommRing R] [CommRing R'] (g : R →+* R') (b : ι → R) (hb : ∀ i, IsIdempotentElem (b i))
    (S : Finset ι) (h : g (∏ i ∈ S, b i) = 1) {i : ι} (hi : i ∈ S) : g (b i) = 1 :=
  idem_unit ((hb i).map g) (isUnit_of_dvd_unit (map_dvd g (Finset.dvd_prod_of_mem b hi)) (h ▸ isUnit_one))

theorem span_of_nil {R P ι : Type} [CommRing R] [CommRing P] (I : Ideal R) (hI : ∀ x ∈ I, IsNilpotent x) (g : ι → R)
    (π : P →+* R ⧸ I) (e : ι → P) (he : Ideal.span (Set.range e) = ⊤)
    (h : ∀ i, π (e i) = Ideal.Quotient.mk I (g i)) : Ideal.span (Set.range g) = ⊤ := by
  have h1 : Ideal.map (Ideal.Quotient.mk I) (Ideal.span (Set.range g)) = ⊤ := by
    have e1 : (Ideal.Quotient.mk I) ∘ g = π ∘ e := funext fun i => (h i).symm
    rw [Ideal.map_span, ← Set.range_comp, e1, Set.range_comp, ← Ideal.map_span, he, Ideal.map_top]
  have h2 : (1 : R ⧸ I) ∈ Ideal.map (Ideal.Quotient.mk I) (Ideal.span (Set.range g)) := by
    rw [h1]; trivial
  obtain ⟨a, ha, ha1⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 h2
  have hj : a - 1 ∈ I := Ideal.Quotient.eq.1 (by rw [ha1, map_one])
  have hu : IsUnit a := by
    have := (hI _ hj).isUnit_add_one
    simpa using this
  exact Ideal.eq_top_of_isUnit_mem _ ha hu

section Gen

open GlobalTheory.CompanionTheory.ThickZar

variable {O : Type} [CommRing O] {F : Fn O} {b : Base} {ht : b.t = 1} {κ : O →+* b.R ⧸ b.I}
  {R₀ : Type} [CommRing R₀] (c : R₀ →+* b.R) (r : ℕ)
  {C : Type*} [Category C] (G : C ⥤ Thick (F.cr b ht κ))

def locModG {m : ℕ} (T' : C) (Lc : Finset (Fin m) → C) (lam : ∀ S, T' ⟶ Lc S)
    (f : Fin m → (G.obj T').B) (hf : Ideal.span (Set.range f) = ⊤)
    (h1 : ∀ S, ∀ k ∈ S, (G.map (lam S)).φ (f k) = 1)
    (hs : ∀ S, ∀ y ∈ (G.obj (Lc S)).pdPow r, ∃ x ∈ (G.obj T').pdPow r, (G.map (lam S)).φ x = y)
    (hk : ∀ S x, (G.map (lam S)).φ x = 0 → (∏ k ∈ S, f k) * x = 0) :
    LocMod (G ⋙ (pdS (F.cr b ht κ) c r).fn) T' Lc lam where
  Λ := (G.obj T').B
  f := f
  span := hf
  ρ₀ := mulR c r (G.obj T')
  ρ S := (mulR c r (G.obj (Lc S))).comp (G.map (lam S)).φ
  lam_ρ S a x := Subtype.ext (map_mul (G.map (lam S)).φ a (show (G.obj T').B from x.1))
  tr_ρ S S' t ht' a x := by
    have e : (G.map t).φ.comp (G.map (lam S)).φ = (G.map (lam S')).φ := by
      have := congrArg Thick.Hom.φ (congrArg G.map ht')
      rw [G.map_comp] at this
      exact this
    refine Subtype.ext ?_
    change (G.map t).φ ((G.map (lam S)).φ a * (show (G.obj (Lc S)).B from x.1)) =
      (G.map (lam S')).φ a * (G.map t).φ (show (G.obj (Lc S)).B from x.1)
    rw [map_mul, ← RingHom.comp_apply (G.map t).φ, e]
  unit S k hk' := by
    change Function.Bijective (mulR c r (G.obj (Lc S)) ((G.map (lam S)).φ (f k)))
    rw [h1 S k hk', map_one]
    exact Function.bijective_id
  surj S y := by
    obtain ⟨x, hx, e⟩ := hs S y.1 y.2
    refine ⟨0, ⟨x, hx⟩, ?_⟩
    rw [pow_zero, map_one]
    exact Subtype.ext e.symm
  ker S x hx := by
    have h0 : (G.map (lam S)).φ (show (G.obj T').B from x.1) = 0 := congrArg Subtype.val hx
    refine ⟨1, Subtype.ext ?_⟩
    rw [pow_one]
    exact hk S _ h0

end Gen

variable {l : ℕ} [Fact l.Prime]

theorem step_onto {A B : PAlg l} (lam : A ⟶ B) (k : Bool) (n r : ℕ) (hs : Function.Surjective (mapAcr lam n))
    {y : B.Acr n} (hy : y ∈ fil (DD k B n) r) : ∃ x ∈ fil (DD k A n) r, mapAcr lam n x = y := by
  have hA := (GlobalTheory.T.period_ring_base_change_from_universal A n).2.2.2.2.1 k r
  have hB := (GlobalTheory.T.period_ring_base_change_from_universal B n).2.2.2.2.1 k r
  have e : (mapAcr lam n).comp (mapAcr A.fromBase n) = mapAcr B.fromBase n :=
    RingHom.ext fun x => mapAcr_fromBase lam n x
  rw [hB, ← e, ← Ideal.map_map, ← hA] at hy
  exact (Ideal.mem_map_iff_of_surjective _ hs).1 hy

theorem span_acr (A : PAlg l) (n : ℕ) {m : ℕ} (e : Fin m → A.A) (he : Ideal.span (Set.range e) = ⊤) :
    Ideal.span (Set.range fun i => A.toAcr n (WittVector.teichmuller l (e i))) = ⊤ := by
  obtain ⟨⟨π, hπ, -⟩, -, -, -, -, hnil, -⟩ := GlobalTheory.T.period_ring_base_change_from_universal A n
  exact span_of_nil (A.PFil n) (fun x hx => (hnil x hx).1) _ π e he fun i => hπ _

theorem acr_teich_one {A B : PAlg l} (f : A ⟶ B) (n : ℕ) {a : A.A} (h : Hom.f f a = 1) :
    mapAcr f n (A.toAcr n (WittVector.teichmuller l a)) = 1 := by
  rw [mapAcr_toAcr, mapW, WittVector.map_teichmuller, h, map_one, map_one]

theorem acr_teich_prod (A : PAlg l) (n : ℕ) {ι : Type} (S : Finset ι) (a : ι → A.A) :
    A.toAcr n (WittVector.teichmuller l (∏ i ∈ S, a i)) = ∏ i ∈ S, A.toAcr n (WittVector.teichmuller l (a i)) := by
  rw [map_prod, map_prod]

section Fac

variable {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l)

def facObj (T' : El (F.pt κ)) (A' : PAlg l) (lam : T'.1.obj ⟶ A') (h : A'.IsTest) : El (F.pt κ) :=
  (testι l ⋙ F.pt κ).elementsMk ⟨A', h⟩ ((F.pt κ).map lam T'.val)

def facHom (T' : El (F.pt κ)) (A' : PAlg l) (lam : T'.1.obj ⟶ A') (h : A'.IsTest) : T' ⟶ facObj F κ T' A' lam h :=
  ⟨ObjectProperty.homMk lam, rfl⟩

theorem fac_univ (T' : El (F.pt κ)) (A' : PAlg l) (lam : T'.1.obj ⟶ A') (h : A'.IsTest) (T'' : El (F.pt κ)) (ψ : T' ⟶ T'')
    (hu : ∃! χ : A' ⟶ T''.1.obj, lam ≫ χ = ψ.1.hom) :
    ∃! χ : facObj F κ T' A' lam h ⟶ T'', facHom F κ T' A' lam h ≫ χ = ψ := by
  obtain ⟨χ, hχ, huniq⟩ := hu
  refine ⟨⟨ObjectProperty.homMk χ, ?_⟩, Functor.Elements.hom_ext (ObjectProperty.hom_ext _ hχ), fun χ' h' =>
    Functor.Elements.hom_ext (ObjectProperty.hom_ext _ (huniq χ'.1.hom (congrArg (fun z => z.1.hom) h')))⟩
  change (F.pt κ).map χ ((F.pt κ).map lam T'.2) = T''.2
  rw [← Functor.map_comp_apply, hχ]
  exact ψ.2

theorem fac_loc (k : Bool) (n r : ℕ) (T' : El (F.pt κ)) {m : ℕ} (b : Fin m → T'.1.obj.A)
    (hspan : Ideal.span (Set.range b) = ⊤) (A' : Finset (Fin m) → PAlg l) (lam : ∀ S, T'.1.obj ⟶ A' S)
    (ht : ∀ S, (A' S).IsTest) (h1 : ∀ S, ∀ i ∈ S, Hom.f (lam S) (b i) = 1)
    (hs : ∀ S, Function.Surjective (mapAcr (lam S) n))
    (hk : ∀ S x, mapAcr (lam S) n x = 0 → T'.1.obj.toAcr n (WittVector.teichmuller l (∏ i ∈ S, b i)) * x = 0) :
    Nonempty (LocMod (gT F κ k n ⋙ (pdS (Lc F κ k n) ((base l).cris n) r).fn) T'
      (fun S => facObj F κ T' (A' S) (lam S) (ht S)) fun S => facHom F κ T' (A' S) (lam S) (ht S)) := by
  have hf : Ideal.span (Set.range fun i => T'.1.obj.toAcr n (WittVector.teichmuller l (b i))) = ⊤ := span_acr _ n b hspan
  have hk' : ∀ S x, mapAcr (lam S) n x = 0 →
      (∏ i ∈ S, T'.1.obj.toAcr n (WittVector.teichmuller l (b i))) * x = 0 := fun S x hx => by
    have h := hk S x hx
    rw [acr_teich_prod] at h
    exact h
  exact ⟨locModG (F := F) (b := bs l k n) (ht := rfl) (κ := κb κ k n) ((base l).cris n) r (gT F κ k n) T'
    (fun S => facObj F κ T' (A' S) (lam S) (ht S)) (fun S => facHom F κ T' (A' S) (lam S) (ht S))
    (fun i => T'.1.obj.toAcr n (WittVector.teichmuller l (b i))) hf
    (fun S i hi => acr_teich_one (lam S) n (h1 S i hi))
    (fun S y hy => step_onto (lam S) k n r (hs S) hy) hk'⟩

theorem factors (k : Bool) (n r : ℕ) (T' : El (F.pt κ)) {m : ℕ}
    (b : Fin m → T'.1.obj.A) (hb : ∀ i, IsIdempotentElem (b i)) (hspan : Ideal.span (Set.range b) = ⊤) :
    ∃ (Lc' : Finset (Fin m) → El (F.pt κ)) (lamE : ∀ S, T' ⟶ Lc' S),
      (∀ S, ∀ i ∈ S, Hom.f (lamE S).1.hom (b i) = 1) ∧
      (∀ S (T'' : El (F.pt κ)) (ψ : T' ⟶ T''), (∀ i ∈ S, Hom.f ψ.1.hom (b i) = 1) → ∃! χ : Lc' S ⟶ T'', lamE S ≫ χ = ψ) ∧
      Nonempty (LocMod (gT F κ k n ⋙ (pdS (Lc F κ k n) ((base l).cris n) r).fn) T' Lc' lamE) := by
  have ha : ∀ S : Finset (Fin m), IsIdempotentElem (∏ i ∈ S, b i) := fun S =>
    Finset.prod_induction _ IsIdempotentElem (fun _ _ h h' => h.mul h') IsIdempotentElem.one fun i _ => hb i
  choose A' lam htest hlam huniv hacr using fun S => GlobalTheory.T.idempotent_localization_universal T'.1.obj (∏ i ∈ S, b i) (ha S)
  have h1 : ∀ S, ∀ i ∈ S, Hom.f (lam S) (b i) = 1 := fun S i hi => factor_one (Hom.f (lam S)) b hb S (hlam S) hi
  have ht : ∀ S, (A' S).IsTest := fun S => htest S T'.1.property
  refine ⟨fun S => facObj F κ T' (A' S) (lam S) (ht S), fun S => facHom F κ T' (A' S) (lam S) (ht S), h1,
    fun S T'' ψ h => fac_univ F κ T' (A' S) (lam S) (ht S) T'' ψ (huniv S T''.1.obj ψ.1.hom ?_),
    fac_loc F κ k n r T' b hspan A' lam ht h1 (fun S => (hacr S n).1) fun S => (hacr S n).2⟩
  rw [map_prod]
  exact Finset.prod_eq_one fun i hi => h i hi

end Fac

theorem chart_of_one {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) {d : ℕ} (𝒜 : F.Atlas d) (k : Bool) (n : ℕ)
    {T T₁ : El (F.pt κ)} (ψ : T ⟶ T₁) (s : T.1.obj.U) (a : T.1.obj.A) (ha : T.1.obj.sharp a ∈ Ideal.span {s})
    (hcov : ∀ (B' : CommRingCat) (φ : CommRingCat.of T.1.obj.U ⟶ B'), IsUnit (φ.hom s) →
      ∃ α, (𝒜.V α).In (F.Pt.map φ T.2.1))
    (h : Hom.f ψ.1.hom a = 1) : ∃ α, (𝒜.V α).In ((gT F κ k n).obj T₁).y.1.2 := by
  have hu : IsUnit ((CommRingCat.ofHom (mapU ψ.1.hom)).hom s) := by
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 ha
    have h2 := congrArg (mapU ψ.1.hom) hc
    rw [map_mul, mapU_sharp, h, map_one] at h2
    exact IsUnit.of_mul_eq_one _ (by rw [mul_comm]; exact h2)
  obtain ⟨α, hα⟩ := hcov _ _ hu
  have hpt : F.Pt.map (CommRingCat.ofHom (mapU ψ.1.hom)) T.2.1 = T₁.2.1 := congrArg Subtype.val ψ.2
  rw [hpt] at hα
  exact ⟨α, (𝒜.V α).in_map (CommRingCat.ofHom (uJ k T₁.1.obj n)) hα⟩

theorem zarCov_test : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) {d : ℕ} (𝒜 : F.Atlas d)
    (k : Bool) (n r : ℕ), ZarCov (gT F κ k n ⋙ (pdS (Lc F κ k n) ((base l).cris n) r).fn)
      fun T => ∃ α, (𝒜.V α).In ((gT F κ k n).obj T).y.1.2 := by
  intro l _ O _ F κ d 𝒜 k n r
  refine ⟨fun T T' φ h => (GlobalTheory.CompanionTheory.ThickZar.zarCov_pdS F (bs l k n) rfl (κb κ k n) ((base l).cris n) 𝒜
    (Fact.out : l.Prime).ne_zero r).1 ((gT F κ k n).map φ) h, fun T => ?_⟩
  obtain ⟨m, s, hs, hcov⟩ := 𝒜.cov (CommRingCat.of T.1.obj.U) T.2.1
  obtain ⟨e, hidem, hspan, hes⟩ := GlobalTheory.T.idempotent_refinement_of_unimodular T.1.obj T.1.property s hs
  refine ⟨m, fun i _ ψ => Hom.f ψ.1.hom (e i) = 1, fun i T₁ T₂ ψ χ h => ?_,
    fun i T₁ ψ h => chart_of_one F κ 𝒜 k n ψ (s i) (e i) (hes i) (hcov i) h, fun T' φ => ?_⟩
  · have h' : Hom.f ψ.1.hom (e i) = 1 := h
    have e1 : Hom.f (ψ ≫ χ).1.hom (e i) = Hom.f χ.1.hom (Hom.f ψ.1.hom (e i)) := rfl
    exact e1.trans (by rw [h', map_one])
  have hspan' : Ideal.span (Set.range fun i => Hom.f φ.1.hom (e i)) = ⊤ := by
    have h := congrArg (Ideal.map (Hom.f φ.1.hom)) hspan
    rw [Ideal.map_span, Ideal.map_top, ← Set.range_comp] at h
    exact h
  obtain ⟨Lc', lamE, h1, h2, h3⟩ := factors F κ k n r T' (fun i => Hom.f φ.1.hom (e i))
    (fun i => (hidem i).map (Hom.f φ.1.hom)) hspan'
  exact ⟨Lc', lamE, fun S i hi => h1 S i hi, fun S T'' ψ h => h2 S T'' ψ fun i hi => h i hi, h3⟩

end GlobalTheory.CompanionTheory.TestZar
end
end

section

set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit segre fibre IsGoodProj IsSheet HermLine IsSmoothHerm sheetDensity maDensity ptsIntegral ptsIntegralAt pot)
open ReciprocityTheory.ChartRestriction.G.AI.I2 (IsRatSectionOn logNormRat)

noncomputable section

namespace GlobalTheory.CompanionTheory.MixZ.ArchEq

variable {m : ℕ} {n : Fin (m + 1) → ℕ} {D : ℕ}

abbrev Over {X : Scheme.{0}} (i : X ⟶ MP ℤ m n) (y : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀)
    (z : (Σ k, Bk n k) → ℂ) : Prop :=
  IsUnder (PtsOver.map i rfl _ y) z

abbrev LinProj (n : Fin (m + 1) → ℕ) (D : ℕ) := (((k : Fin (m + 1)) → Bk n k) → ℂ) →ₗ[ℂ] (Fin (D + 1) → ℂ)

def ratios (Ψ : LinProj n D) (z : (Σ k, Bk n k) → ℂ) : Fin D → ℂ :=
  fun a => Ψ (segre z) a.succ / Ψ (segre z) 0


open Classical in
def liftOf {X : Scheme.{0}} (i : X ⟶ MP ℤ m n) (y : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀) : (Σ k, Bk n k) → ℂ :=
  if h : ∃ z, Over i y z then h.choose else 0

def projCoord {X : Scheme.{0}} (i : X ⟶ MP ℤ m n) (Ψ : LinProj n D) (y : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀) :
    Fin D → ℂ :=
  ratios Ψ (liftOf i y)

def IsRegAt {X : Scheme.{0}} (i : X ⟶ MP ℤ m n) (Ψ : LinProj n D) (c : GlobalTheory.AlgChart (i ≫ mpStr ℤ m n) σ₀ D)
    (y : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀) : Prop :=
  LinearMap.det (fderiv ℂ (projCoord i Ψ ∘ c.finChart.symm) (c.finChart y) :
    (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ)) ≠ 0

def IsPiece {X : Scheme.{0}} [IsIntegral X] (i : X ⟶ MP ℤ m n) (Ψ : LinProj n D) (N : Pol n)
    (e : OpenPartialHomeomorph (GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀) (Fin D → ℂ))
    (Γ : (Fin D → ℂ) → (Σ k, Bk n k) → ℂ) : Prop :=
  (∃ c : GlobalTheory.AlgChart (i ≫ mpStr ℤ m n) σ₀ D, e.source ⊆ c.e.source) ∧ DifferentiableOn ℂ Γ e.target ∧
    ∀ v ∈ e.target, Over i (e.symm v) (Γ v) ∧ Γ v ∈ mcPts (ptIdeal (i (genericPoint X))) ∧
      Ψ (segre (Γ v)) = Fin.cons 1 v ∧ eval (Γ v) (map (Int.castRingHom ℂ) N) ≠ 0

def pieceSet {X : Scheme.{0}} [IsIntegral X] (i : X ⟶ MP ℤ m n) (Ψ : LinProj n D) (N : Pol n) :
    Set (GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀) :=
  {y | ∃ e Γ, IsPiece i Ψ N e Γ ∧ y ∈ e.source}

theorem isOpen_pieceSet {X : Scheme.{0}} [IsIntegral X] (i : X ⟶ MP ℤ m n) (Ψ : LinProj n D) (N : Pol n) :
    IsOpen (pieceSet i Ψ N) := isOpen_iff_forall_mem_open.mpr fun _ ⟨e, Γ, hp, hy⟩ =>
  ⟨e.source, fun _ hy' => ⟨e, Γ, hp, hy'⟩, e.open_source, hy⟩

theorem segre_orbit {z z' : (Σ k, Bk n k) → ℂ} {c : Fin (m + 1) → ℂ} (h : z = fun p => c p.1 * z' p) :
    segre z = (∏ k, c k) • segre z' := by
  subst h
  funext a
  simp [ReciprocityTheory.ChartRestriction.G.Geo.segre, Finset.prod_mul_distrib]

theorem ratios_eq_of_sameOrbit (Ψ : LinProj n D) {z z' : (Σ k, Bk n k) → ℂ} (h : SameOrbit z z')
    (h0 : Ψ (segre z') 0 ≠ 0) : ratios Ψ z = ratios Ψ z' := by
  obtain ⟨c, hc, rfl⟩ := h
  have hprod : (∏ k, c k) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hc k
  funext a
  simp only [ratios, segre_orbit (c := c) rfl, map_smul, Pi.smul_apply, smul_eq_mul]
  exact mul_div_mul_left _ _ hprod

theorem ratios_of_proj (Ψ : LinProj n D) {z : (Σ k, Bk n k) → ℂ} {v : Fin D → ℂ}
    (h : Ψ (segre z) = Fin.cons 1 v) : ratios Ψ z = v := by
  funext a
  simp [ratios, h]

theorem homog_mul {f g : Pol n} {a b : Fin (m + 1) → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g b) :
    IsMultiHomog (f * g) (a + b) := by
  classical
  intro d hd k
  obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.1 (MvPolynomial.support_mul f g hd)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, hf x hx k, hg y hy k, Pi.add_apply]

end GlobalTheory.CompanionTheory.MixZ.ArchEq
end
end

section

open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 GlobalTheory.CompanionTheory.TorusCh
open scoped Pointwise

namespace GlobalTheory.CompanionTheory.TorusCh

theorem pair_range_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
    (D p : Matrix (Fin n) (Fin n) E) (a b : Fin n → E) :
    ∑ i, conjE E ((p *ᵥ a) i) * (D *ᵥ (p *ᵥ b)) i =
      (conjE E ∘ a) ⬝ᵥ (((p.map (conjE E))ᵀ * D * p) *ᵥ b) := by
  have h1 : ((p.map (conjE E))ᵀ * D * p) *ᵥ b = (p.map (conjE E))ᵀ *ᵥ (D *ᵥ (p *ᵥ b)) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, mul_assoc]
  rw [h1, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [RingHom.map_mulVec]

theorem iso_range_iff_sg_mul (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ)
    (d : GL (Fin n) E) (π : Matrix (Fin n) (Fin n) E) :
    LinearMap.range (Matrix.toLin' π) ≤ perpD (conjE E) d (LinearMap.range (Matrix.toLin' π)) ↔
      sg d π * π = 0 := by
  have hd1 : d.val * (d⁻¹ : GL (Fin n) E).val = 1 := Units.mul_inv d
  have hd2 : (d⁻¹ : GL (Fin n) E).val * d.val = 1 := Units.inv_mul d
  have hsg : sg d π * π = d.val * ((π.map (conjE E))ᵀ * (d⁻¹ : GL (Fin n) E).val * π) := by
    simp only [sg, mul_assoc]
  have hM : sg d π * π = 0 ↔ (π.map (conjE E))ᵀ * (d⁻¹ : GL (Fin n) E).val * π = 0 := by
    rw [hsg]
    constructor
    · intro h
      have h2 := congrArg (fun X => (d⁻¹ : GL (Fin n) E).val * X) h
      simpa [← mul_assoc, hd2] using h2
    · intro h
      rw [h, mul_zero]
  rw [hM]
  constructor
  · intro h
    ext i j
    have hv : π *ᵥ Pi.single j 1 ∈ perpD (conjE E) d (LinearMap.range (Matrix.toLin' π)) :=
      h ⟨Pi.single j 1, by rw [Matrix.toLin'_apply]⟩
    obtain ⟨y, hy, hyv⟩ := hv
    have hy' : ∀ x ∈ LinearMap.range (Matrix.toLin' π), ∑ k, conjE E (x k) * y k = 0 := hy
    have hyd : y = (d⁻¹ : GL (Fin n) E).val *ᵥ (π *ᵥ Pi.single j 1) := by
      rw [← hyv, Matrix.toLin'_apply, Matrix.mulVec_mulVec, hd2, Matrix.one_mulVec]
    have h3 := hy' (π *ᵥ Pi.single i 1) ⟨Pi.single i 1, by rw [Matrix.toLin'_apply]⟩
    rw [hyd, pair_range_eq] at h3
    have hc : (conjE E ∘ (Pi.single i 1 : Fin n → E)) = Pi.single i 1 := by
      funext k
      by_cases hk : k = i
      · subst hk; simp
      · simp [Pi.single_apply, hk]
    rw [hc, single_one_dotProduct, Matrix.mulVec_single_one] at h3
    simpa using h3
  · rintro h _ ⟨b, rfl⟩
    refine ⟨(d⁻¹ : GL (Fin n) E).val *ᵥ (π *ᵥ b), ?_, ?_⟩
    · rintro _ ⟨a, rfl⟩
      simp only [Matrix.toLin'_apply]
      rw [pair_range_eq, h, Matrix.zero_mulVec, dotProduct_zero]
    · rw [Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.mulVec_mulVec, hd1, Matrix.one_mulVec]

end GlobalTheory.CompanionTheory.TorusCh
end
