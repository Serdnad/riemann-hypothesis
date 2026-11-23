module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAffCoverSpec
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Edge1
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle043
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCorrespondenceFunctionFieldStatementOne
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.IsIntegralRBIff
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.Bundle012
public import Development.AutomorphicArithmetic.GenericGermInjectivity.CoverGeneric
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle006
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle275
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle067
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR GlobalTheory.PD KaehlerDifferential GlobalTheory.W1 GlobalTheory.WH

private theorem germ_ex {X : Scheme.{0}} [IsIntegral X] {V W : X.Opens} (e : V = W) (hV : genericPoint X ∈ V)
    (hW : genericPoint X ∈ W) (y : X.functionField) :
    (∃ f : Γ(X, V), (X.presheaf.germ V (genericPoint X) hV).hom f = y) ↔
      ∃ f : Γ(X, W), (X.presheaf.germ W (genericPoint X) hW).hom f = y := by
  subst e; rfl

private theorem ring_single {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp ℂ} [Algebra ℂ X.functionField] {ι : Type}
    {U : ι → X.Opens} {B : Finset ι → Subalgebra ℂ X.functionField} (h : IsAffCover p U B) (i : ι)
    (hg : genericPoint X ∈ U i) (y : X.functionField) :
    y ∈ B {i} ↔ ∃ f : Γ(X, U i), (X.presheaf.germ (U i) (genericPoint X) hg).hom f = y :=
  (h.ring {i} ⟨i, by simp⟩ y).trans (germ_ex (Finset.inf_singleton ..) _ _ y)

private theorem clear_denom {Y : Scheme.{0}} [IsIntegral Y] (s' : Y ⟶ Sp ℂ) [Algebra ℂ Y.functionField] {A W : Y.Opens}
    (hA : IsAffineOpen A) (gA : genericPoint Y ∈ A) (gW : genericPoint Y ∈ W) (B : Subalgebra ℂ Y.functionField)
    (hB : ∀ y, y ∈ B ↔ ∃ f : Γ(Y, A), (Y.presheaf.germ A (genericPoint Y) gA).hom f = y) (e : B →ₐ[ℂ] ℂ)
    (y : CxPts s' (RingHom.id ℂ)) (hM : UpperTheory.A.Mt s' A gA B e y) (hyW : y ∈ CxPts.ptsIn s' (RingHom.id ℂ) W)
    (f : Γ(Y, W)) :
    ∃ (b : Y.functionField) (hb : b ∈ B), e ⟨b, hb⟩ ≠ 0 ∧
      b * (Y.presheaf.germ W (genericPoint Y) gW).hom f ∈ B := by
  obtain ⟨hyA, hev⟩ := hM
  obtain ⟨h, hhW, hh⟩ := hA.exists_basicOpen_le (V := W) ⟨_, CxPts.mem_ptsIn.1 hyW⟩ (CxPts.mem_ptsIn.1 hyA)
  have hD : y ∈ CxPts.ptsIn s' (RingHom.id ℂ) (Y.basicOpen h) := CxPts.mem_ptsIn.2 hh
  have hne := (CxPts.mem_ptsIn_basicOpen hyA h).1 hD
  have gD : genericPoint Y ∈ Y.basicOpen h :=
    ((genericPoint_spec Y).mem_open_set_iff (Y.basicOpen h).isOpen).2 ⟨_, trivial, hh⟩
  have := hA.isLocalization_basicOpen h
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj h ((Y.presheaf.map (homOfLE hhW).op).hom f)
  have hb : (Y.presheaf.germ A (genericPoint Y) gA).hom (h ^ n) ∈ B := (hB _).2 ⟨_, rfl⟩
  refine ⟨_, hb, ?_, (hB _).2 ⟨a, ?_⟩⟩
  · rw [hev (h ^ n) hb, CxPts.ev_eq hyA, map_pow, ← CxPts.ev_eq hyA]
    exact pow_ne_zero n hne
  · have e1 := congrArg (Y.presheaf.germ (Y.basicOpen h) (genericPoint Y) gD).hom ha
    have e2 : ∀ g : Γ(Y, A), (Y.presheaf.germ (Y.basicOpen h) (genericPoint Y) gD).hom (algebraMap Γ(Y, A) Γ(Y, Y.basicOpen h) g)
        = (Y.presheaf.germ A (genericPoint Y) gA).hom g := fun g =>
      Y.presheaf.germ_res_apply (homOfLE (Y.basicOpen_le h)) (genericPoint Y) gD g
    have e3 : (Y.presheaf.germ (Y.basicOpen h) (genericPoint Y) gD).hom ((Y.presheaf.map (homOfLE hhW).op).hom f)
        = (Y.presheaf.germ W (genericPoint Y) gW).hom f :=
      Y.presheaf.germ_res_apply (homOfLE hhW) (genericPoint Y) gD f
    rw [map_mul, map_pow, e2, e2, e3] at e1
    rw [map_pow, mul_comm]
    exact e1.symm

theorem UpperTheory.etaleCorrespondence_sections_statement :
    ∀ (d : ℕ) (Z Y : Scheme.{0}) [IsIntegral Z] [IsIntegral Y] (s : Z ⟶ Sp ℂ) (s' : Y ⟶ Sp ℂ) [SmoothOfRelativeDimension d s] [SmoothOfRelativeDimension d s'] (hP : IsProjOver s) (c1 c2 : Y ⟶ Z) (h1 : c1 ≫ s = s') (h2 : c2 ≫ s = s') [IsFinite c1] [Etale c1] [IsFinite c2] [Etale c2] [instK : Algebra ℂ Z.functionField] [instL : Algebra ℂ Y.functionField] (hK : instK = ffAlg s) (hL : instL = ffAlg s') [Algebra Z.functionField Y.functionField] [IsScalarTower ℂ Z.functionField Y.functionField] (g1 : ∀ (V : Z.Opens) (hV : genericPoint Z ∈ V) (hV' : genericPoint Y ∈ c1 ⁻¹ᵁ V) (g : Γ(Z, V)), (Y.presheaf.germ (c1 ⁻¹ᵁ V) (genericPoint Y) hV').hom ((c1.app V).hom g) = algebraMap Z.functionField Y.functionField ((Z.presheaf.germ V (genericPoint Z) hV).hom g)) (j2 : Z.functionField →ₐ[ℂ] Y.functionField) (g2 : ∀ (V : Z.Opens) (hV : genericPoint Z ∈ V) (hV' : genericPoint Y ∈ c2 ⁻¹ᵁ V) (g : Γ(Z, V)), j2 ((Z.presheaf.germ V (genericPoint Z) hV).hom g) = (Y.presheaf.germ (c2 ⁻¹ᵁ V) (genericPoint Y) hV').hom (c2.app V g)) (F : Type) [Field F] [Algebra ℂ F] [Algebra F Z.functionField] [Algebra F Y.functionField] [IsScalarTower ℂ F Z.functionField] [IsScalarTower F Z.functionField Y.functionField] [IsScalarTower ℂ F Y.functionField] (x : Fin (d + 1) → F) (U : Fin (d + 1) → Z.Opens) (hx : IsFinCover ℂ Z.functionField x) (hU : IsAffCover s U (rB ℂ Z.functionField x)) (i : Fin (d + 1)) (e : rB ℂ Y.functionField x {i} →ₐ[ℂ] ℂ), ∃ j : Fin (d + 1), ∀ v ∈ R2 x j2 {j}, ∃ (b : Y.functionField) (hb : b ∈ rB ℂ Y.functionField x {i}), e ⟨b, hb⟩ ≠ 0 ∧ b * v ∈ rB ℂ Y.functionField x {i} := by
  intro d Z Y _ _ s s' _ _ hP c1 c2 h1 h2 _ _ _ _ instK instL hK hL _ _ g1 j2 g2 F _ _ _ _ _ _ _ x U hx hU i e
  obtain ⟨-, hU1⟩ := UpperTheory.A.isFinCover_pull h1 hK hL g1 hx hU
  have hU2 := UpperTheory.etaleCorrespondence_functionField_statement_one d Z Y s s' hP c1 c2 h1 h2 hK hL g1 j2 g2 F x U hx hU
  have gen : ∀ (c : Y ⟶ Z) [Etale c] (k : Fin (d + 1)), genericPoint Y ∈ c ⁻¹ᵁ U k := fun c _ k => by
    change c (genericPoint Y) ∈ U k
    rw [UpperTheory.A.generic_map c]
    simpa using hU.ne {k}
  have hA : IsAffineOpen (c1 ⁻¹ᵁ U i) := by simpa using hU1.affine {i} ⟨i, by simp⟩
  have hB := ring_single hU1 i (gen c1 i)
  obtain ⟨y, hy, -⟩ := (UpperTheory.complexPoints_bijective_algHom_affineOpen Y s' hL _ hA (gen c1 i) _ hB).1 e
  obtain ⟨j, hj⟩ := CxPts.exists_mem_ptsIn hU.cover (UpperTheory.A.zpt c2 h2 y)
  have hyW : y ∈ CxPts.ptsIn s' (RingHom.id ℂ) (c2 ⁻¹ᵁ U j) := by
    refine CxPts.mem_ptsIn.2 ?_
    exact CxPts.mem_ptsIn.1 hj
  refine ⟨j, fun v hv => ?_⟩
  obtain ⟨f, rfl⟩ := (ring_single hU2 j (gen c2 j) v).1 hv
  exact clear_denom s' hA (gen c1 i) (gen c2 j) _ hB e y hy hyW f
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory GlobalTheory.PD GlobalTheory.CechDR GlobalTheory.HodgeCoh ReciprocityTheory.ChartRestriction.G.Geo.Tor UpperTheory.GenericCoverClass

theorem UpperTheory.isAffCover_prod_cechOpen :
    ∀ (d : ℕ) (Z : Scheme.{0}) [IsIntegral Z] (p : Z ⟶ Sp ℂ) [SmoothOfRelativeDimension d p] [inst : Algebra ℂ Z.functionField] (ι : Type) [LinearOrder ι] [Fintype ι] (U : ι → Z.Opens) (B : Finset ι → Subalgebra ℂ Z.functionField) (hinst : inst = ffAlg p) (hU : IsAffCover p U B)
            (d' : ℕ) (Z' : Scheme.{0}) [IsIntegral Z'] (p' : Z' ⟶ Sp ℂ) [SmoothOfRelativeDimension d' p'] [inst' : Algebra ℂ Z'.functionField] (κ : Type) [LinearOrder κ] [Fintype κ] (U' : κ → Z'.Opens) (B' : Finset κ → Subalgebra ℂ Z'.functionField) (hinst' : inst' = ffAlg p') (hU' : IsAffCover p' U' B')
            (f : Z' ⟶ Z) (hf : f ≫ p = p') (ψ : Z.functionField →ₐ[ℂ] Z'.functionField) (φ : DR ℂ Z.functionField →ₗ[ℂ] DR ℂ Z'.functionField) (τ : κ → ι),
            IsDRMap ℂ ψ φ → (∀ (V : Z.Opens) (hV : genericPoint Z ∈ V) (hV' : genericPoint Z' ∈ f ⁻¹ᵁ V) (g : Γ(Z, V)), ψ ((Z.presheaf.germ V (genericPoint Z) hV).hom g) = (Z'.presheaf.germ (f ⁻¹ᵁ V) (genericPoint Z') hV').hom (f.app V g)) → (∀ k, U' k ≤ f ⁻¹ᵁ U (τ k)) →
            ∀ (a b : ℕ) (hm : IsMap (cech fun I => omB ℂ Z.functionField (B I) a) (cech fun I => omB ℂ Z'.functionField (B' I) a) (pullC τ φ)) (z : hodgeH p a b),
              cmp d' p' hinst' hU' a b (hodgePull hf a b z) = Cx.hmap _ _ (pullC τ φ) hm b (cmp d p hinst hU a b z) := by
  classical
  intro d Z _ p _ inst ι _ _ U B hinst hU d' Z' _ p' _ inst' κ _ _ U' B' hinst' hU' f hf ψ φ τ hDR hψ hUU' a b hm z
  letI := algΓ p
  letI := algΓ p'
  have hσ := appTop_algebraMap (k := ℂ) hf
  have hcov : ⨆ i, U i = ⊤ := hU.cover
  have haff : ∀ s : Finset ι, s.Nonempty → IsAffineOpen (⨅ i ∈ s, U i) := fun s hs => cover_biInf hU s hs
  have hcov' : ⨆ i, U' i = ⊤ := hU'.cover
  have haff' : ∀ s : Finset κ, s.Nonempty → IsAffineOpen (⨅ i ∈ s, U' i) := fun s hs => cover_biInf hU' s hs
  obtain ⟨x, hx⟩ := (cechClass_surjective (cechCube ℂ (Omega p a) ⊤ U) b)
    ((cechHEquivCoh ℂ hcov haff (Omega p a) b).symm z)
  have hz : cechHEquivCoh ℂ hcov haff (Omega p a) b (cechClass (cechCube ℂ (Omega p a) ⊤ U) b x) = z := by
    rw [hx]
    exact LinearEquiv.apply_symm_apply _ _
  obtain ⟨eZ, -, heZ, -⟩ := cube_exists d p hinst hU a b
  obtain ⟨w, hw⟩ := heZ x
  have hle : ∀ t : Finset κ, cechOpen ⊤ U' t ≤ f ⁻¹ᵁ cechOpen ⊤ U (Finset.image τ t) := by
    intro t y hy
    rw [mem_cechOpen] at hy
    show f.base y ∈ cechOpen ⊤ U (Finset.image τ t)
    rw [mem_cechOpen]
    refine ⟨trivial, fun i hi => ?_⟩
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hi
    exact hUU' k (hy.2 k hk)
  have hcard : ∀ t : {s : Finset κ // s.card = b + 1}, Set.InjOn τ t.1 → (Finset.image τ t.1).card = b + 1 :=
    fun t hinj => (Finset.card_image_of_injOn hinj).trans t.2
  let x' : (cechCube ℂ (Omega p' a) ⊤ U').Term (b + 1) := fun t =>
    if hinj : Set.InjOn τ t.1 then
      sortSign τ t.1 • sectionsOn.res ℂ (Omega p' a) (hle t.1)
        (sectionsOn.map ℂ (omegaPull hf a) (cechOpen ⊤ U (Finset.image τ t.1)) (x.1 ⟨_, hcard t hinj⟩))
    else 0
  have hwC := hm b w w.2.1
  have hw'mem : pullC τ φ (w : Finset ι → DR ℂ Z.functionField) ∈
      (cech fun I => omB ℂ Z'.functionField (B' I) a).Z b := by
    have hw0 : (cech fun I => omB ℂ Z.functionField (B I) a).D (w : Finset ι → DR ℂ Z.functionField) = 0 :=
      w.2.2
    have h0 : (cech fun I => omB ℂ Z'.functionField (B' I) a).D (pullC τ φ (w : Finset ι → DR ℂ Z.functionField)) = 0 := by
      rw [← hwC.2, hw0, map_zero]
    exact ⟨hwC.1, h0⟩
  let w' : ↥((cech fun I => omB ℂ Z'.functionField (B' I) a).Z b) := ⟨_, hw'mem⟩
  have hgm : ∀ t : {s : Finset κ // s.card = b + 1},
      (w' : Finset κ → DR ℂ Z'.functionField) t.1 = gm p' hinst' hU' a t.1 (x' t) := by
    intro t
    have ht : t.1.Nonempty := Finset.card_pos.mp (by rw [t.2]; omega)
    rw [gm_pos hinst' hU' a ht]
    by_cases hinj : Set.InjOn τ t.1
    · have hne : (Finset.image τ t.1).Nonempty := ht.image τ
      have e1 : (w' : Finset κ → DR ℂ Z'.functionField) t.1 =
          sortSign τ t.1 • φ ((w : Finset ι → DR ℂ Z.functionField) (Finset.image τ t.1)) := by
        show pullC τ φ (w : Finset ι → DR ℂ Z.functionField) t.1 = _
        simp only [pullC, LinearMap.coe_mk, AddHom.coe_mk, if_pos hinj]
      rw [e1, show x' t = _ from dif_pos hinj]
      refine Eq.trans ?_ (map_zsmul (formGermI p' a _ _ hinst') (sortSign τ t.1) _).symm
      rw [hw ⟨_, hcard t hinj⟩, gm_pos hinst hU a hne]
      congr 1
      exact (T.genericGerm_differentialForm_pullback_dominant Z Z' p p' hinst hinst' f hf ψ φ hDR hψ a _ _ _ _ _ _ (hle t.1) _).symm
    · have e1 : (w' : Finset κ → DR ℂ Z'.functionField) t.1 = 0 := by
        show pullC τ φ (w : Finset ι → DR ℂ Z.functionField) t.1 = _
        simp only [pullC, LinearMap.coe_mk, AddHom.coe_mk, if_neg hinj]
      rw [e1, show x' t = 0 from dif_neg hinj]
      exact (map_zero (formGermI p' a _ _ hinst')).symm
  obtain ⟨eY, -, -, hdY⟩ := cube_exists d' p' hinst' hU' a b
  have hker : x' ∈ ((cechCube ℂ (Omega p' a) ⊤ U').d (b + 1)).ker := hdY x' w' hgm
  have hR : cechHEquivCoh ℂ hcov' haff' (Omega p' a) b
      (cechClass (cechCube ℂ (Omega p' a) ⊤ U') b ⟨x', hker⟩) = hodgePull hf a b z := by
    refine (T.scheme_cechComparison_natural_refinement Z Z' ℂ f hσ _ _ (omegaPull hf a) ι κ U U' hcov haff hcov' haff' τ hUU' b x
      ⟨x', hker⟩ ?_ ?_).trans ?_
    · intro t s h hinj hs
      obtain ⟨s, hsc⟩ := s
      simp only at hs
      subst hs
      exact dif_pos hinj
    · intro t hinj
      exact dif_neg hinj
    · rw [hz]
      rfl
  rw [← hR, cmp_class d' p' hinst' hU' a b ⟨x', hker⟩ w' hgm, ← hz, cmp_class d p hinst hU a b x w hw]
  rfl
end
