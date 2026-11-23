module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCMFrame
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle071
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle067
public import Development.WeilBound.CoreStatements.SesquilinearFractions.Bundle012
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle014
public import Development.WeilBound.CoreStatements.SesquilinearFractions.Bundle006
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle010
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
open scoped CategoryTheory.Obj

namespace PositivityTheory.Xgf

section Rings

variable {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R'']

theorem spMap_comp_spMap_sesquilinear_fractions (f : R →+* R') (f' : R' →+* R'') : spMap f' ≫ spMap f = spMap (f'.comp f) := by
  rw [← Spec.map_comp]; rfl

theorem dualMap_comp_algebraMap_sesquilinear_fractions (f : R →+* R') :
    (dualMap f).comp (algebraMap R (DualNumber R)) = (algebraMap R' (DualNumber R')).comp f :=
  RingHom.ext fun x => TrivSqZeroExt.ext (by simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl])
    (by simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl])

theorem fstHom_comp_dualMap' (f : R →+* R') :
    (TrivSqZeroExt.fstHom R' R' R').toRingHom.comp (dualMap f) = f.comp (TrivSqZeroExt.fstHom R R R).toRingHom :=
  RingHom.ext fun x => by simp [dualMap]

theorem fst_comp_algebraMap_dual : (TrivSqZeroExt.fstHom R R R).toRingHom.comp (algebraMap R (DualNumber R)) = RingHom.id R :=
  RingHom.ext fun x => by simp [TrivSqZeroExt.algebraMap_eq_inl]

theorem dualMap_comp_dualMap_ring (f : R →+* R') (f' : R' →+* R'') : (dualMap f').comp (dualMap f) = dualMap (f'.comp f) := by
  ext x <;> simp [dualMap]

theorem dualMap_eq_dualMapR' (f : R →+* R') : dualMap f = ReciprocityTheory.ChartRestriction.G.Chart.dualMapR f := RingHom.ext fun _ => rfl

end Rings

theorem mono_spec_fraction_field (K : Type) [Field K] [NumberField K] : Mono (spMap (algebraMap (𝓞 K) K)) := by
  haveI : Epi (CommRingCat.ofHom (algebraMap (𝓞 K) K)) := IsLocalization.epi (nonZeroDivisors (𝓞 K)) K
  show Mono (Scheme.Spec.map (CommRingCat.ofHom (algebraMap (𝓞 K) K)).op)
  infer_instance


theorem cm_image_unique_lattice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (Z : ∀ b : Bool, Curve0 H (sgnRt H b)) (P : (FU.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (FU.Di i) ty P) (X : CMPack Z c FU i hP) (b : Bool) (a : PureType.lat hP (sgnRt H b)), (∃! u, X.IsImage b a u) ∧ ∀ u, X.IsImage b a u → IsTanAt Xo.univ.t.G _ u ∧ IsDerivAt0 (fun s => (FU.ex i P s).left) ((Z b).z • P a) (spMap (dualMap (algebraMap X.K ℂ)) ≫ u.left) := by
  intro E _ _ _ H D l Xo c g ty FU i Z P hP X b a
  have hmono := mono_spec_fraction_field X.K
  set φ : 𝓞 X.K →+* X.K := algebraMap (𝓞 X.K) X.K with hφ
  have hA : (X.C b).v.left ≫ (X.C b).P.A.hom = spMap (algebraMap (𝓞 X.K) (DualNumber (𝓞 X.K))) := Over.w (X.C b).v
  have hψ : (X.ψ b a).left ≫ X.B.t.G.hom = (X.C b).P.A.hom := Over.w (X.ψ b a)
  set F : Sp (DualNumber X.K) ⟶ X.B.t.G.left := spMap (dualMap φ) ≫ (X.C b).v.left ≫ (X.ψ b a).left with hFdef
  have hF : F ≫ X.B.t.G.hom = spMap (algebraMap X.K (DualNumber X.K)) ≫ spMap φ := by
    rw [hFdef, Category.assoc, Category.assoc, hψ, hA, spMap_comp_spMap_sesquilinear_fractions, spMap_comp_spMap_sesquilinear_fractions, dualMap_comp_algebraMap_sesquilinear_fractions]
  have m'c := X.m'.cart.1
  have mc := X.m.cart.1

  have hbase : ∀ r : Sp (DualNumber X.K) ⟶ X.t.G.left, r ≫ X.m'.φ = F →
      r ≫ X.t.G.hom = spMap (algebraMap X.K (DualNumber X.K)) := by
    intro r hr
    apply (cancel_mono (spMap φ)).1
    rw [Category.assoc, ← m'c.w, ← Category.assoc, hr, hF]
  refine ⟨?_, ?_⟩
  · let r₀ := m'c.lift F (spMap (algebraMap X.K (DualNumber X.K))) hF
    have hr₀ : r₀ ≫ X.m'.φ = F := m'c.lift_fst _ _ _
    have hr₀' : r₀ ≫ X.t.G.hom = spMap (algebraMap X.K (DualNumber X.K)) := m'c.lift_snd _ _ _
    let u₀ : epsAt (under X.y) ⟶ Xo.univ.t.G := Over.homMk (r₀ ≫ X.m.φ) (by
      show (r₀ ≫ X.m.φ) ≫ Xo.univ.t.G.hom = spMap (algebraMap X.K (DualNumber X.K)) ≫ under X.y
      rw [Category.assoc, mc.w, ← Category.assoc, hr₀'])
    refine ⟨u₀, ⟨r₀, rfl, hr₀⟩, ?_⟩
    rintro u ⟨r, hr1, hr2⟩
    have e : r = r₀ := m'c.hom_ext (hr2.trans hr₀.symm) ((hbase r hr2).trans hr₀'.symm)
    apply Over.OverMorphism.ext
    rw [← hr1, e]
    rfl
  · rintro u ⟨r, hr1, hr2⟩
    have hrb := hbase r hr2
    refine ⟨?_, ?_⟩
    ·
      have hs : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom X.K X.K X.K).toRingHom) ≫ r = η[X.t.G].left := by
        refine m'c.hom_ext ?_ ?_
        · rw [Category.assoc, hr2, GlobalTheory.UU.eSec_comp_of_isGrpPullback X.m'.cart]
          have ht : spMap (TrivSqZeroExt.fstHom (𝓞 X.K) (𝓞 X.K) (𝓞 X.K)).toRingHom ≫ (X.C b).v.left =
              η[(X.C b).P.A].left := (X.C b).basis.1 0
          have hmon : η[(X.C b).P.A].left ≫ (X.ψ b a).left = η[X.B.t.G].left := by
            have := ((X.fam b).1 a).isMonHom
            exact congrArg CommaMorphism.left (IsMonHom.one_hom (f := X.ψ b a))
          rw [← Category.assoc, spMap_comp_spMap_sesquilinear_fractions, fstHom_comp_dualMap', ← spMap_comp_spMap_sesquilinear_fractions, Category.assoc,
            reassoc_of% ht, hmon]
        · rw [Category.assoc, hrb]
          show spMap (TrivSqZeroExt.fstHom X.K X.K X.K).toRingHom ≫ spMap (algebraMap X.K (DualNumber X.K)) = _
          rw [spMap_comp_spMap_sesquilinear_fractions, fst_comp_algebraMap_dual, Over.w η[X.t.G]]
          exact Spec.map_id _
      show Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom X.K X.K X.K).toRingHom) ≫ u.left = _
      rw [← hr1, ← Category.assoc, hs, GlobalTheory.UU.eSec_comp_of_isGrpPullback X.m.cart, Hom.one_def]
      rfl
    ·
      have hπ : X.π b ≫ (X.C b).P.A.hom = (Z b).C'.P.A.hom ≫ spMap ((algebraMap X.K ℂ).comp φ) :=
        (X.map' b).2.1.2.1.1.w
      have hvo : (Z b).C'.v.left ≫ X.π b =
          spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR ((algebraMap X.K ℂ).comp φ)) ≫ (X.C b).v.left := (X.map' b).2.2.1
      have hw0 : (X.π b ≫ (X.ψ b a).left) ≫ X.B.t.G.hom =
          ((Z b).C'.P.A.hom ≫ spMap (algebraMap X.K ℂ)) ≫ spMap φ := by
        rw [Category.assoc, hψ, hπ, Category.assoc, spMap_comp_spMap_sesquilinear_fractions]
      let Φ₀ := m'c.lift (X.π b ≫ (X.ψ b a).left) ((Z b).C'.P.A.hom ≫ spMap (algebraMap X.K ℂ)) hw0
      have hΦ₁ : Φ₀ ≫ X.m'.φ = X.π b ≫ (X.ψ b a).left := m'c.lift_fst _ _ _
      have hΦ₂ : Φ₀ ≫ X.t.G.hom = (Z b).C'.P.A.hom ≫ spMap (algebraMap X.K ℂ) := m'c.lift_snd _ _ _
      have claim1 : ∀ s : ℂ, ((Z b).u.ex (fun _ => (Z b).c * s)).left ≫ Φ₀ ≫ X.m.φ = (FU.ex i P (s • P a)).left := by
        intro s
        have hx1 : (((Z b).u.ex (fun _ => (Z b).c * s)).left ≫ Φ₀) ≫ X.t.G.hom = spMap (algebraMap X.K ℂ) := by
          rw [Category.assoc, hΦ₂, ← Category.assoc, Over.w ((Z b).u.ex (fun _ => (Z b).c * s))]
          exact Category.id_comp _
        have hx2 : (((Z b).u.ex (fun _ => (Z b).c * s)).left ≫ Φ₀) ≫ X.m'.φ =
            ((Z b).u.ex (fun _ => (Z b).c * s)).left ≫ X.π b ≫ (X.ψ b a).left := by
          rw [Category.assoc, hΦ₁]
        rw [← Category.assoc]
        exact X.tie b a s _ hx1 hx2
      have claim2 : spMap (dualMap (algebraMap X.K ℂ)) ≫ u.left = (Z b).C'.v.left ≫ Φ₀ ≫ X.m.φ := by
        have key : spMap (dualMap (algebraMap X.K ℂ)) ≫ r = (Z b).C'.v.left ≫ Φ₀ := by
          refine m'c.hom_ext ?_ ?_
          · rw [Category.assoc, hr2, Category.assoc, hΦ₁, reassoc_of% hvo, ← dualMap_eq_dualMapR', ← Category.assoc,
              spMap_comp_spMap_sesquilinear_fractions, dualMap_comp_dualMap_ring]
          · rw [Category.assoc, hrb, Category.assoc, hΦ₂, ← Category.assoc, Over.w (Z b).C'.v, spMap_comp_spMap_sesquilinear_fractions,
              dualMap_comp_algebraMap_sesquilinear_fractions, ← spMap_comp_spMap_sesquilinear_fractions]
            rfl
        rw [← hr1, ← Category.assoc, key, Category.assoc]
      have hline := GlobalTheory.CMPeriodCompare.isDerivAt0_line (φ := 𝟙 (Z b).C'.P.A.left) (t := (Z b).C'.v) (Z b).u ((Z b).C'.basis.1 0) (Z b).diff
      have h2 := ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows.isDerivAt0_comp_hom hline (Φ₀ ≫ X.m.φ)
      have hfun : (fun z : Fin 1 → ℂ => (((Z b).u.ex (z 0 • fun _ => (Z b).c * (Z b).z)).left ≫ 𝟙 _) ≫ Φ₀ ≫ X.m.φ) =
          fun z => (FU.ex i P ((z 0 * (Z b).z) • P a)).left := by
        funext z
        have e : (z 0 • fun _ => (Z b).c * (Z b).z) = (fun _ : Fin (Z b).C'.P.g => (Z b).c * (z 0 * (Z b).z)) := by
          funext k; simp only [Pi.smul_apply, smul_eq_mul]; ring
        rw [Category.comp_id, e, claim1]
      rw [hfun, Category.comp_id, ← claim2] at h2
      let Dl : (Fin 1 → ℂ) →ₗ[ℂ] (Fin g → ℂ) := (LinearMap.proj (0 : Fin 1) : (Fin 1 → ℂ) →ₗ[ℂ] ℂ).smulRight ((Z b).z • P a)
      have hhol : IsHolTo Set.univ (fun z => (FU.ex i P z).left) := by
        intro U f
        obtain ⟨h1, h2⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.anHol FU i P hP U f
        simp only [Set.mem_univ, true_and]
        exact ⟨h1, h2⟩
      have hDl : Dl (fun _ => 1) = (Z b).z • P a := by simp [Dl]
      have hDz : ∀ z, Dl z = (z 0 * (Z b).z) • P a := fun z => by simp [Dl, smul_smul]
      obtain ⟨v₀, hv₀, -⟩ := (FU.ex_diff i P hP).1 ((Z b).z • P a)
      have h3 := GlobalTheory.CMPeriodCompare.isDerivAt0_comp_linear hhol Dl (w := fun _ => 1) (v := v₀.left) (by rw [hDl]; exact hv₀)
      have h3' : IsDerivAt0 (fun z : Fin 1 → ℂ => (FU.ex i P ((z 0 * (Z b).z) • P a)).left) (fun _ => 1) v₀.left := by
        have e : (fun z => (FU.ex i P (Dl z)).left) =
            fun z : Fin 1 → ℂ => (FU.ex i P ((z 0 * (Z b).z) • P a)).left := funext fun z => by
          rw [hDz]
        rw [← e]; exact h3
      rw [ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows.isDerivAt0_unique h2 h3']
      exact hv₀

end PositivityTheory.Xgf
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexConjugate ComplexOrder

noncomputable section

namespace PositivityTheory.Xgf.DPer

open scoped Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {g : ℕ} {ty : Fin g → (E →+* ℂ)} {p q : ℕ} (hty : IsTypeFn H p q ty)
variable (G : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) E)

theorem Hm_herm (hskew : ∀ m m', G m' m = -IsCMField.complexConj E (G m m')) : (Hm hty G).IsHermitian := by
  ext k k'
  simp only [Matrix.conjTranspose_apply, Hm, Matrix.of_apply]
  by_cases h : ty k = ty k'
  · rw [if_pos h.symm, if_pos h, hskew (blk hty k) (blk hty k'), map_neg,
      IsCMField.complexEmbedding_complexConj, h]
    simp [Complex.conj_I]
  · rw [if_neg (Ne.symm h), if_neg h, star_zero]

private theorem re_star_dotProduct_mulVec_pos_of_posDef {n : ℕ} (N : Matrix (Fin n) (Fin n) ℂ) (hN : N.PosDef) (x : Fin n → ℂ) :
    0 ≤ (star x ⬝ᵥ N *ᵥ x).re ∧ (x ≠ 0 → 0 < (star x ⬝ᵥ N *ᵥ x).re) :=
  ⟨(Complex.nonneg_iff.mp (hN.posSemidef.dotProduct_mulVec_nonneg x)).1,
    fun hx => (Complex.pos_iff.mp (hN.dotProduct_mulVec_pos hx)).1⟩

theorem Q_re_inl (σ : E →+* ℂ) (h : σ (H.rt : E) = H.rt0)
    (hG1 : (Matrix.of fun a b : Fin p => Complex.I * σ (G (.inl a) (.inl b))).PosDef) (z : Fin g → ℂ) :
    0 ≤ (Q hty G σ z z).re ∧ ((∃ a, z ((eP hty σ h).symm a) ≠ 0) → 0 < (Q hty G σ z z).re) := by
  set x : Fin p → ℂ := fun a => star (z ((eP hty σ h).symm a)) with hx
  have hQ : Q hty G σ z z =
      2 * (star x ⬝ᵥ (Matrix.of fun a b : Fin p => Complex.I * σ (G (.inl a) (.inl b))) *ᵥ x) := by
    rw [Q_inl hty G σ h]
    simp only [hx, dotProduct, mulVec, Matrix.of_apply, Finset.mul_sum, Pi.star_apply, star_star,
      Complex.star_def, Complex.conj_conj]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  obtain ⟨h0, h1⟩ := re_star_dotProduct_mulVec_pos_of_posDef _ hG1 x
  have hre : (Q hty G σ z z).re = 2 * (star x ⬝ᵥ (Matrix.of fun a b : Fin p =>
      Complex.I * σ (G (.inl a) (.inl b))) *ᵥ x).re := by
    rw [hQ, Complex.mul_re]
    norm_num
  rw [hre]
  refine ⟨by positivity, fun ⟨a, ha⟩ => ?_⟩
  have hx0 : x ≠ 0 := fun h0' => ha (by simpa [hx] using congrFun h0' a)
  have := h1 hx0
  positivity

theorem Q_re_inr (σ : E →+* ℂ) (h : σ (H.rt : E) ≠ H.rt0)
    (hG2 : (-(Matrix.of fun a b : Fin q => Complex.I * ComplexEmbedding.conjugate σ (G (.inr a) (.inr b)))).PosDef)
    (z : Fin g → ℂ) :
    0 ≤ (Q hty G σ z z).re ∧ ((∃ a, z ((eQ hty σ h).symm a) ≠ 0) → 0 < (Q hty G σ z z).re) := by
  set x : Fin q → ℂ := fun a => z ((eQ hty σ h).symm a) with hx
  set M : Matrix (Fin q) (Fin q) ℂ :=
    -(Matrix.of fun a b : Fin q => Complex.I * ComplexEmbedding.conjugate σ (G (.inr a) (.inr b))) with hM
  have hQ : Q hty G σ z z = 2 * starRingEnd ℂ (star x ⬝ᵥ M *ᵥ x) := by
    rw [Q_inr hty G σ h]

    simp only [hx, hM, dotProduct, mulVec, Matrix.neg_apply, Matrix.of_apply, Finset.mul_sum, map_sum,
    map_mul, map_neg, Pi.star_apply, Complex.star_def, Complex.conj_conj, Complex.conj_I,
    ComplexEmbedding.conjugate_coe_eq]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  obtain ⟨h0, h1⟩ := re_star_dotProduct_mulVec_pos_of_posDef _ hG2 x
  have hre : (Q hty G σ z z).re = 2 * (star x ⬝ᵥ M *ᵥ x).re := by
    rw [hQ, Complex.mul_re, Complex.conj_re, Complex.conj_im]
    norm_num
  rw [hre]
  refine ⟨by positivity, fun ⟨a, ha⟩ => ?_⟩
  have hx0 : x ≠ 0 := fun h0' => ha (by simpa [hx] using congrFun h0' a)
  have := h1 hx0
  positivity

theorem Hm_pos
    (hG1 : ∀ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 →
      (Matrix.of fun a b : Fin p => Complex.I * τ (G (.inl a) (.inl b))).PosDef)
    (hG2 : ∀ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 →
      (-(Matrix.of fun a b : Fin q => Complex.I * τ (G (.inr a) (.inr b)))).PosDef)
    (z : Fin g → ℂ) (hz : z ≠ 0) : 0 < (hermForm (Hm hty G) z z).re := by
  rw [herm_split, Complex.re_sum]
  have hQ : ∀ σ : E →+* ℂ, 0 ≤ (Q hty G σ z z).re ∧
      ((∃ k, ty k = σ ∧ z k ≠ 0) → 0 < (Q hty G σ z z).re) := by
    intro σ
    by_cases h : σ (H.rt : E) = H.rt0
    · obtain ⟨h1, h2⟩ := Q_re_inl hty G σ h (hG1 σ h) z
      refine ⟨h1, fun ⟨k, hk, hz⟩ => h2 ⟨eP hty σ h ⟨k, hk⟩, by simpa using hz⟩⟩
    · have hc : ComplexEmbedding.conjugate σ (H.rt : E) = H.rt0 := (conjugate_rt σ).2 h
      obtain ⟨h1, h2⟩ := Q_re_inr hty G σ h (hG2 _ hc) z
      refine ⟨h1, fun ⟨k, hk, hz⟩ => h2 ⟨eQ hty σ h ⟨k, hk⟩, by simpa using hz⟩⟩
  obtain ⟨k0, hk0⟩ : ∃ k, z k ≠ 0 := by
    by_contra hc; push Not at hc; exact hz (funext hc)
  exact Finset.sum_pos' (fun σ _ => (hQ σ).1) ⟨ty k0, Finset.mem_univ _, (hQ (ty k0)).2 ⟨k0, rfl, hk0⟩⟩

end PositivityTheory.Xgf.DPer

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexConjugate

noncomputable section

namespace PositivityTheory.Xgf.DPer

open scoped Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem trace_sum (A : E) : (((Algebra.trace ℚ E A : ℚ) : ℝ) : ℂ) = ∑ σ : E →+* ℂ, σ A := by
  rw [Complex.ofReal_ratCast,
    show ((Algebra.trace ℚ E A : ℚ) : ℂ) = algebraMap ℚ ℂ (Algebra.trace ℚ E A) from (eq_ratCast _ _).symm,
    trace_eq_sum_embeddings]
  exact Fintype.sum_equiv (RingHom.equivRatAlgHom (R := E) (S := ℂ)).symm _ _ (fun σ => rfl)

theorem trace_re (A : E) : ((Algebra.trace ℚ E A : ℚ) : ℝ) =
    ∑ σ ∈ Finset.univ.filter (fun σ : E →+* ℂ => σ (H.rt : E) = H.rt0), 2 * (σ A).re := by
  have h1 := congrArg Complex.re (trace_sum A)
  rw [Complex.ofReal_re, Complex.re_sum, sum_split (H := H)] at h1
  rw [h1, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [ComplexEmbedding.conjugate_coe_eq, Complex.conj_re]
  ring

variable {g : ℕ} {ty : Fin g → (E →+* ℂ)} {p q : ℕ} (hty : IsTypeFn H p q ty)
variable (G : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) E)
variable {D : Datum H} (c : D.La →ₗ[𝓞 E] (Fin p ⊕ Fin q →₀ 𝓞 E)) (n : ℕ)

theorem per_at_inl (σ : E →+* ℂ) (h : σ (H.rt : E) = H.rt0) (y : D.La) (a : Fin p) :
    per hty c n y ((eP hty σ h).symm a).1 = σ ((c y (.inl a) : 𝓞 E) : E) / n := by
  rw [per_apply, blk_inl hty σ h _ ((eP hty σ h).symm a).2, ((eP hty σ h).symm a).2]
  simp

theorem per_at_inr (σ : E →+* ℂ) (h : σ (H.rt : E) ≠ H.rt0) (y : D.La) (a : Fin q) :
    per hty c n y ((eQ hty σ h).symm a).1 = σ ((c y (.inr a) : 𝓞 E) : E) / n := by
  rw [per_apply, blk_inr hty σ h _ ((eQ hty σ h).symm a).2, ((eQ hty σ h).symm a).2]
  simp

def blkA (y y' : D.La) : E := ∑ a : Fin p, ∑ b : Fin p,
  ((c y (.inl a) : 𝓞 E) : E) * G (.inl a) (.inl b) * IsCMField.complexConj E ((c y' (.inl b) : 𝓞 E) : E)

def blkB (y y' : D.La) : E := ∑ a : Fin q, ∑ b : Fin q,
  ((c y (.inr a) : 𝓞 E) : E) * G (.inr a) (.inr b) * IsCMField.complexConj E ((c y' (.inr b) : 𝓞 E) : E)

theorem Q_per_inl (σ : E →+* ℂ) (h : σ (H.rt : E) = H.rt0) (y y' : D.La) :
    Q hty G σ (per hty c n y) (per hty c n y') = Complex.I * (2 * σ (blkA G c y y') / ((n : ℂ) * n)) := by
  rw [Q_inl hty G σ h]

  simp only [per_at_inl, blkA, map_sum, map_mul, IsCMField.complexEmbedding_complexConj, map_div₀, map_natCast,
  Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem Q_per_inr (σ : E →+* ℂ) (h : σ (H.rt : E) ≠ H.rt0) (y y' : D.La) :
    Q hty G σ (per hty c n y) (per hty c n y') = Complex.I * (2 * σ (blkB G c y y') / ((n : ℂ) * n)) := by
  rw [Q_inr hty G σ h]

  simp only [per_at_inr, blkB, map_sum, map_mul, IsCMField.complexEmbedding_complexConj, map_div₀, map_natCast,
  Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem im_I_mul_div_sq (z : ℂ) (n : ℕ) : (Complex.I * (2 * z / ((n : ℂ) * n))).im = 2 * z.re / ((n : ℝ) * n) := by
  have e : (2 * z / ((n : ℂ) * n)) = ((2 / ((n : ℝ) * n) : ℝ) : ℂ) * z := by push_cast; ring
  rw [e, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.re_ofReal_mul]
  ring

theorem herm_im (y y' : D.La) :
    (hermForm (Hm hty G) (per hty c n y) (per hty c n y')).im =
      ((Algebra.trace ℚ E (blkA G c y y' + blkB G c y y') : ℚ) : ℝ) / ((n : ℝ) * n) := by
  rw [herm_split, Complex.im_sum, sum_split (H := H), ← Finset.sum_add_distrib, trace_re (H := H),
    Finset.sum_div]
  refine Finset.sum_congr rfl fun σ hσ => ?_
  have h : σ (H.rt : E) = H.rt0 := (Finset.mem_filter.mp hσ).2
  have h' : ComplexEmbedding.conjugate σ (H.rt : E) ≠ H.rt0 := fun hc => (conjugate_rt σ).mp hc h
  rw [Q_per_inl hty G c n σ h, Q_per_inr hty G c n _ h', im_I_mul_div_sq, im_I_mul_div_sq,
    ComplexEmbedding.conjugate_coe_eq, Complex.conj_re, map_add, Complex.add_re]
  ring

theorem sesq_blocks (x : Fin p ⊕ Fin q → D.La) (hc : ∀ y, ∑ m, c y m • x m = n • y)
    (horth : ∀ a b, sesq D (x (.inl a)) (x (.inr b)) = 0) (y y' : D.La) :
    blkA (gramE D x) c y y' + blkB (gramE D x) c y y' = (n : E) * n * sesq D y y' := by
  obtain ⟨-, hl, hr, hsl, hsr, hsk, -⟩ := sesq_sesquilinear_properties D
  let L : D.La → D.La →+ E := fun y' => AddMonoidHom.mk' (fun u => sesq D u y') (fun a b => hl a b y')
  let R : D.La → D.La →+ E := fun u => AddMonoidHom.mk' (fun v => sesq D u v) (fun a b => hr u a b)
  have key : sesq D (n • y) (n • y') = (n : E) * n * sesq D y y' := by
    have e1 : sesq D (n • y) (n • y') = n • sesq D y (n • y') := map_nsmul (L (n • y')) n y
    have e2 : sesq D y (n • y') = n • sesq D y y' := map_nsmul (R y) n y'
    rw [e1, e2, nsmul_eq_mul, nsmul_eq_mul]
    ring
  rw [← key, ← hc y, ← hc y']
  have e3 : sesq D (∑ m, c y m • x m) (∑ m, c y' m • x m) = ∑ m, ∑ m', ((c y m : 𝓞 E) : E) *
      sesq D (x m) (x m') * IsCMField.complexConj E ((c y' m' : 𝓞 E) : E) := by

    rw [show sesq D (∑ m, c y m • x m) (∑ m, c y' m • x m) =
    L (∑ m, c y' m • x m) (∑ m, c y m • x m) from rfl, map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_

    rw [show L (∑ m, c y' m • x m) (c y m • x m) = sesq D (c y m • x m) (∑ m, c y' m • x m) from rfl,
    hsl, show sesq D (x m) (∑ m', c y' m' • x m') = R (x m) (∑ m', c y' m' • x m') from rfl,
    map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m' _ => ?_
    rw [show R (x m) (c y' m' • x m') = sesq D (x m) (c y' m' • x m') from rfl, hsr]
    ring
  have horth' : ∀ a b, sesq D (x (.inr b)) (x (.inl a)) = 0 := fun a b => by
    rw [hsk, horth, map_zero, neg_zero]
  rw [e3]
  simp only [Fintype.sum_sum_type, blkA, blkB, gramE, Matrix.of_apply, horth, horth', mul_zero,
    zero_mul, Finset.sum_const_zero, add_zero, zero_add]

theorem herm_EF (hn : 0 < n) (x : Fin p ⊕ Fin q → D.La) (hc : ∀ y, ∑ m, c y m • x m = n • y)
    (horth : ∀ a b, sesq D (x (.inl a)) (x (.inr b)) = 0) (y y' : D.La) :
    (hermForm (Hm hty (gramE D x)) (per hty c n y) (per hty c n y')).im = D.EF y y' := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have h1 := trace_mul_sesq_eq_form D 1 y y'
  rw [one_smul, show ((1 : 𝓞 E) : E) = 1 by simp, _root_.one_mul] at h1
  have ht : Algebra.trace ℚ E ((n : E) * n * sesq D y y') = ((n * n : ℕ) : ℚ) * (D.EF y y' : ℚ) := by
    rw [show (n : E) * n * sesq D y y' = (n * n : ℕ) • sesq D y y' by rw [nsmul_eq_mul]; push_cast; ring,
      map_nsmul, h1, nsmul_eq_mul]
  rw [herm_im, sesq_blocks c n x hc horth, ht]
  push_cast
  field_simp

end PositivityTheory.Xgf.DPer

end
end
