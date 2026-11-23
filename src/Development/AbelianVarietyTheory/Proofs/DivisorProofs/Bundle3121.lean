module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2838
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsClopenLocusTorsionSectionsHeckeKernel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3075
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3071
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3070
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle031
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle077
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2849
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.WeilIsGrpPullbackIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2961
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBiextensionExpansionGeneratorOfTauBimult
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2962
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2963
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2964
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2965
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle126
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2854
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle075
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsFinsetRepresentatives
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TorsionEqOneOfTranslationKeepsRatios
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SymmetricLiftOddOrderExistsUnique
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle060
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2796
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle127
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PowEqOneOfPush
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkUInvariantUnderFieldEmbedding
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnivIdentity
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2896
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle777
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CrossRelationGivesConvolutionRelation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3056
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.HTSympCover

noncomputable section

namespace GlobalTheory.HTSympRep

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R]

def PtC {b : Base D R} {N : ℕ} {S : Scheme.{0}} {t : S ⟶ Sp R} (o : Obj b N t) (h M : ℕ) (k : Type) [Field k]
    (y : Sp k ⟶ S) (z : kˣ) (f : (Fin h ⊕ Fin h → ℤ) → (Over.mk y ⟶ o.A)) : Prop :=
  (∀ a, f a = 1 ↔ ∃ c, a = M • c) ∧ (∀ g : Over.mk y ⟶ o.A, g ^ M = 1 → ∃ a, f a = g) ∧
    ∀ a c, Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) M (f a) (f c) (unitOn (z ^ (2 * omegaStd a c)))

theorem ptC_congr {b : Base D R} {N : ℕ} {S : Scheme.{0}} {t : S ⟶ Sp R} (o : Obj b N t) (h M : ℕ) (k : Type)
    [Field k] (z : kˣ) {y y' : Sp k ⟶ S} (hy : y = y') (f : (Fin h ⊕ Fin h → ℤ) → (Over.mk y ⟶ o.A))
    (f' : (Fin h ⊕ Fin h → ℤ) → (Over.mk y' ⟶ o.A)) (hf : ∀ a, (f a).left = (f' a).left) :
    PtC o h M k y z f ↔ PtC o h M k y' z f' := by
  subst hy
  obtain rfl : f = f' := funext fun a => Over.OverMorphism.ext (hf a)
  rfl

theorem lemCyc : ∀ (M : ℕ) (S : Scheme.{0}), 0 < M → IsUnit (M : Γ(S, ⊤)) → ∃ (S' : Over S) (t₀ : S'.left ⟶ Sp (cycAway M)), IsFinite S'.hom ∧ Etale S'.hom ∧ ∀ (T : Scheme.{0}) (f : T ⟶ S) (t₁ : T ⟶ Sp (cycAway M)), ∃! g : T ⟶ S'.left, g ≫ S'.hom = f ∧ g ≫ t₀ = t₁ := GlobalTheory.T.exists_cyclotomicAway_finiteEtale_cover

theorem lemKer : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G], IsAbelianScheme G → ∀ (M h : ℕ), 0 < M → IsUnit (M : Γ(S, ⊤)) → ∀ (Z : Over S) (e : (Fin h ⊕ Fin h → ℤ) → (Z ⟶ G)), (∀ a c, e (a + c) = e a * e c) → (∀ a, e a ^ M = 1) → GlobalTheory.HkClopen.Loc (S := Z.left) (fun k _ _ x => ∀ a, (Over.homMk x rfl : Over.mk (x ≫ Z.hom) ⟶ Z) ≫ e a = 1 ↔ ∃ c, a = M • c) := GlobalTheory.T.torsionFamily_kernel_exact_isClopen_geometric

theorem lemOnto : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N h M : ℕ), 0 < M → M.Coprime p → ∀ (S : Scheme.{0}) (t : S ⟶ Sp R) (o : Obj b N t) (k : Type) [Field k] [IsAlgClosed k] (y : Sp k ⟶ S) (e : (Fin h ⊕ Fin h → ℤ) → (Over.mk y ⟶ o.A)), (∀ a c, e (a + c) = e a * e c) → (∀ a, e a ^ M = 1) → (∀ a, e a = 1 ↔ ∃ c, a = M • c) → ((∀ g : Over.mk y ⟶ o.A, g ^ M = 1 → ∃ a, e a = g) ↔ (M = 1 ∨ 2 * h = Module.finrank ℤ D.La)) := GlobalTheory.T.torsionFamily_surjective_iff_geometricPoint

theorem lemWeil : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N h M : ℕ), 0 < M → M.Coprime p → ∀ (S : Scheme.{0}) (t : S ⟶ Sp R) (o : Obj b N t) (Z : Over S) (t₁ : Z.left ⟶ Sp (cycAway M)) (e : (Fin h ⊕ Fin h → ℤ) → (Z ⟶ o.A)), (∀ a c, e (a + c) = e a * e c) → (∀ a, e a ^ M = 1) → GlobalTheory.HkClopen.Loc (S := Z.left) (fun k _ _ x => ∀ (β : cycAway M →+* k) (z : kˣ), x ≫ t₁ = spMap β → (z : k) = β (zetaAway M) → ∀ a c, Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) M ((Over.homMk x rfl : Over.mk (x ≫ Z.hom) ⟶ Z) ≫ e a) ((Over.homMk x rfl : Over.mk (x ≫ Z.hom) ⟶ Z) ≫ e c) (unitOn (z ^ (2 * omegaStd a c)))) := GlobalTheory.T.weilPairing_condition_locus_isClopen

theorem exists_sympLevScheme : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N h M : ℕ), 0 < M →
  M.Coprime p → ∀ (S : Scheme.{0}) (t : S ⟶ Sp R) (o : Obj b N t),
    ∃ (Y : Over S) (t₁ : Y.left ⟶ Sp (cycAway M)) (lu : (Fin h ⊕ Fin h → ℤ) → (Y ⟶ o.A)),
      IsFinite Y.hom ∧ Etale Y.hom ∧
      ∀ (T : Over S) (t₁' : T.left ⟶ Sp (cycAway M)) (lv : (Fin h ⊕ Fin h → ℤ) → (T ⟶ o.A)),
        (SympCond o h M T t₁' lv → ∃! f : T ⟶ Y, f.left ≫ t₁ = t₁' ∧ ∀ a, f ≫ lu a = lv a) ∧
        ((∃ f : T ⟶ Y, f.left ≫ t₁ = t₁' ∧ ∀ a, f ≫ lu a = lv a) → SympCond o h M T t₁' lv) := by
  intro p _ D R _ b N h M hM hcop S t o
  have hM0 : M ≠ 0 := hM.ne'
  have hMS : IsUnit (M : Γ(S, ⊤)) := by
    have := (b.unit M hcop).map (GlobalTheory.LevCover.fnOn t)
    rwa [map_natCast] at this
  obtain ⟨Z, et, hfin, het, eadd, epow, huniv⟩ :=
    GlobalTheory.exists_finiteEtale_latticeTorsionHom S o.A M (Fin h ⊕ Fin h → ℤ) o.ab hMS
  haveI := hfin
  haveI := het
  obtain ⟨S', t₀, hS1, hS2, hSu⟩ := lemCyc M S hM hMS
  haveI := hS1
  haveI := hS2
  obtain ⟨hW1, hW2⟩ := GlobalTheory.LevCover.finiteEtale_tensor Z S'
  haveI := hW1
  haveI := hW2
  let W : Over S := Z ⊗ S'
  let e : (Fin h ⊕ Fin h → ℤ) → (W ⟶ o.A) := fun a => fst Z S' ≫ et a
  let τ : W.left ⟶ Sp (cycAway M) := (snd Z S').left ≫ t₀
  have eadd' : ∀ a c, e (a + c) = e a * e c := fun a c => by simp only [e, eadd, MonObj.comp_mul]
  have epow' : ∀ a, e a ^ M = 1 := fun a => by simp only [e]; rw [← MonObj.comp_pow, epow, MonObj.comp_one]
  let C : Prop := M = 1 ∨ 2 * h = Module.finrank ℤ D.La
  obtain ⟨Vs, hVs, HV⟩ := (lemKer S o.A o.ab M h hM hMS W e eadd' epow').and
    ((GlobalTheory.HkClopen.Loc.const (S := W.left) C).and (lemWeil p D R b N h M hM hcop S t o W τ e eadd' epow'))
  let U : W.left.Opens := ⟨Vs, hVs.isOpen⟩
  obtain ⟨Y, i, hY1, hY2, hmono, Hi⟩ := GlobalTheory.LevCover.exists_sub U hVs.isClosed
  have memIff : ∀ (T : Over S) (w : T ⟶ W) (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ T.left)
      (β : cycAway M →+* k) (z : kˣ), (x ≫ w.left) ≫ τ = spMap β → (z : k) = β (zetaAway M) →
      ((x ≫ w.left) (default : PrimeSpectrum k) ∈ Vs ↔
        PtC o h M k (x ≫ T.hom) z (fun a => (Over.homMk x rfl : Over.mk (x ≫ T.hom) ⟶ T) ≫ w ≫ e a)) := by
    intro T w k _ _ x β z hβ hz
    rw [HV k (x ≫ w.left), ← ptC_congr o h M k z (show (x ≫ w.left) ≫ W.hom = x ≫ T.hom by
      rw [Category.assoc, Over.w w]) (fun a => (Over.homMk (x ≫ w.left) rfl : Over.mk ((x ≫ w.left) ≫ W.hom) ⟶ W) ≫ e a)
      _ (fun a => by simp)]
    have ha : ∀ a c, (Over.homMk (x ≫ w.left) rfl : Over.mk ((x ≫ w.left) ≫ W.hom) ⟶ W) ≫ e (a + c) =
        ((Over.homMk (x ≫ w.left) rfl : Over.mk ((x ≫ w.left) ≫ W.hom) ⟶ W) ≫ e a) *
          ((Over.homMk (x ≫ w.left) rfl : Over.mk ((x ≫ w.left) ≫ W.hom) ⟶ W) ≫ e c) := fun a c => by
      rw [eadd', MonObj.comp_mul]
    have hp : ∀ a, ((Over.homMk (x ≫ w.left) rfl : Over.mk ((x ≫ w.left) ≫ W.hom) ⟶ W) ≫ e a) ^ M = 1 :=
      fun a => by rw [← MonObj.comp_pow, epow', MonObj.comp_one]
    constructor
    · rintro ⟨hk, hC, hw⟩
      exact ⟨hk, (lemOnto p D R b N h M hM hcop S t o k _ _ ha hp hk).2 hC, hw β z hβ hz⟩
    · rintro ⟨hk, ho, hw⟩
      refine ⟨hk, (lemOnto p D R b N h M hM hcop S t o k _ _ ha hp hk).1 ho, fun β' z' hβ' hz' => ?_⟩
      obtain rfl : β' = β := GlobalTheory.LevCover.spMap_inj' (hβ'.symm.trans hβ)
      obtain rfl : z' = z := Units.ext (hz'.trans hz.symm)
      exact hw
  have unitζ : ∀ (k : Type) [Field k] (β : cycAway M →+* k), IsUnit (β (zetaAway M)) := fun k _ β =>
    IsUnit.of_pow_eq_one (by rw [← map_pow, GlobalTheory.HTSympCover.zetaAway_pow_self M hM0, map_one]) hM0
  refine ⟨Y, i.left ≫ τ, fun a => i ≫ e a, hY1, hY2, fun T t₁' lv => ⟨fun hL => ?_, fun hex => ?_⟩⟩
  · obtain ⟨hadd, hpow, hgeo⟩ := hL
    obtain ⟨u, hu, huu⟩ := huniv T lv hadd hpow
    obtain ⟨g, ⟨hg1, hg2⟩, hgu⟩ := hSu T.left T.hom t₁'
    let v : T ⟶ S' := Over.homMk g hg1
    let w : T ⟶ W := lift u v
    have hwe : ∀ a, w ≫ e a = lv a := fun a => by
      simp only [w, e]
      rw [← Category.assoc, lift_fst, hu]
    have hwτ : w.left ≫ τ = t₁' := by
      simp only [τ]
      rw [← Category.assoc, ← Over.comp_left, lift_snd]
      exact hg2
    have hr : Set.range w.left ⊆ U := by
      rintro _ ⟨q, rfl⟩
      obtain ⟨k, _, _, x, hx⟩ := GlobalTheory.FinEt.exists_algClosed_point T.left q
      obtain ⟨β, hβ⟩ := GlobalTheory.LevCover.exists_spMap (x ≫ t₁')
      have hm : (x ≫ w.left) (default : PrimeSpectrum k) ∈ Vs := by
        refine (memIff T w k x β (unitζ k β).unit (by rw [Category.assoc, hwτ, hβ]) rfl).2 ?_
        have := hgeo k x β (unitζ k β).unit hβ rfl
        simp only [hwe]
        exact this
      have hp' : x (default : PrimeSpectrum k) = q := by
        have : x (default : PrimeSpectrum k) ∈ Set.range x := ⟨_, rfl⟩
        rwa [hx] at this
      exact (show (x ≫ w.left) (default : PrimeSpectrum k) = w.left q by rw [← hp']; rfl) ▸ hm
    obtain ⟨f, hf⟩ := (Hi T w).1 hr
    refine ⟨f, ⟨by rw [← Category.assoc, ← Over.comp_left, hf, hwτ], fun a => by
      rw [← Category.assoc, hf, hwe]⟩, fun f' ⟨hf'1, hf'2⟩ => ?_⟩
    have e1 : f' ≫ i ≫ fst Z S' = u := huu _ fun a => by
      have := hf'2 a
      simp only [e, Category.assoc] at this ⊢
      exact this
    have e2 : f' ≫ i ≫ snd Z S' = v := by
      apply Over.OverMorphism.ext
      refine hgu _ ⟨Over.w (f' ≫ i ≫ snd Z S'), ?_⟩
      rw [← hf'1]
      simp [τ]
    have e3 : f' ≫ i = w := by
      apply CartesianMonoidalCategory.hom_ext
      · rw [Category.assoc, e1]; exact (lift_fst u v).symm
      · rw [Category.assoc, e2]; exact (lift_snd u v).symm
    exact (cancel_mono i).1 (e3.trans hf.symm)
  · obtain ⟨f, hf1, hf2⟩ := hex
    have hlv : ∀ a, lv a = (f ≫ i) ≫ e a := fun a => by rw [Category.assoc]; exact (hf2 a).symm
    refine ⟨fun a c => by rw [hlv, hlv, hlv, eadd', MonObj.comp_mul],
      fun a => by rw [hlv, ← MonObj.comp_pow, epow', MonObj.comp_one], fun k _ _ x β z hx hz => ?_⟩
    have hr : Set.range (f ≫ i).left ⊆ U := (Hi T (f ≫ i)).2 ⟨f, rfl⟩
    have hm : (x ≫ (f ≫ i).left) (default : PrimeSpectrum k) ∈ Vs := hr ⟨x (default : PrimeSpectrum k), rfl⟩
    have hG := (memIff T (f ≫ i) k x β z (by rw [← hx, ← hf1]; simp) hz).1 hm
    simp only [← hlv] at hG
    exact hG

end GlobalTheory.HTSympRep
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

namespace GlobalTheory.Mum.Two.WeilCmp

variable {S : Scheme.{0}} (P₀ P₁ P₂ : PolAV S)

theorem cubN_cmp {T : Over S} (f₁ g₁ : P₀.A ⟶ P₁.A) (f₂ g₂ : P₀.A ⟶ P₂.A) [IsMonHom f₁] [IsMonHom g₁] [IsMonHom f₂]
    [IsMonHom g₂] {U : Type} [CommGroup U] (v : (T ⟶ P₀.A) → (T ⟶ P₀.A) → U)
    {θ₁ : (T ⟶ P₁.A) → (T ⟶ P₁.A) → (T ⟶ P₁.A) → U} {θ₂ : (T ⟶ P₂.A) → (T ⟶ P₂.A) → (T ⟶ P₂.A) → U}
    (h₁ : IsCub θ₁) (h₂ : IsCub θ₂)
    (a₁ : ∀ x x' y, v (x * x') y * θ₁ (x ≫ f₁) (x' ≫ f₁) (y ≫ g₁) =
      θ₂ (x ≫ f₂) (x' ≫ f₂) (y ≫ g₂) * (v x y * v x' y))
    (a₂ : ∀ x y y', v x (y * y') * θ₁ (x ≫ f₁) (y ≫ g₁) (y' ≫ g₁) =
      θ₂ (x ≫ f₂) (y ≫ g₂) (y' ≫ g₂) * (v x y * v x y'))
    {k : ℕ} {x y : T ⟶ P₀.A} (hx : x ^ k = 1) (hy : y ^ k = 1) :
    cubN θ₁ k 1 (x ≫ f₁) (y ≫ g₁) = cubN θ₂ k 1 (x ≫ f₂) (y ≫ g₂) * v x y ^ k ∧
      cubN θ₁ k 1 (y ≫ g₁) (x ≫ f₁) = cubN θ₂ k 1 (y ≫ g₂) (x ≫ f₂) * v x y ^ k := by
  have first : ∀ n : ℕ, v (x ^ n) y * cubN θ₁ n 1 (x ≫ f₁) (y ≫ g₁) =
      v 1 y * (cubN θ₂ n 1 (x ≫ f₂) (y ≫ g₂) * v x y ^ n) := fun n => by
    induction n with
    | zero => simp [cubN]
    | succ n ih =>
      have a := a₁ (x ^ n) x y
      rw [MonObj.pow_comp, MonObj.pow_comp] at a
      simp only [cubN, Finset.prod_range_succ, _root_.one_mul] at ih ⊢
      rw [pow_succ, pow_succ]
      apply Additive.ofMul.injective
      have a' := congrArg Additive.ofMul a
      have ih' := congrArg Additive.ofMul ih
      simp only [ofMul_mul] at a' ih' ⊢
      linear_combination (norm := abel) a' + ih'
  have second : ∀ n : ℕ, v x (y ^ n) * cubN θ₁ n 1 (y ≫ g₁) (x ≫ f₁) =
      v x 1 * (cubN θ₂ n 1 (y ≫ g₂) (x ≫ f₂) * v x y ^ n) := fun n => by
    induction n with
    | zero => simp [cubN]
    | succ n ih =>
      have a := a₂ x (y ^ n) y
      rw [MonObj.pow_comp, MonObj.pow_comp, h₁.s01 (x ≫ f₁), h₁.s12 _ (x ≫ f₁), h₂.s01 (x ≫ f₂),
        h₂.s12 _ (x ≫ f₂)] at a
      simp only [cubN, Finset.prod_range_succ, _root_.one_mul] at ih ⊢
      rw [pow_succ, pow_succ]
      apply Additive.ofMul.injective
      have a' := congrArg Additive.ofMul a
      have ih' := congrArg Additive.ofMul ih
      simp only [ofMul_mul] at a' ih' ⊢
      linear_combination (norm := abel) a' + ih'
  have a := first k
  have b := second k
  rw [hx] at a
  rw [hy] at b
  exact ⟨mul_left_cancel a, mul_left_cancel b⟩

theorem isRatio_cmp (hG : GlobalFnsSt) [Nonempty P₁.A.left] [Nonempty P₂.A.left] (f₁ g₁ : P₀.A ⟶ P₁.A)
    (f₂ g₂ : P₀.A ⟶ P₂.A) [IsMonHom f₁] [IsMonHom g₁] [IsMonHom f₂] [IsMonHom g₂]
    {r₁ : LB.Gen (P₁.L.pull (eSec P₁.A))} {hr₁ : r₁.IsGen} (c₁ : CubicalStr P₁.A ⟨P₁.L, r₁, P₁.isLB, hr₁⟩)
    {r₂ : LB.Gen (P₂.L.pull (eSec P₂.A))} {hr₂ : r₂.IsGen} (c₂ : CubicalStr P₂.A ⟨P₂.L, r₂, P₂.isLB, hr₂⟩)
    (u : LB.Gen (CmpL P₀ P₁ P₂ f₁ g₁ f₂ g₂)) (hu : u.IsGen)
    (hn : ∀ (Z : Scheme.{0}) (r : Z ⟶ S) (z : Z) (J), Good (join P₁.L P₂.L) z J → val u (r ≫ zero2 P₀.A) z J = 1)
    {T : Over S} {k : ℕ} {x y : T ⟶ P₀.A} (hx : x ^ k = 1) (hy : y ^ k = 1) {e : Γ(T.left, ⊤)ˣ}
    (he : WeilCube.IsRatio c₁ k (x ≫ f₁) (y ≫ g₁) e) : WeilCube.IsRatio c₂ k (x ≫ f₂) (y ≫ g₂) e := by
  intro T' ρ z J₂ hJ₂
  obtain ⟨J₁, hJ₁, -⟩ := exists_good P₁.L P₁.isLB z (K := PEmpty) PEmpty.elim PEmpty.elim (fun a => a.elim)
    (fun a => a.elim)
  obtain ⟨J, hJ, e₁, e₂⟩ := exists_good_join P₁.isLB P₂.isLB hJ₁ hJ₂
  have hx' : (ρ ≫ x) ^ k = 1 := by rw [← MonObj.comp_pow, hx, MonObj.comp_one]
  have hy' : (ρ ≫ y) ^ k = 1 := by rw [← MonObj.comp_pow, hy, MonObj.comp_one]
  have q₁ : Good P₁.L z (rl J) := (isPart_inl P₁.L P₂.L).good hJ
  have q₂ : Good P₂.L z (rr J) := (isPart_inr P₁.L P₂.L).good hJ
  obtain ⟨a, b⟩ := cubN_cmp P₀ P₁ P₂ f₁ g₁ f₂ g₂ (fun a b => val u (lift a b).left z J) (isCub_cubV c₁ q₁)
    (isCub_cubV c₂ q₂) (fun x x' y => GlobalTheory.T.weilComparisonGenerator_additive_first_variable hG S P₀ P₁ P₂ f₁ g₁ f₂ g₂ _ _ c₁ _ _ c₂ u hu hn T' z J hJ x x' y)
    (fun x y y' => GlobalTheory.T.weilComparisonGenerator_additive_second_variable hG S P₀ P₁ P₂ f₁ g₁ f₂ g₂ _ _ c₁ _ _ c₂ u hu hn T' z J hJ x y y') hx' hy'
  rw [e₁, e₂] at a b
  simp only [Category.assoc] at a b
  have h := he T' ρ z J₁ hJ₁
  rw [a, b, ← _root_.mul_assoc] at h
  exact mul_right_cancel h

end GlobalTheory.Mum.Two.WeilCmp


open GlobalTheory.Mum.Two.WeilCmp in
theorem GlobalTheory.Mum.Two.weilIs_iff_of_lbIso : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P₀ P₁ P₂ : PolAV S) (f₁ g₁ : P₀.A ⟶ P₁.A) (f₂ g₂ : P₀.A ⟶ P₂.A), IsMonHom f₁ → IsMonHom g₁ → IsMonHom f₂ → IsMonHom g₂ → LBIso (cubeLB P₁.A ![fst P₀.A P₀.A ≫ f₁, snd P₀.A P₀.A ≫ g₁] P₁.L) (cubeLB P₂.A ![fst P₀.A P₀.A ≫ f₂, snd P₀.A P₀.A ≫ g₂] P₂.L) → ∀ (F : Type) [Field F] (p : Sp F ⟶ S) (k : ℕ) (x y : Over.mk p ⟶ P₀.A), x ^ k = 1 → y ^ k = 1 → ∀ c, WeilIs P₁.A P₁.L k (x ≫ f₁) (y ≫ g₁) c ↔ WeilIs P₂.A P₂.L k (x ≫ f₂) (y ≫ g₂) c := by
  intro S _ P₀ P₁ P₂ f₁ g₁ f₂ g₂ _ _ _ _ hw F _ p k x y hx hy c
  have hL := GlobalTheory.allSixLaws.1
  haveI : Nonempty P₁.A.left := ⟨(x ≫ f₁).left (⊥ : PrimeSpectrum F)⟩
  haveI : Nonempty P₂.A.left := ⟨(x ≫ f₂).left (⊥ : PrimeSpectrum F)⟩
  obtain ⟨r₁, hr₁, ⟨c₁⟩⟩ := PolAV_exists_cubical hL.cube P₁
  obtain ⟨r₂, hr₂, ⟨c₂⟩⟩ := PolAV_exists_cubical hL.cube P₂
  obtain ⟨u₀, hu₀⟩ := GlobalTheory.T.exists_weilComparisonGenerator_of_lambdaBundleIso S P₀ P₁ P₂ f₁ g₁ f₂ g₂ hw
  obtain ⟨u, hu, hn⟩ := GlobalTheory.T.exists_weilComparisonGenerator_normalised_zeroSection S P₀ P₁ P₂ f₁ g₁ f₂ g₂ u₀ hu₀
  have hx₁ : (x ≫ f₁) ^ k = 1 := by rw [← MonObj.pow_comp, hx, MonObj.one_comp]
  have hy₁ : (y ≫ g₁) ^ k = 1 := by rw [← MonObj.pow_comp, hy, MonObj.one_comp]
  have hx₂ : (x ≫ f₂) ^ k = 1 := by rw [← MonObj.pow_comp, hx, MonObj.one_comp]
  have hy₂ : (y ≫ g₂) ^ k = 1 := by rw [← MonObj.pow_comp, hy, MonObj.one_comp]
  obtain ⟨e₀, he₀⟩ := WeilCube.exists_isRatio c₁ k (x ≫ f₁) (y ≫ g₁) hx₁ hy₁
  have he₂ := isRatio_cmp P₀ P₁ P₂ hL.globalFns f₁ g₁ f₂ g₂ c₁ c₂ u hu hn hx hy he₀
  exact (WeilCube.weilIs_iff c₁ hL.globalFns P₁.isAb hx₁ hy₁ he₀ c).trans
    (WeilCube.weilIs_iff c₂ hL.globalFns P₂.isAb hx₂ hy₂ he₂ c).symm
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.UpExt GlobalTheory.FieldBaseChange ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section
namespace GlobalTheory.Mum.UpAct
open GlobalTheory.UT GlobalTheory.ThetaScalar

variable {R : Type} [CommRing R] [IsDomain R] {E F : Type} [Field F] [Algebra (FractionRing R) F] [Field E]
  [Algebra (FractionRing R) E] [Algebra E F] [IsScalarTower (FractionRing R) E F]

theorem exists_frame_pull {D : DegPre R} {k : ℕ} {p : QkPt D E k} {p' : QkPt D F k}
    (h : QkExt (algebraMap E F) p p') {w : Frm D E k p.g.b} (hw : w.IsGen) :
    ∃ w' : Frm D F k p'.g.b, w'.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (TF (R := R) F).left) (z : Z) J, Good D.P.L z J →
      val w' r z J = val w (r ≫ (baseMap (R := R) E F).left) z J := by
  obtain ⟨hy, hb, hs⟩ := h
  have h0 : (baseMap (R := R) E F).left ≫ (DegPre.zeroF D E).left = (DegPre.zeroF D F).left :=
    congrArg (fun q : TF (R := R) F ⟶ D.P.A => q.left) (MonObj.comp_one (M := D.P.A) (baseMap (R := R) E F))
  obtain ⟨w', hw', hv⟩ := exists_gen D.P.isLB (φ' := DegPre.lineφ D F p'.g.b) (ε' := DegPre.lineε k)
    (fun U _ h => Finset.prod_congr rfl fun i _ => by
      fin_cases i
      · exact congrArg (fun q => h q ^ _) h0
      · exact congrArg (fun q => h q ^ _) hb.symm)
    (LB.pullGen D.P.L _ _ w (baseMap (R := R) E F).left) (pullGen_isGen _ _ _ _ hw _)
  exact ⟨w', hw', fun Z r z J hJ => (hv Z r z J hJ).trans (val_pull hJ _ _ _)⟩

theorem txFrame_pull {D : DegPre R} {k : ℕ} {p : QkPt D E k} {p' : QkPt D F k}
    (h : QkExt (algebraMap E F) p p') {w : Frm D E k p.g.b} (hw : TXFrame k p w) {w' : Frm D F k p'.g.b} (hw' : w'.IsGen)
    (hv : ∀ (Z : Scheme.{0}) (r : Z ⟶ (TF (R := R) F).left) (z : Z) J, Good D.P.L z J →
      val w' r z J = val w (r ≫ (baseMap (R := R) E F).left) z J) : TXFrame k p' w' := by
  obtain ⟨hy, hb, hs⟩ := h
  have hL := D.P.isLB
  have hb' : (𝟙 _ ≫ (baseMap (R := R) E F).left) ≫ p.g.b.left = p'.g.b.left := by
    rw [Category.id_comp]; exact hb.symm
  refine ⟨hw', fun ν hν z J hJ => ?_, fun κ hκ z J hJ => ?_⟩
  · have c : LB.Gen.Corr D.P.L _ _ _ _ (GeneratorPullback.powGen D.P.L _ _ w 2)
        (LB.mulGen D.P.L _ _ _ _ (p.g.s p.y) (LB.pullGen D.P.L _ _ ν p.g.b.left)) :=
      corr_of_val hL fun y I hI => (map_pow _ _ _).trans ((hw.2.1 ν hν y I hI).trans (by
        rw [val_mul hI, val_pull hI, Category.id_comp]))
    have e := val_corr hJ c (𝟙 _ ≫ (baseMap (R := R) E F).left)
    rw [val_mul hJ, val_pull hJ, hb'] at e
    rw [hv _ _ z J hJ, val_corr hJ (hs p'.y), val_pull hJ, hy]
    exact (map_pow _ _ _).symm.trans e
  · have c : LB.Gen.Corr D.P.L _ _ _ _
        (LB.mulGen D.P.L _ _ _ _ (GeneratorPullback.powGen D.P.L _ _ w k) (LB.pullGen D.P.L _ _ κ p.g.b.left))
        (LB.mulGen D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ (D.psi p.y) (jFK (R := R) E))
          (LB.pullGen D.P.L (fun _ : PUnit => eSec D.P.A) (fun _ => 1) D.rig (TF (R := R) E).hom)) :=
      corr_of_val hL fun y I hI => by
        rw [val_mul hI, val_mul hI, val_pull hI, val_pull hI, val_pull hI, Category.id_comp, Category.id_comp,
          Category.id_comp]
        exact (congrArg (· * _) (map_pow _ _ _)).trans (hw.2.2 κ hκ y I hI)
    have e := val_corr hJ c (𝟙 _ ≫ (baseMap (R := R) E F).left)
    have e₁ : (𝟙 _ ≫ (baseMap (R := R) E F).left) ≫ jFK (R := R) E = jFK (R := R) F := by
      rw [Category.id_comp]; exact specMap_jFK E F
    have e₂ : (𝟙 _ ≫ (baseMap (R := R) E F).left) ≫ (TF (R := R) E).hom = (TF (R := R) F).hom := by
      rw [Category.id_comp]; exact Over.w _
    rw [val_mul hJ, val_mul hJ, val_pull hJ, val_pull hJ, val_pull hJ, hb', e₁, e₂] at e
    rw [hv _ _ z J hJ, hy]
    exact (congrArg (· * _) (map_pow _ _ _)).symm.trans e

theorem phiVal_pull (hG : GlobalFnsSt) {D : DegPre R} {k : ℕ} {p : QkPt D E k} {p' : QkPt D F k}
    (h : QkExt (algebraMap E F) p p') {w : Frm D E k p.g.b} {w' : Frm D F k p'.g.b}
    (hv : ∀ (Z : Scheme.{0}) (r : Z ⟶ (TF (R := R) F).left) (z : Z) J, Good D.P.L z J →
      val w' r z J = val w (r ≫ (baseMap (R := R) E F).left) z J) (s t : Fam D E k) (H : PhiVal p w s.s t.s) :
    PhiVal p' w' (famPull D E F hG k s).s (famPull D E F hG k t).s := by
  obtain ⟨hy, hb, hs⟩ := h
  have hb' : p'.g.b = baseMap (R := R) E F ≫ p.g.b := Over.OverMorphism.ext hb
  intro α β hβ T ρ z J hJ
  have e₁ : DegPre.trPt D F p'.g.b ≫ famMap D E F = famMap D E F ≫ DegPre.trPt D E p.g.b := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, Category.assoc, famMap_fst, tr_fst, ← Category.assoc, tr_fst, famMap_fst]
    · refine ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (famMap_snd D E F)).trans (tr_pr D F _))).trans
        (Eq.symm ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (tr_pr D E _)).trans ?_)))
      rw [MonObj.comp_mul, famMap_snd, ← Category.assoc, famMap_fst, hb', Category.assoc]
  have e₂ : ((ρ ≫ famMap D E F) ≫ fst _ _).left = (ρ ≫ fst _ _).left ≫ (baseMap (R := R) E F).left := by
    rw [Category.assoc, famMap_fst, ← Category.assoc]; rfl
  have e₃ : uVal D E k α p.g.b (ρ ≫ famMap D E F) z J = uVal D F k α p'.g.b ρ z J := by
    have : famMap D E F ≫ fst _ _ ≫ p.g.b = fst _ _ ≫ p'.g.b := by
      rw [← Category.assoc, famMap_fst, hb', Category.assoc]
    simp only [uVal, Category.assoc, famMap_snd, this]
  refine (sval_pullOver _ _ _ _ hJ).trans ((H α β (hy ▸ hβ) T (ρ ≫ famMap D E F) z J hJ).trans
    (congrArg₂ (· * ·) (Eq.trans ?_ (sval_pullOver _ _ _ _ hJ).symm) (congrArg Units.val ?_)))
  · rw [Category.assoc, ← e₁, ← Category.assoc]; rfl
  · rw [e₃, val_mul hJ, val_mul hJ, hv _ _ z J hJ, val_corr hJ (hs α), val_pull hJ, e₂]
    rfl

theorem secMap_eq (A : PolAV (Sp (FractionRing R))) : secMap A E F = baseK (R := R) E F ▷ A.A := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [secMap_fst, whiskerRight_fst]
  · rw [secMap_snd, whiskerRight_snd]

theorem actVal_secPull {A : PolAV (Sp (FractionRing R))} {N : ℕ} (hN : Odd N) {x : TFK (R := R) E ⟶ A.A}
    {θ : ThetaGrp A.A A.L (N : ℤ) (TFK (R := R) E)} {θ' : ThetaGrp A.A A.L (N : ℤ) (TFK (R := R) F)}
    (H : SymLift A.A A.L N N x θ) (H' : SymLift A.A A.L N N (baseK (R := R) E F ≫ x) θ')
    {t u : SecF A E N} (h : ActVal θ t u) : ActVal θ' (UpExt.secPull A E F N t) (UpExt.secPull A E F N u) := by
  obtain ⟨ξ, Hξ, v⟩ := SymLiftGlobal.exists_symLift_pull_val A.isLB (baseK (R := R) E F) H
  have c := SymLiftOdd.symLift_unique GlobalTheory.globalFns_holds A.isAb A.isLB hN θ' ξ H' Hξ
  intro Z r z J hJ
  have h₂ : thetaVal θ' r z J = thetaVal θ (r ≫ (secMap A E F).left) z J := by
    rw [secMap_eq]; exact (val_corr hJ c _).trans (v _ _ z J hJ)
  refine (sval_pullOver _ _ _ _ hJ).trans ((h _ _ z J hJ).trans (congrArg₂ (· * ·)
    (congrArg Units.val h₂.symm) (Eq.trans ?_ (sval_pullOver _ _ _ _ hJ).symm)))
  have e : (translT A.A θ'.pt).left ≫ (secMap A E F).left = (secMap A E F).left ≫ (translT A.A θ.pt).left := by
    rw [H'.pt_eq, H.pt_eq, secMap_eq]
    exact congrArg (fun q => q.left) (CommPairing.whisker_translT (baseK (R := R) E F) x)
  rw [Category.assoc, Category.assoc, e]
  rfl

end GlobalTheory.Mum.UpAct


open GlobalTheory.Mum.UpAct GlobalTheory.UT GlobalTheory.ThetaScalar in
theorem GlobalTheory.Mum.UpAct.act_extension : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (N : ℕ), Odd N → ∀ (lab : QkPt D.toPre (Kb R) N → (TFK (R := R) (Kb R) ⟶ A.A)) (E₀ : Fam D.toPre (Kb R) N → SecK A.L (snd (TFK (R := R) (Kb R)) A.A).left N), Eqv D.toPre A (Kb R) N lab E₀ → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (Kb R) F] [IsScalarTower (FractionRing R) (Kb R) F] (lab' : QkPt D.toPre F N → (TFK (R := R) F ⟶ A.A)), LabExt (IsScalarTower.toAlgHom (FractionRing R) (Kb R) F) lab lab' → ∀ (E' : Fam D.toPre F N →ₗ[F] SecF A F N), (∀ s, E' (famPull D.toPre (Kb R) F GlobalTheory.globalFns_holds N s) = UpExt.secPull A (Kb R) F N (E₀ s)) → ∀ (p : QkPt D.toPre F N) w (θ : ThetaGrp A.A A.L (N : ℤ) (TFK (R := R) F)) (s s' : Fam D.toPre F N), GlobalTheory.UT.TXFrame N p w → SymLift A.A A.L N N (lab' p) θ → PhiRel D.toPre F N p w s s' → IsActOf A.A A.L N θ (E' s) (E' s') := by
  intro R _ _ _ hR D A N hN lab E₀ hE F _ _ _ _ _ lab' hlab E' hE' p w θ s s' hw hθ hs
  have : CharZero R := hR.2
  have hG := GlobalTheory.globalFns_holds
  obtain ⟨p₀, hp, -⟩ := (qkPt_algClosure_bijective R D.toPre F
    (IsScalarTower.toAlgHom (FractionRing R) (Kb R) F) N hN.pos).2 p
  have hx : lab' p = baseK (R := R) (Kb R) F ≫ lab p₀ := Over.OverMorphism.ext (hlab p₀ p hp)
  replace hp : QkExt (algebraMap (Kb R) F) p₀ p := hp
  obtain ⟨w₀, hw₀⟩ := hE.frame p₀
  obtain ⟨θ₀, hθ₀⟩ := hE.lift p₀
  obtain ⟨w', hw', hv'⟩ := exists_frame_pull hp hw₀.1
  have hu := (GlobalTheory.UT.SymFrame.main GlobalTheory.firstFiveLaws R _ hR.1 D F N hN p).2 w w' hw (txFrame_pull hp hw₀ hw' hv')
  have hv : ∀ (Z : Scheme.{0}) (r : Z ⟶ (TF (R := R) F).left) (z : Z) J, Good D.toPre.P.L z J →
      val w r z J = val w₀ (r ≫ (baseMap (R := R) (Kb R) F).left) z J := fun Z r z J hJ =>
    (val_corr hJ (corr_of_val D.toPre.P.isLB hu) r).trans (hv' Z r z J hJ)
  obtain ⟨Φ₀, hΦ₀⟩ := phiFun_of_globalFns hG R _ D (Kb R) N hN.pos p₀ w₀ hw₀.1
  obtain ⟨Φ, hΦ⟩ := phiFun_of_globalFns hG R _ D F N hN.pos p w hw.1
  obtain ⟨Θ, hΘ⟩ : ∃ Θ : SecF A F N →ₗ[F] SecF A F N, ∀ t, ActVal θ t (Θ t) := GlobalTheory.TorsionExt.exists_act θ
  rw [hx] at hθ
  have key : E' ∘ₗ Φ = Θ ∘ₗ E' := LinearMap.ext_on
    (isExtension_famPull D.toPre (Kb R) F GlobalTheory.globalFns_holds hN.pos).span (by
      rintro _ ⟨u, rfl⟩
      have r₀ : PhiRel D.toPre (Kb R) N p₀ w₀ u (Φ₀ u) := (hΦ₀ u _).2 rfl
      have r := (hΦ _ _).1 ((phiRel_iff hG p w hw.1 _ _).2
        (phiVal_pull GlobalTheory.globalFns_holds hp hv u _ ((phiRel_iff hG p₀ w₀ hw₀.1 _ _).1 r₀)))
      have a := actVal_secPull hN hθ₀ hθ (ThetaBaseChange.actVal_of_isActOf (hE.act p₀ w₀ θ₀ u _ hw₀ hθ₀ r₀))
      rw [LinearMap.comp_apply, LinearMap.comp_apply, ← r, hE', hE']
      exact GlobalTheory.TorsionExt.actVal_unique a (hΘ _))
  obtain rfl := (hΦ _ _).1 hs
  have e : E' (Φ s) = Θ (E' s) := LinearMap.congr_fun key s
  rw [e]
  exact (hΘ _).isActOf A.isLB
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.FieldBaseChange GlobalTheory.Mum.Two.Mix

theorem _root_.GlobalTheory.T.integral_relation_kills_mixed_section_sums_level : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D₁ D₂ : DegData R I) (A₁ A₂ : PolAV (Sp (FractionRing R))) (G₁ G₂ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂) (a : G₁ ⟶ G₂) (b : D₁.toPre.P.A ⟶ D₂.toPre.P.A) (h : D₂.toPre.X →+ D₁.toPre.X), Over₀ U₁ U₂ a b → ∀ (u : ∀ χ, LB.Gen (CmpLB D₁.toPre D₂.toPre b (h χ) χ)), (∀ χ (e : ℕ) (Z : Scheme.{0}) (x : Z ⟶ (thickObj R I e G₁).left) (z : Z) (J), Good (JN D₁.toPre D₂.toPre) z J → val ((U₂.gt e).t χ) (x ≫ ((Over.pullback (thick R I e)).map a).left) z (rr J) = val ((U₁.gt e).t (h χ)) x z (rl J) * val (u χ) (x ≫ (U₁.gt e).pG.left) z J) → ∀ (j j' e : ℕ) (N : Type) [Fintype N] (ρ : N → R) (σ : N → H0 U₂.LG.L j) (σ' : N → H0 U₁.LG.L j') (f : N → ∀ α : D₂.toPre.X, D₂.toPre.SecB j α) (f' : N → ∀ α : D₁.toPre.X, D₁.toPre.SecB j' α), (∀ ν, U₂.ExpandsAt e j (σ ν) (f ν)) → (∀ ν, U₁.ExpandsAt e j' (σ' ν) (f' ν)) → (∀ (Z : Scheme.{0}) (r : Z ⟶ G₁.left) (z : Z) (J₁ J₂), Good U₁.LG.L z J₁ → Good U₂.LG.L z J₂ → ∑ ν, constVal (r ≫ G₁.hom) z (ρ ν) * (sval (σ ν) (r ≫ a.left) z J₂ * sval (σ' ν) r z J₁) = 0) → ∀ (m : ∀ α, {p : D₂.toPre.X × D₁.toPre.X // h p.1 + p.2 = α} → LB.Sec (LB.LinComb (JN D₁.toPre D₂.toPre) (mixφ D₁.toPre D₂.toPre b α) (MixedConv.mixε j j'))), (∀ α p (Z : Scheme.{0}) (r : Z ⟶ D₁.toPre.P.A.left) (z : Z) (J), Good (JN D₁.toPre D₂.toPre) z J → sval (m α p) r z J = ∑ ν, constVal (r ≫ D₁.toPre.P.A.hom) z (ρ ν) * (sval (f ν p.1.1) (r ≫ b.left) z (rr J) * sval (f' ν p.1.2) r z (rl J) * (val (u p.1.1) r z J * val (MixedConv.cubB D₁.toPre (h p.1.1) p.1.2) r z (rl J)).val)) → ∀ (α : D₁.toPre.X), ∃ S : Finset {p : D₂.toPre.X × D₁.toPre.X // h p.1 + p.2 = α}, ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e D₁.toPre.P.A).left) (z : Z) (J), Good (JN D₁.toPre D₂.toPre) z J → (∀ i ∉ S, sval (m α i) (r ≫ (D₁.toPre.prBe I e).left) z J = 0) ∧ ∑ i ∈ S, sval (m α i) (r ≫ (D₁.toPre.prBe I e).left) z J = 0 := by
  first | exact @GlobalTheory.Mum.Two.Mix.level | exact GlobalTheory.Mum.Two.Mix.level | (intros; apply GlobalTheory.Mum.Two.Mix.level <;> assumption)
end
