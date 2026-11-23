module

public import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle028
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle026
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle034
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle020
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle014
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle051
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ModuliUnivEtaKilled
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle072
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FramedPointsLiftToLevelCover
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle039
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle052
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IntegralOfFramedPointOverIntegral
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationMultiplicationInvariance
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle052
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle118
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SymmetricLiftOddOrderExistsUnique
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ThetaGrpActsLinearly
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle048
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle023
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle025
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.UniversalSymLiftMulOdd
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle060
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle127
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle125
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Radical.NatInt
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SpanEqTopOfFunctionals

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

namespace GlobalTheory.PlaceInt

theorem eq_of_sq_eq_of_odd {U : Type} [CommGroup U] {r r' : U} {k : ℕ} (hk : Odd k) (h : r ^ 2 = r' ^ 2)
    (h₁ : r ^ k = 1) (h₂ : r' ^ k = 1) : r = r' := by
  obtain ⟨t, rfl⟩ := hk
  rw [pow_succ, pow_mul] at h₁ h₂
  rw [h] at h₁
  exact mul_left_cancel (h₁.trans h₂.symm)

theorem moves_mul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x : Sp S ⟶ Xo.X) (k : ℕ), Odd k → ∀ (a b : (ptO Xo x ⟶ Xo.univ.t.G)) (e : Γ((ptO Xo x).left, ⊤)ˣ), a ^ k = 1 → b ^ k = 1 → WeilIs Xo.univ.t.G Xo.univ.t.PP.L (k : ℤ) a b e → ∃ r : S, toΓ S r ^ 2 = (e : Γ((ptO Xo x).left, ⊤)) ∧ r ^ k = 1 ∧ ∀ F F₁ F₂ F₃ : SecN Xo x k, Moves Xo b F F₁ → Moves Xo a F₁ F₂ → Moves Xo (a * b) F F₃ → (∀ j, F₂.f j = liftFun Xo.univ.t.G _ (T := ptO Xo x) (toΓ S r) * F₃.f j) := by
  intro E _ _ _ H Dw l Xo S _ x k hk a b e ha hb he
  have hLaw : Laws := GlobalTheory.firstFiveLaws.1
  have := UnivPol.isLocallyNoetherian Xo
  have ex : ∀ c : ptO Xo x ⟶ Xo.univ.t.G, c ^ k = 1 →
      ∃ U : ThetaGrp Xo.univ.t.G Xo.univ.t.PP.L (k : ℤ) (ptO Xo x), SymLift Xo.univ.t.G Xo.univ.t.PP.L (k : ℤ) k c U :=
    fun c hc => (symLift_exists_unique_of_cast hLaw Xo.X (UnivPol.pol Xo) k hk
      (UnivPol.isUnit_natCast Xo _ hk.pos) (k : ℤ) rfl (ptO Xo x) c hc).1
  have hA := (moduli_univ_polAV E H Dw l Xo).2.2.2.1
  obtain ⟨Ua, hUa⟩ := ex a ha
  obtain ⟨Ub, hUb⟩ := ex b hb
  obtain ⟨Uab, hUab⟩ := ex (a * b) (by rw [mul_pow, ha, hb, _root_.mul_one])
  obtain ⟨r₀, h₂, hp, -⟩ := SymLiftMul.symLift_mul hLaw.globalFns hA Xo.univ.t.PP.isLB hk hUa hUb hUab he
  have bij : Function.Bijective (toΓ S) :=
    ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of S)).inv
  obtain ⟨r, hr⟩ := bij.2 (r₀ : Γ((ptO Xo x).left, ⊤))
  refine ⟨r, ?_, bij.1 ?_, ?_⟩
  · rw [hr, ← h₂]; exact (Units.val_pow_eq_pow_val r₀ 2).symm
  · rw [map_pow, map_one, hr]
    exact (Units.val_pow_eq_pow_val r₀ k).symm.trans (congrArg Units.val hp)
  · rintro F F₁ F₂ F₃ ⟨-, Vb, hVb, a₁⟩ ⟨-, Va, hVa, a₂⟩ ⟨-, Vab, hVab, a₃⟩ j
    obtain ⟨r₁, h₂', hp', h⟩ := SymLiftMul.symLift_mul hLaw.globalFns hA Xo.univ.t.PP.isLB hk hVa hVb hVab he
    obtain rfl : r₁ = r₀ := eq_of_sq_eq_of_odd hk (h₂'.trans h₂.symm) hp' hp
    rw [hr]
    exact h F F₁ F₂ F₃ a₁ a₂ a₃ j

end GlobalTheory.PlaceInt
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

namespace GlobalTheory.RatData

theorem epi_spMap_fields {K L : Type} [Field K] [Field L] (i : K →+* L) : Epi (spMap i) := by
  have : Flat (spMap i) := by
    rw [spMap, Flat.SpecMap_iff]
    exact RingHom.Flat.of_isField (Field.toIsField K) _
  have : Surjective (spMap i) := ⟨Function.surjective_to_subsingleton _⟩
  exact Flat.epi_of_flat_of_surjective _

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

theorem cancel_of_left_eq (Xo : Moduli Dw l) {K L : Type} [Field K] [Field L] {x : Sp K ⟶ Xo.X} {x' : Sp L ⟶ Xo.X}
    (i : K →+* L) (g : ptO Xo x' ⟶ ptO Xo x) (hg : g.left = spMap i) {a b : ptO Xo x ⟶ Xo.univ.t.G}
    (h : g ≫ a = g ≫ b) : a = b := by
  have := epi_spMap_fields i
  have h₁ := congrArg (fun f => f.left) h
  simp only [Over.comp_left, hg] at h₁
  ext1
  exact (cancel_epi (spMap i)).1 h₁

theorem descend (Xo : Moduli Dw l) {K : Type} [Field K] (x : Sp K ⟶ Xo.X) (M : ℕ) (hx : AllRat Xo x M)
    {B : Type} [CommRing B] (φ : K →+* B) (hφ : φ.FaithfullyFlat) :
    ∃ (Ω : Type) (_ : Field Ω) (χ : B →+* Ω) (x' : Sp Ω ⟶ Xo.X) (g₁ : ptO Xo x' ⟶ ptO Xo (spMap φ ≫ x))
      (g₂ : ptO Xo x' ⟶ ptO Xo x), g₁.left = spMap χ ∧ g₂.left = spMap (χ.comp φ) ∧ g₂.left = g₁.left ≫ spMap φ ∧
      ∀ w : ptO Xo (spMap φ ≫ x) ⟶ Xo.univ.t.G, w ^ M = 1 → ∃ a, g₂ ≫ a = g₁ ≫ w := by
  have : Nontrivial B := hφ.injective.nontrivial
  obtain ⟨m, hm⟩ := Ideal.exists_maximal B
  letI : Field (B ⧸ m) := Ideal.Quotient.field m
  let χ : B →+* B ⧸ m := Ideal.Quotient.mk m
  have hc : spMap (χ.comp φ) = spMap χ ≫ spMap φ := by
    rw [spMap, spMap, spMap, ← Spec.map_comp]
    rfl
  let g₁ : ptO Xo (spMap (χ.comp φ) ≫ x) ⟶ ptO Xo (spMap φ ≫ x) :=
    Over.homMk (spMap χ) (by
      change spMap χ ≫ spMap φ ≫ x = spMap (χ.comp φ) ≫ x
      rw [hc, Category.assoc])
  let g₂ : ptO Xo (spMap (χ.comp φ) ≫ x) ⟶ ptO Xo x := Over.homMk (spMap (χ.comp φ)) rfl
  refine ⟨B ⧸ m, inferInstance, χ, _, g₁, g₂, rfl, rfl, hc, fun w hw => ?_⟩
  obtain ⟨a, ha⟩ := hx (B ⧸ m) (χ.comp φ) (g₁ ≫ w) (by rw [← MonObj.comp_pow, hw, MonObj.comp_one])
  exact ⟨a, Over.OverMorphism.ext ha.symm⟩

theorem exists_root (Xo : Moduli Dw l) {K : Type} [Field K] (x : Sp K ⟶ Xo.X) (N : ℕ) (hN : 0 < N)
    (hx : AllRat Xo x (N ^ 2)) (t : ptO Xo x ⟶ Xo.univ.t.G) (ht : t ^ N = 1) : ∃ r, r ^ N = t := by
  obtain ⟨B, _, φ, w, hφ, hw⟩ := GlobalTheory.T.exists_faithfullyFlat_nthRoots_of_torsion GlobalTheory.firstFiveLaws.1 E H Dw l Xo K x N N hN hN Unit
    (fun _ => t) (fun _ => ht)
  obtain ⟨Ω, _, χ, x', g₁, g₂, h₁, h₂, h₃, h₄⟩ := descend Xo x _ hx φ hφ
  let g : ptO Xo (spMap φ ≫ x) ⟶ ptO Xo x := Over.homMk (spMap φ) rfl
  have hw' : w () ^ N = g ≫ t := Over.OverMorphism.ext (hw ())
  have hg : g₂ = g₁ ≫ g := Over.OverMorphism.ext h₃
  obtain ⟨a, ha⟩ := h₄ (w ()) (by rw [pow_two, pow_mul, hw', ← MonObj.comp_pow, ht, MonObj.comp_one])
  refine ⟨a, cancel_of_left_eq Xo _ g₂ h₂ ?_⟩
  rw [MonObj.comp_pow, ha, ← MonObj.comp_pow, hw', hg, Category.assoc]

theorem exists_linear_level (Xo : Moduli Dw l) {K : Type} [Field K] (x : Sp K ⟶ Xo.X) (k : ℕ) (hk : 0 < k)
    (hx : AllRat Xo x k) : ∃ ev : Dw.La → (ptO Xo x ⟶ Xo.univ.t.G), (∀ a b, ev (a + b) = ev a * ev b) ∧
      (∀ (o : 𝓞 E) a, ev (o • a) = ev a ≫ Xo.univ.t.act.act o) ∧ (∀ a, ev (k • a) = 1) ∧
      ∀ a b, ev a = ev b → Dw.ModN k (a - b) := by
  obtain ⟨B, _, φ, ev, hφ, hadd, hsm, hkill, hinj⟩ := GlobalTheory.T.exists_faithfullyFlat_full_linear_level_structure GlobalTheory.firstFiveLaws.1 E H Dw l Xo K x k hk
  obtain ⟨Ω, _, χ, x', g₁, g₂, h₁, h₂, -, h₄⟩ := descend Xo x _ hx φ hφ
  choose e he using fun a => h₄ (ev a) (by rw [← map_nsmul_eq_pow_of_add_eq_mul ev hadd, hkill])
  refine ⟨e, fun a b => cancel_of_left_eq Xo _ g₂ h₂ ?_, fun o a => cancel_of_left_eq Xo _ g₂ h₂ ?_,
    fun a => cancel_of_left_eq Xo _ g₂ h₂ ?_, fun a b hab => hinj Ω χ a b ?_⟩
  · rw [MonObj.comp_mul, he, he, he, hadd, MonObj.comp_mul]
  · rw [← Category.assoc, he, he, hsm, Category.assoc]
  · rw [he, hkill, MonObj.comp_one, MonObj.comp_one]
  · have h : g₁ ≫ ev a = g₁ ≫ ev b := by rw [← he, ← he, hab]
    have h' := congrArg (fun f => f.left) h
    simp only [Over.comp_left, h₁] at h'
    exact h'

theorem exists_thetaVal_data : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), (AllRat Xo y.x (l.M ^ 2) → ∀ x : Dw.La, ∃ F, IsVtOver Xo.univ.t.G Xo.univ.t.PP l.M (KilledBy Xo (l.Mb ^ 2)) y.s (levPt Xo y.x x) F) ∧ ∀ (n : ℕ) (Λ : GenLat E n) (N : ℕ), Λ.Unimod → Λ.LevOK N l.M → AllRat Xo y.x (N ^ 2) → ∃ (z : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo y.x ⟶ Xo.univ.t.G)) (tp : (Fin n → LevQ Dw l) → Fin n → (ptO Xo y.x ⟶ Xo.univ.t.G)) (F : (Fin n → LevQ Dw l) → Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y.x))), (∀ i, InZh Xo Λ N (z i)) ∧ GeoInj Xo y.x z ∧ (∀ q b, tp q b ^ N = levPt Xo y.x (levRep (q b)) ∧ ∃ j : ℕ, KilledBy Xo (l.Mb ^ j) (tp q b)) ∧ (∀ q i b, IsUUOver Xo.univ.t.G Xo.univ.t.PP N y.s (z i b) (tp q b) (F q i b)) := by
  intro E _ _ _ H Dw l Xo c K _ _ y
  have hL : Laws := GlobalTheory.firstFiveLaws.1
  have hM : 0 < l.M := l.odd.pos
  have hlev : ∀ a : Dw.La, KilledBy Xo l.Mb (levPt Xo y.x a) ∧ levPt Xo y.x a ^ l.M = 1 := by
    intro a
    obtain ⟨h₁, -, h₃⟩ := moduli_univ_eta_killed hL E H Dw l Xo a
    refine ⟨fun b hb => ?_, ?_⟩
    · rw [levPt, Category.assoc, h₁ b hb, MonObj.comp_one]
    · rw [levPt, ← MonObj.comp_pow, h₃, MonObj.comp_one]
  refine ⟨fun hx a => ?_, fun n Λ N hU hLev hx => ?_⟩
  · obtain ⟨v, hv⟩ := exists_root Xo y.x l.M hM hx _ (hlev a).2
    obtain ⟨t', ht', hk⟩ := (exists_root_killedBy_pow E H Dw l Xo _ _ v l.M hM (hlev a).1 hv).2 rfl
    refine (exists_isVtOver_and_existsUnique_isUUOver hL E H Dw l Xo l.M l.odd (ptO Xo y.x) y.s).1 _ _ t' ht' ?_ hk
    rw [pow_two, pow_mul, ht', (hlev a).2]
  · obtain ⟨hodd, hdvd, hle⟩ := hLev
    have hN : 0 < N := hodd.pos
    have hlevN : ∀ a : Dw.La, levPt Xo y.x a ^ N = 1 := by
      intro a
      obtain ⟨k, hk⟩ := hdvd
      rw [hk, pow_mul, (hlev a).2, one_pow]
    choose r hr using fun q : LevQ Dw l => exists_root Xo y.x N hN hx _ (hlevN (levRep q))
    choose t ht ht' using fun q =>
      (exists_root_killedBy_pow E H Dw l Xo _ _ _ N hN (hlev _).1 (hr q)).1
    have htN : ∀ q, t q ^ (N ^ 2) = 1 := fun q => by rw [pow_two, pow_mul, ht q, hlevN]
    obtain ⟨ev, hadd, hsm, hk, hinj⟩ := exists_linear_level Xo y.x (N ^ 2) (pow_pos hN 2) hx
    obtain ⟨zz, hz, hzi, -⟩ := GlobalTheory.T.exists_isotropic_group_lattice_class_representatives E H Dw n Λ N hU hN (hle.trans inf_le_left)
    have hZ : ∀ i, InZh Xo Λ N (fun b => ev (zz i b)) := by
      refine fun i => ⟨fun b => ?_, ?_⟩
      · rw [← map_nsmul_eq_pow_of_add_eq_mul ev hadd, hk]
      · intro mu hmu cm hcm i'
        obtain ⟨u, hu⟩ := hz i mu hmu cm hcm i'
        simp only [← hsm]
        rw [← map_sum_eq_prod_ofFn_of_add_eq_mul ev hadd, hu]
        exact hk u
    choose F hF using fun (q : Fin n → LevQ Dw l) i b =>
      ((exists_isVtOver_and_existsUnique_isUUOver hL E H Dw l Xo N hodd _ y.s).2 (ev (zz i b)) (t (q b))
        ((hZ i).1 b) (htN _)).exists
    refine ⟨fun i b => ev (zz i b), fun q b => t (q b), F, hZ, ?_, fun q b => ⟨ht _, ht' _⟩, hF⟩
    intro k _ ψ g hg i i' hii
    exact hzi _ _ fun b => hinj _ _ (cancel_of_left_eq Xo ψ g hg (congrFun hii b))

end GlobalTheory.RatData
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

namespace GlobalTheory.CoverPoint

theorem exists_finite_subfield {R F k : Type} [CommRing R] [Field F] [Field k] [Algebra F k] [Algebra.IsAlgebraic F k]
    {X : Scheme.{0}} (s : X ⟶ Sp R) [LocallyOfFiniteType s] (ρ : R →+* F) (p : Sp k ⟶ X)
    (hp : p ≫ s = spMap ((algebraMap F k).comp ρ)) :
    ∃ K : IntermediateField F k, FiniteDimensional F K ∧ ∃ q : Sp K ⟶ X, spMap (algebraMap K k) ≫ q = p := by
  classical
  obtain ⟨_, ⟨U, hU, rfl⟩, hpt, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (p (IsLocalRing.closedPoint k))) isOpen_univ
  have hU : IsAffineOpen U := hU
  obtain ⟨f, hf⟩ : ∃ f : Γ(X, U) ⟶ CommRingCat.of k, Spec.map f ≫ hU.fromSpec = p := by
    refine ⟨Spec.preimage (IsOpenImmersion.lift hU.fromSpec p ?_), ?_⟩
    · rintro _ ⟨y, rfl⟩
      rw [hU.range_fromSpec, Subsingleton.elim (α := PrimeSpectrum k) y (IsLocalRing.closedPoint k)]
      exact hpt
    · rw [Spec.map_preimage]; exact IsOpenImmersion.lift_fac _ _ _
  obtain ⟨g, hg⟩ : ∃ g : CommRingCat.of R ⟶ Γ(X, U), Spec.map g = hU.fromSpec ≫ s :=
    ⟨Spec.preimage _, Spec.map_preimage _⟩
  have hgf : g ≫ f = CommRingCat.ofHom ((algebraMap F k).comp ρ) :=
    Spec.map_injective (by
      rw [Spec.map_comp, hg, ← Category.assoc, hf]
      exact hp)
  have hV : ∀ r : R, f.hom (g.hom r) = algebraMap F k (ρ r) := fun r =>
    congrArg (fun q => q.hom r) hgf
  have hft : g.hom.FiniteType := by
    have : LocallyOfFiniteType (Spec.map g) := by rw [hg]; infer_instance
    exact HasRingHomProperty.Spec_iff.1 this
  let _ : Algebra R Γ(X, U) := g.hom.toAlgebra
  obtain ⟨t, ht⟩ := (show Algebra.FiniteType R Γ(X, U) from hft).out
  let S : Set k := (t.image f.hom : Finset k)
  let K := IntermediateField.adjoin F S
  refine ⟨K, IntermediateField.finiteDimensional_adjoin fun x _ =>
    (Algebra.IsAlgebraic.isAlgebraic x).isIntegral, ?_⟩
  have hr : ∀ a, f.hom a ∈ K := fun a => by
    have ha : a ∈ Algebra.adjoin R (t : Set Γ(X, U)) := ht ▸ Algebra.mem_top
    induction ha using Algebra.adjoin_induction with
    | mem x hx => exact IntermediateField.subset_adjoin F S (Finset.mem_image_of_mem _ hx)
    | algebraMap r => exact (hV r).symm ▸ K.algebraMap_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  let f' : Γ(X, U) ⟶ CommRingCat.of K := CommRingCat.ofHom (f.hom.codRestrict K hr)
  refine ⟨Spec.map f' ≫ hU.fromSpec, ?_⟩
  change Spec.map _ ≫ Spec.map f' ≫ hU.fromSpec = _
  rw [← hf, ← Spec.map_comp_assoc]
  rfl

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, ← Spec.map_comp]; rfl

theorem epi_spMap {K k : Type} [Field K] [Field k] (f : K →+* k) : Epi (spMap f) := by
  have h1 : Flat (spMap f) := by
    let _ := f.toAlgebra
    exact HasRingHomProperty.Spec_iff.2 (show (algebraMap K k).Flat from
      RingHom.flat_algebraMap_iff.2 inferInstance)
  have h2 : Surjective (spMap f) := ⟨fun x => ⟨IsLocalRing.closedPoint k, Subsingleton.elim (α := PrimeSpectrum K) _ _⟩⟩
  exact Flat.epi_of_flat_of_surjective _

theorem exists_ext_lift_to_cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n), d.IsLev → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io), T.FinRes → ∃ (T' : CDVR) (iT : T.Fr →+* T'.Fr) (e : ℕ) (y' : IntFr Xo c T' (iT.comp io)) (io₂ : d.c₂.F →+* T'.Fr) (y₂ : IntFr d.Xo₂ d.c₂ T' io₂), IsExt y iT e y' ∧ T'.FinRes ∧ (∀ a : c.F, io₂ (d.eF a) = iT (io a)) ∧ (letI := (iT.comp io).toAlgebra; letI := io₂.toAlgebra; FrOver d y₂.1 y'.1) := by
  intro E _ _ _ H Dw l Xo c n d hd T io y hT
  have hL : Laws := GlobalTheory.firstFiveLaws.1
  let j : d.c₂.F →+* c.F := d.eF.symm.toAlgHom.toRingHom
  have hj : ∀ a : c.F, j (d.eF a) = a := fun a => d.eF.symm_apply_apply a
  let k := AlgebraicClosure T.Fr
  have key : ∃ p : Sp k ⟶ d.Xo₂.X, p ≫ d.r = spMap (algebraMap T.Fr k) ≫ xOf y ∧
      p ≫ d.Xo₂.s = spMap ((algebraMap T.Fr k).comp
        ((io.comp j).comp (IntermediateField.inclusion d.c₂.le).toRingHom)) := by
    letI := io.toAlgebra
    letI : Algebra c.F k := ((algebraMap T.Fr k).comp io).toAlgebra
    letI : Algebra d.c₂.F k := ((algebraMap T.Fr k).comp (io.comp j)).toAlgebra
    let ψ : T.Fr →ₐ[c.F] k := { algebraMap T.Fr k with commutes' := fun _ => rfl }
    obtain ⟨z, hz⟩ := GlobalTheory.FramedBaseChange.exists_frMap hL E H Dw l Xo c T.Fr k ψ y.1
    obtain ⟨z₂, hz₂⟩ := hd.2.2.2.2.2.2.1 k (fun a => by
      change algebraMap T.Fr k (io (j (d.eF a))) = algebraMap T.Fr k (io a)
      rw [hj]) z
    exact ⟨z₂.x, hz₂.1.trans hz.1, z₂.x_over⟩
  obtain ⟨p, hp1, hp2⟩ := key
  haveI := d.Xo₂.smooth
  haveI : Smooth d.Xo₂.s := SmoothOfRelativeDimension.smooth Dw.dim _
  obtain ⟨K, hK, q, hq⟩ := exists_finite_subfield d.Xo₂.s _ p hp2
  haveI := epi_spMap (algebraMap K k)
  have hKk : (algebraMap K k).comp (algebraMap T.Fr K) = algebraMap T.Fr k := rfl
  have hq1 : q ≫ d.r = spMap (algebraMap T.Fr K) ≫ xOf y := by
    rw [← cancel_epi (spMap (algebraMap K k)), ← Category.assoc, hq, hp1, ← Category.assoc, spMap_comp', hKk]
  have hq2 : q ≫ d.Xo₂.s = spMap ((algebraMap T.Fr K).comp
      ((io.comp j).comp (IntermediateField.inclusion d.c₂.le).toRingHom)) := by
    rw [← cancel_epi (spMap (algebraMap K k)), ← Category.assoc, hq, hp2, spMap_comp']
    rfl
  obtain ⟨T', iT, e, ψ, φ, he, hv, hψ, -, hfin⟩ := GlobalTheory.PlaceExtField.exists_cdvr_finite_extension T K
  have hψ' : ψ.toRingHom.comp (algebraMap T.Fr K) = iT := RingHom.ext hψ
  obtain ⟨⟨y', hy'⟩, hx⟩ := GlobalTheory.T.exists_integralFramedPoint_baseChange_cdvr_transitive E H Dw l Xo c T T' io y iT e he hv
  have hx' := (hx y' hy').1
  let io₂ : d.c₂.F →+* T'.Fr := iT.comp (io.comp j)
  have hio : ∀ a : c.F, io₂ (d.eF a) = iT (io a) := fun a => by
    change iT (io (j (d.eF a))) = _
    rw [hj]
  letI := (iT.comp io).toAlgebra
  letI := io₂.toAlgebra
  obtain ⟨y₂, -, hy₂⟩ := (GlobalTheory.frames_lift_to_cover hL E H Dw l Xo c n d).1 T'.Fr hio y'.1
    (spMap ψ.toRingHom ≫ q)
    (by rw [Category.assoc, hq1, ← Category.assoc, spMap_comp', hψ']; exact hx'.symm)
    (by rw [Category.assoc, hq2, spMap_comp', ← RingHom.comp_assoc, hψ']; rfl)
  exact ⟨T', iT, e, y', io₂, ⟨y₂, GlobalTheory.Frames.allTest_of_secBaseChange hL.secBaseChange E H Dw d.l₂ d.Xo₂ d.c₂ _ y₂,
    GlobalTheory.T.integral_of_framed_point_over_integral E H Dw l Xo c n d T' (iT.comp io) io₂ y' hio y₂ hy₂⟩, hy', hfin hT, hio, hy₂⟩

end GlobalTheory.CoverPoint
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm
namespace GlobalTheory

theorem tied_section_expansion_existsUnique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (I : IntData Xo c T io y.1) (P : PELUnif (maximalIdeal T.V) I.G), P.TorsionIso → ∀ (ϖ : T.V), Irreducible ϖ → ∀ (Q : P.D.toPre.X → ℤ), IsQ P.D.toPre ϖ Q → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra T.Fr F] [Algebra T.V F] [IsScalarTower T.V T.Fr F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → ∀ (xF : Sp F ⟶ Xo.X) (h : ptO Xo xF ⟶ ptO Xo (xOf y)), h.left = spMap (algebraMap T.Fr F) → ∀ k : ℕ, 1 ≤ k → ∀ hh : SecN Xo xF k, (∃! σ, SecTieF I P F xF k σ hh) ∧ ∀ σ, SecTieF I P F xF k σ hh → ∃! s, P.U.toUnifPre.ExpandsG F k σ s := by
  intro E _ _ _ H Dw l Xo c T io y I P _ ϖ _ Q _ F _ _ _ _ _ v _ xF h hh k hk s
  have hx : xF = spMap (algebraMap T.Fr F) ≫ xOf y := by
    have := Over.w h
    rw [hh] at this
    exact this.symm
  obtain ⟨h1, h2, -, h4, -⟩ := GlobalTheory.firstFiveLaws
  refine ⟨(GlobalTheory.T.powPullbackSec_modelUniversal_bijective E H Dw l Xo c T io y.1 I P F xF hx k).2.1 s, fun σ _ => ?_⟩
  exact (GlobalTheory.expandsG_bijective_of_dvr h1 h2 h4 GlobalTheory.twistBaseChange T.V P.D P.A I.G.G P.U F k hk).1 σ

end GlobalTheory
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

namespace GlobalTheory.SymMove

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {T : Over S} {k : ℤ}

theorem act_unique (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) {n : ℕ} (hn : Odd n) {x : T ⟶ A}
    {θ θ' : ThetaGrp A L k T} (h : SymLift A L k n x θ) (h' : SymLift A L k n x θ')
    {s t t' : LB.Sec (LPow A L k T)} (a : IsActOf A L k θ s t) (a' : IsActOf A L k θ' s t') : t = t' := by
  have hc := SymLiftOdd.symLift_unique hG hA hL hn θ θ' h h'
  have e : θ.pt = θ'.pt := h.pt_eq.trans h'.pt_eq.symm
  have key : ∀ j, t.f j = t'.f j :=
    sec_ext_val hL (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => k) (s := t) (s' := t')
      fun y J hJ => (twist_val a (𝟙 _) y hJ).trans (Eq.trans (congrArg₂ (· * ·)
        (congrArg Units.val (val_corr hJ hc (𝟙 _))) (by rw [e])) (twist_val a' (𝟙 _) y hJ).symm)
  obtain ⟨f₁, p₁⟩ := t
  obtain ⟨f₂, p₂⟩ := t'
  obtain rfl : f₁ = f₂ := funext key
  rfl

theorem exists_one (hL : L.IsLB) {ν : LB.Gen (negLB A L k T)} (hν : ν.IsGen) (n : ℕ) (s : LB.Sec (LPow A L k T)) :
    ∃ θ : ThetaGrp A L k T, SymLift A L k n 1 θ ∧ IsActOf A L k θ s s := by
  obtain ⟨o, ho, vo⟩ := ThetaCoord.exists_symLift_one hL hν n
  refine ⟨o, ho, VVRank.isTwistPull_of_sv A hL o.isGen fun z J hJ => ?_⟩
  have e : translT A (1 : T ⟶ A) = 𝟙 _ := by
    rw [translT, ThetaAct.translPt_one, lift_fst_snd]
  change _ = (CommPairing.tval o (𝟙 _) z J).val * _
  rw [vo _ _ z J hJ, ho.pt_eq, e, Units.val_one, _root_.one_mul, Over.id_left]
  rfl

end GlobalTheory.SymMove

namespace GlobalTheory

theorem existsUnique_moves : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x : Sp S ⟶ Xo.X) (k : ℕ), Odd k → ∀ (b : (ptO Xo x ⟶ Xo.univ.t.G)), b ^ k = 1 → ∀ F : SecN Xo x k, (∃! F' : SecN Xo x k, Moves Xo b F F') ∧ Moves Xo 1 F F := by
  intro E _ _ _ H Dw l Xo S _ x k hk b hb F
  have hLaw : Laws := firstFiveLaws.1
  have := UnivPol.isLocallyNoetherian Xo
  have hA : IsAbelianScheme Xo.univ.t.G := (UnivPol.pol Xo).isAb
  have hL : Xo.univ.t.PP.L.IsLB := (UnivPol.pol Xo).isLB
  obtain ⟨U, hU⟩ : ∃ U : ThetaGrp Xo.univ.t.G Xo.univ.t.PP.L (k : ℤ) (ptO Xo x),
      SymLift Xo.univ.t.G Xo.univ.t.PP.L (k : ℤ) k b U :=
    exists_symLift_global hLaw Xo.X (UnivPol.pol Xo) k hk (UnivPol.isUnit_natCast Xo _ hk.pos) _ b hb
  obtain ⟨F', hF', -⟩ := existsUnique_isTwistPull _ _ _ hL _ (translT _ U.pt) (translPt _ U.pt) (lift_snd _ _)
    k k U.φ U.isGen F
  obtain ⟨ν, hν, -⟩ := hU.sym
  refine ⟨⟨F', ⟨hb, U, hU, hF'⟩, fun F'' h => ?_⟩, one_pow k, SymMove.exists_one hL hν k F⟩
  obtain ⟨-, U', hU', a⟩ := h
  exact SymMove.act_unique hLaw.globalFns hA hL hk hU' hU a hF'

end GlobalTheory
end
end
