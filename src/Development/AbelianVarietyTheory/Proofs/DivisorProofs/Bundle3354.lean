module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle019
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1280
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1616
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3346
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3239
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3285
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3310
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3328
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle070
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Definitions.Degenerations.NormNatCastPadicAlgClOfCoprime
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3329
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2795
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2805
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2794
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2793
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3270
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle071
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle073
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3347
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle077
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3348
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle095
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle036
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle043
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3302
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3338
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3216
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OnTorusComp
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRatPointOfFiniteType
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
public import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3349
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.QuasiAffine
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
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3104

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.semiAbelian_descends_of_descends_near_closedFibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (S : Scheme.{0}) (π : S ⟶ Sp R), IsProper π → Surjective π → IsIntegral S → ∀ (G' : Over S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ N : Near π G', N.Law → ∃ (G : Over (Sp R)) (_ : GrpObj G) (_ : IsCommMonObj G) (β : G'.left ⟶ G.left) (i : N.U ⟶ G), IsSemiAbelian G ∧ IsGrpPullback G' G π β ∧ IsOpenImmersion i.left ∧ N.u ≫ β = pullback.fst _ _ ≫ i.left := by
  first | exact @GlobalTheory.Mum.descend_of_near | exact GlobalTheory.Mum.descend_of_near | (intros; apply GlobalTheory.Mum.descend_of_near <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

set_option autoImplicit false

namespace GlobalTheory.RecSec

theorem compactSpace_of_projOver {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Sp R}
    (h : IsProjOver f) : CompactSpace X := by
  obtain ⟨m, i, hi, rfl⟩ := h
  have := isProper_str R m
  have : IsProper (i ≫ PSpace.str R m) := inferInstance
  exact QuasiCompact.compactSpace_of_compactSpace (i ≫ PSpace.str R m)

theorem finsum_update_tens (P : GlobalTheory.Published.Principalisation) {F : Type} [Field F] {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] {p : X ⟶ Sp F} {σ : F →+* ℂ} {e : ℕ} (hp : IsProjOver p)
    (hdim : topologicalKrullDim X = (e + 1 : ℕ)) (Δ : CartierDiv X) (B : MLine p σ) (b : B.B.Sec)
    (hb : ∀ z, Δ.mult z ≠ 0 → z ∈ nonzeroLocus b) (L : Fin e → MLine p σ) (i : Fin e) (A C : MLine p σ) :
    ∑ᶠ z, (Δ.mult z : ℝ) * cycInt (Function.update L i (A.tens C)) (B.logSec b) z =
      ∑ᶠ z, (Δ.mult z : ℝ) * cycInt (Function.update L i A) (B.logSec b) z +
        ∑ᶠ z, (Δ.mult z : ℝ) * cycInt (Function.update L i C) (B.logSec b) z := by
  have : CompactSpace X := compactSpace_of_projOver hp
  have hfin := Δ.finite_support_mult
  have hsub (G : X → ℝ) : (Function.support fun z => (Δ.mult z : ℝ) * G z).Finite :=
    hfin.subset fun z hz => by
      simp only [Function.mem_support] at hz ⊢
      intro h0; exact hz (by simp [h0])
  rw [← finsum_add_distrib (hsub _) (hsub _)]
  refine finsum_congr fun z => ?_
  by_cases h0 : Δ.mult z = 0
  · simp [h0]
  have hz1 : Order.coheight z = 1 := CartierDiv.coheight_eq_one_of_mult_ne_zero h0
  have hcl : topologicalKrullDim (closure ({z} : Set X)) = e :=
    (GlobalTheory.T.coheight_eq_one_iff_closure_dim_projective F X p e hp hdim z).1 hz1
  have h₁ := (GlobalTheory.T.mixedChernForm_finite_integrable_pointClosure P F X p σ hp e (Function.update L i A) z hcl).2.2.2 B b (hb z h0)
  have h₂ := (GlobalTheory.T.mixedChernForm_finite_integrable_pointClosure P F X p σ hp e (Function.update L i C) z hcl).2.2.2 B b (hb z h0)
  rw [GlobalTheory.T.pointClosureIntegral_update_tensor_additive F X p σ hp e L i A C (B.logSec b) z h₁ h₂, mul_add]

theorem side_update_tens (P : GlobalTheory.Published.Principalisation) {F : Type} [Field F] {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] {p : X ⟶ Sp F} {σ : F →+* ℂ} {e : ℕ} (hp : IsProjOver p)
    (hdim : topologicalKrullDim X = (e + 1 : ℕ)) (N M : MLine p σ) (s : M.B.Sec)
    (hs : genericPoint X ∈ nonzeroLocus s) (Δ : CartierDiv X) (B : MLine p σ) (b : B.B.Sec)
    (hb : ∀ z, Δ.mult z ≠ 0 → z ∈ nonzeroLocus b) (L : Fin e → MLine p σ) (i : Fin e) (A C : MLine p σ) :
    side N (Function.update L i (A.tens C)) (M.logSec s) (B.logSec b) Δ =
      side N (Function.update L i A) (M.logSec s) (B.logSec b) Δ +
        side N (Function.update L i C) (M.logSec s) (B.logSec b) Δ := by
  simp only [side, Fin.cons_update]
  have hA := GlobalTheory.T.log_norm_section_integrable_mixedChern_projective P F X p σ (e + 1) hp hdim (Function.update (Fin.cons N L) i.succ A) M s hs
  have hC := GlobalTheory.T.log_norm_section_integrable_mixedChern_projective P F X p σ (e + 1) hp hdim (Function.update (Fin.cons N L) i.succ C) M s hs
  rw [(GlobalTheory.T.mixedChernIntegral_additive_in_factor F X p σ hp (e + 1) (Fin.cons N L) i.succ A C (M.logSec s) hA hC).2,
    finsum_update_tens P hp hdim Δ B b hb L i A C]
  ring

theorem reciprocity_sec : GlobalTheory.Published.Principalisation → ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp F) (σ : F →+* ℂ) (e : ℕ), IsProjOver p → topologicalKrullDim X = (e + 1 : ℕ) → ∀ (L : Fin e → MLine p σ) (M N : MLine p σ) (s : M.B.Sec) (hs : genericPoint X ∈ nonzeroLocus s) (t : N.B.Sec) (ht : genericPoint X ∈ nonzeroLocus t), (∀ z : X, Order.coheight z = 1 → z ∈ nonzeroLocus s ∨ z ∈ nonzeroLocus t) → (∃ (n : ℕ) (u : Fin n → M.B.Sec), ⨆ i, nonzeroLocus (u i) = ⊤) → (∃ (n : ℕ) (u : Fin n → N.B.Sec), ⨆ i, nonzeroLocus (u i) = ⊤) → side N L (M.logSec s) (N.logSec t) (divOfSec M.φ.isLB s hs) = side M L (N.logSec t) (M.logSec s) (divOfSec N.φ.isLB t ht) := by
  intro P F _ X _ _ p σ e hp hdim L M N s hs t ht hcod hgM hgN
  classical
  let Df : (Fin e → MLine p σ) → ℝ := fun L =>
    side N L (M.logSec s) (N.logSec t) (divOfSec M.φ.isLB s hs) -
      side M L (N.logSec t) (M.logSec s) (divOfSec N.φ.isLB t ht)
  have hbt : ∀ z, (divOfSec M.φ.isLB s hs).mult z ≠ 0 → z ∈ nonzeroLocus t := fun z h0 =>
    (hcod z (CartierDiv.coheight_eq_one_of_mult_ne_zero h0)).resolve_left fun hz =>
      (notMem_supp_divOfSec.2 hz) (CartierDiv.mem_supp_of_mult_ne_zero h0)
  have hbs : ∀ z, (divOfSec N.φ.isLB t ht).mult z ≠ 0 → z ∈ nonzeroLocus s := fun z h0 =>
    (hcod z (CartierDiv.coheight_eq_one_of_mult_ne_zero h0)).resolve_right fun hz =>
      (notMem_supp_divOfSec.2 hz) (CartierDiv.mem_supp_of_mult_ne_zero h0)
  have hadd : ∀ (L : Fin e → MLine p σ) (i : Fin e) (A C : MLine p σ),
      Df (Function.update L i (A.tens C)) = Df (Function.update L i A) + Df (Function.update L i C) := by
    intro L i A C
    simp only [Df, side_update_tens P hp hdim N M s hs _ N t hbt L i A C,
      side_update_tens P hp hdim M N t ht _ M s hbs L i A C]
    ring
  have hpos : ∀ L : Fin e → MLine p σ, (∀ i, (L i).φ.SemiPosReg (e + 1)) → Df L = 0 := fun L hL =>
    sub_eq_zero.2 (GlobalTheory.T.generatedBundles_reciprocity_semiPositive P F X p σ e hp hdim L M N s hs t ht hcod hL hgM hgN)
  have key : ∀ (S : Finset (Fin e)) (L : Fin e → MLine p σ),
      (∀ i, i ∉ S → (L i).φ.SemiPosReg (e + 1)) → Df L = 0 := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact fun L hL => hpos L fun i => hL i (Finset.notMem_empty i)
    | insert a S ha ih =>
      intro L hL
      obtain ⟨Q, hQ, hAQ⟩ := GlobalTheory.T.exists_semiPos_twist_metrisedLineBundle F X p σ hp (e + 1) (L a)
      have hgood : ∀ R : MLine p σ, R.φ.SemiPosReg (e + 1) → Df (Function.update L a R) = 0 := by
        intro R hR
        refine ih _ fun i hi => ?_
        by_cases hia : i = a
        · subst hia; rw [Function.update_self]; exact hR
        · rw [Function.update_of_ne hia]
          exact hL i (by simp [hia, hi])
      have h := hadd L a (L a) Q
      rw [hgood _ hAQ, hgood _ hQ, Function.update_eq_self] at h
      linarith
  have := key Finset.univ L fun i hi => absurd (Finset.mem_univ i) hi
  exact sub_eq_zero.1 this

end GlobalTheory.RecSec
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.Poinc.Periods

theorem one_lattice {g n : ℕ} {o : Type} [CommRing o] {ζ : o} {F : SFam g n ζ} {R : Type} [CommRing R] [IsDomain R]
    [IsLocalRing R] (D : DegData R (maximalIdeal R)) (W : Matrix (Fin 8) (Fin 8) ℤ) (hW : IsE8 W)
    (m : Fin 8 → Fin 8 → (D.toPre.X →+ D.toPre.X)) (P : ∀ T : Trait F, (R →+* T.V) → Prop)
    (h : ∀ T ψ, P T ψ → ∃ ρT : D.toPre.X ≃+ (Fin 8 → T.D.toPre.X),
      (∀ y r, PsiCoord D.toPre y r → 0 ≤ qW W T.β (ρT y) ∧ Associated (ψ r) (T.ϖ ^ (qW W T.β (ρT y)).toNat)) ∧
      ∀ a b y, MatRel W a b (ρT y) (ρT (m a b y))) :
    ∃ (Λ : Type) (_ : AddCommGroup Λ) (p : Λ → R) (c : ℕ), 1 ≤ c ∧ ∀ T ψ, P T ψ →
      ∃ e : Λ ≃+ T.D.toPre.X, ∀ y, ∃ k : ℕ, (k : ℤ) = c * T.β (e y) (e y) ∧ Associated (ψ (p y)) (T.ϖ ^ k) := by
  have hc : 0 < W 0 0 := by
    have := hW.1.diag_pos (i := 0)
    simp only [Matrix.map_apply, Matrix.add_apply, Matrix.transpose_apply] at this
    have h2 : (0 : ℤ) < W 0 0 + W 0 0 := by exact_mod_cast this
    omega
  by_cases hex : ∃ T ψ, P T ψ
  swap
  · push_neg at hex
    exact ⟨PUnit, inferInstance, fun _ => 0, 1, le_rfl, fun T ψ hP => absurd hP (hex T ψ)⟩
  obtain ⟨T₀, ψ₀, hP₀⟩ := hex
  obtain ⟨e₀, -, he₀⟩ := h T₀ ψ₀ hP₀
  have hcoord : ∀ z, ∃ r, PsiCoord D.toPre (e₀.symm (Pi.single 0 z)) r := fun z =>
    (GlobalTheory.PeriodFormCompare.exists_psiCoord_iff D.toPre _).2 (GlobalTheory.PeriodFormCompare.psiIn_top D _)
  choose p hp using hcoord
  refine ⟨T₀.D.toPre.X, inferInstance, p, (W 0 0).toNat, by omega, fun T ψ hP => ?_⟩
  obtain ⟨ρT, hρ, hm⟩ := h T ψ hP
  obtain ⟨π, hπs, hπ⟩ := exists_diag_of_matRel W hW D.toPre.X T₀.D.toPre.X T.D.toPre.X m e₀ ρT.toAddMonoidHom
    ρT.surjective he₀ hm
  have hsingle : ∀ z, ρT (e₀.symm (Pi.single 0 z)) = Pi.single 0 (π z) := by
    intro z
    funext u
    have := hπ (e₀.symm (Pi.single 0 z)) u
    simp only [AddEquiv.coe_toAddMonoidHom, AddEquiv.apply_symm_apply] at this
    rw [this]
    by_cases hu : u = 0
    · subst hu; simp
    · simp [Pi.single_apply, hu]
  have hinj : Function.Injective π := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro z hz
    have h1 : ρT (e₀.symm (Pi.single 0 z)) = 0 := by rw [hsingle, hz, Pi.single_zero]
    have h2 : e₀.symm (Pi.single 0 z) = 0 := by simpa using h1
    have h3 : (Pi.single 0 z : Fin 8 → T₀.D.toPre.X) = 0 := by simpa using h2
    simpa using congrFun h3 0
  refine ⟨AddEquiv.ofBijective π ⟨hinj, hπs⟩, fun z => ?_⟩
  obtain ⟨h0, ha⟩ := hρ _ _ (hp z)
  rw [hsingle] at h0 ha
  have hq : qW W T.β (Pi.single 0 (π z)) = W 0 0 * T.β (π z) (π z) := by
    unfold qW
    rw [Finset.sum_eq_single 0 (fun u _ hu => by simp [Pi.single_eq_of_ne hu]) (by simp)]
    rw [Finset.sum_eq_single 0 (fun v _ hv => by simp [Pi.single_eq_of_ne hv]) (by simp)]
    simp
  refine ⟨(qW W T.β (Pi.single 0 (π z))).toNat, ?_, ha⟩
  rw [Int.toNat_of_nonneg h0, hq, Int.toNat_of_nonneg hc.le]
  rfl

end GlobalTheory.Poinc.Periods

theorem GlobalTheory.Poinc.Periods.trait_iso : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real) (u : Sp S.R ⟶ F.X) c pr, SharpBy F W ρ.P u c pr → ∀ (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), S.Over₀ M U₀ → ∀ (V : M.Z.Opens) (v : V.toScheme ⟶ F.X), (∀ x : Sp Ω ⟶ V.toScheme, x ≫ V.ι = M.pt → x ≫ v = spMap S.R.val.toRingHom ≫ u) → ∀ (f : Fin 8 → Fin 8 → (FinalForm.G ⟶ FinalForm.G)), (∀ a b, MatOn FinalForm pr a b (f a b)) → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (ξ : Sp R ⟶ M.Z) [IsCommMonObj ((Over.pullback ξ).obj FinalForm.G)] (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A ((Over.pullback ξ).obj FinalForm.G)), LBIso U.LG.L (FinalForm.L.L.pull (pullback.fst FinalForm.G.hom ξ)) → (∀ y, PsiUnitOn D.toPre y (ξ ⁻¹' abLocus FinalForm.G)) → ∀ (m : Fin 8 → Fin 8 → (D.toPre.X →+ D.toPre.X)), (∀ a b, EndChar U ((Over.pullback ξ).map (f a b)) (m a b)) → ∀ (T : Trait F) (ψ : R →+* T.V), IsLocalHom ψ → ThroughU M V v (𝟙 F.X) T (spMap ψ ≫ ξ) → ∃ ρT : D.toPre.X ≃+ (Fin 8 → T.D.toPre.X), (∀ y r, PsiCoord D.toPre y r → 0 ≤ qW W T.β (ρT y) ∧ Associated (ψ r) (T.ϖ ^ (qW W T.β (ρT y)).toNat)) ∧ ∀ a b y, MatRel W a b (ρT y) (ρT (m a b y)) := by
  intro g n o _ ζ F W hW o' Ω _ _ _ hA S ρ u c pr hs M U₀ EE FinalForm hO V v hv f hf R _ _ _ hB ξ _ D A U hL hP m hm T ψ hl ht
  have hVab := (GlobalTheory.T.thetaModel_open_abelian_eighthPower_with_bundle g n o ζ F W o' Ω S ρ u c pr hs M U₀ EE FinalForm hO V v hv).1
  have hBV : GlobalTheory.Mum.Base T.V := ⟨⟨inferInstance, inferInstance, inferInstance, T.complete⟩, inferInstance⟩
  have hgen : ∀ w, (jK T.V ≫ spMap ψ ≫ ξ) w ∈ abLocus FinalForm.G := by
    obtain ⟨ξ₀, hξ₀, -⟩ := ht
    intro w
    rw [← hξ₀]
    exact hVab (ξ₀ w).2
  obtain ⟨G', _, _, D', A', U', gm, ι, hG', hgm, hLB, hC, hE⟩ :=
    GlobalTheory.T.uniformisation_baseChange_completedLocal_abelianLocus M.Z FinalForm.G FinalForm.semi FinalForm.L.L R hB ξ D A U hL hP T.V hBV ψ hl hgen
  refine GlobalTheory.T.characterGroup_eq_eighthPower_lattice_over_trait g n o ζ F W hW o' Ω S ρ u c pr hs M U₀ EE FinalForm hO V v hv f hf R ξ D.toPre m
    T ψ ht G' D' A' U' gm ι hG' hgm hLB hC fun a b => ?_
  obtain ⟨f', hf'm, hf'c, hf'e⟩ := hE (f a b) (hf a b).1
  exact ⟨f', hf'm, hf'c, fun m' hm' => hf'e _ m' (hm a b) hm'⟩

theorem GlobalTheory.Poinc.Periods.main : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real) (u : Sp S.R ⟶ F.X), SharpOver F W ρ.P u → ∀ (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), S.Over₀ M U₀ → ∀ (V : M.Z.Opens) (v : V.toScheme ⟶ F.X), (∀ x : Sp Ω ⟶ V.toScheme, x ≫ V.ι = M.pt → x ≫ v = spMap S.R.val.toRingHom ≫ u) → ∀ x : M.Z, ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : IsLocalRing R) (j : M.Z.presheaf.stalk x →+* R) (Λ : Type) (_ : AddCommGroup Λ) (p : Λ → R) (c : ℕ), GlobalTheory.Mum.Base R ∧ IsCpl j ∧ 1 ≤ c ∧ ∀ (T : Trait F) (ψ : R →+* T.V), IsLocalHom ψ → ThroughU M V v (𝟙 F.X) T (spMap (ψ.comp j) ≫ M.Z.fromSpecStalk x) → ∃ e : Λ ≃+ T.D.toPre.X, ∀ y, ∃ k : ℕ, (k : ℤ) = c * T.β (e y) (e y) ∧ Associated (ψ (p y)) (T.ϖ ^ k) := by
  intro g n o _ ζ F W hW o' Ω _ _ _ hA S ρ u hu M U₀ EE FinalForm hO V v hv x
  obtain ⟨c, pr, hs⟩ := (sharpOver_iff F W ρ.P u).1 hu
  have hinjΩ := M.stalkHom_injective x
  haveI : IsDomain (M.Z.presheaf.stalk x) := hinjΩ.isDomain
  haveI : CharZero Ω := hA.char
  haveI : CharZero (M.Z.presheaf.stalk x) := (RingHom.charZero_iff hinjΩ).2 inferInstance
  haveI : IsIntegrallyClosed (M.Z.presheaf.stalk x) := (hO.normal x).2
  haveI : Algebra.EssFiniteType ℤ (M.Z.presheaf.stalk x) := GlobalTheory.Poinc.CompletedStalk.essFiniteType_int_stalk M x
  haveI : IsNoetherianRing (M.Z.presheaf.stalk x) := Algebra.EssFiniteType.isNoetherianRing ℤ _
  have fg : (maximalIdeal (M.Z.presheaf.stalk x)).FG := IsNoetherian.noetherian _
  haveI hloc : IsLocalRing (AdicCompletion (maximalIdeal (M.Z.presheaf.stalk x)) (M.Z.presheaf.stalk x)) :=
    AdicCompletion.isLocalRing_of_fg fg
  obtain ⟨hRd, hRi⟩ := GlobalTheory.AnalyticNormality.completion_isDomain_and_isIntegrallyClosed (M.Z.presheaf.stalk x)
  haveI hRn : IsNoetherianRing (AdicCompletion (maximalIdeal (M.Z.presheaf.stalk x)) (M.Z.presheaf.stalk x)) :=
    GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion _ _
  have hm := AdicCompletion.maximalIdeal_eq_map_of_fg fg
  set R := AdicCompletion (maximalIdeal (M.Z.presheaf.stalk x)) (M.Z.presheaf.stalk x) with hR
  set φ := algebraMap (M.Z.presheaf.stalk x) R with hφ
  have hcpl : IsAdicComplete (maximalIdeal R) R := by
    rw [hm]
    exact AdicCompletion.isAdicComplete_self _ fg
  have hinj : Function.Injective φ := AdicCompletion.of_injective _ _
  haveI : CharZero R := (RingHom.charZero_iff hinj).1 inferInstance
  set ξ : Sp R ⟶ M.Z := spMap φ ≫ M.Z.fromSpecStalk x with hξ
  have hne : (ξ ⁻¹' abLocus FinalForm.G).Nonempty := by
    let w : Sp R := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)
    let p : Sp (M.Z.presheaf.stalk x) := spMap φ w
    have hp : p.asIdeal = ⊥ := by
      show Ideal.comap φ ⊥ = ⊥
      rw [← RingHom.ker_eq_comap_bot]
      exact (RingHom.injective_iff_ker_eq_bot φ).1 hinj
    have hgen : genericPoint M.Z ∈ Set.range (M.Z.fromSpecStalk x) := by
      rw [Scheme.range_fromSpecStalk]
      exact genericPoint_specializes x
    obtain ⟨q, hq⟩ := hgen
    have hpq : p ⤳ q := (PrimeSpectrum.le_iff_specializes p q).1 (by
      show p.asIdeal ≤ q.asIdeal
      rw [hp]
      exact bot_le)
    have hsp : ξ w ⤳ genericPoint M.Z := by
      have := hpq.map (M.Z.fromSpecStalk x).continuous
      rw [hq] at this
      exact this
    refine ⟨w, ?_⟩
    show ξ w ∈ abLocus FinalForm.G
    rw [FinalForm.ab]
    exact le_bot_iff.1 ((S.TT_anti M hsp).trans (ThetaSys.TT_genericPoint S M).le)
  haveI : IsCommMonObj ((Over.pullback ξ).obj FinalForm.G) := Functor.isCommMonObj_obj
  obtain ⟨D, A, U, hL, hP⟩ := FinalForm.unif R hRn hRi hcpl ξ hne
  have hB : GlobalTheory.Mum.Base R := ⟨⟨hRn, hRd, hRi, hcpl⟩, inferInstance⟩
  have hGs : IsSemiAbelian ((Over.pullback ξ).obj FinalForm.G) := IsSemiAbelian.pullback _ FinalForm.G FinalForm.semi
  obtain ⟨hsb, hpr, huniq, hlb⟩ := hs
  choose f hf using matOn_exists o' Ω S ρ M U₀ EE FinalForm hO.ne c.A pr hpr huniq
  have hfm : ∀ a b, IsMonHom ((Over.pullback ξ).map (f a b)) := fun a b => by
    have := (hf a b).1
    infer_instance
  choose m hmc using fun a b => endChar_exists_of_isMonHom R hB _ hGs D A U _ (hfm a b)
  obtain ⟨Λ, _, p, c', hc', hall⟩ := GlobalTheory.Poinc.Periods.one_lattice D W hW m
    (fun T ψ => IsLocalHom ψ ∧ ThroughU M V v (𝟙 F.X) T (spMap (ψ.comp φ) ≫ M.Z.fromSpecStalk x))
    (fun T ψ hT => by
      obtain ⟨hl, ht⟩ := hT
      have e : spMap (ψ.comp φ) ≫ M.Z.fromSpecStalk x = spMap ψ ≫ ξ := by
        rw [hξ, ← Category.assoc]
        congr 1
        exact Spec.map_comp (CommRingCat.ofHom φ) (CommRingCat.ofHom ψ)
      rw [e] at ht
      exact GlobalTheory.Poinc.Periods.trait_iso g n o ζ F W hW o' Ω S ρ u c pr ⟨hsb, hpr, huniq, hlb⟩ M U₀ EE FinalForm hO V v hv f hf R hB ξ
        D A U hL hP m hmc T ψ hl ht)
  exact ⟨R, inferInstance, hRd, hloc, φ, Λ, inferInstance, p, c', hB, isCpl_self _, hc', fun T ψ hl ht => hall T ψ ⟨hl, ht⟩⟩
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem _root_.GlobalTheory.T.traitExistsAfterFiniteExtension_of_completeDVR : TraitExtSt := by
  first | exact @GlobalTheory.Poinc.traitExtSt | exact GlobalTheory.Poinc.traitExtSt | (intros; apply GlobalTheory.Poinc.traitExtSt <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.e8Power_fibre_conjugate_evaluation_iso : ∀ (g l : ℕ), l.Prime → Odd l → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → ∀ (V V₁ : Type) [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → IsUnit (l : V₁) → ∀ (Q : Data V), Q.g ≤ g → ∀ (ρ : V →+* V₁), Function.Injective ρ → ∀ (D : DegPre V₁) (e : (Fin 8 → Q.X) ≃+ D.X), SharpRef W Q ρ D e → ∀ (C : Type) (u : (Fin 8 → Q.X) → C → V₁) (mo : (Fin 8 → Q.X) → V₁), (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → IsThetaTerms D ((l ^ j) ^ 2) e (fun mu c => u mu c * mo mu) → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ mu c c', IsUnit (u mu c') → ∃ r ∈ k₀, ev (u mu c) = r * ev (u mu c')) → ∀ (σ : K ≃+* K), (∀ r ∈ k₀, σ r = r) → ∃ (f : ((Over.pullback (spMap ev)).obj D.P.A).left ⟶ ((Over.pullback (spMap (σ.toRingHom.comp ev))).obj D.P.A).left), IsGrpPullback ((Over.pullback (spMap ev)).obj D.P.A) ((Over.pullback (spMap (σ.toRingHom.comp ev))).obj D.P.A) (𝟙 _) f ∧ LBIso (D.P.L.pull (pullback.fst D.P.A.hom (spMap ev))) (D.P.L.pull (f ≫ pullback.fst D.P.A.hom (spMap (σ.toRingHom.comp ev)))) ∧ (∀ (y : Over.mk (spMap ev) ⟶ D.P.A), (∃ k : ℕ, y ^ (l ^ k) = 1) → ∀ q : Sp K ⟶ ((Over.pullback (spMap ev)).obj D.P.A).left, q ≫ pullback.fst D.P.A.hom (spMap ev) = y.left → q ≫ pullback.snd D.P.A.hom (spMap ev) = 𝟙 _ → q ≫ f ≫ pullback.fst D.P.A.hom (spMap (σ.toRingHom.comp ev)) = spMap σ.toRingHom ≫ y.left) ∧ (∀ mu (q : Sp K ⟶ ((Over.pullback (spMap ev)).obj D.P.A).left), q ≫ pullback.fst D.P.A.hom (spMap ev) = spMap ev ≫ (D.c (e mu)).left → q ≫ pullback.snd D.P.A.hom (spMap ev) = 𝟙 _ → q ≫ f ≫ pullback.fst D.P.A.hom (spMap (σ.toRingHom.comp ev)) = spMap σ.toRingHom ≫ q ≫ pullback.fst D.P.A.hom (spMap ev)) := by
  first
  | exact @GlobalTheory.Poinc.Sep.sharp_fibre_conj_iso
  | intro g l hl hlo W hW
    obtain ⟨jB, hB⟩ := GlobalTheory.T.theta_series_sharp_reference_sixteen_terms g l hl hlo W hW
    obtain ⟨jD, hD⟩ := GlobalTheory.T.fibre_iso_carries_sharp_points_to_conjugates g l hl hlo W hW
    refine ⟨max jB jD, fun j hj V V₁ _ _ _ _ _ hCN hlU Q hQg ρ hρ D e hS C u mo hmo hT K _ _ ev k₀ hk₀ hr σ hσ => ?_⟩
    obtain ⟨f, h0, h1, h2⟩ :=
      hB j (le_of_max_le_left hj) V V₁ hCN hlU Q hQg ρ hρ D e hS C u mo hmo hT K ev k₀ hk₀ hr σ hσ
    exact ⟨f, h0, h1, h2,
      hD j (le_of_max_le_right hj) V V₁ hCN hlU Q hQg ρ hρ D e hS C u mo hmo hT K ev k₀ hk₀ hr σ hσ f h0 h1
        (fun y hy => h2 y ⟨j * 2, by rw [pow_mul]; exact hy⟩)⟩
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_polarisationSection_ratio_integralThetaFamily : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (F₁ : IntFam (maximalIdeal R) D.toPre 1), ∃ θ₀ : SecK C.P.L.L C.α 1, ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ a b : W, a ≠ 0 ∧ b ≠ 0 ∧ T.Exp a b θ₀ F₁ := by
  first | exact @GlobalTheory.Mum.exists_sec_exp_intFam_one | exact GlobalTheory.Mum.exists_sec_exp_intFam_one | (intros; apply GlobalTheory.Mum.exists_sec_exp_intFam_one <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.UCanon.LowPull.exists_lowObj_cdvr : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (C : MonoFam Xo c φ R) (Cn : Canon C), ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ θ₁ θ₂ : R →+* V, Function.Injective θ₁ → Function.Injective θ₂ → IsLocalHom θ₁ → IsLocalHom θ₂ → ∀ κ₁ κ₂ : Sp (FractionRing V) ⟶ Sp (FractionRing R), κ₁ ≫ jK R = jK V ≫ spMap θ₁ → κ₂ ≫ jK R = jK V ≫ spMap θ₂ → κ₁ ≫ C.y = κ₂ ≫ C.y → ∃ (o' : LowObj Cn.D' c ((θ₁.comp (Cn.ψ.comp MvPolynomial.C)).comp Cn.L.b)) (m₁ : ObjMap o' Cn.L.o (spMap (θ₁.comp (Cn.ψ.comp MvPolynomial.C)))) (m₂ : ObjMap o' Cn.L.o (spMap (θ₂.comp (Cn.ψ.comp MvPolynomial.C)))) (x : Cn.L.D.X → (Sp V ⟶ o'.t.G.left)), (∀ y, x y ≫ m₁.toSABMap.φ ≫ Cn.L.φB = spMap (θ₁.comp (Cn.ψ.comp MvPolynomial.C)) ≫ (Cn.L.D.c y).left) ∧ (∀ y, x y ≫ m₂.toSABMap.φ ≫ Cn.L.φB = spMap (θ₂.comp (Cn.ψ.comp MvPolynomial.C)) ≫ (Cn.L.D.c y).left) ∧ ∀ y, x y ≫ o'.t.G.hom = 𝟙 _ := by
  intro E _ _ _ H Dw l Xo c φ hpq hφ hns R _ _ _ hR C Cn V _ _ _ hV θ₁ θ₂ hθ₁ hθ₂ hl₁ hl₂ κ₁ κ₂ hκ₁ hκ₂ hy
  obtain ⟨hdvr, hc, hch⟩ := hV
  haveI := hdvr
  haveI := hch
  have hb : θ₁.comp C.b = θ₂.comp C.b := LowPull.comp_b_eq C.toFam θ₁ θ₂ κ₁ κ₂ hκ₁ hκ₂ hy
  obtain ⟨D₁, D₂, hD₁, hD₂, j₁, j₂, b, φ', he₁, he₂, hM, hlin, hQ, hbl⟩ :=
    GlobalTheory.UInj.pair_match Xo c φ R hR C.toFam V hc θ₁ θ₂ hθ₁ hθ₂ hl₁ hl₂ κ₁ κ₂ hκ₁ hκ₂ hy
  have hlat := GlobalTheory.T.canonicalFamily_latticeIdentification_eq_id Xo c φ hpq hφ hns R hR C Cn V hc θ₁ θ₂ hθ₁ hθ₂ hl₁ hl₂ D₁ D₂ hD₁ hD₂ j₁ j₂ b φ' he₁ he₂ hM
    hlin hQ
  exact LowPull.exists_pull₂ Cn.L V _ _ (GlobalTheory.T.canonicalFamily_base_eq_of_matching_pullbacks Xo c φ R hR C Cn V hc θ₁ θ₂ hθ₁ hθ₂ hl₁ hl₂ D₁ D₂ hD₁ hD₂ j₁ j₂ b φ'
    he₁ he₂ hM hQ hbl hlat hb)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.degeneratingFamily_data_from_base_algClosed_residue : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → IsAlgClosed (ResidueField V) → ∀ (C : MonoFam Xo c φ V), Nontrivial C.P.D.toPre.X → ∃ (D' : Datum H) (L : LowBase D' c) (θ₀ : L.W →+* V) (N : ℕ) (ε : Module.Basis (Fin C.m ⊕ Fin N) ℤ (balForms H.bar L.D.X)) (e : C.P.D.toPre.X ≃ₗ[𝓞 E] L.D.X) (s : Fin C.m ⊕ Fin N → V), D'.p + Module.finrank (𝓞 E) C.P.D.toPre.X = Dw.p ∧ D'.q + Module.finrank (𝓞 E) C.P.D.toPre.X = Dw.q ∧ IsLocalHom θ₀ ∧ θ₀.comp L.b = C.b ∧ (∀ i, C.δ i = pull e.toLinearMap (ε (.inl i) : LinearMap.BilinForm ℤ L.D.X)) ∧ (∀ i, Associated (s (.inl i)) (C.s i)) ∧ (∀ j, IsUnit (s (.inr j))) ∧ DivFrom L C.P.D.toPre C.P.oD θ₀ s (fun k => (ε k : LinearMap.BilinForm ℤ L.D.X)) e := by
  first | exact @GlobalTheory.VData.exists_divFrom | exact GlobalTheory.VData.exists_divFrom | (intros; apply GlobalTheory.VData.exists_divFrom <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.qkPoint_galois_fixed_up_to_equiv_divided_data : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (iw : L.W →+* R) {I : Type} [Fintype I] (s : I → R) (ε : I → LinearMap.BilinForm ℤ L.D.X) (e : P.D.toPre.X ≃ₗ[𝓞 E] L.D.X), (∀ k, ε k ∈ balForms H.bar L.D.X) → (∀ k, s k ≠ 0) → DivFrom L P.D.toPre P.oD iw s ε e → ∀ (σ : AlgebraicClosure (FractionRing R) ≃ₐ[FractionRing R] AlgebraicClosure (FractionRing R)) (p p' : QkPt P.D.toPre (AlgebraicClosure (FractionRing R)) l.M'), QkExt σ.toAlgHom.toRingHom p p' → QkPt.Equiv P.D.toPre (AlgebraicClosure (FractionRing R)) p p' := by
  first | exact @GlobalTheory.DivGalFix.qkExt_equiv_of_divFrom | exact GlobalTheory.DivGalFix.qkExt_equiv_of_divFrom | (intros; apply GlobalTheory.DivGalFix.qkExt_equiv_of_divFrom <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

theorem _root_.GlobalTheory.T.exists_unitaryThetaSystem_classicalTraits_closedPoint : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z), IsClosed ({z₁} : Set X₁.M.Z) → ∃ (Φ : FPre (H.bar : 𝓞 E → 𝓞 E) (min Dw.p Dw.q) p (X₁.M.Z.presheaf.stalk z₁)), UMatches Φ ∧ Φ.abelian₂ ∧ (∀ y, ∃ t : UCTrait X₁ p z₁, (∀ a, Φ.ev y a = t.val a) ∧ ∃ e : Φ.X y ≃ₗ[𝓞 E] t.T.P.D.toPre.X, ∀ a b, Φ.sc y * Φ.β y a b = t.sc * t.T.be (e a) (e b)) := by
  first | exact @GlobalTheory.UPoinc.PreSys.main | exact GlobalTheory.UPoinc.PreSys.main | (intros; apply GlobalTheory.UPoinc.PreSys.main <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.degenerationData_constant_of_flat_heatOperators : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre (bdParam k m d) gam → LinearIndependent ℤ gam → (∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal) → letI := H.starRing; ∀ (Y : Ray P.oD) (n' : ℕ) (v' : Module.Basis (Fin n') (ChartRing k m d) (TanM (𝟙 (Sp (ChartRing k m d))) Y.H)) (dd : Fin n' → Fld Y.H.left), (∀ a, IsInv Y.H (v' a) (dd a)) → ∀ (D : Derivation ℤ (ChartRing k m d) (ChartRing k m d)) (q : Fin m → ChartRing k m d), (∀ i, D (bdParam k m d i) = q i * bdParam k m d i) → ∀ h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D, IsBasic Y h → HasDefect Y h (fun _ _ _ => 0) → (∀ a b, h.Θ a b ∈ maximalIdeal (ChartRing k m d)) → ∀ ρ : ChartRing k m d →+* DualNumber k, (∀ r, ρ r = TrivSqZeroExt.inl (MvPowerSeries.constantCoeff r) + TrivSqZeroExt.inr (MvPowerSeries.constantCoeff (D r))) → ∃ c : ℚ, c ≠ 0 ∧ IsConstAlong P.D.toPre (bdParam k m d) gam ρ (fun i => (c : k) * MvPowerSeries.constantCoeff (q i)) := by
  first | exact @GlobalTheory.KSFlatPer.isConstAlong_of_heat_flat | exact GlobalTheory.KSFlatPer.isConstAlong_of_heat_flat | (intros; apply GlobalTheory.KSFlatPer.isConstAlong_of_heat_flat <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.USep

theorem _root_.GlobalTheory.T.thetaMember_of_unitary_monomial_uniformisation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c), ∀ (X₁ : GlobalTheory.GSep.GSet) (act : 𝓞 E → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (u : Sp (ratHull X₁.S.R) ⟶ Xo.XF c) (π : X₁.M.Z ⟶ C.Z), GlobalTheory.GSep.ULink C X₁ act u π → ∀ (z₁ : X₁.M.Z) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → ∀ (t : SAB H (Sp V)) (y : Sp (FractionRing V) ⟶ Xo.XF c) (P : PELUnif (maximalIdeal V) t), GenOf Xo c y t → ∀ (m : ℕ) (s : Fin m → V) (β : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre s β → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (ρ : V →+* V₁) (fK : FractionRing V →+* FractionRing V₁) (r : Fin m → V₁), IsCN V₁ → Function.Injective ρ → IsLocalHom ρ → (∀ a, fK (algebraMap V _ a) = algebraMap V₁ _ (ρ a)) → (∀ k, r k ^ 2 = ρ (s k)) → ∀ ev : X₁.M.Z.presheaf.stalk z₁ →+* V₁, IsLocalHom ev → GlobalTheory.GSep.RegAt X₁ z₁ ev → jK V₁ ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁ ≫ π = spMap fK ≫ y ≫ C.i → ∃ (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V₁ ev (Fin 1 → P.D.toPre.X) (mono !![(1 : ℤ)] r β) (fun a mu => a • mu)) (p : IsPullDeg ρ P.D.toPre 𝔪.D.toPre), ∀ mu, p.xe (𝔪.e₈ mu) = mu 0 := by
  first | exact @GlobalTheory.USep.member_of_monomial_unif | exact GlobalTheory.USep.member_of_monomial_unif | (intros; apply GlobalTheory.USep.member_of_monomial_unif <;> assumption)
end
