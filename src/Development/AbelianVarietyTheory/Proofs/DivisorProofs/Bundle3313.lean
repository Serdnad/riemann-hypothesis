module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle073
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle075
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3102
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3246
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3103
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3302
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle076
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle074
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle071
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3301
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3145
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3155
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3273
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3303
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3307
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3215
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3305
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle129
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle131
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle077
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3248
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3304
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.PicardGroup
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068
import Mathlib.Tactic.Polynomial.Basic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3104
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep

theorem _root_.GlobalTheory.T.geometric_fibre_thetaConstants_ratios_mem_subfield : ∀ (g n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → (∀ m : ℕ, m ≠ 0 → IsUnit (m : V₁)) → ∀ (D : DegPre V₁), D.P.g = g → ∀ (X C : Type) [AddCommGroup X] (e : X ≃+ D.X) (u : X → C → V₁) (mo : X → V₁), (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → GlobalTheory.Poinc.Sep.IsThetaTerms D ((n ^ j) ^ 2) e (fun mu c => u mu c * mo mu) → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ mu c c', IsUnit (u mu c') → ∃ r ∈ k₀, ev (u mu c) = r * ev (u mu c')) → ∀ (o : Type) [CommRing o] (J : Type) (b : ZM.TBase o ((n ^ j) ^ 2)) (s : Sp K ⟶ Sp o) (t : ZM.TObj g ((n ^ j) ^ 2) J b s) (π₁ : t.A.left ⟶ D.P.A.left), IsGrpPullback t.A D.P.A (spMap ev) π₁ → LBIso t.L (D.P.L.pull π₁) → ∀ v : ZM.Ix g ((n ^ j) ^ 2) → K, t.HasTh (𝟙 _) v → ∀ a a', v a' ≠ 0 → ∃ r ∈ k₀, v a = r * v a' := by
  first | exact @GlobalTheory.Poinc.Sep.ModelRatio.main | exact GlobalTheory.Poinc.Sep.ModelRatio.main | (intros; apply GlobalTheory.Poinc.Sep.ModelRatio.main <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.Recognition

theorem pullDeg_induces : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (lab : Labels D.toPre A), ∀ n : ℕ, n.Prime → Odd n → IsUnit (n : R) → OneTrait D.toPre A lab → GalEqN n lab → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (φ : R →+* W), Function.Injective φ → IsLocalHom φ → ∀ (G' : Over (Sp W)) [GrpObj G'] [IsCommMonObj G'] (D' : DegData W (maximalIdeal W)) (A' : PolAV (Sp (FractionRing W))) (U' : Unif (maximalIdeal W) D' A' G') (a : A'.A.left ⟶ A.A.left), IsSemiAbelian G' → IsFib φ A A' a → ∃ hD : IsPullDeg φ D.toPre D'.toPre, ∀ j : ℕ, Induces lab φ U' hD a (n ^ j) := by
  intro R _ _ _ hR D A lab n hn ho hu hOT hGal W _ _ _ hW φ hφ hloc G' _ _ D' A' U' a hG hF
  obtain ⟨hD, C, i1, i2, i3, i4, em, hc, hP⟩ := GlobalTheory.T.galois_equivariant_torsion_values_ultrametric R hR D A lab n hn ho hu hOT hGal
    (GlobalTheory.T.isThetaPoint_of_algebraic_series_one_trait R hR D A lab n hn ho hu hOT) W hW φ hφ hloc G' D' A' U' a hG hF
  exact ⟨hD, fun j => GlobalTheory.T.labels_induced_all_embeddings_of_galois R hR D A lab n hn ho hu hGal W hW φ hφ hloc G' D' A' U' a hG hF hD j
    ⟨C, i1, i2, i3, i4, em, hc, hP j⟩⟩

end GlobalTheory.Mum.Recognition
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.Sep

theorem sharp_fibre_theta_object : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (gQ : ℕ), ∃ (J : Type) (_ : Finite J)
    (Mat : J → Matrix (Fin (2 * (8 * gQ))) (Fin (2 * (8 * gQ))) ℤ) (κ : ℕ) (w w' : J),
  ∀ (l : ℕ), l.Prime → Odd l → ∀ j : ℕ, 1 ≤ j →
  ∀ (V V₁ : Type) [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → IsUnit (l : V₁) →
  ∀ (Q : Data V), Q.g = gQ → ∀ (ρ : V →+* V₁), Function.Injective ρ → ∀ (D : DegPre V₁) (e : (Fin 8 → Q.X) ≃+ D.X),
  SharpRef W Q ρ D e → ∀ (C : Type) (u : (Fin 8 → Q.X) → C → V₁) (mo : (Fin 8 → Q.X) → V₁),
  (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → IsThetaTerms D ((l ^ j) ^ 2) e (fun mu c => u mu c * mo mu) →
  ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ →
  (∀ mu c c', IsUnit (u mu c') → ∃ r ∈ k₀, ev (u mu c) = r * ev (u mu c')) →
  ∃ (bT : TBase k₀ ((l ^ j) ^ 2)) (t : TObj (8 * gQ) ((l ^ j) ^ 2) J bT (spMap k₀.subtype))
    (v : Ix (8 * gQ) ((l ^ j) ^ 2) → k₀) (ψ : ((Over.pullback (spMap ev)).obj D.P.A).left ⟶ t.A.left),
    t.Shape Mat κ ∧ t.Prim w w' ∧ t.HasTh (𝟙 _) (fun a => k₀.subtype (v a)) ∧
    IsGrpPullback ((Over.pullback (spMap ev)).obj D.P.A) t.A (𝟙 _) ψ ∧
    LBIso (D.P.L.pull (pullback.fst D.P.A.hom (spMap ev))) (t.L.pull ψ) ∧
    ∀ (y : Over.mk (spMap ev) ⟶ D.P.A), y ^ ((l ^ j) ^ 2) = 1 →
      ∀ q : Sp K ⟶ ((Over.pullback (spMap ev)).obj D.P.A).left,
      q ≫ pullback.fst D.P.A.hom (spMap ev) = y.left → q ≫ pullback.snd D.P.A.hom (spMap ev) = 𝟙 _ →
      ∃ a, q ≫ ψ = (t.lab a).left := by
  intro W hW gQ
  obtain ⟨J, hJ, Mat, κ, w, w', hA⟩ := GlobalTheory.T.sharp_refinement_odd_prime_localization W hW gQ
  refine ⟨J, hJ, Mat, κ, w, w', ?_⟩
  intro l hl ho j hj V V₁ _ _ _ _ _ hCN hu Q hQ ρ hρ D e hS C u mo hmo hT K _ _ ev k₀ hk₀ hr
  obtain ⟨bT, t, ψ, h1, h2, h3, h4, h5⟩ := hA l hl ho j hj V V₁ hCN hu Q hQ ρ hρ D e hS K ev k₀ hk₀
  obtain ⟨v, hv⟩ := GlobalTheory.T.sharp_refinement_coefficient_family W hW gQ J l hl ho j hj V V₁ hCN hu Q hQ ρ hρ D e hS C u mo hmo hT K ev k₀ hk₀ hr bT t ψ h3 h4
  exact ⟨bT, t, v, ψ, h1, h2, hv, h3, h4, h5⟩

end GlobalTheory.Poinc.Sep
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Poinc Formalism.L2.Pj

theorem _root_.GlobalTheory.T.eighthPower_trait_uniformisation_lattice_pow_eight : (∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (T : Trait F) (P : PolAV (Sp (FractionRing T.V))) (ε : Matrix (Fin 8) (Fin 8) ℤ → (P.A ⟶ P.A)), IsDiagEnd F W P T.y ε → ∃ (G' : Over (Sp T.V)) (_ : GrpObj G') (_ : IsCommMonObj G'), IsSemiAbelian G' ∧ ∃ (D' : DegData T.V (maximalIdeal T.V)) (U' : Unif (maximalIdeal T.V) D' P G') (j : D'.toPre.X ≃+ (Fin 8 → T.D.toPre.X)), (∀ y, ∃ v : T.Vˣ, PsiCoord D'.toPre y (v * T.ϖ ^ (qW W T.β (j y)).toNat)) ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra (FractionRing T.V) K] (m : ℕ) (pk pk' : QkPt D'.toPre K m) (x x' : TFK (R := T.V) K ⟶ P.A) (E : Matrix (Fin 8) (Fin 8) ℤ), 1 ≤ m → QkToAkU U'.toUnifPre K m pk x → QkToAkU U'.toUnifPre K m pk' x' → x' = x ≫ ε E → CongMod m (j pk'.y) (fun a => ∑ b, E a b • j pk.y b)) := by
  first | exact @GlobalTheory.EighthTorsion.main | exact GlobalTheory.EighthTorsion.main | (intros; apply GlobalTheory.EighthTorsion.main <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.thetaExpansionScalars_ratio_odd_mul : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (m : ℕ), Odd m → ∀ Φ : IntFam (maximalIdeal R) D.toPre (m ^ 2) → SecK C.P.L.L C.α (m ^ 2), (∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ u : Wˣ, ∀ F, T.Exp 1 u (Φ F) F) → ∀ (F₁ : IntFam (maximalIdeal R) D.toPre 1) (θ₀ : SecK C.P.L.L C.α 1), (∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ a b : W, a ≠ 0 ∧ b ≠ 0 ∧ T.Exp a b θ₀ F₁) → ∃ r t : R, r ≠ 0 ∧ t ≠ 0 ∧ ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ (a b : W) (v : Wˣ), a ≠ 0 ∧ b ≠ 0 ∧ T.Exp a b θ₀ F₁ ∧ b * T.φ t = a * T.φ r * v := by
  first | exact @GlobalTheory.Mum.ratio_odd_mul | exact GlobalTheory.Mum.ratio_odd_mul | (intros; apply GlobalTheory.Mum.ratio_odd_mul <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_ext_normalised_blowup : ∀ g : ℕ, 1 ≤ g → ∀ φ : InvFun ℤ, IsPolFan id g φ → NoSelfInt id g φ → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) (OZ : LB Z) (d : ℕ) (S : Scheme.{0}) (π : S ⟶ Z) (j : F.X ⟶ S) [IsOpenImmersion j] (BD : GlobalTheory.EffCartierData S), MinAt5 F z i OZ → BlowAt F z i φ d π j BD → ∀ (C : Taut (zetaAway n) g n φ) (G₁ : Over (Sp C.R)) [GrpObj G₁] (y : Sp (FractionRing C.R) ⟶ F.X) (α₁ : pullback G₁.hom (jK C.R) ⟶ F.univ.A.left), C.IsFam F G₁ y α₁ → ∃ ξ : Sp C.R ⟶ S, y ≫ j = jK C.R ≫ ξ := by
  first | exact @GlobalTheory.TChart.Taut.exists_ext_normBl | exact GlobalTheory.TChart.Taut.exists_ext_normBl | (intros; apply GlobalTheory.TChart.Taut.exists_ext_normBl <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.UT GlobalTheory.FieldBaseChange

namespace GlobalTheory.USep.Coef

theorem ev_units_zpow {V K : Type} [CommRing V] [Field K] (f : V →+* K) (v : Vˣ) (n : ℤ) :
    f ((v ^ n : Vˣ) : V) = f v ^ n := by
  have h1 : f ((v ^ n : Vˣ) : V) = ((Units.map f.toMonoidHom (v ^ n) : Kˣ) : K) := rfl
  rw [h1, map_zpow, Units.val_zpow_eq_zpow_val]
  rfl

theorem coef_sq_mem_monomial : ∀ (N₁ : ℕ), 2 ≤ N₁ → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → (∀ m : ℕ, m ≠ 0 → IsUnit (m : V₁)) → ∀ (D : DegPre V₁), D.PsiEven → D.TauBimult → ∀ (X C : Type) [AddCommGroup X] (e : X ≃+ D.X) (u : X → C → V₁) (mo : X → V₁), (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → GlobalTheory.Poinc.Sep.IsThetaTerms D N₁ e (fun mu c => u mu c * mo mu) → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → ∀ (τ₀ : GlobalTheory.UChart.Gens D) (m N : ℕ) (s : Fin m ⊕ Fin N → V₁) (ε : Fin m ⊕ Fin N → LinearMap.BilinForm ℤ D.X), (∀ k, IsUnit (s (.inr k))) → GlobalTheory.UChart.TauIn D τ₀ (fun k => s (finSumFinEquiv.symm k)) (fun k => ε (finSumFinEquiv.symm k)) → (∀ mu, algebraMap V₁ (FractionRing V₁) (mo mu) ^ 2 = ∏ k, algebraMap V₁ (FractionRing V₁) (s (.inl k)) ^ ε (.inl k) (e mu) (e mu)) → ∀ (W₀ : Type) [CommRing W₀] (ib : W₀ →+* V₁), GlobalTheory.UChart.FromBase D τ₀ ib → (∀ a, ev (ib a) ∈ k₀) → ∀ mu c, ∃ r ∈ k₀, ev (u mu c) ^ 2 = r * ∏ k, ev (s (.inr k)) ^ ε (.inr k) (e mu) (e mu) := by
  intro N₁ hN V₁ _ _ _ hV hunit D hpe htb X C _ e u mo hmo hT K _ _ ev k₀ hk₀ τ₀ m N s ε hs hτ hmo2 W₀ _ ib hB hib mu c
  obtain ⟨θ, b, t, χt, s₀, G, hθ, hb, ht, hχt, hs₀, hG, hGf⟩ :=
    GlobalTheory.T.integral_squaredThetaTerms_torusCoordinates N₁ hN V₁ hV hunit D hpe htb X C e u mo hmo hT τ₀ m N s ε hs hτ hmo2
  obtain ⟨Λ, hΛ⟩ := GlobalTheory.T.integral_expression_values_at_descended_point N₁ hN V₁ hV hunit D X C e τ₀ θ hθ b hb t ht χt hχt G hGf K ev k₀ hk₀ W₀ ib hB hib
  obtain ⟨-, -, -, -, -, -, -, -, -, c₀, hc₀⟩ := hT
  have hc₀' : u 0 c₀ * mo 0 = 1 := hc₀
  have hm0 : mo 0 ^ 2 = 1 := by
    have h := hmo2 0
    simp only [map_zero, LinearMap.map_zero₂, zpow_zero, Finset.prod_const_one] at h
    exact IsFractionRing.injective V₁ (FractionRing V₁) (by simpa using h)
  have hu0 : u 0 c₀ ^ 2 = 1 := by
    have h := congrArg (· ^ 2) hc₀'
    simpa only [mul_pow, hm0, _root_.mul_one, one_pow] using h
  have hP0 : ((∏ k, (hs k).unit ^ ε (.inr k) (e 0) (e 0) : V₁ˣ) : V₁) = 1 := by
    simp only [map_zero, LinearMap.map_zero₂, zpow_zero, Finset.prod_const_one, Units.val_one]
  have h0 : s₀ = G 0 c₀ := by
    have h := hG 0 c₀
    rw [hu0, _root_.one_mul, hP0, _root_.one_mul] at h
    exact h
  obtain ⟨r₀, hr₀, e₀⟩ := hΛ 0 c₀
  obtain ⟨r, hr, e₁⟩ := hΛ mu c
  have hev0 : ev s₀ ≠ 0 := (hs₀.map ev).ne_zero
  have hΛr₀ : Λ * r₀ ≠ 0 := by rw [← e₀, ← h0]; exact hev0
  have hr₀0 : r₀ ≠ 0 := right_ne_zero_of_mul hΛr₀
  have hΛ0 : Λ ≠ 0 := left_ne_zero_of_mul hΛr₀
  refine ⟨r / r₀, k₀.div_mem hr hr₀, ?_⟩
  have h := congrArg ev (hG mu c)
  rw [map_mul, map_mul, map_pow, e₁, h0, e₀, Units.coe_prod, map_prod] at h
  simp only [ev_units_zpow, IsUnit.unit_spec] at h
  field_simp
  apply mul_left_cancel₀ hΛ0
  linear_combination h

end GlobalTheory.USep.Coef
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem gs_liftFun_top {S0 : Scheme.{0}} (A : Over S0) {T : Over S0} (W : (T ⊗ A).left.Opens) (r : Γ(T.left, ⊤))
    {Z : Scheme.{0}} (q : Z ⟶ (T ⊗ A).left) (z : Z) (hz : q z ∈ W) :
    gs q z W (liftFun A W r) = gs (q ≫ (fst T A).left) z ⊤ r :=
  (gs_res q z le_top hz _).trans (gs_pull q (fst T A).left z ⊤ trivial r)

theorem fvalue_const : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (j : ℕ) (wA : LB.Iso C.A.L (C.P.L.L.pull C.α)), wA.IsGen → ∀ E₀ (Φ₀ : IntFam (maximalIdeal R) D.toPre (C.n ^ j) → H0 C.A.L (C.n ^ j)), Eqv D.toPre C.A (Kb R) (C.n ^ j) (C.lab j) E₀ → (∀ F₀ s, F₀.Over s → Agree C.A.L (E₀ s) (Φ₀ F₀)) → ∀ (Φ : IntFam (maximalIdeal R) D.toPre (C.n ^ j) → SecK C.P.L.L C.α (C.n ^ j)), (∀ F₀ (Z : Scheme.{0}) (p : Z ⟶ C.A.A.left) (z : Z) J J', Good C.P.L.L z J → Good C.A.L z J' → sval (Φ F₀) p z J = (gw wA p z (J (p ≫ C.α)) (J' p) ^ (C.n ^ j)).val * sval (Φ₀ F₀) p z J') → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F] (em : Kb R →ₐ[FractionRing R] F), (∀ r, algebraMap (FractionRing R) F (algebraMap R _ r) = algebraMap (FractionRing W) F (algebraMap W _ (T.φ r))) → ∃ c : F, c ≠ 0 ∧ ∀ (F₀ : IntFam (maximalIdeal R) D.toPre (C.n ^ j)) (σ : SecK C.P.L.L T.β (C.n ^ j)), T.ExpBy 1 σ F₀ → ∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ (TFK (R := R) F ⊗ C.A.A).left), p ≫ T.β = p' ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α → p ≫ T.G.hom = p' ≫ (fst (TFK (R := R) F) C.A.A).left ≫ spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _)) → ∀ z J, Good C.P.L.L z J → sval σ p z J = gs (p' ≫ (fst (TFK (R := R) F) C.A.A).left) z ⊤ (fnF F c) * sval (Φ F₀) (p' ≫ (snd (TFK (R := R) F) C.A.A).left) z J := by
  intro R _ _ _ hR D C j wA hwA E₀ Φ₀ hE₀ hΦ₀ Φ hΦ W _ _ _ T F _ _ _ _ em hem
  obtain ⟨lab, E, hlab, hE, hT⟩ := GlobalTheory.T.trait_inverse_expansion_equivariant_labels R hR D C j wA hwA W T F em hem
  have hodd : Odd (C.n ^ j) := C.n_odd.pow
  obtain ⟨E', hE', hAg⟩ := GlobalTheory.T.exists_equivariant_bijection_larger_closed_field R hR D C.A (C.n ^ j) hodd (C.lab j) E₀ Φ₀ hE₀ hΦ₀ F em lab hlab
  haveI : CharZero R := hR.2
  obtain ⟨c₀, hc₀⟩ := GlobalTheory.Mum.eqv_eq_smul R (maximalIdeal R) D C.A F (C.n ^ j) hodd lab E E' hE hE'
  refine ⟨(c₀ : F)⁻¹, inv_ne_zero c₀.ne_zero, ?_⟩
  intro F₀ σ hσ Z p p' h1 h2 z J hJ
  obtain ⟨s, hs, -⟩ := GlobalTheory.Mum.IntFam.existsUnique_over R (maximalIdeal R) D.toPre (C.n ^ j) F₀ F
  obtain ⟨J', hJ', -⟩ := exists_good C.A.L C.A.isLB z (K := Empty) (fun e => e.elim) (fun e => e.elim)
    (fun a => a.elim) (fun k => k.elim)
  set q := p' ≫ (snd (TFK (R := R) F) C.A.A).left with hq
  have e1 := hT F₀ s σ hs hσ Z p p' h1 h2 z J J' hJ hJ'
  have e2 : sval (E' s) p' z J' = gs (p' ≫ (fst (TFK (R := R) F) C.A.A).left) z ⊤ (fnF F (c₀ : F)) * sval (E s) p' z J' := by
    unfold sval
    refine (congrArg (gs p' z _) (hc₀ s _)).trans ?_
    exact (gs_mul p' z _ (hJ'.mem _ p') _ _).trans (congrArg (· * _) (gs_liftFun_top _ _ _ _ _ (hJ'.mem _ p')))
  have e3 := hAg F₀ s hs Z p' q (Category.comp_id _).symm z J' hJ'
  have e4 := hΦ F₀ Z q z J J' hJ hJ'
  have hβ : J (q ≫ C.α) = J (p ≫ T.β) := by rw [h1, hq, Category.assoc]
  rw [hβ] at e4
  have huv : gs (p' ≫ (fst (TFK (R := R) F) C.A.A).left) z ⊤ (fnF F (c₀ : F)⁻¹) *
      gs (p' ≫ (fst (TFK (R := R) F) C.A.A).left) z ⊤ (fnF F (c₀ : F)) = 1 := by
    rw [← gs_mul (p' ≫ (fst (TFK (R := R) F) C.A.A).left) z ⊤ trivial, fnF, fnF, ← map_mul, inv_mul_cancel₀ c₀.ne_zero,
      map_one, gs_eq (p' ≫ (fst (TFK (R := R) F) C.A.A).left) z ⊤ trivial, map_one, map_one]
  rw [e1, e4, ← e3, e2]
  linear_combination (-(gw wA q z (J (p ≫ T.β)) (J' q) ^ (C.n ^ j)).val * sval (E s) p' z J') * huv

end GlobalTheory.Mum
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.CanonTors

theorem galois_fixed : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (iw : W →+* R) {I : Type} [Fintype I] (s : I → R) (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ), IsCN R → 1 ≤ n → IsUnit (n : R) → ∀ ζ : R, IsPrimitiveRoot ζ n → ∀ (Q : Data R) (e : Q.X ≃+ (Fin T.r → ℤ)), DataFrom T iw s ε n Q e → TorsRat Q.B n → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left), Canon Q G P → ∀ (σ : AlgebraicClosure (FractionRing R) ≃ₐ[FractionRing R] AlgebraicClosure (FractionRing R)) (x : Over.mk (spMap (algebraMap (FractionRing R) (AlgebraicClosure (FractionRing R))) ≫ jK R) ⟶ G), x ^ n = 1 → spMap σ.toAlgHom.toRingHom ≫ x.left = x.left := by
  intro o W _ _ _ T R _ _ _ iw I _ s ε n hCN hn hnu ζ hζ Q e hD hQ G _ _ P hC σ x hx
  obtain ⟨-, D', F, A', G', _, _, U', oA, oG, inc, pr, hG', hlin, hinc, hpr, hip, hpi, -⟩ := hC
  haveI : CharZero R := hCN.2.2.2
  have hadm : AdmBase R (maximalIdeal R) := ⟨hCN.1, inferInstance, hCN.2.1, hCN.2.2.1⟩
  obtain ⟨y, hy0⟩ : ∃ y : (Over.map (jK R)).obj (TFK (R := R) (AlgebraicClosure (FractionRing R))) ⟶ G', y = x ≫ inc := ⟨_, rfl⟩
  obtain ⟨h, hh0⟩ : ∃ h : TFK (R := R) (AlgebraicClosure (FractionRing R)) ⟶ (Over.pullback (jK R)).obj G',
    h = (Over.mapPullbackAdj (jK R)).unit.app _ ≫ (Over.pullback (jK R)).map y := ⟨_, rfl⟩
  have hy : y ^ n = 1 := by
    rw [hy0, ← MonObj.pow_comp, hx, MonObj.one_comp]
  have hmp : ∀ m : ℕ, (Over.pullback (jK R)).map (y ^ m) = ((Over.pullback (jK R)).map y) ^ m := by
    intro m
    induction m with
    | zero => simp [Functor.map_one]
    | succ m ih => rw [pow_succ, Functor.map_mul, ih, pow_succ]
  have hh : h ^ n = 1 := by
    rw [hh0, ← MonObj.comp_pow, ← hmp, hy, Functor.map_one, MonObj.comp_one]
  haveI := U'.gen_hom
  obtain ⟨a, ha0⟩ : ∃ a : TFK (R := R) (AlgebraicClosure (FractionRing R)) ⟶ A'.A, a = h ≫ U'.gen.hom := ⟨_, rfl⟩
  have ha : a ^ n = 1 := by
    rw [ha0, ← MonObj.pow_comp, hh, MonObj.one_comp]
  have hye : y ≫ oG.act F.e = y := by
    rw [hy0, ← hpi, Category.assoc, ← Category.assoc inc, hip, Category.id_comp]
  have hae : a ≫ oA.act F.e = a := by
    rw [ha0, Category.assoc, ← hlin.ext, hh0]
    simp only [Category.assoc]
    rw [← Functor.map_comp_assoc, hye]
  obtain ⟨f, hT, -⟩ := GlobalTheory.TorsionIso.torsion_clause R (maximalIdeal R) hadm D' A' G' hG' U'
    (AlgebraicClosure (FractionRing R)) n hn
  obtain ⟨p, hp⟩ := hT.2.1 a ha
  obtain ⟨p₁, hy₁, hg₁, he₁⟩ := GlobalTheory.T.exists_equivalent_idempotent_image_fixed_torsion R hCN n hn hnu Q D' F A' G' U' oA oG hG' hlin a ha hae p ((hT.1 p a).2 hp.symm)
  have hf₁ : f p₁ = a := ((hT.2.2.1 p₁ p).2 he₁).trans hp
  obtain ⟨⟨p₁', hext⟩, hpt, hiff⟩ := GlobalTheory.UT.Cl.galois_holds R (maximalIdeal R) hadm D' A' G' hG' U'
    (AlgebraicClosure (FractionRing R)) (AlgebraicClosure (FractionRing R)) σ.toAlgHom n hn p₁
  obtain ⟨a', ha'⟩ := hpt a
  have h2 := (hiff p₁' a a' hext ha').1 ((hT.1 p₁ a).2 hf₁.symm)
  have heq := GlobalTheory.T.idempotent_image_nDividedPoint_galoisConj_equiv T R iw s ε n hCN hn hnu ζ hζ Q e hD hQ D' F A' G' U' oA oG hG' hlin σ p p₁ p₁' hy₁ hg₁ hext
  have haa : a' = a := ((hT.1 p₁' a').1 h2).trans (((hT.2.2.1 p₁ p₁').2 heq).symm.trans hf₁)
  rw [haa] at ha'
  have e1 : (Over.mapPullbackAdj (jK R)).homEquiv _ _ y = h := by rw [Adjunction.homEquiv_unit, hh0]
  have hyl : y.left = h.left ≫ ((Over.mapPullbackAdj (jK R)).counit.app G').left := by
    have e2 : y = (Over.map (jK R)).map h ≫ (Over.mapPullbackAdj (jK R)).counit.app G' := by
      conv_lhs => rw [← ((Over.mapPullbackAdj (jK R)).homEquiv _ _).symm_apply_apply y, e1]
      exact Adjunction.homEquiv_counit _ _ _ _
    rw [e2, Over.comp_left]
    rfl
  have hhl : spMap σ.toAlgHom.toRingHom ≫ h.left = h.left := by
    have := congrArg (· ≫ U'.gen.inv.left) ha'
    simp only [ha0, Over.comp_left, Category.assoc] at this
    rw [← Over.comp_left _ _ _ U'.gen.hom U'.gen.inv, Iso.hom_inv_id, Over.id_left, Category.comp_id] at this
    exact this.symm
  have hyx : spMap σ.toAlgHom.toRingHom ≫ y.left = y.left := by
    rw [hyl, ← Category.assoc, hhl]
  have := congrArg (· ≫ pr.left) hyx
  simp only [hy0, Over.comp_left, Category.assoc] at this
  rw [← Over.comp_left _ _ _ inc pr, hip, Over.id_left, Category.comp_id] at this
  exact this
end GlobalTheory.Mum.CanonTors
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

theorem _root_.GlobalTheory.T.canonicalFamily_bundle_birigid_symmetric : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (Q : Data R) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left), Canon Q G P → IsBiRig G P := by
  first | exact @GlobalTheory.Mum.canon_isBiRig | exact GlobalTheory.Mum.canon_isBiRig | (intros; apply GlobalTheory.Mum.canon_isBiRig <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

theorem _root_.GlobalTheory.T.exists_tautological_point_torus_extension : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) {I : Type} [Fintype I] (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ) (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (ω : W →+* V) (s : I → V) (e : D.X ≃+ (Fin T.r → ℤ)) (β : D.P.A.left ⟶ T.B.left) (ββ : (G2 D.P.A).left ⟶ (G2 T.B).left) (w : LB.Iso (abelian₂ D.P.A D.P.L) ((abelian₂ T.B T.M.L).pull ββ)), D.TauBimult → From T ω s ε n D e β ββ w → (∀ i, s i ≠ 0) → ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (a : Fin T.r → ℤ), ∃ g : GtPtF D F, TautPt T ω s ε n D e β ββ w F a g := by
  first | exact @GlobalTheory.TInj.exists_tautPt | exact GlobalTheory.TInj.exists_tautPt | (intros; apply GlobalTheory.TInj.exists_tautPt <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RigBase

theorem grp_through {S S₁ S₂ : Scheme.{0}} {B' : Over S₂} {Q : Over S₁} {D O : Over S} [GrpObj B'] [GrpObj Q]
    [GrpObj D] [GrpObj O] {g : S₂ ⟶ S} {π : B'.left ⟶ Q.left} {β : Q.left ⟶ D.left} {φB : O.left ⟶ D.left}
    {ρ₁ : S₂ ⟶ S₁} {j : S₁ ⟶ S} (hπ : IsGrpPullback B' Q ρ₁ π) (hβ : IsGrpPullback Q D j β)
    (hφ : IsGrpPullback O D (𝟙 S) φB) (hg : ρ₁ ≫ j = g) :
    ∃ π' : B'.left ⟶ O.left, π' ≫ φB = π ≫ β ∧ π' ≫ O.hom = B'.hom ≫ g ∧ IsGrpPullback B' O g π' := by
  have hc := (hπ.comp hβ).congr hg rfl
  have w : (π ≫ β) ≫ D.hom = (B'.hom ≫ g) ≫ 𝟙 S := by rw [Category.comp_id]; exact hc.1.w
  exact ⟨hφ.1.lift (π ≫ β) (B'.hom ≫ g) w, hφ.1.lift_fst _ _ _, hφ.1.lift_snd _ _ _,
    hφ.cancel (hc.congr (Category.comp_id g).symm (hφ.1.lift_fst _ _ _).symm) (hφ.1.lift_snd _ _ _)⟩

theorem lb_through {X Y Z T : Scheme.{0}} {L₀ : LB X} {L : LB Y} {M : LB Z} (hL₀ : L₀.IsLB) (hL : L.IsLB)
    (hM : M.IsLB) {φB : X ⟶ Y} {β : Z ⟶ Y} {π₁ π₂ : T ⟶ Z} {π₁' π₂' : T ⟶ X} (h₀ : LBIso L₀ (L.pull φB))
    (hβ : LBIso M (L.pull β)) (h : LBIso (M.pull π₁) (M.pull π₂)) (e₁ : π₁' ≫ φB = π₁ ≫ β)
    (e₂ : π₂' ≫ φB = π₂ ≫ β) : LBIso (L₀.pull π₁') (L₀.pull π₂') := by
  have key : ∀ {A : Scheme.{0}} {L' : LB A} {F : A ⟶ Y}, LBIso L' (L.pull F) → ∀ j : T ⟶ A,
      LBIso (L'.pull j) (L.pull (j ≫ F)) := fun H j =>
    LBIso.chartPull (chartPullPull _ _) (chartPullSame L _ _ _ j fun _ => rfl) H
  have a₁ := key h₀ π₁'
  have a₂ := key h₀ π₂'
  have b₁ := key hβ π₁
  have b₂ := key hβ π₂
  rw [e₁] at a₁
  rw [e₂] at a₂
  exact LBIso.trans (pull_isLB hL₀ _) (pull_isLB hL _) (pull_isLB hL₀ _) (LBIso.trans (pull_isLB hL₀ _) (pull_isLB hM _) (pull_isLB hL _)
    (LBIso.trans (pull_isLB hL₀ _) (pull_isLB hM _) (pull_isLB hM _) (LBIso.trans (pull_isLB hL₀ _) (pull_isLB hL _) (pull_isLB hM _) a₁ b₁.symm) h) b₂) a₂.symm

theorem const_on_base : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (C : MonoFam Xo c φ R) (Cn : Canon C), ∀ (k : Type) [Field k] (ρ : R →+* DualNumber k) (a : Fin C.m → k), GlobalTheory.RigChart.IsConstAlong C.P.D.toPre C.s (fun i => (l.M' : ℤ) • C.δ i) ρ a → ρ.comp (Cn.ψ.comp MvPolynomial.C) = GlobalTheory.RigChart.constHom (ρ.comp (Cn.ψ.comp MvPolynomial.C)) := by
  intro E _ _ _ H Dw l Xo c φ R _ _ _ _ C Cn k _ ρ a hC
  obtain ⟨B', _, π₁, π₂, w, c', h₁, h₂, h0, hw, hc', -⟩ := hC
  obtain ⟨g, hD, -, hxe, -⟩ := Cn.data
  haveI := hD.e_hom
  have hβ : IsGrpPullback C.P.D.toPre.P.A Cn.L.D.P.A (specOf (Cn.ψ.comp MvPolynomial.C))
      (hD.e.hom.left ≫ pullback.fst Cn.L.D.P.A.hom (specOf (Cn.ψ.comp MvPolynomial.C))) :=
    ((isGrpPullback_of_iso hD.e).comp (isGrpPullback_pullback _ _)).congr (Category.id_comp _) rfl
  have hsp : ∀ ρ' : R →+* DualNumber k, spMap ρ' ≫ specOf (Cn.ψ.comp MvPolynomial.C) = spMap (ρ'.comp (Cn.ψ.comp MvPolynomial.C)) := fun ρ' => by
    rw [← Spec.map_comp]; rfl
  obtain ⟨π₁', e₁, w₁, g₁⟩ := grp_through h₁ hβ Cn.L.ab.1 (hsp ρ)
  obtain ⟨π₂', e₂, w₂, g₂⟩ := grp_through h₂ hβ Cn.L.ab.1
    (hsp _ : _ = spMap (GlobalTheory.RigChart.constHom (ρ.comp (Cn.ψ.comp MvPolynomial.C))))
  have hfst : spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ spMap (ρ.comp (Cn.ψ.comp MvPolynomial.C)) =
      spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ spMap (GlobalTheory.RigChart.constHom (ρ.comp (Cn.ψ.comp MvPolynomial.C))) := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
  have agree : ∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k),
      x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁' = x ≫ π₂' := by
    intro Z x y hx
    apply Cn.L.ab.1.1.hom_ext
    · rw [Category.assoc, Category.assoc, e₁, e₂, ← Category.assoc, ← Category.assoc, h0 Z x y hx]
    · rw [Category.assoc, Category.assoc, w₁, w₂, ← Category.assoc, ← Category.assoc, hx, Category.assoc,
        Category.assoc, hfst]
  obtain ⟨w₀, hw₀⟩ := Cn.L.ab.2.2
  have hLB : LBIso (Cn.L.o.t.PP.L.pull π₁') (Cn.L.o.t.PP.L.pull π₂') :=
    lb_through Cn.L.o.t.PP.isLB Cn.L.D.P.isLB C.P.D.toPre.P.isLB ⟨w₀, hw₀⟩ ⟨hD.w, hD.w_gen⟩ ⟨w, hw⟩ e₁ e₂
  obtain ⟨o', m₁, m₂, io, hio, hm₁, hm₂⟩ :=
    GlobalTheory.T.exists_objectMaps_of_dualNumber_identifications c Cn.L.W Cn.L.b Cn.L.o k (ρ.comp (Cn.ψ.comp MvPolynomial.C)) B' π₁' π₂' g₁ g₂ agree hLB
  have hn : ((l.M' : ℕ) : k) ≠ 0 := by
    intro h0'
    have hM : l.M' ≠ 0 := Nat.lcm_ne_zero (by have := l.three_le; omega) l.A_pos.ne'
    have hk : ((TrivSqZeroExt.fstHom k k k).toRingHom.comp ((ρ.comp (Cn.ψ.comp MvPolynomial.C)).comp Cn.L.b))
        (l.M' : c.F) = 0 := by rw [map_natCast]; exact h0'
    rw [map_eq_zero_iff _ (RingHom.injective _)] at hk
    exact hM (by exact_mod_cast hk)
  have agree' : ∀ (Z : Scheme.{0}) (x : Z ⟶ o'.t.G.left) (y : Z ⟶ Sp k),
      x ≫ o'.t.G.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom →
        x ≫ m₁.toSABMap.φ = x ≫ m₂.toSABMap.φ := by
    intro Z x y hx
    rw [hm₁, hm₂, ← Category.assoc, ← Category.assoc]
    exact agree Z _ y (by rw [Category.assoc, hio, hx])
  have hinv : io.inv ≫ o'.t.G.hom = B'.hom := by rw [← hio, Iso.inv_hom_id_assoc]
  have hc : ∀ y, (C.P.D.toPre.c (Cn.e.symm y)).left ≫ hD.e.hom.left ≫ pullback.fst Cn.L.D.P.A.hom (specOf (Cn.ψ.comp MvPolynomial.C)) =
      specOf (Cn.ψ.comp MvPolynomial.C) ≫ (Cn.L.D.c (l.M' • y)).left := fun y => by
    have := hD.c_pr (Cn.e.symm y)
    rw [hxe, LinearEquiv.apply_symm_apply] at this
    exact this
  obtain ⟨x, hx₁, hx₂, hx₀⟩ := GlobalTheory.T.dualNumber_points_pulledBack_object_from_base Cn.L k (ρ.comp (Cn.ψ.comp MvPolynomial.C)) o' m₁ m₂ l.M' hn agree'
    (fun y => c' (Cn.e.symm y) ≫ io.inv)
    (fun y => by rw [Category.assoc, hinv, (hc' _).1])
    (fun y => by
      rw [hm₁]; simp only [Category.assoc, Iso.inv_hom_id_assoc]; rw [e₁, ← Category.assoc, (hc' _).2.1, Category.assoc, hc,
        ← Category.assoc, hsp])
    (fun y => by
      rw [hm₂]; simp only [Category.assoc, Iso.inv_hom_id_assoc]; rw [e₂, ← Category.assoc, (hc' _).2.2, Category.assoc, hc,
        ← Category.assoc, hsp]; rfl)
  exact Cn.L.fineEps k (ρ.comp (Cn.ψ.comp MvPolynomial.C)) o' m₁ m₂ x hx₁ hx₂ hx₀

end GlobalTheory.RigBase
end
