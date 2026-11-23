module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle070
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle074
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle071
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3211
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCubicalRigidifiedExtension
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle133
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3224
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3202
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3203
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3051
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3052
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3181
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3025
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3097
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3157
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLabelledLatticeEquivOfCommonFibre
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle073
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2892
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ToStkAInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3098
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3218
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3160
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle075
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2927
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3213
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3102
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraitTransport
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecScalOneVal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3212
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.Algebra.Order.Star.Int
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle076
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenOfIso

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.BundleExt

theorem exists_rigLB_cubical_symm : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → (∀ x : S, x ∉ Set.range j → UPre Xo c φ j BD d x) → ∀ (tF : SAB H (Xo.XF c)), SABMap tF Xo.univ.t (pullback.fst _ _) → ∀ (G : Over S) [GrpObj G] [IsCommMonObj G] (e : tF.G.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback tF.G G j e → (∀ {k : Type} [Field k] {m n : ℕ} (C : MonoFam Xo c φ (ChartRing k m n)), IsTaut C → ∀ ξ : Sp (ChartRing k m n) ⟶ S, C.y ≫ j = jK _ ≫ ξ → ∀ (tK : SAB H (Sp (FractionRing (ChartRing k m n)))) (a : SABMap tK C.t (jK _)) (b : SABMap tK tF C.y), ∃ πC : C.t.G.left ⟶ G.left, IsGrpPullback C.t.G G ξ πC ∧ a.φ ≫ πC = b.φ ≫ e) → ∃ (PP : RigLB G) (cub : CubicalStr G PP), PP.IsSymmetric ∧ ∃ cm : CubeMap tF.G G, cm.F = e ∧ cm.e = j ∧ cm.IsPullCubical tF.cub cub := by
  intro E _ _ _ H Dw l Xo c φ hpq hpol hns Z zs i OZ N d J S π j _ BD hU hPre tF htF G _ _ e hsa he hC
  obtain ⟨M, hM, hw⟩ := GlobalTheory.T.exists_lineBundle_extension_descended_semiAbelian Xo c φ hpq hpol hns zs i OZ N d J π j BD hU hPre tF htF G e hsa he hC
  obtain ⟨⟨-, -, -, -, -, -, -⟩, -, -, -, ⟨⟨hnorm, -⟩, hproj, -, hdense, -, -⟩, -⟩ := hU
  have := hsa.smooth
  have := hsa.geomConnected
  obtain ⟨h1, h2⟩ : QuasiCompact (π ≫ zs) ∧ LocallyOfFiniteType (π ≫ zs) := by
    obtain ⟨M, i', hi', hcomp⟩ := hproj
    haveI := hi'
    haveI := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str c.F M
    rw [← hcomp]
    exact ⟨inferInstance, inferInstance⟩
  haveI : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian (π ≫ zs)
  haveI : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace (π ≫ zs)
  haveI : IsDominant j := ⟨hdense⟩
  have hS : Geo.Tor.IsNormalScheme S := (GlobalTheory.isNormalScheme_iff_pred S).mp hnorm
  obtain ⟨L', c', m, hF, he', hpc, hsym⟩ :=
    DenseCubeExt.exists_cubical_extension S _ j hS G tF.G e he tF.PP tF.cub M hM hw
  exact ⟨L', c', hsym tF.sym, m, hF, he', hpc⟩

end GlobalTheory.BundleExt
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.USep.thetaConst_eq_lam_root_mul_unit : ∀ (n : ℕ), n.Prime → Odd n → ∀ j : ℕ, 1 ≤ j → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → IsUnit (n : V₁) →
  ∀ (D : DegPre V₁) (X C : Type) [AddCommGroup X] (e : X ≃+ D.X) (u : X → C → V₁) (mo : X → V₁),
  (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → IsThetaTerms D ((n ^ j) ^ 2) e (fun mu c => u mu c * mo mu) →
  ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (ρ₀ : LB.Gen (D.P.L.pull (eSec D.P.A))), ρ₀.IsGen →
  ∀ (th : LB.Sec (LPow D.P.A D.P.L ((1 : ℕ) : ℤ) (Over.mk (spMap ev)))), IsGenSec D.P.A D.P.L ((1 : ℕ) : ℤ) th →
  ∃ (M : ℕ) (lam : K), 1 ≤ M ∧ ∀ (y : Over.mk (spMap ev) ⟶ D.P.A) (c : K),
    GlobalTheory.Ex.OneGen.ThG D.P.A D.P.L ρ₀ (n ^ j) th y (GlobalTheory.Ex.fnOf c) → ∃ (c₀ : C) (ζ : K), ζ ^ M = 1 ∧ c = lam * ζ * ev (u 0 c₀) := by
  intro n hn hodd j hj V₁ _ _ _ hV hunit D X C _ e u mo hmo hT K _ _ ev ρ₀ hρ₀ th hth
  have hn3 : 3 ≤ n := by
    have h2 := hn.two_le
    rcases hodd with ⟨k, rfl⟩
    omega
  have hm3 : 3 ≤ n ^ j := le_trans hn3 (Nat.le_self_pow (by omega) n)
  have hmu : IsUnit ((n ^ j : ℕ) : V₁) := by push_cast; exact hunit.pow j
  obtain ⟨M, lam, hM, H⟩ := GlobalTheory.T.theta_terms_separation_algebraically_closed (n ^ j) (hodd.pow) hm3 V₁ hV hmu D X C e u mo hmo hT K ev ρ₀ hρ₀ th hth
  refine ⟨M, lam, hM, fun y c hc => ?_⟩
  haveI : IsNoetherianRing V₁ := hV.1
  obtain ⟨τ, hτ, hv⟩ := GlobalTheory.T.exists_torsionFrame_isValueAt_thetaConstant (Sp V₁) D.P ρ₀ hρ₀ (n ^ j) (hodd.pow) _ th y _ hc
  exact H (y ^ n ^ j) τ c (GlobalTheory.USep.isTorsFrame_sq _ D.P ρ₀ (n ^ j) _ (y ^ n ^ j) τ hτ) hv
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.Sep.E8Fibration

theorem eighthPowerFibre_thetaObj : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (gQ : ℕ), ∃ (J : Type) (_ : Finite J)
    (Mat : J → Matrix (Fin (2 * (8 * gQ))) (Fin (2 * (8 * gQ))) ℤ) (κ : ℕ) (w w' : J),
  ∀ (l : ℕ), l.Prime → Odd l → ∀ j : ℕ, 1 ≤ j →
  ∀ (V V₁ : Type) [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → IsUnit (l : V₁) →
  ∀ (Q : Data V), Q.g = gQ → ∀ (ρ : V →+* V₁), Function.Injective ρ → ∀ (D : DegPre V₁) (e : (Fin 8 → Q.X) ≃+ D.X),
  SharpRef W Q ρ D e →
  ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ →
  ∃ (bT : TBase k₀ ((l ^ j) ^ 2)) (t : TObj (8 * gQ) ((l ^ j) ^ 2) J bT (spMap k₀.subtype))
    (ψ : ((Over.pullback (spMap ev)).obj D.P.A).left ⟶ t.A.left),
    t.Shape Mat κ ∧ t.Prim w w' ∧
    IsGrpPullback ((Over.pullback (spMap ev)).obj D.P.A) t.A (𝟙 _) ψ ∧
    LBIso (D.P.L.pull (pullback.fst D.P.A.hom (spMap ev))) (t.L.pull ψ) ∧
    ∀ (y : Over.mk (spMap ev) ⟶ D.P.A), y ^ ((l ^ j) ^ 2) = 1 →
      ∀ q : Sp K ⟶ ((Over.pullback (spMap ev)).obj D.P.A).left,
      q ≫ pullback.fst D.P.A.hom (spMap ev) = y.left → q ≫ pullback.snd D.P.A.hom (spMap ev) = 𝟙 _ →
      ∃ a, q ≫ ψ = (t.lab a).left := by
  intro W hW gQ
  obtain ⟨κ, hκ⟩ := GlobalTheory.T.e8_act_linComb_relAmple W hW
  obtain ⟨Mat, hMat⟩ := GlobalTheory.T.e8_fibration_algebraically_closed_field W hW gQ
  refine ⟨Fin 2, inferInstance, Mat, κ, 0, 1, ?_⟩
  intro l hl hlo j hj V V₁ _ _ _ _ _ hCN hlu Q hQ ρ hρ D e hS K _ _ ev k₀ hk₀
  obtain ⟨P', ψ, B, _, M, pr, hg, hψ, hL, hB, hpr, hE, hpt⟩ := GlobalTheory.T.exists_polarized_specialization_field W gQ V V₁ Q hQ ρ hρ D e hS K ev
  haveI : IsCommMonObj B := hB.1.comm
  choose act hact1 hact2 using fun i : Fin 2 => GlobalTheory.T.exists_eighth_power_endomorphism_acting_by_matrix _ _ _ pr hpr (E8Fibration.actMat W i)
  have hlK : (l : K) ≠ 0 := by
    have := hlu.map ev
    rw [map_natCast] at this
    exact this.ne_zero
  obtain ⟨bT, pt, htor, hbij, hpair, hsh⟩ := hMat l hl hlo j hj K k₀ hk₀ hlK P' hg B M pr hB hpr hE act hact1 hact2
  let t : TObj (8 * gQ) ((l ^ j) ^ 2) (Fin 2) bT (spMap k₀.subtype) :=
    { A := P'.A, grp := P'.grp, ab := P'.isAb, dim := hg ▸ P'.smoothDim, L := P'.L, isLB := P'.isLB,
      rigid := P'.rigid, sym := P'.sym, ample := P'.ample, ktriv := P'.ktriv, pt := pt, torsion := htor,
      bij := hbij, pairing := hpair, act := act, hom := hact1 }
  refine ⟨bT, t, ψ, ?_, ?_, hψ, hL, ?_⟩
  · exact fun a => ⟨hsh a, hκ gQ K P' B M pr hB hpr hE act hact1 hact2 a⟩
  · exact GlobalTheory.T.e8_act_prod_eq_one W hW gQ K P' B M pr hB hpr hE act hact1 hact2
  · intro y hy q hq1 hq2
    obtain ⟨y', hy'1, hy'2⟩ := hpt _ y hy q hq1 hq2
    obtain ⟨c, hc, -⟩ := hbij K (𝟙 _) y' hy'2
    refine ⟨c, ?_⟩
    rw [← hy'1, ← hc]
    have h0 : (Over.homMk (𝟙 (Sp K)) (by simp) : Over.mk (𝟙 (Sp K)) ⟶ Out.baseOver (Sp K)) = 𝟙 _ := by
      ext; simp
    simp only [h0, Category.id_comp]
    rfl

end GlobalTheory.Poinc.Sep.E8Fibration
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.TensExist

theorem exists_tens : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → IsUnit (W + W.transpose).det → ∃ D' : DegData R (maximalIdeal R), Nonempty (Tens D.toPre D'.toPre W) := by
  intro R _ _ _ hA D r W hpos hdet
  obtain ⟨D', T, hrig⟩ := GlobalTheory.T.exists_tensorPreData_rigidification_inv_psi_zero R hA D W hpos hdet
  obtain ⟨hp, ht⟩ := GlobalTheory.T.tensorData_psi_mem_maximalIdeal_tendsto_zero R hA D D' W hpos T
  exact ⟨⟨D', GlobalTheory.T.tensorData_psi_isEven R hA D D' W T, GlobalTheory.T.tensorData_tau_bimultiplicative R hA D D' W T hrig, hp, ht⟩, ⟨T⟩⟩

end GlobalTheory.Mum.TensExist
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open Classical
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_labelled_lattice_equiv_of_common_fibre : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (Y : RatModel X₁.o₁ X₁.Ω₁) (U₀ : Y.Z.Opens) (EE : Y.Lat X₁.S.J) (_ : ZHOut X₁.ρ Y U₀ EE) (q : Y.Z ⟶ X₁.M.Z), X₁.S.Over₀ Y U₀ → X₁.S.IsEE Y U₀ EE → IsProper q → Y.pt ≫ q = X₁.M.pt → ∀ (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z), _root_.IsPreconnected (q.base ⁻¹' {z₁}) → ∀ (c c' : CTrait X₁ p z₁) (y y' : Sp (OO p) ⟶ Y.Z), y ≫ q = c.y → y' ≫ q = c'.y → ∀ (yy : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) (Fin 8 → c.T.D.toPre.X)) (yy' : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) (Fin 8 → c'.T.D.toPre.X)), IsLab X₁ ε₁ c yy → IsLab X₁ ε₁ c' yy' → ∃ θ : (Fin 8 → c.T.D.toPre.X) ≃+ (Fin 8 → c'.T.D.toPre.X), (∀ a μ, yy a = QuotientAddGroup.mk μ → yy' a = QuotientAddGroup.mk (θ μ)) ∧ ∀ (E : Matrix (Fin 8) (Fin 8) ℤ) (v : Fin 8 → c.T.D.toPre.X), θ (fun a => ∑ b, E a b • v b) = fun a => ∑ b, E a b • θ v b := by
  first | exact @GlobalTheory.Poinc.FibLat.exists_equiv_of_fibre | exact GlobalTheory.Poinc.FibLat.exists_equiv_of_fibre | (intros; apply GlobalTheory.Poinc.FibLat.exists_equiv_of_fibre <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum

theorem exists_unit_value_at_unit : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (k : ℕ), 1 ≤ k → ∀ b₀ : D.toPre.SecB k 0, eSec D.toPre.P.A (closedPoint R) ∈ nonzeroLocus b₀ → ∀ F₀ : IntFam (maximalIdeal R) D.toPre k, F₀.Lead 0 b₀ → ∃ s₀ : R, IsUnit s₀ ∧ ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (b : W) (σ : SecK C.P.L.L T.β k), T.ExpBy b σ F₀ → ∃ ε : Wˣ, ∀ J, Good C.P.L.L (cpt W) J → sval σ (unitW T.G) (cpt W) J = stalkOf (cpt W) (b * ε * T.φ s₀) * (val C.P.L.rig T.ξ (cpt W) J).val ^ k := by
  intro R _ _ _ hR D C k hk b₀ hb₀ F₀ hF₀
  obtain ⟨s₀, hs₀, h⟩ := GlobalTheory.T.exists_unit_adic_sum_origin_values_integral_family R hR D C k hk b₀ hb₀ F₀ hF₀
  refine ⟨s₀, hs₀, fun W _ _ _ T b σ hσ => ?_⟩
  obtain ⟨σ', f', hc, hp, he⟩ := hσ
  obtain ⟨ε, hε⟩ := GlobalTheory.T.carries_unitSection_rigidification_unit R D C W T k b σ' σ hc
  refine ⟨ε, fun J hJ => ?_⟩
  obtain ⟨J', hJ', -⟩ := exists_good T.U.LG.L T.U.LG.isLB (cpt W) (K := Empty) (fun e => e.elim) (fun e => e.elim)
    (fun e => e.elim) (fun e => e.elim)
  have e1 := hε J J' hJ hJ'
  rw [h W T σ' f' hp he J' hJ'] at e1
  refine mul_right_cancel₀ (pow_ne_zero k (Units.ne_zero (val T.U.LG.rig (idW W) (cpt W) J'))) ?_
  rw [e1]
  simp only [map_mul]
  ring

theorem exists_norm_const : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (k : ℕ), 1 ≤ k → ∀ b₀ : D.toPre.SecB k 0, eSec D.toPre.P.A (closedPoint R) ∈ nonzeroLocus b₀ → ∀ F₀ : IntFam (maximalIdeal R) D.toPre k, F₀.Lead 0 b₀ → ∀ s : SecK C.P.L.L C.α k, ∃ c₁ c₂ : R, c₂ ≠ 0 ∧ ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (a b : W), a ≠ 0 → b ≠ 0 → T.Exp a b s F₀ → ∃ u : Wˣ, T.φ c₂ * (u : W) * a = T.φ c₁ * b := by
  intro R _ _ _ hR D C k hk b₀ hb₀ F₀ hF₀ s
  obtain ⟨x, y, hy, h1⟩ := GlobalTheory.T.value_unitSection_smul_genericFibre_section R hR D C k s
  obtain ⟨s₀, hs₀, h2⟩ := exists_unit_value_at_unit R hR D C k hk b₀ hb₀ F₀ hF₀
  have key : ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (a b : W), T.Exp a b s F₀ →
      ∃ ε : Wˣ, T.φ y * (b * ε * T.φ s₀) = a * T.φ x := by
    intro W _ _ _ T a b hE
    obtain ⟨σ, hσ, hgen⟩ := hE
    obtain ⟨ε, hε⟩ := h2 W T b σ hσ
    obtain ⟨J, hJ, -⟩ := exists_good C.P.L.L C.P.L.isLB (cpt W) (K := Empty) (fun e => e.elim) (fun e => e.elim)
      (fun e => e.elim) (fun e => e.elim)
    have e1 := h1 W T a σ hgen J hJ
    rw [hε J hJ, ← _root_.mul_assoc, ← map_mul] at e1
    refine ⟨ε, stalkOf_injective (cpt W) (mul_right_cancel₀ ?_ e1)⟩
    exact pow_ne_zero _ (Units.ne_zero _)
  by_cases hx : x = 0
  · refine ⟨0, 1, one_ne_zero, fun W _ _ _ T a b ha hb hE => ?_⟩
    exfalso
    obtain ⟨ε, e⟩ := key W T a b hE
    rw [hx, map_zero, mul_zero] at e
    have hφy : T.φ y ≠ 0 := fun h => hy (T.inj (h.trans (map_zero _).symm))
    have hφs : T.φ s₀ ≠ 0 := (hs₀.map T.φ).ne_zero
    exact mul_ne_zero hφy (mul_ne_zero (mul_ne_zero hb (Units.ne_zero ε)) hφs) e
  · refine ⟨s₀ * y, x, hx, fun W _ _ _ T a b ha hb hE => ?_⟩
    obtain ⟨ε, e⟩ := key W T a b hE
    refine ⟨ε⁻¹, ?_⟩
    rw [map_mul]
    have hinv : (ε : W) * ((ε⁻¹ : Wˣ) : W) = 1 := Units.mul_inv ε
    linear_combination (-(((ε⁻¹ : Wˣ) : W))) * e + (T.φ y * b * T.φ s₀) * hinv

end GlobalTheory.Mum
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem GlobalTheory.Mum.trait_lead_value : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (Y : Ext D.toPre) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ (κ : ResidueField R →+* ResidueField W) (e : (Over.pullback (spMap (residue W))).obj T.G ≅ (Over.pullback (spMap κ)).obj ((Over.pullback (spMap (residue R))).obj Y.H)), κ.comp (residue R) = (residue W).comp T.φ ∧ IsMonHom e.hom ∧ ∀ (Z : Scheme.{0}) (p : Z ⟶ ((Over.pullback (spMap (residue W))).obj T.G).left) (p' : Z ⟶ T.G.left) (y : Z ⟶ Y.H.left), p' = p ≫ pullback.fst T.G.hom (spMap (residue W)) → y = p ≫ e.hom.left ≫ pullback.fst ((Over.pullback (spMap (residue R))).obj Y.H).hom (spMap κ) ≫ pullback.fst Y.H.hom (spMap (residue R)) → ∀ (k : ℕ) (u : Wˣ) (z : Z) J J', Good C.P.L.L z J → Good D.toPre.P.L z J' → ∃ c : (Z.presheaf.stalk z)ˣ, ∀ (α : D.toPre.X) (b : D.toPre.SecB k α) (τ : SecK D.toPre.P.L Y.q.left k) (F : IntFam (maximalIdeal R) D.toPre k) (σ : SecK C.P.L.L T.β k), IsTermOf Y b τ → F.Lead α b → T.ExpBy u σ F → sval σ p' z J = c.val * sval τ y z J' := by
  intro R _ _ _ hB D C Y W _ _ _ T
  obtain ⟨κ, e, h1, h2, h3⟩ := GlobalTheory.T.exists_closedFibre_iso_torusExtension_baseChange R hB D C Y W T
  refine ⟨κ, e, h1, h2, fun Z p p' y hp hy k u z J J' hJ hJ' => ?_⟩
  obtain ⟨g, ξ', hg, hξ, hP⟩ := h3 Z p p' y hp hy
  exact GlobalTheory.T.closedFibre_value_eq_unit_mul_leadingFourierTerm R hB D C Y W T Z p' y g ξ' hg hξ hP k u z J J' hJ hJ'
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_ratio_of_expansions_proportional_at_trait : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (k : ℕ), 1 ≤ k → ∀ (G : IntFam (maximalIdeal R) D.toPre k) (S Ψ : SecK C.P.L.L C.α k), (∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ u : Wˣ, T.Exp 1 u Ψ G) → ∀ (W₀ : Type) [CommRing W₀] [IsDomain W₀] [IsLocalRing W₀] (T₀ : Trait C W₀) (a₀ b₀ : W₀), a₀ ≠ 0 → b₀ ≠ 0 → T₀.Exp a₀ b₀ S G → ∃ r t : R, r ≠ 0 ∧ t ≠ 0 ∧ ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ u : Wˣ, T.Exp (T.φ t) (T.φ r * u) S G := by
  first | exact @GlobalTheory.Mum.exists_ratio_of_exp_one_trait | exact GlobalTheory.Mum.exists_ratio_of_exp_one_trait | (intros; apply GlobalTheory.Mum.exists_ratio_of_exp_one_trait <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

theorem GlobalTheory.TInj.taut_refine : ∀ {o : Type} [CommRing o] {ζ : o} {g n : ℕ} {φ : InvFun ℤ}, 1 ≤ n → ∀ C : Taut ζ g n φ, IsCN C.R → ∃ (R₁ : Type) (_ : CommRing R₁) (_ : IsDomain R₁) (_ : IsLocalRing R₁) (ρ : C.R →+* R₁) (D : DegData R₁ (maximalIdeal R₁)) (e' : D.toPre.X ≃+ C.Q.X), IsCN R₁ ∧ Function.Injective ρ ∧ ρ.Finite ∧ IsLocalHom ρ ∧ Refines C.Q ρ D.toPre e' := by
  intro o _ ζ g n φ hn C hCN
  obtain ⟨hmono, -, hcone, hdef, ht0⟩ := GlobalTheory.TChart.Taut.monomial_chart g n φ hn C
  have hsymm : ∀ i y z, ((n : ℤ) • C.δ i) y z = ((n : ℤ) • C.δ i) z y := fun i y z => by
    simp only [LinearMap.smul_apply, mem_balForms_int.1 (hcone.mem i) y z]
  have hnn : ∀ i y, 0 ≤ ((n : ℤ) • C.δ i) y y := fun i y => by
    simp only [LinearMap.smul_apply, smul_eq_mul]
    exact mul_nonneg (by positivity) (hcone.nonneg i y)
  have hdef' : ∀ y, y ≠ 0 → ∃ i, 0 < ((n : ℤ) • C.δ i) y y := fun y hy => by
    obtain ⟨i, hi⟩ := hdef y hy
    refine ⟨i, ?_⟩
    simp only [LinearMap.smul_apply, smul_eq_mul]
    exact mul_pos (by exact_mod_cast hn) hi
  obtain ⟨R', _, _, _, ρ, -, D, e, hCN', hinj, hfin, hloc, -, href, -⟩ :=
    GlobalTheory.PolDeg.refine_monomial_of_polarised C.R C.Q C.m C.t (fun i => (n : ℤ) • C.δ i) hCN hmono C.bd ht0 hsymm hnn hdef'
  exact ⟨R', inferInstance, inferInstance, inferInstance, ρ, D, e, hCN', hinj, hfin, hloc, href⟩
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_galoisConjugate_equivariantBijection_twist : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (N : ℕ), Odd N → ∀ (lab : QkPt D.toPre (Kb R) N → (TFK (R := R) (Kb R) ⟶ A.A)) E, Eqv D.toPre A (Kb R) N lab E → (∀ τ : Kb R →ₐ[FractionRing R] Kb R, LabExt τ lab lab) → ∀ σ : Kb R →ₐ[FractionRing R] Kb R, ∃ E', Eqv D.toPre A (Kb R) N lab E' ∧ ∀ (F₀ : IntFam (maximalIdeal R) D.toPre N) s, F₀.Over s → SecTw σ (E s) (E' s) := by
  first | exact @GlobalTheory.Mum.exists_eqv_conj | exact GlobalTheory.Mum.exists_eqv_conj | (intros; apply GlobalTheory.Mum.exists_eqv_conj <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem trait_transport : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (j : ℕ) (wA : LB.Iso C.A.L (C.P.L.L.pull C.α)), wA.IsGen → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F] (em : Kb R →ₐ[FractionRing R] F), (∀ r, algebraMap (FractionRing R) F (algebraMap R _ r) = algebraMap (FractionRing W) F (algebraMap W _ (T.φ r))) → ∀ f : (TFK (R := W) F ⊗ T.A.A).left ⟶ (TFK (R := R) F ⊗ C.A.A).left, IsIso f → f ≫ (fst (TFK (R := R) F) C.A.A).left = (fst (TFK (R := W) F) T.A.A).left → f ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α = (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β → ∀ w₀ : LB.Iso (T.A.L.pull T.U.gen.hom.left) (T.U.LG.L.pull (pullback.fst T.G.hom (jK W))), w₀.IsGen → ∀ lab' : QkPt T.D'.toPre F (C.n ^ j) → (TFK (R := W) F ⟶ T.A.A), (∀ (p : QkPt D.toPre (Kb R) (C.n ^ j)) (p₁ : QkPt D.toPre F (C.n ^ j)) (p' : QkPt T.D'.toPre F (C.n ^ j)), QkExt em.toRingHom p p₁ → p'.y = T.hD.xe.symm p₁.y → IsPullGtF T.φ T.hD F p₁.g p'.g → (lab' p').left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β = spMap em.toRingHom ≫ (C.lab j p).left ≫ C.α) → ∀ E' : Fam T.D'.toPre F (C.n ^ j) → SecK T.A.L (snd (TFK (R := W) F) T.A.A).left (C.n ^ j), Eqv T.D'.toPre T.A F (C.n ^ j) lab' E' → ∃ (lab : QkPt D.toPre F (C.n ^ j) → (TFK (R := R) F ⟶ C.A.A)) (E : Fam D.toPre F (C.n ^ j) → SecK C.A.L (snd (TFK (R := R) F) C.A.A).left (C.n ^ j)) (Φ : Fam D.toPre F (C.n ^ j) → Fam T.D'.toPre F (C.n ^ j)), LabExt em (C.lab j) lab ∧ Eqv D.toPre C.A F (C.n ^ j) lab E ∧ (∀ (s : Fam D.toPre F (C.n ^ j)) (F₀ : IntFam (maximalIdeal R) D.toPre (C.n ^ j)), F₀.Over s → (∀ f' : ∀ x, T.D'.toPre.SecB (C.n ^ j) x, (∀ x, PullB T.hD x (F₀.f (T.hD.xe x)) (f' x)) → ∀ x, GeneratorPullback.SecScal T.D'.toPre.P.L (DegPre.famφ T.D'.toPre F x) (DegPre.famε (C.n ^ j)) ((Φ s).s x) (T.D'.toPre.famφB x) (DegPre.famε (C.n ^ j)) (f' x) (DegPre.prB T.D'.toPre F).left 1)) ∧ ∀ (s : Fam D.toPre F (C.n ^ j)) (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ (TFK (R := R) F ⊗ C.A.A).left) (q : Z ⟶ (TFK (R := W) F ⊗ T.A.A).left), q ≫ f = p' → p ≫ T.β = p' ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α → p ≫ T.G.hom = q ≫ (fst (TFK (R := W) F) T.A.A).left ≫ spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _)) → ∀ z JP JA JG Jt, Good C.P.L.L z JP → Good C.A.L z JA → Good T.U.LG.L z JG → Good T.A.L z Jt → (gw wA (p' ≫ (snd (TFK (R := R) F) C.A.A).left) z (JP (p ≫ T.β)) (JA (p' ≫ (snd (TFK (R := R) F) C.A.A).left)) ^ (C.n ^ j)).val * sval (E s) p' z JA = (gw T.ℓ p z (JP (p ≫ T.β)) (JG p) ^ (C.n ^ j)).val * (gw w₀ (q ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left) z (JG (q ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W))) (fun _ => Jt (q ≫ (snd (TFK (R := W) F) T.A.A).left)) ^ (C.n ^ j)).val * sval (E' (Φ s)) q z Jt := by
  intro R _ _ _ hR D C j wA hwA W _ _ _ T F _ _ _ _ em hc f hf hfst hα w₀ hw₀ lab' hlab' E' hE'
  obtain ⟨Φ, hΦb, hΦa, hΦs, hΦP, hΦp, hΦf⟩ := GlobalTheory.FamPull.fam_transport R D W T.φ T.D' T.hD F hc (C.n ^ j)
  obtain ⟨lab, hLE, hon, hlr⟩ := GlobalTheory.Mum.Trait.exists_lab_push R hR D C j W T F em hc f hf hfst hα lab' hlab' hE'.onto
  obtain ⟨Tr, hTb, hTa, hTs, hTv⟩ := GlobalTheory.Mum.SecMove.exists_trait_transport R hR D C j wA hwA W T F hc f hf hfst hα w₀ hw₀
  have hC2 := GlobalTheory.T.transport_symmetric_lifts_theta_group_trait R hR D C j wA hwA W T F hc f hf hfst hα w₀ hw₀
  refine ⟨lab, fun s => Tr (E' (Φ s)), Φ, hLE, ⟨?_, ?_, ?_, hon, ?_, ?_, ?_⟩, hΦP, fun s => hTv (E' (Φ s))⟩
  · exact hTb.comp (hE'.bij.comp hΦb)
  · intro s s' s'' h i
    exact hTa _ _ _ (hE'.add _ _ _ (hΦa s s' s'' h)) i
  · intro c s s' h i
    exact hTs c _ _ (hE'.smul c _ _ (hΦs c s s' h)) i
  · intro p
    obtain ⟨p', hy, hg⟩ := hΦp p
    exact (hΦf p p' hy hg).1 (hE'.frame p')
  · intro p
    obtain ⟨p', hy, hg⟩ := hΦp p
    exact (hC2 _ _ (hlr p p' hy hg) ((hE'.onto _).2 ⟨p', rfl⟩)).1 (hE'.lift p')
  · intro p w θ s s' hw hθ hr
    obtain ⟨p', hy, hg⟩ := hΦp p
    obtain ⟨w', hw', hr'⟩ := (hΦf p p' hy hg).2 w hw
    obtain ⟨θ', hθ', hact⟩ := (hC2 _ _ (hlr p p' hy hg) ((hE'.onto _).2 ⟨p', rfl⟩)).2 θ hθ
    exact hact _ _ _ _ (hTv _) (hTv _) (hE'.act p' w' θ' _ _ hw' hθ' (hr' s s' hr))

end GlobalTheory.Mum
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.toroidalCompactification_smooth_snc_boundary : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → SepB Xo c φ j → (∀ x : S, x ∉ Set.range j → UPre Xo c φ j BD d x) → SmoothOfRelativeDimension Dw.dim (π ≫ zs) ∧ FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal j.opensRange.compl) := by
  first | exact @GlobalTheory.UChartSmooth.smooth_and_snc | exact GlobalTheory.UChartSmooth.smooth_and_snc | (intros; apply GlobalTheory.UChartSmooth.smooth_and_snc <;> assumption)
end
