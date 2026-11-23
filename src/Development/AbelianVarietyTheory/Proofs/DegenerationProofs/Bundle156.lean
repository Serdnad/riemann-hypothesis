module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle007
public import Development.AbelianVarietyTheory.Definitions.Degenerations.MorAlgSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle001
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle033
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle118
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle141
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle121
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle002
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle007
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle148
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle145
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusTorsionPointsCorrespondValues
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle144
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle132
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle142
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle119
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle089
import Mathlib.Algebra.AffineMonoid.Basic
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TwistIsoTorsionRepresentativeMulEquiv
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.PUnit
import Mathlib.Algebra.Ring.BooleanRing
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

namespace GlobalTheory.Ex.AllLevels

theorem ser_nested {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}
    {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {O' : Type} [CommRing O'] [IsDomain O'] {b : O →+* O'}
    {a : ArcIn D l β O' b} {K : Type} [Field K] [IsAlgClosed K] [Algebra (FractionRing O') K] [Algebra (PowerSeries O') K]
    [FaithfulSMul (PowerSeries O') K] [Algebra.IsAlgebraic (PowerSeries O') K] (S : Ser a K (algebraMap _ K))
    (r m : ℕ) (hr : Odd r) (hm : Odd m) : ∃ c : Kˣ, ∀ x, S.v (r * m) (r • x) = c * S.v m x := by
  obtain ⟨C, _, _, _, _, _, gam, u, h₁, h₂, h₃, h₄⟩ := GlobalTheory.T.exists_complete_algClosed_field_powerSeries_extension O' K
  obtain ⟨A, ρ, -, -, hρ, hv⟩ := S.val C gam u h₁ h₂ h₃ h₄
  have hR : Roots u ρ := ⟨Units.ext ((hρ 1).trans ((congrArg gam S.r_one).trans h₃.symm)), fun n k hn hk => Units.ext (by
    rw [Units.val_pow_eq_pow_val, hρ, hρ, ← map_pow, ← Units.val_pow_eq_pow_val, S.roots.2 n k hn hk])⟩
  obtain ⟨b₁, -, b₃, -, b₅⟩ := GlobalTheory.T.torus_torsion_points_correspond_values O' a.D₀ a.even a.bimult C A.N A.ν
  obtain ⟨q₁, q₂⟩ := GlobalTheory.T.qval_add_of_tower E H D O' a.D₀ a.oa a.even a.bimult C A.I A.N A.ν A.q b₁ b₃
    (fun k => ⟨(b₅ k).1, (b₅ k).2.2⟩) A.hq
  have hrm : Odd (r * m) := hr.mul hm
  choose p hp _ using fun x => existsUnique_twRel A.be u (ρ (m ^ 2)) (hR.pow (pow_pos hm.pos 2)) (A.q _ x)
  choose p' hp' _ using fun x => existsUnique_twRel A.be u (ρ ((r * m) ^ 2)) (hR.pow (pow_pos hrm.pos 2)) (A.q _ x)
  obtain ⟨s, hs⟩ := (hv m hm p hp).1
  obtain ⟨s', hs'⟩ := (hv _ hrm p' hp').1
  have key : ∀ x, gam (S.v (r * m) (r • x)) = (s' * s⁻¹ : Cˣ) * gam (S.v m x) := fun x => by
    rw [hs, hs', GlobalTheory.T.twist_tx_nsmul_eq_of_odd C A.N D.La A.q q₁ q₂ _ A.be u ρ hR r m hr hm x _ _ (hp' _) (hp x), Units.val_mul,
      _root_.mul_assoc, Units.inv_mul_cancel_left]
  by_cases h : ∃ x, S.v m x ≠ 0
  · obtain ⟨x₀, h₀⟩ := h
    have e : gam (S.v (r * m) (r • x₀) / S.v m x₀) = (s' * s⁻¹ : Cˣ) := by
      rw [map_div₀, key, mul_div_cancel_right₀ _ ((map_ne_zero gam).2 h₀)]
    refine ⟨Units.mk0 (S.v (r * m) (r • x₀) / S.v m x₀) fun h => (s' * s⁻¹).ne_zero (by rw [← e, h, map_zero]),
      fun x => gam.injective ?_⟩
    rw [map_mul, Units.val_mk0, e, key]
  · simp only [not_exists, not_not] at h
    exact ⟨1, fun x => gam.injective (by rw [key, h, mul_zero, map_zero, mul_zero])⟩

theorem one_object : HV → Laws6 → GlobalTheory.LN.UDvrSt → GlobalTheory.LN.HomExtSt → ThetaPtDeterminesSt → EndDeterminedOnTorsionSt → ThetaUnifAV → AllA fun {E} _ _ _ {H} {D} {l} {Xo} {c} {W₀} Y {O'} _ _ {b} a => ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra (FractionRing O') K] [Algebra (PowerSeries O') K] [FaithfulSMul (PowerSeries O') K] [Algebra.IsAlgebraic (PowerSeries O') K], (∀ x, algebraMap (FractionRing O') K (algebraMap O' _ x) = algebraMap (PowerSeries O') K (PowerSeries.C x)) → ∀ (S : Ser a K (algebraMap _ K)) (n : ℕ), n.Prime → Odd n → (∀ j, 2 ≤ j → ∃ o : Full D K, o.ρ = S.A.ρ ∧ o.I.ζ ((n ^ j) ^ 2) = S.A.I.ζ ((n ^ j) ^ 2) ∧ o.Theta (n ^ j) (S.v (n ^ j))) → ∃ o : Full D K, o.ρ = S.A.ρ ∧ ∀ j, o.I.ζ (n ^ j) = S.A.I.ζ (n ^ j) ∧ o.Theta (n ^ j) (S.v (n ^ j)) := by
  intro hV _ _ _ h₁ h₂ _ E _ _ _ H D l Xo c W₀ Y O' _ _ _ b ϖ a _ K _ _ _ _ _ _ _ S n hn ho h
  exact exists_full_all hV.1.1 h₁ h₂ S.A.ρ S.A.I.ζ S.A.I.ζ_pow S.v (ser_nested S) hn ho h

end GlobalTheory.Ex.AllLevels
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.AbLaw

noncomputable section
namespace GlobalTheory.TowerAlg

theorem isPullback_of_grp {S S' : Scheme.{0}} {B : Over S} {B' : Over S'} [GrpObj B] [GrpObj B'] {f : S' ⟶ S}
    {F : B'.left ⟶ B.left} (h : IsGrpPullback B' B f F) : IsPullback F B'.hom B.hom f := h.1

theorem exists_alg (hG : GlobalFnsSt) (hE : Ega) {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {I : Ideal R}
    (hA : admitted R I) (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) [∀ e, GrpObj (Y e)]
    [∀ e, IsCommMonObj (Y e)] (hY : ∀ e, IsAbelianScheme (Y e)) (N : ∀ e, CP (Y e))
    (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (h : ∀ e, IsCPPullback (N e) (N (e + 1)) (thickTrans R I e) (β e))
    (hamp : RelAmple (Y 0) (N 0).L.L) :
    ∃ (B : Over (Spec (CommRingCat.of R))) (_ : GrpObj B) (_ : IsCommMonObj B) (Q : CP B)
      (b : ∀ e, (Y e).left ⟶ B.left), IsAbelianScheme B ∧ RelAmple B Q.L.L ∧
      (∀ e, IsCPPullback (N e) Q (thick R I e) (b e)) ∧ ∀ e, β e ≫ b (e + 1) = b e := by
  have hN : IsNoetherianRing R := hA.1.1
  have hI : I ≠ ⊤ := hA.2.2.2.1.ne_top
  have hc : IsAdicComplete I R := hA.1.2.2.2
  choose hβ v hv using h
  obtain ⟨B, M, b, hp, hs, hM, ha, hb, hβb, hiso⟩ := hE.1 R I hI hc hA.2.1 Y β
    (fun e => (N e).L.L) v (fun e => isPullback_of_grp (hβ e)) (fun e => (hY e).smooth)
    (fun e => ⟨(N e).L.isLB, (hv e).gen⟩) hamp
  obtain ⟨g, hB, hg⟩ := GlobalTheory.T.isAbelianScheme_of_abelian_thickenings hE R I hA Y β hY hβ B b hp hs hb hβb
  have c := hB.comm
  obtain ⟨Q, hQ, hq⟩ := exists_cp_alg hG hE.2.2.1 hI hc N hB hp hg hM hiso hY
  exact ⟨B, g, c, Q, b, hB, by rw [hQ]; exact ha, hq, hβb⟩

theorem nonempty_alg : Laws → Laws2 → Ega → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), admitted R I → ∀ (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (P : CP G) (X : Type) [AddCommGroup X] (T : TowerR I P X), RelAmple (T.l 0).Q.B (T.l 0).D.M.L.L → Nonempty T.Alg := by
  intro hL _ hE R _ _ _ I hA G _ _ P X _ T hamp
  obtain ⟨B, _, _, Q, b, h₁, h₂, h₃, h₄⟩ := exists_alg hL.globalFns hE hA (fun e => (T.l e).Q.B)
    (fun e => (T.l e).Q.isAb) (fun e => (T.l e).D.M) T.β T.β_pb hamp
  exact ⟨⟨B, h₁, Q, h₂, b, h₃, h₄⟩⟩

end GlobalTheory.TowerAlg
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
namespace GlobalTheory.SS.MaxTorus
open GlobalTheory.SplitTorus

theorem surjective_of_mono {S : Scheme.{0}} [Nonempty S] {X Y : Type} [AddCommGroup X] [AddCommGroup Y]
    (φ : Y →+ X) [Mono (torusMap S φ)] : Function.Surjective φ := by
  let π : X →+ X ⧸ φ.range := QuotientAddGroup.mk' _
  have h : π.comp φ = (0 : X →+ X ⧸ φ.range).comp φ := by
    ext y
    simp [π]
  have h' : π = 0 := by
    apply torusMap_injective (S := S)
    rw [← cancel_mono (torusMap S φ), ← torusMap_comp, ← torusMap_comp, h]
  intro x
  have : π x = 0 := by rw [h']; rfl
  exact (QuotientAddGroup.eq_zero_iff x).1 this

theorem injective_of_surjective {X Y : Type} [AddCommGroup X] [AddCommGroup Y]
    [Module.Free ℤ X] [Module.Finite ℤ X] [Module.Free ℤ Y] [Module.Finite ℤ Y]
    (φ : Y →+ X) (h : Function.Surjective φ) (hr : Module.finrank ℤ Y ≤ Module.finrank ℤ X) :
    Function.Injective φ := by
  have h1 : Module.finrank ℤ X ≤ Module.finrank ℤ Y :=
    LinearMap.finrank_le_finrank_of_surjective (f := φ.toIntLinearMap) h
  let e : Y ≃ₗ[ℤ] X := LinearEquiv.ofFinrankEq _ _ (le_antisymm hr h1)
  exact OrzechProperty.injective_of_surjective_of_injective e.toLinearMap φ.toIntLinearMap e.injective h

theorem exists_inv {S : Scheme.{0}} [ConnectedSpace S] {X Y : Type} [AddCommGroup X] [AddCommGroup Y]
    [Module.Free ℤ X] [Module.Finite ℤ X] [Module.Free ℤ Y] [Module.Finite ℤ Y]
    (σ : splitTorus S X ⟶ splitTorus S Y) [IsMonHom σ] [Mono σ]
    (hr : Module.finrank ℤ Y ≤ Module.finrank ℤ X) : ∃ τ, τ ≫ σ = 𝟙 _ := by
  obtain ⟨φ, rfl⟩ := exists_eq_torusMap σ
  have hs := surjective_of_mono (S := S) φ
  let e : Y ≃+ X := AddEquiv.ofBijective φ ⟨injective_of_surjective φ hs hr, hs⟩
  refine ⟨torusMap S e.symm.toAddMonoidHom, ?_⟩
  rw [← torusMap_comp, ← torusMap_id]
  congr 1
  ext y
  exact e.symm_apply_apply y

theorem exists_quot_no_cocharacter : ∀ (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G], SmConn G → ∃ (X : Type) (_ : AddCommGroup X) (_ : Module.Free ℤ X) (_ : Module.Finite ℤ X) (B : Over (Sp k)) (_ : GrpObj B) (i : splitTorus (Sp k) X ⟶ G) (q : G ⟶ B), IsQuot i q ∧ ∀ f : Gm (Sp k) ⟶ B, IsMonHom f → f = 1 := by
  classical
  intro k _ _ G _ hG
  obtain ⟨hc, hsm, hsep, hqc, hgc⟩ := id hG
  have : ConnectedSpace G.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton G.hom
  obtain ⟨g, hg⟩ := exists_dim_of_preconnected G.hom (Classical.arbitrary _)
  let P : ℕ → Prop := fun n => ∃ (X : Type) (_ : AddCommGroup X) (_ : Module.Free ℤ X) (_ : Module.Finite ℤ X)
    (i : splitTorus (Sp k) X ⟶ G), IsMonHom i ∧ (∀ x : G.left, ∃ V, x ∈ V ∧ GoodOpen i V) ∧ Module.finrank ℤ X = n
  have hb : ∀ n, P n → n ≤ g := by
    rintro _ ⟨X, _, _, _, i, hi, hV, rfl⟩
    obtain ⟨B, _, q, -, hd⟩ := GlobalTheory.T.exists_smooth_torus_quotient_of_goodOpen_cover k G hG X i hi hV
    obtain ⟨a, -, ha⟩ := hd g hg
    omega
  obtain ⟨n₀, h₀⟩ : ∃ n, P n := by
    obtain ⟨X', _, _, _, i', ρ, h1, -, -, -, hV⟩ := GlobalTheory.T.splitTorus_image_factor_quotient_goodOpen k G hG PUnit 1
      (inferInstanceAs (IsMonHom (toUnit _ ≫ η[G])))
    exact ⟨_, X', _, ‹_›, ‹_›, i', h1, hV, rfl⟩
  obtain ⟨X, _, _, _, i, hi, hV, hn⟩ : P (Nat.findGreatest P g) := Nat.findGreatest_spec (hb _ h₀) h₀
  obtain ⟨B, _, q, hq, -⟩ := GlobalTheory.T.exists_smooth_torus_quotient_of_goodOpen_cover k G hG X i hi hV
  refine ⟨X, _, inferInstance, inferInstance, B, _, i, q, hq, fun f hf => ?_⟩
  obtain ⟨j, hj, rfl⟩ := GlobalTheory.T.exists_lift_oneParameter_quotient_torus k G hG X B i q hq f hf
  obtain ⟨-, hqm, -, -, -, hpb, -⟩ := hq
  have : Mono (η[B]) := ⟨fun a b _ => toUnit_unique a b⟩
  have : Mono i := hpb.mono_fst_of_mono
  let φ : splitTorus (Sp k) (X × ULift.{0} ℤ) ⟶ G :=
    (torusMap _ (AddMonoidHom.inl X (ULift.{0} ℤ)) ≫ i) * (torusMap _ (AddMonoidHom.inr X (ULift.{0} ℤ)) ≫ j)
  obtain ⟨X', _, _, _, i', ρ, h1, h2, -, h3, hV'⟩ := GlobalTheory.T.splitTorus_image_factor_quotient_goodOpen k G hG (X × ULift.{0} ℤ) φ
    (by simp only [φ]; rw [Hom.mul_def]; infer_instance)
  have hr : Module.finrank ℤ X' ≤ Module.finrank ℤ X := by
    have hP : P (Module.finrank ℤ X') := ⟨X', _, ‹_›, ‹_›, i', h1, hV', rfl⟩
    rw [hn]
    exact Nat.le_findGreatest (hb _ hP) hP
  have e1 : torusMap _ (AddMonoidHom.fst X (ULift.{0} ℤ)) ≫ φ = i := by
    simp only [φ, MonObj.comp_mul, ← Category.assoc, ← torusMap_comp, AddMonoidHom.fst_comp_inl,
      AddMonoidHom.fst_comp_inr, torusMap_id, torusMap_zero, Category.id_comp, MonObj.one_comp, _root_.mul_one]
  have e2 : torusMap _ (AddMonoidHom.snd X (ULift.{0} ℤ)) ≫ φ = j := by
    simp only [φ, MonObj.comp_mul, ← Category.assoc, ← torusMap_comp, AddMonoidHom.snd_comp_inl,
      AddMonoidHom.snd_comp_inr, torusMap_id, torusMap_zero, Category.id_comp, MonObj.one_comp, _root_.one_mul]
  let σ := torusMap _ (AddMonoidHom.fst X (ULift.{0} ℤ)) ≫ ρ
  have e3 : σ ≫ i' = i := by rw [Category.assoc, h3, e1]
  have : Mono σ := mono_of_mono_fac e3
  obtain ⟨τ, hτ⟩ := exists_inv σ hr
  have e4 : i' = τ ≫ i := by rw [← e3, ← Category.assoc, hτ, Category.id_comp]
  have e5 : i ≫ q = 1 := hpb.w
  rw [← e2, ← h3, e4]
  simp only [Category.assoc, e5, MonObj.comp_one]

end GlobalTheory.SS.MaxTorus
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis

theorem _root_.GlobalTheory.T.model_trait_extension_polarised_flat_bundleIso : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β), (∀ (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (y : Sp (FractionRing W) ⟶ Y.X) (s : Sp W ⟶ Sp O), y ≫ Y.s = jK W ≫ s → ∃ χ : Sp W ⟶ Y.X, y = jK W ≫ χ) ∧ (∀ (K : Type) [Field K] (y : Sp K ⟶ Xo.XF c), PolAt Y.t (y ≫ Y.j)) ∧ Flat Y.t.G.hom ∧ ∀ (S : Scheme.{0}) (t : SAB H S) (χ : S ⟶ Y.X) (m : SABMap t Y.t χ) (L : RigLB t.G), L = t.PP → ∃ ω : LB.Iso L.L (Y.t.PP.L.pull m.φ), RigPull t.G Y.t.G χ m.φ ω L.rig Y.t.PP.rig := by
  first | exact @GlobalTheory.ModelFacts.model_facts | exact GlobalTheory.ModelFacts.model_facts | (intros; apply GlobalTheory.ModelFacts.model_facts <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Relabel

noncomputable section
namespace GlobalTheory.Relabel

theorem c_smul_val {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F]
    [Algebra (FractionRing R) F] {N : NumD F} {O : Type} [CommRing O] [StarRing O] [Module O D.X]
    (ν : NumOf D F N) (oa : D.OAct O) (x : O) (χ : N.X) :
    N.c (ν.eX.symm (x • ν.eX χ)) = actV ν oa.onB x (N.c χ) := by
  rw [actV, ν.eA.eq_symm_apply, ν.c_eq, ν.c_eq, ν.eX.apply_symm_apply, DegPre.cF, oa.c_lin, Category.assoc]

theorem actq_cancel {F : Type} [Field F] {s s' s₀ s₀' t h₁ h₂ h₃ h₄ h₅ h₆ : Fˣ} {ρ ρ' : F}
    (e₁ : (s : F) = s₀ * ρ) (e₂ : s' * h₃ = s * t * h₅ * h₆) (e₃ : s₀' * h₄ = s₀ * t * h₁ * h₂)
    (e₄ : ρ' * (h₁ * h₂ * h₃ : Fˣ) = ρ * (h₄ * h₅ * h₆ : Fˣ)) : (s' : F) = s₀' * ρ' := by
  have a := congrArg Units.val e₂
  have b := congrArg Units.val e₃
  simp only [Units.val_mul] at a b e₄
  refine mul_right_cancel₀ (mul_ne_zero h₃.ne_zero h₄.ne_zero) ?_
  rw [e₁] at a
  linear_combination (h₄ : F) * a - ρ' * h₃ * b - (s₀ : F) * t * e₄

theorem actCompat_of_rosV : GlobalFnsSt → BrGtSt → AllD fun {E} _ _ _ {H} D => letI := H.starRing; ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing R') F] (A : ArcF D R F) (D' : DegPre R') [Module (𝓞 E) D'.X] (oa' : D'.OAct (𝓞 E)), D'.PsiEven → D'.TauBimult → ∀ (N' : NumD F) (ν' : NumOf D' F N') (k : ℕ) (β : A.N.Form k) (u : Fˣ) (r : ℕ → Fˣ) (J : NumD.Iso (A.N.twist β u) N'), Roots u r → A.Bal β → (∀ (x : 𝓞 E) y, ν'.eX (J.e (A.act x y)) = x • ν'.eX (J.e y)) → (∀ (x : 𝓞 E) b, J.φ (actV (N := A.N) A.ν A.oa.onB x b) = actV ν' oa'.onB x (J.φ b)) → (∀ a : 𝓞 E, ∃ ρ ρ', RosV A.ν A.oa.onB a ρ ∧ RosV ν' oa'.onB a ρ' ∧ ∀ b b' : A.N.A, ρ' (J.φ b) (J.φ b') * (J.h (actV (N := A.N) A.ν A.oa.onB (star a) b) * J.h b' * J.h (b * actV (N := A.N) A.ν A.oa.onB a b') : Fˣ) = ρ b b' * (J.h (actV (N := A.N) A.ν A.oa.onB (star a) b * b') * J.h b * J.h (actV (N := A.N) A.ν A.oa.onB a b') : Fˣ)) → ActCompat A.ν A.oa ν' oa' β u r J := by
  intro hG hB E _ _ _ H D
  letI := H.starRing
  intro R R' _ _ _ _ F _ _ _ _ A D' _ oa' he' hb' N' ν' k β u r J hr hbal hX hA hρ
  intro j hj x p₀ p₁ p₀' p₁' q₀ q₁ q₀' q₁' ⟨q, hqy, hqg, hqe⟩ h₀ h₁ t₀ t₁ h₀' h₁'
  obtain ⟨-, -, -, -, B⟩ := hB R A.D₀ A.even A.bimult F A.N A.ν
  obtain ⟨-, -, -, -, B'⟩ := hB R' D' he' hb' F N' ν'
  obtain ⟨τ, hτ, hτe, -⟩ := (twJ_mulEquiv F A.N N' k β u J).1 (r j) j (hr.pow hj)
  obtain ⟨qv, hqv, -⟩ := (B j).1 q
  obtain ⟨q', hq'⟩ := (B' j).2.1 (τ qv)
  have tq := (hτ qv _).1 rfl
  obtain ⟨ρ, ρ', hρ₁, hρ₂, hρ₃⟩ := hρ x
  obtain ⟨vb, vs⟩ := ((gtAct_values hG R A.D₀ F A.N A.ν (𝓞 E)).2 A.oa x ρ hρ₁ _ _ _ _ h₀.2 hqv.2).1 hqg
  have hy : qv.1.1.toAdd = A.act x q₀.1.1.toAdd := by
    rw [ArcF.act, A.ν.eX.eq_symm_apply, hqv.1, h₀.1, hqy]
  obtain ⟨P, ⟨Py, Pb, Ps⟩, Py', Pb', Ps'⟩ := tq
  obtain ⟨P₀, ⟨P₀y, P₀b, P₀s⟩, P₀y', P₀b', P₀s'⟩ := t₀
  refine ⟨q', ?_, ?_, ?_⟩
  · rw [← hq'.1, ← h₀'.1, Py', P₀y', Py, P₀y]
    exact (congrArg (fun y => ν'.eX (J.e y)) hy).trans (hX _ _)
  · refine ((gtAct_values hG R' D' F N' ν' (𝓞 E)).2 oa' x ρ' hρ₂ _ _ _ _ h₀'.2 hq'.2).2 ⟨?_, ?_⟩
    · rw [Pb', P₀b', Pb, P₀b, vb]
      exact hA _ _
    · rw [J.e.surjective.forall]
      intro (χ : A.N.X)
      have e₁ := vs χ
      have e₂ := Ps' χ
      have e₃ := P₀s' (A.act (star x) χ)
      have e₄ := hρ₃ (A.N.c χ) q₀.1.2.b
      have c₁ : (A.N.twist β u).c (A.act (star x) χ) = actV (N := A.N) A.ν A.oa.onB (star x) (A.N.c χ) :=
        c_smul_val A.ν A.oa (star x) χ
      rw [Ps, Pb, vb, hy, hbal] at e₂
      rw [P₀s, P₀b, c₁] at e₃
      have l : ν'.eX.symm (star x • ν'.eX (J.e χ)) = J.e (A.act (star x) χ) := by
        rw [ν'.eX.symm_apply_eq, hX]
      have c₂ : N'.c (J.e χ) = J.φ (A.N.c χ) := J.c_eq χ
      rw [l, c₂, P₀b', P₀b]
      exact actq_cancel e₁ e₂ e₃ e₄
  · refine ((B' j).2.2 q' p₁' _ _ hq' h₁').2 ?_
    rw [← (hτ q₁ q₁').2 t₁]
    exact (hτe _ _).1 (((B j).2.2 q p₁ _ _ hqv h₁).1 hqe)

end GlobalTheory.Relabel
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Relabel

theorem _root_.GlobalTheory.T.arcTorsionLabels_action_compat : Laws → BrGtSt → AllD fun {E} _ _ _ {H} D => letI := H.starRing; ∀ (R : Type) [CommRing R] [IsDomain R] (C : Type) [NormedField C] [IsAlgClosed C] [Algebra (FractionRing R) C] (A : ArcF D R C) (o : Full D C) (M : Mdl o), M.P.TorsionIso → ∀ (N' : NumD C) (ν' : NumOf M.P.D.toPre C N') (k : ℕ) (β : A.N.Form k) (u r : Cˣ) (J : NumD.Iso (A.N.twist β u) N') (j : ℕ), 0 < j → r ^ j = u → (∀ x (p : (A.N.twist β u).QT j) (q' : N'.QT j) p' z, TwRel β u r (A.q _ x) p → q'.1.1.toAdd = J.e p.1.1.toAdd → J.Rel p.1.2 q'.1.2 → ν'.QPt p' q' → z.left = (o.I.ev j x).left ≫ M.φ → M.P.ToA C j p' z) → ∀ (x : 𝓞 E) (b : A.N.A), b ^ j = 1 → J.φ (actV (N := A.N) A.ν A.oa.onB x b) = actV ν' M.P.oD.onB x (J.φ b) := by
  first | exact @GlobalTheory.Relabel.act_compat_on_torsion | exact GlobalTheory.Relabel.act_compat_on_torsion | (intros; apply GlobalTheory.Relabel.act_compat_on_torsion <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Relabel

namespace GlobalTheory.Relabel

theorem exists_tateIsoQ_twJ : BrGtSt → BrWpSt → AllD fun {E} _ _ _ {H} D => letI := H.starRing; ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing R') F] (A : ArcF D R F) (D' : DegPre R') [Module (𝓞 E) D'.X] (oa' : D'.OAct (𝓞 E)), D'.PsiEven → D'.TauBimult → ∀ (N' : NumD F) (ν' : NumOf D' F N') (k : ℕ) (β : A.N.Form k) (u : Fˣ) (r : ℕ → Fˣ) (J : NumD.Iso (A.N.twist β u) N'), Roots u r → ActCompat A.ν A.oa ν' oa' β u r J → ∃ I' : TateIsoQ D D' oa' F, I'.ζ = A.I.ζ ∧ ∀ j, 0 < j → ∀ x, ∃ q', TwJ β u (r j) J (A.q j x) q' ∧ ν'.QPt (I'.ev j x) q' := by
  intro hGt hWp
  unfold BrGtSt AllN at hGt
  unfold BrWpSt AllN at hWp
  unfold AllD
  intro E _ _ _ H D R R' _ _ _ _ F _ _ _ _ A D' _ oa' hE' hB' N' ν' k β u r J hr hact
  unfold ActCompat at hact
  have hG := hGt R A.D₀ A.even A.bimult F A.N A.ν
  have hG' := hGt R' D' hE' hB' F N' ν'
  have hW := hWp R A.D₀ A.even A.bimult F A.N A.ν
  have hW' := hWp R' D' hE' hB' F N' ν'
  have hI := GlobalTheory.T.twist_iso_torsionRepresentative_mulEquiv F A.N N' k β u J
  choose τ hτ using fun n (hn : 0 < n) => hI.1 (r n) n (hr.pow hn)
  have hex : ∀ n (a : D.La), ∃ p : QkPt D' F n, ∀ hn : 0 < n, ν'.QPt p (τ n hn (A.q n a)) := by
    intro n a
    by_cases hn : 0 < n
    · obtain ⟨p, hp⟩ := (hG'.2.2.2.2 n).2.1 (τ n hn (A.q n a))
      exact ⟨p, fun _ => hp⟩
    · obtain ⟨p, -⟩ := (hG'.2.2.2.2 n).2.1 1
      exact ⟨p, fun h => absurd h hn⟩
  choose ev hev using hex
  let I' : TateIsoQ D D' oa' F :=
    { ζ := A.I.ζ
      ζ_prim := A.I.ζ_prim
      ζ_pow := A.I.ζ_pow
      ev := ev
      add := by
        intro n hn a b
        obtain ⟨q₀, hy, hadd, heq⟩ := A.I.add n hn a b
        obtain ⟨w₀, hw₀, -⟩ := (hG.2.2.2.2 n).1 q₀
        have hw : w₀ = A.q n a * A.q n b := by
          apply Subtype.ext
          apply Prod.ext
          · apply Multiplicative.toAdd.injective
            apply A.ν.eX.injective
            rw [hw₀.1, hy, ← (A.hq n a).1, ← (A.hq n b).1, ← map_add (f := _)]
            rfl
          · exact (hG.2.2.1 _ _ _ _ _ _ (A.hq n a).2 (A.hq n b).2 hw₀.2).mp hadd
        have hqe := ((hG.2.2.2.2 n).2.2 _ _ _ _ hw₀ (A.hq n (a + b))).mp heq
        rw [hw] at hqe
        have hqe' := ((hτ n hn).2.1 _ _).mp hqe
        rw [map_mul] at hqe'
        obtain ⟨p, hp⟩ := (hG'.2.2.2.2 n).2.1 (τ n hn (A.q n a) * τ n hn (A.q n b))
        refine ⟨p, ?_, ?_, ?_⟩
        · rw [← hp.1, ← (hev n a hn).1, ← (hev n b hn).1, ← map_add (f := _)]
          rfl
        · exact (hG'.2.2.1 _ _ _ _ _ _ (hev n a hn).2 (hev n b hn).2 hp.2).mpr rfl
        · exact ((hG'.2.2.2.2 n).2.2 _ _ _ _ hp (hev n (a + b) hn)).mpr hqe'
      lin := by
        intro n hn x a
        exact hact n hn x _ _ _ _ _ _ _ _ (A.I.lin n hn x a) (A.hq n a) (A.hq n (x • a))
          (((hτ n hn).1 _ _).mp rfl) (((hτ n hn).1 _ _).mp rfl) (hev n a hn) (hev n (x • a) hn)
      ker := by
        intro n hn a b
        rw [(hG'.2.2.2.2 n).2.2 _ _ _ _ (hev n a hn) (hev n b hn), ← (hτ n hn).2.1,
          ← (hG.2.2.2.2 n).2.2 _ _ _ _ (A.hq n a) (A.hq n b)]
        exact A.I.ker n hn a b
      onto := by
        intro n hn p
        obtain ⟨v, hv, -⟩ := (hG'.2.2.2.2 n).1 p
        obtain ⟨p₀, hp₀⟩ := (hG.2.2.2.2 n).2.1 ((τ n hn).symm v)
        obtain ⟨a, ha⟩ := A.I.onto n hn p₀
        refine ⟨a, ?_⟩
        rw [(hG'.2.2.2.2 n).2.2 _ _ _ _ (hev n a hn) hv]
        have h := ((hτ n hn).2.1 _ _).mp (((hG.2.2.2.2 n).2.2 _ _ _ _ (A.hq n a) hp₀).mp ha)
        rwa [MulEquiv.apply_symm_apply] at h
      tower := by
        intro n m hn hm a
        have hnm : 0 < n * m := Nat.mul_pos hn hm
        obtain ⟨q₀, hy, hns, heq⟩ := A.I.tower n m hn hm a
        obtain ⟨w₀, hw₀, -⟩ := (hG.2.2.2.2 n).1 q₀
        have h1 : w₀.1.1 = (A.q (n * m) a).1.1 := by
          apply Multiplicative.toAdd.injective
          apply A.ν.eX.injective
          rw [hw₀.1, hy, (A.hq (n * m) a).1]
        have h2 : w₀.1.2 = (A.q (n * m) a).1.2 ^ m :=
          (GtValues.isNsmul_val A.ν m (A.hq (n * m) a).2 hw₀.2).mp hns
        obtain ⟨e1, e2⟩ := hI.2 (r n) (r (n * m)) n (n * m) m w₀ (A.q (n * m) a) (τ n hn w₀)
          (τ (n * m) hnm (A.q (n * m) a)) (hr.2 n m hn hm) h1 h2 (((hτ n hn).1 _ _).mp rfl)
          (((hτ (n * m) hnm).1 _ _).mp rfl)
        obtain ⟨p, hp⟩ := (hG'.2.2.2.2 n).2.1 (τ n hn w₀)
        refine ⟨p, ?_, ?_, ?_⟩
        · rw [← hp.1, ← (hev (n * m) a hnm).1, e1]
        · exact (GtValues.isNsmul_val ν' m (hev (n * m) a hnm).2 hp.2).mpr e2
        · rw [(hG'.2.2.2.2 n).2.2 _ _ _ _ hp (hev n a hn), ← (hτ n hn).2.1,
            ← (hG.2.2.2.2 n).2.2 _ _ _ _ hw₀ (A.hq n a)]
          exact heq
      isom := by
        intro n hn a b
        have h1 : 1 ≤ n := hn
        rw [hW' n h1 _ _ _ _ _ (hev n a hn) (hev n b hn), (hτ n hn).2.2]
        exact (hW n h1 _ _ _ _ _ (A.hq n a) (A.hq n b)).mp (A.I.isom n hn a b) }
  exact ⟨I', rfl, fun j hj x => ⟨τ j hj (A.q j x), ((hτ j hj).1 _ _).mp rfl, hev j x hj⟩⟩

end GlobalTheory.Relabel
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Relabel

theorem _root_.GlobalTheory.T.torusExtension_action_in_values : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (N : NumD F) (ν : NumOf D F N) (O : Type) [CommRing O] [StarRing O], (∀ (oa : D.P.OAct O) (x : O), ∃ ρ, RosV ν oa x ρ) ∧ ∀ [Module O D.X] (oa : D.OAct O) (x : O) (ρ : N.A → N.A → F), RosV ν oa.onB x ρ → ∀ g g' v v', ν.Pt g v → ν.Pt g' v' → (GtAct oa x g g' ↔ v'.b = actV ν oa.onB x v.b ∧ ∀ χ, (v'.s χ : F) = v.s (ν.eX.symm (star x • ν.eX χ)) * ρ (N.c χ) v.b) := by
  first | exact @GlobalTheory.Relabel.gtAct_values | exact GlobalTheory.Relabel.gtAct_values | (intros; apply GlobalTheory.Relabel.gtAct_values <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Relabel

theorem _root_.GlobalTheory.T.normalisedRosatiGenerator_values_move_along_iso : Laws → ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (D : DegPre R) (D' : DegPre R') (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing R') F] (N N' : NumD F) (ν : NumOf D F N) (ν' : NumOf D' F N') (O : Type) [CommRing O] [StarRing O] (oa : D.P.OAct O) (oa' : D'.P.OAct O) (Φ : (TF (R := R) F ⊗ D.P.A).left ⟶ D'.P.A.left) (w : LB.Iso (D.P.L.pull (snd (TF (R := R) F) D.P.A).left) (D'.P.L.pull Φ)) (φ : N.A →* N'.A) (wv : N.A → F), w.IsGen → Φ ≫ D'.P.A.hom = (fst (TF (R := R) F) D.P.A).left ≫ (TF (R := R') F).hom → (∀ x, (lift (𝟙 (TF (R := R) F)) (ν.eA x)).left ≫ Φ = (ν'.eA (φ x)).left) → (∀ x, wv x = valF (lift (𝟙 (TF (R := R) F)) (ν.eA x)).left _ (w.s (fun _ => ν'.J (ν'.eA (φ x)).left, fun _ => ν.J (ν.eA x).left)).val) → (∀ y b, φ (actV ν oa y b) = actV ν' oa' y (φ b)) → ∀ (a : O) ρ ρ', RosV ν oa a ρ → RosV ν' oa' a ρ' → ∀ b b', ρ' (φ b) (φ b') * (wv (actV ν oa (star a) b) * wv b' * wv (b * actV ν oa a b')) = ρ b b' * (wv (actV ν oa (star a) b * b') * wv b * wv (actV ν oa a b')) := by
  first | exact @GlobalTheory.RosMove.rosV_move | exact GlobalTheory.RosMove.rosV_move | (intros; apply GlobalTheory.RosMove.rosV_move <;> assumption)
end
