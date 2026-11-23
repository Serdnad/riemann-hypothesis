module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.MorAlgSt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle143
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle131
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsMonHomOfPG
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle122
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle145
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle130
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle146
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle133
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle147
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle148
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle149
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

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN

namespace GlobalTheory.LN.PreCompare

theorem exists_cmp : Laws → Laws2 → Ega → ∀ (R V : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing V] [IsDomain V] [IsLocalRing V] (I : Ideal R) (I' : Ideal V), AdmBase R I → AdmBase V I' → I' ≠ ⊤ → ∀ φ : R →+* V, I.map φ ≤ I' → ∀ (D : DegPre R) (D' : DegPre V) (A : PolAV (Sp (FractionRing R))) (A' : PolAV (Sp (FractionRing V))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (G' : Over (Spec (CommRingCat.of V))) [GrpObj G'] [IsCommMonObj G'] (U : PreU I D A G) (U' : PreU I' D' A' G') (F : G'.left ⟶ G.left) (pb : IsGrpPullback G' G (spMap φ) F) (wL : LB.Iso U'.P.L.L (U.P.L.L.pull F)), IsCPMap U'.P U.P (spMap φ) F pb.1.w wL → ∃ C : Cmp φ U U' F, C.wL = wL := by
  intro hL _ _ R V _ _ _ _ _ _ I I' _ hV _ φ hI D D' A A' G _ _ G' _ _ U U' F pb wL hw
  obtain ⟨D₁, U₁, C₁, hP, hC⟩ := PreBaseChange.exists_cmp_pull hL R V I I' φ hI D D' A A' G G' U U' F pb wL hw
  obtain ⟨semi, gen, gen_hom, P, wA, wA_gen, gt, gt_q, gt_t, w, w_gen, w_vals, w_compat⟩ := U'
  obtain rfl : U₁.P = P := hP
  obtain rfl : C₁.wL = wL := eq_of_heq hC
  obtain ⟨C₂, h₂⟩ := PreUnique.exists_cmp_id hL V I' hV D₁ D' A' A' G' U₁
    ⟨semi, gen, gen_hom, U₁.P, wA, wA_gen, gt, gt_q, gt_t, w, w_gen, w_vals, w_compat⟩ (idIso U₁.P.L.L) (by simp)
    (IsCPMap.id U₁.P)
  refine GlobalTheory.T.exists_comparison_comp_along_identity R V I I' φ D D₁ D' A A' A' G G' U U₁ _ F C₁ C₂ C₁.wL hw fun Z r z j i k hj hi hk => ?_
  rw [h₂]
  have a := (isGen_iff _).1 C₁.wL_map.gen Z r z j j i k hj hj hi hk
  rw [gm_self U.P.L.isLB (r ≫ F) z hj, _root_.one_mul] at a
  exact ((congrArg₂ (· * ·) a (gw_idIso U₁.P.L.L r z hi hk)).trans (by rw [mul_comm, mul_inv_cancel_left])).symm

end GlobalTheory.LN.PreCompare
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
open GlobalTheory.Ex.AbPartIso

theorem _root_.GlobalTheory.T.abelianPartIso_carries_symmetry_values : GlobalFnsSt → AllIso fun {_} _ _ {_} {_} {F} _ _ {N} {N'} ν ν' {_} w f => ∀ x, (N'.σ (f x) : F) * wVal ν ν' w f x = (N.σ x : F) * wVal ν ν' w f x⁻¹ := by
  first | exact @GlobalTheory.AbPartSym.sym_values | exact GlobalTheory.AbPartSym.sym_values | (intros; apply GlobalTheory.AbPartSym.sym_values <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Trait

theorem _root_.GlobalTheory.T.modelIso_of_valued_agreement_over_field : GlobalTheory.UT.LL → AllS fun {_} _ _ _ {H} {_} {_} {_} {_} _ {_} {_} _ _ {_} a {C} _ _ A u _ {_} M f {_} ν' J => ∀ u₀ : M.W, (u : C) = algebraMap (FractionRing M.W) C (algebraMap _ _ u₀) → ∀ ψ (he : eSec M.P.D.toPre.P.A ≫ ψ = spMap f ≫ eSec a.D₀.P.A) w e, Fit A u M f ν' J ψ w e → LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec M.P.D.toPre.P.A) (fun _ => 1)) M.P.D.toPre.rig (rigPullOf ψ (spMap f) he a.D₀.P.L a.D₀.rig) → (letI := H.starRing; ∀ x, (M.P.oD.onB.act x).left ≫ ψ = ψ ≫ (a.oa.onB.act x).left) → GlobalTheory.LN.Match a f u₀ M.P.D.toPre M.P.oD ψ he w e := by
  first | exact @GlobalTheory.FitMatch.match_of_fit | exact GlobalTheory.FitMatch.match_of_fit | (intros; apply GlobalTheory.FitMatch.match_of_fit <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Trait

theorem _root_.GlobalTheory.T.exists_completeDVR_extension_torsion_rational : Laws → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (C : Type) [NormedField C] [IsUltrametricDist C] [IsAlgClosed C] [Algebra (FractionRing W) C], CExt W (IsLocalRing.maximalIdeal W) C → ∀ n : ℕ, 1 ≤ n → ∀ (S₁ S₂ : Scheme.{0}) (s₁ : Sp W ⟶ S₁) (s₂ : Sp W ⟶ S₂) (B₁ : PolAV S₁) (B₂ : PolAV S₂), ∃ (W' : Type) (_ : CommRing W') (_ : IsDomain W') (_ : IsLocalRing W') (_ : Algebra (FractionRing W') C) (io : W →+* W'), GlobalTheory.LN.CDvr W' ∧ Function.Injective io ∧ io.Finite ∧ IsLocalHom io ∧ Along io C ∧ CExt W' (IsLocalRing.maximalIdeal W') C ∧ (∀ (B : PolAV (Sp W')) (ψ : B.A.left ⟶ B₁.A.left), IsGrpPullback B.A B₁.A (spMap io ≫ s₁) ψ → RatTors B C n) ∧ ∀ (B : PolAV (Sp W')) (ψ : B.A.left ⟶ B₂.A.left), IsGrpPullback B.A B₂.A (spMap io ≫ s₂) ψ → RatTors B C n := by
  first | exact @GlobalTheory.Ex.TorsionField.exists_cDvr_ratTors | exact GlobalTheory.Ex.TorsionField.exists_cDvr_ratTors | (intros; apply GlobalTheory.Ex.TorsionField.exists_cDvr_ratTors <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Trait

theorem _root_.GlobalTheory.T.valuesIso_comm_action_abelianPart_torsion : GlobalTheory.UT.LL → BrGtSt → AllS fun {E} _ _ _ {H} {_} {_} {_} {_} _ {_} {_} _ _ {_} a {_} _ _ A u r {_} M _ {_} ν' J => M.P.TorsionIso → ∀ k : ℕ, 0 < k → Labels A u r M ν' J k → (∀ (x : 𝓞 E) y, ν'.eX (J.e (A.arc.act x y)) = x • ν'.eX (J.e y)) → ∀ (x : 𝓞 E) (y y' : A.N.A), y ^ k = 1 → (letI := H.starRing; A.ν.eA y' = A.ν.eA y ≫ a.oa.onB.act x → ν'.eA (J.φ y') = ν'.eA (J.φ y) ≫ M.P.oD.onB.act x) := by
  first | exact @GlobalTheory.Ex.ActPt.main | exact GlobalTheory.Ex.ActPt.main | (intros; apply GlobalTheory.Ex.ActPt.main <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Trait

theorem _root_.GlobalTheory.T.levelCondition_of_one_algClosed_field : GlobalTheory.UT.LL → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R O' : Type) [CommRing R] [IsDomain R] [CharZero R] [CommRing O'] [IsDomain O'] (I : Ideal R), AdmBase R I → ∀ (t : SAB H (Sp R)) (P : PELUnif I t) (D₀ : DegPre O'), D₀.TauBimult → ∀ (f : O' →+* R) (ψ : P.D.toPre.P.A.left ⟶ D₀.P.A.left) (w : LB.Iso P.D.toPre.P.L (D₀.P.L.pull ψ)) (e : D₀.X ≃+ P.D.toPre.X), IsGrpPullback P.D.toPre.P.A D₀.P.A (spMap f) ψ → w.IsGen → ∀ k : ℕ, 1 ≤ k → ∀ (p₀ : QkPt D₀ (FractionRing O') k) (s : D₀.X → FractionRing R) (x₀ : Sp (FractionRing R) ⟶ P.A.A.left) (C : Type) [Field C] [IsAlgClosed C] [Algebra (FractionRing R) C] [Algebra (FractionRing O') C], Along f C → ∀ (q₀ : QkPt D₀ C k) (q : QkPt P.D.toPre C k) (x : TFK (R := R) C ⟶ P.A.A), QkExt (algebraMap _ C) p₀ q₀ → q.y = e q₀.y → (∀ χ, GenRel w (q.g.s (e χ)) (q₀.g.s χ) (algebraMap _ C (s χ))) → x.left = jFK (R := R) C ≫ x₀ → P.ToA C k q x → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing O') F], Along f F → ∀ (q₀' : QkPt D₀ F k) (q' : QkPt P.D.toPre F k) (x' : TFK (R := R) F ⟶ P.A.A), QkExt (algebraMap _ F) p₀ q₀' → q'.y = e q₀'.y → (∀ χ, GenRel w (q'.g.s (e χ)) (q₀'.g.s χ) (algebraMap _ F (s χ))) → x'.left = jFK (R := R) F ≫ x₀ → P.ToA F k q' x' := by
  first | exact @GlobalTheory.LevelField.toA_of_toA | exact GlobalTheory.LevelField.toA_of_toA | (intros; apply GlobalTheory.LevelField.toA_of_toA <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Trait

theorem _root_.GlobalTheory.T.levelCondition_valuedField_twistedUniformisation : GlobalTheory.UT.LL → BrGtSt → AllS fun {_} _ _ _ {_} {D} {l} {_} {_} _ {_} {O'} _ _ {_} a {C} _ _ A u r {o} M f {_} ν' J => M.P.TorsionIso → ∀ ψ w e, Fit A u M f ν' J ψ w e → ∀ k : ℕ, 0 < k → k ∣ l.M' → Labels A u r M ν' J k → ∀ (p₀ : QkPt a.D₀ (FractionRing O') k) (v : D.La), (∀ p, QkExt (algebraMap _ C) p₀ p → QkPt.Equiv a.D₀ C p (A.I.ev k v)) → ∀ z : TFK (R := M.W) C ⟶ M.P.A.A, z.left = (o.I.ev k v).left ≫ M.φ → ∃ (q₀ : QkPt a.D₀ C k) (q : QkPt M.P.D.toPre C k), QkExt (algebraMap _ C) p₀ q₀ ∧ q.y = e q₀.y ∧ (∀ χ, GenRel w (q.g.s (e χ)) (q₀.g.s χ) ((u : C) ^ (a.be q₀.y χ / k))) ∧ M.P.ToA C k q z := by
  first | exact @GlobalTheory.Ex.Trait.LevelClause.level_clause | exact GlobalTheory.Ex.Trait.LevelClause.level_clause | (intros; apply GlobalTheory.Ex.Trait.LevelClause.level_clause <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.ThetaPtMove GlobalTheory.ConstFam
open GlobalTheory.Ex.OneGen GlobalTheory.UT


theorem _root_.GlobalTheory.T.exists_generator_thetaPoint_normalised_thetaConstants : ∀ (K : Type) [Field K] (P : PolAV (Sp K)) (ρ : LB.Gen (P.L.pull (eSec P.A))), ρ.IsGen → ∀ (m : ℕ) (Ix : Type) (x : Ix → (baseOver (Sp K) ⟶ P.A)) (v : Ix → K), (∀ i, x i ^ (m ^ 2) = 1) → IsThetaPt P m x (fun i => fnOf (v i)) → ∃ th : LB.Sec (LPow P.A P.L ((1 : ℕ) : ℤ) (baseOver (Sp K))), IsGenSec P.A P.L ((1 : ℕ) : ℤ) th ∧ ∀ i, ThG P.A P.L ρ m th (x i) (fnOf (v i)) := by
  first | exact @GlobalTheory.Ex.OneGen.exists_gen_thG_of_isThetaPt | exact GlobalTheory.Ex.OneGen.exists_gen_thG_of_isThetaPt | (intros; apply GlobalTheory.Ex.OneGen.exists_gen_thG_of_isThetaPt <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.ThetaPtMove GlobalTheory.ConstFam
open GlobalTheory.Ex.OneGen GlobalTheory.UT


theorem _root_.GlobalTheory.T.exists_universal_section_basis_polarised_fibre : Laws2 → ∀ (S S' : Scheme.{0}) (G : Over S) [GrpObj G] (L : LB G.left), L.IsLB → ∀ (P : PolAV S') (f : S' ⟶ S) (φ : P.A.left ⟶ G.left), IsGrpPullback P.A G f φ → LBIso P.L (L.pull φ) → ∀ (K : Type) [Field K] (y : Sp K ⟶ S') (x : Sp K ⟶ S), y ≫ f = x → ∃ e, UnivBasis G L x e := by
  first | exact @GlobalTheory.Ex.OneGen.exists_univBasis_of_fibre | exact GlobalTheory.Ex.OneGen.exists_univBasis_of_fibre | (intros; apply GlobalTheory.Ex.OneGen.exists_univBasis_of_fibre <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.ThetaPtMove GlobalTheory.ConstFam
open GlobalTheory.Ex.OneGen GlobalTheory.UT


theorem _root_.GlobalTheory.T.generatingSection_finite_ext_normal_domain_isBasis : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [Flat G.hom] (L : LB G.left), L.IsLB → ∀ (W W' : Type) [CommRing W] [IsDomain W] [IsIntegrallyClosed W] [CommRing W'] [IsDomain W'] (i : W →+* W'), Function.Injective i → i.Finite → ∀ (χ : Sp W ⟶ S) (σ : LB.Sec (LPow G L ((1 : ℕ) : ℤ) (Over.mk χ))), IsGenSec G L ((1 : ℕ) : ℤ) (VVRank.pullS G _ (Over.homMk (spMap i) rfl : Over.mk (spMap i ≫ χ) ⟶ Over.mk χ) σ) → (∃ e, UnivBasis G L (jK W ≫ χ) e) → SecM.ofSec G (VVRank.pullS G _ (Over.homMk (jK W) rfl : Over.mk (jK W ≫ χ) ⟶ Over.mk χ) σ) ≠ 0 → GlobalTheory.LN.BasisAlong G L 1 (𝟙 (Over.mk χ)) (fun _ : Fin 1 => σ) := by
  first | exact @GlobalTheory.Ex.OneGenBasis.basisAlong_of_isGenSec | exact GlobalTheory.Ex.OneGenBasis.basisAlong_of_isGenSec | (intros; apply GlobalTheory.Ex.OneGenBasis.basisAlong_of_isGenSec <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.ThetaPtMove GlobalTheory.ConstFam
open GlobalTheory.Ex.OneGen GlobalTheory.UT


theorem _root_.GlobalTheory.T.exists_nz_of_polAt' : Laws → Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S) (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (χ : Sp W ⟶ S) (t' : SAB H (Sp W)) (_ : SABMap t' t χ), GlobalTheory.LN.PolAt t' (jK W) → ∃ σ : LB.Sec (LPow t.G t.PP.L ((1 : ℕ) : ℤ) (Over.mk χ)), ∀ (W' : Type) [CommRing W'] [IsLocalRing W'] (i : W →+* W') (χ' : Sp W' ⟶ S) (h : spMap i ≫ χ = χ'), NZ t.G t.PP.L χ' (VVRank.pullS t.G _ (Over.homMk (spMap i) h : Over.mk χ' ⟶ Over.mk χ) σ) := by
  first | exact @GlobalTheory.Ex.OneGen.exists_nz_of_polAt | exact GlobalTheory.Ex.OneGen.exists_nz_of_polAt | (intros; apply GlobalTheory.Ex.OneGen.exists_nz_of_polAt <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.ThetaPtMove GlobalTheory.ConstFam
open GlobalTheory.Ex.OneGen GlobalTheory.UT


theorem _root_.GlobalTheory.T.uniformisation_generic_fibre_cartesian_to_model_bundleIso : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G), ∃ (w₀ : W0 U) (ρ : LB.Gen (A.L.pull (eSec A.A))) (w : LB.Iso A.L (U.LG.L.pull (U.gen.inv.left ≫ pullback.fst G.hom (jK R)))), IsGrpPullback A.A G (jK R) (U.gen.inv.left ≫ pullback.fst G.hom (jK R)) ∧ NormW U w₀ ρ ∧ w.IsGen ∧ IsRigidificationPullbackCompatibleIso w (jK R) ρ U.LG.rig ∧ ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) (σ : H0 U.LG.L k) (th : SecA A F k), (∀ (Z : Scheme.{0}) (r : Z ⟶ (TFK (R := R) F ⊗ A.A).left) (z : Z) (J) (J'), Good U.LG.L z J → Good A.L z J' → sval σ (r ≫ (snd (TFK (R := R) F) A.A).left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R)) z J = (wVal w z J J' (r ≫ (snd (TFK (R := R) F) A.A).left) ^ (k : ℤ)).val * VVRank.sv A.A th r z J') → ∃ σ' : U.SecGF F k, (∀ z J, Good U.LG.L z J → sval σ' (𝟙 _) z J = sval σ (UnifPre.gFK (G := G) F) z J) ∧ ∀ s, U.ExpandsG F k σ' s → U.ExpandsF F k w₀ th s := by
  first | exact @GlobalTheory.Ex.GenericFibre.exists_isoData | exact GlobalTheory.Ex.GenericFibre.exists_isoData | (intros; apply GlobalTheory.Ex.GenericFibre.exists_isoData <;> assumption)
end
