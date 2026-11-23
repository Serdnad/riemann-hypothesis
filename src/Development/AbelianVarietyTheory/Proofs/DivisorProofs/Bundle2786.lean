module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasThetaConstantsTwoLevelsMoveCartesian
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2702
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2644
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle116
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGeneratorNeZero
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle119
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle063
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.HasBasisOfBasis
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle149
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle171
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle134
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle203
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle098
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsExpandsAtOfIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2691
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaEmbeddingSectionsBaseChangeAffine
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2645
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2698
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2701
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2703
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2687

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UMin.ThNe

variable {S : Scheme.{0}}

theorem ptSecT_translT_mulT {A : Over S} [GrpObj A] (T : Over S) (y : T ⟶ A) (m : ℕ) :
    ptSecT A (1 : T ⟶ A) ≫ translT A y ≫ mulT A T m = ptSecT A (y ^ m) := by
  have e : ptSecT A (1 : T ⟶ A) ≫ translT A y = ptSecT A y := by
    apply CartesianMonoidalCategory.hom_ext
    · simp [ptSecT, translT]
    · simp only [ptSecT, translT, translPt, Category.assoc, lift_snd, Hom.mul_def, comp_lift_assoc, lift_fst_assoc,
        Category.id_comp]
      rw [← Hom.mul_def, _root_.mul_one]
  rw [← Category.assoc, e]
  apply CartesianMonoidalCategory.hom_ext
  · simp [ptSecT, mulT]
  · simp only [ptSecT, mulT, lift_snd, Category.assoc]
    rw [MonObj.comp_pow, lift_snd]

theorem ne_zero_of_thG {K : Type} [Field K] {A : Over S} [GrpObj A] {L : LB A.left} (hL : L.IsLB)
    {ρ : LB.Gen (L.pull (eSec A))} {m : ℕ} {t : Sp K ⟶ S} {th : LB.Sec (LPow A L ((1 : ℕ) : ℤ) (Over.mk t))}
    {y : Over.mk t ⟶ A} {c : K} (H : ThG A L ρ m th y (fn c))
    (hu : ∀ z J, Good L z J → IsUnit (VVRank.sv A th (ptSecT A (y ^ m)).left z J)) : c ≠ 0 := by
  intro hc
  obtain ⟨-, t', α, s₁, θ, -, -, hs₁, hθ, ht, hc'⟩ := H
  obtain ⟨z⟩ : Nonempty (Sp K) := inferInstance
  obtain ⟨J, hJ, -⟩ := exists_good L hL z (K := Empty) Empty.elim Empty.elim (fun a => a.elim) (fun k => k.elim)
  have q := hc' z J hJ
  have a1 := VVRank.sv_of_isTwistPull A ht (ptSecT A 1).left z hJ
  have a2 := VVRank.sv_of_isTwistPull A hs₁ ((ptSecT A 1).left ≫ (translT A θ.pt).left) z hJ
  have e : ((ptSecT A (1 : Over.mk t ⟶ A)).left ≫ (translT A θ.pt).left) ≫ (mulT A (Over.mk t) m).left =
      (ptSecT A (y ^ m)).left := by
    rw [hθ.pt_eq, ← Over.comp_left, ← Over.comp_left, Category.assoc, ptSecT_translT_mulT]
  rw [e] at a2
  rw [a2] at a1
  have f0 : (fn (0 : K) : Γ((Over.mk t).left, ⊤)) = 0 := map_zero _
  rw [hc, f0, gs_eq _ z ⊤ trivial, map_zero, map_zero, zero_mul] at q
  have q2 := a1.symm.trans q
  rw [Units.mul_right_eq_zero, Units.mul_right_eq_zero] at q2
  exact (hu z J hJ).ne_zero q2

theorem exists_pow_eq_of_card {G : Type} [CommGroup G] {m g : ℕ} (hm : 0 < m)
    (h1 : Nat.card {x : G // x ^ m = 1} = m ^ (2 * g)) (h2 : Nat.card {x : G // x ^ (m ^ 2) = 1} = (m ^ 2) ^ (2 * g))
    (x : G) (hx : x ^ m = 1) : ∃ y : G, y ^ (m ^ 2) = 1 ∧ y ^ m = x := by
  let H2 := (powMonoidHom (m ^ 2) : G →* G).ker
  let H1 := (powMonoidHom m : G →* G).ker
  let f : H2 →* G := (powMonoidHom m).comp H2.subtype
  have cH2 : Nat.card H2 = (m ^ 2) ^ (2 * g) := h2 ▸ Nat.card_congr (Equiv.subtypeEquivRight fun y => by simp [H2])
  have cH1 : Nat.card H1 = m ^ (2 * g) := h1 ▸ Nat.card_congr (Equiv.subtypeEquivRight fun y => by simp [H1])
  have cK : Nat.card f.ker = m ^ (2 * g) := by
    rw [← h1]
    refine Nat.card_congr
      { toFun := fun y => ⟨y.1.1, MonoidHom.mem_ker.1 y.2⟩
        invFun := fun x => ⟨⟨x.1, by simp [H2, pow_two, pow_mul, x.2]⟩, MonoidHom.mem_ker.2 x.2⟩
        left_inv := fun y => rfl
        right_inv := fun x => rfl }
  have hpos : 0 < m ^ (2 * g) := pow_pos hm _
  haveI : Finite H2 := Nat.finite_of_card_ne_zero (by rw [cH2]; positivity)
  haveI : Finite H1 := Nat.finite_of_card_ne_zero (by rw [cH1]; positivity)
  have cR : Nat.card f.range = m ^ (2 * g) := by
    have e := Subgroup.card_mul_index f.ker
    rw [Subgroup.index_ker, cK, cH2, show (m ^ 2) ^ (2 * g) = m ^ (2 * g) * m ^ (2 * g) by ring] at e
    exact Nat.eq_of_mul_eq_mul_left hpos e
  have hle : f.range ≤ H1 := by
    rintro _ ⟨y, rfl⟩
    have := y.2
    simp only [H2, MonoidHom.mem_ker, powMonoidHom_apply] at this
    simp [H1, f, ← pow_mul, ← pow_two, this]
  have heq := Subgroup.eq_of_le_of_card_ge hle (by rw [cH1, cR])
  have hx1 : x ∈ H1 := by simpa [H1] using hx
  rw [← heq] at hx1
  obtain ⟨y, hy⟩ := hx1
  exact ⟨y.1, MonoidHom.mem_ker.1 y.2, hy⟩

end GlobalTheory.UMin.ThNe

namespace GlobalTheory.UMin.ThNe

theorem spMap_id_self (R : Type) [CommRing R] : spMap (RingHom.id R) = 𝟙 (Sp R) := Spec.map_id _

theorem th_ne_zero : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left)
    (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (g m N : ℕ) (K : Type) [Field K] (x : Sp K ⟶ S)
    (c : Fin N → K), Odd m → 3 ≤ m → (m : K) ≠ 0 → PolFib G L g x → HasTh G L ρ m x c → ∃ a, c a ≠ 0 := by
  intro S G _ _ L ρ hL hρ g m N K _ x c hm hm3 hmK hpol H
  obtain ⟨hLaws, hLaws2⟩ := abelianSchemeLaws_all
  obtain ⟨P, α, -, hα, hPL⟩ := hpol
  haveI := P.isAb.comm
  obtain ⟨ρ', hρ'⟩ := P.rigid
  have H' : HasTh P.A P.L ρ' m (𝟙 (Sp K)) c := by
    rw [hasTh_iff] at H ⊢
    exact (ThMove.hasTh₂_move S G L ρ hL hρ (Sp K) P.A P.L ρ' x α P.isLB hρ' hα hPL m m N N K (𝟙 _) c c).2
      (by rwa [Category.id_comp])
  obtain ⟨θ, pt, hgθ, hl⟩ := H'
  let i : K →+* AlgebraicClosure K := algebraMap K (AlgebraicClosure K)
  obtain ⟨pt', -, hl'⟩ := GlobalTheory.T.isThetaConstantListOfFibre_pullback_field_extension (Sp K) P.A P.L ρ' P.isLB hρ' m N K (AlgebraicClosure K) i (𝟙 _) θ pt c hl
  have hg' : IsGenSec P.A P.L _ (SecAt.pull P.A P.L θ i) :=
    (gen_of_polFib (Sp K) P.A P.L P.isLB P.g K (𝟙 _) (Model.polFib_self P)).2 θ hgθ (AlgebraicClosure K) i
  have hne := ThetaCoset.ne_zero_of_isGenSec hLaws2.secBaseChangeAny P (spMap i ≫ 𝟙 (Sp K)) hg'
  have hmKb : (m : AlgebraicClosure K) ≠ 0 := by
    rw [← map_natCast i]; exact (map_ne_zero i).2 hmK
  obtain ⟨z, hz, hu⟩ := UT.ExactTerm.exists_good_point hLaws.goodPt hLaws.polBaseChange P (spMap i ≫ 𝟙 (Sp K))
    (n := m) (by omega) hmKb _ hne 1
  have c1 := (hLaws.mulN (Sp K) P m (by omega)).2.2.2.2 (AlgebraicClosure K) (spMap i ≫ 𝟙 (Sp K)) hmKb
  have c2 := (hLaws.mulN (Sp K) P (m ^ 2) (Nat.one_le_iff_ne_zero.2 (pow_ne_zero _ (by omega)))).2.2.2.2
    (AlgebraicClosure K) (spMap i ≫ 𝟙 (Sp K)) (by push_cast; exact pow_ne_zero _ hmKb)
  obtain ⟨y, hy2, hym⟩ := exists_pow_eq_of_card (by omega) c1 c2 (1 * z) (by rw [_root_.one_mul, hz])
  let π : Over.mk (spMap (RingHom.id (AlgebraicClosure K)) ≫ spMap i ≫ 𝟙 (Sp K)) ⟶ Over.mk (spMap i ≫ 𝟙 (Sp K)) :=
    Over.homMk (spMap (RingHom.id (AlgebraicClosure K))) rfl
  obtain ⟨a, ha⟩ := hl'.2.2 (AlgebraicClosure K) (RingHom.id _) (π ≫ y)
    (by rw [← MonObj.comp_pow, hy2, MonObj.comp_one])
  have hya : y = pt' a := by
    apply Over.OverMorphism.ext
    have := ha
    simp only [π, Over.comp_left, Over.homMk_left] at this
    rwa [spMap_id_self, Category.id_comp, Category.id_comp] at this
  refine ⟨a, fun h0 => ?_⟩
  have hth := hl'.2.1 a
  rw [← hya] at hth
  refine ne_zero_of_thG P.isLB hth (fun p J hJ => ?_) (by show i (c a) = 0; rw [h0, map_zero])
  rw [hym]
  exact hu p J hJ

end GlobalTheory.UMin.ThNe
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.SiegTh.CrdMapBC

open GlobalTheory.ProjSpace GlobalTheory.Cartier GlobalTheory.QCoh.Qcqs

theorem secMaps_baseChangeIso {o k : Type} [CommRing o] [CommRing k] (β : o →+* k) (n : ℕ) (j : Fin (n + 1)) :
    SecMaps (baseChangeIso n β) (secPull (coord o n j) (baseChange n β)) (coord k n j) := by
  rintro ⟨i, l⟩
  refine (baseChangeIso_coord n β j i l).trans ?_
  congr 1

theorem pCrd_comp_baseChange {o k A : Type} [CommRing o] [CommRing k] [CommRing A] (β : o →+* k) {n : ℕ}
    (x : Sp A ⟶ PSpace k n) (v : Fin (n + 1) → A) (h : PCrd x v) : PCrd (x ≫ baseChange n β) v := by
  refine (RepBC.secCoord_pull (O1 o n) (coord o n) (baseChange n β) x v).1 ?_
  exact (FibreEmbed.secCoord_iff_of_secMaps (LB.isLB_pull (O1_isLB o n) _) (O1_isLB k n)
    (w := baseChangeIso n β) (fun j => secMaps_baseChangeIso β n j)
    (iSup_nonzeroLocus_secPull (iSup_nonzeroLocus_coord o n) _) (iSup_nonzeroLocus_coord k n)).2 h

theorem exists_map_of_hasDiv : ∀ (k Ω o : Type) [CommRing k] [Field Ω] [Algebra k Ω] [CommRing o] (β : o →+* k) (M : RatModel k Ω) (n : ℕ) (c : Fin (n + 1) → Ω), M.HasDiv c → ∃ h : M.Z ⟶ PSpace o n, h ≫ PSpace.str o n = M.s ≫ spMap β ∧ PCrd (M.pt ≫ h) c := by
  intro k Ω o _ _ _ _ β M n c hc
  obtain ⟨h₀, hs, hp⟩ := GlobalTheory.T.exists_projectiveSpace_map_of_model_hasDiv k Ω M n c hc
  refine ⟨h₀ ≫ baseChange n β, ?_, ?_⟩
  · rw [Category.assoc, baseChange_str, ← Category.assoc, hs]
  · rw [← Category.assoc]
    exact pCrd_comp_baseChange β _ c hp

end GlobalTheory.SiegTh.CrdMapBC
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin.FibExist

theorem polFib_of_point : ∀ (X : Scheme.{0}) (P : PolAV X) (R : Type) [CommRing R] (x : Sp R ⟶ X),
    PolFib P.A P.L P.g x := by
  intro X P R _ x
  obtain ⟨P', g, hg, hgg, mul, t, ht⟩ := GlobalTheory.polBaseChange_holds X (Sp R) x P
  obtain ⟨t', ht', -⟩ := GenericSectionBasis.exists_inv_iso t ht
  refine ⟨P', g, hgg, ⟨hg, fun T a b a₀ b₀ ha hb => ?_⟩, ⟨t', ht'⟩⟩
  have ea : a₀ = toBase hg.w a := Over.OverMorphism.ext ha
  have eb : b₀ = toBase hg.w b := Over.OverMorphism.ext hb
  subst ea eb
  rw [← mul]
  rfl

end GlobalTheory.UMin.FibExist
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Ex.OneGen
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin.ModelNZ

theorem exists_sec_nz : ∀ (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [CharZero W], IsAdicComplete (IsLocalRing.maximalIdeal W) W → ∀ (D : DegData W (IsLocalRing.maximalIdeal W)) (A : PolAV (Sp (FractionRing W))) (G : Over (Sp W)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (IsLocalRing.maximalIdeal W) D A G), ∃ σ : SecAt G U.LG.L (𝟙 (Sp W)), NZ G U.LG.L (𝟙 (Sp W)) σ := by
  intro R _ _ _ _ _ D A G _ _ hsemi U
  haveI : GeometricallyConnected G.hom := hsemi.geomConnected
  have hLaws := GlobalTheory.abelianSchemeLaws_all

  obtain ⟨th, hth, -⟩ := GlobalTheory.PsiRing.exists_basis_fibNZ hLaws.2.secTwist R D.toPre
  obtain ⟨f₀, hf₀⟩ : ∃ f₀ : D.toPre.SecB 1 0, ∀ (Z : Scheme.{0}) (r : Z ⟶ _) (z : Z) (J), Good D.toPre.P.L z J →
      sval th r z J = sval f₀ (r ≫ (snd (𝟙_ _) D.toPre.P.A).left) z J := by
    refine GlobalTheory.PsiExpansion.exists_sec_of_retract D.toPre.P.isLB _ _
      (GlobalTheory.PsiExpansion.snd_lift_unit D.toPre.P.A) (fun i => ?_) th
    fin_cases i
    · exact congrArg CommaMorphism.left (lift_snd (toUnit D.toPre.P.A) (𝟙 D.toPre.P.A))
    · refine congrArg CommaMorphism.left (show lift (toUnit D.toPre.P.A) (𝟙 D.toPre.P.A) ≫
        padd D.toPre.P.A (snd _ _) (toUnit _ ≫ D.toPre.c 0) = padd D.toPre.P.A (𝟙 _) (toUnit _ ≫ D.toPre.c 0) from ?_)
      simp only [padd, ← Category.assoc, comp_lift, lift_snd, comp_toUnit]
    · refine congrArg CommaMorphism.left
        (show lift (toUnit D.toPre.P.A) (𝟙 D.toPre.P.A) ≫ toUnit _ ≫ D.toPre.c 0 = toUnit _ ≫ D.toPre.c 0 from ?_)
      rw [← Category.assoc, comp_toUnit]
    · refine congrArg CommaMorphism.left
        (show lift (toUnit D.toPre.P.A) (𝟙 D.toPre.P.A) ≫ toUnit _ ≫ η[D.toPre.P.A] = toUnit _ ≫ η[D.toPre.P.A] from ?_)
      rw [← Category.assoc, comp_toUnit]
  obtain ⟨z₀, hz₀, hn₀⟩ := hth (IsLocalRing.closedPoint R)
  have hx : D.toPre.P.A.hom ((snd (𝟙_ (Over (Sp R))) D.toPre.P.A).left z₀) = IsLocalRing.closedPoint R :=
    (congrArg (fun q => q z₀) (Over.w (snd (𝟙_ (Over (Sp R))) D.toPre.P.A))).trans hz₀
  obtain ⟨J, hJ⟩ := GlobalTheory.ConstFam.exists_good' D.toPre.P.isLB z₀
  have hu : IsUnit (sval th (𝟙 _) z₀ J) := (isUnit_sval_iff th (𝟙 _) z₀ hJ).2 hn₀
  rw [hf₀ _ _ z₀ J hJ, Category.id_comp] at hu
  have hxn := (isUnit_sval_iff f₀ _ z₀ hJ).1 hu

  obtain ⟨σ, fam, hfam0, hσ, hmem, -⟩ := GlobalTheory.ThetaUnit.exists_theta hLaws.1.globalFns hLaws.1.secBaseChange
    le_rfl U f₀ ⟨_, hx, hxn⟩
  obtain ⟨g, hg, hn⟩ : ∃ g, G.hom g = IsLocalRing.closedPoint R ∧ g ∈ nonzeroLocus σ :=
    GlobalTheory.ThetaUnit.exists_mem_nonzeroLocus le_rfl U.toUnifPre (hσ 0)
      (by rw [hfam0]; exact ⟨_, hx, hxn⟩) hmem
  refine ⟨GlobalTheory.TorRef.upSec G σ, GlobalTheory.Ex.OnModel.toBase G g, ?_, ?_⟩
  · have a : GlobalTheory.Ex.OnModel.toBase G ≫ (fst (Over.mk (𝟙 (Sp R))) G).left = G.hom := by
      rw [GlobalTheory.Ex.OnModel.toBase, ← Over.comp_left, lift_fst]; rfl
    rw [← Scheme.Hom.comp_apply, a]
    exact hg
  · refine GlobalTheory.Ex.OnModel.mem_nonzeroLocus_pullTo σ _ _ ?_
    rw [← Scheme.Hom.comp_apply, GlobalTheory.Ex.OnModel.toBase_snd]
    exact hn

end GlobalTheory.UMin.ModelNZ
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.UMin

theorem isGenSec_real_pull : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (K : Type) [Field K] (i : S.R →+* K), IsGenSec ρ.P.A ρ.P.L _ (SecAt.pull ρ.P.A ρ.P.L (x := 𝟙 (Sp S.R)) ρ.th₁ i) := by
  intro o Ω _ _ _ _ S ρ K _ i
  haveI : IsAffine (Over.mk (𝟙 (Sp S.R))).left := inferInstanceAs (IsAffine (Sp S.R))
  haveI : IsAffine (Over.mk (spMap i ≫ 𝟙 (Sp S.R))).left := inferInstanceAs (IsAffine (Sp K))
  exact GlobalTheory.EmbPull.isGenSec_pullS ρ.P GlobalTheory.abelianSchemeLaws_all.2.secBaseChangeAny _ (GlobalTheory.ThetaLevel.isGenSec_real ρ)

end GlobalTheory.UMin
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SiegCrd

theorem eq_of_generic_pCrd : ∀ (o : Type) [CommRing o] (n : ℕ) (X : Scheme.{0}) [IsIntegral X] [IsReduced X] (s : X ⟶ Sp o) (h h' : X ⟶ PSpace o n) (K : Type) [Field K] (x : Sp K ⟶ X) (c : Fin (n + 1) → K), h ≫ PSpace.str o n = s → h' ≫ PSpace.str o n = s → Set.range x = {genericPoint X} → PCrd (x ≫ h) c → PCrd (x ≫ h') c → h = h' := by
  intro o _ n X _ _ s h h' K _ x c hs hs' hx hc hc'
  have : IsSeparated (PSpace.str o n) := by
    have := isProper_str o n
    infer_instance
  have hd : IsDominant x := by
    refine ⟨?_⟩
    change Dense (Set.range x.base)
    have e : Set.range x.base = {genericPoint X} := hx
    rw [e, dense_iff_closure_eq]
    exact genericPoint_closure X
  have he : x ≫ h = x ≫ h' :=
    CrdUniq.eq_of_pCrd (by rw [Category.assoc, Category.assoc, hs, hs']) hc hc'
  exact ext_of_isDominant_of_isSeparated (PSpace.str o n) (hs.trans hs'.symm) x he

end GlobalTheory.SiegCrd
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.homogeneousCoords_in_standardChart_ratio : ∀ (o K : Type) [CommRing o] [Field K] (n : ℕ) (x : Sp K ⟶ PSpace o n) (v : Fin (n + 1) → K) (a : Fin (n + 1)), PCrd x v → ⊤ ≤ x ⁻¹ᵁ ProjSpace.chart o n a → v a ≠ 0 ∧ ∀ b, valR x (ProjSpace.chart o n a) (ProjSpace.ratio o n a b) = v b / v a := by
  first | exact @GlobalTheory.UMin.CrdChart.pCrd_chart | exact GlobalTheory.UMin.CrdChart.pCrd_chart | (intros; apply GlobalTheory.UMin.CrdChart.pCrd_chart <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open GlobalTheory.ProjSpace GlobalTheory.UMin.ThBdl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin.ChartDiv

theorem chart_ratio_mem_O : ∀ (k Ω : Type) [CommRing k] [Field Ω] [Algebra k Ω] (M : RatModel k Ω) (n : ℕ) (c : Fin (n + 1) → Ω) (h : M.Z ⟶ PSpace k n) (a : Fin (n + 1)) (z : M.Z), PCrd (M.pt ≫ h) c → z ∈ h ⁻¹ᵁ chart k n a → c a ≠ 0 ∧ ∀ z' ∈ h ⁻¹ᵁ chart k n a, ∀ b, c b / c a ∈ M.O z' := by
  intro k Ω _ _ _ M n c h a z hc hz
  have hx : ⊤ ≤ (M.pt ≫ h) ⁻¹ᵁ chart k n a := M.top_le_preimage_pt (U := h ⁻¹ᵁ chart k n a) ⟨z, hz⟩
  obtain ⟨ha, hb⟩ := GlobalTheory.UMin.CrdChart.pCrd_chart k Ω n (M.pt ≫ h) c a hc hx
  refine ⟨ha, fun z' hz' b => ?_⟩
  rw [← hb b, Points.valR_comp, ← Points.valF_eq_valR]
  exact RatModel.valF_mem_O hz' _

end GlobalTheory.UMin.ChartDiv
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.principallyPolarised_genericFibre_uniformised_trait : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ (χ : Sp V ⟶ S) (t' : SAB H (Sp V)), Nonempty (SABMap t' t χ) → Nonempty (PELUnif (IsLocalRing.maximalIdeal V) t') → ∃ g : ℕ, ∀ (R : Type) [CommRing R] (e : FractionRing V →+* R), PolFib t.G t.PP.L g (spMap e ≫ jK V ≫ χ) := by
  first | exact @GlobalTheory.UMin.UnifPolFib.polFib_of_unif | exact GlobalTheory.UMin.UnifPolFib.polFib_of_unif | (intros; apply GlobalTheory.UMin.UnifPolFib.polFib_of_unif <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_local_thetaConstants_localisation : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (g m : ℕ) (R : Type) [CommRing R] [IsNoetherianRing R] (x : Sp R ⟶ S) (θ : SecAt G L x) (R₁ : Type) [CommRing R₁] [Algebra R R₁] [IsNoetherianRing R₁] (N : ℕ) (q : Fin N → (Over.mk (spMap (algebraMap R R₁) ≫ x) ⟶ G)), Odd m → IsUnit (m : R) → PolFib G L g x → (∀ a, q a ^ (m ^ 2) = 1) → ∀ p : Ideal R₁, p.IsPrime → ∃ f ∉ p, ∃ c : Fin N → Localization.Away f, ∀ (K : Type) [Field K] (j : Localization.Away f →+* K) (a : Fin N) (pt : Over.mk (spMap ((j.comp (algebraMap R₁ (Localization.Away f))).comp (algebraMap R R₁)) ≫ x) ⟶ G), pt.left = spMap (j.comp (algebraMap R₁ (Localization.Away f))) ≫ (q a).left → ThG G L ρ m (SecAt.pull G L θ ((j.comp (algebraMap R₁ (Localization.Away f))).comp (algebraMap R R₁))) pt (fn (j (c a))) := by
  first | exact @GlobalTheory.UMin.ThLocal.exists_local | exact GlobalTheory.UMin.ThLocal.exists_local | (intros; apply GlobalTheory.UMin.ThLocal.exists_local <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin

theorem exists_thList : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (g m N : ℕ) (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) (θ : SecAt G L x), Odd m → (m : K) ≠ 0 → N = m ^ (4 * g) → PolFib G L g x → ∃ (pt : Fin N → (Over.mk x ⟶ G)) (c : Fin N → K), ThList G L ρ m x θ pt c := by
  intro S G _ _ L ρ hL hρ g m N K _ _ x θ hm hmK hN hP
  subst hN
  obtain ⟨pt, hinj, hpt, hall⟩ := GlobalTheory.T.exists_injective_list_m_sq_torsion_polarisedFibre S G L g m K x hmK hP
  have hex : ∀ a, ∃ c : K, ThG G L ρ m θ (pt a) (GlobalTheory.ZH.fn c) := by
    intro a
    exact GlobalTheory.T.exists_thetaConstant_m_sq_torsion_algClosed_fibre S G L ρ hL hρ g m K x θ (pt a) hm hmK hP (hpt a)
  choose c hc using hex
  exact ⟨pt, c, hinj, hc, hall⟩

end GlobalTheory.UMin
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.thetaSymmetricFunctions_div_pow_factorial_isUnit : ∀ (k Ω : Type) [CommRing k] [Field Ω] [Algebra k Ω] (A : Subalgebra k Ω) [IsLocalRing A] (N : ℕ) (c : Fin N → Ω) (a j : Fin N), c a ≠ 0 → (∀ b, c b / c a ∈ A) → symTup c j ≠ 0 → (∀ b, symTup c b / symTup c j ∈ A) → symTup c j / c a ^ N.factorial ≠ 0 ∧ symTup c j / c a ^ N.factorial ∈ A ∧ (symTup c j / c a ^ N.factorial)⁻¹ ∈ A := by
  first | exact @GlobalTheory.UMin.symTup_div_pow_isUnit_of_dvd | exact GlobalTheory.UMin.symTup_div_pow_isUnit_of_dvd | (intros; apply GlobalTheory.UMin.symTup_div_pow_isUnit_of_dvd <;> assumption)
end
