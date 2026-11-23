module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle082
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle104
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle024
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsTateIsoOfPeriods
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle072
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsOfDouble
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle112
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.Bundle003
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsIntegralOfIsAbelianSchemeField
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle087
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle083
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle101
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle113
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ObjMapIdCompCancel
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.ExtremalEpi
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001

@[expose] public section

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

open PeriodPoint

theorem exists_point_of_period : ThetaUnifAV → Out.Laws → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M
    : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → (∀ (g : ℕ) (Λ : Submodule ℤ (Fin
    g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ) (Ef
    : LinearMap.BilinForm ℤ Λ), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g →
    ℂ)) = ⊤ → Hm.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) → (∀ a b : Λ, (Ef
    a b : ℝ) = (hermForm Hm a b).im) → Function.Bijective Ef → ∃ (P : Out.PolAV (Sp ℂ)) (u
    : HolUnif P.A P.L g) (χ
    : u.Λ → ℂ), P.g = g ∧ u.Λ = Λ ∧ u.IsAH Hm χ ∧ (∀ v, IsTangent v → ∃! w, u.IsDiff w v) ∧ (∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v)) → (∀ (P
    P' : Out.PolAV (Sp ℂ)) (g : ℕ) (u : HolUnif P.A P.L g) (u' : HolUnif P'.A P'.L g) (F : (Fin g →
    ℂ) →ₗ[ℂ] (Fin g →
    ℂ)), P.g = g → P'.g = g → (∀ z ∈ u.Λ, F z ∈ u'.Λ) → ∃ f : P.A ⟶ P'.A, IsMonHom f ∧ ∀ z, u'.ex (F
    z) = u.ex z ≫ f) → (∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (P : Out.PolAV (Sp
    k)) (a a' : P.A ⟶ P.A), IsMonHom a → IsMonHom a' → (∀ (n : ℕ) (x y : 𝟙_ (Over (Sp k)) ⟶ P.A) (c
    : Γ((𝟙_ (Over (Sp k))).left, ⊤)ˣ), 0 < n → x ^ n = 1 → y ^ n = 1 → Out.WeilIs P.A P.L n (x ≫
    a) y c → Out.WeilIs P.A P.L n x (y ≫ a') c) → LBIso (cubeLB P.A ![fst P.A P.A ≫ a, snd P.A P.A]
    P.L) (cubeLB P.A ![fst P.A P.A, snd P.A P.A ≫ a'] P.L)) → (∀ (E : Type) [Field E] [NumberField
    E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (B : Over S) [GrpObj B] [IsCommMonObj B] (act
    : OAct (𝓞 E) B) (M : LB B.left), IsAbelianScheme B → M.IsLB → (∃ t : LB.Gen (Theta B
    M), t.IsGen) → (∀ a, LBIso (cubeLB B ![fst B B ≫ act.act a, snd B B] M) (cubeLB B ![fst B B, snd
    B B ≫ act.act (H.bar a)] M)) → ∃ (PP : RigLB B) (_
    : CubicalStr B PP), PP.IsSymmetric ∧ LBIso PP.L (cubeLB B ![𝟙 B, act.act H.w0]
    M) ∧ LBIso (abelian₂ B PP.L) (abelian₂ B M) ∧ LBIso PP.L (cubeLB B ![𝟙 B, act.act H.w0]
    PP.L) ∧ ∀ a, LBIso (cubeLB B ![fst B B ≫ act.act a, snd B B] PP.L) (cubeLB B ![fst B B, snd B B
    ≫ act.act (H.bar a)] PP.L)) → (∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (P
    : Out.PolAV (Sp k)) (n : ℕ) (B : Over (Sp k)) [GrpObj B] (ψ : P.A ⟶ B) (M
    : LB B.left), 0 < n → IsAbelianScheme B → M.IsLB → IsMonHom ψ → IsFinite ψ.left → Etale ψ.left → Surjective ψ.left → Nat.card {x
    : 𝟙_ (Over (Sp k)) ⟶ P.A // x ≫ ψ = 1} = n ^ P.g → LBIso (abelian₂ P.A (lbPow P.L n)) (abelian₂
    P.A (M.pull ψ.left)) → Out.KTriv B M) → (∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A B
    : Over S) [GrpObj A] [GrpObj B] (ψ : A ⟶ B) (M : LB B.left) (n
    : ℕ), 0 < n → IsAbelianScheme A → IsAbelianScheme B → M.IsLB → IsFinite ψ.left → (Out.RelAmple B
    M → Out.RelAmple A (M.pull ψ.left)) ∧ (Out.RelAmple B (lbPow M n) ↔ Out.RelAmple B M) ∧ (Flat
    ψ.left → Surjective ψ.left → Out.RelAmple A (M.pull ψ.left) → Out.RelAmple B
    M) ∧ ∀ M' : LB B.left, M'.IsLB → LBIso M M' → Out.RelAmple B M → Out.RelAmple B M') → (∀ (E
    : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo
    : Moduli D l) (B : Type) [CommRing B] (b : Base l B) (j : KA l →+* B) (S : Scheme.{0}) (s
    : S ⟶ Sp B) (o : Obj D l b s), IsReduced S → j (baseKA l).ρ = b.ρ → j (baseKA
    l).ζ = b.ζ → ∃! f : S ⟶ Xo.X, f ≫ Xo.s = s ≫ spMap j ∧ Nonempty (ObjMap o Xo.univ f)) → ∀ (E
    : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo
    : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)), 1 ≤ D.p + D.q → σ (baseKA
    l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → ∀ (D' : Datum H) (t : D.La →ₗ[𝓞 E] D'.La) (P
    : D'.La →+ (Fin g → ℂ)), (D'.p = D.p ∧ D'.q = D.q ∧ ∃ (f : ℕ → D.La →ₗ[𝓞 E] D'.La) (ν
    : ℕ → ℤ), (∀ n m : ℕ, 0 < n → 0 < m → ∀ a, ∃ e, f (n *
    m) a = f n a + n • e) ∧ (∀ n : ℕ, 0 < n → (∀ a, (∃ e, f n a = n • e) ↔ ∃ e, a = n • e) ∧ ∀ a', ∃ a e, a' = f n a + n • e) ∧ (∀ n : ℕ, 0 < n → ∀ a a', (n
    : ℤ) ∣ D'.EF (f n a) (f n a') - ν n * D.EF a a') ∧ σ (baseKA l).ζ = Complex.exp (-(2 * Real.pi *
    Complex.I) * (ν l.A : ℂ) / l.A) ∧ t = f l.M') → IsPeriod D' ty P → ∃ (y : Sp ℂ ⟶ Xo.X) (e : (Fin
    g → ℂ) → (Over.mk y ⟶ Xo.univ.t.G)), (y ≫ Xo.s = spMap σ ∧ IsPeriod D' ty P ∧ ((∀ z w, e (z +
    w) = e z * e w) ∧ Function.Surjective e ∧ IsHolTo Set.univ (fun z => (e z).left) ∧
    (∀ w, ∃! v : epsPt y ⟶ Xo.univ.t.G, IsDerivAt0 (fun z => (e z).left) w v.left) ∧
    (∀ v : epsPt y ⟶ Xo.univ.t.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e
    0).left → ∃! w, IsDerivAt0 (fun z => (e z).left) w v.left)) ∧ (∀ z, e z = 1 ↔ z ∈ (P).range) ∧
    (∀ (a : 𝓞 E) z, e (fun k => ty k (a : E) * z k) = e z ≫ Xo.univ.t.act.act a) ∧ (∀ (k : ℕ) (a a₂
    : D'.La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a a₂ : ℂ)
    / k) → Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L k (e ((k : ℂ)⁻¹ • P a)) (e ((k : ℂ)⁻¹ • P
    a₂)) (unitOn c)) ∧ (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞
    E) D.La), toUnit _ ≫ Xo.univ.eta a = e ((l.M : ℂ)⁻¹ • P (t a))) ∧
    ∀ a, toUnit _ ≫ Xo.univ.etaA a = e ((l.A : ℂ)⁻¹ • P (t a))) := by
  intro _ laws cube tor hom adjW prim princ amp rep E _ _ _ H D l Xo σ g ty hpq hσ hty D' t P
    ⟨hp, hq, f, ν, htow, hiso, hsim, hζ, ht⟩ hP
  obtain ⟨T, L, u, hA, hdim, hamp, hK, ht₁, ht₂, hker, hact, hW⟩ :=
    exists_triple laws cube tor hom adjW prim princ amp D' ty P hP
  let Q : Out.PolAV (Sp ℂ) :=
    { A := T.G, isAb := hA, g := g, smoothDim := hdim, L := T.PP.L, isLB := T.PP.isLB,
      rigid := ⟨T.PP.rig, T.PP.rigGen⟩, sym := CechPic.sym_of_isSymmetric T.PP T.sym, ample := hamp, ktriv := hK }
  obtain ⟨v, hv, heig⟩ := exists_lieBasis_of_holUnif T.G L g u hA.smooth ht₁ ht₂
  have hmul : ∀ (n : ℕ) a, 0 < n → u.ex ((n : ℂ)⁻¹ • P (n • a)) = 1 := fun n a hn => by
    rw [hker, map_nsmul, ← Nat.cast_smul_eq_nsmul ℂ, inv_smul_smul₀ (Nat.cast_ne_zero.2 hn.ne')]
    exact ⟨a, rfl⟩
  have hadd : ∀ (n : ℕ) a b, u.ex ((n : ℂ)⁻¹ • P (f n (a + b))) =
      u.ex ((n : ℂ)⁻¹ • P (f n a)) * u.ex ((n : ℂ)⁻¹ • P (f n b)) := fun n a b => by
    rw [map_add (f := _), map_add (f := _), smul_add, u.ex_add]
  have hM : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  obtain ⟨κ, hκ₁, hκ₂, hκ₃⟩ := exists_halfLevel (D := D) l (fun a => u.ex ((l.M : ℂ)⁻¹ • P (f l.M a))) (hadd l.M)
    fun b => by rw [map_nsmul, hmul _ _ hM]
  let b : Base l ℂ :=
    { unit := fun n hn => IsUnit.mk0 _ (Nat.cast_ne_zero.2 hn.ne')
      ρ := σ (baseKA l).ρ
      ρ_sq := by rw [← map_pow, (baseKA l).ρ_sq, map_neg, map_natCast]
      ζ := σ (baseKA l).ζ
      ζ_prim := (baseKA l).ζ_prim.map_of_injective σ.injective }
  let o : Obj D l b (𝟙 (Sp ℂ)) :=
    { t := T, proper := hA.proper, ample := hamp, ktriv := hK
      eta := κ, eta_add := hκ₁, eta_ker := hκ₂
      etaA := fun a => u.ex ((l.A : ℂ)⁻¹ • P (f l.A a))
      etaA_add := hadd l.A
      etaA_ker := fun a => by rw [map_nsmul, hmul _ _ l.A_pos]
      geom := fun k _ _ x β hx => by
        obtain rfl : x = spMap β := (Category.comp_id x).symm.trans hx
        refine ⟨?_, ?_⟩
        · rw [show b.ρ = H.rt0 from hσ]
          exact detCond_of_eigenbasis lieMult_of_eigenbasis D T ty hty v hv
            (fun i a => heig _ _ (T.act.hom a) (hact a) i) β
        · obtain ⟨I, hI₁, hI₂⟩ := exists_tateIso_of_periods laws E H D D' g ty P Q T.act u.ex f ν hpq hP u.ex_add
            u.ex_onto hker hact hW htow hiso hsim k β
          exact ⟨I, (hI₁ _).trans (congrArg β hζ.symm), fun a => (hI₂ _ a).symm,
            fun a ha => by rw [hκ₃ a ha]; exact (hI₂ _ a).symm⟩ }
  obtain ⟨y, ⟨hy, ⟨m⟩⟩, -⟩ := rep E H D l Xo ℂ b σ (Sp ℂ) (𝟙 _) o inferInstance rfl rfl
  obtain ⟨e, he, hhol, he₁, he₂, he₃⟩ := exists_fibre_unif T Xo.univ.t y m.toSABMap u ht₁ ht₂
  have hlev : ∀ n : ℕ, 0 < n → n ∣ l.M' → ∀ a, u.ex ((n : ℂ)⁻¹ • P (t a)) = u.ex ((n : ℂ)⁻¹ • P (f n a)) := by
    rintro n hn ⟨r, hr⟩ a
    have hr0 : 0 < r := Nat.pos_of_mul_pos_left ((Nat.lcm_pos hM l.A_pos).trans_eq hr)
    obtain ⟨c, hc⟩ := htow n r hn hr0 a
    rw [ht, hr, hc, map_add (f := _), smul_add, u.ex_add, hmul _ _ hn, _root_.mul_one]
  refine ⟨y, e, hy.trans (Category.id_comp _), hP, hhol, fun z => (he₁ z).trans (hker z),
    fun a z => he₂ a z _ (hact a z), fun k a a₂ c hk hc => he₃ k _ _ _ (hW k a a₂ c hk hc),
    fun a ha => Over.OverMorphism.ext ?_, fun a => Over.OverMorphism.ext ?_⟩
  · rw [he, hlev _ hM (Nat.dvd_lcm_left _ _), ← hκ₃ a ha]
    exact (m.eta a).symm
  · rw [he, hlev _ l.A_pos (Nat.dvd_lcm_right _ _)]
    exact (m.etaA a).symm

end GlobalTheory
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV

namespace GlobalTheory.PrimePowerTorsion

theorem dense_torsion (hA : Out.AmpleSt) (hK : Out.KerPowSt) (hI : Out.IrredSt) (K : Type) [Field K] [IsAlgClosed K]
    (P : Out.PolAV (Sp K)) (l : ℕ) (hl : 2 ≤ l) (hlK : (l : K) ≠ 0) :
    Dense (⋃ x ∈ {x : 𝟙_ (Over (Sp K)) ⟶ P.A | ∃ j : ℕ, x ^ l ^ j = 1}, Set.range x.left) := by
  have := P.isAb.comm
  refine dense_iff_inter_open.2 fun U hU ⟨x, hx⟩ => ?_
  obtain ⟨a, -, s, hs, hle, -⟩ := (isAmpleLB_of_relAmple_of_isAffine P.A P.isLB P.ample).exists_affine_le
    (x := x) (U := ⟨U, hU⟩) hx
  have gen : ∀ N : ℕ, 4 ≤ N → ∀ y : P.A.left, ∃ t : (lbPow P.L N).Sec, y ∈ Out.nonzeroLocus t := fun N hN y => by
    obtain ⟨m, t, ht, -⟩ := veryAmple_lbPow hA K P N hN
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (ht.ge (Set.mem_univ y))
    exact ⟨t i, hi⟩
  obtain ⟨m, hm, ham⟩ : ∃ m : ℕ, 4 ≤ m ∧ a + m = l ^ (a + 4) := by
    have := Nat.lt_pow_self (n := a + 4) (show 1 < l by omega)
    exact ⟨l ^ (a + 4) - a, by omega, by omega⟩
  obtain ⟨t, ht⟩ := gen m hm x
  let p : (Out.baseOver (Sp K)).left := IsLocalRing.closedPoint K
  obtain ⟨t', ht'⟩ := gen (a + m) (by omega) ((1 : Out.baseOver (Sp K) ⟶ P.A).left p)
  have e := nonzeroLocus_secMul s t
  obtain ⟨b, hb, q, hq⟩ := TorsionDense.exists_mem_nonzeroLocus P hI hK (a + m) (by omega)
    (by rw [ham, Nat.cast_pow]; exact pow_ne_zero _ hlK)
    {x | ∃ j : ℕ, x ^ l ^ j = 1} (fun w hw b ⟨j, hb⟩ => ⟨a + 4 + j, by
      rw [mul_pow, pow_add, pow_mul w, ← ham, hw, one_pow, mul_comm _ (l ^ j), pow_mul, hb, one_pow,
        _root_.one_mul]⟩)
    (secMul s t) t' x (e.ge ⟨hs, ht⟩) 1 ⟨0, one_pow _⟩ p ht'
  exact ⟨b.left q, hle (e.le hq).1, Set.mem_iUnion₂.2 ⟨b, hb, q, rfl⟩⟩

theorem dense_torsion_and_eq_one :
    Out.Laws → Out.Laws2 → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (l : ℕ), l.Prime → (l : K) ≠ 0 → Dense (⋃ x ∈ {x : 𝟙_ (Over (Sp K)) ⟶ P.A | ∃ j : ℕ, x ^ l ^ j = 1}, Set.range x.left) ∧ ∀ f : P.A ⟶ P.A, (∀ (j : ℕ) (x : 𝟙_ (Over (Sp K)) ⟶ P.A), x ^ l ^ j = 1 → x ≫ f = 1) → f = 1 := by
  intro h1 _ K _ _ P l hl hlK
  have hD := dense_torsion h1.ample h1.kerPow h1.irred K P l hl.two_le hlK
  refine ⟨hD, fun f hf => Over.OverMorphism.ext ?_⟩
  have := polAV_isIntegral_of_isAlgClosed K P
  have := P.isAb.proper
  let g : P.A ⟶ P.A := 1
  suffices IsDominant (equalizer.ι f.left g.left) from
    ext_of_isDominant_of_isSeparated P.A.hom ((Over.w f).trans (Over.w g).symm) (equalizer.ι f.left g.left)
      (equalizer.condition _ _)
  refine ⟨Dense.mono (fun y hy => ?_) hD⟩
  obtain ⟨x, ⟨j, hx⟩, q, rfl⟩ := Set.mem_iUnion₂.1 hy
  have hxy : x.left ≫ f.left = x.left ≫ g.left :=
    congrArg CommaMorphism.left ((hf j x hx).trans (MonObj.comp_one x).symm)
  refine ⟨equalizer.lift x.left hxy q, ?_⟩
  rw [← Scheme.Hom.comp_apply, equalizer.lift_ι]

end GlobalTheory.PrimePowerTorsion
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ObjDescent

theorem isGrpPullback_id {S S₂ : Scheme.{0}} {G G' : Over S} {G₂ : Over S₂} [GrpObj G] [GrpObj G'] [GrpObj G₂]
    {q : S₂ ⟶ S} [Flat q] [Surjective q] {a : G₂.left ⟶ G.left} {c : G₂.left ⟶ G'.left}
    (h : IsGrpPullback G₂ G q a) (h' : IsGrpPullback G₂ G' q c) (φ : G.left ⟶ G'.left) [IsIso φ] (e : a ≫ φ = c)
    (w : φ ≫ G'.hom = G.hom ≫ 𝟙 S) : IsGrpPullback G G' (𝟙 S) φ := by
  refine ⟨IsPullback.of_horiz_isIso ⟨w⟩, fun T x y x₀ y₀ hx hy => ?_⟩
  let r := pullback.fst T.hom q
  have : Epi r := Flat.epi_of_flat_of_surjective _
  let T' : Over S₂ := Over.mk (pullback.snd T.hom q)
  have up : ∀ z : T ⟶ G, ∃ z' : T' ⟶ G₂, r ≫ z.left = z'.left ≫ a := fun z =>
    ⟨Over.homMk (h.1.lift (r ≫ z.left) (pullback.snd T.hom q)
      (by rw [Category.assoc, Over.w z]; exact pullback.condition)) (h.1.lift_snd _ _ _),
      (h.1.lift_fst _ _ _).symm⟩
  obtain ⟨x', hx'⟩ := up x
  obtain ⟨y', hy'⟩ := up y
  let R : Over.mk (T'.hom ≫ q) ⟶ T := Over.homMk r pullback.condition
  let R' : Over.mk (T'.hom ≫ q) ⟶ Over.mk (T.hom ≫ 𝟙 S) :=
    Over.homMk r ((congrArg (r ≫ ·) (Category.comp_id T.hom)).trans pullback.condition)
  have e₁ := h.2 T' x' y' (R ≫ x) (R ≫ y) hx' hy'
  have e₂ := h'.2 T' x' y' (R' ≫ x₀) (R' ≫ y₀)
    (by show r ≫ x₀.left = _; rw [hx, ← Category.assoc, hx', Category.assoc, e])
    (by show r ≫ y₀.left = _; rw [hy, ← Category.assoc, hy', Category.assoc, e])
  rw [← MonObj.comp_mul] at e₁ e₂
  rw [← cancel_epi r, ← Category.assoc]
  refine e₂.trans ?_
  rw [← e, ← Category.assoc]
  exact congrArg (· ≫ φ) e₁.symm

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B''] {b : Base l B} {b' : Base l B'} {b'' : Base l B''}
  {S S₂ : Scheme.{0}} {s : S ⟶ Sp B} {s' : S ⟶ Sp B'} {s'' : S₂ ⟶ Sp B''}
  {u : Obj D l b s} {ob : Obj D l b' s'} {ob₂ : Obj D l b'' s''} {q : S₂ ⟶ S}

theorem exists_congr {q' : S₂ ⟶ S} (e : q = q') (m : ObjMap ob₂ ob q) :
    ∃ m' : ObjMap ob₂ ob q', m'.toSABMap.φ = m.toSABMap.φ := by
  subst e
  exact ⟨m, rfl⟩

theorem comp_eq_of_comp_eq (hL : Out.Laws) (m : ObjMap ob₂ ob q) (n : ObjMap ob₂ u q) {Z : Scheme.{0}}
    (g₁ g₂ : Z ⟶ ob₂.t.G.left) (h : g₁ ≫ m.toSABMap.φ = g₂ ≫ m.toSABMap.φ) :
    g₁ ≫ n.toSABMap.φ = g₂ ≫ n.toSABMap.φ := by
  have hp : (g₁ ≫ ob₂.t.G.hom) ≫ q = (g₂ ≫ ob₂.t.G.hom) ≫ q := by
    rw [Category.assoc, Category.assoc, ← m.cart.1.w, ← Category.assoc, h, Category.assoc]
  obtain ⟨o, ⟨m₁⟩⟩ := obj_pull E H D l B'' B'' b'' b'' (RingHom.id _) S₂ Z s'' ((g₁ ≫ ob₂.t.G.hom) ≫ s'')
    (g₁ ≫ ob₂.t.G.hom) rfl rfl ((Category.comp_id _).symm.trans (congrArg _ (Spec.map_id _).symm)) ob₂
  obtain ⟨k, hk⟩ := ObjComp.objMap_comp m m₁
  obtain ⟨k', hk'⟩ := exists_congr hp k
  obtain ⟨m₂, hm₂⟩ := ObjComp.objMap_cancel m k'
  obtain ⟨n₁, hn₁⟩ := ObjComp.objMap_comp n m₁
  obtain ⟨n₁', hn₁'⟩ := exists_congr hp n₁
  obtain ⟨n₂, hn₂⟩ := ObjComp.objMap_comp n m₂
  have e := obj_rigid_of_pol hL obj_isAbelianScheme_dim_rigidified_sym E H D l _ _ _ _ _ _ _ _ u o _
    n₁'.toSABMap n₂.toSABMap fun a => ⟨_, n₁'.eta a, n₂.eta a⟩
  rw [hn₁', hn₁, hn₂] at e
  rw [hk', hk] at hm₂
  let σ := m₁.cart.1.lift g₁ (𝟙 Z) (Category.id_comp _).symm
  have h₁ : σ ≫ m₁.toSABMap.φ = g₁ := m₁.cart.1.lift_fst _ _ _
  have h₀ : σ ≫ o.t.G.hom = 𝟙 Z := m₁.cart.1.lift_snd _ _ _
  have h₂ : σ ≫ m₂.toSABMap.φ = g₂ := by
    apply m.cart.1.hom_ext
    · rw [Category.assoc]
      refine (congrArg (σ ≫ ·) hm₂.symm).trans ?_
      rw [← Category.assoc, h₁, h]
    · rw [Category.assoc, m₂.cart.1.w, ← Category.assoc, h₀, Category.id_comp]
  refine (congrArg (· ≫ n.toSABMap.φ) h₁).symm.trans (Eq.trans ?_ (congrArg (· ≫ n.toSABMap.φ) h₂))
  exact (Category.assoc _ _ _).trans ((congrArg (σ ≫ ·) e).trans (Category.assoc _ _ _).symm)

variable [Flat q] [Surjective q] [QuasiCompact q]

theorem effectiveEpi (m : ObjMap ob₂ ob q) : EffectiveEpi m.toSABMap.φ := by
  have : Flat m.toSABMap.φ := MorphismProperty.of_isPullback m.cart.1.flip inferInstance
  have : Surjective m.toSABMap.φ := MorphismProperty.of_isPullback m.cart.1.flip inferInstance
  have : QuasiCompact m.toSABMap.φ := MorphismProperty.of_isPullback m.cart.1.flip inferInstance
  infer_instance

theorem exists_fac (hL : Out.Laws) (m : ObjMap ob₂ ob q) (n : ObjMap ob₂ u q) :
    ∃ φ : ob.t.G.left ⟶ u.t.G.left, m.toSABMap.φ ≫ φ = n.toSABMap.φ :=
  have := effectiveEpi m
  ⟨EffectiveEpi.desc m.toSABMap.φ n.toSABMap.φ (comp_eq_of_comp_eq hL m n), EffectiveEpi.fac _ _ _⟩

theorem nonempty_objMap_id (hL : Out.Laws) (m : ObjMap ob₂ ob q) (n : ObjMap ob₂ u q) :
    Nonempty (ObjMap ob u (𝟙 S)) := by
  obtain ⟨φ, hφ⟩ := exists_fac hL m n
  obtain ⟨ψ, hψ⟩ := exists_fac hL n m
  have := effectiveEpi m
  have := effectiveEpi n
  have : Epi q := Flat.epi_of_flat_of_surjective _
  have : IsIso φ := ⟨ψ, by rw [← cancel_epi m.toSABMap.φ, ← Category.assoc, hφ, hψ, Category.comp_id],
    by rw [← cancel_epi n.toSABMap.φ, ← Category.assoc, hψ, hφ, Category.comp_id]⟩
  have w : φ ≫ u.t.G.hom = ob.t.G.hom ≫ 𝟙 S := by
    rw [← cancel_epi m.toSABMap.φ, ← Category.assoc, hφ, Category.comp_id, m.cart.1.w, n.cart.1.w]
  have gp : IsGrpPullback ob.t.G u.t.G (𝟙 S) φ := isGrpPullback_id m.cart n.cart φ hφ w
  have hact : ∀ a, (ob.t.act.act a).left ≫ φ = φ ≫ (u.t.act.act a).left := fun a => by
    rw [← cancel_epi m.toSABMap.φ, ← Category.assoc, ← m.act, Category.assoc, hφ, n.act, ← Category.assoc, hφ]
  have hiso : LBIso ob.t.PP.L (u.t.PP.L.pull φ) := by
    have h₁ := ob.t.PP.isLB
    have h₂ := pull_isLB u.t.PP.isLB φ
    have hN := LB.isLB_div h₂ h₁
    have cN : CechPic.cls _ hN = CechPic.pull φ (CechPic.cls _ u.t.PP.isLB) - CechPic.cls _ h₁ :=
      CechPic.cls_div h₂ h₁ hN
    have cl : ∀ {t : SAB H S} (k : SABMap ob₂.t t q),
        CechPic.cls _ ob₂.t.PP.isLB = CechPic.pull k.φ (CechPic.cls _ t.PP.isLB) := fun {t} k => by
      obtain ⟨w, hw, -⟩ := k.lin
      exact (CechPic.cls_eq_iff _ (pull_isLB t.PP.isLB _)).2 ⟨w, hw⟩
    have z : ∀ t : SAB H S, CechPic.pull (eSec t.G) (CechPic.cls _ t.PP.isLB) = 0 := fun t =>
      (CechPic.cls_eq_zero_iff (pull_isLB t.PP.isLB _)).2 ⟨_, t.PP.rigGen⟩
    refine GlobalTheory.exists_gen_of_rigidified_of_flat_baseChange hL.globalFns S S₂ q ob.t.G _ (ObjDim.isAbelianScheme ob) hN inferInstance inferInstance
      inferInstance ((CechPic.cls_eq_zero_iff (pull_isLB hN _)).1 ?_)
      ((CechPic.cls_eq_zero_iff (pull_isLB hN _)).1 ?_)
    · have he : eSec ob.t.G ≫ φ = 𝟙 S ≫ eSec u.t.G := (cubeMapOf gp).e_comm
      rw [CechPic.cls_pull hN, cN, map_sub, ← CechPic.pull_comp, z, he, Category.id_comp, z, sub_zero]
    · rw [CechPic.cls_pull hN, cN, ← m.cart.1.isoPullback_inv_fst, CechPic.pull_comp, map_sub, ← CechPic.pull_comp,
        hφ, ← cl, ← cl, sub_self, map_zero]
  obtain ⟨k, hk⟩ := exists_sabMap_of_isProper_of_lbIso hL.globalFns E H S S u.t ob.t (𝟙 S) φ u.proper gp hiso hact
  have key : ∀ (σ₂ : S₂ ⟶ ob₂.t.G.left) (σ : S ⟶ ob.t.G.left) (τ : S ⟶ u.t.G.left),
      σ₂ ≫ m.toSABMap.φ = q ≫ σ → σ₂ ≫ n.toSABMap.φ = q ≫ τ → σ ≫ k.φ = 𝟙 S ≫ τ := fun σ₂ σ τ h₁ h₂ => by
    rw [← cancel_epi q, hk, Category.id_comp, ← Category.assoc, ← h₁, ← h₂, Category.assoc, hφ]
  exact ⟨⟨k, fun a => key _ _ _ (m.eta a) (n.eta a), fun a => key _ _ _ (m.etaA a) (n.etaA a)⟩⟩

end GlobalTheory.ObjDescent

namespace GlobalTheory

theorem nonempty_objMap_of_finite_etale_cover : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B B' B'' : Type) [CommRing B] [CommRing B'] [CommRing B''] (b : Base l B) (b' : Base l B') (b'' : Base l B'') (X S S₂ : Scheme.{0}) (s : X ⟶ Sp B) (s' : S ⟶ Sp B') (s'' : S₂ ⟶ Sp B'') (u : Obj D l b s) (ob : Obj D l b' s') (ob₂ : Obj D l b'' s'') (q : S₂ ⟶ S) (f : S ⟶ X), (IsReduced S ∨ IsLocallyNoetherian S) → IsFinite q → Etale q → Surjective q → Nonempty (ObjMap ob₂ ob q) → Nonempty (ObjMap ob₂ u (q ≫ f)) → Nonempty (ObjMap ob u f) := by
  intro hL _ E _ _ _ H D l B B' B'' _ _ _ b b' b'' X S S₂ s s' s'' u ob ob₂ q f _ _ _ _ ⟨m⟩ ⟨n⟩
  obtain ⟨u', ⟨p⟩⟩ := obj_pull E H D l B B b b (RingHom.id _) X S s (f ≫ s) f rfl rfl
    ((Category.comp_id _).symm.trans (congrArg _ (Spec.map_id _).symm)) u
  obtain ⟨n', -⟩ := ObjComp.objMap_cancel p n
  obtain ⟨k⟩ := ObjDescent.nonempty_objMap_id hL m n'
  obtain ⟨k', -⟩ := ObjComp.objMap_comp p k
  obtain ⟨k'', -⟩ := ObjDescent.exists_congr (Category.id_comp f) k'
  exact ⟨k''⟩

end GlobalTheory
end
