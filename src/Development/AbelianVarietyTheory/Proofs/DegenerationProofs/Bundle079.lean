module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle071
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle038
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle054
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PullPullAndSplitPull
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsBasisLatticeNear
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle056
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaSysFFMemFinitePerpProj
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle015
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ThetaGrpActsLinearly
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle075
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle011
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PolarizedAbelianEmbeddingBySections
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionValuesCoordsOperatorPermute
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.AppCompatGeneric
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle007
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle076
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle072
public import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle073
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

noncomputable section
namespace GlobalTheory.ZJ.DenseSplit

theorem exists_ringHom_kb (F : Type) [Field F] [Finite F] :
    ∃ (p : ℕ) (_ : Fact p.Prime), Nonempty (F →+* kb p) := by
  obtain ⟨p, hp⟩ := CharP.exists F
  have hpp : Fact p.Prime := ⟨CharP.char_is_prime F p⟩
  have : CharP (kb p) p := (CharP.charP_iff_prime_eq_zero hpp.out).mpr
    (GlobalTheory.natCast_self_residueField_padicAlgCl_eq_zero p)
  have := (kb_isAlgClosed_and_conj p).1
  letI : Algebra (ZMod p) F := ZMod.algebra F p
  letI : Algebra (ZMod p) (kb p) := ZMod.algebra _ p
  have : Module.Finite (ZMod p) F := Module.Finite.of_finite
  exact ⟨p, hpp, ⟨(IsAlgClosed.lift (R := ZMod p) (S := F) (M := kb p)).toRingHom⟩⟩

theorem isNoetherianRing_of_lft (R : Type) [CommRing R] (π : Sp R ⟶ Sp ℤ) [LocallyOfFiniteType π] :
    IsNoetherianRing R := by
  have : IsLocallyNoetherian (Sp R) := LocallyOfFiniteType.isLocallyNoetherian π
  exact isLocallyNoetherian_Spec.mp this

theorem exists_dense_splitOn : ∀ (C : Core) (L : C.Law), C.HasTests → C.HasCharts → letI := L.grp; letI := L.comm; ∀ z : C.Z, ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : IsNoetherianRing R) (t : Sp R ⟶ C.Z) (_ : IsImmersion t), t (⊥ : PrimeSpectrum R) = z ∧ ∃ (Ch : Charts ((Over.pullback t).obj C.GG).left) (d : ℕ) (c : Fin d → Ch.Cl) (Sg : Set (Sp R)), Dense Sg ∧ Ch.SplitOn c Sg ∧ ∀ x ∈ Sg, IsClosed ({t x} : Set C.Z) := by
  intro C L hT hC z
  letI := L.grp; letI := L.comm
  obtain ⟨R, _, _, t, _, htz, Ch, hCh⟩ := hC z
  have := C.lft
  have := C.flat
  obtain ⟨-, hfin, -, -, hdense⟩ := GlobalTheory.jacobson_closedPoints_tools_int (Sp R) (t ≫ C.π)
  refine ⟨R, inferInstance, inferInstance, isNoetherianRing_of_lft R (t ≫ C.π), t, inferInstance, htz, Ch, ?_⟩
  let κ := Σ d : Fin (C.g + 1), (Fin d → Ch.Cl)
  let Sg : κ → Set (Sp R) := fun k => {x | Charts.SplitOn (G := (Over.pullback t).obj C.GG) Ch k.2 {x} ∧
    IsClosed ({t x} : Set C.Z)}
  obtain ⟨k, hk⟩ := hdense κ Sg inferInstance (by
    intro x hx
    have := hfin x hx
    obtain ⟨p, hp, ⟨r⟩⟩ := exists_ringHom_kb ((Sp R).residueField x)
    let xb : Sp (kb p) ⟶ Sp R := Spec.map (CommRingCat.ofHom r) ≫ (Sp R).fromSpecResidueField x
    have hxb : ∀ s, xb s = x := fun s => by
      have : xb s ∈ Set.range ((Sp R).fromSpecResidueField x) := ⟨_, (Scheme.Hom.comp_apply _ _ _).symm⟩
      rwa [Scheme.range_fromSpecResidueField] at this
    have hrange : Set.range xb = {x} := by
      ext w
      exact ⟨fun ⟨s, hs⟩ => hs ▸ hxb s, fun hw => ⟨IsLocalRing.closedPoint (kb p), (hxb _).trans hw.symm⟩⟩
    obtain ⟨hlift, hcl⟩ := GlobalTheory.exists_integral_point_lifting_residue_point C.Z C.π C.U C.ne p
    obtain ⟨y, hy, hyU⟩ := hlift (xb ≫ t)
    obtain ⟨τ⟩ := hT p y hyU
    have e : (rPt p ≫ spMap τ.j) ≫ τ.y₀ = xb ≫ t := by rw [Category.assoc, τ.fac, hy]
    have g1 : IsGrpPullback ((Over.pullback (rPt p ≫ spMap τ.j)).obj τ.H) C.GG (xb ≫ t)
        (pullback.fst τ.H.hom (rPt p ≫ spMap τ.j) ≫ τ.f) :=
      ((isGrpPullback_pullback _ _).comp (L.test p y τ)).congr e rfl
    have g2 : IsGrpPullback ((Over.pullback t).obj C.GG) C.GG t (pullback.fst C.GG.hom t) :=
      isGrpPullback_pullback _ _
    have g3 : IsGrpPullback ((Over.pullback xb).obj ((Over.pullback t).obj C.GG)) ((Over.pullback t).obj C.GG) xb
        (pullback.fst ((Over.pullback t).obj C.GG).hom xb) :=
      isGrpPullback_pullback _ _
    let h : pullback τ.H.hom (rPt p ≫ spMap τ.j) ⟶ pullback C.GG.hom t :=
      pullback.lift (pullback.fst _ _ ≫ τ.f) (pullback.snd _ _ ≫ xb) (g1.1.w.trans (Category.assoc _ _ _).symm)
    have h1 : h ≫ pullback.fst _ _ = pullback.fst _ _ ≫ τ.f := pullback.lift_fst _ _ _
    have h2 : h ≫ pullback.snd _ _ = pullback.snd _ _ ≫ xb := pullback.lift_snd _ _ _
    have g4 : IsGrpPullback ((Over.pullback (rPt p ≫ spMap τ.j)).obj τ.H) ((Over.pullback t).obj C.GG) xb h :=
      g2.cancel (g1.congr rfl h1.symm) h2
    have ha : IsAffineHom h := MorphismProperty.of_isPullback (P := @IsAffineHom) g4.1.flip inferInstance
    have ha' : IsAffineHom (pullback.fst ((Over.pullback t).obj C.GG).hom xb) :=
      MorphismProperty.of_isPullback (P := @IsAffineHom) g3.1.flip inferInstance
    obtain ⟨d, hd, c, hs⟩ := hCh p y τ xb hy.symm h h1 h2
    have w : pullback.fst ((Over.pullback t).obj C.GG).hom xb ≫ ((Over.pullback t).obj C.GG).hom =
      ((Over.pullback xb).obj ((Over.pullback t).obj C.GG)).hom ≫ xb := g3.1.w
    let φ := g4.1.lift _ _ w
    have f1 : φ ≫ h = _ := g4.1.lift_fst _ _ w
    have f2 : φ ≫ _ = _ := g4.1.lift_snd _ _ w
    have g5 : IsGrpPullback ((Over.pullback xb).obj ((Over.pullback t).obj C.GG))
        ((Over.pullback (rPt p ≫ spMap τ.j)).obj τ.H) (𝟙 _) φ :=
      g4.cancel (g3.congr (Category.id_comp _).symm f1.symm) (f2.trans (Category.comp_id _).symm)
    have hφ : IsAffineHom φ := MorphismProperty.of_isPullback (P := @IsAffineHom) g5.1.flip inferInstance
    have hs' := @SplitPull.pull_pull_and_split_pull.2 (kb p) (kb p) _ _
      ((Over.pullback (rPt p ≫ spMap τ.j)).obj τ.H) _ ((Over.pullback xb).obj ((Over.pullback t).obj C.GG)) _
      (𝟙 _) φ hφ g5 (Ch.pull h) d c hs
    refine ⟨⟨⟨d, Nat.lt_succ_of_le hd⟩, c⟩, ?_, ?_⟩
    · rintro _ rfl
      refine ⟨kb p, inferInstance, xb, ha', hrange, ?_⟩
      have key : ∀ (ψ : ((Over.pullback xb).obj ((Over.pullback t).obj C.GG)).left ⟶ pullback C.GG.hom t)
          [IsAffineHom ψ], φ ≫ h = ψ →
          Charts.Split (H := (Over.pullback xb).obj ((Over.pullback t).obj C.GG)) (Ch.pull ψ) c := by
        intro ψ _ hψ
        subst hψ
        exact hs'
      exact @key _ ha' f1
    · have := hcl (xb ≫ t) (IsLocalRing.closedPoint (kb p))
      exact ((Scheme.Hom.comp_apply xb t _).trans (congrArg t (hxb _))) ▸ this)
  exact ⟨k.1, k.2, Sg k, hk, fun x hx => hx.1 x rfl, fun x hx => hx.2⟩

end GlobalTheory.ZJ.DenseSplit
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

namespace GlobalTheory.ZH.DualSection

theorem proj_mul_proj_eq_zero {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] [hA : ArithBase o Ω]
    (S : ThetaSys o Ω) {T T' : AddSubgroup S.Gam} (h : T' ≤ T) (hT : S.IsoFree T) (hT' : S.IsoFree T')
    (c : T →+ ZMod S.N) (c' : T' →+ ZMod S.N) (hc : c.comp (AddSubgroup.inclusion h) ≠ c') :
    S.proj T c * S.proj T' c' = 0 := by
  haveI : IsDomain o := hA.inj.isDomain
  haveI := FreeNear.finite_char S T
  haveI := Fintype.ofFinite (T →+ ZMod S.N)
  rw [(thetaSys_FF_mem_finite_perp_proj o Ω S).2.2.2 T T' h hT hT' c',
    finsum_mem_eq_finite_toFinset_sum _ (Set.toFinite _), Finset.mul_sum]
  refine Finset.sum_eq_zero fun c'' hc'' => ?_
  rw [(FreeNear.proj_orthogonal S T hT).1, if_neg]
  rintro rfl
  rw [Set.Finite.mem_toFinset] at hc''
  exact hc hc''

theorem mul_dotProduct_mem_of_mem_span {o Ω J : Type} [CommRing o] [Field Ω] [Algebra o Ω] [Fintype J]
    (O : Subalgebra o Ω) (a : Ω) (u : J → Ω) (V : Set (J → Ω)) (hV : ∀ v ∈ V, a * (u ⬝ᵥ v) ∈ O) :
    ∀ v ∈ Submodule.span O V, a * (u ⬝ᵥ v) ∈ O := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem _ h' => exact hV _ h'
  | zero => simp
  | add x y _ _ hx hy => rw [dotProduct_add, mul_add]; exact add_mem hx hy
  | smul s x _ hx =>
    rw [dotProduct_smul, Subalgebra.smul_def, smul_eq_mul, mul_left_comm]
    exact mul_mem s.2 hx

theorem ff_div_th_mul_dotProduct_mem : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), S.admitted M U₀ → ((∀ U₁ : M.Z.Opens, U₁ ≤ U₀ → (U₁ : Set M.Z).Nonempty → ∀ z : M.Z, IsClosed ({z} : Set M.Z) → (∃ (p : ℕ) (_ : Fact p.Prime) (y : Sp (OO p) ⟶ M.Z), M.Cen U₁ z y) ∧ ∀ φ ∈ M.ringOn U₁, (∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), M.Cen U₁ z y → ‖M.val (gPt p ≫ y) φ‖ ≤ 1) → φ ∈ M.O z) ∧ JacobsonSpace M.Z) → (∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), M.Cen U₀ z y → ∃ y₀ : S.R →+* PadicAlgCl p, S.At M y y₀ ∧ (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) ∧ Nonempty (S.Test p y₀)) → (∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), M.Cen U₀ z y → S.At M y y₀ → (∀ x, x ∈ S.supI M z ↔ ‖M.val (gPt p ≫ y) (S.th x)‖ = τ.δ) ∧ S.HH M z = τ.yy.ker) → ((∀ ξ : M.Z, S.IsoFree (S.TT M ξ) ∧ S.perp (S.TT M ξ) = S.HH M ξ) ∧ (∀ ξ z : M.Z, ξ ⤳ z → S.supI M z ⊆ S.supI M ξ) ∧ (∀ ξ ∈ U₀, S.TT M ξ = ⊥) ∧ (∀ (ξ : M.Z) (W : M.Z.Opens), ξ ∈ W → ∃ x ∈ W, IsClosed ({x} : Set M.Z) ∧ ξ ⤳ x ∧ S.supI M x = S.supI M ξ)) → (∀ (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), (∀ c : S.perp τ.yy.ker →+ ZMod S.N, ∃ α : τ.X, (∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) ∧ τ.wt α = c) ∧ ∀ (T : AddSubgroup S.Gam), S.IsoFree T → T ≤ S.perp τ.yy.ker → ∀ (w : S.Gam → τ.X), (∀ x, τ.yy x = QuotientAddGroup.mk (w x)) → ∀ (I : Set S.Gam), AddSubgroup.closure I = S.perp T → ∀ α : τ.X, (∀ (t : S.Gam) (h₂ : t ∈ S.perp τ.yy.ker), t ∈ T → τ.wt α ⟨t, h₂⟩ = 0) ↔ α ∈ AddSubgroup.closure (w '' I ∪ Set.range fun v₀ : τ.X => S.N • v₀)) → (∀ (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → ∀ (T : AddSubgroup S.Gam) (c : T →+ ZMod S.N) (k : _) (hk : S.FF T c k ∈ S.R), S.IsoFree T → (S.perp τ.yy.ker ≤ T → T ≤ τ.yy.ker → ∀ α : τ.X, (∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) → (∀ (t : S.Gam) (h₁ : t ∈ T) (h₂ : t ∈ S.perp τ.yy.ker), c ⟨t, h₁⟩ = τ.wt α ⟨t, h₂⟩) → ‖y₀ ⟨S.FF T c k, hk⟩‖ ≤ τ.δ * Real.exp (-(τ.q α / S.N))) ∧ (T ≤ S.perp τ.yy.ker → ∃ α : τ.X, (∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) ∧ (∀ (t : S.Gam) (h₁ : t ∈ T) (h₂ : t ∈ S.perp τ.yy.ker), c ⟨t, h₁⟩ = τ.wt α ⟨t, h₂⟩) ∧ ‖y₀ ⟨S.FF T c k, hk⟩‖ ≤ τ.δ * Real.exp (-(τ.q α / S.N)))) → (∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), M.Cen U₀ z y → S.At M y y₀ → ∀ (c : S.TT M z →+ ZMod S.N) (k : _) (α : τ.X), M.Div (S.FF (S.TT M z) c) k z → (∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) → (∀ (t : S.Gam) (h₁ : t ∈ S.TT M z) (h₂ : t ∈ S.perp τ.yy.ker), c ⟨t, h₁⟩ = τ.wt α ⟨t, h₂⟩) → ‖M.val (gPt p ≫ y) (S.FF (S.TT M z) c k)‖ = τ.δ * Real.exp (-(τ.q α / S.N))) → (∀ (ξ : M.Z) (c : S.TT M ξ →+ ZMod S.N), S.FF (S.TT M ξ) c ≠ 0) → (∀ z : M.Z, IsClosed ({z} : Set M.Z) → EE.E z = Submodule.span (M.O z) {v | ∃ (c : S.TT M z →+ ZMod S.N) (k : _) (x₀ : S.Gam) (i : S.J), M.Div (S.FF (S.TT M z) c) k z ∧ x₀ ∈ S.supI M z ∧ v = fun j => S.th x₀ / S.FF _ c k * algebraMap o Ω (S.proj _ c j i)}) → ∀ (ξ : M.Z) (c : S.TT M ξ →+ ZMod S.N) (k : _) (i : S.J) (z : M.Z), S.supI M ξ ⊆ S.supI M z → ∀ x₀ ∈ S.supI M z, ∀ v ∈ EE.E z, S.FF _ c k / S.th x₀ * ((fun j => algebraMap o Ω (S.proj _ c i j)) ⬝ᵥ v) ∈ M.O z := by
  intro o Ω _ _ _ _ S M U₀ EE hAdm hLL hT hS hG hW hB hE _ hEE ξ c k i
  have hO := hAdm.1
  have key : ∀ z : M.Z, IsClosed ({z} : Set M.Z) → S.supI M ξ ⊆ S.supI M z → ∀ x₀ ∈ S.supI M z, ∀ v ∈ EE.E z,
      S.FF _ c k / S.th x₀ * ((fun j => algebraMap o Ω (S.proj _ c i j)) ⬝ᵥ v) ∈ M.O z := by
    intro z hz hI x₀ hx₀
    have hH : S.HH M ξ ≤ S.HH M z := AddSubgroup.closure_mono hI
    have hTT : S.TT M z ≤ S.TT M ξ := FirstIneq.perp_anti_of_le S hH
    rw [hEE z hz]
    refine mul_dotProduct_mem_of_mem_span _ _ _ _ ?_
    rintro _ ⟨c₁, k₁, x₁, i₁, hd, -, rfl⟩
    have e : S.FF _ c k / S.th x₀ * ((fun j => algebraMap o Ω (S.proj _ c i j)) ⬝ᵥ
        fun j => S.th x₁ / S.FF _ c₁ k₁ * algebraMap o Ω (S.proj _ c₁ j i₁)) =
        S.FF _ c k / S.FF _ c₁ k₁ * (S.th x₁ / S.th x₀) *
          algebraMap o Ω ((S.proj _ c * S.proj _ c₁) i i₁) := by

      simp only [dotProduct, Matrix.mul_apply, map_sum, map_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [e]
    by_cases hc : c.comp (AddSubgroup.inclusion hTT) = c₁
    swap
    · rw [proj_mul_proj_eq_zero S hTT (hG.1 ξ).1 (hG.1 z).1 c c₁ hc]
      simp
    refine mul_mem (mul_mem ?_ (hx₀.2 x₁)) (Subalgebra.algebraMap_mem _ _)
    have hf : S.FF _ c k ∈ M.ringOn U₀ := hO.le (FirstIneq.ff_mem_ring S _ c k)
    have hf' : S.FF _ c₁ k₁ ∈ M.ringOn U₀ := hO.le (FirstIneq.ff_mem_ring S _ c₁ k₁)
    have hi : (S.FF _ c₁ k₁)⁻¹ ∈ M.ringOn U₀ := hO.FF_unit _ c₁ k₁ (hG.1 z).1 hd.1
    refine (hLL.1 U₀ le_rfl hO.ne z hz).2 _ ?_ ?_
    · rw [div_eq_mul_inv]
      exact mul_mem hf hi
    intro p _ y hy
    obtain ⟨y₀, hAt, hint, ⟨τ⟩⟩ := hT z p y hy
    have hker : S.HH M z = τ.yy.ker := (hS z p y y₀ τ hy hAt).2
    have hperp : S.perp τ.yy.ker = S.TT M z := by rw [← hker]; rfl
    obtain ⟨α, hα, hwt⟩ := (hW p y₀ τ).1 (c₁.comp (AddSubgroup.inclusion hperp.le))
    have h1 := (hB p y₀ τ hint (S.TT M ξ) c k (FirstIneq.ff_mem_ring S _ c k) (hG.1 ξ).1).1
      (hperp.le.trans hTT) (((hG.1 ξ).1.1.trans (hG.1 ξ).2.le).trans (hH.trans hker.le)) α hα
      (fun t h₁ h₂ => by rw [hwt, ← hc]; rfl)
    have h2 := hE z p y y₀ τ hy hAt c₁ k₁ α hd hα (fun t h₁ h₂ => by rw [hwt]; rfl)
    rw [hAt, ← h2] at h1
    set yg := gPt p ≫ y with hyg
    have w : Sp (PadicAlgCl p) := IsLocalRing.closedPoint (PadicAlgCl p)
    have hw : yg w ∈ (U₀ : Set M.Z) := hy.2 ⟨w, rfl⟩
    have hsp := RatModel.specializes_of_range_eq (RatModel.range_eq_singleton yg w)
    have e1 : M.val yg (S.FF _ c₁ k₁) * M.val yg (S.FF _ c₁ k₁)⁻¹ = 1 := by
      rw [← RatModel.val_mul hsp (RatModel.ringOn_le_O hw hf') (RatModel.ringOn_le_O hw hi),
        mul_inv_cancel₀ hd.1, RatModel.val_one]
    rw [div_eq_mul_inv, RatModel.val_mul hsp (RatModel.ringOn_le_O hw hf) (RatModel.ringOn_le_O hw hi),
      norm_mul, ← norm_one (α := PadicAlgCl p), ← e1, norm_mul]
    exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
  intro z hI x₀ hx₀
  obtain ⟨U, b, hzU, -, hb⟩ := EE.loc z
  obtain ⟨x, hxU, hxc, hzx, hIx⟩ := hG.2.2.2 z U hzU
  rw [hb z hzU]
  refine mul_dotProduct_mem_of_mem_span _ _ _ _ fun v hv => RatModel.O_le_of_specializes hzx ?_
  refine key x hxc (hIx ▸ hI) x₀ (hIx ▸ hx₀) v ?_
  rw [hb x hxU]
  exact Submodule.subset_span hv

end GlobalTheory.ZH.DualSection
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.ThetaReal

theorem pt_nsmul {G H : Type} [AddCommGroup G] [Group H] (pt : G → H) (h : ∀ a b, pt (a + b) = pt a * pt b) :
    pt 0 = 1 ∧ ∀ (n : ℕ) a, pt (n • a) = pt a ^ n := by
  have h0 : pt 0 = 1 := by
    have := h 0 0
    rw [add_zero] at this
    exact left_eq_mul.1 this
  refine ⟨h0, fun n a => ?_⟩
  induction n with
  | zero => rw [zero_smul, pow_zero, h0]
  | succ n ih => rw [succ_nsmul, h, ih, pow_succ]

theorem eStd_nsmul (g M r : ℕ) (a b : Fin g ⊕ Fin g → ZMod M) : eStd g M a (r • b) = r • eStd g M a b := by
  simp only [eStd, Finset.smul_sum, Pi.smul_apply, nsmul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem nsmul_self {κ : Type} (M : ℕ) (a : κ → ZMod M) : M • a = 0 := by
  funext i
  simp

theorem exists_operators (hL : Laws) {S : Scheme.{0}} [IsLocallyNoetherian S] (P : PolAV S) {g m r N : ℕ}
    (hN : N = m ^ 2) (hm : Odd m) (hu : IsUnit ((r * N : ℕ) : Γ(S, ⊤))) (ze : Γ(S, ⊤)ˣ)
    (pt : (Fin g ⊕ Fin g → ZMod (r * N)) → (baseOver S ⟶ P.A)) (hadd : ∀ a b, pt (a + b) = pt a * pt b)
    (hw : ∀ a b, WeilIs P.A P.L (r * N : ℕ) (pt a) (pt b) (ze ^ (r * N * (eStd g (r * N) a b).val)))
    (U : (Fin g ⊕ Fin g → ZMod (r * N)) → ThetaGrp P.A P.L N (baseOver S))
    (hU : ∀ a, SymLift P.A P.L N N (pt (r • a)) (U a))
    {α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(snd (baseOver S) P.A).left, (snd (baseOver S) P.A ^ m).left]
      ![(N : ℤ), -1])} (hα : α.IsGen) {th : LB.Sec (LPow P.A P.L 1 (baseOver S))}
    {s₀ : LB.Sec (LPow P.A P.L N (baseOver S))}
    (hs : IsTwistPull P.A P.L (mulT P.A _ m) (snd _ P.A ^ m) (lift_snd _ _) N 1 α th s₀) :
    ∃ u : (Fin g ⊕ Fin g → ZMod (r * N)) →
        SecM P.A P.L N (baseOver S) →ₗ[Γ((baseOver S).left, ⊤)] SecM P.A P.L N (baseOver S),
      (∀ a s s', IsActOf P.A P.L N (U a) s s' ↔ u a (SecM.ofSec P.A s) = SecM.ofSec P.A s') ∧
      (∀ a, r • a = 0 → ∀ v, u a v = v) ∧
      (∀ a b, ∃ e : ℕ, ∀ v, u a (u b v) = (show Γ((baseOver S).left, ⊤) from ze.val ^ e) • u (a + b) v) ∧
      (∀ a b, r • eStd g _ a b = 0 → ∀ v, u a (u b v) = u (a + b) v) ∧
      ∀ a, (r * m) • a = 0 → u a (SecM.ofSec P.A s₀) = SecM.ofSec P.A s₀ := by
  obtain ⟨ρ, hρ, -⟩ := GlobalTheory.thetaGrp_acts_linearly hL.globalFns S P N (baseOver S)
  obtain ⟨h0, hsm⟩ := pt_nsmul pt hadd
  have hodd : Odd N := hN ▸ hm.pow
  have tors : ∀ a, pt (r • a) ^ N = 1 := fun a => by rw [← hsm, smul_smul, mul_comm N r, nsmul_self, h0]
  have act : ∀ a v, IsActOf P.A P.L N (U a) (SecM.toSec P.A v) (SecM.toSec P.A (ρ (U a) v)) := fun a v =>
    (hρ _ _ _).2 rfl
  have weil : ∀ a b, WeilIs P.A P.L N (pt (r • a)) (pt (r • b))
      (ze ^ (r * N * (r • eStd g (r * N) a b).val)) := fun a b => by
    have h₁ := hw a (r • b)
    rw [eStd_nsmul] at h₁
    have h₂ := (hL.weil S P N (baseOver S)).2.2.2 r (pt a) (pt (r • b))
      (ze ^ (r * N * (r • eStd g (r * N) a b).val)) (by rw [mul_comm]; exact hu)
      (by rw [← hsm, mul_comm N r, nsmul_self, h0]) (tors b)
    rw [hsm r a]
    refine h₂.1 ?_
    rw [← Nat.cast_mul, mul_comm N r]
    exact h₁
  have key : ∀ a b v, ρ (U a) (ρ (U b) v) = (show Γ((baseOver S).left, ⊤) from
      ze.val ^ (r * N * (r • eStd g (r * N) a b).val * ((N + 1) / 2))) • ρ (U (a + b)) v := fun a b v => by
    have := act_act hL.globalFns P.isAb P.isLB hodd (tors b) (hU a) (hU b)
      (by rw [← hadd, ← smul_add, add_comm]; exact hU (a + b)) (weil a b) (act b v) (act a _) (act (a + b) v)
    refine this.trans (congrArg (· • _) ?_)
    rw [pow_mul ze.val]
    exact (Units.val_pow_eq_pow_val _ _).trans (congrArg (· ^ _) (Units.val_pow_eq_pow_val _ _))
  refine ⟨fun a => (ρ (U a)).toLinearMap, fun a => hρ _, fun a ha v => ?_, fun a b => ⟨_, key a b⟩,
    fun a b h v => ?_, fun a ha => (hρ _ _ _).1 ?_⟩
  · have h₁ : SymLift P.A P.L N N 1 (U a) := by
      have := hU a
      rwa [ha, h0] at this
    have := act_act hL.globalFns P.isAb P.isLB hodd (one_pow N) h₁ h₁ (by rw [_root_.mul_one]; exact h₁)
      ((hL.weil S P N (baseOver S)).2.2.1 1 (one_pow N)) (act a v) (act a _) (act a v)
    rw [one_pow, Units.val_one, one_smul] at this
    exact (ρ (U a)).injective this
  · refine (key a b v).trans ?_
    rw [h, ZMod.val_zero, mul_zero, zero_mul, pow_zero]
    exact one_smul _ _
  · obtain ⟨ν, hν⟩ := GlobalTheory.exists_gen_negLB hL.globalFns S P 1 (baseOver S)
    exact isActOf_self hL.globalFns P.isAb P.isLB hν hodd hα hs
      (by rw [← hsm, smul_smul, mul_comm m r, ha, h0]) (tors a) (hU a)

end GlobalTheory.ThetaReal
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UnitTheta

theorem le_preimage_wchart_of_section {X Y : Scheme.{0}} (L : LB X) (π : Y ⟶ X) (σ : X ⟶ Y) (h : σ ≫ π = 𝟙 X)
    (k : L.ι) : L.U k ≤ σ ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => π) (fun _ => k) := by
  intro x hx
  refine Set.mem_iInter.2 fun _ => ?_
  change (σ ≫ π) x ∈ L.U k
  rw [h]
  exact hx

noncomputable def secOfSection {X Y : Scheme.{0}} (L : LB X) (π : Y ⟶ X) (σ : X ⟶ Y) (h : σ ≫ π = 𝟙 X)
    (s : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => π) (fun _ => 1))) : LB.Sec L where
  f k := (X.presheaf.map (homOfLE (le_preimage_wchart_of_section L π σ h k)).op).hom
    ((σ.app _).hom (s.f (fun _ => k)))
  compat i j := fn_ext fun x hx => by
    have li := le_preimage_wchart_of_section L π σ h i hx.1
    have lj := le_preimage_wchart_of_section L π σ h j hx.2
    rw [gs_res _ x inf_le_left hx, gs_mul _ x _ hx, gs_res _ x inf_le_right hx, gs_res _ x _ hx.1, gs_res _ x _ hx.2,
      gs_unit _ x _ hx]
    refine (gs_pull (𝟙 X) σ x _ li _).trans ((sec_trans s (𝟙 X ≫ σ) x li lj).trans
      (congrArg₂ (· * ·) ?_ (gs_pull (𝟙 X) σ x _ lj _).symm))
    simp only [trF, Fin.prod_univ_one, zpow_one, Category.assoc, h, Category.comp_id]

theorem gs_secOfSection {X Y Z : Scheme.{0}} (L : LB X) (π : Y ⟶ X) (σ : X ⟶ Y) (h : σ ≫ π = 𝟙 X)
    (s : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => π) (fun _ => 1))) (r : Z ⟶ X) (z : Z) (k : L.ι)
    (hz : r z ∈ L.U k) : gs r z _ ((secOfSection L π σ h s).f k) =
      gs (r ≫ σ) z (LB.wchart L (fun _ : Fin 1 => π) (fun _ => k)) (s.f (fun _ => k)) :=
  (gs_res r z _ hz _).trans (gs_pull r σ z _ (le_preimage_wchart_of_section L π σ h k hz) _)

theorem valR_secOfSection {X Y : Scheme.{0}} (L : LB X) (π : Y ⟶ X) (σ : X ⟶ Y) (h : σ ≫ π = 𝟙 X)
    (s : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => π) (fun _ => 1))) {F : Type} [CommRing F] (r : Sp F ⟶ X)
    (k : L.ι) (hr : ⊤ ≤ r ⁻¹ᵁ L.U k) : valR r _ ((secOfSection L π σ h s).f k) =
      valR (r ≫ σ) (LB.wchart L (fun _ : Fin 1 => π) (fun _ => k)) (s.f (fun _ => k)) :=
  (HolHom.valR_res r _ _ hr).trans (HolHom.valR_comp r σ _ _).symm

theorem mem_nonzeroLocus_secOfSection {X Y : Scheme.{0}} (L : LB X) (π : Y ⟶ X) (σ : X ⟶ Y) (h : σ ≫ π = 𝟙 X)
    (h' : π ≫ σ = 𝟙 Y) (s : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => π) (fun _ => 1))) (y : Y)
    (hy : y ∈ nonzeroLocus s) : π y ∈ nonzeroLocus (secOfSection L π σ h s) := by
  obtain ⟨j, hj⟩ := AmpleSpan.exists_chart_of_mem s hy
  obtain ⟨k, rfl⟩ : ∃ k, j = fun _ => k := ⟨j (0 : Fin 1), funext fun i => by rw [Subsingleton.elim i 0]⟩
  have hk : π y ∈ L.U k := Set.mem_iInter.1 hj 0
  rw [AmpleSpan.mem_nonzeroLocus_iff_gs _ π y hk, gs_secOfSection L π σ h s π y k hk, h']
  exact (AmpleSpan.mem_nonzeroLocus_iff_gs s (𝟙 Y) y hj).1 hy

theorem exists_sec_of_baseOver : ∀ (R : Type) [CommRing R] (P : PolAV (Sp R)) (th : LB.Sec (LPow P.A P.L 1 (baseOver (Sp R)))), ∃ θ : LB.Sec P.L, (∀ y ∈ nonzeroLocus th, (snd (baseOver (Sp R)) P.A).left y ∈ nonzeroLocus θ) ∧ ∀ (z : baseOver (Sp R) ⟶ P.A) (τ : LB.Gen (LB.LinComb P.L (Y := (baseOver (Sp R)).left) (K := Fin 1) (fun _ => z.left) (fun _ => 1))) (a : R), IsValueAt P.A P.L 1 th z τ (fn a) → ∀ (F : Type) [CommRing F] (f : R →+* F) (k : P.L.ι), ⊤ ≤ (spMap f ≫ z.left) ⁻¹ᵁ P.L.U k → valR (spMap f ≫ z.left) _ (θ.f k) = f a * valR (X := (baseOver (Sp R)).left) (spMap f) _ (τ.s (fun _ => k)).val := by
  intro R _ P th
  let σ : P.A ⟶ baseOver (Sp R) ⊗ P.A := lift (toUnit P.A) (𝟙 P.A)
  have h : σ ≫ snd _ _ = 𝟙 _ := lift_snd _ _
  have h' : snd _ _ ≫ σ = 𝟙 _ := by
    refine CartesianMonoidalCategory.hom_ext _ _ (toUnit_unique _ _) ?_
    rw [Category.assoc, h, Category.comp_id, Category.id_comp]
  have hl : σ.left ≫ (snd (baseOver (Sp R)) P.A).left = 𝟙 _ := by rw [← Over.comp_left, h, Over.id_left]
  have hl' : (snd (baseOver (Sp R)) P.A).left ≫ σ.left = 𝟙 _ := by rw [← Over.comp_left, h', Over.id_left]
  refine ⟨secOfSection P.L _ σ.left hl th, mem_nonzeroLocus_secOfSection P.L _ σ.left hl hl' th, ?_⟩
  intro z τ a hv F _ f k hk
  have e : z ≫ σ = ptSecT P.A z := by
    refine CartesianMonoidalCategory.hom_ext _ _ (toUnit_unique _ _) ?_
    rw [Category.assoc, h, Category.comp_id, ptSecT, lift_snd]
  have e' : z.left ≫ σ.left = (ptSecT P.A z).left := by rw [← Over.comp_left, e]
  let x : Sp F ⟶ (baseOver (Sp R)).left := spMap f
  have hw : ⊤ ≤ x ⁻¹ᵁ LB.wchart P.L (fun _ : Fin 1 => z.left) (fun _ => k) :=
    fun p hp => Set.mem_iInter.2 fun _ => hk hp
  have H := congrArg (valR x _) (hv (fun _ => k))
  have H₁ := (HolHom.valR_comp x (ptSecT P.A z).left _ _).trans ((HolHom.valR_res x _ _ hw).symm.trans H)
  have H₂ := H₁.trans (((HolHom.valR_eq x _ hw _).trans (map_mul _ _ _)).trans (congrArg₂ (· * ·)
    ((HolHom.valR_eq x _ hw _).symm.trans ((HolHom.valR_res x _ _ hw).trans (Conv.valR_spMap_top f a)))
    (HolHom.valR_eq x _ hw _).symm))
  refine (valR_secOfSection P.L _ σ.left hl th (x ≫ z.left) k hk).trans ?_
  rw [Category.assoc, e']
  exact H₂

end GlobalTheory.UnitTheta
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
theorem _root_.GlobalTheory.T.torsionValues_coords_operator_permute : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real), (∀ (K : Type) [Field K] (y : S.R →+* K) (a : S.Gam), ρ.Crd (spMap y ≫ (ρ.pt a).left) (fun i => y ⟨S.ev a i, S.ev_mem a i⟩)) ∧ ∀ a h : S.Gam, ∃ e : ℕ, ∀ i, ∑ n, algebraMap o Ω (S.ρ a n i) * S.ev h n = algebraMap o Ω (S.ζ ^ e) * S.ev (h + S.r • a) i := by
  first | exact @GlobalTheory.ZH.EvCrd.ev_crd_act | exact GlobalTheory.ZH.EvCrd.ev_crd_act | (intros; apply GlobalTheory.ZH.EvCrd.ev_crd_act <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite

theorem _root_.GlobalTheory.T.twistedPower_sectionBasis_baseChange : DVR.TwistBaseChangeStatement → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (D : DegPre R) (N : ℕ), 1 ≤ N → ∀ (α : D.X) (R' : Type) [CommRing R'] (φ : R →+* R') (B : Scheme.{0}) (pB : B ⟶ Sp R') (π : B ⟶ D.P.A.left), IsPullback π pB D.P.A.hom (spMap φ) → ∀ (I : Type) [Fintype I] (β : I → D.SecB N α), IsBasisB D β → ∀ b : LB.Sec (LB.LinComb D.P.L (fun i => π ≫ D.famφB α i) (DegPre.famε N)), ∃! a : I → R', IsLin pB (fun i => DVR.pullSec D.P.L (D.famφB α) (DegPre.famε N) (β i) π) a b := by
  first | exact @GlobalTheory.ZH.BasisBaseChange.basis_pullback | exact GlobalTheory.ZH.BasisBaseChange.basis_pullback | (intros; apply GlobalTheory.ZH.BasisBaseChange.basis_pullback <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
theorem _root_.GlobalTheory.T.testQuadraticForm_eq_psi_valuation_mul : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab), ∃ (ϖ : u.V) (Q : u.D.toPre.X → ℤ), Irreducible ϖ ∧ DVR.QForm.IsQ u.D.toPre ϖ Q ∧ ‖(u.j ϖ : PadicAlgCl p)‖ < 1 ∧ ∀ χ, l.q χ = Q χ * (-Real.log ‖(u.j ϖ : PadicAlgCl p)‖) := by
  first | exact @GlobalTheory.ZH.PsiForm.q_eq_val_mul | exact GlobalTheory.ZH.PsiForm.q_eq_val_mul | (intros; apply GlobalTheory.ZH.PsiForm.q_eq_val_mul <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

theorem _root_.GlobalTheory.T.exists_projBundle_closure_alt : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [IsNoetherianRing o] (M : RatModel o Ω) (Ω' : Type) [Field Ω'] [Algebra o Ω'] (φ : Ω →ₐ[o] Ω') (J : Type) [Fintype J] (EE : M.Lat J) (s : J → Ω'), IsProjOver M.s → (∃ j, s j ≠ 0) → Subfield.closure (Set.range φ ∪ {x | ∃ i j, x = s j / s i}) = ⊤ → ∃ (M' : RatModel o Ω') (f : M'.Z ⟶ M.Z), M.IsHom M' φ f ∧ IsProjOver M'.s ∧ ∀ (W : M.Z.Opens) (B : Matrix J J Ω), IsAffineOpen W → (W : Set M.Z).Nonempty → (∀ z ∈ W, EE.E z = Submodule.span (M.O z) (Set.range B)) → (∀ z', f z' ∈ W → ∃ i, M'.Div ((B.map φ).mulVec s) i z') ∧ ∀ i, (B.map φ).mulVec s i ≠ 0 → ∃ U : M'.Z.Opens, IsAffineOpen U ∧ (U : Set M'.Z) = {z' | f z' ∈ W ∧ M'.Div ((B.map φ).mulVec s) i z'} ∧ M'.ringOn U = Algebra.adjoin o (φ '' (M.ringOn W : Set Ω) ∪ Set.range fun j => (B.map φ).mulVec s j / (B.map φ).mulVec s i) := by
  first | exact @GlobalTheory.ZH.RatModel.exists_projBundle_closure | exact GlobalTheory.ZH.RatModel.exists_projBundle_closure | (intros; apply GlobalTheory.ZH.RatModel.exists_projBundle_closure <;> assumption)
end
