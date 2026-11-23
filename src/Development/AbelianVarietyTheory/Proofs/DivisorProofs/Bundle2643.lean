module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle015
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle111
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle091
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.UniformityLowerBounds
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle064
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle084
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle127
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle090
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle018
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle024
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle160
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle028
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2618
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.SiegAct

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem spMap_inj {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B} (h : spMap f = spMap g) : f = g :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)

theorem spMap_id' (A : Type) [CommRing A] : spMap (RingHom.id A) = 𝟙 (Sp A) := Spec.map_id _

theorem exists_spMap {k B : Type} [CommRing k] [CommRing B] (x : Sp k ⟶ Sp B) : ∃ β : B →+* k, x = spMap β :=
  ⟨(Spec.preimage x).hom, by rw [spMap, CommRingCat.ofHom_hom, Spec.map_preimage]⟩

theorem unit_left' {S T : Scheme.{0}} {G : Over S} (x : T ⟶ S) (σ : 𝟙_ (Over S) ⟶ G) :
    (toUnit (Over.mk x) ≫ σ).left = x ≫ σ.left := by
  simp

variable {h N m : ℕ} {B B' : Type} [CommRing B] [CommRing B'] {ζ : B} {ζ' : B'} {S : Scheme.{0}} {s : S ⟶ Sp B}

theorem lev_zero (C : SiegPre h N ζ s) : C.lev 0 = 1 := by
  have := C.lev_add 0 0
  rw [add_zero] at this
  exact left_eq_mul.1 this

theorem lev_nsmul (C : SiegPre h N ζ s) (k : ℕ) (a : Fin h ⊕ Fin h → ℤ) : C.lev (k • a) = C.lev a ^ k := by
  induction k with
  | zero => rw [zero_smul, pow_zero, lev_zero]
  | succ k ih => rw [succ_nsmul, C.lev_add, ih, pow_succ]

theorem lev_N_smul (C : SiegPre h N ζ s) (a : Fin h ⊕ Fin h → ℤ) : C.lev (N • a) = 1 := by
  rw [lev_nsmul, C.lev_tors]

def relabel (C : SiegPre h N ζ s) (T : (Fin h ⊕ Fin h → ℤ) →ₗ[ℤ] (Fin h ⊕ Fin h → ℤ)) (σ : B' →+* B)
    (hN : N ≠ 0) (hζ : ζ ^ N = 1) (hσ : σ ζ' = ζ ^ m)
    (hω : ∀ x y, omegaStd (T x) (T y) ≡ m * omegaStd x y [ZMOD N])
    (hinj : ∀ a, (∃ b, T a = N • b) → ∃ b, a = N • b)
    (hsurj : ∀ a, ∃ a' b, T a' = a + N • b) : SiegPre h N ζ' (s ≫ spMap σ) where
  A := C.A
  ab := C.ab
  P := C.P
  isLB := C.isLB
  rig₁ := C.rig₁
  rig₂ := C.rig₂
  symm := C.symm
  lev x := C.lev (T x)
  lev_add a b := by rw [map_add (f := _), C.lev_add]
  lev_tors a := C.lev_tors _
  geom k _ _ x β z hx hz := by
    obtain ⟨β₀, hβ₀⟩ := exists_spMap (x ≫ s)
    have hb : β = β₀.comp σ := spMap_inj (by rw [← hx, ← Category.assoc, hβ₀, spMap_comp'])
    have h1 : β₀ ζ ^ N = 1 := by rw [← map_pow, hζ, map_one]
    let z₀ : kˣ := Units.ofPowEqOne (β₀ ζ) N h1 hN
    obtain ⟨g1, g2, g3⟩ := C.geom k x β₀ z₀ hβ₀ rfl
    have hzm : z = z₀ ^ m := Units.ext (by
      rw [hz, hb, RingHom.comp_apply, hσ, map_pow, Units.val_pow_eq_pow_val]; rfl)
    have hz₀ : z₀ ^ N = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val]; exact h1)
    refine ⟨fun a => (g1 (T a)).trans ⟨hinj a, fun ⟨b, hb⟩ => ⟨T b, by rw [hb, map_nsmul]⟩⟩, fun g hg => ?_,
      fun a b => ?_⟩
    · obtain ⟨a, ha⟩ := g2 g hg
      obtain ⟨a', b, hab⟩ := hsurj a
      refine ⟨a', ?_⟩
      show toUnit _ ≫ C.lev (T a') = g
      rw [hab, C.lev_add, MonObj.comp_mul, lev_N_smul, MonObj.comp_one, _root_.mul_one, ha]
    · have e : z₀ ^ (2 * omegaStd (T a) (T b)) = z ^ (2 * omegaStd a b) := by
        rw [hzm, ← zpow_natCast, ← zpow_mul]
        refine zpow_eq_zpow_iff_modEq.2 (Int.ModEq.of_dvd (Int.natCast_dvd_natCast.2 (orderOf_dvd_of_pow_eq_one hz₀)) ?_)
        have := (hω a b).mul_left 2
        calc 2 * omegaStd (T a) (T b) ≡ 2 * (m * omegaStd a b) [ZMOD N] := this
          _ = m * (2 * omegaStd a b) := by ring
      have := g3 (T a) (T b)
      rw [e] at this
      exact this

section Calc

open GlobalTheory.SiegelPullComp GlobalTheory.SiegelPull

variable {h n n' n'' : ℕ} {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B''] {ζ : B} {ζ' : B'} {ζ'' : B''}
  {S S' S'' : Scheme.{0}} {s : S ⟶ Sp B} {s' : S' ⟶ Sp B'} {s'' : S'' ⟶ Sp B''}
  {c : SiegPre h n ζ s} {c' : SiegPre h n' ζ' s'} {c'' : SiegPre h n'' ζ'' s''} {f : S' ⟶ S} {f' : S'' ⟶ S'}
  {d d' d'' : ℕ}

def Sq (c' : SiegPre h n' ζ' s') (c : SiegPre h n ζ s) (φ : c'.A.left ⟶ c.A.left) : Prop :=
  ∃ φ₂ : (G2 c'.A).left ⟶ (G2 c.A).left, IsSquare φ φ₂ ∧ LBIso c'.P (c.P.pull φ₂)

theorem Sq.comp {φ : c'.A.left ⟶ c.A.left} {ψ : c''.A.left ⟶ c'.A.left} (m : Sq c' c φ) (m' : Sq c'' c' ψ) :
    Sq c'' c (ψ ≫ φ) := by
  obtain ⟨φ₂, hs, hw⟩ := m
  obtain ⟨ψ₂, hs', hw'⟩ := m'
  refine ⟨ψ₂ ≫ φ₂, ⟨?_, ?_⟩, ?_⟩
  · rw [Category.assoc, hs.1, ← Category.assoc, hs'.1, Category.assoc]
  · rw [Category.assoc, hs.2, ← Category.assoc, hs'.2, Category.assoc]
  · exact (hw'.trans c''.isLB (pull_isLB c'.isLB _) (pull_isLB (pull_isLB c.isLB _) _) (iso_pull ψ₂ hw)).trans
      c''.isLB (pull_isLB (pull_isLB c.isLB _) _) (pull_isLB c.isLB _) (iso_pull_pull c.isLB φ₂ ψ₂)

theorem sRelBy_comp {φ : c'.A.left ⟶ c.A.left} {ψ : c''.A.left ⟶ c'.A.left} (m : SRelBy c' c d' d f φ)
    (m' : SRelBy c'' c' d'' d' f' ψ) : SRelBy c'' c d'' d (f' ≫ f) (ψ ≫ φ) := by
  obtain ⟨hφ, hs, hl⟩ := m
  obtain ⟨hψ, hs', hl'⟩ := m'
  refine ⟨hψ.comp hφ, Sq.comp (c := c) (c' := c') (c'' := c'') hs hs', fun a => ?_⟩
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ φ) (hl' a)).trans ((Category.assoc _ _ _).trans
      ((congrArg (f' ≫ ·) (hl a)).trans (Category.assoc _ _ _).symm)))

theorem pow_section {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {φ : A'.left ⟶ A.left}
    (hφ : IsGrpPullback A' A f φ) (x' : 𝟙_ (Over S') ⟶ A') (x : 𝟙_ (Over S) ⟶ A)
    (e : x'.left ≫ φ = f ≫ x.left) (k : ℕ) : (x' ^ k).left ≫ φ = f ≫ (x ^ k).left := by
  have e₁ : x' = SiegelPull.secPull hφ x := by
    refine push_injective hφ _ (Over.OverMorphism.ext ?_)
    exact e.trans (SiegelPull.secPull_left hφ x).symm
  have e₂ : x' ^ k = SiegelPull.secPull hφ (x ^ k) := push_injective hφ _ (by
    rw [map_pow, e₁, push_secPull', push_secPull', MonObj.comp_pow])
  rw [e₂, SiegelPull.secPull_left]

end Calc

section Twist

variable {h n N : ℕ}

structure Twist (F : SFam h N (zetaAway N)) (j : cycAway n →+* cycAway N)
    (T : (Fin h ⊕ Fin h → ℤ) →ₗ[ℤ] (Fin h ⊕ Fin h → ℤ)) (m : ℕ) (σ : cycAway N →+* cycAway N) (f : F.X ⟶ F.X) :
    Prop where
  cop : m.Coprime N
  root : σ (zetaAway N) = zetaAway N ^ m
  fix : σ.comp j = j
  symp : ∀ x y, omegaStd (T x) (T y) ≡ m * omegaStd x y [ZMOD N]
  low : ∀ x, F.univ.lev (T x) ^ (N / n) = F.univ.lev x ^ (N / n)
  comm : f ≫ F.s = F.s ≫ spMap σ
  map : ∃ ν : F.univ.A.left ⟶ F.univ.A.left, IsGrpPullback F.univ.A F.univ.A f ν ∧ Sq F.univ F.univ ν ∧
    ∀ x, (F.univ.lev (T x)).left ≫ ν = f ≫ (F.univ.lev x).left

end Twist

end GlobalTheory.SiegAct
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ThetaAtRoot

section
variable {S : Scheme.{0}} (P : PolAV S) (rig : LB.Gen (P.L.pull (eSec P.A)))

theorem val_powFrame' {T : Over S} (x : T ⟶ P.A) (e) (k : ℤ) {Z : Scheme.{0}} (r : Z ⟶ T.left) (z : Z) (J) :
    val (powFrame P.A P.L x e k) r z J = val e r z J ^ k :=
  map_zpow _ _ _

theorem isThetaConst_of_thG (hrig : rig.IsGen) {m : ℕ} {T : Over S} {th : LB.Sec (LPow P.A P.L ((1 : ℕ) : ℤ) T)}
    {x : T ⟶ P.A} {c : Γ(T.left, ⊤)} (H : ThG P.A P.L rig m th x c) :
    ∃ (s₁ s₂ : LB.Sec (LPow P.A P.L ((m ^ 2 : ℕ) : ℤ) T)) (U : ThetaGrp P.A P.L ((m ^ 2 : ℕ) : ℤ) T),
      GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.IsMulPull P rig m ((m ^ 2 : ℕ) : ℤ) th s₁ ∧ SymLift P.A P.L ((m ^ 2 : ℕ) : ℤ) (m ^ 2) x U ∧
      IsActOf P.A P.L ((m ^ 2 : ℕ) : ℤ) U s₁ s₂ ∧ GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.IsValueZero P rig ((m ^ 2 : ℕ) : ℤ) s₂ c := by
  obtain ⟨-, t, α, s₁, θ, hα, h₂, h₃, h₄, h₅, h₆⟩ := H
  refine ⟨s₁, t, θ, ⟨α, hα, corr_of_val P.isLB fun y J hJ => ?_, h₃⟩, h₄, h₅,
    ⟨rigT P.A P.L rig T ((m ^ 2 : ℕ) : ℤ), GlobalTheory.ThetaReal.NormMul.rigT_isGen hrig _, corr_of_val P.isLB fun _ _ _ => rfl,
      GlobalTheory.ThetaPtMove.isValueAt_of_sv P.isLB fun y J hJ => by rw [Category.id_comp]; exact h₆ y J hJ⟩⟩
  refine (val_corr hJ h₂ (𝟙 _)).trans ?_
  rw [val_mul hJ, val_inv, GlobalTheory.Ex.OneGen.val_rigT _ _ y hJ, GlobalTheory.Ex.OneGen.val_rigT _ _ y hJ,
    GlobalTheory.Ex.OneGen.val_rigT _ _ y hJ, zpow_sub_one, zpow_one]

theorem frame_pull {n : ℕ} {T T₀ : Over S} (u : T ⟶ T₀) {x₀ : T₀ ⟶ P.A}
    {e₀ : LB.Gen (LB.LinComb P.L (Y := T₀.left) (K := Fin 1) (fun _ => x₀.left) (fun _ => 1))}
    (H : IsTorsFrame P rig n x₀ e₀) :
    IsTorsFrame P rig n (u ≫ x₀) (LB.pullGen P.L (fun _ => x₀.left) (fun _ => 1) e₀ u.left) := by
  obtain ⟨h₁, h₂, α, hα, hN, hc⟩ := H
  refine ⟨by rw [← MonObj.comp_pow, h₁, MonObj.comp_one], LB.isGen_pullGen _ _ _ _ h₂ _, α, hα, hN,
    corr_of_val P.isLB fun y J hJ => ?_⟩
  have q := val_corr hJ hc u.left
  rw [val_powFrame', val_mul hJ, val_pull hJ, GlobalTheory.Ex.OneGen.val_rigT _ _ y hJ, Over.w u] at q
  rw [val_powFrame', val_pull hJ, val_mul hJ, val_pull hJ, GlobalTheory.Ex.OneGen.val_rigT _ _ y hJ, Category.id_comp,
    Category.id_comp, Category.id_comp, Over.comp_left]
  exact q

theorem value_pull {T T₀ : Over S} (u : T ⟶ T₀) {x₀ : T₀ ⟶ P.A}
    {e₀ : LB.Gen (LB.LinComb P.L (Y := T₀.left) (K := Fin 1) (fun _ => x₀.left) (fun _ => 1))}
    {th : LB.Sec (LPow P.A P.L 1 T₀)} {c : Γ(T₀.left, ⊤)} (H : IsValueAt P.A P.L 1 th x₀ e₀ c) :
    IsValueAt P.A P.L 1 (VVRank.pullS P.A 1 u th) (u ≫ x₀)
      (LB.pullGen P.L (fun _ => x₀.left) (fun _ => 1) e₀ u.left) (u.left.appTop.hom c) := by
  refine GlobalTheory.ThetaPtMove.isValueAt_of_sv P.isLB fun y J hJ => ?_
  have e : (ptSecT P.A (u ≫ x₀)) ≫ (u ▷ P.A) = u ≫ ptSecT P.A x₀ := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [ptSecT]
  have e' : (𝟙 _ ≫ (ptSecT P.A (u ≫ x₀)).left) ≫ (u ▷ P.A).left = u.left ≫ (ptSecT P.A x₀).left := by
    rw [Category.id_comp, ← Over.comp_left, e, Over.comp_left]
  rw [VVRank.sv_pullS _ _ _ _ _ _ hJ, e', GlobalTheory.ThetaPtMove.sv_of_isValueAt H u.left y hJ, val_pull hJ, Category.id_comp]
  exact congrArg (· * _) (gs_pull (𝟙 _) u.left y ⊤ trivial c).symm

end

end GlobalTheory.ThetaAtRoot

namespace GlobalTheory


open GlobalTheory.ThetaAtRoot in
theorem thetaConst_pow_eq_at_root : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (K : Type) [Field K] (i : S.R →+* K) (b : S.Gam) (y : Over.mk (spMap i ≫ 𝟙 (Sp S.R)) ⟶ ρ.P.A) (v : K), y ^ (S.r * S.N) = (Over.homMk (spMap i) (by simp) : Over.mk (spMap i ≫ 𝟙 (Sp S.R)) ⟶ baseOver (Sp S.R)) ≫ ρ.pt b → ThG ρ.P.A ρ.P.L ρ.rig (S.r * S.N) (SecAt.pull ρ.P.A ρ.P.L (x := 𝟙 (Sp S.R)) ρ.th₁ i) y (GlobalTheory.ZH.fn v) → v ^ ((S.r * S.N) ^ 2) = i ⟨S.th b, S.th_mem b⟩ ^ ((S.r * S.N) ^ 2) := by
  intro o Ω _ _ _ _ S ρ K _ i b y v hy H
  have hL : Laws := GlobalTheory.firstFiveLaws.1
  have hk : Odd (S.r * S.N) := by
    obtain ⟨j, -, hj⟩ := ρ.r_eq
    rw [hj, ρ.N_eq]
    exact ρ.n_odd.pow.mul ρ.n_odd.pow.pow
  let u : Over.mk (spMap i ≫ 𝟙 (Sp S.R)) ⟶ baseOver (Sp S.R) := Over.homMk (spMap i) (by simp)
  have hfr := frame_pull ρ.P ρ.rig u (ρ.fr_tors b)
  have ht := value_pull ρ.P u (ρ.th_val b)
  obtain ⟨s₁, s₂, U, h₁, hU, hs, h₃⟩ := isThetaConst_of_thG ρ.P ρ.rig ρ.rig_gen H
  let z : Sp K := (⊥ : PrimeSpectrum K)
  obtain ⟨ξ, hξ, e⟩ := GlobalTheory.ThetaCompare.normalised_root_stalk hL.globalFns ρ.P hk hy hfr ht _
    (Nat.cast_pow (S.r * S.N) 2) h₁ hU hs h₃ z
  have ec : u.left.appTop.hom (GlobalTheory.ZH.fn (⟨S.th b, S.th_mem b⟩ : S.R)) = GlobalTheory.ZH.fn (i ⟨S.th b, S.th_mem b⟩) :=
    (congrArg (fun q => q.hom (⟨S.th b, S.th_mem b⟩ : S.R)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom i))).symm
  rw [ec] at e
  let iso := Scheme.ΓSpecIso (CommRingCat.of K)
  let g : K →+* (Sp K).presheaf.stalk z := ((Sp K).presheaf.germ ⊤ z trivial).hom.comp iso.inv.hom
  have hg : Function.Injective g :=
    (germ_injective_of_isIntegral (Sp K) (U := ⊤) z trivial).comp (ConcreteCategory.bijective_of_isIso iso.inv).1
  have hgs : ∀ a : K, gs (𝟙 (Over.mk (spMap i ≫ 𝟙 (Sp S.R))).left) z ⊤ (GlobalTheory.ZH.fn a) = g a :=
    fun a => gs_eq _ z ⊤ trivial _
  apply hg
  rw [map_pow, map_pow, ← hgs, ← hgs, e, mul_pow, ← Units.val_pow_eq_pow_val, hξ, Units.val_one, _root_.one_mul]

end GlobalTheory
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UMin.FibMove

theorem lbIso_pull_comp {X Y Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) (f : Y ⟶ X) (g : Z ⟶ Y) :
    LBIso (L.pull (g ≫ f)) ((L.pull f).pull g) :=
  LBIso.chartPull (RigidBundleGlue.chartPullComp L f g _ rfl) (chartPullId _)
    ⟨idIso _, idIso_isGen (pull_isLB (pull_isLB hL f) g)⟩

theorem polFib_move : ∀ (S S' : Scheme.{0}) (G : Over S) [GrpObj G] (L : LB G.left) (A : Over S') [GrpObj A] (L' : LB A.left) (f : S' ⟶ S) (φ : A.left ⟶ G.left), L.IsLB → L'.IsLB → IsGrpPullback A G f φ → LBIso L' (L.pull φ) → ∀ (g : ℕ) (R : Type) [CommRing R] (x : Sp R ⟶ S'), (PolFib A L' g x ↔ PolFib G L g (x ≫ f)) ∧ ∀ (R' : Type) [CommRing R'] (i : R →+* R'), PolFib A L' g x → PolFib A L' g (spMap i ≫ x) := by
  intro S S' G _ L A _ L' f φ hL hL' hφ hLL' g R _ x
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rintro ⟨P, α, hg, hα, hPL⟩
    refine ⟨P, α ≫ φ, hg, hα.comp hφ, ?_⟩
    exact LBIso.trans P.isLB (pull_isLB hL' α) (pull_isLB hL _) hPL
      (LBIso.trans (pull_isLB hL' α) (pull_isLB (pull_isLB hL φ) α) (pull_isLB hL _)
        (RigidBundleGlue.LBIso.pull hLL' α) (lbIso_pull_comp hL φ α).symm)
  · rintro ⟨P, β, hg, hβ, hPL⟩
    have w : β ≫ G.hom = P.A.hom ≫ (x ≫ f) := hβ.1.w
    let α : P.A.left ⟶ A.left := hφ.1.lift β (P.A.hom ≫ x) (by rw [w, Category.assoc])
    have e₁ : α ≫ φ = β := hφ.1.lift_fst _ _ _
    have e₂ : α ≫ A.hom = P.A.hom ≫ x := hφ.1.lift_snd _ _ _
    refine ⟨P, α, hg, IsGrpPullback.cancel hφ (hβ.congr rfl e₁.symm) e₂, ?_⟩
    have h1 : LBIso P.L (L.pull (α ≫ φ)) := by rw [e₁]; exact hPL
    exact LBIso.trans P.isLB (pull_isLB hL _) (pull_isLB hL' α) h1
      (LBIso.trans (pull_isLB hL _) (pull_isLB (pull_isLB hL φ) α) (pull_isLB hL' α)
        (lbIso_pull_comp hL φ α) (RigidBundleGlue.LBIso.pull hLL'.symm α))
  · rintro R' _ i ⟨P, α, hg, hα, hPL⟩
    obtain ⟨P', ψ, hg', hψ, hPL'⟩ := exists_isPolFibre polBaseChange_holds i P
    refine ⟨P', ψ ≫ α, hg'.trans hg, hψ.comp hα, ?_⟩
    exact LBIso.trans P'.isLB (pull_isLB P.isLB ψ) (pull_isLB hL' _) hPL'.symm
      (LBIso.trans (pull_isLB P.isLB ψ) (pull_isLB (pull_isLB hL' α) ψ) (pull_isLB hL' _)
        (RigidBundleGlue.LBIso.pull hPL ψ) (lbIso_pull_comp hL' α ψ).symm)

end GlobalTheory.UMin.FibMove
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin.ThPull
open GlobalTheory.ThetaPtMove

theorem thG_pull {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {L : LB G.left}
    {ρ : LB.Gen (L.pull (eSec G))} (hL : L.IsLB) (hρ : ρ.IsGen) {m : ℕ}
    {B T : Over S} (β : B ⟶ T) {θ : LB.Sec (LPow G L ((1 : ℕ) : ℤ) T)} {y : T ⟶ G} {c : Γ(T.left, ⊤)}
    (H : ThG G L ρ m θ y c) : ThG G L ρ m (VVRank.pullS G _ β θ) (β ≫ y) (β.left.appTop.hom c) := by
  have hp : IsGrpPullback G G (𝟙 _) (𝟙 G.left) :=
    @isGrpPullback_of_iso _ _ _ _ _ (Iso.refl G) (inferInstanceAs (IsMonHom (𝟙 G)))
  obtain ⟨w, hw⟩ : LBIso L (L.pull (𝟙 _)) :=
    (GlobalTheory.PolBaseChange.lbIso_refl hL).chartPull (chartPullId _) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ _ _ rfl)
  obtain ⟨ρ', -, hr⟩ := exists_rigidificationPullbackCompatibleIso hp hw hL hL hρ
  have hτ : β.left ≫ T.hom = B.hom ≫ 𝟙 S := by rw [Over.w, Category.comp_id]
  have hσ : 𝟙 B.left ≫ B.hom = B.hom ≫ 𝟙 S := by simp
  obtain ⟨t, ht⟩ := exists_secRel hp β.left hτ hw hL hL θ
  have hu : (β ≫ y) ^ (m ^ 2) = 1 := by rw [← MonObj.comp_pow, H.1, MonObj.comp_one]
  have hrel := secRel_smul hp β.left hτ (𝟙 B.left) hσ β (Category.id_comp _) ht
    (th' := VVRank.pullS G _ β θ) (c := 1) (one_smul _ _).symm
  have q := ThG.smul (th' := SecM.toSec G ((𝟙 B.left : B.left ⟶ B.left).appTop.hom 1 • SecM.ofSec G t)) hL rfl
    (ThG.move hp β.left hτ hw hL hL hr (x := β ≫ y) (by simp) hu ht H)
  have q' := ThG.up hp (𝟙 B.left) hσ hw hL hL hr (x₀ := β ≫ y) (by simp) hu hrel q
  simpa using q'

theorem thList_pull : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (m N : ℕ) (K K' : Type) [Field K] [Field K'] (i : K →+* K') (x : Sp K ⟶ S) (θ : SecAt G L x) (pt : Fin N → (Over.mk x ⟶ G)) (c : Fin N → K), ThList G L ρ m x θ pt c → ∃ pt' : Fin N → (Over.mk (spMap i ≫ x) ⟶ G), (∀ a, (pt' a).left = spMap i ≫ (pt a).left) ∧ ThList G L ρ m (spMap i ≫ x) (SecAt.pull G L θ i) pt' (fun a => i (c a)) := by
  intro S G _ _ L ρ hL hρ m N K K' _ _ i x θ pt c H
  let β : Over.mk (spMap i ≫ x) ⟶ Over.mk x := Over.homMk (spMap i) rfl
  have hβ : β.left = spMap i := Over.homMk_left _ _
  refine ⟨fun a => β ≫ pt a, fun a => by simp only [Over.comp_left, hβ], fun a b h => H.1 (TorsionFieldExt.comp_injective β _ h), fun a => ?_,
    fun F _ _ k => ?_⟩
  · have q := thG_pull hL hρ β (H.2.1 a)
    have e : β.left.appTop.hom (GlobalTheory.ZH.fn (c a)) = GlobalTheory.ZH.fn (i (c a)) :=
      (congrArg (fun q => q.hom (c a)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom i))).symm
    rw [e] at q
    exact q
  · have e : spMap k ≫ spMap i ≫ x = spMap (k.comp i) ≫ x := by
      rw [ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap_comp, Category.assoc]
    rw [e]
    intro p hp
    obtain ⟨a, ha⟩ := H.2.2 F (k.comp i) p hp
    refine ⟨a, ?_⟩
    rw [ha, ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap_comp, Category.assoc, Over.comp_left, hβ, Category.assoc]

end GlobalTheory.UMin.ThPull
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin

theorem thG_unique_of_polFib : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (g m : ℕ) (R : Type) [CommRing R] [IsNoetherianRing R] (x : Sp R ⟶ S) (K : Type) [Field K] (i : R →+* K), Odd m → IsUnit (m : R) → PolFib G L g x → ∀ (th : SecAt G L (spMap i ≫ x)) (pt : Over.mk (spMap i ≫ x) ⟶ G) (c c' : K), ThG G L ρ m th pt (fn c) → ThG G L ρ m th pt (fn c') → c = c' := by
  intro S G _ _ L ρ hL hρ g m R _ _ x K _ i hm hu hP th pt c c' H H'
  obtain ⟨P, α, -, hp, w, hw⟩ := hP
  obtain ⟨ρ₁, -, hr⟩ := GlobalTheory.Ex.OneGen.exists_rigidificationPullbackCompatibleIso hp hw hL P.isLB hρ
  let T : Over (Sp R) := Over.mk (spMap i)
  let T₀ : Over S := Over.mk (spMap i ≫ x)
  have hτ : 𝟙 (Sp K) ≫ T₀.hom = T.hom ≫ x := Category.id_comp _
  obtain ⟨th₁, hth⟩ := GlobalTheory.ThetaPtMove.exists_secRel hp (T := T) (T₀ := T₀) (𝟙 _) hτ hw hL P.isLB th
  have hsq : pt.left ≫ G.hom = spMap i ≫ x := Over.w pt
  let x₁ : T ⟶ P.A := Over.homMk (hp.1.lift pt.left (spMap i) hsq) (hp.1.lift_snd _ _ _)
  have hx : 𝟙 (Sp K) ≫ pt.left = x₁.left ≫ α := by
    rw [Category.id_comp]; exact (hp.1.lift_fst _ _ _).symm
  have hn : x₁ ^ (m ^ 2) = 1 := by
    have h1 := GlobalTheory.ThetaPtMove.over_pow hp (T := T) (T₀ := T₀) (𝟙 _) hτ hx (m ^ 2)
    rw [H.1] at h1
    have h2 := GlobalTheory.ThetaPtMove.over_one hp (T := T) (T₀ := T₀) (𝟙 _) hτ
    exact Over.OverMorphism.ext (hp.1.hom_ext (h1.symm.trans h2) ((Over.w _).trans (Over.w _).symm))
  have hu' : IsUnit ((m ^ 2 : ℕ) : Γ(Sp R, ⊤)) := by
    rw [Nat.cast_pow, ← map_natCast (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom m, ← map_pow]
    exact (hu.pow 2).map _
  have m1 : ThG P.A P.L ρ₁ m th₁ x₁ ((𝟙 (Sp K) : Sp K ⟶ Sp K).appTop.hom (fn c)) :=
    ThG.move (T := T) (T₀ := T₀) hp (𝟙 _) hτ hw hL P.isLB hr hx hn hth H
  have m2 : ThG P.A P.L ρ₁ m th₁ x₁ ((𝟙 (Sp K) : Sp K ⟶ Sp K).appTop.hom (fn c')) :=
    ThG.move (T := T) (T₀ := T₀) hp (𝟙 _) hτ hw hL P.isLB hr hx hn hth H'
  have e := ThG.unique (T := T) abelianSchemeLaws_all.1 P hm hu' m1 m2
  have e2 := congrArg (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom e
  simpa using e2

end GlobalTheory.UMin
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Ex GlobalTheory.ThetaPtMove GlobalTheory.ConstFam

noncomputable section
namespace GlobalTheory.UMin

theorem thG_smul_iff : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (g m : ℕ) (K : Type) [Field K] (x : Sp K ⟶ S) (θ θ' : SecAt G L x) (p : Over.mk x ⟶ G) (a c c' : K), Odd m → (m : K) ≠ 0 → PolFib G L g x → SecM.ofSec G θ' = @id Γ((Over.mk x).left, ⊤) (GlobalTheory.ZH.fn a) • SecM.ofSec G θ → ThG G L ρ m θ p (GlobalTheory.ZH.fn c) → (ThG G L ρ m θ' p (GlobalTheory.ZH.fn c') ↔ c' = a * c) := by
  intro S G _ _ L ρ hL hρ g m K _ x θ θ' p a c c' hm hmK hpol hθ H
  obtain ⟨P, φ, -, hp, w, hw⟩ := hpol
  have hL₁ := P.isLB
  have := P.isAb.comm
  obtain ⟨ρ', -, hr⟩ := exists_rigidificationPullbackCompatibleIso hp hw hL hL₁ hρ
  have hfn : ∀ u v : K, GlobalTheory.ZH.fn (u * v) = GlobalTheory.ZH.fn u * GlobalTheory.ZH.fn v := fun u v => map_mul _ u v
  have Ha : ThG G L ρ m θ' p (GlobalTheory.ZH.fn (a * c)) := by
    rw [hfn]; exact ThG.smul hL hθ H
  refine ⟨fun H' => ?_, fun h => h ▸ Ha⟩
  let τ : (baseOver (Sp K)).left ⟶ (Over.mk x).left := 𝟙 (Sp K)
  have hτ : τ ≫ (Over.mk x).hom = (baseOver (Sp K)).hom ≫ x := rfl
  obtain ⟨z, hz, hz'⟩ := exists_torsion_down hp τ hτ p H.1
  obtain ⟨t', ht'⟩ := exists_secRel hp τ hτ hw hL hL₁ θ'
  have hun : IsUnit ((m ^ 2 : ℕ) : Γ(Sp K, ⊤)) := by
    rw [← map_natCast (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom]
    exact (IsUnit.mk0 _ (by push_cast; exact pow_ne_zero _ hmK)).map _
  have q := ThG.unique abelianSchemeLaws_all.1 P hm hun (ThG.move hp τ hτ hw hL hL₁ hr hz hz' ht' H')
    (ThG.move hp τ hτ hw hL hL₁ hr hz hz' ht' Ha)
  have q' : GlobalTheory.ZH.fn c' = GlobalTheory.ZH.fn (a * c) := by simpa [τ] using q
  exact (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv.injective q'

end GlobalTheory.UMin
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep GlobalTheory.FieldPair

theorem _root_.GlobalTheory.T.rationalResidueField_closedPoint_projectiveComplex : ∀ (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp ℂ), IsProjOver p → ∀ x : X,
    IsClosed ({x} : Set X) → RatRes (Cartier.constFn p) (locRing x) := by
  first | exact @GlobalTheory.FieldPair.ratRes_locRing_of_isClosed_of_isProjOver | exact GlobalTheory.FieldPair.ratRes_locRing_of_isClosed_of_isProjOver | (intros; apply GlobalTheory.FieldPair.ratRes_locRing_of_isClosed_of_isProjOver <;> assumption)
end
