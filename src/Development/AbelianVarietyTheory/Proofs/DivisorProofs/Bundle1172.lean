module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsFrameOfForallExists
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1135
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle677
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle828
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1125
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1136
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1156
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1146
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaxSlopeExtendedLatticeGaloisLe
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1138
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1139
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle029
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle032
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorusStableGoodOpenOfWeightUnits
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle970
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1100
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1144
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle411
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle034

@[expose] public section

section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry GlobalTheory.NeronCurve GlobalTheory.SS GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TorusPart

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TorusCot

open GlobalTheory.LB (resG_resG resG_self)
open GlobalTheory.Twist (resM resM_resM resM_self app_resM)
open GlobalTheory.QCoh (pullbackSections)
open GlobalTheory.DualPull (appLE_resG resG_appLE)
open GlobalTheory.Conormal GlobalTheory.SS.TorusSlice

theorem isFrame_append {S : Scheme.{0}} {F F₁ F₂ : S.Modules} {p₁ : F₁ ⟶ F} {p₂ : F₂ ⟶ F} {i₁ : F ⟶ F₁}
    {i₂ : F ⟶ F₂} (h : i₁ ≫ p₁ + i₂ ≫ p₂ = 𝟙 _) (h₁ : p₁ ≫ i₁ = 𝟙 _) (h₂ : p₂ ≫ i₂ = 𝟙 _) (h₃ : p₁ ≫ i₂ = 0)
    (h₄ : p₂ ≫ i₁ = 0) {U : S.Opens} {n m : ℕ} {e₁ : Fin n → Γ(F₁, U)} {e₂ : Fin m → Γ(F₂, U)}
    (he₁ : IsFrame e₁) (he₂ : IsFrame e₂) :
    IsFrame (Fin.append (fun i => p₁.app U (e₁ i)) fun j => p₂.app U (e₂ j)) := by
  let ψ (V : S.Opens) : (Γ(F₁, V) × Γ(F₂, V)) ≃ₗ[Γ(S, V)] Γ(F, V) :=
    LinearEquiv.ofBijective ((QCoh.appLinear p₁ V).coprod (QCoh.appLinear p₂ V)) ⟨by
      set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
      rintro ⟨a, b⟩ hab
      change p₁.app V a + p₂.app V b = 0 at hab
      have a₁ := congrArg (i₁.app V) hab
      have a₂ := congrArg (i₂.app V) hab
      rw [map_add (f := _), map_zero, QCoh.app_app, QCoh.app_app] at a₁ a₂
      rw [h₁, h₄] at a₁
      rw [h₃, h₂] at a₂
      ext
      · simpa using a₁
      · simpa using a₂, fun c => ⟨(i₁.app V c, i₂.app V c), congr(($h).app V c)⟩⟩
  refine isFrame_of_basis (fun V k => (((he₁.basis k).prod (he₂.basis k)).map (ψ V)).reindex finSumFinEquiv)
    fun V k i => ?_
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  rw [Module.Basis.reindex_apply, Equiv.symm_apply_apply, Module.Basis.map_apply]
  rcases i with i | i
  · change p₁.app V _ + p₂.app V _ = _
    simp [app_resM]
  · change p₁.app V _ + p₂.app V _ = _
    simp [app_resM]

section Geo

variable {S : Scheme.{0}} {T G B Y : Over S} [GrpObj T] [GrpObj G] [GrpObj B] {u : T ⟶ G} {q : G ⟶ B}
  [IsMonHom u] {j : Y ⟶ G} {σ : Y ⟶ T}

end Geo

end GlobalTheory.TorusCot

namespace GlobalTheory.TorusPart

open GlobalTheory.TorusCot GlobalTheory.QCoh

end GlobalTheory.TorusPart
end
end

section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

theorem GlobalTheory.noSection_H1_bound_riemann_roch : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → ∀ (d : ℕ) (L : LB X), L.IsLB → ∀ (F : X.Modules) [IsFiniteQC F], suppDim F ≤ (d + 1 : ℕ) → (∀ m : ℕ, 1 ≤ m → hdim k (twist F (lbPow L m)) 0 = 0) → 0 ≤ interNum k F (fun _ : Fin (d + 1) => L) → (∀ i, 2 ≤ i → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist F (lbPow L m)) i ≤ C * ((d + 1) * (m + 1) ^ d))) → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist F (lbPow L m)) 1 ≤ C * ((d + 1) * (m + 1) ^ d)) := by
  intro k _ _ X _ hX d L hL F _ hF h0 hI hi
  obtain ⟨C2, hC2⟩ := GlobalTheory.T.abs_factorial_mul_eulerChar_twist_pow_sub_le k X hX (d+1) F hF L hL
  obtain ⟨C1, hC1⟩ := GlobalTheory.T.euler_char_h0_h1_bound_higher k X hX (d+1) L hL F hF (fun m => (d+1)*(m+1)^d) hi
  refine ⟨C1 + C2 + hdim k (twist F (lbPow L 0)) 1, fun m => ?_⟩
  have he1 : 1 ≤ (d+1)*(m+1)^d := Nat.one_le_iff_ne_zero.mpr (by positivity)
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · calc hdim k (twist F (lbPow L 0)) 1 ≤ hdim k (twist F (lbPow L 0)) 1 * ((d+1)*(0+1)^d) :=
          Nat.le_mul_of_pos_right _ he1
      _ ≤ (C1 + C2 + hdim k (twist F (lbPow L 0)) 1) * ((d+1)*(0+1)^d) :=
          Nat.mul_le_mul_right _ (by omega)
  · have a1 := hC1 m
    have a2 := hC2 m
    rw [h0 m hm] at a1
    simp only [Nat.add_sub_cancel] at a2
    have hfac : (1 : ℤ) ≤ ((d+1).factorial : ℤ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hImp : 0 ≤ interNum k F (fun _ : Fin (d + 1) => L) * (m : ℤ)^(d+1) := mul_nonneg hI (by positivity)
    have hE : (((d+1)*(m+1)^d : ℕ) : ℤ) = ((d+1 : ℕ) : ℤ) * ((m : ℤ) + 1) ^ d := by push_cast; ring
    rw [← hE] at a2
    have hEpos : (1 : ℤ) ≤ (((d+1)*(m+1)^d : ℕ) : ℤ) := by exact_mod_cast he1
    suffices h : (hdim k (twist F (lbPow L m)) 1 : ℤ) ≤
        ((C1 + C2 + hdim k (twist F (lbPow L 0)) 1 : ℕ) : ℤ) * (((d+1)*(m+1)^d : ℕ) : ℤ) by
      exact_mod_cast h
    generalize (((d+1)*(m+1)^d : ℕ) : ℤ) = E at a1 a2 hEpos ⊢
    generalize chi k (twist F (lbPow L m)) = c at a1 a2
    generalize interNum k F (fun _ : Fin (d + 1) => L) * (m : ℤ)^(d+1) = I at a2 hImp
    generalize (((d+1).factorial : ℕ) : ℤ) = f at a2 hfac
    generalize (hdim k (twist F (lbPow L m)) 1 : ℤ) = H at a1 ⊢
    push_cast
    have hh0 : (0 : ℤ) ≤ (hdim k (twist F (lbPow L 0)) 1 : ℤ) := by positivity
    generalize (hdim k (twist F (lbPow L 0)) 1 : ℤ) = h00 at hh0 ⊢
    have hC1' : (0:ℤ) ≤ C1 := by positivity
    have hC2' : (0:ℤ) ≤ C2 := by positivity
    rw [abs_le] at a1 a2
    simp only [CharP.cast_eq_zero, sub_zero] at a1
    have hc : -c ≤ (C2 : ℤ) * E := by
      rcases le_or_gt 0 c with hc | hc
      · nlinarith
      · nlinarith
    nlinarith
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.EtC.OneCoh

theorem dies_on_etale_with_point (q : ℕ) [NeZero q] (B : Type) [CommRing B] (hq : IsUnit (q : B))
    (P : Ideal B) [P.IsMaximal] (hsep : IsSepClosed (IsLocalRing.ResidueField (Localization.AtPrime P)))
    (m i : ℤ) (hm : 0 < m) (y : Ht q (sp B) m i) :
    ∃ (D : Type) (_ : CommRing D) (_ : Algebra B D) (_ : Algebra.Etale B D) (Q : Ideal D),
      Q.IsPrime ∧ Q.comap (algebraMap B D) = P ∧ (∀ d : D, ∃ b : B, d - algebraMap B D b ∈ Q) ∧
      pull _ (spMap (algebraMap B D)) _ _ y = 0 := by
  obtain ⟨O, _, _, hSH, hInd, hO⟩ := GlobalTheory.T.exists_strictHenselization_at_maximal B P hsep
  have hsub : Subsingleton (Ht q (sp O) m i) := GlobalTheory.EtC.b2 (ZMod q) O hSH (tw q i) m hm
  have h0 : pull _ (spMap (algebraMap B O)) _ _ y = 0 := Subsingleton.elim _ _
  obtain ⟨D, _, _, _, φ, hD⟩ := GlobalTheory.T.vanishes_on_etale_neighbourhood q B O hq hInd m i y h0
  obtain ⟨hH, -⟩ := hSH
  haveI : IsLocalRing O := hH.toIsLocalRing
  obtain ⟨hP, hres⟩ := hO (IsLocalRing.maximalIdeal O) inferInstance
  refine ⟨D, inferInstance, inferInstance, inferInstance, (IsLocalRing.maximalIdeal O).comap φ, ?_, ?_, ?_, hD⟩
  · exact Ideal.comap_isPrime _ _
  · rw [← hP]
    ext b
    rw [Ideal.mem_comap, Ideal.mem_comap, Ideal.mem_comap, AlgHom.commutes]
  · intro d
    obtain ⟨b, hb⟩ := hres (φ d)
    refine ⟨b, ?_⟩
    rw [Ideal.mem_comap, map_sub, AlgHom.commutes]
    exact hb

end GlobalTheory.EtC.OneCoh

theorem GlobalTheory.EtC.oneCoh_main : ∀ (q : ℕ) [NeZero q] (B : Type) [CommRing B], IsUnit (q : B) → ∀ (P : Ideal B) [P.IsMaximal], IsSepClosed (IsLocalRing.ResidueField (Localization.AtPrime P)) → ∀ (m i : ℤ), 0 < m → ∀ y : Ht q (sp B) m i, ∃ (D : Type) (_ : CommRing D) (_ : Algebra B D) (_ : Algebra.Etale B D) (Q : Ideal D), Q.IsPrime ∧ Q.comap (algebraMap B D) = P ∧ (∀ d : D, ∃ b : B, d - algebraMap B D b ∈ Q) ∧ pull _ (spMap (algebraMap B D)) _ _ y = 0 :=
  fun q _ B _ hq P _ hsep m i hm y => GlobalTheory.EtC.OneCoh.dies_on_etale_with_point q B hq P hsep m i hm y
end

section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal Neutral.B1
open scoped nonZeroDivisors

theorem _root_.GlobalTheory.T.exists_cmCurve_torsionTransport_secondPeriod : ∀ {K : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K], Module.finrank ℚ K = 2 → ∀ (ι : K →+* ℂ) (Λ₀ : PeriodPair) (Ω₀ : ℂ), GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.IsLatOf ι 1 Λ₀ → Ω₀ ≠ 0 → letI : Algebra K ℂ := ι.toAlgebra; ∃ (X : WeierstrassCurve ℂ) (_ : X.IsElliptic) (ξ : (ℂ ⧸ GlobalTheory.EllipticCM.idealSub (1 : FractionalIdeal (𝓞 K)⁰ K)) ≃+ X.toAffine.Point), GlobalTheory.EllipticCM.IsAnalyticIso ξ ∧ ∀ (σ : ℂ ≃ₐ[K] ℂ) (t : (Af K)ˣ), GlobalTheory.EllipticCM.Transports σ t one_ne_zero ξ → ∃ (Λ₁ : PeriodPair) (Ω₁ : ℂ), TorsTransport ι σ.toRingEquiv t Λ₀ Λ₁ Ω₀ Ω₁ := by
  first | exact @GlobalTheory.LatVal.CurveTransport.exists_curve_torsTransport | exact GlobalTheory.LatVal.CurveTransport.exists_curve_torsTransport | (intros; apply GlobalTheory.LatVal.CurveTransport.exists_curve_torsTransport <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.VB GlobalTheory.TwoSeq GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PDivGroup

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.BadPt

section Linear

variable {R K : Type} [CommRing R] [Field K] [Algebra R K] {H : Type*} [AddCommGroup H] [Module K H] [Module R H]
  [IsScalarTower R K H]

end Linear

section Sheaf

variable {O : Type} [CommRing O] {X T : Scheme.{0}} {R K : Type} [CommRing R] [Field K] [Algebra R K]
  {f : Sp R ⟶ X} {f₀ : T ⟶ X} {ξ : Sp K ⟶ T}

def resSec (w : spMap (algebraMap R K) ≫ f = ξ ≫ f₀) (A : X.Modules) (t : Γ((Scheme.Modules.pullback f).obj A, ⊤)) :
    Γ((Scheme.Modules.pullback ξ).obj ((Scheme.Modules.pullback f₀).obj A), ⊤) :=
  ((sqIso w).hom.app A).app ⊤ (QCoh.pullbackSections (spMap (algebraMap R K)) _ (V := ⊤) le_top t)


variable (w : spMap (algebraMap R K) ≫ f = ξ ≫ f₀) {A B A' B' : X.Modules} {D : T.Modules}
  (a : (Scheme.Modules.pullback f₀).obj A ⟶ D) (b : D ⟶ (Scheme.Modules.pullback f₀).obj B)

def Reads {H : Type*} [AddCommGroup H] [Module K H] [Module R H] [IsScalarTower R K H]
    (E : Γ((Scheme.Modules.pullback ξ).obj D, ⊤) ≃+ H) (β : LinearMap.BilinForm K H) (F : Submodule K H)
    (N : Submodule R H) : Prop :=
  (∀ s, ((Scheme.Modules.pullback ξ).map b).app ⊤ s = 0 ↔ E s ∈ F) ∧
    (∀ s, E s ∈ N ↔ ∃ t, s = ((Scheme.Modules.pullback ξ).map a).app ⊤ (resSec w A t)) ∧
    (∀ s, E s ∈ β.dualSubmodule N ↔ ∃ t, ((Scheme.Modules.pullback ξ).map b).app ⊤ s = resSec w B t) ∧
    Function.Surjective (((Scheme.Modules.pullback ξ).map b).app ⊤)


variable {α : O →+* End A} {β : O →+* End B} {α' : O →+* End A'} {β' : O →+* End B'} {r : ℕ}

end Sheaf

section Forms

variable {R K : Type} [CommRing R] [Field K] [Algebra R K]

end Forms

section Tower

variable {p : ℕ} {R K : Type} [CommRing R] [CommRing K] [Algebra R K]

structure FinTower (Γ : PDivGroup p R) (G : Over (Sp R)) [GrpObj G] : Type where

  y : ∀ n, SpAlg R (Γ.A n) ⟶ G

  mul : ∀ (n : ℕ) (B : Type) [CommRing B] [Algebra R B] (φ ψ : WithConv (Γ.A n →ₐ[R] B)),
    spOver (φ * ψ).ofConv ≫ y n = (spOver φ.ofConv ≫ y n) * (spOver ψ.ofConv ≫ y n)

  inj : ∀ (n : ℕ) (B : Type) [CommRing B] [Algebra R B] (φ ψ : Γ.A n →ₐ[R] B),
    spOver φ ≫ y n = spOver ψ ≫ y n → φ = ψ

  surj : ∀ (n : ℕ) (B : Type) [CommRing B] [Algebra R B] [Module.Finite R B] (z : SpAlg R B ⟶ G),
    z ^ p ^ n = 1 → ∃ φ : Γ.A n →ₐ[R] B, spOver φ ≫ y n = z

  res : ∀ n, spOver (Γ.res n : Γ.A (n + 1) →ₐ[R] Γ.A n) ≫ y (n + 1) = y n

def FinTower.ofTower {Γ : PDivGroup p R} {G : Over (Sp R)} [GrpObj G] (t : Γ.TorsionTower G) : FinTower Γ G :=
  ⟨t.y, t.mul, t.inj, fun n B _ _ _ => t.surj n B, t.res⟩

def IsWeilHom {𝒜 ℬ : PDivGroup p R} {A B : Over (Sp R)} [GrpObj A] [GrpObj B] (t : 𝒜.TorsionTower A)
    (u : ℬ.TorsionTower B) (P : LB (A ⊗ B).left) (w : 𝒜 ⟶ ℬ.dual) : Prop :=
  ∀ n, ∃ U : (𝒜.A n ⊗[R] ℬ.A n)ˣ,
    Out.WeilIs (A ⊗ B) P ((p ^ n : ℕ) : ℤ) (T := SpAlg R (𝒜.A n ⊗[R] ℬ.A n))
      (CartesianMonoidalCategory.lift
        (spOver (Algebra.TensorProduct.includeLeft : 𝒜.A n →ₐ[R] 𝒜.A n ⊗[R] ℬ.A n) ≫ t.y n) 1)
      (CartesianMonoidalCategory.lift 1
        (spOver (Algebra.TensorProduct.includeRight : ℬ.A n →ₐ[R] 𝒜.A n ⊗[R] ℬ.A n) ≫ u.y n))
      (unitOn U) ∧
    ∀ χ : CartierDual R (ℬ.A n), w.app n χ = TensorProduct.rid R _ (χ.ofConv.lTensor _ U.val)

variable [Fact p.Prime] {Γ : PDivGroup p R} {𝒜 : PDivGroup p K}

variable [Module R 𝒜.RigExt] [IsScalarTower R K 𝒜.RigExt]

end Tower

end GlobalTheory.BadPt
end
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PDivGroup

theorem exists_lieCorr_of_pow_eq_zero : ∀ (p : ℕ) [Fact p.Prime]  (R : Type) [CommRing R] (N : ℕ), (p : R) ^ N = 0 → ∀ (A : Over (Sp R)) [GrpObj A] (G : PDivGroup p R) (t : G.TorsionTower A) (x : G.Lie), ∃ v : epsR R ⟶ A, t.LieCorr x v := by
  intro p _ R _ N hN A _ G t x
  have hb := omegaLevel_bijective_of_pow_eq_zero p R N hN G N le_rfl
  let e := LinearEquiv.ofBijective (G.omegaLevel N) hb
  let D : G.A N →ₗ[R] R := x ∘ₗ e.symm.toLinearMap ∘ₗ AugCot.d (Bialgebra.counitAlgHom R (G.A N))
  have hD : ∀ a b : G.A N, D (a * b) = Coalgebra.counit (R := R) a * D b + Coalgebra.counit (R := R) b * D a := by
    intro a b
    simp only [D, LinearMap.comp_apply, AugCot.d_mul, map_add (f := _), map_smul, smul_eq_mul]
    rfl
  have hD1 : D 1 = 0 := by simp [D]
  let ψ₀ : G.A N →ₐ[R] DualNumber R :=
    AlgHom.ofLinearMap
      (Algebra.linearMap R (DualNumber R) ∘ₗ Coalgebra.counit + TrivSqZeroExt.inrHom R R ∘ₗ D)
      (by simp [hD1])
      (fun a b ↦ by
        ext
        · simp [TrivSqZeroExt.algebraMap_eq_inl]
        · simp [TrivSqZeroExt.algebraMap_eq_inl, hD, mul_comm])
  have hfst : ∀ a, (ψ₀ a).fst = Coalgebra.counit (R := R) a := fun a ↦ by
    simp [ψ₀, TrivSqZeroExt.algebraMap_eq_inl]
  have hsnd : ∀ a, (ψ₀ a).snd = D a := fun a ↦ by
    simp [ψ₀, TrivSqZeroExt.algebraMap_eq_inl]
  let v : epsR R ⟶ A := spOver ψ₀ ≫ t.y N
  have hv : IsTangent v := by
    have h := (t.eq_one_iff N ((TrivSqZeroExt.fstHom R R R).comp ψ₀)).2 hfst
    rw [← spOver_comp, Category.assoc] at h
    refine (congrArg Over.Hom.left h).trans ?_
    rw [Hom.one_def, Over.comp_left, Over.toUnit_left]
    exact (congrArg (· ≫ η[A].left) (Cris.spMap_id R)).trans (Category.id_comp _)
  haveI : IsAdicComplete (Ideal.span {(p : R)}) R :=
    isAdicComplete_span_natCast_of_isNilpotent p R ⟨N, hN⟩
  obtain ⟨x', hx', -⟩ := t.existsUnique_lieCorr hv
  refine ⟨v, ?_⟩
  suffices hx : x' = x by rw [← hx]; exact hx'
  refine LinearMap.ext fun w ↦ ?_
  have k := (t.lieCorr_iff hv x').1 hx' N w
  obtain ⟨a, ha⟩ := AugCot.d_surjective _ (w.1 N)
  have ep : t.tanPt hv N = (epsTo R (ModPow p R N)).comp ψ₀ :=
    t.inj N _ _ _ (by rw [t.tanPt_y hv N, ← spOver_comp, Category.assoc])
  have ew : e.symm (w.1 N) = w := e.symm_apply_eq.2 rfl
  rw [← ha, TorsionTower.tanDer_d, ep, AlgHom.comp_apply, snd_epsTo, hsnd] at k
  have k2 : D a = x w := by
    simp only [D, LinearMap.comp_apply]
    change x (e.symm (AugCot.d (Bialgebra.counitAlgHom R (G.A N)) a)) = x w
    rw [ha, ew]
  rw [k2, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq, hN, Ideal.mem_span_singleton,
    zero_dvd_iff, sub_eq_zero] at k
  exact k

end GlobalTheory.PDivGroup
end
end

section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

noncomputable section

namespace GlobalTheory.FlatChar

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}


open Classical in
theorem exOf_flatWt_some (τ : Psi H) (σ : E →+* ℂ) (i : Fin (Dw.mult σ)) :
    exOf Dw (flatWt Dw τ) 0 (some ⟨σ, i⟩) = if σ = τ.1 then -1 else if σ = conjEmb τ.1 then 1 else 0 := by
  classical
  show (wtOf Dw (flatWt Dw τ) 0).1 (σ, (i : ℕ)) = _
  have hi := i.2
  by_cases h : σ (H.rt : E) = H.rt0
  · have hp : (i : ℕ) < Dw.p := by simpa [Datum.mult, h] using hi
    have e0 := wtOf_big (flatWt Dw τ) 0 ⟨σ, h⟩ i hp
    refine e0.trans ?_
    have hne : σ ≠ conjEmb τ.1 := fun e => conj_not_mem τ (e ▸ h)
    by_cases e : σ = τ.1
    · have : (⟨σ, h⟩ : Psi H) = τ := Subtype.ext e
      simp [flatWt, parWt, this, e]
    · have : (⟨σ, h⟩ : Psi H) ≠ τ := fun e' => e (congrArg Subtype.val e')
      simp [flatWt, parWt, this, e, hne]
  · have h' := conj_mem h
    have hq : (i : ℕ) < Dw.q := by simpa [Datum.mult, h] using hi
    have e0 := wtOf_small (flatWt Dw τ) 0 ⟨conjEmb σ, h'⟩ i hq
    simp only [GlobalTheory.AllWt.conjEmb_conjEmb] at e0
    refine e0.trans ?_
    have hne : σ ≠ τ.1 := fun e' => h (e' ▸ τ.2)
    have hiff : (⟨conjEmb σ, h'⟩ : Psi H) = τ ↔ σ = conjEmb τ.1 := by
      constructor
      · intro e'; rw [← congrArg Subtype.val e', GlobalTheory.AllWt.conjEmb_conjEmb]
      · intro e'; apply Subtype.ext; show conjEmb σ = τ.1; rw [e', GlobalTheory.AllWt.conjEmb_conjEmb]
    by_cases e : σ = conjEmb τ.1
    · have h2 := hiff.2 e
      rw [if_neg hne, if_pos e]
      simp only [flatWt, parWt, if_pos h2]
      norm_num
    · have : (⟨conjEmb σ, h'⟩ : Psi H) ≠ τ := fun e' => e (hiff.1 e')
      simp [flatWt, parWt, this, e, hne]

theorem flatWt_char (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (τ : Psi H) (S : Type) [Field S] (t : Ix Dw → Sˣ) :
    (((∏ i, t i ^ exOf Dw (flatWt Dw τ) 0 i : Sˣ)) : S) * ∏ i : Fin (Dw.mult τ.1), (t (some ⟨τ.1, i⟩) : S) =
      ∏ j : Fin (Dw.mult (conjEmb τ.1)), (t (some ⟨conjEmb τ.1, j⟩) : S) := by
  classical
  have hne : τ.1 ≠ conjEmb τ.1 := fun e => conj_not_mem τ (e ▸ τ.2)
  have key : (∏ i, t i ^ exOf Dw (flatWt Dw τ) 0 i) =
      (∏ i : Fin (Dw.mult τ.1), t (some ⟨τ.1, i⟩))⁻¹ * ∏ j : Fin (Dw.mult (conjEmb τ.1)), t (some ⟨conjEmb τ.1, j⟩) := by
    rw [Fintype.prod_option, Fintype.prod_sigma]
    have h0 : exOf Dw (flatWt Dw τ) 0 none = 0 := rfl
    rw [h0, zpow_zero, one_mul]
    rw [Fintype.prod_eq_mul τ.1 (conjEmb τ.1) hne ?_]
    · congr 1
      · rw [← Finset.prod_inv_distrib]
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [exOf_flatWt_some, if_pos rfl, zpow_neg_one]
      · refine Finset.prod_congr rfl fun i _ => ?_
        rw [exOf_flatWt_some, if_neg hne.symm, if_pos rfl, zpow_one]
    · rintro σ ⟨h1, h2⟩
      refine Finset.prod_eq_one fun i _ => ?_
      rw [exOf_flatWt_some, if_neg h1, if_neg h2, zpow_zero]
  rw [key, ← Units.coe_prod, ← Units.coe_prod, ← Units.val_mul]
  congr 1
  rw [mul_comm, mul_inv_cancel_left]

end GlobalTheory.FlatChar
end
end

section

open NumberField GlobalTheory.AllWt

theorem _root_.GlobalTheory.T.maxSlope_extendedLattice_galois_le : ∀ (K K' V V' : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] [Field K'] [NumberField K'] [Algebra K K'] [IsGalois K K'] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K' V'] [Module (𝓞 K') V'] [IsScalarTower (𝓞 K') K' V'] (N : (K →+* ℂ) → V → ℝ) (N' : (K' →+* ℂ) → V' → ℝ) (ι : V →ₛₗ[algebraMap K K'] V') (L : Submodule (𝓞 K) V), HasGram N → HasGram N' → (∀ σ x, N ((starRingEnd ℂ).comp σ) x = N σ x) → (∀ (n : ℕ) (b : Fin n → V), LinearIndependent K b → LinearIndependent K' (fun k => ι (b k))) → L.FG → L ≠ ⊥ → (∀ σ' x, N' σ' (ι x) = N (σ'.comp (algebraMap K K')) x) → slopeMax_sq N' (Submodule.span (𝓞 K') (ι '' (L : Set V))) ≤ slopeMax_sq N L := by
  first | exact @GlobalTheory.SlopeGal.slopeMax_sq_span_le | exact GlobalTheory.SlopeGal.slopeMax_sq_span_le | (intros; apply GlobalTheory.SlopeGal.slopeMax_sq_span_le <;> assumption)
end

section

open NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.heckeTj_cosets_finite_card_le : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (ϖ : w.adicCompletion E), Formalism.UG.IsUnifV E w ϖ → ∀ j ≤ n, {q : GL (Fin n) (w.adicCompletion E) ⧸ GlobalTheory.LFun.KGL w (n := n) | Formalism.UG.Tj ℂ n (Formalism.UG.Ov E w) ϖ j q.out ≠ 0}.Finite ∧ Nat.card {q : GL (Fin n) (w.adicCompletion E) ⧸ GlobalTheory.LFun.KGL w (n := n) // Formalism.UG.Tj ℂ n (Formalism.UG.Ov E w) ϖ j q.out ≠ 0} ≤ Formalism.UG.qV E w ^ (n * j) := by
  first | exact @GlobalTheory.TjCount.tj_cosets_finite_card_le | exact GlobalTheory.TjCount.tj_cosets_finite_card_le | (intros; apply GlobalTheory.TjCount.tj_cosets_finite_card_le <;> assumption)
end

section

open NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.heckeTn_scalar_uniformiser_single_translation : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V) (ϖ : w.adicCompletion E), Formalism.UG.IsUnifV E w ϖ → ∀ x ∈ GlobalTheory.PRep.fixed ρ (GlobalTheory.LFun.KGL w (n := n)), ∃ g, GlobalTheory.LFun.heckeVec ρ (GlobalTheory.LFun.KGL w (n := n)) (Formalism.UG.Tj ℂ n (Formalism.UG.Ov E w) ϖ n) x = ρ g x := by
  first | exact @GlobalTheory.LFun.tn_single | exact GlobalTheory.LFun.tn_single | (intros; apply GlobalTheory.LFun.tn_single <;> assumption)
end
