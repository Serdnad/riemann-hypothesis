module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SectionsGrowthBasicPropertiesAbelianVariety
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle002
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle003
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle121
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle026
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle081
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle075
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle130
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle156
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle109
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle116
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle124
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle157
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.ExistsGeneratorOfIsField
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle158
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.FlatIsoUnitGenerator
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle004

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ThetaClassical

theorem constFn_mul {X : Scheme.{0}} (f : X ⟶ Sp ℂ) (U : X.Opens) (a b : ℂ) :
    constFn f U (a * b) = constFn f U a * constFn f U b := by
  unfold constFn
  rw [map_mul, map_mul]

theorem constFn_one {X : Scheme.{0}} (f : X ⟶ Sp ℂ) (U : X.Opens) : constFn f U 1 = 1 := by
  unfold constFn
  rw [map_one, map_one]

theorem constFn_top (a : ℂ) :
    (⊤ : (Sp ℂ).Opens).ι.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom a) =
      constFn ((⊤ : (Sp ℂ).Opens).ι ≫ 𝟙 _) ⊤ a := by
  rw [Category.comp_id]
  exact congrArg (fun f : Γ(Sp ℂ, ⊤) ⟶ Γ((⊤ : (Sp ℂ).Opens).toScheme, (⊤ : (Sp ℂ).Opens).ι ⁻¹ᵁ ⊤) =>
    f.hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom a))
    (Scheme.Hom.appLE_eq_app (⊤ : (Sp ℂ).Opens).ι (U := ⊤)).symm

theorem isThetaPtOver (hL : Out.Laws) (hL2 : Out.Laws2) (hT : ThetaUnifAV) (P : Out.PolAV (Sp ℂ))
    (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ)
    (θ : (Fin P.g → ℂ) → ℂ) (N : ℕ) (T : Over (Sp ℂ)) [IsIso T.hom] (p : 𝟙_ (Over (Sp ℂ)) ⟶ T)
    {I : Type} (x : I → (T ⟶ P.A)) (l : I → u.Λ) (hN : Odd N) (hAH : u.IsAH Hm χ)
    (hθ : u.IsThetaFn Hm χ 1 θ) (h0 : θ ≠ 0)
    (hx : ∀ i, p ≫ x i = u.ex (((N : ℂ) ^ 2)⁻¹ • (l i : Fin P.g → ℂ)))
    (hU : ∀ i, ∃ U : Out.ThetaGrp P.A P.L ((N : ℤ) ^ 2) T,
      Out.SymLift P.A P.L ((N : ℤ) ^ 2) (N ^ 2) (x i) U) :
    Out.IsThetaPtOver P N x (fun i => constFn T.hom ⊤
      (χ (l i) * Complex.exp (-(Real.pi / 2 / (N : ℂ) ^ 2) * hermForm Hm (l i) (l i)) *
        θ ((N : ℂ)⁻¹ • (l i : Fin P.g → ℂ)))) := by
  have hC := GlobalTheory.Moduli.cube_of_isLB
  obtain ⟨th, hgen, hth⟩ := GlobalTheory.exists_isGenSec_of_isThetaFn hL hL2 hC hT P u Hm χ θ T p hAH hθ h0
  obtain ⟨s1, α, c, hc, hα, htw, hs1⟩ := GlobalTheory.exists_twistPull_mul_fn hL hL2 hC hT P u Hm χ N θ T p th hAH hN hth
  obtain ⟨τ, hτ, hval⟩ := GlobalTheory.OriginValue.exists_gen_isValueAt_origin P u ((N : ℤ) ^ 2) T p
  choose U hU using hU
  choose s2 hs2 using fun i => GlobalTheory.ThetaPtExist.exists_isTwistPull P.isLB (Out.translT P.A (U i).pt)
    (Out.translPt P.A (U i).pt) (lift_snd _ _) ((N : ℤ) ^ 2) ((N : ℤ) ^ 2) (U i).φ (U i).isGen s1
  have hact := fun i => GlobalTheory.T.symmetricLift_torsionPoint_action_on_theta hL hL2 hC hT P u Hm χ N (l i) (fun z => c * θ ((N : ℂ) • z)) T p
    (x i) (U i) s1 (s2 i) hAH hN (hx i) (hU i) (hs2 i) hs1
  have hv := fun i => hval (s2 i) (fun z => χ (l i) * Complex.exp (-(Real.pi / 2 / (N : ℂ) ^ 2) *
    hermForm Hm (l i) (l i) - Real.pi * hermForm Hm z (l i)) *
      (c * θ ((N : ℂ) • (z + ((N : ℂ) ^ 2)⁻¹ • (l i : Fin P.g → ℂ))))) (hact i)
  have hcu : IsUnit (constFn T.hom ⊤ c⁻¹) :=
    IsUnit.of_mul_eq_one (constFn T.hom ⊤ c) (by rw [← constFn_mul, inv_mul_cancel₀ hc, constFn_one])
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast hN.pos.ne'
  refine ⟨th, s1, α, τ, U, s2, _, hcu.unit, hgen, hα, hτ, htw, hU, hs2, hv, fun i => ?_⟩
  refine Eq.trans (congrArg (constFn T.hom ⊤) ?_) (constFn_mul T.hom ⊤ c⁻¹ _)
  have e1 : hermForm Hm 0 (l i) = 0 := by simp [hermForm]
  have e2 : (N : ℂ) • (0 + ((N : ℂ) ^ 2)⁻¹ • (l i : Fin P.g → ℂ)) = (N : ℂ)⁻¹ • (l i : Fin P.g → ℂ) := by
    rw [zero_add, smul_smul]
    congr 1
    field_simp
  simp only [e1, e2, mul_zero, sub_zero]
  field_simp

theorem exists_symLift (hL : Out.Laws) (P : Out.PolAV (Sp ℂ)) (n : ℕ) (k : ℤ) (hk : k = n) (hn : Odd n)
    (x : Out.baseOver (Sp ℂ) ⟶ P.A) (hx : x ^ n = 1) :
    ∃ U : Out.ThetaGrp P.A P.L k (Out.overRes (T := Out.baseOver (Sp ℂ)) ⊤),
      Out.SymLift P.A P.L k n (Out.overResι ⊤ ≫ x) U := by
  subst hk
  have hu : IsUnit (n : Γ(Sp ℂ, ⊤)) := by
    have h : IsUnit (n : ℂ) := IsUnit.mk0 _ (by exact_mod_cast hn.pos.ne')
    simpa using h.map (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
  obtain ⟨V, hV, U, hU⟩ := (hL.symLift (Sp ℂ) P n hn hu _ x hx).1 (default : PrimeSpectrum ℂ)
  obtain rfl : V = ⊤ := by
    refine top_le_iff.1 fun y _ => ?_
    have : y = (default : PrimeSpectrum ℂ) := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
    rw [this]
    exact hV
  exact ⟨U, hU⟩

theorem ex_zero {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g) :
    u.ex 0 = 1 := (u.ker 0).2 u.Λ.zero_mem

theorem ex_nsmul {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
    (z : Fin g → ℂ) (n : ℕ) : u.ex (n • z) = u.ex z ^ n := by
  induction n with
  | zero => rw [zero_smul, pow_zero, ex_zero]
  | succ n ih => rw [succ_nsmul, u.ex_add, ih, pow_succ]

theorem ex_sum {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
    {r : ℕ} (z : Fin r → Fin g → ℂ) (a : Fin r → ℕ) :
    u.ex (∑ i, a i • z i) = Out.linComb (fun i => u.ex (z i)) a := by
  induction r with
  | zero => simp [Out.linComb, ex_zero]
  | succ r ih =>
    rw [Fin.sum_univ_succ, u.ex_add, ih, ex_nsmul]
    simp [Out.linComb, List.ofFn_succ]

theorem hasTh_classical : Out.Laws → Out.Laws2 → ThetaUnifAV → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (em : o →+* ℂ) (t : TObj g (N' ^ 2) J b (spMap em)) (u : HolUnif t.A t.L g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ) (θ : (Fin g → ℂ) → ℂ) (lam : Fin (2 * g) → u.Λ), Odd N' → u.IsAH Hm χ → u.IsThetaFn Hm χ 1 θ → θ ≠ 0 → (∀ i, (t.pt i).left = (u.ex (((N' : ℂ) ^ 2)⁻¹ • (lam i : Fin g → ℂ))).left) → t.HasTh (𝟙 _) (fun a => χ (∑ i, ((a i).val : ℤ) • lam i) * Complex.exp (-(Real.pi / 2 / (N' : ℂ) ^ 2) * hermForm Hm (∑ i, ((a i).val : ℂ) • (lam i : Fin g → ℂ)) (∑ i, ((a i).val : ℂ) • (lam i : Fin g → ℂ))) * θ ((N' : ℂ)⁻¹ • ∑ i, ((a i).val : ℂ) • (lam i : Fin g → ℂ))) := by
  intro hL hL2 hT o _ g N' J b em t u Hm χ θ lam hN hAH hθ h0 hpt
  have hN0 : (N' : ℂ) ≠ 0 := by exact_mod_cast hN.pos.ne'
  haveI := t.ab.comm
  refine ⟨hN, ?_, fun q => ⟨⊤, trivial, ?_⟩⟩
  · have h : IsUnit (N' : ℂ) := IsUnit.mk0 _ hN0
    have h' := h.map (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
    rw [map_natCast] at h'
    exact h'
  let T : Over (Sp ℂ) := Out.overRes (T := Out.baseOver (Sp ℂ)) ⊤
  haveI : IsIso T.hom := by
    show IsIso ((⊤ : (Sp ℂ).Opens).ι ≫ 𝟙 _)
    rw [Category.comp_id]
    exact inferInstanceAs (IsIso (Sp ℂ).topIso.hom)
  let p : 𝟙_ (Over (Sp ℂ)) ⟶ T := Over.homMk (inv T.hom) (by simp)
  have hp : p ≫ Out.overResι (T := Out.baseOver (Sp ℂ)) ⊤ = 𝟙 _ := by
    ext1
    show inv T.hom ≫ (⊤ : (Sp ℂ).Opens).ι = 𝟙 _
    rw [IsIso.inv_comp_eq]
    rfl
  have hpt' : t.pt = fun i => u.ex (((N' : ℂ) ^ 2)⁻¹ • (lam i : Fin g → ℂ)) :=
    funext fun i => Over.OverMorphism.ext (hpt i)
  have hcoe : ∀ a : Ix g (N' ^ 2), ((∑ i, ((a i).val : ℤ) • lam i : u.Λ) : Fin g → ℂ) =
      ∑ i, ((a i).val : ℂ) • (lam i : Fin g → ℂ) := fun a => by
    rw [Submodule.coe_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Submodule.coe_smul, natCast_zsmul, Nat.cast_smul_eq_nsmul]
  have hlab : ∀ a : Ix g (N' ^ 2), t.lab a =
      u.ex (((N' : ℂ) ^ 2)⁻¹ • ((∑ i, ((a i).val : ℤ) • lam i : u.Λ) : Fin g → ℂ)) := fun a => by
    rw [hcoe, Finset.smul_sum, TObj.lab, hpt']
    refine (ex_sum u _ _).symm.trans (congrArg u.ex (Finset.sum_congr rfl fun i _ => ?_))
    rw [smul_comm, Nat.cast_smul_eq_nsmul]
  have htor : ∀ a : Ix g (N' ^ 2), t.lab a ^ (N' ^ 2) = 1 := fun a => by
    rw [TObj.lab, Out.linComb, List.prod_ofFn, ← Finset.prod_pow]
    refine Finset.prod_eq_one fun i _ => ?_
    rw [← pow_mul, mul_comm, pow_mul, t.torsion, one_pow]
  have key := isThetaPtOver hL hL2 hT t.pol u Hm χ θ N' T p
    (fun a : Ix g (N' ^ 2) => Out.overResι ⊤ ≫ t.lab a) (fun a => ∑ i, ((a i).val : ℤ) • lam i)
    hN hAH hθ h0 (fun a => (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ t.lab a) hp).trans
      ((Category.id_comp _).trans (hlab a))))
    (fun a => exists_symLift hL t.pol (N' ^ 2) _ (by push_cast; rfl) hN.pow (t.lab a) (htor a))
  convert key using 2 with a a
  · congr 1
  · refine (constFn_top _).trans ?_
    refine congrArg (constFn T.hom ⊤) ?_
    exact congrArg (fun w : Fin g → ℂ => χ (∑ i, ((a i).val : ℤ) • lam i) *
      Complex.exp (-(Real.pi / 2 / (N' : ℂ) ^ 2) * hermForm Hm w w) * θ ((N' : ℂ)⁻¹ • w)) (hcoe a).symm

end GlobalTheory.ThetaClassical
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM

theorem eval₂_mul_eq_zero_of_complex {o K₀ K σ : Type} [CommRing o] [Field K₀] [CommRing K] (β : o →+* K₀)
    (i : K₀ →+* K) (j : K₀ →+* ℂ) (v : σ → K₀) (F : MvPolynomial σ o)
    (h : ∀ c : ℂ, c ≠ 0 → MvPolynomial.eval₂ (j.comp β) (fun a => c * j (v a)) F = 0) (u : K) :
    MvPolynomial.eval₂ (i.comp β) (fun a => u * i (v a)) F = 0 := by
  let P : Polynomial K₀ :=
    MvPolynomial.eval₂ (Polynomial.C.comp β) (fun a => Polynomial.X * Polynomial.C (v a)) F
  have key : ∀ {E : Type} [CommRing E] (k : K₀ →+* E) (c : E),
      Polynomial.eval₂RingHom k c P = MvPolynomial.eval₂ (k.comp β) (fun a => c * k (v a)) F := by
    intro E _ k c
    simp only [P]
    rw [MvPolynomial.hom_eval₂]
    congr 1
    · ext r
      simp
    · funext a
      rw [map_mul]
      simp
  have hP : P.map j = 0 := by
    refine Polynomial.eq_zero_of_infinite_isRoot _ ((Set.finite_singleton (0 : ℂ)).infinite_compl.mono fun c hc => ?_)
    change (P.map j).eval c = 0
    rw [Polynomial.eval_map]
    exact (key j c).trans (h c hc)
  rw [Polynomial.map_eq_zero] at hP
  rw [← key, hP, map_zero]

theorem TObj.exists_hasTh_field (hL : Out.Laws) (hL2 : Out.Laws2) {o : Type} [CommRing o] {g N' : ℕ} {J : Type}
    {b : TBase o (N' ^ 2)} {K : Type} [Field K] {s : Sp K ⟶ Sp o} (t : TObj g (N' ^ 2) J b s) (hN : Odd N') :
    ∃ v : Ix g (N' ^ 2) → K, t.HasTh (𝟙 _) v := by
  obtain ⟨R, _, x, v, hx, ⟨p, hp⟩, hth⟩ := GlobalTheory.ThetaLocal.exists_hasTh hL hL2 o g N' J b _ s t hN
    (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K)
  have hr : Set.range (𝟙 (Sp K) : Sp K ⟶ Sp K) ⊆ Set.range x := by
    rintro q -
    exact ⟨p, Subsingleton.elim (α := PrimeSpectrum K) _ _⟩
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (IsOpenImmersion.lift x (𝟙 _) hr)
  have e : spMap φ.hom ≫ x = 𝟙 _ := by
    rw [← IsOpenImmersion.lift_fac x (𝟙 _) hr, ← hφ]
    rfl
  exact ⟨_, e ▸ GlobalTheory.T.hasThetaConstants_ring_baseChange hL2 o g N' J b _ s t R K φ.hom x v hth⟩

theorem eval₂_eq_zero_of_fromC (hL : Out.Laws) (hL2 : Out.Laws2) {o : Type} [CommRing o] {g n N' : ℕ} {J : Type}
    {b : TBase o (N' ^ 2)} {em : o →+* ℂ} {C : TObj g (N' ^ 2) J b (spMap em) → Prop} {S : Scheme.{0}}
    {s : S ⟶ Sp o} {t : TObj g (N' ^ 2) J b s} (h2 : 2 ≤ n) (hn : n ∣ N') (hN : Odd N') {K : Type} [Field K]
    {y : Sp K ⟶ S} (hy : FromC em C t y) (β : o →+* K) (hβ : y ≫ s = spMap β) {w : Ix g (N' ^ 2) → K}
    (hw : t.HasTh y w) {F : MvPolynomial (Ix g (N' ^ 2)) o} (hF : F ∈ thIdeal em C) :
    MvPolynomial.eval₂ β w F = 0 := by
  obtain ⟨K₀, _, β₀, i, j, t₀, tx, tc, hem, hs, m1, m2, m3, hC⟩ := hy
  have hβi : β = i.comp β₀ := by
    have e : Spec.map (CommRingCat.ofHom β) = Spec.map (CommRingCat.ofHom β₀ ≫ CommRingCat.ofHom i) := by
      rw [Spec.map_comp]
      exact hβ.symm.trans hs
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective e)
  have a1 : tx.HasTh (𝟙 _) w :=
    (GlobalTheory.hasTh_iff_of_tmap o g N' J b _ _ t _ _ tx y K (𝟙 _) w m1).2 (by rwa [Category.id_comp])
  have a2 : t₀.HasTh (spMap i) w := by
    have := (GlobalTheory.hasTh_iff_of_tmap o g N' J b _ _ t₀ _ _ tx (spMap i) K (𝟙 _) w m2).1 a1
    rwa [Category.id_comp] at this
  obtain ⟨v₀, hv₀⟩ := t₀.exists_hasTh_field hL hL2 hN
  have a3 : t₀.HasTh (spMap i) (fun a => i (v₀ a)) := by
    have := GlobalTheory.T.hasThetaConstants_ring_baseChange hL2 o g N' J b _ _ t₀ K₀ K i (𝟙 _) v₀ hv₀
    rwa [Category.comp_id] at this
  have hspan : Ideal.span (Set.range fun a => i (v₀ a)) = ⊤ := by
    obtain ⟨a, ha⟩ := GlobalTheory.T.thetaCosetNonvanishing_of_hasTh hL hL2 o g N' J b _ _ t₀ n K (spMap i) _ ⊥ h2 hn a3 Ideal.isPrime_bot 0
    rw [Ideal.mem_bot] at ha
    exact Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨_, rfl⟩) (Ne.isUnit ha)
  obtain ⟨u, hu⟩ := GlobalTheory.hasTh_unique_unit hL hL2 o g N' J b _ _ t₀ K (spMap i) _ w a3 a2 hspan
  have a4 : tc.HasTh (𝟙 _) (fun a => j (v₀ a)) := by
    refine (GlobalTheory.hasTh_iff_of_tmap o g N' J b _ _ t₀ _ _ tc (spMap j) ℂ (𝟙 _) _ m3).2 ?_
    have := GlobalTheory.T.hasThetaConstants_ring_baseChange hL2 o g N' J b _ _ t₀ K₀ ℂ j (𝟙 _) v₀ hv₀
    rw [Category.comp_id] at this
    rwa [Category.id_comp]
  rw [hβi, funext hu]
  refine eval₂_mul_eq_zero_of_complex β₀ i j v₀ F (fun c hc => ?_) u
  have hle : thIdeal em C ≤ RingHom.ker (MvPolynomial.eval₂Hom em (fun a => c * j (v₀ a))) :=
    iInf_le_of_le tc (iInf_le_of_le _ (iInf_le_of_le ⟨hC, a4.unit_mul c hc.isUnit⟩ le_rfl))
  rw [hem]
  exact hle hF

theorem inMM_of_dense_fromSet :
    Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g n N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (em : o →+* ℂ) (C : TObj g (N' ^ 2) J b (spMap em) → Prop) (S : Scheme.{0}) (s : S ⟶ Sp o) (t : TObj g (N' ^ 2) J b s) (R : Type) [CommRing R] (β : o →+* R) (x : Sp R ⟶ S) (v : Ix g (N' ^ 2) → R), 2 ≤ n → n ∣ N' → Odd N' → IsReduced S → Dense (fromSet em C t) → IsOpenImmersion x → x ≫ s = spMap β → t.HasTh x v → InMM n N' (thIdeal em C) β v := by
  intro hL hL2 o _ g n N' J b em C S s t R _ β x v h2 hn hN hS hd hx hβ hth
  refine ⟨fun F hF => ?_, fun q hq => GlobalTheory.T.thetaCosetNonvanishing_of_hasTh hL hL2 o g N' J b S s t n R x v q h2 hn hth hq⟩
  have hR : IsReduced (Sp R) := isReduced_of_isOpenImmersion x
  have hR' : _root_.IsReduced R := (affine_isReduced_iff (CommRingCat.of R)).1 hR
  refine IsNilpotent.eq_zero ((PrimeSpectrum.basicOpen_eq_bot_iff _).1 ?_)
  by_contra hne
  have hd' : Dense (x ⁻¹' fromSet em C t) := hd.preimage x.isOpenEmbedding.isOpenMap
  obtain ⟨q, hq, K, _, y, ⟨p, hp⟩, hy⟩ := hd'.inter_open_nonempty
    (PrimeSpectrum.basicOpen (MvPolynomial.eval₂ β v F) : Set (PrimeSpectrum R))
    (PrimeSpectrum.basicOpen _).isOpen ((TopologicalSpace.Opens.ne_bot_iff_nonempty _).1 hne)
  have hr : Set.range y ⊆ Set.range x := by
    rintro _ ⟨p', rfl⟩
    exact ⟨q, by rw [← hp, Subsingleton.elim (α := PrimeSpectrum K) p p']⟩
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (IsOpenImmersion.lift x y hr)
  have e : spMap φ.hom ≫ x = y := by
    rw [← IsOpenImmersion.lift_fac x y hr, ← hφ]
    rfl
  have hq' : PrimeSpectrum.comap φ.hom p = q := by
    apply x.isOpenEmbedding.injective
    rw [← hp, ← e]
    rfl
  have hw : t.HasTh y (fun a => φ.hom (v a)) := e ▸ GlobalTheory.T.hasThetaConstants_ring_baseChange hL2 o g N' J b S s t R K φ.hom x v hth
  have hs : y ≫ s = spMap (φ.hom.comp β) := by
    rw [← e, Category.assoc, hβ, ← Spec.map_comp]
    rfl
  have h0 := eval₂_eq_zero_of_fromC hL hL2 h2 hn hN hy _ hs hw hF
  rw [← MvPolynomial.hom_eval₂] at h0
  apply hq
  rw [← hq']
  change φ.hom _ ∈ PrimeSpectrum.asIdeal p
  rw [h0]
  exact Ideal.zero_mem _

end GlobalTheory.ZM
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.exists_thetaConstants_locally_on_base : Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (S : Scheme.{0}) (s : S ⟶ Sp o) (t : TObj g (N' ^ 2) J b s), Odd N' → ∀ p : S, ∃ (R : Type) (_ : CommRing R) (x : Sp R ⟶ S) (v : Ix g (N' ^ 2) → R), IsOpenImmersion x ∧ p ∈ Set.range x ∧ t.HasTh x v := by
  first | exact @GlobalTheory.ThetaLocal.exists_hasTh | exact GlobalTheory.ThetaLocal.exists_hasTh | (intros; apply GlobalTheory.ThetaLocal.exists_hasTh <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV

theorem _root_.GlobalTheory.T.sectionsGrowth_basic_properties_abelianVariety : ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (M : LB P.A.left) (g : ℕ), M.IsLB → (∃ r, SectionsHaveFiniteDimension P.A.hom M r) ∧ (∀ δ δ', Vol P.A.hom M g δ → Vol P.A.hom M g δ' → δ = δ') ∧ (∀ (M' : LB P.A.left) δ, M'.IsLB → LBIso M M' → Vol P.A.hom M g δ → Vol P.A.hom M' g δ) ∧ (∀ (a : ℕ) δ, 1 ≤ a → Vol P.A.hom M g δ → Vol P.A.hom (lbPow M a) g ((a : ℝ) ^ g * δ)) ∧ (∀ (a : ℕ) δ, 1 ≤ a → Out.RelAmple P.A M → Vol P.A.hom (lbPow M a) g ((a : ℝ) ^ g * δ) → Vol P.A.hom M g δ) ∧ ∀ (M' : LB P.A.left) (s : (LB.div M' M).Sec), M'.IsLB → (∃ j, s.f j ≠ 0) → (∀ r r', SectionsHaveFiniteDimension P.A.hom M r → SectionsHaveFiniteDimension P.A.hom M' r' → r ≤ r') ∧ ∀ δ δ', Vol P.A.hom M g δ → Vol P.A.hom M' g δ' → δ ≤ δ' := by
  first | exact @GlobalTheory.VolBasic.vol_basic | exact GlobalTheory.VolBasic.vol_basic | (intros; apply GlobalTheory.VolBasic.vol_basic <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV

theorem _root_.GlobalTheory.T.mulA_pullback_iso_pow_sq_symmetric_abelianVariety : ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (M : LB P.A.left) (k : ℕ), M.IsLB → SymB M → LBIso (M.pull (Out.mulA P.A k).left) (lbPow M (k ^ 2)) := by
  first | exact @GlobalTheory.MulSym.lbIso_mulPull_of_symB | exact GlobalTheory.MulSym.lbIso_mulPull_of_symB | (intros; apply GlobalTheory.MulSym.lbIso_mulPull_of_symB <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.ZM GlobalTheory.KS

theorem _root_.GlobalTheory.T.tangent_injects_symmetric_antilinear_commuting : Out.Laws → Out.Laws2 → ThetaUnifAV → ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (R : Type) [CommRing R] [Algebra o R] [Algebra o ℂ] [Algebra R ℂ] [IsScalarTower o R ℂ] (t : TObj g k J b (spMap (algebraMap o R))), (∀ (x : Sp (DualNumber ℂ) ⟶ Sp R) (t' : TObj g k J b (x ≫ spMap (algebraMap o R))), x ≫ spMap (algebraMap o R) = constPt x ≫ spMap (algebraMap o R) → TMap t' t x → TMap t' t (constPt x) → x = constPt x) → ∃ (t₀ : TObj g k J b (spMap (algebraMap o ℂ))) (m : t₀.A.left ⟶ t.A.left) (u : HolUnif t₀.pol.A t₀.pol.L t₀.pol.g) (Hm : Matrix (Fin t₀.pol.g) (Fin t₀.pol.g) ℂ) (χ : u.Λ → ℂ) (κ : Derivation o R ℂ →ₗ[ℂ] Matrix (Fin t₀.pol.g) (Fin t₀.pol.g) ℂ), GoodU u Hm χ ∧ (IsGrpPullback t₀.A t.A (spMap (algebraMap R ℂ)) m ∧ LBIso t₀.L (t.L.pull m) ∧ (∀ i, (t₀.pt i).left ≫ m = (spMap (algebraMap R ℂ)) ≫ (t.pt i).left) ∧ ∀ jj, (t₀.act jj).left ≫ m = m ≫ (t.act jj).left) ∧ Function.Injective κ ∧ ∀ D, IsSymm Hm (κ D) ∧ ∀ (f : t.A ⟶ t.A) (f₀ : t₀.pol.A ⟶ t₀.pol.A) (F : (Fin t₀.pol.g → ℂ) →ₗ[ℂ] (Fin t₀.pol.g → ℂ)), f₀.left ≫ m = m ≫ f.left → (∀ z, u.ex (F z) = u.ex z ≫ f₀) → Comm (κ D) F := by
  first | exact @GlobalTheory.KS.tangent_injects_symm_antilinear | exact GlobalTheory.KS.tangent_injects_symm_antilinear | (intros; apply GlobalTheory.KS.tangent_injects_symm_antilinear <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

theorem _root_.GlobalTheory.T.theorem_of_cube_polAbelianScheme : ∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen := by
  first | exact @GlobalTheory.Moduli.cube_of_isLB | exact GlobalTheory.Moduli.cube_of_isLB | (intros; apply GlobalTheory.Moduli.cube_of_isLB <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct

theorem _root_.GlobalTheory.T.kTriv_of_geometric_points_and_tangents : Out.Laws → ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → IsProjBy A.hom → ∀ M : LB A.left, M.IsLB → (∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra R K], (∀ x : specO R K ⟶ A, Triv (Out.translDiff A M x) → x = 1) ∧ ∀ x : specO R (DualNumber K) ⟶ A, ptMap (TrivSqZeroExt.fstHom R K K) ≫ x = 1 → Triv (Out.translDiff A M x) → x = 1) → Out.KTriv A M := by
  first | exact @GlobalTheory.KCriterion.kTriv_of_points_of_tangents | exact GlobalTheory.KCriterion.kTriv_of_points_of_tangents | (intros; apply GlobalTheory.KCriterion.kTriv_of_points_of_tangents <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.FlatTors GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator
open scoped TensorProduct

theorem _root_.GlobalTheory.T.isFinite_and_flat_mul_abelianScheme : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ k : ℕ, 1 ≤ k → IsFinite ((𝟙 A) ^ k : A ⟶ A).left ∧ Flat ((𝟙 A) ^ k : A ⟶ A).left := by
  first | exact @GlobalTheory.MulFiniteFlat.isFinite_and_flat_mul | exact GlobalTheory.MulFiniteFlat.isFinite_and_flat_mul | (intros; apply GlobalTheory.MulFiniteFlat.isFinite_and_flat_mul <;> assumption)
end
