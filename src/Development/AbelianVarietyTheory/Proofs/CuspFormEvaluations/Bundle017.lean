module

public import Development.AbelianVarietyTheory.Definitions.ThetaValues.LetAct
public import Formalism.GradedWeylDivisibility.FinalD
public import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.GradedWeylDivisibility.FinalC
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle011
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle001
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle015
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
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
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle001

@[expose] public section

section

open NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.FrameRead
open scoped Classical

noncomputable section

namespace GlobalTheory.DetSat

theorem mem_valuationSubring_of_indep {K σ ι : Type} [Field K] [Fintype ι] (A : ValuationSubring K)
    (q : ι → MvPolynomial σ ℤ)
    (hq : LinearIndependent (IsLocalRing.ResidueField A)
      (fun i => map (Int.castRingHom (IsLocalRing.ResidueField A)) (q i)))
    (c : ι → K) (hc : ∀ m, (∑ i, c i • map (Int.castRingHom K) (q i)).coeff m ∈ A) (i : ι) : c i ∈ A := by
  by_contra hi
  obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ (fun i => A.valuation (c i)) ⟨i, Finset.mem_univ i⟩
  have h1 : 1 < A.valuation (c j) :=
    lt_of_lt_of_le (not_le.mp fun h => hi ((A.valuation_le_one_iff _).mp h)) (hj i (Finset.mem_univ i))
  have hv0 : 0 < A.valuation (c j) := lt_trans zero_lt_one h1
  have hj0 : c j ≠ 0 := by
    rintro h
    rw [h, map_zero] at hv0
    exact lt_irrefl _ hv0
  have ha : ∀ k, c k / c j ∈ A := fun k => by
    rw [← A.valuation_le_one_iff, map_div₀, div_le_one₀ hv0]
    exact hj k (Finset.mem_univ k)
  let a : ι → A := fun k => ⟨c k / c j, ha k⟩
  have key : ∑ k, IsLocalRing.residue A (a k) • map (Int.castRingHom (IsLocalRing.ResidueField A)) (q k) = 0 := by
    ext m
    have e1 : (∑ k, IsLocalRing.residue A (a k) • map (Int.castRingHom (IsLocalRing.ResidueField A)) (q k)).coeff m
        = IsLocalRing.residue A (∑ k, a k * (((q k).coeff m : ℤ) : A)) := by
      simp [coeff_map]
    rw [e1, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply, IsLocalRing.residue_eq_zero_iff, A.valuation_lt_one_iff]
    have e2 : ((∑ k, a k * (((q k).coeff m : ℤ) : A) : A) : K)
        = (∑ i, c i • map (Int.castRingHom K) (q i)).coeff m / c j := by
      rw [coeff_sum, Finset.sum_div]
      change A.subtype _ = _

      rw [map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_mul, map_intCast, MvPolynomial.coeff_smul, coeff_map]
      simp only [a, ValuationSubring.coe_subtype, smul_eq_mul, eq_intCast]
      ring
    rw [e2, map_div₀, div_lt_one₀ hv0]
    exact lt_of_le_of_lt ((A.valuation_le_one_iff _).mpr (hc m)) h1
  have h0 := Fintype.linearIndependent_iff.mp hq _ key j
  have : a j = 1 := Subtype.ext (div_self hj0)
  rw [this, map_one] at h0
  exact one_ne_zero h0

theorem integral_of_indep {K σ ι : Type} [Field K] [NumberField K] [Fintype ι] (q : ι → MvPolynomial σ ℤ)
    (hq : ∀ (k : Type) [Field k], LinearIndependent k (fun i => map (Int.castRingHom k) (q i)))
    (c : ι → K) (hc : ∀ m, IsIntegral ℤ ((∑ i, c i • map (Int.castRingHom K) (q i)).coeff m)) (i : ι) :
    ∃ a : 𝓞 K, algebraMap (𝓞 K) K a = c i := by
  refine IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 K) K (c i) fun v => ?_
  refine mem_valuationSubring_of_indep (v.valuation K).valuationSubring q (hq _) c (fun m => ?_) i
  exact v.valuation_le_one (K := K) (⟨_, hc m⟩ : 𝓞 K)

def ssZ (n : ℕ) (ν : Fin n → ℕ) : Formalism.GradedWeylDivisibility.ssIdx n n ν → MvPolynomial (Fin n × Fin n) ℤ :=
  (Formalism.GradedWeylDivisibility.sSBasis ℤ n n ν).choose

theorem ssZ_indep (k : Type) [Field k] (n : ℕ) (ν : Fin n → ℕ) :
    LinearIndependent k (fun m => map (Int.castRingHom k) (ssZ n ν m)) := by
  have h : ∀ m, (Formalism.GradedWeylDivisibility.colLex n n).degree (map (Int.castRingHom k) (ssZ n ν m)) = m.1 ∧
      (Formalism.GradedWeylDivisibility.colLex n n).leadingCoeff (map (Int.castRingHom k) (ssZ n ν m)) = 1 := fun m => by
    obtain ⟨hd, -, N, sz, hsz, I, -, hI, hb⟩ := (Formalism.GradedWeylDivisibility.sSBasis ℤ n n ν).choose_spec.2 m
    have hb' : ssZ n ν m = Formalism.GradedWeylDivisibility.bideterminant ℤ sz hsz I := hb
    have hd' : (Formalism.GradedWeylDivisibility.colLex n n).degree (ssZ n ν m) = m.1 := hd
    rw [hb', (Formalism.GradedWeylDivisibility.column_lex_bideterminant ℤ n n N sz hsz I hI).1] at hd'
    rw [hb', Formalism.GradedWeylDivisibility.ldlat_map_bidet, ← hd']
    exact Formalism.GradedWeylDivisibility.column_lex_bideterminant k n n N sz hsz I hI
  refine Formalism.GradedWeylDivisibility.ldbasis_linearIndependent (Formalism.GradedWeylDivisibility.colLex n n) _ (fun m m' e => ?_) fun m => (h m).2
  exact Subtype.ext ((h m).1.symm.trans (e.trans (h m').1))

theorem ssZ_span (K : Type) [Field K] [CharZero K] (n : ℕ) (ν : Fin n → ℕ) :
    Submodule.span K (Set.range fun m => map (Int.castRingHom K) (ssZ n ν m)) = Formalism.GradedWeylDivisibility.dualWeyl K n n ν := by
  have h := (Formalism.GradedWeylDivisibility.nablaLKBasis ℤ K (algebraMap ℤ K).injective_int n n ν (ssZ n ν) _
    (Formalism.GradedWeylDivisibility.sSBasis ℤ n n ν).choose_spec.1 1 (by simp)).2
  have h1 : Formalism.GradedWeylDivisibility.rowAct K (n := n) ((1 : Matrix (Fin n) (Fin n) K)⁻¹) = AlgHom.id K _ := by
    rw [inv_one]
    apply MvPolynomial.algHom_ext
    intro v
    simp [Formalism.GradedWeylDivisibility.rowAct, Matrix.one_apply, apply_ite C]
  rw [h1] at h
  exact h

theorem ssZ_mem (n : ℕ) (ν : Fin n → ℕ) (m) : ssZ n ν m ∈ Formalism.GradedWeylDivisibility.dualWeyl ℤ n n ν := by
  rw [← (Formalism.GradedWeylDivisibility.sSBasis ℤ n n ν).choose_spec.1.2.1]
  exact Submodule.subset_span ⟨m, rfl⟩

variable {Ix : Type} [Fintype Ix] {n : ℕ}

def prodZ (lam : Ix → DomWeight n) (i : VVIdx lam) : MvPolynomial (Ix × Fin n × Fin n) ℤ :=
  ∏ t, Formalism.GradedWeylDivisibility.blockEmb ℤ t (ssZ n (lam t).natW (i t))

theorem map_prodZ (k : Type) [CommRing k] (lam : Ix → DomWeight n) (i : VVIdx lam) :
    map (Int.castRingHom k) (prodZ lam i) =
      ∏ t, Formalism.GradedWeylDivisibility.blockEmb k t (map (Int.castRingHom k) (ssZ n (lam t).natW (i t))) := by
  simp only [prodZ, map_prod, Formalism.GradedWeylDivisibility.blockEmb, map_rename]

theorem prodZ_basis (k : Type) [Field k] (lam : Ix → DomWeight n) :
    LinearIndependent k (fun i => map (Int.castRingHom k) (prodZ lam i)) ∧
      Submodule.span k (Set.range fun i => map (Int.castRingHom k) (prodZ lam i)) =
        Formalism.GradedWeylDivisibility.tensorLat k k fun t =>
          Submodule.span k (Set.range fun m => map (Int.castRingHom k) (ssZ n (lam t).natW m)) := by
  simp only [map_prodZ]
  exact Formalism.GradedWeylDivisibility.tensorBasis k k Ix n n (fun t => Formalism.GradedWeylDivisibility.ssIdx n n (lam t).natW) _
    (fun t m => map (Int.castRingHom k) (ssZ n (lam t).natW m)) (fun t => ssZ_indep k n _) (fun _ => rfl)

theorem prodZ_mem (K : Type) [Field K] [NumberField K] (lam : Ix → DomWeight n) (i : VVIdx lam) :
    map (Int.castRingHom K) (prodZ lam i) ∈ nabStd K lam := by
  rw [map_prodZ]
  refine Submodule.subset_span ⟨_, fun t => ?_, rfl⟩
  refine ⟨map (Int.castRingHom (𝓞 K)) (ssZ n (lam t).natW (i t)),
    Formalism.GradedWeylDivisibility.dualWeylMap _ _ _ n n _ _ (ssZ_mem n _ _), ?_⟩
  change map (algebraMap (𝓞 K) K) _ = _
  rw [map_map]
  congr 2

theorem map_detProd (k : Type) [CommRing k] (e : Ix → ℕ) :
    map (Int.castRingHom k) (∏ t, (gen ℤ n t).det ^ e t) = ∏ t, (gen k n t).det ^ e t := by
  simp only [map_prod, map_pow, RingHom.map_det]
  refine Finset.prod_congr rfl fun t _ => ?_
  congr 2
  ext a s : 2
  simp [gen]

theorem detProd_ne_zero (k : Type) [Field k] (e : Ix → ℕ) : (∏ t, (gen k n t).det ^ e t) ≠ 0 := by
  refine Finset.prod_ne_zero_iff.mpr fun t _ => pow_ne_zero _ fun h => ?_
  have h2 := congrArg (eval fun v : Ix × Fin n × Fin n => (1 : Matrix (Fin n) (Fin n) k) v.2.1 v.2.2) h
  rw [RingHom.map_det, map_zero] at h2
  have h3 : (eval fun v : Ix × Fin n × Fin n => (1 : Matrix (Fin n) (Fin n) k) v.2.1 v.2.2).mapMatrix (gen k n t)
      = 1 := by
    ext a s
    simp [gen]
  rw [h3, Matrix.det_one] at h2
  exact one_ne_zero h2

theorem mem_nabStd_of_det_mul_integral : ∀ (K : Type) [Field K] [NumberField K] (Ix : Type) [Fintype Ix] (n : ℕ)
    (lam : Ix → DomWeight n) (e : Ix → ℕ), ∀ F ∈ VV K lam,
    (∀ m, IsIntegral ℤ (((∏ t, (gen K n t).det ^ e t) * F).coeff m)) → F ∈ nabStd K lam := by
  intro K _ _ Ix _ n lam e F hF hint
  have hV : Submodule.span K (Set.range fun i => map (Int.castRingHom K) (prodZ lam i)) = VV K lam := by
    rw [(prodZ_basis K lam).2]
    simp only [ssZ_span]
    rfl
  rw [← hV, Submodule.mem_span_range_iff_exists_fun] at hF
  obtain ⟨c, rfl⟩ := hF
  have h := integral_of_indep (fun i => (∏ t, (gen ℤ n t).det ^ e t) * prodZ lam i) (fun k _ => by
      simp only [map_mul, map_detProd]
      exact (prodZ_basis k lam).1.map' (LinearMap.mulLeft k (∏ t, (gen k n t).det ^ e t))
        (LinearMap.ker_eq_bot.mpr (mul_right_injective₀ (detProd_ne_zero k e)))) c (fun m => by
      have := hint m
      rw [Finset.mul_sum] at this
      simpa only [map_mul, map_detProd, mul_smul_comm] using this)
  choose a ha using h
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [← ha i, algebraMap_smul]
  exact Submodule.smul_mem _ _ (prodZ_mem K lam i)

end GlobalTheory.DetSat
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ThetaPullback

variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

private theorem gm_res_eq_gm {X Z : Scheme.{0}} (r : Z ⟶ X) (z : Z) {U V : X.Opens} (hle : V ≤ U) (hz : r z ∈ V)
    (a : Γ(X, U)ˣ) : gm r z V (res hle a) = gm r z U a := by
  have key : X.presheaf.map (homOfLE hle).op ≫ r.app V ≫ Z.presheaf.germ (r ⁻¹ᵁ V) z hz =
      r.app U ≫ Z.presheaf.germ (r ⁻¹ᵁ U) z (hle hz) := by
    rw [Scheme.Hom.naturality_assoc]
    congr 1
    exact TopCat.Presheaf.germ_res _ _ _ _
  unfold gm res pullU
  rw [dite_eq_left hz, dite_eq_left (hle hz)]
  ext
  simp only [MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe]
  exact congrArg (fun φ => φ.hom (a : Γ(X, U))) key

private theorem exists_isGen_linComb_val_eq_of_eq {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ φ' : K → (Y ⟶ X)}
    {ε : K → ℤ} (hφ : φ = φ') (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) :
    ∃ t' : LB.Gen (LB.LinComb L φ' ε), t'.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι), val t' r z J = val t r z J := by
  subst hφ
  exact ⟨t, ht, fun _ _ _ _ => rfl⟩

theorem whiskerRight_translPt {T T' : Over S} (h : T' ⟶ T) (x : T ⟶ A) :
    h ▷ A ≫ translPt A x = translPt A (h ≫ x) := by
  unfold translPt
  rw [← Category.assoc, comp_lift]
  simp

theorem translT_whiskerRight {T T' : Over S} (h : T' ⟶ T) (x : T ⟶ A) :
    translT A (h ≫ x) ≫ h ▷ A = h ▷ A ≫ translT A x := by
  ext <;> simp [translT, whiskerRight_translPt]

theorem negT_whiskerRight {T T' : Over S} (h : T' ⟶ T) :
    negT A T' ≫ h ▷ A = h ▷ A ≫ negT A T := by
  ext <;> simp [negT]

theorem val_powGen {L : LB A.left} {k : ℤ} {T : Over S} (θ : ThetaGrp A L k T) (n : ℕ) {Z : Scheme.{0}}
    (r : Z ⟶ (T ⊗ A).left) {z : Z} {J} (hJ : Good L z J) :
    val (powGen A L k θ n) r z J = ∏ j : Fin n,
      val (L := L) (φ := ![(snd T A).left, (translPt A θ.pt).left]) (ε := ![k, -k]) θ.φ
        (r ≫ (translT A (θ.pt ^ (j : ℕ))).left) z J := by
  have e : ∀ j : Fin n, val (L := L) (φ := ![(snd T A).left, (translPt A θ.pt).left]) (ε := ![k, -k]) θ.φ
      (r ≫ (translT A (θ.pt ^ (j : ℕ))).left) z J =
      val (LB.pullGen L _ _ θ.φ (translT A (θ.pt ^ (j : ℕ))).left) r z J := fun j => (val_pull hJ _ _ r).symm
  rw [Finset.prod_congr rfl fun j _ => e j]
  unfold powGen val
  dsimp only
  erw [map_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  exact gm_res_eq_gm _ _ _ (hJ.mem _ r) _

theorem val_symGen {L : LB A.left} {k : ℤ} {T : Over S} (θ : ThetaGrp A L k T) (ν : LB.Gen (negLB A L k T))
    {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) {z : Z} {J} (hJ : Good L z J) :
    val (symGen A L k θ ν) r z J =
      val (L := L) (φ := ![(snd T A).left, (translPt A θ.pt).left]) (ε := ![k, -k]) θ.φ
          (r ≫ (translT A θ.pt⁻¹).left) z J *
        val (L := L) (φ := ![(snd T A).left, (snd T A ≫ (GrpObj.inv : A ⟶ A)).left]) (ε := ![k, -k]) ν r z J *
        (val (L := L) (φ := ![(snd T A).left, (translPt A θ.pt).left]) (ε := ![k, -k]) θ.φ
          (r ≫ (negT A T).left) z J *
        (val (L := L) (φ := ![(snd T A).left, (snd T A ≫ (GrpObj.inv : A ⟶ A)).left]) (ε := ![k, -k]) ν
          (r ≫ (translT A θ.pt⁻¹).left) z J)⁻¹) := by
  unfold symGen
  rw [val_mul hJ, val_mul hJ, val_inv]
  have e1 := val_mul hJ (LB.pullGen L _ _ θ.φ (translT A θ.pt⁻¹).left) ν r
  have e2 := val_pull hJ θ.φ (translT A θ.pt⁻¹).left r
  have e3 := val_pull hJ θ.φ (negT A T).left r
  have e4 := val_pull hJ ν (translT A θ.pt⁻¹).left r
  rw [e1, e2, e3, e4]

theorem exists_thetaGrp_pullback : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : LB A.left), L.IsLB → ∀ (k : ℤ) (T T' : Over S) (h : T' ⟶ T) (θ : ThetaGrp A L k T), ∃ θ' : ThetaGrp A L k T', θ'.pt = h ≫ θ.pt ∧ LB.Gen.Corr L _ _ _ _ θ'.φ (LB.pullGen L _ _ θ.φ (h ▷ A).left) ∧ (∀ (n : ℕ) (x : T ⟶ A), SymLift A L k n x θ → SymLift A L k n (h ≫ x) θ') ∧ ∀ (s t : LB.Sec (LPow A L k T)) (s' t' : LB.Sec (LPow A L k T')), IsActOf A L k θ s t → IsPullSec A L k (h ▷ A) (whiskerRight_snd _ _) s s' → IsPullSec A L k (h ▷ A) (whiskerRight_snd _ _) t t' → IsActOf A L k θ' s' t' := by
  intro S A _ _ L hL k T T' h θ
  have hφ : (fun b => (h ▷ A).left ≫ (![(snd T A).left, (translPt A θ.pt).left] : Fin 2 → _) b) =
      ![(snd T' A).left, (translPt A (h ≫ θ.pt)).left] := by
    funext b
    fin_cases b
    · simp only [Fin.zero_eta, Matrix.cons_val_zero]
      rw [← Over.comp_left, whiskerRight_snd]
    · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      rw [← Over.comp_left, whiskerRight_translPt]
  obtain ⟨φ', gφ', vφ'⟩ :=
    exists_isGen_linComb_val_eq_of_eq hφ _ (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen L _ _ θ.φ θ.3 (h ▷ A).left)
  have vθ : ∀ (Z : Scheme.{0}) (r : Z ⟶ (T' ⊗ A).left) (z : Z) (J : (Z ⟶ A.left) → L.ι), Good L z J →
      val φ' r z J = val (L := L) (φ := ![(snd T A).left, (translPt A θ.pt).left]) (ε := ![k, -k]) θ.φ
        (r ≫ (h ▷ A).left) z J :=
    fun Z r z J hJ => (vφ' Z r z J).trans (val_pull hJ _ _ r)
  have hcorr : LB.Gen.Corr L _ _ _ _ φ' (LB.pullGen L _ _ θ.φ (h ▷ A).left) :=
    corr_of_val hL fun y J _ => vφ' _ _ y J
  have hpow : ∀ j : ℕ, h ≫ θ.pt ^ j = (h ≫ θ.pt) ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ, pow_succ, comp_mul, ih]
  have hinv : h ≫ θ.pt⁻¹ = (h ≫ θ.pt)⁻¹ := GrpObj.comp_inv h θ.pt
  refine ⟨⟨h ≫ θ.pt, φ', gφ'⟩, rfl, hcorr, ?_, ?_⟩
  · intro n x hs
    obtain ⟨hpt, hpw, nu, gnu, hsym⟩ := hs
    refine ⟨?_, ?_, ?_⟩
    · show h ≫ θ.pt = h ≫ x
      rw [hpt]
    · refine corr_of_val hL fun y J hJ => ?_
      have hθ1 := val_corr hJ hpw (h ▷ A).left
      rw [val_one, val_powGen _ _ _ hJ] at hθ1
      rw [val_one, val_powGen _ _ _ hJ, ← hθ1]
      refine Finset.prod_congr rfl fun j _ => ?_
      dsimp only
      rw [vθ _ _ _ _ hJ]
      have e : (𝟙 _ ≫ (translT A ((h ≫ θ.pt) ^ (j : ℕ))).left) ≫ (h ▷ A).left =
          (h ▷ A).left ≫ (translT A (θ.pt ^ (j : ℕ))).left := by
        rw [Category.id_comp, ← Over.comp_left, ← Over.comp_left, ← hpow, translT_whiskerRight]
      rw [e]
    · have hφn : (fun b => (h ▷ A).left ≫
            (![(snd T A).left, (snd T A ≫ (GrpObj.inv : A ⟶ A)).left] : Fin 2 → _) b) =
          ![(snd T' A).left, (snd T' A ≫ (GrpObj.inv : A ⟶ A)).left] := by
        funext b
        fin_cases b
        · simp only [Fin.zero_eta, Matrix.cons_val_zero]
          rw [← Over.comp_left, whiskerRight_snd]
        · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]
          rw [← Over.comp_left, whiskerRight_snd_assoc]
      obtain ⟨nu', gnu', vnu'⟩ :=
        exists_isGen_linComb_val_eq_of_eq hφn _ (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen L _ _ nu gnu (h ▷ A).left)
      have vnu : ∀ (Z : Scheme.{0}) (r : Z ⟶ (T' ⊗ A).left) (z : Z) (J : (Z ⟶ A.left) → L.ι), Good L z J →
          val nu' r z J = val (L := L) (φ := ![(snd T A).left, (snd T A ≫ (GrpObj.inv : A ⟶ A)).left])
            (ε := ![k, -k]) nu (r ≫ (h ▷ A).left) z J :=
        fun Z r z J hJ => (vnu' Z r z J).trans (val_pull hJ _ _ r)
      refine ⟨nu', gnu', corr_of_val hL fun y J hJ => ?_⟩
      have hθ2 := val_corr hJ hsym (h ▷ A).left
      rw [val_one, val_symGen _ _ _ hJ] at hθ2
      rw [val_one]
      refine (val_symGen _ _ _ hJ).trans ?_
      rw [← hθ2]
      dsimp only
      rw [vθ _ _ _ _ hJ, vθ _ _ _ _ hJ, vnu _ _ _ _ hJ, vnu _ _ _ _ hJ]
      have e1 : (𝟙 _ ≫ (translT A (h ≫ θ.pt)⁻¹).left) ≫ (h ▷ A).left =
          (h ▷ A).left ≫ (translT A θ.pt⁻¹).left := by
        rw [Category.id_comp, ← Over.comp_left, ← Over.comp_left, ← hinv, translT_whiskerRight]
      have e3 : (𝟙 _ ≫ (negT A T').left) ≫ (h ▷ A).left = (h ▷ A).left ≫ (negT A T).left := by
        rw [Category.id_comp, ← Over.comp_left, ← Over.comp_left, negT_whiskerRight]
      rw [e1, e3, Category.id_comp]
  · intro s t s' t' hact hs ht
    unfold IsActOf at hact ⊢
    exact GlobalTheory.TwistBaseChange.isTwistPull_baseChange S A L hL T T' h _ _ _ _ _ _
      (translT_whiskerRight h θ.pt) k k θ.φ φ' θ.3 gφ' hcorr s t s' t' hact hs ht

end GlobalTheory.ThetaPullback
end
