module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1240
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1528
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1338
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1290
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzFunctionFactorizableSum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1298
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1530
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1310
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DsumEqZeroOfFibreSums
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1318
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1525
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1337
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle045
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1346
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1347
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1527
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1446
import GroundTheory.AutomorphicForms.LocallyProfinite
import GroundTheory.AutomorphicForms.Bundle003
import GroundTheory.GlobalFields.KummerTheory.LocalIndex
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodicityLevelHeightBound

@[expose] public section

section

open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

noncomputable section

namespace GlobalTheory.TwLat

theorem twCent_iff_gram : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E) (B : GlobalTheory.UnitLemma.InvAlg K) (m : ℕ) (b : Module.Basis (Fin m) K.E B.A) (β : B.A), IsUnit (GlobalTheory.TwLat.gram e b β) → ∀ g : GLw m w, g ∈ twCent (thL m w) (GlobalTheory.TwLat.dlt e b β) ↔ g.valᵀ * GlobalTheory.TwLat.gram e b β * g.val.map (cj w) = GlobalTheory.TwLat.gram e b β := by
  intro E _ _ _ w hw K e B m b β hG g
  have hth : thL m w = thetaGL m (cj w) := by rw [thL, if_neg hw]
  have hd : dlt e b β = invT m _ hG.unit * (PhiU m _)⁻¹ := by rw [dlt, dite_eq_left hG]
  rw [hth, hd]
  change g * _ = _ * _ ↔ _
  rw [Units.ext_iff]
  set G := gram e b β with hGdef
  set Φ := GlobalTheory.Tw.Phi m (w.adicCompletion E) with hΦdef
  have hΦ' : Φᵀ * Φ = 1 := mul_eq_one_comm.1 (Phi_mul_transpose m _)
  set Gi := (hG.unit⁻¹).val with hGidef
  have hGi1 : G * Gi = 1 := hG.unit.mul_inv
  have hGi2 : Gi * G = 1 := hG.unit.inv_mul
  set H := g.val.map (cj w) with hHdef
  set Hi := (g⁻¹ : GLw m w).val.map (cj w) with hHidef
  have hH : H * Hi = 1 := by
    rw [hHdef, hHidef, show g.val.map (cj w) = (cj w).mapMatrix g.val from rfl,
      show (g⁻¹ : GLw m w).val.map (cj w) = (cj w).mapMatrix (g⁻¹ : GLw m w).val from rfl, ← map_mul, Units.mul_inv,
      map_one]
  have hL : (g * (invT m _ hG.unit * (PhiU m _)⁻¹)).val = g.val * (Giᵀ * Φᵀ) := rfl
  have hR : (invT m _ hG.unit * (PhiU m _)⁻¹ * thetaGL m (cj w) g).val = Giᵀ * Φᵀ * (Φ * Hiᵀ * Φᵀ) := rfl
  rw [hL, hR]
  have hA : Giᵀ * Φᵀ * (Φ * Hiᵀ * Φᵀ) = Giᵀ * Hiᵀ * Φᵀ := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Φᵀ Φ, hΦ', Matrix.one_mul]
  rw [hA]
  have hB : g.val * (Giᵀ * Φᵀ) = Giᵀ * Hiᵀ * Φᵀ ↔ g.val * Giᵀ = Giᵀ * Hiᵀ := by
    constructor
    · intro h
      have := congrArg (· * Φ) h
      simp only [Matrix.mul_assoc, hΦ', Matrix.mul_one] at this
      simpa only [Matrix.mul_assoc] using this
    · intro h
      rw [← Matrix.mul_assoc, h]
  rw [hB]
  have hC : g.val * Giᵀ = Giᵀ * Hiᵀ ↔ Gi * g.valᵀ = Hi * Gi := by
    rw [← Matrix.transpose_inj]
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
  rw [hC]
  constructor
  · intro h
    calc g.valᵀ * G * H = (G * Gi) * g.valᵀ * G * H := by rw [hGi1, Matrix.one_mul]
      _ = G * (Gi * g.valᵀ) * G * H := by simp only [Matrix.mul_assoc]
      _ = G * Hi * (Gi * G) * H := by rw [h]; simp only [Matrix.mul_assoc]
      _ = G * (Hi * H) := by rw [hGi2, Matrix.mul_one, Matrix.mul_assoc]
      _ = G := by rw [mul_eq_one_comm.1 hH, Matrix.mul_one]
  · intro h
    calc Gi * g.valᵀ = Gi * g.valᵀ * ((G * H) * Hi * Gi) := by
          rw [Matrix.mul_assoc G, hH, Matrix.mul_one, hGi1, Matrix.mul_one]
      _ = Gi * (g.valᵀ * G * H) * Hi * Gi := by simp only [Matrix.mul_assoc]
      _ = Hi * Gi := by rw [h, hGi2, Matrix.one_mul]

theorem herm_finsum_left {K : GlobalTheory.UnitLemma.UQ} (B : GlobalTheory.UnitLemma.InvAlg K) (β : B.A) {ι : Type} (s : Finset ι)
    (v : ι → K.E) (x : ι → B.A) (z : B.A) :
    B.herm β (∑ i ∈ s, v i • x i) z = ∑ i ∈ s, v i * B.herm β (x i) z := by

  simp only [GlobalTheory.UnitLemma.InvAlg.herm, Finset.mul_sum, Finset.sum_mul, map_sum, mul_smul_comm, smul_mul_assoc,
  map_smul, smul_eq_mul]

theorem herm_finsum_right {K : GlobalTheory.UnitLemma.UQ} (B : GlobalTheory.UnitLemma.InvAlg K) (β y : B.A) {ι : Type} (s : Finset ι)
    (r : ι → K.E) (x : ι → B.A) :
    B.herm β y (∑ i ∈ s, r i • x i) = ∑ i ∈ s, K.c (r i) * B.herm β y (x i) := by

  simp only [GlobalTheory.UnitLemma.InvAlg.herm, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.smul_def, RingEquiv.map_mul B.σ, B.σ_alg, ← Algebra.smul_def, mul_smul_comm, map_smul, smul_eq_mul]

theorem gram_isometry_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → ∀ (B : GlobalTheory.UnitLemma.InvAlg K) (m : ℕ) (b : Module.Basis (Fin m) K.E B.A) (β : B.A) (f : B.A →ₗ[K.E] B.A), ((LinearMap.toMatrix b b f).map e)ᵀ * GlobalTheory.TwLat.gram e b β * ((LinearMap.toMatrix b b f).map e).map (cj w) = GlobalTheory.TwLat.gram e b β ↔ ∀ y z, B.herm β (f y) (f z) = B.herm β y z := by
  intro E _ _ _ w K e hec B m b β f
  set M := LinearMap.toMatrix b b f with hM
  have hf : ∀ i, f (b i) = ∑ k, M k i • b k := by
    intro i
    simp only [hM, LinearMap.toMatrix_apply]
    exact (b.sum_repr (f (b i))).symm
  have hent : ∀ i j, ((M.map e)ᵀ * gram e b β * (M.map e).map (cj w)) i j = e (B.herm β (f (b i)) (f (b j))) := by
    intro i j
    rw [hf i, hf j, herm_finsum_left]

    simp only [herm_finsum_right, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, gram, Matrix.of_apply,
    Finset.mul_sum, Finset.sum_mul, map_sum, map_mul, hec]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  constructor
  · intro h y z
    have hij : ∀ i j, B.herm β (f (b i)) (f (b j)) = B.herm β (b i) (b j) := by
      intro i j
      apply e.injective
      rw [← hent, h]
      rfl
    rw [← b.sum_repr y, ← b.sum_repr z]

    simp only [map_sum, map_smul, herm_finsum_left, herm_finsum_right, hij]
  · intro h
    ext i j
    rw [hent, h]
    rfl

theorem twCent_equiv_torus : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → (∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) → ∀ (B : GlobalTheory.UnitLemma.InvAlg K) (m : ℕ) (b : Module.Basis (Fin m) K.E B.A), ∀ u β : B.A, IsUnit β → B.σ β = β * ((-1) ^ (m - 1) * u) → Algebra.adjoin K.E {u} = ⊤ → IsUnit (GlobalTheory.TwLat.gram e b β) → ∃ φ : twCent (thL m w) (GlobalTheory.TwLat.dlt e b β) ≃* B.T, (∀ t : twCent (thL m w) (GlobalTheory.TwLat.dlt e b β), (t : GLw m w).val = GlobalTheory.TwLat.mulMat e b (((φ t : B.T) : B.Aˣ) : B.A)) ∧ ∀ t : twCent (thL m w) (GlobalTheory.TwLat.dlt e b β), ((t : GLw m w) ∈ cptPart (twCent (thL m w) (GlobalTheory.TwLat.dlt e b β)) ↔ ((φ t : B.T) : B.Aˣ) ∈ GlobalTheory.UnitLemma.intUnits K.O B.A) := by
  intro E _ _ _ hE w hw K e hec hint hval B m b u β hβu hβ hadj hG

  have hnd : ∀ y, (∀ z, B.herm β y z = 0) → y = 0 := by
    intro y hy
    have hsum : ∀ z, B.herm β y z = ∑ i, b.repr y i * B.herm β (b i) z := by
      intro z
      conv_lhs => rw [← b.sum_repr y]

      simp only [GlobalTheory.UnitLemma.InvAlg.herm, Finset.mul_sum, Finset.sum_mul, map_sum, mul_smul_comm,
      smul_mul_assoc, map_smul, smul_eq_mul]
    have h1 : Matrix.vecMul (fun i => e (b.repr y i)) (gram e b β) = 0 := by
      funext j
      have := congrArg e (hsum (b j))

      rw [hy, map_zero, map_sum] at this
      simp only [Matrix.vecMul, dotProduct, gram, Matrix.of_apply, Pi.zero_apply]
      rw [this]
      simp only [map_mul]
    have hGi : gram e b β * (gram e b β)⁻¹ = 1 :=
      Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hG)
    have h2 : (fun i => e (b.repr y i)) = 0 := by
      rw [← Matrix.vecMul_one (fun i => e (b.repr y i)), ← hGi, ← Matrix.vecMul_vecMul, h1, Matrix.zero_vecMul]
    have h3 : b.repr y = 0 := by
      ext i
      have := congrFun h2 i
      simpa using this
    simpa using h3

  have hT : ∀ t : B.Aˣ, t ∈ B.T → mulU e b t ∈ twCent (thL m w) (dlt e b β) := by
    intro t ht
    have ht' : (t : B.A) * B.σ (t : B.A) = 1 := ht
    rw [twCent_iff_gram E w hw K e B m b β hG]
    refine (gram_isometry_iff E w K e hec B m b β (LinearMap.mulLeft K.E (t : B.A))).2 fun y z => ?_
    simp only [LinearMap.mulLeft_apply, GlobalTheory.UnitLemma.InvAlg.herm]
    rw [map_mul B.σ, show β * ((t : B.A) * y) * (B.σ t * B.σ z) = β * y * B.σ z * ((t : B.A) * B.σ t) by ring,
      ht', mul_one]

  have hsurj : ∀ g : GLw m w, g ∈ twCent (thL m w) (dlt e b β) → ∃ t : B.Aˣ, t ∈ B.T ∧ mulU e b t = g := by
    intro g hg
    have hg1 := (twCent_iff_gram E w hw K e B m b β hG g).1 hg
    let em := (e.symm : w.adicCompletion E →+* K.E).mapMatrix (m := Fin m)
    let f : B.A →ₗ[K.E] B.A := Matrix.toLin b b (em g.val)
    have hfM : (LinearMap.toMatrix b b f).map e = g.val := by
      simp only [f, LinearMap.toMatrix_toLin, em, RingHom.mapMatrix_apply, Matrix.map_map]
      ext i j; simp
    have hiso := (gram_isometry_iff E w K e hec B m b β f).1 (by rw [hfM]; exact hg1)
    have hfs : Function.Surjective f := by
      intro y
      refine ⟨Matrix.toLin b b (em (g⁻¹ : GLw m w).val) y, ?_⟩
      rw [← LinearMap.comp_apply, ← Matrix.toLin_mul, ← map_mul, Units.mul_inv, map_one, Matrix.toLin_one,
        LinearMap.id_apply]
    obtain ⟨a, haT, hfa⟩ := GlobalTheory.T.traceForm_linearIsometry_eq_mul_normOneTorus K B (m - 1) u β hβ hadj hnd f hfs hiso
    refine ⟨a, haT, Units.ext ?_⟩
    rw [mulU_val, ← hfM]
    have : LinearMap.mulLeft K.E (a : B.A) = f := LinearMap.ext fun y => (hfa y).symm
    rw [mulMat, this]
  let ψ : B.T →* twCent (thL m w) (dlt e b β) :=
    { toFun := fun t => ⟨mulU e b t, hT t t.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun s t => Subtype.ext (by simp) }
  have hψ : Function.Bijective ψ := by
    refine ⟨fun s t h => Subtype.ext (mulU_injective e b (congrArg Subtype.val h)), ?_⟩
    rintro ⟨g, hg⟩
    obtain ⟨t, ht, rfl⟩ := hsurj g hg
    exact ⟨⟨t, ht⟩, rfl⟩
  let φ := (MulEquiv.ofBijective ψ hψ).symm
  have hφ : ∀ t : twCent (thL m w) (dlt e b β), (t : GLw m w) = mulU e b ((φ t : B.T) : B.Aˣ) := by
    intro t
    have := congrArg Subtype.val ((MulEquiv.ofBijective ψ hψ).apply_symm_apply t)
    exact this.symm
  refine ⟨φ, fun t => by rw [hφ t, mulU_val], fun t => ?_⟩

  have hset : {t | t ∈ twCent (thL m w) (dlt e b β) ∧
      IsCompact (closure (Subgroup.zpowers t : Set (GLw m w)))} =
      (((GlobalTheory.UnitLemma.intUnits K.O B.A) ⊓ B.T).map (mulU e b) : Set (GLw m w)) := by
    ext g
    constructor
    · rintro ⟨hg, hc⟩
      obtain ⟨a, haT, rfl⟩ := hsurj g hg
      exact ⟨a, ⟨GlobalTheory.T.integralUnits_of_isCompact_closure_zpowers_mul E hE w hw K e hec hint hval B m b a hc, haT⟩, rfl⟩
    · rintro ⟨a, ⟨hai, haT⟩, rfl⟩
      exact ⟨hT a haT, GlobalTheory.T.isCompact_closure_zpowers_mul_integralUnit E hE w hw K e hec hint hval B m b a hai⟩
  rw [cptPart, hset, Subgroup.closure_eq, hφ t]
  constructor
  · rintro ⟨a, ⟨hai, -⟩, ha⟩
    rwa [← mulU_injective e b ha]
  · intro h
    exact ⟨_, ⟨h, (φ t).2⟩, rfl⟩

end GlobalTheory.TwLat
end
end

section

open NumberField IsDedekindDomain Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.DblEval

theorem _root_.GlobalTheory.T.adelic_schwartz_function_factorizable_sum : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (a : (κ → Af F) → ℂ), a ∈ SB (κ → Af F) → ∃ (m : ℕ) (φ : Fin m → ∀ v : Pl (F := F), (κ → Fv F v) → ℂ), (∀ j v, φ j v ∈ SB (κ → Fv F v)) ∧ (∀ j, ∀ᶠ v in cofinite, φ j v = stdInd F κ v) ∧ ∀ x, a x = ∑ j, ∏ᶠ v, φ j v fun i => evalV F v (x i) := by
  first | exact @GlobalTheory.SBRestrProd.sb_eq_sum_restrProd | exact GlobalTheory.SBRestrProd.sb_eq_sum_restrProd | (intros; apply GlobalTheory.SBRestrProd.sb_eq_sum_restrProd <;> assumption)
end

section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

namespace GlobalTheory.AutGrowth

theorem word_eq_smoothing_of_reproduced : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (ν : Measure (Lie E a)) [ν.IsAddHaarMeasure] (α : Lie E a → ℂ), IsTest (invSet E a) α → ∀ φ : Sm E a,
    smoothing ν α φ.1 = φ.1 → ∀ l : List (Lie E a), ∃ β : Lie E a → ℂ, IsTest (invSet E a) β ∧
      ((l.map (lie E a)).prod φ).1 = smoothing ν β φ.1 := by
  intro E _ _ _ a ν _ α hα φ hφ l
  induction l with
  | nil => exact ⟨α, hα, by simpa using hφ.symm⟩
  | cons X l ih =>
    obtain ⟨β, hβ, e⟩ := ih
    refine ⟨dens X β, isTest_dens X hβ, ?_⟩
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply]
    funext g
    change lieD X ((l.map (lie E a)).prod φ).1 g = _
    rw [e]
    exact lieD_smoothing ν hβ φ.2 X g

end GlobalTheory.AutGrowth
end

section

noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory Filter Topology

namespace GlobalTheory.AutGrowth

theorem smoothing_growth_exponent : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (ν : Measure (Lie E a)) [ν.IsAddHaarMeasure] (α : Lie E a → ℂ), IsTest (invSet E a) α →
    ∀ (f : GA E a → ℂ) (C : ℝ) (N : ℕ), (∀ y, ‖f (infGL E a y)‖ ≤ C * height y ^ N) →
    ∃ C' : ℝ, ∀ y, ‖smoothing ν α f (infGL E a y)‖ ≤ C' * height y ^ N := by
  intro E _ _ _ a ν _ α hα f C N hC
  have C0 : 0 ≤ C := by
    have h1 := (norm_nonneg _).trans (hC 1)
    have hp : 0 < height (1 : GL (Fin a) (Cinf E)) ^ N :=
      pow_pos (by linarith [one_le_height (1 : GL (Fin a) (Cinf E))]) N
    exact nonneg_of_mul_nonneg_left h1 hp
  have hK : IsCompact (tsupport α) := hα.2.1
  obtain ⟨M, M0, hM⟩ : ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ tsupport α, ‖x‖ ≤ M ∧ ‖toL (Matrix.of x)⁻¹‖ ≤ M := by
    obtain ⟨M1, h1⟩ := hK.exists_bound_of_continuousOn continuous_id.continuousOn
    obtain ⟨M2, h2⟩ := hK.exists_bound_of_continuousOn (continuousOn_toL_inv.mono hα.2.2)
    refine ⟨max 0 (max M1 M2), le_max_left _ _, fun x hx => ⟨?_, ?_⟩⟩
    · exact (h1 x hx).trans ((le_max_left _ _).trans (le_max_right _ _))
    · exact (h2 x hx).trans ((le_max_right _ _).trans (le_max_right _ _))
  set c : ℝ := 1 + a * M with hc
  have hc1 : 1 ≤ c := by
    have : 0 ≤ (a : ℝ) * M := by positivity
    linarith
  refine ⟨(∫ x, ‖α x‖ ∂ν) * C * c ^ N, fun y => ?_⟩
  have hb : ∀ x, ‖α x * chart f (infGL E a y) x‖ ≤ ‖α x‖ * (C * c ^ N * height y ^ N) := by
    intro x
    by_cases hx : x ∈ tsupport α
    · obtain ⟨u, hu⟩ : IsUnit (Matrix.of x) := hα.2.2 hx
      have hxu : x = toL u.val := by rw [hu]; rfl
      subst hxu
      obtain ⟨m1, m2⟩ := hM _ hx
      have m2' : ‖toL (u⁻¹).val‖ ≤ M := by rw [Matrix.coe_units_inv]; exact m2
      rw [norm_mul]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      rw [chart_val, ← map_mul]
      refine (hC (y * u)).trans ?_
      have hh : height (y * u) ≤ c * height y := by
        have e2 : ((y * u)⁻¹ : GL (Fin a) (Cinf E)).val = (u⁻¹).val * (y⁻¹).val := by
          rw [_root_.mul_inv_rev]; rfl
        have p1 := norm_toL_mul_le y.val u.val
        have p2 := norm_toL_mul_le (u⁻¹).val (y⁻¹).val
        have n1 := norm_nonneg (toL y.val)
        have n2 := norm_nonneg (toL (y⁻¹).val)
        have q1 : (a : ℝ) * (‖toL y.val‖ * ‖toL u.val‖) ≤ a * M * ‖toL y.val‖ := by
          calc (a : ℝ) * (‖toL y.val‖ * ‖toL u.val‖) ≤ a * (‖toL y.val‖ * M) :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left m1 n1) (Nat.cast_nonneg a)
            _ = a * M * ‖toL y.val‖ := by ring
        have q2 : (a : ℝ) * (‖toL (u⁻¹).val‖ * ‖toL (y⁻¹).val‖) ≤ a * M * ‖toL (y⁻¹).val‖ := by
          rw [← mul_assoc]
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left m2' (Nat.cast_nonneg a)) n2
        have aM : 0 ≤ (a : ℝ) * M := by positivity
        unfold height
        rw [show toL (y * u).val = toL (y.val * u.val) from rfl, e2, hc]
        nlinarith
      calc C * height (y * u) ^ N ≤ C * (c * height y) ^ N :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith [one_le_height (y * u)]) hh N) C0
        _ = C * c ^ N * height y ^ N := by rw [mul_pow, mul_assoc]
    · rw [image_eq_zero_of_notMem_tsupport hx]
      simp
  change ‖∫ x, α x * chart f (infGL E a y) x ∂ν‖ ≤ _
  have hi : Integrable (fun x => ‖α x‖) ν :=
    hα.1.continuous.norm.integrable_of_hasCompactSupport hα.2.1.norm
  refine (norm_integral_le_of_norm_le (hi.mul_const _) (.of_forall hb)).trans (le_of_eq ?_)
  rw [integral_mul_const]
  ring

end GlobalTheory.AutGrowth
end
end

section

open MeasureTheory Matrix
open scoped Classical

theorem _root_.GlobalTheory.T.doubleCosetVolumeWeightedSum_conj : ∀ (H : Type) [Group H] (T L U : Subgroup H) (Ψ : H → ℂ) (c : H),
  (∀ s ∈ T, ∀ t ∈ T, s * t = t * s) → (∀ t ∈ T, ∀ x, Ψ (t * x) = Ψ x) → (∀ l ∈ L, ∀ x, Ψ (x * l) = Ψ x) →
  GlobalTheory.OrbDesc.dsum T L U Ψ = GlobalTheory.OrbDesc.dsum (T.map (MulAut.conj c).toMonoidHom) (L.map (MulAut.conj c).toMonoidHom)
    (U.map (MulAut.conj c).toMonoidHom) (fun x => Ψ (c⁻¹ * x * c)) := by
  first | exact @GlobalTheory.OrbDesc.dsum_conj | exact GlobalTheory.OrbDesc.dsum_conj | (intros; apply GlobalTheory.OrbDesc.dsum_conj <;> assumption)
end

section

open MeasureTheory Matrix
open scoped Classical

theorem _root_.GlobalTheory.T.orbit_sum_vanishes_of_parabolic_sums : ∀ (H : Type) [Group H] (T P L U : Subgroup H) (Ψ : H → ℂ), T ≤ P →
  (∀ s ∈ T, ∀ t ∈ T, s * t = t * s) → (∀ t ∈ T, ∀ x, Ψ (t * x) = Ψ x) → (∀ l ∈ L, ∀ x, Ψ (x * l) = Ψ x) →
  (∀ y : H, GlobalTheory.OrbDesc.dsum T (P ⊓ L.map (MulAut.conj y).toMonoidHom) U (fun x => if x ∈ P then Ψ (x * y) else 0) = 0) →
  GlobalTheory.OrbDesc.dsum T L U Ψ = 0 := by
  first | (exact @GlobalTheory.OrbDesc.dsum_eq_zero_of_par) | (exact GlobalTheory.OrbDesc.dsum_eq_zero_of_par) | (intros; apply GlobalTheory.OrbDesc.dsum_eq_zero_of_par  <;> assumption)
end

section

open MeasureTheory Matrix
open scoped Classical

theorem _root_.GlobalTheory.T.dsum_eq_zero_of_fibre_sums' : ∀ (H : Type) [Group H] (T P N L U : Subgroup H) (Ψ : H → ℂ), T ≤ P → N ≤ P → L ≤ P →
  (∀ p ∈ P, ∀ n ∈ N, p * n * p⁻¹ ∈ N) → (∀ s ∈ T, ∀ t ∈ T, s * t = t * s) →
  (∀ t ∈ T, ∀ x, Ψ (t * x) = Ψ x) → (∀ l ∈ L, ∀ x, Ψ (x * l) = Ψ x) → (∀ x, x ∉ P → Ψ x = 0) →
  (∀ x ∈ P, (T ⊓ L.map (MulAut.conj x).toMonoidHom).relIndex (T ⊓ (L ⊔ N).map (MulAut.conj x).toMonoidHom) ≠ 0) →
  (∀ m ∈ P, ∑ᶠ q : H ⧸ (N ⊓ L), (if Quotient.out q ∈ N then Ψ (m * Quotient.out q) else 0) = 0) →
  GlobalTheory.OrbDesc.dsum T L U Ψ = 0 := by
  first | (exact @GlobalTheory.OrbDesc.dsum_eq_zero_of_fibre_sums) | (exact GlobalTheory.OrbDesc.dsum_eq_zero_of_fibre_sums) | (intros; apply GlobalTheory.OrbDesc.dsum_eq_zero_of_fibre_sums  <;> assumption)
end

section


theorem _root_.GlobalTheory.T.schwartz_functional_depends_on_value_at_zero : ∀ {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    (ℓ : SchwartzMap Y ℂ →L[ℂ] ℂ),
    (∀ L : Y →ₗ[ℝ] ℝ, ∀ f g : SchwartzMap Y ℂ, ⇑g = (fun x => GlobalTheory.ArchSch.ech (L x) * f x) → ℓ g = ℓ f) →
    ∀ f g : SchwartzMap Y ℂ, f 0 = g 0 → ℓ f = ℓ g := by
  first | exact @GlobalTheory.CharInvAtZero.eq_of_eq_zero | exact GlobalTheory.CharInvAtZero.eq_of_eq_zero | (intros; apply GlobalTheory.CharInvAtZero.eq_of_eq_zero <;> assumption)
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThetaDenom
open scoped TensorProduct NNReal Matrix

namespace GlobalTheory.ThetaDenom


open Formalism.UG in
theorem transport_denom : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ}
    (e : Matrix (Fin n) (Fin d) (AF F ⊗[F] E) ≃ₗ[AF F] (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F)),
    ∃ C : ℝ, ∀ (g : GL (Fin n) (AF F ⊗[F] E)) (h : GL (Fin d) (AF F ⊗[F] E)), ∃ N : ℕ, 0 < N ∧
      (N : ℝ) ≤ C * ((heightGL F g : ℝ) * heightGL F h) ∧
      ∀ (M : ℕ) (y : Fin n × Fin d → AF F), IsMulInt F (M * N) y →
        IsMulInt F M (e ((g : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) * e.symm (0, y) * (h : Matrix (Fin d) (Fin d) (AF F ⊗[F] E))ᵀ)).1 ∧
        IsMulInt F M (e ((g : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) * e.symm (0, y) * (h : Matrix (Fin d) (Fin d) (AF F ⊗[F] E))ᵀ)).2 :=
  @GlobalTheory.ThetaLevel.transport_denom

end GlobalTheory.ThetaDenom

end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.exists_translationInvariant_doubledForm_conjProduct_ne_zero : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ], ∀ Ψ ∈ schA F κ, Ψ ≠ 0 →
    ∃ l ∈ (adeleClass F).adm (κ ⊕ κ), (∀ φ ∈ schA F (κ ⊕ κ), ∀ (φ' : (κ ⊕ κ → AF F) → ℂ) (x : κ → AF F),
      (∀ u, φ' (Sum.elim u u) = φ (Sum.elim (u + x) (u + x))) → l φ' = l φ) ∧ l (GlobalTheory.InertDbl.dblFun Ψ) ≠ 0 := by
  first | exact @GlobalTheory.DblDiagForm.exists_form | exact GlobalTheory.DblDiagForm.exists_form | (intros; apply GlobalTheory.DblDiagForm.exists_form <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.doubledStabilizer_weilOperator_transports_latticeEigen : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ (d' : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J)) (Fin a × Fin (a + a'))),
    (∀ x : Matrix (Fin a) (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), d'.e xᵀ = G.M.co.e x) →
    ∀ (dd : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J))) ((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')))),
    IsDblCoord (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) d' dd →
    ∀ θ : 𝓞 E, (θ : E) + σ θ = 1 →
    (∀ γ ∈ latAtV G.V G.W v, Acts (evFin F v) (G.M.co.rho B.ψ γ) (G.M.vac v)
        (B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) γ γ) • G.M.vac v)) →
    ∀ (omd : GlobalTheory.DblVac.UD σ G.V →* Module.End ℂ (((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')) → AF F) → ℂ)),
    IsUWeilSplit (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (adeleClass F) B.ψ (-1 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J)) dd (X.β / X.α) (diagCols (Fin a)) omd →
    ∀ g ∈ GlobalTheory.DblVac.KD σ G.V v, ∀ φ ∈ SB ((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')) → Fv F v), ∀ φ₁ ∈ SB ((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')) → Fv F v),
    (∀ w₁ ∈ latAtV G.V G.W v, ∀ w₂ ∈ latAtV G.V G.W v,
      Acts (evFin F v) (dd.rho B.ψ (Matrix.fromCols w₁ᵀ w₂ᵀ)) φ
        (B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J))
          (Matrix.fromCols w₁ᵀ w₂ᵀ) (Matrix.fromCols w₁ᵀ w₂ᵀ)) • φ)) → Acts (evFin F v) (omd g) φ φ₁ →
    (∀ w₁ ∈ latAtV G.V G.W v, ∀ w₂ ∈ latAtV G.V G.W v,
      Acts (evFin F v) (dd.rho B.ψ (Matrix.fromCols w₁ᵀ w₂ᵀ)) φ₁
        (B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J))
          (Matrix.fromCols w₁ᵀ w₂ᵀ) (Matrix.fromCols w₁ᵀ w₂ᵀ)) • φ₁)) := by
  first | exact @GlobalTheory.DblVacTransport.transport | exact GlobalTheory.DblVacTransport.transport | (intros; apply GlobalTheory.DblVacTransport.transport <;> assumption)
end
