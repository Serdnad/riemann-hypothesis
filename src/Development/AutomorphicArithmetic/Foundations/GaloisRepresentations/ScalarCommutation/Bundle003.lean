module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1742
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFixedIff
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.Bundle002
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.Bundle003
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.Bundle004
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle059
import GroundTheory.LocalFields.PadicLogSeries
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle017
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PLocComm
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.TypeStar
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep
open GlobalTheory.SplitPts (conjE)

namespace UpperTheory.Gal.Spc

section LinAlg

variable {K : Type*} [Field K] {m : ℕ}

private theorem sep_of_mul_closed [IsAlgClosed K] {M N : Matrix (Fin m) (Fin m) K} {a : K} (ha : a ≠ 0)
    (h : N * M = a • (1 : Matrix (Fin m) (Fin m) K)) (hM : M.charpoly.Separable) : N.charpoly.Separable := by
  classical
  have hdet : M.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det h
    rw [Matrix.det_mul, h0, mul_zero, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at this
    by_cases hm : m = 0
    · subst hm
      simp [Matrix.det_isEmpty] at h0
    · exact pow_ne_zero _ ha this.symm
  have hroot : ∀ x ∈ M.charpoly.roots, x ≠ 0 ∧ a / x ∈ N.charpoly.roots := by
    intro x hx
    have hx0 : M.charpoly.eval x = 0 := (Polynomial.mem_roots'.1 hx).2
    rw [Matrix.eval_charpoly] at hx0
    have hne : x ≠ 0 := by
      rintro rfl
      apply hdet
      simpa [Matrix.det_neg] using hx0
    refine ⟨hne, Polynomial.mem_roots'.2 ⟨(Matrix.charpoly_monic N).ne_zero, ?_⟩⟩
    show N.charpoly.eval (a / x) = 0
    rw [Matrix.eval_charpoly]
    have e : Matrix.scalar (Fin m) (a / x) - N = (-x⁻¹) • (N * (Matrix.scalar (Fin m) x - M)) := by
      rw [Matrix.mul_sub, h, Matrix.scalar_apply, Matrix.scalar_apply]
      ext i j
      by_cases hij : i = j <;> simp [hij, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.one_apply] <;> field_simp <;> ring
    rw [e, Matrix.det_smul, Matrix.det_mul, hx0, mul_zero, mul_zero]
  have hnd : M.charpoly.roots.Nodup := Polynomial.nodup_roots hM
  have hcM : M.charpoly.roots.card = m := by
    have := Polynomial.splits_iff_card_roots.1 (IsAlgClosed.splits M.charpoly)
    rw [this, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hcN : N.charpoly.roots.card = m := by
    have := Polynomial.splits_iff_card_roots.1 (IsAlgClosed.splits N.charpoly)
    rw [this, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hinj : Set.InjOn (fun x : K => a / x) (M.charpoly.roots.toFinset : Set K) := by
    intro x hx y hy hxy
    have hx0 := (hroot x (by simpa using hx)).1
    have hy0 := (hroot y (by simpa using hy)).1
    have hxy' : a * x⁻¹ = a * y⁻¹ := by simpa only [div_eq_mul_inv] using hxy
    exact inv_injective (mul_left_cancel₀ ha hxy')
  have hsub : M.charpoly.roots.toFinset.image (fun x : K => a / x) ⊆ N.charpoly.roots.toFinset := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
    exact Multiset.mem_toFinset.2 (hroot x (Multiset.mem_toFinset.1 hx)).2
  have hle : m ≤ N.charpoly.roots.toFinset.card := by
    have h1 := Finset.card_le_card hsub
    rwa [Finset.card_image_of_injOn hinj, Multiset.toFinset_card_of_nodup hnd, hcM] at h1
  have hndN : N.charpoly.roots.Nodup := by
    rw [← Multiset.dedup_card_eq_card_iff_nodup]
    refine le_antisymm (Multiset.card_le_card (Multiset.dedup_le _)) ?_
    rw [hcN]
    exact hle
  exact (Polynomial.nodup_roots_iff_of_splits (Matrix.charpoly_monic N).ne_zero (IsAlgClosed.splits _)).1 hndN

private theorem sep_of_mul {M N : Matrix (Fin m) (Fin m) K} {a : K} (ha : a ≠ 0)
    (h : N * M = a • (1 : Matrix (Fin m) (Fin m) K)) (hM : M.charpoly.Separable) : N.charpoly.Separable := by
  have h' : N.map (algebraMap K (AlgebraicClosure K)) * M.map (algebraMap K (AlgebraicClosure K)) =
      algebraMap K (AlgebraicClosure K) a • (1 : Matrix (Fin m) (Fin m) (AlgebraicClosure K)) := by
    rw [← Matrix.map_mul, h]
    ext i j
    by_cases hij : i = j <;> simp [hij, Matrix.one_apply]
  have h2 := sep_of_mul_closed (K := AlgebraicClosure K) (a := algebraMap K (AlgebraicClosure K) a)
    (by simpa using ha) h' (by rw [Matrix.charpoly_map]; exact hM.map)
  rw [Matrix.charpoly_map] at h2
  exact (Polynomial.separable_map _).1 h2

end LinAlg

end UpperTheory.Gal.Spc

theorem UpperTheory.Gal.Spc.sepConj :
    UpperTheory.Gal.Spc.SepConj := by
  intro E _ _ _ n g w hw
  have h0 : (g.1.1.val.map (conjFin (conjE E)))ᵀ * g.1.1.val =
      GroundTheory.Global.AdeleBaseChange.finiteAdeleMap ℚ E (g.1.2 : UpperTheory.Gal.CertificateRingHomMap.AfQ) • (1 : Matrix (Fin n) (Fin n) _) := g.2
  have h1 := congrArg (RingHom.mapMatrix (pLoc E w)) h0
  rw [map_mul] at h1
  have ha : pLoc E w (GroundTheory.Global.AdeleBaseChange.finiteAdeleMap ℚ E (g.1.2 : UpperTheory.Gal.CertificateRingHomMap.AfQ)) ≠ 0 :=
    ((g.1.2.isUnit.map (GroundTheory.Global.AdeleBaseChange.finiteAdeleMap ℚ E)).map (pLoc E w)).ne_zero
  have h2 : (((UpperTheory.Gal.CertificateRingHomMap.comp (UpperTheory.Gal.CertificateRingHomMap.cj w) g).val.map (conjLoc (conjE E) w))ᵀ) * (UpperTheory.Gal.CertificateRingHomMap.comp w g).val =
      pLoc E w (GroundTheory.Global.AdeleBaseChange.finiteAdeleMap ℚ E (g.1.2 : UpperTheory.Gal.CertificateRingHomMap.AfQ)) • (1 : Matrix (Fin n) (Fin n) _) := by
    refine Eq.trans ?_ (h1.trans ?_)
    · congr 1
    · ext i j
      by_cases hij : i = j <;> simp [hij, Matrix.one_apply]
  have h3 := UpperTheory.Gal.Spc.sep_of_mul ha h2 hw
  rw [Matrix.charpoly_transpose, Matrix.charpoly_map] at h3
  exact (Polynomial.separable_map _).1 h3
end

section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc comp cj lev GLw mat)
open UpperTheory.Gal.LocalSmoothExtension UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl
open scoped TensorProduct Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Gal.Spc

private def cnj {k : Type} [Field k] {n : ℕ} (a : GL (Fin n) k) : Matrix (Fin n) (Fin n) k →+* Matrix (Fin n) (Fin n) k where
  toFun x := (a⁻¹).val * x * a.val
  map_one' := by simp
  map_mul' x y := by
    have h : a.val * (a⁻¹).val = 1 := Units.mul_inv a
    calc (a⁻¹).val * (x * y) * a.val = (a⁻¹).val * x * 1 * y * a.val := by simp [Matrix.mul_assoc]
      _ = _ := by rw [← h]; simp only [Matrix.mul_assoc]
  map_zero' := by simp
  map_add' x y := by simp [Matrix.mul_add, Matrix.add_mul]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {A : Arith E} {n p : ℕ} [Fact p.Prime] {S : Setup A n p}

private def rd (T : Tr S) (w : Plc E) (hp : (p : 𝓞 E) ∉ w.asIdeal) : AfP p ⊗[ℚ] E →+* w.adicCompletion E :=
  RingHom.liftOfSurjective T.Φ T.Φ_surj ⟨pLoc E w, fun x hx => by
    have := (T.Φ_ker x).1 hx w hp
    exact this⟩

private theorem rd_Φ (T : Tr S) (w : Plc E) (hp : (p : 𝓞 E) ∉ w.asIdeal) (x : Af E) : rd T w hp (T.Φ x) = pLoc E w x :=
  RingHom.liftOfRightInverse_comp_apply _ _ _ _ _

private def aw (T : Tr S) (w : Plc E) : GL (Fin n) (w.adicCompletion E) := GeneralLinearGroup.map (pLoc E w) T.a

private theorem cnj_apply {k : Type} [Field k] {n : ℕ} (a : GL (Fin n) k) (x : Matrix (Fin n) (Fin n) k) :
    cnj a x = (a⁻¹).val * x * a.val := rfl

private theorem alg_mat (n : ℕ) (w : Plc E) (r : E) :
    (algebraMap E (Matrix (Fin n) (Fin n) E) r).map (algebraMap E (w.adicCompletion E)) =
      algebraMap E (Matrix (Fin n) (Fin n) (w.adicCompletion E)) r := by
  apply Matrix.ext
  intro i k
  rw [Matrix.map_apply, Matrix.algebraMap_matrix_apply, Matrix.algebraMap_matrix_apply]
  split_ifs <;> simp

private theorem cnj_alg {w : Plc E} (a : GL (Fin n) (w.adicCompletion E)) (r : E) :
    cnj a (algebraMap E (Matrix (Fin n) (Fin n) (w.adicCompletion E)) r) =
      algebraMap E (Matrix (Fin n) (Fin n) (w.adicCompletion E)) r := by
  rw [cnj_apply, Algebra.algebraMap_eq_smul_one, Matrix.mul_smul, smul_mul_assoc, Matrix.mul_one,
    Units.inv_mul]

private def iotaAt (S : Setup A n p) (w : Plc E) (a : GL (Fin n) (w.adicCompletion E)) :
    S.G.C →ₐ[S.G.F] Matrix (Fin S.G.n) (Fin S.G.n) (w.adicCompletion E) :=
  { (cnj a).comp (RingHom.mapMatrix (algebraMap E (w.adicCompletion E))) with
    commutes' := fun r => (congrArg (cnj a) (alg_mat n w r)).trans (cnj_alg a r) }

private def kap0 (T : Tr S) (w : Plc E) (hp : (p : 𝓞 E) ∉ w.asIdeal) :
    AfP p ⊗[ℚ] Matrix (Fin n) (Fin n) E →+* Matrix (Fin n) (Fin n) (w.adicCompletion E) :=
  ((cnj (aw T w)).comp (RingHom.mapMatrix (rd T w hp))).comp (T.μ : _ →+* _)

private theorem rd_one (T : Tr S) (w : Plc E) (hp : (p : 𝓞 E) ∉ w.asIdeal) (x : E) :
    rd T w hp ((1 : AfP p) ⊗ₜ x) = algebraMap E (w.adicCompletion E) x := by
  rw [← T.Φ_E x, rd_Φ]
  rfl

private theorem map_mu (T : Tr S) (w : Plc E) (hp : (p : 𝓞 E) ∉ w.asIdeal) (y : Matrix (Fin n) (Fin n) E) :
    (T.μ ((1 : AfP p) ⊗ₜ[ℚ] y)).map (rd T w hp) = y.map (algebraMap E (w.adicCompletion E)) := by
  apply Matrix.ext
  intro i k
  rw [Matrix.map_apply, T.mu, rd_one, Matrix.map_apply]

private theorem map_Φ (T : Tr S) (w : Plc E) (hp : (p : 𝓞 E) ∉ w.asIdeal) (M : Matrix (Fin n) (Fin n) (Af E)) :
    (M.map T.Φ).map (rd T w hp) = M.map (pLoc E w) := by
  apply Matrix.ext
  intro i k
  rw [Matrix.map_apply, Matrix.map_apply, Matrix.map_apply, rd_Φ]

private theorem at_eq (T : Tr S) (w : Plc E) (hp : (p : 𝓞 E) ∉ w.asIdeal) (g : GUf E n) :
    cnj (aw T w) ((T.μ (S.mx (T.j g))).map (rd T w hp)) = (comp w g).val := by
  have h2 : aw T w * comp w g * (aw T w)⁻¹ = GeneralLinearGroup.map (pLoc E w) (T.a * mat g * T.a⁻¹) := by
    rw [map_mul, map_mul, map_inv]
    rfl
  have h1 : (GeneralLinearGroup.map (pLoc E w) (T.a * mat g * T.a⁻¹)).val = (T.a * mat g * T.a⁻¹).val.map (pLoc E w) := rfl
  rw [T.j_mx g, map_Φ, ← h1, ← h2, cnj_apply]
  simp [Matrix.mul_assoc]

end UpperTheory.Gal.Spc

open UpperTheory.Gal.Spc in
theorem UpperTheory.Gal.Spc.plTr :
    UpperTheory.Gal.Spc.PlTr := by
  intro E _ _ _ A n p _ S T w hp
  refine ⟨⟨kap0 T w hp, iotaAt S w (aw T w), fun y => ?_⟩, fun g => at_eq T w hp g⟩
  exact congrArg (cnj (aw T w)) (map_mu T w hp y)
end
end

section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc comp cj lev GLw)
open UpperTheory.Gal.LocalSmoothExtension UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl
open scoped TensorProduct Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Gal.Spc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {A : Arith E} {n p : ℕ} [Fact p.Prime] {S : Setup A n p}
variable {x : E} {U : Submodule ℂ (UA E n → ℂ)} {w₀ : Plc E} {Up : Plc E → Prop}

private theorem cont_comp (w : Plc E) : Continuous (comp w : GUf E n → GL (Fin n) (w.adicCompletion E)) :=
  (Continuous.units_map _ (continuous_id.matrix_map (RestrictedProduct.continuous_eval w))).comp
    (continuous_fst.comp continuous_subtype_val)

private theorem th_eq (F : Frame S) (g : GUf E n) : F.th g = UpperTheory.Gal.CertificateRingHomMap.th g :=
  Subtype.ext (Prod.ext (Units.ext ((F.th_mat g).trans (UpperTheory.Gal.CertificateRingHomMap.invT_val _).symm)) (F.th_sim g))

private theorem pr_loc_one {F : Frame S} {w u : Spl E p} {L : Loc S.G.GAf (GLw n w.1)} {L' : Loc S.G.GAf (GLw n u.1)}
    (hf : IsFac F w L) (hf' : IsFac F u L') (h : GlobalTheory.Cong.Apart w.1 u.1) (y : GLw n u.1) : L.pr (L'.loc y) = 1 := by
  rw [hf'.2, hf.1, UpperTheory.Gal.CertificateRingHomMap.comp_loc_of_apart u.2.1 h]

private theorem fac_apart {F : Frame S} {w u : Spl E p} {L : Loc S.G.GAf (GLw n w.1)} {L' : Loc S.G.GAf (GLw n u.1)}
    (hf : IsFac F w L) (hf' : IsFac F u L') (h : GlobalTheory.Cong.Apart w.1 u.1) : L.Apart L' :=
  ⟨pr_loc_one hf hf' h, pr_loc_one hf' hf (Ne.symm h)⟩

private theorem exists_prime_mem (w : Plc E) : ∃ q : ℕ, q.Prime ∧ (q : 𝓞 E) ∈ w.asIdeal :=
  _root_.UpperTheory.Reformulated.B.Qk68.exists_prime_mem w

private theorem val_lt_one {w : Plc E} {q : ℕ} (hq : (q : 𝓞 E) ∈ w.asIdeal) : Valued.v (q : w.adicCompletion E) < 1 := by
  have h := (HeightOneSpectrum.valuation_lt_one_iff_mem (K := E) w (q : 𝓞 E)).2 hq
  have e : ((q : ℕ) : w.adicCompletion E) = algebraMap E (w.adicCompletion E) (algebraMap (𝓞 E) E (q : 𝓞 E)) := by
    rw [map_natCast, map_natCast]
  rw [e]
  exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _).trans_lt h

private theorem mul_mem_of_dvd {w : Plc E} {a b : ℕ} (h : a ∣ b) {y : w.adicCompletion E}
    (hy : (a : w.adicCompletion E) * y ∈ w.adicCompletionIntegers E) : (b : w.adicCompletion E) * y ∈ w.adicCompletionIntegers E := by
  obtain ⟨d, rfl⟩ := h
  rw [Nat.cast_mul, mul_comm (a : w.adicCompletion E), mul_assoc]
  exact mul_mem (natCast_mem _ d) hy

private theorem exists_pow {T : Type} [TopologicalSpace T] {w : Plc E} {q : ℕ} (hq : (q : 𝓞 E) ∈ w.asIdeal) {C : Set T}
    (hC : IsCompact C) {f : T → w.adicCompletion E} (hf : Continuous f) :
    ∃ m : ℕ, ∀ t ∈ C, ((q ^ m : ℕ) : w.adicCompletion E) * f t ∈ w.adicCompletionIntegers E := by
  have ho : IsOpen (w.adicCompletionIntegers E : Set (w.adicCompletion E)) := Valued.isOpen_valuationSubring _
  obtain ⟨m, hm⟩ := hC.elim_directed_cover
    (fun m : ℕ => {t | ((q ^ m : ℕ) : w.adicCompletion E) * f t ∈ w.adicCompletionIntegers E})
    (fun m => ho.preimage (continuous_const.mul hf)) (fun t _ => by
      rw [Set.mem_iUnion]
      by_cases h0 : Valued.v (f t) = 0
      · refine ⟨0, ?_⟩
        show Valued.v (_ * f t) ≤ 1
        rw [map_mul, h0, mul_zero]
        exact zero_le_one
      · obtain ⟨m, hm⟩ := exists_pow_lt₀ (val_lt_one hq) (Units.mk0 _ h0)⁻¹
        refine ⟨m, ?_⟩
        show Valued.v (_ * f t) ≤ 1
        rw [map_mul, Nat.cast_pow, map_pow]
        rw [Units.val_inv_eq_inv_val, Units.val_mk0] at hm
        calc _ ≤ (Valued.v (f t))⁻¹ * Valued.v (f t) := mul_le_mul' hm.le le_rfl
          _ = 1 := inv_mul_cancel₀ h0)
    (Monotone.directed_le fun a b hab t ht => mul_mem_of_dvd (pow_dvd_pow q hab) ht)
  exact ⟨m, fun t ht => hm ht⟩

private theorem bound_at (F : Frame S) {C : Set (GUf E n)} (hC : IsCompact C) (w : Plc E) :
    ∃ c : ℕ, 0 < c ∧ c.Coprime p ∧ ((p : 𝓞 E) ∉ w.asIdeal → ∀ t ∈ C, ∀ i k,
      (c : w.adicCompletion E) * F.cmp w (UpperTheory.Gal.CertificateRingHomMap.th t) i k ∈ w.adicCompletionIntegers E) := by
  by_cases hp : (p : 𝓞 E) ∈ w.asIdeal
  · exact ⟨1, one_pos, Nat.coprime_one_left p, fun h => absurd hp h⟩
  obtain ⟨q, hq, hqw⟩ := exists_prime_mem w
  have hne : q ≠ p := fun e => hp (e ▸ hqw)
  have hc : Continuous fun t : GUf E n => F.cmp w (UpperTheory.Gal.CertificateRingHomMap.th t) := by
    simp only [Frame.cmp, UpperTheory.Gal.CertificateRingHomMap.comp_th]
    exact Units.continuous_val.comp
      ((continuous_const.mul ((GlobalTheory.SplitPts.continuous_invT _).comp (cont_comp w))).mul continuous_const)
  choose m hm using fun i k : Fin n => exists_pow hqw hC (hc.matrix_elem i k)
  refine ⟨q ^ ∑ i, ∑ k, m i k, pow_pos hq.pos _, ((Nat.coprime_primes hq Fact.out).2 hne).pow_left _, fun _ t ht i k => ?_⟩
  refine mul_mem_of_dvd (pow_dvd_pow q ?_) (hm i k t ht)
  exact (Finset.single_le_sum (f := fun k => m i k) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)).trans
    (Finset.single_le_sum (f := fun i => ∑ k, m i k) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))

private theorem bound (F : Frame S) (V : Vec x U w₀ Up) :
    ∃ c : ℕ, 0 < c ∧ c.Coprime p ∧ ∀ g : GUf E n, F.th g ∈ lev V.S V.Kw → ∀ w : Plc E, (p : 𝓞 E) ∉ w.asIdeal → ∀ i k,
      (c : w.adicCompletion E) * F.cmp w g i k ∈ w.adicCompletionIntegers E := by
  choose c h0 h1 h2 using fun w => bound_at F V.cpt w
  have hfin : {w | ¬ F.a w ∈ GlobalTheory.LFun.KGL w (n := n)}.Finite := Filter.eventually_cofinite.1 F.a_cof
  let B : Finset (Plc E) := hfin.toFinset ∪ V.S ∪ V.S.image cj
  refine ⟨∏ w ∈ B, c w, Finset.prod_pos fun w _ => h0 w, Nat.Coprime.prod_left fun w _ => h1 w, fun g hg w hw i k => ?_⟩
  rw [th_eq] at hg
  by_cases hB : w ∈ B
  · have := h2 w hw _ hg i k
    rw [UpperTheory.Gal.CertificateRingHomMap.th_th] at this
    exact mul_mem_of_dvd (Finset.dvd_prod_of_mem _ hB) this
  · simp only [B, Finset.mem_union, Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_or, not_not, Finset.mem_image] at hB
    obtain ⟨⟨ha, hS⟩, hc⟩ := hB
    have hg' := (UpperTheory.Gal.CertificateRingHomMap.mem_lev.1 (UpperTheory.Gal.CertificateRingHomMap.th_mem_lev.1 hg)).2.2 w hS
      fun h => hc ⟨_, h, GlobalTheory.SplitPts.conjSrc_conjSrc_cm w⟩
    have hm := ((GlobalTheory.BCT.GlobLev.mem_KGL_iff_val w _).1 (mul_mem (mul_mem ha hg') (inv_mem ha))).1 i k
    exact mul_mem (natCast_mem _ _) hm

private theorem loc_mem {F : Frame S} {V : Vec x U w₀ Up} {W : Finset (Spl E p)} {N : ℕ}
    {L : ∀ w : Spl E p, Loc S.G.GAf (GLw n w.1)} {hw : IsSplitAt w₀ ∧ (p : 𝓞 E) ∉ w₀.asIdeal} {Ty : TyLev S.G.GAf (GLw n w₀)}
    (h : TyOK F V W N L hw Ty) (w : Spl E p) (h1 : w.1 ∉ V.S) (h2 : cj w.1 ∉ V.S) {y : GLw n w.1} (hy : y ∈ GlobalTheory.LFun.KGL w.1 (n := n))
    (hI : ∀ u ∈ W, (L u).pr ((L w).loc y) ∈ Iw n u.1) : (L w).loc y ∈ Ty.K := by
  refine (h.K_iff _).2 ⟨⟨UpperTheory.Gal.CertificateRingHomMap.loc w.2.1 y, ((h.fac w).2 y).symm, ?_⟩, hI⟩
  rw [th_eq, UpperTheory.Gal.CertificateRingHomMap.th_mem_lev]
  exact (UpperTheory.Gal.CertificateRingHomMap.pLocMem_of UpperTheory.Gal.CertificateRingHomMap.pIntConj_of UpperTheory.Gal.CertificateRingHomMap.pLocComm_of E n V.S _ w.1 w.2.1 h2 y).2 h1 hy

private theorem iw_le (w : Plc E) : Iw n w ≤ GlobalTheory.LFun.KGL w (n := n) := by
  intro y hy
  have := GlobalTheory.SmGL.iwahori_le_KO _ _ hy
  rwa [GlobalTheory.SmGL.SphCompletion.KO_completion] at this

end UpperTheory.Gal.Spc

open UpperTheory.Gal.Spc in
theorem UpperTheory.Gal.Spc.tyFact :
    UpperTheory.Gal.Spc.TyFact := by
  intro E _ _ _ A n p _ S F x U w₀ Up V _ _ _ _ _ r W aux N _ _ L hw Ty h
  refine ⟨fun w hwW => ?_, fun w h1 h2 h3 => ⟨⟨fun y hy => ?_, fun g hg => ?_⟩, ?_⟩, ?_⟩
  · haveI : Fact r.Prime := ⟨aux.prime⟩
    have hoff : ∀ u ∈ V.S, GlobalTheory.Cong.Apart w.1 u := fun u hu =>
      apart_of_not_mem (p := r) (aux.off u hu) (aux.half.above w hwW)
    obtain ⟨-, hap, -⟩ := UpperTheory.Gal.CertificateRingHomMap.pLocComm_of E n w.1 w.2.1
    have h1 : w.1 ∉ V.S := fun e => hoff _ e rfl
    have h2 : cj w.1 ∉ V.S := fun e => ((hap _).1 (Ne.symm (hoff _ e))).2 rfl
    refine ⟨⟨fun y hy => loc_mem h w h1 h2 (iw_le _ hy) fun u hu => ?_, fun g hg => ((h.K_iff g).1 hg).2 w hwW⟩, ?_,
      fun w' hw' hne => fac_apart (h.fac w) (h.fac w') (aux.half.apart w hwW w' hw' hne)⟩
    · by_cases e : u = w
      · subst e
        rw [Loc.pr_loc]
        exact hy
      · rw [pr_loc_one (h.fac u) (h.fac w) (aux.half.apart u hu w hwW e)]
        exact one_mem _
    · rw [h.L_eq]
      exact fac_apart (h.fac ⟨w₀, hw⟩) (h.fac w) (Ne.symm (hoff _ V.shape.mem))
  · refine loc_mem h w h1 h2 hy fun u hu => ?_
    rw [pr_loc_one (h.fac u) (h.fac w) (Ne.symm (h3 u hu))]
    exact one_mem _
  · obtain ⟨⟨k, rfl, hk⟩, -⟩ := (h.K_iff g).1 hg
    rw [th_eq, UpperTheory.Gal.CertificateRingHomMap.th_mem_lev] at hk
    rw [(h.fac w).1]
    exact (UpperTheory.Gal.CertificateRingHomMap.mem_lev.1 hk).2.2 w.1 h1 h2
  · obtain ⟨-, hap, -, -, hcc, -⟩ := UpperTheory.Gal.CertificateRingHomMap.pLocComm_of E n w₀ hw.1
    rw [h.L_eq]
    refine fac_apart (h.fac ⟨w₀, hw⟩) (h.fac w) (Ne.symm ((hap w.1).2 ⟨fun e => h1 ?_, fun e => h2 ?_⟩))
    · rw [e]
      exact V.shape.mem
    · rw [e, hcc]
      exact V.shape.mem
  · obtain ⟨c, h0, h1, h2⟩ := bound F V
    refine ⟨c, h0, h1, fun k hk => ?_⟩
    obtain ⟨⟨g, rfl, hg⟩, -⟩ := (h.K_iff k).1 hk
    exact (nsmul_integ_iff F g c).2 (h2 g hg)
end
end

section

set_option autoImplicit false

namespace UpperTheory.Gal.Spc

open UpperTheory.Gal.W2.Seed GlobalTheory.LKTrip GlobalTheory.UPel.HT

private def splitEquiv {X M : Type} [Group X] [Group M] (L : Loc X M) : X ≃* M × L.pr.ker where
  toFun g := (L.pr g, ⟨(L.loc (L.pr g))⁻¹ * g, by simp [MonoidHom.mem_ker, L.pr_loc]⟩)
  invFun x := L.loc x.1 * (x.2 : X)
  left_inv g := by simp
  right_inv x := by
    obtain ⟨m, h, hh⟩ := x
    have hh' : L.pr h = 1 := hh
    ext <;> simp [L.pr_loc, hh']
  map_mul' g h := by
    have hc : L.pr ((L.loc (L.pr g))⁻¹ * g) = 1 := by simp [L.pr_loc]
    have key := L.comm (L.pr h)⁻¹ _ hc
    rw [map_inv] at key
    refine Prod.ext (map_mul _ _ _) (Subtype.ext ?_)
    show (L.loc (L.pr (g * h)))⁻¹ * (g * h) = (L.loc (L.pr g))⁻¹ * g * ((L.loc (L.pr h))⁻¹ * h)
    rw [← mul_assoc ((L.loc (L.pr g))⁻¹ * g), ← key]
    simp [mul_assoc]

private theorem t2Space_hTGroup_gAf {p : ℕ} [Fact p.Prime] (G : HTGroup p) : T2Space G.GAf := by
  haveI := GlobalTheory.GfTop.t2Space_afP p
  haveI := GlobalTheory.GfTop.finiteAdeleRingAway_locallyCompactSpace p
  haveI := GlobalTheory.GfTop.finiteAdeleRingAway_totallyDisconnectedSpace p
  haveI := GlobalTheory.GfTop.finiteAdeleRingAway_secondCountableTopology p
  exact (GlobalTheory.GfTop.upts_props G.star (AfP p)).2.1

theorem splitC : SplitC := by
  intro p _ G Lv k _ _ _ _ P L hcont hat Kw hKo hKc hF
  haveI := t2Space_hTGroup_gAf G
  have hker : IsClosed (L.pr.ker : Set G.GAf) := isClosed_singleton.preimage hcont
  refine ⟨inferInstance, inferInstance, inferInstance,
    ⟨splitEquiv L, fun g => (hat g).symm, Kw, (Lv.K : Subgroup G.GAf).subgroupOf L.pr.ker,
      hKo, hKc, ?_, ?_, ?_⟩, fun g h => rfl⟩
  · exact Lv.K.isOpen.preimage continuous_subtype_val
  · exact hker.isClosedEmbedding_subtypeVal.isCompact_preimage Lv.compact
  · ext x
    constructor
    · rintro ⟨g, hg, rfl⟩
      refine ⟨hF.2 g hg, ?_⟩
      show (L.loc (L.pr g))⁻¹ * g ∈ (Lv.K : Subgroup G.GAf)
      exact mul_mem (inv_mem (hF.1 _ (hF.2 g hg))) hg
    · rintro ⟨hm, hh⟩
      exact ⟨L.loc x.1 * (x.2 : G.GAf), mul_mem (hF.1 _ hm) hh,
        (splitEquiv L).apply_symm_apply x⟩

end UpperTheory.Gal.Spc
end

section

open NumberField IsDedekindDomain

theorem UpperTheory.Gal.Spc.facEx :
    UpperTheory.Gal.Spc.FacEx := by
  intro E _ _ _ A n p _ S F w
  refine ⟨F.tr.at UpperTheory.Gal.W2.Seed.pLocComm w.1 w.2.1 w.2.2, fun g => ?_, fun y => ?_⟩
  · have h := (F.tr.j_eq (F.tr.sec (F.j g)) g).1 (by rw [F.j_tr]; exact F.tr.j_sec _) w.1 w.2.2
    exact h
  · rw [F.j_tr]
    rfl
end
