module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle006
public import Mathlib.Analysis.Matrix.Normed
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle024
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle495
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIsFundamentalDomainAndQuotMeasureEq
public import GroundTheory.AutomorphicForms.AdelicGLn
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoThreeFamily
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle514
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle015
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle517

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec

open Matrix

namespace GlobalTheory.IwasawaAdelic

theorem cornerGL_entry {R S : Type} [CommRing R] [CommRing S] {a : ℕ} (s : R →ₙ+* S)
    (g : GL (Fin a) R) (i j : Fin a) :
    (cornerGL a s g).val i j
      = (1 : Matrix (Fin a) (Fin a) S) i j - s ((1 : Matrix (Fin a) (Fin a) R) i j) + s (g.val i j) :=
  rfl

theorem cornerGL_entry_ne {R S : Type} [CommRing R] [CommRing S] {a : ℕ} (s : R →ₙ+* S)
    (g : GL (Fin a) R) {i j : Fin a} (h : i ≠ j) :
    (cornerGL a s g).val i j = s (g.val i j) := by
  rw [cornerGL_entry]; simp [Matrix.one_apply_ne h]

theorem cornerGL_entry_same {R S : Type} [CommRing R] [CommRing S] {a : ℕ} (s : R →ₙ+* S)
    (g : GL (Fin a) R) (i : Fin a) :
    (cornerGL a s g).val i i = 1 - s 1 + s (g.val i i) := by
  rw [cornerGL_entry]; simp

theorem stdBlocks_lt_of_lt {s r : ℕ} (d : Fin s → ℕ) (hd : ∑ i, d i = r) {a b : Fin s}
    (i : Fin (d a)) (j : Fin (d b)) (hba : b < a) : stdBlocks d hd ⟨b, j⟩ < stdBlocks d hd ⟨a, i⟩ := by
  let f : ℕ → ℕ := fun n => if h : n < s then d ⟨n, h⟩ else 0
  have key : ∀ c : Fin s, ∑ x : Fin c, d (Fin.castLE c.2.le x) = ∑ x ∈ Finset.range c, f x := by
    intro c
    rw [← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun x _ => ?_
    have hx : (x : ℕ) < s := x.2.trans c.2
    simp only [f, hx, dif_pos]
    rfl
  rw [Fin.lt_def, stdBlocks_val, stdBlocks_val, key, key]
  have h1 : ∑ x ∈ Finset.range (b + 1), f x ≤ ∑ x ∈ Finset.range a, f x :=
    Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.succ_le_of_lt hba))
  rw [Finset.sum_range_succ] at h1
  have h2 : f b = d b := by simp [f]
  have := j.2
  omega

theorem mem_parab_of_upper {R : Type} [CommRing R] {c N : ℕ} (n : Fin c → ℕ) (h : ∑ i, n i = N)
    (b : GL (Fin N) R) (hb : (b : Matrix (Fin N) (Fin N) R).BlockTriangular id) :
    b ∈ parab R (stdBlocks n h) := by
  rw [mem_parab_iff]
  intro a a' i j hlt
  exact hb (stdBlocks_lt_of_lt n h i j hlt)

theorem exists_upper_mul_unitary (N : ℕ) (y : GL (Fin N) ℂ) :
    ∃ b : GL (Fin N) ℂ, (b : Matrix (Fin N) (Fin N) ℂ).BlockTriangular id ∧
      ∃ k : Matrix (Fin N) (Fin N) ℂ, k ∈ Matrix.unitaryGroup (Fin N) ℂ ∧
        (y : Matrix (Fin N) (Fin N) ℂ) = b * k := by
  set A : Matrix (Fin N) (Fin N) ℂ := ((y⁻¹ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) with hAdef
  have hyA : (y : Matrix (Fin N) (Fin N) ℂ) * A = 1 := by simp [hAdef]
  have hAdet : IsUnit A.det := by
    rw [← Matrix.isUnit_iff_isUnit_det]; exact (y⁻¹).isUnit
  have hdet : IsUnit (Aᴴ * A).det := by
    rw [det_mul, det_conjTranspose]; exact hAdet.star.mul hAdet
  obtain ⟨Q, u, hQ, hu, hudet, hA⟩ := GlobalTheory.QRDecomp.exists_qr N N A hdet
  letI := u.invertibleOfIsUnitDet hudet
  refine ⟨(Matrix.nonsingInvUnit u hudet)⁻¹, ?_, Qᴴ, ?_, ?_⟩
  · show (u⁻¹).BlockTriangular id
    exact Matrix.blockTriangular_inv_of_blockTriangular hu
  · rw [Matrix.mem_unitaryGroup_iff', star_eq_conjTranspose, conjTranspose_conjTranspose]
    exact mul_eq_one_comm.1 hQ
  · show (y : Matrix (Fin N) (Fin N) ℂ) = u⁻¹ * Qᴴ
    have hQQ : Q * Qᴴ = 1 := mul_eq_one_comm.1 hQ
    have h1 : (Q * u) * (u⁻¹ * Qᴴ) = 1 := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc u, Matrix.mul_nonsing_inv u hudet, Matrix.one_mul, hQQ]
    calc (y : Matrix (Fin N) (Fin N) ℂ) = (y : Matrix (Fin N) (Fin N) ℂ) * ((Q * u) * (u⁻¹ * Qᴴ)) := by
          rw [h1, Matrix.mul_one]
      _ = u⁻¹ * Qᴴ := by rw [← Matrix.mul_assoc, ← hA, hyA, Matrix.one_mul]

theorem ext_eval {ι : Type} {N : ℕ} {P Q : Matrix (Fin N) (Fin N) (ι → ℂ)}
    (hPQ : ∀ v, P.map (Pi.evalRingHom (fun _ : ι => ℂ) v) = Q.map (Pi.evalRingHom (fun _ : ι => ℂ) v)) :
    P = Q := by
  ext i j v; exact congrFun (congrFun (hPQ v) i) j

theorem exists_upper_mul_unitary_inf (E : Type) [Field E] (N : ℕ) (y : GL (Fin N) (Cinf E)) :
    ∃ b : GL (Fin N) (Cinf E), (b : Matrix (Fin N) (Fin N) (Cinf E)).BlockTriangular id ∧
      ∃ k : Kinf E N, y = b * Unitary.toUnits k := by
  let ev : InfinitePlace E → (Cinf E →+* ℂ) := fun v => Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) v
  choose B hB K hK hyK using fun v => exists_upper_mul_unitary N (Matrix.GeneralLinearGroup.map (ev v) y)
  let bm : Matrix (Fin N) (Fin N) (Cinf E) := fun i j v => (B v : Matrix (Fin N) (Fin N) ℂ) i j
  let bi : Matrix (Fin N) (Fin N) (Cinf E) := fun i j v => (((B v)⁻¹ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) i j
  let km : Matrix (Fin N) (Fin N) (Cinf E) := fun i j v => K v i j
  have hbm : ∀ v, bm.map (ev v) = (B v : Matrix (Fin N) (Fin N) ℂ) := fun v => rfl
  have hbi : ∀ v, bi.map (ev v) = (((B v)⁻¹ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) := fun v => rfl
  have hkm : ∀ v, km.map (ev v) = K v := fun v => rfl
  have h1 : bm * bi = 1 := ext_eval fun v => by
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _), hbm, hbi]; simp
  have h2 : bi * bm = 1 := ext_eval fun v => by
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _), hbm, hbi]; simp
  have hkU : km ∈ Matrix.unitaryGroup (Fin N) (Cinf E) := by
    rw [Matrix.mem_unitaryGroup_iff']
    refine ext_eval fun v => ?_
    have hs : (star km).map (ev v) = star (K v) := by
      ext i j; rfl
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _), hs, hkm]
    exact (Matrix.mem_unitaryGroup_iff').1 (hK v)
  refine ⟨⟨bm, bi, h1, h2⟩, ?_, ⟨km, hkU⟩, ?_⟩
  · intro i j hij
    funext v
    exact hB v hij
  · apply Units.ext
    refine ext_eval fun v => ?_
    show (y : Matrix (Fin N) (Fin N) (Cinf E)).map (ev v) = (bm * km).map (ev v)
    rw [Matrix.map_mul, hbm, hkm]
    exact hyK v

theorem infGL_eq (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (N : ℕ) :
    infGL E N = cornerGL N (GlobalTheory.CuspRep.sInf E) := rfl

theorem infGL_mem_unipRad (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {c N : ℕ}
    (n : Fin c → ℕ) (h : ∑ i, n i = N) (u : GL (Fin N) (Cinf E))
    (hu : u ∈ unipRad (Cinf E) (stdBlocks n h)) : infGL E N u ∈ unipRad (Ad E) (stdBlocks n h) := by
  rw [mem_unipRad] at hu ⊢
  obtain ⟨hP, hD⟩ := hu
  refine ⟨mem_parab_iff.2 fun a b i j hlt => ?_, fun a i j => ?_⟩
  · have hne : stdBlocks n h ⟨a, i⟩ ≠ stdBlocks n h ⟨b, j⟩ := fun he => by
      have := congrArg Sigma.fst ((stdBlocks n h).injective he)
      exact (ne_of_gt hlt) this
    rw [infGL_eq, cornerGL_entry_ne _ _ hne, mem_parab_iff.1 hP a b i j hlt, map_zero]
  · by_cases hij : i = j
    · subst hij
      rw [infGL_eq, cornerGL_entry_same, hD a i i]; simp
    · have hne : stdBlocks n h ⟨a, i⟩ ≠ stdBlocks n h ⟨a, j⟩ := fun he => by
        exact hij (by simpa using (stdBlocks n h).injective he)
      rw [infGL_eq, cornerGL_entry_ne _ _ hne, hD a i j, Matrix.one_apply_ne hij, Matrix.one_apply_ne hij,
        map_zero]

theorem infGL_leviEmb (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {c N : ℕ}
    (n : Fin c → ℕ) (h : ∑ i, n i = N) (l : ∀ i, GL (Fin (n i)) (Cinf E)) :
    infGL E N (leviEmb (Cinf E) (stdBlocks n h) l)
      = leviEmb (Ad E) (stdBlocks n h) (fun i => infGL E (n i) (l i)) := by
  have leviEmb_apply_same : ∀ (R : Type) [CommRing R] (l : ∀ i, GL (Fin (n i)) R) a i j,
      (leviEmb R (stdBlocks n h) l : Matrix (Fin N) (Fin N) R) (stdBlocks n h ⟨a, i⟩) (stdBlocks n h ⟨a, j⟩) = (l a : Matrix _ _ R) i j := by
    intro R _ l a i j
    simp [leviEmb, blockDiagonal'_apply_eq]
  have leviEmb_apply_ne : ∀ (R : Type) [CommRing R] (l : ∀ i, GL (Fin (n i)) R) {a b}, a ≠ b → ∀ i j,
      (leviEmb R (stdBlocks n h) l : Matrix (Fin N) (Fin N) R) (stdBlocks n h ⟨a, i⟩) (stdBlocks n h ⟨b, j⟩) = 0 := by
    intro R _ l a b hab i j
    simp [leviEmb, blockDiagonal'_apply, hab]
  apply Units.ext
  ext p q
  obtain ⟨⟨a, i⟩, rfl⟩ := (stdBlocks n h).surjective p
  obtain ⟨⟨b, j⟩, rfl⟩ := (stdBlocks n h).surjective q
  by_cases hab : a = b
  · subst hab
    rw [leviEmb_apply_same]
    by_cases hij : i = j
    · subst hij
      rw [infGL_eq, infGL_eq, cornerGL_entry_same, cornerGL_entry_same, leviEmb_apply_same]
    · have hne : stdBlocks n h ⟨a, i⟩ ≠ stdBlocks n h ⟨a, j⟩ := fun he =>
        hij (by simpa using (stdBlocks n h).injective he)
      rw [infGL_eq, infGL_eq, cornerGL_entry_ne _ _ hne, cornerGL_entry_ne _ _ hij, leviEmb_apply_same]
  · have hne : stdBlocks n h ⟨a, i⟩ ≠ stdBlocks n h ⟨b, j⟩ := fun he =>
      hab (congrArg Sigma.fst ((stdBlocks n h).injective he))
    rw [leviEmb_apply_ne _ _ hab, infGL_eq, cornerGL_entry_ne _ _ hne, leviEmb_apply_ne _ _ hab, map_zero]

theorem iwasawa : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {c N : ℕ} (n : Fin c → ℕ) (h : ∑ i, n i = N) (x : GA E N), ∃ u ∈ unipRad (Ad E) (stdBlocks n h), ∃ (m : ∀ i, GA E (n i)) (k : Kinf E N) (g : GL (Fin N) (Af E)), x = u * leviEmb (Ad E) (stdBlocks n h) m * (infGL E N (Unitary.toUnits k) * finGL E N g) := by
  intro E _ _ _ c N n h x
  obtain ⟨b, hb, k, hy⟩ := exists_upper_mul_unitary_inf E N (Matrix.GeneralLinearGroup.map (pInf E) x)
  let p : parab (Cinf E) (stdBlocks n h) := ⟨b, mem_parab_of_upper n h b hb⟩
  let l := leviProj (Cinf E) (stdBlocks n h) p
  have hLp : leviEmb (Cinf E) (stdBlocks n h) l ∈ parab (Cinf E) (stdBlocks n h) := by
    apply mem_parab_iff.2
    intro a b i j hab
    simp [leviEmb, blockDiagonal'_apply, hab.ne']
  let Lp : parab (Cinf E) (stdBlocks n h) := ⟨leviEmb (Cinf E) (stdBlocks n h) l, hLp⟩
  have hproj : leviProj (Cinf E) (stdBlocks n h) Lp = l := by
    funext a
    ext i j
    simp [leviProj_apply, Lp, leviEmb, blockDiagonal'_apply_eq]
  let u : GL (Fin N) (Cinf E) := ((Lp⁻¹ * p : parab (Cinf E) (stdBlocks n h)) : GL (Fin N) (Cinf E))
  have hu : u ∈ unipRad (Cinf E) (stdBlocks n h) := by
    apply (coe_mem_unipRad (Cinf E) (Lp⁻¹ * p)).2
    simp [hproj, l]
  have hbu : b = leviEmb (Cinf E) (stdBlocks n h) l * u := by
    change (p : GL (Fin N) (Cinf E)) = (Lp : GL (Fin N) (Cinf E)) * ((Lp⁻¹ * p : parab (Cinf E) (stdBlocks n h)) : GL (Fin N) (Cinf E))
    simp
  set L := leviEmb (Cinf E) (stdBlocks n h) (leviProj (Cinf E) (stdBlocks n h) ⟨b, mem_parab_of_upper n h b hb⟩) with hL
  have hu' : L * u * L⁻¹ ∈ unipRad (Cinf E) (stdBlocks n h) := by
    let U : parab (Cinf E) (stdBlocks n h) := ⟨u, (mem_unipRad.1 hu).1⟩
    have hU : leviProj (Cinf E) (stdBlocks n h) U = 1 := (coe_mem_unipRad (Cinf E) U).1 hu
    change ((Lp * U * Lp⁻¹ : parab (Cinf E) (stdBlocks n h)) : GL (Fin N) (Cinf E)) ∈ _
    rw [coe_mem_unipRad, map_mul, map_mul, map_inv, hU, mul_one, mul_inv_cancel]
  refine ⟨infGL E N (L * u * L⁻¹), infGL_mem_unipRad E n h _ hu', fun i => infGL E (n i) (leviProj (Cinf E) (stdBlocks n h) ⟨b, mem_parab_of_upper n h b hb⟩ i), k, Matrix.GeneralLinearGroup.map (pFin E) x, ?_⟩
  rw [← infGL_leviEmb, ← hL]
  conv_lhs => rw [← infGL_mul_finGL x, hy]
  rw [hbu]
  simp only [map_mul, map_inv]
  group

end GlobalTheory.IwasawaAdelic
end

section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec

open scoped Matrix.Norms.Operator

noncomputable section

namespace GlobalTheory.SmoothIwasawaNear

variable (E : Type) [Field E] [NumberField E] {c N : ℕ} {n : Fin c → ℕ} (e : (Σ i, Fin (n i)) ≃ Fin N)

def lowPart (X : Matrix (Fin N) (Fin N) (Cinf E)) : Matrix (Fin N) (Fin N) (Cinf E) :=
  Matrix.of fun p q => if blk e q < blk e p then X p q else 0

def skewLin : Matrix (Fin N) (Fin N) (Cinf E) →ₗ[ℝ] Matrix (Fin N) (Fin N) (Cinf E) where
  toFun X := lowPart E e X - (lowPart E e X).conjTranspose
  map_add' X Y := by
    refine Matrix.ext fun p q => ?_
    simp only [lowPart, Matrix.add_apply, Matrix.sub_apply, Matrix.conjTranspose_apply, Matrix.of_apply]
    split_ifs <;> simp [star_add] <;> abel
  map_smul' r X := by
    refine Matrix.ext fun p q => ?_
    simp only [lowPart, Matrix.smul_apply, Matrix.sub_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
      RingHom.id_apply]
    split_ifs <;> simp [star_smul, smul_sub]

def skew : Matrix (Fin N) (Fin N) (Cinf E) →L[ℝ] Matrix (Fin N) (Fin N) (Cinf E) :=
  LinearMap.toContinuousLinearMap (skewLin E e)

theorem skew_apply (X : Matrix (Fin N) (Fin N) (Cinf E)) : skew E e X = lowPart E e X - (lowPart E e X).conjTranspose := rfl

theorem skew_conjTranspose (X : Matrix (Fin N) (Fin N) (Cinf E)) : (skew E e X).conjTranspose = -skew E e X := by
  rw [skew_apply, Matrix.conjTranspose_sub, Matrix.conjTranspose_conjTranspose, neg_sub]

theorem blockTriangular_up (X : Matrix (Fin N) (Fin N) (Cinf E)) :
    (1 + (X - skew E e X)).BlockTriangular (blk e) := by
  intro i j h
  have hij : i ≠ j := fun hh => by subst hh; exact lt_irrefl _ h
  simp [skew_apply, lowPart, Matrix.conjTranspose_apply, Matrix.one_apply_ne hij, h, not_lt_of_gt h]

def Fm (X : Matrix (Fin N) (Fin N) (Cinf E)) : Matrix (Fin N) (Fin N) (Cinf E) :=
  (1 + (X - skew E e X)) * NormedSpace.exp (skew E e X)

theorem contDiff_exp' {k : WithTop ℕ∞} :
    ContDiff ℝ k (NormedSpace.exp : Matrix (Fin N) (Fin N) (Cinf E) → Matrix (Fin N) (Fin N) (Cinf E)) :=
  contDiff_iff_contDiffAt.2 fun x => (NormedSpace.exp_analytic (𝕂 := ℝ) x).contDiffAt

theorem contDiff_Fm {k : WithTop ℕ∞} : ContDiff ℝ k (Fm E e) :=
  (contDiff_const.add (contDiff_id.sub (skew E e).contDiff)).mul ((contDiff_exp' E).comp (skew E e).contDiff)

theorem Fm_zero : Fm E e 0 = 1 := by simp [Fm, NormedSpace.exp_zero]

theorem hasFDerivAt_Fm : HasFDerivAt (Fm E e)
    ((ContinuousLinearEquiv.refl ℝ (Matrix (Fin N) (Fin N) (Cinf E)) : _ →L[ℝ] _)) 0 := by
  have h1 : HasFDerivAt (fun X : Matrix (Fin N) (Fin N) (Cinf E) => 1 + (X - skew E e X))
      (ContinuousLinearMap.id ℝ _ - skew E e) 0 :=
    ((hasFDerivAt_id 0).sub (skew E e).hasFDerivAt).const_add 1
  have h0 := hasFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := Matrix (Fin N) (Fin N) (Cinf E))
  rw [← map_zero (skew E e)] at h0
  have h2 := h0.comp (0 : Matrix (Fin N) (Fin N) (Cinf E)) (skew E e).hasFDerivAt
  have h3 := h1.mul' h2
  refine h3.congr_fderiv (ContinuousLinearMap.ext fun X => ?_)
  have hs0 : skew E e 0 = 0 := map_zero _
  show (1 + (0 - skew E e 0)) * skew E e X + (X - skew E e X) * NormedSpace.exp (skew E e 0) = X
  rw [hs0, NormedSpace.exp_zero, sub_zero, add_zero, one_mul, mul_one]
  abel

theorem exists_local_iwasawa : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {c N : ℕ} (n : Fin c → ℕ) (e : (Σ i, Fin (n i)) ≃ Fin N), ∃ (p : Lie E N → parab (Cinf E) e) (k : Lie E N → Kinf E N), ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => toL (p y).1.val) (oneL E N) ∧ ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => toL (k y).1) (oneL E N) ∧ p (oneL E N) = 1 ∧ k (oneL E N) = 1 ∧ ∀ᶠ y in nhds (oneL E N), Matrix.of y = (p y).1.val * (k y).1 := by
  intro E _ _ _ c N n e
  classical
  have hn : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  have hF : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Fm E e) 0 := (contDiff_Fm E e).contDiffAt
  have hF' := hasFDerivAt_Fm E e
  set G := hF.localInverse hF' hn with hGdef
  have hG : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G (Fm E e 0) := hF.to_localInverse hF' hn
  have hG1 : G (Fm E e 0) = 0 := hF.localInverse_apply_image hF' hn
  have hinv : ∀ᶠ X in nhds (Fm E e 0), Fm E e (G X) = X :=
    (hF.hasStrictFDerivAt' hF' hn).eventually_right_inverse
  rw [Fm_zero] at hG hG1 hinv
  let T : Lie E N ≃L[ℝ] Matrix (Fin N) (Fin N) (Cinf E) := (Matrix.ofLinearEquiv ℝ).toContinuousLinearEquiv
  let φ : Matrix (Fin N) (Fin N) (Cinf E) → Matrix (Fin N) (Fin N) (Cinf E) := fun X => 1 + (G X - skew E e (G X))
  let ψ : Matrix (Fin N) (Fin N) (Cinf E) → Matrix (Fin N) (Fin N) (Cinf E) :=
    fun X => NormedSpace.exp (skew E e (G X))
  have hφ : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ 1 :=
    contDiffAt_const.add (hG.sub ((skew E e).contDiff.contDiffAt.comp _ hG))
  have hψ : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ 1 :=
    (contDiff_exp' E).contDiffAt.comp _ ((skew E e).contDiff.contDiffAt.comp _ hG)
  have hφ1 : φ 1 = 1 := by simp [φ, hG1]
  have hψ1 : ψ 1 = 1 := by simp [ψ, hG1, NormedSpace.exp_zero]
  have hunit : ∀ᶠ X in nhds (1 : Matrix (Fin N) (Fin N) (Cinf E)), IsUnit (φ X) :=
    hφ.continuousAt.eventually_mem (by rw [hφ1]; exact Units.isOpen.mem_nhds isUnit_one)
  have hTt : Filter.Tendsto (fun y : Lie E N => Matrix.of y) (nhds (oneL E N)) (nhds 1) :=
    T.continuous.tendsto (oneL E N)
  have hunitV : ∀ᶠ y in nhds (oneL E N), IsUnit (φ (Matrix.of y)) := hTt.eventually hunit
  have hinvV : ∀ᶠ y in nhds (oneL E N), Fm E e (G (Matrix.of y)) = Matrix.of y := hTt.eventually hinv
  have hU : ∀ X, ψ X ∈ Matrix.unitaryGroup (Fin N) (Cinf E) := fun X => by
    show NormedSpace.exp (skew E e (G X)) ∈ _
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose,
      skew_conjTranspose, ← Matrix.exp_add_of_commute _ _ (Commute.refl (skew E e (G X))).neg_left, neg_add_cancel,
      NormedSpace.exp_zero]
  have hφT : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ (T (oneL E N)) := hφ
  have hψT : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ (T (oneL E N)) := hψ
  refine ⟨fun y => if h : IsUnit (φ (Matrix.of y)) then ⟨h.unit, blockTriangular_up E e (G (Matrix.of y))⟩ else 1,
    fun y => ⟨ψ (Matrix.of y), hU _⟩, ?_, ?_, ?_, ?_, ?_⟩
  · have hsm : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => T.symm (φ (T y))) (oneL E N) :=
      T.symm.contDiff.contDiffAt.comp _ (hφT.comp (oneL E N) T.contDiff.contDiffAt)
    refine hsm.congr_of_eventuallyEq ?_
    filter_upwards [hunitV] with y hy
    simp only [dif_pos hy]
    show toL (hy.unit : Matrix (Fin N) (Fin N) (Cinf E)) = _
    rw [hy.unit_spec]
    rfl
  · exact T.symm.contDiff.contDiffAt.comp _ (hψT.comp (oneL E N) T.contDiff.contDiffAt)
  · have h1 : IsUnit (φ (Matrix.of (oneL E N))) := by
      show IsUnit (φ 1)
      rw [hφ1]
      exact isUnit_one
    refine Subtype.ext (Units.ext ?_)
    simp only [dif_pos h1]
    exact (IsUnit.unit_spec _).trans hφ1
  · exact Subtype.ext hψ1
  · filter_upwards [hunitV, hinvV] with y hy hy'
    simp only [dif_pos hy]
    show Matrix.of y = (hy.unit : Matrix (Fin N) (Fin N) (Cinf E)) * ψ (Matrix.of y)
    rw [hy.unit_spec]
    exact hy'.symm

end GlobalTheory.SmoothIwasawaNear
end
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.AutomorphicL2Unitary GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.Published

noncomputable section

namespace GlobalTheory.CapOrth

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N : ℕ} {μ : Measure (GA E N)}
  {W : Submodule ℂ (Sm E N)} (h : ∀ φ ∈ W, MemL2Quotient (latticeGL E N) μ φ.1)


open Classical in
def cls (x : Sm E N) : L2 (latticeGL E N) μ := if hx : x ∈ W then toL2ₗ μ W h ⟨x, hx⟩ else 0

theorem cls_mk {x : Sm E N} (hx : x ∈ W) : cls h x = toL2ₗ μ W h ⟨x, hx⟩ := dif_pos hx

theorem cls_add {x y : Sm E N} (hx : x ∈ W) (hy : y ∈ W) : cls h (x + y) = cls h x + cls h y := by
  rw [cls_mk h (W.add_mem hx hy), cls_mk h hx, cls_mk h hy, ← map_add (f := _)]; rfl

theorem cls_smul (c : ℂ) {x : Sm E N} (hx : x ∈ W) : cls h (c • x) = c • cls h x := by
  rw [cls_mk h (W.smul_mem c hx), cls_mk h hx, ← map_smul]; rfl

theorem cls_sub {x y : Sm E N} (hx : x ∈ W) (hy : y ∈ W) : cls h (x - y) = cls h x - cls h y := by
  rw [cls_mk h (W.sub_mem hx hy), cls_mk h hx, cls_mk h hy, ← map_sub]; rfl

variable (J : Submodule ℂ (Sm E N))

variable [μ.IsHaarMeasure] [μ.IsMulRightInvariant]

end GlobalTheory.CapOrth
end
end

section

noncomputable section
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.RSJ GlobalTheory.ZEul Filter Topology Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate

namespace GlobalTheory.ZEul


open GlobalTheory.CuspRep.CuspidalL2GL in
theorem exists_fundamentalDomain_NE : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (μ : Measure (GA E n)) [μ.IsHaarMeasure],
  ∃ 𝓕₀ : Set (GA E n), IsFundamentalDomain (GlobalTheory.CellDec.NE E n) 𝓕₀ μ := by
  intro E _ _ n μ _
  haveI := CuspidalL2GL.locallyCompactSpace_GA E n
  haveI := CuspidalL2GL.t2Space_GA E n
  haveI := CuspidalL2GL.secondCountableTopology_GA E n
  haveI : DiscreteTopology (ratGL E n).range := GroundTheory.Automorphic.AdelicGLn.discreteTopology_rationalGL E n
  have hsub : (GlobalTheory.CellDec.NE E n : Set (GA E n)) ⊆ ((ratGL E n).range : Set (GA E n)) := by
    rintro _ ⟨u, -, rfl⟩
    exact ⟨u, rfl⟩
  haveI : DiscreteTopology (GlobalTheory.CellDec.NE E n) := DiscreteTopology.of_subset (inferInstance : DiscreteTopology ((ratGL E n).range : Set (GA E n))) hsub
  obtain ⟨𝓕, -, -, h𝓕⟩ := GlobalTheory.exists_isFundamentalDomain_subgroup (GlobalTheory.CellDec.NE E n)
  exact ⟨𝓕, h𝓕 _⟩

end GlobalTheory.ZEul
end
end

section

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff
open Matrix

theorem _root_.GlobalTheory.T.blockGL_supported_mem_mirabolic_supported : ∀ (E : Type) [Field E] [NumberField E] (m r : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))),
    ∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S,
      GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h ∈ (GlobalTheory.JSW.supS (E := E) (a := (m + r + 1) + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) (m + r + 1)) := by
  first | (exact @GlobalTheory.BlockMirabolic.blockGL_mem_mirS) | (exact GlobalTheory.BlockMirabolic.blockGL_mem_mirS) | (intros; apply GlobalTheory.BlockMirabolic.blockGL_mem_mirS  <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors Classical

theorem _root_.GlobalTheory.T.globalWhittakerCoefficient_continuous_norm_invariant : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (F : GA E a → ℂ), Continuous F →
    (∀ γ g, F (ratGL E a γ * g) = F g) →
    Continuous (GlobalTheory.JSW.whit F) ∧ ∀ u ∈ GlobalTheory.CellDec.NA E a, ∀ g, ‖GlobalTheory.JSW.whit F (u * g)‖ = ‖GlobalTheory.JSW.whit F g‖ := by
  first | exact @GlobalTheory.JSW.WhitNorm.continuous_whit_and_norm_mul | exact GlobalTheory.JSW.WhitNorm.continuous_whit_and_norm_mul | (intros; apply GlobalTheory.JSW.WhitNorm.continuous_whit_and_norm_mul <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors Classical

theorem _root_.GlobalTheory.T.cuspFormRapidKernelSmoothSpan_left_invariant : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CuspSub E a), ∀ F ∈ GlobalTheory.JSW.mspanR π,
    ∀ (γ : GL (Fin a) E) (g : GA E a), F (ratGL E a γ * g) = F g := by
  first | exact @GlobalTheory.JSW.mspanR_left_invariant | exact GlobalTheory.JSW.mspanR_left_invariant | (intros; apply GlobalTheory.JSW.mspanR_left_invariant <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

theorem _root_.GlobalTheory.T.mediumInert_smallInert_lengthBound_tabX : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (HW : HWOf D.loc) (X : KillingConditions.HubData D) (R : KillingConditions.RowK) (C : ℝ), KillingConditions.DataAD L HW X R → R.Le C → TwistedPlaces.MediumInertPrimeLengthBound L (tabX L X) C ∧ TwistedPlaces.SmallInertPrimeSmallOrderLengthBound L (tabX L X) C := by
  first | exact @GlobalTheory.NLink.localBoundTable_rowsCD_admissible | exact GlobalTheory.NLink.localBoundTable_rowsCD_admissible | (intros; apply GlobalTheory.NLink.localBoundTable_rowsCD_admissible <;> assumption)
end
