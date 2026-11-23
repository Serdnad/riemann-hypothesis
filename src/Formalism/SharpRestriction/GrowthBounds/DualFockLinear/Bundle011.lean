module

public import Formalism.LocalToGlobal.GroupLattices.FockModels.TransposeWords.TransposeWordsProofs.FockPairingRowAction
public import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.OneSidedLemma4Realisable
import Formalism.LocalToGlobal.GroupLattices.FockModels.FlatModels.LetterWtAnti
public import Formalism.LocalToGlobal.GroupLattices.FockModels.TransposeWords.TransposeWordsProofs.ProdBlockEmbMonomial
public import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.Bundle007
public import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.SourcePrimitiveIntegrality
public import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.Bundle009
public import Formalism.SharpRestriction.GrowthBounds.Joints
public import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments
public import Formalism.SharpRestriction.GrowthBounds.Bundle008
import Formalism.SharpRestriction.GrowthBounds.ProjectionOfIsotypicDecomposition
import Formalism.SharpRestriction.GrowthBounds.RootWeights.WeightConditionFromIntegralForm
public import Formalism.SharpRestriction.GrowthBounds.ScaleEdges
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.TestSideCounting

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.Pf14
open Formalism.L2.G.Model (Lin Th0 Aa Lin_comp Lin_one Lin_Pol Th0_inj mem_tens_nabla mem_tens_dw map_Pol mem_Pol VS
  letterWt_anti flat_lam)
open Formalism.L2.G.Model.TS

def fockL {τ K : Type} [CommRing K] (Q : MvPolynomial τ K) : MvPolynomial τ K →ₗ[K] K where
  toFun P := fockR P Q
  map_add' a b := tsact_add_left a b Q
  map_smul' c a := by simpa using tsact_smul_left c a Q

theorem fockR_add_right {τ K : Type} [CommRing K] (g f f' : MvPolynomial τ K) :
    fockR g (f + f') = fockR g f + fockR g f' := by
  simp only [Formalism.L2.G.Model.TS.fockR, MvPolynomial.coeff_add, mul_add, add_mul, Finset.sum_add_distrib]

section Pair

variable {O Kf : Type} [CommRing O] [IsDomain O] [Field Kf] [Algebra O Kf] {n' m : ℕ}

def LatM (O : Type) {Kf : Type} [CommRing O] [Field Kf] [Algebra O Kf] {n' m : ℕ} (d : Fin n' → ℕ)
    (M : Fin n' → Matrix (Fin (m + 1)) (Fin (m + 1)) Kf) :
    Submodule O (MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) :=
  tensorLat O Kf (fun s => nablaLTw O Kf m (letterWt m (d s) (vecE n' s)) (M s))

theorem VS_eq (Kf : Type) [Field Kf] {n' m : ℕ} (d : Fin n' → ℕ) :
    VS Kf m (vecE n') d = Vsp Kf (flW (m := m) d) := by
  unfold VS Vsp
  congr 1
  funext s
  rw [flat_lam (vecE n') d (flW d) (isFlat_flW d) s, if_pos (letterWt_anti _ _ _)]

theorem Hten_flW (O : Type) {Kf : Type} [CommRing O] [Field Kf] [Algebra O Kf] {n' m : ℕ} (d : Fin n' → ℕ)
    (Λ : Fin n' → Submodule O (Fin (m + 1) → Kf)) :
    Hten O (flW (m := m) d) Λ = tensorLat O Kf (fun x => H0 O m (letterWt m (d x) (vecE n' x)) (Λ x)) := by
  unfold Hten
  congr 1
  funext s
  rw [flat_lam (vecE n') d (flW d) (isFlat_flW d) s]

theorem exists_thK (Kf : Type) [Field Kf] {n' m : ℕ} (hm : 1 ≤ m) (d : Fin n' → ℕ) :
    ∃ thK : ↥(Pol Kf (ι := Fin n') (m + 1) d) ≃ₗ[Kf] ↥(Vsp Kf (flW (m := m) d)),
      ∀ P, ((thK P : ↥(Vsp Kf (flW (m := m) d))) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) =
        Th0 Kf m (vecE n') (P : MvPolynomial (Fin n' × Fin (m + 1)) Kf) := by
  have hV : ∀ P : ↥(Pol Kf (ι := Fin n') (m + 1) d),
      Th0 Kf m (vecE n') (P : MvPolynomial (Fin n' × Fin (m + 1)) Kf) ∈ Vsp Kf (flW (m := m) d) := by
    intro P
    rw [← VS_eq]
    exact (mem_tens_dw Kf m hm (vecE n') d _).mpr ⟨P, P.2, rfl⟩
  let f : ↥(Pol Kf (ι := Fin n') (m + 1) d) →ₗ[Kf] ↥(Vsp Kf (flW (m := m) d)) :=
    LinearMap.codRestrict _ ((Th0 Kf m (vecE n')).toLinearMap.comp (Pol Kf (ι := Fin n') (m + 1) d).subtype) hV
  have hinj : Function.Injective f := by
    intro P Q h
    apply Subtype.ext
    have h' := congrArg Subtype.val h
    exact Th0_inj Kf m hm (vecE n') d _ _ P.2 Q.2 h'
  have hsurj : Function.Surjective f := by
    intro y
    have hy : (y : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) ∈ VS Kf m (vecE n') d := by
      rw [VS_eq]
      exact y.2
    obtain ⟨F, hF, hFy⟩ := (mem_tens_dw Kf m hm (vecE n') d _).mp hy
    exact ⟨⟨F, hF⟩, Subtype.ext hFy.symm⟩
  exact ⟨LinearEquiv.ofBijective f ⟨hinj, hsurj⟩, fun P => rfl⟩

variable {d : Fin n' → ℕ} (thK : ↥(Pol Kf (ι := Fin n') (m + 1) d) ≃ₗ[Kf] ↥(Vsp Kf (flW (m := m) d)))

def TY (c : Kf) : ↥(Vsp Kf (flW (m := m) d)) →ₗ[Kf] Module.Dual Kf ↥(Vsp Kf (flW (m := m) d)) where
  toFun y := c • ((fockL ((thK.symm y : ↥(Pol Kf (ι := Fin n') (m + 1) d)) :
      MvPolynomial (Fin n' × Fin (m + 1)) Kf)).comp
    ((Pol Kf (ι := Fin n') (m + 1) d).subtype.comp thK.symm.toLinearMap))
  map_add' y y' := by
    ext u
    simp only [LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.add_apply, fockL, LinearMap.coe_mk,
      AddHom.coe_mk, map_add, Submodule.coe_add, smul_eq_mul]
    rw [fockR_add_right, mul_add]
  map_smul' a y := by
    ext u
    simp only [LinearMap.smul_apply, LinearMap.comp_apply, fockL, LinearMap.coe_mk, AddHom.coe_mk, map_smul,
      Submodule.coe_smul, smul_eq_mul, RingHom.id_apply]
    rw [tsact_smul_right]
    ring

theorem TY_apply (c : Kf) (P Q : ↥(Pol Kf (ι := Fin n') (m + 1) d)) :
    TY thK c (thK Q) (thK P) = c * fockR (P : MvPolynomial (Fin n' × Fin (m + 1)) Kf)
      (Q : MvPolynomial (Fin n' × Fin (m + 1)) Kf) := by
  simp [TY, fockL]

theorem int_pair (p κ : ℕ) (hMD : MultDiv O p κ (k := m + 1) d) (G : MvPolynomial (Fin n' × Fin (m + 1)) O)
    (hG : G ∈ Pol O (m + 1) d) (E : MvPolynomial (Fin n' × Fin (m + 1)) O) :
    ∃ z : O, ((p : Kf) ^ κ / (((∏ s, (d s).factorial : ℕ) : ℕ) : Kf)) *
      fockR (map (algebraMap O Kf) G) (map (algebraMap O Kf) E) = algebraMap O Kf z := by
  classical
  by_cases hD0 : (((∏ s, (d s).factorial : ℕ) : ℕ) : Kf) = 0
  · refine ⟨0, ?_⟩
    rw [hD0, div_zero, zero_mul, map_zero]
  have hw : ∀ μ : Fin n' × Fin (m + 1) →₀ ℕ, ∃ w : O, μ ∈ G.support →
      (p : O) ^ κ * ((∏ j ∈ μ.support, (μ j).factorial : ℕ) : O) = ((∏ s, (d s).factorial : ℕ) : O) * w := by
    intro μ
    by_cases hμ : μ ∈ G.support
    · obtain ⟨w, hw⟩ := hMD μ ((mem_Pol.mp hG) μ hμ)
      exact ⟨w, fun _ => hw⟩
    · exact ⟨0, fun h => absurd h hμ⟩
  choose w hw using hw
  refine ⟨∑ μ ∈ G.support, AddMonoidAlgebra.coeff G μ * AddMonoidAlgebra.coeff E μ * w μ, ?_⟩

  rw [fockR_eq_sum _ _ G.support (support_map_subset _ _), Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl ?_
  intro μ hμ
  have h := congrArg (algebraMap O Kf) (hw μ hμ)
  simp only [map_mul, map_pow, map_natCast] at h
  simp only [coeff_map, map_mul]
  rw [div_mul_eq_mul_div, div_eq_iff hD0]
  linear_combination (algebraMap O Kf (AddMonoidAlgebra.coeff G μ) * algebraMap O Kf (AddMonoidAlgebra.coeff E μ)) * h

theorem sandwich (hm : 1 ≤ m)
    (hthK : ∀ P, ((thK P : ↥(Vsp Kf (flW (m := m) d))) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) =
      Th0 Kf m (vecE n') (P : MvPolynomial (Fin n' × Fin (m + 1)) Kf))
    (p κ : ℕ) (hMD : MultDiv O p κ (k := m + 1) d)
    (M : Fin n' → Matrix (Fin (m + 1)) (Fin (m + 1)) Kf) (hM : ∀ s, IsUnit (M s).det)
    (u y : ↥(Vsp Kf (flW (m := m) d)))
    (hu : (u : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) ∈ LatM O d M)
    (hy : (y : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) ∈ LatM O d (fun s => ((M s)⁻¹).transpose)) :
    TY thK ((p : Kf) ^ κ / (((∏ s, (d s).factorial : ℕ) : ℕ) : Kf)) y u ∈ Set.range (algebraMap O Kf) := by
  obtain ⟨F, hF, hFu⟩ := (mem_tens_nabla O Kf m hm (vecE n') d M hM _).mp hu
  have hM' : ∀ s, IsUnit (((M s)⁻¹).transpose).det := fun s => by
    rw [Matrix.det_transpose]
    exact Matrix.isUnit_nonsing_inv_det _ (hM s)
  obtain ⟨G, hG, hGy⟩ := (mem_tens_nabla O Kf m hm (vecE n') d _ hM' _).mp hy
  have hP : ((thK.symm u : ↥(Pol Kf (ι := Fin n') (m + 1) d)) : MvPolynomial (Fin n' × Fin (m + 1)) Kf) =
      Lin (fun s => Aa (vecE n' s) (M s)⁻¹) (map (algebraMap O Kf) F) := by
    apply Th0_inj Kf m hm (vecE n') d _ _ (thK.symm u).2 (Lin_Pol _ _ (map_Pol _ _ hF))
    rw [← hthK, LinearEquiv.apply_symm_apply, ← hFu]
  have hQ : ((thK.symm y : ↥(Pol Kf (ι := Fin n') (m + 1) d)) : MvPolynomial (Fin n' × Fin (m + 1)) Kf) =
      Lin (fun s => Aa (vecE n' s) (((M s)⁻¹).transpose)⁻¹) (map (algebraMap O Kf) G) := by
    apply Th0_inj Kf m hm (vecE n') d _ _ (thK.symm y).2 (Lin_Pol _ _ (map_Pol _ _ hG))
    rw [← hthK, LinearEquiv.apply_symm_apply, ← hGy]
  have e := TY_apply thK ((p : Kf) ^ κ / (((∏ s, (d s).factorial : ℕ) : ℕ) : Kf)) (thK.symm u) (thK.symm y)
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at e
  obtain ⟨z, hz⟩ := int_pair (Kf := Kf) p κ hMD F hF G
  refine ⟨z, ?_⟩
  rw [e, hP, hQ, fockR_Lin_dual _ _ (fun s => Aa_dual (vecE n' s) (M s) (hM s))]
  exact hz.symm

end Pair

end Formalism.MainNotions.TestSideCounting
end
end

section

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.TestSideCounting

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14
open Formalism.L2.G.Model (Lin)

section ND

variable {R : Type} [CommRing R] {n' k : ℕ}

theorem normDeg_univ (r : ℕ) (m : TV n' k →₀ ℕ) :
    normDeg r m = ∑ v : TV n' k, if IsNormal r v then m v else 0 := by
  unfold normDeg
  apply Finset.sum_subset (Finset.subset_univ _)
  intro v _ hv
  rw [Finsupp.notMem_support_iff] at hv
  simp [hv]

theorem normDeg_add (r : ℕ) (m m' : TV n' k →₀ ℕ) : normDeg r (m + m') = normDeg r m + normDeg r m' := by
  simp only [normDeg_univ, Finsupp.coe_add, Pi.add_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun v _ => ?_
  split_ifs <;> simp

def NDsub (R : Type) [CommRing R] (n' k r T : ℕ) : Submodule R (MvPolynomial (TV n' k) R) :=
  restrictSupport R {mm | normDeg r mm ≤ T}

theorem mem_NDsub {r T : ℕ} {P : MvPolynomial (TV n' k) R} :
    P ∈ NDsub R n' k r T ↔ ∀ mm ∈ P.support, normDeg r mm ≤ T := by
  show P ∈ restrictSupport R {mm | normDeg r mm ≤ T} ↔ _
  exact ⟨fun h mm hm => h hm, fun h mm hm => h mm hm⟩

theorem NDsub_mono {r T T' : ℕ} (h : T ≤ T') : NDsub R n' k r T ≤ NDsub R n' k r T' := by
  intro P hP
  rw [mem_NDsub] at hP ⊢
  intro mm hm
  exact (hP mm hm).trans h

theorem nd_move (r : ℕ) (mm : TV n' k →₀ ℕ) (v v' : TV n' k) :
    normDeg r (Finsupp.single v 1 + (mm - Finsupp.single v' 1)) ≤ normDeg r mm + 1 := by
  rw [normDeg_add]
  have h1 : normDeg r (Finsupp.single v 1 : TV n' k →₀ ℕ) ≤ 1 := by
    rw [normDeg_univ]
    calc ∑ w : TV n' k, (if IsNormal r w then (Finsupp.single v 1 : TV n' k →₀ ℕ) w else 0)
        ≤ ∑ w : TV n' k, (Finsupp.single v 1 : TV n' k →₀ ℕ) w :=
          Finset.sum_le_sum fun w _ => by split_ifs <;> simp
      _ = 1 := by simp [Finsupp.single_apply]
  have h2 : normDeg r (mm - Finsupp.single v' 1) ≤ normDeg r mm := by
    rw [normDeg_univ, normDeg_univ]
    apply Finset.sum_le_sum
    intro w _
    split_ifs
    · simp only [Finsupp.tsub_apply]
      exact tsub_le_self
    · exact le_rfl
  omega

theorem nd_op (r T : ℕ) (v v' : TV n' k) {P : MvPolynomial (TV n' k) R} (hP : P ∈ NDsub R n' k r T) :
    X v * pderiv v' P ∈ NDsub R n' k r (T + 1) := by
  rw [mem_NDsub] at hP

  rw [P.as_sum, map_sum, Finset.mul_sum]
  refine Submodule.sum_mem _ fun mm hmm => ?_
  rw [pderiv_monomial, ← pow_one (X v), ← monomial_single_add, mem_NDsub]
  intro mm' hmm'
  rw [Finset.mem_singleton.mp (support_monomial_subset hmm')]
  exact (nd_move r mm v v').trans (Nat.add_le_add_right (hP mm hmm) 1)

theorem nd_mul {r T T' : ℕ} {P Q : MvPolynomial (TV n' k) R} (hP : P ∈ NDsub R n' k r T) (hQ : Q ∈ NDsub R n' k r T') :
    P * Q ∈ NDsub R n' k r (T + T') := by
  rw [mem_NDsub] at *
  intro mm hmm
  have h1 := support_mul P Q hmm
  rw [Finset.mem_add] at h1
  obtain ⟨a, ha, b, hb, rfl⟩ := h1
  rw [normDeg_add]
  exact Nat.add_le_add (hP a ha) (hQ b hb)

theorem Lin_pderiv (N N' : Fin n' → Matrix (Fin k) (Fin k) R) (h : ∀ s, N s * N' s = 1) (s : Fin n') (b : Fin k)
    (f : MvPolynomial (Fin n' × Fin k) R) :
    Lin N (pderiv (s, b) f) = ∑ c, N' s c b • pderiv (s, c) (Lin N f) := by
  simp only [Lin_chain, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul]
  have hm : ∀ a, ∑ c, N' s c b * N s a c = (1 : Matrix (Fin k) (Fin k) R) a b := by
    intro a
    rw [← h s, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun c _ => mul_comm _ _
  simp [hm, Matrix.one_apply]

theorem nd_Lin_op (N N' : Fin n' → Matrix (Fin k) (Fin k) R) (h : ∀ s, N s * N' s = 1) (r T : ℕ) (s : Fin n')
    (a b : Fin k) {f : MvPolynomial (Fin n' × Fin k) R} (hf : Lin N f ∈ NDsub R n' k r T) :
    Lin N (X (s, a) * pderiv (s, b) f) ∈ NDsub R n' k r (T + 1) := by
  rw [map_mul, Lin_X, Lin_pderiv N N' h, Finset.sum_mul]
  refine Submodule.sum_mem _ fun b' _ => ?_
  rw [Finset.mul_sum]
  refine Submodule.sum_mem _ fun c _ => ?_
  rw [mul_smul_comm, mul_assoc, ← smul_eq_C_mul]
  exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (nd_op r T _ _ hf))

theorem nd_word (N N' : Fin n' → Matrix (Fin k) (Fin k) R) (h : ∀ s, N s * N' s = 1) (r T : ℕ)
    {f : MvPolynomial (Fin n' × Fin k) R} (hf : Lin N f ∈ NDsub R n' k r T) :
    ∀ l : List (Fin n' × (Fin k × Fin k)), Lin N (opWord l f) ∈ NDsub R n' k r (T + l.length) := by
  intro l
  induction l with
  | nil => exact hf
  | cons y l ih =>
    show Lin N (X (y.1, y.2.1) * pderiv (y.1, y.2.2) (opWord l f)) ∈ NDsub R n' k r (T + (l.length + 1))
    rw [← Nat.add_assoc]
    exact nd_Lin_op N N' h r (T + l.length) y.1 y.2.1 y.2.2 ih

theorem word_length {τ : Type} (TT : Finset (Fin n')) (c : ℕ) :
    ∀ l : List (Fin n' × τ), (∀ z ∈ l, z.1 ∈ TT) → (∀ s, (l.filter fun z => z.1 = s).length ≤ c) →
      l.length ≤ TT.card * c := by
  intro l hl hc
  have key : ∀ l : List (Fin n' × τ), (∀ z ∈ l, z.1 ∈ TT) →
      l.length = ∑ s ∈ TT, (l.filter fun z => z.1 = s).length := by
    intro l hl
    induction l with
    | nil => simp
    | cons z l ih =>
      have e : ∀ s, ((z :: l).filter fun w => w.1 = s).length =
          (l.filter fun w => w.1 = s).length + if z.1 = s then 1 else 0 := by
        intro s
        by_cases hs : z.1 = s <;> simp [List.filter_cons, hs]
      rw [List.length_cons, ih (fun w hw => hl w (List.mem_cons_of_mem _ hw)),
        Finset.sum_congr rfl (fun s _ => e s), Finset.sum_add_distrib, Finset.sum_ite_eq]
      simp [hl z (by simp)]
  rw [key l hl]
  calc ∑ s ∈ TT, (l.filter fun z => z.1 = s).length ≤ ∑ s ∈ TT, c := Finset.sum_le_sum fun s _ => hc s
    _ = TT.card * c := by rw [Finset.sum_const, smul_eq_mul]

theorem nd_OpCl (N N' : Fin n' → Matrix (Fin k) (Fin k) R) (h : ∀ s, N s * N' s = 1) (r T : ℕ) (TT : Finset (Fin n'))
    (c : ℕ) (M : Submodule R (MvPolynomial (Fin n' × Fin k) R)) (hM : ∀ f ∈ M, Lin N f ∈ NDsub R n' k r T) :
    ∀ f ∈ OpCl TT c M, Lin N f ∈ NDsub R n' k r (T + TT.card * c) := by
  intro f hf
  unfold OpCl at hf
  induction hf using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨f0, hf0, l, h1, h2, rfl⟩ := hy
    exact NDsub_mono (Nat.add_le_add_left (word_length TT c l h1 h2) T) (nd_word N N' h r T (hM f0 hf0) l)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

end ND

end Formalism.MainNotions.TestSideCounting
end
end

section

noncomputable section

namespace Formalism.MainNotions.TestSideCounting

open Formalism.MainNotions.G Formalism.MainNotions.Pf14

theorem cleaning_of_admitted : ∃ C : ℝ, 1 ≤ C ∧ ∀ (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ), tableLineDegreeFive.admitted D CLa Ck Crk Cdeg →
    SourceCleaning.aux₃ D C (C + 1) C := by
  obtain ⟨C, hC, H⟩ := Formalism.MainNotions.G.symbolGeneratorData.classMap_estimate_of_admissible
  refine ⟨C, hC, fun D CLa Ck Crk Cdeg hA => ?_⟩
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h15, h16, h17, h18, _, h20, h21, _⟩ := hA
  exact ⟨WittFrameLocaliserOrders.theta_kernel_expansion D, WittFrameLocaliserOrders.splitting_package_holds D, WittFrameLocaliserOrders.segment_statement_holds D, WittFrameLocaliserOrders.order_lemma_holds D,
    WittFrameLocaliserOrders.divisibility_of_field_lemma D h21, H D h15 h16 h17 h18 h20 h21⟩

theorem plane_gram_lemmas_of_admitted (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) (hA : tableLineDegreeFive.admitted D CLa Ck Crk Cdeg) : PlaneGramData.admitted D := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, h11, _, h12, _, h14, h15, _, _, _, _, _, _, _, h23, h24, _⟩ := hA
  have hV : Formalism.MainNotions.CovariantDegrees.ValuationLemmaField D := h12
  have hL52 : Formalism.MainNotions.CovariantDegrees.UnitProductSecondLemma D := h23
  have hL61 : Formalism.MainNotions.CovariantDegrees.DerivativeLemma D := h24
  exact ⟨Joints.isotypic_multiplicity_of_reducibility_alt D hV (GLWeightTheory.weight_condition_from_integral_form D),
    ⟨Joints.valuation_clauses_of_lattice_index D hL61.1, Joints.twisted_valuation_second_sentence D⟩,
    ⟨Joints.isotypic_coefficient_of_degree_bound D h14, Joints.third_degree_bound_gives_span_clause D h15, Joints.span_column_clauses D⟩,
    Joints.projection_of_integral_corollary D h11 hV.2 (GLWeightTheory.weight_condition_from_integral_form D), Joints.digit_identity_of_decomposition D hL52.1,
    Joints.derivation_of_lattice_index D hL61.2.1⟩

theorem plane_gram_of_admitted (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) (hA : tableLineDegreeFive.admitted D CLa Ck Crk Cdeg) {CH : ℝ} (hCH : 26 ≤ CH) :
    PlaneGramData.aux₃ D CH 2 24 60 := by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := plane_gram_lemmas_of_admitted D CLa Ck Crk Cdeg hA
  intro p O _ _ _ _ hSet
  exact Formalism.MainNotions.PlaneGram.stmt D hCH p O hSet
    ⟨a1 p O hSet, ⟨a2.1 p O hSet, a2.2 p O hSet⟩, ⟨a3.1 p O hSet, a3.2.1 p O hSet, a3.2.2 p O hSet⟩, a4 p O hSet,
      a5 p O hSet, a6 p O hSet⟩

theorem theorem_II_closed_of_test_bound : ∃ C : ℝ, 1 ≤ C ∧ ∀ (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ), tableLineDegreeFive.admitted D CLa Ck Crk Cdeg →
    RemainingInputsAfter D CLa Ck Crk Cdeg C (C + 1) C 26 2 24 60 → tableLineDegreeFive.ConclusionE D := by
  obtain ⟨C, hC, H⟩ := cleaning_of_admitted
  refine ⟨C, hC, fun D CLa Ck Crk Cdeg hA h6b => ?_⟩
  exact theorem_II_of_split_cloud_bounds D CLa Ck Crk Cdeg C (C + 1) C 26 2 24 60 hA (H D CLa Ck Crk Cdeg hA)
    (plane_gram_of_admitted D CLa Ck Crk Cdeg hA le_rfl) (rest6a D CLa Ck Crk Cdeg) h6b

end Formalism.MainNotions.TestSideCounting
end
end
