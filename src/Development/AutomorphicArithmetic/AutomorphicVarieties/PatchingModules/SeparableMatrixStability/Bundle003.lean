module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PairedDualFirstOrderDualMatrixSpace
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ThetaCoefficientMapEq
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.LinearAlgebra.Matrix.CharP
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Algebra.ClopenNhdofOne
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Separation.Connected
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle004

@[expose] public section

section

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

section Cont

variable {Γ R : Type} [TopologicalSpace Γ] [CommRing R] {I : Ideal R}

private theorem ac_const (c : R) : AdicCont I fun _ : Γ => c := fun _ => IsLocallyConstant.const _

private theorem ac_add {f g : Γ → R} (hf : AdicCont I f) (hg : AdicCont I g) : AdicCont I fun a => f a + g a := fun N => by
  simpa only [map_add (f := _)] using (hf N).comp₂ (hg N) (· + ·)

private theorem ac_mul {f g : Γ → R} (hf : AdicCont I f) (hg : AdicCont I g) : AdicCont I fun a => f a * g a := fun N => by
  simpa only [map_mul] using (hf N).comp₂ (hg N) (· * ·)

private theorem ac_sum {ι : Type} (s : Finset ι) {f : ι → Γ → R} (hf : ∀ i, AdicCont I (f i)) :
    AdicCont I fun a => ∑ i ∈ s, f i a := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using ac_const (0 : R)
  | insert i s hi ih => simpa only [Finset.sum_insert hi] using ac_add (hf i) ih

private theorem ac_map {S : Type} [CommRing S] (φ : R →+* S) {t : R} {f : Γ → R} (hf : AdicCont (Ideal.span {t}) f) :
    AdicCont (Ideal.span {φ t}) fun a => φ (f a) := fun N => by
  have hle : Ideal.span {t} ^ N ≤ (Ideal.span {φ t} ^ N).comap φ := by
    rw [Ideal.span_singleton_pow, Ideal.span_singleton_pow, Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_pow]
    exact Ideal.mem_span_singleton_self _
  exact (hf N).comp (Ideal.quotientMap _ φ hle)

private theorem ac_nil {t : R} (ht : IsNilpotent t) {f : Γ → R} (hf : AdicCont (Ideal.span {t}) f) :
    IsLocallyConstant f := by
  obtain ⟨N, hN⟩ := ht
  refine IsLocallyConstant.desc _ (Ideal.Quotient.mk (Ideal.span {t} ^ N)) (hf N) ?_
  rw [RingHom.injective_iff_ker_eq_bot, Ideal.mk_ker, Ideal.span_singleton_pow, hN]
  simp

private theorem lc_mat {n : ℕ} {f : Γ → Matrix (Fin n) (Fin n) R} (hf : ∀ i j, IsLocallyConstant fun a => f a i j) :
    IsLocallyConstant f := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro a
  have : ∀ᶠ b in nhds a, ∀ i j, f b i j = f a i j :=
    eventually_all.2 fun i => eventually_all.2 fun j => (hf i j).eventually_eq a
  exact this.mono fun b hb => Matrix.ext hb

end Cont

private theorem epM_entry {A X : Type} [CommRing A] [CommRing X] [Algebra A X] {g n : ℕ}
    (Z : Fin g → Matrix (Fin n) (Fin n) A) (a b : Fin n) :
    (DD.epM fun j => (Z j).map (algebraMap A X)) a b =
      ∑ j, (⟨0, Pi.single j 1, 0, 0⟩ : DD X g) * algebraMap A (DD X g) (Z j a b) := by
  have e : ∀ c : A, algebraMap A (DD X g) c = DD.C (algebraMap A X c) := fun _ => rfl
  have s : ∀ (s : Finset (Fin g)), (∑ j ∈ s, (⟨0, Pi.single j 1, 0, 0⟩ : DD X g) * algebraMap A (DD X g) (Z j a b)) =
      ⟨0, fun i => if i ∈ s then algebraMap A X (Z i a b) else 0, 0, 0⟩ := by
    intro s
    induction s using Finset.induction_on with
    | empty => ext <;> simp
    | insert i s hi ih =>
      rw [Finset.sum_insert hi, ih, e]
      ext j
      · simp
      · by_cases h : j = i
        · subst h; simp [hi]
        · simp [h]
      · simp
      · simp
  rw [s]
  simp [DD.epM]

private theorem ρX_cont {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x : NP F n) (X : Type) [CommRing X]
    [Algebra x.A X] (i j : Fin n) : AdicCont (Ideal.span {algebraMap x.A X x.t}) fun g => x.ρX X g i j := by
  have h := x.cont i j
  rw [PowerSeries.maximalIdeal_eq_span_X] at h
  exact ac_map (algebraMap x.A X) h

theorem UpperTheory.V.Pa.rho_hom :
    ∀ (l : ℕ) [Fact l.Prime] (F : GFrame l) (n : ℕ) (x : NP F n) (k : Kap x) (X : Type) [CommRing X] [Algebra x.A X], (x.ρX X 1 = 1 ∧ (∀ g h, x.ρX X (g * h) = x.ρX X g * x.ρX X h) ∧ ∀ i j, AdicCont (Ideal.span {algebraMap x.A X x.t}) fun g => x.ρX X g i j) ∧ (k.ρ1 X 1 = 1 ∧ (∀ g h, k.ρ1 X (g * h) = k.ρ1 X g * k.ρ1 X h) ∧ ∀ i j, AdicCont (Ideal.span {algebraMap x.A (DD X k.g) x.t}) fun g => k.ρ1 X g i j) ∧ (IsNilpotent (algebraMap x.A X x.t) → IsLocallyConstant (x.ρX X) ∧ IsLocallyConstant (k.ρ1 X)) ∧ ∀ v, k.w1 X v * k.wi1 X v = 1 ∧ x.wX X v * x.wiX X v = 1 := by
  intro l _ F n x k X _ _
  obtain ⟨h1, h2, -, h4⟩ := Det.rho1Hom k X
  have c1 : ∀ i j, AdicCont (Ideal.span {algebraMap x.A (DD X k.g) x.t}) fun g => k.ρ1 X g i j := by
    intro i j
    simp only [Kap.ρ1, Matrix.mul_apply, Matrix.add_apply, epM_entry]
    refine ac_sum _ fun c => ac_mul (ac_add (ac_const _) (ac_sum _ fun a => ac_mul (ac_const _) ?_)) (ρX_cont x _ c j)
    exact ac_map (algebraMap x.A (DD X k.g)) ((k.mem a).2.1 i c)
  refine ⟨⟨by simp [NP.ρX, mat], fun g h => by simp [NP.ρX, mat, Matrix.map_mul], ρX_cont x X⟩, ⟨h1, h2, c1⟩,
    fun ht => ⟨lc_mat fun i j => ac_nil ht (ρX_cont x X i j), lc_mat fun i j => ac_nil ?_ (c1 i j)⟩,
    fun v => ⟨(h4 v).1, ?_⟩⟩
  · exact ht.map (DD.C : X →+* DD X k.g)
  · rw [NP.wX, NP.wiX, ← Matrix.map_mul]; simp
end

section

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

section Abs

variable {K M : Type} [Group K] [Ring M] (ρ z : K → M) (h1 : ρ 1 = 1) (hm : ∀ g h, ρ (g * h) = ρ g * ρ h)
  (hz : ∀ g h, z (g * h) = z g + ρ g * z h * ρ g⁻¹)

include h1 hz in
private theorem cocycle_apply_one_eq_zero : z 1 = 0 := by
  simpa [h1] using hz 1 1

include h1 hm in
private theorem cp_inv {g : K} (hg : ρ g = 1) : ρ g⁻¹ = 1 := by
  have := hm g g⁻¹
  rw [mul_inv_cancel, h1, hg, one_mul] at this
  exact this.symm

include h1 hm hz in
private theorem cp_add {g : K} (hg : ρ g = 1) (h : K) : z (g * h) = z g + z h := by
  rw [hz, hg, cp_inv ρ h1 hm hg, one_mul, mul_one]

include h1 hm hz in
private theorem cp_pow {g : K} (hg : ρ g = 1) (k : ℕ) : ρ (g ^ k) = 1 ∧ z (g ^ k) = k • z g := by
  induction k with
  | zero => exact ⟨by simpa using h1, by simpa using cocycle_apply_one_eq_zero ρ z h1 hz⟩
  | succ k ih =>
    refine ⟨by rw [pow_succ', hm, hg, ih.1, one_mul], ?_⟩
    rw [pow_succ', cp_add ρ z h1 hm hz hg, ih.2, succ_nsmul']

include h1 hm hz in
private theorem cp_U [TopologicalSpace K] (cρ : IsLocallyConstant ρ) (cz : IsLocallyConstant z) :
    ∃ U : OpenNormalSubgroup K, ∀ g, g ∈ U ↔ ρ g = 1 ∧ z g = 0 := by
  have hinv : ∀ g, ρ g = 1 → z g = 0 → ρ g⁻¹ = 1 ∧ z g⁻¹ = 0 := by
    intro g hg hzg
    refine ⟨cp_inv ρ h1 hm hg, ?_⟩
    have := cp_add ρ z h1 hm hz hg g⁻¹
    rwa [mul_inv_cancel, cocycle_apply_one_eq_zero ρ z h1 hz, hzg, zero_add, eq_comm] at this
  let S : Subgroup K :=
    { carrier := {g | ρ g = 1 ∧ z g = 0}
      mul_mem' := by
        rintro a b ⟨ha, hza⟩ ⟨hb, hzb⟩
        exact ⟨by rw [hm, ha, hb, one_mul], by rw [cp_add ρ z h1 hm hz ha, hza, hzb, zero_add]⟩
      one_mem' := ⟨h1, cocycle_apply_one_eq_zero ρ z h1 hz⟩
      inv_mem' := by
        rintro a ⟨ha, hza⟩
        exact hinv a ha hza }
  have hS : IsOpen (S : Set K) := (cρ.isOpen_fiber 1).inter (cz.isOpen_fiber 0)
  have hN : S.Normal := by
    constructor
    rintro a ⟨ha, hza⟩ k
    show ρ (k * a * k⁻¹) = 1 ∧ z (k * a * k⁻¹) = 0
    refine ⟨?_, ?_⟩
    · rw [hm, hm, ha, mul_one, ← hm, mul_inv_cancel, h1]
    · rw [mul_assoc, hz, cp_add ρ z h1 hm hz ha, hza, zero_add, ← hz, mul_inv_cancel, cocycle_apply_one_eq_zero ρ z h1 hz]
  exact ⟨{ toOpenSubgroup := ⟨S, hS⟩, isNormal' := hN }, fun g => Iff.rfl⟩

end Abs

private theorem cp_lc {K R : Type} [TopologicalSpace K] [CommRing R] {n : ℕ} (I : Ideal R)
    (f : K → Matrix (Fin n) (Fin n) R) (hf : ∀ i j, AdicCont I fun g => f g i j) (m : ℕ) :
    IsLocallyConstant fun g => (Ideal.Quotient.mk (I ^ m)).mapMatrix (f g) := by
  rw [IsLocallyConstant.iff_isOpen_fiber]
  intro y
  have e : (fun g => (Ideal.Quotient.mk (I ^ m)).mapMatrix (f g)) ⁻¹' {y} =
      ⋂ i, ⋂ j, (fun g => Ideal.Quotient.mk (I ^ m) (f g i j)) ⁻¹' {y i j} := by
    ext g
    simp [← Matrix.ext_iff]
  rw [e]
  exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => (hf i j m).isOpen_fiber _

private theorem cp_zero {R : Type} [CommRing R] {n : ℕ} (J : Ideal R) (A : Matrix (Fin n) (Fin n) R) :
    (Ideal.Quotient.mk J).mapMatrix A = 0 ↔ ∀ i j, A i j ∈ J := by
  rw [← Matrix.ext_iff]
  simp [Ideal.Quotient.eq_zero_iff_mem]

private theorem cp_one {R : Type} [CommRing R] {n : ℕ} (J : Ideal R) (A : Matrix (Fin n) (Fin n) R) :
    (Ideal.Quotient.mk J).mapMatrix A = 1 ↔ ∀ i j, (A - 1) i j ∈ J := by
  rw [← sub_eq_zero, ← map_one (Ideal.Quotient.mk J).mapMatrix, ← map_sub, cp_zero]

theorem UpperTheory.V.Pa.coc_pl :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G : Glob l L) (n : ℕ) (R : Type) [CommRing R] (I : Ideal R) (ρ z : G.G₀ → Matrix (Fin n) (Fin n) R) (H : Subgroup G.Γ) [H.Normal], IsOpen (H : Set G.Γ) → H ≤ G.η.ker → (l : R) = 0 → ρ 1 = 1 → (∀ g h, ρ (g * h) = ρ g * ρ h) → (∀ i j, AdicCont I fun g => ρ g i j) → (∀ (m : ℕ) (h : G.G₀), (h : G.Γ) ∈ H → ∃ e : ℕ, ∀ i j, (ρ (h ^ l ^ e) - 1) i j ∈ I ^ m) → (∀ i j, AdicCont I fun g => z g i j) → (∀ g h, z (g * h) = z g + ρ g * z h * ρ g⁻¹) → (∀ (m : ℕ) (h : G.G₀), (h : G.Γ) ∈ H → ∃ e : ℕ, ∀ i j, (ρ (h ^ l ^ e) - 1) i j ∈ I ^ m ∧ z (h ^ l ^ e) i j ∈ I ^ m) ∧ ∀ k : G.G₀, (k : G.Γ) ∈ PL l H → ∀ (m : ℕ) i j, (ρ k - 1) i j ∈ I ^ m ∧ z k i j ∈ I ^ m := by
  intro l _ L G n R _ I ρ z H _ hHo hHk hl h1 hm hρc hρH hzc hz
  have main : ∀ m : ℕ, (∀ (h : G.G₀), (h : G.Γ) ∈ H → ∃ e : ℕ, ∀ i j,
      (ρ (h ^ l ^ e) - 1) i j ∈ I ^ m ∧ z (h ^ l ^ e) i j ∈ I ^ m) ∧
      ∀ k : G.G₀, (k : G.Γ) ∈ PL l H → ∀ i j, (ρ k - 1) i j ∈ I ^ m ∧ z k i j ∈ I ^ m := by
    intro m
    let ρ' := fun x => (Ideal.Quotient.mk (I ^ m)).mapMatrix (ρ x)
    let z' := fun x => (Ideal.Quotient.mk (I ^ m)).mapMatrix (z x)
    have h1' : ρ' 1 = 1 := by simp [ρ', h1]
    have hm' : ∀ a b, ρ' (a * b) = ρ' a * ρ' b := by
      intro a b
      simp [ρ', hm]
    have hz' : ∀ a b, z' (a * b) = z' a + ρ' a * z' b * ρ' a⁻¹ := by
      intro a b
      simp only [z', ρ', hz, map_add (f := _), map_mul]
    have hlq : ((l : ℕ) : R ⧸ I ^ m) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk (I ^ m)), hl, map_zero]
    have key : ∀ g : G.G₀, ρ' g = 1 → ρ' (g ^ l) = 1 ∧ z' (g ^ l) = 0 := by
      intro g hg
      obtain ⟨p1, p2⟩ := cp_pow ρ' z' h1' hm' hz' hg l
      refine ⟨p1, p2.trans ?_⟩
      ext i j
      simp [Matrix.smul_apply, nsmul_eq_mul, hlq]
    have P1 : ∀ (h : G.G₀), (h : G.Γ) ∈ H → ∃ e : ℕ, ∀ i j,
        (ρ (h ^ l ^ e) - 1) i j ∈ I ^ m ∧ z (h ^ l ^ e) i j ∈ I ^ m := by
      intro h hh
      obtain ⟨e, he⟩ := hρH m h hh
      refine ⟨e + 1, fun i j => ?_⟩
      rw [pow_succ l e, pow_mul]
      obtain ⟨q1, q2⟩ := key _ ((cp_one _ _).2 he)
      exact ⟨(cp_one _ _).1 q1 i j, (cp_zero _ _).1 q2 i j⟩
    refine ⟨P1, ?_⟩
    obtain ⟨U, hU⟩ := cp_U ρ' z' h1' hm' hz' (cp_lc I ρ hρc m) (cp_lc I z hzc m)
    intro k hk i j
    have hkU : k ∈ U := by
      refine pl_sub l G.Γ H G.η.ker G.η_open hHk U ?_ k hk
      intro h hh
      obtain ⟨e, he⟩ := P1 h hh
      exact ⟨e, (hU _).2 ⟨(cp_one _ _).2 fun i j => (he i j).1, (cp_zero _ _).2 fun i j => (he i j).2⟩⟩
    obtain ⟨q1, q2⟩ := (hU k).1 hkU
    exact ⟨(cp_one _ _).1 q1 i j, (cp_zero _ _).1 q2 i j⟩
  exact ⟨fun m h hh => (main m).1 h hh, fun k hk m i j => (main m).2 k hk i j⟩
end

section

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem cast_zero (l : ℕ) [Fact l.Prime] (K : Type) [Field K] [Finite K] [Algebra ℤ_[l] K] : (l : K) = 0 := by
  have hni : ¬ Function.Injective (algebraMap ℤ_[l] K) := by
    haveI : Infinite ℤ_[l] := Infinite.of_injective (Nat.cast : ℕ → ℤ_[l]) Nat.cast_injective
    exact not_injective_infinite_finite _
  have hker : RingHom.ker (algebraMap ℤ_[l] K) ≠ ⊥ := by
    intro h
    exact hni ((RingHom.injective_iff_ker_eq_bot _).2 h)
  obtain ⟨e, he⟩ := PadicInt.ideal_eq_span_pow_p hker
  have hmem : (l : ℤ_[l]) ^ e ∈ RingHom.ker (algebraMap ℤ_[l] K) := by
    rw [he]
    exact Ideal.subset_span rfl
  rw [RingHom.mem_ker, map_pow, map_natCast] at hmem
  exact pow_eq_zero_iff'.mp hmem |>.1

private theorem key (l : ℕ) [Fact l.Prime] (K : Type) [Field K] (hl : (l : K) = 0) (n : ℕ)
    (P : Matrix (Fin n) (Fin n) (PowerSeries K))
    (hP : P.charpoly.map (PowerSeries.constantCoeff : PowerSeries K →+* K) = (Polynomial.X - 1) ^ n) (m : ℕ) :
    ∃ e : ℕ, ∀ i j, (P ^ l ^ e - 1) i j ∈ Ideal.span {(PowerSeries.X : PowerSeries K) ^ m} := by
  classical
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨0, fun i => i.elim0⟩
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  haveI : CharP K l := (CharP.charP_iff_prime_eq_zero (Fact.out : l.Prime)).2 hl
  haveI : CharP (PowerSeries K) l :=
    charP_of_injective_algebraMap (algebraMap K (PowerSeries K)).injective l
  set I : Ideal (PowerSeries K) := Ideal.span {PowerSeries.X} with hI
  have hmul : ∀ (A B : Matrix (Fin n) (Fin n) (PowerSeries K)) (J J' : Ideal (PowerSeries K)),
      (∀ i j, A i j ∈ J) → (∀ i j, B i j ∈ J') → ∀ i j, (A * B) i j ∈ J * J' := by
    intro A B J J' hA hB i j
    rw [Matrix.mul_apply]
    exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_mul (hA i k) (hB k j)
  have hpow : ∀ (A : Matrix (Fin n) (Fin n) (PowerSeries K)) (J : Ideal (PowerSeries K)),
      (∀ i j, A i j ∈ J) → ∀ k : ℕ, ∀ i j, (A ^ k) i j ∈ J ^ k := by
    intro A J hA k
    induction k with
    | zero => intro i j; simp
    | succ k ih =>
      intro i j
      rw [pow_succ, pow_succ]
      exact hmul _ _ _ _ ih hA i j
  set d := P.charpoly - (Polynomial.X - 1) ^ n with hd
  have hdmap : d.map (PowerSeries.constantCoeff : PowerSeries K →+* K) = 0 := by
    rw [hd, Polynomial.map_sub, hP, Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X,
      Polynomial.map_one, sub_self]
  have hdc : ∀ k, d.coeff k ∈ I := by
    intro k
    rw [hI, Ideal.mem_span_singleton, PowerSeries.X_dvd_iff]
    have := congrArg (fun q => _root_.AddMonoidAlgebra.coeff (M := ℕ) q k) hdmap
    simpa [Polynomial.coeff_map] using this
  have hev : Polynomial.aeval P d = -(P - 1) ^ n := by
    rw [hd, map_sub, Matrix.aeval_self_charpoly, map_pow, map_sub, Polynomial.aeval_X, map_one,
      zero_sub]
  have hA : ∀ i j, (Polynomial.aeval P d) i j ∈ I := by
    intro i j
    rw [Polynomial.aeval_eq_sum_range, Matrix.sum_apply]
    exact Ideal.sum_mem _ fun k _ => by
      rw [Matrix.smul_apply, smul_eq_mul]
      exact Ideal.mul_mem_right _ _ (hdc k)
  have hQ : ∀ i j, ((P - 1) ^ n) i j ∈ I := by
    intro i j
    have h1 : (P - 1) ^ n = -(Polynomial.aeval P d) := by rw [hev, neg_neg]
    rw [h1, Matrix.neg_apply]
    exact I.neg_mem (hA i j)
  refine ⟨n * m, fun i j => ?_⟩
  have hle : n * m ≤ l ^ (n * m) := (Nat.lt_pow_self (Fact.out : l.Prime).one_lt).le
  have hsub : P ^ l ^ (n * m) - 1 = (P - 1) ^ l ^ (n * m) := by
    rw [sub_pow_char_pow_of_commute l (n * m) (Commute.one_right P), one_pow]
  obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le hle
  rw [hsub, hr, pow_add, pow_mul]
  have h2 := hmul (((P - 1) ^ n) ^ m) ((P - 1) ^ r) (I ^ m) ⊤ (hpow _ _ hQ m)
    (fun a b => Submodule.mem_top (x := ((P - 1) ^ r) a b)) i j
  rwa [Ideal.mul_top, hI, Ideal.span_singleton_pow] at h2

theorem UpperTheory.V.Pa.unip_of :
    ∀ (l : ℕ) [Fact l.Prime] (F : GFrame l) (n : ℕ) (x : NP F n) (H : Subgroup F.Γ), (∀ h : F.G₀, (h : F.Γ) ∈ H → (mat x.ρ h).charpoly.map (PowerSeries.constantCoeff : x.A →+* x.K) = (Polynomial.X - 1) ^ n) → x.UnipOn H := by
  intro l _ F n x H hH m h hh
  obtain ⟨e, he⟩ := key l x.K (cast_zero l x.K) n (mat x.ρ h) (hH h hh) m
  exact ⟨e, fun i j => by rw [map_pow]; exact he i j⟩
end

section

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

section

variable {A X X' : Type} [CommRing A] [CommRing X] [Algebra A X] [CommRing X'] [Algebra A X'] (f : X →ₐ[A] X') {n : ℕ}

private theorem map_alg (M : Matrix (Fin n) (Fin n) A) :
    (M.map (algebraMap A X)).map f = M.map (algebraMap A X') := by
  ext i j; simp

private theorem map_mul_alg (M N : Matrix (Fin n) (Fin n) X) : (M * N).map f = M.map f * N.map f :=
  map_mul f.mapMatrix M N

private theorem map_add_one (M : Matrix (Fin n) (Fin n) X) : (1 + M).map f = 1 + M.map f := by
  rw [Matrix.map_add _ (map_add f), Matrix.map_one _ (map_zero f) (map_one f)]

private theorem map_sub_one (M : Matrix (Fin n) (Fin n) X) : (1 - M).map f = 1 - M.map f := by
  rw [Matrix.map_sub _ (map_sub f), Matrix.map_one _ (map_zero f) (map_one f)]

private theorem map_epM {g : ℕ} (Z : Fin g → Matrix (Fin n) (Fin n) A) :
    (DD.epM fun j => (Z j).map (algebraMap A X)).map (DD.map g f) = DD.epM fun j => (Z j).map (algebraMap A X') := by
  ext i j <;> simp [DD.epM, DD.map]

private theorem blk_map (a : ℕ) (V₁ V₂ : Submodule A X) (V₁' V₂' : Submodule A X')
    (h₁ : ∀ y ∈ V₁, f y ∈ V₁') (h₂ : ∀ y ∈ V₂, f y ∈ V₂') :
    ∀ Z ∈ blkMat n a V₁ V₂, Z.map f ∈ blkMat n a V₁' V₂' :=
  fun _ hZ i j => ⟨fun e => h₁ _ ((hZ i j).1 e), fun e => h₂ _ ((hZ i j).2 e)⟩

private theorem part_map (g : ℕ) (b₁ b₂ b₃ b₄ : Bool) :
    ∀ y ∈ ddPart A X g b₁ b₂ b₃ b₄, DD.map g f y ∈ ddPart A X' g b₁ b₂ b₃ b₄ := by
  rintro y ⟨ha, hep, hep', heta⟩
  refine ⟨fun hb => ?_, fun hb => ?_, fun hb => ?_, fun hb => ?_⟩
  · show f y.a = 0
    rw [ha hb, map_zero]
  · show (fun j => f (y.ep j)) = 0
    funext j
    rw [hep hb]
    simp
  · show (fun j => f (y.ep' j)) = 0
    funext j
    rw [hep' hb]
    simp
  · show f y.eta = 0
    rw [heta hb, map_zero]

end

theorem UpperTheory.V.Pa.sel_red :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n) (k : Kap x) (X X' : Type) [CommRing X] [Algebra x.A X] [CommRing X'] [Algebra x.A X'] (f : X →ₐ[x.A] X'), (∀ z ∈ SelP h x X, (fun g => (z g).map f) ∈ SelP h x X') ∧ (∀ z ∈ Sel1 h X k, (fun g => (z g).map (DD.map k.g f)) ∈ Sel1 h X' k) ∧ (∀ z ∈ Sel2 h X k, (fun g => (z g).map (DD.map k.g f)) ∈ Sel2 h X' k) ∧ (∀ g, (k.ρ1 X g).map (DD.map k.g f) = k.ρ1 X' g) ∧ ∀ v, (k.w1 X v).map (DD.map k.g f) = k.w1 X' v ∧ (k.wi1 X v).map (DD.map k.g f) = k.wi1 X' v := by
  intro l _ L G G0 h n x k X X' _ _ _ _ f
  have hρ1 : ∀ g, (k.ρ1 X g).map (DD.map k.g f) = k.ρ1 X' g := by
    intro g
    unfold Kap.ρ1 NP.ρX
    rw [map_mul_alg, map_add_one, map_epM, map_alg]
  have hw1 : ∀ v, (k.w1 X v).map (DD.map k.g f) = k.w1 X' v := by
    intro v
    unfold Kap.w1 NP.wX
    rw [map_mul_alg, map_sub_one, map_epM, map_alg]
  have hwi1 : ∀ v, (k.wi1 X v).map (DD.map k.g f) = k.wi1 X' v := by
    intro v
    unfold Kap.wi1 NP.wiX
    rw [map_mul_alg, map_add_one, map_epM, map_alg]
  refine ⟨fun z hz => ?_, fun z hz => ?_, fun z hz => ?_, hρ1, fun v => ⟨hw1 v, hwi1 v⟩⟩
  · have hV : ∀ Z ∈ Ev x.A X n x.a, Z.map f ∈ Ev x.A X' n x.a :=
      blk_map f x.a ⊤ ⊥ ⊤ ⊥ (fun _ _ => Submodule.mem_top) (fun y hy => by
        rw [Submodule.mem_bot] at hy ⊢
        rw [hy, map_zero])
    have H := (sel_map l G.frame n x.A X X' f x.t (fun g => x.ρX X (h.p₀ g)) (x.wX X) (x.wiX X) _ _ hV z).1 hz
    simp only [NP.ρX, NP.wX, NP.wiX, map_alg] at H
    exact H
  · have hV : ∀ Z ∈ W1 n x.A X k.g x.a, Z.map (DD.map k.g f) ∈ W1 n x.A X' k.g x.a :=
      blk_map (DD.map k.g f) x.a _ _ _ _ (part_map f k.g _ _ _ _) (part_map f k.g _ _ _ _)
    have H := (sel_map l G.frame n x.A (DD X k.g) (DD X' k.g) (DD.map k.g f) x.t
      (fun g => k.ρ1 X (h.p₀ g)) (k.w1 X) (k.wi1 X) _ _ hV z).1 hz
    simp only [hρ1, hw1, hwi1] at H
    exact H
  · have hV : ∀ Z ∈ W2 n x.A X k.g x.a, Z.map (DD.map k.g f) ∈ W2 n x.A X' k.g x.a :=
      blk_map (DD.map k.g f) x.a _ _ _ _ (part_map f k.g _ _ _ _) (part_map f k.g _ _ _ _)
    have H := (sel_map l G.frame n x.A (DD X k.g) (DD X' k.g) (DD.map k.g f) x.t
      (fun g => k.ρ1 X (h.p₀ g)) (k.w1 X) (k.wi1 X) _ _ hV z).1 hz
    simp only [hρ1, hw1, hwi1] at H
    exact H
end

section

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

theorem UpperTheory.V.Pa.close_map :
    ∀ (Ph B Z : Type) [Group Ph] [TopologicalSpace Ph] [IsTopologicalGroup Ph] [CompactSpace Ph] [TotallyDisconnectedSpace Ph] [Group B] [Group Z] [TopologicalSpace Z] [IsTopologicalGroup Z] [CompactSpace Z] [TotallyDisconnectedSpace Z] (Γ : ℕ → Type) [∀ N, Group (Γ N)] (π : ∀ N, Ph →* Γ N) (πo : Ph →* B) (p : ∀ N, Γ N →* Z) (po : B →* Z) (U : Ultrafilter ℕ) (a : ∀ N, Γ N) (b : B) (z : Z), Continuous (po.comp πo) → (∀ W : OpenNormalSubgroup Z, ∀ᶠ N in (U : Filter ℕ), ∀ g, p N (π N g) * (po (πo g))⁻¹ ∈ W) → (∀ V : OpenNormalSubgroup Ph, ∀ᶠ N in (U : Filter ℕ), Close (π N) πo V.toSubgroup (a N) b) → (∀ W : OpenNormalSubgroup Z, ∀ᶠ N in (U : Filter ℕ), p N (a N) * z⁻¹ ∈ W) → po b = z := by
  intro Ph B Z _ _ _ _ _ _ _ _ _ _ _ Γ _ π πo p po U a b z hf hp hclose ha
  set f : Ph →* Z := po.comp πo with hfdef
  have key : ∀ W : OpenNormalSubgroup Z, po b * z⁻¹ ∈ W := by
    intro W
    let V : OpenNormalSubgroup Ph :=
      { toOpenSubgroup := ⟨W.toSubgroup.comap f, W.isOpen.preimage hf⟩
        isNormal' := Subgroup.Normal.comap W.isNormal' f }
    obtain ⟨N, h1, h2, h3⟩ := ((hp W).and ((hclose V).and (ha W))).exists
    obtain ⟨g, g', hg, hg', hV⟩ := h2
    have hV' : f (g⁻¹ * g') ∈ W := hV
    have e1 := h1 g
    rw [hg] at e1
    have hb : po b = f g' := by simp [hfdef, hg']
    have hn : f g' * (f g)⁻¹ ∈ W := by
      have hc := W.isNormal'.conj_mem _ hV' (f g)
      have he : f g * f (g⁻¹ * g') * (f g)⁻¹ = f g' * (f g)⁻¹ := by
        simp [map_mul, map_inv, mul_assoc]
      rw [he] at hc
      exact hc
    have hx : po b * z⁻¹ = (f g' * (f g)⁻¹) * (p N (a N) * (f g)⁻¹)⁻¹ * (p N (a N) * z⁻¹) := by
      rw [hb]; group
    rw [hx]
    exact W.mul_mem (W.mul_mem hn (W.inv_mem e1)) h3
  by_contra hne
  have hx1 : po b * z⁻¹ ≠ 1 := fun h => hne (mul_inv_eq_one.mp h)
  obtain ⟨H, hH⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    (isOpen_compl_singleton (x := po b * z⁻¹)) (by simpa [eq_comm] using hx1)
  exact hH (key H) rfl
end
