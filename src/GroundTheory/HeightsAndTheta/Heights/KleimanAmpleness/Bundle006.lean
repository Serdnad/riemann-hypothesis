module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.AlgebraMapMemChartRingLine
import Mathlib.Algebra.Lie.OfAssociative
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
import Mathlib.NumberTheory.Chebyshev
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

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

namespace Cech

variable {n : ℕ} {U : Finset (Fin n)} {R : Type u} [CommRing R] {G : Cell U → Type v}
  [∀ I, AddCommGroup (G I)] [∀ I, Module R (G I)] {ρ : ∀ I J : Cell U, I.1 ⊆ J.1 → G I →ₗ[R] G J}

theorem subsingleton_H_one_iff :
    Subsingleton (H G ρ 1) ↔ ∀ z : Cochain G 1, d G ρ 1 z = 0 → ∃ w : Cochain G 0, d G ρ 0 w = z := by
  unfold H
  rw [Submodule.Quotient.subsingleton_iff, Submodule.comap_subtype_eq_top]
  constructor
  · intro h z hz
    exact h (LinearMap.mem_ker.mpr hz)
  · intro h z hz
    exact h z (LinearMap.mem_ker.mp hz)

theorem sgn_mul_sgn_erase {J : Finset (Fin n)} {j k : Fin n} (hj : j ∈ J) (hk : k ∈ J) (hjk : j ≠ k) :
    sgn J j * sgn (J.erase j) k = -(sgn J k * sgn (J.erase k) j) := by
  wlog h : j < k generalizing j k
  · have h' : k < j := lt_of_le_of_ne (not_lt.mp h) hjk.symm
    rw [this hk hj hjk.symm h', neg_neg]
  have hmem : j ∈ J.filter (· < k) := Finset.mem_filter.mpr ⟨hj, h⟩
  have e1 : (J.erase j).filter (· < k) = (J.filter (· < k)).erase j := by rw [Finset.filter_erase]
  have e2 : (J.erase k).filter (· < j) = J.filter (· < j) := by
    rw [Finset.filter_erase]
    apply Finset.erase_eq_of_notMem
    simp only [Finset.mem_filter, not_and, not_lt]
    intro _; exact h.le
  have hb : 1 ≤ (J.filter (· < k)).card := Finset.card_pos.mpr ⟨j, hmem⟩
  unfold sgn
  rw [e1, e2, Finset.card_erase_of_mem hmem]
  obtain ⟨b', hb'⟩ : ∃ b', (J.filter (· < k)).card = b' + 1 := ⟨_, (Nat.sub_add_cancel hb).symm⟩
  rw [hb', Nat.add_sub_cancel, pow_succ]
  ring

theorem d_one_d_zero
    (hρ : ∀ (I J K : Cell U) (h : I.1 ⊆ J.1) (h' : J.1 ⊆ K.1) (m : G I),
      ρ J K h' (ρ I J h m) = ρ I K (h.trans h') m)
    (w : Cochain G 0) : d G ρ 1 (d G ρ 0 w) = 0 := by
  funext J
  have key : ∀ (K K' : Idx U 0) (h : K.1.1 ⊆ J.1.1) (h' : K'.1.1 ⊆ J.1.1), K = K' →
      ρ K.1 J.1 h (w K) = ρ K'.1 J.1 h' (w K') := by
    rintro K _ h h' rfl; rfl
  rw [d_apply]

  simp only [d_apply, map_sum, map_zsmul, hρ, Finset.smul_sum, smul_smul]
  rw [Pi.zero_apply, Finset.sum_sigma']
  refine Finset.sum_involution
    (fun p _ => ⟨⟨p.2.1, Finset.mem_of_mem_erase p.2.2⟩,
      ⟨p.1.1, Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp p.2.2).1.symm, p.1.2⟩⟩⟩) ?_ ?_
    (fun _ _ => Finset.mem_univ _) (fun p _ => rfl)
  · rintro ⟨⟨j, hj⟩, ⟨k, hk⟩⟩ -
    have hk' := Finset.mem_erase.mp hk
    have hidx : face (face J ⟨j, hj⟩) ⟨k, hk⟩ =
        face (face J ⟨k, hk'.2⟩) ⟨j, Finset.mem_erase.mpr ⟨hk'.1.symm, hj⟩⟩ :=
      Subtype.ext (Subtype.ext (Finset.erase_right_comm))
    dsimp only
    rw [key _ _ _ (((face_subset _ _).trans (face_subset _ _))) hidx, ← add_smul]
    have hs : sgn J.1.1 j * sgn (face J ⟨j, hj⟩).1.1 k =
        -(sgn J.1.1 k * sgn (face J ⟨k, hk'.2⟩).1.1 j) :=
      sgn_mul_sgn_erase hj hk'.2 hk'.1.symm
    rw [hs, neg_add_cancel, zero_smul]
  · rintro ⟨⟨j, hj⟩, ⟨k, hk⟩⟩ - - heq
    exact (Finset.mem_erase.mp hk).1 (congrArg (fun p => p.1.1) heq)

end Cech

namespace SubSystem

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

section General

variable {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]

theorem d_one_d_zero (F : SubSystem S x E) (w : Cech.Cochain (fun I => F.sub I) 0) :
    Cech.d (fun I => F.sub I) F.res 1 (Cech.d (fun I => F.sub I) F.res 0 w) = 0 :=
  Cech.d_one_d_zero (fun _ _ _ _ _ _ => rfl) w



theorem subsingleton_H_one_of_quot (F G : SubSystem S x E)
    (hGF : ∀ I, ∀ y ∈ G.sub I, y ∈ F.sub I) (hG : Subsingleton (G.H 1))
    (hQ : Subsingleton (quotH F G 1)) : Subsingleton (F.H 1) := by
  unfold SubSystem.H at hG ⊢
  unfold quotH at hQ
  rw [Cech.subsingleton_H_one_iff] at hG hQ ⊢
  intro z hz
  let q : ∀ I, F.sub I →ₗ[S] (F.sub I ⧸ quotSub F G I) := fun I => (quotSub F G I).mkQ
  have hq : ∀ I J h m, q J (F.res I J h m) = quotRes F G I J h (q I m) := fun _ _ _ _ => rfl
  have hqd := Cech.mapC_d (R := S) (G := fun I => ↥(F.sub I))
    (G' := fun I => ↥(F.sub I) ⧸ quotSub F G I) q hq
  obtain ⟨wb, hwb⟩ := hQ (Cech.mapC (R := S) (G := fun I => ↥(F.sub I)) (G' := fun I => ↥(F.sub I) ⧸ quotSub F G I) q 1 z) (by rw [← hqd, hz, map_zero])
  choose w hw using fun I : Cech.Idx (support x) 0 => Submodule.Quotient.mk_surjective _ (wb I)
  have hmw : (Cech.mapC (R := S) (G := fun I => ↥(F.sub I)) (G' := fun I => ↥(F.sub I) ⧸ quotSub F G I) q 0 w) = wb := funext hw
  have hr : (Cech.mapC (R := S) (G := fun I => ↥(F.sub I)) (G' := fun I => ↥(F.sub I) ⧸ quotSub F G I) q 1 (z - Cech.d (fun I => F.sub I) F.res 0 w)) = 0 := by
    rw [map_sub, hqd 0, hmw, hwb]
    exact @sub_eq_zero_of_eq (Cech.Cochain (fun I => ↥(F.sub I) ⧸ quotSub F G I) 1) _ _ _ rfl
  have hrG : ∀ J, (((z - Cech.d (fun I => F.sub I) F.res 0 w) J : F.sub J.1) : E) ∈ G.sub J.1 :=
    fun J => (Submodule.Quotient.mk_eq_zero (quotSub F G J.1)).mp (congrFun hr J)
  let ι : ∀ I, G.sub I →ₗ[S] F.sub I := fun I =>
    { toFun := fun y => ⟨y, hGF I y y.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hι : ∀ I J h m, ι J (G.res I J h m) = F.res I J h (ι I m) := fun _ _ _ _ => rfl
  have hιd := Cech.mapC_d (R := S) (G := fun I => ↥(G.sub I)) (G' := fun I => ↥(F.sub I)) ι hι
  have hιinj : ∀ i, Function.Injective (Cech.mapC (R := S) (G := fun I => ↥(G.sub I)) (G' := fun I => ↥(F.sub I)) ι i) := fun i a b hab =>
    funext fun I => Subtype.ext (congrArg (fun c => ((c I : F.sub I.1) : E)) hab)
  obtain ⟨g, hg⟩ : ∃ g : Cech.Cochain (fun I => ↥(G.sub I)) 1,
      (Cech.mapC (R := S) (G := fun I => ↥(G.sub I)) (G' := fun I => ↥(F.sub I)) ι 1 g) =
        z - Cech.d (fun I => F.sub I) F.res 0 w := ⟨fun J => ⟨_, hrG J⟩, rfl⟩
  have hdg : Cech.d (fun I => ↥(G.sub I)) G.res 1 g = 0 := by
    have h2 : (Cech.mapC (R := S) (G := fun I => ↥(G.sub I)) (G' := fun I => ↥(F.sub I)) ι (1 + 1)
        (Cech.d (fun I => ↥(G.sub I)) G.res 1 g)) = 0 := by
      rw [hιd 1 g, hg, map_sub, hz, d_one_d_zero, sub_zero]
    exact hιinj (1 + 1) (h2.trans (LinearMap.map_zero _).symm)
  obtain ⟨v, hv⟩ := hG g hdg
  refine ⟨w + (Cech.mapC (R := S) (G := fun I => ↥(G.sub I)) (G' := fun I => ↥(F.sub I)) ι 0 v), ?_⟩
  rw [map_add (f := _), ← hιd, hv, hg, add_sub_cancel]

end General

theorem subsingleton_H_one_of_smul (F' G : SubSystem S x Ω) (σ : Ω) (hσ : σ ≠ 0)
    (hG : ∀ I z, z ∈ G.sub I ↔ ∃ y ∈ F'.sub I, z = σ * y) (hF : Subsingleton (F'.H 1)) :
    Subsingleton (G.H 1) := by
  unfold SubSystem.H at hF ⊢
  rw [Cech.subsingleton_H_one_iff] at hF ⊢
  have hdiv : ∀ I (z : G.sub I), σ⁻¹ * (z : Ω) ∈ F'.sub I := fun I z => by
    obtain ⟨y, hy, hzy⟩ := (hG I z).mp z.2
    rw [hzy, ← mul_assoc, inv_mul_cancel₀ hσ, one_mul]
    exact hy
  let φ : ∀ I, G.sub I →ₗ[S] F'.sub I := fun I =>
    { toFun := fun z => ⟨σ⁻¹ * z, hdiv I z⟩
      map_add' := fun a b => Subtype.ext (mul_add _ _ _)
      map_smul' := fun s a => Subtype.ext (by
        show σ⁻¹ * (s • (a : Ω)) = s • (σ⁻¹ * (a : Ω))
        rw [Algebra.smul_def, Algebra.smul_def]; ring) }
  let ψ : ∀ I, F'.sub I →ₗ[S] G.sub I := fun I =>
    { toFun := fun y => ⟨σ * y, (hG I _).mpr ⟨y, y.2, rfl⟩⟩
      map_add' := fun a b => Subtype.ext (mul_add _ _ _)
      map_smul' := fun s a => Subtype.ext (by
        show σ * (s • (a : Ω)) = s • (σ * (a : Ω))
        rw [Algebra.smul_def, Algebra.smul_def]; ring) }
  have hφ : ∀ I J h m, φ J (G.res I J h m) = F'.res I J h (φ I m) := fun _ _ _ _ => rfl
  have hψ : ∀ I J h m, ψ J (F'.res I J h m) = G.res I J h (ψ I m) := fun _ _ _ _ => rfl
  have hφd := Cech.mapC_d (R := S) (G := fun I => ↥(G.sub I)) (G' := fun I => ↥(F'.sub I)) φ hφ
  have hψd := Cech.mapC_d (R := S) (G := fun I => ↥(F'.sub I)) (G' := fun I => ↥(G.sub I)) ψ hψ
  intro z hz
  obtain ⟨w, hw⟩ := hF (Cech.mapC (R := S) (G := fun I => ↥(G.sub I)) (G' := fun I => ↥(F'.sub I)) φ 1 z) (by rw [← hφd, hz, map_zero])
  refine ⟨(Cech.mapC (R := S) (G := fun I => ↥(F'.sub I)) (G' := fun I => ↥(G.sub I)) ψ 0 w), ?_⟩
  rw [← hψd, hw]
  funext J
  apply Subtype.ext
  show σ * (σ⁻¹ * ((z J : G.sub J.1) : Ω)) = ((z J : G.sub J.1) : Ω)
  rw [← mul_assoc, mul_inv_cancel₀ hσ, one_mul]

end SubSystem

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

namespace SubSystem

theorem twist_sub_eq_mul_of_line (F Q : SubSystem S x Ω) (I : Chart x) :
    (F.twist Q).sub I = Q.sub I * F.sub I := by
  rw [Submodule.mul_eq_span_mul_set]
  change Submodule.span _ _ = _
  congr 1
  ext z
  constructor
  · rintro ⟨q, hq, y, hy, rfl⟩
    exact Set.mul_mem_mul hq hy
  · rintro ⟨q, hq, y, hy, rfl⟩
    exact ⟨q, hq, y, hy, rfl⟩

theorem twist_comm (F Q : SubSystem S x Ω) : F.twist Q = Q.twist F :=
  ext_sub fun I => by rw [twist_sub_eq_mul_of_line, twist_sub_eq_mul_of_line, mul_comm]

theorem twist_assoc (F P Q : SubSystem S x Ω) : (F.twist P).twist Q = F.twist (P.twist Q) :=
  ext_sub fun I => by simp only [twist_sub_eq_mul_of_line, mul_assoc]

theorem pow_sub (Q : SubSystem S x Ω) (n : ℕ) (I : Chart x) : (Q.pow n).sub I = Q.sub I ^ n := by
  induction n with
  | zero =>
    obtain ⟨i, hi⟩ := I.2.1
    change twistMod S x 0 I = _
    rw [twistMod_eq_span 0 I hi, zpow_zero, pow_zero, Submodule.one_eq_span]
  | succ n ih =>
    change ((Q.pow n).twist Q).sub I = _
    rw [twist_sub_eq_mul_of_line, ih, pow_succ']

end SubSystem

theorem twistSys_twist_eq_add (a b : ℤ) :
    (twistSys S x a).twist (twistSys S x b) = twistSys S x (a + b) := by
  refine SubSystem.ext_sub fun I => ?_
  obtain ⟨i, hi⟩ := I.2.1
  have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
  rw [SubSystem.twist_sub_eq_mul_of_line]
  change twistMod S x b I * twistMod S x a I = twistMod S x (a + b) I
  rw [twistMod_eq_span b I hi, twistMod_eq_span a I hi, twistMod_eq_span (a + b) I hi,
    Submodule.span_mul_span, Set.singleton_mul_singleton, ← zpow_add₀ hxi, add_comm b a]

theorem pow_twistSys (c : ℤ) (n : ℕ) : (twistSys S x c).pow n = twistSys S x (n * c) := by
  induction n with
  | zero =>
    show twistSys S x 0 = twistSys S x (((0 : ℕ) : ℤ) * c)
    rw [Nat.cast_zero, zero_mul]
  | succ n ih =>
    change ((twistSys S x c).pow n).twist (twistSys S x c) = _
    rw [ih, twistSys_twist_eq_add]
    congr 1
    push_cast
    ring

theorem twistMul_sub (M : SubSystem S x Ω) (p : ℕ) (m : ℤ) (I : Chart x) :
    (twistMul M p m).sub I = (twistSys S x m).sub I * M.sub I ^ p := by
  rw [twistMul, SubSystem.twist_sub_eq_mul_of_line, SubSystem.pow_sub]

theorem twistSys_sub_mul (a b : ℤ) (I : Chart x) :
    (twistSys S x a).sub I * (twistSys S x b).sub I = (twistSys S x (a + b)).sub I := by
  rw [← twistSys_twist_eq_add, SubSystem.twist_sub_eq_mul_of_line, mul_comm]

theorem twistSys_sub_pow (c : ℤ) (n : ℕ) (I : Chart x) :
    (twistSys S x c).sub I ^ n = (twistSys S x (n * c)).sub I := by
  rw [← SubSystem.pow_sub, pow_twistSys]

theorem twistMul_twistMul (M : SubSystem S x Ω) (q n : ℕ) (m a : ℤ) :
    twistMul (twistMul M q m) n a = twistMul M (n * q) (n * m + a) := by
  refine SubSystem.ext_sub fun I => ?_
  rw [twistMul_sub, twistMul_sub, twistMul_sub, mul_pow, twistSys_sub_pow, ← pow_mul,
    ← mul_assoc, twistSys_sub_mul, mul_comm q n, add_comm a]

theorem pow_twistMul (M : SubSystem S x Ω) (q j : ℕ) (m : ℤ) :
    (twistMul M q m).pow j = twistMul M (j * q) (j * m) := by
  have h := twistMul_twistMul M q j m 0
  rw [add_zero] at h
  rw [← h]
  exact (SubSystem.twist_twistSys_zero _).symm

namespace LineBundle

def tensorProd (P Q : LineBundle S x) : LineBundle S x where
  toSubSystem := P.toSubSystem.twist Q.toSubSystem
  mem_iff I J h y := by
    constructor
    · intro hy
      have hy' : y ∈ Submodule.span (chartRing S x J)
          {z | ∃ q ∈ Q.sub J, ∃ p ∈ P.sub J, z = q • p} := hy
      refine Submodule.span_induction (p := fun z _ => ∃ a : chartRing S x I,
        IsUnit (chartIncl h a) ∧ (a : Ω) • z ∈ (P.toSubSystem.twist Q.toSubSystem).sub I)
        ?_ ?_ ?_ ?_ hy'
      · rintro _ ⟨q, hq, p, hp, rfl⟩
        obtain ⟨a, ha, haq⟩ := (Q.mem_iff I J h q).mp hq
        obtain ⟨b, hb, hbp⟩ := (P.mem_iff I J h p).mp hp
        refine ⟨a * b, by rw [map_mul]; exact ha.mul hb, ?_⟩
        have : ((a * b : chartRing S x I) : Ω) • (q • p) = ((a : Ω) • q) • ((b : Ω) • p) := by
          simp only [smul_eq_mul, MulMemClass.coe_mul]; ring
        rw [this]
        exact Submodule.subset_span ⟨_, haq, _, hbp, rfl⟩
      · exact ⟨1, by simp, by simp⟩
      · rintro y₁ y₂ - - ⟨a₁, ha₁, h₁⟩ ⟨a₂, ha₂, h₂⟩
        refine ⟨a₁ * a₂, by rw [map_mul]; exact ha₁.mul ha₂, ?_⟩
        have : ((a₁ * a₂ : chartRing S x I) : Ω) • (y₁ + y₂) =
            a₂ • ((a₁ : Ω) • y₁) + a₁ • ((a₂ : Ω) • y₂) := by
          simp only [smul_eq_mul, chartRing_smul_def, MulMemClass.coe_mul]; ring
        rw [this]
        exact Submodule.add_mem _ (Submodule.smul_mem _ _ h₁) (Submodule.smul_mem _ _ h₂)
      · rintro c z - ⟨a, ha, hz⟩
        obtain ⟨a', ha', hc⟩ := exists_isUnit_mul_mem h c
        refine ⟨a' * a, by rw [map_mul]; exact ha'.mul ha, ?_⟩
        have : ((a' * a : chartRing S x I) : Ω) • (c • z) =
            (⟨_, hc⟩ : chartRing S x I) • ((a : Ω) • z) := by
          simp only [smul_eq_mul, chartRing_smul_def, MulMemClass.coe_mul]; ring
        rw [this]
        exact Submodule.smul_mem _ _ hz
    · rintro ⟨a, ⟨u, hu⟩, hay⟩
      have hJ := (P.toSubSystem.twist Q.toSubSystem).mono I J h _ hay
      have hinv : ((↑u⁻¹ : chartRing S x J) : Ω) * (a : Ω) = 1 := by
        have := congrArg Subtype.val (Units.inv_mul u)
        rw [hu] at this
        exact this
      have hy : y = (↑u⁻¹ : chartRing S x J) • ((a : Ω) • y) := by
        rw [chartRing_smul_def, smul_eq_mul, ← mul_assoc, hinv, one_mul]
      rw [hy]
      exact Submodule.smul_mem _ _ hJ
  fg I := by
    rw [SubSystem.twist_sub_eq_mul_of_line]
    exact (Q.fg I).mul (P.fg I)
  invertible I := by
    obtain ⟨P', hP⟩ := P.invertible I
    obtain ⟨Q', hQ⟩ := Q.invertible I
    refine ⟨P' * Q', ?_⟩
    rw [SubSystem.twist_sub_eq_mul_of_line,
      show Q.sub I * P.sub I * (P' * Q') = (P.sub I * P') * (Q.sub I * Q') by ring, hP, hQ, one_mul]

def powBundle (Q : LineBundle S x) : ℕ → LineBundle S x
  | 0 => twistBundle S x 0
  | n + 1 => (Q.powBundle n).tensorProd Q

theorem powBundle_toSubSystem (Q : LineBundle S x) (n : ℕ) :
    (Q.powBundle n).toSubSystem = Q.toSubSystem.pow n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (Q.powBundle n).toSubSystem.twist Q.toSubSystem = (Q.toSubSystem.pow n).twist Q.toSubSystem
    rw [ih]

end LineBundle

theorem exists_lineBundle_twistMul (M : LineBundle S x) (p : ℕ) (m : ℤ) :
    ∃ L : LineBundle S x, L.toSubSystem = twistMul M.toSubSystem p m :=
  ⟨(M.powBundle p).tensorProd (twistBundle S x m), by
    change (M.powBundle p).toSubSystem.twist (twistSys S x m) = _
    rw [LineBundle.powBundle_toSubSystem]
    rfl⟩

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u w

def CutComponent.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (n : ℕ) (pp : Ideal (Poly k N)) (L : LineBundle k x) (s : Ω), IsSubvar (x := x) pp (n + 1) →
    IsVeryAmple L.toSubSystem → s ∈ L.secs → (∃ I, s ∉ (L.twist (idealSys (x := x) pp)).sub I) →
    ∃ qq ∈ (pp ⊔ zeroIdeal L.toSubSystem s).minimalPrimes, IsSubvar (x := x) qq n

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

def CutDimLower.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (n : ℕ) (pp : Ideal (Poly k N)) (L : LineBundle k x) (s : Ω) (qq : Ideal (Poly k N)),
    IsSubvar x pp (n + 1) → s ∈ L.secs → qq ∈ (pp ⊔ zeroIdeal L.toSubSystem s).minimalPrimes →
    (∃ j, (X j : Poly k N) ∉ qq) → ((n + 1 : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (Poly k N ⧸ qq)

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u

def CutMultPos.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (N : ℕ) (J qq : Ideal (Poly S N))
    (h : qq ∈ J.minimalPrimes),
    haveI : qq.IsPrime := h.1.1
    0 < cutMult J qq ∧ cutMult J qq < ⊤

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

def CutNonempty.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (n : ℕ) (pp : Ideal (Poly k N)) (L : LineBundle k x) (s : Ω), IsSubvar x pp (n + 1) →
    IsVeryAmple L.toSubSystem → s ∈ L.secs → (∃ I, s ∉ (L.twist (idealSys x pp)).sub I) →
    ∃ qq ∈ (pp ⊔ zeroIdeal L.toSubSystem s).minimalPrimes, ∃ j, (X j : Poly k N) ∉ qq

end

end GroundTheory.Heights₂.Heights.Kleiman
end
