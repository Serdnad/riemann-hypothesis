module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtA
public import Formalism.LocalToGlobal.Columns.QthExistsBound
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.TwU.Approx
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem intAtA_of_val {ι : AfE F E ≃+* FiniteAdeleRing (𝓞 E) E} (hι : IsAdIso ι) (P : HeightOneSpectrum (𝓞 E))
    (z : AfE F E) (h : Valued.v (ι z P) ≤ 1) : IntAtA (F := F) P z := by
  classical
  set w := ι z with hw
  have hfin : Set.Finite {Q : HeightOneSpectrum (𝓞 E) | w Q ∉ Q.adicCompletionIntegers E} :=
    Filter.eventually_cofinite.1 w.2
  set T := hfin.toFinset with hT
  have hPT : P ∉ T := by
    rw [hT, Set.Finite.mem_toFinset]
    exact fun h' => h' ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 h)
  let e : HeightOneSpectrum (𝓞 E) → ℕ := fun Q => (WithZero.log (Valued.v (w Q))).toNat
  have hbound : ∀ Q ∈ T, ∀ s : 𝓞 E, s ∈ Q.asIdeal ^ e Q →
      Valued.v ((algebraMap E (Q.adicCompletion E) (algebraMap (𝓞 E) E s))) * Valued.v (w Q) ≤ 1 := by
    intro Q hQ s hs
    have hQ' : w Q ∉ Q.adicCompletionIntegers E := by rwa [hT, Set.Finite.mem_toFinset] at hQ
    have hne : Valued.v (w Q) ≠ 0 := by
      intro h0
      apply hQ'
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, h0]
      exact zero_le'
    have h1 : Valued.v ((algebraMap E (Q.adicCompletion E) (algebraMap (𝓞 E) E s))) ≤ WithZero.exp (-((e Q : ℕ) : ℤ)) := by
      show Valued.v (((algebraMap (𝓞 E) E s : E)) : Q.adicCompletion E) ≤ _
      rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_of_algebraMap]
      exact (HeightOneSpectrum.intValuation_le_pow_iff_mem _ _ _).2 hs
    have h2 : Valued.v (w Q) ≤ WithZero.exp ((e Q : ℕ) : ℤ) := by
      rw [← WithZero.exp_log hne, WithZero.exp_le_exp]
      exact Int.self_le_toNat _
    calc _ ≤ WithZero.exp (-((e Q : ℕ) : ℤ)) * WithZero.exp ((e Q : ℕ) : ℤ) := mul_le_mul' h1 h2
      _ = 1 := by rw [← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero]
  obtain ⟨s, hs⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := insert P T)
    (fun Q : HeightOneSpectrum (𝓞 E) => Q.asIdeal) (fun Q => if Q = P then 1 else e Q)
    (fun Q _ => Q.prime) (fun Q _ Q' _ hne h' => hne (HeightOneSpectrum.ext h'))
    (fun Q => if Q.1 = P then 1 else 0)
  have hsP : s ∉ P.asIdeal := by
    intro hm
    have h1 := hs P (Finset.mem_insert_self _ _)
    simp only [if_true, pow_one] at h1
    apply P.isPrime.ne_top
    rw [Ideal.eq_top_iff_one]
    have := P.asIdeal.sub_mem hm h1
    simpa using this
  have hsQ : ∀ Q ∈ T, s ∈ Q.asIdeal ^ e Q := by
    intro Q hQ
    have hQP : Q ≠ P := fun h' => hPT (h' ▸ hQ)
    have h1 := hs Q (Finset.mem_insert_of_mem hQ)
    simpa [hQP] using h1
  refine ⟨s, hsP, ?_⟩
  have hmem : iA F E (algebraMap (𝓞 E) E s) * z ∈ RInt F E := by
    refine (hι.2 _).2 fun Q => ?_
    have e1 : ι (iA F E (algebraMap (𝓞 E) E s) * z) Q =
        algebraMap E (Q.adicCompletion E) (algebraMap (𝓞 E) E s) * w Q := by
      rw [map_mul, show ι (iA F E (algebraMap (𝓞 E) E s)) = algebraMap E _ (algebraMap (𝓞 E) E s) from hι.1 _]
      rfl
    rw [e1, map_mul]
    by_cases hQ : Q ∈ T
    · exact hbound Q hQ s (hsQ Q hQ)
    · have hQ' : w Q ∈ Q.adicCompletionIntegers E := by
        by_contra hc
        exact hQ (by rw [hT, Set.Finite.mem_toFinset]; exact hc)
      rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hQ'
      have hs1 : Valued.v ((algebraMap E (Q.adicCompletion E) (algebraMap (𝓞 E) E s))) ≤ 1 := by
        show Valued.v (((algebraMap (𝓞 E) E s : E)) : Q.adicCompletion E) ≤ _
        rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_of_algebraMap]
        exact HeightOneSpectrum.intValuation_le_one _ _
      exact mul_le_one' hs1 hQ'
  exact hmem

def compAt (ι : AfE F E ≃+* FiniteAdeleRing (𝓞 E) E) (P : HeightOneSpectrum (𝓞 E)) : AfE F E →+* P.adicCompletion E where
  toFun a := ι a P
  map_one' := by rw [map_one]; rfl
  map_mul' a b := by rw [map_mul]; rfl
  map_zero' := by rw [map_zero]; rfl
  map_add' a b := by rw [map_add (f := _)]; rfl

theorem exists_nearAt (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (N n : ℕ)
    (P : HeightOneSpectrum (𝓞 E)) (y : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : ∃ g : GL (Fin N) E, NearAt P n y g := by
  classical
  obtain ⟨ι, hι⟩ := exists_isAdIso F E
  set Φ := compAt ι P with hΦ
  have hΦi : ∀ x : E, Φ (iA F E x) = algebraMap E (P.adicCompletion E) x := by
    intro x
    show (ι (iA F E x)) P = _
    rw [show ι (iA F E x) = algebraMap E _ x from hι.1 x]
    rfl
  set A : Matrix (Fin N) (Fin N) (P.adicCompletion E) := Φ.mapMatrix ((y⁻¹ : GL (Fin N) _) : Matrix (Fin N) (Fin N) _) with hA
  set B : Matrix (Fin N) (Fin N) (P.adicCompletion E) := Φ.mapMatrix ((y : GL (Fin N) _) : Matrix (Fin N) (Fin N) _) with hB
  have hAB : A * B = 1 := by
    rw [hA, hB, ← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one]
  set qq : P.adicCompletion E := algebraMap E _ ((((qOf P : ℕ) : E) ^ n)⁻¹) with hqq
  let S : Set (Matrix (Fin N) (Fin N) (P.adicCompletion E)) :=
    {G | G.det ≠ 0} ∩ ⋂ a : Fin N, ⋂ b : Fin N, {G | Valued.v (qq * (A * G - 1) a b) ≤ 1}
  have hSo : IsOpen S := by
    refine IsOpen.inter (isOpen_ne_fun (Continuous.matrix_det continuous_id) continuous_const) ?_
    refine isOpen_iInter_of_finite fun a => isOpen_iInter_of_finite fun b => ?_
    have hc : Continuous fun G : Matrix (Fin N) (Fin N) (P.adicCompletion E) => qq * (A * G - 1) a b := by
      refine continuous_const.mul ?_
      exact ((continuous_const.matrix_mul continuous_id).sub continuous_const).matrix_elem a b
    exact (Valued.isOpen_integer (P.adicCompletion E)).preimage hc
  have hBS : B ∈ S := by
    refine ⟨?_, Set.mem_iInter.2 fun a => Set.mem_iInter.2 fun b => ?_⟩
    · intro h0
      have := congrArg Matrix.det hAB
      rw [Matrix.det_mul, h0, mul_zero, Matrix.det_one] at this
      exact zero_ne_one this
    · show Valued.v (qq * (A * B - 1) a b) ≤ 1
      rw [hAB, sub_self]
      simp
  have hd : DenseRange fun g : Matrix (Fin N) (Fin N) E => g.map (algebraMap E (P.adicCompletion E)) :=
    DenseRange.piMap fun _ => DenseRange.piMap fun _ => HeightOneSpectrum.denseRange_algebraMap E P
  obtain ⟨g0, hg0⟩ := hd.exists_mem_open hSo ⟨B, hBS⟩
  obtain ⟨hdet, hcong⟩ := hg0
  have hdet0 : g0.det ≠ 0 := by
    intro h0
    apply hdet
    show (g0.map (algebraMap E (P.adicCompletion E))).det = 0
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero g0 hdet0, fun a b => ?_⟩
  refine intAtA_of_val hι P _ ?_
  have hc : Valued.v (qq * (A * g0.map (algebraMap E (P.adicCompletion E)) - 1) a b) ≤ 1 :=
    Set.mem_iInter.1 (Set.mem_iInter.1 hcong a) b
  refine Eq.trans_le ?_ hc
  congr 1
  show Φ _ = _
  rw [map_mul, hΦi]
  congr 1
  have e1 : ((y⁻¹ * ratA F (Matrix.GeneralLinearGroup.mkOfDetNeZero g0 hdet0) : GL (Fin N) _) : Matrix (Fin N) (Fin N) _) - 1 =
      ((y⁻¹ : GL (Fin N) _) : Matrix (Fin N) (Fin N) _) * g0.map (iA F E) - 1 := rfl
  rw [e1]
  have e2 : Φ (((((y⁻¹ : GL (Fin N) _) : Matrix (Fin N) (Fin N) (AfE F E)) * g0.map (iA F E) - 1 :
      Matrix (Fin N) (Fin N) (AfE F E))) a b) =
      Φ.mapMatrix (((y⁻¹ : GL (Fin N) _) : Matrix (Fin N) (Fin N) (AfE F E)) * g0.map (iA F E) - 1) a b := rfl
  have e3 : Φ.mapMatrix (g0.map (iA F E)) = g0.map (algebraMap E (P.adicCompletion E)) :=
    Matrix.ext fun i j => hΦi (g0 i j)
  rw [e2, map_sub, map_mul, map_one, e3]

end GlobalTheory.TwU.Approx
end
end

section

noncomputable section

namespace GlobalTheory.TwU.CongTwo

open NumberField IsDedekindDomain Matrix _root_.Formalism.L2.Col
open scoped TensorProduct

theorem val_cong_of_mul_eq {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) {ι : Type} [Fintype ι]
    [DecidableEq ι] {c : K} (hc0 : c ≠ 0) (hc : v c < 1) {A B H : Matrix ι ι K}
    (hA : ∀ i j, v (c⁻¹ * (A - 1) i j) ≤ 1) (hB : ∀ i j, v (c⁻¹ * (B - 1) i j) ≤ 1) (hAH : A * H = B) (i j : ι) :
    v (c⁻¹ * (H - 1) i j) ≤ 1 := by
  let S := v.integer
  let A0 : Matrix ι ι S := fun k l => ⟨c⁻¹ * (A - 1) k l, hA k l⟩
  let cS : S := ⟨c, hc.le⟩
  let AS : Matrix ι ι S := 1 + cS • A0
  have hAS : AS.map S.subtype = A := by
    ext k l
    show (((1 : Matrix ι ι S) k l : S) : K) + c * (c⁻¹ * (A - 1) k l) = A k l
    rw [← mul_assoc, mul_inv_cancel₀ hc0, one_mul, Matrix.sub_apply]
    by_cases h : k = l
    · subst h; simp
    · simp [Matrix.one_apply_ne h]
  have hdet : ∃ y : S, AS.det - 1 = y * cS := by
    let π := Ideal.Quotient.mk (Ideal.span {cS})
    have hπc : π cS = 0 := Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
    have hπ : π.mapMatrix AS = 1 := by
      ext k l
      simp only [AS, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add (f := _), map_mul, hπc,
        zero_mul, add_zero]
      rw [Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> simp
    have h1 : π AS.det = π 1 := by rw [RingHom.map_det, hπ, Matrix.det_one, map_one]
    exact Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 h1) |>.imp fun y hy => hy.symm
  obtain ⟨y, hy⟩ := hdet
  have hdA : A.det = (AS.det : K) := by
    rw [← hAS]
    exact (RingHom.map_det S.subtype AS).symm
  have hv1 : v A.det = 1 := by
    have e : A.det = 1 + (y : K) * c := by
      rw [hdA]
      have : ((AS.det - 1 : S) : K) = ((y * cS : S) : K) := congrArg Subtype.val hy
      push_cast at this
      linear_combination this
    rw [e]
    apply Valuation.map_one_add_of_lt
    rw [map_mul]
    calc v (y : K) * v c ≤ 1 * v c := mul_le_mul' y.2 le_rfl
      _ = v c := one_mul _
      _ < 1 := hc
  have hdet0 : A.det ≠ 0 := fun h => by rw [h, map_zero] at hv1; exact zero_ne_one hv1
  have hMA : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A (isUnit_iff_ne_zero.2 hdet0)
  have hH : H - 1 = A⁻¹ * (B - A) := by
    rw [Matrix.mul_sub, ← hAH, ← Matrix.mul_assoc, hMA, Matrix.one_mul]
  have hinv : ∀ k l, v ((A⁻¹) k l) ≤ 1 := by
    intro k l
    have hadj : A.adjugate = AS.adjugate.map S.subtype := by
      rw [← hAS]
      exact (RingHom.map_adjugate S.subtype AS).symm
    rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv', map_mul, map_inv₀, hv1, inv_one, one_mul,
      hadj, Matrix.map_apply]
    exact (AS.adjugate k l).2
  have e : c⁻¹ * (H - 1) i j = ∑ k, A⁻¹ i k * (c⁻¹ * (B - 1) k j - c⁻¹ * (A - 1) k j) := by
    rw [hH, Matrix.mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Matrix.sub_apply]
    ring
  rw [e]
  exact Subring.sum_mem S fun k _ => Subring.mul_mem S (hinv i k) (Subring.sub_mem S (hB k j) (hA k j))

end GlobalTheory.TwU.CongTwo

namespace GlobalTheory.TwU.CongTwo

open NumberField IsDedekindDomain Matrix _root_.Formalism.L2.Col
open Formalism.L2.DIV (AfE)
open scoped TensorProduct

theorem intAt_inv_mul_of_nearAt {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}
    (P : HeightOneSpectrum (𝓞 E)) (n : ℕ) (x : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (g₁ g₂ : GL (Fin N) E) :
    0 < n → NearAt P n x g₁ → NearAt P n x g₂ → ∀ a b : Fin N,
      IntAt P ((((qOf P : ℕ) : E) ^ n)⁻¹ * (((g₁⁻¹ * g₂ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) - 1) a b) := by
  intro hn h1 h2 a b
  obtain ⟨ι, hι⟩ := exists_isAdIso F E
  let φ : AfE F E →+* P.adicCompletion E :=
    { toFun := fun z => ι z P
      map_one' := by rw [map_one]; rfl
      map_mul' := fun x y => by rw [map_mul]; rfl
      map_zero' := by rw [map_zero]; rfl
      map_add' := fun x y => by rw [map_add (f := _)]; rfl }
  have hφ : ∀ e : E, φ (iA F E e) = algebraMap E (P.adicCompletion E) e := fun e => by
    show ι (iA F E e) P = _
    rw [show ι (iA F E e) = algebraMap E _ e from hι.1 e]; rfl
  have hq0 : ((qOf P : ℕ) : E) ≠ 0 := by
    have : qOf P ≠ 0 := fun h0 => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
    exact_mod_cast this
  have hqv : Valued.v (algebraMap E (P.adicCompletion E) ((qOf P : ℕ) : E)) < 1 := by
    show Valued.v (((((qOf P : ℕ) : E)) : P.adicCompletion E)) < 1
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', ← map_natCast (algebraMap (𝓞 E) E),
      HeightOneSpectrum.valuation_of_algebraMap]
    exact (HeightOneSpectrum.intValuation_lt_one_iff_mem _ _).2 (Ideal.absNorm_mem _)
  set c : P.adicCompletion E := algebraMap E (P.adicCompletion E) ((((qOf P : ℕ) : E)) ^ n) with hc
  have hc0 : c ≠ 0 := (map_ne_zero _).2 (pow_ne_zero _ hq0)
  have hcv : Valued.v c < 1 := by
    rw [hc, map_pow, map_pow]
    exact pow_lt_one' hqv (Nat.pos_iff_ne_zero.1 hn)
  have h1apply : ∀ k l : Fin N, φ ((1 : Matrix (Fin N) (Fin N) (AfE F E)) k l) = (1 : Matrix (Fin N) (Fin N) (P.adicCompletion E)) k l := by
    intro k l
    rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have htr : ∀ g : GL (Fin N) E, NearAt P n x g → ∀ k l,
      Valued.v (c⁻¹ * ((((x⁻¹ * ratA F g : GL (Fin N) (AfE F E)) : Matrix (Fin N) (Fin N) (AfE F E)).map φ) - 1) k l) ≤ 1 := by
    intro g hg k l
    have h := hι.val_le (hg k l)
    have e : ι (iA F E (((qOf P : ℕ) : E) ^ n)⁻¹ * (((x⁻¹ * ratA F g : GL (Fin N) (AfE F E)) : Matrix (Fin N) (Fin N) (AfE F E)) - 1) k l) P =
        c⁻¹ * ((((x⁻¹ * ratA F g : GL (Fin N) (AfE F E)) : Matrix (Fin N) (Fin N) (AfE F E)).map φ) - 1) k l := by
      show φ _ = _
      rw [map_mul, hφ, map_inv₀, Matrix.sub_apply, Matrix.sub_apply, map_sub, h1apply, Matrix.map_apply]
    rw [e] at h
    exact h
  have hrat : ∀ g : GL (Fin N) E, ((ratA F g : GL (Fin N) (AfE F E)) : Matrix (Fin N) (Fin N) (AfE F E)).map φ =
      (g : Matrix (Fin N) (Fin N) E).map (algebraMap E (P.adicCompletion E)) := by
    intro g
    exact Matrix.ext fun k l => hφ _
  have hmul : (((x⁻¹ * ratA F g₁ : GL (Fin N) (AfE F E)) : Matrix (Fin N) (Fin N) (AfE F E)).map φ) *
      ((g₁⁻¹ * g₂ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E).map (algebraMap E (P.adicCompletion E)) =
      (((x⁻¹ * ratA F g₂ : GL (Fin N) (AfE F E)) : Matrix (Fin N) (Fin N) (AfE F E)).map φ) := by
    rw [← hrat, ← Matrix.map_mul, ← Units.val_mul]
    congr 2
    rw [map_mul, map_inv]
    group
  have key := val_cong_of_mul_eq Valued.v hc0 hcv (htr g₁ h1) (htr g₂ h2) hmul a b
  have e2 : c⁻¹ * (((g₁⁻¹ * g₂ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E).map (algebraMap E (P.adicCompletion E)) - 1) a b =
      algebraMap E (P.adicCompletion E) ((((qOf P : ℕ) : E) ^ n)⁻¹ * (((g₁⁻¹ * g₂ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) - 1) a b) := by
    rw [map_mul, map_inv₀, Matrix.sub_apply, Matrix.sub_apply, map_sub, Matrix.map_apply]
    congr 2
    rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  rw [e2] at key
  letI : StarRing E := starRingOfComm
  rw [qth_intAt_iff]
  rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  exact key

end GlobalTheory.TwU.CongTwo
end
end

section

noncomputable section

namespace GlobalTheory.TwU

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG _root_.Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat
open Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Apx

variable {D : D7} {X : Fields} (s : Seam D X)

def apxAt {N : ℕ} (P : HeightOneSpectrum (𝓞 X.E)) (n : ℕ)
    (k : GL (Fin N) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) : Sp X.E N ≃ₗ[X.E] Sp X.E N :=
  Classical.epsilon fun g : Sp X.E N ≃ₗ[X.E] Sp X.E N => NearAt (seamP s P) n k (seamGL s g)

def seamVec (n : ℕ) :
    Sp X.E n →ₛₗ[(RingOfIntegers.mapRingEquiv s.iE : 𝓞 X.E →+* 𝓞 D.host.E)] (Fin n → D.host.E) where
  toFun x l := s.iE (x l)
  map_add' x y := by
    funext l
    simp
  map_smul' r x := by
    funext l
    simp only [Pi.smul_apply, Algebra.smul_def, map_mul]
    rfl

def latBack {n : ℕ} (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) : Submodule (𝓞 X.E) (Sp X.E n) :=
  L.comap (seamVec s n)

theorem mem_latBack {n : ℕ} (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (y : Sp X.E n) :
    y ∈ latBack s L ↔ (fun l => s.iE (y l)) ∈ L := Iff.rfl

end Apx

section Ad

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Y : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl Kc Y cX} {t : KerEntTied ex} {u : D.what₂.Word} {μ : D.what₂.Tup} {St : ChainCharts D u μ}
  (A : AdData t u μ St) (a : 𝓞 D.host.E)

def latAdX (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch)
    (x : GL (Fin (D.R.N i)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) : Submodule (𝓞 t.X.E) (Sp t.X.E (D.R.N i)) :=
  latBack t.seam (latCo D.sp (gramN D i hi) (A.crd i hi) a x ((St i hi).K β).lev.Lb)




end Ad

end GlobalTheory.TwU

end
end

section

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker GlobalTheory.TwU

noncomputable section

namespace GlobalTheory.SeamCong

theorem qOf_seamP {D : D7} {X : Fields} (s : Seam D X) (P : HeightOneSpectrum (𝓞 X.E)) : qOf (seamP s P) = qOf P := by
  have hI : (seamP s P).asIdeal = P.asIdeal.map (RingOfIntegers.mapRingEquiv s.iE) := by
    ext y
    rw [← (RingOfIntegers.mapRingEquiv s.iE).apply_symm_apply y, mem_seamP, Ideal.mem_map_of_equiv]
    constructor
    · intro hy; exact ⟨_, hy, rfl⟩
    · rintro ⟨z, hz, e⟩
      rw [(RingOfIntegers.mapRingEquiv s.iE).injective e] at hz
      exact hz
  unfold qOf
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact (Nat.card_congr (Ideal.quotientEquiv P.asIdeal (seamP s P).asIdeal (RingOfIntegers.mapRingEquiv s.iE) hI).toEquiv).symm

theorem intAt_seamP_iff {D : D7} {X : Fields} (s : Seam D X) (P : HeightOneSpectrum (𝓞 X.E)) (e : X.E) :
    IntAt (seamP s P) (s.iE e) ↔ IntAt P e := by
  have hc : ∀ y : 𝓞 X.E, algebraMap (𝓞 D.host.E) D.host.E (RingOfIntegers.mapRingEquiv s.iE y) = s.iE (algebraMap (𝓞 X.E) X.E y) :=
    fun y => rfl
  constructor
  · rintro ⟨r, c, hc', h⟩
    refine ⟨(RingOfIntegers.mapRingEquiv s.iE).symm r, (RingOfIntegers.mapRingEquiv s.iE).symm c, ?_, ?_⟩
    · rw [← mem_seamP s, RingEquiv.apply_symm_apply]; exact hc'
    · apply s.iE.injective
      rw [map_mul, ← hc, ← hc, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
      exact h
  · rintro ⟨r, c, hc', h⟩
    refine ⟨RingOfIntegers.mapRingEquiv s.iE r, RingOfIntegers.mapRingEquiv s.iE c, ?_, ?_⟩
    · rw [mem_seamP s]; exact hc'
    · rw [hc, hc, ← map_mul, h]

theorem cong_seam {D : D7} {X : Fields} (s : Seam D X) {N : ℕ} (P : HeightOneSpectrum (𝓞 X.E)) (n : ℕ)
    (g : Sp X.E N ≃ₗ[X.E] Sp X.E N)
    (h : ∀ a b, IntAt (seamP s P) ((((qOf (seamP s P) : ℕ) : D.host.E) ^ n)⁻¹ *
      (((seamGL s g : GL (Fin N) D.host.E) : Matrix (Fin N) (Fin N) D.host.E) - 1) a b)) :
    ∀ s' l, IntAt P (((qOf P : X.E) ^ n)⁻¹ * (g (Pi.single s' (1 : X.E)) l - (Pi.single s' (1 : X.E) : Sp X.E N) l)) := by
  intro s' l
  have h1 := h l s'
  have hM : ((seamGL s g : GL (Fin N) D.host.E) : Matrix (Fin N) (Fin N) D.host.E) =
      (LinearMap.toMatrix' g.toLinearMap).map (s.iE : X.E →+* D.host.E) := rfl
  rw [← intAt_seamP_iff s P]
  have e : s.iE (((qOf P : X.E) ^ n)⁻¹ * (g (Pi.single s' (1 : X.E)) l - (Pi.single s' (1 : X.E) : Sp X.E N) l)) =
      (((qOf (seamP s P) : ℕ) : D.host.E) ^ n)⁻¹ *
      (((seamGL s g : GL (Fin N) D.host.E) : Matrix (Fin N) (Fin N) D.host.E) - 1) l s' := by
    rw [hM, qOf_seamP, Matrix.sub_apply, Matrix.map_apply, LinearMap.toMatrix'_apply, map_mul, map_inv₀, map_pow,
      map_natCast, map_sub, Matrix.one_apply, Pi.single_apply]
    split_ifs <;> simp
  rw [e]
  exact h1

end GlobalTheory.SeamCong
end
end

section

noncomputable section

namespace GlobalTheory.TwU

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG _root_.Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat
open Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G
open scoped TensorProduct

section Seam

variable {D : D7} {X : Fields} (s : Seam D X)

def seamLE {n : ℕ} (g : GL (Fin n) D.host.E) : Sp X.E n ≃ₗ[X.E] Sp X.E n :=
  LinearMap.GeneralLinearGroup.generalLinearEquiv X.E (Fin n → X.E)
    (Matrix.GeneralLinearGroup.toLin (bc (s.iE.symm : D.host.E →+* X.E) g))

theorem seamGL_seamLE {n : ℕ} (g : GL (Fin n) D.host.E) : seamGL s (seamLE s g) = g := by
  ext a b
  simp [seamGL, seamLE, bc]

end Seam

end GlobalTheory.TwU

end
end
