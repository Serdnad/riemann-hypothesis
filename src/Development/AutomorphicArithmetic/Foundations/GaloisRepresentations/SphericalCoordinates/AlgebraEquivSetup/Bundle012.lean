module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.Bundle004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1202
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle151
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
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Tactic.TypeStar
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.MapWopWmap

@[expose] public section

section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open GlobalTheory.SplitPts (conjE)
open GroundTheory.Global.AdeleBaseChange (finiteAdeleMap)
open scoped TensorProduct

theorem UpperTheory.Gal.W2.Seed.pAdTEx :
    AdQEx → AdTensor → IdemP → AdTEx := by
  intro hQ hT hI p _ E _ _ _
  obtain ⟨Q⟩ := hQ p
  obtain ⟨ι, h1, h2, h3⟩ := hT E
  obtain ⟨e, he, he'⟩ := hI p E
  let M : AfQ ⊗[ℚ] E →ₐ[ℚ] AfP p ⊗[ℚ] E :=
    Algebra.TensorProduct.map Q.ρ.toRatAlgHom (AlgHom.id ℚ E)
  have hM : ∀ (a : AfQ) (x : E), M (a ⊗ₜ x) = Q.ρ a ⊗ₜ x := fun a x => rfl
  have hρe : Q.ρ e = 0 := (Q.ker e).2 fun v hv => (he v).2 hv
  have hιa : ∀ a : AfQ, ι (a ⊗ₜ 1) = finiteAdeleMap ℚ E a := fun a => by
    rw [h1, map_one, mul_one]
  have hιE : ∀ x : E, ι (1 ⊗ₜ x) = algebraMap E (Af E) x := fun x => by
    rw [h1, map_one, one_mul]

  have hMker : ∀ y, M y = 0 → (e ⊗ₜ[ℚ] (1 : E)) * y = y := by
    intro y hy
    let b := Module.finBasis ℚ E
    obtain ⟨c, rfl⟩ := TensorProduct.eq_repr_basis_right b y
    have hc0 : (c.mapRange Q.ρ (map_zero _)).sum (fun i m => m ⊗ₜ[ℚ] b i) = 0 := by
      rw [Finsupp.sum_mapRange_index (by simp)]

      rw [← hy, Finsupp.sum, Finsupp.sum, map_sum]
      rfl
    have hc := TensorProduct.sum_tmul_basis_right_eq_zero b _ hc0
    have hci : ∀ i, e * c i = c i := by
      intro i
      have hi : Q.ρ (c i) = 0 := by
        have := DFunLike.congr_fun hc i
        simpa using this
      have hv := (Q.ker (c i)).1 hi
      refine Subtype.ext (funext fun v => ?_)
      by_cases hp : (p : 𝓞 ℚ) ∈ v.asIdeal
      · show e v * c i v = c i v
        rw [(he v).1 hp, one_mul]
      · show e v * c i v = c i v
        rw [hv v hp, mul_zero]
    rw [Finsupp.sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, hci]

  have hιe : ι (e ⊗ₜ 1) = finiteAdeleMap ℚ E e := hιa e
  have hMe : M (e ⊗ₜ 1) = 0 := by rw [hM, hρe, TensorProduct.zero_tmul]
  have hMker' : ∀ x : Af E, M (ι.symm x) = 0 ↔
      ∀ w : Plc E, (p : 𝓞 E) ∉ w.asIdeal → pLoc E w x = 0 := by
    intro x
    constructor
    · intro h w hw
      have h' := congrArg ι (hMker _ h)
      rw [map_mul, hιe, ι.apply_symm_apply] at h'
      rw [← h', map_mul, (he' w).2 hw, zero_mul]
    · intro h
      have hx : finiteAdeleMap ℚ E e * x = x := by
        refine GlobalTheory.EulerTw.pLoc_ext E fun w => ?_
        by_cases hp : (p : 𝓞 E) ∈ w.asIdeal
        · rw [map_mul, (he' w).1 hp, one_mul]
        · rw [map_mul, (he' w).2 hp, zero_mul, h w hp]
      rw [← hx, ← hιe, map_mul ι.symm, ι.symm_apply_apply, map_mul, hMe, zero_mul]
  have hgen : ∀ (a : AfP p) (c : 𝓞 E), IsIntAf a →
      ∃ y ∈ AddSubgroup.closure {y : AfQ ⊗[ℚ] E | ∃ (a : AfQ) (x : 𝓞 E),
        (∀ v : Plc ℚ, Valued.v (a v) ≤ 1) ∧ y = a ⊗ₜ (x : E)}, M y = a ⊗ₜ (c : E) := by
    intro a c ha
    obtain ⟨b, rfl⟩ := Q.surj a
    have hb := (Q.int b).1 ha
    refine ⟨((1 - e) * b) ⊗ₜ (c : E), AddSubgroup.subset_closure ⟨_, c, ?_, rfl⟩, ?_⟩
    · intro v
      by_cases hp : (p : 𝓞 ℚ) ∈ v.asIdeal
      · have : ((1 - e) * b) v = (1 - e v) * b v := rfl
        rw [this, (he v).1 hp, sub_self, zero_mul, map_zero]
        exact zero_le
      · have : ((1 - e) * b) v = (1 - e v) * b v := rfl
        rw [this, (he v).2 hp, sub_zero, one_mul]
        exact hb v hp
    · rw [hM, map_mul, map_sub, map_one, hρe, sub_zero, one_mul]
  have hMs : Function.Surjective M := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul a x =>
      obtain ⟨b, rfl⟩ := Q.surj a
      exact ⟨b ⊗ₜ x, rfl⟩
    | add u v hu hv =>
      obtain ⟨u', rfl⟩ := hu
      obtain ⟨v', rfl⟩ := hv
      exact ⟨u' + v', map_add _ _ _⟩
  have hO : ∀ z ∈ OHat p E, ∃ y ∈ AddSubgroup.closure {y : AfQ ⊗[ℚ] E | ∃ (a : AfQ) (x : 𝓞 E),
      (∀ v : Plc ℚ, Valued.v (a v) ≤ 1) ∧ y = a ⊗ₜ (x : E)}, M y = z := by
    intro z hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, c, ha, rfl⟩ := hz
      exact hgen a c ha
    | zero => exact ⟨0, zero_mem _, map_zero _⟩
    | add u v _ _ hu hv =>
      obtain ⟨u', hu', rfl⟩ := hu
      obtain ⟨v', hv', rfl⟩ := hv
      exact ⟨u' + v', add_mem hu' hv', map_add _ _ _⟩
    | neg u _ hu =>
      obtain ⟨u', hu', rfl⟩ := hu
      exact ⟨-u', neg_mem hu', map_neg _ _⟩
  have hC : ∀ y ∈ AddSubgroup.closure {y : AfQ ⊗[ℚ] E | ∃ (a : AfQ) (x : 𝓞 E),
      (∀ v : Plc ℚ, Valued.v (a v) ≤ 1) ∧ y = a ⊗ₜ (x : E)}, M y ∈ OHat p E := by
    intro y hy
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, c, ha, rfl⟩ := hy
      exact AddSubgroup.subset_closure ⟨Q.ρ a, c, (Q.int a).2 fun v _ => ha v, rfl⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add u v _ _ hu hv => rw [map_add]; exact add_mem hu hv
    | neg u _ hu => rw [map_neg]; exact neg_mem hu
  exact ⟨{ toAdQ := Q
           Φ := (M : AfQ ⊗[ℚ] E →+* AfP p ⊗[ℚ] E).comp (ι.symm : Af E →+* AfQ ⊗[ℚ] E)
           Φ_E := fun x => by
            show M (ι.symm _) = _
            rw [← hιE, ι.symm_apply_apply, hM, map_one]
           Φ_Q := fun a => by
            show M (ι.symm _) = _
            rw [← hιa, ι.symm_apply_apply, hM]
           Φ_surj := fun z => by
            obtain ⟨y, rfl⟩ := hMs z
            refine ⟨ι y, ?_⟩
            show M (ι.symm (ι y)) = _
            rw [ι.symm_apply_apply]
           Φ_ker := hMker'
           Φ_int := fun x => by
            show M (ι.symm x) ∈ OHat p E ↔ _
            constructor
            · intro hx w hw
              obtain ⟨y, hy, hyz⟩ := hO _ hx
              have hd : M (ι.symm (x - ι y)) = 0 := by
                rw [map_sub, map_sub, ι.symm_apply_apply, hyz, sub_self]
              have h0 := (hMker' _).1 hd w hw
              rw [map_sub, sub_eq_zero] at h0
              rw [h0]
              exact (h2 y).1 hy w
            · intro hx
              have hz : M (ι.symm (finiteAdeleMap ℚ E e * x)) = 0 := by
                rw [← hιe, map_mul ι.symm, ι.symm_apply_apply, map_mul, hMe, zero_mul]
              have hi : ι.symm (x - finiteAdeleMap ℚ E e * x) ∈ AddSubgroup.closure
                  {y : AfQ ⊗[ℚ] E | ∃ (a : AfQ) (x : 𝓞 E),
                    (∀ v : Plc ℚ, Valued.v (a v) ≤ 1) ∧ y = a ⊗ₜ (x : E)} := by
                refine (h2 _).2 fun w => ?_
                rw [ι.apply_symm_apply, map_sub, map_mul]
                by_cases hp : (p : 𝓞 E) ∈ w.asIdeal
                · rw [(he' w).1 hp, one_mul, sub_self, map_zero]
                  exact zero_le
                · rw [(he' w).2 hp, zero_mul, sub_zero]
                  exact hx w hp
              have := hC _ hi
              rwa [map_sub, map_sub, hz, sub_zero] at this
           Φ_conj := fun x => by
            show M (ι.symm (conjFin (conjE E) x)) = conjT E (AfP p) (M (ι.symm x))
            obtain ⟨y, rfl⟩ := ι.surjective x
            rw [ι.symm_apply_apply]
            induction y using TensorProduct.inductionOn with
            | tmul a z =>
              rw [h1, map_mul, h3, conjFin_algebraMap, ← h1, ι.symm_apply_apply, hM, hM, conjT_tmul]
              rfl
            | add u v hu hv =>
              simp only [map_add (f := _), hu, hv] }⟩
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open GroundTheory.Global.AdeleBaseChange (finiteAdeleMap below)
open scoped TensorProduct

namespace UpperTheory.Gal.W2.Seed

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

private theorem exists_over (v : Plc ℚ) : ∃ w : Plc E, below ℚ w = v := by
  haveI := v.isMaximal
  obtain ⟨Q, hQm, hQo⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) v.asIdeal
  exact ⟨⟨Q, hQm.isPrime, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩, HeightOneSpectrum.ext hQo.over.symm⟩

private theorem fam_inj : Function.Injective (finiteAdeleMap ℚ E) := by
  intro x y h
  refine FiniteAdeleRing.ext (K := ℚ) fun v => ?_
  obtain ⟨w, rfl⟩ := exists_over (E := E) v
  have h1 := congrArg (fun z : FiniteAdeleRing (𝓞 E) E => z w) h
  exact (GroundTheory.Global.SemiLocal.completionMap (below ℚ w) w).injective h1

variable {n : ℕ}

private theorem mat_eq_of_comp {g g' : GUf E n} (h : ∀ w, comp w g = comp w g') : mat g = mat g' := by
  refine Units.ext (Matrix.ext fun i k => GlobalTheory.EulerTw.pLoc_ext E fun w => ?_)
  exact congrArg (fun x : GL (Fin n) (w.adicCompletion E) => x.val i k) (h w)

private theorem sim_eq_of_mat (hn : 1 ≤ n) {g g' : GUf E n} (h : mat g = mat g') : sim g = sim g' := by
  have h1 := UpperTheory.Gal.CertificateRingHomMap.mem_Sim.1 g.2
  have h2 := UpperTheory.Gal.CertificateRingHomMap.mem_Sim.1 g'.2
  have h3 : (g : GL (Fin n) (Af E) × AfQˣ).1 = (g' : GL (Fin n) (Af E) × AfQˣ).1 := h
  rw [h3, h2] at h1
  have h4 := congrFun (congrFun h1 ⟨0, hn⟩) ⟨0, hn⟩
  simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h4
  exact Units.ext (fam_inj h4.symm)

private theorem eq_of_comp (hn : 1 ≤ n) {g g' : GUf E n} (h : ∀ w, comp w g = comp w g') : g = g' :=
  Subtype.ext (Prod.ext (mat_eq_of_comp h) (sim_eq_of_mat hn (mat_eq_of_comp h)))

private theorem map_eq_iff {p : ℕ} [Fact p.Prime] (T : AdT p E) (x y : GL (Fin n) (Af E)) :
    x.val.map T.Φ = y.val.map T.Φ ↔ ∀ w : Plc E, (p : 𝓞 E) ∉ w.asIdeal →
      GeneralLinearGroup.map (pLoc E w) x = GeneralLinearGroup.map (pLoc E w) y := by
  constructor
  · intro h w hw
    refine Units.ext (Matrix.ext fun i k => ?_)
    have h1 : T.Φ (x.val i k - y.val i k) = 0 := by
      rw [map_sub]
      exact sub_eq_zero.2 (congrFun (congrFun h i) k)
    have h2 := (T.Φ_ker _).1 h1 w hw
    rw [map_sub] at h2
    exact sub_eq_zero.1 h2
  · intro h
    refine Matrix.ext fun i k => ?_
    have h1 : T.Φ (x.val i k - y.val i k) = 0 := by
      refine (T.Φ_ker _).2 fun w hw => ?_
      rw [map_sub]
      exact sub_eq_zero.2 (congrArg (fun z : GL (Fin n) (w.adicCompletion E) => z.val i k) (h w hw))
    rw [map_sub] at h1
    exact sub_eq_zero.1 h1

private theorem conj_comp_iff (a : GL (Fin n) (Af E)) (w : Plc E) (g g' : GUf E n) :
    GeneralLinearGroup.map (pLoc E w) (a * mat g * a⁻¹) = GeneralLinearGroup.map (pLoc E w) (a * mat g' * a⁻¹) ↔
      comp w g = comp w g' := by
  have e : ∀ h : GUf E n, GeneralLinearGroup.map (pLoc E w) (a * mat h * a⁻¹) =
      GeneralLinearGroup.map (pLoc E w) a * comp w h * (GeneralLinearGroup.map (pLoc E w) a)⁻¹ := fun h => by
    rw [map_mul, map_mul, map_inv]; rfl
  rw [e, e, mul_left_inj, mul_right_inj]

private theorem algMap_inj {p : ℕ} [Fact p.Prime] (hn : 1 ≤ n)
    (μ : AfP p ⊗[ℚ] Matrix (Fin n) (Fin n) E ≃+* Matrix (Fin n) (Fin n) (AfP p ⊗[ℚ] E)) (hμ : IsMu μ)
    {c c' : AfP p} (h : c ⊗ₜ[ℚ] (1 : Matrix (Fin n) (Fin n) E) = c' ⊗ₜ[ℚ] (1 : Matrix (Fin n) (Fin n) E)) : c = c' := by
  have h1 := congrFun (congrFun (congrArg μ h) ⟨0, hn⟩) ⟨0, hn⟩
  rw [hμ, hμ, Matrix.one_apply_eq] at h1
  exact Algebra.TensorProduct.includeLeft_injective (R := ℚ) (S := ℚ) (A := AfP p) (B := E)
    (algebraMap ℚ E).injective h1

end UpperTheory.Gal.W2.Seed

theorem UpperTheory.Gal.W2.Seed.pJEq :
    JEq := by
  intro E _ _ _ A n p _ S T μ hμ a j hj
  refine ⟨fun g g' h => eq_of_comp S.facts.pos h, fun g g' => ?_⟩
  have key : S.mx (j g) = S.mx (j g') ↔ ∀ w : Plc E, (p : 𝓞 E) ∉ w.asIdeal → comp w g = comp w g' := by
    rw [← μ.injective.eq_iff, hj, hj, map_eq_iff]
    exact forall₂_congr fun w _ => conj_comp_iff a w g g'
  rw [← key]
  refine ⟨fun h => congrArg S.mx h, fun h => ?_⟩
  have h1 : (((j g : S.G.GAf) : (AfP p ⊗[ℚ] S.G.C)ˣ × (AfP p)ˣ).1) = ((j g' : S.G.GAf) : (AfP p ⊗[ℚ] S.G.C)ˣ × (AfP p)ˣ).1 := Units.ext h
  refine Subtype.ext (Prod.ext h1 (Units.ext ?_))
  have e1 := mem_uGroup.1 (j g).2
  have e2 := mem_uGroup.1 (j g').2
  rw [h1, e2] at e1
  exact algMap_inj S.facts.pos μ hμ e1.symm
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open scoped TensorProduct

open Rat.HeightOneSpectrum GlobalTheory.NormLevelCompare in
private theorem away_iff (p : ℕ) [hp : Fact p.Prime] (w : HeightOneSpectrum ℤ) :
    w.asIdeal ≠ Ideal.span {(p : ℤ)} ↔ (p : 𝓞 ℚ) ∉ (primeCorr w).asIdeal := by
  have mem : ∀ {R : Type} [CommRing R] [Algebra R ℚ] [IsIntegralClosure R ℤ ℚ]
      (v : HeightOneSpectrum R) (n : ℕ), (n : R) ∈ v.asIdeal ↔ natGenerator v ∣ n := by
    intro R _ _ _ v n
    rw [natGenerator_dvd_iff, ← map_natCast (Rat.IsIntegralClosure.intEquiv R) n,
      Ideal.apply_mem_of_equiv_iff]
  have key : primesEquiv (primeCorr w) = primesEquiv w := by
    change primesEquiv (primesEquiv.symm (primesEquiv w)) = _
    exact Equiv.apply_symm_apply _ _
  have hg : natGenerator (primeCorr w) = natGenerator w := congrArg Subtype.val key
  rw [mem, hg, ← mem (R := ℤ)]
  refine not_congr ⟨fun h ↦ h ▸ Ideal.mem_span_singleton_self _, fun h ↦ ?_⟩
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp.out).irreducible
  exact (hmax.eq_of_le w.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).2 h)).symm

private theorem ringEquiv_of_algEquiv {K A B : Type*} [CommSemiring K] [Semiring A] [Semiring B]
    {_ : Algebra K A} {_ : Algebra K B} (e : A ≃ₐ[K] B) : ∃ f : A ≃+* B, ∀ x, f x = e x := ⟨e.toRingEquiv, fun _ ↦ rfl⟩

open GlobalTheory.NormLevelCompare in
private theorem exists_local_ring (w : HeightOneSpectrum ℤ) :
    ∃ e : (primeCorr w).adicCompletion ℚ ≃+* w.adicCompletion ℚ,
      ∀ x, e x ∈ w.adicCompletionIntegers ℚ ↔ x ∈ (primeCorr w).adicCompletionIntegers ℚ := by
  obtain ⟨e, he⟩ := exists_local w
  obtain ⟨f, hf⟩ := ringEquiv_of_algEquiv e
  exact ⟨f, fun x ↦ by rw [hf]; exact he x⟩

open GlobalTheory.NormLevelCompare in
private noncomputable def eL (w : HeightOneSpectrum ℤ) :
    (primeCorr w).adicCompletion ℚ ≃+* w.adicCompletion ℚ :=
  Classical.choose (exists_local_ring w)

open GlobalTheory.NormLevelCompare in
private theorem eL_mem (w : HeightOneSpectrum ℤ) (x : (primeCorr w).adicCompletion ℚ) :
    eL w x ∈ w.adicCompletionIntegers ℚ ↔ x ∈ (primeCorr w).adicCompletionIntegers ℚ := Classical.choose_spec (exists_local_ring w) x

open GlobalTheory.NormLevelCompare in
private theorem eL_mapsTo (w : HeightOneSpectrum ℤ) :
    Set.MapsTo (eL w).toRingHom ((primeCorr w).adicCompletionIntegers ℚ) (w.adicCompletionIntegers ℚ) := fun x hx ↦ (eL_mem w x).2 hx

private theorem finiteAdeleRingAway_ext {p : ℕ} {x y : AfP p} (h : ∀ v, AfP.eval v x = AfP.eval v y) : x = y := RestrictedProduct.ext _ _ h

open GlobalTheory.NormLevelCompare in
private noncomputable def rho (p : ℕ) : AfQ →+* AfP p :=
  RestrictedProduct.mapAlongRingHom (fun u : HeightOneSpectrum (𝓞 ℚ) ↦ u.adicCompletion ℚ)
    (fun v : AwayP p ↦ v.1.adicCompletion ℚ)
    (B₁ := fun u ↦ u.adicCompletionIntegers ℚ) (B₂ := fun v ↦ v.1.adicCompletionIntegers ℚ)
    (fun v ↦ primeCorr v.1) (primeCorr.injective.comp Subtype.val_injective).tendsto_cofinite
    (fun v ↦ (eL v.1).toRingHom) (hφ := .of_forall fun v ↦ eL_mapsTo v.1)

open GlobalTheory.NormLevelCompare in
private theorem eval_rho {p : ℕ} (a : AfQ) (v : AwayP p) :
    AfP.eval v (rho p a) = eL v.1 (a (primeCorr v.1)) := rfl

section
open GlobalTheory.NormLevelCompare
open scoped Classical in
private noncomputable def gL {p : ℕ} (b : AfP p) (w : HeightOneSpectrum ℤ) :
    (primeCorr w).adicCompletion ℚ :=
  if h : w.asIdeal ≠ Ideal.span {(p : ℤ)} then (eL w).symm (AfP.eval (⟨w, h⟩ : AwayP p) b) else 0

private theorem gL_pos {p : ℕ} (b : AfP p) (v : AwayP p) : gL b v.1 = (eL v.1).symm (AfP.eval v b) := by
  unfold gL
  rw [dite_eq_left v.2]
  rfl

private theorem gL_neg {p : ℕ} (b : AfP p) (w : HeightOneSpectrum ℤ)
    (h : ¬ w.asIdeal ≠ Ideal.span {(p : ℤ)}) : gL b w = 0 := by
  unfold gL
  rw [dite_eq_right h]

private theorem afP_ev {p : ℕ} (b : AfP p) :
    ∀ᶠ v : AwayP p in Filter.cofinite, AfP.eval v b ∈ v.1.adicCompletionIntegers ℚ := b.2

private theorem gL_ev {p : ℕ} (b : AfP p) : ∀ᶠ w : HeightOneSpectrum ℤ in Filter.cofinite,
    gL b w ∈ (primeCorr w).adicCompletionIntegers ℚ := by
  have hb := afP_ev b
  rw [Filter.eventually_cofinite] at hb ⊢
  refine (hb.image Subtype.val).subset ?_
  intro w hw
  by_cases h : w.asIdeal ≠ Ideal.span {(p : ℤ)}
  · refine ⟨⟨w, h⟩, ?_, rfl⟩
    intro hv
    apply hw
    rw [show gL b w = _ from gL_pos b ⟨w, h⟩]
    exact (eL_mem w _).1 (by simpa using hv)
  · exact absurd (by rw [gL_neg b w h]; exact zero_mem _) hw

private theorem exists_pi_extend {α β : Type*} (P : β → Type*) (σ : α ≃ β) (g : ∀ a, P (σ a)) :
    ∃ f : ∀ b, P b, ∀ a, f (σ a) = g a := ⟨Equiv.piCongrLeft P σ g, fun a ↦ Equiv.piCongrLeft_apply_apply P σ g a⟩

private noncomputable def fL {p : ℕ} (b : AfP p) : ∀ u : HeightOneSpectrum (𝓞 ℚ), u.adicCompletion ℚ :=
  Classical.choose (exists_pi_extend (fun u : HeightOneSpectrum (𝓞 ℚ) => u.adicCompletion ℚ) primeCorr (gL b))

private theorem fL_corr {p : ℕ} (b : AfP p) (w : HeightOneSpectrum ℤ) : fL b (primeCorr w) = gL b w := Classical.choose_spec
  (exists_pi_extend (fun u : HeightOneSpectrum (𝓞 ℚ) => u.adicCompletion ℚ) primeCorr (gL b)) w

private theorem fL_ev {p : ℕ} (b : AfP p) : ∀ᶠ u : HeightOneSpectrum (𝓞 ℚ) in Filter.cofinite,
    fL b u ∈ u.adicCompletionIntegers ℚ := by
  have hg := gL_ev b
  rw [Filter.eventually_cofinite] at hg ⊢
  refine (hg.image primeCorr).subset ?_
  intro u hu
  obtain ⟨w, rfl⟩ := primeCorr.surjective u
  refine ⟨w, ?_, rfl⟩
  intro hw
  apply hu
  rw [fL_corr]
  exact hw

private noncomputable def liftA {p : ℕ} (b : AfP p) : AfQ := ⟨fL b, fL_ev b⟩

private theorem liftA_apply {p : ℕ} (b : AfP p) (u : HeightOneSpectrum (𝓞 ℚ)) : liftA b u = fL b u := rfl

private theorem rho_surj (p : ℕ) : Function.Surjective (rho p) := by
  intro b
  refine ⟨liftA b, finiteAdeleRingAway_ext fun v ↦ ?_⟩
  rw [eval_rho, liftA_apply, fL_corr, gL_pos, RingEquiv.apply_symm_apply]
end

open GlobalTheory.NormLevelCompare in
private theorem rho_ker (p : ℕ) [Fact p.Prime] (a : AfQ) :
    rho p a = 0 ↔ ∀ v : Plc ℚ, (p : 𝓞 ℚ) ∉ v.asIdeal → a v = 0 := by
  constructor
  · intro h v hv
    obtain ⟨w, rfl⟩ := primeCorr.surjective v
    have h2 : eL w (a (primeCorr w)) = 0 :=
      (congrArg (AfP.eval (⟨w, (away_iff p w).2 hv⟩ : AwayP p)) h).trans (map_zero _)
    exact (map_eq_zero_iff _ (eL w).injective).1 h2
  · intro h
    refine finiteAdeleRingAway_ext fun v ↦ ?_
    rw [eval_rho, map_zero, h _ ((away_iff p v.1).1 v.2), map_zero]

open GlobalTheory.NormLevelCompare in
private theorem rho_int (p : ℕ) [Fact p.Prime] (a : AfQ) :
    IsIntAf (rho p a) ↔ ∀ v : Plc ℚ, (p : 𝓞 ℚ) ∉ v.asIdeal → Valued.v (a v) ≤ 1 := by
  constructor
  · intro h v hv
    obtain ⟨w, rfl⟩ := primeCorr.surjective v
    have h2 : eL w (a (primeCorr w)) ∈ w.adicCompletionIntegers ℚ := h ⟨w, (away_iff p w).2 hv⟩
    rw [eL_mem] at h2
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 h2
  · intro h v
    show AfP.eval v (rho p a) ∈ _
    rw [eval_rho, eL_mem]
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (h _ ((away_iff p v.1).1 v.2))

theorem UpperTheory.Gal.W2.Seed.pAdQEx :
    AdQEx := fun p _ ↦ ⟨⟨rho p, rho_surj p, rho_ker p, rho_int p⟩⟩
end
