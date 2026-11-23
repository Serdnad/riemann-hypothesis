module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.Bundle002
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle002
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle005
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.TwistSplitObj
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.TwistSplitCech
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle006
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle029
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PIdealTwistFamily
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
import Mathlib.Topology.Sheaves.Init
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Statements
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.AlgDefs
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.Bundle003

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver mConeMapOver)
open GroundTheory.Heights₂.Heights.NumbersDVR (MRing blockWeight IsMultiHomog IsMultiProjPrime gradedPiece hilbFn intNum
  genFib)
open GroundTheory.Heights₂.Heights.FieldNumbers (relDim)

namespace GenFibNef

section Transport

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {F₁ F₂ : Type} [Field F₁] [Field F₂] (e : F₁ ≃+* F₂)


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem isMultiHomog_map_iff (f : MRing ι F₁) (b : K → ℕ) :
    IsMultiHomog (map (e : F₁ →+* F₂) f) b ↔ IsMultiHomog f b := by
  unfold IsMultiHomog IsWeightedHomogeneous
  simp only [coeff_map, ne_eq, RingHom.coe_coe, EmbeddingLike.map_eq_zero_iff]

noncomputable def quotEquiv (P : Ideal (MRing ι F₁)) :
    (MRing ι F₁ ⧸ P) ≃+* (MRing ι F₂ ⧸ P.map (map (e : F₁ →+* F₂))) :=
  Ideal.quotientEquiv P _ (mapEquiv (Σ k, ι k) e) (by
    congr 1)


omit [Fintype K] [DecidableEq K] [∀ k, Fintype (ι k)] in
theorem quotEquiv_mk (P : Ideal (MRing ι F₁)) (f : MRing ι F₁) :
    quotEquiv e P (Ideal.Quotient.mk P f) = Ideal.Quotient.mk _ (map (e : F₁ →+* F₂) f) := rfl


omit [Fintype K] [DecidableEq K] [∀ k, Fintype (ι k)] in
theorem quotEquiv_smul (P : Ideal (MRing ι F₁)) (r : F₁) (x : MRing ι F₁ ⧸ P) :
    quotEquiv e P (r • x) = e r • quotEquiv e P x := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  have h₁ : r • Ideal.Quotient.mk P f = Ideal.Quotient.mk P (C r * f) := by
    rw [← Ideal.Quotient.mkₐ_eq_mk F₁, ← map_smul, smul_eq_C_mul]
  have h₂ : e r • Ideal.Quotient.mk (P.map (map (e : F₁ →+* F₂))) (map (e : F₁ →+* F₂) f) =
      Ideal.Quotient.mk (P.map (map (e : F₁ →+* F₂))) (C (e r) * map (e : F₁ →+* F₂) f) := by
    rw [← Ideal.Quotient.mkₐ_eq_mk F₂, ← map_smul, smul_eq_C_mul]
  rw [h₁, quotEquiv_mk, quotEquiv_mk, h₂, map_mul, map_C]
  rfl


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem quotEquiv_mem_gradedPiece (P : Ideal (MRing ι F₁)) (n : K → ℕ) (x : MRing ι F₁ ⧸ P)
    (hx : x ∈ gradedPiece P n) : quotEquiv e P x ∈ gradedPiece (P.map (map (e : F₁ →+* F₂))) n := by
  obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.1 hx
  refine Submodule.mem_map.2 ⟨map (e : F₁ →+* F₂) f, ?_, rfl⟩
  rw [mem_weightedHomogeneousSubmodule] at hf ⊢
  exact (isMultiHomog_map_iff e f n).2 hf

theorem finrank_gradedPiece_map (P : Ideal (MRing ι F₁)) (n : K → ℕ) :
    Module.finrank F₂ (gradedPiece (P.map (map (e : F₁ →+* F₂))) n) =
      Module.finrank F₁ (gradedPiece P n) := by
  let j₀ : gradedPiece P n →+ gradedPiece (P.map (map (e : F₁ →+* F₂))) n :=
    { toFun := fun x => ⟨quotEquiv e P x.1, quotEquiv_mem_gradedPiece e P n x.1 x.2⟩
      map_zero' := Subtype.ext (map_zero (quotEquiv e P))
      map_add' := fun a b => Subtype.ext (map_add (quotEquiv e P) a.1 b.1) }
  have hinj : Function.Injective j₀ := fun a b h =>
    Subtype.ext ((quotEquiv e P).injective (congrArg Subtype.val h))
  have hsurj : Function.Surjective j₀ := by
    rintro ⟨z, hz⟩
    obtain ⟨g, hg, rfl⟩ := Submodule.mem_map.1 hz
    have hg' : map (e.symm : F₂ →+* F₁) g ∈ weightedHomogeneousSubmodule F₁ (blockWeight ι) n := by
      rw [mem_weightedHomogeneousSubmodule] at hg ⊢
      have hgg : map (e : F₁ →+* F₂) (map (e.symm : F₂ →+* F₁) g) = g :=
        (mapEquiv (Σ k, ι k) e).apply_symm_apply g
      have h' : IsMultiHomog (map (e : F₁ →+* F₂) (map (e.symm : F₂ →+* F₁) g)) n := by
        rw [hgg]
        exact hg
      exact (isMultiHomog_map_iff e _ n).1 h'
    refine ⟨⟨Ideal.Quotient.mk P (map (e.symm : F₂ →+* F₁) g), Submodule.mem_map.2 ⟨_, hg', rfl⟩⟩, ?_⟩
    apply Subtype.ext
    change quotEquiv e P (Ideal.Quotient.mk P (map (e.symm : F₂ →+* F₁) g)) = Ideal.Quotient.mk _ g
    rw [quotEquiv_mk]
    congr 1
    exact (mapEquiv (Σ k, ι k) e).apply_symm_apply g
  let j := AddEquiv.ofBijective j₀ ⟨hinj, hsurj⟩
  have hrank := rank_eq_of_equiv_equiv (e : F₁ → F₂) j e.bijective (fun r m => by
    apply Subtype.ext
    exact quotEquiv_smul e P r m)
  unfold Module.finrank
  rw [hrank]

theorem hilbFn_map (P : Ideal (MRing ι F₁)) :
    hilbFn (P.map (map (e : F₁ →+* F₂))) = hilbFn P := by
  funext m
  unfold hilbFn
  split_ifs
  · rw [finrank_gradedPiece_map]
  · rfl

theorem intNum_map (P : Ideal (MRing ι F₁)) {n : ℕ} (bs : Fin n → K → ℤ) :
    intNum F₂ (P.map (map (e : F₁ →+* F₂))) bs = intNum F₁ P bs := by
  unfold intNum
  rw [hilbFn_map]

end Transport

end GenFibNef

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (cechHc quotPart mIdealOver)

def MultiSerre.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)]
    [∀ k, LinearOrder (ι k)] (V : Ideal (MvPolynomial (Σ k, ι k) F)),
    NumbersDVR.IsMultiHomogIdeal V →
      ∀ᶠ m : K → ℤ in Filter.atTop,
        (∀ i : ℕ, 1 ≤ i → Subsingleton (cechHc ι (quotPart F V) m i)) ∧
        (Module.finrank F (cechHc ι (quotPart F V) m 0) : ℤ) = NumbersDVR.hilbFn V m

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (cechHc quotPart mIdealOver)

def EulerPoly.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)]
    [∀ k, LinearOrder (ι k)] (V : Ideal (MvPolynomial (Σ k, ι k) F)),
    NumbersDVR.IsMultiHomogIdeal V →
      ∃ (B : ℕ) (χ : MvPolynomial K ℚ),
        (∀ (m : K → ℤ) (i : ℕ), FiniteDimensional F (cechHc ι (quotPart F V) m i)) ∧
        (∀ (m : K → ℤ) (i : ℕ), B < i → Subsingleton (cechHc ι (quotPart F V) m i)) ∧
        ∀ m : K → ℤ, ∑ i ∈ Finset.range (B + 1),
          (-1 : ℚ) ^ i * (Module.finrank F (cechHc ι (quotPart F V) m i) : ℚ) =
            eval (fun k => (m k : ℚ)) χ

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open GroundTheory.Heights₂.Heights.NumbersDVR (MRing IsMultiProjPrime intNum)
open GroundTheory.Heights₂.Heights.FieldNumbers (relDim)
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver)

def SegreLiftComap.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (W' : Ideal (MRing (segreIdx ι) F)), IsMultiProjPrime W' →
      segreRels ι F ⊆ W' →
      IsMultiProjPrime (W'.comap (segreIncl ι F)) ∧ W' = segreLift ι F (W'.comap (segreIncl ι F))

theorem SegreLiftComap.hyps :
    IsMultiProjPrime (⊥ : Ideal (MRing (segreIdx (fun _ : Unit => Fin 1)) ℚ)) ∧
      segreRels (fun _ : Unit => Fin 1) ℚ ⊆
        ((⊥ : Ideal (MRing (segreIdx (fun _ : Unit => Fin 1)) ℚ)) : Set _) := by
  have : ∀ k, Nonempty (segreIdx (fun _ : Unit => Fin 1) k) := fun k => by
    rcases k with _ | _
    · exact ⟨fun _ => (0 : Fin 1)⟩
    · exact ⟨(0 : Fin 1)⟩
  refine ⟨NumbersDVR.isMultiProjPrime_bot, ?_⟩
  rintro g ⟨c, d, rfl⟩
  obtain rfl : c = d := Subsingleton.elim _ _
  simp

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open GroundTheory.Heights₂.Heights.NumbersDVR (MRing IsMultiProjPrime intNum)
open GroundTheory.Heights₂.Heights.FieldNumbers (relDim)
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver)

def SegreLiftPrime.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (W : Ideal (MRing ι F)), IsMultiProjPrime W →
      IsMultiProjPrime (segreLift ι F W)

theorem SegreLiftPrime.hyps : IsMultiProjPrime (⊥ : Ideal (MRing (fun _ : Unit => Fin 2) ℚ)) :=
  NumbersDVR.isMultiProjPrime_bot

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

section Retract

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {r : ℕ} (η : Fin (r + 1) → Ω) (M₀ : FinGradedSub (S := S) (x := x) Ω) (n : ℕ) (c : ℤ)
  {G B : SubSystem S x Ω} (hG : ∀ I, M₀.tilde 0 I = G.sub I)
  (hB : ∀ I, Submodule.span (chartRing S x I) (Set.range η) = B.sub I)


include hG hB in
theorem twist_retract (i : ℕ) :
    ∃ (ι : ((G.twist (B.pow n)).twist (twistSys S x c)).H i →+ cohom (twGraded η M₀) i c)
      (π : cohom (twGraded η M₀) i c →+ ((G.twist (B.pow n)).twist (twistSys S x c)).H i),
      ∀ z, π (ι z) = z := by
  have hker : ∀ z : Cech.Cochain (fun K : Chart x => ↥(((G.twist (B.pow n)).twist (twistSys S x c)).sub K)) i,
      Cech.d _ ((G.twist (B.pow n)).twist (twistSys S x c)).res i z = 0 →
      Cech.d _ locResS i (Fmap η M₀ n c hG hB i z) = 0 := by
    intro z hz
    rw [← F_d, hz, Fmap_zero]
  have hker' : ∀ (s : Cech.Cochain (locSys (MvPolynomial (Fin (r + 1)) S) N (TwM η M₀)) i)
      (hs : s ∈ Cech.Cdeg (locSys (MvPolynomial (Fin (r + 1)) S) N (TwM η M₀)) (degLoc (twGraded η M₀) c) i),
      Cech.d _ locResS i s = 0 →
      Cech.d _ ((G.twist (B.pow n)).twist (twistSys S x c)).res i (Gm η M₀ n c hG hB i s hs) = 0 := by
    intro s hs h0
    rw [← Gm_d η M₀ n c hG hB i s hs (by rw [h0]; exact Submodule.zero_mem _)]
    funext K
    apply Subtype.ext
    change gm η M₀ n c (i + 1) (Cech.d _ locResS i s) K = 0
    rw [h0, gm_zero]
  let f : LinearMap.ker (Cech.d (fun K : Chart x => ↥(((G.twist (B.pow n)).twist (twistSys S x c)).sub K))
        ((G.twist (B.pow n)).twist (twistSys S x c)).res i) →+
      Cech.cocyDeg (locSys (MvPolynomial (Fin (r + 1)) S) N (TwM η M₀)) (degLoc (twGraded η M₀) c) locResS i :=
    { toFun := fun z => ⟨Fmap η M₀ n c hG hB i z.1, Submodule.mem_inf.mpr
        ⟨LinearMap.mem_ker.mpr (hker z.1 (LinearMap.mem_ker.mp z.2)), Fmap_mem η M₀ n c hG hB i z.1⟩⟩
      map_zero' := Subtype.ext (Fmap_zero η M₀ n c hG hB i)
      map_add' := fun a b => Subtype.ext (Fmap_add η M₀ n c hG hB i a.1 b.1) }
  let g : Cech.cocyDeg (locSys (MvPolynomial (Fin (r + 1)) S) N (TwM η M₀)) (degLoc (twGraded η M₀) c) locResS i →+
      LinearMap.ker (Cech.d (fun K : Chart x => ↥(((G.twist (B.pow n)).twist (twistSys S x c)).sub K))
        ((G.twist (B.pow n)).twist (twistSys S x c)).res i) :=
    { toFun := fun y => ⟨Gm η M₀ n c hG hB i y.1 (Submodule.mem_inf.mp y.2).2,
        LinearMap.mem_ker.mpr (hker' _ _ (LinearMap.mem_ker.mp (Submodule.mem_inf.mp y.2).1))⟩
      map_zero' := Subtype.ext (funext fun K => Subtype.ext (gm_zero η M₀ n c i K))
      map_add' := fun a b => Subtype.ext (funext fun K => Subtype.ext (gm_add η M₀ n c i a.1 b.1 K)) }
  set_option synthInstance.maxHeartbeats 200000 in
    refine quot_retract _ _ f g ?_ ?_ ?_
    · intro z hz
      exact F_bdry η M₀ n c hG hB i z.1 hz
    · intro y hy
      exact G_bdry η M₀ n c hG hB i y.1 (Submodule.mem_inf.mp y.2).2 hy
    · intro z
      apply Subtype.ext
      funext K
      apply Subtype.ext
      exact gm_Fmap η M₀ n c hG hB i z.1 K

end Retract

theorem TwistSplit.proof : TwistSplit.Statement := by
  intro S _ _ Ω _ _ N x M₀ G B r η hG _ hB
  refine ⟨TwM η M₀, inferInstance, inferInstance, inferInstance, inferInstance, twGraded η M₀, inferInstance, ?_⟩
  intro b c i
  exact twist_retract η M₀ b c hG hB i

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

section Helpers

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem twistPows_twist_comm (F Q : SubSystem S x Ω) :
    ∀ (t : ℕ) (L : Fin t → SubSystem S x Ω) (n : Fin t → ℕ),
      (F.twist Q).twistPows t L n = (F.twistPows t L n).twist Q
  | 0, _, _ => rfl
  | t + 1, L, n => by
    simp only [SubSystem.twistPows]
    rw [twistPows_twist_comm F Q t, SubSystem.twist_assoc, SubSystem.twist_comm Q, ← SubSystem.twist_assoc]

def twistPowsBundle (F : LineBundle S x) :
    (t : ℕ) → (Fin t → LineBundle S x) → (Fin t → ℕ) → LineBundle S x
  | 0, _, _ => F
  | t + 1, L, n => (twistPowsBundle F t (fun j => L j.castSucc) (fun j => n j.castSucc)).tensorProd
      ((L (Fin.last t)).powBundle (n (Fin.last t)))

theorem twistPowsBundle_toSubSystem (F : LineBundle S x) :
    ∀ (t : ℕ) (L : Fin t → LineBundle S x) (n : Fin t → ℕ),
      (twistPowsBundle F t L n).toSubSystem = F.toSubSystem.twistPows t (fun j => (L j).toSubSystem) n
  | 0, _, _ => rfl
  | t + 1, L, n => by
    change (twistPowsBundle F t (fun j => L j.castSucc) (fun j => n j.castSucc)).toSubSystem.twist
      ((L (Fin.last t)).powBundle (n (Fin.last t))).toSubSystem = _
    rw [twistPowsBundle_toSubSystem F t, LineBundle.powBundle_toSubSystem]
    rfl

theorem idealMod_le_one (J : Ideal (Poly S N)) (I : Chart x) : idealMod J I ≤ 1 := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨f, s, e, -, hs, hf, hse, rfl⟩
  exact Submodule.mem_one.mpr ⟨⟨_, f, s, e, hs, hf, hse, rfl⟩, rfl⟩

theorem idealMod_le_of_le {J J' : Ideal (Poly S N)} (h : J ≤ J') (I : Chart x) :
    idealMod J I ≤ idealMod J' I :=
  Submodule.span_mono fun _ ⟨f, s, e, hf, hs, hfe, hse, hz⟩ => ⟨f, s, e, h hf, hs, hfe, hse, hz⟩

theorem twist_idealSys_sub_le (Q : SubSystem S x Ω) (J : Ideal (Poly S N)) (I : Chart x) :
    (Q.twist (idealSys x J)).sub I ≤ Q.sub I := by
  rw [SubSystem.twist_sub_eq_mul_of_line]
  exact (Submodule.mul_le.mpr fun a ha b hb => Submodule.mul_mem_mul (idealMod_le_one J I ha) hb).trans (one_mul _).le

theorem twist_idealSys_sub_mono (Q : SubSystem S x Ω) {J J' : Ideal (Poly S N)} (h : J ≤ J') (I : Chart x) :
    (Q.twist (idealSys x J)).sub I ≤ (Q.twist (idealSys x J')).sub I := by
  rw [SubSystem.twist_sub_eq_mul_of_line, SubSystem.twist_sub_eq_mul_of_line]
  exact Submodule.mul_le.mpr fun a ha b hb => Submodule.mul_mem_mul (idealMod_le_of_le h I ha) hb

end Helpers

theorem sup_span_X_homogeneous {R : Type u} [CommRing R] {N : ℕ} (pp : Ideal (Poly R N))
    (hh : ∀ f ∈ pp, ∀ d : ℕ, homogeneousComponent d f ∈ pp) (i : Fin (N + 1)) :
    ∀ f ∈ pp ⊔ Ideal.span {(X i : Poly R N)}, ∀ d : ℕ,
      homogeneousComponent d f ∈ pp ⊔ Ideal.span {(X i : Poly R N)} := by
  intro f hf d
  obtain ⟨g, hg, y, hy, rfl⟩ := Submodule.mem_sup.mp hf
  obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp hy
  rw [map_add (f := _)]
  refine Ideal.add_mem _ (Ideal.mem_sup_left (hh g hg d)) (Ideal.mem_sup_right ?_)
  have hspan := IdealTwistFamily.homogeneousComponent_mul_form r (X i) (isHomogeneous_X R i) d
  refine (Submodule.span_le.mpr ?_ : _ ≤ (Ideal.span {(X i : Poly R N)}).restrictScalars R) hspan
  rintro _ ⟨z, d', -, -, rfl⟩
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

theorem SnapperHyperplane.proof (hA : SnapperQuotAdd.Statement.{u, w, w})
    (hD : SnapperQuotDevissage.Statement.{u, w, w}) (hM : SnapperHyperplaneMid.Statement.{u, w}) :
    SnapperHyperplane.Statement.{u, w} := by
  intro k _ Ω _ _ N x pp hp hh hle i hi a
  set J : Ideal (Poly k N) := pp ⊔ Ideal.span {(X i : Poly k N)} with hJdef
  let B := twistBundle k x (a + 1)
  let F₂ : SubFamily k x Ω :=
    { B.twist (idealSys x J) with mem_iff := IdealTwistFamily.twist_mem_iff B J }
  obtain ⟨r, qq, b, hqq, heq⟩ := hD k Ω N x Ω B.toSubFamily F₂ B.fg
    (fun I => twist_idealSys_sub_le B.toSubSystem J I) J (sup_span_X_homogeneous pp hh i)
    (hle.trans le_sup_left) (fun I => le_rfl)
  refine ⟨r, qq, b, fun m => ⟨(hqq m).1, (hqq m).2.1, le_sup_left.trans (hqq m).2.2,
    (hqq m).2.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))⟩, fun t L n c => ?_⟩
  let Q := (twistPowsBundle B t L n).tensorProd (twistBundle k x c)
  have hQ : Q.toSubSystem =
      ((twistSys k x (a + 1)).twistPows t (fun j => (L j).toSubSystem) n).twist (twistSys k x c) := by
    change (twistPowsBundle B t L n).toSubSystem.twist (twistSys k x c) = _
    rw [twistPowsBundle_toSubSystem]
    rfl
  have hG : ∀ K : Ideal (Poly k N),
      (((twistSys k x (a + 1)).twist (idealSys x K)).twistPows t (fun j => (L j).toSubSystem) n).twist
        (twistSys k x c) = Q.toSubSystem.twist (idealSys x K) := by
    intro K
    rw [hQ, twistPows_twist_comm (twistSys k x (a + 1)) (idealSys x K), SubSystem.twist_assoc,
      SubSystem.twist_comm (idealSys x K), ← SubSystem.twist_assoc]
  let G₂ : SubFamily k x Ω := { Q.twist (idealSys x J) with mem_iff := IdealTwistFamily.twist_mem_iff Q J }
  let G₃ : SubFamily k x Ω := { Q.twist (idealSys x pp) with mem_iff := IdealTwistFamily.twist_mem_iff Q pp }
  have hadd : eulerCharQuot k Q.toSubSystem (Q.toSubSystem.twist (idealSys x pp)) =
      eulerCharQuot k Q.toSubSystem (Q.toSubSystem.twist (idealSys x J)) +
        eulerCharQuot k (Q.toSubSystem.twist (idealSys x J)) (Q.toSubSystem.twist (idealSys x pp)) :=
    hA k Ω N x Ω Q.toSubFamily G₂ G₃ Q.fg (fun I => twist_idealSys_sub_le Q.toSubSystem J I)
      (fun I => twist_idealSys_sub_mono Q.toSubSystem le_sup_left I)
  have h1 : pieceChar k pp a L n (c + 1) =
      eulerCharQuot k Q.toSubSystem (Q.toSubSystem.twist (idealSys x pp)) := by
    have eA : ((twistSys k x a).twistPows t (fun j => (L j).toSubSystem) n).twist (twistSys k x (c + 1)) =
        Q.toSubSystem := by
      rw [hQ, ← twistSys_twist_eq_add a 1,
        twistPows_twist_comm (twistSys k x a) (twistSys k x 1), SubSystem.twist_assoc,
        twistSys_twist_eq_add, add_comm 1 c]
    have eB : (((twistSys k x a).twist (idealSys x pp)).twistPows t (fun j => (L j).toSubSystem) n).twist
        (twistSys k x (c + 1)) = Q.toSubSystem.twist (idealSys x pp) := by
      rw [← hG pp, ← twistSys_twist_eq_add a 1, SubSystem.twist_assoc (twistSys k x a),
        SubSystem.twist_comm (twistSys k x 1), ← SubSystem.twist_assoc (twistSys k x a),
        twistPows_twist_comm ((twistSys k x a).twist (idealSys x pp)) (twistSys k x 1),
        SubSystem.twist_assoc _ (twistSys k x 1), twistSys_twist_eq_add, add_comm 1 c]
    unfold pieceChar
    rw [eA, eB]
  have h2 : eulerCharQuot k Q.toSubSystem (Q.toSubSystem.twist (idealSys x J)) =
      ∑ m, pieceChar k (qq m) (b m) L n c := by
    have := heq t L n c
    change eulerCharQuot k
      (((twistSys k x (a + 1)).twistPows t (fun j => (L j).toSubSystem) n).twist (twistSys k x c))
      ((((twistSys k x (a + 1)).twist (idealSys x J)).twistPows t (fun j => (L j).toSubSystem) n).twist
        (twistSys k x c)) = _ at this
    rwa [hG J, ← hQ] at this
  have h3 := hM k Ω N x pp hp hh hle i hi a t L n c
  rw [← hJdef, hG J, hG pp] at h3
  rw [h1, hadd, h2, h3]
  ring

end

end GroundTheory.Heights₂.Heights.Kleiman
end
