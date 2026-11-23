module

public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle155
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemXSmulOfProjective
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle188
public import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.Bundle001
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CayleyHamilton
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle085
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle060
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle206
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle216
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle207
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle197
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.NumberTheory.Padics.ValuativeRel
public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.NumberTheory.Padics.Complex
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle218
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
public import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.SimpleModule.IsAlgClosed
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle007

@[expose] public section

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL

namespace GlobalTheory.NL



theorem N_basis_loc {l : ℕ} [Fact l.Prime] {P : LocPrime l} (H : LocHW l P) (K : FinExt l) (s : ℕ)
    (LL : FinExt l) (h : Good K s LL) (T : Lt K LL) (hT : IsCrys (P.PD K) T.ρ) :
    Nonempty (Module.Basis (Fin (Module.finrank ↥(OL LL) ↥T.L.T)) (AA K LL) ↥((H.W K s LL h).N T)) := by
  obtain ⟨_, -, hl⟩ := GlobalTheory.FinExtIntegers.dvr_complete LL
  haveI := (P.PD K).finK₀
  haveI : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨Module.finrank_pos.ne'⟩
  have hproj := H.W_proj K s LL h T
  generalize H.W K s LL h = W at hproj ⊢
  obtain ⟨hfree, hrk⟩ := W.DD_free T
  rw [← hrk]
  haveI : Module.Finite (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) ↥(W.N T) :=
    Module.Finite.iff_fg.mpr (W.N_fg T)
  have hl0 : ((l : ℕ) : ↥(OL LL)) ≠ 0 := by
    intro h0
    have := congrArg (fun x : ↥(OL LL) => (x : ↥LL.1)) h0
    simp [(Fact.out : l.Prime).ne_zero] at this
  refine GlobalTheory.WachFree.basis_of_regular (ι := ZMod (Module.finrank ℚ_[l] ↥(K0 K))) (O := ↥(OL LL))
    (N := ↥(W.N T)) (E := W.EE) (D := W.DD T) W.EE_inj (W.N T).subtype (W.N_base T hT)
    ((l : ℕ) : ↥(OL LL)) hl0 hl ?_ ?_
  · intro x y hxy
    have h1 : (letπ : LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) • (x : W.DD T) =
        (letπ : LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) • (y : W.DD T) :=
      congrArg Subtype.val hxy
    rw [← algebraMap_smul W.EE, ← algebraMap_smul W.EE letπ (y : W.DD T)] at h1
    exact Subtype.ext (W.EE_π.smul_left_cancel.mp h1)
  · intro x y hxy
    have e1 : zlA LL (Module.finrank ℚ_[l] ↥(K0 K)) (PowerSeries.C ((l : ℕ) : ℤ_[l])) =
        fun _ => PowerSeries.C ((l : ℕ) : ↥(OL LL)) := by
      funext i
      simp
    have e2 : zlA LL (Module.finrank ℚ_[l] ↥(K0 K)) PowerSeries.X = fun _ => PowerSeries.X := by
      funext i
      simp [zlA]
    exact GlobalTheory.HWL.mem_smul_of_projective_comp _ hproj ((l : ℕ) : ℤ_[l])
      (Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero) e1 e2 x y hxy

theorem N_basis : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let _E := ((F l).E K s LL h).tie; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → Nonempty (Module.Basis (Fin (Module.finrank ↥(OL LL) ↥T.L.T)) (AA K LL) ↥(W.N T)) :=
  fun _ HW _ l _ K s LL h T hT => N_basis_loc (HW l) K s LL h T hT

end GlobalTheory.NL
end

section

noncomputable section

open Formalism.BasicNotions Formalism.IndefR.NX
open scoped TensorProduct

namespace GlobalTheory.GoodSS

variable {D : D7} (S : RatDat D.ntw)

def opK (j : ℕ) (f : Module.End D.what₂.LL (S.WL j)) (hf : ∀ x ∈ (S.A j).WK, f x ∈ (S.A j).WK) :
    Module.End S.Ks (FmK S j) :=
  (f.restrictScalars S.Ks).restrict (p := (S.A j).WK) (q := (S.A j).WK) hf

def goodProjectorBaseChangeForms (j : ℕ) (hst : RhoStab S j) (hχ : ChiInLL0 S j) (eC : G0g D.nd → ↥D.LL0) :
    Module.End ↥D.LL0 (↥D.LL0 ⊗[S.Ks] FmK S j) :=
  ∑ᶠ g : G0g D.nd, (eC g * (chiL S j hχ (S.eG.symm g))⁻¹) •
    LinearMap.baseChange ↥D.LL0 (rhoKG S j hst (S.eG.symm g))

end GlobalTheory.GoodSS
end
end

section

open Formalism.MainNotions.N GlobalTheory.PsChar

namespace GlobalTheory.PsChar

theorem finite_semisimple (k R : Type) [Field k] [CharZero k] [IsAlgClosed k] [Ring R] [Algebra k R]
    (d : ℕ) (T : R →ₗ[k] k) (h : IsPsChar d (fun x => T x))
    (hnd : ∀ x, (∀ y, T (x * y) = 0) → x = 0) :
    Module.Finite k R ∧ IsSemisimpleRing R := by
  refine GlobalTheory.T.finite_and_isSemisimpleRing_of_no_nil_ideals_bounded_idempotents k R d (fun x => ?_) (fun x hx => ?_) (fun m e he hne => ?_)
  · obtain ⟨p, hp, -, hT⟩ := cayleyHamilton k R d T h x
    exact ⟨p, hp, hnd _ hT⟩
  · refine hnd x fun y => ?_
    rw [show T (x * y) = T (y * x) from h.comm x y]
    exact GlobalTheory.T.pseudoCharacter_eq_zero_of_isNilpotent k R d T h _ (hx y)
  · have hv : ∀ i, ∃ a : ℕ, 1 ≤ a ∧ T (e i) = a := fun i => by
      obtain ⟨⟨a, -, ha⟩, h0⟩ := GlobalTheory.T.pseudoCharacter_apply_idempotent_nat_le k R d T h (e i) (he.idem i)
      refine ⟨a, Nat.one_le_iff_ne_zero.2 fun h' => hne i (hnd _ (h0 ?_)), ha⟩
      rw [ha, h', Nat.cast_zero]
    choose a ha1 ha using hv
    obtain ⟨⟨s, hs, hsT⟩, -⟩ := GlobalTheory.T.pseudoCharacter_apply_idempotent_nat_le k R d T h (∑ i, e i) he.isIdempotentElem_sum
    have h1 : ((∑ i, a i : ℕ) : k) = s := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← hsT, map_sum]; push_cast; exact Finset.sum_congr rfl fun i _ => (ha i).symm
    have h2 : ∑ i, a i = s := by exact_mod_cast h1
    calc m = ∑ _i : Fin m, 1 := by simp
      _ ≤ ∑ i, a i := Finset.sum_le_sum fun i _ => ha1 i
      _ = s := h2
      _ ≤ d := hs

def traceKer {k A : Type} [Field k] [Ring A] [Algebra k A] (T : A →ₗ[k] k)
    (hc : ∀ x y, T (x * y) = T (y * x)) : TwoSidedIdeal A :=
  TwoSidedIdeal.mk' {x | ∀ y, T (x * y) = 0} (by simp)
    (fun {x y} hx hy z => by simp only [Set.mem_setOf_eq] at hx hy; simp [add_mul, hx z, hy z])
    (fun {x} hx z => by simp only [Set.mem_setOf_eq] at hx; simp [neg_mul, hx z])
    (fun {x y} hy z => by
      simp only [Set.mem_setOf_eq] at hy
      rw [mul_assoc, hc, mul_assoc, hy])
    (fun {x y} hx z => by simp only [Set.mem_setOf_eq] at hx; rw [mul_assoc, hx])

theorem mem_traceKer {k A : Type} [Field k] [Ring A] [Algebra k A] (T : A →ₗ[k] k)
    (hc : ∀ x y, T (x * y) = T (y * x)) (x : A) : x ∈ traceKer T hc ↔ ∀ y, T (x * y) = 0 :=
  TwoSidedIdeal.mem_mk' _ _ _ _ _ _ x

theorem exists_descend {k A B : Type} [Field k] [AddCommGroup A] [Module k A] [AddCommGroup B]
    [Module k B] (f : A →ₗ[k] B) (hf : Function.Surjective f) (T : A →ₗ[k] k)
    (h : ∀ a, f a = 0 → T a = 0) : ∃ S : B →ₗ[k] k, ∀ a, S (f a) = T a := by
  refine ⟨(LinearMap.ker f).liftQ T (fun a ha => h a ha) ∘ₗ (f.quotKerEquivOfSurjective hf).symm.toLinearMap,
    fun a => ?_⟩
  have : (f.quotKerEquivOfSurjective hf).symm (f a) = Submodule.Quotient.mk a := by
    rw [LinearEquiv.symm_apply_eq]; rfl
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, this]
  exact Submodule.liftQ_apply _ _ _

theorem exists_ssRep (Γ k : Type) [Group Γ] [Field k] [CharZero k] [IsAlgClosed k] (d : ℕ)
    (T : Γ → k) (hT : IsPsChar d T) :
    ∃ r : Γ →* GL (Fin d) k, IsSSRep r ∧
      ∀ g, ((r g : GL (Fin d) k) : Matrix (Fin d) (Fin d) k).trace = T g := by
  obtain ⟨T', hT'g, hT'⟩ := exists_linear_extension Γ k d T hT
  have hc : ∀ x y, T' (x * y) = T' (y * x) := hT'.comm
  let I := traceKer T' hc
  let f : MonoidAlgebra k Γ →ₐ[k] I.ringCon.Quotient := RingCon.mkₐ k I.ringCon
  have hf : Function.Surjective f := fun y => Quotient.inductionOn' y fun x => ⟨x, rfl⟩
  have hk : ∀ x, f x = 0 ↔ x ∈ I := fun x => by
    rw [TwoSidedIdeal.mem_iff, ← RingCon.eq]
    rfl
  obtain ⟨S, hS⟩ := exists_descend f.toLinearMap hf T' fun a ha => by
    simpa using (mem_traceKer T' hc a).1 ((hk a).1 ha) 1
  have hS1 : ∀ a, S (f a) = T' a := hS
  have hS' : IsPsChar d (fun x => S x) := by
    refine ⟨?_, ?_, ?_⟩
    · show S 1 = d
      rw [← map_one f, hS1]; exact hT'.one
    · intro x y
      obtain ⟨a, rfl⟩ := hf x
      obtain ⟨b, rfl⟩ := hf y
      show S (f a * f b) = S (f b * f a)
      rw [← map_mul, ← map_mul, hS1, hS1]; exact hc a b
    · intro x
      choose a ha using fun i => hf (x i)
      have hx : x = fun i => (f : MonoidAlgebra k Γ →* I.ringCon.Quotient) (a i) := funext fun i => (ha i).symm
      rw [hx, alt_comp_monoidHom]
      have he : (fun g => S ((f : MonoidAlgebra k Γ →* I.ringCon.Quotient) g)) = fun g => T' g :=
        funext fun g => hS1 g
      rw [he]; exact hT'.alt_eq_zero a
  have hnd : ∀ x, (∀ y, S (x * y) = 0) → x = 0 := by
    intro x hx
    obtain ⟨a, rfl⟩ := hf x
    refine (hk a).2 ((mem_traceKer T' hc a).2 fun b => ?_)
    rw [← hS1, map_mul]; exact hx (f b)
  obtain ⟨hfin, hss⟩ := finite_semisimple k _ d S hS' hnd
  obtain ⟨N, n, hn, ⟨e⟩⟩ := IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed k I.ringCon.Quotient
  let τ : (Π i, Matrix (Fin (n i)) (Fin (n i)) k) →ₗ[k] k := S ∘ₗ e.symm.toLinearMap
  have hτ : ∀ x, τ x = S (e.symm x) := fun x => rfl
  obtain ⟨c, hcτ⟩ := GlobalTheory.T.exists_eq_sum_trace_of_trace_like_pi_matrix k N n τ fun x y => by
    rw [hτ, hτ, map_mul e.symm, map_mul e.symm]; exact hS'.comm _ _
  have hcn : ∀ i, ∃ m : ℕ, c i = m := by
    intro i
    haveI := hn i
    let E : Π j, Matrix (Fin (n j)) (Fin (n j)) k := Pi.single i (Matrix.single 0 0 1)
    have hE : IsIdempotentElem E := by
      unfold IsIdempotentElem
      ext1 j
      by_cases hj : j = i
      · subst hj; simp [E, Matrix.single_mul_single_same]
      · simp [E, hj]
    have hτE : τ E = c i := by
      rw [hcτ, Finset.sum_eq_single i]
      · simp [E, Matrix.trace_single_eq_same]
      · intro j _ hj; simp [E, hj]
      · simp
    obtain ⟨⟨m, -, hm⟩, -⟩ := GlobalTheory.T.pseudoCharacter_apply_idempotent_nat_le k _ d S hS' (e.symm E) (hE.map e.symm)
    exact ⟨m, hτE.symm.trans hm⟩
  choose m hm using hcn
  have hsum : ∑ i, m i * n i = d := by
    have h1 : τ 1 = d := by rw [hτ, map_one]; exact hS'.one
    rw [hcτ] at h1
    simp only [Pi.one_apply, Matrix.trace_one, Fintype.card_fin, hm] at h1
    exact_mod_cast h1
  obtain ⟨ρ₀, hρ₀⟩ := GlobalTheory.T.exists_algHom_trace_eq_sum_mul_trace k N n m d hsum
  let g : I.ringCon.Quotient →ₐ[k] Matrix (Fin d) (Fin d) k := ρ₀.comp e.toAlgHom
  let ρ : MonoidAlgebra k Γ →ₐ[k] Matrix (Fin d) (Fin d) k := g.comp f
  have htr : ∀ a, (ρ a).trace = T' a := fun a => by
    show (ρ₀ (e (f a))).trace = _
    rw [hρ₀, ← hS1, ← e.symm_apply_apply (f a), ← hτ, hcτ]
    simp [hm]
  have hrange : IsSemisimpleRing ρ.range := by
    have : ρ.range = g.range := by
      rw [AlgHom.range_comp, (AlgHom.range_eq_top f).2 hf, Algebra.map_top]
    rw [this]
    exact RingHom.isSemisimpleRing_of_surjective g.rangeRestrict.toRingHom
      (AlgHom.rangeRestrict_surjective _)
  refine ⟨(ρ.toMonoidHom.comp (MonoidAlgebra.of k Γ)).toHomUnits, GlobalTheory.T.isSemisimpleRep_of_isSemisimpleRing_range Γ k d ρ hrange,
    fun x => ?_⟩
  show (ρ (MonoidAlgebra.of k Γ x)).trace = T x
  rw [htr, hT'g]

end GlobalTheory.PsChar
end

section

noncomputable section

namespace GlobalTheory.SenLines

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.AdmLoc TensorProduct PowerSeries

section Series

variable {F M : Type} [Field F] [AddCommGroup M] [Module F M]

def serAct (f : F⟦X⟧) (y : ℤ → M) : ℤ → M := fun m => ∑ᶠ j : ℕ, coeff j f • y (m - j)

def serLine (u : ℤ) (d : M) (c : F⟦X⟧) : ℤ → M :=
  fun m => if 0 ≤ m + u then coeff (m + u).toNat c • d else 0

theorem serAct_one (y : ℤ → M) : serAct (1 : F⟦X⟧) y = y := by
  funext m
  rw [serAct, finsum_eq_single _ 0 (fun j hj => by rw [coeff_one, ite_eq_right hj, zero_smul])]
  simp

def SpanIsLines {N : Type} (L : N → ℤ → M) {r : ℕ} (u : Fin r → ℤ) (d : Fin r → M) (F : Type) [Field F]
    [Module F M] : Prop :=
  ∀ y : ℤ → M, (∃ (s : ℕ) (x : Fin s → N) (f : Fin s → F⟦X⟧), y = ∑ j, serAct (f j) (L (x j))) ↔
    ∃ c : Fin r → F⟦X⟧, y = ∑ k, serLine (u k) (d k) (c k)

end Series

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

def LinesAt (i : ZMod n) (ζ : LL) (U : Multiset ℤ) : Prop :=
  ∃ (u : Fin (Module.finrank LL T.V) → ℤ) (d : Fin (Module.finrank LL T.V) → T.V ⊗[Qp] BdR),
    Finset.univ.val.map u = U ∧ LinearIndependent LL d ∧ SpanIsLines (W.levN T i ζ) u d LL

def QFrame (g : W.Gam) (J : O⟦X⟧ →ₐ[O] O⟦X⟧) : Prop :=
  Function.Injective J ∧
  (∀ a, (∃ b, J b = a) ↔ ∀ δ ∈ W.DelF, W.γ₀ δ a = a) ∧
  J X = W.π₀₁ + ((PD.p : ℕ) : O⟦X⟧) ∧
  (∀ c, constantCoeff (J c) = 0 → X - ((PD.p : ℕ) : O⟦X⟧) ∣ c) ∧
  (∃ s : (O⟦X⟧)ˣ, W.γ₀ g (J X) = J X * J s ∧ X - ((PD.p : ℕ) : O⟦X⟧) ∣ (s : O⟦X⟧) - 1) ∧
  Associated (J X) W.q₀ ∧
  IsUnit (algebraMap (LetA O n) W.EE (W.π₀ + ((PD.p : ℕ) : LetA O n)))

end Generic

end GlobalTheory.SenLines
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

theorem geom_sum_add_one_eq_sum_choose {R : Type*} [Ring R] (D : R) (n : ℕ) :
    ∑ i ∈ Finset.range n, (D + 1) ^ i = ∑ j ∈ Finset.range n, n.choose (j + 1) • D ^ j := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have h := (Commute.one_right D).add_pow n
    simp only [one_pow, mul_one] at h
    rw [h]
    simp_rw [Nat.choose_succ_succ', add_smul]
    rw [Finset.sum_add_distrib, Finset.sum_range_succ (fun j => n.choose (j + 1) • D ^ j) n,
      Nat.choose_succ_self, zero_smul, add_zero, add_comm]
    congr 1
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [nsmul_eq_mul, Nat.cast_comm]

theorem norm_geom_sum_galois_le (l : ℕ) [Fact l.Prime] (σ : GQ l) (S : AddSubgroup (Om l)) (s : ℝ)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hS : ∀ x ∈ S, σ x ∈ S) (hσ : ∀ x ∈ S, ‖σ x - x‖ ≤ s * ‖x‖) :
    ∀ x ∈ S, ‖∑ i ∈ Finset.range l, (σ ^ i) x‖ ≤ max (s ^ (l - 1)) ‖((l : ℕ) : Om l)‖ * ‖x‖ ∧
      ‖(σ ^ l) x - x‖ ≤ max (s ^ (l - 1)) ‖((l : ℕ) : Om l)‖ * s * ‖x‖ := by
  intro x hx
  set M := max (s ^ (l - 1)) ‖((l : ℕ) : Om l)‖ with hM

  have hpowS : ∀ (i : ℕ), ∀ y ∈ S, (σ ^ i) y ∈ S := by
    intro i
    induction i with
    | zero => intro y hy; simpa using hy
    | succ i ih => intro y hy; rw [pow_succ', AlgEquiv.mul_apply]; exact hS _ (ih y hy)

  let T : AddMonoid.End (Om l) := AddMonoidHom.mk' (fun y => σ y) (fun a b => map_add σ a b)
  have hT : ∀ (i : ℕ) (y : Om l), (T ^ i) y = (σ ^ i) y := by
    intro i
    induction i with
    | zero => intro y; rfl
    | succ i ih => intro y; rw [pow_succ', pow_succ', AlgEquiv.mul_apply, ← ih]; rfl
  have hD : ∀ (j : ℕ), ∀ y ∈ S, ((T - 1) ^ j) y ∈ S ∧ ‖((T - 1) ^ j) y‖ ≤ s ^ j * ‖y‖ := by
    intro j
    induction j with
    | zero => intro y hy; rw [pow_zero]; exact ⟨hy, by rw [pow_zero, one_mul]; exact le_rfl⟩
    | succ j ih =>
      intro y hy
      obtain ⟨h1, h2⟩ := ih y hy
      rw [pow_succ']
      change σ (((T - 1) ^ j) y) - ((T - 1) ^ j) y ∈ S ∧
        ‖σ (((T - 1) ^ j) y) - ((T - 1) ^ j) y‖ ≤ s ^ (j + 1) * ‖y‖
      refine ⟨S.sub_mem (hS _ h1) h1, ?_⟩
      calc ‖σ (((T - 1) ^ j) y) - ((T - 1) ^ j) y‖ ≤ s * ‖((T - 1) ^ j) y‖ := hσ _ h1
        _ ≤ s * (s ^ j * ‖y‖) := mul_le_mul_of_nonneg_left h2 hs0
        _ = s ^ (j + 1) * ‖y‖ := by ring

  have hnat : ∀ n : ℕ, ‖((n : ℕ) : Om l)‖ ≤ 1 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Nat.cast_succ]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ih norm_one.le)

  have key := geom_sum_add_one_eq_sum_choose (T - 1) l
  rw [sub_add_cancel] at key
  have hsum : ∑ i ∈ Finset.range l, (σ ^ i) x =
      ∑ j ∈ Finset.range l, l.choose (j + 1) • ((T - 1) ^ j) x := by
    let ev : AddMonoid.End (Om l) →+ Om l :=
      { toFun := fun f => f x, map_zero' := rfl, map_add' := fun _ _ => rfl }
    have h := congrArg ev key

    simp only [map_sum, map_nsmul] at h
    calc ∑ i ∈ Finset.range l, (σ ^ i) x = ∑ i ∈ Finset.range l, (T ^ i) x :=
          Finset.sum_congr rfl fun i _ => (hT i x).symm
      _ = _ := h
  have hbound : ‖∑ i ∈ Finset.range l, (σ ^ i) x‖ ≤ M * ‖x‖ := by
    rw [hsum]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
      (mul_nonneg (le_max_of_le_right (norm_nonneg _)) (norm_nonneg _)) fun j hj => ?_
    obtain ⟨-, hle⟩ := hD j x hx
    have hsj : s ^ j ≤ 1 := pow_le_one₀ hs0 hs1
    rw [nsmul_eq_mul, norm_mul]
    rcases Nat.lt_or_ge (j + 1) l with hlt | hge
    ·
      obtain ⟨m, hm⟩ := (Fact.out : l.Prime).dvd_choose_self (Nat.succ_ne_zero j) hlt
      rw [hm, Nat.cast_mul, norm_mul]
      have h3 : ‖((T - 1) ^ j) x‖ ≤ 1 * ‖x‖ :=
        hle.trans (mul_le_mul_of_nonneg_right hsj (norm_nonneg _))
      calc _ ≤ ‖((l : ℕ) : Om l)‖ * 1 * (1 * ‖x‖) :=
            mul_le_mul (mul_le_mul_of_nonneg_left (hnat m) (norm_nonneg _)) h3 (norm_nonneg _)
              (mul_nonneg (norm_nonneg _) zero_le_one)
        _ ≤ M * ‖x‖ := by
            rw [mul_one, one_mul]
            exact mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)
    ·
      have hjl : j = l - 1 := by have := Finset.mem_range.mp hj; omega
      have hc : l.choose (j + 1) = 1 := by
        rw [show j + 1 = l by have := Finset.mem_range.mp hj; omega, Nat.choose_self]
      rw [hc, Nat.cast_one, norm_one, one_mul]
      calc _ ≤ s ^ j * ‖x‖ := hle
        _ ≤ M * ‖x‖ := by
            rw [hjl]
            exact mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)

  set y := ∑ i ∈ Finset.range l, (σ ^ i) x with hy
  have hyS : y ∈ S := S.sum_mem fun i _ => hpowS i x hx
  have htel : (σ ^ l) x - x = σ y - y := by

    rw [hy, map_sum, ← Finset.sum_sub_distrib]
    have h := Finset.sum_range_sub (fun i => (σ ^ i) x) l
    simp only [pow_zero, AlgEquiv.one_apply] at h
    rw [← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [pow_succ', AlgEquiv.mul_apply]
  refine ⟨hbound, ?_⟩
  rw [htel]
  calc ‖σ y - y‖ ≤ s * ‖y‖ := hσ y hyS
    _ ≤ s * (M * ‖x‖) := mul_le_mul_of_nonneg_left hbound hs0
    _ = M * s * ‖x‖ := by ring

end GlobalTheory.MemLoc
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

theorem _root_.GlobalTheory.T.localFieldInteger_iff_algebraicClosureNorm : ∀ (l : ℕ) [Fact l.Prime] (L : Type) [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra ℚ_[l] L] [ValuativeExtension ℚ_[l] L] [FiniteDimensional ℚ_[l] L] [IsGalois ℚ_[l] L] [Algebra L (Om l)] [IsScalarTower ℚ_[l] L (Om l)] (x : L), (x ∈ 𝒪[L] ↔ ‖algebraMap L (Om l) x‖ ≤ 1) ∧ (valuation L x < 1 ↔ ‖algebraMap L (Om l) x‖ < 1) := by
  first | exact @GlobalTheory.PMon.Ram.mem_integer_iff_norm_le_and_valuation_lt_one_iff_norm_lt | exact GlobalTheory.PMon.Ram.mem_integer_iff_norm_le_and_valuation_lt_one_iff_norm_lt | (intros; apply GlobalTheory.PMon.Ram.mem_integer_iff_norm_le_and_valuation_lt_one_iff_norm_lt <;> assumption)
end

section

open Polynomial

theorem _root_.GlobalTheory.T.exists_separated_roots_additive_poly : ∀ (l : ℕ) [Fact l.Prime] (E M h : ℕ) (a : ℕ → ℂ_[l]) (ρ : ℝ), M + h ≤ E → (∀ k, k ≤ E → ‖a k‖ ≤ 1) → ‖a (M + h)‖ = 1 → 0 < ρ → ρ < 1 → ‖a M‖ * ρ ^ l ^ M = ‖(l : ℂ_[l])‖ → (∀ k, M < k → k ≤ E → ‖a k‖ * ρ ^ l ^ k < ‖(l : ℂ_[l])‖) → ∃ Z : Finset ℂ_[l], l ^ h ≤ Z.card ∧ (∀ W ∈ Z, ‖W‖ ≤ 1 ∧ ∑ k ∈ Finset.range (E + 1), a k * W ^ l ^ k = 0) ∧ ∀ W ∈ Z, ∀ W' ∈ Z, W ≠ W' → ρ < ‖W - W'‖ := by
  first | exact @GlobalTheory.separated_roots_additive_poly | exact GlobalTheory.separated_roots_additive_poly | (intros; apply GlobalTheory.separated_roots_additive_poly <;> assumption)
end
