module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle024
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.TraceConjugationCover

variable {l : ℕ} [Fact l.Prime] {Γ : Type} [Group Γ] {a : ℕ}

def tup {m : ℕ} (ρs : Fin m → (Γ →* GL (Fin a) (Om l))) (g : Γ) : Fin m → Matrix (Fin a) (Fin a) (Om l) :=
  fun k => ((ρs k g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))

def latL {m : ℕ} (t : Fin m → Finset (Matrix (Fin a) (Fin a) (Om l))) (M : ℕ) :
    Submodule ℤ_[l] (Fin m → Matrix (Fin a) (Fin a) (Om l)) :=
  Submodule.span ℤ_[l] (⋃ k, (fun x => Pi.single k ((l : Om l) ^ M • x)) '' (t k : Set (Matrix (Fin a) (Fin a) (Om l))))

def latT {m : ℕ} (ρs : Fin m → (Γ →* GL (Fin a) (Om l))) (t : Fin m → Finset (Matrix (Fin a) (Fin a) (Om l))) (M : ℕ) :
    Submodule ℤ_[l] (Fin m → Matrix (Fin a) (Fin a) (Om l)) :=
  Submodule.span ℤ_[l] (Set.range (tup ρs)) ⊔ latL t M

def Carries (r : Γ →* GL (Fin a) (Om l)) {d d' m : ℕ} (b : Fin d → Matrix (Fin a) (Fin a) (Om l))
    (ρs : Fin m → (Γ →* GL (Fin a) (Om l))) (t : Fin m → Finset (Matrix (Fin a) (Fin a) (Om l))) (M : ℕ)
    (bb : Fin d' → Fin m → Matrix (Fin a) (Fin a) (Om l)) (P : Matrix (Fin d) (Fin d') ℤ_[l]) (N : ℕ) : Prop :=
  ∀ (z : Fin d' → ℤ_[l]) (F : Γ →₀ ℤ_[l]) (y : Fin m → Matrix (Fin a) (Fin a) (Om l)), y ∈ latL t M →
    ∑ s, zOm l (z s) • bb s = (F.sum fun g c => zOm l c • tup ρs g) + y →
    ∃ w : Fin d → ℤ_[l], ∑ i, zOm l ((P *ᵥ z) i) • b i =
      (F.sum fun g c => zOm l c • ((r g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))) +
        (l : Om l) ^ N • ∑ i, zOm l (w i) • b i

theorem zOm_smul {α : Type} [AddCommGroup α] [Module (Om l) α] [Module ℤ_[l] α] [IsScalarTower ℤ_[l] (Om l) α]
    (c : ℤ_[l]) (x : α) : zOm l c • x = c • x := by
  rw [← algebraMap_smul (Om l) c x]
  congr 1

theorem norm_l : ‖(l : Om l)‖ = (l : ℝ)⁻¹ := by
  rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l))]
  exact (PadicAlgCl.norm_extends l (l : ℚ_[l])).trans Padic.norm_p

theorem norm_zOm_le (c : ℤ_[l]) : ‖zOm l c‖ ≤ 1 := by
  simp only [zOm, RingHom.comp_apply]
  exact (PadicAlgCl.norm_extends l _).trans_le (PadicInt.norm_le_one c)

theorem tup_mem_latT {m : ℕ} (ρs : Fin m → (Γ →* GL (Fin a) (Om l))) (t : Fin m → Finset (Matrix (Fin a) (Fin a) (Om l)))
    (M : ℕ) (g : Γ) : tup ρs g ∈ latT ρs t M :=
  Submodule.mem_sup_left (Submodule.subset_span ⟨g, rfl⟩)

theorem traceL : ∀ (l : ℕ) [Fact l.Prime] (a d : ℕ) (b : Fin d → Matrix (Fin a) (Fin a) (Om l)), ∃ K : ℕ, ∀ w : Fin d → ℤ_[l], ‖(∑ i, zOm l (w i) • b i).trace‖ ≤ (l : ℝ) ^ K := by
  intro l _ a d b
  obtain ⟨K, hK⟩ := pow_unbounded_of_one_lt (∑ i, ‖(b i).trace‖) (show (1 : ℝ) < l by exact_mod_cast (Fact.out : l.Prime).one_lt)
  refine ⟨K, fun w => ?_⟩
  rw [Matrix.trace_sum]
  refine (norm_sum_le _ _).trans (le_trans ?_ hK.le)
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Matrix.trace_smul, smul_eq_mul, norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (norm_zOm_le _)

end GlobalTheory.TraceConjugationCover

end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.KerLat

variable {l : ℕ} [Fact l.Prime]

def kerMod {d d' : ℕ} (P : Matrix (Fin d) (Fin d') ℤ_[l]) (n : ℕ) : Submodule ℤ_[l] (Fin d' → ℤ_[l]) where
  carrier := {v | ∀ i, (l : ℤ_[l]) ^ n ∣ (P *ᵥ v) i}
  add_mem' {a b} ha hb i := by
    rw [Matrix.mulVec_add]; exact dvd_add (ha i) (hb i)
  zero_mem' i := by simp
  smul_mem' c v hv i := by
    rw [Matrix.mulVec_smul]; exact Dvd.dvd.mul_left (hv i) c

theorem mulVec_mem_kerMod {d d' n : ℕ} {P : Matrix (Fin d) (Fin d') ℤ_[l]}
    {A : Matrix (Fin d') (Fin d') ℤ_[l]} {B : Matrix (Fin d) (Fin d) ℤ_[l]}
    (h : ∀ i j, (l : ℤ_[l]) ^ n ∣ (P * A - B * P) i j) {v : Fin d' → ℤ_[l]} (hv : v ∈ kerMod P n) :
    A *ᵥ v ∈ kerMod P n := by
  intro i
  have e : P *ᵥ (A *ᵥ v) = (P * A - B * P) *ᵥ v + B *ᵥ (P *ᵥ v) := by
    rw [Matrix.sub_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]; abel
  rw [e, Pi.add_apply]
  refine dvd_add ?_ ?_
  · show _ ∣ ∑ j, (P * A - B * P) i j * v j
    exact Finset.dvd_sum fun j _ => dvd_mul_of_dvd_left (h i j) _
  · show _ ∣ ∑ j, B i j * (P *ᵥ v) j
    exact Finset.dvd_sum fun j _ => dvd_mul_of_dvd_right (hv j) _

theorem pow_ne_zero' (n : ℕ) : ((l : ℤ_[l]) ^ n) ≠ 0 :=
  pow_ne_zero _ (by exact_mod_cast (Fact.out : l.Prime).ne_zero)

theorem finrank_kerMod {d d' n : ℕ} (P : Matrix (Fin d) (Fin d') ℤ_[l]) :
    Module.finrank ℤ_[l] (kerMod P n) = d' := by
  apply le_antisymm
  · calc Module.finrank ℤ_[l] (kerMod P n) ≤ Module.finrank ℤ_[l] (Fin d' → ℤ_[l]) :=
          Submodule.finrank_le _
      _ = d' := by simp
  · have hm : ∀ v : Fin d' → ℤ_[l], ((l : ℤ_[l]) ^ n • LinearMap.id : (Fin d' → ℤ_[l]) →ₗ[ℤ_[l]] _) v ∈ kerMod P n := by
      intro v i
      simp only [LinearMap.smul_apply, LinearMap.id_apply, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
      exact dvd_mul_right _ _
    let φ : (Fin d' → ℤ_[l]) →ₗ[ℤ_[l]] kerMod P n :=
      LinearMap.codRestrict (kerMod P n) ((l : ℤ_[l]) ^ n • LinearMap.id) hm
    have hinj : Function.Injective φ := by
      intro a b hab
      have h2 := congrArg Subtype.val hab
      simp only [φ, LinearMap.codRestrict_apply, LinearMap.smul_apply, LinearMap.id_apply] at h2
      exact smul_right_injective _ (pow_ne_zero' n) h2
    have := LinearMap.finrank_le_finrank_of_injective hinj
    simpa using this

end GlobalTheory.KerLat

namespace GlobalTheory.KerLat

variable {l : ℕ} [Fact l.Prime]

noncomputable def kerBasis {d d' : ℕ} (P : Matrix (Fin d) (Fin d') ℤ_[l]) (n : ℕ) :
    Module.Basis (Fin d') ℤ_[l] (kerMod P n) :=
  Module.finBasisOfFinrankEq ℤ_[l] (kerMod P n) (finrank_kerMod P)

noncomputable def kerMat {d d' : ℕ} (P : Matrix (Fin d) (Fin d') ℤ_[l]) (n : ℕ) :
    Matrix (Fin d') (Fin d') ℤ_[l] :=
  Matrix.of fun i j => ((kerBasis P n j : kerMod P n) : Fin d' → ℤ_[l]) i

theorem kerMat_mulVec {d d' : ℕ} (P : Matrix (Fin d) (Fin d') ℤ_[l]) (n : ℕ) (w : Fin d' → ℤ_[l]) :
    kerMat P n *ᵥ w = ((∑ j, w j • kerBasis P n j : kerMod P n) : Fin d' → ℤ_[l]) := by
  ext i
  simp [kerMat, Matrix.mulVec, dotProduct, Submodule.coe_sum, Finset.sum_apply, mul_comm]

theorem exists_kernel_lattice : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] (d d' n : ℕ) (ρ : Γ →* GL (Fin d) ℤ_[l]) (ρ' : Γ →* GL (Fin d') ℤ_[l]) (Pi : Matrix (Fin d) (Fin d') (ℤ_[l])), Onto (fun g => (ρ g).val) (fun g => (ρ' g).val) Pi n → ∃ (f : Matrix (Fin d') (Fin d') (ℤ_[l])) (ρ'' : Γ →* GL (Fin d') ℤ_[l]), f.det ≠ 0 ∧ (∀ g, f * (ρ'' g).val = (ρ' g).val * f) ∧ ∀ v : Fin d' → ℤ_[l], (∀ i, (l : ℤ_[l]) ^ n ∣ (Pi *ᵥ v) i) ↔ ∃ w, v = f *ᵥ w := by
  intro l _ Γ _ d d' n ρ ρ' P hP
  set b := kerBasis P n
  set f := kerMat P n
  have hf : ∀ w, f *ᵥ w = ((∑ j, w j • b j : kerMod P n) : Fin d' → ℤ_[l]) := kerMat_mulVec P n
  have hiff : ∀ v, v ∈ kerMod P n ↔ ∃ w, v = f *ᵥ w := by
    intro v; constructor
    · intro hv; refine ⟨b.repr ⟨v, hv⟩, ?_⟩
      rw [hf, b.sum_repr]
    · rintro ⟨w, rfl⟩; rw [hf]; exact Submodule.coe_mem _
  have hinj : ∀ w, f *ᵥ w = 0 → w = 0 := by
    intro w hw
    rw [hf] at hw
    have h0 : (∑ j, w j • b j) = 0 := Subtype.ext hw
    funext j
    exact Fintype.linearIndependent_iff.mp b.linearIndependent w h0 j
  have hdet : f.det ≠ 0 := by
    intro h0
    obtain ⟨w, hw0, hw⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    exact hw0 (hinj w hw)
  have hcancel : ∀ X Y : Matrix (Fin d') (Fin d') ℤ_[l], f * X = f * Y → X = Y := by
    intro X Y h
    have h2 := congrArg (fun M => f.adjugate * M) h
    simp only [← Matrix.mul_assoc, Matrix.adjugate_mul] at h2
    apply Matrix.ext
    intro i j
    have h3 := congrFun (congrFun h2 i) j
    simp only [Matrix.smul_mul, Matrix.one_mul, Matrix.smul_apply, smul_eq_mul] at h3
    exact mul_left_cancel₀ hdet h3
  have hcol : ∀ g j, ∃ w, (ρ' g).val *ᵥ (fun i => f i j) = f *ᵥ w := by
    intro g j
    apply (hiff _).mp
    apply mulVec_mem_kerMod (A := (ρ' g).val) (B := (ρ g).val) (hP.equi g)
    exact Submodule.coe_mem (b j)
  choose W hW using hcol
  let R : Γ → Matrix (Fin d') (Fin d') ℤ_[l] := fun g => Matrix.of fun i j => W g j i
  have hR : ∀ g, f * R g = (ρ' g).val * f := by
    intro g
    apply Matrix.ext
    intro i j
    have := congrFun (hW g j) i
    simp only [Matrix.mulVec, dotProduct] at this
    simp only [Matrix.mul_apply, R, Matrix.of_apply]
    exact this.symm
  have hR1 : R 1 = 1 := hcancel _ _ (by rw [hR, map_one, Units.val_one, Matrix.one_mul, Matrix.mul_one])
  have hRm : ∀ g h, R (g * h) = R g * R h := fun g h => hcancel _ _ (by
    rw [hR, map_mul, Units.val_mul, Matrix.mul_assoc, ← hR h, ← Matrix.mul_assoc, ← hR g, Matrix.mul_assoc])
  let Rm : Γ →* Matrix (Fin d') (Fin d') ℤ_[l] := { toFun := R, map_one' := hR1, map_mul' := hRm }
  refine ⟨f, Rm.toHomUnits, hdet, fun g => hR g, fun v => hiff v⟩

end GlobalTheory.KerLat
end

section

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.CoordEx

theorem exists_basis {A B M N : Type} [CommRing A] [CommRing B] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module B N] {f : A →+* B} {u : M →ₛₗ[f] N} (h : SemiBC u) {d : ℕ}
    (e : Module.Basis (Fin d) A M) : ∃ b : Module.Basis (Fin d) B N, ∀ i, b i = u (e i) := by
  let v : M →ₛₗ[f] (Fin d → B) :=
    { toFun := fun x i => f (e.repr x i)
      map_add' := fun x y => by ext i; simp
      map_smul' := fun a x => by ext i; simp }
  obtain ⟨S, hS, -⟩ := h _ v
  let Q : (Fin d → B) →ₗ[B] N := Fintype.linearCombination B fun i => u (e i)
  have hQ : Q.comp S = LinearMap.id := h.hom_ext fun x => by
    rw [LinearMap.comp_apply, hS, LinearMap.id_apply, Fintype.linearCombination_apply]

    conv_rhs => rw [← e.sum_repr x, map_sum]
    exact Finset.sum_congr rfl fun i _ => (u.map_smulₛₗ _ _).symm
  have hv : ∀ i, S (u (e i)) = Pi.single i 1 := fun i => by
    rw [hS]
    ext j
    change f (e.repr (e i) j) = _
    by_cases hij : j = i
    · subst hij; simp
    · simp [hij, Ne.symm hij]
  have hQ1 : ∀ i, Q (Pi.single i 1) = u (e i) := fun i => by
    simp [Q, Fintype.linearCombination_apply_single]
  have hS' : S.comp Q = LinearMap.id := by
    refine (Pi.basisFun B (Fin d)).ext fun i => ?_
    rw [Pi.basisFun_apply, LinearMap.comp_apply, hQ1, hv, LinearMap.id_apply]
  refine ⟨(Pi.basisFun B (Fin d)).map (LinearEquiv.ofLinear Q S hQ hS'), fun i => ?_⟩
  rw [Module.Basis.map_apply, Pi.basisFun_apply, LinearEquiv.ofLinear_apply, hQ1]

theorem equivFun_eq {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] {d : ℕ}
    (b : Module.Basis (Fin d) A M) (y : M) (c : Fin d → A) (h : y = ∑ i, c i • b i) : b.equivFun y = c := by
  rw [h, ← b.equivFun_symm_apply, LinearEquiv.apply_symm_apply]

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (S : Strat bk d) (M : FCrys l ↥(OL K))
    (e : Module.Basis (Fin d) bk.prism.A (M.M bk.prism)), Framed S M e →
    ∀ B : Obj l ↥(OL K), ∃ V : Eval S B (M.M B), IsCoord e V := by
  intro l _ K bk d S M e hF B
  have hb : ∀ (Q : Obj l ↥(OL K)) (g : Hom bk.prism Q), ∃ b : Module.Basis (Fin d) Q.A (M.M Q),
      ∀ i, b i = M.tr g (e i) := fun Q g => exists_basis (M.tr_bc g) e
  choose b hb using hb
  have hs : ∀ (Q : Obj l ↥(OL K)) (g : Hom bk.prism Q) (y : M.M Q),
      y = ∑ i, (b Q g).equivFun y i • M.tr g (e i) := fun Q g y => by
    conv_lhs => rw [← (b Q g).sum_equivFun y]
    exact Finset.sum_congr rfl fun i _ => by rw [hb]
  refine ⟨{ fin := M.fin B
            proj := M.proj B
            v := fun {Q} a g => (b Q g).equivFun.toLinearMap.comp (M.tr a)
            bc := fun {Q} a g => (M.tr_bc a).comp_equiv _
            v_ε := fun {Q} a g g' x => ?_
            v_nat := fun {Q Q'} c a g x i => ?_ }, fun {Q} a g x => hs Q g _⟩
  · change (b Q g).equivFun (M.tr a x) = (S.ε g g').mulVec ((b Q g').equivFun (M.tr a x))
    refine equivFun_eq _ _ _ ?_
    refine (hs Q g' (M.tr a x)).trans ?_
    generalize (b Q g').equivFun (M.tr a x) = c
    simp only [hF.tr g g', Finset.smul_sum, smul_smul, hb, Matrix.mulVec, dotProduct, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm (c j)]
  · change (b Q' (c.comp g)).equivFun (M.tr (c.comp a) x) i = c.f ((b Q g).equivFun (M.tr a x) i)
    refine congrFun (equivFun_eq _ _ (fun i => c.f ((b Q g).equivFun (M.tr a x) i)) ?_) i
    refine (M.tr_comp c a x).trans ((congrArg (M.tr c) (hs Q g (M.tr a x))).trans ?_)
    refine (map_sum (M.tr c) _ _).trans (Finset.sum_congr rfl fun j _ => ?_)
    exact ((M.tr c).map_smulₛₗ _ _).trans
      (congrArg (c.f _ • ·) ((hb Q' (c.comp g) j).trans (M.tr_comp c g (e j))).symm)

end GlobalTheory.BSP.CoordEx
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

private lemma map_quotient_mk_proper_of_le_jacobson {B : Type} [CommRing B] (J 𝔟 : Ideal B) (hJ : 𝔟 ≤ Ideal.jacobson ⊥)
    (h : J ≠ ⊤) : J.map (Ideal.Quotient.mk 𝔟) ≠ ⊤ := by
  intro htop
  obtain ⟨x, hx, hx1⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1
    ((Ideal.eq_top_iff_one _).1 htop)
  have h1 : 1 - x ∈ 𝔟 := by
    rw [← Ideal.Quotient.eq, map_one, hx1]
  have hu := Ideal.mem_jacobson_bot.1 (hJ h1) (-1)
  have hx' : (1 - x) * -1 + 1 = x := by ring
  rw [hx'] at hu
  exact h (Ideal.eq_top_of_isUnit_mem _ hx hu)

theorem faithfullyFlat_quotientMap_of_map_ne_top {A B : Type} [CommRing A] [CommRing B] (f : A →+* B)
    (𝔞 : Ideal A) (𝔟 : Ideal B) (hle : 𝔞 ≤ 𝔟.comap f) (hJ : 𝔟 ≤ Ideal.jacobson ⊥)
    (hfl : (Ideal.quotientMap 𝔟 f hle).Flat) (hm : ∀ 𝔪 : Ideal A, 𝔪.IsMaximal → 𝔪.map f ≠ ⊤) :
    (Ideal.quotientMap 𝔟 f hle).FaithfullyFlat := by
  letI : Algebra (A ⧸ 𝔞) (B ⧸ 𝔟) := (Ideal.quotientMap 𝔟 f hle).toAlgebra
  have hfl' : Module.Flat (A ⧸ 𝔞) (B ⧸ 𝔟) := hfl
  show Module.FaithfullyFlat (A ⧸ 𝔞) (B ⧸ 𝔟)
  refine { toFlat := hfl', submodule_ne_top := fun 𝔫 h𝔫 htop => ?_ }
  rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_eq_top_iff] at htop

  set 𝔪 := 𝔫.comap (Ideal.Quotient.mk 𝔞)
  have hmax : 𝔪.IsMaximal := Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
  have key : (𝔪.map f).map (Ideal.Quotient.mk 𝔟) = ⊤ := by
    rw [Ideal.map_map, ← Ideal.quotientMap_comp_mk hle, ← Ideal.map_map,
      Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]
    exact htop
  exact map_quotient_mk_proper_of_le_jacobson _ _ hJ (hm 𝔪 hmax) key

theorem cover_of_stable_of_map_ne_top : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (B C : Obj l R)
    (h : Hom B C), Stable h → (∀ 𝔪 : Ideal B.A, 𝔪.IsMaximal → 𝔪.map h.f ≠ ⊤) → Cover h := by
  intro l _ R _ B C h hs hm
  refine ⟨hs, fun m => ?_⟩
  rcases m with _ | m
  ·
    haveI : Subsingleton (B.A ⧸ adI B ^ 0) := Ideal.Quotient.subsingleton_iff.2 (by simp)
    rw [RingHom.FaithfullyFlat.iff_flat_and_comap_surjective]
    exact ⟨hs.flat 0, fun p => isEmptyElim p⟩
  · haveI := C.complete
    have hJ : adI C ^ (m + 1) ≤ Ideal.jacobson ⊥ :=
      (Ideal.pow_le_self (Nat.succ_ne_zero m)).trans (IsAdicComplete.le_jacobson_bot (adI C))
    exact faithfullyFlat_quotientMap_of_map_ne_top h.f _ _ (adI_pow_le h (m + 1)) hJ (hs.flat (m + 1)) hm

end GlobalTheory.BSP
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.FrameEq

theorem map_inj {R S : Type} [CommRing R] [CommRing S] {m n : Type} (f : R →+* S) (hf : Function.Injective f)
    {M M' : Matrix m n R} (h : M.map f = M'.map f) : M = M' := by
  ext i j
  exact hf (congrFun (congrFun h i) j)

private theorem padicInt_hom_ext_pt {l : ℕ} [Fact l.Prime] {R : Type} [CommRing R]
    [IsHausdorff (Ideal.span {(l : R)}) R] (f g : ℤ_[l] →+* R) (z : ℤ_[l]) : f z = g z := by
  rw [← sub_eq_zero]
  refine IsHausdorff.haus' (I := Ideal.span {(l : R)}) _ fun n => ?_
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec n z)
  have hz : z = (PadicInt.appr z n : ℤ_[l]) + c * (l : ℤ_[l]) ^ n := by rw [hc]; ring
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton']
  refine ⟨f c - g c, ?_⟩
  rw [hz]
  simp only [map_add (f := _), map_mul, map_pow, map_natCast]
  ring

theorem map_smul_rh {R S : Type} [CommRing R] [CommRing S] {m n : Type} (f : R →+* S) (c : R)
    (M : Matrix m n R) : (c • M).map f = f c • M.map f := by
  ext i j
  simp

theorem frobW_galW {l : ℕ} [Fact l.Prime] (g : GQ l) (x : WCb l) :
    frobW l (galW l g x) = galW l g (frobW l x) := by
  ext n
  simp [frobW, galW, mapAlgEquivW, mapEquivW, WittVector.map_coeff, frobenius_def, map_pow]

theorem cocycle_frob {R : Type} [CommRing R] {d N : ℕ} (fr ga : R →+* R) (hc : ∀ x, fr (ga x) = ga (fr x))
    (e : R) (T A ε Z : Matrix (Fin d) (Fin d) R) (hT : IsUnit T) (hφ : e ^ N • T.map fr = T * A)
    (hgal : Z * T.map ga = T * ε) (hZ : Z.map fr = Z) :
    e ^ N • (ε * A.map ga) = ga e ^ N • (A * ε.map fr) := by
  have h1 : ga e ^ N • T.map (fun x => ga (fr x)) = T.map ga * A.map ga := by
    have := congrArg (fun M => M.map ga) hφ
    simp only [map_smul_rh, Matrix.map_mul, Matrix.map_map, map_pow] at this
    exact this
  have h2 : Z * T.map (fun x => ga (fr x)) = T.map fr * ε.map fr := by
    have := congrArg (fun M => M.map fr) hgal
    simp only [Matrix.map_mul, Matrix.map_map, hZ] at this
    have e2 : T.map (fun x => ga (fr x)) = T.map (⇑fr ∘ ⇑ga) := by
      ext i j; simp [hc]
    rw [e2]; exact this
  apply hT.mul_left_cancel
  calc T * (e ^ N • (ε * A.map ga)) = e ^ N • (T * ε * A.map ga) := by
        rw [Matrix.mul_smul, Matrix.mul_assoc]
    _ = e ^ N • (Z * (ga e ^ N • T.map (fun x => ga (fr x)))) := by
        rw [h1, ← hgal, Matrix.mul_assoc]
    _ = ga e ^ N • ((e ^ N • T.map fr) * ε.map fr) := by
        rw [Matrix.mul_smul, smul_smul, mul_comm, ← smul_smul, h2, Matrix.smul_mul]
    _ = T * (ga e ^ N • (A * ε.map fr)) := by
        rw [hφ, Matrix.mul_smul, Matrix.mul_assoc]


open GlobalTheory.FrameEq in
theorem frame_Y_eqs : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (N d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (F : Frame bk N d ρ) (Y Y' : Matrix (Fin d) (Fin d) (Ainf l)), Y.map (inclW l) = inclW l τ ^ N • F.T → Y * Y' = τ ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (Ainf l)) → Y.map WittVector.frobenius = Y * F.A.map bk.ev ∧ (∀ g : ↥(GK K), τ ^ N • ((ρ g).map (Per.zA l) * Y.map (Per.σA (g : GQ l))) = Per.σA (g : GQ l) τ ^ N • (Y * F.ε g)) ∧ ∀ g : ↥(GK K), bk.ev bk.E ^ N • (F.ε g * F.A.map (fun s => Per.σA (g : GQ l) (bk.ev s))) = Per.σA (g : GQ l) (bk.ev bk.E) ^ N • (F.A.map bk.ev * (F.ε g).map WittVector.frobenius) := by
  intro l _ K bk τ hτ N d ρ F Y Y' hY _
  have hev : ∀ s, inclW l (bk.ev s) = bk.evW s := fun s => rfl
  have hz : ∀ z : ℤ_[l], inclW l (Per.zA l z) = algebraMap ℤ_[l] (WCb l) z := fun z => by
    rw [← (inclWA l).commutes z, padicInt_hom_ext_pt (Per.zA l) (algebraMap ℤ_[l] (Ainf l)) z]; rfl
  refine ⟨?_, ?_, ?_⟩
  · apply map_inj (inclW l) inclW_injective
    have e1 : (Y.map WittVector.frobenius).map (inclW l) = (Y.map (inclW l)).map (frobW l) := by
      ext i j; simp [frobW_inclW]
    rw [e1, Matrix.map_mul, hY]
    have e2 : (F.A.map bk.ev).map (inclW l) = F.A.map bk.evW := by ext i j; simp [hev]
    rw [e2, Matrix.smul_mul, ← F.φ]
    have e3 : ((inclW l τ ^ N) • F.T).map (frobW l) = frobW l (inclW l τ) ^ N • F.T.map (frobW l) := by
      ext i j; simp
    rw [e3, frobW_inclW, hτ.1, map_mul, hev, smul_smul, mul_pow, mul_comm]
  · intro g
    apply map_inj (inclW l) inclW_injective
    have e1 : (Y.map (Per.σA (g : GQ l))).map (inclW l) = (Y.map (inclW l)).map (galW l (g : GQ l)) := by
      ext i j; simp [galW_inclW]
    have e2 : ((ρ g).map (Per.zA l)).map (inclW l) = zW (ρ g) := by ext i j; simp [hz]
    rw [map_smul_rh, map_smul_rh, Matrix.map_mul, Matrix.map_mul, e1, e2, hY]
    have e3 : ((inclW l τ ^ N) • F.T).map (galW l (g : GQ l)) =
        galW l (g : GQ l) (inclW l τ) ^ N • F.T.map (galW l (g : GQ l)) := by
      ext i j; simp
    rw [e3, galW_inclW, Matrix.mul_smul, F.gal, map_pow, map_pow, smul_smul, Matrix.smul_mul, smul_smul, mul_comm]
  · intro g
    apply map_inj (inclW l) inclW_injective
    have key := cocycle_frob (frobW l).toRingHom (galW l (g : GQ l)).toRingEquiv.toRingHom
      (fun x => frobW_galW (g : GQ l) x) (bk.evW bk.E) F.T (F.A.map bk.evW) ((F.ε g).map (inclW l)) (zW (ρ g))
      F.unit F.φ (F.gal g) (by ext i j; simp [zW])
    rw [map_smul_rh, map_smul_rh, Matrix.map_mul, Matrix.map_mul, map_pow, map_pow, hev]
    have e1 : (F.A.map (fun s => Per.σA (g : GQ l) (bk.ev s))).map (inclW l) =
        (F.A.map bk.evW).map (galW l (g : GQ l)).toRingEquiv.toRingHom := by
      refine Matrix.ext fun i j => ?_
      simp only [Matrix.map_apply]
      show _ = galW l (g : GQ l) (bk.evW (F.A i j))
      rw [← hev, galW_inclW]
    have e2 : ((F.ε g).map WittVector.frobenius).map (inclW l) = ((F.ε g).map (inclW l)).map (frobW l).toRingHom := by
      ext i j; simp [frobW_inclW]
    have e3 : (F.A.map bk.ev).map (inclW l) = F.A.map bk.evW := by ext i j; simp [hev]
    rw [e1, e2, e3, ← galW_inclW, hev]
    exact key

end GlobalTheory.FrameEq
end
end
