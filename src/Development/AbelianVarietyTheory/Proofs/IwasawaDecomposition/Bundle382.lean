module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle015
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle360
public import Formalism.SharpRestriction.GlobalSchurBounds.Joints
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle373
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianSideClassesEqFormClasses
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.KerEntHyp
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle363
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle016
public import Formalism.LocalToGlobal.HermitianColumns.Bundle005
public import Formalism.LocalToGlobal.HermitianForms.Bundle006
public import Formalism.LocalToGlobal.KernelLattices.Bundle001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle355
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LastAllTranspose
import Formalism.LocalToGlobal.HermitianForms.Bundle004
public import Formalism.LocalToGlobal.HermitianForms.Bundle009
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle359
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSmulLk
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.HAt Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.exists_diamond_elements_step_levels : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → ∀ u i (hi : i ≤ (I.rec7 l Z).R.m) v (a : (((I.rec7 l Z).mem u).A.Fv v)ˣ), ∃ k : ℤ, (k : ((I.rec7 l Z).mem u).A.Fv v) = a ∧ (∀ h : i = 0 ∨ i = (I.rec7 l Z).R.m, ∃ δ, IsDia ((F u).cls i hi h).lev ((F u).atT.eV v).1 ((F u).atT.eV v).2 k δ) ∧ ∀ (h1 : 1 ≤ i) (h2 : i + 1 ≤ (I.rec7 l Z).R.m) (β : H.Ch u i), ∃ δ, IsDia ((F u).ch i h1 h2 β).lev ((F u).atT.eV v).1 ((F u).atT.eV v).2 k δ := by
  first | exact @GlobalTheory.Mem.Col2.HAt.exists_isDia_steps | exact GlobalTheory.Mem.Col2.HAt.exists_isDia_steps | (intros; apply GlobalTheory.Mem.Col2.HAt.exists_isDia_steps <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.TC

theorem base_sup_dual_eq {E : Type} [Field E] [NumberField E] (σ : E →+* E) {n : ℕ}
    (Lb M : Submodule (𝓞 E) (Fin n → E)) (π pb : 𝓞 E) (hpb : (pb : E) = σ (π : E))
    (hspan : Submodule.span E (Lb : Set (Fin n → E)) = ⊤)
    (hL : ∀ x, x ∈ Lb ↔ ∀ j : Fin n, ∃ r : 𝓞 E, x j = (r : E) ∧ (j.1 + 1 = n → π ∣ r))
    (hM : ∀ x, x ∈ M ↔ ∀ j, x j ∈ (algebraMap (𝓞 E) E).range) :
    Lb ⊔ Ideal.span {pb} • Submodule.span (𝓞 E) (dualSet σ (1 : Matrix (Fin n) (Fin n) E) Lb) = M := by
  have hform1 : ∀ x y : Fin n → E, hform σ (1 : Matrix (Fin n) (Fin n) E) x y = ∑ i, σ (x i) * y i := by
    intro x y
    unfold hform
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Matrix.one_apply]
  have hσO : ∀ r : 𝓞 E, σ (r : E) ∈ (algebraMap (𝓞 E) E).range := fun r =>
    ⟨⟨σ (r : E), map_isIntegral_int σ (RingOfIntegers.isIntegral_coe r)⟩, rfl⟩
  apply le_antisymm
  · refine sup_le ?_ ?_
    · intro x hx
      refine (hM x).2 fun j => ?_
      obtain ⟨r, hr, -⟩ := (hL x).1 hx j
      exact ⟨r, hr.symm⟩
    · rw [Submodule.ideal_span_singleton_smul]
      rintro _ ⟨y, hy, rfl⟩
      simp only [DistribSMul.toLinearMap_apply]
      induction hy using Submodule.span_induction with
      | mem y hy =>
        refine (hM _).2 fun j => ?_
        by_cases hj : j.1 + 1 = n
        · have hx : Pi.single j (π : E) ∈ Lb := by
            refine (hL _).2 fun i => ?_
            by_cases h : i = j
            · subst h
              exact ⟨π, by simp, fun _ => dvd_rfl⟩
            · exact ⟨0, by simp [h], fun _ => dvd_zero _⟩
          have := hy _ hx
          rw [hform1, Finset.sum_eq_single j (by intro b _ hb; simp [hb]) (by simp)] at this
          simpa [Algebra.smul_def, hpb] using this
        · have hx : Pi.single j (1 : E) ∈ Lb := by
            refine (hL _).2 fun i => ?_
            by_cases h : i = j
            · subst h
              exact ⟨1, by simp, fun hi => absurd hi hj⟩
            · exact ⟨0, by simp [h], fun _ => dvd_zero _⟩
          have := hy _ hx
          rw [hform1, Finset.sum_eq_single j (by intro b _ hb; simp [hb]) (by simp)] at this
          simp only [Pi.single_eq_same, map_one, one_mul] at this
          obtain ⟨r, hr⟩ := this
          exact ⟨pb * r, by simp [Algebra.smul_def, hr]⟩
      | zero => simp
      | add y z _ _ h1 h2 => rw [smul_add]; exact M.add_mem h1 h2
      | smul c y _ h => rw [smul_comm]; exact M.smul_mem c h
  · intro x hx
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact (le_sup_left : Lb ≤ _) ((hL x).2 fun j => j.elim0)
    have hxi := (hM x).1 hx
    let l : Fin n := ⟨n - 1, by omega⟩
    have hl : l.1 + 1 = n := by simp [l]; omega
    have hπ : π ≠ 0 := by
      rintro rfl
      have hle : Submodule.span E (Lb : Set (Fin n → E)) ≤ LinearMap.ker (LinearMap.proj (R := E) (φ := fun _ : Fin n => E) l) := by
        refine Submodule.span_le.2 fun z hz => ?_
        obtain ⟨r, hr, hd⟩ := (hL z).1 hz l
        have : r = 0 := zero_dvd_iff.1 (hd hl)
        simp [hr, this]
      rw [hspan] at hle
      have := hle (Submodule.mem_top (x := Pi.single l (1 : E)))
      simp at this
    have hpb0 : (pb : E) ≠ 0 := by
      rw [hpb]
      intro h
      exact hπ (by simpa using (map_eq_zero σ).1 h)
    obtain ⟨t, ht⟩ := hxi l
    have hy : Pi.single l (x l / (pb : E)) ∈ dualSet σ (1 : Matrix (Fin n) (Fin n) E) Lb := by
      intro z hz
      rw [hform1, Finset.sum_eq_single l (by intro b _ hb; simp [hb]) (by simp)]
      obtain ⟨r, hr, hd⟩ := (hL z).1 hz l
      obtain ⟨s, rfl⟩ := hd hl
      obtain ⟨w, hw⟩ := hσO s
      refine ⟨w * t, ?_⟩
      rw [map_mul, hw, ht, hr, Pi.single_eq_same]
      simp only [map_mul, ← hpb]
      rw [← ht]
      field_simp
    have hx' : Function.update x l 0 ∈ Lb := by
      refine (hL _).2 fun j => ?_
      by_cases h : j = l
      · subst h
        exact ⟨0, by simp, fun _ => dvd_zero _⟩
      · obtain ⟨r, hr⟩ := hxi j
        refine ⟨r, by simp [h, hr], fun hj => absurd (Fin.ext (by simp [l]; omega)) h⟩
    have hx'' : Pi.single l (x l) ∈ Ideal.span {pb} • Submodule.span (𝓞 E) (dualSet σ (1 : Matrix (Fin n) (Fin n) E) Lb) := by
      rw [Submodule.ideal_span_singleton_smul]
      refine ⟨_, Submodule.subset_span hy, ?_⟩
      funext j
      by_cases h : j = l
      · subst h
        simp [Algebra.smul_def, mul_div_cancel₀ _ hpb0]
      · simp [h]
    refine Submodule.mem_sup.2 ⟨_, hx', _, hx'', ?_⟩
    funext j
    by_cases h : j = l
    · subst h
      simp
    · simp [h]

end GlobalTheory.Mem.Col2.TC

namespace GlobalTheory.Mem.Col2.TC



theorem base_step_zero_tied : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)) (A : ∀ u, Formalism.L2.Herm.AtT (I.rec7 l Z) u (H.vT u) (H.Fv u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → CarT H F A → ∀ u (pb : 𝓞 (I.rec7 l Z).host.E), (pb : (I.rec7 l Z).host.E) = (I.rec7 l Z).host.conj ((A u).piU : (I.rec7 l Z).host.E) → (H.lev0 u).Lb ⊔ Ideal.span {pb} • Submodule.span (𝓞 (I.rec7 l Z).host.E) (dualSet ((I.rec7 l Z).sp.cm.sig : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E) (I.rec7 l Z).sp.gram0 (H.lev0 u).Lb) = (I.rec7 l Z).sp.crdLat0 ((I.rec7 l Z).sp.X 0).L0 := by
  intro B X I hI hP l Z H F A hS hH hT u pb hpb
  obtain ⟨-, -, -, hN⟩ := GlobalTheory.T.trueColumn_spaces_standard_in_frameCoords I hI hP l Z
  obtain ⟨hgram, hl0, -⟩ := hN 0 (Nat.zero_le _)
  have hgram0 : (I.rec7 l Z).sp.gram0 = 1 := by
    refine Matrix.ext fun a b => ?_
    have := congrFun (congrFun hgram (Fin.cast (rank_eq_first_level (I.rec7 l Z).R) a)) (Fin.cast (rank_eq_first_level (I.rec7 l Z).R) b)
    have e : (Fin.cast (rank_eq_first_level (I.rec7 l Z).R) a = Fin.cast (rank_eq_first_level (I.rec7 l Z).R) b) ↔ a = b := by simp [Fin.ext_iff]
    simp only [Matrix.one_apply, e] at this
    rw [Matrix.one_apply]
    exact this
  rw [hgram0]
  obtain ⟨k, hk⟩ := (hS u).1.ends 0 (Nat.zero_le _) (Or.inl rfl)
  have hLb := (hH.car0 u).Lb_eq
  have hπ : (A u).piU = X.piT u := (hT.piU u).symm.trans (hS u).1.piU
  refine base_sup_dual_eq _ _ _ (X.piT u) pb ?_ (H.lev0 u).Lb_span ?_ ?_
  · have e := congrArg (fun t : 𝓞 B.host.E => (t : B.host.E)) hπ
    exact hpb.trans ((congrArg (I.rec7 l Z).host.conj e).trans (Formalism.MainNotions.GlobalTheoryTheory.jnt_sig_eq_conj (I.rec7 l Z) _).symm)
  · intro x
    have e1 : x ∈ (H.lev0 u).Lb ↔ reV (rank_eq_first_level (I.rec7 l Z).R) _ x ∈ ((F u).cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.Lb := by
      rw [hLb]
      constructor
      · exact fun h => ⟨x, h, rfl⟩
      · rintro ⟨y, hy, e⟩
        have : y = x := (reV (rank_eq_first_level (I.rec7 l Z).R) _).injective e
        exact this ▸ hy
    refine e1.trans ((hk.lb () _).trans ?_)
    constructor
    · intro h j
      obtain ⟨r, hr, hd⟩ := h (Fin.cast (rank_eq_first_level (I.rec7 l Z).R) j)
      exact ⟨r, hr, fun hj => hd (hj.trans (rank_eq_first_level _))⟩
    · intro h j
      obtain ⟨r, hr, hd⟩ := h (Fin.cast (rank_eq_first_level (I.rec7 l Z).R).symm j)
      exact ⟨r, hr, fun hj => hd (hj.trans (rank_eq_first_level _).symm)⟩
  · intro x
    have e1 : (fun j => x (Fin.cast (rank_eq_first_level (I.rec7 l Z).R).symm j)) ∈ selfDualLatticeCoords (I.rec7 l Z) 0 (Nat.zero_le _) ↔
        x ∈ (I.rec7 l Z).sp.crdLat0 ((I.rec7 l Z).sp.X 0).L0 := by
      constructor
      · rintro ⟨v, hv, e⟩
        refine ⟨v, hv, ?_⟩
        funext a
        exact congrFun e (Fin.cast (rank_eq_first_level (I.rec7 l Z).R) a)
      · rintro ⟨v, hv, e⟩
        refine ⟨v, hv, ?_⟩
        funext j
        exact congrFun e (Fin.cast (rank_eq_first_level (I.rec7 l Z).R).symm j)
    refine e1.symm.trans ((hl0 _).trans ?_)
    exact ⟨fun h j => h (Fin.cast (rank_eq_first_level (I.rec7 l Z).R) j), fun h j => h (Fin.cast (rank_eq_first_level (I.rec7 l Z).R).symm j)⟩

end GlobalTheory.Mem.Col2.TC
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.HAt Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.stabiliserMap_hyperplane_eq_conj_classMap : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → ∀ (A : ∀ u, Formalism.L2.Herm.AtT (I.rec7 l Z) u (H.vT u) (H.Fv u)), CarT H F A → Formalism.L2.Herm.SymmetricStabilizerMapCompatibility (I.rec7 l Z) H A := by
  first | exact @GlobalTheory.Mem.Col2.HAt.Stab.stabMap_tied | exact GlobalTheory.Mem.Col2.HAt.Stab.stabMap_tied | (intros; apply GlobalTheory.Mem.Col2.HAt.Stab.stabMap_tied <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.HAt Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.hermitianSide_classes_eq_formClasses : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → ∀ u, ∃ (lattice₂ : ((I.rec7 l Z).fm u).clsP → Submodule (𝓞 (I.rec7 l Z).host.E) (I.rec7 l Z).sp.X'.V) (levP : Formalism.L2.Herm.StepLevel0 (I.rec7 l Z).sp.cm (I.rec7 l Z).sp.X' (I.rec7 l Z).host.g (Formalism.L2.Herm.crdLat (I.rec7 l Z).sp.X' (I.rec7 l Z).sp.X'.L0)) (clsP : Formalism.L2.Herm.ClassTie (I.rec7 l Z).sp.cm (I.rec7 l Z).sp.X' (Formalism.L2.Herm.crdLat (I.rec7 l Z).sp.X' (I.rec7 l Z).sp.X'.L0) levP.U ((I.rec7 l Z).fm u).stabilizer₂ lattice₂), SameCar (rankP (I.rec7 l Z)) (Formalism.L2.Herm.crdLat (I.rec7 l Z).sp.X' (I.rec7 l Z).sp.X'.L0) (F u).clsP.lev.Lb levP.Uloc (F u).clsP.lev.Uloc levP.U (F u).clsP.lev.U (fun c => (clsP.y c).1) (fun c => ((F u).clsP.y c).1) (fun c s => (clsP.stabI c s).1) (fun c s => ((F u).clsP.stabI c s).1) ∧ ∀ c, (F u).clsP.lat c = (lattice₂ c).map ((crdP (I.rec7 l Z) : (I.rec7 l Z).sp.X'.V →ₗ[(I.rec7 l Z).host.E] (Fin ((I.rec7 l Z).R.N (I.rec7 l Z).R.m - 1) → (I.rec7 l Z).host.E)).restrictScalars (𝓞 (I.rec7 l Z).host.E)) := by
  first | exact @GlobalTheory.Mem.Col2.HAt.clsP_hermitian | exact GlobalTheory.Mem.Col2.HAt.clsP_hermitian | (intros; apply GlobalTheory.Mem.Col2.HAt.clsP_hermitian <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.sectionPolynomial_eq_of_function_eq_coefficient : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (Qp : I.ι → Finset ℕ) (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)), I.StdO l Z Qp O → ∀ (u : B.Word) (μ : I.ι) (i : ℕ), i < (I.rec7 l Z).R.m → ∀ (z : VV B.LL (lamT (B.hcW u) (i + 1))) (v' : ValQ O u μ (i + 1)), evC O u μ (i + 1) v' = evV B.fields.emb (1 : Matrix (Fin (B.R.N (i + 1))) (Fin (B.R.N (i + 1))) B.fields.E) (lamT (B.hcW u) (i + 1)) B.embLL z → ((secC O u μ (i + 1) v' : MvPolynomial (GL3Theta.FrV (I.rec7 l Z) ((I.rec7 l Z).R.N (i + 1))) (I.rec7 l Z).what₂.LL)) = (show MvPolynomial (GL3Theta.FrV (I.rec7 l Z) ((I.rec7 l Z).R.N (i + 1))) (I.rec7 l Z).what₂.LL from z.1) := by
  first | exact @GlobalTheory.Mem.Col2.PolyId.secC_eq_of_evC_eq_evV | exact GlobalTheory.Mem.Col2.PolyId.secC_eq_of_evC_eq_evV | (intros; apply GlobalTheory.Mem.Col2.PolyId.secC_eq_of_evC_eq_evV <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.complexValue_det_shift_mul_ratSpan : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (Y : DivX (I.rec7 l Z)) (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)), I.QpIs Y.Qp → I.StdO l Z Y.Qp O → ∀ (u : B.Word) (μ : I.ι) (i : ℕ) (hi : i < B.R.m) (eY : (I.chain l u μ).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi.le), I.IdY l Z u μ i hi.le eY → ∀ v : ValQ O u μ i, ∃ P ∈ Formalism.L2.Forms.RatSpan (I.rec7 l Z) ((I.fm l u μ).lam i), ∀ z, evC O u μ i v z = fnOf (gramC (gramN (I.rec7 l Z) i hi.le) (embT (I.rec7 l Z))) (shiftOf (lamTG (I.fm l u μ) i)) 1 P (eY z) := by
  first | exact @GlobalTheory.KerValRat.evC_ratSpan | exact GlobalTheory.KerValRat.evC_ratSpan | (intros; apply GlobalTheory.KerValRat.evC_ratSpan <;> assumption)
end

section

noncomputable section
namespace GlobalTheory.HeightCounting
open Formalism.BasicNotions Formalism.MainNotions.N Formalism.L2.Host GlobalTheory.CuspRep NumberField IsDedekindDomain




def trueK (hL : GlobalTheory.Published.LocalLanglandsGL) (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL) (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut)
    (η η' : HostCGu D.host 1)
    (h1 : ∀ w, (ParLaws.locG hL D.nd.plOm η w).unr)
    (h2 : ∀ w, ¬ IsSplitPl D.host w → (ParLaws.locG hL D.nd.plOm η w).frobEig = {-1})
    (h3 : ∀ w, (ParLaws.locG hL D.nd.plOm η' w).unr ∧ (ParLaws.locG hL D.nd.plOm η' w).frobEig = (ParLaws.locG hL D.nd.plOm η w).frobEig.map (·⁻¹))
    (h4 : ∀ w w', IsSplitPl D.host w → IsConjPl D.host w w' → ∀ a b : ℂ, (ParLaws.locG hL D.nd.plOm η w).frobEig = {a} →
      (ParLaws.locG hL D.nd.plOm η w').frobEig = {b} → a * b = 1) : CGK D.naut :=
  haveI := host_isCMField D.host
  have L := ParLaws.laws hL hF D.host D.nd.Om D.nd.plOm
  have U : ∀ {a} (π : HostCGu D.host a) w, D.naut.unr ((T.e w).symm (ParLaws.locG hL D.nd.plOm π w)) ↔ (ParLaws.locG hL D.nd.plOm π w).unr :=
    fun π w => by rw [T.unr, Equiv.apply_symm_apply]
  have Fr : ∀ {a} (π : HostCGu D.host a) w, (ParLaws.locG hL D.nd.plOm π w).unr →
      D.naut.frobEig ((T.e w).symm (ParLaws.locG hL D.nd.plOm π w)) = (ParLaws.locG hL D.nd.plOm π w).frobEig :=
    fun π w h => by rw [T.frobEig _ _ ((U π w).2 h), Equiv.apply_symm_apply]
  have Dm : ∀ {a} (π : HostCGu D.host a) w, D.naut.lpDim ((T.e w).symm (ParLaws.locG hL D.nd.plOm π w)) = a :=
    fun π w => by rw [← T.dim, Equiv.apply_symm_apply]; exact L.1 π w
  { CG := fun a => {_π : HostCGu D.host a // 0 < a}
    csd := fun π => π.1.IsCsd
    ralg := fun π => π.1.IsRegAlg
    locG := fun π w => (T.e w).symm (ParLaws.locG hL D.nd.plOm π.1 w)
    locG_dim := fun π w => Dm π.1 w
    locG_unr_ae := fun π => (L.2.1 π.1).mono fun w h => (U π.1 w).2 h
    tw := fun π χ => ⟨π.1.tw χ.1, π.2⟩
    locG_tw := fun π χ w => (T.e w).injective (by
      rw [T.char _ _ _ (Dm χ.1 w), Equiv.apply_symm_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
      exact L.2.2.1 π.1 χ.1 w)
    infG := fun π τ => π.1.infChar τ
    infG_card := fun π => L.2.2.2.1 π.1
    ralg_def := fun π => L.2.2.2.2.1 π.1
    infG_tw := fun π χ => L.2.2.2.2.2.1 π.1 χ.1
    csd_tw := fun π χ => L.2.2.2.2.2.2.1 π.1 χ.1
    csd_unr := fun π w w' hπ hc hu => by
      have h := L.2.2.2.2.2.2.2.1 π.1 w w' hπ hc ((U π.1 w).1 hu)
      exact ⟨(U π.1 w').2 h.1, by rw [Fr π.1 w' h.1, Fr π.1 w ((U π.1 w).1 hu)]; exact h.2⟩
    etaT := ⟨η, one_pos⟩
    etaTinv := ⟨η', one_pos⟩
    etaT_unr := fun w => (U η w).2 (h1 w)
    etaT_inert := fun w h => by rw [Fr η w (h1 w)]; exact h2 w h
    etaTinv_def := fun w => ⟨(U η' w).2 (h3 w).1, by rw [Fr η' w (h3 w).1, Fr η w (h1 w)]; exact (h3 w).2⟩
    etaT_split := fun w w' hs hc a b ha hb => by
      rw [Fr η w (h1 w)] at ha; rw [Fr η w' (h1 w')] at hb; exact h4 w w' hs hc a b ha hb }




def trueCG (hL hF) (D : D7) (hE : IsEmpty D.nd.Loc) (T : GlobalTheory.RowTie.WDTie D.nd D.naut) (η η' h1 h2 h3 h4) :
    CGTrue hL (setCG D hE (trueK hL hF D T η η' h1 h2 h3 h4)) (wdCG hE _ T) where
  e := fun _ => Function.Embedding.subtype _
  surj := fun _ h π => ⟨⟨π, h⟩, rfl⟩
  zero := ⟨fun π => lt_irrefl 0 π.2⟩
  loc := fun _ _ w => (T.e w).apply_symm_apply _
  tw := fun _ _ _ => rfl
  inf := fun _ _ _ => rfl
  csd := fun _ _ => Iff.rfl

end GlobalTheory.HeightCounting
end
end

section

noncomputable section

namespace GlobalTheory.Mem.SRe.ColRe

open Formalism.BasicNotions Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.SRe NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (Z : New D)



def hermRe (H : Formalism.L2.Herm.ColsHermS D) : Formalism.L2.Herm.ColsHermS (reD D Z) :=
  { H with
    base := { H.base with }
    atT := fun u => { H.atT u with }
    ad := { H.ad with } }

end GlobalTheory.Mem.SRe.ColRe

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar



namespace GlobalTheory.Mem.Col2.LowerTie

theorem lowerMap_tw_gen {B : Base} {X : PreX B.toPre} (I : TC B X) (hO : I.Ok) (hP : TC.Pins B X) (l : I.Laws) (Z : TC.Later B (I.cols l))
    (l0 : I.Law0 l) {cf : Formalism.L2.Host.CharFrame (I.rec7 l Z)} {nch : NChoice (I.rec7 l Z)}
    {tp : Formalism.L2.Host.TupTied (I.rec7 l Z) cf nch} {C : ColsTiedSym (I.rec7 l Z)} {Tw : TwForms (I.rec7 l Z)}
    (t : SymmetricTwistedColumnsAtPrimes tp C Tw) (he : Tw = I.tw l l0 Z) (hC : I.StdC l Z C) (hTw : I.StdTw l Z l0 (he ▸ t))
    (u : (I.rec7 l Z).what₂.Word) (a : (I.rec7 l Z).what₂.Tup) (ha : a ≠ (I.rec7 l Z).what₂.mu0) (h1 : 1 ≤ (I.rec7 l Z).R.m) :
    IsUnit (Formalism.L2.Forms.bZ u (t.pt.til u a ha h1).z0).det → ∀ (ψ : ((I.rec7 l Z).PTw u a).Wz) (c : (Tw.fm u a).clsP)
      (P : MvPolynomial ((I.rec7 l Z).what₂.Tau × Fin ((I.rec7 l Z).R.N (I.rec7 l Z).R.m) × Fin ((I.rec7 l Z).R.N (I.rec7 l Z).R.m)) ℂ),
      P ∈ Formalism.L2.Forms.CSpan (((I.rec7 l Z).fm u).lam (I.rec7 l Z).R.m) →
      (∀ s, t.ptE.eWz u a ψ c s =
        Formalism.L2.Forms.fnOf _ (Formalism.L2.Forms.shiftOf (Formalism.L2.Forms.lamT u (I.rec7 l Z).R.m)) (Formalism.L2.Forms.mZ u (t.pt.til u a ha h1).z0) P
          (Formalism.L2.Forms.twYS t.ch C.forms u a (I.rec7 l Z).R.m le_rfl s)) →
      (t.pt.val u a ha).eW (((I.rec7 l Z).PTw u a).lowerMap ψ) c =
        Formalism.L2.Forms.fnOf _ (Formalism.L2.Forms.shiftOf (Formalism.L2.Forms.sgT u)) 1 (Formalism.L2.Ker.brTen (I.rec7 l Z) u P) := by

  subst he
  obtain ⟨hW, hLv, hPd⟩ := hTw
  intro _ ψ c P _ hψ
  have hS := hC u
  have hPd' : I.StdP l Z l0 t.pt t.ptE := hPd
  have hW' : I.StdW l Z l0 t.forms := hW
  have hl : Formalism.MainNotions.product_first_zeroth_parts.lamTr (I.rec7 l Z) u = B.wts.lamTrue u B.R.m := funext (trueWeight_lastStep_trueColumns I l Z u)
  have hs : Formalism.MainNotions.product_first_zeroth_parts.sgTr (I.rec7 l Z) u = B.wts.sgTrue := funext (trueRowWeight_trueColumns I l Z u)
  have hl' : Formalism.L2.Forms.lamT (D := I.rec7 l Z) u (I.rec7 l Z).R.m = B.wts.lamTrue u B.R.m := hl
  have hs' : Formalism.L2.Forms.sgT (D := I.rec7 l Z) u = B.wts.sgTrue := hs
  have hI : ∀ τ i, 0 ≤ Br.bBr (N_m_succ B.R) (B.wts.lamTrue u B.R.m τ) (B.wts.sgTrue τ) i := by
    intro τ i
    have h := (Formalism.MainNotions.product_first_zeroth_parts.interlaceTr (I.rec7 l Z) u (sg_interlace (C.forms u).valP) τ i).1
    rw [hl, hs] at h
    exact sub_nonneg.2 h
  have h1' : ψ c = fnOf (Col2.Gr B.fields.emb B.embLL (B.R.N B.R.m)) (shiftOf (B.wts.lamTrue u B.R.m)) 1
      (actP (B.wts.lamTrue u B.R.m) (lastAll (B.R.N B.R.m) (aT I l u)) P) := by
    refine Eq.trans ?_ (fnOf_lastAll (Col2.Gr B.fields.emb B.embLL (B.R.N B.R.m)) (B.wts.lamTrue u B.R.m) (aT I l u) P)
    funext s
    have h := hψ s
    rw [hPd'.eWz, hl', hPd'.z0 u a ha h1, mZ_std I l Z u hO hP (TC.z0 X u) (fun j => rfl)] at h
    refine h.trans ?_
    have h2 : (Formalism.L2.Forms.twYS t.ch C.forms u a (I.rec7 l Z).R.m le_rfl s).1 = s.1 := by
      simp only [Formalism.L2.Forms.twYS, Equiv.trans_apply, hW'.eY, Equiv.refl_symm, Equiv.refl_apply]
      rw [Formalism.L2.Forms.eYS_end _ _ _ (Or.inr rfl)]
      exact hS.eY B.R.m le_rfl (Or.inr rfl) s
    exact congrArg (fnOf (Col2.Gr B.fields.emb B.embLL (B.R.N B.R.m)) (shiftOf (B.wts.lamTrue u B.R.m)) _ P) (Subtype.ext h2)
  have h3 : polOf (Col2.Gr B.fields.emb B.embLL (B.R.N B.R.m)) (shiftOf (B.wts.lamTrue u B.R.m)) (Col2.fr0 B.fields.emb B.embLL (B.R.N B.R.m)) (ψ c) =
      actP (B.wts.lamTrue u B.R.m) (lastAll (B.R.N B.R.m) (aT I l u)) P := by
    have e : (fun τ => ((Col2.fr0 B.fields.emb B.embLL (B.R.N B.R.m)).1 τ)⁻¹) = 1 := funext fun τ => inv_one
    have h := polOf_fnOf (Col2.Gr B.fields.emb B.embLL (B.R.N B.R.m)) (shiftOf (B.wts.lamTrue u B.R.m)) (Col2.fr0 B.fields.emb B.embLL (B.R.N B.R.m))
      (actP (B.wts.lamTrue u B.R.m) (lastAll (B.R.N B.R.m) (aT I l u)) P)
    rw [e] at h
    rw [h1']
    exact h
  have h4 : Formalism.L2.Ker.brTen (I.rec7 l Z) u P = (Br.brStdP (N_m_succ B.R) (B.wts.lamTrue u B.R.m) B.wts.sgTrue P : Pol ℂ (Tau B.R) (B.R.N B.R.m - 1)) := by
    have h := blk_brOne (ι := Tau B.R) (N_m_succ B.R) (B.wts.lamTrue u B.R.m) B.wts.sgTrue P
    refine Eq.trans ?_ h
    unfold Formalism.L2.Ker.brTen
    rw [hl, hs]
    rfl
  have h5 := branchingProjection_act_last (N_m_succ B.R) (B.wts.lamTrue u B.R.m) B.wts.sgTrue hI (aT I l u) P
  funext s
  rw [hPd'.eW u a ha _ c s ⟨s.1, s.2⟩ rfl, hs', h4, ← h5, ← h3]
  rfl

end GlobalTheory.Mem.Col2.LowerTie
end

section

noncomputable section

namespace GlobalTheory.Mem.SRe.ColRe

open Formalism.BasicNotions Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.SRe NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (Z : New D)



def formsRe {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i} (T : FormsTiedSym D u Ch chOf) :
    FormsTiedSym (reD D Z) u Ch chOf :=
  { T with
    atT := { T.atT with }
    cls := fun i hi h => { T.cls i hi h with }
    val := fun i hi h => { T.val i hi h with }
    lv := fun i hi => { T.lv i hi with }
    ch := fun i h1 h2 β => { T.ch i h1 h2 β with }
    valC := fun i h1 h2 => { T.valC i h1 h2 with }
    dilC := fun i h1 h2 => { T.dilC i h1 h2 with }
    lvC := fun i h1 h2 => { T.lvC i h1 h2 with }
    clsP := { T.clsP with }
    valP := { T.valP with }
    til := { T.til with }
    tilAd := { T.tilAd with } }

end GlobalTheory.Mem.SRe.ColRe

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.UG.P Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix

theorem _root_.GlobalTheory.T.couplingCosetInFrames_rational_action_eq : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (u : B.Word) (a : I.ι) (j : ℕ) (b : (I.stp u a j).β) (x : (I.stp u a j).G b) (p : (I.stp u a j).D b), x.2 = 1 → cosetIn ((I.stp u a j).act b x p) = cosetIn p := by
  first | exact @GlobalTheory.Mem.Col2.cosetIn_act_rat | exact GlobalTheory.Mem.Col2.cosetIn_act_rat | (intros; apply GlobalTheory.Mem.Col2.cosetIn_act_rat <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.eCls0_mu0_eq_self : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (u : B.Word) (c : (I.stp u I.mu0 0).Cl), I.eCls0 l u I.mu0 c = c := by
  first | exact @GlobalTheory.Mem.Col2.TC.MuZeroCls.stepZeroClassEquiv_referenceTuple_eq_self | exact GlobalTheory.Mem.Col2.TC.MuZeroCls.stepZeroClassEquiv_referenceTuple_eq_self | (intros; apply GlobalTheory.Mem.Col2.TC.MuZeroCls.stepZeroClassEquiv_referenceTuple_eq_self <;> assumption)
end
