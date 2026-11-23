module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle022
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle163
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationDisjointPlacesCommuteVacua
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle330
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle188
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle143
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle270
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle344
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio

@[expose] public section

section

open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SeeSaw ValuativeRel Matrix

noncomputable section

namespace GlobalTheory.SeeSaw.MuUnits

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem Phi_eq {a t : Type} [Fintype a] [DecidableEq a] [Fintype t] [DecidableEq t] (Q Q' : TypeDatum k a)
    (hJ : Q.J = Q'.J) (hl : ∀ x (hx : x ∈ Q.J) (hx' : x ∈ Q'.J), Q.lam ⟨x, hx⟩ = Q'.lam ⟨x, hx'⟩)
    (μ μ' : kˣ →* ℂˣ) (hμ : ∀ x : kˣ, valuation k (x : k) = 1 → μ x = μ' x) (x : Matrix (a ⊕ t) a k) :
    Q.Phi t μ x = Q'.Phi t μ' x := by
  by_cases h : (∃ g ∈ Q.J, g.val = x.toRows₁) ∧ MaxM x.toRows₂
  · obtain ⟨⟨g, hg, e⟩, h2⟩ := h
    have hg' : g ∈ Q'.J := hJ ▸ hg
    rw [Q.Phi_of_mem μ ⟨g, hg⟩ e h2, Q'.Phi_of_mem μ' ⟨g, hg'⟩ e h2, hl g hg hg',
      hμ _ (valuation_det_of_mem_KO (Q.le_KO hg))]
  · have h' : ¬ ((∃ g ∈ Q'.J, g.val = x.toRows₁) ∧ MaxM x.toRows₂) := by rwa [← hJ]
    rw [not_not.1 (mt (Q.Phi_ne_zero_iff μ).1 h), not_not.1 (mt (Q'.Phi_ne_zero_iff μ').1 h')]

theorem iter_eq {r t : Type} [Fintype r] [DecidableEq r] [Fintype t] [DecidableEq t] (P : TypeDatum k r)
    (μ μ' : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, IsTame (μ j)) (hμ' : ∀ j, IsTame (μ' j))
    (h : ∀ j (x : kˣ), valuation k (x : k) = 1 → μ j x = μ' j x) (j : ℕ) :
    (P.iter t μ hμ j).J = (P.iter t μ' hμ' j).J ∧ ∀ x (hx : x ∈ (P.iter t μ hμ j).J) (hx' : x ∈ (P.iter t μ' hμ' j).J),
      (P.iter t μ hμ j).lam ⟨x, hx⟩ = (P.iter t μ' hμ' j).lam ⟨x, hx'⟩ := by
  induction j with
  | zero => exact ⟨rfl, fun _ _ _ => rfl⟩
  | succ j ih =>
    obtain ⟨hJ, hl⟩ := ih
    set Q := P.iter t μ hμ j
    set Q' := P.iter t μ' hμ' j
    have hS : Q.stepJ t = Q'.stepJ t := by
      ext g; rw [TypeDatum.mem_stepJ, TypeDatum.mem_stepJ, hJ]
    refine ⟨?_, fun x hx hx' => ?_⟩
    · rw [TypeDatum.iter_succ, TypeDatum.iter_succ]
      change (Q.stepJ t).comap _ = (Q'.stepJ t).comap _
      rw [hS]
    · have hx1 : (reGL (ixSucc r t j)).symm x ∈ Q.stepJ t := hx
      have hx1' : (reGL (ixSucc r t j)).symm x ∈ Q'.stepJ t := hx'
      change (Q.step t (μ (j + 1)) (hμ _)).lam ⟨_, hx1⟩ = (Q'.step t (μ' (j + 1)) (hμ' _)).lam ⟨_, hx1'⟩
      have hg' : ((Q.corner ⟨_, hx1⟩ : Q.J) : GL _ k) ∈ Q'.J := hJ ▸ (Q.corner ⟨_, hx1⟩).2
      refine (Q.step_lam _ _ ⟨_, hx1⟩ (Q.corner ⟨_, hx1⟩) (Q.corner_val _)).trans
        (Eq.trans ?_ (Q'.step_lam _ _ ⟨_, hx1'⟩ ⟨_, hg'⟩ (Q.corner_val _)).symm)
      rw [hl _ (Q.corner ⟨_, hx1⟩).2 hg',
        h _ _ (valuation_det_of_mem_KO (Q.le_KO (Q.corner ⟨_, hx1⟩).2)), h _ _ (valuation_det_of_mem_KO hx1.1)]

theorem withMu_eq (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (s κ : ℕ)
    (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t] (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, IsTame (μ j)) :
    (∀ j (x : kˣ), valuation k (x : k) = 1 → μ j x = S.μ j x) →
      (∀ j a H, ((withMu S μ hμ).T t).Phi j a H = (S.T t).Phi j a H) ∧
      ∀ j a H, (((withMu S μ hμ).T t).lev j a H).J = ((S.T t).lev j a H).J ∧
        ∀ x hx hx', (((withMu S μ hμ).T t).lev j a H).lam ⟨x, hx⟩ = ((S.T t).lev j a H).lam ⟨x, hx'⟩ := by
  intro h
  have E := iter_eq (t := t) S.P μ S.μ hμ S.tame h
  refine ⟨fun j a H => funext fun x => ?_, fun j a H => ⟨?_, fun x hx hx' => ?_⟩⟩
  · change (S.P.iter t μ hμ j).Phi t (μ (j + 1)) _ = (S.P.iter t S.μ S.tame j).Phi t (S.μ (j + 1)) _
    exact Phi_eq _ _ (E j).1 (E j).2 _ _ (h (j + 1)) _
  · change (S.P.iter t μ hμ j).J.comap _ = (S.P.iter t S.μ S.tame j).J.comap _
    rw [(E j).1]; rfl
  · exact (E j).2 _ hx hx'

end GlobalTheory.SeeSaw.MuUnits
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam

noncomputable section

namespace GlobalTheory.DatumTopAt

section Gen

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

theorem combAt_mono' {P Q : GlobalTheory.FinPl.Pl D → Prop} (h : ∀ x, P x → Q x) {c : WO S T →₀ ℂ}
    (hc : GlobalTheory.FinPl.CombAt P c) : GlobalTheory.FinPl.CombAt Q c := fun x hx => GlobalTheory.DisjComb.mxAt_mono h (hc x hx)

theorem vac_mono' {LS : GlobalTheory.FinPl.Lat S} {LT : GlobalTheory.FinPl.Lat T} (P : GlobalTheory.FinPl.Pl D → Prop) {f : WO S T → ℂ}
    (h : GlobalTheory.FinPl.Vac ψ S T LS LT (fun _ => True) f) : GlobalTheory.FinPl.Vac ψ S T LS LT P f := by
  have hle : latO S T (LS : Set _) (LT : Set _) P ≤ latO S T (LS : Set _) (LT : Set _) fun _ => True :=
    AddSubgroup.closure_mono fun w ⟨α, hα, _, hw⟩ => ⟨α, hα, fun _ h => absurd trivial h, hw⟩
  exact ⟨h.1, fun u hu => h.2.1 u (hle hu), fun e he u hu hh => h.2.2 e he u (hle hu) hh⟩

theorem locPl_combAt {M : GlobalTheory.FinPl.Lat S} {M' : GlobalTheory.FinPl.Lat T} (Lp : LocPl ψ S T M M') :
    GlobalTheory.FinPl.CombAt (· = Lp.q.v) Lp.o ∧ GlobalTheory.FinPl.CombAt (· = Lp.q.v) Lp.e :=
  ⟨fun u hu => GlobalTheory.FinPl.SplitHalfSuppImp.mxAt_of_isHalf D Lp.k Lp.q u (Lp.o_at u hu),
    fun u hu => GlobalTheory.FinPl.SplitHalfSuppImp.mxAt_of_isHalf D Lp.k Lp.q u (Lp.e_is.1 u hu)⟩

theorem comm_list (hψ : IsStdChar D ψ (-1)) {n : ℕ} (pv : Fin n → GlobalTheory.FinPl.Pl D) (hv : Function.Injective pv)
    (a b : Fin n → (WO S T →₀ ℂ)) (ha : ∀ i, GlobalTheory.FinPl.CombAt (· = pv i) (a i))
    (hb : ∀ i, GlobalTheory.FinPl.CombAt (· = pv i) (b i)) :
    ∀ l : List (Fin n), l.Nodup → ∀ g, l.foldr (fun i g' => comb ψ S T (b i) (comb ψ S T (a i) g')) g =
      l.foldr (fun i g' => comb ψ S T (b i) g') (l.foldr (fun i g' => comb ψ S T (a i) g') g) := by
  have pass : ∀ x (t : List (Fin n)), x ∉ t → ∀ Y, comb ψ S T (a x) (t.foldr (fun i g' => comb ψ S T (b i) g') Y) =
      t.foldr (fun i g' => comb ψ S T (b i) g') (comb ψ S T (a x) Y) := by
    intro x t
    induction t with
    | nil => intro _ Y; rfl
    | cons y t ih =>
      intro hx Y
      have hxy : x ≠ y := fun e => hx (e ▸ List.mem_cons_self)
      have hxt : x ∉ t := fun m => hx (List.mem_cons_of_mem _ m)
      have hd : ∀ p, (· = pv x) p → ¬ (· = pv y) p := fun p h1 h2 => hxy (hv (h1.symm.trans h2))
      simp only [List.foldr_cons]
      rw [(GlobalTheory.DisjComb.main D ψ hψ S T _ _ hd).1 (a x) (b y) (ha x) (hb y), ih hxt]
  intro l
  induction l with
  | nil => intro _ g; rfl
  | cons x t ih =>
    intro hnd g
    rw [List.nodup_cons] at hnd
    simp only [List.foldr_cons]
    rw [ih hnd.2, pass x t hnd.1]

theorem comp_list (hψ : IsStdChar D ψ (-1)) {n : ℕ} (Q : GlobalTheory.FinPl.Pl D → Prop) (a : Fin n → (WO S T →₀ ℂ))
    (ha : ∀ i, GlobalTheory.FinPl.CombAt Q (a i)) : ∀ l : List (Fin n), ∃ o, GlobalTheory.FinPl.CombAt Q o ∧
      ∀ g, comb ψ S T o g = l.foldr (fun i g' => comb ψ S T (a i) g') g := by
  intro l
  induction l with
  | nil =>
    refine ⟨Finsupp.single 0 1, fun u hu => ?_, fun g => ?_⟩
    · rw [Finsupp.mem_support_iff, Finsupp.single_apply] at hu
      split_ifs at hu with h0
      · subst h0; exact fun i j => Submodule.zero_mem _
      · exact absurd rfl hu
    · simp only [comb, Finsupp.support_single_ne_zero _ one_ne_zero, Finset.sum_singleton,
        Finsupp.single_eq_same, one_smul, List.foldr_nil]
      exact GlobalTheory.MixPer.heisO_zero ψ S T g
  | cons x t ih =>
    obtain ⟨o, ho, hc⟩ := ih
    obtain ⟨e, he, hce⟩ := (GlobalTheory.DisjComb.main D ψ hψ S T Q (fun _ => False) (fun _ _ h => h)).2.2.2.1 (a x) o
      (combAt_mono' (fun p hp => Or.inl hp) (ha x)) (combAt_mono' (fun p hp => Or.inl hp) ho)
    refine ⟨e, combAt_mono' (fun p hp => hp.elim id False.elim) he, fun g => ?_⟩
    rw [hce, hc]
    rfl

theorem latV_eq_of_moves {V : HSp D} {g : GA D V} {Λ M N : GlobalTheory.FinPl.Lat V} {P : GlobalTheory.FinPl.Pl D → Prop}
    (hM : Submodule.IsLattice D.host.E M) (hN : Submodule.IsLattice D.host.E N)
    (h1 : GlobalTheory.FinPl.Moves V g Λ M P) (h2 : GlobalTheory.FinPl.Moves V g Λ N P) :
    GlobalTheory.FinPl.latV V M P = GlobalTheory.FinPl.latV V N P := by
  have key : ∀ (A B : GlobalTheory.FinPl.Lat V), Submodule.IsLattice D.host.E A → GlobalTheory.FinPl.Moves V g Λ A P →
      GlobalTheory.FinPl.Moves V g Λ B P → ∀ y, y ∈ GlobalTheory.FinPl.latV V A P → y ∈ GlobalTheory.FinPl.latV V B P := by
    intro A B hA hgA hgB y hy
    have hent : ∀ i, y i ∈ GlobalTheory.FinPl.idAt D P := ((((GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D P).2 V).2.2.2 A y hA).1 hy).1
    have hz := GlobalTheory.VacMove.mem_ideal_mulVec _ (Formalism.L2.Theta.mt V g⁻¹) y hent
    have e : Formalism.L2.Theta.mt V g *ᵥ (Formalism.L2.Theta.mt V g⁻¹ *ᵥ y) = y := by
      rw [Matrix.mulVec_mulVec, GlobalTheory.VacMove.mt_mul_inv', Matrix.one_mulVec]
    have h3 := (hgA _ hz).2 (e.symm ▸ hy)
    have h4 := (hgB _ hz).1 h3
    rwa [e] at h4
  ext y
  exact ⟨key M N hM h1 h2 y, key N M hN h2 h1 y⟩

end Gen

end GlobalTheory.DatumTopAt

namespace GlobalTheory.DatumTopAt

end GlobalTheory.DatumTopAt
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw.CellProd

theorem prod_ofFn_mul {M : Type} [Monoid M] : ∀ {n : ℕ} (r u : Fin n → M), (∀ i i', i ≠ i' → Commute (u i) (r i')) →
    (List.ofFn fun i => r i * u i).prod = (List.ofFn r).prod * (List.ofFn u).prod
  | 0, _, _, _ => by simp
  | n + 1, r, u, h => by
    have ih := prod_ofFn_mul (fun i => r i.succ) (fun i => u i.succ)
      (fun i i' hi => h _ _ fun e => hi (Fin.succ_injective _ e))
    have hc : Commute (u 0) (List.ofFn fun i : Fin n => r i.succ).prod := by
      refine Commute.list_prod_right _ _ ?_
      rw [List.forall_mem_ofFn_iff]
      intro i
      exact h _ _ (Fin.succ_ne_zero i).symm
    simp only [List.ofFn_succ, List.prod_cons]
    rw [ih, mul_assoc, mul_assoc, ← mul_assoc (u 0), hc.eq, mul_assoc]

theorem prod_ofFn_single {M : Type} [Monoid M] : ∀ {n : ℕ} (f : Fin n → M) (i : Fin n), (∀ i', i' ≠ i → f i' = 1) →
    (List.ofFn f).prod = f i
  | 0, _, i, _ => i.elim0
  | n + 1, f, i, h => by
    simp only [List.ofFn_succ, List.prod_cons]
    induction i using Fin.cases with
    | zero =>
      rw [List.prod_eq_one, mul_one]
      rw [List.forall_mem_ofFn_iff]
      intro i
      exact h _ (Fin.succ_ne_zero i)
    | succ i =>
      rw [h 0 (Fin.succ_ne_zero i).symm, one_mul]
      exact prod_ofFn_single (fun i => f i.succ) i fun i' hi => h _ fun e => hi (Fin.succ_injective _ e)

variable {D : D7} {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k']

theorem idAt_le {P P' : Pl D → Prop} (h : ∀ v, P v → P' v) : idAt D P ≤ idAt D P' :=
  inf_le_inf_left _ (le_iInf fun w => iInf_le_of_le ⟨w.1, fun hw => w.2 (h _ hw)⟩ le_rfl)

theorem mem_idAt (q : SplitPt D k) {a : AE D} (h : (q.e + cA D q.e) * a = a) : a ∈ idAt D (· = q.v) := by
  obtain ⟨ε, hε, hs⟩ := q.above
  exact ((placeIdem_acts D q.v ε hε).1 a).2 (hs ▸ h)

theorem idem_mul_eq_zero (q : SplitPt D k) (q' : SplitPt D k') (hv : q'.v ≠ q.v) {a : AE D}
    (h : (q'.e + cA D q'.e) * a = a) : (q.e + cA D q.e) * a = 0 := by
  obtain ⟨ε, hε, hs⟩ := q.above
  rw [hs]
  exact (placeIdem_acts D q.v ε hε).2 a (idAt_le (fun v (e : v = q'.v) => e ▸ hv) (mem_idAt q' h))

theorem pr_eq_zero (q : SplitPt D k) (q' : SplitPt D k') (hv : q'.v ≠ q.v) {a : AE D}
    (h : (q'.e + cA D q'.e) * a = a) : q.pr a = 0 := by
  have h0 := idem_mul_eq_zero q q' hv h
  obtain ⟨h1, h2, -⟩ := q.split
  have : q.e * a = 0 := by
    have := congrArg (q.e * ·) h0
    simpa only [← mul_assoc, mul_add, h1, h2, add_zero, mul_zero] using this
  rw [← q.pr_sec (q.pr a), q.sec_pr, this, map_zero]

theorem mem_grpAt (q : SplitPt D k) {V : HSp D} {g : GA D V} (hg : SuppAt q.e V g) {P : Pl D → Prop} (hP : P q.v) :
    g ∈ grpAt V P := by
  rw [grpAt, congGrp, MonoidHom.mem_ker]
  ext i j
  change Ideal.Quotient.mk _ (mt V g i j) = (1 : Matrix (Fin V.rank) (Fin V.rank) _) i j
  rw [← Matrix.map_one (Ideal.Quotient.mk (idAt D P)) (map_zero _) (map_one _), Matrix.map_apply, Ideal.Quotient.eq]
  exact idAt_le (fun v (e : v = q.v) => e ▸ hP) (mem_idAt q (hg i j))

theorem mt_mul' (V : HSp D) (g h : GA D V) : mt V (g * h) = mt V g * mt V h := by
  simp [Formalism.L2.Theta.mt]

theorem sub_mul_sub (q : SplitPt D k) (q' : SplitPt D k') (hv : q'.v ≠ q.v) {V : HSp D} {g h : GA D V}
    (hg : SuppAt q.e V g) (hh : SuppAt q'.e V h) :
    (mt V g - 1) * (mt V h - 1) = 0 ∧ (mt V h - 1) * (mt V g - 1) = 0 := by
  have key : ∀ a b c d, (mt V g - 1) a b * (mt V h - 1) c d = 0 := fun a b c d => by
    rw [← hg a b, mul_comm (q.e + _), mul_assoc, idem_mul_eq_zero q q' hv (hh c d), mul_zero]
  constructor
  · ext a b
    rw [Matrix.mul_apply]
    exact Finset.sum_eq_zero fun c _ => key _ _ _ _
  · ext a b
    rw [Matrix.mul_apply]
    exact Finset.sum_eq_zero fun c _ => by rw [mul_comm]; exact key _ _ _ _

theorem commute_of_suppAt (q : SplitPt D k) (q' : SplitPt D k') (hv : q'.v ≠ q.v) {V : HSp D} {g h : GA D V}
    (hg : SuppAt q.e V g) (hh : SuppAt q'.e V h) : Commute g h := by
  obtain ⟨h1, h2⟩ := sub_mul_sub q q' hv hg hh
  have : mt V (g * h) = mt V (h * g) := by
    rw [mt_mul', mt_mul', ← sub_eq_zero]
    have e : mt V g * mt V h - mt V h * mt V g = (mt V g - 1) * (mt V h - 1) - (mt V h - 1) * (mt V g - 1) := by
      noncomm_ring
    rw [e, h1, h2, sub_zero]
  exact Subtype.ext (Units.ext this)

theorem map_eq_one (q : SplitPt D k) (q' : SplitPt D k') (hv : q'.v ≠ q.v) {V : HSp D} {g : GA D V}
    (hg : SuppAt q'.e V g) : (mt V g).map q.pr = 1 := by
  ext i j
  have := pr_eq_zero q q' hv (hg i j)
  rw [Matrix.sub_apply, map_sub, sub_eq_zero] at this
  rw [Matrix.map_apply, this, ← Matrix.map_one q.pr (map_zero _) (map_one _), Matrix.map_apply]

def matAt (q : SplitPt D k) (V : HSp D) : GA D V →* Matrix (Fin V.rank) (Fin V.rank) k :=
  (q.pr.mapMatrix.toMonoidHom.comp (Units.coeHom _)).comp (matHom V)

end GlobalTheory.SeeSaw.CellProd


open GlobalTheory.SeeSaw.CellProd in
theorem GlobalTheory.SeeSaw.prod_local_cells : ∀ {D : D7} {c : Comm D} {v : VCom c} {n : ℕ} (G : Fin n → GLoc v), GPin G → ∀ (j' : ℕ), j' < D.R.m → ∀ (R : Subgroup (GA D (c.V j'))) (b : Fin n → ℕ) (hb : ∀ i, j' + b i = (G i).s + 1) (xs : Fin n → GA D (c.V j')), (∀ i, ∃ r ∈ R, SuppAt (G i).q.e (c.V j') r ∧ ∃ u uk, (GlobalTheory.LocMod.ofSplit (G i).q).IsLoc ((G i).FY j' (b i) (hb i)) u uk ∧ uk ∈ (((G i).S.T (Fin D.R.t)).lev j' (b i) (hb i)).J ∧ xs i = r * u) → ∃ r ∈ R, r ∈ grpAt (c.V j') (· ∈ v.gP) ∧ ∃ k ∈ v.JG j', (List.ofFn xs).prod = r * k := by
  intro D c v n G hG j' hj R b hb xs H
  choose r hr hrs u uk hu huk hx using H
  have hne : ∀ i i', i ≠ i' → (G i).q.v ≠ (G i').q.v := fun i i' h e => h (hG.inj e)
  have hP : ∀ i, (G i).q.v ∈ v.gP := fun i => (hG.places _).2 ⟨i, rfl⟩
  have hus : ∀ i, SuppAt (G i).q.e (c.V j') (u i) := fun i => (hu i).1
  refine ⟨(List.ofFn r).prod, R.list_prod_mem ?_, Subgroup.list_prod_mem _ ?_, (List.ofFn u).prod,
    (hG.lev j' hj _).2 ⟨Subgroup.list_prod_mem _ ?_, ?_⟩, ?_⟩
  · rw [List.forall_mem_ofFn_iff]
    intro i
    exact hr i
  · rw [List.forall_mem_ofFn_iff]
    intro i
    exact mem_grpAt (G i).q (hrs i) (hP i)
  · rw [List.forall_mem_ofFn_iff]
    intro i
    exact mem_grpAt (G i).q (hus i) (hP i)
  · intro i a ha y hy
    obtain rfl : a = b i := by have := hb i; omega
    have e : matAt (G i).q (c.V j') (List.ofFn u).prod = matAt (G i).q (c.V j') (u i) := by
      rw [map_list_prod, List.map_ofFn]
      exact prod_ofFn_single _ i fun i' hi => map_eq_one (G i).q (G i').q (hne _ _ hi) (hus i')
    have e2 : ((G i).FY j' (b i) ha).β * y.val * ((G i).FY j' (b i) ha).γ =
        ((G i).FY j' (b i) ha).β * (uk i).val * ((G i).FY j' (b i) ha).γ := hy.symm.trans (e.trans (hu i).2)
    have e3 := congrArg (fun x => ((G i).FY j' (b i) ha).γ * x * ((G i).FY j' (b i) ha).β) e2
    simp only [← Matrix.mul_assoc, GlobalTheory.LocMod.Frame.γβ, Matrix.one_mul] at e3
    simp only [Matrix.mul_assoc, GlobalTheory.LocMod.Frame.γβ, Matrix.mul_one] at e3
    rw [Units.ext e3]
    exact huk i
  · rw [show xs = fun i => r i * u i from funext hx]
    exact prod_ofFn_mul r u fun i i' h => commute_of_suppAt (G i).q (G i').q (hne _ _ h.symm) (hus i) (hrs i')

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.GSuppComb

theorem foldr_extract {ι X : Type} [DecidableEq ι] (g : ι → X → X) (i : ι)
    (hc : ∀ a, a ≠ i → ∀ x, g a (g i x) = g i (g a x)) :
    ∀ (l : List ι) (x : X), i ∈ l → l.foldr g x = g i ((l.erase i).foldr g x) := by
  intro l x hi
  induction l with
  | nil => simp at hi
  | cons a t ih =>
    by_cases ha : a = i
    · subst ha
      simp
    · have hit : i ∈ t := by
        rcases List.mem_cons.1 hi with h | h
        · exact absurd h.symm ha
        · exact h
      have he : (a :: t).erase i = a :: t.erase i := by
        simp [List.erase_cons, ha]
      rw [he, List.foldr_cons, List.foldr_cons, ih hit, hc a ha]

variable {D : D7}

theorem latO_mono {S T : HSp D} (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    {P P' : Pl D → Prop} (h : ∀ p, P p → P' p) : latO S T LS LT P ≤ latO S T LS LT P' := by
  apply AddSubgroup.closure_mono
  rintro w ⟨α, hα, hv, rest⟩
  exact ⟨α, hα, fun p hp => hv p fun hq => hp (h p hq), rest⟩

theorem vac_mono {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {LS : Lat S} {LT : Lat T} {P P' : Pl D → Prop}
    (h : ∀ p, P p → P' p) {f : WO S T → ℂ} (hf : Vac ψ S T LS LT P' f) : Vac ψ S T LS LT P f :=
  ⟨hf.1, fun u hu => hf.2.1 u (latO_mono _ _ h hu), fun e he u hu hh => hf.2.2 e he u (latO_mono _ _ h hu) hh⟩

theorem eg_combAt {c : Comm D} {v : VCom c} (G : GLoc v) (j : ℕ) (hj : j ≤ G.s) : CombAt (· = G.q.v) (G.eg j) := by
  intro u hu a b
  have h := (G.eg_is j (G.s - j) (by omega)).1 u hu a b
  exact (GlobalTheory.FinPl.FrameLat.idem_iff G.q _).2 h

theorem comb_eq_at_place : ∀ {D : D7} {c : Comm D} {v : VCom c} {n : ℕ}, c.Is → v.Is → ∀ (G : Fin n → GLoc v), GPin G → ∀ (j : ℕ), j + 1 < D.R.m → ∀ (Ψ : WO (c.V j) (c.V (j + 1)) → ℂ), Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ v.gP) Ψ → ∀ (i : Fin n), ∃ F, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· = (G i).q.v) F ∧ comb c.ψ _ _ (v.eG j) Ψ = comb c.ψ _ _ ((G i).eg j) F := by
  intro D c v n hc hv G hG j hj Ψ hΨ i
  have hI := GlobalTheory.T.heisenbergCombination_disjoint_places_commute_vacua D c.ψ hc.std (c.V j) (c.V (j + 1))
  have hca : ∀ i', CombAt (· = (G i').q.v) ((G i').eg j) := fun i' =>
    eg_combAt (G i') j (by have := (G i').hs; omega)
  have hdisj : ∀ a b : Fin n, a ≠ b → ∀ p, p = (G a).q.v → ¬ p = (G b).q.v := fun a b hab p ha hb =>
    hab (hG.inj (ha.symm.trans hb))
  let g : Fin n → (WO (c.V j) (c.V (j + 1)) → ℂ) → (WO (c.V j) (c.V (j + 1)) → ℂ) :=
    fun a f => comb c.ψ _ _ ((G a).eg j) f
  refine ⟨((List.finRange n).erase i).foldr g Ψ, ?_, ?_⟩
  · have h0 : Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· = (G i).q.v) Ψ :=
      vac_mono (fun p hp => by rw [hp]; exact (hG.places _).2 ⟨i, rfl⟩) hΨ
    have key : ∀ l : List (Fin n), (∀ a ∈ l, a ≠ i) → Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· = (G i).q.v) (l.foldr g Ψ) := by
      intro l
      induction l with
      | nil => intro _; exact h0
      | cons a t ih =>
        intro hl
        exact ((hI (· = (G a).q.v) (· = (G i).q.v) (hdisj a i (hl a (List.mem_cons_self ..)))).2.1 _ (hca a)).2 _ _ _
          (ih fun b hb => hl b (List.mem_cons_of_mem _ hb))
    exact key _ fun a ha => ((List.nodup_finRange n).mem_erase_iff.1 ha).1
  · rw [hG.eG j hj Ψ hΨ.1]
    exact foldr_extract g i (fun a ha x => (hI _ _ (hdisj a i ha)).1 _ _ (hca a) (hca i) x) _ Ψ (List.mem_finRange i)

end GlobalTheory.GSuppComb

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.OffPlaceWeil

theorem vac_off {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle} {om : Om S T}
    (hW : IsWeilDatumO ψ S T χS χT om) {LS : Lat S} {LT : Lat T} {P : GlobalTheory.FinPl.Pl D → Prop} {f : WO S T → ℂ}
    (hf : Vac ψ S T LS LT P f) {g : GA D S} {h : GA D T} (hg : g ∈ grpOff S P) (hh : h ∈ grpOff T P) :
    Vac ψ S T LS LT P (om (g, h) f) := by
  have key : ∀ u ∈ latO S T (LS : Set _) (LT : Set _) P, heisO ψ S T u f = f →
      heisO ψ S T u (om (g, h) f) = om (g, h) f := by
    intro u hu hfix
    have e := hW.om_heis g h u f hf.1
    rw [hfix, GlobalTheory.DisjComb.actO_off hg hh (GlobalTheory.FinPl.LatMem.latO_mxAt hu)] at e
    exact e.symm
  exact ⟨hW.om_pres _ f hf.1, fun u hu => key _ (AddSubgroup.nsmul_mem _ hu 2) (hf.2.1 u hu),
    fun e he u hu hh' => key u hu (hf.2.2 e he u hu hh')⟩

theorem combAt_eg {D : D7} {c : Comm D} {v : VCom c} (Gi : GLoc v) (j : ℕ) (hj : j + 1 < D.R.m) :
    CombAt (· = Gi.q.v) (Gi.eg j) := by
  have hs := Gi.hs
  intro u hu a b
  have h1 := (Gi.eg_is j (Gi.s - j) (by omega)).1 u hu a b
  obtain ⟨ε, hε, hsum⟩ := Gi.q.above
  exact ((GlobalTheory.FinPl.placeIdem_acts D Gi.q.v ε hε).1 _).2 (hsum ▸ h1)

theorem main : ∀ {D : D7} {c : Comm D} {v : VCom c}, c.Is → v.Is → ∀ (Gi : GLoc v) (j : ℕ), j + 1 < D.R.m → ∀ (χS χT : (AE D)ˣ →* Circle) (om : Om (c.V j) (c.V (j + 1))), IsWeilDatumO c.ψ _ _ χS χT om → ∀ (F : WO (c.V j) (c.V (j + 1)) → ℂ), Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· = Gi.q.v) F → ∀ y ∈ grpOff (c.V (j + 1)) (· = Gi.q.v), Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· = Gi.q.v) (om (1, y) F) ∧ om (1, y) (comb c.ψ _ _ (Gi.eg j) F) = comb c.ψ _ _ (Gi.eg j) (om (1, y) F) := by
  intro D c v hc _ Gi j hj χS χT om hW F hF y hy
  exact ⟨vac_off hW hF (one_mem _) hy,
    (GlobalTheory.DisjComb.main D c.ψ hc.std _ _ (· = Gi.q.v) (fun _ => False) (fun _ _ h => h)).2.2.1 χS χT om hW _
      (combAt_eg Gi j hj) 1 (one_mem _) y hy F hF.1⟩

end GlobalTheory.OffPlaceWeil
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod

theorem _root_.GlobalTheory.T.exists_heisenberg_combination_split_place_datum : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (S T : HSp D) (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ Φ₀ Φ : SB (Matrix Y Y' k), Φ₀ ≠ 0 → ∃ c : WO S T →₀ ℂ, (∀ w ∈ c.support, IsHalf (p.e + cA D p.e) w) ∧ ∀ Tm, p.IsModel ψ FS FT Tm → Tm Φ = comb ψ S T c (Tm Φ₀) := by
  first | exact @GlobalTheory.LocComb.exists_comb | exact GlobalTheory.LocComb.exists_comb | (intros; apply GlobalTheory.LocComb.exists_comb <;> assumption)
end
